import LSBA.Analysis.Boole
import LSBA.Upper.LargeTransfer
import LSBA.Upper.ConversionBoundary
import LSBA.Transfer.PathCut
import LSBA.Gauss.BlockWindow

/-!
# Energy-integrated fractional resolvents on a path

The fixed-parameter core of Proposition 8.4(ii) [up:prop:conversion], for finite Dirichlet block
paths with arbitrary deterministic Hermitian endpoint shifts (8.5) [up:eq:shifted-resolvent]: the
bound (8.12) [up:eq:negative-transfer-input] on `|E| ≤ E₀` gives
`∫_{J₀} 𝔼‖G^{L₀,R₀}(x, y; E)‖^{s/2} dE ≤ K W² e^{−(c/2)|x−y|/(Wg²)}` for every measurable
`J₀ ⊆ [−E₀, E₀]`, through (8.15) [uvg:eq:boundary] and (8.16) [uvg:eq:energyapriori].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The matrix inverse is measurable. -/
private lemma greenPath_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable fun A : Matrix ι ι ℂ => A⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hd : Measurable fun A : Matrix ι ι ℂ => A.det := (continuous_id.matrix_det).measurable
  have ha : Measurable fun A : Matrix ι ι ℂ => A.adjugate i j :=
    (continuous_id.matrix_adjugate).measurable.eval_matrix
  exact hd.inv.mul ha

/-- Each block of the GUE sample is continuous in the sample. -/
private lemma greenPath_continuous_gueBlock (W m : ℕ) (a : Fin m) :
    Continuous fun ω : Ω W m => gueBlock W m ω a := by
  refine continuous_pi fun α => continuous_pi fun β => ?_
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The block-diagonal operator is continuous in its blocks. -/
private lemma greenPath_continuous_blockDiagOp {W m : ℕ} :
    Continuous fun V : Fin m → Matrix (Fin W) (Fin W) ℂ => blockDiagOp V := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [blockDiagOp, Matrix.of_apply]
  split_ifs
  · exact ((continuous_apply p.1).matrix_elem p.2 q.2)
  · exact continuous_const

/-- The path operator (8.5) [up:eq:shifted-resolvent] is continuous in its blocks. -/
private lemma greenPath_continuous_pathOp (g : ℝ) {W m : ℕ} (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) :
    Continuous fun V : Fin m → Matrix (Fin W) (Fin W) ℂ => pathOp g V L₀ R₀ := by
  unfold pathOp
  exact ((continuous_const.add (greenPath_continuous_blockDiagOp (W := W) (m := m))).const_smul
    ((max 1 g : ℝ)⁻¹ : ℂ)).add continuous_const

/-- `H − E` for the path operator (8.5) [up:eq:shifted-resolvent] of a GUE sample is jointly
continuous in `(E, ω)`. -/
private lemma greenPath_continuous_sub (g : ℝ) {W m : ℕ} (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) :
    Continuous fun z : ℝ × Ω W m => pathOp g (gueBlock W m z.2) L₀ R₀ -
      ((z.1 : ℂ)) • (1 : Matrix (Fin m × Fin W) (Fin m × Fin W) ℂ) := by
  have h1 : Continuous fun z : ℝ × Ω W m => pathOp g (gueBlock W m z.2) L₀ R₀ :=
    (greenPath_continuous_pathOp g L₀ R₀).comp
      (continuous_pi fun a => (greenPath_continuous_gueBlock W m a).comp continuous_snd)
  exact h1.sub ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_const)

/-- A block of a matrix is continuous in the matrix. -/
private lemma greenPath_continuous_blockOf {W m : ℕ} (i j : Fin m) :
    Continuous fun X : Matrix (Fin m × Fin W) (Fin m × Fin W) ℂ => blockOf X i j :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_id.matrix_elem _ _

/-- `x ↦ ‖(A x)⁻¹(i, j)‖^p` is measurable for a continuous family of matrices `A`. -/
private lemma greenPath_measurable_blockOf_inv {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {W m : ℕ}
    {A : X → Matrix (Fin m × Fin W) (Fin m × Fin W) ℂ} (hA : Continuous A) (i j : Fin m)
    (p : ℝ) : Measurable fun x => ‖blockOf (A x)⁻¹ i j‖ₑ ^ p :=
  (continuous_enorm.measurable.comp ((greenPath_continuous_blockOf (W := W) i j).measurable.comp
    (greenPath_measurable_inv.comp hA.measurable))).pow_const p

/-- `(E, ω) ↦ ‖G(i, j; E)‖^p` is jointly measurable. -/
lemma greenPath_measurable_entry (g : ℝ) {W m : ℕ} (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ)
    (i j : Fin m) (p : ℝ) :
    Measurable fun z : ℝ × Ω W m =>
      ‖blockOf (resolventMat (pathOp g (gueBlock W m z.2) L₀ R₀) z.1) i j‖ₑ ^ p := by
  unfold resolventMat
  exact greenPath_measurable_blockOf_inv (greenPath_continuous_sub g L₀ R₀) i j p

/-- `E ↦ ‖G(i, j; E)‖^p` is measurable for a fixed sample. -/
private lemma greenPath_measurable_entry_energy (g : ℝ) {W m : ℕ}
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (i j : Fin m) (p : ℝ) (ω : Ω W m) :
    Measurable fun E : ℝ =>
      ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E) i j‖ₑ ^ p := by
  unfold resolventMat
  exact greenPath_measurable_blockOf_inv (A := fun E : ℝ => pathOp g (gueBlock W m ω) L₀ R₀ -
    (E : ℂ) • (1 : Matrix (Fin m × Fin W) (Fin m × Fin W) ℂ))
    (continuous_const.sub (Complex.continuous_ofReal.smul continuous_const)) i j p

/-- `ω ↦ ‖G(i, j; E)‖^p` is measurable for a fixed energy. -/
private lemma greenPath_measurable_entry_sample (g : ℝ) {W m : ℕ}
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (i j : Fin m) (p : ℝ) (E : ℝ) :
    Measurable fun ω : Ω W m =>
      ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E) i j‖ₑ ^ p := by
  unfold resolventMat
  exact greenPath_measurable_blockOf_inv (A := fun ω : Ω W m => pathOp g (gueBlock W m ω) L₀ R₀ -
    (E : ℂ) • (1 : Matrix (Fin m × Fin W) (Fin m × Fin W) ℂ))
    (((greenPath_continuous_pathOp g L₀ R₀).comp
      (continuous_pi fun a => greenPath_continuous_gueBlock W m a)).sub continuous_const) i j p

/-- The resolvent of a path operator whose blocks depend continuously on a parameter is
measurable in that parameter. -/
private lemma greenPath_measurable_resolvent {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (g : ℝ) {W k : ℕ} {V : X → Fin k → Matrix (Fin W) (Fin W) ℂ}
    (hV : Continuous V) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ) :
    Measurable fun x => resolventMat (pathOp g (V x) L₀ R₀) E := by
  unfold resolventMat
  exact greenPath_measurable_inv.comp
    (((greenPath_continuous_pathOp g L₀ R₀).comp hV).sub continuous_const).measurable

/-- The shift `-(g/max{1,g})² G^{0,R₀}(0, 0)` of a Hermitian path at a real energy is
Hermitian. -/
private lemma greenPath_shiftFromRight_isHermitian (g : ℝ) {W k : ℕ}
    {V : Fin k → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ a, (V a).IsHermitian)
    {R₀ : Matrix (Fin W) (Fin W) ℂ} (hR₀ : R₀.IsHermitian) (E : ℝ) :
    (shiftFromRight g V R₀ E).IsHermitian := by
  unfold shiftFromRight
  split_ifs with h
  · have hA := pathOp_isHermitian g hV Matrix.isHermitian_zero hR₀
    have hs := blockOf_resolventMat_swap hA E ⟨0, h⟩ ⟨0, h⟩
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, ← hs, star_neg, Complex.star_def,
      Complex.conj_ofReal]
  · exact Matrix.isHermitian_zero

/-- `cfc f` is continuous on the self-adjoint matrices for continuous `f`. -/
private lemma greenPath_continuous_cfc {W : ℕ} {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous fun A : {A : Matrix (Fin W) (Fin W) ℂ // IsSelfAdjoint A} => cfc f A.1 :=
  Continuous.cfc_of_mem_nhdsSet (s := Set.univ) f (by simp) continuous_subtype_val
    (fun x => x.2) hf.continuousOn

/-- `Y ↦ (I; Y)` is continuous. -/
private lemma greenPath_continuous_colStack {W : ℕ} :
    Continuous fun Y : Matrix (Fin W) (Fin W) ℂ => colStack 1 Y := by
  refine continuous_pi fun p => continuous_pi fun α => ?_
  simp only [colStack, Matrix.of_apply]
  split_ifs
  · exact continuous_const
  · exact continuous_id.matrix_elem _ _

/-- The frame `Φ^ph_R` (proof of Proposition 8.4(i) [up:prop:conversion]) of a
measurable family of Hermitian matrices `R` is measurable. -/
private lemma greenPath_measurable_phFrame {X : Type*} [MeasurableSpace X] (g : ℝ) {W : ℕ}
    {R : X → Matrix (Fin W) (Fin W) ℂ} (hR : Measurable R) (hRh : ∀ x, (R x).IsHermitian) :
    Measurable fun x => phFrame g (R x) := by
  have hr : IsSelfAdjoint (((max 1 g / g : ℝ) : ℂ)) := Complex.conj_ofReal _
  have hQ : ∀ x, IsSelfAdjoint (((max 1 g / g : ℝ) : ℂ) • R x) := fun x =>
    hr.smul (hRh x)
  have hQm : Measurable fun x => ((max 1 g / g : ℝ) : ℂ) • R x :=
    (continuous_const_smul _).measurable.comp hR
  have hf : Continuous fun x : ℝ => (1 + x ^ 2) ^ (-(1 / 2 : ℝ)) :=
    (continuous_const.add (continuous_pow 2)).rpow_const fun x =>
      Or.inl (by positivity : (0 : ℝ) < 1 + x ^ 2).ne'
  have h2 : Measurable fun x => cfc (fun x : ℝ => (1 + x ^ 2) ^ (-(1 / 2 : ℝ)))
      (((max 1 g / g : ℝ) : ℂ) • R x) :=
    (greenPath_continuous_cfc (W := W) hf).measurable.comp (hQm.subtype_mk (h := hQ))
  have h1 : Measurable fun x => colStack 1 (((max 1 g / g : ℝ) : ℂ) • R x) :=
    greenPath_continuous_colStack.measurable.comp hQm
  have hmul : Continuous fun p : Matrix (Fin 2 × Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
      p.1 * p.2 := continuous_fst.matrix_mul continuous_snd
  exact hmul.measurable.comp (h1.prodMk h2)

/-- The transfer matrix of Definition 7.1 [def:transfer-matrices] is continuous in its block. -/
private lemma greenPath_continuous_transferMat {W : ℕ} (g : ℝ) (z : ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => transferMat g z V := by
  unfold transferMat
  refine continuous_const.sub ((continuous_const_smul ((g : ℂ)⁻¹)).comp ?_)
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [Matrix.kroneckerMap_apply]
  exact continuous_const.mul (continuous_id.matrix_elem _ _)

/-- Products of transfer matrices of continuously varying blocks are continuous. -/
private lemma greenPath_continuous_transferProd {X : Type*} [TopologicalSpace X] {W : ℕ}
    (g : ℝ) (z : ℂ) {U : X → ℕ → Matrix (Fin W) (Fin W) ℂ} (hU : ∀ j, Continuous fun x => U x j)
    (n : ℕ) : Continuous fun x => transferProd g z (U x) n := by
  induction n with
  | zero => exact continuous_const
  | succ j ih => exact ((greenPath_continuous_transferMat g z).comp (hU j)).mul ih

/-- `(M, Φ) ↦ D(M, Φ)` of (8.10) [up:eq:D-definition] is continuous. -/
private lemma greenPath_continuous_frameD {W : ℕ} :
    Continuous fun p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin W) ℂ => frameD p.1 p.2 := by
  refine continuous_pi fun α => continuous_pi fun β => ?_
  simp only [frameD, Matrix.of_apply]
  exact continuous_const.mul ((((continuous_const.matrix_mul continuous_fst).matrix_mul
    continuous_const).matrix_mul continuous_snd).matrix_elem _ _)

/-- `‖D(M, Φ)⁻¹‖^s` is measurable for continuous `M` and measurable `Φ`. -/
private lemma greenPath_measurable_frameD_inv {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {W : ℕ} {M : X → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {Φ : X → Matrix (Fin 2 × Fin W) (Fin W) ℂ} (hM : Continuous M) (hΦ : Measurable Φ) (s : ℝ) :
    Measurable fun x => ‖(frameD (M x) (Φ x))⁻¹‖ₑ ^ s := by
  have h := greenPath_measurable_inv.comp
    (greenPath_continuous_frameD.measurable.comp (hM.measurable.prodMk hΦ))
  exact (continuous_enorm.measurable.comp h).pow_const s

/-- Resolvent blocks of a path do not change under a cast of the index type. -/
private lemma greenPath_blockOf_cast (g : ℝ) {W m m' : ℕ} (h : m = m')
    (V : Fin m → Matrix (Fin W) (Fin W) ℂ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (i j : Fin m) :
    blockOf (resolventMat (pathOp g V L₀ R₀) E) i j =
      blockOf (resolventMat (pathOp g (V ∘ Fin.cast h.symm) L₀ R₀) E) (Fin.cast h i)
        (Fin.cast h j) := by
  subst h
  rfl

/-- Cutting off the blocks `[p, p + q)` of a path (none if `q = 0`) turns `R₀` into the induced
shift. -/
private lemma greenPath_cutRight (g : ℝ) {W p q : ℕ} (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ)
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (hd : 0 < q → (pathOp g (V ∘ Fin.natAdd p) 0 R₀ -
      (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ)).det ≠ 0)
    (i i' : Fin p) :
    blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.castAdd q i) (Fin.castAdd q i') =
      blockOf (resolventMat (pathOp g (V ∘ Fin.castAdd q) L₀
        (if 0 < q then shiftFromRight g (V ∘ Fin.natAdd p) R₀ E else R₀)) E) i i' := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [lt_irrefl, ↓reduceIte]
    rfl
  · simp only [hq, ↓reduceIte]
    exact pathOp_cut_left g hq V L₀ R₀ E (hd hq) i i'

/-- Cutting off the blocks `[0, p)` of a path (none if `p = 0`) turns `L₀` into the
induced shift. -/
private lemma greenPath_cutLeft (g : ℝ) {W p q : ℕ} (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ)
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (hd : 0 < p → (pathOp g (V ∘ Fin.castAdd q) L₀ 0 -
      (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ)).det ≠ 0)
    (j j' : Fin q) :
    blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.natAdd p j) (Fin.natAdd p j') =
      blockOf (resolventMat (pathOp g (V ∘ Fin.natAdd p)
        (if 0 < p then shiftFromLeft g (V ∘ Fin.castAdd q) L₀ E else L₀) R₀) E) j j' := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp only [lt_irrefl, ↓reduceIte]
    have e1 : ∀ j : Fin q, Fin.cast (zero_add q) (Fin.natAdd 0 j) = j := fun j =>
      Fin.ext (by simp)
    have e2 : V ∘ Fin.cast (zero_add q).symm = V ∘ Fin.natAdd 0 := by
      funext j
      simp only [Function.comp]
      congr 1
      ext
      simp
    rw [greenPath_blockOf_cast g (zero_add q) V, e1, e1, e2]
  · simp only [hp, ↓reduceIte]
    exact pathOp_cut_right g hp V L₀ R₀ E (hd hp) j j'

/-- (8.15) [uvg:eq:boundary] for the blocks `a, a + n` of a path of length `m = a + (n + 1) + k`:
after cutting off `[0, a)` and `(a + n, m)` (at energies where the two remaining parts are
invertible), `‖G(a + n, a)‖ ≤ ‖D′⁻¹‖ (‖G(a, a)‖ + ‖G(a + 1, a)‖)`, where `D′` is built from the
reversed blocks `V_{a+n}, …, V_{a+1}` and the frame of the shift induced by `(a + n, m)`. -/
private theorem greenPath_comparison {g : ℝ} (hg : 0 < g) {W m a n k : ℕ}
    (hm : m = a + (n + 1) + k) (hn : 1 ≤ n) (V : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (hV : ∀ i, (V i).IsHermitian) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (hR₀ : R₀.IsHermitian)
    (E : ℝ)
    (hdR : 0 < k → (pathOp g (fun j : Fin k => V ⟨a + (n + 1) + j, by omega⟩) 0 R₀ -
      (E : ℂ) • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ)).det ≠ 0)
    (hdL : 0 < a → (pathOp g (fun j : Fin a => V ⟨j, by omega⟩) L₀ 0 -
      (E : ℂ) • (1 : Matrix (Fin a × Fin W) (Fin a × Fin W) ℂ)).det ≠ 0) :
    ‖blockOf (resolventMat (pathOp g V L₀ R₀) E) ⟨a + n, by omega⟩ ⟨a, by omega⟩‖ ≤
      ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
            (fun j => V ⟨a + (n - j), by omega⟩) n)
          ((freeConj W 0)ᴴ * phFrame g (if 0 < k then shiftFromRight g
            (fun j : Fin k => V ⟨a + (n + 1) + j, by omega⟩) R₀ E else R₀)))⁻¹‖ *
        (‖blockOf (resolventMat (pathOp g V L₀ R₀) E) ⟨a, by omega⟩ ⟨a, by omega⟩‖ +
          ‖blockOf (resolventMat (pathOp g V L₀ R₀) E) ⟨a + 1, by omega⟩ ⟨a, by omega⟩‖) := by
  subst hm
  have hRh : (if 0 < k then shiftFromRight g
      (fun j : Fin k => V ⟨a + (n + 1) + j, by omega⟩) R₀ E else R₀).IsHermitian := by
    split_ifs
    · exact greenPath_shiftFromRight_isHermitian g (fun _ => hV _) hR₀ E
    · exact hR₀
  have key : ∀ i j : Fin (n + 1),
      blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.castAdd k (Fin.natAdd a i))
          (Fin.castAdd k (Fin.natAdd a j)) =
        blockOf (resolventMat (pathOp g (fun i : Fin (n + 1) => V ⟨a + i, by omega⟩)
          (if 0 < a then shiftFromLeft g (fun j : Fin a => V ⟨j, by omega⟩) L₀ E else L₀)
          (if 0 < k then shiftFromRight g
            (fun j : Fin k => V ⟨a + (n + 1) + j, by omega⟩) R₀ E else R₀)) E) i j := by
    intro i j
    rw [greenPath_cutRight g V L₀ R₀ E hdR]
    exact greenPath_cutLeft g (V ∘ Fin.castAdd k) L₀ _ E hdL i j
  have hc := pathOp_boundary_comparison hg hn (fun i : Fin (n + 1) => V ⟨a + i, by omega⟩)
    (fun _ => hV _)
    (if 0 < a then shiftFromLeft g (fun j : Fin a => V ⟨j, by omega⟩) L₀ E else L₀) _ hRh E
  have e0 : (⟨a + n, by omega⟩ : Fin (a + (n + 1) + k)) =
      Fin.castAdd k (Fin.natAdd a (Fin.last n)) := rfl
  have e1 : (⟨a, by omega⟩ : Fin (a + (n + 1) + k)) = Fin.castAdd k (Fin.natAdd a 0) := rfl
  have e2 : (⟨a + 1, by omega⟩ : Fin (a + (n + 1) + k)) = Fin.castAdd k (Fin.natAdd a 1) := by
    ext
    simp [Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
  rw [e0, e1, e2, key, key, key]
  exact hc

/-- `H = H(V = 0) + max{1,g}⁻¹ diag(V)` for the path operator (8.5) [up:eq:shifted-resolvent]. -/
private lemma greenPath_pathOp_eq (g : ℝ) {W m : ℕ} (V : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) :
    pathOp g V L₀ R₀ = pathOp g (fun _ => 0) L₀ R₀ +
      (((max 1 g)⁻¹ : ℝ) : ℂ) • blockDiagOp V := by
  have h0 : blockDiagOp (fun _ : Fin m => (0 : Matrix (Fin W) (Fin W) ℂ)) = 0 := by
    ext p q
    simp [blockDiagOp]
  simp only [pathOp, h0, add_zero, smul_add, Complex.ofReal_inv]
  abel

/-- For a fixed energy, the path of the blocks of a GUE sample in an injective window is almost
surely invertible at that energy. -/
private lemma greenPath_ae_det (g : ℝ) {W m q : ℕ} {s : Fin q → Fin m}
    (hs : Function.Injective s) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ) :
    ∀ᵐ ω ∂(μ W m), (pathOp g (fun j => gueBlock W m ω (s j)) L₀ R₀ -
      (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ)).det ≠ 0 := by
  have hc : ((max 1 g)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (lt_max_of_lt_left one_pos).ne'
  have h := ae_det_ne_zero_gueBlock (W := W) (n := q) (pathOp g (fun _ => 0) L₀ R₀) hc (E : ℂ)
  have h2 := (measurePreserving_windowSample W m q hs).quasiMeasurePreserving.ae h
  filter_upwards [h2] with ω hω
  rw [greenPath_pathOp_eq]
  exact hω

/-- Transfer products of length `n` only read the first `n` blocks. -/
private lemma greenPath_transferProd_congr {W : ℕ} (g : ℝ) (z : ℂ)
    {U U' : ℕ → Matrix (Fin W) (Fin W) ℂ} {n : ℕ} (h : ∀ j < n, U j = U' j) :
    transferProd g z U n = transferProd g z U' n := by
  induction n with
  | zero => rfl
  | succ j ih =>
    simp only [transferProd, h j (Nat.lt_succ_self j), ih fun i hi => h i (Nat.lt_succ_of_lt hi)]

/-- Theorem 11.1 [uvg:thm:transfer] for the reversed blocks `V_{a+n}, …, V_{a+1}` of a GUE path
of length `m = a + (n + 1) + k`, with the frame of the shift induced by the blocks
`(a + n, m)`, which are independent of the window. -/
private theorem greenPath_frame_moment {E₀ C c s : ℝ} {W : ℕ} {g : ℝ}
    (hT : ∀ n : ℕ, 1 ≤ n → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ, IsBoundaryFrame Φ →
        ∫⁻ ω, ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
            (seqBlocks (gueBlock W n ω)) n) Φ)⁻¹‖ₑ ^ s ∂(μ W n) ≤
          ENNReal.ofReal (C * W * Real.exp (-c * n / (W * g ^ 2))))
    (hg0 : 0 < g) {m a n k : ℕ} (hn : 1 ≤ n)
    (hm : m = a + (n + 1) + k) (R₀ : Matrix (Fin W) (Fin W) ℂ) (hR₀ : R₀.IsHermitian) {E : ℝ}
    (hE : |E| ≤ E₀) :
    ∫⁻ ω, ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
          (fun j => gueBlock W m ω ⟨a + (n - j), by omega⟩) n)
        ((freeConj W 0)ᴴ * phFrame g (if 0 < k then shiftFromRight g
          (fun j : Fin k => gueBlock W m ω ⟨a + (n + 1) + j, by omega⟩) R₀ E else R₀)))⁻¹‖ₑ ^ s
        ∂(μ W m) ≤
      ENNReal.ofReal (C * W * Real.exp (-c * n / (W * g ^ 2))) := by
  set rS : Ω W m → Matrix (Fin W) (Fin W) ℂ := fun ω => if 0 < k then shiftFromRight g
    (fun j : Fin k => gueBlock W m ω ⟨a + (n + 1) + j, by omega⟩) R₀ E else R₀ with hrS
  have hrSh : ∀ ω, (rS ω).IsHermitian := fun ω => by
    simp only [hrS]
    split_ifs
    · exact greenPath_shiftFromRight_isHermitian g (fun _ => gueBlock_isHermitian _ _ _ _) hR₀ E
    · exact hR₀
  have hrSm : Measurable rS := by
    by_cases hk : 0 < k
    · simp only [hrS, hk, ↓reduceIte]
      unfold shiftFromRight
      simp only [hk, ↓reduceDIte]
      exact (continuous_const_smul _).measurable.comp
        ((greenPath_continuous_blockOf _ _).measurable.comp
          (greenPath_measurable_resolvent g (continuous_pi fun j =>
            greenPath_continuous_gueBlock W m _) 0 R₀ E))
    · simp only [hrS, hk, ↓reduceIte]
      exact measurable_const
  have hF : Measurable fun ω => ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
      (fun j => gueBlock W m ω ⟨a + (n - j), by omega⟩) n)
        ((freeConj W 0)ᴴ * phFrame g (rS ω)))⁻¹‖ₑ ^ s :=
    greenPath_measurable_frameD_inv
      (greenPath_continuous_transferProd g _ (fun j => greenPath_continuous_gueBlock W m _) n)
      ((continuous_const.matrix_mul continuous_id).measurable.comp
        (greenPath_measurable_phFrame g hrSm hrSh)) s
  set sw : Fin n → Fin m := fun j => ⟨a + (n - j), by omega⟩ with hsw_def
  have hsw : Function.Injective sw := by
    intro i j h
    simp only [hsw_def, Fin.ext_iff] at h
    ext
    omega
  rw [lintegral_windowJoin W m n hsw hF]
  calc _ ≤ ∫⁻ _, ENNReal.ofReal (C * W * Real.exp (-c * n / (W * g ^ 2)))
        ∂(stdGauss {p : Fin m × Fin W × Fin W // p.1 ∉ Set.range sw}) := by
        refine lintegral_mono fun e => ?_
        have hT' : ∀ v, transferProd g ((max 1 g * E / g : ℝ) : ℂ)
            (fun j => gueBlock W m (windowJoin sw v e) ⟨a + (n - j), by omega⟩) n =
            transferProd g ((max 1 g * E / g : ℝ) : ℂ) (seqBlocks (gueBlock W n v)) n := by
          intro v
          refine greenPath_transferProd_congr g _ fun j hj => ?_
          simp only [seqBlocks, hj, ↓reduceDIte]
          exact gueBlock_windowJoin_apply hsw v e ⟨j, hj⟩
        have hR' : ∀ v, rS (windowJoin sw v e) = rS (windowJoin sw 0 e) := by
          intro v
          simp only [hrS]
          split_ifs
          · congr 1
            funext j
            refine gueBlock_windowJoin_of_not_mem sw v 0 e ?_
            rintro ⟨i, hi⟩
            simp only [hsw_def, Fin.ext_iff] at hi
            omega
          · rfl
        calc _ = ∫⁻ v, ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
                (seqBlocks (gueBlock W n v)) n)
              ((freeConj W 0)ᴴ * phFrame g (rS (windowJoin sw 0 e))))⁻¹‖ₑ ^ s ∂(μ W n) :=
              lintegral_congr fun v => by rw [hT' v, hR' v]
          _ ≤ _ := hT n hn E hE _ (isBoundaryFrame_phFrame hg0 (hrSh _))
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- (8.16) [uvg:eq:energyapriori] on a set of length at most `4`. -/
private lemma greenPath_boole {W L : ℕ} {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hA : A.IsHermitian) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {J₀ : Set ℝ}
    (hJ₀ : MeasurableSet J₀) (hJ4 : volume J₀ ≤ ENNReal.ofReal 4) (i j : Fin L) :
    ∫⁻ E in J₀, ‖blockOf (resolventMat A E) i j‖ₑ ^ p ≤
      ENNReal.ofReal (booleConst p * (W : ℝ) ^ 2 * 4) := by
  have hJf : volume J₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hJ4
  refine (lintegral_blockOf_resolventMat_le hA hp0 hp1 hJ₀ hJf i j).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hℓ : (volume J₀).toReal ≤ 4 := ENNReal.toReal_le_of_le_ofReal (by norm_num) hJ4
  have h4 : (volume J₀).toReal ^ (1 - p) ≤ 4 := by
    calc (volume J₀).toReal ^ (1 - p) ≤ (4 : ℝ) ^ (1 - p) :=
          Real.rpow_le_rpow ENNReal.toReal_nonneg hℓ (by linarith)
      _ ≤ (4 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := Real.rpow_one 4
  have hB : 0 ≤ booleConst p := by
    unfold booleConst
    exact div_nonneg (by positivity) (by linarith)
  gcongr

/-- `ab ≤ τ a² + τ⁻¹ b²` in `[0, ∞]` for `0 < τ < ∞`. -/
private lemma greenPath_mul_le {a b τ : ℝ≥0∞} (hτ0 : τ ≠ 0) (hτ : τ ≠ ⊤) :
    a * b ≤ τ * (a * a) + τ⁻¹ * (b * b) := by
  rcases le_total (τ * a) b with h | h
  · have ha : a ≤ τ⁻¹ * b := by
      calc a = τ⁻¹ * (τ * a) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hτ0 hτ, one_mul]
        _ ≤ τ⁻¹ * b := by gcongr
    calc a * b ≤ τ⁻¹ * b * b := by gcongr
      _ = τ⁻¹ * (b * b) := by rw [mul_assoc]
      _ ≤ _ := le_add_self
  · calc a * b ≤ a * (τ * a) := by gcongr
      _ = τ * (a * a) := by ring
      _ ≤ _ := le_self_add

/-- At a fixed energy `E` with `|E| ≤ E₀`, (8.15) [uvg:eq:boundary] and Theorem 11.1
[uvg:thm:transfer] give `𝔼‖G(a + n, a)‖^{s/2} ≤ τ C W e^{−cn/(Wg²)} + τ⁻¹ 𝔼(‖G(a, a)‖^s +
‖G(a + 1, a)‖^s)` for every `τ > 0`. -/
private theorem greenPath_fixed_energy {E₀ C c s : ℝ} {W : ℕ} {g : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hT : ∀ n : ℕ, 1 ≤ n → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ, IsBoundaryFrame Φ →
        ∫⁻ ω, ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
            (seqBlocks (gueBlock W n ω)) n) Φ)⁻¹‖ₑ ^ s ∂(μ W n) ≤
          ENNReal.ofReal (C * W * Real.exp (-c * n / (W * g ^ 2))))
    (hg0 : 0 < g)
    {m a n k : ℕ} (hm : m = a + (n + 1) + k) (hn : 1 ≤ n)
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (hR₀ : R₀.IsHermitian) {E : ℝ} (hE : |E| ≤ E₀)
    {τ : ℝ≥0∞} (hτ0 : τ ≠ 0) (hτ : τ ≠ ⊤) :
    ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E)
        ⟨a + n, by omega⟩ ⟨a, by omega⟩‖ₑ ^ (s / 2) ∂(μ W m) ≤
      τ * ENNReal.ofReal (C * W * Real.exp (-c * n / (W * g ^ 2))) +
        τ⁻¹ * ∫⁻ ω,
          (‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E)
            ⟨a, by omega⟩ ⟨a, by omega⟩‖ₑ ^ s +
          ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E)
            ⟨a + 1, by omega⟩ ⟨a, by omega⟩‖ₑ ^ s) ∂(μ W m) := by
  have hR := greenPath_ae_det g (W := W) (m := m)
    (s := fun j : Fin k => (⟨a + (n + 1) + j, by omega⟩ : Fin m))
    (fun i j h => Fin.ext (by simpa [Fin.ext_iff] using h)) 0 R₀ E
  have hL := greenPath_ae_det g (W := W) (m := m)
    (s := fun j : Fin a => (⟨j, by omega⟩ : Fin m))
    (fun i j h => Fin.ext (by simpa [Fin.ext_iff] using h)) L₀ 0 E
  have hs2 : (0 : ℝ) ≤ s / 2 := by linarith
  have hsq : ∀ u : ℝ≥0∞, u ^ s = u ^ (s / 2) * u ^ (s / 2) := fun u => by
    rw [← ENNReal.rpow_add_of_nonneg (x := u) _ _ hs2 hs2, add_halves]
  have hae : ∀ᵐ ω ∂(μ W m),
      ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E)
        ⟨a + n, by omega⟩ ⟨a, by omega⟩‖ₑ ^ (s / 2) ≤
      τ * ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun j => gueBlock W m ω ⟨a + (n - j), by omega⟩) n)
      ((freeConj W 0)ᴴ * phFrame g (if 0 < k then shiftFromRight g
        (fun j : Fin k => gueBlock W m ω ⟨a + (n + 1) + j, by omega⟩) R₀ E else R₀)))⁻¹‖ₑ ^ s +
        τ⁻¹ * (‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E)
            ⟨a, by omega⟩ ⟨a, by omega⟩‖ₑ ^ s +
          ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E)
            ⟨a + 1, by omega⟩ ⟨a, by omega⟩‖ₑ ^ s) := by
    filter_upwards [hR, hL] with ω h1 h2
    have hcmp := greenPath_comparison hg0 hm hn (gueBlock W m ω)
      (fun _ => gueBlock_isHermitian _ _ _ _) L₀ R₀ hR₀ E (fun _ => h1) (fun _ => h2)
    set Z := ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun j => gueBlock W m ω ⟨a + (n - j), by omega⟩) n)
      ((freeConj W 0)ᴴ * phFrame g (if 0 < k then shiftFromRight g
        (fun j : Fin k => gueBlock W m ω ⟨a + (n + 1) + j, by omega⟩) R₀ E else R₀)))⁻¹‖ₑ
      with hZ
    set G := resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E
    set A := ‖blockOf G ⟨a, by omega⟩ ⟨a, by omega⟩‖ₑ +
      ‖blockOf G ⟨a + 1, by omega⟩ ⟨a, by omega⟩‖ₑ with hA
    have he : ‖blockOf G ⟨a + n, by omega⟩ ⟨a, by omega⟩‖ₑ ≤ Z * A := by
      rw [hZ, hA, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hcmp
    calc _ ≤ (Z * A) ^ (s / 2) := ENNReal.rpow_le_rpow he hs2
      _ = Z ^ (s / 2) * A ^ (s / 2) := ENNReal.mul_rpow_of_nonneg _ _ hs2
      _ ≤ τ * Z ^ s + τ⁻¹ * A ^ s := by
          rw [hsq Z, hsq A]
          exact greenPath_mul_le hτ0 hτ
      _ ≤ _ := by
          gcongr
          exact ENNReal.rpow_add_le_add_rpow _ _ hs0.le hs1.le
  calc _ ≤ _ := lintegral_mono_ae hae
    _ = _ := by
      rw [lintegral_add_right _ ?_, lintegral_const_mul' _ _ hτ,
        lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hτ0)]
      exact ((greenPath_measurable_entry_sample g L₀ R₀ _ _ s E).add
        (greenPath_measurable_entry_sample g L₀ R₀ _ _ s E)).const_mul _
    _ ≤ _ := by
      gcongr
      exact greenPath_frame_moment hT hg0 hn hm R₀ hR₀ hE

/-- (8.16) [uvg:eq:energyapriori] for `‖G(i, i)‖^s + ‖G(j, i)‖^s`, integrated over the GUE
sample and over `J₀` with `|J₀| ≤ 4`. -/
private lemma greenPath_apriori_pair {W m : ℕ} {g : ℝ} {L₀ R₀ : Matrix (Fin W) (Fin W) ℂ}
    (hL₀ : L₀.IsHermitian) (hR₀ : R₀.IsHermitian) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {J₀ : Set ℝ} (hJ₀ : MeasurableSet J₀) (hJ4 : volume J₀ ≤ ENNReal.ofReal 4) (i j : Fin m) :
    ∫⁻ E in J₀, ∫⁻ ω,
      (‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E) i i‖ₑ ^ s +
      ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E) j i‖ₑ ^ s) ∂(μ W m) ≤
      ENNReal.ofReal (booleConst s * (W : ℝ) ^ 2 * 4) +
        ENNReal.ofReal (booleConst s * (W : ℝ) ^ 2 * 4) := by
  have hHerm : ∀ ω, (pathOp g (gueBlock W m ω) L₀ R₀).IsHermitian := fun ω =>
    pathOp_isHermitian g (fun _ => gueBlock_isHermitian _ _ _ _) hL₀ hR₀
  rw [lintegral_lintegral_swap (((greenPath_measurable_entry g L₀ R₀ i i s).add
    (greenPath_measurable_entry g L₀ R₀ j i s)).aemeasurable)]
  calc _ ≤ ∫⁻ _, ENNReal.ofReal (booleConst s * (W : ℝ) ^ 2 * 4) +
        ENNReal.ofReal (booleConst s * (W : ℝ) ^ 2 * 4) ∂(μ W m) := by
        refine lintegral_mono fun ω => ?_
        rw [lintegral_add_left (greenPath_measurable_entry_energy g L₀ R₀ i i s ω)]
        exact add_le_add (greenPath_boole (hHerm ω) hs0 hs1 hJ₀ hJ4 _ _)
          (greenPath_boole (hHerm ω) hs0 hs1 hJ₀ hJ4 _ _)
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- The real arithmetic closing the off-diagonal bound. -/
private lemma greenPath_arith {C c B W b n : ℝ} (hC : 0 < C) (hW : 1 ≤ W) :
    Real.exp (c / 2 * n / b) * (C * W * Real.exp (-c * n / b)) * 4 +
        (Real.exp (c / 2 * n / b))⁻¹ * (B * W ^ 2 * 4 + B * W ^ 2 * 4) ≤
      (4 * C + 8 * B) * W ^ 2 * Real.exp (-(c / 2) * n / b) := by
  have e1 : Real.exp (c / 2 * n / b) * Real.exp (-c * n / b) =
      Real.exp (-(c / 2) * n / b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e2 : (Real.exp (c / 2 * n / b))⁻¹ = Real.exp (-(c / 2) * n / b) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hWW : W ≤ W ^ 2 := by nlinarith
  have hex : 0 < Real.exp (-(c / 2) * n / b) := Real.exp_pos _
  calc Real.exp (c / 2 * n / b) * (C * W * Real.exp (-c * n / b)) * 4 +
        (Real.exp (c / 2 * n / b))⁻¹ * (B * W ^ 2 * 4 + B * W ^ 2 * 4) =
        4 * C * W * Real.exp (-(c / 2) * n / b) +
          8 * B * W ^ 2 * Real.exp (-(c / 2) * n / b) := by
        rw [e2, ← e1]
        ring
    _ ≤ 4 * C * W ^ 2 * Real.exp (-(c / 2) * n / b) +
          8 * B * W ^ 2 * Real.exp (-(c / 2) * n / b) := by
        gcongr
    _ = _ := by ring

/-- The integrated bound for `G(a + n, a)` with `n ≥ 1`, from (8.15) [uvg:eq:boundary],
Theorem 11.1 [uvg:thm:transfer] and (8.16) [uvg:eq:energyapriori], with `q = s/2`. -/
private theorem greenPath_offDiag_core {E₀ C c s : ℝ} {W : ℕ} {g : ℝ} (hE₀ : E₀ < 2) (hC : 0 < C)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hT : ∀ n : ℕ, 1 ≤ n → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ, IsBoundaryFrame Φ →
        ∫⁻ ω, ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
            (seqBlocks (gueBlock W n ω)) n) Φ)⁻¹‖ₑ ^ s ∂(μ W n) ≤
          ENNReal.ofReal (C * W * Real.exp (-c * n / (W * g ^ 2))))
    (hW1 : 1 ≤ W) (hg0 : 0 < g)
    {m a n k : ℕ} (hm : m = a + (n + 1) + k) (hn : 1 ≤ n)
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (hL₀ : L₀.IsHermitian) (hR₀ : R₀.IsHermitian)
    {J₀ : Set ℝ} (hJ₀ : MeasurableSet J₀) (hJsub : J₀ ⊆ Set.Icc (-E₀) E₀)
    (x y : Fin m) (hx : (x : ℕ) = a) (hy : (y : ℕ) = a + n) :
    ∫⁻ E in J₀, ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E) y x‖ₑ ^ (s / 2)
        ∂(μ W m) ≤
      ENNReal.ofReal ((4 * C + 8 * booleConst s) * (W : ℝ) ^ 2 *
        Real.exp (-(c / 2) * n / (W * g ^ 2))) := by
  have ha : a < m := by clear hx hy; omega
  have han : a + n < m := by clear hx hy; omega
  obtain rfl : x = ⟨a, ha⟩ := Fin.ext hx
  obtain rfl : y = ⟨a + n, han⟩ := Fin.ext hy
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hb : 0 < (W : ℝ) * g ^ 2 := by positivity
  have hτ : 0 < Real.exp (c / 2 * n / (W * g ^ 2)) := Real.exp_pos _
  have hτ0 : ENNReal.ofReal (Real.exp (c / 2 * n / (W * g ^ 2))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hτ).ne'
  have hBs : 0 ≤ booleConst s := by
    unfold booleConst
    exact div_nonneg (by positivity) (by linarith)
  have hJ4 : volume J₀ ≤ ENNReal.ofReal 4 :=
    (measure_mono hJsub).trans
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_le_ofReal (by linarith))
  have step1 := fun (E : ℝ) (hE : E ∈ J₀) => greenPath_fixed_energy hs0 hs1 hT hg0 hm hn
    L₀ R₀ hR₀ (abs_le.mpr ⟨(hJsub hE).1, (hJsub hE).2⟩) hτ0 ENNReal.ofReal_ne_top
  calc _ ≤ ∫⁻ E in J₀, (ENNReal.ofReal (Real.exp (c / 2 * n / (W * g ^ 2))) *
        ENNReal.ofReal (C * W * Real.exp (-c * n / (W * g ^ 2))) +
          (ENNReal.ofReal (Real.exp (c / 2 * n / (W * g ^ 2))))⁻¹ * ∫⁻ ω,
            (‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E)
              ⟨a, ha⟩ ⟨a, ha⟩‖ₑ ^ s +
            ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E)
              ⟨a + 1, by omega⟩ ⟨a, ha⟩‖ₑ ^ s) ∂(μ W m)) :=
        lintegral_mono_ae ((ae_restrict_iff' hJ₀).mpr (ae_of_all _ step1))
    _ = ENNReal.ofReal (Real.exp (c / 2 * n / (W * g ^ 2))) *
          ENNReal.ofReal (C * W * Real.exp (-c * n / (W * g ^ 2))) * volume J₀ +
          (ENNReal.ofReal (Real.exp (c / 2 * n / (W * g ^ 2))))⁻¹ * ∫⁻ E in J₀, ∫⁻ ω,
            (‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E)
              ⟨a, ha⟩ ⟨a, ha⟩‖ₑ ^ s +
            ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E)
              ⟨a + 1, by omega⟩ ⟨a, ha⟩‖ₑ ^ s) ∂(μ W m) := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hτ0)]
    _ ≤ ENNReal.ofReal (Real.exp (c / 2 * n / (W * g ^ 2))) *
          ENNReal.ofReal (C * W * Real.exp (-c * n / (W * g ^ 2))) * ENNReal.ofReal 4 +
          ENNReal.ofReal (Real.exp (c / 2 * n / (W * g ^ 2)))⁻¹ *
          (ENNReal.ofReal (booleConst s * (W : ℝ) ^ 2 * 4) +
            ENNReal.ofReal (booleConst s * (W : ℝ) ^ 2 * 4)) := by
        rw [ENNReal.ofReal_inv_of_pos hτ]
        gcongr
        exact greenPath_apriori_pair hL₀ hR₀ hs0 hs1 hJ₀ hJ4 _ _
    _ = ENNReal.ofReal (Real.exp (c / 2 * n / (W * g ^ 2)) *
          (C * W * Real.exp (-c * n / (W * g ^ 2))) * 4 +
          (Real.exp (c / 2 * n / (W * g ^ 2)))⁻¹ *
          (booleConst s * (W : ℝ) ^ 2 * 4 + booleConst s * (W : ℝ) ^ 2 * 4)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul hτ.le,
          ← ENNReal.ofReal_mul (p := Real.exp (c / 2 * n / (W * g ^ 2)) *
            (C * W * Real.exp (-c * n / (W * g ^ 2)))) (by positivity),
          ← ENNReal.ofReal_mul (inv_nonneg.mpr hτ.le),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (greenPath_arith hC hW1')

/-- (8.16) [uvg:eq:energyapriori] for a diagonal block, integrated over the GUE sample and over
`J₀` with `|J₀| ≤ 4`. -/
private lemma greenPath_diag {W m : ℕ} {g : ℝ} {L₀ R₀ : Matrix (Fin W) (Fin W) ℂ}
    (hL₀ : L₀.IsHermitian) (hR₀ : R₀.IsHermitian) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {J₀ : Set ℝ} (hJ₀ : MeasurableSet J₀) (hJ4 : volume J₀ ≤ ENNReal.ofReal 4) (x : Fin m) :
    ∫⁻ E in J₀, ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E) x x‖ₑ ^ p
        ∂(μ W m) ≤
      ENNReal.ofReal (booleConst p * (W : ℝ) ^ 2 * 4) := by
  rw [lintegral_lintegral_swap (greenPath_measurable_entry g L₀ R₀ x x p).aemeasurable]
  calc _ ≤ ∫⁻ _, ENNReal.ofReal (booleConst p * (W : ℝ) ^ 2 * 4) ∂(μ W m) :=
        lintegral_mono fun ω => greenPath_boole
          (pathOp_isHermitian g (fun _ => gueBlock_isHermitian _ _ _ _) hL₀ hR₀) hp0 hp1 hJ₀ hJ4
          x x
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- `‖G(x, y)‖ = ‖G(y, x)‖` at real energies, under the integrals. -/
private lemma greenPath_swap {W m : ℕ} {g : ℝ} {L₀ R₀ : Matrix (Fin W) (Fin W) ℂ}
    (hL₀ : L₀.IsHermitian) (hR₀ : R₀.IsHermitian) (J₀ : Set ℝ) (x y : Fin m) (p : ℝ) :
    ∫⁻ E in J₀, ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E) x y‖ₑ ^ p
        ∂(μ W m) =
      ∫⁻ E in J₀, ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E) y x‖ₑ ^ p
        ∂(μ W m) := by
  refine lintegral_congr fun E => lintegral_congr fun ω => ?_
  rw [blockOf_resolventMat_swap
      (pathOp_isHermitian g (fun _ => gueBlock_isHermitian _ _ _ _) hL₀ hR₀) E y x,
    enorm_eq_nnnorm, enorm_eq_nnnorm, Matrix.l2_opNNNorm_conjTranspose]

/-- The fixed-parameter core of Proposition 8.4 [up:prop:conversion] (ii): for `E₀ < 2`,
`s ∈ (0, 1)`, `W ≥ 1` and `g > 0`, the bound (8.12) [up:eq:negative-transfer-input] on `|E| ≤ E₀`
for all `n ≥ 1` gives, for all Hermitian endpoint shifts and measurable `J₀ ⊆ [-E₀, E₀]`,
`∫_{J₀} 𝔼‖G^{L₀,R₀}(x, y; E)‖^{s/2} dE ≤ K W² exp(-(c/2) |x - y| / (W g²))`, through (8.15)
[uvg:eq:boundary] and (8.16) [uvg:eq:energyapriori]. -/
theorem green_path_of_transfer {E₀ s C c : ℝ} {W : ℕ} {g : ℝ} (hE₀ : E₀ < 2) (hC : 0 < C)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hT : ∀ n : ℕ, 1 ≤ n → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ, IsBoundaryFrame Φ →
        ∫⁻ ω, ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
            (seqBlocks (gueBlock W n ω)) n) Φ)⁻¹‖ₑ ^ s ∂(μ W n) ≤
          ENNReal.ofReal (C * W * Real.exp (-c * n / (W * g ^ 2))))
    (hW1 : 1 ≤ W) (hg0 : 0 < g) (m : ℕ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ)
    (hL₀ : L₀.IsHermitian) (hR₀ : R₀.IsHermitian) {J₀ : Set ℝ} (hJ₀ : MeasurableSet J₀)
    (hJsub : J₀ ⊆ Set.Icc (-E₀) E₀) (x y : Fin m) :
    ∫⁻ E in J₀, ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) L₀ R₀) E) x y‖ₑ ^ (s / 2)
        ∂(μ W m) ≤
      ENNReal.ofReal ((4 * C + 8 * booleConst s + 4 * booleConst (s / 2)) * (W : ℝ) ^ 2 *
        Real.exp (-(c / 2) * |((x : ℕ) : ℝ) - (y : ℕ)| / (W * g ^ 2))) := by
  have hBs : 0 < booleConst s := by
    unfold booleConst
    exact div_pos (by positivity) (by linarith)
  have hBq : 0 < booleConst (s / 2) := by
    unfold booleConst
    exact div_pos (by positivity) (by linarith)
  have hJ4 : volume J₀ ≤ ENNReal.ofReal 4 :=
    (measure_mono hJsub).trans
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_le_ofReal (by linarith))
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have hxy' : (x : ℕ) < y := hxy
    rw [greenPath_swap hL₀ hR₀ J₀ x y]
    refine (greenPath_offDiag_core hE₀ hC hs0 hs1 hT hW1 hg0 (a := x) (n := y - x)
      (k := m - y - 1) (by omega) (by omega) L₀ R₀ hL₀ hR₀ hJ₀ hJsub x y rfl
      (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hd : |((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)| = (((y : ℕ) - x : ℕ) : ℝ) := by
      rw [Nat.cast_sub hxy'.le, abs_sub_comm, abs_of_nonneg (by
        have : ((x : ℕ) : ℝ) ≤ (y : ℕ) := by exact_mod_cast hxy'.le
        linarith)]
    rw [hd]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
      (Real.exp_pos _).le
  · rw [sub_self, abs_zero, mul_zero, zero_div, Real.exp_zero, mul_one]
    refine (greenPath_diag hL₀ hR₀ (by linarith) (by linarith) hJ₀ hJ4 x).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have := sq_nonneg (W : ℝ)
    nlinarith
  · have hxy' : (y : ℕ) < x := hxy
    refine (greenPath_offDiag_core hE₀ hC hs0 hs1 hT hW1 hg0 (a := y) (n := x - y)
      (k := m - x - 1) (by omega) (by omega) L₀ R₀ hL₀ hR₀ hJ₀ hJsub y x rfl
      (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hd : |((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)| = (((x : ℕ) - y : ℕ) : ℝ) := by
      rw [Nat.cast_sub hxy'.le, abs_of_nonneg (by
        have : ((y : ℕ) : ℝ) ≤ (x : ℕ) := by exact_mod_cast hxy'.le
        linarith)]
    rw [hd]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
      (Real.exp_pos _).le

end LSBA
