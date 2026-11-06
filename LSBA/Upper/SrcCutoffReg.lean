import LSBA.Upper.SrcCutoffPoint
import LSBA.Upper.ChainBridge
import LSBA.Upper.SmallGeneratorReg

/-!
# The cutoff family of Lemma 9.3 [su:lem:chosen-generator]

(9.84) [su:eq:construction-cutoff-goals] and Lemma 9.3 [su:lem:chosen-generator](ii), (v):
the family clauses `GenFamily` for `K̂ = K` of (9.18) [us:eq:normalize] and the cutoff `χ̂` of
Section 9.4.4 [su:sec:cutoff-estimates]. Every factor of `χ̂` depends on the active blocks
`4, …, q - 2` only, lies in `[0, 1]`, is a ratio homogeneous of degree zero in `v̂`, and is
invariant under the change (9.24) [su:eq:cut-generator-equivariance] by a unitary `U` with
`U (1 - P) = 1 - P`, because `R_j`, `R_{[j,5]}`, `R←_j`, `A`, `R̃`, `Q` and the active-chain matrix
are conjugated by `U` while `P` commutes with `U`. The cutoff is smooth on `{v̂ ≠ 0}`: each inverse
cutoff vanishes near the set where its inverse fails to exist, so the chain of inverses is smooth
wherever the product does not vanish identically, and the factor `‖v̂‖² ≤ 2 W^{20} ‖P v̂‖²` vanishes
near `P v̂ = 0`. On its topological support the construction is smooth (the open set of the
construction), the charts exist and the active blocks are bounded. The cutoff is jointly
measurable in `(R_4, ω, v̂)` for a measurable rule `R_4 ↦ P`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Smoothness of matrix expressions -/

section Tools

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : WithTop ℕ∞} {x : X}

/-- The inverse is `C^k` at a point where the argument is `C^k` and invertible. -/
private lemma SrcCutoffReg_cd_inv {n : Type*} [Fintype n] [DecidableEq n] {f : X → Matrix n n ℂ}
    (hf : ContDiffAt ℝ k f x) (hu : IsUnit (f x)) : ContDiffAt ℝ k (fun y => (f y)⁻¹) x := by
  have h1 := contDiffAt_ringInverse ℝ (n := k) hu.unit
  rw [hu.unit_spec] at h1
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  exact h1.comp x hf

/-- A matrix-valued map is `C^k` at a point iff all its entries are. -/
private lemma SrcCutoffReg_cd_matrix_iff {m : Type*} [Fintype m] [DecidableEq m]
    {Φ : X → Matrix m m ℂ} : ContDiffAt ℝ k Φ x ↔ ∀ i j, ContDiffAt ℝ k (fun y => Φ y i j) x := by
  let e : Matrix m m ℂ ≃L[ℝ] (m → m → ℂ) :=
    (Matrix.ofLinearEquiv ℝ).symm.toContinuousLinearEquiv
  rw [← e.comp_contDiffAt_iff, contDiffAt_pi]
  refine forall_congr' fun i => ?_
  rw [contDiffAt_pi]
  rfl

/-- The adjoint of a `C^k` matrix-valued map is `C^k`. -/
private lemma SrcCutoffReg_cd_conjTranspose {m : Type*} [Fintype m] [DecidableEq m]
    {A : X → Matrix m m ℂ} (hA : ContDiffAt ℝ k A x) : ContDiffAt ℝ k (fun y => (A y)ᴴ) x := by
  rw [SrcCutoffReg_cd_matrix_iff] at hA ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact Complex.conjCLE.contDiff.contDiffAt.comp x (hA j i)

/-- `y ↦ ‖M y‖²_HS` is `C^k` at `x` when `M` is. -/
private lemma SrcCutoffReg_cd_hsSq {m : Type*} [Fintype m] [DecidableEq m]
    {M : X → Matrix m m ℂ} (hM : ContDiffAt ℝ k M x) : ContDiffAt ℝ k (fun y => hsSq (M y)) x := by
  rw [SrcCutoffReg_cd_matrix_iff] at hM
  unfold hsSq
  exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => (hM a b).norm_sq ℝ

/-- `y ↦ ‖A(y) u(y)‖²` is `C^k` at `x` when `A` and `u` are. -/
private lemma SrcCutoffReg_cd_sumSq {W : ℕ} {A : X → Matrix (Fin W) (Fin W) ℂ}
    {u : X → Fin W → ℂ} (hA : ContDiffAt ℝ k A x) (hu : ContDiffAt ℝ k u x) :
    ContDiffAt ℝ k (fun y => ∑ i, ‖(A y *ᵥ u y) i‖ ^ 2) x := by
  rw [SrcCutoffReg_cd_matrix_iff] at hA
  rw [contDiffAt_pi] at hu
  refine ContDiffAt.sum fun i _ => ContDiffAt.norm_sq ℝ ?_
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiffAt.sum fun j _ => (hA i j).mul (hu j)

/-- `y ↦ ‖u(y)‖²` is `C^k` at `x` when `u` is. -/
private lemma SrcCutoffReg_cd_vecSq {W : ℕ} {u : X → Fin W → ℂ} (hu : ContDiffAt ℝ k u x) :
    ContDiffAt ℝ k (fun y => ∑ i, ‖u y i‖ ^ 2) x := by
  rw [contDiffAt_pi] at hu
  exact ContDiffAt.sum fun i _ => (hu i).norm_sq ℝ

/-- `y ↦ Re Tr M(y)` is `C^k` at `x` when `M` is. -/
private lemma SrcCutoffReg_cd_traceRe {m : Type*} [Fintype m] [DecidableEq m]
    {M : X → Matrix m m ℂ} (hM : ContDiffAt ℝ k M x) :
    ContDiffAt ℝ k (fun y => (M y).trace.re) x := by
  rw [SrcCutoffReg_cd_matrix_iff] at hM
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  exact ContDiffAt.sum fun i _ => Complex.reCLM.contDiff.contDiffAt.comp x (hM i i)

/-- The rank surrogate `rankSurr s (M y)` is `C^k` at `x` when `M` is and `M x + s²` is
invertible. -/
private lemma SrcCutoffReg_cd_rankSurr {m : Type*} [Fintype m] [DecidableEq m] {s : ℝ}
    {M : X → Matrix m m ℂ} (hM : ContDiffAt ℝ k M x)
    (hu : IsUnit (M x + ((s ^ 2 : ℝ) : ℂ) • 1)) :
    ContDiffAt ℝ k (fun y => rankSurr s (M y)) x := by
  unfold rankSurr
  exact contDiffAt_const.mul (SrcCutoffReg_cd_traceRe
    (hM.mul (SrcCutoffReg_cd_inv (hM.add contDiffAt_const) hu)))

/-- `normCut L Y⁻¹⁻¹ = normCut L Y` for every square matrix `Y`. -/
private lemma SrcCutoffReg_normCut_inv_inv {m : Type*} [Fintype m] [DecidableEq m] (L : ℝ)
    (Y : Matrix m m ℂ) : normCut L Y⁻¹⁻¹ = normCut L Y := by
  by_cases h : IsUnit Y
  · rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 h)]
  · simp only [normCut, Matrix.isUnit_nonsing_inv_iff, h, ↓reduceIte]

/-- `y ↦ normCut L (f y)⁻¹` is `C²` at `x` when `f` is and `L > 0`. -/
private lemma SrcCutoffReg_cd_normCut_inv {m : Type*} [Fintype m] [DecidableEq m] {L : ℝ}
    (hL : 0 < L) {f : X → Matrix m m ℂ} (hf : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 2 (fun y => normCut L (f y)⁻¹) x :=
  ((normCut_inv_spec hL).1.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp x hf

/-- `y ↦ normCut L (f y)` is `C²` at `x` when `f` is, `f x` is invertible and `L > 0`. -/
private lemma SrcCutoffReg_cd_normCut {m : Type*} [Fintype m] [DecidableEq m] {L : ℝ}
    (hL : 0 < L) {f : X → Matrix m m ℂ} (hf : ContDiffAt ℝ 2 f x) (hu : IsUnit (f x)) :
    ContDiffAt ℝ 2 (fun y => normCut L (f y)) x := by
  have h := SrcCutoffReg_cd_normCut_inv hL (SrcCutoffReg_cd_inv hf hu)
  simpa only [SrcCutoffReg_normCut_inv_inv] using h

end Tools

open scoped ComplexOrder in
/-- `Y* Y + s` is invertible for `s > 0`. -/
private lemma SrcCutoffReg_isUnit_gram_add {n : Type*} [Fintype n] [DecidableEq n]
    (Y : Matrix n n ℂ) {s : ℝ} (hs : 0 < s) : IsUnit (Yᴴ * Y + ((s : ℝ) : ℂ) • 1) := by
  have h1 : (((s : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hs)
  exact (Matrix.PosDef.posSemidef_add (Matrix.posSemidef_conjTranspose_mul_self Y) h1).isUnit

/-- Near a point where `f` is continuous and singular, `normCut L (f ·)⁻¹` vanishes identically
(`L > 0`). -/
private lemma SrcCutoffReg_normCut_vanish {Y : Type*} [TopologicalSpace Y] {m : Type*} [Fintype m]
    [DecidableEq m] {L : ℝ} (hL : 0 < L) {f : Y → Matrix m m ℂ} {y₀ : Y}
    (hf : ContinuousAt f y₀) (h : ¬ IsUnit (f y₀)) :
    (fun y => normCut L (f y)⁻¹) =ᶠ[nhds y₀] 0 := by
  have hns : f y₀ ∉ tsupport (fun X : Matrix m m ℂ => normCut L X⁻¹) :=
    fun hm => h ((normCut_inv_spec hL).2.1 _ hm).1
  exact (notMem_tsupport_iff_eventuallyEq.1 hns).comp_tendsto hf

/-! ### Smoothness of the chains in the sample -/

/-- Each block `ω ↦ gueBlock W q ω i` is a smooth (real-linear) function of the sample. -/
private lemma SrcCutoffReg_cd_gueBlock (W q : ℕ) (i : Fin q) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun ω : Ω W q => gueBlock W q ω i) := by
  rw [contDiff_iff_contDiffAt]
  intro ω₀
  rw [SrcCutoffReg_cd_matrix_iff]
  intro α β
  have hc : ∀ p : Fin q × Fin W × Fin W,
      ContDiff ℝ k (fun ω : Ω W q => ((ω p : ℝ) : ℂ)) := fun p =>
    Complex.ofRealCLM.contDiff.comp (contDiff_pi.1 contDiff_id p)
  simp only [gueBlock, Matrix.of_apply]
  split_ifs
  · exact ((hc _).div_const _).contDiffAt
  · exact (((hc _).add (contDiff_const.mul (hc _))).div_const _).contDiffAt
  · exact (((hc _).sub (contDiff_const.mul (hc _))).div_const _).contDiffAt

/-- The input sequence `ω ↦ blockSeq W q ω j` is smooth. -/
private lemma SrcCutoffReg_cd_blockSeq (W q j : ℕ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun ω : Ω W q => blockSeq W q ω j) := by
  unfold blockSeq
  by_cases hj : j < q
  · simp only [hj, ↓reduceDIte]
    exact SrcCutoffReg_cd_gueBlock W q ⟨j, hj⟩
  · simp only [hj, ↓reduceDIte]
    exact contDiff_const

/-- The recursion `R_{j+1} = (V_{j+1} - E - g² R_j)⁻¹` of (9.2) [su:eq:transported-normal] for
`j ≥ 4`. -/
private lemma SrcCutoffReg_chartR_succ {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {ω : Ω W q} {j : ℕ} (hj : 4 ≤ j) :
    chartR W g E q R ω (j + 1) =
      (blockSeq W q ω j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω j)⁻¹ := by
  simp only [chartR, show ¬ j < 4 by omega, ↓reduceIte]

/-- The graph coordinates `R_j` are `C^k` at `ω₀` when `R_5, …, R_j` are invertible there. -/
private lemma SrcCutoffReg_cd_chartR {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {ω₀ : Ω W q} {k : WithTop ℕ∞} :
    ∀ j, (∀ i, 5 ≤ i → i ≤ j → IsUnit (chartR W g E q R ω₀ i)) →
      ContDiffAt ℝ k (fun ω => chartR W g E q R ω j) ω₀
  | 0, _ => by
    simp only [chartR]
    exact contDiffAt_const
  | j + 1, hU => by
    by_cases h4 : j < 4
    · simp only [chartR, h4, ↓reduceIte]
      exact contDiffAt_const
    · have ih := SrcCutoffReg_cd_chartR (k := k) j fun i h5 hi => hU i h5 (by omega)
      have hu := hU (j + 1) (by omega) le_rfl
      simp only [SrcCutoffReg_chartR_succ (show 4 ≤ j by omega)] at hu ⊢
      rw [Matrix.isUnit_nonsing_inv_iff] at hu
      exact SrcCutoffReg_cd_inv ((((SrcCutoffReg_cd_blockSeq W q j).contDiffAt).sub
        contDiffAt_const).sub (ih.const_smul _)) hu

/-- The products `R_{[j,5]}` are `C^k` at `ω₀` when `R_5, …, R_j` are invertible there. -/
private lemma SrcCutoffReg_cd_chartProd {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {ω₀ : Ω W q} {k : WithTop ℕ∞} :
    ∀ j, (∀ i, 5 ≤ i → i ≤ j → IsUnit (chartR W g E q R ω₀ i)) →
      ContDiffAt ℝ k (fun ω => chartProd W g E q R ω j) ω₀
  | 0, _ => by
    simp only [chartProd]
    exact contDiffAt_const
  | j + 1, hU => by
    by_cases h4 : j < 4
    · simp only [chartProd, h4, ↓reduceIte]
      exact contDiffAt_const
    · simp only [chartProd, h4, ↓reduceIte]
      exact (SrcCutoffReg_cd_chartR (j + 1) hU).mul
        (SrcCutoffReg_cd_chartProd j fun i h5 hi => hU i h5 (by omega))

/-- The right-cavity inverses `cavR … m` are `C^k` at `ω₀` when `cavR … i`, `i ≤ m`, are
invertible there. -/
private lemma SrcCutoffReg_cd_cavR {W q : ℕ} {g E : ℝ} {ω₀ : Ω W q} {k : WithTop ℕ∞} :
    ∀ m, (∀ i, i ≤ m → IsUnit (cavR W g E q ω₀ i)) →
      ContDiffAt ℝ k (fun ω => cavR W g E q ω m) ω₀
  | 0, hU => by
    have hu := hU 0 le_rfl
    simp only [cavR] at hu ⊢
    rw [Matrix.isUnit_nonsing_inv_iff] at hu
    exact SrcCutoffReg_cd_inv
      (((SrcCutoffReg_cd_blockSeq W q _).contDiffAt).sub contDiffAt_const) hu
  | m + 1, hU => by
    have ih := SrcCutoffReg_cd_cavR (k := k) m fun i hi => hU i (by omega)
    have hu := hU (m + 1) le_rfl
    simp only [cavR] at hu ⊢
    rw [Matrix.isUnit_nonsing_inv_iff] at hu
    exact SrcCutoffReg_cd_inv ((((SrcCutoffReg_cd_blockSeq W q _).contDiffAt).sub
      contDiffAt_const).sub (ih.const_smul _)) hu

/-- The products `cavProd … m` are `C^k` at `ω₀` when `cavR … i`, `i < m`, are invertible
there. -/
private lemma SrcCutoffReg_cd_cavProd {W q : ℕ} {g E : ℝ} {ω₀ : Ω W q} {k : WithTop ℕ∞} :
    ∀ m, (∀ i, i < m → IsUnit (cavR W g E q ω₀ i)) →
      ContDiffAt ℝ k (fun ω => cavProd W g E q ω m) ω₀
  | 0, _ => by
    simp only [cavProd]
    exact contDiffAt_const
  | m + 1, hU => by
    simp only [cavProd]
    exact (SrcCutoffReg_cd_cavProd m fun i hi => hU i (by omega)).mul
      (SrcCutoffReg_cd_cavR m fun i hi => hU i (by omega))

/-- `A* A` is `C^k` at `ω₀` when the right-cavity inverses exist there. -/
private lemma SrcCutoffReg_cd_gram {W q : ℕ} {g E : ℝ} {ω₀ : Ω W q} {k : WithTop ℕ∞}
    (hK : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω₀ m)) :
    ContDiffAt ℝ k (fun ω => (cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) ω₀ := by
  have h := SrcCutoffReg_cd_cavProd (k := k) (g := g) (E := E) (q - 6) fun i hi =>
    hK i (by omega)
  exact (SrcCutoffReg_cd_conjTranspose h).mul h

/-- The matrix `V_5 - E - g² R_4 - g² R←_6` inverted in `R̃` is `C^k` at `ω₀` when the
right-cavity inverses exist there. -/
private lemma SrcCutoffReg_cd_cavResX {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {ω₀ : Ω W q} {k : WithTop ℕ∞} (hK : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω₀ m)) :
    ContDiffAt ℝ k (fun ω => blockSeq W q ω 4 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R -
      ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) ω₀ :=
  ((((SrcCutoffReg_cd_blockSeq W q 4).contDiffAt).sub contDiffAt_const).sub
    contDiffAt_const).sub ((SrcCutoffReg_cd_cavR (q - 7) hK).const_smul _)

/-- The active-chain matrix is smooth in the sample. -/
private lemma SrcCutoffReg_cd_activeMat {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {k : WithTop ℕ∞} : ContDiff ℝ k (fun ω : Ω W q => activeMat W g E q R ω) := by
  refine contDiff_iff_contDiffAt.2 fun ω₀ => ?_
  rw [SrcCutoffReg_cd_matrix_iff]
  intro a b
  simp only [activeMat, Matrix.of_apply]
  by_cases h1 : a.1 = b.1
  · simp only [h1, ↓reduceIte]
    exact (SrcCutoffReg_cd_matrix_iff.1 ((((SrcCutoffReg_cd_blockSeq W q
      ((b.1 : ℕ) + 4)).contDiffAt).sub contDiffAt_const).sub contDiffAt_const)) a.2 b.2
  · simp only [h1, ↓reduceIte]
    exact contDiffAt_const

/-! ### Dependence on the active blocks only -/

section Congr

variable {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ} {ω ω' : Ω W q}

/-- Samples with the same active blocks have the same inputs `V_{k+1}`, `4 ≤ k ≤ q - 2`. -/
private lemma SrcCutoffReg_blockSeq_congr
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q ω i = gueBlock W q ω' i)
    {k : ℕ} (h4 : 4 ≤ k) (hk : k + 2 ≤ q) : blockSeq W q ω k = blockSeq W q ω' k := by
  have hkq : k < q := by omega
  simp only [blockSeq, hkq, ↓reduceDIte]
  exact h ⟨k, hkq⟩ h4 hk

/-- The graph coordinates `R_j`, `j ≤ q - 1`, depend on the active blocks only. -/
private lemma SrcCutoffReg_chartR_congr
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q ω i = gueBlock W q ω' i) :
    ∀ j, j ≤ q - 1 → chartR W g E q R ω j = chartR W g E q R ω' j
  | 0, _ => rfl
  | j + 1, hj => by
    by_cases h4 : j < 4
    · simp only [chartR, h4, ↓reduceIte]
    · simp only [chartR, h4, ↓reduceIte, SrcCutoffReg_blockSeq_congr h (k := j) (by omega)
        (by omega), SrcCutoffReg_chartR_congr h j (by omega)]

/-- The products `R_{[j,5]}`, `j ≤ q - 1`, depend on the active blocks only. -/
private lemma SrcCutoffReg_chartProd_congr
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q ω i = gueBlock W q ω' i) :
    ∀ j, j ≤ q - 1 → chartProd W g E q R ω j = chartProd W g E q R ω' j
  | 0, _ => rfl
  | j + 1, hj => by
    by_cases h4 : j < 4
    · simp only [chartProd, h4, ↓reduceIte]
    · simp only [chartProd, h4, ↓reduceIte, SrcCutoffReg_chartR_congr h (j + 1) hj,
        SrcCutoffReg_chartProd_congr h j (by omega)]

/-- The right-cavity inverses `cavR … m`, `m ≤ q - 7`, depend on the active blocks only. -/
private lemma SrcCutoffReg_cavR_congr (hq : 7 ≤ q)
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q ω i = gueBlock W q ω' i) :
    ∀ m, m ≤ q - 7 → cavR W g E q ω m = cavR W g E q ω' m
  | 0, _ => by
    simp only [cavR, SrcCutoffReg_blockSeq_congr h (k := q - 2) (by omega) (by omega)]
  | m + 1, hm => by
    simp only [cavR, SrcCutoffReg_blockSeq_congr h (k := q - 3 - m) (by omega) (by omega),
      SrcCutoffReg_cavR_congr hq h m (by omega)]

/-- The products `cavProd … m`, `m ≤ q - 6`, depend on the active blocks only. -/
private lemma SrcCutoffReg_cavProd_congr (hq : 7 ≤ q)
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q ω i = gueBlock W q ω' i) :
    ∀ m, m ≤ q - 6 → cavProd W g E q ω m = cavProd W g E q ω' m
  | 0, _ => rfl
  | m + 1, hm => by
    simp only [cavProd, SrcCutoffReg_cavProd_congr hq h m (by omega),
      SrcCutoffReg_cavR_congr hq h m (by omega)]

/-- `R̃` depends on the active blocks only. -/
private lemma SrcCutoffReg_cavRes_congr (hq : 7 ≤ q)
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q ω i = gueBlock W q ω' i) :
    cavRes W g E q R ω = cavRes W g E q R ω' := by
  simp only [cavRes, SrcCutoffReg_blockSeq_congr h (k := 4) le_rfl (by omega),
    SrcCutoffReg_cavR_congr hq h (q - 7) le_rfl]

/-- The retained projection `Q` depends on the active blocks only. -/
private lemma SrcCutoffReg_retProj_congr (hq : 7 ≤ q) (t : ℝ)
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q ω i = gueBlock W q ω' i) :
    retProj W g E q R t ω = retProj W g E q R t ω' := by
  simp only [retProj, retSpec, SrcCutoffReg_cavRes_congr hq h,
    SrcCutoffReg_cavProd_congr hq h (q - 6) le_rfl]

/-- The active-chain matrix depends on the active blocks only. -/
private lemma SrcCutoffReg_activeMat_congr
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q ω i = gueBlock W q ω' i) :
    activeMat W g E q R ω = activeMat W g E q R ω' := by
  ext x y
  have hx := x.1.2
  simp only [activeMat, Matrix.of_apply,
    SrcCutoffReg_blockSeq_congr h (k := (x.1 : ℕ) + 4) (by omega) (by omega)]

end Congr

/-- The cutoff depends on the active blocks only. -/
private lemma SrcCutoffReg_srcCut_congr {W q : ℕ} {g E : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {c : CutLevels} {ω ω' : Ω W q} (hq : 7 ≤ q)
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q ω i = gueBlock W q ω' i)
    (w : Fin W → ℂ) : srcCut W g E q R P c ω w = srcCut W g E q R P c ω' w := by
  have e1 : ∏ j ∈ Finset.Icc 5 (q - 2), regCut W g (chartR W g E q R ω j) =
      ∏ j ∈ Finset.Icc 5 (q - 2), regCut W g (chartR W g E q R ω' j) :=
    Finset.prod_congr rfl fun j hj => by
      rw [SrcCutoffReg_chartR_congr h j (by simp only [Finset.mem_Icc] at hj; omega)]
  have e2 : ∏ m ∈ Finset.range (q - 6), normCut ((W : ℝ) ^ 6 / 2) (cavR W g E q ω m) =
      ∏ m ∈ Finset.range (q - 6), normCut ((W : ℝ) ^ 6 / 2) (cavR W g E q ω' m) :=
    Finset.prod_congr rfl fun m hm => by
      rw [SrcCutoffReg_cavR_congr hq h m (by simp only [Finset.mem_range] at hm; omega)]
  have e3 : ∏ i ∈ Finset.Icc 5 (q - 2), stepDown (hsSq (blockSeq W q ω i) / (W : ℝ) ^ 8) =
      ∏ i ∈ Finset.Icc 5 (q - 2), stepDown (hsSq (blockSeq W q ω' i) / (W : ℝ) ^ 8) :=
    Finset.prod_congr rfl fun i hi => by
      simp only [Finset.mem_Icc] at hi
      rw [SrcCutoffReg_blockSeq_congr h (k := i) (by omega) (by omega)]
  unfold srcCut matCut srcCutV
  rw [e1, e2, e3, SrcCutoffReg_chartR_congr h (q - 1) le_rfl, SrcCutoffReg_cavRes_congr hq h,
    SrcCutoffReg_activeMat_congr h, SrcCutoffReg_cavProd_congr hq h (q - 6) le_rfl,
    SrcCutoffReg_retProj_congr hq c.t h, SrcCutoffReg_blockSeq_congr h (k := 4) le_rfl (by omega),
    SrcCutoffReg_chartProd_congr h (q - 1) le_rfl]

/-- The generator depends on the active blocks only. -/
private lemma SrcCutoffReg_smallGen_congr {W q : ℕ} {g E t : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {ω ω' : Ω W q} (hq : 7 ≤ q)
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q ω i = gueBlock W q ω' i)
    (w : Fin W → ℂ) : smallGen W g E q R t P ω w = smallGen W g E q R t P ω' w := by
  simp only [smallGen, genScale, gen0, srcVec, SrcCutoffReg_retProj_congr hq t h,
    SrcCutoffReg_chartProd_congr h (q - 1) le_rfl]

/-! ### Invariance under unitary conjugation -/

section Conj

variable {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}

omit [DecidableEq n] in
/-- `‖A‖²_HS = Re Tr (A* A)`. -/
private lemma SrcCutoffReg_hsSq_eq (A : Matrix n n ℂ) : hsSq A = (Aᴴ * A).trace.re := by
  simp only [hsSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

private lemma SrcCutoffReg_conj_mul (hU : Uᴴ * U = 1) (M N : Matrix n n ℂ) :
    U * (M * N) * Uᴴ = U * M * Uᴴ * (U * N * Uᴴ) := by
  calc U * (M * N) * Uᴴ = U * M * (Uᴴ * U) * N * Uᴴ := by
        rw [hU, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = U * M * Uᴴ * (U * N * Uᴴ) := by simp only [Matrix.mul_assoc]

private lemma SrcCutoffReg_conj_inv (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (M : Matrix n n ℂ) :
    (U * M * Uᴴ)⁻¹ = U * M⁻¹ * Uᴴ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hU,
    Matrix.inv_eq_left_inv hU', Matrix.mul_assoc]

omit [DecidableEq n] in
private lemma SrcCutoffReg_conj_conjTranspose (M : Matrix n n ℂ) :
    (U * M * Uᴴ)ᴴ = U * Mᴴ * Uᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

private lemma SrcCutoffReg_conj_add_smul (hU' : U * Uᴴ = 1) (M : Matrix n n ℂ) (a : ℂ) :
    U * M * Uᴴ + a • 1 = U * (M + a • 1) * Uᴴ := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU']

private lemma SrcCutoffReg_conj_sub_smul (hU' : U * Uᴴ = 1) (M : Matrix n n ℂ) (a : ℂ) :
    U * M * Uᴴ - a • 1 = U * (M - a • 1) * Uᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU']

private lemma SrcCutoffReg_conj_pow (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (M : Matrix n n ℂ) :
    ∀ k : ℕ, (U * M * Uᴴ) ^ k = U * M ^ k * Uᴴ
  | 0 => by rw [pow_zero, pow_zero, Matrix.mul_one, hU']
  | k + 1 => by
    rw [pow_succ, pow_succ, SrcCutoffReg_conj_pow hU hU' M k, SrcCutoffReg_conj_mul hU]

private lemma SrcCutoffReg_trace_conj (hU : Uᴴ * U = 1) (M : Matrix n n ℂ) :
    (U * M * Uᴴ).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

private lemma SrcCutoffReg_hsSq_conj (hU : Uᴴ * U = 1) (M : Matrix n n ℂ) :
    hsSq (U * M * Uᴴ) = hsSq M := by
  rw [SrcCutoffReg_hsSq_eq, SrcCutoffReg_hsSq_eq, SrcCutoffReg_conj_conjTranspose,
    ← SrcCutoffReg_conj_mul hU, SrcCutoffReg_trace_conj hU]

private lemma SrcCutoffReg_normCut_conj (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (L : ℝ)
    (M : Matrix n n ℂ) : normCut L (U * M * Uᴴ) = normCut L M := by
  have hu : IsUnit U := ⟨⟨U, Uᴴ, hU', hU⟩, rfl⟩
  have hu' : IsUnit Uᴴ := ⟨⟨Uᴴ, U, hU, hU'⟩, rfl⟩
  have hiff : IsUnit (U * M * Uᴴ) ↔ IsUnit M := by
    refine ⟨fun h => ?_, fun h => (hu.mul h).mul hu'⟩
    have he : M = Uᴴ * (U * M * Uᴴ) * U := by
      simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
      rw [Matrix.mul_assoc, hU, Matrix.mul_one]
    rw [he]
    exact (hu'.mul h).mul hu
  simp only [normCut, hiff, SrcCutoffReg_hsSq_conj hU]

private lemma SrcCutoffReg_rankSurr_conj (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (s : ℝ)
    (M : Matrix n n ℂ) : rankSurr s (U * M * Uᴴ) = rankSurr s M := by
  unfold rankSurr
  rw [SrcCutoffReg_conj_add_smul hU', SrcCutoffReg_conj_inv hU hU', ← SrcCutoffReg_conj_mul hU,
    SrcCutoffReg_trace_conj hU]

end Conj

section ConjW

variable {W q : ℕ} {g E : ℝ} {R U : Matrix (Fin W) (Fin W) ℂ}

private lemma SrcCutoffReg_gsq_smul_herm (g : ℝ) {M : Matrix (Fin W) (Fin W) ℂ}
    (hM : M.IsHermitian) : (((g : ℂ) ^ 2) • M).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hM.eq]
  simp

private lemma SrcCutoffReg_conj_herm {M : Matrix (Fin W) (Fin W) ℂ} (hM : M.IsHermitian) :
    (U * M * Uᴴ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [SrcCutoffReg_conj_conjTranspose, hM.eq]

/-- The blocks of the changed sample (9.24) [su:eq:cut-generator-equivariance]. -/
private lemma SrcCutoffReg_gueBlock_srcAct (hRh : R.IsHermitian) (ω : Ω W q) :
    gueBlock W q (srcAct W q g R U ω) = fun i : Fin q =>
      if (i : ℕ) = 4 then U * (gueBlock W q ω i - ((g : ℂ) ^ 2) • R) * Uᴴ + ((g : ℂ) ^ 2) • R
      else if 5 ≤ (i : ℕ) ∧ (i : ℕ) + 2 ≤ q then U * gueBlock W q ω i * Uᴴ
      else gueBlock W q ω i := by
  unfold srcAct
  refine gueBlock_gueCoord W q _ fun i => ?_
  split_ifs
  · exact (SrcCutoffReg_conj_herm
      ((gueBlock_isHermitian W q ω i).sub (SrcCutoffReg_gsq_smul_herm g hRh))).add
      (SrcCutoffReg_gsq_smul_herm g hRh)
  · exact SrcCutoffReg_conj_herm (gueBlock_isHermitian W q ω i)
  · exact gueBlock_isHermitian W q ω i

private lemma SrcCutoffReg_blockSeq_srcAct_four (hRh : R.IsHermitian) (ω : Ω W q) (hq : 4 < q) :
    blockSeq W q (srcAct W q g R U ω) 4 =
      U * (blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R) * Uᴴ + ((g : ℂ) ^ 2) • R := by
  simp only [blockSeq, hq, ↓reduceDIte, SrcCutoffReg_gueBlock_srcAct hRh]
  simp

private lemma SrcCutoffReg_blockSeq_srcAct_mid (hRh : R.IsHermitian) (ω : Ω W q) {k : ℕ}
    (h5 : 5 ≤ k) (hk : k + 2 ≤ q) :
    blockSeq W q (srcAct W q g R U ω) k = U * blockSeq W q ω k * Uᴴ := by
  have hkq : k < q := by omega
  have h4 : k ≠ 4 := by omega
  simp only [blockSeq, hkq, ↓reduceDIte, SrcCutoffReg_gueBlock_srcAct hRh]
  simp [h4, h5, hk]

/-- Conjugation of a block matrix by `1 ⊗ U` conjugates every block by `U`. -/
private lemma SrcCutoffReg_kron_conj {m : ℕ} (U : Matrix (Fin W) (Fin W) ℂ)
    (B : Fin m → Fin m → Matrix (Fin W) (Fin W) ℂ) :
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U) *
      Matrix.of (fun x y : Fin m × Fin W => B x.1 y.1 x.2 y.2) *
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U)ᴴ =
      Matrix.of (fun x y : Fin m × Fin W => (U * B x.1 y.1 * Uᴴ) x.2 y.2) := by
  have h1 : ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U) *
      Matrix.of (fun x y : Fin m × Fin W => B x.1 y.1 x.2 y.2) =
      Matrix.of (fun x y : Fin m × Fin W => (U * B x.1 y.1) x.2 y.2) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
      ite_mul, Finset.sum_ite_eq]
  have h2 : Matrix.of (fun x y : Fin m × Fin W => (U * B x.1 y.1) x.2 y.2) *
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U)ᴴ =
      Matrix.of (fun x y : Fin m × Fin W => (U * B x.1 y.1 * Uᴴ) x.2 y.2) := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    ext ⟨a, i⟩ ⟨b, j⟩
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
      mul_ite, Finset.sum_ite_eq']
  rw [h1, h2]

/-- The blocks of the active-chain matrix. -/
private def SrcCutoffReg_actBlk (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) (k l : Fin (q - 5)) : Matrix (Fin W) (Fin W) ℂ :=
  if k = l then blockSeq W q ω ((k : ℕ) + 4) - (E : ℂ) • 1 -
    (if (k : ℕ) = 0 then ((g : ℂ) ^ 2) • R else 0)
  else if (k : ℕ) + 1 = (l : ℕ) ∨ (l : ℕ) + 1 = (k : ℕ) then (g : ℂ) • 1 else 0

private lemma SrcCutoffReg_activeMat_blk (ω : Ω W q) :
    activeMat W g E q R ω = Matrix.of (fun x y : Fin (q - 5) × Fin W =>
      SrcCutoffReg_actBlk W g E q R ω x.1 y.1 x.2 y.2) := by
  ext x y
  simp only [activeMat, SrcCutoffReg_actBlk, Matrix.of_apply]
  split_ifs <;> simp [Matrix.one_apply, *]

/-- Under (9.24) [su:eq:cut-generator-equivariance] the active-chain matrix is conjugated by
`1 ⊗ U`. -/
private lemma SrcCutoffReg_activeMat_srcAct (hRh : R.IsHermitian) (hU' : U * Uᴴ = 1)
    (ω : Ω W q) :
    activeMat W g E q R (srcAct W q g R U ω) =
      ((1 : Matrix (Fin (q - 5)) (Fin (q - 5)) ℂ) ⊗ₖ U) * activeMat W g E q R ω *
        ((1 : Matrix (Fin (q - 5)) (Fin (q - 5)) ℂ) ⊗ₖ U)ᴴ := by
  have hblk : ∀ k l : Fin (q - 5), SrcCutoffReg_actBlk W g E q R (srcAct W q g R U ω) k l =
      U * SrcCutoffReg_actBlk W g E q R ω k l * Uᴴ := by
    intro k l
    have hk := k.2
    unfold SrcCutoffReg_actBlk
    by_cases hkl : k = l
    · simp only [hkl, ↓reduceIte]
      by_cases h0 : (l : ℕ) = 0
      · simp only [h0, ↓reduceIte, zero_add]
        rw [SrcCutoffReg_blockSeq_srcAct_four hRh ω (by omega)]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, hU']
        abel
      · simp only [h0, ↓reduceIte, sub_zero]
        rw [SrcCutoffReg_blockSeq_srcAct_mid hRh ω (by omega) (by rw [← hkl]; omega)]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, hU']
    · simp only [hkl, ↓reduceIte]
      split_ifs
      · simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU']
      · simp
  rw [SrcCutoffReg_activeMat_blk, SrcCutoffReg_activeMat_blk, SrcCutoffReg_kron_conj]
  ext x y
  simp only [Matrix.of_apply, hblk]

end ConjW

/-- The cutoff is invariant under the change (9.24) [su:eq:cut-generator-equivariance] by a
unitary `U` with `U (1 - P) = 1 - P`. -/
private lemma SrcCutoffReg_srcCut_srcAct {W q : ℕ} {g E : ℝ} {R P U : Matrix (Fin W) (Fin W) ℂ}
    {c : CutLevels} (hq : 7 ≤ q) (hR : R.IsHermitian) (hP : P.IsHermitian)
    (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ) (hUP : U * (1 - P) = 1 - P) (ω : Ω W q)
    (w : Fin W → ℂ) :
    srcCut W g E q R P c (srcAct W q g R U ω) (U *ᵥ w) = srcCut W g E q R P c ω w := by
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  obtain ⟨hC, hK, hA, hT, -, hQ⟩ := srcAct_conj (g := g) (E := E) hq hR hU ω c.t
  have h1P : (1 - P) * Uᴴ = 1 - P := by
    have h := congrArg Matrix.conjTranspose hUP
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      hP.eq] at h
  have hconjP : U * (1 - P) * Uᴴ = 1 - P := by rw [hUP, h1P]
  have h2P : (1 - P) * U = 1 - P := by
    calc (1 - P) * U = (1 - P) * Uᴴ * U := by rw [h1P]
      _ = 1 - P := by rw [Matrix.mul_assoc, hU1, Matrix.mul_one]
  have hPU : P * U = U * P := by
    have h3 : U * (1 - P) = (1 - P) * U := by rw [hUP, h2P]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul] at h3
    exact (sub_right_injective h3).symm
  have hPv : ∀ v : Fin W → ℂ, P *ᵥ (U *ᵥ v) = U *ᵥ (P *ᵥ v) := fun v => by
    rw [Matrix.mulVec_mulVec, hPU, ← Matrix.mulVec_mulVec]
  have hMv : ∀ (M : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ),
      (U * M * Uᴴ) *ᵥ (U *ᵥ v) = U *ᵥ (M *ᵥ v) := fun M v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (U * M), hU1, Matrix.mul_one, Matrix.mulVec_mulVec]
  have hn : ∀ v : Fin W → ℂ, ∑ i, ‖(U *ᵥ v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := fun v => by
    have h : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU1,
        Matrix.one_mulVec]
    have hd : ∀ a : Fin W → ℂ, star a ⬝ᵥ a = ((∑ i, ‖a i‖ ^ 2 : ℝ) : ℂ) := fun a => by
      simp [dotProduct, Complex.conj_mul', Complex.ofReal_sum]
    rw [hd, hd] at h
    exact_mod_cast h
  have hreg : ∀ Y : Matrix (Fin W) (Fin W) ℂ, regCut W g (U * Y * Uᴴ) = regCut W g Y := fun Y => by
    unfold regCut
    rw [SrcCutoffReg_normCut_conj hU1 hU2, SrcCutoffReg_conj_conjTranspose,
      ← SrcCutoffReg_conj_mul hU1, SrcCutoffReg_rankSurr_conj hU1 hU2]
  have e1 : ∏ j ∈ Finset.Icc 5 (q - 2), regCut W g (chartR W g E q R (srcAct W q g R U ω) j) =
      ∏ j ∈ Finset.Icc 5 (q - 2), regCut W g (chartR W g E q R ω j) :=
    Finset.prod_congr rfl fun j hj => by
      simp only [Finset.mem_Icc] at hj
      rw [(hC j hj.1 (by omega)).1, hreg]
  have e2 : ∏ m ∈ Finset.range (q - 6),
      normCut ((W : ℝ) ^ 6 / 2) (cavR W g E q (srcAct W q g R U ω) m) =
      ∏ m ∈ Finset.range (q - 6), normCut ((W : ℝ) ^ 6 / 2) (cavR W g E q ω m) :=
    Finset.prod_congr rfl fun m hm => by
      simp only [Finset.mem_range] at hm
      rw [hK m (by omega), SrcCutoffReg_normCut_conj hU1 hU2]
  have e3 : ∏ i ∈ Finset.Icc 5 (q - 2),
      stepDown (hsSq (blockSeq W q (srcAct W q g R U ω) i) / (W : ℝ) ^ 8) =
      ∏ i ∈ Finset.Icc 5 (q - 2), stepDown (hsSq (blockSeq W q ω i) / (W : ℝ) ^ 8) :=
    Finset.prod_congr rfl fun i hi => by
      simp only [Finset.mem_Icc] at hi
      rw [SrcCutoffReg_blockSeq_srcAct_mid hR ω hi.1 (by omega), SrcCutoffReg_hsSq_conj hU1]
  set D : Matrix (Fin (q - 5) × Fin W) (Fin (q - 5) × Fin W) ℂ :=
    (1 : Matrix (Fin (q - 5)) (Fin (q - 5)) ℂ) ⊗ₖ U with hD
  have hD1 : Dᴴ * D = 1 := by
    rw [hD, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, hU1, Matrix.one_kronecker_one]
  have hD2 : D * Dᴴ = 1 := by
    rw [hD, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, hU2, Matrix.one_kronecker_one]
  have htr : U * retProj W g E q R c.t ω * Uᴴ * (1 - P) * (U * retProj W g E q R c.t ω * Uᴴ) =
      U * (retProj W g E q R c.t ω * (1 - P) * retProj W g E q R c.t ω) * Uᴴ := by
    conv_lhs => rw [← hconjP]
    rw [← SrcCutoffReg_conj_mul hU1, ← SrcCutoffReg_conj_mul hU1]
  unfold srcCut matCut srcCutV
  rw [e1, e2, e3, (hC (q - 1) (by omega) le_rfl).1, (hC (q - 1) (by omega) le_rfl).2, hT, hA, hQ,
    SrcCutoffReg_activeMat_srcAct hR hU2, SrcCutoffReg_blockSeq_srcAct_four hR ω (by omega),
    add_sub_cancel_right, htr, SrcCutoffReg_conj_pow hU1 hU2, SrcCutoffReg_trace_conj hU1,
    SrcCutoffReg_hsSq_conj hU1, SrcCutoffReg_conj_inv hD1 hD2,
    SrcCutoffReg_normCut_conj hD1 hD2, SrcCutoffReg_conj_conjTranspose,
    ← SrcCutoffReg_conj_mul hU1, SrcCutoffReg_rankSurr_conj hU1 hU2,
    SrcCutoffReg_conj_sub_smul hU2, SrcCutoffReg_conj_inv hU1 hU2]
  simp only [SrcCutoffReg_normCut_conj hU1 hU2, hPv, hMv, hn]

/-! ### Homogeneity in the source -/

/-- `‖a u‖² = |a|² ‖u‖²`. -/
private lemma SrcCutoffReg_sumSq_smul {W : ℕ} (a : ℂ) (u : Fin W → ℂ) :
    ∑ i, ‖(a • u) i‖ ^ 2 = ‖a‖ ^ 2 * ∑ i, ‖u i‖ ^ 2 := by
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]

/-- The cutoff is homogeneous of degree zero in the source. -/
private lemma SrcCutoffReg_srcCut_smul {W q : ℕ} {g E : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {c : CutLevels} (ω : Ω W q) (w : Fin W → ℂ) {a : ℂ} (ha : a ≠ 0) :
    srcCut W g E q R P c ω (a • w) = srcCut W g E q R P c ω w := by
  have hk : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 ha)
  have l1 : ∀ x y z : ℝ, z * (‖a‖ ^ 2 * x) / (‖a‖ ^ 2 * y) = z * x / y := fun x y z => by
    rw [mul_left_comm, mul_div_mul_left _ _ hk]
  have l2 : ∀ x y z : ℝ, ‖a‖ ^ 2 * x / (z * (‖a‖ ^ 2 * y)) = x / (z * y) := fun x y z => by
    rw [mul_left_comm z, mul_div_mul_left _ _ hk]
  unfold srcCut srcCutV
  simp only [Matrix.mulVec_smul, SrcCutoffReg_sumSq_smul, l1, l2]

/-! ### Smoothness of the cutoff off `v̂ = 0` -/

section Smooth

variable {W q : ℕ} {g E : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ} {c : CutLevels}

/-- A vanishing chain, cavity, `R̃` or gap factor makes the matrix cutoff vanish. -/
private lemma SrcCutoffReg_matCut_eq_zero (hq : 7 ≤ q) {ω : Ω W q}
    (h : (∃ j, 5 ≤ j ∧ j ≤ q - 1 ∧ normCut ((W : ℝ) ^ 6 / 2) (chartR W g E q R ω j) = 0) ∨
      (∃ m, m ≤ q - 7 ∧ normCut ((W : ℝ) ^ 6 / 2) (cavR W g E q ω m) = 0) ∨
      normCut ((W : ℝ) ^ 6 / 2) (cavRes W g E q R ω) = 0 ∨
      normCut c.Lgap ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) -
        ((c.t ^ 2 : ℝ) : ℂ) • 1)⁻¹ = 0) :
    matCut W g E q R P c ω = 0 := by
  rcases h with ⟨j, h5, hj, h0⟩ | ⟨m, hm, h0⟩ | h0 | h0
  · by_cases hjq : j = q - 1
    · rw [hjq] at h0
      unfold matCut
      rw [h0]
      simp
    · have hr : regCut W g (chartR W g E q R ω j) = 0 := by
        unfold regCut
        rw [h0, zero_mul]
      unfold matCut
      rw [Finset.prod_eq_zero (i := j) (by simp only [Finset.mem_Icc]; omega) hr]
      simp
  · unfold matCut
    rw [Finset.prod_eq_zero (Finset.mem_range.2 (show m < q - 6 by omega)) h0]
    simp
  · unfold matCut
    rw [h0]
    simp
  · unfold matCut
    rw [h0]
    simp

/-- At every sample either the chain inverses, the cavity inverses, `R̃` and `(A* A - t²)⁻¹`
exist, or the matrix cutoff vanishes on a neighbourhood. -/
private lemma SrcCutoffReg_dichotomy (hq : 7 ≤ q) (hW : 1 ≤ W) (hLgap : 0 < c.Lgap) (ω₀ : Ω W q) :
    ((∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω₀ j)) ∧
      (∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω₀ m)) ∧ IsUnit (cavRes W g E q R ω₀) ∧
      IsUnit ((cavProd W g E q ω₀ (q - 6))ᴴ * cavProd W g E q ω₀ (q - 6) -
        ((c.t ^ 2 : ℝ) : ℂ) • 1)) ∨
    (fun ω => matCut W g E q R P c ω) =ᶠ[nhds ω₀] 0 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hL : (0 : ℝ) < (W : ℝ) ^ 6 / 2 := by positivity
  have hA : ∀ j, j ≤ q - 1 → (∀ i, 5 ≤ i → i ≤ j → IsUnit (chartR W g E q R ω₀ i)) ∨
      (fun ω => matCut W g E q R P c ω) =ᶠ[nhds ω₀] 0 := by
    intro j
    induction j with
    | zero => exact fun _ => Or.inl fun i h5 hi => by omega
    | succ j ih =>
      intro hj
      rcases ih (by omega) with hU | hz
      · by_cases hj4 : j < 4
        · exact Or.inl fun i h5 hi => by omega
        by_cases hu : IsUnit (chartR W g E q R ω₀ (j + 1))
        · refine Or.inl fun i h5 hi => ?_
          rcases Nat.lt_or_ge i (j + 1) with h | h
          · exact hU i h5 (by omega)
          · rwa [show i = j + 1 by omega]
        · right
          have hc : ContinuousAt (fun ω => blockSeq W q ω j - (E : ℂ) • 1 -
              ((g : ℂ) ^ 2) • chartR W g E q R ω j) ω₀ :=
            ((((SrcCutoffReg_cd_blockSeq (k := 0) W q j).contDiffAt).sub contDiffAt_const).sub
              ((SrcCutoffReg_cd_chartR (k := 0) j hU).const_smul _)).continuousAt
          rw [SrcCutoffReg_chartR_succ (by omega), Matrix.isUnit_nonsing_inv_iff] at hu
          filter_upwards [SrcCutoffReg_normCut_vanish hL hc hu] with ω hω
          refine SrcCutoffReg_matCut_eq_zero hq (Or.inl ⟨j + 1, by omega, hj, ?_⟩)
          rw [SrcCutoffReg_chartR_succ (by omega)]
          exact hω
      · exact Or.inr hz
  have hB : ∀ m, m ≤ q - 7 → (∀ i, i ≤ m → IsUnit (cavR W g E q ω₀ i)) ∨
      (fun ω => matCut W g E q R P c ω) =ᶠ[nhds ω₀] 0 := by
    intro m
    induction m with
    | zero =>
      intro hm
      by_cases hu : IsUnit (cavR W g E q ω₀ 0)
      · exact Or.inl fun i hi => by rwa [show i = 0 by omega]
      · right
        have hc : ContinuousAt (fun ω => blockSeq W q ω (q - 2) - (E : ℂ) • 1) ω₀ :=
          (((SrcCutoffReg_cd_blockSeq (k := 0) W q _).contDiffAt).sub
            contDiffAt_const).continuousAt
        simp only [cavR, Matrix.isUnit_nonsing_inv_iff] at hu
        filter_upwards [SrcCutoffReg_normCut_vanish hL hc hu] with ω hω
        exact SrcCutoffReg_matCut_eq_zero hq (Or.inr (Or.inl ⟨0, hm, hω⟩))
    | succ m ih =>
      intro hm
      rcases ih (by omega) with hU | hz
      · by_cases hu : IsUnit (cavR W g E q ω₀ (m + 1))
        · refine Or.inl fun i hi => ?_
          rcases Nat.lt_or_ge i (m + 1) with h | h
          · exact hU i (by omega)
          · rwa [show i = m + 1 by omega]
        · right
          have hc : ContinuousAt (fun ω => blockSeq W q ω (q - 3 - m) - (E : ℂ) • 1 -
              ((g : ℂ) ^ 2) • cavR W g E q ω m) ω₀ :=
            ((((SrcCutoffReg_cd_blockSeq (k := 0) W q _).contDiffAt).sub contDiffAt_const).sub
              ((SrcCutoffReg_cd_cavR (k := 0) m hU).const_smul _)).continuousAt
          simp only [cavR, Matrix.isUnit_nonsing_inv_iff] at hu
          filter_upwards [SrcCutoffReg_normCut_vanish hL hc hu] with ω hω
          exact SrcCutoffReg_matCut_eq_zero hq (Or.inr (Or.inl ⟨m + 1, hm, hω⟩))
      · exact Or.inr hz
  rcases hA (q - 1) le_rfl with hC | hz
  swap
  · exact Or.inr hz
  rcases hB (q - 7) le_rfl with hK | hz
  swap
  · exact Or.inr hz
  have hK' : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω₀ m) := fun m hm => hK m hm
  by_cases hT : IsUnit (cavRes W g E q R ω₀)
  swap
  · right
    have hc := (SrcCutoffReg_cd_cavResX (k := 0) (R := R) hK').continuousAt
    unfold cavRes at hT
    rw [Matrix.isUnit_nonsing_inv_iff] at hT
    filter_upwards [SrcCutoffReg_normCut_vanish hL hc hT] with ω hω
    exact SrcCutoffReg_matCut_eq_zero hq (Or.inr (Or.inr (Or.inl hω)))
  by_cases hG : IsUnit ((cavProd W g E q ω₀ (q - 6))ᴴ * cavProd W g E q ω₀ (q - 6) -
      ((c.t ^ 2 : ℝ) : ℂ) • 1)
  · exact Or.inl ⟨fun j h5 hj => hC j h5 hj, hK', hT, hG⟩
  · right
    have hc := ((SrcCutoffReg_cd_gram (k := 0) (g := g) (E := E) hK').sub
      (contDiffAt_const (c := ((c.t ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)))).continuousAt
    filter_upwards [SrcCutoffReg_normCut_vanish hLgap hc hG] with ω hω
    exact SrcCutoffReg_matCut_eq_zero hq (Or.inr (Or.inr (Or.inr hω)))

/-- `R̃` is `C^k` at `ω₀` when the right-cavity inverses and `R̃` exist there. -/
private lemma SrcCutoffReg_cd_cavRes {ω₀ : Ω W q} {k : WithTop ℕ∞}
    (hK : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω₀ m)) (hT : IsUnit (cavRes W g E q R ω₀)) :
    ContDiffAt ℝ k (fun ω => cavRes W g E q R ω) ω₀ := by
  unfold cavRes at hT ⊢
  rw [Matrix.isUnit_nonsing_inv_iff] at hT
  exact SrcCutoffReg_cd_inv (SrcCutoffReg_cd_cavResX hK) hT

/-- The retained projection is `C²` at a sample where the cavity inverses, `R̃` and
`(A* A - t²)⁻¹` exist. -/
private lemma SrcCutoffReg_cd_retProj (hq : 7 ≤ q) (t : ℝ) {ω₀ : Ω W q}
    (hK : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω₀ m)) (hT : IsUnit (cavRes W g E q R ω₀))
    (hG : IsUnit ((cavProd W g E q ω₀ (q - 6))ᴴ * cavProd W g E q ω₀ (q - 6) -
      ((t ^ 2 : ℝ) : ℂ) • 1)) :
    ContDiffAt ℝ 2 (fun ω => retProj W g E q R t ω) ω₀ := by
  have e1 : ∀ᶠ ω in nhds ω₀, ∀ m ∈ Set.Iic (q - 7), IsUnit (cavR W g E q ω m) := by
    refine (Filter.eventually_all_finite (Set.finite_Iic _)).2 fun m hm => ?_
    have hm' : m ≤ q - 7 := hm
    exact ((SrcCutoffReg_cd_cavR (k := 0) m fun i hi => hK i (by omega)).continuousAt
      ).eventually_mem (Units.isOpen.mem_nhds (hK m hm'))
  have e2 : ∀ᶠ ω in nhds ω₀, IsUnit (cavRes W g E q R ω) :=
    ((SrcCutoffReg_cd_cavRes (k := 0) hK hT).continuousAt).eventually_mem
      (Units.isOpen.mem_nhds hT)
  have e3 : ∀ᶠ ω in nhds ω₀, IsUnit ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) -
      ((t ^ 2 : ℝ) : ℂ) • 1) :=
    (((SrcCutoffReg_cd_gram (k := 0) (g := g) (E := E) hK).sub
      (contDiffAt_const (c := ((t ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)))).continuousAt
      ).eventually_mem (Units.isOpen.mem_nhds hG)
  have hmem : {ω | (∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m)) ∧ IsUnit (cavRes W g E q R ω) ∧
      IsUnit ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) -
        ((t ^ 2 : ℝ) : ℂ) • 1)} ∈ nhds ω₀ := by
    filter_upwards [e1, e2, e3] with ω h1 h2 h3
    exact ⟨fun m hm => h1 m hm, h2, h3⟩
  exact ((contDiffOn_retProj hq g E R t).contDiffAt hmem).of_le (WithTop.coe_le_coe.mpr le_top)

/-- The matrix cutoff is `C²` at a sample where the chain inverses, the cavity inverses, `R̃` and
`(A* A - t²)⁻¹` exist. -/
private lemma SrcCutoffReg_cd_matCut (hq : 7 ≤ q) (hW : 1 ≤ W) (hg : 0 < g) (ht : 0 < c.t)
    (hLgap : 0 < c.Lgap) {ω₀ : Ω W q}
    (hC : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω₀ j))
    (hK : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω₀ m)) (hT : IsUnit (cavRes W g E q R ω₀))
    (hG : IsUnit ((cavProd W g E q ω₀ (q - 6))ᴴ * cavProd W g E q ω₀ (q - 6) -
      ((c.t ^ 2 : ℝ) : ℂ) • 1)) :
    ContDiffAt ℝ 2 (fun ω => matCut W g E q R P c ω) ω₀ := by
  obtain ⟨-, -, hSD, -, -, -, -, -⟩ := step_spec
  have hD : ContDiff ℝ 2 stepDown := hSD.of_le (WithTop.coe_le_coe.mpr le_top)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hL : (0 : ℝ) < (W : ℝ) ^ 6 / 2 := by positivity
  have hCR : ∀ j, j ≤ q - 1 → ContDiffAt ℝ 2 (fun ω => chartR W g E q R ω j) ω₀ := fun j hj =>
    SrcCutoffReg_cd_chartR j fun i h5 hi => hC i h5 (by omega)
  have hQ := SrcCutoffReg_cd_retProj (R := R) hq c.t hK hT hG
  have f1 : ContDiffAt ℝ 2 (fun ω =>
      ∏ j ∈ Finset.Icc 5 (q - 2), regCut W g (chartR W g E q R ω j)) ω₀ := by
    refine contDiffAt_prod fun j hj => ?_
    simp only [Finset.mem_Icc] at hj
    have h1 := hCR j (by omega)
    have hu : IsUnit ((chartR W g E q R ω₀ j)ᴴ * chartR W g E q R ω₀ j +
        ((g⁻¹ ^ 2 : ℝ) : ℂ) • 1) := SrcCutoffReg_isUnit_gram_add _ (by positivity)
    unfold regCut
    exact (SrcCutoffReg_cd_normCut hL h1 (hC j hj.1 (by omega))).mul (hD.contDiffAt.comp ω₀
      ((contDiffAt_const.mul (SrcCutoffReg_cd_rankSurr
        ((SrcCutoffReg_cd_conjTranspose h1).mul h1) hu)).div_const _))
  have f2 : ContDiffAt ℝ 2 (fun ω =>
      normCut ((W : ℝ) ^ 6 / 2) (chartR W g E q R ω (q - 1))) ω₀ :=
    SrcCutoffReg_cd_normCut hL (hCR (q - 1) le_rfl) (hC (q - 1) (by omega) le_rfl)
  have f3 : ContDiffAt ℝ 2 (fun ω =>
      ∏ m ∈ Finset.range (q - 6), normCut ((W : ℝ) ^ 6 / 2) (cavR W g E q ω m)) ω₀ := by
    refine contDiffAt_prod fun m hm => ?_
    simp only [Finset.mem_range] at hm
    exact SrcCutoffReg_cd_normCut hL (SrcCutoffReg_cd_cavR m fun i hi => hK i (by omega))
      (hK m (by omega))
  have f4 : ContDiffAt ℝ 2 (fun ω => normCut ((W : ℝ) ^ 6 / 2) (cavRes W g E q R ω)) ω₀ :=
    SrcCutoffReg_cd_normCut hL (SrcCutoffReg_cd_cavRes hK hT) hT
  have f5 : ContDiffAt ℝ 2 (fun ω =>
      normCut ((W : ℝ) ^ 6 / 2) (activeMat W g E q R ω)⁻¹) ω₀ :=
    SrcCutoffReg_cd_normCut_inv hL SrcCutoffReg_cd_activeMat.contDiffAt
  have f6 : ContDiffAt ℝ 2 (fun ω => normCut c.Lgap ((cavProd W g E q ω (q - 6))ᴴ *
      cavProd W g E q ω (q - 6) - ((c.t ^ 2 : ℝ) : ℂ) • 1)⁻¹) ω₀ :=
    SrcCutoffReg_cd_normCut_inv hLgap ((SrcCutoffReg_cd_gram hK).sub contDiffAt_const)
  have f7 : ContDiffAt ℝ 2 (fun ω => stepDown (rankSurr c.t ((cavProd W g E q ω (q - 6))ᴴ *
      cavProd W g E q ω (q - 6)) / c.Lrk)) ω₀ :=
    hD.contDiffAt.comp ω₀ ((SrcCutoffReg_cd_rankSurr (SrcCutoffReg_cd_gram hK)
      (SrcCutoffReg_isUnit_gram_add _ (by positivity))).div_const _)
  have f8 : ContDiffAt ℝ 2 (fun ω => stepDown (2 * 8 ^ c.kP * ((retProj W g E q R c.t ω *
      (1 - P) * retProj W g E q R c.t ω) ^ c.kP).trace.re)) ω₀ :=
    hD.contDiffAt.comp ω₀ (contDiffAt_const.mul (SrcCutoffReg_cd_traceRe
      (((hQ.mul contDiffAt_const).mul hQ).pow _)))
  have f9 : ContDiffAt ℝ 2 (fun ω =>
      stepDown (hsSq (blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R) / (W : ℝ) ^ 8)) ω₀ :=
    hD.contDiffAt.comp ω₀ ((SrcCutoffReg_cd_hsSq
      ((SrcCutoffReg_cd_blockSeq W q 4).contDiffAt.sub contDiffAt_const)).div_const _)
  have f10 : ContDiffAt ℝ 2 (fun ω =>
      ∏ i ∈ Finset.Icc 5 (q - 2), stepDown (hsSq (blockSeq W q ω i) / (W : ℝ) ^ 8)) ω₀ :=
    contDiffAt_prod fun i _ => hD.contDiffAt.comp ω₀ ((SrcCutoffReg_cd_hsSq
      (SrcCutoffReg_cd_blockSeq W q i).contDiffAt).div_const _)
  unfold matCut
  exact (((((((((f1.mul f2).mul f3).mul f4).mul f5).mul f6).mul f7).mul f8).mul f9).mul f10)

/-- `‖v‖² > 0` for `v ≠ 0`. -/
private lemma SrcCutoffReg_sumSq_pos {x : Fin W → ℂ} (hx : x ≠ 0) : 0 < ∑ i, ‖x i‖ ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  have hi' : 0 < ‖x i‖ ^ 2 := by
    have : x i ≠ 0 := hi
    positivity
  exact lt_of_lt_of_le hi' (Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i))

/-- The source factor is `C²` at `(ω₀, v₀)` when `v₀ ≠ 0`, `P v₀ ≠ 0` and the chain inverses,
the cavity inverses, `R̃` and `(A* A - t²)⁻¹` exist at `ω₀`. -/
private lemma SrcCutoffReg_cd_srcCutV (hq : 7 ≤ q) (hLov : 0 < c.Lov) (hkOut : 0 < c.kOut)
    {ω₀ : Ω W q} {v₀ : Fin W → ℂ}
    (hC : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω₀ j))
    (hK : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω₀ m)) (hT : IsUnit (cavRes W g E q R ω₀))
    (hG : IsUnit ((cavProd W g E q ω₀ (q - 6))ᴴ * cavProd W g E q ω₀ (q - 6) -
      ((c.t ^ 2 : ℝ) : ℂ) • 1))
    (hv : 0 < ∑ i, ‖v₀ i‖ ^ 2) (hPv : 0 < ∑ i, ‖(P *ᵥ v₀) i‖ ^ 2) :
    ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => srcCutV W g E q R P c p.1 p.2) (ω₀, v₀) := by
  obtain ⟨-, -, hSD, hSU, -, -, -, -⟩ := step_spec
  have hD : ContDiff ℝ 2 stepDown := hSD.of_le (WithTop.coe_le_coe.mpr le_top)
  have hU : ContDiff ℝ 2 stepUp := hSU.of_le (WithTop.coe_le_coe.mpr le_top)
  set p₀ : Ω W q × (Fin W → ℂ) := (ω₀, v₀)
  have hQ : ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => retProj W g E q R c.t p.1) p₀ :=
    (SrcCutoffReg_cd_retProj hq c.t hK hT hG).comp p₀ contDiffAt_fst
  have hCh : ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) =>
      chartProd W g E q R p.1 (q - 1)) p₀ :=
    (SrcCutoffReg_cd_chartProd (q - 1) fun i h5 hi => hC i h5 hi).comp p₀ contDiffAt_fst
  have hV : ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => p.2) p₀ := contDiffAt_snd
  have hPV : ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => P *ᵥ p.2) p₀ := by
    have h := SrcCutoffReg_cd_matrix_iff.1 (contDiffAt_const (c := P) (x := p₀) (n := 2))
    rw [contDiffAt_pi] at hV ⊢
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact ContDiffAt.sum fun j _ => (h i j).mul (hV j)
  have sV := SrcCutoffReg_cd_vecSq hV
  have sP := SrcCutoffReg_cd_sumSq (contDiffAt_const (c := P)) hV
  have sQ := SrcCutoffReg_cd_sumSq hQ hV
  have sQP := SrcCutoffReg_cd_sumSq hQ hPV
  have sC := SrcCutoffReg_cd_sumSq hCh hV
  have n1 : c.Lov * ∑ i, ‖(P *ᵥ v₀) i‖ ^ 2 ≠ 0 := by positivity
  have n2 : c.kOut ^ 2 * ∑ i, ‖(P *ᵥ v₀) i‖ ^ 2 ≠ 0 := by positivity
  unfold srcCutV
  exact (((hU.contDiffAt.comp p₀ ((contDiffAt_const.mul sP).div sV hv.ne')).mul
    (hD.contDiffAt.comp p₀ (sQ.div (contDiffAt_const.mul sP) n1))).mul
    (hD.contDiffAt.comp p₀ ((contDiffAt_const.mul sQP).div sP hPv.ne'))).mul
    (hU.contDiffAt.comp p₀ (sC.div (contDiffAt_const.mul sP) n2))

/-- The cutoff is `C²` at every `(ω₀, v₀)` with `v₀ ≠ 0`. -/
private lemma SrcCutoffReg_cd_srcCut (hq : 7 ≤ q) (hW : 1 ≤ W) (hg : 0 < g) (ht : 0 < c.t)
    (hLov : 0 < c.Lov) (hkOut : 0 < c.kOut) (hLgap : 0 < c.Lgap) (p₀ : Ω W q × (Fin W → ℂ))
    (hp : p₀.2 ≠ 0) :
    ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => srcCut W g E q R P c p.1 p.2) p₀ := by
  obtain ⟨ω₀, v₀⟩ := p₀
  obtain ⟨-, -, -, -, -, hle, -, -⟩ := step_spec
  have hv := SrcCutoffReg_sumSq_pos hp
  by_cases hr : 2 * (W : ℝ) ^ 20 * (∑ i, ‖(P *ᵥ v₀) i‖ ^ 2) / ∑ i, ‖v₀ i‖ ^ 2 < 1
  · have hc : ContinuousAt (fun p : Ω W q × (Fin W → ℂ) =>
        2 * (W : ℝ) ^ 20 * (∑ i, ‖(P *ᵥ p.2) i‖ ^ 2) / ∑ i, ‖p.2 i‖ ^ 2) (ω₀, v₀) :=
      ((contDiffAt_const.mul (SrcCutoffReg_cd_sumSq (k := 0) (contDiffAt_const (c := P))
        contDiffAt_snd)).div (SrcCutoffReg_cd_vecSq contDiffAt_snd) hv.ne').continuousAt
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hc.eventually (Iio_mem_nhds hr)] with p hp1
    unfold srcCut srcCutV
    rw [(hle _ (le_of_lt hp1)).2]
    simp
  · have hPv : 0 < ∑ i, ‖(P *ᵥ v₀) i‖ ^ 2 := by
      by_contra h0
      have h00 : ∑ i, ‖(P *ᵥ v₀) i‖ ^ 2 = 0 :=
        le_antisymm (not_lt.1 h0) (Finset.sum_nonneg fun i _ => by positivity)
      rw [h00, mul_zero, zero_div] at hr
      exact hr one_pos
    rcases SrcCutoffReg_dichotomy (R := R) (P := P) (c := c) (g := g) (E := E) hq hW hLgap ω₀ with
      ⟨hC, hK, hT, hG⟩ | hz
    · unfold srcCut
      exact ((SrcCutoffReg_cd_matCut hq hW hg ht hLgap hC hK hT hG).comp (ω₀, v₀)
        contDiffAt_fst).mul (SrcCutoffReg_cd_srcCutV hq hLov hkOut hC hK hT hG hv hPv)
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hz.comp_tendsto (continuousAt_fst (p := (ω₀, v₀)))] with p hp1
      simp only [Function.comp_apply, Pi.zero_apply] at hp1
      unfold srcCut
      rw [hp1, zero_mul]

/-- `‖A‖ ≤ ‖A‖_HS`. -/
private lemma SrcCutoffReg_norm_le_sqrt_hsSq (A : Matrix (Fin W) (Fin W) ℂ) :
    ‖A‖ ≤ Real.sqrt (hsSq A) := by
  have h0 : 0 ≤ hsSq A := by unfold hsSq; positivity
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  change ‖Matrix.toEuclideanLin A x‖ ≤ _ * ‖x‖
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul h0]
  refine Real.sqrt_le_sqrt ?_
  unfold hsSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ‖(A *ᵥ x.ofLp) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖x.ofLp j‖) ^ 2 := by
        gcongr
        simp only [Matrix.mulVec, dotProduct]
        exact (norm_sum_le _ _).trans (by simp)
    _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- Where the cutoff does not vanish, the active blocks are bounded by
`√(2 W⁸) + g² ‖R‖`. -/
private lemma SrcCutoffReg_block_bound (hW : 1 ≤ W) {ω : Ω W q} {w : Fin W → ℂ}
    (h : srcCut W g E q R P c ω w ≠ 0) (i : Fin q) (h4 : 4 ≤ (i : ℕ)) (hi : (i : ℕ) + 2 ≤ q) :
    ‖gueBlock W q ω i‖ ≤ Real.sqrt (2 * (W : ℝ) ^ 8) + ‖((g : ℂ) ^ 2) • R‖ := by
  obtain ⟨-, -, -, -, -, -, hge, -⟩ := step_spec
  have hW0 : (0 : ℝ) < (W : ℝ) ^ 8 := by
    have : (0 : ℝ) < W := by exact_mod_cast hW
    positivity
  have hsd : ∀ M : Matrix (Fin W) (Fin W) ℂ, stepDown (hsSq M / (W : ℝ) ^ 8) ≠ 0 →
      ‖M‖ ≤ Real.sqrt (2 * (W : ℝ) ^ 8) := fun M hM => by
    have hlt : hsSq M / (W : ℝ) ^ 8 < 2 := by
      by_contra hc
      exact hM (hge _ (not_lt.1 hc)).1
    rw [div_lt_iff₀ hW0] at hlt
    exact (SrcCutoffReg_norm_le_sqrt_hsSq M).trans (Real.sqrt_le_sqrt hlt.le)
  unfold srcCut matCut at h
  have h1 := mul_ne_zero_iff.1 (mul_ne_zero_iff.1 h).1
  have hb4 := (mul_ne_zero_iff.1 h1.1).2
  have hbi := Finset.prod_ne_zero_iff.1 h1.2
  have hblk : gueBlock W q ω i = blockSeq W q ω i := by
    simp only [blockSeq, i.2, ↓reduceDIte]
  rw [hblk]
  by_cases hi4 : (i : ℕ) = 4
  · rw [hi4]
    calc ‖blockSeq W q ω 4‖ = ‖(blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R) + ((g : ℂ) ^ 2) • R‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R‖ + ‖((g : ℂ) ^ 2) • R‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact hsd _ hb4
  · exact (hsd _ (hbi i (by simp only [Finset.mem_Icc]; omega))).trans
      (le_add_of_nonneg_right (norm_nonneg _))

end Smooth

/-! ### Measurability -/

section Meas

variable {W q : ℕ} {α : Type*} [MeasurableSpace α]

private lemma SrcCutoffReg_meas_inv {n : Type*} [Fintype n] [DecidableEq n] :
    Measurable (fun M : Matrix n n ℂ => M⁻¹) := by
  have h : (fun M : Matrix n n ℂ => M⁻¹) = fun M => Ring.inverse M.det • M.adjugate :=
    funext Matrix.inv_def
  rw [h, Ring.inverse_eq_inv']
  exact ((Continuous.matrix_det continuous_id).measurable.inv).smul
    (Continuous.matrix_adjugate continuous_id).measurable

private lemma SrcCutoffReg_cont_hsSq {n : Type*} [Fintype n] [DecidableEq n] :
    Continuous (fun M : Matrix n n ℂ => hsSq M) :=
  continuous_iff_continuousAt.2 fun _ =>
    (SrcCutoffReg_cd_hsSq (k := 0) contDiffAt_id).continuousAt

private lemma SrcCutoffReg_meas_smul (a : ℂ) {f : α → Matrix (Fin W) (Fin W) ℂ}
    (hf : Measurable f) : Measurable (fun y => a • f y) :=
  hf.const_smul a

private lemma SrcCutoffReg_meas_conjTranspose {f : α → Matrix (Fin W) (Fin W) ℂ}
    (hf : Measurable f) : Measurable (fun y => (f y)ᴴ) :=
  continuous_star.measurable.comp hf

private lemma SrcCutoffReg_cont_step : Continuous stepDown ∧ Continuous stepUp := by
  obtain ⟨-, -, hSD, hSU, -⟩ := step_spec
  exact ⟨hSD.continuous, hSU.continuous⟩

private lemma SrcCutoffReg_meas_normCut {n : Type*} [Fintype n] [DecidableEq n] (L : ℝ) :
    Measurable (fun M : Matrix n n ℂ => normCut L M) := by
  unfold normCut
  exact Measurable.ite Units.isOpen.measurableSet
    (SrcCutoffReg_cont_step.1.measurable.comp (SrcCutoffReg_cont_hsSq.measurable.div_const L))
    measurable_const

private lemma SrcCutoffReg_meas_rankSurr {n : Type*} [Fintype n] [DecidableEq n] (s : ℝ) :
    Measurable (fun M : Matrix n n ℂ => rankSurr s M) := by
  unfold rankSurr
  exact measurable_const.mul (Complex.measurable_re.comp
    ((Continuous.matrix_trace continuous_id).measurable.comp
      (measurable_id.mul (SrcCutoffReg_meas_inv.comp (measurable_id.add measurable_const)))))

private lemma SrcCutoffReg_meas_blockSeq {ω : α → Ω W q} (hω : Measurable ω) (k : ℕ) :
    Measurable (fun y => blockSeq W q (ω y) k) :=
  (SrcCutoffReg_cd_blockSeq (k := 0) W q k).continuous.measurable.comp hω

private lemma SrcCutoffReg_meas_chartR (g E : ℝ) {R : α → Matrix (Fin W) (Fin W) ℂ}
    {ω : α → Ω W q} (hR : Measurable R) (hω : Measurable ω) :
    ∀ j, Measurable (fun y => chartR W g E q (R y) (ω y) j)
  | 0 => by
    simp only [chartR]
    exact hR
  | j + 1 => by
    by_cases hj : j < 4
    · simp only [chartR, hj, ↓reduceIte]
      exact hR
    · simp only [chartR, hj, ↓reduceIte]
      exact SrcCutoffReg_meas_inv.comp (((SrcCutoffReg_meas_blockSeq hω j).sub
        measurable_const).sub (SrcCutoffReg_meas_smul _ (SrcCutoffReg_meas_chartR g E hR hω j)))

private lemma SrcCutoffReg_meas_chartProd (g E : ℝ) {R : α → Matrix (Fin W) (Fin W) ℂ}
    {ω : α → Ω W q} (hR : Measurable R) (hω : Measurable ω) :
    ∀ j, Measurable (fun y => chartProd W g E q (R y) (ω y) j)
  | 0 => by
    simp only [chartProd]
    exact measurable_const
  | j + 1 => by
    by_cases hj : j < 4
    · simp only [chartProd, hj, ↓reduceIte]
      exact measurable_const
    · simp only [chartProd, hj, ↓reduceIte]
      exact (SrcCutoffReg_meas_chartR g E hR hω (j + 1)).mul
        (SrcCutoffReg_meas_chartProd g E hR hω j)

private lemma SrcCutoffReg_meas_cavR (g E : ℝ) {ω : α → Ω W q} (hω : Measurable ω) :
    ∀ m, Measurable (fun y => cavR W g E q (ω y) m)
  | 0 => by
    simp only [cavR]
    exact SrcCutoffReg_meas_inv.comp ((SrcCutoffReg_meas_blockSeq hω _).sub measurable_const)
  | m + 1 => by
    simp only [cavR]
    exact SrcCutoffReg_meas_inv.comp (((SrcCutoffReg_meas_blockSeq hω _).sub
      measurable_const).sub (SrcCutoffReg_meas_smul _ (SrcCutoffReg_meas_cavR g E hω m)))

private lemma SrcCutoffReg_meas_cavProd (g E : ℝ) {ω : α → Ω W q} (hω : Measurable ω) :
    ∀ m, Measurable (fun y => cavProd W g E q (ω y) m)
  | 0 => by
    simp only [cavProd]
    exact measurable_const
  | m + 1 => by
    simp only [cavProd]
    exact (SrcCutoffReg_meas_cavProd g E hω m).mul (SrcCutoffReg_meas_cavR g E hω m)

private lemma SrcCutoffReg_meas_cavRes (g E : ℝ) {R : α → Matrix (Fin W) (Fin W) ℂ}
    {ω : α → Ω W q} (hR : Measurable R) (hω : Measurable ω) :
    Measurable (fun y => cavRes W g E q (R y) (ω y)) := by
  unfold cavRes
  exact SrcCutoffReg_meas_inv.comp ((((SrcCutoffReg_meas_blockSeq hω 4).sub
    measurable_const).sub (SrcCutoffReg_meas_smul _ hR)).sub
    (SrcCutoffReg_meas_smul _ (SrcCutoffReg_meas_cavR g E hω _)))

private lemma SrcCutoffReg_meas_retProj (g E t : ℝ) {R : α → Matrix (Fin W) (Fin W) ℂ}
    {ω : α → Ω W q} (hR : Measurable R) (hω : Measurable ω) :
    Measurable (fun y => retProj W g E q (R y) t (ω y)) := by
  have hA := SrcCutoffReg_meas_cavProd g E hω (q - 6)
  have hAA : Measurable fun y => (cavProd W g E q (ω y) (q - 6))ᴴ * cavProd W g E q (ω y) (q - 6) :=
    (SrcCutoffReg_meas_conjTranspose hA).mul hA
  have hS : Measurable (fun y => retSpec W g E q t (ω y)) := by
    have h : (fun y => retSpec W g E q t (ω y)) = fun y =>
        1 - specProj ((cavProd W g E q (ω y) (q - 6))ᴴ * cavProd W g E q (ω y) (q - 6))
          (Set.Iic (t ^ 2)) := by
      funext y
      have hs := (specProj_add_compl (Matrix.isHermitian_conjTranspose_mul_self
        (cavProd W g E q (ω y) (q - 6))) (Set.Ioi (t ^ 2))).1
      rw [Set.compl_Ioi] at hs
      unfold retSpec
      rw [← hs, add_sub_cancel_right]
    rw [h]
    exact measurable_const.sub ((measurable_specProj isClosed_Iic).comp hAA)
  have hT := SrcCutoffReg_meas_cavRes g E hR hω
  have hTs := SrcCutoffReg_meas_conjTranspose hT
  unfold retProj flagProj
  exact (((hT.mul hS).mul (SrcCutoffReg_meas_inv.comp ((((hS.mul hTs).mul hT).mul hS).add
    (measurable_const.sub hS)))).mul hS).mul hTs

private lemma SrcCutoffReg_cont_activeMat (g E : ℝ) :
    Continuous fun z : Matrix (Fin W) (Fin W) ℂ × Ω W q => activeMat W g E q z.1 z.2 := by
  refine continuous_matrix fun x y => ?_
  have hb : ∀ k, Continuous fun z : Matrix (Fin W) (Fin W) ℂ × Ω W q => blockSeq W q z.2 k :=
    fun k => (SrcCutoffReg_cd_blockSeq (k := 0) W q k).continuous.comp continuous_snd
  have hs : Continuous fun z : Matrix (Fin W) (Fin W) ℂ × Ω W q => ((g : ℂ) ^ 2) • z.1 := by
    fun_prop
  have h1 : ∀ k, Continuous fun z : Matrix (Fin W) (Fin W) ℂ × Ω W q =>
      blockSeq W q z.2 k - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • z.1 := fun k =>
    ((hb k).sub continuous_const).sub hs
  have h2 : ∀ k, Continuous fun z : Matrix (Fin W) (Fin W) ℂ × Ω W q =>
      blockSeq W q z.2 k - (E : ℂ) • 1 - (0 : Matrix (Fin W) (Fin W) ℂ) := fun k =>
    ((hb k).sub continuous_const).sub continuous_const
  simp only [activeMat, Matrix.of_apply]
  split_ifs
  all_goals first
    | exact continuous_const
    | exact (h1 _).matrix_elem _ _
    | exact (h2 _).matrix_elem _ _

end Meas

/-- Lemma 9.3 [su:lem:chosen-generator](ii), (v) for the construction: under the level rows of
`genPoint_of_cutSupp`, `(K, χ̂)` satisfies `GenFamily` at a Hermitian chart `R` and an orthogonal
projection `P` commuting with `R`. -/
theorem genFamily_srcCut {W q : ℕ} {g E : ℝ} (hW : 1 ≤ W) (hq : 7 ≤ q) (hg : 0 < g)
    (hg1 : g ≤ 1) {R P : Matrix (Fin W) (Fin W) ℂ} (hR : R.IsHermitian) (hP : P.IsHermitian)
    (hPP : P * P = P) (hPR : P * R = R * P) {c : CutLevels} (ht : 0 < c.t) (hLov : 0 < c.Lov)
    (hLov' : 64 * c.Lov ≤ 1) (hkOut : 0 < c.kOut) (hkP : 1 ≤ c.kP) (hLrk : 0 < c.Lrk)
    (hLgap : 0 < c.Lgap) (herr : 32 * c.t ^ 2 * (W : ℝ) ^ 34 ≤ c.kOut ^ 2) :
    GenFamily W q g E P R (fun ω w => smallGen W g E q R c.t P ω w)
      (fun ω w => srcCut W g E q R P c ω w) := by
  have _ := hPR
  obtain ⟨hG, hKd⟩ := contDiffOn_smallGen W g E q R c.t P
  refine ⟨fun ω ω' h w => ⟨SrcCutoffReg_smallGen_congr hq h w, SrcCutoffReg_srcCut_congr hq h w⟩,
    fun ω w => (srcCut_eq_one hW hg R P hLov hLrk hLgap hkOut ω w).1,
    fun ω w a ha => ⟨(smallGen_equivariant hR c.t hP hPP ω w).2 a ha,
      SrcCutoffReg_srcCut_smul ω w ha⟩,
    fun U hU hUP ω w => ⟨(smallGen_equivariant hR c.t hP hPP ω w).1 U hU hUP,
      SrcCutoffReg_srcCut_srcAct hq hR hP hU hUP ω w⟩,
    fun p hp => (SrcCutoffReg_cd_srcCut hq hW hg ht hLov hkOut hLgap p hp).contDiffWithinAt,
    ⟨genGood W g E q R c.t P, hG, hKd.of_le (WithTop.coe_le_coe.mpr le_top), fun p hp hv => ?_⟩,
    ⟨_, fun ω w h i h4 hi => SrcCutoffReg_block_bound hW h i h4 hi⟩⟩
  have hS := srcCut_tsupport hW hq hg hR P hLov hLrk hLgap hkOut p hp hv
  have hp' := cutSupp_genGood hW hq hg hg1 hR hP hPP hv ht hLov hLov' hkOut hkP herr hS
  exact ⟨hp', hp'.1⟩

/-- The cutoff is jointly measurable in `(R_4, ω, v̂)` for a measurable rule `R_4 ↦ P`. -/
theorem measurable_srcCut (W : ℕ) (g E : ℝ) (q : ℕ) (c : CutLevels)
    {Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} (hPf : Measurable Pf) :
    Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) =>
      srcCut W g E q p.1 (Pf p.1) c p.2.1 p.2.2 := by
  have hR : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) => p.1 :=
    measurable_fst
  have hω : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) => p.2.1 :=
    measurable_fst.comp measurable_snd
  have hv : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) => p.2.2 :=
    measurable_snd.comp measurable_snd
  have hP : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) => Pf p.1 :=
    hPf.comp measurable_fst
  have hD := SrcCutoffReg_cont_step.1.measurable
  have hU := SrcCutoffReg_cont_step.2.measurable
  have hN := fun L : ℝ => SrcCutoffReg_meas_normCut (n := Fin W) L
  have hH := (SrcCutoffReg_cont_hsSq (n := Fin W)).measurable
  have hC := SrcCutoffReg_meas_chartR g E hR hω
  have hK := SrcCutoffReg_meas_cavR g E hω
  have hA := SrcCutoffReg_meas_cavProd g E hω (q - 6)
  have hAA : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) =>
      (cavProd W g E q p.2.1 (q - 6))ᴴ * cavProd W g E q p.2.1 (q - 6) :=
    (SrcCutoffReg_meas_conjTranspose hA).mul hA
  have hQ := SrcCutoffReg_meas_retProj g E c.t hR hω
  have hCh := SrcCutoffReg_meas_chartProd g E hR hω (q - 1)
  have hmv : ∀ {M : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
      {u : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) → Fin W → ℂ}, Measurable M →
      Measurable u → Measurable fun p => ∑ i, ‖(M p *ᵥ u p) i‖ ^ 2 := fun hM hu =>
    Finset.measurable_sum _ fun i _ => (measurable_norm.comp ((measurable_pi_apply i).comp
      ((Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp
        (hM.prodMk hu)))).pow_const 2
  have hsv : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) =>
      ∑ i, ‖p.2.2 i‖ ^ 2 :=
    Finset.measurable_sum _ fun i _ => (measurable_norm.comp ((measurable_pi_apply i).comp
      hv)).pow_const 2
  have hPv : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) =>
      Pf p.1 *ᵥ p.2.2 :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp (hP.prodMk hv)
  have hreg : Measurable fun Y : Matrix (Fin W) (Fin W) ℂ => regCut W g Y := by
    unfold regCut
    exact (hN _).mul (hD.comp ((measurable_const.mul ((SrcCutoffReg_meas_rankSurr _).comp
      ((SrcCutoffReg_meas_conjTranspose measurable_id).mul measurable_id))).div_const _))
  have hTr : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) =>
      ((retProj W g E q p.1 c.t p.2.1 * (1 - Pf p.1) * retProj W g E q p.1 c.t p.2.1) ^
        c.kP).trace.re :=
    (Complex.continuous_re.comp (Continuous.matrix_trace continuous_id)).measurable.comp
      ((continuous_pow c.kP).measurable.comp ((hQ.mul (measurable_const.sub hP)).mul hQ))
  have m1 := Finset.measurable_prod (Finset.Icc 5 (q - 2)) fun j _ => hreg.comp (hC j)
  have m2 := (hN ((W : ℝ) ^ 6 / 2)).comp (hC (q - 1))
  have m3 := Finset.measurable_prod (Finset.range (q - 6)) fun m _ =>
    (hN ((W : ℝ) ^ 6 / 2)).comp (hK m)
  have m4 := (hN ((W : ℝ) ^ 6 / 2)).comp (SrcCutoffReg_meas_cavRes g E hR hω)
  have m5 := (SrcCutoffReg_meas_normCut ((W : ℝ) ^ 6 / 2)).comp (SrcCutoffReg_meas_inv.comp
    ((SrcCutoffReg_cont_activeMat (q := q) g E).measurable.comp (hR.prodMk hω)))
  have m6 := (hN c.Lgap).comp (SrcCutoffReg_meas_inv.comp (hAA.sub
    (measurable_const (a := ((c.t ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)))))
  have m7 := hD.comp (((SrcCutoffReg_meas_rankSurr c.t).comp hAA).div_const c.Lrk)
  have m8 := hD.comp ((measurable_const (a := (2 * 8 ^ c.kP : ℝ))).mul hTr)
  have m9 := hD.comp ((hH.comp ((SrcCutoffReg_meas_blockSeq hω 4).sub
    (SrcCutoffReg_meas_smul ((g : ℂ) ^ 2) hR))).div_const ((W : ℝ) ^ 8))
  have m10 := Finset.measurable_prod (Finset.Icc 5 (q - 2)) fun i _ =>
    hD.comp ((hH.comp (SrcCutoffReg_meas_blockSeq hω i)).div_const ((W : ℝ) ^ 8))
  have s1 := hU.comp (((measurable_const (a := 2 * (W : ℝ) ^ 20)).mul (hmv hP hv)).div hsv)
  have s2 := hD.comp ((hmv hQ hv).div ((measurable_const (a := c.Lov)).mul (hmv hP hv)))
  have s3 := hD.comp (((measurable_const (a := (16 : ℝ))).mul (hmv hQ hPv)).div (hmv hP hv))
  have s4 := hU.comp ((hmv hCh hv).div ((measurable_const (a := c.kOut ^ 2)).mul (hmv hP hv)))
  unfold srcCut matCut srcCutV
  exact (((((((((m1.mul m2).mul m3).mul m4).mul m5).mul m6).mul m7).mul m8).mul m9).mul
    m10).mul (((s1.mul s2).mul s3).mul s4)

end LSBA
