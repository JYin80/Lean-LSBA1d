import LSBA.Averaging.Haar
import LSBA.Averaging.Expansion
import LSBA.Sampling.Inputs
import LSBA.Prop.Domination
import LSBA.Flow.Comparison

/-!
# The averaging inputs

The covariance-weighted rows (6.13) [gc:eq:residual-row-bounds] on the comparison segments, the
averaging input of Lemma 5.9 [gc:lem:residual] from the rows, the crude moments and the sampling
inputs for every base family, and its bounded-coupling and large-coupling forms used by Theorem
5.12 [gc:thm:common].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The covariance-weighted Dyson rows (6.13) [gc:eq:residual-row-bounds] with constant `Γ` at
every admissible pair of Lemma 5.9 [gc:lem:residual] for `W ≥ W₀`: a positive height, a bounded
root `m_u(z)` in the closed upper half-plane, bounded entries of `M_{B,u}(z)` and
`uγ_g Σ_c (|M_{ac}| + |M_{ac}|²) ≤ Γ`. -/
def SegRows (base : ℕ → Set FlowPt) (J : ℕ) (Γ : ℝ) (W₀ : ℕ) : Prop :=
  ∀ W : ℕ, W₀ ≤ W → ∀ x : FlowPt × ℝ, SegAdm base J W x →
    let r := x.2 / gammaG x.1.g
    let xr := (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re
    let mu := mRootV (hopB x.1.g) (x.1.u * gammaG x.1.g) x.1.L
      ((xr : ℂ) + ((gammaG x.1.g * r : ℝ) : ℂ) * Complex.I)
    let M := segMat x.1.g x.1.L xr x.1.u r
    0 < x.2 ∧ 0 ≤ x.1.u ∧ 0 ≤ mu.im ∧ ‖mu‖ ≤ Γ ∧ (∀ a c, ‖M a c‖ ≤ Γ) ∧
      ∀ a, x.1.u * gammaG x.1.g * ∑ c, (‖M a c‖ + ‖M a c‖ ^ 2) ≤ Γ

/-! ### Measurability and the crude moments of the traces and entries -/

/-- Measurability of the entries of a matrix inverse of a matrix-valued measurable function. -/
private lemma averagingInput_measurable_det {α : Type*} [MeasurableSpace α] {n : Type*}
    [Fintype n] [DecidableEq n] (M : α → Matrix n n ℂ) (hM : ∀ p q, Measurable fun x => M x p q) :
    Measurable fun x => (M x).det := by
  simp_rw [Matrix.det_apply]
  exact Finset.measurable_sum _ fun σ _ =>
    Measurable.const_smul (Finset.measurable_prod _ fun i _ => hM _ _) _

private lemma averagingInput_measurable_inv {α : Type*} [MeasurableSpace α] {n : Type*}
    [Fintype n] [DecidableEq n] (M : α → Matrix n n ℂ) (hM : ∀ p q, Measurable fun x => M x p q)
    (p q : n) : Measurable fun x => (M x)⁻¹ p q := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul,
    Ring.inverse_eq_inv']
  refine Measurable.mul (averagingInput_measurable_det M hM).inv ?_
  refine averagingInput_measurable_det _ fun r s => ?_
  simp only [Matrix.updateRow_apply]
  by_cases h : r = q
  · simp only [h, ite_true]
    by_cases h2 : s = p <;> simp [h2]
  · simp only [h, ite_false]
    exact hM r s

/-- The entries of `H_u(g)` are continuous in the Gaussian coordinates. -/
private lemma averagingInput_continuous_flowH (g : ℝ) (W L : ℕ) (u : ℝ) (x y : Fin L × Fin W) :
    Continuous fun ω : Ω W L => flowH g W L u ω x y := by
  have h : ∀ a, Continuous fun ω : Ω W L => gueBlock W L ω a := fun a => by
    refine continuous_matrix fun α β => ?_
    simp only [gueBlock, Matrix.of_apply]
    split_ifs <;> fun_prop
  simp only [flowH, blockFlow, blockV, blockDiagOp, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul]
  refine continuous_const.add (continuous_const.mul ?_)
  by_cases hxy : x.1 = y.1
  · simp only [hxy, ite_true]
    exact (h y.1).matrix_elem x.2 y.2
  · simp only [hxy, ite_false]
    exact continuous_const

/-- The entries of `segG W x` are measurable. -/
private lemma averagingInput_measurable_segG (W : ℕ) (x : FlowPt × ℝ) (p q : Fin x.1.L × Fin W) :
    Measurable fun ω : Ω W x.1.L => segG W x ω p q := by
  unfold segG resolventMat
  refine averagingInput_measurable_inv (fun ω : Ω W x.1.L => flowH x.1.g W x.1.L x.1.u ω -
    (((zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re : ℂ) + (x.2 : ℂ) * Complex.I) •
      (1 : Matrix (Fin x.1.L × Fin W) (Fin x.1.L × Fin W) ℂ)) (fun r s => ?_) p q
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  exact (averagingInput_continuous_flowH _ _ _ _ r s).measurable.sub measurable_const

/-- The block traces of `segG W x` are measurable. -/
private lemma averagingInput_measurable_blockTr (W : ℕ) (x : FlowPt × ℝ) (a b : Fin x.1.L) :
    Measurable fun ω : Ω W x.1.L => blockTr (segG W x ω) a b := by
  unfold blockTr
  exact measurable_const.mul (Finset.measurable_sum _ fun α _ =>
    averagingInput_measurable_segG W x _ _)

/-- The traceless entries of `segG W x` are measurable. -/
private lemma averagingInput_measurable_traceless (W : ℕ) (x : FlowPt × ℝ)
    (e : (Fin x.1.L × Fin W) × (Fin x.1.L × Fin W)) :
    Measurable fun ω : Ω W x.1.L => segG W x ω e.1 e.2 -
      if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0 := by
  refine (averagingInput_measurable_segG W x _ _).sub ?_
  by_cases h : e.1.2 = e.2.2
  · simp only [h, ite_true]
    exact averagingInput_measurable_blockTr W x _ _
  · simp only [h, ite_false]
    exact measurable_const

open scoped Matrix.Norms.L2Operator in
/-- An entry is bounded by the operator norm. -/
private lemma averagingInput_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
  have hn : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [hn, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  convert this using 2
  simp

open scoped Matrix.Norms.L2Operator in
/-- `‖⟨G⟩_{ab}‖ ≤ ‖G_{ab}‖_op`. -/
private lemma averagingInput_blockTr_le {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : ‖blockTr G a b‖ ≤ ‖blockOf G a b‖ := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp [blockTr]
  · simp only [blockTr, norm_mul, norm_inv, Complex.norm_natCast]
    have hWr : (0 : ℝ) < W := by exact_mod_cast hW
    rw [inv_mul_le_iff₀ hWr]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ α, ‖G (a, α) (b, α)‖ ≤ ∑ _α : Fin W, ‖blockOf G a b‖ :=
          Finset.sum_le_sum fun α _ => averagingInput_entry_le (blockOf G a b) α α
      _ = W * ‖blockOf G a b‖ := by simp

open scoped Matrix.Norms.L2Operator in
/-- `|G_{(a,i),(b,j)} - δ_{ij}⟨G⟩_{ab}| ≤ 2‖G_{ab}‖_op`. -/
private lemma averagingInput_traceless_le {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (e : (Fin L × Fin W) × (Fin L × Fin W)) :
    ‖G e.1 e.2 - if e.1.2 = e.2.2 then blockTr G e.1.1 e.2.1 else 0‖ ≤
      2 * ‖blockOf G e.1.1 e.2.1‖ := by
  have h1 : ‖G e.1 e.2‖ ≤ ‖blockOf G e.1.1 e.2.1‖ :=
    averagingInput_entry_le (blockOf G e.1.1 e.2.1) e.1.2 e.2.2
  refine (norm_sub_le _ _).trans ?_
  by_cases h : e.1.2 = e.2.2
  · simp only [h, ite_true]
    linarith [averagingInput_blockTr_le G e.1.1 e.2.1]
  · simp only [h, ite_false, norm_zero]
    linarith [norm_nonneg (blockOf G e.1.1 e.2.1)]

/-- A measurable `X` dominated by `c B` inherits the integrability and the moment of `B`. -/
private lemma averagingInput_moment_of_le {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'}
    (X : Ω' → ℂ) (B : Ω' → ℝ) (hX : Measurable X) (c : ℝ)
    (hle : ∀ ω, ‖X ω‖ ≤ c * B ω) (q : ℕ) (hB : Integrable (fun ω => B ω ^ q) P) :
    Integrable (fun ω => ‖X ω‖ ^ q) P ∧
      ∫ ω, ‖X ω‖ ^ q ∂P ≤ c ^ q * ∫ ω, B ω ^ q ∂P := by
  have hpt : ∀ ω, ‖X ω‖ ^ q ≤ c ^ q * B ω ^ q := fun ω => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hle ω) q
  have hint : Integrable (fun ω => ‖X ω‖ ^ q) P := by
    refine Integrable.mono' (hB.const_mul (c ^ q)) (hX.norm.pow_const q).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt ω
  refine ⟨hint, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hint (hB.const_mul (c ^ q)) hpt

open scoped Matrix.Norms.L2Operator in
/-- The crude moments of `⟨G⟩_{ab}` and of the traceless entries of `G`, of every even order
`2r` with `r ≥ 1`, from the crude moments of the blocks `G_{ab}`. -/
private lemma averagingInput_crude_trace (base : ℕ → Set FlowPt) (J : ℕ)
    (hcrude : CrudeInput base J) :
    ∃ C₀ : ℝ, ∀ r : ℕ, 1 ≤ r → ∃ Cr : ℝ, ∃ Wc : ℕ, ∀ W : ℕ, Wc ≤ W → ∀ x : FlowPt × ℝ,
      SegAdm base J W x →
      (∀ a b : Fin x.1.L, Integrable (fun ω => ‖blockTr (segG W x ω) a b‖ ^ (2 * r))
          (μ W x.1.L) ∧
        ∫ ω, ‖blockTr (segG W x ω) a b‖ ^ (2 * r) ∂(μ W x.1.L) ≤ Cr * (W : ℝ) ^ (2 * r * C₀)) ∧
      (∀ e : (Fin x.1.L × Fin W) × (Fin x.1.L × Fin W),
        Integrable (fun ω => ‖segG W x ω e.1 e.2 -
          if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0‖ ^ (2 * r))
          (μ W x.1.L) ∧
        ∫ ω, ‖segG W x ω e.1 e.2 -
          if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0‖ ^ (2 * r)
          ∂(μ W x.1.L) ≤ Cr * (W : ℝ) ^ (2 * r * C₀)) := by
  obtain ⟨C₀, H⟩ := hcrude
  refine ⟨C₀, fun r hr => ?_⟩
  obtain ⟨Cq, Wq, hq⟩ := H (2 * r) (by omega)
  refine ⟨2 ^ (2 * r) * Cq, Wq, fun W hW x hx => ?_⟩
  have hexp : (W : ℝ) ^ (C₀ * ((2 * r : ℕ) : ℝ)) = (W : ℝ) ^ (2 * r * C₀) := by
    congr 1; push_cast; ring
  have hmain : ∀ (X : Ω W x.1.L → ℂ) (a b : Fin x.1.L), Measurable X →
      (∀ ω, ‖X ω‖ ≤ 2 * ‖blockOf (segG W x ω) a b‖) →
      Integrable (fun ω => ‖X ω‖ ^ (2 * r)) (μ W x.1.L) ∧
        ∫ ω, ‖X ω‖ ^ (2 * r) ∂(μ W x.1.L) ≤ 2 ^ (2 * r) * Cq * (W : ℝ) ^ (2 * r * C₀) := by
    intro X a b hX hle
    obtain ⟨hi, hm⟩ := hq W hW x hx a b
    obtain ⟨h1, h2⟩ := averagingInput_moment_of_le (P := μ W x.1.L) X
      (fun ω => ‖blockOf (segG W x ω) a b‖) hX 2 hle (2 * r) hi
    refine ⟨h1, h2.trans ?_⟩
    rw [mul_assoc, ← hexp]
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  refine ⟨fun a b => hmain _ a b (averagingInput_measurable_blockTr W x a b) fun ω => ?_,
    fun e => hmain _ e.1.1 e.2.1 (averagingInput_measurable_traceless W x e) fun ω => ?_⟩
  · exact (averagingInput_blockTr_le _ a b).trans (by
      linarith [norm_nonneg (blockOf (segG W x ω) a b)])
  · exact averagingInput_traceless_le _ e

/-! ### The rows at one pair and the moments of the residual -/

/-- `γ_g > 0`. -/
private lemma averagingInput_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG; positivity

/-- The conditions of `SegRows` at one pair. -/
private def averagingInput_rowsAt (Γ : ℝ) (x : FlowPt × ℝ) : Prop :=
  let r := x.2 / gammaG x.1.g
  let xr := (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re
  let mu := mRootV (hopB x.1.g) (x.1.u * gammaG x.1.g) x.1.L
    ((xr : ℂ) + ((gammaG x.1.g * r : ℝ) : ℂ) * Complex.I)
  let M := segMat x.1.g x.1.L xr x.1.u r
  0 < x.2 ∧ 0 ≤ x.1.u ∧ 0 ≤ mu.im ∧ ‖mu‖ ≤ Γ ∧ (∀ a c, ‖M a c‖ ≤ Γ) ∧
    ∀ a, x.1.u * gammaG x.1.g * ∑ c, (‖M a c‖ + ‖M a c‖ ^ 2) ≤ Γ

/-- The rows at one pair are monotone in the constant. -/
private lemma averagingInput_rowsAt_mono {Γ Γ' : ℝ} (h : Γ ≤ Γ') {x : FlowPt × ℝ}
    (hx : averagingInput_rowsAt Γ x) : averagingInput_rowsAt Γ' x := by
  unfold averagingInput_rowsAt at hx ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx
  exact ⟨h1, h2, h3, h4.trans h, fun a c => (h5 a c).trans h, fun a => (h6 a).trans h⟩

/-- On the segment, `segMat` is the Dyson matrix at `z = Re z_u + iy` with the root `m_u(z)`. -/
private lemma averagingInput_segMat_eq (g : ℝ) (L : ℕ) (xr u y : ℝ) :
    segMat g L xr u (y / gammaG g) =
      dysonMat (hopB g) (u * gammaG g) L ((xr : ℂ) + (y : ℂ) * Complex.I)
        (mRootV (hopB g) (u * gammaG g) L ((xr : ℂ) + (y : ℂ) * Complex.I)) := by
  have hγ : gammaG g ≠ 0 := (averagingInput_gammaG_pos g).ne'
  have h : gammaG g * (y / gammaG g) = y := by field_simp
  unfold segMat
  rw [h]

/-- (5.31) [fo:eq:residual-moments] in the vocabulary of the admissible pairs: the entry moments
`‖(G - M ⊗ I)_{e₁e₂}‖_{2p} ≤ Cχ` and the rows give `E|R_{ab}|^p ≤ C_p χ^{2p}`. -/
private lemma averagingInput_bridge_entries (p : ℕ) (hp : 2 ≤ p) (hpe : Even p) (C Γ : ℝ)
    (hC : 0 < C) (hΓ : 0 < Γ) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ W : ℕ, 1 ≤ W → ∀ x : FlowPt × ℝ, averagingInput_rowsAt Γ x →
      ∀ χ : ℝ, (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ χ →
      (∀ e₁ e₂ : Fin x.1.L × Fin W,
        (∫ ω, ‖(segG W x ω - segM W x) e₁ e₂‖ ^ (2 * p) ∂(μ W x.1.L)) ^ (1 / (2 * (p : ℝ))) ≤
          C * χ) →
      ∀ a b : Fin x.1.L, Integrable (fun ω => ‖segRes W x ω a b‖ ^ p) (μ W x.1.L) ∧
        ∫ ω, ‖segRes W x ω a b‖ ^ p ∂(μ W x.1.L) ≤ Cp * χ ^ (2 * p) := by
  obtain ⟨Cp, hCp, H⟩ := residual_moment_entries p hp hpe C Γ hC hΓ
  refine ⟨Cp, hCp, fun W hW x hrow χ hχ hE a b => ?_⟩
  unfold averagingInput_rowsAt at hrow
  obtain ⟨hy, hu, hmu, hmuΓ, hM, hrw⟩ := hrow
  set z : ℂ := ((zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re : ℂ) +
    (x.2 : ℂ) * Complex.I with hz
  set m' : ℂ := mRootV (hopB x.1.g) (x.1.u * gammaG x.1.g) x.1.L z with hm'
  have hseg := averagingInput_segMat_eq x.1.g x.1.L
    (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.1.u x.2
  rw [← hz, ← hm'] at hseg
  have hγ : gammaG x.1.g ≠ 0 := (averagingInput_gammaG_pos x.1.g).ne'
  have hγy : gammaG x.1.g * (x.2 / gammaG x.1.g) = x.2 := by field_simp
  simp only [hγy] at hmu hmuΓ
  have hsegM : segM W x = dysonMat (hopB x.1.g) (x.1.u * gammaG x.1.g) x.1.L z m' ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ) := by
    unfold segM
    rw [hseg]
  have hres : ∀ ω, segRes W x ω a b =
      blockTr ((dysonMat (hopB x.1.g) (x.1.u * gammaG x.1.g) x.1.L z m' ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ)) * resPi x.1.g x.1.u z
          (resolventMat (flowH x.1.g W x.1.L x.1.u ω) z)) a b := fun ω => by
    unfold segRes
    rw [hsegM]
    rfl
  rw [hsegM] at hE
  simp only [hres]
  exact H W x.1.L hW x.1.g x.1.u hu z m' (by simpa [hz] using hy) hmu hmuΓ
    (fun a c => by rw [← hseg]; exact hM a c) (fun a => by rw [← hseg]; exact hrw a) χ hχ hE a b

/-- (7.26) [gc:eq:residual-fixed-moment] in the vocabulary of the admissible pairs: the moments
`‖⟨G⟩_{ab}‖_{2p} ≤ CK`, `‖G_{ai,bj} - δ_{ij}⟨G⟩_{ab}‖_{2p} ≤ CKχ` and the rows give
`E|R_{ab}|^p ≤ C_p (K²χ²)^p`. -/
private lemma averagingInput_bridge_trace (p : ℕ) (hp : 2 ≤ p) (hpe : Even p) (C Γ : ℝ)
    (hC : 0 < C) (hΓ : 0 < Γ) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ W : ℕ, 1 ≤ W → ∀ x : FlowPt × ℝ, averagingInput_rowsAt Γ x →
      ∀ K χ : ℝ, 1 ≤ K → (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ χ →
      (∀ a b : Fin x.1.L,
        (∫ ω, ‖blockTr (segG W x ω) a b‖ ^ (2 * p) ∂(μ W x.1.L)) ^ (1 / (2 * (p : ℝ))) ≤
          C * K) →
      (∀ e₁ e₂ : Fin x.1.L × Fin W,
        (∫ ω, ‖segG W x ω e₁ e₂ - if e₁.2 = e₂.2 then blockTr (segG W x ω) e₁.1 e₂.1 else 0‖ ^
          (2 * p) ∂(μ W x.1.L)) ^ (1 / (2 * (p : ℝ))) ≤ C * K * χ) →
      ∀ a b : Fin x.1.L, Integrable (fun ω => ‖segRes W x ω a b‖ ^ p) (μ W x.1.L) ∧
        ∫ ω, ‖segRes W x ω a b‖ ^ p ∂(μ W x.1.L) ≤ Cp * (K ^ 2 * χ ^ 2) ^ p := by
  obtain ⟨Cp, hCp, H⟩ := residual_moment p hp hpe C Γ hC hΓ
  refine ⟨Cp, hCp, fun W hW x hrow K χ hK hχ h1 h2 a b => ?_⟩
  unfold averagingInput_rowsAt at hrow
  obtain ⟨hy, hu, hmu, hmuΓ, hM, hrw⟩ := hrow
  set z : ℂ := ((zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re : ℂ) +
    (x.2 : ℂ) * Complex.I with hz
  set m' : ℂ := mRootV (hopB x.1.g) (x.1.u * gammaG x.1.g) x.1.L z with hm'
  have hseg := averagingInput_segMat_eq x.1.g x.1.L
    (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.1.u x.2
  rw [← hz, ← hm'] at hseg
  have hγ : gammaG x.1.g ≠ 0 := (averagingInput_gammaG_pos x.1.g).ne'
  have hγy : gammaG x.1.g * (x.2 / gammaG x.1.g) = x.2 := by field_simp
  simp only [hγy] at hmu hmuΓ
  have hsegM : segM W x = dysonMat (hopB x.1.g) (x.1.u * gammaG x.1.g) x.1.L z m' ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ) := by
    unfold segM
    rw [hseg]
  have hres : ∀ ω, segRes W x ω a b =
      blockTr ((dysonMat (hopB x.1.g) (x.1.u * gammaG x.1.g) x.1.L z m' ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ)) * resPi x.1.g x.1.u z
          (resolventMat (flowH x.1.g W x.1.L x.1.u ω) z)) a b := fun ω => by
    unfold segRes
    rw [hsegM]
    rfl
  simp only [hres]
  exact H W x.1.L hW x.1.g x.1.u hu z m' (by simpa [hz] using hy) hmu hmuΓ
    (fun a c => by rw [← hseg]; exact hM a c) (fun a => by rw [← hseg]; exact hrw a) K χ hK hχ
    h1 h2 a b

/-! ### The rows from the positive-height bounds -/

/-- For `ρ → ∞` and any reals `a`, `M`, eventually `a ≤ ρ(W)`, `M ≤ log W` and `1 ≤ W`. -/
private lemma averagingInput_threshold (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop atTop) (a M : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → a ≤ ρ W ∧ M ≤ Real.log W ∧ 1 ≤ W := by
  have h1 : ∀ᶠ W : ℕ in atTop, a ≤ ρ W := hρ.eventually_ge_atTop a
  have h2 : ∀ᶠ W : ℕ in atTop, M ≤ Real.log W :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop M
  have h3 : ∀ᶠ W : ℕ in atTop, 1 ≤ W := eventually_ge_atTop 1
  exact Filter.eventually_atTop.mp ((h1.and h2).and h3) |>.imp fun W₀ h W hW =>
    ⟨(h W hW).1.1, (h W hW).1.2, (h W hW).2⟩

/-- The time of a point with `W^{-3} ≤ 1 - u` is below `1` when `W ≥ 1`. -/
private lemma averagingInput_time_lt_one {W : ℕ} (hW : 1 ≤ W) {u : ℝ}
    (h : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - u) : u < 1 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have := Real.rpow_pos_of_pos hW0 (-3 : ℝ)
  linarith

/-- The rows at one pair from the positive-height bounds (Lemma 6.4 [da:lem:positive-height]):
the root `m_u(z)` is a diagonal entry of `M_{B,u}(z)`, and `u ≤ 1` turns the bound with `γ_g`
into the bound with `uγ_g`. -/
private lemma averagingInput_rowsAt_of_ph (x : FlowPt × ℝ) (Γ : ℝ) (hL : 1 ≤ x.1.L)
    (hy : 0 < x.2) (hu0 : 0 ≤ x.1.u) (hu1 : x.1.u ≤ 1)
    (hroot : IsDysonRootV (hopB x.1.g) (x.1.u * gammaG x.1.g) x.1.L
      (((zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re : ℂ) + (x.2 : ℂ) * Complex.I)
      (mRootV (hopB x.1.g) (x.1.u * gammaG x.1.g) x.1.L
        (((zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re : ℂ) + (x.2 : ℂ) * Complex.I)))
    (hM : ∀ a c, ‖segMat x.1.g x.1.L (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re
      x.1.u (x.2 / gammaG x.1.g) a c‖ ≤ Γ)
    (hrow : ∀ a, gammaG x.1.g * ∑ c,
      (‖segMat x.1.g x.1.L (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re
        x.1.u (x.2 / gammaG x.1.g) a c‖ +
      ‖segMat x.1.g x.1.L (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re
        x.1.u (x.2 / gammaG x.1.g) a c‖ ^ 2) ≤ Γ) :
    averagingInput_rowsAt Γ x := by
  have hγ := averagingInput_gammaG_pos x.1.g
  have hγy : gammaG x.1.g * (x.2 / gammaG x.1.g) = x.2 := by field_simp
  have hseg := averagingInput_segMat_eq x.1.g x.1.L
    (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.1.u x.2
  unfold averagingInput_rowsAt
  simp only [hγy]
  refine ⟨hy, hu0, hroot.1.le, ?_, hM, fun a => ?_⟩
  · set z : ℂ := (((zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re : ℂ) +
      (x.2 : ℂ) * Complex.I) with hz
    set mu : ℂ := mRootV (hopB x.1.g) (x.1.u * gammaG x.1.g) x.1.L z with hmu
    have hw : 0 < (z + ((x.1.u * gammaG x.1.g : ℝ) : ℂ) * mu).im := by
      have h1 : (z + ((x.1.u * gammaG x.1.g : ℝ) : ℂ) * mu).im =
          x.2 + x.1.u * gammaG x.1.g * mu.im := by simp [hz]
      rw [h1]
      have := mul_nonneg (mul_nonneg hu0 hγ.le) hroot.1.le
      linarith
    have haa : segMat x.1.g x.1.L (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re
        x.1.u (x.2 / gammaG x.1.g) ⟨0, hL⟩ ⟨0, hL⟩ = mu := by
      rw [hseg, dysonMat_diag _ _ _ hL _ _ hw]
      exact hroot.2.symm
    rw [← haa]
    exact hM _ _
  · have h0 : 0 ≤ gammaG x.1.g * ∑ c, (‖segMat x.1.g x.1.L
        (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.1.u (x.2 / gammaG x.1.g) a c‖ +
        ‖segMat x.1.g x.1.L (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.1.u
          (x.2 / gammaG x.1.g) a c‖ ^ 2) :=
      mul_nonneg hγ.le (Finset.sum_nonneg fun c _ => by positivity)
    calc x.1.u * gammaG x.1.g * ∑ c, (‖segMat x.1.g x.1.L
          (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.1.u (x.2 / gammaG x.1.g) a c‖ +
          ‖segMat x.1.g x.1.L (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.1.u
            (x.2 / gammaG x.1.g) a c‖ ^ 2)
        = x.1.u * (gammaG x.1.g * ∑ c, (‖segMat x.1.g x.1.L
          (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.1.u (x.2 / gammaG x.1.g) a c‖ +
          ‖segMat x.1.g x.1.L (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.1.u
            (x.2 / gammaG x.1.g) a c‖ ^ 2)) := by ring
      _ ≤ 1 * (gammaG x.1.g * ∑ c, (‖segMat x.1.g x.1.L
          (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.1.u (x.2 / gammaG x.1.g) a c‖ +
          ‖segMat x.1.g x.1.L (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.1.u
            (x.2 / gammaG x.1.g) a c‖ ^ 2)) := mul_le_mul_of_nonneg_right hu1 h0
      _ ≤ Γ := by rw [one_mul]; exact hrow a

/-- The rows (6.13) [gc:eq:residual-row-bounds] at the admissible pairs of a bounded-coupling
base family (Lemma 6.4 [da:lem:positive-height] along the reach of Lemma 6.3(b)
[da:lem:comparison-parameters]). -/
theorem segRows_bdd (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') (gmin ρ : ℕ → ℝ)
    (hgmin : ∀ W, 0 < gmin W) (hρ : Tendsto ρ atTop atTop) (J : ℕ) :
    ∃ Γ : ℝ, 0 < Γ ∧ ∃ W₀ : ℕ, ∀ base : ℕ → Set FlowPt,
      (∀ W p, p ∈ base W → gmin W ≤ p.g ∧ RegBdd C B c' p.L p.g p.E ∧
        ρ W * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ (W : ℝ) ^ 2 ∧ 1 / 2 ≤ p.u ∧
        (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u) →
      SegRows base J Γ W₀ := by
  obtain ⟨BJ, cJ, hcJ, W₁, HR⟩ := cmpReach_bdd C B c' hC hB hc' gmin ρ hgmin hρ J
  have hB₀ : 0 < max BJ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨c, C', L₀, hc, hC', HP⟩ := positiveHeight_bdd C (max BJ 1) cJ hC hB₀ hcJ
  obtain ⟨C'', L₀', hC'', HC⟩ := cmpParams_bdd C (max BJ 1) cJ hC hB₀ hcJ
  obtain ⟨W₂, hW₂⟩ := averagingInput_threshold ρ hρ (max (L₀ : ℝ) (L₀' : ℝ)) 1
  refine ⟨C', hC', max W₁ W₂, fun base hbase => ?_⟩
  intro W hW x hx
  have hW₁ : W₁ ≤ W := (le_max_left _ _).trans hW
  have hW₂' : W₂ ≤ W := (le_max_right _ _).trans hW
  obtain ⟨hρL, hlog, hW1⟩ := hW₂ W hW₂'
  obtain ⟨d, hd, hreach, hseg⟩ := hx
  obtain ⟨hreg, hg0, hL3, -, hu12, hut⟩ := HR base hbase W hW₁ d x.1 hd hreach
  obtain ⟨q, hq, -, -, -, -, -, hLq, -, -, -⟩ := cmpReach_chain base W d x.1 hreach
  obtain ⟨-, -, hLlog, -, -, -⟩ := hbase W q hq
  have hu1 : x.1.u < 1 := averagingInput_time_lt_one hW1 hut
  have hlog0 : 0 ≤ Real.log W := by linarith
  have hρ0 : 0 ≤ ρ W := le_trans (le_max_of_le_left (Nat.cast_nonneg _)) hρL
  have hLge : max (L₀ : ℝ) (L₀' : ℝ) ≤ x.1.L := by
    rw [hLq]
    calc max (L₀ : ℝ) (L₀' : ℝ) ≤ ρ W := hρL
      _ ≤ ρ W * Real.log W := le_mul_of_one_le_right hρ0 hlog
      _ ≤ q.L := hLlog
  have hL₀ : L₀ ≤ x.1.L := by exact_mod_cast (le_max_left _ _).trans hLge
  have hL₀' : L₀' ≤ x.1.L := by exact_mod_cast (le_max_right _ _).trans hLge
  obtain ⟨hgnn, hgC, hE, hroot, hcm⟩ := hreg
  have hE' : |x.1.E| ≤ max BJ 1 := hE.trans (le_max_left _ _)
  have hcm0 : 0 < (mRoot x.1.g x.1.L x.1.E).im := lt_of_lt_of_le hcJ hcm
  have hη0 : 0 < etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u :=
    mul_pos (mul_pos (sub_pos.mpr hu1) (averagingInput_gammaG_pos _)) hcm0
  obtain ⟨s, hs1, hsu, hηy, hyw⟩ : ∃ s : ℝ, 1 / 2 ≤ s ∧ s ≤ x.1.u ∧
      etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u ≤ x.2 ∧
      x.2 ≤ (wCmp x.1.g x.1.L x.1.E (mRoot x.1.g x.1.L x.1.E) s x.1.u).im := by
    rcases hseg with h | ⟨-, s, hs1, hsu, h1, h2⟩
    · refine ⟨x.1.u, hu12, le_rfl, h.ge, ?_⟩
      have hH := HC x.1.g hgnn hgC x.1.L hL3 hL₀' x.1.E hE' (mRoot x.1.g x.1.L x.1.E) hroot hcm
        x.1.u x.1.u hu12 le_rfl hu1
      dsimp only at hH
      rw [h]
      exact hH.2.2.2.1
    · exact ⟨s, hs1, hsu, h1, h2⟩
  have hy0 : 0 < x.2 := lt_of_lt_of_le hη0 hηy
  have hP := HP x.1.g hgnn hgC x.1.L hL3 hL₀ x.1.E hE' (mRoot x.1.g x.1.L x.1.E) hroot hcm s
    x.1.u hs1 hsu hu1 x.2 hηy hyw
  dsimp only at hP
  obtain ⟨hroot', -, -, hM, hrow, -⟩ := hP
  exact averagingInput_rowsAt_of_ph x C' (by omega) hy0 (by linarith) hu1.le hroot' hM hrow

/-- The rows (6.13) [gc:eq:residual-row-bounds] at the admissible pairs of a large-coupling base
family (Lemma 6.4 [da:lem:positive-height] at `κ/2` along the reach). -/
theorem segRows_large (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) (J : ℕ) :
    ∃ Cκ₀ Γ : ℝ, 1 ≤ Cκ₀ ∧ 0 < Γ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ,
      Tendsto ρ atTop atTop → ∃ W₀ : ℕ, ∀ base : ℕ → Set FlowPt,
        (∀ W p, p ∈ base W → Cκ ≤ p.g ∧ |p.E| ≤ 2 - 3 * κ / 4 ∧
          ρ W * p.g ^ 2 * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ CV * p.g ^ 2 * (W : ℝ) ^ 2 ∧
          1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u) →
        SegRows base J Γ W₀ := by
  obtain ⟨CκR, C'', hCκR, hC'', HR⟩ := cmpReach_large κ CV hκ hκ2 hCV J
  obtain ⟨CκS, CA, hCκS, hCA, HS⟩ := segAdm_large κ CV hκ hκ2 hCV J
  obtain ⟨Cκc, Cch, hCκc, hCch, HC⟩ := char_large (κ / 2) C'' (by linarith) (by linarith) hC''
  obtain ⟨Cκp, R, c, C', hCκp, hR, hc, hC', HP⟩ :=
    positiveHeight_large (κ / 2) CA (by linarith) (by linarith) (by linarith)
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  refine ⟨max (max CκR CκS) (max (Real.sqrt 2 * Cκc) (Real.sqrt 2 * Cκp)), C',
    hCκR.trans ((le_max_left _ _).trans (le_max_left _ _)), hC', fun Cκ hCκ ρ hρ => ?_⟩
  have hCκR' : CκR ≤ Cκ := ((le_max_left _ _).trans (le_max_left _ _)).trans hCκ
  have hCκS' : CκS ≤ Cκ := ((le_max_right _ _).trans (le_max_left _ _)).trans hCκ
  have hCκc' : Real.sqrt 2 * Cκc ≤ Cκ := ((le_max_left _ _).trans (le_max_right _ _)).trans hCκ
  have hCκp' : Real.sqrt 2 * Cκp ≤ Cκ := ((le_max_right _ _).trans (le_max_right _ _)).trans hCκ
  obtain ⟨W₁, hW₁⟩ := HR Cκ hCκR' ρ hρ
  obtain ⟨W₂, hW₂⟩ := HS Cκ hCκS' ρ hρ
  obtain ⟨W₃, hW₃⟩ := averagingInput_threshold ρ hρ (max R 1) 1
  refine ⟨max (max W₁ W₂) W₃, fun base hbase => ?_⟩
  intro W hW x hx
  have hW₁' : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW₂' : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW₃' : W₃ ≤ W := (le_max_right _ _).trans hW
  obtain ⟨hρR, hlog, hW1⟩ := hW₃ W hW₃'
  obtain ⟨hCκg, hE', hroot, hIm, hm, hvol, -, hu12, hut⟩ :=
    hW₁ base hbase W hW₁' _ x.1 (hx.choose_spec.1) (hx.choose_spec.2.1)
  obtain ⟨hηy, hyC⟩ := hW₂ base hbase W hW₂' x hx
  have hu1 : x.1.u < 1 := averagingInput_time_lt_one hW1 hut
  have hu0 : 0 ≤ x.1.u := by linarith
  have hgc : Cκc ≤ x.1.g := by
    refine le_trans ?_ hCκg
    rw [le_div_iff₀ hs2]; linarith
  have hgp : Cκp ≤ x.1.g := by
    refine le_trans ?_ hCκg
    rw [le_div_iff₀ hs2]; linarith
  obtain ⟨hzre, -, hη0, -, -⟩ := HC x.1.g hgc x.1.E (mRoot x.1.g x.1.L x.1.E) hE' hm hIm
    x.1.u hu0 hu1
  have hy0 : 0 < x.2 := lt_of_lt_of_le hη0 hηy
  have hg1 : 1 ≤ x.1.g := hCκc.trans hgc
  have hg2 : (0 : ℝ) < x.1.g ^ 2 := by positivity
  have hρ0 : 0 ≤ ρ W := le_trans (by positivity) hρR
  have hRL : R * x.1.g ^ 2 ≤ x.1.L := by
    calc R * x.1.g ^ 2 ≤ (ρ W * Real.log W) * x.1.g ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hg2.le
          calc R ≤ ρ W := (le_max_left _ _).trans hρR
            _ ≤ ρ W * Real.log W := le_mul_of_one_le_right hρ0 hlog
      _ = ρ W * x.1.g ^ 2 * Real.log W := by ring
      _ ≤ x.1.L := hvol
  have hP := HP x.1.g hgp x.1.L hRL (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.2
    x.1.u hzre hy0 hyC hu12 hu1.le
  dsimp only at hP
  obtain ⟨hroot', -, -, hM, hrow, -⟩ := hP
  have hL1 : 1 ≤ x.1.L := by
    have h1 : (0 : ℝ) < x.1.L := lt_of_lt_of_le (by positivity) hRL
    exact_mod_cast h1
  exact averagingInput_rowsAt_of_ph x C' hL1 hy0 hu0 hu1.le hroot' hM hrow

/-! ### The averaging input from the rows -/

/-- The moment bound from a domination and crude moments (the Hölder step on the exceptional
events in the proof of Lemma 5.9 [gc:lem:residual](i)): at each label, `X ≺ Y` with
`Y ≥ W^{-C₁}` and crude moments `E‖X‖^{2r} ≤ C_r W^{2rC₀}` for `W ≥ W_c` give
`‖X‖_{L^r} ≤ W^ε Y` for all large `W`, uniformly on the family. -/
private lemma averagingInput_lemmaE {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι}
    {Λ : ℕ → ι → Type*}
    {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ} {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ}
    (h : ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ p ∈ Dom W, ∀ l : Λ W p,
      μ W (vol p) {ω | (W : ℝ) ^ ε * Y W p l < ‖X W p l ω‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)))
    (C₀ C₁ : ℝ) (hY : ∀ W p, p ∈ Dom W → ∀ l, (W : ℝ) ^ (-C₁) ≤ Y W p l)
    (hm : ∀ W p, p ∈ Dom W → ∀ l, AEStronglyMeasurable (X W p l) (μ W (vol p)))
    (r : ℕ) (hr : 1 ≤ r) (Cr : ℝ) (Wc : ℕ)
    (hcrude : ∀ W : ℕ, Wc ≤ W → ∀ p ∈ Dom W, ∀ l : Λ W p,
      Integrable (fun ω => ‖X W p l ω‖ ^ (2 * r)) (μ W (vol p)) ∧
        ∫ ω, ‖X W p l ω‖ ^ (2 * r) ∂(μ W (vol p)) ≤ Cr * (W : ℝ) ^ (2 * r * C₀))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ p ∈ Dom W, ∀ l : Λ W p,
      (∫ ω, ‖X W p l ω‖ ^ r ∂(μ W (vol p))) ^ (1 / (r : ℝ)) ≤ (W : ℝ) ^ ε * Y W p l := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hrne : r ≠ 0 := by omega
  set m : ℝ := |C₀| + |C₁| + 1 with hm_def
  have hm1 : 1 ≤ m := by
    have := abs_nonneg C₀
    have := abs_nonneg C₁
    linarith
  set D : ℝ := 2 * r * m with hD_def
  have hD : 0 < D := by positivity
  obtain ⟨W₁, hW₁⟩ := h (ε / 2) D (half_pos hε) hD
  set M : ℝ := max Cr 0 with hM_def
  have hM0 : 0 ≤ M := le_max_right _ _
  set c : ℝ := M ^ (1 / (2 * (r : ℝ))) with hc_def
  have hc0 : 0 ≤ c := Real.rpow_nonneg hM0 _
  have hcpow : c ^ (2 * r) = M := by
    have h2r : (2 * r : ℕ) ≠ 0 := by omega
    have := Real.rpow_inv_natCast_pow hM0 h2r
    rw [hc_def, show 1 / (2 * (r : ℝ)) = ((2 * r : ℕ) : ℝ)⁻¹ by push_cast; rw [one_div]]
    exact this
  obtain ⟨n, hn⟩ := exists_nat_ge c
  have ht : Tendsto (fun W : ℕ => (W : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop
  obtain ⟨W₂, hW₂⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 2)
  refine ⟨max (max (max W₁ n) (max W₂ 1)) Wc, fun W hW p hp l => ?_⟩
  have hW' : max (max W₁ n) (max W₂ 1) ≤ W := (le_max_left _ _).trans hW
  have hWa : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW')
  have hWb : n ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW')
  have hWc : W₂ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW')
  have hWd : 1 ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW')
  have hWe : Wc ≤ W := (le_max_right _ _).trans hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hWd
  have hWpos : (0 : ℝ) < W := by linarith
  have hcW : c ≤ (W : ℝ) := hn.trans (by exact_mod_cast hWb)
  have hu2 : (2 : ℝ) ≤ (W : ℝ) ^ (ε / 2) := hW₂ W hWc
  have hYC : (W : ℝ) ^ (-C₁) ≤ Y W p l := hY W p hp l
  have hYpos : 0 < Y W p l := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hYC
  obtain ⟨hint, hmom⟩ := hcrude W hWe p hp l
  have hWε : (W : ℝ) ^ ε = (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hWpos]; congr 1; ring
  set K : ℝ := c * (W : ℝ) ^ C₀ with hK_def
  have hK0 : 0 ≤ K := mul_nonneg hc0 (Real.rpow_nonneg hWpos.le _)
  have hKpow : K ^ (2 * r) = M * (W : ℝ) ^ (2 * r * C₀) := by
    rw [hK_def, mul_pow, hcpow, ← Real.rpow_mul_natCast hWpos.le]
    congr 2
    push_cast
    ring
  have hKm : ∫ ω, ‖X W p l ω‖ ^ (2 * r) ∂(μ W (vol p)) ≤ K ^ (2 * r) := by
    rw [hKpow]
    exact hmom.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hWpos.le _))
  have htail : ((μ W (vol p)) {ω | (W : ℝ) ^ (ε / 2) * Y W p l < ‖X W p l ω‖}).toReal ≤
      (W : ℝ) ^ (-D) :=
    ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hWpos.le _) (hW₁ W hWa p hp l)
  have hE := moment_of_tail (μ W (vol p)) (fun ω => ‖X W p l ω‖) (fun ω => norm_nonneg _)
    (hm W p hp l).norm r hr K ((W : ℝ) ^ (ε / 2) * Y W p l) ((W : ℝ) ^ (-D)) hK0
    (mul_nonneg (Real.rpow_nonneg hWpos.le _) hYpos.le) (Real.rpow_nonneg hWpos.le _) hint hKm
    htail
  have hδ : ((W : ℝ) ^ (-D)) ^ (1 / (2 * (r : ℝ))) = (W : ℝ) ^ (-m) := by
    rw [← Real.rpow_mul hWpos.le]
    congr 1
    rw [hD_def]
    field_simp
  have hcorr : K * ((W : ℝ) ^ (-D)) ^ (1 / (2 * (r : ℝ))) ≤ Y W p l := by
    rw [hδ, hK_def, mul_assoc, ← Real.rpow_add hWpos]
    have hexp : C₀ + -m ≤ -|C₁| - 1 := by
      have := le_abs_self C₀
      rw [hm_def]; linarith
    calc c * (W : ℝ) ^ (C₀ + -m) ≤ (W : ℝ) * (W : ℝ) ^ (-|C₁| - 1) :=
          mul_le_mul hcW (Real.rpow_le_rpow_of_exponent_le hWr hexp)
            (Real.rpow_nonneg hWpos.le _) hWpos.le
      _ = (W : ℝ) ^ (1 : ℝ) * (W : ℝ) ^ (-|C₁| - 1) := by rw [Real.rpow_one]
      _ = (W : ℝ) ^ (-|C₁|) := by
          rw [← Real.rpow_add hWpos]; congr 1; ring
      _ ≤ (W : ℝ) ^ (-C₁) :=
          Real.rpow_le_rpow_of_exponent_le hWr (by linarith [le_abs_self C₁])
      _ ≤ Y W p l := hYC
  have hYle : Y W p l ≤ (W : ℝ) ^ (ε / 2) * Y W p l := by
    have : (1 : ℝ) ≤ (W : ℝ) ^ (ε / 2) := by linarith
    exact le_mul_of_one_le_left hYpos.le this
  calc (∫ ω, ‖X W p l ω‖ ^ r ∂(μ W (vol p))) ^ (1 / (r : ℝ))
      ≤ (W : ℝ) ^ (ε / 2) * Y W p l + K * ((W : ℝ) ^ (-D)) ^ (1 / (2 * (r : ℝ))) := hE
    _ ≤ (W : ℝ) ^ (ε / 2) * Y W p l + (W : ℝ) ^ (ε / 2) * Y W p l :=
        add_le_add le_rfl (hcorr.trans hYle)
    _ = 2 * (W : ℝ) ^ (ε / 2) * Y W p l := by ring
    _ ≤ (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) * Y W p l :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu2 (by linarith)) hYpos.le
    _ = (W : ℝ) ^ ε * Y W p l := by rw [hWε]

/-- Markov at order `p` and a union over a finite set of labels. -/
private lemma averagingInput_markov_union {Ω' ι : Type*} [MeasurableSpace Ω']
    (P : Measure Ω') [IsProbabilityMeasure P] (R : ι → Ω' → ℂ) (S : Finset ι) (p : ℕ)
    (T Cp : ℝ) (hT : 0 < T)
    (h : ∀ s ∈ S, Integrable (fun ω => ‖R s ω‖ ^ p) P ∧ ∫ ω, ‖R s ω‖ ^ p ∂P ≤ Cp) :
    P {ω | ∃ s ∈ S, T < ‖R s ω‖} ≤ ENNReal.ofReal ((S.card : ℝ) * (Cp / T ^ p)) := by
  have hset : {ω | ∃ s ∈ S, T < ‖R s ω‖} = ⋃ s ∈ S, {ω | T < ‖R s ω‖} := by
    ext ω; simp
  have hone : ∀ s ∈ S, P {ω | T < ‖R s ω‖} ≤ ENNReal.ofReal (Cp / T ^ p) := by
    intro s hs
    obtain ⟨hint, hmom⟩ := h s hs
    have hsub : {ω | T < ‖R s ω‖} ⊆ {ω | T ^ p ≤ ‖R s ω‖ ^ p} := fun ω hω =>
      pow_le_pow_left₀ hT.le (le_of_lt hω) p
    have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => ‖R s ω‖ ^ p)
      (Filter.Eventually.of_forall fun ω => pow_nonneg (norm_nonneg _) p) hint (T ^ p)
    have hTp : 0 < T ^ p := pow_pos hT p
    have h1 : P.real {ω | T < ‖R s ω‖} ≤ Cp / T ^ p := by
      rw [le_div_iff₀ hTp]
      calc P.real {ω | T < ‖R s ω‖} * T ^ p = T ^ p * P.real {ω | T < ‖R s ω‖} := mul_comm _ _
        _ ≤ T ^ p * P.real {ω | T ^ p ≤ ‖R s ω‖ ^ p} :=
            mul_le_mul_of_nonneg_left (measureReal_mono hsub) hTp.le
        _ ≤ ∫ ω, ‖R s ω‖ ^ p ∂P := hmark
        _ ≤ Cp := hmom
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal h1
  calc P {ω | ∃ s ∈ S, T < ‖R s ω‖} = P (⋃ s ∈ S, {ω | T < ‖R s ω‖}) := by rw [hset]
    _ ≤ ∑ s ∈ S, P {ω | T < ‖R s ω‖} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _s ∈ S, ENNReal.ofReal (Cp / T ^ p) := Finset.sum_le_sum hone
    _ = ENNReal.ofReal ((S.card : ℝ) * (Cp / T ^ p)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- The norming step of (5.34) [fo:eq:weighted-sampling-input]: with `2 max(C_s, 1) T ≤ B` and
`δ ≤ B/2`, if `B < ‖R_l‖` for some label `l` then, off the failure event of the sampling
inequality, some sampled label has `‖R_s‖ > T`; Markov at order `p` and a union over the sample
set bound the probability of the latter. -/
private lemma averagingInput_event_bound {Ω' ι : Type*} [MeasurableSpace Ω']
    (P : Measure Ω') [IsProbabilityMeasure P] (R : ι → Ω' → ℂ) (S : Finset ι)
    (Cs δ η B T : ℝ) (p : ℕ) (Cp : ℝ) (hT : 0 < T) (hB : 2 * max Cs 1 * T ≤ B)
    (hδ : δ ≤ B / 2)
    (hS : SampleBound P R (fun _ => 1) S Cs δ η)
    (h : ∀ s ∈ S, Integrable (fun ω => ‖R s ω‖ ^ p) P ∧ ∫ ω, ‖R s ω‖ ^ p ∂P ≤ Cp) :
    P {ω | ∃ l, B < ‖R l ω‖} ≤
      ENNReal.ofReal η + ENNReal.ofReal ((S.card : ℝ) * (Cp / T ^ p)) := by
  unfold SampleBound at hS
  have hS' : P {ω | ∃ l, Cs * (⨆ s : S, ‖R s ω‖) + δ < ‖R l ω‖} ≤ ENNReal.ofReal η := by
    simpa only [div_one] using hS
  refine le_trans (measure_mono ?_) ((measure_union_le _ _).trans
    (add_le_add hS' (averagingInput_markov_union P R S p T Cp hT h)))
  intro ω hω
  obtain ⟨l, hl⟩ := hω
  by_cases hF : ∃ l', Cs * (⨆ s : S, ‖R s ω‖) + δ < ‖R l' ω‖
  · exact Or.inl hF
  · refine Or.inr ?_
    push Not at hF
    have hl' := hF l
    have hM0 : 0 ≤ ⨆ s : S, ‖R s ω‖ := Real.iSup_nonneg fun s => norm_nonneg _
    have h1 : B < max Cs 1 * (⨆ s : S, ‖R s ω‖) + B / 2 := by
      have : Cs * (⨆ s : S, ‖R s ω‖) ≤ max Cs 1 * (⨆ s : S, ‖R s ω‖) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hM0
      linarith
    have h2 : T < ⨆ s : S, ‖R s ω‖ := by
      have h3 : 2 * max Cs 1 * T < 2 * max Cs 1 * (⨆ s : S, ‖R s ω‖) := by nlinarith
      have hC : 0 < 2 * max Cs 1 := by
        have := le_max_right Cs 1
        linarith
      exact lt_of_mul_lt_mul_left h3 hC.le
    have hne : Nonempty S := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      rw [Real.iSup_of_isEmpty] at h2
      linarith
    obtain ⟨s, hs⟩ := exists_lt_of_lt_ciSup h2
    exact ⟨s, s.2, hs⟩

/-- The numerical closing inequality of the Markov union bound:
`W^{-(D+1)} + N · C_p ((W^{ε/16})²κ²)^p / (W^{ε/2}κ²)^p ≤ W^{-D}` for `N ≤ W^{C_S}`,
`(ε/4) p ≥ C_S + D + 2` and `W ≥ 2 + C_p`. -/
private lemma averagingInput_final_ineq (W : ℝ) (hW : 2 ≤ W) (Cp : ℝ) (hCp : 0 < Cp)
    (hWC : 2 + Cp ≤ W) (D CS ε : ℝ) (hε : 0 < ε) (p : ℕ)
    (hεp : CS + D + 2 ≤ ε * p / 4) (N : ℝ) (hN : N ≤ W ^ CS) (κ : ℝ)
    (hκ : 0 < κ) :
    W ^ (-(D + 1)) + N * (Cp * ((W ^ (ε / 16)) ^ 2 * κ ^ 2) ^ p / (W ^ (ε / 2) * κ ^ 2) ^ p) ≤
      W ^ (-D) := by
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hκ2 : 0 < κ ^ 2 := by positivity
  -- the ratio
  have hratio : Cp * ((W ^ (ε / 16)) ^ 2 * κ ^ 2) ^ p / (W ^ (ε / 2) * κ ^ 2) ^ p =
      Cp * (W ^ (-(3 * ε / 8))) ^ p := by
    have h1 : (W ^ (ε / 16)) ^ 2 = W ^ (ε / 8) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
    have h2 : W ^ (-(3 * ε / 8)) = W ^ (ε / 8) / W ^ (ε / 2) := by
      rw [← Real.rpow_sub hW0]; congr 1; ring
    rw [h1, h2, mul_pow, mul_pow, div_pow, mul_div_assoc]
    have hWe : 0 < (W ^ (ε / 2)) := Real.rpow_pos_of_pos hW0 _
    field_simp
  rw [hratio]
  -- the power
  have hpow : (W ^ (-(3 * ε / 8))) ^ p ≤ W ^ (-(CS + D + 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    refine Real.rpow_le_rpow_of_exponent_le hW1 ?_
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    nlinarith
  have hterm : N * (Cp * (W ^ (-(3 * ε / 8))) ^ p) ≤ Cp * W ^ (-(D + 2)) := by
    calc N * (Cp * (W ^ (-(3 * ε / 8))) ^ p) ≤ W ^ CS * (Cp * W ^ (-(CS + D + 2))) := by
          gcongr
      _ = Cp * W ^ (-(D + 2)) := by
          rw [mul_left_comm, ← Real.rpow_add hW0]; congr 2; ring
  have e1 : W ^ (-(D + 1)) = W ^ (-D) * W⁻¹ := by
    rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hW0, Real.rpow_neg_one]
  have e2 : W ^ (-(D + 2)) = W ^ (-D) * (W ^ 2)⁻¹ := by
    rw [show -(D + 2) = -D + (-2) by ring, Real.rpow_add hW0, Real.rpow_neg hW0.le (2 : ℝ),
      Real.rpow_two]
  have hWD : 0 < W ^ (-D) := Real.rpow_pos_of_pos hW0 _
  have hfin : W⁻¹ + Cp * (W ^ 2)⁻¹ ≤ 1 := by
    rw [← sub_nonneg]
    have : 1 - (W⁻¹ + Cp * (W ^ 2)⁻¹) = (W ^ 2 - W - Cp) / W ^ 2 := by
      field_simp
      ring
    rw [this]
    apply div_nonneg _ (by positivity)
    nlinarith
  calc W ^ (-(D + 1)) + N * (Cp * (W ^ (-(3 * ε / 8))) ^ p)
      ≤ W ^ (-D) * W⁻¹ + Cp * (W ^ (-D) * (W ^ 2)⁻¹) := by rw [e1, ← e2]; linarith
    _ = W ^ (-D) * (W⁻¹ + Cp * (W ^ 2)⁻¹) := by ring
    _ ≤ W ^ (-D) * 1 := mul_le_mul_of_nonneg_left hfin hWD.le
    _ = W ^ (-D) := mul_one _

/-- A domination with the maximum over labels inside the probability gives the bound at each
single label. -/
private lemma averagingInput_label {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι}
    {Λ : ℕ → ι → Type*} {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ}
    {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ} (h : PrecMax vol Dom X Y) :
    ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ p ∈ Dom W, ∀ l : Λ W p,
      μ W (vol p) {ω | (W : ℝ) ^ ε * Y W p l < ‖X W p l ω‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  intro ε D hε hD
  obtain ⟨W₀, hW⟩ := h ε D hε hD
  refine ⟨W₀, fun W hW0 p hp l => (measure_mono ?_).trans (hW W hW0 p hp)⟩
  intro ω hω
  exact ⟨l, hω⟩

/-- `W^{-1/2} ≤ χ` gives `W⁻¹ ≤ χ²`. -/
private lemma averagingInput_inv_le_sq {W : ℝ} (hW : 0 < W) {χ : ℝ}
    (h : W ^ (-(1 / 2 : ℝ)) ≤ χ) : W⁻¹ ≤ χ ^ 2 := by
  have h0 : 0 ≤ W ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hW.le _
  have hsq : (W ^ (-(1 / 2 : ℝ))) ^ 2 = W⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    norm_num
    exact Real.rpow_neg_one W
  rw [← hsq]
  exact pow_le_pow_left₀ h0 h 2

/-- Lemma 5.9 [gc:lem:residual] (i), (5.29) [gc:eq:averaging-input], from the rows (6.13)
[gc:eq:residual-row-bounds], the crude moments and the residual sampling: the Hölder step on
the exceptional events gives the moments of `⟨G⟩_{ab}` and of the traceless entries from their
dominations, (7.26) [gc:eq:residual-fixed-moment] gives the moments of the residual, and Markov's
inequality on the sample set of the residual gives the domination of the residual with the maximum
over all labels inside the probability. -/
private theorem averagingInput_clause_one (base : ℕ → Set FlowPt) (J : ℕ) (Γ : ℝ) (W₀ : ℕ)
    (hrows : SegRows base J Γ W₀) (hcrude : CrudeInput base J) (hsamp : SamplingInput base J) :
    ∀ Dom : ℕ → Set (FlowPt × ℝ), (∀ W x, x ∈ Dom W → SegAdm base J W x) →
    ∀ (K χ : ℕ → FlowPt × ℝ → ℝ) (CK : ℝ), (∀ W x, x ∈ Dom W →
      1 ≤ K W x ∧ K W x ≤ (W : ℝ) ^ CK ∧ (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ χ W x) →
    PrecMax (fun x : FlowPt × ℝ => x.1.L) Dom (Λ := fun _ x => Fin x.1.L × Fin x.1.L)
      (fun W x ab ω => blockTr (segG W x ω) ab.1 ab.2) (fun W x _ => K W x) →
    PrecMax (fun x : FlowPt × ℝ => x.1.L) Dom
      (Λ := fun W x => (Fin x.1.L × Fin W) × (Fin x.1.L × Fin W))
      (fun W x e ω => segG W x ω e.1 e.2 -
        if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0)
      (fun W x _ => K W x * χ W x) →
    PrecMax (fun x : FlowPt × ℝ => x.1.L) Dom (Λ := fun _ x => Fin x.1.L × Fin x.1.L)
      (fun W x ab ω => segRes W x ω ab.1 ab.2) (fun W x _ => (K W x * χ W x) ^ 2) := by
  intro Dom hDom K χ CK hKχ hP1 hP2 ε D hε hD
  obtain ⟨CS, Cs, Ws, hWs⟩ := hsamp.2 2 (D + 1) two_pos (by linarith)
  obtain ⟨p, hp2, hpe, hpε⟩ : ∃ p : ℕ, 2 ≤ p ∧ Even p ∧ CS + D + 2 ≤ ε * p / 4 := by
    set n : ℕ := ⌈4 * (|CS| + D + 2) / ε⌉₊ with hn
    refine ⟨2 * (n + 1), by omega, ⟨n + 1, by ring⟩, ?_⟩
    have h1 : 4 * (|CS| + D + 2) / ε ≤ n := Nat.le_ceil _
    have h2 : 4 * (|CS| + D + 2) ≤ n * ε := (div_le_iff₀ hε).mp h1
    have h3 : CS ≤ |CS| := le_abs_self CS
    push_cast
    nlinarith
  obtain ⟨C₀, hC₀⟩ := averagingInput_crude_trace base J hcrude
  obtain ⟨Cr, Wc, hCr⟩ := hC₀ (2 * p) (by omega)
  have hε1 : 0 < ε / 16 := by positivity
  obtain ⟨WA, hWA⟩ := averagingInput_lemmaE (averagingInput_label hP1) C₀ 0
    (fun W x hx l => by simpa using (hKχ W x hx).1)
    (fun W x _ l => (averagingInput_measurable_blockTr W x _ _).aestronglyMeasurable)
    (2 * p) (by omega) Cr Wc
    (fun W hW x hx l => (hCr W hW x (hDom W x hx)).1 l.1 l.2) (ε / 16) hε1
  obtain ⟨WB, hWB⟩ := averagingInput_lemmaE (averagingInput_label hP2) C₀ (1 / 2)
    (fun W x hx l => by
      obtain ⟨hK1, -, hχ⟩ := hKχ W x hx
      have hχ0 : 0 ≤ χ W x := le_trans (Real.rpow_nonneg (Nat.cast_nonneg W) _) hχ
      exact hχ.trans (le_mul_of_one_le_left hχ0 hK1))
    (fun W x _ l => (averagingInput_measurable_traceless W x _).aestronglyMeasurable)
    (2 * p) (by omega) Cr Wc
    (fun W hW x hx l => (hCr W hW x (hDom W x hx)).2 l) (ε / 16) hε1
  set Γ' : ℝ := max Γ 1 with hΓ'
  have hΓ'0 : 0 < Γ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨Cp, hCp, HCp⟩ := averagingInput_bridge_trace p hp2 hpe 1 Γ' one_pos hΓ'0
  have ht : Tendsto (fun W : ℕ => (W : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop
  obtain ⟨Wt, hWt⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (2 * max Cs 1))
  refine ⟨max (max (max W₀ 2) (max Ws Wc)) (max (max WA WB) (max Wt ⌈2 + Cp⌉₊)),
    fun W hW x hx => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW₀, hW2⟩, hWs', hWc'⟩, ⟨hWA', hWB'⟩, hWt', hWCp'⟩ := hW
  have hxA : SegAdm base J W x := hDom W x hx
  obtain ⟨hK1, hKW, hχW⟩ := hKχ W x hx
  have hW2r : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  have hW0r : (0 : ℝ) < W := by linarith
  have hW1 : 1 ≤ W := by omega
  have hW1r : (1 : ℝ) ≤ W := by linarith
  have hWCp : 2 + Cp ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWCp')
  have hrowx : averagingInput_rowsAt Γ' x :=
    averagingInput_rowsAt_mono (le_max_left Γ 1) (hrows W hW₀ x hxA)
  obtain ⟨S₁, S₂, hS₁, -, -, -, hSR⟩ := hWs W hWs' x hxA
  -- the moments of the traces and of the traceless entries
  have ha1 : (1 : ℝ) ≤ (W : ℝ) ^ (ε / 16) := Real.one_le_rpow hW1r hε1.le
  have hexp : (1 : ℝ) / ((2 * p : ℕ) : ℝ) = 1 / (2 * (p : ℝ)) := by push_cast; ring
  have hmG : ∀ a b : Fin x.1.L,
      (∫ ω, ‖blockTr (segG W x ω) a b‖ ^ (2 * p) ∂(μ W x.1.L)) ^ (1 / (2 * (p : ℝ))) ≤
        1 * ((W : ℝ) ^ (ε / 16) * K W x) := by
    intro a b
    have h := hWA W hWA' x hx (a, b)
    rw [hexp] at h
    rw [one_mul]
    exact h
  have hmZ : ∀ e₁ e₂ : Fin x.1.L × Fin W,
      (∫ ω, ‖segG W x ω e₁ e₂ - if e₁.2 = e₂.2 then blockTr (segG W x ω) e₁.1 e₂.1 else 0‖ ^
        (2 * p) ∂(μ W x.1.L)) ^ (1 / (2 * (p : ℝ))) ≤
        1 * ((W : ℝ) ^ (ε / 16) * K W x) * χ W x := by
    intro e₁ e₂
    have h := hWB W hWB' x hx (e₁, e₂)
    rw [hexp] at h
    calc _ ≤ (W : ℝ) ^ (ε / 16) * (K W x * χ W x) := h
      _ = _ := by ring
  have hres := HCp W hW1 x hrowx ((W : ℝ) ^ (ε / 16) * K W x) (χ W x)
    (one_le_mul_of_one_le_of_one_le ha1 hK1) hχW hmG hmZ
  -- the event
  have hχ0 : 0 < χ W x := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0r _) hχW
  have hκ0 : 0 < K W x * χ W x := mul_pos (by linarith) hχ0
  have hκ2 : 0 < (K W x * χ W x) ^ 2 := by positivity
  have hT : 0 < (W : ℝ) ^ (ε / 2) * (K W x * χ W x) ^ 2 :=
    mul_pos (Real.rpow_pos_of_pos hW0r _) hκ2
  have hWε : (W : ℝ) ^ ε = (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hW0r]; congr 1; ring
  have hB : 2 * max Cs 1 * ((W : ℝ) ^ (ε / 2) * (K W x * χ W x) ^ 2) ≤
      (W : ℝ) ^ ε * (K W x * χ W x) ^ 2 := by
    calc 2 * max Cs 1 * ((W : ℝ) ^ (ε / 2) * (K W x * χ W x) ^ 2) ≤
        (W : ℝ) ^ (ε / 2) * ((W : ℝ) ^ (ε / 2) * (K W x * χ W x) ^ 2) :=
          mul_le_mul_of_nonneg_right (hWt W hWt') hT.le
      _ = (W : ℝ) ^ ε * (K W x * χ W x) ^ 2 := by rw [hWε]; ring
  have hδ : (W : ℝ) ^ (-(2 : ℝ)) ≤ (W : ℝ) ^ ε * (K W x * χ W x) ^ 2 / 2 := by
    have h1 : (W : ℝ)⁻¹ ≤ χ W x ^ 2 := averagingInput_inv_le_sq hW0r hχW
    have h2 : χ W x ^ 2 ≤ (K W x * χ W x) ^ 2 :=
      pow_le_pow_left₀ hχ0.le (le_mul_of_one_le_left hχ0.le hK1) 2
    have h3 : (1 : ℝ) ≤ (W : ℝ) ^ ε := Real.one_le_rpow hW1r hε.le
    have h4 : (W : ℝ) ^ (-(2 : ℝ)) = (W : ℝ)⁻¹ * (W : ℝ)⁻¹ := by
      rw [Real.rpow_neg hW0r.le, Real.rpow_two, sq, mul_inv]
    have h5 : (W : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW2r
    have h6 : (W : ℝ)⁻¹ * (W : ℝ)⁻¹ ≤ (W : ℝ)⁻¹ * (1 / 2) :=
      mul_le_mul_of_nonneg_left h5 (inv_nonneg.mpr hW0r.le)
    have h7 : (K W x * χ W x) ^ 2 ≤ (W : ℝ) ^ ε * (K W x * χ W x) ^ 2 :=
      le_mul_of_one_le_left hκ2.le h3
    rw [h4]
    nlinarith
  have hev := averagingInput_event_bound (μ W x.1.L) (fun ab ω => segRes W x ω ab.1 ab.2) S₁ Cs
    ((W : ℝ) ^ (-(2 : ℝ))) ((W : ℝ) ^ (-(D + 1)))
    ((W : ℝ) ^ ε * (K W x * χ W x) ^ 2) ((W : ℝ) ^ (ε / 2) * (K W x * χ W x) ^ 2) p
    (Cp * (((W : ℝ) ^ (ε / 16) * K W x) ^ 2 * χ W x ^ 2) ^ p) hT hB hδ hSR
    (fun s _ => hres s.1 s.2)
  refine hev.trans ?_
  rw [← ENNReal.ofReal_add (Real.rpow_nonneg hW0r.le _) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hfin := averagingInput_final_ineq (W : ℝ) hW2r Cp hCp hWCp D CS ε hε p hpε S₁.card hS₁
    (K W x * χ W x) hκ0
  have heq : Cp * (((W : ℝ) ^ (ε / 16) * K W x) ^ 2 * χ W x ^ 2) ^ p =
      Cp * (((W : ℝ) ^ (ε / 16)) ^ 2 * (K W x * χ W x) ^ 2) ^ p := by
    congr 2; ring
  rw [heq]
  exact hfin

/-- Lemma 5.9 [gc:lem:residual] from the rows (6.13) [gc:eq:residual-row-bounds], the crude
moments (first bound of (5.33) [fo:eq:coarse-time-input]) and the residual sampling of (5.34)
[fo:eq:weighted-sampling-input], for every base family and depth. -/
theorem averagingInput_of_rows (base : ℕ → Set FlowPt) (J : ℕ) (Γ : ℝ) (W₀ : ℕ)
    (hrows : SegRows base J Γ W₀) (hcrude : CrudeInput base J) (hsamp : SamplingInput base J) :
    AveragingInput base J := by
  refine ⟨averagingInput_clause_one base J Γ W₀ hrows hcrude hsamp, averaging_haar base J, ?_⟩
  intro p hp hpe C hC
  obtain ⟨Cp, hCp, H⟩ := averagingInput_bridge_entries p hp hpe C (max Γ 1) hC
    (lt_of_lt_of_le one_pos (le_max_right _ _))
  refine ⟨Cp, max W₀ 1, fun W hW x hx χ hχ hE a b => ?_⟩
  exact H W (le_trans (le_max_right _ _) hW) x
    (averagingInput_rowsAt_mono (le_max_left Γ 1)
      (hrows W (le_trans (le_max_left _ _) hW) x hx)) χ hχ (fun e₁ e₂ => (hE e₁ e₂).2) a b

/-- Lemma 5.9 [gc:lem:residual] at bounded coupling, for every base family inside the range of
`baseBdd`. -/
theorem averagingInput_of_bdd (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c')
    (gmin ρ : ℕ → ℝ) (hgmin : ∀ W, 0 < gmin W) (hρ : Tendsto ρ atTop atTop) (J : ℕ)
    (base : ℕ → Set FlowPt)
    (hbase : ∀ W p, p ∈ base W → gmin W ≤ p.g ∧ RegBdd C B c' p.L p.g p.E ∧
      ρ W * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ (W : ℝ) ^ 2 ∧ 1 / 2 ≤ p.u ∧
      (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u) :
    AveragingInput base J := by
  obtain ⟨Γ, -, W₀, H⟩ := segRows_bdd C B c' hC hB hc' gmin ρ hgmin hρ J
  exact averagingInput_of_rows base J Γ W₀ (H base hbase)
    (crudeInput_of_bdd C B c' hC hB hc' gmin ρ hgmin hρ J base hbase)
    (samplingInput_of_bdd C B c' hC hB hc' gmin ρ hgmin hρ J base hbase)

/-- Lemma 5.9 [gc:lem:residual] at large coupling, for every base family inside the range of
`baseLarge`. -/
theorem averagingInput_of_large (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) (J : ℕ) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ base : ℕ → Set FlowPt,
        (∀ W p, p ∈ base W → Cκ ≤ p.g ∧ |p.E| ≤ 2 - 3 * κ / 4 ∧
          ρ W * p.g ^ 2 * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ CV * p.g ^ 2 * (W : ℝ) ^ 2 ∧
          1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u) →
        AveragingInput base J := by
  obtain ⟨Cκ₁, Γ, h1, -, H1⟩ := segRows_large κ CV hκ hκ2 hCV J
  obtain ⟨Cκ₂, h2, H2⟩ := crudeInput_of_large κ CV hκ hκ2 hCV J
  obtain ⟨Cκ₃, h3, H3⟩ := samplingInput_of_large κ CV hκ hκ2 hCV J
  refine ⟨max Cκ₁ (max Cκ₂ Cκ₃), h1.trans (le_max_left _ _),
    fun Cκ hCκ ρ hρ base hbase => ?_⟩
  have hc1 : Cκ₁ ≤ Cκ := (le_max_left _ _).trans hCκ
  have hc2 : Cκ₂ ≤ Cκ := ((le_max_left _ _).trans (le_max_right _ _)).trans hCκ
  have hc3 : Cκ₃ ≤ Cκ := ((le_max_right _ _).trans (le_max_right _ _)).trans hCκ
  obtain ⟨W₀, hW₀⟩ := H1 Cκ hc1 ρ hρ
  exact averagingInput_of_rows base J Γ W₀ (hW₀ base hbase) (H2 Cκ hc2 ρ hρ base hbase)
    (H3 Cκ hc3 ρ hρ base hbase)

/-- Lemma 5.9 [gc:lem:residual] at bounded coupling. -/
theorem averagingInput_bdd (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c')
    (gmin ρ : ℕ → ℝ) (hgmin : ∀ W, 0 < gmin W) (hρ : Tendsto ρ atTop atTop) (J : ℕ) :
    AveragingInput (baseBdd C B c' gmin ρ) J :=
  averagingInput_of_bdd C B c' hC hB hc' gmin ρ hgmin hρ J (baseBdd C B c' gmin ρ)
    (fun _ _ hp => hp)

/-- Lemma 5.9 [gc:lem:residual] at large coupling. -/
theorem averagingInput_large (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) (J : ℕ) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      AveragingInput (baseLarge κ Cκ CV ρ) J := by
  obtain ⟨Cκ₀, h1, H⟩ := averagingInput_of_large κ CV hκ hκ2 hCV J
  exact ⟨Cκ₀, h1, fun Cκ hCκ ρ hρ => H Cκ hCκ ρ hρ (baseLarge κ Cκ CV ρ) (fun _ _ hp => hp)⟩

end LSBA
