import LSBA.Transfer.Transition
import LSBA.Gauss.GUEContract
import LSBA.Gauss.GUENormMoment

/-!
# The mean of the first matrix observable

(11.20) [uvg:eq:mmean]: `P_g m₁ = −e^{−2iθ} m₁ + e^{−2iθ} h²g⁻² (1 + m₁)(1 + 2m₁ + m₂) + O(g⁻⁴)`,
for every `W ≥ 1`, `g ≥ 1` and state, with the constant depending only on `E₀`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Norm estimates for the one-step update -/

private lemma mm_normalH_nonneg (E : ℝ) : 0 ≤ normalH E := by
  unfold normalH freeAngle
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg (E / 2))
    (Real.arccos_le_pi (E / 2))
  positivity

/-- `h_θ ≤ (2 √(1 − E₀²/4))⁻¹` for `|E| ≤ E₀ < 2`. -/
private lemma mm_normalH_le {E₀ E : ℝ} (hE₀ : E₀ < 2) (hE : |E| ≤ E₀) :
    normalH E ≤ (2 * √(1 - E₀ ^ 2 / 4))⁻¹ := by
  unfold normalH freeAngle
  rw [Real.sin_arccos]
  have ha := abs_nonneg E
  have h1 : E ^ 2 ≤ E₀ ^ 2 := by
    rw [← sq_abs E]
    exact pow_le_pow_left₀ ha hE 2
  have h2 : 0 < 1 - E₀ ^ 2 / 4 := by nlinarith
  have h3 : √(1 - E₀ ^ 2 / 4) ≤ √(1 - (E / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have h4 : 0 < √(1 - E₀ ^ 2 / 4) := Real.sqrt_pos.mpr h2
  exact inv_anti₀ (by positivity) (by linarith)

private lemma mm_norm_normalPhase (E : ℝ) : ‖normalPhase E‖ = 1 := by
  unfold normalPhase
  rw [norm_neg, show 2 * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma mm_norm_lin_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : ‖Matrix.toEuclideanLin A v‖ ≤ ‖A‖ * ‖v‖ :=
  (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) A).le_opNorm v

/-- Every entry of a matrix has modulus at most its operator norm. -/
private lemma mm_norm_entry_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) :
    ‖A i j‖ ≤ ‖A‖ := by
  have h : A i j = inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (Matrix.toEuclideanLin A (EuclideanSpace.single j (1 : ℂ))) := by
    simp [Matrix.toLpLin_apply, EuclideanSpace.inner_single_left]
  rw [h]
  calc ‖inner ℂ (EuclideanSpace.single i (1 : ℂ))
        (Matrix.toEuclideanLin A (EuclideanSpace.single j (1 : ℂ)))‖
      ≤ ‖EuclideanSpace.single i (1 : ℂ)‖ *
          ‖Matrix.toEuclideanLin A (EuclideanSpace.single j (1 : ℂ))‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (‖A‖ * 1) := by
        gcongr
        · simp
        · exact (mm_norm_lin_le A _).trans (by simp)
    _ = ‖A‖ := by ring

/-- The normalized trace has norm at most the operator norm. -/
private lemma mm_norm_trace_le {W : ℕ} (hW : 1 ≤ W) (B : Matrix (Fin W) (Fin W) ℂ) :
    ‖(W : ℂ)⁻¹ * B.trace‖ ≤ ‖B‖ := by
  have htr : ‖B.trace‖ ≤ W * ‖B‖ := by
    calc ‖B.trace‖ = ‖∑ i, B i i‖ := rfl
      _ ≤ ∑ i, ‖B i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin W, ‖B‖ := Finset.sum_le_sum fun i _ => mm_norm_entry_le B i i
      _ = W * ‖B‖ := by simp
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖B.trace‖ ≤ (W : ℝ)⁻¹ * (W * ‖B‖) := by gcongr
    _ = ‖B‖ := by field_simp

/-! ### The fourth-order expansion of the update (11.3) [lg:eq:matrix-update] -/

/-- `X = i h_θ g⁻¹ V (I + C)`, the first-order term of the update (11.3) [lg:eq:matrix-update]. -/
private def mmD (g E : ℝ) {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))

/-- The normalized trace `W⁻¹ Tr[(I + C) X^k]` of the order-`k` term of the update. -/
private def mmP (g E : ℝ) {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (k : ℕ) : ℂ :=
  (W : ℂ)⁻¹ * ((1 + C) * mmD g E C V ^ k).trace

/-- The fourth-order remainder of the update (11.3) [lg:eq:matrix-update]:
`X⁴ + (C + X) X⁴ F⁻¹`. -/
private def mmR (g E : ℝ) {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  mmD g E C V ^ 4 + (C + mmD g E C V) * mmD g E C V ^ 4 * (stepF g E C V)⁻¹

/-- The exact expansion `C' = −e^{−2iθ}[C + (I + C)(X + X² + X³) + X⁴ + (C + X) X⁴ F⁻¹]` of (11.3)
[lg:eq:matrix-update]. -/
private lemma mm_expand {W : ℕ} (g E : ℝ) {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) :
    stepC g E C V = -normalPhase E • (C + (1 + C) * (mmD g E C V + mmD g E C V ^ 2 +
      mmD g E C V ^ 3) + mmR g E C V) := by
  have e := inv_stepF_eq_sum_add g E hC hV 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at e
  have e' : (stepF g E C V)⁻¹ = 1 + mmD g E C V + mmD g E C V ^ 2 + mmD g E C V ^ 3 +
      mmD g E C V ^ 4 * (stepF g E C V)⁻¹ := e
  have key : (C + mmD g E C V) * (stepF g E C V)⁻¹ = (C + mmD g E C V) *
      (1 + mmD g E C V + mmD g E C V ^ 2 + mmD g E C V ^ 3 +
        mmD g E C V ^ 4 * (stepF g E C V)⁻¹) := by
    rw [← e']
  have hs : stepC g E C V = -normalPhase E • ((C + mmD g E C V) * (stepF g E C V)⁻¹) := rfl
  rw [hs, key]
  unfold mmR
  congr 1
  generalize mmD g E C V = D
  generalize (stepF g E C V)⁻¹ = Fi
  noncomm_ring

/-- The observable `m₁` along the update, as `−e^{−2iθ}` times the four orders of the expansion and
the remainder. -/
private lemma mm_obsM_eq {W : ℕ} (g E : ℝ) {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    obsM 1 (stepState g E X V) = -normalPhase E * (obsM 1 X + mmP g E X.1 V 1 +
      mmP g E X.1 V 2 + mmP g E X.1 V 3 + (W : ℂ)⁻¹ * (mmR g E X.1 V).trace) := by
  have h : (stepState g E X V).1 = stepC g E X.1 V := rfl
  unfold obsM mmP
  rw [h, zpow_one, zpow_one, mm_expand g E hX.1 hV]
  simp only [Matrix.trace_smul, Matrix.trace_add, Matrix.mul_add, smul_eq_mul, pow_one]
  ring

private lemma mm_norm_one_add {W : ℕ} (hW : 1 ≤ W) {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) : ‖C‖ = 1 ∧ ‖1 + C‖ ≤ 2 := by
  have : Nonempty (Fin W) := ⟨⟨0, hW⟩⟩
  have hnC : ‖C‖ = 1 := CStarRing.norm_of_mem_unitary hC
  refine ⟨hnC, ?_⟩
  calc ‖1 + C‖ ≤ ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ + ‖C‖ := norm_add_le _ _
    _ = 2 := by rw [norm_one, hnC]; norm_num

/-- `‖X‖ ≤ 2 t (1 + ‖V‖)` with `t = h_θ / g`. -/
private lemma mm_norm_D {W : ℕ} (hW : 1 ≤ W) {g E : ℝ} (hg : 0 < g)
    {C : Matrix (Fin W) (Fin W) ℂ} (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ)
    (V : Matrix (Fin W) (Fin W) ℂ) :
    ‖mmD g E C V‖ ≤ 2 * (normalH E / g) * (1 + ‖V‖) := by
  obtain ⟨hnC, hn2⟩ := mm_norm_one_add hW hC
  have ht0 : 0 ≤ normalH E / g := div_nonneg (mm_normalH_nonneg E) hg.le
  have hnc : ‖Complex.I * ((normalH E / g : ℝ) : ℂ)‖ = normalH E / g := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
  unfold mmD
  rw [norm_smul, hnc]
  calc normalH E / g * ‖V * (1 + C)‖ ≤ normalH E / g * (‖V‖ * 2) := by
        gcongr
        exact (norm_mul_le _ _).trans (by gcongr)
    _ ≤ 2 * (normalH E / g) * (1 + ‖V‖) := by nlinarith [norm_nonneg V]

/-- The remainder satisfies `‖R‖ ≤ K t⁴ (1 + ‖V‖)⁶` on all Hermitian blocks, where `t = h_θ / g` and
`h_θ ≤ H`. -/
private lemma mm_norm_R {W : ℕ} (hW : 1 ≤ W) {g E H : ℝ} (hg : 1 ≤ g) (hH : normalH E ≤ H)
    {C V : Matrix (Fin W) (Fin W) ℂ} (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ)
    (hV : V.IsHermitian) :
    ‖mmR g E C V‖ ≤ 16 * (1 + (1 + 2 * H) ^ 2) * (normalH E / g) ^ 4 * (1 + ‖V‖) ^ 6 := by
  have hg0 : 0 < g := by linarith
  obtain ⟨hnC, hn2⟩ := mm_norm_one_add hW hC
  have hh0 := mm_normalH_nonneg E
  have ht0 : 0 ≤ normalH E / g := div_nonneg hh0 hg0.le
  have htH : normalH E / g ≤ H := (div_le_self hh0 hg).trans hH
  have hH0 : 0 ≤ H := hh0.trans hH
  have hD := mm_norm_D hW hg0 hC V (E := E)
  have hF := (norm_stepF_le hg0 E hC hV).2
  have hVn := norm_nonneg V
  set t := normalH E / g with ht
  set S : ℝ := 1 + ‖V‖ with hS
  have hS1 : 1 ≤ S := by rw [hS]; linarith
  have hS0 : 0 ≤ S := by linarith
  have hF' : ‖(stepF g E C V)⁻¹‖ ≤ (1 + 2 * H) * S := by
    have e : 2 * normalH E * ‖V‖ / g = 2 * t * ‖V‖ := by rw [ht]; ring
    rw [e] at hF
    nlinarith [mul_nonneg ht0 hVn, mul_nonneg (sub_nonneg.mpr htH) hVn]
  have hCD : ‖C + mmD g E C V‖ ≤ (1 + 2 * H) * S := by
    refine (norm_add_le _ _).trans ?_
    rw [hnC]
    nlinarith [mul_nonneg (sub_nonneg.mpr htH) hS0]
  have hD4 : ‖mmD g E C V ^ 4‖ ≤ 16 * t ^ 4 * S ^ 4 := by
    refine (norm_pow_le' _ (by norm_num : 0 < 4)).trans ?_
    calc ‖mmD g E C V‖ ^ 4 ≤ (2 * t * S) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hD 4
      _ = 16 * t ^ 4 * S ^ 4 := by ring
  have hq0 : 0 ≤ (1 + 2 * H) * S := by positivity
  have h2 : ‖(C + mmD g E C V) * mmD g E C V ^ 4 * (stepF g E C V)⁻¹‖ ≤
      ((1 + 2 * H) * S) * (16 * t ^ 4 * S ^ 4) * ((1 + 2 * H) * S) := by
    refine (norm_mul_le _ _).trans ?_
    refine mul_le_mul ((norm_mul_le _ _).trans ?_) hF' (norm_nonneg _) (by positivity)
    exact mul_le_mul hCD hD4 (norm_nonneg _) hq0
  have hS46 : S ^ 4 ≤ S ^ 6 := pow_le_pow_right₀ hS1 (by norm_num)
  unfold mmR
  refine (norm_add_le _ _).trans ?_
  have hA : 16 * t ^ 4 * S ^ 4 ≤ 16 * t ^ 4 * S ^ 6 := by
    have : 0 ≤ 16 * t ^ 4 := by positivity
    exact mul_le_mul_of_nonneg_left hS46 this
  have hB : ((1 + 2 * H) * S) * (16 * t ^ 4 * S ^ 4) * ((1 + 2 * H) * S) =
      16 * (1 + 2 * H) ^ 2 * t ^ 4 * S ^ 6 := by ring
  rw [hB] at h2
  have hfin : 16 * (1 + (1 + 2 * H) ^ 2) * t ^ 4 * S ^ 6 =
      16 * t ^ 4 * S ^ 6 + 16 * (1 + 2 * H) ^ 2 * t ^ 4 * S ^ 6 := by ring
  rw [hfin]
  linarith

/-! ### Integration over one block -/

private lemma mm_measurable_gb (W : ℕ) : Measurable fun ω : Ω W 1 => gueBlock W 1 ω 0 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma mm_pow_le {x : ℝ} (hx : 0 ≤ x) (r : ℕ) : (1 + x) ^ r ≤ 2 ^ r * (1 + x ^ r) := by
  have h := add_pow_le zero_le_one hx r
  rw [one_pow] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le r 1)

/-- `𝔼 (1 + ‖V‖)^r ≤ M` uniformly in `W`, from the moment bound (11.14) [uvg:eq:tail]. -/
private lemma mm_moment (r : ℕ) : ∃ M : ℝ, 0 < M ∧ ∀ W : ℕ,
    Integrable (fun ω : Ω W 1 => (1 + ‖gueBlock W 1 ω 0‖) ^ r) (μ W 1) ∧
      ∫ ω, (1 + ‖gueBlock W 1 ω 0‖) ^ r ∂(μ W 1) ≤ M := by
  obtain ⟨C, hC, h⟩ := lintegral_norm_gueBlock_pow_le r
  refine ⟨2 ^ r * (1 + C), by positivity, fun W => ?_⟩
  have hdom : Integrable (fun ω : Ω W 1 => 2 ^ r * (1 + ‖gueBlock W 1 ω 0‖ ^ r)) (μ W 1) :=
    ((integrable_const (1 : ℝ)).add (integrable_norm_gueBlock_pow W r)).const_mul _
  have hmeas : Measurable fun ω : Ω W 1 => (1 + ‖gueBlock W 1 ω 0‖) ^ r :=
    (measurable_const.add (measurable_norm.comp (mm_measurable_gb W))).pow_const r
  have hint : Integrable (fun ω : Ω W 1 => (1 + ‖gueBlock W 1 ω 0‖) ^ r) (μ W 1) :=
    hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact mm_pow_le (norm_nonneg _) r)
  refine ⟨hint, ?_⟩
  have hn : ∫ ω, ‖gueBlock W 1 ω 0‖ ^ r ∂(μ W 1) ≤ C := by
    have h1 := ofReal_integral_eq_lintegral_ofReal (integrable_norm_gueBlock_pow W r)
      (Filter.Eventually.of_forall fun ω => by positivity)
    have h2 : ∫⁻ ω, ENNReal.ofReal (‖gueBlock W 1 ω 0‖ ^ r) ∂(μ W 1) =
        ∫⁻ ω, ‖gueBlock W 1 ω 0‖ₑ ^ r ∂(μ W 1) := by
      refine lintegral_congr fun ω => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [h2] at h1
    exact (ENNReal.ofReal_le_ofReal_iff hC.le).mp (h1.trans_le (h W))
  calc ∫ ω, (1 + ‖gueBlock W 1 ω 0‖) ^ r ∂(μ W 1)
      ≤ ∫ ω, 2 ^ r * (1 + ‖gueBlock W 1 ω 0‖ ^ r) ∂(μ W 1) :=
        integral_mono hint hdom fun ω => mm_pow_le (norm_nonneg _) r
    _ = 2 ^ r * (1 + ∫ ω, ‖gueBlock W 1 ω 0‖ ^ r ∂(μ W 1)) := by
        rw [integral_const_mul, integral_add (integrable_const _)
          (integrable_norm_gueBlock_pow W r)]
        simp
    _ ≤ 2 ^ r * (1 + C) := by gcongr

private lemma mm_continuous_P (g E : ℝ) {W : ℕ} (C : Matrix (Fin W) (Fin W) ℂ) (k : ℕ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => mmP g E C V k := by
  have h1 : Continuous fun V : Matrix (Fin W) (Fin W) ℂ =>
      (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C)) :=
    by fun_prop
  unfold mmP mmD
  exact continuous_const.mul (Continuous.matrix_trace (continuous_const.mul (h1.pow k)))

/-- `ω ↦ W⁻¹ Tr[(I + C) X^k]` along a GUE block is integrable. -/
private lemma mm_integrable_P {W : ℕ} (hW : 1 ≤ W) {g E : ℝ} (hg : 0 < g)
    {C : Matrix (Fin W) (Fin W) ℂ} (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (k : ℕ) :
    Integrable (fun ω : Ω W 1 => mmP g E C (gueBlock W 1 ω 0) k) (μ W 1) := by
  obtain ⟨M, -, hM⟩ := mm_moment k
  obtain ⟨hnC, hn2⟩ := mm_norm_one_add hW hC
  have : Nonempty (Fin W) := ⟨⟨0, hW⟩⟩
  have hmeas : Measurable fun ω : Ω W 1 => mmP g E C (gueBlock W 1 ω 0) k :=
    (mm_continuous_P g E C k).measurable.comp (mm_measurable_gb W)
  refine ((hM W).1.const_mul (2 * (2 * (normalH E / g)) ^ k)).mono'
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have ht0 : 0 ≤ normalH E / g := div_nonneg (mm_normalH_nonneg E) hg.le
  have hD := mm_norm_D hW hg hC (gueBlock W 1 ω 0) (E := E)
  have hn : ‖mmP g E C (gueBlock W 1 ω 0) k‖ ≤ 2 * (2 * (normalH E / g) *
      (1 + ‖gueBlock W 1 ω 0‖)) ^ k := by
    unfold mmP
    refine (mm_norm_trace_le hW _).trans ((norm_mul_le _ _).trans ?_)
    refine mul_le_mul hn2 ((norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hD k))
      (norm_nonneg _) (by norm_num)
  refine hn.trans (le_of_eq ?_)
  rw [mul_pow, mul_pow]
  ring

private lemma mm_mmD_neg (g E : ℝ) {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) :
    mmD g E C (-V) = -mmD g E C V := by
  unfold mmD
  simp only [Matrix.neg_mul, smul_neg]

/-- The orders `1` and `3` of the expansion are odd in `V`. -/
private lemma mm_P_neg_odd (g E : ℝ) {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) {k : ℕ}
    (hk : Odd k) : mmP g E C (-V) k = -mmP g E C V k := by
  unfold mmP
  rw [mm_mmD_neg, hk.neg_pow, Matrix.mul_neg, Matrix.trace_neg, mul_neg]

/-- One-block mean of the contraction: `𝔼 Tr[(V B V) Y] = W⁻¹ Tr(B) Tr(Y)` (the covariance (1.2)
[eq:covariance]). -/
private lemma mm_integral_trace (W : ℕ) (B Y : Matrix (Fin W) (Fin W) ℂ) :
    ∫ ω, ((gueBlock W 1 ω 0 * B * gueBlock W 1 ω 0) * Y).trace ∂(μ W 1) =
      (W : ℂ)⁻¹ * B.trace * Y.trace := by
  have hexp : ∀ ω : Ω W 1, ((gueBlock W 1 ω 0 * B * gueBlock W 1 ω 0) * Y).trace =
      ∑ α, ∑ β, (gueBlock W 1 ω 0 * B * gueBlock W 1 ω 0) α β * Y β α := by
    intro ω
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have hint : ∀ α β : Fin W, Integrable (fun ω : Ω W 1 =>
      (gueBlock W 1 ω 0 * B * gueBlock W 1 ω 0) α β * Y β α) (μ W 1) := by
    intro α β
    have hmeas : Measurable fun ω : Ω W 1 =>
        (gueBlock W 1 ω 0 * B * gueBlock W 1 ω 0) α β * Y β α := by
      have hc : Continuous fun V : Matrix (Fin W) (Fin W) ℂ => (V * B * V) α β * Y β α :=
        (((continuous_id.mul continuous_const).mul continuous_id).matrix_elem α β).mul
          continuous_const
      exact hc.measurable.comp (mm_measurable_gb W)
    refine ((integrable_norm_gueBlock_pow W 2).const_mul (‖B‖ * ‖Y β α‖)).mono'
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [norm_mul]
    have h1 : ‖(gueBlock W 1 ω 0 * B * gueBlock W 1 ω 0) α β‖ ≤
        ‖gueBlock W 1 ω 0‖ * ‖B‖ * ‖gueBlock W 1 ω 0‖ :=
      (mm_norm_entry_le _ α β).trans ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
    calc ‖(gueBlock W 1 ω 0 * B * gueBlock W 1 ω 0) α β‖ * ‖Y β α‖
        ≤ (‖gueBlock W 1 ω 0‖ * ‖B‖ * ‖gueBlock W 1 ω 0‖) * ‖Y β α‖ := by gcongr
      _ = ‖B‖ * ‖Y β α‖ * ‖gueBlock W 1 ω 0‖ ^ 2 := by ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint α β]
  have h1 : ∀ α : Fin W, ∫ ω, ∑ β, (gueBlock W 1 ω 0 * B * gueBlock W 1 ω 0) α β * Y β α
      ∂(μ W 1) = (W : ℂ)⁻¹ * B.trace * Y α α := by
    intro α
    rw [integral_finsetSum _ fun β _ => hint α β]
    simp_rw [integral_mul_const, integral_gueBlock_mul_mul_apply]
    simp [Finset.sum_ite_eq, mul_comm]
  simp_rw [h1]
  simp [Matrix.trace, Matrix.diag, Finset.mul_sum]

/-- `𝔼 mmP g E C V 2 = (i t)² W⁻¹ Tr(I + C) · W⁻¹ Tr (I + C)²`, the second-order Wick contraction of
(11.20) [uvg:eq:mmean]. -/
private lemma mm_integral_P2 {W : ℕ} (g E : ℝ) (C : Matrix (Fin W) (Fin W) ℂ) :
    ∫ ω, mmP g E C (gueBlock W 1 ω 0) 2 ∂(μ W 1) =
      (Complex.I * ((normalH E / g : ℝ) : ℂ)) ^ 2 * ((W : ℂ)⁻¹ * (1 + C).trace) *
        ((W : ℂ)⁻¹ * ((1 + C) * (1 + C)).trace) := by
  have hpt : ∀ V : Matrix (Fin W) (Fin W) ℂ, mmP g E C V 2 =
      ((Complex.I * ((normalH E / g : ℝ) : ℂ)) ^ 2 * (W : ℂ)⁻¹) *
        ((V * (1 + C) * V) * ((1 + C) * (1 + C))).trace := by
    intro V
    unfold mmP mmD
    rw [smul_pow, pow_two (V * (1 + C)), Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, mm_integral_trace]
  ring

/-- `W⁻¹ Tr(I + C) = 1 + m₁` and `W⁻¹ Tr (I + C)² = 1 + 2 m₁ + m₂`. -/
private lemma mm_trace_one_add {W : ℕ} (hW : 1 ≤ W) (C : Matrix (Fin W) (Fin W) ℂ) :
    (W : ℂ)⁻¹ * (1 + C).trace = 1 + (W : ℂ)⁻¹ * C.trace ∧
      (W : ℂ)⁻¹ * ((1 + C) * (1 + C)).trace =
        1 + 2 * ((W : ℂ)⁻¹ * C.trace) + (W : ℂ)⁻¹ * (C * C).trace := by
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hW)
  have e : (1 + C) * (1 + C) = 1 + (C + C) + C * C := by noncomm_ring
  constructor
  · rw [Matrix.trace_add, Matrix.trace_one]
    simp only [Fintype.card_fin]
    field_simp
  · rw [e, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_one]
    simp only [Fintype.card_fin]
    field_simp
    ring

private lemma mm_measurable_obsM_one (W : ℕ) : Measurable fun X : State W => obsM 1 X := by
  unfold obsM
  simp only [zpow_one]
  exact measurable_const.mul ((continuous_id.matrix_trace).measurable.comp measurable_fst)

/-- (11.20) [uvg:eq:mmean]:
`P_g m_1 = -e^{-2iθ} m_1 + e^{-2iθ} h² g⁻² (1 + m_1)(1 + 2 m_1 + m_2) + O(g⁻⁴)`. -/
theorem transOp_obsM_one {E₀ : ℝ} (hE₀ : E₀ < 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X →
        ‖transOp g E (obsM 1) X - (-normalPhase E * obsM 1 X + normalPhase E *
            ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (1 + obsM 1 X) * (1 + 2 * obsM 1 X + obsM 2 X))‖ ≤
          K / g ^ 4 := by
  obtain ⟨M, hM0, hM⟩ := mm_moment 6
  set H : ℝ := (2 * √(1 - E₀ ^ 2 / 4))⁻¹ with hH
  have hH0 : 0 ≤ H := by positivity
  set KR : ℝ := 16 * (1 + (1 + 2 * H) ^ 2) with hKR
  have hKR0 : 0 ≤ KR := by positivity
  refine ⟨KR * M * H ^ 4 + 1, by positivity, ?_⟩
  intro W hW g hg E hE X hX
  have hg0 : 0 < g := by linarith
  have hh0 := mm_normalH_nonneg E
  have hhH : normalH E ≤ H := mm_normalH_le hE₀ hE
  have hφ1 : ‖-normalPhase E‖ = 1 := by rw [norm_neg, mm_norm_normalPhase]
  have hφ : -normalPhase E ≠ 0 := by
    intro h
    rw [h, norm_zero] at hφ1
    exact zero_ne_one hφ1
  have hgb := mm_measurable_gb W
  -- the integrand and its bound
  have hFm : Measurable fun ω : Ω W 1 => obsM 1 (stepState g E X (gueBlock W 1 ω 0)) := by
    have hS : Measurable fun ω : Ω W 1 => (X, gueBlock W 1 ω 0) :=
      Measurable.prodMk measurable_const hgb
    have h1 := (measurable_stepState g E W).comp hS
    have h2 := (mm_measurable_obsM_one W).comp h1
    exact h2
  have hFb : ∀ ω : Ω W 1, ‖obsM 1 (stepState g E X (gueBlock W 1 ω 0))‖ ≤ 1 := fun ω =>
    norm_obsM_le_one 1 (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0))
  have hFi : Integrable (fun ω : Ω W 1 => obsM 1 (stepState g E X (gueBlock W 1 ω 0))) (μ W 1) :=
    Integrable.of_bound hFm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hFb)
  have hpt := fun ω : Ω W 1 => mm_obsM_eq g E hX (gueBlock_isHermitian W 1 ω 0)
  have i1 := mm_integrable_P hW hg0 (E := E) hX.1 1
  have i2 := mm_integrable_P hW hg0 (E := E) hX.1 2
  have i3 := mm_integrable_P hW hg0 (E := E) hX.1 3
  have iA1 : Integrable (fun ω : Ω W 1 =>
      obsM 1 X + mmP g E X.1 (gueBlock W 1 ω 0) 1) (μ W 1) :=
    (integrable_const (obsM 1 X)).add i1
  have iA2 : Integrable (fun ω : Ω W 1 =>
      obsM 1 X + mmP g E X.1 (gueBlock W 1 ω 0) 1 + mmP g E X.1 (gueBlock W 1 ω 0) 2)
      (μ W 1) := iA1.add i2
  have iA3 : Integrable (fun ω : Ω W 1 =>
      obsM 1 X + mmP g E X.1 (gueBlock W 1 ω 0) 1 + mmP g E X.1 (gueBlock W 1 ω 0) 2 +
        mmP g E X.1 (gueBlock W 1 ω 0) 3) (μ W 1) := iA2.add i3
  -- the remainder is integrable and small
  have hρe : ∀ ω : Ω W 1, (W : ℂ)⁻¹ * (mmR g E X.1 (gueBlock W 1 ω 0)).trace =
      (-normalPhase E)⁻¹ * obsM 1 (stepState g E X (gueBlock W 1 ω 0)) -
        (obsM 1 X + mmP g E X.1 (gueBlock W 1 ω 0) 1 + mmP g E X.1 (gueBlock W 1 ω 0) 2 +
          mmP g E X.1 (gueBlock W 1 ω 0) 3) := by
    intro ω
    rw [hpt ω, inv_mul_cancel_left₀ hφ]
    ring
  have iρ : Integrable (fun ω : Ω W 1 => (W : ℂ)⁻¹ * (mmR g E X.1 (gueBlock W 1 ω 0)).trace)
      (μ W 1) := by
    have h : Integrable (fun ω : Ω W 1 =>
        (-normalPhase E)⁻¹ * obsM 1 (stepState g E X (gueBlock W 1 ω 0)) -
          (obsM 1 X + mmP g E X.1 (gueBlock W 1 ω 0) 1 + mmP g E X.1 (gueBlock W 1 ω 0) 2 +
            mmP g E X.1 (gueBlock W 1 ω 0) 3)) (μ W 1) :=
      (hFi.const_mul _).sub iA3
    exact h.congr (Filter.Eventually.of_forall fun ω => (hρe ω).symm)
  have hρb : ‖∫ ω, (W : ℂ)⁻¹ * (mmR g E X.1 (gueBlock W 1 ω 0)).trace ∂(μ W 1)‖ ≤
      KR * (normalH E / g) ^ 4 * M := by
    have h := norm_integral_le_of_norm_le ((hM W).1.const_mul (KR * (normalH E / g) ^ 4))
      (μ := μ W 1) (f := fun ω : Ω W 1 => (W : ℂ)⁻¹ * (mmR g E X.1 (gueBlock W 1 ω 0)).trace)
      (Filter.Eventually.of_forall fun ω =>
        (mm_norm_trace_le hW _).trans (mm_norm_R hW hg hhH hX.1 (gueBlock_isHermitian W 1 ω 0)))
    refine h.trans ?_
    rw [integral_const_mul]
    have := (hM W).2
    have h0 : 0 ≤ KR * (normalH E / g) ^ 4 := by
      have : 0 ≤ normalH E / g := div_nonneg hh0 hg0.le
      positivity
    exact mul_le_mul_of_nonneg_left this h0
  -- the means of the four orders
  have hI1 : ∫ ω, mmP g E X.1 (gueBlock W 1 ω 0) 1 ∂(μ W 1) = 0 :=
    integral_odd_gueBlock (G := ℂ) W (fun V => mmP g E X.1 V 1)
      (fun V => mm_P_neg_odd g E X.1 V (by decide))
  have hI3 : ∫ ω, mmP g E X.1 (gueBlock W 1 ω 0) 3 ∂(μ W 1) = 0 :=
    integral_odd_gueBlock (G := ℂ) W (fun V => mmP g E X.1 V 3)
      (fun V => mm_P_neg_odd g E X.1 V (by decide))
  have hI2 := mm_integral_P2 g E X.1
  obtain ⟨ht1, ht2⟩ := mm_trace_one_add hW X.1
  have hm1 : obsM 1 X = (W : ℂ)⁻¹ * X.1.trace := by unfold obsM; rw [zpow_one]
  have hm2 : obsM 2 X = (W : ℂ)⁻¹ * (X.1 * X.1).trace := by unfold obsM; rw [zpow_two]
  rw [ht1, ht2, ← hm1, ← hm2] at hI2
  have hmain : transOp g E (obsM 1) X = -normalPhase E * (obsM 1 X + 0 +
      (Complex.I * ((normalH E / g : ℝ) : ℂ)) ^ 2 * (1 + obsM 1 X) *
        (1 + 2 * obsM 1 X + obsM 2 X) + 0 +
      ∫ ω, (W : ℂ)⁻¹ * (mmR g E X.1 (gueBlock W 1 ω 0)).trace ∂(μ W 1)) := by
    unfold transOp
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
    rw [integral_add iA3 iρ, integral_add iA2 i3, integral_add iA1 i2,
      integral_add (integrable_const (obsM 1 X)) i1, integral_const, hI1, hI3, hI2]
    simp
  have hc2 : (Complex.I * ((normalH E / g : ℝ) : ℂ)) ^ 2 =
      -((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, div_pow]
    push_cast
    ring
  rw [hmain, hc2]
  have e : -normalPhase E * (obsM 1 X + 0 + -((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (1 + obsM 1 X) *
        (1 + 2 * obsM 1 X + obsM 2 X) + 0 +
      ∫ ω, (W : ℂ)⁻¹ * (mmR g E X.1 (gueBlock W 1 ω 0)).trace ∂(μ W 1)) -
      (-normalPhase E * obsM 1 X + normalPhase E * ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) *
        (1 + obsM 1 X) * (1 + 2 * obsM 1 X + obsM 2 X)) =
      -normalPhase E * ∫ ω, (W : ℂ)⁻¹ * (mmR g E X.1 (gueBlock W 1 ω 0)).trace ∂(μ W 1) := by
    ring
  rw [e, norm_mul, hφ1, one_mul]
  refine hρb.trans ?_
  have hg4 : 0 < g ^ 4 := by positivity
  have h4 : (normalH E / g) ^ 4 ≤ H ^ 4 / g ^ 4 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hh0 hhH 4) hg4.le
  calc KR * (normalH E / g) ^ 4 * M ≤ KR * (H ^ 4 / g ^ 4) * M := by gcongr
    _ = KR * M * H ^ 4 / g ^ 4 := by ring
    _ ≤ (KR * M * H ^ 4 + 1) / g ^ 4 := by
        refine div_le_div_of_nonneg_right ?_ hg4.le
        linarith

end LSBA
