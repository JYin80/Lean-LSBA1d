import LSBA.Upper.LargeGradient

/-!
# The drift inequalities

Lemma 11.2 [uvg:lem:drifts]: (11.18) [uvg:eq:Mdrift] and (11.19) [uvg:eq:Fdrift] for every `g ≥ 1`
and `W ≥ 1`, uniformly in the state and in `|E| ≤ E₀`, with shared constants `a, C`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### The variance decomposition and the Young step -/

/-- `𝔼|f|² = |𝔼 f|² + 𝔼|f - 𝔼 f|²` for a bounded measurable `f`. -/
private lemma ld_var_identity {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'}
    [IsProbabilityMeasure ν] {f : Ω' → ℂ} (hf : Integrable f ν)
    (hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) ν) :
    ∫ ω, ‖f ω‖ ^ 2 ∂ν = ‖∫ ω, f ω ∂ν‖ ^ 2 + ∫ ω, ‖f ω - ∫ ω', f ω' ∂ν‖ ^ 2 ∂ν := by
  set m : ℂ := ∫ ω', f ω' ∂ν with hm
  have h1 : ∀ ω, ‖f ω - m‖ ^ 2 = ‖f ω‖ ^ 2 + ‖m‖ ^ 2 - 2 * (f ω * (starRingEnd ℂ) m).re := by
    intro ω
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
  have h2 : Integrable (fun ω => (f ω * (starRingEnd ℂ) m).re) ν :=
    (hf.mul_const _).re
  have h3 : ∫ ω, (f ω * (starRingEnd ℂ) m).re ∂ν = ‖m‖ ^ 2 := by
    have h4 : ∫ ω, (f ω * (starRingEnd ℂ) m).re ∂ν = (∫ ω, f ω * (starRingEnd ℂ) m ∂ν).re :=
      integral_re (hf.mul_const _)
    rw [h4, integral_mul_const, ← hm, Complex.mul_conj, Complex.sq_norm]
    simp
  have i1 : Integrable (fun ω => ‖f ω‖ ^ 2 + ‖m‖ ^ 2) ν := hf2.add (integrable_const _)
  have i2 : Integrable (fun ω => 2 * (f ω * (starRingEnd ℂ) m).re) ν := h2.const_mul 2
  simp_rw [h1]
  rw [integral_sub i1 i2, integral_add hf2 (integrable_const _), integral_const_mul, h3]
  simp
  ring

/-- Young's inequality with `ε = 1/(4 g²)`: for `|α|² ≤ 1 - 1/(2g²)`,
`|m|² ≤ (1 - 1/(4g²)) |Z|² + 5 g² |m - α Z|²`. -/
private lemma ld_young {g : ℝ} (hg : 1 ≤ g) {α Z m : ℂ} (hα : ‖α‖ ^ 2 ≤ 1 - 1 / (2 * g ^ 2)) :
    ‖m‖ ^ 2 ≤ (1 - 1 / (4 * g ^ 2)) * ‖Z‖ ^ 2 + 5 * g ^ 2 * ‖m - α * Z‖ ^ 2 := by
  have hs : 1 ≤ g ^ 2 := one_le_pow₀ hg
  have hs0 : 0 < g ^ 2 := by linarith
  set x : ℝ := ‖α * Z‖ with hx
  set y : ℝ := ‖m - α * Z‖ with hy
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy0 : 0 ≤ y := norm_nonneg _
  have h1 : ‖m‖ ≤ x + y := by
    calc ‖m‖ = ‖α * Z + (m - α * Z)‖ := by rw [add_sub_cancel]
      _ ≤ x + y := norm_add_le _ _
  have h2 : ‖m‖ ^ 2 ≤ (x + y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 2 * x * y ≤ x ^ 2 / (4 * g ^ 2) + 4 * g ^ 2 * y ^ 2 := by
    rw [← sub_nonneg]
    have : x ^ 2 / (4 * g ^ 2) + 4 * g ^ 2 * y ^ 2 - 2 * x * y = (x - 4 * g ^ 2 * y) ^ 2 /
        (4 * g ^ 2) := by field_simp; ring
    rw [this]; positivity
  have h4 : x ^ 2 = ‖α‖ ^ 2 * ‖Z‖ ^ 2 := by rw [hx, norm_mul, mul_pow]
  have h5 : ‖α‖ ^ 2 * ‖Z‖ ^ 2 ≤ (1 - 1 / (2 * g ^ 2)) * ‖Z‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hα (by positivity)
  have h6 : (1 + 1 / (4 * g ^ 2)) * (1 - 1 / (2 * g ^ 2)) ≤ 1 - 1 / (4 * g ^ 2) := by
    have : (1 + 1 / (4 * g ^ 2)) * (1 - 1 / (2 * g ^ 2)) = 1 - 1 / (4 * g ^ 2) -
        1 / (8 * g ^ 2 * g ^ 2) := by field_simp; ring
    rw [this]
    have : 0 ≤ 1 / (8 * g ^ 2 * g ^ 2) := by positivity
    linarith
  have h7 : (1 + 1 / (4 * g ^ 2)) * (1 - 1 / (2 * g ^ 2)) * ‖Z‖ ^ 2 ≤
      (1 - 1 / (4 * g ^ 2)) * ‖Z‖ ^ 2 := mul_le_mul_of_nonneg_right h6 (by positivity)
  have h8 : 1 + 4 * g ^ 2 ≤ 5 * g ^ 2 := by linarith
  have h9 : (1 + 1 / (4 * g ^ 2)) * (‖α‖ ^ 2 * ‖Z‖ ^ 2) ≤
      (1 + 1 / (4 * g ^ 2)) * ((1 - 1 / (2 * g ^ 2)) * ‖Z‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have h10 : (1 + 4 * g ^ 2) * y ^ 2 ≤ 5 * g ^ 2 * y ^ 2 :=
    mul_le_mul_of_nonneg_right h8 (by positivity)
  have h11 : x ^ 2 / (4 * g ^ 2) = 1 / (4 * g ^ 2) * x ^ 2 := by ring
  nlinarith

/-! ### Scalar facts and the bounds of `M` and `F` on states -/

private lemma ld_sin_pos {E : ℝ} (hE : |E| < 2) : 0 < Real.sin (freeAngle E) := by
  unfold freeAngle
  rw [Real.sin_arccos]
  apply Real.sqrt_pos.mpr
  have h : E ^ 2 < 4 := by
    have := sq_abs E
    nlinarith [abs_nonneg E]
  nlinarith

private lemma ld_normalH_pos {E : ℝ} (hE : |E| < 2) : 0 < normalH E := by
  unfold normalH
  have := ld_sin_pos hE
  positivity

/-- `h_θ ≤ (2 √(1 - E₀²/4))⁻¹` for `|E| ≤ E₀ < 2`. -/
private lemma ld_normalH_le {E₀ E : ℝ} (hE₀ : E₀ < 2) (hE : |E| ≤ E₀) :
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

private lemma ld_norm_normalPhase (E : ℝ) : ‖normalPhase E‖ = 1 := by
  unfold normalPhase
  rw [norm_neg, show 2 * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `|1 + e^{-2iθ}| = 2 sin ϑ = h_θ⁻¹` for `|E| < 2`. -/
private lemma ld_norm_one_add {E : ℝ} (hE : |E| < 2) : ‖1 + normalPhase E‖ = (normalH E)⁻¹ := by
  have hs := ld_sin_pos hE
  have h1 : 1 + normalPhase E = -(Complex.exp (freeAngle E * Complex.I) *
      (2 * Complex.I * (Real.sin (freeAngle E) : ℂ))) := by
    unfold normalPhase
    rw [Complex.ofReal_sin, Complex.sin]
    set z : ℂ := Complex.exp ((freeAngle E : ℂ) * Complex.I) with hz
    set w : ℂ := Complex.exp (-(freeAngle E : ℂ) * Complex.I) with hw
    have h2 : Complex.exp (2 * ((freeAngle E : ℂ) * Complex.I)) = z * z := by
      rw [hz, ← Complex.exp_add]; ring_nf
    have h3 : w * z = 1 := by
      rw [hw, hz, ← Complex.exp_add]; simp
    rw [h2]
    linear_combination (-1 : ℂ) * h3 + (z * w - z ^ 2) * Complex.I_sq
  rw [h1, norm_neg, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  simp only [Complex.norm_I, Complex.norm_ofNat]
  unfold normalH
  rw [inv_inv, mul_one]

private lemma ld_norm_q {E g : ℝ} (hE : |E| < 2) :
    ‖((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ)‖ = normalH E ^ 2 / g ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  have := ld_normalH_pos hE
  positivity

private lemma ld_mul_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a‖ * ‖b‖ ≤ 1 :=
  (mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- The correction of `M` in (11.16) [uvg:eq:M] has norm at most `4 h_θ³ g⁻²`. -/
private lemma ld_norm_corrM_sub {W : ℕ} {E g : ℝ} (hE : |E| < 2) {Y : State W} (hY : IsState Y) :
    ‖corrM g E Y - obsM 1 Y‖ ≤ 4 * normalH E ^ 3 / g ^ 2 := by
  have hh := ld_normalH_pos hE
  unfold corrM
  rw [sub_sub_cancel_left, norm_neg, norm_mul, ld_norm_q hE, norm_div, ld_norm_one_add hE,
    div_inv_eq_mul]
  have hm1 := norm_obsM_le_one 1 hY
  have hm2 := norm_obsM_le_one 2 hY
  have hN : ‖normalPhase E + obsM 2 Y + 2 * obsM 1 Y ^ 2‖ ≤ 4 := by
    calc ‖normalPhase E + obsM 2 Y + 2 * obsM 1 Y ^ 2‖
        ≤ ‖normalPhase E‖ + ‖obsM 2 Y‖ + ‖2 * obsM 1 Y ^ 2‖ := norm_add₃_le
      _ ≤ 1 + 1 + 2 := by
        rw [ld_norm_normalPhase, norm_mul, norm_pow, Complex.norm_ofNat]
        have : ‖obsM 1 Y‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hm1
        linarith
      _ = 4 := by norm_num
  calc normalH E ^ 2 / g ^ 2 * (‖normalPhase E + obsM 2 Y + 2 * obsM 1 Y ^ 2‖ * normalH E)
      ≤ normalH E ^ 2 / g ^ 2 * (4 * normalH E) := by gcongr
    _ = 4 * normalH E ^ 3 / g ^ 2 := by ring

/-- The correction of `F` in (11.17) [uvg:eq:F] has norm at most `8 h_θ³ g⁻²`. -/
private lemma ld_norm_corrF_sub {W : ℕ} {E g : ℝ} (hE : |E| < 2) {Y : State W} (hY : IsState Y) :
    ‖corrF g E Y - obsF 1 Y‖ ≤ 8 * normalH E ^ 3 / g ^ 2 := by
  have hh := ld_normalH_pos hE
  unfold corrF
  rw [sub_sub_cancel_left, norm_neg, norm_mul, ld_norm_q hE, norm_div, ld_norm_one_add hE,
    div_inv_eq_mul]
  have hm1 := norm_obsM_le_one 1 hY
  have hf1 := norm_obsF_le_one 1 hY
  have hf2 := norm_obsF_le_one 2 hY
  have hf3 := norm_obsF_le_one (-1) hY
  have hN : ‖4 * obsM 1 Y * obsF 1 Y + 2 * obsF 2 Y - obsF 1 Y ^ 2 -
      normalPhase E * obsF 1 Y * obsF (-1) Y‖ ≤ 8 := by
    have e1 : ‖4 * obsM 1 Y * obsF 1 Y‖ ≤ 4 := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat]
      have := ld_mul_le_one hm1 hf1
      linarith
    have e2 : ‖2 * obsF 2 Y‖ ≤ 2 := by
      rw [norm_mul, Complex.norm_ofNat]; linarith
    have e3 : ‖obsF 1 Y ^ 2‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hf1
    have e4 : ‖normalPhase E * obsF 1 Y * obsF (-1) Y‖ ≤ 1 := by
      rw [norm_mul, norm_mul, ld_norm_normalPhase, one_mul]
      exact ld_mul_le_one hf1 hf3
    calc _ ≤ ‖4 * obsM 1 Y * obsF 1 Y + 2 * obsF 2 Y - obsF 1 Y ^ 2‖ +
          ‖normalPhase E * obsF 1 Y * obsF (-1) Y‖ := norm_sub_le _ _
      _ ≤ ‖4 * obsM 1 Y * obsF 1 Y + 2 * obsF 2 Y‖ + ‖obsF 1 Y ^ 2‖ +
          ‖normalPhase E * obsF 1 Y * obsF (-1) Y‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ (‖4 * obsM 1 Y * obsF 1 Y‖ + ‖2 * obsF 2 Y‖) + ‖obsF 1 Y ^ 2‖ +
          ‖normalPhase E * obsF 1 Y * obsF (-1) Y‖ := by gcongr; exact norm_add_le _ _
      _ ≤ 8 := by linarith
  calc normalH E ^ 2 / g ^ 2 * (‖4 * obsM 1 Y * obsF 1 Y + 2 * obsF 2 Y - obsF 1 Y ^ 2 -
      normalPhase E * obsF 1 Y * obsF (-1) Y‖ * normalH E)
      ≤ normalH E ^ 2 / g ^ 2 * (8 * normalH E) := by gcongr
    _ = 8 * normalH E ^ 3 / g ^ 2 := by ring

/-- `M` and `F` are bounded by `1 + 8 H³` on states, for `g ≥ 1` and `|E| ≤ E₀`, where
`H = (2 √(1 - E₀²/4))⁻¹` bounds `h_θ`. -/
private lemma ld_norm_le {E₀ : ℝ} (hE₀ : E₀ < 2) {W : ℕ} {g E : ℝ} (hg : 1 ≤ g) (hE : |E| ≤ E₀)
    {Y : State W} (hY : IsState Y) :
    ‖corrM g E Y‖ ≤ 1 + 8 * (2 * √(1 - E₀ ^ 2 / 4))⁻¹ ^ 3 ∧
      ‖corrF g E Y‖ ≤ 1 + 8 * (2 * √(1 - E₀ ^ 2 / 4))⁻¹ ^ 3 := by
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have hh := ld_normalH_pos hE'
  have hHe := ld_normalH_le hE₀ hE
  set H : ℝ := (2 * √(1 - E₀ ^ 2 / 4))⁻¹
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg
  have h3 : normalH E ^ 3 ≤ H ^ 3 := pow_le_pow_left₀ hh.le hHe 3
  have h3' : 0 ≤ normalH E ^ 3 := by positivity
  have hdiv : ∀ c : ℝ, 0 ≤ c → c * normalH E ^ 3 / g ^ 2 ≤ c * H ^ 3 := by
    intro c hc
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ c * normalH E ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 hc]
  have hM := ld_norm_corrM_sub (g := g) hE' hY
  have hF := ld_norm_corrF_sub (g := g) hE' hY
  have hm1 := norm_obsM_le_one 1 hY
  have hf1 := norm_obsF_le_one 1 hY
  have hH0 : 0 ≤ H ^ 3 := by
    have : 0 ≤ H := by positivity
    positivity
  constructor
  · calc ‖corrM g E Y‖ ≤ ‖corrM g E Y - obsM 1 Y‖ + ‖obsM 1 Y‖ := by
          have := norm_sub_norm_le (corrM g E Y) (obsM 1 Y)
          linarith
      _ ≤ 4 * H ^ 3 + 1 := add_le_add (hM.trans (hdiv 4 (by norm_num))) hm1
      _ ≤ _ := by linarith
  · calc ‖corrF g E Y‖ ≤ ‖corrF g E Y - obsF 1 Y‖ + ‖obsF 1 Y‖ := by
          have := norm_sub_norm_le (corrF g E Y) (obsF 1 Y)
          linarith
      _ ≤ 8 * H ^ 3 + 1 := add_le_add (hF.trans (hdiv 8 (by norm_num))) hf1
      _ ≤ _ := by linarith

private lemma ld_continuous_corrM (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) :
    Continuous (fun ω : Ω W 1 => corrM g E (stepState g E X (gueBlock W 1 ω 0))) := by
  unfold corrM
  have h1 := contDiff_obsM_stepState g E hX 1
  have h2 := contDiff_obsM_stepState g E hX 2
  have : ContDiff ℝ 1 (fun ω : Ω W 1 => obsM 1 (stepState g E X (gueBlock W 1 ω 0)) -
      ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * ((normalPhase E +
        obsM 2 (stepState g E X (gueBlock W 1 ω 0)) +
        2 * obsM 1 (stepState g E X (gueBlock W 1 ω 0)) ^ 2) / (1 + normalPhase E))) := by
    fun_prop
  exact this.continuous

private lemma ld_continuous_corrF (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) :
    Continuous (fun ω : Ω W 1 => corrF g E (stepState g E X (gueBlock W 1 ω 0))) := by
  unfold corrF
  have m1 := contDiff_obsM_stepState g E hX 1
  have f1 := contDiff_obsF_stepState g E hX 1
  have f2 := contDiff_obsF_stepState g E hX 2
  have fm := contDiff_obsF_stepState g E hX (-1)
  have : ContDiff ℝ 1 (fun ω : Ω W 1 => obsF 1 (stepState g E X (gueBlock W 1 ω 0)) -
      ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * ((4 * obsM 1 (stepState g E X (gueBlock W 1 ω 0)) *
        obsF 1 (stepState g E X (gueBlock W 1 ω 0)) +
        2 * obsF 2 (stepState g E X (gueBlock W 1 ω 0)) -
        obsF 1 (stepState g E X (gueBlock W 1 ω 0)) ^ 2 -
        normalPhase E * obsF 1 (stepState g E X (gueBlock W 1 ω 0)) *
          obsF (-1) (stepState g E X (gueBlock W 1 ω 0))) / (1 + normalPhase E))) := by
    fun_prop
  exact this.continuous

/-- `P_g |Z|² = |P_g Z|² + 𝔼|Z' - P_g Z|²` for `Z` continuous along the step and bounded on
states. -/
private lemma ld_transOp_normSq {W : ℕ} (g E : ℝ) {X : State W} (hX : IsState X)
    {Z : State W → ℂ} {B : ℝ}
    (hc : Continuous (fun ω : Ω W 1 => Z (stepState g E X (gueBlock W 1 ω 0))))
    (hB : ∀ Y : State W, IsState Y → ‖Z Y‖ ≤ B) :
    transOp g E (fun Y => ‖Z Y‖ ^ 2) X = ‖transOp g E Z X‖ ^ 2 +
      ∫ ω, ‖Z (stepState g E X (gueBlock W 1 ω 0)) - transOp g E Z X‖ ^ 2 ∂(μ W 1) := by
  have hb : ∀ ω : Ω W 1, ‖Z (stepState g E X (gueBlock W 1 ω 0))‖ ≤ B := fun ω =>
    hB _ (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0))
  have h1 : Integrable (fun ω : Ω W 1 => Z (stepState g E X (gueBlock W 1 ω 0))) (μ W 1) :=
    Integrable.of_bound hc.aestronglyMeasurable B (Filter.Eventually.of_forall hb)
  have h2 : Integrable (fun ω : Ω W 1 => ‖Z (stepState g E X (gueBlock W 1 ω 0))‖ ^ 2)
      (μ W 1) := by
    refine Integrable.of_bound (hc.norm.pow 2).aestronglyMeasurable (B ^ 2)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb ω) 2
  exact ld_var_identity h1 h2

/-- `P_g |Z|² ≤ B²` for `Z` bounded by `B` on states. -/
private lemma ld_transOp_normSq_le {W : ℕ} (g E : ℝ) {X : State W} (hX : IsState X)
    {Z : State W → ℂ} {B : ℝ} (hB : ∀ Y : State W, IsState Y → ‖Z Y‖ ≤ B) :
    transOp g E (fun Y => ‖Z Y‖ ^ 2) X ≤ B ^ 2 := by
  have h := integral_mono_of_nonneg (μ := μ W 1)
    (f := fun ω : Ω W 1 => ‖Z (stepState g E X (gueBlock W 1 ω 0))‖ ^ 2)
    (g := fun _ => B ^ 2) (Filter.Eventually.of_forall fun ω => by positivity)
    (integrable_const _) (Filter.Eventually.of_forall fun ω => ?_)
  · unfold transOp
    simpa using h
  · exact pow_le_pow_left₀ (norm_nonneg _)
      (hB _ (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0))) 2

/-! ### The three regimes: the scalar inequalities -/

/-- Large `g`, the `M` drift: from `P|M|² = |m|² + V`, Young's bound for `|m|²`, `|R| ≤ K₁ g⁻⁴`
and `V ≤ K₃ g⁻² W⁻²`. -/
private lemma ld_alg_M {g w K₁ K₃ C P m2 V Z2 R2 : ℝ} (hg : 1 ≤ g) (hw : 1 ≤ w)
    (hK₁ : 5 * K₁ ^ 2 ≤ C) (hK₃ : K₃ ≤ C) (hid : P = m2 + V)
    (hV : V ≤ K₃ / (g ^ 2 * w ^ 2))
    (hy : m2 ≤ (1 - 1 / 4 / g ^ 2) * Z2 + 5 * g ^ 2 * R2) (hR : R2 ≤ (K₁ / g ^ 4) ^ 2) :
    P - Z2 ≤ -(1 / 4 / g ^ 2) * Z2 + C / g ^ 2 * (1 / w ^ 2 + 1 / g ^ 4) := by
  have hg0 : 0 < g := by linarith
  have hw0 : 0 < w := by linarith
  have t1 : 5 * g ^ 2 * R2 ≤ 5 * g ^ 2 * (K₁ / g ^ 4) ^ 2 :=
    mul_le_mul_of_nonneg_left hR (by positivity)
  have t2 : 5 * g ^ 2 * (K₁ / g ^ 4) ^ 2 = 5 * K₁ ^ 2 / g ^ 2 * (1 / g ^ 4) := by
    field_simp
  have t3 : K₃ / (g ^ 2 * w ^ 2) = K₃ / g ^ 2 * (1 / w ^ 2) := by field_simp
  have t4 : 5 * K₁ ^ 2 / g ^ 2 * (1 / g ^ 4) ≤ C / g ^ 2 * (1 / g ^ 4) := by gcongr
  have t5 : K₃ / g ^ 2 * (1 / w ^ 2) ≤ C / g ^ 2 * (1 / w ^ 2) := by gcongr
  rw [mul_add]
  rw [t3] at hV
  rw [t2] at t1
  linarith

/-- Large `g`, the `F` drift: as `ld_alg_M`, with `|R| ≤ K₂ g⁻² (x + g⁻² + w⁻¹)`,
`x = |M|`, and `V ≤ K₃ g⁻² w⁻¹`. -/
private lemma ld_alg_F {g w K₂ K₃ C P m2 V Z2 R2 x : ℝ} (hg : 1 ≤ g) (hw : 1 ≤ w)
    (hK₂ : 15 * K₂ ^ 2 + K₃ ≤ C) (hK₃ : 0 ≤ K₃) (hid : P = m2 + V)
    (hV : V ≤ K₃ / (g ^ 2 * w))
    (hy : m2 ≤ (1 - 1 / 4 / g ^ 2) * Z2 + 5 * g ^ 2 * R2)
    (hR : R2 ≤ (K₂ / g ^ 2 * (x + 1 / g ^ 2 + 1 / w)) ^ 2) :
    P - Z2 ≤ -(1 / 4 / g ^ 2) * Z2 + C / g ^ 2 * x ^ 2 + C / g ^ 2 * (1 / w + 1 / g ^ 4) := by
  have hg0 : 0 < g := by linarith
  have hw0 : 0 < w := by linarith
  have hz0 : 0 ≤ 1 / w := by positivity
  have hz1 : 1 / w ≤ 1 := by rw [div_le_one hw0]; exact hw
  have hK₂0 : 0 ≤ 15 * K₂ ^ 2 := by positivity
  have u1 : (x + 1 / g ^ 2 + 1 / w) ^ 2 ≤ 3 * (x ^ 2 + (1 / g ^ 2) ^ 2 + 1 / w) := by
    have : (1 / w) ^ 2 ≤ 1 / w := by nlinarith
    nlinarith [sq_nonneg (x - 1 / g ^ 2), sq_nonneg (x - 1 / w), sq_nonneg (1 / g ^ 2 - 1 / w)]
  have u2 : 5 * g ^ 2 * R2 ≤
      5 * g ^ 2 * ((K₂ / g ^ 2) ^ 2 * (3 * (x ^ 2 + (1 / g ^ 2) ^ 2 + 1 / w))) := by
    refine mul_le_mul_of_nonneg_left (hR.trans ?_) (by positivity)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left u1 (by positivity)
  have u3 : 5 * g ^ 2 * ((K₂ / g ^ 2) ^ 2 * (3 * (x ^ 2 + (1 / g ^ 2) ^ 2 + 1 / w))) =
      15 * K₂ ^ 2 / g ^ 2 * x ^ 2 + 15 * K₂ ^ 2 / g ^ 2 * (1 / g ^ 4) +
        15 * K₂ ^ 2 / g ^ 2 * (1 / w) := by
    field_simp
    ring
  have u4 : K₃ / (g ^ 2 * w) = K₃ / g ^ 2 * (1 / w) := by field_simp
  have u5 : 15 * K₂ ^ 2 / g ^ 2 * x ^ 2 ≤ C / g ^ 2 * x ^ 2 := by
    gcongr; linarith
  have u6 : 15 * K₂ ^ 2 / g ^ 2 * (1 / g ^ 4) ≤ C / g ^ 2 * (1 / g ^ 4) := by
    gcongr; linarith
  have u7 : 15 * K₂ ^ 2 / g ^ 2 * (1 / w) + K₃ / g ^ 2 * (1 / w) ≤ C / g ^ 2 * (1 / w) := by
    rw [← add_mul, ← add_div]
    gcongr
  rw [mul_add]
  rw [u4] at hV
  rw [u3] at u2
  linarith

/-- Small `g`: `P ≤ B²` and the term `C g⁻²·g⁻⁴ ≥ C/(512 H⁶)` dominate everything. -/
private lemma ld_alg_small {g C B H P Z2 T : ℝ} (hg : 1 ≤ g) (hH : g ^ 2 * g ^ 4 ≤ 512 * H ^ 6)
    (hC : 1024 * H ^ 6 * B ^ 2 ≤ C) (hP : P ≤ B ^ 2) (hZ : Z2 ≤ B ^ 2) (hZ0 : 0 ≤ Z2)
    (hT : 0 ≤ T) :
    P - Z2 ≤ -(1 / 4 / g ^ 2) * Z2 + (T + C / g ^ 2 * (1 / g ^ 4)) := by
  have hg0 : 0 < g := by linarith
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg
  have hlow : 2 * B ^ 2 ≤ C / g ^ 2 * (1 / g ^ 4) := by
    have e : C / g ^ 2 * (1 / g ^ 4) = C / (g ^ 2 * g ^ 4) := by field_simp
    rw [e, le_div_iff₀ (by positivity)]
    calc 2 * B ^ 2 * (g ^ 2 * g ^ 4) ≤ 2 * B ^ 2 * (512 * H ^ 6) := by gcongr
      _ = 1024 * H ^ 6 * B ^ 2 := by ring
      _ ≤ C := hC
  have ha : (1 : ℝ) / 4 / g ^ 2 ≤ 1 / 4 := div_le_self (by norm_num) hg2
  have s1 : 1 / 4 / g ^ 2 * Z2 ≤ 1 / 4 * B ^ 2 := mul_le_mul ha hZ hZ0 (by norm_num)
  linarith

/-- Lemma 11.2 [uvg:lem:drifts], (11.18) [uvg:eq:Mdrift] and (11.19) [uvg:eq:Fdrift], for every
`g ≥ 1` and `W ≥ 1`, uniformly in the state and `|E| ≤ E₀`:
`(P_g - I)|M|² ≤ -a g⁻²|M|² + C g⁻²(W⁻² + g⁻⁴)` and
`(P_g - I)|F|² ≤ -a g⁻²|F|² + C g⁻²|M|² + C g⁻²(W⁻¹ + g⁻⁴)`. -/
theorem large_drifts {E₀ : ℝ} (hE₀ : E₀ < 2) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X →
        transOp g E (fun Y => ‖corrM g E Y‖ ^ 2) X - ‖corrM g E X‖ ^ 2 ≤
            -(a / g ^ 2) * ‖corrM g E X‖ ^ 2 + C / g ^ 2 * (1 / (W : ℝ) ^ 2 + 1 / g ^ 4) ∧
          transOp g E (fun Y => ‖corrF g E Y‖ ^ 2) X - ‖corrF g E X‖ ^ 2 ≤
            -(a / g ^ 2) * ‖corrF g E X‖ ^ 2 + C / g ^ 2 * ‖corrM g E X‖ ^ 2 +
              C / g ^ 2 * (1 / (W : ℝ) + 1 / g ^ 4) := by
  obtain ⟨K₁, hK₁, h₁⟩ := transOp_corrM hE₀
  obtain ⟨K₂, hK₂, h₂⟩ := transOp_corrF hE₀
  obtain ⟨K₃, hK₃, h₃⟩ := innovation_var hE₀
  set H : ℝ := (2 * √(1 - E₀ ^ 2 / 4))⁻¹ with hH
  have hH0 : 0 ≤ H := by positivity
  set B : ℝ := 1 + 8 * H ^ 3 with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨1 / 4, 5 * K₁ ^ 2 + 15 * K₂ ^ 2 + K₃ + 1024 * H ^ 6 * B ^ 2 + 1, by norm_num,
    by positivity, ?_⟩
  intro W hW g hg E hE X hX
  set C : ℝ := 5 * K₁ ^ 2 + 15 * K₂ ^ 2 + K₃ + 1024 * H ^ 6 * B ^ 2 + 1 with hC
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have hg0 : 0 < g := by linarith
  have hw : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hw0 : 0 < (W : ℝ) := by linarith
  have hHB : 0 ≤ H ^ 6 * B ^ 2 := by positivity
  have hCK₁ : 5 * K₁ ^ 2 ≤ C := by rw [hC]; nlinarith [sq_nonneg K₂]
  have hCK₂ : 15 * K₂ ^ 2 + K₃ ≤ C := by rw [hC]; nlinarith [sq_nonneg K₁]
  have hCK₃ : K₃ ≤ C := by rw [hC]; nlinarith [sq_nonneg K₁, sq_nonneg K₂]
  have hCK₄ : 1024 * H ^ 6 * B ^ 2 ≤ C := by rw [hC]; nlinarith [sq_nonneg K₁, sq_nonneg K₂]
  have hBM : ∀ Y : State W, IsState Y → ‖corrM g E Y‖ ≤ B := fun Y hY =>
    (ld_norm_le hE₀ hg hE hY).1
  have hBF : ∀ Y : State W, IsState Y → ‖corrF g E Y‖ ≤ B := fun Y hY =>
    (ld_norm_le hE₀ hg hE hY).2
  have idM := ld_transOp_normSq g E hX (ld_continuous_corrM g E hX) hBM
  have idF := ld_transOp_normSq g E hX (ld_continuous_corrF g E hX) hBF
  obtain ⟨hv1, hv2, -⟩ := h₃ W hW g hg E hE X hX
  by_cases hbig : √8 * normalH E ≤ g
  · -- large `g`: `|α|² ≤ 1 - 1/(2g²)`, Young's inequality and the innovation variances
    have hα := normSq_driftAlpha_le hW hE' hbig hX
    have e0 : (1 : ℝ) / (4 * g ^ 2) = 1 / 4 / g ^ 2 := by field_simp
    have y1 := ld_young hg (Z := corrM g E X) (m := transOp g E (corrM g E) X) hα
    have y2 := ld_young hg (Z := corrF g E X) (m := transOp g E (corrF g E) X) hα
    rw [e0] at y1 y2
    have hRM := pow_le_pow_left₀ (norm_nonneg _) (h₁ W hW g hg E hE X hX) 2
    have hRF := pow_le_pow_left₀ (norm_nonneg _) (h₂ W hW g hg E hE X hX) 2
    exact ⟨ld_alg_M hg hw hCK₁ hCK₃ idM hv1 y1 hRM,
      ld_alg_F hg hw hCK₂ hK₃.le idF hv2 y2 hRF⟩
  · -- small `g`: `g² < 8 h_θ² ≤ 8 H²`, so the constant term `C g⁻⁶` dominates
    have hhH : normalH E ≤ H := ld_normalH_le hE₀ hE
    have hh0 := ld_normalH_pos hE'
    have hlt : g < √8 * normalH E := not_le.mp hbig
    have hg2lt : g ^ 2 < 8 * H ^ 2 := by
      have h1 : g ^ 2 < (√8 * normalH E) ^ 2 := pow_lt_pow_left₀ hlt hg0.le two_ne_zero
      have h2 : (√8 * normalH E) ^ 2 = 8 * normalH E ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
      have h3 : normalH E ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ hh0.le hhH 2
      linarith
    have hg6 : g ^ 2 * g ^ 4 ≤ 512 * H ^ 6 := by
      have : (g ^ 2) ^ 3 ≤ (8 * H ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hg2lt.le 3
      calc g ^ 2 * g ^ 4 = (g ^ 2) ^ 3 := by ring
        _ ≤ (8 * H ^ 2) ^ 3 := this
        _ = 512 * H ^ 6 := by ring
    have hC0 : 0 ≤ C := by rw [hC]; positivity
    have hHC : 0 ≤ C / g ^ 2 := by positivity
    have s3 : 0 ≤ C / g ^ 2 * (1 / (W : ℝ) ^ 2) := by positivity
    have s4 : 0 ≤ C / g ^ 2 * (1 / (W : ℝ)) := by positivity
    have s5 : 0 ≤ C / g ^ 2 * ‖corrM g E X‖ ^ 2 := by positivity
    have mM := ld_alg_small hg hg6 hCK₄ (ld_transOp_normSq_le g E hX hBM)
      (pow_le_pow_left₀ (norm_nonneg _) (hBM X hX) 2) (sq_nonneg _) s3
    have mF := ld_alg_small hg hg6 hCK₄ (ld_transOp_normSq_le g E hX hBF)
      (pow_le_pow_left₀ (norm_nonneg _) (hBF X hX) 2) (sq_nonneg _) (add_nonneg s5 s4)
    refine ⟨?_, ?_⟩
    · rw [mul_add]; exact mM
    · rw [mul_add]; linarith

end LSBA
