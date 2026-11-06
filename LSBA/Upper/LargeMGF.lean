import LSBA.Upper.LargePositive

/-!
# The moment generating function of the corrected increment

Lemma 11.4 [uvg:lem:mgf]: with `𝒬` bounded as in Lemma 11.3 [uvg:lem:positive], there are `s, c > 0`
with `𝔼(e^{−sY} | X) ≤ exp(−c g⁻²/W)` uniformly in the state, for `W ≥ W₀` and `g ≥ C_*√W`; the
constants are restated existentially.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Elementary inequalities -/

/-- `e^y ≤ 1 + y + y²` for `y ≤ 1`. -/
private lemma lm_exp_le {y : ℝ} (hy : y ≤ 1) : Real.exp y ≤ 1 + y + y ^ 2 := by
  by_cases h : |y| ≤ 1
  · have := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le h)).2
    linarith
  · have hy' : y < -1 := by
      rcases lt_abs.mp (not_le.mp h) with h | h
      · linarith
      · linarith
    have h1 : Real.exp y * Real.exp 1 ≤ 1 := by
      rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [Real.exp_pos y, Real.add_one_le_exp 1, sq_nonneg (y + 1 / 2)]

/-- The tail term `e (1 + 2 h r) (2 h r / g)⁴` of the bound on `e^{-sY}` in Lemma 11.4
[uvg:lem:mgf], with `r` the norm of the fresh block. -/
private def lmT (H g r : ℝ) : ℝ := Real.exp 1 * (1 + 2 * H * r) * (2 * H * r / g) ^ 4

private lemma lmT_nonneg {H g r : ℝ} (hH : 0 ≤ H) (hr : 0 ≤ r) : 0 ≤ lmT H g r := by
  unfold lmT; positivity

/-- The pointwise bound `e^{-sY} ≤ 1 - sY + s²Y² + T` in the proof of Lemma 11.4 [uvg:lem:mgf]:
`|c| ≤ log(1 + 2 h r/g)` and `|Y - c| ≤ 2K`, with `s ≤ 1/2` and `sK ≤ 1/4`. -/
private lemma lm_pointwise {s K H g r Y c : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    (hsK : s * K ≤ 1 / 4) (hg : 1 ≤ g) (hH : 0 ≤ H) (hr : 0 ≤ r)
    (hc : |c| ≤ Real.log (1 + 2 * H * r / g)) (hYc : |Y - c| ≤ 2 * K) :
    Real.exp (-s * Y) ≤ 1 - s * Y + s ^ 2 * Y ^ 2 + lmT H g r := by
  have hg0 : 0 < g := by linarith
  have hz0 : 0 ≤ 2 * H * r / g := by positivity
  have hT0 : 0 ≤ lmT H g r := lmT_nonneg hH hr
  by_cases hY : -s * Y ≤ 1
  · have := lm_exp_le hY
    nlinarith
  · replace hY := not_le.mp hY
    have hLpos : 0 < 1 + 2 * H * r / g := by linarith
    have hlogL : 0 ≤ Real.log (1 + 2 * H * r / g) := Real.log_nonneg (by linarith)
    have h1 : -s * Y ≤ s * |c| + s * (2 * K) := by
      have e : -s * Y = s * (-c) + s * (-(Y - c)) := by ring
      rw [e]
      have a1 : -c ≤ |c| := neg_le_abs c
      have a2 : -(Y - c) ≤ |Y - c| := neg_le_abs _
      nlinarith [mul_le_mul_of_nonneg_left a1 hs.le, mul_le_mul_of_nonneg_left a2 hs.le,
        mul_le_mul_of_nonneg_left hYc hs.le]
    have h2 : s * |c| ≤ s * Real.log (1 + 2 * H * r / g) := mul_le_mul_of_nonneg_left hc hs.le
    have h3 : s * Real.log (1 + 2 * H * r / g) ≤ 1 / 2 * Real.log (1 + 2 * H * r / g) :=
      mul_le_mul_of_nonneg_right hs2 hlogL
    have h4 : s * Real.log (1 + 2 * H * r / g) ≤ Real.log (1 + 2 * H * r / g) := by
      have : (1 / 2 : ℝ) * Real.log (1 + 2 * H * r / g) ≤ Real.log (1 + 2 * H * r / g) := by
        linarith
      linarith
    have hlog1 : 1 < Real.log (1 + 2 * H * r / g) := by nlinarith
    have hL : Real.exp 1 < 1 + 2 * H * r / g := (Real.lt_log_iff_exp_lt hLpos).mp hlog1
    have hz1 : 1 ≤ 2 * H * r / g := by
      have := Real.exp_one_gt_d9
      linarith
    have hz4 : 1 ≤ (2 * H * r / g) ^ 4 := one_le_pow₀ hz1
    have hzr : 2 * H * r / g ≤ 2 * H * r := div_le_self (by positivity) hg
    have hexp : Real.exp (-s * Y) ≤ Real.exp 1 * (1 + 2 * H * r) := by
      calc Real.exp (-s * Y) ≤ Real.exp (Real.log (1 + 2 * H * r / g) + 1) := by
            apply Real.exp_le_exp.mpr; linarith
        _ = (1 + 2 * H * r / g) * Real.exp 1 := by rw [Real.exp_add, Real.exp_log hLpos]
        _ ≤ (1 + 2 * H * r) * Real.exp 1 := by gcongr
        _ = _ := by ring
    have hpos : 0 ≤ Real.exp 1 * (1 + 2 * H * r) := by positivity
    have : Real.exp 1 * (1 + 2 * H * r) ≤ lmT H g r :=
      le_mul_of_one_le_right hpos hz4
    nlinarith [sq_nonneg (s * Y - 1 / 2)]

/-- Integrating the pointwise bound `e^{-sY} ≤ 1 - sY + s²Y² + T`. -/
private lemma lm_lintegral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y T : Ω → ℝ} {s : ℝ} (hY : Integrable Y μ)
    (hY2 : Integrable (fun ω => Y ω ^ 2) μ) (hT : Integrable T μ)
    (hpt : ∀ ω, Real.exp (-s * Y ω) ≤ 1 - s * Y ω + s ^ 2 * Y ω ^ 2 + T ω)
    (hT0 : ∀ ω, 0 ≤ T ω) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * Y ω)) ∂μ ≤
      ENNReal.ofReal (1 - s * ∫ ω, Y ω ∂μ + s ^ 2 * ∫ ω, Y ω ^ 2 ∂μ + ∫ ω, T ω ∂μ) := by
  have iA : Integrable (fun ω => 1 - s * Y ω) μ := (integrable_const 1).sub (hY.const_mul s)
  have hI0 : Integrable (fun ω => 1 - s * Y ω + s ^ 2 * Y ω ^ 2) μ :=
    iA.add (hY2.const_mul (s ^ 2))
  have hI : Integrable (fun ω => 1 - s * Y ω + s ^ 2 * Y ω ^ 2 + T ω) μ := hI0.add hT
  have hnn : 0 ≤ᵐ[μ] (fun ω => 1 - s * Y ω + s ^ 2 * Y ω ^ 2 + T ω) :=
    Filter.Eventually.of_forall fun ω => by
      change (0 : ℝ) ≤ 1 - s * Y ω + s ^ 2 * Y ω ^ 2 + T ω
      nlinarith [sq_nonneg (s * Y ω - 1 / 2), hT0 ω]
  have hint : ∫ ω, (1 - s * Y ω + s ^ 2 * Y ω ^ 2 + T ω) ∂μ =
      1 - s * ∫ ω, Y ω ∂μ + s ^ 2 * ∫ ω, Y ω ^ 2 ∂μ + ∫ ω, T ω ∂μ := by
    rw [integral_add hI0 hT, integral_add iA (hY2.const_mul (s ^ 2)),
      integral_sub (integrable_const 1) (hY.const_mul s),
      integral_const_mul, integral_const_mul]
    simp
  rw [← hint, ofReal_integral_eq_lintegral_ofReal hI hnn]
  exact lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)

/-- `𝔼Y² ≤ (𝔼Y)² + 𝔼(Y - a)²` for every constant `a`. -/
private lemma lm_sq_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY : Integrable Y μ) (hY2 : Integrable (fun ω => Y ω ^ 2) μ) (a : ℝ) :
    ∫ ω, Y ω ^ 2 ∂μ ≤ (∫ ω, Y ω ∂μ) ^ 2 + ∫ ω, (Y ω - a) ^ 2 ∂μ := by
  have e : ∫ ω, (Y ω - a) ^ 2 ∂μ = ∫ ω, Y ω ^ 2 ∂μ - 2 * a * ∫ ω, Y ω ∂μ + a ^ 2 := by
    have h : (fun ω => (Y ω - a) ^ 2) = fun ω => Y ω ^ 2 - 2 * a * Y ω + a ^ 2 := by
      funext ω; ring
    have iB : Integrable (fun ω => Y ω ^ 2 - 2 * a * Y ω) μ := hY2.sub (hY.const_mul (2 * a))
    rw [h, integral_add iB (integrable_const _), integral_sub hY2 (hY.const_mul _),
      integral_const_mul]
    simp
  nlinarith [sq_nonneg (∫ ω, Y ω ∂μ - a)]

/-- The closing arithmetic of Lemma 11.4 [uvg:lem:mgf]: with `t = g⁻²`, `u = W⁻¹` and
`t C_*² ≤ u`. -/
private lemma lm_final {t u Cs s a₀ V₁ V₂ K₄ : ℝ} (ht : 0 < t) (hu : 0 < u)
    (htu : t * Cs ^ 2 ≤ u) (hCs : 1 ≤ Cs) (hs : 0 < s) (ha : 0 < a₀) (hV₁ : s * V₁ ≤ a₀ / 8)
    (hV₂ : 8 * s * V₂ / a₀ ≤ Cs) (hK₄ : 8 * K₄ / (s * a₀) ≤ Cs) :
    1 - s / 2 * (a₀ * (t * u)) + s ^ 2 * (V₁ * (t * u) + V₂ * t ^ 2) + K₄ * t ^ 2 ≤
      1 - s * a₀ / 8 * (t * u) := by
  have hCs2 : Cs ≤ Cs ^ 2 := by nlinarith
  have hsV₂ : s * V₂ ≤ a₀ * Cs / 8 := by
    rw [div_le_iff₀ ha] at hV₂; linarith
  have hK : K₄ ≤ s * a₀ * Cs / 8 := by
    rw [div_le_iff₀ (by positivity)] at hK₄; linarith
  have hT : t ^ 2 * Cs ≤ t * u := by
    have h1 : t ^ 2 * Cs ^ 2 ≤ t * u := by
      have := mul_le_mul_of_nonneg_left htu ht.le
      nlinarith
    have h2 : t ^ 2 * Cs ≤ t ^ 2 * Cs ^ 2 := mul_le_mul_of_nonneg_left hCs2 (by positivity)
    linarith
  have a1 : s ^ 2 * (V₁ * (t * u)) ≤ s * (a₀ / 8) * (t * u) := by
    have := mul_le_mul_of_nonneg_left hV₁ hs.le
    have h0 : 0 ≤ t * u := by positivity
    nlinarith [mul_le_mul_of_nonneg_right this h0]
  have a2 : s ^ 2 * (V₂ * t ^ 2) ≤ s * (a₀ / 8) * (t * u) := by
    have h1 := mul_le_mul_of_nonneg_left hsV₂ (by positivity : 0 ≤ s * t ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ s * a₀ / 8)
    nlinarith
  have a3 : K₄ * t ^ 2 ≤ s * (a₀ / 8) * (t * u) := by
    have h1 := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ t ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ s * a₀ / 8)
    nlinarith
  nlinarith

/-! ### Scalar facts -/

/-- `H = (2 √(1 - E₀²/4))⁻¹`, the bound `h_θ ≤ H` of (11.1) [lg:eq:normal] for `|E| ≤ E₀ < 2`. -/
private def lmH (E₀ : ℝ) : ℝ := (2 * √(1 - E₀ ^ 2 / 4))⁻¹

private lemma lmH_nonneg (E₀ : ℝ) : 0 ≤ lmH E₀ := by
  unfold lmH; positivity

private lemma lm_sin_pos {E : ℝ} (hE : |E| < 2) : 0 < Real.sin (freeAngle E) := by
  unfold freeAngle
  rw [Real.sin_arccos]
  apply Real.sqrt_pos.mpr
  have h : E ^ 2 < 4 := by
    have := sq_abs E
    nlinarith [abs_nonneg E]
  nlinarith

private lemma lm_normalH_pos {E : ℝ} (hE : |E| < 2) : 0 < normalH E := by
  unfold normalH
  have := lm_sin_pos hE
  positivity


private lemma lm_normalH_le {E₀ E : ℝ} (hE₀ : E₀ < 2) (hE : |E| ≤ E₀) :
    normalH E ≤ lmH E₀ := by
  unfold normalH freeAngle lmH
  rw [Real.sin_arccos]
  have ha := abs_nonneg E
  have h1 : E ^ 2 ≤ E₀ ^ 2 := by
    rw [← sq_abs E]
    exact pow_le_pow_left₀ ha hE 2
  have h2 : 0 < 1 - E₀ ^ 2 / 4 := by nlinarith
  have h3 : √(1 - E₀ ^ 2 / 4) ≤ √(1 - (E / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have h4 : 0 < √(1 - E₀ ^ 2 / 4) := Real.sqrt_pos.mpr h2
  exact inv_anti₀ (by positivity) (by linarith)

/-- `|e^{-2iθ}| = 1`. -/
private lemma lm_norm_normalPhase (E : ℝ) : ‖normalPhase E‖ = 1 := by
  unfold normalPhase
  rw [norm_neg, show 2 * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `|1 + e^{-2iθ}| = 2 sin ϑ = h_θ⁻¹` for `|E| < 2`. -/
private lemma lm_norm_one_add {E : ℝ} (hE : |E| < 2) : ‖1 + normalPhase E‖ = (normalH E)⁻¹ := by
  have hs := lm_sin_pos hE
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

/-- `|h²/(1 + e^{-2iθ})| = h_θ³` (the coefficient of `f_1` in the linear corrector before Lemma
11.3 [uvg:lem:positive]). -/
private lemma lm_norm_kappa {E : ℝ} (hE : |E| < 2) :
    ‖((normalH E ^ 2 : ℝ) : ℂ) / (1 + normalPhase E)‖ = normalH E ^ 3 := by
  have hh := lm_normalH_pos hE
  rw [norm_div, lm_norm_one_add hE, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), div_inv_eq_mul]
  ring

private lemma lm_mul_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a‖ * ‖b‖ ≤ 1 :=
  (mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

private lemma lm_norm_q {E g : ℝ} (hE : |E| < 2) :
    ‖((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ)‖ = normalH E ^ 2 / g ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  have := lm_normalH_pos hE
  positivity

/-- The correction of `M` in (11.16) [uvg:eq:M] has norm at most `4 h_θ³ g⁻²`. -/
private lemma lm_norm_corrM_sub {W : ℕ} {E g : ℝ} (hE : |E| < 2) {Y : State W} (hY : IsState Y) :
    ‖corrM g E Y - obsM 1 Y‖ ≤ 4 * normalH E ^ 3 / g ^ 2 := by
  have hh := lm_normalH_pos hE
  unfold corrM
  rw [sub_sub_cancel_left, norm_neg, norm_mul, lm_norm_q hE, norm_div, lm_norm_one_add hE,
    div_inv_eq_mul]
  have hm1 := norm_obsM_le_one 1 hY
  have hm2 := norm_obsM_le_one 2 hY
  have hN : ‖normalPhase E + obsM 2 Y + 2 * obsM 1 Y ^ 2‖ ≤ 4 := by
    calc ‖normalPhase E + obsM 2 Y + 2 * obsM 1 Y ^ 2‖
        ≤ ‖normalPhase E‖ + ‖obsM 2 Y‖ + ‖2 * obsM 1 Y ^ 2‖ := norm_add₃_le
      _ ≤ 1 + 1 + 2 := by
        rw [lm_norm_normalPhase, norm_mul, norm_pow, Complex.norm_ofNat]
        have : ‖obsM 1 Y‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hm1
        linarith
      _ = 4 := by norm_num
  calc normalH E ^ 2 / g ^ 2 * (‖normalPhase E + obsM 2 Y + 2 * obsM 1 Y ^ 2‖ * normalH E)
      ≤ normalH E ^ 2 / g ^ 2 * (4 * normalH E) := by gcongr
    _ = 4 * normalH E ^ 3 / g ^ 2 := by ring

/-- The correction of `F` in (11.17) [uvg:eq:F] has norm at most `8 h_θ³ g⁻²`. -/
private lemma lm_norm_corrF_sub {W : ℕ} {E g : ℝ} (hE : |E| < 2) {Y : State W} (hY : IsState Y) :
    ‖corrF g E Y - obsF 1 Y‖ ≤ 8 * normalH E ^ 3 / g ^ 2 := by
  have hh := lm_normalH_pos hE
  unfold corrF
  rw [sub_sub_cancel_left, norm_neg, norm_mul, lm_norm_q hE, norm_div, lm_norm_one_add hE,
    div_inv_eq_mul]
  have hm1 := norm_obsM_le_one 1 hY
  have hf1 := norm_obsF_le_one 1 hY
  have hf2 := norm_obsF_le_one 2 hY
  have hf3 := norm_obsF_le_one (-1) hY
  have hN : ‖4 * obsM 1 Y * obsF 1 Y + 2 * obsF 2 Y - obsF 1 Y ^ 2 -
      normalPhase E * obsF 1 Y * obsF (-1) Y‖ ≤ 8 := by
    have e1 : ‖4 * obsM 1 Y * obsF 1 Y‖ ≤ 4 := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat]
      have := lm_mul_le_one hm1 hf1
      linarith
    have e2 : ‖2 * obsF 2 Y‖ ≤ 2 := by
      rw [norm_mul, Complex.norm_ofNat]; linarith
    have e3 : ‖obsF 1 Y ^ 2‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hf1
    have e4 : ‖normalPhase E * obsF 1 Y * obsF (-1) Y‖ ≤ 1 := by
      rw [norm_mul, norm_mul, lm_norm_normalPhase, one_mul]
      exact lm_mul_le_one hf1 hf3
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

/-- `‖M - m₁‖ ≤ 4 H³ g⁻²` uniformly in `|E| ≤ E₀`. -/
private lemma lm_corrM_sub_le {E₀ : ℝ} (hE₀ : E₀ < 2) {W : ℕ} {g E : ℝ} (hE : |E| ≤ E₀)
    {Y : State W} (hY : IsState Y) :
    ‖corrM g E Y - obsM 1 Y‖ ≤ 4 * lmH E₀ ^ 3 * (1 / g ^ 2) := by
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have h3 : normalH E ^ 3 ≤ lmH E₀ ^ 3 :=
    pow_le_pow_left₀ (lm_normalH_pos hE').le (lm_normalH_le hE₀ hE) 3
  calc _ ≤ 4 * normalH E ^ 3 / g ^ 2 := lm_norm_corrM_sub hE' hY
    _ = 4 * normalH E ^ 3 * (1 / g ^ 2) := by ring
    _ ≤ _ := by gcongr

/-- `‖F - f₁‖ ≤ 8 H³ g⁻²` uniformly in `|E| ≤ E₀`. -/
private lemma lm_corrF_sub_le {E₀ : ℝ} (hE₀ : E₀ < 2) {W : ℕ} {g E : ℝ} (hE : |E| ≤ E₀)
    {Y : State W} (hY : IsState Y) :
    ‖corrF g E Y - obsF 1 Y‖ ≤ 8 * lmH E₀ ^ 3 * (1 / g ^ 2) := by
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have h3 : normalH E ^ 3 ≤ lmH E₀ ^ 3 :=
    pow_le_pow_left₀ (lm_normalH_pos hE').le (lm_normalH_le hE₀ hE) 3
  calc _ ≤ 8 * normalH E ^ 3 / g ^ 2 := lm_norm_corrF_sub hE' hY
    _ = 8 * normalH E ^ 3 * (1 / g ^ 2) := by ring
    _ ≤ _ := by gcongr

/-- `‖M‖ ≤ 1 + 4 H³` and `‖F‖ ≤ 1 + 8 H³` on states, for `g ≥ 1`. -/
private lemma lm_norm_corr_le {E₀ : ℝ} (hE₀ : E₀ < 2) {W : ℕ} {g E : ℝ} (hg : 1 ≤ g)
    (hE : |E| ≤ E₀) {Y : State W} (hY : IsState Y) :
    ‖corrM g E Y‖ ≤ 1 + 4 * lmH E₀ ^ 3 ∧ ‖corrF g E Y‖ ≤ 1 + 8 * lmH E₀ ^ 3 := by
  have hg2 : 1 / g ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ hg
  have hH0 : 0 ≤ lmH E₀ ^ 3 := pow_nonneg (lmH_nonneg E₀) 3
  have hm1 := norm_obsM_le_one 1 hY
  have hf1 := norm_obsF_le_one 1 hY
  have hM := lm_corrM_sub_le hE₀ (g := g) hE hY
  have hF := lm_corrF_sub_le hE₀ (g := g) hE hY
  constructor
  · calc ‖corrM g E Y‖ ≤ ‖corrM g E Y - obsM 1 Y‖ + ‖obsM 1 Y‖ := by
          have := norm_sub_norm_le (corrM g E Y) (obsM 1 Y)
          linarith
      _ ≤ 4 * lmH E₀ ^ 3 * 1 + 1 := by
          gcongr
          exact hM.trans (by gcongr)
      _ = _ := by ring
  · calc ‖corrF g E Y‖ ≤ ‖corrF g E Y - obsF 1 Y‖ + ‖obsF 1 Y‖ := by
          have := norm_sub_norm_le (corrF g E Y) (obsF 1 Y)
          linarith
      _ ≤ 8 * lmH E₀ ^ 3 * 1 + 1 := by
          gcongr
          exact hF.trans (by gcongr)
      _ = _ := by ring

/-! ### The corrector along one step -/

private lemma lm_contDiff_corrM (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) :
    ContDiff ℝ 1 (fun ω : Ω W 1 => corrM g E (stepState g E X (gueBlock W 1 ω 0))) := by
  unfold corrM
  have h1 := contDiff_obsM_stepState g E hX 1
  have h2 := contDiff_obsM_stepState g E hX 2
  fun_prop

private lemma lm_contDiff_corrF (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) :
    ContDiff ℝ 1 (fun ω : Ω W 1 => corrF g E (stepState g E X (gueBlock W 1 ω 0))) := by
  unfold corrF
  have m1 := contDiff_obsM_stepState g E hX 1
  have f1 := contDiff_obsF_stepState g E hX 1
  have f2 := contDiff_obsF_stepState g E hX 2
  have fm := contDiff_obsF_stepState g E hX (-1)
  fun_prop

private lemma lm_contDiff_linCorr (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) :
    ContDiff ℝ 1 (fun ω : Ω W 1 => linCorr g E (stepState g E X (gueBlock W 1 ω 0))) := by
  unfold linCorr
  have f1 := contDiff_obsF_stepState g E hX 1
  exact contDiff_const.mul (Complex.reCLM.contDiff.comp (contDiff_const.mul f1))

private lemma lm_integrable_of_bdd {W : ℕ} {G : Type*} [NormedAddCommGroup G] {F : Ω W 1 → G}
    (hc : Continuous F) {B : ℝ} (hb : ∀ ω, ‖F ω‖ ≤ B) : Integrable F (μ W 1) :=
  Integrable.of_bound hc.aestronglyMeasurable B (Filter.Eventually.of_forall hb)

private lemma lm_isState_step (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    (ω : Ω W 1) : IsState (stepState g E X (gueBlock W 1 ω 0)) :=
  isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)
/-! ### Moments of one block and the increment -/

/-- `𝔼‖V‖^p ≤ C_p` uniformly in `W`, as a Bochner integral (the moment half of (11.14)
[uvg:eq:tail]). -/
private lemma lm_moment (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ, ∫ ω, ‖gueBlock W 1 ω 0‖ ^ p ∂(μ W 1) ≤ C := by
  obtain ⟨C, hC, h⟩ := lintegral_norm_gueBlock_pow_le p
  refine ⟨C, hC, fun W => ?_⟩
  have hI := integrable_norm_gueBlock_pow W p
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => by positivity) hI.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hC.le ?_
  calc ∫⁻ ω, ENNReal.ofReal (‖gueBlock W 1 ω 0‖ ^ p) ∂μ W 1
      = ∫⁻ ω, ‖gueBlock W 1 ω 0‖ₑ ^ p ∂μ W 1 := by
        congr 1; funext ω
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ ≤ _ := h W

/-- `|c| ≤ 2 h_θ ‖V‖` for `g ≥ 1`, from (11.13) [uvg:eq:global]. -/
private lemma lm_abs_stepInc_le {g : ℝ} (hg : 1 ≤ g) {E : ℝ} (hE : |E| < 2) {W : ℕ}
    {X : State W} (hX : IsState X) {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    |stepInc g E X V| ≤ 2 * normalH E * ‖V‖ := by
  have hg0 : 0 < g := by linarith
  have hh := (lm_normalH_pos hE).le
  refine (abs_stepInc_le hg0 E hX hV).trans ?_
  have h0 : 0 < 1 + 2 * normalH E * ‖V‖ / g := by positivity
  have h1 := Real.log_le_sub_one_of_pos h0
  have h2 : 2 * normalH E * ‖V‖ / g ≤ 2 * normalH E * ‖V‖ := div_le_self (by positivity) hg
  linarith

/-- The tail integral `𝔼 T ≤ K₄ g⁻⁴` of Lemma 11.4 [uvg:lem:mgf], from the fourth and fifth
moments of the norm of one block. -/
private lemma lm_tail {E₀ : ℝ} :
    ∃ K₄ : ℝ, 0 < K₄ ∧ ∀ W : ℕ, ∀ g : ℝ, 1 ≤ g →
      Integrable (fun ω => lmT (lmH E₀) g ‖gueBlock W 1 ω 0‖) (μ W 1) ∧
      ∫ ω, lmT (lmH E₀) g ‖gueBlock W 1 ω 0‖ ∂(μ W 1) ≤ K₄ * (1 / g ^ 2) ^ 2 := by
  obtain ⟨C₄, hC₄, h4⟩ := lm_moment 4
  obtain ⟨C₅, hC₅, h5⟩ := lm_moment 5
  have hH0 : 0 ≤ lmH E₀ := lmH_nonneg E₀
  set H : ℝ := lmH E₀ with hH
  refine ⟨16 * Real.exp 1 * H ^ 4 * (C₄ + 2 * H * C₅) + 1, by positivity, fun W g hg => ?_⟩
  have hg0 : 0 < g := by linarith
  have e : (fun ω => lmT H g ‖gueBlock W 1 ω 0‖) = fun ω =>
      (16 * Real.exp 1 * H ^ 4 / g ^ 4) *
        (‖gueBlock W 1 ω 0‖ ^ 4 + 2 * H * ‖gueBlock W 1 ω 0‖ ^ 5) := by
    funext ω; unfold lmT; field_simp; ring
  have i4 := integrable_norm_gueBlock_pow W 4
  have i5 := (integrable_norm_gueBlock_pow W 5).const_mul (2 * H)
  have hI : Integrable (fun ω => ‖gueBlock W 1 ω 0‖ ^ 4 + 2 * H * ‖gueBlock W 1 ω 0‖ ^ 5)
      (μ W 1) := i4.add i5
  rw [e]
  refine ⟨hI.const_mul _, ?_⟩
  rw [integral_const_mul, integral_add i4 i5, integral_const_mul]
  have b4 := h4 W
  have b5 := h5 W
  have hs : ∫ ω, ‖gueBlock W 1 ω 0‖ ^ 4 ∂(μ W 1) + 2 * H * ∫ ω, ‖gueBlock W 1 ω 0‖ ^ 5 ∂(μ W 1) ≤
      C₄ + 2 * H * C₅ := by nlinarith
  have hq : 0 ≤ 16 * Real.exp 1 * H ^ 4 / g ^ 4 := by positivity
  calc 16 * Real.exp 1 * H ^ 4 / g ^ 4 * (∫ ω, ‖gueBlock W 1 ω 0‖ ^ 4 ∂(μ W 1) +
        2 * H * ∫ ω, ‖gueBlock W 1 ω 0‖ ^ 5 ∂(μ W 1))
      ≤ 16 * Real.exp 1 * H ^ 4 / g ^ 4 * (C₄ + 2 * H * C₅) := mul_le_mul_of_nonneg_left hs hq
    _ = (16 * Real.exp 1 * H ^ 4 * (C₄ + 2 * H * C₅)) * (1 / g ^ 2) ^ 2 := by
        field_simp
    _ ≤ _ := by
        have : 0 ≤ (1 / g ^ 2) ^ 2 := by positivity
        nlinarith

/-! ### Continuity of the corrector along one step -/

private lemma lm_continuous_driftCorr (g E A B : ℝ) {W : ℕ} {X : State W} (hX : IsState X) :
    Continuous (fun ω : Ω W 1 => driftCorr g E A B (stepState g E X (gueBlock W 1 ω 0))) := by
  unfold driftCorr
  exact ((lm_contDiff_linCorr g E hX).continuous.add
    (continuous_const.mul ((lm_contDiff_corrM g E hX).continuous.norm.pow 2))).add
    (continuous_const.mul ((lm_contDiff_corrF g E hX).continuous.norm.pow 2))

private lemma lm_continuous_driftY (g E A B : ℝ) {W : ℕ} {X : State W} (hX : IsState X) :
    Continuous (fun ω : Ω W 1 => driftY g E A B X (gueBlock W 1 ω 0)) := by
  unfold driftY
  exact ((contDiff_stepInc g E hX).continuous.sub (lm_continuous_driftCorr g E A B hX)).add
    continuous_const


/-- The linear corrector of Lemma 11.3 [uvg:lem:positive] satisfies `|Q| ≤ H³ g⁻²` on states,
for `|E| ≤ E₀ < 2`. -/
private lemma lm_abs_linCorr_le {E₀ : ℝ} (hE₀ : E₀ < 2) {W : ℕ} {g E : ℝ} (hE : |E| ≤ E₀)
    {X : State W} (hX : IsState X) : |linCorr g E X| ≤ lmH E₀ ^ 3 * (1 / g ^ 2) := by
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have h3 : normalH E ^ 3 ≤ lmH E₀ ^ 3 :=
    pow_le_pow_left₀ (lm_normalH_pos hE').le (lm_normalH_le hE₀ hE) 3
  have hf := norm_obsF_le_one 1 hX
  have hk : ‖(((normalH E ^ 2 : ℝ) : ℂ) / (1 + normalPhase E)) * obsF 1 X‖ ≤ lmH E₀ ^ 3 := by
    rw [norm_mul, lm_norm_kappa hE']
    have : 0 ≤ normalH E ^ 3 := pow_nonneg (lm_normalH_pos hE').le 3
    nlinarith
  unfold linCorr
  rw [abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  have := Complex.abs_re_le_norm ((((normalH E ^ 2 : ℝ) : ℂ) / (1 + normalPhase E)) * obsF 1 X)
  calc 1 / g ^ 2 * |((((normalH E ^ 2 : ℝ) : ℂ) / (1 + normalPhase E)) * obsF 1 X).re|
      ≤ 1 / g ^ 2 * lmH E₀ ^ 3 := mul_le_mul_of_nonneg_left (this.trans hk) (by positivity)
    _ = _ := by ring

/-- A continuous function bounded by `α‖V‖ + β` is integrable together with its square. -/
private lemma lm_integrable_lin {W : ℕ} {f : Ω W 1 → ℝ} (hf : Continuous f) {α β : ℝ}
    (hb : ∀ ω, |f ω| ≤ α * ‖gueBlock W 1 ω 0‖ + β) :
    Integrable f (μ W 1) ∧ Integrable (fun ω => f ω ^ 2) (μ W 1) := by
  constructor
  · refine Integrable.mono' (((integrable_norm_gueBlock_pow W 1).const_mul α).add
      (integrable_const β)) hf.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    simpa only [Pi.add_apply, pow_one, Real.norm_eq_abs] using hb ω
  · refine Integrable.mono' (((integrable_norm_gueBlock_pow W 2).const_mul (2 * α ^ 2)).add
      (integrable_const (2 * β ^ 2))) (hf.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : f ω ^ 2 ≤ (α * ‖gueBlock W 1 ω 0‖ + β) ^ 2 := by
      rw [← sq_abs (f ω)]; exact pow_le_pow_left₀ (abs_nonneg _) (hb ω) 2
    have h2 : (α * ‖gueBlock W 1 ω 0‖ + β) ^ 2 ≤
        2 * α ^ 2 * ‖gueBlock W 1 ω 0‖ ^ 2 + 2 * β ^ 2 := by
      nlinarith [sq_nonneg (α * ‖gueBlock W 1 ω 0‖ - β)]
    simp only [Pi.add_apply]
    linarith

/-- `(‖z‖² - ‖w‖²)² ≤ 4 b² ‖z - w‖²` for `‖z‖, ‖w‖ ≤ b`. -/
private lemma lm_sq_norm_sub {z w : ℂ} {b : ℝ} (hz : ‖z‖ ≤ b) (hw : ‖w‖ ≤ b) :
    (‖z‖ ^ 2 - ‖w‖ ^ 2) ^ 2 ≤ 4 * b ^ 2 * ‖z - w‖ ^ 2 := by
  have h1 : |‖z‖ - ‖w‖| ≤ ‖z - w‖ := abs_norm_sub_norm_le z w
  have hb : 0 ≤ b := (norm_nonneg z).trans hz
  have h2 : ‖z‖ + ‖w‖ ≤ 2 * b := by linarith
  have h3 : (‖z‖ ^ 2 - ‖w‖ ^ 2) ^ 2 = (‖z‖ - ‖w‖) ^ 2 * (‖z‖ + ‖w‖) ^ 2 := by ring
  rw [h3]
  have h4 : (‖z‖ - ‖w‖) ^ 2 ≤ ‖z - w‖ ^ 2 := by
    rw [← sq_abs (‖z‖ - ‖w‖)]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h5 : (‖z‖ + ‖w‖) ^ 2 ≤ (2 * b) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  calc _ ≤ ‖z - w‖ ^ 2 * (2 * b) ^ 2 := mul_le_mul h4 h5 (by positivity) (by positivity)
    _ = _ := by ring

private lemma lm_four_sq (x₁ x₂ x₃ x₄ : ℝ) :
    (x₁ - x₂ - x₃ - x₄) ^ 2 ≤ 4 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2) := by
  nlinarith [sq_nonneg (x₁ + x₂), sq_nonneg (x₁ + x₃), sq_nonneg (x₁ + x₄),
    sq_nonneg (x₂ - x₃), sq_nonneg (x₂ - x₄), sq_nonneg (x₃ - x₄)]

/-! ### The variance of the corrected increment -/

/-- The centered second moment of `Y` is at most `C (g⁻²W⁻¹ + g⁻⁴)` (proof of Lemma 11.4
[uvg:lem:mgf]), from the innovation variances of Lemma 11.2 [uvg:lem:drifts]. -/
private lemma lm_var {E₀ : ℝ} (hE₀ : E₀ < 2) (A B : ℝ) :
    ∃ V₁ V₂ : ℝ, 0 < V₁ ∧ 0 ≤ V₂ ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X → ∃ a : ℝ,
        ∫ ω, (driftY g E A B X (gueBlock W 1 ω 0) - a) ^ 2 ∂(μ W 1) ≤
          V₁ * (1 / g ^ 2 * (1 / (W : ℝ))) + V₂ * (1 / g ^ 2) ^ 2 := by
  obtain ⟨K₀, hK₀, hinn⟩ := innovation_var hE₀
  have hH0 : 0 ≤ lmH E₀ := lmH_nonneg E₀
  set H : ℝ := lmH E₀ with hH
  set b : ℝ := 1 + 8 * H ^ 3 with hb
  have hb0 : 0 ≤ b := by positivity
  refine ⟨4 * K₀ + 16 * A ^ 2 * b ^ 2 * K₀ + 16 * B ^ 2 * b ^ 2 * K₀, 4 * H ^ 6, by positivity,
    by positivity, ?_⟩
  intro W hW g hg E hE X hX
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have hg0 : 0 < g := by linarith
  have hw : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hw0 : 0 < (W : ℝ) := by linarith
  have hnH : normalH E ≤ H := lm_normalH_le hE₀ hE
  obtain ⟨hM0, hF0, hc0⟩ := hinn W hW g hg E hE X hX
  set PM : ℂ := transOp g E (corrM g E) X with hPM
  set PF : ℂ := transOp g E (corrF g E) X with hPF
  set Pc : ℝ := incMean g E X with hPc
  have hH3 : 0 ≤ H ^ 3 := pow_nonneg hH0 3
  have hMb : ∀ ω : Ω W 1, ‖corrM g E (stepState g E X (gueBlock W 1 ω 0))‖ ≤ b := fun ω =>
    ((lm_norm_corr_le hE₀ hg hE (lm_isState_step g E hX ω)).1).trans (by rw [hb]; linarith)
  have hFb : ∀ ω : Ω W 1, ‖corrF g E (stepState g E X (gueBlock W 1 ω 0))‖ ≤ b := fun ω =>
    (lm_norm_corr_le hE₀ hg hE (lm_isState_step g E hX ω)).2
  have hPMb : ‖PM‖ ≤ b := by
    have := norm_integral_le_of_norm_le_const (μ := μ W 1)
      (f := fun ω => corrM g E (stepState g E X (gueBlock W 1 ω 0))) (C := b)
      (Filter.Eventually.of_forall hMb)
    rwa [probReal_univ, mul_one] at this
  have hPFb : ‖PF‖ ≤ b := by
    have := norm_integral_le_of_norm_le_const (μ := μ W 1)
      (f := fun ω => corrF g E (stepState g E X (gueBlock W 1 ω 0))) (C := b)
      (Filter.Eventually.of_forall hFb)
    rwa [probReal_univ, mul_one] at this
  have hlb : ∀ ω : Ω W 1, |linCorr g E (stepState g E X (gueBlock W 1 ω 0))| ≤
      H ^ 3 * (1 / g ^ 2) := fun ω => lm_abs_linCorr_le hE₀ hE (lm_isState_step g E hX ω)
  have hcb : ∀ ω : Ω W 1, |stepInc g E X (gueBlock W 1 ω 0)| ≤
      2 * H * ‖gueBlock W 1 ω 0‖ := fun ω =>
    (lm_abs_stepInc_le hg hE' hX (gueBlock_isHermitian W 1 ω 0)).trans
      (by gcongr)
  have ccont : Continuous fun ω : Ω W 1 => stepInc g E X (gueBlock W 1 ω 0) :=
    (contDiff_stepInc g E hX).continuous
  have iC0 : Integrable (fun ω : Ω W 1 => (stepInc g E X (gueBlock W 1 ω 0) - Pc) ^ 2) (μ W 1) :=
    (lm_integrable_lin (f := fun ω : Ω W 1 => stepInc g E X (gueBlock W 1 ω 0) - Pc)
      (ccont.sub continuous_const) (α := 2 * H) (β := |Pc|)
      (fun ω => by
        refine (abs_sub _ _).trans ?_
        linarith [hcb ω])).2
  have iM : Integrable (fun ω : Ω W 1 =>
      ‖corrM g E (stepState g E X (gueBlock W 1 ω 0)) - PM‖ ^ 2) (μ W 1) :=
    lm_integrable_of_bdd (((lm_contDiff_corrM g E hX).continuous.sub continuous_const).norm.pow 2)
      (B := (2 * b) ^ 2) fun ω => by
      rw [norm_pow, norm_norm]
      refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
      linarith [hMb ω]
  have iF : Integrable (fun ω : Ω W 1 =>
      ‖corrF g E (stepState g E X (gueBlock W 1 ω 0)) - PF‖ ^ 2) (μ W 1) :=
    lm_integrable_of_bdd (((lm_contDiff_corrF g E hX).continuous.sub continuous_const).norm.pow 2)
      (B := (2 * b) ^ 2) fun ω => by
      rw [norm_pow, norm_norm]
      refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
      linarith [hFb ω]
  refine ⟨Pc + driftCorr g E A B X - A * ‖PM‖ ^ 2 - B * ‖PF‖ ^ 2, ?_⟩
  have iU1 : Integrable (fun ω : Ω W 1 => 4 * (stepInc g E X (gueBlock W 1 ω 0) - Pc) ^ 2)
      (μ W 1) := iC0.const_mul 4
  have iU12 : Integrable (fun ω : Ω W 1 => 4 * (stepInc g E X (gueBlock W 1 ω 0) - Pc) ^ 2 +
      4 * (H ^ 3 * (1 / g ^ 2)) ^ 2) (μ W 1) := iU1.add (integrable_const _)
  have iU123 : Integrable (fun ω : Ω W 1 => 4 * (stepInc g E X (gueBlock W 1 ω 0) - Pc) ^ 2 +
      4 * (H ^ 3 * (1 / g ^ 2)) ^ 2 +
      16 * A ^ 2 * b ^ 2 * ‖corrM g E (stepState g E X (gueBlock W 1 ω 0)) - PM‖ ^ 2) (μ W 1) :=
    iU12.add (iM.const_mul _)
  have iU : Integrable (fun ω : Ω W 1 => 4 * (stepInc g E X (gueBlock W 1 ω 0) - Pc) ^ 2 +
      4 * (H ^ 3 * (1 / g ^ 2)) ^ 2 +
      16 * A ^ 2 * b ^ 2 * ‖corrM g E (stepState g E X (gueBlock W 1 ω 0)) - PM‖ ^ 2 +
      16 * B ^ 2 * b ^ 2 * ‖corrF g E (stepState g E X (gueBlock W 1 ω 0)) - PF‖ ^ 2) (μ W 1) :=
    iU123.add (iF.const_mul _)
  have hpt : ∀ ω : Ω W 1, (driftY g E A B X (gueBlock W 1 ω 0) -
      (Pc + driftCorr g E A B X - A * ‖PM‖ ^ 2 - B * ‖PF‖ ^ 2)) ^ 2 ≤
      4 * (stepInc g E X (gueBlock W 1 ω 0) - Pc) ^ 2 + 4 * (H ^ 3 * (1 / g ^ 2)) ^ 2 +
      16 * A ^ 2 * b ^ 2 * ‖corrM g E (stepState g E X (gueBlock W 1 ω 0)) - PM‖ ^ 2 +
      16 * B ^ 2 * b ^ 2 * ‖corrF g E (stepState g E X (gueBlock W 1 ω 0)) - PF‖ ^ 2 := by
    intro ω
    have e : driftY g E A B X (gueBlock W 1 ω 0) -
        (Pc + driftCorr g E A B X - A * ‖PM‖ ^ 2 - B * ‖PF‖ ^ 2) =
        (stepInc g E X (gueBlock W 1 ω 0) - Pc) -
          linCorr g E (stepState g E X (gueBlock W 1 ω 0)) -
          A * (‖corrM g E (stepState g E X (gueBlock W 1 ω 0))‖ ^ 2 - ‖PM‖ ^ 2) -
          B * (‖corrF g E (stepState g E X (gueBlock W 1 ω 0))‖ ^ 2 - ‖PF‖ ^ 2) := by
      simp only [driftY, driftCorr]; ring
    rw [e]
    refine (lm_four_sq _ _ _ _).trans ?_
    have l2 : linCorr g E (stepState g E X (gueBlock W 1 ω 0)) ^ 2 ≤ (H ^ 3 * (1 / g ^ 2)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hlb ω) 2
    have m2 := lm_sq_norm_sub (hMb ω) hPMb
    have f2 := lm_sq_norm_sub (hFb ω) hPFb
    have m3 : (A * (‖corrM g E (stepState g E X (gueBlock W 1 ω 0))‖ ^ 2 - ‖PM‖ ^ 2)) ^ 2 ≤
        4 * A ^ 2 * b ^ 2 * ‖corrM g E (stepState g E X (gueBlock W 1 ω 0)) - PM‖ ^ 2 := by
      rw [mul_pow]
      nlinarith [sq_nonneg A]
    have f3 : (B * (‖corrF g E (stepState g E X (gueBlock W 1 ω 0))‖ ^ 2 - ‖PF‖ ^ 2)) ^ 2 ≤
        4 * B ^ 2 * b ^ 2 * ‖corrF g E (stepState g E X (gueBlock W 1 ω 0)) - PF‖ ^ 2 := by
      rw [mul_pow]
      nlinarith [sq_nonneg B]
    linarith
  have hint := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω => sq_nonneg _) iU (Filter.Eventually.of_forall hpt)
  refine hint.trans ?_
  rw [integral_add iU123 (iF.const_mul _), integral_add iU12 (iM.const_mul _),
    integral_add iU1 (integrable_const _)]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
  have hu1 : 1 / (W : ℝ) ≤ 1 := by rw [div_le_one hw0]; exact hw
  have e1 : K₀ / (g ^ 2 * (W : ℝ)) = K₀ * (1 / g ^ 2 * (1 / (W : ℝ))) := by field_simp
  have e2 : K₀ / (g ^ 2 * (W : ℝ) ^ 2) = K₀ * (1 / g ^ 2 * (1 / (W : ℝ))) * (1 / (W : ℝ)) := by
    field_simp
  have h1 : ∫ ω : Ω W 1, (stepInc g E X (gueBlock W 1 ω 0) - Pc) ^ 2 ∂(μ W 1) ≤
      K₀ * (1 / g ^ 2 * (1 / (W : ℝ))) := by rw [← e1]; exact hc0
  have h2 : ∫ ω : Ω W 1, ‖corrM g E (stepState g E X (gueBlock W 1 ω 0)) - PM‖ ^ 2 ∂(μ W 1) ≤
      K₀ * (1 / g ^ 2 * (1 / (W : ℝ))) := by
    refine hM0.trans ?_
    rw [e2]
    have : 0 ≤ K₀ * (1 / g ^ 2 * (1 / (W : ℝ))) := by positivity
    nlinarith
  have h3 : ∫ ω : Ω W 1, ‖corrF g E (stepState g E X (gueBlock W 1 ω 0)) - PF‖ ^ 2 ∂(μ W 1) ≤
      K₀ * (1 / g ^ 2 * (1 / (W : ℝ))) := by rw [← e1]; exact hF0
  have p2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 16 * A ^ 2 * b ^ 2)
  have p3 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 16 * B ^ 2 * b ^ 2)
  have e3 : 4 * (H ^ 3 * (1 / g ^ 2)) ^ 2 = 4 * H ^ 6 * (1 / g ^ 2) ^ 2 := by ring
  linarith

/-! ### The mean of the corrected increment -/

/-- Integrability of `Y` and `Y²`, the identity `𝔼Y = P_g c - (P_g - I)𝒬`, and the crude bound
`𝔼Y ≤ M₁` (proof of Lemma 11.4 [uvg:lem:mgf]). -/
private lemma lm_mean {E₀ : ℝ} (hE₀ : E₀ < 2) (A B K : ℝ) (hK0 : 0 < K)
    (hK : ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ → ∀ X : State W, IsState X →
      |driftCorr g E A B X| ≤ K) :
    ∃ M₁ : ℝ, 0 < M₁ ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X →
        Integrable (fun ω => driftY g E A B X (gueBlock W 1 ω 0)) (μ W 1) ∧
        Integrable (fun ω => driftY g E A B X (gueBlock W 1 ω 0) ^ 2) (μ W 1) ∧
        ∫ ω, driftY g E A B X (gueBlock W 1 ω 0) ∂(μ W 1) =
          incMean g E X - (transOp g E (driftCorr g E A B) X - driftCorr g E A B X) ∧
        ∫ ω, driftY g E A B X (gueBlock W 1 ω 0) ∂(μ W 1) ≤ M₁ := by
  obtain ⟨C₁, hC₁, h1⟩ := lm_moment 1
  have hH0 : 0 ≤ lmH E₀ := lmH_nonneg E₀
  set H : ℝ := lmH E₀ with hH
  refine ⟨2 * H * C₁ + 2 * K, by positivity, fun W hW g hg E hE X hX => ?_⟩
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have hnH : normalH E ≤ H := lm_normalH_le hE₀ hE
  have hcb : ∀ ω : Ω W 1, |stepInc g E X (gueBlock W 1 ω 0)| ≤ 2 * H * ‖gueBlock W 1 ω 0‖ :=
    fun ω => (lm_abs_stepInc_le hg hE' hX (gueBlock_isHermitian W 1 ω 0)).trans (by gcongr)
  have hq : ∀ ω : Ω W 1, |driftCorr g E A B (stepState g E X (gueBlock W 1 ω 0))| ≤ K :=
    fun ω => hK W hW g hg E hE _ (lm_isState_step g E hX ω)
  have hq0 := hK W hW g hg E hE X hX
  have hYb : ∀ ω : Ω W 1, |driftY g E A B X (gueBlock W 1 ω 0)| ≤
      2 * H * ‖gueBlock W 1 ω 0‖ + 2 * K := by
    intro ω
    have := hcb ω
    have := hq ω
    unfold driftY
    calc _ ≤ |stepInc g E X (gueBlock W 1 ω 0) -
          driftCorr g E A B (stepState g E X (gueBlock W 1 ω 0))| +
          |driftCorr g E A B X| := abs_add_le _ _
      _ ≤ |stepInc g E X (gueBlock W 1 ω 0)| +
          |driftCorr g E A B (stepState g E X (gueBlock W 1 ω 0))| + |driftCorr g E A B X| := by
        gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  obtain ⟨iY, iY2⟩ := lm_integrable_lin (lm_continuous_driftY g E A B hX) hYb
  have ic : Integrable (fun ω : Ω W 1 => stepInc g E X (gueBlock W 1 ω 0)) (μ W 1) :=
    (lm_integrable_lin (contDiff_stepInc g E hX).continuous (α := 2 * H) (β := 0)
      (fun ω => by linarith [hcb ω])).1
  have iq : Integrable (fun ω : Ω W 1 => driftCorr g E A B (stepState g E X (gueBlock W 1 ω 0)))
      (μ W 1) :=
    lm_integrable_of_bdd (lm_continuous_driftCorr g E A B hX) (B := K) fun ω => by
      rw [Real.norm_eq_abs]; exact hq ω
  have ics : Integrable (fun ω : Ω W 1 => stepInc g E X (gueBlock W 1 ω 0) -
      driftCorr g E A B (stepState g E X (gueBlock W 1 ω 0))) (μ W 1) := ic.sub iq
  have hint : ∫ ω, driftY g E A B X (gueBlock W 1 ω 0) ∂(μ W 1) =
      incMean g E X - (transOp g E (driftCorr g E A B) X - driftCorr g E A B X) := by
    unfold driftY incMean transOp
    rw [integral_add ics (integrable_const _), integral_sub ic iq, integral_const, probReal_univ,
      one_smul]
    ring
  refine ⟨iY, iY2, hint, ?_⟩
  have iR : Integrable (fun ω : Ω W 1 => 2 * H * ‖gueBlock W 1 ω 0‖ ^ 1 + 2 * K) (μ W 1) :=
    ((integrable_norm_gueBlock_pow W 1).const_mul (2 * H)).add (integrable_const _)
  have hle : ∫ ω, driftY g E A B X (gueBlock W 1 ω 0) ∂(μ W 1) ≤
      ∫ ω, (2 * H * ‖gueBlock W 1 ω 0‖ ^ 1 + 2 * K) ∂(μ W 1) :=
    integral_mono iY iR fun ω => by
      simp only [pow_one]; exact (le_abs_self _).trans (hYb ω)
  have iR1 : Integrable (fun ω : Ω W 1 => 2 * H * ‖gueBlock W 1 ω 0‖ ^ 1) (μ W 1) :=
    (integrable_norm_gueBlock_pow W 1).const_mul (2 * H)
  rw [integral_add iR1 (integrable_const _), integral_const_mul, integral_const, probReal_univ,
    one_smul] at hle
  have := mul_le_mul_of_nonneg_left (h1 W) (by positivity : 0 ≤ 2 * H)
  linarith

/-- The pointwise bound `e^{-sY} ≤ 1 - sY + s²Y² + T` for the corrected increment of one step. -/
private lemma lm_pointwise_step {E₀ : ℝ} (hE₀ : E₀ < 2) {A B K s : ℝ} (hs : 0 < s)
    (hs2 : s ≤ 1 / 2) (hsK : s * K ≤ 1 / 4)
    (hK : ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ → ∀ X : State W, IsState X →
      |driftCorr g E A B X| ≤ K)
    {W : ℕ} (hW : 1 ≤ W) {g : ℝ} (hg : 1 ≤ g) {E : ℝ} (hE : |E| ≤ E₀) {X : State W}
    (hX : IsState X) (ω : Ω W 1) :
    Real.exp (-s * driftY g E A B X (gueBlock W 1 ω 0)) ≤
      1 - s * driftY g E A B X (gueBlock W 1 ω 0) +
        s ^ 2 * driftY g E A B X (gueBlock W 1 ω 0) ^ 2 +
        lmT (lmH E₀) g ‖gueBlock W 1 ω 0‖ := by
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have hg0 : 0 < g := by linarith
  have hH0 := lmH_nonneg E₀
  have hh := (lm_normalH_pos hE').le
  have hnH : normalH E ≤ lmH E₀ := lm_normalH_le hE₀ hE
  refine lm_pointwise (c := stepInc g E X (gueBlock W 1 ω 0)) hs hs2 hsK hg hH0
    (norm_nonneg _) ?_ ?_
  · refine (abs_stepInc_le hg0 E hX (gueBlock_isHermitian W 1 ω 0)).trans ?_
    apply Real.log_le_log (by positivity)
    gcongr
  · have h1 := hK W hW g hg E hE _ (lm_isState_step g E hX ω)
    have h2 := hK W hW g hg E hE X hX
    have e : driftY g E A B X (gueBlock W 1 ω 0) - stepInc g E X (gueBlock W 1 ω 0) =
        -driftCorr g E A B (stepState g E X (gueBlock W 1 ω 0)) + driftCorr g E A B X := by
      unfold driftY; ring
    rw [e]
    calc _ ≤ |-driftCorr g E A B (stepState g E X (gueBlock W 1 ω 0))| +
          |driftCorr g E A B X| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg]; linarith

/-- The closing step of Lemma 11.4 [uvg:lem:mgf]: `𝔼e^{-sY} ≤ 1 - s𝔼Y + s²(𝔼Y)² + s²V + 𝔼T`. -/
private lemma lm_close {s a₀ m t u V₁ V₂ K₄ Y2 V Tint : ℝ} (hs : 0 < s) (hm0 : 0 ≤ s * m)
    (hm1 : s * m ≤ 1 / 2) (hmlow : a₀ * (t * u) ≤ m) (hY2 : Y2 ≤ m ^ 2 + V)
    (hV : V ≤ V₁ * (t * u) + V₂ * t ^ 2) (hT : Tint ≤ K₄ * t ^ 2)
    (key : 1 - s / 2 * (a₀ * (t * u)) + s ^ 2 * (V₁ * (t * u) + V₂ * t ^ 2) + K₄ * t ^ 2 ≤
      1 - s * a₀ / 8 * (t * u)) :
    1 - s * m + s ^ 2 * Y2 + Tint ≤ 1 - s * a₀ / 8 * (t * u) := by
  have A1 : s ^ 2 * m ^ 2 ≤ s * m / 2 := by
    nlinarith [mul_nonneg hm0 (sub_nonneg.2 hm1)]
  have A2 : s * (a₀ * (t * u)) ≤ s * m := mul_le_mul_of_nonneg_left hmlow hs.le
  have A3 : s ^ 2 * Y2 ≤ s ^ 2 * (m ^ 2 + (V₁ * (t * u) + V₂ * t ^ 2)) :=
    mul_le_mul_of_nonneg_left (hY2.trans (by linarith)) (by positivity)
  nlinarith

/-- Lemma 11.4 [uvg:lem:mgf]: with `𝒬` bounded as in Lemma 11.3 [uvg:lem:positive], there are
`s, c > 0` with `𝔼(e^{-sY} | X) ≤ exp(-c g⁻²/W)` uniformly in the state, for `W ≥ W₀` and
`g ≥ C_* √W`. -/
theorem large_mgf {E₀ : ℝ} (hE₀ : E₀ < 2) :
    ∃ A B K Cs s c : ℝ, 0 < A ∧ 0 < B ∧ 0 < K ∧ 1 ≤ Cs ∧ 0 < s ∧ s < 1 ∧ 0 < c ∧
      (∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ → ∀ X : State W, IsState X →
        |driftCorr g E A B X| ≤ K) ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, Cs * Real.sqrt W ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
        ∀ X : State W, IsState X →
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * driftY g E A B X (gueBlock W 1 ω 0))) ∂(μ W 1) ≤
            ENNReal.ofReal (Real.exp (-c / (W * g ^ 2))) := by
  obtain ⟨A, B, a₀, Cs₀, K, hA, hB, ha₀, hCs₀, hK, hbd, W₀', hpos⟩ := large_positive hE₀
  obtain ⟨V₁, V₂, hV₁, hV₂, hvar⟩ := lm_var hE₀ A B
  obtain ⟨M₁, hM₁, hmean⟩ := lm_mean hE₀ A B K hK hbd
  obtain ⟨K₄, hK₄, htail⟩ := lm_tail (E₀ := E₀)
  set s : ℝ := min (1 / 2) (min (1 / (4 * K)) (min (1 / (2 * M₁)) (a₀ / (8 * V₁)))) with hs
  have hs0 : 0 < s :=
    lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hs2 : s ≤ 1 / 2 := min_le_left _ _
  have hsK' : s ≤ 1 / (4 * K) := (min_le_right _ _).trans (min_le_left _ _)
  have hsM' : s ≤ 1 / (2 * M₁) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hsV' : s ≤ a₀ / (8 * V₁) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hsK : s * K ≤ 1 / 4 := by
    calc s * K ≤ 1 / (4 * K) * K := by gcongr
      _ = 1 / 4 := by field_simp
  have hsM : s * M₁ ≤ 1 / 2 := by
    calc s * M₁ ≤ 1 / (2 * M₁) * M₁ := by gcongr
      _ = 1 / 2 := by field_simp
  have hsV : s * V₁ ≤ a₀ / 8 := by
    calc s * V₁ ≤ a₀ / (8 * V₁) * V₁ := by gcongr
      _ = a₀ / 8 := by field_simp
  set Cs : ℝ := Cs₀ + 8 * s * V₂ / a₀ + 8 * K₄ / (s * a₀) with hCs
  have hCsV : 8 * s * V₂ / a₀ ≤ Cs := by
    have : 0 ≤ 8 * K₄ / (s * a₀) := by positivity
    linarith
  have hCsK : 8 * K₄ / (s * a₀) ≤ Cs := by
    have : 0 ≤ 8 * s * V₂ / a₀ := by positivity
    linarith
  have hCs₀le : Cs₀ ≤ Cs := by
    have : 0 ≤ 8 * s * V₂ / a₀ := by positivity
    have : 0 ≤ 8 * K₄ / (s * a₀) := by positivity
    linarith
  have hCs1 : 1 ≤ Cs := hCs₀.trans hCs₀le
  refine ⟨A, B, K, Cs, s, s * a₀ / 8, hA, hB, hK, hCs1, hs0, by linarith, by positivity, hbd,
    max W₀' 1, ?_⟩
  intro W hW g hgCs E hE X hX
  have hW0' : W₀' ≤ W := (le_max_left _ _).trans hW
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hw1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hw0 : 0 < (W : ℝ) := by linarith
  have hsq1 : 1 ≤ Real.sqrt W := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hw1
  have hg1 : 1 ≤ g := (one_le_mul_of_one_le_of_one_le hCs1 hsq1).trans hgCs
  have hg0 : 0 < g := by linarith
  have hgCs₀ : Cs₀ * Real.sqrt W ≤ g :=
    (mul_le_mul_of_nonneg_right hCs₀le (Real.sqrt_nonneg _)).trans hgCs
  obtain ⟨hYi, hY2i, hYeq, hYle⟩ := hmean W hW1 g hg1 E hE X hX
  obtain ⟨a, hva⟩ := hvar W hW1 g hg1 E hE X hX
  obtain ⟨hTi, hTle⟩ := htail W g hg1
  have hlow := hpos W hW0' g hgCs₀ E hE X hX
  have h1 := lm_lintegral_le (μ := μ W 1) (s := s)
    (Y := fun ω => driftY g E A B X (gueBlock W 1 ω 0))
    (T := fun ω => lmT (lmH E₀) g ‖gueBlock W 1 ω 0‖) hYi hY2i hTi
    (fun ω => lm_pointwise_step hE₀ hs0 hs2 hsK hbd hW1 hg1 hE hX ω)
    (fun ω => lmT_nonneg (lmH_nonneg E₀) (norm_nonneg _))
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsq := lm_sq_le hYi hY2i a
  set m : ℝ := ∫ ω, driftY g E A B X (gueBlock W 1 ω 0) ∂(μ W 1) with hm
  have hmlow : a₀ / (g ^ 2 * W) ≤ m := by rw [hYeq]; exact hlow
  have ht0 : 0 < 1 / g ^ 2 := by positivity
  have hu0 : 0 < 1 / (W : ℝ) := by positivity
  have hat : a₀ / (g ^ 2 * W) = a₀ * (1 / g ^ 2 * (1 / (W : ℝ))) := by field_simp
  have hg2 : Cs ^ 2 * W ≤ g ^ 2 := by
    have : (Cs * Real.sqrt W) ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ (by positivity) hgCs 2
    rwa [mul_pow, Real.sq_sqrt hw0.le] at this
  have htu : 1 / g ^ 2 * Cs ^ 2 ≤ 1 / (W : ℝ) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hw0]
    linarith
  have key := lm_final ht0 hu0 htu hCs1 hs0 ha₀ hsV hCsV hCsK (K₄ := K₄) (V₁ := V₁) (V₂ := V₂)
  have hm0 : 0 ≤ s * m := by
    have : 0 < a₀ / (g ^ 2 * W) := by positivity
    exact mul_nonneg hs0.le (by linarith)
  have hm1 : s * m ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hYle hs0.le).trans hsM
  have hcl := lm_close (t := 1 / g ^ 2) (u := 1 / (W : ℝ)) (a₀ := a₀) (V₁ := V₁) (V₂ := V₂)
    (K₄ := K₄) hs0 hm0 hm1 (by rw [← hat]; exact hmlow) hsq hva hTle key
  have hexp : 1 - s * a₀ / 8 * (1 / g ^ 2 * (1 / (W : ℝ))) ≤
      Real.exp (-(s * a₀ / 8) / (W * g ^ 2)) := by
    have e : -(s * a₀ / 8) / (W * g ^ 2) = -(s * a₀ / 8 * (1 / g ^ 2 * (1 / (W : ℝ)))) := by
      field_simp
    rw [e]
    have := Real.add_one_le_exp (-(s * a₀ / 8 * (1 / g ^ 2 * (1 / (W : ℝ)))))
    linarith
  exact hcl.trans hexp

end LSBA
