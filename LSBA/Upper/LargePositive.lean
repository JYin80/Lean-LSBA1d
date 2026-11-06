import LSBA.Upper.LargeDrift
import LSBA.Upper.LargeIncrement

/-!
# The bounded corrector and positive drift

The linear corrector `Q = −g⁻² Re[h² f₁/(1 + e^{−2iθ})]`, the corrector `𝒬 = Q + A|M|² + B|F|²` and
the corrected increment `Y = c − 𝒬(X′) + 𝒬(X)`; Lemma 11.3 [uvg:lem:positive]: `𝒬` is bounded and
(11.23) [uvg:eq:positive] `P_g c − (P_g − I)𝒬 ≥ a₀/(g²W)` for `W ≥ W₀`, `g ≥ C_*√W`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The real linear corrector `Q = -g⁻² Re[h² f_1/(1 + e^{-2iθ})]` before Lemma 11.3
[uvg:lem:positive]. -/
def linCorr (g E : ℝ) {W : ℕ} (X : State W) : ℝ :=
  -(1 / g ^ 2) * ((((normalH E ^ 2 : ℝ) : ℂ) / (1 + normalPhase E)) * obsF 1 X).re

/-- `𝒬 = Q + A|M|² + B|F|²` of Lemma 11.3 [uvg:lem:positive]. -/
def driftCorr (g E A B : ℝ) {W : ℕ} (X : State W) : ℝ :=
  linCorr g E X + A * ‖corrM g E X‖ ^ 2 + B * ‖corrF g E X‖ ^ 2

/-- `Y = c(X, V) - 𝒬(X') + 𝒬(X)` before Lemma 11.4 [uvg:lem:mgf]. -/
def driftY (g E A B : ℝ) {W : ℕ} (X : State W) (V : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  stepInc g E X V - driftCorr g E A B (stepState g E X V) + driftCorr g E A B X

/-! ### Scalar facts -/

/-- `H = (2 √(1 - E₀²/4))⁻¹`, the bound `h_θ ≤ H` of (11.1) [lg:eq:normal] for `|E| ≤ E₀ < 2`. -/
private def lpH (E₀ : ℝ) : ℝ := (2 * √(1 - E₀ ^ 2 / 4))⁻¹

private lemma lpH_nonneg (E₀ : ℝ) : 0 ≤ lpH E₀ := by
  unfold lpH; positivity

private lemma lp_sin_pos {E : ℝ} (hE : |E| < 2) : 0 < Real.sin (freeAngle E) := by
  unfold freeAngle
  rw [Real.sin_arccos]
  apply Real.sqrt_pos.mpr
  have h : E ^ 2 < 4 := by
    have := sq_abs E
    nlinarith [abs_nonneg E]
  nlinarith

private lemma lp_normalH_pos {E : ℝ} (hE : |E| < 2) : 0 < normalH E := by
  unfold normalH
  have := lp_sin_pos hE
  positivity

private lemma lp_half_le_normalH {E : ℝ} (hE : |E| < 2) : 1 / 2 ≤ normalH E := by
  unfold normalH
  have hs := lp_sin_pos hE
  have h1 : Real.sin (freeAngle E) ≤ 1 := Real.sin_le_one _
  have : (2 * Real.sin (freeAngle E))⁻¹ ≥ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by positivity) (by linarith)
  simpa using this

private lemma lp_normalH_le {E₀ E : ℝ} (hE₀ : E₀ < 2) (hE : |E| ≤ E₀) :
    normalH E ≤ lpH E₀ := by
  unfold normalH freeAngle lpH
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
private lemma lp_norm_normalPhase (E : ℝ) : ‖normalPhase E‖ = 1 := by
  unfold normalPhase
  rw [norm_neg, show 2 * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `|1 + e^{-2iθ}| = 2 sin ϑ = h_θ⁻¹` for `|E| < 2`. -/
private lemma lp_norm_one_add {E : ℝ} (hE : |E| < 2) : ‖1 + normalPhase E‖ = (normalH E)⁻¹ := by
  have hs := lp_sin_pos hE
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
private lemma lp_norm_kappa {E : ℝ} (hE : |E| < 2) :
    ‖((normalH E ^ 2 : ℝ) : ℂ) / (1 + normalPhase E)‖ = normalH E ^ 3 := by
  have hh := lp_normalH_pos hE
  rw [norm_div, lp_norm_one_add hE, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), div_inv_eq_mul]
  ring

private lemma lp_mul_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a‖ * ‖b‖ ≤ 1 :=
  (mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

private lemma lp_norm_q {E g : ℝ} (hE : |E| < 2) :
    ‖((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ)‖ = normalH E ^ 2 / g ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  have := lp_normalH_pos hE
  positivity

/-- The correction of `M` in (11.16) [uvg:eq:M] has norm at most `4 h_θ³ g⁻²`. -/
private lemma lp_norm_corrM_sub {W : ℕ} {E g : ℝ} (hE : |E| < 2) {Y : State W} (hY : IsState Y) :
    ‖corrM g E Y - obsM 1 Y‖ ≤ 4 * normalH E ^ 3 / g ^ 2 := by
  have hh := lp_normalH_pos hE
  unfold corrM
  rw [sub_sub_cancel_left, norm_neg, norm_mul, lp_norm_q hE, norm_div, lp_norm_one_add hE,
    div_inv_eq_mul]
  have hm1 := norm_obsM_le_one 1 hY
  have hm2 := norm_obsM_le_one 2 hY
  have hN : ‖normalPhase E + obsM 2 Y + 2 * obsM 1 Y ^ 2‖ ≤ 4 := by
    calc ‖normalPhase E + obsM 2 Y + 2 * obsM 1 Y ^ 2‖
        ≤ ‖normalPhase E‖ + ‖obsM 2 Y‖ + ‖2 * obsM 1 Y ^ 2‖ := norm_add₃_le
      _ ≤ 1 + 1 + 2 := by
        rw [lp_norm_normalPhase, norm_mul, norm_pow, Complex.norm_ofNat]
        have : ‖obsM 1 Y‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hm1
        linarith
      _ = 4 := by norm_num
  calc normalH E ^ 2 / g ^ 2 * (‖normalPhase E + obsM 2 Y + 2 * obsM 1 Y ^ 2‖ * normalH E)
      ≤ normalH E ^ 2 / g ^ 2 * (4 * normalH E) := by gcongr
    _ = 4 * normalH E ^ 3 / g ^ 2 := by ring

/-- The correction of `F` in (11.17) [uvg:eq:F] has norm at most `8 h_θ³ g⁻²`. -/
private lemma lp_norm_corrF_sub {W : ℕ} {E g : ℝ} (hE : |E| < 2) {Y : State W} (hY : IsState Y) :
    ‖corrF g E Y - obsF 1 Y‖ ≤ 8 * normalH E ^ 3 / g ^ 2 := by
  have hh := lp_normalH_pos hE
  unfold corrF
  rw [sub_sub_cancel_left, norm_neg, norm_mul, lp_norm_q hE, norm_div, lp_norm_one_add hE,
    div_inv_eq_mul]
  have hm1 := norm_obsM_le_one 1 hY
  have hf1 := norm_obsF_le_one 1 hY
  have hf2 := norm_obsF_le_one 2 hY
  have hf3 := norm_obsF_le_one (-1) hY
  have hN : ‖4 * obsM 1 Y * obsF 1 Y + 2 * obsF 2 Y - obsF 1 Y ^ 2 -
      normalPhase E * obsF 1 Y * obsF (-1) Y‖ ≤ 8 := by
    have e1 : ‖4 * obsM 1 Y * obsF 1 Y‖ ≤ 4 := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat]
      have := lp_mul_le_one hm1 hf1
      linarith
    have e2 : ‖2 * obsF 2 Y‖ ≤ 2 := by
      rw [norm_mul, Complex.norm_ofNat]; linarith
    have e3 : ‖obsF 1 Y ^ 2‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hf1
    have e4 : ‖normalPhase E * obsF 1 Y * obsF (-1) Y‖ ≤ 1 := by
      rw [norm_mul, norm_mul, lp_norm_normalPhase, one_mul]
      exact lp_mul_le_one hf1 hf3
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
private lemma lp_corrM_sub_le {E₀ : ℝ} (hE₀ : E₀ < 2) {W : ℕ} {g E : ℝ} (hE : |E| ≤ E₀)
    {Y : State W} (hY : IsState Y) :
    ‖corrM g E Y - obsM 1 Y‖ ≤ 4 * lpH E₀ ^ 3 * (1 / g ^ 2) := by
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have h3 : normalH E ^ 3 ≤ lpH E₀ ^ 3 :=
    pow_le_pow_left₀ (lp_normalH_pos hE').le (lp_normalH_le hE₀ hE) 3
  calc _ ≤ 4 * normalH E ^ 3 / g ^ 2 := lp_norm_corrM_sub hE' hY
    _ = 4 * normalH E ^ 3 * (1 / g ^ 2) := by ring
    _ ≤ _ := by gcongr

/-- `‖F - f₁‖ ≤ 8 H³ g⁻²` uniformly in `|E| ≤ E₀`. -/
private lemma lp_corrF_sub_le {E₀ : ℝ} (hE₀ : E₀ < 2) {W : ℕ} {g E : ℝ} (hE : |E| ≤ E₀)
    {Y : State W} (hY : IsState Y) :
    ‖corrF g E Y - obsF 1 Y‖ ≤ 8 * lpH E₀ ^ 3 * (1 / g ^ 2) := by
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have h3 : normalH E ^ 3 ≤ lpH E₀ ^ 3 :=
    pow_le_pow_left₀ (lp_normalH_pos hE').le (lp_normalH_le hE₀ hE) 3
  calc _ ≤ 8 * normalH E ^ 3 / g ^ 2 := lp_norm_corrF_sub hE' hY
    _ = 8 * normalH E ^ 3 * (1 / g ^ 2) := by ring
    _ ≤ _ := by gcongr

/-- `‖M‖ ≤ 1 + 4 H³` and `‖F‖ ≤ 1 + 8 H³` on states, for `g ≥ 1`. -/
private lemma lp_norm_corr_le {E₀ : ℝ} (hE₀ : E₀ < 2) {W : ℕ} {g E : ℝ} (hg : 1 ≤ g)
    (hE : |E| ≤ E₀) {Y : State W} (hY : IsState Y) :
    ‖corrM g E Y‖ ≤ 1 + 4 * lpH E₀ ^ 3 ∧ ‖corrF g E Y‖ ≤ 1 + 8 * lpH E₀ ^ 3 := by
  have hg2 : 1 / g ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ hg
  have hH0 : 0 ≤ lpH E₀ ^ 3 := pow_nonneg (lpH_nonneg E₀) 3
  have hm1 := norm_obsM_le_one 1 hY
  have hf1 := norm_obsF_le_one 1 hY
  have hM := lp_corrM_sub_le hE₀ (g := g) hE hY
  have hF := lp_corrF_sub_le hE₀ (g := g) hE hY
  constructor
  · calc ‖corrM g E Y‖ ≤ ‖corrM g E Y - obsM 1 Y‖ + ‖obsM 1 Y‖ := by
          have := norm_sub_norm_le (corrM g E Y) (obsM 1 Y)
          linarith
      _ ≤ 4 * lpH E₀ ^ 3 * 1 + 1 := by
          gcongr
          exact hM.trans (by gcongr)
      _ = _ := by ring
  · calc ‖corrF g E Y‖ ≤ ‖corrF g E Y - obsF 1 Y‖ + ‖obsF 1 Y‖ := by
          have := norm_sub_norm_le (corrF g E Y) (obsF 1 Y)
          linarith
      _ ≤ 8 * lpH E₀ ^ 3 * 1 + 1 := by
          gcongr
          exact hF.trans (by gcongr)
      _ = _ := by ring

/-- `|Q| ≤ H³` on states, for `g ≥ 1`. -/
private lemma lp_abs_linCorr_le {E₀ : ℝ} (hE₀ : E₀ < 2) {W : ℕ} {g E : ℝ} (hg : 1 ≤ g)
    (hE : |E| ≤ E₀) {X : State W} (hX : IsState X) : |linCorr g E X| ≤ lpH E₀ ^ 3 := by
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have hg2 : 1 / g ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ hg
  have h3 : normalH E ^ 3 ≤ lpH E₀ ^ 3 :=
    pow_le_pow_left₀ (lp_normalH_pos hE').le (lp_normalH_le hE₀ hE) 3
  have hf := norm_obsF_le_one 1 hX
  have hk : ‖(((normalH E ^ 2 : ℝ) : ℂ) / (1 + normalPhase E)) * obsF 1 X‖ ≤ lpH E₀ ^ 3 := by
    rw [norm_mul, lp_norm_kappa hE']
    have : 0 ≤ normalH E ^ 3 := pow_nonneg (lp_normalH_pos hE').le 3
    nlinarith
  unfold linCorr
  rw [abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  have := Complex.abs_re_le_norm ((((normalH E ^ 2 : ℝ) : ℂ) / (1 + normalPhase E)) * obsF 1 X)
  have h0 : 0 ≤ lpH E₀ ^ 3 := pow_nonneg (lpH_nonneg E₀) 3
  calc 1 / g ^ 2 * |((((normalH E ^ 2 : ℝ) : ℂ) / (1 + normalPhase E)) * obsF 1 X).re|
      ≤ 1 * lpH E₀ ^ 3 := by
        apply mul_le_mul hg2 (this.trans hk) (abs_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-! ### The Young step of (11.23) [uvg:eq:positive] -/

/-- The constant `K_ε` of the Young step in the proof of Lemma 11.3 [uvg:lem:positive]. -/
private def lpKe (P c₁ c₂ ε : ℝ) : ℝ :=
  ε * (2 * P / ε) ^ 2 / 4 + 1 + (P * c₂) ^ 2 / 4 + ε * (2 * P / ε) ^ 2 * c₁ ^ 2 / 4 +
    P * c₁ * c₂ + ε * c₂ ^ 2 / 4

private lemma lpKe_nonneg {P c₁ c₂ ε : ℝ} (hP : 0 ≤ P) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hε : 0 < ε) : 0 ≤ lpKe P c₁ c₂ ε := by
  unfold lpKe; positivity

/-- `h² (|m₁||f₁| + |f₁|²/(2W)) ≤ K_ε |M|² + ε |F|² + K_ε g⁻⁴` from `|m₁| ≤ |M| + c₁ g⁻²`,
`|f₁| ≤ |F| + c₂ g⁻²`, for `W ≥ 4 h₀²/ε`; here `t = g⁻²` and `u = W⁻¹`. -/
private lemma lp_young_alg {P c₁ c₂ ε t u h2 x y μ φ : ℝ} (hP : 0 ≤ P) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hε : 0 < ε) (ht : 0 ≤ t) (hu : 0 ≤ u) (hPu : 4 * P * u ≤ ε) (h2P : h2 ≤ P)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hμ : 0 ≤ μ)
    (hx : x ≤ μ + c₁ * t) (hy : y ≤ φ + c₂ * t) :
    h2 * (x * y) + h2 * y ^ 2 * u / 2 ≤
      lpKe P c₁ c₂ ε * μ ^ 2 + ε * φ ^ 2 + lpKe P c₁ c₂ ε * t ^ 2 := by
  set q : ℝ := 2 * P / ε with hq
  have hPq : P = q * ε / 2 := by rw [hq]; field_simp
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  -- the product term
  have hxy : x * y ≤ (μ + c₁ * t) * (φ + c₂ * t) :=
    mul_le_mul hx hy hy0 (by positivity)
  have h1 : h2 * (x * y) ≤ P * ((μ + c₁ * t) * (φ + c₂ * t)) :=
    mul_le_mul h2P hxy (by positivity) hP
  -- the square term
  have hy2 : y ^ 2 ≤ 2 * φ ^ 2 + 2 * c₂ ^ 2 * t ^ 2 := by
    have : y ^ 2 ≤ (φ + c₂ * t) ^ 2 := pow_le_pow_left₀ hy0 hy 2
    nlinarith [sq_nonneg (φ - c₂ * t)]
  have h3 : h2 * y ^ 2 * u / 2 ≤ ε / 8 * y ^ 2 := by
    have h5 : h2 * y ^ 2 * u ≤ P * y ^ 2 * u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2P (sq_nonneg y)) hu
    have h6 := mul_le_mul_of_nonneg_right hPu (sq_nonneg y)
    linarith
  have h4 : ε / 8 * y ^ 2 ≤ ε / 4 * φ ^ 2 + ε / 4 * c₂ ^ 2 * t ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hy2 (by positivity : (0 : ℝ) ≤ ε / 8)]
  -- three Young inequalities
  have y1 : P * μ * φ ≤ ε / 4 * φ ^ 2 + ε * q ^ 2 / 4 * μ ^ 2 := by
    rw [hPq]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ ε / 4) (sq_nonneg (φ - q * μ))]
  have y2 : P * c₂ * t * μ ≤ μ ^ 2 + (P * c₂) ^ 2 / 4 * t ^ 2 := by
    nlinarith [sq_nonneg (μ - P * c₂ * t / 2)]
  have y3 : P * c₁ * t * φ ≤ ε / 4 * φ ^ 2 + ε * q ^ 2 * c₁ ^ 2 / 4 * t ^ 2 := by
    rw [hPq]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ ε / 4) (sq_nonneg (φ - q * c₁ * t))]
  have hR : 0 ≤ (P * c₂) ^ 2 / 4 + ε * q ^ 2 * c₁ ^ 2 / 4 + P * c₁ * c₂ + ε * c₂ ^ 2 / 4 := by
    positivity
  have k1 := mul_nonneg hR (sq_nonneg μ)
  have k2 := mul_nonneg (by positivity : (0 : ℝ) ≤ ε * q ^ 2 / 4 + 1) (sq_nonneg t)
  have k3 := mul_nonneg (by positivity : (0 : ℝ) ≤ ε) (sq_nonneg φ)
  have hK : lpKe P c₁ c₂ ε = ε * q ^ 2 / 4 + 1 + ((P * c₂) ^ 2 / 4 + ε * q ^ 2 * c₁ ^ 2 / 4 +
      P * c₁ * c₂ + ε * c₂ ^ 2 / 4) := by
    unfold lpKe; rw [hq]; ring
  rw [hK]
  linarith [k1, k2, k3]

/-! ### The corrector along one step -/

private lemma lp_contDiff_corrM (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) :
    ContDiff ℝ 1 (fun ω : Ω W 1 => corrM g E (stepState g E X (gueBlock W 1 ω 0))) := by
  unfold corrM
  have h1 := contDiff_obsM_stepState g E hX 1
  have h2 := contDiff_obsM_stepState g E hX 2
  fun_prop

private lemma lp_contDiff_corrF (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) :
    ContDiff ℝ 1 (fun ω : Ω W 1 => corrF g E (stepState g E X (gueBlock W 1 ω 0))) := by
  unfold corrF
  have m1 := contDiff_obsM_stepState g E hX 1
  have f1 := contDiff_obsF_stepState g E hX 1
  have f2 := contDiff_obsF_stepState g E hX 2
  have fm := contDiff_obsF_stepState g E hX (-1)
  fun_prop

private lemma lp_contDiff_linCorr (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) :
    ContDiff ℝ 1 (fun ω : Ω W 1 => linCorr g E (stepState g E X (gueBlock W 1 ω 0))) := by
  unfold linCorr
  have f1 := contDiff_obsF_stepState g E hX 1
  exact contDiff_const.mul (Complex.reCLM.contDiff.comp (contDiff_const.mul f1))

private lemma lp_integrable_of_bdd {W : ℕ} {G : Type*} [NormedAddCommGroup G] {F : Ω W 1 → G}
    (hc : Continuous F) {B : ℝ} (hb : ∀ ω, ‖F ω‖ ≤ B) : Integrable F (μ W 1) :=
  Integrable.of_bound hc.aestronglyMeasurable B (Filter.Eventually.of_forall hb)

private lemma lp_isState_step (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    (ω : Ω W 1) : IsState (stepState g E X (gueBlock W 1 ω 0)) :=
  isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)

/-- `P_g` is linear on `𝒬 = Q + A|M|² + B|F|²` of Lemma 11.3 [uvg:lem:positive]. -/
private lemma lp_transOp_driftCorr {E₀ : ℝ} (hE₀ : E₀ < 2) {W : ℕ} {g E : ℝ} (hg : 1 ≤ g)
    (hE : |E| ≤ E₀) {X : State W} (hX : IsState X) (A B : ℝ) :
    transOp g E (driftCorr g E A B) X = transOp g E (linCorr g E) X +
      A * transOp g E (fun Y => ‖corrM g E Y‖ ^ 2) X +
        B * transOp g E (fun Y => ‖corrF g E Y‖ ^ 2) X := by
  have iL : Integrable (fun ω : Ω W 1 => linCorr g E (stepState g E X (gueBlock W 1 ω 0)))
      (μ W 1) :=
    lp_integrable_of_bdd (lp_contDiff_linCorr g E hX).continuous (B := lpH E₀ ^ 3) fun ω => by
      rw [Real.norm_eq_abs]; exact lp_abs_linCorr_le hE₀ hg hE (lp_isState_step g E hX ω)
  have iM : Integrable (fun ω : Ω W 1 => ‖corrM g E (stepState g E X (gueBlock W 1 ω 0))‖ ^ 2)
      (μ W 1) :=
    lp_integrable_of_bdd ((lp_contDiff_corrM g E hX).continuous.norm.pow 2)
      (B := (1 + 4 * lpH E₀ ^ 3) ^ 2) fun ω => by
      rw [norm_pow, norm_norm]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (lp_norm_corr_le hE₀ hg hE (lp_isState_step g E hX ω)).1 2
  have iF : Integrable (fun ω : Ω W 1 => ‖corrF g E (stepState g E X (gueBlock W 1 ω 0))‖ ^ 2)
      (μ W 1) :=
    lp_integrable_of_bdd ((lp_contDiff_corrF g E hX).continuous.norm.pow 2)
      (B := (1 + 8 * lpH E₀ ^ 3) ^ 2) fun ω => by
      rw [norm_pow, norm_norm]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (lp_norm_corr_le hE₀ hg hE (lp_isState_step g E hX ω)).2 2
  unfold transOp
  simp only [driftCorr]
  have iLM : Integrable (fun ω : Ω W 1 => linCorr g E (stepState g E X (gueBlock W 1 ω 0)) +
      A * ‖corrM g E (stepState g E X (gueBlock W 1 ω 0))‖ ^ 2) (μ W 1) :=
    iL.add (iM.const_mul A)
  rw [integral_add iLM (iF.const_mul B), integral_add iL (iM.const_mul A),
    integral_const_mul, integral_const_mul]

/-- `P_g Q = -g⁻² Re[κ P_g f₁]` with `κ = h²/(1 + e^{-2iθ})`, for `Q` of Lemma 11.3
[uvg:lem:positive]. -/
private lemma lp_transOp_linCorr {W : ℕ} {g E : ℝ} {X : State W} (hX : IsState X) :
    transOp g E (linCorr g E) X = -(1 / g ^ 2) *
      ((((normalH E ^ 2 : ℝ) : ℂ) / (1 + normalPhase E)) * transOp g E (obsF 1) X).re := by
  have iF : Integrable (fun ω : Ω W 1 => obsF 1 (stepState g E X (gueBlock W 1 ω 0)))
      (μ W 1) :=
    lp_integrable_of_bdd (contDiff_obsF_stepState g E hX 1).continuous (B := 1) fun ω =>
      norm_obsF_le_one 1 (lp_isState_step g E hX ω)
  unfold transOp linCorr
  rw [integral_const_mul]
  congr 1
  have h1 : ∫ ω : Ω W 1, ((((normalH E ^ 2 : ℝ) : ℂ) / (1 + normalPhase E)) *
      obsF 1 (stepState g E X (gueBlock W 1 ω 0))).re ∂(μ W 1) =
      (∫ ω : Ω W 1, (((normalH E ^ 2 : ℝ) : ℂ) / (1 + normalPhase E)) *
      obsF 1 (stepState g E X (gueBlock W 1 ω 0)) ∂(μ W 1)).re := integral_re (iF.const_mul _)
  rw [h1, integral_const_mul]

/-! ### The drift of the linear corrector, from (11.21) [uvg:eq:fmean] -/

private lemma lp_norm_bOdd_le {W : ℕ} {X : State W} (hX : IsState X) : ‖bOdd X‖ ≤ 8 := by
  have m1 := norm_obsM_le_one 1 hX
  have m2 := norm_obsM_le_one 2 hX
  have m3 := norm_obsM_le_one (-1) hX
  have f1 := norm_obsF_le_one 1 hX
  have f2 := norm_obsF_le_one 2 hX
  have f3 := norm_obsF_le_one (-1) hX
  have e0 : ‖(3 : ℂ) + obsM 2 X‖ ≤ 4 := by
    calc ‖(3 : ℂ) + obsM 2 X‖ ≤ ‖(3 : ℂ)‖ + ‖obsM 2 X‖ := norm_add_le _ _
      _ ≤ 3 + 1 := by rw [Complex.norm_ofNat]; linarith
      _ = 4 := by norm_num
  have e1 : ‖(3 + obsM 2 X) * obsF 1 X‖ ≤ 4 := by
    rw [norm_mul]; nlinarith [norm_nonneg (obsF 1 X), norm_nonneg ((3 : ℂ) + obsM 2 X)]
  have e2 : ‖2 * obsM 1 X * obsF 2 X‖ ≤ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    nlinarith [norm_nonneg (obsF 2 X), norm_nonneg (obsM 1 X)]
  have e3 : ‖obsF 1 X * (obsM 1 X * obsF 1 X + obsM (-1) X * obsF (-1) X)‖ ≤ 2 := by
    rw [norm_mul]
    have : ‖obsM 1 X * obsF 1 X + obsM (-1) X * obsF (-1) X‖ ≤ 2 := by
      calc _ ≤ ‖obsM 1 X * obsF 1 X‖ + ‖obsM (-1) X * obsF (-1) X‖ := norm_add_le _ _
        _ ≤ 1 + 1 := by
          rw [norm_mul, norm_mul]
          have := lp_mul_le_one m1 f1
          have := lp_mul_le_one m3 f3
          linarith
        _ = 2 := by norm_num
    nlinarith [norm_nonneg (obsF 1 X),
      norm_nonneg (obsM 1 X * obsF 1 X + obsM (-1) X * obsF (-1) X)]
  unfold bOdd
  calc _ ≤ ‖(3 + obsM 2 X) * obsF 1 X + 2 * obsM 1 X * obsF 2 X‖ +
        ‖obsF 1 X * (obsM 1 X * obsF 1 X + obsM (-1) X * obsF (-1) X)‖ := norm_sub_le _ _
    _ ≤ (‖(3 + obsM 2 X) * obsF 1 X‖ + ‖2 * obsM 1 X * obsF 2 X‖) +
        ‖obsF 1 X * (obsM 1 X * obsF 1 X + obsM (-1) X * obsF (-1) X)‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ 8 := by linarith

private lemma lp_norm_bEven_le {W : ℕ} {X : State W} (hX : IsState X) : ‖bEven X‖ ≤ 8 := by
  have m1 := norm_obsM_le_one 1 hX
  have f1 := norm_obsF_le_one 1 hX
  have f2 := norm_obsF_le_one 2 hX
  have f3 := norm_obsF_le_one (-1) hX
  have e1 : ‖4 * obsM 1 X * obsF 1 X‖ ≤ 4 := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have := lp_mul_le_one m1 f1
    linarith
  have e2 : ‖2 * obsF 2 X‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_ofNat]; linarith
  have e3 : ‖obsF 1 X ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) f1
  have e4 : ‖obsF 1 X * obsF (-1) X‖ ≤ 1 := by
    rw [norm_mul]; exact lp_mul_le_one f1 f3
  unfold bEven
  calc _ ≤ ‖4 * obsM 1 X * obsF 1 X + 2 * obsF 2 X - obsF 1 X ^ 2‖ +
        ‖obsF 1 X * obsF (-1) X‖ := norm_sub_le _ _
    _ ≤ ‖4 * obsM 1 X * obsF 1 X + 2 * obsF 2 X‖ + ‖obsF 1 X ^ 2‖ +
        ‖obsF 1 X * obsF (-1) X‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ (‖4 * obsM 1 X * obsF 1 X‖ + ‖2 * obsF 2 X‖) + ‖obsF 1 X ^ 2‖ +
        ‖obsF 1 X * obsF (-1) X‖ := by gcongr; exact norm_add_le _ _
    _ ≤ 8 := by linarith

/-- The remainder `ρ = P_g f₁ + e^{-2iθ} f₁` of (11.21) [uvg:eq:fmean] is `O(g⁻²)`. -/
private lemma lp_rho_le {E₀ : ℝ} (hE₀ : E₀ < 2) {W : ℕ} (hW : 1 ≤ W) {g E : ℝ} (hg : 1 ≤ g)
    (hE : |E| ≤ E₀) {X : State W} (hX : IsState X) {K₅ : ℝ} (hK₅ : 0 ≤ K₅)
    (h5 : ‖transOp g E (obsF 1) X - (-normalPhase E * obsF 1 X + normalPhase E *
      ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (bOdd X + bEven X))‖ ≤
        K₅ * (1 / g ^ 4 + 1 / (g ^ 2 * W))) :
    ‖transOp g E (obsF 1) X + normalPhase E * obsF 1 X‖ ≤
      (16 * lpH E₀ ^ 2 + 2 * K₅) * (1 / g ^ 2) := by
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have hg0 : 0 < g := by linarith
  have hw : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg
  have ht : 1 / g ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hg2
  have ht0 : 0 ≤ 1 / g ^ 2 := by positivity
  have hh := lp_normalH_pos hE'
  have hhH : normalH E ^ 2 ≤ lpH E₀ ^ 2 :=
    pow_le_pow_left₀ hh.le (lp_normalH_le hE₀ hE) 2
  have hB : ‖bOdd X + bEven X‖ ≤ 16 :=
    (norm_add_le _ _).trans (by linarith [lp_norm_bOdd_le hX, lp_norm_bEven_le hX])
  have h1 : 1 / g ^ 4 + 1 / (g ^ 2 * W) ≤ 2 * (1 / g ^ 2) := by
    have a1 : 1 / g ^ 4 ≤ 1 / g ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have a2 : 1 / (g ^ 2 * W) ≤ 1 / g ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    linarith
  have h2 : ‖normalPhase E * ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (bOdd X + bEven X)‖ ≤
      lpH E₀ ^ 2 * (1 / g ^ 2) * 16 := by
    rw [norm_mul, norm_mul, lp_norm_normalPhase, one_mul, lp_norm_q hE']
    have : normalH E ^ 2 / g ^ 2 ≤ lpH E₀ ^ 2 * (1 / g ^ 2) := by
      rw [div_eq_mul_one_div]; gcongr
    have h0 : 0 ≤ normalH E ^ 2 / g ^ 2 := by positivity
    nlinarith [norm_nonneg (bOdd X + bEven X)]
  have key : transOp g E (obsF 1) X + normalPhase E * obsF 1 X =
      (transOp g E (obsF 1) X - (-normalPhase E * obsF 1 X + normalPhase E *
        ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (bOdd X + bEven X))) +
        normalPhase E * ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (bOdd X + bEven X) := by ring
  rw [key]
  calc _ ≤ ‖transOp g E (obsF 1) X - (-normalPhase E * obsF 1 X + normalPhase E *
        ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (bOdd X + bEven X))‖ +
        ‖normalPhase E * ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (bOdd X + bEven X)‖ := norm_add_le _ _
    _ ≤ K₅ * (2 * (1 / g ^ 2)) + lpH E₀ ^ 2 * (1 / g ^ 2) * 16 :=
        add_le_add (h5.trans (mul_le_mul_of_nonneg_left h1 hK₅)) h2
    _ = _ := by ring

/-- `(P_g - I) Q = h² g⁻² Re f₁ + O(g⁻⁴)` (Lemma 11.3 [uvg:lem:positive]). -/
private lemma lp_transOp_sub_linCorr {E₀ : ℝ} (hE₀ : E₀ < 2) {W : ℕ} {g E : ℝ} (hg : 1 ≤ g)
    (hE : |E| ≤ E₀) {X : State W} (hX : IsState X) {c : ℝ}
    (hρ : ‖transOp g E (obsF 1) X + normalPhase E * obsF 1 X‖ ≤ c * (1 / g ^ 2)) :
    |transOp g E (linCorr g E) X - linCorr g E X - normalH E ^ 2 * (1 / g ^ 2) * (obsF 1 X).re| ≤
      lpH E₀ ^ 3 * c * (1 / g ^ 2) ^ 2 := by
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have hh := lp_normalH_pos hE'
  have ht0 : 0 ≤ 1 / g ^ 2 := by positivity
  set κ : ℂ := ((normalH E ^ 2 : ℝ) : ℂ) / (1 + normalPhase E) with hκ
  set ρ : ℂ := transOp g E (obsF 1) X + normalPhase E * obsF 1 X with hρdef
  have hne : (1 + normalPhase E) ≠ 0 := norm_pos_iff.mp (by rw [lp_norm_one_add hE']; positivity)
  have hk : κ * (1 + normalPhase E) = ((normalH E ^ 2 : ℝ) : ℂ) := div_mul_cancel₀ _ hne
  have hP : transOp g E (obsF 1) X = ρ - normalPhase E * obsF 1 X := by rw [hρdef]; ring
  have key : κ * transOp g E (obsF 1) X - κ * obsF 1 X =
      κ * ρ - ((normalH E ^ 2 : ℝ) : ℂ) * obsF 1 X := by
    rw [hP]; linear_combination (-(obsF 1 X)) * hk
  have hre : (κ * transOp g E (obsF 1) X).re - (κ * obsF 1 X).re =
      (κ * ρ).re - normalH E ^ 2 * (obsF 1 X).re := by
    have := congrArg Complex.re key
    rw [Complex.sub_re, Complex.sub_re, Complex.re_ofReal_mul] at this
    exact this
  have hQ : transOp g E (linCorr g E) X - linCorr g E X - normalH E ^ 2 * (1 / g ^ 2) *
      (obsF 1 X).re = -(1 / g ^ 2) * (κ * ρ).re := by
    rw [lp_transOp_linCorr hX]
    unfold linCorr
    rw [← hκ]
    linear_combination (-(1 / g ^ 2)) * hre
  rw [hQ, abs_mul, abs_neg, abs_of_nonneg ht0]
  have h1 : |(κ * ρ).re| ≤ lpH E₀ ^ 3 * (c * (1 / g ^ 2)) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, hκ, lp_norm_kappa hE']
    have h3 : normalH E ^ 3 ≤ lpH E₀ ^ 3 :=
      pow_le_pow_left₀ hh.le (lp_normalH_le hE₀ hE) 3
    exact mul_le_mul h3 hρ (norm_nonneg _) (pow_nonneg (lpH_nonneg E₀) 3)
  calc 1 / g ^ 2 * |(κ * ρ).re| ≤ 1 / g ^ 2 * (lpH E₀ ^ 3 * (c * (1 / g ^ 2))) :=
        mul_le_mul_of_nonneg_left h1 ht0
    _ = _ := by ring

/-! ### The drift inequality (11.23) [uvg:eq:positive] -/

/-- The final inequality of (11.23) [uvg:eq:positive] with `t = g⁻²` and `u = W⁻¹`: the four
negative terms of the bracket are each at most `u/64`, which leaves `u/16`. -/
private lemma lp_assemble {t u h2 K₁ c₄ Kd Cs A B C Ke a ε x y μ2 φ2 rf rmf rf2 I PQ Q0 PM PF : ℝ}
    (ht : 0 < t) (hu : 0 < u) (htu : t * Cs ^ 2 ≤ u) (hCs : 1 ≤ Cs) (hKd : 64 * Kd ≤ Cs)
    (hKd' : K₁ + c₄ = Kd) (ha : 0 < a) (hC : 0 < C) (hA : 0 < A) (hB : 0 < B) (hKe : 0 ≤ Ke)
    (hAa : A * a = Ke + 1 + C * B) (hBC : 64 * C * B = 1) (hε : ε = a * B / 2)
    (hW1 : 64 * C * A * u ≤ 1) (hW2 : 64 * (C * (A + B) + Ke) * u ≤ 1) (h2q : 1 / 4 ≤ h2)
    (hμ2 : 0 ≤ μ2) (hφ2 : 0 ≤ φ2)
    (hI : h2 * t * (u / 2 + rf + rmf - u / 2 * rf2) - K₁ * t ^ 2 ≤ I)
    (hQ : PQ - Q0 ≤ h2 * t * rf + c₄ * t ^ 2)
    (hPM : PM - μ2 ≤ -(a * t) * μ2 + C * t * (u ^ 2 + t ^ 2))
    (hPF : PF - φ2 ≤ -(a * t) * φ2 + C * t * μ2 + C * t * (u + t ^ 2))
    (hY : h2 * (x * y) + h2 * y ^ 2 * u / 2 ≤ Ke * μ2 + ε * φ2 + Ke * t ^ 2)
    (hrmf : -(x * y) ≤ rmf) (hrf2 : rf2 ≤ y ^ 2) :
    1 / 16 * (t * u) ≤ I - ((PQ + A * PM + B * PF) - (Q0 + A * μ2 + B * φ2)) := by
  have hCs2 : 1 ≤ Cs ^ 2 := one_le_pow₀ hCs
  have htu' : t ≤ u := by
    have : t ≤ t * Cs ^ 2 := le_mul_of_one_le_right ht.le hCs2
    linarith
  have b1 : Kd * t ≤ u / 64 := by
    have h1 : 64 * Kd ≤ Cs ^ 2 := by nlinarith
    have : 64 * Kd * t ≤ Cs ^ 2 * t := mul_le_mul_of_nonneg_right h1 ht.le
    linarith
  have b2 : A * C * u ^ 2 ≤ u / 64 := by
    have := mul_le_mul_of_nonneg_right hW1 hu.le
    linarith
  have b3 : B * C * u = u / 64 := by
    have : B * C = 1 / 64 := by linarith
    rw [this]; ring
  have b4 : (A * C + B * C + Ke) * t ^ 2 ≤ u / 64 := by
    have h1 : t ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ ht.le htu' 2
    have h0 : 0 ≤ A * C + B * C + Ke := by positivity
    have h3 : (A * C + B * C + Ke) * t ^ 2 ≤ (A * C + B * C + Ke) * u ^ 2 :=
      mul_le_mul_of_nonneg_left h1 h0
    have h4 := mul_le_mul_of_nonneg_right hW2 hu.le
    linarith
  have b5 : u / 8 ≤ h2 * u / 2 := by
    have := mul_le_mul_of_nonneg_right h2q hu.le
    linarith
  have br : 1 / 16 * u ≤ h2 * u / 2 - Kd * t - A * C * u ^ 2 - B * C * u -
      (A * C + B * C + Ke) * t ^ 2 := by linarith
  have F1 : -(h2 * t) * (x * y) ≤ h2 * t * rmf := by
    have := mul_le_mul_of_nonneg_left hrmf (by positivity : 0 ≤ h2 * t)
    linarith
  have hh2 : 0 ≤ h2 := by linarith
  have F2 : h2 * t * (u / 2) * rf2 ≤ h2 * t * (u / 2) * y ^ 2 :=
    mul_le_mul_of_nonneg_left hrf2 (by positivity)
  have F3 := mul_le_mul_of_nonneg_left hY ht.le
  have F4 := mul_le_mul_of_nonneg_left hPM hA.le
  have F5 := mul_le_mul_of_nonneg_left hPF hB.le
  have F6 := mul_le_mul_of_nonneg_left br ht.le
  have F7 : 0 ≤ t * μ2 * (A * a - Ke - B * C) := by
    have : A * a - Ke - B * C = 1 := by linarith
    rw [this]; positivity
  have F8 : 0 ≤ t * φ2 * (B * a - ε) := by
    have : B * a - ε = B * a / 2 := by rw [hε]; ring
    rw [this]; positivity
  have F9 : Kd * t ^ 2 = K₁ * t ^ 2 + c₄ * t ^ 2 := by rw [← hKd']; ring
  linarith [F1, F2, F3, F4, F5, F6, F7, F8, F9]

/-- Lemma 11.3 [uvg:lem:positive], (11.23) [uvg:eq:positive]: there are `A, B, a₀, C_*, W₀`
such that `𝒬` is bounded independently of `W, g` and
`P_g c - (P_g - I)𝒬 ≥ a₀ g⁻²/W` for `W ≥ W₀`, `g ≥ C_* √W`. -/
theorem large_positive {E₀ : ℝ} (hE₀ : E₀ < 2) :
    ∃ A B a₀ Cs K : ℝ, 0 < A ∧ 0 < B ∧ 0 < a₀ ∧ 1 ≤ Cs ∧ 0 < K ∧
      (∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ → ∀ X : State W, IsState X →
        |driftCorr g E A B X| ≤ K) ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, Cs * Real.sqrt W ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
        ∀ X : State W, IsState X →
          a₀ / (g ^ 2 * W) ≤
            incMean g E X - (transOp g E (driftCorr g E A B) X - driftCorr g E A B X) := by
  obtain ⟨a, C, ha, hC, hdr⟩ := large_drifts hE₀
  obtain ⟨K₁, hK₁, hexp⟩ := incMean_expansion hE₀
  obtain ⟨K₅, hK₅, hF1⟩ := transOp_obsF_one hE₀
  have hH0 : 0 ≤ lpH E₀ := lpH_nonneg E₀
  set H : ℝ := lpH E₀ with hH
  set c₃ : ℝ := 16 * H ^ 2 + 2 * K₅ with hc₃
  set Kd : ℝ := K₁ + H ^ 3 * c₃ with hKd
  set B : ℝ := 1 / (64 * C) with hB
  have hB0 : 0 < B := by rw [hB]; positivity
  set ε : ℝ := a * B / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  set Ke : ℝ := lpKe (H ^ 2) (4 * H ^ 3) (8 * H ^ 3) ε with hKe
  have hKe0 : 0 ≤ Ke :=
    lpKe_nonneg (by positivity) (by positivity) (by positivity) hε0
  set A : ℝ := (Ke + 1 + C * B) / a with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  have hc₃0 : 0 ≤ c₃ := by rw [hc₃]; positivity
  have hKd0 : 0 < Kd := by rw [hKd]; positivity
  set Cs : ℝ := 1 + 64 * Kd with hCs
  have hCs1 : 1 ≤ Cs := by rw [hCs]; linarith
  set Tw : ℝ := 1 + 4 * H ^ 2 / ε + 64 * C * A + 64 * (C * (A + B) + Ke) with hTw
  set K : ℝ := H ^ 3 + A * (1 + 4 * H ^ 3) ^ 2 + B * (1 + 8 * H ^ 3) ^ 2 + 1 with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  refine ⟨A, B, 1 / 16, Cs, K, hA0, hB0, by norm_num, hCs1, hK0, ?_, ⌈Tw⌉₊, ?_⟩
  · -- `𝒬` is bounded
    intro W hW g hg E hE X hX
    have hQ := lp_abs_linCorr_le hE₀ hg hE hX
    obtain ⟨hM, hF⟩ := lp_norm_corr_le hE₀ hg hE hX
    have hM2 : ‖corrM g E X‖ ^ 2 ≤ (1 + 4 * H ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hM 2
    have hF2 : ‖corrF g E X‖ ^ 2 ≤ (1 + 8 * H ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hF 2
    have h1 : |A * ‖corrM g E X‖ ^ 2| ≤ A * (1 + 4 * H ^ 3) ^ 2 := by
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hM2 hA0.le
    have h2 : |B * ‖corrF g E X‖ ^ 2| ≤ B * (1 + 8 * H ^ 3) ^ 2 := by
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hF2 hB0.le
    unfold driftCorr
    calc |linCorr g E X + A * ‖corrM g E X‖ ^ 2 + B * ‖corrF g E X‖ ^ 2|
        ≤ |linCorr g E X + A * ‖corrM g E X‖ ^ 2| + |B * ‖corrF g E X‖ ^ 2| := abs_add_le _ _
      _ ≤ (|linCorr g E X| + |A * ‖corrM g E X‖ ^ 2|) + |B * ‖corrF g E X‖ ^ 2| := by
          gcongr; exact abs_add_le _ _
      _ ≤ K := by rw [hK]; linarith
  · -- the drift inequality (11.23) [uvg:eq:positive]
    intro W hW g hgCs E hE X hX
    have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
    have hTwW : Tw ≤ (W : ℝ) := (Nat.le_ceil Tw).trans (by exact_mod_cast hW)
    have hn1 : 0 ≤ 4 * H ^ 2 / ε := by positivity
    have hn2 : 0 ≤ C * (A + B) + Ke := by positivity
    have hn3 : 0 ≤ C * A := by positivity
    have hrest : 0 ≤ 4 * H ^ 2 / ε + 64 * C * A + 64 * (C * (A + B) + Ke) := by positivity
    have hw1 : (1 : ℝ) ≤ W := by rw [hTw] at hTwW; linarith
    have hW1 : 1 ≤ W := by exact_mod_cast hw1
    have hw0 : 0 < (W : ℝ) := by linarith
    have hsq1 : 1 ≤ Real.sqrt W := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hw1
    have hg1 : 1 ≤ g := by nlinarith
    have hg0 : 0 < g := by linarith
    have hg2 : Cs ^ 2 * W ≤ g ^ 2 := by
      have : (Cs * Real.sqrt W) ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ (by positivity) hgCs 2
      rwa [mul_pow, Real.sq_sqrt hw0.le] at this
    have ht0 : 0 < 1 / g ^ 2 := by positivity
    have hu0 : 0 < 1 / (W : ℝ) := by positivity
    have htu : 1 / g ^ 2 * Cs ^ 2 ≤ 1 / (W : ℝ) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hw0]
      linarith
    have hW1' : 64 * C * A * (1 / (W : ℝ)) ≤ 1 := by
      rw [mul_one_div, div_le_one hw0]; rw [hTw] at hTwW; linarith
    have hW2' : 64 * (C * (A + B) + Ke) * (1 / (W : ℝ)) ≤ 1 := by
      rw [mul_one_div, div_le_one hw0]; rw [hTw] at hTwW; linarith
    have hPu : 4 * H ^ 2 * (1 / (W : ℝ)) ≤ ε := by
      rw [mul_one_div, div_le_iff₀ hw0]
      have : 4 * H ^ 2 / ε ≤ W := by rw [hTw] at hTwW; linarith
      rw [div_le_iff₀ hε0] at this
      linarith
    have h2q : 1 / 4 ≤ normalH E ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) (lp_half_le_normalH hE') 2
      linarith
    have hh := lp_normalH_pos hE'
    have hh2H : normalH E ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ hh.le (lp_normalH_le hE₀ hE) 2
    -- the expansion of `P c` (11.12) [lg:eq:c2]
    have hI : normalH E ^ 2 * (1 / g ^ 2) * (1 / (W : ℝ) / 2 + (obsF 1 X).re +
        (obsM 1 X * obsF 1 X).re - 1 / (W : ℝ) / 2 * (obsF 1 X ^ 2).re) -
          K₁ * (1 / g ^ 2) ^ 2 ≤ incMean g E X := by
      have h := (abs_le.mp (hexp W hW1 g hg1 E hE X hX)).1
      have e1 : normalH E ^ 2 / g ^ 2 * (1 / (2 * (W : ℝ)) + (obsF 1 X).re +
          (obsM 1 X * obsF 1 X).re - 1 / (2 * (W : ℝ)) * (obsF 1 X ^ 2).re) =
          normalH E ^ 2 * (1 / g ^ 2) * (1 / (W : ℝ) / 2 + (obsF 1 X).re +
        (obsM 1 X * obsF 1 X).re - 1 / (W : ℝ) / 2 * (obsF 1 X ^ 2).re) := by
        field_simp
      have e2 : K₁ / g ^ 4 = K₁ * (1 / g ^ 2) ^ 2 := by field_simp
      rw [e1, e2] at h
      linarith
    -- `(P - I) Q`
    have hρ := lp_rho_le hE₀ hW1 hg1 hE hX hK₅.le (hF1 W hW1 g hg1 E hE X hX)
    have hQ := (abs_le.mp (lp_transOp_sub_linCorr hE₀ hg1 hE hX hρ)).2
    -- the drifts of `|M|²` and `|F|²` (11.18) [uvg:eq:Mdrift]–(11.19) [uvg:eq:Fdrift]
    obtain ⟨hdM, hdF⟩ := hdr W hW1 g hg1 E hE X hX
    have hPM : transOp g E (fun Y => ‖corrM g E Y‖ ^ 2) X - ‖corrM g E X‖ ^ 2 ≤
        -(a * (1 / g ^ 2)) * ‖corrM g E X‖ ^ 2 +
          C * (1 / g ^ 2) * ((1 / (W : ℝ)) ^ 2 + (1 / g ^ 2) ^ 2) := by
      refine hdM.trans (le_of_eq ?_)
      field_simp
    have hPF : transOp g E (fun Y => ‖corrF g E Y‖ ^ 2) X - ‖corrF g E X‖ ^ 2 ≤
        -(a * (1 / g ^ 2)) * ‖corrF g E X‖ ^ 2 + C * (1 / g ^ 2) * ‖corrM g E X‖ ^ 2 +
          C * (1 / g ^ 2) * (1 / (W : ℝ) + (1 / g ^ 2) ^ 2) := by
      refine hdF.trans (le_of_eq ?_)
      field_simp
    -- the Young step
    have hmM := lp_corrM_sub_le hE₀ (g := g) hE hX
    have hfF := lp_corrF_sub_le hE₀ (g := g) hE hX
    have hx : ‖obsM 1 X‖ ≤ ‖corrM g E X‖ + 4 * H ^ 3 * (1 / g ^ 2) := by
      have := norm_sub_norm_le (obsM 1 X) (corrM g E X)
      rw [norm_sub_rev] at this
      linarith
    have hy : ‖obsF 1 X‖ ≤ ‖corrF g E X‖ + 8 * H ^ 3 * (1 / g ^ 2) := by
      have := norm_sub_norm_le (obsF 1 X) (corrF g E X)
      rw [norm_sub_rev] at this
      linarith
    have hY := lp_young_alg (P := H ^ 2) (c₁ := 4 * H ^ 3) (c₂ := 8 * H ^ 3) (ε := ε)
      (t := 1 / g ^ 2) (u := 1 / (W : ℝ)) (h2 := normalH E ^ 2) (x := ‖obsM 1 X‖)
      (y := ‖obsF 1 X‖) (μ := ‖corrM g E X‖) (φ := ‖corrF g E X‖) (by positivity)
      (by positivity) (by positivity) hε0 ht0.le hu0.le hPu hh2H (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) hx hy
    have hrmf : -(‖obsM 1 X‖ * ‖obsF 1 X‖) ≤ (obsM 1 X * obsF 1 X).re := by
      have := Complex.abs_re_le_norm (obsM 1 X * obsF 1 X)
      rw [norm_mul] at this
      exact neg_le_of_abs_le this
    have hrf2 : (obsF 1 X ^ 2).re ≤ ‖obsF 1 X‖ ^ 2 := by
      have := Complex.re_le_norm (obsF 1 X ^ 2)
      rwa [norm_pow] at this
    have key := lp_assemble (t := 1 / g ^ 2) (u := 1 / (W : ℝ)) (h2 := normalH E ^ 2)
      (K₁ := K₁) (c₄ := H ^ 3 * c₃) (Kd := Kd) (Cs := Cs) (A := A) (B := B) (C := C)
      (Ke := Ke) (a := a) (ε := ε) (x := ‖obsM 1 X‖) (y := ‖obsF 1 X‖)
      (μ2 := ‖corrM g E X‖ ^ 2) (φ2 := ‖corrF g E X‖ ^ 2) (rf := (obsF 1 X).re)
      (rmf := (obsM 1 X * obsF 1 X).re) (rf2 := (obsF 1 X ^ 2).re) (I := incMean g E X)
      (PQ := transOp g E (linCorr g E) X) (Q0 := linCorr g E X)
      (PM := transOp g E (fun Y => ‖corrM g E Y‖ ^ 2) X)
      (PF := transOp g E (fun Y => ‖corrF g E Y‖ ^ 2) X) ht0 hu0 htu hCs1
      (by rw [hCs]; linarith) rfl ha hC
      hA0 hB0 hKe0 (by rw [hA]; field_simp) (by rw [hB]; field_simp) hε hW1' hW2' h2q
      (by positivity) (by positivity) hI (by linarith) hPM hPF hY hrmf hrf2
    rw [lp_transOp_driftCorr hE₀ hg1 hE hX A B]
    have hdc : driftCorr g E A B X =
        linCorr g E X + A * ‖corrM g E X‖ ^ 2 + B * ‖corrF g E X‖ ^ 2 := rfl
    rw [hdc]
    calc 1 / 16 / (g ^ 2 * W) = 1 / 16 * (1 / g ^ 2 * (1 / (W : ℝ))) := by field_simp
      _ ≤ _ := key

end LSBA
