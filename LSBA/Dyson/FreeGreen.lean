import LSBA.Dyson.Scalar

/-!
# Free Green functions

The free transform in closed form, the decay factor and the free row on the cycle, Lemma A.1
[da:lem:free-green], (A.1) [bl:eq:physical]–(A.5) [bl:eq:free]; and the quartic form of (1.9)
[eq:dyson].
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- The root of `w² - 4b²` with positive imaginary part on `ℂ_+`: `i·(-(w² - 4b²))^{1/2}`. -/
def freeS (b : ℝ) (w : ℂ) : ℂ := I * (-(w ^ 2 - 4 * (b : ℂ) ^ 2)) ^ (2⁻¹ : ℂ)

/-- Decay factor `ρ(w) = 2b / (w + s(w))`, (A.4) [da:eq:free-decay-factor]. -/
def freeRho (b : ℝ) (w : ℂ) : ℂ := 2 * b / (w + freeS b w)

theorem freeS_sq (b : ℝ) (w : ℂ) : freeS b w ^ 2 = w ^ 2 - 4 * (b : ℂ) ^ 2 := by
  unfold freeS
  rw [mul_pow, Complex.I_sq]
  have h := Complex.cpow_ofNat_inv_pow (-(w ^ 2 - 4 * (b : ℂ) ^ 2)) 2
  rw [h]
  ring

theorem freeS_im_pos (b : ℝ) (w : ℂ) (hw : 0 < w.im) : 0 < (freeS b w).im := by
  unfold freeS
  rw [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
    Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  set ζ : ℂ := -(w ^ 2 - 4 * (b : ℂ) ^ 2) with hζ
  have hre : ζ.re = 4 * b ^ 2 - (w.re ^ 2 - w.im ^ 2) := by
    simp [hζ, sq]
  have him : ζ.im = -(2 * w.re * w.im) := by
    simp [hζ, sq]; ring
  have : 0 < ‖ζ‖ + ζ.re := by
    by_cases h0 : w.re = 0
    · have h1 : 0 < ζ.re := by rw [hre, h0]; nlinarith [sq_nonneg b]
      have := Complex.re_le_norm ζ
      linarith
    · have h2 : ζ.im ≠ 0 := by
        rw [him]
        have : w.re * w.im ≠ 0 := mul_ne_zero h0 hw.ne'
        intro h; apply this; linarith
      have := Complex.abs_re_lt_norm.mpr h2
      have := neg_abs_le ζ.re
      linarith
  linarith

/-! ### Algebra of `s` and `ρ` -/

private lemma add_freeS_im_pos (b : ℝ) {w : ℂ} (hw : 0 < w.im) : 0 < (w + freeS b w).im := by
  rw [Complex.add_im]
  linarith [freeS_im_pos b w hw]

private lemma add_freeS_ne_zero (b : ℝ) {w : ℂ} (hw : 0 < w.im) : w + freeS b w ≠ 0 := by
  intro h
  have := add_freeS_im_pos b hw
  rw [h] at this
  simp at this

private lemma freeS_ne_zero (b : ℝ) {w : ℂ} (hw : 0 < w.im) : freeS b w ≠ 0 := by
  intro h
  have := freeS_im_pos b w hw
  rw [h] at this
  simp at this

/-- `ρ (w + s) = 2b`, from the definition of `ρ`. -/
private lemma freeRho_mul (b : ℝ) {w : ℂ} (hw : 0 < w.im) :
    freeRho b w * (w + freeS b w) = 2 * b := by
  unfold freeRho
  field_simp [add_freeS_ne_zero b hw]

/-- `w - s = 2bρ`. -/
private lemma sub_freeS_eq (b : ℝ) {w : ℂ} (hw : 0 < w.im) :
    w - freeS b w = 2 * b * freeRho b w := by
  have h1 := freeRho_mul b hw
  have h2 := freeS_sq b w
  have h3 : (w - freeS b w) * (w + freeS b w) = (2 * b * freeRho b w) * (w + freeS b w) := by
    linear_combination (-1 : ℂ) * h2 - (2 * (b : ℂ)) * h1
  exact mul_right_cancel₀ (add_freeS_ne_zero b hw) h3

/-- `ρ w = b (1 + ρ²)`. -/
private lemma freeRho_w (b : ℝ) {w : ℂ} (hw : 0 < w.im) :
    freeRho b w * w = b * (1 + freeRho b w ^ 2) := by
  have h1 := freeRho_mul b hw
  have h2 := sub_freeS_eq b hw
  linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * freeRho b w * h2

/-- `ρ s = b (1 - ρ²)`. -/
private lemma freeRho_s (b : ℝ) {w : ℂ} (hw : 0 < w.im) :
    freeRho b w * freeS b w = b * (1 - freeRho b w ^ 2) := by
  have h1 := freeRho_mul b hw
  have h2 := sub_freeS_eq b hw
  linear_combination (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * freeRho b w * h2

/-- (A.4) [da:eq:free-decay-factor]: `|ρ(w)| < 1`. -/
theorem norm_freeRho_lt_one (b : ℝ) (w : ℂ) (hw : 0 < w.im) : ‖freeRho b w‖ < 1 := by
  by_cases hb : b = 0
  · subst hb
    simp [freeRho]
  set ρ := freeRho b w with hρ
  set s := freeS b w with hs
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  have hρ0 : ρ ≠ 0 := by
    intro h
    have := freeRho_mul b hw
    rw [← hρ, h, zero_mul] at this
    exact (mul_ne_zero two_ne_zero hb') this.symm
  have hW : w = b * (ρ + ρ⁻¹) := by
    have := freeRho_w b hw
    rw [← hρ] at this
    field_simp
    linear_combination this
  have hS : s = b * (ρ⁻¹ - ρ) := by
    have := freeRho_s b hw
    rw [← hρ, ← hs] at this
    field_simp
    linear_combination this
  have hr : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr hρ0
  set r := Complex.normSq ρ with hrdef
  have hwim : w.im = b * ρ.im * (1 - 1 / r) := by
    rw [hW, Complex.im_ofReal_mul, Complex.add_im, Complex.inv_im, ← hrdef]
    field_simp
    ring
  have hsim : s.im = -(b * ρ.im * (1 + 1 / r)) := by
    rw [hS, Complex.im_ofReal_mul, Complex.sub_im, Complex.inv_im, ← hrdef]
    field_simp
    ring
  have hs0 : 0 < s.im := freeS_im_pos b w hw
  have hlt : r < 1 := by
    by_contra hge'
    have hge := not_lt.mp hge'
    have h1 : 0 ≤ 1 - 1 / r := by
      rw [sub_nonneg, div_le_one hr]; exact hge
    have h2 : 0 < 1 + 1 / r := by positivity
    rw [hsim] at hs0
    rw [hwim] at hw
    nlinarith
  rw [← sq_lt_one_iff₀ (norm_nonneg _), Complex.sq_norm]
  exact hlt

/-! ### The average of `(1 - ρ e^{ip})⁻¹` -/

private lemma norm_mul_exp_lt {ρ : ℂ} (hρ : ‖ρ‖ < 1) (p : ℝ) : ‖ρ * Complex.exp (p * I)‖ < 1 := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact hρ

private lemma integral_exp_pow (n : ℕ) :
    ∫ p in (-π)..π, Complex.exp (p * I) ^ n =
      if n = 0 then ((2 * π : ℝ) : ℂ) else 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
    ring
  · have hn0 : n ≠ 0 := hn.ne'
    simp only [hn0, ↓reduceIte]
    have hc : ((n : ℂ) * I) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') Complex.I_ne_zero
    have := integral_exp_mul_complex (a := -π) (b := π) hc
    have e : ∀ p : ℝ, Complex.exp (p * I) ^ n = Complex.exp ((n : ℂ) * I * p) := by
      intro p
      rw [← Complex.exp_nat_mul]
      ring_nf
    simp_rw [e]
    rw [this]
    have h1 : Complex.exp ((n : ℂ) * I * π) = Complex.exp ((n : ℂ) * I * (-π : ℝ)) := by
      have h2 := Complex.exp_nat_mul_two_pi_mul_I n
      have h3 : Complex.exp ((n : ℂ) * I * π) =
          Complex.exp ((n : ℂ) * I * (-π : ℝ)) * Complex.exp (n * (2 * π * I)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [h3, h2, mul_one]
    rw [h1, sub_self, zero_div]

/-- `⟨(1 - ρ e^{ip})⁻¹⟩ = 1` for `‖ρ‖ < 1`, as the integral over `[-π, π]`. -/
private lemma integral_geom {ρ : ℂ} (hρ : ‖ρ‖ < 1) :
    ∫ p in (-π)..π, (1 - ρ * Complex.exp (p * I))⁻¹ = ((2 * π : ℝ) : ℂ) := by
  have hF : ∀ n : ℕ, ∫ p in (-π)..π, (ρ * Complex.exp (p * I)) ^ n =
      if n = 0 then ((2 * π : ℝ) : ℂ) else 0 := by
    intro n
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul, integral_exp_pow]
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  have hsum : HasSum (fun n : ℕ => ∫ p in (-π)..π, (ρ * Complex.exp (p * I)) ^ n)
      (∫ p in (-π)..π, (1 - ρ * Complex.exp (p * I))⁻¹) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => ‖ρ‖ ^ n)
      (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
    · exact (by fun_prop :
        Continuous fun p : ℝ => (ρ * Complex.exp (p * I)) ^ n).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun t _ => ?_)
      rw [norm_pow, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    · exact Filter.Eventually.of_forall (fun t _ => summable_geometric_of_lt_one (norm_nonneg _) hρ)
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall
        (fun t _ => hasSum_geometric_of_norm_lt_one (norm_mul_exp_lt hρ t))
  simp_rw [hF] at hsum
  exact hsum.unique (hasSum_ite_eq (0 : ℕ) ((2 * π : ℝ) : ℂ))

private lemma continuous_geom {ρ : ℂ} (hρ : ‖ρ‖ < 1) :
    Continuous fun p : ℝ => (1 - ρ * Complex.exp (p * I))⁻¹ := by
  refine Continuous.inv₀ (by fun_prop) (fun p => ?_)
  intro h
  have := norm_mul_exp_lt hρ p
  have h2 : ρ * Complex.exp (p * I) = 1 := by linear_combination -h
  rw [h2] at this
  simp at this

/-- Partial fractions: if `ρ w = b (1 + ρ²)` and `‖ρ‖ < 1`, then
`(2b cos p - w)⁻¹ = -ρ/(b (1 - ρ²)) · (J(p) + J(-p) - 1)` with `J(p) = (1 - ρ e^{ip})⁻¹`. -/
private lemma res_partial {b : ℝ} {w ρ : ℂ} (hb : (b : ℂ) ≠ 0) (hρ : ‖ρ‖ < 1)
    (hw : ρ * w = b * (1 + ρ ^ 2)) (hw' : 0 < w.im) (p : ℝ) :
    ((2 * b * Real.cos p : ℝ) - w : ℂ)⁻¹ =
      (-ρ / (b * (1 - ρ ^ 2))) *
        ((1 - ρ * Complex.exp (p * I))⁻¹ + (1 - ρ * Complex.exp ((-p : ℝ) * I))⁻¹ - 1) := by
  set E := Complex.exp (p * I) with hE
  set E' := Complex.exp ((-p : ℝ) * I) with hE'
  have hEE : E * E' = 1 := by
    rw [hE, hE', ← Complex.exp_add]
    push_cast
    ring_nf
    simp
  have hcos : ((2 * b * Real.cos p : ℝ) : ℂ) = b * (E + E') := by
    push_cast
    rw [hE, hE']
    have := Complex.two_cos (x := (p : ℂ))
    push_cast
    linear_combination (b : ℂ) * this
  have h1 := norm_mul_exp_lt hρ p
  have h2 := norm_mul_exp_lt hρ (-p)
  have hD1 : 1 - ρ * E ≠ 0 := by
    intro h
    have h3 : ρ * E = 1 := by linear_combination -h
    rw [← hE, h3] at h1
    simp at h1
  have hD2 : 1 - ρ * E' ≠ 0 := by
    intro h
    have h3 : ρ * E' = 1 := by linear_combination -h
    rw [← hE', h3] at h2
    simp at h2
  have hρ2 : 1 - ρ ^ 2 ≠ 0 := by
    intro h
    have h3 : ρ ^ 2 = 1 := by linear_combination -h
    have : ‖ρ‖ ^ 2 = 1 := by rw [← norm_pow, h3, norm_one]
    nlinarith [norm_nonneg ρ]
  have hX : ((2 * b * Real.cos p : ℝ) - w : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  apply inv_eq_of_mul_eq_one_right
  rw [hcos]
  have hD1' : 1 - E * ρ ≠ 0 := by rwa [mul_comm]
  have hD2' : 1 - E' * ρ ≠ 0 := by rwa [mul_comm]
  field_simp
  linear_combination (1 - ρ ^ 2 * (E * E')) * hw + (ρ ^ 2 * (b * ρ * (E + E') - 2 * b)) * hEE

/-- (A.1) [bl:eq:physical]: `f(w) = -1/√(w² - 4b²)`. -/
theorem freeT_eq (b : ℝ) (w : ℂ) (hw : 0 < w.im) : freeT b w = -(freeS b w)⁻¹ := by
  by_cases hb : b = 0
  · subst hb
    have hs : freeS 0 w = w := by
      have h1 := freeS_sq 0 w
      push_cast at h1
      have h2 : (freeS 0 w - w) * (freeS 0 w + w) = 0 := by
        linear_combination h1
      have h3 : freeS 0 w + w ≠ 0 := by
        rw [add_comm]; exact add_freeS_ne_zero 0 hw
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right h3)
    rw [hs]
    unfold freeT
    have hπ : (2 * π : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact mul_ne_zero two_ne_zero this
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
      intervalIntegral.integral_const, Complex.real_smul]
    rw [show ((π - -π : ℝ) : ℂ) = 2 * (π : ℂ) by push_cast; ring, ← mul_assoc,
      inv_mul_cancel₀ hπ, one_mul, inv_neg]
  · have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
    set ρ := freeRho b w with hρdef
    set s := freeS b w with hsdef
    have hρ : ‖ρ‖ < 1 := norm_freeRho_lt_one b w hw
    have hρw : ρ * w = b * (1 + ρ ^ 2) := freeRho_w b hw
    have hρs : ρ * s = b * (1 - ρ ^ 2) := freeRho_s b hw
    have hs0 : s ≠ 0 := freeS_ne_zero b hw
    have hρ0 : ρ ≠ 0 := by
      intro h
      have h3 : (b : ℂ) * (1 - ρ ^ 2) = 0 := by rw [← hρs, h]; ring
      rw [h] at h3
      have h4 : (b : ℂ) = 0 := by simpa using h3
      exact hb (Complex.ofReal_eq_zero.mp h4)
    have hρ2 : 1 - ρ ^ 2 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hρs
      exact mul_ne_zero hρ0 hs0 hρs
    have hcont := continuous_geom hρ
    have hcont' : Continuous fun p : ℝ => (1 - ρ * Complex.exp ((-p : ℝ) * I))⁻¹ := by
      have := hcont.comp continuous_neg
      exact this
    have hint : ∫ p in (-π)..π, ((2 * b * Real.cos p : ℝ) - w : ℂ)⁻¹ =
        (-ρ / (b * (1 - ρ ^ 2))) * (2 * π : ℝ) := by
      simp_rw [res_partial hb' hρ hρw hw]
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [intervalIntegral.integral_sub
        ((hcont.intervalIntegrable _ _).add (hcont'.intervalIntegrable _ _))
        intervalIntegrable_const,
        intervalIntegral.integral_add (hcont.intervalIntegrable _ _)
          (hcont'.intervalIntegrable _ _),
        integral_geom hρ]
      have hneg : ∫ p in (-π)..π, (1 - ρ * Complex.exp ((-p : ℝ) * I))⁻¹ =
          ∫ p in (-π)..π, (1 - ρ * Complex.exp (p * I))⁻¹ := by
        rw [intervalIntegral.integral_comp_neg (fun p : ℝ => (1 - ρ * Complex.exp (p * I))⁻¹)]
        simp
      rw [hneg, integral_geom hρ]
      simp
      ring
    unfold freeT
    rw [hint]
    have hπ : (2 * π : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact mul_ne_zero two_ne_zero this
    push_cast
    field_simp
    linear_combination (-1 : ℂ) * hρs

/-! ### The row on the cycle -/

/-- `ρ^L ≠ 1` for `‖ρ‖ < 1` and `L ≥ 1`. -/
private lemma one_sub_pow_ne_zero {ρ : ℂ} (hρ : ‖ρ‖ < 1) {L : ℕ} (hL : L ≠ 0) :
    1 - ρ ^ L ≠ 0 := by
  intro h
  have h1 : ρ ^ L = 1 := by linear_combination -h
  have h2 : ‖ρ‖ ^ L < 1 := pow_lt_one₀ (norm_nonneg _) hρ hL
  rw [← norm_pow, h1, norm_one] at h2
  exact lt_irrefl _ h2

/-- The profile `k ↦ f (ρ^k + ρ^{L-k}) / (1 - ρ^L)` of the row on `ℤ_L`, (A.5) [bl:eq:free]. -/
private def cycV (b : ℝ) (w : ℂ) (L k : ℕ) : ℂ :=
  freeT b w * (freeRho b w ^ k + freeRho b w ^ (L - k)) / (1 - freeRho b w ^ L)

private lemma cycV_L (b : ℝ) (w : ℂ) (L : ℕ) : cycV b w L L = cycV b w L 0 := by
  unfold cycV
  simp only [Nat.sub_self, Nat.sub_zero, pow_zero]
  rw [add_comm]

/-- The recurrence `b (V(d-1) + V(d+1)) = w V(d)` for `1 ≤ d` and `d + 1 ≤ L`. -/
private lemma cycV_rec_int (b : ℝ) {w : ℂ} (hw : 0 < w.im) (L d : ℕ) (hd : 1 ≤ d)
    (hd' : d + 1 ≤ L) :
    b * (cycV b w L (d - 1) + cycV b w L (d + 1)) - w * cycV b w L d = 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, L = e + n + 2 := ⟨L - e - 2, by omega⟩
  have hρw := freeRho_w b hw
  unfold cycV
  have e1 : e + n + 2 - (e + 1 - 1) = n + 2 := by omega
  have e2 : e + n + 2 - (e + 1 + 1) = n := by omega
  have e3 : e + n + 2 - (e + 1) = n + 1 := by omega
  rw [e1, e2, e3, Nat.add_sub_cancel]
  linear_combination ((1 - freeRho b w ^ (e + n + 2))⁻¹ *
    (-(freeT b w * (freeRho b w ^ e + freeRho b w ^ n)))) * hρw

/-- The recurrence at `d = 0`: `b (V(L-1) + V(1)) - w V(0) = 1`. -/
private lemma cycV_rec_zero (b : ℝ) {w : ℂ} (hw : 0 < w.im) (L : ℕ) (hL : 2 ≤ L) :
    b * (cycV b w L (L - 1) + cycV b w L 1) - w * cycV b w L 0 = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 2 := ⟨L - 2, by omega⟩
  have hρ := norm_freeRho_lt_one b w hw
  have hD := one_sub_pow_ne_zero hρ (L := n + 2) (by omega)
  have hf := freeT_eq b w hw
  have hρs := freeRho_s b hw
  have h1 := sub_freeS_eq b hw
  have hρw := freeRho_w b hw
  have hs0 := freeS_ne_zero b hw
  unfold cycV
  have e2 : n + 2 - 1 = n + 1 := by omega
  have e3 : n + 2 - (n + 1) = 1 := by omega
  rw [e2, e3, Nat.sub_zero]
  have h0 := freeRho_mul b hw
  have key : 2 * (b : ℂ) * (freeRho b w + freeRho b w ^ (n + 1)) -
      w * (1 + freeRho b w ^ (n + 2)) = -freeS b w * (1 - freeRho b w ^ (n + 2)) := by
    linear_combination (-1 : ℂ) * h1 - freeRho b w ^ (n + 1) * h0
  have hfs : freeT b w * freeS b w = -1 := by
    rw [hf]; field_simp
  have hsum : (b : ℂ) *
        (freeT b w * (freeRho b w ^ (n + 1) + freeRho b w ^ 1) / (1 - freeRho b w ^ (n + 2)) +
          freeT b w * (freeRho b w ^ 1 + freeRho b w ^ (n + 1)) / (1 - freeRho b w ^ (n + 2))) -
      w * (freeT b w * (freeRho b w ^ 0 + freeRho b w ^ (n + 2)) / (1 - freeRho b w ^ (n + 2))) =
      freeT b w * (2 * (b : ℂ) * (freeRho b w + freeRho b w ^ (n + 1)) -
        w * (1 + freeRho b w ^ (n + 2))) / (1 - freeRho b w ^ (n + 2)) := by ring
  rw [hsum, key]
  field_simp
  linear_combination (-1 : ℂ) * hfs

/-- The successor on `ℤ_L`. -/
private def cycSucc {L : ℕ} (a : Fin L) : Fin L :=
  ⟨if a.val + 1 < L then a.val + 1 else 0, by have := a.isLt; split_ifs <;> omega⟩

/-- The predecessor on `ℤ_L`. -/
private def cycPred {L : ℕ} (a : Fin L) : Fin L :=
  ⟨if 0 < a.val then a.val - 1 else L - 1, by have := a.isLt; split_ifs <;> omega⟩

private lemma succ_mod_eq (L x : ℕ) (hx : x < L) :
    (x + 1) % L = if x + 1 < L then x + 1 else 0 := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : x + 1 = L := by omega
    rw [this, Nat.mod_self]

private lemma cycleAdj_apply {L : ℕ} (a k : Fin L) :
    cycleAdj L a k = (if k = cycSucc a then 1 else 0) + (if k = cycPred a then 1 else 0) := by
  simp only [cycleAdj, Matrix.of_apply]
  have hk := k.isLt
  have ha := a.isLt
  have h1 : (k.val = (a.val + 1) % L) ↔ k = cycSucc a := by
    rw [succ_mod_eq L a.val ha, Fin.ext_iff]
    simp only [cycSucc]
  have h2 : (a.val = (k.val + 1) % L) ↔ k = cycPred a := by
    rw [succ_mod_eq L k.val hk, Fin.ext_iff]
    simp only [cycPred]
    split_ifs <;> omega
  rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl]

/-- The distance `c - a` on `ℤ_L`, as a natural number below `L`. -/
private def cycD (L : ℕ) (a c : Fin L) : ℕ :=
  if a.val ≤ c.val then c.val - a.val else c.val + L - a.val

/-- The circulant matrix with first row `V`. -/
private def cycN (b : ℝ) (w : ℂ) (L : ℕ) : Matrix (Fin L) (Fin L) ℂ :=
  Matrix.of fun a c => cycV b w L (cycD L a c)

private lemma cycle_mul (b : ℝ) {w : ℂ} (hw : 0 < w.im) (L : ℕ) (hL : 3 ≤ L) :
    ((b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ)) * cycN b w L = 1 := by
  ext a c
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin L,
      ((b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ)) a k * cycN b w L k c =
        (if k = cycSucc a then (b : ℂ) * cycN b w L k c else 0) +
        (if k = cycPred a then (b : ℂ) * cycN b w L k c else 0) -
        (if k = a then w * cycN b w L k c else 0) := by
    intro k
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      cycleAdj_apply, eq_comm (a := a) (b := k)]
    split_ifs <;> ring
  simp_rw [key]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [cycN, Matrix.of_apply, Matrix.one_apply]
  have hA := a.isLt
  have hC := c.isLt
  have hs : (cycSucc a).val = if a.val + 1 < L then a.val + 1 else 0 := rfl
  have hp : (cycPred a).val = if 0 < a.val then a.val - 1 else L - 1 := rfl
  by_cases hac : a = c
  · subst hac
    have e0 : cycD L a a = 0 := by simp [cycD]
    have e1 : cycD L (cycSucc a) a = L - 1 := by
      unfold cycD; rw [hs]; split_ifs <;> omega
    have e2 : cycD L (cycPred a) a = 1 := by
      unfold cycD; rw [hp]; split_ifs <;> omega
    rw [e0, e1, e2]
    simp only [↓reduceIte]
    linear_combination cycV_rec_zero b hw L (by omega)
  · have hne : a.val ≠ c.val := fun h => hac (Fin.ext h)
    have hd1 : 1 ≤ cycD L a c := by unfold cycD; split_ifs <;> omega
    have hd2 : cycD L a c < L := by unfold cycD; split_ifs <;> omega
    have e1 : cycD L (cycSucc a) c = cycD L a c - 1 := by
      unfold cycD; rw [hs]; split_ifs <;> omega
    rw [e1]
    simp only [hac, ↓reduceIte]
    by_cases hlt : cycD L a c + 1 < L
    · have e2 : cycD L (cycPred a) c = cycD L a c + 1 := by
        unfold cycD at hlt ⊢; rw [hp]; split_ifs at hlt ⊢ <;> omega
      rw [e2]
      linear_combination cycV_rec_int b hw L _ hd1 hlt.le
    · have e2 : cycD L (cycPred a) c = 0 := by
        unfold cycD at hlt ⊢; rw [hp]; split_ifs at hlt ⊢ <;> omega
      rw [e2, ← cycV_L b w L]
      have : cycD L a c + 1 = L := by omega
      have h := cycV_rec_int b hw L _ hd1 this.le
      rw [this] at h
      linear_combination h

/-- (A.5) [bl:eq:free], row on the cycle `ℤ_L`. -/
theorem freeRowCycle_eq (b : ℝ) (w : ℂ) (hw : 0 < w.im) (L : ℕ) (hL : 3 ≤ L) (x : Fin L) :
    ((b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ ⟨0, by omega⟩ x =
      freeT b w * (freeRho b w ^ x.val + freeRho b w ^ (L - x.val)) /
        (1 - freeRho b w ^ L) := by
  rw [Matrix.inv_eq_right_inv (cycle_mul b hw L hL)]
  have hD : cycD L ⟨0, by omega⟩ x = x.val := by
    unfold cycD
    simp
  change cycV b w L (cycD L ⟨0, by omega⟩ x) = _
  rw [hD]
  rfl

set_option linter.unusedVariables false in
/-- In `ℂ_+`, (1.9) [eq:dyson] is the quartic `u²((z + γ_g u)² - 4b²) = 1`, `b = g/max{1,g}`. -/
theorem dyson_iff_quartic (g : ℝ) (hg : 0 ≤ g) (z : ℂ) (hz : 0 < z.im) (u : ℂ) (hu : 0 < u.im) :
    u = dysonRHS g z u ↔ u ^ 2 * ((z + gammaG g * u) ^ 2 - 4 * (hopB g : ℂ) ^ 2) = 1 := by
  have hm : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hwim : 0 < (z + (gammaG g : ℂ) * u).im := by
    rw [Complex.add_im, Complex.im_ofReal_mul]
    positivity
  rw [dysonRHS_eq_freeT, freeT_eq _ _ hwim, ← freeS_sq (hopB g) (z + (gammaG g : ℂ) * u)]
  set s := freeS (hopB g) (z + (gammaG g : ℂ) * u) with hs
  have hs0 : s ≠ 0 := freeS_ne_zero _ hwim
  have hsim : 0 < s.im := freeS_im_pos _ _ hwim
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    have h2 : (u * s - 1) * (u * s + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exfalso
      have h4 : s = u⁻¹ := by
        have : u * s = 1 := by linear_combination h3
        exact eq_inv_of_mul_eq_one_right this
      have h5 : s.im = -u.im / Complex.normSq u := by rw [h4, Complex.inv_im]
      have h6 : 0 < Complex.normSq u := Complex.normSq_pos.mpr (fun h => by simp [h] at hu)
      have : s.im < 0 := by rw [h5]; exact div_neg_of_neg_of_pos (by linarith) h6
      linarith
    · have : u * s = -1 := by linear_combination h3
      have h4 : u * (-s) = 1 := by linear_combination -this
      rw [← inv_neg]
      exact eq_inv_of_mul_eq_one_left h4

end LSBA
