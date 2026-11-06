import LSBA.Dyson.Scalar

/-!
# Rough stability of the Dyson equation

Lemma A.17 [da:lem:rough-stability]: an approximate solution of (1.9) [eq:dyson] in the upper
half-plane is close to `m_g`, and finite Fourier averages are close to the integral.
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-! ### The resolvent `R_w(p) = (2b cos p - w)⁻¹` -/

/-- Integrand of `freeT b w`. -/
private def rsRes (b : ℝ) (w : ℂ) (p : ℝ) : ℂ := ((2 * b * Real.cos p : ℝ) - w)⁻¹

private lemma rsRes_base_ne {b : ℝ} {w : ℂ} (hw : 0 < w.im) (p : ℝ) :
    ((2 * b * Real.cos p : ℝ) : ℂ) - w ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

private lemma continuous_rsRes {b : ℝ} {w : ℂ} (hw : 0 < w.im) : Continuous (rsRes b w) := by
  unfold rsRes
  exact Continuous.inv₀ (by fun_prop) (rsRes_base_ne hw)

private lemma norm_rsRes_le (b : ℝ) {w : ℂ} (hw : 0 < w.im) (p : ℝ) :
    ‖rsRes b w p‖ ≤ w.im⁻¹ := by
  unfold rsRes
  rw [norm_inv]
  apply inv_anti₀ hw
  calc w.im = |(((2 * b * Real.cos p : ℝ) : ℂ) - w).im| := by simp [abs_of_pos hw]
    _ ≤ ‖((2 * b * Real.cos p : ℝ) : ℂ) - w‖ := Complex.abs_im_le_norm _

private lemma rsRes_periodic (b : ℝ) (w : ℂ) : Function.Periodic (rsRes b w) (2 * π) := by
  intro p
  unfold rsRes
  rw [Real.cos_add_two_pi]

/-- The resolvent is Lipschitz in `p` with constant `2 |b| (Im w)⁻²`. -/
private lemma rsRes_lipschitz (b : ℝ) {w : ℂ} (hw : 0 < w.im) (p q : ℝ) :
    ‖rsRes b w p - rsRes b w q‖ ≤ 2 * |b| * (w.im⁻¹) ^ 2 * |p - q| := by
  have h1 := rsRes_base_ne (b := b) hw p
  have h2 := rsRes_base_ne (b := b) hw q
  have e : rsRes b w p - rsRes b w q =
      (((2 * b * Real.cos q : ℝ) : ℂ) - ((2 * b * Real.cos p : ℝ) : ℂ)) *
        (rsRes b w p * rsRes b w q) := by
    unfold rsRes
    field_simp
    ring
  rw [e, norm_mul, norm_mul]
  have hcos : ‖(((2 * b * Real.cos q : ℝ) : ℂ) - ((2 * b * Real.cos p : ℝ) : ℂ))‖ ≤
      2 * |b| * |p - q| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have := Real.abs_cos_sub_cos_le q p
    calc |2 * b * Real.cos q - 2 * b * Real.cos p| = 2 * |b| * |Real.cos q - Real.cos p| := by
          rw [← mul_sub, abs_mul, abs_mul, abs_two]
      _ ≤ 2 * |b| * |p - q| := by
          rw [abs_sub_comm q p] at this
          gcongr
  have hp := norm_rsRes_le b hw p
  have hq := norm_rsRes_le b hw q
  have hpq : ‖rsRes b w p‖ * ‖rsRes b w q‖ ≤ (w.im⁻¹) ^ 2 := by
    rw [sq]
    exact mul_le_mul hp hq (norm_nonneg _) (inv_nonneg.mpr hw.le)
  calc _ ≤ (2 * |b| * |p - q|) * (w.im⁻¹) ^ 2 :=
        mul_le_mul hcos hpq (by positivity) (by positivity)
    _ = _ := by ring

/-- Riemann-sum error for a `2π`-periodic function that is `K`-Lipschitz: the mean over the
`L`-point grid differs from the mean over a period by at most `π K / L`. -/
private lemma riemann_error {F : ℝ → ℂ} (hc : Continuous F)
    (hper : Function.Periodic F (2 * π)) {K : ℝ} (hK : ∀ p q, ‖F p - F q‖ ≤ K * |p - q|)
    {L : ℕ} (hL : 1 ≤ L) :
    ‖(L : ℂ)⁻¹ * ∑ k ∈ Finset.range L, F (2 * π * k / L) -
        (2 * π : ℂ)⁻¹ * ∫ p in (-π)..π, F p‖ ≤ π * K / L := by
  have hπ := Real.pi_pos
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  set δ : ℝ := 2 * π / L with hδ
  have hδpos : 0 < δ := by positivity
  set a : ℕ → ℝ := fun k => k * δ with ha
  have hadj : ∀ k, a (k + 1) = a k + δ := by
    intro k
    simp only [ha]
    push_cast
    ring
  have hint : ∫ p in (-π)..π, F p = ∑ k ∈ Finset.range L, ∫ p in a k..a (k + 1), F p := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => hc.intervalIntegrable _ _)]
    have e1 : a 0 = 0 := by simp [ha]
    have e2 : a L = 2 * π := by
      simp only [ha, hδ]
      field_simp
    rw [e1, e2]
    have := hper.intervalIntegral_add_eq (-π) 0
    rw [show -π + 2 * π = π by ring, zero_add] at this
    exact this
  have hloc : ∀ k, ‖(δ : ℂ) * F (a k) - ∫ p in a k..a (k + 1), F p‖ ≤ K * δ ^ 2 / 2 := by
    intro k
    have h1 : (δ : ℂ) * F (a k) = ∫ p in a k..a (k + 1), F (a k) := by
      rw [intervalIntegral.integral_const, hadj, Complex.real_smul]
      congr 2
      ring
    rw [h1, ← intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
    have hle : a k ≤ a (k + 1) := by rw [hadj]; linarith
    calc ‖∫ p in a k..a (k + 1), (F (a k) - F p)‖
        ≤ ∫ p in a k..a (k + 1), ‖F (a k) - F p‖ :=
          intervalIntegral.norm_integral_le_integral_norm hle
      _ ≤ ∫ p in a k..a (k + 1), K * (p - a k) := by
          refine intervalIntegral.integral_mono_on hle
            ((continuous_const.sub hc).norm.intervalIntegrable _ _)
            ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _)
            (fun p hp => ?_)
          have := hK (a k) p
          rwa [abs_sub_comm, abs_of_nonneg (by linarith [hp.1])] at this
      _ = K * δ ^ 2 / 2 := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_comp_sub_right (fun p => p) (a k), integral_id, hadj]
          ring
  have hL' : (L : ℂ)⁻¹ = (2 * π : ℂ)⁻¹ * (δ : ℂ) := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have : (L : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
    simp only [hδ]
    push_cast
    field_simp
  have hgrid : ∀ k : ℕ, 2 * π * (k : ℝ) / L = a k := by
    intro k
    simp only [ha, hδ]
    ring
  have e : (L : ℂ)⁻¹ * ∑ k ∈ Finset.range L, F (2 * π * k / L) -
        (2 * π : ℂ)⁻¹ * ∫ p in (-π)..π, F p =
      (2 * π : ℂ)⁻¹ * ∑ k ∈ Finset.range L,
        ((δ : ℂ) * F (a k) - ∫ p in a k..a (k + 1), F p) := by
    rw [hint, Finset.sum_sub_distrib, ← Finset.mul_sum, hL']
    simp only [hgrid]
    ring
  rw [e, norm_mul, norm_inv, show ‖(2 * π : ℂ)‖ = 2 * π by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]]
  calc (2 * π)⁻¹ * ‖∑ k ∈ Finset.range L, ((δ : ℂ) * F (a k) - ∫ p in a k..a (k + 1), F p)‖
      ≤ (2 * π)⁻¹ * ∑ k ∈ Finset.range L, (K * δ ^ 2 / 2) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => hloc k))
    _ = π * K / L := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hδ]
        field_simp


private lemma rs_max_one_pos (g : ℝ) : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)

private lemma rs_abs_hopB_le_one {g : ℝ} (hg : 0 ≤ g) : |hopB g| ≤ 1 := by
  unfold hopB
  rw [abs_of_nonneg (div_nonneg hg (rs_max_one_pos g).le)]
  exact div_le_one_of_le₀ (le_max_right _ _) (rs_max_one_pos g).le

/-! ### The averages `⟨|R_w|²⟩` and `⟨R_w R_{w'}⟩` -/

private lemma rs_norm_two_pi : ‖(2 * π : ℂ)‖ = 2 * π := by
  rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

/-- `⟨|R_w|²⟩`, the mean of `|R_w(p)|²` over `[-π, π]`. -/
private def rsNsq (b : ℝ) (w : ℂ) : ℝ := (2 * π)⁻¹ * ∫ p in (-π)..π, ‖rsRes b w p‖ ^ 2

/-- Ward identity for `freeT`: `Im f(w) = Im w · ⟨|R_w|²⟩`. -/
private lemma rs_im_freeT (b : ℝ) {w : ℂ} (hw : 0 < w.im) :
    (freeT b w).im = w.im * rsNsq b w := by
  have hcont := continuous_rsRes (b := b) hw
  have e : freeT b w = (((2 * π)⁻¹ : ℝ) : ℂ) * ∫ p in (-π)..π, rsRes b w p := by
    unfold freeT rsRes
    push_cast
    ring_nf
  rw [e, Complex.im_ofReal_mul]
  unfold rsNsq
  rw [mul_left_comm]
  congr 1
  rw [show (∫ p in (-π)..π, rsRes b w p).im = ∫ p in (-π)..π, (rsRes b w p).im from
    (intervalIntegral.intervalIntegral_im (hcont.intervalIntegrable _ _)).symm]
  have : ∀ p, (rsRes b w p).im = w.im * ‖rsRes b w p‖ ^ 2 := by
    intro p
    unfold rsRes
    rw [Complex.inv_im, Complex.sq_norm, Complex.normSq_inv]
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
    ring
  simp only [this]
  rw [intervalIntegral.integral_const_mul]

/-- Resolvent identity for the free transform:
`f(w) - f(w') = (w - w') ⟨R_w R_{w'}⟩`. -/
private lemma rs_freeT_sub (b : ℝ) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) :
    freeT b w - freeT b w' =
      (w - w') * ((2 * π : ℂ)⁻¹ * ∫ p in (-π)..π, rsRes b w p * rsRes b w' p) := by
  have h1 := continuous_rsRes (b := b) hw
  have h2 := continuous_rsRes (b := b) hw'
  have hp : ∀ p, rsRes b w p - rsRes b w' p = (w - w') * (rsRes b w p * rsRes b w' p) := by
    intro p
    have a1 := rsRes_base_ne (b := b) hw p
    have a2 := rsRes_base_ne (b := b) hw' p
    unfold rsRes
    field_simp
    ring
  have e1 : freeT b w = (2 * π : ℂ)⁻¹ * ∫ p in (-π)..π, rsRes b w p := rfl
  have e2 : freeT b w' = (2 * π : ℂ)⁻¹ * ∫ p in (-π)..π, rsRes b w' p := rfl
  rw [e1, e2, ← mul_sub, ← intervalIntegral.integral_sub (h1.intervalIntegrable _ _)
    (h2.intervalIntegrable _ _)]
  simp only [hp]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- `‖⟨R_w R_{w'}⟩‖ ≤ (⟨|R_w|²⟩ + ⟨|R_{w'}|²⟩) / 2`. -/
private lemma rs_norm_avg_le (b : ℝ) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) :
    ‖(2 * π : ℂ)⁻¹ * ∫ p in (-π)..π, rsRes b w p * rsRes b w' p‖ ≤
      (rsNsq b w + rsNsq b w') / 2 := by
  have hπ := Real.pi_pos
  have h1 := continuous_rsRes (b := b) hw
  have h2 := continuous_rsRes (b := b) hw'
  have hle : -π ≤ π := by linarith
  rw [norm_mul, norm_inv, rs_norm_two_pi]
  have hA : ‖∫ p in (-π)..π, rsRes b w p * rsRes b w' p‖ ≤
      ∫ p in (-π)..π, (‖rsRes b w p‖ ^ 2 + ‖rsRes b w' p‖ ^ 2) / 2 := by
    refine (intervalIntegral.norm_integral_le_integral_norm hle).trans ?_
    refine intervalIntegral.integral_mono_on hle ((h1.mul h2).norm.intervalIntegrable _ _)
      ((((h1.norm.pow 2).add (h2.norm.pow 2)).div_const 2).intervalIntegrable _ _)
      (fun p _ => ?_)
    rw [norm_mul]
    nlinarith [sq_nonneg (‖rsRes b w p‖ - ‖rsRes b w' p‖)]
  have hB : ∫ p in (-π)..π, (‖rsRes b w p‖ ^ 2 + ‖rsRes b w' p‖ ^ 2) / 2 =
      ((∫ p in (-π)..π, ‖rsRes b w p‖ ^ 2) + ∫ p in (-π)..π, ‖rsRes b w' p‖ ^ 2) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add
      ((show Continuous fun p => ‖rsRes b w p‖ ^ 2 by fun_prop).intervalIntegrable _ _)
      ((show Continuous fun p => ‖rsRes b w' p‖ ^ 2 by fun_prop).intervalIntegrable _ _)]
  unfold rsNsq
  calc (2 * π)⁻¹ * ‖∫ p in (-π)..π, rsRes b w p * rsRes b w' p‖
      ≤ (2 * π)⁻¹ * (((∫ p in (-π)..π, ‖rsRes b w p‖ ^ 2) +
          ∫ p in (-π)..π, ‖rsRes b w' p‖ ^ 2) / 2) := by
        gcongr
        exact hA.trans hB.le
    _ = _ := by ring

private lemma rs_gamma_pos (g : ℝ) : 0 < gammaG g := by
  have := rs_max_one_pos g
  unfold gammaG
  positivity

private lemma rs_gamma_le_one (g : ℝ) : gammaG g ≤ 1 := by
  unfold gammaG
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_max_left _ _))

/-- Lemma A.17 [da:lem:rough-stability], first part, with constant `8`. -/
theorem rough_stability (g : ℝ) (hg : 0 ≤ g) (E η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (u r : ℂ)
    (hu : 0 < u.im) (hu1 : ‖u‖ ≤ η⁻¹)
    (hur : u = freeT (hopB g) (E + η * I + gammaG g * u) + r) (hr : ‖r‖ ≤ η / 2) :
    ‖u - mDyson g (E + η * I)‖ ≤ 8 * (η⁻¹) ^ 2 * ‖r‖ := by
  set γ := gammaG g with hγdef
  have hγ0 : 0 < γ := rs_gamma_pos g
  have hγ1 : γ ≤ 1 := rs_gamma_le_one g
  set z : ℂ := (E : ℂ) + η * I with hzdef
  have hz : z.im = η := by simp [hzdef]
  have hzpos : 0 < z.im := by rw [hz]; exact hη
  set m := mDyson g z with hmdef
  obtain ⟨hm, hfix⟩ := mDyson_spec g hg z hzpos
  rw [← hmdef, dysonRHS_eq_freeT, ← hγdef] at hfix
  set b := hopB g with hbdef
  have hw1 : (z + (γ : ℂ) * u).im = η + γ * u.im := by simp [hz]
  have hw2 : (z + (γ : ℂ) * m).im = η + γ * m.im := by simp [hz]
  have hw1pos : 0 < (z + (γ : ℂ) * u).im := by rw [hw1]; positivity
  have hw2pos : 0 < (z + (γ : ℂ) * m).im := by rw [hw2]; positivity
  -- the linear relation `(1 - q)(u - m) = r`
  set A : ℂ := (2 * π : ℂ)⁻¹ * ∫ p in (-π)..π,
    rsRes b (z + (γ : ℂ) * u) p * rsRes b (z + (γ : ℂ) * m) p with hA
  have hdiff := rs_freeT_sub b hw1pos hw2pos
  have e1 : freeT b (z + (γ : ℂ) * u) = u - r := eq_sub_of_add_eq hur.symm
  have hrel : (1 - (γ : ℂ) * A) * (u - m) = r := by
    rw [e1, ← hfix] at hdiff
    rw [← hA] at hdiff
    have : (z + (γ : ℂ) * u - (z + (γ : ℂ) * m)) = (γ : ℂ) * (u - m) := by ring
    rw [this] at hdiff
    linear_combination hdiff
  -- Ward identities
  have hN1 : (η + γ * u.im) * rsNsq b (z + (γ : ℂ) * u) = u.im - r.im := by
    have := rs_im_freeT b hw1pos
    rw [hw1, e1] at this
    simpa using this.symm
  have hN2 : (η + γ * m.im) * rsNsq b (z + (γ : ℂ) * m) = m.im := by
    have := rs_im_freeT b hw2pos
    rw [hw2, ← hfix] at this
    exact this.symm
  set n1 := rsNsq b (z + (γ : ℂ) * u)
  set n2 := rsNsq b (z + (γ : ℂ) * m)
  have hrim : -r.im ≤ ‖r‖ := by
    have := Complex.abs_im_le_norm r
    have := neg_abs_le r.im
    linarith
  have huim : u.im ≤ η⁻¹ := (le_abs_self _).trans ((Complex.abs_im_le_norm u).trans hu1)
  -- bounds on `γ n1` and `γ n2`
  have hγu : γ * u.im ≤ η⁻¹ := by nlinarith
  have hγu' : γ * u.im * η ≤ 1 := by
    calc γ * u.im * η ≤ η⁻¹ * η := by gcongr
      _ = 1 := inv_mul_cancel₀ hη.ne'
  have hn1 : γ * n1 ≤ 1 - η ^ 2 / 4 := by
    have hpos : 0 < η + γ * u.im := by positivity
    have h1 : (η + γ * u.im) * (γ * n1) ≤ γ * (u.im + ‖r‖) := by
      have : (η + γ * u.im) * (γ * n1) = γ * (u.im - r.im) := by rw [← hN1]; ring
      rw [this]
      nlinarith
    have h2 : γ * (u.im + ‖r‖) ≤ (η + γ * u.im) * (1 - η ^ 2 / 4) := by
      have a1 : γ * ‖r‖ ≤ η / 2 := by nlinarith [norm_nonneg r]
      have a2 : γ * u.im * η ^ 2 / 4 ≤ η / 4 := by
        have : γ * u.im * η ^ 2 = (γ * u.im * η) * η := by ring
        rw [this]
        nlinarith
      nlinarith [mul_pos hη hη, mul_pos (mul_pos hη hη) hη]
    exact le_of_mul_le_mul_left (h1.trans h2) hpos
  have hn2 : γ * n2 ≤ 1 := by
    have hpos : 0 < η + γ * m.im := by positivity
    have h1 : (η + γ * m.im) * (γ * n2) = γ * m.im := by linear_combination γ * hN2
    have : (η + γ * m.im) * (γ * n2) ≤ (η + γ * m.im) * 1 := by
      rw [h1]; nlinarith
    exact le_of_mul_le_mul_left this hpos
  -- `‖q‖ ≤ 1 - η²/8`
  have hq : ‖(γ : ℂ) * A‖ ≤ 1 - η ^ 2 / 8 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ0.le]
    have := rs_norm_avg_le b hw1pos hw2pos
    calc γ * ‖A‖ ≤ γ * ((n1 + n2) / 2) := by gcongr
      _ = (γ * n1 + γ * n2) / 2 := by ring
      _ ≤ _ := by linarith
  have h1q : η ^ 2 / 8 ≤ ‖1 - (γ : ℂ) * A‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((γ : ℂ) * A)
    rw [norm_one] at this
    linarith
  have hfin : ‖1 - (γ : ℂ) * A‖ * ‖u - m‖ = ‖r‖ := by rw [← norm_mul, hrel]
  have hη2 : 0 < η ^ 2 := by positivity
  have : η ^ 2 / 8 * ‖u - m‖ ≤ ‖r‖ := by
    rw [← hfin]
    gcongr
  rw [inv_pow, show 8 * (η ^ 2)⁻¹ * ‖r‖ = ‖r‖ / (η ^ 2 / 8) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- Lemma A.17 [da:lem:rough-stability], second part: the finite Fourier average is close to the
integral, with constant `2π`. -/
theorem freeTL_sub_freeT (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 1 ≤ L) (η : ℝ) (hη : 0 < η)
    (w : ℂ) (hw : η ≤ w.im) :
    ‖freeTL (hopB g) L w - freeT (hopB g) w‖ ≤ 2 * π / L * (η⁻¹) ^ 2 := by
  have hπ := Real.pi_pos
  have hpos : 0 < w.im := lt_of_lt_of_le hη hw
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le one_pos hL)
  have key := riemann_error (continuous_rsRes (b := hopB g) hpos)
    (rsRes_periodic (hopB g) w) (K := 2 * |hopB g| * (w.im⁻¹) ^ 2)
    (rsRes_lipschitz (hopB g) hpos) hL
  have e : freeTL (hopB g) L w =
      (L : ℂ)⁻¹ * ∑ k ∈ Finset.range L, rsRes (hopB g) w (2 * π * k / L) := by
    unfold freeTL
    rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => rsRes (hopB g) w (2 * π * k / L)) L]
    rfl
  have e' : freeT (hopB g) w = (2 * π : ℂ)⁻¹ * ∫ p in (-π)..π, rsRes (hopB g) w p := rfl
  rw [e, e']
  refine key.trans ?_
  have hb := rs_abs_hopB_le_one hg
  have hinv : w.im⁻¹ ≤ η⁻¹ := inv_anti₀ hη hw
  have h2 : (w.im⁻¹) ^ 2 ≤ (η⁻¹) ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) hinv 2
  have h3 : 2 * |hopB g| * (w.im⁻¹) ^ 2 ≤ 2 * (η⁻¹) ^ 2 := by
    calc 2 * |hopB g| * (w.im⁻¹) ^ 2 ≤ 2 * 1 * (η⁻¹) ^ 2 := by gcongr
      _ = _ := by ring
  calc π * (2 * |hopB g| * (w.im⁻¹) ^ 2) / L ≤ π * (2 * (η⁻¹) ^ 2) / L := by gcongr
    _ = _ := by ring

end LSBA
