import LSBA.Kernel.Defs

/-!
# Scales and budgets

The scales `ℓ_t`, `ζ_t` of (A.46) [gc:eq:scale] and (6.6) [fo:eq:spatial-sum-budget], the comparison
of scales under a change of coupling (A.61) [bl:eq:backdomain] and the profile minimum (A.56)
[da:eq:profile-minimum] (Appendices A.7 [app:main-propagators]–A.8 [app:scale-budgets]).
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

private lemma scales_gamma_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG; positivity

private lemma scales_gamma_le_one (g : ℝ) : gammaG g ≤ 1 := by
  unfold gammaG
  have h : (1 : ℝ) ≤ (max 1 g) ^ 2 := one_le_pow₀ (le_max_left _ _)
  exact inv_le_one_of_one_le₀ h

/-- `g √γ_g = min{g, 1}` for `g ≥ 0`. -/
private lemma scales_sigma (g : ℝ) (hg : 0 ≤ g) : g * Real.sqrt (gammaG g) = min g 1 := by
  unfold gammaG
  rcases le_total g 1 with h | h
  · rw [max_eq_left h, min_eq_left h]; simp
  · rw [max_eq_right h, min_eq_right h, Real.sqrt_inv, Real.sqrt_sq (by linarith)]
    exact mul_inv_cancel₀ (by linarith)

private lemma scales_zeta_eq (g : ℝ) (W L : ℕ) (t : ℝ) :
    zetaProp g W L t = ((W : ℝ) * (ellProp g L t * (1 - t) * gammaG g))⁻¹ := by
  unfold zetaProp; congr 1; ring

private lemma scales_ell_ge_one (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 1 ≤ L) (t : ℝ) :
    1 ≤ ellProp g L t := by
  unfold ellProp
  refine le_min (by exact_mod_cast hL) ?_
  have : 0 ≤ g / Real.sqrt (gammaG g * (1 - t)) := div_nonneg hg (Real.sqrt_nonneg _)
  linarith

private lemma scales_Q_pos (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 1 ≤ L) (t : ℝ) (ht : t < 1) :
    0 < ellProp g L t * (1 - t) * gammaG g := by
  have h1 := scales_ell_ge_one g hg L hL t
  have h2 : 0 < 1 - t := by linarith
  have h3 := scales_gamma_pos g
  positivity

/-- `ℓ_t (1 - t) γ = min{L γ (1 - t), γ (1 - t) + min{g, 1} √(1 - t)}`. -/
private lemma scales_Q (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (t : ℝ) (ht : t < 1) :
    ellProp g L t * (1 - t) * gammaG g =
      min ((L : ℝ) * (gammaG g * (1 - t)))
        (gammaG g * (1 - t) + min g 1 * Real.sqrt (1 - t)) := by
  have hx : 0 < 1 - t := by linarith
  have hγ := scales_gamma_pos g
  unfold ellProp
  rw [min_mul_of_nonneg _ _ hx.le, min_mul_of_nonneg _ _ hγ.le]
  have hpos : 0 < gammaG g * (1 - t) := mul_pos hγ hx
  have ha : 0 < Real.sqrt (gammaG g * (1 - t)) := Real.sqrt_pos.mpr hpos
  have hmul := Real.mul_self_sqrt hpos.le
  have hsq : Real.sqrt (gammaG g * (1 - t)) = Real.sqrt (gammaG g) * Real.sqrt (1 - t) :=
    Real.sqrt_mul hγ.le _
  congr 1
  · ring
  · set a := Real.sqrt (gammaG g * (1 - t)) with ha_def
    have h1 : (1 + g / a) * (1 - t) * gammaG g = gammaG g * (1 - t) + g * a := by
      have : (1 + g / a) * (1 - t) * gammaG g
          = gammaG g * (1 - t) + g * (gammaG g * (1 - t)) / a := by
        field_simp
      rw [this, ← hmul]
      field_simp
    rw [h1, hsq, ← scales_sigma g hg]
    ring

private lemma scales_Q_le_two (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    ellProp g L s * (1 - s) * gammaG g ≤ 2 := by
  rw [scales_Q g hg L s hs1]
  refine (min_le_right _ _).trans ?_
  have hγ := scales_gamma_pos g
  have h1 : gammaG g * (1 - s) ≤ 1 := by
    have := scales_gamma_le_one g
    nlinarith
  have h2 : min g 1 * Real.sqrt (1 - s) ≤ 1 := by
    refine mul_le_one₀ (min_le_right _ _) (Real.sqrt_nonneg _) ?_
    rw [Real.sqrt_le_one]; linarith
  linarith

/-- (A.46) [gc:eq:scale] and the scale facts after (5.18) [fo:eq:scale], with the explicit lower
bound `ζ ≥ (2W)⁻¹` and the identity of (6.6) [fo:eq:spatial-sum-budget]. -/
theorem scale_facts (g : ℝ) (hg : 0 ≤ g) (W L : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L) (s u : ℝ)
    (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u < 1) :
    1 ≤ ellProp g L s ∧ ellProp g L s ≤ ellProp g L u ∧ ellProp g L u ≤ L ∧
      (2 * (W : ℝ))⁻¹ ≤ zetaProp g W L s ∧ zetaProp g W L s ≤ zetaProp g W L u ∧
      zetaProp g W L u ≤ (1 - s) / (1 - u) * zetaProp g W L s ∧
      gammaG g * W * ellProp g L u * zetaProp g W L u = (1 - u)⁻¹ := by
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu
  have hγ := scales_gamma_pos g
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hu1 : 0 < 1 - u := by linarith
  have hs1' : 0 < 1 - s := by linarith
  have hlu : ellProp g L s ≤ ellProp g L u := by
    unfold ellProp
    refine min_le_min le_rfl ?_
    have h1 : Real.sqrt (gammaG g * (1 - u)) ≤ Real.sqrt (gammaG g * (1 - s)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have h2 : 0 < Real.sqrt (gammaG g * (1 - u)) := Real.sqrt_pos.mpr (mul_pos hγ hu1)
    have := div_le_div_of_nonneg_left hg h2 h1
    linarith
  have hQpos := scales_Q_pos g hg L hL u hu
  refine ⟨scales_ell_ge_one g hg L hL s, hlu, min_le_left _ _, ?_, ?_, ?_, ?_⟩
  · rw [scales_zeta_eq]
    have hQ := scales_Q_le_two g hg L s hs hs1
    have hQs := scales_Q_pos g hg L hL s hs1
    apply inv_anti₀ (by positivity)
    nlinarith
  · rw [scales_zeta_eq, scales_zeta_eq]
    have hQs := scales_Q_pos g hg L hL s hs1
    apply inv_anti₀ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hW0.le
    rw [scales_Q g hg L s hs1, scales_Q g hg L u hu]
    have hr : Real.sqrt (1 - u) ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt (by linarith)
    have hm : 0 ≤ min g 1 := le_min hg zero_le_one
    refine min_le_min ?_ ?_
    · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hγ.le)
        (Nat.cast_nonneg L)
    · nlinarith
  · rw [scales_zeta_eq, scales_zeta_eq]
    have hQs := scales_Q_pos g hg L hL s hs1
    have e : (1 - s) / (1 - u) * ((W : ℝ) * (ellProp g L s * (1 - s) * gammaG g))⁻¹
        = ((W : ℝ) * (ellProp g L s * (1 - u) * gammaG g))⁻¹ := by
      field_simp
    rw [e]
    have hl1 := scales_ell_ge_one g hg L hL s
    apply inv_anti₀ (by positivity)
    have : 0 < (1 - u) * gammaG g := mul_pos hu1 hγ
    nlinarith [mul_le_mul_of_nonneg_right hlu this.le]
  · rw [scales_zeta_eq]
    have hl1 := scales_ell_ge_one g hg L hL u
    have : (W : ℝ) * (ellProp g L u * (1 - u) * gammaG g) ≠ 0 := by positivity
    have : ellProp g L u ≠ 0 := by positivity
    field_simp

private lemma scales_sqrt_ratio (s u : ℝ) (hs : 1 / 2 ≤ s) (hsu : s ≤ u) (hu1 : u < 1) :
    0 < Real.sqrt (s / u) ∧ Real.sqrt (s / u) ≤ 1 ∧ 1 / 2 ≤ Real.sqrt (s / u) ^ 2 ∧
      1 - u ≤ Real.sqrt (s / u) ^ 2 * (1 - s) := by
  have hu : 0 < u := by linarith
  have hr : s / u ≤ 1 := (div_le_one hu).mpr hsu
  have hq : 0 ≤ s / u := by positivity
  have hsq : Real.sqrt (s / u) ^ 2 = s / u := Real.sq_sqrt hq
  have hpos : 0 < s / u := by apply div_pos <;> linarith
  refine ⟨Real.sqrt_pos.mpr hpos, ?_, ?_, ?_⟩
  · rw [Real.sqrt_le_one]; exact hr
  · rw [hsq, le_div_iff₀ hu]; nlinarith
  · rw [hsq, div_mul_eq_mul_div, le_div_iff₀ hu]
    nlinarith

private lemma scales_inv_mul_le {A B c : ℝ} (hA : 0 < A) (hB : 0 < B) (h : B ≤ c * A) :
    A⁻¹ ≤ c * B⁻¹ := by
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hA hB]
  linarith

private lemma scales_gamma_cmp (g r : ℝ) (hg : 0 ≤ g) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    gammaG g ≤ gammaG (g * r) ∧ gammaG (g * r) * r ^ 2 ≤ gammaG g ∧
      min (g * r) 1 ≤ min g 1 ∧ r * min g 1 ≤ min (g * r) 1 := by
  have hgr : 0 ≤ g * r := mul_nonneg hg hr0.le
  have hgle : g * r ≤ g := by nlinarith
  refine ⟨?_, ?_, min_le_min hgle le_rfl, ?_⟩
  · unfold gammaG
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (max_le_max le_rfl hgle) 2
  · unfold gammaG
    have hm : 0 < max 1 (g * r) := lt_max_of_lt_left one_pos
    have hmg : 0 < max 1 g := lt_max_of_lt_left one_pos
    have h1 : max 1 g * r ≤ max 1 (g * r) := by
      rw [max_mul_of_nonneg _ _ hr0.le]
      exact max_le_max (by nlinarith) le_rfl
    have h2 : (max 1 g * r) ^ 2 ≤ (max 1 (g * r)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [inv_mul_eq_div, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : r ^ 2 * (max 1 g) ^ 2 = (max 1 g * r) ^ 2 := by ring
    linarith
  · rcases le_total g 1 with h | h
    · rw [min_eq_left h]
      rcases le_total (g * r) 1 with h' | h'
      · rw [min_eq_left h']; nlinarith
      · rw [min_eq_right h']; nlinarith
    · rw [min_eq_right h]
      exact le_min (by nlinarith) (by linarith)

/-- (A.61) [bl:eq:backdomain]: `ζ_s(g') ≤ ζ_u(g)` and `ζ_s(g') ≍ ζ_s(g)` for `g' = g√(s/u)`. -/
theorem zeta_cmp_le (g : ℝ) (hg : 0 ≤ g) (W L : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L) (s u : ℝ)
    (hs : 1 / 2 ≤ s) (hsu : s ≤ u) (hu : u < 1) :
    zetaProp (g * Real.sqrt (s / u)) W L s ≤ zetaProp g W L u ∧
      zetaProp (g * Real.sqrt (s / u)) W L s ≤ 2 * zetaProp g W L s ∧
      zetaProp g W L s ≤ 2 * zetaProp (g * Real.sqrt (s / u)) W L s := by
  obtain ⟨hr0, hr1, hr2, hr3⟩ := scales_sqrt_ratio s u hs hsu hu
  set r := Real.sqrt (s / u) with hr
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu
  have hg' : 0 ≤ g * r := mul_nonneg hg hr0.le
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨hc1, hc2, hc3, hc4⟩ := scales_gamma_cmp g r hg hr0 hr1
  have hγ := scales_gamma_pos g
  have hγ' := scales_gamma_pos (g * r)
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hx : 0 < 1 - s := by linarith
  have hxu : 0 < 1 - u := by linarith
  have hσ : 0 ≤ min g 1 := le_min hg zero_le_one
  have hσ' : 0 ≤ min (g * r) 1 := le_min hg' zero_le_one
  have hQu := scales_Q_pos g hg L hL u hu
  have hQs := scales_Q_pos g hg L hL s hs1
  have hQs' := scales_Q_pos (g * r) hg' L hL s hs1
  have hsq : Real.sqrt (1 - u) ≤ r * Real.sqrt (1 - s) := by
    calc Real.sqrt (1 - u) ≤ Real.sqrt (r ^ 2 * (1 - s)) := Real.sqrt_le_sqrt hr3
      _ = r * Real.sqrt (1 - s) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hr0.le]
  have hsn : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have hsnu : 0 ≤ Real.sqrt (1 - u) := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · rw [scales_zeta_eq, scales_zeta_eq]
    apply inv_anti₀ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hW0.le
    rw [scales_Q g hg L u hu, scales_Q (g * r) hg' L s hs1]
    refine min_le_min ?_ ?_
    · exact mul_le_mul_of_nonneg_left (by nlinarith) hL0
    · have e1 : gammaG g * (1 - u) ≤ gammaG (g * r) * (1 - s) :=
        mul_le_mul hc1 (by linarith) hxu.le hγ'.le
      have e2 : min g 1 * Real.sqrt (1 - u) ≤ min (g * r) 1 * Real.sqrt (1 - s) := by
        calc min g 1 * Real.sqrt (1 - u) ≤ min g 1 * (r * Real.sqrt (1 - s)) :=
              mul_le_mul_of_nonneg_left hsq hσ
          _ = (r * min g 1) * Real.sqrt (1 - s) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hc4 hsn
      linarith
  · rw [scales_zeta_eq, scales_zeta_eq]
    apply scales_inv_mul_le (by positivity) (by positivity)
    rw [mul_left_comm (2 : ℝ)]
    apply mul_le_mul_of_nonneg_left _ hW0.le
    rw [scales_Q g hg L s hs1, scales_Q (g * r) hg' L s hs1]
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    refine min_le_min ?_ ?_
    · have : gammaG g * (1 - s) ≤ 2 * (gammaG (g * r) * (1 - s)) := by nlinarith
      nlinarith
    · have e1 : gammaG g * (1 - s) ≤ gammaG (g * r) * (1 - s) :=
        mul_le_mul_of_nonneg_right hc1 hx.le
      have e2 : min g 1 * Real.sqrt (1 - s) ≤ 2 * (min (g * r) 1 * Real.sqrt (1 - s)) := by
        have : min g 1 ≤ 2 * min (g * r) 1 := by nlinarith
        nlinarith
      nlinarith
  · rw [scales_zeta_eq, scales_zeta_eq]
    apply scales_inv_mul_le (by positivity) (by positivity)
    rw [mul_left_comm (2 : ℝ)]
    apply mul_le_mul_of_nonneg_left _ hW0.le
    rw [scales_Q g hg L s hs1, scales_Q (g * r) hg' L s hs1]
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    refine min_le_min ?_ ?_
    · have hg2 : gammaG (g * r) ≤ 2 * gammaG g := by
        nlinarith [mul_le_mul_of_nonneg_left hr2 hγ'.le]
      have e : gammaG (g * r) * (1 - s) ≤ 2 * (gammaG g * (1 - s)) := by
        have := mul_le_mul_of_nonneg_right hg2 hx.le
        linarith
      have := mul_le_mul_of_nonneg_left e hL0
      linarith
    · have hg2 : gammaG (g * r) ≤ 2 * gammaG g := by
        nlinarith [mul_le_mul_of_nonneg_left hr2 hγ'.le]
      have e1 : gammaG (g * r) * (1 - s) ≤ 2 * (gammaG g * (1 - s)) := by
        have := mul_le_mul_of_nonneg_right hg2 hx.le
        linarith
      have e2 : min (g * r) 1 * Real.sqrt (1 - s) ≤ min g 1 * Real.sqrt (1 - s) :=
        mul_le_mul_of_nonneg_right hc3 hsn
      have e3 : 0 ≤ min g 1 * Real.sqrt (1 - s) := mul_nonneg hσ hsn
      linarith

/-- (A.56) [da:eq:profile-minimum], Lemma A.12 [da:lem:profile-improvement]. -/
theorem profile_minimum (c_p θ : ℝ) (hcp : 0 < c_p) (hθ : 0 < θ) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧ ∀ W : ℕ, 3 ≤ W → ∀ R x : ℝ, 1 ≤ R → R ≤ (W : ℝ) ^ 3 →
      0 ≤ x → min 1 (R ^ 10 * Real.exp (-(c_p * x ^ θ))) ≤
        Real.exp (C' * Real.sqrt (Real.log W)) * Real.exp (-(c' * x ^ (θ / 2))) := by
  refine ⟨1, 1 / (2 * c_p) + Real.sqrt (60 / c_p), one_pos, by positivity, ?_⟩
  intro W hW R x hR hRW hx
  have hy0 : 0 ≤ x ^ (θ / 2) := Real.rpow_nonneg hx _
  have hxy : x ^ θ = (x ^ (θ / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; push_cast; ring
  generalize x ^ (θ / 2) = y at hy0 hxy
  rw [hxy, one_mul]
  have hR0 : 0 < R := by linarith
  have hW3 : (3 : ℝ) ≤ W := by exact_mod_cast hW
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢; linarith
  have hlam : 1 ≤ Real.log W :=
    hlog3.le.trans (Real.log_le_log (by norm_num) hW3)
  have hlR : Real.log R ≤ 3 * Real.log W := by
    calc Real.log R ≤ Real.log ((W : ℝ) ^ 3) := Real.log_le_log hR0 hRW
      _ = 3 * Real.log W := by rw [Real.log_pow]; norm_num
  have hlR0 : 0 ≤ Real.log R := Real.log_nonneg hR
  set lam := Real.log W with hlam_def
  set K := Real.sqrt (60 / c_p) with hK
  set m := Real.sqrt lam with hm
  have hm1 : 1 ≤ m := by rw [hm, Real.one_le_sqrt]; exact hlam
  have hm2 : m ^ 2 = lam := Real.sq_sqrt (by linarith)
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hK2 : K ^ 2 = 60 / c_p := Real.sq_sqrt (by positivity)
  have hC1 : 1 / (2 * c_p) ≤ (1 / (2 * c_p) + K) * m := by
    have : 0 ≤ 1 / (2 * c_p) := by positivity
    nlinarith
  rw [← Real.exp_add]
  set C' := 1 / (2 * c_p) + K with hC'
  by_cases hcase : 10 * Real.log R ≤ c_p * y ^ 2 / 2
  · have hR10 : R ^ 10 = Real.exp (10 * Real.log R) := by
      rw [show (10 : ℝ) * Real.log R = ((10 : ℕ) : ℝ) * Real.log R by norm_num,
        Real.exp_nat_mul, Real.exp_log hR0]
    refine (min_le_right _ _).trans ?_
    rw [hR10, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : y - c_p * y ^ 2 / 2 ≤ 1 / (2 * c_p) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c_p * y - 1)]
    linarith
  · push_neg at hcase
    refine (min_le_left _ _).trans ?_
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hy2 : y ^ 2 < K ^ 2 * m ^ 2 := by
      rw [hK2, hm2, div_mul_eq_mul_div, lt_div_iff₀ hcp]
      nlinarith
    have : y ≤ K * m := by
      by_contra h
      push_neg at h
      nlinarith [mul_nonneg hK0 (zero_le_one.trans hm1)]
    have : K * m ≤ C' * m := by
      have : 0 ≤ 1 / (2 * c_p) := by positivity
      nlinarith
    linarith

end LSBA
