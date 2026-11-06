import Mathlib

/-!
# The exponents of Lemma 8.12 [up:lem:small-contraction]

The bound of the Gaussian divergence of the cut field in the proof of Lemma 8.12
[up:lem:small-contraction], in terms of the constants `C_s, c` of Lemma 9.4 [us:lem:score], the
constant `C` of Lemma 9.3 [su:lem:chosen-generator], the rate `σ` and the bound `M₀`:
`C_s (6 C³ W σ + 2 C)` from the source energy (9.37) [su:eq:chosen-generator-cut-costs]–(9.38)
[su:eq:pair-source-energy], `C_s C W (1 + M₀²) σ` from the generator size (9.25)
[su:eq:pair-generator-size], `36 C⁴ W⁻¹ g⁴` from the terminal correction (Section 9.3
[su:sec:generator-bounds]) and the remainder `C_s W M₀ e^{-c W}`. In regime (i)
(`g = W^{-a}`, `σ = g² W^{ε/4}`, `M₀ = W^{ε/800}`) it is `≤ C' W^{ε/2} W g²`, (9.39)
[su:eq:local]; in regime (ii) (the critical window (8.37)
[eq:critical-window], `σ = W^{-1+14θ}`, `M₀ = C W^{2θ}`) it is `≤ C' W^{18θ}`, (9.40)
[nc:eq:finalscore]; uniformly in `a`, resp. `g`, for large `W`.
-/

open Real

noncomputable section

namespace LSBA

/-- The bound `C_s (6 C³ W σ + 2 C) + C_s C W (1 + M₀²) σ + 36 C⁴ W⁻¹ g⁴ + C_s W M₀ e^{-c W}` of
`𝔼 |δ_G(χ X)|²` in the proof of Lemma 8.12 [up:lem:small-contraction]. -/
def smallDivBound (Cs c C W g σ M₀ : ℝ) : ℝ :=
  Cs * (6 * C ^ 3 * W * σ + 2 * C) + Cs * C * W * (1 + M₀ ^ 2) * σ + 36 * C ^ 4 * W⁻¹ * g ^ 4 +
    Cs * W * M₀ * Real.exp (-c * W)

/-- Regime (i) of Lemma 8.12 [up:lem:small-contraction], (9.39)
[su:eq:local]: for `g = W^{-a}`, `σ = g² W^{ε/4}` and `M₀ = W^{ε/800}`, the bound is at most
`C' W^{ε/2} W g²`, uniformly in `a ∈ [α, β]` for large `W`. -/
theorem smallDivBound_weak_le (Cs c C α β ε : ℝ) (hCs : 0 < Cs) (hc : 0 < c) (hC : 0 < C)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 2) (hε : 0 < ε) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ a ∈ Set.Icc α β,
      smallDivBound Cs c C W ((W : ℝ) ^ (-a)) (((W : ℝ) ^ (-a)) ^ 2 * (W : ℝ) ^ (ε / 4))
          ((W : ℝ) ^ (ε / 800)) ≤
        C' * ((W : ℝ) ^ (ε / 2) * W * ((W : ℝ) ^ (-a)) ^ 2) := by
    have tail : ∀ (K : ℝ) (n : ℕ), ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        K * (W : ℝ) ^ n * Real.exp (-c * W) ≤ 1 := by
      intro K n
      have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
      have h2 := h.const_mul (K / c ^ n)
      rw [mul_zero] at h2
      obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.1 (h2.eventually (gt_mem_nhds one_pos))
      refine ⟨W₀, fun W hW => ?_⟩
      have := hW₀ W hW
      have e : K * (W : ℝ) ^ n * Real.exp (-c * W) =
          K / c ^ n * (((c * (W : ℝ)) ^ n) * Real.exp (-(c * (W : ℝ)))) := by
        rw [mul_pow, neg_mul]
        field_simp
      rw [e]
      exact this.le
    set m : ℕ := ⌈ε / 800⌉₊ with hm
    obtain ⟨W₀, hW₀⟩ := tail Cs (m + 1)
    refine ⟨6 * Cs * C ^ 3 + 2 * Cs * C + 2 * Cs * C + 36 * C ^ 4 + 1, by positivity,
      max W₀ 1, fun W hW a ha => ?_⟩
    have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
    have hWW₀ : W₀ ≤ W := le_trans (le_max_left _ _) hW
    have hx : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    have hx0 : (0 : ℝ) < W := lt_of_lt_of_le one_pos hx
    have ha0 : 0 ≤ a := le_trans hα.le ha.1
    have haβ : a ≤ β := ha.2
    set x : ℝ := (W : ℝ) with hxdef
    have mono : ∀ s t : ℝ, s ≤ t → x ^ s ≤ x ^ t :=
      fun s t h => Real.rpow_le_rpow_of_exponent_le hx h
    have hg2 : (x ^ (-a)) ^ 2 = x ^ (-(2 * a)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
    have hg0 : 0 ≤ x ^ (-a) := Real.rpow_nonneg hx0.le _
    have hg1 : x ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
    have hT1 : 1 ≤ x ^ (ε / 2) * x * (x ^ (-a)) ^ 2 := by
      have : x ^ (ε / 2) * x * (x ^ (-a)) ^ 2 = x ^ (ε / 2 + 1 + -(2 * a)) := by
        rw [hg2, Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_one]
      rw [this]
      exact Real.one_le_rpow hx (by linarith)
    set T : ℝ := x ^ (ε / 2) * x * (x ^ (-a)) ^ 2 with hT
    have hxe4 : 1 ≤ x ^ (ε / 4) := Real.one_le_rpow hx (by linarith)
    have hxx : x ^ (ε / 4) * x ^ (ε / 4) = x ^ (ε / 2) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have hM2 : (x ^ (ε / 800)) ^ 2 ≤ x ^ (ε / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      exact mono _ _ (by push_cast; linarith)
    have hWs : x * ((x ^ (-a)) ^ 2 * x ^ (ε / 4)) ≤ T := by
      have h1 : x ^ (ε / 4) ≤ x ^ (ε / 2) := mono _ _ (by linarith)
      have h2 : 0 ≤ x * (x ^ (-a)) ^ 2 := by positivity
      calc x * ((x ^ (-a)) ^ 2 * x ^ (ε / 4)) = (x * (x ^ (-a)) ^ 2) * x ^ (ε / 4) := by ring
        _ ≤ (x * (x ^ (-a)) ^ 2) * x ^ (ε / 2) := mul_le_mul_of_nonneg_left h1 h2
        _ = T := by rw [hT]; ring
    have hGen : x * (1 + (x ^ (ε / 800)) ^ 2) * ((x ^ (-a)) ^ 2 * x ^ (ε / 4)) ≤ 2 * T := by
      have h2 : 0 ≤ x * ((x ^ (-a)) ^ 2) := by positivity
      have hA : x * (1 + (x ^ (ε / 800)) ^ 2) * ((x ^ (-a)) ^ 2 * x ^ (ε / 4)) =
          (1 + (x ^ (ε / 800)) ^ 2) * (x * (x ^ (-a)) ^ 2) * x ^ (ε / 4) := by ring
      have hB : (1 + (x ^ (ε / 800)) ^ 2) * x ^ (ε / 4) ≤ 2 * x ^ (ε / 2) := by
        rw [← hxx]; nlinarith
      calc _ = (x * (x ^ (-a)) ^ 2) * ((1 + (x ^ (ε / 800)) ^ 2) * x ^ (ε / 4)) := by rw [hA]; ring
        _ ≤ (x * (x ^ (-a)) ^ 2) * (2 * x ^ (ε / 2)) := mul_le_mul_of_nonneg_left hB h2
        _ = 2 * T := by rw [hT]; ring
    have hInv : x⁻¹ * (x ^ (-a)) ^ 4 ≤ 1 := by
      have h4 : (x ^ (-a)) ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
      have h5 : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
      calc x⁻¹ * (x ^ (-a)) ^ 4 ≤ 1 * 1 :=
            mul_le_mul h5 h4 (by positivity) zero_le_one
        _ = 1 := by norm_num
    have hRem : Cs * x * x ^ (ε / 800) * Real.exp (-c * W) ≤ 1 := by
      have h1 : x ^ (ε / 800) ≤ x ^ (m : ℝ) :=
        mono _ _ (by rw [hm]; exact Nat.le_ceil _)
      rw [Real.rpow_natCast] at h1
      have h3 := hW₀ W hWW₀
      have h4 : Cs * x * x ^ (ε / 800) ≤ Cs * x ^ (m + 1) := by
        calc Cs * x * x ^ (ε / 800) ≤ Cs * x * x ^ m :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = Cs * x ^ (m + 1) := by ring
      calc Cs * x * x ^ (ε / 800) * Real.exp (-c * W)
          ≤ Cs * x ^ (m + 1) * Real.exp (-c * W) :=
            mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
        _ ≤ 1 := h3
    have hC3 : 0 < C ^ 3 := by positivity
    unfold smallDivBound
    have e1 : 6 * C ^ 3 * x * ((x ^ (-a)) ^ 2 * x ^ (ε / 4)) ≤ 6 * C ^ 3 * T := by
      calc 6 * C ^ 3 * x * ((x ^ (-a)) ^ 2 * x ^ (ε / 4))
          = 6 * C ^ 3 * (x * ((x ^ (-a)) ^ 2 * x ^ (ε / 4))) := by ring
        _ ≤ 6 * C ^ 3 * T := mul_le_mul_of_nonneg_left hWs (by positivity)
    have e3 : Cs * C * x * (1 + (x ^ (ε / 800)) ^ 2) * ((x ^ (-a)) ^ 2 * x ^ (ε / 4))
        ≤ Cs * C * (2 * T) := by
      calc Cs * C * x * (1 + (x ^ (ε / 800)) ^ 2) * ((x ^ (-a)) ^ 2 * x ^ (ε / 4))
          = Cs * C * (x * (1 + (x ^ (ε / 800)) ^ 2) * ((x ^ (-a)) ^ 2 * x ^ (ε / 4))) := by
            ring
        _ ≤ Cs * C * (2 * T) := mul_le_mul_of_nonneg_left hGen (by positivity)
    have e4 : 36 * C ^ 4 * x⁻¹ * (x ^ (-a)) ^ 4 ≤ 36 * C ^ 4 * T := by
      calc 36 * C ^ 4 * x⁻¹ * (x ^ (-a)) ^ 4 = 36 * C ^ 4 * (x⁻¹ * (x ^ (-a)) ^ 4) := by ring
        _ ≤ 36 * C ^ 4 * 1 := mul_le_mul_of_nonneg_left hInv (by positivity)
        _ ≤ 36 * C ^ 4 * T := mul_le_mul_of_nonneg_left hT1 (by positivity)
    have e2 : 2 * Cs * C ≤ 2 * Cs * C * T := by
      have : 0 ≤ 2 * Cs * C := by positivity
      nlinarith
    have e5 : Cs * x * x ^ (ε / 800) * Real.exp (-c * x) ≤ T := le_trans hRem hT1
    nlinarith [e1, e2, e3, e4, e5]

/-- Regime (ii) of Lemma 8.12 [up:lem:small-contraction], (9.40) [nc:eq:finalscore]: in the
critical window (8.37) [eq:critical-window], for `σ = W^{-1+14θ}` and `M₀ = C W^{2θ}`, the bound is
at most `C' W^{18θ}`, uniformly in `g` for large `W`. -/
theorem smallDivBound_crit_le (Cs c C cs θ : ℝ) (hCs : 0 < Cs) (hc : 0 < c) (hC : 0 < C)
    (hcs : 0 < cs) (hθ : 0 < θ) (hθ' : θ ≤ 1 / 100) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ g : ℝ,
      cs * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ g → g ≤ (W : ℝ) ^ (-(1 / 2 : ℝ) + θ / 2) →
      smallDivBound Cs c C W g ((W : ℝ) ^ (-1 + 14 * θ)) (C * (W : ℝ) ^ (2 * θ)) ≤
        C' * (W : ℝ) ^ (18 * θ) := by
    have tail : ∀ (K : ℝ) (n : ℕ), ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        K * (W : ℝ) ^ n * Real.exp (-c * W) ≤ 1 := by
      intro K n
      have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
      have h2 := h.const_mul (K / c ^ n)
      rw [mul_zero] at h2
      obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.1 (h2.eventually (gt_mem_nhds one_pos))
      refine ⟨W₀, fun W hW => ?_⟩
      have := hW₀ W hW
      have e : K * (W : ℝ) ^ n * Real.exp (-c * W) =
          K / c ^ n * (((c * (W : ℝ)) ^ n) * Real.exp (-(c * (W : ℝ)))) := by
        rw [mul_pow, neg_mul]
        field_simp
      rw [e]
      exact this.le
    obtain ⟨W₀, hW₀⟩ := tail (Cs * C) 2
    refine ⟨6 * Cs * C ^ 3 + 2 * Cs * C + Cs * C * (1 + C ^ 2) + 36 * C ^ 4 + 1,
      by positivity, max W₀ 1, fun W hW g hg1 hg2 => ?_⟩
    have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
    have hWW₀ : W₀ ≤ W := le_trans (le_max_left _ _) hW
    have hx : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    have hx0 : (0 : ℝ) < W := lt_of_lt_of_le one_pos hx
    set x : ℝ := (W : ℝ) with hxdef
    have mono : ∀ s t : ℝ, s ≤ t → x ^ s ≤ x ^ t :=
      fun s t h => Real.rpow_le_rpow_of_exponent_le hx h
    have hg0 : 0 ≤ g := le_trans (by positivity) hg1
    have hgle : g ≤ 1 := by
      refine le_trans hg2 ?_
      exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
    have hT1 : 1 ≤ x ^ (18 * θ) := Real.one_le_rpow hx (by linarith)
    set T : ℝ := x ^ (18 * θ) with hT
    have hWs : x * x ^ (-1 + 14 * θ) = x ^ (14 * θ) := by
      rw [← Real.rpow_one_add' hx0.le (by linarith)]; congr 1; ring
    have hM : x * x ^ (-1 + 14 * θ) * (C * x ^ (2 * θ)) ^ 2 = C ^ 2 * T := by
      have : (C * x ^ (2 * θ)) ^ 2 = C ^ 2 * x ^ (4 * θ) := by
        have h : (x ^ (2 * θ)) ^ 2 = x ^ (4 * θ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
        rw [mul_pow, h]
      rw [this, hWs, hT]
      have : x ^ (14 * θ) * x ^ (4 * θ) = x ^ (18 * θ) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      rw [← this]; ring
    have h14 : x ^ (14 * θ) ≤ T := mono _ _ (by linarith)
    have hInv : x⁻¹ * g ^ 4 ≤ 1 := by
      have h4 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hgle
      have h5 : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
      calc x⁻¹ * g ^ 4 ≤ 1 * 1 := mul_le_mul h5 h4 (by positivity) zero_le_one
        _ = 1 := by norm_num
    have hRem : Cs * x * (C * x ^ (2 * θ)) * Real.exp (-c * x) ≤ 1 := by
      have h1 : x ^ (2 * θ) ≤ x ^ (1 : ℝ) := mono _ _ (by linarith)
      rw [Real.rpow_one] at h1
      have h3 := hW₀ W hWW₀
      have h4 : Cs * x * (C * x ^ (2 * θ)) ≤ Cs * C * x ^ 2 := by
        calc Cs * x * (C * x ^ (2 * θ)) = Cs * C * (x * x ^ (2 * θ)) := by ring
          _ ≤ Cs * C * (x * x) := mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h1 hx0.le) (by positivity)
          _ = Cs * C * x ^ 2 := by ring
      calc Cs * x * (C * x ^ (2 * θ)) * Real.exp (-c * x)
          ≤ Cs * C * x ^ 2 * Real.exp (-c * x) :=
            mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
        _ ≤ 1 := h3
    unfold smallDivBound
    have e1 : 6 * C ^ 3 * x * x ^ (-1 + 14 * θ) ≤ 6 * C ^ 3 * T := by
      calc 6 * C ^ 3 * x * x ^ (-1 + 14 * θ) = 6 * C ^ 3 * (x * x ^ (-1 + 14 * θ)) := by ring
        _ = 6 * C ^ 3 * x ^ (14 * θ) := by rw [hWs]
        _ ≤ 6 * C ^ 3 * T := mul_le_mul_of_nonneg_left h14 (by positivity)
    have e3 : Cs * C * x * (1 + (C * x ^ (2 * θ)) ^ 2) * x ^ (-1 + 14 * θ)
        ≤ Cs * C * (1 + C ^ 2) * T := by
      have : Cs * C * x * (1 + (C * x ^ (2 * θ)) ^ 2) * x ^ (-1 + 14 * θ)
          = Cs * C * (x * x ^ (-1 + 14 * θ) + x * x ^ (-1 + 14 * θ) * (C * x ^ (2 * θ)) ^ 2) := by
        ring
      rw [this, hM, hWs]
      have : 0 ≤ Cs * C := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h14 this]
    have e4 : 36 * C ^ 4 * x⁻¹ * g ^ 4 ≤ 36 * C ^ 4 * T := by
      calc 36 * C ^ 4 * x⁻¹ * g ^ 4 = 36 * C ^ 4 * (x⁻¹ * g ^ 4) := by ring
        _ ≤ 36 * C ^ 4 * 1 := mul_le_mul_of_nonneg_left hInv (by positivity)
        _ ≤ 36 * C ^ 4 * T := mul_le_mul_of_nonneg_left hT1 (by positivity)
    have e2 : 2 * Cs * C ≤ 2 * Cs * C * T := by
      have : 0 ≤ 2 * Cs * C := by positivity
      nlinarith
    have e5 : Cs * x * (C * x ^ (2 * θ)) * Real.exp (-c * x) ≤ T := le_trans hRem hT1
    nlinarith [e1, e2, e3, e4, e5]

end LSBA
