import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Absorbing a constant times a logarithm

For a fixed constant `C`, uniformly in `b ≥ 1`: `⌈C b log W⌉ ≤ W^δ b` for every fixed `δ > 0`,
and `⌈C b log W⌉ ≤ b (log W)²`, once `W` is large. These are the absorptions of the radius
`⌈C 𝔟 log W⌉` of (8.4) [uva:eq:conversion-radius] into (3.8) [eq:sharp-small-radius] and
(3.9) [eq:coarse-radius] (Section 8.5 [sec:upper-center-completion]).
-/

open Real

noncomputable section

namespace LSBA

/-- `⌈x⌉₊ ≤ y + 1` for `x ≤ y`, `0 ≤ y`. -/
private theorem logAbsorb_ceil_le {x y : ℝ} (hxy : x ≤ y) (hy : 0 ≤ y) :
    (⌈x⌉₊ : ℝ) ≤ y + 1 :=
  (Nat.cast_le.2 (Nat.ceil_mono hxy)).trans (Nat.ceil_lt_add_one hy).le

/-- `⌈C b log W⌉ ≤ W^δ b` for all `b ≥ 1` once `W` is large, for fixed `C` and `δ > 0`. -/
theorem ceil_mul_log_le_rpow_mul (C δ : ℝ) (hδ : 0 < δ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ b : ℝ, 1 ≤ b →
      (⌈C * b * Real.log W⌉₊ : ℝ) ≤ (W : ℝ) ^ δ * b := by
  set K := max C 0 with hK
  set M := 2 * K / δ + 1 with hM
  have hK0 : 0 ≤ K := le_max_right _ _
  have hM1 : 1 ≤ M := by
    have : 0 ≤ 2 * K / δ := by positivity
    linarith
  refine ⟨⌈M ^ (2 / δ)⌉₊ + 1, fun W hW b hb => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (show 1 ≤ W by omega)
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  set T := (W : ℝ) ^ (δ / 2) with hT
  have hTM : M ≤ T := by
    have h1 : M ^ (2 / δ) ≤ (W : ℝ) := by
      have := Nat.le_ceil (M ^ (2 / δ))
      have h2 : ((⌈M ^ (2 / δ)⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (show _ ≤ W by omega)
      linarith
    have h3 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ δ / 2)
    rwa [← Real.rpow_mul (by linarith), show 2 / δ * (δ / 2) = (1 : ℝ) by field_simp,
      Real.rpow_one] at h3
  have hTT : (W : ℝ) ^ δ = T * T := by
    rw [hT, ← Real.rpow_add' hW0 (by linarith)]
    ring_nf
  have hlog : Real.log W ≤ 2 / δ * T := by
    have := Real.log_le_rpow_div hW0 (half_pos hδ)
    rw [div_div_eq_mul_div] at this
    calc Real.log W ≤ T * 2 / δ := by simpa [hT] using this
      _ = 2 / δ * T := by ring
  have hkey : K * Real.log W + 1 ≤ (W : ℝ) ^ δ := by
    rw [hTT]
    have hT1 : 1 ≤ T := hM1.trans hTM
    calc K * Real.log W + 1 ≤ K * (2 / δ * T) + 1 := by gcongr
      _ = (2 * K / δ) * T + 1 := by ring
      _ ≤ (2 * K / δ) * T + T := by linarith
      _ = M * T := by rw [hM]; ring
      _ ≤ T * T := by gcongr
  have hb0 : 0 ≤ b := by linarith
  have hx : C * b * Real.log W ≤ K * b * Real.log W := by
    have := le_max_left C 0
    have : 0 ≤ b * Real.log W := mul_nonneg hb0 hlog0
    nlinarith
  calc (⌈C * b * Real.log W⌉₊ : ℝ) ≤ K * b * Real.log W + 1 :=
        logAbsorb_ceil_le hx (by positivity)
    _ ≤ b * (K * Real.log W + 1) := by nlinarith [mul_nonneg hK0 hlog0]
    _ ≤ b * (W : ℝ) ^ δ := by gcongr
    _ = (W : ℝ) ^ δ * b := by ring

/-- `⌈C b log W⌉ ≤ b (log W)²` for all `b ≥ 1` once `W` is large, for fixed `C`. -/
theorem ceil_mul_log_le_mul_log_sq (C : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ b : ℝ, 1 ≤ b →
      (⌈C * b * Real.log W⌉₊ : ℝ) ≤ b * Real.log W ^ 2 := by
  set K := max C 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  refine ⟨⌈Real.exp (K + 1)⌉₊ + 1, fun W hW b hb => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (show 1 ≤ W by omega)
  have hWpos : (0 : ℝ) < W := by linarith
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  have hlogK : K + 1 ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le hWpos]
    have := Nat.le_ceil (Real.exp (K + 1))
    have h2 : ((⌈Real.exp (K + 1)⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (show _ ≤ W by omega)
    linarith
  have hb0 : 0 ≤ b := by linarith
  have hx : C * b * Real.log W ≤ K * b * Real.log W := by
    have := le_max_left C 0
    have : 0 ≤ b * Real.log W := mul_nonneg hb0 hlog0
    nlinarith
  have hkey : K * Real.log W + 1 ≤ Real.log W ^ 2 := by nlinarith
  calc (⌈C * b * Real.log W⌉₊ : ℝ) ≤ K * b * Real.log W + 1 :=
        logAbsorb_ceil_le hx (by positivity)
    _ ≤ b * (K * Real.log W + 1) := by nlinarith [mul_nonneg hK0 hlog0]
    _ ≤ b * Real.log W ^ 2 := by gcongr

end LSBA
