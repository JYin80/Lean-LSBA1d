import LSBA.Model.Bulk
import LSBA.Model.Scales

/-!
# Deterministic steps of the proof of (3.11) [uv:eq:upper-count]

The scale `ℓ_{W,g,L}` inside and outside the cap case, the radius bounds `W(2⌈R⌉+1) ≤ W^τ ℓ_{W,g}`
for the radii (3.7) [eq:strong-radius]–(3.10) [eq:large-radius], and the inclusion of the set (1.16)
[eq:bulk-sampling] in the energy
windows of Theorems 3.2 [thm:sharp-small-upper]–3.4 [thm:large-upper], as used in the proof of the
upper bound of Theorem 1.4 [thm:main].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `ℓ_{W,g} = W · max{1, Wg²}`. -/
private lemma assemblyBounds_ellScale_eq (W : ℕ) (g : ℝ) :
    ellScale W g = (W : ℝ) * max 1 ((W : ℝ) * g ^ 2) := by
  unfold ellScale
  rw [mul_max_of_nonneg _ _ (Nat.cast_nonneg W)]
  congr 1
  · ring
  · ring

/-- For large `W`: `W ≥ 1`, `W^{τ/2} ≥ 6` and `log W ≤ W^{τ/4} / 2`. -/
private lemma assemblyBounds_eventually {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ W : ℕ in atTop, 1 ≤ W ∧ 6 ≤ (W : ℝ) ^ (τ / 2) ∧
      Real.log W ≤ (W : ℝ) ^ (τ / 4) / 2 := by
  have h1 : ∀ᶠ W : ℕ in atTop, 1 ≤ W := eventually_ge_atTop 1
  have h2 : ∀ᶠ W : ℕ in atTop, 6 ≤ (W : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (by linarith : 0 < τ / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 6
  have h3 : ∀ᶠ W : ℕ in atTop, Real.log W ≤ (W : ℝ) ^ (τ / 4) / 2 := by
    have h := (isLittleO_log_rpow_atTop (by linarith : 0 < τ / 4)).def
      (by norm_num : (0 : ℝ) < 1 / 2)
    have h' := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually h
    filter_upwards [h', eventually_ge_atTop 1] with W hW hW1
    have h0 : (0 : ℝ) ≤ (W : ℝ) ^ (τ / 4) := Real.rpow_nonneg (Nat.cast_nonneg W) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0] at hW
    calc Real.log W ≤ |Real.log W| := le_abs_self _
      _ ≤ 1 / 2 * (W : ℝ) ^ (τ / 4) := hW
      _ = (W : ℝ) ^ (τ / 4) / 2 := by ring
  filter_upwards [h1, h2, h3] with W a b c using ⟨a, b, c⟩

/-- Outside the cap case `L ≤ W^τ max{1, Wg²}`, `ℓ_{W,g,L} = ℓ_{W,g}` ((1.7) [eq:scales]). -/
theorem ellStar_eq_ellScale_of_lt {W L : ℕ} {g τ : ℝ} (hW : 1 ≤ W) (hτ : 0 ≤ τ)
    (h : (W : ℝ) ^ τ * max 1 ((W : ℝ) * g ^ 2) < L) : ellStar W L g = ellScale W g := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hP : (1 : ℝ) ≤ (W : ℝ) ^ τ := Real.one_le_rpow hW1 hτ
  have hM : (1 : ℝ) ≤ max 1 ((W : ℝ) * g ^ 2) := le_max_left _ _
  have hML : max 1 ((W : ℝ) * g ^ 2) < L := by nlinarith
  unfold ellStar
  rw [assemblyBounds_ellScale_eq]
  exact min_eq_right (mul_le_mul_of_nonneg_left hML.le (by linarith))

/-- In the cap case `L ≤ W^τ max{1, Wg²}`, the volume is at most `W^τ ℓ_{W,g,L}`. -/
theorem mul_le_rpow_mul_ellStar {W L : ℕ} {g τ : ℝ} (hW : 1 ≤ W) (hτ : 0 ≤ τ)
    (h : (L : ℝ) ≤ (W : ℝ) ^ τ * max 1 ((W : ℝ) * g ^ 2)) :
    ((L * W : ℕ) : ℝ) ≤ (W : ℝ) ^ τ * ellStar W L g := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hP : (1 : ℝ) ≤ (W : ℝ) ^ τ := Real.one_le_rpow hW1 hτ
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  unfold ellStar
  rw [assemblyBounds_ellScale_eq, mul_min_of_nonneg _ _ (by linarith), le_min_iff, Nat.cast_mul]
  constructor
  · have := mul_nonneg (sub_nonneg.2 hP) (mul_nonneg (by linarith : (0 : ℝ) ≤ W) hL)
    nlinarith
  · have := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ W)
    nlinarith

/-- Radius of Theorem 3.1 [thm:strong-upper], (3.7) [eq:strong-radius]: `W(2⌈R⌉+1) ≤ W^τ ℓ_{W,g}`
for large
`W`. -/
theorem upperRadius_strong {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ W : ℕ in atTop, ∀ g : ℝ,
      (W : ℝ) * (2 * ⌈(⌈Real.log W ^ 2⌉₊ : ℝ)⌉ + 1) ≤ (W : ℝ) ^ τ * ellScale W g := by
  filter_upwards [assemblyBounds_eventually hτ] with W ⟨hW, hx, hlog⟩ g
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set x : ℝ := (W : ℝ) ^ (τ / 2) with hxdef
  set y : ℝ := (W : ℝ) ^ (τ / 4) with hydef
  have hxy : y * y = x := by
    rw [hxdef, hydef, ← Real.rpow_add hW0]; congr 1; ring
  have hP : (W : ℝ) ^ τ = x * x := by
    rw [hxdef, ← Real.rpow_add hW0]; congr 1; ring
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  have hL2 : Real.log W ^ 2 ≤ x / 4 := by
    nlinarith [hxy]
  have hM : (1 : ℝ) ≤ max 1 ((W : ℝ) * g ^ 2) := le_max_left _ _
  rw [assemblyBounds_ellScale_eq, Int.ceil_natCast, Int.cast_natCast]
  have hc := Nat.ceil_lt_add_one (sq_nonneg (Real.log W))
  have key : 2 * (⌈Real.log W ^ 2⌉₊ : ℝ) + 1 ≤ (W : ℝ) ^ τ * max 1 ((W : ℝ) * g ^ 2) := by
    rw [hP]; nlinarith
  calc (W : ℝ) * (2 * (⌈Real.log W ^ 2⌉₊ : ℝ) + 1)
      ≤ (W : ℝ) * ((W : ℝ) ^ τ * max 1 ((W : ℝ) * g ^ 2)) :=
        mul_le_mul_of_nonneg_left key hW0.le
    _ = (W : ℝ) ^ τ * ((W : ℝ) * max 1 ((W : ℝ) * g ^ 2)) := by ring

/-- Radius of Theorem 3.2 [thm:sharp-small-upper], (3.8) [eq:sharp-small-radius] with `ε = τ/2`. -/
theorem upperRadius_sharpSmall {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ W : ℕ in atTop, ∀ g : ℝ,
      (W : ℝ) * (2 * ⌈(W : ℝ) ^ (τ / 2) * max 1 ((W : ℝ) * g ^ 2)⌉ + 1) ≤
        (W : ℝ) ^ τ * ellScale W g := by
  filter_upwards [assemblyBounds_eventually hτ] with W ⟨hW, hx, hlog⟩ g
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set x : ℝ := (W : ℝ) ^ (τ / 2) with hxdef
  have hP : (W : ℝ) ^ τ = x * x := by
    rw [hxdef, ← Real.rpow_add hW0]; congr 1; ring
  have hM : (1 : ℝ) ≤ max 1 ((W : ℝ) * g ^ 2) := le_max_left _ _
  set M : ℝ := max 1 ((W : ℝ) * g ^ 2) with hMdef
  rw [assemblyBounds_ellScale_eq]
  have hc := Int.ceil_lt_add_one (x * M)
  have h3 : 0 ≤ M * ((x - 3) * (x + 1)) := mul_nonneg (by linarith) (by nlinarith)
  have key : 2 * (⌈x * M⌉ : ℝ) + 1 ≤ (W : ℝ) ^ τ * M := by
    rw [hP]; nlinarith
  calc (W : ℝ) * (2 * (⌈x * M⌉ : ℝ) + 1)
      ≤ (W : ℝ) * ((W : ℝ) ^ τ * M) := mul_le_mul_of_nonneg_left key hW0.le
    _ = (W : ℝ) ^ τ * ((W : ℝ) * M) := by ring

/-- Radius of Theorem 3.3 [thm:compact-upper], (3.9) [eq:coarse-radius], on
`W^{-τ/8} ≤ g ≤ W^{τ/4}`. -/
theorem upperRadius_compact {τ : ℝ} (hτ : 0 < τ ∧ τ < 1) :
    ∀ᶠ W : ℕ in atTop, ∀ g : ℝ, (W : ℝ) ^ (-(τ / 8)) ≤ g → g ≤ (W : ℝ) ^ (τ / 4) →
      (W : ℝ) * (2 * ⌈(W : ℝ) * max (g ^ 2)⁻¹ (g ^ 4) * Real.log W ^ 2⌉ + 1) ≤
        (W : ℝ) ^ τ * ellScale W g := by
  filter_upwards [assemblyBounds_eventually hτ.1] with W ⟨hW, hx, hlog⟩ g hg1 hg2
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set x : ℝ := (W : ℝ) ^ (τ / 2) with hxdef
  set y : ℝ := (W : ℝ) ^ (τ / 4) with hydef
  set z : ℝ := (W : ℝ) ^ (τ / 8) with hzdef
  have hz0 : 0 < z := Real.rpow_pos_of_pos hW0 _
  have hxy : y * y = x := by
    rw [hxdef, hydef, ← Real.rpow_add hW0]; congr 1; ring
  have hyz : z * z = y := by
    rw [hydef, hzdef, ← Real.rpow_add hW0]; congr 1; ring
  have hP : (W : ℝ) ^ τ = x * x := by
    rw [hxdef, ← Real.rpow_add hW0]; congr 1; ring
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  have hL2 : Real.log W ^ 2 ≤ x / 4 := by
    nlinarith [hxy]
  have hzg : 1 ≤ z * g := by
    have h := mul_le_mul_of_nonneg_left hg1 hz0.le
    rwa [Real.rpow_neg hW0.le, ← hzdef, mul_inv_cancel₀ hz0.ne'] at h
  have hg0 : 0 < g := by
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith
  -- `g⁻⁴ ≤ x` and `g² ≤ x`
  have hxg : 1 ≤ x * g ^ 4 := by
    have h4 : 1 ≤ (z * g) ^ 4 := one_le_pow₀ hzg
    have : (z * g) ^ 4 = x * g ^ 4 := by
      rw [← hxy, ← hyz]; ring
    linarith
  have hg2x : g ^ 2 ≤ x := by
    have h := pow_le_pow_left₀ hg0.le hg2 2
    have : y ^ 2 = x := by rw [sq]; exact hxy
    linarith
  set M : ℝ := max 1 ((W : ℝ) * g ^ 2) with hMdef
  have hM : (1 : ℝ) ≤ M := le_max_left _ _
  have hMW : (W : ℝ) * g ^ 2 ≤ M := le_max_right _ _
  have hg2p : 0 < g ^ 2 := by positivity
  have hmax : (W : ℝ) * max (g ^ 2)⁻¹ (g ^ 4) ≤ x * M := by
    rw [mul_max_of_nonneg _ _ hW0.le]
    refine max_le ?_ ?_
    · -- `W g⁻² = W g² · g⁻⁴ ≤ x · W g²`
      have h1 : (g ^ 2)⁻¹ ≤ x * g ^ 2 := by
        rw [inv_le_iff_one_le_mul₀ hg2p]
        nlinarith
      calc (W : ℝ) * (g ^ 2)⁻¹ ≤ (W : ℝ) * (x * g ^ 2) :=
            mul_le_mul_of_nonneg_left h1 hW0.le
        _ = x * ((W : ℝ) * g ^ 2) := by ring
        _ ≤ x * M := mul_le_mul_of_nonneg_left hMW (by linarith)
    · have h1 : g ^ 4 ≤ x * g ^ 2 := by
        have : g ^ 4 = g ^ 2 * g ^ 2 := by ring
        rw [this]; nlinarith
      calc (W : ℝ) * g ^ 4 ≤ (W : ℝ) * (x * g ^ 2) :=
            mul_le_mul_of_nonneg_left h1 hW0.le
        _ = x * ((W : ℝ) * g ^ 2) := by ring
        _ ≤ x * M := mul_le_mul_of_nonneg_left hMW (by linarith)
  have hR : (W : ℝ) * max (g ^ 2)⁻¹ (g ^ 4) * Real.log W ^ 2 ≤ x * M * (x / 4) := by
    calc (W : ℝ) * max (g ^ 2)⁻¹ (g ^ 4) * Real.log W ^ 2
        ≤ x * M * Real.log W ^ 2 :=
          mul_le_mul_of_nonneg_right hmax (sq_nonneg _)
      _ ≤ x * M * (x / 4) := mul_le_mul_of_nonneg_left hL2 (by positivity)
  rw [assemblyBounds_ellScale_eq]
  have hc := Int.ceil_lt_add_one ((W : ℝ) * max (g ^ 2)⁻¹ (g ^ 4) * Real.log W ^ 2)
  have key : 2 * (⌈(W : ℝ) * max (g ^ 2)⁻¹ (g ^ 4) * Real.log W ^ 2⌉ : ℝ) + 1 ≤
      (W : ℝ) ^ τ * M := by
    rw [hP]
    have h3 : 0 ≤ (M - 1) * (x * x) := mul_nonneg (by linarith) (by positivity)
    nlinarith
  calc (W : ℝ) * (2 * (⌈(W : ℝ) * max (g ^ 2)⁻¹ (g ^ 4) * Real.log W ^ 2⌉ : ℝ) + 1)
      ≤ (W : ℝ) * ((W : ℝ) ^ τ * M) := mul_le_mul_of_nonneg_left key hW0.le
    _ = (W : ℝ) ^ τ * ((W : ℝ) * M) := by ring

/-- Radius of Theorem 3.4 [thm:large-upper], (3.10) [eq:large-radius], on `g ≥ 1`. -/
theorem upperRadius_large {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ W : ℕ in atTop, ∀ g : ℝ, 1 ≤ g →
      (W : ℝ) * (2 * ⌈(W : ℝ) * g ^ 2 * Real.log W ^ 2⌉ + 1) ≤ (W : ℝ) ^ τ * ellScale W g := by
  filter_upwards [assemblyBounds_eventually hτ] with W ⟨hW, hx, hlog⟩ g _
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set x : ℝ := (W : ℝ) ^ (τ / 2) with hxdef
  set y : ℝ := (W : ℝ) ^ (τ / 4) with hydef
  have hxy : y * y = x := by
    rw [hxdef, hydef, ← Real.rpow_add hW0]; congr 1; ring
  have hP : (W : ℝ) ^ τ = x * x := by
    rw [hxdef, ← Real.rpow_add hW0]; congr 1; ring
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  have hL2 : Real.log W ^ 2 ≤ x / 4 := by
    nlinarith [hxy]
  set M : ℝ := max 1 ((W : ℝ) * g ^ 2) with hMdef
  have hM : (1 : ℝ) ≤ M := le_max_left _ _
  have hMW : (W : ℝ) * g ^ 2 ≤ M := le_max_right _ _
  have hR : (W : ℝ) * g ^ 2 * Real.log W ^ 2 ≤ M * (x / 4) :=
    calc (W : ℝ) * g ^ 2 * Real.log W ^ 2 ≤ M * Real.log W ^ 2 :=
          mul_le_mul_of_nonneg_right hMW (sq_nonneg _)
      _ ≤ M * (x / 4) := mul_le_mul_of_nonneg_left hL2 (by linarith)
  rw [assemblyBounds_ellScale_eq]
  have hc := Int.ceil_lt_add_one ((W : ℝ) * g ^ 2 * Real.log W ^ 2)
  have key : 2 * (⌈(W : ℝ) * g ^ 2 * Real.log W ^ 2⌉ : ℝ) + 1 ≤ (W : ℝ) ^ τ * M := by
    rw [hP]
    have h3 : 0 ≤ (M - 1) * (x * x) := mul_nonneg (by linarith) (by positivity)
    nlinarith
  calc (W : ℝ) * (2 * (⌈(W : ℝ) * g ^ 2 * Real.log W ^ 2⌉ : ℝ) + 1)
      ≤ (W : ℝ) * ((W : ℝ) ^ τ * M) := mul_le_mul_of_nonneg_left key hW0.le
    _ = (W : ℝ) ^ τ * ((W : ℝ) * M) := by ring

/-- (1.14) [eq:bulk-bridge] at level `κ/2`: for `g ≤ κ²/16` or `g ≥ 32/κ²`, the set (1.16)
[eq:bulk-sampling] lies in `[-2+κ²/16, 2-κ²/16]`. -/
theorem bulkSet_subset_Icc_of_window {g κ : ℝ} (hg : 0 ≤ g) (hκ : 0 < κ ∧ κ < 1 / 2)
    {L₀ L : ℕ} (hL : L₀ ≤ L) (hw : g ≤ κ ^ 2 / 16 ∨ 32 / κ ^ 2 ≤ g) :
    bulkSet g κ L₀ L ⊆ Set.Icc (-2 + κ ^ 2 / 16) (2 - κ ^ 2 / 16) := by
  intro E hE
  unfold bulkSet at hE
  have hLL : ¬ L < L₀ := not_lt.mpr hL
  simp only [hLL, ↓reduceIte] at hE
  have e1 : (κ / 2) ^ 2 / 4 = κ ^ 2 / 16 := by ring
  have e2 : 8 / (κ / 2) ^ 2 = 32 / κ ^ 2 := by
    have : κ ≠ 0 := hκ.1.ne'
    field_simp
    ring
  have hgc : g ≤ (κ / 2) ^ 2 / 4 ∨ 8 / (κ / 2) ^ 2 ≤ g := by
    rw [e1, e2]; exact hw
  have h := bulk_window_explicit (κ / 2) ⟨by linarith [hκ.1], by linarith [hκ.2]⟩ g hg hgc E hE
  rw [e1] at h
  rw [Set.mem_Icc]
  exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩

/-- (1.12) [eq:bounded-physical-bulk]: the set (1.16) [eq:bulk-sampling] lies in `[-4, 4]`. -/
theorem bulkSet_subset_Icc_four {g κ : ℝ} (hg : 0 ≤ g) (hκ : 0 < κ) {L₀ L : ℕ} (hL : L₀ ≤ L) :
    bulkSet g κ L₀ L ⊆ Set.Icc (-4) 4 := by
  intro E hE
  unfold bulkSet at hE
  have hLL : ¬ L < L₀ := not_lt.mpr hL
  simp only [hLL, ↓reduceIte] at hE
  have hE' : κ / 2 ≤ Fdist g (-|E|) := hE
  by_contra hnot
  have h4 : 4 < |E| := by
    by_contra h
    rw [not_lt] at h
    exact hnot (abs_le.mp h)
  have hb := support_bound_le_four g hg
  have hnull := nuDyson_compl_support g hg
  have hsub : Set.Iic (-|E|) ⊆
      (Set.Icc (-((2 * g + 2) / max 1 g)) ((2 * g + 2) / max 1 g))ᶜ := by
    intro t ht
    simp only [Set.mem_Iic] at ht
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le]
    left
    linarith
  have h0 : nuDyson g (Set.Iic (-|E|)) = 0 := measure_mono_null hsub hnull
  have : Fdist g (-|E|) = 0 := by
    unfold Fdist
    rw [h0]; rfl
  linarith

end LSBA
