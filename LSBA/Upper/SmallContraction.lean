import LSBA.Upper.SmallCutField
import LSBA.Upper.ChosenGeneratorExists

/-!
# Lemma 8.12 [up:lem:small-contraction]: Gaussian divergence bounds at small coupling

Lemma 8.12 [up:lem:small-contraction] with `J = [-2 + κ₀, 2 - κ₀]`, in the form of the hypotheses
of Lemma 8.11 [up:lem:angular]. Regime (i): `0 < α < β < 1/2`, `ε > 0`, `g = W^{-a}` with
`a ∈ [α, β]` and `𝔟 = W^{ε/2} W g²`. Regime (ii): `c_* > 0`, `0 < θ ≤ 1/100`, `g` in the
critical window (8.37) [eq:critical-window] and `𝔟 = W^{18θ}` ((8.38)
[up:eq:small-transfer-scales]). In each regime a local length `q ≥ 7`, a constant `C` and a width
threshold, depending only on the fixed parameters, serve every coupling in the range, every
`E ∈ J` and every incoming flag. The cutoff and the field are those of the proof (Section 9.3
[su:sec:generator-bounds]), built from Lemma 9.3 [su:lem:chosen-generator]; in regime (i) Lemma 9.3
[su:lem:chosen-generator]
is applied with `min(ε, ε₀)`, since `𝔟` increases with `ε` (Section 9.2
[su:sec:generator-choice]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The hypotheses of Lemma 8.11 [up:lem:angular] persist when `C 𝔟` increases. -/
theorem angularFieldAt_mono {W : ℕ} {g E : ℝ} {q : ℕ} {b C b' C' : ℝ} {x : IsoFlag W}
    {χ : Ω W q → ℝ} {Y : Ω W q → Ω W q} (h : AngularFieldAt W g E q b C x χ Y)
    (hb : C * b ≤ C' * b') : AngularFieldAt W g E q b' C' x χ Y := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6.trans (ENNReal.ofReal_le_ofReal hb)⟩

/-- Lemma 8.12 [up:lem:small-contraction], regime (i): `g = W^{-a}`, `a ∈ [α, β]`,
`𝔟 = W^{ε/2} W g²` ((8.38) [up:eq:small-transfer-scales]). -/
theorem small_contraction_weak (κ₀ α β ε : ℝ) (hκ₀ : 0 < κ₀) (hκ₂ : κ₀ < 2) (hα : 0 < α)
    (hαβ : α < β) (hβ : β < 1 / 2) (hε : 0 < ε) :
    ∃ q : ℕ, 7 ≤ q ∧ ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ a ∈ Set.Icc α β, ∀ E ∈ Set.Icc (-2 + κ₀) (2 - κ₀), ∀ x : IsoFlag W,
        ∃ (χ : Ω W q → ℝ) (Y : Ω W q → Ω W q),
          AngularFieldAt W ((W : ℝ) ^ (-a)) E q
            ((W : ℝ) ^ (ε / 2) * W * ((W : ℝ) ^ (-a)) ^ 2) C x χ Y := by
  obtain ⟨ε₀, hε₀, hgen⟩ := chosen_generator_weak κ₀ α β hκ₀ hκ₂ hα hαβ hβ
  have hε'0 : 0 < min ε ε₀ := lt_min hε hε₀
  have hε'le : min ε ε₀ ≤ ε := min_le_left _ _
  obtain ⟨q, hq, C, hC, W₀, hW₀⟩ := hgen (min ε ε₀) hε'0 (min_le_right _ _)
  obtain ⟨Cs, c, hCs, hc, hsc⟩ := angularFieldAt_smallCut C hC
  obtain ⟨C', hC', W₁, hW₁⟩ :=
    smallDivBound_weak_le Cs c C α β (min ε ε₀) hCs hc hC hα hαβ hβ hε'0
  refine ⟨q, hq, C', hC', max (max W₀ W₁) 1, fun W hW a ha E hE x => ?_⟩
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWW₀ : W₀ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWW₁ : W₁ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := lt_of_lt_of_le one_pos hWr
  obtain ⟨pre, Rf, vf, Kh, χh, hG⟩ := hW₀ W hWW₀ a ha E hE x
  have hg0 : 0 < (W : ℝ) ^ (-a) := Real.rpow_pos_of_pos hWpos _
  have hg1 : (W : ℝ) ^ (-a) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith [ha.1])
  have hσ : 0 ≤ ((W : ℝ) ^ (-a)) ^ 2 * (W : ℝ) ^ (min ε ε₀ / 4) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos hWpos _).le
  have hM : 0 ≤ (W : ℝ) ^ (min ε ε₀ / 800) := (Real.rpow_pos_of_pos hWpos _).le
  have hfield := hsc W q _ E _ _ x _ pre Rf vf Kh χh hW1 hq hg0 hg1 hσ hM hG
  refine ⟨_, _, angularFieldAt_mono hfield ?_⟩
  have hexp : (W : ℝ) ^ (min ε ε₀ / 2) ≤ (W : ℝ) ^ (ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hWr (by linarith)
  have hgsq : 0 ≤ (W : ℝ) * ((W : ℝ) ^ (-a)) ^ 2 := mul_nonneg hWpos.le (sq_nonneg _)
  calc (1 : ℝ) * _ = _ := one_mul _
    _ ≤ C' * ((W : ℝ) ^ (min ε ε₀ / 2) * W * ((W : ℝ) ^ (-a)) ^ 2) := hW₁ W hWW₁ a ha
    _ ≤ C' * ((W : ℝ) ^ (ε / 2) * W * ((W : ℝ) ^ (-a)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hC'.le
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right hexp hgsq

/-- Lemma 8.12 [up:lem:small-contraction], regime (ii): `g` in the critical window (8.37)
[eq:critical-window], `𝔟 = W^{18θ}` ((8.38) [up:eq:small-transfer-scales]). -/
theorem small_contraction_crit (κ₀ cs θ : ℝ) (hκ₀ : 0 < κ₀) (hκ₂ : κ₀ < 2) (hcs : 0 < cs)
    (hθ : 0 < θ) (hθ' : θ ≤ 1 / 100) :
    ∃ q : ℕ, 7 ≤ q ∧ ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ g : ℝ, cs * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ g → g ≤ (W : ℝ) ^ (-(1 / 2 : ℝ) + θ / 2) →
        ∀ E ∈ Set.Icc (-2 + κ₀) (2 - κ₀), ∀ x : IsoFlag W,
          ∃ (χ : Ω W q → ℝ) (Y : Ω W q → Ω W q),
            AngularFieldAt W g E q ((W : ℝ) ^ (18 * θ)) C x χ Y := by
  obtain ⟨q, hq, C, hC, W₀, hW₀⟩ := chosen_generator_crit κ₀ cs θ hκ₀ hκ₂ hcs hθ hθ'
  obtain ⟨Cs, c, hCs, hc, hsc⟩ := angularFieldAt_smallCut C hC
  obtain ⟨C', hC', W₁, hW₁⟩ := smallDivBound_crit_le Cs c C cs θ hCs hc hC hcs hθ hθ'
  refine ⟨q, hq, C', hC', max (max W₀ W₁) 1, fun W hW g hg₁ hg₂ E hE x => ?_⟩
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWW₀ : W₀ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWW₁ : W₁ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := lt_of_lt_of_le one_pos hWr
  obtain ⟨pre, Rf, vf, Kh, χh, hG⟩ := hW₀ W hWW₀ g hg₁ hg₂ E hE x
  have hg0 : 0 < g :=
    lt_of_lt_of_le (mul_pos hcs (Real.rpow_pos_of_pos hWpos _)) hg₁
  have hg1 : g ≤ 1 := by
    refine hg₂.trans ?_
    exact Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith)
  have hσ : 0 ≤ (W : ℝ) ^ (-1 + 14 * θ) := (Real.rpow_pos_of_pos hWpos _).le
  have hM : 0 ≤ C * (W : ℝ) ^ (2 * θ) :=
    mul_nonneg hC.le (Real.rpow_pos_of_pos hWpos _).le
  have hfield := hsc W q g E _ _ x _ pre Rf vf Kh χh hW1 hq hg0 hg1 hσ hM hG
  refine ⟨_, _, angularFieldAt_mono hfield ?_⟩
  rw [one_mul]
  exact hW₁ W hWW₁ g hg₁ hg₂

end LSBA
