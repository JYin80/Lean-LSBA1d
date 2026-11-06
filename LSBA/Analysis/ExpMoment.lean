import Mathlib

/-!
# An exponential moment bound from two moments

For a real random variable `Y` with finite second moment under a probability measure,
`𝔼 e^{−Y} ≤ 1 − 𝔼Y + 𝔼Y² + 𝔼[e^{−Y}; Y < −1]`, from `e^{−x} ≤ 1 − x + x²` for `x ≥ −1`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- Elementary bound `e^{-y} ≤ 1 - y + y²` for `y ≥ -1`. -/
private lemma ExpMoment_exp_neg_le {y : ℝ} (hy : -1 ≤ y) :
    Real.exp (-y) ≤ 1 - y + y ^ 2 := by
  rcases le_or_gt 0 y with h0 | h0
  · -- case `0 ≤ y`: `e^{-y} (1 + y) ≤ 1 ≤ (1 - y + y²)(1 + y)`
    have h1 : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    have hpos : 0 < 1 + y := by linarith
    have hexp : Real.exp (-y) * (1 + y) ≤ 1 := by
      calc Real.exp (-y) * (1 + y) ≤ Real.exp (-y) * Real.exp y :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have hq : 1 ≤ (1 - y + y ^ 2) * (1 + y) := by nlinarith [pow_nonneg h0 3]
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [Real.exp_pos (-y)]
  · -- case `-1 ≤ y < 0`: `|-y| ≤ 1`, so `e^{-y} ≤ 1 - y + y²`
    have h := Real.abs_exp_sub_one_sub_id_le (x := -y) (by
      rw [abs_le]; constructor <;> linarith)
    have := (abs_le.mp h).2
    nlinarith [sq_nonneg y]

/-- `𝔼 e^{−Y} ≤ 1 − 𝔼Y + 𝔼Y² + 𝔼[e^{−Y}; Y < −1]` under a probability measure. -/
theorem lintegral_exp_neg_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Integrable Y P)
    (hY2 : Integrable (fun ω => Y ω ^ 2) P) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-Y ω)) ∂P ≤
      ENNReal.ofReal (1 - ∫ ω, Y ω ∂P + ∫ ω, Y ω ^ 2 ∂P) +
        ∫⁻ ω in {ω | Y ω < -1}, ENNReal.ofReal (Real.exp (-Y ω)) ∂P := by
  set s : Set Ω := {ω | Y ω < -1} with hs
  have h1Y : Integrable (fun ω => 1 - Y ω) P := (integrable_const (1 : ℝ)).sub hY
  have hq : Integrable (fun ω => 1 - Y ω + Y ω ^ 2) P := h1Y.add hY2
  have hqnn : 0 ≤ᵐ[P] fun ω => 1 - Y ω + Y ω ^ 2 :=
    Filter.Eventually.of_forall fun ω => by
      change (0 : ℝ) ≤ 1 - Y ω + Y ω ^ 2
      nlinarith [sq_nonneg (Y ω - 1 / 2)]
  have hint : ∫ ω, (1 - Y ω + Y ω ^ 2) ∂P = 1 - ∫ ω, Y ω ∂P + ∫ ω, Y ω ^ 2 ∂P := by
    rw [integral_add h1Y hY2, integral_sub (integrable_const (1 : ℝ)) hY]
    simp
  have hsm : NullMeasurableSet s P :=
    hY.aestronglyMeasurable.nullMeasurableSet_lt aestronglyMeasurable_const
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (-Y ω)) ≤
      ENNReal.ofReal (1 - Y ω + Y ω ^ 2) +
        s.indicator (fun ω => ENNReal.ofReal (Real.exp (-Y ω))) ω := by
    intro ω
    by_cases h : Y ω < -1
    · have : ω ∈ s := h
      rw [Set.indicator_of_mem this]
      exact le_add_self
    · have : ω ∉ s := h
      rw [Set.indicator_of_notMem this, add_zero]
      exact ENNReal.ofReal_le_ofReal (ExpMoment_exp_neg_le (not_lt.mp h))
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-Y ω)) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (1 - Y ω + Y ω ^ 2) +
        s.indicator (fun ω => ENNReal.ofReal (Real.exp (-Y ω))) ω) ∂P := lintegral_mono hpt
    _ = ∫⁻ ω, ENNReal.ofReal (1 - Y ω + Y ω ^ 2) ∂P +
        ∫⁻ ω, s.indicator (fun ω => ENNReal.ofReal (Real.exp (-Y ω))) ω ∂P :=
          lintegral_add_left' hq.aemeasurable.ennreal_ofReal _
    _ = ENNReal.ofReal (1 - ∫ ω, Y ω ∂P + ∫ ω, Y ω ^ 2 ∂P) +
        ∫⁻ ω in s, ENNReal.ofReal (Real.exp (-Y ω)) ∂P := by
          rw [lintegral_indicator₀ hsm, ← hint, ofReal_integral_eq_lintegral_ofReal hq hqnn]

end LSBA
