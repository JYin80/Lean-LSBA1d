import LSBA.Upper.AngularIBP

/-!
# Nonconcentration of the angular ratio

With `t = c₀ 𝔟^{-1/2}` and `c₀ = min{1, 1/(3√C)}`, the logarithmic ratio `log R_T(Y)` of the
proof of Lemma 8.11 [up:lem:angular] exceeds `t` in absolute value with probability at least `¼`,
for every fixed incoming flag.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `𝔼 |D| ≤ √M` on a probability space when `D` is measurable and `𝔼 D² ≤ M`. -/
private lemma nonconc_abs_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {D : α → ℝ} (hD : Measurable D) {M : ℝ} (hM : 0 ≤ M)
    (h : ∫⁻ ω, ‖D ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal M) :
    ∫ ω, |D ω| ∂μ ≤ Real.sqrt M := by
  have h1 : eLpNorm D 1 μ ≤ eLpNorm D 2 μ := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have h2 : eLpNorm D 2 μ ≤ ENNReal.ofReal (Real.sqrt M) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hD.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    have : ∫⁻ ω, ‖D ω‖ₑ ^ (2 : ℝ) ∂μ = ∫⁻ ω, ‖D ω‖ₑ ^ 2 ∂μ := by
      simp_rw [← ENNReal.rpow_natCast]; norm_num
    rw [this, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hM (by norm_num)]
    exact ENNReal.rpow_le_rpow h (by norm_num)
  have h3 : ∫ ω, |D ω| ∂μ = (eLpNorm D 1 μ).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm hD.aestronglyMeasurable,
      ← integral_norm_eq_lintegral_enorm hD.aestronglyMeasurable]
    simp_rw [Real.norm_eq_abs]
  rw [h3]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h1.trans h2)
  rwa [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at this

/-- Markov-type step of the proof of Lemma 8.11 [up:lem:angular]: the cutoff bound
`2 𝔼[χ 1{|L| ≤ t}] ≤ (3t/2) 𝔼|D|` for every `t > 0`, together with `𝔼 χ ≥ ½`, `0 ≤ χ ≤ 1` and
`𝔼 D² ≤ C 𝔟`, gives `P(|L| > c₀ 𝔟^{-1/2}) ≥ ¼`. -/
private lemma nonconc_core {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {χ D LA : α → ℝ} {b C : ℝ} (hb : 1 ≤ b) (hC : 0 < C)
    (hχm : Measurable χ) (hχ : ∀ ω, 0 ≤ χ ω ∧ χ ω ≤ 1) (hDm : Measurable D)
    (hint : (1 / 2 : ℝ) ≤ ∫ ω, χ ω ∂μ)
    (hD : ∫⁻ ω, ‖D ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * b)) (hLA : Measurable LA)
    (hibp : ∀ t : ℝ, 0 < t →
      2 * ∫ ω, χ ω * Set.indicator {ω | |LA ω| ≤ t} (fun _ => (1 : ℝ)) ω ∂μ ≤
        3 * t / 2 * ∫ ω, |D ω| ∂μ) :
    (1 / 4 : ℝ≥0∞) ≤ μ {ω | Real.sqrt (min 1 (1 / (9 * C))) / Real.sqrt b < |LA ω|} := by
  set c₀ := Real.sqrt (min 1 (1 / (9 * C))) with hc₀
  have hmin : 0 < min 1 (1 / (9 * C)) := lt_min one_pos (by positivity)
  have hc₀pos : 0 < c₀ := Real.sqrt_pos.mpr hmin
  have hbpos : 0 < Real.sqrt b := Real.sqrt_pos.mpr (by linarith)
  set t := c₀ / Real.sqrt b with ht
  have htpos : 0 < t := by positivity
  set A : Set α := {ω | |LA ω| ≤ t} with hA
  have hAm : MeasurableSet A := measurableSet_le hLA.abs measurable_const
  have h1 : ∫ ω, |D ω| ∂μ ≤ Real.sqrt (C * b) :=
    nonconc_abs_integral_le hDm (by positivity) hD
  have h2 : c₀ * Real.sqrt C ≤ 1 / 3 := by
    rw [hc₀, ← Real.sqrt_mul hmin.le]
    calc Real.sqrt (min 1 (1 / (9 * C)) * C) ≤ Real.sqrt (1 / 9) := by
          apply Real.sqrt_le_sqrt
          calc min 1 (1 / (9 * C)) * C ≤ 1 / (9 * C) * C :=
                mul_le_mul_of_nonneg_right (min_le_right _ _) hC.le
            _ = 1 / 9 := by field_simp
      _ = 1 / 3 := by
          rw [show (1 / 9 : ℝ) = (1 / 3) ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
  have h3 : 3 * t / 2 * ∫ ω, |D ω| ∂μ ≤ 1 / 2 := by
    have h4 : 3 * t / 2 * Real.sqrt (C * b) = 3 / 2 * (c₀ * Real.sqrt C) := by
      rw [Real.sqrt_mul hC.le, ht]; field_simp
    calc 3 * t / 2 * ∫ ω, |D ω| ∂μ ≤ 3 * t / 2 * Real.sqrt (C * b) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 3 / 2 * (c₀ * Real.sqrt C) := h4
      _ ≤ 1 / 2 := by linarith
  have h5 := (hibp t htpos).trans h3
  -- decomposition of `∫ χ`
  have hχint : Integrable χ μ :=
    Integrable.of_bound hχm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hχ ω).1]; exact (hχ ω).2)
  have hint1 : Integrable (fun ω => χ ω * Set.indicator A (fun _ => (1 : ℝ)) ω) μ :=
    Integrable.of_bound (hχm.mul (measurable_const.indicator hAm)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        have := (hχ ω)
        have h6 : |Set.indicator A (fun _ => (1 : ℝ)) ω| ≤ 1 := by
          by_cases hω : ω ∈ A <;> simp [hω]
        rw [abs_of_nonneg this.1]
        nlinarith [abs_nonneg (Set.indicator A (fun _ => (1 : ℝ)) ω)])
  have hint2 : Integrable (fun ω => χ ω * Set.indicator Aᶜ (fun _ => (1 : ℝ)) ω) μ :=
    Integrable.of_bound (hχm.mul (measurable_const.indicator hAm.compl)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        have := (hχ ω)
        have h6 : |Set.indicator Aᶜ (fun _ => (1 : ℝ)) ω| ≤ 1 := by
          by_cases hω : ω ∈ Aᶜ <;> simp [hω]
        rw [abs_of_nonneg this.1]
        nlinarith [abs_nonneg (Set.indicator Aᶜ (fun _ => (1 : ℝ)) ω)])
  have hsplit : ∫ ω, χ ω ∂μ =
      ∫ ω, χ ω * Set.indicator A (fun _ => (1 : ℝ)) ω ∂μ +
        ∫ ω, χ ω * Set.indicator Aᶜ (fun _ => (1 : ℝ)) ω ∂μ := by
    rw [← integral_add hint1 hint2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ A <;> simp [hω]
  have h7 : (1 / 4 : ℝ) ≤ ∫ ω, χ ω * Set.indicator Aᶜ (fun _ => (1 : ℝ)) ω ∂μ := by
    linarith
  have h8 : ∫ ω, χ ω * Set.indicator Aᶜ (fun _ => (1 : ℝ)) ω ∂μ ≤ μ.real Aᶜ := by
    have : ∫ ω, Set.indicator Aᶜ (fun _ => (1 : ℝ)) ω ∂μ = μ.real Aᶜ := by
      rw [integral_indicator_const _ hAm.compl]; simp
    rw [← this]
    refine integral_mono hint2 ((integrable_const (1 : ℝ)).indicator hAm.compl) fun ω => ?_
    have := hχ ω
    by_cases hω : ω ∈ Aᶜ
    · simpa [hω] using this.2
    · simp [hω]
  have hset : {ω | c₀ / Real.sqrt b < |LA ω|} = Aᶜ := by
    ext ω; simp [hA, ht]
  rw [hset]
  have h9 : (1 / 4 : ℝ) ≤ μ.real Aᶜ := h7.trans h8
  have h10 : ENNReal.ofReal (1 / 4) ≤ μ Aᶜ := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ Aᶜ)]
    exact ENNReal.ofReal_le_ofReal h9
  have : ENNReal.ofReal (1 / 4) = (1 / 4 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rwa [this] at h10

/-- `log R_T(Y)` of the proof of Lemma 8.11 [up:lem:angular] is measurable in the batch. -/
private lemma nonconc_measurable_logAngRatio {W : ℕ} (g E : ℝ) (q : ℕ) {h : IsoFlag W → ℝ}
    (hh : Measurable h) (r : ℝ) (y : IsoFlag W) : Measurable (logAngRatio W g E q h r y) := by
  have hBy := (measurable_batchMat W g E q).prodMk
    (measurable_const : Measurable fun _ : Ω W q => y)
  have h1 := (measurable_flagAct W).comp hBy
  have h2 := (measurable_volCocycle W).comp hBy
  have h1' : Measurable fun ω : Ω W q => flagAct (batchMat W g E q ω) y := h1
  have h2' : Measurable fun ω : Ω W q => volCocycle (batchMat W g E q ω) y := h2
  have h3 : Measurable fun ω : Ω W q =>
      Real.log (h (flagAct (batchMat W g E q ω) y)) := Real.measurable_log.comp (hh.comp h1')
  have h4 : Measurable fun ω : Ω W q =>
      -Real.log r - 2 * volCocycle (batchMat W g E q ω) y :=
    measurable_const.sub (h2'.const_mul 2)
  exact h4.add (h3.const_mul 4)

/-- Proof of Lemma 8.11 [up:lem:angular]: `P(|log R_T(Y)| > c₀ 𝔟^{-1/2}) ≥ ¼` with
`c₀ = √(min{1, 1/(9C)})`, for bounded measurable `h ≥ ε > 0` satisfying (8.25)
[up:eq:invariant-function] and `r > 0`. -/
theorem quarter_le_measure_logAngRatio {W : ℕ} {g E : ℝ} {q : ℕ} {b C : ℝ} {y : IsoFlag W}
    {χ : Ω W q → ℝ} {Y : Ω W q → Ω W q} (hfield : AngularFieldAt W g E q b C y χ Y)
    (hb : 1 ≤ b) (hC : 0 < C) {h : IsoFlag W → ℝ} (hh : IsBddMeas h) {ε : ℝ} (hε : 0 < ε)
    (hhε : ∀ z, ε ≤ h z) (hinv : IsSimulInvariant h) {r : ℝ} (hr : 0 < r) :
    (1 / 4 : ℝ≥0∞) ≤ μ W q {ω | Real.sqrt (min 1 (1 / (9 * C))) / Real.sqrt b <
      |logAngRatio W g E q h r y ω|} := by
  obtain ⟨hχm, hχ, -, hadm, hint, hD⟩ := id hfield
  exact nonconc_core hb hC hχm hχ hadm.1 hint hD
    (nonconc_measurable_logAngRatio g E q hh.1 r y)
    fun t ht => two_mul_integral_cutoff_le hfield hh hε hhε hinv hr ht

/-- The same with `K_out = 0`, for every bounded measurable `h ≥ ε > 0`. -/
theorem quarter_le_measure_logAngRatio_of_zero {W : ℕ} {g E : ℝ} {q : ℕ} {b C : ℝ}
    {y : IsoFlag W} {χ : Ω W q → ℝ} {Y : Ω W q → Ω W q}
    (hfield : AngularFieldZeroAt W g E q b C y χ Y) (hb : 1 ≤ b) (hC : 0 < C)
    {h : IsoFlag W → ℝ} (hh : IsBddMeas h) {ε : ℝ} (hε : 0 < ε) (hhε : ∀ z, ε ≤ h z) {r : ℝ}
    (hr : 0 < r) :
    (1 / 4 : ℝ≥0∞) ≤ μ W q {ω | Real.sqrt (min 1 (1 / (9 * C))) / Real.sqrt b <
      |logAngRatio W g E q h r y ω|} := by
  obtain ⟨hχm, hχ, -, hadm, hint, hD⟩ := id hfield
  exact nonconc_core hb hC hχm hχ hadm.1 hint hD
    (nonconc_measurable_logAngRatio g E q hh.1 r y)
    fun t ht => two_mul_integral_cutoff_le_of_zero hfield hh hε hhε hr ht

end LSBA
