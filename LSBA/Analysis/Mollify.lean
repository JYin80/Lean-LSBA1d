import Mathlib

/-!
# Smoothing of Lipschitz functions

On a finite-dimensional real inner product space, a `K`-Lipschitz function `f` and a radius
`r > 0` give a `C^∞` function that is again `K`-Lipschitz and whose value at every `x` lies
between two values of `f` on the closed ball of radius `r` about `x` (an average of `f` over that
ball). This is the mollification step of the cutoff in Appendix G.4 [app:compact-gaussian].
-/

open MeasureTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

namespace LSBA

/-- Mollification of a `K`-Lipschitz function at radius `r`: a `C^∞`, `K`-Lipschitz `g` such that
every value `g x` lies between two values of `f` within distance `r` of `x`. -/
theorem exists_contDiff_lipschitz_near {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {r : ℝ} (hr : 0 < r) :
    ∃ g : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ LipschitzWith K g ∧
      (∀ x, ∃ y, dist y x ≤ r ∧ g x ≤ f y) ∧ (∀ x, ∃ y, dist y x ≤ r ∧ f y ≤ g x) := by
  borelize E
  set μ : Measure E := Measure.addHaar with hμ
  set φ : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩ with hφ
  set ψ : E → ℝ := φ.normed μ with hψ
  have hψ0 : ∀ t, 0 ≤ ψ t := fun t => φ.nonneg_normed t
  have hψint : ∫ t, ψ t ∂μ = 1 := φ.integral_normed
  have hψsupp : ∀ t, ψ t ≠ 0 → ‖t‖ < r := by
    intro t ht
    have : t ∈ Function.support ψ := ht
    rw [hψ, φ.support_normed_eq] at this
    simpa using this
  have hψcs : HasCompactSupport ψ := φ.hasCompactSupport_normed
  have hψc : Continuous ψ := φ.continuous_normed
  have hfc : Continuous f := hf.continuous
  -- the integrand is integrable
  have hint : ∀ x, Integrable (fun t => ψ t * f (x - t)) μ := by
    intro x
    refine Continuous.integrable_of_hasCompactSupport
      (hψc.mul (hfc.comp (continuous_const.sub continuous_id))) ?_
    exact hψcs.mul_right
  refine ⟨fun x => ∫ t, ψ t * f (x - t) ∂μ, ?_, ?_, ?_, ?_⟩
  · exact hψcs.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) (n := (⊤ : ℕ∞))
      φ.contDiff_normed (hfc.locallyIntegrable (μ := μ))
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, ← integral_sub (hint x) (hint y)]
    have h1 : ∀ t, ‖ψ t * f (x - t) - ψ t * f (y - t)‖ ≤ ψ t * (K * dist x y) := by
      intro t
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (hψ0 t)]
      refine mul_le_mul_of_nonneg_left ?_ (hψ0 t)
      have := hf.dist_le_mul (x - t) (y - t)
      rw [dist_sub_right, dist_eq_norm] at this
      exact this
    calc |∫ t, (ψ t * f (x - t) - ψ t * f (y - t)) ∂μ|
        = ‖∫ t, (ψ t * f (x - t) - ψ t * f (y - t)) ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ t, ‖ψ t * f (x - t) - ψ t * f (y - t)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, ψ t * (K * dist x y) ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
            ((hψc.integrable_of_hasCompactSupport hψcs).mul_const _)
            (Filter.Eventually.of_forall h1)
      _ = K * dist x y := by rw [integral_mul_const, hψint, one_mul]
  · intro x
    obtain ⟨y, hy, hmax⟩ := (isCompact_closedBall x r).exists_isMaxOn
      (Metric.nonempty_closedBall.2 hr.le) hfc.continuousOn
    refine ⟨y, by simpa [Metric.mem_closedBall] using hy, ?_⟩
    calc ∫ t, ψ t * f (x - t) ∂μ ≤ ∫ t, ψ t * f y ∂μ := by
          refine integral_mono (hint x) ((hψc.integrable_of_hasCompactSupport hψcs).mul_const _)
            fun t => ?_
          by_cases ht : ψ t = 0
          · simp [ht]
          · refine mul_le_mul_of_nonneg_left ?_ (hψ0 t)
            refine hmax ?_
            have := hψsupp t ht
            simpa [Metric.mem_closedBall, dist_eq_norm] using this.le
      _ = f y := by rw [integral_mul_const, hψint, one_mul]
  · intro x
    obtain ⟨y, hy, hmin⟩ := (isCompact_closedBall x r).exists_isMinOn
      (Metric.nonempty_closedBall.2 hr.le) hfc.continuousOn
    refine ⟨y, by simpa [Metric.mem_closedBall] using hy, ?_⟩
    calc f y = ∫ t, ψ t * f y ∂μ := by rw [integral_mul_const, hψint, one_mul]
      _ ≤ ∫ t, ψ t * f (x - t) ∂μ := by
          refine integral_mono ((hψc.integrable_of_hasCompactSupport hψcs).mul_const _) (hint x)
            fun t => ?_
          by_cases ht : ψ t = 0
          · simp [ht]
          · refine mul_le_mul_of_nonneg_left ?_ (hψ0 t)
            refine hmin ?_
            have := hψsupp t ht
            simpa [Metric.mem_closedBall, dist_eq_norm] using this.le

end LSBA
