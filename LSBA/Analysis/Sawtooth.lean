import Mathlib

/-!
# The zero-mean primitive of a periodic function

For a continuous `2π`-periodic `f`, the sawtooth average
`S f (θ) = (2π)⁻¹ ∫_0^{2π} (t - π) f(θ + t) dt` is a primitive of `f - (2π)⁻¹ ∫_0^{2π} f`, and
if `f ≥ -ε` then `|S f| ≤ 2π ((2π)⁻¹ ∫_0^{2π} f + ε)`: the primitive has mean zero and its
oscillation is at most the integral of `f + ε` over one period. This is the primitive on each
circle in the proof of Lemma F.3 [lem:c-operators].
-/

open Real

noncomputable section

namespace LSBA

/-- The sawtooth average `S f (θ) = (2π)⁻¹ ∫_0^{2π} (t - π) f(θ + t) dt`. -/
def sawtooth (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), (t - π) * f (θ + t)

/-- For continuous `2π`-periodic `f`, `S f` is a primitive of `f - (2π)⁻¹ ∫_0^{2π} f`. -/
theorem hasDerivAt_sawtooth {f : ℝ → ℝ} (hf : Continuous f) (hper : Function.Periodic f (2 * π))
    (θ : ℝ) :
    HasDerivAt (sawtooth f) (f θ - (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), f t) θ := by
  have hc : Continuous fun s => s * f s := continuous_id.mul hf
  set c : ℝ := ∫ t in (0 : ℝ)..(2 * π), f t with hc_def
  set G : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, s * f s with hG
  have hGd : ∀ x, HasDerivAt G (x * f x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have hform : sawtooth f = fun θ => (2 * π)⁻¹ * (G (θ + 2 * π) - G θ - (θ + π) * c) := by
    funext θ
    have h1 : ∫ t in (0 : ℝ)..(2 * π), (t - π) * f (θ + t)
        = (∫ t in (0 : ℝ)..(2 * π), (θ + t) * f (θ + t))
          - (θ + π) * ∫ t in (0 : ℝ)..(2 * π), f (θ + t) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
      · congr 1; funext t; ring
      · exact (hc.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
      · exact ((hf.comp (continuous_const.add continuous_id)).const_mul _).intervalIntegrable _ _
    have h2 : (∫ t in (0 : ℝ)..(2 * π), (θ + t) * f (θ + t)) = G (θ + 2 * π) - G θ := by
      rw [intervalIntegral.integral_comp_add_left (fun s => s * f s) θ]
      simp only [hG, add_zero]
      rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
    have h3 : (∫ t in (0 : ℝ)..(2 * π), f (θ + t)) = c := by
      rw [intervalIntegral.integral_comp_add_left f θ, add_zero, hc_def]
      exact hper.intervalIntegral_add_eq θ 0 |>.trans (by simp)
    unfold sawtooth
    rw [h1, h2, h3]
  rw [hform]
  have h4 : HasDerivAt (fun θ => G (θ + 2 * π)) ((θ + 2 * π) * f (θ + 2 * π)) θ := by
    simpa using (hGd (θ + 2 * π)).comp_add_const θ (2 * π)
  have h5 : HasDerivAt (fun θ => (θ + π) * c) c θ := by
    simpa using ((hasDerivAt_id θ).add_const π).mul_const c
  have h6 := ((h4.sub (hGd θ)).sub h5).const_mul (2 * π)⁻¹
  convert h6 using 1
  rw [hper θ]
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- For continuous `2π`-periodic `f ≥ -ε`: `|S f| ≤ 2π ((2π)⁻¹ ∫_0^{2π} f + ε)`. -/
theorem abs_sawtooth_le {f : ℝ → ℝ} (hf : Continuous f) (hper : Function.Periodic f (2 * π))
    {ε : ℝ} (hfε : ∀ t, -ε ≤ f t) (θ : ℝ) :
    |sawtooth f θ| ≤ 2 * π * ((2 * π)⁻¹ * (∫ t in (0 : ℝ)..(2 * π), f t) + ε) := by
  have hc0 : Continuous fun t : ℝ => f t + ε := hf.add continuous_const
  have hg : ∀ t, 0 ≤ f t + ε := fun t => by linarith [hfε t]
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hcomp : Continuous fun t : ℝ => f (θ + t) + ε :=
    hc0.comp (continuous_const.add continuous_id)
  have hmean : (∫ t in (0 : ℝ)..(2 * π), (t - π)) = 0 := by
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
      intervalIntegrable_const]
    simp [integral_id]
    ring
  have hshift : (∫ t in (0 : ℝ)..(2 * π), (f (θ + t) + ε))
      = (∫ t in (0 : ℝ)..(2 * π), f t) + 2 * π * ε := by
    have hi : IntervalIntegrable (fun t => f (θ + t)) MeasureTheory.volume 0 (2 * π) :=
      (hf.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi intervalIntegrable_const,
      intervalIntegral.integral_comp_add_left f θ, add_zero]
    rw [hper.intervalIntegral_add_eq θ 0]
    simp
  have hK : 0 ≤ (∫ t in (0 : ℝ)..(2 * π), f t) + 2 * π * ε := by
    rw [← hshift]
    exact intervalIntegral.integral_nonneg (by positivity) (fun t _ => hg _)
  have h1 : (∫ t in (0 : ℝ)..(2 * π), (t - π) * f (θ + t))
      = ∫ t in (0 : ℝ)..(2 * π), (t - π) * (f (θ + t) + ε) := by
    have : (∫ t in (0 : ℝ)..(2 * π), (t - π) * (f (θ + t) + ε))
        = (∫ t in (0 : ℝ)..(2 * π), (t - π) * f (θ + t))
          + ε * ∫ t in (0 : ℝ)..(2 * π), (t - π) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
      · congr 1; funext t; ring
      · exact (((continuous_id.sub continuous_const).mul
          (hf.comp (continuous_const.add continuous_id)))).intervalIntegrable _ _
      · exact ((continuous_const.mul (continuous_id.sub continuous_const))).intervalIntegrable _ _
    rw [this, hmean, mul_zero, add_zero]
  have h2 : |∫ t in (0 : ℝ)..(2 * π), (t - π) * (f (θ + t) + ε)|
      ≤ ∫ t in (0 : ℝ)..(2 * π), π * (f (θ + t) + ε) := by
    refine (intervalIntegral.abs_integral_le_integral_abs (by positivity)).trans ?_
    refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ ?_
    · exact (((continuous_id.sub continuous_const).mul hcomp).abs).intervalIntegrable _ _
    · exact (continuous_const.mul hcomp).intervalIntegrable _ _
    · intro t ht
      have ht1 : |t - π| ≤ π := by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      rw [abs_mul, abs_of_nonneg (hg _)]
      exact mul_le_mul_of_nonneg_right ht1 (hg _)
  have h3 : (∫ t in (0 : ℝ)..(2 * π), π * (f (θ + t) + ε))
      = π * ((∫ t in (0 : ℝ)..(2 * π), f t) + 2 * π * ε) := by
    rw [intervalIntegral.integral_const_mul, hshift]
  unfold sawtooth
  rw [h1, abs_mul, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * π))]
  have h4 := h2.trans_eq h3
  have h5 : (2 * π)⁻¹ * |∫ t in (0 : ℝ)..(2 * π), (t - π) * (f (θ + t) + ε)|
      ≤ (2 * π)⁻¹ * (π * ((∫ t in (0 : ℝ)..(2 * π), f t) + 2 * π * ε)) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  refine h5.trans ?_
  have : 2 * π * ((2 * π)⁻¹ * (∫ t in (0 : ℝ)..(2 * π), f t) + ε)
      = (∫ t in (0 : ℝ)..(2 * π), f t) + 2 * π * ε := by
    field_simp
  rw [this]
  have : (2 * π)⁻¹ * (π * ((∫ t in (0 : ℝ)..(2 * π), f t) + 2 * π * ε))
      = ((∫ t in (0 : ℝ)..(2 * π), f t) + 2 * π * ε) / 2 := by
    field_simp
  rw [this]
  linarith

end LSBA
