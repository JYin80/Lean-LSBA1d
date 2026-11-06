import Mathlib

/-!
# Measurability of line derivatives of a measurable family

For a jointly measurable family `f_a`, measurable points `x a` and directions `d a`, the line
derivative `a ↦ ∂_{d a} f_a (x a)` is measurable on a measurable set where all these line
derivatives exist: there it is the limit of the difference quotients
`n (f_a (x a + n⁻¹ d a) - f_a (x a))`. No continuity in the parameter `a` is needed. This gives
the measurability of the Gaussian divergence (8.33) [up:eq:gaussian-divergence] of the cut field
of Lemma 8.12 [up:lem:small-contraction], whose cutoff, chart and source depend only measurably
on the preparation blocks.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace LSBA

/-- On a measurable set `S` where `f_a` has a line derivative at `x a` along `d a`, the line
derivative is a measurable function of `a`, for a jointly measurable family `f` and measurable
`x`, `d`. -/
theorem measurable_indicator_lineDeriv {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F] {f : α → E → F}
    (hf : Measurable (Function.uncurry f)) {x d : α → E}
    (hx : Measurable x) (hd : Measurable d) {S : Set α} (hS : MeasurableSet S)
    (hdiff : ∀ a ∈ S, LineDifferentiableAt ℝ (f a) (x a) (d a)) :
    Measurable (S.indicator fun a => lineDeriv ℝ (f a) (x a) (d a)) := by
  -- the step sizes `1 / (n + 1)`
  set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with ht
  have hevalm : ∀ s : ℝ, Measurable fun a => f a (x a + s • d a) := fun s =>
    hf.comp (measurable_id.prodMk (hx.add (hd.const_smul s)))
  have hgm : ∀ n, Measurable (S.indicator fun a =>
      (t n)⁻¹ • (f a (x a + t n • d a) - f a (x a))) := fun n => by
    refine Measurable.indicator (Measurable.const_smul ?_ _) hS
    have h0 := hevalm 0
    simp only [zero_smul, add_zero] at h0
    exact (hevalm (t n)).sub h0
  have ht0 : Tendsto t atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Eventually.of_forall fun n => by simp only [ht, Set.mem_Ioi]; positivity
  refine measurable_of_tendsto_metrizable hgm (tendsto_pi_nhds.2 fun a => ?_)
  by_cases ha : a ∈ S
  · simp only [Set.indicator_of_mem ha]
    exact ((hdiff a ha).hasLineDerivAt.tendsto_slope_zero_right).comp ht0
  · simp [Set.indicator_of_notMem ha]

end LSBA
