import LSBA.Upper.VerticalBound
import LSBA.Upper.CircleMeasureBound
import LSBA.Analysis.LayerCakeL4

/-!
# The good part of the transfer operator

(F.6) [cc:eq:smoothing] in the lift form, under the law of the GUE inputs (Lemma F.3
[lem:c-operators] with the cutoff of Appendix G.5 [sec:c-component-proof]): for the batch
cutoff `χ_q` with `‖T‖ ≤ K` on its support and a cut lift of `√2 K_U` at the incoming flag with
`𝔼 |δ_G(χ X)|² ≤ b`, every bounded measurable `h` with angular `L⁴` norm at most `M` (Section
8.3 [sec:upper-inputs]) satisfies
`|𝔼[χ_q e^{-c/2} h(TU, TY)]| ≤ (4/3) K^{1/2} (1 + 2π A₀) M`, `A₀ = ½ K² (b^{1/2} + 2)`.
The law of the terminal flag under `χ_q dμ` has mass at most one and the vertical bound (F.8)
[cc:eq:vertical] with constant `A₀`, so it is at most `(1 + 2π A₀) sup_U m_U` on sets; the
layer-cake bound gives the angular `L⁴` norm, and `e^{-c/2} ≤ ‖T‖^{1/2}` by (F.2)
[cc:eq:boundc].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Helpers -/

/-- The generator `K_U` of the rotation of the circle is continuous in the base projection. -/
private theorem go_continuous_circleGen {W : ℕ} :
    Continuous fun P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => circleGen P := by
  unfold circleGen quotProj
  fun_prop

/-- The derivative along the circle of a `C¹` function of the projection pair is measurable on
the flags. -/
private theorem go_measurable_circleDeriv {W : ℕ}
    {ψ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) : Measurable (circleDeriv ψ : IsoFlag W → ℝ) := by
  have hg := go_continuous_circleGen (W := W)
  have h1 : Continuous fun y : IsoFlag W => fderiv ℝ ψ y.1 :=
    (hψ.continuous_fderiv one_ne_zero).comp continuous_subtype_val
  have h2 : Continuous fun y : IsoFlag W =>
      ((0 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
        circleGen y.1.1 * y.1.2 - y.1.2 * circleGen y.1.1) := by
    have hy1 : Continuous fun y : IsoFlag W => y.1.1 :=
      continuous_fst.comp continuous_subtype_val
    have hy2 : Continuous fun y : IsoFlag W => y.1.2 :=
      continuous_snd.comp continuous_subtype_val
    have hgy : Continuous fun y : IsoFlag W => circleGen y.1.1 := hg.comp hy1
    exact continuous_const.prodMk ((hgy.mul hy2).sub (hy2.mul hgy))
  exact (h1.clm_apply h2).measurable

/-- On a batch in `𝒢` with `‖T‖ ≤ K`, `e^{-c/2} ≤ K^{1/2}` ((F.2) [cc:eq:boundc]). -/
private theorem go_exp_le {W : ℕ} (hW : 1 ≤ W)
    {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hT : T ∈ isoGroup W) (x : IsoFlag W)
    {K : ℝ} (hK : ‖T‖ ≤ K) : Real.exp (-volCocycle T x / 2) ≤ Real.sqrt K := by
  have hne : T ≠ 0 := by
    rintro rfl
    have h := hT.2
    have : Nonempty (Fin 2 × Fin W) := ⟨(0, ⟨0, hW⟩)⟩
    rw [Matrix.det_zero] at h
    exact zero_ne_one h
  have hpos : 0 < ‖T‖ := norm_pos_iff.2 hne
  have hc := abs_volCocycle_le hT.1 x
  have h1 : -volCocycle T x / 2 ≤ Real.log ‖T‖ / 2 := by
    have := neg_abs_le (volCocycle T x)
    have := le_abs_self (-volCocycle T x)
    rw [abs_neg] at this
    linarith
  calc Real.exp (-volCocycle T x / 2) ≤ Real.exp (Real.log ‖T‖ / 2) := Real.exp_le_exp.2 h1
    _ = Real.sqrt ‖T‖ := by rw [Real.exp_half, Real.exp_log hpos]
    _ ≤ Real.sqrt K := Real.sqrt_le_sqrt hK

/-- (F.6) [cc:eq:smoothing] in the lift form: `|𝔼[χ_q e^{-c/2} h(TU, TY)]| ≤
(4/3) K^{1/2} (1 + 2π A₀) M` with `A₀ = ½ K² (b^{1/2} + 2)`, for bounded measurable `h` with
angular `L⁴` norm at most `M` (proof of Lemma F.3 [lem:c-operators]). -/
theorem abs_integral_goodPart_le {W n : ℕ} (hW : 1 ≤ W) {g E K b M : ℝ} {x : IsoFlag W}
    {χ : Ω W 1000 → ℝ} {Y : Ω W 1000 → Ω W 1000} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχ01 : ∀ ω, 0 ≤ χ ω ∧ χ ω ≤ 1)
    (hY : IsCutLift W 1000 (batchMat W g E 1000) (((Real.sqrt 2 : ℝ) : ℂ) • circleGen x.1.1) b χ
      Y)
    (hK : ∀ ω ∈ tsupport (batchCut W n χ), ‖batchMat W g E (1000 + n) ω‖ ≤ K)
    {h : IsoFlag W → ℝ} (hh : IsBddMeas h) (hM : 0 ≤ M) (h4 : AngL4Le h M) :
    |∫ ω, batchCut W n χ ω * (Real.exp (-volCocycle (batchMat W g E (1000 + n) ω) x / 2) *
        h (flagAct (batchMat W g E (1000 + n) ω) x)) ∂(μ W (1000 + n))| ≤
      4 / 3 * Real.sqrt K * (1 + 2 * π * (K ^ 2 * (Real.sqrt b + 2) / 2)) * M := by
  set A₀ : ℝ := K ^ 2 * (Real.sqrt b + 2) / 2 with hA₀def
  have hA₀ : 0 ≤ A₀ := by positivity
  have hqs := batchCut_spec (n := n) hχ hχc hχ01
  have hqm : Measurable (batchCut W n χ) := hqs.1.continuous.measurable
  have hfm : Measurable fun ω : Ω W (1000 + n) => ENNReal.ofReal (batchCut W n χ ω) :=
    ENNReal.measurable_ofReal.comp hqm
  have hφ : Measurable fun ω : Ω W (1000 + n) => flagAct (batchMat W g E (1000 + n) ω) x := by
    have h1 : Measurable fun ω : Ω W (1000 + n) => (batchMat W g E (1000 + n) ω, x) :=
      (measurable_batchMat W g E (1000 + n)).prodMk measurable_const
    have h2 := (measurable_flagAct W).comp h1
    exact h2
  set ν : Measure (IsoFlag W) :=
    ((μ W (1000 + n)).withDensity fun ω => ENNReal.ofReal (batchCut W n χ ω)).map
      fun ω => flagAct (batchMat W g E (1000 + n) ω) x with hν
  have hνuniv : ν Set.univ ≤ 1 := by
    rw [hν, Measure.map_apply hφ MeasurableSet.univ, Set.preimage_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ ω, ENNReal.ofReal (batchCut W n χ ω) ∂(μ W (1000 + n))
        ≤ ∫⁻ _, 1 ∂(μ W (1000 + n)) :=
          lintegral_mono fun ω => ENNReal.ofReal_le_one.2 (hqs.2.2 ω).2
      _ = 1 := by simp
  have : IsFiniteMeasure ν := ⟨lt_of_le_of_lt hνuniv ENNReal.one_lt_top⟩
  have hvert : ∀ ψ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ, ContDiff ℝ 1 ψ →
      ∀ S : ℝ, (∀ y : IsoFlag W, |ψ y.1| ≤ S) → |∫ y, circleDeriv ψ y ∂ν| ≤ A₀ * S := by
    intro ψ hψ S hS
    have h1 : ∫ y, circleDeriv ψ y ∂ν = ∫ ω, batchCut W n χ ω *
        circleDeriv ψ (flagAct (batchMat W g E (1000 + n) ω) x) ∂(μ W (1000 + n)) := by
      rw [hν, integral_map hφ.aemeasurable (go_measurable_circleDeriv hψ).aestronglyMeasurable,
        integral_withDensity_eq_integral_toReal_smul hfm
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp [ENNReal.toReal_ofReal (hqs.2.2 ω).1]
    rw [h1]
    exact abs_integral_circleDeriv_le hχ hχc hχ01 hY hK hψ hS
  have hset : ∀ S : Set (IsoFlag W), MeasurableSet S →
      ν S ≤ ENNReal.ofReal (1 + 2 * π * A₀) * ⨆ y, circleMeasure y S := fun S hS =>
    measure_le_of_circleDeriv_le hW hνuniv hA₀ hvert hS
  have hm : ∀ y : IsoFlag W, circleMeasure y Set.univ ≤ 1 := fun y => by
    have := isProbabilityMeasure_circleMeasure y
    simp
  have hA : 0 ≤ 1 + 2 * π * A₀ := by positivity
  have hlay := lintegral_enorm_le_of_measure_le_iSup (m := fun y : IsoFlag W => circleMeasure y)
    hm hA hM hset hh.1 h4
  have hlν : ∫⁻ y, ‖h y‖ₑ ∂ν = ∫⁻ ω, ENNReal.ofReal (batchCut W n χ ω) *
      ‖h (flagAct (batchMat W g E (1000 + n) ω) x)‖ₑ ∂(μ W (1000 + n)) := by
    have hg : Measurable fun ω : Ω W (1000 + n) =>
        ‖h (flagAct (batchMat W g E (1000 + n) ω) x)‖ₑ := hh.1.enorm.comp hφ
    rw [hν, lintegral_map hh.1.enorm hφ, lintegral_withDensity_eq_lintegral_mul _ hfm hg]
    rfl
  have hpt : ∀ ω : Ω W (1000 + n), ENNReal.ofReal ‖batchCut W n χ ω *
      (Real.exp (-volCocycle (batchMat W g E (1000 + n) ω) x / 2) *
        h (flagAct (batchMat W g E (1000 + n) ω) x))‖ ≤
      ENNReal.ofReal (Real.sqrt K) * (ENNReal.ofReal (batchCut W n χ ω) *
        ‖h (flagAct (batchMat W g E (1000 + n) ω) x)‖ₑ) := by
    intro ω
    by_cases h0 : batchCut W n χ ω = 0
    · simp [h0]
    · have hexp := go_exp_le hW (batchMat_mem_isoGroup W g E (1000 + n) ω) x
        (hK ω (subset_tsupport _ h0))
      have hq0 := (hqs.2.2 ω).1
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hq0, abs_of_nonneg (Real.exp_pos _).le, Real.enorm_eq_ofReal_abs,
        ← ENNReal.ofReal_mul hq0, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_nonneg hq0 (abs_nonneg (h (flagAct (batchMat W g E (1000 + n) ω) x)))
      nlinarith
  have hbound : ∫⁻ ω, ENNReal.ofReal ‖batchCut W n χ ω *
      (Real.exp (-volCocycle (batchMat W g E (1000 + n) ω) x / 2) *
        h (flagAct (batchMat W g E (1000 + n) ω) x))‖ ∂(μ W (1000 + n)) ≤
      ENNReal.ofReal (Real.sqrt K * (4 / 3 * (1 + 2 * π * A₀) * M)) := by
    calc _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.sqrt K) * (ENNReal.ofReal (batchCut W n χ ω) *
          ‖h (flagAct (batchMat W g E (1000 + n) ω) x)‖ₑ) ∂(μ W (1000 + n)) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (Real.sqrt K) * ∫⁻ y, ‖h y‖ₑ ∂ν := by
          rw [hlν, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (Real.sqrt K) * ENNReal.ofReal (4 / 3 * (1 + 2 * π * A₀) * M) :=
          mul_le_mul_right hlay _
      _ = _ := (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
  have hnn : 0 ≤ Real.sqrt K * (4 / 3 * (1 + 2 * π * A₀) * M) := by positivity
  calc |∫ ω, batchCut W n χ ω * (Real.exp (-volCocycle (batchMat W g E (1000 + n) ω) x / 2) *
        h (flagAct (batchMat W g E (1000 + n) ω) x)) ∂(μ W (1000 + n))|
      = ‖∫ ω, batchCut W n χ ω * (Real.exp (-volCocycle (batchMat W g E (1000 + n) ω) x / 2) *
        h (flagAct (batchMat W g E (1000 + n) ω) x)) ∂(μ W (1000 + n))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ _ := norm_integral_le_lintegral_norm _
    _ ≤ (ENNReal.ofReal (Real.sqrt K * (4 / 3 * (1 + 2 * π * A₀) * M))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = Real.sqrt K * (4 / 3 * (1 + 2 * π * A₀) * M) := ENNReal.toReal_ofReal hnn
    _ = 4 / 3 * Real.sqrt K * (1 + 2 * π * (K ^ 2 * (Real.sqrt b + 2) / 2)) * M := by
        rw [hA₀def]; ring

end LSBA
