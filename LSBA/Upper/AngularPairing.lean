import LSBA.Upper.AngularNonconc
import LSBA.Analysis.QuarticDeficit
import LSBA.Transfer.CircleJacobian

/-!
# The angular `L⁴` pairing

The dual pairing in the proof of Lemma 8.11 [up:lem:angular]: for a density `ρ` on the circle
`𝒞_U`, `∫ ρ^{3/4} P_{1/2} h dm_U = ∫ ρ 𝔼 R_T^{1/4} dm_U ≤ 1 - c/𝔟`, from the Jacobian
(8.36) [cc:eq:jac], the quartic deficit and the nonconcentration bound.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `ofReal (1/4) = 1/4` in `ℝ≥0∞`. -/
private lemma angPair_ofReal_quarter : ENNReal.ofReal (1 / 4) = (1 / 4 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

/-- Pointwise step of the proof of Lemma 8.11 [up:lem:angular] (the quartic deficit weighted by
`ρ(Y)`): with `r = ρ(Y)`, `c = c(T; U, Y)`, `v = h(TU, TY)` and
`L = log R_T(Y) = -log r - 2c + 4 log v`,
`r^{3/4} e^{-c/2} v + r (t²/32) 1{t < |L|} ≤ ¾ r + ¼ v⁴ e^{-2c}`. -/
private lemma angPair_scalar {r c v t : ℝ} (hr : 0 < r) (hv : 0 < v) (ht : 0 < t) (ht1 : t ≤ 1) :
    r ^ (3 / 4 : ℝ) * (Real.exp (-c / 2) * v) +
        (if t < |-Real.log r - 2 * c + 4 * Real.log v| then r * (t ^ 2 / 32) else 0) ≤
      3 / 4 * r + 1 / 4 * (v ^ 4 * Real.exp (-2 * c)) := by
  set L := -Real.log r - 2 * c + 4 * Real.log v with hL
  set R := Real.exp L with hR
  have hRpos : 0 < R := Real.exp_pos _
  have hlogR : Real.log R = L := Real.log_exp L
  have hR14 : R ^ (1 / 4 : ℝ) = Real.exp (L / 4) := by
    rw [Real.rpow_def_of_pos hRpos, hlogR]; congr 1; ring
  have hr34 : r ^ (3 / 4 : ℝ) = Real.exp (Real.log r * (3 / 4)) := Real.rpow_def_of_pos hr _
  have hv4 : Real.exp (4 * Real.log v) = v ^ 4 := by
    have := Real.exp_nat_mul (Real.log v) 4
    rw [Real.exp_log hv] at this
    simpa using this
  have e1 : r * R = v ^ 4 * Real.exp (-2 * c) := by
    calc r * R = Real.exp (Real.log r) * Real.exp L := by rw [Real.exp_log hr]
      _ = Real.exp (Real.log r + L) := (Real.exp_add _ _).symm
      _ = Real.exp (4 * Real.log v + -2 * c) := by congr 1; rw [hL]; ring
      _ = v ^ 4 * Real.exp (-2 * c) := by rw [Real.exp_add, hv4]
  have e2 : r * R ^ (1 / 4 : ℝ) = r ^ (3 / 4 : ℝ) * (Real.exp (-c / 2) * v) := by
    calc r * R ^ (1 / 4 : ℝ) = Real.exp (Real.log r) * Real.exp (L / 4) := by
          rw [Real.exp_log hr, hR14]
      _ = Real.exp (Real.log r + L / 4) := (Real.exp_add _ _).symm
      _ = Real.exp (Real.log r * (3 / 4) + -c / 2 + Real.log v) := by
          congr 1; rw [hL]; ring
      _ = r ^ (3 / 4 : ℝ) * (Real.exp (-c / 2) * v) := by
          rw [Real.exp_add, Real.exp_add, hr34, mul_assoc]
          congr 2
          exact Real.exp_log hv
  have key : r * (3 / 4 + R / 4 - R ^ (1 / 4 : ℝ)) =
      3 / 4 * r + 1 / 4 * (v ^ 4 * Real.exp (-2 * c)) -
        r ^ (3 / 4 : ℝ) * (Real.exp (-c / 2) * v) := by
    linear_combination (1 / 4 : ℝ) * e1 - e2
  have hD0 : 0 ≤ r * (3 / 4 + R / 4 - R ^ (1 / 4 : ℝ)) :=
    mul_nonneg hr.le (quarticDeficit_nonneg hRpos.le)
  by_cases hA : t < |L|
  · have hD := sq_div_le_quarticDeficit hRpos ht ht1 (by rw [hlogR]; exact hA)
    have := mul_le_mul_of_nonneg_left hD hr.le
    simp only [hA, ↓reduceIte]
    linarith
  · simp only [hA, ↓reduceIte]
    linarith

/-- `(Y, ω) ↦ T(ω) Y` is measurable on the product of the circle and the batch space. -/
private lemma angPair_measurable_flag {W : ℕ} (g E : ℝ) (q : ℕ) :
    Measurable fun p : IsoFlag W × Ω W q => flagAct (batchMat W g E q p.2) p.1 := by
  have hp := (((measurable_batchMat W g E q).comp measurable_snd).prodMk
    (measurable_fst : Measurable fun p : IsoFlag W × Ω W q => p.1))
  have h1 := (measurable_flagAct W).comp hp
  exact h1

/-- `(Y, ω) ↦ c(T(ω); U, Y)` is measurable on the product of the circle and the batch space. -/
private lemma angPair_measurable_cocycle {W : ℕ} (g E : ℝ) (q : ℕ) :
    Measurable fun p : IsoFlag W × Ω W q => volCocycle (batchMat W g E q p.2) p.1 := by
  have hp := (((measurable_batchMat W g E q).comp measurable_snd).prodMk
    (measurable_fst : Measurable fun p : IsoFlag W × Ω W q => p.1))
  have h1 := (measurable_volCocycle W).comp hp
  exact h1

/-- For a fixed `Y`, `ω ↦ T(ω) Y` is measurable. -/
private lemma angPair_measurable_flag_fiber {W : ℕ} (g E : ℝ) (q : ℕ) (y : IsoFlag W) :
    Measurable fun ω : Ω W q => flagAct (batchMat W g E q ω) y := by
  have hy : Measurable fun ω : Ω W q => (y, ω) := measurable_const.prodMk measurable_id
  have h1 := (angPair_measurable_flag (W := W) g E q).comp hy
  exact h1

/-- For a fixed `Y`, `ω ↦ c(T(ω); U, Y)` is measurable. -/
private lemma angPair_measurable_cocycle_fiber {W : ℕ} (g E : ℝ) (q : ℕ) (y : IsoFlag W) :
    Measurable fun ω : Ω W q => volCocycle (batchMat W g E q ω) y := by
  have hy : Measurable fun ω : Ω W q => (y, ω) := measurable_const.prodMk measurable_id
  have h1 := (angPair_measurable_cocycle (W := W) g E q).comp hy
  exact h1

/-- `log R_T(Y)` of the proof of Lemma 8.11 [up:lem:angular] is measurable in the batch. -/
private lemma angPair_measurable_logAngRatio {W : ℕ} (g E : ℝ) (q : ℕ) {h : IsoFlag W → ℝ}
    (hh : Measurable h) (r : ℝ) (y : IsoFlag W) : Measurable (logAngRatio W g E q h r y) := by
  have h2 := angPair_measurable_cocycle_fiber g E q y
  have h3 : Measurable fun ω : Ω W q => Real.log (h (flagAct (batchMat W g E q ω) y)) :=
    Real.measurable_log.comp (hh.comp (angPair_measurable_flag_fiber g E q y))
  exact (measurable_const.sub (h2.const_mul 2)).add (h3.const_mul 4)

/-- The fibre inequality of the proof of Lemma 8.11 [up:lem:angular] over one incoming point `Y`
with `r = ρ(Y) > 0`: if `P(|log R_T(Y)| > t) ≥ ¼` with `t² = min{1, 1/(9C)}/𝔟`, then
`𝔼 ρ^{3/4} e^{-c/2} h(TY) + c r/𝔟 ≤ ¾ r + ¼ 𝔼 h(TY)⁴ e^{-2c}` with `c = angularConst C`. -/
private lemma angPair_fiber {W : ℕ} {g E : ℝ} {q : ℕ} {b C : ℝ} (hb : 1 ≤ b) (hC : 0 < C)
    {h : IsoFlag W → ℝ} (hhm : Measurable h) {ε : ℝ} (hε : 0 < ε) (hhε : ∀ z, ε ≤ h z)
    (y : IsoFlag W) {r : ℝ} (hr : 0 < r)
    (hq : (1 / 4 : ℝ≥0∞) ≤ μ W q {ω | Real.sqrt (min 1 (1 / (9 * C))) / Real.sqrt b <
      |logAngRatio W g E q h r y ω|}) :
    ∫⁻ ω, ENNReal.ofReal (r ^ (3 / 4 : ℝ) * (Real.exp (-volCocycle (batchMat W g E q ω) y / 2) *
        h (flagAct (batchMat W g E q ω) y))) ∂(μ W q) +
      ENNReal.ofReal (angularConst C / b) * ENNReal.ofReal r ≤
    ENNReal.ofReal (3 / 4) * ENNReal.ofReal r + ENNReal.ofReal (1 / 4) *
      ∫⁻ ω, ENNReal.ofReal (h (flagAct (batchMat W g E q ω) y) ^ 4) *
        ENNReal.ofReal (Real.exp (-2 * volCocycle (batchMat W g E q ω) y)) ∂(μ W q) := by
  have hm : 0 < min 1 (1 / (9 * C)) := lt_min one_pos (by positivity)
  have hbpos : 0 < Real.sqrt b := Real.sqrt_pos.mpr (by linarith)
  set t := Real.sqrt (min 1 (1 / (9 * C))) / Real.sqrt b with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hbpos]
    exact (Real.sqrt_le_one.mpr (min_le_left _ _)).trans (Real.one_le_sqrt.mpr hb)
  have hk : r * (t ^ 2 / 32) * (1 / 4) = angularConst C / b * r := by
    have : t ^ 2 = min 1 (1 / (9 * C)) / b := by
      rw [ht, div_pow, Real.sq_sqrt hm.le, Real.sq_sqrt (by linarith)]
    rw [this]; unfold angularConst; field_simp; ring
  have hf := angPair_measurable_flag_fiber g E q y
  have hc := angPair_measurable_cocycle_fiber g E q y
  have hhf : Measurable fun ω : Ω W q => h (flagAct (batchMat W g E q ω) y) := hhm.comp hf
  have hAm : MeasurableSet {ω | t < |logAngRatio W g E q h r y ω|} :=
    measurableSet_lt measurable_const (angPair_measurable_logAngRatio g E q hhm r y).abs
  have hFm : Measurable fun ω : Ω W q => ENNReal.ofReal (r ^ (3 / 4 : ℝ) *
      (Real.exp (-volCocycle (batchMat W g E q ω) y / 2) *
        h (flagAct (batchMat W g E q ω) y))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((Real.measurable_exp.comp ((hc.neg).div_const 2)).mul hhf))
  have hpt : ∀ ω : Ω W q, ENNReal.ofReal (r ^ (3 / 4 : ℝ) *
      (Real.exp (-volCocycle (batchMat W g E q ω) y / 2) * h (flagAct (batchMat W g E q ω) y))) +
      Set.indicator {ω | t < |logAngRatio W g E q h r y ω|}
        (fun _ => ENNReal.ofReal (r * (t ^ 2 / 32))) ω ≤
      ENNReal.ofReal (3 / 4) * ENNReal.ofReal r + ENNReal.ofReal (1 / 4) *
        (ENNReal.ofReal (h (flagAct (batchMat W g E q ω) y) ^ 4) *
          ENNReal.ofReal (Real.exp (-2 * volCocycle (batchMat W g E q ω) y))) := by
    intro ω
    have hv : 0 < h (flagAct (batchMat W g E q ω) y) := lt_of_lt_of_le hε (hhε _)
    have hs := angPair_scalar (c := volCocycle (batchMat W g E q ω) y) hr hv ht0 ht1
    have hRHS : ENNReal.ofReal (3 / 4) * ENNReal.ofReal r + ENNReal.ofReal (1 / 4) *
        (ENNReal.ofReal (h (flagAct (batchMat W g E q ω) y) ^ 4) *
          ENNReal.ofReal (Real.exp (-2 * volCocycle (batchMat W g E q ω) y))) =
        ENNReal.ofReal (3 / 4 * r + 1 / 4 * (h (flagAct (batchMat W g E q ω) y) ^ 4 *
          Real.exp (-2 * volCocycle (batchMat W g E q ω) y))) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity)]
    rw [hRHS]
    have hnn : 0 ≤ r ^ (3 / 4 : ℝ) * (Real.exp (-volCocycle (batchMat W g E q ω) y / 2) *
        h (flagAct (batchMat W g E q ω) y)) := by positivity
    by_cases hA : ω ∈ {ω | t < |logAngRatio W g E q h r y ω|}
    · rw [Set.indicator_of_mem hA, ← ENNReal.ofReal_add hnn (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hA' : t < |-Real.log r - 2 * volCocycle (batchMat W g E q ω) y +
          4 * Real.log (h (flagAct (batchMat W g E q ω) y))| := hA
      simp only [hA', ↓reduceIte] at hs
      exact hs
    · rw [Set.indicator_of_notMem hA, add_zero]
      refine ENNReal.ofReal_le_ofReal ?_
      have hA' : ¬ t < |-Real.log r - 2 * volCocycle (batchMat W g E q ω) y +
          4 * Real.log (h (flagAct (batchMat W g E q ω) y))| := hA
      simp only [hA', ↓reduceIte, add_zero] at hs
      exact hs
  have hint := lintegral_mono (μ := μ W q) hpt
  rw [lintegral_add_left hFm, lintegral_add_left measurable_const, lintegral_const,
    measure_univ, mul_one, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_indicator_const hAm] at hint
  refine le_trans (add_le_add le_rfl ?_) hint
  have hb0 : 0 < b := by linarith
  have hk0 : 0 ≤ angularConst C / b := by unfold angularConst; positivity
  calc ENNReal.ofReal (angularConst C / b) * ENNReal.ofReal r
      = ENNReal.ofReal (angularConst C / b * r) := (ENNReal.ofReal_mul hk0).symm
    _ = ENNReal.ofReal (r * (t ^ 2 / 32)) * ENNReal.ofReal (1 / 4) := by
        rw [← hk, ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (r * (t ^ 2 / 32)) * (1 / 4 : ℝ≥0∞) := by rw [angPair_ofReal_quarter]
    _ ≤ ENNReal.ofReal (r * (t ^ 2 / 32)) * μ W q {ω | t < |logAngRatio W g E q h r y ω|} :=
        mul_le_mul' le_rfl hq

/-- The duality step of the proof of Lemma 8.11 [up:lem:angular] (8.36) [cc:eq:jac]: the pairing
`∫ ρ^{3/4} P_{1/2} h dm_U ≤ 1 - c/𝔟`, given the quarter bound
`P(|log R_T(Y)| > t) ≥ ¼` at every point with `ρ(Y) > 0`. -/
private lemma angPair_core {W : ℕ} {g E : ℝ} {q : ℕ} {b C : ℝ} (hb : 1 ≤ b) (hC : 0 < C)
    {h : IsoFlag W → ℝ} (hh : IsBddMeas h) {ε : ℝ} (hε : 0 < ε) (hhε : ∀ z, ε ≤ h z)
    (hL4 : AngL4Le h 1) (x : IsoFlag W) {ρ : IsoFlag W → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂(circleMeasure x) = 1)
    (hq : ∀ y, 0 < ρ y → (1 / 4 : ℝ≥0∞) ≤ μ W q {ω | Real.sqrt (min 1 (1 / (9 * C))) /
      Real.sqrt b < |logAngRatio W g E q h (ρ y) y ω|}) :
    ∫⁻ y, ENNReal.ofReal (ρ y ^ (3 / 4 : ℝ) * halfOp W g E q h y) ∂(circleMeasure x) ≤
      ENNReal.ofReal (1 - angularConst C / b) := by
  have := isProbabilityMeasure_circleMeasure x
  have hb0 : 0 < b := by linarith
  have hk0 : 0 ≤ angularConst C / b := by unfold angularConst; positivity
  have hρ' : Measurable fun y => ENNReal.ofReal (ρ y) := ENNReal.measurable_ofReal.comp hρm
  -- the pairing is bounded by the lower integral over the batch
  have h1 : ∀ y, ENNReal.ofReal (ρ y ^ (3 / 4 : ℝ) * halfOp W g E q h y) ≤
      ∫⁻ ω, ENNReal.ofReal (ρ y ^ (3 / 4 : ℝ) *
        (Real.exp (-volCocycle (batchMat W g E q ω) y / 2) *
          h (flagAct (batchMat W g E q ω) y))) ∂(μ W q) := by
    intro y
    have hf := angPair_measurable_flag_fiber g E q y
    have hc := angPair_measurable_cocycle_fiber g E q y
    have hGm : Measurable fun ω : Ω W q => ρ y ^ (3 / 4 : ℝ) *
        (Real.exp (-volCocycle (batchMat W g E q ω) y / 2) *
          h (flagAct (batchMat W g E q ω) y)) :=
      measurable_const.mul ((Real.measurable_exp.comp ((hc.neg).div_const 2)).mul (hh.1.comp hf))
    have hG0 : ∀ ω : Ω W q, 0 ≤ ρ y ^ (3 / 4 : ℝ) *
        (Real.exp (-volCocycle (batchMat W g E q ω) y / 2) *
          h (flagAct (batchMat W g E q ω) y)) := fun ω =>
      mul_nonneg (Real.rpow_nonneg (hρ0 y) _)
        (mul_nonneg (Real.exp_pos _).le (lt_of_lt_of_le hε (hhε _)).le)
    have hhalf : ρ y ^ (3 / 4 : ℝ) * halfOp W g E q h y = ∫ ω, ρ y ^ (3 / 4 : ℝ) *
        (Real.exp (-volCocycle (batchMat W g E q ω) y / 2) *
          h (flagAct (batchMat W g E q ω) y)) ∂(μ W q) := by
      unfold halfOp
      rw [integral_const_mul]
    rw [hhalf, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hG0) hGm.aestronglyMeasurable]
    exact ENNReal.ofReal_toReal_le
  -- the fibre inequality at every point
  have h2 : ∀ y, ∫⁻ ω, ENNReal.ofReal (ρ y ^ (3 / 4 : ℝ) *
        (Real.exp (-volCocycle (batchMat W g E q ω) y / 2) *
          h (flagAct (batchMat W g E q ω) y))) ∂(μ W q) +
      ENNReal.ofReal (angularConst C / b) * ENNReal.ofReal (ρ y) ≤
      ENNReal.ofReal (3 / 4) * ENNReal.ofReal (ρ y) + ENNReal.ofReal (1 / 4) *
        ∫⁻ ω, ENNReal.ofReal (h (flagAct (batchMat W g E q ω) y) ^ 4) *
          ENNReal.ofReal (Real.exp (-2 * volCocycle (batchMat W g E q ω) y)) ∂(μ W q) := by
    intro y
    by_cases hy : 0 < ρ y
    · exact angPair_fiber hb hC hh.1 hε hhε y hy (hq y hy)
    · have h0 : ρ y = 0 := le_antisymm (not_lt.mp hy) (hρ0 y)
      rw [h0]
      simp [Real.zero_rpow (by norm_num : (3 / 4 : ℝ) ≠ 0)]
  -- the Jacobian (8.36) [cc:eq:jac] bounds the quartic average by `1`
  have h3 : ∫⁻ y, ∫⁻ ω, ENNReal.ofReal (h (flagAct (batchMat W g E q ω) y) ^ 4) *
      ENNReal.ofReal (Real.exp (-2 * volCocycle (batchMat W g E q ω) y)) ∂(μ W q)
        ∂(circleMeasure x) ≤ 1 := by
    have hmeas : Measurable (Function.uncurry fun (y : IsoFlag W) (ω : Ω W q) =>
        ENNReal.ofReal (h (flagAct (batchMat W g E q ω) y) ^ 4) *
          ENNReal.ofReal (Real.exp (-2 * volCocycle (batchMat W g E q ω) y))) := by
      have hf := angPair_measurable_flag (W := W) g E q
      have hc := angPair_measurable_cocycle (W := W) g E q
      have h4 : Measurable fun p : IsoFlag W × Ω W q =>
          h (flagAct (batchMat W g E q p.2) p.1) := hh.1.comp hf
      exact (ENNReal.measurable_ofReal.comp (h4.pow_const 4)).mul
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hc.const_mul (-2))))
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    calc ∫⁻ ω, ∫⁻ y, ENNReal.ofReal (h (flagAct (batchMat W g E q ω) y) ^ 4) *
          ENNReal.ofReal (Real.exp (-2 * volCocycle (batchMat W g E q ω) y))
            ∂(circleMeasure x) ∂(μ W q)
        ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂(μ W q) := by
          refine lintegral_mono fun ω => ?_
          have hT := (batchMat_mem_isoGroup W g E q ω).1
          have hφ : Measurable fun z : IsoFlag W => ENNReal.ofReal (h z ^ 4) :=
            ENNReal.measurable_ofReal.comp (hh.1.pow_const 4)
          have hJ := lintegral_circleMeasure_flagAct hT x hφ
          rw [hJ]
          have hL := hL4 (flagAct (batchMat W g E q ω) x)
          rw [ENNReal.ofReal_one, one_pow] at hL
          refine le_trans (le_of_eq ?_) hL
          refine lintegral_congr fun z => ?_
          have hz : 0 ≤ h z := (lt_of_lt_of_le hε (hhε z)).le
          rw [Real.enorm_of_nonneg hz, ENNReal.ofReal_pow hz]
      _ = 1 := by simp
  -- integrate the fibre inequality against `m_U`
  have h4 : ∫⁻ y, ∫⁻ ω, ENNReal.ofReal (ρ y ^ (3 / 4 : ℝ) *
        (Real.exp (-volCocycle (batchMat W g E q ω) y / 2) *
          h (flagAct (batchMat W g E q ω) y))) ∂(μ W q) ∂(circleMeasure x) +
      ENNReal.ofReal (angularConst C / b) ≤ 1 := by
    calc _ = ∫⁻ y, ∫⁻ ω, ENNReal.ofReal (ρ y ^ (3 / 4 : ℝ) *
              (Real.exp (-volCocycle (batchMat W g E q ω) y / 2) *
                h (flagAct (batchMat W g E q ω) y))) ∂(μ W q) ∂(circleMeasure x) +
            ENNReal.ofReal (angularConst C / b) *
              ∫⁻ y, ENNReal.ofReal (ρ y) ∂(circleMeasure x) := by rw [hρ1, mul_one]
      _ = ∫⁻ y, (∫⁻ ω, ENNReal.ofReal (ρ y ^ (3 / 4 : ℝ) *
              (Real.exp (-volCocycle (batchMat W g E q ω) y / 2) *
                h (flagAct (batchMat W g E q ω) y))) ∂(μ W q) +
            ENNReal.ofReal (angularConst C / b) * ENNReal.ofReal (ρ y)) ∂(circleMeasure x) := by
          rw [lintegral_add_right _ (hρ'.const_mul _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ∫⁻ y, (ENNReal.ofReal (3 / 4) * ENNReal.ofReal (ρ y) + ENNReal.ofReal (1 / 4) *
            ∫⁻ ω, ENNReal.ofReal (h (flagAct (batchMat W g E q ω) y) ^ 4) *
              ENNReal.ofReal (Real.exp (-2 * volCocycle (batchMat W g E q ω) y))
                ∂(μ W q)) ∂(circleMeasure x) := lintegral_mono h2
      _ = ENNReal.ofReal (3 / 4) * 1 + ENNReal.ofReal (1 / 4) *
            ∫⁻ y, ∫⁻ ω, ENNReal.ofReal (h (flagAct (batchMat W g E q ω) y) ^ 4) *
              ENNReal.ofReal (Real.exp (-2 * volCocycle (batchMat W g E q ω) y))
                ∂(μ W q) ∂(circleMeasure x) := by
          rw [lintegral_add_left (hρ'.const_mul _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hρ1]
      _ ≤ ENNReal.ofReal (3 / 4) * 1 + ENNReal.ofReal (1 / 4) * 1 := by gcongr
      _ = 1 := by
          rw [mul_one, mul_one, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  calc _ ≤ ∫⁻ y, ∫⁻ ω, ENNReal.ofReal (ρ y ^ (3 / 4 : ℝ) *
          (Real.exp (-volCocycle (batchMat W g E q ω) y / 2) *
            h (flagAct (batchMat W g E q ω) y))) ∂(μ W q) ∂(circleMeasure x) :=
        lintegral_mono h1
    _ ≤ 1 - ENNReal.ofReal (angularConst C / b) :=
        ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top h4
    _ = ENNReal.ofReal (1 - angularConst C / b) := by
        rw [ENNReal.ofReal_sub 1 hk0, ENNReal.ofReal_one]

/-- Proof of Lemma 8.11 [up:lem:angular]: if every incoming flag carries a cutoff and field, then
for bounded measurable `h ≥ ε > 0` satisfying (8.25) [up:eq:invariant-function] with angular
`L⁴` norm at most `1`, and every density `ρ ≥ 0` on the circle through the base of `x`,
`∫ ρ^{3/4} P_{1/2} h dm_U ≤ 1 - c/𝔟` with `c = angularConst C`. -/
theorem lintegral_rpow_mul_halfOp_le {W : ℕ} {g E : ℝ} {q : ℕ} {b C : ℝ}
    (hfield : ∀ y : IsoFlag W, ∃ χ Y, AngularFieldAt W g E q b C y χ Y) (hb : 1 ≤ b)
    (hC : 0 < C) {h : IsoFlag W → ℝ} (hh : IsBddMeas h) {ε : ℝ} (hε : 0 < ε)
    (hhε : ∀ z, ε ≤ h z) (hinv : IsSimulInvariant h) (hL4 : AngL4Le h 1) (x : IsoFlag W)
    {ρ : IsoFlag W → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂(circleMeasure x) = 1) :
    ∫⁻ y, ENNReal.ofReal (ρ y ^ (3 / 4 : ℝ) * halfOp W g E q h y) ∂(circleMeasure x) ≤
      ENNReal.ofReal (1 - angularConst C / b) := by
  refine angPair_core hb hC hh hε hhε hL4 x hρm hρ0 hρ1 fun y hy => ?_
  obtain ⟨χ, Y, hf⟩ := hfield y
  exact quarter_le_measure_logAngRatio hf hb hC hh hε hhε hinv hy

/-- The same with `K_out = 0`, for every bounded measurable `h ≥ ε > 0` with angular `L⁴` norm
at most `1`. -/
theorem lintegral_rpow_mul_halfOp_le_of_zero {W : ℕ} {g E : ℝ} {q : ℕ} {b C : ℝ}
    (hfield : ∀ y : IsoFlag W, ∃ χ Y, AngularFieldZeroAt W g E q b C y χ Y) (hb : 1 ≤ b)
    (hC : 0 < C) {h : IsoFlag W → ℝ} (hh : IsBddMeas h) {ε : ℝ} (hε : 0 < ε)
    (hhε : ∀ z, ε ≤ h z) (hL4 : AngL4Le h 1) (x : IsoFlag W)
    {ρ : IsoFlag W → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂(circleMeasure x) = 1) :
    ∫⁻ y, ENNReal.ofReal (ρ y ^ (3 / 4 : ℝ) * halfOp W g E q h y) ∂(circleMeasure x) ≤
      ENNReal.ofReal (1 - angularConst C / b) := by
  refine angPair_core hb hC hh hε hhε hL4 x hρm hρ0 hρ1 fun y hy => ?_
  obtain ⟨χ, Y, hf⟩ := hfield y
  exact quarter_le_measure_logAngRatio_of_zero hf hb hC hh hε hhε hy

end LSBA
