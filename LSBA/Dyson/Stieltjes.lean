import LSBA.Dyson.Scalar

/-!
# Stieltjes transforms and the measure ν_g

Stieltjes transforms of finite measures, inversion and injectivity, a representation theorem for
the transforms needed here, and the measure `ν_g` and distribution function `F_g` of (1.10)
[eq:distribution].
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- Stieltjes transform `∫ (t - z)⁻¹ dν(t)`. -/
def stieltjes (ν : Measure ℝ) (z : ℂ) : ℂ := ∫ t, ((t : ℂ) - z)⁻¹ ∂ν

/-- `ν_g`: a probability measure with Stieltjes transform `m_g` on `ℂ_+` (junk `dirac 0`). -/
def nuDyson (g : ℝ) : Measure ℝ :=
  if h : ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ z : ℂ, 0 < z.im → stieltjes ν z = mDyson g z
  then h.choose else Measure.dirac 0

/-- `F_g(x) = ν_g((-∞, x])`, (1.10) [eq:distribution]. -/
def Fdist (g x : ℝ) : ℝ := (nuDyson g (Set.Iic x)).toReal

/-! ### The kernel `(t - z)⁻¹` and the Poisson kernel -/

private lemma sub_ne_zero_of_im {z : ℂ} (hz : 0 < z.im) (t : ℝ) : (t : ℂ) - z ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

private lemma norm_inv_sub_le {z : ℂ} (hz : 0 < z.im) (t : ℝ) : ‖((t : ℂ) - z)⁻¹‖ ≤ z.im⁻¹ := by
  rw [norm_inv]
  apply inv_anti₀ hz
  have := Complex.abs_im_le_norm ((t : ℂ) - z)
  simp only [sub_im, ofReal_im, zero_sub, abs_neg, abs_of_pos hz] at this
  exact this

private lemma continuous_inv_sub {z : ℂ} (hz : 0 < z.im) :
    Continuous (fun t : ℝ => ((t : ℂ) - z)⁻¹) :=
  (continuous_ofReal.sub continuous_const).inv₀ (sub_ne_zero_of_im hz)

private lemma integrable_inv_sub (ν : Measure ℝ) [IsFiniteMeasure ν] {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹) ν :=
  Integrable.of_bound (continuous_inv_sub hz).aestronglyMeasurable z.im⁻¹
    (Eventually.of_forall (norm_inv_sub_le hz))

private lemma im_inv_sub (t E η : ℝ) :
    (((t : ℂ) - (E + η * I))⁻¹).im = η / ((t - E) ^ 2 + η ^ 2) := by
  simp [Complex.inv_im, Complex.normSq_apply]
  ring

/-- `Im S_ν(E + iη) = ∫ η / ((t - E)² + η²) dν(t)`. -/
private lemma im_stieltjes (ν : Measure ℝ) [IsFiniteMeasure ν] (E : ℝ) {η : ℝ} (hη : 0 < η) :
    (stieltjes ν (E + η * I)).im = ∫ t, η / ((t - E) ^ 2 + η ^ 2) ∂ν := by
  have hz : 0 < ((E : ℂ) + η * I).im := by simpa using hη
  unfold stieltjes
  have h := integral_im (integrable_inv_sub ν hz)
  simp only [RCLike.im_to_complex] at h
  rw [← h]
  simp_rw [im_inv_sub]

private lemma poisson_denom_pos (t E : ℝ) {η : ℝ} (hη : 0 < η) : 0 < (t - E) ^ 2 + η ^ 2 := by
  positivity

private lemma poisson_le (t E : ℝ) {η : ℝ} (hη : 0 < η) : η / ((t - E) ^ 2 + η ^ 2) ≤ η⁻¹ := by
  rw [div_le_iff₀ (poisson_denom_pos t E hη)]
  have : η⁻¹ * η ^ 2 = η := by field_simp
  nlinarith [sq_nonneg (t - E), inv_pos.mpr hη]

private lemma hasDerivAt_arctan_poisson (t E : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun E => Real.arctan ((E - t) / η)) (η / ((t - E) ^ 2 + η ^ 2)) E := by
  have h := (((hasDerivAt_id E).sub_const t).div_const η).arctan
  simp only [id_eq] at h
  convert h using 1
  have : (t - E) ^ 2 + η ^ 2 ≠ 0 := (poisson_denom_pos t E hη).ne'
  field_simp
  ring

/-- `∫_c^d η / ((t - E)² + η²) dE = arctan((d - t)/η) - arctan((c - t)/η)`. -/
private lemma integral_poisson (t c d : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫ E in c..d, η / ((t - E) ^ 2 + η ^ 2) =
      Real.arctan ((d - t) / η) - Real.arctan ((c - t) / η) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun E _ => hasDerivAt_arctan_poisson t E hη)]
  refine ContinuousOn.intervalIntegrable ?_
  refine Continuous.continuousOn ?_
  exact continuous_const.div (by fun_prop) (fun E => (poisson_denom_pos t E hη).ne')

/-! ### Limits of `arctan (a / η)` as `η ↓ 0` -/

/-- `lim_{η ↓ 0} arctan (a / η)`. -/
private def arctanLim (a : ℝ) : ℝ := if 0 < a then π / 2 else if a < 0 then -(π / 2) else 0

private lemma tendsto_arctan_div (a : ℝ) :
    Tendsto (fun η : ℝ => Real.arctan (a / η)) (𝓝[>] 0) (𝓝 (arctanLim a)) := by
  rcases lt_trichotomy 0 a with ha | rfl | ha
  · have h : Tendsto (fun η : ℝ => a / η) (𝓝[>] 0) atTop := by
      simp_rw [div_eq_mul_inv]
      exact tendsto_inv_nhdsGT_zero.const_mul_atTop ha
    simp only [arctanLim, ha, ↓reduceIte]
    exact (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h
  · simp [arctanLim]
  · have h : Tendsto (fun η : ℝ => a / η) (𝓝[>] 0) atBot := by
      simp_rw [div_eq_mul_inv]
      exact tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg ha
    simp only [arctanLim, not_lt.mpr ha.le, ha, ↓reduceIte]
    exact (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp h

private lemma abs_arctan_sub_le (a b : ℝ) : |Real.arctan a - Real.arctan b| ≤ π := by
  have h1 := neg_pi_div_two_lt_arctan a
  have h2 := arctan_lt_pi_div_two a
  have h3 := neg_pi_div_two_lt_arctan b
  have h4 := arctan_lt_pi_div_two b
  rw [abs_le]
  constructor <;> linarith

/-! ### Stieltjes inversion -/

/-- The inversion kernel `π⁻¹ (arctan((d - t)/η) - arctan((c - t)/η))`. -/
private def invKer (c d η t : ℝ) : ℝ :=
  π⁻¹ * (Real.arctan ((d - t) / η) - Real.arctan ((c - t) / η))

/-- Pointwise limit of `invKer c d η` as `η ↓ 0`. -/
private def invLim (c d t : ℝ) : ℝ := π⁻¹ * (arctanLim (d - t) - arctanLim (c - t))

private lemma abs_invKer_le (c d η t : ℝ) : |invKer c d η t| ≤ 1 := by
  unfold invKer
  rw [abs_mul, abs_inv, abs_of_pos pi_pos]
  calc π⁻¹ * |Real.arctan ((d - t) / η) - Real.arctan ((c - t) / η)| ≤ π⁻¹ * π := by
        gcongr; exact abs_arctan_sub_le _ _
    _ = 1 := inv_mul_cancel₀ pi_pos.ne'

private lemma tendsto_invKer (c d t : ℝ) :
    Tendsto (fun η => invKer c d η t) (𝓝[>] 0) (𝓝 (invLim c d t)) :=
  ((tendsto_arctan_div _).sub (tendsto_arctan_div _)).const_mul _

private lemma invLim_eq {c d : ℝ} (hcd : c < d) (t : ℝ) :
    invLim c d t = (Set.Ioo c d).indicator (fun _ => (1 : ℝ)) t +
      ({c} : Set ℝ).indicator (fun _ => (1 / 2 : ℝ)) t +
      ({d} : Set ℝ).indicator (fun _ => (1 / 2 : ℝ)) t := by
  have hπ := pi_pos.ne'
  unfold invLim arctanLim
  rcases lt_trichotomy t c with htc | rfl | htc
  · have h1 : 0 < d - t := by linarith
    have h2 : 0 < c - t := by linarith
    have h3 : t ∉ Set.Ioo c d := fun h => by linarith [h.1]
    have h4 : t ≠ d := by linarith
    simp [h1, h2, h3, htc.ne, h4]
  · have h1 : 0 < d - t := by linarith
    simp [h1, hcd.ne]
    field_simp
  · rcases lt_trichotomy t d with htd | rfl | htd
    · have h1 : 0 < d - t := by linarith
      have h2 : c - t < 0 := by linarith
      have h2' : ¬ 0 < c - t := by linarith
      simp [h1, h2, h2', htc, htd, htc.ne', htd.ne]
    · have h2 : c - t < 0 := by linarith
      have h2' : ¬ 0 < c - t := by linarith
      simp [h2, h2', htc.ne']
      field_simp
    · have h1 : d - t < 0 := by linarith
      have h1' : ¬ 0 < d - t := by linarith
      have h2 : c - t < 0 := by linarith
      have h2' : ¬ 0 < c - t := by linarith
      have h3 : t ∉ Set.Ioo c d := fun h => by linarith [h.2]
      simp [h1, h1', h2, h2', h3, htc.ne', htd.ne']

private lemma measurable_invLim {c d : ℝ} (hcd : c < d) : Measurable (invLim c d) := by
  rw [show invLim c d = fun t => _ from funext (invLim_eq hcd)]
  exact ((measurable_const.indicator measurableSet_Ioo).add
    (measurable_const.indicator (measurableSet_singleton c))).add
    (measurable_const.indicator (measurableSet_singleton d))

private lemma integral_invLim (ν : Measure ℝ) [IsFiniteMeasure ν] {c d : ℝ} (hcd : c < d) :
    ∫ t, invLim c d t ∂ν =
      (ν (Set.Ioo c d)).toReal + (ν {c}).toReal / 2 + (ν {d}).toReal / 2 := by
  simp_rw [invLim_eq hcd]
  have i1 : Integrable ((Set.Ioo c d).indicator (fun _ => (1 : ℝ))) ν :=
    (integrable_const _).indicator measurableSet_Ioo
  have i2 : Integrable (({c} : Set ℝ).indicator (fun _ => (1 / 2 : ℝ))) ν :=
    (integrable_const _).indicator (measurableSet_singleton c)
  have i3 : Integrable (({d} : Set ℝ).indicator (fun _ => (1 / 2 : ℝ))) ν :=
    (integrable_const _).indicator (measurableSet_singleton d)
  have i12 : Integrable (fun t => (Set.Ioo c d).indicator (fun _ => (1 : ℝ)) t +
      ({c} : Set ℝ).indicator (fun _ => (1 / 2 : ℝ)) t) ν := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2,
    integral_indicator_const _ measurableSet_Ioo, integral_indicator_const _
      (measurableSet_singleton c), integral_indicator_const _ (measurableSet_singleton d)]
  simp only [measureReal_def, smul_eq_mul]
  ring

/-- `π⁻¹ ∫_c^d Im S_ν(E + iη) dE = ∫ invKer c d η dν`, by Fubini. -/
private lemma integral_im_stieltjes (ν : Measure ℝ) [IsFiniteMeasure ν] {c d : ℝ} (hcd : c < d)
    {η : ℝ} (hη : 0 < η) :
    π⁻¹ * ∫ E in c..d, (stieltjes ν (E + η * I)).im = ∫ t, invKer c d η t ∂ν := by
  have hint : Integrable (Function.uncurry fun (E t : ℝ) => η / ((t - E) ^ 2 + η ^ 2))
      ((volume.restrict (Set.Ioc c d)).prod ν) := by
    refine Integrable.of_bound ?_ η⁻¹ (Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact continuous_const.div (by fun_prop)
        (fun p => (poisson_denom_pos p.2 p.1 hη).ne')
    · simp only [Function.uncurry, Real.norm_eq_abs]
      rw [abs_of_pos (div_pos hη (poisson_denom_pos _ _ hη))]
      exact poisson_le _ _ hη
  have e1 : ∫ E in c..d, (stieltjes ν (E + η * I)).im =
      ∫ t, (∫ E in c..d, η / ((t - E) ^ 2 + η ^ 2)) ∂ν := by
    simp_rw [im_stieltjes ν _ hη, intervalIntegral.integral_of_le hcd.le]
    rw [integral_integral_swap hint]
  rw [e1, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [integral_poisson t c d hη]
  rfl

/-- Stieltjes inversion for a finite measure on `ℝ`. -/
theorem stieltjes_inversion (ν : Measure ℝ) [IsFiniteMeasure ν] (c d : ℝ) (hcd : c < d) :
    Tendsto (fun η : ℝ => π⁻¹ * ∫ E in c..d, (stieltjes ν (E + η * I)).im) (𝓝[>] 0)
      (𝓝 ((ν (Set.Ioo c d)).toReal + (ν {c}).toReal / 2 + (ν {d}).toReal / 2)) := by
  rw [← integral_invLim ν hcd]
  have e : (fun η => ∫ t, invKer c d η t ∂ν) =ᶠ[𝓝[>] 0]
      (fun η : ℝ => π⁻¹ * ∫ E in c..d, (stieltjes ν (E + η * I)).im) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact (integral_im_stieltjes ν hcd hη).symm
  refine Tendsto.congr' e ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_
    (integrable_const _) (Eventually.of_forall fun t => tendsto_invKer c d t)
  · refine Eventually.of_forall fun η => Continuous.aestronglyMeasurable ?_
    unfold invKer
    fun_prop
  · exact Eventually.of_forall fun η => Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact abs_invKer_le c d η t

/-! ### Injectivity -/

private lemma abs_invLim_le (c d t : ℝ) : |invLim c d t| ≤ 1 :=
  le_of_tendsto' ((continuous_abs.tendsto _).comp (tendsto_invKer c d t))
    (fun η => abs_invKer_le c d η t)

private lemma integral_Iic_eq_of_invLim (ν₁ ν₂ : Measure ℝ) [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] (h : ∀ c d : ℝ, c < d → ∫ t, invLim c d t ∂ν₁ = ∫ t, invLim c d t ∂ν₂)
    (x : ℝ) : ν₁ (Set.Iic x) = ν₂ (Set.Iic x) := by
  set c : ℕ → ℝ := fun n => x - n - 1
  set d : ℕ → ℝ := fun n => x + 1 / ((n : ℝ) + 1)
  have hcd : ∀ n, c n < d n := fun n => by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    simp only [c, d]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hlim : ∀ t, Tendsto (fun n => invLim (c n) (d n) t) atTop
      (𝓝 ((Set.Iic x).indicator (fun _ => (1 : ℝ)) t)) := by
    intro t
    obtain ⟨N, hN⟩ := exists_nat_gt (x - t)
    by_cases htx : t ≤ x
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr htx)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      have h1 : 0 < d n - t := by
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        simp only [d]; linarith
      have h2 : c n - t < 0 := by simp only [c]; linarith
      have h2' : ¬ 0 < c n - t := by linarith
      simp only [invLim, arctanLim, h1, h2', h2, ↓reduceIte]
      field_simp
      ring
    · rw [Set.indicator_of_notMem (by simpa using htx)]
      obtain ⟨M, hM⟩ := exists_nat_one_div_lt (sub_pos.mpr (not_le.mp htx))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop M] with n hn
      have hn' : (M : ℝ) ≤ n := by exact_mod_cast hn
      have h1 : d n - t < 0 := by
        have : 1 / ((n : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
          gcongr
        simp only [d]; linarith
      have h1' : ¬ 0 < d n - t := by linarith
      have h2 : c n - t < 0 := by
        have := (n.cast_nonneg : (0 : ℝ) ≤ n)
        simp only [c]; linarith [not_le.mp htx]
      have h2' : ¬ 0 < c n - t := by linarith
      simp [invLim, arctanLim, h1', h1, h2', h2]
  have hT : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν], Tendsto (fun n => ∫ t, invLim (c n) (d n) t ∂ν)
      atTop (𝓝 (ν (Set.Iic x)).toReal) := by
    intro ν _
    have e : (ν (Set.Iic x)).toReal = ∫ t, (Set.Iic x).indicator (fun _ => (1 : ℝ)) t ∂ν := by
      rw [integral_indicator_const _ measurableSet_Iic, measureReal_def, smul_eq_mul, mul_one]
    rw [e]
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_)
      (integrable_const _) (fun n => Eventually.of_forall fun t => ?_)
      (Eventually.of_forall hlim)
    · exact (measurable_invLim (hcd n)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact abs_invLim_le _ _ t
  have h12 : (ν₁ (Set.Iic x)).toReal = (ν₂ (Set.Iic x)).toReal :=
    tendsto_nhds_unique ((hT ν₁).congr fun n => h (c n) (d n) (hcd n)) (hT ν₂)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h12

theorem stieltjes_injective (ν₁ ν₂ : Measure ℝ) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h : ∀ z : ℂ, 0 < z.im → stieltjes ν₁ z = stieltjes ν₂ z) : ν₁ = ν₂ := by
  refine Measure.ext_of_Iic ν₁ ν₂ (integral_Iic_eq_of_invLim ν₁ ν₂ (fun c d hcd => ?_))
  rw [integral_invLim ν₁ hcd, integral_invLim ν₂ hcd]
  refine tendsto_nhds_unique (stieltjes_inversion ν₁ c d hcd) ?_
  refine (stieltjes_inversion ν₂ c d hcd).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hz : ∀ E : ℝ, 0 < ((E : ℂ) + η * I).im := fun E => by simpa using hη
  simp_rw [h _ (hz _)]

/-! ### Line integrals of functions decaying in the closed upper half-plane -/

/-- A continuous function on `ℝ` with `‖f t‖ ≤ C / t²` for large `|t|` is integrable. -/
private lemma integrable_of_le_div_sq {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) {C T : ℝ} (h : ∀ t : ℝ, T ≤ |t| → ‖f t‖ ≤ C / t ^ 2) : Integrable f := by
  refine hf.locallyIntegrable.integrable_of_isBigO_cocompact
    (g := fun t : ℝ => (1 + t ^ 2)⁻¹) ?_ (integrable_inv_one_add_sq.integrableAtFilter _)
  refine Asymptotics.IsBigO.of_bound (2 * |C|) ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (max T 1)] with t ht
  rw [Real.norm_eq_abs] at ht
  have hT : T ≤ |t| := le_trans (le_max_left _ _) ht
  have h1 : 1 ≤ |t| := le_trans (le_max_right _ _) ht
  have ht2 : 1 ≤ t ^ 2 := by rw [← sq_abs]; nlinarith
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  have h3 : 0 < t ^ 2 := lt_of_lt_of_le one_pos ht2
  have key : 1 / t ^ 2 ≤ 2 / (1 + t ^ 2) := by
    rw [div_le_div_iff₀ h3 hpos]; nlinarith
  calc ‖f t‖ ≤ C / t ^ 2 := h t hT
    _ ≤ |C| / t ^ 2 := by gcongr; exact le_abs_self C
    _ = |C| * (1 / t ^ 2) := by ring
    _ ≤ |C| * (2 / (1 + t ^ 2)) := mul_le_mul_of_nonneg_left key (abs_nonneg C)
    _ = 2 * |C| * (1 + t ^ 2)⁻¹ := by ring

private lemma integrable_line {f : ℂ → ℂ} (hf : ContinuousOn f {ζ : ℂ | 0 ≤ ζ.im}) {K A₀ : ℝ}
    (hK : ∀ ζ : ℂ, 0 ≤ ζ.im → A₀ ≤ ‖ζ‖ → ‖f ζ‖ ≤ K / ‖ζ‖ ^ 2) :
    Integrable (fun t : ℝ => f t) := by
  refine integrable_of_le_div_sq (T := A₀) (C := K)
    (hf.comp_continuous continuous_ofReal (fun t => by simp)) (fun t ht => ?_)
  have h := hK t (by simp) (by rwa [Complex.norm_real, Real.norm_eq_abs])
  rwa [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h

/-- If `f` is holomorphic on the closed upper half-plane and `‖f ζ‖ ≤ K / ‖ζ‖²` there for large
`‖ζ‖`, then `∫_ℝ f = 0` (rectangle Cauchy theorem and `A → ∞`). -/
private lemma integral_line_eq_zero {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {ζ : ℂ | 0 ≤ ζ.im})
    {K A₀ : ℝ} (hK : ∀ ζ : ℂ, 0 ≤ ζ.im → A₀ ≤ ‖ζ‖ → ‖f ζ‖ ≤ K / ‖ζ‖ ^ 2) :
    ∫ t : ℝ, f t = 0 := by
  have hint := integrable_line hf.continuousOn hK
  have hlim := intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hedge : ∀ A : ℝ, 0 < A → A₀ ≤ A → ∀ ζ : ℂ, 0 ≤ ζ.im → A ≤ ‖ζ‖ →
      ‖f ζ‖ ≤ |K| / A ^ 2 := by
    intro A hA hAA ζ h1 h2
    calc ‖f ζ‖ ≤ K / ‖ζ‖ ^ 2 := hK ζ h1 (hAA.trans h2)
      _ ≤ |K| / ‖ζ‖ ^ 2 := by gcongr; exact le_abs_self K
      _ ≤ |K| / A ^ 2 := by gcongr
  have hbd : ∀ A : ℝ, max A₀ 1 ≤ A → ‖∫ t in -A..id A, f t‖ ≤ 4 * |K| / A := by
    intro A hA
    have hA0 : 0 < A := by linarith [le_max_right A₀ 1]
    have hAA : A₀ ≤ A := le_trans (le_max_left _ _) hA
    have hsub : Set.uIcc ((-A : ℝ) : ℂ).re (A + A * I).re ×ℂ
        Set.uIcc ((-A : ℝ) : ℂ).im (A + A * I).im ⊆ {ζ : ℂ | 0 ≤ ζ.im} := by
      intro ζ hζ
      rw [Complex.mem_reProdIm] at hζ
      have h2 := hζ.2
      simp only [ofReal_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero,
        mul_one, zero_add] at h2
      rw [Set.mem_uIcc] at h2
      simp only [Set.mem_ofPred_eq]
      rcases h2 with h2 | h2 <;> linarith [h2.1, h2.2]
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f _ _ (hf.mono hsub)
    simp only [ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re,
      mul_zero, mul_one, sub_zero, zero_add, add_zero, ofReal_zero, zero_mul] at hrect
    have htop : ‖∫ x in -A..A, f (x + A * I)‖ ≤ |K| / A ^ 2 * |A - -A| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => ?_)
      refine hedge A hA0 hAA _ (by simp [hA0.le]) ?_
      have := Complex.abs_im_le_norm ((x : ℂ) + A * I)
      simpa [abs_of_pos hA0] using this
    have hright : ‖∫ y in (0 : ℝ)..A, f (A + y * I)‖ ≤ |K| / A ^ 2 * |A - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => ?_)
      rw [Set.uIoc_of_le hA0.le] at hy
      refine hedge A hA0 hAA _ (by simp [hy.1.le]) ?_
      have := Complex.abs_re_le_norm ((A : ℂ) + y * I)
      simpa [abs_of_pos hA0] using this
    have hleft : ‖∫ y in (0 : ℝ)..A, f (-A + y * I)‖ ≤ |K| / A ^ 2 * |A - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => ?_)
      rw [Set.uIoc_of_le hA0.le] at hy
      refine hedge A hA0 hAA _ (by simp [hy.1.le]) ?_
      have := Complex.abs_re_le_norm (-(A : ℂ) + y * I)
      simpa [abs_of_pos hA0] using this
    have e : ∫ t in -A..id A, f t = (∫ x in -A..A, f (x + A * I)) -
        I • (∫ y in (0 : ℝ)..A, f (A + y * I)) + I • (∫ y in (0 : ℝ)..A, f (-A + y * I)) := by
      simp only [id]
      push_cast at hrect
      linear_combination hrect
    rw [e]
    have hI : ∀ v : ℂ, ‖I • v‖ = ‖v‖ := fun v => by rw [smul_eq_mul, norm_mul, norm_I, one_mul]
    calc _ ≤ ‖(∫ x in -A..A, f (x + A * I)) - I • (∫ y in (0 : ℝ)..A, f (A + y * I))‖ +
          ‖I • (∫ y in (0 : ℝ)..A, f (-A + y * I))‖ := norm_add_le _ _
      _ ≤ ‖∫ x in -A..A, f (x + A * I)‖ + ‖I • (∫ y in (0 : ℝ)..A, f (A + y * I))‖ +
          ‖I • (∫ y in (0 : ℝ)..A, f (-A + y * I))‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ |K| / A ^ 2 * |A - -A| + |K| / A ^ 2 * |A - 0| + |K| / A ^ 2 * |A - 0| := by
          rw [hI, hI]; gcongr
      _ = 4 * |K| / A := by
          rw [sub_neg_eq_add, sub_zero, abs_of_pos (by linarith : 0 < A + A), abs_of_pos hA0]
          field_simp
          ring
  have h0 : Tendsto (fun A : ℝ => ∫ t in -A..id A, f t) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun A : ℝ => 4 * |K| / A) ?_
      ((tendsto_const_nhds (x := 4 * |K|)).div_atTop tendsto_id)
    filter_upwards [eventually_ge_atTop (max A₀ 1)] with A hA
    exact hbd A hA
  exact tendsto_nhds_unique hlim h0

/-! ### Representation of `m(· + iη)` as a Stieltjes transform -/

section Representation

/-- The hypotheses of the representation theorem. -/
private structure ReprHyp (m : ℂ → ℂ) (R : ℝ) : Prop where
  hm : DifferentiableOn ℂ m {z : ℂ | 0 < z.im}
  him : ∀ z : ℂ, 0 < z.im → 0 ≤ (m z).im
  hR : 0 < R
  hdecay : ∀ z : ℂ, 0 < z.im → R < ‖z‖ → ‖z * m z + 1‖ ≤ R / (‖z‖ - R)

variable {m : ℂ → ℂ} {R : ℝ}

private lemma ReprHyp.norm_le (H : ReprHyp m R) {w : ℂ} (hw : 0 < w.im) (hwR : R < ‖w‖) :
    ‖m w‖ ≤ (‖w‖ - R)⁻¹ := by
  have hR := H.hR
  have hpos : 0 < ‖w‖ - R := by linarith
  have hw0 : 0 < ‖w‖ := by linarith
  have h1 : ‖w‖ * ‖m w‖ ≤ ‖w‖ * (‖w‖ - R)⁻¹ := by
    rw [← norm_mul]
    calc ‖w * m w‖ = ‖(w * m w + 1) - 1‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖w * m w + 1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ R / (‖w‖ - R) + 1 := by rw [norm_one]; linarith [H.hdecay w hw hwR]
      _ = ‖w‖ * (‖w‖ - R)⁻¹ := by field_simp; ring
  exact le_of_mul_le_mul_left h1 hw0

private lemma ReprHyp.norm_add_inv_le (H : ReprHyp m R) {w : ℂ} (hw : 0 < w.im)
    (hwR : R < ‖w‖) : ‖m w + w⁻¹‖ ≤ R / (‖w‖ - R) / ‖w‖ := by
  have hR := H.hR
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hwR; linarith
  have e : m w + w⁻¹ = (w * m w + 1) / w := by field_simp
  rw [e, norm_div]
  gcongr
  exact H.hdecay w hw hwR

private lemma norm_le_norm_add_I {ζ : ℂ} (hζ : 0 ≤ ζ.im) {η : ℝ} (hη : 0 < η) :
    ‖ζ‖ ≤ ‖ζ + η * I‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  nlinarith

private lemma ReprHyp.norm_shift_le (H : ReprHyp m R) {η : ℝ} (hη : 0 < η) {ζ : ℂ}
    (hζ : 0 ≤ ζ.im) (hζR : 2 * R ≤ ‖ζ‖) : ‖m (ζ + η * I)‖ ≤ 2 / ‖ζ‖ := by
  have hR := H.hR
  have h1 := norm_le_norm_add_I hζ hη
  have hw : 0 < (ζ + η * I).im := by simp; linarith
  have hpos : 0 < ‖ζ‖ - R := by linarith
  have hζ0 : 0 < ‖ζ‖ := by linarith
  calc ‖m (ζ + η * I)‖ ≤ (‖ζ + η * I‖ - R)⁻¹ := H.norm_le hw (by linarith)
    _ ≤ (‖ζ‖ - R)⁻¹ := by gcongr
    _ ≤ 2 / ‖ζ‖ := by
        rw [inv_le_comm₀ hpos (by positivity), inv_div]
        linarith

private lemma ReprHyp.diff_shift (H : ReprHyp m R) {η δ : ℝ} (hδ : δ ≤ η) :
    DifferentiableOn ℂ (fun ζ => m (ζ + η * I)) {ζ : ℂ | -δ < ζ.im} :=
  H.hm.comp (differentiableOn_id.add_const _) (fun ζ hζ => by
    simp at hζ ⊢
    linarith)

private lemma ReprHyp.continuous_shift (H : ReprHyp m R) {η : ℝ} (hη : 0 < η) :
    Continuous (fun t : ℝ => m (t + η * I)) :=
  (H.diff_shift (le_refl η)).continuousOn.comp_continuous continuous_ofReal
    (fun t => by simp [hη])

private lemma norm_inv_sub_le_two {ζ w : ℂ} (hw : 0 < ‖w‖) (h : 2 * ‖w‖ ≤ ‖ζ‖) :
    ‖(ζ - w)⁻¹‖ ≤ 2 / ‖ζ‖ := by
  have h1 : ‖ζ‖ - ‖w‖ ≤ ‖ζ - w‖ := norm_sub_norm_le ζ w
  have hζ : 0 < ‖ζ‖ := by linarith
  have hpos : 0 < ‖ζ - w‖ := by linarith
  rw [norm_inv, inv_le_comm₀ hpos (by positivity), inv_div]
  linarith

/-- `∫ ((t - x)² + y²)⁻¹ dt = π / y` for `y > 0`. -/
private lemma integral_inv_sq_add_sq (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ t : ℝ, ((t - x) ^ 2 + y ^ 2)⁻¹ = π / y := by
  have h1 := ProbabilityTheory.integral_cauchyPDFReal_eq_one x (γ := y.toNNReal)
    (Real.toNNReal_pos.mpr hy).ne'
  simp only [ProbabilityTheory.cauchyPDFReal, Real.coe_toNNReal _ hy.le] at h1
  rw [integral_const_mul] at h1
  rw [eq_div_iff hy.ne']
  have hπ := pi_pos.ne'
  calc (∫ t : ℝ, ((t - x) ^ 2 + y ^ 2)⁻¹) * y =
      π * (π⁻¹ * y * ∫ t : ℝ, ((t - x) ^ 2 + y ^ 2)⁻¹) := by field_simp
    _ = π := by rw [h1, mul_one]

private lemma integrable_inv_sq_add_sq (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (fun t : ℝ => ((t - x) ^ 2 + y ^ 2)⁻¹) := by
  have h := (ProbabilityTheory.integrable_cauchyPDFReal x (γ := y.toNNReal)).const_mul (π / y)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [ProbabilityTheory.cauchyPDFReal, Real.coe_toNNReal _ hy.le]
  have hπ := pi_pos
  field_simp

open ComplexConjugate in
/-- For `η > 0` and `z ∈ ℂ_+`: `m(z + iη) = ∫ (t - z)⁻¹ π⁻¹ Im m(t + iη) dt`. -/
private lemma ReprHyp.repr (H : ReprHyp m R) {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 < z.im) :
    m (z + η * I) = ∫ t : ℝ, ((π⁻¹ * (m (t + η * I)).im : ℝ) : ℂ) * ((t : ℂ) - z)⁻¹ := by
  have hR := H.hR
  set F : ℂ → ℂ := fun ζ => m (ζ + η * I) with hF
  set δ := min η z.im with hδdef
  have hδ : 0 < δ := lt_min hη hz
  have hδz : δ ≤ z.im := min_le_right _ _
  have hFd : DifferentiableOn ℂ F {ζ : ℂ | -δ < ζ.im} := H.diff_shift (min_le_left _ _)
  have hU : IsOpen {ζ : ℂ | -δ < ζ.im} := isOpen_lt continuous_const continuous_im
  have hzU : z ∈ {ζ : ℂ | -δ < ζ.im} := by simp only [Set.mem_ofPred_eq]; linarith
  have hHP : {ζ : ℂ | 0 ≤ ζ.im} ⊆ {ζ : ℂ | -δ < ζ.im} := fun ζ hζ => by
    simp only [Set.mem_ofPred_eq] at hζ ⊢; linarith
  have hne : ∀ ζ ∈ {ζ : ℂ | -δ < ζ.im}, ζ - conj z ≠ 0 := by
    intro ζ hζ h
    have := congrArg Complex.im h
    simp only [Set.mem_ofPred_eq] at hζ
    simp at this
    linarith
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr (fun h => by rw [h] at hz; simp at hz)
  have hFb : ∀ ζ : ℂ, 0 ≤ ζ.im → 2 * R ≤ ‖ζ‖ → ‖F ζ‖ ≤ 2 / ‖ζ‖ :=
    fun ζ h1 h2 => H.norm_shift_le hη h1 h2
  have hcz : ∀ ζ : ℂ, 2 * ‖z‖ ≤ ‖ζ‖ → ‖(ζ - conj z)⁻¹‖ ≤ 2 / ‖ζ‖ := fun ζ h =>
    norm_inv_sub_le_two (by rwa [RCLike.norm_conj]) (by rwa [RCLike.norm_conj])
  -- `f₁ ζ = F ζ (ζ - z̄)⁻¹`
  set f₁ : ℂ → ℂ := fun ζ => F ζ * (ζ - conj z)⁻¹ with hf₁
  have hf₁d : DifferentiableOn ℂ f₁ {ζ : ℂ | -δ < ζ.im} :=
    hFd.mul ((differentiableOn_id.sub_const _).inv hne)
  have hf₁b : ∀ ζ : ℂ, 0 ≤ ζ.im → max (2 * R) (2 * ‖z‖) ≤ ‖ζ‖ → ‖f₁ ζ‖ ≤ 4 / ‖ζ‖ ^ 2 := by
    intro ζ h1 h2
    have hζ0 : 0 < ‖ζ‖ := by linarith [le_max_right (2 * R) (2 * ‖z‖)]
    calc ‖f₁ ζ‖ = ‖F ζ‖ * ‖(ζ - conj z)⁻¹‖ := norm_mul _ _
      _ ≤ (2 / ‖ζ‖) * (2 / ‖ζ‖) := mul_le_mul (hFb ζ h1 (le_trans (le_max_left _ _) h2))
          (hcz ζ (le_trans (le_max_right _ _) h2)) (norm_nonneg _) (by positivity)
      _ = 4 / ‖ζ‖ ^ 2 := by ring
  -- `f₂ ζ = dslope F z ζ (ζ - z̄)⁻¹`
  set f₂ : ℂ → ℂ := fun ζ => dslope F z ζ * (ζ - conj z)⁻¹ with hf₂
  have hf₂d : DifferentiableOn ℂ f₂ {ζ : ℂ | -δ < ζ.im} :=
    ((differentiableOn_dslope (hU.mem_nhds hzU)).mpr hFd).mul
      ((differentiableOn_id.sub_const _).inv hne)
  have hf₂b : ∀ ζ : ℂ, 0 ≤ ζ.im → max (max (2 * R) (2 * ‖z‖)) 1 ≤ ‖ζ‖ →
      ‖f₂ ζ‖ ≤ 4 * (2 + ‖F z‖) / ‖ζ‖ ^ 2 := by
    intro ζ h1 h2
    have hR' : 2 * R ≤ ‖ζ‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h2
    have hz' : 2 * ‖z‖ ≤ ‖ζ‖ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
    have h1' : 1 ≤ ‖ζ‖ := le_trans (le_max_right _ _) h2
    have hζ0 : 0 < ‖ζ‖ := by linarith
    have hζz : ζ ≠ z := fun h => by rw [h] at hz'; linarith
    have hds : dslope F z ζ = (F ζ - F z) * (ζ - z)⁻¹ := by
      rw [dslope_of_ne _ hζz, slope_def_field, div_eq_mul_inv]
    have hFζ := hFb ζ h1 hR'
    have hFz : ‖F ζ - F z‖ ≤ 2 + ‖F z‖ := by
      have : 2 / ‖ζ‖ ≤ 2 := by rw [div_le_iff₀ hζ0]; linarith
      linarith [norm_sub_le (F ζ) (F z)]
    calc ‖f₂ ζ‖ = ‖F ζ - F z‖ * ‖(ζ - z)⁻¹‖ * ‖(ζ - conj z)⁻¹‖ := by
          simp only [f₂, hds, norm_mul]
      _ ≤ (2 + ‖F z‖) * (2 / ‖ζ‖) * (2 / ‖ζ‖) := by
          gcongr
          · exact norm_inv_sub_le_two hz0 hz'
          · exact hcz ζ hz'
      _ = 4 * (2 + ‖F z‖) / ‖ζ‖ ^ 2 := by ring
  have I₁ := integral_line_eq_zero (hf₁d.mono hHP) hf₁b
  have I₂ := integral_line_eq_zero (hf₂d.mono hHP) hf₂b
  have i₁ := integrable_line (hf₁d.mono hHP).continuousOn hf₁b
  have i₂ := integrable_line (hf₂d.mono hHP).continuousOn hf₂b
  -- `k t = ((t - x)² + y²)⁻¹`
  set k : ℝ → ℂ := fun t => ((((t - z.re) ^ 2 + z.im ^ 2)⁻¹ : ℝ) : ℂ) with hk
  have ik : Integrable k := (integrable_inv_sq_add_sq z.re hz).ofReal
  have Ik : ∫ t, k t = ((π / z.im : ℝ) : ℂ) := by
    simp only [k]
    rw [integral_complex_ofReal, integral_inv_sq_add_sq z.re hz]
  have hkt : ∀ t : ℝ, k t = ((t : ℂ) - z)⁻¹ * ((t : ℂ) - conj z)⁻¹ := by
    intro t
    rw [← mul_inv]
    simp only [k]
    push_cast
    congr 1
    apply Complex.ext <;> simp [pow_two]
    ring
  have hpt : ∀ t : ℝ, ((π⁻¹ * (F t).im : ℝ) : ℂ) * ((t : ℂ) - z)⁻¹ =
      (2 * π * I)⁻¹ * (f₁ t - conj (f₁ t) + (z - conj z) * f₂ t + (z - conj z) * F z * k t) := by
    intro t
    have hp : (t : ℂ) - z ≠ 0 := sub_ne_zero_of_im hz t
    have hq : (t : ℂ) - conj z ≠ 0 := hne t (by simp; linarith)
    have htz : (t : ℂ) ≠ z := sub_ne_zero.mp hp
    have hds : dslope F z t = (F t - F z) * ((t : ℂ) - z)⁻¹ := by
      rw [dslope_of_ne _ htz, slope_def_field, div_eq_mul_inv]
    have hcq : conj (((t : ℂ) - conj z)⁻¹) = ((t : ℂ) - z)⁻¹ := by
      rw [map_inv₀, map_sub, Complex.conj_ofReal, Complex.conj_conj]
    simp only [f₁, f₂, hds, hkt, map_mul, hcq]
    push_cast
    rw [Complex.im_eq_sub_conj]
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
    field_simp
    ring
  have hconj : Integrable (fun t : ℝ => conj (f₁ t)) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp i₁
  have j1 : Integrable (fun t : ℝ => f₁ t - conj (f₁ t)) := i₁.sub hconj
  have j2 : Integrable (fun t : ℝ => (z - conj z) * f₂ t) := i₂.const_mul _
  have j3 : Integrable (fun t : ℝ => (z - conj z) * F z * k t) := ik.const_mul _
  have j12 : Integrable (fun t : ℝ => f₁ t - conj (f₁ t) + (z - conj z) * f₂ t) := j1.add j2
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    integral_add j12 j3, integral_add j1 j2, integral_sub i₁ hconj, integral_conj,
    integral_const_mul, integral_const_mul, I₁, I₂, Ik, map_zero, sub_zero, mul_zero, zero_add,
    Complex.sub_conj, show F z = m (z + η * I) from rfl]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  have hy : (z.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
  push_cast
  field_simp
  ring

private lemma ReprHyp.integrable_im (H : ReprHyp m R) {η : ℝ} (hη : 0 < η) :
    Integrable (fun t : ℝ => (m (t + η * I)).im) := by
  have hR := H.hR
  refine integrable_of_le_div_sq (T := 2 * R) (C := 2 * R + η)
    (continuous_im.comp (H.continuous_shift hη)) (fun t ht => ?_)
  set w : ℂ := t + η * I with hw
  have hwim : 0 < w.im := by simp [w, hη]
  have hwt : |t| ≤ ‖w‖ := by
    have := Complex.abs_re_le_norm w
    simpa [w] using this
  have hwR : R < ‖w‖ := by linarith
  have hw0 : 0 < ‖w‖ := by linarith
  have ht0 : 0 < t ^ 2 := by rw [← sq_abs]; nlinarith
  have hsq : t ^ 2 ≤ ‖w‖ ^ 2 := by rw [← sq_abs]; gcongr
  have h1 : ‖m w + w⁻¹‖ ≤ 2 * R / t ^ 2 := by
    calc ‖m w + w⁻¹‖ ≤ R / (‖w‖ - R) / ‖w‖ := H.norm_add_inv_le hwim hwR
      _ ≤ 2 * R / ‖w‖ ^ 2 := by
          have h2R : 2 * R ≤ ‖w‖ := by linarith
          rw [div_div, div_le_div_iff₀ (by nlinarith) (by positivity)]
          nlinarith [mul_nonneg (mul_nonneg hR.le hw0.le) (sub_nonneg.mpr h2R)]
      _ ≤ 2 * R / t ^ 2 := by gcongr
  have h2 : |(w⁻¹).im| ≤ η / t ^ 2 := by
    rw [Complex.inv_im, Complex.normSq_eq_norm_sq, abs_div, abs_neg, abs_of_pos hwim,
      abs_of_pos (by positivity)]
    have : w.im = η := by simp [w]
    rw [this]
    gcongr
  rw [Real.norm_eq_abs]
  have e : (m w).im = (m w + w⁻¹).im - (w⁻¹).im := by simp
  rw [e]
  calc |(m w + w⁻¹).im - (w⁻¹).im| ≤ |(m w + w⁻¹).im| + |(w⁻¹).im| := abs_sub _ _
    _ ≤ ‖m w + w⁻¹‖ + η / t ^ 2 := by gcongr; exact Complex.abs_im_le_norm _
    _ ≤ 2 * R / t ^ 2 + η / t ^ 2 := by gcongr
    _ = (2 * R + η) / t ^ 2 := by ring

/-- Density `π⁻¹ Im m(t + iη)` of the approximating measures. -/
private def shiftDensity (m : ℂ → ℂ) (η t : ℝ) : ℝ := π⁻¹ * (m (t + η * I)).im

/-- The measure `π⁻¹ Im m(t + iη) dt`. -/
private def shiftMeasure (m : ℂ → ℂ) (η : ℝ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (shiftDensity m η t))

private lemma ReprHyp.shiftDensity_nonneg (H : ReprHyp m R) {η : ℝ} (hη : 0 < η) (t : ℝ) :
    0 ≤ shiftDensity m η t :=
  mul_nonneg (inv_nonneg.mpr pi_pos.le) (H.him _ (by simp [hη]))

private lemma ReprHyp.integrable_shiftDensity (H : ReprHyp m R) {η : ℝ} (hη : 0 < η) :
    Integrable (shiftDensity m η) :=
  (H.integrable_im hη).const_mul π⁻¹

private lemma ReprHyp.measurable_shiftDensity (H : ReprHyp m R) {η : ℝ} (hη : 0 < η) :
    Measurable (shiftDensity m η) :=
  (continuous_const.mul (continuous_im.comp (H.continuous_shift hη))).measurable

private lemma ReprHyp.stieltjes_shiftMeasure (H : ReprHyp m R) {η : ℝ} (hη : 0 < η) {z : ℂ}
    (hz : 0 < z.im) : stieltjes (shiftMeasure m η) z = m (z + η * I) := by
  unfold stieltjes shiftMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun t => ENNReal.ofReal (shiftDensity m η t))
    (ENNReal.measurable_ofReal.comp (H.measurable_shiftDensity hη))
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), H.repr hη hz]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [ENNReal.toReal_ofReal (H.shiftDensity_nonneg hη t), Complex.real_smul]
  rfl

private lemma ReprHyp.integral_shiftDensity (H : ReprHyp m R) {η : ℝ} (hη : 0 < η) :
    ∫ t, shiftDensity m η t = 1 := by
  have hR := H.hR
  set ρ := shiftDensity m η
  have hρ := H.integrable_shiftDensity hη
  -- `-(iy) m(iy + iη) = ∫ ρ(t) (-(iy)) (t - iy)⁻¹ dt`
  have hrep : ∀ y : ℝ, 0 < y → -((y : ℂ) * I) * m (y * I + η * I) =
      ∫ t, (ρ t : ℂ) * (-((y : ℂ) * I) * ((t : ℂ) - y * I)⁻¹) := by
    intro y hy
    rw [H.repr hη (z := y * I) (by simpa using hy), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [ρ, shiftDensity]
    ring
  -- the right side tends to `∫ ρ`
  have hR1 : Tendsto (fun y : ℝ => ∫ t, (ρ t : ℂ) * (-((y : ℂ) * I) * ((t : ℂ) - y * I)⁻¹))
      atTop (𝓝 (∫ t, (ρ t : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖ρ t‖) ?_ ?_
      hρ.norm ?_
    · filter_upwards [eventually_gt_atTop 0] with y hy
      exact hρ.ofReal.aestronglyMeasurable.mul (continuous_const.mul
        (continuous_inv_sub (z := (y : ℂ) * I) (by simpa using hy))).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with y hy
      refine Eventually.of_forall fun t => ?_
      rw [norm_mul, Complex.norm_real]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, norm_I, mul_one,
        Real.norm_of_nonneg hy.le]
      have := norm_inv_sub_le (z := (y : ℂ) * I) (by simpa using hy) t
      simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one, mul_zero, add_zero] at this
      calc y * ‖((t : ℂ) - y * I)⁻¹‖ ≤ y * y⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hy.ne'
    · refine Eventually.of_forall fun t => ?_
      have hlim : Tendsto (fun y : ℝ => -((y : ℂ) * I) * ((t : ℂ) - y * I)⁻¹) atTop (𝓝 1) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
          ((tendsto_const_nhds (x := |t|)).div_atTop tendsto_id)
        filter_upwards [eventually_gt_atTop 0] with y hy
        have hne := sub_ne_zero_of_im (z := (y : ℂ) * I) (by simpa using hy) t
        have e : -((y : ℂ) * I) * ((t : ℂ) - y * I)⁻¹ - 1 = -(t : ℂ) * ((t : ℂ) - y * I)⁻¹ := by
          field_simp
          ring
        rw [e, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
        have := norm_inv_sub_le (z := (y : ℂ) * I) (by simpa using hy) t
        simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one, mul_zero, add_zero] at this
        calc |t| * ‖((t : ℂ) - y * I)⁻¹‖ ≤ |t| * y⁻¹ := by gcongr
          _ = |t| / id y := by simp [div_eq_mul_inv]
      simpa using (tendsto_const_nhds (x := (ρ t : ℂ))).mul hlim
  -- the left side tends to `1`
  have hL : Tendsto (fun y : ℝ => -((y : ℂ) * I) * m (y * I + η * I)) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      ((tendsto_const_nhds (x := R + η)).div_atTop
        (tendsto_atTop_add_const_right atTop (-R) tendsto_id))
    filter_upwards [eventually_gt_atTop R] with y hy
    have hy0 : 0 < y := by linarith
    set w : ℂ := ((y + η : ℝ) : ℂ) * I with hw
    have hwe : (y : ℂ) * I + η * I = w := by simp only [w]; push_cast; ring
    have hwim : 0 < w.im := by simp [w]; linarith
    have hwn : ‖w‖ = y + η := by
      simp only [w, norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs]
      exact abs_of_pos (by linarith)
    have hwR : R < ‖w‖ := by rw [hwn]; linarith
    have hd := H.hdecay w hwim hwR
    rw [hwn] at hd
    have hyη : (0 : ℝ) < y + η := by linarith
    have e : -((y : ℂ) * I) * m w - 1 =
        -(((y / (y + η) : ℝ) : ℂ)) * (w * m w + 1) - ((η / (y + η) : ℝ) : ℂ) := by
      simp only [w]
      have : ((y + η : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hyη.ne'
      push_cast at this ⊢
      field_simp
      ring
    rw [hwe, e]
    calc ‖-(((y / (y + η) : ℝ) : ℂ)) * (w * m w + 1) - ((η / (y + η) : ℝ) : ℂ)‖
        ≤ ‖-(((y / (y + η) : ℝ) : ℂ)) * (w * m w + 1)‖ + ‖((η / (y + η) : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
      _ = (y / (y + η)) * ‖w * m w + 1‖ + η / (y + η) := by
          rw [norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg
            (by positivity), Real.norm_of_nonneg (by positivity)]
      _ ≤ 1 * (R / (y + η - R)) + η / (y - R) := by
          have h1 : y / (y + η) ≤ 1 := by rw [div_le_one hyη]; linarith
          have h2 : η / (y + η) ≤ η / (y - R) :=
            div_le_div_of_nonneg_left hη.le (by linarith) (by linarith)
          have h3 := mul_le_mul h1 hd (norm_nonneg _) zero_le_one
          linarith
      _ ≤ R / (y - R) + η / (y - R) := by
          have h4 : R / (y + η - R) ≤ R / (y - R) :=
            div_le_div_of_nonneg_left hR.le (by linarith) (by linarith)
          linarith
      _ = (R + η) / (id y + -R) := by rw [id, ← sub_eq_add_neg, add_div]
  have hR2 : Tendsto (fun y : ℝ => ∫ t, (ρ t : ℂ) * (-((y : ℂ) * I) * ((t : ℂ) - y * I)⁻¹))
      atTop (𝓝 1) := by
    refine hL.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    exact hrep y hy
  have hmass := tendsto_nhds_unique hR1 hR2
  rw [integral_complex_ofReal] at hmass
  exact_mod_cast hmass

private lemma ReprHyp.isProbabilityMeasure_shiftMeasure (H : ReprHyp m R) {η : ℝ} (hη : 0 < η) :
    IsProbabilityMeasure (shiftMeasure m η) := by
  constructor
  unfold shiftMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (H.integrable_shiftDensity hη)
      (Eventually.of_forall (H.shiftDensity_nonneg hη)), H.integral_shiftDensity hη,
    ENNReal.ofReal_one]

/-- `shiftMeasure m η` as a probability measure (junk `dirac 0` if it is not one). -/
private def shiftProb (m : ℂ → ℂ) (η : ℝ) : ProbabilityMeasure ℝ :=
  if h : IsProbabilityMeasure (shiftMeasure m η) then ⟨shiftMeasure m η, h⟩
  else ⟨Measure.dirac 0, inferInstance⟩

private lemma ReprHyp.shiftProb_eq (H : ReprHyp m R) {η : ℝ} (hη : 0 < η) :
    (shiftProb m η : Measure ℝ) = shiftMeasure m η := by
  have hp := H.isProbabilityMeasure_shiftMeasure hη
  simp [shiftProb, hp]

/-- Tail bound `P(|t| > y) ≤ 2 ‖1 + iy S_P(iy)‖` for a probability measure `P` on `ℝ`. -/
private lemma measureReal_abs_gt_le (P : Measure ℝ) [IsProbabilityMeasure P] {y : ℝ}
    (hy : 0 < y) : P.real {t | y < |t|} ≤ 2 * ‖1 + (y * I) * stieltjes P (y * I)‖ := by
  have hz : 0 < ((y : ℂ) * I).im := by simpa using hy
  set u : ℝ → ℂ := fun t => 1 + (y * I) * ((t : ℂ) - y * I)⁻¹ with hu
  have hint : Integrable u P :=
    (integrable_const _).add ((integrable_inv_sub P hz).const_mul _)
  have hIu : ∫ t, u t ∂P = 1 + (y * I) * stieltjes P (y * I) := by
    simp only [u]
    rw [integral_add (integrable_const _) ((integrable_inv_sub P hz).const_mul _),
      integral_const, integral_const_mul]
    simp [stieltjes]
  have hre : ∀ t : ℝ, (u t).re = t ^ 2 / (t ^ 2 + y ^ 2) := by
    intro t
    have hd : t ^ 2 + y ^ 2 ≠ 0 := by positivity
    simp [u, Complex.inv_im, Complex.normSq_apply]
    field_simp
    ring
  have hS : MeasurableSet {t : ℝ | y < |t|} :=
    measurableSet_lt measurable_const measurable_abs
  have h1 : P.real {t | y < |t|} / 2 =
      ∫ t, {t : ℝ | y < |t|}.indicator (fun _ => (1 / 2 : ℝ)) t ∂P := by
    rw [integral_indicator_const _ hS, smul_eq_mul]
    ring
  have h2 : ∫ t, {t : ℝ | y < |t|}.indicator (fun _ => (1 / 2 : ℝ)) t ∂P ≤ ∫ t, (u t).re ∂P := by
    refine integral_mono ((integrable_const _).indicator hS) hint.re (fun t => ?_)
    rw [hre t]
    by_cases ht : y < |t|
    · rw [Set.indicator_of_mem (by exact ht)]
      have : y ^ 2 < t ^ 2 := by rw [← sq_abs t]; gcongr
      rw [le_div_iff₀ (by positivity)]
      linarith
    · rw [Set.indicator_of_notMem (by exact ht)]
      positivity
  have h3 : ∫ t, (u t).re ∂P ≤ ‖1 + (y * I) * stieltjes P (y * I)‖ := by
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [this, hIu]
    exact Complex.re_le_norm _
  linarith

private lemma ReprHyp.measure_shift_abs_gt_le (H : ReprHyp m R) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) {y : ℝ} (hy : R < y) :
    (shiftMeasure m η) {t | y < ‖t‖} ≤ ENNReal.ofReal (2 * (R + 1) / (y - R)) := by
  have hR := H.hR
  have hy0 : 0 < y := by linarith
  have := H.isProbabilityMeasure_shiftMeasure hη
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [Real.norm_eq_abs]
  refine (measureReal_abs_gt_le _ hy0).trans ?_
  rw [H.stieltjes_shiftMeasure hη (by simpa using hy0)]
  set w : ℂ := ((y + η : ℝ) : ℂ) * I with hw
  have hwe : (y : ℂ) * I + η * I = w := by simp only [w]; push_cast; ring
  have hwim : 0 < w.im := by simp [w]; linarith
  have hwn : ‖w‖ = y + η := by
    simp only [w, norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs]
    exact abs_of_pos (by linarith)
  have hwR : R < ‖w‖ := by rw [hwn]; linarith
  have hd := H.hdecay w hwim hwR
  have hm := H.norm_le hwim hwR
  rw [hwn] at hd hm
  rw [hwe]
  have e : 1 + (y : ℂ) * I * m w = (w * m w + 1) - (η : ℂ) * I * m w := by
    simp only [w]; push_cast; ring
  rw [e]
  have h1 : ‖(η : ℂ) * I * m w‖ ≤ 1 / (y - R) := by
    rw [norm_mul, norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_of_nonneg hη.le]
    calc η * ‖m w‖ ≤ 1 * (y + η - R)⁻¹ := mul_le_mul hη1 hm (norm_nonneg _) zero_le_one
      _ ≤ 1 / (y - R) := by
          rw [one_mul, one_div]
          exact inv_anti₀ (by linarith) (by linarith)
  have h2 : R / (y + η - R) ≤ R / (y - R) :=
    div_le_div_of_nonneg_left hR.le (by linarith) (by linarith)
  calc 2 * ‖w * m w + 1 - (η : ℂ) * I * m w‖ ≤ 2 * (‖w * m w + 1‖ + ‖(η : ℂ) * I * m w‖) := by
        gcongr; exact norm_sub_le _ _
    _ ≤ 2 * (R / (y - R) + 1 / (y - R)) := by gcongr; linarith
    _ = 2 * (R + 1) / (y - R) := by ring

end Representation

/-- A holomorphic map `ℂ_+ → closure ℂ_+` with `z m(z) + 1 → 0` at the
stated rate is the Stieltjes transform of a probability measure. -/
theorem exists_stieltjes_eq (m : ℂ → ℂ) (hm : DifferentiableOn ℂ m {z : ℂ | 0 < z.im})
    (him : ∀ z : ℂ, 0 < z.im → 0 ≤ (m z).im) (R : ℝ) (hR : 0 < R)
    (hdecay : ∀ z : ℂ, 0 < z.im → R < ‖z‖ → ‖z * m z + 1‖ ≤ R / (‖z‖ - R)) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ z : ℂ, 0 < z.im → stieltjes ν z = m z := by
  have H : ReprHyp m R := ⟨hm, him, hR, hdecay⟩
  set S : Set (ProbabilityMeasure ℝ) := shiftProb m '' Set.Ioo 0 1 with hS
  have htight : IsTightMeasureSet {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ S} := by
    refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
    have hg : Tendsto (fun r : ℝ => ENNReal.ofReal (2 * (R + 1) / (r - R))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      have := (tendsto_const_nhds (x := 2 * (R + 1))).div_atTop
        (tendsto_atTop_add_const_right atTop (-R) tendsto_id)
      simpa [sub_eq_add_neg] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_gt_atTop R] with r hr
    refine iSup₂_le fun μ hμ => ?_
    obtain ⟨P, ⟨η, hη, rfl⟩, rfl⟩ := hμ
    rw [H.shiftProb_eq hη.1]
    exact H.measure_shift_abs_gt_le hη.1 hη.2.le hr
  have hcomp := isCompact_closure_of_isTightMeasureSet htight
  have hle : map (shiftProb m) (𝓝[>] 0) ≤ 𝓟 (closure S) := by
    rw [le_principal_iff, mem_map]
    exact mem_of_superset (Ioo_mem_nhdsGT one_pos)
      (fun η hη => subset_closure (Set.mem_image_of_mem _ hη))
  obtain ⟨ν, -, hν⟩ := hcomp.exists_clusterPt hle
  refine ⟨ν, inferInstance, fun z hz => ?_⟩
  set kz : BoundedContinuousFunction ℝ ℂ := BoundedContinuousFunction.mkOfBound
    (⟨fun t : ℝ => ((t : ℂ) - z)⁻¹, continuous_inv_sub hz⟩ : C(ℝ, ℂ)) (2 * z.im⁻¹) (fun s t => by
      simp only [ContinuousMap.coe_mk]
      refine (dist_le_norm_add_norm _ _).trans ?_
      have h1 := norm_inv_sub_le hz s
      have h2 := norm_inv_sub_le hz t
      linarith) with hkz
  set Φ : ProbabilityMeasure ℝ → ℂ := fun μ => ∫ t, kz t ∂(μ : Measure ℝ) with hΦ
  have hcont : ContinuousAt Φ ν :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp tendsto_id kz
  have hz' : Tendsto (fun η : ℝ => z + η * I) (𝓝[>] 0) (𝓝 z) := by
    have : Continuous (fun η : ℝ => z + η * I) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hmz : ContinuousAt m z :=
    hm.continuousOn.continuousAt ((isOpen_lt continuous_const continuous_im).mem_nhds hz)
  have hT : Tendsto Φ (map (shiftProb m) (𝓝[>] 0)) (𝓝 (m z)) := by
    rw [tendsto_map'_iff]
    refine (hmz.tendsto.comp hz').congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    simp only [Function.comp, Φ, kz, BoundedContinuousFunction.mkOfBound_coe,
      ContinuousMap.coe_mk]
    rw [H.shiftProb_eq hη, ← H.stieltjes_shiftMeasure hη hz]
    rfl
  have hcl := hν.map hcont hT
  have he : Φ ν = m z := eq_of_nhds_neBot hcl
  rw [← he]
  rfl

/-! ### The measure `ν_g` and the distribution function `F_g` -/

/-- `ν_g` is a probability measure whose Stieltjes transform is `m_g` on `ℂ_+`, as required by
(1.10) [eq:distribution]. -/
theorem nuDyson_spec (g : ℝ) (hg : 0 ≤ g) :
    IsProbabilityMeasure (nuDyson g) ∧
      ∀ z : ℂ, 0 < z.im → stieltjes (nuDyson g) z = mDyson g z := by
  have hex : ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ∀ z : ℂ, 0 < z.im → stieltjes ν z = mDyson g z :=
    exists_stieltjes_eq (mDyson g) (mDyson_differentiableOn g hg)
      (fun z hz => (mDyson_spec g hg z hz).1.le) 3 (by norm_num)
      (fun z hz hz3 => mDyson_asymp g hg z hz hz3)
  have e : nuDyson g = hex.choose := by
    unfold nuDyson
    split_ifs
    rfl
  rw [e]
  exact hex.choose_spec

private lemma integrable_poisson (t : ℝ) {η : ℝ} (hη : 0 < η) :
    Integrable (fun E : ℝ => η / ((t - E) ^ 2 + η ^ 2)) := by
  refine ((integrable_inv_sq_add_sq t hη).const_mul η).congr (Eventually.of_forall fun E => ?_)
  simp only
  rw [div_eq_mul_inv, show (E - t) ^ 2 = (t - E) ^ 2 by ring]

/-- `∫_{-∞}^x η / ((t - E)² + η²) dE = arctan((x - t)/η) + π/2`. -/
private lemma integral_Iic_poisson (t x : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫ E in Set.Iic x, η / ((t - E) ^ 2 + η ^ 2) = Real.arctan ((x - t) / η) + π / 2 := by
  have hlim : Tendsto (fun E : ℝ => Real.arctan ((E - t) / η)) atBot (𝓝 (-(π / 2))) := by
    have h : Tendsto (fun E : ℝ => (E - t) / η) atBot atBot := by
      refine Tendsto.atBot_div_const hη ?_
      simpa [sub_eq_add_neg] using tendsto_atBot_add_const_right atBot (-t) tendsto_id
    exact (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp h
  rw [integral_Iic_of_hasDerivAt_of_tendsto (f := fun E => Real.arctan ((E - t) / η))
    ((hasDerivAt_arctan_poisson t x hη).continuousAt.continuousWithinAt)
    (fun E _ => hasDerivAt_arctan_poisson t E hη) (integrable_poisson t hη).integrableOn hlim]
  ring

/-- The kernel `π⁻¹ (arctan((x - t)/η) + π/2)`. -/
private def cdfKer (x η t : ℝ) : ℝ := π⁻¹ * (Real.arctan ((x - t) / η) + π / 2)

/-- Pointwise limit of `cdfKer x η` as `η ↓ 0`. -/
private def cdfLim (x t : ℝ) : ℝ := π⁻¹ * (arctanLim (x - t) + π / 2)

private lemma abs_cdfKer_le (x η t : ℝ) : |cdfKer x η t| ≤ 1 := by
  unfold cdfKer
  have h1 := neg_pi_div_two_lt_arctan ((x - t) / η)
  have h2 := arctan_lt_pi_div_two ((x - t) / η)
  rw [abs_mul, abs_inv, abs_of_pos pi_pos, abs_of_pos (by linarith), inv_mul_le_iff₀ pi_pos]
  linarith

private lemma tendsto_cdfKer (x t : ℝ) :
    Tendsto (fun η => cdfKer x η t) (𝓝[>] 0) (𝓝 (cdfLim x t)) :=
  ((tendsto_arctan_div _).add_const _).const_mul _

/-- `π⁻¹ ∫_{-∞}^x Im S_ν(E + iη) dE = ∫ cdfKer x η dν`, by Fubini. -/
private lemma integral_im_stieltjes_Iic (ν : Measure ℝ) [IsFiniteMeasure ν] (x : ℝ) {η : ℝ}
    (hη : 0 < η) :
    π⁻¹ * ∫ E in Set.Iic x, (stieltjes ν (E + η * I)).im = ∫ t, cdfKer x η t ∂ν := by
  have hcont : Continuous (Function.uncurry fun (E t : ℝ) => η / ((t - E) ^ 2 + η ^ 2)) :=
    continuous_const.div (by fun_prop) (fun p => (poisson_denom_pos p.2 p.1 hη).ne')
  have hint : Integrable (Function.uncurry fun (E t : ℝ) => η / ((t - E) ^ 2 + η ^ 2))
      ((volume.restrict (Set.Iic x)).prod ν) := by
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun t => (integrable_poisson t hη).integrableOn, ?_⟩
    have hb : Integrable (fun t : ℝ => Real.arctan ((x - t) / η) + π / 2) ν := by
      refine Integrable.of_bound (by fun_prop : Continuous _).aestronglyMeasurable π
        (Eventually.of_forall fun t => ?_)
      have h1 := neg_pi_div_two_lt_arctan ((x - t) / η)
      have h2 := arctan_lt_pi_div_two ((x - t) / η)
      rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    refine hb.congr (Eventually.of_forall fun t => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [← integral_Iic_poisson t x hη]
    refine integral_congr_ae (Eventually.of_forall fun E => ?_)
    simp only
    rw [Real.norm_of_nonneg (div_pos hη (poisson_denom_pos t E hη)).le]
  have e1 : ∫ E in Set.Iic x, (stieltjes ν (E + η * I)).im =
      ∫ t, (∫ E in Set.Iic x, η / ((t - E) ^ 2 + η ^ 2)) ∂ν := by
    simp_rw [im_stieltjes ν _ hη]
    rw [integral_integral_swap hint]
  rw [e1, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [integral_Iic_poisson t x hη]
  rfl

/-- (1.10) [eq:distribution] in limit form. -/
theorem Fdist_eq_limit (g : ℝ) (hg : 0 ≤ g) (x : ℝ) :
    Tendsto (fun η : ℝ => π⁻¹ * ∫ E in Set.Iic x, (mDyson g (E + η * I)).im) (𝓝[>] 0)
      (𝓝 (Fdist g x)) := by
  obtain ⟨hP, hS⟩ := nuDyson_spec g hg
  set ν := nuDyson g with hν
  have hz : ∀ E η : ℝ, 0 < η → 0 < ((E : ℂ) + η * I).im := fun E η hη => by simpa using hη
  -- `ν_g` has no atom at `x`: `ν{x} ≤ η Im m_g(x + iη) ≤ η max{1, g}`
  have hat : ∀ η : ℝ, 0 < η → ν.real {x} ≤ η * max 1 g := by
    intro η hη
    have h1 : ν.real {x} * η⁻¹ ≤ (mDyson g (x + η * I)).im := by
      rw [← hS _ (hz x η hη), im_stieltjes ν x hη]
      have hi : ∫ t, ({x} : Set ℝ).indicator (fun _ => η⁻¹) t ∂ν = ν.real {x} * η⁻¹ := by
        rw [integral_indicator_const _ (measurableSet_singleton x), smul_eq_mul]
      rw [← hi]
      refine integral_mono ((integrable_const _).indicator (measurableSet_singleton x))
        (Integrable.of_bound (Continuous.aestronglyMeasurable (continuous_const.div
          (by fun_prop) (fun t => (poisson_denom_pos t x hη).ne'))) η⁻¹
          (Eventually.of_forall fun t => ?_)) (fun t => ?_)
      · rw [Real.norm_of_nonneg (div_pos hη (poisson_denom_pos t x hη)).le]
        exact poisson_le t x hη
      · by_cases ht : t = x
        · rw [Set.indicator_of_mem (by simp [ht]), ht]
          apply le_of_eq
          simp only [sub_self]
          field_simp
          ring
        · rw [Set.indicator_of_notMem (by simpa using ht)]
          exact (div_pos hη (poisson_denom_pos t x hη)).le
    have h2 : (mDyson g (x + η * I)).im ≤ max 1 g :=
      (Complex.im_le_norm _).trans (mDyson_norm_le_max g hg _ (hz x η hη))
    have h3 := h1.trans h2
    rwa [mul_inv_le_iff₀ hη, mul_comm] at h3
  have hatom : ν {x} = 0 := by
    have h0 : ν.real {x} = 0 := by
      by_contra hne
      have hpos : 0 < ν.real {x} := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
      have hM : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
      have := hat (ν.real {x} / (2 * max 1 g)) (by positivity)
      rw [div_mul_eq_mul_div, mul_comm 2, ← div_div, mul_div_cancel_right₀ _ hM.ne'] at this
      linarith
    exact (measureReal_eq_zero_iff).mp h0
  -- the limit kernel agrees `ν`-a.e. with the indicator of `(-∞, x]`
  have hlimeq : ∫ t, cdfLim x t ∂ν = Fdist g x := by
    have hae : (fun t => cdfLim x t) =ᵐ[ν] (Set.Iic x).indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [compl_mem_ae_iff.mpr hatom] with t ht
      have htx : t ≠ x := by simpa using ht
      rcases lt_or_gt_of_ne htx with h | h
      · have h1 : 0 < x - t := by linarith
        rw [Set.indicator_of_mem (Set.mem_Iic.mpr h.le)]
        simp only [cdfLim, arctanLim, h1, ↓reduceIte]
        field_simp
        ring
      · have h1 : x - t < 0 := by linarith
        have h1' : ¬ 0 < x - t := by linarith
        rw [Set.indicator_of_notMem (by simpa using h)]
        simp [cdfLim, arctanLim, h1, h1']
    rw [integral_congr_ae hae, integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one,
      measureReal_def]
    rfl
  rw [← hlimeq]
  have e : (fun η => ∫ t, cdfKer x η t ∂ν) =ᶠ[𝓝[>] 0]
      (fun η : ℝ => π⁻¹ * ∫ E in Set.Iic x, (mDyson g (E + η * I)).im) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    rw [← integral_im_stieltjes_Iic ν x hη]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun E => ?_)
    simp only
    rw [hS _ (hz E η hη)]
  refine Tendsto.congr' e ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_
    (integrable_const _) (Eventually.of_forall fun t => tendsto_cdfKer x t)
  · refine Eventually.of_forall fun η => Continuous.aestronglyMeasurable ?_
    unfold cdfKer
    fun_prop
  · exact Eventually.of_forall fun η => Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact abs_cdfKer_le x η t

end LSBA
