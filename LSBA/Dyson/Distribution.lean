import LSBA.Dyson.FreeGreen
import LSBA.Dyson.Stieltjes

/-!
# Properties of the deterministic distribution

Continuity and monotonicity of `F_g`, the support bound (1.12) [eq:bounded-physical-bulk], the
uniform atom bound (1.13) [rd:eq:noatoms], evenness of `ν_g`, and Lemma 1.2(iii)
[da:lem:distribution].
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Elementary facts on `ν_g` -/

/-- `ν_g` is a probability measure for every `g` (the junk value `dirac 0` included). -/
private lemma isProbabilityMeasure_nuDyson (g : ℝ) : IsProbabilityMeasure (nuDyson g) := by
  unfold nuDyson
  split_ifs with h
  · exact h.choose_spec.1
  · infer_instance

/-- `0 < max 1 g`. -/
private lemma max_one_pos' (g : ℝ) : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)

/-- `0 < γ_g`. -/
private lemma gammaG_pos' (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have := max_one_pos' g
  positivity

/-- `F_g` is nondecreasing, (1.10) [eq:distribution]. -/
theorem Fdist_monotone (g : ℝ) : Monotone (Fdist g) := by
  have := isProbabilityMeasure_nuDyson g
  intro x y hxy
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr hxy))

/-! ### The Poisson bound -/

/-- The denominator of the Poisson kernel is positive. -/
private lemma poisson_pos' (t E : ℝ) {η : ℝ} (hη : 0 < η) : 0 < (t - E) ^ 2 + η ^ 2 := by
  positivity

/-- `t ↦ (t - z)⁻¹` is integrable for a finite measure when `Im z > 0`. -/
private lemma integrable_inv_sub' (ν : Measure ℝ) [IsFiniteMeasure ν] {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹) ν := by
  have hne : ∀ t : ℝ, (t : ℂ) - z ≠ 0 := fun t h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  refine Integrable.of_bound
    ((continuous_ofReal.sub continuous_const).inv₀ hne).aestronglyMeasurable z.im⁻¹
    (Eventually.of_forall fun t => ?_)
  rw [norm_inv]
  apply inv_anti₀ hz
  have := Complex.abs_im_le_norm ((t : ℂ) - z)
  simp only [sub_im, ofReal_im, zero_sub, abs_neg, abs_of_pos hz] at this
  exact this

/-- `Im S_ν(E + iη) = ∫ η / ((t - E)² + η²) dν(t)`. -/
private lemma im_stieltjes' (ν : Measure ℝ) [IsFiniteMeasure ν] (E : ℝ) {η : ℝ} (hη : 0 < η) :
    (stieltjes ν (E + η * I)).im = ∫ t, η / ((t - E) ^ 2 + η ^ 2) ∂ν := by
  have hz : 0 < ((E : ℂ) + η * I).im := by simpa using hη
  unfold stieltjes
  have h := integral_im (integrable_inv_sub' ν hz)
  simp only [RCLike.im_to_complex] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp [Complex.inv_im, Complex.normSq_apply]
  ring

/-- `ν([x - h, x + h]) ≤ 2h · Im S_ν(x + ih)`. -/
private lemma measureReal_Icc_le (ν : Measure ℝ) [IsFiniteMeasure ν] (x : ℝ) {h : ℝ} (hh : 0 < h) :
    ν.real (Set.Icc (x - h) (x + h)) ≤ 2 * h * (stieltjes ν (x + h * I)).im := by
  rw [im_stieltjes' ν x hh]
  have hi : ∫ t, (Set.Icc (x - h) (x + h)).indicator (fun _ => (2 * h)⁻¹) t ∂ν =
      ν.real (Set.Icc (x - h) (x + h)) * (2 * h)⁻¹ := by
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul]
  have hle : ν.real (Set.Icc (x - h) (x + h)) * (2 * h)⁻¹ ≤
      ∫ t, h / ((t - x) ^ 2 + h ^ 2) ∂ν := by
    rw [← hi]
    refine integral_mono ((integrable_const _).indicator measurableSet_Icc)
      (Integrable.of_bound (Continuous.aestronglyMeasurable (continuous_const.div
        (by fun_prop) (fun t => (poisson_pos' t x hh).ne'))) h⁻¹
        (Eventually.of_forall fun t => ?_)) (fun t => ?_)
    · rw [Real.norm_of_nonneg (div_pos hh (poisson_pos' t x hh)).le]
      rw [div_le_iff₀ (poisson_pos' t x hh)]
      have : 0 ≤ (t - x) ^ 2 := sq_nonneg _
      field_simp
      nlinarith
    · by_cases ht : t ∈ Set.Icc (x - h) (x + h)
      · rw [Set.indicator_of_mem ht]
        obtain ⟨h1, h2⟩ := ht
        have hsq : (t - x) ^ 2 ≤ h ^ 2 := by nlinarith
        rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (poisson_pos' t x hh)]
        nlinarith
      · rw [Set.indicator_of_notMem ht]
        exact (div_pos hh (poisson_pos' t x hh)).le
  have h2h : 0 < 2 * h := by positivity
  rw [← div_eq_mul_inv, div_le_iff₀ h2h] at hle
  linarith


/-- For `g ≥ 1` and `z ∈ ℂ_+`, `|m_g(z)|² · 2 Im z ≤ 1`, from the quartic form of (1.9)
[eq:dyson] with `b = 1`. -/
private lemma norm_sq_mDyson_le (g : ℝ) (hg : 1 ≤ g) {z : ℂ} (hz : 0 < z.im) :
    ‖mDyson g z‖ ^ 2 * (2 * z.im) ≤ 1 := by
  have hg0 : 0 ≤ g := le_trans zero_le_one hg
  obtain ⟨hm, hfix⟩ := mDyson_spec g hg0 z hz
  have hq := (dyson_iff_quartic g hg0 z hz _ hm).mp hfix
  have hb : hopB g = 1 := by
    unfold hopB
    rw [max_eq_right hg]
    exact div_self (by positivity)
  rw [hb] at hq
  set m := mDyson g z with hmdef
  set w : ℂ := z + (gammaG g : ℂ) * m with hw
  have hwim : z.im ≤ w.im := by
    rw [hw, Complex.add_im, Complex.im_ofReal_mul]
    have := gammaG_pos' g
    nlinarith
  have hfac : m ^ 2 * ((w - 2) * (w + 2)) = 1 := by
    rw [← hq]; push_cast; ring
  have hn : ‖m‖ ^ 2 * (‖w - 2‖ * ‖w + 2‖) = 1 := by
    have := congrArg norm hfac
    rw [norm_mul, norm_pow, norm_mul, norm_one] at this
    exact this
  have hA : z.im ≤ ‖w - 2‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp only [sub_im]
    norm_num
    exact hwim.trans (le_abs_self _)
  have hB : z.im ≤ ‖w + 2‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp only [add_im]
    norm_num
    exact hwim.trans (le_abs_self _)
  have hAB : 4 ≤ ‖w - 2‖ + ‖w + 2‖ := by
    have := norm_sub_le (w + 2) (w - 2)
    have e : w + 2 - (w - 2) = 4 := by ring
    rw [e] at this
    have h4 : ‖(4 : ℂ)‖ = 4 := by simp
    linarith
  have hprod : 2 * z.im ≤ ‖w - 2‖ * ‖w + 2‖ := by
    by_cases h : 2 ≤ ‖w - 2‖
    · nlinarith
    · have : 2 ≤ ‖w + 2‖ := by linarith
      nlinarith
  have hsq : 0 ≤ ‖m‖ ^ 2 := sq_nonneg _
  nlinarith


/-- A quantitative form of (1.13) [rd:eq:noatoms]. -/
theorem nuDyson_Icc_le (g : ℝ) (hg : 0 ≤ g) (x h : ℝ) (hh : 0 < h) (hh2 : h ≤ 1 / 2) :
    (nuDyson g (Set.Icc (x - h) (x + h))).toReal ≤ Real.sqrt (2 * h) := by
  obtain ⟨hP, hS⟩ := nuDyson_spec g hg
  have hz : 0 < ((x : ℂ) + h * I).im := by simpa using hh
  have h1 := measureReal_Icc_le (nuDyson g) x hh
  rw [hS _ hz] at h1
  change (nuDyson g).real (Set.Icc (x - h) (x + h)) ≤ _
  refine h1.trans ?_
  have hIm : (mDyson g (x + h * I)).im ≤ ‖mDyson g (x + h * I)‖ := Complex.im_le_norm _
  have h2h : 0 < 2 * h := by positivity
  rcases le_total g 1 with hg1 | hg1
  · have hM : max 1 g = 1 := max_eq_left hg1
    have hn := mDyson_norm_le_max g hg _ hz
    rw [hM] at hn
    refine le_trans (mul_le_mul_of_nonneg_left (hIm.trans hn) h2h.le) ?_
    rw [mul_one]
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith
  · have hn := norm_sq_mDyson_le g hg1 hz
    simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_zero, mul_one, zero_add]
      at hn
    refine Real.le_sqrt_of_sq_le ?_
    have hb : (2 * h * (mDyson g (x + h * I)).im) ^ 2 ≤
        (2 * h) ^ 2 * ‖mDyson g (x + h * I)‖ ^ 2 := by
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      exact pow_le_pow_left₀ (mDyson_spec g hg _ hz).1.le hIm 2
    nlinarith


/-- (1.13) [rd:eq:noatoms]: no atoms, uniformly in `g ≥ 0`. -/
theorem nuDyson_noatoms_uniform :
    ∀ ε > 0, ∃ h₀ > 0, ∀ h ∈ Set.Ioc 0 h₀, ∀ g : ℝ, 0 ≤ g → ∀ x : ℝ,
      (nuDyson g (Set.Icc (x - h) (x + h))).toReal ≤ ε := by
  intro ε hε
  refine ⟨min (1 / 2) (ε ^ 2 / 2), lt_min (by norm_num) (by positivity), ?_⟩
  intro h hh g hg x
  obtain ⟨hh0, hh1⟩ := hh
  refine (nuDyson_Icc_le g hg x h hh0 (hh1.trans (min_le_left _ _))).trans ?_
  refine Real.sqrt_le_iff.mpr ⟨hε.le, ?_⟩
  have := hh1.trans (min_le_right (1 / 2) (ε ^ 2 / 2))
  linarith

/-- `F_g` is continuous, (1.10) [eq:distribution]. -/
theorem Fdist_continuous (g : ℝ) (hg : 0 ≤ g) : Continuous (Fdist g) := by
  have hP := isProbabilityMeasure_nuDyson g
  have key : ∀ x y : ℝ, x ≤ y → y - x ≤ 1 → Fdist g y - Fdist g x ≤ Real.sqrt (y - x) := by
    intro x y hxy hy1
    rcases hxy.eq_or_lt with rfl | hlt
    · simp
    · have hd : Fdist g y - Fdist g x = (nuDyson g (Set.Ioc x y)).toReal := by
        unfold Fdist
        rw [← Set.Iic_union_Ioc_eq_Iic hxy, measure_union (Set.Iic_disjoint_Ioc le_rfl)
          measurableSet_Ioc, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        ring
      rw [hd]
      have hh : 0 < (y - x) / 2 := by linarith
      have hsub : Set.Ioc x y ⊆
          Set.Icc ((x + y) / 2 - (y - x) / 2) ((x + y) / 2 + (y - x) / 2) := by
        intro t ht
        constructor <;> linarith [ht.1, ht.2]
      refine (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans ?_
      have := nuDyson_Icc_le g hg ((x + y) / 2) ((y - x) / 2) hh (by linarith)
      convert this using 3
      ring
  rw [Metric.continuous_iff]
  intro b ε hε
  have step : ∀ x y : ℝ, x ≤ y → |y - x| < min 1 (ε ^ 2) → |Fdist g y - Fdist g x| < ε := by
    intro x y hxy hd
    have hd' : y - x < min 1 (ε ^ 2) := by rwa [abs_of_nonneg (sub_nonneg.mpr hxy)] at hd
    have h1 := key x y hxy (hd'.le.trans (min_le_left _ _))
    have h2 : Real.sqrt (y - x) < ε := by
      rw [Real.sqrt_lt' hε]
      exact lt_of_lt_of_le hd' (min_le_right _ _)
    have hm := Fdist_monotone g hxy
    rw [abs_of_nonneg (sub_nonneg.mpr hm)]
    linarith
  refine ⟨min 1 (ε ^ 2), lt_min one_pos (by positivity), fun a ha => ?_⟩
  rw [Real.dist_eq] at ha ⊢
  rcases le_total b a with hba | hab
  · exact step b a hba ha
  · rw [abs_sub_comm]
    exact step a b hab (by rwa [abs_sub_comm] at ha)


set_option linter.unusedVariables false in
/-- (1.12) [eq:bounded-physical-bulk]: the support bound is at most `4`. -/
theorem support_bound_le_four (g : ℝ) (hg : 0 ≤ g) : (2 * g + 2) / max 1 g ≤ 4 := by
  rcases le_total g 1 with h | h
  · rw [max_eq_left h, div_one]
    linarith
  · rw [max_eq_right h, div_le_iff₀ (by linarith)]
    linarith

/-- `ν_g` is even (Section 1.1 [sec:model], after (1.10) [eq:distribution]). -/
theorem nuDyson_map_neg (g : ℝ) (hg : 0 ≤ g) :
    (nuDyson g).map (fun t : ℝ => -t) = nuDyson g := by
  obtain ⟨hP, hS⟩ := nuDyson_spec g hg
  have hmeas : Measurable (fun t : ℝ => -t) := measurable_neg
  have hP' : IsProbabilityMeasure ((nuDyson g).map (fun t : ℝ => -t)) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).mpr hP
  refine stieltjes_injective _ _ (fun z hz => ?_)
  rw [hS z hz]
  have hw : 0 < (-(starRingEnd ℂ z)).im := by simpa using hz
  have hne : ∀ t : ℝ, (t : ℂ) - z ≠ 0 := fun t h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  unfold stieltjes
  rw [integral_map (f := fun t : ℝ => ((t : ℂ) - z)⁻¹) hmeas.aemeasurable
    ((continuous_ofReal.sub continuous_const).inv₀ hne).aestronglyMeasurable]
  have e : ∀ t : ℝ, (((-t : ℝ) : ℂ) - z)⁻¹ =
      -(starRingEnd ℂ (((t : ℂ) - (-(starRingEnd ℂ z)))⁻¹)) := by
    intro t
    have h1 : starRingEnd ℂ ((t : ℂ) - (-(starRingEnd ℂ z))) = (t : ℂ) + z := by
      simp [Complex.conj_ofReal]
    rw [map_inv₀, h1, ← inv_neg]
    congr 1
    push_cast
    ring
  simp_rw [e]
  rw [integral_neg, integral_conj]
  have := hS _ hw
  unfold stieltjes at this
  rw [this, mDyson_neg_conj g hg z hz]
  simp

/-! ### The support bound (1.12) [eq:bounded-physical-bulk] -/

/-- Away from the band, `Im m_g(E + iη) ≤ η / ε²`, where `|E| ≥ (2g+2)/max{1,g} + ε`. -/
private lemma im_mDyson_le_far (g : ℝ) (hg : 0 ≤ g) {E η ε : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (hE : (2 * g + 2) / max 1 g + ε ≤ |E|) : (mDyson g (E + η * I)).im ≤ η / ε ^ 2 := by
  have hz : 0 < ((E : ℂ) + η * I).im := by simpa using hη
  set z : ℂ := (E : ℂ) + η * I with hzdef
  obtain ⟨hm, hfix⟩ := mDyson_spec g hg z hz
  have hMpos := max_one_pos' g
  set M := max 1 g with hMdef
  set s := M⁻¹ with hs
  have hspos : 0 < s := inv_pos.mpr hMpos
  have hγ : gammaG g = s ^ 2 := by
    unfold gammaG
    rw [← hMdef, hs, inv_pow]
  have hγM : gammaG g * M = s := by
    rw [hγ, hs]
    field_simp
  set b := hopB g with hbdef
  have hb0 : 0 ≤ b := div_nonneg hg hMpos.le
  have hE0 : (2 * g + 2) / M = 2 * b + 2 * s := by
    rw [hbdef, hs]
    unfold hopB
    rw [← hMdef]
    field_simp
  rw [hE0] at hE
  set m := mDyson g z with hmdef
  have hmn : ‖m‖ ≤ M := mDyson_norm_le_max g hg z hz
  have hre : |gammaG g * m.re| ≤ s := by
    rw [abs_mul, abs_of_pos (gammaG_pos' g), ← hγM]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm m).trans hmn) (gammaG_pos' g).le
  -- the lower bound on the denominators
  set D := s + ε with hD
  have hDpos : 0 < D := by positivity
  have hden : ∀ p : ℝ, D ≤ ‖((2 * b * Real.cos p : ℝ) : ℂ) - z - (gammaG g : ℂ) * m‖ := by
    intro p
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    have hz1 : z.re = E := by simp [hzdef]
    have hre' : (((2 * b * Real.cos p : ℝ) : ℂ) - z - (gammaG g : ℂ) * m).re =
        2 * b * Real.cos p - E - gammaG g * m.re := by
      rw [Complex.sub_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul, hz1]
    rw [hre']
    have hcos : |2 * b * Real.cos p| ≤ 2 * b := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * b)]
      calc 2 * b * |Real.cos p| ≤ 2 * b * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one p) (by positivity)
        _ = 2 * b := mul_one _
    have h1 : |E| ≤ |2 * b * Real.cos p - E - gammaG g * m.re| + |2 * b * Real.cos p| +
        |gammaG g * m.re| := by
      have a1 := neg_abs_le (2 * b * Real.cos p - E - gammaG g * m.re)
      have a2 := le_abs_self (2 * b * Real.cos p - E - gammaG g * m.re)
      have a3 := neg_abs_le (2 * b * Real.cos p)
      have a4 := le_abs_self (2 * b * Real.cos p)
      have a5 := neg_abs_le (gammaG g * m.re)
      have a6 := le_abs_self (gammaG g * m.re)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    rw [hD]
    linarith
  -- Ward identity (A.6) [da:eq:ward] and the pointwise bound `|R_w| ≤ D⁻¹`
  have hward := mDyson_ward g hg z hz
  rw [← hmdef, ← hbdef] at hward
  have hcont : Continuous fun p : ℝ =>
      ‖(((2 * b * Real.cos p : ℝ) : ℂ) - z - (gammaG g : ℂ) * m)⁻¹‖ ^ 2 := by
    refine (Continuous.norm (Continuous.inv₀ (by fun_prop) (fun p => ?_))).pow 2
    intro h0
    have := hden p
    rw [h0, norm_zero] at this
    linarith
  have hint : ∫ p in (-π)..π, ‖(((2 * b * Real.cos p : ℝ) : ℂ) - z - (gammaG g : ℂ) * m)⁻¹‖ ^ 2
      ≤ ∫ p in (-π)..π, (D ^ 2)⁻¹ := by
    refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      (hcont.intervalIntegrable _ _) intervalIntegrable_const (fun p _ => ?_)
    rw [norm_inv, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hDpos.le (hden p) 2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hpi := Real.pi_pos
  have hwd : m.im / (z.im + gammaG g * m.im) ≤ (D ^ 2)⁻¹ := by
    rw [← hward]
    calc (2 * π)⁻¹ * ∫ p in (-π)..π,
          ‖(((2 * b * Real.cos p : ℝ) : ℂ) - z - (gammaG g : ℂ) * m)⁻¹‖ ^ 2
        ≤ (2 * π)⁻¹ * ((π - -π) * (D ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ = (D ^ 2)⁻¹ := by field_simp; ring
  have hzim : z.im = η := by simp [hzdef]
  rw [hzim] at hwd
  have hdenpos : 0 < η + gammaG g * m.im := by
    have := gammaG_pos' g
    positivity
  rw [div_le_iff₀ hdenpos, inv_mul_eq_div, le_div_iff₀ (by positivity)] at hwd
  rw [le_div_iff₀ (by positivity)]
  have hγε : gammaG g = s ^ 2 := hγ
  have : m.im * ε ^ 2 ≤ m.im * (D ^ 2 - gammaG g) := by
    refine mul_le_mul_of_nonneg_left ?_ hm.le
    rw [hD, hγε]
    nlinarith
  nlinarith


/-- `ν_g` puts no mass on an open interval whose closure stays at distance `ε` from the band. -/
private lemma nuDyson_Ioo_null (g : ℝ) (hg : 0 ≤ g) {c d ε : ℝ} (hcd : c < d) (hε : 0 < ε)
    (hfar : ∀ t ∈ Set.Icc c d, (2 * g + 2) / max 1 g + ε ≤ |t|) :
    nuDyson g (Set.Ioo c d) = 0 := by
  obtain ⟨hP, hS⟩ := nuDyson_spec g hg
  have hT := stieltjes_inversion (nuDyson g) c d hcd
  have hz : ∀ E η : ℝ, 0 < η → 0 < ((E : ℂ) + η * I).im := fun E η hη => by simpa using hη
  have hle : ∀ η : ℝ, 0 < η →
      π⁻¹ * ∫ E in c..d, (stieltjes (nuDyson g) (E + η * I)).im ≤
        π⁻¹ * ((d - c) * (η / ε ^ 2)) := by
    intro η hη
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e : ∫ E in c..d, (stieltjes (nuDyson g) (E + η * I)).im =
        ∫ E in c..d, (mDyson g (E + η * I)).im :=
      intervalIntegral.integral_congr (fun E _ => by rw [hS _ (hz E η hη)])
    rw [e]
    have hcont : Continuous fun E : ℝ => (mDyson g (E + η * I)).im := by
      refine Complex.continuous_im.comp ?_
      refine (mDyson_differentiableOn g hg).continuousOn.comp_continuous
        (by fun_prop) (fun E => hz E η hη)
    have := intervalIntegral.integral_mono_on (μ := volume) (g := fun _ => η / ε ^ 2) hcd.le
      (hcont.intervalIntegrable _ _)
      intervalIntegrable_const (fun E hE => im_mDyson_le_far g hg hη hε (hfar E hE))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    exact this
  have hlim : Tendsto (fun η : ℝ => π⁻¹ * ((d - c) * (η / ε ^ 2))) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun η : ℝ => π⁻¹ * ((d - c) * (η / ε ^ 2))) (𝓝 0)
        (𝓝 (π⁻¹ * ((d - c) * (0 / ε ^ 2)))) := by
      refine Continuous.tendsto (by fun_prop) 0
    rw [zero_div, mul_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hmain := le_of_tendsto_of_tendsto hT hlim
    (by filter_upwards [self_mem_nhdsWithin] with η hη using hle η hη)
  have h1 : 0 ≤ (nuDyson g {c}).toReal := ENNReal.toReal_nonneg
  have h2 : 0 ≤ (nuDyson g {d}).toReal := ENNReal.toReal_nonneg
  have h3 : (nuDyson g (Set.Ioo c d)).toReal ≤ 0 := by linarith
  have h4 := ENNReal.toReal_eq_zero_iff _ |>.mp (le_antisymm h3 ENNReal.toReal_nonneg)
  exact h4.resolve_right (measure_ne_top _ _)

/-- (1.12) [eq:bounded-physical-bulk]: `ν_g` lives on `[-(2g+2)/max{1,g}, (2g+2)/max{1,g}]`. -/
theorem nuDyson_compl_support (g : ℝ) (hg : 0 ≤ g) :
    nuDyson g (Set.Icc (-((2 * g + 2) / max 1 g)) ((2 * g + 2) / max 1 g))ᶜ = 0 := by
  set E₀ := (2 * g + 2) / max 1 g with hE₀
  have hpos : ∀ n : ℕ, nuDyson g (Set.Ioo (E₀ + 1 / ((n : ℝ) + 1)) (E₀ + n + 2)) = 0 := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    refine nuDyson_Ioo_null g hg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) (fun t ht => ?_)
    exact (by linarith [ht.1] : E₀ + 1 / ((n : ℝ) + 1) ≤ t).trans (le_abs_self t)
  have hneg : ∀ n : ℕ, nuDyson g (Set.Ioo (-E₀ - n - 2) (-E₀ - 1 / ((n : ℝ) + 1))) = 0 := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    refine nuDyson_Ioo_null g hg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) (fun t ht => ?_)
    exact (by linarith [ht.2] : E₀ + 1 / ((n : ℝ) + 1) ≤ -t).trans (neg_le_abs t)
  have hcompl : (Set.Icc (-E₀) E₀)ᶜ = Set.Iio (-E₀) ∪ Set.Ioi E₀ := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, Set.mem_union, Set.mem_Iio,
      Set.mem_Ioi]
  rw [hcompl]
  refine measure_union_null ?_ ?_
  · refine measure_mono_null (fun t ht => ?_)
      (measure_iUnion_null (fun n : ℕ => hneg n))
    rw [Set.mem_Iio] at ht
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by linarith : 0 < -E₀ - t)
    obtain ⟨k, hk⟩ := exists_nat_gt (-E₀ - t)
    have hN1 : (n : ℝ) ≤ ((max n k : ℕ) : ℝ) := Nat.cast_le.mpr (le_max_left _ _)
    have hN2 : (k : ℝ) ≤ ((max n k : ℕ) : ℝ) := Nat.cast_le.mpr (le_max_right _ _)
    have h1 : 1 / (((max n k : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    exact Set.mem_iUnion.mpr ⟨max n k, by linarith, by linarith⟩
  · refine measure_mono_null (fun t ht => ?_)
      (measure_iUnion_null (fun n : ℕ => hpos n))
    rw [Set.mem_Ioi] at ht
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by linarith : 0 < t - E₀)
    obtain ⟨k, hk⟩ := exists_nat_gt (t - E₀)
    have hN1 : (n : ℝ) ≤ ((max n k : ℕ) : ℝ) := Nat.cast_le.mpr (le_max_left _ _)
    have hN2 : (k : ℝ) ≤ ((max n k : ℕ) : ℝ) := Nat.cast_le.mpr (le_max_right _ _)
    have h1 : 1 / (((max n k : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    exact Set.mem_iUnion.mpr ⟨max n k, by linarith, by linarith⟩

/-! ### Lemma 1.2(iii) [da:lem:distribution] -/

/-- If `[x - h, x + h]` reaches below the band, the mass of `(-∞, x + h]` is at most `√(2h)`. -/
private lemma Fdist_le_sqrt (g : ℝ) (hg : 0 ≤ g) {x h : ℝ} (hh : 0 < h) (hh2 : h ≤ 1 / 2)
    (hlow : x - h ≤ -((2 * g + 2) / max 1 g)) : Fdist g (x + h) ≤ Real.sqrt (2 * h) := by
  have hP := isProbabilityMeasure_nuDyson g
  unfold Fdist
  have hsub : Set.Iic (x + h) ⊆
      (Set.Icc (-((2 * g + 2) / max 1 g)) ((2 * g + 2) / max 1 g))ᶜ ∪ Set.Icc (x - h) (x + h) := by
    intro t ht
    by_cases hc : t ∈ Set.Icc (-((2 * g + 2) / max 1 g)) ((2 * g + 2) / max 1 g)
    · exact Or.inr ⟨by linarith [hc.1], ht⟩
    · exact Or.inl hc
  calc (nuDyson g (Set.Iic (x + h))).toReal
      ≤ (nuDyson g ((Set.Icc (-((2 * g + 2) / max 1 g)) ((2 * g + 2) / max 1 g))ᶜ ∪
          Set.Icc (x - h) (x + h))).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    _ ≤ (nuDyson g (Set.Icc (x - h) (x + h))).toReal := by
        refine (ENNReal.toReal_mono (by
          exact ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
          (measure_union_le _ _)).trans ?_
        rw [nuDyson_compl_support g hg, zero_add]
    _ ≤ Real.sqrt (2 * h) := nuDyson_Icc_le g hg x h hh hh2

/-- Lemma 1.2(iii) [da:lem:distribution] with the explicit constants `κ₀ = c = κ²/4`, `C = 8/κ²`. -/
theorem bulk_window_explicit (κ : ℝ) (hκ : 0 < κ ∧ κ < 1 / 2) (g : ℝ) (hg : 0 ≤ g)
    (hgc : g ≤ κ ^ 2 / 4 ∨ 8 / κ ^ 2 ≤ g) (E : ℝ) (hE : κ ≤ Fdist g (-|E|)) :
    |E| ≤ 2 - κ ^ 2 / 4 := by
  obtain ⟨hκ0, hκ1⟩ := hκ
  by_contra hcon
  replace hcon := not_le.mp hcon
  have hκ2 : κ ^ 2 < 1 / 4 := by nlinarith
  have hκ2' : 0 < κ ^ 2 := by positivity
  have ha : -|E| < -2 + κ ^ 2 / 4 := by linarith
  have hF : Fdist g (-|E|) ≤ Fdist g (-2 + κ ^ 2 / 4) := Fdist_monotone g ha.le
  have hlt : Fdist g (-2 + κ ^ 2 / 4) < κ := by
    rcases hgc with hs | hl
    · have hg1 : g ≤ 1 := by linarith
      have hM : max 1 g = 1 := max_eq_left hg1
      have := Fdist_le_sqrt g hg (x := -2 - κ ^ 2 / 8) (h := 3 * κ ^ 2 / 8) (by positivity)
        (by linarith) (by rw [hM]; linarith)
      have e : -2 - κ ^ 2 / 8 + 3 * κ ^ 2 / 8 = -2 + κ ^ 2 / 4 := by ring
      rw [e] at this
      refine this.trans_lt ?_
      rw [Real.sqrt_lt' hκ0]
      nlinarith
    · have h8 : 8 ≤ g * κ ^ 2 := by rwa [div_le_iff₀ hκ2'] at hl
      have hg1 : 1 ≤ g := by nlinarith
      have hM : max 1 g = g := max_eq_right hg1
      have hg0 : 0 < g := by linarith
      have := Fdist_le_sqrt g hg (x := -2) (h := κ ^ 2 / 4) (by positivity)
        (by linarith) (by
          rw [hM]
          have : (2 * g + 2) / g ≤ 2 + κ ^ 2 / 4 := by
            rw [div_le_iff₀ hg0]
            nlinarith
          linarith)
      refine this.trans_lt ?_
      rw [Real.sqrt_lt' hκ0]
      nlinarith
  linarith

end LSBA
