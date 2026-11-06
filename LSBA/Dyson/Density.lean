import LSBA.Dyson.Band

/-!
# The density of `ν_g`

`F_g(x) = π⁻¹ ∫_{(-∞, x]} Im m_g(E + i0) dE`, the literal form of (1.10) [eq:distribution].
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-! ### A uniform integrable bound on `Im m_g(E + iη)` -/

private lemma density_norm_inv_sub_le {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    ‖((t : ℂ) - z)⁻¹‖ ≤ z.im⁻¹ := by
  have hne : ((t : ℂ) - z) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  rw [norm_inv]
  apply inv_anti₀ hz
  have h1 : |((t : ℂ) - z).im| ≤ ‖(t : ℂ) - z‖ := Complex.abs_im_le_norm _
  have h2 : ((t : ℂ) - z).im = -z.im := by simp
  rw [h2, abs_neg, abs_of_pos hz] at h1
  exact h1

private lemma density_continuous_inv_sub {z : ℂ} (hz : 0 < z.im) :
    Continuous (fun t : ℝ => ((t : ℂ) - z)⁻¹) := by
  refine (continuous_ofReal.sub continuous_const).inv₀ fun t => ?_
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- `Im ∫ (t - (E + iη))⁻¹ dν(t) = ∫ η / ((t - E)² + η²) dν(t)`. -/
private lemma density_im_stieltjes (ν : Measure ℝ) [IsFiniteMeasure ν] (E : ℝ) {η : ℝ}
    (hη : 0 < η) :
    (∫ t, ((t : ℂ) - ((E : ℂ) + η * I))⁻¹ ∂ν).im = ∫ t, η / ((t - E) ^ 2 + η ^ 2) ∂ν := by
  have hz : 0 < ((E : ℂ) + η * I).im := by simpa using hη
  have hint : Integrable (fun t : ℝ => ((t : ℂ) - ((E : ℂ) + η * I))⁻¹) ν :=
    Integrable.of_bound (density_continuous_inv_sub hz).aestronglyMeasurable _
      (Eventually.of_forall (density_norm_inv_sub_le hz))
  have h := integral_im hint
  simp only [RCLike.im_to_complex] at h
  rw [← h]
  congr 1
  ext t
  simp [Complex.inv_im, Complex.normSq_apply]
  ring

/-- The constant of the integrable majorant of `Im m_g(E + iη)`. -/
private def densityK (g : ℝ) : ℝ :=
  max 1 g * (1 + ((2 * g + 2) / max 1 g + 1) ^ 2) + 3 + 2 * ((2 * g + 2) / max 1 g) ^ 2

private lemma density_im_le (g : ℝ) (hg : 0 ≤ g) (E : ℝ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (mDyson g (E + η * I)).im ≤ densityK g / (1 + E ^ 2) := by
  have hz : 0 < ((E : ℂ) + η * I).im := by simpa using hη
  have hM0 : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  set M := max 1 g with hM
  set R := (2 * g + 2) / M with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hK : densityK g = M * (1 + (R + 1) ^ 2) + 3 + 2 * R ^ 2 := rfl
  have hpos : 0 < 1 + E ^ 2 := by positivity
  by_cases hE : |E| ≤ R + 1
  · have h1 : (mDyson g (E + η * I)).im ≤ M :=
      (Complex.im_le_norm _).trans (mDyson_norm_le_max g hg _ hz)
    refine h1.trans ?_
    rw [le_div_iff₀ hpos, hK]
    have h2 : E ^ 2 ≤ (R + 1) ^ 2 := by
      rw [← sq_abs E]
      exact pow_le_pow_left₀ (abs_nonneg E) hE 2
    nlinarith [mul_le_mul_of_nonneg_left h2 hM0.le, sq_nonneg R]
  · rw [not_le] at hE
    set s := |E| - R with hs
    have hs1 : 1 < s := by rw [hs]; linarith
    obtain ⟨hP, hS⟩ := nuDyson_spec g hg
    have hae : ∀ᵐ t ∂nuDyson g, t ∈ Set.Icc (-R) R := by
      have := nuDyson_compl_support g hg
      rw [← hR] at this
      exact measure_eq_zero_iff_ae_notMem.1 this |>.mono fun t ht => by simpa using ht
    have himm : (mDyson g (E + η * I)).im = ∫ t, η / ((t - E) ^ 2 + η ^ 2) ∂nuDyson g := by
      rw [← density_im_stieltjes (nuDyson g) E hη]
      have := hS _ hz
      unfold stieltjes at this
      rw [this]
    have hbd : (mDyson g (E + η * I)).im ≤ 1 / s ^ 2 := by
      rw [himm]
      have := integral_mono_of_nonneg (μ := nuDyson g)
        (f := fun t : ℝ => η / ((t - E) ^ 2 + η ^ 2)) (g := fun _ => 1 / s ^ 2)
        (Eventually.of_forall fun t => by positivity) (integrable_const _)
        (hae.mono fun t ht => by
          have hd : s ^ 2 ≤ (t - E) ^ 2 + η ^ 2 := by
            have h3 : s ≤ |t - E| := by
              have h4 : |t| ≤ R := abs_le.2 ⟨ht.1, ht.2⟩
              have h6 := abs_sub_abs_le_abs_sub E t
              rw [abs_sub_comm E t] at h6
              linarith
            have h5 : s ^ 2 ≤ |t - E| ^ 2 := pow_le_pow_left₀ (by linarith) h3 2
            rw [sq_abs] at h5
            nlinarith [sq_nonneg η]
          exact div_le_div₀ zero_le_one hη1 (by positivity) hd)
      simpa using this
    refine hbd.trans ?_
    rw [div_le_div_iff₀ (by positivity) hpos, hK]
    have hE2 : E ^ 2 = (s + R) ^ 2 := by
      rw [← sq_abs E, hs]; ring_nf
    rw [hE2]
    have hs2 : 1 ≤ s ^ 2 := by nlinarith
    nlinarith [sq_nonneg (s - R), sq_nonneg R, mul_nonneg (sq_nonneg R) (sub_nonneg.2 hs2),
      mul_nonneg (sq_nonneg s) (mul_nonneg hM0.le (sq_nonneg (R + 1)))]

private lemma density_continuous_slice (g : ℝ) (hg : 0 ≤ g) {η : ℝ} (hη : 0 < η) :
    Continuous fun E : ℝ => (mDyson g (E + η * I)).im := by
  have hz : ∀ E : ℝ, 0 < ((E : ℂ) + η * I).im := fun E => by simpa using hη
  exact Complex.continuous_im.comp ((mDyson_differentiableOn g hg).continuousOn.comp_continuous
    (by fun_prop) hz)

private lemma density_integrable_majorant (g : ℝ) :
    Integrable (fun E : ℝ => densityK g / (1 + E ^ 2)) := by
  have := (integrable_inv_one_add_sq).const_mul (densityK g)
  refine this.congr (Eventually.of_forall fun E => ?_)
  simp [div_eq_mul_inv]

private lemma density_Fdist (g : ℝ) (hg : 0 ≤ g) (x : ℝ) :
    Fdist g x = π⁻¹ * ∫ E in Set.Iic x, (mDysonBdry g E).im := by
  have hlim := (Fdist_eq_limit g hg x)
  have hdom : Tendsto (fun η : ℝ => ∫ E in Set.Iic x, (mDyson g (E + η * I)).im) (𝓝[>] 0)
      (𝓝 (∫ E in Set.Iic x, (mDysonBdry g E).im)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun E => densityK g / (1 + E ^ 2)) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact (density_continuous_slice g hg hη).aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT one_pos] with η hη
      refine Eventually.of_forall fun E => ?_
      have hz : 0 < ((E : ℂ) + η * I).im := by simpa using hη.1
      rw [Real.norm_of_nonneg (mDyson_spec g hg _ hz).1.le]
      exact density_im_le g hg E hη.1 hη.2
    · exact (density_integrable_majorant g).integrableOn
    · exact Eventually.of_forall fun E =>
        (Complex.continuous_im.tendsto _).comp (mDysonBdry_tendsto g hg E)
  exact tendsto_nhds_unique hlim (hdom.const_mul π⁻¹)

/-- (1.10) [eq:distribution], literal form. -/
theorem Fdist_eq_integral_bdry (g : ℝ) (hg : 0 ≤ g) (x : ℝ) :
    Fdist g x = π⁻¹ * ∫ E in Set.Iic x, (mDysonBdry g E).im := density_Fdist g hg x

end LSBA
