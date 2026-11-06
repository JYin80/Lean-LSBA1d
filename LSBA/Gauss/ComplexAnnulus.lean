import LSBA.Gauss.CGauss

/-!
# Small-ball bounds for a shifted complex Gaussian

For `x = γ + β` with `γ` standard complex Gaussian and `β ∈ ℂ`: `|x|²` lies in an interval of length
`δ` with probability `O(δ / (1 + |β|))`; and `P(|x| ≥ t ||x|² - c|) = O(1/t)`. These are the
one-coordinate inputs of the quadratic-form bound behind [APSSS, Lemma 2.1 (2.7)].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### `γ + β` in real coordinates -/

/-- The shifted real Gaussian: `(√2)⁻¹ y + m` with `y ~ N(0, 1)` has law `N(m, 1/2)`. -/
private lemma cGauss_map_affine (m : ℝ) :
    (gaussianReal 0 1).map (fun a : ℝ => (Real.sqrt 2)⁻¹ * a + m) = gaussianReal m (1 / 2) := by
  have h1 := gaussianReal_map_const_mul (μ := (0:ℝ)) (v := (1:ℝ≥0)) (Real.sqrt 2)⁻¹
  have h2 := gaussianReal_map_add_const (μ := (Real.sqrt 2)⁻¹ * 0)
    (v := (NNReal.mk (((Real.sqrt 2)⁻¹) ^ 2) (sq_nonneg _)) * 1) m
  have hf : (fun a : ℝ => (Real.sqrt 2)⁻¹ * a + m) =
      (fun a => a + m) ∘ (fun a => (Real.sqrt 2)⁻¹ * a) := rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), h1, h2]
  congr 1
  · simp
  · ext
    simp [inv_pow]

/-- The real coordinates of `γ + β`: the law of `((√2)⁻¹ y₀ + β₁, (√2)⁻¹ y₁ + β₂)` with `y` standard
Gaussian on `ℝ²` is the product `N(β₁, 1/2) ⊗ N(β₂, 1/2)`. -/
private lemma cGauss_map_coord (β : ℂ) :
    (stdGauss (Fin 2)).map (fun y : Fin 2 → ℝ =>
        ((Real.sqrt 2)⁻¹ * y 0 + β.re, (Real.sqrt 2)⁻¹ * y 1 + β.im)) =
      (gaussianReal β.re (1 / 2)).prod (gaussianReal β.im (1 / 2)) := by
  have hf : (fun y : Fin 2 → ℝ => ((Real.sqrt 2)⁻¹ * y 0 + β.re, (Real.sqrt 2)⁻¹ * y 1 + β.im)) =
      Prod.map (fun a : ℝ => (Real.sqrt 2)⁻¹ * a + β.re) (fun a : ℝ => (Real.sqrt 2)⁻¹ * a + β.im)
        ∘ (MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ) := rfl
  have hm : Measurable (Prod.map (fun a : ℝ => (Real.sqrt 2)⁻¹ * a + β.re)
      (fun a : ℝ => (Real.sqrt 2)⁻¹ * a + β.im)) := by fun_prop
  rw [hf, ← Measure.map_map hm (MeasurableEquiv.measurable _)]
  have h := (measurePreserving_piFinTwo fun _ : Fin 2 => gaussianReal (0:ℝ) 1).map_eq
  unfold stdGauss
  rw [h, ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), cGauss_map_affine,
    cGauss_map_affine]

/-- `P(γ + β ∈ E)` in real coordinates, for measurable `E`. -/
private lemma cGauss_apply_shift (β : ℂ) {E : Set ℂ} (hE : MeasurableSet E) :
    cGauss {z | z + β ∈ E} =
      ((gaussianReal β.re (1 / 2)).prod (gaussianReal β.im (1 / 2)))
        {p : ℝ × ℝ | (⟨p.1, p.2⟩ : ℂ) ∈ E} := by
  have hmk : Measurable (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) :=
    Complex.measurableEquivRealProd.symm.measurable
  have hmap : Measurable (fun y : Fin 2 → ℝ => ((Real.sqrt 2)⁻¹ : ℂ) * ⟨y 0, y 1⟩) := by
    have h2 : Measurable (fun y : Fin 2 → ℝ => (⟨y 0, y 1⟩ : ℂ)) :=
      hmk.comp (f := fun y : Fin 2 → ℝ => (y 0, y 1))
        ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
    exact h2.const_mul _
  have hS : MeasurableSet {p : ℝ × ℝ | (⟨p.1, p.2⟩ : ℂ) ∈ E} := hE.preimage hmk
  rw [← cGauss_map_coord, Measure.map_apply (by fun_prop) hS]
  unfold cGauss
  rw [show {z : ℂ | z + β ∈ E} = (fun z : ℂ => z + β) ⁻¹' E from rfl,
    Measure.map_apply hmap (hE.preimage (by fun_prop))]
  congr 1
  ext y
  change (((Real.sqrt 2)⁻¹ : ℂ) * ⟨y 0, y 1⟩ + β) ∈ E ↔
    (⟨(Real.sqrt 2)⁻¹ * y 0 + β.re, (Real.sqrt 2)⁻¹ * y 1 + β.im⟩ : ℂ) ∈ E
  have : ((Real.sqrt 2)⁻¹ : ℂ) * ⟨y 0, y 1⟩ + β =
      ⟨(Real.sqrt 2)⁻¹ * y 0 + β.re, (Real.sqrt 2)⁻¹ * y 1 + β.im⟩ := by
    apply Complex.ext <;> simp [Real.sqrt_div_self']
  rw [this]

/-! ### Section and density bounds -/

private lemma cGauss_measurable_mk : Measurable (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) :=
  Complex.measurableEquivRealProd.symm.measurable

/-- The density of `N(m, 1/2)` is at most `1`. -/
private lemma cGauss_gaussianPDFReal_le_one (m x : ℝ) : gaussianPDFReal m (1 / 2) x ≤ 1 := by
  rw [gaussianPDFReal_def]
  have h1 : (Real.sqrt (2 * π * ((1 / 2 : ℝ≥0) : ℝ)))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    rw [Real.one_le_sqrt]
    norm_num
    linarith [Real.pi_gt_three]
  have h2 : rexp (-(x - m) ^ 2 / (2 * ((1 / 2 : ℝ≥0) : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (x - m) ^ 2 := sq_nonneg _
    have h3 : (0:ℝ) < 2 * ((1 / 2 : ℝ≥0) : ℝ) := by norm_num
    rw [div_nonpos_iff]
    right
    exact ⟨by linarith, h3.le⟩
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
    _ = 1 := one_mul 1

/-- `N(m, 1/2)` of a set is at most its Lebesgue measure. -/
private lemma cGauss_gaussianReal_apply_le (m : ℝ) (s : Set ℝ) :
    gaussianReal m (1 / 2) s ≤ volume s := by
  rw [gaussianReal_apply m (by norm_num) s]
  calc ∫⁻ x in s, gaussianPDF m (1 / 2) x ≤ ∫⁻ _ in s, 1 :=
        setLIntegral_mono measurable_const fun x _ => by
          rw [gaussianPDF_def]
          exact ENNReal.ofReal_le_one.mpr (cGauss_gaussianPDFReal_le_one m x)
    _ = volume s := by simp

/-- If every horizontal section of a measurable `E` has length at most `M`, then
`P(γ + β ∈ E) ≤ M`. -/
private lemma cGauss_shift_le_of_sections_re {β : ℂ} {E : Set ℂ} (hE : MeasurableSet E) {M : ℝ}
    (hM : ∀ v : ℝ, volume {u : ℝ | (⟨u, v⟩ : ℂ) ∈ E} ≤ ENNReal.ofReal M) :
    cGauss {z | z + β ∈ E} ≤ ENNReal.ofReal M := by
  have hS : MeasurableSet {p : ℝ × ℝ | (⟨p.1, p.2⟩ : ℂ) ∈ E} := hE.preimage cGauss_measurable_mk
  rw [cGauss_apply_shift β hE, Measure.prod_apply_symm hS]
  calc ∫⁻ y, gaussianReal β.re (1 / 2)
        ((fun x => (x, y)) ⁻¹' {p : ℝ × ℝ | (⟨p.1, p.2⟩ : ℂ) ∈ E}) ∂gaussianReal β.im (1 / 2)
      ≤ ∫⁻ _, ENNReal.ofReal M ∂gaussianReal β.im (1 / 2) :=
        lintegral_mono fun y => (cGauss_gaussianReal_apply_le _ _).trans (hM y)
    _ = ENNReal.ofReal M := by simp

/-- If every vertical section of a measurable `E` has length at most `M`, then
`P(γ + β ∈ E) ≤ M`. -/
private lemma cGauss_shift_le_of_sections_im {β : ℂ} {E : Set ℂ} (hE : MeasurableSet E) {M : ℝ}
    (hM : ∀ u : ℝ, volume {v : ℝ | (⟨u, v⟩ : ℂ) ∈ E} ≤ ENNReal.ofReal M) :
    cGauss {z | z + β ∈ E} ≤ ENNReal.ofReal M := by
  have hS : MeasurableSet {p : ℝ × ℝ | (⟨p.1, p.2⟩ : ℂ) ∈ E} := hE.preimage cGauss_measurable_mk
  rw [cGauss_apply_shift β hE, Measure.prod_apply hS]
  calc ∫⁻ x, gaussianReal β.im (1 / 2)
        (Prod.mk x ⁻¹' {p : ℝ × ℝ | (⟨p.1, p.2⟩ : ℂ) ∈ E}) ∂gaussianReal β.re (1 / 2)
      ≤ ∫⁻ _, ENNReal.ofReal M ∂gaussianReal β.re (1 / 2) :=
        lintegral_mono fun x => (cGauss_gaussianReal_apply_le _ _).trans (hM x)
    _ = ENNReal.ofReal M := by simp

/-- The product of two densities of `N(·, 1/2)`. -/
private lemma cGauss_pdf_mul (m₁ m₂ u w : ℝ) :
    gaussianPDFReal m₁ (1 / 2) u * gaussianPDFReal m₂ (1 / 2) w =
      π⁻¹ * rexp (-((u - m₁) ^ 2 + (w - m₂) ^ 2)) := by
  rw [gaussianPDFReal_def, gaussianPDFReal_def]
  have h : 2 * π * ((1 / 2 : ℝ≥0) : ℝ) = π := by push_cast; ring
  have h2 : 2 * ((1 / 2 : ℝ≥0) : ℝ) = 1 := by push_cast; ring
  simp only [h, h2, div_one]
  have hs : (Real.sqrt π)⁻¹ * (Real.sqrt π)⁻¹ = π⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt Real.pi_pos.le]
  calc _ = ((Real.sqrt π)⁻¹ * (Real.sqrt π)⁻¹) * (rexp (-(u - m₁) ^ 2) * rexp (-(w - m₂) ^ 2)) := by
        ring
    _ = _ := by
        rw [hs, ← Real.exp_add]
        congr 2
        ring

/-- The measure of `{p | ⟨p₁, p₂⟩ ∈ E}` in `ℝ × ℝ` is the planar measure of `E`. -/
private lemma cGauss_volume_realProd (E : Set ℂ) :
    (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | (⟨p.1, p.2⟩ : ℂ) ∈ E} = volume E :=
  Complex.volume_preserving_equiv_real_prod.symm.measure_preimage_equiv E

/-- If the density `π⁻¹ exp (-|w - β|²)` of `γ + β` is at most `K / π` on a measurable `E` of
area at most `π δ`, then `P(γ + β ∈ E) ≤ K δ`. -/
private lemma cGauss_shift_le_of_density {β : ℂ} {E : Set ℂ} (hE : MeasurableSet E) {K δ : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ w ∈ E, rexp (-‖w - β‖ ^ 2) ≤ K)
    (hvol : volume E ≤ ENNReal.ofReal (π * δ)) :
    cGauss {z | z + β ∈ E} ≤ ENNReal.ofReal (K * δ) := by
  have hS : MeasurableSet {p : ℝ × ℝ | (⟨p.1, p.2⟩ : ℂ) ∈ E} := hE.preimage cGauss_measurable_mk
  have hv : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  rw [cGauss_apply_shift β hE, gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    prod_withDensity (by fun_prop) (by fun_prop), withDensity_apply _ hS]
  calc ∫⁻ p in {p : ℝ × ℝ | (⟨p.1, p.2⟩ : ℂ) ∈ E},
          gaussianPDF β.re (1 / 2) p.1 * gaussianPDF β.im (1 / 2) p.2 ∂(volume.prod volume)
      ≤ ∫⁻ _ in {p : ℝ × ℝ | (⟨p.1, p.2⟩ : ℂ) ∈ E}, ENNReal.ofReal (K / π)
          ∂(volume.prod volume) := by
        refine setLIntegral_mono measurable_const fun p hp => ?_
        rw [gaussianPDF_def, gaussianPDF_def,
          ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
        apply ENNReal.ofReal_le_ofReal
        rw [cGauss_pdf_mul]
        have h1 := hK _ hp
        have h2 : ‖(⟨p.1, p.2⟩ : ℂ) - β‖ ^ 2 = (p.1 - β.re) ^ 2 + (p.2 - β.im) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp [sq]
        rw [h2] at h1
        rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ENNReal.ofReal (K / π) * volume {p : ℝ × ℝ | (⟨p.1, p.2⟩ : ℂ) ∈ E} := by
        rw [setLIntegral_const]; rfl
    _ ≤ ENNReal.ofReal (K / π) * ENNReal.ofReal (π * δ) := by
        rw [cGauss_volume_realProd]
        exact mul_le_mul' le_rfl hvol
    _ = ENNReal.ofReal (K * δ) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-! ### Areas and thin shells -/

/-- The `norm`-annulus `{w | ‖w‖² ∈ [c, c + δ]}` is measurable. -/
private lemma cGauss_measurableSet_annulus (c δ : ℝ) :
    MeasurableSet {w : ℂ | ‖w‖ ^ 2 ∈ Set.Icc c (c + δ)} :=
  measurableSet_Icc.preimage (by fun_prop)

/-- The area of `{w | ‖w‖² ∈ [c, c + δ]}` is at most `π δ`. -/
private lemma cGauss_volume_annulus_le (c δ : ℝ) (hδ : 0 < δ) :
    volume {w : ℂ | ‖w‖ ^ 2 ∈ Set.Icc c (c + δ)} ≤ ENNReal.ofReal (π * δ) := by
  have hpi : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal π := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hsub : {w : ℂ | ‖w‖ ^ 2 ∈ Set.Icc c (c + δ)} ⊆ Metric.closedBall 0 (Real.sqrt (c + δ)) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    have := Real.abs_le_sqrt hw.2
    rwa [abs_of_nonneg (norm_nonneg w)] at this
  by_cases hc : 0 ≤ c
  · have hdisj : Disjoint (Metric.ball (0 : ℂ) (Real.sqrt c))
        {w : ℂ | ‖w‖ ^ 2 ∈ Set.Icc c (c + δ)} := by
      rw [Set.disjoint_left]
      intro w hw hw'
      rw [Metric.mem_ball, dist_zero_right, Real.lt_sqrt (norm_nonneg w)] at hw
      exact absurd hw'.1 (not_le.mpr hw)
    have hunion : Metric.ball (0 : ℂ) (Real.sqrt c) ∪
        {w : ℂ | ‖w‖ ^ 2 ∈ Set.Icc c (c + δ)} ⊆ Metric.closedBall 0 (Real.sqrt (c + δ)) := by
      refine Set.union_subset ?_ hsub
      intro w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hw.le.trans (Real.sqrt_le_sqrt (by linarith))
    have h1 : volume (Metric.ball (0 : ℂ) (Real.sqrt c)) +
        volume {w : ℂ | ‖w‖ ^ 2 ∈ Set.Icc c (c + δ)} ≤
        volume (Metric.closedBall (0 : ℂ) (Real.sqrt (c + δ))) :=
      calc _ = volume (Metric.ball (0 : ℂ) (Real.sqrt c) ∪
            {w : ℂ | ‖w‖ ^ 2 ∈ Set.Icc c (c + δ)}) :=
            (measure_union hdisj (cGauss_measurableSet_annulus c δ)).symm
        _ ≤ _ := measure_mono hunion
    rw [Complex.volume_ball, Complex.volume_closedBall, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hc, Real.sq_sqrt (by linarith),
      hpi, ENNReal.ofReal_add hc hδ.le, add_mul] at h1
    have h2 := (ENNReal.add_le_add_iff_left
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)).mp h1
    rwa [← ENNReal.ofReal_mul hδ.le, mul_comm] at h2
  · have hc := not_le.mp hc
    refine (measure_mono hsub).trans ?_
    rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), hpi,
      ← ENNReal.ofReal_mul (by positivity), mul_comm]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    by_cases h : 0 ≤ c + δ
    · rw [Real.sq_sqrt h]; linarith
    · rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]; simp [hδ.le]

/-- The set of `u` with `|u| ≥ s₀` and `u² ∈ [A, B]` has length at most `2 (B - A) / s₀`. -/
private lemma cGauss_volume_sq_le (s₀ A B : ℝ) (hs : 0 < s₀) :
    volume {u : ℝ | s₀ ≤ |u| ∧ A ≤ u ^ 2 ∧ u ^ 2 ≤ B} ≤ ENNReal.ofReal (2 * (B - A) / s₀) := by
  by_cases hne : {u : ℝ | s₀ ≤ |u| ∧ A ≤ u ^ 2 ∧ u ^ 2 ≤ B}.Nonempty
  · obtain ⟨u₀, h0s, h0A, h0B⟩ := hne
    have hBA : 0 ≤ B - A := by linarith
    have hD0 : 0 ≤ (B - A) / (2 * s₀) := by positivity
    have hDe : (B - A) / (2 * s₀) * (2 * s₀) = B - A := by field_simp
    have hsub : {u : ℝ | s₀ ≤ |u| ∧ A ≤ u ^ 2 ∧ u ^ 2 ≤ B} ⊆
        Set.Icc (|u₀| - (B - A) / (2 * s₀)) (|u₀| + (B - A) / (2 * s₀)) ∪
          Set.Icc (-|u₀| - (B - A) / (2 * s₀)) (-|u₀| + (B - A) / (2 * s₀)) := by
      rintro u ⟨hus, huA, huB⟩
      have h1 : |u| ^ 2 = u ^ 2 := sq_abs u
      have h2 : |u₀| ^ 2 = u₀ ^ 2 := sq_abs u₀
      have hd : abs (|u| - |u₀|) ≤ (B - A) / (2 * s₀) := by
        rw [abs_le]
        constructor
        · by_contra h
          have h := not_le.mp h
          nlinarith [mul_pos hs hs]
        · by_contra h
          have h := not_le.mp h
          nlinarith [mul_pos hs hs]
      rw [abs_le] at hd
      rcases le_total 0 u with hu | hu
      · left
        rw [abs_of_nonneg hu] at hd
        exact ⟨by linarith [hd.1, hd.2], by linarith [hd.1, hd.2]⟩
      · right
        rw [abs_of_nonpos hu] at hd
        exact ⟨by linarith [hd.1, hd.2], by linarith [hd.1, hd.2]⟩
    calc _ ≤ volume (Set.Icc (|u₀| - (B - A) / (2 * s₀)) (|u₀| + (B - A) / (2 * s₀)) ∪
          Set.Icc (-|u₀| - (B - A) / (2 * s₀)) (-|u₀| + (B - A) / (2 * s₀))) := measure_mono hsub
      _ ≤ volume (Set.Icc (|u₀| - (B - A) / (2 * s₀)) (|u₀| + (B - A) / (2 * s₀))) +
          volume (Set.Icc (-|u₀| - (B - A) / (2 * s₀)) (-|u₀| + (B - A) / (2 * s₀))) :=
        measure_union_le _ _
      _ = ENNReal.ofReal (2 * (B - A) / s₀) := by
        rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        field_simp
        ring
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

/-- A point of the shell `||w| - r| ≤ h` has squared coordinates summing to `[(r-h)², (r+h)²]`. -/
private lemma cGauss_shell_sq (w : ℂ) {r h : ℝ} (hh : h ≤ r) (hw : |‖w‖ - r| ≤ h) :
    (r - h) ^ 2 ≤ w.re ^ 2 + w.im ^ 2 ∧ w.re ^ 2 + w.im ^ 2 ≤ (r + h) ^ 2 := by
  have h2 : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [h2]
  rw [abs_le] at hw
  exact ⟨pow_le_pow_left₀ (by linarith) (by linarith) 2,
    pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2⟩

/-- The shell `{w | ||w| - r| ≤ h}` is measurable. -/
private lemma cGauss_measurableSet_shell (r h : ℝ) :
    MeasurableSet {w : ℂ | |‖w‖ - r| ≤ h} :=
  measurableSet_le (by fun_prop) measurable_const

/-! ### The two bounds with explicit constants -/

/-- `P(||γ + β| - r| ≤ h) ≤ 64 h`. -/
private lemma cGauss_abs_norm_sub_le_aux (β : ℂ) (r h : ℝ) (hh : 0 < h) :
    cGauss {z | |‖z + β‖ - r| ≤ h} ≤ ENNReal.ofReal (64 * h) := by
  by_cases hrh : r ≤ 2 * h
  · -- the event lies in `|Re x| ≤ 3h`
    have hE : MeasurableSet {w : ℂ | |w.re| ≤ 3 * h} :=
      measurableSet_le (by fun_prop) measurable_const
    have h1 : cGauss {z | |‖z + β‖ - r| ≤ h} ≤ cGauss {z | z + β ∈ {w : ℂ | |w.re| ≤ 3 * h}} := by
      refine measure_mono fun z hz => ?_
      have hz' : |‖z + β‖ - r| ≤ h := hz
      rw [abs_le] at hz'
      change |(z + β).re| ≤ 3 * h
      exact (Complex.abs_re_le_norm _).trans (by linarith)
    refine h1.trans ((cGauss_shift_le_of_sections_re hE (M := 6 * h) fun v => ?_).trans ?_)
    · have : {u : ℝ | (⟨u, v⟩ : ℂ) ∈ {w : ℂ | |w.re| ≤ 3 * h}} = Set.Icc (-(3 * h)) (3 * h) := by
        ext u
        simp [abs_le]
      rw [this, Real.volume_Icc]
      apply le_of_eq
      congr 1
      ring
    · exact ENNReal.ofReal_le_ofReal (by linarith)
  · have hr0 : 0 < r := by linarith
    have hrh' : h ≤ r := by linarith
    set E₁ : Set ℂ := {w : ℂ | |‖w‖ - r| ≤ h ∧ r / 4 ≤ |w.re|} with hE₁
    set E₂ : Set ℂ := {w : ℂ | |‖w‖ - r| ≤ h ∧ r / 4 ≤ |w.im|} with hE₂
    have hm₁ : MeasurableSet E₁ := by
      have h2 : MeasurableSet {w : ℂ | r / 4 ≤ |w.re|} :=
        measurableSet_le measurable_const (by fun_prop)
      exact (cGauss_measurableSet_shell r h).inter h2
    have hm₂ : MeasurableSet E₂ := by
      have h2 : MeasurableSet {w : ℂ | r / 4 ≤ |w.im|} :=
        measurableSet_le measurable_const (by fun_prop)
      exact (cGauss_measurableSet_shell r h).inter h2
    have hcover : {z : ℂ | |‖z + β‖ - r| ≤ h} ⊆
        {z : ℂ | z + β ∈ E₁} ∪ {z : ℂ | z + β ∈ E₂} := by
      intro z hz
      have hz' : |‖z + β‖ - r| ≤ h := hz
      have hn : r - h ≤ ‖z + β‖ := by rw [abs_le] at hz'; linarith
      have hle : ‖z + β‖ ≤ |(z + β).re| + |(z + β).im| := Complex.norm_le_abs_re_add_abs_im _
      by_cases hre : r / 4 ≤ |(z + β).re|
      · exact Or.inl ⟨hz', hre⟩
      · exact Or.inr ⟨hz', by linarith⟩
    have hsec₁ : ∀ v : ℝ, volume {u : ℝ | (⟨u, v⟩ : ℂ) ∈ E₁} ≤ ENNReal.ofReal (32 * h) := by
      intro v
      refine (measure_mono ?_).trans (cGauss_volume_sq_le (r / 4) ((r - h) ^ 2 - v ^ 2)
        ((r + h) ^ 2 - v ^ 2) (by linarith)) |>.trans (le_of_eq ?_)
      · rintro u ⟨hu, hu'⟩
        have := cGauss_shell_sq (⟨u, v⟩ : ℂ) hrh' hu
        refine ⟨hu', ?_, ?_⟩ <;> simp only at this <;> linarith [this.1, this.2]
      · congr 1
        field_simp
        ring
    have hsec₂ : ∀ u : ℝ, volume {v : ℝ | (⟨u, v⟩ : ℂ) ∈ E₂} ≤ ENNReal.ofReal (32 * h) := by
      intro u
      refine (measure_mono ?_).trans (cGauss_volume_sq_le (r / 4) ((r - h) ^ 2 - u ^ 2)
        ((r + h) ^ 2 - u ^ 2) (by linarith)) |>.trans (le_of_eq ?_)
      · rintro v ⟨hv, hv'⟩
        have := cGauss_shell_sq (⟨u, v⟩ : ℂ) hrh' hv
        refine ⟨hv', ?_, ?_⟩ <;> simp only at this <;> linarith [this.1, this.2]
      · congr 1
        field_simp
        ring
    calc cGauss {z | |‖z + β‖ - r| ≤ h}
        ≤ cGauss ({z : ℂ | z + β ∈ E₁} ∪ {z : ℂ | z + β ∈ E₂}) := measure_mono hcover
      _ ≤ cGauss {z : ℂ | z + β ∈ E₁} + cGauss {z : ℂ | z + β ∈ E₂} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (32 * h) + ENNReal.ofReal (32 * h) :=
          add_le_add (cGauss_shift_le_of_sections_re hm₁ hsec₁)
            (cGauss_shift_le_of_sections_im hm₂ hsec₂)
      _ = ENNReal.ofReal (64 * h) := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1
          ring

/-- `P(|γ + β|² ∈ [c, c + δ]) ≤ 50 δ / (1 + |β|)`. -/
private lemma cGauss_normSq_mem_Icc_le_aux (β : ℂ) (c δ : ℝ) (hδ : 0 < δ) :
    cGauss {z | ‖z + β‖ ^ 2 ∈ Set.Icc c (c + δ)} ≤ ENNReal.ofReal (50 * δ / (1 + ‖β‖)) := by
  have hb0 : 0 ≤ ‖β‖ := norm_nonneg β
  have hE := cGauss_measurableSet_annulus c δ
  have hvol := cGauss_volume_annulus_le c δ hδ
  by_cases hb : ‖β‖ ≤ 2
  · -- the density is at most `1/π`
    have h1 := cGauss_shift_le_of_density (β := β) hE (K := 1) zero_le_one
      (fun w _ => Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖w - β‖])) hvol
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · have hb := not_le.mp hb
    by_cases hc : ‖β‖ ^ 2 / 4 ≤ c
    · -- the event is a shell `||x| - r| ≤ h`
      have hc0 : 0 < c := by nlinarith
      have hs : ‖β‖ / 2 ≤ Real.sqrt c := by
        have := Real.abs_le_sqrt (x := ‖β‖ / 2) (y := c) (by nlinarith)
        exact (le_abs_self _).trans this
      have hss : Real.sqrt c < Real.sqrt (c + δ) := Real.sqrt_lt_sqrt hc0.le (by linarith)
      have hsq1 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0.le
      have hsq2 : Real.sqrt (c + δ) ^ 2 = c + δ := Real.sq_sqrt (by linarith)
      set h := (Real.sqrt (c + δ) - Real.sqrt c) / 2 with hh
      set r := (Real.sqrt c + Real.sqrt (c + δ)) / 2 with hr
      have hh0 : 0 < h := by rw [hh]; linarith
      have hsub : {z : ℂ | ‖z + β‖ ^ 2 ∈ Set.Icc c (c + δ)} ⊆ {z : ℂ | |‖z + β‖ - r| ≤ h} := by
        intro z hz
        have hz' : ‖z + β‖ ^ 2 ∈ Set.Icc c (c + δ) := hz
        have h1 : Real.sqrt c ≤ ‖z + β‖ := by
          have := Real.sqrt_le_sqrt hz'.1
          rwa [Real.sqrt_sq (norm_nonneg _)] at this
        have h2 : ‖z + β‖ ≤ Real.sqrt (c + δ) := by
          have := Real.abs_le_sqrt hz'.2
          rwa [abs_of_nonneg (norm_nonneg _)] at this
        change |‖z + β‖ - r| ≤ h
        rw [abs_le]
        constructor <;> linarith
      have h2b : 2 * h * ‖β‖ ≤ δ := by
        nlinarith [mul_pos (sub_pos.mpr hss)
          (by linarith : (0 : ℝ) < Real.sqrt c + Real.sqrt (c + δ))]
      refine (measure_mono hsub).trans ((cGauss_abs_norm_sub_le_aux β r h hh0).trans
        (ENNReal.ofReal_le_ofReal ?_))
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · have hc := not_le.mp hc
      by_cases hd : ‖β‖ ^ 2 / 8 ≤ δ
      · -- trivial bound by one
        refine prob_le_one.trans ?_
        rw [ENNReal.one_le_ofReal, le_div_iff₀ (by positivity)]
        nlinarith
      · have hd := not_le.mp hd
        -- the event avoids a neighbourhood of `β`, where the density is small
        have hK : ∀ w ∈ {w : ℂ | ‖w‖ ^ 2 ∈ Set.Icc c (c + δ)},
            rexp (-‖w - β‖ ^ 2) ≤ rexp (-(‖β‖ ^ 2 / 8)) := by
          intro w hw
          have hw2 : ‖w‖ ^ 2 ≤ c + δ := hw.2
          have hw3 : ‖w‖ ≤ 62 / 100 * ‖β‖ := by
            by_contra h
            have h := not_le.mp h
            nlinarith [norm_nonneg w]
          have hw4 : ‖β‖ - ‖w‖ ≤ ‖w - β‖ := by
            rw [norm_sub_rev]; exact norm_sub_norm_le _ _
          apply Real.exp_le_exp.mpr
          nlinarith [norm_nonneg (w - β)]
        have h1 := cGauss_shift_le_of_density (β := β) hE (Real.exp_pos _).le hK hvol
        refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
        have h3 : 1 + ‖β‖ ≤ 3 * rexp (‖β‖ ^ 2 / 8) := by
          have := Real.add_one_le_exp (‖β‖ ^ 2 / 8)
          nlinarith [sq_nonneg (‖β‖ - 4)]
        have h4 : rexp (-(‖β‖ ^ 2 / 8)) * (1 + ‖β‖) ≤ 3 := by
          rw [Real.exp_neg]
          calc (rexp (‖β‖ ^ 2 / 8))⁻¹ * (1 + ‖β‖)
              ≤ (rexp (‖β‖ ^ 2 / 8))⁻¹ * (3 * rexp (‖β‖ ^ 2 / 8)) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = 3 := by field_simp
        rw [le_div_iff₀ (by positivity)]
        nlinarith [mul_pos hδ (Real.exp_pos (-(‖β‖ ^ 2 / 8)))]

/-- `P(|x| ≥ t ||x|² - c|) ≤ 64 / t`. -/
private lemma cGauss_norm_ge_mul_abs_le_aux (β : ℂ) (c t : ℝ) (ht : 0 < t) :
    cGauss {z | t * |‖z + β‖ ^ 2 - c| ≤ ‖z + β‖} ≤ ENNReal.ofReal (64 / t) := by
  have h64 : (64 : ℝ) / t = 64 * (1 / t) := by ring
  rw [h64]
  by_cases hc : c ≤ 0
  · refine (measure_mono ?_).trans (cGauss_abs_norm_sub_le_aux β 0 (1 / t) (by positivity))
    intro z hz
    have hz' : t * |‖z + β‖ ^ 2 - c| ≤ ‖z + β‖ := hz
    change |‖z + β‖ - 0| ≤ 1 / t
    have hn := norm_nonneg (z + β)
    rw [sub_zero, abs_of_nonneg hn, le_div_iff₀ ht]
    have h1 : ‖z + β‖ ^ 2 ≤ |‖z + β‖ ^ 2 - c| := by
      rw [abs_of_nonneg (by nlinarith [sq_nonneg ‖z + β‖])]; linarith
    by_contra h
    have h := not_le.mp h
    nlinarith [mul_le_mul_of_nonneg_left h1 ht.le]
  · have hc := not_le.mp hc
    have hr := Real.sqrt_pos.mpr hc
    have hr2 := Real.sq_sqrt hc.le
    refine (measure_mono ?_).trans
      (cGauss_abs_norm_sub_le_aux β (Real.sqrt c) (1 / t) (by positivity))
    intro z hz
    have hz' : t * |‖z + β‖ ^ 2 - c| ≤ ‖z + β‖ := hz
    change |‖z + β‖ - Real.sqrt c| ≤ 1 / t
    have hn := norm_nonneg (z + β)
    have h1 : |‖z + β‖ ^ 2 - c| = |‖z + β‖ - Real.sqrt c| * (‖z + β‖ + Real.sqrt c) := by
      rw [← abs_of_pos (by positivity : 0 < ‖z + β‖ + Real.sqrt c), ← abs_mul]
      · congr 1
        nlinarith
    rw [le_div_iff₀ ht]
    by_contra h
    have h := not_le.mp h
    rw [h1] at hz'
    nlinarith [mul_pos (lt_of_lt_of_le zero_lt_one h.le) hr]

/-- `P(|γ + β|² ∈ [c, c + δ]) ≤ C δ / (1 + |β|)` for every shift `β`, `c ∈ ℝ` and `δ > 0`. -/
theorem cGauss_normSq_mem_Icc_le : ∃ C : ℝ, 0 < C ∧
    ∀ (β : ℂ) (c δ : ℝ), 0 < δ →
      cGauss {z | ‖z + β‖ ^ 2 ∈ Set.Icc c (c + δ)} ≤ ENNReal.ofReal (C * δ / (1 + ‖β‖)) := by
  exact ⟨50, by norm_num, fun β c δ hδ => cGauss_normSq_mem_Icc_le_aux β c δ hδ⟩

/-- `P(|x| ≥ t ||x|² - c|) ≤ C / t` for `x = γ + β`, every `c ∈ ℝ` and `t > 0`; the complex form
of [APSSS, Claim 6.1]. -/
theorem cGauss_norm_ge_mul_abs_le : ∃ C : ℝ, 0 < C ∧
    ∀ (β : ℂ) (c t : ℝ), 0 < t →
      cGauss {z | t * |‖z + β‖ ^ 2 - c| ≤ ‖z + β‖} ≤ ENNReal.ofReal (C / t) := by
  exact ⟨64, by norm_num, fun β c t ht => cGauss_norm_ge_mul_abs_le_aux β c t ht⟩

end LSBA
