import LSBA.Gauss.Haar

/-!
# Haar columns

A column `U v` of a Haar unitary, for a unit vector `v`, has the law of a normalized standard
complex Gaussian vector. Consequences used in Appendix D.1 [subsec:pf_thm31]: the exponential bound
on the mass of a prescribed set of coordinates.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- Complex vector from `2W` real coordinates. -/
def cplxVec (W : ℕ) (x : Fin W × Fin 2 → ℝ) : Fin W → ℂ := fun i => ⟨x (i, 0), x (i, 1)⟩

/-- Euclidean normalization `v / ‖v‖₂`. -/
def normalize {W : ℕ} (v : Fin W → ℂ) : Fin W → ℂ :=
  ((Real.sqrt (∑ i, ‖v i‖ ^ 2))⁻¹ : ℂ) • v

/-! ### Real and complex coordinates -/

/-- The `2W` real coordinates of a complex vector (inverse of `cplxVec`). -/
private def sphere_realify {W : ℕ} (y : Fin W → ℂ) : Fin W × Fin 2 → ℝ :=
  fun p => if p.2 = 0 then (y p.1).re else (y p.1).im

private lemma sphere_cplxVec_realify {W : ℕ} (y : Fin W → ℂ) :
    cplxVec W (sphere_realify y) = y := by
  funext i
  apply Complex.ext <;> simp [cplxVec, sphere_realify]

private lemma sphere_realify_cplxVec {W : ℕ} (x : Fin W × Fin 2 → ℝ) :
    sphere_realify (cplxVec W x) = x := by
  funext p
  rcases p with ⟨i, k⟩
  fin_cases k <;> simp [cplxVec, sphere_realify]

private lemma sphere_cplxVec_add {W : ℕ} (x y : Fin W × Fin 2 → ℝ) :
    cplxVec W (x + y) = cplxVec W x + cplxVec W y := by
  funext i
  apply Complex.ext <;> simp [cplxVec]

private lemma sphere_cplxVec_smul {W : ℕ} (c : ℝ) (x : Fin W × Fin 2 → ℝ) :
    cplxVec W (c • x) = (c : ℂ) • cplxVec W x := by
  funext i
  apply Complex.ext <;> simp [cplxVec]

private lemma sphere_realify_add {W : ℕ} (y z : Fin W → ℂ) :
    sphere_realify (y + z) = sphere_realify y + sphere_realify z := by
  funext p
  by_cases h : p.2 = 0 <;> simp [sphere_realify, h]

private lemma sphere_realify_smul {W : ℕ} (c : ℝ) (y : Fin W → ℂ) :
    sphere_realify ((c : ℂ) • y) = c • sphere_realify y := by
  funext p
  by_cases h : p.2 = 0 <;> simp [sphere_realify, h]

private lemma sphere_cplxVec_apply {W : ℕ} (x : Fin W × Fin 2 → ℝ) (i : Fin W) :
    cplxVec W x i = (x (i, 0) : ℂ) + (x (i, 1) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [cplxVec]

private lemma sphere_continuous_cplxVec (W : ℕ) : Continuous (cplxVec W) := by
  have : cplxVec W = fun x i => (x (i, 0) : ℂ) + (x (i, 1) : ℂ) * Complex.I := by
    funext x i
    exact sphere_cplxVec_apply x i
  rw [this]
  fun_prop

/-- `∑ₚ xₚ² = ∑ᵢ |gᵢ|²` for `g = cplxVec W x`. -/
private lemma sphere_sum_sq {W : ℕ} (x : Fin W × Fin 2 → ℝ) :
    ∑ p, x p ^ 2 = ∑ i, ‖cplxVec W x i‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two, Complex.sq_norm]
  simp [cplxVec, Complex.normSq_mk]
  ring

private lemma sphere_star_dotProduct {W : ℕ} (z : Fin W → ℂ) :
    star z ⬝ᵥ z = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
  push_cast
  rfl

/-- A unitary matrix preserves `∑ᵢ |yᵢ|²`. -/
private lemma sphere_sum_norm_mulVec {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ)
    (y : Fin W → ℂ) :
    ∑ i, ‖((U : Matrix (Fin W) (Fin W) ℂ).mulVec y) i‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
  have hU : star (U : Matrix (Fin W) (Fin W) ℂ) * (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  have h : star ((U : Matrix (Fin W) (Fin W) ℂ).mulVec y) ⬝ᵥ
      ((U : Matrix (Fin W) (Fin W) ℂ).mulVec y) = star y ⬝ᵥ y := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, hU, Matrix.one_mulVec]
  rw [sphere_star_dotProduct, sphere_star_dotProduct] at h
  exact_mod_cast h

/-- `|normalize(y)ᵢ|² = |yᵢ|² / ∑ₖ |yₖ|²`, also for `y = 0`. -/
private lemma sphere_norm_normalize_sq {W : ℕ} (y : Fin W → ℂ) (i : Fin W) :
    ‖normalize y i‖ ^ 2 = ‖y i‖ ^ 2 / ∑ k, ‖y k‖ ^ 2 := by
  have hN : 0 ≤ ∑ k, ‖y k‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
  simp only [normalize, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, inv_pow, sq_abs, Real.sq_sqrt hN]
  rw [div_eq_inv_mul]

private lemma sphere_normalize_mulVec {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ)
    (y : Fin W → ℂ) :
    (U : Matrix (Fin W) (Fin W) ℂ).mulVec (normalize y) =
      normalize ((U : Matrix (Fin W) (Fin W) ℂ).mulVec y) := by
  simp only [normalize]
  rw [Matrix.mulVec_smul, sphere_sum_norm_mulVec]

private lemma sphere_measurable_normalize (W : ℕ) :
    Measurable (normalize : (Fin W → ℂ) → (Fin W → ℂ)) := by
  unfold normalize
  fun_prop

/-! ### Unitary invariance of the normalized Gaussian -/

/-- A unitary `U` of `ℂ^W` acting on the `2W` real coordinates, as a real isometry. -/
private def sphere_iso {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ) :
    EuclideanSpace ℝ (Fin W × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin W × Fin 2) where
  toFun z := WithLp.toLp 2
    (sphere_realify ((U : Matrix (Fin W) (Fin W) ℂ).mulVec (cplxVec W z.ofLp)))
  invFun z := WithLp.toLp 2
    (sphere_realify ((star (U : Matrix (Fin W) (Fin W) ℂ)).mulVec (cplxVec W z.ofLp)))
  map_add' a b := by
    simp only [WithLp.ofLp_add, sphere_cplxVec_add, Matrix.mulVec_add, sphere_realify_add,
      WithLp.toLp_add]
  map_smul' c a := by
    simp only [WithLp.ofLp_smul, sphere_cplxVec_smul, Matrix.mulVec_smul, sphere_realify_smul,
      WithLp.toLp_smul, RingHom.id_apply]
  left_inv z := by
    have hU : star (U : Matrix (Fin W) (Fin W) ℂ) * (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp U.2
    simp only [sphere_cplxVec_realify, Matrix.mulVec_mulVec, hU,
      Matrix.one_mulVec, sphere_realify_cplxVec, WithLp.toLp_ofLp]
  right_inv z := by
    have hU : (U : Matrix (Fin W) (Fin W) ℂ) * star (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp U.2
    simp only [sphere_cplxVec_realify, Matrix.mulVec_mulVec, hU,
      Matrix.one_mulVec, sphere_realify_cplxVec, WithLp.toLp_ofLp]
  norm_map' z := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [Real.norm_eq_abs, sq_abs]
    rw [sphere_sum_sq, sphere_cplxVec_realify, sphere_sum_norm_mulVec, ← sphere_sum_sq]

private lemma sphere_iso_apply {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ)
    (x : Fin W × Fin 2 → ℝ) :
    cplxVec W (sphere_iso U (WithLp.toLp 2 x)).ofLp =
      (U : Matrix (Fin W) (Fin W) ℂ).mulVec (cplxVec W x) := by
  change cplxVec W (sphere_realify ((U : Matrix (Fin W) (Fin W) ℂ).mulVec (cplxVec W x))) = _
  rw [sphere_cplxVec_realify]

private lemma sphere_measurable_normalize_cplxVec (W : ℕ) :
    Measurable (fun x : Fin W × Fin 2 → ℝ => normalize (cplxVec W x)) :=
  (sphere_measurable_normalize W).comp (sphere_continuous_cplxVec W).measurable

private lemma sphere_measurable_mulVec {W : ℕ} (U : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (fun w : Fin W → ℂ => U.mulVec w) :=
  (Continuous.matrix_mulVec continuous_const continuous_id).measurable

/-- The law of `normalize (cplxVec W x)` is invariant under every unitary. -/
private lemma sphere_invariant {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ)
    {A : Set (Fin W → ℂ)} (hA : MeasurableSet A) :
    stdGauss (Fin W × Fin 2)
        {x | (U : Matrix (Fin W) (Fin W) ℂ).mulVec (normalize (cplxVec W x)) ∈ A} =
      stdGauss (Fin W × Fin 2) {x | normalize (cplxVec W x) ∈ A} := by
  have hQ := measurePreserving_stdGauss_linearIsometry (sphere_iso U)
  have hset : {x | (U : Matrix (Fin W) (Fin W) ℂ).mulVec (normalize (cplxVec W x)) ∈ A} =
      (fun x => (sphere_iso U (WithLp.toLp 2 x)).ofLp) ⁻¹' {x | normalize (cplxVec W x) ∈ A} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, sphere_iso_apply, sphere_normalize_mulVec]
  rw [hset, hQ.measure_preimage]
  exact (hA.preimage (sphere_measurable_normalize_cplxVec W)).nullMeasurableSet

/-- Every unit vector is a column of a unitary matrix. -/
private lemma sphere_exists_unitary {W : ℕ} (i₀ : Fin W) (w : Fin W → ℂ)
    (hw : ∑ i, ‖w i‖ ^ 2 = 1) :
    ∃ M : Matrix.unitaryGroup (Fin W) ℂ,
      (M : Matrix (Fin W) (Fin W) ℂ).mulVec (Pi.single i₀ 1) = w := by
  have hn : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin W))‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [hw]
  have hon : Orthonormal ℂ (({i₀} : Set (Fin W)).domRestrict
      (fun _ : Fin W => (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin W)))) := by
    refine ⟨fun i => by simpa [Set.domRestrict] using hn, fun i j hij => ?_⟩
    exact absurd (Subsingleton.elim i j) hij
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨⟨(EuclideanSpace.basisFun (Fin W) ℂ).toBasis.toMatrix b,
    (EuclideanSpace.basisFun (Fin W) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩, ?_⟩
  ext i
  rw [Matrix.mulVec_single_one]
  simp [Module.Basis.toMatrix_apply, hb i₀ rfl]

/-- `haarU{U | U w ∈ A}` is the same for every unit vector `w`. -/
private lemma sphere_haar_unit {W : ℕ} (i₀ : Fin W) (w : Fin W → ℂ)
    (hw : ∑ i, ‖w i‖ ^ 2 = 1) (A : Set (Fin W → ℂ)) :
    haarU W {U | (U : Matrix (Fin W) (Fin W) ℂ).mulVec w ∈ A} =
      haarU W {U | (U : Matrix (Fin W) (Fin W) ℂ).mulVec (Pi.single i₀ 1) ∈ A} := by
  obtain ⟨M, hM⟩ := sphere_exists_unitary i₀ w hw
  have := isMulRightInvariant_haarU W
  rw [← measure_preimage_mul_right (haarU W) M
    {U | (U : Matrix (Fin W) (Fin W) ℂ).mulVec (Pi.single i₀ 1) ∈ A}]
  congr 1
  ext U
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [show ((U * M : Matrix.unitaryGroup (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ) =
    (U : Matrix (Fin W) (Fin W) ℂ) * (M : Matrix (Fin W) (Fin W) ℂ) from rfl,
    ← Matrix.mulVec_mulVec, hM]

/-- `cplxVec W x ≠ 0` for almost every `x`. -/
private lemma sphere_ae_ne_zero {W : ℕ} (i₀ : Fin W) :
    ∀ᵐ x ∂(stdGauss (Fin W × Fin 2)), cplxVec W x ≠ 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have h0 : stdGauss (Fin W × Fin 2) {x | x (i₀, 0) = 0} = 0 := by
    have := (measurePreserving_eval (fun _ : Fin W × Fin 2 => gaussianReal 0 1)
      (i₀, 0)).measure_preimage (s := {0}) (measurableSet_singleton 0).nullMeasurableSet
    rw [measure_singleton] at this
    exact this
  refine ae_iff.mpr (measure_mono_null (fun x hx => ?_) h0)
  simp only [Set.mem_ofPred_eq, not_not] at hx
  have := congrArg Complex.re (congrFun hx i₀)
  simpa [cplxVec] using this

private lemma sphere_sum_normalize {W : ℕ} {y : Fin W → ℂ} (hy : y ≠ 0) :
    ∑ i, ‖normalize y i‖ ^ 2 = 1 := by
  simp_rw [sphere_norm_normalize_sq]
  rw [← Finset.sum_div, div_self]
  intro h
  apply hy
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).mp h i (mem_univ i)
  simpa using this

/-- A Haar column is a normalized complex Gaussian vector. -/
theorem map_haarU_mulVec (W : ℕ) (v : Fin W → ℂ) (hv : ∑ i, ‖v i‖ ^ 2 = 1) :
    (haarU W).map
        (fun U : Matrix.unitaryGroup (Fin W) ℂ => (U : Matrix (Fin W) (Fin W) ℂ).mulVec v) =
      (stdGauss (Fin W × Fin 2)).map (fun x => normalize (cplxVec W x)) := by
  have hW : Nonempty (Fin W) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hv
  obtain ⟨i₀⟩ := hW
  have hg := sphere_measurable_normalize_cplxVec W
  have hmv : ∀ w : Fin W → ℂ,
      Measurable (fun U : Matrix.unitaryGroup (Fin W) ℂ =>
        (U : Matrix (Fin W) (Fin W) ℂ).mulVec w) :=
    fun w => (Continuous.matrix_mulVec continuous_subtype_val continuous_const).measurable
  have hjoint : Measurable (fun p : Matrix.unitaryGroup (Fin W) ℂ × (Fin W → ℂ) =>
      (p.1 : Matrix (Fin W) (Fin W) ℂ).mulVec p.2) :=
    (Continuous.matrix_mulVec (continuous_subtype_val.comp continuous_fst)
      continuous_snd).measurable
  set ν := (stdGauss (Fin W × Fin 2)).map (fun x => normalize (cplxVec W x)) with hν
  have hunit : ∀ᵐ w ∂ν, ∑ i, ‖w i‖ ^ 2 = 1 := by
    rw [hν, ae_map_iff hg.aemeasurable
      (measurableSet_eq_fun (by fun_prop) measurable_const)]
    filter_upwards [sphere_ae_ne_zero i₀] with x hx
    exact sphere_sum_normalize hx
  ext A hA
  have hpre : ∀ U : Matrix (Fin W) (Fin W) ℂ, MeasurableSet {w : Fin W → ℂ | U.mulVec w ∈ A} :=
    fun U => hA.preimage (sphere_measurable_mulVec U)
  have hinv : ∀ U : Matrix.unitaryGroup (Fin W) ℂ,
      ν {w | (U : Matrix (Fin W) (Fin W) ℂ).mulVec w ∈ A} = ν A := by
    intro U
    rw [hν, Measure.map_apply hg (hpre _), Measure.map_apply hg hA]
    exact sphere_invariant U hA
  have hin : ∀ w : Fin W → ℂ, ∫⁻ U, A.indicator 1 ((U : Matrix (Fin W) (Fin W) ℂ).mulVec w)
      ∂(haarU W) = haarU W {U | (U : Matrix (Fin W) (Fin W) ℂ).mulVec w ∈ A} := by
    intro w
    exact lintegral_indicator_one (hA.preimage (hmv w))
  have key : ν A = haarU W {U | (U : Matrix (Fin W) (Fin W) ℂ).mulVec v ∈ A} := by
    calc ν A = ∫⁻ U, ν {w | (U : Matrix (Fin W) (Fin W) ℂ).mulVec w ∈ A} ∂(haarU W) := by
          simp_rw [hinv]
          rw [lintegral_const, measure_univ, mul_one]
      _ = ∫⁻ U, ∫⁻ w, A.indicator 1 ((U : Matrix (Fin W) (Fin W) ℂ).mulVec w) ∂ν
            ∂(haarU W) := by
          refine lintegral_congr fun U => ?_
          exact (lintegral_indicator_one (hpre _)).symm
      _ = ∫⁻ w, ∫⁻ U, A.indicator 1 ((U : Matrix (Fin W) (Fin W) ℂ).mulVec w) ∂(haarU W)
            ∂ν :=
          lintegral_lintegral_swap ((measurable_one.indicator hA).comp hjoint).aemeasurable
      _ = ∫⁻ _w, haarU W {U | (U : Matrix (Fin W) (Fin W) ℂ).mulVec v ∈ A} ∂ν := by
          refine lintegral_congr_ae ?_
          filter_upwards [hunit] with w hw
          rw [hin, sphere_haar_unit i₀ w hw, sphere_haar_unit i₀ v hv]
      _ = _ := by
          rw [lintegral_const, hν, measure_univ, mul_one]
  rw [Measure.map_apply (hmv v) hA, key]
  rfl

/-! ### Gaussian computations -/

private lemma sphere_pdf_mul_exp (c x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (c * x ^ 2) =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2 - c) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- `exp (c t²)` is integrable against the standard Gaussian for `c < 1/2`. -/
private lemma sphere_integrable_exp_sq {c : ℝ} (hc : c < 1 / 2) :
    Integrable (fun t : ℝ => Real.exp (c * t ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)]
  have h := (integrable_exp_neg_mul_sq (b := 1 / 2 - c) (by linarith)).const_mul
    ((Real.sqrt (2 * π))⁻¹)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x), smul_eq_mul]
  exact (sphere_pdf_mul_exp c x).symm

/-- `E exp (c t²) = (1 - 2c)^{-1/2}` for the standard Gaussian and `c < 1/2`. -/
private lemma sphere_integral_exp_sq {c : ℝ} (hc : c < 1 / 2) :
    ∫ t : ℝ, Real.exp (c * t ^ 2) ∂(gaussianReal 0 1) = Real.sqrt ((1 - 2 * c)⁻¹) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul, sphere_pdf_mul_exp]
  rw [integral_const_mul, integral_gaussian]
  have h1 : 0 < 1 - 2 * c := by linarith
  have h4 : π / (1 / 2 - c) = (2 * π) * (1 - 2 * c)⁻¹ := by
    field_simp
  have : Real.sqrt (2 * π) ≠ 0 := by positivity
  have h5 : Real.sqrt (2 * π * (1 - 2 * c)⁻¹) =
      Real.sqrt (2 * π) * Real.sqrt ((1 - 2 * c)⁻¹) :=
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π) ((1 - 2 * c)⁻¹)
  rw [h4, h5, ← mul_assoc, inv_mul_cancel₀ this, one_mul]

/-- Gaussian form of the mass tail of Appendix D.1 [subsec:pf_thm31], by exponential Markov with
weights `3/16` on `S` and `-1/16` off `S`. -/
private lemma sphere_gauss_mass_tail {W : ℕ} (S : Finset (Fin W)) :
    stdGauss (Fin W × Fin 2) {x | (1 / 4 : ℝ) ≤ ∑ i ∈ S, ‖normalize (cplxVec W x) i‖ ^ 2} ≤
      ENNReal.ofReal ((8 / 5 : ℝ) ^ S.card * (8 / 9 : ℝ) ^ (W - S.card)) := by
  set κ : Fin W → ℝ := fun i => (if i ∈ S then 1 / 4 else 0) - 1 / 16 with hκ
  have hκlt : ∀ i, κ i < 1 / 2 := by
    intro i
    simp only [hκ]
    split_ifs <;> norm_num
  set F : (Fin W × Fin 2 → ℝ) → ℝ := fun x => ∏ p, Real.exp (κ p.1 * x p ^ 2) with hF
  have hFsum : ∀ x, F x = Real.exp ((1 / 4) * ∑ i ∈ S, ‖cplxVec W x i‖ ^ 2 -
      (1 / 16) * ∑ i, ‖cplxVec W x i‖ ^ 2) := by
    intro x
    simp only [hF]
    rw [← Real.exp_sum]
    congr 1
    rw [Fintype.sum_prod_type]
    have h2 : ∀ i, ∑ k : Fin 2, κ i * x (i, k) ^ 2 = κ i * ‖cplxVec W x i‖ ^ 2 := by
      intro i
      rw [Fin.sum_univ_two, Complex.sq_norm]
      simp [cplxVec, Complex.normSq_mk]
      ring
    simp_rw [h2, hκ, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_mem,
      Finset.univ_inter, ← Finset.mul_sum]
  have hI : Integrable F (stdGauss (Fin W × Fin 2)) :=
    Integrable.fintype_prod (f := fun (p : Fin W × Fin 2) (t : ℝ) => Real.exp (κ p.1 * t ^ 2))
      (μ := fun _ => gaussianReal 0 1) (fun p => sphere_integrable_exp_sq (hκlt p.1))
  have hsub : {x | (1 / 4 : ℝ) ≤ ∑ i ∈ S, ‖normalize (cplxVec W x) i‖ ^ 2} ⊆
      {x | 1 ≤ ENNReal.ofReal (F x)} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    simp_rw [sphere_norm_normalize_sq] at hx
    rw [← Finset.sum_div] at hx
    have hN : 0 < ∑ i, ‖cplxVec W x i‖ ^ 2 := by
      rcases (Finset.sum_nonneg (fun i _ => sq_nonneg ‖cplxVec W x i‖) :
        0 ≤ ∑ i, ‖cplxVec W x i‖ ^ 2).lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at hx
        norm_num at hx
    rw [le_div_iff₀ hN] at hx
    rw [ENNReal.one_le_ofReal, hFsum]
    exact Real.one_le_exp (by linarith)
  have hval : ∫ x, F x ∂(stdGauss (Fin W × Fin 2)) =
      (8 / 5 : ℝ) ^ S.card * (8 / 9 : ℝ) ^ (W - S.card) := by
    change ∫ x : Fin W × Fin 2 → ℝ, (∏ p : Fin W × Fin 2, Real.exp (κ p.1 * x p ^ 2))
      ∂(Measure.pi fun _ => gaussianReal 0 1) = _
    rw [integral_fintype_prod_eq_prod
        (fun (p : Fin W × Fin 2) (t : ℝ) => Real.exp (κ p.1 * t ^ 2)),
      Finset.prod_congr rfl (fun p _ => sphere_integral_exp_sq (hκlt p.1)),
      Fintype.prod_prod_type]
    simp only [Fin.prod_univ_two]
    have hf : ∀ i, Real.sqrt ((1 - 2 * κ i)⁻¹) * Real.sqrt ((1 - 2 * κ i)⁻¹) =
        if i ∈ S then 8 / 5 else 8 / 9 := by
      intro i
      rw [Real.mul_self_sqrt (inv_nonneg.mpr (by linarith [hκlt i]))]
      simp only [hκ]
      split_ifs <;> norm_num
    simp_rw [hf]
    rw [← Finset.prod_mul_prod_compl S]
    rw [Finset.prod_congr rfl (fun i hi => ite_eq_left hi),
      Finset.prod_congr rfl (fun i hi => ite_eq_right (Finset.mem_compl.mp hi)),
      Finset.prod_const, Finset.prod_const, Finset.card_compl, Fintype.card_fin]
  calc stdGauss (Fin W × Fin 2) {x | (1 / 4 : ℝ) ≤ ∑ i ∈ S, ‖normalize (cplxVec W x) i‖ ^ 2}
      ≤ 1 * stdGauss (Fin W × Fin 2) {x | 1 ≤ ENNReal.ofReal (F x)} := by
        rw [one_mul]
        exact measure_mono hsub
    _ ≤ ∫⁻ x, ENNReal.ofReal (F x) ∂(stdGauss (Fin W × Fin 2)) :=
        mul_meas_ge_le_lintegral₀
          (ENNReal.measurable_ofReal.comp_aemeasurable hI.aestronglyMeasurable.aemeasurable) 1
    _ = ENNReal.ofReal (∫ x, F x ∂(stdGauss (Fin W × Fin 2))) :=
        (ofReal_integral_eq_lintegral_ofReal hI
          (Filter.Eventually.of_forall fun x => by simp only [hF, Pi.zero_apply]; positivity)).symm
    _ = _ := by rw [hval]

/-! ### From a Haar column to the normalized Gaussian -/

private lemma sphere_sum_pos {W : ℕ} {y : Fin W → ℂ} (hy : y ≠ 0) : 0 < ∑ i, ‖y i‖ ^ 2 := by
  refine lt_of_le_of_ne (Finset.sum_nonneg fun k _ => by positivity) (fun h => hy ?_)
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).mp h.symm i (mem_univ i)
  simpa using this

/-- For `v ≠ 0`, `|(U v)_j|² = ‖v‖² |(U v̂)_j|²` with `v̂ = normalize v`. -/
private lemma sphere_norm_mulVec_sq {W : ℕ} {v : Fin W → ℂ} (hv : v ≠ 0)
    (U : Matrix.unitaryGroup (Fin W) ℂ) (j : Fin W) :
    ‖(U : Matrix (Fin W) (Fin W) ℂ).mulVec v j‖ ^ 2 =
      (∑ i, ‖v i‖ ^ 2) * ‖(U : Matrix (Fin W) (Fin W) ℂ).mulVec (normalize v) j‖ ^ 2 := by
  have hN := sphere_sum_pos hv
  rw [sphere_normalize_mulVec, sphere_norm_normalize_sq, sphere_sum_norm_mulVec]
  field_simp

/-- An event for the column `U u`, `u` a unit vector, has the probability of the same event for
the normalized Gaussian. -/
private lemma sphere_haar_to_gauss {W : ℕ} {u : Fin W → ℂ} (hu : ∑ i, ‖u i‖ ^ 2 = 1)
    {B : Set (Fin W → ℂ)} (hB : MeasurableSet B) :
    haarU W {U | (U : Matrix (Fin W) (Fin W) ℂ).mulVec u ∈ B} =
      stdGauss (Fin W × Fin 2) {x | normalize (cplxVec W x) ∈ B} := by
  have h := congrArg (fun μ : Measure (Fin W → ℂ) => μ B) (map_haarU_mulVec W u hu)
  rw [Measure.map_apply (Continuous.matrix_mulVec continuous_subtype_val
      continuous_const).measurable hB,
    Measure.map_apply (sphere_measurable_normalize_cplxVec W) hB] at h
  exact h

/-- Exponential-sum tail of Appendix D.1 [subsec:pf_thm31]: mass of a prescribed coordinate
set. -/
theorem haarU_mass_tail (W : ℕ) (v : Fin W → ℂ) (hv : v ≠ 0) (S : Finset (Fin W)) :
    haarU W {U | (∑ i, ‖v i‖ ^ 2) / 4 ≤ ∑ i ∈ S, ‖(U : Matrix (Fin W) (Fin W) ℂ).mulVec v i‖ ^ 2} ≤
      ENNReal.ofReal ((8 / 5 : ℝ) ^ S.card * (8 / 9 : ℝ) ^ (W - S.card)) := by
  have hN := sphere_sum_pos hv
  have hB : MeasurableSet {w : Fin W → ℂ | (1 / 4 : ℝ) ≤ ∑ i ∈ S, ‖w i‖ ^ 2} :=
    measurableSet_le measurable_const (by fun_prop)
  have hset : {U : Matrix.unitaryGroup (Fin W) ℂ |
      (∑ i, ‖v i‖ ^ 2) / 4 ≤ ∑ i ∈ S, ‖(U : Matrix (Fin W) (Fin W) ℂ).mulVec v i‖ ^ 2} =
      {U : Matrix.unitaryGroup (Fin W) ℂ | (U : Matrix (Fin W) (Fin W) ℂ).mulVec (normalize v) ∈
        {w | (1 / 4 : ℝ) ≤ ∑ i ∈ S, ‖w i‖ ^ 2}} := by
    ext U
    simp only [Set.mem_ofPred_eq]
    rw [Finset.sum_congr rfl (fun i _ => sphere_norm_mulVec_sq hv U i), ← Finset.mul_sum]
    constructor <;> intro h <;> nlinarith
  rw [hset, sphere_haar_to_gauss (sphere_sum_normalize hv) hB]
  exact sphere_gauss_mass_tail S

theorem mass_tail_le_exp (W r : ℕ) (hr : 8 * r ≤ W) :
    (8 / 5 : ℝ) ^ r * (8 / 9 : ℝ) ^ (W - r) ≤ Real.exp (-(W : ℝ) / 25) := by
  obtain ⟨m, rfl⟩ : ∃ m, W = 8 * r + m := ⟨W - 8 * r, by omega⟩
  have hq : (24 / 25 : ℝ) ≤ Real.exp (-1 / 25) := by
    linarith [Real.add_one_le_exp (-1 / 25 : ℝ)]
  have hWr : 8 * r + m - r = 7 * r + m := by omega
  rw [hWr]
  calc (8 / 5 : ℝ) ^ r * (8 / 9 : ℝ) ^ (7 * r + m)
      = ((8 / 5 : ℝ) * (8 / 9 : ℝ) ^ 7) ^ r * (8 / 9 : ℝ) ^ m := by
        rw [pow_add, pow_mul, mul_pow]
        ring
    _ ≤ ((24 / 25 : ℝ) ^ 8) ^ r * (24 / 25 : ℝ) ^ m :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num) (by norm_num) r)
          (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (by positivity) (by positivity)
    _ ≤ (Real.exp (-1 / 25) ^ 8) ^ r * Real.exp (-1 / 25) ^ m := by
        gcongr
    _ = Real.exp (-((8 * r + m : ℕ) : ℝ) / 25) := by
        rw [← pow_mul, ← pow_add, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

end LSBA
