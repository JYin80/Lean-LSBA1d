import LSBA.Gauss.CGauss
import LSBA.Gauss.Concentration
import LSBA.Gauss.SphereNet
import LSBA.Spectral.BorderInverse

/-!
# Rectangular complex Gaussian matrices

The matrix `G = (x_{ij})` with independent standard complex Gaussian entries
(`𝔼|x_{ij}|² = 1`, `𝔼 x_{ij}² = 0`) under `stdCGauss (m × κ)`, and two bounds with exponential
failure used for (9.45) [us:eq:lowerK] and (9.46) [us:eq:Gaussnorm] in Appendix G.2.1
[app:gaussian-projection-inputs]: the operator norm of `M G` for a deterministic `M`, at most
`C (‖M‖_HS + ‖M‖ √(k + s))` with failure `e^{-s}`; and the least singular value of `N G` when
`‖N* u‖ ≥ λ ‖u‖` and `N` has `h ≥ C₀ k` rows, at least `c λ √h` with failure `e^{-c h}`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The `m × κ` matrix with entries `x (i, j)`. -/
def cgMat {m κ : Type*} (x : m × κ → ℂ) : Matrix m κ ℂ := Matrix.of fun i j => x (i, j)


/-! ### Real coordinates -/

/-- The complex vector with the real coordinates `y`: `(y_{i,0} + i y_{i,1}) / √2`. -/
private def cgMat_rc {ι : Type*} (y : ι × Fin 2 → ℝ) : ι → ℂ :=
  fun i => ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y (i, 0), y (i, 1)⟩ : ℂ)

private lemma cgMat_rc_sub {ι : Type*} (y z : ι × Fin 2 → ℝ) :
    cgMat_rc (y - z) = cgMat_rc y - cgMat_rc z := by
  funext i
  apply Complex.ext <;> simp [cgMat_rc, mul_sub]

private lemma cgMat_rc_norm_sq {ι : Type*} [Fintype ι] (y : ι × Fin 2 → ℝ) :
    ∑ i, ‖cgMat_rc y i‖ ^ 2 = (∑ p, y p ^ 2) / 2 := by
  rw [Fintype.sum_prod_type, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
  simp only [cgMat_rc, Complex.mul_re, Complex.mul_im]
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 2) ≠ 0 := by positivity
  field_simp
  simp
  nlinarith [h2]

/-- `‖cgMat_rc y‖₂ = ‖y‖₂ / √2`. -/
private lemma cgMat_rc_l2Norm {ι : Type*} [Fintype ι] (y : ι × Fin 2 → ℝ) :
    l2Norm (cgMat_rc y) = ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (ι × Fin 2))‖ / Real.sqrt 2 := by
  rw [l2Norm, cgMat_rc_norm_sq, EuclideanSpace.norm_eq, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2)]
  simp [Real.norm_eq_abs, sq_abs]


/-- The smoothed norm `√(‖A z‖₂² + ε²)` of the linear image of the complex vector with real
coordinates `y`. -/
private def cgMat_sm {κ ι : Type*} [Fintype κ] [Fintype ι] (A : Matrix κ ι ℂ) (ε : ℝ)
    (y : ι × Fin 2 → ℝ) : ℝ :=
  Real.sqrt (l2Norm (A *ᵥ cgMat_rc y) ^ 2 + ε ^ 2)

private lemma cgMat_l2Norm_nonneg {κ : Type*} [Fintype κ] (v : κ → ℂ) : 0 ≤ l2Norm v :=
  Real.sqrt_nonneg _

private lemma cgMat_l2Norm_sq {κ : Type*} [Fintype κ] (v : κ → ℂ) :
    l2Norm v ^ 2 = ∑ a, ‖v a‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun a _ => by positivity)

private lemma cgMat_sq_contDiff {κ ι : Type*} [Fintype κ] [Fintype ι] (A : Matrix κ ι ℂ) :
    ContDiff ℝ 1 (fun y : ι × Fin 2 → ℝ => l2Norm (A *ᵥ cgMat_rc y) ^ 2) := by
  have hc : ∀ p : ι × Fin 2, ContDiff ℝ 1 fun y : ι × Fin 2 → ℝ => y p :=
    fun p => contDiff_apply ℝ (fun _ : ι × Fin 2 => ℝ) p
  have hz : ∀ j : ι, ContDiff ℝ 1 fun y : ι × Fin 2 → ℝ => cgMat_rc y j := by
    intro j
    have : (fun y : ι × Fin 2 → ℝ => cgMat_rc y j) = fun y =>
        ((Real.sqrt 2)⁻¹ : ℂ) * ((y (j, 0) : ℂ) + (y (j, 1) : ℂ) * Complex.I) := by
      funext y
      simp only [cgMat_rc]
      rw [Complex.mk_eq_add_mul_I]
    rw [this]
    exact contDiff_const.mul ((Complex.ofRealCLM.contDiff.comp (hc (j, 0))).add
      ((Complex.ofRealCLM.contDiff.comp (hc (j, 1))).mul contDiff_const))
  have : (fun y : ι × Fin 2 → ℝ => l2Norm (A *ᵥ cgMat_rc y) ^ 2) =
      fun y => ∑ a, ‖∑ j, A a j * cgMat_rc y j‖ ^ 2 := by
    funext y
    rw [cgMat_l2Norm_sq]
    rfl
  rw [this]
  refine ContDiff.sum fun a _ => ?_
  exact (ContDiff.sum fun j _ => contDiff_const.mul (hz j)).norm_sq ℝ

private lemma cgMat_sm_contDiff {κ ι : Type*} [Fintype κ] [Fintype ι] (A : Matrix κ ι ℂ)
    {ε : ℝ} (hε : ε ≠ 0) : ContDiff ℝ 1 (cgMat_sm A ε) :=
  ((cgMat_sq_contDiff A).add contDiff_const).sqrt fun y => by positivity


private lemma cgMat_abs_sqrt_sub_le (a b ε : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt (a ^ 2 + ε ^ 2) - Real.sqrt (b ^ 2 + ε ^ 2)| ≤ |a - b| := by
  set p := Real.sqrt (a ^ 2 + ε ^ 2) with hp
  set q := Real.sqrt (b ^ 2 + ε ^ 2) with hq
  have hp0 : 0 ≤ p := Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hap : a ≤ p := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε])
  have hbq : b ≤ q := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε])
  have hp2 : p ^ 2 = a ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)
  have hq2 : q ^ 2 = b ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)
  have hmul : |p - q| * (p + q) = |a - b| * (a + b) := by
    rw [← abs_of_nonneg (add_nonneg hp0 hq0), ← abs_mul, ← abs_of_nonneg (add_nonneg ha hb),
      ← abs_mul]
    congr 1
    nlinarith
  rcases eq_or_lt_of_le (add_nonneg hp0 hq0) with h0 | h0
  · have hpq : p = q := by linarith
    rw [hpq, sub_self, abs_zero]
    exact abs_nonneg _
  · refine le_of_mul_le_mul_right ?_ h0
    rw [hmul]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

private lemma cgMat_abs_l2Norm_sub_le {κ : Type*} [Fintype κ] (u v : κ → ℂ) :
    |l2Norm u - l2Norm v| ≤ l2Norm (u - v) := by
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, WithLp.toLp_sub]
  exact abs_norm_sub_norm_le _ _

private lemma cgMat_sm_lipschitz {κ ι : Type*} [Fintype κ] [Fintype ι] (A : Matrix κ ι ℂ)
    (ε : ℝ) {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ z : ι → ℂ, l2Norm (A *ᵥ z) ≤ L * l2Norm z) :
    LipschitzWith (L / Real.sqrt 2).toNNReal
      (fun x : EuclideanSpace ℝ (ι × Fin 2) => cgMat_sm A ε x.ofLp) := by
  refine LipschitzWith.of_dist_le_mul fun x z => ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  have h1 := cgMat_abs_sqrt_sub_le (l2Norm (A *ᵥ cgMat_rc x.ofLp))
    (l2Norm (A *ᵥ cgMat_rc z.ofLp)) ε (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h2 := cgMat_abs_l2Norm_sub_le (A *ᵥ cgMat_rc x.ofLp) (A *ᵥ cgMat_rc z.ofLp)
  rw [← Matrix.mulVec_sub, ← cgMat_rc_sub] at h2
  have h3 := hL (cgMat_rc (x.ofLp - z.ofLp))
  rw [cgMat_rc_l2Norm] at h3
  have h4 : ‖(WithLp.toLp 2 (x.ofLp - z.ofLp) : EuclideanSpace ℝ (ι × Fin 2))‖ = ‖x - z‖ := rfl
  rw [h4] at h3
  calc |cgMat_sm A ε x.ofLp - cgMat_sm A ε z.ofLp| ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ = L / Real.sqrt 2 * ‖x - z‖ := by ring


/-! ### Variance of a Lipschitz function -/

private lemma cgMat_toLp_norm_le {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ ≤ Real.sqrt (Fintype.card ι) * ‖v‖ := by
  rw [EuclideanSpace.norm_eq]
  have h : ∑ i, ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι) i‖ ^ 2 ≤ (Fintype.card ι) * ‖v‖ ^ 2 := by
    calc ∑ i, ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι) i‖ ^ 2 ≤ ∑ _i : ι, ‖v‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
      _ = (Fintype.card ι) * ‖v‖ ^ 2 := by simp
  calc Real.sqrt (∑ i, ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι) i‖ ^ 2)
      ≤ Real.sqrt ((Fintype.card ι) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (Fintype.card ι) * ‖v‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- A `C¹` function that is `K`-Lipschitz for the Euclidean norm has `|Df(x) v| ≤ K ‖v‖₂`. -/
private lemma cgMat_fderiv_apply_le {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ)
    (hf1 : ContDiff ℝ 1 f) (K : ℝ≥0)
    (hf : LipschitzWith K (fun x : EuclideanSpace ℝ ι => f x.ofLp)) (x v : ι → ℝ) :
    ‖fderiv ℝ f x v‖ ≤ K * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ := by
  set e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ) with he
  have hg : HasFDerivAt (fun z : EuclideanSpace ℝ ι => f z.ofLp)
      ((fderiv ℝ f x).comp (e : EuclideanSpace ℝ ι →L[ℝ] (ι → ℝ))) (WithLp.toLp 2 x) :=
    ((hf1.differentiable one_ne_zero) x).hasFDerivAt.comp (WithLp.toLp 2 x) e.hasFDerivAt
  have hK := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := WithLp.toLp 2 x)
  rw [hg.fderiv] at hK
  calc ‖fderiv ℝ f x v‖
      = ‖((fderiv ℝ f x).comp (e : EuclideanSpace ℝ ι →L[ℝ] (ι → ℝ))) (WithLp.toLp 2 v)‖ := rfl
    _ ≤ ‖(fderiv ℝ f x).comp (e : EuclideanSpace ℝ ι →L[ℝ] (ι → ℝ))‖ *
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ := by gcongr

private lemma cgMat_clm_apply {ι : Type*} [Fintype ι] (L : (ι → ℝ) →L[ℝ] ℝ) (y : ι → ℝ) :
    L y = ∑ i, y i * L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (y i) : ι → ℝ) = y i • Pi.single i 1 := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [this, map_smul, smul_eq_mul]

/-- The Euclidean gradient of a `K`-Lipschitz `C¹` function has `|∇f(x)|₂² ≤ K²`. -/
private lemma cgMat_grad_sq_le {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ)
    (hf1 : ContDiff ℝ 1 f) (K : ℝ≥0)
    (hf : LipschitzWith K (fun x : EuclideanSpace ℝ ι => f x.ofLp)) (x : ι → ℝ) :
    ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2 ≤ (K : ℝ) ^ 2 := by
  set a : ι → ℝ := fun i => fderiv ℝ f x (Pi.single i 1) with ha
  set S := ∑ i, a i ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have h1 : fderiv ℝ f x a = S := by
    rw [cgMat_clm_apply (fderiv ℝ f x) a, hS]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sq]
  have h2 : ‖(WithLp.toLp 2 a : EuclideanSpace ℝ ι)‖ = Real.sqrt S := by
    rw [EuclideanSpace.norm_eq, hS]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.norm_eq_abs, sq_abs]
  have h3 := cgMat_fderiv_apply_le f hf1 K hf x a
  rw [h1, h2, Real.norm_of_nonneg hS0] at h3
  have hs := Real.sq_sqrt hS0
  have hs0 := Real.sqrt_nonneg S
  have hK : (0 : ℝ) ≤ K := K.coe_nonneg
  change S ≤ (K : ℝ) ^ 2
  rcases eq_or_lt_of_le hs0 with h | h
  · have hS' : S = 0 := by rw [← hs, ← h]; ring
    rw [hS']; positivity
  · have : Real.sqrt S ≤ K := le_of_mul_le_mul_left (by nlinarith) h
    nlinarith

/-- Gaussian Poincaré inequality for a `C¹` function that is `K`-Lipschitz for the Euclidean
norm: `∫ (f - ∫ f)² ≤ (π²/8) K²`. -/
private lemma cgMat_var_le {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (hf1 : ContDiff ℝ 1 f)
    (K : ℝ≥0) (hf : LipschitzWith K (fun x : EuclideanSpace ℝ ι => f x.ofLp)) :
    ∫ x, (f x - ∫ y, f y ∂(stdGauss ι)) ^ 2 ∂(stdGauss ι) ≤ π ^ 2 / 8 * (K : ℝ) ^ 2 := by
  set F : (ι → ℝ) → ℂ := fun x => ((f x : ℝ) : ℂ) with hF
  have hF1 : ContDiff ℝ 1 F := Complex.ofRealCLM.contDiff.comp hf1
  have hd : ∀ x, fderiv ℝ F x = Complex.ofRealCLM.comp (fderiv ℝ f x) := fun x =>
    (Complex.ofRealCLM.hasFDerivAt.comp x
      (((hf1.differentiable one_ne_zero) x).hasFDerivAt)).fderiv
  have hb : ∀ x, ‖fderiv ℝ F x‖ ≤ K * Real.sqrt (Fintype.card ι) := by
    intro x
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real]
    calc ‖fderiv ℝ f x v‖ ≤ K * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ :=
          cgMat_fderiv_apply_le f hf1 K hf x v
      _ ≤ K * (Real.sqrt (Fintype.card ι) * ‖v‖) := by
          gcongr; exact cgMat_toLp_norm_le v
      _ = K * Real.sqrt (Fintype.card ι) * ‖v‖ := by ring
  have hP := poincare_grad F hF1 hb
  have hint : ∫ y, F y ∂(stdGauss ι) = ((∫ y, f y ∂(stdGauss ι) : ℝ) : ℂ) := integral_ofReal
  have hL : (fun x => ‖F x - ∫ y, F y ∂(stdGauss ι)‖ ^ 2) =
      fun x => (f x - ∫ y, f y ∂(stdGauss ι)) ^ 2 := by
    funext x
    rw [hint, hF]
    simp only
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hL] at hP
  refine hP.trans ?_
  gcongr
  calc ∫ x, ∑ i, ‖fderiv ℝ F x (Pi.single i 1)‖ ^ 2 ∂(stdGauss ι)
      ≤ ∫ _x, (K : ℝ) ^ 2 ∂(stdGauss ι) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
          (integrable_const _) (Filter.Eventually.of_forall fun x => ?_)
        simp only [hd, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real,
          Real.norm_eq_abs, sq_abs]
        exact cgMat_grad_sq_le f hf1 K hf x
    _ = (K : ℝ) ^ 2 := by rw [integral_const, probReal_univ, one_smul]


/-! ### Concentration of the norm of a linear image -/

private lemma cgMat_rc_continuous (ι : Type*) :
    Continuous (cgMat_rc : (ι × Fin 2 → ℝ) → ι → ℂ) := by
  refine continuous_pi fun i => ?_
  have : (fun y : ι × Fin 2 → ℝ => cgMat_rc y i) = fun y =>
      ((Real.sqrt 2)⁻¹ : ℂ) * ((y (i, 0) : ℂ) + (y (i, 1) : ℂ) * Complex.I) := by
    funext y
    simp only [cgMat_rc]
    rw [Complex.mk_eq_add_mul_I]
  rw [this]
  fun_prop

private lemma cgMat_l2Norm_continuous (κ : Type*) [Fintype κ] :
    Continuous (fun v : κ → ℂ => l2Norm v) := by
  unfold l2Norm
  fun_prop

/-- `stdCGauss ι` is the law of `cgMat_rc y` for `y` standard Gaussian on `ℝ^{ι × 2}`. -/
private lemma cgMat_stdCGauss_eq_map (ι : Type*) [Fintype ι] :
    stdCGauss ι = (stdGauss (ι × Fin 2)).map cgMat_rc := stdCGauss_eq_map ι

/-- The second moment of `‖A z‖₂` in real coordinates. -/
private lemma cgMat_lintegral_sq {κ ι : Type*} [Fintype κ] [Fintype ι] (A : Matrix κ ι ℂ) :
    ∫⁻ y, ENNReal.ofReal (l2Norm (A *ᵥ cgMat_rc y) ^ 2) ∂(stdGauss (ι × Fin 2)) =
      ENNReal.ofReal (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  have h := lintegral_l2Norm_sq_stdCGauss A (0 : ι → ℂ)
  have h0 : l2Norm (A *ᵥ (0 : ι → ℂ)) = 0 := by simp [l2Norm]
  simp only [add_zero, h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  rw [cgMat_stdCGauss_eq_map, lintegral_map] at h
  · exact h
  · refine ENNReal.measurable_ofReal.comp ?_
    exact ((cgMat_l2Norm_continuous κ).comp (Continuous.matrix_mulVec continuous_const
      continuous_id)).pow 2 |>.measurable
  · exact (cgMat_rc_continuous ι).measurable

private lemma cgMat_integral_sq {κ ι : Type*} [Fintype κ] [Fintype ι] (A : Matrix κ ι ℂ) :
    Integrable (fun y : ι × Fin 2 → ℝ => l2Norm (A *ᵥ cgMat_rc y) ^ 2) (stdGauss (ι × Fin 2)) ∧
      ∫ y, l2Norm (A *ᵥ cgMat_rc y) ^ 2 ∂(stdGauss (ι × Fin 2)) = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have hc : Continuous (fun y : ι × Fin 2 → ℝ => l2Norm (A *ᵥ cgMat_rc y) ^ 2) :=
    (cgMat_sq_contDiff A).continuous
  have hnn : 0 ≤ᵐ[stdGauss (ι × Fin 2)] (fun y : ι × Fin 2 → ℝ => l2Norm (A *ᵥ cgMat_rc y) ^ 2) :=
    Filter.Eventually.of_forall fun y => by positivity
  have h := cgMat_lintegral_sq A
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable hnn).1
    (by rw [h]; exact ENNReal.ofReal_ne_top), ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hc.aestronglyMeasurable, h,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]

/-- Concentration of the smoothed norm `√(‖A x‖₂² + ε²)` of a linear image of a standard complex
Gaussian vector `x`, with `‖A z‖₂ ≤ L ‖z‖₂`: its mean `m` satisfies
`‖A‖_HS² + ε² - π² L² / 16 ≤ m² ≤ ‖A‖_HS² + ε²`, and `|√(‖A x‖₂² + ε²) - m| > u` has probability
at most `2 exp (-4 u² / (π² L²))`. -/
private lemma cgMat_norm_conc {κ ι : Type*} [Fintype κ] [Fintype ι] (A : Matrix κ ι ℂ)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (hAL : ∀ z : ι → ℂ, l2Norm (A *ᵥ z) ≤ L * l2Norm z) :
    ∃ m : ℝ, 0 ≤ m ∧ m ^ 2 ≤ (∑ i, ∑ j, ‖A i j‖ ^ 2) + ε ^ 2 ∧
      (∑ i, ∑ j, ‖A i j‖ ^ 2) + ε ^ 2 - π ^ 2 * L ^ 2 / 16 ≤ m ^ 2 ∧
      ∀ u : ℝ, 0 ≤ u →
        stdCGauss ι {x | u < |Real.sqrt (l2Norm (A *ᵥ x) ^ 2 + ε ^ 2) - m|} ≤
          ENNReal.ofReal (2 * Real.exp (-(4 * u ^ 2) / (π ^ 2 * L ^ 2))) := by
  set μ := stdGauss (ι × Fin 2) with hμ
  set f := cgMat_sm A ε with hf
  have hf1 : ContDiff ℝ 1 f := cgMat_sm_contDiff A hε.ne'
  have hfL := cgMat_sm_lipschitz A ε hL.le hAL
  set K : ℝ≥0 := (L / Real.sqrt 2).toNNReal with hK
  have hKc : (K : ℝ) = L / Real.sqrt 2 := Real.coe_toNNReal _ (by positivity)
  have hK2 : (K : ℝ) ^ 2 = L ^ 2 / 2 := by
    rw [hKc, div_pow, Real.sq_sqrt (by norm_num)]
  obtain ⟨hQi, hQ⟩ := cgMat_integral_sq A
  set HS := ∑ i, ∑ j, ‖A i j‖ ^ 2 with hHS
  have hf2 : ∀ y, f y ^ 2 = l2Norm (A *ᵥ cgMat_rc y) ^ 2 + ε ^ 2 := fun y =>
    Real.sq_sqrt (by positivity)
  have hf0 : ∀ y, 0 ≤ f y := fun y => Real.sqrt_nonneg _
  have hfm : AEStronglyMeasurable f μ := hf1.continuous.aestronglyMeasurable
  have hfi2 : Integrable (fun y => f y ^ 2) μ := by
    simp_rw [hf2]
    exact hQi.add (integrable_const _)
  have hfi : Integrable f μ := by
    refine (hfi2.add (integrable_const (1 : ℝ))).mono' hfm (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (hf0 y)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (f y - 1)]
  have hmem : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfm).2 hfi2
  have hE2 : ∫ y, f y ^ 2 ∂μ = HS + ε ^ 2 := by
    simp_rw [hf2]
    rw [integral_add hQi (integrable_const _), hQ, integral_const, probReal_univ, one_smul]
  have hvar := variance_eq_sub hmem
  have hvar2 := variance_eq_integral hmem.aemeasurable
  have hvle := cgMat_var_le f hf1 K hfL
  have hE : μ[f ^ 2] = HS + ε ^ 2 := by
    rw [← hE2]
    rfl
  refine ⟨∫ y, f y ∂μ, integral_nonneg hf0, ?_, ?_, ?_⟩
  · have := variance_nonneg f μ
    rw [hvar, hE] at this
    linarith
  · have h1 : Var[f; μ] = HS + ε ^ 2 - (∫ y, f y ∂μ) ^ 2 := by rw [hvar, hE]
    rw [hvar2] at h1
    have h2 : π ^ 2 / 8 * (K : ℝ) ^ 2 = π ^ 2 * L ^ 2 / 16 := by rw [hK2]; ring
    linarith
  · intro u hu
    have hc := concentration_real f hf1 K hfL u hu
    have hmeas : MeasurableSet {x : ι → ℂ |
        u < |Real.sqrt (l2Norm (A *ᵥ x) ^ 2 + ε ^ 2) - ∫ y, f y ∂μ|} := by
      refine (isOpen_lt continuous_const ?_).measurableSet
      refine continuous_abs.comp (Continuous.sub ?_ continuous_const)
      exact (((cgMat_l2Norm_continuous κ).comp (Continuous.matrix_mulVec continuous_const
        continuous_id)).pow 2 |>.add continuous_const).sqrt
    rw [cgMat_stdCGauss_eq_map, Measure.map_apply (cgMat_rc_continuous ι).measurable hmeas]
    refine hc.trans (le_of_eq ?_)
    congr 2
    rw [hKc, div_pow, Real.sq_sqrt (by norm_num)]
    field_simp
    ring_nf


/-! ### The linear map `G ↦ M G b` -/

/-- The matrix of the linear map `x ↦ M (cgMat x) b` on the entries of `cgMat x`. -/
private def cgMat_amp {κ ι θ : Type*} (M : Matrix κ ι ℂ) (b : θ → ℂ) :
    Matrix κ (ι × θ) ℂ :=
  Matrix.of fun i p => M i p.1 * b p.2

private lemma cgMat_amp_mulVec {κ ι θ : Type*} [Fintype ι] [Fintype θ] (M : Matrix κ ι ℂ)
    (b : θ → ℂ) (x : ι × θ → ℂ) : cgMat_amp M b *ᵥ x = M *ᵥ (cgMat x *ᵥ b) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, cgMat, cgMat_amp, Matrix.of_apply, Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

private lemma cgMat_amp_hs {κ ι θ : Type*} [Fintype κ] [Fintype ι] [Fintype θ] (M : Matrix κ ι ℂ)
    (b : θ → ℂ) : ∑ i, ∑ p, ‖cgMat_amp M b i p‖ ^ 2 = (∑ i, ∑ j, ‖M i j‖ ^ 2) * l2Norm b ^ 2 := by
  rw [cgMat_l2Norm_sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [cgMat_amp, Matrix.of_apply, norm_mul, mul_pow]

private lemma cgMat_l2Norm_mulVec_le {ι θ : Type*} [Fintype ι] [Fintype θ] (x : ι × θ → ℂ)
    (b : θ → ℂ) : l2Norm (cgMat x *ᵥ b) ≤ l2Norm x * l2Norm b := by
  have hrow : ∀ j : ι, ‖(cgMat x *ᵥ b) j‖ ^ 2 ≤ (∑ l, ‖x (j, l)‖ ^ 2) * l2Norm b ^ 2 := by
    intro j
    rw [cgMat_l2Norm_sq]
    have h1 : ‖(cgMat x *ᵥ b) j‖ ≤ ∑ l, ‖x (j, l)‖ * ‖b l‖ := by
      calc ‖(cgMat x *ᵥ b) j‖ = ‖∑ l, x (j, l) * b l‖ := rfl
        _ ≤ ∑ l, ‖x (j, l) * b l‖ := norm_sum_le _ _
        _ = _ := by simp only [norm_mul]
    calc ‖(cgMat x *ᵥ b) j‖ ^ 2 ≤ (∑ l, ‖x (j, l)‖ * ‖b l‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ l, ‖x (j, l)‖ ^ 2) * ∑ l, ‖b l‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsq : l2Norm (cgMat x *ᵥ b) ^ 2 ≤ (l2Norm x * l2Norm b) ^ 2 := by
    rw [cgMat_l2Norm_sq (cgMat x *ᵥ b), mul_pow, cgMat_l2Norm_sq x, Fintype.sum_prod_type]
    calc ∑ j, ‖(cgMat x *ᵥ b) j‖ ^ 2 ≤ ∑ j, (∑ l, ‖x (j, l)‖ ^ 2) * l2Norm b ^ 2 :=
          Finset.sum_le_sum fun j _ => hrow j
      _ = _ := by rw [← Finset.sum_mul]
  exact (pow_le_pow_iff_left₀ (cgMat_l2Norm_nonneg _)
    (mul_nonneg (cgMat_l2Norm_nonneg _) (cgMat_l2Norm_nonneg _)) two_ne_zero).1 hsq

private lemma cgMat_amp_norm_le {κ ι θ : Type*} [Fintype κ] [Fintype ι] [Fintype θ]
    (M : Matrix κ ι ℂ) (b : θ → ℂ) (x : ι × θ → ℂ) :
    l2Norm (cgMat_amp M b *ᵥ x) ≤ ‖M‖ * l2Norm b * l2Norm x := by
  rw [cgMat_amp_mulVec]
  calc l2Norm (M *ᵥ (cgMat x *ᵥ b)) ≤ ‖M‖ * l2Norm (cgMat x *ᵥ b) := l2Norm_mulVec_le _ _
    _ ≤ ‖M‖ * (l2Norm x * l2Norm b) := mul_le_mul_of_nonneg_left (cgMat_l2Norm_mulVec_le x b)
        (norm_nonneg _)
    _ = ‖M‖ * l2Norm b * l2Norm x := by ring

private lemma cgMat_opNorm_le {κ ι : Type*} [Fintype κ] [Fintype ι] (A : Matrix κ ι ℂ) {β : ℝ}
    (hβ : 0 ≤ β) (h : ∀ y : ι → ℂ, l2Norm (A *ᵥ y) ≤ β * l2Norm y) : ‖A‖ ≤ β := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hβ fun v => ?_
  have := h v.ofLp
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp] at this
  exact this


/-! ### Upper and lower tails of a fixed linear image -/

/-- Upper tail: for `‖A z‖₂ ≤ L ‖z‖₂`, `‖A x‖₂ > ‖A‖_HS + L + u` has probability at most
`2 exp (-4 u² / (π² L²))`. -/
private lemma cgMat_upper_tail {κ ι : Type*} [Fintype κ] [Fintype ι] (A : Matrix κ ι ℂ)
    {L : ℝ} (hL : 0 < L) (hAL : ∀ z : ι → ℂ, l2Norm (A *ᵥ z) ≤ L * l2Norm z) {u : ℝ}
    (hu : 0 ≤ u) :
    stdCGauss ι {x | Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) + L + u < l2Norm (A *ᵥ x)} ≤
      ENNReal.ofReal (2 * Real.exp (-(4 * u ^ 2) / (π ^ 2 * L ^ 2))) := by
  obtain ⟨m, hm0, hmle, -, hconc⟩ := cgMat_norm_conc A hL hL hAL
  set HS := ∑ i, ∑ j, ‖A i j‖ ^ 2 with hHS
  have hHS0 : 0 ≤ HS := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hm : m ≤ Real.sqrt HS + L := by
    refine (pow_le_pow_iff_left₀ hm0 (by positivity) two_ne_zero).1 ?_
    have := Real.sq_sqrt hHS0
    nlinarith [Real.sqrt_nonneg HS]
  refine le_trans (measure_mono fun x hx => ?_) (hconc u hu)
  have hx' : Real.sqrt HS + L + u < l2Norm (A *ᵥ x) := hx
  have hf : l2Norm (A *ᵥ x) ≤ Real.sqrt (l2Norm (A *ᵥ x) ^ 2 + L ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg L])
  change u < |Real.sqrt (l2Norm (A *ᵥ x) ^ 2 + L ^ 2) - m|
  exact lt_of_lt_of_le (by linarith) (le_abs_self _)

/-- Lower tail: for `‖A z‖₂ ≤ ‖z‖₂` and `‖A‖_HS² = H ≥ 16`, `‖A x‖₂ < √H / 2` has probability at
most `2 exp (-H / 40)`. -/
private lemma cgMat_lower_tail {κ ι : Type*} [Fintype κ] [Fintype ι] (A : Matrix κ ι ℂ)
    (hAL : ∀ z : ι → ℂ, l2Norm (A *ᵥ z) ≤ 1 * l2Norm z) {H : ℝ}
    (hH : ∑ i, ∑ j, ‖A i j‖ ^ 2 = H) (h16 : 16 ≤ H) :
    stdCGauss ι {x | l2Norm (A *ᵥ x) < Real.sqrt H / 2} ≤
      ENNReal.ofReal (2 * Real.exp (-(H / 40))) := by
  obtain ⟨m, hm0, -, hmge, hconc⟩ := cgMat_norm_conc A one_pos one_pos hAL
  rw [hH] at hmge
  have hpi : π ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_le_four]
  have hsH : Real.sqrt H ^ 2 = H := Real.sq_sqrt (by linarith)
  have hs4 : 4 ≤ Real.sqrt H := Real.le_sqrt_of_sq_le (by linarith)
  have hmH : Real.sqrt H ≤ m := by
    refine (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) hm0 two_ne_zero).1 ?_
    rw [hsH]
    nlinarith
  have hu : (0 : ℝ) ≤ Real.sqrt H / 4 := by positivity
  refine le_trans (measure_mono fun x hx => ?_) ((hconc _ hu).trans ?_)
  · have hx' : l2Norm (A *ᵥ x) < Real.sqrt H / 2 := hx
    have h0 := cgMat_l2Norm_nonneg (A *ᵥ x)
    have hf : Real.sqrt (l2Norm (A *ᵥ x) ^ 2 + 1 ^ 2) ≤ l2Norm (A *ᵥ x) + 1 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    change Real.sqrt H / 4 < |Real.sqrt (l2Norm (A *ᵥ x) ^ 2 + 1 ^ 2) - m|
    rw [abs_sub_comm]
    have h5 : Real.sqrt H / 4 < m - Real.sqrt (l2Norm (A *ᵥ x) ^ 2 + 1 ^ 2) := by
      set a := l2Norm (A *ᵥ x)
      set b := Real.sqrt (a ^ 2 + 1 ^ 2)
      set r := Real.sqrt H
      have e1 : r / 2 ≤ r - a := by linarith
      linarith
    exact lt_of_lt_of_le h5 (le_abs_self _)
  · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num))
    have hp : π ^ 2 < 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
    have : (Real.sqrt H / 4) ^ 2 = H / 16 := by rw [div_pow, hsH]; norm_num
    rw [this, one_pow, mul_one]
    rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith


/-! ### Reduction of `N G` to a co-isometry -/

private lemma cgMat_star_dotProduct {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    star z ⬝ᵥ z = ((l2Norm z ^ 2 : ℝ) : ℂ) := by
  rw [cgMat_l2Norm_sq]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
  push_cast
  rfl

private lemma cgMat_star_mulVec_self {κ ι : Type*} [Fintype κ] [Fintype ι] (D : Matrix κ ι ℂ)
    (y : ι → ℂ) : star (D *ᵥ y) ⬝ᵥ (D *ᵥ y) = star y ⬝ᵥ ((Dᴴ * D) *ᵥ y) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

/-- Two matrices with the same Gram matrix `Bᴴ B = Cᴴ C` give vectors of the same length. -/
private lemma cgMat_l2Norm_eq_of_gram {κ₁ κ₂ ι : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype ι]
    (B : Matrix κ₁ ι ℂ) (C : Matrix κ₂ ι ℂ) (hBC : Bᴴ * B = Cᴴ * C) (y : ι → ℂ) :
    l2Norm (B *ᵥ y) = l2Norm (C *ᵥ y) := by
  have h := cgMat_star_mulVec_self B y
  rw [hBC, ← cgMat_star_mulVec_self C y, cgMat_star_dotProduct, cgMat_star_dotProduct] at h
  have h2 : l2Norm (B *ᵥ y) ^ 2 = l2Norm (C *ᵥ y) ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (cgMat_l2Norm_nonneg _) (cgMat_l2Norm_nonneg _)).1 h2

private lemma cgMat_eq_zero_of_l2Norm {ι : Type*} [Fintype ι] {v : ι → ℂ} (hv : l2Norm v = 0) :
    v = 0 := by
  have h := cgMat_l2Norm_sq v
  rw [hv] at h
  funext i
  have h1 : ‖v i‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg ‖v a‖)).1 (by simpa using h.symm) i
      (Finset.mem_univ i)
  simpa using h1

open scoped MatrixOrder ComplexOrder in
/-- If `‖Nᴴ u‖₂ ≥ λ ‖u‖₂` with `λ > 0`, then `N = S P` with `P Pᴴ = 1` and `S` Hermitian with
`‖S w‖₂ ≥ λ ‖w‖₂`; in particular `‖N v‖₂ ≥ λ ‖P v‖₂`. -/
private lemma cgMat_exists_coisometry {h n : ℕ} (N : Matrix (Fin h) (Fin n) ℂ) {lam : ℝ}
    (hlam : 0 < lam) (hN : ∀ u, lam * l2Norm u ≤ l2Norm (Nᴴ *ᵥ u)) :
    ∃ P : Matrix (Fin h) (Fin n) ℂ, P * Pᴴ = 1 ∧ ∀ v, lam * l2Norm (P *ᵥ v) ≤ l2Norm (N *ᵥ v) := by
  have hG : (N * Nᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose N
  set S : Matrix (Fin h) (Fin h) ℂ := CFC.sqrt (N * Nᴴ) with hS
  have hSS : S * S = N * Nᴴ := CFC.sqrt_mul_sqrt_self _ hG.nonneg
  have hSH : Sᴴ = S :=
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg (N * Nᴴ))).isHermitian.eq
  have hgram : Sᴴ * S = (Nᴴ)ᴴ * Nᴴ := by rw [hSH, hSS, Matrix.conjTranspose_conjTranspose]
  have hSn : ∀ w, lam * l2Norm w ≤ l2Norm (S *ᵥ w) := fun w => by
    rw [cgMat_l2Norm_eq_of_gram S Nᴴ hgram w]
    exact hN w
  have hU : IsUnit S := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro w w' hww
    have h0 : S *ᵥ (w - w') = 0 := by rw [Matrix.mulVec_sub, hww, sub_self]
    have h1 := hSn (w - w')
    rw [h0] at h1
    have h2 : l2Norm (w - w') = 0 := by
      have : l2Norm (0 : Fin h → ℂ) = 0 := by simp [l2Norm]
      rw [this] at h1
      have := cgMat_l2Norm_nonneg (w - w')
      nlinarith
    exact sub_eq_zero.1 (cgMat_eq_zero_of_l2Norm h2)
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hU
  refine ⟨S⁻¹ * N, ?_, fun v => ?_⟩
  · have e1 : (S⁻¹ * N) * (S⁻¹ * N)ᴴ = S⁻¹ * (N * Nᴴ) * S⁻¹ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hSH]
      simp only [Matrix.mul_assoc]
    rw [e1, ← hSS]
    calc S⁻¹ * (S * S) * S⁻¹ = (S⁻¹ * S) * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  · have : N *ᵥ v = S *ᵥ ((S⁻¹ * N) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
        Matrix.one_mul]
    rw [this]
    exact hSn _


/-! ### From the unit sphere to all vectors -/

private lemma cgMat_l2Norm_smul {ι : Type*} [Fintype ι] (c : ℂ) (v : ι → ℂ) :
    l2Norm (c • v) = ‖c‖ * l2Norm v := by
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, WithLp.toLp_smul, norm_smul]

private lemma cgMat_unit_of_ne {ι : Type*} [Fintype ι] {y : ι → ℂ} (hy : l2Norm y ≠ 0) :
    ∑ i, ‖((((l2Norm y)⁻¹ : ℝ) : ℂ) • y) i‖ ^ 2 = 1 := by
  have h := cgMat_l2Norm_smul (((l2Norm y)⁻¹ : ℝ) : ℂ) y
  rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_nonneg (cgMat_l2Norm_nonneg y),
    inv_mul_cancel₀ hy] at h
  have h2 := cgMat_l2Norm_sq ((((l2Norm y)⁻¹ : ℝ) : ℂ) • y)
  rw [h] at h2
  rw [← h2]
  norm_num

private lemma cgMat_unit_sum {ι : Type*} [Fintype ι] {y : ι → ℂ} (hy : ∑ i, ‖y i‖ ^ 2 = 1) :
    l2Norm y = 1 := by
  rw [l2Norm, hy, Real.sqrt_one]

/-- An upper bound on the unit sphere is an operator-norm bound. -/
private lemma cgMat_opNorm_le_of_unit {κ ι : Type*} [Fintype κ] [Fintype ι] (A : Matrix κ ι ℂ)
    {β : ℝ} (hβ : 0 ≤ β) (h : ∀ y : ι → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 → l2Norm (A *ᵥ y) ≤ β) :
    ‖A‖ ≤ β := by
  refine cgMat_opNorm_le A hβ fun y => ?_
  by_cases hy : l2Norm y = 0
  · rw [cgMat_eq_zero_of_l2Norm hy]
    simp [l2Norm]
  · have hpos : 0 < l2Norm y := lt_of_le_of_ne (cgMat_l2Norm_nonneg y) (Ne.symm hy)
    have h1 := h _ (cgMat_unit_of_ne hy)
    rw [Matrix.mulVec_smul, cgMat_l2Norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (cgMat_l2Norm_nonneg y)] at h1
    rw [inv_mul_le_iff₀ hpos] at h1
    linarith

/-- A lower bound on the unit sphere is a lower bound on all vectors. -/
private lemma cgMat_lower_of_unit {κ ι : Type*} [Fintype κ] [Fintype ι] (A : Matrix κ ι ℂ)
    {α : ℝ} (h : ∀ y : ι → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 → α ≤ l2Norm (A *ᵥ y)) (b : ι → ℂ) :
    α * l2Norm b ≤ l2Norm (A *ᵥ b) := by
  by_cases hb : l2Norm b = 0
  · rw [hb, mul_zero]
    exact cgMat_l2Norm_nonneg _
  · have hpos : 0 < l2Norm b := lt_of_le_of_ne (cgMat_l2Norm_nonneg b) (Ne.symm hb)
    have h1 := h _ (cgMat_unit_of_ne hb)
    rw [Matrix.mulVec_smul, cgMat_l2Norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (cgMat_l2Norm_nonneg b)] at h1
    rw [le_inv_mul_iff₀ hpos] at h1
    linarith

private lemma cgMat_coisometry_hs {h n : ℕ} (P : Matrix (Fin h) (Fin n) ℂ) (hP : P * Pᴴ = 1) :
    ∑ i, ∑ j, ‖P i j‖ ^ 2 = h := by
  have hi : ∀ i, ∑ j, ‖P i j‖ ^ 2 = 1 := by
    intro i
    have h1 := congrFun (congrFun hP i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      RCLike.star_def, Complex.mul_conj'] at h1
    exact_mod_cast h1
  simp [hi]

private lemma cgMat_coisometry_norm {h n : ℕ} (P : Matrix (Fin h) (Fin n) ℂ) (hP : P * Pᴴ = 1) :
    ‖P‖ ≤ 1 := by
  have h1 : ‖(1 : Matrix (Fin h) (Fin h) ℂ)‖ ≤ 1 :=
    cgMat_opNorm_le _ zero_le_one fun y => by simp
  have h2 := Matrix.l2_opNorm_conjTranspose_mul_self Pᴴ
  rw [Matrix.conjTranspose_conjTranspose, hP] at h2
  have h3 : ‖Pᴴ‖ ≤ 1 := by nlinarith [norm_nonneg Pᴴ]
  rwa [Matrix.l2_opNorm_conjTranspose] at h3

/-- The operator norm of `M G` (proof of (9.46) [us:eq:Gaussnorm]): for a deterministic
`m × n` matrix `M` and `G` an `n × k` standard complex Gaussian matrix,
`‖M G‖ ≤ C (‖M‖_HS + ‖M‖ √(k + s))` with failure `e^{-s}`. -/
theorem cgMat_mul_norm_le : ∃ C : ℝ, 0 < C ∧
    ∀ (m n k : ℕ) (M : Matrix (Fin m) (Fin n) ℂ) (s : ℝ), 0 ≤ s →
      stdCGauss (Fin n × Fin k)
          {x | C * (Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) + ‖M‖ * Real.sqrt (k + s)) <
            ‖M * cgMat x‖} ≤
        ENNReal.ofReal (Real.exp (-s)) := by
  refine ⟨10, by norm_num, fun m n k M s hs => ?_⟩
  set H := Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) with hH
  have hH0 : 0 ≤ H := Real.sqrt_nonneg _
  have hRHS0 : 0 ≤ 10 * (H + ‖M‖ * Real.sqrt (k + s)) :=
    mul_nonneg (by norm_num) (add_nonneg hH0 (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))
  by_cases hdeg : k = 0 ∨ ‖M‖ = 0
  · have hz : ∀ x : Fin n × Fin k → ℂ, ‖M * cgMat x‖ ≤ 0 := by
      intro x
      rcases hdeg with hk | hM
      · subst hk
        refine cgMat_opNorm_le _ le_rfl fun y => ?_
        have : (M * cgMat x) *ᵥ y = 0 := by
          funext i
          simp [Matrix.mulVec, dotProduct]
        rw [this]
        simp [l2Norm]
      · have : M = 0 := norm_eq_zero.1 hM
        subst this
        simp
    have : {x : Fin n × Fin k → ℂ | 10 * (H + ‖M‖ * Real.sqrt (k + s)) < ‖M * cgMat x‖} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact (hz x).trans hRHS0
    rw [this, measure_empty]
    exact zero_le
  push Not at hdeg
  obtain ⟨hk, hL⟩ := hdeg
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
  have hLpos : 0 < ‖M‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hL)
  set L := ‖M‖ with hLdef
  set t : ℝ := s + 4 * k + 1 with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  set u : ℝ := π / 2 * L * Real.sqrt t with hu
  have hu0 : 0 ≤ u := by positivity
  obtain ⟨N, hNc, hNu, hNcover⟩ := exists_sphere_net (Fin k) (δ := 1 / 2) (by norm_num)
  -- the tail of one fixed direction
  have hvec : ∀ v ∈ N, stdCGauss (Fin n × Fin k)
      {x | H + L + u < l2Norm (M *ᵥ (cgMat x *ᵥ v))} ≤ ENNReal.ofReal (2 * Real.exp (-t)) := by
    intro v hv
    have hv1 : l2Norm v = 1 := cgMat_unit_sum (hNu v hv)
    have hAL : ∀ z, l2Norm (cgMat_amp M v *ᵥ z) ≤ L * l2Norm z := fun z => by
      have := cgMat_amp_norm_le M v z
      rwa [hv1, mul_one] at this
    have h := cgMat_upper_tail (cgMat_amp M v) hLpos hAL hu0
    have hhs : Real.sqrt (∑ i, ∑ p, ‖cgMat_amp M v i p‖ ^ 2) = H := by
      rw [cgMat_amp_hs, hv1, one_pow, mul_one]
    rw [hhs] at h
    simp only [cgMat_amp_mulVec] at h
    refine h.trans (le_of_eq ?_)
    congr 2
    have hu2 : u ^ 2 = (π / 2 * L) ^ 2 * t := by
      rw [hu, mul_pow, Real.sq_sqrt ht0]
    rw [hu2]
    have : π ^ 2 * L ^ 2 ≠ 0 := by positivity
    field_simp
    congr 1
    ring
  -- the union bound
  have hreal : (N.card : ℝ) * (2 * Real.exp (-t)) ≤ Real.exp (-s) := by
    have h25 : (25 : ℝ) ≤ Real.exp 4 := by
      have h1 : (2.7 : ℝ) < Real.exp 1 := lt_of_lt_of_le (by norm_num) Real.exp_one_gt_d9.le
      have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [h2]
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) h1.le 4
      norm_num at this
      linarith
    have h1 : (N.card : ℝ) ≤ Real.exp (4 * k) := by
      refine hNc.trans ?_
      have : (1 + 2 / (1 / 2 : ℝ)) ^ (2 * Fintype.card (Fin k)) = 25 ^ k := by
        rw [Fintype.card_fin, pow_mul]
        norm_num
      rw [this, mul_comm, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) h25 k
    have h2 : 2 * Real.exp (-1) ≤ 1 := by
      have h3 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-1), Real.add_one_le_exp (1 : ℝ)]
    calc (N.card : ℝ) * (2 * Real.exp (-t)) ≤ Real.exp (4 * k) * (2 * Real.exp (-t)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (2 * Real.exp (-1)) * Real.exp (-s) := by
          have h4 : Real.exp (4 * k) * Real.exp (-t) = Real.exp (-1) * Real.exp (-s) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            rw [ht]
            ring
          calc Real.exp (4 * k) * (2 * Real.exp (-t)) = 2 * (Real.exp (4 * k) * Real.exp (-t)) := by
                ring
            _ = _ := by rw [h4]; ring
      _ ≤ 1 * Real.exp (-s) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (-s) := one_mul _
  have hsub : {x | 10 * (H + L * Real.sqrt (k + s)) < ‖M * cgMat x‖} ⊆
      ⋃ v ∈ N, {x | H + L + u < l2Norm (M *ᵥ (cgMat x *ᵥ v))} := by
    intro x hx
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists] at hnot
    have hle : ∀ v ∈ N, l2Norm (M *ᵥ (cgMat x *ᵥ v)) ≤ H + L + u := fun v hv =>
      not_lt.1 (hnot v hv)
    have hβ0 : 0 ≤ H + L + u := by positivity
    have hop : ‖M * cgMat x‖ ≤ 2 * (H + L + u) := by
      refine cgMat_opNorm_le_of_unit _ (by positivity) fun y hy => ?_
      have := sphere_net_upper (M * cgMat x) (δ := 1 / 2) (β := H + L + u) (by norm_num)
        (by norm_num) hNcover (fun v hv => by
          rw [← Matrix.mulVec_mulVec]
          exact hle v hv) y hy
      have e : (H + L + u) / (1 - 1 / 2) = 2 * (H + L + u) := by ring
      rw [e] at this
      exact this
    have hs1 : 1 ≤ Real.sqrt (k + s) := Real.one_le_sqrt.2 (by linarith)
    have hts : t ≤ 5 * (k + s) := by rw [ht]; linarith
    have hu4 : u ≤ 4 * L * Real.sqrt (k + s) := by
      have hpi : π ^ 2 < 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
      have h1 : π / 2 * Real.sqrt t ≤ 4 * Real.sqrt (k + s) := by
        refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
        rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt ht0, Real.sq_sqrt (by linarith)]
        nlinarith
      calc u = L * (π / 2 * Real.sqrt t) := by rw [hu]; ring
        _ ≤ L * (4 * Real.sqrt (k + s)) := mul_le_mul_of_nonneg_left h1 hLpos.le
        _ = 4 * L * Real.sqrt (k + s) := by ring
    have hLs : L ≤ L * Real.sqrt (k + s) := by nlinarith
    have := hx
    simp only [Set.mem_ofPred_eq] at this
    nlinarith
  calc stdCGauss (Fin n × Fin k) {x | 10 * (H + L * Real.sqrt (k + s)) < ‖M * cgMat x‖}
      ≤ stdCGauss (Fin n × Fin k)
        (⋃ v ∈ N, {x | H + L + u < l2Norm (M *ᵥ (cgMat x *ᵥ v))}) := measure_mono hsub
    _ ≤ ∑ v ∈ N, stdCGauss (Fin n × Fin k)
        {x | H + L + u < l2Norm (M *ᵥ (cgMat x *ᵥ v))} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ N, ENNReal.ofReal (2 * Real.exp (-t)) := Finset.sum_le_sum hvec
    _ = ENNReal.ofReal ((N.card : ℝ) * (2 * Real.exp (-t))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (Real.exp (-s)) := ENNReal.ofReal_le_ofReal hreal

/-- The least singular value of `N G` (proof of (9.45) [us:eq:lowerK]): if `N` has `h` rows,
`‖N* u‖ ≥ λ ‖u‖` for every `u` and `h ≥ C₀ k`, then `‖N G b‖ ≥ c λ √h ‖b‖` for every
`b ∈ ℂ^k`, with failure `e^{-c h}`. -/
theorem cgMat_sminor : ∃ C₀ c : ℝ, 0 < C₀ ∧ 0 < c ∧
    ∀ (h n k : ℕ) (N : Matrix (Fin h) (Fin n) ℂ) (lam : ℝ), 0 ≤ lam →
      (∀ u, lam * l2Norm u ≤ l2Norm (Nᴴ *ᵥ u)) → C₀ * k ≤ h →
      stdCGauss (Fin n × Fin k)
          {x | ∃ b, l2Norm (N *ᵥ (cgMat x *ᵥ b)) < c * lam * Real.sqrt h * l2Norm b} ≤
        ENNReal.ofReal (Real.exp (-(c * h))) := by
  obtain ⟨C, hC, hup⟩ := cgMat_mul_norm_le
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 3 * C + 1 := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := by linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (8 * B + 3) ^ 2 := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  refine ⟨80 * R + 400, 1 / 160, by positivity, by norm_num, fun h n k N lam hlam hN hhk => ?_⟩
  by_cases hdeg : lam = 0 ∨ k = 0
  · have : {x : Fin n × Fin k → ℂ | ∃ b, l2Norm (N *ᵥ (cgMat x *ᵥ b)) <
        1 / 160 * lam * Real.sqrt h * l2Norm b} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
      intro b
      have h0 := cgMat_l2Norm_nonneg (N *ᵥ (cgMat x *ᵥ b))
      rcases hdeg with hl | hk
      · rw [hl]
        simpa using h0
      · subst hk
        have : l2Norm b = 0 := by simp [l2Norm]
        rw [this]
        simpa using h0
    rw [this, measure_empty]
    exact zero_le
  push Not at hdeg
  obtain ⟨hlam0, hk⟩ := hdeg
  have hlam' : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hlam0)
  obtain ⟨P, hPP, hPN⟩ := cgMat_exists_coisometry N hlam' hN
  have hPhs := cgMat_coisometry_hs P hPP
  have hPn := cgMat_coisometry_norm P hPP
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
  have hh400 : (400 : ℝ) ≤ h := by nlinarith
  have hkh : R * k ≤ h / 80 := by nlinarith
  have hkh' : (k : ℝ) ≤ h := by nlinarith
  have hsh0 : 0 < Real.sqrt h := Real.sqrt_pos.2 (by linarith)
  obtain ⟨sh, hsh⟩ : ∃ sh : ℝ, sh = Real.sqrt h := ⟨_, rfl⟩
  have hsh2 : sh ^ 2 = h := by rw [hsh]; exact Real.sq_sqrt (by linarith)
  have hsh0' : 0 < sh := by rw [hsh]; exact hsh0
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (4 * B + 1) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ < 1 := by
    rw [hδ, div_lt_one (by linarith)]
    linarith
  obtain ⟨Nt, hNc, hNu, hNcover⟩ := exists_sphere_net (Fin k) hδ0
  -- the operator norm of `P G`
  have hnorm : stdCGauss (Fin n × Fin k) {x | B * sh < ‖P * cgMat x‖} ≤
      ENNReal.ofReal (Real.exp (-h)) := by
    refine le_trans (measure_mono fun x hx => ?_) (hup h n k P h (Nat.cast_nonneg h))
    have hx' : B * sh < ‖P * cgMat x‖ := hx
    have h1 : Real.sqrt (k + h) ≤ 2 * sh := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      nlinarith
    change C * (Real.sqrt (∑ i, ∑ j, ‖P i j‖ ^ 2) + ‖P‖ * Real.sqrt (k + h)) < ‖P * cgMat x‖
    rw [hPhs, ← hsh]
    refine lt_of_le_of_lt ?_ hx'
    have h2 : ‖P‖ * Real.sqrt (k + h) ≤ 2 * sh :=
      (mul_le_mul hPn h1 (Real.sqrt_nonneg _) zero_le_one).trans (by linarith)
    nlinarith
  -- one fixed direction
  have hvec : ∀ v ∈ Nt, stdCGauss (Fin n × Fin k)
      {x | l2Norm (P *ᵥ (cgMat x *ᵥ v)) < sh / 2} ≤ ENNReal.ofReal (2 * Real.exp (-(h / 40))) := by
    intro v hv
    have hv1 : l2Norm v = 1 := cgMat_unit_sum (hNu v hv)
    have hAL : ∀ z, l2Norm (cgMat_amp P v *ᵥ z) ≤ 1 * l2Norm z := fun z => by
      have := cgMat_amp_norm_le P v z
      rw [hv1, mul_one] at this
      exact this.trans (mul_le_mul_of_nonneg_right hPn (cgMat_l2Norm_nonneg _))
    have hH : ∑ i, ∑ p, ‖cgMat_amp P v i p‖ ^ 2 = h := by
      rw [cgMat_amp_hs, hv1, hPhs, one_pow, mul_one]
    have := cgMat_lower_tail (cgMat_amp P v) hAL hH (by linarith)
    rw [← hsh] at this
    simpa only [cgMat_amp_mulVec] using this
  -- the bad event
  have hsub : {x : Fin n × Fin k → ℂ | ∃ b, l2Norm (N *ᵥ (cgMat x *ᵥ b)) <
        1 / 160 * lam * Real.sqrt h * l2Norm b} ⊆
      {x | B * sh < ‖P * cgMat x‖} ∪ ⋃ v ∈ Nt, {x | l2Norm (P *ᵥ (cgMat x *ᵥ v)) < sh / 2} := by
    intro x hx
    obtain ⟨b, hb⟩ := hx
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hnot
    obtain ⟨h1, h2⟩ := hnot
    have h1' : ‖P * cgMat x‖ ≤ B * sh := not_lt.1 h1
    have h2' : ∀ v ∈ Nt, sh / 2 ≤ l2Norm (P *ᵥ (cgMat x *ᵥ v)) := fun v hv => not_lt.1 (h2 v hv)
    have hunit : ∀ y : Fin k → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 →
        sh / 4 ≤ l2Norm ((P * cgMat x) *ᵥ y) := by
      intro y hy
      have := sphere_net_lower (P * cgMat x) (δ := δ) (α := sh / 2) (β := B * sh) hδ0.le hδ1
        hNcover (fun v hv => by
          rw [← Matrix.mulVec_mulVec]
          exact h2' v hv) (fun v hv => by
          have := l2Norm_mulVec_le (P * cgMat x) v
          rw [cgMat_unit_sum (hNu v hv), mul_one] at this
          exact this.trans h1') y hy
      have e : sh / 2 - δ * (B * sh) / (1 - δ) = sh / 4 := by
        rw [hδ]
        have : (4 * B + 1) ≠ 0 := by linarith
        field_simp
        ring
      rw [e] at this
      exact this
    have hbd := cgMat_lower_of_unit (P * cgMat x) hunit b
    rw [← Matrix.mulVec_mulVec] at hbd
    have h3 := hPN (cgMat x *ᵥ b)
    rw [← hsh] at hb
    have hl0 := cgMat_l2Norm_nonneg b
    have hl1 := cgMat_l2Norm_nonneg (P *ᵥ (cgMat x *ᵥ b))
    nlinarith [mul_nonneg hlam hl0, mul_nonneg (mul_nonneg hlam hsh0'.le) hl0]
  -- the failure probability
  have hreal : Real.exp (-h) + (Nt.card : ℝ) * (2 * Real.exp (-(h / 40))) ≤
      Real.exp (-(1 / 160 * h)) := by
    have hc1 : (Nt.card : ℝ) ≤ Real.exp (h / 80) := by
      refine hNc.trans ?_
      have e1 : (1 + 2 / δ) ^ (2 * Fintype.card (Fin k)) = R ^ k := by
        rw [Fintype.card_fin, pow_mul, hR, hδ]
        congr 1
        field_simp
        ring
      rw [e1]
      calc R ^ k ≤ Real.exp R ^ k :=
            pow_le_pow_left₀ hR0 (by linarith [Real.add_one_le_exp R]) k
        _ = Real.exp (R * k) := by rw [← Real.exp_nat_mul, mul_comm]
        _ ≤ Real.exp (h / 80) := Real.exp_le_exp.2 hkh
    have hA : (Nt.card : ℝ) * (2 * Real.exp (-(h / 40))) ≤ 2 * Real.exp (-(h / 80)) := by
      calc (Nt.card : ℝ) * (2 * Real.exp (-(h / 40)))
          ≤ Real.exp (h / 80) * (2 * Real.exp (-(h / 40))) :=
            mul_le_mul_of_nonneg_right hc1 (by positivity)
        _ = 2 * Real.exp (-(h / 80)) := by
            rw [mul_left_comm, ← Real.exp_add]
            congr 2
            ring
    have hB' : Real.exp (-h) ≤ Real.exp (-(h / 80)) := Real.exp_le_exp.2 (by linarith)
    have hE : Real.exp (-(h / 80)) = Real.exp (-(1 / 160 * h)) * Real.exp (-(1 / 160 * h)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3 : 3 * Real.exp (-(1 / 160 * h)) ≤ 1 := by
      have h4 : Real.exp (-(1 / 160 * h)) * Real.exp (1 / 160 * h) = 1 := by
        rw [← Real.exp_add]
        simp
      have h5 : 1 / 160 * (h : ℝ) + 1 ≤ Real.exp (1 / 160 * h) := Real.add_one_le_exp _
      nlinarith [Real.exp_pos (-(1 / 160 * (h : ℝ)))]
    nlinarith [Real.exp_pos (-(1 / 160 * (h : ℝ)))]
  calc stdCGauss (Fin n × Fin k) {x | ∃ b, l2Norm (N *ᵥ (cgMat x *ᵥ b)) <
        1 / 160 * lam * Real.sqrt h * l2Norm b}
      ≤ stdCGauss (Fin n × Fin k) ({x | B * sh < ‖P * cgMat x‖} ∪
        ⋃ v ∈ Nt, {x | l2Norm (P *ᵥ (cgMat x *ᵥ v)) < sh / 2}) := measure_mono hsub
    _ ≤ stdCGauss (Fin n × Fin k) {x | B * sh < ‖P * cgMat x‖} +
        stdCGauss (Fin n × Fin k) (⋃ v ∈ Nt, {x | l2Norm (P *ᵥ (cgMat x *ᵥ v)) < sh / 2}) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-h)) + ∑ v ∈ Nt, stdCGauss (Fin n × Fin k)
        {x | l2Norm (P *ᵥ (cgMat x *ᵥ v)) < sh / 2} :=
        add_le_add hnorm (measure_biUnion_finset_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (-h)) + ∑ _v ∈ Nt, ENNReal.ofReal (2 * Real.exp (-(h / 40))) :=
        add_le_add le_rfl (Finset.sum_le_sum hvec)
    _ = ENNReal.ofReal (Real.exp (-h) + (Nt.card : ℝ) * (2 * Real.exp (-(h / 40)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_add (Real.exp_pos _).le (by positivity),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (Real.exp (-(1 / 160 * h))) := ENNReal.ofReal_le_ofReal hreal

end LSBA
