import LSBA.Gauss.PoincarePoly

/-!
# Moment Poincaré inequality with polynomial gradients

The dimension-free Gaussian `L^{2p}` Poincaré inequality
`𝔼|f − 𝔼f|^{2p} ≤ K_p 𝔼(Σ_i |∂_i f|²)^p` for `C¹` functions whose derivative grows at most
polynomially, with `K_p` depending only on `p`. It is used for the innovation bounds (11.58)
[lg:eq:innovations] (proof of Lemma 11.8 [lg:lem:dynamic]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Polynomial moments -/

private lemma poincareMoment_one_add_abs_pow_le (m : ℕ) (x : ℝ) :
    (1 + |x|) ^ m ≤ 2 ^ m * (1 + |x| ^ m) := by
  have h2 : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hx : (0 : ℝ) ≤ |x| ^ m := by positivity
  rcases le_total |x| 1 with h | h
  · calc (1 + |x|) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
  · calc (1 + |x|) ^ m ≤ (2 * |x|) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = 2 ^ m * |x| ^ m := by rw [mul_pow]
      _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith

private lemma poincareMoment_integrable_one_add_abs_pow (m : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 1) := by
  have hm : MemLp id (m : ENNReal) (gaussianReal (0 : ℝ) 1) :=
    memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) m (ENNReal.natCast_ne_top m)
  have hm' : MemLp id (m : ℕ) (gaussianReal (0 : ℝ) 1) := by simpa using hm
  have h1 : Integrable (fun x : ℝ => ‖id x‖ ^ m) (gaussianReal 0 1) := hm'.integrable_norm_pow'
  have h2 : Integrable (fun x : ℝ => (2 : ℝ) ^ m * (1 + |x| ^ m)) (gaussianReal 0 1) :=
    ((integrable_const (1 : ℝ)).add (by simpa using h1)).const_mul _
  refine h2.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ℝ => (1 + |x|) ^ m).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    exact poincareMoment_one_add_abs_pow_le m x

private lemma poincareMoment_one_add_norm_le_prod {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    1 + ‖x‖ ≤ ∏ j, (1 + |x j|) := by
  have hone : ∀ s : Finset ι, (1 : ℝ) ≤ ∏ l ∈ s, (1 + |x l|) := fun s =>
    Finset.one_le_prod₀ fun l _ => by linarith [abs_nonneg (x l)]
  have : ‖x‖ ≤ (∏ j, (1 + |x j|)) - 1 := by
    refine (pi_norm_le_iff_of_nonneg (by linarith [hone Finset.univ])).mpr fun j => ?_
    have hj : 1 + |x j| ≤ ∏ l, (1 + |x l|) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      exact le_mul_of_one_le_right (by positivity) (hone _)
    rw [Real.norm_eq_abs]
    linarith
  linarith

/-- Polynomial functions of the sup norm are integrable under the standard Gaussian on `ℝ^ι`. -/
private lemma poincareMoment_integrable_poly (ι : Type*) [Fintype ι] (m : ℕ) :
    Integrable (fun x : ι → ℝ => (1 + ‖x‖) ^ m) (stdGauss ι) := by
  have hprod : Integrable (fun x : ι → ℝ => ∏ j, (1 + |x j|) ^ m) (stdGauss ι) :=
    Integrable.fintype_prod (f := fun _ (t : ℝ) => (1 + |t|) ^ m)
      (fun _ => poincareMoment_integrable_one_add_abs_pow m)
  refine hprod.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ι → ℝ => (1 + ‖x‖) ^ m).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity), Finset.prod_pow]
    exact pow_le_pow_left₀ (by positivity) (poincareMoment_one_add_norm_le_prod x) m

/-! ### Law of a linear form -/

/-- The law of a linear form `y ↦ Σ_i a_i y_i` under the standard Gaussian is the law of
`√(Σ_i a_i²) · t` with `t ~ N(0, 1)`. -/
private lemma poincareMoment_map_linear {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (stdGauss ι).map (fun y => ∑ i, a i * y i) =
      (gaussianReal 0 1).map (fun t => Real.sqrt (∑ i, a i ^ 2) * t) := by
  set μ := stdGauss ι with hμ
  have hs : 0 ≤ ∑ i, a i ^ 2 := by positivity
  have hcoord : ∀ i, HasLaw (fun y : ι → ℝ => y i) (gaussianReal 0 1) μ := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  have hG : ∀ i, HasGaussianLaw (fun y : ι → ℝ => a i * y i) μ := fun i =>
    (hcoord i).hasGaussianLaw.fun_smul (a i)
  have hind : iIndepFun (fun (i : ι) (y : ι → ℝ) => a i * y i) μ :=
    iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1) (X := fun i t => a i * t)
      fun i => (measurable_const.mul measurable_id).aemeasurable
  have hGs : HasGaussianLaw (fun y : ι → ℝ => ∑ i, a i * y i) μ :=
    hind.hasGaussianLaw_fun_sum hG
  rw [hGs.map_eq_gaussianReal, gaussianReal_map_const_mul]
  have hmean : μ[fun y : ι → ℝ => ∑ i, a i * y i] = 0 := by
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_const_mul]
      have : ∫ y : ι → ℝ, y i ∂μ = 0 := by
        rw [hμ, stdGauss, integral_eval]
        exact integral_id_gaussianReal
      rw [this, mul_zero]
    · exact fun i _ => (hG i).integrable
  have hvar : Var[fun y : ι → ℝ => ∑ i, a i * y i; μ] = ∑ i, a i ^ 2 := by
    have := variance_sum_pi (μ := fun _ : ι => gaussianReal 0 1) (X := fun i t => a i * t)
      (fun i => IsGaussian.memLp_two_id.const_mul _)
    have e : (fun y : ι → ℝ => ∑ i, a i * y i) = ∑ i, fun y : ι → ℝ => a i * y i := by
      funext y; simp
    rw [e]
    refine this.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    change Var[fun t => a i * (id t); gaussianReal 0 1] = _
    rw [variance_const_mul, variance_id_gaussianReal]
    simp
  rw [hmean, hvar]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt hs, hs]

/-- The `2p`-th moment of the standard Gaussian on `ℝ`. -/
private def poincareMoment_cp (p : ℕ) : ℝ := ∫ t : ℝ, t ^ (2 * p) ∂(gaussianReal 0 1)

private lemma poincareMoment_cp_nonneg (p : ℕ) : 0 ≤ poincareMoment_cp p :=
  integral_nonneg fun t => by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg t) p

/-- `E (Σ_i a_i y_i)^{2p} = c_p (Σ_i a_i²)^p` under the standard Gaussian. -/
private lemma poincareMoment_integral_linear_pow {ι : Type*} [Fintype ι] (p : ℕ) (a : ι → ℝ) :
    ∫ y, (∑ i, a i * y i) ^ (2 * p) ∂(stdGauss ι) =
      poincareMoment_cp p * (∑ i, a i ^ 2) ^ p := by
  have hs : 0 ≤ ∑ i, a i ^ 2 := by positivity
  have hX : Measurable fun y : ι → ℝ => ∑ i, a i * y i :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  have h1 := integral_map (μ := stdGauss ι) (φ := fun y : ι → ℝ => ∑ i, a i * y i)
    (f := fun u : ℝ => u ^ (2 * p)) hX.aemeasurable
    (by fun_prop : Continuous fun u : ℝ => u ^ (2 * p)).aestronglyMeasurable
  rw [← h1, poincareMoment_map_linear]
  have hc : Measurable fun t : ℝ => Real.sqrt (∑ i, a i ^ 2) * t :=
    measurable_const.mul measurable_id
  rw [integral_map hc.aemeasurable
    (by fun_prop : Continuous fun u : ℝ => u ^ (2 * p)).aestronglyMeasurable]
  simp only [mul_pow]
  rw [integral_const_mul, poincareMoment_cp, pow_mul, Real.sq_sqrt hs, mul_comm]

/-! ### The real case with bounded derivative -/

private lemma poincareMoment_clm_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (y : ι → ℝ) : L y = ∑ i, L (Pi.single i 1) * y i := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (y i) : ι → ℝ) = y i • (Pi.single i 1 : ι → ℝ) := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [this, map_smul, smul_eq_mul, mul_comm]

/-- The Gaussian `L^{2p}` Poincaré inequality for a real `C¹` function with bounded derivative,
with constant `(π/2)^{2p} c_p`, where `c_p` is the `2p`-th moment of `N(0, 1)`. -/
private lemma poincareMoment_real {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ)
    (F : (ι → ℝ) → ℝ) (hF : ContDiff ℝ 1 F) {B : ℝ} (hB : ∀ x, ‖fderiv ℝ F x‖ ≤ B) :
    ∫ x, (F x - ∫ y, F y ∂(stdGauss ι)) ^ (2 * p) ∂(stdGauss ι) ≤
      (π / 2) ^ (2 * p) * poincareMoment_cp p *
        ∫ x, (∑ i, (fderiv ℝ F x (Pi.single i 1)) ^ 2) ^ p ∂(stdGauss ι) := by
  set μ := stdGauss ι with hμ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hDc : Continuous fun x => fderiv ℝ F x := hF.continuous_fderiv one_ne_zero
  have hDq : Integrable (fun q : (ι → ℝ) × (ι → ℝ) => (fderiv ℝ F q.1 q.2) ^ (2 * p))
      (μ.prod μ) := by
    refine (((poincareMoment_integrable_poly ι (2 * p)).const_mul (B ^ (2 * p))).comp_snd μ).mono'
      (((hDc.comp continuous_fst).clm_apply continuous_snd).pow (2 * p)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    rw [norm_pow, ← mul_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    calc ‖fderiv ℝ F q.1 q.2‖ ≤ ‖fderiv ℝ F q.1‖ * ‖q.2‖ := (fderiv ℝ F q.1).le_opNorm _
      _ ≤ B * ‖q.2‖ := by gcongr; exact hB _
      _ ≤ B * (1 + ‖q.2‖) := by gcongr; linarith
  have hint : Integrable (fun q : (ι → ℝ) × (ι → ℝ) => (π / 2 * fderiv ℝ F q.1 q.2) ^ (2 * p))
      (μ.prod μ) := by
    simp_rw [mul_pow]
    exact hDq.const_mul _
  have hle := pisier_interpolation F hF hB (fun t => t ^ (2 * p)) (even_two_mul p).convexOn_pow hint
  refine hle.trans (le_of_eq ?_)
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_prod _ hDq, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have := poincareMoment_integral_linear_pow (ι := ι) p (fun i => fderiv ℝ F x (Pi.single i 1))
  beta_reduce
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [← poincareMoment_clm_apply (fderiv ℝ F x) y]

/-! ### The complex case with bounded derivative -/

private lemma poincareMoment_add_pow_le (p : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ p ≤ 2 ^ p * (a ^ p + b ^ p) := by
  have h2 : (0 : ℝ) ≤ 2 ^ p := by positivity
  rcases le_total a b with h | h
  · calc (a + b) ^ p ≤ (2 * b) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
      _ = 2 ^ p * b ^ p := by rw [mul_pow]
      _ ≤ 2 ^ p * (a ^ p + b ^ p) := by
          have : 0 ≤ a ^ p := by positivity
          nlinarith
  · calc (a + b) ^ p ≤ (2 * a) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
      _ = 2 ^ p * a ^ p := by rw [mul_pow]
      _ ≤ 2 ^ p * (a ^ p + b ^ p) := by
          have : 0 ≤ b ^ p := by positivity
          nlinarith

private lemma poincareMoment_gradSq_nonneg {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ)
    (x : ι → ℝ) : 0 ≤ gradSq f x :=
  Finset.sum_nonneg fun _ _ => by positivity

private lemma poincareMoment_gradSq_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) (x : ι → ℝ) :
    gradSq f x = ∑ i, ‖fderiv ℝ f x (Pi.single i 1)‖ ^ 2 := by
  unfold gradSq
  congr!

private lemma poincareMoment_norm_partial_le {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ)
    (x : ι → ℝ) (i : ι) : ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ ‖fderiv ℝ f x‖ := by
  have h := (fderiv ℝ f x).le_opNorm (Pi.single i 1)
  have h1 : ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ = 1 := by
    rw [Pi.norm_single]; simp
  rwa [h1, mul_one] at h

private lemma poincareMoment_gradSq_le {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ) (x : ι → ℝ)
    {B : ℝ} (hB : ‖fderiv ℝ f x‖ ≤ B) : gradSq f x ≤ Fintype.card ι * B ^ 2 := by
  unfold gradSq
  calc ∑ i, ‖fderiv ℝ f x (Pi.single i 1)‖ ^ 2 ≤ ∑ _i : ι, B ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _)
          ((poincareMoment_norm_partial_le f x i).trans hB) 2
    _ = Fintype.card ι * B ^ 2 := by simp

private lemma poincareMoment_continuous_gradSq {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ 1 f) : Continuous (gradSq f) := by
  unfold gradSq
  refine continuous_finsetSum _ fun i _ => ?_
  exact (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm).pow 2

/-- The Gaussian `L^{2p}` Poincaré inequality for a complex `C¹` function with bounded values
and bounded derivative. -/
private lemma poincareMoment_complex {ι : Type*} [Fintype ι] (p : ℕ)
    (F : (ι → ℝ) → ℂ) (hF : ContDiff ℝ 1 F) {M B : ℝ} (hM : ∀ x, ‖F x‖ ≤ M)
    (hB : ∀ x, ‖fderiv ℝ F x‖ ≤ B) :
    ∫ x, ‖F x - ∫ y, F y ∂(stdGauss ι)‖ ^ (2 * p) ∂(stdGauss ι) ≤
      2 ^ (p + 1) * ((π / 2) ^ (2 * p) * poincareMoment_cp p) *
        ∫ x, gradSq F x ^ p ∂(stdGauss ι) := by
  set μ := stdGauss ι with hμ
  set κ : ℝ := (π / 2) ^ (2 * p) * poincareMoment_cp p with hκ
  have hκ0 : 0 ≤ κ := mul_nonneg (by positivity) (poincareMoment_cp_nonneg p)
  set fr : (ι → ℝ) → ℝ := fun x => (F x).re with hfr_def
  set fi : (ι → ℝ) → ℝ := fun x => (F x).im with hfi_def
  have hfd : ∀ x, HasFDerivAt F (fderiv ℝ F x) x :=
    fun x => ((hF.differentiable one_ne_zero) x).hasFDerivAt
  have hdr : ∀ x, fderiv ℝ fr x = Complex.reCLM.comp (fderiv ℝ F x) :=
    fun x => (Complex.reCLM.hasFDerivAt.comp x (hfd x)).fderiv
  have hdi : ∀ x, fderiv ℝ fi x = Complex.imCLM.comp (fderiv ℝ F x) :=
    fun x => (Complex.imCLM.hasFDerivAt.comp x (hfd x)).fderiv
  have hfr : ContDiff ℝ 1 fr := Complex.reCLM.contDiff.comp hF
  have hfi : ContDiff ℝ 1 fi := Complex.imCLM.contDiff.comp hF
  have hbr : ∀ x, ‖fderiv ℝ fr x‖ ≤ B := by
    intro x
    rw [hdr]
    calc _ ≤ ‖Complex.reCLM‖ * ‖fderiv ℝ F x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B := by rw [Complex.reCLM_norm, one_mul]; exact hB x
  have hbi : ∀ x, ‖fderiv ℝ fi x‖ ≤ B := by
    intro x
    rw [hdi]
    calc _ ≤ ‖Complex.imCLM‖ * ‖fderiv ℝ F x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B := by rw [Complex.imCLM_norm, one_mul]; exact hB x
  have hFint : Integrable F μ :=
    Integrable.of_bound hF.continuous.aestronglyMeasurable M (Filter.Eventually.of_forall hM)
  have hre : ∫ y, fr y ∂μ = (∫ y, F y ∂μ).re := by
    have := Complex.reCLM.integral_comp_comm hFint
    simpa using this
  have him : ∫ y, fi y ∂μ = (∫ y, F y ∂μ).im := by
    have := Complex.imCLM.integral_comp_comm hFint
    simpa using this
  set m := ∫ y, F y ∂μ with hm_def
  have hm : ‖m‖ ≤ M := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hM)
    simpa using this
  have hz : ∀ x, ‖F x - m‖ ≤ 2 * M := fun x => (norm_sub_le _ _).trans (by linarith [hM x])
  have hRr := poincareMoment_real p fr hfr hbr
  have hRi := poincareMoment_real p fi hfi hbi
  -- the gradient side
  have hgs : Integrable (fun x => gradSq F x ^ p) μ := by
    refine Integrable.of_bound (C := ((Fintype.card ι : ℝ) * B ^ 2) ^ p)
      ((poincareMoment_continuous_gradSq F hF).pow p).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (poincareMoment_gradSq_nonneg F x) p)]
    exact pow_le_pow_left₀ (poincareMoment_gradSq_nonneg F x)
      (poincareMoment_gradSq_le F x (hB x)) p
  have hgr : ∀ x, ∑ i, (fderiv ℝ fr x (Pi.single i 1)) ^ 2 ≤ gradSq F x := by
    intro x
    rw [poincareMoment_gradSq_eq]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hdr]
    change ((fderiv ℝ F x (Pi.single i 1)).re) ^ 2 ≤ _
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  have hgi : ∀ x, ∑ i, (fderiv ℝ fi x (Pi.single i 1)) ^ 2 ≤ gradSq F x := by
    intro x
    rw [poincareMoment_gradSq_eq]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hdi]
    change ((fderiv ℝ F x (Pi.single i 1)).im) ^ 2 ≤ _
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2
  have hIr : ∫ x, (∑ i, (fderiv ℝ fr x (Pi.single i 1)) ^ 2) ^ p ∂μ ≤ ∫ x, gradSq F x ^ p ∂μ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hgs
      (Filter.Eventually.of_forall fun x =>
        pow_le_pow_left₀ (by positivity) (hgr x) p)
  have hIi : ∫ x, (∑ i, (fderiv ℝ fi x (Pi.single i 1)) ^ 2) ^ p ∂μ ≤ ∫ x, gradSq F x ^ p ∂μ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hgs
      (Filter.Eventually.of_forall fun x =>
        pow_le_pow_left₀ (by positivity) (hgi x) p)
  -- the left side
  have hure : ∀ x, fr x - ∫ y, fr y ∂μ = (F x - m).re := fun x => by
    rw [hre, Complex.sub_re]
  have hvim : ∀ x, fi x - ∫ y, fi y ∂μ = (F x - m).im := fun x => by
    rw [him, Complex.sub_im]
  have hui : Integrable (fun x => (fr x - ∫ y, fr y ∂μ) ^ (2 * p)) μ := by
    refine Integrable.of_bound (C := (2 * M) ^ (2 * p))
      (((hfr.continuous.sub continuous_const).pow (2 * p)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [hure, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (((Complex.abs_re_le_norm _).trans (hz x)).trans' (by rw [Real.norm_eq_abs])) _
  have hvi : Integrable (fun x => (fi x - ∫ y, fi y ∂μ) ^ (2 * p)) μ := by
    refine Integrable.of_bound (C := (2 * M) ^ (2 * p))
      (((hfi.continuous.sub continuous_const).pow (2 * p)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [hvim, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (((Complex.abs_im_le_norm _).trans (hz x)).trans' (by rw [Real.norm_eq_abs])) _
  have hpt : ∀ x, ‖F x - m‖ ^ (2 * p) ≤
      2 ^ p * ((fr x - ∫ y, fr y ∂μ) ^ (2 * p) + (fi x - ∫ y, fi y ∂μ) ^ (2 * p)) := by
    intro x
    rw [hure, hvim, pow_mul, Complex.sq_norm, Complex.normSq_apply, pow_mul, pow_mul]
    have := poincareMoment_add_pow_le p (a := (F x - m).re * (F x - m).re)
      (b := (F x - m).im * (F x - m).im) (mul_self_nonneg _) (mul_self_nonneg _)
    simpa only [← sq] using this
  have hmono : ∫ x, ‖F x - m‖ ^ (2 * p) ∂μ ≤
      ∫ x, 2 ^ p * ((fr x - ∫ y, fr y ∂μ) ^ (2 * p) + (fi x - ∫ y, fi y ∂μ) ^ (2 * p)) ∂μ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
      ((hui.add hvi).const_mul _) (Filter.Eventually.of_forall hpt)
  refine hmono.trans ?_
  rw [integral_const_mul, integral_add hui hvi]
  have h2p : (2 : ℝ) ^ (p + 1) = 2 ^ p * 2 := pow_succ _ _
  rw [h2p]
  have hsum : ∫ x, (fr x - ∫ y, fr y ∂μ) ^ (2 * p) ∂μ +
      ∫ x, (fi x - ∫ y, fi y ∂μ) ^ (2 * p) ∂μ ≤ 2 * (κ * ∫ x, gradSq F x ^ p ∂μ) := by
    have h1 := hRr.trans (mul_le_mul_of_nonneg_left hIr hκ0)
    have h2 := hRi.trans (mul_le_mul_of_nonneg_left hIi hκ0)
    linarith
  calc 2 ^ p * (∫ x, (fr x - ∫ y, fr y ∂μ) ^ (2 * p) ∂μ +
        ∫ x, (fi x - ∫ y, fi y ∂μ) ^ (2 * p) ∂μ)
      ≤ 2 ^ p * (2 * (κ * ∫ x, gradSq F x ^ p ∂μ)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-! ### Growth of `f` -/

private lemma poincareMoment_nonneg {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ) {C : ℝ} {k : ℕ}
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k) : 0 ≤ C := by
  have h := (norm_nonneg _).trans (hb 0)
  simpa using h

/-- `‖f x‖ ≤ (‖f 0‖ + C) (1 + ‖x‖)^(k+1)`. -/
private lemma poincareMoment_norm_le {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ 1 f) {C : ℝ} {k : ℕ} (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k)
    (x : ι → ℝ) : ‖f x‖ ≤ (‖f 0‖ + C) * (1 + ‖x‖) ^ (k + 1) := by
  have hC : 0 ≤ C := poincareMoment_nonneg f hb
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := f)
    (s := Metric.closedBall (0 : ι → ℝ) ‖x‖) (C := C * (1 + ‖x‖) ^ k) (x := 0) (y := x)
    (fun z _ => (hf.differentiable one_ne_zero) z)
    (fun z hz => (hb z).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by
        have := mem_closedBall_zero_iff.mp hz
        linarith) k) hC))
    (convex_closedBall _ _) (by simp) (by simp)
  rw [sub_zero] at h
  have hp : (1 : ℝ) ≤ (1 + ‖x‖) ^ (k + 1) := one_le_pow₀ (by linarith)
  have h1 : C * (1 + ‖x‖) ^ k * ‖x‖ ≤ C * (1 + ‖x‖) ^ (k + 1) := by
    rw [pow_succ, ← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  calc ‖f x‖ = ‖f 0 + (f x - f 0)‖ := by rw [add_sub_cancel]
    _ ≤ ‖f 0‖ + ‖f x - f 0‖ := norm_add_le _ _
    _ ≤ ‖f 0‖ * (1 + ‖x‖) ^ (k + 1) + C * (1 + ‖x‖) ^ (k + 1) := by
        have := le_mul_of_one_le_right (norm_nonneg (f 0)) hp
        linarith
    _ = (‖f 0‖ + C) * (1 + ‖x‖) ^ (k + 1) := by ring

/-! ### Cutoffs -/

/-- A sequence of `C¹` cutoffs with values in `[0, 1]`, compact supports, derivatives bounded by a
common constant, and locally equal to `1` for large index around each point. -/
private lemma poincareMoment_cutoff (ι : Type*) [Fintype ι] :
    ∃ (c : ℕ → (ι → ℝ) → ℝ) (L : ℝ), 0 ≤ L ∧ (∀ n, ContDiff ℝ 1 (c n)) ∧
      (∀ n, HasCompactSupport (c n)) ∧ (∀ n x, 0 ≤ c n x ∧ c n x ≤ 1) ∧
      (∀ n x, ‖fderiv ℝ (c n) x‖ ≤ L) ∧
      (∀ x, ∀ᶠ n in Filter.atTop, ∀ᶠ y in nhds x, c n y = 1) := by
  let χ : ContDiffBump (0 : ι → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨L, hL⟩ := ((χ.contDiff (n := 1)).continuous_fderiv one_ne_zero
    ).bounded_above_of_compact_support (χ.hasCompactSupport.fderiv ℝ)
  have hL0 : 0 ≤ max L 0 := le_max_right _ _
  have hr : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := fun n => by positivity
  have hr1 : ∀ n : ℕ, ((n : ℝ) + 1)⁻¹ ≤ 1 := fun n =>
    inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  refine ⟨fun n x => χ (((n : ℝ) + 1)⁻¹ • x), max L 0, hL0, fun n => ?_, fun n => ?_,
    fun n x => ⟨χ.nonneg, χ.le_one⟩, fun n x => ?_, fun x => ?_⟩
  · exact χ.contDiff.comp (by fun_prop : ContDiff ℝ 1 fun x : ι → ℝ => ((n : ℝ) + 1)⁻¹ • x)
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℝ) (2 * ((n : ℝ) + 1)))
      fun x hx => ?_
    refine χ.zero_of_le_dist ?_
    have hx' : 2 * ((n : ℝ) + 1) < ‖x‖ := by simpa using hx
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have : ‖(((n : ℝ) + 1)⁻¹ • x)‖ = ((n : ℝ) + 1)⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (hr n).le]
    rw [dist_zero_right, this]
    change (2 : ℝ) ≤ _
    rw [inv_mul_eq_div, le_div_iff₀ hR]
    linarith
  · have hs : HasFDerivAt (fun y : ι → ℝ => ((n : ℝ) + 1)⁻¹ • y)
        (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (ι → ℝ)) x :=
      (hasFDerivAt_id x).const_smul (((n : ℝ) + 1)⁻¹)
    have hd : HasFDerivAt (fun x : ι → ℝ => χ (((n : ℝ) + 1)⁻¹ • x))
        ((fderiv ℝ χ (((n : ℝ) + 1)⁻¹ • x)).comp
          (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (ι → ℝ))) x :=
      (((χ.contDiff (n := 1)).differentiable one_ne_zero) (((n : ℝ) + 1)⁻¹ • x)).hasFDerivAt.comp x
        hs
    rw [hd.fderiv]
    calc _ ≤ ‖fderiv ℝ χ (((n : ℝ) + 1)⁻¹ • x)‖ *
          ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (ι → ℝ)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ max L 0 * 1 := by
          refine mul_le_mul ((hL _).trans (le_max_left _ _)) ?_ (norm_nonneg _) hL0
          calc _ ≤ ‖((n : ℝ) + 1)⁻¹‖ * ‖ContinuousLinearMap.id ℝ (ι → ℝ)‖ := norm_smul_le _ _
            _ ≤ 1 * 1 := by
                refine mul_le_mul ?_ ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
                rw [Real.norm_of_nonneg (hr n).le]; exact hr1 n
            _ = 1 := one_mul 1
      _ = max L 0 := mul_one _
  · obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hlt : ‖x‖ < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hmem : ((n : ℝ) + 1)⁻¹ • x ∈ Metric.ball (0 : ι → ℝ) χ.rIn := by
      have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (hr n).le, inv_mul_eq_div,
        div_lt_iff₀ hR]
      change ‖x‖ < 1 * _
      linarith
    have h1 : ∀ᶠ y in nhds (((n : ℝ) + 1)⁻¹ • x), χ y = 1 :=
      χ.eventuallyEq_one_of_mem_ball hmem
    exact ((continuous_const_smul (((n : ℝ) + 1)⁻¹)).tendsto x).eventually h1

private lemma poincareMoment_norm_fderiv_smul_le {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ 1 f) (c : (ι → ℝ) → ℝ) (hc : ContDiff ℝ 1 c) (hc0 : ∀ x, 0 ≤ c x)
    (hc1 : ∀ x, c x ≤ 1) (x : ι → ℝ) :
    ‖fderiv ℝ (fun y => c y • f y) x‖ ≤ ‖fderiv ℝ f x‖ + ‖fderiv ℝ c x‖ * ‖f x‖ := by
  have hd : fderiv ℝ (fun y => c y • f y) x =
      c x • fderiv ℝ f x + (fderiv ℝ c x).smulRight (f x) :=
    (((hc.differentiable one_ne_zero) x).hasFDerivAt.smul
      ((hf.differentiable one_ne_zero) x).hasFDerivAt).fderiv
  rw [hd]
  calc _ ≤ ‖c x • fderiv ℝ f x‖ + ‖(fderiv ℝ c x).smulRight (f x)‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ f x‖ + ‖fderiv ℝ c x‖ * ‖f x‖ := by
        refine add_le_add ?_ (ContinuousLinearMap.norm_smulRight_apply _ _).le
        rw [norm_smul, Real.norm_of_nonneg (hc0 x)]
        exact mul_le_of_le_one_left (norm_nonneg _) (hc1 x)

/-! ### Truncation -/

/-- The `L^{2p}` Poincaré inequality for `C¹` functions with polynomially growing derivative,
with an explicit constant. -/
private lemma poincareMoment_poly {ι : Type*} [Fintype ι] (p : ℕ)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ 1 f) {C : ℝ} {k : ℕ}
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    ∫ x, ‖f x - ∫ y, f y ∂(stdGauss ι)‖ ^ (2 * p) ∂(stdGauss ι) ≤
      2 ^ (p + 1) * ((π / 2) ^ (2 * p) * poincareMoment_cp p) *
        ∫ x, gradSq f x ^ p ∂(stdGauss ι) := by
  obtain ⟨c, L, hL0, hcd, hcs, hc01, hcL, hclim⟩ := poincareMoment_cutoff ι
  set μ := stdGauss ι with hμ
  have hC : 0 ≤ C := poincareMoment_nonneg f hb
  set A : ℝ := ‖f 0‖ + C with hA
  have hA0 : 0 ≤ A := by have := norm_nonneg (f 0); linarith
  have hfgrow := poincareMoment_norm_le f hf hb
  have hfc : Continuous f := hf.continuous
  have hint1 : Integrable f μ :=
    ((poincareMoment_integrable_poly ι (k + 1)).const_mul A).mono' hfc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hfgrow x)
  -- truncations
  set F : ℕ → (ι → ℝ) → ℂ := fun n y => c n y • f y with hF
  have hFd : ∀ n, ContDiff ℝ 1 (F n) := fun n => (hcd n).smul hf
  have hFnorm : ∀ n x, ‖F n x‖ ≤ ‖f x‖ := fun n x => by
    simp only [hF]
    rw [norm_smul, Real.norm_of_nonneg (hc01 n x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hc01 n x).2
  have hFsupp : ∀ n, HasCompactSupport (F n) := fun n => (hcs n).smul_right
  have hPoin : ∀ n, ∫ x, ‖F n x - ∫ y, F n y ∂μ‖ ^ (2 * p) ∂μ ≤
      2 ^ (p + 1) * ((π / 2) ^ (2 * p) * poincareMoment_cp p) * ∫ x, gradSq (F n) x ^ p ∂μ :=
    fun n => by
    obtain ⟨M, hM⟩ := (hFd n).continuous.bounded_above_of_compact_support (hFsupp n)
    obtain ⟨B, hB⟩ := ((hFd n).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
      ((hFsupp n).fderiv ℝ)
    exact poincareMoment_complex p (F n) (hFd n) hM hB
  have hFlim : ∀ x, ∀ᶠ n in Filter.atTop, F n x = f x := fun x => by
    filter_upwards [hclim x] with n hn
    have : c n x = 1 := hn.self_of_nhds
    simp [hF, this]
  have hFlimD : ∀ x, ∀ᶠ n in Filter.atTop, fderiv ℝ (F n) x = fderiv ℝ f x := fun x => by
    filter_upwards [hclim x] with n hn
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hn] with y hy
    simp [hF, hy]
  -- convergence of the means
  have hmean : Filter.Tendsto (fun n => ∫ y, F n y ∂μ) Filter.atTop
      (nhds (∫ y, f y ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖f y‖)
      (fun n => (hFd n).continuous.aestronglyMeasurable) hint1.norm
      (fun n => Filter.Eventually.of_forall fun y => hFnorm n y)
      (Filter.Eventually.of_forall fun y => ?_)
    exact tendsto_const_nhds.congr' ((hFlim y).mono fun n hn => hn.symm)
  set S : ℝ := ∫ y, ‖f y‖ ∂μ with hS
  have hS0 : 0 ≤ S := integral_nonneg fun _ => norm_nonneg _
  have hmbound : ∀ n, ‖∫ y, F n y ∂μ‖ ≤ S := fun n =>
    norm_integral_le_of_norm_le hint1.norm (Filter.Eventually.of_forall (hFnorm n))
  -- left side
  have hLim : Filter.Tendsto (fun n => ∫ x, ‖F n x - ∫ y, F n y ∂μ‖ ^ (2 * p) ∂μ)
      Filter.atTop (nhds (∫ x, ‖f x - ∫ y, f y ∂μ‖ ^ (2 * p) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => (A + S) ^ (2 * p) * (1 + ‖x‖) ^ ((k + 1) * (2 * p)))
      (fun n => (((hFd n).continuous.sub continuous_const).norm.pow (2 * p)).aestronglyMeasurable)
      ((poincareMoment_integrable_poly ι ((k + 1) * (2 * p))).const_mul _)
      (fun n => Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => ?_)
    · rw [norm_pow, norm_norm, pow_mul (1 + ‖x‖) (k + 1) (2 * p), ← mul_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
      have hx1 : (1 : ℝ) ≤ (1 + ‖x‖) ^ (k + 1) := one_le_pow₀ (by linarith [norm_nonneg x])
      calc ‖F n x - ∫ y, F n y ∂μ‖ ≤ ‖F n x‖ + ‖∫ y, F n y ∂μ‖ := norm_sub_le _ _
        _ ≤ A * (1 + ‖x‖) ^ (k + 1) + S := add_le_add ((hFnorm n x).trans (hfgrow x)) (hmbound n)
        _ ≤ (A + S) * (1 + ‖x‖) ^ (k + 1) := by nlinarith
    · have h1 : Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x)) :=
        tendsto_const_nhds.congr' ((hFlim x).mono fun n hn => hn.symm)
      exact ((h1.sub hmean).norm).pow _
  -- right side
  have hRim : Filter.Tendsto (fun n => ∫ x, gradSq (F n) x ^ p ∂μ) Filter.atTop
      (nhds (∫ x, gradSq f x ^ p ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => ((Fintype.card ι : ℝ) * (C + L * A) ^ 2) ^ p * (1 + ‖x‖) ^ (2 * (k + 1) * p))
      (fun n => ((poincareMoment_continuous_gradSq (F n) (hFd n)).pow p).aestronglyMeasurable)
      ((poincareMoment_integrable_poly ι (2 * (k + 1) * p)).const_mul _)
      (fun n => Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => ?_)
    · rw [Real.norm_of_nonneg (pow_nonneg (poincareMoment_gradSq_nonneg _ _) p)]
      have hx1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
      have hpk : (1 + ‖x‖) ^ k ≤ (1 + ‖x‖) ^ (k + 1) := pow_le_pow_right₀ hx1 (Nat.le_succ k)
      have hD := poincareMoment_norm_fderiv_smul_le f hf (c n) (hcd n) (fun y => (hc01 n y).1)
        (fun y => (hc01 n y).2) x
      have hB : ‖fderiv ℝ (F n) x‖ ≤ (C + L * A) * (1 + ‖x‖) ^ (k + 1) := by
        refine hD.trans ?_
        have h1 : ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ (k + 1) :=
          (hb x).trans (mul_le_mul_of_nonneg_left hpk hC)
        have h2 : ‖fderiv ℝ (c n) x‖ * ‖f x‖ ≤ L * (A * (1 + ‖x‖) ^ (k + 1)) :=
          mul_le_mul (hcL n x) (hfgrow x) (norm_nonneg _) hL0
        nlinarith
      have hg : gradSq (F n) x ≤
          (Fintype.card ι : ℝ) * (C + L * A) ^ 2 * (1 + ‖x‖) ^ (2 * (k + 1)) :=
        calc gradSq (F n) x ≤ Fintype.card ι * ((C + L * A) * (1 + ‖x‖) ^ (k + 1)) ^ 2 :=
              poincareMoment_gradSq_le (F n) x hB
          _ = _ := by rw [mul_pow, ← pow_mul]; ring_nf
      calc gradSq (F n) x ^ p ≤
            ((Fintype.card ι : ℝ) * (C + L * A) ^ 2 * (1 + ‖x‖) ^ (2 * (k + 1))) ^ p :=
            pow_le_pow_left₀ (poincareMoment_gradSq_nonneg _ _) hg p
        _ = _ := by rw [mul_pow, ← pow_mul]
    · have h1 : ∀ᶠ n in Filter.atTop, gradSq (F n) x = gradSq f x :=
        (hFlimD x).mono fun n hn => by unfold gradSq; rw [hn]
      exact tendsto_const_nhds.congr' (h1.mono fun n hn => by
        change gradSq f x ^ p = gradSq (F n) x ^ p
        rw [hn])
  exact le_of_tendsto_of_tendsto' hLim (hRim.const_mul _) hPoin

/-- Gaussian `L^{2p}` Poincaré inequality with a constant depending only on `p`, for `C¹`
functions with polynomially growing derivative. -/
theorem moment_poincare_grad_poly (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℂ),
      ContDiff ℝ 1 f → ∀ {C : ℝ} {k : ℕ}, (∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k) →
        ∫ x, ‖f x - ∫ y, f y ∂(stdGauss ι)‖ ^ (2 * p) ∂(stdGauss ι) ≤
          K * ∫ x, gradSq f x ^ p ∂(stdGauss ι) := by
  have hκ : 0 ≤ 2 ^ (p + 1) * ((π / 2) ^ (2 * p) * poincareMoment_cp p) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) (poincareMoment_cp_nonneg p))
  refine ⟨2 ^ (p + 1) * ((π / 2) ^ (2 * p) * poincareMoment_cp p) + 1, by linarith, ?_⟩
  intro ι _ _ f hf C k hb
  refine (poincareMoment_poly p f hf hb).trans ?_
  refine mul_le_mul_of_nonneg_right (by linarith) (integral_nonneg fun x => ?_)
  exact pow_nonneg (poincareMoment_gradSq_nonneg f x) p

end LSBA
