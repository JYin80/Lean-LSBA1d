import LSBA.Gauss.StdGauss

/-!
# Gaussian interpolation: Poincaré and concentration

The Maurey–Pisier interpolation inequality for the standard Gaussian on `ℝ^ι`, and its
consequences: the Poincaré inequality with constant `π²/8` (used for (D.2) [rd:eq:poincare])
and Lipschitz concentration with the Maurey–Pisier constant (used for (D.6)
[eq:rough-density]). All constants are explicit and independent of the dimension.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Exponential moments of the standard Gaussian -/

/-- `exp (c |t|)` is integrable against the standard Gaussian on `ℝ`. -/
private lemma concentration_integrable_exp_abs (c : ℝ) :
    Integrable (fun t : ℝ => Real.exp (c * |t|)) (gaussianReal 0 1) := by
  have h := (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) c).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-c))
  refine h.mono' (by fun_prop : Continuous fun t : ℝ => Real.exp (c * |t|)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  change _ ≤ Real.exp (c * t) + Real.exp (-c * t)
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]; linarith [Real.exp_pos (-c * t)]
  · rw [abs_of_nonpos ht, show c * -t = -c * t by ring]; linarith [Real.exp_pos (c * t)]

/-- `exp (c ∑ᵢ |xᵢ|)` is integrable against the standard Gaussian on `ℝ^ι`. -/
private lemma concentration_integrable_exp_sum {ι : Type*} [Fintype ι] (c : ℝ) :
    Integrable (fun x : ι → ℝ => Real.exp (c * ∑ i, |x i|)) (stdGauss ι) := by
  have hprod : (fun x : ι → ℝ => Real.exp (c * ∑ i, |x i|)) =
      fun x => ∏ i, Real.exp (c * |x i|) := by
    funext x
    rw [Finset.mul_sum, Real.exp_sum]
  rw [hprod]
  exact Integrable.fintype_prod (f := fun _ (t : ℝ) => Real.exp (c * |t|))
    (fun _ => concentration_integrable_exp_abs c)

private lemma concentration_norm_le_sum {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ‖x‖ ≤ ∑ i, |x i| := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun i => |x i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)

/-- Affine functions of the sup norm are integrable under `stdGauss ι`. -/
private lemma concentration_integrable_affine {ι : Type*} [Fintype ι] (A B : ℝ) :
    Integrable (fun x : ι → ℝ => A + B * ‖x‖) (stdGauss ι) := by
  refine (integrable_const A).add (Integrable.const_mul ?_ B)
  refine ((concentration_integrable_exp_sum (ι := ι) 1)).mono'
    continuous_norm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_norm, one_mul]
  have h1 := concentration_norm_le_sum x
  linarith [Real.add_one_le_exp (∑ i, |x i|)]

/-- Squares of affine functions of the sup norm are integrable under `stdGauss ι`. -/
private lemma concentration_integrable_affine_sq {ι : Type*} [Fintype ι] (A B : ℝ) :
    Integrable (fun x : ι → ℝ => (A + B * ‖x‖) ^ 2) (stdGauss ι) := by
  have hI : Integrable (fun x : ι → ℝ => 2 * A ^ 2 + 2 * B ^ 2 * (2 * Real.exp (∑ i, |x i|)))
      (stdGauss ι) :=
    (integrable_const _).add (((concentration_integrable_exp_sum (ι := ι) 1).const_mul 2).congr
      (Filter.Eventually.of_forall fun x => by simp) |>.const_mul _)
  refine hI.mono' (by fun_prop : Continuous fun x : ι → ℝ => (A + B * ‖x‖) ^ 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  set s := ∑ i, |x i|
  have hs : 0 ≤ s := by positivity
  have h1 : ‖x‖ ≤ s := concentration_norm_le_sum x
  have h2 : ‖x‖ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 := Real.quadratic_le_exp_of_nonneg hs
  have h4 : (A + B * ‖x‖) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 * ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg (A - B * ‖x‖)]
  have h5 : B ^ 2 * ‖x‖ ^ 2 ≤ B ^ 2 * (2 * Real.exp s) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg B)
  linarith

/-! ### Linear growth from a bounded derivative -/

/-- A function with derivative bounded by `C` in operator norm grows at most linearly. -/
private lemma concentration_norm_le_affine {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (ι → ℝ) → E) (hf : ContDiff ℝ 1 f) {C : ℝ}
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (x : ι → ℝ) : ‖f x‖ ≤ ‖f 0‖ + C * ‖x‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hf.differentiable one_ne_zero) z) (fun z _ => hb z) convex_univ
    (Set.mem_univ 0) (Set.mem_univ x)
  rw [sub_zero] at h
  calc ‖f x‖ = ‖f 0 + (f x - f 0)‖ := by rw [add_sub_cancel]
    _ ≤ ‖f 0‖ + ‖f x - f 0‖ := norm_add_le _ _
    _ ≤ ‖f 0‖ + C * ‖x‖ := by linarith

private lemma concentration_integrable_of_fderiv {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (ι → ℝ) → E) (hf : ContDiff ℝ 1 f) {C : ℝ}
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) : Integrable f (stdGauss ι) :=
  (concentration_integrable_affine ‖f 0‖ C).mono' hf.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => concentration_norm_le_affine f hf hb x)

/-! ### The interpolation path -/

/-- `f x - f y = ∫₀^{π/2} Df(x sin θ + y cos θ)(x cos θ - y sin θ) dθ`. -/
private lemma concentration_path {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : (ι → ℝ) → E) (hf : ContDiff ℝ 1 f)
    (x y : ι → ℝ) :
    f x - f y = ∫ θ in (0 : ℝ)..(π / 2),
      fderiv ℝ f (Real.sin θ • x + Real.cos θ • y) (Real.cos θ • x - Real.sin θ • y) := by
  have hd : ∀ θ : ℝ, HasDerivAt (fun θ => Real.sin θ • x + Real.cos θ • y)
      (Real.cos θ • x - Real.sin θ • y) θ := by
    intro θ
    have := ((Real.hasDerivAt_sin θ).smul_const x).add ((Real.hasDerivAt_cos θ).smul_const y)
    have e : Real.cos θ • x - Real.sin θ • y = Real.cos θ • x + (-Real.sin θ) • y := by
      rw [neg_smul, ← sub_eq_add_neg]
    rw [e]
    exact this
  have hF : ∀ θ : ℝ, HasDerivAt (fun θ => f (Real.sin θ • x + Real.cos θ • y))
      (fderiv ℝ f (Real.sin θ • x + Real.cos θ • y) (Real.cos θ • x - Real.sin θ • y)) θ :=
    fun θ => ((hf.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt θ (hd θ)
  have hc : Continuous fun θ : ℝ =>
      fderiv ℝ f (Real.sin θ • x + Real.cos θ • y) (Real.cos θ • x - Real.sin θ • y) :=
    ((hf.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hF θ) (hc.intervalIntegrable _ _)]
  simp

/-- Jensen's inequality for the normalized measure `(2/π) dθ` on `[0, π/2]`. -/
private lemma concentration_jensen_theta (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ Set.univ Φ)
    (hΦc : Continuous Φ) (D : ℝ → ℝ) (hD : Continuous D) :
    Φ (∫ θ in (0 : ℝ)..(π / 2), D θ) ≤
      2 / π * ∫ θ in Set.Ioc (0 : ℝ) (π / 2), Φ (π / 2 * D θ) := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have hvol : volume.real (Set.Ioc (0 : ℝ) (π / 2)) = π / 2 := by
    rw [Real.volume_real_Ioc_of_le hpi.le, sub_zero]
  have h0 : volume (Set.Ioc (0 : ℝ) (π / 2)) ≠ 0 := by
    rw [Real.volume_Ioc]; simp [hpi]
  have ht : volume (Set.Ioc (0 : ℝ) (π / 2)) ≠ ∞ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have h := hΦ.map_set_average_le hΦc.continuousOn isClosed_univ h0 ht
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    (f := fun θ => π / 2 * D θ) (by fun_prop : Continuous fun θ => π / 2 * D θ).integrableOn_Ioc
    (hΦc.comp (by fun_prop : Continuous fun θ => π / 2 * D θ)).integrableOn_Ioc
  rw [setAverage_eq, setAverage_eq, hvol, integral_const_mul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul, ← intervalIntegral.integral_of_le hpi.le] at h
  convert h using 1
  field_simp

/-- Midpoint convexity at `0`. -/
private lemma concentration_midpoint (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ Set.univ Φ) (t : ℝ) :
    2 * Φ 0 - Φ (-t) ≤ Φ t := by
  have h := hΦ.2 (Set.mem_univ t) (Set.mem_univ (-t)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have : 1 / 2 * t + 1 / 2 * -t = 0 := by ring
  rw [this] at h
  linarith

/-! ### Rotation of a pair of independent standard Gaussians -/

/-- The rotated pair `(x sin θ + y cos θ, x cos θ - y sin θ)`. -/
private def concentration_rot {ι : Type*} (θ : ℝ) (q : (ι → ℝ) × (ι → ℝ)) :
    (ι → ℝ) × (ι → ℝ) :=
  (Real.sin θ • q.1 + Real.cos θ • q.2, Real.cos θ • q.1 - Real.sin θ • q.2)

private lemma concentration_rot_continuous {ι : Type*} :
    Continuous fun p : ℝ × ((ι → ℝ) × (ι → ℝ)) => concentration_rot p.1 p.2 := by
  unfold concentration_rot
  fun_prop

private lemma concentration_rot_integral {ι : Type*} [Fintype ι] (θ : ℝ) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (G : (ι → ℝ) × (ι → ℝ) → E) (hG : Continuous G) :
    ∫ q, G (concentration_rot θ q) ∂((stdGauss ι).prod (stdGauss ι)) =
      ∫ q, G q ∂((stdGauss ι).prod (stdGauss ι)) := by
  have hmp := measurePreserving_stdGauss_rotation (ι := ι) θ
  have := integral_map hmp.measurable.aemeasurable (f := G)
    (by rw [hmp.map_eq]; exact hG.aestronglyMeasurable)
  rw [hmp.map_eq] at this
  exact this.symm

private lemma concentration_rot_integrable {ι : Type*} [Fintype ι] (θ : ℝ) {E : Type*}
    [NormedAddCommGroup E] (G : (ι → ℝ) × (ι → ℝ) → E) (hG : Continuous G)
    (hi : Integrable G ((stdGauss ι).prod (stdGauss ι))) :
    Integrable (fun q => G (concentration_rot θ q)) ((stdGauss ι).prod (stdGauss ι)) :=
  ((measurePreserving_stdGauss_rotation (ι := ι) θ).integrable_comp
    hG.aestronglyMeasurable).mpr hi

private lemma concentration_abs_le {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) : |b| ≤ |a| + |c| :=
  abs_le.mpr ⟨by linarith [neg_abs_le a, abs_nonneg c], by linarith [le_abs_self c, abs_nonneg a]⟩

/-- The two-copy form of the interpolation inequality:
`E Φ(f(X) - f(Y)) ≤ E Φ((π/2)⟨∇f(X), Y⟩)`, together with the integrability of the left side. -/
private lemma concentration_core {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ Set.univ Φ)
    (hint : Integrable (fun q : (ι → ℝ) × (ι → ℝ) => Φ (π / 2 * fderiv ℝ f q.1 q.2))
      ((stdGauss ι).prod (stdGauss ι))) :
    Integrable (fun q : (ι → ℝ) × (ι → ℝ) => Φ (f q.1 - f q.2))
        ((stdGauss ι).prod (stdGauss ι)) ∧
      ∫ q, Φ (f q.1 - f q.2) ∂((stdGauss ι).prod (stdGauss ι)) ≤
        ∫ q, Φ (π / 2 * fderiv ℝ f q.1 q.2) ∂((stdGauss ι).prod (stdGauss ι)) := by
  set P := (stdGauss ι).prod (stdGauss ι) with hP
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (π / 2)) with hν
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hΦc : Continuous Φ := continuousOn_univ.mp (hΦ.continuousOn isOpen_univ)
  have hDc : Continuous fun x => fderiv ℝ f x := hf.continuous_fderiv one_ne_zero
  set H : (ι → ℝ) × (ι → ℝ) → ℝ := fun q => Φ (π / 2 * fderiv ℝ f q.1 q.2) with hH
  have hHc : Continuous H :=
    hΦc.comp (continuous_const.mul ((hDc.comp continuous_fst).clm_apply continuous_snd))
  set G : ℝ × ((ι → ℝ) × (ι → ℝ)) → ℝ := fun p => H (concentration_rot p.1 p.2) with hG
  have hGc : Continuous G := hHc.comp concentration_rot_continuous
  have hGi : Integrable G (ν.prod P) := by
    rw [integrable_prod_iff hGc.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun θ => concentration_rot_integrable θ H hHc hint, ?_⟩
    have : (fun θ => ∫ q, ‖G (θ, q)‖ ∂P) = fun _ => ∫ q, ‖H q‖ ∂P := by
      funext θ
      exact concentration_rot_integral θ (fun q => ‖H q‖) hHc.norm
    rw [this]
    exact integrable_const _
  set h : (ι → ℝ) × (ι → ℝ) → ℝ := fun q => 2 / π * ∫ θ, G (θ, q) ∂ν with hh
  have hhi : Integrable h P := hGi.integral_prod_right.const_mul _
  have hup : ∀ q : (ι → ℝ) × (ι → ℝ), Φ (f q.1 - f q.2) ≤ h q := by
    intro q
    rw [concentration_path f hf q.1 q.2]
    exact concentration_jensen_theta Φ hΦ hΦc _
      ((hDc.comp (by fun_prop)).clm_apply (by fun_prop))
  have hswap : Integrable (fun q => h q.swap) P :=
    (Measure.measurePreserving_swap.integrable_comp hhi.aestronglyMeasurable).mpr hhi
  have hlo : ∀ q : (ι → ℝ) × (ι → ℝ), 2 * Φ 0 - h q.swap ≤ Φ (f q.1 - f q.2) := by
    intro q
    have h1 := concentration_midpoint Φ hΦ (f q.1 - f q.2)
    have h2 := hup q.swap
    rw [neg_sub] at h1
    simp only [Prod.fst_swap, Prod.snd_swap] at h2
    linarith
  have hk : Integrable (fun q : (ι → ℝ) × (ι → ℝ) => Φ (f q.1 - f q.2)) P := by
    refine (((integrable_const (2 * Φ 0)).sub hswap).abs.add hhi.abs).mono'
      (hΦc.comp ((hf.continuous.comp continuous_fst).sub
        (hf.continuous.comp continuous_snd))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs]
    exact concentration_abs_le (hlo q) (hup q)
  refine ⟨hk, (integral_mono hk hhi hup).trans (le_of_eq ?_)⟩
  rw [hh, integral_const_mul]
  have hsw := integral_integral_swap (μ := ν) (ν := P) (f := fun θ q => G (θ, q)) hGi
  rw [← hsw]
  have hin : ∀ θ : ℝ, ∫ q, G (θ, q) ∂P = ∫ q, H q ∂P := fun θ =>
    concentration_rot_integral θ H hHc
  simp_rw [hin]
  rw [integral_const, smul_eq_mul, hν, measureReal_restrict_apply_univ,
    Real.volume_real_Ioc_of_le (by positivity), sub_zero]
  field_simp

/-! ### The interpolation inequality -/

/-- The interpolation inequality together with the integrability of its left side. -/
private lemma concentration_pisier_aux {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) {C : ℝ} (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (Φ : ℝ → ℝ)
    (hΦ : ConvexOn ℝ Set.univ Φ)
    (hint : Integrable (fun q : (ι → ℝ) × (ι → ℝ) => Φ (π / 2 * fderiv ℝ f q.1 q.2))
      ((stdGauss ι).prod (stdGauss ι))) :
    Integrable (fun x => Φ (f x - ∫ y, f y ∂(stdGauss ι))) (stdGauss ι) ∧
      ∫ x, Φ (f x - ∫ y, f y ∂(stdGauss ι)) ∂(stdGauss ι) ≤
        ∫ q, Φ (π / 2 * fderiv ℝ f q.1 q.2) ∂((stdGauss ι).prod (stdGauss ι)) := by
  set μ := stdGauss ι with hμ
  have hΦc : Continuous Φ := continuousOn_univ.mp (hΦ.continuousOn isOpen_univ)
  have hfi : Integrable f μ := concentration_integrable_of_fderiv f hf hb
  obtain ⟨hk, hle⟩ := concentration_core f hf Φ hΦ hint
  set m := ∫ y, f y ∂μ with hm
  have hJ : ∀ᵐ x ∂μ, Φ (f x - m) ≤ ∫ y, Φ (f x - f y) ∂μ := by
    filter_upwards [hk.prod_right_ae] with x hx
    have := hΦ.map_integral_le (f := fun y => f x - f y) hΦc.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) ((integrable_const (f x)).sub hfi) hx
    rwa [integral_sub (integrable_const _) hfi, integral_const, probReal_univ, one_smul] at this
  have hJ' : ∀ᵐ x ∂μ, Φ (m - f x) ≤ ∫ y, Φ (f y - f x) ∂μ := by
    filter_upwards [hk.prod_left_ae] with x hx
    have := hΦ.map_integral_le (f := fun y => f y - f x) hΦc.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) (hfi.sub (integrable_const (f x))) hx
    rwa [integral_sub hfi (integrable_const _), integral_const, probReal_univ, one_smul] at this
  have hU : Integrable (fun x => ∫ y, Φ (f x - f y) ∂μ) μ := hk.integral_prod_left
  have hL : Integrable (fun x => ∫ y, Φ (f y - f x) ∂μ) μ := hk.integral_prod_right
  have hlo : ∀ᵐ x ∂μ, 2 * Φ 0 - ∫ y, Φ (f y - f x) ∂μ ≤ Φ (f x - m) := by
    filter_upwards [hJ'] with x hx
    have := concentration_midpoint Φ hΦ (f x - m)
    rw [neg_sub] at this
    linarith
  have hint' : Integrable (fun x => Φ (f x - m)) μ := by
    refine (((integrable_const (2 * Φ 0)).sub hL).abs.add hU.abs).mono'
      (hΦc.comp (hf.continuous.sub continuous_const)).aestronglyMeasurable ?_
    filter_upwards [hJ, hlo] with x h1 h2
    rw [Real.norm_eq_abs]
    exact concentration_abs_le h2 h1
  refine ⟨hint', ?_⟩
  calc ∫ x, Φ (f x - m) ∂μ ≤ ∫ x, ∫ y, Φ (f x - f y) ∂μ ∂μ := integral_mono_ae hint' hU hJ
    _ = ∫ q, Φ (f q.1 - f q.2) ∂(μ.prod μ) := (integral_prod _ hk).symm
    _ ≤ _ := hle

/-- Maurey–Pisier interpolation inequality, root of the Poincaré, concentration and moment
bounds: `E Φ(f - Ef) ≤ E Φ((π/2)⟨∇f(X), Y⟩)` for convex `Φ`, `X, Y` independent standard. -/
theorem pisier_interpolation {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ Set.univ Φ)
    (hint : Integrable (fun q : (ι → ℝ) × (ι → ℝ) => Φ (π / 2 * fderiv ℝ f q.1 q.2))
      ((stdGauss ι).prod (stdGauss ι))) :
    ∫ x, Φ (f x - ∫ y, f y ∂(stdGauss ι)) ∂(stdGauss ι) ≤
      ∫ q, Φ (π / 2 * fderiv ℝ f q.1 q.2) ∂((stdGauss ι).prod (stdGauss ι)) :=
  (concentration_pisier_aux f hf hb Φ hΦ hint).2

/-! ### Poincaré inequality -/

private lemma concentration_clm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (L : (ι → ℝ) →L[ℝ] E) (y : ι → ℝ) :
    L y = ∑ i, y i • L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_smul]
  congr 1
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- Second moment of a linear form: `E (L y)² = ∑ᵢ (L eᵢ)²`. -/
private lemma concentration_sq_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) :
    ∫ y, (L y) ^ 2 ∂(stdGauss ι) = ∑ i, (L (Pi.single i 1)) ^ 2 := by
  set F : (ι → ℝ) →L[ℝ] ℂ := Complex.ofRealCLM.comp L with hF
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg _
  have hb : ∀ x, ‖F x‖ ≤ ‖L‖ * (1 + ‖x‖) ^ 1 := by
    intro x
    rw [hF, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real, pow_one]
    calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
      _ ≤ ‖L‖ * (1 + ‖x‖) := by gcongr; linarith
  have hb' : ∀ x, ‖fderiv ℝ F x‖ ≤ ‖L‖ * (1 + ‖x‖) ^ 1 := by
    intro x
    rw [F.fderiv, pow_one]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hF, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real]
    calc ‖L v‖ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
      _ ≤ ‖L‖ * (1 + ‖x‖) * ‖v‖ := by
          gcongr
          nlinarith [norm_nonneg x]
  have hcoord : ∀ i, Integrable (fun y : ι → ℝ => y i * L y) (stdGauss ι) := by
    intro i
    refine ((concentration_integrable_affine_sq (ι := ι) 0 1).const_mul ‖L‖).mono'
      (by fun_prop : Continuous fun y : ι → ℝ => y i * L y).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    have hy : |y i| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm y i
    rw [norm_mul, Real.norm_eq_abs, zero_add, one_mul]
    calc |y i| * ‖L y‖ ≤ ‖y‖ * (‖L‖ * ‖y‖) :=
          mul_le_mul hy (L.le_opNorm y) (norm_nonneg _) (norm_nonneg _)
      _ = ‖L‖ * ‖y‖ ^ 2 := by ring
  have hS : ∀ i, ∫ y, y i * L y ∂(stdGauss ι) = L (Pi.single i 1) := by
    intro i
    have h := integral_coord_mul_stdGauss (fun y => F y) F.contDiff hb hb' i
    simp only [F.fderiv, integral_const, probReal_univ, one_smul] at h
    have h2 : ∫ x, (x i : ℂ) * F x ∂(stdGauss ι) = ((∫ y, y i * L y ∂(stdGauss ι) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [hF]
    rw [h2] at h
    have h3 : F (Pi.single i 1) = ((L (Pi.single i 1) : ℝ) : ℂ) := by simp [hF]
    rw [h3] at h
    exact_mod_cast h
  have hexp : (fun y : ι → ℝ => (L y) ^ 2) =
      fun y => ∑ i, L (Pi.single i 1) * (y i * L y) := by
    funext y
    conv_lhs => rw [sq]; arg 1; rw [concentration_clm_apply L y]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul]
    ring
  rw [hexp, integral_finsetSum _ fun i _ => (hcoord i).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, hS i, sq]

/-- `(f - c)²` is integrable when `f` has bounded derivative. -/
private lemma concentration_integrable_sq {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) {C : ℝ} (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (c : ℝ) :
    Integrable (fun x => (f x - c) ^ 2) (stdGauss ι) := by
  refine (concentration_integrable_affine_sq (ι := ι) (‖f 0‖ + |c|) C).mono'
    ((hf.continuous.sub continuous_const).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have h1 := concentration_norm_le_affine f hf hb x
  rw [Real.norm_eq_abs] at h1
  have h2 : |f x - c| ≤ ‖f 0‖ + |c| + C * ‖x‖ := by
    have := abs_sub (f x) c
    linarith
  rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h2 2

/-- The gradient square sum is bounded, hence integrable. -/
private lemma concentration_integrable_grad {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) {C : ℝ} (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) :
    Integrable (fun x => ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2) (stdGauss ι) := by
  have hDc : Continuous fun x => fderiv ℝ f x := hf.continuous_fderiv one_ne_zero
  refine Integrable.of_bound (C := ∑ _i : ι, C ^ 2)
    (continuous_finsetSum _ fun i _ =>
      (hDc.clm_apply continuous_const).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ C := by
    calc ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ ‖fderiv ℝ f x‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ :=
          (fderiv ℝ f x).le_opNorm _
      _ ≤ C * 1 := by
          gcongr
          · exact (norm_nonneg _).trans (hb x)
          · exact hb x
          · rw [Pi.norm_single]; simp
      _ = C := mul_one C
  rw [Real.norm_eq_abs] at h1
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

/-- `(Df(X)Y)²` is integrable on the product when `Df` is bounded. -/
private lemma concentration_integrable_deriv_sq {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) {C : ℝ} (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) :
    Integrable (fun q : (ι → ℝ) × (ι → ℝ) => (fderiv ℝ f q.1 q.2) ^ 2)
      ((stdGauss ι).prod (stdGauss ι)) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hb 0)
  have hDc : Continuous fun x => fderiv ℝ f x := hf.continuous_fderiv one_ne_zero
  refine ((concentration_integrable_affine_sq (ι := ι) 0 C).comp_snd (stdGauss ι)).mono'
    (((hDc.comp continuous_fst).clm_apply continuous_snd).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), zero_add, ← sq_abs]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
  calc |fderiv ℝ f q.1 q.2| = ‖fderiv ℝ f q.1 q.2‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ f q.1‖ * ‖q.2‖ := (fderiv ℝ f q.1).le_opNorm _
    _ ≤ C * ‖q.2‖ := by gcongr; exact hb _

/-- Real Gaussian Poincaré inequality with constant `π²/8`. -/
private lemma concentration_poincare_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) {C : ℝ} (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) :
    ∫ x, (f x - ∫ y, f y ∂(stdGauss ι)) ^ 2 ∂(stdGauss ι) ≤
      π ^ 2 / 8 * ∫ x, ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2 ∂(stdGauss ι) := by
  set μ := stdGauss ι with hμ
  have hC : 0 ≤ C := (norm_nonneg _).trans (hb 0)
  have hDc : Continuous fun x => fderiv ℝ f x := hf.continuous_fderiv one_ne_zero
  have hfi : Integrable f μ := concentration_integrable_of_fderiv f hf hb
  set m := ∫ y, f y ∂μ with hm
  have hDq : Integrable (fun q : (ι → ℝ) × (ι → ℝ) => (fderiv ℝ f q.1 q.2) ^ 2) (μ.prod μ) :=
    concentration_integrable_deriv_sq f hf hb
  have hint : Integrable (fun q : (ι → ℝ) × (ι → ℝ) => (π / 2 * fderiv ℝ f q.1 q.2) ^ 2)
      (μ.prod μ) := by
    simp_rw [mul_pow]
    exact hDq.const_mul _
  obtain ⟨_, hle⟩ := concentration_core f hf (fun t => t ^ 2) (even_two.convexOn_pow) hint
  -- right side of the two-copy inequality
  have hR : ∫ q, (π / 2 * fderiv ℝ f q.1 q.2) ^ 2 ∂(μ.prod μ) =
      (π / 2) ^ 2 * ∫ x, ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2 ∂μ := by
    simp_rw [mul_pow]
    rw [integral_const_mul, integral_prod _ hDq]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact concentration_sq_moment (fderiv ℝ f x)
  -- left side of the two-copy inequality
  set g : (ι → ℝ) → ℝ := fun x => f x - m with hg
  have hgi : Integrable g μ := hfi.sub (integrable_const m)
  have hg0 : ∫ x, g x ∂μ = 0 := by
    rw [hg, integral_sub hfi (integrable_const m), integral_const, probReal_univ, one_smul,
      sub_self]
  have hg2 : Integrable (fun x => g x ^ 2) μ := concentration_integrable_sq f hf hb m
  have hfst : ∫ q, g q.1 ^ 2 ∂(μ.prod μ) = ∫ x, g x ^ 2 ∂μ := by
    have := integral_prod_mul (μ := μ) (ν := μ) (fun x => g x ^ 2) (fun _ => (1 : ℝ))
    simpa using this
  have hsnd : ∫ q, g q.2 ^ 2 ∂(μ.prod μ) = ∫ x, g x ^ 2 ∂μ := by
    have := integral_prod_mul (μ := μ) (ν := μ) (fun _ => (1 : ℝ)) (fun x => g x ^ 2)
    simpa using this
  have hcross : ∫ q, g q.1 * g q.2 ∂(μ.prod μ) = 0 := by
    rw [integral_prod_mul (μ := μ) (ν := μ) g g, hg0, zero_mul]
  have hL : ∫ q, (f q.1 - f q.2) ^ 2 ∂(μ.prod μ) = 2 * ∫ x, (f x - m) ^ 2 ∂μ := by
    have he : (fun q : (ι → ℝ) × (ι → ℝ) => (f q.1 - f q.2) ^ 2) =
        fun q => g q.1 ^ 2 + g q.2 ^ 2 - 2 * (g q.1 * g q.2) := by
      funext q; simp only [hg]; ring
    have i1 : Integrable (fun q : (ι → ℝ) × (ι → ℝ) => g q.1 ^ 2) (μ.prod μ) := hg2.comp_fst μ
    have i2 : Integrable (fun q : (ι → ℝ) × (ι → ℝ) => g q.2 ^ 2) (μ.prod μ) := hg2.comp_snd μ
    have i3 : Integrable (fun q : (ι → ℝ) × (ι → ℝ) => g q.1 * g q.2) (μ.prod μ) :=
      hgi.mul_prod hgi
    rw [he, integral_sub (f := fun q => g q.1 ^ 2 + g q.2 ^ 2) (i1.add i2) (i3.const_mul 2),
      integral_add i1 i2, integral_const_mul,
      hfst, hsnd, hcross]
    simp only [hg]
    ring
  have h : ∫ q, (f q.1 - f q.2) ^ 2 ∂(μ.prod μ) ≤
      ∫ q, (π / 2 * fderiv ℝ f q.1 q.2) ^ 2 ∂(μ.prod μ) := hle
  rw [hL, hR] at h
  have : (π / 2) ^ 2 = 2 * (π ^ 2 / 8) := by ring
  rw [this, mul_assoc] at h
  linarith

/-- Gaussian Poincaré inequality, gradient form, constant `π²/8`. -/
theorem poincare_grad {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ 1 f) {C : ℝ} (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) :
    ∫ x, ‖f x - ∫ y, f y ∂(stdGauss ι)‖ ^ 2 ∂(stdGauss ι) ≤
      π ^ 2 / 8 * ∫ x, ∑ i, ‖fderiv ℝ f x (Pi.single i 1)‖ ^ 2 ∂(stdGauss ι) := by
  set μ := stdGauss ι with hμ
  set fr : (ι → ℝ) → ℝ := fun x => (f x).re with hfr_def
  set fi : (ι → ℝ) → ℝ := fun x => (f x).im with hfi_def
  have hfd : ∀ x, HasFDerivAt f (fderiv ℝ f x) x :=
    fun x => ((hf.differentiable one_ne_zero) x).hasFDerivAt
  have hdr : ∀ x, fderiv ℝ fr x = Complex.reCLM.comp (fderiv ℝ f x) :=
    fun x => (Complex.reCLM.hasFDerivAt.comp x (hfd x)).fderiv
  have hdi : ∀ x, fderiv ℝ fi x = Complex.imCLM.comp (fderiv ℝ f x) :=
    fun x => (Complex.imCLM.hasFDerivAt.comp x (hfd x)).fderiv
  have hfr : ContDiff ℝ 1 fr := Complex.reCLM.contDiff.comp hf
  have hfi' : ContDiff ℝ 1 fi := Complex.imCLM.contDiff.comp hf
  have hbr : ∀ x, ‖fderiv ℝ fr x‖ ≤ C := by
    intro x
    rw [hdr]
    calc _ ≤ ‖Complex.reCLM‖ * ‖fderiv ℝ f x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C := by rw [Complex.reCLM_norm, one_mul]; exact hb x
  have hbi : ∀ x, ‖fderiv ℝ fi x‖ ≤ C := by
    intro x
    rw [hdi]
    calc _ ≤ ‖Complex.imCLM‖ * ‖fderiv ℝ f x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C := by rw [Complex.imCLM_norm, one_mul]; exact hb x
  have hfint : Integrable f μ := concentration_integrable_of_fderiv f hf hb
  have hre : ∫ y, fr y ∂μ = (∫ y, f y ∂μ).re := by
    have := Complex.reCLM.integral_comp_comm hfint
    simpa using this
  have him : ∫ y, fi y ∂μ = (∫ y, f y ∂μ).im := by
    have := Complex.imCLM.integral_comp_comm hfint
    simpa using this
  have hpr := concentration_poincare_real fr hfr hbr
  have hpi := concentration_poincare_real fi hfi' hbi
  have hL : (fun x => ‖f x - ∫ y, f y ∂μ‖ ^ 2) =
      fun x => (fr x - ∫ y, fr y ∂μ) ^ 2 + (fi x - ∫ y, fi y ∂μ) ^ 2 := by
    funext x
    rw [hre, him, Complex.sq_norm, Complex.normSq_apply]
    simp only [hfr_def, hfi_def, Complex.sub_re, Complex.sub_im]
    ring
  have hR : (fun x => ∑ i, ‖fderiv ℝ f x (Pi.single i 1)‖ ^ 2) =
      fun x => ∑ i, (fderiv ℝ fr x (Pi.single i 1)) ^ 2 +
        ∑ i, (fderiv ℝ fi x (Pi.single i 1)) ^ 2 := by
    funext x
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdr, hdi, Complex.sq_norm, Complex.normSq_apply]
    simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
    ring
  rw [hL, hR, integral_add (concentration_integrable_sq fr hfr hbr _)
      (concentration_integrable_sq fi hfi' hbi _),
    integral_add (concentration_integrable_grad fr hfr hbr)
      (concentration_integrable_grad fi hfi' hbi)]
  linarith

/-! ### Lipschitz concentration -/

private lemma concentration_toLp_norm_le {ι : Type*} [Fintype ι] (v : ι → ℝ) :
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

/-- A `C¹` function that is `K`-Lipschitz for the Euclidean norm has `|Df(x)v| ≤ K |v|₂`. -/
private lemma concentration_fderiv_apply_le {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (ι → ℝ) → E) (hf1 : ContDiff ℝ 1 f) (K : ℝ≥0)
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

/-- The sup-norm operator bound `‖Df(x)‖ ≤ K √|ι|` for a Euclidean `K`-Lipschitz function. -/
private lemma concentration_fderiv_le {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (ι → ℝ) → E) (hf1 : ContDiff ℝ 1 f) (K : ℝ≥0)
    (hf : LipschitzWith K (fun x : EuclideanSpace ℝ ι => f x.ofLp)) (x : ι → ℝ) :
    ‖fderiv ℝ f x‖ ≤ K * Real.sqrt (Fintype.card ι) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  calc ‖fderiv ℝ f x v‖ ≤ K * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ :=
        concentration_fderiv_apply_le f hf1 K hf x v
    _ ≤ K * (Real.sqrt (Fintype.card ι) * ‖v‖) := by
        gcongr; exact concentration_toLp_norm_le v
    _ = K * Real.sqrt (Fintype.card ι) * ‖v‖ := by ring

/-- The Euclidean gradient of a `K`-Lipschitz `C¹` function has `|∇f(x)|₂² ≤ K²`. -/
private lemma concentration_grad_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (hf1 : ContDiff ℝ 1 f) (K : ℝ≥0)
    (hf : LipschitzWith K (fun x : EuclideanSpace ℝ ι => f x.ofLp)) (x : ι → ℝ) :
    ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2 ≤ (K : ℝ) ^ 2 := by
  set a : ι → ℝ := fun i => fderiv ℝ f x (Pi.single i 1) with ha
  set S := ∑ i, a i ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have h1 : fderiv ℝ f x a = S := by
    rw [concentration_clm_apply (fderiv ℝ f x) a, hS]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, sq]
  have h2 : ‖(WithLp.toLp 2 a : EuclideanSpace ℝ ι)‖ = Real.sqrt S := by
    rw [EuclideanSpace.norm_eq, hS]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.norm_eq_abs, sq_abs]
  have h3 := concentration_fderiv_apply_le f hf1 K hf x a
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

/-- Moment generating function of a linear form: `E exp(t L y) = exp(t² ∑ᵢ (L eᵢ)² / 2)`. -/
private lemma concentration_mgf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    ∫ y, Real.exp (t * L y) ∂(stdGauss ι) =
      Real.exp (t ^ 2 * (∑ i, (L (Pi.single i 1)) ^ 2) / 2) := by
  have hprod : (fun y : ι → ℝ => Real.exp (t * L y)) =
      fun y => ∏ i, Real.exp ((t * L (Pi.single i 1)) * y i) := by
    funext y
    rw [concentration_clm_apply L y, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [smul_eq_mul]
    ring_nf
  have h1 : ∀ c : ℝ, ∫ s, Real.exp (c * s) ∂(gaussianReal 0 1) = Real.exp (c ^ 2 / 2) := by
    intro c
    have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) c
    rw [mgf] at h
    simpa using h
  rw [hprod]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (fun i (s : ℝ) => Real.exp ((t * L (Pi.single i 1)) * s))]
  simp only [h1]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- One-sided Lipschitz concentration with the Maurey–Pisier constant, for `K > 0`. -/
private lemma concentration_tail {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ)
    (hf1 : ContDiff ℝ 1 f) (K : ℝ≥0) (hK : 0 < (K : ℝ))
    (hf : LipschitzWith K (fun x : EuclideanSpace ℝ ι => f x.ofLp)) (u : ℝ) (hu : 0 ≤ u) :
    stdGauss ι {x | u < f x - ∫ y, f y ∂(stdGauss ι)} ≤
      ENNReal.ofReal (Real.exp (-(2 * u ^ 2) / (π ^ 2 * (K : ℝ) ^ 2))) := by
  set μ := stdGauss ι with hμ
  set m := ∫ y, f y ∂μ with hm
  set C := (K : ℝ) * Real.sqrt (Fintype.card ι) with hCdef
  have hC : 0 ≤ C := by positivity
  have hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C := concentration_fderiv_le f hf1 K hf
  have hpi : 0 < π := Real.pi_pos
  set l := 4 * u / (π ^ 2 * (K : ℝ) ^ 2) with hl
  have hl0 : 0 ≤ l := by positivity
  set Φ : ℝ → ℝ := fun t => Real.exp (l * t) with hΦ
  have hΦc : ConvexOn ℝ Set.univ Φ := by
    have := convexOn_exp.comp_linearMap (LinearMap.mulLeft ℝ l)
    simpa [Function.comp_def] using this
  have hDc : Continuous fun x => fderiv ℝ f x := hf1.continuous_fderiv one_ne_zero
  have hint : Integrable (fun q : (ι → ℝ) × (ι → ℝ) => Φ (π / 2 * fderiv ℝ f q.1 q.2))
      (μ.prod μ) := by
    refine ((concentration_integrable_exp_sum (ι := ι) (l * (π / 2) * C)).comp_snd μ).mono'
      (Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul
        ((hDc.comp continuous_fst).clm_apply continuous_snd)))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.mpr ?_
    have h1 : |fderiv ℝ f q.1 q.2| ≤ C * ∑ i, |q.2 i| := by
      calc |fderiv ℝ f q.1 q.2| = ‖fderiv ℝ f q.1 q.2‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ f q.1‖ * ‖q.2‖ := (fderiv ℝ f q.1).le_opNorm _
        _ ≤ C * ∑ i, |q.2 i| := mul_le_mul (hb _) (concentration_norm_le_sum _) (norm_nonneg _) hC
    have h2 := le_abs_self (fderiv ℝ f q.1 q.2)
    have h3 : 0 ≤ l * (π / 2) := by positivity
    calc l * (π / 2 * fderiv ℝ f q.1 q.2) = (l * (π / 2)) * fderiv ℝ f q.1 q.2 := by ring
      _ ≤ (l * (π / 2)) * (C * ∑ i, |q.2 i|) := mul_le_mul_of_nonneg_left (h2.trans h1) h3
      _ = l * (π / 2) * C * ∑ i, |q.2 i| := by ring
  obtain ⟨hI, hle⟩ := concentration_pisier_aux f hf1 hb Φ hΦc hint
  -- the right side is at most `exp(l²π²K²/8)`
  have hR : ∫ q, Φ (π / 2 * fderiv ℝ f q.1 q.2) ∂(μ.prod μ) ≤
      Real.exp ((l * (π / 2)) ^ 2 * (K : ℝ) ^ 2 / 2) := by
    rw [integral_prod _ hint]
    have hin : ∀ x, ∫ y, Φ (π / 2 * fderiv ℝ f x y) ∂μ =
        Real.exp ((l * (π / 2)) ^ 2 * (∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2) / 2) := by
      intro x
      rw [← concentration_mgf (fderiv ℝ f x) (l * (π / 2))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hΦ]
      ring_nf
    have hc : Integrable (fun _ : ι → ℝ => Real.exp ((l * (π / 2)) ^ 2 * (K : ℝ) ^ 2 / 2)) μ :=
      integrable_const _
    calc ∫ x, ∫ y, Φ (π / 2 * fderiv ℝ f (x, y).1 (x, y).2) ∂μ ∂μ
        ≤ ∫ _x, Real.exp ((l * (π / 2)) ^ 2 * (K : ℝ) ^ 2 / 2) ∂μ := by
          refine integral_mono hint.integral_prod_left hc fun x => ?_
          simp only
          rw [hin x]
          refine Real.exp_le_exp.mpr ?_
          have := concentration_grad_sq_le f hf1 K hf x
          have h0 : 0 ≤ (l * (π / 2)) ^ 2 := sq_nonneg _
          nlinarith
      _ = Real.exp ((l * (π / 2)) ^ 2 * (K : ℝ) ^ 2 / 2) := by
          rw [integral_const, probReal_univ, one_smul]
  -- Chernoff
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := fun x => Φ (f x - m))
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) hI (Real.exp (l * u))
  have hsub : {x | u < f x - m} ⊆ {x | Real.exp (l * u) ≤ Φ (f x - m)} := by
    intro x hx
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt hx) hl0)
  have hfin : μ {x | Real.exp (l * u) ≤ Φ (f x - m)} =
      ENNReal.ofReal (μ.real {x | Real.exp (l * u) ≤ Φ (f x - m)}) :=
    (ofReal_measureReal (measure_ne_top _ _)).symm
  refine (measure_mono hsub).trans (hfin.le.trans (ENNReal.ofReal_le_ofReal ?_))
  have hpos : 0 < Real.exp (l * u) := Real.exp_pos _
  have h4 := (hM.trans hle).trans hR
  refine ((le_div_iff₀' hpos).mpr h4).trans (le_of_eq ?_)
  rw [← Real.exp_sub]
  congr 1
  rw [hl]
  field_simp
  ring

/-- Real Lipschitz concentration with the Maurey–Pisier constant. -/
theorem concentration_real {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (hf1 : ContDiff ℝ 1 f)
    (K : ℝ≥0) (hf : LipschitzWith K (fun x : EuclideanSpace ℝ ι => f x.ofLp)) (u : ℝ)
    (hu : 0 ≤ u) :
    stdGauss ι {x | u < |f x - ∫ y, f y ∂(stdGauss ι)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 * u ^ 2) / (π ^ 2 * (K : ℝ) ^ 2))) := by
  rcases eq_or_lt_of_le K.coe_nonneg with hK | hK
  · have h2 : (2 : ℝ) * Real.exp (-(2 * u ^ 2) / (π ^ 2 * (K : ℝ) ^ 2)) = 2 := by
      rw [← hK]; simp
    rw [h2]
    exact prob_le_one.trans (by simp)
  · set m := ∫ y, f y ∂(stdGauss ι) with hm
    set e := Real.exp (-(2 * u ^ 2) / (π ^ 2 * (K : ℝ) ^ 2)) with he
    have h1 := concentration_tail f hf1 K hK hf u hu
    have h2 := concentration_tail (fun x => -f x) hf1.neg K hK hf.neg u hu
    have hneg : ∫ y, -f y ∂(stdGauss ι) = -m := integral_neg _
    rw [hneg] at h2
    have hsub : {x | u < |f x - m|} ⊆
        {x | u < f x - m} ∪ {x | u < -f x - -m} := by
      intro x hx
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
      rcases lt_abs.mp hx with h | h
      · exact Or.inl h
      · right; linarith
    calc stdGauss ι {x | u < |f x - m|}
        ≤ stdGauss ι ({x | u < f x - m} ∪ {x | u < -f x - -m}) := measure_mono hsub
      _ ≤ stdGauss ι {x | u < f x - m} + stdGauss ι {x | u < -f x - -m} := measure_union_le _ _
      _ ≤ ENNReal.ofReal e + ENNReal.ofReal e := add_le_add h1 h2
      _ = ENNReal.ofReal (2 * e) := by
          rw [two_mul, ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]

/-- Complex Lipschitz concentration (real and imaginary parts at `u/√2`). -/
theorem concentration_complex {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ) (hf1 : ContDiff ℝ 1 f)
    (K : ℝ≥0) (hf : LipschitzWith K (fun x : EuclideanSpace ℝ ι => f x.ofLp)) (u : ℝ)
    (hu : 0 ≤ u) :
    stdGauss ι {x | u < ‖f x - ∫ y, f y ∂(stdGauss ι)‖} ≤
      ENNReal.ofReal (4 * Real.exp (-u ^ 2 / (π ^ 2 * (K : ℝ) ^ 2))) := by
  set μ := stdGauss ι with hμ
  set m := ∫ y, f y ∂μ with hm
  set fr : (ι → ℝ) → ℝ := fun x => (f x).re with hfr_def
  set fi : (ι → ℝ) → ℝ := fun x => (f x).im with hfi_def
  have hfr1 : ContDiff ℝ 1 fr := Complex.reCLM.contDiff.comp hf1
  have hfi1 : ContDiff ℝ 1 fi := Complex.imCLM.contDiff.comp hf1
  have hre1 : LipschitzWith 1 Complex.re := LipschitzWith.of_dist_le_mul fun a b => by
    rw [Real.dist_eq, Complex.dist_eq, NNReal.coe_one, one_mul, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  have him1 : LipschitzWith 1 Complex.im := LipschitzWith.of_dist_le_mul fun a b => by
    rw [Real.dist_eq, Complex.dist_eq, NNReal.coe_one, one_mul, ← Complex.sub_im]
    exact Complex.abs_im_le_norm _
  have hfrL : LipschitzWith K (fun x : EuclideanSpace ℝ ι => fr x.ofLp) := by
    have := hre1.comp hf
    rw [one_mul] at this
    exact this
  have hfiL : LipschitzWith K (fun x : EuclideanSpace ℝ ι => fi x.ofLp) := by
    have := him1.comp hf
    rw [one_mul] at this
    exact this
  have hfint : Integrable f μ :=
    concentration_integrable_of_fderiv f hf1 (concentration_fderiv_le f hf1 K hf)
  have hre : ∫ y, fr y ∂μ = m.re := by
    have := Complex.reCLM.integral_comp_comm hfint
    simpa using this
  have him : ∫ y, fi y ∂μ = m.im := by
    have := Complex.imCLM.integral_comp_comm hfint
    simpa using this
  have hv : 0 ≤ u / Real.sqrt 2 := by positivity
  have h1 := concentration_real fr hfr1 K hfrL (u / Real.sqrt 2) hv
  have h2 := concentration_real fi hfi1 K hfiL (u / Real.sqrt 2) hv
  have hsq : (u / Real.sqrt 2) ^ 2 = u ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
  have hexp : 2 * Real.exp (-(2 * (u / Real.sqrt 2) ^ 2) / (π ^ 2 * (K : ℝ) ^ 2)) =
      2 * Real.exp (-u ^ 2 / (π ^ 2 * (K : ℝ) ^ 2)) := by
    rw [hsq]; congr 3; ring
  rw [hexp, hre] at h1
  rw [hexp, him] at h2
  have hsub : {x | u < ‖f x - m‖} ⊆
      {x | u / Real.sqrt 2 < |fr x - m.re|} ∪ {x | u / Real.sqrt 2 < |fi x - m.im|} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    obtain ⟨a1, a2⟩ := hcon
    have b1 : (fr x - m.re) ^ 2 ≤ u ^ 2 / 2 := by
      rw [← hsq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) a1 2
    have b2 : (fi x - m.im) ^ 2 ≤ u ^ 2 / 2 := by
      rw [← hsq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) a2 2
    have b3 : ‖f x - m‖ ^ 2 = (fr x - m.re) ^ 2 + (fi x - m.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [hfr_def, hfi_def, Complex.sub_re, Complex.sub_im]
      ring
    nlinarith [norm_nonneg (f x - m)]
  set e := Real.exp (-u ^ 2 / (π ^ 2 * (K : ℝ) ^ 2)) with he
  have he0 : 0 ≤ 2 * e := by positivity
  calc μ {x | u < ‖f x - m‖}
      ≤ μ ({x | u / Real.sqrt 2 < |fr x - m.re|} ∪ {x | u / Real.sqrt 2 < |fi x - m.im|}) :=
        measure_mono hsub
    _ ≤ μ {x | u / Real.sqrt 2 < |fr x - m.re|} + μ {x | u / Real.sqrt 2 < |fi x - m.im|} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * e) + ENNReal.ofReal (2 * e) := add_le_add h1 h2
    _ = ENNReal.ofReal (4 * e) := by
        rw [← ENNReal.ofReal_add he0 he0]; congr 1; ring

end LSBA
