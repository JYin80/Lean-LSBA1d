import LSBA.Gauss.Concentration

/-!
# Poincaré inequality with polynomial gradients

The Gaussian Poincaré inequality for functions whose gradient grows at most polynomially, extending
the bounded-gradient form; used for the innovation variances in the proof of Lemma 11.2
[uvg:lem:drifts].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The squared Euclidean norm of the coordinate gradient, `Σ_i |∂_i f(x)|²`. -/
def gradSq {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ) (x : ι → ℝ) : ℝ :=
  ∑ i, ‖fderiv ℝ f x (Pi.single i 1)‖ ^ 2

/-! ### Polynomial moments -/

private lemma poincarePoly_one_add_abs_pow_le (m : ℕ) (x : ℝ) :
    (1 + |x|) ^ m ≤ 2 ^ m * (1 + |x| ^ m) := by
  have h2 : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hx : (0 : ℝ) ≤ |x| ^ m := by positivity
  rcases le_total |x| 1 with h | h
  · calc (1 + |x|) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
  · calc (1 + |x|) ^ m ≤ (2 * |x|) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = 2 ^ m * |x| ^ m := by rw [mul_pow]
      _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith

private lemma poincarePoly_integrable_one_add_abs_pow (m : ℕ) :
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
    exact poincarePoly_one_add_abs_pow_le m x

private lemma poincarePoly_one_add_norm_le_prod {ι : Type*} [Fintype ι] (x : ι → ℝ) :
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
private lemma poincarePoly_integrable_poly (ι : Type*) [Fintype ι] (m : ℕ) :
    Integrable (fun x : ι → ℝ => (1 + ‖x‖) ^ m) (stdGauss ι) := by
  have hprod : Integrable (fun x : ι → ℝ => ∏ j, (1 + |x j|) ^ m) (stdGauss ι) :=
    Integrable.fintype_prod (f := fun _ (t : ℝ) => (1 + |t|) ^ m)
      (fun _ => poincarePoly_integrable_one_add_abs_pow m)
  refine hprod.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ι → ℝ => (1 + ‖x‖) ^ m).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity), Finset.prod_pow]
    exact pow_le_pow_left₀ (by positivity) (poincarePoly_one_add_norm_le_prod x) m

/-! ### Growth of `f` and its gradient -/

private lemma poincarePoly_nonneg {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ) {C : ℝ} {k : ℕ}
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k) : 0 ≤ C := by
  have h := (norm_nonneg _).trans (hb 0)
  simpa using h

/-- `‖f x‖ ≤ (‖f 0‖ + C) (1 + ‖x‖)^(k+1)`. -/
private lemma poincarePoly_norm_le {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ 1 f) {C : ℝ} {k : ℕ} (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k)
    (x : ι → ℝ) : ‖f x‖ ≤ (‖f 0‖ + C) * (1 + ‖x‖) ^ (k + 1) := by
  have hC : 0 ≤ C := poincarePoly_nonneg f hb
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

private lemma poincarePoly_norm_partial_le {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ)
    (x : ι → ℝ) (i : ι) : ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ ‖fderiv ℝ f x‖ := by
  have h := (fderiv ℝ f x).le_opNorm (Pi.single i 1)
  have h1 : ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ = 1 := by
    rw [Pi.norm_single]; simp
  rwa [h1, mul_one] at h

private lemma poincarePoly_gradSq_le {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ) (x : ι → ℝ)
    {B : ℝ} (hB : ‖fderiv ℝ f x‖ ≤ B) : gradSq f x ≤ Fintype.card ι * B ^ 2 := by
  unfold gradSq
  calc ∑ i, ‖fderiv ℝ f x (Pi.single i 1)‖ ^ 2 ≤ ∑ _i : ι, B ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _)
          ((poincarePoly_norm_partial_le f x i).trans hB) 2
    _ = Fintype.card ι * B ^ 2 := by simp

private lemma poincarePoly_continuous_gradSq {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ 1 f) : Continuous (gradSq f) := by
  unfold gradSq
  refine continuous_finsetSum _ fun i _ => ?_
  exact (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm).pow 2

private lemma poincarePoly_gradSq_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) (x : ι → ℝ) :
    gradSq f x = ∑ i, ‖fderiv ℝ f x (Pi.single i 1)‖ ^ 2 := by
  unfold gradSq
  congr!

/-! ### Cutoffs -/

/-- A sequence of `C¹` cutoffs with values in `[0, 1]`, compact supports, derivatives bounded by a
common constant, and locally equal to `1` for large index around each point. -/
private lemma poincarePoly_cutoff (ι : Type*) [Fintype ι] :
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

/-! ### Truncation by a cutoff -/

private lemma poincarePoly_gradSq_nonneg {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ)
    (x : ι → ℝ) : 0 ≤ gradSq f x :=
  Finset.sum_nonneg fun _ _ => by positivity

private lemma poincarePoly_norm_fderiv_smul_le {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℂ)
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

/-- Gaussian Poincaré inequality, constant `π²/8`, for `C¹` functions whose derivative grows
at most polynomially. -/
theorem poincare_grad_poly {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ 1 f) {C : ℝ} {k : ℕ} (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    ∫ x, ‖f x - ∫ y, f y ∂(stdGauss ι)‖ ^ 2 ∂(stdGauss ι) ≤
      π ^ 2 / 8 * ∫ x, gradSq f x ∂(stdGauss ι) := by
  obtain ⟨c, L, hL0, hcd, hcs, hc01, hcL, hclim⟩ := poincarePoly_cutoff ι
  set μ := stdGauss ι with hμ
  have hC : 0 ≤ C := poincarePoly_nonneg f hb
  set A : ℝ := ‖f 0‖ + C with hA
  have hA0 : 0 ≤ A := by have := norm_nonneg (f 0); linarith
  have hfgrow := poincarePoly_norm_le f hf hb
  have hfc : Continuous f := hf.continuous
  have hint1 : Integrable f μ :=
    ((poincarePoly_integrable_poly ι (k + 1)).const_mul A).mono' hfc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hfgrow x)
  have hint2 : Integrable (fun x => ‖f x‖ ^ 2) μ := by
    refine ((poincarePoly_integrable_poly ι (2 * (k + 1))).const_mul (A ^ 2)).mono'
      (hfc.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖f x‖ ^ 2 ≤ (A * (1 + ‖x‖) ^ (k + 1)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hfgrow x) 2
      _ = A ^ 2 * (1 + ‖x‖) ^ (2 * (k + 1)) := by rw [mul_pow, ← pow_mul]; ring_nf
  -- truncations
  set F : ℕ → (ι → ℝ) → ℂ := fun n y => c n y • f y with hF
  have hFd : ∀ n, ContDiff ℝ 1 (F n) := fun n => (hcd n).smul hf
  have hFnorm : ∀ n x, ‖F n x‖ ≤ ‖f x‖ := fun n x => by
    simp only [hF]
    rw [norm_smul, Real.norm_of_nonneg (hc01 n x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hc01 n x).2
  have hFint : ∀ n, Integrable (F n) μ := fun n =>
    hint1.norm.mono' (hFd n).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (hFnorm n))
  have hFsupp : ∀ n, HasCompactSupport (F n) := fun n => (hcs n).smul_right
  have hPoin : ∀ n, ∫ x, ‖F n x - ∫ y, F n y ∂μ‖ ^ 2 ∂μ ≤
      π ^ 2 / 8 * ∫ x, gradSq (F n) x ∂μ := fun n => by
    obtain ⟨B, hB⟩ := ((hFd n).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
      ((hFsupp n).fderiv ℝ)
    have := poincare_grad (F n) (hFd n) hB
    simpa only [poincarePoly_gradSq_eq] using this
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
  have hmbound : ∀ n, ‖∫ y, F n y ∂μ‖ ≤ S := fun n =>
    norm_integral_le_of_norm_le hint1.norm (Filter.Eventually.of_forall (hFnorm n))
  -- left side
  have hLim : Filter.Tendsto (fun n => ∫ x, ‖F n x - ∫ y, F n y ∂μ‖ ^ 2 ∂μ) Filter.atTop
      (nhds (∫ x, ‖f x - ∫ y, f y ∂μ‖ ^ 2 ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => 2 * ‖f x‖ ^ 2 + 2 * S ^ 2)
      (fun n => (((hFd n).continuous.sub continuous_const).norm.pow 2).aestronglyMeasurable)
      ((hint2.const_mul 2).add (integrable_const _))
      (fun n => Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => ?_)
    · rw [Real.norm_of_nonneg (by positivity)]
      have ha := hFnorm n x
      have hm := hmbound n
      have h0 := norm_nonneg (F n x)
      have h1 := norm_nonneg (∫ y, F n y ∂μ)
      have h2 : ‖F n x - ∫ y, F n y ∂μ‖ ≤ ‖F n x‖ + ‖∫ y, F n y ∂μ‖ := norm_sub_le _ _
      have h3 : ‖F n x - ∫ y, F n y ∂μ‖ ^ 2 ≤ (‖F n x‖ + ‖∫ y, F n y ∂μ‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
      have h4 : ‖F n x‖ ^ 2 ≤ ‖f x‖ ^ 2 := pow_le_pow_left₀ h0 ha 2
      have h5 : ‖∫ y, F n y ∂μ‖ ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ h1 hm 2
      nlinarith [sq_nonneg (‖F n x‖ - ‖∫ y, F n y ∂μ‖)]
    · have h1 : Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x)) :=
        tendsto_const_nhds.congr' ((hFlim x).mono fun n hn => hn.symm)
      exact ((h1.sub hmean).norm).pow 2
  -- right side
  have hRim : Filter.Tendsto (fun n => ∫ x, gradSq (F n) x ∂μ) Filter.atTop
      (nhds (∫ x, gradSq f x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => (Fintype.card ι : ℝ) * (C + L * A) ^ 2 * (1 + ‖x‖) ^ (2 * (k + 1)))
      (fun n => (poincarePoly_continuous_gradSq (F n) (hFd n)).aestronglyMeasurable)
      ((poincarePoly_integrable_poly ι (2 * (k + 1))).const_mul _)
      (fun n => Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => ?_)
    · rw [Real.norm_of_nonneg (poincarePoly_gradSq_nonneg _ _)]
      have hx1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
      have hpk : (1 + ‖x‖) ^ k ≤ (1 + ‖x‖) ^ (k + 1) := pow_le_pow_right₀ hx1 (Nat.le_succ k)
      have hD := poincarePoly_norm_fderiv_smul_le f hf (c n) (hcd n) (fun y => (hc01 n y).1)
        (fun y => (hc01 n y).2) x
      have hB : ‖fderiv ℝ (F n) x‖ ≤ (C + L * A) * (1 + ‖x‖) ^ (k + 1) := by
        refine hD.trans ?_
        have h1 : ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ (k + 1) :=
          (hb x).trans (mul_le_mul_of_nonneg_left hpk hC)
        have h2 : ‖fderiv ℝ (c n) x‖ * ‖f x‖ ≤ L * (A * (1 + ‖x‖) ^ (k + 1)) :=
          mul_le_mul (hcL n x) (hfgrow x) (norm_nonneg _) hL0
        nlinarith
      calc gradSq (F n) x ≤ Fintype.card ι * ((C + L * A) * (1 + ‖x‖) ^ (k + 1)) ^ 2 :=
            poincarePoly_gradSq_le (F n) x hB
        _ = _ := by rw [mul_pow, ← pow_mul]; ring_nf
    · have h1 : ∀ᶠ n in Filter.atTop, gradSq (F n) x = gradSq f x :=
        (hFlimD x).mono fun n hn => by unfold gradSq; rw [hn]
      exact tendsto_const_nhds.congr' (h1.mono fun n hn => hn.symm)
  exact le_of_tendsto_of_tendsto' hLim (hRim.const_mul _) hPoin

end LSBA
