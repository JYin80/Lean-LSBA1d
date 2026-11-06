import LSBA.Gauss.Haar
import LSBA.Gauss.Sphere
import LSBA.Gauss.SphereNet
import LSBA.Gauss.StdGauss

/-!
# Overlap of a Haar-rotated subspace with a fixed projection

For orthogonal projections `P`, `Q₀` on `ℂ^W` and a Haar unitary `O`, the operator norm of
`Q₀ (O P O*)` is at most `C √((Tr P + Tr Q₀ + s)/W)` except with probability `C e^{-c s}`. The same
bound holds for a projection-valued map on the GUE sample space that is equivariant under common
conjugation of the blocks. This is the transversality estimate (9.56) [us:eq:Haar].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Gaussian mass of a coordinate set -/

/-- The standard Gaussian density times `exp (c x²)` is `(2π)^{-1/2} exp (-(1/2 - c) x²)`. -/
private lemma haarSubspace_pdf_mul_exp (c x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (c * x ^ 2) =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2 - c) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- `exp (c t²)` is integrable against the standard Gaussian for `c < 1/2`. -/
private lemma haarSubspace_integrable_exp_sq {c : ℝ} (hc : c < 1 / 2) :
    Integrable (fun t : ℝ => Real.exp (c * t ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)]
  have h := (integrable_exp_neg_mul_sq (b := 1 / 2 - c) (by linarith)).const_mul
    ((Real.sqrt (2 * π))⁻¹)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x), smul_eq_mul]
  exact (haarSubspace_pdf_mul_exp c x).symm

/-- `E exp (c t²) = (1 - 2c)^{-1/2}` for the standard Gaussian and `c < 1/2`. -/
private lemma haarSubspace_integral_exp_sq {c : ℝ} (hc : c < 1 / 2) :
    ∫ t : ℝ, Real.exp (c * t ^ 2) ∂(gaussianReal 0 1) = Real.sqrt ((1 - 2 * c)⁻¹) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul, haarSubspace_pdf_mul_exp]
  rw [integral_const_mul, integral_gaussian]
  have h1 : 0 < 1 - 2 * c := by linarith
  have h4 : π / (1 / 2 - c) = (2 * π) * (1 - 2 * c)⁻¹ := by
    field_simp
  have : Real.sqrt (2 * π) ≠ 0 := by positivity
  have h5 : Real.sqrt (2 * π * (1 - 2 * c)⁻¹) =
      Real.sqrt (2 * π) * Real.sqrt ((1 - 2 * c)⁻¹) :=
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π) ((1 - 2 * c)⁻¹)
  rw [h4, h5, ← mul_assoc, inv_mul_cancel₀ this, one_mul]

/-- The map from `2W` real coordinates to a complex vector is continuous. -/
private lemma haarSubspace_continuous_cplxVec (W : ℕ) : Continuous (cplxVec W) := by
  have : cplxVec W = fun x i => (x (i, 0) : ℂ) + (x (i, 1) : ℂ) * Complex.I := by
    funext x i
    apply Complex.ext <;> simp [cplxVec]
  rw [this]
  fun_prop

private lemma haarSubspace_measurable_normalize_cplxVec (W : ℕ) :
    Measurable (fun x : Fin W × Fin 2 → ℝ => normalize (cplxVec W x)) := by
  have h : Measurable (normalize : (Fin W → ℂ) → (Fin W → ℂ)) := by
    unfold normalize
    fun_prop
  exact h.comp (haarSubspace_continuous_cplxVec W).measurable

/-- `|normalize(y)ᵢ|² = |yᵢ|² / ∑ₖ |yₖ|²`, also for `y = 0`. -/
private lemma haarSubspace_norm_normalize_sq {W : ℕ} (y : Fin W → ℂ) (i : Fin W) :
    ‖normalize y i‖ ^ 2 = ‖y i‖ ^ 2 / ∑ k, ‖y k‖ ^ 2 := by
  have hN : 0 ≤ ∑ k, ‖y k‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
  simp only [normalize, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, inv_pow, sq_abs, Real.sq_sqrt hN]
  rw [div_eq_inv_mul]

/-- Chernoff bound for the mass of the coordinates in `S` of a normalized standard complex
Gaussian vector: for `0 ≤ θ ≤ 1`, the mass is at least `θ` with probability at most
`2^{|S|} e^{-θ (W - |S|) / 4}`. -/
private lemma haarSubspace_gauss_tail {W : ℕ} (S : Finset (Fin W)) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    stdGauss (Fin W × Fin 2) {x | θ ≤ ∑ i ∈ S, ‖normalize (cplxVec W x) i‖ ^ 2} ≤
      ENNReal.ofReal ((2 : ℝ) ^ S.card * Real.exp (-θ / 4) ^ (W - S.card)) := by
  set κ : Fin W → ℝ := fun i => (if i ∈ S then 1 / 4 else 0) - θ / 4 with hκ
  have hκlt : ∀ i, κ i < 1 / 2 := by
    intro i
    simp only [hκ]
    split_ifs <;> linarith
  set F : (Fin W × Fin 2 → ℝ) → ℝ := fun x => ∏ p, Real.exp (κ p.1 * x p ^ 2) with hF
  have hFsum : ∀ x, F x = Real.exp ((1 / 4) * ∑ i ∈ S, ‖cplxVec W x i‖ ^ 2 -
      (θ / 4) * ∑ i, ‖cplxVec W x i‖ ^ 2) := by
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
      (μ := fun _ => gaussianReal 0 1) (fun p => haarSubspace_integrable_exp_sq (hκlt p.1))
  have hsub : {x | θ ≤ ∑ i ∈ S, ‖normalize (cplxVec W x) i‖ ^ 2} ⊆
      {x | 1 ≤ ENNReal.ofReal (F x)} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    simp_rw [haarSubspace_norm_normalize_sq] at hx
    rw [← Finset.sum_div] at hx
    have hN : 0 ≤ ∑ i, ‖cplxVec W x i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hS : θ * ∑ i, ‖cplxVec W x i‖ ^ 2 ≤ ∑ i ∈ S, ‖cplxVec W x i‖ ^ 2 := by
      rcases hN.lt_or_eq with h | h
      · rwa [le_div_iff₀ h] at hx
      · rw [← h, mul_zero]
        exact Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [ENNReal.one_le_ofReal, hFsum]
    exact Real.one_le_exp (by linarith)
  have hb : ∀ i, Real.sqrt ((1 - 2 * κ i)⁻¹) * Real.sqrt ((1 - 2 * κ i)⁻¹) ≤
      if i ∈ S then 2 else Real.exp (-θ / 4) := by
    intro i
    have hpos : 0 < 1 - 2 * κ i := by linarith [hκlt i]
    rw [Real.mul_self_sqrt (inv_nonneg.mpr hpos.le)]
    by_cases hi : i ∈ S
    · simp only [hκ, hi, ite_true]
      rw [inv_le_comm₀ (by simp only [hκ, hi, ite_true] at hpos; exact hpos) (by norm_num)]
      linarith
    · simp only [hκ, hi, ite_false]
      have h1 : (1 - 2 * (0 - θ / 4))⁻¹ ≤ 1 - θ / 4 := by
        rw [inv_le_iff_one_le_mul₀ (by linarith)]
        nlinarith
      exact h1.trans (by linarith [Real.add_one_le_exp (-θ / 4)])
  have hval : ∫ x, F x ∂(stdGauss (Fin W × Fin 2)) ≤
      (2 : ℝ) ^ S.card * Real.exp (-θ / 4) ^ (W - S.card) := by
    change ∫ x : Fin W × Fin 2 → ℝ, (∏ p : Fin W × Fin 2, Real.exp (κ p.1 * x p ^ 2))
      ∂(Measure.pi fun _ => gaussianReal 0 1) ≤ _
    rw [integral_fintype_prod_eq_prod
        (fun (p : Fin W × Fin 2) (t : ℝ) => Real.exp (κ p.1 * t ^ 2)),
      Finset.prod_congr rfl (fun p _ => haarSubspace_integral_exp_sq (hκlt p.1)),
      Fintype.prod_prod_type]
    simp only [Fin.prod_univ_two]
    calc ∏ i, (Real.sqrt ((1 - 2 * κ i)⁻¹) * Real.sqrt ((1 - 2 * κ i)⁻¹))
        ≤ ∏ i : Fin W, (if i ∈ S then (2 : ℝ) else Real.exp (-θ / 4)) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hb i)
      _ = _ := by
          rw [← Finset.prod_mul_prod_compl S]
          rw [Finset.prod_congr rfl (fun i hi => ite_eq_left hi),
            Finset.prod_congr rfl (fun i hi => ite_eq_right (Finset.mem_compl.mp hi)),
            Finset.prod_const, Finset.prod_const, Finset.card_compl, Fintype.card_fin]
  calc stdGauss (Fin W × Fin 2) {x | θ ≤ ∑ i ∈ S, ‖normalize (cplxVec W x) i‖ ^ 2}
      ≤ 1 * stdGauss (Fin W × Fin 2) {x | 1 ≤ ENNReal.ofReal (F x)} := by
        rw [one_mul]
        exact measure_mono hsub
    _ ≤ ∫⁻ x, ENNReal.ofReal (F x) ∂(stdGauss (Fin W × Fin 2)) :=
        mul_meas_ge_le_lintegral₀
          (ENNReal.measurable_ofReal.comp_aemeasurable hI.aestronglyMeasurable.aemeasurable) 1
    _ = ENNReal.ofReal (∫ x, F x ∂(stdGauss (Fin W × Fin 2))) :=
        (ofReal_integral_eq_lintegral_ofReal hI
          (Filter.Eventually.of_forall fun x => by simp only [hF, Pi.zero_apply]; positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hval

/-- The mass of the coordinates in `S` of a Haar column `O v`, `v` a unit vector, is at least `θ`
with probability at most `2^{|S|} e^{-θ (W - |S|) / 4}`, for `0 ≤ θ ≤ 1`. -/
private lemma haarSubspace_haar_vec_tail {W : ℕ} (v : Fin W → ℂ) (hv : ∑ i, ‖v i‖ ^ 2 = 1)
    (S : Finset (Fin W)) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    haarU W {O | θ ≤ ∑ i ∈ S, ‖((O : Matrix (Fin W) (Fin W) ℂ) *ᵥ v) i‖ ^ 2} ≤
      ENNReal.ofReal ((2 : ℝ) ^ S.card * Real.exp (-θ / 4) ^ (W - S.card)) := by
  have hB : MeasurableSet {w : Fin W → ℂ | θ ≤ ∑ i ∈ S, ‖w i‖ ^ 2} :=
    measurableSet_le measurable_const (by fun_prop)
  have hmv : Measurable (fun U : Matrix.unitaryGroup (Fin W) ℂ =>
      (U : Matrix (Fin W) (Fin W) ℂ).mulVec v) :=
    (Continuous.matrix_mulVec continuous_subtype_val continuous_const).measurable
  have h := congrArg (fun μ : Measure (Fin W → ℂ) => μ {w | θ ≤ ∑ i ∈ S, ‖w i‖ ^ 2})
    (map_haarU_mulVec W v hv)
  rw [Measure.map_apply hmv hB,
    Measure.map_apply (haarSubspace_measurable_normalize_cplxVec W) hB] at h
  change haarU W _ ≤ _
  exact h.le.trans (haarSubspace_gauss_tail S hθ0 hθ1)

/-! ### Coordinate projections and nets -/

/-- The diagonal `0`-`1` matrix of the coordinate projection onto `T`. -/
private def haarSubspace_diag {W : ℕ} (T : Finset (Fin W)) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.diagonal fun i => if i ∈ T then 1 else 0

private lemma haarSubspace_diag_mulVec {W : ℕ} (T : Finset (Fin W)) (w : Fin W → ℂ) (i : Fin W) :
    (haarSubspace_diag T *ᵥ w) i = if i ∈ T then w i else 0 := by
  simp only [haarSubspace_diag, Matrix.mulVec_diagonal]
  split_ifs <;> simp

private lemma haarSubspace_sum_diag_mulVec {W : ℕ} (T : Finset (Fin W)) (w : Fin W → ℂ) :
    ∑ i, ‖(haarSubspace_diag T *ᵥ w) i‖ ^ 2 = ∑ i ∈ T, ‖w i‖ ^ 2 := by
  have h : ∀ i, ‖(haarSubspace_diag T *ᵥ w) i‖ ^ 2 = if i ∈ T then ‖w i‖ ^ 2 else 0 := by
    intro i
    rw [haarSubspace_diag_mulVec]
    split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

private lemma haarSubspace_norm_diag_le {W : ℕ} (T : Finset (Fin W)) :
    ‖haarSubspace_diag T‖ ≤ 1 := by
  rw [haarSubspace_diag, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  split_ifs <;> simp

/-- Extension by zero of a vector indexed by the coordinates of `T`. -/
private def haarSubspace_ext {W : ℕ} (T : Finset (Fin W)) (y : T → ℂ) : Fin W → ℂ :=
  fun i => if h : i ∈ T then y ⟨i, h⟩ else 0

private lemma haarSubspace_sum_ext {W : ℕ} {G : Type*} [AddCommMonoid G] (T : Finset (Fin W))
    (g : Fin W → G) (h0 : ∀ j, j ∉ T → g j = 0) : ∑ j, g j = ∑ t : T, g t.1 := by
  rw [Finset.sum_coe_sort T g]
  exact (Finset.sum_subset (Finset.subset_univ T) (fun j _ hj => h0 j hj)).symm

private lemma haarSubspace_sum_norm_ext {W : ℕ} (T : Finset (Fin W)) (y : T → ℂ) :
    ∑ i, ‖haarSubspace_ext T y i‖ ^ 2 = ∑ t : T, ‖y t‖ ^ 2 := by
  rw [haarSubspace_sum_ext T (fun i => ‖haarSubspace_ext T y i‖ ^ 2)
    (fun j hj => by simp [haarSubspace_ext, hj])]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [haarSubspace_ext]

private lemma haarSubspace_diag_mulVec_eq_ext {W : ℕ} (T : Finset (Fin W)) (x : Fin W → ℂ) :
    haarSubspace_diag T *ᵥ x = haarSubspace_ext T (fun t => x t.1) := by
  funext i
  rw [haarSubspace_diag_mulVec]
  by_cases hi : i ∈ T <;> simp [haarSubspace_ext, hi]

private lemma haarSubspace_submatrix_mulVec {W : ℕ} (T : Finset (Fin W))
    (M : Matrix (Fin W) (Fin W) ℂ) (y : T → ℂ) :
    (M.submatrix id (Subtype.val : T → Fin W)) *ᵥ y = M *ᵥ haarSubspace_ext T y := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]
  have h := haarSubspace_sum_ext T (fun j => M i j * haarSubspace_ext T y j) (fun j hj => by
    simp [haarSubspace_ext, hj])
  rw [h]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [haarSubspace_ext]

/-- Net bound for a vector of norm at most `1`, from a `1/2`-net: if `‖A v‖ ≤ β` on the net, then
`‖A y‖ ≤ 2 β` for every `y` with `‖y‖ ≤ 1`. -/
private lemma haarSubspace_net_bound {k m : Type*} [Fintype k] [Fintype m] (A : Matrix k m ℂ)
    {N : Finset (m → ℂ)}
    (hN : ∀ y : m → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 → ∃ v ∈ N, ∑ i, ‖y i - v i‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : ∀ v ∈ N, Real.sqrt (∑ a, ‖(A *ᵥ v) a‖ ^ 2) ≤ β)
    (y : m → ℂ) (hy : ∑ i, ‖y i‖ ^ 2 ≤ 1) :
    Real.sqrt (∑ a, ‖(A *ᵥ y) a‖ ^ 2) ≤ 2 * β := by
  have hσ0 : 0 ≤ ∑ i, ‖y i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hσ0.lt_or_eq with hσ | hσ
  · set c : ℝ := Real.sqrt (∑ i, ‖y i‖ ^ 2) with hc_def
    have hc : 0 < c := Real.sqrt_pos.2 hσ
    have hc1 : c ≤ 1 := by
      rw [hc_def, Real.sqrt_le_one]
      exact hy
    have hcc : c ^ 2 = ∑ i, ‖y i‖ ^ 2 := Real.sq_sqrt hσ0
    set z : m → ℂ := ((c⁻¹ : ℝ) : ℂ) • y with hz
    have hz1 : ∑ i, ‖z i‖ ^ 2 = 1 := by
      simp only [hz, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        mul_pow, sq_abs]
      rw [← Finset.mul_sum, ← hcc, inv_pow]
      exact inv_mul_cancel₀ (by positivity)
    have h1 := sphere_net_upper A (δ := 1 / 2) (β := β) (by norm_num) (by norm_num) hN hβ z hz1
    have hyz : y = (c : ℂ) • z := by
      simp only [hz, smul_smul]
      have : (c : ℂ) * ((c⁻¹ : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ hc.ne']
        simp
      rw [this, one_smul]
    have h2 : ∑ a, ‖(A *ᵥ y) a‖ ^ 2 = c ^ 2 * ∑ a, ‖(A *ᵥ z) a‖ ^ 2 := by
      rw [hyz, Matrix.mulVec_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        mul_pow, sq_abs]
    rw [h2, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
    calc c * Real.sqrt (∑ a, ‖(A *ᵥ z) a‖ ^ 2) ≤ 1 * Real.sqrt (∑ a, ‖(A *ᵥ z) a‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hc1 (Real.sqrt_nonneg _)
      _ ≤ β / (1 - 1 / 2) := by rw [one_mul]; exact h1
      _ = 2 * β := by ring
  · have hy0 : y = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ‖y k‖)).mp hσ.symm i
        (Finset.mem_univ i)
      simpa using this
    rw [hy0, Matrix.mulVec_zero]
    simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, Real.sqrt_zero]
    linarith

/-- The operator norm of a square matrix is at most `B` if `‖M x‖ ≤ B` on unit vectors. -/
private lemma haarSubspace_opNorm_le {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ x : Fin W → ℂ, ∑ i, ‖x i‖ ^ 2 = 1 → Real.sqrt (∑ a, ‖(M *ᵥ x) a‖ ^ 2) ≤ B) :
    ‖M‖ ≤ B := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hB (fun x hx => ?_)
  have hx' : ∑ i, ‖x.ofLp i‖ ^ 2 = 1 := by
    have h2 := congrArg (fun r => r ^ 2) hx
    simp only [one_pow] at h2
    rwa [EuclideanSpace.norm_sq_eq] at h2
  have := h x.ofLp hx'
  rw [EuclideanSpace.norm_eq]
  simpa [Matrix.ofLp_toEuclideanCLM] using this

/-- Overlap of coordinate projections `D_S O D_T` with a Haar unitary `O`: a `1/2`-net of the unit
sphere of `ℂ^T` and the one-vector bound give `‖D_S O D_T‖ ≤ 2 √θ` except with probability at most
`25^{|T|} 2^{|S|} e^{-θ (W - |S|) / 4}`, for `0 ≤ θ ≤ 1`. -/
private lemma haarSubspace_coord_tail {W : ℕ} (S T : Finset (Fin W)) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    haarU W {O | 2 * Real.sqrt θ <
        ‖haarSubspace_diag S * (O : Matrix (Fin W) (Fin W) ℂ) * haarSubspace_diag T‖} ≤
      ENNReal.ofReal ((25 : ℝ) ^ T.card *
        ((2 : ℝ) ^ S.card * Real.exp (-θ / 4) ^ (W - S.card))) := by
  obtain ⟨N, hNcard, hNunit, hNcover⟩ := exists_sphere_net T (δ := 1 / 2) (by norm_num)
  set b : ℝ := (2 : ℝ) ^ S.card * Real.exp (-θ / 4) ^ (W - S.card) with hb
  have hb0 : 0 ≤ b := by positivity
  have hsub : {O : Matrix.unitaryGroup (Fin W) ℂ | 2 * Real.sqrt θ <
        ‖haarSubspace_diag S * (O : Matrix (Fin W) (Fin W) ℂ) * haarSubspace_diag T‖} ⊆
      ⋃ v ∈ N, {O : Matrix.unitaryGroup (Fin W) ℂ |
        θ ≤ ∑ i ∈ S, ‖((O : Matrix (Fin W) (Fin W) ℂ) *ᵥ haarSubspace_ext T v) i‖ ^ 2} := by
    intro O hO
    by_contra hcon
    simp only [Set.mem_iUnion, not_exists, Set.mem_ofPred_eq, not_le] at hcon
    apply absurd hO
    rw [Set.mem_ofPred_eq, not_lt]
    refine haarSubspace_opNorm_le _ (by positivity) (fun x hx => ?_)
    have hM : (haarSubspace_diag S * (O : Matrix (Fin W) (Fin W) ℂ) * haarSubspace_diag T) *ᵥ x =
        ((haarSubspace_diag S * (O : Matrix (Fin W) (Fin W) ℂ)).submatrix id
          (Subtype.val : T → Fin W)) *ᵥ (fun t : T => x t.1) := by
      rw [← Matrix.mulVec_mulVec, haarSubspace_diag_mulVec_eq_ext, haarSubspace_submatrix_mulVec]
    rw [hM]
    refine haarSubspace_net_bound _ hNcover (by positivity) (fun v hv => ?_) _ ?_
    · rw [haarSubspace_submatrix_mulVec, ← Matrix.mulVec_mulVec, haarSubspace_sum_diag_mulVec]
      exact Real.sqrt_le_sqrt (hcon v hv).le
    · rw [← hx]
      change ∑ t : T, ‖x t.1‖ ^ 2 ≤ _
      rw [Finset.sum_coe_sort T (fun i => ‖x i‖ ^ 2)]
      exact Finset.sum_le_univ_sum_of_nonneg fun i => sq_nonneg _
  have hcard : (N.card : ℝ) ≤ (25 : ℝ) ^ T.card := by
    have h := hNcard
    rw [Fintype.card_coe, show (1 + 2 / (1 / 2 : ℝ)) = 5 by norm_num, pow_mul] at h
    norm_num at h
    exact h
  calc haarU W {O | 2 * Real.sqrt θ <
        ‖haarSubspace_diag S * (O : Matrix (Fin W) (Fin W) ℂ) * haarSubspace_diag T‖}
      ≤ haarU W (⋃ v ∈ N, {O : Matrix.unitaryGroup (Fin W) ℂ |
        θ ≤ ∑ i ∈ S, ‖((O : Matrix (Fin W) (Fin W) ℂ) *ᵥ haarSubspace_ext T v) i‖ ^ 2}) :=
        measure_mono hsub
    _ ≤ ∑ v ∈ N, haarU W {O : Matrix.unitaryGroup (Fin W) ℂ |
        θ ≤ ∑ i ∈ S, ‖((O : Matrix (Fin W) (Fin W) ℂ) *ᵥ haarSubspace_ext T v) i‖ ^ 2} :=
        measure_biUnion_finset_le N _
    _ ≤ ∑ v ∈ N, ENNReal.ofReal b := Finset.sum_le_sum fun v hv =>
        haarSubspace_haar_vec_tail (haarSubspace_ext T v)
          (by rw [haarSubspace_sum_norm_ext]; exact hNunit v hv) S hθ0 hθ1
    _ = (N.card : ℝ≥0∞) * ENNReal.ofReal b := by simp
    _ = ENNReal.ofReal (N.card * b) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hb0)

/-- Spectral form of an orthogonal projection: `P = U D_T U*` for a unitary `U` and a coordinate
set `T` with `|T| = Tr P`. -/
private lemma haarSubspace_proj_diag {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ} (hH : P.IsHermitian)
    (hP : P * P = P) :
    ∃ (U : Matrix.unitaryGroup (Fin W) ℂ) (T : Finset (Fin W)),
      P = (U : Matrix (Fin W) (Fin W) ℂ) * haarSubspace_diag T *
        star (U : Matrix (Fin W) (Fin W) ℂ) ∧ (Matrix.trace P).re = T.card := by
  set U := hH.eigenvectorUnitary with hU
  set D : Matrix (Fin W) (Fin W) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) with hD
  have hspec : P = (U : Matrix (Fin W) (Fin W) ℂ) * D * star (U : Matrix (Fin W) (Fin W) ℂ) := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hU1 : star (U : Matrix (Fin W) (Fin W) ℂ) * (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  have hU2 : (U : Matrix (Fin W) (Fin W) ℂ) * star (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Unitary.coe_mul_star_self U
  have hDP : D = star (U : Matrix (Fin W) (Fin W) ℂ) * P * (U : Matrix (Fin W) (Fin W) ℂ) := by
    conv_rhs => rw [hspec]
    calc D = (star (U : Matrix (Fin W) (Fin W) ℂ) * (U : Matrix (Fin W) (Fin W) ℂ)) * D *
          (star (U : Matrix (Fin W) (Fin W) ℂ) * (U : Matrix (Fin W) (Fin W) ℂ)) := by
          rw [hU1]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hDD : D * D = D := by
    calc D * D = (star (U : Matrix (Fin W) (Fin W) ℂ) * P * (U : Matrix (Fin W) (Fin W) ℂ)) *
          (star (U : Matrix (Fin W) (Fin W) ℂ) * P * (U : Matrix (Fin W) (Fin W) ℂ)) := by
          rw [← hDP]
      _ = star (U : Matrix (Fin W) (Fin W) ℂ) * P *
          ((U : Matrix (Fin W) (Fin W) ℂ) * star (U : Matrix (Fin W) (Fin W) ℂ)) * P *
            (U : Matrix (Fin W) (Fin W) ℂ) := by simp only [Matrix.mul_assoc]
      _ = star (U : Matrix (Fin W) (Fin W) ℂ) * (P * P) * (U : Matrix (Fin W) (Fin W) ℂ) := by
          rw [hU2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = D := by rw [hP, hDP]
  have hev : ∀ i, hH.eigenvalues i * hH.eigenvalues i = hH.eigenvalues i := by
    intro i
    have h := congrFun (congrFun hDD i) i
    simp only [hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Function.comp_apply] at h
    exact_mod_cast h
  set T : Finset (Fin W) := Finset.univ.filter fun i => hH.eigenvalues i = 1 with hT
  have hev' : ∀ i, hH.eigenvalues i = if i ∈ T then 1 else 0 := by
    intro i
    by_cases h1 : hH.eigenvalues i = 1
    · simp [hT, h1]
    · have h0 : hH.eigenvalues i = 0 := by
        by_contra h0
        exact h1 (mul_left_cancel₀ h0 ((hev i).trans (mul_one _).symm))
      simp [hT, h0]
  have hDT : D = haarSubspace_diag T := by
    simp only [hD, haarSubspace_diag]
    congr 1
    funext i
    simp only [Function.comp_apply, hev' i]
    split_ifs <;> simp
  refine ⟨U, T, by rw [← hDT]; exact hspec, ?_⟩
  rw [hH.trace_eq_sum_eigenvalues, Complex.re_sum]
  simp only [hev' _]
  simp [apply_ite Complex.re]

/-- The arithmetic of the union bound with `C = 20` and `c = 1`: if `400 (m + r + s) < W`, then
`25^m 2^r e^{-θ (W - r) / 4} ≤ 20 e^{-s}` for `θ = 100 (m + r + s) / W`. -/
private lemma haarSubspace_numeric {W m r : ℕ} {s : ℝ} (hs : 0 ≤ s) (hW : 1 ≤ W)
    (hlt : 400 * ((m : ℝ) + r + s) < W) :
    (25 : ℝ) ^ m * ((2 : ℝ) ^ r * Real.exp (-(100 * ((m : ℝ) + r + s) / W) / 4) ^ (W - r)) ≤
      20 * Real.exp (-1 * s) := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  set x : ℝ := (m : ℝ) + r + s with hx
  have hx0 : 0 ≤ x := by positivity
  have hrW : (r : ℝ) ≤ W / 400 := by nlinarith
  have hrW' : r ≤ W := by
    have : (r : ℝ) ≤ W := by linarith
    exact_mod_cast this
  have hcast : ((W - r : ℕ) : ℝ) = W - r := by rw [Nat.cast_sub hrW']
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hexp4 : (25 : ℝ) ≤ Real.exp 4 := by
    have h1 := Real.exp_one_gt_d9
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    have h2 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
      pow_le_pow_left₀ (by norm_num) h1.le 4
    refine le_trans ?_ h2
    norm_num
  have hA : (25 : ℝ) ^ m ≤ Real.exp (4 * m) := by
    calc (25 : ℝ) ^ m ≤ Real.exp 4 ^ m := pow_le_pow_left₀ (by norm_num) hexp4 m
      _ = Real.exp (4 * m) := by rw [← Real.exp_nat_mul]; ring_nf
  have hB : (2 : ℝ) ^ r ≤ Real.exp r := by
    calc (2 : ℝ) ^ r ≤ Real.exp 1 ^ r := pow_le_pow_left₀ (by norm_num) hexp1 r
      _ = Real.exp r := by rw [← Real.exp_nat_mul]; ring_nf
  have hfrac : (1 : ℝ) / 2 ≤ ((W : ℝ) - r) / W := by
    rw [le_div_iff₀ hWpos]
    linarith
  have hC : Real.exp (-(100 * x / W) / 4) ^ (W - r) ≤ Real.exp (-(25 / 2) * x) := by
    rw [← Real.exp_nat_mul, hcast]
    refine Real.exp_le_exp.mpr ?_
    have h1 : ((W : ℝ) - r) * (-(100 * x / W) / 4) = -(25 * x * (((W : ℝ) - r) / W)) := by
      field_simp
      ring
    rw [h1]
    nlinarith
  calc (25 : ℝ) ^ m * ((2 : ℝ) ^ r * Real.exp (-(100 * x / W) / 4) ^ (W - r))
      ≤ Real.exp (4 * m) * (Real.exp r * Real.exp (-(25 / 2) * x)) := by
        gcongr
    _ = Real.exp (4 * m + r + -(25 / 2) * x) := by
        rw [← Real.exp_add, ← Real.exp_add, add_assoc]
    _ ≤ Real.exp (-1 * s) := by
        refine Real.exp_le_exp.mpr ?_
        simp only [hx]
        nlinarith
    _ ≤ 20 * Real.exp (-1 * s) := by
        have := Real.exp_pos (-1 * s)
        linarith

/-- (9.56) [us:eq:Haar] for fixed data: a Haar-rotated projection `O P O*` and a fixed projection
`Q₀` overlap in operator norm by at most `C √((Tr P + Tr Q₀ + s)/W)`, except with probability
`C e^{-c s}`. -/
theorem haarU_proj_overlap_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ W : ℕ, 1 ≤ W →
    ∀ P Q₀ : Matrix (Fin W) (Fin W) ℂ, P.IsHermitian → P * P = P → Q₀.IsHermitian →
      Q₀ * Q₀ = Q₀ → ∀ s : ℝ, 0 ≤ s →
        haarU W {O | C * Real.sqrt (((Matrix.trace P).re + (Matrix.trace Q₀).re + s) / W) <
            ‖Q₀ * ((O : Matrix (Fin W) (Fin W) ℂ) * P * star (O : Matrix (Fin W) (Fin W) ℂ))‖} ≤
          ENNReal.ofReal (C * Real.exp (-c * s)) := by
  refine ⟨20, 1, by norm_num, by norm_num, ?_⟩
  intro W hW P Q₀ hPH hPP hQH hQP s hs
  have : Nonempty (Fin W) := ⟨⟨0, hW⟩⟩
  obtain ⟨UP, T, hPeq, hTr⟩ := haarSubspace_proj_diag hPH hPP
  obtain ⟨UQ, S, hQeq, hSr⟩ := haarSubspace_proj_diag hQH hQP
  set φ : Matrix.unitaryGroup (Fin W) ℂ → Matrix.unitaryGroup (Fin W) ℂ :=
    fun O => UQ⁻¹ * O * UP with hφ
  have hnorm : ∀ O : Matrix.unitaryGroup (Fin W) ℂ,
      ‖Q₀ * ((O : Matrix (Fin W) (Fin W) ℂ) * P * star (O : Matrix (Fin W) (Fin W) ℂ))‖ =
        ‖haarSubspace_diag S * ((φ O : Matrix.unitaryGroup (Fin W) ℂ) :
          Matrix (Fin W) (Fin W) ℂ) * haarSubspace_diag T‖ := by
    intro O
    have hcoe : ((φ O : Matrix.unitaryGroup (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ) =
        star (UQ : Matrix (Fin W) (Fin W) ℂ) * O * UP := rfl
    have heq : Q₀ * ((O : Matrix (Fin W) (Fin W) ℂ) * P * star (O : Matrix (Fin W) (Fin W) ℂ)) =
        (UQ : Matrix (Fin W) (Fin W) ℂ) * (haarSubspace_diag S *
          ((φ O : Matrix.unitaryGroup (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ) *
            haarSubspace_diag T) * ((star (O * UP) : Matrix.unitaryGroup (Fin W) ℂ) :
              Matrix (Fin W) (Fin W) ℂ) := by
      rw [hcoe, Unitary.coe_star, Submonoid.coe_mul, star_mul, hQeq, hPeq]
      simp only [Matrix.mul_assoc]
    rw [heq, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  have hle1 : ∀ O' : Matrix.unitaryGroup (Fin W) ℂ,
      ‖haarSubspace_diag S * (O' : Matrix (Fin W) (Fin W) ℂ) * haarSubspace_diag T‖ ≤ 1 := by
    intro O'
    calc ‖haarSubspace_diag S * (O' : Matrix (Fin W) (Fin W) ℂ) * haarSubspace_diag T‖
        ≤ ‖haarSubspace_diag S * (O' : Matrix (Fin W) (Fin W) ℂ)‖ * ‖haarSubspace_diag T‖ :=
          norm_mul_le _ _
      _ ≤ (‖haarSubspace_diag S‖ * ‖(O' : Matrix (Fin W) (Fin W) ℂ)‖) *
            ‖haarSubspace_diag T‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ 1 := by
          rw [CStarRing.norm_coe_unitary, mul_one]
          have h1 := haarSubspace_norm_diag_le S
          have h2 := haarSubspace_norm_diag_le T
          have h3 : 0 ≤ ‖haarSubspace_diag S‖ := norm_nonneg _
          nlinarith [norm_nonneg (haarSubspace_diag T)]
  have hφmp : (haarU W).map φ = haarU W := by
    have h1 : (haarU W).map (fun O : Matrix.unitaryGroup (Fin W) ℂ => UQ⁻¹ * O) = haarU W := by
      have := isMulLeftInvariant_haarU W
      exact map_mul_left_eq_self (haarU W) UQ⁻¹
    have h2 : (haarU W).map (fun O : Matrix.unitaryGroup (Fin W) ℂ => O * UP) = haarU W := by
      have := isMulRightInvariant_haarU W
      exact map_mul_right_eq_self (haarU W) UP
    have hφ' : φ = (fun O : Matrix.unitaryGroup (Fin W) ℂ => O * UP) ∘
        (fun O : Matrix.unitaryGroup (Fin W) ℂ => UQ⁻¹ * O) := rfl
    rw [hφ', ← Measure.map_map (measurable_mul_const UP) (measurable_const_mul UQ⁻¹), h1, h2]
  have hφm : Measurable φ := (measurable_const_mul UQ⁻¹).mul_const UP
  rw [hTr, hSr]
  set y : ℝ := ((T.card : ℝ) + S.card + s) / W with hy
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hy0 : 0 ≤ y := by positivity
  set Bset : Set (Matrix.unitaryGroup (Fin W) ℂ) := {O' | 20 * Real.sqrt y <
    ‖haarSubspace_diag S * (O' : Matrix (Fin W) (Fin W) ℂ) * haarSubspace_diag T‖} with hBset
  calc haarU W {O : Matrix.unitaryGroup (Fin W) ℂ | 20 * Real.sqrt y <
        ‖Q₀ * ((O : Matrix (Fin W) (Fin W) ℂ) * P * star (O : Matrix (Fin W) (Fin W) ℂ))‖}
      ≤ haarU W (φ ⁻¹' Bset) := measure_mono fun O hO => by
        simp only [Set.mem_preimage, hBset, Set.mem_ofPred_eq] at hO ⊢
        rwa [← hnorm O]
    _ ≤ (haarU W).map φ Bset := Measure.le_map_apply hφm.aemeasurable _
    _ = haarU W Bset := by rw [hφmp]
    _ ≤ ENNReal.ofReal (20 * Real.exp (-1 * s)) := by
        by_cases hthr : 1 ≤ 20 * Real.sqrt y
        · have : Bset = ∅ := by
            ext O'
            simp only [hBset, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            exact (hle1 O').trans hthr
          rw [this, measure_empty]
          exact zero_le
        · rw [not_le] at hthr
          have h1 : Real.sqrt y < 1 / 20 := by linarith
          have h2 : y < (1 / 20 : ℝ) ^ 2 := (Real.sqrt_lt' (by norm_num)).mp h1
          have hlt : 400 * ((T.card : ℝ) + S.card + s) < W := by
            have : y * W < W / 400 := by nlinarith
            have h3 : y * W = (T.card : ℝ) + S.card + s := by
              rw [hy]; field_simp
            linarith
          have hθ1 : 100 * y ≤ 1 := by nlinarith
          have hsq : Real.sqrt (100 * y) = 10 * Real.sqrt y := by
            rw [Real.sqrt_mul (by norm_num), show (100 : ℝ) = 10 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]
          have hB : Bset = {O' : Matrix.unitaryGroup (Fin W) ℂ | 2 * Real.sqrt (100 * y) <
              ‖haarSubspace_diag S * (O' : Matrix (Fin W) (Fin W) ℂ) * haarSubspace_diag T‖} := by
            ext O'
            simp only [hBset, Set.mem_ofPred_eq, hsq]
            constructor <;> intro h <;> linarith
          rw [hB]
          refine (haarSubspace_coord_tail S T (by positivity) hθ1).trans
            (ENNReal.ofReal_le_ofReal ?_)
          have := haarSubspace_numeric (m := T.card) (r := S.card) hs hW hlt
          rw [show 100 * y = 100 * ((T.card : ℝ) + S.card + s) / W by rw [hy]; ring]
          exact this

/-- (9.56) [us:eq:Haar] on the GUE sample space: for a measurable projection-valued `P` that is
equivariant under common conjugation (`P (conjMap W L O ω) = O P(ω) O*`) and a fixed projection
`Q₀`, the same bound holds under `μ W L`. -/
theorem proj_overlap_le_of_equivariant : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ W L : ℕ, 1 ≤ W →
    ∀ P : Ω W L → Matrix (Fin W) (Fin W) ℂ, Measurable P →
      (∀ ω, (P ω).IsHermitian ∧ P ω * P ω = P ω) →
      (∀ (O : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W L),
        P (conjMap W L O ω) =
          (O : Matrix (Fin W) (Fin W) ℂ) * P ω * star (O : Matrix (Fin W) (Fin W) ℂ)) →
      ∀ Q₀ : Matrix (Fin W) (Fin W) ℂ, Q₀.IsHermitian → Q₀ * Q₀ = Q₀ → ∀ s : ℝ, 0 ≤ s →
        μ W L {ω | C * Real.sqrt (((Matrix.trace (P ω)).re + (Matrix.trace Q₀).re + s) / W) <
            ‖Q₀ * P ω‖} ≤ ENNReal.ofReal (C * Real.exp (-c * s)) := by
  obtain ⟨C, c, hC, hc, h1⟩ := haarU_proj_overlap_le
  refine ⟨C, c, hC, hc, ?_⟩
  intro W L hW P hPm hPproj hPequiv Q₀ hQH hQP s hs
  have hPtr : Measurable fun ω : Ω W L => (Matrix.trace (P ω)).re :=
    (Complex.continuous_re.comp continuous_id.matrix_trace).measurable.comp hPm
  have hPn : Measurable fun ω : Ω W L => ‖Q₀ * P ω‖ :=
    (continuous_norm.comp (continuous_const.matrix_mul continuous_id)).measurable.comp hPm
  have hthr : Measurable fun ω : Ω W L =>
      C * Real.sqrt (((Matrix.trace (P ω)).re + (Matrix.trace Q₀).re + s) / W) := by
    fun_prop
  set B₀ : Set (Ω W L) := {ω | C * Real.sqrt (((Matrix.trace (P ω)).re +
    (Matrix.trace Q₀).re + s) / W) < ‖Q₀ * P ω‖} with hB₀
  have hB₀m : MeasurableSet B₀ := measurableSet_lt hthr hPn
  have hΦ := measurePreserving_conj_haar W L
  have hG : MeasurableSet (B₀ ×ˢ (Set.univ : Set (Matrix.unitaryGroup (Fin W) ℂ))) :=
    hB₀m.prod MeasurableSet.univ
  have hGm : MeasurableSet ((fun p : Ω W L × Matrix.unitaryGroup (Fin W) ℂ =>
      (conjMap W L p.2 p.1, p.2)) ⁻¹' (B₀ ×ˢ (Set.univ : Set (Matrix.unitaryGroup (Fin W) ℂ)))) :=
    hΦ.measurable hG
  have h2 : ((μ W L).prod (haarU W)) (B₀ ×ˢ (Set.univ : Set (Matrix.unitaryGroup (Fin W) ℂ))) =
      μ W L B₀ := by
    rw [Measure.prod_prod, measure_univ, mul_one]
  have h3 := hΦ.measure_preimage hG.nullMeasurableSet
  rw [← h2, ← h3, Measure.prod_apply hGm]
  calc ∫⁻ ω, haarU W (Prod.mk ω ⁻¹' ((fun p : Ω W L × Matrix.unitaryGroup (Fin W) ℂ =>
          (conjMap W L p.2 p.1, p.2)) ⁻¹' (B₀ ×ˢ Set.univ))) ∂(μ W L)
      ≤ ∫⁻ _ω, ENNReal.ofReal (C * Real.exp (-c * s)) ∂(μ W L) := by
        refine lintegral_mono fun ω => ?_
        have hfib := h1 W hW (P ω) Q₀ (hPproj ω).1 (hPproj ω).2 hQH hQP s hs
        refine le_trans (measure_mono fun O hO => ?_) hfib
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, hB₀,
          Set.mem_ofPred_eq] at hO ⊢
        rw [hPequiv O ω] at hO
        have htr : (Matrix.trace ((O : Matrix (Fin W) (Fin W) ℂ) * P ω *
            star (O : Matrix (Fin W) (Fin W) ℂ))).re = (Matrix.trace (P ω)).re := by
          rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
        rwa [htr] at hO
    _ = ENNReal.ofReal (C * Real.exp (-c * s)) := by
        rw [lintegral_const, measure_univ, mul_one]

end LSBA
