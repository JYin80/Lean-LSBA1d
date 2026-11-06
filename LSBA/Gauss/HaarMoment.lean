import LSBA.Gauss.Concentration
import LSBA.Gauss.Sphere

/-!
# Moments of the entries of a Haar conjugate

(7.27) [gc:eq:haar-fixed-moment]: for a Haar unitary `U` and a fixed matrix `A`, the entries of
`U A U*` concentrate around `δ_{ij} W⁻¹ Tr A` at the scale `W⁻¹ ‖A‖_HS`, with every moment and a
constant independent of `W` and `A`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

open scoped Classical

namespace LSBA

open scoped Matrix

/-! ### One-dimensional Gaussian integrals -/

private lemma haarMoment_pdf_mul_exp (c x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (c * x ^ 2) =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2 - c) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- `exp (c t²)` is integrable against the standard Gaussian for `c < 1/2`. -/
private lemma haarMoment_integrable_exp_sq {c : ℝ} (hc : c < 1 / 2) :
    Integrable (fun t : ℝ => Real.exp (c * t ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)]
  have h := (integrable_exp_neg_mul_sq (b := 1 / 2 - c) (by linarith)).const_mul
    ((Real.sqrt (2 * π))⁻¹)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x), smul_eq_mul]
  exact (haarMoment_pdf_mul_exp c x).symm

/-- `E exp (c t²) = (1 - 2c)^{-1/2}` for the standard Gaussian and `c < 1/2`. -/
private lemma haarMoment_integral_exp_sq {c : ℝ} (hc : c < 1 / 2) :
    ∫ t : ℝ, Real.exp (c * t ^ 2) ∂(gaussianReal 0 1) = Real.sqrt ((1 - 2 * c)⁻¹) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul, haarMoment_pdf_mul_exp]
  rw [integral_const_mul, integral_gaussian]
  have h1 : 0 < 1 - 2 * c := by linarith
  have h4 : π / (1 / 2 - c) = (2 * π) * (1 - 2 * c)⁻¹ := by
    field_simp
  have : Real.sqrt (2 * π) ≠ 0 := by positivity
  have h5 : Real.sqrt (2 * π * (1 - 2 * c)⁻¹) =
      Real.sqrt (2 * π) * Real.sqrt ((1 - 2 * c)⁻¹) :=
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π) ((1 - 2 * c)⁻¹)
  rw [h4, h5, ← mul_assoc, inv_mul_cancel₀ this, one_mul]

/-- `(1 - u) e^{u + u²} ≥ 1` for `|u| ≤ 1/2`. -/
private lemma haarMoment_one_le (u : ℝ) (h1 : -1 / 2 ≤ u) (h2 : u ≤ 1 / 2) :
    1 ≤ (1 - u) * Real.exp (u + u ^ 2) := by
  rcases le_total u 0 with hu | hu
  · have he := Real.add_one_le_exp (u + u ^ 2)
    have h3 : 0 ≤ 1 - u := by linarith
    nlinarith [mul_le_mul_of_nonneg_left he h3, pow_two_nonneg u, mul_nonneg (neg_nonneg.mpr hu)
      (pow_two_nonneg u)]
  · have hv : 0 ≤ u + u ^ 2 := by positivity
    have he := Real.quadratic_le_exp_of_nonneg hv
    have h3 : 0 ≤ 1 - u := by linarith
    have h4 : u + u ^ 2 + u ^ 3 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left he h3, mul_nonneg (pow_two_nonneg u) hu,
      mul_nonneg (mul_nonneg (pow_two_nonneg u) hu) hu]

/-- Sub-Gaussian bound for a centered `χ²₁` variable: `E e^{s(t² - 1)} ≤ e^{2 s²}` for
`|s| ≤ 1/4`. -/
private lemma haarMoment_mgf_coord {s : ℝ} (hs : |s| ≤ 1 / 4) :
    Integrable (fun t : ℝ => Real.exp (s * (t ^ 2 - 1))) (gaussianReal 0 1) ∧
      ∫ t : ℝ, Real.exp (s * (t ^ 2 - 1)) ∂(gaussianReal 0 1) ≤ Real.exp (2 * s ^ 2) := by
  have hs' := abs_le.mp hs
  have hc : s < 1 / 2 := by linarith
  have hfun : (fun t : ℝ => Real.exp (s * (t ^ 2 - 1))) =
      fun t => Real.exp (-s) * Real.exp (s * t ^ 2) := by
    funext t
    rw [← Real.exp_add]
    ring_nf
  rw [hfun]
  refine ⟨(haarMoment_integrable_exp_sq hc).const_mul _, ?_⟩
  rw [integral_const_mul, haarMoment_integral_exp_sq hc]
  have h1 : 0 < 1 - 2 * s := by linarith
  have hsq : Real.sqrt ((1 - 2 * s)⁻¹) ≤ Real.exp (2 * s ^ 2 + s) := by
    rw [← Real.sqrt_sq (Real.exp_pos (2 * s ^ 2 + s)).le]
    refine Real.sqrt_le_sqrt ?_
    rw [inv_le_iff_one_le_mul₀' h1, ← Real.exp_nat_mul]
    have := haarMoment_one_le (2 * s) (by linarith) (by linarith)
    convert this using 3
    push_cast
    ring
  calc Real.exp (-s) * Real.sqrt ((1 - 2 * s)⁻¹)
      ≤ Real.exp (-s) * Real.exp (2 * s ^ 2 + s) :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = Real.exp (2 * s ^ 2) := by rw [← Real.exp_add]; ring_nf

/-! ### Diagonal Gaussian quadratic forms -/

private lemma haarMoment_norm_sq_cplxVec {W : ℕ} (x : Fin W × Fin 2 → ℝ) (k : Fin W) :
    ‖cplxVec W x k‖ ^ 2 = x (k, 0) ^ 2 + x (k, 1) ^ 2 := by
  rw [Complex.sq_norm]
  simp [cplxVec, Complex.normSq_mk]
  ring

private lemma haarMoment_diag_sum {W : ℕ} (lam : Fin W → ℝ) (x : Fin W × Fin 2 → ℝ) :
    ∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2) = ∑ q : Fin W × Fin 2, lam q.1 * (x q ^ 2 - 1) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fin.sum_univ_two, haarMoment_norm_sq_cplxVec]
  ring

/-- Exponential moment of `X = ∑ₖ λₖ (|gₖ|² - 2)` when `|t λₖ| ≤ 1/4`. -/
private lemma haarMoment_diag_mgf {W : ℕ} (lam : Fin W → ℝ) (t : ℝ)
    (ht : ∀ k, |t * lam k| ≤ 1 / 4) :
    Integrable (fun x => Real.exp (t * ∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2)))
        (stdGauss (Fin W × Fin 2)) ∧
      ∫ x, Real.exp (t * ∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2)) ∂(stdGauss (Fin W × Fin 2)) ≤
        Real.exp (4 * t ^ 2 * ∑ k, lam k ^ 2) := by
  have hprod : (fun x : Fin W × Fin 2 → ℝ =>
      Real.exp (t * ∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2))) =
      fun x => ∏ q : Fin W × Fin 2, Real.exp ((t * lam q.1) * (x q ^ 2 - 1)) := by
    funext x
    rw [haarMoment_diag_sum, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun q _ => ?_
    ring_nf
  rw [hprod]
  refine ⟨Integrable.fintype_prod
    (f := fun (q : Fin W × Fin 2) (s : ℝ) => Real.exp ((t * lam q.1) * (s ^ 2 - 1)))
    (μ := fun _ => gaussianReal 0 1) (fun q => (haarMoment_mgf_coord (ht q.1)).1), ?_⟩
  change ∫ x : Fin W × Fin 2 → ℝ, (∏ q : Fin W × Fin 2,
      Real.exp ((t * lam q.1) * (x q ^ 2 - 1))) ∂(Measure.pi fun _ => gaussianReal 0 1) ≤ _
  rw [integral_fintype_prod_eq_prod
    (fun (q : Fin W × Fin 2) (s : ℝ) => Real.exp ((t * lam q.1) * (s ^ 2 - 1)))]
  calc ∏ q : Fin W × Fin 2, ∫ s, Real.exp ((t * lam q.1) * (s ^ 2 - 1)) ∂(gaussianReal 0 1)
      ≤ ∏ q : Fin W × Fin 2, Real.exp (2 * (t * lam q.1) ^ 2) :=
        Finset.prod_le_prod₀ (fun q _ => integral_nonneg fun _ => (Real.exp_pos _).le)
          (fun q _ => (haarMoment_mgf_coord (ht q.1)).2)
    _ = Real.exp (4 * t ^ 2 * ∑ k, lam k ^ 2) := by
        rw [← Real.exp_sum, Fintype.sum_prod_type]
        congr 1
        simp only [Fin.sum_univ_two, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring

/-- Moment bound for `X = ∑ₖ λₖ (|gₖ|² - 2)`: `E|X|^{2p} ≤ 6 (2p)! 16^p (∑ₖ λₖ²)^p`. -/
private lemma haarMoment_diag (p : ℕ) {W : ℕ} (lam : Fin W → ℝ) :
    Integrable (fun x => |∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2)| ^ (2 * p))
        (stdGauss (Fin W × Fin 2)) ∧
      ∫ x, |∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2)| ^ (2 * p) ∂(stdGauss (Fin W × Fin 2)) ≤
        6 * (2 * p).factorial * 16 ^ p * (∑ k, lam k ^ 2) ^ p := by
  set Λ := ∑ k, lam k ^ 2 with hΛ
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hX : Continuous (fun x : Fin W × Fin 2 → ℝ => ∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2)) := by
    simp_rw [haarMoment_diag_sum]
    fun_prop
  rcases hΛ0.lt_or_eq with hpos | hzero
  · set t : ℝ := (4 * Real.sqrt Λ)⁻¹ with htdef
    have hsq : 0 < Real.sqrt Λ := Real.sqrt_pos.mpr hpos
    have ht0 : 0 < t := by positivity
    have htΛ : t * (4 * Real.sqrt Λ) = 1 := inv_mul_cancel₀ (by positivity)
    have hlam : ∀ k, |lam k| ≤ Real.sqrt Λ := fun k =>
      Real.abs_le_sqrt (Finset.single_le_sum (f := fun k => lam k ^ 2)
        (fun k _ => sq_nonneg _) (mem_univ k))
    have ht : ∀ k, |t * lam k| ≤ 1 / 4 := by
      intro k
      rw [abs_mul, abs_of_pos ht0]
      calc t * |lam k| ≤ t * Real.sqrt Λ := mul_le_mul_of_nonneg_left (hlam k) ht0.le
        _ = 1 / 4 := by rw [htdef]; field_simp
    have ht' : ∀ k, |-t * lam k| ≤ 1 / 4 := by
      intro k
      rw [neg_mul, abs_neg]
      exact ht k
    obtain ⟨hI1, hE1⟩ := haarMoment_diag_mgf lam t ht
    obtain ⟨hI2, hE2⟩ := haarMoment_diag_mgf lam (-t) ht'
    set c : ℝ := (2 * p).factorial * (4 * Real.sqrt Λ) ^ (2 * p) with hc
    have hpt : ∀ x : Fin W × Fin 2 → ℝ,
        |∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2)| ^ (2 * p) ≤
          c * (Real.exp (t * ∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2)) +
            Real.exp (-t * ∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2))) := by
      intro x
      set y := ∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2)
      have h1 := Real.pow_div_factorial_le_exp _ (mul_nonneg ht0.le (abs_nonneg y)) (2 * p)
      have h2 : Real.exp (t * |y|) ≤ Real.exp (t * y) + Real.exp (-t * y) := by
        rcases le_total 0 y with hy | hy
        · rw [abs_of_nonneg hy]
          linarith [Real.exp_pos (-t * y)]
        · rw [abs_of_nonpos hy, show t * -y = -t * y by ring]
          linarith [Real.exp_pos (t * y)]
      have hf : (0 : ℝ) < (2 * p).factorial := by exact_mod_cast Nat.factorial_pos _
      have h3 : |y| ^ (2 * p) = (t * |y|) ^ (2 * p) * (4 * Real.sqrt Λ) ^ (2 * p) := by
        rw [← mul_pow, mul_comm t, mul_assoc, htΛ, mul_one]
      rw [h3, hc]
      rw [div_le_iff₀ hf] at h1
      have h4 : 0 ≤ (4 * Real.sqrt Λ) ^ (2 * p) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_right h2 hf.le)) h4]
    have hmeas : AEStronglyMeasurable
        (fun x => |∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2)| ^ (2 * p))
        (stdGauss (Fin W × Fin 2)) :=
      ((continuous_abs.comp hX).pow _).aestronglyMeasurable
    have hInt : Integrable (fun x => |∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2)| ^ (2 * p))
        (stdGauss (Fin W × Fin 2)) := by
      refine ((hI1.add hI2).const_mul c).mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpt x
    refine ⟨hInt, ?_⟩
    calc ∫ x, |∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2)| ^ (2 * p) ∂(stdGauss (Fin W × Fin 2))
        ≤ ∫ x, c * (Real.exp (t * ∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2)) +
            Real.exp (-t * ∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2))) ∂(stdGauss (Fin W × Fin 2)) :=
          integral_mono hInt ((hI1.add hI2).const_mul c) hpt
      _ = c * (∫ x, Real.exp (t * ∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2))
              ∂(stdGauss (Fin W × Fin 2)) +
            ∫ x, Real.exp (-t * ∑ k, lam k * (‖cplxVec W x k‖ ^ 2 - 2))
              ∂(stdGauss (Fin W × Fin 2))) := by
          rw [integral_const_mul, integral_add hI1 hI2]
      _ ≤ c * (Real.exp (4 * t ^ 2 * Λ) + Real.exp (4 * (-t) ^ 2 * Λ)) := by
          have : 0 ≤ c := by positivity
          gcongr
      _ = 6 * (2 * p).factorial * 16 ^ p * Λ ^ p * (Real.exp (1 / 4) / 3) := by
          have h4 : 4 * t ^ 2 * Λ = 1 / 4 := by
            rw [htdef, inv_pow, mul_pow, Real.sq_sqrt hΛ0]
            field_simp
          rw [neg_sq, h4, hc, pow_mul, mul_pow, Real.sq_sqrt hΛ0]
          ring
      _ ≤ 6 * (2 * p).factorial * 16 ^ p * Λ ^ p := by
          have h5 : Real.exp (1 / 4) / 3 ≤ 1 := by
            have := Real.exp_one_lt_d9
            have h6 : Real.exp (1 / 4) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
            rw [div_le_one (by norm_num)]
            linarith
          have : 0 ≤ 6 * ((2 * p).factorial : ℝ) * 16 ^ p * Λ ^ p := by positivity
          nlinarith
  · have hlam : ∀ k, lam k = 0 := by
      intro k
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (lam k))).mp hzero.symm k
        (mem_univ k)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    simp only [hlam, zero_mul, Finset.sum_const_zero, abs_zero, ← hzero]
    refine ⟨integrable_const _, ?_⟩
    rw [integral_const, probReal_univ, one_smul]
    rcases p with _ | p
    · norm_num
    · simp

/-! ### Unitary invariance of the complex Gaussian vector -/

/-- The `2W` real coordinates of a complex vector (inverse of `cplxVec`). -/
private def haarMoment_realify {W : ℕ} (y : Fin W → ℂ) : Fin W × Fin 2 → ℝ :=
  fun p => if p.2 = 0 then (y p.1).re else (y p.1).im

private lemma haarMoment_cplxVec_realify {W : ℕ} (y : Fin W → ℂ) :
    cplxVec W (haarMoment_realify y) = y := by
  funext i
  apply Complex.ext <;> simp [cplxVec, haarMoment_realify]

private lemma haarMoment_realify_cplxVec {W : ℕ} (x : Fin W × Fin 2 → ℝ) :
    haarMoment_realify (cplxVec W x) = x := by
  funext p
  rcases p with ⟨i, k⟩
  fin_cases k <;> simp [cplxVec, haarMoment_realify]

private lemma haarMoment_cplxVec_add {W : ℕ} (x y : Fin W × Fin 2 → ℝ) :
    cplxVec W (x + y) = cplxVec W x + cplxVec W y := by
  funext i
  apply Complex.ext <;> simp [cplxVec]

private lemma haarMoment_cplxVec_smul {W : ℕ} (c : ℝ) (x : Fin W × Fin 2 → ℝ) :
    cplxVec W (c • x) = (c : ℂ) • cplxVec W x := by
  funext i
  apply Complex.ext <;> simp [cplxVec]

private lemma haarMoment_realify_add {W : ℕ} (y z : Fin W → ℂ) :
    haarMoment_realify (y + z) = haarMoment_realify y + haarMoment_realify z := by
  funext p
  by_cases h : p.2 = 0 <;> simp [haarMoment_realify, h]

private lemma haarMoment_realify_smul {W : ℕ} (c : ℝ) (y : Fin W → ℂ) :
    haarMoment_realify ((c : ℂ) • y) = c • haarMoment_realify y := by
  funext p
  by_cases h : p.2 = 0 <;> simp [haarMoment_realify, h]

private lemma haarMoment_continuous_cplxVec (W : ℕ) : Continuous (cplxVec W) := by
  have : cplxVec W = fun x i => (x (i, 0) : ℂ) + (x (i, 1) : ℂ) * Complex.I := by
    funext x i
    apply Complex.ext <;> simp [cplxVec]
  rw [this]
  fun_prop

private lemma haarMoment_continuous_realify (W : ℕ) :
    Continuous (haarMoment_realify : (Fin W → ℂ) → Fin W × Fin 2 → ℝ) := by
  refine continuous_pi fun p => ?_
  by_cases h : p.2 = 0
  · simp only [haarMoment_realify, h, ite_true]
    fun_prop
  · simp only [haarMoment_realify, h, ite_false]
    fun_prop

/-- `∑ₚ xₚ² = ∑ᵢ |gᵢ|²` for `g = cplxVec W x`. -/
private lemma haarMoment_sum_sq {W : ℕ} (x : Fin W × Fin 2 → ℝ) :
    ∑ p, x p ^ 2 = ∑ i, ‖cplxVec W x i‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two, haarMoment_norm_sq_cplxVec]

private lemma haarMoment_star_dotProduct {W : ℕ} (z : Fin W → ℂ) :
    star z ⬝ᵥ z = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
  push_cast
  rfl

/-- A unitary matrix preserves `∑ᵢ |yᵢ|²`. -/
private lemma haarMoment_sum_norm_mulVec {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ)
    (y : Fin W → ℂ) :
    ∑ i, ‖((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ y) i‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
  have hU : star (U : Matrix (Fin W) (Fin W) ℂ) * (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  have h : star ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ y) ⬝ᵥ
      ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ y) = star y ⬝ᵥ y := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, hU, Matrix.one_mulVec]
  rw [haarMoment_star_dotProduct, haarMoment_star_dotProduct] at h
  exact_mod_cast h

/-- A unitary `U` of `ℂ^W` acting on the `2W` real coordinates, as a real isometry. -/
private def haarMoment_iso {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ) :
    EuclideanSpace ℝ (Fin W × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin W × Fin 2) where
  toFun z := WithLp.toLp 2
    (haarMoment_realify ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ (cplxVec W z.ofLp)))
  invFun z := WithLp.toLp 2
    (haarMoment_realify ((star (U : Matrix (Fin W) (Fin W) ℂ)) *ᵥ (cplxVec W z.ofLp)))
  map_add' a b := by
    simp only [WithLp.ofLp_add, haarMoment_cplxVec_add, Matrix.mulVec_add, haarMoment_realify_add,
      WithLp.toLp_add]
  map_smul' c a := by
    simp only [WithLp.ofLp_smul, haarMoment_cplxVec_smul, Matrix.mulVec_smul,
      haarMoment_realify_smul, WithLp.toLp_smul, RingHom.id_apply]
  left_inv z := by
    have hU : star (U : Matrix (Fin W) (Fin W) ℂ) * (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp U.2
    simp only [haarMoment_cplxVec_realify, Matrix.mulVec_mulVec, hU,
      Matrix.one_mulVec, haarMoment_realify_cplxVec, WithLp.toLp_ofLp]
  right_inv z := by
    have hU : (U : Matrix (Fin W) (Fin W) ℂ) * star (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp U.2
    simp only [haarMoment_cplxVec_realify, Matrix.mulVec_mulVec, hU,
      Matrix.one_mulVec, haarMoment_realify_cplxVec, WithLp.toLp_ofLp]
  norm_map' z := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [Real.norm_eq_abs, sq_abs]
    rw [haarMoment_sum_sq, haarMoment_cplxVec_realify, haarMoment_sum_norm_mulVec,
      ← haarMoment_sum_sq]

/-- The action `x ↦ realify (U (cplxVec x))` of a unitary on the real coordinates. -/
private def haarMoment_gaussEquiv {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ) :
    (Fin W × Fin 2 → ℝ) ≃ᵐ (Fin W × Fin 2 → ℝ) where
  toFun x := haarMoment_realify ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ cplxVec W x)
  invFun x := haarMoment_realify ((star (U : Matrix (Fin W) (Fin W) ℂ)) *ᵥ cplxVec W x)
  left_inv x := by
    have hU : star (U : Matrix (Fin W) (Fin W) ℂ) * (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp U.2
    simp only [haarMoment_cplxVec_realify, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec,
      haarMoment_realify_cplxVec]
  right_inv x := by
    have hU : (U : Matrix (Fin W) (Fin W) ℂ) * star (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp U.2
    simp only [haarMoment_cplxVec_realify, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec,
      haarMoment_realify_cplxVec]
  measurable_toFun := ((haarMoment_continuous_realify W).comp
    (Continuous.matrix_mulVec continuous_const (haarMoment_continuous_cplxVec W))).measurable
  measurable_invFun := ((haarMoment_continuous_realify W).comp
    (Continuous.matrix_mulVec continuous_const (haarMoment_continuous_cplxVec W))).measurable

private lemma haarMoment_cplxVec_gaussEquiv {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ)
    (x : Fin W × Fin 2 → ℝ) :
    cplxVec W (haarMoment_gaussEquiv U x) = (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ cplxVec W x :=
  haarMoment_cplxVec_realify _

private lemma haarMoment_mp_gaussEquiv {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ) :
    MeasurePreserving (haarMoment_gaussEquiv U) (stdGauss (Fin W × Fin 2))
      (stdGauss (Fin W × Fin 2)) :=
  measurePreserving_stdGauss_linearIsometry (haarMoment_iso U)

/-- `E G(U g) = E G(g)` for a unitary `U` and the standard complex Gaussian vector `g`. -/
private lemma haarMoment_integral_unitary {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ)
    (G : (Fin W → ℂ) → ℝ) :
    ∫ x, G ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ cplxVec W x) ∂(stdGauss (Fin W × Fin 2)) =
      ∫ x, G (cplxVec W x) ∂(stdGauss (Fin W × Fin 2)) := by
  simp_rw [← haarMoment_cplxVec_gaussEquiv U]
  exact (haarMoment_mp_gaussEquiv U).integral_comp' (fun x => G (cplxVec W x))

private lemma haarMoment_integrable_unitary {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ)
    (G : (Fin W → ℂ) → ℝ) :
    Integrable (fun x => G ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ cplxVec W x))
        (stdGauss (Fin W × Fin 2)) ↔
      Integrable (fun x => G (cplxVec W x)) (stdGauss (Fin W × Fin 2)) := by
  simp_rw [← haarMoment_cplxVec_gaussEquiv U]
  exact (haarMoment_mp_gaussEquiv U).integrable_comp_emb
    (haarMoment_gaussEquiv U).measurableEmbedding
    (g := fun x => G (cplxVec W x))

/-! ### Gaussian quadratic forms -/

/-- `tr(Mᴴ M) = ∑ₖₗ |Mₖₗ|²`. -/
private lemma haarMoment_trace_HS {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) :
    (Mᴴ * M).trace = ((∑ k, ∑ l, ‖M k l‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Complex.conj_mul']
  push_cast
  exact Finset.sum_comm

/-- `z* D z = ∑ₖ λₖ |zₖ|²` for the real diagonal matrix `D = diag(λ)`. -/
private lemma haarMoment_dot_diag {W : ℕ} (lam : Fin W → ℝ) (z : Fin W → ℂ) :
    star z ⬝ᵥ Matrix.diagonal (RCLike.ofReal ∘ lam) *ᵥ z = ((∑ k, lam k * ‖z k‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def,
    Function.comp_apply]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.conj_mul']
  simp only [RCLike.ofReal_eq_complex_ofReal]
  ring

/-- `y* (V D V*) y = (V* y)* D (V* y)`. -/
private lemma haarMoment_quad_conj {W : ℕ} (V D : Matrix (Fin W) (Fin W) ℂ) (y : Fin W → ℂ) :
    star y ⬝ᵥ (V * D * star V) *ᵥ y = star (star V *ᵥ y) ⬝ᵥ D *ᵥ (star V *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

/-- The Gaussian quadratic-form moment bound for a Hermitian matrix. -/
private lemma haarMoment_herm (p : ℕ) {W : ℕ} (H : Matrix (Fin W) (Fin W) ℂ)
    (hH : H.IsHermitian) :
    Integrable (fun x => ‖star (cplxVec W x) ⬝ᵥ H *ᵥ cplxVec W x - 2 * H.trace‖ ^ (2 * p))
        (stdGauss (Fin W × Fin 2)) ∧
      ∫ x, ‖star (cplxVec W x) ⬝ᵥ H *ᵥ cplxVec W x - 2 * H.trace‖ ^ (2 * p)
          ∂(stdGauss (Fin W × Fin 2)) ≤
        6 * (2 * p).factorial * 16 ^ p * (∑ k, ∑ l, ‖H k l‖ ^ 2) ^ p := by
  set V : Matrix.unitaryGroup (Fin W) ℂ := hH.eigenvectorUnitary with hV
  set lam := hH.eigenvalues with hlam
  set D : Matrix (Fin W) (Fin W) ℂ := Matrix.diagonal (RCLike.ofReal ∘ lam) with hD
  have hspec : H = (V : Matrix (Fin W) (Fin W) ℂ) * D * star (V : Matrix (Fin W) (Fin W) ℂ) := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hVV : star (V : Matrix (Fin W) (Fin W) ℂ) * (V : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp V.2
  have htr : H.trace = D.trace := by
    rw [hspec, Matrix.trace_mul_comm, ← mul_assoc, hVV, one_mul]
  have htrD : D.trace = ((∑ k, lam k : ℝ) : ℂ) := by
    simp [hD, Matrix.trace_diagonal]
  have hHS : ∑ k, ∑ l, ‖H k l‖ ^ 2 = ∑ k, lam k ^ 2 := by
    have h1 := haarMoment_trace_HS H
    have h2 := haarMoment_trace_HS D
    have h3 : (Hᴴ * H).trace = (Dᴴ * D).trace := by
      have hVV' : ∀ M : Matrix (Fin W) (Fin W) ℂ,
          star (V : Matrix (Fin W) (Fin W) ℂ) * ((V : Matrix (Fin W) (Fin W) ℂ) * M) = M := by
        intro M
        rw [← mul_assoc, hVV, one_mul]
      rw [hspec]
      simp only [← Matrix.star_eq_conjTranspose, star_mul, star_star, mul_assoc, hVV']
      rw [Matrix.trace_mul_comm]
      simp only [mul_assoc, hVV, mul_one]
    have h4 : ∑ k, ∑ l, ‖D k l‖ ^ 2 = ∑ k, lam k ^ 2 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hD, Matrix.diagonal_apply]
      rw [Finset.sum_eq_single k]
      · simp
      · intro l _ hl
        simp [Ne.symm hl]
      · simp
    rw [← h4]
    exact_mod_cast (h1.symm.trans h3).trans h2
  set G : (Fin W → ℂ) → ℝ := fun z => |∑ k, lam k * (‖z k‖ ^ 2 - 2)| ^ (2 * p) with hG
  have hpt : ∀ x, ‖star (cplxVec W x) ⬝ᵥ H *ᵥ cplxVec W x - 2 * H.trace‖ ^ (2 * p) =
      G (((star V : Matrix.unitaryGroup (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ) *ᵥ cplxVec W x) := by
    intro x
    rw [Unitary.coe_star, htr, htrD]
    conv_lhs => rw [hspec, haarMoment_quad_conj, haarMoment_dot_diag]
    simp only [hG]
    congr 1
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hpt]
  rw [haarMoment_integrable_unitary, haarMoment_integral_unitary, hHS]
  exact haarMoment_diag p lam

private lemma haarMoment_add_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ n ≤ (2 * b) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * b ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (a ^ n + b ^ n) := by
          have : 0 ≤ a ^ n := by positivity
          have : (0 : ℝ) ≤ 2 ^ n := by positivity
          nlinarith
  · calc (a + b) ^ n ≤ (2 * a) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * a ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (a ^ n + b ^ n) := by
          have : 0 ≤ b ^ n := by positivity
          have : (0 : ℝ) ≤ 2 ^ n := by positivity
          nlinarith

/-- A matrix with `|Mₖₗ| ≤ (|Aₖₗ| + |Aₗₖ|)/2` has `‖M‖_HS ≤ ‖A‖_HS`. -/
private lemma haarMoment_HS_le {W : ℕ} (A M : Matrix (Fin W) (Fin W) ℂ)
    (h : ∀ k l, ‖M k l‖ ≤ (‖A k l‖ + ‖A l k‖) / 2) :
    ∑ k, ∑ l, ‖M k l‖ ^ 2 ≤ ∑ k, ∑ l, ‖A k l‖ ^ 2 := by
  have h1 : ∀ k l, ‖M k l‖ ^ 2 ≤ (‖A k l‖ ^ 2 + ‖A l k‖ ^ 2) / 2 := by
    intro k l
    have := h k l
    have h0 : 0 ≤ ‖M k l‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖A k l‖ - ‖A l k‖)]
  calc ∑ k, ∑ l, ‖M k l‖ ^ 2 ≤ ∑ k, ∑ l, (‖A k l‖ ^ 2 + ‖A l k‖ ^ 2) / 2 :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => h1 k l
    _ = ((∑ k, ∑ l, ‖A k l‖ ^ 2) + ∑ k, ∑ l, ‖A l k‖ ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ k, ∑ l, ‖A k l‖ ^ 2 := by
        rw [Finset.sum_comm (f := fun k l => ‖A l k‖ ^ 2)]
        ring

/-- Gaussian quadratic-form moment bound, Section 7.5 [app:uniform-continuation]: for the
standard complex Gaussian vector `g = cplxVec W x` (so `E g* A g = 2 tr A`),
`E|g* A g - 2 tr A|^{2p} ≤ K ‖A‖_HS^{2p}` with `K` depending only on `p`. -/
theorem haarMoment_gauss_quadForm (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (W : ℕ) (A : Matrix (Fin W) (Fin W) ℂ),
      Integrable (fun x => ‖star (cplxVec W x) ⬝ᵥ A *ᵥ cplxVec W x - 2 * A.trace‖ ^ (2 * p))
          (stdGauss (Fin W × Fin 2)) ∧
        ∫ x, ‖star (cplxVec W x) ⬝ᵥ A *ᵥ cplxVec W x - 2 * A.trace‖ ^ (2 * p)
            ∂(stdGauss (Fin W × Fin 2)) ≤
          K * (∑ k, ∑ l, ‖A k l‖ ^ 2) ^ p := by
  set K₀ : ℝ := 6 * (2 * p).factorial * 16 ^ p with hK₀
  have hK₀ : 0 < K₀ := by
    have : (0 : ℝ) < (2 * p).factorial := by exact_mod_cast Nat.factorial_pos _
    positivity
  refine ⟨2 ^ (2 * p) * (2 * K₀), by positivity, fun W A => ?_⟩
  set H₁ : Matrix (Fin W) (Fin W) ℂ := (1 / 2 : ℂ) • (A + Aᴴ) with hH₁
  set H₂ : Matrix (Fin W) (Fin W) ℂ := (-Complex.I / 2) • (A - Aᴴ) with hH₂
  have hA : A = H₁ + Complex.I • H₂ := by
    simp only [hH₁, hH₂, smul_smul]
    ext k l
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hH₁h : H₁.IsHermitian := by
    simp only [hH₁, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
    rw [add_comm]
    congr 1
    simp
  have hH₂h : H₂.IsHermitian := by
    simp only [hH₂, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    ext k l
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, star_div₀, star_neg,
      Complex.star_def, Complex.conj_I, map_ofNat]
    ring
  obtain ⟨hI₁, hE₁⟩ := haarMoment_herm p H₁ hH₁h
  obtain ⟨hI₂, hE₂⟩ := haarMoment_herm p H₂ hH₂h
  have hB₁ : ∑ k, ∑ l, ‖H₁ k l‖ ^ 2 ≤ ∑ k, ∑ l, ‖A k l‖ ^ 2 := by
    refine haarMoment_HS_le A H₁ fun k l => ?_
    simp only [hH₁, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply, smul_eq_mul,
      norm_mul]
    have : ‖A k l + star (A l k)‖ ≤ ‖A k l‖ + ‖A l k‖ := (norm_add_le _ _).trans (by simp)
    rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
    linarith
  have hB₂ : ∑ k, ∑ l, ‖H₂ k l‖ ^ 2 ≤ ∑ k, ∑ l, ‖A k l‖ ^ 2 := by
    refine haarMoment_HS_le A H₂ fun k l => ?_
    simp only [hH₂, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, smul_eq_mul,
      norm_mul]
    have : ‖A k l - star (A l k)‖ ≤ ‖A k l‖ + ‖A l k‖ := (norm_sub_le _ _).trans (by simp)
    rw [show ‖(-Complex.I / 2 : ℂ)‖ = 1 / 2 by simp]
    linarith
  clear_value H₁ H₂
  set E₁ : (Fin W × Fin 2 → ℝ) → ℂ :=
    fun x => star (cplxVec W x) ⬝ᵥ H₁ *ᵥ cplxVec W x - 2 * H₁.trace with hE₁def
  set E₂ : (Fin W × Fin 2 → ℝ) → ℂ :=
    fun x => star (cplxVec W x) ⬝ᵥ H₂ *ᵥ cplxVec W x - 2 * H₂.trace with hE₂def
  have hsplit : ∀ x, star (cplxVec W x) ⬝ᵥ A *ᵥ cplxVec W x - 2 * A.trace =
      E₁ x + Complex.I * E₂ x := by
    intro x
    simp only [hE₁def, hE₂def]
    conv_lhs => rw [hA]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hpt : ∀ x, ‖star (cplxVec W x) ⬝ᵥ A *ᵥ cplxVec W x - 2 * A.trace‖ ^ (2 * p) ≤
      2 ^ (2 * p) * (‖E₁ x‖ ^ (2 * p) + ‖E₂ x‖ ^ (2 * p)) := by
    intro x
    rw [hsplit]
    calc ‖E₁ x + Complex.I * E₂ x‖ ^ (2 * p) ≤ (‖E₁ x‖ + ‖E₂ x‖) ^ (2 * p) := by
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
          refine (norm_add_le _ _).trans ?_
          simp
      _ ≤ _ := haarMoment_add_pow_le _ _ (norm_nonneg _) (norm_nonneg _) _
  have hcont : Continuous (fun x => ‖star (cplxVec W x) ⬝ᵥ A *ᵥ cplxVec W x - 2 * A.trace‖ ^
      (2 * p)) := by
    have hc := haarMoment_continuous_cplxVec W
    have : Continuous (fun x => star (cplxVec W x) ⬝ᵥ A *ᵥ cplxVec W x) :=
      Continuous.dotProduct (continuous_star.comp hc) (Continuous.matrix_mulVec continuous_const hc)
    fun_prop
  have hI : Integrable (fun x => ‖star (cplxVec W x) ⬝ᵥ A *ᵥ cplxVec W x - 2 * A.trace‖ ^ (2 * p))
      (stdGauss (Fin W × Fin 2)) := by
    refine ((hI₁.add hI₂).const_mul (2 ^ (2 * p))).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt x
  refine ⟨hI, ?_⟩
  have hS0 : 0 ≤ ∑ k, ∑ l, ‖A k l‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => by positivity
  have hP₁ : (∑ k, ∑ l, ‖H₁ k l‖ ^ 2) ^ p ≤ (∑ k, ∑ l, ‖A k l‖ ^ 2) ^ p :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => by positivity) hB₁ p
  have hP₂ : (∑ k, ∑ l, ‖H₂ k l‖ ^ 2) ^ p ≤ (∑ k, ∑ l, ‖A k l‖ ^ 2) ^ p :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => by positivity) hB₂ p
  calc ∫ x, ‖star (cplxVec W x) ⬝ᵥ A *ᵥ cplxVec W x - 2 * A.trace‖ ^ (2 * p)
        ∂(stdGauss (Fin W × Fin 2))
      ≤ ∫ x, 2 ^ (2 * p) * (‖E₁ x‖ ^ (2 * p) + ‖E₂ x‖ ^ (2 * p)) ∂(stdGauss (Fin W × Fin 2)) :=
        integral_mono hI ((hI₁.add hI₂).const_mul _) hpt
    _ = 2 ^ (2 * p) * (∫ x, ‖E₁ x‖ ^ (2 * p) ∂(stdGauss (Fin W × Fin 2)) +
          ∫ x, ‖E₂ x‖ ^ (2 * p) ∂(stdGauss (Fin W × Fin 2))) := by
        rw [integral_const_mul, integral_add hI₁ hI₂]
    _ ≤ 2 ^ (2 * p) * (K₀ * (∑ k, ∑ l, ‖A k l‖ ^ 2) ^ p + K₀ * (∑ k, ∑ l, ‖A k l‖ ^ 2) ^ p) := by
        gcongr
        · exact hE₁.trans (mul_le_mul_of_nonneg_left hP₁ hK₀.le)
        · exact hE₂.trans (mul_le_mul_of_nonneg_left hP₂ hK₀.le)
    _ = 2 ^ (2 * p) * (2 * K₀) * (∑ k, ∑ l, ‖A k l‖ ^ 2) ^ p := by ring

/-! ### Radius and direction of the complex Gaussian vector -/

/-- Every power of `∑ₚ xₚ²` is integrable under `stdGauss`. -/
private lemma haarMoment_integrable_radius_pow {W : ℕ} (n : ℕ) :
    Integrable (fun x : Fin W × Fin 2 → ℝ => (∑ q, x q ^ 2) ^ n) (stdGauss (Fin W × Fin 2)) := by
  have hE : Integrable (fun x : Fin W × Fin 2 → ℝ => ∏ q, Real.exp ((1 / 4) * x q ^ 2))
      (stdGauss (Fin W × Fin 2)) :=
    Integrable.fintype_prod (f := fun (_ : Fin W × Fin 2) (t : ℝ) => Real.exp ((1 / 4) * t ^ 2))
      (μ := fun _ => gaussianReal 0 1) (fun _ => haarMoment_integrable_exp_sq (by norm_num))
  refine (hE.const_mul ((n.factorial : ℝ) * 4 ^ n)).mono'
    (by fun_prop : Continuous fun x : Fin W × Fin 2 → ℝ => (∑ q, x q ^ 2) ^ n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hr : 0 ≤ ∑ q, x q ^ 2 := Finset.sum_nonneg fun q _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Real.exp_sum, ← Finset.mul_sum]
  have h1 := Real.pow_div_factorial_le_exp _ (by positivity : 0 ≤ (1 / 4 : ℝ) * ∑ q, x q ^ 2) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_iff₀ hf, mul_pow] at h1
  have h4 : (4 : ℝ) ^ n * (1 / 4) ^ n = 1 := by rw [← mul_pow]; norm_num
  calc (∑ q, x q ^ 2) ^ n = (4 : ℝ) ^ n * ((1 / 4) ^ n * (∑ q, x q ^ 2) ^ n) := by
        rw [← mul_assoc, h4, one_mul]
    _ ≤ (4 : ℝ) ^ n * (Real.exp ((1 / 4) * ∑ q, x q ^ 2) * n.factorial) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/-- `E x_q² = 1` for each coordinate. -/
private lemma haarMoment_integral_coord_sq {W : ℕ} (q : Fin W × Fin 2) :
    ∫ x : Fin W × Fin 2 → ℝ, x q ^ 2 ∂(stdGauss (Fin W × Fin 2)) = 1 := by
  unfold stdGauss
  rw [integral_comp_eval (μ := fun _ : Fin W × Fin 2 => gaussianReal 0 1) (i := q)
    (f := fun t : ℝ => t ^ 2) (by fun_prop)]
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa [integral_id_gaussianReal] using h

/-- Radius moment, Section 7.5 [app:uniform-continuation]: for the standard complex Gaussian
vector `g = cplxVec W x`, `E (∑ₖ |gₖ|²)^{2p} ≥ (E ∑ₖ |gₖ|²)^{2p} = (2W)^{2p}` (Jensen). -/
theorem haarMoment_radius_moment (W p : ℕ) :
    Integrable (fun x => (∑ k, ‖cplxVec W x k‖ ^ 2) ^ (2 * p)) (stdGauss (Fin W × Fin 2)) ∧
      (2 * W : ℝ) ^ (2 * p) ≤
        ∫ x, (∑ k, ‖cplxVec W x k‖ ^ 2) ^ (2 * p) ∂(stdGauss (Fin W × Fin 2)) := by
  simp_rw [← haarMoment_sum_sq]
  refine ⟨haarMoment_integrable_radius_pow (2 * p), ?_⟩
  have hI1 : Integrable (fun x : Fin W × Fin 2 → ℝ => ∑ q, x q ^ 2) (stdGauss (Fin W × Fin 2)) := by
    simpa using haarMoment_integrable_radius_pow (W := W) 1
  have hIq : ∀ q : Fin W × Fin 2,
      Integrable (fun x : Fin W × Fin 2 → ℝ => x q ^ 2) (stdGauss (Fin W × Fin 2)) := by
    intro q
    refine hI1.mono' (Continuous.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (f := fun q => x q ^ 2) (fun q _ => sq_nonneg _) (mem_univ q)
  have hmean : ∫ x : Fin W × Fin 2 → ℝ, ∑ q, x q ^ 2 ∂(stdGauss (Fin W × Fin 2)) = 2 * W := by
    rw [integral_finsetSum _ fun q _ => hIq q]
    simp only [haarMoment_integral_coord_sq, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  have hJ := (convexOn_pow (𝕜 := ℝ) (2 * p)).map_integral_le (μ := stdGauss (Fin W × Fin 2))
    (f := fun x : Fin W × Fin 2 → ℝ => ∑ q, x q ^ 2) (continuous_pow _).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun x => Set.mem_Ici.mpr
      (Finset.sum_nonneg fun q _ => sq_nonneg _)) hI1 (haarMoment_integrable_radius_pow (2 * p))
  rw [hmean] at hJ
  exact hJ

private lemma haarMoment_normalize_mulVec {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ)
    (y : Fin W → ℂ) :
    (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ normalize y =
      normalize ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ y) := by
  simp only [normalize]
  rw [Matrix.mulVec_smul, haarMoment_sum_norm_mulVec]

private lemma haarMoment_measurable_normalize (W : ℕ) :
    Measurable (normalize : (Fin W → ℂ) → (Fin W → ℂ)) := by
  unfold normalize
  fun_prop

/-- `|normalize(y)ᵢ|² = |yᵢ|² / ∑ₖ |yₖ|²`, also for `y = 0`. -/
private lemma haarMoment_norm_normalize_sq {W : ℕ} (y : Fin W → ℂ) (i : Fin W) :
    ‖normalize y i‖ ^ 2 = ‖y i‖ ^ 2 / ∑ k, ‖y k‖ ^ 2 := by
  have hN : 0 ≤ ∑ k, ‖y k‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
  simp only [normalize, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, inv_pow, sq_abs, Real.sq_sqrt hN]
  rw [div_eq_inv_mul]

private lemma haarMoment_sum_normalize {W : ℕ} {y : Fin W → ℂ} (hy : y ≠ 0) :
    ∑ i, ‖normalize y i‖ ^ 2 = 1 := by
  simp_rw [haarMoment_norm_normalize_sq]
  rw [← Finset.sum_div, div_self]
  intro h
  apply hy
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).mp h i (mem_univ i)
  simpa using this

/-- `cplxVec W x ≠ 0` for almost every `x`. -/
private lemma haarMoment_ae_ne_zero {W : ℕ} (i₀ : Fin W) :
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

/-- Independence of the radius and the direction of the standard complex Gaussian vector,
Section 7.5 [app:uniform-continuation]: for `g = cplxVec W x`,
`E[φ(∑ₖ |gₖ|²) ψ(g/‖g‖₂)] = E φ(∑ₖ |gₖ|²) · E ψ(g/‖g‖₂)` for measurable `φ, ψ ≥ 0`. -/
theorem haarMoment_radius_direction (W : ℕ) (φ : ℝ → ℝ≥0∞) (ψ : (Fin W → ℂ) → ℝ≥0∞)
    (hφ : Measurable φ) (hψ : Measurable ψ) :
    ∫⁻ x, φ (∑ k, ‖cplxVec W x k‖ ^ 2) * ψ (normalize (cplxVec W x)) ∂(stdGauss (Fin W × Fin 2)) =
      (∫⁻ x, φ (∑ k, ‖cplxVec W x k‖ ^ 2) ∂(stdGauss (Fin W × Fin 2))) *
        ∫⁻ x, ψ (normalize (cplxVec W x)) ∂(stdGauss (Fin W × Fin 2)) := by
  set γ := stdGauss (Fin W × Fin 2) with hγ
  set r : (Fin W × Fin 2 → ℝ) → ℝ := fun x => ∑ k, ‖cplxVec W x k‖ ^ 2 with hr
  set nv : (Fin W × Fin 2 → ℝ) → (Fin W → ℂ) := fun x => normalize (cplxVec W x) with hnv
  have hrm : Measurable r := by
    simp only [hr]
    exact (by fun_prop : Continuous fun y : Fin W → ℂ => ∑ k, ‖y k‖ ^ 2).measurable.comp
      (haarMoment_continuous_cplxVec W).measurable
  have hnm : Measurable nv :=
    (haarMoment_measurable_normalize W).comp (haarMoment_continuous_cplxVec W).measurable
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW
    have hc : ∀ x, nv x = 0 := fun x => Subsingleton.elim _ _
    have hr0 : ∀ x, r x = 0 := fun x => by simp [hr]
    change ∫⁻ x, φ (r x) * ψ (nv x) ∂γ = (∫⁻ x, φ (r x) ∂γ) * ∫⁻ x, ψ (nv x) ∂γ
    simp only [hc, hr0, lintegral_const, measure_univ, mul_one]
  obtain ⟨i₀⟩ : Nonempty (Fin W) := ⟨⟨0, hW⟩⟩
  -- invariance of the joint law under every unitary
  have hinv : ∀ U : Matrix.unitaryGroup (Fin W) ℂ,
      ∫⁻ x, φ (r x) * ψ (nv x) ∂γ =
        ∫⁻ x, φ (r x) * ψ ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ nv x) ∂γ := by
    intro U
    have h := (haarMoment_mp_gaussEquiv U).lintegral_comp
      (f := fun x => φ (r x) * ψ (nv x)) ((hφ.comp hrm).mul (hψ.comp hnm))
    rw [← h]
    refine lintegral_congr fun x => ?_
    simp only [hr, hnv, haarMoment_cplxVec_gaussEquiv, haarMoment_sum_norm_mulVec,
      haarMoment_normalize_mulVec]
  have hjoint : Measurable (fun q : Matrix.unitaryGroup (Fin W) ℂ × (Fin W × Fin 2 → ℝ) =>
      φ (r q.2) * ψ ((q.1 : Matrix (Fin W) (Fin W) ℂ) *ᵥ nv q.2)) := by
    refine (hφ.comp (hrm.comp measurable_snd)).mul (hψ.comp ?_)
    have hc : Continuous (fun z : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) => z.1 *ᵥ z.2) :=
      Continuous.matrix_mulVec continuous_fst continuous_snd
    exact hc.measurable.comp ((continuous_subtype_val.measurable.comp measurable_fst).prodMk
      (hnm.comp measurable_snd))
  set c := ∫⁻ x, ψ (nv x) ∂γ with hc
  have hcol : ∀ᵐ x ∂γ, ∫⁻ U, ψ ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ nv x) ∂(haarU W) = c := by
    filter_upwards [haarMoment_ae_ne_zero i₀] with x hx
    have hu := haarMoment_sum_normalize hx
    have hmv : Measurable (fun U : Matrix.unitaryGroup (Fin W) ℂ =>
        (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ nv x) :=
      (Continuous.matrix_mulVec continuous_subtype_val continuous_const).measurable
    rw [← lintegral_map hψ hmv, map_haarU_mulVec W (nv x) hu, lintegral_map hψ hnm]
  calc ∫⁻ x, φ (r x) * ψ (nv x) ∂γ
      = ∫⁻ _U, ∫⁻ x, φ (r x) * ψ (nv x) ∂γ ∂(haarU W) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ U, ∫⁻ x, φ (r x) * ψ ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ nv x) ∂γ ∂(haarU W) :=
        lintegral_congr fun U => hinv U
    _ = ∫⁻ x, ∫⁻ U, φ (r x) * ψ ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ nv x) ∂(haarU W) ∂γ :=
        lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ x, φ (r x) * ∫⁻ U, ψ ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ nv x) ∂(haarU W) ∂γ := by
        refine lintegral_congr fun x => ?_
        exact lintegral_const_mul _ (hψ.comp
          (Continuous.matrix_mulVec continuous_subtype_val continuous_const).measurable)
    _ = ∫⁻ x, φ (r x) * c ∂γ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hcol] with x hx
        rw [hx]
    _ = (∫⁻ x, φ (r x) ∂γ) * c := lintegral_mul_const _ (hφ.comp hrm)

/-! ### The quadratic form of a uniform unit vector -/

/-- `q(normalize y) = (∑ₖ |yₖ|²)⁻¹ q(y)` for the form `q(y) = y* B y`. -/
private lemma haarMoment_quad_normalize {W : ℕ} (B : Matrix (Fin W) (Fin W) ℂ) (y : Fin W → ℂ) :
    star (normalize y) ⬝ᵥ B *ᵥ normalize y =
      ((∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ)⁻¹ * (star y ⬝ᵥ B *ᵥ y) := by
  have hN : 0 ≤ ∑ k, ‖y k‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
  have hs : ((Real.sqrt (∑ k, ‖y k‖ ^ 2) : ℂ))⁻¹ * ((Real.sqrt (∑ k, ‖y k‖ ^ 2) : ℂ))⁻¹ =
      ((∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hN]
  simp only [normalize, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, RCLike.star_def, map_inv₀, Complex.conj_ofReal]
  rw [← mul_assoc, hs]

/-- Moment of the quadratic form of a uniform unit vector: for `tr B = 0`,
`E|w* B w|^{2p} ≤ K (2W)^{-2p} ‖B‖_HS^{2p}` with `w = g/‖g‖₂`. -/
private lemma haarMoment_sphere (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (W : ℕ), 1 ≤ W → ∀ (B : Matrix (Fin W) (Fin W) ℂ), B.trace = 0 →
      ∫ x, ‖star (normalize (cplxVec W x)) ⬝ᵥ B *ᵥ normalize (cplxVec W x)‖ ^ (2 * p)
          ∂(stdGauss (Fin W × Fin 2)) ≤
        K / (2 * W : ℝ) ^ (2 * p) * (∑ k, ∑ l, ‖B k l‖ ^ 2) ^ p := by
  obtain ⟨K, hK, hS1⟩ := haarMoment_gauss_quadForm p
  refine ⟨K, hK, fun W hW B hB => ?_⟩
  set γ := stdGauss (Fin W × Fin 2) with hγ
  obtain ⟨hIQ, hEQ⟩ := hS1 W B
  simp only [hB, mul_zero, sub_zero] at hIQ hEQ
  obtain ⟨hIR, hER⟩ := haarMoment_radius_moment W p
  set R : (Fin W × Fin 2 → ℝ) → ℝ := fun x => ∑ k, ‖cplxVec W x k‖ ^ 2 with hR
  set ψ : (Fin W → ℂ) → ℝ := fun w => ‖star w ⬝ᵥ B *ᵥ w‖ ^ (2 * p) with hψ
  have hψc : Continuous ψ := by
    have : Continuous (fun w : Fin W → ℂ => star w ⬝ᵥ B *ᵥ w) :=
      Continuous.dotProduct continuous_star (Continuous.matrix_mulVec continuous_const
        continuous_id)
    fun_prop
  have hRm : Measurable R := by
    simp only [hR]
    exact (by fun_prop : Continuous fun y : Fin W → ℂ => ∑ k, ‖y k‖ ^ 2).measurable.comp
      (haarMoment_continuous_cplxVec W).measurable
  have hnm : Measurable (fun x => normalize (cplxVec W x)) :=
    (haarMoment_measurable_normalize W).comp (haarMoment_continuous_cplxVec W).measurable
  have hfac := haarMoment_radius_direction W (fun t => ENNReal.ofReal (t ^ (2 * p)))
    (fun w => ENNReal.ofReal (ψ w)) (ENNReal.measurable_ofReal.comp (by fun_prop))
    (ENNReal.measurable_ofReal.comp hψc.measurable)
  obtain ⟨i₀⟩ : Nonempty (Fin W) := ⟨⟨0, hW⟩⟩
  -- the left side is the Gaussian moment
  have hL : ∫⁻ x, ENNReal.ofReal (R x ^ (2 * p)) * ENNReal.ofReal (ψ (normalize (cplxVec W x))) ∂γ =
      ENNReal.ofReal (∫ x, ‖star (cplxVec W x) ⬝ᵥ B *ᵥ cplxVec W x‖ ^ (2 * p) ∂γ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hIQ
      (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr_ae ?_
    filter_upwards [haarMoment_ae_ne_zero i₀] with x hx
    have hpos : 0 < R x := by
      refine lt_of_le_of_ne (Finset.sum_nonneg fun k _ => by positivity) (fun h => hx ?_)
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).mp h.symm i
        (mem_univ i)
      simpa using this
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [hψ, haarMoment_quad_normalize, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs]
    rw [← mul_pow, ← mul_assoc, abs_of_pos hpos, mul_inv_cancel₀ hpos.ne', one_mul]
  have hM : ∫⁻ x, ENNReal.ofReal (R x ^ (2 * p)) ∂γ = ENNReal.ofReal (∫ x, R x ^ (2 * p) ∂γ) :=
    (ofReal_integral_eq_lintegral_ofReal hIR (Filter.Eventually.of_forall fun x => by
      positivity)).symm
  set L := ∫⁻ x, ENNReal.ofReal (ψ (normalize (cplxVec W x))) ∂γ with hLdef
  rw [hL, hM] at hfac
  have hW2 : (0 : ℝ) < (2 * W : ℝ) ^ (2 * p) := by
    have : (0 : ℝ) < W := by exact_mod_cast hW
    positivity
  have hMpos : 0 < ∫ x, R x ^ (2 * p) ∂γ := hW2.trans_le hER
  have hLtop : L ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by simpa using hMpos)] at hfac
    exact ENNReal.ofReal_ne_top hfac
  have hreal : (∫ x, R x ^ (2 * p) ∂γ) * L.toReal =
      ∫ x, ‖star (cplxVec W x) ⬝ᵥ B *ᵥ cplxVec W x‖ ^ (2 * p) ∂γ := by
    have := congrArg ENNReal.toReal hfac
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hMpos.le,
      ENNReal.toReal_ofReal (integral_nonneg fun x => by positivity)] at this
    exact this.symm
  have hint : ∫ x, ‖star (normalize (cplxVec W x)) ⬝ᵥ B *ᵥ normalize (cplxVec W x)‖ ^ (2 * p) ∂γ =
      L.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity)
      (hψc.comp_aestronglyMeasurable hnm.aestronglyMeasurable)]
  rw [hint]
  have hL0 : 0 ≤ L.toReal := ENNReal.toReal_nonneg
  rw [div_mul_eq_mul_div, le_div_iff₀ hW2]
  calc L.toReal * (2 * W : ℝ) ^ (2 * p) ≤ L.toReal * ∫ x, R x ^ (2 * p) ∂γ :=
        mul_le_mul_of_nonneg_left hER hL0
    _ = ∫ x, ‖star (cplxVec W x) ⬝ᵥ B *ᵥ cplxVec W x‖ ^ (2 * p) ∂γ := by rw [mul_comm, hreal]
    _ ≤ K * (∑ k, ∑ l, ‖B k l‖ ^ 2) ^ p := hEQ

/-! ### Haar unitaries -/

private instance haarMoment_isInvInvariant (W : ℕ) : (haarU W).IsInvInvariant := by
  constructor
  have := isMulRightInvariant_haarU W
  have : IsProbabilityMeasure (haarU W).inv := by
    rw [Measure.inv]
    infer_instance
  have : (haarU W).inv.IsHaarMeasure := {}
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- For a unit vector `v`, `E_U F(U* v) = E F(g/‖g‖₂)`. -/
private lemma haarMoment_integral_star_mulVec {W : ℕ} (v : Fin W → ℂ) (hv : ∑ i, ‖v i‖ ^ 2 = 1)
    {F : (Fin W → ℂ) → ℝ} (hF : Measurable F) :
    ∫ U, F (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v) ∂(haarU W) =
      ∫ x, F (normalize (cplxVec W x)) ∂(stdGauss (Fin W × Fin 2)) := by
  have hmv : Measurable (fun U : Matrix.unitaryGroup (Fin W) ℂ =>
      (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v) :=
    (Continuous.matrix_mulVec continuous_subtype_val continuous_const).measurable
  have hnm : Measurable (fun x => normalize (cplxVec W x)) :=
    (haarMoment_measurable_normalize W).comp (haarMoment_continuous_cplxVec W).measurable
  have h1 : ∫ U, F (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v) ∂(haarU W) =
      ∫ U, F ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v) ∂(haarU W) :=
    integral_inv_eq_self (fun U : Matrix.unitaryGroup (Fin W) ℂ =>
      F ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v)) (haarU W)
  rw [h1, ← integral_map hmv.aemeasurable hF.aestronglyMeasurable, map_haarU_mulVec W v hv,
    integral_map hnm.aemeasurable hF.aestronglyMeasurable]

/-- Expansion of `w* N w` at `w = eᵢ + c eⱼ`. -/
private lemma haarMoment_quad_two {W : ℕ} (N : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) (c : ℂ) :
    star (Pi.single i 1 + c • Pi.single j 1 : Fin W → ℂ) ⬝ᵥ
        N *ᵥ (Pi.single i 1 + c • Pi.single j 1) =
      N i i + c * N i j + star c * N j i + star c * c * N j j := by
  simp [dotProduct_add, add_dotProduct, Matrix.mulVec_add, Matrix.mulVec_smul, star_smul]
  ring

/-- `(w/√2)* N (w/√2) = (1/2) w* N w`. -/
private lemma haarMoment_quad_half {W : ℕ} (N : Matrix (Fin W) (Fin W) ℂ) (w : Fin W → ℂ) :
    star ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • w) ⬝ᵥ N *ᵥ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • w) =
      (1 / 2 : ℂ) * (star w ⬝ᵥ N *ᵥ w) := by
  simp only [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    RCLike.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast
  ring

/-- The polarization vectors `(eᵢ + iᵏ eⱼ)/√2`, `k = 0, 1, 2, 3`. -/
private def haarMoment_pol {W : ℕ} (i j : Fin W) (k : Fin 4) : Fin W → ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (Pi.single i 1 + (Complex.I ^ (k : ℕ)) • Pi.single j 1)

/-- Polarization: `Nᵢⱼ = (1/2) ∑ₖ (-i)ᵏ vₖ* N vₖ` for `i ≠ j`. -/
private lemma haarMoment_polarization {W : ℕ} (N : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) :
    N i j = (1 / 2 : ℂ) * ∑ k : Fin 4, star (Complex.I ^ (k : ℕ)) *
      (star (haarMoment_pol i j k) ⬝ᵥ N *ᵥ haarMoment_pol i j k) := by
  simp only [haarMoment_pol, haarMoment_quad_half, haarMoment_quad_two, Fin.sum_univ_four]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, star_one,
    RCLike.star_def, Complex.conj_I, Fin.isValue]
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3]
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  have hc3 : (starRingEnd ℂ) (-Complex.I) = Complex.I := by simp
  rw [hI3, hc3, Complex.I_sq]
  simp only [map_neg, map_one]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The polarization vectors are unit vectors when `i ≠ j`. -/
private lemma haarMoment_pol_unit {W : ℕ} {i j : Fin W} (hij : i ≠ j) (k : Fin 4) :
    ∑ l, ‖haarMoment_pol i j k l‖ ^ 2 = 1 := by
  have hn : star (Complex.I ^ (k : ℕ)) * Complex.I ^ (k : ℕ) = 1 := by
    rw [RCLike.star_def, Complex.conj_mul', norm_pow, Complex.norm_I]
    simp
  have hq : star (haarMoment_pol i j k) ⬝ᵥ (1 : Matrix (Fin W) (Fin W) ℂ) *ᵥ
      haarMoment_pol i j k = 1 := by
    simp only [haarMoment_pol, haarMoment_quad_half, haarMoment_quad_two, Matrix.one_apply_eq,
      Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij), mul_zero, add_zero, mul_one, hn]
    norm_num
  rw [Matrix.one_mulVec, haarMoment_star_dotProduct] at hq
  exact_mod_cast hq

private lemma haarMoment_sum_four_pow (a : Fin 4 → ℝ) (ha : ∀ k, 0 ≤ a k) (n : ℕ) :
    ((1 / 2 : ℝ) * ∑ k, a k) ^ n ≤ 2 ^ n * ∑ k, a k ^ n := by
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  have h1 := haarMoment_add_pow_le (a 0 + a 1) (a 2 + a 3) (by linarith [ha 0, ha 1])
    (by linarith [ha 2, ha 3]) n
  have h2 := haarMoment_add_pow_le (a 0) (a 1) (ha 0) (ha 1) n
  have h3 := haarMoment_add_pow_le (a 2) (a 3) (ha 2) (ha 3) n
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hsum : (a 0 + a 1 + a 2 + a 3) ^ n ≤
      2 ^ n * 2 ^ n * (a 0 ^ n + a 1 ^ n + a 2 ^ n + a 3 ^ n) := by
    calc (a 0 + a 1 + a 2 + a 3) ^ n = ((a 0 + a 1) + (a 2 + a 3)) ^ n := by ring_nf
      _ ≤ 2 ^ n * ((a 0 + a 1) ^ n + (a 2 + a 3) ^ n) := h1
      _ ≤ 2 ^ n * (2 ^ n * (a 0 ^ n + a 1 ^ n) + 2 ^ n * (a 2 ^ n + a 3 ^ n)) := by gcongr
      _ = _ := by ring
  rw [mul_pow]
  calc (1 / 2 : ℝ) ^ n * (a 0 + a 1 + a 2 + a 3) ^ n
      ≤ (1 / 2 : ℝ) ^ n * (2 ^ n * 2 ^ n * (a 0 ^ n + a 1 ^ n + a 2 ^ n + a 3 ^ n)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((1 / 2 : ℝ) * 2) ^ n * 2 ^ n * (a 0 ^ n + a 1 ^ n + a 2 ^ n + a 3 ^ n) := by
        rw [mul_pow]; ring
    _ = _ := by norm_num

/-- `‖A - (W⁻¹ tr A) I‖_HS ≤ ‖A‖_HS`. -/
private lemma haarMoment_HS_center {W : ℕ} (hW : 1 ≤ W) (A : Matrix (Fin W) (Fin W) ℂ) :
    ∑ k, ∑ l, ‖(A - ((W : ℂ)⁻¹ * A.trace) • 1) k l‖ ^ 2 ≤ ∑ k, ∑ l, ‖A k l‖ ^ 2 := by
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
  set c : ℂ := (W : ℂ)⁻¹ * A.trace with hc
  have h1 := haarMoment_trace_HS (A - c • 1)
  have h2 := haarMoment_trace_HS A
  have hexp : ((A - c • 1)ᴴ * (A - c • 1)).trace =
      (Aᴴ * A).trace - ((‖A.trace‖ ^ 2 / W : ℝ) : ℂ) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      Matrix.trace_conjTranspose, smul_eq_mul, Fintype.card_fin]
    simp only [hc, star_mul', star_inv₀, RCLike.star_def, Complex.conj_natCast]
    push_cast
    rw [← Complex.mul_conj']
    field_simp
    ring
  rw [hexp, h2] at h1
  have h3 : ((∑ k, ∑ l, ‖(A - c • 1) k l‖ ^ 2 : ℝ) : ℂ) =
      ((∑ k, ∑ l, ‖A k l‖ ^ 2 - ‖A.trace‖ ^ 2 / W : ℝ) : ℂ) := by
    rw [← h1]
    push_cast
    ring
  have h4 := Complex.ofReal_injective h3
  rw [h4]
  have : 0 ≤ ‖A.trace‖ ^ 2 / (W : ℝ) := by positivity
  linarith

/-! ### Moments of the entries of `U A U*` -/

/-- (7.27) [gc:eq:haar-fixed-moment]. -/
theorem haarU_entry_moment (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ), 1 ≤ W → ∀ (A : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W),
      ∫ U, ‖((U : Matrix (Fin W) (Fin W) ℂ) * A * star (U : Matrix (Fin W) (Fin W) ℂ)) i j -
          (if i = j then (W : ℂ)⁻¹ * A.trace else 0)‖ ^ (2 * p) ∂(haarU W) ≤
        C / (W : ℝ) ^ (2 * p) * (∑ k, ∑ l, ‖A k l‖ ^ 2) ^ p := by
  obtain ⟨K, hK, hsph⟩ := haarMoment_sphere p
  refine ⟨4 * K, by positivity, fun W hW A i j => ?_⟩
  set c : ℂ := (W : ℂ)⁻¹ * A.trace with hc
  set A₀ : Matrix (Fin W) (Fin W) ℂ := A - c • 1 with hA₀
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have htr : A₀.trace = 0 := by
    simp only [hA₀, hc, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      smul_eq_mul]
    field_simp
    ring
  have hHS := haarMoment_HS_center hW A
  set a := ∑ k, ∑ l, ‖A k l‖ ^ 2 with ha
  set a₀ := ∑ k, ∑ l, ‖A₀ k l‖ ^ 2 with ha₀
  have ha₀0 : 0 ≤ a₀ := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => by positivity
  set S := ∫ x, ‖star (normalize (cplxVec W x)) ⬝ᵥ A₀ *ᵥ normalize (cplxVec W x)‖ ^ (2 * p)
    ∂(stdGauss (Fin W × Fin 2)) with hS
  have hS0 : 0 ≤ S := integral_nonneg fun x => by positivity
  have hSb : S ≤ K / (2 * W : ℝ) ^ (2 * p) * a₀ ^ p := hsph W hW A₀ htr
  have hmain : 4 ^ p * (4 * S) ≤ 4 * K / (W : ℝ) ^ (2 * p) * a ^ p := by
    have h2W : (2 * W : ℝ) ^ (2 * p) = 4 ^ p * (W : ℝ) ^ (2 * p) := by
      rw [mul_pow, pow_mul]
      norm_num
    have hWp : (0 : ℝ) < (W : ℝ) ^ (2 * p) := by positivity
    calc 4 ^ p * (4 * S) ≤ 4 ^ p * (4 * (K / (2 * W : ℝ) ^ (2 * p) * a₀ ^ p)) := by gcongr
      _ = 4 * K / (W : ℝ) ^ (2 * p) * a₀ ^ p := by
          rw [h2W]
          field_simp
      _ ≤ 4 * K / (W : ℝ) ^ (2 * p) * a ^ p := by
          gcongr
  have hF : Measurable (fun w : Fin W → ℂ => ‖star w ⬝ᵥ A₀ *ᵥ w‖ ^ (2 * p)) := by
    have : Continuous (fun w : Fin W → ℂ => star w ⬝ᵥ A₀ *ᵥ w) :=
      Continuous.dotProduct continuous_star (Continuous.matrix_mulVec continuous_const
        continuous_id)
    exact (this.norm.pow _).measurable
  have hlaw : ∀ v : Fin W → ℂ, ∑ l, ‖v l‖ ^ 2 = 1 →
      ∫ U, ‖star (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v) ⬝ᵥ
          A₀ *ᵥ (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v)‖ ^ (2 * p) ∂(haarU W) = S :=
    fun v hv => haarMoment_integral_star_mulVec v hv hF
  have hint : ∀ v : Fin W → ℂ, Integrable (fun U : Matrix.unitaryGroup (Fin W) ℂ =>
      ‖star (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v) ⬝ᵥ
          A₀ *ᵥ (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v)‖ ^ (2 * p)) (haarU W) := by
    intro v
    have h1 : Continuous (fun U : Matrix.unitaryGroup (Fin W) ℂ =>
        star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v) :=
      Continuous.matrix_mulVec (continuous_star.comp continuous_subtype_val) continuous_const
    have h2 : Continuous (fun U : Matrix.unitaryGroup (Fin W) ℂ =>
        star (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v) ⬝ᵥ
          A₀ *ᵥ (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v)) :=
      Continuous.dotProduct (continuous_star.comp h1) (Continuous.matrix_mulVec continuous_const h1)
    exact (h2.norm.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hentry : ∀ U : Matrix.unitaryGroup (Fin W) ℂ,
      ((U : Matrix (Fin W) (Fin W) ℂ) * A * star (U : Matrix (Fin W) (Fin W) ℂ)) i j -
          (if i = j then c else 0) =
        ((U : Matrix (Fin W) (Fin W) ℂ) * A₀ * star (U : Matrix (Fin W) (Fin W) ℂ)) i j := by
    intro U
    have hU : (U : Matrix (Fin W) (Fin W) ℂ) * star (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp U.2
    rw [hA₀, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hc]
    split_ifs <;> simp
  simp_rw [hentry]
  by_cases hij : i = j
  · subst hij
    have hu : ∑ l, ‖(Pi.single i 1 : Fin W → ℂ) l‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro l _ hl
        simp [hl]
      · simp
    have hpt : ∀ U : Matrix.unitaryGroup (Fin W) ℂ,
        ‖((U : Matrix (Fin W) (Fin W) ℂ) * A₀ * star (U : Matrix (Fin W) (Fin W) ℂ)) i i‖ ^
            (2 * p) =
          ‖star (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ Pi.single i 1) ⬝ᵥ
            A₀ *ᵥ (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ Pi.single i 1)‖ ^ (2 * p) := by
      intro U
      rw [← haarMoment_quad_conj]
      simp
    simp_rw [hpt]
    rw [hlaw _ hu]
    have h1 : (1 : ℝ) ≤ 4 ^ p * 4 := by
      have : (1 : ℝ) ≤ 4 ^ p := one_le_pow₀ (by norm_num)
      linarith
    calc S ≤ (4 ^ p * 4) * S := le_mul_of_one_le_left hS0 h1
      _ = 4 ^ p * (4 * S) := by ring
      _ ≤ _ := hmain
  · have hpt : ∀ U : Matrix.unitaryGroup (Fin W) ℂ,
        ‖((U : Matrix (Fin W) (Fin W) ℂ) * A₀ * star (U : Matrix (Fin W) (Fin W) ℂ)) i j‖ ^
            (2 * p) ≤
          4 ^ p * ∑ k : Fin 4,
            ‖star (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ haarMoment_pol i j k) ⬝ᵥ
              A₀ *ᵥ (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ haarMoment_pol i j k)‖ ^ (2 * p) := by
      intro U
      set N := (U : Matrix (Fin W) (Fin W) ℂ) * A₀ * star (U : Matrix (Fin W) (Fin W) ℂ)
      have hN : ‖N i j‖ ≤ (1 / 2 : ℝ) * ∑ k : Fin 4,
          ‖star (haarMoment_pol i j k) ⬝ᵥ N *ᵥ haarMoment_pol i j k‖ := by
        rw [haarMoment_polarization N i j, norm_mul]
        rw [show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by simp]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) (by norm_num)
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul, RCLike.star_def, Complex.norm_conj, norm_pow, Complex.norm_I, one_pow,
          one_mul]
      have h4 := haarMoment_sum_four_pow
        (fun k => ‖star (haarMoment_pol i j k) ⬝ᵥ N *ᵥ haarMoment_pol i j k‖)
        (fun k => norm_nonneg _) (2 * p)
      rw [show (2 : ℝ) ^ (2 * p) = 4 ^ p by rw [pow_mul]; norm_num] at h4
      calc ‖N i j‖ ^ (2 * p) ≤ ((1 / 2 : ℝ) * ∑ k : Fin 4,
            ‖star (haarMoment_pol i j k) ⬝ᵥ N *ᵥ haarMoment_pol i j k‖) ^ (2 * p) :=
            pow_le_pow_left₀ (norm_nonneg _) hN _
        _ ≤ _ := h4
        _ = _ := by
            simp only [N, haarMoment_quad_conj]
    have hR : Integrable (fun U : Matrix.unitaryGroup (Fin W) ℂ =>
        4 ^ p * ∑ k : Fin 4, ‖star (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ haarMoment_pol i j k) ⬝ᵥ
          A₀ *ᵥ (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ haarMoment_pol i j k)‖ ^ (2 * p))
          (haarU W) :=
      (integrable_finsetSum _ fun k _ => hint _).const_mul _
    calc ∫ U, ‖((U : Matrix (Fin W) (Fin W) ℂ) * A₀ * star (U : Matrix (Fin W) (Fin W) ℂ)) i j‖ ^
            (2 * p) ∂(haarU W)
        ≤ ∫ U, 4 ^ p * ∑ k : Fin 4,
            ‖star (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ haarMoment_pol i j k) ⬝ᵥ
              A₀ *ᵥ (star (U : Matrix (Fin W) (Fin W) ℂ) *ᵥ haarMoment_pol i j k)‖ ^ (2 * p)
            ∂(haarU W) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun U => by positivity) hR
            (Filter.Eventually.of_forall hpt)
      _ = 4 ^ p * (4 * S) := by
          rw [integral_const_mul, integral_finsetSum _ fun k _ => hint _]
          simp only [hlaw _ (haarMoment_pol_unit hij _), Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          norm_num
      _ ≤ _ := hmain

end LSBA
