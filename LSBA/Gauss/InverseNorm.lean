import LSBA.Gauss.FixedVector

/-!
# Inverse-norm tail for a deformed GUE matrix

[APSSS, Theorem 1 (1.7)], GUE case: for `H = A + V`, `A` Hermitian and `V` the `n × n` GUE
matrix of (1.2) [eq:covariance], `P(‖H⁻¹‖ ≥ t n) ≤ P(‖H⁻¹‖_F ≥ t n) ≤ C / t`, with an absolute
constant. The proof tests `H⁻¹` on an independent standard complex Gaussian vector.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `E exp (-(s/2) y²) = (1 + s)^{-1/2}` for `y ~ N(0, 1)` and `s ≥ 0`. -/
private lemma inverseNorm_gauss_exp {s : ℝ} (hs : 0 ≤ s) :
    ∫ y : ℝ, Real.exp (-(s / 2) * y ^ 2) ∂(gaussianReal 0 1) = (Real.sqrt (1 + s))⁻¹ := by
  have ha : 0 < (1 + s) / 2 := by linarith
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hpt : ∀ y : ℝ, gaussianPDFReal 0 1 y • Real.exp (-(s / 2) * y ^ 2) =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-((1 + s) / 2) * y ^ 2) := by
    intro y
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_gaussian]
  have h2 : Real.sqrt (π / ((1 + s) / 2)) = Real.sqrt (2 * π) * (Real.sqrt (1 + s))⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [h2]
  have : Real.sqrt (2 * π) ≠ 0 := by positivity
  field_simp

/-- `E exp (-s |z|²) = (1 + s)⁻¹` for `z ~ cGauss` and `s ≥ 0`. -/
private lemma inverseNorm_cGauss_exp {s : ℝ} (hs : 0 ≤ s) :
    ∫ z : ℂ, Real.exp (-s * ‖z‖ ^ 2) ∂cGauss = (1 + s)⁻¹ := by
  unfold cGauss
  have hφ : Measurable fun y : Fin 2 → ℝ => ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y 0, y 1⟩ : ℂ) := by
    have : (fun y : Fin 2 → ℝ => ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y 0, y 1⟩ : ℂ)) =
        fun y => ((Real.sqrt 2)⁻¹ : ℂ) * ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) := by
      funext y
      rw [Complex.mk_eq_add_mul_I]
    rw [this]
    fun_prop
  rw [integral_map hφ.aemeasurable (by fun_prop)]
  have h : ∀ y : Fin 2 → ℝ, Real.exp (-s * ‖((Real.sqrt 2)⁻¹ : ℂ) * (⟨y 0, y 1⟩ : ℂ)‖ ^ 2) =
      ∏ i : Fin 2, Real.exp (-(s / 2) * y i ^ 2) := by
    intro y
    rw [Fin.prod_univ_two, ← Real.exp_add]
    congr 1
    rw [norm_mul, mul_pow, norm_inv, inv_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (by norm_num), Complex.sq_norm, Complex.normSq_mk]
    ring
  simp_rw [h]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (f := fun _ (y : ℝ) => Real.exp (-(s / 2) * y ^ 2))]
  simp only [inverseNorm_gauss_exp hs, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [inv_pow, Real.sq_sqrt (by positivity)]

/-- `E exp (-ξ ∑ₖ aₖ |xₖ|²) = ∏ₖ (1 + ξ aₖ)⁻¹` for `x ~ stdCGauss`, `aₖ ≥ 0`, `ξ ≥ 0`. -/
private lemma inverseNorm_laplace {ι : Type*} [Fintype ι] {a : ι → ℝ} (ha : ∀ k, 0 ≤ a k)
    {ξ : ℝ} (hξ : 0 ≤ ξ) :
    ∫ x : ι → ℂ, Real.exp (-ξ * ∑ k, a k * ‖x k‖ ^ 2) ∂(stdCGauss ι) =
      ∏ k, (1 + ξ * a k)⁻¹ := by
  have h : ∀ x : ι → ℂ, Real.exp (-ξ * ∑ k, a k * ‖x k‖ ^ 2) =
      ∏ k, Real.exp (-(ξ * a k) * ‖x k‖ ^ 2) := by
    intro x
    rw [← Real.exp_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [h]
  unfold stdCGauss
  rw [integral_fintype_prod_eq_prod (f := fun k (z : ℂ) => Real.exp (-(ξ * a k) * ‖z‖ ^ 2))]
  exact Finset.prod_congr rfl fun k _ => inverseNorm_cGauss_exp (mul_nonneg hξ (ha k))

/-- `1 + ∑ bₖ ≤ ∏ (1 + bₖ)` for `bₖ ≥ 0`. -/
private lemma inverseNorm_one_add_sum_le_prod {ι : Type*} (s : Finset ι) {b : ι → ℝ}
    (hb : ∀ k, 0 ≤ b k) : 1 + ∑ k ∈ s, b k ≤ ∏ k ∈ s, (1 + b k) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0 : 0 ≤ ∑ k ∈ s, b k := Finset.sum_nonneg fun k _ => hb k
    have h1 := hb a
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + b a) (sub_nonneg.mpr ih), mul_nonneg h1 h0]

/-- Small-ball bound for a weighted sum of `|xₖ|²`: `P(∑ aₖ |xₖ|² ≤ (∑ aₖ)/9) ≤ 1/2` for
`aₖ ≥ 0` with `∑ aₖ > 0`. -/
private lemma inverseNorm_diag_small {ι : Type*} [Fintype ι] {a : ι → ℝ} (ha : ∀ k, 0 ≤ a k)
    (hS : 0 < ∑ k, a k) :
    stdCGauss ι {x | ∑ k, a k * ‖x k‖ ^ 2 ≤ (∑ k, a k) / 9} ≤ 1 / 2 := by
  set S := ∑ k, a k with hSdef
  set ξ := 9 / S with hξ
  have hξ0 : 0 < ξ := by positivity
  have hY : Continuous fun x : ι → ℂ => ∑ k, a k * ‖x k‖ ^ 2 := by fun_prop
  have hYn : ∀ x : ι → ℂ, 0 ≤ ∑ k, a k * ‖x k‖ ^ 2 := fun x =>
    Finset.sum_nonneg fun k _ => mul_nonneg (ha k) (by positivity)
  set f : (ι → ℂ) → ℝ := fun x => Real.exp (-ξ * ∑ k, a k * ‖x k‖ ^ 2) with hf
  have hfc : Continuous f := by rw [hf]; fun_prop
  have hfi : Integrable f (stdCGauss ι) := by
    refine Integrable.of_bound hfc.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => ?_)
    rw [hf, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
    nlinarith [hYn x]
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := stdCGauss ι) (f := f)
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg _) hfi (Real.exp (-1))
  have hsub : {x : ι → ℂ | ∑ k, a k * ‖x k‖ ^ 2 ≤ S / 9} ⊆ {x | Real.exp (-1) ≤ f x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, hf] at hx ⊢
    rw [Real.exp_le_exp]
    have : ξ * ∑ k, a k * ‖x k‖ ^ 2 ≤ 1 := by
      calc ξ * ∑ k, a k * ‖x k‖ ^ 2 ≤ ξ * (S / 9) := by gcongr
        _ = 1 := by rw [hξ]; field_simp
    linarith
  have hint : ∫ x, f x ∂(stdCGauss ι) = ∏ k, (1 + ξ * a k)⁻¹ := inverseNorm_laplace ha hξ0.le
  have hprod : ∏ k, (1 + ξ * a k)⁻¹ ≤ (1 + ξ * S)⁻¹ := by
    rw [Finset.prod_inv_distrib]
    refine inv_anti₀ (by positivity) ?_
    have := inverseNorm_one_add_sum_le_prod Finset.univ (b := fun k => ξ * a k)
      (fun k => mul_nonneg hξ0.le (ha k))
    rwa [← Finset.mul_sum] at this
  have hξS : ξ * S = 9 := by rw [hξ]; field_simp
  have hreal : (stdCGauss ι).real {x | ∑ k, a k * ‖x k‖ ^ 2 ≤ S / 9} ≤ 1 / 2 := by
    have h1 : Real.exp (-1) * (stdCGauss ι).real {x | ∑ k, a k * ‖x k‖ ^ 2 ≤ S / 9} ≤
        (1 + ξ * S)⁻¹ := by
      calc _ ≤ Real.exp (-1) * (stdCGauss ι).real {x | Real.exp (-1) ≤ f x} := by
            exact mul_le_mul_of_nonneg_left (measureReal_mono (μ := stdCGauss ι) hsub)
              (Real.exp_nonneg _)
        _ ≤ ∫ x, f x ∂(stdCGauss ι) := hmark
        _ ≤ _ := by rw [hint]; exact hprod
    rw [hξS] at h1
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have h2 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
    have hm0 := measureReal_nonneg (μ := stdCGauss ι)
      (s := {x | ∑ k, a k * ‖x k‖ ^ 2 ≤ S / 9})
    nlinarith [Real.exp_pos 1, Real.exp_pos (-1)]
  calc _ = ENNReal.ofReal ((stdCGauss ι).real {x | ∑ k, a k * ‖x k‖ ^ 2 ≤ S / 9}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 1 / 2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        simp

/-- `w* w = ‖w‖₂²`. -/
private lemma inverseNorm_dot_self {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']

/-- A unitary matrix preserves `‖·‖₂`. -/
private lemma inverseNorm_l2Norm_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (w : ι → ℂ) : l2Norm ((U : Matrix ι ι ℂ) *ᵥ w) = l2Norm w := by
  have hU : star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  have h : star ((U : Matrix ι ι ℂ) *ᵥ w) ⬝ᵥ ((U : Matrix ι ι ℂ) *ᵥ w) = star w ⬝ᵥ w := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, hU, Matrix.one_mulVec]
  rw [inverseNorm_dot_self, inverseNorm_dot_self] at h
  unfold l2Norm
  rw [Complex.ofReal_injective h]

/-- `‖D y‖₂² = ∑ₖ λₖ² |yₖ|²` for a real diagonal matrix `D = diag(λ)`. -/
private lemma inverseNorm_l2Norm_diag_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ)
    (y : ι → ℂ) :
    l2Norm (Matrix.diagonal (fun j => (E j : ℂ)) *ᵥ y) ^ 2 = ∑ k, E k ^ 2 * ‖y k‖ ^ 2 := by
  unfold l2Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun k _ => by positivity)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- A nonzero Hermitian matrix: `P(‖M x‖₂ < ‖M‖_F / 3) ≤ 1/2` for `x ~ stdCGauss`. -/
private lemma inverseNorm_anticonc {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hF : 0 < ∑ i, ∑ j, ‖M i j‖ ^ 2) :
    stdCGauss ι {x | l2Norm (M *ᵥ x) < Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) / 3} ≤ 1 / 2 := by
  set U := hM.eigenvectorUnitary with hUdef
  set E := hM.eigenvalues with hEdef
  set D : Matrix ι ι ℂ := Matrix.diagonal fun j => (E j : ℂ) with hD
  have hMU : M = (U : Matrix ι ι ℂ) * D * star (U : Matrix ι ι ℂ) := by
    conv_lhs => rw [hM.spectral_theorem]
    rfl
  set Us : Matrix.unitaryGroup ι ℂ := star U with hUs
  have hUs' : (Us : Matrix ι ι ℂ) = star (U : Matrix ι ι ℂ) := rfl
  have hmp := measurePreserving_stdCGauss_unitary Us
  have hMx : ∀ x : ι → ℂ, M *ᵥ x = (U : Matrix ι ι ℂ) *ᵥ (D *ᵥ ((Us : Matrix ι ι ℂ) *ᵥ x)) := by
    intro x
    rw [hMU, hUs', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hsq : ∀ x : ι → ℂ, l2Norm (M *ᵥ x) ^ 2 = ∑ k, E k ^ 2 * ‖((Us : Matrix ι ι ℂ) *ᵥ x) k‖ ^ 2 :=
    fun x => by rw [hMx, inverseNorm_l2Norm_unitary, inverseNorm_l2Norm_diag_sq]
  -- the Frobenius norm of `M` is `∑ₖ λₖ²`
  have hFS : ∑ i, ∑ j, ‖M i j‖ ^ 2 = ∑ k, E k ^ 2 := by
    have h1 := lintegral_l2Norm_sq_stdCGauss M 0
    have h2 := lintegral_l2Norm_sq_stdCGauss D 0
    have hz : l2Norm (0 : ι → ℂ) = 0 := by simp [l2Norm]
    simp only [add_zero, Matrix.mulVec_zero, hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at h1 h2
    have hg : Measurable fun y : ι → ℂ => ENNReal.ofReal (l2Norm (D *ᵥ y) ^ 2) := by
      refine ENNReal.measurable_ofReal.comp ?_
      have : Continuous fun y : ι → ℂ => l2Norm (D *ᵥ y) := by
        unfold l2Norm
        fun_prop
      exact (this.pow 2).measurable
    have h3 : ∫⁻ x, ENNReal.ofReal (l2Norm (M *ᵥ x) ^ 2) ∂(stdCGauss ι) =
        ∫⁻ y, ENNReal.ofReal (l2Norm (D *ᵥ y) ^ 2) ∂(stdCGauss ι) := by
      rw [← hmp.lintegral_comp hg]
      refine lintegral_congr fun x => ?_
      simp only [hMx, inverseNorm_l2Norm_unitary]
    rw [h1, h2] at h3
    have hD2 : ∑ i, ∑ j, ‖D i j‖ ^ 2 = ∑ k, E k ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have : ∀ x, ‖D i x‖ ^ 2 = if i = x then E i ^ 2 else 0 := by
        intro x
        simp only [hD, Matrix.diagonal_apply]
        split_ifs <;> simp [Complex.norm_real, sq_abs]
      simp_rw [this]
      simp
    rw [hD2, ENNReal.ofReal_eq_ofReal_iff (by positivity)
      (Finset.sum_nonneg fun k _ => by positivity)] at h3
    exact h3
  have hpos : 0 < ∑ k, E k ^ 2 := hFS ▸ hF
  have hset : {x : ι → ℂ | l2Norm (M *ᵥ x) < Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) / 3} ⊆
      (fun x => (Us : Matrix ι ι ℂ) *ᵥ x) ⁻¹'
        {y | ∑ k, E k ^ 2 * ‖y k‖ ^ 2 ≤ (∑ k, E k ^ 2) / 9} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hx ⊢
    rw [← hsq, ← hFS]
    have h0 : 0 ≤ l2Norm (M *ᵥ x) := Real.sqrt_nonneg _
    have h1 : l2Norm (M *ᵥ x) ^ 2 ≤ (Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) / 3) ^ 2 :=
      pow_le_pow_left₀ h0 hx.le 2
    rw [div_pow, Real.sq_sqrt hF.le] at h1
    linarith
  have hSm : MeasurableSet {y : ι → ℂ | ∑ k, E k ^ 2 * ‖y k‖ ^ 2 ≤ (∑ k, E k ^ 2) / 9} :=
    measurableSet_le (by fun_prop) measurable_const
  calc _ ≤ stdCGauss ι ((fun x => (Us : Matrix ι ι ℂ) *ᵥ x) ⁻¹'
        {y | ∑ k, E k ^ 2 * ‖y k‖ ^ 2 ≤ (∑ k, E k ^ 2) / 9}) := measure_mono hset
    _ = stdCGauss ι {y | ∑ k, E k ^ 2 * ‖y k‖ ^ 2 ≤ (∑ k, E k ^ 2) / 9} :=
        hmp.measure_preimage hSm.nullMeasurableSet
    _ ≤ 1 / 2 := inverseNorm_diag_small (fun k => sq_nonneg (E k)) hpos

/-- Anti-concentration of a Hermitian matrix: if `3c ≤ ‖M‖_F` and `c > 0`, then
`P(‖M x‖₂ ≥ c) ≥ 1/2` for `x ~ stdCGauss`, in the form `1 ≤ 2 P(‖M x‖₂ ≥ c)`. -/
private lemma inverseNorm_anticonc_ge {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) {c : ℝ} (hc : 0 < c)
    (hcF : 3 * c ≤ Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2)) :
    1 ≤ 2 * stdCGauss ι {x | c ≤ l2Norm (M *ᵥ x)} := by
  have hF : 0 < ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
    rw [← Real.sqrt_pos]
    linarith
  have hB := inverseNorm_anticonc hM hF
  set B := {x : ι → ℂ | l2Norm (M *ᵥ x) < Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) / 3} with hBdef
  have hBm : MeasurableSet B := by
    refine measurableSet_lt ?_ measurable_const
    have : Continuous fun x : ι → ℂ => l2Norm (M *ᵥ x) := by
      unfold l2Norm
      fun_prop
    exact this.measurable
  have hsub : Bᶜ ⊆ {x : ι → ℂ | c ≤ l2Norm (M *ᵥ x)} := by
    intro x hx
    simp only [hBdef, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hx ⊢
    linarith
  have h1 : 1 ≤ 1 / 2 + stdCGauss ι {x | c ≤ l2Norm (M *ᵥ x)} := by
    calc (1 : ℝ≥0∞) = stdCGauss ι B + stdCGauss ι Bᶜ := (prob_add_prob_compl hBm).symm
      _ ≤ 1 / 2 + stdCGauss ι {x | c ≤ l2Norm (M *ᵥ x)} := add_le_add hB (measure_mono hsub)
  have h2 : (1 : ℝ≥0∞) / 2 ≤ stdCGauss ι {x | c ≤ l2Norm (M *ᵥ x)} := by
    have h3 : (1 : ℝ≥0∞) - 1 / 2 ≤ stdCGauss ι {x | c ≤ l2Norm (M *ᵥ x)} :=
      tsub_le_iff_left.mpr h1
    rwa [one_div, ENNReal.one_sub_inv_two, ← one_div] at h3
  calc (1 : ℝ≥0∞) = 2 * (1 / 2) := by
        rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
    _ ≤ 2 * stdCGauss ι {x | c ≤ l2Norm (M *ᵥ x)} := by gcongr

/-- `‖M v‖₂ ≤ ‖M‖_F ‖v‖₂`, with `‖M‖_F = (∑ᵢⱼ |Mᵢⱼ|²)^{1/2}`. -/
private lemma inverseNorm_l2Norm_mulVec_le {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    l2Norm (M *ᵥ v) ≤ Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) * l2Norm v := by
  have hrow : ∀ i, ‖(M *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ ^ 2) * (∑ j, ‖v j‖ ^ 2) := by
    intro i
    calc ‖(M *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ * ‖v j‖) ^ 2 := by
          gcongr
          simp only [Matrix.mulVec, dotProduct]
          exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  unfold l2Norm
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => hrow i

/-- `‖M‖ ≤ ‖M‖_F`: the operator norm is at most the Frobenius norm. -/
private lemma inverseNorm_opNorm_le_frob {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) : ‖M‖ ≤ Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have h := inverseNorm_l2Norm_mulVec_le M x.ofLp
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp] at h
  exact h

/-- The matrix inverse `X ↦ X⁻¹ = det(X)⁻¹ adj(X)` is Borel. -/
private lemma inverseNorm_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable fun X : Matrix ι ι ℂ => X⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have h : (fun X : Matrix ι ι ℂ => X⁻¹ i j) = fun X => (X.det)⁻¹ * X.adjugate i j := by
    funext X
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [h]
  have hd : Continuous fun X : Matrix ι ι ℂ => X.det := continuous_id.matrix_det
  have ha : Continuous fun X : Matrix ι ι ℂ => X.adjugate i j :=
    (continuous_id.matrix_adjugate).matrix_elem i j
  exact hd.measurable.inv.mul ha.measurable

/-- The GUE matrix of (1.2) [eq:covariance] is continuous in its coordinates. -/
private lemma inverseNorm_continuous_gueMat (n : ℕ) : Continuous (gueMat n) := by
  refine continuous_pi fun α => continuous_pi fun β => ?_
  simp only [gueMat, gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

/-- `‖·‖₂` is continuous. -/
private lemma inverseNorm_continuous_l2Norm {ι : Type*} [Fintype ι] :
    Continuous (l2Norm : (ι → ℂ) → ℝ) := by
  unfold l2Norm
  fun_prop

/-- `E‖x‖₂ ≤ √n` for `x ~ stdCGauss (Fin n)`, `n ≥ 1`, in the form
`∫ c ‖x‖₂ ≤ c √n` for every `c ≥ 0`. -/
private lemma inverseNorm_lintegral_l2Norm_le {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ x, ENNReal.ofReal (c * l2Norm x) ∂(stdCGauss (Fin n)) ≤
      ENNReal.ofReal (c * Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set s := Real.sqrt n with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hn0
  have hs2 : s ^ 2 = n := Real.sq_sqrt hn0.le
  have hnorm := lintegral_l2Norm_sq_stdCGauss (1 : Matrix (Fin n) (Fin n) ℂ) 0
  have hz : l2Norm (0 : Fin n → ℂ) = 0 := by simp [l2Norm]
  have hfrob : ∑ i : Fin n, ∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = n := by
    have : ∀ i j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = if i = j then 1 else 0 := by
      intro i j
      rw [Matrix.one_apply]
      split_ifs <;> simp
    simp_rw [this]
    simp
  simp only [Matrix.one_mulVec, add_zero, Matrix.mulVec_zero, hz, hfrob, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hnorm
  have hmeas : Measurable fun x : Fin n → ℂ => ENNReal.ofReal (l2Norm x ^ 2) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have : Continuous fun x : Fin n → ℂ => l2Norm x := by
      unfold l2Norm
      fun_prop
    exact (this.pow 2).measurable
  calc ∫⁻ x, ENNReal.ofReal (c * l2Norm x) ∂(stdCGauss (Fin n))
      ≤ ∫⁻ x, ENNReal.ofReal (c / (2 * s)) * (ENNReal.ofReal (l2Norm x ^ 2) + ENNReal.ofReal n)
          ∂(stdCGauss (Fin n)) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_add (by positivity) hn0.le,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 : 2 * s * l2Norm x ≤ l2Norm x ^ 2 + n := by
          nlinarith [sq_nonneg (l2Norm x - s)]
        calc c * l2Norm x = c / (2 * s) * (2 * s * l2Norm x) := by field_simp
          _ ≤ _ := by gcongr
    _ = ENNReal.ofReal (c / (2 * s)) * (ENNReal.ofReal n + ENNReal.ofReal n) := by
        rw [lintegral_const_mul (f := fun x => ENNReal.ofReal (l2Norm x ^ 2) + ENNReal.ofReal n) _
          (hmeas.add_const _), lintegral_add_right _ measurable_const, hnorm, lintegral_const,
          measure_univ, mul_one]
    _ = ENNReal.ofReal (c * s) := by
        rw [← ENNReal.ofReal_add hn0.le hn0.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← hs2]
        field_simp
        ring

/-- Frobenius form of [APSSS, Theorem 1 (1.7)]: `P(‖(A + V)⁻¹‖_F ≥ t n) ≤ C / t` for `n ≥ 1`,
every Hermitian `A` and `t > 0`. -/
theorem gueMat_inv_frob_tail : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (A : Matrix (Fin n) (Fin n) ℂ), A.IsHermitian → ∀ t : ℝ, 0 < t →
      μ n 1 {ω | t * n ≤ Real.sqrt (∑ i, ∑ j, ‖(A + gueMat n ω)⁻¹ i j‖ ^ 2)} ≤
        ENNReal.ofReal (C / t) := by
  obtain ⟨C₁, hC₁, h₁⟩ := gueMat_inv_mulVec_tail
  refine ⟨6 * C₁, by positivity, ?_⟩
  intro n hn A hA t ht
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hs2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hMm : Measurable fun ω : Ω n 1 => (A + gueMat n ω)⁻¹ :=
    inverseNorm_measurable_inv.comp
      (continuous_const.add (inverseNorm_continuous_gueMat n)).measurable
  have hMh : ∀ ω : Ω n 1, ((A + gueMat n ω)⁻¹).IsHermitian := fun ω =>
    (hA.add (gueBlock_isHermitian n 1 ω 0)).inv
  set T : Set (Ω n 1 × (Fin n → ℂ)) :=
    {p | t * n / 3 ≤ l2Norm ((A + gueMat n p.1)⁻¹ *ᵥ p.2)} with hT
  have hTm : MeasurableSet T := by
    refine measurableSet_le measurable_const ?_
    have hc : Continuous fun q : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) =>
        l2Norm (q.1 *ᵥ q.2) :=
      inverseNorm_continuous_l2Norm.comp (Continuous.matrix_mulVec continuous_fst continuous_snd)
    have hq : Measurable fun p : Ω n 1 × (Fin n → ℂ) => ((A + gueMat n p.1)⁻¹, p.2) :=
      (hMm.comp measurable_fst).prodMk measurable_snd
    have hcm := hc.measurable.comp hq
    exact hcm
  obtain ⟨E, hE⟩ : ∃ E : Set (Ω n 1), E =
      {ω | t * n ≤ Real.sqrt (∑ i, ∑ j, ‖(A + gueMat n ω)⁻¹ i j‖ ^ 2)} := ⟨_, rfl⟩
  rw [← hE]
  have hEm : MeasurableSet E := by
    rw [hE]
    refine measurableSet_le measurable_const ?_
    have : Continuous fun X : Matrix (Fin n) (Fin n) ℂ =>
        Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) := by fun_prop
    exact this.measurable.comp hMm
  -- for `ω ∈ E`, a standard complex Gaussian test vector has `‖H⁻¹ γ‖ ≥ t n / 3` with
  -- probability at least `1/2`
  have hstep1 : ∀ ω ∈ E, 1 ≤ 2 * stdCGauss (Fin n) (Prod.mk ω ⁻¹' T) := by
    intro ω hω
    have hω' : t * n ≤ Real.sqrt (∑ i, ∑ j, ‖(A + gueMat n ω)⁻¹ i j‖ ^ 2) := by
      rw [hE] at hω
      exact hω
    exact inverseNorm_anticonc_ge (hMh ω) (by positivity) (by linarith)
  have h2 : μ n 1 E ≤ ∫⁻ ω, 2 * stdCGauss (Fin n) (Prod.mk ω ⁻¹' T) ∂(μ n 1) := by
    calc μ n 1 E = ∫⁻ ω, E.indicator 1 ω ∂(μ n 1) := (lintegral_indicator_one hEm).symm
      _ ≤ _ := lintegral_mono fun ω => by
        by_cases hω : ω ∈ E
        · rw [Set.indicator_of_mem hω]
          exact hstep1 ω hω
        · rw [Set.indicator_of_notMem hω]
          exact zero_le
  -- Tonelli
  have h3 : ∫⁻ ω, stdCGauss (Fin n) (Prod.mk ω ⁻¹' T) ∂(μ n 1) =
      ∫⁻ x, μ n 1 ((fun ω => (ω, x)) ⁻¹' T) ∂(stdCGauss (Fin n)) := by
    rw [← Measure.prod_apply hTm, Measure.prod_apply_symm hTm]
  -- for a fixed test vector, the fixed-vector tail
  set c : ℝ := 3 * C₁ / (t * Real.sqrt n) with hc
  have hc0 : 0 ≤ c := by positivity
  have h4 : ∀ x : Fin n → ℂ, μ n 1 ((fun ω => (ω, x)) ⁻¹' T) ≤
      ENNReal.ofReal (c * l2Norm x) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      have : (fun ω : Ω n 1 => (ω, (0 : Fin n → ℂ))) ⁻¹' T = ∅ := by
        ext ω
        simp only [hT, Set.mem_preimage, Set.mem_ofPred_eq, Matrix.mulVec_zero,
          Set.mem_empty_iff_false, iff_false, not_le]
        have hz : l2Norm (0 : Fin n → ℂ) = 0 := by simp [l2Norm]
        rw [hz]
        positivity
      rw [this]
      exact (measure_empty (μ := μ n 1)).le.trans zero_le
    · have hx0 : 0 < l2Norm x := by
        rw [l2Norm_eq_norm_toLp, norm_pos_iff]
        intro h
        apply hx
        simpa using congrArg WithLp.ofLp h
      set t' : ℝ := t * Real.sqrt n / (3 * l2Norm x) with ht'def
      have ht' : 0 < t' := by positivity
      have hset : (fun ω : Ω n 1 => (ω, x)) ⁻¹' T =
          {ω | t' * Real.sqrt n * l2Norm x ≤ l2Norm ((A + gueMat n ω)⁻¹ *ᵥ x)} := by
        have : t' * Real.sqrt n * l2Norm x = t * n / 3 := by
          calc t' * Real.sqrt n * l2Norm x = t * (Real.sqrt n * Real.sqrt n) / 3 := by
                rw [ht'def]
                field_simp
            _ = t * n / 3 := by rw [hs2]
        rw [this]
        rfl
      rw [hset]
      refine (h₁ n A hA x hx t' ht').trans (le_of_eq ?_)
      congr 1
      rw [ht'def, hc]
      field_simp
  calc μ n 1 E ≤ ∫⁻ ω, 2 * stdCGauss (Fin n) (Prod.mk ω ⁻¹' T) ∂(μ n 1) := h2
    _ = 2 * ∫⁻ x, μ n 1 ((fun ω => (ω, x)) ⁻¹' T) ∂(stdCGauss (Fin n)) := by
        rw [lintegral_const_mul' _ _ (by norm_num), h3]
    _ ≤ 2 * ∫⁻ x, ENNReal.ofReal (c * l2Norm x) ∂(stdCGauss (Fin n)) := by
        gcongr with x
        exact h4 x
    _ ≤ 2 * ENNReal.ofReal (c * Real.sqrt n) := by
        gcongr
        exact inverseNorm_lintegral_l2Norm_le hn hc0
    _ = ENNReal.ofReal (6 * C₁ / t) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        rw [hc]
        field_simp
        ring

/-- Operator-norm form of [APSSS, Theorem 1 (1.7)]: `P(‖(A + V)⁻¹‖ ≥ t n) ≤ C / t` for `n ≥ 1`,
every Hermitian `A` and `t > 0`. -/
theorem gueMat_inv_norm_tail : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (A : Matrix (Fin n) (Fin n) ℂ), A.IsHermitian → ∀ t : ℝ, 0 < t →
      μ n 1 {ω | t * n ≤ ‖(A + gueMat n ω)⁻¹‖} ≤ ENNReal.ofReal (C / t) := by
  obtain ⟨C, hC, h⟩ := gueMat_inv_frob_tail
  refine ⟨C, hC, fun n hn A hA t ht => (measure_mono ?_).trans (h n hn A hA t ht)⟩
  intro ω hω
  exact le_trans hω (inverseNorm_opNorm_le_frob _)

end LSBA
