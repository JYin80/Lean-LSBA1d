import LSBA.Gauss.RectGauss
import LSBA.Gauss.ExpQuadratic

/-!
# Quadratic forms of a rectangular complex Gaussian matrix

For a deterministic square `M` and an `n × k` standard complex Gaussian matrix `G`, the centered
`k × k` quadratic form `G* M G - (Tr M) I` has operator norm at most
`C (√(k + s) ‖M‖_HS + (k + s) ‖M‖)` with failure `e^{-s}`; `M` need not be Hermitian. This is
the bound behind (9.47) [us:eq:quadratic] in Appendix G.2.1 [app:gaussian-projection-inputs].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### The exponential moment of `‖z‖²` -/

private lemma cgQuad_integral_aux {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) ∧
      ∫ y : ℝ, Real.exp (-a * y ^ 2) = Real.sqrt (π / a) := by
  exact ⟨integrable_exp_neg_mul_sq ha, integral_gaussian a⟩

private lemma cgQuad_pdf_mul (α y : ℝ) :
    gaussianPDFReal 0 1 y * Real.exp (α / 2 * y ^ 2) =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-((1 - α) / 2) * y ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- For `α < 1`, `E exp (α y² / 2) = (1 - α)^{-1/2}` under the standard Gaussian on `ℝ`, and the
integrand is integrable. -/
private lemma cgQuad_gauss_one {α : ℝ} (hα : α < 1) :
    Integrable (fun y : ℝ => Real.exp (α / 2 * y ^ 2)) (gaussianReal 0 1) ∧
      ∫ y : ℝ, Real.exp (α / 2 * y ^ 2) ∂(gaussianReal 0 1) = (Real.sqrt (1 - α))⁻¹ := by
  have ha : 0 < (1 - α) / 2 := by linarith
  obtain ⟨hI, hE⟩ := cgQuad_integral_aux ha
  refine ⟨?_, ?_⟩
  · rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
        (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)]
    refine (hI.const_mul ((Real.sqrt (2 * π))⁻¹)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 y), smul_eq_mul]
    exact (cgQuad_pdf_mul α y).symm
  · rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp only [smul_eq_mul, cgQuad_pdf_mul]
    rw [integral_const_mul, hE]
    have h1 : 0 < 1 - α := by linarith
    have h2 : Real.sqrt (π / ((1 - α) / 2)) = Real.sqrt (2 * π) * (Real.sqrt (1 - α))⁻¹ := by
      rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    rw [h2]
    have : Real.sqrt (2 * π) ≠ 0 := by positivity
    field_simp

private lemma cgQuad_cGauss_continuous : Continuous fun y : Fin 2 → ℝ =>
    ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y 0, y 1⟩ : ℂ) := by
  have : (fun y : Fin 2 → ℝ => ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y 0, y 1⟩ : ℂ)) =
      fun y => ((Real.sqrt 2)⁻¹ : ℂ) * ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) := by
    funext y
    rw [Complex.mk_eq_add_mul_I]
  rw [this]
  fun_prop

/-- `E exp (a |z|²) = (1 - a)⁻¹` for `z` standard complex Gaussian and `a < 1`, with integrable
integrand. -/
private lemma cgQuad_cGauss_exp {a : ℝ} (ha : a < 1) :
    Integrable (fun z : ℂ => Real.exp (a * ‖z‖ ^ 2)) cGauss ∧
      ∫ z : ℂ, Real.exp (a * ‖z‖ ^ 2) ∂cGauss = (1 - a)⁻¹ := by
  have hφ := cgQuad_cGauss_continuous
  have hf : Continuous fun z : ℂ => Real.exp (a * ‖z‖ ^ 2) := by fun_prop
  have hcomp : ∀ y : Fin 2 → ℝ, Real.exp (a * ‖((Real.sqrt 2)⁻¹ : ℂ) * (⟨y 0, y 1⟩ : ℂ)‖ ^ 2) =
      ∏ i : Fin 2, Real.exp (a / 2 * y i ^ 2) := by
    intro y
    rw [← Real.exp_sum, Fin.sum_univ_two]
    congr 1
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im]
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h3 : (Real.sqrt 2) ≠ 0 := by positivity
    simp
    field_simp
    rw [h2]
  unfold cGauss
  have hI : Integrable (fun y : Fin 2 → ℝ => ∏ i : Fin 2, Real.exp (a / 2 * y i ^ 2))
      (stdGauss (Fin 2)) :=
    Integrable.fintype_prod (f := fun _ (y : ℝ) => Real.exp (a / 2 * y ^ 2))
      (fun _ => (cgQuad_gauss_one ha).1)
  refine ⟨?_, ?_⟩
  · rw [integrable_map_measure hf.aestronglyMeasurable hφ.measurable.aemeasurable]
    refine hI.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Function.comp_apply]
    exact (hcomp y).symm
  · rw [integral_map hφ.measurable.aemeasurable hf.aestronglyMeasurable]
    simp only [hcomp]
    unfold stdGauss
    rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin 2 => gaussianReal 0 1)
      (fun _ y => Real.exp (a / 2 * y ^ 2))]
    simp only [(cgQuad_gauss_one ha).2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [inv_pow, Real.sq_sqrt (by linarith)]

/-! ### The exponential moment of a Hermitian quadratic form -/

private lemma cgQuad_inv_le_exp {b : ℝ} (hb : |b| ≤ 1 / 2) :
    (1 - b)⁻¹ ≤ Real.exp (b + 2 * b ^ 2) := by
  have hb2 := abs_le.1 hb
  have h1 : 0 < 1 - b := by linarith
  have h2 : (1 - b)⁻¹ ≤ 1 + (b + 2 * b ^ 2) := by
    rw [inv_eq_one_div, div_le_iff₀ h1]
    nlinarith [mul_nonneg (sq_nonneg b) (by linarith : (0 : ℝ) ≤ 1 - 2 * b)]
  exact h2.trans (by linarith [Real.add_one_le_exp (b + 2 * b ^ 2)])

/-- The exponential moment of a weighted sum of `|z_i|²`. -/
private lemma cgQuad_mgf_diag {n : ℕ} (l : Fin n → ℝ) {t : ℝ} (ht : ∀ i, |t * l i| ≤ 1 / 2) :
    Integrable (fun z : Fin n → ℂ => Real.exp (t * ∑ i, l i * ‖z i‖ ^ 2)) (stdCGauss (Fin n)) ∧
      ∫ z, Real.exp (t * ∑ i, l i * ‖z i‖ ^ 2) ∂(stdCGauss (Fin n)) ≤
        Real.exp (t * ∑ i, l i + 2 * t ^ 2 * ∑ i, l i ^ 2) := by
  have hrw : ∀ z : Fin n → ℂ, Real.exp (t * ∑ i, l i * ‖z i‖ ^ 2) =
      ∏ i, Real.exp (t * l i * ‖z i‖ ^ 2) := by
    intro z
    rw [← Real.exp_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hrw]
  have h1 : ∀ i, t * l i < 1 := fun i => by have := (abs_le.1 (ht i)).2; linarith
  refine ⟨Integrable.fintype_prod (f := fun i (z : ℂ) => Real.exp (t * l i * ‖z‖ ^ 2))
    (fun i => (cgQuad_cGauss_exp (h1 i)).1), ?_⟩
  unfold stdCGauss
  rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin n => cGauss)
    (fun i z => Real.exp (t * l i * ‖z‖ ^ 2))]
  calc ∏ i, ∫ z, Real.exp (t * l i * ‖z‖ ^ 2) ∂cGauss = ∏ i, (1 - t * l i)⁻¹ :=
        Finset.prod_congr rfl fun i _ => (cgQuad_cGauss_exp (h1 i)).2
    _ ≤ ∏ i, Real.exp (t * l i + 2 * (t * l i) ^ 2) :=
        Finset.prod_le_prod₀ (fun i _ => inv_nonneg.2 (by linarith [h1 i]))
          (fun i _ => cgQuad_inv_le_exp (ht i))
    _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring

private lemma cgQuad_l2Norm_smul {ι : Type*} [Fintype ι] (c : ℂ) (v : ι → ℂ) :
    l2Norm (c • v) = ‖c‖ * l2Norm v := by
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, WithLp.toLp_smul, norm_smul]

/-- The spectral data of a Hermitian matrix: a unitary `U` and real eigenvalues `l` with
`(Uz)* H (Uz) = ∑ l_i |z_i|²`, `Re Tr H = ∑ l_i`, `‖H‖_HS² = ∑ l_i²` and `|l_i| ≤ ‖H‖`. -/
private lemma cgQuad_herm_spectral {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) :
    ∃ (U : Matrix.unitaryGroup (Fin n) ℂ) (l : Fin n → ℝ),
      (∀ z : Fin n → ℂ,
        (star ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z) ⬝ᵥ
          (H *ᵥ ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z))).re = ∑ i, l i * ‖z i‖ ^ 2) ∧
      H.trace.re = ∑ i, l i ∧ ∑ i, ∑ j, ‖H i j‖ ^ 2 = ∑ i, l i ^ 2 ∧ ∀ i, |l i| ≤ ‖H‖ := by
  set Um : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hUm
  set l : Fin n → ℝ := hH.eigenvalues with hl
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => ((l i : ℝ) : ℂ)) with hD
  have hspec : H = Um * D * star Um := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [Function.comp_def] using this
  have hU1 : star Um * Um = 1 := Matrix.mem_unitaryGroup_iff'.1 hH.eigenvectorUnitary.2
  have hU2 : Um * star Um = 1 := Matrix.mem_unitaryGroup_iff.1 hH.eigenvectorUnitary.2
  refine ⟨hH.eigenvectorUnitary, l, ?_, ?_, ?_, ?_⟩
  · intro z
    have h1 : H *ᵥ (Um *ᵥ z) = Um *ᵥ (D *ᵥ z) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hspec, Matrix.mul_assoc, Matrix.mul_assoc,
        hU1, Matrix.mul_one]
    have h2 : star (Um *ᵥ z) ⬝ᵥ (Um *ᵥ (D *ᵥ z)) = star z ⬝ᵥ (D *ᵥ z) := by
      rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        ← Matrix.star_eq_conjTranspose, hU1, Matrix.vecMul_one]
    rw [h1, h2]
    simp only [dotProduct, Pi.star_apply, hD, Matrix.mulVec_diagonal, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : star (z i) * (((l i : ℝ) : ℂ) * z i) = ((l i * ‖z i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, mul_left_comm, Complex.conj_mul']
      push_cast
      ring
    rw [this, Complex.ofReal_re]
  · rw [hH.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
  · have hc : ((∑ i, ∑ j, ‖H i j‖ ^ 2 : ℝ) : ℂ) = ((∑ i, l i ^ 2 : ℝ) : ℂ) := by
      have e1 : ((∑ i, ∑ j, ‖H i j‖ ^ 2 : ℝ) : ℂ) = (Hᴴ * H).trace := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
          RCLike.star_def, Complex.conj_mul']
        push_cast
        rw [Finset.sum_comm]
      have e2 : Hᴴ * H = Um * (D * D) * star Um := by
        rw [hH.eq, hspec]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (star Um) Um, hU1, Matrix.one_mul]
      have e3 : (Um * (D * D) * star Um).trace = ((∑ i, l i ^ 2 : ℝ) : ℂ) := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul, hD,
          Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
        push_cast
        exact Finset.sum_congr rfl fun i _ => (sq _).symm
      rw [e1, e2, e3]
    exact_mod_cast hc
  · intro i
    set e := hH.eigenvectorBasis i with he
    have h1 := hH.mulVec_eigenvectorBasis i
    have h2 : l2Norm e.ofLp = 1 := by
      rw [l2Norm_eq_norm_toLp]
      exact hH.eigenvectorBasis.norm_eq_one i
    have h3 := l2Norm_mulVec_le H e.ofLp
    have h5 : hH.eigenvalues i • (hH.eigenvectorBasis i).ofLp =
        ((hH.eigenvalues i : ℝ) : ℂ) • (hH.eigenvectorBasis i).ofLp := by
      funext j
      simp [Complex.real_smul]
    rw [he, h1, h5, cgQuad_l2Norm_smul, h2] at h3
    have h4 : ‖((l i : ℝ) : ℂ)‖ = |l i| := Complex.norm_real _ |>.trans (Real.norm_eq_abs _)
    simpa [h4] using h3

/-- `E exp (t w* H w) ≤ exp (t Re Tr H + 2 t² ‖H‖_HS²)` for a Hermitian `H`, `|t| ‖H‖ ≤ 1/2` and
`w` standard complex Gaussian. -/
private lemma cgQuad_mgf_herm {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    {L t : ℝ} (hL : ‖H‖ ≤ L) (ht : |t| * L ≤ 1 / 2) :
    Integrable (fun w : Fin n → ℂ => Real.exp (t * (star w ⬝ᵥ (H *ᵥ w)).re))
        (stdCGauss (Fin n)) ∧
      ∫ w, Real.exp (t * (star w ⬝ᵥ (H *ᵥ w)).re) ∂(stdCGauss (Fin n)) ≤
        Real.exp (t * H.trace.re + 2 * t ^ 2 * ∑ i, ∑ j, ‖H i j‖ ^ 2) := by
  obtain ⟨U, l, hform, htr, hhs, hlH⟩ := cgQuad_herm_spectral hH
  have hT := measurePreserving_stdCGauss_unitary U
  have ht' : ∀ i, |t * l i| ≤ 1 / 2 := fun i => by
    rw [abs_mul]
    calc |t| * |l i| ≤ |t| * L :=
          mul_le_mul_of_nonneg_left ((hlH i).trans hL) (abs_nonneg _)
      _ ≤ 1 / 2 := ht
  obtain ⟨hI, hE⟩ := cgQuad_mgf_diag l ht'
  have hg : Continuous (fun w : Fin n → ℂ => Real.exp (t * (star w ⬝ᵥ (H *ᵥ w)).re)) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hcomp : ∀ z : Fin n → ℂ,
      Real.exp (t * (star ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z) ⬝ᵥ
        (H *ᵥ ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z))).re) =
        Real.exp (t * ∑ i, l i * ‖z i‖ ^ 2) := fun z => by rw [hform z]
  refine ⟨?_, ?_⟩
  · rw [← hT.integrable_comp hg.aestronglyMeasurable]
    exact (show Integrable _ _ from hI).congr (Filter.Eventually.of_forall fun z => (hcomp z).symm)
  · have h1 : ∫ w, Real.exp (t * (star w ⬝ᵥ (H *ᵥ w)).re) ∂(stdCGauss (Fin n)) =
        ∫ z, Real.exp (t * (star ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z) ⬝ᵥ
          (H *ᵥ ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z))).re) ∂(stdCGauss (Fin n)) := by
      rw [← integral_map hT.measurable.aemeasurable hg.aestronglyMeasurable, hT.map_eq]
    rw [h1]
    simp only [hcomp]
    refine hE.trans (le_of_eq ?_)
    rw [htr, hhs]

/-! ### The tail of a centered Hermitian quadratic form -/

/-- Chernoff bound from a sub-exponential moment estimate: if `E exp (t Z) ≤ exp (2 t² σ²)` for
`0 ≤ t ≤ 1/(2L)`, then `P(Z > 3 √T σ + 4 T L) ≤ e^{-T}`. -/
private lemma cgQuad_chernoff {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Ω → ℝ} {σ L : ℝ} (hσ : 0 < σ) (hL : 0 < L)
    (hZ : ∀ t : ℝ, 0 ≤ t → t * L ≤ 1 / 2 →
      Integrable (fun ω => Real.exp (t * Z ω)) μ ∧
        ∫ ω, Real.exp (t * Z ω) ∂μ ≤ Real.exp (2 * t ^ 2 * σ ^ 2))
    {T a : ℝ} (hT : 0 ≤ T) (ha : 3 * Real.sqrt T * σ + 4 * T * L ≤ a) :
    μ {ω | a < Z ω} ≤ ENNReal.ofReal (Real.exp (-T)) := by
  have hu0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have huT : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT
  have ha0 : 0 ≤ a := by nlinarith [mul_nonneg hu0 hσ.le, mul_nonneg hT hL.le]
  have hσ2 : 0 < σ ^ 2 := by positivity
  set t : ℝ := min (a / (4 * σ ^ 2)) (1 / (2 * L)) with ht
  have ht0 : 0 ≤ t := le_min (by positivity) (by positivity)
  have htL : t * L ≤ 1 / 2 := by
    calc t * L ≤ 1 / (2 * L) * L := mul_le_mul_of_nonneg_right (min_le_right _ _) hL.le
      _ = 1 / 2 := by field_simp
  have h4 : 4 * σ ^ 2 * t ≤ a := by
    have : t ≤ a / (4 * σ ^ 2) := min_le_left _ _
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  have hta : 2 * T ≤ t * a := by
    rcases min_cases (a / (4 * σ ^ 2)) (1 / (2 * L)) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [ht, h, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have h3 : 3 * Real.sqrt T * σ ≤ a := by nlinarith [mul_nonneg hT hL.le]
      have h5 : (3 * Real.sqrt T * σ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
      have h6 : (3 * Real.sqrt T * σ) ^ 2 = 9 * T * σ ^ 2 := by
        rw [mul_pow, mul_pow, huT]; ring
      nlinarith [mul_nonneg hT hσ2.le]
    · rw [ht, h, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg hT hL.le]
  obtain ⟨hint, hle⟩ := hZ t ht0 htL
  have hM := measure_ge_le_exp_mul_mgf (μ := μ) (X := Z) a ht0 hint
  have hmgf : mgf Z μ t ≤ Real.exp (2 * t ^ 2 * σ ^ 2) := hle
  have hexp : -t * a + 2 * t ^ 2 * σ ^ 2 ≤ -T := by nlinarith
  calc μ {ω | a < Z ω} ≤ μ {ω | a ≤ Z ω} := measure_mono fun ω hω => (le_of_lt hω : a ≤ Z ω)
    _ = ENNReal.ofReal (μ.real {ω | a ≤ Z ω}) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-T)) := by
        refine ENNReal.ofReal_le_ofReal (hM.trans ?_)
        calc Real.exp (-t * a) * mgf Z μ t ≤ Real.exp (-t * a) * Real.exp (2 * t ^ 2 * σ ^ 2) :=
              mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
          _ = Real.exp (-t * a + 2 * t ^ 2 * σ ^ 2) := (Real.exp_add _ _).symm
          _ ≤ Real.exp (-T) := Real.exp_le_exp.2 hexp

private lemma cgQuad_hs_pos {n m : ℕ} {H : Matrix (Fin n) (Fin m) ℂ} (hH0 : H ≠ 0) :
    0 < ∑ i, ∑ j, ‖H i j‖ ^ 2 := by
  by_contra hle
  have hz : ∑ i, ∑ j, ‖H i j‖ ^ 2 = 0 :=
    le_antisymm (not_lt.1 hle)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)
  refine hH0 ?_
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => by positivity)).1 hz i (Finset.mem_univ i)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h1 j
    (Finset.mem_univ j)
  simpa using h2

/-- The upper tail of the centered quadratic form of a Hermitian matrix. -/
private lemma cgQuad_tail {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    {σ L T : ℝ} (hσ : Real.sqrt (∑ i, ∑ j, ‖H i j‖ ^ 2) ≤ σ) (hL : ‖H‖ ≤ L) (hT : 0 ≤ T) :
    stdCGauss (Fin n)
        {w | 3 * Real.sqrt T * σ + 4 * T * L < (star w ⬝ᵥ (H *ᵥ w)).re - H.trace.re} ≤
      ENNReal.ofReal (Real.exp (-T)) := by
  have hσ0 : 0 ≤ σ := (Real.sqrt_nonneg _).trans hσ
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hL
  have hu0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  by_cases hH0 : H = 0
  · subst hH0
    have : {w : Fin n → ℂ | 3 * Real.sqrt T * σ + 4 * T * L <
        (star w ⬝ᵥ ((0 : Matrix (Fin n) (Fin n) ℂ) *ᵥ w)).re -
          (0 : Matrix (Fin n) (Fin n) ℂ).trace.re} = ∅ := by
      ext w
      simp only [Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re, Matrix.trace_zero,
        sub_self, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      positivity
    rw [this, measure_empty]
    exact zero_le
  · have hpos := cgQuad_hs_pos hH0
    have hσH : 0 < Real.sqrt (∑ i, ∑ j, ‖H i j‖ ^ 2) := Real.sqrt_pos.2 hpos
    have hLH : 0 < ‖H‖ := norm_pos_iff.2 hH0
    have hσH2 : Real.sqrt (∑ i, ∑ j, ‖H i j‖ ^ 2) ^ 2 = ∑ i, ∑ j, ‖H i j‖ ^ 2 :=
      Real.sq_sqrt hpos.le
    refine cgQuad_chernoff (μ := stdCGauss (Fin n))
      (Z := fun w => (star w ⬝ᵥ (H *ᵥ w)).re - H.trace.re) hσH hLH ?_ hT ?_
    · intro t ht0 htL
      obtain ⟨hI, hE⟩ := cgQuad_mgf_herm hH (L := ‖H‖) le_rfl (by rwa [abs_of_nonneg ht0])
      have e : ∀ w : Fin n → ℂ, Real.exp (t * ((star w ⬝ᵥ (H *ᵥ w)).re - H.trace.re)) =
          Real.exp (t * (star w ⬝ᵥ (H *ᵥ w)).re) * Real.exp (-(t * H.trace.re)) := by
        intro w
        rw [← Real.exp_add]
        congr 1
        ring
      simp only [e]
      refine ⟨hI.mul_const _, ?_⟩
      rw [integral_mul_const]
      calc (∫ w, Real.exp (t * (star w ⬝ᵥ (H *ᵥ w)).re) ∂(stdCGauss (Fin n))) *
            Real.exp (-(t * H.trace.re))
          ≤ Real.exp (t * H.trace.re + 2 * t ^ 2 * ∑ i, ∑ j, ‖H i j‖ ^ 2) *
            Real.exp (-(t * H.trace.re)) :=
            mul_le_mul_of_nonneg_right hE (Real.exp_pos _).le
        _ = Real.exp (2 * t ^ 2 * Real.sqrt (∑ i, ∑ j, ‖H i j‖ ^ 2) ^ 2) := by
            rw [← Real.exp_add, hσH2]
            congr 1
            ring
    · nlinarith [mul_nonneg hu0 (sub_nonneg.2 hσ), mul_nonneg hT (sub_nonneg.2 hL)]

/-- The two-sided tail of the centered quadratic form of a Hermitian matrix. -/
private lemma cgQuad_tail_abs {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    {σ L T : ℝ} (hσ : Real.sqrt (∑ i, ∑ j, ‖H i j‖ ^ 2) ≤ σ) (hL : ‖H‖ ≤ L) (hT : 0 ≤ T) :
    stdCGauss (Fin n)
        {w | 3 * Real.sqrt T * σ + 4 * T * L < |(star w ⬝ᵥ (H *ᵥ w)).re - H.trace.re|} ≤
      2 * ENNReal.ofReal (Real.exp (-T)) := by
  have h1 := cgQuad_tail hH hσ hL hT
  have hH' : (-H).IsHermitian := hH.neg
  have h2 := cgQuad_tail hH' (σ := σ) (L := L) (T := T)
    (by simpa using hσ) (by simpa using hL) hT
  calc _ ≤ stdCGauss (Fin n)
        ({w | 3 * Real.sqrt T * σ + 4 * T * L < (star w ⬝ᵥ (H *ᵥ w)).re - H.trace.re} ∪
          {w | 3 * Real.sqrt T * σ + 4 * T * L <
            (star w ⬝ᵥ ((-H) *ᵥ w)).re - (-H).trace.re}) := by
        refine measure_mono fun w hw => ?_
        simp only [Set.mem_ofPred_eq, Set.mem_union, Matrix.neg_mulVec, dotProduct_neg,
          Complex.neg_re, Matrix.trace_neg] at hw ⊢
        rcases lt_abs.1 hw with h | h
        · exact Or.inl h
        · right; linarith
    _ ≤ _ := (measure_union_le _ _).trans (by rw [two_mul]; exact add_le_add h1 h2)

/-! ### The law of `G v` -/

/-- A unit vector `v` of `ℂ^k` is a row of a unitary matrix. -/
private lemma cgQuad_unitary_row {k : ℕ} {v : Fin k → ℂ} (hv : ∑ j, ‖v j‖ ^ 2 = 1) :
    ∃ (U : Matrix.unitaryGroup (Fin k) ℂ) (i₀ : Fin k),
      ∀ j, (U : Matrix (Fin k) (Fin k) ℂ) i₀ j = v j := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      simp at hv
    · exact h
  set i₀ : Fin k := ⟨0, hk⟩ with hi₀
  set u : EuclideanSpace ℂ (Fin k) := WithLp.toLp 2 (fun j => star (v j)) with hu
  have hu1 : ‖u‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [hu, hv]
  have hon : Orthonormal ℂ (({i₀} : Set (Fin k)).domRestrict (fun _ => u)) := by
    refine ⟨fun i => hu1, fun i j hij => ?_⟩
    exact absurd (Subtype.ext ((Set.mem_singleton_iff.1 i.2).trans
      (Set.mem_singleton_iff.1 j.2).symm)) hij
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp) hon
  have hbi : b i₀ = u := hb i₀ rfl
  have hB := OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
    (EuclideanSpace.basisFun (Fin k) ℂ) b
  refine ⟨⟨star ((EuclideanSpace.basisFun (Fin k) ℂ).toBasis.toMatrix b), ?_⟩, i₀, fun j => ?_⟩
  · exact Unitary.star_mem hB
  · change star ((EuclideanSpace.basisFun (Fin k) ℂ).toBasis.toMatrix b) i₀ j = v j
    rw [Matrix.star_apply, Module.Basis.toMatrix_apply, hbi]
    simp [hu]

/-- A unit linear functional of a standard complex Gaussian vector is a standard complex
Gaussian. -/
private lemma cgQuad_map_functional {k : ℕ} {v : Fin k → ℂ} (hv : ∑ j, ‖v j‖ ^ 2 = 1) :
    (stdCGauss (Fin k)).map (fun r : Fin k → ℂ => ∑ j, r j * v j) = cGauss := by
  obtain ⟨U, i₀, hU⟩ := cgQuad_unitary_row hv
  have hP := (measurePreserving_eval (fun _ : Fin k => cGauss) i₀).comp
    (measurePreserving_stdCGauss_unitary U)
  have : (fun r : Fin k → ℂ => ∑ j, r j * v j) =
      (Function.eval i₀) ∘ (fun r => (U : Matrix (Fin k) (Fin k) ℂ) *ᵥ r) := by
    funext r
    simp only [Function.comp, Function.eval, Matrix.mulVec, dotProduct, hU]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [this]
  exact hP.map_eq

/-- Grouping the entries of an `n × k` array by rows carries the product of `n` copies of
`stdCGauss (Fin k)` to `stdCGauss (Fin n × Fin k)`. -/
private lemma cgQuad_map_uncurry (n k : ℕ) :
    (Measure.pi fun _ : Fin n => stdCGauss (Fin k)).map
      (fun (r : Fin n → Fin k → ℂ) (p : Fin n × Fin k) => r p.1 p.2) =
        stdCGauss (Fin n × Fin k) := by
  have hm : Measurable (fun (r : Fin n → Fin k → ℂ) (p : Fin n × Fin k) => r p.1 p.2) := by
    refine measurable_pi_iff.mpr fun p => ?_
    exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  symm
  unfold stdCGauss
  refine Measure.pi_eq fun s hs => ?_
  have hm' : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [Measure.map_apply hm hm']
  have hpre : (fun (r : Fin n → Fin k → ℂ) (p : Fin n × Fin k) => r p.1 p.2) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun i : Fin n => Set.univ.pi fun j : Fin k => s (i, j) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp only [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- For a unit vector `v`, the vector `G v` of an `n × k` standard complex Gaussian matrix `G` is a
standard complex Gaussian vector. -/
private lemma cgQuad_measurePreserving_mulVec {n k : ℕ} {v : Fin k → ℂ}
    (hv : ∑ j, ‖v j‖ ^ 2 = 1) :
    MeasurePreserving (fun x : Fin n × Fin k → ℂ => cgMat x *ᵥ v) (stdCGauss (Fin n × Fin k))
      (stdCGauss (Fin n)) := by
  have hF : Measurable (fun x : Fin n × Fin k → ℂ => cgMat x *ᵥ v) :=
    (Continuous.matrix_mulVec (by unfold cgMat; fun_prop) continuous_const).measurable
  have hu : Measurable (fun (r : Fin n → Fin k → ℂ) (p : Fin n × Fin k) => r p.1 p.2) := by
    refine measurable_pi_iff.mpr fun p => ?_
    exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  have hf : Measurable (fun r : Fin k → ℂ => ∑ j, r j * v j) := by fun_prop
  refine ⟨hF, ?_⟩
  rw [← cgQuad_map_uncurry n k, Measure.map_map hF hu]
  have hcomp : (fun x : Fin n × Fin k → ℂ => cgMat x *ᵥ v) ∘
      (fun (r : Fin n → Fin k → ℂ) (p : Fin n × Fin k) => r p.1 p.2) =
      fun (r : Fin n → Fin k → ℂ) (i : Fin n) => ∑ j, r i j * v j := by
    funext r i
    simp [cgMat, Matrix.mulVec, dotProduct]
  rw [hcomp, Measure.pi_map_pi (fun _ => hf.aemeasurable), cgQuad_map_functional hv]
  rfl

/-! ### The net argument for a Hermitian matrix -/

/-- The operator norm of a Hermitian matrix is at most `ρ` if `|y* K y| ≤ ρ` on the unit sphere. -/
private lemma cgQuad_herm_norm_le {k : ℕ} {K : Matrix (Fin k) (Fin k) ℂ} (hK : K.IsHermitian)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ y : Fin k → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 → |(star y ⬝ᵥ (K *ᵥ y)).re| ≤ ρ) : ‖K‖ ≤ ρ := by
  set T := Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) K with hT
  have hsymm : (T : EuclideanSpace ℂ (Fin k) →ₗ[ℂ] EuclideanSpace ℂ (Fin k)).IsSymmetric := by
    rw [hT, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.2 hK
  have hnorm : ‖K‖ = ‖T‖ := rfl
  rw [hnorm, T.norm_eq_iSup_rayleighQuotient hsymm]
  refine ciSup_le fun x => ?_
  by_cases hx : x = 0
  · rw [hx, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero]
    exact hρ
  · have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
    set y : EuclideanSpace ℂ (Fin k) := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hy
    have hy1 : ‖y‖ = 1 := by
      rw [hy, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hxn,
        inv_mul_cancel₀ hxn.ne']
    have hR : T.rayleighQuotient x = T.rayleighQuotient y := by
      rw [hy, ContinuousLinearMap.rayleigh_smul]
      exact_mod_cast (inv_ne_zero hxn.ne')
    rw [hR]
    have hsum : ∑ i, ‖y.ofLp i‖ ^ 2 = 1 := by
      have := EuclideanSpace.norm_sq_eq y
      rw [hy1] at this
      simpa using this.symm
    have hq : T.rayleighQuotient y = (star y.ofLp ⬝ᵥ (K *ᵥ y.ofLp)).re := by
      rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, hy1,
        one_pow, div_one, EuclideanSpace.inner_eq_star_dotProduct, hT,
        Matrix.ofLp_toEuclideanCLM, Matrix.star_mulVec, dotProduct_comm,
        ← Matrix.dotProduct_mulVec, hK.eq]
      rfl
    rw [hq]
    exact h y.ofLp hsum

/-- Cauchy–Schwarz: `|a* b| ≤ ‖a‖₂ ‖b‖₂`. -/
private lemma cgQuad_cs {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖star a ⬝ᵥ b‖ ≤ l2Norm a * l2Norm b := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 a : EuclideanSpace ℂ ι) (WithLp.toLp 2 b)
  rw [EuclideanSpace.inner_eq_star_dotProduct, ← l2Norm_eq_norm_toLp, ← l2Norm_eq_norm_toLp] at h
  simpa [dotProduct_comm] using h

private lemma cgQuad_l2Norm_of_unit {ι : Type*} [Fintype ι] {y : ι → ℂ} (hy : ∑ i, ‖y i‖ ^ 2 = 1) :
    l2Norm y = 1 := by
  rw [l2Norm, hy, Real.sqrt_one]

/-- A `1/4`-net of the unit sphere controls the operator norm of a Hermitian matrix: if
`|v* K v| ≤ a` at every net point, then `‖K‖ ≤ 2a`. -/
private lemma cgQuad_net_herm {k : ℕ} {K : Matrix (Fin k) (Fin k) ℂ} (hK : K.IsHermitian)
    {N : Finset (Fin k → ℂ)} {a : ℝ} (ha : 0 ≤ a) (hNu : ∀ v ∈ N, ∑ i, ‖v i‖ ^ 2 = 1)
    (hNc : ∀ y : Fin k → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 →
      ∃ v ∈ N, ∑ i, ‖y i - v i‖ ^ 2 ≤ (1 / 4) ^ 2)
    (hN : ∀ v ∈ N, |(star v ⬝ᵥ (K *ᵥ v)).re| ≤ a) : ‖K‖ ≤ 2 * a := by
  have hκ := norm_nonneg K
  have key : ∀ y : Fin k → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 →
      |(star y ⬝ᵥ (K *ᵥ y)).re| ≤ a + ‖K‖ / 2 := by
    intro y hy
    obtain ⟨v, hv, hyv⟩ := hNc y hy
    have hv1 := cgQuad_l2Norm_of_unit (hNu v hv)
    have hy1 := cgQuad_l2Norm_of_unit hy
    have hd : l2Norm (y - v) ≤ 1 / 4 := by
      rw [l2Norm]
      refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
      simpa using hyv
    have e : star y ⬝ᵥ (K *ᵥ y) - star v ⬝ᵥ (K *ᵥ v) =
        star (y - v) ⬝ᵥ (K *ᵥ y) + star v ⬝ᵥ (K *ᵥ (y - v)) := by
      simp only [star_sub, sub_dotProduct, Matrix.mulVec_sub, dotProduct_sub]
      ring
    have h1 : ‖star (y - v) ⬝ᵥ (K *ᵥ y)‖ ≤ ‖K‖ / 4 := by
      calc _ ≤ l2Norm (y - v) * l2Norm (K *ᵥ y) := cgQuad_cs _ _
        _ ≤ (1 / 4) * (‖K‖ * l2Norm y) :=
            mul_le_mul hd (l2Norm_mulVec_le K y) (by unfold l2Norm; positivity) (by norm_num)
        _ = ‖K‖ / 4 := by rw [hy1]; ring
    have h2 : ‖star v ⬝ᵥ (K *ᵥ (y - v))‖ ≤ ‖K‖ / 4 := by
      calc _ ≤ l2Norm v * l2Norm (K *ᵥ (y - v)) := cgQuad_cs _ _
        _ ≤ 1 * (‖K‖ * (1 / 4)) := by
            refine mul_le_mul hv1.le ((l2Norm_mulVec_le K (y - v)).trans ?_)
              (by unfold l2Norm; positivity) (by norm_num)
            exact mul_le_mul_of_nonneg_left hd hκ
        _ = ‖K‖ / 4 := by ring
    have h3 : |(star y ⬝ᵥ (K *ᵥ y)).re - (star v ⬝ᵥ (K *ᵥ v)).re| ≤ ‖K‖ / 2 := by
      rw [← Complex.sub_re, e]
      calc _ ≤ ‖star (y - v) ⬝ᵥ (K *ᵥ y) + star v ⬝ᵥ (K *ᵥ (y - v))‖ := Complex.abs_re_le_norm _
        _ ≤ _ := (norm_add_le _ _).trans (by linarith)
    calc |(star y ⬝ᵥ (K *ᵥ y)).re| ≤ |(star v ⬝ᵥ (K *ᵥ v)).re| +
          |(star y ⬝ᵥ (K *ᵥ y)).re - (star v ⬝ᵥ (K *ᵥ v)).re| := by
          have := abs_sub_abs_le_abs_sub (star y ⬝ᵥ (K *ᵥ y)).re (star v ⬝ᵥ (K *ᵥ v)).re
          linarith
      _ ≤ a + ‖K‖ / 2 := add_le_add (hN v hv) h3
  have := cgQuad_herm_norm_le hK (by positivity) key
  linarith

/-! ### The centered form of a Hermitian matrix on the net -/

private lemma cgQuad_star_dotProduct {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    star z ⬝ᵥ z = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
  push_cast
  rfl

private lemma cgQuad_K_herm {n k : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (G : Matrix (Fin n) (Fin k) ℂ) :
    ((Gᴴ * H * G - H.trace • (1 : Matrix (Fin k) (Fin k) ℂ))).IsHermitian := by
  have htr : star H.trace = H.trace := by rw [← Matrix.trace_conjTranspose, hH.eq]
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, htr,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH.eq, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

private lemma cgQuad_K_form {n k : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (G : Matrix (Fin n) (Fin k) ℂ)
    {v : Fin k → ℂ} (hv : ∑ i, ‖v i‖ ^ 2 = 1) :
    star v ⬝ᵥ ((Gᴴ * H * G - H.trace • (1 : Matrix (Fin k) (Fin k) ℂ)) *ᵥ v) =
      star (G *ᵥ v) ⬝ᵥ (H *ᵥ (G *ᵥ v)) - H.trace := by
  rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, cgQuad_star_dotProduct, hv,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  simp

/-- For a Hermitian `H` and a `1/4`-net `N` of the unit sphere of `ℂ^k`:
`‖G* H G - (Tr H) I‖ > 2 (3 √T σ + 4 T L)` has probability at most `|N| · 2 e^{-T}`. -/
private lemma cgQuad_herm_main {n k : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    {σ L T : ℝ} (hσ : Real.sqrt (∑ i, ∑ j, ‖H i j‖ ^ 2) ≤ σ) (hL : ‖H‖ ≤ L) (hT : 0 ≤ T)
    {N : Finset (Fin k → ℂ)} (hNu : ∀ v ∈ N, ∑ i, ‖v i‖ ^ 2 = 1)
    (hNc : ∀ y : Fin k → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 →
      ∃ v ∈ N, ∑ i, ‖y i - v i‖ ^ 2 ≤ (1 / 4) ^ 2) :
    stdCGauss (Fin n × Fin k)
        {x | 2 * (3 * Real.sqrt T * σ + 4 * T * L) <
          ‖(cgMat x)ᴴ * H * cgMat x - H.trace • (1 : Matrix (Fin k) (Fin k) ℂ)‖} ≤
      (N.card : ℝ≥0∞) * (2 * ENNReal.ofReal (Real.exp (-T))) := by
  set a : ℝ := 3 * Real.sqrt T * σ + 4 * T * L with ha
  have hσ0 : 0 ≤ σ := (Real.sqrt_nonneg _).trans hσ
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hL
  have ha0 : 0 ≤ a := by positivity
  have hmeas : ∀ v ∈ N, MeasurableSet
      {w : Fin n → ℂ | a < |(star w ⬝ᵥ (H *ᵥ w)).re - H.trace.re|} := by
    intro v hv
    refine measurableSet_lt measurable_const ?_
    have : Continuous fun w : Fin n → ℂ => |(star w ⬝ᵥ (H *ᵥ w)).re - H.trace.re| := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    exact this.measurable
  have hsub : {x : Fin n × Fin k → ℂ | 2 * a <
      ‖(cgMat x)ᴴ * H * cgMat x - H.trace • (1 : Matrix (Fin k) (Fin k) ℂ)‖} ⊆
      ⋃ v ∈ N, (fun x : Fin n × Fin k → ℂ => cgMat x *ᵥ v) ⁻¹'
        {w : Fin n → ℂ | a < |(star w ⬝ᵥ (H *ᵥ w)).re - H.trace.re|} := by
    intro x hx
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_ofPred_eq, not_exists, not_lt] at hnot
    have hle := cgQuad_net_herm (cgQuad_K_herm hH (cgMat x)) ha0 hNu hNc (fun v hv => by
      rw [cgQuad_K_form H (cgMat x) (hNu v hv), Complex.sub_re]
      exact hnot v hv)
    exact absurd hx (not_lt.2 hle)
  calc _ ≤ stdCGauss (Fin n × Fin k) (⋃ v ∈ N, (fun x : Fin n × Fin k → ℂ => cgMat x *ᵥ v) ⁻¹'
        {w : Fin n → ℂ | a < |(star w ⬝ᵥ (H *ᵥ w)).re - H.trace.re|}) := measure_mono hsub
    _ ≤ ∑ v ∈ N, stdCGauss (Fin n × Fin k) ((fun x : Fin n × Fin k → ℂ => cgMat x *ᵥ v) ⁻¹'
        {w : Fin n → ℂ | a < |(star w ⬝ᵥ (H *ᵥ w)).re - H.trace.re|}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ N, 2 * ENNReal.ofReal (Real.exp (-T)) := by
        refine Finset.sum_le_sum fun v hv => ?_
        rw [(cgQuad_measurePreserving_mulVec (hNu v hv)).measure_preimage
          (hmeas v hv).nullMeasurableSet]
        exact cgQuad_tail_abs hH hσ hL hT
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### The Hermitian parts of a square matrix -/

/-- The Hermitian real part `(M + M*)/2`. -/
private def cgQuad_re {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (M + (1 : ℂ) • Mᴴ)

/-- The Hermitian imaginary part `(M - M*)/(2i)`. -/
private def cgQuad_im {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (-Complex.I / 2 : ℂ) • (M + (-1 : ℂ) • Mᴴ)

private lemma cgQuad_re_herm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (cgQuad_re M).IsHermitian := by
  unfold Matrix.IsHermitian cgQuad_re
  ext i j
  simp [Matrix.conjTranspose_apply]
  ring

private lemma cgQuad_im_herm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (cgQuad_im M).IsHermitian := by
  unfold Matrix.IsHermitian cgQuad_im
  ext i j
  simp [Matrix.conjTranspose_apply]
  ring

private lemma cgQuad_split {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    M = cgQuad_re M + Complex.I • cgQuad_im M := by
  unfold cgQuad_re cgQuad_im
  ext i j
  simp [Matrix.conjTranspose_apply]
  linear_combination ((M i j - (starRingEnd ℂ) (M j i)) / 2) * Complex.I_sq

private lemma cgQuad_K_split {n k : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (G : Matrix (Fin n) (Fin k) ℂ) :
    Gᴴ * M * G - M.trace • (1 : Matrix (Fin k) (Fin k) ℂ) =
      (Gᴴ * cgQuad_re M * G - (cgQuad_re M).trace • (1 : Matrix (Fin k) (Fin k) ℂ)) +
        Complex.I • (Gᴴ * cgQuad_im M * G -
          (cgQuad_im M).trace • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
  conv_lhs => rw [cgQuad_split M]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, add_smul, smul_sub, smul_smul, smul_eq_mul]
  abel

private lemma cgQuad_part_norm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {c ε : ℂ}
    (hc : ‖c‖ = 1 / 2) (hε : ‖ε‖ = 1) : ‖c • (M + ε • Mᴴ)‖ ≤ ‖M‖ := by
  rw [norm_smul, hc]
  have h1 := norm_add_le M (ε • Mᴴ)
  rw [norm_smul, hε, one_mul, Matrix.l2_opNorm_conjTranspose] at h1
  linarith

private lemma cgQuad_part_hs {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {c ε : ℂ}
    (hc : ‖c‖ = 1 / 2) (hε : ‖ε‖ = 1) :
    ∑ i, ∑ j, ‖(c • (M + ε • Mᴴ)) i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  have h : ∀ i j, ‖(c • (M + ε • Mᴴ)) i j‖ ^ 2 ≤ (‖M i j‖ ^ 2 + ‖M j i‖ ^ 2) / 2 := by
    intro i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply, smul_eq_mul,
      norm_mul, hc]
    have h1 : ‖M i j + ε * star (M j i)‖ ≤ ‖M i j‖ + ‖M j i‖ := by
      calc _ ≤ ‖M i j‖ + ‖ε * star (M j i)‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul, hε, one_mul, norm_star]
    have h2 : 0 ≤ ‖M i j + ε * star (M j i)‖ := norm_nonneg _
    have h3 := pow_le_pow_left₀ h2 h1 2
    nlinarith [sq_nonneg (‖M i j‖ - ‖M j i‖)]
  calc _ ≤ ∑ i, ∑ j, (‖M i j‖ ^ 2 + ‖M j i‖ ^ 2) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = _ := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => ‖M j i‖ ^ 2)]
      ring

/-- The centered quadratic form (proof of (9.47) [us:eq:quadratic]):
`‖G* M G - (Tr M) I‖ ≤ C (√(k + s) ‖M‖_HS + (k + s) ‖M‖)` with failure `e^{-s}`. -/
theorem cgMat_quadForm_le : ∃ C : ℝ, 0 < C ∧
    ∀ (n k : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 ≤ s →
      stdCGauss (Fin n × Fin k)
          {x | C * (Real.sqrt (k + s) * Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) + (k + s) * ‖M‖) <
            ‖(cgMat x)ᴴ * M * cgMat x - M.trace • (1 : Matrix (Fin k) (Fin k) ℂ)‖} ≤
        ENNReal.ofReal (Real.exp (-s)) := by
  refine ⟨112, by norm_num, fun n k M s hs => ?_⟩
  set σ : ℝ := Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) with hσdef
  set L : ℝ := ‖M‖ with hLdef
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := norm_nonneg _
  have hks : (0 : ℝ) ≤ k + s := by positivity
  have hRHS0 : 0 ≤ 112 * (Real.sqrt (k + s) * σ + (k + s) * L) := by positivity
  by_cases hk : k = 0
  · subst hk
    have hE : {x : Fin n × Fin 0 → ℂ | 112 * (Real.sqrt (((0 : ℕ) : ℝ) + s) * σ +
        (((0 : ℕ) : ℝ) + s) * L) <
        ‖(cgMat x)ᴴ * M * cgMat x - M.trace • (1 : Matrix (Fin 0) (Fin 0) ℂ)‖} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [Subsingleton.elim ((cgMat x)ᴴ * M * cgMat x - M.trace • (1 : Matrix (Fin 0) (Fin 0) ℂ))
        0, norm_zero]
      exact hRHS0
    rw [hE, measure_empty]
    exact zero_le
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
    set T : ℝ := s + 5 * k + 2 with hT
    have hT0 : 0 ≤ T := by positivity
    obtain ⟨N, hNc, hNu, hNcover⟩ := exists_sphere_net (Fin k) (δ := 1 / 4) (by norm_num)
    set a : ℝ := 3 * Real.sqrt T * σ + 4 * T * L with ha
    have hc1 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    have hc2 : ‖(-Complex.I / 2 : ℂ)‖ = 1 / 2 := by simp
    have he1 : ‖(1 : ℂ)‖ = 1 := by simp
    have he2 : ‖(-1 : ℂ)‖ = 1 := by simp
    have h1 := cgQuad_herm_main (cgQuad_re_herm M) (σ := σ) (L := L) (T := T)
      (Real.sqrt_le_sqrt (cgQuad_part_hs M hc1 he1))
      (cgQuad_part_norm M hc1 he1) hT0 hNu hNcover
    have h2 := cgQuad_herm_main (cgQuad_im_herm M) (σ := σ) (L := L) (T := T)
      (Real.sqrt_le_sqrt (cgQuad_part_hs M hc2 he2))
      (cgQuad_part_norm M hc2 he2) hT0 hNu hNcover
    have hsub : {x : Fin n × Fin k → ℂ | 112 * (Real.sqrt (k + s) * σ + (k + s) * L) <
        ‖(cgMat x)ᴴ * M * cgMat x - M.trace • (1 : Matrix (Fin k) (Fin k) ℂ)‖} ⊆
        {x | 2 * a < ‖(cgMat x)ᴴ * cgQuad_re M * cgMat x -
          (cgQuad_re M).trace • (1 : Matrix (Fin k) (Fin k) ℂ)‖} ∪
        {x | 2 * a < ‖(cgMat x)ᴴ * cgQuad_im M * cgMat x -
          (cgQuad_im M).trace • (1 : Matrix (Fin k) (Fin k) ℂ)‖} := by
      intro x hx
      by_contra hnot
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot hx
      obtain ⟨hn1, hn2⟩ := hnot
      have hK : ‖(cgMat x)ᴴ * M * cgMat x - M.trace • (1 : Matrix (Fin k) (Fin k) ℂ)‖ ≤ 4 * a := by
        rw [cgQuad_K_split M (cgMat x)]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Complex.norm_I, one_mul]
        linarith
      have hsq : Real.sqrt T ≤ 3 * Real.sqrt (k + s) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        rw [mul_pow, Real.sq_sqrt hks]
        norm_num
        rw [hT]
        linarith
      have hTk : T ≤ 7 * (k + s) := by rw [hT]; linarith
      have : 4 * a ≤ 112 * (Real.sqrt (k + s) * σ + (k + s) * L) := by
        rw [ha]
        nlinarith [mul_le_mul_of_nonneg_right hsq hσ0, mul_le_mul_of_nonneg_right hTk hL0,
          mul_nonneg (Real.sqrt_nonneg ((k : ℝ) + s)) hσ0, mul_nonneg hks hL0]
      linarith
    have hreal : 4 * (N.card : ℝ) * Real.exp (-T) ≤ Real.exp (-s) := by
      have h25 : (81 : ℝ) ≤ Real.exp 5 := by
        have h1 : (2.7 : ℝ) < Real.exp 1 := lt_of_lt_of_le (by norm_num) Real.exp_one_gt_d9.le
        have h2 : Real.exp 5 = Real.exp 1 ^ 5 := by
          rw [← Real.exp_nat_mul]
          norm_num
        rw [h2]
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) h1.le 5
        norm_num at this
        linarith
      have h4 : (4 : ℝ) ≤ Real.exp 2 := by
        have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
          rw [← Real.exp_nat_mul]
          norm_num
        rw [h2]
        nlinarith
      have hN : (N.card : ℝ) ≤ Real.exp (5 * k) := by
        refine hNc.trans ?_
        have : (1 + 2 / (1 / 4 : ℝ)) ^ (2 * Fintype.card (Fin k)) = 81 ^ k := by
          rw [Fintype.card_fin, pow_mul]
          norm_num
        rw [this, mul_comm, Real.exp_nat_mul]
        exact pow_le_pow_left₀ (by norm_num) h25 k
      have hexp : Real.exp (5 * k) * Real.exp (-T) = Real.exp (-2) * Real.exp (-s) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        rw [hT]
        ring
      have h2' : 4 * Real.exp (-2) ≤ 1 := by
        have h3 : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (-2)]
      calc 4 * (N.card : ℝ) * Real.exp (-T) ≤ 4 * Real.exp (5 * k) * Real.exp (-T) := by
            gcongr
        _ = 4 * Real.exp (-2) * Real.exp (-s) := by rw [mul_assoc, hexp]; ring
        _ ≤ 1 * Real.exp (-s) := mul_le_mul_of_nonneg_right h2' (Real.exp_pos _).le
        _ = Real.exp (-s) := one_mul _
    calc _ ≤ stdCGauss (Fin n × Fin k)
          ({x | 2 * a < ‖(cgMat x)ᴴ * cgQuad_re M * cgMat x -
            (cgQuad_re M).trace • (1 : Matrix (Fin k) (Fin k) ℂ)‖} ∪
          {x | 2 * a < ‖(cgMat x)ᴴ * cgQuad_im M * cgMat x -
            (cgQuad_im M).trace • (1 : Matrix (Fin k) (Fin k) ℂ)‖}) := measure_mono hsub
      _ ≤ (N.card : ℝ≥0∞) * (2 * ENNReal.ofReal (Real.exp (-T))) +
          (N.card : ℝ≥0∞) * (2 * ENNReal.ofReal (Real.exp (-T))) :=
          (measure_union_le _ _).trans (add_le_add h1 h2)
      _ = ENNReal.ofReal (4 * (N.card : ℝ) * Real.exp (-T)) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
          ring
      _ ≤ ENNReal.ofReal (Real.exp (-s)) := ENNReal.ofReal_le_ofReal hreal

end LSBA
