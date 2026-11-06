import LSBA.Gauss.StdGauss

/-!
# A Gaussian exponential moment

For a standard Gaussian vector `x` on `ℝ^ι` and a real matrix `Λ` with `s‖Λ‖² ≤ 1/2`:
`E exp(⟨b, Λx⟩ + (s/2)‖Λx‖²) ≤ exp(s‖Λ‖²_HS + ‖Λ‖²‖b‖²)`, used in the one-step moment bound
(7.2) [uvs:eq:one-step-moment] of the proof of Lemma 7.2 [uvs:lem:transfer-moments].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### The one-dimensional integral -/

/-- Completing the square: `∫ exp (-a y² + c y) = √(π/a) exp (c²/(4a))` for `a > 0`. -/
private lemma expQuadratic_integral_aux {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-a * y ^ 2 + c * y)) ∧
      ∫ y : ℝ, Real.exp (-a * y ^ 2 + c * y) = Real.sqrt (π / a) * Real.exp (c ^ 2 / (4 * a)) := by
  have hform : ∀ y : ℝ, Real.exp (-a * y ^ 2 + c * y) =
      Real.exp (c ^ 2 / (4 * a)) * Real.exp (-a * (y - c / (2 * a)) ^ 2) := by
    intro y
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  simp_rw [hform]
  refine ⟨((integrable_exp_neg_mul_sq ha).comp_sub_right (c / (2 * a))).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub_right_eq_self (fun y => Real.exp (-a * y ^ 2)),
    integral_gaussian]
  ring

/-- The standard Gaussian density times `exp (c y + α y² / 2)`. -/
private lemma expQuadratic_pdf_mul (α c y : ℝ) :
    gaussianPDFReal 0 1 y * Real.exp (c * y + α / 2 * y ^ 2) =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-((1 - α) / 2) * y ^ 2 + c * y) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- For `α < 1`, `E exp (c y + α y² / 2) = (1 - α)^{-1/2} exp (c² / (2 (1 - α)))` under the
standard Gaussian on `ℝ`, and the integrand is integrable. -/
private lemma expQuadratic_gauss_one {α : ℝ} (hα : α < 1) (c : ℝ) :
    Integrable (fun y : ℝ => Real.exp (c * y + α / 2 * y ^ 2)) (gaussianReal 0 1) ∧
      ∫ y : ℝ, Real.exp (c * y + α / 2 * y ^ 2) ∂(gaussianReal 0 1) =
        (Real.sqrt (1 - α))⁻¹ * Real.exp (c ^ 2 / (2 * (1 - α))) := by
  have ha : 0 < (1 - α) / 2 := by linarith
  obtain ⟨hI, hE⟩ := expQuadratic_integral_aux ha c
  refine ⟨?_, ?_⟩
  · rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
        (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)]
    refine (hI.const_mul ((Real.sqrt (2 * π))⁻¹)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 y), smul_eq_mul]
    exact (expQuadratic_pdf_mul α c y).symm
  · rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp only [smul_eq_mul, expQuadratic_pdf_mul]
    rw [integral_const_mul, hE]
    have h1 : 0 < 1 - α := by linarith
    have h2 : Real.sqrt (π / ((1 - α) / 2)) = Real.sqrt (2 * π) * (Real.sqrt (1 - α))⁻¹ := by
      rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    have h3 : c ^ 2 / (4 * ((1 - α) / 2)) = c ^ 2 / (2 * (1 - α)) := by
      field_simp
      ring
    rw [h2, h3]
    have : Real.sqrt (2 * π) ≠ 0 := by positivity
    field_simp

/-- `(1 - α)^{-1/2} ≤ exp α` for `0 ≤ α ≤ 1/2`. -/
private lemma expQuadratic_inv_sqrt_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) :
    (Real.sqrt (1 - α))⁻¹ ≤ Real.exp α := by
  have hpos : 0 < Real.sqrt (1 - α) := Real.sqrt_pos.mpr (by linarith)
  rw [inv_le_comm₀ hpos (Real.exp_pos α)]
  have hsq : (Real.exp α)⁻¹ ^ 2 ≤ 1 - α := by
    have hexp : 1 + 2 * α ≤ Real.exp (2 * α) := by linarith [Real.add_one_le_exp (2 * α)]
    have h2 : (Real.exp α)⁻¹ ^ 2 = (Real.exp (2 * α))⁻¹ := by
      rw [← Real.exp_neg, ← Real.exp_neg, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    rw [h2, inv_le_comm₀ (Real.exp_pos _) (by linarith)]
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    nlinarith
  calc (Real.exp α)⁻¹ = Real.sqrt ((Real.exp α)⁻¹ ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (1 - α) := Real.sqrt_le_sqrt hsq

/-- For `0 ≤ α ≤ 1/2`, `E exp (c y + α y² / 2) ≤ exp (α + c²)` under the standard Gaussian on `ℝ`,
and the integrand is integrable. -/
private lemma expQuadratic_gauss_one_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) (c : ℝ) :
    Integrable (fun y : ℝ => Real.exp (c * y + α / 2 * y ^ 2)) (gaussianReal 0 1) ∧
      ∫ y : ℝ, Real.exp (c * y + α / 2 * y ^ 2) ∂(gaussianReal 0 1) ≤ Real.exp (α + c ^ 2) := by
  obtain ⟨hI, hE⟩ := expQuadratic_gauss_one (show α < 1 by linarith) c
  refine ⟨hI, ?_⟩
  rw [hE, Real.exp_add]
  refine mul_le_mul (expQuadratic_inv_sqrt_le h0 h1) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
    (Real.exp_pos _).le
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg c]

/-! ### Diagonalization -/

/-- Parseval for an orthonormal basis of `ℝ^ι`, in coordinates. -/
private lemma expQuadratic_parseval {ι : Type*} [Fintype ι]
    (B : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (u v : ι → ℝ) :
    ∑ k, (∑ i, u i * B k i) * (∑ i, v i * B k i) = ∑ i, u i * v i := by
  have h := B.sum_inner_mul_inner (WithLp.toLp 2 u) (WithLp.toLp 2 v)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h
  simpa only [mul_comm] using h

/-- The coordinate of `x` along the basis vector `B k`. -/
private lemma expQuadratic_coord {ι : Type*} [Fintype ι]
    (B : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (x : ι → ℝ) (k : ι) :
    (B.repr (WithLp.toLp 2 x)) k = ∑ i, x i * B k i := by
  rw [OrthonormalBasis.repr_apply_apply]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

/-- `‖Λ w‖² ≤ ‖Λ‖² ‖w‖²` in coordinates, for the operator norm of `Matrix.Norms.L2Operator`. -/
private lemma expQuadratic_sq_mulVec_le {ι m : Type*} [Fintype ι] [Fintype m]
    (Λ : Matrix m ι ℝ) (w : ι → ℝ) :
    ∑ i, (Λ *ᵥ w) i ^ 2 ≤ ‖Λ‖ ^ 2 * ∑ j, w j ^ 2 := by
  have h := Λ.l2_opNorm_mulVec (WithLp.toLp 2 w)
  have h0 : 0 ≤ ‖(EuclideanSpace.equiv m ℝ).symm (Λ *ᵥ w)‖ := norm_nonneg _
  have h2 := pow_le_pow_left₀ h0 h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa using h2

/-- The sum of squares of the entries of `Λ w` as a quadratic form of `Λᵀ Λ`. -/
private lemma expQuadratic_sq_eq_dot {ι m : Type*} [Fintype ι] [Fintype m]
    (Λ : Matrix m ι ℝ) (w : ι → ℝ) :
    ∑ i, (Λ *ᵥ w) i ^ 2 = ((Λᵀ * Λ) *ᵥ w) ⬝ᵥ w := by
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  simp [dotProduct, sq]

/-- An orthonormal eigenbasis `B` of `Λᵀ Λ` with eigenvalues `μ`: the squared norm of `Λ x` is
`∑ μ_k ⟨B_k, x⟩²`, each `μ_k ∈ [0, ‖Λ‖²]`, and `∑ μ_k` is the squared Hilbert–Schmidt norm. -/
private lemma expQuadratic_diag {ι m : Type*} [Fintype ι] [Fintype m] [DecidableEq ι]
    (Λ : Matrix m ι ℝ) :
    ∃ (B : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (μ : ι → ℝ),
      (∀ x : ι → ℝ, ∑ i, (Λ *ᵥ x) i ^ 2 = ∑ k, μ k * (∑ i, x i * B k i) ^ 2) ∧
      (∀ k, 0 ≤ μ k ∧ μ k ≤ ‖Λ‖ ^ 2) ∧ ∑ k, μ k = ∑ i, ∑ j, Λ i j ^ 2 := by
  have hA : (Λᵀ * Λ).IsHermitian := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self Λ
  have hsym : ∀ u v : ι → ℝ, ((Λᵀ * Λ) *ᵥ u) ⬝ᵥ v = u ⬝ᵥ ((Λᵀ * Λ) *ᵥ v) := by
    intro u v
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hB : ∀ k, (Λᵀ * Λ) *ᵥ ⇑(hA.eigenvectorBasis k) =
      hA.eigenvalues k • ⇑(hA.eigenvectorBasis k) := fun k => hA.mulVec_eigenvectorBasis k
  have hnorm : ∀ k, ∑ i, hA.eigenvectorBasis k i ^ 2 = 1 := by
    intro k
    have h := hA.eigenvectorBasis.norm_eq_one k
    have h2 := EuclideanSpace.norm_sq_eq (hA.eigenvectorBasis k)
    rw [h] at h2
    simpa using h2.symm
  have hmu : ∀ k, ∑ i, (Λ *ᵥ ⇑(hA.eigenvectorBasis k)) i ^ 2 = hA.eigenvalues k := by
    intro k
    rw [expQuadratic_sq_eq_dot, hB k]
    have h1 : ⇑(hA.eigenvectorBasis k) ⬝ᵥ ⇑(hA.eigenvectorBasis k) = 1 := by
      simpa [dotProduct, sq] using hnorm k
    rw [smul_dotProduct, h1, smul_eq_mul, mul_one]
  have hquad : ∀ x : ι → ℝ, ∑ i, (Λ *ᵥ x) i ^ 2 =
      ∑ k, hA.eigenvalues k * (∑ i, x i * hA.eigenvectorBasis k i) ^ 2 := by
    intro x
    rw [expQuadratic_sq_eq_dot]
    have hP := expQuadratic_parseval hA.eigenvectorBasis ((Λᵀ * Λ) *ᵥ x) x
    have hk : ∀ k, ∑ i, ((Λᵀ * Λ) *ᵥ x) i * hA.eigenvectorBasis k i =
        hA.eigenvalues k * ∑ i, x i * hA.eigenvectorBasis k i := by
      intro k
      have := hsym x ⇑(hA.eigenvectorBasis k)
      rw [hB k, dotProduct_smul, smul_eq_mul] at this
      exact this
    calc ((Λᵀ * Λ) *ᵥ x) ⬝ᵥ x = ∑ i, ((Λᵀ * Λ) *ᵥ x) i * x i := rfl
      _ = ∑ k, (∑ i, ((Λᵀ * Λ) *ᵥ x) i * hA.eigenvectorBasis k i) *
            (∑ i, x i * hA.eigenvectorBasis k i) := hP.symm
      _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hk k]
        ring
  refine ⟨hA.eigenvectorBasis, hA.eigenvalues, hquad, ?_, ?_⟩
  · intro k
    refine ⟨?_, ?_⟩
    · rw [← hmu k]; positivity
    · rw [← hmu k]
      calc _ ≤ ‖Λ‖ ^ 2 * ∑ j, hA.eigenvectorBasis k j ^ 2 := expQuadratic_sq_mulVec_le Λ _
        _ = ‖Λ‖ ^ 2 := by rw [hnorm k, mul_one]
  · calc ∑ k, hA.eigenvalues k = ∑ k, ∑ i, (Λ *ᵥ ⇑(hA.eigenvectorBasis k)) i ^ 2 :=
          Finset.sum_congr rfl fun k _ => (hmu k).symm
      _ = ∑ i, ∑ k, (∑ j, Λ i j * hA.eigenvectorBasis k j) *
            (∑ j, Λ i j * hA.eigenvectorBasis k j) := by
        rw [Finset.sum_comm]
        simp only [sq]
        rfl
      _ = ∑ i, ∑ j, Λ i j ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [expQuadratic_parseval hA.eigenvectorBasis (fun j => Λ i j) (fun j => Λ i j)]
        simp [sq]

/-- Gaussian linear-quadratic exponential moment: for a standard Gaussian `x` on `ℝ^ι`, a real
matrix `Λ` with `s‖Λ‖² ≤ 1/2`, `E exp(⟨b, Λx⟩ + (s/2)‖Λx‖²) ≤ exp(s‖Λ‖²_HS + ‖Λ‖²‖b‖²)`. -/
theorem integral_exp_linear_add_quadratic_le {ι m : Type*} [Fintype ι] [Fintype m]
    [DecidableEq ι] (Λ : Matrix m ι ℝ) (b : m → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (hΛ : s * ‖Λ‖ ^ 2 ≤ 1 / 2) :
    Integrable (fun x : ι → ℝ => Real.exp (b ⬝ᵥ (Λ *ᵥ x) + s / 2 * ∑ i, (Λ *ᵥ x) i ^ 2))
        (stdGauss ι) ∧
      ∫ x, Real.exp (b ⬝ᵥ (Λ *ᵥ x) + s / 2 * ∑ i, (Λ *ᵥ x) i ^ 2) ∂(stdGauss ι) ≤
        Real.exp (s * ∑ i, ∑ j, Λ i j ^ 2 + ‖Λ‖ ^ 2 * ∑ i, b i ^ 2) := by
  obtain ⟨B, μ, hq, hμ, hμsum⟩ := expQuadratic_diag Λ
  set c : ι → ℝ := fun k => ∑ i, (Λᵀ *ᵥ b) i * B k i with hc_def
  have hlin : ∀ x : ι → ℝ, b ⬝ᵥ (Λ *ᵥ x) = ∑ k, c k * (∑ i, x i * B k i) := by
    intro x
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    exact (expQuadratic_parseval B (Λᵀ *ᵥ b) x).symm
  have hcsq : ∑ k, c k ^ 2 ≤ ‖Λ‖ ^ 2 * ∑ i, b i ^ 2 := by
    have h1 := expQuadratic_parseval B (Λᵀ *ᵥ b) (Λᵀ *ᵥ b)
    have h2 := expQuadratic_sq_mulVec_le Λᵀ b
    have h3 : ‖Λᵀ‖ = ‖Λ‖ := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact Matrix.l2_opNorm_conjTranspose Λ
    rw [h3] at h2
    simp only [sq] at h2 ⊢
    exact h1.le.trans h2
  have hα0 : ∀ k, 0 ≤ s * μ k := fun k => mul_nonneg hs (hμ k).1
  have hα1 : ∀ k, s * μ k ≤ 1 / 2 := fun k =>
    (mul_le_mul_of_nonneg_left (hμ k).2 hs).trans hΛ
  let F : (ι → ℝ) → ℝ := fun y => ∏ k, Real.exp (c k * y k + s * μ k / 2 * y k ^ 2)
  have hF : Integrable F (stdGauss ι) :=
    Integrable.fintype_prod (f := fun k y => Real.exp (c k * y + s * μ k / 2 * y ^ 2))
      (fun k => (expQuadratic_gauss_one_le (hα0 k) (hα1 k) (c k)).1)
  have hFint : ∫ y, F y ∂(stdGauss ι) ≤ Real.exp (s * ∑ k, μ k + ∑ k, c k ^ 2) := by
    have hprod : ∫ y, F y ∂(stdGauss ι) =
        ∏ k, ∫ y : ℝ, Real.exp (c k * y + s * μ k / 2 * y ^ 2) ∂(gaussianReal 0 1) :=
      integral_fintype_prod_eq_prod (μ := fun _ : ι => gaussianReal 0 1)
        (fun k y => Real.exp (c k * y + s * μ k / 2 * y ^ 2))
    rw [hprod]
    calc _ ≤ ∏ k, Real.exp (s * μ k + c k ^ 2) :=
          Finset.prod_le_prod₀ (fun k _ => integral_nonneg (fun y => (Real.exp_pos _).le))
            (fun k _ => (expQuadratic_gauss_one_le (hα0 k) (hα1 k) (c k)).2)
      _ = _ := by
        rw [← Real.exp_sum, Finset.sum_add_distrib, Finset.mul_sum]
  have hQ := measurePreserving_stdGauss_linearIsometry B.repr
  have hint : ∀ x : ι → ℝ,
      Real.exp (b ⬝ᵥ (Λ *ᵥ x) + s / 2 * ∑ i, (Λ *ᵥ x) i ^ 2) =
        F ((B.repr (WithLp.toLp 2 x)).ofLp) := by
    intro x
    simp only [F, ← Real.exp_sum]
    congr 1
    rw [hlin x, hq x, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (B.repr (WithLp.toLp 2 x)).ofLp k = ∑ i, x i * B k i from
      expQuadratic_coord B x k]
    ring
  have hFm : Continuous F := by
    simp only [F]
    fun_prop
  simp_rw [hint]
  refine ⟨(hQ.integrable_comp hFm.aestronglyMeasurable).mpr hF, ?_⟩
  calc _ = ∫ y, F y ∂(stdGauss ι) := by
        rw [← integral_map (μ := stdGauss ι) hQ.measurable.aemeasurable hFm.aestronglyMeasurable
          (f := F), hQ.map_eq]
    _ ≤ _ := hFint.trans (Real.exp_le_exp.mpr ?_)
  rw [hμsum]
  linarith

end LSBA
