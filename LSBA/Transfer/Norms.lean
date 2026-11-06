import LSBA.Transfer.Basic

/-!
# Norms of the free transfer matrices

The product bound `‖S_E‖ ‖S_E⁻¹‖ ≤ 2 (2/κ)^{1/2}` on `|E| ≤ 2 − κ` (Definition 7.1
[def:transfer-matrices] states the sum bound `‖S_E‖ + ‖S_E⁻¹‖ ≤ C_κ`), and the norm of the
shear part.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- A `2 × 2` matrix tensored with the identity has operator norm at most its Frobenius norm. -/
private theorem norms_kron_one_le (W : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp only [Matrix.ofLp_toEuclideanCLM]
  have key : ∀ (i : Fin 2) (β : Fin W),
      ((A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *ᵥ x.ofLp) (i, β) = ∑ j, A i j * x.ofLp (j, β) := by
    intro i β
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type_right (f := fun k => ‖x.ofLp k‖ ^ 2)]
  simp only [key]
  have h : ∀ (i : Fin 2) (β : Fin W), ‖∑ j, A i j * x.ofLp (j, β)‖ ^ 2 ≤
      (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp (j, β)‖ ^ 2 := by
    intro i β
    have h1 : ‖∑ j, A i j * x.ofLp (j, β)‖ ≤ ∑ j, ‖A i j‖ * ‖x.ofLp (j, β)‖ :=
      (norm_sum_le _ _).trans (by simp)
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖)
      (fun j => ‖x.ofLp (j, β)‖)
    calc _ ≤ (∑ j, ‖A i j‖ * ‖x.ofLp (j, β)‖) ^ 2 := by gcongr
      _ ≤ _ := h2
  calc ∑ i, ∑ β, ‖∑ j, A i j * x.ofLp (j, β)‖ ^ 2
      ≤ ∑ i : Fin 2, ∑ β : Fin W, (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp (j, β)‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun β _ => h i β
    _ = _ := by rw [Finset.sum_mul_sum]

/-! ### The angle `ϑ = arccos(E/2)` -/

private theorem norms_cos_freeAngle {E : ℝ} (hE : |E| < 2) : Real.cos (freeAngle E) = E / 2 := by
  have h := abs_lt.mp hE
  exact Real.cos_arccos (by linarith) (by linarith)

private theorem norms_sin_freeAngle_pos {E : ℝ} (hE : |E| < 2) : 0 < Real.sin (freeAngle E) := by
  have h := abs_lt.mp hE
  exact Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr (by linarith))
    (Real.arccos_lt_pi.mpr (by linarith))

/-- `sin² ϑ ≥ κ / 2` for `|E| ≤ 2 - κ`. -/
private theorem norms_sin_sq_ge {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    κ / 2 ≤ Real.sin (freeAngle E) ^ 2 := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| < 2 := by linarith
  have h1 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    have := abs_le.mp hE
    exact sq_le_sq' (by linarith) this.2
  have h2 := Real.sin_sq_add_cos_sq (freeAngle E)
  rw [norms_cos_freeAngle hE2] at h2
  nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hκ2)]

/-- `1 / sin ϑ ≤ (2/κ)^{1/2}` for `|E| ≤ 2 - κ`. -/
private theorem norms_inv_sin_le {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    1 / Real.sin (freeAngle E) ≤ Real.sqrt (2 / κ) := by
  have hE2 : |E| < 2 := by linarith [abs_nonneg E]
  have hs := norms_sin_freeAngle_pos hE2
  have hsq := norms_sin_sq_ge hκ hE
  rw [Real.le_sqrt' (by positivity), div_pow, one_pow, div_le_div_iff₀ (by positivity) hκ]
  linarith

private theorem norms_norm_exp_neg (E : ℝ) : ‖Complex.exp (-(freeAngle E * Complex.I))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

private theorem norms_exp_neg_sub_exp (E : ℝ) :
    Complex.exp (-(freeAngle E * Complex.I)) - Complex.exp (freeAngle E * Complex.I) =
      -(2 * (Real.sin (freeAngle E) : ℂ)) * Complex.I := by
  rw [← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-! ### The inverse of `S_E` -/

private theorem norms_block_mul (a b : ℂ) :
    (!![1, 1; a, b] : Matrix (Fin 2) (Fin 2) ℂ) * !![b, -1; -a, 1] =
      (b - a) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `S_E⁻¹ = (i / (2 sin ϑ)^{1/2}) [[e^{-iϑ}, -1], [-e^{iϑ}, 1]] ⊗ I_W` for `|E| < 2`,
Definition 7.1 [def:transfer-matrices]. -/
private theorem norms_freeConj_inv {E : ℝ} (W : ℕ) (hE : |E| < 2) :
    (freeConj W E)⁻¹ = (Complex.I / ((Real.sqrt (2 * Real.sin (freeAngle E)) : ℝ) : ℂ)) •
      (!![Complex.exp (-(freeAngle E * Complex.I)), -1;
          -Complex.exp (freeAngle E * Complex.I), 1] ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ)) := by
  apply Matrix.inv_eq_right_inv
  have hs := norms_sin_freeAngle_pos hE
  have ht : 0 < Real.sqrt (2 * Real.sin (freeAngle E)) := Real.sqrt_pos.mpr (by positivity)
  have ht2 : ((Real.sqrt (2 * Real.sin (freeAngle E)) : ℝ) : ℂ) ^ 2 =
      2 * (Real.sin (freeAngle E) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.sin (freeAngle E))
  have htne : ((Real.sqrt (2 * Real.sin (freeAngle E)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ht.ne'
  have hsc : (((Real.sqrt (2 * Real.sin (freeAngle E)))⁻¹ : ℝ) : ℂ) *
      (Complex.I / ((Real.sqrt (2 * Real.sin (freeAngle E)) : ℝ) : ℂ)) *
        (Complex.exp (-(freeAngle E * Complex.I)) - Complex.exp (freeAngle E * Complex.I)) = 1 := by
    rw [norms_exp_neg_sub_exp, Complex.ofReal_inv]
    field_simp
    rw [ht2, Complex.I_sq]
    ring
  unfold freeConj
  rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_kronecker_mul, norms_block_mul, Matrix.mul_one,
    Matrix.smul_kronecker, Matrix.one_kronecker_one, smul_smul, smul_smul, hsc, one_smul]

/-! ### Norm bounds -/

/-- A `2 × 2` matrix with entries of modulus one, tensored with `I_W`, has norm at most `2`. -/
private theorem norms_kron_one_le_two (W : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ i j, ‖A i j‖ = 1) : ‖A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 2 := by
  refine (norms_kron_one_le W A).trans ?_
  have h4 : ∑ i, ∑ j, ‖A i j‖ ^ 2 = (2 : ℝ) ^ 2 := by
    simp only [h, Fin.sum_univ_two]
    norm_num
  rw [h4, Real.sqrt_sq (by norm_num)]

/-- `‖S_E‖ ≤ 2 (2 sin ϑ)^{-1/2}` for `|E| < 2`, Definition 7.1 [def:transfer-matrices]. -/
private theorem norms_freeConj_le (W : ℕ) {E : ℝ} (hE : |E| < 2) :
    ‖freeConj W E‖ ≤ 2 / Real.sqrt (2 * Real.sin (freeAngle E)) := by
  have hs := norms_sin_freeAngle_pos hE
  have ht : 0 < Real.sqrt (2 * Real.sin (freeAngle E)) := Real.sqrt_pos.mpr (by positivity)
  unfold freeConj
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht), div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left (norms_kron_one_le_two W _ ?_) (inv_pos.mpr ht).le
  intro i j
  fin_cases i <;> fin_cases j <;> simp [norms_norm_exp_neg]

/-- `‖S_E⁻¹‖ ≤ 2 (2 sin ϑ)^{-1/2}` for `|E| < 2`, Definition 7.1 [def:transfer-matrices]. -/
private theorem norms_freeConj_inv_le (W : ℕ) {E : ℝ} (hE : |E| < 2) :
    ‖(freeConj W E)⁻¹‖ ≤ 2 / Real.sqrt (2 * Real.sin (freeAngle E)) := by
  have hs := norms_sin_freeAngle_pos hE
  have ht : 0 < Real.sqrt (2 * Real.sin (freeAngle E)) := Real.sqrt_pos.mpr (by positivity)
  rw [norms_freeConj_inv W hE, norm_smul, norm_div, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht, div_eq_inv_mul 2, one_div]
  refine mul_le_mul_of_nonneg_left (norms_kron_one_le_two W _ ?_) (inv_pos.mpr ht).le
  intro i j
  fin_cases i <;> fin_cases j <;> simp [norms_norm_exp_neg]

private theorem norms_block_shear (a b : ℂ) :
    (!![b, -1; -a, 1] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, 0] * !![1, 1; a, b] =
      !![b, b; -a, -a] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `B_E = (i / (2 sin ϑ)) [[e^{-iϑ}, e^{-iϑ}], [-e^{iϑ}, -e^{iϑ}]] ⊗ I_W` for `|E| < 2`
(proof of Lemma 7.2 [uvs:lem:transfer-moments]). -/
private theorem norms_freeShear_eq (W : ℕ) {E : ℝ} (hE : |E| < 2) :
    freeShear W E = (Complex.I / (2 * (Real.sin (freeAngle E) : ℂ))) •
      (!![Complex.exp (-(freeAngle E * Complex.I)), Complex.exp (-(freeAngle E * Complex.I));
          -Complex.exp (freeAngle E * Complex.I), -Complex.exp (freeAngle E * Complex.I)] ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ)) := by
  have hs := norms_sin_freeAngle_pos hE
  have ht : 0 < Real.sqrt (2 * Real.sin (freeAngle E)) := Real.sqrt_pos.mpr (by positivity)
  have ht2 : ((Real.sqrt (2 * Real.sin (freeAngle E)) : ℝ) : ℂ) ^ 2 =
      2 * (Real.sin (freeAngle E) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.sin (freeAngle E))
  have htne : ((Real.sqrt (2 * Real.sin (freeAngle E)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ht.ne'
  have hsne : (Real.sin (freeAngle E) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold freeShear
  rw [norms_freeConj_inv W hE]
  conv_lhs => rw [freeConj]
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one, norms_block_shear, smul_smul,
    Complex.ofReal_inv]
  congr 1
  field_simp
  rw [ht2]

/-- `(2 / (2 σ)^{1/2})² = 2 / σ` for `σ > 0`. -/
private theorem norms_two_div_sqrt_mul_self {σ : ℝ} (hσ : 0 < σ) :
    (2 / Real.sqrt (2 * σ)) * (2 / Real.sqrt (2 * σ)) = 2 / σ := by
  rw [div_mul_div_comm, Real.mul_self_sqrt (by positivity)]
  field_simp

/-- `‖S_E‖ ‖S_E⁻¹‖ ≤ 2 (2/κ)^{1/2}` for `|E| ≤ 2 - κ`; Definition 7.1 [def:transfer-matrices]
states the sum bound `‖S_E‖ + ‖S_E⁻¹‖ ≤ C_κ`. -/
theorem norm_freeConj_mul_norm_inv_le (W : ℕ) {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    ‖freeConj W E‖ * ‖(freeConj W E)⁻¹‖ ≤ 2 * Real.sqrt (2 / κ) := by
  have hE2 : |E| < 2 := by linarith [abs_nonneg E]
  have hs := norms_sin_freeAngle_pos hE2
  have hK := norms_inv_sin_le hκ hE
  have ht : 0 < Real.sqrt (2 * Real.sin (freeAngle E)) := Real.sqrt_pos.mpr (by positivity)
  calc ‖freeConj W E‖ * ‖(freeConj W E)⁻¹‖
      ≤ (2 / Real.sqrt (2 * Real.sin (freeAngle E))) *
          (2 / Real.sqrt (2 * Real.sin (freeAngle E))) :=
        mul_le_mul (norms_freeConj_le W hE2) (norms_freeConj_inv_le W hE2) (norm_nonneg _)
          (by positivity)
    _ = 2 * (1 / Real.sin (freeAngle E)) := by
        rw [norms_two_div_sqrt_mul_self hs]; ring
    _ ≤ 2 * Real.sqrt (2 / κ) := by linarith

/-- `‖B_E‖ ≤ (2/κ)^{1/2}` for `|E| ≤ 2 - κ`. -/
theorem norm_freeShear_le (W : ℕ) {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    ‖freeShear W E‖ ≤ Real.sqrt (2 / κ) := by
  have hE2 : |E| < 2 := by linarith [abs_nonneg E]
  have hs := norms_sin_freeAngle_pos hE2
  have hK := norms_inv_sin_le hκ hE
  rw [norms_freeShear_eq W hE2, norm_smul, norm_div, Complex.norm_I, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hM := norms_kron_one_le_two W
    (!![Complex.exp (-(freeAngle E * Complex.I)), Complex.exp (-(freeAngle E * Complex.I));
        -Complex.exp (freeAngle E * Complex.I), -Complex.exp (freeAngle E * Complex.I)])
    (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [norms_norm_exp_neg])
  calc 1 / (‖(2 : ℂ)‖ * Real.sin (freeAngle E)) * _
      ≤ 1 / (‖(2 : ℂ)‖ * Real.sin (freeAngle E)) * 2 :=
        mul_le_mul_of_nonneg_left hM (by positivity)
    _ = 1 / Real.sin (freeAngle E) := by
        rw [show ‖(2 : ℂ)‖ = 2 by simp]; field_simp
    _ ≤ Real.sqrt (2 / κ) := hK

end LSBA
