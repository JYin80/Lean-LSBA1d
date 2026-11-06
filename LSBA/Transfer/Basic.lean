import LSBA.Model.Basic

/-!
# Transfer matrices

Definition 7.1 [def:transfer-matrices]: the transfer matrices `T_j(z)` of the block recurrence and
their inverses, the free transfer matrix `T(z)`, the free conjugation `S_E` and rotation `R_E` for
`|E| < 2`, the shear part, and products of transfer matrices.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Free transfer matrix `T(z) = [[z, -1], [1, 0]] ⊗ I_W`, Definition 7.1
[def:transfer-matrices]. -/
def transferFree (W : ℕ) (z : ℂ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  !![z, -1; 1, 0] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)

/-- Transfer matrix `T_j(z) = [[z I - V/g, -I], [I, 0]]` of Definition 7.1
[def:transfer-matrices] for the onsite block `V`. -/
def transferMat {W : ℕ} (g : ℝ) (z : ℂ) (V : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  transferFree W z - ((g : ℂ)⁻¹) • (!![1, 0; 0, 0] ⊗ₖ V)

/-- The matrix `[[0, I], [-I, z I - V/g]]`, the inverse of `transferMat g z V`. -/
def transferInv {W : ℕ} (g : ℝ) (z : ℂ) (V : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  !![0, 1; -1, z] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) - ((g : ℂ)⁻¹) • (!![0, 0; 0, 1] ⊗ₖ V)

/-- The angle `ϑ = arccos(E/2)` of Definition 7.1 [def:transfer-matrices]. -/
def freeAngle (E : ℝ) : ℝ := Real.arccos (E / 2)

/-- `S_E = (2 sin ϑ)^{-1/2} [[1, 1], [e^{iϑ}, e^{-iϑ}]] ⊗ I_W`, Definition 7.1
[def:transfer-matrices]; it is `0` when `|E| ≥ 2`. -/
def freeConj (W : ℕ) (E : ℝ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (((Real.sqrt (2 * Real.sin (freeAngle E)))⁻¹ : ℝ) : ℂ) •
    (!![1, 1; Complex.exp (freeAngle E * Complex.I), Complex.exp (-(freeAngle E * Complex.I))] ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ))

/-- `R_E = diag(e^{-iϑ}, e^{iϑ}) ⊗ I_W`, Definition 7.1 [def:transfer-matrices], for every
real `E`. -/
def freeRot (W : ℕ) (E : ℝ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  Matrix.diagonal ![Complex.exp (-(freeAngle E * Complex.I)), Complex.exp (freeAngle E * Complex.I)] ⊗ₖ
    (1 : Matrix (Fin W) (Fin W) ℂ)

/-- `B_E = S_E⁻¹ (P₁ ⊗ I) S_E`, the coefficient of `iη` in `S_E⁻¹ T_j(E + iη) S_E`
(proof of Lemma 7.2 [uvs:lem:transfer-moments]). -/
def freeShear (W : ℕ) (E : ℝ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (freeConj W E)⁻¹ * (!![1, 0; 0, 0] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * freeConj W E

/-- Prefix products `P_j = T(V_{j-1}) ⋯ T(V_0)` along a sequence of onsite blocks, `P_0 = I`. -/
def transferProd {W : ℕ} (g : ℝ) (z : ℂ) (V : ℕ → Matrix (Fin W) (Fin W) ℂ) :
    ℕ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ
  | 0 => 1
  | j + 1 => transferMat g z (V j) * transferProd g z V j


/-- Block product `[[z, -1], [1, 0]] * [[0, 1], [-1, z]] = 1`. -/
private theorem transferBlock_mul (z : ℂ) :
    (!![z, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; -1, z] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem transferMat_mul_transferInv {W : ℕ} (g : ℝ) (z : ℂ) (V : Matrix (Fin W) (Fin W) ℂ) :
    transferMat g z V * transferInv g z V = 1 := by
  unfold transferMat transferInv transferFree
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_kronecker_mul, transferBlock_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.one_kronecker_one]
  have h0 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 0; 0, 1] = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h1 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; -1, z] +
      !![z, -1; 1, 0] * !![0, 0; 0, 1] = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h2 : ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; -1, z]) ⊗ₖ V +
      ((!![z, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 0; 0, 1]) ⊗ₖ V = 0 := by
    rw [← Matrix.add_kronecker, h1]
    ext i j
    simp
  rw [h0, Matrix.zero_kronecker, smul_zero, sub_zero, sub_sub, ← smul_add, h2, smul_zero, sub_zero]

/-- The inverse of `T_j(z)`, proof of Lemma 7.2 [uvs:lem:transfer-moments]. -/
theorem inv_transferMat {W : ℕ} (g : ℝ) (z : ℂ) (V : Matrix (Fin W) (Fin W) ℂ) :
    (transferMat g z V)⁻¹ = transferInv g z V :=
  Matrix.inv_eq_right_inv (transferMat_mul_transferInv g z V)

private theorem cos_freeAngle {E : ℝ} (hE : |E| < 2) : Real.cos (freeAngle E) = E / 2 := by
  have h := abs_lt.mp hE
  exact Real.cos_arccos (by linarith) (by linarith)

private theorem sin_freeAngle_pos {E : ℝ} (hE : |E| < 2) : 0 < Real.sin (freeAngle E) := by
  have h := abs_lt.mp hE
  exact Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr (by linarith))
    (Real.arccos_lt_pi.mpr (by linarith))

private theorem exp_freeAngle_mul_I (E : ℝ) :
    Complex.exp (freeAngle E * Complex.I) =
      (Real.cos (freeAngle E) : ℂ) + (Real.sin (freeAngle E) : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private theorem exp_neg_freeAngle_mul_I (E : ℝ) :
    Complex.exp (-(freeAngle E * Complex.I)) =
      (Real.cos (freeAngle E) : ℂ) - (Real.sin (freeAngle E) : ℂ) * Complex.I := by
  rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  ring

private theorem exp_freeAngle_add {E : ℝ} (hE : |E| < 2) :
    Complex.exp (freeAngle E * Complex.I) + Complex.exp (-(freeAngle E * Complex.I)) = (E : ℂ) := by
  rw [exp_freeAngle_mul_I, exp_neg_freeAngle_mul_I, cos_freeAngle hE]
  push_cast
  ring

private theorem exp_freeAngle_mul_exp_neg (E : ℝ) :
    Complex.exp (freeAngle E * Complex.I) * Complex.exp (-(freeAngle E * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

private theorem star_exp_freeAngle (E : ℝ) :
    star (Complex.exp (freeAngle E * Complex.I)) = Complex.exp (-(freeAngle E * Complex.I)) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  simp

private theorem star_exp_neg_freeAngle (E : ℝ) :
    star (Complex.exp (-(freeAngle E * Complex.I))) = Complex.exp (freeAngle E * Complex.I) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  simp


theorem isUnit_freeConj (W : ℕ) {E : ℝ} (hE : |E| < 2) : IsUnit (freeConj W E) := by
  have hs := sin_freeAngle_pos hE
  have hc : ((Real.sqrt (2 * Real.sin (freeAngle E)))⁻¹ : ℝ) ≠ 0 :=
    inv_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne'
  have hd : Complex.exp (-(freeAngle E * Complex.I)) -
      Complex.exp (freeAngle E * Complex.I) ≠ 0 := by
    rw [exp_freeAngle_mul_I, exp_neg_freeAngle_mul_I]
    intro h
    have h' : (-(2 * Real.sin (freeAngle E)) : ℂ) * Complex.I = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact hs.ne' (by exact_mod_cast (by simpa using h'' : (Real.sin (freeAngle E) : ℂ) = 0))
    · exact Complex.I_ne_zero h''
  rw [Matrix.isUnit_iff_isUnit_det]
  unfold freeConj
  rw [Matrix.det_smul, Matrix.det_kronecker, Matrix.det_fin_two_of]
  simp only [Matrix.det_one, one_pow, mul_one, one_mul]
  refine (IsUnit.pow _ (isUnit_iff_ne_zero.mpr (by exact_mod_cast hc))).mul
    (IsUnit.pow _ (isUnit_iff_ne_zero.mpr ?_))
  simpa [sub_eq_add_neg] using hd

private theorem transferBlock_conj (a b : ℂ) (h1 : a * b = 1) :
    (!![a + b, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 1; a, b] =
      !![1, 1; a, b] * Matrix.diagonal ![b, a] := by
  have h2 : b * a = 1 := by rw [mul_comm, h1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, add_comm a b]

private theorem transferFree_mul_freeConj (W : ℕ) {E : ℝ} (hE : |E| < 2) :
    transferFree W E * freeConj W E = freeConj W E * freeRot W E := by
  have hab := exp_freeAngle_add hE
  have h1 := exp_freeAngle_mul_exp_neg E
  unfold transferFree freeConj freeRot
  rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← hab, transferBlock_conj _ _ h1]

/-- `R_E = S_E⁻¹ T(E) S_E`, Definition 7.1 [def:transfer-matrices]. -/
theorem inv_freeConj_mul_transferFree_mul (W : ℕ) {E : ℝ} (hE : |E| < 2) :
    (freeConj W E)⁻¹ * transferFree W E * freeConj W E = freeRot W E := by
  have hU := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_freeConj W hE)
  rw [Matrix.mul_assoc, transferFree_mul_freeConj W hE, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]

/-- `R_E` is unitary, Definition 7.1 [def:transfer-matrices]. -/
theorem freeRot_mem_unitaryGroup (W : ℕ) (E : ℝ) :
    freeRot W E ∈ Matrix.unitaryGroup (Fin 2 × Fin W) ℂ := by
  have h1 := exp_freeAngle_mul_exp_neg E
  have hs1 := star_exp_neg_freeAngle E
  have hs2 := star_exp_freeAngle E
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold freeRot
  set D : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![Complex.exp (-(freeAngle E * Complex.I)),
    Complex.exp (freeAngle E * Complex.I)] with hDdef
  have hD : Dᴴ * D = 1 := by
    rw [hDdef]
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i
    · simp only [Pi.star_apply, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, hs1]
      exact h1
    · change star (Complex.exp (freeAngle E * Complex.I)) *
        Complex.exp (freeAngle E * Complex.I) = 1
      rw [hs2, mul_comm]
      exact h1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hD, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.one_kronecker_one]

/-- `S_E⁻¹ T_j(E + iη) S_E = R_E + iη B_E + g⁻¹ X_j` with `X_j = -S_E⁻¹ (P₁ ⊗ V_j) S_E`, proof of
Lemma 7.2 [uvs:lem:transfer-moments]. -/
theorem inv_freeConj_mul_transferMat_mul {W : ℕ} {E : ℝ} (hE : |E| < 2) (g η : ℝ)
    (V : Matrix (Fin W) (Fin W) ℂ) :
    (freeConj W E)⁻¹ * transferMat g (↑E + ↑η * Complex.I) V * freeConj W E =
      freeRot W E + ((η : ℂ) * Complex.I) • freeShear W E -
        ((g : ℂ)⁻¹) • ((freeConj W E)⁻¹ * (!![1, 0; 0, 0] ⊗ₖ V) * freeConj W E) := by
  have hz : transferFree W (↑E + ↑η * Complex.I) = transferFree W E +
      ((η : ℂ) * Complex.I) • (!![1, 0; 0, 0] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) := by
    have : (!![(E : ℂ) + η * Complex.I, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) =
        !![(E : ℂ), -1; 1, 0] + ((η : ℂ) * Complex.I) • !![1, 0; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    unfold transferFree
    rw [this, Matrix.add_kronecker, Matrix.smul_kronecker]
  have hR := inv_freeConj_mul_transferFree_mul W hE
  unfold freeShear
  unfold transferMat
  rw [hz, ← hR]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul]

end LSBA
