import LSBA.Transfer.Basic

/-!
# Boundary frames and the matrix `D_n`

The forms `J = diag(I, −I)` and `J_ph`, maximal isotropic boundary frames (8.8)
[up:eq:boundary-frame], the matrix `D_n` of (8.10) [up:eq:D-definition], the symplectic identity
`Pᴴ J_ph P = J_ph` for transfer products, and (8.13) [eq:c-D].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `J = diag(I_W, -I_W)` of Section 8.2 [sec:upper-conversion]. -/
def isoJ (W : ℕ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  !![1, 0; 0, -1] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)

/-- `J_ph = [[0, -i I_W], [i I_W, 0]]` (proof of Proposition 8.4(i)
[up:prop:conversion]). -/
def phJ (W : ℕ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  !![0, -Complex.I; Complex.I, 0] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)

/-- The `2W × W` matrix `(X; Y)`. -/
def colStack {W : ℕ} (X Y : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  Matrix.of fun p α => if p.1 = 0 then X p.2 α else Y p.2 α

/-- Orthonormal frame of a maximal `J`-isotropic subspace, (8.8) [up:eq:boundary-frame]. -/
def IsBoundaryFrame {W : ℕ} (Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ) : Prop :=
  Φᴴ * Φ = 1 ∧ Φᴴ * isoJ W * Φ = 0

/-- `√2 (I_W 0) S* M S Φ` with `S = S_0` of Definition 7.1 [def:transfer-matrices]; for
`M = T_n ⋯ T_1` this is `D_n(Φ; E)` of (8.10) [up:eq:D-definition]. -/
def frameD {W : ℕ} (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun α β => ((Real.sqrt 2 : ℝ) : ℂ) * ((freeConj W 0)ᴴ * M * freeConj W 0 * Φ) (0, α) β

private theorem frames_colStack_gram {W : ℕ} (X Y X' Y' : Matrix (Fin W) (Fin W) ℂ) :
    (colStack X Y)ᴴ * colStack X' Y' = Xᴴ * X' + Yᴴ * Y' := by
  ext α β
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, colStack,
    Matrix.conjTranspose_apply]

private theorem frames_colStack_gram_isoJ {W : ℕ} (X Y X' Y' : Matrix (Fin W) (Fin W) ℂ) :
    (colStack X Y)ᴴ * isoJ W * colStack X' Y' = Xᴴ * X' - Yᴴ * Y' := by
  ext α β
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, colStack, isoJ,
    Matrix.conjTranspose_apply, Matrix.one_apply, sub_eq_add_neg]

private theorem frames_colStack_top_bot {W : ℕ} (Q : Matrix (Fin 2 × Fin W) (Fin W) ℂ) :
    Q = colStack (Matrix.of fun α β => Q (0, α) β) (Matrix.of fun α β => Q (1, α) β) := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack]

private theorem frames_smul_colStack {W : ℕ} (c : ℂ) (X Y : Matrix (Fin W) (Fin W) ℂ) :
    c • colStack X Y = colStack (c • X) (c • Y) := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack]

private theorem frames_sqrt_inv_sq :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (1 / 2 : ℂ) := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast
  norm_num

private theorem frames_sqrt_mul_inv :
    ((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (by norm_num)).ne']
  simp

private theorem frames_mem_unitary_iff {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} :
    U ∈ Matrix.unitaryGroup (Fin W) ℂ ↔ Uᴴ * U = 1 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]

private theorem frames_transferMat_phJ {W : ℕ} (g z : ℝ) (V : Matrix (Fin W) (Fin W) ℂ)
    (hV : V.IsHermitian) :
    (transferMat g (z : ℂ) V)ᴴ * phJ W * transferMat g (z : ℂ) V = phJ W := by
  have hc : star ((g : ℂ)⁻¹) = (g : ℂ)⁻¹ := by simp
  have he : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = !![1, 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have ha : (!![(z : ℂ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = !![(z : ℂ), 1; -1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  unfold transferMat transferFree phJ
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_kronecker, hc, he, ha, hV.eq, Matrix.conjTranspose_one]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have f1 : (!![(z : ℂ), 1; -1, 0] * !![0, -Complex.I; Complex.I, 0] * !![(z : ℂ), -1; 1, 0] :
      Matrix (Fin 2) (Fin 2) ℂ) = !![0, -Complex.I; Complex.I, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have f2 : (!![(z : ℂ), 1; -1, 0] * !![0, -Complex.I; Complex.I, 0] * !![1, 0; 0, 0] :
      Matrix (Fin 2) (Fin 2) ℂ) =
      -(!![1, 0; 0, 0] * !![0, -Complex.I; Complex.I, 0] * !![(z : ℂ), -1; 1, 0]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have f3 : (!![1, 0; 0, 0] * !![0, -Complex.I; Complex.I, 0] * !![1, 0; 0, 0] :
      Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hneg : ∀ m : Matrix (Fin 2) (Fin 2) ℂ, (-m) ⊗ₖ V = -(m ⊗ₖ V) := by
    intro m
    ext i j
    simp
  rw [f1, f2, f3, hneg, Matrix.zero_kronecker, smul_zero, sub_zero, smul_neg, sub_neg_eq_add]
  abel

/-- `T_i* J_ph T_i = J_ph` for real `z` and Hermitian blocks, for products (proof of
Proposition 8.4(i) [up:prop:conversion]). -/
theorem transferProd_conjTranspose_mul_phJ {W : ℕ} (g z : ℝ) (V : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (hV : ∀ k, (V k).IsHermitian) (n : ℕ) :
    (transferProd g (z : ℂ) V n)ᴴ * phJ W * transferProd g (z : ℂ) V n = phJ W := by
  induction n with
  | zero => simp [transferProd]
  | succ n ih =>
    have hT := frames_transferMat_phJ g z (V n) (hV n)
    simp only [transferProd]
    calc (transferMat g (z : ℂ) (V n) * transferProd g (z : ℂ) V n)ᴴ * phJ W *
          (transferMat g (z : ℂ) (V n) * transferProd g (z : ℂ) V n)
        = (transferProd g (z : ℂ) V n)ᴴ *
            ((transferMat g (z : ℂ) (V n))ᴴ * phJ W * transferMat g (z : ℂ) (V n)) *
            transferProd g (z : ℂ) V n := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = phJ W := by rw [hT, ih]

private theorem frames_freeConj_eq (W : ℕ) :
    freeConj W 0 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      (!![1, 1; Complex.I, -Complex.I] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) := by
  have h1 : Complex.exp (((freeAngle 0 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    unfold freeAngle
    rw [show (0 : ℝ) / 2 = 0 by norm_num, Real.arccos_zero, Complex.exp_mul_I]
    simp
  have h2 : Complex.exp (-(((freeAngle 0 : ℝ) : ℂ) * Complex.I)) = -Complex.I := by
    rw [Complex.exp_neg, h1, Complex.inv_I]
  have h3 : Real.sin (freeAngle 0) = 1 := by
    unfold freeAngle
    rw [show (0 : ℝ) / 2 = 0 by norm_num, Real.arccos_zero, Real.sin_pi_div_two]
  unfold freeConj
  rw [h1, h2, h3, mul_one]

private theorem frames_conjTranspose_freeConj (W : ℕ) :
    (freeConj W 0)ᴴ = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      (!![1, -Complex.I; 1, Complex.I] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) := by
  rw [frames_freeConj_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  congr 1
  · simp
  · congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp

private theorem frames_freeConj_conjTranspose_mul (W : ℕ) :
    (freeConj W 0)ᴴ * freeConj W 0 = 1 := by
  rw [frames_conjTranspose_freeConj, frames_freeConj_eq, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, frames_sqrt_inv_sq]
  have : (!![1, -Complex.I; 1, Complex.I] * !![1, 1; Complex.I, -Complex.I] :
      Matrix (Fin 2) (Fin 2) ℂ) = (2 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf
  rw [this, Matrix.smul_kronecker, Matrix.one_kronecker_one, smul_smul]
  norm_num

private theorem frames_freeConj_mul_conjTranspose (W : ℕ) :
    freeConj W 0 * (freeConj W 0)ᴴ = 1 :=
  mul_eq_one_comm.mp (frames_freeConj_conjTranspose_mul W)

private theorem frames_freeConj_conjTranspose_phJ (W : ℕ) :
    (freeConj W 0)ᴴ * phJ W * freeConj W 0 = isoJ W := by
  unfold phJ isoJ
  rw [frames_conjTranspose_freeConj, frames_freeConj_eq, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.one_mul, frames_sqrt_inv_sq]
  have : (!![1, -Complex.I; 1, Complex.I] * !![0, -Complex.I; Complex.I, 0] *
      !![1, 1; Complex.I, -Complex.I] : Matrix (Fin 2) (Fin 2) ℂ) =
      (2 : ℂ) • !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf
  rw [this, Matrix.smul_kronecker, smul_smul]
  norm_num

private theorem frames_freeConj_isoJ (W : ℕ) :
    freeConj W 0 * isoJ W * (freeConj W 0)ᴴ = phJ W := by
  calc freeConj W 0 * isoJ W * (freeConj W 0)ᴴ
      = freeConj W 0 * ((freeConj W 0)ᴴ * phJ W * freeConj W 0) * (freeConj W 0)ᴴ := by
        rw [frames_freeConj_conjTranspose_phJ]
    _ = (freeConj W 0 * (freeConj W 0)ᴴ) * phJ W * (freeConj W 0 * (freeConj W 0)ᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = phJ W := by rw [frames_freeConj_mul_conjTranspose, Matrix.one_mul, Matrix.mul_one]

private theorem frames_frameD_eq {W : ℕ} (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ) :
    frameD M Φ = ((Real.sqrt 2 : ℝ) : ℂ) •
      (Matrix.of fun α β => ((freeConj W 0)ᴴ * M * freeConj W 0 * Φ) (0, α) β) := by
  ext α β
  simp [frameD]

private theorem frames_decomp {W : ℕ} {M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hM : Mᴴ * phJ W * M = phJ W) {Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ}
    (hΦ : IsBoundaryFrame Φ) :
    ∃ X Y : Matrix (Fin W) (Fin W) ℂ,
      (freeConj W 0)ᴴ * M * freeConj W 0 * Φ = colStack X Y ∧
        frameD M Φ = ((Real.sqrt 2 : ℝ) : ℂ) • X ∧ Xᴴ * X = Yᴴ * Y := by
  have hiso : ((freeConj W 0)ᴴ * M * freeConj W 0 * Φ)ᴴ * isoJ W *
      ((freeConj W 0)ᴴ * M * freeConj W 0 * Φ) = 0 := by
    calc ((freeConj W 0)ᴴ * M * freeConj W 0 * Φ)ᴴ * isoJ W *
          ((freeConj W 0)ᴴ * M * freeConj W 0 * Φ)
        = Φᴴ * (freeConj W 0)ᴴ * (Mᴴ * (freeConj W 0 * isoJ W * (freeConj W 0)ᴴ) * M) *
            freeConj W 0 * Φ := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
      _ = Φᴴ * ((freeConj W 0)ᴴ * phJ W * freeConj W 0) * Φ := by
          rw [frames_freeConj_isoJ, hM]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [frames_freeConj_conjTranspose_phJ]; exact hΦ.2
  obtain ⟨X, Y, hQ⟩ : ∃ X Y : Matrix (Fin W) (Fin W) ℂ,
      (freeConj W 0)ᴴ * M * freeConj W 0 * Φ = colStack X Y :=
    ⟨_, _, frames_colStack_top_bot _⟩
  refine ⟨X, Y, hQ, ?_, ?_⟩
  · rw [frames_frameD_eq, hQ]
    congr 1
  · rw [hQ] at hiso
    exact sub_eq_zero.mp (by rw [← frames_colStack_gram_isoJ]; exact hiso)

private theorem frames_sqrt_mul_self : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  simp

private theorem frames_star_sqrt : star ((Real.sqrt 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := by
  simp

/-- The two blocks of `S* M S Φ` have equal Gram matrices; hence
`(M S Φ)*(M S Φ) = D* D`, the norm identity of (8.13) [eq:c-D]. -/
theorem frameD_gram {W : ℕ} {M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hM : Mᴴ * phJ W * M = phJ W) {Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ}
    (hΦ : IsBoundaryFrame Φ) :
    (M * freeConj W 0 * Φ)ᴴ * (M * freeConj W 0 * Φ) = (frameD M Φ)ᴴ * frameD M Φ := by
  obtain ⟨X, Y, hQ, hD, hXY⟩ := frames_decomp hM hΦ
  have hSS := frames_freeConj_mul_conjTranspose W
  have h1 : (M * freeConj W 0 * Φ)ᴴ * (M * freeConj W 0 * Φ) =
      ((freeConj W 0)ᴴ * M * freeConj W 0 * Φ)ᴴ * ((freeConj W 0)ᴴ * M * freeConj W 0 * Φ) := by
    calc (M * freeConj W 0 * Φ)ᴴ * (M * freeConj W 0 * Φ)
        = (M * freeConj W 0 * Φ)ᴴ * (freeConj W 0 * (freeConj W 0)ᴴ) * (M * freeConj W 0 * Φ) := by
          rw [hSS, Matrix.mul_one]
      _ = _ := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
  rw [h1, hQ, hD, frames_colStack_gram, ← hXY, Matrix.conjTranspose_smul, frames_star_sqrt,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, frames_sqrt_mul_self, two_smul]

open scoped ComplexOrder in
private theorem frames_isUnit_frameD {W : ℕ} {M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hM : Mᴴ * phJ W * M = phJ W) (hMu : IsUnit M) {Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ}
    (hΦ : IsBoundaryFrame Φ) : IsUnit (frameD M Φ) := by
  obtain ⟨M', hM'⟩ := hMu.exists_left_inv
  have hSS := frames_freeConj_conjTranspose_mul W
  have hDD := frameD_gram hM hΦ
  have hLR : (Φᴴ * (freeConj W 0)ᴴ * M') * (M * freeConj W 0 * Φ) = 1 := by
    calc (Φᴴ * (freeConj W 0)ᴴ * M') * (M * freeConj W 0 * Φ)
        = Φᴴ * ((freeConj W 0)ᴴ * (M' * M) * freeConj W 0) * Φ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM', Matrix.mul_one, hSS, Matrix.mul_one, hΦ.1]
  have hker : ∀ x : Fin W → ℂ, ((frameD M Φ)ᴴ * frameD M Φ) *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [← hDD] at hx
    have h0 : star ((M * freeConj W 0 * Φ) *ᵥ x) ⬝ᵥ ((M * freeConj W 0 * Φ) *ᵥ x) = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hx,
        dotProduct_zero]
    have h1 : (M * freeConj W 0 * Φ) *ᵥ x = 0 := dotProduct_star_self_eq_zero.mp h0
    calc x = ((Φᴴ * (freeConj W 0)ᴴ * M') * (M * freeConj W 0 * Φ)) *ᵥ x := by
          rw [hLR, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  have hDDu : IsUnit ((frameD M Φ)ᴴ * frameD M Φ) := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have : ((frameD M Φ)ᴴ * frameD M Φ) *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hker _ this)
  rw [Matrix.isUnit_iff_isUnit_det] at hDDu ⊢
  rw [Matrix.det_mul] at hDDu
  exact isUnit_of_mul_isUnit_right hDDu

/-- (8.13) [eq:c-D]: `S* M S Φ = 2^{-1/2} (D; U D)` with `U` unitary and `D` invertible. -/
theorem frameD_spec {W : ℕ} {M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hM : Mᴴ * phJ W * M = phJ W) (hMu : IsUnit M) {Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ}
    (hΦ : IsBoundaryFrame Φ) :
    IsUnit (frameD M Φ) ∧ ∃ U ∈ Matrix.unitaryGroup (Fin W) ℂ,
      (freeConj W 0)ᴴ * M * freeConj W 0 * Φ =
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • colStack (frameD M Φ) (U * frameD M Φ) := by
  obtain ⟨X, Y, hQ, hD, hXY⟩ := frames_decomp hM hΦ
  have hunit := frames_isUnit_frameD hM hMu hΦ
  refine ⟨hunit, ?_⟩
  set s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hs
  set r : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) with hr
  have hrs : r * s = 1 := frames_sqrt_mul_inv
  have hsu : IsUnit s := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one hrs)
  have hXs : X = s • frameD M Φ := by
    rw [hD, smul_smul, mul_comm, hrs, one_smul]
  have hdetX : IsUnit X.det := by
    rw [hXs, Matrix.det_smul]
    exact (hsu.pow _).mul ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have hUu : (Y * X⁻¹)ᴴ * (Y * X⁻¹) = 1 := by
    calc (Y * X⁻¹)ᴴ * (Y * X⁻¹) = (X⁻¹)ᴴ * (Yᴴ * Y) * X⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (X * X⁻¹)ᴴ * (X * X⁻¹) := by
          rw [← hXY]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hdetX, Matrix.conjTranspose_one, Matrix.mul_one]
  refine ⟨Y * X⁻¹, frames_mem_unitary_iff.mpr hUu, ?_⟩
  rw [hQ, frames_smul_colStack, ← Matrix.mul_smul, ← hXs, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hdetX, Matrix.mul_one]

end LSBA
