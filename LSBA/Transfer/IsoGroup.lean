import LSBA.Transfer.Frames
import LSBA.Transfer.OneStep

/-!
# The indefinite unitary group of `J`

The group of `J`-unitary matrices for `J = diag(I_W, −I_W)` and its subgroup 𝒢 of (8.24)
[eq:c-group]; the conjugated transfer products `S*(T_n⋯T_1)S` lie in it (Definition 8.5
[up:def:transfer-operator]); inverses and norms of `J`-unitary matrices (Lemma F.1
[cc:lem:quotient]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The group `𝒢 = {T : T* J T = J, det T = 1}` of (8.24) [eq:c-group], with
`J = diag(I_W, -I_W)`. -/
def isoGroup (W : ℕ) : Set (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :=
  {T | Tᴴ * isoJ W * T = isoJ W ∧ T.det = 1}

/-- `J* = J`. -/
theorem isoJ_conjTranspose (W : ℕ) : (isoJ W)ᴴ = isoJ W := by
  unfold isoJ
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `J² = 1`. -/
theorem isoJ_mul_isoJ (W : ℕ) : isoJ W * isoJ W = 1 := by
  unfold isoJ
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have : (!![1, 0; 0, -1] * !![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, Matrix.one_kronecker_one]

private theorem isoGroup_freeConj_eq (W : ℕ) :
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

private theorem isoGroup_sqrt_inv_sq :
    ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (1 / 2 : ℂ) := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast
  ring

private theorem isoGroup_conjTranspose_freeConj (W : ℕ) :
    (freeConj W 0)ᴴ = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      (!![1, -Complex.I; 1, Complex.I] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) := by
  rw [isoGroup_freeConj_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  congr 1
  · simp
  · congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp

private theorem isoGroup_freeConj_conjTranspose_mul (W : ℕ) :
    (freeConj W 0)ᴴ * freeConj W 0 = 1 := by
  rw [isoGroup_conjTranspose_freeConj, isoGroup_freeConj_eq, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, isoGroup_sqrt_inv_sq]
  have : (!![1, -Complex.I; 1, Complex.I] * !![1, 1; Complex.I, -Complex.I] :
      Matrix (Fin 2) (Fin 2) ℂ) = (2 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf
  rw [this, Matrix.smul_kronecker, Matrix.one_kronecker_one, smul_smul]
  norm_num

/-- The matrix `S = S_0` of Definition 7.1 [def:transfer-matrices] is unitary. -/
theorem freeConj_zero_mem_unitaryGroup (W : ℕ) :
    freeConj W 0 ∈ Matrix.unitaryGroup (Fin 2 × Fin W) ℂ := by
  have h := isoGroup_freeConj_conjTranspose_mul W
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  exact mul_eq_one_comm.mp h

/-- `S* J_ph S = J` (proof of Proposition 8.4(i) [up:prop:conversion]). -/
theorem conjTranspose_freeConj_mul_phJ_mul (W : ℕ) :
    (freeConj W 0)ᴴ * phJ W * freeConj W 0 = isoJ W := by
  unfold phJ isoJ
  rw [isoGroup_conjTranspose_freeConj, isoGroup_freeConj_eq, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.one_mul, isoGroup_sqrt_inv_sq]
  have : (!![1, -Complex.I; 1, Complex.I] * !![0, -Complex.I; Complex.I, 0] *
      !![1, 1; Complex.I, -Complex.I] : Matrix (Fin 2) (Fin 2) ℂ) =
      (2 : ℂ) • !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf
  rw [this, Matrix.smul_kronecker, smul_smul]
  norm_num

private theorem isoGroup_det_unipotent {W : ℕ} (a : Matrix (Fin W) (Fin W) ℂ) :
    (1 + !![0, 1; 0, 0] ⊗ₖ a : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ).det = 1 := by
  let e : Fin 2 × Fin W ≃ Fin W ⊕ Fin W :=
    (Equiv.prodCongr finTwoEquiv (Equiv.refl (Fin W))).trans (Equiv.boolProdEquivSum (Fin W))
  have h : Matrix.reindex e e (1 + !![0, 1; 0, 0] ⊗ₖ a : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      = Matrix.fromBlocks 1 a 0 1 := by
    ext p q
    rcases p with p | p <;> rcases q with q | q <;>
      simp [e, Matrix.reindex_apply, Matrix.one_apply, finTwoEquiv,
        Equiv.boolProdEquivSum]
  rw [← Matrix.det_reindex_self e, h, Matrix.det_fromBlocks_zero₂₁]
  simp

private theorem isoGroup_det_transferMat {W : ℕ} (g z : ℝ) (V : Matrix (Fin W) (Fin W) ℂ) :
    (transferMat g (z : ℂ) V).det = 1 := by
  have h : transferMat g (z : ℂ) V =
      (1 + !![0, 1; 0, 0] ⊗ₖ ((z : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - ((g : ℂ)⁻¹) • V)) *
        (!![0, -1; 1, 0] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) := by
    unfold transferMat transferFree
    ext ⟨i, α⟩ ⟨j, β⟩
    by_cases h : α = β <;>
      fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, h]
  rw [h, Matrix.det_mul, isoGroup_det_unipotent, Matrix.det_kronecker]
  simp

private theorem isoGroup_det_transferProd {W : ℕ} (g z : ℝ) (V : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (n : ℕ) : (transferProd g (z : ℂ) V n).det = 1 := by
  induction n with
  | zero => simp [transferProd]
  | succ n ih => rw [transferProd, Matrix.det_mul, isoGroup_det_transferMat, ih, one_mul]

private theorem isoGroup_freeConj_isoJ_conjTranspose (W : ℕ) :
    freeConj W 0 * isoJ W * (freeConj W 0)ᴴ = phJ W := by
  have hS := isoGroup_freeConj_conjTranspose_mul W
  have hS' : freeConj W 0 * (freeConj W 0)ᴴ = 1 := mul_eq_one_comm.mp hS
  calc freeConj W 0 * isoJ W * (freeConj W 0)ᴴ
      = freeConj W 0 * ((freeConj W 0)ᴴ * phJ W * freeConj W 0) * (freeConj W 0)ᴴ := by
        rw [conjTranspose_freeConj_mul_phJ_mul]
    _ = (freeConj W 0 * (freeConj W 0)ᴴ) * phJ W * (freeConj W 0 * (freeConj W 0)ᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = phJ W := by rw [hS', Matrix.one_mul, Matrix.mul_one]

/-- For real `z` and Hermitian blocks, `S* T_n ⋯ T_1 S ∈ 𝒢` (Definition 8.5
[up:def:transfer-operator]); here `det T_i = 1` for every block. -/
theorem conj_transferProd_mem_isoGroup {W : ℕ} (g z : ℝ) (V : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (hV : ∀ k, (V k).IsHermitian) (n : ℕ) :
    (freeConj W 0)ᴴ * transferProd g (z : ℂ) V n * freeConj W 0 ∈ isoGroup W := by
  have hS := isoGroup_freeConj_conjTranspose_mul W
  have hphJ := transferProd_conjTranspose_mul_phJ g z V hV n
  refine ⟨?_, ?_⟩
  · calc ((freeConj W 0)ᴴ * transferProd g (z : ℂ) V n * freeConj W 0)ᴴ * isoJ W *
          ((freeConj W 0)ᴴ * transferProd g (z : ℂ) V n * freeConj W 0)
        = (freeConj W 0)ᴴ * ((transferProd g (z : ℂ) V n)ᴴ *
            (freeConj W 0 * isoJ W * (freeConj W 0)ᴴ) * transferProd g (z : ℂ) V n) *
            freeConj W 0 := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
      _ = (freeConj W 0)ᴴ * phJ W * freeConj W 0 := by
          rw [isoGroup_freeConj_isoJ_conjTranspose, hphJ]
      _ = isoJ W := conjTranspose_freeConj_mul_phJ_mul W
  · rw [Matrix.det_mul, Matrix.det_mul, isoGroup_det_transferProd, mul_one, ← Matrix.det_mul, hS,
      Matrix.det_one]

/-- `T⁻¹ = J T* J` for `T* J T = J`. -/
theorem inv_eq_isoJ_mul_conjTranspose_mul {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : Tᴴ * isoJ W * T = isoJ W) : T⁻¹ = isoJ W * Tᴴ * isoJ W := by
  refine Matrix.inv_eq_left_inv ?_
  calc isoJ W * Tᴴ * isoJ W * T = isoJ W * (Tᴴ * isoJ W * T) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hT, isoJ_mul_isoJ]

/-- `‖T⁻¹‖ = ‖T‖` for `T* J T = J` (proof of Lemma F.1 [cc:lem:quotient]). -/
theorem norm_inv_eq_of_isoJ {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : Tᴴ * isoJ W * T = isoJ W) : ‖T⁻¹‖ = ‖T‖ := by
  have hJu : isoJ W ∈ Matrix.unitaryGroup (Fin 2 × Fin W) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, isoJ_conjTranspose,
      isoJ_mul_isoJ]
  rw [inv_eq_isoJ_mul_conjTranspose_mul hT]
  have h1 := CStarRing.norm_mul_coe_unitary (isoJ W * Tᴴ)
    (⟨isoJ W, hJu⟩ : unitary (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))
  have h2 := CStarRing.norm_coe_unitary_mul
    (⟨isoJ W, hJu⟩ : unitary (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) Tᴴ
  simp only at h1 h2
  rw [h1, h2, Matrix.l2_opNorm_conjTranspose]

end LSBA
