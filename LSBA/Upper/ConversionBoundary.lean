import LSBA.Transfer.Path
import LSBA.Transfer.BoundaryFrame

/-!
# Boundary comparison

(8.14) [eq:c-boundary-comparison]: `‖G(n, 0)‖ ≤ ‖D′⁻¹‖ (‖G(0, 0)‖ + ‖G(1, 0)‖)` for the block path,
with `D′` the matrix (8.10) [up:eq:D-definition] of the reversed transfer product and the physical
boundary frame, for
every Hermitian right shift.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

private theorem conversionBoundary_colStack_gram {W : ℕ} (X Y X' Y' : Matrix (Fin W) (Fin W) ℂ) :
    (colStack X Y)ᴴ * colStack X' Y' = Xᴴ * X' + Yᴴ * Y' := by
  ext α β
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, colStack,
    Matrix.conjTranspose_apply]

private theorem conversionBoundary_colStack_mul {W : ℕ} (X Y K : Matrix (Fin W) (Fin W) ℂ) :
    colStack X Y * K = colStack (X * K) (Y * K) := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack, Matrix.mul_apply]

private theorem conversionBoundary_colStack_mulVec {W : ℕ} (X Y : Matrix (Fin W) (Fin W) ℂ)
    (u : Fin W → ℂ) : colStack X Y *ᵥ u = pairVec (X *ᵥ u) (Y *ᵥ u) := by
  ext ⟨i, α⟩
  fin_cases i <;> simp [colStack, pairVec, Matrix.mulVec, dotProduct]

private theorem conversionBoundary_sqrt_inv_sq :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (1 / 2 : ℂ) := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast
  norm_num

private theorem conversionBoundary_freeConj_eq (W : ℕ) :
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

private theorem conversionBoundary_freeConj_conjTranspose_mul (W : ℕ) :
    (freeConj W 0)ᴴ * freeConj W 0 = 1 := by
  have hT : (freeConj W 0)ᴴ = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      (!![1, -Complex.I; 1, Complex.I] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) := by
    rw [conversionBoundary_freeConj_eq, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    congr 1
    · simp
    · congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  rw [hT, conversionBoundary_freeConj_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, conversionBoundary_sqrt_inv_sq]
  have : (!![1, -Complex.I; 1, Complex.I] * !![1, 1; Complex.I, -Complex.I] :
      Matrix (Fin 2) (Fin 2) ℂ) = (2 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf
  rw [this, Matrix.smul_kronecker, Matrix.one_kronecker_one, smul_smul]
  norm_num

private theorem conversionBoundary_freeConj_mul_conjTranspose (W : ℕ) :
    freeConj W 0 * (freeConj W 0)ᴴ = 1 :=
  mul_eq_one_comm.mp (conversionBoundary_freeConj_conjTranspose_mul W)

private theorem conversionBoundary_isUnit_transferProd {W : ℕ} (g : ℝ) (z : ℂ)
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (j : ℕ) : IsUnit (transferProd g z V j) := by
  induction j with
  | zero => exact isUnit_one
  | succ j ih =>
    have h : IsUnit (transferMat g z (V j)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr
        (Matrix.isUnit_det_of_right_inverse (transferMat_mul_transferInv g z (V j)))
    exact h.mul ih

private theorem conversionBoundary_norm_one_le {m : Type*} [Fintype m] [DecidableEq m] :
    ‖(1 : Matrix m m ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  simp

private theorem conversionBoundary_norm_isometry_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (Φ : Matrix m n ℂ) (h : Φᴴ * Φ = 1) : ‖Φ‖ ≤ 1 := by
  have h1 : ‖Φ‖ * ‖Φ‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, h]
    exact conversionBoundary_norm_one_le
  nlinarith [norm_nonneg Φ]

private theorem conversionBoundary_norm_colStack_le {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) :
    ‖colStack A B‖ ≤ ‖A‖ + ‖B‖ := by
  have h1 : ‖colStack A B‖ * ‖colStack A B‖ ≤ (‖A‖ + ‖B‖) * (‖A‖ + ‖B‖) := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, conversionBoundary_colStack_gram]
    calc ‖Aᴴ * A + Bᴴ * B‖ ≤ ‖Aᴴ * A‖ + ‖Bᴴ * B‖ := norm_add_le _ _
      _ = ‖A‖ * ‖A‖ + ‖B‖ * ‖B‖ := by
          rw [Matrix.l2_opNorm_conjTranspose_mul_self, Matrix.l2_opNorm_conjTranspose_mul_self]
      _ ≤ _ := by nlinarith [norm_nonneg A, norm_nonneg B]
  nlinarith [norm_nonneg (colStack A B), norm_nonneg A, norm_nonneg B]

/-- The norm comparison in the proof of (8.14) [eq:c-boundary-comparison]: from `(A; B) = M Φ C K`
for a transfer product
`M` with `Mᴴ J_ph M = J_ph` and a frame `Φ` with `S*Φ` a boundary frame and `Φ C = (I; Q)`,
one has `‖K‖ ≤ ‖D⁻¹‖ (‖A‖ + ‖B‖)` for `D = D(S*Φ)`. -/
private theorem conversionBoundary_abstract {W : ℕ}
    {M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hM : Mᴴ * phJ W * M = phJ W)
    (hMu : IsUnit M) {Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ}
    (hΦ : IsBoundaryFrame ((freeConj W 0)ᴴ * Φ)) {C K A B : Matrix (Fin W) (Fin W) ℂ}
    (hΦC : ∃ Q : Matrix (Fin W) (Fin W) ℂ, Φ * C = colStack 1 Q)
    (hcol : colStack A B = M * (Φ * C * K)) :
    ‖K‖ ≤ ‖(frameD M ((freeConj W 0)ᴴ * Φ))⁻¹‖ * (‖A‖ + ‖B‖) := by
  obtain ⟨Q, hΦC⟩ := hΦC
  have hSS : freeConj W 0 * (freeConj W 0)ᴴ = 1 :=
    conversionBoundary_freeConj_mul_conjTranspose W
  have hΦΦ : Φᴴ * Φ = 1 := by
    calc Φᴴ * Φ = Φᴴ * (freeConj W 0 * (freeConj W 0)ᴴ) * Φ := by rw [hSS, Matrix.mul_one]
      _ = ((freeConj W 0)ᴴ * Φ)ᴴ * ((freeConj W 0)ᴴ * Φ) := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
      _ = 1 := hΦ.1
  have hD := frameD_gram hM hΦ
  have hMSΦ : M * freeConj W 0 * ((freeConj W 0)ᴴ * Φ) = M * Φ := by
    rw [Matrix.mul_assoc M, ← Matrix.mul_assoc (freeConj W 0), hSS, Matrix.one_mul]
  rw [hMSΦ] at hD
  obtain ⟨hDu, -⟩ := frameD_spec hM hMu hΦ
  set D := frameD M ((freeConj W 0)ᴴ * Φ) with hDdef
  have hdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det _).mp hDu
  have hX : colStack A B = (M * Φ) * (C * K) := by
    rw [hcol]; simp only [Matrix.mul_assoc]
  have h1 : (D * (C * K))ᴴ * (D * (C * K)) = (colStack A B)ᴴ * colStack A B := by
    rw [hX]
    calc (D * (C * K))ᴴ * (D * (C * K)) = (C * K)ᴴ * (Dᴴ * D) * (C * K) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by
          rw [← hD]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h3 : ‖D * (C * K)‖ ≤ ‖colStack A B‖ := by
    have h := congrArg norm h1
    rw [Matrix.l2_opNorm_conjTranspose_mul_self, Matrix.l2_opNorm_conjTranspose_mul_self] at h
    nlinarith [norm_nonneg (D * (C * K)), norm_nonneg (colStack A B)]
  have h4 : C * K = D⁻¹ * (D * (C * K)) := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have h5 : ‖C * K‖ ≤ ‖D⁻¹‖ * ‖D * (C * K)‖ := by
    calc ‖C * K‖ = ‖D⁻¹ * (D * (C * K))‖ := by rw [← h4]
      _ ≤ _ := Matrix.l2_opNorm_mul _ _
  have hP1 : (colStack (1 : Matrix (Fin W) (Fin W) ℂ) 0)ᴴ * colStack 1 Q = 1 := by
    rw [conversionBoundary_colStack_gram]; simp
  have hK : K = ((colStack (1 : Matrix (Fin W) (Fin W) ℂ) 0)ᴴ * Φ) * (C * K) := by
    calc K = ((colStack (1 : Matrix (Fin W) (Fin W) ℂ) 0)ᴴ * colStack 1 Q) * K := by
          rw [hP1, Matrix.one_mul]
      _ = _ := by rw [← hΦC]; simp only [Matrix.mul_assoc]
  have hc1 : ‖colStack (1 : Matrix (Fin W) (Fin W) ℂ) 0‖ ≤ 1 := by
    refine conversionBoundary_norm_isometry_le _ ?_
    rw [conversionBoundary_colStack_gram]; simp
  have hc2 : ‖((colStack (1 : Matrix (Fin W) (Fin W) ℂ) 0)ᴴ * Φ)‖ ≤ 1 := by
    calc _ ≤ ‖(colStack (1 : Matrix (Fin W) (Fin W) ℂ) 0)ᴴ‖ * ‖Φ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * 1 := by
          rw [Matrix.l2_opNorm_conjTranspose]
          exact mul_le_mul hc1 (conversionBoundary_norm_isometry_le Φ hΦΦ) (norm_nonneg _)
            zero_le_one
      _ = 1 := one_mul 1
  have h6 : ‖K‖ ≤ ‖C * K‖ := by
    calc ‖K‖ = ‖((colStack (1 : Matrix (Fin W) (Fin W) ℂ) 0)ᴴ * Φ) * (C * K)‖ := by rw [← hK]
      _ ≤ ‖((colStack (1 : Matrix (Fin W) (Fin W) ℂ) 0)ᴴ * Φ)‖ * ‖C * K‖ :=
          Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖C * K‖ := mul_le_mul_of_nonneg_right hc2 (norm_nonneg _)
      _ = ‖C * K‖ := one_mul _
  have h7 := conversionBoundary_norm_colStack_le A B
  calc ‖K‖ ≤ ‖C * K‖ := h6
    _ ≤ ‖D⁻¹‖ * ‖D * (C * K)‖ := h5
    _ ≤ ‖D⁻¹‖ * ‖colStack A B‖ := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ ≤ ‖D⁻¹‖ * (‖A‖ + ‖B‖) := mul_le_mul_of_nonneg_left h7 (norm_nonneg _)

/-- (8.14) [eq:c-boundary-comparison]: `‖G(n, 0)‖ ≤ ‖D′⁻¹‖ (‖G(0, 0)‖ + ‖G(1, 0)‖)` with
`D′ = D_n(S* Φ^ph_{R₀}; E)` built from the reversed blocks `V_n, …, V_1`. -/
theorem pathOp_boundary_comparison {g : ℝ} (hg : 0 < g) {W n : ℕ} (hn : 1 ≤ n)
    (V : Fin (n + 1) → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ a, (V a).IsHermitian)
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (hR₀ : R₀.IsHermitian) (E : ℝ) :
    ‖blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.last n) 0‖ ≤
      ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ) (fun k => V ⟨n - k, by omega⟩) n)
          ((freeConj W 0)ᴴ * phFrame g R₀))⁻¹‖ *
        (‖blockOf (resolventMat (pathOp g V L₀ R₀) E) 0 0‖ +
          ‖blockOf (resolventMat (pathOp g V L₀ R₀) E) 1 0‖) := by
  have h1 : (1 : Fin (n + 1)) = ⟨1, by omega⟩ :=
    Fin.ext (by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)])
  have hM := transferProd_conjTranspose_mul_phJ g (max 1 g * E / g)
    (fun k => V ⟨n - k, by omega⟩) (fun k => hV _) n
  have hMu := conversionBoundary_isUnit_transferProd g ((max 1 g * E / g : ℝ) : ℂ)
    (fun k => V ⟨n - k, by omega⟩) n
  refine conversionBoundary_abstract hM hMu (isBoundaryFrame_phFrame hg hR₀)
    (C := cfc (fun x : ℝ => (1 + x ^ 2) ^ (1 / 2 : ℝ)) (((max 1 g / g : ℝ) : ℂ) • R₀))
    (K := blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.last n) 0)
    ⟨_, phFrame_mul_cfc hg hR₀⟩ ?_
  rw [h1]
  refine Matrix.ext_iff_mulVec.mpr fun u => ?_
  have h := pathCol_transferProd hg V L₀ R₀ E u
  have hQ := phFrame_mul_cfc hg hR₀
  have hmat : phFrame g R₀ * cfc (fun x : ℝ => (1 + x ^ 2) ^ (1 / 2 : ℝ))
      (((max 1 g / g : ℝ) : ℂ) • R₀) *
        blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.last n) 0 =
      colStack (blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.last n) 0)
        ((((max 1 g / g : ℝ) : ℂ) • R₀) *
          blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.last n) 0) := by
    rw [hQ, conversionBoundary_colStack_mul, Matrix.one_mul]
  rw [hmat, ← Matrix.mulVec_mulVec, conversionBoundary_colStack_mulVec,
    conversionBoundary_colStack_mulVec, ← Matrix.mulVec_mulVec]
  have e0 : pathCol g V L₀ R₀ E u 0 =
      blockOf (resolventMat (pathOp g V L₀ R₀) E) 0 0 *ᵥ u := by
    simp [pathCol]
  have e1 : pathCol g V L₀ R₀ E u 1 =
      blockOf (resolventMat (pathOp g V L₀ R₀) E) ⟨1, by omega⟩ 0 *ᵥ u := by
    simp [pathCol, hn]
  have en : pathCol g V L₀ R₀ E u n =
      blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.last n) 0 *ᵥ u := by
    simp [pathCol]
    rfl
  have en1 : pathCol g V L₀ R₀ E u (n + 1) =
      (((max 1 g / g : ℝ) : ℂ) • R₀) *ᵥ
        (blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.last n) 0 *ᵥ u) := by
    simp only [pathCol, Nat.not_succ_le_self, dite_false, ite_true]
  rw [e0, e1, en, en1] at h
  exact h

end LSBA
