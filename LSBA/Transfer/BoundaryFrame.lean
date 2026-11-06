import LSBA.Transfer.Frames

/-!
# The physical boundary frame

The frame `Φ^ph_{R₀} = (I; Q)(I + Q²)^{-1/2}`, `Q = max{1,g}R₀/g`, of the right boundary pairs in
the proof of Proposition 8.4(i) [up:prop:conversion], and `S*Φ^ph` as a boundary frame (8.8)
[up:eq:boundary-frame].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `Φ^ph_{R₀} = (I; Q)(I + Q²)^{-1/2}` with `Q = max{1,g} R₀ / g` (proof of
Proposition 8.4(i) [up:prop:conversion]). -/
def phFrame (g : ℝ) {W : ℕ} (R₀ : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  colStack 1 (((max 1 g / g : ℝ) : ℂ) • R₀) *
    cfc (fun x : ℝ => (1 + x ^ 2) ^ (-(1 / 2 : ℝ))) (((max 1 g / g : ℝ) : ℂ) • R₀)

private theorem boundaryFrame_colStack_gram {W : ℕ} (X Y X' Y' : Matrix (Fin W) (Fin W) ℂ) :
    (colStack X Y)ᴴ * colStack X' Y' = Xᴴ * X' + Yᴴ * Y' := by
  ext α β
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, colStack,
    Matrix.conjTranspose_apply]

private theorem boundaryFrame_colStack_gram_phJ {W : ℕ} (X Y X' Y' : Matrix (Fin W) (Fin W) ℂ) :
    (colStack X Y)ᴴ * phJ W * colStack X' Y' =
      Xᴴ * (-Complex.I • Y') + Yᴴ * (Complex.I • X') := by
  ext α β
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, colStack, phJ,
    Matrix.conjTranspose_apply, Matrix.one_apply, Finset.mul_sum, ← Finset.sum_neg_distrib,
    mul_assoc, mul_left_comm Complex.I, add_comm]

private theorem boundaryFrame_sqrt_inv_sq :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (1 / 2 : ℂ) := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast
  norm_num

private theorem boundaryFrame_freeConj_eq (W : ℕ) :
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

private theorem boundaryFrame_conjTranspose_freeConj (W : ℕ) :
    (freeConj W 0)ᴴ = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      (!![1, -Complex.I; 1, Complex.I] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) := by
  rw [boundaryFrame_freeConj_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  congr 1
  · simp
  · congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp

private theorem boundaryFrame_freeConj_conjTranspose_mul (W : ℕ) :
    (freeConj W 0)ᴴ * freeConj W 0 = 1 := by
  rw [boundaryFrame_conjTranspose_freeConj, boundaryFrame_freeConj_eq, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    boundaryFrame_sqrt_inv_sq]
  have : (!![1, -Complex.I; 1, Complex.I] * !![1, 1; Complex.I, -Complex.I] :
      Matrix (Fin 2) (Fin 2) ℂ) = (2 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf
  rw [this, Matrix.smul_kronecker, Matrix.one_kronecker_one, smul_smul]
  norm_num

private theorem boundaryFrame_freeConj_mul_conjTranspose (W : ℕ) :
    freeConj W 0 * (freeConj W 0)ᴴ = 1 :=
  mul_eq_one_comm.mp (boundaryFrame_freeConj_conjTranspose_mul W)

private theorem boundaryFrame_freeConj_conjTranspose_phJ (W : ℕ) :
    (freeConj W 0)ᴴ * phJ W * freeConj W 0 = isoJ W := by
  unfold phJ isoJ
  rw [boundaryFrame_conjTranspose_freeConj, boundaryFrame_freeConj_eq, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul, boundaryFrame_sqrt_inv_sq]
  have : (!![1, -Complex.I; 1, Complex.I] * !![0, -Complex.I; Complex.I, 0] *
      !![1, 1; Complex.I, -Complex.I] : Matrix (Fin 2) (Fin 2) ℂ) =
      (2 : ℂ) • !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf
  rw [this, Matrix.smul_kronecker, smul_smul]
  norm_num

private theorem boundaryFrame_freeConj_isoJ (W : ℕ) :
    freeConj W 0 * isoJ W * (freeConj W 0)ᴴ = phJ W := by
  calc freeConj W 0 * isoJ W * (freeConj W 0)ᴴ
      = freeConj W 0 * ((freeConj W 0)ᴴ * phJ W * freeConj W 0) * (freeConj W 0)ᴴ := by
        rw [boundaryFrame_freeConj_conjTranspose_phJ]
    _ = (freeConj W 0 * (freeConj W 0)ᴴ) * phJ W * (freeConj W 0 * (freeConj W 0)ᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = phJ W := by
        rw [boundaryFrame_freeConj_mul_conjTranspose, Matrix.one_mul, Matrix.mul_one]

private theorem boundaryFrame_cont_neg :
    Continuous fun x : ℝ => (1 + x ^ 2) ^ (-(1 / 2 : ℝ)) :=
  (continuous_const.add (continuous_pow 2)).rpow_const fun x =>
    Or.inl (by change (1 + x ^ 2 : ℝ) ≠ 0; positivity)

private theorem boundaryFrame_cont_pos :
    Continuous fun x : ℝ => (1 + x ^ 2) ^ (1 / 2 : ℝ) :=
  (continuous_const.add (continuous_pow 2)).rpow_const fun x =>
    Or.inl (by change (1 + x ^ 2 : ℝ) ≠ 0; positivity)

private theorem boundaryFrame_neg_mul_pos (x : ℝ) :
    (1 + x ^ 2) ^ (-(1 / 2 : ℝ)) * (1 + x ^ 2) ^ (1 / 2 : ℝ) = 1 := by
  rw [← Real.rpow_add (by positivity)]
  norm_num

private theorem boundaryFrame_selfAdjoint {g : ℝ} {W : ℕ} {R₀ : Matrix (Fin W) (Fin W) ℂ}
    (hR₀ : R₀.IsHermitian) : IsSelfAdjoint (((max 1 g / g : ℝ) : ℂ) • R₀) := by
  have h : star (((max 1 g / g : ℝ) : ℂ)) = ((max 1 g / g : ℝ) : ℂ) := Complex.conj_ofReal _
  have h2 : star R₀ = R₀ := hR₀
  change star _ = _
  rw [star_smul, h, h2]

private theorem boundaryFrame_cfc_mul_cfc {W : ℕ} {Q : Matrix (Fin W) (Fin W) ℂ}
    (hQ : IsSelfAdjoint Q) :
    cfc (fun x : ℝ => (1 + x ^ 2) ^ (-(1 / 2 : ℝ))) Q *
      cfc (fun x : ℝ => (1 + x ^ 2) ^ (1 / 2 : ℝ)) Q = 1 := by
  rw [← cfc_mul _ _ Q boundaryFrame_cont_neg.continuousOn boundaryFrame_cont_pos.continuousOn]
  simp only [boundaryFrame_neg_mul_pos]
  exact cfc_const_one ℝ Q

private theorem boundaryFrame_cfc_pos_sq {W : ℕ} {Q : Matrix (Fin W) (Fin W) ℂ}
    (hQ : IsSelfAdjoint Q) :
    cfc (fun x : ℝ => (1 + x ^ 2) ^ (1 / 2 : ℝ)) Q *
      cfc (fun x : ℝ => (1 + x ^ 2) ^ (1 / 2 : ℝ)) Q = 1 + Q * Q := by
  have hc : Continuous fun x : ℝ => (1 + x ^ 2) ^ (1 / 2 : ℝ) := boundaryFrame_cont_pos
  rw [← cfc_mul _ _ Q hc.continuousOn hc.continuousOn]
  have : (fun x : ℝ => (1 + x ^ 2) ^ (1 / 2 : ℝ) * (1 + x ^ 2) ^ (1 / 2 : ℝ)) =
      fun x : ℝ => 1 + x * x := by
    funext x
    rw [← Real.rpow_add (by positivity)]
    norm_num
    ring
  rw [this]
  rw [show cfc (fun x : ℝ => 1 + x * x) Q =
      cfc (fun x : ℝ => (fun _ : ℝ => (1 : ℝ)) x + (fun x : ℝ => x * x) x) Q from rfl,
    cfc_add (a := Q) (fun _ : ℝ => (1 : ℝ)) (fun x : ℝ => x * x) continuous_const.continuousOn
      (continuous_id.mul continuous_id).continuousOn,
    cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) Q continuous_id.continuousOn
      continuous_id.continuousOn, cfc_id' ℝ Q, cfc_const_one ℝ Q]

/-- `S* Φ^ph_{R₀}` satisfies (8.8) [up:eq:boundary-frame] for Hermitian `R₀`. -/
theorem isBoundaryFrame_phFrame {g : ℝ} (hg : 0 < g) {W : ℕ} {R₀ : Matrix (Fin W) (Fin W) ℂ}
    (hR₀ : R₀.IsHermitian) : IsBoundaryFrame ((freeConj W 0)ᴴ * phFrame g R₀) := by
  have hQ := boundaryFrame_selfAdjoint (g := g) hR₀
  set Q := ((max 1 g / g : ℝ) : ℂ) • R₀ with hQdef
  set A := cfc (fun x : ℝ => (1 + x ^ 2) ^ (-(1 / 2 : ℝ))) Q with hA
  set B := cfc (fun x : ℝ => (1 + x ^ 2) ^ (1 / 2 : ℝ)) Q with hB
  have hAs : Aᴴ = A := (cfc_predicate _ Q : IsSelfAdjoint A)
  have hBs : Bᴴ = B := (cfc_predicate _ Q : IsSelfAdjoint B)
  have hAB : A * B = 1 := boundaryFrame_cfc_mul_cfc hQ
  have hBA : B * A = 1 := by
    rw [← (cfc_commute_cfc _ _ Q).eq]; exact hAB
  have hBB : B * B = 1 + Q * Q := boundaryFrame_cfc_pos_sq hQ
  have hQh : Qᴴ = Q := hQ
  have hΦ : phFrame g R₀ = colStack 1 Q * A := rfl
  have hgram : (phFrame g R₀)ᴴ * phFrame g R₀ = 1 := by
    calc (phFrame g R₀)ᴴ * phFrame g R₀
        = A * ((colStack 1 Q)ᴴ * colStack 1 Q) * A := by
          rw [hΦ, Matrix.conjTranspose_mul, hAs]; simp only [Matrix.mul_assoc]
      _ = (A * B) * (B * A) := by
          rw [boundaryFrame_colStack_gram, Matrix.conjTranspose_one, hQh, Matrix.one_mul, ← hBB]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, hBA, Matrix.one_mul]
  have hJ : (phFrame g R₀)ᴴ * phJ W * phFrame g R₀ = 0 := by
    have h0 : (colStack 1 Q)ᴴ * phJ W * colStack 1 Q = 0 := by
      rw [boundaryFrame_colStack_gram_phJ, Matrix.conjTranspose_one, hQh]
      simp
    calc (phFrame g R₀)ᴴ * phJ W * phFrame g R₀
        = A * ((colStack 1 Q)ᴴ * phJ W * colStack 1 Q) * A := by
          rw [hΦ, Matrix.conjTranspose_mul, hAs]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h0]; simp
  have hS := boundaryFrame_freeConj_mul_conjTranspose W
  constructor
  · calc ((freeConj W 0)ᴴ * phFrame g R₀)ᴴ * ((freeConj W 0)ᴴ * phFrame g R₀)
        = (phFrame g R₀)ᴴ * (freeConj W 0 * (freeConj W 0)ᴴ) * phFrame g R₀ := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
      _ = 1 := by rw [hS, Matrix.mul_one, hgram]
  · calc ((freeConj W 0)ᴴ * phFrame g R₀)ᴴ * isoJ W * ((freeConj W 0)ᴴ * phFrame g R₀)
        = (phFrame g R₀)ᴴ * (freeConj W 0 * isoJ W * (freeConj W 0)ᴴ) * phFrame g R₀ := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
      _ = 0 := by rw [boundaryFrame_freeConj_isoJ, hJ]

/-- `Φ^ph_{R₀} (I + Q²)^{1/2} = (I; Q)`. -/
theorem phFrame_mul_cfc {g : ℝ} (hg : 0 < g) {W : ℕ} {R₀ : Matrix (Fin W) (Fin W) ℂ}
    (hR₀ : R₀.IsHermitian) :
    phFrame g R₀ * cfc (fun x : ℝ => (1 + x ^ 2) ^ (1 / 2 : ℝ)) (((max 1 g / g : ℝ) : ℂ) • R₀) =
      colStack 1 (((max 1 g / g : ℝ) : ℂ) • R₀) := by
  have hQ := boundaryFrame_selfAdjoint (g := g) hR₀
  unfold phFrame
  rw [Matrix.mul_assoc, boundaryFrame_cfc_mul_cfc hQ, Matrix.mul_one]

end LSBA
