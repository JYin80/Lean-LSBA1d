import LSBA.Dyson.DeformedRoot

/-!
# Unitary covariance of `M_B`

The conjugation rule `M_{UBU*} = U M_B U*` (Appendix A.16 [app:deformed-dyson]).
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section
open scoped Classical

namespace LSBA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unitary covariance of `M_B(z)`, Lemma A.21 [da:lem:deformed]. -/
theorem MB_conj [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ) {B : Matrix ι ι ℂ}
    (hB : B.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    MB ((U : Matrix ι ι ℂ) * B * star (U : Matrix ι ι ℂ)) z =
      (U : Matrix ι ι ℂ) * MB B z * star (U : Matrix ι ι ℂ) := by
  set V : Matrix ι ι ℂ := (U : Matrix ι ι ℂ) with hV
  have hUU : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have hUU' : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hA : (V * B * star V).IsHermitian := by
    have := Matrix.isHermitian_conjTranspose_mul_mul (star V) hB
    rwa [← Matrix.star_eq_conjTranspose, star_star] at this
  -- conjugation rule for the trial profile
  have hprof : ∀ q : ℂ, 0 < (z + q).im →
      deformedMat (V * B * star V) z q = V * deformedMat B z q * star V := by
    intro q hq
    have hX : (-B - (z + q) • (1 : Matrix ι ι ℂ)) * resolventMat (-B) (z + q) = 1 :=
      sub_smul_mul_resolventMat hB.neg hq.ne'
    have hXA : -(V * B * star V) - (z + q) • (1 : Matrix ι ι ℂ) =
        V * (-B - (z + q) • (1 : Matrix ι ι ℂ)) * star V := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul, hUU]
    unfold deformedMat resolventMat
    refine Matrix.inv_eq_right_inv ?_
    rw [hXA]
    calc V * (-B - (z + q) • (1 : Matrix ι ι ℂ)) * star V *
          (V * resolventMat (-B) (z + q) * star V)
        = V * ((-B - (z + q) • (1 : Matrix ι ι ℂ)) * (star V * V) *
            resolventMat (-B) (z + q)) * star V := by simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hUU', Matrix.mul_one]
          rw [hX, Matrix.mul_one, hUU]
  have hmB := isDeformedRoot_mB hB hz
  have hmA := isDeformedRoot_mB hA hz
  have hw : 0 < (z + mB B z).im := by rw [Complex.add_im]; linarith [hmB.1]
  have hmap : deformedMap (V * B * star V) z (mB B z) = deformedMap B z (mB B z) := by
    unfold deformedMap ntr
    rw [hprof _ hw, Matrix.trace_mul_comm (V * deformedMat B z (mB B z)) (star V),
      ← Matrix.mul_assoc, hUU', Matrix.one_mul]
  have hroot : IsDeformedRoot (V * B * star V) z (mB B z) :=
    ⟨hmB.1, by rw [hmap]; exact hmB.2⟩
  have heq : mB (V * B * star V) z = mB B z := IsDeformedRoot.unique hA hz hmA hroot
  unfold MB
  rw [heq, hprof _ hw]

end LSBA
