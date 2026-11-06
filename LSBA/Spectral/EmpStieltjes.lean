import LSBA.Spectral.Counts
import LSBA.Spectral.Resolvent
import LSBA.Dyson.Stieltjes

/-!
# The empirical Stieltjes transform

The normalized trace of the resolvent is the Stieltjes transform of the empirical spectral measure
(Section 1.1 [sec:model] notation; used in the proof of Lemma 1.3 [lem:rough-density], Appendix D.2
[sec:rough-density-proof]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `N⁻¹ Tr G(z)` is the Stieltjes transform of the empirical spectral measure. -/
theorem trace_resolventMat_eq_stieltjes {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    ((Fintype.card n : ℂ))⁻¹ * (resolventMat A z).trace = stieltjes (empMeasure A) z := by
  have hmeas : Measurable fun t : ℝ => ((t : ℂ) - z)⁻¹ :=
    (Complex.measurable_ofReal.sub_const z).inv
  have hint : ∀ k, Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹) (Measure.dirac (hA.eigenvalues k)) :=
    fun k => integrable_dirac enorm_lt_top
  have hnorm : ∀ k, ∑ x, hA.eigenvectorBasis k x * star (hA.eigenvectorBasis k x) = 1 := by
    intro k
    have h1 := (hA.eigenvectorBasis.orthonormal.1 k)
    have h2 : ‖hA.eigenvectorBasis k‖ ^ 2 = ∑ x, ‖hA.eigenvectorBasis k x‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq _
    rw [h1] at h2
    have h3 : (∑ x, ‖hA.eigenvectorBasis k x‖ ^ 2 : ℝ) = 1 := by linarith
    have h4 : ∑ x, hA.eigenvectorBasis k x * star (hA.eigenvectorBasis k x) =
        ((∑ x, ‖hA.eigenvectorBasis k x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_comm, Complex.star_def, Complex.conj_mul']
    rw [h4, h3]
    simp
  have hL : (resolventMat A z).trace = ∑ k, ((hA.eigenvalues k : ℂ) - z)⁻¹ := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply, resolventMat_apply hA hz]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_div, hnorm k, one_div]
  have hR : stieltjes (empMeasure A) z =
      ((Fintype.card n : ℂ))⁻¹ * ∑ k, ((hA.eigenvalues k : ℂ) - z)⁻¹ := by
    simp only [stieltjes, empMeasure, hA, ↓reduceDIte]
    rw [integral_smul_measure, integral_finsetSum_measure (fun k _ => hint k)]
    simp_rw [integral_dirac' _ _ hmeas.stronglyMeasurable]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul]
    push_cast
    rfl
  rw [hL, hR]

end LSBA
