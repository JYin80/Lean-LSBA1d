import LSBA.Spectral.EigMass
import LSBA.Spectral.Measurability

/-!
# Eigenfunction correlators

The correlator `Σ_{λ_k ∈ J} |ψ_k(x)| |ψ_k(y)|` of a Hermitian matrix, its bounds `0 ≤ Q ≤ 1`, its
form through the sorted eigenvalues and the adjugate profile on simple spectrum, and Jensen for the
diagonal spectral weight `Σ_k |ψ_k(x)|² φ(λ_k)`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenfunction correlator `Q_{xy}(J) = Σ_{λ_k ∈ J} |ψ_k(x)| |ψ_k(y)|` (the coordinate
form of the block correlator of Appendix E.1 [app:fr-concentration-proof]), with the eigenvectors of
`eigenvectorBasis`; `0` off Hermitian
matrices. -/
def eigCorr {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (J : Set ℝ) (x y : n) :
    ℝ :=
  if hA : A.IsHermitian then
    ∑ k, if hA.eigenvalues k ∈ J then ‖hA.eigenvectorBasis k x‖ * ‖hA.eigenvectorBasis k y‖ else 0
  else 0

/-- `0 ≤ Q_{xy}(J)`. -/
theorem eigCorr_nonneg (A : Matrix n n ℂ) (J : Set ℝ) (x y : n) : 0 ≤ eigCorr A J x y := by
  unfold eigCorr
  split_ifs with hA
  · exact Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  · exact le_rfl

/-- `eigCorr` is the mass correlator of the singletons `{x}`, `{y}`. -/
private lemma eigCorr_eq_eigMassCorr (A : Matrix n n ℂ) (J : Set ℝ) (x y : n) :
    eigCorr A J x y = eigMassCorr A {x} {y} J := by
  unfold eigCorr eigMassCorr
  split_ifs with hA
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · simp only [Finset.sum_singleton]
      rw [← mul_pow, Real.sqrt_sq (by positivity)]
    · rfl
  · rfl

/-- `Q_{xy}(J) ≤ Σ_k (|ψ_k(x)|² + |ψ_k(y)|²)/2 = 1`. -/
theorem eigCorr_le_one (A : Matrix n n ℂ) (J : Set ℝ) (x y : n) : eigCorr A J x y ≤ 1 := by
  rw [eigCorr_eq_eigMassCorr]
  simpa using eigMassCorr_le_sqrt_card A {x} {y} J

/-- On simple spectrum, `Q_{xy}(J)` through the sorted eigenvalues and the adjugate profile. -/
theorem eigCorr_eq_sum_eigProfile {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hinj : Function.Injective hA.eigenvalues) (J : Set ℝ) (x y : n) :
    eigCorr A J x y = ∑ k, if eigAt A k ∈ J then
      Real.sqrt (eigProfile A k x) * Real.sqrt (eigProfile A k y) else 0 := by
  have hev : ∀ k, hA.eigenvalues k = eigAt A k := fun k => eigenvalues_eq_sortedEig hA k
  have hp : ∀ k i, eigProfile A k i = ‖hA.eigenvectorBasis k i‖ ^ 2 := by
    intro k i
    rw [norm_sq_eigenvectorBasis_eq_adjugate hA hinj]
    simp only [eigProfile, hev]
  unfold eigCorr
  simp only [hA, ↓reduceDIte]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hev, hp, Real.sqrt_sq (norm_nonneg _)]

/-- For an orthonormal eigenbasis, `Σ_k |ψ_k(i)|² = 1` for every coordinate `i`. -/
private lemma eigCorr_sum_sq_eq_one {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) :
    ∑ k, ‖hA.eigenvectorBasis k i‖ ^ 2 = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have h2 := congrFun (congrFun h i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def] at h2
  have h3 : ∀ k, hA.eigenvectorUnitary.1 i k * (starRingEnd ℂ) (hA.eigenvectorUnitary.1 i k) =
      ((‖hA.eigenvectorBasis k i‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  simp only [h3] at h2
  exact_mod_cast h2

/-- Jensen for the probability weights `|ψ_k(x)|²`:
`(Σ_k |ψ_k(x)|² φ(λ_k))² ≤ Σ_k |ψ_k(x)|² φ(λ_k)²`. -/
theorem eigMassSum_singleton_sq_le (A : Matrix n n ℂ) (x : n) (φ : ℝ → ℝ≥0∞) :
    eigMassSum A {x} φ ^ 2 ≤ eigMassSum A {x} (fun E => φ E ^ 2) := by
  unfold eigMassSum
  split_ifs with hA
  · simp only [Finset.sum_singleton]
    have hw : ∑ k, ENNReal.ofReal (‖hA.eigenvectorBasis k x‖ ^ 2) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), eigCorr_sum_sq_eq_one hA,
        ENNReal.ofReal_one]
    have := ENNReal.rpow_arith_mean_le_arith_mean_rpow (s := (Finset.univ : Finset n))
      (fun k => ENNReal.ofReal (‖hA.eigenvectorBasis k x‖ ^ 2))
      (fun k => φ (hA.eigenvalues k)) hw (p := 2) (by norm_num)
    simpa [ENNReal.rpow_two] using this
  · simp

end LSBA
