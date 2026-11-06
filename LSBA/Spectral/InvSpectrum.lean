import LSBA.Spectral.SpecProj

/-!
# Spectra of inverses and truncated traces

For a Hermitian `R` with eigenvalues `r_k`, the truncated power sums
`Tr |R_<|^j = Σ_{|r_k| < s} |r_k|^j` (`R_< = R 1_{|R| < s}`); with `s = η⁻¹` these are the two
truncated traces of (9.43) [us:eq:spectrum]. For an invertible Hermitian `A`, the eigenvalues of
`A⁻¹` are the inverses of those of `A`, so the counts of `A⁻¹` in a set `S` are the counts of `A`
in `{x : x⁻¹ ∈ S}`: this turns the spectral conditions on `R = Γ⁻¹` in (9.43) [us:eq:spectrum],
(9.48)
[us:eq:complement-spectrum], (9.3) [us:eq:regular] and (9.6) [su:eq:prepared-large-rank] into
eigenvalue counts of `Γ`. Two facts on spectral projections: `rank 1_S(A) = #{k : λ_k ∈ S}`, and
`1_S(A) 1_T(A) = 1_S(A)` for `S ⊆ T`.
-/

open MeasureTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Tr |R_<|^j = Σ_{|r_k| < s} |r_k|^j` over the eigenvalues `r_k` of a Hermitian `R`
(`0` otherwise); the truncated traces of (9.43) [us:eq:spectrum] at `s = η⁻¹`. -/
def truncPowSum (R : Matrix n n ℂ) (s : ℝ) (j : ℕ) : ℝ :=
  if hR : R.IsHermitian then
    ∑ k ∈ univ.filter (fun k => |hR.eigenvalues k| < s), |hR.eigenvalues k| ^ j
  else 0

/-- Eigenvalue counts of an inverse: for an invertible Hermitian `A`,
`#{k : λ_k(A⁻¹) ∈ S} = #{k : λ_k(A)⁻¹ ∈ S}`. -/
theorem countIn_inv {A : Matrix n n ℂ} (hA : A.IsHermitian) (hu : IsUnit A) (S : Set ℝ) :
    countIn A⁻¹ S = countIn A {x | x⁻¹ ∈ S} := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hdet : ∀ k, (hA.eigenvalues k : ℂ) ≠ 0 := by
    have h := (Matrix.isUnit_iff_isUnit_det A).mp hu
    rw [hA.det_eq_prod_eigenvalues] at h
    intro k
    exact (Finset.prod_ne_zero_iff.mp h.ne_zero) k (Finset.mem_univ k)
  have hspec : A = U * Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ)) * Uᴴ := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hinv : A⁻¹ = U * Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ))⁻¹) * Uᴴ := by
    apply Matrix.inv_eq_right_inv
    calc A * (U * Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ))⁻¹) * Uᴴ)
        = (U * Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ)) * Uᴴ) *
          (U * Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ))⁻¹) * Uᴴ) := by
            rw [← hspec]
      _ = U * (Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ)) * (Uᴴ * U) *
          Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ))⁻¹)) * Uᴴ := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hU1, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
        have : (fun k => (hA.eigenvalues k : ℂ) * ((hA.eigenvalues k : ℂ))⁻¹) = fun _ => 1 := by
          funext k; exact mul_inv_cancel₀ (hdet k)
        rw [this, Matrix.diagonal_one, Matrix.mul_one, hU2]
  have hcp : A⁻¹.charpoly =
      ∏ k, (Polynomial.X - Polynomial.C (((hA.eigenvalues k)⁻¹ : ℝ) : ℂ)) := by
    rw [hinv, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul,
      Matrix.charpoly_diagonal]
    simp
  have hroots : A⁻¹.charpoly.roots =
      Multiset.map (fun k => (((hA.eigenvalues k)⁻¹ : ℝ) : ℂ)) Finset.univ.val := by
    rw [hcp, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  rw [countIn_eq_card_roots hA.inv, hroots, Multiset.filter_map]
  simp [countIn, hA, Finset.card_def, Finset.filter_val]

/-- The rank of a spectral projection: `rank 1_S(A) = #{k : λ_k ∈ S}`. -/
theorem rank_specProj {A : Matrix n n ℂ} (hA : A.IsHermitian) (S : Set ℝ) :
    (specProj A S).rank = countIn A S := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have key : ∀ S : Set ℝ, specProj A S =
      U * Matrix.diagonal (fun k => if hA.eigenvalues k ∈ S then (1 : ℂ) else 0) * Uᴴ := by
    intro S
    simp only [specProj, hA, ↓reduceDIte]
    ext i j
    rw [Finset.sum_filter, Matrix.sum_apply]
    simp only [hUdef, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : hA.eigenvalues c ∈ S <;> simp [h, Matrix.vecMulVec_apply, mul_comm]
  have hdU : IsUnit (U.det) := by
    have : IsUnit U := ⟨⟨U, Uᴴ, hU2, hU1⟩, rfl⟩
    exact (Matrix.isUnit_iff_isUnit_det U).mp this
  have hdUh : IsUnit (Uᴴ.det) := by
    have : IsUnit Uᴴ := ⟨⟨Uᴴ, U, hU1, hU2⟩, rfl⟩
    exact (Matrix.isUnit_iff_isUnit_det Uᴴ).mp this
  rw [key S, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdUh,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdU, Matrix.rank_diagonal]
  simp only [countIn, hA, ↓reduceDIte]
  rw [Fintype.card_subtype]
  congr 1
  ext k
  by_cases h : hA.eigenvalues k ∈ S <;> simp [h]

/-- `1_S(A) 1_T(A) = 1_S(A)` for `S ⊆ T`. -/
theorem specProj_mul_of_subset {A : Matrix n n ℂ} (hA : A.IsHermitian) {S T : Set ℝ}
    (hST : S ⊆ T) : specProj A S * specProj A T = specProj A S := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have key : ∀ S : Set ℝ, specProj A S =
      U * Matrix.diagonal (fun k => if hA.eigenvalues k ∈ S then (1 : ℂ) else 0) * Uᴴ := by
    intro S
    simp only [specProj, hA, ↓reduceDIte]
    ext i j
    rw [Finset.sum_filter, Matrix.sum_apply]
    simp only [hUdef, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : hA.eigenvalues c ∈ S <;> simp [h, Matrix.vecMulVec_apply, mul_comm]
  have hD : Matrix.diagonal (fun k => if hA.eigenvalues k ∈ S then (1 : ℂ) else 0) *
      Matrix.diagonal (fun k => if hA.eigenvalues k ∈ T then (1 : ℂ) else 0) =
      Matrix.diagonal (fun k => if hA.eigenvalues k ∈ S then (1 : ℂ) else 0) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    by_cases hS : hA.eigenvalues k ∈ S
    · have hT := hST hS
      simp [hS, hT]
    · simp [hS]
  rw [key S, key T]
  calc _ = U * (Matrix.diagonal (fun k => if hA.eigenvalues k ∈ S then (1 : ℂ) else 0) *
        (Uᴴ * U) *
        Matrix.diagonal (fun k => if hA.eigenvalues k ∈ T then (1 : ℂ) else 0)) * Uᴴ := by
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU1, Matrix.mul_one, hD]

end LSBA
