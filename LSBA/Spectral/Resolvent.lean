import Mathlib

/-!
# Resolvents of Hermitian matrices

The resolvent `G(z) = (A - z)^{-1}` of Section 1.1 [sec:model], its spectral representation, and
Ward's
identity, for any Hermitian matrix on any finite index type.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The resolvent `G(z) = (A - z)^{-1}`. -/
def resolventMat (A : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ := (A - z • (1 : Matrix n n ℂ))⁻¹

/-- `A - z` is diagonalized by the unitary of eigenvectors, with diagonal `λ_k - z`. -/
private lemma sub_smul_one_eq_unitary_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : ℂ) :
    A - z • (1 : Matrix n n ℂ) =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ) - z) *
        (star (hA.eigenvectorUnitary : Matrix n n ℂ)) := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  have hU : (hA.eigenvectorUnitary : Matrix n n ℂ) * (star (hA.eigenvectorUnitary : Matrix n n ℂ))
      = 1 := Unitary.coe_mul_star_self _
  have hD : Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ) - z) =
      Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) - z • (1 : Matrix n n ℂ) := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
    rfl
  rw [hD, Matrix.mul_sub, Matrix.sub_mul, ← h]
  congr 1
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

/-- The candidate inverse of `A - z` built from the spectral decomposition. -/
private lemma sub_smul_one_mul_spectral {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    (A - z • (1 : Matrix n n ℂ)) *
      ((hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ) - z)⁻¹) *
        (star (hA.eigenvectorUnitary : Matrix n n ℂ))) = 1 := by
  have hU : (hA.eigenvectorUnitary : Matrix n n ℂ) * (star (hA.eigenvectorUnitary : Matrix n n ℂ))
      = 1 := Unitary.coe_mul_star_self _
  have hU' : (star (hA.eigenvectorUnitary : Matrix n n ℂ)) * (hA.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_star_mul_self _
  have hne : ∀ k, (hA.eigenvalues k : ℂ) - z ≠ 0 := by
    intro k h
    apply hz
    have := congrArg Complex.im h
    simpa using this.symm
  rw [sub_smul_one_eq_unitary_mul hA z]
  calc _ = (hA.eigenvectorUnitary : Matrix n n ℂ) *
          (Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ) - z) *
            Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ) - z)⁻¹)) *
          (star (hA.eigenvectorUnitary : Matrix n n ℂ)) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (star (hA.eigenvectorUnitary : Matrix n n ℂ)), hU', Matrix.one_mul]
    _ = 1 := by
        rw [Matrix.diagonal_mul_diagonal]
        have : (fun k => ((hA.eigenvalues k : ℂ) - z) * ((hA.eigenvalues k : ℂ) - z)⁻¹) =
            fun _ => (1 : ℂ) := by
          funext k
          exact mul_inv_cancel₀ (hne k)
        rw [this, Matrix.diagonal_one, Matrix.mul_one, hU]

/-- The resolvent equals the spectral expression. -/
private lemma resolventMat_eq_unitary_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    resolventMat A z =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ) - z)⁻¹) *
        (star (hA.eigenvectorUnitary : Matrix n n ℂ)) :=
  Matrix.inv_eq_right_inv (sub_smul_one_mul_spectral hA hz)

theorem sub_smul_mul_resolventMat {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) : (A - z • (1 : Matrix n n ℂ)) * resolventMat A z = 1 := by
  rw [resolventMat_eq_unitary_mul hA hz]
  exact sub_smul_one_mul_spectral hA hz

theorem resolventMat_apply {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (x y : n) :
    resolventMat A z x y = ∑ k, hA.eigenvectorBasis k x * star (hA.eigenvectorBasis k y) /
      ((hA.eigenvalues k : ℂ) - z) := by
  rw [resolventMat_eq_unitary_mul hA hz]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.star_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, div_eq_mul_inv]
  ring

/-- Both products `G* G` and `G G*` equal `(G - G*) / (2 i Im z)`. -/
private lemma conjTranspose_mul_self_and_self_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    (resolventMat A z)ᴴ * resolventMat A z =
        ((2 * z.im * Complex.I)⁻¹ : ℂ) • (resolventMat A z - (resolventMat A z)ᴴ) ∧
      resolventMat A z * (resolventMat A z)ᴴ =
        ((2 * z.im * Complex.I)⁻¹ : ℂ) • (resolventMat A z - (resolventMat A z)ᴴ) := by
  have hMG := sub_smul_mul_resolventMat hA hz
  have hGM := mul_eq_one_comm.mp hMG
  have h1 : (resolventMat A z)ᴴ * (A - z • (1 : Matrix n n ℂ))ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hMG, Matrix.conjTranspose_one]
  have h2 : (A - z • (1 : Matrix n n ℂ))ᴴ * (resolventMat A z)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hGM, Matrix.conjTranspose_one]
  have hdiff : (A - z • (1 : Matrix n n ℂ))ᴴ - (A - z • (1 : Matrix n n ℂ)) =
      (2 * z.im * Complex.I : ℂ) • (1 : Matrix n n ℂ) := by
    have hz2 : (2 * (z.im : ℂ) * Complex.I) = z - star z := by
      apply Complex.ext <;> simp [two_mul]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hA.eq,
      hz2, sub_smul]
    abel
  have hc : (2 * z.im * Complex.I : ℂ) ≠ 0 := by
    simp [hz]
  have e1 : (2 * z.im * Complex.I : ℂ) • ((resolventMat A z)ᴴ * resolventMat A z) =
      resolventMat A z - (resolventMat A z)ᴴ := by
    calc (2 * z.im * Complex.I : ℂ) • ((resolventMat A z)ᴴ * resolventMat A z)
        = (resolventMat A z)ᴴ * ((2 * z.im * Complex.I : ℂ) • (1 : Matrix n n ℂ)) *
            resolventMat A z := by
          rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = (resolventMat A z)ᴴ * ((A - z • (1 : Matrix n n ℂ))ᴴ - (A - z • (1 : Matrix n n ℂ))) *
            resolventMat A z := by rw [hdiff]
      _ = ((resolventMat A z)ᴴ * (A - z • (1 : Matrix n n ℂ))ᴴ) * resolventMat A z -
            (resolventMat A z)ᴴ * ((A - z • (1 : Matrix n n ℂ)) * resolventMat A z) := by
          rw [Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_assoc (resolventMat A z)ᴴ (A - z • (1 : Matrix n n ℂ))]
      _ = resolventMat A z - (resolventMat A z)ᴴ := by
          rw [h1, hMG, Matrix.one_mul, Matrix.mul_one]
  have e2 : (2 * z.im * Complex.I : ℂ) • (resolventMat A z * (resolventMat A z)ᴴ) =
      resolventMat A z - (resolventMat A z)ᴴ := by
    calc (2 * z.im * Complex.I : ℂ) • (resolventMat A z * (resolventMat A z)ᴴ)
        = resolventMat A z * ((2 * z.im * Complex.I : ℂ) • (1 : Matrix n n ℂ)) *
            (resolventMat A z)ᴴ := by
          rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = resolventMat A z * ((A - z • (1 : Matrix n n ℂ))ᴴ - (A - z • (1 : Matrix n n ℂ))) *
            (resolventMat A z)ᴴ := by rw [hdiff]
      _ = resolventMat A z * ((A - z • (1 : Matrix n n ℂ))ᴴ * (resolventMat A z)ᴴ) -
            (resolventMat A z * (A - z • (1 : Matrix n n ℂ))) * (resolventMat A z)ᴴ := by
          rw [Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_assoc (resolventMat A z) (A - z • (1 : Matrix n n ℂ))ᴴ]
      _ = resolventMat A z - (resolventMat A z)ᴴ := by
          rw [h2, hGM, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · rw [← e1, inv_smul_smul₀ hc]
  · rw [← e2, inv_smul_smul₀ hc]

theorem im_resolventMat_diag {A : Matrix n n ℂ} (hA : A.IsHermitian) (E : ℝ) {η : ℝ}
    (hη : η ≠ 0) (x : n) :
    (resolventMat A (E + η * Complex.I) x x).im =
      ∑ k, η * ‖hA.eigenvectorBasis k x‖ ^ 2 / ((hA.eigenvalues k - E) ^ 2 + η ^ 2) := by
  rw [resolventMat_apply hA (by simpa using hη), Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hmul : hA.eigenvectorBasis k x * star (hA.eigenvectorBasis k x) =
      ((‖hA.eigenvectorBasis k x‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  have hpos : ((hA.eigenvalues k - E) ^ 2 + η ^ 2) ≠ 0 := by positivity
  rw [hmul, div_eq_mul_inv, Complex.im_ofReal_mul, Complex.inv_im, Complex.normSq_apply]
  simp
  field_simp

/-- Ward's identity `Σ_y |G_xy|² = Im G_xx / η`. -/
theorem ward {A : Matrix n n ℂ} (hA : A.IsHermitian) (E : ℝ) {η : ℝ} (hη : η ≠ 0) (x : n) :
    ∑ y, ‖resolventMat A (E + η * Complex.I) x y‖ ^ 2 =
      (resolventMat A (E + η * Complex.I) x x).im / η := by
  have hz : (E + η * Complex.I).im ≠ 0 := by simpa using hη
  have hx := congrFun (congrFun (conjTranspose_mul_self_and_self_mul hA hz).2 x) x
  rw [Matrix.mul_apply] at hx
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply] at hx
  have e : ∑ y, resolventMat A (E + η * Complex.I) x y *
        star (resolventMat A (E + η * Complex.I) x y)
      = ((∑ y, ‖resolventMat A (E + η * Complex.I) x y‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [mul_comm, Complex.star_def, Complex.conj_mul']
  rw [e, smul_eq_mul] at hx
  have him : (E + η * Complex.I).im = η := by simp
  have hw : ∀ w : ℂ, w - star w = ((2 * w.im : ℝ) : ℂ) * Complex.I := fun w => by
    apply Complex.ext <;> simp [two_mul]
  rw [hw, him] at hx
  apply Complex.ofReal_injective
  rw [hx]
  push_cast
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  field_simp

/-- Matrix Ward identity `G* G = (G - G*) / (2 i η)`. -/
theorem ward_matrix {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (resolventMat A z)ᴴ * resolventMat A z =
      ((2 * z.im * Complex.I)⁻¹ : ℂ) • (resolventMat A z - (resolventMat A z)ᴴ) :=
  (conjTranspose_mul_self_and_self_mul hA hz).1

end LSBA
