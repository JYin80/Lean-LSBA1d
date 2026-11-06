import LSBA.Gauss.GUE
import LSBA.Upper.CoercivityMap

/-!
# Block matrices, the real Hilbert–Schmidt product and Hermitian completeness

Two-by-two block matrices `[[A, B], [C, D]]` on `Fin 2 × n` and their blocks; the real
Hilbert–Schmidt inner product `⟨A, B⟩ = Re Tr(A* B)`; the real coordinates
`(Re A_{ab}, Im A_{ab})` of a complex matrix, orthonormal for this product; and the
completeness relations (10.19) [eq:c-completeness] of the trace-orthonormal Hermitian basis
`H_α`: `Σ_α H_α² = W I` and `Σ_α ‖A H_α B‖² = ‖A‖² ‖B‖²` (Hilbert–Schmidt norms), with the
Parseval bound `Σ_α ⟨H_α, A⟩² ≤ ‖A‖²`, an equality with `A = Σ_α ⟨H_α, A⟩ H_α` for Hermitian
`A` (Section 10 [sec:compact-proof]).
-/

open Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The block matrix `[[A, B], [C, D]]` on `Fin 2 × n`. -/
def blockMat {n : Type*} (A B C D : Matrix n n ℂ) : Matrix (Fin 2 × n) (Fin 2 × n) ℂ :=
  Matrix.of fun p r => (![![A, B], ![C, D]] p.1 r.1) p.2 r.2

/-- The block `(a, b)` of a matrix on `Fin 2 × n`. -/
def blockPart {n : Type*} (Z : Matrix (Fin 2 × n) (Fin 2 × n) ℂ) (a b : Fin 2) : Matrix n n ℂ :=
  Matrix.of fun α β => Z (a, α) (b, β)

/-- The real Hilbert–Schmidt inner product `⟨A, B⟩ = Re Tr(A* B)`. -/
def hsInner {k l : Type*} [Fintype k] [Fintype l] (A B : Matrix k l ℂ) : ℝ :=
  ∑ a, ∑ b, (star (A a b) * B a b).re

/-- The real coordinates `(Re A_{ab}, Im A_{ab})` of a complex matrix. -/
def reCoord {k l : Type*} (A : Matrix k l ℂ) : Fin 2 × k × l → ℝ :=
  fun p => if p.1 = 0 then (A p.2.1 p.2.2).re else (A p.2.1 p.2.2).im

/-- The complex matrix with real coordinates `x`. -/
def ofReCoord {k l : Type*} (x : Fin 2 × k × l → ℝ) : Matrix k l ℂ :=
  Matrix.of fun a b => ⟨x (0, a, b), x (1, a, b)⟩

/-- A matrix on `Fin 2 × n` is the block matrix of its four blocks, and the blocks of
`[[A, B], [C, D]]` are `A, B, C, D`. -/
theorem blockMat_blockPart {n : Type*} (Z : Matrix (Fin 2 × n) (Fin 2 × n) ℂ)
    (A B C D : Matrix n n ℂ) :
    blockMat (blockPart Z 0 0) (blockPart Z 0 1) (blockPart Z 1 0) (blockPart Z 1 1) = Z ∧
      blockPart (blockMat A B C D) 0 0 = A ∧ blockPart (blockMat A B C D) 0 1 = B ∧
      blockPart (blockMat A B C D) 1 0 = C ∧ blockPart (blockMat A B C D) 1 1 = D := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext ⟨a, α⟩ ⟨b, β⟩
    fin_cases a <;> fin_cases b <;> rfl
  · ext α β; rfl
  · ext α β; rfl
  · ext α β; rfl
  · ext α β; rfl

/-- Products, adjoints, traces and Hilbert–Schmidt norms of block matrices. -/
theorem blockMat_algebra {n : Type*} [Fintype n] (A B C D A' B' C' D' : Matrix n n ℂ) :
    blockMat A B C D * blockMat A' B' C' D' =
        blockMat (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') ∧
      (blockMat A B C D)ᴴ = blockMat Aᴴ Cᴴ Bᴴ Dᴴ ∧
      (blockMat A B C D).trace = A.trace + D.trace ∧
      hsSq (blockMat A B C D) = hsSq A + hsSq B + hsSq C + hsSq D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext ⟨a, α⟩ ⟨b, β⟩
    fin_cases a <;> fin_cases b <;>
      simp [blockMat, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  · ext ⟨a, α⟩ ⟨b, β⟩
    fin_cases a <;> fin_cases b <;> simp [blockMat, Matrix.conjTranspose_apply]
  · simp [Matrix.trace, blockMat, Fintype.sum_prod_type, Fin.sum_univ_two]
  · simp only [hsSq, blockMat, Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Finset.sum_add_distrib]
    ring

/-- `⟨A, B⟩ = Re Tr(A* B)` and `⟨A, A⟩ = ‖A‖²`; the coordinates `reCoord` are inverse to
`ofReCoord` and orthonormal: `Σ_p (reCoord A)_p (reCoord B)_p = ⟨A, B⟩`. -/
theorem hsInner_reCoord {k l : Type*} [Fintype k] [Fintype l] (A B : Matrix k l ℂ)
    (x : Fin 2 × k × l → ℝ) :
    hsInner A B = (Aᴴ * B).trace.re ∧ hsInner A A = hsSq A ∧ ofReCoord (reCoord A) = A ∧
      reCoord (ofReCoord x) = x ∧ ∑ p, reCoord A p * reCoord B p = hsInner A B := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.re_sum]
    exact Finset.sum_comm
  · unfold hsInner hsSq
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  · ext a b
    simp [ofReCoord, reCoord]
  · funext ⟨i, a, b⟩
    fin_cases i <;> simp [reCoord, ofReCoord]
  · simp only [Fintype.sum_prod_type, Fin.sum_univ_two, reCoord, hsInner]
    simp only [ite_true, Fin.one_eq_zero_iff]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [Complex.mul_re]

/-- (10.19) [eq:c-completeness]: `Σ_α H_α² = W I` and `Σ_α ‖A H_α B‖² = ‖A‖² ‖B‖²` for the
trace-orthonormal Hermitian basis; with `A = I` or `B = I` this is
`Σ_α ‖H_α B‖² = Σ_α ‖B H_α‖² = W ‖B‖²`. -/
theorem hermBasis_completeness (W : ℕ) (A B : Matrix (Fin W) (Fin W) ℂ) :
    ∑ k, hermBasis W k * hermBasis W k = (W : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) ∧
      ∑ k, hsSq (A * hermBasis W k * B) = hsSq A * hsSq B := by
  have htr : ∀ M : Matrix (Fin W) (Fin W) ℂ, (Mᴴ * M).trace = (hsSq M : ℂ) := by
    intro M
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      hsSq]
    rw [Finset.sum_comm]
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  refine ⟨?_, ?_⟩
  · have h := sum_hermBasis_mul_mul W 1
    simpa using h
  · apply Complex.ofReal_injective
    have h1 : ∀ k : Fin W × Fin W, ((hsSq (A * hermBasis W k * B) : ℝ) : ℂ) =
        (Bᴴ * (hermBasis W k * (Aᴴ * A) * hermBasis W k) * B).trace := by
      intro k
      rw [← htr]
      simp only [Matrix.conjTranspose_mul, (hermBasis_isHermitian W k).eq, Matrix.mul_assoc]
    push_cast
    simp only [h1]
    have h2 : ∑ k : Fin W × Fin W, Bᴴ * (hermBasis W k * (Aᴴ * A) * hermBasis W k) * B =
        Bᴴ * ((Aᴴ * A).trace • (1 : Matrix (Fin W) (Fin W) ℂ)) * B := by
      rw [← sum_hermBasis_mul_mul, Finset.mul_sum, Finset.sum_mul]
    rw [← Matrix.trace_sum, h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.trace_smul, htr, htr, smul_eq_mul]

/-- Parseval for the Hermitian basis: `Σ_α ⟨H_α, A⟩² ≤ ‖A‖²`, and `A = Σ_α ⟨H_α, A⟩ H_α` for
Hermitian `A`. -/
theorem hermBasis_parseval (W : ℕ) (A : Matrix (Fin W) (Fin W) ℂ) :
    ∑ k, hsInner (hermBasis W k) A ^ 2 ≤ hsSq A ∧
      (A.IsHermitian → A = ∑ k, ((hsInner (hermBasis W k) A : ℝ) : ℂ) • hermBasis W k) := by
  refine ⟨?_, ?_⟩
  · have hinner : ∀ M N : Matrix (Fin W) (Fin W) ℂ,
        inner ℝ (WithLp.toLp 2 (reCoord M) : EuclideanSpace ℝ (Fin 2 × Fin W × Fin W))
          (WithLp.toLp 2 (reCoord N)) = hsInner M N := by
      intro M N
      rw [← (hsInner_reCoord M N 0).2.2.2.2]
      simp [PiLp.inner_apply, mul_comm]
    have hon : Orthonormal ℝ (fun k : Fin W × Fin W =>
        (WithLp.toLp 2 (reCoord (hermBasis W k)) : EuclideanSpace ℝ (Fin 2 × Fin W × Fin W))) := by
      rw [orthonormal_iff_ite]
      intro k l
      rw [hinner, (hsInner_reCoord _ _ 0).1, (hermBasis_isHermitian W k).eq, trace_hermBasis_mul]
      split_ifs <;> simp
    have h := hon.sum_inner_products_le (s := Finset.univ)
      (WithLp.toLp 2 (reCoord A) : EuclideanSpace ℝ (Fin 2 × Fin W × Fin W))
    rw [← real_inner_self_eq_norm_sq, hinner, (hsInner_reCoord A A 0).2.1] at h
    simpa [hinner, Real.norm_eq_abs, sq_abs] using h
  · intro hA
    have hreal : ∀ k, ((hsInner (hermBasis W k) A : ℝ) : ℂ) = (hermBasis W k * A).trace := by
      intro k
      rw [(hsInner_reCoord _ _ 0).1, (hermBasis_isHermitian W k).eq]
      apply Complex.ext
      · simp
      · have h1 : star ((hermBasis W k * A).trace) = (hermBasis W k * A).trace := by
          rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq,
            (hermBasis_isHermitian W k).eq, Matrix.trace_mul_comm]
        have h2 := Complex.conj_eq_iff_im.mp h1
        simp [h2]
    ext i m
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, hreal, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply]
    have h3 : ∀ k : Fin W × Fin W, (∑ j, ∑ l, hermBasis W k j l * A l j) * hermBasis W k i m =
        ∑ j, ∑ l, A l j * (hermBasis W k j l * hermBasis W k i m) := by
      intro k
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    simp only [h3]
    rw [Finset.sum_comm]
    have h4 : ∀ j : Fin W,
        ∑ k : Fin W × Fin W, ∑ l, A l j * (hermBasis W k j l * hermBasis W k i m) =
          ∑ l, A l j * (if j = m ∧ l = i then 1 else 0) := by
      intro j
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.mul_sum, sum_hermBasis_apply_mul_apply]
    simp only [h4]
    simp [ite_and]

end LSBA
