import LSBA.Analysis.ComplexMatrix
import LSBA.Transfer.IsoGroup

/-!
# The Lie algebra of 𝒢 in two coordinate systems

The Lie algebra `𝔤 = {M : M* J + J M = 0, Tr M = 0}` of (10.1) [up:eq:lie-algebra] for
`J = diag(I, -I)`, and the same algebra in the original transfer coordinates,
`{M : M* J_ph + J_ph M = 0, Tr M = 0}` with `J_ph = [[0, -iI], [iI, 0]]` and `S* J_ph S = J`
for `S = S_0`: its block form (10.3) [eq:c-Lie], the passage `M ↦ S* M S`, which preserves
Hilbert–Schmidt norms and Hermitian matrices, and the invariance under `Z ↦ Q^{-*} Z Q*` and
`Z ↦ Q⁻¹ Z Q` for `Q* J_ph Q = J_ph` (the step `Z_i ∈ 𝔤` of (G.18) [eq:c-observe]).
-/

open Real Finset
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The Lie algebra `𝔤 = {M : M* J + J M = 0, Tr M = 0}` of (10.1) [up:eq:lie-algebra]. -/
def lieJ (W : ℕ) : Set (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :=
  {M | Mᴴ * isoJ W + isoJ W * M = 0 ∧ M.trace = 0}

/-- The algebra of (10.3) [eq:c-Lie] in the original transfer coordinates:
`M* J_ph + J_ph M = 0` and `Tr M = 0`, that is `S* M S ∈ 𝔤` for `S = S_0`. -/
def lieOmega (W : ℕ) : Set (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :=
  {M | Mᴴ * phJ W + phJ W * M = 0 ∧ M.trace = 0}

/-- (10.3) [eq:c-Lie]: `[[A, B₁], [B₂, D]]` lies in the algebra iff `B₁, B₂` are Hermitian,
`D = -A*` and `Im Tr A = 0`. -/
theorem mem_lieOmega_iff {W : ℕ} (A B₁ B₂ D : Matrix (Fin W) (Fin W) ℂ) :
    blockMat A B₁ B₂ D ∈ lieOmega W ↔
      B₁.IsHermitian ∧ B₂.IsHermitian ∧ D = -Aᴴ ∧ A.trace.im = 0 := by
  have hadd : ∀ (A B C D A' B' C' D' : Matrix (Fin W) (Fin W) ℂ),
      blockMat A B C D + blockMat A' B' C' D' = blockMat (A + A') (B + B') (C + C') (D + D') := by
    intro A B C D A' B' C' D'
    ext ⟨a, α⟩ ⟨b, β⟩
    fin_cases a <;> fin_cases b <;> rfl
  have hzero : ∀ (A B C D : Matrix (Fin W) (Fin W) ℂ),
      blockMat A B C D = 0 ↔ A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
    intro A B C D
    have h0 : (0 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) =
        blockMat (0 : Matrix (Fin W) (Fin W) ℂ) 0 0 0 := by
      ext ⟨a, α⟩ ⟨b, β⟩
      fin_cases a <;> fin_cases b <;> rfl
    constructor
    · intro h
      have := congrArg (fun Z => (blockPart Z 0 0, blockPart Z 0 1, blockPart Z 1 0,
        blockPart Z 1 1)) h
      obtain ⟨-, e1, e2, e3, e4⟩ := blockMat_blockPart
        (0 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) A B C D
      obtain ⟨-, f1, f2, f3, f4⟩ := blockMat_blockPart
        (0 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) 0 0 0 0
      simp only [e1, e2, e3, e4, Prod.mk.injEq] at this
      rw [h0] at this
      simp only [f1, f2, f3, f4] at this
      exact this
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      exact h0.symm
  have hph : phJ W = blockMat 0 (-(Complex.I • (1 : Matrix (Fin W) (Fin W) ℂ)))
      (Complex.I • 1) 0 := by
    ext ⟨a, α⟩ ⟨b, β⟩
    fin_cases a <;> fin_cases b <;>
      simp [phJ, blockMat, Matrix.kroneckerMap_apply, Matrix.one_apply]
    split_ifs <;> simp
  obtain ⟨-, hct, htr, -⟩ := blockMat_algebra A B₁ B₂ D 0 0 0 0
  simp only [lieOmega, Set.mem_ofPred_eq]
  rw [hct, htr, hph,
    (blockMat_algebra Aᴴ B₂ᴴ B₁ᴴ Dᴴ 0 (-(Complex.I • (1 : Matrix (Fin W) (Fin W) ℂ)))
      (Complex.I • 1) 0).1,
    (blockMat_algebra 0 (-(Complex.I • (1 : Matrix (Fin W) (Fin W) ℂ))) (Complex.I • 1) 0
      A B₁ B₂ D).1, hadd, hzero]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have hI : ∀ X Y : Matrix (Fin W) (Fin W) ℂ,
      Complex.I • X + -(Complex.I • Y) = 0 ↔ X = Y := by
    intro X Y
    rw [← smul_neg, ← smul_add, smul_eq_zero]
    simp [Complex.I_ne_zero, add_neg_eq_zero]
  have hI' : ∀ X Y : Matrix (Fin W) (Fin W) ℂ,
      -(Complex.I • X) + -(Complex.I • Y) = 0 ↔ Y = -X := by
    intro X Y
    rw [← smul_neg, ← smul_neg, ← smul_add, smul_eq_zero]
    simp only [Complex.I_ne_zero, false_or, ← neg_add, neg_eq_zero]
    rw [add_comm, add_eq_zero_iff_eq_neg]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, ht⟩
    have hB2 : B₂ᴴ = B₂ := (hI _ _).1 h1
    have hB1 : B₁ᴴ = B₁ := by
      exact ((hI _ _).1 (by rw [add_comm]; exact h4)).symm
    have hD : D = -Aᴴ := (hI' _ _).1 h2
    refine ⟨hB1, hB2, hD, ?_⟩
    have := congrArg Complex.im ht
    rw [hD, Matrix.trace_neg, Matrix.trace_conjTranspose] at this
    simpa using this
  · rintro ⟨hB1, hB2, hD, him⟩
    refine ⟨⟨(hI _ _).2 hB2, (hI' _ _).2 hD, ?_, ?_⟩, ?_⟩
    · subst hD
      simp
    · rw [add_comm]; exact (hI _ _).2 (hB1 : B₁ᴴ = B₁).symm
    · rw [hD, Matrix.trace_neg, Matrix.trace_conjTranspose]
      apply Complex.ext <;> simp [him]

/-- `S* M S ∈ 𝔤` iff `M` lies in the algebra (10.3) [eq:c-Lie], for `S = S_0`; conjugation by
`S` preserves Hilbert–Schmidt norms and Hermitian matrices. -/
theorem conj_freeConj_lie {W : ℕ} (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ((freeConj W 0)ᴴ * M * freeConj W 0 ∈ lieJ W ↔ M ∈ lieOmega W) ∧
      hsSq ((freeConj W 0)ᴴ * M * freeConj W 0) = hsSq M ∧
      (((freeConj W 0)ᴴ * M * freeConj W 0).IsHermitian ↔ M.IsHermitian) ∧
      freeConj W 0 * ((freeConj W 0)ᴴ * M * freeConj W 0) * (freeConj W 0)ᴴ = M := by
  have hSS : (freeConj W 0)ᴴ * freeConj W 0 = 1 := by
    have h := freeConj_zero_mem_unitaryGroup W
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  have hSS' : freeConj W 0 * (freeConj W 0)ᴴ = 1 := by
    have h := freeConj_zero_mem_unitaryGroup W
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have hJ := conjTranspose_freeConj_mul_phJ_mul W
  generalize freeConj W 0 = S at hSS hSS' hJ ⊢
  have hback : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, S * (Sᴴ * X * S) * Sᴴ = X := by
    intro X
    calc S * (Sᴴ * X * S) * Sᴴ = (S * Sᴴ) * X * (S * Sᴴ) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hSS', Matrix.one_mul, Matrix.mul_one]
  have hinj : ∀ X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      Sᴴ * X * S = Sᴴ * Y * S → X = Y := by
    intro X Y h
    rw [← hback X, ← hback Y, h]
  have hzero : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Sᴴ * X * S = 0 ↔ X = 0 := by
    intro X
    constructor
    · intro h
      exact hinj X 0 (by rw [h]; simp)
    · rintro rfl
      simp
  have hct : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, (Sᴴ * X * S)ᴴ = Sᴴ * Xᴴ * S := by
    intro X
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hkey : (Sᴴ * M * S)ᴴ * isoJ W + isoJ W * (Sᴴ * M * S) =
      Sᴴ * (Mᴴ * phJ W + phJ W * M) * S := by
    rw [hct, ← hJ]
    have e1 : Sᴴ * Mᴴ * S * (Sᴴ * phJ W * S) = Sᴴ * (Mᴴ * phJ W) * S := by
      calc Sᴴ * Mᴴ * S * (Sᴴ * phJ W * S) = Sᴴ * Mᴴ * (S * Sᴴ) * phJ W * S := by
            simp only [Matrix.mul_assoc]
        _ = Sᴴ * (Mᴴ * phJ W) * S := by rw [hSS', Matrix.mul_one]; simp only [Matrix.mul_assoc]
    have e2 : Sᴴ * phJ W * S * (Sᴴ * M * S) = Sᴴ * (phJ W * M) * S := by
      calc Sᴴ * phJ W * S * (Sᴴ * M * S) = Sᴴ * phJ W * (S * Sᴴ) * M * S := by
            simp only [Matrix.mul_assoc]
        _ = Sᴴ * (phJ W * M) * S := by rw [hSS', Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [e1, e2, Matrix.mul_add, Matrix.add_mul]
  have htr : (Sᴴ * M * S).trace = M.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hSS', Matrix.one_mul]
  have hhs : ∀ A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, hsSq A = (Aᴴ * A).trace.re := by
    intro A
    simp only [hsSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  refine ⟨?_, ?_, ?_, hback M⟩
  · simp only [lieJ, lieOmega, Set.mem_ofPred_eq]
    rw [hkey, htr, hzero]
  · rw [hhs, hhs, hct, show Sᴴ * Mᴴ * S * (Sᴴ * M * S) = Sᴴ * (Mᴴ * M) * S by
      calc Sᴴ * Mᴴ * S * (Sᴴ * M * S) = Sᴴ * Mᴴ * (S * Sᴴ) * M * S := by
            simp only [Matrix.mul_assoc]
        _ = Sᴴ * (Mᴴ * M) * S := by rw [hSS', Matrix.mul_one]; simp only [Matrix.mul_assoc]]
    congr 1
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hSS', Matrix.one_mul]
  · change (Sᴴ * M * S)ᴴ = Sᴴ * M * S ↔ Mᴴ = M
    rw [hct]
    exact ⟨hinj _ _, fun h => by rw [h]⟩

/-- The step `Z_i ∈ 𝔤` of (G.18) [eq:c-observe]: for `Q* J_ph Q = J_ph`, the maps
`Z ↦ Q^{-*} Z Q*` and `Z ↦ Q⁻¹ Z Q` preserve the algebra (10.3) [eq:c-Lie]. -/
theorem conj_mem_lieOmega {W : ℕ} {Q Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hQ : Qᴴ * phJ W * Q = phJ W) (hZ : Z ∈ lieOmega W) :
    (Q⁻¹)ᴴ * Z * Qᴴ ∈ lieOmega W ∧ Q⁻¹ * Z * Q ∈ lieOmega W := by
  have hJJ : phJ W * phJ W = 1 := by
    unfold phJ
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
    have : (!![0, -Complex.I; Complex.I, 0] * !![0, -Complex.I; Complex.I, 0] :
        Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [this, Matrix.one_kronecker_one]
  have hJh : (phJ W)ᴴ = phJ W := by
    unfold phJ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hmain : ∀ Q' : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Q'ᴴ * phJ W * Q' = phJ W →
      ∀ Z' ∈ lieOmega W, Q'⁻¹ * Z' * Q' ∈ lieOmega W := by
    intro Q' hQ' Z' hZ'
    have hL : phJ W * Q'ᴴ * phJ W * Q' = 1 := by
      calc phJ W * Q'ᴴ * phJ W * Q' = phJ W * (Q'ᴴ * phJ W * Q') := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hQ', hJJ]
    have hinv : Q'⁻¹ = phJ W * Q'ᴴ * phJ W := Matrix.inv_eq_left_inv hL
    have hR : Q' * (phJ W * Q'ᴴ * phJ W) = 1 := mul_eq_one_comm.mp hL
    obtain ⟨hZ1, hZ2⟩ := hZ'
    refine ⟨?_, ?_⟩
    · have e : (Q'⁻¹ * Z' * Q')ᴴ * phJ W + phJ W * (Q'⁻¹ * Z' * Q') =
          Q'ᴴ * (Z'ᴴ * phJ W + phJ W * Z') * Q' := by
        rw [hinv]
        have e1 : (phJ W * Q'ᴴ * phJ W * Z' * Q')ᴴ * phJ W = Q'ᴴ * (Z'ᴴ * phJ W) * Q' := by
          calc (phJ W * Q'ᴴ * phJ W * Z' * Q')ᴴ * phJ W
              = Q'ᴴ * Z'ᴴ * (phJ W * Q' * (phJ W * phJ W)) := by
                simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh,
                  Matrix.mul_assoc]
            _ = Q'ᴴ * (Z'ᴴ * phJ W) * Q' := by
                rw [hJJ, Matrix.mul_one]
                simp only [Matrix.mul_assoc]
        have e2 : phJ W * (phJ W * Q'ᴴ * phJ W * Z' * Q') = Q'ᴴ * (phJ W * Z') * Q' := by
          calc phJ W * (phJ W * Q'ᴴ * phJ W * Z' * Q')
              = (phJ W * phJ W) * Q'ᴴ * phJ W * Z' * Q' := by simp only [Matrix.mul_assoc]
            _ = Q'ᴴ * (phJ W * Z') * Q' := by
                rw [hJJ, Matrix.one_mul]; simp only [Matrix.mul_assoc]
        rw [e1, e2, Matrix.mul_add, Matrix.add_mul]
      rw [e, hZ1, Matrix.mul_zero, Matrix.zero_mul]
    · have hQQ : Q' * Q'⁻¹ = 1 := by rw [hinv]; exact hR
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
      exact hZ2
  have hQJ : Q * phJ W * Qᴴ = phJ W := by
    have hL : phJ W * Qᴴ * phJ W * Q = 1 := by
      calc phJ W * Qᴴ * phJ W * Q = phJ W * (Qᴴ * phJ W * Q) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hQ, hJJ]
    have hR : Q * (phJ W * Qᴴ * phJ W) = 1 := mul_eq_one_comm.mp hL
    calc Q * phJ W * Qᴴ = Q * phJ W * Qᴴ * (phJ W * phJ W) := by rw [hJJ, Matrix.mul_one]
      _ = (Q * (phJ W * Qᴴ * phJ W)) * phJ W := by simp only [Matrix.mul_assoc]
      _ = phJ W := by rw [hR, Matrix.one_mul]
  refine ⟨?_, hmain Q hQ Z hZ⟩
  rw [Matrix.conjTranspose_nonsing_inv]
  exact hmain Qᴴ (by rw [Matrix.conjTranspose_conjTranspose]; exact hQJ) Z hZ

end LSBA
