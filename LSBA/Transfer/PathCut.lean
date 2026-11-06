import LSBA.Transfer.Path

/-!
# Cutting a block path

The induced endpoint shifts of a cut path and the Schur identities for the off-diagonal and the
two diagonal resolvent blocks of a path `Fin (p + q)` (proof of Proposition 8.2
[up:prop:fr-concentration],
Appendix E.2 [app:finite-volume-criterion]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The shift `-(g/max{1,g})² G^{L₀,0}(n-1, n-1)` that a path induces on the block to its
right (proof of Proposition 8.2 [up:prop:fr-concentration]); `0` for the empty path. -/
def shiftFromLeft (g : ℝ) {W n : ℕ} (V : Fin n → Matrix (Fin W) (Fin W) ℂ)
    (L₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  if h : 0 < n then
    -(((g / max 1 g) ^ 2 : ℝ) : ℂ) •
      blockOf (resolventMat (pathOp g V L₀ 0) E) ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩
  else 0

/-- The shift `-(g/max{1,g})² G^{0,R₀}(0, 0)` that a path induces on the block to its left. -/
def shiftFromRight (g : ℝ) {W n : ℕ} (V : Fin n → Matrix (Fin W) (Fin W) ℂ)
    (R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  if h : 0 < n then
    -(((g / max 1 g) ^ 2 : ℝ) : ℂ) • blockOf (resolventMat (pathOp g V 0 R₀) E) ⟨0, h⟩ ⟨0, h⟩
  else 0

section BlockInv

variable {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

/-- The top-left and top-right blocks of the inverse of a block matrix with invertible bottom-right
block `D` (proof of Proposition 8.2 [up:prop:fr-concentration]): `(A - B D⁻¹ C)⁻¹` and
`-(A - B D⁻¹ C)⁻¹ B D⁻¹`. The inverse is
the total inverse, `0` for a singular matrix. -/
private theorem pathCut_inv_fromBlocks₂₂ (A : Matrix J J ℂ) (B : Matrix J K ℂ)
    (C : Matrix K J ℂ) (D : Matrix K K ℂ) (hD : IsUnit D.det) :
    (Matrix.fromBlocks A B C D)⁻¹.toBlocks₁₁ = (A - B * D⁻¹ * C)⁻¹ ∧
    (Matrix.fromBlocks A B C D)⁻¹.toBlocks₁₂ = -((A - B * D⁻¹ * C)⁻¹ * B * D⁻¹) := by
  have : Invertible D := Matrix.invertibleOfIsUnitDet D hD
  have hdet : (Matrix.fromBlocks A B C D).det = D.det * (A - B * D⁻¹ * C).det := by
    rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  by_cases hS : IsUnit (A - B * D⁻¹ * C).det
  · have : Invertible (A - B * ⅟D * C) := by
      rw [Matrix.invOf_eq_nonsing_inv]
      exact Matrix.invertibleOfIsUnitDet _ hS
    have := Matrix.fromBlocks₂₂Invertible A B C D
    have h := Matrix.invOf_fromBlocks₂₂_eq A B C D
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.invOf_eq_nonsing_inv, Matrix.invOf_eq_nonsing_inv] at h
    rw [h]
    simp
  · have h0 : ¬ IsUnit (Matrix.fromBlocks A B C D).det := by
      rw [hdet]
      intro h
      exact hS (isUnit_of_mul_isUnit_right h)
    have h1 : (Matrix.fromBlocks A B C D)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ h0
    have h2 : (A - B * D⁻¹ * C)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hS
    rw [h1, h2]
    constructor <;> ext <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]

/-- The bottom-right block of the inverse of a block matrix with invertible top-left block `A`
(proof of Proposition 8.2 [up:prop:fr-concentration]): `(D - C A⁻¹ B)⁻¹`. -/
private theorem pathCut_inv_fromBlocks₁₁ (A : Matrix J J ℂ) (B : Matrix J K ℂ)
    (C : Matrix K J ℂ) (D : Matrix K K ℂ) (hA : IsUnit A.det) :
    (Matrix.fromBlocks A B C D)⁻¹.toBlocks₂₂ = (D - C * A⁻¹ * B)⁻¹ := by
  have : Invertible A := Matrix.invertibleOfIsUnitDet A hA
  have hdet : (Matrix.fromBlocks A B C D).det = A.det * (D - C * A⁻¹ * B).det := by
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  by_cases hS : IsUnit (D - C * A⁻¹ * B).det
  · have : Invertible (D - C * ⅟A * B) := by
      rw [Matrix.invOf_eq_nonsing_inv]
      exact Matrix.invertibleOfIsUnitDet _ hS
    have := Matrix.fromBlocks₁₁Invertible A B C D
    have h := Matrix.invOf_fromBlocks₁₁_eq A B C D
    simp only [Matrix.invOf_eq_nonsing_inv] at h
    rw [h]
    simp
  · have h0 : ¬ IsUnit (Matrix.fromBlocks A B C D).det := by
      rw [hdet]
      intro h
      exact hS (isUnit_of_mul_isUnit_right h)
    have h1 : (Matrix.fromBlocks A B C D)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ h0
    have h2 : (D - C * A⁻¹ * B)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hS
    rw [h1, h2]
    ext
    simp [Matrix.toBlocks₂₂]

end BlockInv

/-- Entries of the block path operator. -/
private theorem pathCut_pathOp_apply (g : ℝ) {W n : ℕ} (V : Fin n → Matrix (Fin W) (Fin W) ℂ)
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (a b : Fin n) (α β : Fin W) :
    pathOp g V L₀ R₀ (a, α) (b, β) =
      ((max 1 g : ℝ)⁻¹ : ℂ) * ((g : ℂ) * ((pathAdj n a b) * (if α = β then 1 else 0)) +
        (if a = b then V a α β else 0)) +
      (if a = b then ((if a.val = 0 then L₀ else 0) + (if a.val + 1 = n then R₀ else 0)) α β
        else 0) := by
  by_cases h1 : α = β <;> by_cases h2 : a = b <;>
    simp [pathOp, blockDiagOp, Matrix.kroneckerMap_apply, h1, h2, mul_add]

private def pathCutEquiv (W p q : ℕ) : (Fin p × Fin W) ⊕ (Fin q × Fin W) ≃ Fin (p + q) × Fin W :=
  (Equiv.sumProdDistrib (Fin p) (Fin q) (Fin W)).symm.trans
    (finSumFinEquiv.prodCongr (Equiv.refl (Fin W)))

private theorem pathCutEquiv_inl (W p q : ℕ) (i : Fin p) (α : Fin W) :
    pathCutEquiv W p q (Sum.inl (i, α)) = (Fin.castAdd q i, α) := by
  simp [pathCutEquiv]

private theorem pathCutEquiv_inr (W p q : ℕ) (j : Fin q) (β : Fin W) :
    pathCutEquiv W p q (Sum.inr (j, β)) = (Fin.natAdd p j, β) := by
  simp [pathCutEquiv]

/-- The diagonal block of the left part. -/
private theorem pathCut_left_entry (g : ℝ) {W p q : ℕ} (hq : 0 < q)
    (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (i i' : Fin p) (α β : Fin W) :
    (pathOp g V L₀ R₀ - (E : ℂ) • (1 : Matrix (Fin (p + q) × Fin W) (Fin (p + q) × Fin W) ℂ))
        (Fin.castAdd q i, α) (Fin.castAdd q i', β) =
      (pathOp g (V ∘ Fin.castAdd q) L₀ 0 -
        (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ)) (i, α) (i', β) := by
  have h1 : (i.val + 1 = p + q) ↔ False := by
    have := i.isLt
    constructor
    · intro h; omega
    · intro h; exact h.elim
  have h2 : pathAdj (p + q) (Fin.castAdd q i) (Fin.castAdd q i') = pathAdj p i i' := by
    simp [pathAdj]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq,
    pathCut_pathOp_apply, h2, Fin.castAdd_inj, Fin.val_castAdd, h1, Function.comp]
  simp

/-- The diagonal block of the right part. -/
private theorem pathCut_right_entry (g : ℝ) {W p q : ℕ} (hp : 0 < p)
    (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (j j' : Fin q) (α β : Fin W) :
    (pathOp g V L₀ R₀ - (E : ℂ) • (1 : Matrix (Fin (p + q) × Fin W) (Fin (p + q) × Fin W) ℂ))
        (Fin.natAdd p j, α) (Fin.natAdd p j', β) =
      (pathOp g (V ∘ Fin.natAdd p) 0 R₀ -
        (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ)) (j, α) (j', β) := by
  have h1 : ((p + j.val = 0)) ↔ False := by
    constructor
    · intro h; omega
    · intro h; exact h.elim
  have h2 : pathAdj (p + q) (Fin.natAdd p j) (Fin.natAdd p j') = pathAdj q j j' := by
    simp only [pathAdj, Matrix.of_apply, Fin.val_natAdd]
    have : (p + j.val + 1 = p + j'.val ∨ p + j'.val + 1 = p + j.val) ↔
        (j.val + 1 = j'.val ∨ j'.val + 1 = j.val) := by omega
    simp only [this]
  have h3 : (p + j.val + 1 = p + q) ↔ (j.val + 1 = q) := by omega
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq,
    pathCut_pathOp_apply, h2, Fin.natAdd_inj, Fin.val_natAdd, h1, h3, Function.comp]
  simp

/-- The coupling entry between the last block of the left part and the first block of the right
part. -/
private theorem pathCut_offdiag_entry (g : ℝ) {W p q : ℕ}
    (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (i : Fin p) (j : Fin q) (α β : Fin W) :
    (pathOp g V L₀ R₀ - (E : ℂ) • (1 : Matrix (Fin (p + q) × Fin W) (Fin (p + q) × Fin W) ℂ))
        (Fin.castAdd q i, α) (Fin.natAdd p j, β) =
      if i.val + 1 = p ∧ j.val = 0 ∧ α = β then ((g / max 1 g : ℝ) : ℂ) else 0 := by
  have hi := i.isLt
  have h1 : pathAdj (p + q) (Fin.castAdd q i) (Fin.natAdd p j) =
      if i.val + 1 = p ∧ j.val = 0 then 1 else 0 := by
    simp only [pathAdj, Matrix.of_apply, Fin.val_castAdd, Fin.val_natAdd]
    have : (i.val + 1 = p + j.val ∨ p + j.val + 1 = i.val) ↔ (i.val + 1 = p ∧ j.val = 0) := by
      omega
    simp only [this]
  have h2 : Fin.castAdd q i ≠ Fin.natAdd p j := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  have h3 : ((max 1 g : ℝ)⁻¹ : ℂ) * (g : ℂ) = ((g / max 1 g : ℝ) : ℂ) := by
    have : (max 1 g : ℝ) ≠ 0 := (lt_of_lt_of_le one_pos (le_max_left 1 g)).ne'
    push_cast
    field_simp
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq,
    pathCut_pathOp_apply, h1, h2, false_and, ite_false, add_zero]
  by_cases h : i.val + 1 = p ∧ j.val = 0
  · by_cases hab : α = β
    · simp [h, hab, ← h3]
    · simp [h, hab]
  · have h' : ¬ (i.val + 1 = p ∧ j.val = 0 ∧ α = β) := fun ⟨a, b, _⟩ => h ⟨a, b⟩
    simp only [h, h', ite_false]
    simp

/-- The coupling entry, transposed. -/
private theorem pathCut_offdiag_entry' (g : ℝ) {W p q : ℕ}
    (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (i : Fin p) (j : Fin q) (α β : Fin W) :
    (pathOp g V L₀ R₀ - (E : ℂ) • (1 : Matrix (Fin (p + q) × Fin W) (Fin (p + q) × Fin W) ℂ))
        (Fin.natAdd p j, β) (Fin.castAdd q i, α) =
      if i.val + 1 = p ∧ j.val = 0 ∧ α = β then ((g / max 1 g : ℝ) : ℂ) else 0 := by
  have hi := i.isLt
  have h1 : pathAdj (p + q) (Fin.natAdd p j) (Fin.castAdd q i) =
      if i.val + 1 = p ∧ j.val = 0 then 1 else 0 := by
    simp only [pathAdj, Matrix.of_apply, Fin.val_castAdd, Fin.val_natAdd]
    have : (p + j.val + 1 = i.val ∨ i.val + 1 = p + j.val) ↔ (i.val + 1 = p ∧ j.val = 0) := by
      omega
    simp only [this]
  have h2 : Fin.natAdd p j ≠ Fin.castAdd q i := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  have h3 : ((max 1 g : ℝ)⁻¹ : ℂ) * (g : ℂ) = ((g / max 1 g : ℝ) : ℂ) := by
    have : (max 1 g : ℝ) ≠ 0 := (lt_of_lt_of_le one_pos (le_max_left 1 g)).ne'
    push_cast
    field_simp
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq,
    pathCut_pathOp_apply, h1, h2, false_and, ite_false, add_zero]
  by_cases h : i.val + 1 = p ∧ j.val = 0
  · by_cases hab : α = β
    · simp [h, hab, ← h3]
    · have hab' : ¬ β = α := fun e => hab e.symm
      simp [h, hab, hab']
  · have h' : ¬ (i.val + 1 = p ∧ j.val = 0 ∧ α = β) := fun ⟨a, b, _⟩ => h ⟨a, b⟩
    simp only [h, h', ite_false]
    simp

/-- The coupling block between the left part and the right part. -/
private def pathCutB (g : ℝ) (W p q : ℕ) : Matrix (Fin p × Fin W) (Fin q × Fin W) ℂ :=
  Matrix.of fun x y =>
    if x.1.val + 1 = p ∧ y.1.val = 0 ∧ x.2 = y.2 then ((g / max 1 g : ℝ) : ℂ) else 0

/-- The block decomposition of `H - E` along the cut. -/
private theorem pathCut_blocks (g : ℝ) {W p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ) :
    (pathOp g V L₀ R₀ -
      (E : ℂ) • (1 : Matrix (Fin (p + q) × Fin W) (Fin (p + q) × Fin W) ℂ)).submatrix
        (pathCutEquiv W p q) (pathCutEquiv W p q) =
      Matrix.fromBlocks
        (pathOp g (V ∘ Fin.castAdd q) L₀ 0 -
          (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ))
        (pathCutB g W p q) (pathCutB g W p q)ᵀ
        (pathOp g (V ∘ Fin.natAdd p) 0 R₀ -
          (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ)) := by
  ext (⟨i, α⟩ | ⟨j, α⟩) (⟨i', β⟩ | ⟨j', β⟩)
  · simp only [Matrix.submatrix_apply, pathCutEquiv_inl, Matrix.fromBlocks_apply₁₁]
    exact pathCut_left_entry g hq V L₀ R₀ E i i' α β
  · simp only [Matrix.submatrix_apply, pathCutEquiv_inl, pathCutEquiv_inr,
      Matrix.fromBlocks_apply₁₂]
    rw [pathCut_offdiag_entry]
    rfl
  · simp only [Matrix.submatrix_apply, pathCutEquiv_inl, pathCutEquiv_inr,
      Matrix.fromBlocks_apply₂₁]
    rw [pathCut_offdiag_entry']
    simp only [pathCutB, Matrix.transpose_apply, Matrix.of_apply]
  · simp only [Matrix.submatrix_apply, pathCutEquiv_inr, Matrix.fromBlocks_apply₂₂]
    exact pathCut_right_entry g hp V L₀ R₀ E j j' α β

/-- Left multiplication of `X` by the coupling block. -/
private theorem pathCutB_mul_apply (g : ℝ) {W p q : ℕ} (hq : 0 < q)
    (X : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ) (x : Fin p × Fin W) (y : Fin q × Fin W) :
    (pathCutB g W p q * X) x y =
      if x.1.val + 1 = p then ((g / max 1 g : ℝ) : ℂ) * X (⟨0, hq⟩, x.2) y else 0 := by
  rw [Matrix.mul_apply]
  by_cases hx : x.1.val + 1 = p
  · simp only [hx, ite_true]
    rw [Finset.sum_eq_single (⟨0, hq⟩, x.2)]
    · simp [pathCutB, hx]
    · intro z _ hz
      have : ¬ (x.1.val + 1 = p ∧ z.1.val = 0 ∧ x.2 = z.2) := by
        rintro ⟨_, h1, h2⟩
        exact hz (Prod.ext (Fin.ext h1) h2.symm)
      simp [pathCutB, this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp [pathCutB, hx]

/-- The Schur correction `B X Bᵀ` of the left part. -/
private theorem pathCutB_mul_mul_transpose (g : ℝ) {W p q : ℕ} (hq : 0 < q)
    (X : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ) (x x' : Fin p × Fin W) :
    (pathCutB g W p q * X * (pathCutB g W p q)ᵀ) x x' =
      if x.1.val + 1 = p ∧ x'.1.val + 1 = p then
        ((g / max 1 g : ℝ) : ℂ) * ((g / max 1 g : ℝ) : ℂ) * X (⟨0, hq⟩, x.2) (⟨0, hq⟩, x'.2)
      else 0 := by
  rw [Matrix.mul_apply]
  simp only [pathCutB_mul_apply g hq X, Matrix.transpose_apply]
  by_cases hx : x.1.val + 1 = p
  · by_cases hx' : x'.1.val + 1 = p
    · simp only [hx, hx', and_self, ite_true]
      rw [Finset.sum_eq_single (⟨0, hq⟩, x'.2)]
      · simp [pathCutB, hx']
        ring
      · intro z _ hz
        have : ¬ (x'.1.val + 1 = p ∧ z.1.val = 0 ∧ x'.2 = z.2) := by
          rintro ⟨_, h1, h2⟩
          exact hz (Prod.ext (Fin.ext h1) h2.symm)
        simp [pathCutB, this]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · simp [pathCutB, hx, hx']
  · simp [hx]

/-- The Schur correction `Bᵀ X B` of the right part. -/
private theorem pathCutB_transpose_mul_mul (g : ℝ) {W p q : ℕ} (hp : 0 < p)
    (X : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ) (y y' : Fin q × Fin W) :
    ((pathCutB g W p q)ᵀ * X * pathCutB g W p q) y y' =
      if y.1.val = 0 ∧ y'.1.val = 0 then
        ((g / max 1 g : ℝ) : ℂ) * ((g / max 1 g : ℝ) : ℂ) *
          X (⟨p - 1, by omega⟩, y.2) (⟨p - 1, by omega⟩, y'.2)
      else 0 := by
  have key : ∀ (y : Fin q × Fin W) (x' : Fin p × Fin W),
      ((pathCutB g W p q)ᵀ * X) y x' =
        if y.1.val = 0 then ((g / max 1 g : ℝ) : ℂ) * X (⟨p - 1, by omega⟩, y.2) x' else 0 := by
    intro y x'
    rw [Matrix.mul_apply]
    by_cases hy : y.1.val = 0
    · simp only [hy, ite_true]
      rw [Finset.sum_eq_single (⟨p - 1, by omega⟩, y.2)]
      · simp [pathCutB, hy]
        omega
      · intro z _ hz
        have : ¬ (z.1.val + 1 = p ∧ y.1.val = 0 ∧ z.2 = y.2) := by
          rintro ⟨h1, _, h2⟩
          exact hz (Prod.ext (Fin.ext (by simp; omega)) h2)
        simp [pathCutB, this]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · simp [pathCutB, hy]
  rw [Matrix.mul_apply]
  simp only [key]
  by_cases hy : y.1.val = 0
  · by_cases hy' : y'.1.val = 0
    · simp only [hy, hy', and_self, ite_true]
      rw [Finset.sum_eq_single (⟨p - 1, by omega⟩, y'.2)]
      · have e : p - 1 + 1 = p := by omega
        simp [pathCutB, hy', e]
        ring
      · intro z _ hz
        have : ¬ (z.1.val + 1 = p ∧ y'.1.val = 0 ∧ z.2 = y'.2) := by
          rintro ⟨h1, _, h2⟩
          exact hz (Prod.ext (Fin.ext (by simp; omega)) h2)
        simp [pathCutB, this]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · simp [pathCutB, hy, hy']
  · simp [hy]

/-- The off-diagonal Schur term `X B Y` in blocks. -/
private theorem pathCutB_offdiag_apply (g : ℝ) {W p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (X : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ) (Y : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ)
    (i : Fin p) (j : Fin q) (α β : Fin W) :
    (X * pathCutB g W p q * Y) (i, α) (j, β) =
      ((g / max 1 g : ℝ) : ℂ) *
        (blockOf X i ⟨p - 1, by omega⟩ * blockOf Y ⟨0, hq⟩ j) α β := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [pathCutB_mul_apply g hq Y]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (⟨p - 1, by omega⟩ : Fin p)]
  · simp only [Matrix.mul_apply, blockOf, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have e : p - 1 + 1 = p := by omega
    simp [e]
    ring
  · intro a _ ha
    have : ¬ (a.val + 1 = p) := fun h => ha (Fin.ext (by simp; omega))
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The Schur complement of the right part in `H - E` is `H - E` of the left part with the
induced shift (proof of Proposition 8.2 [up:prop:fr-concentration]). -/
private theorem pathCut_schur_left (g : ℝ) {W p q : ℕ} (hq : 0 < q)
    (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ) :
    (pathOp g (V ∘ Fin.castAdd q) L₀ 0 - (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ)) -
        pathCutB g W p q * (pathOp g (V ∘ Fin.natAdd p) 0 R₀ -
          (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ))⁻¹ * (pathCutB g W p q)ᵀ =
      pathOp g (V ∘ Fin.castAdd q) L₀ (shiftFromRight g (V ∘ Fin.natAdd p) R₀ E) -
        (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ) := by
  ext ⟨i, α⟩ ⟨i', β⟩
  rw [Matrix.sub_apply, pathCutB_mul_mul_transpose g hq]
  have hs : shiftFromRight g (V ∘ Fin.natAdd p) R₀ E =
      -(((g / max 1 g) ^ 2 : ℝ) : ℂ) • blockOf (pathOp g (V ∘ Fin.natAdd p) 0 R₀ -
          (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ))⁻¹ ⟨0, hq⟩ ⟨0, hq⟩ := by
    simp only [shiftFromRight, hq, ↓reduceDIte, resolventMat]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq,
    pathCut_pathOp_apply, hs]
  by_cases hi : i = i'
  · subst hi
    by_cases hip : i.val + 1 = p
    · simp [hip, blockOf]
      ring
    · simp [hip]
  · have : ¬ (i.val + 1 = p ∧ i'.val + 1 = p) := by
      rintro ⟨h1, h2⟩
      exact hi (Fin.ext (by omega))
    simp [hi, this]

/-- The Schur complement of the left part in `H - E` is `H - E` of the right part with the
induced shift (proof of Proposition 8.2 [up:prop:fr-concentration]). -/
private theorem pathCut_schur_right (g : ℝ) {W p q : ℕ} (hp : 0 < p)
    (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ) :
    (pathOp g (V ∘ Fin.natAdd p) 0 R₀ - (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ)) -
        (pathCutB g W p q)ᵀ * (pathOp g (V ∘ Fin.castAdd q) L₀ 0 -
          (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ))⁻¹ * pathCutB g W p q =
      pathOp g (V ∘ Fin.natAdd p) (shiftFromLeft g (V ∘ Fin.castAdd q) L₀ E) R₀ -
        (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ) := by
  ext ⟨j, α⟩ ⟨j', β⟩
  rw [Matrix.sub_apply, pathCutB_transpose_mul_mul g hp]
  have hs : shiftFromLeft g (V ∘ Fin.castAdd q) L₀ E =
      -(((g / max 1 g) ^ 2 : ℝ) : ℂ) • blockOf (pathOp g (V ∘ Fin.castAdd q) L₀ 0 -
          (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ))⁻¹ ⟨p - 1, by omega⟩
            ⟨p - 1, by omega⟩ := by
    simp only [shiftFromLeft, hp, ↓reduceDIte, resolventMat]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq,
    pathCut_pathOp_apply, hs]
  by_cases hj : j = j'
  · subst hj
    by_cases hjp : j.val = 0
    · simp [hjp, blockOf]
      ring
    · simp [hjp]
  · have : ¬ (j.val = 0 ∧ j'.val = 0) := by
      rintro ⟨h1, h2⟩
      exact hj (Fin.ext (by omega))
    simp [hj, this]

/-- Top-left block of the inverse of `H - E` along the cut. -/
private theorem pathCut_inv_castAdd (g : ℝ) {W p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (hR : (pathOp g (V ∘ Fin.natAdd p) 0 R₀ -
      (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ)).det ≠ 0)
    (i i' : Fin p) (α β : Fin W) :
    resolventMat (pathOp g V L₀ R₀) E (Fin.castAdd q i, α) (Fin.castAdd q i', β) =
      resolventMat
        (pathOp g (V ∘ Fin.castAdd q) L₀ (shiftFromRight g (V ∘ Fin.natAdd p) R₀ E)) E
        (i, α) (i', β) := by
  have h1 := (pathCut_inv_fromBlocks₂₂
    (pathOp g (V ∘ Fin.castAdd q) L₀ 0 - (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ))
    (pathCutB g W p q) (pathCutB g W p q)ᵀ
    (pathOp g (V ∘ Fin.natAdd p) 0 R₀ - (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ))
    (isUnit_iff_ne_zero.mpr hR)).1
  have h2 := congrFun (congrFun h1 (i, α)) (i', β)
  rw [Matrix.toBlocks₁₁, Matrix.of_apply, ← pathCut_blocks g hp hq V L₀ R₀ E,
    Matrix.inv_submatrix_equiv, pathCut_schur_left g hq] at h2
  simpa [pathCutEquiv_inl, resolventMat] using h2

/-- Top-right block of the inverse of `H - E` along the cut. -/
private theorem pathCut_inv_castAdd_natAdd (g : ℝ) {W p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (hR : (pathOp g (V ∘ Fin.natAdd p) 0 R₀ -
      (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ)).det ≠ 0)
    (i : Fin p) (j : Fin q) (α β : Fin W) :
    resolventMat (pathOp g V L₀ R₀) E (Fin.castAdd q i, α) (Fin.natAdd p j, β) =
      -(((g / max 1 g : ℝ) : ℂ) *
        (blockOf (resolventMat
            (pathOp g (V ∘ Fin.castAdd q) L₀ (shiftFromRight g (V ∘ Fin.natAdd p) R₀ E)) E)
            i ⟨p - 1, by omega⟩ *
          blockOf (resolventMat (pathOp g (V ∘ Fin.natAdd p) 0 R₀) E) ⟨0, hq⟩ j) α β) := by
  have h1 := (pathCut_inv_fromBlocks₂₂
    (pathOp g (V ∘ Fin.castAdd q) L₀ 0 - (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ))
    (pathCutB g W p q) (pathCutB g W p q)ᵀ
    (pathOp g (V ∘ Fin.natAdd p) 0 R₀ - (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ))
    (isUnit_iff_ne_zero.mpr hR)).2
  have h2 := congrFun (congrFun h1 (i, α)) (j, β)
  rw [Matrix.toBlocks₁₂, Matrix.of_apply, ← pathCut_blocks g hp hq V L₀ R₀ E,
    Matrix.inv_submatrix_equiv, pathCut_schur_left g hq, Matrix.neg_apply,
    pathCutB_offdiag_apply g hp hq] at h2
  simpa [pathCutEquiv_inl, pathCutEquiv_inr, resolventMat] using h2

/-- Bottom-right block of the inverse of `H - E` along the cut. -/
private theorem pathCut_inv_natAdd (g : ℝ) {W p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (hL : (pathOp g (V ∘ Fin.castAdd q) L₀ 0 -
      (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ)).det ≠ 0)
    (j j' : Fin q) (α β : Fin W) :
    resolventMat (pathOp g V L₀ R₀) E (Fin.natAdd p j, α) (Fin.natAdd p j', β) =
      resolventMat
        (pathOp g (V ∘ Fin.natAdd p) (shiftFromLeft g (V ∘ Fin.castAdd q) L₀ E) R₀) E
        (j, α) (j', β) := by
  have h1 := pathCut_inv_fromBlocks₁₁
    (pathOp g (V ∘ Fin.castAdd q) L₀ 0 - (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ))
    (pathCutB g W p q) (pathCutB g W p q)ᵀ
    (pathOp g (V ∘ Fin.natAdd p) 0 R₀ - (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ))
    (isUnit_iff_ne_zero.mpr hL)
  have h2 := congrFun (congrFun h1 (j, α)) (j', β)
  rw [Matrix.toBlocks₂₂, Matrix.of_apply, ← pathCut_blocks g hp hq V L₀ R₀ E,
    Matrix.inv_submatrix_equiv, pathCut_schur_right g hp] at h2
  simpa [pathCutEquiv_inr, resolventMat] using h2

/-- Block Schur complement for a path cut into a left part `[0, p)` and a right part
`[p, p+q)`: off-diagonal blocks. -/
theorem pathOp_cut_offdiag (g : ℝ) {W p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (hR : (pathOp g (V ∘ Fin.natAdd p) 0 R₀ -
      (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ)).det ≠ 0)
    (i : Fin p) (j : Fin q) :
    blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.castAdd q i) (Fin.natAdd p j) =
      -((g / max 1 g : ℝ) : ℂ) •
        (blockOf (resolventMat
            (pathOp g (V ∘ Fin.castAdd q) L₀ (shiftFromRight g (V ∘ Fin.natAdd p) R₀ E)) E)
            i ⟨p - 1, by omega⟩ *
          blockOf (resolventMat (pathOp g (V ∘ Fin.natAdd p) 0 R₀) E) ⟨0, hq⟩ j) := by
  ext α β
  simp only [blockOf, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, neg_mul]
  exact pathCut_inv_castAdd_natAdd g hp hq V L₀ R₀ E hR i j α β

/-- Block Schur complement for a cut path: blocks of the left part. -/
theorem pathOp_cut_left (g : ℝ) {W p q : ℕ} (hq : 0 < q)
    (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ)
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (hR : (pathOp g (V ∘ Fin.natAdd p) 0 R₀ -
      (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ)).det ≠ 0)
    (i i' : Fin p) :
    blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.castAdd q i) (Fin.castAdd q i') =
      blockOf (resolventMat
        (pathOp g (V ∘ Fin.castAdd q) L₀ (shiftFromRight g (V ∘ Fin.natAdd p) R₀ E)) E) i i' := by
  ext α β
  simp only [blockOf, Matrix.of_apply]
  exact pathCut_inv_castAdd g i.pos hq V L₀ R₀ E hR i i' α β

/-- Block Schur complement for a cut path: blocks of the right part. -/
theorem pathOp_cut_right (g : ℝ) {W p q : ℕ} (hp : 0 < p)
    (V : Fin (p + q) → Matrix (Fin W) (Fin W) ℂ)
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (hL : (pathOp g (V ∘ Fin.castAdd q) L₀ 0 -
      (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ)).det ≠ 0)
    (j j' : Fin q) :
    blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.natAdd p j) (Fin.natAdd p j') =
      blockOf (resolventMat
        (pathOp g (V ∘ Fin.natAdd p) (shiftFromLeft g (V ∘ Fin.castAdd q) L₀ E) R₀) E) j j' := by
  ext α β
  simp only [blockOf, Matrix.of_apply]
  exact pathCut_inv_natAdd g hp j.pos V L₀ R₀ E hL j j' α β

end LSBA
