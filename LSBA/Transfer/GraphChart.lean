import LSBA.Transfer.Frames

/-!
# Graph frames and one transfer step

The frame `(I; -g R)` of the graph subspace `{(x, -g R x)}` and its image under one transfer
matrix `T(z) = [[z - V/g, -I], [I, 0]]` of Definition 7.1 [def:transfer-matrices]:
`T (I; -g R) = (-g⁻¹ M; I)` with `M = V - g z - g² R`, for every `R`. If `M` is invertible, this
is the graph frame of `R' = M⁻¹` times `-g⁻¹ M`, which is the recursion (9.2)
[su:eq:transported-normal] for the graph coordinate and the graph representation (9.1)
[su:eq:graph-input] (with `g z = E`).
-/

open Real Finset
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The `2W × W` frame `(I; -g R)` of the graph subspace `{(x, -g R x)}` (9.1)
[su:eq:graph-input]. -/
def graphFrame {W : ℕ} (g : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  colStack 1 (-((g : ℂ) • R))

/-- One transfer step on a graph frame: `T (I; -g R) = (-g⁻¹ (V - g z - g² R); I)`. -/
theorem transferMat_mul_graphFrame {W : ℕ} {g : ℝ} (hg : g ≠ 0) (z : ℂ)
    (V R : Matrix (Fin W) (Fin W) ℂ) :
    transferMat g z V * graphFrame g R =
      colStack (-((g : ℂ)⁻¹ • (V - ((g : ℂ) * z) • 1 - ((g : ℂ) ^ 2) • R))) 1 := by
  have hgc : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
  ext ⟨i, α⟩ β
  fin_cases i
  · simp [transferMat, transferFree, graphFrame, colStack, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.smul_apply, Matrix.sub_apply, mul_sub]
    by_cases h : α = β
    · simp only [h, ite_true]
      field_simp
      ring
    · simp only [h, ite_false]
      field_simp
      ring
  · simp [transferMat, transferFree, graphFrame, colStack, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- (9.2) [su:eq:transported-normal], (9.1) [su:eq:graph-input]: if `M = V - g z - g² R` is
invertible, then `T (I; -g R) = (I; -g M⁻¹) (-g⁻¹ M)`. -/
theorem transferMat_mul_graphFrame_of_isUnit {W : ℕ} {g : ℝ} (hg : g ≠ 0) (z : ℂ)
    (V R : Matrix (Fin W) (Fin W) ℂ) (hM : IsUnit (V - ((g : ℂ) * z) • 1 - ((g : ℂ) ^ 2) • R)) :
    transferMat g z V * graphFrame g R =
      graphFrame g (V - ((g : ℂ) * z) • 1 - ((g : ℂ) ^ 2) • R)⁻¹ *
        (-((g : ℂ)⁻¹ • (V - ((g : ℂ) * z) • 1 - ((g : ℂ) ^ 2) • R))) := by
  have hgc : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
  have hcol : ∀ X Y B : Matrix (Fin W) (Fin W) ℂ,
      colStack X Y * B = colStack (X * B) (Y * B) := by
    intro X Y B
    ext ⟨i, α⟩ β
    fin_cases i <;> simp [colStack, Matrix.mul_apply]
  set M : Matrix (Fin W) (Fin W) ℂ := V - ((g : ℂ) * z) • 1 - ((g : ℂ) ^ 2) • R with hMdef
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).mp hM)
  rw [transferMat_mul_graphFrame hg z V R, graphFrame, hcol]
  congr 1
  · simp [hMdef]
  · rw [neg_mul_neg, smul_mul_assoc, Matrix.mul_smul, hinv, smul_smul, mul_inv_cancel₀ hgc,
      one_smul]

end LSBA
