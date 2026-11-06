import LSBA.Upper.Interface

/-!
# Unions of energy sets in the count of (3.6) [eq:averaged-tail]

The count of (3.6) [eq:averaged-tail] is subadditive in the energy set and bounded by the eigenvalue
count.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The count of (3.6) [eq:averaged-tail] is subadditive in the energy set. -/
theorem tailCount_union_le (W L : ℕ) (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (J₁ J₂ : Set ℝ) (R A : ℝ) :
    tailCount W L H (J₁ ∪ J₂) R A ≤ tailCount W L H J₁ R A + tailCount W L H J₂ R A := by
  unfold tailCount profCount
  by_cases hH : H.IsHermitian
  · simp only [hH, ↓reduceDIte]
    refine le_trans (le_of_eq ?_) (Finset.card_union_le _ _)
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and, Set.mem_union]
    tauto
  · simp [hH]

/-- The count of (3.6) [eq:averaged-tail] is at most the number of eigenvalues in `J`. -/
theorem tailCount_le_countIn (W L : ℕ) (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (J : Set ℝ) (R A : ℝ) : tailCount W L H J R A ≤ countIn H J := by
  unfold tailCount profCount countIn
  by_cases hH : H.IsHermitian
  · simp only [hH, ↓reduceDIte]
    refine Finset.card_le_card fun k hk => ?_
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.1⟩
  · simp [hH]

end LSBA
