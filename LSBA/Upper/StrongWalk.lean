import LSBA.Spectral.BlockMask
import LSBA.Gauss.ScalarDensity

/-!
# Walks on the cycle

The objects of the two-path expansion behind the bound of [PSSS, Theorem 1] on the cycle: along a
walk `γ` of blocks, the sets `Λ_i = ℤ_L ∖ {γ_0, …, γ_{i-1}}` and the product
`G_{Λ_0}(γ_0, γ_0) G_{Λ_1}(γ_1, γ_1) ⋯ G_{Λ_k}(γ_k, γ_k)` of diagonal blocks of the masked
resolvents of (8.1) [up:eq:local-resolvent].
-/

open Finset
open scoped Matrix Kronecker

noncomputable section

open scoped Classical

namespace LSBA

/-- The blocks left after deleting the first `i` blocks of a walk:
`Λ_i = ℤ_L ∖ {γ_0, …, γ_{i-1}}`. -/
def walkRest {L : ℕ} (γ : ℕ → Fin L) (i : ℕ) : Finset (Fin L) :=
  univ.filter fun c => ∀ j < i, c ≠ γ j

/-- The product `G_{Λ_0}(γ_0, γ_0) G_{Λ_1}(γ_1, γ_1) ⋯ G_{Λ_k}(γ_k, γ_k)` of diagonal blocks of
masked resolvents along a walk. -/
def walkProd {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (E : ℝ) (γ : ℕ → Fin L)
    (k : ℕ) : Matrix (Fin W) (Fin W) ℂ :=
  ((List.range (k + 1)).map fun i => blockOf (maskRes H (walkRest γ i) E) (γ i) (γ i)).prod

end LSBA
