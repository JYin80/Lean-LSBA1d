import Mathlib

/-!
# Iterating a good–bad split

An abstract iteration lemma: if `P = G + B` with `‖B h‖ ≤ ½‖h‖`, `‖G h‖ ≤ K‖h‖_{ang}` and `‖P^r
1‖_{ang} ≤ ρ^r`, then `‖P^k 1‖ ≤ (1 + 4K) ρ^k` — the expansion (8.31) [cc:eq:firstgood] and (8.32)
[cc:eq:pointwise] in the proof of Lemma 8.10 [up:lem:operator-iteration].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Iterates of a split operator: if `‖B h‖_∞ ≤ ½ ‖h‖_∞`, `‖P h - B h‖_∞ ≤ K a(h)` and
`a(P^r 1) ≤ ρ^r` with `ρ ≥ 3/4`, then `‖P^k 1‖_∞ ≤ (1 + 4K) ρ^k`. This is the bound
(8.32) [cc:eq:pointwise] of Lemma 8.10 [up:lem:operator-iteration] for an abstract operator. -/
theorem iterate_one_le_of_split {X : Type*} {good : (X → ℝ) → Prop}
    {angLe : (X → ℝ) → ℝ → Prop} (P Bop : (X → ℝ) → X → ℝ) {K ρ : ℝ} (hK : 0 ≤ K)
    (hρ : 3 / 4 ≤ ρ) (hgood : ∀ r : ℕ, good (P^[r] fun _ => 1))
    (hB : ∀ h M, good h → (∀ x, |h x| ≤ M) → ∀ x, |Bop h x| ≤ M / 2)
    (hG : ∀ h M, good h → 0 ≤ M → angLe h M → ∀ x, |P h x - Bop h x| ≤ K * M)
    (hang : ∀ r : ℕ, angLe (P^[r] fun _ => 1) (ρ ^ r)) :
    ∀ k : ℕ, ∀ x, |P^[k] (fun _ => 1) x| ≤ (1 + 4 * K) * ρ ^ k := by
  intro k
  induction k with
  | zero =>
    intro x
    simp only [Function.iterate_zero, id_eq, abs_one, pow_zero, mul_one]
    linarith
  | succ k ih =>
    intro x
    have hρ0 : 0 ≤ ρ ^ k := pow_nonneg (by linarith) k
    have h1 := hB _ _ (hgood k) ih x
    have h2 := hG _ _ (hgood k) hρ0 (hang k) x
    rw [Function.iterate_succ_apply']
    have h3 : |P (P^[k] fun _ => (1 : ℝ)) x| ≤
        |Bop (P^[k] fun _ => (1 : ℝ)) x| + |P (P^[k] fun _ => (1 : ℝ)) x -
          Bop (P^[k] fun _ => (1 : ℝ)) x| := by
      calc |P (P^[k] fun _ => (1 : ℝ)) x|
          = |Bop (P^[k] fun _ => (1 : ℝ)) x + (P (P^[k] fun _ => (1 : ℝ)) x -
              Bop (P^[k] fun _ => (1 : ℝ)) x)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h4 : (1 + 4 * K) * ρ ^ k / 2 + K * ρ ^ k ≤ (1 + 4 * K) * ρ ^ (k + 1) := by
      rw [pow_succ]
      have : 0 ≤ ρ ^ k * (ρ - 3 / 4) * (1 + 4 * K) := by
        have : 0 ≤ ρ - 3 / 4 := by linarith
        have : 0 ≤ 1 + 4 * K := by linarith
        positivity
      nlinarith [this]
    linarith

end LSBA
