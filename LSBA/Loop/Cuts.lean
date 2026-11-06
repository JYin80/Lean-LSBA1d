import Mathlib

/-!
# Cut maps of loop words

Loop families indexed by length, labels and signs; the labels and signs of `Cut_{L,i,j}^c`,
`Cut_{R,i,j}^c` of (5.6) [fo:eq:cuts] and of the insertion `Cut_i^c` before (5.7) [fo:eq:light],
with positions from `0`; the quadratic cut sum of (5.8) [fo:eq:hierarchy] and (5.10)
[fo:eq:primitive]; the cut terms of (5.17) [fo:eq:error-hierarchy] and the operator `Θ` of
(5.14) [fo:eq:generator]. Shared by the primitive loops (`LSBA/Primitive/`) and the loop
hierarchy (`LSBA/Loop/`).
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- A family of loop functionals indexed by length, labels and signs. -/
abbrev LoopFam (L : ℕ) : Type := (n : ℕ) → (Fin n → Fin L) → (Fin n → Bool) → ℂ

/-- Labels of `Cut_{L,i,j}^c` in (5.6) [fo:eq:cuts] (positions from `0`). -/
def cutLLab {α : Type*} {k : ℕ} (a : Fin k → α) (i j : Fin k) (c : α) : Fin (k + i - j + 1) → α :=
  fun p => if h : p.val < i.val then a ⟨p.val, by have := i.2; omega⟩
    else if p.val = i.val then c
    else a ⟨p.val + j.val - i.val - 1, by have := p.2; have := j.2; omega⟩

/-- Signs of `Cut_{L,i,j}^c` in (5.6) [fo:eq:cuts]. -/
def cutLSgn {k : ℕ} (σ : Fin k → Bool) (i j : Fin k) : Fin (k + i - j + 1) → Bool :=
  fun p => if h : p.val ≤ i.val then σ ⟨p.val, by have := i.2; omega⟩
    else σ ⟨p.val + j.val - i.val - 1, by have := p.2; have := j.2; omega⟩

/-- Labels of `Cut_{R,i,j}^c` in (5.6) [fo:eq:cuts]. -/
def cutRLab {α : Type*} {k : ℕ} (a : Fin k → α) (i j : Fin k) (c : α) : Fin (j - i + 1) → α :=
  fun p => if h : p.val < j.val - i.val then a ⟨i.val + p.val, by have := j.2; omega⟩ else c

/-- Signs of `Cut_{R,i,j}^c` in (5.6) [fo:eq:cuts]. -/
def cutRSgn {k : ℕ} (σ : Fin k → Bool) (i j : Fin k) : Fin (j - i + 1) → Bool :=
  fun p => σ ⟨i.val + p.val, by have := p.2; have := i.2; have := j.2; omega⟩

/-- Labels of the insertion `Cut_i^c` before (5.7) [fo:eq:light]. -/
def insLab {α : Type*} {k : ℕ} (a : Fin k → α) (i : Fin k) (c : α) : Fin (k + 1) → α :=
  Fin.insertNth i.castSucc c a

/-- Signs of the insertion `Cut_i^c`: the sign `σ_i` is doubled. -/
def insSgn {k : ℕ} (σ : Fin k → Bool) (i : Fin k) : Fin (k + 1) → Bool :=
  Fin.insertNth i.castSucc (σ i) σ

/-- `Σ_{i<j} Σ_c (Cut_L F)(Cut_R F)`, the quadratic term of (5.8) [fo:eq:hierarchy] and (5.10)
[fo:eq:primitive]. -/
def cutSumFam {L k : ℕ} (F : LoopFam L) (a : Fin k → Fin L) (σ : Fin k → Bool) : ℂ :=
  ∑ i : Fin k, ∑ j : Fin k, if i < j then ∑ c : Fin L,
    F _ (cutLLab a i j c) (cutLSgn σ i j) * F _ (cutRLab a i j c) (cutRSgn σ i j) else 0

/-- The cut terms of (5.17) [fo:eq:error-hierarchy]. -/
def cutErrSum {L k : ℕ} (K D : LoopFam L) (a : Fin k → Fin L) (σ : Fin k → Bool) : ℂ :=
  ∑ i : Fin k, ∑ j : Fin k, if i < j then ∑ c : Fin L,
    (K _ (cutLLab a i j c) (cutLSgn σ i j) * D _ (cutRLab a i j c) (cutRSgn σ i j) +
      D _ (cutLLab a i j c) (cutLSgn σ i j) * K _ (cutRLab a i j c) (cutRSgn σ i j) +
      D _ (cutLLab a i j c) (cutLSgn σ i j) * D _ (cutRLab a i j c) (cutRSgn σ i j)) else 0

/-- The operator `Θ_{u,σ}` of (5.14) [fo:eq:generator] with two-loop kernel `K 2`. -/
def thetaOp {L k : ℕ} (γ : ℝ) (W : ℕ) (K D : LoopFam L) (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ℂ :=
  ((γ * W : ℝ) : ℂ) * ∑ j : Fin k, ∑ c : Fin L,
    K 2 ![a j, c] ![σ j, σ (finRotate k j)] * D k (Function.update a j c) σ

/-- Linear source of (5.17) [fo:eq:error-hierarchy] after `Θ` is removed: `𝒦_k D_2` at the
adjacent pairs, `D_2 𝒦_k` at the cyclic pair, both orders at nonadjacent pairs; `0` for `k ≤ 2`. -/
def cutSrcLin {L k : ℕ} (K D : LoopFam L) (a : Fin k → Fin L) (σ : Fin k → Bool) : ℂ :=
  if k ≤ 2 then 0 else
  ∑ i : Fin k, ∑ j : Fin k, if i < j then ∑ c : Fin L,
    (if j.val = i.val + 1 then
        K _ (cutLLab a i j c) (cutLSgn σ i j) * D _ (cutRLab a i j c) (cutRSgn σ i j)
      else if i.val = 0 ∧ j.val = k - 1 then
        D _ (cutLLab a i j c) (cutLSgn σ i j) * K _ (cutRLab a i j c) (cutRSgn σ i j)
      else
        K _ (cutLLab a i j c) (cutLSgn σ i j) * D _ (cutRLab a i j c) (cutRSgn σ i j) +
          D _ (cutLLab a i j c) (cutLSgn σ i j) * K _ (cutRLab a i j c) (cutRSgn σ i j)) else 0

/-- Quadratic source `Σ_{i<j} Σ_c (Cut_L D)(Cut_R D)` of (5.17) [fo:eq:error-hierarchy]. -/
def cutSrcQuad {L k : ℕ} (D : LoopFam L) (a : Fin k → Fin L) (σ : Fin k → Bool) : ℂ :=
  cutSumFam D a σ

end LSBA
