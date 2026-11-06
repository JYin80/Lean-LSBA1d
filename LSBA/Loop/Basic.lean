import LSBA.Model.Basic

/-!
# Loop words

The normalized block projections `E_a = P_a / W`, the signed matrices `X^+ = X`, `X^- = X*`, and
the loop `Tr(X^{σ_1} E_{a_1} ⋯ X^{σ_k} E_{a_k})` of (5.5) [fo:eq:loops] for an arbitrary matrix
`X` on `ℂ^L ⊗ ℂ^W` (Section 5.2 [sec:fo-loops]). The trace is unnormalized.
-/

open Real Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `E_a = P_a / W`, the normalized projection onto block `a`. -/
def blockE (W L : ℕ) (a : Fin L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.diagonal fun p => if p.1 = a then (W : ℂ)⁻¹ else 0

/-- `X^+ = X` and `X^- = X*`; the sign `true` is `+`. -/
def sgnMat {n : Type*} (X : Matrix n n ℂ) (σ : Bool) : Matrix n n ℂ := if σ then X else Xᴴ

/-- The loop `Tr(X^{σ_1} E_{a_1} ⋯ X^{σ_k} E_{a_k})` of (5.5) [fo:eq:loops]. -/
def loopTr {W L k : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a : Fin k → Fin L)
    (σ : Fin k → Bool) : ℂ :=
  (List.ofFn fun i : Fin k => sgnMat X (σ i) * blockE W L (a i)).prod.trace

/-- `ℒ_1(a, +) = ⟨X⟩_{aa} = W⁻¹ Tr X_{aa}`. -/
theorem loopTr_one {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a : Fin L) :
    loopTr X ![a] ![true] = (W : ℂ)⁻¹ * ∑ α, X (a, α) (a, α) := by
  simp only [loopTr, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, sgnMat, ite_true, blockE, Matrix.mul_diagonal, Matrix.trace,
    Matrix.diag, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp [Finset.mul_sum, mul_comm]
  · intro b _ hb
    simp [hb]
  · simp

/-- `ℒ_2(a, b; +, -) = W⁻² ‖X_{ba}‖²_HS`. -/
theorem loopTr_two {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    loopTr X ![a, b] ![true, false] =
      ((((W : ℝ) ^ 2)⁻¹ * ∑ β : Fin W, ∑ α : Fin W, ‖X (b, β) (a, α)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [loopTr, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ, sgnMat, ite_true, Bool.false_eq_true, ite_false]
  rw [← Matrix.mul_assoc]
  simp only [blockE, Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  have h : ∀ p : Fin L × Fin W, (X * Matrix.diagonal (fun q : Fin L × Fin W =>
      if q.1 = a then (W : ℂ)⁻¹ else 0) * Xᴴ) p p =
      ∑ q : Fin L × Fin W, if q.1 = a then (W : ℂ)⁻¹ * ((‖X p q‖ ^ 2 : ℝ) : ℂ) else 0 := by
    intro p
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.star_def]
    by_cases hq : q.1 = a
    · simp only [hq, ite_true, Complex.ofReal_pow, ← Complex.mul_conj']
      ring
    · simp [hq]
  simp only [h]
  simp only [Fintype.sum_prod_type]
  have h2 : ∀ (x : Fin L) (y : Fin W), (∑ x_2 : Fin L, ∑ x_3 : Fin W,
      if x_2 = a then (W : ℂ)⁻¹ * ((‖X (x, y) (x_2, x_3)‖ ^ 2 : ℝ) : ℂ) else 0) =
      ∑ x_3 : Fin W, (W : ℂ)⁻¹ * ((‖X (x, y) (a, x_3)‖ ^ 2 : ℝ) : ℂ) := by
    intro x y
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc
      simp [hc]
    · simp
  simp only [h2]
  rw [Finset.sum_eq_single b]
  · simp only [ite_true]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring
  · intro c _ hc
    simp [hc]
  · simp

/-- Moving the first factor of a word to the end is reindexing by `finRotate`. -/
private lemma loop_ofFn_rotate_prod {M : Type*} [Monoid M] {n : ℕ} (Y : Fin (n + 1) → M) :
    (List.ofFn fun i => Y (finRotate (n + 1) i)).prod =
      (List.ofFn fun i : Fin n => Y i.succ).prod * Y 0 := by
  rw [List.ofFn_succ', List.prod_concat, finRotate_last]
  congr 3
  funext i
  rw [finRotate_apply]
  exact congrArg Y (Fin.coeSucc_eq_succ)

/-- Cyclic invariance of a loop under a joint rotation of labels and signs. -/
theorem loopTr_rotate {W L k : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    loopTr X (a ∘ finRotate k) (σ ∘ finRotate k) = loopTr X a σ := by
  cases k with
  | zero => simp [loopTr]
  | succ n =>
    unfold loopTr
    rw [show (List.ofFn fun i : Fin (n + 1) =>
        sgnMat X ((σ ∘ finRotate (n + 1)) i) * blockE W L ((a ∘ finRotate (n + 1)) i)) =
      List.ofFn fun i => (fun j => sgnMat X (σ j) * blockE W L (a j)) (finRotate (n + 1) i) from
      rfl, loop_ofFn_rotate_prod (fun j => sgnMat X (σ j) * blockE W L (a j)),
      Matrix.trace_mul_comm, List.ofFn_succ, List.prod_cons]

/-- Interleaving two sequences, shifted by one position. -/
private lemma loop_interleave {M : Type*} [Monoid M] :
    ∀ (n : ℕ) (V : Fin (n + 1) → M) (U : Fin n → M),
      V 0 * (List.ofFn fun i : Fin n => U i * V i.succ).prod =
        (List.ofFn fun i : Fin n => V i.castSucc * U i).prod * V (Fin.last n)
  | 0, V, U => by simp
  | n + 1, V, U => by
    have ih := loop_interleave n (fun i => V i.succ) (fun i => U i.succ)
    simp only [List.ofFn_succ, List.prod_cons, Fin.succ_zero_eq_one, Fin.castSucc_zero]
    simp only [Fin.succ_zero_eq_one, Fin.succ_castSucc, Fin.succ_last] at ih
    simp only [← mul_assoc]
    rw [mul_assoc (V 0 * U 0) (V 1), ih]
    simp only [mul_assoc]

/-- The `ofFn` list reverses by reindexing with `Fin.rev`. -/
private lemma loop_ofFn_reverse {M : Type*} {n : ℕ} (f : Fin n → M) :
    (List.ofFn f).reverse = List.ofFn fun i => f (Fin.rev i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_reverse, List.getElem_ofFn, Fin.rev]
    exact congrArg f (Fin.ext (by simp only [List.length_ofFn]; omega))

/-- Cyclic move of the last factor `U_n` to the front, at the level of traces. -/
private lemma loop_cyclic {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (V U T : Fin (n + 1) → Matrix ι ι ℂ) (h0 : T 0 = U (Fin.last n) * V 0)
    (hs : ∀ i : Fin n, T i.succ = U i.castSucc * V i.succ) :
    (List.ofFn fun j => V j * U j).prod.trace = (List.ofFn T).prod.trace := by
  rw [List.ofFn_succ' (fun j => V j * U j), List.prod_concat, List.ofFn_succ (f := T),
    List.prod_cons, h0]
  simp only [hs]
  have key := loop_interleave n V (fun i => U i.castSucc)
  rw [mul_assoc, ← mul_assoc _ (V (Fin.last n)), ← key, mul_assoc, Matrix.trace_mul_comm,
    ← mul_assoc, mul_assoc, Matrix.trace_mul_comm]

/-- Complex conjugation reverses the word and flips every sign: the labels become
`a_{k-1}, …, a_0` and the sign in position `j` is `¬σ_{(k-j) mod k}`. -/
theorem star_loopTr {W L k : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    star (loopTr X a σ) =
      loopTr X (a ∘ Fin.rev) (fun j => !(σ (finRotate k (Fin.rev j)))) := by
  have hE : ∀ c : Fin L, (blockE W L c)ᴴ = blockE W L c := by
    intro c
    rw [blockE, Matrix.diagonal_conjTranspose]
    congr 1
    funext p
    by_cases h : p.1 = c <;> simp [h]
  have hS : ∀ s : Bool, (sgnMat X s)ᴴ = sgnMat X (!s) := by
    intro s
    cases s <;> simp [sgnMat]
  unfold loopTr
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_list_prod, List.map_ofFn,
    loop_ofFn_reverse]
  cases k with
  | zero => simp
  | succ n =>
    have hc := loop_cyclic (fun j => blockE W L (a (Fin.rev j)))
      (fun j => sgnMat X (!σ (Fin.rev j)))
      (fun j => sgnMat X (!σ (finRotate (n + 1) (Fin.rev j))) * blockE W L (a (Fin.rev j)))
      (by simp) (fun i => by simp [Fin.rev_succ, Fin.rev_castSucc])
    refine Eq.trans ?_ hc
    congr 3
    funext j
    simp only [Function.comp, Matrix.conjTranspose_mul, hE, hS]

end LSBA
