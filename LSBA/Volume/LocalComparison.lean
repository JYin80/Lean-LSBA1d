import LSBA.Model.Basic
import LSBA.Spectral.Resolvent

/-!
# Local resolvent comparison

Theorem 4.1 [uv:thm:smooth-cutoff]: for the block operator on the cycle `ℤ_L` and its periodic
restriction to the window of `2R + 1` blocks around `a`, with the same onsite blocks and
hopping, the imaginary parts of the diagonal blocks at `a` of the two resolvents are comparable
within the factor `3` whenever `η R ≥ 2`. The estimate is deterministic.
-/

open Real Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The `(a, b)` block of a matrix on `ℂ^L ⊗ ℂ^W`. -/
def blockOf {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun α β => X (a, α) (b, β)

/-- Imaginary part `(X - X*) / (2i)` of a square matrix. -/
def matIm {m : Type*} (X : Matrix m m ℂ) : Matrix m m ℂ := (2 * Complex.I)⁻¹ • (X - Xᴴ)

/-- Real part of the quadratic form `u* M u`. -/
def qform {m : Type*} [Fintype m] (M : Matrix m m ℂ) (u : m → ℂ) : ℝ :=
  (∑ i, ∑ j, star (u i) * M i j * u j).re

/-- Block `a - R + j` of `ℤ_L` for `j ∈ {0, …, 2R}`: the window `[a - R, a + R]`. -/
def windowBlock {L : ℕ} (a : Fin L) (R : ℕ) (j : Fin (2 * R + 1)) : Fin L :=
  ⟨(a.val + j.val + L * R - R) % L, Nat.mod_lt _ a.pos⟩

/-- Centre `j = R` of the window. -/
def windowCenter (R : ℕ) : Fin (2 * R + 1) := ⟨R, by omega⟩

/-- Onsite blocks of the window: the periodic restriction `H_I^per` is `Hdet g` of these. -/
def windowBlocks {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (a : Fin L) (R : ℕ) :
    Fin (2 * R + 1) → Matrix (Fin W) (Fin W) ℂ :=
  fun j => V (windowBlock a R j)

theorem windowBlock_windowCenter {L : ℕ} (a : Fin L) (R : ℕ) :
    windowBlock a R (windowCenter R) = a := by
  have h1 : R ≤ L * R := Nat.le_mul_of_pos_left R a.pos
  apply Fin.ext
  simp only [windowBlock, windowCenter]
  have : a.val + R + L * R - R = a.val + L * R := by omega
  rw [this, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt a.isLt

theorem windowBlock_injective {L : ℕ} (a : Fin L) (R : ℕ) (h : 2 * R + 1 ≤ L) :
    Function.Injective (windowBlock a R) := by
  intro j k hjk
  have h1 : R ≤ L * R := Nat.le_mul_of_pos_left R a.pos
  have h2 : (a.val + j.val + L * R - R) % L = (a.val + k.val + L * R - R) % L :=
    congrArg Fin.val hjk
  have e1 : a.val + j.val + L * R - R = (a.val + L * R - R) + j.val := by omega
  have e2 : a.val + k.val + L * R - R = (a.val + L * R - R) + k.val := by omega
  rw [e1, e2] at h2
  have h3 : j.val ≡ k.val [MOD L] := Nat.ModEq.add_left_cancel' _ h2
  have := Nat.ModEq.eq_of_lt_of_lt h3 (by omega) (by omega)
  exact Fin.ext this

/-- Consecutive window positions `j, j + 1` are consecutive blocks `b, b + 1` of `ℤ_L`. -/
private lemma localComparison_windowBlock_succ {L : ℕ} (a : Fin L) (R : ℕ)
    (j k : Fin (2 * R + 1)) (hjk : j.val + 1 = k.val) :
    ((windowBlock a R j).val + 1) % L = (windowBlock a R k).val := by
  have h1 : R ≤ L * R := Nat.le_mul_of_pos_left R a.pos
  simp only [windowBlock]
  rw [Nat.mod_add_mod]
  congr 1
  omega

/-- The successor map `b ↦ b + 1` of `ℤ_L` is injective. -/
private lemma localComparison_succ_injective {L : ℕ} (b b' : Fin L)
    (h : (b.val + 1) % L = (b'.val + 1) % L) : b = b' := by
  have h3 : b.val ≡ b'.val [MOD L] := Nat.ModEq.add_right_cancel' 1 h
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h3 b.isLt b'.isLt)

/-- Sum against the adjacency row of the cycle at an interior window position. -/
private lemma localComparison_cycleAdj_sum {L : ℕ} (a : Fin L) (R : ℕ) (j : Fin (2 * R + 1))
    (h0 : 0 < j.val) (h1 : j.val < 2 * R) (f : Fin L → ℂ) :
    ∑ b, cycleAdj L (windowBlock a R j) b * f b =
      f (windowBlock a R ⟨j.val + 1, by omega⟩) + f (windowBlock a R ⟨j.val - 1, by omega⟩) := by
  have hs : ∀ b : Fin L, cycleAdj L (windowBlock a R j) b * f b =
      (if b = windowBlock a R ⟨j.val + 1, by omega⟩ then f b else 0) +
      (if b = windowBlock a R ⟨j.val - 1, by omega⟩ then f b else 0) := by
    intro b
    have e1 : (b.val = ((windowBlock a R j).val + 1) % L) ↔
        b = windowBlock a R ⟨j.val + 1, by omega⟩ := by
      rw [Fin.ext_iff, localComparison_windowBlock_succ a R j ⟨j.val + 1, by omega⟩ rfl]
    have e2 : ((windowBlock a R j).val = (b.val + 1) % L) ↔
        b = windowBlock a R ⟨j.val - 1, by omega⟩ := by
      have hh := localComparison_windowBlock_succ a R ⟨j.val - 1, by omega⟩ j (by simp; omega)
      constructor
      · intro h
        apply localComparison_succ_injective
        rw [hh, h]
      · intro h
        rw [h]
        exact hh.symm
    simp only [cycleAdj, Matrix.of_apply, add_mul, ite_mul, one_mul, zero_mul, e1, e2]
  simp only [hs, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Positions `j, k` of the window path are neighbours. -/
private def localComparison_adj {N : ℕ} (j k : Fin N) : Prop :=
  j.val + 1 = k.val ∨ k.val + 1 = j.val

/-- Neighbouring positions of the window path form a symmetric relation. -/
private lemma localComparison_adj_comm {N : ℕ} (j k : Fin N) :
    localComparison_adj j k ↔ localComparison_adj k j := by
  unfold localComparison_adj
  exact Or.comm

/-- Every position of the window path has at most two neighbours. -/
private lemma localComparison_card_adj {N : ℕ} (j : Fin N) :
    (Finset.univ.filter fun k : Fin N => localComparison_adj j k).card ≤ 2 := by
  have h1 : (Finset.univ.filter fun k : Fin N => j.val + 1 = k.val).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact Fin.ext (by omega)
  have h2 : (Finset.univ.filter fun k : Fin N => k.val + 1 = j.val).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact Fin.ext (by omega)
  calc (Finset.univ.filter fun k : Fin N => localComparison_adj j k).card
      ≤ ((Finset.univ.filter fun k : Fin N => j.val + 1 = k.val) ∪
          (Finset.univ.filter fun k : Fin N => k.val + 1 = j.val)).card := by
        apply Finset.card_le_card
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hk ⊢
        exact hk
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 2 := by omega

/-- Schur test for a matrix supported on neighbouring pairs of the window path, with entries
bounded by `δ`: every row and every column has at most two nonzero entries. -/
private lemma localComparison_schur {N : ℕ} (t : Fin N → Fin N → ℂ) (x : Fin N → ℂ) (δ : ℝ)
    (ht : ∀ j k, localComparison_adj j k → ‖t j k‖ ≤ δ) :
    ∑ j, ‖∑ k, if localComparison_adj j k then t j k * x k else 0‖ ^ 2 ≤
      4 * δ ^ 2 * ∑ k, ‖x k‖ ^ 2 := by
  have hrow : ∀ j, ‖∑ k, if localComparison_adj j k then t j k * x k else 0‖ ^ 2 ≤
      2 * ∑ k, if localComparison_adj j k then δ ^ 2 * ‖x k‖ ^ 2 else 0 := by
    intro j
    have h1 : ‖∑ k, if localComparison_adj j k then t j k * x k else 0‖ ≤
        ∑ k, if localComparison_adj j k then δ * ‖x k‖ else 0 := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      split_ifs with h
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (ht j k h) (norm_nonneg _)
      · simp
    have h2 : (∑ k, if localComparison_adj j k then δ * ‖x k‖ else 0) ^ 2 ≤
        2 * ∑ k, if localComparison_adj j k then δ ^ 2 * ‖x k‖ ^ 2 else 0 := by
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      refine sq_sum_le_card_mul_sum_sq.trans ?_
      have hc : ((Finset.univ.filter fun k : Fin N => localComparison_adj j k).card : ℝ) ≤ 2 := by
        exact_mod_cast localComparison_card_adj j
      refine mul_le_mul hc (le_of_eq ?_) (Finset.sum_nonneg fun k _ => by positivity)
        (by norm_num)
      exact Finset.sum_congr rfl fun k _ => by ring
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2
  calc ∑ j, ‖∑ k, if localComparison_adj j k then t j k * x k else 0‖ ^ 2
      ≤ ∑ j, 2 * ∑ k, if localComparison_adj j k then δ ^ 2 * ‖x k‖ ^ 2 else 0 :=
        Finset.sum_le_sum fun j _ => hrow j
    _ = 2 * ∑ k, ∑ j, if localComparison_adj j k then δ ^ 2 * ‖x k‖ ^ 2 else 0 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 2 * ∑ k, 2 * (δ ^ 2 * ‖x k‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by norm_num)
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hc : ((Finset.univ.filter fun j : Fin N => localComparison_adj j k).card : ℝ) ≤ 2 := by
          have : (Finset.univ.filter fun j : Fin N => localComparison_adj j k) =
              (Finset.univ.filter fun j : Fin N => localComparison_adj k j) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact localComparison_adj_comm j k
          rw [this]
          exact_mod_cast localComparison_card_adj k
        exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 4 * δ ^ 2 * ∑ k, ‖x k‖ ^ 2 := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring

/-- The cutoff `χ(b) = max{0, 1 - |b - a| / R}` of the proof of Theorem 4.1
[uv:thm:smooth-cutoff] at window position `j`, that is `min{j, 2R - j} / R`. -/
private def localComparison_cut (R : ℕ) (j : Fin (2 * R + 1)) : ℝ :=
  ((min j.val (2 * R - j.val) : ℕ) : ℝ) / R

/-- The cutoff equals `1` at the window centre. -/
private lemma localComparison_cut_center {R : ℕ} (hR : 1 ≤ R) :
    localComparison_cut R (windowCenter R) = 1 := by
  have : min R (2 * R - R) = R := by omega
  simp only [localComparison_cut, windowCenter, this]
  have : (R : ℝ) ≠ 0 := by positivity
  field_simp

/-- The cutoff vanishes at both ends of the window. -/
private lemma localComparison_cut_ne_zero {R : ℕ} {j : Fin (2 * R + 1)}
    (h : localComparison_cut R j ≠ 0) : 0 < j.val ∧ j.val < 2 * R := by
  by_contra hc
  apply h
  have : min j.val (2 * R - j.val) = 0 := by
    have := j.isLt
    omega
  simp [localComparison_cut, this]

/-- The cutoff changes by at most `1 / R` between neighbouring window positions. -/
private lemma localComparison_cut_adj {R : ℕ} (hR : 1 ≤ R) {j k : Fin (2 * R + 1)}
    (h : localComparison_adj j k) :
    |localComparison_cut R k - localComparison_cut R j| ≤ 1 / R := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have h1 : min k.val (2 * R - k.val) ≤ min j.val (2 * R - j.val) + 1 := by
    unfold localComparison_adj at h
    omega
  have h2 : min j.val (2 * R - j.val) ≤ min k.val (2 * R - k.val) + 1 := by
    unfold localComparison_adj at h
    omega
  have h1' : ((min k.val (2 * R - k.val) : ℕ) : ℝ) ≤ ((min j.val (2 * R - j.val) : ℕ) : ℝ) + 1 := by
    exact_mod_cast h1
  have h2' : ((min j.val (2 * R - j.val) : ℕ) : ℝ) ≤ ((min k.val (2 * R - k.val) : ℕ) : ℝ) + 1 := by
    exact_mod_cast h2
  unfold localComparison_cut
  rw [← sub_div, abs_div, abs_of_pos hRpos, div_le_div_iff_of_pos_right hRpos, abs_le]
  constructor <;> linarith

/-- Window cycle of `2R + 1` blocks: the wrap-around edge is invisible after multiplying by
the cutoff, which vanishes at both ends. -/
private lemma localComparison_cycleAdj_cut {R : ℕ} (j k : Fin (2 * R + 1)) :
    cycleAdj (2 * R + 1) j k * (localComparison_cut R k : ℂ) =
      if localComparison_adj j k then (localComparison_cut R k : ℂ) else 0 := by
  by_cases hc : localComparison_cut R k = 0
  · simp [hc]
  · obtain ⟨hk0, hk1⟩ := localComparison_cut_ne_zero hc
    have e1 : (k.val = (j.val + 1) % (2 * R + 1)) ↔ j.val + 1 = k.val := by
      by_cases hj : j.val + 1 < 2 * R + 1
      · rw [Nat.mod_eq_of_lt hj]; omega
      · have : j.val + 1 = 2 * R + 1 := by have := j.isLt; omega
        rw [this, Nat.mod_self]; omega
    have e2 : (j.val = (k.val + 1) % (2 * R + 1)) ↔ k.val + 1 = j.val := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp only [cycleAdj, Matrix.of_apply, e1, e2, localComparison_adj]
    by_cases h1 : j.val + 1 = k.val <;> by_cases h2 : k.val + 1 = j.val
    · omega
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]

/-- Entry `(j, α)` of `Hdet g V` applied to a vector. -/
private lemma localComparison_Hdet_mulVec (g : ℝ) {W L : ℕ}
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (x : Fin L × Fin W → ℂ) (j : Fin L) (α : Fin W) :
    (Hdet g V *ᵥ x) (j, α) = ((max 1 g : ℝ)⁻¹ : ℂ) *
      ((g : ℂ) * ∑ k, cycleAdj L j k * x (k, α) + ∑ γ, V j α γ * x (j, γ)) := by
  simp only [Hdet, Matrix.smul_mulVec, Matrix.add_mulVec, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul]
  congr 2
  · simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  · simp only [Matrix.mulVec, dotProduct, blockDiagOp, Matrix.of_apply, Fintype.sum_prod_type]
    simp

/-- The rectangular multiplication operator `χ` from the cycle `ℤ_L` to the window of
Theorem 4.1 [uv:thm:smooth-cutoff]: it sends block `windowBlock a R j` to position `j` with
weight `χ(j)`. -/
private def localComparison_chi {W L : ℕ} (a : Fin L) (R : ℕ) :
    Matrix (Fin (2 * R + 1) × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.of fun p q =>
    if windowBlock a R p.1 = q.1 ∧ p.2 = q.2 then (localComparison_cut R p.1 : ℂ) else 0

/-- Entry `(k, γ)` of `χ` applied to a vector. -/
private lemma localComparison_chi_mulVec {W L : ℕ} (a : Fin L) (R : ℕ) (v : Fin L × Fin W → ℂ)
    (k : Fin (2 * R + 1)) (γ : Fin W) :
    (localComparison_chi a R *ᵥ v) (k, γ) =
      (localComparison_cut R k : ℂ) * v (windowBlock a R k, γ) := by
  simp only [Matrix.mulVec, dotProduct, localComparison_chi, Matrix.of_apply, Fintype.sum_prod_type,
    ite_and, ite_mul, zero_mul]
  simp

/-- Sum over the neighbours of an interior window position. -/
private lemma localComparison_adj_sum {R : ℕ} (j : Fin (2 * R + 1)) (h0 : 0 < j.val)
    (h1 : j.val < 2 * R) (F : Fin (2 * R + 1) → ℂ) :
    ∑ k, (if localComparison_adj j k then F k else 0) =
      F ⟨j.val + 1, by omega⟩ + F ⟨j.val - 1, by omega⟩ := by
  have hs : ∀ k : Fin (2 * R + 1), (if localComparison_adj j k then F k else 0) =
      (if k = ⟨j.val + 1, by omega⟩ then F k else 0) +
      (if k = ⟨j.val - 1, by omega⟩ then F k else 0) := by
    intro k
    have e1 : k = (⟨j.val + 1, by omega⟩ : Fin (2 * R + 1)) ↔ j.val + 1 = k.val := by
      rw [Fin.ext_iff]; exact eq_comm
    have e2 : k = (⟨j.val - 1, by omega⟩ : Fin (2 * R + 1)) ↔ k.val + 1 = j.val := by
      rw [Fin.ext_iff]; simp only; omega
    simp only [localComparison_adj, e1, e2]
    by_cases h1 : j.val + 1 = k.val <;> by_cases h2 : k.val + 1 = j.val
    · omega
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  simp only [hs, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Hopping part of the commutator `H_I^per χ - χ H_L` applied to a vector. -/
private lemma localComparison_hop {W L : ℕ} (a : Fin L) (R : ℕ)
    (v : Fin L × Fin W → ℂ) (j : Fin (2 * R + 1)) (α : Fin W) :
    ∑ k, cycleAdj (2 * R + 1) j k * ((localComparison_cut R k : ℂ) * v (windowBlock a R k, α)) -
      (localComparison_cut R j : ℂ) * ∑ b, cycleAdj L (windowBlock a R j) b * v (b, α) =
    ∑ k, if localComparison_adj j k then
      ((localComparison_cut R k - localComparison_cut R j : ℝ) : ℂ) * v (windowBlock a R k, α)
      else 0 := by
  have hsplit : ∀ k : Fin (2 * R + 1), (if localComparison_adj j k then
      ((localComparison_cut R k - localComparison_cut R j : ℝ) : ℂ) * v (windowBlock a R k, α)
      else 0) = (if localComparison_adj j k then
        (localComparison_cut R k : ℂ) * v (windowBlock a R k, α) else 0) -
        (if localComparison_adj j k then
        (localComparison_cut R j : ℂ) * v (windowBlock a R k, α) else 0) := by
    intro k
    split_ifs
    · push_cast; ring
    · simp
  have E1 : ∑ k, cycleAdj (2 * R + 1) j k * ((localComparison_cut R k : ℂ) *
      v (windowBlock a R k, α)) = ∑ k, if localComparison_adj j k then
        (localComparison_cut R k : ℂ) * v (windowBlock a R k, α) else 0 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, localComparison_cycleAdj_cut]
    split_ifs <;> simp
  have E2 : (localComparison_cut R j : ℂ) * ∑ b, cycleAdj L (windowBlock a R j) b * v (b, α) =
      ∑ k, if localComparison_adj j k then
        (localComparison_cut R j : ℂ) * v (windowBlock a R k, α) else 0 := by
    by_cases hc : localComparison_cut R j = 0
    · simp [hc]
    · obtain ⟨h0, h1⟩ := localComparison_cut_ne_zero hc
      rw [localComparison_cycleAdj_sum a R j h0 h1 (fun b => v (b, α)),
        localComparison_adj_sum j h0 h1 (fun k => (localComparison_cut R j : ℂ) *
          v (windowBlock a R k, α))]
      ring
  simp only [hsplit, Finset.sum_sub_distrib, E1, E2]

/-- The commutator `K = H_I^per χ - χ H_L` acts on a vector through the hopping weight
`g / max{1,g}` and the cutoff differences at neighbouring window positions. -/
private lemma localComparison_K_apply (g : ℝ) {W L : ℕ}
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (a : Fin L) (R : ℕ)
    (v : Fin L × Fin W → ℂ) (j : Fin (2 * R + 1)) (α : Fin W) :
    ((Hdet g (windowBlocks V a R) * localComparison_chi a R -
        localComparison_chi a R * Hdet g V) *ᵥ v) (j, α) =
      ((g / max 1 g : ℝ) : ℂ) * ∑ k, if localComparison_adj j k then
        ((localComparison_cut R k - localComparison_cut R j : ℝ) : ℂ) *
          v (windowBlock a R k, α) else 0 := by
  have h1 : (Hdet g (windowBlocks V a R) * localComparison_chi a R) *ᵥ v =
      Hdet g (windowBlocks V a R) *ᵥ (localComparison_chi a R *ᵥ v) :=
    (Matrix.mulVec_mulVec v _ _).symm
  have h2 : (localComparison_chi a R * Hdet g V) *ᵥ v =
      localComparison_chi a R *ᵥ (Hdet g V *ᵥ v) :=
    (Matrix.mulVec_mulVec v _ _).symm
  rw [Matrix.sub_mulVec, h1, h2, Pi.sub_apply,
    localComparison_Hdet_mulVec, localComparison_chi_mulVec, localComparison_Hdet_mulVec]
  simp only [localComparison_chi_mulVec, windowBlocks]
  rw [← localComparison_hop a R v j α]
  have hV : ∑ γ, V (windowBlock a R j) α γ * ((localComparison_cut R j : ℂ) *
      v (windowBlock a R j, γ)) = (localComparison_cut R j : ℂ) *
      ∑ γ, V (windowBlock a R j) α γ * v (windowBlock a R j, γ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun γ _ => by ring
  rw [hV]
  push_cast
  ring

/-- The commutator `K = H_I^per χ - χ H_L` has norm at most `2 g / (max{1,g} R) ≤ η`, stated as
an inequality between explicit sums of squares (the Schur bound of Theorem 4.1
[uv:thm:smooth-cutoff]). -/
private lemma localComparison_K_bound (g : ℝ) (hg : 0 ≤ g) {W L : ℕ}
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (a : Fin L) (R : ℕ) (hR : 1 ≤ R)
    (hRL : 2 * R + 1 ≤ L) (η : ℝ) (hη : 2 ≤ η * R) (v : Fin L × Fin W → ℂ) :
    ∑ p, ‖((Hdet g (windowBlocks V a R) * localComparison_chi a R -
        localComparison_chi a R * Hdet g V) *ᵥ v) p‖ ^ 2 ≤ η ^ 2 * ∑ q, ‖v q‖ ^ 2 := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hm : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hβ0 : 0 ≤ g / max 1 g := div_nonneg hg hm.le
  have hβ1 : g / max 1 g ≤ 1 := (div_le_one hm).mpr (le_max_right _ _)
  have hηR : 4 * (1 / (R : ℝ)) ^ 2 ≤ η ^ 2 := by
    have h2 : 2 / (R : ℝ) ≤ η := by rw [div_le_iff₀ hRpos]; exact hη
    have : 4 * (1 / (R : ℝ)) ^ 2 = (2 / (R : ℝ)) ^ 2 := by ring
    rw [this]
    exact pow_le_pow_left₀ (by positivity) h2 2
  have hinj := windowBlock_injective a R hRL
  have hper : ∀ α : Fin W, ∑ j : Fin (2 * R + 1), ‖((Hdet g (windowBlocks V a R) *
        localComparison_chi a R - localComparison_chi a R * Hdet g V) *ᵥ v) (j, α)‖ ^ 2 ≤
      η ^ 2 * ∑ b : Fin L, ‖v (b, α)‖ ^ 2 := by
    intro α
    have hS := localComparison_schur
      (fun j k => ((localComparison_cut R k - localComparison_cut R j : ℝ) : ℂ))
      (fun k => v (windowBlock a R k, α)) (1 / (R : ℝ))
      (fun j k hjk => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact localComparison_cut_adj hR hjk)
    have hsub : ∑ k : Fin (2 * R + 1), ‖v (windowBlock a R k, α)‖ ^ 2 ≤
        ∑ b : Fin L, ‖v (b, α)‖ ^ 2 := by
      rw [← Finset.sum_image (f := fun b : Fin L => ‖v (b, α)‖ ^ 2)
        (s := Finset.univ) (g := windowBlock a R) (fun x _ y _ h => hinj h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => by positivity)
    have hterm : ∀ j : Fin (2 * R + 1), ‖((Hdet g (windowBlocks V a R) *
        localComparison_chi a R - localComparison_chi a R * Hdet g V) *ᵥ v) (j, α)‖ ^ 2 ≤
        ‖∑ k, if localComparison_adj j k then
          ((localComparison_cut R k - localComparison_cut R j : ℝ) : ℂ) *
            v (windowBlock a R k, α) else 0‖ ^ 2 := by
      intro j
      rw [localComparison_K_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hβ0, mul_pow]
      exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hβ0 hβ1)
    calc _ ≤ ∑ j : Fin (2 * R + 1), ‖∑ k, if localComparison_adj j k then
          ((localComparison_cut R k - localComparison_cut R j : ℝ) : ℂ) *
            v (windowBlock a R k, α) else 0‖ ^ 2 := Finset.sum_le_sum fun j _ => hterm j
      _ ≤ 4 * (1 / (R : ℝ)) ^ 2 * ∑ k : Fin (2 * R + 1), ‖v (windowBlock a R k, α)‖ ^ 2 := hS
      _ ≤ η ^ 2 * ∑ b : Fin L, ‖v (b, α)‖ ^ 2 :=
        mul_le_mul hηR hsub (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right, Finset.mul_sum]
  exact Finset.sum_le_sum fun α _ => hper α

/-- Geometric resolvent identity `G₁ (H₁ χ - χ H₂) G₂ = χ G₂ - G₁ χ`, from
`(H_i - z) G_i = G_i (H_i - z) = 1`. -/
private lemma localComparison_geom {n₁ n₂ : Type*} [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] {H₁ : Matrix n₁ n₁ ℂ} {H₂ : Matrix n₂ n₂ ℂ} (h₁ : H₁.IsHermitian)
    (h₂ : H₂.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (χ : Matrix n₁ n₂ ℂ) :
    resolventMat H₁ z * (H₁ * χ - χ * H₂) * resolventMat H₂ z =
      χ * resolventMat H₂ z - resolventMat H₁ z * χ := by
  have hl₁ : resolventMat H₁ z * (H₁ - z • (1 : Matrix n₁ n₁ ℂ)) = 1 :=
    mul_eq_one_comm.mp (sub_smul_mul_resolventMat h₁ hz)
  have hr₂ : (H₂ - z • (1 : Matrix n₂ n₂ ℂ)) * resolventMat H₂ z = 1 :=
    sub_smul_mul_resolventMat h₂ hz
  have hK : H₁ * χ - χ * H₂ = (H₁ - z • (1 : Matrix n₁ n₁ ℂ)) * χ -
      χ * (H₂ - z • (1 : Matrix n₂ n₂ ℂ)) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
    abel
  have key : ∀ (G₁ A : Matrix n₁ n₁ ℂ) (B G₂ : Matrix n₂ n₂ ℂ),
      G₁ * (A * χ - χ * B) * G₂ = (G₁ * A) * χ * G₂ - G₁ * χ * (B * G₂) := by
    intros
    rw [Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  calc resolventMat H₁ z * (H₁ * χ - χ * H₂) * resolventMat H₂ z
      = (resolventMat H₁ z * (H₁ - z • (1 : Matrix n₁ n₁ ℂ))) * χ * resolventMat H₂ z -
        resolventMat H₁ z * χ * ((H₂ - z • (1 : Matrix n₂ n₂ ℂ)) * resolventMat H₂ z) := by
        rw [hK]; exact key _ _ _ _
    _ = χ * resolventMat H₂ z - resolventMat H₁ z * χ := by
        rw [hl₁, hr₂, Matrix.one_mul, Matrix.mul_one]

/-- `u* M* u` is the complex conjugate of `u* M u`. -/
private lemma localComparison_dot_conjTranspose {n : Type*} [Fintype n] (M : Matrix n n ℂ)
    (u : n → ℂ) : star u ⬝ᵥ (Mᴴ *ᵥ u) = star (star u ⬝ᵥ (M *ᵥ u)) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star]

/-- The sum of squares of the entries of `G u` for a matrix with `G* G = (G - G*) / (2 i η)`. -/
private lemma localComparison_sumsq_eq {n : Type*} [Fintype n] (G : Matrix n n ℂ) {η : ℝ}
    (hη : η ≠ 0) (h : Gᴴ * G = ((2 * η * Complex.I)⁻¹ : ℂ) • (G - Gᴴ)) (u : n → ℂ) :
    ∑ i, ‖(G *ᵥ u) i‖ ^ 2 = (star u ⬝ᵥ (G *ᵥ u)).im / η := by
  have h1 : star (G *ᵥ u) ⬝ᵥ (G *ᵥ u) = star u ⬝ᵥ ((Gᴴ * G) *ᵥ u) := by
    rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec u Gᴴ G,
      Matrix.dotProduct_mulVec (star u) Gᴴ]
  have h2 : star (G *ᵥ u) ⬝ᵥ (G *ᵥ u) = ((∑ i, ‖(G *ᵥ u) i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  have h3 : star u ⬝ᵥ ((Gᴴ * G) *ᵥ u) = ((2 * η * Complex.I)⁻¹ : ℂ) *
      (star u ⬝ᵥ (G *ᵥ u) - star (star u ⬝ᵥ (G *ᵥ u))) := by
    rw [h, Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul, dotProduct_sub,
      localComparison_dot_conjTranspose, smul_eq_mul]
  have h4 : ∀ w : ℂ, w - star w = ((2 * w.im : ℝ) : ℂ) * Complex.I := fun w => by
    apply Complex.ext <;> simp [two_mul]
  apply Complex.ofReal_injective
  rw [← h2, h1, h3, h4]
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  push_cast
  field_simp

/-- The conjugate transpose of the resolvent is the resolvent at `conj z`. -/
private lemma localComparison_resolventMat_conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : ℂ) :
    (resolventMat A z)ᴴ = resolventMat A (star z) := by
  unfold resolventMat
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, hA.eq,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one]

/-- Ward's identity for `G` and `G*` as sums of squares, `‖G u‖² = ‖G* u‖² = Im ⟨u, G u⟩ / η`. -/
private lemma localComparison_ward_vec {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (u : n → ℂ) :
    ∑ i, ‖(resolventMat A z *ᵥ u) i‖ ^ 2 = (star u ⬝ᵥ (resolventMat A z *ᵥ u)).im / z.im ∧
    ∑ i, ‖((resolventMat A z)ᴴ *ᵥ u) i‖ ^ 2 = (star u ⬝ᵥ (resolventMat A z *ᵥ u)).im / z.im := by
  refine ⟨localComparison_sumsq_eq _ hz (ward_matrix hA hz) u, ?_⟩
  have hz' : (star z).im ≠ 0 := by simpa using hz
  have h := localComparison_sumsq_eq (resolventMat A (star z)) hz' (ward_matrix hA hz') u
  rw [← localComparison_resolventMat_conjTranspose hA z] at h
  rw [h, localComparison_dot_conjTranspose]
  simp

/-- Cauchy–Schwarz for the pairing `⟨x, y⟩ = x* y`, with explicit sums. -/
private lemma localComparison_cauchy {n : Type*} [Fintype n] (x y : n → ℂ) :
    ‖star x ⬝ᵥ y‖ ^ 2 ≤ (∑ i, ‖x i‖ ^ 2) * ∑ i, ‖y i‖ ^ 2 := by
  have h1 : ‖star x ⬝ᵥ y‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp
  calc ‖star x ⬝ᵥ y‖ ^ 2 ≤ (∑ i, ‖x i‖ * ‖y i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- The comparison of two resolvents through a rectangular intertwiner `χ`: if
`‖(H₁ χ - χ H₂) v‖ ≤ η ‖v‖`, `χ` carries `u₂` to `u₁` and `χ*` carries `u₁` to `u₂`, then the
numbers `x_i = Im ⟨u_i, G_i u_i⟩` are nonnegative and satisfy `(x₂ - x₁)² ≤ x₁ x₂`
(Cauchy–Schwarz and Ward's identity in the proof of Theorem 4.1 [uv:thm:smooth-cutoff]). -/
private lemma localComparison_abstract {n₁ n₂ : Type*} [Fintype n₁] [DecidableEq n₁]
    [Fintype n₂] [DecidableEq n₂] {H₁ : Matrix n₁ n₁ ℂ} {H₂ : Matrix n₂ n₂ ℂ}
    (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian) {z : ℂ} (hz : 0 < z.im) (χ : Matrix n₁ n₂ ℂ)
    (hK : ∀ v : n₂ → ℂ, ∑ i, ‖((H₁ * χ - χ * H₂) *ᵥ v) i‖ ^ 2 ≤ z.im ^ 2 * ∑ j, ‖v j‖ ^ 2)
    (u₁ : n₁ → ℂ) (u₂ : n₂ → ℂ) (hu₁ : χᴴ *ᵥ u₁ = u₂) (hu₂ : χ *ᵥ u₂ = u₁) :
    0 ≤ (star u₁ ⬝ᵥ (resolventMat H₁ z *ᵥ u₁)).im ∧
      0 ≤ (star u₂ ⬝ᵥ (resolventMat H₂ z *ᵥ u₂)).im ∧
      ((star u₂ ⬝ᵥ (resolventMat H₂ z *ᵥ u₂)).im - (star u₁ ⬝ᵥ (resolventMat H₁ z *ᵥ u₁)).im) ^ 2 ≤
        (star u₁ ⬝ᵥ (resolventMat H₁ z *ᵥ u₁)).im * (star u₂ ⬝ᵥ (resolventMat H₂ z *ᵥ u₂)).im := by
  have hη : z.im ≠ 0 := hz.ne'
  obtain ⟨-, hW1⟩ := localComparison_ward_vec h₁ hη u₁
  obtain ⟨hW2, -⟩ := localComparison_ward_vec h₂ hη u₂
  set x₁ := (star u₁ ⬝ᵥ (resolventMat H₁ z *ᵥ u₁)).im with hx₁
  set x₂ := (star u₂ ⬝ᵥ (resolventMat H₂ z *ᵥ u₂)).im with hx₂
  set X := star u₁ ⬝ᵥ ((χ * resolventMat H₂ z - resolventMat H₁ z * χ) *ᵥ u₂) with hX
  have hx₁0 : 0 ≤ x₁ := by
    have : 0 ≤ x₁ / z.im := hW1 ▸ Finset.sum_nonneg fun i _ => by positivity
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hz)
  have hx₂0 : 0 ≤ x₂ := by
    have : 0 ≤ x₂ / z.im := hW2 ▸ Finset.sum_nonneg fun i _ => by positivity
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hz)
  have hX1 : X = star u₂ ⬝ᵥ (resolventMat H₂ z *ᵥ u₂) - star u₁ ⬝ᵥ (resolventMat H₁ z *ᵥ u₁) := by
    have e1 : star u₁ ⬝ᵥ ((χ * resolventMat H₂ z) *ᵥ u₂) =
        star u₂ ⬝ᵥ (resolventMat H₂ z *ᵥ u₂) := by
      rw [← Matrix.mulVec_mulVec u₂ χ, Matrix.dotProduct_mulVec, ← hu₁, Matrix.star_mulVec,
        Matrix.conjTranspose_conjTranspose]
    have e2 : star u₁ ⬝ᵥ ((resolventMat H₁ z * χ) *ᵥ u₂) =
        star u₁ ⬝ᵥ (resolventMat H₁ z *ᵥ u₁) := by
      rw [← Matrix.mulVec_mulVec u₂, hu₂]
    rw [hX, Matrix.sub_mulVec, dotProduct_sub, e1, e2]
  have hX2 : X = star ((resolventMat H₁ z)ᴴ *ᵥ u₁) ⬝ᵥ
      ((H₁ * χ - χ * H₂) *ᵥ (resolventMat H₂ z *ᵥ u₂)) := by
    rw [hX, ← localComparison_geom h₁ h₂ hη χ, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec]
  have hnorm := localComparison_cauchy ((resolventMat H₁ z)ᴴ *ᵥ u₁)
    ((H₁ * χ - χ * H₂) *ᵥ (resolventMat H₂ z *ᵥ u₂))
  rw [← hX2, hW1] at hnorm
  have hKb := hK (resolventMat H₂ z *ᵥ u₂)
  rw [hW2] at hKb
  have hXle : ‖X‖ ^ 2 ≤ x₁ * x₂ := by
    refine hnorm.trans ?_
    calc x₁ / z.im * ∑ i, ‖((H₁ * χ - χ * H₂) *ᵥ (resolventMat H₂ z *ᵥ u₂)) i‖ ^ 2
        ≤ x₁ / z.im * (z.im ^ 2 * (x₂ / z.im)) :=
          mul_le_mul_of_nonneg_left hKb (div_nonneg hx₁0 hz.le)
      _ = x₁ * x₂ := by field_simp
  have him : X.im = x₂ - x₁ := by rw [hX1]; simp [hx₁, hx₂]
  refine ⟨hx₁0, hx₂0, ?_⟩
  rw [← him]
  calc X.im ^ 2 = |X.im| ^ 2 := (sq_abs _).symm
    _ ≤ ‖X‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm X) 2
    _ ≤ x₁ * x₂ := hXle

/-- `qform M u` is the real part of `u* M u`. -/
private lemma localComparison_qform_eq {m : Type*} [Fintype m] (M : Matrix m m ℂ) (u : m → ℂ) :
    qform M u = (star u ⬝ᵥ (M *ᵥ u)).re := by
  unfold qform
  congr 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]

/-- The quadratic form of `Im B` is the imaginary part of `u* B u`. -/
private lemma localComparison_qform_matIm {m : Type*} [Fintype m] (B : Matrix m m ℂ)
    (u : m → ℂ) : qform (matIm B) u = (star u ⬝ᵥ (B *ᵥ u)).im := by
  rw [localComparison_qform_eq, matIm, Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul,
    dotProduct_sub, localComparison_dot_conjTranspose, smul_eq_mul]
  set s := star u ⬝ᵥ (B *ᵥ u) with hs
  have h4 : s - star s = ((2 * s.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [two_mul]
  rw [h4]
  have : ((2 : ℂ) * Complex.I)⁻¹ * (((2 * s.im : ℝ) : ℂ) * Complex.I) = (s.im : ℂ) := by
    push_cast
    field_simp
  rw [this, Complex.ofReal_re]

/-- Embedding of `u ∈ ℂ^W` at block `b` of `ℂ^L ⊗ ℂ^W`. -/
private def localComparison_embed {W L : ℕ} (b : Fin L) (u : Fin W → ℂ) : Fin L × Fin W → ℂ :=
  fun p => if p.1 = b then u p.2 else 0

/-- The quadratic form of an embedded vector is the quadratic form of the diagonal block. -/
private lemma localComparison_dot_embed {W L : ℕ}
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (b : Fin L) (u : Fin W → ℂ) :
    star (localComparison_embed b u) ⬝ᵥ (M *ᵥ localComparison_embed b u) =
      star u ⬝ᵥ (blockOf M b b *ᵥ u) := by
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, localComparison_embed,
    blockOf, Matrix.mulVec, Matrix.of_apply]
  simp [apply_ite (starRingEnd ℂ)]

/-- `χ` carries the embedding of `u` at block `a` to its embedding at the window centre. -/
private lemma localComparison_chi_embed {W L : ℕ} (a : Fin L) (R : ℕ) (hR : 1 ≤ R)
    (hRL : 2 * R + 1 ≤ L) (u : Fin W → ℂ) :
    localComparison_chi a R *ᵥ localComparison_embed a u =
      localComparison_embed (windowCenter R) u := by
  funext ⟨k, γ⟩
  rw [localComparison_chi_mulVec]
  by_cases hk : k = windowCenter R
  · subst hk
    simp [localComparison_embed, localComparison_cut_center hR, windowBlock_windowCenter]
  · have : windowBlock a R k ≠ a := by
      intro h
      apply hk
      apply windowBlock_injective a R hRL
      rw [h, windowBlock_windowCenter]
    simp [localComparison_embed, hk, this]

/-- `χ*` carries the embedding of `u` at the window centre to its embedding at block `a`. -/
private lemma localComparison_chiT_embed {W L : ℕ} (a : Fin L) (R : ℕ) (hR : 1 ≤ R)
    (u : Fin W → ℂ) :
    (localComparison_chi a R)ᴴ *ᵥ localComparison_embed (windowCenter R) u =
      localComparison_embed a u := by
  funext ⟨b, β⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    localComparison_chi, Matrix.of_apply, localComparison_embed]
  simp [apply_ite (starRingEnd ℂ), ite_and, localComparison_cut_center hR,
    windowBlock_windowCenter, eq_comm]

/-- Both imaginary parts in (4.1) [uv:eq:smooth-comparison] are nonnegative and
`(x_L - x_I)² ≤ x_I x_L`. -/
private lemma localComparison_main (g : ℝ) (hg : 0 ≤ g) {W L : ℕ}
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ a, (V a).IsHermitian) (a : Fin L) (R : ℕ)
    (hR : 1 ≤ R) (hRL : 2 * R + 1 ≤ L) (z : ℂ) (hz : 0 < z.im) (hηR : 2 ≤ z.im * R)
    (u : Fin W → ℂ) :
    0 ≤ qform (matIm (blockOf (resolventMat (Hdet g (windowBlocks V a R)) z)
          (windowCenter R) (windowCenter R))) u ∧
      0 ≤ qform (matIm (blockOf (resolventMat (Hdet g V) z) a a)) u ∧
      (qform (matIm (blockOf (resolventMat (Hdet g V) z) a a)) u -
        qform (matIm (blockOf (resolventMat (Hdet g (windowBlocks V a R)) z)
          (windowCenter R) (windowCenter R))) u) ^ 2 ≤
      qform (matIm (blockOf (resolventMat (Hdet g (windowBlocks V a R)) z)
          (windowCenter R) (windowCenter R))) u *
        qform (matIm (blockOf (resolventMat (Hdet g V) z) a a)) u := by
  have hV' : ∀ j, (windowBlocks V a R j).IsHermitian := fun j => hV _
  have h := localComparison_abstract (Hdet_isHermitian g hV') (Hdet_isHermitian g hV) hz
    (localComparison_chi a R)
    (fun v => localComparison_K_bound g hg V a R hR hRL z.im hηR v)
    (localComparison_embed (windowCenter R) u) (localComparison_embed a u)
    (localComparison_chiT_embed a R hR u) (localComparison_chi_embed a R hR hRL u)
  simpa only [localComparison_qform_matIm, localComparison_dot_embed] using h

/-- The quadratic form of `Im B` at a basis vector is the imaginary part of the diagonal entry. -/
private lemma localComparison_qform_single {W : ℕ} (B : Matrix (Fin W) (Fin W) ℂ) (α : Fin W) :
    qform (matIm B) (Pi.single α 1) = (B α α).im := by
  rw [localComparison_qform_matIm]
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

/-- Theorem 4.1 [uv:thm:smooth-cutoff], (4.1) [uv:eq:smooth-comparison] with `C = 3`, as
quadratic forms. -/
theorem im_resolvent_window_comparison (g : ℝ) (hg : 0 ≤ g) {W L : ℕ}
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ a, (V a).IsHermitian) (a : Fin L) (R : ℕ)
    (hR : 1 ≤ R) (hRL : 2 * R + 1 < L) (z : ℂ) (hz : 0 < z.im) (hηR : 2 ≤ z.im * R)
    (u : Fin W → ℂ) :
    qform (matIm (blockOf (resolventMat (Hdet g V) z) a a)) u ≤
        3 * qform (matIm (blockOf (resolventMat (Hdet g (windowBlocks V a R)) z)
          (windowCenter R) (windowCenter R))) u ∧
      qform (matIm (blockOf (resolventMat (Hdet g (windowBlocks V a R)) z)
          (windowCenter R) (windowCenter R))) u ≤
        3 * qform (matIm (blockOf (resolventMat (Hdet g V) z) a a)) u := by
  obtain ⟨h1, h2, h3⟩ := localComparison_main g hg V hV a R hR hRL.le z hz hηR u
  set xI := qform (matIm (blockOf (resolventMat (Hdet g (windowBlocks V a R)) z)
          (windowCenter R) (windowCenter R))) u
  set xL := qform (matIm (blockOf (resolventMat (Hdet g V) z) a a)) u
  constructor
  · by_contra hc
    rw [not_le] at hc
    nlinarith [sq_nonneg xI, mul_pos (by linarith : 0 < xL) (by linarith : 0 < xL - 3 * xI)]
  · by_contra hc
    rw [not_le] at hc
    nlinarith [sq_nonneg xL, mul_pos (by linarith : 0 < xI) (by linarith : 0 < xI - 3 * xL)]

/-- Diagonal entries of (4.1) [uv:eq:smooth-comparison]. -/
theorem im_resolvent_diag_le_window (g : ℝ) (hg : 0 ≤ g) {W L : ℕ}
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ a, (V a).IsHermitian) (a : Fin L) (R : ℕ)
    (hR : 1 ≤ R) (hRL : 2 * R + 1 < L) (z : ℂ) (hz : 0 < z.im) (hηR : 2 ≤ z.im * R)
    (α : Fin W) :
    (resolventMat (Hdet g V) z (a, α) (a, α)).im ≤
      3 * (resolventMat (Hdet g (windowBlocks V a R)) z (windowCenter R, α)
        (windowCenter R, α)).im := by
  have h := (im_resolvent_window_comparison g hg V hV a R hR hRL z hz hηR (Pi.single α 1)).1
  simpa only [localComparison_qform_single, blockOf, Matrix.of_apply] using h

end LSBA
