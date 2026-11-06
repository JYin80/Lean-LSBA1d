import Mathlib

/-!
# The Ward projection

The projection `𝒬_u F(a) = F(a) − h(a₀) Π_{j ≥ 1} θ_u(a₀ − a_j)` before (C.33)
[fo:eq:ward-projection], the one-leg operator `Θ`, and the commutator identity behind (C.35)
[fo:eq:projected-error-equation], stated for any symmetric kernel with row sums `(1 − u)⁻¹`
and any profile `θ` with the derivative identity; the commutator is that of (6.4)
[gc:eq:commutator].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Signed row `h(c) = Σ_{b : b₀ = c} F(b)`. -/
def rowSum {L n : ℕ} (F : (Fin (n + 1) → Fin L) → ℂ) (c : Fin L) : ℂ :=
  ∑ b : Fin (n + 1) → Fin L, if b 0 = c then F b else 0

/-- The projection `𝒬_u F(a) = F(a) - h(a₀) Π_{j ≥ 1} θ_u(a₀ - a_j)` before (C.33)
[fo:eq:ward-projection]. -/
def projQ {L n : ℕ} (θ : Fin L → ℝ) (F : (Fin (n + 1) → Fin L) → ℂ) (a : Fin (n + 1) → Fin L) : ℂ :=
  F a - rowSum F (a 0) * ∏ j : Fin n, ((θ (a 0 - a j.succ) : ℝ) : ℂ)

/-- `Θ F(a) = Σ_j Σ_c K(a_j, c) F(a[j ↦ c])` with one leg kernel `K` (alternating words). -/
def thetaK {L n : ℕ} (K : Matrix (Fin L) (Fin L) ℝ) (F : (Fin n → Fin L) → ℂ) (a : Fin n → Fin L) :
    ℂ :=
  ∑ j : Fin n, ∑ c : Fin L, ((K (a j) c : ℝ) : ℂ) * F (Function.update a j c)

/-- Exchanging the two values `b j` and `c` of one coordinate permutes the pairs `(b, c)`. -/
private theorem projection_sum_swap {L m : ℕ} (j : Fin m) (Ψ : (Fin m → Fin L) → Fin L → ℂ) :
    ∑ b, ∑ c, Ψ b c = ∑ b, ∑ c, Ψ (Function.update b j c) (b j) := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let e : (Fin m → Fin L) × Fin L ≃ (Fin m → Fin L) × Fin L :=
    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
      left_inv := by rintro ⟨b, c⟩; simp
      right_inv := by rintro ⟨b, c⟩; simp }
  exact (Equiv.sum_comp e (fun p => Ψ p.1 p.2)).symm

/-- The row sum of `Θ F`: the leg `0` moves the row index through `K`, and each other leg
contributes the column sum `(1 - u)⁻¹` of `K` times the row sum of `F`. -/
private theorem projection_rowSum_thetaK {L n : ℕ} (K : Matrix (Fin L) (Fin L) ℝ) {u : ℝ}
    (hKsym : ∀ x y, K x y = K y x) (hrow : ∀ x, ∑ y, K x y = (1 - u)⁻¹)
    (F : (Fin (n + 1) → Fin L) → ℂ) (c₀ : Fin L) :
    rowSum (thetaK K F) c₀ = ∑ c, ((K c₀ c : ℝ) : ℂ) * rowSum F c +
      (n : ℂ) * (((1 - u)⁻¹ : ℝ) : ℂ) * rowSum F c₀ := by
  unfold rowSum thetaK
  have h1 : ∀ b : Fin (n + 1) → Fin L,
      (if b 0 = c₀ then ∑ j : Fin (n + 1), ∑ c, ((K (b j) c : ℝ) : ℂ) * F (Function.update b j c)
        else 0) =
      ∑ j : Fin (n + 1), ∑ c, (if b 0 = c₀ then
        ((K (b j) c : ℝ) : ℂ) * F (Function.update b j c) else 0) := by
    intro b; split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_comm, Fin.sum_univ_succ]
  have h0 : ∑ b : Fin (n + 1) → Fin L, ∑ c, (if b 0 = c₀ then
        ((K (b 0) c : ℝ) : ℂ) * F (Function.update b 0 c) else 0) =
      ∑ c, ((K c₀ c : ℝ) : ℂ) * ∑ b : Fin (n + 1) → Fin L, if b 0 = c then F b else 0 := by
    rw [projection_sum_swap 0]
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [mul_ite]
  have hj : ∀ k : Fin n, ∑ b : Fin (n + 1) → Fin L, ∑ c, (if b 0 = c₀ then
        ((K (b k.succ) c : ℝ) : ℂ) * F (Function.update b k.succ c) else 0) =
      (((1 - u)⁻¹ : ℝ) : ℂ) * ∑ b : Fin (n + 1) → Fin L, if b 0 = c₀ then F b else 0 := by
    intro k
    rw [projection_sum_swap k.succ]
    have e1 : ∀ (b : Fin (n + 1) → Fin L) (c : Fin L),
        (if (Function.update b k.succ c) 0 = c₀ then
          ((K ((Function.update b k.succ c) k.succ) (b k.succ) : ℝ) : ℂ) *
            F (Function.update (Function.update b k.succ c) k.succ (b k.succ)) else 0) =
        if b 0 = c₀ then ((K c (b k.succ) : ℝ) : ℂ) * F b else 0 := by
      intro b c
      simp [Function.update_of_ne (Fin.succ_ne_zero k).symm]
    simp_rw [e1]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [← Finset.sum_mul, ← Complex.ofReal_sum]
      have : ∑ c, K c (b k.succ) = (1 - u)⁻¹ := by
        simp_rw [hKsym _ (b k.succ)]; exact hrow _
      rw [this, mul_comm]
    · simp
  rw [h0, Finset.sum_congr rfl fun k _ => hj k]
  simp [mul_assoc]

/-- Replacing the factor `k` of a product `Π_i g(a₀ - b_i)` by the value at `c`. -/
private theorem projection_prod_update {L n : ℕ} (g : Fin L → ℝ) (a₀ : Fin L)
    (b : Fin n → Fin L) (k : Fin n) (c : Fin L) :
    ∏ i : Fin n, g (a₀ - Function.update b k c i) =
      g (a₀ - c) * ∏ i ∈ Finset.univ.erase k, g (a₀ - b i) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- The commutator identity behind (C.35) [fo:eq:projected-error-equation]:
`∂_u 𝒬_u F + 𝒬_u Θ F - Θ 𝒬_u F = C_u(h)`, with `C_u` the commutator of (6.4)
[gc:eq:commutator]. -/
theorem projection_commutator {L n : ℕ} (θ : ℝ → Fin L → ℝ) (K : Matrix (Fin L) (Fin L) ℝ)
    {u : ℝ} (hu : u < 1) (hKsym : ∀ x y, K x y = K y x) (hrow : ∀ x, ∑ y, K x y = (1 - u)⁻¹)
    (hθ : ∀ x y : Fin L, HasDerivAt (fun r => θ r (x - y))
      (∑ c, K y c * θ u (x - c) - (1 - u)⁻¹ * θ u (x - y)) u)
    (F : (Fin (n + 1) → Fin L) → ℂ) (a : Fin (n + 1) → Fin L) :
    ∃ Qd : ℂ, HasDerivAt (fun r => projQ (θ r) F a) Qd u ∧
      Qd + projQ (θ u) (thetaK K F) a - thetaK K (projQ (θ u) F) a =
        ∑ c : Fin L, ((K (a 0) c : ℝ) : ℂ) * rowSum F c *
          (∏ j : Fin n, ((θ u (c - a j.succ) : ℝ) : ℂ) -
            ∏ j : Fin n, ((θ u (a 0 - a j.succ) : ℝ) : ℂ)) := by
  have _ := hu
  set b : Fin n → Fin L := fun i => a i.succ with hb
  -- the derivative of the real product
  have hprod : HasDerivAt (fun r => ∏ i : Fin n, θ r (a 0 - b i))
      (∑ k : Fin n, (∏ i ∈ Finset.univ.erase k, θ u (a 0 - b i)) *
        (∑ c, K (b k) c * θ u (a 0 - c) - (1 - u)⁻¹ * θ u (a 0 - b k))) u := by
    have := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin n)))
      (f := fun i r => θ r (a 0 - b i)) (x := u) (fun i _ => hθ (a 0) (b i))
    simpa [smul_eq_mul] using this
  set D : ℝ := ∑ k : Fin n, (∏ i ∈ Finset.univ.erase k, θ u (a 0 - b i)) *
        (∑ c, K (b k) c * θ u (a 0 - c) - (1 - u)⁻¹ * θ u (a 0 - b k)) with hD
  have hC : HasDerivAt (fun r => projQ (θ r) F a) (-(rowSum F (a 0) * (D : ℂ))) u := by
    have h1 := (hprod.ofReal_comp.const_mul (rowSum F (a 0))).const_sub (F a)
    have h2 : (fun r => projQ (θ r) F a) =
        fun r => F a - rowSum F (a 0) * (((∏ i : Fin n, θ r (a 0 - b i) : ℝ)) : ℂ) := by
      funext r; simp [projQ, hb, Complex.ofReal_prod]
    rw [h2]; exact h1
  refine ⟨_, hC, ?_⟩
  -- notation
  set pr : ℂ := ∏ j : Fin n, ((θ u (a 0 - a j.succ) : ℝ) : ℂ) with hpr
  set T : ℂ := ∑ k : Fin n, ∑ c, ((K (b k) c : ℝ) : ℂ) *
    ∏ i : Fin n, ((θ u (a 0 - Function.update b k c i) : ℝ) : ℂ) with hT
  set S0 : ℂ := ∑ c : Fin L, ((K (a 0) c : ℝ) : ℂ) * rowSum F c *
    ∏ j : Fin n, ((θ u (c - a j.succ) : ℝ) : ℂ) with hS0
  set KH : ℂ := ∑ c : Fin L, ((K (a 0) c : ℝ) : ℂ) * rowSum F c with hKH
  -- (C) the derivative
  have hDc : (D : ℂ) = T - (n : ℂ) * (((1 - u)⁻¹ : ℝ) : ℂ) * pr := by
    have hreal : D = ∑ k : Fin n, (∑ c, K (b k) c *
          ∏ i : Fin n, θ u (a 0 - Function.update b k c i) -
        (1 - u)⁻¹ * ∏ i : Fin n, θ u (a 0 - b i)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp_rw [projection_prod_update (θ u) (a 0) b k]
      rw [← Finset.mul_prod_erase Finset.univ (fun i => θ u (a 0 - b i)) (Finset.mem_univ k)]
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun c _ => by ring
      · ring
    rw [hreal, hT, hpr]
    push_cast
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [mul_assoc]
  -- (A) `Θ 𝒬 F`
  have hA : thetaK K (projQ (θ u) F) a = thetaK K F a - S0 - rowSum F (a 0) * T := by
    unfold thetaK projQ
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have e0 : ∀ c : Fin L, Function.update a 0 c 0 = c := fun c => Function.update_self ..
    have es : ∀ (c : Fin L) (i : Fin n), Function.update a 0 c i.succ = a i.succ :=
      fun c i => Function.update_of_ne (Fin.succ_ne_zero i) _ _
    have ek0 : ∀ (k : Fin n) (c : Fin L), Function.update a k.succ c 0 = a 0 :=
      fun k c => Function.update_of_ne (Fin.succ_ne_zero k).symm _ _
    have eks : ∀ (k : Fin n) (c : Fin L) (i : Fin n),
        Function.update a k.succ c i.succ = Function.update b k c i := by
      intro k c i
      by_cases hik : i = k
      · subst hik; simp [hb]
      · rw [Function.update_of_ne hik,
          Function.update_of_ne (fun h => hik (Fin.succ_injective _ h))]
    simp only [e0, es, ek0, eks]
    simp only [mul_sub, Finset.sum_sub_distrib, hS0, hT, Finset.mul_sum, mul_assoc, mul_left_comm]
    abel
  -- (B) `𝒬 Θ F`
  have hB : projQ (θ u) (thetaK K F) a = thetaK K F a -
      (KH + (n : ℂ) * (((1 - u)⁻¹ : ℝ) : ℂ) * rowSum F (a 0)) * pr := by
    unfold projQ
    rw [projection_rowSum_thetaK K hKsym hrow F (a 0)]
  -- the commutator
  have hR : ∑ c : Fin L, ((K (a 0) c : ℝ) : ℂ) * rowSum F c *
      (∏ j : Fin n, ((θ u (c - a j.succ) : ℝ) : ℂ) -
        ∏ j : Fin n, ((θ u (a 0 - a j.succ) : ℝ) : ℂ)) = S0 - KH * pr := by
    rw [hS0, hKH, hpr, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hR, hB, hA, hDc]
  ring

end LSBA
