import Mathlib

/-!
# Localization length

Cyclic intervals of `ℤ_N` in the coordinate order (1.1) [eq:blocks] and the localization length of
Definition 1.1 [def:length], (1.6) [eq:length].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Cyclic interval `{x, …, x+r-1} ⊆ ℤ_N`. -/
def cycInterval (N : ℕ) (x : Fin N) (r : ℕ) : Finset (Fin N) :=
  univ.filter fun i => (i.val + N - x.val) % N < r

/-- Localization length of a mass profile `p : ℤ_N → ℝ`, (1.6) [eq:length]; the clause
`r = N` makes the value lie in `[1, N]` for every profile when `0 < N`. -/
def ellMass (N : ℕ) (p : Fin N → ℝ) : ℕ :=
  sInf {r : ℕ | 1 ≤ r ∧ r ≤ N ∧
    (r = N ∨ ∃ x : Fin N, (1 : ℝ) / 2 ≤ ∑ i ∈ cycInterval N x r, p i)}

/-- Localization length of a profile on `Fin L × Fin W`, through the coordinates (1.1) [eq:blocks].
-/
def ellProf (W L : ℕ) (p : Fin L × Fin W → ℝ) : ℕ :=
  ellMass (L * W) fun i => p (finProdFinEquiv.symm i)

/-- `ℓ(ψ)` of Definition 1.1 [def:length] for `ψ ∈ ℂ^L ⊗ ℂ^W`. -/
def ell (W L : ℕ) (ψ : Fin L × Fin W → ℂ) : ℕ := ellProf W L fun x => ‖ψ x‖ ^ 2

theorem card_cycInterval (N : ℕ) (x : Fin N) (r : ℕ) (hr : r ≤ N) :
    (cycInterval N x r).card = r := by
  have hN : 0 < N := x.pos
  have hx := x.isLt
  have key : (cycInterval N x r).card = (Finset.range r).card := by
    refine Finset.card_bij' (fun i _ => (i.val + N - x.val) % N)
      (fun k _ => (⟨(k + x.val) % N, Nat.mod_lt _ hN⟩ : Fin N)) ?_ ?_ ?_ ?_
    · intro i hi
      simpa [cycInterval] using hi
    · intro k hk
      have hkr : k < r := by simpa using hk
      have hkN : k < N := lt_of_lt_of_le hkr hr
      simp only [cycInterval, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : k + x.val < N
      · rw [Nat.mod_eq_of_lt h]
        have : k + x.val + N - x.val = k + N := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hkN]
        exact hkr
      · have h1 : (k + x.val) % N = k + x.val - N := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [h1]
        have : k + x.val - N + N - x.val = k := by omega
        rw [this, Nat.mod_eq_of_lt hkN]
        exact hkr
    · intro i _
      apply Fin.ext
      have hi' := i.isLt
      change ((i.val + N - x.val) % N + x.val) % N = i.val
      by_cases h : x.val ≤ i.val
      · have h2 : i.val + N - x.val = (i.val - x.val) + N := by omega
        have h3 : i.val - x.val < N := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt h3]
        have h4 : i.val - x.val + x.val = i.val := by omega
        rw [h4, Nat.mod_eq_of_lt hi']
      · have h3 : i.val + N - x.val < N := by omega
        rw [Nat.mod_eq_of_lt h3]
        have h4 : i.val + N - x.val + x.val = i.val + N := by omega
        rw [h4, Nat.add_mod_right, Nat.mod_eq_of_lt hi']
    · intro k hk
      have hkr : k < r := by simpa using hk
      have hkN : k < N := lt_of_lt_of_le hkr hr
      change ((k + x.val) % N + N - x.val) % N = k
      by_cases h : k + x.val < N
      · rw [Nat.mod_eq_of_lt h]
        have : k + x.val + N - x.val = k + N := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hkN]
      · have h1 : (k + x.val) % N = k + x.val - N := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [h1]
        have : k + x.val - N + N - x.val = k := by omega
        rw [this, Nat.mod_eq_of_lt hkN]
  rw [key, Finset.card_range]

private lemma cycInterval_self (N : ℕ) (x : Fin N) : cycInterval N x N = univ := by
  apply Finset.eq_univ_of_card
  rw [card_cycInterval N x N le_rfl, Fintype.card_fin]

private lemma ellMass_mem {N : ℕ} (hN : 0 < N) (p : Fin N → ℝ) :
    ellMass N p ∈ {r : ℕ | 1 ≤ r ∧ r ≤ N ∧
      (r = N ∨ ∃ x : Fin N, (1 : ℝ) / 2 ≤ ∑ i ∈ cycInterval N x r, p i)} :=
  Nat.sInf_mem (s := {r : ℕ | 1 ≤ r ∧ r ≤ N ∧
      (r = N ∨ ∃ x : Fin N, (1 : ℝ) / 2 ≤ ∑ i ∈ cycInterval N x r, p i)})
    ⟨N, hN, le_rfl, Or.inl rfl⟩

theorem one_le_ellMass {N : ℕ} (hN : 0 < N) (p : Fin N → ℝ) : 1 ≤ ellMass N p :=
  (ellMass_mem hN p).1

theorem ellMass_le (N : ℕ) (p : Fin N → ℝ) : ellMass N p ≤ N := by
  rcases Nat.eq_zero_or_pos N with h | hN
  · subst h
    have : {r : ℕ | 1 ≤ r ∧ r ≤ 0 ∧
        (r = 0 ∨ ∃ x : Fin 0, (1 : ℝ) / 2 ≤ ∑ i ∈ cycInterval 0 x r, p i)} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      omega
    unfold ellMass
    rw [this, Nat.sInf_empty]
  · exact (ellMass_mem hN p).2.1

theorem ellMass_le_of_mass {N : ℕ} (p : Fin N → ℝ) (x : Fin N) {r : ℕ} (h1 : 1 ≤ r)
    (hN : r ≤ N) (h : (1 : ℝ) / 2 ≤ ∑ i ∈ cycInterval N x r, p i) : ellMass N p ≤ r := by
  exact Nat.sInf_le ⟨h1, hN, Or.inr ⟨x, h⟩⟩

theorem exists_mass_ellMass {N : ℕ} (hN : 0 < N) (p : Fin N → ℝ)
    (hp : (1 : ℝ) / 2 ≤ ∑ i, p i) :
    ∃ x : Fin N, (1 : ℝ) / 2 ≤ ∑ i ∈ cycInterval N x (ellMass N p), p i := by
  rcases (ellMass_mem hN p).2.2 with h | h
  · refine ⟨⟨0, hN⟩, ?_⟩
    rw [h, cycInterval_self]
    exact hp
  · exact h

theorem isClosed_setOf_ellMass_le (N r : ℕ) : IsClosed {p : Fin N → ℝ | ellMass N p ≤ r} := by
  by_cases hr : N ≤ r
  · have : {p : Fin N → ℝ | ellMass N p ≤ r} = Set.univ :=
      Set.eq_univ_of_forall fun p => (ellMass_le N p).trans hr
    rw [this]
    exact isClosed_univ
  · have hr' : r < N := not_le.mp hr
    have hN : 0 < N := by omega
    have : {p : Fin N → ℝ | ellMass N p ≤ r} = ⋃ r' ∈ Finset.Icc 1 r, ⋃ x : Fin N,
        {p : Fin N → ℝ | (1 : ℝ) / 2 ≤ ∑ i ∈ cycInterval N x r', p i} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_Icc, exists_prop]
      constructor
      · intro h
        obtain ⟨h1, h2, h3⟩ := ellMass_mem hN p
        rcases h3 with h3 | ⟨x, hx⟩
        · omega
        · exact ⟨ellMass N p, ⟨h1, h⟩, x, hx⟩
      · rintro ⟨r', ⟨h1, h2⟩, x, hx⟩
        exact (ellMass_le_of_mass p x h1 (by omega) hx).trans h2
    rw [this]
    refine isClosed_biUnion_finset fun r' _ => isClosed_iUnion_of_finite fun x => ?_
    exact isClosed_le continuous_const (continuous_finsetSum _ fun i _ => continuous_apply i)

theorem ell_congr {W L : ℕ} {ψ φ : Fin L × Fin W → ℂ} (h : ∀ x, ‖ψ x‖ = ‖φ x‖) :
    ell W L ψ = ell W L φ := by
  have : (fun x => ‖ψ x‖ ^ 2) = fun x => ‖φ x‖ ^ 2 := funext fun x => by rw [h x]
  unfold ell
  rw [this]

theorem ell_smul_of_norm_eq_one {W L : ℕ} (ψ : Fin L × Fin W → ℂ) {c : ℂ} (hc : ‖c‖ = 1) :
    ell W L (c • ψ) = ell W L ψ :=
  ell_congr fun x => by simp [hc]

end LSBA
