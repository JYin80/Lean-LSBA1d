import LSBA.Model.Basic

/-!
# Uniform stochastic domination

The relation `X ≺ Y` of the definition before (5.22) [gc:eq:one-step-input], uniform over a
deterministic parameter family, with the maximum over labels inside the probability (`PrecMax`), and
its algebra: monotonicity, sums, finite label sets of polynomial size.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Stochastic domination (the definition before (5.22) [gc:eq:one-step-input]) with the maximum
over labels inside the probability, uniform over a deterministic parameter family: the family
`Dom` and the labels are fixed first; for all `ε, D > 0` there is `W₀` such that for `W ≥ W₀` and
every point `p ∈ Dom W`, `ℙ(∃ λ, ‖X_λ‖ > W^ε Y_λ) ≤ W^{-D}`. -/
def PrecMax {ι : Type*} (vol : ι → ℕ) (Dom : ℕ → Set ι) {Λ : ℕ → ι → Type*}
    (X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ) (Y : (W : ℕ) → (p : ι) → Λ W p → ℝ) :
    Prop :=
  ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ p ∈ Dom W,
    μ W (vol p) {ω | ∃ l : Λ W p, (W : ℝ) ^ ε * Y W p l < ‖X W p l ω‖} ≤
      ENNReal.ofReal ((W : ℝ) ^ (-D))

/-- A larger bound. -/
theorem PrecMax.mono {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι} {Λ : ℕ → ι → Type*}
    {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ} {Y Y' : (W : ℕ) → (p : ι) → Λ W p → ℝ}
    (h : PrecMax vol Dom X Y) (hY : ∀ W p, p ∈ Dom W → ∀ l, Y W p l ≤ Y' W p l) :
    PrecMax vol Dom X Y' := by
  intro ε D hε hD
  obtain ⟨W₀, hW⟩ := h ε D hε hD
  refine ⟨W₀, fun W hW0 p hp => (measure_mono ?_).trans (hW W hW0 p hp)⟩
  rintro ω ⟨l, hl⟩
  exact ⟨l, lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (hY W p hp l) (Real.rpow_nonneg (Nat.cast_nonneg W) ε)) hl⟩

/-- A smaller family. -/
theorem PrecMax.anti {ι : Type*} {vol : ι → ℕ} {Dom Dom' : ℕ → Set ι} {Λ : ℕ → ι → Type*}
    {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ} {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ}
    (h : PrecMax vol Dom X Y) (hD : ∀ W, Dom' W ⊆ Dom W) : PrecMax vol Dom' X Y := by
  intro ε D hε hD'
  obtain ⟨W₀, hW⟩ := h ε D hε hD'
  exact ⟨W₀, fun W hW0 p hp => hW W hW0 p (hD W hp)⟩

private lemma domination_two_le (W : ℕ) (hW : 2 ≤ W) (D : ℝ) :
    ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) ≤
      ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  have hWpos : (0 : ℝ) < W := by linarith
  have hnn : 0 ≤ (W : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hWpos.le _
  rw [← ENNReal.ofReal_add hnn hnn]
  apply ENNReal.ofReal_le_ofReal
  have e : (W : ℝ) ^ (-(D + 1)) = (W : ℝ) ^ (-D) * (W : ℝ)⁻¹ := by
    rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
  have hpos : 0 < (W : ℝ) ^ (-D) := Real.rpow_pos_of_pos hWpos _
  have hinv : (W : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW2
  rw [e]
  nlinarith

/-- Combination of two dominations at `ε/2, D+1` when the event for the combined quantity is
contained in the union of the two events. -/
private lemma domination_combine {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι}
    {Λ : ℕ → ι → Type*}
    {X X₁ X₂ : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ}
    {Y Y₁ Y₂ : (W : ℕ) → (p : ι) → Λ W p → ℝ} (h₁ : PrecMax vol Dom X₁ Y₁)
    (h₂ : PrecMax vol Dom X₂ Y₂)
    (hincl : ∀ ε : ℝ, 0 < ε → ∀ W : ℕ, 2 ≤ W → ∀ p l ω,
      (W : ℝ) ^ ε * Y W p l < ‖X W p l ω‖ →
        (W : ℝ) ^ (ε / 2) * Y₁ W p l < ‖X₁ W p l ω‖ ∨
          (W : ℝ) ^ (ε / 2) * Y₂ W p l < ‖X₂ W p l ω‖) :
    PrecMax vol Dom X Y := by
  intro ε D hε hD
  obtain ⟨W₁, hW₁⟩ := h₁ (ε / 2) (D + 1) (by positivity) (by linarith)
  obtain ⟨W₂, hW₂⟩ := h₂ (ε / 2) (D + 1) (by positivity) (by linarith)
  refine ⟨max (max W₁ W₂) 2, fun W hW p hp => ?_⟩
  have h1 : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have h2 : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have h3 : 2 ≤ W := (le_max_right _ _).trans hW
  calc μ W (vol p) {ω | ∃ l : Λ W p, (W : ℝ) ^ ε * Y W p l < ‖X W p l ω‖}
      ≤ μ W (vol p) ({ω | ∃ l : Λ W p, (W : ℝ) ^ (ε / 2) * Y₁ W p l < ‖X₁ W p l ω‖} ∪
          {ω | ∃ l : Λ W p, (W : ℝ) ^ (ε / 2) * Y₂ W p l < ‖X₂ W p l ω‖}) := by
        apply measure_mono
        rintro ω ⟨l, hl⟩
        rcases hincl ε hε W h3 p l ω hl with h | h
        · exact Or.inl ⟨l, h⟩
        · exact Or.inr ⟨l, h⟩
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) :=
        add_le_add (hW₁ W h1 p hp) (hW₂ W h2 p hp)
    _ ≤ _ := domination_two_le W h3 D

/-- Sums: `X₁ ≺ Y₁` and `X₂ ≺ Y₂` give `X₁ + X₂ ≺ Y₁ + Y₂`. -/
theorem PrecMax.add {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι} {Λ : ℕ → ι → Type*}
    {X₁ X₂ : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ}
    {Y₁ Y₂ : (W : ℕ) → (p : ι) → Λ W p → ℝ} (h₁ : PrecMax vol Dom X₁ Y₁)
    (h₂ : PrecMax vol Dom X₂ Y₂) (hY₁ : ∀ W p l, 0 ≤ Y₁ W p l) (hY₂ : ∀ W p l, 0 ≤ Y₂ W p l) :
    PrecMax vol Dom (fun W p l ω => X₁ W p l ω + X₂ W p l ω)
      (fun W p l => Y₁ W p l + Y₂ W p l) := by
  refine domination_combine h₁ h₂ fun ε hε W hW p l ω hlt => ?_
  by_contra hcon
  obtain ⟨c1, c2⟩ := not_or.mp hcon
  rw [not_lt] at c1 c2
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hle : (W : ℝ) ^ (ε / 2) ≤ (W : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hs : 0 ≤ Y₁ W p l + Y₂ W p l := add_nonneg (hY₁ W p l) (hY₂ W p l)
  have : ‖X₁ W p l ω + X₂ W p l ω‖ ≤ (W : ℝ) ^ ε * (Y₁ W p l + Y₂ W p l) :=
    calc ‖X₁ W p l ω + X₂ W p l ω‖ ≤ ‖X₁ W p l ω‖ + ‖X₂ W p l ω‖ := norm_add_le _ _
      _ ≤ (W : ℝ) ^ (ε / 2) * (Y₁ W p l + Y₂ W p l) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hle hs
  exact absurd hlt (not_lt.mpr this)

/-- Union bound: a bound for each label, uniform in the label, and at most `W^C` labels give the
maximum inside the probability. -/
theorem PrecMax.of_card {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι} {Λ : ℕ → ι → Type*}
    [∀ W p, Fintype (Λ W p)] {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ}
    {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ} (C : ℝ)
    (hcard : ∀ W p, p ∈ Dom W → (Fintype.card (Λ W p) : ℝ) ≤ (W : ℝ) ^ C)
    (h : ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ p ∈ Dom W, ∀ l : Λ W p,
      μ W (vol p) {ω | (W : ℝ) ^ ε * Y W p l < ‖X W p l ω‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D))) :
    PrecMax vol Dom X Y := by
  intro ε D hε hD
  have hCp : 0 ≤ max C 0 := le_max_right _ _
  obtain ⟨W₁, hW₁⟩ := h ε (D + max C 0) hε (by linarith)
  refine ⟨max W₁ 2, fun W hW p hp => ?_⟩
  have h1 : W₁ ≤ W := (le_max_left _ _).trans hW
  have h3 : 2 ≤ W := (le_max_right _ _).trans hW
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hset : {ω | ∃ l : Λ W p, (W : ℝ) ^ ε * Y W p l < ‖X W p l ω‖} =
      ⋃ l : Λ W p, {ω | (W : ℝ) ^ ε * Y W p l < ‖X W p l ω‖} := by
    ext ω; simp
  calc μ W (vol p) {ω | ∃ l : Λ W p, (W : ℝ) ^ ε * Y W p l < ‖X W p l ω‖}
      = μ W (vol p) (⋃ l : Λ W p, {ω | (W : ℝ) ^ ε * Y W p l < ‖X W p l ω‖}) := by rw [hset]
    _ ≤ ∑ l : Λ W p, μ W (vol p) {ω | (W : ℝ) ^ ε * Y W p l < ‖X W p l ω‖} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _l : Λ W p, ENNReal.ofReal ((W : ℝ) ^ (-(D + max C 0))) :=
        Finset.sum_le_sum fun l _ => hW₁ W h1 p hp l
    _ = ENNReal.ofReal ((Fintype.card (Λ W p) : ℝ) * (W : ℝ) ^ (-(D + max C 0))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        have hpos : 0 < (W : ℝ) ^ (-(D + max C 0)) := Real.rpow_pos_of_pos hWpos _
        calc (Fintype.card (Λ W p) : ℝ) * (W : ℝ) ^ (-(D + max C 0))
            ≤ (W : ℝ) ^ C * (W : ℝ) ^ (-(D + max C 0)) :=
              mul_le_mul_of_nonneg_right (hcard W p hp) hpos.le
          _ = (W : ℝ) ^ (C + -(D + max C 0)) := (Real.rpow_add hWpos _ _).symm
          _ ≤ (W : ℝ) ^ (-D) :=
              Real.rpow_le_rpow_of_exponent_le hW1 (by linarith [le_max_left C 0])

end LSBA
