import LSBA.Kernel.Algebra

/-!
# Projected tensors

The propagation of tensors with zero rows or with one stable leg, (A.74)
[fo:eq:projected-propagation] (Appendix A.12 [sec:gc-projected]).
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

private lemma ktens_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- A cyclic ball of radius `r` has at most `2r + 1` points. -/
private lemma ktens_ball_card {L : ℕ} (β : Fin L) (r : ℕ) :
    (Finset.univ.filter fun x : Fin L => cycDist x β ≤ r).card ≤ 2 * r + 1 := by
  have hβ := β.isLt
  have h1 : (Finset.univ.filter fun x : Fin L => cycDist x β ≤ r).card ≤
      (Finset.range (r + 1) ∪ Finset.Ico (L - r) L).card := by
    refine Finset.card_le_card_of_injOn (fun x : Fin L => (x.val + L - β.val) % L) ?_ ?_
    · intro x hx
      have hx' : cycDist x β ≤ r := by simpa using hx
      have hxl := x.isLt
      simp only [cycDist, ktens_mod hxl hβ, ktens_mod hβ hxl] at hx'
      simp only [Finset.coe_union, Finset.coe_range, Finset.coe_Ico, Set.mem_union,
        Set.mem_Iio, Set.mem_Ico, ktens_mod hxl hβ]
      split_ifs at hx' ⊢ <;> omega
    · intro x _ x' _ hxx
      have hxl := x.isLt
      have hxl' := x'.isLt
      simp only [ktens_mod hxl hβ, ktens_mod hxl' hβ] at hxx
      apply Fin.ext
      split_ifs at hxx <;> omega
  refine h1.trans ?_
  calc (Finset.range (r + 1) ∪ Finset.Ico (L - r) L).card
      ≤ (Finset.range (r + 1)).card + (Finset.Ico (L - r) L).card := Finset.card_union_le _ _
    _ ≤ (r + 1) + r := by
        rw [Finset.card_range, Nat.card_Ico]
        omega
    _ = 2 * r + 1 := by ring

/-- Sum over a cyclic ball of a function bounded by `c` on it. -/
private lemma ktens_ball_sum {L : ℕ} (β : Fin L) (R c : ℝ) (hR : 1 ≤ R) (f : Fin L → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hfc : ∀ x, (cycDist x β : ℝ) ≤ R → f x ≤ c) :
    ∑ x, (if (cycDist x β : ℝ) ≤ R then f x else 0) ≤ 3 * R * c := by
  have hc : 0 ≤ c := le_trans (hf0 β) (hfc β (by simp [cycDist]; linarith))
  have hfl : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le (by linarith)
  have hflag : ∀ x : Fin L, (cycDist x β : ℝ) ≤ R ↔ cycDist x β ≤ ⌊R⌋₊ := fun x =>
    (Nat.le_floor_iff (by linarith)).symm
  calc ∑ x, (if (cycDist x β : ℝ) ≤ R then f x else 0)
      ≤ ∑ x, (if cycDist x β ≤ ⌊R⌋₊ then c else 0) := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases hx : (cycDist x β : ℝ) ≤ R
        · simp only [hx, (hflag x).mp hx, ↓reduceIte]; exact hfc x hx
        · have hx' : ¬ cycDist x β ≤ ⌊R⌋₊ := fun h => hx ((hflag x).mpr h)
          simp only [hx, hx', ↓reduceIte, le_refl]
    _ = ((Finset.univ.filter fun x : Fin L => cycDist x β ≤ ⌊R⌋₊).card : ℝ) * c := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (⌊R⌋₊ : ℝ) + 1) * c := by
        apply mul_le_mul_of_nonneg_right _ hc
        exact_mod_cast ktens_ball_card β ⌊R⌋₊
    _ ≤ 3 * R * c := by
        apply mul_le_mul_of_nonneg_right _ hc
        linarith

/-- Summation over tuples that are within `R` of the anchor leg `i₀`: each other leg has a weight
depending on the anchor position. -/
private lemma ktens_anchor {n L : ℕ} (i₀ : Fin n) (R : ℝ) (h : Fin L → ℝ)
    (g : Fin n → Fin L → Fin L → ℝ) (hh : ∀ β, 0 ≤ h β) (hg : ∀ j β x, 0 ≤ g j β x)
    (T : Fin n → ℝ)
    (hT : ∀ j β, j ≠ i₀ → ∑ x, (if (cycDist x β : ℝ) ≤ R then g j β x else 0) ≤ T j) :
    ∑ b : Fin n → Fin L, (if ∀ j, (cycDist (b j) (b i₀) : ℝ) ≤ R then
        h (b i₀) * ∏ j ∈ Finset.univ.erase i₀, g j (b i₀) (b j) else 0)
      ≤ (∑ β, h β) * ∏ j ∈ Finset.univ.erase i₀, T j := by
  set φ : Fin L → Fin n → Fin L → ℝ := fun β j x =>
    if j = i₀ then (if x = β then h β else 0)
    else (if (cycDist x β : ℝ) ≤ R then g j β x else 0) with hφ
  have hφ0 : ∀ β j x, 0 ≤ φ β j x := by
    intro β j x
    simp only [hφ]
    split_ifs <;> first | exact hh _ | exact hg _ _ _ | exact le_rfl
  have step1 : ∀ b : Fin n → Fin L, (if ∀ j, (cycDist (b j) (b i₀) : ℝ) ≤ R then
        h (b i₀) * ∏ j ∈ Finset.univ.erase i₀, g j (b i₀) (b j) else 0) ≤
      ∑ β, ∏ j, φ β j (b j) := by
    intro b
    split_ifs with hc
    · refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun β => ∏ j, φ β j (b j))
        (fun β _ => Finset.prod_nonneg fun j _ => hφ0 β j (b j)) (Finset.mem_univ (b i₀)))
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
      simp only [hφ, ↓reduceIte]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj' : j ≠ i₀ := Finset.ne_of_mem_erase hj
      simp only [hj', hc j, ↓reduceIte]
    · exact Finset.sum_nonneg fun β _ => Finset.prod_nonneg fun j _ => hφ0 β j (b j)
  calc _ ≤ ∑ b : Fin n → Fin L, ∑ β, ∏ j, φ β j (b j) := Finset.sum_le_sum fun b _ => step1 b
    _ = ∑ β, ∏ j, ∑ x, φ β j x := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [Fintype.prod_sum]
    _ ≤ ∑ β, h β * ∏ j ∈ Finset.univ.erase i₀, T j := by
        refine Finset.sum_le_sum fun β _ => ?_
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
        have h1 : ∑ x, φ β i₀ x = h β := by simp [hφ]
        rw [h1]
        refine mul_le_mul_of_nonneg_left ?_ (hh β)
        refine Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun x _ => hφ0 β j x)
          (fun j hj => ?_)
        have hj' : j ≠ i₀ := Finset.ne_of_mem_erase hj
        simpa [hφ, hj'] using hT j β hj'
    _ = (∑ β, h β) * ∏ j ∈ Finset.univ.erase i₀, T j := by rw [Finset.sum_mul]

/-- Telescoping bound for the difference of two products of bounded factors. -/
private lemma ktens_prod_sub {ι : Type*} (x y : ι → ℝ) (q δ : ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hy0 : ∀ i, 0 ≤ y i) (hxq : ∀ i, x i ≤ q) (hyq : ∀ i, y i ≤ q)
    (hxy : ∀ i, |x i - y i| ≤ δ) (s : Finset ι) :
    |∏ i ∈ s, x i - ∏ i ∈ s, y i| ≤ s.card * q ^ (s.card - 1) * δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hq0 : 0 ≤ q := le_trans (hx0 a) (hxq a)
    have hPy : ∏ i ∈ s, y i ≤ q ^ s.card := by
      calc _ ≤ ∏ _i ∈ s, q := Finset.prod_le_prod₀ (fun i _ => hy0 i) (fun i _ => hyq i)
        _ = q ^ s.card := Finset.prod_const _
    have hPy0 : 0 ≤ ∏ i ∈ s, y i := Finset.prod_nonneg fun i _ => hy0 i
    have key : x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i =
        x a * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x a - y a) * ∏ i ∈ s, y i := by ring
    rw [key]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (hx0 a), abs_of_nonneg hPy0]
    have h1 : x a * |∏ i ∈ s, x i - ∏ i ∈ s, y i| ≤ q * (s.card * q ^ (s.card - 1) * δ) :=
      mul_le_mul (hxq a) ih (abs_nonneg _) hq0
    have h2 : |x a - y a| * ∏ i ∈ s, y i ≤ δ * q ^ s.card :=
      mul_le_mul (hxy a) hPy hPy0 ((abs_nonneg _).trans (hxy a))
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    rcases Nat.eq_zero_or_pos s.card with h0 | h0
    · simp [h0]
    · obtain ⟨k, hk⟩ : ∃ k, s.card = k + 1 := ⟨s.card - 1, by omega⟩
      rw [hk]
      push_cast
      ring

/-- Weighted bound for a sum against a tensor supported on tuples within `R` of each other. -/
private lemma ktens_sum_bound {n L : ℕ} (A c : (Fin n → Fin L) → ℂ) (R : ℝ) (i₀ : Fin n)
    (hsupp : ∀ b : Fin n → Fin L, (∃ i j, R < cycDist (b i) (b j)) → A b = 0)
    (h : Fin L → ℝ) (g : Fin n → Fin L → Fin L → ℝ) (T : Fin n → ℝ)
    (hh : ∀ β, 0 ≤ h β) (hg : ∀ j β x, 0 ≤ g j β x)
    (hT : ∀ j β, j ≠ i₀ → ∑ x, (if (cycDist x β : ℝ) ≤ R then g j β x else 0) ≤ T j)
    (hc : ∀ b : Fin n → Fin L, (∀ j, (cycDist (b j) (b i₀) : ℝ) ≤ R) →
      ‖c b‖ ≤ h (b i₀) * ∏ j ∈ Finset.univ.erase i₀, g j (b i₀) (b j)) :
    ‖∑ b, c b * A b‖ ≤ (⨆ b, ‖A b‖) * ((∑ β, h β) * ∏ j ∈ Finset.univ.erase i₀, T j) := by
  have hAM : ∀ b, ‖A b‖ ≤ ⨆ b, ‖A b‖ := fun b =>
    le_ciSup (f := fun b => ‖A b‖) (Finite.bddAbove_range _) b
  have hM0 : 0 ≤ ⨆ b, ‖A b‖ := Real.iSup_nonneg fun b => norm_nonneg _
  calc ‖∑ b, c b * A b‖ ≤ ∑ b, ‖c b * A b‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin n → Fin L, (⨆ b, ‖A b‖) * (if ∀ j, (cycDist (b j) (b i₀) : ℝ) ≤ R then
        h (b i₀) * ∏ j ∈ Finset.univ.erase i₀, g j (b i₀) (b j) else 0) := by
        refine Finset.sum_le_sum fun b _ => ?_
        split_ifs with hb
        · rw [norm_mul, mul_comm]
          exact mul_le_mul (hAM b) (hc b hb) (norm_nonneg _) hM0
        · have : A b = 0 := by
            apply hsupp
            push Not at hb
            obtain ⟨j, hj⟩ := hb
            exact ⟨j, i₀, hj⟩
          simp [this]
    _ = (⨆ b, ‖A b‖) * ∑ b : Fin n → Fin L, (if ∀ j, (cycDist (b j) (b i₀) : ℝ) ≤ R then
        h (b i₀) * ∏ j ∈ Finset.univ.erase i₀, g j (b i₀) (b j) else 0) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (ktens_anchor i₀ R h g hh hg T hT) hM0

/-- Expansion of a product of sums over subsets of the factors. -/
private lemma ktens_expand {n : ℕ} (f g : Fin n → ℝ) :
    ∏ i, (f i + g i) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, ∏ i, (if i ∈ S then f i else g i) := by
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_ite]
  congr 1
  · refine Finset.prod_congr ?_ fun _ _ => rfl
    ext i; simp
  · refine Finset.prod_congr ?_ fun _ _ => rfl
    ext i; simp

/-- Terms of the expansion of `∏ (I + Ξ)` that contain at least one identity factor. -/
private lemma ktens_zero_other {m L : ℕ} (Ξ : Matrix (Fin L) (Fin L) ℝ)
    (A : (Fin (m + 2) → Fin L) → ℂ) (a : Fin (m + 2) → Fin L) (R q Λ : ℝ)
    (hΞ0 : ∀ x y, 0 ≤ Ξ x y) (hΞq : ∀ x y, Ξ x y ≤ q) (hR1 : 1 ≤ R) (hΛ1 : 1 ≤ Λ)
    (h3 : 3 * R * q ≤ Λ)
    (hsupp : ∀ b : Fin (m + 2) → Fin L, (∃ i j, R < cycDist (b i) (b j)) → A b = 0)
    (S : Finset (Fin (m + 2))) (hS : S ≠ Finset.univ) :
    ‖∑ b, ((∏ i, (if i ∈ S then Ξ (a i) (b i) else (if a i = b i then (1 : ℝ) else 0)) : ℝ) : ℂ) *
        A b‖ ≤ (⨆ b, ‖A b‖) * Λ ^ (m + 1) := by
  obtain ⟨i₁, hi₁⟩ : ∃ i, i ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hS (Finset.eq_univ_iff_forall.mpr hcon)
  have hq0 : 0 ≤ q := le_trans (hΞ0 (a i₁) (a i₁)) (hΞq _ _)
  have key := ktens_sum_bound A
    (fun b => ((∏ i, (if i ∈ S then Ξ (a i) (b i) else (if a i = b i then (1 : ℝ) else 0)) : ℝ) :
      ℂ))
    R i₁ hsupp (fun β => if a i₁ = β then (1 : ℝ) else 0)
    (fun j _ x => if j ∈ S then Ξ (a j) x else (if a j = x then (1 : ℝ) else 0)) (fun _ => Λ)
    (fun β => by split_ifs <;> norm_num)
    (fun j β x => by
      by_cases hj : j ∈ S
      · simp only [hj, ↓reduceIte]; exact hΞ0 _ _
      · simp only [hj, ↓reduceIte]; split_ifs <;> norm_num)
    (fun j β _ => by
      by_cases hj : j ∈ S
      · simp only [hj, ↓reduceIte]
        refine le_trans (ktens_ball_sum β R q hR1 (fun x => Ξ (a j) x) (fun x => hΞ0 _ _)
          (fun x _ => hΞq _ _)) h3
      · simp only [hj, ↓reduceIte]
        calc ∑ x, (if (cycDist x β : ℝ) ≤ R then (if a j = x then (1 : ℝ) else 0) else 0)
            ≤ ∑ x, (if a j = x then (1 : ℝ) else 0) := by
              refine Finset.sum_le_sum fun x _ => ?_
              split_ifs <;> norm_num
          _ = 1 := by simp
          _ ≤ Λ := hΛ1)
    (fun b _ => by
      have hnn : 0 ≤ ∏ i, (if i ∈ S then Ξ (a i) (b i) else (if a i = b i then (1 : ℝ) else 0)) :=
        Finset.prod_nonneg fun i _ => by
          by_cases hi : i ∈ S
          · simp only [hi, ↓reduceIte]; exact hΞ0 _ _
          · simp only [hi, ↓reduceIte]; split_ifs <;> norm_num
      rw [Complex.norm_real, Real.norm_of_nonneg hnn,
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₁)]
      simp only [hi₁, ↓reduceIte, le_refl])
  refine key.trans (le_of_eq ?_)
  have hprod : ∏ j ∈ Finset.univ.erase i₁, Λ = Λ ^ (m + 1) := by
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    rfl
  rw [hprod]
  simp

/-- The all-`Ξ` term of the expansion of `∏ (I + Ξ)`, using the zero rows of the first leg. -/
private lemma ktens_zero_main {m L : ℕ} (Ξ : Matrix (Fin L) (Fin L) ℝ)
    (A : (Fin (m + 2) → Fin L) → ℂ) (a : Fin (m + 2) → Fin L) (R q δ ρ : ℝ)
    (hΞ0 : ∀ x y, 0 ≤ Ξ x y) (hΞq : ∀ x y, Ξ x y ≤ q) (hq0 : 0 ≤ q) (hδ0 : 0 ≤ δ)
    (hrow : ∀ x, ∑ y, Ξ x y ≤ ρ)
    (hinc : ∀ c x y, (cycDist x y : ℝ) ≤ R → |Ξ c x - Ξ c y| ≤ δ) (hR1 : 1 ≤ R)
    (hsupp : ∀ b : Fin (m + 2) → Fin L, (∃ i j, R < cycDist (b i) (b j)) → A b = 0)
    (hzero : ∀ b₁ : Fin L, ∑ b : Fin (m + 2) → Fin L,
      (if b ⟨0, by omega⟩ = b₁ then A b else 0) = 0) :
    ‖∑ b, ((∏ i, Ξ (a i) (b i) : ℝ) : ℂ) * A b‖ ≤
      (⨆ b, ‖A b‖) * (ρ * ((m + 1) * q ^ m * δ) * (3 * R) ^ (m + 1)) := by
  set i0 : Fin (m + 2) := ⟨0, by omega⟩ with hi0
  set K : ℝ := (m + 1) * q ^ m * δ with hK
  have hK0 : 0 ≤ K := by positivity
  have hρ0 : 0 ≤ ρ := le_trans (Finset.sum_nonneg fun y _ => hΞ0 (a i0) y) (hrow (a i0))
  -- subtract the part depending only on the first leg
  have hF0 : ∑ b : Fin (m + 2) → Fin L, ((∏ i, Ξ (a i) (b i0) : ℝ) : ℂ) * A b = 0 := by
    calc ∑ b : Fin (m + 2) → Fin L, ((∏ i, Ξ (a i) (b i0) : ℝ) : ℂ) * A b
        = ∑ b : Fin (m + 2) → Fin L, ∑ β, ((∏ i, Ξ (a i) β : ℝ) : ℂ) *
            (if b i0 = β then A b else 0) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          simp [mul_ite]
      _ = ∑ β, ((∏ i, Ξ (a i) β : ℝ) : ℂ) * ∑ b : Fin (m + 2) → Fin L,
            (if b i0 = β then A b else 0) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [Finset.mul_sum]
      _ = 0 := by
          refine Finset.sum_eq_zero fun β _ => ?_
          rw [hzero β, mul_zero]
  have hsub : ∑ b, ((∏ i, Ξ (a i) (b i) : ℝ) : ℂ) * A b =
      ∑ b, (((∏ i, Ξ (a i) (b i)) - ∏ i, Ξ (a i) (b i0) : ℝ) : ℂ) * A b := by
    have : ∑ b, (((∏ i, Ξ (a i) (b i)) - ∏ i, Ξ (a i) (b i0) : ℝ) : ℂ) * A b =
        ∑ b, ((∏ i, Ξ (a i) (b i) : ℝ) : ℂ) * A b -
          ∑ b : Fin (m + 2) → Fin L, ((∏ i, Ξ (a i) (b i0) : ℝ) : ℂ) * A b := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      push_cast; ring
    rw [this, hF0, sub_zero]
  rw [hsub]
  have key := ktens_sum_bound A
    (fun b => (((∏ i, Ξ (a i) (b i)) - ∏ i, Ξ (a i) (b i0) : ℝ) : ℂ)) R i0 hsupp
    (fun β => Ξ (a i0) β * K) (fun _ _ _ => (1 : ℝ)) (fun _ => 3 * R)
    (fun β => mul_nonneg (hΞ0 _ _) hK0) (fun _ _ _ => zero_le_one)
    (fun j β _ => by
      have := ktens_ball_sum β R 1 hR1 (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (fun _ _ => le_rfl)
      simpa using this)
    (fun b hb => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h1 : (∏ i, Ξ (a i) (b i)) - ∏ i, Ξ (a i) (b i0) =
          Ξ (a i0) (b i0) * (∏ i ∈ Finset.univ.erase i0, Ξ (a i) (b i) -
            ∏ i ∈ Finset.univ.erase i0, Ξ (a i) (b i0)) := by
        rw [← Finset.mul_prod_erase Finset.univ (fun i => Ξ (a i) (b i)) (Finset.mem_univ i0),
          ← Finset.mul_prod_erase Finset.univ (fun i => Ξ (a i) (b i0)) (Finset.mem_univ i0)]
        ring
      rw [h1, abs_mul, abs_of_nonneg (hΞ0 _ _)]
      simp only [Finset.prod_const_one, mul_one]
      refine mul_le_mul_of_nonneg_left ?_ (hΞ0 _ _)
      have := ktens_prod_sub (fun i => Ξ (a i) (b i)) (fun i => Ξ (a i) (b i0)) q δ
        (fun i => hΞ0 _ _) (fun i => hΞ0 _ _) (fun i => hΞq _ _) (fun i => hΞq _ _)
        (fun i => hinc (a i) (b i) (b i0) (hb i)) (Finset.univ.erase i0)
      have hc : (Finset.univ.erase i0).card = m + 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        rfl
      rw [hc] at this
      simpa [hK] using this)
  refine key.trans ?_
  have hprod : ∏ j ∈ Finset.univ.erase i0, (3 * R) = (3 * R) ^ (m + 1) := by
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    rfl
  rw [hprod]
  have hM0 : 0 ≤ ⨆ b, ‖A b‖ := Real.iSup_nonneg fun b => norm_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ hM0
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hrow (a i0)) hK0

/-- (A.74) [fo:eq:projected-propagation], zero-row case: `Ξ` has row at most `ρ`, entries at most
`C₁ρ/ℓ_v` and increments at most `C₁ρ/ℓ_v · d/ℓ_v`; `A` has zero rows in its first leg and
relative diameter at most `Hℓ_u`. Here `ρ = (1-u)/(1-v)` and `ρℓ_u/ℓ_v = ζ_v/ζ_u`. -/
theorem projected_zeroRow (n : ℕ) (hn : 2 ≤ n) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (L : ℕ) (Ξ : Matrix (Fin L) (Fin L) ℝ) (A : (Fin n → Fin L) → ℂ)
      (ρ ℓu ℓv H : ℝ), (∀ a b, 0 ≤ Ξ a b) → (∀ a, ∑ b, Ξ a b ≤ ρ) →
      (∀ a b, Ξ a b ≤ C₁ * ρ / ℓv) →
      (∀ a b b', |Ξ a b - Ξ a b'| ≤ C₁ * ρ / ℓv * ((cycDist b b' : ℝ) / ℓv)) →
      1 ≤ ℓu → ℓu ≤ ℓv → 1 ≤ H → 1 ≤ ρ * ℓu / ℓv →
      (∀ b : Fin n → Fin L, (∃ i j, H * ℓu < cycDist (b i) (b j)) → A b = 0) →
      (∀ b₁ : Fin L, ∑ b : Fin n → Fin L, (if b ⟨0, by omega⟩ = b₁ then A b else 0) = 0) →
      ∀ a : Fin n → Fin L,
        ‖∑ b : Fin n → Fin L, (∏ i, (((1 + Ξ) (a i) (b i) : ℝ) : ℂ)) * A b‖ ≤
          Cn * H ^ n * (ρ * ℓu / ℓv) ^ n * ⨆ b, ‖A b‖ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set c₀ : ℝ := max 1 (3 * C₁) with hc₀
  have hc01 : 1 ≤ c₀ := le_max_left _ _
  have hc03 : 3 * C₁ ≤ c₀ := le_max_right _ _
  refine ⟨2 ^ (m + 2) * c₀ ^ (m + 1) + (m + 1) * (3 * C₁) ^ (m + 1), by positivity, ?_⟩
  intro L Ξ A ρ ℓu ℓv H hΞ0 hΞrow hΞent hΞinc h1u huv hH hX hsupp hzero a
  have hℓv : 0 < ℓv := by linarith
  have hρ : 0 < ρ := by
    by_contra hρ
    push Not at hρ
    have : ρ * ℓu / ℓv ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hρ (by linarith)) hℓv.le
    linarith
  set X := ρ * ℓu / ℓv with hXdef
  set R := H * ℓu with hRdef
  have hR1 : 1 ≤ R := by nlinarith
  set Y := H * X with hY
  have hY1 : 1 ≤ Y := by nlinarith
  set q := C₁ * ρ / ℓv with hq
  have hq0 : 0 ≤ q := by positivity
  have hRq : R * q = C₁ * Y := by
    simp only [hRdef, hq, hXdef, hY]; field_simp
  have hρR : ρ * (R / ℓv) = Y := by
    simp only [hRdef, hXdef, hY]; field_simp
  set Λ := c₀ * Y with hΛ
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; nlinarith
  have h3 : 3 * R * q ≤ Λ := by
    calc 3 * R * q = 3 * C₁ * Y := by rw [mul_assoc, hRq]; ring
      _ ≤ c₀ * Y := mul_le_mul_of_nonneg_right hc03 (by linarith)
  have hM0 : 0 ≤ ⨆ b, ‖A b‖ := Real.iSup_nonneg fun b => norm_nonneg _
  set i0 : Fin (m + 2) := ⟨0, by omega⟩ with hi0
  -- the expansion
  set u : Finset (Fin (m + 2)) → Fin (m + 2) → Fin L → ℝ := fun S i x =>
    if i ∈ S then Ξ (a i) x else (if a i = x then (1 : ℝ) else 0) with hu
  have hexp : ∀ b : Fin (m + 2) → Fin L, (∏ i, (((1 + Ξ) (a i) (b i) : ℝ) : ℂ)) =
      ((∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powerset, ∏ i, u S i (b i) : ℝ) : ℂ) := by
    intro b
    rw [← Complex.ofReal_prod]
    congr 1
    rw [← ktens_expand (fun i => Ξ (a i) (b i)) (fun i => if a i = b i then (1 : ℝ) else 0)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Matrix.add_apply, Matrix.one_apply, add_comm]
  have hsum : ∑ b, (∏ i, (((1 + Ξ) (a i) (b i) : ℝ) : ℂ)) * A b =
      ∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powerset,
        ∑ b, ((∏ i, u S i (b i) : ℝ) : ℂ) * A b := by
    simp_rw [hexp]
    push_cast
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  have huniv : (Finset.univ : Finset (Fin (m + 2))) ∈
      (Finset.univ : Finset (Fin (m + 2))).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ _)
  have hB1 := ktens_zero_main Ξ A a R q (q * (R / ℓv)) ρ hΞ0 hΞent hq0
    (by positivity) hΞrow
    (fun c x y hxy => by
      calc |Ξ c x - Ξ c y| ≤ C₁ * ρ / ℓv * ((cycDist x y : ℝ) / ℓv) := hΞinc c x y
        _ ≤ q * (R / ℓv) := by
            apply mul_le_mul_of_nonneg_left _ hq0
            exact div_le_div_of_nonneg_right hxy hℓv.le)
    hR1 hsupp hzero
  have hBo : ∀ S ∈ (Finset.univ : Finset (Fin (m + 2))).powerset.erase Finset.univ,
      ‖∑ b, ((∏ i, u S i (b i) : ℝ) : ℂ) * A b‖ ≤ (⨆ b, ‖A b‖) * Λ ^ (m + 1) := by
    intro S hS
    exact ktens_zero_other Ξ A a R q Λ hΞ0 hΞent hR1 hΛ1 h3 hsupp S (Finset.ne_of_mem_erase hS)
  have hB1' : ‖∑ b, ((∏ i, u Finset.univ i (b i) : ℝ) : ℂ) * A b‖ ≤
      (⨆ b, ‖A b‖) * ((m + 1) * (3 * C₁) ^ (m + 1) * Y ^ (m + 2)) := by
    have e1 : ∀ b : Fin (m + 2) → Fin L, ∏ i, u Finset.univ i (b i) = ∏ i, Ξ (a i) (b i) := by
      intro b; simp [hu]
    simp_rw [e1]
    refine hB1.trans (le_of_eq ?_)
    congr 1
    have : ρ * ((m + 1) * q ^ m * (q * (R / ℓv))) * (3 * R) ^ (m + 1) =
        (m + 1) * 3 ^ (m + 1) * (ρ * (R / ℓv)) * (q * R) ^ (m + 1) := by
      rw [mul_pow, mul_pow]; ring
    rw [this, hρR, mul_comm q R, hRq, mul_pow, mul_pow]
    ring
  rw [hsum, ← Finset.add_sum_erase _ _ huniv]
  have hcard :
      ((Finset.univ : Finset (Fin (m + 2))).powerset.erase Finset.univ).card ≤ 2 ^ (m + 2) := by
    refine (Finset.card_erase_le).trans ?_
    rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  calc ‖∑ b, ((∏ i, u Finset.univ i (b i) : ℝ) : ℂ) * A b +
        ∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powerset.erase Finset.univ,
          ∑ b, ((∏ i, u S i (b i) : ℝ) : ℂ) * A b‖
      ≤ ‖∑ b, ((∏ i, u Finset.univ i (b i) : ℝ) : ℂ) * A b‖ +
        ∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powerset.erase Finset.univ,
          ‖∑ b, ((∏ i, u S i (b i) : ℝ) : ℂ) * A b‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ (⨆ b, ‖A b‖) * ((m + 1) * (3 * C₁) ^ (m + 1) * Y ^ (m + 2)) +
        ((Finset.univ : Finset (Fin (m + 2))).powerset.erase Finset.univ).card •
          ((⨆ b, ‖A b‖) * Λ ^ (m + 1)) :=
        add_le_add hB1' (Finset.sum_le_card_nsmul _ _ _ hBo)
    _ ≤ (⨆ b, ‖A b‖) * ((m + 1) * (3 * C₁) ^ (m + 1) * Y ^ (m + 2)) +
        2 ^ (m + 2) * ((⨆ b, ‖A b‖) * Λ ^ (m + 1)) := by
        rw [nsmul_eq_mul]
        gcongr
        exact_mod_cast hcard
    _ ≤ (⨆ b, ‖A b‖) * ((m + 1) * (3 * C₁) ^ (m + 1) * Y ^ (m + 2)) +
        2 ^ (m + 2) * ((⨆ b, ‖A b‖) * (c₀ ^ (m + 1) * Y ^ (m + 2))) := by
        have hle : Λ ^ (m + 1) ≤ c₀ ^ (m + 1) * Y ^ (m + 2) := by
          rw [hΛ, mul_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 (Nat.le_succ (m + 1)))
            (by positivity)
        gcongr
    _ = (2 ^ (m + 2) * c₀ ^ (m + 1) + (m + 1) * (3 * C₁) ^ (m + 1)) * H ^ (m + 2) *
          X ^ (m + 2) * ⨆ b, ‖A b‖ := by
        rw [hY, mul_pow]; ring

/-- (A.74) [fo:eq:projected-propagation], case of at least one stable leg: each leg is stable
(absolute row at most `C₁`) or mixed (`|U - I|` entrywise at most `C₁ρ/ℓ_v`), and leg `i₀` is
stable; `A` has relative diameter at most `Hℓ_u`. -/
theorem projected_stableLeg (n : ℕ) (hn : 2 ≤ n) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (L : ℕ) (U : Fin n → Matrix (Fin L) (Fin L) ℂ)
      (A : (Fin n → Fin L) → ℂ) (ρ ℓu ℓv H : ℝ) (i₀ : Fin n),
      (∀ i, (∀ a, ∑ b, ‖U i a b‖ ≤ C₁) ∨
        ∀ a b, ‖U i a b - (1 : Matrix (Fin L) (Fin L) ℂ) a b‖ ≤ C₁ * ρ / ℓv) →
      (∀ a, ∑ b, ‖U i₀ a b‖ ≤ C₁) →
      1 ≤ ℓu → ℓu ≤ ℓv → 1 ≤ H → 1 ≤ ρ * ℓu / ℓv →
      (∀ b : Fin n → Fin L, (∃ i j, H * ℓu < cycDist (b i) (b j)) → A b = 0) →
      ∀ a : Fin n → Fin L,
        ‖∑ b : Fin n → Fin L, (∏ i, U i (a i) (b i)) * A b‖ ≤
          Cn * H ^ (n - 1) * (ρ * ℓu / ℓv) ^ (n - 1) * ⨆ b, ‖A b‖ := by
  refine ⟨C₁ * (1 + 3 * C₁) ^ (n - 1), by positivity, ?_⟩
  intro L U A ρ ℓu ℓv H i₀ hleg hi₀ h1u huv hH hX hsupp a
  have hℓv : 0 < ℓv := by linarith
  have hρ : 0 < ρ := by
    by_contra hρ
    push Not at hρ
    have : ρ * ℓu / ℓv ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hρ (by linarith)) hℓv.le
    linarith
  set X := ρ * ℓu / ℓv with hXdef
  set R := H * ℓu with hRdef
  have hR1 : 1 ≤ R := by nlinarith
  have hHX : 1 ≤ H * X := by nlinarith
  set q := C₁ * ρ / ℓv with hq
  have hq0 : 0 ≤ q := by positivity
  have hRq : R * q = C₁ * (H * X) := by
    simp only [hRdef, hq, hXdef]; field_simp
  set Λ := (1 + 3 * C₁) * (H * X) with hΛ
  have hΛ1 : 1 + 3 * C₁ * (H * X) ≤ Λ := by rw [hΛ]; nlinarith
  have hΛ2 : C₁ ≤ Λ := by rw [hΛ]; nlinarith
  have hT : ∀ j β, j ≠ i₀ → ∑ x, (if (cycDist x β : ℝ) ≤ R then ‖U j (a j) x‖ else 0) ≤ Λ := by
    intro j β _
    rcases hleg j with hs | hm
    · refine le_trans (Finset.sum_le_sum fun x _ => ?_) (le_trans (hs (a j)) hΛ2)
      split_ifs <;> simp
    · have h1 : ∀ x, (if (cycDist x β : ℝ) ≤ R then ‖U j (a j) x‖ else 0) ≤
          (if a j = x then (1 : ℝ) else 0) + (if (cycDist x β : ℝ) ≤ R then q else 0) := by
        intro x
        have hux : ‖U j (a j) x‖ ≤ (if a j = x then (1 : ℝ) else 0) + q := by
          calc ‖U j (a j) x‖ = ‖(U j (a j) x - (1 : Matrix (Fin L) (Fin L) ℂ) (a j) x) +
                (1 : Matrix (Fin L) (Fin L) ℂ) (a j) x‖ := by rw [sub_add_cancel]
            _ ≤ ‖U j (a j) x - (1 : Matrix (Fin L) (Fin L) ℂ) (a j) x‖ +
                ‖(1 : Matrix (Fin L) (Fin L) ℂ) (a j) x‖ := norm_add_le _ _
            _ ≤ q + (if a j = x then (1 : ℝ) else 0) := by
                refine add_le_add (hm (a j) x) ?_
                rw [Matrix.one_apply]
                split_ifs <;> simp
            _ = _ := add_comm _ _
        have hnn : 0 ≤ (if a j = x then (1 : ℝ) else 0) := by split_ifs <;> norm_num
        by_cases hd : (cycDist x β : ℝ) ≤ R
        · simp only [hd, ↓reduceIte]; exact hux
        · simp only [hd, ↓reduceIte]; linarith
      calc _ ≤ ∑ x, ((if a j = x then (1 : ℝ) else 0) +
              (if (cycDist x β : ℝ) ≤ R then q else 0)) := Finset.sum_le_sum fun x _ => h1 x
        _ = 1 + ∑ x, (if (cycDist x β : ℝ) ≤ R then q else 0) := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq]; simp
        _ ≤ 1 + 3 * R * q := by
            gcongr
            exact ktens_ball_sum β R q hR1 (fun _ => q) (fun _ => hq0) (fun _ _ => le_rfl)
        _ = 1 + 3 * C₁ * (H * X) := by rw [mul_assoc, hRq]; ring
        _ ≤ Λ := hΛ1
  have key := ktens_sum_bound A (fun b => ∏ i, U i (a i) (b i)) R i₀ hsupp
    (fun β => ‖U i₀ (a i₀) β‖) (fun j _ x => ‖U j (a j) x‖) (fun _ => Λ)
    (fun β => norm_nonneg _) (fun j β x => norm_nonneg _) hT (fun b _ => by
      rw [norm_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)])
  have hM0 : 0 ≤ ⨆ b, ‖A b‖ := Real.iSup_nonneg fun b => norm_nonneg _
  refine key.trans ?_
  have hprod : ∏ j ∈ Finset.univ.erase i₀, Λ = Λ ^ (n - 1) := by
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  rw [hprod]
  have hs : ∑ β, ‖U i₀ (a i₀) β‖ ≤ C₁ := hi₀ (a i₀)
  have hΛ0 : 0 ≤ Λ := by positivity
  calc (⨆ b, ‖A b‖) * ((∑ β, ‖U i₀ (a i₀) β‖) * Λ ^ (n - 1))
      ≤ (⨆ b, ‖A b‖) * (C₁ * Λ ^ (n - 1)) := by gcongr
    _ = C₁ * (1 + 3 * C₁) ^ (n - 1) * H ^ (n - 1) * X ^ (n - 1) * ⨆ b, ‖A b‖ := by
        rw [hΛ, mul_pow, mul_pow]; ring

/-- (A.74) [fo:eq:projected-propagation], zero-row case, with the increment premise in the form
given by (A.49) [da:eq:mixed-profile-increment] after the factor `v - u`: increments at most
`C₁ρ/ℓ_v · (d + ℓ_u)/ℓ_v`; the term `ℓ_u/ℓ_v` absorbs the remainder `ℓ_v⁻¹W^{-A}` of (A.49)
[da:eq:mixed-profile-increment]. -/
theorem projected_zeroRow' (n : ℕ) (hn : 2 ≤ n) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (L : ℕ) (Ξ : Matrix (Fin L) (Fin L) ℝ) (A : (Fin n → Fin L) → ℂ)
      (ρ ℓu ℓv H : ℝ), (∀ a b, 0 ≤ Ξ a b) → (∀ a, ∑ b, Ξ a b ≤ ρ) →
      (∀ a b, Ξ a b ≤ C₁ * ρ / ℓv) →
      (∀ a b b', |Ξ a b - Ξ a b'| ≤ C₁ * ρ / ℓv * (((cycDist b b' : ℝ) + ℓu) / ℓv)) →
      1 ≤ ℓu → ℓu ≤ ℓv → 1 ≤ H → 1 ≤ ρ * ℓu / ℓv →
      (∀ b : Fin n → Fin L, (∃ i j, H * ℓu < cycDist (b i) (b j)) → A b = 0) →
      (∀ b₁ : Fin L, ∑ b : Fin n → Fin L, (if b ⟨0, by omega⟩ = b₁ then A b else 0) = 0) →
      ∀ a : Fin n → Fin L,
        ‖∑ b : Fin n → Fin L, (∏ i, (((1 + Ξ) (a i) (b i) : ℝ) : ℂ)) * A b‖ ≤
          Cn * H ^ n * (ρ * ℓu / ℓv) ^ n * ⨆ b, ‖A b‖ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set c₀ : ℝ := max 1 (3 * C₁) with hc₀
  have hc01 : 1 ≤ c₀ := le_max_left _ _
  have hc03 : 3 * C₁ ≤ c₀ := le_max_right _ _
  refine ⟨2 ^ (m + 2) * c₀ ^ (m + 1) + 2 * ((m + 1) * (3 * C₁) ^ (m + 1)), by positivity, ?_⟩
  intro L Ξ A ρ ℓu ℓv H hΞ0 hΞrow hΞent hΞinc h1u huv hH hX hsupp hzero a
  have hℓv : 0 < ℓv := by linarith
  have hρ : 0 < ρ := by
    by_contra hρ
    push Not at hρ
    have : ρ * ℓu / ℓv ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hρ (by linarith)) hℓv.le
    linarith
  set X := ρ * ℓu / ℓv with hXdef
  set R := H * ℓu with hRdef
  have hR1 : 1 ≤ R := by nlinarith
  have hℓuR : ℓu ≤ R := by nlinarith
  set Y := H * X with hY
  have hY1 : 1 ≤ Y := by nlinarith
  set q := C₁ * ρ / ℓv with hq
  have hq0 : 0 ≤ q := by positivity
  have hRq : R * q = C₁ * Y := by
    simp only [hRdef, hq, hXdef, hY]; field_simp
  have hρR : ρ * (R / ℓv) = Y := by
    simp only [hRdef, hXdef, hY]; field_simp
  set Λ := c₀ * Y with hΛ
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; nlinarith
  have h3 : 3 * R * q ≤ Λ := by
    calc 3 * R * q = 3 * C₁ * Y := by rw [mul_assoc, hRq]; ring
      _ ≤ c₀ * Y := mul_le_mul_of_nonneg_right hc03 (by linarith)
  have hM0 : 0 ≤ ⨆ b, ‖A b‖ := Real.iSup_nonneg fun b => norm_nonneg _
  set i0 : Fin (m + 2) := ⟨0, by omega⟩ with hi0
  -- the expansion
  set u : Finset (Fin (m + 2)) → Fin (m + 2) → Fin L → ℝ := fun S i x =>
    if i ∈ S then Ξ (a i) x else (if a i = x then (1 : ℝ) else 0) with hu
  have hexp : ∀ b : Fin (m + 2) → Fin L, (∏ i, (((1 + Ξ) (a i) (b i) : ℝ) : ℂ)) =
      ((∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powerset, ∏ i, u S i (b i) : ℝ) : ℂ) := by
    intro b
    rw [← Complex.ofReal_prod]
    congr 1
    rw [← ktens_expand (fun i => Ξ (a i) (b i)) (fun i => if a i = b i then (1 : ℝ) else 0)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Matrix.add_apply, Matrix.one_apply, add_comm]
  have hsum : ∑ b, (∏ i, (((1 + Ξ) (a i) (b i) : ℝ) : ℂ)) * A b =
      ∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powerset,
        ∑ b, ((∏ i, u S i (b i) : ℝ) : ℂ) * A b := by
    simp_rw [hexp]
    push_cast
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  have huniv : (Finset.univ : Finset (Fin (m + 2))) ∈
      (Finset.univ : Finset (Fin (m + 2))).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ _)
  have hB1 := ktens_zero_main Ξ A a R q (q * (2 * (R / ℓv))) ρ hΞ0 hΞent hq0
    (by positivity) hΞrow
    (fun c x y hxy => by
      calc |Ξ c x - Ξ c y| ≤ C₁ * ρ / ℓv * (((cycDist x y : ℝ) + ℓu) / ℓv) := hΞinc c x y
        _ ≤ q * (2 * (R / ℓv)) := by
            apply mul_le_mul_of_nonneg_left _ hq0
            rw [← mul_div_assoc]
            exact div_le_div_of_nonneg_right (by linarith) hℓv.le)
    hR1 hsupp hzero
  have hBo : ∀ S ∈ (Finset.univ : Finset (Fin (m + 2))).powerset.erase Finset.univ,
      ‖∑ b, ((∏ i, u S i (b i) : ℝ) : ℂ) * A b‖ ≤ (⨆ b, ‖A b‖) * Λ ^ (m + 1) := by
    intro S hS
    exact ktens_zero_other Ξ A a R q Λ hΞ0 hΞent hR1 hΛ1 h3 hsupp S (Finset.ne_of_mem_erase hS)
  have hB1' : ‖∑ b, ((∏ i, u Finset.univ i (b i) : ℝ) : ℂ) * A b‖ ≤
      (⨆ b, ‖A b‖) * (2 * ((m + 1) * (3 * C₁) ^ (m + 1)) * Y ^ (m + 2)) := by
    have e1 : ∀ b : Fin (m + 2) → Fin L, ∏ i, u Finset.univ i (b i) = ∏ i, Ξ (a i) (b i) := by
      intro b; simp [hu]
    simp_rw [e1]
    refine hB1.trans (le_of_eq ?_)
    congr 1
    have : ρ * ((m + 1) * q ^ m * (q * (2 * (R / ℓv)))) * (3 * R) ^ (m + 1) =
        2 * ((m + 1) * 3 ^ (m + 1) * (ρ * (R / ℓv)) * (q * R) ^ (m + 1)) := by
      rw [mul_pow, mul_pow]; ring
    rw [this, hρR, mul_comm q R, hRq, mul_pow, mul_pow]
    ring
  rw [hsum, ← Finset.add_sum_erase _ _ huniv]
  have hcard :
      ((Finset.univ : Finset (Fin (m + 2))).powerset.erase Finset.univ).card ≤ 2 ^ (m + 2) := by
    refine (Finset.card_erase_le).trans ?_
    rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  calc ‖∑ b, ((∏ i, u Finset.univ i (b i) : ℝ) : ℂ) * A b +
        ∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powerset.erase Finset.univ,
          ∑ b, ((∏ i, u S i (b i) : ℝ) : ℂ) * A b‖
      ≤ ‖∑ b, ((∏ i, u Finset.univ i (b i) : ℝ) : ℂ) * A b‖ +
        ∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powerset.erase Finset.univ,
          ‖∑ b, ((∏ i, u S i (b i) : ℝ) : ℂ) * A b‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ (⨆ b, ‖A b‖) * (2 * ((m + 1) * (3 * C₁) ^ (m + 1)) * Y ^ (m + 2)) +
        ((Finset.univ : Finset (Fin (m + 2))).powerset.erase Finset.univ).card •
          ((⨆ b, ‖A b‖) * Λ ^ (m + 1)) :=
        add_le_add hB1' (Finset.sum_le_card_nsmul _ _ _ hBo)
    _ ≤ (⨆ b, ‖A b‖) * (2 * ((m + 1) * (3 * C₁) ^ (m + 1)) * Y ^ (m + 2)) +
        2 ^ (m + 2) * ((⨆ b, ‖A b‖) * Λ ^ (m + 1)) := by
        rw [nsmul_eq_mul]
        gcongr
        exact_mod_cast hcard
    _ ≤ (⨆ b, ‖A b‖) * (2 * ((m + 1) * (3 * C₁) ^ (m + 1)) * Y ^ (m + 2)) +
        2 ^ (m + 2) * ((⨆ b, ‖A b‖) * (c₀ ^ (m + 1) * Y ^ (m + 2))) := by
        have hle : Λ ^ (m + 1) ≤ c₀ ^ (m + 1) * Y ^ (m + 2) := by
          rw [hΛ, mul_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 (Nat.le_succ (m + 1)))
            (by positivity)
        gcongr
    _ = (2 ^ (m + 2) * c₀ ^ (m + 1) + 2 * ((m + 1) * (3 * C₁) ^ (m + 1))) * H ^ (m + 2) *
          X ^ (m + 2) * ⨆ b, ‖A b‖ := by
        rw [hY, mul_pow]; ring

end LSBA
