import LSBA.Kernel.Tensor
import LSBA.Loop.Projection
import LSBA.Primitive.Defs

/-!
# Restoration and propagation of truncated tensors

The row bound of a tensor localized at a given diameter, and the propagation (A.74)
[fo:eq:projected-propagation] of a truncated tensor after its zero rows are restored against a
profile at the local scale, for alternating and for other words.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Cyclic distance and words -/

private lemma restore_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma restore_cycDist_comm {L : ℕ} (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

private lemma restore_cycDist_tri {L : ℕ} (a b c : Fin L) :
    cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [cycDist, restore_mod ha hb, restore_mod hb ha, restore_mod ha hc,
    restore_mod hc ha, restore_mod hb hc, restore_mod hc hb]
  split_ifs <;> omega

private lemma restore_cycDist_eq {L : ℕ} [NeZero L] (a b : Fin L) :
    cycDist a b = min (a - b).val (-(a - b)).val := by
  rw [neg_sub]
  unfold cycDist
  rw [Fin.val_sub, Fin.val_sub]
  have ha := a.isLt
  have hb := b.isLt
  have e1 : L - (b : ℕ) + (a : ℕ) = (a : ℕ) + L - (b : ℕ) := by omega
  have e2 : L - (a : ℕ) + (b : ℕ) = (b : ℕ) + L - (a : ℕ) := by omega
  rw [e1, e2]

private lemma restore_le_wordDiam {L k : ℕ} (y : Fin k → Fin L) (i j : Fin k) :
    cycDist (y i) (y j) ≤ wordDiam y :=
  Finset.le_sup (f := fun p : Fin k × Fin k => cycDist (y p.1) (y p.2)) (Finset.mem_univ (i, j))

/-- A word within `R` of a point has diameter at most `2R`. -/
private lemma restore_wordDiam_le {L k : ℕ} (y : Fin k → Fin L) (b : Fin L) (R : ℕ)
    (h : ∀ i, cycDist (y i) b ≤ R) : wordDiam y ≤ 2 * R := by
  refine Finset.sup_le fun p _ => ?_
  have h1 := restore_cycDist_tri (y p.1) b (y p.2)
  rw [restore_cycDist_comm b] at h1
  have := h p.1
  have := h p.2
  omega

/-- A cyclic ball of radius `r` has at most `2r + 1` points. -/
private lemma restore_ball_card {L : ℕ} (β : Fin L) (r : ℕ) :
    (Finset.univ.filter fun x : Fin L => cycDist x β ≤ r).card ≤ 2 * r + 1 := by
  have hβ := β.isLt
  have h1 : (Finset.univ.filter fun x : Fin L => cycDist x β ≤ r).card ≤
      (Finset.range (r + 1) ∪ Finset.Ico (L - r) L).card := by
    refine Finset.card_le_card_of_injOn (fun x : Fin L => (x.val + L - β.val) % L) ?_ ?_
    · intro x hx
      have hx' : cycDist x β ≤ r := by simpa using hx
      have hxl := x.isLt
      simp only [cycDist, restore_mod hxl hβ, restore_mod hβ hxl] at hx'
      simp only [Finset.coe_union, Finset.coe_range, Finset.coe_Ico, Set.mem_union,
        Set.mem_Iio, Set.mem_Ico, restore_mod hxl hβ]
      split_ifs at hx' ⊢ <;> omega
    · intro x _ x' _ hxx
      have hxl := x.isLt
      have hxl' := x'.isLt
      simp only [restore_mod hxl hβ, restore_mod hxl' hβ] at hxx
      apply Fin.ext
      split_ifs at hxx <;> omega
  refine h1.trans ?_
  calc (Finset.range (r + 1) ∪ Finset.Ico (L - r) L).card
      ≤ (Finset.range (r + 1)).card + (Finset.Ico (L - r) L).card := Finset.card_union_le _ _
    _ ≤ (r + 1) + r := by
        rw [Finset.card_range, Nat.card_Ico]
        omega
    _ = 2 * r + 1 := by ring

/-! ### Sums over words with a fixed first label -/

/-- Splitting off the first label of a word. -/
private lemma restore_sum_cons {L k : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin (k + 1) → Fin L) → M) :
    ∑ b, f b = ∑ x : Fin L, ∑ c : Fin k → Fin L, f (Fin.cons x c) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin L)).sum_comp, Fintype.sum_prod_type]
  rfl

/-- Words with a given first label are `L ^ k` in number. -/
private lemma restore_row_count {L k : ℕ} (c : Fin L) :
    ∑ b : Fin (k + 1) → Fin L, (if b 0 = c then (1 : ℝ) else 0) = (L : ℝ) ^ k := by
  rw [restore_sum_cons]
  simp only [Fin.cons_zero]
  simp [Finset.card_univ, Fintype.card_fin]

/-- Bound for a row of a tensor bounded by `δ`. -/
private lemma restore_row_norm_le {L k : ℕ} (F : (Fin (k + 1) → Fin L) → ℂ) (δ : ℝ)
    (hF : ∀ b, ‖F b‖ ≤ δ) (c : Fin L) : ‖rowSum F c‖ ≤ (L : ℝ) ^ k * δ := by
  unfold rowSum
  calc ‖∑ b : Fin (k + 1) → Fin L, if b 0 = c then F b else 0‖
      ≤ ∑ b : Fin (k + 1) → Fin L, ‖if b 0 = c then F b else 0‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin (k + 1) → Fin L, δ * (if b 0 = c then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun b _ => ?_
        split_ifs
        · simpa using hF b
        · have : 0 ≤ δ := le_trans (norm_nonneg _) (hF b)
          simp
    _ = (L : ℝ) ^ k * δ := by
        rw [← Finset.mul_sum, restore_row_count]; ring

/-! ### Product weights -/

/-- A product-weighted sum of a tensor bounded by `δ` is at most `δ` times the product of the
absolute rows of the weights. -/
private lemma restore_prod_bound {L n : ℕ} (w : Fin n → Fin L → ℂ) (D : (Fin n → Fin L) → ℂ)
    (δ : ℝ) (hD : ∀ b, ‖D b‖ ≤ δ) :
    ‖∑ b : Fin n → Fin L, (∏ i, w i (b i)) * D b‖ ≤ δ * ∏ i, ∑ x, ‖w i x‖ := by
  calc ‖∑ b : Fin n → Fin L, (∏ i, w i (b i)) * D b‖
      ≤ ∑ b : Fin n → Fin L, ‖(∏ i, w i (b i)) * D b‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin n → Fin L, (∏ i, ‖w i (b i)‖) * δ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_prod]
        exact mul_le_mul_of_nonneg_left (hD b) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = δ * ∏ i, ∑ x, ‖w i x‖ := by
        rw [← Finset.sum_mul, ← Fintype.prod_sum (fun i x => ‖w i x‖)]; ring

/-! ### The row bound of a localized tensor -/

/-- A signed row of a tensor with entries at most `X`, and at most `τ` above relative diameter
`d`: `|Σ_{b : b_0 = c} F(b)| ≤ (2d + 1)^n X + L^n τ`, the localized absolute sum after (C.34)
[gc:eq:row]. -/
theorem rowSum_le_of_tail {L n : ℕ} (F : (Fin (n + 1) → Fin L) → ℂ) (d X τ : ℝ) (hd : 0 ≤ d)
    (hτ0 : 0 ≤ τ) (hX : ∀ b, ‖F b‖ ≤ X)
    (hτ : ∀ b : Fin (n + 1) → Fin L, d < wordDiam b → ‖F b‖ ≤ τ) (c : Fin L) :
    ‖rowSum F c‖ ≤ (2 * d + 1) ^ n * X + (L : ℝ) ^ n * τ := by
  have hX0 : 0 ≤ X := le_trans (norm_nonneg _) (hX (fun _ => c))
  set near : Finset (Fin (n + 1) → Fin L) :=
    Finset.univ.filter fun b => b 0 = c ∧ ¬ d < (wordDiam b : ℝ) with hnear
  have hcard : (near.card : ℝ) ≤ (2 * d + 1) ^ n := by
    have h1 : near.card ≤ (Fintype.piFinset fun _ : Fin n =>
        Finset.univ.filter fun x : Fin L => cycDist x c ≤ ⌊d⌋₊).card := by
      refine Finset.card_le_card_of_injOn (fun b j => b j.succ) ?_ ?_
      · intro b hb
        simp only [hnear, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb
        rw [Finset.mem_coe, Fintype.mem_piFinset]
        intro j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have h1 := restore_le_wordDiam b j.succ 0
        rw [hb.1] at h1
        refine Nat.le_floor ?_
        have : ((cycDist (b j.succ) c : ℕ) : ℝ) ≤ (wordDiam b : ℝ) := by exact_mod_cast h1
        exact this.trans (not_lt.mp hb.2)
      · intro b hb b' hb' hbb
        simp only [hnear, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
        funext j
        refine Fin.cases ?_ (fun j => ?_) j
        · rw [hb.1, hb'.1]
        · exact congrFun hbb j
    rw [Fintype.card_piFinset] at h1
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ((Finset.univ.filter fun x : Fin L => cycDist x c ≤ ⌊d⌋₊).card : ℝ) ≤
        2 * d + 1 := by
      have := restore_ball_card c ⌊d⌋₊
      have h3 : (⌊d⌋₊ : ℝ) ≤ d := Nat.floor_le hd
      have : ((Finset.univ.filter fun x : Fin L => cycDist x c ≤ ⌊d⌋₊).card : ℝ) ≤
          2 * (⌊d⌋₊ : ℝ) + 1 := by exact_mod_cast this
      linarith
    calc (near.card : ℝ)
        ≤ (((Finset.univ.filter fun x : Fin L => cycDist x c ≤ ⌊d⌋₊).card ^ n : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ = ((Finset.univ.filter fun x : Fin L => cycDist x c ≤ ⌊d⌋₊).card : ℝ) ^ n := by
          push_cast; rfl
      _ ≤ (2 * d + 1) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 n
  unfold rowSum
  calc ‖∑ b : Fin (n + 1) → Fin L, if b 0 = c then F b else 0‖
      ≤ ∑ b : Fin (n + 1) → Fin L, ‖if b 0 = c then F b else 0‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin (n + 1) → Fin L,
          (X * (if b ∈ near then (1 : ℝ) else 0) + τ * (if b 0 = c then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum fun b _ => ?_
        by_cases hb : b 0 = c
        · by_cases hn : d < (wordDiam b : ℝ)
          · have hnb : b ∉ near := by simp [hnear, hn]
            simp only [hb, hnb, ite_true, ite_false]
            have := hτ b hn
            linarith
          · have hnb : b ∈ near := by
              simp only [hnear, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hb, hn⟩
            simp only [hb, hnb, ite_true]
            have := hX b
            nlinarith
        · have : 0 ≤ X * (if b ∈ near then (1 : ℝ) else 0) + τ * (if b 0 = c then (1 : ℝ) else 0) := by
            positivity
          simpa [hb] using this
    _ = X * (near.card : ℝ) + τ * (L : ℝ) ^ n := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, restore_row_count]
        simp
    _ ≤ (2 * d + 1) ^ n * X + (L : ℝ) ^ n * τ := by
        have := mul_le_mul_of_nonneg_left hcard hX0
        nlinarith

/-! ### Truncation at a relative diameter -/

/-- The part of a tensor on words of relative diameter above `R`. -/
private def restoreTail {L n : ℕ} (A : (Fin n → Fin L) → ℂ) (R : ℝ) : (Fin n → Fin L) → ℂ :=
  fun b => if R < (wordDiam b : ℝ) then A b else 0

private lemma restoreTail_norm_le_tau {L n : ℕ} (A : (Fin n → Fin L) → ℂ) (R τ : ℝ) (hτ0 : 0 ≤ τ)
    (htail : ∀ b : Fin n → Fin L, R < wordDiam b → ‖A b‖ ≤ τ) (b : Fin n → Fin L) :
    ‖restoreTail A R b‖ ≤ τ := by
  unfold restoreTail; split_ifs with h
  · exact htail b h
  · simpa using hτ0

/-- The truncated tensor `A - restoreTail A R` vanishes on words with two labels at distance
above `R`. -/
private lemma restoreTail_supp {L n : ℕ} (A : (Fin n → Fin L) → ℂ) (R : ℝ)
    (b : Fin n → Fin L) (h : ∃ i j, R < cycDist (b i) (b j)) : A b - restoreTail A R b = 0 := by
  obtain ⟨i, j, hij⟩ := h
  have h1 : R < (wordDiam b : ℝ) := by
    have : (cycDist (b i) (b j) : ℝ) ≤ (wordDiam b : ℝ) := by
      exact_mod_cast restore_le_wordDiam b i j
    exact lt_of_lt_of_le hij this
  simp [restoreTail, h1]

private lemma restoreTail_iSup_le {L n : ℕ} (A : (Fin n → Fin L) → ℂ) (R : ℝ)
    [Nonempty (Fin n → Fin L)] : ⨆ b, ‖A b - restoreTail A R b‖ ≤ ⨆ b, ‖A b‖ := by
  refine ciSup_le fun b => ?_
  refine le_trans ?_ (le_ciSup (Finite.bddAbove_range fun b => ‖A b‖) b)
  unfold restoreTail; split_ifs <;> simp

/-! ### Propagation with a stable leg -/

/-- (A.74) [fo:eq:projected-propagation], case of at least one stable leg, for a tensor whose
entries of relative diameter above `Hℓ_u` are at most `τ`: the discarded tail is propagated by the
rows of the legs, at cost `((1 + ρ)L/ℓ_u)^n τ`. -/
theorem restore_stableLeg (n : ℕ) (hn : 2 ≤ n) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (L : ℕ) (U : Fin n → Matrix (Fin L) (Fin L) ℂ)
      (A : (Fin n → Fin L) → ℂ) (ρ ℓu ℓv H τ : ℝ) (i₀ : Fin n),
      (∀ i, (∀ a, ∑ b, ‖U i a b‖ ≤ C₁) ∨
        ∀ a b, ‖U i a b - (1 : Matrix (Fin L) (Fin L) ℂ) a b‖ ≤ C₁ * ρ / ℓv) →
      (∀ a, ∑ b, ‖U i₀ a b‖ ≤ C₁) →
      1 ≤ ℓu → ℓu ≤ ℓv → ℓu ≤ L → 1 ≤ H → 1 ≤ ρ * ℓu / ℓv → 0 ≤ τ →
      (∀ b : Fin n → Fin L, H * ℓu < wordDiam b → ‖A b‖ ≤ τ) →
      ∀ a : Fin n → Fin L,
        ‖∑ b : Fin n → Fin L, (∏ i, U i (a i) (b i)) * A b‖ ≤
          Cn * H ^ (n - 1) * (ρ * ℓu / ℓv) ^ (n - 1) * (⨆ b, ‖A b‖) +
            Cn * ((1 + ρ) * (L / ℓu)) ^ n * τ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨Cn₀, hCn₀, hmain⟩ := projected_stableLeg (k + 1) hn C₁ hC₁
  refine ⟨Cn₀ + (1 + C₁) ^ (k + 1) + 1, by positivity, ?_⟩
  intro L U A ρ ℓu ℓv H τ i₀ hleg hi₀ h1u huv huL hH hX hτ0 htail a
  simp only [Nat.add_sub_cancel]
  have : Nonempty (Fin (k + 1) → Fin L) := ⟨a⟩
  have hℓu : 0 < ℓu := by linarith
  have hℓv : 0 < ℓv := by linarith
  have hρ : 0 < ρ := by
    by_contra hρ
    push Not at hρ
    have : ρ * ℓu / ℓv ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hρ (by linarith)) hℓv.le
    linarith
  set Q : ℝ := (L : ℝ) / ℓu with hQdef
  have hQ1 : 1 ≤ Q := (one_le_div hℓu).mpr huL
  have hrow : ∀ i, ∑ x, ‖U i (a i) x‖ ≤ (1 + C₁) * ((1 + ρ) * Q) := by
    intro i
    rcases hleg i with h | h
    · calc ∑ x, ‖U i (a i) x‖ ≤ C₁ := h (a i)
        _ ≤ (1 + C₁) * ((1 + ρ) * Q) := by
            nlinarith [mul_nonneg hC₁.le hρ.le, mul_nonneg hC₁.le (sub_nonneg.mpr hQ1),
              mul_nonneg hρ.le (sub_nonneg.mpr hQ1), mul_nonneg (mul_nonneg hC₁.le hρ.le)
                (sub_nonneg.mpr hQ1)]
    · have h1 : ∑ x, ‖U i (a i) x‖ ≤
          ∑ x, (‖(1 : Matrix (Fin L) (Fin L) ℂ) (a i) x‖ + C₁ * ρ / ℓv) := by
        refine Finset.sum_le_sum fun x _ => ?_
        have := norm_le_insert' (U i (a i) x) ((1 : Matrix (Fin L) (Fin L) ℂ) (a i) x)
        linarith [h (a i) x]
      have h2 : ∑ x, (‖(1 : Matrix (Fin L) (Fin L) ℂ) (a i) x‖ + C₁ * ρ / ℓv) =
          1 + (L : ℝ) * (C₁ * ρ / ℓv) := by
        have hn1 : ∀ x, ‖(1 : Matrix (Fin L) (Fin L) ℂ) (a i) x‖ = if a i = x then 1 else 0 := by
          intro x; by_cases hx : a i = x <;> simp [Matrix.one_apply, hx]
        simp only [Finset.sum_add_distrib, hn1, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h3 : (L : ℝ) * (C₁ * ρ / ℓv) ≤ C₁ * ρ * Q := by
        have : (L : ℝ) / ℓv ≤ (L : ℝ) / ℓu :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) hℓu huv
        calc (L : ℝ) * (C₁ * ρ / ℓv) = C₁ * ρ * ((L : ℝ) / ℓv) := by ring
          _ ≤ C₁ * ρ * Q := mul_le_mul_of_nonneg_left this (by positivity)
      nlinarith [mul_nonneg hC₁.le hρ.le, mul_nonneg hC₁.le (sub_nonneg.mpr hQ1),
        mul_nonneg hρ.le (sub_nonneg.mpr hQ1)]
  have hmainA := hmain L U (fun b => A b - restoreTail A (H * ℓu) b) ρ ℓu ℓv H i₀ hleg hi₀ h1u huv
    hH hX (fun b hb => restoreTail_supp A (H * ℓu) b hb) a
  simp only [Nat.add_sub_cancel] at hmainA
  have hS := restoreTail_iSup_le A (H * ℓu)
  have hS0 : 0 ≤ ⨆ b, ‖A b‖ := Real.iSup_nonneg fun b => norm_nonneg _
  have hPos : 0 ≤ H ^ k * (ρ * ℓu / ℓv) ^ k * ⨆ b, ‖A b‖ := by
    have : 0 ≤ ρ * ℓu / ℓv := by positivity
    have : 0 ≤ H := by linarith
    positivity
  have htailb : ‖∑ b : Fin (k + 1) → Fin L, (∏ i, U i (a i) (b i)) *
      restoreTail A (H * ℓu) b‖ ≤ τ * ∏ i, ∑ x, ‖U i (a i) x‖ :=
    restore_prod_bound (fun i x => U i (a i) x) (restoreTail A (H * ℓu)) τ
    (fun b => restoreTail_norm_le_tau A (H * ℓu) τ hτ0 htail b)
  have hprod : ∏ i, ∑ x, ‖U i (a i) x‖ ≤ ((1 + C₁) * ((1 + ρ) * Q)) ^ (k + 1) := by
    calc ∏ i, ∑ x, ‖U i (a i) x‖ ≤ ∏ _i : Fin (k + 1), (1 + C₁) * ((1 + ρ) * Q) :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun x _ => norm_nonneg _)
            (fun i _ => hrow i)
      _ = ((1 + C₁) * ((1 + ρ) * Q)) ^ (k + 1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsplit : ∑ b : Fin (k + 1) → Fin L, (∏ i, U i (a i) (b i)) * A b =
      ∑ b : Fin (k + 1) → Fin L, (∏ i, U i (a i) (b i)) * (A b - restoreTail A (H * ℓu) b) +
      ∑ b : Fin (k + 1) → Fin L, (∏ i, U i (a i) (b i)) * restoreTail A (H * ℓu) b := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hE : 0 ≤ (1 + C₁) ^ (k + 1) := by positivity
  have hP2 : 0 ≤ ((1 + ρ) * Q) ^ (k + 1) * τ := by positivity
  have h2 : τ * ((1 + C₁) * ((1 + ρ) * Q)) ^ (k + 1) =
      (1 + C₁) ^ (k + 1) * (((1 + ρ) * Q) ^ (k + 1) * τ) := by rw [mul_pow]; ring
  have e1 : (Cn₀ + (1 + C₁) ^ (k + 1) + 1) * H ^ k * (ρ * ℓu / ℓv) ^ k * (⨆ b, ‖A b‖) =
      Cn₀ * H ^ k * (ρ * ℓu / ℓv) ^ k * (⨆ b, ‖A b‖) +
        (1 + C₁) ^ (k + 1) * (H ^ k * (ρ * ℓu / ℓv) ^ k * (⨆ b, ‖A b‖)) +
        (H ^ k * (ρ * ℓu / ℓv) ^ k * (⨆ b, ‖A b‖)) := by ring
  have e2 : (Cn₀ + (1 + C₁) ^ (k + 1) + 1) * ((1 + ρ) * Q) ^ (k + 1) * τ =
      Cn₀ * (((1 + ρ) * Q) ^ (k + 1) * τ) +
        (1 + C₁) ^ (k + 1) * (((1 + ρ) * Q) ^ (k + 1) * τ) + (((1 + ρ) * Q) ^ (k + 1) * τ) := by
    ring
  calc ‖∑ b : Fin (k + 1) → Fin L, (∏ i, U i (a i) (b i)) * A b‖
      ≤ ‖∑ b : Fin (k + 1) → Fin L, (∏ i, U i (a i) (b i)) *
          (A b - restoreTail A (H * ℓu) b)‖ +
        ‖∑ b : Fin (k + 1) → Fin L, (∏ i, U i (a i) (b i)) * restoreTail A (H * ℓu) b‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ Cn₀ * H ^ k * (ρ * ℓu / ℓv) ^ k * (⨆ b, ‖A b‖) +
        τ * ((1 + C₁) * ((1 + ρ) * Q)) ^ (k + 1) := by
        refine add_le_add ?_ (htailb.trans (mul_le_mul_of_nonneg_left hprod hτ0))
        have : 0 ≤ Cn₀ * H ^ k * (ρ * ℓu / ℓv) ^ k := by
          have : 0 ≤ ρ * ℓu / ℓv := by positivity
          have : 0 ≤ H := by linarith
          positivity
        exact hmainA.trans (mul_le_mul_of_nonneg_left hS this)
    _ ≤ (Cn₀ + (1 + C₁) ^ (k + 1) + 1) * H ^ k * (ρ * ℓu / ℓv) ^ k * (⨆ b, ‖A b‖) +
        (Cn₀ + (1 + C₁) ^ (k + 1) + 1) * ((1 + ρ) * Q) ^ (k + 1) * τ := by
        rw [h2, e1, e2]
        linarith [mul_nonneg hE hPos, mul_nonneg hCn₀.le hP2, hPos, hP2]

/-! ### Restoration of a zero row -/

/-- A probability profile on `ℤ_L` at scale `ℓ_u`: uniform on an arc of `⌊ℓ_u/2⌋ + 1` points
starting at the anchor, so entries are at most `2/ℓ_u` and the support is within `⌊ℓ_u/2⌋` of the
anchor. -/
private lemma restore_profile {L : ℕ} [NeZero L] (ℓu : ℝ) (h1u : 1 ≤ ℓu) (huL : ℓu ≤ L) :
    ∃ P : Fin L → Fin L → ℝ, (∀ β x, 0 ≤ P β x) ∧ (∀ β x, P β x ≤ 2 / ℓu) ∧
      (∀ β, ∑ x, P β x = 1) ∧ (∀ β x, P β x ≠ 0 → cycDist x β ≤ ⌊ℓu / 2⌋₊) := by
  have hℓu : 0 < ℓu := by linarith
  have hL1 : 1 ≤ L := Nat.pos_of_neZero L
  set N : ℕ := min (⌊ℓu / 2⌋₊ + 1) L with hNdef
  have hN1 : 1 ≤ N := le_min (by omega) hL1
  have hNL : N ≤ L := min_le_right _ _
  have hNup : N ≤ ⌊ℓu / 2⌋₊ + 1 := min_le_left _ _
  have hNge : ℓu / 2 ≤ (N : ℝ) := by
    rw [hNdef, Nat.cast_min]
    refine le_min ?_ ?_
    · have := Nat.lt_floor_add_one (ℓu / 2)
      push_cast
      linarith
    · linarith
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN1
  refine ⟨fun β x => if (x - β).val < N then 1 / (N : ℝ) else 0, ?_, ?_, ?_, ?_⟩
  · intro β x
    dsimp only
    split_ifs <;> positivity
  · intro β x
    dsimp only
    split_ifs
    · rw [div_le_div_iff₀ hNpos hℓu]
      linarith
    · positivity
  · intro β
    dsimp only
    rw [Fintype.sum_equiv (Equiv.subRight β) _ (fun y : Fin L => if y.val < N then 1 / (N : ℝ) else 0)
      (fun x => by simp)]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < N then 1 / (N : ℝ) else 0) L,
      ← Finset.sum_filter]
    have : Finset.filter (fun i => i < N) (Finset.range L) = Finset.range N := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  · intro β x hx
    dsimp only at hx
    have hlt : (x - β).val < N := by
      by_contra h; simp [h] at hx
    rw [restore_cycDist_eq]
    have := min_le_left (x - β).val (-(x - β)).val
    omega

/-- The sum of a product of a function of the first label and functions of the other labels. -/
private lemma restore_cor_row {L k : ℕ} (r : Fin L → ℂ) (P : Fin L → Fin L → ℝ)
    (hP : ∀ β, ∑ x, P β x = 1) (c : Fin L) :
    ∑ b : Fin (k + 1) → Fin L, (if b 0 = c then
      r (b 0) * ∏ j : Fin k, ((P (b 0) (b j.succ) : ℝ) : ℂ) else 0) = r c := by
  rw [restore_sum_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Finset.sum_eq_single c]
  · simp only [ite_true]
    rw [← Finset.mul_sum]
    have h1 : ∑ c' : Fin k → Fin L, ∏ j : Fin k, ((P c (c' j) : ℝ) : ℂ) =
        (∑ y, ((P c y : ℝ) : ℂ)) ^ k := (Fintype.sum_pow (fun y => ((P c y : ℝ) : ℂ)) k).symm
    rw [h1, ← Complex.ofReal_sum, hP c]
    simp
  · intro x _ hx
    simp [hx]
  · simp

/-- Arithmetic of the restoration estimate. -/
private lemma restore_zero_arith (k : ℕ) (Cn₀ H X ρ Q τ S : ℝ) (hC : 0 ≤ Cn₀) (hH : 1 ≤ H)
    (hX0 : 0 ≤ X) (hXρ : X ≤ ρ) (hρ : 0 ≤ ρ) (hQ : 1 ≤ Q) (hτ : 0 ≤ τ) (hS : 0 ≤ S) :
    Cn₀ * H ^ (k + 1) * X ^ (k + 1) * (S + (2 * Q) ^ k * τ) +
        (τ + (2 * Q) ^ k * τ) * (1 + ρ) ^ (k + 1) ≤
      2 ^ (k + 1) * (Cn₀ + 1) * H ^ (k + 1) * X ^ (k + 1) * S +
        2 ^ (k + 1) * (Cn₀ + 1) * (H * (1 + ρ) * Q) ^ (2 * (k + 1)) * τ := by
  set Λ := H * (1 + ρ) * Q with hΛ
  have hH0 : 0 ≤ H := by linarith
  have hΛ1 : 1 ≤ Λ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hH (by linarith)) hQ
  have hQk : 1 ≤ Q ^ k := one_le_pow₀ hQ
  have hQk1 : Q ^ k ≤ Q ^ (k + 1) := pow_le_pow_right₀ hQ (Nat.le_succ k)
  have hQk1' : 1 ≤ Q ^ (k + 1) := one_le_pow₀ hQ
  have hHk : 1 ≤ H ^ (k + 1) := one_le_pow₀ hH
  have hc2 : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hΛ0 : 0 ≤ Λ ^ (k + 1) := by positivity
  have a1 : H ^ (k + 1) * X ^ (k + 1) * Q ^ k ≤ Λ ^ (k + 1) := by
    calc H ^ (k + 1) * X ^ (k + 1) * Q ^ k ≤ H ^ (k + 1) * (1 + ρ) ^ (k + 1) * Q ^ (k + 1) := by
          have : X ^ (k + 1) ≤ (1 + ρ) ^ (k + 1) := pow_le_pow_left₀ hX0 (by linarith) _
          gcongr
      _ = Λ ^ (k + 1) := by rw [hΛ, mul_pow, mul_pow]
  have a2 : (1 + ρ) ^ (k + 1) * (1 + 2 ^ k * Q ^ k) ≤ (1 + 2 ^ k) * Λ ^ (k + 1) := by
    have h1 : 1 + 2 ^ k * Q ^ k ≤ (1 + 2 ^ k) * Q ^ (k + 1) := by
      have : (2 : ℝ) ^ k * Q ^ k ≤ 2 ^ k * Q ^ (k + 1) := by gcongr
      linarith
    have h2 : (1 + ρ) ^ (k + 1) * Q ^ (k + 1) ≤ Λ ^ (k + 1) := by
      rw [hΛ, mul_pow, mul_pow]
      have : 0 ≤ (1 + ρ) ^ (k + 1) * Q ^ (k + 1) := by positivity
      nlinarith
    calc (1 + ρ) ^ (k + 1) * (1 + 2 ^ k * Q ^ k)
        ≤ (1 + ρ) ^ (k + 1) * ((1 + 2 ^ k) * Q ^ (k + 1)) := by gcongr
      _ = (1 + 2 ^ k) * ((1 + ρ) ^ (k + 1) * Q ^ (k + 1)) := by ring
      _ ≤ (1 + 2 ^ k) * Λ ^ (k + 1) := by gcongr
  have hΛpow : Λ ^ (k + 1) * τ ≤ Λ ^ (2 * (k + 1)) * τ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hΛ1 (by omega)) hτ
  have hu0 : 0 ≤ Λ ^ (k + 1) * τ := by positivity
  have hPS : 0 ≤ H ^ (k + 1) * X ^ (k + 1) * S := by positivity
  have t2 : Cn₀ * H ^ (k + 1) * X ^ (k + 1) * ((2 * Q) ^ k * τ) ≤
      Cn₀ * 2 ^ k * (Λ ^ (k + 1) * τ) := by
    have : Cn₀ * H ^ (k + 1) * X ^ (k + 1) * ((2 * Q) ^ k * τ) =
        Cn₀ * 2 ^ k * ((H ^ (k + 1) * X ^ (k + 1) * Q ^ k) * τ) := by rw [mul_pow]; ring
    rw [this]
    gcongr
  have t3 : (τ + (2 * Q) ^ k * τ) * (1 + ρ) ^ (k + 1) ≤ (1 + 2 ^ k) * (Λ ^ (k + 1) * τ) := by
    have : (τ + (2 * Q) ^ k * τ) * (1 + ρ) ^ (k + 1) =
        τ * ((1 + ρ) ^ (k + 1) * (1 + 2 ^ k * Q ^ k)) := by rw [mul_pow]; ring
    rw [this]
    calc τ * ((1 + ρ) ^ (k + 1) * (1 + 2 ^ k * Q ^ k)) ≤ τ * ((1 + 2 ^ k) * Λ ^ (k + 1)) := by
          gcongr
      _ = (1 + 2 ^ k) * (Λ ^ (k + 1) * τ) := by ring
  have e0 : Cn₀ * H ^ (k + 1) * X ^ (k + 1) * (S + (2 * Q) ^ k * τ) =
      Cn₀ * (H ^ (k + 1) * X ^ (k + 1) * S) + Cn₀ * H ^ (k + 1) * X ^ (k + 1) * ((2 * Q) ^ k * τ) := by
    ring
  have e1 : (2 : ℝ) ^ (k + 1) * (Cn₀ + 1) * H ^ (k + 1) * X ^ (k + 1) * S =
      2 ^ (k + 1) * (Cn₀ + 1) * (H ^ (k + 1) * X ^ (k + 1) * S) := by ring
  have e2 : (2 : ℝ) ^ (k + 1) * (Cn₀ + 1) * (H * (1 + ρ) * Q) ^ (2 * (k + 1)) * τ =
      2 ^ (k + 1) * (Cn₀ + 1) * (Λ ^ (2 * (k + 1)) * τ) := by rw [hΛ]; ring
  have hp : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  rw [e0, e1, e2, hp]
  have f1 : 0 ≤ (2 ^ k * 2 * (Cn₀ + 1) - Cn₀) * (H ^ (k + 1) * X ^ (k + 1) * S) :=
    mul_nonneg (by nlinarith) hPS
  have f2 : 0 ≤ (2 ^ k * 2 * (Cn₀ + 1) - Cn₀ * 2 ^ k - 1 - 2 ^ k) * (Λ ^ (2 * (k + 1)) * τ) :=
    mul_nonneg (by nlinarith) (le_trans hu0 hΛpow)
  have f3 : (Cn₀ * 2 ^ k + 1 + 2 ^ k) * (Λ ^ (k + 1) * τ) ≤
      (Cn₀ * 2 ^ k + 1 + 2 ^ k) * (Λ ^ (2 * (k + 1)) * τ) :=
    mul_le_mul_of_nonneg_left hΛpow (by positivity)
  linarith

/-- (A.74) [fo:eq:projected-propagation], zero-row case, for a tensor with a zero first row whose
entries of relative diameter above `Hℓ_u` are at most `τ`: the tensor is truncated at `Hℓ_u` and
its row is restored against a normalized profile at scale `ℓ_u`, as in the truncation check after
(C.35) [fo:eq:projected-error-equation]; the truncation costs `(H(1 + ρ)L/ℓ_u)^{2n} τ`. -/
theorem restore_zeroRow (n : ℕ) (hn : 2 ≤ n) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (L : ℕ) (Ξ : Matrix (Fin L) (Fin L) ℝ) (A : (Fin n → Fin L) → ℂ)
      (ρ ℓu ℓv H τ : ℝ), (∀ a b, 0 ≤ Ξ a b) → (∀ a, ∑ b, Ξ a b ≤ ρ) →
      (∀ a b, Ξ a b ≤ C₁ * ρ / ℓv) →
      (∀ a b b', |Ξ a b - Ξ a b'| ≤ C₁ * ρ / ℓv * (((cycDist b b' : ℝ) + ℓu) / ℓv)) →
      1 ≤ ℓu → ℓu ≤ ℓv → ℓu ≤ L → 1 ≤ H → 1 ≤ ρ * ℓu / ℓv → 0 ≤ τ →
      (∀ b : Fin n → Fin L, H * ℓu < wordDiam b → ‖A b‖ ≤ τ) →
      (∀ b₁ : Fin L, ∑ b : Fin n → Fin L, (if b ⟨0, by omega⟩ = b₁ then A b else 0) = 0) →
      ∀ a : Fin n → Fin L,
        ‖∑ b : Fin n → Fin L, (∏ i, (((1 + Ξ) (a i) (b i) : ℝ) : ℂ)) * A b‖ ≤
          Cn * H ^ n * (ρ * ℓu / ℓv) ^ n * (⨆ b, ‖A b‖) +
            Cn * (H * (1 + ρ) * (L / ℓu)) ^ (2 * n) * τ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨Cn₀, hCn₀, hmain⟩ := projected_zeroRow' (k + 1) hn C₁ hC₁
  refine ⟨2 ^ (k + 1) * (Cn₀ + 1), by positivity, ?_⟩
  intro L Ξ A ρ ℓu ℓv H τ hΞ0 hΞrow hΞent hΞinc h1u huv huL hH hX hτ0 htail hzero a
  have : NeZero L := ⟨by rintro rfl; exact (a 0).elim0⟩
  have : Nonempty (Fin (k + 1) → Fin L) := ⟨a⟩
  have hℓu : 0 < ℓu := by linarith
  have hℓv : 0 < ℓv := by linarith
  have hρ : 0 < ρ := by
    by_contra hρ
    push Not at hρ
    have : ρ * ℓu / ℓv ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hρ (by linarith)) hℓv.le
    linarith
  have hH0 : 0 ≤ H := by linarith
  set X : ℝ := ρ * ℓu / ℓv with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hXρ : X ≤ ρ := by
    rw [hXdef, div_le_iff₀ hℓv]
    nlinarith
  set Q : ℝ := (L : ℝ) / ℓu with hQdef
  have hQ1 : 1 ≤ Q := (one_le_div hℓu).mpr huL
  set S : ℝ := ⨆ b, ‖A b‖ with hSdef
  have hS0 : 0 ≤ S := Real.iSup_nonneg fun b => norm_nonneg _
  have hAS : ∀ b, ‖A b‖ ≤ S := fun b => le_ciSup (Finite.bddAbove_range fun b => ‖A b‖) b
  -- the truncation and its row
  set T := restoreTail A (H * ℓu) with hT
  have hTτ : ∀ b, ‖T b‖ ≤ τ := fun b => restoreTail_norm_le_tau A (H * ℓu) τ hτ0 htail b
  set AH : (Fin (k + 1) → Fin L) → ℂ := fun b => A b - T b with hAH
  set r : Fin L → ℂ := rowSum AH with hr
  have hrow_sub : ∀ c, rowSum AH c = rowSum A c - rowSum T c := by
    intro c
    unfold rowSum
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp [hAH]
  have hrA : ∀ c, rowSum A c = 0 := fun c => hzero c
  have hr_norm : ∀ c, ‖r c‖ ≤ (L : ℝ) ^ k * τ := by
    intro c
    have h1 := restore_row_norm_le T τ hTτ c
    have h2 : r c = - rowSum T c := by rw [hr, hrow_sub, hrA]; ring
    rw [h2, norm_neg]
    exact h1
  -- the profile
  obtain ⟨P, hP0, hPle, hPsum, hPsupp⟩ := restore_profile (L := L) ℓu h1u huL
  set Cor : (Fin (k + 1) → Fin L) → ℂ := fun b =>
    r (b 0) * ∏ j : Fin k, ((P (b 0) (b j.succ) : ℝ) : ℂ) with hCor
  set A' : (Fin (k + 1) → Fin L) → ℂ := fun b => AH b - Cor b with hA'
  have hCor_norm : ∀ b, ‖Cor b‖ ≤ (2 * Q) ^ k * τ := by
    intro b
    have h1 : ‖∏ j : Fin k, ((P (b 0) (b j.succ) : ℝ) : ℂ)‖ ≤ (2 / ℓu) ^ k := by
      rw [norm_prod]
      calc ∏ j : Fin k, ‖((P (b 0) (b j.succ) : ℝ) : ℂ)‖ ≤ ∏ _j : Fin k, (2 / ℓu) := by
            refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP0 _ _)]
            exact hPle _ _
        _ = (2 / ℓu) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc ‖Cor b‖ = ‖r (b 0)‖ * ‖∏ j : Fin k, ((P (b 0) (b j.succ) : ℝ) : ℂ)‖ := norm_mul _ _
      _ ≤ ((L : ℝ) ^ k * τ) * (2 / ℓu) ^ k :=
          mul_le_mul (hr_norm _) h1 (norm_nonneg _) (by positivity)
      _ = (2 * Q) ^ k * τ := by
          have : 2 * Q = (L : ℝ) * (2 / ℓu) := by rw [hQdef]; ring
          rw [this, mul_pow]; ring
  have hCor_row : ∀ c, ∑ b : Fin (k + 1) → Fin L, (if b 0 = c then Cor b else 0) = r c :=
    fun c => restore_cor_row r P hPsum c
  have hA'row : ∀ b₁ : Fin L, ∑ b : Fin (k + 1) → Fin L,
      (if b ⟨0, by omega⟩ = b₁ then A' b else 0) = 0 := by
    intro b₁
    have : ∑ b : Fin (k + 1) → Fin L, (if b 0 = b₁ then A' b else 0) =
        rowSum AH b₁ - ∑ b : Fin (k + 1) → Fin L, (if b 0 = b₁ then Cor b else 0) := by
      unfold rowSum
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp [hA']
    change ∑ b : Fin (k + 1) → Fin L, (if b 0 = b₁ then A' b else 0) = 0
    rw [this, hCor_row]
    simp [hr]
  have hA'supp : ∀ b : Fin (k + 1) → Fin L, (∃ i j, H * ℓu < cycDist (b i) (b j)) → A' b = 0 := by
    intro b hb
    have h1 : AH b = 0 := restoreTail_supp A (H * ℓu) b hb
    have h2 : Cor b = 0 := by
      by_contra hne
      have hne' : ∏ j : Fin k, ((P (b 0) (b j.succ) : ℝ) : ℂ) ≠ 0 := fun h => hne (by simp [hCor, h])
      have hj : ∀ j : Fin k, cycDist (b j.succ) (b 0) ≤ ⌊ℓu / 2⌋₊ := by
        intro j
        refine hPsupp _ _ ?_
        intro h0
        exact hne' (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [h0]))
      have hall : ∀ i : Fin (k + 1), cycDist (b i) (b 0) ≤ ⌊ℓu / 2⌋₊ := by
        intro i
        refine Fin.cases ?_ (fun j => hj j) i
        simp [cycDist]
      have hd := restore_wordDiam_le b (b 0) _ hall
      obtain ⟨i, j, hij⟩ := hb
      have h3 : (cycDist (b i) (b j) : ℝ) ≤ (wordDiam b : ℝ) := by
        exact_mod_cast restore_le_wordDiam b i j
      have h4 : (wordDiam b : ℝ) ≤ 2 * (⌊ℓu / 2⌋₊ : ℝ) := by exact_mod_cast hd
      have h5 : (⌊ℓu / 2⌋₊ : ℝ) ≤ ℓu / 2 := Nat.floor_le (by linarith)
      nlinarith
    simp [hA', h1, h2]
  have hA'norm : ∀ b, ‖A' b‖ ≤ S + (2 * Q) ^ k * τ := by
    intro b
    calc ‖A' b‖ ≤ ‖AH b‖ + ‖Cor b‖ := norm_sub_le _ _
      _ ≤ S + (2 * Q) ^ k * τ := by
          refine add_le_add ?_ (hCor_norm b)
          refine le_trans ?_ (hAS b)
          simp only [hAH, hT, restoreTail]
          split_ifs <;> simp
  have hSA' : ⨆ b, ‖A' b‖ ≤ S + (2 * Q) ^ k * τ := ciSup_le hA'norm
  have hmainA := hmain L Ξ A' ρ ℓu ℓv H hΞ0 hΞrow hΞent hΞinc h1u huv hH hX hA'supp hA'row a
  -- the discarded part
  have hD : ∀ b, ‖A b - A' b‖ ≤ τ + (2 * Q) ^ k * τ := by
    intro b
    have : A b - A' b = T b + Cor b := by simp only [hA', hAH]; ring
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add (hTτ b) (hCor_norm b))
  have hW0 : ∀ x y, 0 ≤ (1 + Ξ) x y := by
    intro x y
    rw [Matrix.add_apply, Matrix.one_apply]
    split_ifs <;> linarith [hΞ0 x y]
  have hWrow : ∀ i : Fin (k + 1), ∑ x, ‖(((1 + Ξ) (a i) x : ℝ) : ℂ)‖ ≤ 1 + ρ := by
    intro i
    have h1 : ∀ x, ‖(((1 + Ξ) (a i) x : ℝ) : ℂ)‖ = (1 + Ξ) (a i) x := by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW0 _ _)]
    have h2 : ∀ x, (1 + Ξ) (a i) x = (if a i = x then (1 : ℝ) else 0) + Ξ (a i) x := fun x => by
      rw [Matrix.add_apply, Matrix.one_apply]
    rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_congr rfl fun x _ => h2 x,
      Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    linarith [hΞrow (a i)]
  have hprodW : ∏ i : Fin (k + 1), ∑ x, ‖(((1 + Ξ) (a i) x : ℝ) : ℂ)‖ ≤ (1 + ρ) ^ (k + 1) := by
    calc ∏ i : Fin (k + 1), ∑ x, ‖(((1 + Ξ) (a i) x : ℝ) : ℂ)‖
        ≤ ∏ _i : Fin (k + 1), (1 + ρ) :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun x _ => norm_nonneg _)
            (fun i _ => hWrow i)
      _ = (1 + ρ) ^ (k + 1) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hDsum : ‖∑ b : Fin (k + 1) → Fin L, (∏ i, (((1 + Ξ) (a i) (b i) : ℝ) : ℂ)) *
      (A b - A' b)‖ ≤ (τ + (2 * Q) ^ k * τ) * ∏ i : Fin (k + 1), ∑ x,
        ‖(((1 + Ξ) (a i) x : ℝ) : ℂ)‖ :=
    restore_prod_bound (fun i x => (((1 + Ξ) (a i) x : ℝ) : ℂ)) (fun b => A b - A' b) _ hD
  have hsplit : ∑ b : Fin (k + 1) → Fin L, (∏ i, (((1 + Ξ) (a i) (b i) : ℝ) : ℂ)) * A b =
      ∑ b : Fin (k + 1) → Fin L, (∏ i, (((1 + Ξ) (a i) (b i) : ℝ) : ℂ)) * A' b +
      ∑ b : Fin (k + 1) → Fin L, (∏ i, (((1 + Ξ) (a i) (b i) : ℝ) : ℂ)) * (A b - A' b) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hHX : 0 ≤ Cn₀ * H ^ (k + 1) * X ^ (k + 1) := by positivity
  have hδ0 : 0 ≤ τ + (2 * Q) ^ k * τ := by positivity
  calc ‖∑ b : Fin (k + 1) → Fin L, (∏ i, (((1 + Ξ) (a i) (b i) : ℝ) : ℂ)) * A b‖
      ≤ ‖∑ b : Fin (k + 1) → Fin L, (∏ i, (((1 + Ξ) (a i) (b i) : ℝ) : ℂ)) * A' b‖ +
        ‖∑ b : Fin (k + 1) → Fin L, (∏ i, (((1 + Ξ) (a i) (b i) : ℝ) : ℂ)) * (A b - A' b)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ Cn₀ * H ^ (k + 1) * X ^ (k + 1) * (S + (2 * Q) ^ k * τ) +
        (τ + (2 * Q) ^ k * τ) * (1 + ρ) ^ (k + 1) := by
        refine add_le_add ?_ (hDsum.trans (mul_le_mul_of_nonneg_left hprodW hδ0))
        exact hmainA.trans (mul_le_mul_of_nonneg_left hSA' hHX)
    _ ≤ 2 ^ (k + 1) * (Cn₀ + 1) * H ^ (k + 1) * X ^ (k + 1) * S +
        2 ^ (k + 1) * (Cn₀ + 1) * (H * (1 + ρ) * Q) ^ (2 * (k + 1)) * τ :=
        restore_zero_arith k Cn₀ H X ρ Q τ S hCn₀.le hH hX0 hXρ hρ.le hQ1 hτ0 hS0

end LSBA
