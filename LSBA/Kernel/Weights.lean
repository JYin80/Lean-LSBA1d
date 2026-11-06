import LSBA.Kernel.Algebra
import LSBA.Kernel.Scales

/-!
# Weights

The spatial weights of Lemma 6.2 [da:lem:scale-budgets]: comparison (6.7)
[da:eq:weight-comparison], convolution (6.8) [da:eq:weight-convolution] and the propagated weight
(A.53) [da:eq:propagated-weight] (Appendix A.8 [app:scale-budgets]).
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- The weight is positive when `W ≥ 1`. -/
private lemma weights_pos (c₁ θ F : ℝ) (W : ℕ) (hW : 1 ≤ W) (ℓ r : ℝ) :
    0 < weightFn c₁ θ F W ℓ r := by
  unfold weightFn
  exact add_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by exact_mod_cast hW) _)

/-- Weight comparison with two displacements: if `r ≤ r' + n₁ + n₂` then
`w(r') ≤ w(r) e^{c(n₁/ℓ)^θ} e^{c(n₂/ℓ)^θ}`. -/
private lemma weights_step3 (c θ F : ℝ) (hc : 0 < c) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (W : ℕ)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (r r' n₁ n₂ : ℝ) (hr : 0 ≤ r) (hr' : 0 ≤ r') (hn₁ : 0 ≤ n₁)
    (hn₂ : 0 ≤ n₂) (h : r ≤ r' + n₁ + n₂) :
    weightFn c θ F W ℓ r' ≤
      weightFn c θ F W ℓ r * Real.exp (c * (n₁ / ℓ) ^ θ) * Real.exp (c * (n₂ / ℓ) ^ θ) := by
  have h1 : (r / ℓ) ^ θ ≤ (r' / ℓ) ^ θ + (n₁ / ℓ) ^ θ + (n₂ / ℓ) ^ θ := by
    calc (r / ℓ) ^ θ ≤ (r' / ℓ + n₁ / ℓ + n₂ / ℓ) ^ θ := by
          apply Real.rpow_le_rpow (div_nonneg hr hℓ.le) _ hθ.le
          rw [← add_div, ← add_div]; exact div_le_div_of_nonneg_right h hℓ.le
      _ ≤ (r' / ℓ + n₁ / ℓ) ^ θ + (n₂ / ℓ) ^ θ :=
          Real.rpow_add_le_add_rpow (by positivity) (by positivity) hθ.le hθ1
      _ ≤ (r' / ℓ) ^ θ + (n₁ / ℓ) ^ θ + (n₂ / ℓ) ^ θ := by
          gcongr
          exact Real.rpow_add_le_add_rpow (by positivity) (by positivity) hθ.le hθ1
  have h2 : Real.exp (-(c * (r' / ℓ) ^ θ)) ≤
      Real.exp (-(c * (r / ℓ) ^ θ)) * Real.exp (c * (n₁ / ℓ) ^ θ) *
        Real.exp (c * (n₂ / ℓ) ^ θ) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]
  have h3 : (1 : ℝ) ≤ Real.exp (c * (n₁ / ℓ) ^ θ) := Real.one_le_exp (by positivity)
  have h3' : (1 : ℝ) ≤ Real.exp (c * (n₂ / ℓ) ^ θ) := Real.one_le_exp (by positivity)
  have h4 : (0 : ℝ) ≤ (W : ℝ) ^ (-F) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h5 : (W : ℝ) ^ (-F) ≤ (W : ℝ) ^ (-F) * Real.exp (c * (n₁ / ℓ) ^ θ) *
      Real.exp (c * (n₂ / ℓ) ^ θ) := by
    calc (W : ℝ) ^ (-F) = (W : ℝ) ^ (-F) * 1 * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h3 h4) h3' zero_le_one (by positivity)
  unfold weightFn
  rw [add_mul, add_mul]
  linarith

/-- One-sided comparison: if `r ≤ r' + 2n` then `w(r') ≤ e^{2c₁(n/ℓ)^θ} w(r)`. -/
private lemma weights_step (c₁ θ F : ℝ) (hc₁ : 0 < c₁) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (W : ℕ)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (r r' n : ℝ) (hr : 0 ≤ r) (hr' : 0 ≤ r') (hn : 0 ≤ n)
    (h : r ≤ r' + 2 * n) :
    weightFn c₁ θ F W ℓ r' ≤ Real.exp (2 * c₁ * (n / ℓ) ^ θ) * weightFn c₁ θ F W ℓ r := by
  have h1 := weights_step3 c₁ θ F hc₁ hθ hθ1 W ℓ hℓ r r' n n hr hr' hn hn (by linarith)
  have e : Real.exp (c₁ * (n / ℓ) ^ θ) * Real.exp (c₁ * (n / ℓ) ^ θ) =
      Real.exp (2 * c₁ * (n / ℓ) ^ θ) := by
    rw [← Real.exp_add]; congr 1; ring
  calc weightFn c₁ θ F W ℓ r' ≤ _ := h1
    _ = (Real.exp (c₁ * (n / ℓ) ^ θ) * Real.exp (c₁ * (n / ℓ) ^ θ)) *
          weightFn c₁ θ F W ℓ r := by ring
    _ = _ := by rw [e]

/-- Cyclic distance is symmetric. -/
private lemma weights_cycDist_comm {L : ℕ} (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

/-- Cyclic distance of a point to itself is `0`. -/
private lemma weights_cycDist_self {L : ℕ} (a : Fin L) : cycDist a a = 0 := by
  simp [cycDist]

private lemma weights_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The cyclic distance satisfies the triangle inequality. -/
private lemma weights_cycDist_tri {L : ℕ} (a b c : Fin L) :
    cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [cycDist, weights_mod ha hb, weights_mod hb ha, weights_mod ha hc, weights_mod hc ha,
    weights_mod hb hc, weights_mod hc hb]
  split_ifs <;> omega

/-- A sum over `Fin L` along an injection into `{0, …, L-1}` is bounded by the full sum. -/
private lemma weights_sum_inj {L : ℕ} (g : Fin L → ℕ) (hg : Function.Injective g)
    (hlt : ∀ b, g b < L) (h : ℕ → ℝ) (h0 : ∀ j, 0 ≤ h j) :
    ∑ b, h (g b) ≤ ∑ j ∈ Finset.range L, h j := by
  rw [← Finset.sum_image (f := h) (s := Finset.univ) (g := g) (fun x _ y _ hxy => hg hxy)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj
    obtain ⟨b, hb⟩ := hj
    rw [Finset.mem_range, ← hb]
    exact hlt b
  · intro i _ _
    exact h0 i

/-- For a nonnegative function of the distance, the sum over a cycle is at most twice the sum over
`{0, …, L-1}`. -/
private lemma weights_sum_dist {L : ℕ} (a : Fin L) (h : ℕ → ℝ) (h0 : ∀ j, 0 ≤ h j) :
    ∑ b, h (cycDist a b) ≤ 2 * ∑ j ∈ Finset.range L, h j := by
  have ha := a.isLt
  have h1 : ∑ b : Fin L, h ((a.val + L - b.val) % L) ≤ ∑ j ∈ Finset.range L, h j := by
    apply weights_sum_inj (fun b : Fin L => (a.val + L - b.val) % L) _ _ h h0
    · intro b b' hbb
      have hb := b.isLt
      have hb' := b'.isLt
      simp only [weights_mod ha hb, weights_mod ha hb'] at hbb
      apply Fin.ext
      split_ifs at hbb <;> omega
    · intro b
      exact Nat.mod_lt _ (by omega)
  have h2 : ∑ b : Fin L, h ((b.val + L - a.val) % L) ≤ ∑ j ∈ Finset.range L, h j := by
    apply weights_sum_inj (fun b : Fin L => (b.val + L - a.val) % L) _ _ h h0
    · intro b b' hbb
      have hb := b.isLt
      have hb' := b'.isLt
      simp only [weights_mod hb ha, weights_mod hb' ha] at hbb
      apply Fin.ext
      split_ifs at hbb <;> omega
    · intro b
      exact Nat.mod_lt _ (by omega)
  have h3 : ∀ b : Fin L, h (cycDist a b) ≤
      h ((a.val + L - b.val) % L) + h ((b.val + L - a.val) % L) := by
    intro b
    unfold cycDist
    rcases min_choice ((a.val + L - b.val) % L) ((b.val + L - a.val) % L) with e | e
    · rw [e]; linarith [h0 ((b.val + L - a.val) % L)]
    · rw [e]; linarith [h0 ((a.val + L - b.val) % L)]
  calc ∑ b, h (cycDist a b) ≤ ∑ b : Fin L, (h ((a.val + L - b.val) % L) +
        h ((b.val + L - a.val) % L)) := Finset.sum_le_sum fun b _ => h3 b
    _ ≤ 2 * ∑ j ∈ Finset.range L, h j := by
        rw [Finset.sum_add_distrib]; linarith

/-- A stretched exponential is dominated by an inverse square: `e^{-κ s^θ} ≤ C₀/(1+s)²`. -/
private lemma weights_exp_poly (κ θ : ℝ) (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ s : ℝ, 0 ≤ s → Real.exp (-(κ * s ^ θ)) ≤ C₀ / (1 + s) ^ 2 := by
  set m : ℕ := ⌈2 / θ⌉₊ with hm
  have hmθ : 2 ≤ θ * m := by
    have h := Nat.le_ceil (2 / θ)
    rw [← hm] at h
    calc (2 : ℝ) = θ * (2 / θ) := by field_simp
      _ ≤ θ * m := mul_le_mul_of_nonneg_left h hθ.le
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hκm : 0 < κ ^ m := pow_pos hκ m
  set M₁ : ℝ := (m.factorial : ℝ) / κ ^ m with hM₁
  have hM₁pos : 0 < M₁ := by positivity
  refine ⟨4 * max 1 M₁, by positivity, fun s hs => ?_⟩
  rcases le_or_gt 1 s with h1 | h1
  · have hspow : s ^ (2 : ℝ) ≤ s ^ (θ * m) :=
      Real.rpow_le_rpow_of_exponent_le h1 hmθ
    have hs2 : s ^ (2 : ℝ) = s ^ 2 := Real.rpow_two s
    have hsm : (s ^ θ) ^ m = s ^ (θ * m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    have hE : κ ^ m * s ^ 2 / m.factorial ≤ Real.exp (κ * s ^ θ) := by
      calc κ ^ m * s ^ 2 / m.factorial ≤ (κ * s ^ θ) ^ m / m.factorial := by
            apply div_le_div_of_nonneg_right _ hfac.le
            rw [mul_pow, hsm]
            exact mul_le_mul_of_nonneg_left (hs2 ▸ hspow) hκm.le
        _ ≤ Real.exp (κ * s ^ θ) :=
            Real.pow_div_factorial_le_exp _ (by positivity) m
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    have h4 : (1 + s) ^ 2 ≤ 4 * s ^ 2 := by nlinarith
    calc 1 * (1 + s) ^ 2 ≤ 4 * s ^ 2 := by linarith
      _ = 4 * M₁ * (κ ^ m * s ^ 2 / m.factorial) := by
          rw [hM₁]; field_simp
      _ ≤ 4 * max 1 M₁ * Real.exp (κ * s ^ θ) := by
          apply mul_le_mul _ hE (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  · have hle : Real.exp (-(κ * s ^ θ)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ κ * s ^ θ := by positivity
      linarith
    have hC : (4 : ℝ) ≤ 4 * max 1 M₁ := by
      have := le_max_left 1 M₁
      linarith
    have : (1 + s) ^ 2 ≤ 4 := by nlinarith
    rw [le_div_iff₀ (by positivity)]
    calc Real.exp (-(κ * s ^ θ)) * (1 + s) ^ 2 ≤ 1 * 4 :=
          mul_le_mul hle this (by positivity) (by norm_num)
      _ ≤ 4 * max 1 M₁ := by linarith

/-- Telescoping bound `Σ_{j<N} (ℓ+j)⁻² ≤ ℓ⁻² + ℓ⁻¹` for `ℓ > 0`. -/
private lemma weights_inv_sq_sum (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) :
    ∑ j ∈ Finset.range N, 1 / (ℓ + j) ^ 2 ≤ 1 / ℓ ^ 2 + 1 / ℓ := by
  have key : ∀ n : ℕ, ∑ j ∈ Finset.range (n + 1), 1 / (ℓ + j) ^ 2 ≤
      1 / ℓ ^ 2 + 1 / ℓ - 1 / (ℓ + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hp : 0 < ℓ + n := by positivity
      have h1 : 1 / (ℓ + ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / (ℓ + n) - 1 / (ℓ + ((n + 1 : ℕ) : ℝ)) := by
        push_cast
        rw [div_sub_div _ _ hp.ne' (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith
  cases N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
  | succ n =>
    have := key n
    have h2 : 0 ≤ 1 / (ℓ + (n : ℝ)) := by positivity
    linarith

/-- Sum of a stretched exponential of the cyclic distance over a cycle is `O(ℓ)` for `ℓ ≥ 1`. -/
private lemma weights_sum_bound_aux (κ θ : ℝ) (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (L : ℕ) (ℓ : ℝ), 1 ≤ ℓ → ∀ a : Fin L,
      ∑ b, Real.exp (-(κ * ((cycDist a b : ℝ) / ℓ) ^ θ)) ≤ A * ℓ := by
  obtain ⟨C₀, hC₀, hpoly⟩ := weights_exp_poly κ θ hκ hθ
  refine ⟨4 * C₀, by positivity, fun L ℓ hℓ a => ?_⟩
  have hℓ0 : 0 < ℓ := by linarith
  set h : ℕ → ℝ := fun j => Real.exp (-(κ * ((j : ℝ) / ℓ) ^ θ)) with hh
  have h0 : ∀ j, 0 ≤ h j := fun j => (Real.exp_pos _).le
  have h1 : ∑ b, h (cycDist a b) ≤ 2 * ∑ j ∈ Finset.range L, h j := weights_sum_dist a h h0
  have h2 : ∀ j : ℕ, h j ≤ C₀ * ℓ ^ 2 * (1 / (ℓ + j) ^ 2) := by
    intro j
    have := hpoly ((j : ℝ) / ℓ) (by positivity)
    have e : C₀ / (1 + (j : ℝ) / ℓ) ^ 2 = C₀ * ℓ ^ 2 * (1 / (ℓ + j) ^ 2) := by
      field_simp
    rw [e] at this
    exact this
  have h3 : ∑ j ∈ Finset.range L, h j ≤ C₀ * ℓ ^ 2 * (1 / ℓ ^ 2 + 1 / ℓ) := by
    calc ∑ j ∈ Finset.range L, h j ≤ ∑ j ∈ Finset.range L, C₀ * ℓ ^ 2 * (1 / (ℓ + j) ^ 2) :=
          Finset.sum_le_sum fun j _ => h2 j
      _ = C₀ * ℓ ^ 2 * ∑ j ∈ Finset.range L, 1 / (ℓ + j) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ C₀ * ℓ ^ 2 * (1 / ℓ ^ 2 + 1 / ℓ) :=
          mul_le_mul_of_nonneg_left (weights_inv_sq_sum ℓ hℓ0 L) (by positivity)
  have e : C₀ * ℓ ^ 2 * (1 / ℓ ^ 2 + 1 / ℓ) = C₀ * (1 + ℓ) := by field_simp
  calc ∑ b, Real.exp (-(κ * ((cycDist a b : ℝ) / ℓ) ^ θ)) = ∑ b, h (cycDist a b) := rfl
    _ ≤ 2 * (C₀ * (1 + ℓ)) := by rw [← e]; linarith
    _ ≤ 4 * C₀ * ℓ := by nlinarith

/-- The bound of the previous lemma with the same constant for the summation variable in either
slot of the distance. -/
private lemma weights_sum_bound (κ θ : ℝ) (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (L : ℕ) (ℓ : ℝ), 1 ≤ ℓ → ∀ a : Fin L,
      ∑ b, Real.exp (-(κ * ((cycDist a b : ℝ) / ℓ) ^ θ)) ≤ A * ℓ ∧
      ∑ b, Real.exp (-(κ * ((cycDist b a : ℝ) / ℓ) ^ θ)) ≤ A * ℓ := by
  obtain ⟨A, hA, h⟩ := weights_sum_bound_aux κ θ hκ hθ
  refine ⟨A, hA, fun L ℓ hℓ a => ⟨h L ℓ hℓ a, ?_⟩⟩
  calc ∑ b, Real.exp (-(κ * ((cycDist b a : ℝ) / ℓ) ^ θ))
      = ∑ b, Real.exp (-(κ * ((cycDist a b : ℝ) / ℓ) ^ θ)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [weights_cycDist_comm b a]
    _ ≤ A * ℓ := h L ℓ hℓ a

/-- `(M + m)^θ ≤ M^θ + θ m^θ` for `0 ≤ m ≤ M` and `0 < θ ≤ 1`. -/
private lemma weights_gain_aux (θ m M : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hm : 0 ≤ m)
    (hmM : m ≤ M) : (M + m) ^ θ ≤ M ^ θ + θ * m ^ θ := by
  rcases eq_or_lt_of_le (hm.trans hmM) with h0 | hM
  · have hm0 : m = 0 := le_antisymm (h0 ▸ hmM) hm
    subst hm0
    rw [← h0]
    simp [Real.zero_rpow hθ.ne']
  · obtain ⟨t, ht0, ht1, rfl⟩ : ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ m = M * t :=
      ⟨m / M, div_nonneg hm hM.le, (div_le_one hM).mpr hmM, by field_simp⟩
    have h1 : (1 + t) ^ θ ≤ 1 + θ * t :=
      rpow_one_add_le_one_add_mul_self (by linarith) hθ.le hθ1
    have h2 : t ≤ t ^ θ := by
      calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
        _ ≤ t ^ θ := Real.rpow_le_rpow_of_exponent_ge' ht0 ht1 hθ.le hθ1
    have e : M + M * t = M * (1 + t) := by ring
    rw [e, Real.mul_rpow hM.le (by linarith), Real.mul_rpow hM.le ht0]
    have hMθ : 0 ≤ M ^ θ := Real.rpow_nonneg hM.le _
    nlinarith [mul_le_mul_of_nonneg_left h1 hMθ, mul_le_mul_of_nonneg_left h2 hMθ]

/-- Gain from the sub-additivity of `t ↦ t^θ`:
`z^θ + (1-θ) min(x,y)^θ ≤ x^θ + y^θ` for `z ≤ x + y`. -/
private lemma weights_gain (θ x y z : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz0 : 0 ≤ z) (hz : z ≤ x + y) :
    z ^ θ + (1 - θ) * (min x y) ^ θ ≤ x ^ θ + y ^ θ := by
  have hz1 : z ^ θ ≤ (x + y) ^ θ := Real.rpow_le_rpow hz0 hz hθ.le
  rcases le_total x y with h | h
  · have := weights_gain_aux θ x y hθ hθ1 hx h
    rw [min_eq_left h]
    rw [add_comm x y] at hz1
    nlinarith
  · have := weights_gain_aux θ y x hθ hθ1 hy h
    rw [min_eq_right h]
    nlinarith

/-- Pointwise convolution bound for stretched exponentials. -/
private lemma weights_pt (κ θ x y z : ℝ) (hκ : 0 < κ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hz0 : 0 ≤ z) (hz : z ≤ x + y) :
    Real.exp (-(κ * x ^ θ)) * Real.exp (-(κ * y ^ θ)) ≤
      Real.exp (-(κ * z ^ θ)) *
        (Real.exp (-(κ * (1 - θ) * x ^ θ)) + Real.exp (-(κ * (1 - θ) * y ^ θ))) := by
  have hg := weights_gain θ x y z hθ hθ1 hx hy hz0 hz
  have h1 : Real.exp (-(κ * x ^ θ)) * Real.exp (-(κ * y ^ θ)) ≤
      Real.exp (-(κ * z ^ θ)) * Real.exp (-(κ * (1 - θ) * (min x y) ^ θ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hg hκ.le]
  have h2 : Real.exp (-(κ * (1 - θ) * (min x y) ^ θ)) ≤
      Real.exp (-(κ * (1 - θ) * x ^ θ)) + Real.exp (-(κ * (1 - θ) * y ^ θ)) := by
    rcases min_choice x y with e | e
    · rw [e]; linarith [Real.exp_pos (-(κ * (1 - θ) * y ^ θ))]
    · rw [e]; linarith [Real.exp_pos (-(κ * (1 - θ) * x ^ θ))]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)

/-- `√(a + b) ≤ √a + √b` for `a, b ≥ 0`. -/
private lemma weights_sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a)
    (Real.sqrt_nonneg b)]

/-- `√(e^{-κ r}) = e^{-(κ/2) r}`. -/
private lemma weights_sqrt_exp (κ r : ℝ) :
    Real.sqrt (Real.exp (-(κ * r))) = Real.exp (-(κ / 2 * r)) := by
  rw [← Real.exp_half]
  congr 1
  ring

/-- Pointwise bound for the product of two weights. -/
private lemma weights_conv_pt1 (c₁ θ f x y z : ℝ) (hc₁ : 0 < c₁) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz0 : 0 ≤ z) (hz : z ≤ x + y) :
    (Real.exp (-(c₁ * x ^ θ)) + f) * (Real.exp (-(c₁ * y ^ θ)) + f) ≤
      Real.exp (-(c₁ * z ^ θ)) *
          (Real.exp (-(c₁ * (1 - θ) * x ^ θ)) + Real.exp (-(c₁ * (1 - θ) * y ^ θ))) +
        f * Real.exp (-(c₁ * x ^ θ)) + f * Real.exp (-(c₁ * y ^ θ)) + f * f := by
  have := weights_pt c₁ θ x y z hc₁ hθ hθ1 hx hy hz0 hz
  nlinarith

/-- Pointwise bound for the geometric mean of two weights. -/
private lemma weights_conv_pt2 (c₁ θ s x y z : ℝ) (hc₁ : 0 < c₁) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz0 : 0 ≤ z) (hz : z ≤ x + y) (hs : 0 ≤ s) :
    Real.sqrt ((Real.exp (-(c₁ * x ^ θ)) + s * s) * (Real.exp (-(c₁ * y ^ θ)) + s * s)) ≤
      Real.exp (-(c₁ / 2 * z ^ θ)) *
          (Real.exp (-(c₁ / 2 * (1 - θ) * x ^ θ)) + Real.exp (-(c₁ / 2 * (1 - θ) * y ^ θ))) +
        s * Real.exp (-(c₁ / 2 * x ^ θ)) + s * Real.exp (-(c₁ / 2 * y ^ θ)) + s * s := by
  have hss : Real.sqrt (s * s) = s := Real.sqrt_mul_self hs
  have hsx : Real.sqrt (Real.exp (-(c₁ * x ^ θ)) + s * s) ≤
      Real.exp (-(c₁ / 2 * x ^ θ)) + s := by
    calc _ ≤ Real.sqrt (Real.exp (-(c₁ * x ^ θ))) + Real.sqrt (s * s) :=
          weights_sqrt_add_le _ _ (Real.exp_pos _).le (mul_self_nonneg s)
      _ = _ := by rw [weights_sqrt_exp, hss]
  have hsy : Real.sqrt (Real.exp (-(c₁ * y ^ θ)) + s * s) ≤
      Real.exp (-(c₁ / 2 * y ^ θ)) + s := by
    calc _ ≤ Real.sqrt (Real.exp (-(c₁ * y ^ θ))) + Real.sqrt (s * s) :=
          weights_sqrt_add_le _ _ (Real.exp_pos _).le (mul_self_nonneg s)
      _ = _ := by rw [weights_sqrt_exp, hss]
  have hp := weights_pt (c₁ / 2) θ x y z (by positivity) hθ hθ1 hx hy hz0 hz
  rw [Real.sqrt_mul (by positivity)]
  have hm := mul_le_mul hsx hsy (Real.sqrt_nonneg _) (by positivity)
  nlinarith

/-- (6.7) [da:eq:weight-comparison] with the explicit constant `2c₁`. -/
theorem weight_comparison (c₁ θ F : ℝ) (hc₁ : 0 < c₁) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (W : ℕ)
    (hW : 1 ≤ W) (ℓ : ℝ) (hℓ : 0 < ℓ) (r r' n : ℝ) (hr : 0 ≤ r) (hr' : 0 ≤ r') (hn : 0 ≤ n)
    (hrr : |r - r'| ≤ 2 * n) :
    Real.exp (-(2 * c₁ * (n / ℓ) ^ θ)) ≤ weightFn c₁ θ F W ℓ r' / weightFn c₁ θ F W ℓ r ∧
      weightFn c₁ θ F W ℓ r' / weightFn c₁ θ F W ℓ r ≤ Real.exp (2 * c₁ * (n / ℓ) ^ θ) := by
  have hpos := weights_pos c₁ θ F W hW ℓ r
  have hpos' := weights_pos c₁ θ F W hW ℓ r'
  obtain ⟨hab1, hab2⟩ := abs_le.mp hrr
  constructor
  · rw [le_div_iff₀ hpos]
    have h := weights_step c₁ θ F hc₁ hθ hθ1 W ℓ hℓ r' r n hr' hr hn (by linarith)
    have h2 : Real.exp (-(2 * c₁ * (n / ℓ) ^ θ)) * Real.exp (2 * c₁ * (n / ℓ) ^ θ) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp (-(2 * c₁ * (n / ℓ) ^ θ)) * weightFn c₁ θ F W ℓ r
        ≤ Real.exp (-(2 * c₁ * (n / ℓ) ^ θ)) *
          (Real.exp (2 * c₁ * (n / ℓ) ^ θ) * weightFn c₁ θ F W ℓ r') :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = weightFn c₁ θ F W ℓ r' := by rw [← mul_assoc, h2, one_mul]
  · rw [div_le_iff₀ hpos]
    exact weights_step c₁ θ F hc₁ hθ hθ1 W ℓ hℓ r r' n hr hr' hn (by linarith)

/-- (6.8) [da:eq:weight-convolution]. -/
theorem weight_convolution (c₁ θ F : ℝ) (hc₁ : 0 < c₁) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (hF : 0 < F) :
    ∃ C : ℝ, 0 < C ∧ ∀ W L : ℕ, 1 ≤ W → 1 ≤ L → ∀ ℓ : ℝ, 1 ≤ ℓ → ℓ ≤ L →
      (L : ℝ) * (W : ℝ) ^ (-(F / 2)) ≤ ℓ → ∀ a c : Fin L,
      ∑ b, weightFn c₁ θ F W ℓ (cycDist a b) * weightFn c₁ θ F W ℓ (cycDist b c) ≤
          C * ℓ * weightFn c₁ θ F W ℓ (cycDist a c) ∧
      ∑ b, Real.sqrt (weightFn c₁ θ F W ℓ (cycDist a b) * weightFn c₁ θ F W ℓ (cycDist b c)) ≤
          C * ℓ * Real.sqrt (weightFn c₁ θ F W ℓ (cycDist a c)) := by
  have hθ1 : θ ≤ 1 := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  obtain ⟨A₁, hA₁, hS₁⟩ := weights_sum_bound (c₁ * (1 - θ)) θ (mul_pos hc₁ h1θ) hθ
  obtain ⟨A₂, hA₂, hS₂⟩ := weights_sum_bound c₁ θ hc₁ hθ
  obtain ⟨A₃, hA₃, hS₃⟩ := weights_sum_bound (c₁ / 2 * (1 - θ)) θ (by positivity) hθ
  obtain ⟨A₄, hA₄, hS₄⟩ := weights_sum_bound (c₁ / 2) θ (by positivity) hθ
  refine ⟨max (2 * A₁ + 2 * A₂ + 1) (2 * A₃ + 2 * A₄ + 1),
    lt_max_of_lt_left (by positivity), ?_⟩
  intro W L hW hL ℓ hℓ1 _ hLW a c
  have hℓ0 : 0 < ℓ := by linarith
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWpos : (0 : ℝ) < W := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (W : ℝ) ^ (-(F / 2)) := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ Real.rpow_pos_of_pos hWpos _
  have hs1 : s ≤ 1 := hs ▸ Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hf : (W : ℝ) ^ (-F) = s * s := by
    rw [hs, ← Real.rpow_add hWpos]; congr 1; ring
  have hLs : (L : ℝ) * s ≤ ℓ := hs ▸ hLW
  have hw : ∀ r : ℝ, weightFn c₁ θ F W ℓ r = Real.exp (-(c₁ * (r / ℓ) ^ θ)) + s * s := by
    intro r; unfold weightFn; rw [hf]
  have hx : ∀ b : Fin L, 0 ≤ (cycDist a b : ℝ) / ℓ := fun b => by positivity
  have hy : ∀ b : Fin L, 0 ≤ (cycDist b c : ℝ) / ℓ := fun b => by positivity
  have hz0 : 0 ≤ (cycDist a c : ℝ) / ℓ := by positivity
  have htri : ∀ b : Fin L,
      (cycDist a c : ℝ) / ℓ ≤ (cycDist a b : ℝ) / ℓ + (cycDist b c : ℝ) / ℓ := by
    intro b
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast weights_cycDist_tri a b c) hℓ0.le
  have hLf : (L : ℝ) * (s * s * (s * s)) ≤ ℓ * (s * s) := by
    calc (L : ℝ) * (s * s * (s * s)) = ((L : ℝ) * s) * (s * s * s) := by ring
      _ ≤ ℓ * (s * s * s) := mul_le_mul_of_nonneg_right hLs (by positivity)
      _ ≤ ℓ * (s * s) := mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (by positivity) hs1)
          hℓ0.le
  have hLf' : (L : ℝ) * (s * s) ≤ ℓ * s := by
    calc (L : ℝ) * (s * s) = ((L : ℝ) * s) * s := by ring
      _ ≤ ℓ * s := mul_le_mul_of_nonneg_right hLs hs0.le
  have hφz : 0 ≤ Real.exp (-(c₁ * ((cycDist a c : ℝ) / ℓ) ^ θ)) := (Real.exp_pos _).le
  have hss : 0 ≤ s * s := by positivity
  constructor
  · -- (i)
    have hpt : ∀ b : Fin L,
        weightFn c₁ θ F W ℓ (cycDist a b) * weightFn c₁ θ F W ℓ (cycDist b c) ≤
        Real.exp (-(c₁ * ((cycDist a c : ℝ) / ℓ) ^ θ)) *
          (Real.exp (-(c₁ * (1 - θ) * ((cycDist a b : ℝ) / ℓ) ^ θ)) +
            Real.exp (-(c₁ * (1 - θ) * ((cycDist b c : ℝ) / ℓ) ^ θ))) +
        (s * s) * Real.exp (-(c₁ * ((cycDist a b : ℝ) / ℓ) ^ θ)) +
        (s * s) * Real.exp (-(c₁ * ((cycDist b c : ℝ) / ℓ) ^ θ)) + (s * s) * (s * s) := by
      intro b
      rw [hw, hw]
      exact weights_conv_pt1 c₁ θ (s * s) _ _ _ hc₁ hθ hθ1 (hx b) (hy b) hz0 (htri b)
    refine (Finset.sum_le_sum fun b _ => hpt b).trans ?_
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have e1 := (hS₁ L ℓ hℓ1 a).1
    have e2 := (hS₁ L ℓ hℓ1 c).2
    have e3 := (hS₂ L ℓ hℓ1 a).1
    have e4 := (hS₂ L ℓ hℓ1 c).2
    rw [hw]
    have P1 := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hφz
    have P2 := mul_le_mul_of_nonneg_left e3 hss
    have P3 := mul_le_mul_of_nonneg_left e4 hss
    have hC := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left (2 * A₁ + 2 * A₂ + 1) (2 * A₃ + 2 * A₄ + 1))
        hℓ0.le) (add_nonneg hφz hss)
    have q1 : 0 ≤ A₂ * ℓ * Real.exp (-(c₁ * ((cycDist a c : ℝ) / ℓ) ^ θ)) := by positivity
    have q2 : 0 ≤ A₁ * ℓ * (s * s) := by positivity
    have q3 : 0 ≤ ℓ * Real.exp (-(c₁ * ((cycDist a c : ℝ) / ℓ) ^ θ)) := by positivity
    nlinarith
  · -- (ii)
    have hpt : ∀ b : Fin L,
        Real.sqrt (weightFn c₁ θ F W ℓ (cycDist a b) * weightFn c₁ θ F W ℓ (cycDist b c)) ≤
        Real.exp (-(c₁ / 2 * ((cycDist a c : ℝ) / ℓ) ^ θ)) *
          (Real.exp (-(c₁ / 2 * (1 - θ) * ((cycDist a b : ℝ) / ℓ) ^ θ)) +
            Real.exp (-(c₁ / 2 * (1 - θ) * ((cycDist b c : ℝ) / ℓ) ^ θ))) +
        s * Real.exp (-(c₁ / 2 * ((cycDist a b : ℝ) / ℓ) ^ θ)) +
        s * Real.exp (-(c₁ / 2 * ((cycDist b c : ℝ) / ℓ) ^ θ)) + s * s := by
      intro b
      rw [hw, hw]
      exact weights_conv_pt2 c₁ θ s _ _ _ hc₁ hθ hθ1 (hx b) (hy b) hz0 (htri b) hs0.le
    refine (Finset.sum_le_sum fun b _ => hpt b).trans ?_
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have e1 := (hS₃ L ℓ hℓ1 a).1
    have e2 := (hS₃ L ℓ hℓ1 c).2
    have e3 := (hS₄ L ℓ hℓ1 a).1
    have e4 := (hS₄ L ℓ hℓ1 c).2
    have hZ1 : Real.exp (-(c₁ / 2 * ((cycDist a c : ℝ) / ℓ) ^ θ)) ≤
        Real.sqrt (weightFn c₁ θ F W ℓ (cycDist a c)) := by
      rw [← weights_sqrt_exp, hw]
      exact Real.sqrt_le_sqrt (by linarith)
    have hZ2 : s ≤ Real.sqrt (weightFn c₁ θ F W ℓ (cycDist a c)) := by
      rw [hw]
      calc s = Real.sqrt (s * s) := (Real.sqrt_mul_self hs0.le).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
    have hZ0 : 0 ≤ Real.sqrt (weightFn c₁ θ F W ℓ (cycDist a c)) := Real.sqrt_nonneg _
    have hφ' : 0 ≤ Real.exp (-(c₁ / 2 * ((cycDist a c : ℝ) / ℓ) ^ θ)) := (Real.exp_pos _).le
    have P1 := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hφ'
    have P2 := mul_le_mul_of_nonneg_left e3 hs0.le
    have P3 := mul_le_mul_of_nonneg_left e4 hs0.le
    have hC := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right (2 * A₁ + 2 * A₂ + 1) (2 * A₃ + 2 * A₄ + 1))
        hℓ0.le) hZ0
    have q1 := mul_le_mul_of_nonneg_left hZ1 (by positivity : 0 ≤ A₃ * ℓ)
    have q2 := mul_le_mul_of_nonneg_left hZ2 (by positivity : 0 ≤ A₄ * ℓ)
    have q3 := mul_le_mul_of_nonneg_left hZ2 hℓ0.le
    nlinarith

/-- `c_p t^θ ≤ (c/2) t + M` for `t ≥ 0`, `θ ≤ 1/2`. -/
private lemma weights_prop_exp_bound (c c_p θ : ℝ) (hc : 0 < c) (hcp : 0 < c_p) (hθ : 0 < θ)
    (hθ2 : θ ≤ 1 / 2) : ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → c_p * t ^ θ ≤ c / 2 * t + M := by
  refine ⟨c_p + c_p ^ 2 / (2 * c), fun t ht => ?_⟩
  have h1 : t ^ θ ≤ 1 + Real.sqrt t := by
    rcases le_total t 1 with h | h
    · have : t ^ θ ≤ 1 := Real.rpow_le_one ht h hθ.le
      linarith [Real.sqrt_nonneg t]
    · have : t ^ θ ≤ t ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le h hθ2
      rw [← Real.sqrt_eq_rpow] at this
      linarith
  have h2 : c_p * Real.sqrt t ≤ c / 2 * t + c_p ^ 2 / (2 * c) := by
    have hsq := Real.sq_sqrt ht
    have e : c / 2 * (Real.sqrt t - c_p / c) ^ 2 =
        c / 2 * t - c_p * Real.sqrt t + c_p ^ 2 / (2 * c) := by
      rw [sub_sq, hsq]; field_simp
    have : 0 ≤ c / 2 * (Real.sqrt t - c_p / c) ^ 2 := by positivity
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hcp.le]

/-- The weight is nondecreasing in the scale `ℓ`. -/
private lemma weights_mono_ell (c θ F : ℝ) (hc : 0 ≤ c) (hθ : 0 ≤ θ) (W : ℕ) (ℓ ℓ' r : ℝ)
    (hℓ : 0 < ℓ) (hℓℓ' : ℓ ≤ ℓ') (hr : 0 ≤ r) :
    weightFn c θ F W ℓ r ≤ weightFn c θ F W ℓ' r := by
  unfold weightFn
  have hℓ' : 0 < ℓ' := lt_of_lt_of_le hℓ hℓℓ'
  have h1 : r / ℓ' ≤ r / ℓ := div_le_div_of_nonneg_left hr hℓ hℓℓ'
  have h2 : (r / ℓ') ^ θ ≤ (r / ℓ) ^ θ := Real.rpow_le_rpow (by positivity) h1 hθ
  have : Real.exp (-(c * (r / ℓ) ^ θ)) ≤ Real.exp (-(c * (r / ℓ') ^ θ)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left h2 hc])
  linarith

/-- The weight is at most `2` for `W ≥ 1`, `F > 0`. -/
private lemma weights_le_two (c θ F : ℝ) (hc : 0 ≤ c) (hF : 0 < F) (W : ℕ) (hW : 1 ≤ W)
    (ℓ r : ℝ) (hℓ : 0 < ℓ) (hr : 0 ≤ r) : weightFn c θ F W ℓ r ≤ 2 := by
  unfold weightFn
  have h1 : Real.exp (-(c * (r / ℓ) ^ θ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ c * (r / ℓ) ^ θ := by positivity
    linarith
  have h2 : (W : ℝ) ^ (-F) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hW) (by linarith)
  linarith

/-- The floor `W^{-F}` is at most the weight. -/
private lemma weights_floor_le (c θ F : ℝ) (W : ℕ) (ℓ r : ℝ) :
    (W : ℝ) ^ (-F) ≤ weightFn c θ F W ℓ r := by
  unfold weightFn
  linarith [Real.exp_pos (-(c * (r / ℓ) ^ θ))]

/-- Product of two perturbed entries: if `p' = p + δ k`, `q' = q + δ k'` with `0 ≤ k, k' ≤ ρ`, then
`p' q' ≤ p q + δ ρ (p' + q')`. -/
private lemma weights_prop_pt (p q k k' δ ρ : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hk : 0 ≤ k)
    (hk' : 0 ≤ k') (hkρ : k ≤ ρ) (hk'ρ : k' ≤ ρ) (hδ : 0 ≤ δ) :
    (p + δ * k) * (q + δ * k') ≤ p * q + δ * ρ * ((p + δ * k) + (q + δ * k')) := by
  have hρ : 0 ≤ ρ := hk.trans hkρ
  nlinarith [mul_nonneg (mul_nonneg hδ hp) (sub_nonneg.2 hk'ρ),
    mul_nonneg (mul_nonneg hδ hq) (sub_nonneg.2 hkρ),
    mul_nonneg (mul_nonneg (mul_nonneg hδ hδ) hk) (sub_nonneg.2 hk'ρ),
    mul_nonneg (mul_nonneg (mul_nonneg hδ hδ) hρ) hk']

/-- (A.53) [da:eq:propagated-weight], from the profile bound (6.3) [fo:eq:kernel-bounds] with the
remainder at accuracy `B + F + 1`. -/
theorem propagated_weight (C₁ c c_p θ B F : ℝ) (hC₁ : 0 < C₁) (hc : 0 < c) (hcp : 0 < c_p)
    (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hB : 0 ≤ B) (hF : 0 < F) :
    ∃ C : ℝ, 0 < C ∧ ∀ W L : ℕ, 1 ≤ W → 1 ≤ L →
      ∀ (P : Matrix (Fin L) (Fin L) ℝ) (v u ℓv ℓu : ℝ),
      (∀ a b, 0 ≤ P a b) → (∀ a, ∑ b, P a b = 1) → 0 ≤ v → v ≤ u → u < 1 →
      1 ≤ ℓv → ℓv ≤ ℓu → (L : ℝ) / ℓv ≤ (W : ℝ) ^ B →
      (∀ a b, mixedKer P u a b ≤
        C₁ / ((1 - u) * ℓu) * Real.exp (-(c * cycDist a b / ℓu)) +
          ℓu⁻¹ * (W : ℝ) ^ (-(B + F + 1))) →
      ∀ a b, ∑ a', ∑ b', propPM P v u a a' * propPM P v u b b' *
          weightFn c_p θ F W ℓv (cycDist a' b') ≤
        C * ((1 - v) / (1 - u)) ^ 2 * weightFn c_p θ F W ℓu (cycDist a b) := by
  have _ := hB
  have hθ1 : θ ≤ 1 := by linarith
  obtain ⟨M, hM⟩ := weights_prop_exp_bound c c_p θ hc hcp hθ hθ2
  obtain ⟨A, hA, hS⟩ := weights_sum_bound (c / 2) 1 (by positivity) one_pos
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = C₁ * Real.exp M * A := ⟨_, rfl⟩
  have hQpos : 0 < Q := hQ ▸ by positivity
  refine ⟨(max 1 Q) ^ 2 + 4, by positivity, ?_⟩
  intro W L hW hL P v u ℓv ℓu hP hrow hv hvu hu hℓv hℓvu hLW hK a b
  have hu0 : 0 ≤ u := hv.trans hvu
  have h1u : 0 < 1 - u := by linarith
  have hℓv0 : 0 < ℓv := by linarith
  have hℓu1 : 1 ≤ ℓu := hℓv.trans hℓvu
  have hℓu0 : 0 < ℓu := by linarith
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWpos : (0 : ℝ) < W := by linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (1 - v) / (1 - u) := ⟨_, rfl⟩
  rw [← hR]
  have hR1 : 1 ≤ R := by rw [hR, le_div_iff₀ h1u]; linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = u - v := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by linarith
  have hδ1 : δ ≤ 1 := by linarith
  have hRδ : R - 1 = δ / (1 - u) := by rw [hR, hδ]; field_simp; ring
  obtain ⟨hKnn, hKrow⟩ := mixedKer_nonneg_row P hP hrow u hu0 hu
  obtain ⟨hUnn, hUrow⟩ := propPM_nonneg_row P hP hrow v u hv hvu hu
  have hUid : ∀ x y, propPM P v u x y = (if x = y then 1 else 0) + δ * mixedKer P u x y := by
    intro x y
    have := (propPM_identities P hP hrow v u u hv hvu le_rfl hu).1
    rw [this]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, hδ]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ℓu⁻¹ * (W : ℝ) ^ (-(B + F + 1)) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := hρ ▸ by positivity
  obtain ⟨Eb, hEb⟩ : ∃ Eb : Fin L → Fin L → ℝ, ∀ x y,
      Eb x y = C₁ / ((1 - u) * ℓu) * Real.exp (-(c * cycDist x y / ℓu)) :=
    ⟨_, fun _ _ => rfl⟩
  have hEb0 : ∀ x y, 0 ≤ Eb x y := fun x y => by rw [hEb]; positivity
  have hKE : ∀ x y, mixedKer P u x y ≤ Eb x y + ρ := fun x y => by rw [hEb, hρ]; exact hK x y
  obtain ⟨ke, hke⟩ : ∃ ke : Fin L → Fin L → ℝ, ∀ x y,
      ke x y = min (mixedKer P u x y) (Eb x y) := ⟨_, fun _ _ => rfl⟩
  have hke0 : ∀ x y, 0 ≤ ke x y := fun x y => by
    rw [hke]; exact le_min (hKnn x y) (hEb0 x y)
  have hkeE : ∀ x y, ke x y ≤ Eb x y := fun x y => by rw [hke]; exact min_le_right _ _
  have hkr0 : ∀ x y, 0 ≤ mixedKer P u x y - ke x y := fun x y => by
    rw [hke]; linarith [min_le_left (mixedKer P u x y) (Eb x y)]
  have hkrρ : ∀ x y, mixedKer P u x y - ke x y ≤ ρ := fun x y => by
    rw [hke]
    rcases min_choice (mixedKer P u x y) (Eb x y) with e | e
    · rw [e]; linarith
    · rw [e]; linarith [hKE x y]
  obtain ⟨Ue, hUe⟩ : ∃ Ue : Fin L → Fin L → ℝ, ∀ x y,
      Ue x y = (if x = y then 1 else 0) + δ * ke x y := ⟨_, fun _ _ => rfl⟩
  have hUe0 : ∀ x y, 0 ≤ Ue x y := fun x y => by
    rw [hUe]
    have : (0 : ℝ) ≤ if x = y then 1 else 0 := by split_ifs <;> norm_num
    have := mul_nonneg hδ0 (hke0 x y)
    linarith
  have hUU : ∀ x y, propPM P v u x y = Ue x y + δ * (mixedKer P u x y - ke x y) := by
    intro x y; rw [hUid, hUe]; ring
  have hpt : ∀ a' b', propPM P v u a a' * propPM P v u b b' ≤
      Ue a a' * Ue b b' + δ * ρ * (propPM P v u a a' + propPM P v u b b') := by
    intro a' b'
    rw [hUU a a', hUU b b']
    exact weights_prop_pt _ _ _ _ δ ρ (hUe0 a a') (hUe0 b b') (hkr0 a a') (hkr0 b b')
      (hkrρ a a') (hkrρ b b') hδ0
  -- weights
  have hcmp : ∀ a' b', weightFn c_p θ F W ℓv (cycDist a' b') ≤
      weightFn c_p θ F W ℓu (cycDist a b) *
        Real.exp (c_p * ((cycDist a a' : ℝ) / ℓu) ^ θ) *
        Real.exp (c_p * ((cycDist b b' : ℝ) / ℓu) ^ θ) := by
    intro a' b'
    refine (weights_mono_ell c_p θ F hcp.le hθ.le W ℓv ℓu (cycDist a' b' : ℝ) hℓv0 hℓvu
      (by positivity)).trans ?_
    apply weights_step3 c_p θ F hcp hθ hθ1 W ℓu hℓu0 (cycDist a b : ℝ) (cycDist a' b' : ℝ)
      (cycDist a a' : ℝ) (cycDist b b' : ℝ) (by positivity) (by positivity) (by positivity)
      (by positivity)
    have h1 := weights_cycDist_tri a a' b
    have h2 := weights_cycDist_tri a' b' b
    have h3 := weights_cycDist_comm b' b
    have : cycDist a b ≤ cycDist a' b' + cycDist a a' + cycDist b b' := by omega
    exact_mod_cast this
  have hwv2 : ∀ a' b' : Fin L, weightFn c_p θ F W ℓv (cycDist a' b') ≤ 2 := fun a' b' =>
    weights_le_two c_p θ F hcp.le hF W hW ℓv _ hℓv0 (by positivity)
  have hwv0 : ∀ a' b' : Fin L, 0 ≤ weightFn c_p θ F W ℓv (cycDist a' b') := fun a' b' =>
    (weights_pos c_p θ F W hW ℓv _).le
  have hwu0 : 0 ≤ weightFn c_p θ F W ℓu (cycDist a b) := (weights_pos c_p θ F W hW ℓu _).le
  -- weighted row bound for the exponential part of the propagator
  have hSrow : ∀ x : Fin L,
      ∑ y, Ue x y * Real.exp (c_p * ((cycDist x y : ℝ) / ℓu) ^ θ) ≤ max 1 Q * R := by
    intro x
    have hper : ∀ y : Fin L, ke x y * Real.exp (c_p * ((cycDist x y : ℝ) / ℓu) ^ θ) ≤
        C₁ / ((1 - u) * ℓu) * Real.exp M *
          Real.exp (-(c / 2 * ((cycDist x y : ℝ) / ℓu) ^ (1 : ℝ))) := by
      intro y
      have ht : 0 ≤ (cycDist x y : ℝ) / ℓu := by positivity
      have h1 := hM _ ht
      calc ke x y * Real.exp (c_p * ((cycDist x y : ℝ) / ℓu) ^ θ)
          ≤ Eb x y * Real.exp (c_p * ((cycDist x y : ℝ) / ℓu) ^ θ) :=
            mul_le_mul_of_nonneg_right (hkeE x y) (Real.exp_pos _).le
        _ = C₁ / ((1 - u) * ℓu) * Real.exp (-(c * ((cycDist x y : ℝ) / ℓu)) +
              c_p * ((cycDist x y : ℝ) / ℓu) ^ θ) := by
            rw [hEb, mul_assoc, ← Real.exp_add, mul_div_assoc]
        _ ≤ C₁ / ((1 - u) * ℓu) * (Real.exp M *
              Real.exp (-(c / 2 * ((cycDist x y : ℝ) / ℓu) ^ (1 : ℝ)))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [← Real.exp_add, Real.rpow_one]
            apply Real.exp_le_exp.mpr
            linarith
        _ = _ := by ring
    have hsum_main : ∑ y, Ue x y * Real.exp (c_p * ((cycDist x y : ℝ) / ℓu) ^ θ) =
        Real.exp (c_p * ((cycDist x x : ℝ) / ℓu) ^ θ) +
          δ * ∑ y, ke x y * Real.exp (c_p * ((cycDist x y : ℝ) / ℓu) ^ θ) := by
      calc ∑ y, Ue x y * Real.exp (c_p * ((cycDist x y : ℝ) / ℓu) ^ θ)
          = ∑ y, ((if x = y then Real.exp (c_p * ((cycDist x y : ℝ) / ℓu) ^ θ) else 0) +
              δ * (ke x y * Real.exp (c_p * ((cycDist x y : ℝ) / ℓu) ^ θ))) :=
            Finset.sum_congr rfl fun y _ => by rw [hUe]; split_ifs <;> ring
        _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ← Finset.mul_sum]
            simp
    have hg : Real.exp (c_p * ((cycDist x x : ℝ) / ℓu) ^ θ) = 1 := by
      simp [weights_cycDist_self, Real.zero_rpow hθ.ne']
    have hsumE : ∑ y, ke x y * Real.exp (c_p * ((cycDist x y : ℝ) / ℓu) ^ θ) ≤ Q / (1 - u) := by
      calc ∑ y, ke x y * Real.exp (c_p * ((cycDist x y : ℝ) / ℓu) ^ θ)
          ≤ ∑ y, C₁ / ((1 - u) * ℓu) * Real.exp M *
              Real.exp (-(c / 2 * ((cycDist x y : ℝ) / ℓu) ^ (1 : ℝ))) :=
            Finset.sum_le_sum fun y _ => hper y
        _ = C₁ / ((1 - u) * ℓu) * Real.exp M *
              ∑ y, Real.exp (-(c / 2 * ((cycDist x y : ℝ) / ℓu) ^ (1 : ℝ))) := by
            rw [Finset.mul_sum]
        _ ≤ C₁ / ((1 - u) * ℓu) * Real.exp M * (A * ℓu) :=
            mul_le_mul_of_nonneg_left (hS L ℓu hℓu1 x).1 (by positivity)
        _ = Q / (1 - u) := by rw [hQ]; field_simp
    rw [hsum_main, hg]
    have h2 : δ * ∑ y, ke x y * Real.exp (c_p * ((cycDist x y : ℝ) / ℓu) ^ θ) ≤
        (R - 1) * Q := by
      calc _ ≤ δ * (Q / (1 - u)) := mul_le_mul_of_nonneg_left hsumE hδ0
        _ = (R - 1) * Q := by rw [hRδ]; ring
    have hm1 : (1 : ℝ) ≤ max 1 Q := le_max_left _ _
    have hm2 : Q ≤ max 1 Q := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_left hm2 (sub_nonneg.2 hR1)]
  -- pointwise reduction
  have hLHS : ∑ a', ∑ b', propPM P v u a a' * propPM P v u b b' *
        weightFn c_p θ F W ℓv (cycDist a' b') ≤
      ∑ a' : Fin L, ∑ b' : Fin L,
        (weightFn c_p θ F W ℓu (cycDist a b) *
            ((Ue a a' * Real.exp (c_p * ((cycDist a a' : ℝ) / ℓu) ^ θ)) *
              (Ue b b' * Real.exp (c_p * ((cycDist b b' : ℝ) / ℓu) ^ θ))) +
          2 * δ * ρ * (propPM P v u a a' + propPM P v u b b')) := by
    apply Finset.sum_le_sum; intro a' _
    apply Finset.sum_le_sum; intro b' _
    have hnn : 0 ≤ δ * ρ * (propPM P v u a a' + propPM P v u b b') :=
      mul_nonneg (mul_nonneg hδ0 hρ0) (add_nonneg (hUnn a a') (hUnn b b'))
    calc propPM P v u a a' * propPM P v u b b' * weightFn c_p θ F W ℓv (cycDist a' b')
        ≤ (Ue a a' * Ue b b' + δ * ρ * (propPM P v u a a' + propPM P v u b b')) *
            weightFn c_p θ F W ℓv (cycDist a' b') :=
          mul_le_mul_of_nonneg_right (hpt a' b') (hwv0 a' b')
      _ = Ue a a' * Ue b b' * weightFn c_p θ F W ℓv (cycDist a' b') +
            δ * ρ * (propPM P v u a a' + propPM P v u b b') *
              weightFn c_p θ F W ℓv (cycDist a' b') := by ring
      _ ≤ Ue a a' * Ue b b' * (weightFn c_p θ F W ℓu (cycDist a b) *
              Real.exp (c_p * ((cycDist a a' : ℝ) / ℓu) ^ θ) *
              Real.exp (c_p * ((cycDist b b' : ℝ) / ℓu) ^ θ)) +
            δ * ρ * (propPM P v u a a' + propPM P v u b b') * 2 :=
          add_le_add (mul_le_mul_of_nonneg_left (hcmp a' b')
            (mul_nonneg (hUe0 a a') (hUe0 b b'))) (mul_le_mul_of_nonneg_left (hwv2 a' b') hnn)
      _ = _ := by ring
  have hsum1 : ∑ a' : Fin L, ∑ b' : Fin L,
        (weightFn c_p θ F W ℓu (cycDist a b) *
            ((Ue a a' * Real.exp (c_p * ((cycDist a a' : ℝ) / ℓu) ^ θ)) *
              (Ue b b' * Real.exp (c_p * ((cycDist b b' : ℝ) / ℓu) ^ θ)))) =
      weightFn c_p θ F W ℓu (cycDist a b) *
        ((∑ a', Ue a a' * Real.exp (c_p * ((cycDist a a' : ℝ) / ℓu) ^ θ)) *
          ∑ b', Ue b b' * Real.exp (c_p * ((cycDist b b' : ℝ) / ℓu) ^ θ)) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hsum2 : ∑ a' : Fin L, ∑ b' : Fin L,
        (2 * δ * ρ * (propPM P v u a a' + propPM P v u b b')) = 2 * δ * ρ * (2 * L * R) := by
    have hUrow' : ∀ x, ∑ y, propPM P v u x y = R := fun x => by rw [hUrow, hR]
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hUrow']
    ring
  -- remainder
  have hρL : ρ * L ≤ weightFn c_p θ F W ℓu (cycDist a b) := by
    have h1 : (L : ℝ) / ℓu ≤ (W : ℝ) ^ B :=
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hℓv0 hℓvu).trans hLW
    have h2 : (W : ℝ) ^ B * (W : ℝ) ^ (-(B + F + 1)) ≤ (W : ℝ) ^ (-F) := by
      rw [← Real.rpow_add hWpos]
      exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    calc ρ * L = (L : ℝ) / ℓu * (W : ℝ) ^ (-(B + F + 1)) := by rw [hρ]; ring
      _ ≤ (W : ℝ) ^ B * (W : ℝ) ^ (-(B + F + 1)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hWpos.le _)
      _ ≤ (W : ℝ) ^ (-F) := h2
      _ ≤ _ := weights_floor_le c_p θ F W ℓu _
  have hSa := hSrow a
  have hSb := hSrow b
  have hSa0 : 0 ≤ ∑ a', Ue a a' * Real.exp (c_p * ((cycDist a a' : ℝ) / ℓu) ^ θ) :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hUe0 a y) (Real.exp_pos _).le
  have hSb0 : 0 ≤ ∑ b', Ue b b' * Real.exp (c_p * ((cycDist b b' : ℝ) / ℓu) ^ θ) :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hUe0 b y) (Real.exp_pos _).le
  have hT1 := mul_le_mul_of_nonneg_left (mul_le_mul hSa hSb hSb0 (by positivity)) hwu0
  have hT2 : δ * (ρ * L) ≤ weightFn c_p θ F W ℓu (cycDist a b) := by
    calc δ * (ρ * L) ≤ 1 * (ρ * L) := mul_le_mul_of_nonneg_right hδ1 (by positivity)
      _ ≤ _ := by rw [one_mul]; exact hρL
  have hR0 : 0 ≤ R := by linarith
  have hT3 := mul_le_mul_of_nonneg_left hT2 (by positivity : 0 ≤ 4 * R)
  have hT4 := mul_le_mul_of_nonneg_right (by nlinarith : R ≤ R * R) hwu0
  simp only [Finset.sum_add_distrib] at hLHS
  rw [hsum1, hsum2] at hLHS
  nlinarith

end LSBA
