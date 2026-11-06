import LSBA.Prop.Objects
import LSBA.Loop.Generator
import LSBA.Volume.LocalComparison
import LSBA.Kernel.Weights

/-!
# Good-set rates for the mixed-pair bound

Deterministic bounds on the terms of the generator of the mixed-pair errors on the good sets:
the kernel row with the profile (6.3) [fo:eq:kernel-bounds] and exact row sums, the quadratic term,
the near and distant light terms and the bracket, each normalized by the envelope at the terminal
scale, as used by the no-exit lemma with multiplicative rates.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The excess constant `2Ce^{c/2}(1 + 2/c + 4/c²)` of the kernel row. -/
def kerExcess (C c : ℝ) : ℝ := 2 * C * Real.exp (c / 2) * (1 + 2 / c + 4 / c ^ 2)

/-! ### Cyclic distance -/

private lemma lemmaNRates_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The cyclic distance is symmetric. -/
private lemma lemmaNRates_cycDist_comm {L : ℕ} (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

/-- The cyclic distance satisfies the triangle inequality. -/
private lemma lemmaNRates_cycDist_tri {L : ℕ} (a b c : Fin L) :
    cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [cycDist, lemmaNRates_mod ha hb, lemmaNRates_mod hb ha, lemmaNRates_mod ha hc,
    lemmaNRates_mod hc ha, lemmaNRates_mod hb hc, lemmaNRates_mod hc hb]
  split_ifs <;> omega

/-- A sum over `Fin L` along an injection into `{0, …, L-1}` is bounded by the full sum. -/
private lemma lemmaNRates_sum_inj {L : ℕ} (g : Fin L → ℕ) (hg : Function.Injective g)
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

/-- For a nonnegative function of the distance, the sum over the cycle is at most twice the sum
over `{0, …, L-1}`. -/
private lemma lemmaNRates_sum_dist {L : ℕ} (a : Fin L) (h : ℕ → ℝ) (h0 : ∀ j, 0 ≤ h j) :
    ∑ b, h (cycDist a b) ≤ 2 * ∑ j ∈ Finset.range L, h j := by
  have ha := a.isLt
  have h1 : ∑ b : Fin L, h ((a.val + L - b.val) % L) ≤ ∑ j ∈ Finset.range L, h j := by
    apply lemmaNRates_sum_inj (fun b : Fin L => (a.val + L - b.val) % L) _ _ h h0
    · intro b b' hbb
      have hb := b.isLt
      have hb' := b'.isLt
      simp only [lemmaNRates_mod ha hb, lemmaNRates_mod ha hb'] at hbb
      apply Fin.ext
      split_ifs at hbb <;> omega
    · intro b
      exact Nat.mod_lt _ (by omega)
  have h2 : ∑ b : Fin L, h ((b.val + L - a.val) % L) ≤ ∑ j ∈ Finset.range L, h j := by
    apply lemmaNRates_sum_inj (fun b : Fin L => (b.val + L - a.val) % L) _ _ h h0
    · intro b b' hbb
      have hb := b.isLt
      have hb' := b'.isLt
      simp only [lemmaNRates_mod hb ha, lemmaNRates_mod hb' ha] at hbb
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

/-! ### Kernel row -/

/-- `Σ_{j<n} e^{-αj} ≤ 1 + 1/α` and `Σ_{j<n} j e^{-αj} ≤ 1/α²` for `α > 0`. -/
private lemma lemmaNRates_geom (α : ℝ) (hα : 0 < α) (n : ℕ) :
    ∑ j ∈ Finset.range n, Real.exp (-(α * j)) ≤ 1 + 1 / α ∧
      ∑ j ∈ Finset.range n, (j : ℝ) * Real.exp (-(α * j)) ≤ 1 / α ^ 2 := by
  set q := Real.exp (-α) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpow : ∀ j : ℕ, Real.exp (-(α * j)) = q ^ j := by
    intro j
    rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  simp only [hpow]
  have hqα : q * (1 + α) ≤ 1 := by
    have h := Real.add_one_le_exp α
    have e : q * Real.exp α = 1 := by rw [hq, ← Real.exp_add]; simp
    nlinarith
  constructor
  · have hs := (summable_geometric_of_lt_one hq0.le hq1).sum_le_tsum (Finset.range n)
      (fun j _ => by positivity)
    rw [tsum_geometric_of_lt_one hq0.le hq1] at hs
    refine hs.trans ?_
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    have e : (1 + 1 / α) * (1 - q) = 1 + (1 - q * (1 + α)) / α := by field_simp; ring
    rw [e]
    have : 0 ≤ (1 - q * (1 + α)) / α := div_nonneg (by linarith) hα.le
    linarith
  · have hnq : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
    have hs := (by simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnq :
      Summable fun j : ℕ => (j : ℝ) * q ^ j).sum_le_tsum (Finset.range n)
      (fun j _ => by positivity)
    rw [tsum_coe_mul_geometric_of_norm_lt_one hnq] at hs
    refine hs.trans ?_
    -- `α e^{-α/2} ≤ 1 - e^{-α}`
    set p := Real.exp (-(α / 2)) with hp
    have hp0 : 0 < p := Real.exp_pos _
    have hpq : q = p ^ 2 := by rw [hq, hp, ← Real.exp_nat_mul]; congr 1; ring
    have hsinh : α / 2 ≤ Real.sinh (α / 2) := Real.self_le_sinh_iff.mpr (by linarith)
    rw [Real.sinh_eq] at hsinh
    have hpinv : Real.exp (α / 2) * p = 1 := by rw [hp, ← Real.exp_add]; simp
    have h1 : α * p ≤ 1 - q := by
      rw [hpq]
      have : α ≤ Real.exp (α / 2) - p := by rw [hp]; linarith
      nlinarith
    have h2 : q * α ^ 2 ≤ (1 - q) ^ 2 := by
      have hap : 0 ≤ α * p := by positivity
      calc q * α ^ 2 = (α * p) ^ 2 := by rw [hpq]; ring
        _ ≤ (1 - q) ^ 2 := pow_le_pow_left₀ hap h1 2
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    linarith

/-- `e^y - 1 ≤ y e^y` for every real `y`. -/
private lemma lemmaNRates_exp_sub_one (y : ℝ) : Real.exp y - 1 ≤ y * Real.exp y := by
  have h := Real.add_one_le_exp (-y)
  have e : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos y]

/-- Comparison of the weight at `d(x,b)` with the weight at `d(a,b)`: the ratio is at most
`1 + min(e^{c_p(d(a,x)/ℓ)^θ} - 1, 2W^F)`. -/
private lemma lemmaNRates_weight_ratio {L : ℕ} (W : ℕ) (hW : 1 ≤ W) {cp θ F ℓ : ℝ} (hcp : 0 < cp)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hF : 0 ≤ F) (hℓ : 0 < ℓ) (a x b : Fin L) :
    weightFn cp θ F W ℓ (cycDist x b) ≤
      (1 + min (Real.exp (cp * ((cycDist a x : ℝ) / ℓ) ^ θ) - 1) (2 * (W : ℝ) ^ F)) *
        weightFn cp θ F W ℓ (cycDist a b) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set dab : ℝ := (cycDist a b : ℝ)
  set dax : ℝ := (cycDist a x : ℝ)
  set dxb : ℝ := (cycDist x b : ℝ)
  have hdab : 0 ≤ dab := Nat.cast_nonneg _
  have hdax : 0 ≤ dax := Nat.cast_nonneg _
  have hdxb : 0 ≤ dxb := Nat.cast_nonneg _
  have htri : dab ≤ dax + dxb := by
    have := lemmaNRates_cycDist_tri a x b
    simp only [dab, dax, dxb]; exact_mod_cast this
  set φ := Real.exp (cp * (dax / ℓ) ^ θ) with hφ
  have hφ1 : 1 ≤ φ := Real.one_le_exp (by positivity)
  have hfl0 : 0 ≤ (W : ℝ) ^ (-F) := Real.rpow_nonneg hW0.le _
  -- ratio bounded by `φ`
  have hA : weightFn cp θ F W ℓ dxb ≤ φ * weightFn cp θ F W ℓ dab := by
    have h1 : (dab / ℓ) ^ θ ≤ (dax / ℓ) ^ θ + (dxb / ℓ) ^ θ := by
      calc (dab / ℓ) ^ θ ≤ (dax / ℓ + dxb / ℓ) ^ θ := by
            apply Real.rpow_le_rpow (by positivity) _ hθ.le
            rw [← add_div]; exact div_le_div_of_nonneg_right htri hℓ.le
        _ ≤ _ := Real.rpow_add_le_add_rpow (by positivity) (by positivity) hθ.le hθ1
    have h2 : Real.exp (-(cp * (dxb / ℓ) ^ θ)) ≤ φ * Real.exp (-(cp * (dab / ℓ) ^ θ)) := by
      rw [hφ, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left h1 hcp.le]
    unfold weightFn
    nlinarith
  -- ratio bounded by `2 W^F`
  have hB : weightFn cp θ F W ℓ dxb ≤ 2 * (W : ℝ) ^ F * weightFn cp θ F W ℓ dab := by
    have h1 : Real.exp (-(cp * (dxb / ℓ) ^ θ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have : 0 ≤ cp * (dxb / ℓ) ^ θ := by positivity
                                  linarith)
    have h2 : (W : ℝ) ^ (-F) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
    have h3 : (W : ℝ) ^ F * (W : ℝ) ^ (-F) = 1 := by
      rw [← Real.rpow_add hW0]; simp
    have h4 : (W : ℝ) ^ (-F) ≤ weightFn cp θ F W ℓ dab := by
      unfold weightFn; linarith [Real.exp_pos (-(cp * (dab / ℓ) ^ θ))]
    have h5 : 0 ≤ (W : ℝ) ^ F := Real.rpow_nonneg hW0.le _
    have h6 : 1 ≤ (W : ℝ) ^ F * weightFn cp θ F W ℓ dab := by
      rw [← h3]; exact mul_le_mul_of_nonneg_left h4 h5
    unfold weightFn at *
    nlinarith
  have hw0 : 0 ≤ weightFn cp θ F W ℓ dab := by unfold weightFn; positivity
  rcases min_choice (φ - 1) (2 * (W : ℝ) ^ F) with e | e
  · rw [e]; linarith
  · rw [e]
    have : (1 + 2 * (W : ℝ) ^ F) * weightFn cp θ F W ℓ dab =
        2 * (W : ℝ) ^ F * weightFn cp θ F W ℓ dab + weightFn cp θ F W ℓ dab := by ring
    linarith

/-- The exponential part of the profile times the excess of the weight ratio, summed over the
cycle, is at most `(1-u)⁻¹ c_p K(C,c)`. -/
private lemma lemmaNRates_excess_sum {L : ℕ} {u ℓu ℓv C c cp θ : ℝ} (hu : u < 1) (hC : 0 ≤ C)
    (hc : 0 < c) (hcp : 0 < cp) (hcp2 : cp ≤ c / 2) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hℓ : 1 ≤ ℓu)
    (hℓuv : ℓu ≤ ℓv) (a : Fin L) :
    ∑ x, C / ((1 - u) * ℓu) * Real.exp (-(c * cycDist a x / ℓu)) *
        (Real.exp (cp * ((cycDist a x : ℝ) / ℓv) ^ θ) - 1) ≤
      (1 - u)⁻¹ * (cp * kerExcess C c) := by
  have h1u : 0 < 1 - u := by linarith
  have hℓ0 : 0 < ℓu := by linarith
  have hℓv0 : 0 < ℓv := by linarith
  set α := c / (2 * ℓu) with hα
  have hα0 : 0 < α := by positivity
  set K0 := C * cp * Real.exp (c / 2) / ((1 - u) * ℓu) with hK0
  have hK00 : 0 ≤ K0 := by positivity
  set h : ℕ → ℝ := fun j => (1 + (j : ℝ) / ℓu) * Real.exp (-(α * j)) with hh
  have hpt : ∀ x : Fin L, C / ((1 - u) * ℓu) * Real.exp (-(c * cycDist a x / ℓu)) *
      (Real.exp (cp * ((cycDist a x : ℝ) / ℓv) ^ θ) - 1) ≤ K0 * h (cycDist a x) := by
    intro x
    set d : ℝ := (cycDist a x : ℝ)
    have hd : 0 ≤ d := Nat.cast_nonneg _
    set t := d / ℓu with ht
    have ht0 : 0 ≤ t := by positivity
    set s := (d / ℓv) ^ θ with hs
    have hs0 : 0 ≤ s := by positivity
    have hst : s ≤ 1 + t := by
      have h1 : s ≤ t ^ θ :=
        Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_left hd hℓ0 hℓuv) hθ.le
      have h2 : t ^ θ ≤ 1 + t := by
        rcases le_total t 1 with h | h
        · have := Real.rpow_le_one ht0 h hθ.le; linarith
        · have := Real.rpow_le_rpow_of_exponent_le h hθ1
          rw [Real.rpow_one] at this; linarith
      linarith
    have hy : cp * s ≤ c / 2 * (1 + t) :=
      mul_le_mul hcp2 hst hs0 (by positivity)
    have hy' : cp * s ≤ cp * (1 + t) := mul_le_mul_of_nonneg_left hst hcp.le
    have hφ : Real.exp (cp * s) - 1 ≤ cp * (1 + t) * Real.exp (c / 2 * (1 + t)) :=
      (lemmaNRates_exp_sub_one (cp * s)).trans
        (mul_le_mul hy' (Real.exp_le_exp.mpr hy) (Real.exp_pos _).le (by positivity))
    have hφ0 : 0 ≤ Real.exp (cp * s) - 1 := by
      have := Real.one_le_exp (by positivity : 0 ≤ cp * s); linarith
    have he : Real.exp (-(c * d / ℓu)) * Real.exp (c / 2 * (1 + t)) =
        Real.exp (c / 2) * Real.exp (-(α * d)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [ht, hα]; field_simp; ring
    have hE0 : 0 ≤ C / ((1 - u) * ℓu) * Real.exp (-(c * d / ℓu)) := by positivity
    calc C / ((1 - u) * ℓu) * Real.exp (-(c * d / ℓu)) * (Real.exp (cp * s) - 1)
        ≤ C / ((1 - u) * ℓu) * Real.exp (-(c * d / ℓu)) *
            (cp * (1 + t) * Real.exp (c / 2 * (1 + t))) :=
          mul_le_mul_of_nonneg_left hφ hE0
      _ = C * cp / ((1 - u) * ℓu) * (1 + t) *
            (Real.exp (-(c * d / ℓu)) * Real.exp (c / 2 * (1 + t))) := by ring
      _ = K0 * h (cycDist a x) := by rw [he, hK0, hh]; simp only [t, d]; ring
  have hh0 : ∀ j, 0 ≤ h j := fun j => by simp only [hh]; positivity
  obtain ⟨hg1, hg2⟩ := lemmaNRates_geom α hα0 L
  have hsum : ∑ j ∈ Finset.range L, h j ≤ (1 + 1 / α) + 1 / ℓu * (1 / α ^ 2) := by
    have e : ∑ j ∈ Finset.range L, h j = ∑ j ∈ Finset.range L, Real.exp (-(α * j)) +
        1 / ℓu * ∑ j ∈ Finset.range L, (j : ℝ) * Real.exp (-(α * j)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hh]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hg2 (by positivity : (0 : ℝ) ≤ 1 / ℓu)
    linarith
  calc ∑ x, C / ((1 - u) * ℓu) * Real.exp (-(c * cycDist a x / ℓu)) *
        (Real.exp (cp * ((cycDist a x : ℝ) / ℓv) ^ θ) - 1)
      ≤ ∑ x, K0 * h (cycDist a x) := Finset.sum_le_sum fun x _ => hpt x
    _ = K0 * ∑ x, h (cycDist a x) := by rw [Finset.mul_sum]
    _ ≤ K0 * (2 * ((1 + 1 / α) + 1 / ℓu * (1 / α ^ 2))) :=
        mul_le_mul_of_nonneg_left ((lemmaNRates_sum_dist a h hh0).trans (by linarith)) hK00
    _ = (1 - u)⁻¹ * (cp * (2 * C * Real.exp (c / 2) * (1 / ℓu + 2 / c + 4 / c ^ 2))) := by
        rw [hK0, hα]; field_simp; ring
    _ ≤ (1 - u)⁻¹ * (cp * kerExcess C c) := by
        unfold kerExcess
        have h1 : 1 / ℓu ≤ 1 := by rw [div_le_one hℓ0]; exact hℓ
        have : 0 ≤ (1 - u)⁻¹ * (cp * (2 * C * Real.exp (c / 2))) := by positivity
        have := mul_le_mul_of_nonneg_left (by linarith : 1 / ℓu + 2 / c + 4 / c ^ 2 ≤
          1 + 2 / c + 4 / c ^ 2) this
        linarith

/-- Kernel row: a nonnegative kernel with row sums `(1-u)⁻¹` and the profile (6.3)
[fo:eq:kernel-bounds] at scale `ℓ_u` maps the weight `w_v` at the larger scale `ℓ_v ≥ ℓ_u` to
itself up to `(1-u)⁻¹(1 + c_p K(C,c)) + 2(L/ℓ_u)W^{F-A}`, for `c_p ≤ c/2`. -/
theorem lemmaNRates_kernel {L : ℕ} (W : ℕ) (hW : 1 ≤ W) (K : Matrix (Fin L) (Fin L) ℝ)
    {u ℓu ℓv C c cp θ F A : ℝ} (hu : u < 1) (hC : 0 ≤ C) (hc : 0 < c) (hcp : 0 < cp)
    (hcp2 : cp ≤ c / 2) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hF : 0 ≤ F) (hℓ : 1 ≤ ℓu) (hℓuv : ℓu ≤ ℓv)
    (hK0 : ∀ a b, 0 ≤ K a b) (hrow : ∀ a, ∑ b, K a b = (1 - u)⁻¹)
    (hprof : ∀ a b, K a b ≤ C / ((1 - u) * ℓu) * Real.exp (-(c * cycDist a b / ℓu)) +
      ℓu⁻¹ * (W : ℝ) ^ (-A))
    (a b : Fin L) :
    ∑ x, K a x * weightFn cp θ F W ℓv (cycDist x b) ≤
      ((1 - u)⁻¹ * (1 + cp * kerExcess C c) + 2 * L / ℓu * (W : ℝ) ^ (F - A)) *
        weightFn cp θ F W ℓv (cycDist a b) := by
  have hℓ0 : 0 < ℓu := by linarith
  have hℓv0 : 0 < ℓv := by linarith
  have hW0 : (0 : ℝ) < W := by have : (1 : ℝ) ≤ W := by exact_mod_cast hW
                               linarith
  set wab := weightFn cp θ F W ℓv (cycDist a b) with hwab
  have hw0 : 0 ≤ wab := by rw [hwab]; unfold weightFn; positivity
  set ρ := ℓu⁻¹ * (W : ℝ) ^ (-A) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set E : Fin L → ℝ := fun x => C / ((1 - u) * ℓu) * Real.exp (-(c * cycDist a x / ℓu)) with hE
  set m : Fin L → ℝ := fun x =>
    min (Real.exp (cp * ((cycDist a x : ℝ) / ℓv) ^ θ) - 1) (2 * (W : ℝ) ^ F) with hm
  have hm0 : ∀ x, 0 ≤ m x := fun x => by
    simp only [hm]
    refine le_min ?_ (by positivity)
    have := Real.one_le_exp (by positivity : 0 ≤ cp * ((cycDist a x : ℝ) / ℓv) ^ θ); linarith
  have hpt : ∀ x, K a x * weightFn cp θ F W ℓv (cycDist x b) ≤
      K a x * wab + (E x * (Real.exp (cp * ((cycDist a x : ℝ) / ℓv) ^ θ) - 1) +
        ρ * (2 * (W : ℝ) ^ F)) * wab := by
    intro x
    have h1 := lemmaNRates_weight_ratio W hW hcp hθ hθ1 hF hℓv0 a x b
    have h2 : K a x * m x ≤ E x * (Real.exp (cp * ((cycDist a x : ℝ) / ℓv) ^ θ) - 1) +
        ρ * (2 * (W : ℝ) ^ F) := by
      calc K a x * m x ≤ (E x + ρ) * m x := mul_le_mul_of_nonneg_right (hprof a x) (hm0 x)
        _ = E x * m x + ρ * m x := by ring
        _ ≤ _ := by
          have hE0 : 0 ≤ E x := by simp only [hE]; positivity
          exact add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) hE0)
            (mul_le_mul_of_nonneg_left (min_le_right _ _) hρ0)
    calc K a x * weightFn cp θ F W ℓv (cycDist x b) ≤ K a x * ((1 + m x) * wab) :=
          mul_le_mul_of_nonneg_left h1 (hK0 a x)
      _ = K a x * wab + (K a x * m x) * wab := by ring
      _ ≤ _ := by gcongr
  have hex := lemmaNRates_excess_sum (L := L) hu hC hc hcp hcp2 hθ hθ1 hℓ hℓuv a
  have hrem : ∑ _x : Fin L, ρ * (2 * (W : ℝ) ^ F) = 2 * L / ℓu * (W : ℝ) ^ (F - A) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hρ,
      Real.rpow_sub hW0, Real.rpow_neg hW0.le]
    field_simp
  calc ∑ x, K a x * weightFn cp θ F W ℓv (cycDist x b)
      ≤ ∑ x, (K a x * wab + (E x * (Real.exp (cp * ((cycDist a x : ℝ) / ℓv) ^ θ) - 1) +
        ρ * (2 * (W : ℝ) ^ F)) * wab) := Finset.sum_le_sum fun x _ => hpt x
    _ = ((∑ x, K a x) + (∑ x, E x * (Real.exp (cp * ((cycDist a x : ℝ) / ℓv) ^ θ) - 1)) +
        ∑ _x : Fin L, ρ * (2 * (W : ℝ) ^ F)) * wab := by
      simp only [Finset.sum_add_distrib, add_mul, Finset.sum_mul]
      ring
    _ ≤ ((1 - u)⁻¹ + (1 - u)⁻¹ * (cp * kerExcess C c) +
        2 * L / ℓu * (W : ℝ) ^ (F - A)) * wab := by
      rw [hrow a, hrem]
      gcongr
    _ = _ := by ring

/-- Quadratic row: `|D(x,y)| ≤ Λ w(x,y)` and the convolution bound `Σ_c w(x,c)w(c,y) ≤ C ℓ w(x,y)`
give `|Σ_c D(a,c) D(c,b)| ≤ Λ² C ℓ w(a,b)`. -/
theorem lemmaNRates_quad {L : ℕ} (D : Fin L → Fin L → ℂ) (w : Fin L → Fin L → ℝ)
    {Λ Cw ℓ : ℝ} (hΛ : 0 ≤ Λ) (hw0 : ∀ x y, 0 ≤ w x y) (hD : ∀ x y, ‖D x y‖ ≤ Λ * w x y)
    (hconv : ∀ x y, ∑ c, w x c * w c y ≤ Cw * ℓ * w x y) (a b : Fin L) :
    ‖∑ c, D a c * D c b‖ ≤ Λ ^ 2 * Cw * ℓ * w a b := by
  calc ‖∑ c, D a c * D c b‖ ≤ ∑ c, ‖D a c‖ * ‖D c b‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => norm_mul _ _))
    _ ≤ ∑ c, (Λ * w a c) * (Λ * w c b) := Finset.sum_le_sum fun c _ =>
        mul_le_mul (hD a c) (hD c b) (norm_nonneg _) (mul_nonneg hΛ (hw0 a c))
    _ = Λ ^ 2 * ∑ c, w a c * w c b := by rw [Finset.mul_sum]; congr 1; ext c; ring
    _ ≤ Λ ^ 2 * (Cw * ℓ * w a b) := mul_le_mul_of_nonneg_left (hconv a b) (by positivity)
    _ = Λ ^ 2 * Cw * ℓ * w a b := by ring

/-! ### Hilbert–Schmidt and operator norms of blocks -/

section LinAlg

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Squared Hilbert–Schmidt norm `Σ_{ij} |A_{ij}|²`. -/
private def lemmaNRates_hs (A : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

/-- `‖A u‖² ≤ ‖A‖² ‖u‖²` for the operator norm. -/
private lemma lemmaNRates_nsq_le (A : Matrix n n ℂ) (u : n → ℂ) :
    ∑ i, ‖(A *ᵥ u) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ i, ‖u i‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 u)
  have h1 : ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ u)‖ ^ 2 = ∑ i, ‖(A *ᵥ u) i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ n)‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  rw [← h1, ← h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- `‖Y X‖²_HS ≤ ‖Y‖² ‖X‖²_HS`. -/
private lemma lemmaNRates_hs_mul_left (Y X : Matrix n n ℂ) :
    lemmaNRates_hs (Y * X) ≤ ‖Y‖ ^ 2 * lemmaNRates_hs X := by
  unfold lemmaNRates_hs
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖X i j‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := lemmaNRates_nsq_le Y (fun i => X i j)
  have e : (Y *ᵥ fun i => X i j) = fun i => (Y * X) i j := by
    funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [e] at h
  exact h

omit [DecidableEq n] in
private lemma lemmaNRates_hs_conjTranspose (X : Matrix n n ℂ) :
    lemmaNRates_hs Xᴴ = lemmaNRates_hs X := by
  unfold lemmaNRates_hs
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

omit [DecidableEq n] in
/-- `|Tr(A B)| ≤ ‖A‖_HS ‖B‖_HS`. -/
private lemma lemmaNRates_trace_mul_le (A B : Matrix n n ℂ) :
    ‖(A * B).trace‖ ≤ Real.sqrt (lemmaNRates_hs A) * Real.sqrt (lemmaNRates_hs B) := by
  have h1 : (A * B).trace = ∑ x : n × n, A x.1 x.2 * B x.2 x.1 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact (Fintype.sum_prod_type' _).symm
  have hA : lemmaNRates_hs A = ∑ x : n × n, ‖A x.1 x.2‖ ^ 2 := (Fintype.sum_prod_type' _).symm
  have hB : lemmaNRates_hs B = ∑ x : n × n, ‖B x.2 x.1‖ ^ 2 := by
    unfold lemmaNRates_hs
    rw [Finset.sum_comm]
    exact (Fintype.sum_prod_type' (fun i j => ‖B j i‖ ^ 2)).symm
  rw [h1, hA, hB]
  calc ‖∑ x : n × n, A x.1 x.2 * B x.2 x.1‖ ≤ ∑ x : n × n, ‖A x.1 x.2‖ * ‖B x.2 x.1‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => norm_mul _ _))
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- `|Tr(A B C)| ≤ ‖A‖ ‖B‖_HS ‖C‖_HS`. -/
private lemma lemmaNRates_trace3_le (A B C : Matrix n n ℂ) :
    ‖(A * B * C).trace‖ ≤
      ‖A‖ * (Real.sqrt (lemmaNRates_hs B) * Real.sqrt (lemmaNRates_hs C)) := by
  refine (lemmaNRates_trace_mul_le _ _).trans ?_
  have h : Real.sqrt (lemmaNRates_hs (A * B)) ≤ ‖A‖ * Real.sqrt (lemmaNRates_hs B) := by
    rw [← Real.sqrt_sq (norm_nonneg A), ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (lemmaNRates_hs_mul_left A B)
  calc Real.sqrt (lemmaNRates_hs (A * B)) * Real.sqrt (lemmaNRates_hs C)
      ≤ ‖A‖ * Real.sqrt (lemmaNRates_hs B) * Real.sqrt (lemmaNRates_hs C) :=
        mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)
    _ = _ := by ring

omit [DecidableEq n] in
/-- `‖A + B‖²_HS ≤ 2‖A‖²_HS + 2‖B‖²_HS`. -/
private lemma lemmaNRates_hs_add_le (A B : Matrix n n ℂ) :
    lemmaNRates_hs (A + B) ≤ 2 * lemmaNRates_hs A + 2 * lemmaNRates_hs B := by
  unfold lemmaNRates_hs
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.add_apply]
  have h := norm_add_le (A i j) (B i j)
  have h0 := norm_nonneg (A i j + B i j)
  nlinarith [sq_nonneg (‖A i j‖ - ‖B i j‖), norm_nonneg (A i j), norm_nonneg (B i j)]

omit [DecidableEq n] in
private lemma lemmaNRates_hs_smul (k : ℂ) (A : Matrix n n ℂ) :
    lemmaNRates_hs (k • A) = ‖k‖ ^ 2 * lemmaNRates_hs A := by
  unfold lemmaNRates_hs
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

omit [DecidableEq n] in
/-- `Tr(Z Z*) = ‖Z‖²_HS`. -/
private lemma lemmaNRates_trace_mul_conjTranspose (Z : Matrix n n ℂ) :
    (Z * Zᴴ).trace = ((lemmaNRates_hs Z : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    lemmaNRates_hs]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj']

end LinAlg

section BlockAlg

variable {W L : ℕ}

/-- `(X E_a Y)_{cd} = W⁻¹ X_{ca} Y_{ad}`. -/
private lemma lemmaNRates_blockOf_mul_blockE_mul (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a c d : Fin L) :
    blockOf (X * blockE W L a * Y) c d = (W : ℂ)⁻¹ • (blockOf X c a * blockOf Y a d) := by
  ext α β
  simp only [blockOf, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  simp only [blockE, Matrix.mul_diagonal, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun γ _ => ?_
    simp only [ite_true, Matrix.of_apply]; ring
  · intro e _ he; simp [he]
  · simp

/-- `Tr(Y E_z) = W⁻¹ Tr Y_{zz}`. -/
private lemma lemmaNRates_trace_mul_blockE (Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (z : Fin L) : (Y * blockE W L z).trace = (W : ℂ)⁻¹ * (blockOf Y z z).trace := by
  simp only [Matrix.trace, Matrix.diag, blockE, Matrix.mul_diagonal, blockOf, Matrix.of_apply,
    Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_eq_single z]
  · refine Finset.sum_congr rfl fun γ _ => ?_
    simp only [ite_true]; ring
  · intro e _ he; simp [he]
  · simp

/-- A loop of length three as the trace of the product of three blocks. -/
private lemma lemmaNRates_loopTr_three (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x y z : Fin L) (s₀ s₁ s₂ : Bool) :
    loopTr X ![x, y, z] ![s₀, s₁, s₂] = (W : ℂ)⁻¹ ^ 3 *
      (blockOf (sgnMat X s₀) z x * blockOf (sgnMat X s₁) x y *
        blockOf (sgnMat X s₂) y z).trace := by
  have e : (List.ofFn fun i : Fin 3 =>
      sgnMat X (![s₀, s₁, s₂] i) * blockE W L (![x, y, z] i)).prod =
      sgnMat X s₀ * blockE W L x * (sgnMat X s₁ * blockE W L y * sgnMat X s₂) * blockE W L z := by
    simp [List.ofFn_succ, Matrix.mul_assoc]
  unfold loopTr
  rw [e, lemmaNRates_trace_mul_blockE, lemmaNRates_blockOf_mul_blockE_mul,
    lemmaNRates_blockOf_mul_blockE_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_assoc]
  ring

private lemma lemmaNRates_blockOf_conjTranspose (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (e f : Fin L) : blockOf Xᴴ e f = (blockOf X f e)ᴴ := by
  ext α β; simp [blockOf, Matrix.conjTranspose_apply]

private lemma lemmaNRates_hs_blockOf (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (e f : Fin L) : lemmaNRates_hs (blockOf X e f) = blockHS2 X e f := by
  simp [lemmaNRates_hs, blockHS2, blockOf]

end BlockAlg

/-! ### Light row -/

section LightRow

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ}

/-- Both cuts of the light term of `ℒ₂(a,b;+,-)` at the inserted label `c` are bounded by the
operator norm of one of the edges `bc`, `ca` times the Hilbert–Schmidt norms of the other two. -/
private lemma lemmaNRates_cut_bound (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b c : Fin L) :
    let Q₁ := ‖blockOf G b c‖ * (Real.sqrt (blockHS2 G c a) * Real.sqrt (blockHS2 G b a))
    let Q₂ := ‖blockOf G c a‖ * (Real.sqrt (blockHS2 G b c) * Real.sqrt (blockHS2 G b a))
    (‖loopTr G ![c, a, b] ![true, true, false]‖ ≤ ((W : ℝ)⁻¹) ^ 3 * Q₁ ∧
      ‖loopTr G ![c, a, b] ![true, true, false]‖ ≤ ((W : ℝ)⁻¹) ^ 3 * Q₂) ∧
    (‖loopTr G ![a, c, b] ![true, false, false]‖ ≤ ((W : ℝ)⁻¹) ^ 3 * Q₁ ∧
      ‖loopTr G ![a, c, b] ![true, false, false]‖ ≤ ((W : ℝ)⁻¹) ^ 3 * Q₂) := by
  intro Q₁ Q₂
  have hn : ∀ z : ℂ, ‖(W : ℂ)⁻¹ ^ 3 * z‖ = ((W : ℝ)⁻¹) ^ 3 * ‖z‖ := by
    intro z; rw [norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
  have hW3 : (0 : ℝ) ≤ ((W : ℝ)⁻¹) ^ 3 := by positivity
  have hct : ∀ x y, (blockOf (sgnMat G false) x y) = (blockOf G y x)ᴴ := by
    intro x y
    simp only [sgnMat, Bool.false_eq_true, ↓reduceIte]
    exact lemmaNRates_blockOf_conjTranspose G x y
  have hst : ∀ x y, (blockOf (sgnMat G true) x y) = blockOf G x y := by
    intro x y; simp [sgnMat]
  have hsH : ∀ x y, Real.sqrt (lemmaNRates_hs (blockOf G x y)ᴴ) = Real.sqrt (blockHS2 G x y) := by
    intro x y; rw [lemmaNRates_hs_conjTranspose, lemmaNRates_hs_blockOf]
  have hsG : ∀ x y, Real.sqrt (lemmaNRates_hs (blockOf G x y)) = Real.sqrt (blockHS2 G x y) := by
    intro x y; rw [lemmaNRates_hs_blockOf]
  have hoH : ∀ x y, ‖(blockOf G x y)ᴴ‖ = ‖blockOf G x y‖ := fun x y =>
    Matrix.l2_opNorm_conjTranspose _
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lemmaNRates_loopTr_three, hn, hst, hst, hct]
    refine mul_le_mul_of_nonneg_left ?_ hW3
    refine (lemmaNRates_trace3_le _ _ _).trans (le_of_eq ?_)
    rw [hsG, hsH]
  · rw [lemmaNRates_loopTr_three, hn, hst, hst, hct]
    refine mul_le_mul_of_nonneg_left ?_ hW3
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
    refine (lemmaNRates_trace3_le _ _ _).trans (le_of_eq ?_)
    rw [hsG, hsH]; ring
  · rw [lemmaNRates_loopTr_three, hn, hst, hct, hct]
    refine mul_le_mul_of_nonneg_left ?_ hW3
    rw [Matrix.trace_mul_cycle]
    refine (lemmaNRates_trace3_le _ _ _).trans (le_of_eq ?_)
    rw [hoH, hsG, hsH]; ring
  · rw [lemmaNRates_loopTr_three, hn, hst, hct, hct]
    refine mul_le_mul_of_nonneg_left ?_ hW3
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
    refine (lemmaNRates_trace3_le _ _ _).trans (le_of_eq ?_)
    rw [hoH, hsG, hsH]

/-- The light term of `ℒ₂(a,b;+,-)` is at most `2γWτ Σ_c B(c)` when both cuts at `c` are at most
`B(c)` and the centered one-loops are at most `τ`. -/
private lemma lemmaNRates_light_reduce (g E : ℝ) (m : ℂ) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {τ : ℝ} (hτ : 0 ≤ τ)
    (havg : ∀ (c : Fin L) (s : Bool),
      ‖loopTr (resolventMat M (zChar g E m u)) ![c] ![s] - sgnScalar m s‖ ≤ τ)
    (a b : Fin L) (B : Fin L → ℝ)
    (hB : ∀ c, ‖loopTr (resolventMat M (zChar g E m u)) ![c, a, b] ![true, true, false]‖ ≤ B c ∧
      ‖loopTr (resolventMat M (zChar g E m u)) ![a, c, b] ![true, false, false]‖ ≤ B c) :
    ‖lightW g E m ![a, b] ![true, false] u M‖ ≤ 2 * gammaG g * W * τ * ∑ c, B c := by
  set G := resolventMat M (zChar g E m u) with hG
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hins0 : ∀ c : Fin L, insLab ![a, b] 0 c = ![c, a, b] := by
    intro c; funext i; fin_cases i <;> rfl
  have hins1 : ∀ c : Fin L, insLab ![a, b] 1 c = ![a, c, b] := by
    intro c; funext i; fin_cases i <;> rfl
  have hsgn0 : insSgn ![true, false] 0 = ![true, true, false] := by
    funext i; fin_cases i <;> rfl
  have hsgn1 : insSgn ![true, false] 1 = ![true, false, false] := by
    funext i; fin_cases i <;> rfl
  have hexp : lightW g E m ![a, b] ![true, false] u M = ((gammaG g * W : ℝ) : ℂ) * ∑ c,
      ((loopTr G ![c] ![true] - sgnScalar m true) * loopTr G ![c, a, b] ![true, true, false] +
        (loopTr G ![c] ![false] - sgnScalar m false) *
          loopTr G ![a, c, b] ![true, false, false]) := by
    unfold lightW
    rw [Fin.sum_univ_two, ← Finset.sum_add_distrib]
    simp only [hins0, hins1, hsgn0, hsgn1]
    rfl
  have hB0 : ∀ c, 0 ≤ B c := fun c => (norm_nonneg _).trans (hB c).1
  rw [hexp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsum : ‖∑ c, ((loopTr G ![c] ![true] - sgnScalar m true) *
        loopTr G ![c, a, b] ![true, true, false] +
      (loopTr G ![c] ![false] - sgnScalar m false) *
        loopTr G ![a, c, b] ![true, false, false])‖ ≤ ∑ c, 2 * τ * B c := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := mul_le_mul (havg c true) (hB c).1 (norm_nonneg _) hτ
    have h2 := mul_le_mul (havg c false) (hB c).2 (norm_nonneg _) hτ
    linarith
  calc gammaG g * W * ‖∑ c, ((loopTr G ![c] ![true] - sgnScalar m true) *
        loopTr G ![c, a, b] ![true, true, false] +
      (loopTr G ![c] ![false] - sgnScalar m false) *
        loopTr G ![a, c, b] ![true, false, false])‖
      ≤ gammaG g * W * ∑ c, 2 * τ * B c := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * gammaG g * W * τ * ∑ c, B c := by rw [← Finset.mul_sum]; ring

/-- At most `2(H + 1)` labels lie within distance `H ≥ 0` of a given label. -/
private lemma lemmaNRates_near_count (a : Fin L) {H : ℝ} (hH : 0 ≤ H) :
    ∑ c : Fin L, (if (cycDist a c : ℝ) ≤ H then (1 : ℝ) else 0) ≤ 2 * (H + 1) := by
  have h := lemmaNRates_sum_dist a (fun j => if (j : ℝ) ≤ H then (1 : ℝ) else 0)
    (fun j => by split_ifs <;> norm_num)
  refine h.trans ?_
  have h2 : ∑ j ∈ Finset.range L, (if (j : ℝ) ≤ H then (1 : ℝ) else 0) ≤ H + 1 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub : (Finset.range L).filter (fun j : ℕ => (j : ℝ) ≤ H) ⊆
        Finset.range (⌊H⌋₊ + 1) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      have := Nat.le_floor hj.2
      omega
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_range] at h3
    have h4 : ((((Finset.range L).filter (fun j : ℕ => (j : ℝ) ≤ H)).card : ℕ) : ℝ) ≤
        (⌊H⌋₊ : ℝ) + 1 := by exact_mod_cast h3
    have h5 := Nat.floor_le hH
    linarith
  linarith

end LightRow

/-- A cut bounded by `W⁻³ p q r` with `p ≤ W o X`, `q ≤ W Y`, `r ≤ W Z` is at most `o X Y Z`. -/
private lemma lemmaNRates_cut_scale {W : ℕ} (hW : 1 ≤ W) {t p q r o X Y Z : ℝ}
    (ht : t ≤ ((W : ℝ)⁻¹) ^ 3 * (p * (q * r))) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hp : p ≤ W * o * X) (hq : q ≤ W * Y) (hr : r ≤ W * Z) : t ≤ o * (X * (Y * Z)) := by
  have hW0 : (0 : ℝ) < W := by have : (1 : ℝ) ≤ W := by exact_mod_cast hW
                               linarith
  have h1 : p * (q * r) ≤ (W * o * X) * ((W * Y) * (W * Z)) :=
    mul_le_mul hp (mul_le_mul hq hr hr0 (hq0.trans hq)) (by positivity) (hp0.trans hp)
  calc t ≤ ((W : ℝ)⁻¹) ^ 3 * (p * (q * r)) := ht
    _ ≤ ((W : ℝ)⁻¹) ^ 3 * ((W * o * X) * ((W * Y) * (W * Z))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = o * (X * (Y * Z)) := by field_simp

/-- `√(B) ≤ W √(B')` from `B ≤ W² B'`. -/
private lemma lemmaNRates_sqrt_le {W : ℕ} {B B' : ℝ} (h : B ≤ (W : ℝ) ^ 2 * B') :
    Real.sqrt B ≤ W * Real.sqrt B' := by
  calc Real.sqrt B ≤ Real.sqrt ((W : ℝ) ^ 2 * B') := Real.sqrt_le_sqrt h
    _ = W * Real.sqrt B' := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg _)]

open scoped Matrix.Norms.L2Operator in
/-- Light row of the mixed pair, (C.18) [fo:eq:pair-far-light] and (C.20)
[fo:eq:pair-near-sources]: with the centered trace bound `τ`, the weighted operator bound
`W⁻¹‖G_{xy}‖ ≤ o√w(x,y)`, the rough Hilbert–Schmidt bound `s₀` and the long-edge bound
`W⁻²‖G_{xy}‖²_HS ≤ Λζ²w(x,y)` beyond `h`, the light term `𝒲₂(a,b)` is at most
`2γW τ Λζ² o Cℓ w(a,b)` for `d(a,b) > 2h`, and at most
`2√2 γW τ o ((4H + 2)s₀ + L√(s₀Λζ²ε₀))` for every pair, with `w ≤ ε₀` beyond the halo `H ≥ h`. -/
theorem lemmaNRates_light (g E : ℝ) (m : ℂ) {W L : ℕ} (hW : 1 ≤ W) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (w : Fin L → Fin L → ℝ)
    (hw0 : ∀ x y, 0 ≤ w x y) (hw2 : ∀ x y, w x y ≤ 2) (hwsym : ∀ x y, w x y = w y x)
    {Cw ℓ h H τ o s₀ Λ ζ ε₀ : ℝ} (hτ : 0 ≤ τ) (ho : 0 ≤ o) (hs₀ : 0 ≤ s₀) (hΛ : 0 ≤ Λ)
    (hH : 0 ≤ H) (hhH : h ≤ H)
    (hconv : ∀ x y, ∑ c, Real.sqrt (w x c * w c y) ≤ Cw * ℓ * Real.sqrt (w x y))
    (havg : ∀ (c : Fin L) (s : Bool),
      ‖loopTr (resolventMat M (zChar g E m u)) ![c] ![s] - sgnScalar m s‖ ≤ τ)
    (hop : ∀ x y, ‖blockOf (resolventMat M (zChar g E m u)) x y‖ ≤ W * o * Real.sqrt (w x y))
    (hhs0 : ∀ x y, blockHS2 (resolventMat M (zChar g E m u)) x y ≤ (W : ℝ) ^ 2 * s₀)
    (hhs : ∀ x y, h < cycDist x y →
      blockHS2 (resolventMat M (zChar g E m u)) x y ≤ (W : ℝ) ^ 2 * Λ * ζ ^ 2 * w x y)
    (hfar : ∀ x y, H < cycDist x y → w x y ≤ ε₀) (a b : Fin L) :
    (2 * h < cycDist a b → ‖lightW g E m ![a, b] ![true, false] u M‖ ≤
        2 * gammaG g * W * τ * Λ * ζ ^ 2 * o * Cw * ℓ * w a b) ∧
      ‖lightW g E m ![a, b] ![true, false] u M‖ ≤
        2 * Real.sqrt 2 * gammaG g * W * τ * o *
          ((4 * H + 2) * s₀ + L * Real.sqrt (s₀ * Λ * ζ ^ 2 * ε₀)) := by
  set G := resolventMat M (zChar g E m u) with hG
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hP : 0 ≤ Λ * ζ ^ 2 := by positivity
  have hsP : Real.sqrt (Λ * ζ ^ 2) * Real.sqrt (Λ * ζ ^ 2) = Λ * ζ ^ 2 := Real.mul_self_sqrt hP
  have hhs' : ∀ x y, h < cycDist x y →
      Real.sqrt (blockHS2 G x y) ≤ W * Real.sqrt (Λ * ζ ^ 2 * w x y) := fun x y hxy =>
    lemmaNRates_sqrt_le ((hhs x y hxy).trans (le_of_eq (by ring)))
  have hhs0' : ∀ x y, Real.sqrt (blockHS2 G x y) ≤ W * Real.sqrt s₀ := fun x y =>
    lemmaNRates_sqrt_le (hhs0 x y)
  have hop2 : ∀ x y, ‖blockOf G x y‖ ≤ W * o * Real.sqrt 2 := fun x y =>
    (hop x y).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hw2 x y)) (by positivity))
  have hsq0 : ∀ x y, 0 ≤ Real.sqrt (blockHS2 G x y) := fun _ _ => Real.sqrt_nonneg _
  have hnorm0 : ∀ x y, 0 ≤ ‖blockOf G x y‖ := fun _ _ => norm_nonneg _
  constructor
  · intro hab
    have hab' : h < (cycDist b a : ℝ) := by
      rw [lemmaNRates_cycDist_comm]
      have : (0 : ℝ) ≤ cycDist a b := Nat.cast_nonneg _
      linarith
    set B : Fin L → ℝ := fun c =>
      o * (Λ * ζ ^ 2) * (Real.sqrt (w a c * w c b) * Real.sqrt (w a b)) with hB
    have hBc : ∀ c, ‖loopTr G ![c, a, b] ![true, true, false]‖ ≤ B c ∧
        ‖loopTr G ![a, c, b] ![true, false, false]‖ ≤ B c := by
      intro c
      obtain ⟨⟨h01, h02⟩, ⟨h11, h12⟩⟩ := lemmaNRates_cut_bound (W := W) G a b c
      have htri : (cycDist a b : ℝ) ≤ cycDist c a + cycDist b c := by
        have := lemmaNRates_cycDist_tri a c b
        rw [lemmaNRates_cycDist_comm a c, lemmaNRates_cycDist_comm c b] at this
        exact_mod_cast this
      have hca : ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y →
          Real.sqrt x * (Real.sqrt (Λ * ζ ^ 2 * y) * Real.sqrt (Λ * ζ ^ 2 * z)) =
            Λ * ζ ^ 2 * (Real.sqrt (y * x) * Real.sqrt z) := by
        intro x y z hx hy
        calc Real.sqrt x * (Real.sqrt (Λ * ζ ^ 2 * y) * Real.sqrt (Λ * ζ ^ 2 * z))
            = Real.sqrt x * Real.sqrt y * Real.sqrt z *
                (Real.sqrt (Λ * ζ ^ 2) * Real.sqrt (Λ * ζ ^ 2)) := by
              rw [Real.sqrt_mul hP, Real.sqrt_mul hP]; ring
          _ = _ := by rw [hsP, Real.sqrt_mul hy]; ring
      by_cases hc : h < (cycDist c a : ℝ)
      · -- the edge `ca` is long: operator norm on `bc`
        have key : ∀ t : ℝ, t ≤ ((W : ℝ)⁻¹) ^ 3 * (‖blockOf G b c‖ *
            (Real.sqrt (blockHS2 G c a) * Real.sqrt (blockHS2 G b a))) → t ≤ B c := by
          intro t ht
          refine (lemmaNRates_cut_scale hW ht (hnorm0 _ _) (hsq0 _ _) (hsq0 _ _) (hop b c)
            (hhs' c a hc) (hhs' b a hab')).trans (le_of_eq ?_)
          rw [hca _ _ _ (hw0 _ _) (hw0 _ _), hB, hwsym b c, hwsym c a, hwsym b a]
          ring
        exact ⟨key _ h01, key _ h11⟩
      · -- otherwise the edge `bc` is long: operator norm on `ca`
        have hbc : h < (cycDist b c : ℝ) := by linarith [not_lt.mp hc]
        have key : ∀ t : ℝ, t ≤ ((W : ℝ)⁻¹) ^ 3 * (‖blockOf G c a‖ *
            (Real.sqrt (blockHS2 G b c) * Real.sqrt (blockHS2 G b a))) → t ≤ B c := by
          intro t ht
          refine (lemmaNRates_cut_scale hW ht (hnorm0 _ _) (hsq0 _ _) (hsq0 _ _) (hop c a)
            (hhs' b c hbc) (hhs' b a hab')).trans (le_of_eq ?_)
          rw [hca _ _ _ (hw0 _ _) (hw0 _ _), hB, hwsym b c, hwsym c a, hwsym b a,
            mul_comm (w c b)]
          ring
        exact ⟨key _ h02, key _ h12⟩
    refine (lemmaNRates_light_reduce g E m u M hτ havg a b B hBc).trans ?_
    have hsum : ∑ c, B c ≤ o * (Λ * ζ ^ 2) * (Cw * ℓ * Real.sqrt (w a b) * Real.sqrt (w a b)) := by
      simp only [hB, ← Finset.mul_sum, ← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hconv a b)
        (Real.sqrt_nonneg _)) (by positivity)
    have hww : Real.sqrt (w a b) * Real.sqrt (w a b) = w a b := Real.mul_self_sqrt (hw0 a b)
    calc 2 * gammaG g * W * τ * ∑ c, B c
        ≤ 2 * gammaG g * W * τ *
            (o * (Λ * ζ ^ 2) * (Cw * ℓ * Real.sqrt (w a b) * Real.sqrt (w a b))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * gammaG g * W * τ * Λ * ζ ^ 2 * o * Cw * ℓ * w a b := by
          rw [mul_assoc (Cw * ℓ), hww]; ring
  · set B : Fin L → ℝ := fun c => Real.sqrt 2 * o *
      (s₀ * (if (cycDist a c : ℝ) ≤ H then (1 : ℝ) else 0) + Real.sqrt (s₀ * Λ * ζ ^ 2 * ε₀))
      with hB
    have hss : Real.sqrt s₀ * Real.sqrt s₀ = s₀ := Real.mul_self_sqrt hs₀
    have hBc : ∀ c, ‖loopTr G ![c, a, b] ![true, true, false]‖ ≤ B c ∧
        ‖loopTr G ![a, c, b] ![true, false, false]‖ ≤ B c := by
      intro c
      obtain ⟨⟨h01, _⟩, ⟨h11, _⟩⟩ := lemmaNRates_cut_bound (W := W) G a b c
      have hr0 : 0 ≤ Real.sqrt (s₀ * Λ * ζ ^ 2 * ε₀) := Real.sqrt_nonneg _
      by_cases hc : (cycDist a c : ℝ) ≤ H
      · have key : ∀ t : ℝ, t ≤ ((W : ℝ)⁻¹) ^ 3 * (‖blockOf G b c‖ *
            (Real.sqrt (blockHS2 G c a) * Real.sqrt (blockHS2 G b a))) → t ≤ B c := by
          intro t ht
          refine (lemmaNRates_cut_scale hW ht (hnorm0 _ _) (hsq0 _ _) (hsq0 _ _) (hop2 b c)
            (hhs0' c a) (hhs0' b a)).trans ?_
          rw [hB]
          simp only [hc, ite_true, mul_one]
          have : 0 ≤ Real.sqrt 2 * o := by positivity
          nlinarith [mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hr0 : s₀ ≤ s₀ + _) this]
        exact ⟨key _ h01, key _ h11⟩
      · have hca : H < (cycDist c a : ℝ) := by
          rw [lemmaNRates_cycDist_comm]; exact not_le.mp hc
        have hε : Real.sqrt (blockHS2 G c a) ≤ W * Real.sqrt (Λ * ζ ^ 2 * ε₀) :=
          (hhs' c a (lt_of_le_of_lt hhH hca)).trans (mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hfar c a hca) hP)) (Nat.cast_nonneg _))
        have key : ∀ t : ℝ, t ≤ ((W : ℝ)⁻¹) ^ 3 * (‖blockOf G b c‖ *
            (Real.sqrt (blockHS2 G c a) * Real.sqrt (blockHS2 G b a))) → t ≤ B c := by
          intro t ht
          refine (lemmaNRates_cut_scale hW ht (hnorm0 _ _) (hsq0 _ _) (hsq0 _ _) (hop2 b c)
            hε (hhs0' b a)).trans (le_of_eq ?_)
          rw [hB]
          simp only [hc, ite_false, mul_zero, zero_add]
          rw [show s₀ * Λ * ζ ^ 2 * ε₀ = Λ * ζ ^ 2 * ε₀ * s₀ by ring, Real.sqrt_mul' _ hs₀]
          ring
        exact ⟨key _ h01, key _ h11⟩
    refine (lemmaNRates_light_reduce g E m u M hτ havg a b B hBc).trans ?_
    have hcount := lemmaNRates_near_count (L := L) a hH
    have hsum : ∑ c, B c ≤ Real.sqrt 2 * o *
        ((4 * H + 2) * s₀ + L * Real.sqrt (s₀ * Λ * ζ ^ 2 * ε₀)) := by
      simp only [hB, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : s₀ * ∑ c : Fin L, (if (cycDist a c : ℝ) ≤ H then (1 : ℝ) else 0) ≤
          (4 * H + 2) * s₀ := by
        nlinarith [mul_le_mul_of_nonneg_left hcount hs₀]
      linarith
    calc 2 * gammaG g * W * τ * ∑ c, B c
        ≤ 2 * gammaG g * W * τ * (Real.sqrt 2 * o *
            ((4 * H + 2) * s₀ + L * Real.sqrt (s₀ * Λ * ζ ^ 2 * ε₀))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring

/-! ### Bracket row -/

section BracketRow

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ}

/-- `‖X Y‖²_HS ≤ ‖Y‖² ‖X‖²_HS`. -/
private lemma lemmaNRates_hs_mul_right {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℂ) : lemmaNRates_hs (X * Y) ≤ ‖Y‖ ^ 2 * lemmaNRates_hs X := by
  have h := lemmaNRates_hs_mul_left Yᴴ Xᴴ
  rwa [← Matrix.conjTranspose_mul, lemmaNRates_hs_conjTranspose, Matrix.l2_opNorm_conjTranspose,
    lemmaNRates_hs_conjTranspose] at h

/-- `‖A B C‖²_HS ≤ ‖A‖² ‖C‖² ‖B‖²_HS`. -/
private lemma lemmaNRates_hs_three {n : Type*} [Fintype n] [DecidableEq n]
    (A B C : Matrix n n ℂ) :
    lemmaNRates_hs (A * (B * C)) ≤ ‖A‖ ^ 2 * ‖C‖ ^ 2 * lemmaNRates_hs B := by
  calc lemmaNRates_hs (A * (B * C)) ≤ ‖A‖ ^ 2 * lemmaNRates_hs (B * C) :=
        lemmaNRates_hs_mul_left _ _
    _ ≤ ‖A‖ ^ 2 * (‖C‖ ^ 2 * lemmaNRates_hs B) :=
        mul_le_mul_of_nonneg_left (lemmaNRates_hs_mul_right _ _) (by positivity)
    _ = _ := by ring

/-- The diagonal block of `X E_a (Y E_b Z)` is `W⁻² X_{ca} Y_{ab} Z_{bc}`. -/
private lemma lemmaNRates_blockOf_five (X Y Z : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b c : Fin L) :
    blockOf (X * blockE W L a * (Y * blockE W L b * Z)) c c =
      ((W : ℂ)⁻¹ * (W : ℂ)⁻¹) • (blockOf X c a * (blockOf Y a b * blockOf Z b c)) := by
  rw [lemmaNRates_blockOf_mul_blockE_mul, lemmaNRates_blockOf_mul_blockE_mul, Matrix.mul_smul,
    smul_smul]

private lemma lemmaNRates_blockOf_add (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (c d : Fin L) : blockOf (X + Y) c d = blockOf X c d + blockOf Y c d := by
  ext α β; simp [blockOf]

/-- `‖Z_{cc}‖²_HS ≤ 4W⁻⁴ ‖G_{ca}‖² ‖G_{bc}‖² ‖G_{ba}‖²_HS` for the bracket matrix `Z`. -/
private lemma lemmaNRates_hs_Z (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b c : Fin L) :
    lemmaNRates_hs (blockOf (G * blockE W L a * (Gᴴ * blockE W L b * G) +
        Gᴴ * blockE W L b * (G * blockE W L a * Gᴴ)) c c) ≤
      4 * ((W : ℝ)⁻¹) ^ 4 * (‖blockOf G c a‖ ^ 2 * ‖blockOf G b c‖ ^ 2 * blockHS2 G b a) := by
  rw [lemmaNRates_blockOf_add, lemmaNRates_blockOf_five, lemmaNRates_blockOf_five]
  refine (lemmaNRates_hs_add_le _ _).trans ?_
  rw [lemmaNRates_hs_smul, lemmaNRates_hs_smul]
  have hk : ‖(W : ℂ)⁻¹ * (W : ℂ)⁻¹‖ ^ 2 = ((W : ℝ)⁻¹) ^ 4 := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]; ring
  rw [hk]
  have h0 := lemmaNRates_hs_three (blockOf G c a) (blockOf Gᴴ a b) (blockOf G b c)
  have h1 := lemmaNRates_hs_three (blockOf Gᴴ c b) (blockOf G b a) (blockOf Gᴴ a c)
  have e0 : lemmaNRates_hs (blockOf Gᴴ a b) = blockHS2 G b a := by
    rw [lemmaNRates_blockOf_conjTranspose, lemmaNRates_hs_conjTranspose, lemmaNRates_hs_blockOf]
  have e1 : ∀ x y, ‖blockOf Gᴴ x y‖ = ‖blockOf G y x‖ := fun x y => by
    rw [lemmaNRates_blockOf_conjTranspose, Matrix.l2_opNorm_conjTranspose]
  rw [e0] at h0
  rw [e1, e1, lemmaNRates_hs_blockOf] at h1
  have hW4 : (0 : ℝ) ≤ ((W : ℝ)⁻¹) ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h0 hW4, mul_le_mul_of_nonneg_left h1 hW4]

/-- `Tr(P_c Z P_c Z*) = ‖Z_{cc}‖²_HS` with `P_c = W E_c`. -/
private lemma lemmaNRates_trace_proj (hW : 1 ≤ W) (c : Fin L)
    (Z : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    (((W : ℂ) • blockE W L c) * Z * ((W : ℂ) • blockE W L c) * Zᴴ).trace =
      ((lemmaNRates_hs (blockOf Z c c) : ℝ) : ℂ) := by
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
  have e : ((W : ℂ) • blockE W L c) * Z * ((W : ℂ) • blockE W L c) * Zᴴ =
      ((W : ℂ) * W) • (blockE W L c * (Z * blockE W L c * Zᴴ)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [e, Matrix.trace_smul, Matrix.trace_mul_comm, lemmaNRates_trace_mul_blockE,
    lemmaNRates_blockOf_mul_blockE_mul, Matrix.trace_smul, lemmaNRates_blockOf_conjTranspose,
    lemmaNRates_trace_mul_conjTranspose, smul_eq_mul, smul_eq_mul]
  field_simp

/-- The bracket of `ℒ₂(a,b;+,-)` with itself is `(γ/W) Σ_c ‖Z_{cc}‖²_HS` with
`Z = G E_a G* E_b G + G* E_b G E_a G*`. -/
private lemma lemmaNRates_gamma_eq (g E : ℝ) (m : ℂ) (hm : 0 < m.im) (hW : 1 ≤ W) {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (a b : Fin L) :
    blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, false] u)
        (resLoop g E m ![a, b] ![true, false] u) M =
      ((gammaG g / W : ℝ) : ℂ) * ∑ c, ((lemmaNRates_hs (blockOf
        (resolventMat M (zChar g E m u) * blockE W L a *
            ((resolventMat M (zChar g E m u))ᴴ * blockE W L b * resolventMat M (zChar g E m u)) +
          (resolventMat M (zChar g E m u))ᴴ * blockE W L b *
            (resolventMat M (zChar g E m u) * blockE W L a * (resolventMat M (zChar g E m u))ᴴ))
        c c) : ℝ) : ℂ) := by
  rw [blockGamma_loopTr g E m hm hu hM]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  set G := resolventMat M (zChar g E m u)
  have hB0 : loopB G ![a, b] ![true, false] 0 = G * blockE W L a * (Gᴴ * blockE W L b * G) := by
    simp [loopB, List.ofFn_succ, sgnMat, Matrix.mul_assoc]
  have hB1 : loopB G ![a, b] ![true, false] 1 = Gᴴ * blockE W L b * (G * blockE W L a * Gᴴ) := by
    simp [loopB, List.ofFn_succ, sgnMat, Matrix.mul_assoc]
  rw [← lemmaNRates_trace_proj hW c]
  simp only [Fin.sum_univ_two, hB0, hB1, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.trace_add]
  ring

end BracketRow

open scoped Matrix.Norms.L2Operator in
/-- Bracket row of the mixed pair, (C.19) [fo:eq:pair-far-bracket] and (C.20)
[fo:eq:pair-near-sources]: with the weighted operator bound `W⁻¹‖G_{xy}‖ ≤ o√w(x,y)` and
`W⁻²‖G_{ba}‖²_HS ≤ η`, the bracket (5.9) [gc:eq:bracket] of `ℒ₂(a,b;+,-)` is at most
`4γW η o⁴ C ℓ w(a,b)`. -/
theorem lemmaNRates_bracket (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L : ℕ} (hW : 1 ≤ W) {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (w : Fin L → Fin L → ℝ) (hw0 : ∀ x y, 0 ≤ w x y) (hwsym : ∀ x y, w x y = w y x)
    {Cw ℓ o η : ℝ} (ho : 0 ≤ o) (hconv : ∀ x y, ∑ c, w x c * w c y ≤ Cw * ℓ * w x y)
    (hop : ∀ x y, ‖blockOf (resolventMat M (zChar g E m u)) x y‖ ≤ W * o * Real.sqrt (w x y))
    (a b : Fin L) (hab : blockHS2 (resolventMat M (zChar g E m u)) b a ≤ (W : ℝ) ^ 2 * η) :
    (blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, false] u)
        (resLoop g E m ![a, b] ![true, false] u) M).re ≤
      4 * gammaG g * W * η * o ^ 4 * Cw * ℓ * w a b := by
  have _ := ho
  rw [lemmaNRates_gamma_eq g E m hm hW hu hM a b, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  set G := resolventMat M (zChar g E m u) with hG
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hη : 0 ≤ η := by
    have h0 : 0 ≤ blockHS2 G b a := by unfold blockHS2; positivity
    have : 0 ≤ (W : ℝ) ^ 2 * η := h0.trans hab
    exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℝ) < (W : ℝ) ^ 2)
  have hop2 : ∀ x y, ‖blockOf G x y‖ ^ 2 ≤ (W : ℝ) ^ 2 * o ^ 2 * w x y := by
    intro x y
    calc ‖blockOf G x y‖ ^ 2 ≤ ((W : ℝ) * o * Real.sqrt (w x y)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hop x y) 2
      _ = (W : ℝ) ^ 2 * o ^ 2 * w x y := by rw [mul_pow, Real.sq_sqrt (hw0 x y)]; ring
  have hc : ∀ c, lemmaNRates_hs (blockOf (G * blockE W L a * (Gᴴ * blockE W L b * G) +
        Gᴴ * blockE W L b * (G * blockE W L a * Gᴴ)) c c) ≤
      4 * (W : ℝ) ^ 2 * η * o ^ 4 * (w a c * w c b) := by
    intro c
    refine (lemmaNRates_hs_Z G a b c).trans ?_
    have h1 := mul_le_mul (hop2 c a) (hop2 b c) (by positivity)
      (by have := hw0 c a; positivity)
    have h2 := mul_le_mul h1 hab (by unfold blockHS2; positivity)
      (by have := hw0 c a; have := hw0 b c; positivity)
    calc 4 * ((W : ℝ)⁻¹) ^ 4 * (‖blockOf G c a‖ ^ 2 * ‖blockOf G b c‖ ^ 2 * blockHS2 G b a)
        ≤ 4 * ((W : ℝ)⁻¹) ^ 4 * ((W : ℝ) ^ 2 * o ^ 2 * w c a * ((W : ℝ) ^ 2 * o ^ 2 * w b c) *
            ((W : ℝ) ^ 2 * η)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 4 * (W : ℝ) ^ 2 * η * o ^ 4 * (w a c * w c b) := by
          rw [hwsym c a, hwsym b c]; field_simp
  calc gammaG g / W * ∑ c, lemmaNRates_hs (blockOf (G * blockE W L a *
        (Gᴴ * blockE W L b * G) + Gᴴ * blockE W L b * (G * blockE W L a * Gᴴ)) c c)
      ≤ gammaG g / W * ∑ c, 4 * (W : ℝ) ^ 2 * η * o ^ 4 * (w a c * w c b) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hc c) (by positivity)
    _ = gammaG g / W * (4 * (W : ℝ) ^ 2 * η * o ^ 4) * ∑ c, w a c * w c b := by
        rw [← Finset.mul_sum]; ring
    _ ≤ gammaG g / W * (4 * (W : ℝ) ^ 2 * η * o ^ 4) * (Cw * ℓ * w a b) :=
        mul_le_mul_of_nonneg_left (hconv a b) (by positivity)
    _ = 4 * gammaG g * W * η * o ^ 4 * Cw * ℓ * w a b := by field_simp
/-- The terminal scale against the earlier one, from (5.18) [fo:eq:scale]: for `u ≤ v < 1`,
`ℓ_v ≤ √((1-u)/(1-v)) ℓ_u`. -/
theorem lemmaNRates_ell_ratio (g : ℝ) (hg : 0 ≤ g) (L : ℕ) {u v : ℝ} (huv : u ≤ v) (hv : v < 1) :
    ellProp g L v ≤ Real.sqrt ((1 - u) / (1 - v)) * ellProp g L u := by
  have _ := hg
  have h1v : 0 < 1 - v := by linarith
  have h1u : 0 < 1 - u := by linarith
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  set ρ := Real.sqrt ((1 - u) / (1 - v)) with hρ
  have hρ1 : 1 ≤ ρ := by
    rw [hρ, Real.one_le_sqrt, le_div_iff₀ h1v]; linarith
  have hsq : Real.sqrt (gammaG g * (1 - u)) = ρ * Real.sqrt (gammaG g * (1 - v)) := by
    rw [hρ, ← Real.sqrt_mul (div_nonneg h1u.le h1v.le)]
    congr 1; field_simp
  have hs0 : 0 < Real.sqrt (gammaG g * (1 - v)) := Real.sqrt_pos.mpr (by positivity)
  have hx : g / Real.sqrt (gammaG g * (1 - v)) = ρ * (g / Real.sqrt (gammaG g * (1 - u))) := by
    rw [hsq]; field_simp
  unfold ellProp
  rw [hx, mul_min_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ ρ)]
  apply min_le_min
  · have : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    nlinarith
  · nlinarith

section Examples

open scoped Matrix.Norms.L2Operator

end Examples

end LSBA
