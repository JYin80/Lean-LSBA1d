import LSBA.Primitive.Defs

/-!
# Uniform profile: abstract lemmas

The kernel and core contracts of Appendix B.5 [app:uniform-profile], Lemma B.4 [uvp:lem:anchor] and
Theorem B.6 [uvp:thm:molecule], stated abstractly.
-/

open MeasureTheory Real Filter Topology Complex Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The kernel contract of Appendix B.5 [app:uniform-profile] at scale `a`: (A.16) [uvp:eq:stable]
for the stable legs, and (A.38) [uvp:eq:xi], (A.39) [uvp:eq:xi1], (A.40) [uvp:eq:xi2], (A.41)
[uvp:eq:error] for the even kernels `Ξ` and `E`, with `g²` replaced by `a`, `ℓ = min{L, a/√δ}`,
`λ = √δ/a`. -/
def UvpKernels (L : ℕ) [NeZero L] (a δ c C ε : ℝ) (Ξ Er : Fin L → ℂ) {k : ℕ}
    (mixed : Fin k → Bool) (Vst : Fin k → Fin L → ℂ) : Prop :=
  let ℓ := min (L : ℝ) (a / Real.sqrt δ)
  let lam := Real.sqrt δ / a
  (∀ x, Ξ (-x) = Ξ x) ∧ (∀ x, Er (-x) = Er x) ∧
  (∀ j, mixed j = false → (∀ x, Vst j (-x) = Vst j x) ∧
    ∑ x, Real.exp (c * cycDist x 0 / a) * ‖Vst j x‖ ≤ C) ∧
  ∑ x, ‖Ξ x‖ ≤ C / δ ∧ (∀ x, ‖Ξ x‖ ≤ C / (δ * ℓ)) ∧
  ∑ x, ‖Ξ (finRotate L x) - Ξ x‖ ≤ C * lam / δ ∧
  (∀ x, ‖Ξ (finRotate L x) - Ξ x‖ ≤ C * lam / (δ * ℓ)) ∧
  ∑ x, ‖Ξ (finRotate L (finRotate L x)) - 2 * Ξ (finRotate L x) + Ξ x‖ ≤ C * lam ^ 2 / δ ∧
  ∑ x, ‖Er x‖ ≤ C * ε / δ ^ 2 ∧ (∀ x, ‖Er x‖ ≤ C * ε / (a * δ ^ 2)) ∧ ε ≤ δ ^ 2

/-- The core hypotheses of Appendix B.5 [app:uniform-profile]: translation and reflection
invariance, the profile (B.7) [uvp:eq:coreprofile], and, for an alternating molecule, the signed
mass (B.9) [uvp:eq:mass] at every anchor. -/
def UvpCore (L : ℕ) [NeZero L] (a δ c C : ℝ) {k : ℕ} (alt : Prop)
    (S : (Fin k → Fin L) → ℂ) : Prop :=
  (∀ (x : Fin k → Fin L) (z : Fin L), S (fun i => x i + z) = S x) ∧
  (∀ x, S (fun i => -x i) = S x) ∧
  (∀ x, ‖S x‖ ≤ C * Real.exp (-(c * wordDiam x / a))) ∧
  (alt → ∀ v : Fin k, ‖∑ x ∈ Finset.univ.filter (fun x : Fin k → Fin L => x v = 0), S x‖ ≤
    C * δ * a ^ (k - 1))

/-- The external factor of the leg `j`: `U = I + Ξ + E` on a mixed leg, the stable kernel
otherwise. -/
def uvpLeg {L : ℕ} [NeZero L] (Ξ Er : Fin L → ℂ) {k : ℕ} (mixed : Fin k → Bool)
    (Vst : Fin k → Fin L → ℂ) (j : Fin k) : Fin L → ℂ :=
  if mixed j then fun x => (if x = 0 then 1 else 0) + Ξ x + Er x else Vst j

/-- Dressing `F(x) = Σ_y S(y) Π_j V_j(x_j - y_j)`; with `some v` the factor of the leg `v` is
replaced by the identity (`F^{⟨v⟩}`), Appendix B.5 [app:uniform-profile]. -/
def uvpDress {L : ℕ} [NeZero L] (Ξ Er : Fin L → ℂ) {k : ℕ} (mixed : Fin k → Bool)
    (Vst : Fin k → Fin L → ℂ) (S : (Fin k → Fin L) → ℂ) (undress : Option (Fin k))
    (x : Fin k → Fin L) : ℂ :=
  ∑ y, S y * ∏ j, (if undress = some j then (if x j = y j then 1 else 0)
    else uvpLeg Ξ Er mixed Vst j (x j - y j))

/-! ### Cyclic distance on `ℤ_L` -/

private lemma uvp_cycDist_eq {L : ℕ} [NeZero L] (a b : Fin L) :
    cycDist a b = min (a - b).val (-(a - b)).val := by
  rw [neg_sub]
  unfold cycDist
  rw [Fin.val_sub, Fin.val_sub]
  have ha := a.isLt
  have hb := b.isLt
  have e1 : L - (b : ℕ) + (a : ℕ) = (a : ℕ) + L - (b : ℕ) := by omega
  have e2 : L - (a : ℕ) + (b : ℕ) = (b : ℕ) + L - (a : ℕ) := by omega
  rw [e1, e2]

private lemma uvp_cycDist_zero_right {L : ℕ} [NeZero L] (a : Fin L) :
    cycDist a 0 = min a.val (L - a.val) := by
  rw [uvp_cycDist_eq, sub_zero, Fin.val_neg']
  rcases Nat.eq_zero_or_pos a.val with h | h
  · rw [h]; simp
  · rw [Nat.mod_eq_of_lt (by have := a.isLt; omega)]

private lemma uvp_cycDist_add_right {L : ℕ} [NeZero L] (a b z : Fin L) :
    cycDist (a + z) (b + z) = cycDist a b := by
  rw [uvp_cycDist_eq, uvp_cycDist_eq, add_sub_add_right_eq_sub]

private lemma uvp_cycDist_neg {L : ℕ} [NeZero L] (a : Fin L) :
    cycDist (-a) 0 = cycDist a 0 := by
  rw [uvp_cycDist_eq, uvp_cycDist_eq, sub_zero, sub_zero, neg_neg, min_comm]

private lemma uvp_cycDist_self {L : ℕ} [NeZero L] (a : Fin L) : cycDist a a = 0 := by
  rw [uvp_cycDist_eq]; simp

private lemma uvp_cycDist_peel {L : ℕ} [NeZero L] (x : Fin L) (hx : x ≠ 0) :
    ∃ s : Fin L, (s = 1 ∨ s = -1) ∧ cycDist (x - s) 0 + 1 = cycDist x 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by have := NeZero.ne L; omega⟩
  have hv : 1 ≤ x.val := by
    rcases Nat.eq_zero_or_pos x.val with h | h
    · exact absurd (Fin.ext (by simpa using h)) hx
    · exact h
  have hlt := x.isLt
  by_cases h : x.val ≤ n + 1 - x.val
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [uvp_cycDist_zero_right, uvp_cycDist_zero_right, Fin.coe_sub_one]
    simp only [hx, ↓reduceIte]
    omega
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [sub_neg_eq_add, uvp_cycDist_zero_right, uvp_cycDist_zero_right, Fin.val_add_one]
    by_cases hl : x = Fin.last n
    · simp only [hl, ↓reduceIte]
      have : x.val = n := by rw [hl]; simp
      omega
    · simp only [hl, ↓reduceIte]
      have : x.val ≠ n := fun h' => hl (Fin.ext (by simpa using h'))
      omega

/-- The geometric sum of an exponential in the cyclic distance. -/
private lemma uvp_geom_sum {L : ℕ} [NeZero L] (c' a : ℝ) (hc' : 0 < c') (ha : 0 < a) :
    ∑ y : Fin L, Real.exp (-(c' * (cycDist y 0 : ℝ) / a)) ≤ 2 * (1 + a / c') := by
  set s : ℝ := c' / a with hs
  have hs0 : 0 < s := div_pos hc' ha
  set r : ℝ := Real.exp (-s) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hpow : ∀ n : ℕ, Real.exp (-(c' * (n : ℝ) / a)) = r ^ n := by
    intro n
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    rw [hs]; field_simp
  have hgeom : ∑ y : Fin L, r ^ (y : ℕ) ≤ 1 / (1 - r) := by
    rw [Fin.sum_univ_eq_sum_range (fun n => r ^ n) L, Finset.range_eq_Ico]
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := L) hr0.le hr1
    simpa using this
  have hneg : ∑ y : Fin L, r ^ ((-y : Fin L) : ℕ) = ∑ y : Fin L, r ^ (y : ℕ) :=
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun x => rfl)
  have hterm : ∀ y : Fin L, Real.exp (-(c' * (cycDist y 0 : ℝ) / a)) ≤
      r ^ (y : ℕ) + r ^ ((-y : Fin L) : ℕ) := by
    intro y
    rw [hpow, uvp_cycDist_eq, sub_zero]
    rcases min_choice (y : ℕ) ((-y : Fin L) : ℕ) with h | h
    · rw [h]; have : 0 ≤ r ^ ((-y : Fin L) : ℕ) := by positivity
      linarith
    · rw [h]; have : 0 ≤ r ^ (y : ℕ) := by positivity
      linarith
  calc ∑ y : Fin L, Real.exp (-(c' * (cycDist y 0 : ℝ) / a))
      ≤ ∑ y : Fin L, (r ^ (y : ℕ) + r ^ ((-y : Fin L) : ℕ)) :=
        Finset.sum_le_sum (fun y _ => hterm y)
    _ = 2 * ∑ y : Fin L, r ^ (y : ℕ) := by
        rw [Finset.sum_add_distrib, hneg]; ring
    _ ≤ 2 * (1 / (1 - r)) := by gcongr
    _ ≤ 2 * (1 + a / c') := by
        have h1 : 1 / (1 - r) ≤ 1 + a / c' := by
          have hE : s + 1 ≤ Real.exp s := Real.add_one_le_exp s
          have hrE : r * Real.exp s = 1 := by rw [hr, ← Real.exp_add]; simp
          have hlow : 1 - r ≥ s / (1 + s) := by
            have : r ≤ 1 / (1 + s) := by
              rw [le_div_iff₀ (by linarith)]
              nlinarith
            have h2 : 1 - 1 / (1 + s) = s / (1 + s) := by field_simp; ring
            linarith
          have hpos : 0 < s / (1 + s) := by positivity
          calc 1 / (1 - r) ≤ 1 / (s / (1 + s)) := by gcongr
            _ = 1 + a / c' := by rw [hs]; field_simp; ring
        linarith

/-! ### Sums over `ℤ_L^k` -/

/-- Anchoring at the coordinate `p`: every point is a common translate of a point with
`w p = 0`. -/
private lemma uvp_sum_anchor {L k : ℕ} [NeZero L] {β : Type*} [AddCommMonoid β] (p : Fin k)
    (F : (Fin k → Fin L) → β) :
    ∑ y, F y =
      ∑ u : Fin L, ∑ w : Fin k → Fin L, (if w p = 0 then F (w + fun _ => u) else 0) := by
  have h1 : ∀ u : Fin L, ∑ w : Fin k → Fin L, (if w p = 0 then F (w + fun _ => u) else 0)
      = ∑ y : Fin k → Fin L, (if y p = u then F y else 0) := by
    intro u
    refine Fintype.sum_equiv (Equiv.addRight (fun _ : Fin k => u)) _ _ (fun w => ?_)
    simp
  rw [Finset.sum_congr rfl (fun u _ => h1 u), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp

/-- The sum over the points with `w p = 0` of a product over the other coordinates factorizes. -/
private lemma uvp_sum_prod_anchor {L k : ℕ} [NeZero L] (p : Fin k) (g : Fin k → Fin L → ℝ) :
    ∑ w : Fin k → Fin L, (if w p = 0 then ∏ i ∈ Finset.univ.erase p, g i (w i) else 0)
      = ∏ i ∈ Finset.univ.erase p, ∑ x : Fin L, g i x := by
  set ψ : Fin k → Fin L → ℝ := fun i x => if i = p then (if x = 0 then 1 else 0) else g i x with hψ
  have h := Fintype.prod_sum ψ
  have hL : ∏ i, ∑ x : Fin L, ψ i x = ∏ i ∈ Finset.univ.erase p, ∑ x : Fin L, g i x := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => ∑ x : Fin L, ψ i x) (Finset.mem_univ p)]
    have h1 : ∑ x : Fin L, ψ p x = 1 := by simp [hψ]
    rw [h1, one_mul]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have : i ≠ p := Finset.ne_of_mem_erase hi
    simp [hψ, this]
  have hR : ∀ w : Fin k → Fin L, ∏ i, ψ i (w i) =
      (if w p = 0 then ∏ i ∈ Finset.univ.erase p, g i (w i) else 0) := by
    intro w
    rw [← Finset.mul_prod_erase Finset.univ (fun i => ψ i (w i)) (Finset.mem_univ p)]
    have h2 : ∏ i ∈ Finset.univ.erase p, ψ i (w i) = ∏ i ∈ Finset.univ.erase p, g i (w i) := by
      refine Finset.prod_congr rfl (fun i hi => ?_)
      have : i ≠ p := Finset.ne_of_mem_erase hi
      simp [hψ, this]
    rw [h2]
    by_cases hw : w p = 0 <;> simp [hψ, hw]
  rw [← hL, h]
  exact Finset.sum_congr rfl (fun w _ => (hR w).symm)

/-! ### Anchoring (Lemma B.4 [uvp:lem:anchor]) -/

private lemma uvp_wordDiam_ge {L k : ℕ} [NeZero L] (y : Fin k → Fin L) (i j : Fin k) :
    cycDist (y i) (y j) ≤ wordDiam y :=
  Finset.le_sup (f := fun p : Fin k × Fin k => cycDist (y p.1) (y p.2)) (Finset.mem_univ (i, j))

/-- The diameter profile dominates the product of the anchored profiles at the reduced weight
`c / (k - 1)`. -/
private lemma uvp_profile_prod {L k : ℕ} [NeZero L] (hk : 2 ≤ k) (c a : ℝ) (hc : 0 < c)
    (ha : 0 < a) (p : Fin k) (y : Fin k → Fin L) :
    Real.exp (-(c * (wordDiam y : ℝ) / a)) ≤
      ∏ i ∈ Finset.univ.erase p, Real.exp (-(c / (k - 1) * (cycDist (y i) (y p) : ℝ) / a)) := by
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hcard : ((Finset.univ.erase p).card : ℝ) = (k : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ k := by omega
    push_cast [Nat.cast_sub this]
    ring
  have hsum : ∑ i ∈ Finset.univ.erase p, (cycDist (y i) (y p) : ℝ) ≤
      ((k : ℝ) - 1) * wordDiam y := by
    rw [← hcard]
    have := Finset.sum_le_card_nsmul (Finset.univ.erase p) (fun i => (cycDist (y i) (y p) : ℝ))
      (wordDiam y : ℝ) (fun i _ => by exact_mod_cast uvp_wordDiam_ge y i p)
    simpa [nsmul_eq_mul] using this
  have this : ∑ i ∈ Finset.univ.erase p, -(c / ((k : ℝ) - 1) * (cycDist (y i) (y p) : ℝ) / a) =
      -(c / ((k : ℝ) - 1) / a * ∑ i ∈ Finset.univ.erase p, (cycDist (y i) (y p) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [this]
  have hcoef : 0 ≤ c / ((k : ℝ) - 1) / a := by positivity
  have h2 : c / ((k : ℝ) - 1) / a * ∑ i ∈ Finset.univ.erase p, (cycDist (y i) (y p) : ℝ) ≤
      c * (wordDiam y : ℝ) / a := by
    calc _ ≤ c / ((k : ℝ) - 1) / a * (((k : ℝ) - 1) * wordDiam y) := by gcongr
      _ = c * (wordDiam y : ℝ) / a := by field_simp
  linarith

/-- The anchored weighted sum: one leg with bounded row, the others with the weighted
convolution bound. -/
private lemma uvp_anchor_sum {L k : ℕ} [NeZero L] (c' a : ℝ) (p : Fin k) (φ : Fin k → Fin L → ℝ)
    (hφ : ∀ i y, 0 ≤ φ i y) (Rp : ℝ) (K : Fin k → ℝ) (hp : ∑ u, φ p u ≤ Rp)
    (hK : ∀ i, i ≠ p → ∀ u : Fin L,
      ∑ w : Fin L, Real.exp (-(c' * (cycDist w 0 : ℝ) / a)) * φ i (w + u) ≤ K i) :
    ∑ y : Fin k → Fin L,
      (∏ i ∈ Finset.univ.erase p, Real.exp (-(c' * (cycDist (y i) (y p) : ℝ) / a))) *
        ∏ i, φ i (y i) ≤ Rp * ∏ i ∈ Finset.univ.erase p, K i := by
  have hK0 : ∀ i, i ≠ p → 0 ≤ K i := fun i hi =>
    le_trans (Finset.sum_nonneg (fun w _ => mul_nonneg (Real.exp_pos _).le (hφ _ _)))
      (hK i hi (0 : Fin L))
  rw [uvp_sum_anchor p]
  have key : ∀ u : Fin L, ∑ w : Fin k → Fin L, (if w p = 0 then
      (∏ i ∈ Finset.univ.erase p, Real.exp (-(c' * (cycDist ((w + (fun _ => u : Fin k → Fin L)) i)
        ((w + (fun _ => u : Fin k → Fin L)) p) : ℝ) / a))) *
          ∏ i, φ i ((w + (fun _ => u : Fin k → Fin L)) i) else 0)
      = φ p u * ∏ i ∈ Finset.univ.erase p,
          ∑ w : Fin L, Real.exp (-(c' * (cycDist w 0 : ℝ) / a)) * φ i (w + u) := by
    intro u
    rw [← uvp_sum_prod_anchor p
      (fun i w => Real.exp (-(c' * (cycDist w 0 : ℝ) / a)) * φ i (w + u)), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases hw : w p = 0
    · simp only [hw, ↓reduceIte]
      rw [← Finset.mul_prod_erase Finset.univ
        (fun i => φ i ((w + (fun _ => u : Fin k → Fin L)) i)) (Finset.mem_univ p),
        Finset.prod_mul_distrib]
      have e1 : ∏ i ∈ Finset.univ.erase p, Real.exp (-(c' * (cycDist
          ((w + (fun _ => u : Fin k → Fin L)) i) ((w + (fun _ => u : Fin k → Fin L)) p) : ℝ)
            / a)) =
          ∏ i ∈ Finset.univ.erase p, Real.exp (-(c' * (cycDist (w i) 0 : ℝ) / a)) := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        simp only [Pi.add_apply, hw]
        rw [← zero_add u, uvp_cycDist_add_right]
      have e2 : ∏ i ∈ Finset.univ.erase p, φ i ((w + (fun _ => u : Fin k → Fin L)) i) =
          ∏ i ∈ Finset.univ.erase p, φ i (w i + u) := rfl
      have e3 : φ p ((w + (fun _ => u : Fin k → Fin L)) p) = φ p u := by simp [hw]
      rw [e1, e2, e3]
      ring
    · simp [hw]
  rw [Finset.sum_congr rfl (fun u _ => key u)]
  calc _ ≤ (∑ u, φ p u) * ∏ i ∈ Finset.univ.erase p, K i := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun u _ => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (hφ _ _)
        exact Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg
          (fun w _ => mul_nonneg (Real.exp_pos _).le (hφ _ _)))
          (fun i hi => hK i (Finset.ne_of_mem_erase hi) u)
    _ ≤ Rp * ∏ i ∈ Finset.univ.erase p, K i := by
        gcongr
        exact Finset.prod_nonneg (fun i hi => hK0 i (Finset.ne_of_mem_erase hi))

private lemma uvp_prod_ite {k : ℕ} {β : Type*} [CommMonoid β] (v : Fin k) (a b : Fin k → β) :
    ∏ j, (if j = v then a j else b j) = a v * ∏ j ∈ Finset.univ.erase v, b j := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => if j = v then a j else b j) (Finset.mem_univ v)]
  simp only [↓reduceIte]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  simp [Finset.ne_of_mem_erase hj]

private lemma uvp_sum_sub_left {L : ℕ} [NeZero L] (g : Fin L → ℝ) (x : Fin L) :
    ∑ u : Fin L, g (x - u) = ∑ y : Fin L, g y :=
  Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ => rfl)

/-- Lemma B.4 [uvp:lem:anchor]: anchoring at a leg with bounded absolute row. -/
theorem uvp_anchor (k : ℕ) (hk : 2 ≤ k) (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (L : ℕ) [NeZero L] (a A : ℝ), 1 ≤ a → 1 ≤ A →
      ∀ (S : (Fin k → Fin L) → ℂ) (V : Fin k → Fin L → ℂ) (j₀ : Fin k),
      (∀ x, ‖S x‖ ≤ C * Real.exp (-(c * wordDiam x / a))) → ∑ x, ‖V j₀ x‖ ≤ C →
      (∀ j, j ≠ j₀ → ∀ x : Fin L,
        ∑ y : Fin L, Real.exp (-(c / (k - 1) * cycDist y 0 / a)) * ‖V j (x - y)‖ ≤ C * A) →
      (∀ x : Fin k → Fin L, ‖∑ y, S y * ∏ j, V j (x j - y j)‖ ≤ C' * A ^ (k - 1)) ∧
      ∀ v, v ≠ j₀ → ∀ x : Fin k → Fin L,
        ∑ xv : Fin L, ‖∑ y, S y * ∏ j, (if j = v then (if xv = y j then 1 else 0)
          else V j (x j - y j))‖ ≤ C' * a * A ^ (k - 2) := by
  refine ⟨C ^ (k + 1) + 2 * (1 + ((k : ℝ) - 1) / c) * C ^ k, ?_, ?_⟩
  · have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    positivity
  intro L _ a A ha hA S V j₀ hS hV0 hVc
  have ha0 : 0 < a := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hk1' : (0 : ℝ) ≤ (k : ℝ) - 1 := hk1.le
  have hcard1 : ((Finset.univ.erase j₀).card) = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin]
  -- the profile at the anchor
  have hprof : ∀ y, ‖S y‖ ≤ C * ∏ i ∈ Finset.univ.erase j₀,
      Real.exp (-(c / (k - 1) * (cycDist (y i) (y j₀) : ℝ) / a)) := fun y =>
    (hS y).trans (mul_le_mul_of_nonneg_left (uvp_profile_prod hk c a hc ha0 j₀ y) hC.le)
  have hc0 : 0 < c / ((k : ℝ) - 1) := div_pos hc hk1
  have hCA : 0 ≤ C * A := by positivity
  constructor
  · intro x
    have hbound : ∑ y : Fin k → Fin L, (∏ i ∈ Finset.univ.erase j₀,
        Real.exp (-(c / (k - 1) * (cycDist (y i) (y j₀) : ℝ) / a))) *
          ∏ i, ‖V i (x i - y i)‖ ≤ C * ∏ i ∈ Finset.univ.erase j₀, (C * A) := by
      refine uvp_anchor_sum (c / (k - 1)) a j₀ (fun i y => ‖V i (x i - y)‖)
        (fun _ _ => norm_nonneg _) C (fun _ => C * A) ?_ ?_
      · rw [uvp_sum_sub_left (fun y => ‖V j₀ y‖) (x j₀)]; exact hV0
      · intro i hi u
        have := hVc i hi (x i - u)
        simpa [sub_sub, add_comm] using this
    calc ‖∑ y, S y * ∏ j, V j (x j - y j)‖
        ≤ ∑ y, ‖S y * ∏ j, V j (x j - y j)‖ := norm_sum_le _ _
      _ ≤ ∑ y : Fin k → Fin L, C * ((∏ i ∈ Finset.univ.erase j₀,
          Real.exp (-(c / (k - 1) * (cycDist (y i) (y j₀) : ℝ) / a))) *
            ∏ i, ‖V i (x i - y i)‖) := by
          refine Finset.sum_le_sum (fun y _ => ?_)
          rw [norm_mul, norm_prod]
          calc ‖S y‖ * ∏ i, ‖V i (x i - y i)‖
              ≤ (C * ∏ i ∈ Finset.univ.erase j₀,
                Real.exp (-(c / (k - 1) * (cycDist (y i) (y j₀) : ℝ) / a))) *
                  ∏ i, ‖V i (x i - y i)‖ :=
                mul_le_mul_of_nonneg_right (hprof y) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
            _ = _ := by ring
      _ = C * ∑ y : Fin k → Fin L, (∏ i ∈ Finset.univ.erase j₀,
          Real.exp (-(c / (k - 1) * (cycDist (y i) (y j₀) : ℝ) / a))) *
            ∏ i, ‖V i (x i - y i)‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ C * (C * ∏ i ∈ Finset.univ.erase j₀, (C * A)) := by gcongr
      _ = C ^ (k + 1) * A ^ (k - 1) := by
          rw [Finset.prod_const, hcard1, mul_pow]
          have : k + 1 = (k - 1) + 2 := by omega
          rw [this, pow_add]
          ring
      _ ≤ _ := by
          gcongr
          have : 0 ≤ 2 * (1 + ((k : ℝ) - 1) / c) * C ^ k := by positivity
          linarith
  · intro v hv x
    set K : Fin k → ℝ := fun i => if i = v then 2 * (1 + a / (c / ((k : ℝ) - 1))) else C * A with hK
    have hbound : ∑ y : Fin k → Fin L, (∏ i ∈ Finset.univ.erase j₀,
        Real.exp (-(c / (k - 1) * (cycDist (y i) (y j₀) : ℝ) / a))) *
          ∏ i, (if i = v then (1 : ℝ) else ‖V i (x i - y i)‖) ≤
        C * ∏ i ∈ Finset.univ.erase j₀, K i := by
      refine uvp_anchor_sum (c / (k - 1)) a j₀ (fun i y => if i = v then 1 else ‖V i (x i - y)‖)
        (fun i y => by split_ifs; exacts [zero_le_one, norm_nonneg _]) C K ?_ ?_
      · simp only [Ne.symm hv, ↓reduceIte]
        rw [uvp_sum_sub_left (fun y => ‖V j₀ y‖) (x j₀)]; exact hV0
      · intro i hi u
        by_cases hiv : i = v
        · simp only [hK, hiv, ↓reduceIte, mul_one]
          exact uvp_geom_sum _ _ hc0 ha0
        · simp only [hK, hiv, ↓reduceIte]
          have := hVc i hi (x i - u)
          simpa [sub_sub, add_comm] using this
    have hKprod : ∏ i ∈ Finset.univ.erase j₀, K i =
        2 * (1 + a / (c / ((k : ℝ) - 1))) * (C * A) ^ (k - 2) := by
      have hvm : v ∈ Finset.univ.erase j₀ := Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩
      rw [← Finset.mul_prod_erase _ K hvm]
      simp only [hK, ↓reduceIte]
      congr 1
      rw [Finset.prod_congr rfl (g := fun _ => C * A)]
      · rw [Finset.prod_const, Finset.card_erase_of_mem hvm, hcard1]; rfl
      · intro i hi
        simp [Finset.ne_of_mem_erase hi]
    -- the sum over the output coordinate collapses the indicator
    have hind : ∀ y : Fin k → Fin L, ∑ xv : Fin L, ∏ j, ‖(if j = v then
        (if xv = y j then (1 : ℂ) else 0) else V j (x j - y j))‖ =
          ∏ i, (if i = v then (1 : ℝ) else ‖V i (x i - y i)‖) := by
      intro y
      have h1 : ∀ xv : Fin L, ∏ j, ‖(if j = v then (if xv = y j then (1 : ℂ) else 0)
          else V j (x j - y j))‖ = (if xv = y v then 1 else 0) *
            ∏ j ∈ Finset.univ.erase v, ‖V j (x j - y j)‖ := by
        intro xv
        have := uvp_prod_ite v (fun j => ‖(if xv = y j then (1 : ℂ) else 0)‖)
          (fun j => ‖V j (x j - y j)‖)
        have e : ‖(if xv = y v then (1 : ℂ) else 0)‖ = if xv = y v then (1 : ℝ) else 0 := by
          split_ifs <;> simp
        rw [e] at this
        rw [← this]
        refine Finset.prod_congr rfl (fun j _ => ?_)
        by_cases hj : j = v <;> simp [hj]
      simp only [h1]
      rw [← Finset.sum_mul, uvp_prod_ite v (fun _ => (1 : ℝ)) (fun j => ‖V j (x j - y j)‖)]
      simp
    calc ∑ xv : Fin L, ‖∑ y, S y * ∏ j, (if j = v then (if xv = y j then (1 : ℂ) else 0)
          else V j (x j - y j))‖
        ≤ ∑ xv : Fin L, ∑ y : Fin k → Fin L, ‖S y‖ * ∏ j, ‖(if j = v then
            (if xv = y j then (1 : ℂ) else 0) else V j (x j - y j))‖ := by
          refine Finset.sum_le_sum (fun xv _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun y _ => ?_))
          rw [norm_mul, norm_prod]
      _ = ∑ y : Fin k → Fin L, ‖S y‖ * ∏ i, (if i = v then (1 : ℝ) else ‖V i (x i - y i)‖) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [← Finset.mul_sum, hind]
      _ ≤ ∑ y : Fin k → Fin L, C * ((∏ i ∈ Finset.univ.erase j₀,
          Real.exp (-(c / (k - 1) * (cycDist (y i) (y j₀) : ℝ) / a))) *
            ∏ i, (if i = v then (1 : ℝ) else ‖V i (x i - y i)‖)) := by
          refine Finset.sum_le_sum (fun y _ => ?_)
          calc ‖S y‖ * ∏ i, (if i = v then (1 : ℝ) else ‖V i (x i - y i)‖)
              ≤ (C * ∏ i ∈ Finset.univ.erase j₀,
                Real.exp (-(c / (k - 1) * (cycDist (y i) (y j₀) : ℝ) / a))) *
                  ∏ i, (if i = v then (1 : ℝ) else ‖V i (x i - y i)‖) :=
                mul_le_mul_of_nonneg_right (hprof y) (Finset.prod_nonneg
                  (fun i _ => by split_ifs <;> simp))
            _ = _ := by ring
      _ = C * ∑ y : Fin k → Fin L, (∏ i ∈ Finset.univ.erase j₀,
          Real.exp (-(c / (k - 1) * (cycDist (y i) (y j₀) : ℝ) / a))) *
            ∏ i, (if i = v then (1 : ℝ) else ‖V i (x i - y i)‖) := (Finset.mul_sum _ _ _).symm
      _ ≤ C * (C * ∏ i ∈ Finset.univ.erase j₀, K i) := by gcongr
      _ = C ^ k * (2 * (1 + a / (c / ((k : ℝ) - 1)))) * A ^ (k - 2) := by
          rw [hKprod, mul_pow]
          have hCk : C ^ k = C ^ 2 * C ^ (k - 2) := by rw [← pow_add]; congr 1; omega
          rw [hCk]; ring
      _ ≤ _ := by
          have h1 : 2 * (1 + a / (c / ((k : ℝ) - 1))) ≤ 2 * (1 + ((k : ℝ) - 1) / c) * a := by
            rw [div_div_eq_mul_div]
            have : a * ((k : ℝ) - 1) / c = a * (((k : ℝ) - 1) / c) := by ring
            rw [this]
            nlinarith [div_nonneg hk1' hc.le]
          have h2 : 0 ≤ A ^ (k - 2) := by positivity
          calc C ^ k * (2 * (1 + a / (c / ((k : ℝ) - 1)))) * A ^ (k - 2)
              ≤ C ^ k * (2 * (1 + ((k : ℝ) - 1) / c) * a) * A ^ (k - 2) := by gcongr
            _ = (2 * (1 + ((k : ℝ) - 1) / c) * C ^ k) * a * A ^ (k - 2) := by ring
            _ ≤ (C ^ (k + 1) + 2 * (1 + ((k : ℝ) - 1) / c) * C ^ k) * a * A ^ (k - 2) := by
                have : 0 ≤ C ^ (k + 1) := by positivity
                gcongr
                linarith

/-! ### The discrete symmetric Taylor bound (Lemma B.5 [uvp:lem:taylor]) -/

/-- The mixed difference of `H` at `w` along the steps `z` and `z'`. -/
private def uvpQ {G B : Type*} [AddCommGroup G] [AddCommGroup B] (H : G → B) (w z z' : G) : B :=
  H (w + z + z') - H (w + z) - H (w + z') + H w

private lemma uvpQ_comm {G B : Type*} [AddCommGroup G] [AddCommGroup B] (H : G → B)
    (w z z' : G) : uvpQ H w z z' = uvpQ H w z' z := by
  unfold uvpQ
  rw [add_right_comm w z z']
  abel

private lemma uvpQ_add_left {G B : Type*} [AddCommGroup G] [AddCommGroup B] (H : G → B)
    (w z z'' z' : G) :
    uvpQ H w (z + z'') z' = uvpQ H w z z' + uvpQ H (w + z) z'' z' := by
  unfold uvpQ
  simp only [← add_assoc]
  abel

private lemma uvpQ_add_right {G B : Type*} [AddCommGroup G] [AddCommGroup B] (H : G → B)
    (w z z' z'' : G) :
    uvpQ H w z (z' + z'') = uvpQ H w z z' + uvpQ H (w + z') z z'' := by
  rw [uvpQ_comm, uvpQ_add_left, uvpQ_comm H w z' z, uvpQ_comm H (w + z') z'' z]

private lemma uvpQ_zero_left {G B : Type*} [AddCommGroup G] [AddCommGroup B] (H : G → B)
    (w z' : G) : uvpQ H w 0 z' = 0 := by
  simp [uvpQ]

private lemma uvpQ_zero_right {G B : Type*} [AddCommGroup G] [AddCommGroup B] (H : G → B)
    (w z : G) : uvpQ H w z 0 = 0 := by
  rw [uvpQ_comm, uvpQ_zero_left]

private lemma uvp_seminorm_sum_le {ι B 𝕜 : Type*} [NormedField 𝕜] [AddCommGroup B] [Module 𝕜 B]
    (ν : Seminorm 𝕜 B) (s : Finset ι) (f : ι → B) : ν (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ν (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (map_add_le_add ν _ _).trans (by linarith)

/-- Mixed differences along arbitrary steps are bounded by the product of the step lengths
times the bound on mixed differences along unit steps. -/
private lemma uvpQ_bound {G B 𝕜 : Type*} [AddCommGroup G] [AddCommGroup B] [NormedField 𝕜]
    [Module 𝕜 B] (ν : Seminorm 𝕜 B) (H : G → B) (N : G → ℕ) (U : Set G) (Mb : ℝ)
    (hzero : ∀ z, N z = 0 → z = 0)
    (hpeel : ∀ (n : ℕ) (z : G), N z = n + 1 → ∃ u ∈ U, N (z - u) = n)
    (hU : ∀ u ∈ U, ∀ u' ∈ U, ∀ w, ν (uvpQ H w u u') ≤ Mb) :
    ∀ (z z' w : G), ν (uvpQ H w z z') ≤ (N z : ℝ) * N z' * Mb := by
  have step1 : ∀ (n : ℕ) (z' : G), N z' = n → ∀ u ∈ U, ∀ w, ν (uvpQ H w u z') ≤ n * Mb := by
    intro n
    induction n with
    | zero =>
      intro z' hz' u _ w
      rw [hzero z' hz', uvpQ_zero_right, map_zero]
      simp
    | succ n ih =>
      intro z' hz' u hu w
      obtain ⟨u', hu', hN'⟩ := hpeel n z' hz'
      have hz : z' = u' + (z' - u') := by abel
      rw [hz, uvpQ_add_right]
      calc _ ≤ ν (uvpQ H w u u') + ν (uvpQ H (w + u') u (z' - u')) := map_add_le_add _ _ _
        _ ≤ Mb + n * Mb := add_le_add (hU u hu u' hu' w) (ih _ hN' u hu _)
        _ = ((n + 1 : ℕ) : ℝ) * Mb := by push_cast; ring
  have step2 : ∀ (n : ℕ) (z : G), N z = n → ∀ z' w, ν (uvpQ H w z z') ≤ n * N z' * Mb := by
    intro n
    induction n with
    | zero =>
      intro z hz z' w
      rw [hzero z hz, uvpQ_zero_left, map_zero]
      simp
    | succ n ih =>
      intro z hz z' w
      obtain ⟨u, hu, hN'⟩ := hpeel n z hz
      have hz2 : z = u + (z - u) := by abel
      rw [hz2, uvpQ_add_left]
      have h1 : ν (uvpQ H w u z') ≤ N z' * Mb := step1 _ z' rfl u hu w
      calc _ ≤ ν (uvpQ H w u z') + ν (uvpQ H (w + u) (z - u) z') := map_add_le_add _ _ _
        _ ≤ N z' * Mb + n * N z' * Mb := add_le_add h1 (ih _ hN' z' _)
        _ = ((n + 1 : ℕ) : ℝ) * N z' * Mb := by push_cast; ring
  intro z z' w
  exact step2 (N z) z rfl z' w

/-- The symmetrization step of the Taylor bound. -/
private lemma uvpTaylor_sum {G B 𝕜 : Type*} [AddCommGroup G] [AddCommGroup B] [RCLike 𝕜]
    [Module 𝕜 B] (ν : Seminorm 𝕜 B) (H : G → B) (N : G → ℕ) (Mb : ℝ)
    (hQ : ∀ z, ν (H z + H (-z) - (2 : 𝕜) • H 0) ≤ (N z : ℝ) ^ 2 * Mb)
    (Z : Finset G) (hZ : ∀ z ∈ Z, -z ∈ Z) (S : G → 𝕜) (hS : ∀ z, S (-z) = S z) :
    ν (∑ z ∈ Z, S z • H z) ≤
      ‖∑ z ∈ Z, S z‖ * ν (H 0) + (1 / 2) * ∑ z ∈ Z, ‖S z‖ * ((N z : ℝ) ^ 2 * Mb) := by
  classical
  set T : B := ∑ z ∈ Z, S z • H z with hT
  have ha : ∑ z ∈ Z, S z • H (-z) = T := by
    refine Finset.sum_nbij' (fun z => -z) (fun z => -z) (fun z hz => hZ z hz) (fun z hz => hZ z hz)
      (fun z _ => neg_neg z) (fun z _ => neg_neg z) (fun z _ => ?_)
    rw [hS]
  have hsplit : (2 : 𝕜) • T = ∑ z ∈ Z, S z • (H z + H (-z) - (2 : 𝕜) • H 0) +
      (2 * ∑ z ∈ Z, S z) • H 0 := by
    calc (2 : 𝕜) • T = T + T := two_smul 𝕜 T
      _ = ∑ z ∈ Z, S z • (H z + H (-z)) := by
          nth_rewrite 2 [← ha]
          rw [hT, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun z _ => (smul_add _ _ _).symm)
      _ = _ := by
          rw [Finset.mul_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun z _ => ?_)
          module
  have hnorm2 : ν ((2 : 𝕜) • T) = 2 * ν T := by
    rw [map_smul_eq_mul]; simp
  have h1 : ν (∑ z ∈ Z, S z • (H z + H (-z) - (2 : 𝕜) • H 0)) ≤
      ∑ z ∈ Z, ‖S z‖ * ((N z : ℝ) ^ 2 * Mb) := by
    refine (uvp_seminorm_sum_le ν _ _).trans (Finset.sum_le_sum (fun z _ => ?_))
    rw [map_smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hQ z) (norm_nonneg _)
  have h2 : ν ((2 * ∑ z ∈ Z, S z) • H 0) = 2 * ‖∑ z ∈ Z, S z‖ * ν (H 0) := by
    rw [map_smul_eq_mul, norm_mul]; simp
  have h3 : 2 * ν T ≤ ∑ z ∈ Z, ‖S z‖ * ((N z : ℝ) ^ 2 * Mb) +
      2 * ‖∑ z ∈ Z, S z‖ * ν (H 0) := by
    rw [← hnorm2, hsplit]
    refine (map_add_le_add _ _ _).trans ?_
    rw [h2]
    linarith
  linarith

/-- Peeling a unit step off a vector with a coordinatewise length. -/
private lemma uvp_pi_peel {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    (d : M → ℕ) (Us : Set M) (hd0 : ∀ x, d x = 0 → x = 0) (hd00 : d 0 = 0)
    (hdp : ∀ x, x ≠ 0 → ∃ s ∈ Us, d (x - s) + 1 = d x) :
    (∀ w : ι → M, ∑ i, d (w i) = 0 → w = 0) ∧
    (∀ (n : ℕ) (w : ι → M), ∑ i, d (w i) = n + 1 →
      ∃ i, ∃ s ∈ Us, ∑ j, d ((w - (Pi.single i s : ι → M)) j) = n) := by
  constructor
  · intro w hw
    funext i
    have := (Finset.sum_eq_zero_iff.mp hw) i (Finset.mem_univ i)
    exact hd0 _ this
  · intro n w hn
    have : ∃ i, w i ≠ 0 := by
      by_contra h
      have h' : ∀ i, w i = 0 := fun i => by
        by_contra hi
        exact h ⟨i, hi⟩
      simp [h', hd00] at hn
    obtain ⟨i, hi⟩ := this
    obtain ⟨s, hs, hds⟩ := hdp (w i) hi
    refine ⟨i, s, hs, ?_⟩
    have h1 : ∑ j, d ((w - (Pi.single i s : ι → M)) j) =
        d (w i - s) + ∑ j ∈ Finset.univ.erase i, d (w j) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      congr 1
      · simp
      · refine Finset.sum_congr rfl (fun j hj => ?_)
        simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
    have h2 : ∑ j, d (w j) = d (w i) + ∑ j ∈ Finset.univ.erase i, d (w j) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    omega

/-! ### Expansion of the dressing -/

private lemma uvp_finRotate {L : ℕ} [NeZero L] (x : Fin L) : finRotate L x = x + 1 := by
  simp

/-- The part of the leg `j` that carries an anchor: the identity plus `E` or the stable kernel,
and zero on the undressed leg. -/
private def uvpR {L : ℕ} [NeZero L] (Er : Fin L → ℂ) {k : ℕ} (mixed : Fin k → Bool)
    (Vst : Fin k → Fin L → ℂ) (undress : Option (Fin k)) (j : Fin k) : Fin L → ℂ :=
  if undress = some j then 0
  else if mixed j then fun x => (if x = 0 then 1 else 0) + Er x else Vst j

/-- The part of the leg `j` without an anchor: `Ξ` on a mixed leg, the identity on the undressed
leg and zero on a stable leg. -/
private def uvpX {L : ℕ} [NeZero L] (Ξ : Fin L → ℂ) {k : ℕ} (mixed : Fin k → Bool)
    (undress : Option (Fin k)) (j : Fin k) : Fin L → ℂ :=
  if undress = some j then fun x => if x = 0 then 1 else 0
  else if mixed j then Ξ else 0

private lemma uvp_leg_split {L : ℕ} [NeZero L] (Ξ Er : Fin L → ℂ) {k : ℕ} (mixed : Fin k → Bool)
    (Vst : Fin k → Fin L → ℂ) (undress : Option (Fin k)) (j : Fin k) (a b : Fin L) :
    (if undress = some j then (if a = b then (1 : ℂ) else 0)
      else uvpLeg Ξ Er mixed Vst j (a - b)) =
    uvpR Er mixed Vst undress j (a - b) + uvpX Ξ mixed undress j (a - b) := by
  unfold uvpR uvpX uvpLeg
  by_cases h1 : undress = some j
  · simp [h1, sub_eq_zero]
  · by_cases h2 : mixed j = true
    · simp [h1, h2]; ring
    · simp [h1, h2]

/-- The leg kernel selected by the subset `T`: the anchored part on `T`, the other part
outside. -/
private def uvpV {L : ℕ} [NeZero L] (Ξ Er : Fin L → ℂ) {k : ℕ} (mixed : Fin k → Bool)
    (Vst : Fin k → Fin L → ℂ) (undress : Option (Fin k)) (T : Finset (Fin k)) (j : Fin k) :
    Fin L → ℂ :=
  if j ∈ T then uvpR Er mixed Vst undress j else uvpX Ξ mixed undress j

private lemma uvp_dress_expand {L : ℕ} [NeZero L] (Ξ Er : Fin L → ℂ) {k : ℕ}
    (mixed : Fin k → Bool) (Vst : Fin k → Fin L → ℂ) (S : (Fin k → Fin L) → ℂ)
    (undress : Option (Fin k)) (x : Fin k → Fin L) :
    uvpDress Ξ Er mixed Vst S undress x = ∑ T : Finset (Fin k), ∑ y : Fin k → Fin L,
      S y * ∏ j, uvpV Ξ Er mixed Vst undress T j (x j - y j) := by
  unfold uvpDress
  have h1 : ∀ y : Fin k → Fin L, ∏ j, (if undress = some j then (if x j = y j then (1 : ℂ) else 0)
      else uvpLeg Ξ Er mixed Vst j (x j - y j)) =
      ∑ T : Finset (Fin k), ∏ j, uvpV Ξ Er mixed Vst undress T j (x j - y j) := by
    intro y
    simp_rw [uvp_leg_split]
    rw [Fintype.prod_add]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [← Finset.prod_mul_prod_compl T (fun j => uvpV Ξ Er mixed Vst undress T j (x j - y j))]
    congr 1
    · refine Finset.prod_congr rfl (fun j hj => ?_)
      simp [uvpV, hj]
    · refine Finset.prod_congr rfl (fun j hj => ?_)
      have : j ∉ T := Finset.mem_compl.mp hj
      simp [uvpV, this]
  simp_rw [h1, Finset.mul_sum]
  exact Finset.sum_comm

/-! ### The kernel contract -/

private lemma uvp_kernels_unpack {L : ℕ} [NeZero L] {a δ c C ε : ℝ} {Ξ Er : Fin L → ℂ} {k : ℕ}
    {mixed : Fin k → Bool} {Vst : Fin k → Fin L → ℂ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (h : UvpKernels L a δ c C ε Ξ Er mixed Vst) :
    (∀ j, mixed j = false → ∑ x, ‖Vst j x‖ ≤ C) ∧
    ∑ x, ‖Ξ x‖ ≤ C / δ ∧ (∀ x, ‖Ξ x‖ ≤ C / (δ * min (L : ℝ) (a / Real.sqrt δ))) ∧
    ∑ x, ‖Ξ (x + 1) - Ξ x‖ ≤ C * (Real.sqrt δ / a) / δ ∧
    (∀ x, ‖Ξ (x + 1) - Ξ x‖ ≤ C * (Real.sqrt δ / a) / (δ * min (L : ℝ) (a / Real.sqrt δ))) ∧
    ∑ x, ‖Ξ (x + 1 + 1) - 2 * Ξ (x + 1) + Ξ x‖ ≤ C * (Real.sqrt δ / a) ^ 2 / δ ∧
    ∑ x, ‖Er x‖ ≤ C * ε / δ ^ 2 ∧ ε ≤ δ ^ 2 := by
  obtain ⟨-, -, hst, h1, h2, h3, h4, h5, h6, -, h7⟩ := h
  refine ⟨?_, h1, h2, ?_, ?_, ?_, h6, h7⟩
  · intro j hj
    refine le_trans (Finset.sum_le_sum (fun x _ => ?_)) (hst j hj).2
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))
  · simpa only [uvp_finRotate] using h3
  · simpa only [uvp_finRotate] using h4
  · simpa only [uvp_finRotate] using h5

/-! ### Bounds on the legs -/

private lemma uvp_ell_pos {L : ℕ} [NeZero L] {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    0 < min (L : ℝ) (a / Real.sqrt δ) := by
  have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact lt_min this (div_pos ha (Real.sqrt_pos.mpr hδ))

private lemma uvp_A_ge_one {L : ℕ} [NeZero L] {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ a / (δ * min (L : ℝ) (a / Real.sqrt δ)) := by
  have hℓ := uvp_ell_pos (L := L) ha hδ
  rw [le_div_iff₀ (by positivity), one_mul]
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hs1 : Real.sqrt δ ≤ 1 := by
    rw [Real.sqrt_le_one]; exact hδ1
  calc δ * min (L : ℝ) (a / Real.sqrt δ) ≤ δ * (a / Real.sqrt δ) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hδ.le
    _ = Real.sqrt δ * a := by
        have : δ = Real.sqrt δ * Real.sqrt δ := (Real.mul_self_sqrt hδ.le).symm
        field_simp
        nlinarith [Real.mul_self_sqrt hδ.le]
    _ ≤ a := by nlinarith

private lemma uvp_conv_le_row {L : ℕ} [NeZero L] (c' a : ℝ) (hc' : 0 ≤ c') (ha : 0 < a)
    (W : Fin L → ℂ) (x : Fin L) :
    ∑ y : Fin L, Real.exp (-(c' * (cycDist y 0 : ℝ) / a)) * ‖W (x - y)‖ ≤ ∑ y, ‖W y‖ := by
  calc ∑ y : Fin L, Real.exp (-(c' * (cycDist y 0 : ℝ) / a)) * ‖W (x - y)‖
      ≤ ∑ y : Fin L, ‖W (x - y)‖ := by
        refine Finset.sum_le_sum (fun y _ => ?_)
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        rw [Real.exp_le_one_iff]
        have : 0 ≤ c' * (cycDist y 0 : ℝ) / a := by positivity
        linarith
    _ = ∑ y, ‖W y‖ := uvp_sum_sub_left (fun y => ‖W y‖) x

private lemma uvp_conv_le_sup {L : ℕ} [NeZero L] (c' a M : ℝ) (hc' : 0 < c') (ha : 0 < a)
    (W : Fin L → ℂ) (hW : ∀ y, ‖W y‖ ≤ M) (x : Fin L) :
    ∑ y : Fin L, Real.exp (-(c' * (cycDist y 0 : ℝ) / a)) * ‖W (x - y)‖ ≤
      M * (2 * (1 + a / c')) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hW 0)
  calc ∑ y : Fin L, Real.exp (-(c' * (cycDist y 0 : ℝ) / a)) * ‖W (x - y)‖
      ≤ ∑ y : Fin L, Real.exp (-(c' * (cycDist y 0 : ℝ) / a)) * M :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hW _) (Real.exp_pos _).le)
    _ = M * ∑ y : Fin L, Real.exp (-(c' * (cycDist y 0 : ℝ) / a)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun y _ => by ring)
    _ ≤ M * (2 * (1 + a / c')) := mul_le_mul_of_nonneg_left (uvp_geom_sum c' a hc' ha) hM

private lemma uvp_indicator_sum {L : ℕ} [NeZero L] :
    ∑ y : Fin L, ‖(if y = 0 then (1 : ℂ) else 0)‖ = 1 := by
  have h : ∀ y : Fin L, ‖(if y = 0 then (1 : ℂ) else 0)‖ = if y = 0 then (1 : ℝ) else 0 :=
    fun y => by split_ifs <;> simp
  simp only [h]
  rw [Finset.sum_ite_eq']
  simp

/-- The bounds on the anchored and unanchored parts of the legs, with
`Ct = 1 + C + 2(1 + (k-1)/c) C`. -/
private lemma uvp_legs {L : ℕ} [NeZero L] {k : ℕ} (hk : 2 ≤ k) {a δ c C ε : ℝ} (hc : 0 < c)
    (hC : 0 < C) (ha : 1 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {Ξ Er : Fin L → ℂ}
    {mixed : Fin k → Bool} {Vst : Fin k → Fin L → ℂ}
    (hK : UvpKernels L a δ c C ε Ξ Er mixed Vst) (undress : Option (Fin k)) (T : Finset (Fin k))
    (j : Fin k) :
    (j ∈ T → ∑ y, ‖uvpV Ξ Er mixed Vst undress T j y‖ ≤ 1 + C + 2 * (1 + ((k : ℝ) - 1) / c) * C) ∧
    (∀ x : Fin L, ∑ y : Fin L, Real.exp (-(c / (k - 1) * (cycDist y 0 : ℝ) / a)) *
      ‖uvpV Ξ Er mixed Vst undress T j (x - y)‖ ≤
        (1 + C + 2 * (1 + ((k : ℝ) - 1) / c) * C) * (a / (δ * min (L : ℝ) (a / Real.sqrt δ)))) := by
  have ha0 : 0 < a := by linarith
  obtain ⟨hst, hΞ0, hΞs, -, -, -, hE1, hε⟩ := uvp_kernels_unpack hc.le ha0.le hK
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hkc : 0 ≤ ((k : ℝ) - 1) / c := div_nonneg hk1.le hc.le
  have hc0 : 0 < c / ((k : ℝ) - 1) := div_pos hc hk1
  have hℓ := uvp_ell_pos (L := L) ha0 hδ
  have hA := uvp_A_ge_one (L := L) ha0 hδ hδ1
  set A := a / (δ * min (L : ℝ) (a / Real.sqrt δ)) with hAdef
  set Ct := 1 + C + 2 * (1 + ((k : ℝ) - 1) / c) * C with hCt
  have hCt1 : 1 + C ≤ Ct := by
    have : 0 ≤ 2 * (1 + ((k : ℝ) - 1) / c) * C := by positivity
    linarith
  have hCt0 : 0 ≤ Ct := by linarith
  have hE : ∑ y, ‖Er y‖ ≤ C := by
    refine hE1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- row bound for the anchored part
  have hrowR : ∑ y, ‖uvpR Er mixed Vst undress j y‖ ≤ 1 + C := by
    unfold uvpR
    by_cases h1 : undress = some j
    · simp [h1]; linarith
    · by_cases h2 : mixed j = true
      · simp only [h1, h2, ↓reduceIte]
        calc ∑ y, ‖(if y = 0 then (1 : ℂ) else 0) + Er y‖
            ≤ ∑ y, (‖(if y = 0 then (1 : ℂ) else 0)‖ + ‖Er y‖) :=
              Finset.sum_le_sum (fun y _ => norm_add_le _ _)
          _ = 1 + ∑ y, ‖Er y‖ := by rw [Finset.sum_add_distrib, uvp_indicator_sum]
          _ ≤ 1 + C := by linarith
      · have h2' : mixed j = false := by simpa using h2
        simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]
        linarith [hst j h2']
  constructor
  · intro hj
    unfold uvpV
    simp only [hj, ↓reduceIte]
    linarith
  · intro x
    unfold uvpV
    by_cases hj : j ∈ T
    · simp only [hj, ↓reduceIte]
      calc _ ≤ ∑ y, ‖uvpR Er mixed Vst undress j y‖ := uvp_conv_le_row _ _ hc0.le ha0 _ x
        _ ≤ 1 + C := hrowR
        _ ≤ Ct := hCt1
        _ ≤ Ct * A := le_mul_of_one_le_right hCt0 hA
    · simp only [hj, ↓reduceIte]
      unfold uvpX
      by_cases h1 : undress = some j
      · simp only [h1, ↓reduceIte]
        calc _ ≤ ∑ y, ‖(if y = 0 then (1 : ℂ) else 0)‖ := uvp_conv_le_row _ _ hc0.le ha0 _ x
          _ = 1 := uvp_indicator_sum
          _ ≤ Ct := by linarith
          _ ≤ Ct * A := le_mul_of_one_le_right hCt0 hA
      · by_cases h2 : mixed j = true
        · simp only [h1, h2, ↓reduceIte]
          calc _ ≤ C / (δ * min (L : ℝ) (a / Real.sqrt δ)) * (2 * (1 + a / (c / ((k : ℝ) - 1)))) :=
                uvp_conv_le_sup _ _ _ hc0 ha0 Ξ hΞs x
            _ ≤ C / (δ * min (L : ℝ) (a / Real.sqrt δ)) * (2 * a * (1 + ((k : ℝ) - 1) / c)) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                rw [div_div_eq_mul_div]
                have : a * ((k : ℝ) - 1) / c = a * (((k : ℝ) - 1) / c) := by ring
                rw [this]
                nlinarith [mul_nonneg ha0.le hkc]
            _ = 2 * (1 + ((k : ℝ) - 1) / c) * C * A := by
                rw [hAdef]; field_simp
            _ ≤ Ct * A := by
                refine mul_le_mul_of_nonneg_right ?_ (by linarith)
                linarith
        · have h2' : mixed j = false := by simpa using h2
          simp only [h1, h2', ↓reduceIte, Bool.false_eq_true]
          simp only [Pi.zero_apply, norm_zero, mul_zero, Finset.sum_const_zero]
          exact mul_nonneg hCt0 (by linarith)

/-! ### The all-`Ξ` term: mixed differences of the translated products -/

/-- The product of `Ξ` over the legs in `Act`, translated by `w`, as a function of the anchor
coordinate `u`. -/
private def uvpH {L k : ℕ} [NeZero L] (Ξ : Fin L → ℂ) (Act : Finset (Fin k))
    (x w : Fin k → Fin L) : Fin L → ℂ :=
  fun u => ∏ j ∈ Act, Ξ (x j - u - w j)

/-- The `ℓ¹` seminorm in the anchor coordinate. -/
private def uvpL1 (L : ℕ) : Seminorm ℂ (Fin L → ℂ) where
  toFun h := ∑ u, ‖h u‖
  map_zero' := by simp
  add_le' := by
    intro a b
    calc ∑ u, ‖(a + b) u‖ ≤ ∑ u, (‖a u‖ + ‖b u‖) :=
          Finset.sum_le_sum (fun u _ => norm_add_le _ _)
      _ = _ := Finset.sum_add_distrib
  neg' := by intro a; simp
  smul' := by
    intro c a
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, ← Finset.mul_sum]

/-- The absolute value of the sum over the anchor coordinate. -/
private def uvpSumNorm (L : ℕ) : Seminorm ℂ (Fin L → ℂ) where
  toFun h := ‖∑ u, h u‖
  map_zero' := by simp
  add_le' := by
    intro a b
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    exact norm_add_le _ _
  neg' := by intro a; simp
  smul' := by
    intro c a
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, norm_mul]

private lemma uvpL1_apply {L : ℕ} (h : Fin L → ℂ) : uvpL1 L h = ∑ u, ‖h u‖ := rfl

private lemma uvpSumNorm_apply {L : ℕ} (h : Fin L → ℂ) : uvpSumNorm L h = ‖∑ u, h u‖ := rfl

private lemma uvpSumNorm_le_L1 {L : ℕ} (h : Fin L → ℂ) : uvpSumNorm L h ≤ uvpL1 L h := by
  rw [uvpL1_apply, uvpSumNorm_apply]
  exact norm_sum_le _ _

private lemma uvpH_add_single_notin {L k : ℕ} [NeZero L] (Ξ : Fin L → ℂ) (Act : Finset (Fin k))
    (x w : Fin k → Fin L) (j : Fin k) (hj : j ∉ Act) (s : Fin L) :
    uvpH Ξ Act x (w + Pi.single j s) = uvpH Ξ Act x w := by
  funext u
  unfold uvpH
  refine Finset.prod_congr rfl (fun l hl => ?_)
  have : l ≠ j := fun h => hj (h ▸ hl)
  simp [Pi.single_eq_of_ne this]

private lemma uvpH_single_apply {L k : ℕ} [NeZero L] (Ξ : Fin L → ℂ) (Act : Finset (Fin k))
    (x w : Fin k → Fin L) (i : Fin k) (hi : i ∈ Act) (s u : Fin L) :
    uvpH Ξ Act x (w + Pi.single i s) u =
      Ξ (x i - u - w i - s) * ∏ l ∈ Act.erase i, Ξ (x l - u - w l) := by
  unfold uvpH
  rw [← Finset.mul_prod_erase Act _ hi]
  congr 1
  · simp only [Pi.add_apply, Pi.single_eq_same]
    congr 1; abel
  · refine Finset.prod_congr rfl (fun l hl => ?_)
    simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hl)]

private lemma uvpH_two_apply {L k : ℕ} [NeZero L] (Ξ : Fin L → ℂ) (Act : Finset (Fin k))
    (x w : Fin k → Fin L) (i j : Fin k) (hij : i ≠ j) (hi : i ∈ Act) (hj : j ∈ Act)
    (s s' u : Fin L) :
    uvpH Ξ Act x (w + Pi.single i s + Pi.single j s') u =
      Ξ (x i - u - w i - s) * Ξ (x j - u - w j - s') *
        ∏ l ∈ (Act.erase i).erase j, Ξ (x l - u - w l) := by
  unfold uvpH
  have hj' : j ∈ Act.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  rw [← Finset.mul_prod_erase Act _ hi, ← Finset.mul_prod_erase (Act.erase i) _ hj', ← mul_assoc]
  congr 1
  · congr 1
    · simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero]
      congr 1; abel
    · simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij.symm]
      congr 1; abel
  · refine Finset.prod_congr rfl (fun l hl => ?_)
    have h1 : l ≠ j := Finset.ne_of_mem_erase hl
    have h2 : l ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
    simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]

private lemma uvp_prod_norm_le {L : ℕ} [NeZero L] {k : ℕ} (Ξ : Fin L → ℂ) (T : Finset (Fin k))
    (M : ℝ) (hΞ : ∀ y, ‖Ξ y‖ ≤ M) (c : Fin k → Fin L) (u : Fin L) :
    ∏ l ∈ T, ‖Ξ (c l - u)‖ ≤ M ^ T.card := by
  calc ∏ l ∈ T, ‖Ξ (c l - u)‖ ≤ ∏ _l ∈ T, M :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun l _ => hΞ _)
    _ = M ^ T.card := Finset.prod_const M

/-- Young's inequality for one kernel in `ℓ¹` and the others in `ℓ^∞`. -/
private lemma uvp_young {L : ℕ} [NeZero L] {k : ℕ} (Ξ g : Fin L → ℂ) (T : Finset (Fin k))
    (M R : ℝ) (hΞ : ∀ y, ‖Ξ y‖ ≤ M) (hg : ∑ y, ‖g y‖ ≤ R) (c : Fin k → Fin L) (i : Fin k) :
    ∑ u : Fin L, ‖g (c i - u)‖ * ∏ l ∈ T, ‖Ξ (c l - u)‖ ≤ R * M ^ T.card := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hΞ 0)
  calc ∑ u : Fin L, ‖g (c i - u)‖ * ∏ l ∈ T, ‖Ξ (c l - u)‖
      ≤ ∑ u : Fin L, ‖g (c i - u)‖ * M ^ T.card :=
        Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left
          (uvp_prod_norm_le Ξ T M hΞ c u) (norm_nonneg _))
    _ = (∑ u : Fin L, ‖g (c i - u)‖) * M ^ T.card := (Finset.sum_mul _ _ _).symm
    _ = (∑ y, ‖g y‖) * M ^ T.card := by rw [uvp_sum_sub_left (fun y => ‖g y‖) (c i)]
    _ ≤ R * M ^ T.card := mul_le_mul_of_nonneg_right hg (pow_nonneg hM _)

private lemma uvp_diff1_sum {L : ℕ} [NeZero L] (Ξ : Fin L → ℂ) (R1 M1 : ℝ)
    (hD1 : ∑ y, ‖Ξ (y + 1) - Ξ y‖ ≤ R1) (hD1s : ∀ y, ‖Ξ (y + 1) - Ξ y‖ ≤ M1)
    (s : Fin L) (hs : s = 1 ∨ s = -1) :
    (∑ y, ‖Ξ (y - s) - Ξ y‖ ≤ R1) ∧ (∀ y, ‖Ξ (y - s) - Ξ y‖ ≤ M1) := by
  rcases hs with rfl | rfl
  · have e : ∀ y : Fin L, ‖Ξ (y - 1) - Ξ y‖ = ‖Ξ (y - 1 + 1) - Ξ (y - 1)‖ := by
      intro y
      rw [sub_add_cancel, ← norm_neg]; congr 1; abel
    constructor
    · simp only [e]
      rw [Fintype.sum_equiv (Equiv.subRight (1 : Fin L)) (fun y => ‖Ξ (y - 1 + 1) - Ξ (y - 1)‖)
        (fun z => ‖Ξ (z + 1) - Ξ z‖) (fun y => rfl)]
      exact hD1
    · intro y
      rw [e]; exact hD1s _
  · simp only [sub_neg_eq_add]
    exact ⟨hD1, hD1s⟩

private lemma uvp_diff2_sum {L : ℕ} [NeZero L] (Ξ : Fin L → ℂ) (R2 : ℝ)
    (hD2 : ∑ y, ‖Ξ (y + 1 + 1) - 2 * Ξ (y + 1) + Ξ y‖ ≤ R2) (s s' : Fin L)
    (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) :
    ∑ y, ‖Ξ (y - s - s') - Ξ (y - s) - Ξ (y - s') + Ξ y‖ ≤ R2 := by
  have key : ∀ t : Fin L, ∑ y, ‖Ξ (y - t + 1 + 1) - 2 * Ξ (y - t + 1) + Ξ (y - t)‖ ≤ R2 := by
    intro t
    rw [Fintype.sum_equiv (Equiv.subRight t) (fun y => ‖Ξ (y - t + 1 + 1) - 2 * Ξ (y - t + 1) +
      Ξ (y - t)‖) (fun z => ‖Ξ (z + 1 + 1) - 2 * Ξ (z + 1) + Ξ z‖) (fun y => rfl)]
    exact hD2
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl
  · calc ∑ y, ‖Ξ (y - 1 - 1) - Ξ (y - 1) - Ξ (y - 1) + Ξ y‖
        = ∑ y, ‖Ξ (y - (1 + 1) + 1 + 1) - 2 * Ξ (y - (1 + 1) + 1) + Ξ (y - (1 + 1))‖ := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          have e1 : y - (1 + 1) + 1 + 1 = y := by abel
          have e2 : y - (1 + 1) + 1 = y - 1 := by abel
          have e3 : y - (1 + 1) = y - 1 - 1 := by abel
          rw [e1, e2, e3]; congr 1; ring
      _ ≤ R2 := key (1 + 1)
  · calc ∑ y, ‖Ξ (y - 1 - -1) - Ξ (y - 1) - Ξ (y - -1) + Ξ y‖
        = ∑ y, ‖Ξ (y - 1 + 1 + 1) - 2 * Ξ (y - 1 + 1) + Ξ (y - 1)‖ := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          have e1 : y - 1 + 1 + 1 = y + 1 := by abel
          have e2 : y - 1 + 1 = y := by abel
          have e3 : y - 1 - -1 = y := by abel
          have e4 : y - -1 = y + 1 := by abel
          rw [e1, e2, e3, e4, ← norm_neg]; congr 1; ring
      _ ≤ R2 := key 1
  · calc ∑ y, ‖Ξ (y - -1 - 1) - Ξ (y - -1) - Ξ (y - 1) + Ξ y‖
        = ∑ y, ‖Ξ (y - 1 + 1 + 1) - 2 * Ξ (y - 1 + 1) + Ξ (y - 1)‖ := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          have e1 : y - 1 + 1 + 1 = y + 1 := by abel
          have e2 : y - 1 + 1 = y := by abel
          have e3 : y - -1 - 1 = y := by abel
          have e4 : y - -1 = y + 1 := by abel
          rw [e1, e2, e3, e4, ← norm_neg]; congr 1; ring
      _ ≤ R2 := key 1
  · calc ∑ y, ‖Ξ (y - -1 - -1) - Ξ (y - -1) - Ξ (y - -1) + Ξ y‖
        = ∑ y, ‖Ξ (y - 0 + 1 + 1) - 2 * Ξ (y - 0 + 1) + Ξ (y - 0)‖ := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          have e1 : y - 0 + 1 + 1 = y + 1 + 1 := by abel
          have e2 : y - 0 + 1 = y + 1 := by abel
          have e3 : y - 0 = y := by abel
          have e4 : y - -1 - -1 = y + 1 + 1 := by abel
          have e5 : y - -1 = y + 1 := by abel
          rw [e1, e2, e3, e4, e5]; congr 1; ring
      _ ≤ R2 := key 0

/-- The mixed differences of the translated products along unit steps. -/
private lemma uvpH_Q_bound {L k : ℕ} [NeZero L] (Ξ : Fin L → ℂ) (Act : Finset (Fin k))
    (hn : 2 ≤ Act.card) (M M1 R1 R2 : ℝ) (hΞ : ∀ y, ‖Ξ y‖ ≤ M)
    (hD1 : ∑ y, ‖Ξ (y + 1) - Ξ y‖ ≤ R1) (hD1s : ∀ y, ‖Ξ (y + 1) - Ξ y‖ ≤ M1)
    (hD2 : ∑ y, ‖Ξ (y + 1 + 1) - 2 * Ξ (y + 1) + Ξ y‖ ≤ R2) (hRM : R1 * M1 ≤ R2 * M)
    (x w : Fin k → Fin L) (i j : Fin k) (s s' : Fin L) (hs : s = 1 ∨ s = -1)
    (hs' : s' = 1 ∨ s' = -1) :
    uvpL1 L (uvpQ (uvpH Ξ Act x) w (Pi.single i s) (Pi.single j s')) ≤
      R2 * M ^ (Act.card - 1) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hΞ 0)
  have hM1 : 0 ≤ M1 := (norm_nonneg _).trans (hD1s 0)
  have hR2 : 0 ≤ R2 := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hD2
  have hR1 : 0 ≤ R1 := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hD1
  have hzero : ∀ h : Fin L → ℂ, h = 0 → uvpL1 L h ≤ R2 * M ^ (Act.card - 1) := by
    intro h hh
    rw [hh, map_zero]; positivity
  by_cases hj : j ∈ Act
  swap
  · apply hzero
    unfold uvpQ
    rw [uvpH_add_single_notin Ξ Act x _ j hj, uvpH_add_single_notin Ξ Act x _ j hj]
    abel
  by_cases hi : i ∈ Act
  swap
  · apply hzero
    unfold uvpQ
    rw [add_right_comm w (Pi.single i s) (Pi.single j s'),
      uvpH_add_single_notin Ξ Act x _ i hi, uvpH_add_single_notin Ξ Act x _ i hi]
    abel
  set c : Fin k → Fin L := fun l => x l - w l with hc
  have hsub : ∀ l (u : Fin L), x l - u - w l = c l - u := fun l u => by
    simp only [hc]; abel
  by_cases hij : i = j
  · subst hij
    -- same coordinate
    have hQ : ∀ u : Fin L, uvpQ (uvpH Ξ Act x) w (Pi.single i s) (Pi.single i s') u =
        (Ξ (c i - u - s - s') - Ξ (c i - u - s) - Ξ (c i - u - s') + Ξ (c i - u)) *
          ∏ l ∈ Act.erase i, Ξ (c l - u) := by
      intro u
      have e1 : w + Pi.single i s + Pi.single i s' = w + Pi.single i (s + s') := by
        rw [add_assoc, ← Pi.single_add]
      have e0 : uvpH Ξ Act x w = uvpH Ξ Act x (w + Pi.single i 0) := by simp
      unfold uvpQ
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [e1, e0, uvpH_single_apply Ξ Act x w i hi, uvpH_single_apply Ξ Act x w i hi,
        uvpH_single_apply Ξ Act x w i hi, uvpH_single_apply Ξ Act x w i hi]
      simp only [hsub, sub_zero, sub_add_eq_sub_sub]
      ring
    have hg := uvp_diff2_sum Ξ R2 hD2 s s' hs hs'
    calc uvpL1 L (uvpQ (uvpH Ξ Act x) w (Pi.single i s) (Pi.single i s')) =
        ∑ u : Fin L, ‖(Ξ (c i - u - s - s') - Ξ (c i - u - s) - Ξ (c i - u - s') + Ξ (c i - u)) *
          ∏ l ∈ Act.erase i, Ξ (c l - u)‖ := by
          rw [uvpL1_apply]; exact Finset.sum_congr rfl (fun u _ => by rw [hQ])
      _ = ∑ u : Fin L, ‖(Ξ (c i - u - s - s') - Ξ (c i - u - s) - Ξ (c i - u - s') + Ξ (c i - u))‖ *
          ∏ l ∈ Act.erase i, ‖Ξ (c l - u)‖ := by
          refine Finset.sum_congr rfl (fun u _ => ?_)
          rw [norm_mul, norm_prod]
      _ ≤ R2 * M ^ (Act.erase i).card := by
          have := uvp_young Ξ (fun y => Ξ (y - s - s') - Ξ (y - s) - Ξ (y - s') + Ξ y)
            (Act.erase i) M R2 hΞ hg c i
          simpa using this
      _ = R2 * M ^ (Act.card - 1) := by
          rw [Finset.card_erase_of_mem hi]
  · -- distinct coordinates
    have hj' : j ∈ Act.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
    have hQ : ∀ u : Fin L, uvpQ (uvpH Ξ Act x) w (Pi.single i s) (Pi.single j s') u =
        ((Ξ (c i - u - s) - Ξ (c i - u)) * (Ξ (c j - u - s') - Ξ (c j - u))) *
          ∏ l ∈ (Act.erase i).erase j, Ξ (c l - u) := by
      intro u
      have e1 : uvpH Ξ Act x (w + Pi.single i s) =
          uvpH Ξ Act x (w + Pi.single i s + Pi.single j 0) := by simp
      have e2 : uvpH Ξ Act x (w + Pi.single j s') =
          uvpH Ξ Act x (w + Pi.single i 0 + Pi.single j s') := by simp
      have e3 : uvpH Ξ Act x w = uvpH Ξ Act x (w + Pi.single i 0 + Pi.single j 0) := by simp
      unfold uvpQ
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [e1, e2, e3, uvpH_two_apply Ξ Act x w i j hij hi hj,
        uvpH_two_apply Ξ Act x w i j hij hi hj, uvpH_two_apply Ξ Act x w i j hij hi hj,
        uvpH_two_apply Ξ Act x w i j hij hi hj]
      simp only [hsub, sub_zero]
      ring
    have hg := (uvp_diff1_sum Ξ R1 M1 hD1 hD1s s hs)
    have hg' := (uvp_diff1_sum Ξ R1 M1 hD1 hD1s s' hs')
    have hcard : ((Act.erase i).erase j).card = Act.card - 2 := by
      rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi]; omega
    calc uvpL1 L (uvpQ (uvpH Ξ Act x) w (Pi.single i s) (Pi.single j s')) =
        ∑ u : Fin L, ‖(Ξ (c i - u - s) - Ξ (c i - u))‖ * ‖(Ξ (c j - u - s') - Ξ (c j - u))‖ *
          ∏ l ∈ (Act.erase i).erase j, ‖Ξ (c l - u)‖ := by
          rw [uvpL1_apply]
          refine Finset.sum_congr rfl (fun u _ => ?_)
          rw [hQ, norm_mul, norm_mul, norm_prod]
      _ ≤ ∑ u : Fin L, M1 * (‖(Ξ (c i - u - s) - Ξ (c i - u))‖ *
          ∏ l ∈ (Act.erase i).erase j, ‖Ξ (c l - u)‖) := by
          refine Finset.sum_le_sum (fun u _ => ?_)
          have h1 := hg'.2 (c j - u)
          have h2 : 0 ≤ ‖(Ξ (c i - u - s) - Ξ (c i - u))‖ *
              ∏ l ∈ (Act.erase i).erase j, ‖Ξ (c l - u)‖ :=
            mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
          calc _ = ‖(Ξ (c j - u - s') - Ξ (c j - u))‖ * (‖(Ξ (c i - u - s) - Ξ (c i - u))‖ *
              ∏ l ∈ (Act.erase i).erase j, ‖Ξ (c l - u)‖) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right h1 h2
      _ = M1 * ∑ u : Fin L, ‖(Ξ (c i - u - s) - Ξ (c i - u))‖ *
          ∏ l ∈ (Act.erase i).erase j, ‖Ξ (c l - u)‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ M1 * (R1 * M ^ ((Act.erase i).erase j).card) := by
          refine mul_le_mul_of_nonneg_left ?_ hM1
          have := uvp_young Ξ (fun y => Ξ (y - s) - Ξ y) ((Act.erase i).erase j) M R1 hΞ hg.1 c i
          simpa using this
      _ = (R1 * M1) * M ^ (Act.card - 2) := by rw [hcard]; ring
      _ ≤ (R2 * M) * M ^ (Act.card - 2) :=
          mul_le_mul_of_nonneg_right hRM (pow_nonneg hM _)
      _ = R2 * M ^ (Act.card - 1) := by
          have : Act.card - 1 = (Act.card - 2) + 1 := by omega
          rw [this, pow_succ]; ring

/-! ### The Taylor bound on the cycle -/

/-- The symmetric Taylor bound for a family on `ℤ_L^k`, for the cyclic word length. -/
private lemma uvp_cyc_taylor {L k : ℕ} [NeZero L] {B : Type*} [AddCommGroup B] [Module ℂ B]
    (ν : Seminorm ℂ B) (H : (Fin k → Fin L) → B) (Mb : ℝ)
    (hU : ∀ (w : Fin k → Fin L) (i j : Fin k) (s s' : Fin L), (s = 1 ∨ s = -1) →
      (s' = 1 ∨ s' = -1) → ν (uvpQ H w (Pi.single i s) (Pi.single j s')) ≤ Mb)
    (S₀ : (Fin k → Fin L) → ℂ) (hS : ∀ w, S₀ (-w) = S₀ w) :
    ν (∑ w, S₀ w • H w) ≤ ‖∑ w, S₀ w‖ * ν (H 0) +
      (1 / 2) * ∑ w, ‖S₀ w‖ * (((∑ i, cycDist (w i) 0 : ℕ) : ℝ) ^ 2 * Mb) := by
  classical
  set N : (Fin k → Fin L) → ℕ := fun w => ∑ i, cycDist (w i) 0 with hN
  have hNneg : ∀ z, N (-z) = N z := by
    intro z
    simp only [hN, Pi.neg_apply, uvp_cycDist_neg]
  obtain ⟨hzero, hpeel0⟩ := uvp_pi_peel (ι := Fin k) (M := Fin L) (fun x => cycDist x 0) {1, -1}
    (by
      intro x hx
      rw [uvp_cycDist_zero_right] at hx
      have := x.isLt
      apply Fin.ext
      simp only [Fin.val_zero]
      omega)
    (uvp_cycDist_self 0) (fun x hx => uvp_cycDist_peel x hx)
  set U : Set (Fin k → Fin L) :=
    {u | ∃ i : Fin k, ∃ s : Fin L, (s = 1 ∨ s = -1) ∧ u = Pi.single i s} with hU'
  have hbound := uvpQ_bound ν H N U Mb (fun z hz => hzero z hz)
    (by
      intro n z hz
      obtain ⟨i, s, hs, hsum⟩ := hpeel0 n z hz
      refine ⟨Pi.single i s, ⟨i, s, ?_, rfl⟩, hsum⟩
      simpa using hs)
    (by
      rintro _ ⟨i, s, hs, rfl⟩ _ ⟨j, s', hs', rfl⟩ w
      exact hU w i j s s' hs hs')
  have hQ : ∀ z, ν (H z + H (-z) - (2 : ℂ) • H 0) ≤ (N z : ℝ) ^ 2 * Mb := by
    intro z
    have h := hbound z (-z) 0
    rw [hNneg] at h
    have e : H z + H (-z) - (2 : ℂ) • H 0 = -(uvpQ H 0 z (-z)) := by
      simp only [uvpQ, zero_add, add_neg_cancel]
      module
    rw [e, map_neg_eq_map]
    calc _ ≤ _ := h
      _ = _ := by ring
  exact uvpTaylor_sum ν H N Mb hQ Finset.univ (fun z _ => Finset.mem_univ _) S₀ hS

/-- The Taylor bound for the translated products of `Ξ` over the legs in `Act`. -/
private lemma uvp_xi_bound {L k : ℕ} [NeZero L] (Ξ : Fin L → ℂ) (Act : Finset (Fin k))
    (hn : 2 ≤ Act.card) (M M1 R0 R1 R2 : ℝ) (hΞ : ∀ y, ‖Ξ y‖ ≤ M) (hD0 : ∑ y, ‖Ξ y‖ ≤ R0)
    (hD1 : ∑ y, ‖Ξ (y + 1) - Ξ y‖ ≤ R1) (hD1s : ∀ y, ‖Ξ (y + 1) - Ξ y‖ ≤ M1)
    (hD2 : ∑ y, ‖Ξ (y + 1 + 1) - 2 * Ξ (y + 1) + Ξ y‖ ≤ R2) (hRM : R1 * M1 ≤ R2 * M)
    (ν : Seminorm ℂ (Fin L → ℂ)) (hν : ∀ h, ν h ≤ uvpL1 L h) (x : Fin k → Fin L)
    (S₀ : (Fin k → Fin L) → ℂ) (hS : ∀ w, S₀ (-w) = S₀ w) :
    ν (∑ w, S₀ w • uvpH Ξ Act x w) ≤ ‖∑ w, S₀ w‖ * (R0 * M ^ (Act.card - 1)) +
      (1 / 2) * (R2 * M ^ (Act.card - 1)) *
        ∑ w, ‖S₀ w‖ * ((∑ i, cycDist (w i) 0 : ℕ) : ℝ) ^ 2 := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hΞ 0)
  have key := uvp_cyc_taylor ν (uvpH Ξ Act x) (R2 * M ^ (Act.card - 1))
    (fun w i j s s' hs hs' => (hν _).trans
      (uvpH_Q_bound Ξ Act hn M M1 R1 R2 hΞ hD1 hD1s hD2 hRM x w i j s s' hs hs')) S₀ hS
  have hi : ∃ i, i ∈ Act := Finset.card_pos.mp (by omega)
  obtain ⟨i, hiA⟩ := hi
  have hH0 : ν (uvpH Ξ Act x 0) ≤ R0 * M ^ (Act.card - 1) := by
    refine (hν _).trans ?_
    rw [uvpL1_apply]
    calc ∑ u : Fin L, ‖uvpH Ξ Act x 0 u‖
        = ∑ u : Fin L, ‖Ξ (x i - u)‖ * ∏ l ∈ Act.erase i, ‖Ξ (x l - u)‖ := by
          refine Finset.sum_congr rfl (fun u _ => ?_)
          unfold uvpH
          rw [← Finset.mul_prod_erase Act _ hiA, norm_mul, norm_prod]
          simp
      _ ≤ R0 * M ^ (Act.erase i).card := uvp_young Ξ Ξ (Act.erase i) M R0 hΞ hD0 x i
      _ = R0 * M ^ (Act.card - 1) := by rw [Finset.card_erase_of_mem hiA]
  refine key.trans ?_
  have hS0 : 0 ≤ ‖∑ w, S₀ w‖ := norm_nonneg _
  have e : ∑ w, ‖S₀ w‖ * (((∑ i, cycDist (w i) 0 : ℕ) : ℝ) ^ 2 * (R2 * M ^ (Act.card - 1))) =
      (R2 * M ^ (Act.card - 1)) * ∑ w, ‖S₀ w‖ * ((∑ i, cycDist (w i) 0 : ℕ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  rw [e]
  have := mul_le_mul_of_nonneg_left hH0 hS0
  linarith

/-! ### Moments of the core profile -/

private lemma uvp_sq_exp (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-t) ≤ 8 * Real.exp (-(t / 2)) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := t / 2) (by positivity)
  have h2 : t ^ 2 ≤ 8 * Real.exp (t / 2) := by nlinarith
  calc t ^ 2 * Real.exp (-t) ≤ 8 * Real.exp (t / 2) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 8 * Real.exp (-(t / 2)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

private lemma uvp_prod_exp {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c' a : ℝ) :
    ∏ i ∈ s, Real.exp (-(c' * f i / a)) = Real.exp (-(c' * (∑ i ∈ s, f i) / a)) := by
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_div]

/-- The moment bound (B.8) [uvp:eq:moments]: the core summed against the squared word length. -/
private lemma uvp_moment (k : ℕ) (hk : 2 ≤ k) (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ (L : ℕ) [NeZero L] (a : ℝ), 1 ≤ a →
      ∀ (S : (Fin k → Fin L) → ℂ) (p : Fin k),
      (∀ x, ‖S x‖ ≤ C * Real.exp (-(c * wordDiam x / a))) →
      ∑ w : Fin k → Fin L, ‖(if w p = 0 then S w else 0)‖ *
        ((∑ i, cycDist (w i) 0 : ℕ) : ℝ) ^ 2 ≤ C₃ * a ^ (k + 1) := by
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  set c' : ℝ := c / ((k : ℝ) - 1) with hc'
  have hc'0 : 0 < c' := div_pos hc hk1
  set c'' : ℝ := c' / 2 with hc''
  have hc''0 : 0 < c'' := by positivity
  refine ⟨C * (8 / c' ^ 2) * (2 * (1 + 1 / c'')) ^ (k - 1), by positivity, ?_⟩
  intro L _ a ha S p hS
  have ha0 : 0 < a := by linarith
  have hterm : ∀ w : Fin k → Fin L, ‖(if w p = 0 then S w else 0)‖ *
      ((∑ i, cycDist (w i) 0 : ℕ) : ℝ) ^ 2 ≤ (C * (8 * (a / c') ^ 2)) *
        (if w p = 0 then ∏ i ∈ Finset.univ.erase p,
          Real.exp (-(c'' * (cycDist (w i) 0 : ℝ) / a)) else 0) := by
    intro w
    by_cases hw : w p = 0
    · simp only [hw, ite_true]
      have hprof := uvp_profile_prod hk c a hc ha0 p w
      have hprof' : ‖S w‖ ≤ C * ∏ i ∈ Finset.univ.erase p,
          Real.exp (-(c' * (cycDist (w i) 0 : ℝ) / a)) := by
        refine (hS w).trans (mul_le_mul_of_nonneg_left (hprof.trans (le_of_eq ?_)) hC.le)
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [hw]
      rw [uvp_prod_exp] at hprof'
      set Np : ℝ := ∑ i ∈ Finset.univ.erase p, (cycDist (w i) 0 : ℝ) with hNp
      have hNp0 : 0 ≤ Np := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
      have hcast : ((∑ i, cycDist (w i) 0 : ℕ) : ℝ) = Np := by
        rw [Nat.cast_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ p), hw,
          uvp_cycDist_self]
        simp [hNp]
      rw [hcast, uvp_prod_exp]
      set t : ℝ := c' * Np / a with ht
      have ht0 : 0 ≤ t := by positivity
      have hNt : Np ^ 2 = (a / c') ^ 2 * t ^ 2 := by
        rw [ht]; field_simp
      have hsq := uvp_sq_exp t ht0
      have hexp : -(c'' * Np / a) = -(t / 2) := by
        rw [ht, hc'']; ring
      rw [hexp]
      calc ‖S w‖ * Np ^ 2 ≤ (C * Real.exp (-t)) * Np ^ 2 :=
            mul_le_mul_of_nonneg_right hprof' (sq_nonneg _)
        _ = C * (a / c') ^ 2 * (t ^ 2 * Real.exp (-t)) := by rw [hNt]; ring
        _ ≤ C * (a / c') ^ 2 * (8 * Real.exp (-(t / 2))) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = C * (8 * (a / c') ^ 2) * Real.exp (-(t / 2)) := by ring
    · simp [hw]
  calc ∑ w : Fin k → Fin L, ‖(if w p = 0 then S w else 0)‖ * ((∑ i, cycDist (w i) 0 : ℕ) : ℝ) ^ 2
      ≤ ∑ w : Fin k → Fin L, (C * (8 * (a / c') ^ 2)) *
        (if w p = 0 then ∏ i ∈ Finset.univ.erase p,
          Real.exp (-(c'' * (cycDist (w i) 0 : ℝ) / a)) else 0) :=
        Finset.sum_le_sum (fun w _ => hterm w)
    _ = (C * (8 * (a / c') ^ 2)) * ∑ w : Fin k → Fin L,
        (if w p = 0 then ∏ i ∈ Finset.univ.erase p,
          Real.exp (-(c'' * (cycDist (w i) 0 : ℝ) / a)) else 0) := (Finset.mul_sum _ _ _).symm
    _ = (C * (8 * (a / c') ^ 2)) * ∏ i ∈ Finset.univ.erase p, ∑ y : Fin L,
          Real.exp (-(c'' * (cycDist y 0 : ℝ) / a)) := by
        rw [uvp_sum_prod_anchor p (fun _ y => Real.exp (-(c'' * (cycDist y 0 : ℝ) / a)))]
    _ ≤ (C * (8 * (a / c') ^ 2)) * (2 * (1 + a / c'')) ^ (k - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∏ i ∈ Finset.univ.erase p, ∑ y : Fin L, Real.exp (-(c'' * (cycDist y 0 : ℝ) / a))
            ≤ ∏ _i ∈ Finset.univ.erase p, (2 * (1 + a / c'')) :=
              Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
                (fun _ _ => uvp_geom_sum c'' a hc''0 ha0)
          _ = (2 * (1 + a / c'')) ^ (k - 1) := by
              rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ p),
                Finset.card_univ, Fintype.card_fin]
    _ ≤ (C * (8 * (a / c') ^ 2)) * (2 * (1 + 1 / c'') * a) ^ (k - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine pow_le_pow_left₀ (by positivity) ?_ _
        have : a / c'' ≤ a * (1 / c'') := by rw [div_eq_mul_one_div]
        nlinarith [one_div_pos.mpr hc''0]
    _ = C * (8 / c' ^ 2) * (2 * (1 + 1 / c'')) ^ (k - 1) * a ^ (k + 1) := by
        rw [mul_pow (2 * (1 + 1 / c'')) a]
        have : a ^ (k + 1) = a ^ 2 * a ^ (k - 1) := by
          rw [← pow_add]; congr 1; omega
        rw [this]
        field_simp

/-! ### Translation invariance: reduction to the anchored family -/

private lemma uvp_bridge_point {L k : ℕ} [NeZero L] (Ξ : Fin L → ℂ) (S : (Fin k → Fin L) → ℂ)
    (hT : ∀ (x : Fin k → Fin L) (z : Fin L), S (fun i => x i + z) = S x) (p : Fin k)
    (x : Fin k → Fin L) :
    ‖∑ y, S y * ∏ j, Ξ (x j - y j)‖ =
      uvpSumNorm L (∑ w, (if w p = 0 then S w else 0) • uvpH Ξ Finset.univ x w) := by
  rw [uvpSumNorm_apply]
  congr 1
  rw [uvp_sum_anchor p]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hw : w p = 0
  · simp only [hw, ite_true]
    have h1 : S (w + (fun _ => u : Fin k → Fin L)) = S w := hT w u
    rw [h1]
    congr 1
    unfold uvpH
    refine Finset.prod_congr rfl (fun j _ => ?_)
    congr 1
    simp only [Pi.add_apply]
    abel
  · simp [hw]

private lemma uvp_bridge_row {L k : ℕ} [NeZero L] (Ξ : Fin L → ℂ) (S : (Fin k → Fin L) → ℂ)
    (hT : ∀ (x : Fin k → Fin L) (z : Fin L), S (fun i => x i + z) = S x) (v : Fin k)
    (x : Fin k → Fin L) :
    ∑ xv : Fin L, ‖∑ y, S y * ∏ j, (if j = v then (if xv = y j then (1 : ℂ) else 0)
      else Ξ (x j - y j))‖ =
      uvpL1 L (∑ w, (if w v = 0 then S w else 0) • uvpH Ξ (Finset.univ.erase v) x w) := by
  rw [uvpL1_apply]
  refine Finset.sum_congr rfl (fun xv _ => ?_)
  congr 1
  rw [uvp_sum_anchor v, Finset.sum_comm]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hw : w v = 0
  · simp only [hw, ite_true]
    have h1 : ∀ u : Fin L, S (w + (fun _ => u : Fin k → Fin L)) = S w := fun u => hT w u
    have h2 : ∀ u : Fin L, ∏ j, (if j = v then (if xv = (w + (fun _ => u : Fin k → Fin L)) j
        then (1 : ℂ) else 0) else Ξ (x j - (w + (fun _ => u : Fin k → Fin L)) j)) =
        (if xv = u then 1 else 0) * uvpH Ξ (Finset.univ.erase v) x w u := by
      intro u
      rw [uvp_prod_ite v (fun j => if xv = (w + (fun _ => u : Fin k → Fin L)) j then (1 : ℂ) else 0)
        (fun j => Ξ (x j - (w + (fun _ => u : Fin k → Fin L)) j))]
      congr 1
      · simp [hw]
      · unfold uvpH
        refine Finset.prod_congr rfl (fun j _ => ?_)
        congr 1
        simp only [Pi.add_apply]
        abel
    calc ∑ u : Fin L, S (w + (fun _ => u : Fin k → Fin L)) * ∏ j, (if j = v then
          (if xv = (w + (fun _ => u : Fin k → Fin L)) j then (1 : ℂ) else 0) else
            Ξ (x j - (w + (fun _ => u : Fin k → Fin L)) j))
        = ∑ u : Fin L, (if xv = u then S w * uvpH Ξ (Finset.univ.erase v) x w u else 0) := by
          refine Finset.sum_congr rfl (fun u _ => ?_)
          rw [h1, h2]
          by_cases hu : xv = u <;> simp [hu]
      _ = S w * uvpH Ξ (Finset.univ.erase v) x w xv := by
          rw [Finset.sum_ite_eq]; simp
  · simp [hw]

/-! ### The all-`Ξ` term -/

/-- The all-`Ξ` term of the pointwise norm (proof of Theorem B.6 [uvp:thm:molecule]). -/
private lemma uvp_allXi_point (k : ℕ) (hk : 3 ≤ k) (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (L : ℕ) [NeZero L] (a δ ℓ lam : ℝ), 1 ≤ a → 0 < δ → 0 < ℓ → 0 ≤ lam →
      lam ^ 2 = δ / a ^ 2 → ∀ (Ξ : Fin L → ℂ) (S : (Fin k → Fin L) → ℂ),
      ∑ x, ‖Ξ x‖ ≤ C / δ → (∀ x, ‖Ξ x‖ ≤ C / (δ * ℓ)) →
      ∑ x, ‖Ξ (x + 1) - Ξ x‖ ≤ C * lam / δ → (∀ x, ‖Ξ (x + 1) - Ξ x‖ ≤ C * lam / (δ * ℓ)) →
      ∑ x, ‖Ξ (x + 1 + 1) - 2 * Ξ (x + 1) + Ξ x‖ ≤ C * lam ^ 2 / δ →
      (∀ (x : Fin k → Fin L) (z : Fin L), S (fun i => x i + z) = S x) →
      (∀ x, S (fun i => -x i) = S x) →
      (∀ x, ‖S x‖ ≤ C * Real.exp (-(c * wordDiam x / a))) →
      (∀ v : Fin k, ‖∑ x ∈ Finset.univ.filter (fun x : Fin k → Fin L => x v = 0), S x‖ ≤
        C * δ * a ^ (k - 1)) →
      ∀ x : Fin k → Fin L, ‖∑ y, S y * ∏ j, Ξ (x j - y j)‖ ≤ D * (a / (δ * ℓ)) ^ (k - 1) := by
  obtain ⟨C₃, hC₃, hmom⟩ := uvp_moment k (by omega) c C hc hC
  refine ⟨C ^ (k - 1 + 2) + 1 / 2 * C ^ (k - 1 + 1) * C₃, by positivity, ?_⟩
  intro L _ a δ ℓ lam ha hδ hℓ hlam hlam2 Ξ S hD0 hΞ hD1 hD1s hD2 hT hSev hSprof hmass x
  have ha0 : 0 < a := by linarith
  have hδℓ : 0 < δ * ℓ := mul_pos hδ hℓ
  set p : Fin k := ⟨0, by omega⟩ with hp
  set S₀ : (Fin k → Fin L) → ℂ := fun w => if w p = 0 then S w else 0 with hS₀
  have hS₀ev : ∀ w, S₀ (-w) = S₀ w := by
    intro w
    simp only [hS₀, Pi.neg_apply, neg_eq_zero]
    by_cases hw : w p = 0
    · simp only [hw, ite_true]; exact hSev w
    · simp [hw]
  rw [uvp_bridge_point Ξ S hT p x]
  have hRM : (C * lam / δ) * (C * lam / (δ * ℓ)) ≤ (C * lam ^ 2 / δ) * (C / (δ * ℓ)) := by
    apply le_of_eq; field_simp
  have hxi := uvp_xi_bound Ξ Finset.univ (by simp; omega) (C / (δ * ℓ)) (C * lam / (δ * ℓ))
    (C / δ) (C * lam / δ) (C * lam ^ 2 / δ) hΞ hD0 hD1 hD1s hD2 hRM (uvpSumNorm L)
    uvpSumNorm_le_L1 x S₀ hS₀ev
  refine hxi.trans ?_
  have hm : (Finset.univ : Finset (Fin k)).card - 1 = k - 1 := by simp
  rw [hm]
  have hmass' : ‖∑ w, S₀ w‖ ≤ C * δ * a ^ (k - 1) := by
    have : ∑ w, S₀ w = ∑ x ∈ Finset.univ.filter (fun x : Fin k → Fin L => x p = 0), S x := by
      rw [Finset.sum_filter]
    rw [this]; exact hmass p
  have hmom' : ∑ w, ‖S₀ w‖ * ((∑ i, cycDist (w i) 0 : ℕ) : ℝ) ^ 2 ≤ C₃ * a ^ (k - 1 + 2) := by
    have h := hmom L a ha S p hSprof
    have e : k + 1 = k - 1 + 2 := by omega
    rw [e] at h
    exact h
  set m := k - 1 with hmdef
  have hMpos : 0 ≤ (C / (δ * ℓ)) ^ m := by positivity
  have hmain : (C / (δ * ℓ)) ^ m * a ^ m = C ^ m * (a / (δ * ℓ)) ^ m := by
    rw [← mul_pow, ← mul_pow]; congr 1; field_simp
  calc ‖∑ w, S₀ w‖ * (C / δ * (C / (δ * ℓ)) ^ m) +
        1 / 2 * (C * lam ^ 2 / δ * (C / (δ * ℓ)) ^ m) *
          ∑ w, ‖S₀ w‖ * ((∑ i, cycDist (w i) 0 : ℕ) : ℝ) ^ 2
      ≤ (C * δ * a ^ m) * (C / δ * (C / (δ * ℓ)) ^ m) +
        1 / 2 * (C * lam ^ 2 / δ * (C / (δ * ℓ)) ^ m) * (C₃ * a ^ (m + 2)) := by
        gcongr
    _ = (C ^ (m + 2) + 1 / 2 * C ^ (m + 1) * C₃) * (a / (δ * ℓ)) ^ m := by
        have e1 : (C * δ * a ^ m) * (C / δ * (C / (δ * ℓ)) ^ m) =
            C ^ (m + 2) * (a / (δ * ℓ)) ^ m := by
          calc _ = C ^ 2 * ((C / (δ * ℓ)) ^ m * a ^ m) := by field_simp
            _ = _ := by rw [hmain]; ring
        have e2 : 1 / 2 * (C * lam ^ 2 / δ * (C / (δ * ℓ)) ^ m) * (C₃ * a ^ (m + 2)) =
            1 / 2 * C ^ (m + 1) * C₃ * (a / (δ * ℓ)) ^ m := by
          rw [hlam2]
          calc _ = 1 / 2 * C * C₃ * ((C / (δ * ℓ)) ^ m * a ^ m) := by field_simp; ring
            _ = _ := by rw [hmain]; ring
        rw [e1, e2]; ring

/-- The all-`Ξ` term of the undressed-row norm (proof of Theorem B.6 [uvp:thm:molecule]). -/
private lemma uvp_allXi_row (k : ℕ) (hk : 3 ≤ k) (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (L : ℕ) [NeZero L] (a δ ℓ lam : ℝ), 1 ≤ a → 0 < δ → 0 < ℓ → 0 ≤ lam →
      lam ^ 2 = δ / a ^ 2 → ∀ (Ξ : Fin L → ℂ) (S : (Fin k → Fin L) → ℂ),
      ∑ x, ‖Ξ x‖ ≤ C / δ → (∀ x, ‖Ξ x‖ ≤ C / (δ * ℓ)) →
      ∑ x, ‖Ξ (x + 1) - Ξ x‖ ≤ C * lam / δ → (∀ x, ‖Ξ (x + 1) - Ξ x‖ ≤ C * lam / (δ * ℓ)) →
      ∑ x, ‖Ξ (x + 1 + 1) - 2 * Ξ (x + 1) + Ξ x‖ ≤ C * lam ^ 2 / δ →
      (∀ (x : Fin k → Fin L) (z : Fin L), S (fun i => x i + z) = S x) →
      (∀ x, S (fun i => -x i) = S x) →
      (∀ x, ‖S x‖ ≤ C * Real.exp (-(c * wordDiam x / a))) →
      (∀ v : Fin k, ‖∑ x ∈ Finset.univ.filter (fun x : Fin k → Fin L => x v = 0), S x‖ ≤
        C * δ * a ^ (k - 1)) →
      ∀ (v : Fin k) (x : Fin k → Fin L), ∑ xv : Fin L, ‖∑ y, S y * ∏ j, (if j = v then
        (if xv = y j then (1 : ℂ) else 0) else Ξ (x j - y j))‖ ≤
          D * a * (a / (δ * ℓ)) ^ (k - 2) := by
  obtain ⟨C₃, hC₃, hmom⟩ := uvp_moment k (by omega) c C hc hC
  refine ⟨C ^ (k - 2 + 2) + 1 / 2 * C ^ (k - 2 + 1) * C₃, by positivity, ?_⟩
  intro L _ a δ ℓ lam ha hδ hℓ hlam hlam2 Ξ S hD0 hΞ hD1 hD1s hD2 hT hSev hSprof hmass v x
  have ha0 : 0 < a := by linarith
  have hδℓ : 0 < δ * ℓ := mul_pos hδ hℓ
  set S₀ : (Fin k → Fin L) → ℂ := fun w => if w v = 0 then S w else 0 with hS₀
  have hS₀ev : ∀ w, S₀ (-w) = S₀ w := by
    intro w
    simp only [hS₀, Pi.neg_apply, neg_eq_zero]
    by_cases hw : w v = 0
    · simp only [hw, ite_true]; exact hSev w
    · simp [hw]
  rw [uvp_bridge_row Ξ S hT v x]
  have hRM : (C * lam / δ) * (C * lam / (δ * ℓ)) ≤ (C * lam ^ 2 / δ) * (C / (δ * ℓ)) := by
    apply le_of_eq; field_simp
  have hcard : (Finset.univ.erase v : Finset (Fin k)).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v)]; simp
  have hxi := uvp_xi_bound Ξ (Finset.univ.erase v) (by omega) (C / (δ * ℓ)) (C * lam / (δ * ℓ))
    (C / δ) (C * lam / δ) (C * lam ^ 2 / δ) hΞ hD0 hD1 hD1s hD2 hRM (uvpL1 L)
    (fun h => le_refl _) x S₀ hS₀ev
  refine hxi.trans ?_
  have hm : (Finset.univ.erase v : Finset (Fin k)).card - 1 = k - 2 := by omega
  rw [hm]
  have hmass' : ‖∑ w, S₀ w‖ ≤ C * δ * a ^ (k - 2 + 1) := by
    have : ∑ w, S₀ w = ∑ x ∈ Finset.univ.filter (fun x : Fin k → Fin L => x v = 0), S x := by
      rw [Finset.sum_filter]
    have e : k - 1 = k - 2 + 1 := by omega
    rw [this]; rw [e] at hmass; exact hmass v
  have hmom' : ∑ w, ‖S₀ w‖ * ((∑ i, cycDist (w i) 0 : ℕ) : ℝ) ^ 2 ≤ C₃ * a ^ (k - 2 + 3) := by
    have h := hmom L a ha S v hSprof
    have e : k + 1 = k - 2 + 3 := by omega
    rw [e] at h
    exact h
  set m := k - 2 with hmdef
  have hMpos : 0 ≤ (C / (δ * ℓ)) ^ m := by positivity
  have hmain : (C / (δ * ℓ)) ^ m * a ^ m = C ^ m * (a / (δ * ℓ)) ^ m := by
    rw [← mul_pow, ← mul_pow]; congr 1; field_simp
  calc ‖∑ w, S₀ w‖ * (C / δ * (C / (δ * ℓ)) ^ m) +
        1 / 2 * (C * lam ^ 2 / δ * (C / (δ * ℓ)) ^ m) *
          ∑ w, ‖S₀ w‖ * ((∑ i, cycDist (w i) 0 : ℕ) : ℝ) ^ 2
      ≤ (C * δ * a ^ (m + 1)) * (C / δ * (C / (δ * ℓ)) ^ m) +
        1 / 2 * (C * lam ^ 2 / δ * (C / (δ * ℓ)) ^ m) * (C₃ * a ^ (m + 3)) := by
        gcongr
    _ = (C ^ (m + 2) + 1 / 2 * C ^ (m + 1) * C₃) * a * (a / (δ * ℓ)) ^ m := by
        have e1 : (C * δ * a ^ (m + 1)) * (C / δ * (C / (δ * ℓ)) ^ m) =
            C ^ (m + 2) * a * (a / (δ * ℓ)) ^ m := by
          calc _ = C ^ 2 * a * ((C / (δ * ℓ)) ^ m * a ^ m) := by field_simp; ring
            _ = _ := by rw [hmain]; ring
        have e2 : 1 / 2 * (C * lam ^ 2 / δ * (C / (δ * ℓ)) ^ m) * (C₃ * a ^ (m + 3)) =
            1 / 2 * C ^ (m + 1) * C₃ * a * (a / (δ * ℓ)) ^ m := by
          rw [hlam2]
          calc _ = 1 / 2 * C * C₃ * a * ((C / (δ * ℓ)) ^ m * a ^ m) := by field_simp; ring
            _ = _ := by rw [hmain]; ring
        rw [e1, e2]; ring

/-! ### Assembly of the molecule estimate -/

private lemma uvp_row_prod {L : ℕ} [NeZero L] (Ξ Er : Fin L → ℂ) {k : ℕ} (mixed : Fin k → Bool)
    (Vst : Fin k → Fin L → ℂ) (T : Finset (Fin k)) (v : Fin k) (hvT : v ∉ T)
    (x : Fin k → Fin L) (xv : Fin L) (y : Fin k → Fin L) :
    ∏ j, uvpV Ξ Er mixed Vst (some v) T j ((Function.update x v xv) j - y j) =
      ∏ j, (if j = v then (if xv = y j then (1 : ℂ) else 0)
        else uvpV Ξ Er mixed Vst (some v) T j (x j - y j)) := by
  refine Finset.prod_congr rfl (fun j _ => ?_)
  by_cases hj : j = v
  · subst hj
    simp [uvpV, hvT, uvpX, sub_eq_zero]
  · simp [hj]

private lemma uvp_row_zero {L : ℕ} [NeZero L] (Ξ Er : Fin L → ℂ) {k : ℕ} (mixed : Fin k → Bool)
    (Vst : Fin k → Fin L → ℂ) (T : Finset (Fin k)) (v : Fin k) (hvT : v ∈ T)
    (z : Fin k → Fin L) : ∏ j, uvpV Ξ Er mixed Vst (some v) T j (z j) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
  simp [uvpV, hvT, uvpR]

private lemma uvp_empty_stable {L : ℕ} [NeZero L] (Ξ Er : Fin L → ℂ) {k : ℕ}
    (mixed : Fin k → Bool) (Vst : Fin k → Fin L → ℂ) (undress : Option (Fin k)) (j : Fin k)
    (hj : mixed j = false) (hu : undress ≠ some j) (z : Fin L) :
    uvpV Ξ Er mixed Vst undress ∅ j z = 0 := by
  simp [uvpV, uvpX, hj, hu]

private lemma uvp_empty_mixed {L : ℕ} [NeZero L] (Ξ Er : Fin L → ℂ) {k : ℕ}
    (mixed : Fin k → Bool) (Vst : Fin k → Fin L → ℂ) (undress : Option (Fin k)) (j : Fin k)
    (hj : mixed j = true) (hu : undress ≠ some j) :
    uvpV Ξ Er mixed Vst undress ∅ j = Ξ := by
  simp [uvpV, uvpX, hj, hu]

/-- Theorem B.6 [uvp:thm:molecule]: the pointwise and undressed-row norms of a single dressed
molecule, uniformly in `a, L, δ`. -/
theorem uvp_molecule (k : ℕ) (hk : 3 ≤ k) (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (L : ℕ) [NeZero L] (a δ ε : ℝ), 1 ≤ a → a ≤ L → 0 < δ → δ ≤ 1 →
      ∀ (Ξ Er : Fin L → ℂ) (mixed : Fin k → Bool) (Vst : Fin k → Fin L → ℂ)
        (S : (Fin k → Fin L) → ℂ),
      UvpKernels L a δ c C ε Ξ Er mixed Vst → UvpCore L a δ c C (∀ j, mixed j = true) S →
      let A := a / (δ * min (L : ℝ) (a / Real.sqrt δ))
      (∀ x, ‖uvpDress Ξ Er mixed Vst S none x‖ ≤ C' * A ^ (k - 1)) ∧
      ∀ v, mixed v = true → ∀ x : Fin k → Fin L,
        ∑ xv : Fin L, ‖uvpDress Ξ Er mixed Vst S (some v) (Function.update x v xv)‖ ≤
          C' * a * A ^ (k - 2) := by
  have hk2 : 2 ≤ k := by omega
  have hCt0 : 0 < 1 + C + 2 * (1 + ((k : ℝ) - 1) / c) * C := by
    have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    positivity
  have hCCt : C ≤ 1 + C + 2 * (1 + ((k : ℝ) - 1) / c) * C := by
    have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have : 0 ≤ 2 * (1 + ((k : ℝ) - 1) / c) * C := by positivity
    linarith
  obtain ⟨C₁, hC₁, hanc⟩ := uvp_anchor k hk2 c _ hc hCt0
  obtain ⟨D₁, hD₁, hpt⟩ := uvp_allXi_point k hk c C hc hC
  obtain ⟨D₂, hD₂, hrw⟩ := uvp_allXi_row k hk c C hc hC
  refine ⟨2 ^ k * (C₁ + D₁ + D₂), by positivity, ?_⟩
  intro L _ a δ ε ha haL hδ hδ1 Ξ Er mixed Vst S hK hS A
  have ha0 : 0 < a := by linarith
  have hℓ := uvp_ell_pos (L := L) ha0 hδ
  have hA1 : 1 ≤ A := uvp_A_ge_one (L := L) ha0 hδ hδ1
  have hA0 : 0 ≤ A := by linarith
  obtain ⟨hst, hΞ0, hΞs, hΔ1, hΔs, hΔ2, hE1, hε⟩ := uvp_kernels_unpack hc.le ha0.le hK
  obtain ⟨hT, hSev, hSprof, hmass⟩ := hS
  have hSprof' : ∀ x, ‖S x‖ ≤ (1 + C + 2 * (1 + ((k : ℝ) - 1) / c) * C) *
      Real.exp (-(c * (wordDiam x : ℝ) / a)) := fun x =>
    (hSprof x).trans (mul_le_mul_of_nonneg_right hCCt (Real.exp_pos _).le)
  have hlam : 0 ≤ Real.sqrt δ / a := by positivity
  have hlam2 : (Real.sqrt δ / a) ^ 2 = δ / a ^ 2 := by
    rw [div_pow, Real.sq_sqrt hδ.le]
  have hcard : (Finset.univ : Finset (Finset (Fin k))).card = 2 ^ k := by
    simp [Finset.card_univ, Fintype.card_finset]
  have hP1 : 0 ≤ (C₁ + D₁) * A ^ (k - 1) := by positivity
  have hP2 : 0 ≤ (C₁ + D₂) * a * A ^ (k - 2) := by positivity
  constructor
  · -- pointwise norm
    intro x
    have hterm : ∀ T : Finset (Fin k),
        ‖∑ y, S y * ∏ j, uvpV Ξ Er mixed Vst none T j (x j - y j)‖ ≤
          (C₁ + D₁) * A ^ (k - 1) := by
      intro T
      by_cases hTne : T.Nonempty
      · obtain ⟨j₀, hj₀⟩ := hTne
        refine le_trans ((hanc L a A ha hA1 S (uvpV Ξ Er mixed Vst none T) j₀ hSprof'
          ((uvp_legs hk2 hc hC ha hδ hδ1 hK none T j₀).1 hj₀)
          (fun j _ x' => (uvp_legs hk2 hc hC ha hδ hδ1 hK none T j).2 x')).1 x) ?_
        gcongr
        linarith
      · have hT0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
        subst hT0
        by_cases hall : ∀ j, mixed j = true
        · have hΞe : ∀ j, uvpV Ξ Er mixed Vst none ∅ j = Ξ := fun j =>
            uvp_empty_mixed Ξ Er mixed Vst none j (hall j) (by simp)
          have hmass' := hmass hall
          simp only [hΞe]
          refine le_trans (hpt L a δ (min (L : ℝ) (a / Real.sqrt δ)) (Real.sqrt δ / a) ha hδ hℓ
            hlam hlam2 Ξ S hΞ0 hΞs hΔ1 hΔs hΔ2 hT hSev hSprof hmass' x) ?_
          have : 0 ≤ A ^ (k - 1) := by positivity
          nlinarith [mul_nonneg hC₁.le this]
        · push Not at hall
          obtain ⟨j, hj⟩ := hall
          have hj' : mixed j = false := by simpa using hj
          have h0 : ∀ y : Fin k → Fin L,
              ∏ j', uvpV Ξ Er mixed Vst none ∅ j' (x j' - y j') = 0 := fun y =>
            Finset.prod_eq_zero (Finset.mem_univ j) (uvp_empty_stable Ξ Er mixed Vst none j hj'
              (by simp) _)
          simp only [h0, mul_zero, Finset.sum_const_zero, norm_zero]
          exact hP1
    rw [uvp_dress_expand]
    calc ‖∑ T : Finset (Fin k), ∑ y : Fin k → Fin L,
          S y * ∏ j, uvpV Ξ Er mixed Vst none T j (x j - y j)‖
        ≤ ∑ T : Finset (Fin k), ‖∑ y : Fin k → Fin L,
          S y * ∏ j, uvpV Ξ Er mixed Vst none T j (x j - y j)‖ := norm_sum_le _ _
      _ ≤ ∑ _T : Finset (Fin k), (C₁ + D₁) * A ^ (k - 1) :=
          Finset.sum_le_sum (fun T _ => hterm T)
      _ = 2 ^ k * ((C₁ + D₁) * A ^ (k - 1)) := by
          rw [Finset.sum_const, hcard]; simp
      _ ≤ 2 ^ k * (C₁ + D₁ + D₂) * A ^ (k - 1) := by
          have : 0 ≤ A ^ (k - 1) := by positivity
          have h2 : (0 : ℝ) ≤ 2 ^ k := by positivity
          nlinarith [mul_nonneg h2 (mul_nonneg hD₂.le this)]
  · -- undressed row
    intro v hv x
    have hterm : ∀ T : Finset (Fin k), ∑ xv : Fin L,
        ‖∑ y, S y * ∏ j, uvpV Ξ Er mixed Vst (some v) T j ((Function.update x v xv) j - y j)‖ ≤
          (C₁ + D₂) * a * A ^ (k - 2) := by
      intro T
      by_cases hvT : v ∈ T
      · have h0 : ∀ xv : Fin L, ∀ y : Fin k → Fin L,
            ∏ j, uvpV Ξ Er mixed Vst (some v) T j ((Function.update x v xv) j - y j) = 0 :=
          fun xv y => uvp_row_zero Ξ Er mixed Vst T v hvT _
        simp only [h0, mul_zero, Finset.sum_const_zero, norm_zero]
        exact hP2
      · simp only [uvp_row_prod Ξ Er mixed Vst T v hvT x]
        by_cases hTne : T.Nonempty
        · obtain ⟨j₀, hj₀⟩ := hTne
          have hne : v ≠ j₀ := fun h => hvT (h ▸ hj₀)
          refine le_trans ((hanc L a A ha hA1 S (uvpV Ξ Er mixed Vst (some v) T) j₀ hSprof'
            ((uvp_legs hk2 hc hC ha hδ hδ1 hK (some v) T j₀).1 hj₀)
            (fun j _ x' => (uvp_legs hk2 hc hC ha hδ hδ1 hK (some v) T j).2 x')).2 v hne x) ?_
          have : 0 ≤ a * A ^ (k - 2) := by positivity
          nlinarith [mul_nonneg hD₂.le this]
        · have hT0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
          subst hT0
          by_cases hall : ∀ j, mixed j = true
          · have hΞe : ∀ xv : Fin L, ∀ y : Fin k → Fin L,
                ∏ j, (if j = v then (if xv = y j then (1 : ℂ) else 0)
                  else uvpV Ξ Er mixed Vst (some v) ∅ j (x j - y j)) =
                ∏ j, (if j = v then (if xv = y j then (1 : ℂ) else 0) else Ξ (x j - y j)) := by
              intro xv y
              refine Finset.prod_congr rfl (fun j _ => ?_)
              by_cases hj : j = v
              · simp [hj]
              · simp only [hj, ↓reduceIte]
                rw [uvp_empty_mixed Ξ Er mixed Vst (some v) j (hall j)
                  (fun h => hj (Option.some.inj h).symm)]
            simp only [hΞe]
            have hmass' := hmass hall
            refine le_trans (hrw L a δ (min (L : ℝ) (a / Real.sqrt δ)) (Real.sqrt δ / a) ha hδ hℓ
              hlam hlam2 Ξ S hΞ0 hΞs hΔ1 hΔs hΔ2 hT hSev hSprof hmass' v x) ?_
            have : 0 ≤ a * A ^ (k - 2) := by positivity
            nlinarith [mul_nonneg hC₁.le this]
          · push Not at hall
            obtain ⟨j, hj⟩ := hall
            have hj' : mixed j = false := by simpa using hj
            have hjv : j ≠ v := fun h => by rw [h] at hj'; simp [hv] at hj'
            have h0 : ∀ xv : Fin L, ∀ y : Fin k → Fin L,
                ∏ j', (if j' = v then (if xv = y j' then (1 : ℂ) else 0)
                  else uvpV Ξ Er mixed Vst (some v) ∅ j' (x j' - y j')) = 0 := by
              intro xv y
              refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
              simp only [hjv, ↓reduceIte]
              exact uvp_empty_stable Ξ Er mixed Vst (some v) j hj'
                (fun h => hjv (Option.some.inj h).symm) _
            simp only [h0, mul_zero, Finset.sum_const_zero, norm_zero]
            exact hP2
    simp only [uvp_dress_expand]
    calc ∑ xv : Fin L, ‖∑ T : Finset (Fin k), ∑ y : Fin k → Fin L,
          S y * ∏ j, uvpV Ξ Er mixed Vst (some v) T j ((Function.update x v xv) j - y j)‖
        ≤ ∑ xv : Fin L, ∑ T : Finset (Fin k), ‖∑ y : Fin k → Fin L,
          S y * ∏ j, uvpV Ξ Er mixed Vst (some v) T j ((Function.update x v xv) j - y j)‖ :=
          Finset.sum_le_sum (fun xv _ => norm_sum_le _ _)
      _ = ∑ T : Finset (Fin k), ∑ xv : Fin L, ‖∑ y : Fin k → Fin L,
          S y * ∏ j, uvpV Ξ Er mixed Vst (some v) T j ((Function.update x v xv) j - y j)‖ :=
          Finset.sum_comm
      _ ≤ ∑ _T : Finset (Fin k), (C₁ + D₂) * a * A ^ (k - 2) :=
          Finset.sum_le_sum (fun T _ => hterm T)
      _ = 2 ^ k * ((C₁ + D₂) * a * A ^ (k - 2)) := by
          rw [Finset.sum_const, hcard]; simp
      _ ≤ 2 ^ k * (C₁ + D₁ + D₂) * a * A ^ (k - 2) := by
          have : 0 ≤ a * A ^ (k - 2) := by positivity
          have h2 : (0 : ℝ) ≤ 2 ^ k := by positivity
          nlinarith [mul_nonneg h2 (mul_nonneg hD₁.le this)]

end LSBA
