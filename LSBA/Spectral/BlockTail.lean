import LSBA.Spectral.TwoSidedCounts
import LSBA.Model.Cycle

/-!
# Block tails and the count of (3.6) [eq:averaged-tail]

The block tail `min_a Σ_{‖b-a‖_L > R} Σ_α p(b, α)` of a profile and the count of (3.6)
[eq:averaged-tail]; monotonicity, a.e.-measurability and integrability for the model (1.3)
[eq:model]; and the half-mass step after (3.6) [eq:averaged-tail]: off the counted set,
`ℓ(ψ_k) ≤ W(2⌈R⌉+1)`, so `B₊`
with threshold at least `W(2⌈R⌉+1)` is at most the count.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Block tail `min_a Σ_{‖b-a‖_L > R} Σ_α p(b, α)` of (3.6) [eq:averaged-tail]. -/
def blockTail (W L : ℕ) (R : ℝ) (p : Fin L × Fin W → ℝ) : ℝ :=
  if h : 0 < L then
    (univ.image fun a : Fin L =>
      ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist a b : ℝ)), ∑ α, p (b, α)).min'
      (by simp [Finset.image_nonempty, Finset.univ_nonempty_iff]; exact ⟨⟨0, h⟩⟩)
  else 0

/-- The count of (3.6) [eq:averaged-tail]: eigenvalues in `J` whose block tail beyond radius
`R` exceeds `W^{-a}`. -/
def tailCount (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (J : Set ℝ)
    (R a : ℝ) : ℕ :=
  profCount W L A J {p | (W : ℝ) ^ (-a) < blockTail W L R p}

/-- `c` is below the block tail exactly when it is below every block-ball complement mass. -/
private lemma blockTail_lt_iff {W L : ℕ} (hL : 0 < L) (R c : ℝ) (p : Fin L × Fin W → ℝ) :
    c < blockTail W L R p ↔ ∀ a : Fin L,
      c < ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist a b : ℝ)), ∑ α, p (b, α) := by
  simp only [blockTail, hL, ↓reduceDIte, Finset.lt_min'_iff]
  simp

/-- For `L = 0` the block tail is `0`. -/
private lemma blockTail_of_not_pos {W L : ℕ} (hL : ¬ 0 < L) (R : ℝ) (p : Fin L × Fin W → ℝ) :
    blockTail W L R p = 0 := by
  simp [blockTail, hL]

/-- On nonnegative profiles the block tail is antitone in the radius. -/
private lemma blockTail_anti {W L : ℕ} {R R' : ℝ} (hR : R' ≤ R) {p : Fin L × Fin W → ℝ}
    (hp : ∀ x, 0 ≤ p x) : blockTail W L R p ≤ blockTail W L R' p := by
  by_cases hL : 0 < L
  · simp only [blockTail, hL, ↓reduceDIte]
    refine Finset.le_min' _ _ _ fun y hy => ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
    refine le_trans (Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      fun b _ _ => Finset.sum_nonneg fun α _ => hp _
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact lt_of_le_of_lt hR hb
  · rw [blockTail_of_not_pos hL, blockTail_of_not_pos hL]

private lemma blockTail_projDiag_nonneg {n : Type*} [Fintype n] (ev : n → ℝ)
    (v : n → n → ℂ) (k i : n) : 0 ≤ projDiag ev v k i :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The count of (3.6) [eq:averaged-tail] is monotone in the energy set and antitone in the
radius. -/
theorem tailCount_mono (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {J J' : Set ℝ}
    (hJ : J ⊆ J') {R R' : ℝ} (hR : R' ≤ R) (a : ℝ) :
    tailCount W L A J R a ≤ tailCount W L A J' R' a := by
  unfold tailCount profCount
  by_cases hA : A.IsHermitian
  · simp only [hA, ↓reduceDIte]
    refine Finset.card_le_card fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hk ⊢
    exact ⟨hJ hk.1, lt_of_lt_of_le hk.2 (blockTail_anti hR fun x =>
      blockTail_projDiag_nonneg _ _ _ _)⟩
  · simp [hA]

private lemma measurableSet_blockTail_lt (W L : ℕ) (R c : ℝ) :
    MeasurableSet {p : Fin L × Fin W → ℝ | c < blockTail W L R p} := by
  by_cases hL : 0 < L
  · have h : {p : Fin L × Fin W → ℝ | c < blockTail W L R p} = ⋂ a : Fin L,
        {p : Fin L × Fin W → ℝ |
          c < ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist a b : ℝ)), ∑ α, p (b, α)} := by
      ext p
      simp [blockTail_lt_iff hL]
    rw [h]
    exact MeasurableSet.iInter fun a => measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun b _ =>
        Finset.measurable_sum _ fun α _ => measurable_pi_apply (b, α))
  · have h : {p : Fin L × Fin W → ℝ | c < blockTail W L R p} = {p | c < 0} := by
      ext p
      simp [blockTail_of_not_pos hL]
    rw [h]
    exact measurableSet_lt measurable_const measurable_const

theorem aemeasurable_tailCount_Hmat (g : ℝ) (W L : ℕ) {J : Set ℝ} (hJ : MeasurableSet J)
    (R a : ℝ) : AEMeasurable (fun ω => (tailCount W L (Hmat g W L ω) J R a : ℝ)) (μ W L) := by
  exact aemeasurable_profCount_Hmat g W L hJ (measurableSet_blockTail_lt W L R _)

theorem integrable_tailCount_Hmat (g : ℝ) (W L : ℕ) {J : Set ℝ} (hJ : MeasurableSet J)
    (R a : ℝ) : Integrable (fun ω => (tailCount W L (Hmat g W L ω) J R a : ℝ)) (μ W L) := by
  have hb : ∀ A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ,
      ((tailCount W L A J R a : ℕ) : ℝ) ≤ ((L * W : ℕ) : ℝ) := fun A => by
    by_cases hA : A.IsHermitian
    · simp only [tailCount, profCount, hA, ↓reduceDIte]
      have := Finset.card_filter_le (univ : Finset (Fin L × Fin W)) fun k =>
        hA.eigenvalues k ∈ J ∧
          projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k ∈
            {p : Fin L × Fin W → ℝ | (W : ℝ) ^ (-a) < blockTail W L R p}
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
      exact_mod_cast this
    · simp only [tailCount, profCount, hA, ↓reduceDIte, Nat.cast_zero]
      exact Nat.cast_nonneg _
  refine Integrable.of_bound (aemeasurable_tailCount_Hmat g W L hJ R a).aestronglyMeasurable
    ((L * W : ℕ) : ℝ) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact hb _

/-- Residue of `x - y` modulo `L` for `x, y < L`, as a case split. -/
private lemma blockTail_cyc_mod (x y L : ℕ) (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have h1 : x + L - y = (x - y) + L := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- A cyclic block ball of radius `m` around `a`, with `2m + 1 < L`, lies in the `2m + 1` blocks
starting at `a - m`. -/
private lemma blockTail_ball_shift (L m a b : ℕ) (ha : a < L) (hb : b < L) (hm : 2 * m + 1 < L)
    (h : (a + L - b) % L ≤ m ∨ (b + L - a) % L ≤ m) :
    (b + L - (a + L - m) % L) % L ≤ 2 * m := by
  have hs : (a + L - m) % L < L := Nat.mod_lt _ (by omega)
  rw [blockTail_cyc_mod b _ L hb hs, blockTail_cyc_mod a m L ha (by omega)]
  rw [blockTail_cyc_mod a b L ha hb, blockTail_cyc_mod b a L hb ha] at h
  split_ifs at h ⊢ <;> omega

/-- Coordinates `α + W b` of the block `b`, read from the coordinate `W s` modulo `L W`. -/
private lemma blockTail_coord_mod (W L α b s : ℕ) (hα : α < W) (hb : b < L) (hs : s < L) :
    (α + W * b + L * W - W * s) % (L * W) = α + W * ((b + L - s) % L) := by
  have hL : 0 < L := by omega
  have h1 : L * ((b + L - s) / L) + (b + L - s) % L = b + L - s := Nat.div_add_mod _ _
  have hdL : (b + L - s) % L < L := Nat.mod_lt _ hL
  set d := (b + L - s) % L with hd
  set q := (b + L - s) / L with hq
  have h2 : W * (L * q + d + s) = W * (b + L) := by
    have : L * q + d + s = b + L := by omega
    rw [this]
  have h4 : α + W * b + L * W = (α + W * d) + (L * W) * q + W * s := by nlinarith [h2]
  have h5 : α + W * b + L * W - W * s = (α + W * d) + (L * W) * q := by omega
  have h6 : W * (d + 1) ≤ W * L := Nat.mul_le_mul_left W hdL
  have h7 : W * (d + 1) = W * d + W := Nat.mul_succ W d
  rw [h5, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have := Nat.mul_comm L W
  omega

/-- If the block ball of radius `m` around some block carries mass at least `1/2` of a
nonnegative profile, then its length is at most `W(2m + 1)`. -/
private lemma blockTail_ellProf_le (W L m : ℕ) (p : Fin L × Fin W → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (a₀ : Fin L)
    (hball : (1 : ℝ) / 2 ≤ ∑ b ∈ univ.filter (fun b : Fin L => cycDist a₀ b ≤ m), ∑ α, p (b, α)) :
    ellProf W L p ≤ W * (2 * m + 1) := by
  by_cases hcase : L ≤ 2 * m + 1 ∨ W = 0
  · have h := ellMass_le (L * W) (fun i => p (finProdFinEquiv.symm i))
    unfold ellProf
    rcases hcase with h' | h'
    · calc _ ≤ L * W := h
        _ ≤ (2 * m + 1) * W := Nat.mul_le_mul_right _ h'
        _ = _ := Nat.mul_comm _ _
    · subst h'
      simpa using h
  · push Not at hcase
    obtain ⟨hLm, hW⟩ := hcase
    have hW' : 0 < W := Nat.pos_of_ne_zero hW
    have hsL : (a₀.val + L - m) % L < L := Nat.mod_lt _ (by omega)
    set s : ℕ := (a₀.val + L - m) % L with hs
    set x : Fin (L * W) := finProdFinEquiv (⟨s, hsL⟩, ⟨0, hW'⟩) with hx
    have hxv : x.val = W * s := by simp [hx, finProdFinEquiv]
    set T : Finset (Fin L × Fin W) :=
      (univ.filter fun b : Fin L => cycDist a₀ b ≤ m) ×ˢ univ with hT
    have hsub : T.map finProdFinEquiv.toEmbedding ⊆ cycInterval (L * W) x (W * (2 * m + 1)) := by
      intro i hi
      obtain ⟨⟨b, α⟩, hbα, rfl⟩ := Finset.mem_map.mp hi
      simp only [hT, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
        and_true] at hbα
      simp only [cycInterval, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.coe_toEmbedding, finProdFinEquiv_apply_val, hxv]
      rw [blockTail_coord_mod W L α b s α.isLt b.isLt hsL]
      have hd : (b.val + L - s) % L ≤ 2 * m :=
        blockTail_ball_shift L m a₀.val b.val a₀.isLt b.isLt hLm
          (by simpa [cycDist, min_le_iff] using hbα)
      have h1 := α.isLt
      have h2 : W * ((b.val + L - s) % L) ≤ W * (2 * m) := Nat.mul_le_mul_left W hd
      have h3 : W * (2 * m + 1) = W * (2 * m) + W := Nat.mul_succ W (2 * m)
      omega
    have hmass : (1 : ℝ) / 2 ≤
        ∑ i ∈ cycInterval (L * W) x (W * (2 * m + 1)), p (finProdFinEquiv.symm i) := by
      calc (1 : ℝ) / 2 ≤ ∑ b ∈ univ.filter (fun b : Fin L => cycDist a₀ b ≤ m), ∑ α, p (b, α) :=
            hball
        _ = ∑ q ∈ T, p q := by rw [hT, Finset.sum_product]
        _ = ∑ i ∈ T.map finProdFinEquiv.toEmbedding, p (finProdFinEquiv.symm i) := by
            rw [Finset.sum_map]
            simp
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hp0 _
    exact ellMass_le_of_mass _ x (Nat.one_le_iff_ne_zero.mpr (by positivity))
      (by nlinarith [Nat.mul_comm L W]) hmass

private lemma blockTail_mult_eq_one {m : Type*} [Fintype m] {ev : m → ℝ}
    (hinj : Function.Injective ev) (k : m) : mult ev k = 1 := by
  unfold mult
  rw [Finset.card_eq_one]
  exact ⟨k, by ext j; simp [hinj.eq_iff]⟩

/-- Off the counted set of (3.6) [eq:averaged-tail], `ℓ(ψ_k) ≤ W(2⌈R⌉+1)` when
`W^{-a} ≤ 1/2`: so `B₊` with threshold `r ≥ W(2⌈R⌉+1)` is at most the count of (3.6)
[eq:averaged-tail]. -/
theorem badCountUp_le_tailCount (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hA : A.IsHermitian) (hinj : Function.Injective hA.eigenvalues) (J : Set ℝ) {R r a : ℝ}
    (hR : 0 ≤ R) (hr : (W : ℝ) * (2 * ⌈R⌉ + 1) ≤ r) (ha : (W : ℝ) ^ (-a) ≤ 1 / 2) :
    badCountUp W L A J r ≤ tailCount W L A J R a := by
  unfold badCountUp tailCount profCount
  simp only [hA, ↓reduceDIte]
  refine Finset.card_le_card fun k hk => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hk ⊢
  refine ⟨hk.1, ?_⟩
  have hm : mult hA.eigenvalues k = 1 := blockTail_mult_eq_one hinj k
  have hp : projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k =
      fun i => ‖(hA.eigenvectorBasis k) i‖ ^ 2 :=
    funext fun i => projDiag_of_mult_eq_one _ _ hm i
  rw [hp]
  rw [hp] at hk
  have hr' := hk.2.resolve_left (by omega)
  by_contra hcon
  set p : Fin L × Fin W → ℝ := fun i => ‖(hA.eigenvectorBasis k) i‖ ^ 2 with hpdef
  have hp0 : ∀ x, 0 ≤ p x := fun x => by positivity
  have htot : ∑ b, ∑ α, p (b, α) = 1 := by
    rw [← Fintype.sum_prod_type (fun x : Fin L × Fin W => p x), hpdef]
    simp only
    rw [← EuclideanSpace.norm_sq_eq, OrthonormalBasis.norm_eq_one, one_pow]
  have hL : 0 < L := k.1.pos
  rw [blockTail_lt_iff hL] at hcon
  push Not at hcon
  obtain ⟨a₀, ha₀⟩ := hcon
  set m : ℕ := ⌈R⌉.toNat with hmdef
  have hmZ : ((m : ℕ) : ℤ) = ⌈R⌉ := Int.toNat_of_nonneg (Int.ceil_nonneg hR)
  have hmR : (m : ℝ) = (⌈R⌉ : ℝ) := by
    rw [← hmZ, Int.cast_natCast]
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin L))
    (fun b : Fin L => R < (cycDist a₀ b : ℝ)) (fun b => ∑ α, p (b, α))
  have hball : (1 : ℝ) / 2 ≤
      ∑ b ∈ univ.filter (fun b : Fin L => cycDist a₀ b ≤ m), ∑ α, p (b, α) := by
    calc (1 : ℝ) / 2 ≤
        ∑ b ∈ univ.filter (fun b : Fin L => ¬ R < (cycDist a₀ b : ℝ)), ∑ α, p (b, α) := by
          linarith
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => ?_)
            fun b _ _ => Finset.sum_nonneg fun α _ => hp0 _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hb ⊢
          exact_mod_cast hb.trans (Int.le_ceil R |>.trans_eq hmR.symm)
  have hell : (ellProf W L p : ℝ) ≤ W * (2 * m + 1) := by
    exact_mod_cast blockTail_ellProf_le W L m p hp0 a₀ hball
  rw [hmR] at hell
  linarith

end LSBA
