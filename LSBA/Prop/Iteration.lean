import LSBA.Prop.OneStep
import LSBA.Prop.Schedule

/-!
# Theorem 5.12 [gc:thm:common], iterated

Theorem 5.12 [gc:thm:common] (ii) in general form: by strong induction over the steps of the
schedule, the input (5.22) [gc:eq:one-step-input] at every `u ∈ [1/2, t_*]` from the input at time
`1/2` on the reach, with
`θ_* = 2^{-J-1}`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Operations on the one-step input -/

/-- Pullback of a domination along a map of parameter families. -/
private lemma iteration_precMax_pull {ι₁ ι₂ : Type*} {vol : ι₁ → ℕ} {D₁ : ℕ → Set ι₁}
    {D₂ : ℕ → Set ι₂} {Λ : ℕ → ι₁ → Type*}
    {X : (W : ℕ) → (p : ι₁) → Λ W p → Ω W (vol p) → ℂ} {Y : (W : ℕ) → (p : ι₁) → Λ W p → ℝ}
    (σ : ι₂ → ι₁) (h : PrecMax vol D₁ X Y)
    (hD : ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ x ∈ D₂ W, σ x ∈ D₁ W) :
    PrecMax (fun x => vol (σ x)) D₂ (Λ := fun W x => Λ W (σ x)) (fun W x l ω => X W (σ x) l ω)
      (fun W x l => Y W (σ x) l) := by
  intro ε D hε hD'
  obtain ⟨W₁, hW₁⟩ := hD
  obtain ⟨W₀, hW⟩ := h ε D hε hD'
  exact ⟨max W₀ W₁, fun W hW0 x hx => hW W (le_trans (le_max_left _ _) hW0) (σ x)
    (hW₁ W (le_trans (le_max_right _ _) hW0) x hx)⟩

/-- Union of two families for the same domination. -/
private lemma iteration_precMax_union {ι : Type*} {vol : ι → ℕ} {D₁ D₂ : ℕ → Set ι}
    {Λ : ℕ → ι → Type*} {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ}
    {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ} (h₁ : PrecMax vol D₁ X Y) (h₂ : PrecMax vol D₂ X Y) :
    PrecMax vol (fun W => D₁ W ∪ D₂ W) X Y := by
  intro ε D hε hD
  obtain ⟨W₁, hW₁⟩ := h₁ ε D hε hD
  obtain ⟨W₂, hW₂⟩ := h₂ ε D hε hD
  refine ⟨max W₁ W₂, fun W hW p hp => ?_⟩
  rcases hp with hp | hp
  · exact hW₁ W (le_trans (le_max_left _ _) hW) p hp
  · exact hW₂ W (le_trans (le_max_right _ _) hW) p hp

/-- A bound `Y ≤ C Y'` on the family with `Y' ≥ 0` for large `W` transfers a domination by `Y` to
one by `Y'`: the constant `C` is absorbed in `W^ε`. -/
private lemma iteration_precMax_mul_const {ι : Type*} {vol : ι → ℕ} {D : ℕ → Set ι}
    {Λ : ℕ → ι → Type*} {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ}
    {Y Y' : (W : ℕ) → (p : ι) → Λ W p → ℝ} (C : ℝ) (h : PrecMax vol D X Y)
    (hY : ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ p ∈ D W, ∀ l, 0 ≤ Y' W p l ∧ Y W p l ≤ C * Y' W p l) :
    PrecMax vol D X Y' := by
  intro ε D' hε hD'
  obtain ⟨W₁, hW₁⟩ := hY
  obtain ⟨W₀, hW₀⟩ := h (ε / 2) D' (by positivity) hD'
  have ht : Tendsto (fun W : ℕ => (W : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  obtain ⟨W₂, hW₂⟩ := eventually_atTop.mp (ht.eventually_ge_atTop C)
  refine ⟨max W₀ (max W₁ (max W₂ 1)), fun W hW p hp => (measure_mono ?_).trans
    (hW₀ W (le_trans (le_max_left _ _) hW) p hp)⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW2 : W₂ ≤ W :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hW
  have hW3 : 1 ≤ W :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hW
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW3
  rintro ω ⟨l, hl⟩
  refine ⟨l, ?_⟩
  obtain ⟨hY0, hYC⟩ := hW₁ W hW1 p hp l
  have hW0 : (0 : ℝ) ≤ (W : ℝ) ^ (ε / 2) := Real.rpow_nonneg hWpos.le _
  have hsq : (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) = (W : ℝ) ^ ε := by
    rw [← Real.rpow_add hWpos]; congr 1; ring
  calc (W : ℝ) ^ (ε / 2) * Y W p l ≤ (W : ℝ) ^ (ε / 2) * (C * Y' W p l) :=
        mul_le_mul_of_nonneg_left hYC hW0
    _ ≤ (W : ℝ) ^ (ε / 2) * ((W : ℝ) ^ (ε / 2) * Y' W p l) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hW₂ W hW2) hY0) hW0
    _ = (W : ℝ) ^ ε * Y' W p l := by rw [← mul_assoc, hsq]
    _ < ‖X W p l ω‖ := hl

/-- Pullback of the one-step input from a family of flow points along a map `σ` of parameter
families. -/
private lemma iteration_pull {cp θ : ℝ} {ι : Type*} (σ : ι → FlowPt) {D₁ : ℕ → Set FlowPt}
    {D₂ : ℕ → Set ι} (h : OneStepInput cp θ (id : FlowPt → FlowPt) D₁)
    (hD : ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ x ∈ D₂ W, σ x ∈ D₁ W) : OneStepInput cp θ σ D₂ :=
  ⟨fun k hk => iteration_precMax_pull σ (h.loop k hk) hD,
    fun k hk => iteration_precMax_pull σ (h.err k hk) hD,
    iteration_precMax_pull σ h.avg hD, iteration_precMax_pull σ h.entry hD,
    fun F hF => iteration_precMax_pull σ (h.pair F hF) hD,
    fun k hk ε A hε hA => iteration_precMax_pull σ (h.tail k hk ε A hε hA) hD⟩

/-- Pushforward of the one-step input to the image family. -/
private lemma iteration_push {cp θ : ℝ} {ι : Type*} {pt : ι → FlowPt} {D : ℕ → Set ι}
    (h : OneStepInput cp θ pt D) :
    OneStepInput cp θ (id : FlowPt → FlowPt) (fun W => pt '' D W) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_, fun F hF => ?_, fun k hk ε A hε hA => ?_⟩
  · intro ε' D' hε' hD'
    obtain ⟨W₀, hW⟩ := h.loop k hk ε' D' hε' hD'
    refine ⟨W₀, fun W hW0 x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := hx
    exact hW W hW0 i hi
  · intro ε' D' hε' hD'
    obtain ⟨W₀, hW⟩ := h.err k hk ε' D' hε' hD'
    refine ⟨W₀, fun W hW0 x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := hx
    exact hW W hW0 i hi
  · intro ε' D' hε' hD'
    obtain ⟨W₀, hW⟩ := h.avg ε' D' hε' hD'
    refine ⟨W₀, fun W hW0 x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := hx
    exact hW W hW0 i hi
  · intro ε' D' hε' hD'
    obtain ⟨W₀, hW⟩ := h.entry ε' D' hε' hD'
    refine ⟨W₀, fun W hW0 x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := hx
    exact hW W hW0 i hi
  · intro ε' D' hε' hD'
    obtain ⟨W₀, hW⟩ := h.pair F hF ε' D' hε' hD'
    refine ⟨W₀, fun W hW0 x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := hx
    exact hW W hW0 i hi
  · intro ε' D' hε' hD'
    obtain ⟨W₀, hW⟩ := h.tail k hk ε A hε hA ε' D' hε' hD'
    refine ⟨W₀, fun W hW0 x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := hx
    exact hW W hW0 i hi

/-- Union of two families for the same profile constants. -/
private lemma iteration_union {cp θ : ℝ} {D₁ D₂ : ℕ → Set FlowPt}
    (h₁ : OneStepInput cp θ (id : FlowPt → FlowPt) D₁)
    (h₂ : OneStepInput cp θ (id : FlowPt → FlowPt) D₂) :
    OneStepInput cp θ (id : FlowPt → FlowPt) (fun W => D₁ W ∪ D₂ W) :=
  ⟨fun k hk => iteration_precMax_union (h₁.loop k hk) (h₂.loop k hk),
    fun k hk => iteration_precMax_union (h₁.err k hk) (h₂.err k hk),
    iteration_precMax_union h₁.avg h₂.avg, iteration_precMax_union h₁.entry h₂.entry,
    fun F hF => iteration_precMax_union (h₁.pair F hF) (h₂.pair F hF),
    fun k hk ε A hε hA => iteration_precMax_union (h₁.tail k hk ε A hε hA) (h₂.tail k hk ε A hε hA)⟩

/-- The weight `exp(-c_p (r/ℓ)^θ) + W^{-F}` for `(c_p, θ)` is at most `e^{c_p'}` times the weight
for `c_p' ≤ c_p`, `θ' ≤ θ`, for `r/ℓ ≥ 0`. -/
private lemma iteration_weightFn_le (cp θ cp' θ' F : ℝ) (W : ℕ) (ℓ r : ℝ) (hcp' : 0 ≤ cp')
    (hcp : cp' ≤ cp) (hθ' : 0 < θ') (hθ : θ' ≤ θ) (hx : 0 ≤ r / ℓ) :
    weightFn cp θ F W ℓ r ≤ Real.exp cp' * weightFn cp' θ' F W ℓ r := by
  unfold weightFn
  set x := r / ℓ with hxdef
  have hcp0 : 0 ≤ cp := hcp'.trans hcp
  have hxθ : 0 ≤ x ^ θ := Real.rpow_nonneg hx _
  have hxθ' : 0 ≤ x ^ θ' := Real.rpow_nonneg hx _
  have h1 : cp' * x ^ θ' ≤ cp' + cp * x ^ θ := by
    rcases le_total x 1 with h | h
    · have : x ^ θ' ≤ 1 := Real.rpow_le_one hx h hθ'.le
      nlinarith [mul_nonneg hcp0 hxθ]
    · have h2 : x ^ θ' ≤ x ^ θ := Real.rpow_le_rpow_of_exponent_le h hθ
      nlinarith [mul_le_mul hcp h2 hxθ' hcp0]
  have h2 : Real.exp (-(cp * x ^ θ)) ≤ Real.exp cp' * Real.exp (-(cp' * x ^ θ')) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h3 : (1 : ℝ) ≤ Real.exp cp' := Real.one_le_exp hcp'
  have h4 : 0 ≤ (W : ℝ) ^ (-F) := Real.rpow_nonneg (Nat.cast_nonneg W) _
  nlinarith

/-- Weakening of the profile constants in the one-step input: `(c_p, θ)` to `(c_p', θ')` with
`c_p' ≤ c_p`, `θ' ≤ θ`, on a family with nonnegative coupling for large `W`. -/
private lemma iteration_weaken {cp θ cp' θ' : ℝ} {D : ℕ → Set FlowPt}
    (h : OneStepInput cp θ (id : FlowPt → FlowPt) D) (hcp' : 0 < cp') (hcp : cp' ≤ cp)
    (hθ' : 0 < θ') (hθ : θ' ≤ θ) (hg : ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ x ∈ D W, 0 ≤ x.g) :
    OneStepInput cp' θ' (id : FlowPt → FlowPt) D := by
  refine ⟨h.loop, h.err, h.avg, h.entry, fun F hF => ?_, h.tail⟩
  obtain ⟨W₁, hW₁⟩ := hg
  refine iteration_precMax_mul_const (Real.exp cp') (h.pair F hF) ⟨W₁, fun W hW x hx l => ?_⟩
  have hg0 : 0 ≤ x.g := hW₁ W hW x hx
  have hell : 0 ≤ flowEll (id x) := by
    unfold flowEll ellProp
    refine le_min (Nat.cast_nonneg _) ?_
    have : 0 ≤ x.g / Real.sqrt (gammaG x.g * (1 - x.u)) :=
      div_nonneg hg0 (Real.sqrt_nonneg _)
    change 0 ≤ 1 + x.g / Real.sqrt (gammaG x.g * (1 - x.u))
    linarith
  have hr : 0 ≤ ((cycDist l.1 l.2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hwf := iteration_weightFn_le cp θ cp' θ' F W (flowEll (id x))
    ((cycDist l.1 l.2 : ℕ) : ℝ) hcp'.le hcp hθ' hθ (div_nonneg hr hell)
  have hW' : 0 ≤ weightFn cp' θ' F W (flowEll (id x)) ((cycDist l.1 l.2 : ℕ) : ℝ) := by
    unfold weightFn
    exact add_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (Nat.cast_nonneg W) _)
  have hz2 : 0 ≤ flowZeta W (id x) ^ 2 := sq_nonneg _
  refine ⟨mul_nonneg hz2 hW', ?_⟩
  calc flowZeta W (id x) ^ 2 * weightFn cp θ F W (flowEll (id x)) ((cycDist l.1 l.2 : ℕ) : ℝ)
      ≤ flowZeta W (id x) ^ 2 * (Real.exp cp' *
          weightFn cp' θ' F W (flowEll (id x)) ((cycDist l.1 l.2 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hwf hz2
    _ = _ := by ring

/-! ### The exponents and the domains of the induction -/

/-- The exponent `θ_j = 2^{-(j+1)}` after `j` steps, `θ_0 = 1/2`. -/
private def iterTheta (j : ℕ) : ℝ := (2 : ℝ) ^ (-((j : ℝ) + 1))

private lemma iterTheta_zero : iterTheta 0 = 1 / 2 := by
  unfold iterTheta
  rw [Nat.cast_zero, zero_add, Real.rpow_neg (by norm_num), Real.rpow_one]
  norm_num

private lemma iterTheta_pos (j : ℕ) : 0 < iterTheta j := Real.rpow_pos_of_pos (by norm_num) _

private lemma iterTheta_le (j : ℕ) : iterTheta j ≤ 1 / 2 := by
  unfold iterTheta
  have h : (2 : ℝ) ^ (-((j : ℝ) + 1)) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  rw [Real.rpow_neg_one] at h
  linarith

private lemma iterTheta_succ (j : ℕ) : iterTheta j / 2 = iterTheta (j + 1) := by
  unfold iterTheta
  push_cast
  rw [show -((j : ℝ) + 1 + 1) = -((j : ℝ) + 1) + (-1 : ℝ) by ring,
    Real.rpow_add (by norm_num), Real.rpow_neg_one]
  ring

/-- The points of the induction at step `j` in the proof of Theorem 5.12(ii) [gc:thm:common]
(Appendix C.4 [sec:gc-schedule]): time restrictions `v ∈ [1/2, s_j(t)]` of the points `p` reached
with depth `e` and `e + j ≤ J`, on which `ζ_t ≤ W^{-c₀}`, with `s_j` the schedule (C.47)′
[gc:eq:finite-schedule] of `t = p.u`. -/
private def iterDom (R : PropRegime) (c₀ N : ℝ) (j : ℕ) (W : ℕ) : Set FlowPt :=
  {x | ∃ (e : ℕ) (p : FlowPt), CmpReach R.base W e p ∧ e + j ≤ R.J ∧
    zetaProp p.g W p.L p.u ≤ (W : ℝ) ^ (-c₀) ∧
    ∃ v : ℝ, 1 / 2 ≤ v ∧ v ≤ schedTime W c₀ N p.u j ∧ x = ⟨p.g, p.E, p.L, v⟩}

/-- The step points of the induction from step `j` to step `j + 1` (Appendix C.4
[sec:gc-schedule]): the intervals `[s_j(t), s_{j+1}(t)]` of reached points `p` with
`e + j + 1 ≤ J`, `t = p.u`, admissible with `c = 3c₀/4`. -/
private def iterStep (R : PropRegime) (c₀ N : ℝ) (j : ℕ) (W : ℕ) : Set StepPt :=
  {q | StepAdm R (3 * c₀ / 4) N W q ∧ ∃ (e : ℕ) (p : FlowPt) (u : ℝ), CmpReach R.base W e p ∧
    e + (j + 1) ≤ R.J ∧ zetaProp p.g W p.L p.u ≤ (W : ℝ) ^ (-c₀) ∧
    q = ⟨p.g, p.E, p.L, schedTime W c₀ N p.u j, schedTime W c₀ N p.u (j + 1), u⟩}

/-! ### Facts on the reach -/

/-- Reached points have `1/2 ≤ u` and `W^{-3} ≤ 1 - u`. -/
private lemma iteration_reach_time (R : PropRegime) {W : ℕ} {d : ℕ} {p : FlowPt}
    (h : CmpReach R.base W d p) : 1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u := by
  induction h with
  | base hp => exact R.time W _ hp
  | earlier v h hv1 hv2 ih =>
    refine ⟨hv1, ?_⟩
    change _ ≤ 1 - v
    linarith [ih.2]
  | cmp s h hs hsu ih =>
    refine ⟨hs, ?_⟩
    change _ ≤ 1 - s
    linarith [ih.2]
  | lift h ih => exact ih

/-- A threshold `W₀ ≥ 2` beyond which all points reached with depth at most `J` have `g ≥ 0`,
`L ≥ 1`. -/
private lemma iteration_good (R : PropRegime) : ∃ W₀ : ℕ, 2 ≤ W₀ ∧ ∀ W : ℕ, W₀ ≤ W →
    ∀ (e : ℕ) (p : FlowPt), e ≤ R.J → CmpReach R.base W e p → 0 ≤ p.g ∧ 1 ≤ p.L := by
  obtain ⟨W₀, h⟩ := R.dyson
  refine ⟨max W₀ 2, le_max_right _ _, fun W hW e p he hr => ?_⟩
  obtain ⟨hL, hg, -⟩ := h W (le_trans (le_max_left _ _) hW) e p he hr
  exact ⟨hg, by omega⟩

/-! ### The schedule along a reached point -/

/-- The schedule facts used at a reached point `(g, L, t)`: `s_j ≥ 1/2` for `j ≤ J`, `s_J = t`, and
for each step `s_j ≤ s_{j+1} ≤ t` with `R^N ζ_{s_{j+1}} ≤ W^{-3c₀/4}`. -/
private def IterSched (W : ℕ) (c₀ N t g : ℝ) (L : ℕ) : Prop :=
  (∀ j : ℕ, j ≤ schedSteps c₀ N → 1 / 2 ≤ schedTime W c₀ N t j) ∧
  schedTime W c₀ N t (schedSteps c₀ N) = t ∧
  ∀ j : ℕ, j + 1 ≤ schedSteps c₀ N →
    schedTime W c₀ N t j ≤ schedTime W c₀ N t (j + 1) ∧ schedTime W c₀ N t (j + 1) ≤ t ∧
    ((1 - schedTime W c₀ N t j) / (1 - schedTime W c₀ N t (j + 1))) ^ N *
      zetaProp g W L (schedTime W c₀ N t (j + 1)) ≤ (W : ℝ) ^ (-(3 * c₀ / 4))

private lemma iteration_sched (W : ℕ) (hW : 2 ≤ W) (c₀ N t g : ℝ) (L : ℕ) (hc₀ : 0 < c₀)
    (hN : 20 ≤ N) (ht₁ : 1 / 2 ≤ t) (ht₂ : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - t) (hg : 0 ≤ g) (hL : 1 ≤ L)
    (hz : zetaProp g W L t ≤ (W : ℝ) ^ (-c₀)) : IterSched W c₀ N t g L := by
  obtain ⟨h0, hJ, hstep⟩ := schedTime_step W hW c₀ N t hc₀ hN ht₁ ht₂ g hg L hL hz
  refine ⟨?_, hJ, fun j hj => ?_⟩
  · intro j
    induction j with
    | zero => intro _; rw [h0]
    | succ m ih =>
      intro hm
      have := (hstep (m + 1) (Nat.succ_pos m) hm).1
      simp only [Nat.add_sub_cancel] at this
      exact le_trans (ih (by omega)) this
  · have := hstep (j + 1) (Nat.succ_pos j) hj
    simp only [Nat.add_sub_cancel] at this
    exact ⟨this.1, this.2.1, this.2.2.2⟩

/-- At time `1/2` the schedule starts at `1/2`. -/
private lemma iteration_sched_zero (W : ℕ) (c₀ N t : ℝ) (ht : 1 / 2 ≤ t) :
    schedTime W c₀ N t 0 = 1 / 2 := by
  unfold schedTime
  simp only [Nat.cast_zero, zero_mul, zero_div, neg_zero, Real.rpow_zero]
  rw [max_eq_right (by linarith)]
  norm_num

/-! ### One step of the induction -/

private lemma iteration_step (R : PropRegime) (I : PropInputs R.base R.J) (c₀ N : ℝ)
    (hc₀ : 0 < c₀) (hN : lemmaNN0 I.Cw ≤ N) (hinc : IncrementInput R.base R.J) (j : ℕ)
    (hj : j + 1 ≤ schedSteps c₀ N) (cp : ℝ) (hcp : 0 < cp) :
    ∃ cp'' : ℝ, 0 < cp'' ∧
      (OneStepInput cp (iterTheta j) (id : FlowPt → FlowPt) (iterDom R c₀ N j) →
        OneStepInput cp'' (iterTheta (j + 1)) (id : FlowPt → FlowPt) (iterDom R c₀ N (j + 1))) := by
  have hN20 : (20 : ℝ) ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : 0 < N := by linarith
  obtain ⟨Wg, hWg2, hgood⟩ := iteration_good R
  obtain ⟨cp', hcp', hone⟩ := theorem412_one R I (3 * c₀ / 4) cp (iterTheta j) N (by positivity)
    hcp (iterTheta_pos j) (iterTheta_le j) hN hinc
  refine ⟨min cp' cp, lt_min hcp' hcp, fun hQ => ?_⟩
  -- admissibility and closure of the step points
  have hSadm : ∀ W, iterStep R c₀ N j W ⊆ {q | StepAdm R (3 * c₀ / 4) N W q} :=
    fun W q hq => hq.1
  have hSclosed : ∀ W, ∀ q ∈ iterStep R c₀ N j W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
      (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ iterStep R c₀ N j W := by
    intro W q hq v hsv hvu
    obtain ⟨hadm, e, p, u, hr, he, hz, rfl⟩ := hq
    obtain ⟨hend, h1, h2, h3, h4, h5, h6⟩ := hadm
    exact ⟨⟨hend, h1, hsv, le_trans hvu h3, h4, h5, h6⟩, e, p, v, hr, he, hz, rfl⟩
  -- the input at the start point
  have hA : OneStepInput cp (iterTheta j) (fun q : StepPt => q.at q.s) (iterStep R c₀ N j) := by
    refine iteration_pull (fun q : StepPt => q.at q.s) hQ ⟨0, fun W _ q hq => ?_⟩
    obtain ⟨hadm, e, p, u, hr, he, hz, rfl⟩ := hq
    exact ⟨e, p, hr, by omega, hz, schedTime W c₀ N p.u j, hadm.2.1, le_rfl, rfl⟩
  -- the input at the comparison point
  have hB : OneStepInput cp (iterTheta j) (fun q : StepPt => cmpPt (q.at q.u) q.s)
      (iterStep R c₀ N j) := by
    refine iteration_pull (fun q : StepPt => cmpPt (q.at q.u) q.s) hQ ⟨Wg, fun W hW q hq => ?_⟩
    obtain ⟨hadm, e, p, u, hr, he, hz, rfl⟩ := hq
    have hW2 : 2 ≤ W := le_trans hWg2 hW
    have hW1 : 1 ≤ W := by omega
    obtain ⟨hg0, hL1⟩ := hgood W hW e p (by omega) hr
    obtain ⟨hp1, hp2⟩ := iteration_reach_time R hr
    have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
    have hsched := iteration_sched W hW2 c₀ N p.u p.g p.L hc₀ hN20 hp1 hp2 hg0 hL1 hz
    obtain ⟨-, h12, hsu, hut, -, -, -⟩ := hadm
    have hup : u ≤ p.u := le_trans hut (hsched.2.2 j hj).2.1
    have hpos3 : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hWpos _
    have hp1' : p.u < 1 := by linarith
    have hu1 : u < 1 := lt_of_le_of_lt hup hp1'
    have hreach : CmpReach R.base W (e + 1)
        (cmpPt (⟨p.g, p.E, p.L, u⟩ : FlowPt) (schedTime W c₀ N p.u j)) :=
      CmpReach.cmp _ (CmpReach.earlier u hr (le_trans h12 hsu) hup) h12 hsu
    refine ⟨e + 1, cmpPt (⟨p.g, p.E, p.L, u⟩ : FlowPt) (schedTime W c₀ N p.u j), hreach,
      by omega, ?_, schedTime W c₀ N p.u j, h12, ?_, rfl⟩
    · calc zetaProp (cmpPt (⟨p.g, p.E, p.L, u⟩ : FlowPt) (schedTime W c₀ N p.u j)).g W p.L
            (schedTime W c₀ N p.u j)
          ≤ zetaProp p.g W p.L u :=
            (zeta_cmp_le p.g hg0 W p.L hW1 hL1 (schedTime W c₀ N p.u j) u h12 hsu hu1).1
        _ ≤ zetaProp p.g W p.L p.u :=
            (scale_facts p.g hg0 W p.L hW1 hL1 u p.u (by linarith) hup hp1').2.2.2.2.1
        _ ≤ (W : ℝ) ^ (-c₀) := hz
    · have := schedTime_prefix W hW1 c₀ N p.u hc₀ hN0 j j
      rw [min_self] at this
      exact this.ge
  -- the output of the one step
  have hout := hone (iterStep R c₀ N j) hSadm hSclosed hA hB
  rw [iterTheta_succ] at hout
  have hpush := iteration_push hout
  -- weakening to the common constants
  have hgD : ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ x ∈ iterDom R c₀ N j W, 0 ≤ x.g := by
    refine ⟨Wg, fun W hW x hx => ?_⟩
    obtain ⟨e, p, hr, he, hz, v, -, -, rfl⟩ := hx
    exact (hgood W hW e p (by omega) hr).1
  have hgS : ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W →
      ∀ x ∈ (fun q : StepPt => q.at q.u) '' iterStep R c₀ N j W, 0 ≤ x.g := by
    refine ⟨Wg, fun W hW x hx => ?_⟩
    obtain ⟨q, ⟨hadm, e, p, u, hr, he, hz, rfl⟩, rfl⟩ := hx
    exact (hgood W hW e p (by omega) hr).1
  have hθle : iterTheta (j + 1) ≤ iterTheta j := by
    rw [← iterTheta_succ]; linarith [iterTheta_pos j]
  have hw1 := iteration_weaken hQ (lt_min hcp' hcp) (min_le_right _ _) (iterTheta_pos (j + 1))
    hθle hgD
  have hw2 := iteration_weaken hpush (lt_min hcp' hcp) (min_le_left _ _) (iterTheta_pos (j + 1))
    le_rfl hgS
  have hun := iteration_union hw1 hw2
  -- the new domain is covered
  refine iteration_pull (id : FlowPt → FlowPt) hun ⟨Wg, fun W hW x hx => ?_⟩
  obtain ⟨e, p, hr, he, hz, v, hv1, hv2, rfl⟩ := hx
  by_cases hcase : v ≤ schedTime W c₀ N p.u j
  · left
    exact ⟨e, p, hr, by omega, hz, v, hv1, hcase, rfl⟩
  · right
    rw [not_le] at hcase
    have hW2 : 2 ≤ W := le_trans hWg2 hW
    have hW1 : 1 ≤ W := by omega
    obtain ⟨hg0, hL1⟩ := hgood W hW e p (by omega) hr
    obtain ⟨hp1, hp2⟩ := iteration_reach_time R hr
    have hsched := iteration_sched W hW2 c₀ N p.u p.g p.L hc₀ hN20 hp1 hp2 hg0 hL1 hz
    obtain ⟨hhalf, -, hstepj⟩ := hsched
    obtain ⟨hmono, hle, hprod⟩ := hstepj j hj
    refine ⟨⟨p.g, p.E, p.L, schedTime W c₀ N p.u j, schedTime W c₀ N p.u (j + 1), v⟩,
      ⟨⟨⟨e, by omega, CmpReach.earlier (schedTime W c₀ N p.u (j + 1)) hr
        (le_trans hv1 hv2) hle⟩, hhalf j (by omega), hcase.le, hv2, lt_of_lt_of_le hcase hv2,
        ?_, hprod⟩, e, p, v, hr, he, hz, rfl⟩, rfl⟩
    change (W : ℝ) ^ (-3 : ℝ) ≤ 1 - schedTime W c₀ N p.u (j + 1)
    linarith

/-- Theorem 5.12(ii) [gc:thm:common], general form at fixed times: in a regime of
depth `J ≥ ⌈12N/c₀⌉ + 1` with its inputs and `N ≥ N₀(C_w)`, the initial estimates (5.22)
[gc:eq:one-step-input] at time
`1/2` at every reached point give (5.42) [gc:eq:iteration-output] with `θ_* = 2^{-J-1}` at every
deterministic time `u ∈ [1/2, t_*]` of every base point `(g, E, L, t_*)` with
`ζ_{t_*} ≤ W^{-c₀}`. -/
theorem theorem412_iter (R : PropRegime) (I : PropInputs R.base R.J) (c₀ cp₀ N : ℝ)
    (hc₀ : 0 < c₀) (hcp₀ : 0 < cp₀) (hN : lemmaNN0 I.Cw ≤ N) (hJ : schedSteps c₀ N ≤ R.J)
    (hinc : IncrementInput R.base R.J) :
    ∃ cps : ℝ, 0 < cps ∧
      (OneStepInput cp₀ (1 / 2) id
        (fun W => {p | p.u = 1 / 2 ∧ ∃ d : ℕ, d ≤ R.J ∧ CmpReach R.base W d p}) →
      OneStepInput cps ((2 : ℝ) ^ (-((schedSteps c₀ N : ℝ) + 1))) id
        (fun W => {p | ∃ q ∈ R.base W, zetaProp q.g W q.L q.u ≤ (W : ℝ) ^ (-c₀) ∧
          1 / 2 ≤ p.u ∧ p.u ≤ q.u ∧ p = ⟨q.g, q.E, q.L, p.u⟩})) := by
  have hN20 : (20 : ℝ) ≤ N := le_trans (le_max_left _ _) hN
  obtain ⟨Wg, hWg2, hgood⟩ := iteration_good R
  have chain : ∀ j : ℕ, j ≤ schedSteps c₀ N → ∃ cp : ℝ, 0 < cp ∧
      (OneStepInput cp₀ (1 / 2) id
        (fun W => {p | p.u = 1 / 2 ∧ ∃ d : ℕ, d ≤ R.J ∧ CmpReach R.base W d p}) →
      OneStepInput cp (iterTheta j) (id : FlowPt → FlowPt) (iterDom R c₀ N j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨cp₀, hcp₀, fun hin => ?_⟩
      rw [iterTheta_zero]
      refine iteration_pull (id : FlowPt → FlowPt) hin ⟨0, fun W _ x hx => ?_⟩
      obtain ⟨e, p, hr, he, hz, v, hv1, hv2, rfl⟩ := hx
      obtain ⟨hp1, -⟩ := iteration_reach_time R hr
      have h0 := iteration_sched_zero W c₀ N p.u hp1
      rw [h0] at hv2
      have hv : v = 1 / 2 := le_antisymm hv2 hv1
      exact ⟨hv, e, by omega, CmpReach.earlier v hr hv1 (by linarith)⟩
    | succ m ih =>
      intro hm
      obtain ⟨cp, hcp, hQ⟩ := ih (by omega)
      obtain ⟨cp'', hcp'', hstep⟩ := iteration_step R I c₀ N hc₀ hN hinc m hm cp hcp
      exact ⟨cp'', hcp'', fun hin => hstep (hQ hin)⟩
  obtain ⟨cps, hcps, hQ⟩ := chain (schedSteps c₀ N) le_rfl
  refine ⟨cps, hcps, fun hin => ?_⟩
  refine iteration_pull (id : FlowPt → FlowPt) (hQ hin) ⟨Wg, fun W hW x hx => ?_⟩
  obtain ⟨q, hq, hz, h1, h2, hx⟩ := hx
  obtain ⟨hg0, hL1⟩ := hgood W hW 0 q (Nat.zero_le _) (CmpReach.base hq)
  obtain ⟨hq1, hq2⟩ := R.time W q hq
  have hsched := iteration_sched W (le_trans hWg2 hW) c₀ N q.u q.g q.L hc₀ hN20 hq1 hq2 hg0 hL1 hz
  exact ⟨0, q, CmpReach.base hq, by omega, hz, x.u, h1, le_of_le_of_eq h2 hsched.2.1.symm, hx⟩

end LSBA
