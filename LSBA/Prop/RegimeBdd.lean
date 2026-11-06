import LSBA.Prop.Regime
import LSBA.Kernel.Bounded
import LSBA.Kernel.Scales
import LSBA.Primitive.Early
import LSBA.Primitive.Bounded

/-!
# The bounded-coupling regime

The base family of Theorem 5.12 [gc:thm:common] (a) at bounded coupling (`g ≥ W^{-ω}`, `g ≤ C`,
`|E| ≤ B`, `Im m ≥ c′`, `ρ log W ≤ L ≤ W²`, in rate form), and a regime on its reach from any
primitive slot and the bounded-coupling kernel bounds.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The bounded-coupling base family: `g_min(W) ≤ g`, the regular domain `RegBdd C B c'`
(`g ≤ C`, `|E| ≤ B`, the anchor a root with `Im m ≥ c'`), `ρ(W) log W ≤ L ≤ W²`, and a time in
`[1/2, 1 - W^{-3}]` (the ranges of (5.37)(a) [gc:eq:step-parameters] and (5.40)(a)
[gc:eq:initial-parameters] with the
fixed rates). -/
def baseBdd (C B c' : ℝ) (gmin ρ : ℕ → ℝ) (W : ℕ) : Set FlowPt :=
  {p | gmin W ≤ p.g ∧ RegBdd C B c' p.L p.g p.E ∧ ρ W * Real.log W ≤ p.L ∧
    (p.L : ℝ) ≤ (W : ℝ) ^ 2 ∧ 1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u}

private lemma regimeBdd_gamma_pos (g : ℝ) : 0 < gammaG g :=
  inv_pos.mpr (pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) 2)

private lemma regimeBdd_gamma_le_one (g : ℝ) : gammaG g ≤ 1 := by
  unfold gammaG
  have h1 : (1 : ℝ) ≤ max 1 g := le_max_left _ _
  exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)

private lemma regimeBdd_regBdd_mono {C B B' c c'' : ℝ} {L : ℕ} {g E : ℝ}
    (h : RegBdd C B c L g E) (hB : B ≤ B') (hc : c'' ≤ c) : RegBdd C B' c'' L g E :=
  ⟨h.1, h.2.1, h.2.2.1.trans hB, h.2.2.2.1, hc.trans h.2.2.2.2⟩

/-- Invariants of a point of the comparison reach of the base family: it comes from a base point
`q` at the same length by a chain of at most `d` admissible comparisons, at a time in
`[1/2, q.u]`. -/
private lemma regimeBdd_reach_inv (C B c' : ℝ) (gmin ρ : ℕ → ℝ) (W : ℕ) (hW : 1 ≤ W)
    {d : ℕ} {p : FlowPt} (h : CmpReach (baseBdd C B c' gmin ρ) W d p) :
    ∃ q ∈ baseBdd C B c' gmin ρ W, ∃ steps : List (ℝ × ℝ), steps.length ≤ d ∧
      (∀ x ∈ steps, 1 / 2 ≤ x.1 ∧ x.1 ≤ x.2 ∧ x.2 < 1) ∧ p.L = q.L ∧
      (p.g, p.E) = cmpChain q.L (q.g, q.E) steps ∧ 1 / 2 ≤ p.u ∧ p.u ≤ q.u := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW3 : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
  induction h with
  | @base p hp => exact ⟨p, hp, [], by simp, by simp, rfl, rfl, hp.2.2.2.2.1, le_rfl⟩
  | @earlier d p v _ hv hvu ih =>
    obtain ⟨q, hq, steps, hl, hst, hL, hgE, -, huq⟩ := ih
    exact ⟨q, hq, steps, hl, hst, hL, hgE, hv, hvu.trans huq⟩
  | @cmp d p s _ hs hsu ih =>
    obtain ⟨q, hq, steps, hl, hst, hL, hgE, hu, huq⟩ := ih
    have hq1 : q.u < 1 := by linarith [hq.2.2.2.2.2]
    refine ⟨q, hq, steps ++ [(s, p.u)], by simp; omega, ?_, hL, ?_, hs, hsu.trans huq⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hst x hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact ⟨hs, hsu, lt_of_le_of_lt huq hq1⟩
    · unfold cmpChain at hgE ⊢
      rw [List.foldl_append, ← hgE]
      change _ = cmpStep q.L (p.g, p.E) (s, p.u)
      unfold cmpStep cmpPt
      rw [← hL]
  | @lift d p _ ih =>
    obtain ⟨q, hq, steps, hl, hst, hL, hgE, hu, huq⟩ := ih
    exact ⟨q, hq, steps, by omega, hst, hL, hgE, hu, huq⟩

/-- The reach of the base family at large `W`: lengths at least `L₁`, the regular domain
`RegBdd C BJ cJ` along the chain, `g` at least `cJ g_min(W)`, and the time range. -/
private lemma regimeBdd_reach (C B c' : ℝ) (gmin ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop atTop)
    (J : ℕ) (BJ cJ : ℝ) (L₀ : ℕ) (hcJ : 0 < cJ)
    (hchain : ∀ g₀ : ℝ, ∀ L : ℕ, 3 ≤ L → L₀ ≤ L → ∀ E₀ : ℝ, RegBdd C B c' L g₀ E₀ →
      ∀ steps : List (ℝ × ℝ), steps.length ≤ J →
      (∀ p ∈ steps, 1 / 2 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 < 1) →
      cJ * g₀ ≤ (cmpChain L (g₀, E₀) steps).1 ∧
        RegBdd C BJ cJ L (cmpChain L (g₀, E₀) steps).1 (cmpChain L (g₀, E₀) steps).2)
    (L₁ : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J → CmpReach (baseBdd C B c' gmin ρ) W d p →
      3 ≤ W ∧ L₁ ≤ p.L ∧ 3 ≤ p.L ∧ L₀ ≤ p.L ∧ RegBdd C BJ cJ p.L p.g p.E ∧
        cJ * gmin W ≤ p.g ∧ 1 / 2 ≤ p.u ∧ p.u < 1 ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u ∧
        (p.L : ℝ) ≤ (W : ℝ) ^ 2 := by
  set X : ℕ := max L₁ (max 3 L₀) with hX
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hρ.eventually_ge_atTop (X : ℝ))
  refine ⟨max N 3, fun W hW d p hd hp => ?_⟩
  have hWN : N ≤ W := (le_max_left _ _).trans hW
  have hW3 : 3 ≤ W := (le_max_right _ _).trans hW
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  obtain ⟨q, hq, steps, hl, hst, hL, hgE, hu, huq⟩ := regimeBdd_reach_inv C B c' gmin ρ W hW1 hp
  have hρW : (X : ℝ) ≤ ρ W := hN W hWN
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have hlog : 1 ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le hW0]
    have : (3 : ℝ) ≤ W := by exact_mod_cast hW3
    exact (Real.exp_one_lt_three.trans_le this).le
  have hLq : (X : ℝ) ≤ q.L := by
    have h1 : ρ W * 1 ≤ ρ W * Real.log W := mul_le_mul_of_nonneg_left hlog (hX0.trans hρW)
    linarith [hq.2.2.1]
  have hLq' : X ≤ q.L := by exact_mod_cast hLq
  have hL1 : L₁ ≤ q.L := (le_max_left _ _).trans hLq'
  have hL3 : 3 ≤ q.L := ((le_max_left _ _).trans (le_max_right _ _)).trans hLq'
  have hL0 : L₀ ≤ q.L := ((le_max_right _ _).trans (le_max_right _ _)).trans hLq'
  obtain ⟨h1, h2⟩ := hchain q.g q.L hL3 hL0 q.E hq.2.1 steps (hl.trans hd) hst
  rw [← hgE] at h1 h2
  have hq1 : q.u < 1 := by
    have : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
    linarith [hq.2.2.2.2.2]
  refine ⟨hW3, hL ▸ hL1, hL ▸ hL3, hL ▸ hL0, ?_, ?_, hu, lt_of_le_of_lt huq hq1, ?_, ?_⟩
  · rw [hL]; exact h2
  · calc cJ * gmin W ≤ cJ * q.g := mul_le_mul_of_nonneg_left hq.1 hcJ.le
      _ ≤ p.g := h1
  · linarith [hq.2.2.2.2.2]
  · rw [hL]; exact hq.2.2.2.1

/-- Lemma 6.3(b) [da:lem:comparison-parameters] at bounded coupling with a positive energy
bound `B_J`. -/
private lemma regimeBdd_chain (C B c' : ℝ) (J : ℕ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') :
    ∃ BJ cJ : ℝ, ∃ L₀ : ℕ, 0 < BJ ∧ 0 < cJ ∧
      ∀ g₀ : ℝ, ∀ L : ℕ, 3 ≤ L → L₀ ≤ L → ∀ E₀ : ℝ, RegBdd C B c' L g₀ E₀ →
      ∀ steps : List (ℝ × ℝ), steps.length ≤ J →
      (∀ p ∈ steps, 1 / 2 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 < 1) →
      cJ * g₀ ≤ (cmpChain L (g₀, E₀) steps).1 ∧
        RegBdd C BJ cJ L (cmpChain L (g₀, E₀) steps).1 (cmpChain L (g₀, E₀) steps).2 := by
  obtain ⟨BJ0, cJ, L₀, hcJ, hchain⟩ := cmpChain_bdd C B c' J hC hB hc'
  refine ⟨max BJ0 1, cJ, L₀, lt_of_lt_of_le one_pos (le_max_right _ _), hcJ, ?_⟩
  intro g₀ L hL3 hL E₀ hreg steps hlen hadm
  obtain ⟨h1, h2⟩ := hchain g₀ L hL3 hL E₀ hreg steps hlen hadm
  exact ⟨h1, regimeBdd_regBdd_mono h2 (le_max_left _ _) le_rfl⟩

/-- The regime on the reach of the bounded-coupling base family from any primitive slot, without a
positivity hypothesis on the lower rate: every field except the primitive slot comes from the
bounded-coupling statements at the constants `(C, B_J, c_J)` of the comparison chain, uniformly on
`0 ≤ g ≤ C`. -/
private theorem regimeBdd_core (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c')
    (gmin ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop atTop) (J : ℕ)
    (hslot : ∀ kmax : ℕ, ∀ δ : ℝ, 0 < δ → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J →
      CmpReach (baseBdd C B c' gmin ρ) W d p → ∀ k : ℕ, 2 ≤ k → k ≤ kmax →
      ∀ (a : Fin k → Fin p.L) (σ : Fin k → Bool),
        ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u a σ‖ ≤
          (W : ℝ) ^ δ * zetaProp p.g W p.L p.u ^ (k - 1)) :
    ∃ R : PropRegime, R.base = baseBdd C B c' gmin ρ ∧ R.J = J := by
  obtain ⟨BJ, cJ, L₀c, hBJ, hcJ, hchain⟩ := regimeBdd_chain C B c' J hC hB hc'
  have hreach : ∀ L₁ : ℕ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J →
      CmpReach (baseBdd C B c' gmin ρ) W d p →
      3 ≤ W ∧ L₁ ≤ p.L ∧ 3 ≤ p.L ∧ L₀c ≤ p.L ∧ RegBdd C BJ cJ p.L p.g p.E ∧
        cJ * gmin W ≤ p.g ∧ 1 / 2 ≤ p.u ∧ p.u < 1 ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u ∧
        (p.L : ℝ) ≤ (W : ℝ) ^ 2 :=
    fun L₁ => regimeBdd_reach C B c' gmin ρ hρ J BJ cJ L₀c hcJ hchain L₁
  obtain ⟨cs, Cs, L₀s, hcs, hCs, hscales⟩ := scalesProp_bdd C BJ cJ hC hBJ hcJ
  obtain ⟨C'', L₀m, hC''1, hcmp⟩ := cmpParams_bdd C BJ cJ hC hBJ hcJ
  obtain ⟨ch, Ch, L₀h, hch, hCh, hheight⟩ := positiveHeight_bdd C BJ cJ hC hBJ hcJ
  set CR : ℝ := max 3 (max cJ⁻¹ (max Cs (max C'' Ch))) with hCR
  set cR : ℝ := min cs ch with hcR
  set L₁ : ℕ := max L₀s (max L₀m L₀h) with hL₁
  have hCR3 : 3 ≤ CR := le_max_left _ _
  have hCR0 : 0 < CR := by linarith
  have hCRc : cJ⁻¹ ≤ CR := (le_max_left _ _).trans (le_max_right _ _)
  have hCRs : Cs ≤ CR := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCRm : C'' ≤ CR :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)
  have hCRh : Ch ≤ CR :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)
  have hcR0 : 0 < cR := lt_min hcs hch
  have hcRs : cR ≤ cs := min_le_left _ _
  have hcRh : cR ≤ ch := min_le_right _ _
  have hL₁s : L₀s ≤ L₁ := le_max_left _ _
  have hL₁m : L₀m ≤ L₁ := (le_max_left _ _).trans (le_max_right _ _)
  have hL₁h : L₀h ≤ L₁ := (le_max_right _ _).trans (le_max_right _ _)
  have hCRinv : CR⁻¹ ≤ cJ := (inv_le_comm₀ hCR0 hcJ).mpr hCRc
  refine ⟨{
    base := baseBdd C B c' gmin ρ
    J := J
    C := CR
    c := cR
    one_le_C := by linarith
    c_pos := hcR0
    time := ?_
    dyson := ?_
    kernel := ?_
    budget := ?_
    cmp := ?_
    height := ?_
    prim := hslot
    primTail := ?_
    longPair := ?_ }, rfl, rfl⟩
  · intro W p hp
    exact ⟨hp.2.2.2.2.1, hp.2.2.2.2.2⟩
  · obtain ⟨W₁, hW₁⟩ := hreach L₁
    refine ⟨W₁, fun W hW d p hd hp => ?_⟩
    obtain ⟨-, hL1, hL3, -, hreg, -⟩ := hW₁ W hW d p hd hp
    obtain ⟨hg0, hgC, hE, hroot, hcm⟩ := hreg
    have H := hscales p.g hg0 hgC p.L hL3 (hL₁s.trans hL1) p.E hE (mRoot p.g p.L p.E) hroot hcm
    dsimp only at H
    obtain ⟨him, hMb, hrow, hQ, -⟩ := H
    exact ⟨hL3, hg0, hroot, hCRinv.trans hcm, him.trans hCRs, fun a b => (hMb a b).trans hCRs,
      fun a => (hrow a).trans hCRs, fun u hu0 hu1 a => (hQ u hu0 hu1 a).trans hCRs⟩
  · intro A hA
    obtain ⟨W₁, hW₁⟩ := hreach L₁
    refine ⟨W₁, fun W hW d p hd hp a b => ?_⟩
    obtain ⟨hW3, hL1, hL3, -, hreg, -, hu0, hu1, -⟩ := hW₁ W hW d p hd hp
    obtain ⟨hg0, hgC, hE, hroot, hcm⟩ := hreg
    have H := hscales p.g hg0 hgC p.L hL3 (hL₁s.trans hL1) p.E hE (mRoot p.g p.L p.E) hroot hcm
    dsimp only at H
    obtain ⟨-, -, -, -, hK⟩ := H
    obtain ⟨hK0, hKle⟩ := hK p.u (by linarith) hu1 a b
    have hℓ1 := (scale_facts p.g hg0 W p.L (by omega) (by omega) p.u p.u (by linarith) le_rfl
      hu1).1
    have hℓ0 : 0 < ellProp p.g p.L p.u := by linarith
    have hδ : 0 < 1 - p.u := by linarith
    have hd0 : (0 : ℝ) ≤ (cycDist a b : ℝ) := Nat.cast_nonneg _
    refine ⟨hK0, hKle.trans ?_⟩
    have hrem : 0 ≤ (ellProp p.g p.L p.u)⁻¹ * (W : ℝ) ^ (-A) := by
      have : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
      positivity
    have h1 : Cs / ((1 - p.u) * ellProp p.g p.L p.u) *
          Real.exp (-(cs * cycDist a b / ellProp p.g p.L p.u)) ≤
        CR / ((1 - p.u) * ellProp p.g p.L p.u) *
          Real.exp (-(cR * cycDist a b / ellProp p.g p.L p.u)) := by
      refine mul_le_mul (div_le_div_of_nonneg_right hCRs (by positivity)) ?_
        (Real.exp_pos _).le (by positivity)
      exact Real.exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcRs hd0) hℓ0.le))
    linarith
  · obtain ⟨W₁, hW₁⟩ := hreach 0
    refine ⟨W₁, fun W hW d p hd hp => ?_⟩
    obtain ⟨hW3, -, hL3, -, hreg, -, hu0, hu1, -, hLW⟩ := hW₁ W hW d p hd hp
    have hg0 := hreg.1
    have hℓ1 := (scale_facts p.g hg0 W p.L (by omega) (by omega) p.u p.u (by linarith) le_rfl
      hu1).1
    have hL0 : (0 : ℝ) ≤ p.L := Nat.cast_nonneg _
    have h1 : gammaG p.g * p.L ≤ p.L := mul_le_of_le_one_left hL0 (regimeBdd_gamma_le_one p.g)
    have h2 : (p.L : ℝ) / ellProp p.g p.L p.u ≤ p.L := div_le_self hL0 hℓ1
    have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast (by omega : 2 ≤ W)
    have h3 : (W : ℝ) ^ 3 ≤ (W : ℝ) ^ CR := by
      have := Real.rpow_le_rpow_of_exponent_le (x := (W : ℝ)) (by linarith) (show ((3 : ℕ) : ℝ) ≤ CR
        by push_cast; exact hCR3)
      rwa [Real.rpow_natCast] at this
    have h4 : 2 * (W : ℝ) ^ 2 ≤ (W : ℝ) ^ 3 := by nlinarith [sq_nonneg (W : ℝ)]
    linarith
  · obtain ⟨W₁, hW₁⟩ := hreach L₁
    refine ⟨W₁, fun W hW d p s hd hp hs hsu => ?_⟩
    obtain ⟨-, hL1, hL3, -, hreg, -, hu0, hu1, -⟩ := hW₁ W hW d p hd.le hp
    obtain ⟨hg0, hgC, hE, hroot, hcm⟩ := hreg
    have H := hcmp p.g hg0 hgC p.L hL3 (hL₁m.trans hL1) p.E hE (mRoot p.g p.L p.E) hroot hcm
      s p.u hs hsu hu1
    dsimp only at H
    obtain ⟨-, -, hre, hηle, hwle, hid, -⟩ := H
    have hη : 0 ≤ etaChar p.g (mRoot p.g p.L p.E) p.u := by
      unfold etaChar
      have h1 : 0 < 1 - p.u := by linarith
      have h2 : 0 < (mRoot p.g p.L p.E).im := lt_of_lt_of_le hcJ hcm
      have h3 := regimeBdd_gamma_pos p.g
      positivity
    have hfac : 0 ≤ (1 - s) / (1 - p.u) := div_nonneg (by linarith) (by linarith)
    refine ⟨hre, hηle, hwle.trans ?_, hid⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCRm hfac) hη
  · obtain ⟨W₁, hW₁⟩ := hreach L₁
    refine ⟨W₁, fun W hW d p s y hd hp hs hsu hηy hyw => ?_⟩
    obtain ⟨-, hL1, hL3, -, hreg, -, hu0, hu1, -⟩ := hW₁ W hW d p hd.le hp
    obtain ⟨hg0, hgC, hE, hroot, hcm⟩ := hreg
    have H := hheight p.g hg0 hgC p.L hL3 (hL₁h.trans hL1) p.E hE (mRoot p.g p.L p.E) hroot hcm
      s p.u hs hsu hu1 y hηy hyw
    dsimp only at H
    obtain ⟨hr, hcm', -, hMb, hrow, hQ, hdiff, hderiv, -⟩ := H
    exact ⟨hr, hcRh.trans hcm', fun a b => (hMb a b).trans hCRh,
      fun a => (hrow a).trans hCRh, fun a => (hQ a).trans hCRh, hdiff,
      fun a b => (hderiv a b).trans hCRh⟩
  · intro k hk ε Q hε hQ
    obtain ⟨Wt, Lt, ht⟩ := primLoop_bdd_tail C BJ cJ ε Q hC hBJ hcJ hε hQ k hk
    obtain ⟨W₁, hW₁⟩ := hreach Lt
    refine ⟨max W₁ Wt, fun W hW d p hd hp a σ hdiam => ?_⟩
    obtain ⟨-, hL1, hL3, -, hreg, -, hu0, hu1, hu3, -⟩ :=
      hW₁ W ((le_max_left _ _).trans hW) d p hd hp
    obtain ⟨hg0, hgC, hE, hroot, hcm⟩ := hreg
    exact ht W ((le_max_right _ _).trans hW) p.g hg0 hgC p.L hL3 hL1 p.E hE
      (mRoot p.g p.L p.E) hroot hcm p.u (by linarith) hu3 a σ hdiam
  · intro θ cp F hθ hθ2 hcp hF
    obtain ⟨C', Wt, Lt, hC', ht⟩ := primLoop_longPair C BJ cJ θ cp F hC hBJ hcJ hθ hθ2 hcp hF
    obtain ⟨W₁, hW₁⟩ := hreach Lt
    refine ⟨C', max W₁ Wt, fun W hW d p hd hp a b σ₁ σ₂ hdist => ?_⟩
    obtain ⟨-, hL1, hL3, -, hreg, -, hu0, hu1, hu3, -⟩ :=
      hW₁ W ((le_max_left _ _).trans hW) d p hd hp
    obtain ⟨hg0, hgC, hE, hroot, hcm⟩ := hreg
    exact ht W ((le_max_right _ _).trans hW) p.g hg0 hgC p.L hL3 hL1 p.E hE
      (mRoot p.g p.L p.E) hroot hcm p.u hu0 hu3 a b σ₁ σ₂ hdist

/-- A bounded-coupling regime from any primitive slot: the kernel, comparison and positive-height
fields come from Lemmas 6.1 [da:lem:scales-propagators], 6.3 [da:lem:comparison-parameters], 6.4
[da:lem:positive-height] at bounded coupling, uniformly on `0 ≤ g ≤ C`; the slot is
the hypothesis. -/
theorem regimeBdd_of_slot (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c')
    (gmin ρ : ℕ → ℝ) (hgmin : ∀ W, 0 < gmin W) (hρ : Tendsto ρ atTop atTop) (J : ℕ)
    (hslot : ∀ kmax : ℕ, ∀ δ : ℝ, 0 < δ → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J →
      CmpReach (baseBdd C B c' gmin ρ) W d p → ∀ k : ℕ, 2 ≤ k → k ≤ kmax →
      ∀ (a : Fin k → Fin p.L) (σ : Fin k → Bool),
        ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u a σ‖ ≤
          (W : ℝ) ^ δ * zetaProp p.g W p.L p.u ^ (k - 1)) :
    ∃ R : PropRegime, R.base = baseBdd C B c' gmin ρ ∧ R.J = J := by
  have _ := hgmin
  exact regimeBdd_core C B c' hC hB hc' gmin ρ hρ J hslot

end LSBA
