import LSBA.Small.Primitive
import LSBA.Prop.Iteration
import LSBA.Flow.BoundedInitialPacket
import LSBA.Averaging.Inputs
import LSBA.Prop.IncrementInputs

/-!
# Propagation at small coupling

Theorem 5.12 [gc:thm:common](ii) at bounded coupling on the base family for every positive
lower rate `g_min(W) > 0` of the coupling, in particular on the range
`W^{-1/2+ε} ≤ g ≤ W^{-ε}`: a bounded-coupling regime with the
sharp primitive slot, the bounded-coupling inputs (5.22) [gc:eq:one-step-input], and the initial
estimates of Lemma 5.3 [fo:lem:bounded-initial].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Eventual inclusion of parameter families preserves stochastic domination. -/
private lemma propagation_precMax_anti {ι : Type*} {vol : ι → ℕ} {Dom Dom' : ℕ → Set ι}
    {Λ : ℕ → ι → Type*} {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ}
    {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ} (h : PrecMax vol Dom X Y) (W₁ : ℕ)
    (hD : ∀ W, W₁ ≤ W → Dom' W ⊆ Dom W) : PrecMax vol Dom' X Y := by
  intro ε D hε hD'
  obtain ⟨W₀, hW⟩ := h ε D hε hD'
  exact ⟨max W₀ W₁, fun W hW0 p hp =>
    hW W (le_of_max_le_left hW0) p (hD W (le_of_max_le_right hW0) hp)⟩

/-- Eventual inclusion of parameter families preserves the input (5.22) [gc:eq:one-step-input]. -/
private lemma propagation_oneStep_anti {cp θ : ℝ} {ι : Type*} {pt : ι → FlowPt}
    {Dom Dom' : ℕ → Set ι} (h : OneStepInput cp θ pt Dom) (W₁ : ℕ)
    (hD : ∀ W, W₁ ≤ W → Dom' W ⊆ Dom W) : OneStepInput cp θ pt Dom' :=
  ⟨fun k hk => propagation_precMax_anti (h.loop k hk) W₁ hD,
    fun k hk => propagation_precMax_anti (h.err k hk) W₁ hD,
    propagation_precMax_anti h.avg W₁ hD, propagation_precMax_anti h.entry W₁ hD,
    fun F hF => propagation_precMax_anti (h.pair F hF) W₁ hD,
    fun k hk ε A hε hA => propagation_precMax_anti (h.tail k hk ε A hε hA) W₁ hD⟩

/-- A bounded-coupling regime on the base family `baseBdd` for every positive lower rate
`g_min(W) > 0` of the coupling, with the primitive slot of the sharp bound. -/
theorem regimeSmall_exists (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c')
    (gmin ρ : ℕ → ℝ) (hgmin : ∀ W, 0 < gmin W) (hρ : Tendsto ρ atTop atTop) (J : ℕ) :
    ∃ R : PropRegime, R.base = baseBdd C B c' gmin ρ ∧ R.J = J := by
  refine regimeBdd_of_slot C B c' hC hB hc' gmin ρ hgmin hρ J fun kmax δ hδ => ?_
  obtain ⟨BJ, cJ, hcJ, W₁, hreach⟩ := cmpReach_bdd C B c' hC hB hc' gmin ρ hgmin hρ J
  obtain ⟨W₂, L₀, hslot⟩ :=
    primLoop_sharp_slot C (max BJ 1) cJ δ hC (lt_of_lt_of_le one_pos (le_max_right _ _)) hcJ hδ
      kmax
  have hlog : Tendsto (fun W : ℕ => ρ W * Real.log W) atTop atTop :=
    hρ.atTop_mul_atTop₀ (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨W₃, hW₃⟩ := Filter.eventually_atTop.mp (hlog.eventually_ge_atTop (L₀ : ℝ))
  refine ⟨max (max W₁ W₂) (max W₃ 1), fun W hW d p hd hp k hk2 hkk a σ => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW0 : (0 : ℝ) < W := by
    have : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
    exact_mod_cast this
  obtain ⟨⟨-, hgC, hE, hroot, hc⟩, hg0, hL3, -, hu12, hu1⟩ :=
    hreach (baseBdd C B c' gmin ρ) (fun _ _ hq => hq) W hW1 d p hd hp
  obtain ⟨q, hq, -, -, -, -, -, hL, -⟩ := cmpReach_chain _ W d p hp
  have hLq : (L₀ : ℝ) ≤ p.L := by rw [hL]; exact (hW₃ W hW3).trans hq.2.2.1
  have hu : p.u < 1 := by linarith [Real.rpow_pos_of_pos hW0 (-3 : ℝ)]
  exact hslot W hW2 p.g hg0 hgC p.L hL3 (by exact_mod_cast hLq) p.E
    (hE.trans (le_max_left _ _)) _ hroot hc p.u (by linarith) hu k hk2 hkk a σ

/-- Theorem 5.12(ii) [gc:thm:common] at bounded coupling for every positive lower rate
`g_min(W) > 0` (in particular `g ≥ W^{-1/2+ε}`), from the general form, the inputs and Lemma 5.3
[fo:lem:bounded-initial]. -/
theorem theorem412_small (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c')
    (gmin ρ : ℕ → ℝ) (hgmin : ∀ W, 0 < gmin W) (hρ : Tendsto ρ atTop atTop) (c₀ : ℝ)
    (hc₀ : 0 < c₀) :
    ∃ θs cps : ℝ, 0 < θs ∧ 0 < cps ∧ OneStepInput cps θs id
      (fun W => {p | ∃ q ∈ baseBdd C B c' gmin ρ W,
        zetaProp q.g W q.L q.u ≤ (W : ℝ) ^ (-c₀) ∧ 1 / 2 ≤ p.u ∧ p.u ≤ q.u ∧
        p = ⟨q.g, q.E, q.L, p.u⟩}) := by
  set N : ℝ := lemmaNN0 1
  set J : ℕ := schedSteps c₀ N
  obtain ⟨R, hbase, hJ⟩ := regimeSmall_exists C B c' hC hB hc' gmin ρ hgmin hρ J
  let I0 : PropInputs (baseBdd C B c' gmin ρ) J :=
    ⟨1, le_rfl, crudeInput_bdd C B c' hC hB hc' gmin ρ hgmin hρ J,
      averagingInput_bdd C B c' hC hB hc' gmin ρ hgmin hρ J,
      samplingInput_bdd C B c' hC hB hc' gmin ρ hgmin hρ J,
      swInput_bdd C B c' hC hB hc' gmin ρ hgmin hρ J⟩
  obtain ⟨BJ, cJ, hcJ, W₁, hreach⟩ := cmpReach_bdd C B c' hC hB hc' gmin ρ hgmin hρ J
  obtain ⟨cp₀, hcp₀, hinit⟩ :=
    boundedInitial_packet C (max BJ 1) cJ hC (lt_of_lt_of_le one_pos (le_max_right _ _)) hcJ
  have key : ∃ I : PropInputs R.base R.J, I.Cw = 1 ∧ IncrementInput R.base R.J := by
    cases R
    dsimp only at hbase hJ ⊢
    subst hbase hJ
    exact ⟨I0, rfl, incrementInput_bdd C B c' hC hB hc' gmin ρ hρ J⟩
  obtain ⟨I, hI, hinc⟩ := key
  obtain ⟨cps, hcps, himp⟩ :=
    theorem412_iter R I c₀ cp₀ N hc₀ hcp₀ (by rw [hI]) (by rw [hJ]) hinc
  have hout := himp (propagation_oneStep_anti hinit W₁ ?_)
  · rw [hbase] at hout
    exact ⟨_, cps, by positivity, hcps, hout⟩
  rintro W hW p ⟨hpu, d, hd, hp⟩
  rw [hbase] at hp
  rw [hJ] at hd
  obtain ⟨⟨hg0', hgC, hE, hroot, hc⟩, hg0, hL3, hLW, -, -⟩ :=
    hreach (baseBdd C B c' gmin ρ) (fun _ _ hq => hq) W hW d p hd hp
  exact ⟨hg0, ⟨hg0', hgC, hE.trans (le_max_left _ _), hroot, hc⟩, hL3, hLW,
    by simp only [hpu]; norm_num, by simp only [hpu]; norm_num⟩

end LSBA
