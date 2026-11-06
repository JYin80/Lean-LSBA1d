import LSBA.Prop.Iteration
import LSBA.Prop.RegimeBdd
import LSBA.Prop.RegimeLarge
import LSBA.Flow.BoundedInitialPacket
import LSBA.Sampling.Inputs
import LSBA.Averaging.Inputs
import LSBA.Averaging.Lemma46
import LSBA.Prop.IncrementInputs

/-!
# Theorem 5.12(ii) [gc:thm:common] at large coupling

The iteration of Theorem 5.12 [gc:thm:common] from its general form in the large-coupling case (b)
on `baseLarge` with no upper bound on `g`, from Lemma 5.6 [fo:prop:inputs]; the inputs are Lemmas
5.8 [uvc:thm:ordinary-sampling]–5.10 [fo:lem:sampling-continuity] and the weighted sampling (5.34)
[fo:eq:weighted-sampling-input].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Restriction of the input (5.22) [gc:eq:one-step-input] to a family -/

/-- Pullback of a domination along a map of parameter families, for `W` large. -/
private lemma theorem412_precMax_pull {ι₁ ι₂ : Type*} {vol : ι₁ → ℕ} {D₁ : ℕ → Set ι₁}
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

/-- Pullback of the input (5.22) [gc:eq:one-step-input] along a map `σ` into a family of flow
points, for `W` large. -/
private lemma theorem412_pull {cp θ : ℝ} {ι : Type*} (σ : ι → FlowPt) {D₁ : ℕ → Set FlowPt}
    {D₂ : ℕ → Set ι} (h : OneStepInput cp θ (id : FlowPt → FlowPt) D₁)
    (hD : ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ x ∈ D₂ W, σ x ∈ D₁ W) : OneStepInput cp θ σ D₂ :=
  ⟨fun k hk => theorem412_precMax_pull σ (h.loop k hk) hD,
    fun k hk => theorem412_precMax_pull σ (h.err k hk) hD,
    theorem412_precMax_pull σ h.avg hD, theorem412_precMax_pull σ h.entry hD,
    fun F hF => theorem412_precMax_pull σ (h.pair F hF) hD,
    fun k hk ε A hε hA => theorem412_precMax_pull σ (h.tail k hk ε A hε hA) hD⟩

/-! ### The initial estimates on the reach -/

/-- Lemma 5.6 [fo:prop:inputs] on the reach: (5.23) [gc:eq:iteration-input] at time `1/2` at
every point reached with depth at most `J` from the large-coupling base family, through the
reach bounds `g ≥ C_κ/√2`, `|E| ≤ 2 - κ/2`, `L ≤ 2C_V g²W²` (Lemma 5.6 [fo:prop:inputs] at
`(κ/2, max(2, 2C_V))`). -/
private lemma theorem412_init_large (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV)
    (J : ℕ) :
    ∃ Cκ₀ cp₀ : ℝ, 1 ≤ Cκ₀ ∧ 0 < cp₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ,
      Tendsto ρ atTop atTop → ∀ R : PropRegime, R.base = baseLarge κ Cκ CV ρ → R.J = J →
      OneStepInput cp₀ (1 / 2) id
        (fun W => {p | p.u = 1 / 2 ∧ ∃ d : ℕ, d ≤ R.J ∧ CmpReach R.base W d p}) := by
  obtain ⟨Cm, C'', hCm, -, Hm⟩ := cmpReach_large κ CV hκ hκ2 hCV J
  obtain ⟨Cl, cp₀, -, hcp₀, Hl⟩ := lemma46_fixedTime (κ / 2) (max 2 (2 * CV)) (by linarith)
    (by linarith) (le_max_left _ _)
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  refine ⟨max Cm (Real.sqrt 2 * Cl), cp₀, hCm.trans (le_max_left _ _), hcp₀,
    fun Cκ hCκ ρ hρ R hR hRJ => ?_⟩
  have hCl' : Cl ≤ Cκ / Real.sqrt 2 := by
    rw [le_div_iff₀ hs2]
    linarith [le_max_right Cm (Real.sqrt 2 * Cl)]
  obtain ⟨W₀, H⟩ := Hm Cκ ((le_max_left _ _).trans hCκ) ρ hρ
  refine theorem412_pull id (Hl (Cκ / Real.sqrt 2) hCl' ρ hρ) ⟨W₀, fun W hW p hp => ?_⟩
  obtain ⟨hu, d, hd, hr⟩ := hp
  obtain ⟨hg, hE, -, -, -, hLlo, hLhi, -, -⟩ :=
    H R.base (fun W p hp => by rw [hR] at hp; exact hp) W hW d p (hRJ ▸ hd) hr
  refine ⟨hg, hE, hLlo, ?_, (by rw [hu]; norm_num : (0 : ℝ) ≤ p.u), hu.le⟩
  have h1 : 2 * CV ≤ max 2 (2 * CV) := le_max_right _ _
  have h2 : 0 ≤ p.g ^ 2 * (W : ℝ) ^ 2 := by positivity
  calc (p.L : ℝ) ≤ 2 * CV * p.g ^ 2 * (W : ℝ) ^ 2 := hLhi
    _ = 2 * CV * (p.g ^ 2 * (W : ℝ) ^ 2) := by ring
    _ ≤ max 2 (2 * CV) * (p.g ^ 2 * (W : ℝ) ^ 2) := mul_le_mul_of_nonneg_right h1 h2
    _ = max 2 (2 * CV) * p.g ^ 2 * (W : ℝ) ^ 2 := by ring

/-! ### Theorem 5.12(ii) [gc:thm:common] -/

/-- Theorem 5.12(ii) [gc:thm:common] at large coupling (case (b)), from the general form, the
inputs and Lemma 5.6 [fo:prop:inputs]; no upper bound on `g`. -/
theorem theorem412_large (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) (c₀ : ℝ)
    (hc₀ : 0 < c₀) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∃ θs cps : ℝ, 0 < θs ∧ 0 < cps ∧ OneStepInput cps θs id
        (fun W => {p | ∃ q ∈ baseLarge κ Cκ CV ρ W, zetaProp q.g W q.L q.u ≤ (W : ℝ) ^ (-c₀) ∧
          1 / 2 ≤ p.u ∧ p.u ≤ q.u ∧ p = ⟨q.g, q.E, q.L, p.u⟩}) := by
  obtain ⟨Cw, hCw, Hsw⟩ := swInput_large κ hκ hκ2
  obtain ⟨Cr, hCr, Hr⟩ := regimeLarge_exists κ CV hκ hκ2 hCV (schedSteps c₀ (lemmaNN0 Cw))
  obtain ⟨Cc, hCc, Hc⟩ := crudeInput_large κ CV hκ hκ2 hCV (schedSteps c₀ (lemmaNN0 Cw))
  obtain ⟨Cs, hCs, Hs⟩ := samplingInput_large κ CV hκ hκ2 hCV (schedSteps c₀ (lemmaNN0 Cw))
  obtain ⟨Ca, hCa, Ha⟩ := averagingInput_large κ CV hκ hκ2 hCV (schedSteps c₀ (lemmaNN0 Cw))
  obtain ⟨Cw₀, hCw₀, Hw⟩ := Hsw CV hCV (schedSteps c₀ (lemmaNN0 Cw))
  obtain ⟨Ci, hCi, Hi⟩ := incrementInput_large κ CV hκ hκ2 hCV (schedSteps c₀ (lemmaNN0 Cw))
  obtain ⟨Cl, cp₀, hCl, hcp₀, Hl⟩ :=
    theorem412_init_large κ CV hκ hκ2 hCV (schedSteps c₀ (lemmaNN0 Cw))
  refine ⟨Cr + Cc + Cs + Ca + Cw₀ + Ci + Cl, by linarith, fun Cκ hCκ ρ hρ => ?_⟩
  obtain ⟨R, hRb, hRJ⟩ := Hr Cκ (by linarith) ρ hρ
  have hcr : CrudeInput R.base R.J := by
    rw [hRb, hRJ]; exact Hc Cκ (by linarith) ρ hρ
  have hav : AveragingInput R.base R.J := by
    rw [hRb, hRJ]; exact Ha Cκ (by linarith) ρ hρ
  have hsa : SamplingInput R.base R.J := by
    rw [hRb, hRJ]; exact Hs Cκ (by linarith) ρ hρ
  have hsw : SwInput R.base R.J Cw := by
    rw [hRb, hRJ]; exact Hw Cκ (by linarith) ρ hρ
  have hinc : IncrementInput R.base R.J := by
    rw [hRb, hRJ]; exact Hi Cκ (by linarith) ρ hρ
  have hinit := Hl Cκ (by linarith) ρ hρ R hRb hRJ
  obtain ⟨cps, hcps, himp⟩ := theorem412_iter R ⟨Cw, hCw, hcr, hav, hsa, hsw⟩ c₀ cp₀
    (lemmaNN0 Cw) hc₀ hcp₀ le_rfl (by rw [hRJ]) hinc
  refine ⟨(2 : ℝ) ^ (-((schedSteps c₀ (lemmaNN0 Cw) : ℝ) + 1)), cps,
    Real.rpow_pos_of_pos two_pos _, hcps, ?_⟩
  have h := himp hinit
  rw [hRb] at h
  exact h

end LSBA
