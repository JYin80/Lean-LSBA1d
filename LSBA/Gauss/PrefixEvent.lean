import LSBA.Gauss.BlockWindow
import LSBA.Gauss.PrefixProduct

/-!
# Events after a prefix of blocks

Data that depend only on the first `a` blocks of a sample are fixed before the remaining blocks
are sampled. For a function of such data and of the sample that does not see the first `a`
blocks, a bound on its integral at every fixed value of the data on a set `S` of prefixes passes
to the full sample with the factor `P(S)`. This is the conditioning on the prepared data
`(R_4, v_4)` of Lemma 9.1 [su:lem:preparation] in the proof of Lemma 9.3
[su:lem:chosen-generator], Section 9.4 [su:sec:construction-estimates].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `f` depends only on the first `a` blocks: it takes the same value on samples that agree on
blocks `0, …, a - 1`. -/
def PrefixData {X : Type*} (W L a : ℕ) (f : Ω W L → X) : Prop :=
  ∀ ω ω' : Ω W L, (∀ x : Fin L × Fin W × Fin W, (x.1 : ℕ) < a → ω x = ω' x) → f ω = f ω'

/-- Conditioning on the first `a` blocks, integral form: for data `D` and a set `S` of prefixes,
and a measurable `F (d, ω)` that does not see the first `a` blocks, if `∫ F (D ω, ·) ≤ b` for every
`ω ∈ S`, then `∫_S F (D ω, ω) ≤ b P(S)`. -/
theorem lintegral_prefix_le (W L a : ℕ) {X : Type*} [MeasurableSpace X] {D : Ω W L → X}
    (hD : Measurable D) (hDa : PrefixData W L a D) {S : Set (Ω W L)} (hS : MeasurableSet S)
    (hSa : PrefixData W L a (· ∈ S)) {F : X → Ω W L → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F))
    (hFa : ∀ d ω ω', (∀ x : Fin L × Fin W × Fin W, a ≤ (x.1 : ℕ) → ω x = ω' x) →
      F d ω = F d ω')
    {b : ℝ≥0∞} (hb : ∀ ω ∈ S, ∫⁻ ω', F (D ω) ω' ∂(μ W L) ≤ b) :
    ∫⁻ ω, S.indicator (fun ω => F (D ω) ω) ω ∂(μ W L) ≤ b * μ W L S := by
  set G : Ω W L → Ω W L → ℝ≥0∞ := fun ω' ω => S.indicator (fun ω' => F (D ω') ω) ω' with hGdef
  have hG : Measurable (Function.uncurry G) := by
    have : Function.uncurry G = (Prod.fst ⁻¹' S).indicator (fun p => F (D p.1) p.2) := by
      ext ⟨x, y⟩
      simp [hGdef, Set.indicator]
    rw [this]
    exact Measurable.indicator (hF.comp ((hD.comp measurable_fst).prodMk measurable_snd))
      (measurable_fst hS)
  have h₁ : ∀ ω₁ ω₂ ω : Ω W L, (∀ k : Fin L × Fin W × Fin W, (k.1 : ℕ) < a → ω₁ k = ω₂ k) →
      G ω₁ ω = G ω₂ ω := by
    intro ω₁ ω₂ ω h
    have hS12 : ω₁ ∈ S ↔ ω₂ ∈ S := Iff.of_eq (hSa ω₁ ω₂ h)
    simp only [hGdef, Set.indicator, hS12, hDa ω₁ ω₂ h]
  have h₂ : ∀ ω' ω₁ ω₂ : Ω W L, (∀ k : Fin L × Fin W × Fin W, a ≤ (k.1 : ℕ) → ω₁ k = ω₂ k) →
      G ω' ω₁ = G ω' ω₂ := by
    intro ω' ω₁ ω₂ h
    simp only [hGdef, Set.indicator, hFa _ ω₁ ω₂ h]
  have hdiag := lintegral_prefix_diag (W := W) (q := L) a hG h₁ h₂
  have hgoal : ∫⁻ ω, S.indicator (fun ω => F (D ω) ω) ω ∂(μ W L) =
      ∫⁻ ω, G ω ω ∂(μ W L) := rfl
  rw [hgoal, hdiag]
  calc ∫⁻ ω', ∫⁻ ω, G ω' ω ∂(μ W L) ∂(μ W L)
      ≤ ∫⁻ ω', S.indicator (fun _ => b) ω' ∂(μ W L) := by
        refine lintegral_mono fun ω' => ?_
        by_cases hω' : ω' ∈ S
        · simpa [hGdef, Set.indicator_of_mem hω'] using hb ω' hω'
        · simp [hGdef, Set.indicator_of_notMem hω']
    _ = b * μ W L S := by
        rw [lintegral_indicator_const hS]

/-- Conditioning on the first `a` blocks, event form: `P(S ∩ {(D, ω) ∈ T}) ≤ b P(S)` when the
section of `T` at every value `D ω`, `ω ∈ S`, has probability at most `b` and `T` does not see
the first `a` blocks. -/
theorem measure_prefix_le (W L a : ℕ) {X : Type*} [MeasurableSpace X] {D : Ω W L → X}
    (hD : Measurable D) (hDa : PrefixData W L a D) {S : Set (Ω W L)} (hS : MeasurableSet S)
    (hSa : PrefixData W L a (· ∈ S)) {T : Set (X × Ω W L)} (hT : MeasurableSet T)
    (hTa : ∀ d ω ω', (∀ x : Fin L × Fin W × Fin W, a ≤ (x.1 : ℕ) → ω x = ω' x) →
      ((d, ω) ∈ T ↔ (d, ω') ∈ T))
    {b : ℝ≥0∞} (hb : ∀ ω ∈ S, μ W L {ω' | (D ω, ω') ∈ T} ≤ b) :
    μ W L {ω | ω ∈ S ∧ (D ω, ω) ∈ T} ≤ b * μ W L S := by
  have hmeas : Measurable fun ω : Ω W L => (D ω, ω) := hD.prodMk measurable_id
  have hset : {ω | ω ∈ S ∧ (D ω, ω) ∈ T} = S ∩ (fun ω => (D ω, ω)) ⁻¹' T := rfl
  have hmT : MeasurableSet ((fun ω => (D ω, ω)) ⁻¹' T) := hmeas hT
  have h := lintegral_prefix_le W L a hD hDa hS hSa
    (F := fun d ω => T.indicator (fun _ => (1 : ℝ≥0∞)) (d, ω))
    ((measurable_const.indicator hT).comp measurable_id)
    (fun d ω ω' h => by
      by_cases hω : (d, ω) ∈ T
      · have hω' : (d, ω') ∈ T := (hTa d ω ω' h).1 hω
        simp [Set.indicator_of_mem hω, Set.indicator_of_mem hω']
      · have hω' : (d, ω') ∉ T := fun h' => hω ((hTa d ω ω' h).2 h')
        simp [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω'])
    (b := b) (fun ω hω => by
      have hsec : MeasurableSet {ω' | (D ω, ω') ∈ T} := measurable_prodMk_left hT
      have : ∫⁻ ω', T.indicator (fun _ => (1 : ℝ≥0∞)) (D ω, ω') ∂(μ W L) =
          μ W L {ω' | (D ω, ω') ∈ T} := by
        have := lintegral_indicator_one (μ := μ W L) hsec
        simpa [Set.indicator] using this
      rw [this]
      exact hb ω hω)
  have hL : ∫⁻ ω, S.indicator (fun ω => T.indicator (fun _ => (1 : ℝ≥0∞)) (D ω, ω)) ω
      ∂(μ W L) = μ W L {ω | ω ∈ S ∧ (D ω, ω) ∈ T} := by
    rw [hset, ← lintegral_indicator_one (hS.inter hmT)]
    refine lintegral_congr fun ω => ?_
    by_cases h1 : ω ∈ S <;> by_cases h2 : (D ω, ω) ∈ T <;> simp [Set.indicator, h1, h2]
  rw [← hL]
  exact h

end LSBA
