import LSBA.Prop.RegimeBdd
import LSBA.Prop.RegimeLarge
import LSBA.Sampling.CrudeLarge
import LSBA.Sampling.Residual

/-!
# The inputs of Lemmas 5.8 [uvc:thm:ordinary-sampling] and 5.10 [fo:lem:sampling-continuity]

The crude moments, the sampling inputs and the weighted sampling (5.34)
[fo:eq:weighted-sampling-input] for the bounded-coupling and large-coupling base families of Theorem
5.12 [gc:thm:common], as used by the general theorem: Lemma 5.10 [fo:lem:sampling-continuity] (5.33)
[fo:eq:coarse-time-input]–(5.34) [fo:eq:weighted-sampling-input], Lemma 5.8
[uvc:thm:ordinary-sampling] and Corollary 7.8 [uvc:cor:weighted-sampling].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- the crude moments at bounded coupling (first bound of (5.33) [fo:eq:coarse-time-input],
`‖G‖ ≤ η⁻¹`). -/
theorem crudeInput_bdd (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') (gmin ρ : ℕ → ℝ)
    (hgmin : ∀ W, 0 < gmin W) (hρ : Tendsto ρ atTop atTop) (J : ℕ) :
    CrudeInput (baseBdd C B c' gmin ρ) J := by
  exact crudeInput_of_bdd C B c' hC hB hc' gmin ρ hgmin hρ J (baseBdd C B c' gmin ρ)
    (fun _ _ hp => hp)

/-- the crude moments at large coupling, from Lemma 5.5 [fo:lem:resolvent-moments]. -/
theorem crudeInput_large (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) (J : ℕ) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      CrudeInput (baseLarge κ Cκ CV ρ) J := by
  obtain ⟨Cκ₀, h1, H⟩ := crudeInput_of_large κ CV hκ hκ2 hCV J
  exact ⟨Cκ₀, h1, fun Cκ hCκ ρ hρ => H Cκ hCκ ρ hρ (baseLarge κ Cκ CV ρ) (fun _ _ hp => hp)⟩

/-- Lemma 5.10(b) [fo:lem:sampling-continuity] with Lemma 5.8 [uvc:thm:ordinary-sampling] at bounded
coupling
(polynomial volume, all tuples). -/
theorem samplingInput_bdd (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c')
    (gmin ρ : ℕ → ℝ) (hgmin : ∀ W, 0 < gmin W) (hρ : Tendsto ρ atTop atTop) (J : ℕ) :
    SamplingInput (baseBdd C B c' gmin ρ) J := by
  exact samplingInput_of_bdd C B c' hC hB hc' gmin ρ hgmin hρ J (baseBdd C B c' gmin ρ)
    (fun _ _ hp => hp)

/-- Lemma 5.10(b) [fo:lem:sampling-continuity] with Lemma 5.8 [uvc:thm:ordinary-sampling] at
large coupling. -/
theorem samplingInput_large (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) (J : ℕ) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      SamplingInput (baseLarge κ Cκ CV ρ) J := by
  obtain ⟨Cκ₀, h1, H⟩ := samplingInput_of_large κ CV hκ hκ2 hCV J
  exact ⟨Cκ₀, h1, fun Cκ hCκ ρ hρ => H Cκ hCκ ρ hρ (baseLarge κ Cκ CV ρ) (fun _ _ hp => hp)⟩

/-- The weighted sampling (5.34) [fo:eq:weighted-sampling-input] at bounded coupling with `C_w = 1`
(all pairs). -/
theorem swInput_bdd (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') (gmin ρ : ℕ → ℝ)
    (hgmin : ∀ W, 0 < gmin W) (hρ : Tendsto ρ atTop atTop) (J : ℕ) :
    SwInput (baseBdd C B c' gmin ρ) J 1 := by
  exact swInput_of_bdd C B c' hC hB hc' gmin ρ hgmin hρ J (baseBdd C B c' gmin ρ)
    (fun _ _ hp => hp)

/-- The weighted sampling (5.34) [fo:eq:weighted-sampling-input] at large coupling with `C_w`
depending only on `κ`, fixed before the chain depth. -/
theorem swInput_large (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cw : ℝ, 1 ≤ Cw ∧ ∀ (CV : ℝ), 0 < CV → ∀ J : ℕ, ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ →
      ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop → SwInput (baseLarge κ Cκ CV ρ) J Cw := by
  refine ⟨72, by norm_num, fun CV hCV J => ?_⟩
  obtain ⟨Cκ₀, h1, H⟩ := swInput_of_large κ hκ hκ2 CV hCV J
  exact ⟨Cκ₀, h1, fun Cκ hCκ ρ hρ => H Cκ hCκ ρ hρ (baseLarge κ Cκ CV ρ) (fun _ _ hp => hp)⟩

end LSBA
