import LSBA.Prop.Step45

/-!
# Theorem 5.12(i) [gc:thm:common]: one step

Theorem 5.12 [gc:thm:common] (i) in general form: from (5.22) [gc:eq:one-step-input] at `(g, E, s)`
and at
the comparison points to (5.22) [gc:eq:one-step-input] at every `u ∈ [s, t]` with `θ/2`, under
(5.38)′ [gc:eq:one-step] `R^N ζ_t ≤ W^{-c}`,
`N ≥ N₀(C_w)`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Theorem 5.12(i) [gc:thm:common], general form at fixed times: in a regime with
its inputs, for fixed `c, c_p, θ` and `N ≥ N₀(C_w)`, there is `c_p' > 0` such that on every family
of admissible step points ((5.37) [gc:eq:step-parameters] through the regime, strengthened (5.38)
[gc:eq:one-step]), the estimates (5.22)
[gc:eq:one-step-input] at the start and at the comparison points give (5.39)
[gc:eq:one-step-output] at each deterministic time `u ∈ [s, t]`. -/
theorem theorem412_one (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N : ℝ) (hc : 0 < c)
    (hcp : 0 < cp) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hN : lemmaNN0 I.Cw ≤ N)
    (hinc : IncrementInput R.base R.J) :
    ∃ cp' : ℝ, 0 < cp' ∧ ∀ S : ℕ → Set StepPt, (∀ W, S W ⊆ {q | StepAdm R c N W q}) →
      (∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
        (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W) →
      OneStepInput cp θ (fun q : StepPt => q.at q.s) S →
      OneStepInput cp θ (fun q : StepPt => cmpPt (q.at q.u) q.s) S →
      OneStepInput cp' (θ / 2) (fun q : StepPt => q.at q.u) S := by
  have hN20 : (20 : ℝ) ≤ N := le_trans (le_max_left _ _) hN
  obtain ⟨cp₂, hcp₂, -, hstep2⟩ := step2 R I c cp θ N hc hcp hθ hθ2 hN
  obtain ⟨cp', hcp', hstep5⟩ := step5 R c N cp₂ θ hc hcp₂ hθ hθ2 hN20
  refine ⟨cp', hcp', fun S hS hSu hin hcmp => ?_⟩
  have h1 := step1 R I c cp θ N hc hN20 S hS hin hcmp
  have h2 := hstep2 S hS hSu hin hcmp h1
  have h3 := step3 R I c cp θ N cp₂ hc hcp₂ hθ hθ2 hN hinc S hS hSu hin hcmp h1 h2
  have h4 := step4 R I c cp θ N cp₂ hc hcp₂ hθ hθ2 hN hinc S hS hSu hin hcmp h1 h2 h3
  obtain ⟨h5, -⟩ := hstep5 S hS hSu h2 h3 h4
  exact ⟨h3.loop, h4, h2.avg, h2.entry, h5, h3.tail⟩

end LSBA
