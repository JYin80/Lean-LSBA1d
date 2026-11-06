import LSBA.Prop.Regime
import LSBA.Volume.LocalComparison

/-!
# Step data of the one-step propagation

Step points `(s, t)` with the time ratio, the admissibility of a step (the (5.38)′ [gc:eq:one-step]
condition
`R^N ζ_t ≤ W^{-c}`), and the outputs of Steps 1–3 of Appendix C.3
[sec:gc-one-step].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- A deterministic step point: `(g, E, L)`, a time step `[s, t]` and a time `u`. -/
structure StepPt where
  g : ℝ
  E : ℝ
  L : ℕ
  s : ℝ
  t : ℝ
  u : ℝ

/-- The point `(g, E, L, v)` of a step point. -/
def StepPt.at (q : StepPt) (v : ℝ) : FlowPt := ⟨q.g, q.E, q.L, v⟩

/-- `R = (1 - s)/(1 - t)`. -/
def StepPt.ratio (q : StepPt) : ℝ := (1 - q.s) / (1 - q.t)

/-- Admissible step points of Theorem 5.12(i) [gc:thm:common] in a regime: the endpoint
`(g, E, L, t)` is reached with depth `d < J`, `1/2 ≤ s ≤ u ≤ t`, `s < t`, `1 - t ≥ W^{-3}`, and
the strengthened (5.38) [gc:eq:one-step] `R^N ζ_t ≤ W^{-c}`. -/
def StepAdm (R : PropRegime) (c N : ℝ) (W : ℕ) (q : StepPt) : Prop :=
  (∃ d : ℕ, d < R.J ∧ CmpReach R.base W d (q.at q.t)) ∧ 1 / 2 ≤ q.s ∧ q.s ≤ q.u ∧ q.u ≤ q.t ∧
    q.s < q.t ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - q.t ∧ q.ratio ^ N * zetaProp q.g W q.L q.t ≤ (W : ℝ) ^ (-c)

open scoped Matrix.Norms.L2Operator in
/-- The goal (C.5) [fo:eq:step1] of Step 1 and (C.6) [fo:eq:step1-density] at the time `u` of each
step point, with the maxima inside the probability. -/
structure Step1Out (S : ℕ → Set StepPt) : Prop where
  op : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
    (fun W q ab ω => ((‖blockOf (flowG W (q.at q.u) ω) ab.1 ab.2‖ : ℝ) : ℂ))
    (fun W q _ => W * q.ratio * zetaProp q.g W q.L q.u)
  hs : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
    (fun W q ab ω => ((blockHS2 (flowG W (q.at q.u) ω) ab.1 ab.2 : ℝ) : ℂ))
    (fun W q _ => (W : ℝ) ^ 2 * q.ratio * zetaProp q.g W q.L q.u)
  avg : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L)
    (fun W q a ω => blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) a a)
    (fun W q _ => q.ratio ^ 2 * zetaProp q.g W q.L q.u)
  loop : ∀ k : ℕ, 1 ≤ k → PrecMax StepPt.L S (Λ := fun _ q => Word k q.L)
    (fun W q w ω => loopTr (flowG W (q.at q.u) ω) w.1 w.2)
    (fun W q _ => (q.ratio * zetaProp q.g W q.L q.u) ^ (k - 1))
  density : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L)
    (fun W q a ω => (((blockTr (flowG W (q.at q.u) ω) a a).im : ℝ) : ℂ)) (fun _ _ _ => 1)

/-- The goal (C.15) [fo:eq:step2] of Step 2 with the spatial loss `R^6` in place of `R^{10}`
(the mixed pair after the mixed-pair bound and the propagated pair estimate), and the sharp local
law. -/
structure Step2Out (cp θ : ℝ) (S : ℕ → Set StepPt) : Prop where
  pair : ∀ F : ℝ, 0 < F → PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
    (fun W q ab ω => flowErr W (q.at q.u) ![ab.1, ab.2] ![true, false] ω)
    (fun W q ab => q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2 *
      weightFn cp θ F W (ellProp q.g q.L q.u) (cycDist ab.1 ab.2))
  hs : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
    (fun W q ab ω => ((blockHS2 (flowG W (q.at q.u) ω) ab.1 ab.2 : ℝ) : ℂ))
    (fun W q _ => (W : ℝ) ^ 2 * zetaProp q.g W q.L q.u)
  entry : PrecMax StepPt.L S (Λ := fun W q => (Fin q.L × Fin W) × (Fin q.L × Fin W))
    (fun W q e ω => (flowG W (q.at q.u) ω - flowM W (q.at q.u)) e.1 e.2)
    (fun W q _ => Real.sqrt (zetaProp q.g W q.L q.u))
  avg : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
    (fun W q ab ω => blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) ab.1 ab.2)
    (fun W q _ => zetaProp q.g W q.L q.u)

/-- The goals of Step 3: the joint tails (C.29) [fo:eq:step5-tails], the same-sign pair bound
`R^{7/2}`, the actual loops (C.27) [fo:eq:step3] and the intermediate errors
(C.28) [fo:eq:step3-error]. -/
structure Step3Out (S : ℕ → Set StepPt) : Prop where
  tail : ∀ k : ℕ, 2 ≤ k → ∀ ε A : ℝ, 0 < ε → 0 < A → PrecMax StepPt.L S
    (Λ := fun W q => {w : Word k q.L // (W : ℝ) ^ ε * ellProp q.g q.L q.u < wordDiam w.1})
    (fun W q w ω => ((‖loopTr (flowG W (q.at q.u) ω) w.1.1 w.1.2‖ +
      ‖flowErr W (q.at q.u) w.1.1 w.1.2 ω‖ : ℝ) : ℂ))
    (fun W _ _ => (W : ℝ) ^ (-A))
  same : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L × Bool)
    (fun W q x ω => flowErr W (q.at q.u) ![x.1, x.2.1] ![x.2.2, x.2.2] ω)
    (fun W q _ => q.ratio ^ ((7 : ℝ) / 2) * zetaProp q.g W q.L q.u ^ 2)
  loop : ∀ k : ℕ, 1 ≤ k → PrecMax StepPt.L S (Λ := fun _ q => Word k q.L)
    (fun W q w ω => loopTr (flowG W (q.at q.u) ω) w.1 w.2)
    (fun W q _ => zetaProp q.g W q.L q.u ^ (k - 1))
  err : ∀ k : ℕ, 1 ≤ k → PrecMax StepPt.L S (Λ := fun _ q => Word k q.L)
    (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
    (fun W q _ => (Real.sqrt (zetaProp q.g W q.L q.s))⁻¹ * zetaProp q.g W q.L q.u ^ k)

end LSBA
