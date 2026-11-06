import LSBA.Prop.Regime

/-!
# The increment input of the propagation theorem

The increment bound (A.49) [da:eq:mixed-profile-increment] of the mixed kernel on the reach of a
base family, the input of the zero-row case of (A.74) [fo:eq:projected-propagation] in Step 3 of
the proof of Theorem 5.12 [gc:thm:common] (Appendix C.3 [sec:gc-one-step]).
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The increment bound (A.49) [da:eq:mixed-profile-increment] of the mixed kernel `P(I-uP)⁻¹` of
(5.13) [fo:eq:pairs] at every point reached from `base` with depth at most `J`, in the linear form
`C/((1-u)ℓ_u) · ‖b-b'‖_L/ℓ_u` with remainder `ℓ_u⁻¹W^{-A}` for every prescribed `A > 0`; `C` does
not depend on `A`. -/
def IncrementInput (base : ℕ → Set FlowPt) (J : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J →
    CmpReach base W d p → ∀ a b b' : Fin p.L,
      |mixedKer (pairP (gammaG p.g) (dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E)))
          p.u a b -
        mixedKer (pairP (gammaG p.g) (dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E)))
          p.u a b'| ≤
      C / ((1 - p.u) * ellProp p.g p.L p.u) * ((cycDist b b' : ℝ) / ellProp p.g p.L p.u) +
        (ellProp p.g p.L p.u)⁻¹ * (W : ℝ) ^ (-A)

end LSBA
