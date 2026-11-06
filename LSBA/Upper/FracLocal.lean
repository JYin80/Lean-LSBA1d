import LSBA.Upper.ConversionEndpoint
import LSBA.Upper.NearZeroTransfer

/-!
# From high-probability transfer growth to the endpoint moment

Proposition 8.4 [up:prop:conversion] (i): the transfer input (8.11) [up:eq:input] at a large
fixed exponent gives the endpoint bound (8.6) [uv:eq:upper-volume-input] with `s = t`, through
the boundary comparison (8.14) [eq:c-boundary-comparison] and (8.7) [eq:c-apriori].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Proposition 8.4 [up:prop:conversion] (i): for fixed `C₀ ≥ 1` and `t ∈ (0, 1/2)` there are
`D′ > 0` and a width threshold, independent of `g, J, n`, such that for `0 < g ≤ W^{C₀}`, every
energy set `J` and every `n ≥ 1`, (8.11) [up:eq:input] at exponent `D′` and length `n` gives
(8.6) [uv:eq:upper-volume-input] with `s = t` at the same length. -/
theorem frac_local_of_growth {C₀ t : ℝ} (hC₀ : 1 ≤ C₀) (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    ∃ D' : ℝ, 0 < D' ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, 0 < g → g ≤ (W : ℝ) ^ C₀ →
      ∀ (J : Set ℝ) (n : ℕ), 1 ≤ n → TransferInputAt W g J D' n →
        EndpointMomentAt W g J t n ((W : ℝ) ^ (-2 : ℝ)) := by
  have hB : 0 < C₀ := by linarith
  refine ⟨endpointExponent 2 t C₀, by unfold endpointExponent; positivity,
    ⌈2 * aprioriConst t + Real.sqrt (aprioriConst (2 * t))⌉₊, ?_⟩
  intro W hW g hg0 hgB J n hn hT
  exact endpointMoment_of_transferInput ht0 ht1 two_pos hB (Nat.ceil_le.1 hW) hg0 hgB hn hT

end LSBA
