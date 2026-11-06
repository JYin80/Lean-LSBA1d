import LSBA.Upper.Operator
import LSBA.Gauss.Divergence

/-!
# The hypotheses of Lemma 8.11 [up:lem:angular]

The cutoff and field hypotheses of Lemma 8.11 [up:lem:angular] at one energy and incoming flag,
in the standard Gaussian coordinates of `Ω W q`: (8.34) [up:eq:angular-geometry] in projection
coordinates wherever the cutoff is nonzero, Gaussian integration by parts for the cut field, and
(8.35) [up:eq:field]; the variant with `K_out = 0`; the logarithmic ratio `log R_T(Y)` of the
proof; and the contraction constant.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- (8.34) [up:eq:angular-geometry] at the sample `ω`, in projection coordinates: along `Y ω`,
the cocycle `c(T; U, Y)` has derivative `1` and the terminal flag `(P_{TU}, P_{TY})` has
derivative `([1 ⊗ K, P_{TU}], [1 ⊗ K, P_{TY}])`, the first-order motion under
`diag(e^{tK}, e^{tK})`. -/
def FlagFieldGeom (W : ℕ) (g E : ℝ) (q : ℕ) (x : IsoFlag W) (Y : Ω W q → Ω W q) (ω : Ω W q)
    (K : Matrix (Fin W) (Fin W) ℂ) : Prop :=
  HasLineDerivAt ℝ (fun η : Ω W q => volCocycle (batchMat W g E q η) x) 1 ω (Y ω) ∧
  HasLineDerivAt ℝ (fun η : Ω W q => ((flagAct (batchMat W g E q η) x : IsoFlag W) :
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))
    (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) * (flagAct (batchMat W g E q ω) x).1.1 -
        (flagAct (batchMat W g E q ω) x).1.1 * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K),
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) * (flagAct (batchMat W g E q ω) x).1.2 -
        (flagAct (batchMat W g E q ω) x).1.2 * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K))
    ω (Y ω)

/-- The hypotheses of Lemma 8.11 [up:lem:angular] at the incoming flag `x`: a measurable cutoff
`0 ≤ χ ≤ 1` and a field `Y` on `Ω W q`; (8.34) [up:eq:angular-geometry] wherever `χ ≠ 0`, with a
skew-Hermitian K_out; Gaussian integration by parts for `χ Y`; and (8.35) [up:eq:field]: `𝔼 χ ≥ ½`
and `𝔼 |δ_G (χ Y)|² ≤ C 𝔟`. -/
def AngularFieldAt (W : ℕ) (g E : ℝ) (q : ℕ) (b C : ℝ) (x : IsoFlag W) (χ : Ω W q → ℝ)
    (Y : Ω W q → Ω W q) : Prop :=
  Measurable χ ∧ (∀ ω, 0 ≤ χ ω ∧ χ ω ≤ 1) ∧
  (∀ ω, χ ω ≠ 0 → ∃ K : Matrix (Fin W) (Fin W) ℂ, Kᴴ = -K ∧ FlagFieldGeom W g E q x Y ω K) ∧
  IBPAdmissible (fun ω => χ ω • Y ω) ∧
  (1 / 2 : ℝ) ≤ ∫ ω, χ ω ∂(μ W q) ∧
  ∫⁻ ω, ‖gaussDiv (fun η => χ η • Y η) ω‖ₑ ^ 2 ∂(μ W q) ≤ ENNReal.ofReal (C * b)

/-- The hypotheses of Lemma 8.11 [up:lem:angular] at the incoming flag `x` with `K_out = 0`
throughout `{χ ≠ 0}`. -/
def AngularFieldZeroAt (W : ℕ) (g E : ℝ) (q : ℕ) (b C : ℝ) (x : IsoFlag W) (χ : Ω W q → ℝ)
    (Y : Ω W q → Ω W q) : Prop :=
  Measurable χ ∧ (∀ ω, 0 ≤ χ ω ∧ χ ω ≤ 1) ∧
  (∀ ω, χ ω ≠ 0 → FlagFieldGeom W g E q x Y ω 0) ∧
  IBPAdmissible (fun ω => χ ω • Y ω) ∧
  (1 / 2 : ℝ) ≤ ∫ ω, χ ω ∂(μ W q) ∧
  ∫⁻ ω, ‖gaussDiv (fun η => χ η • Y η) ω‖ₑ ^ 2 ∂(μ W q) ≤ ENNReal.ofReal (C * b)

/-- `log R_T(Y) = -log ρ(Y) - 2 c(T; U, Y) + 4 log h(TU, TY)` in the proof of Lemma 8.11
[up:lem:angular], with `r = ρ(Y)` and `T = T(ω)`. -/
def logAngRatio (W : ℕ) (g E : ℝ) (q : ℕ) (h : IsoFlag W → ℝ) (r : ℝ) (y : IsoFlag W)
    (ω : Ω W q) : ℝ :=
  -Real.log r - 2 * volCocycle (batchMat W g E q ω) y +
    4 * Real.log (h (flagAct (batchMat W g E q ω) y))

/-- The contraction constant `c = min{1, 1/(9C)}/128` of Lemma 8.11 [up:lem:angular] for the
field bound `C` of (8.35) [up:eq:field]. -/
def angularConst (C : ℝ) : ℝ := min 1 (1 / (9 * C)) / 128

end LSBA
