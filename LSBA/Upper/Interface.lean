import LSBA.Spectral.BlockTail

/-!
# Theorems 3.1 [thm:strong-upper]–3.4 [thm:large-upper] as propositions

The averaged-tail bound (3.6) [eq:averaged-tail] at fixed parameters, and Theorems 3.1
[thm:strong-upper], 3.2 [thm:sharp-small-upper], 3.3 [thm:compact-upper] and 3.4
[thm:large-upper] stated as propositions with the radii (3.7) [eq:strong-radius]–(3.10)
[eq:large-radius]; the proof of (3.11) [uv:eq:upper-count] uses them.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The averaged-tail bound (3.6) [eq:averaged-tail] at fixed `W, L, g`, energy set `J`,
radius `R` and exponents `A, D`. -/
def AveragedTailBound (W L : ℕ) (g : ℝ) (J : Set ℝ) (R A D : ℝ) : Prop :=
  ((W : ℝ) * L)⁻¹ * ∫ ω, (tailCount W L (Hmat g W L ω) J R A : ℝ) ∂(μ W L) ≤ (W : ℝ) ^ (-D)

/-- (3.6) [eq:averaged-tail] passes to a smaller energy set and a larger radius. -/
theorem averagedTailBound_mono {W L : ℕ} {g : ℝ} {J J' : Set ℝ} {R R' A D : ℝ} (hJ : J ⊆ J')
    (hJ' : MeasurableSet J') (hR : R' ≤ R) (h : AveragedTailBound W L g J' R' A D) :
    AveragedTailBound W L g J R A D := by
  have hnn : (0 : ℝ) ≤ ((W : ℝ) * L)⁻¹ := inv_nonneg.2 (by positivity)
  have hle : ∫ ω, (tailCount W L (Hmat g W L ω) J R A : ℝ) ∂(μ W L) ≤
      ∫ ω, (tailCount W L (Hmat g W L ω) J' R' A : ℝ) ∂(μ W L) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg _)
      (integrable_tailCount_Hmat g W L hJ' R' A)
      (Filter.Eventually.of_forall fun ω =>
        Nat.cast_le.2 (tailCount_mono W L (Hmat g W L ω) hJ hR A))
  exact (mul_le_mul_of_nonneg_left hle hnn).trans h

/-- Theorem 3.1 [thm:strong-upper] with (3.7) [eq:strong-radius]: there is `c_* ∈ (0, 1)`
such that for all `A, D > 0` and large `W`, uniformly in `L ≥ 3` and `0 ≤ g ≤ c_* W^{-1/2}`,
(3.6) [eq:averaged-tail] holds with `R = ⌈(log W)²⌉` and `J = ℝ`. -/
def StrongUpper : Prop :=
  ∃ cs : ℝ, 0 < cs ∧ cs < 1 ∧ ∀ A D : ℝ, 0 < A → 0 < D →
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
      g ≤ cs * (W : ℝ) ^ (-(1 / 2 : ℝ)) →
        AveragedTailBound W L g Set.univ (⌈Real.log W ^ 2⌉₊ : ℝ) A D

/-- Theorem 3.2 [thm:sharp-small-upper] with (3.8) [eq:sharp-small-radius]: for
`α ∈ (0, 1/2)`, `c_*, A, D, ε > 0`, `κ ∈ (0, 2)` and large `W`, uniformly in `L ≥ 3` and
`c_* W^{-1/2} ≤ g ≤ W^{-α}`, (3.6) [eq:averaged-tail] holds with `R = W^ε max{1, Wg²}` and
`J = [-2+κ, 2-κ]`. -/
def SharpSmallUpper : Prop :=
  ∀ α cs A D ε κ : ℝ, 0 < α → α < 1 / 2 → 0 < cs → 0 < A → 0 < D → 0 < ε → 0 < κ → κ < 2 →
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ,
      cs * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ g → g ≤ (W : ℝ) ^ (-α) →
        AveragedTailBound W L g (Set.Icc (-2 + κ) (2 - κ))
          ((W : ℝ) ^ ε * max 1 ((W : ℝ) * g ^ 2)) A D

/-- Theorem 3.3 [thm:compact-upper] with (3.9) [eq:coarse-radius]: for `B, E₀, A, D > 0`
and large `W`, uniformly in `L ≥ 3` and `W^{-B} ≤ g ≤ W^B`, (3.6) [eq:averaged-tail] holds with
`R = W max{g^{-2}, g⁴} (log W)²` and `J = [-E₀, E₀]`. -/
def CompactUpper : Prop :=
  ∀ B E₀ A D : ℝ, 0 < B → 0 < E₀ → 0 < A → 0 < D →
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ,
      (W : ℝ) ^ (-B) ≤ g → g ≤ (W : ℝ) ^ B →
        AveragedTailBound W L g (Set.Icc (-E₀) E₀)
          ((W : ℝ) * max (g ^ 2)⁻¹ (g ^ 4) * Real.log W ^ 2) A D

/-- Theorem 3.4 [thm:large-upper] with (3.10) [eq:large-radius]: for `κ ∈ (0, 2)`,
`A, D, ε > 0` and large `W`, uniformly in `L ≥ 3` and `g ≥ W^ε`, (3.6) [eq:averaged-tail] holds with
`R = W g² (log W)²` and `J = [-2+κ, 2-κ]`. -/
def LargeUpper : Prop :=
  ∀ κ A D ε : ℝ, 0 < κ → κ < 2 → 0 < A → 0 < D → 0 < ε →
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, (W : ℝ) ^ ε ≤ g →
      AveragedTailBound W L g (Set.Icc (-2 + κ) (2 - κ))
        ((W : ℝ) * g ^ 2 * Real.log W ^ 2) A D

end LSBA
