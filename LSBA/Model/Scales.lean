import Mathlib

/-!
# Localization scales

The scales `ℓ_{W,g}` and `ℓ_{W,g,L}` of (1.7) [eq:scales].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The uncapped scale `ℓ_{W,g} = max{W, W²g²}`, (1.7) [eq:scales]. -/
def ellScale (W : ℕ) (g : ℝ) : ℝ := max (W : ℝ) ((W : ℝ) ^ 2 * g ^ 2)

/-- The finite-volume scale `ℓ_{W,g,L} = min{WL, ℓ_{W,g}}`, (1.7) [eq:scales]. -/
def ellStar (W L : ℕ) (g : ℝ) : ℝ := min ((W : ℝ) * L) (ellScale W g)

end LSBA
