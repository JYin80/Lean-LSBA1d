import Mathlib

/-!
# Cyclic distance

The block distance `‖a - b‖_L = min_{n ∈ ℤ} |a - b + nL|` on the cycle `ℤ_L = Fin L`, as written
before (3.6) [eq:averaged-tail]; used by the kernels of the lower bound and by the counts of the
upper bound.
-/

namespace LSBA

/-- Cyclic distance `‖a - b‖_L` on `ℤ_L = Fin L`. -/
def cycDist {L : ℕ} (a b : Fin L) : ℕ :=
  min ((a.val + L - b.val) % L) ((b.val + L - a.val) % L)

end LSBA
