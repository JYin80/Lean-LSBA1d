import LSBA.Upper.FracMoment
import LSBA.Upper.LargeAverageUpper

/-!
# From energy-averaged fractional moments to concentration

Lemma 8.1 [uva:thm:upper-audit] (ii): the energy-averaged bound (8.3) [uva:eq:conversion-input]
on Dirichlet paths at `g ≥ W`, `𝔟 = W g²` gives (3.6) [eq:averaged-tail] on every finite cycle,
with block radius (8.4) [uva:eq:conversion-radius], through (E.3) [uva:eq:cell-correlator] to
(E.13) [uva:eq:weight-audit] (Appendix E.1 [app:fr-concentration-proof]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Lemma 8.1 [uva:thm:upper-audit] (ii): for fixed `E₀ < 2`, `q ∈ (0, 1)` and `C, c, A, D > 0`
there are `C_D` and a width threshold, independent of `L, g`, such that for `g ≥ W` the bound
(8.3) [uva:eq:conversion-input] on `J = [-E₀, E₀]` with `𝔟 = W g²` on all Dirichlet paths gives
(3.6) [eq:averaged-tail] on the cycle of `L` blocks with `R = C_D W g² log W`. -/
theorem frac_concentration_averaged {E₀ q C c : ℝ} (hE₀ : E₀ < 2) (hq0 : 0 < q) (hq1 : q < 1)
    (hC : 0 < C) (hc : 0 < c) (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ CD : ℝ, 0 < CD ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, ∀ g : ℝ, (W : ℝ) ≤ g →
      (∀ m : ℕ, AvgFracPath W m g (Set.Icc (-E₀) E₀) q C c (W * g ^ 2)) →
        AveragedTailBound W L g (Set.Icc (-E₀) E₀) (CD * W * g ^ 2 * Real.log W) A D := by
  obtain ⟨C₁, c₁, P, hC₁, hc₁, hP, W₁, hcor⟩ := cell_correlator_of_path (CG := 1) (cG := c)
    (PG := C) hE₀ hq0 hq1 one_pos hc hC.le
  obtain ⟨K, hK, W₂, htail⟩ := averaged_tail_of_correlator (E₀ := E₀) hC₁ hc₁ hP A D hA hD
  refine ⟨K, hK, max (max W₁ W₂) (max 1 ⌈2 + 4 / (2 - E₀)⌉₊), ?_⟩
  intro W hW L g hg hpath
  have hW₁ : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW₂ : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW1 : (1 : ℝ) ≤ W := by
    exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWM : 2 + 4 / (2 - E₀) ≤ (W : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW)
  have hg1 : 1 ≤ g := hW1.trans hg
  have hg0 : 0 < g := by linarith
  have hg2 : (W : ℝ) ≤ g ^ 2 := by nlinarith
  have hM : 2 + 4 / (2 - E₀) ≤ g ^ 2 := hWM.trans hg2
  exact htail W hW₂ L g hg0.le (by nlinarith) fun a b nA nB d h1 h2 h3 h4 hd =>
    hcor W hW₁ g hg0 hM (fun m x y => by simpa only [one_mul] using hpath m x y) L a b nA nB d
      h1 h2 h3 h4 hd _ measurableSet_Icc subset_rfl

end LSBA
