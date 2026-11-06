import LSBA.Upper.CompactRadius
import LSBA.Upper.Angular
import LSBA.Upper.DensityContraction
import LSBA.Upper.GoodBad

/-!
# Theorem 3.3 [thm:compact-upper]

Theorem 3.3 [thm:compact-upper] with the radius (3.9) [eq:coarse-radius] (Section 8.5
[sec:upper-center-completion]): Lemma 8.13 [up:lem:density-contraction] (i) gives, at every
flag, fields with `K_out = 0` at batch length `1000` and `𝔟 = W max{g^{-2}, g⁴} ≥ 1`; Lemma 8.11
[up:lem:angular] turns them into the contraction (8.30) [up:eq:P-contraction] with factor
`1 - c/𝔟`, and Lemma 8.9 [up:lem:good-bad] holds at that length.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Theorem 3.3 [thm:compact-upper] with (3.9) [eq:coarse-radius]. -/
theorem compact_upper : CompactUpper := by
  refine compactUpper_of_contraction good_bad_split ?_
  intro B E₀ hB hE₀
  obtain ⟨C, hC, W₀, h⟩ := density_contraction B E₀ hB hE₀
  obtain ⟨hc0, hc⟩ := angularConst_pos_le hC
  refine ⟨angularConst C, hc0, hc, max W₀ 1, ?_⟩
  intro W hW g E hg1 hg2 hE
  obtain ⟨χ, h1, -⟩ := h W (le_trans (le_max_left _ _) hW)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
  have hg0 : 0 < g := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hg1
  have hm : 1 ≤ max (g⁻¹ ^ 2) (g ^ 4) := by
    rcases le_total g 1 with hg | hg
    · exact le_max_of_le_left (one_le_pow₀ ((one_le_inv₀ hg0).2 hg))
    · exact le_max_of_le_right (one_le_pow₀ hg)
  have hb : 1 ≤ (W : ℝ) * max (g⁻¹ ^ 2) (g ^ 4) := one_le_mul_of_one_le_of_one_le hW1 hm
  exact (angContractionAllAt_of_field_zero hb hC
    (fun x => ⟨χ, h1 g E hg1 hg2 hE x⟩)).angContractionAt

end LSBA
