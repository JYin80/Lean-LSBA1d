import LSBA.Upper.SharpSmallUnion
import LSBA.Upper.Angular
import LSBA.Upper.SmallContraction
import LSBA.Upper.GoodBad

/-!
# Theorem 3.2 [thm:sharp-small-upper]

Theorem 3.2 [thm:sharp-small-upper] with the radius (3.8) [eq:sharp-small-radius]
(Section 8.5 [sec:upper-center-completion]): in each regime of Lemma 8.12
[up:lem:small-contraction] the fields of local length `q` give, by Lemma 8.11 [up:lem:angular],
the contraction (8.30) [up:eq:P-contraction] with factor `1 - c/𝔟` at length `q`, and then at
the batch length `1000 q`, since the operator of `1000 q` blocks is the `1000`-th power of the
operator of `q` blocks and preserves (8.25) [up:eq:invariant-function]; Lemma 8.9
[up:lem:good-bad] holds at that length.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Lemma 8.11 [up:lem:angular] at local length `q` and the passage to length `1000 q`: fields
with `𝔟 ≥ 1` and `C > 0` at every flag give (8.30) [up:eq:P-contraction] at length `q * 1000`
with factor `1 - c/𝔟`, `c = angularConst C`. -/
private theorem sharpSmall_lift {W : ℕ} {g E : ℝ} {q : ℕ} {b C : ℝ} (hb : 1 ≤ b) (hC : 0 < C)
    (hfield : ∀ x : IsoFlag W, ∃ χ Y, AngularFieldAt W g E q b C x χ Y) :
    AngContractionAt W g E (q * 1000) (1 - angularConst C / b) := by
  obtain ⟨hc0, hc⟩ := angularConst_pos_le hC
  have hb0 : 0 < b := by linarith
  refine angContractionAt_mul ?_ ?_ (angContractionAt_of_field hb hC hfield) (by norm_num)
  · have : angularConst C / b ≤ 1 := (div_le_one hb0).2 (by linarith)
    linarith
  · have : 0 ≤ angularConst C / b := div_nonneg hc0.le hb0.le
    linarith

/-- Theorem 3.2 [thm:sharp-small-upper] with (3.8) [eq:sharp-small-radius]. -/
theorem sharp_small_upper : SharpSmallUpper := by
  refine sharpSmallUpper_of_contraction good_bad_split ?_ ?_
  · intro κ cs θ hκ hκ2 hcs hθ hθ'
    obtain ⟨q, hq7, C, hC, W₀, h⟩ := small_contraction_crit κ cs θ hκ hκ2 hcs hθ hθ'
    obtain ⟨hc0, hc⟩ := angularConst_pos_le hC
    refine ⟨q * 1000, by omega, dvd_mul_left _ _, angularConst C, hc0, hc, max W₀ 1, ?_⟩
    intro W hW g hg1 hg2 E hE
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
    exact sharpSmall_lift (Real.one_le_rpow hW1 (by positivity)) hC
      (h W (le_trans (le_max_left _ _) hW) g hg1 hg2 E hE)
  · intro κ α β ε hκ hκ2 hα hαβ hβ hε
    obtain ⟨q, hq7, C, hC, W₀, h⟩ := small_contraction_weak κ α β ε hκ hκ2 hα hαβ hβ hε
    obtain ⟨hc0, hc⟩ := angularConst_pos_le hC
    refine ⟨q * 1000, by omega, dvd_mul_left _ _, angularConst C, hc0, hc, max W₀ 1, ?_⟩
    intro W hW a ha E hE
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
    have hW0 : (0 : ℝ) < W := by linarith
    have h1 : 1 ≤ (W : ℝ) ^ (ε / 2) := Real.one_le_rpow hW1 (by positivity)
    have h2 : (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (W : ℝ) ^ (-a) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by linarith [ha.2])
    have h3 : ((W : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (W : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
      norm_num
      exact Real.rpow_neg_one _
    have h4 : 1 ≤ (W : ℝ) * ((W : ℝ) ^ (-a)) ^ 2 := by
      have : (W : ℝ)⁻¹ ≤ ((W : ℝ) ^ (-a)) ^ 2 :=
        h3 ▸ pow_le_pow_left₀ (by positivity) h2 2
      calc (1 : ℝ) = (W : ℝ) * (W : ℝ)⁻¹ := (mul_inv_cancel₀ hW0.ne').symm
        _ ≤ _ := by gcongr
    have hb : 1 ≤ (W : ℝ) ^ (ε / 2) * W * ((W : ℝ) ^ (-a)) ^ 2 := by
      calc (1 : ℝ) ≤ (W : ℝ) ^ (ε / 2) * ((W : ℝ) * ((W : ℝ) ^ (-a)) ^ 2) :=
            one_le_mul_of_one_le_of_one_le h1 h4
        _ = _ := by ring
    exact sharpSmall_lift hb hC (h W (le_trans (le_max_left _ _) hW) a ha E hE)

end LSBA
