import LSBA.Upper.LargeAverageUpper
import LSBA.Upper.NearZeroTransfer
import LSBA.Upper.ConversionEndpoint
import LSBA.Upper.ConversionCycle
import LSBA.Upper.CorrelatorDecay
import LSBA.Upper.CorrelatorCount
import LSBA.Upper.Interface
import LSBA.Upper.DensityContraction
import LSBA.Upper.Angular
import LSBA.Upper.GoodBad
import LSBA.Upper.OperatorLength
import LSBA.Upper.TailUnion
import LSBA.Upper.FracAvgPath
import LSBA.Upper.FracAveraged
import LSBA.Upper.FracConcentration
import LSBA.Upper.LargeFracCycle

/-!
# Theorem 3.4 [thm:large-upper]: concentration at large coupling

Theorem 3.4 [thm:large-upper] with the radius (3.10) [eq:large-radius]. For `W^ε ≤ g < W`
the near-zero window `[−2κ₁, 2κ₁]` and the two intervals `[κ₁, 2 − κ]`, `[−2 + κ, −κ₁]` each
give (3.6) [eq:averaged-tail] with the exponent `D + 2` at the radius `⌈C W g² log W⌉`; they
cover `[−2 + κ, 2 − κ]`, the exceptional proportions add up to at most `W^{-D}`, and the radius
is at most `W g² (log W)²` once `log W ≥ C + 1`.

Theorem 3.4 [thm:large-upper] itself is proved as in Section 11 [sec:large-upper-proof], split at
`g = W`: for `g ≥ W` by Proposition 8.4 [up:prop:conversion] (ii) and Lemma 8.1
[uva:thm:upper-audit] (ii); for `W^ε ≤ g < W` by (8.2) [up:eq:fmr-pointwise] on `[−2 + κ, 2 − κ]`
and Lemma 8.1 (i) [uva:thm:upper-audit].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `⌈C W g² log W⌉ ≤ W g² (log W)²` for `g ≥ 1`, `C ≥ 0` and `log W ≥ C + 1`. -/
private theorem largeUpper_ceil_le {W : ℕ} {g C : ℝ} (hC : 0 ≤ C) (hg : 1 ≤ g)
    (hlog : C + 1 ≤ Real.log W) :
    (⌈C * W * g ^ 2 * Real.log W⌉₊ : ℝ) ≤ (W : ℝ) * g ^ 2 * Real.log W ^ 2 := by
  have hl1 : 1 ≤ Real.log W := by linarith
  have hW : (1 : ℝ) ≤ W := by
    by_contra h
    have h := not_le.mp h
    have : Real.log W ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h.le
    linarith
  have hx : 1 ≤ (W : ℝ) * g ^ 2 * Real.log W := by
    have : 1 ≤ g ^ 2 := one_le_pow₀ hg
    have h1 : 1 ≤ (W : ℝ) * g ^ 2 := by nlinarith
    nlinarith
  calc (⌈C * W * g ^ 2 * Real.log W⌉₊ : ℝ) ≤ C * W * g ^ 2 * Real.log W + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
    _ ≤ (C + 1) * ((W : ℝ) * g ^ 2 * Real.log W) := by nlinarith
    _ ≤ Real.log W * ((W : ℝ) * g ^ 2 * Real.log W) := by gcongr
    _ = (W : ℝ) * g ^ 2 * Real.log W ^ 2 := by ring

/-- Theorem 3.4 [thm:large-upper] with (3.10) [eq:large-radius], split at `g = W`. For `g ≥ W`:
Theorem 11.1 [uvg:thm:transfer], Proposition 8.4 [up:prop:conversion] (ii) and Lemma 8.1
[uva:thm:upper-audit] (ii). For `W^ε ≤ g < W`: (8.2) [up:eq:fmr-pointwise] on the union of three
energy intervals and Lemma 8.1 (i) [uva:thm:upper-audit]. -/
theorem large_upper : LargeUpper := by
  intro κ A D ε hκ hκ2 hA hD hε
  have hE₀ : 2 - κ < 2 := by linarith
  have hJ : Set.Icc (-2 + κ) (2 - κ) = Set.Icc (-(2 - κ)) (2 - κ) := by
    congr 1
    ring
  -- `g ≥ W`
  obtain ⟨Cs, C, c, s, hCs, hC, hc, hs0, hs1, W₁, hT⟩ := negative_transfer_moment hE₀
  obtain ⟨C', c', hC', hc', W₂, hAF⟩ := frac_avg_of_negative_moment hE₀ hs0 hs1 hC hc
  obtain ⟨Ch, hCh, W₃, hAT⟩ := frac_concentration_averaged hE₀ (q := s / 4) (by positivity)
    (by linarith) hC' hc' A D hA hD
  -- `W^ε ≤ g < W`
  have hε0 : 0 < min ε (1 / 2) := lt_min hε (by norm_num)
  obtain ⟨Cf, cf, hCf, hcf, W₄, hFC⟩ := large_frac_cycle hκ hκ2 hε0
    (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
  obtain ⟨Cm, hCm, W₅, hFT⟩ := frac_concentration_fixed (C₀ := 3) (E₀ := 2 - κ) (q := 1 / 8)
    (by norm_num) (by linarith) (by norm_num) (by norm_num) hCf hcf A D hA hD
  refine ⟨max (max (max W₁ W₂) (max W₃ W₄)) (max W₅ (max 3 (max ⌈Cs ^ 2⌉₊
    ⌈Real.exp (max Ch Cm + 1)⌉₊))), fun W hW L hL g hg => ?_⟩
  have hW₁ : W₁ ≤ W := by omega
  have hW₂ : W₂ ≤ W := by omega
  have hW₃ : W₃ ≤ W := by omega
  have hW₄ : W₄ ≤ W := by omega
  have hW₅ : W₅ ≤ W := by omega
  have hW3 : 3 ≤ W := by omega
  have hW3' : (3 : ℝ) ≤ W := by exact_mod_cast hW3
  have hWr : (1 : ℝ) ≤ W := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hCs2 : Cs ^ 2 ≤ (W : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (by omega : ⌈Cs ^ 2⌉₊ ≤ W))
  have hWe : Real.exp (max Ch Cm + 1) ≤ (W : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (by omega : ⌈Real.exp (max Ch Cm + 1)⌉₊ ≤ W))
  have hlog : max Ch Cm + 1 ≤ Real.log W := by
    rw [← Real.log_exp (max Ch Cm + 1)]
    exact Real.log_le_log (Real.exp_pos _) hWe
  have hg1 : 1 ≤ g := le_trans (Real.one_le_rpow hWr hε.le) hg
  by_cases hgW : (W : ℝ) ≤ g
  · have hCsg : Cs * Real.sqrt W ≤ g := by
      have h1 : Cs ≤ Real.sqrt W := Real.le_sqrt_of_sq_le hCs2
      calc Cs * Real.sqrt W ≤ Real.sqrt W * Real.sqrt W := by gcongr
        _ = W := Real.mul_self_sqrt hW0.le
        _ ≤ g := hgW
    have h := hAT W hW₃ L g hgW (hAF W hW₂ g hgW fun n _ E hE Φ hΦ =>
      hT W hW₁ g hCsg n E (abs_le.mpr hE) Φ hΦ)
    rw [hJ]
    refine averagedTailBound_mono subset_rfl measurableSet_Icc ?_ h
    have hlC : Ch ≤ Real.log W := by linarith [le_max_left Ch Cm]
    have hlog0 : 0 ≤ Real.log W := hCh.le.trans hlC
    have hWg : 0 ≤ (W : ℝ) * g ^ 2 * Real.log W := by positivity
    calc Ch * W * g ^ 2 * Real.log W = Ch * ((W : ℝ) * g ^ 2 * Real.log W) := by ring
      _ ≤ Real.log W * ((W : ℝ) * g ^ 2 * Real.log W) := by gcongr
      _ = (W : ℝ) * g ^ 2 * Real.log W ^ 2 := by ring
  · replace hgW := not_le.mp hgW
    have hg' : (W : ℝ) ^ min ε (1 / 2) ≤ g :=
      (Real.rpow_le_rpow_of_exponent_le hWr (min_le_left _ _)).trans hg
    have hb1 : (1 : ℝ) ≤ (W : ℝ) * g ^ 2 := by nlinarith
    have hbW : (W : ℝ) * g ^ 2 ≤ (W : ℝ) ^ (3 : ℝ) := by
      have h1 : (W : ℝ) * g ^ 2 ≤ W * W ^ 2 := by gcongr
      calc (W : ℝ) * g ^ 2 ≤ W * W ^ 2 := h1
        _ = (W : ℝ) ^ (3 : ℝ) := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          ring
    have hgW3 : g ≤ (W : ℝ) ^ (3 : ℝ) := by
      calc g ≤ (W : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hgW.le
        _ ≤ (W : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hWr (by norm_num)
    have h := hFT W hW₅ L hL g ((W : ℝ) * g ^ 2) (by linarith) hgW3 hb1 hbW _ measurableSet_Icc
      (by rw [hJ]) (hFC W hW₄ g hg' hgW L hL)
    refine averagedTailBound_mono subset_rfl measurableSet_Icc ?_ h
    rw [show Cm * ((W : ℝ) * g ^ 2) * Real.log W = Cm * W * g ^ 2 * Real.log W by ring]
    exact largeUpper_ceil_le hCm.le hg1 (by linarith [le_max_right Ch Cm])

end LSBA
