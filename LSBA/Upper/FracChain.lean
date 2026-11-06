import LSBA.Upper.FracConcentration
import LSBA.Upper.FracCriterion
import LSBA.Upper.FracLocal
import LSBA.Upper.OperatorLength
import LSBA.Upper.OperatorIteration
import LSBA.Upper.GoodBad
import LSBA.Upper.DensityContraction
import LSBA.Upper.Angular

/-!
# From contraction to concentration

The chain common to the proofs of Theorems 3.2 [thm:sharp-small-upper] and 3.3 [thm:compact-upper]
(Section 8.5 [sec:upper-center-completion]). Lemmas 8.9 [up:lem:good-bad], 8.10
[up:lem:operator-iteration] and 8.6 [up:lem:operator-reduction] turn the contraction (8.30)
[up:eq:P-contraction] at one batch length into the transfer input (8.11) [up:eq:input] at a length
`n ≤ C 𝔟 log W`. Proposition 8.4 [up:prop:conversion] (i), Proposition 8.2
[up:prop:fr-concentration] and Lemma 8.1 [uva:thm:upper-audit] (i) turn (8.11) [up:eq:input] into
(3.6)
[eq:averaged-tail] with `R = ⌈C_D 𝔟 log W⌉`. The exponent `D′` is fixed from the range of `g`
alone, before the length constant.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Lemmas 8.9 [up:lem:good-bad], 8.10 [up:lem:operator-iteration] and 8.6
[up:lem:operator-reduction] over a class with `W^{-B} ≤ g ≤ W^B`, `𝔟 ≥ 1` and `J ⊆ [-E₀, E₀]`: the
contraction (8.30) [up:eq:P-contraction] with factor `1 - c/𝔟`, `0 < c ≤ 1/4`, at one length
`q ≥ 1000` divisible by `1000` and at every `E ∈ J` of the class gives, for every `D′ > 0`, the
transfer input (8.11) [up:eq:input] at one length `1 ≤ n ≤ C 𝔟 log W`, with `C` and the width
threshold independent of `g, 𝔟, J`. -/
theorem transferLength_of_contraction (hsplit : GoodBadSplit) {B E₀ : ℝ} (hB : 0 < B)
    (hE₀ : 0 < E₀) {adm : ℕ → ℝ → ℝ → Set ℝ → Prop}
    (hadm : ∀ W g b J, adm W g b J → (W : ℝ) ^ (-B) ≤ g ∧ g ≤ (W : ℝ) ^ B ∧ 1 ≤ b ∧
      J ⊆ Set.Icc (-E₀) E₀)
    {q : ℕ} (hq : 1000 ≤ q) (hq' : 1000 ∣ q) {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 4)
    (hcon : ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ g b : ℝ, ∀ J : Set ℝ, adm W g b J → ∀ E ∈ J,
      AngContractionAt W g E q (1 - c / b))
    (D' : ℝ) (hD' : 0 < D') :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g b : ℝ, ∀ J : Set ℝ, adm W g b J →
      ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ C * b * Real.log W ∧ TransferInputAt W g J D' n := by
  obtain ⟨C₁, W₂, hpd⟩ := powerDecay_of_contraction hsplit hB hE₀ hq hq' hc0 hc
  obtain ⟨W₁, hW₁⟩ := hcon
  obtain ⟨C, W₃, hC⟩ := transferGrowth_of_powerDecay hB hE₀ (q := q) (by omega) hadm
    ⟨c, C₁, hc0, max W₁ W₂, fun W hW g b J hJ E hE => by
      obtain ⟨hg1, hg2, hb, hJE⟩ := hadm W g b J hJ
      exact hpd W (le_trans (le_max_right _ _) hW) g E b hg1 hg2 (abs_le.2 (hJE hE)) hb
        (hW₁ W (le_trans (le_max_left _ _) hW) g b J hJ E hE)⟩ D' hD'
  refine ⟨max C 1, by positivity, max W₃ 3, ?_⟩
  intro W hW g b J hJ
  obtain ⟨n, h2, hn, hT⟩ := hC W (le_trans (le_max_left _ _) hW) g b J hJ
  have hW3 : (3 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
  have hlog : 1 ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_three]
  obtain ⟨-, -, hb, -⟩ := hadm W g b J hJ
  have hn1 : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    subst h0
    simp at h2
    linarith
  refine ⟨n, hn1, hn.trans ?_, hT⟩
  have hbl : 0 ≤ b * Real.log W := by positivity
  calc C * b * Real.log W = C * (b * Real.log W) := by ring
    _ ≤ max C 1 * (b * Real.log W) := mul_le_mul_of_nonneg_right (le_max_left _ _) hbl
    _ = _ := by ring

/-- The chain Proposition 8.4(i) [up:prop:conversion] → Proposition 8.2 [up:prop:fr-concentration]
→ Lemma 8.1(i) [uva:thm:upper-audit] of Section 8.5 [sec:upper-center-completion]: for fixed
`B, B_b` and `E₀ > 0` there is `D′ > 0` such that for every length constant `C_n > 0` and all
`A, D > 0` there are `C_D` and a width threshold, independent of `L, g, 𝔟, J, n`, such that
(8.11) [up:eq:input] at exponent `D′` and one length `1 ≤ n ≤ C_n 𝔟 log W` gives (3.6)
[eq:averaged-tail] with `R = ⌈C_D 𝔟 log W⌉`, for `L ≥ 3`, `0 < g ≤ W^B`, `1 ≤ 𝔟 ≤ W^{B_b}` and
measurable `J ⊆ [-E₀, E₀]`. -/
theorem frac_tail_of_transfer {B Bb E₀ : ℝ} (hE₀ : 0 < E₀) :
    ∃ D' : ℝ, 0 < D' ∧ ∀ Cn : ℝ, 0 < Cn → ∀ A D : ℝ, 0 < A → 0 < D →
      ∃ CD : ℝ, 0 < CD ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g b : ℝ, 0 < g →
        g ≤ (W : ℝ) ^ B → 1 ≤ b → b ≤ (W : ℝ) ^ Bb → ∀ J : Set ℝ, MeasurableSet J →
        J ⊆ Set.Icc (-E₀) E₀ → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ Cn * b * Real.log W →
        TransferInputAt W g J D' n →
          AveragedTailBound W L g J (⌈CD * b * Real.log W⌉₊ : ℝ) A D := by
  obtain ⟨D', hD', W₁, hloc⟩ := frac_local_of_growth (C₀ := max 1 B) (t := 1 / 4)
    (le_max_left _ _) (by norm_num) (by norm_num)
  refine ⟨D', hD', fun Cn hCn A D hA hD => ?_⟩
  set C₀ : ℝ := max (max 1 B) (max Bb Cn) with hC₀
  have hC₀1 : 1 ≤ C₀ := (le_max_left 1 B).trans (le_max_left _ _)
  have hBC : max 1 B ≤ C₀ := le_max_left _ _
  have hBbC : Bb ≤ C₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hCnC : Cn ≤ C₀ := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨C, c, hC, hc, W₂, hcrit⟩ := frac_criterion (C₀ := C₀) (s := 1 / 4) hC₀1 (by norm_num)
    (by norm_num)
  obtain ⟨CD, hCD, W₃, hconc⟩ := frac_concentration_fixed (C₀ := C₀) (E₀ := E₀)
    (q := (1 / 4) / 2) (C := C) (c := c) hC₀1 hE₀ (by norm_num) (by norm_num) hC hc A D hA hD
  refine ⟨CD, hCD, max (max W₁ W₂) (max W₃ 3), ?_⟩
  intro W hW L hL g b hg0 hgB hb1 hbB J hJm hJE n hn1 hn hT
  have hW1W : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2W : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW3W : W₃ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW3 : (3 : ℝ) ≤ W := by
    exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hg1 : g ≤ (W : ℝ) ^ max 1 B :=
    hgB.trans (Real.rpow_le_rpow_of_exponent_le hW1 (le_max_right _ _))
  have hg2 : g ≤ (W : ℝ) ^ C₀ := hg1.trans (Real.rpow_le_rpow_of_exponent_le hW1 hBC)
  have hb2 : b ≤ (W : ℝ) ^ C₀ := hbB.trans (Real.rpow_le_rpow_of_exponent_le hW1 hBbC)
  have hlog : 0 ≤ Real.log W := Real.log_nonneg hW1
  have hbl : 0 ≤ b * Real.log W := by positivity
  have hnC : (n : ℝ) ≤ C₀ * b * Real.log W := by
    calc (n : ℝ) ≤ Cn * b * Real.log W := hn
      _ = Cn * (b * Real.log W) := by ring
      _ ≤ C₀ * (b * Real.log W) := mul_le_mul_of_nonneg_right hCnC hbl
      _ = _ := by ring
  have hEP := hloc W hW1W g hg0 hg1 J n hn1 hT
  exact hconc W hW3W L hL g b hg0.le hg2 hb1 hb2 J hJm hJE
    ((hcrit W hW2W g b hg0 hg2 hb1 J n hn1 hnC hEP).2 L hL)

end LSBA
