import LSBA.Upper.ConversionEndpoint
import LSBA.Upper.ConversionCycle
import LSBA.Upper.CorrelatorDecay
import LSBA.Upper.CorrelatorCount
import LSBA.Upper.Interface
import LSBA.Upper.OperatorLength
import LSBA.Upper.OperatorIteration
import LSBA.Upper.FracChain
import LSBA.Analysis.LogAbsorb

/-!
# Theorem 3.3 [thm:compact-upper] from the contraction at batch length 1000

The proof of Theorem 3.3 [thm:compact-upper] (Section 8.5 [sec:upper-center-completion]) from
Lemma 8.9 [up:lem:good-bad] in operator form and the contraction (8.30) [up:eq:P-contraction]
at batch length `1000` with factor `1 - c/𝔟`, `𝔟 = W max{g^{-2}, g⁴}`, in the form given by
Lemma 8.13 [up:lem:density-contraction] (i) with Lemma 8.11 [up:lem:angular]: the class
`W^{-B} ≤ g ≤ W^B`, `J = [-E₀, E₀]` has `1 ≤ 𝔟 ≤ W^{1+4B}`, the chain Lemma 8.6
[up:lem:operator-reduction] → Proposition 8.4(i) [up:prop:conversion] → Proposition 8.2
[up:prop:fr-concentration] → Lemma 8.1(i) [uva:thm:upper-audit] gives (3.6) [eq:averaged-tail]
with `R = ⌈C_D 𝔟 log W⌉`, and `C_D` is absorbed into a further
`log W` ((3.9) [eq:coarse-radius]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Theorem 3.3 [thm:compact-upper] from Lemma 8.9 [up:lem:good-bad] in operator form and the
contraction (8.30) [up:eq:P-contraction] at length `1000` with factor `1 - c/𝔟`,
`𝔟 = W max{g^{-2}, g⁴}`: for fixed `B, E₀ > 0` there are `0 < c ≤ 1/4` and a width threshold
such that the contraction holds for `W^{-B} ≤ g ≤ W^B` and `|E| ≤ E₀` (Lemma 8.13
[up:lem:density-contraction] (i) with Lemma 8.11 [up:lem:angular]). -/
theorem compactUpper_of_contraction (hsplit : GoodBadSplit)
    (hcon : ∀ B E₀ : ℝ, 0 < B → 0 < E₀ → ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 4 ∧ ∃ W₁ : ℕ, ∀ W : ℕ,
      W₁ ≤ W → ∀ g E : ℝ, (W : ℝ) ^ (-B) ≤ g → g ≤ (W : ℝ) ^ B → |E| ≤ E₀ →
        AngContractionAt W g E 1000 (1 - c / (W * max (g⁻¹ ^ 2) (g ^ 4)))) :
    CompactUpper := by
  intro B E₀ A D hB hE₀ hA hD
  obtain ⟨c, hc0, hc, W₁, hW₁⟩ := hcon B E₀ hB hE₀
  obtain ⟨D', hD', hchain⟩ := frac_tail_of_transfer (B := B) (Bb := 1 + 4 * B) (E₀ := E₀) hE₀
  have hcls : ∀ W : ℕ, ∀ g : ℝ, 1 ≤ W → (W : ℝ) ^ (-B) ≤ g → g ≤ (W : ℝ) ^ B →
      1 ≤ (W : ℝ) * max (g⁻¹ ^ 2) (g ^ 4) ∧
        (W : ℝ) * max (g⁻¹ ^ 2) (g ^ 4) ≤ (W : ℝ) ^ (1 + 4 * B) := by
    intro W g hW hg1 hg2
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
    have hWpos : (0 : ℝ) < W := by linarith
    have hgpos : 0 < g := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hg1
    have hx : (1 : ℝ) ≤ (W : ℝ) ^ B := Real.one_le_rpow hW1 hB.le
    have hginv : g⁻¹ ≤ (W : ℝ) ^ B := by
      have h1 : g⁻¹ ≤ (((W : ℝ) ^ B)⁻¹)⁻¹ := by
        apply inv_anti₀ (inv_pos.2 (by linarith))
        rwa [← Real.rpow_neg hWpos.le]
      rwa [inv_inv] at h1
    have hmax1 : 1 ≤ max (g⁻¹ ^ 2) (g ^ 4) := by
      rcases le_total 1 g with h | h
      · exact le_max_of_le_right (one_le_pow₀ h)
      · exact le_max_of_le_left (one_le_pow₀ ((one_le_inv₀ hgpos).2 h))
    have hpow : (W : ℝ) ^ (1 + 4 * B) = W * ((W : ℝ) ^ B) ^ 4 := by
      rw [Real.rpow_add hWpos, Real.rpow_one]
      congr 1
      rw [show 4 * B = B * ((4 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_mul_natCast hWpos.le]
    constructor
    · exact one_le_mul_of_one_le_of_one_le hW1 hmax1
    · rw [hpow]
      refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) hWpos.le
      · calc g⁻¹ ^ 2 ≤ ((W : ℝ) ^ B) ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hgpos.le) hginv 2
          _ ≤ ((W : ℝ) ^ B) ^ 4 := pow_le_pow_right₀ hx (by norm_num)
      · exact pow_le_pow_left₀ hgpos.le hg2 4
  obtain ⟨Cn, hCn, W₂, hn⟩ := transferLength_of_contraction hsplit hB hE₀
    (adm := fun W g b J => 1 ≤ W ∧ (W : ℝ) ^ (-B) ≤ g ∧ g ≤ (W : ℝ) ^ B ∧
      b = W * max (g⁻¹ ^ 2) (g ^ 4) ∧ J = Set.Icc (-E₀) E₀)
    (by
      rintro W g b J ⟨hW, hg1, hg2, rfl, rfl⟩
      exact ⟨hg1, hg2, (hcls W g hW hg1 hg2).1, subset_rfl⟩)
    (q := 1000) le_rfl dvd_rfl hc0 hc
    ⟨W₁, fun W hW g b J hJ E hE => by
      obtain ⟨-, hg1, hg2, rfl, rfl⟩ := hJ
      exact hW₁ W hW g E hg1 hg2 (abs_le.2 hE)⟩ D' hD'
  obtain ⟨CD, -, W₃, hT⟩ := hchain Cn hCn A D hA hD
  obtain ⟨W₄, hW₄⟩ := ceil_mul_log_le_mul_log_sq CD
  refine ⟨max (max W₂ W₃) (max W₄ 1), fun W hW L hL g hg1 hg2 => ?_⟩
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW)
  have hWR : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  have hgpos : 0 < g := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hg1
  obtain ⟨hb1, hbB⟩ := hcls W g hW1 hg1 hg2
  obtain ⟨n, hn1, hnb, hin⟩ := hn W (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW)
    g _ (Set.Icc (-E₀) E₀) ⟨hW1, hg1, hg2, rfl, rfl⟩
  have hmain := hT W (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW) L hL g _ hgpos
    hg2 hb1 hbB _ measurableSet_Icc subset_rfl n hn1 hnb hin
  refine averagedTailBound_mono subset_rfl measurableSet_Icc ?_ hmain
  have h3 := hW₄ W (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hW)) _ hb1
  rw [inv_pow]
  rw [inv_pow] at h3
  exact h3

end LSBA
