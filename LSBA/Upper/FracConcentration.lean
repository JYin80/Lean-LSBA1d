import LSBA.Upper.FracMoment
import LSBA.Upper.CorrelatorDecay
import LSBA.Upper.CorrelatorCount
import LSBA.Upper.Interface
import LSBA.Upper.ConversionCycle
import LSBA.Upper.NearZeroTransfer

/-!
# From fixed-energy fractional moments to concentration

Lemma 8.1 [uva:thm:upper-audit] (i): the fixed-energy bound (8.2) [up:eq:fmr-pointwise] on one
cycle gives (3.6) [eq:averaged-tail] on that cycle, with block radius (8.4)
[uva:eq:conversion-radius]; through (E.1) [up:eq:correlator-intro] and (E.2)
[uv:eq:ordinary-count] (Appendix E.1 [app:fr-concentration-proof]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Lemma 8.1 [uva:thm:upper-audit] (i): for fixed `C₀ ≥ 1`, `E₀ > 0`, `q ∈ (0, 1)`,
`C, c, A, D > 0` there are `C_D` and a width threshold, independent of `L, g, 𝔟, J`, such that
for `L ≥ 3`, `0 ≤ g ≤ W^{C₀}`, `1 ≤ 𝔟 ≤ W^{C₀}` and measurable `J ⊆ [-E₀, E₀]` the bound (8.2)
[up:eq:fmr-pointwise] on the cycle of `L` blocks gives (3.6) [eq:averaged-tail] with
`R = ⌈C_D 𝔟 log W⌉`. -/
theorem frac_concentration_fixed {C₀ E₀ q C c : ℝ} (hC₀ : 1 ≤ C₀) (hE₀ : 0 < E₀) (hq0 : 0 < q)
    (hq1 : q < 1) (hC : 0 < C) (hc : 0 < c) (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ CD : ℝ, 0 < CD ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g b : ℝ, 0 ≤ g →
      g ≤ (W : ℝ) ^ C₀ → 1 ≤ b → b ≤ (W : ℝ) ^ C₀ → ∀ J : Set ℝ, MeasurableSet J →
      J ⊆ Set.Icc (-E₀) E₀ → FracCycle W L g J q C c b →
        AveragedTailBound W L g J (⌈CD * b * Real.log W⌉₊ : ℝ) A D := by
  have hB : 0 < C₀ := by linarith
  have h1u : 0 < 1 - q := by linarith
  have h4u : 0 < 4 - q := by linarith
  have hCu : 0 ≤ absMomentConst q := by
    unfold absMomentConst
    have : 0 < Real.Gamma ((q + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
    positivity
  set Cq : ℝ := (4 * absMomentConst q * E₀ * 1 / Real.sqrt (2 * π)) ^ (1 / (4 - q)) with hCq_def
  set Pq : ℝ := 2 + ((1 - q) / 2 + C₀ * (1 - q) + C) / (4 - q) with hPq_def
  set cq : ℝ := c / (4 - q) with hcq_def
  have hcq : 0 < cq := div_pos hc h4u
  have hCq : 0 ≤ Cq := Real.rpow_nonneg (by positivity) _
  have hPq : 0 < Pq := by
    have : 0 < (1 - q) / 2 + C₀ * (1 - q) + C := by
      have : 0 < C₀ * (1 - q) := mul_pos hB h1u
      linarith
    have := div_pos this h4u
    linarith
  set K : ℝ := A + Pq + C₀ + D with hK_def
  have hK : 0 < K := by linarith
  set C4 : ℝ := 2 * Cq * (1 + 1 / cq) with hC4_def
  refine ⟨K / cq, div_pos hK hcq, max 3 ⌈C4⌉₊, ?_⟩
  intro W hW L hL g b hg0 hgB hb1 hbB J hJm hJE hF
  have hW3 : 3 ≤ W := le_trans (le_max_left _ _) hW
  have hWC4 : C4 ≤ (W : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hW)
  have hW1' : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hb0 : 0 < b := by linarith
  have hG : ∀ E ∈ J, ∀ a c' : Fin L, a ≠ c' →
      ∫⁻ ω, ‖blockOf (resolventMat (Hmat g W L ω) E) a c'‖ₑ ^ q ∂(μ W L) ≤
        ENNReal.ofReal (1 * (W : ℝ) ^ C * Real.exp (-c * cycDist a c' / b)) := fun E hE a c' _ => by
    rw [one_mul]
    exact hF E hE a c'
  have hQ : ∀ a c' : Fin L, a ≠ c' →
      ∫ ω, blockCorr (Hmat g W L ω) J a c' ∂(μ W L) ≤
        Cq * (W : ℝ) ^ Pq * Real.exp (-cq * cycDist a c' / b) := fun a c' hac =>
    blockCorr_decay hq0 hq1 hB hE₀ zero_le_one hc hb0 hW1' hL hg0 hgB hJm hJE hG hac
  set R : ℝ := (⌈K / cq * b * Real.log W⌉₊ : ℝ) with hR_def
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hT := averagedTail_le_of_blockCorr (A := A) hCq hcq hb0 hW1' hL hJm hQ hR0
  unfold AveragedTailBound
  refine hT.trans ?_
  have hRge : K / cq * b * Real.log W ≤ R := Nat.le_ceil _
  have hexp : Real.exp (-cq * R / b) ≤ (W : ℝ) ^ (-K) := by
    rw [Real.rpow_def_of_pos hW0]
    apply Real.exp_le_exp.mpr
    have h1 : cq * (K / cq * b * Real.log W) ≤ cq * R := mul_le_mul_of_nonneg_left hRge hcq.le
    have h2 : cq * (K / cq * b * Real.log W) = K * Real.log W * b := by
      field_simp
    rw [h2] at h1
    rw [neg_mul, neg_div, mul_neg, neg_le_neg_iff, le_div_iff₀ hb0]
    linarith
  have hbf : 1 + b / cq ≤ (W : ℝ) ^ C₀ * (1 + 1 / cq) := by
    have h1 : 1 + b / cq ≤ b * (1 + 1 / cq) := by
      have : 0 ≤ (b - 1) := by linarith
      have : 1 + b / cq = b * (1 + 1 / cq) - (b - 1) := by ring
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right hbB (by positivity))
  have hWpow : (W : ℝ) ^ C₀ * (W : ℝ) ^ (A + Pq - 1) * (W : ℝ) ^ (-K) =
      (W : ℝ)⁻¹ * (W : ℝ) ^ (-D) := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_neg_one, ← Real.rpow_add hW0]
    congr 1
    rw [hK_def]
    ring
  have hP0 : 0 ≤ (W : ℝ) ^ (A + Pq - 1) := by positivity
  have hD0 : 0 ≤ (W : ℝ) ^ (-D) := by positivity
  calc 2 * Cq * (1 + b / cq) * (W : ℝ) ^ (A + Pq - 1) * Real.exp (-cq * R / b)
      ≤ 2 * Cq * ((W : ℝ) ^ C₀ * (1 + 1 / cq)) * (W : ℝ) ^ (A + Pq - 1) * (W : ℝ) ^ (-K) := by
        gcongr
    _ = C4 * (W : ℝ)⁻¹ * (W : ℝ) ^ (-D) := by
        rw [show 2 * Cq * ((W : ℝ) ^ C₀ * (1 + 1 / cq)) * (W : ℝ) ^ (A + Pq - 1) *
            (W : ℝ) ^ (-K) = C4 * ((W : ℝ) ^ C₀ * (W : ℝ) ^ (A + Pq - 1) * (W : ℝ) ^ (-K)) by
          rw [hC4_def]; ring, hWpow]
        ring
    _ ≤ (W : ℝ) ^ (-D) := by
        have : C4 * (W : ℝ)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hW0]
          exact hWC4
        nlinarith

end LSBA
