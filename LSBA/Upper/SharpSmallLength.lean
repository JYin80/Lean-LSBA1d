import LSBA.Upper.FracChain
import LSBA.Upper.SmallContraction

/-!
# The transfer input in the two regimes of Theorem 3.2 [thm:sharp-small-upper]

The two regimes of the proof of Theorem 3.2 [thm:sharp-small-upper] (Section 8.5
[sec:upper-center-completion]), each from the contraction (8.30) [up:eq:P-contraction] at one
batch length `q ≥ 1000` divisible by `1000` and Lemma 8.9 [up:lem:good-bad] in operator form.
Regime (ii): `g` in the critical window (8.37) [eq:critical-window] and scale `W^{18θ}` give (8.11)
[up:eq:input] at one length `n ≤ C W^{18θ} log W`. Regime (i): `W^{-β} ≤ g ≤ W^{-α}`, written as
`g = W^{-a}` with `a = -log g / log W ∈ [α, β]`, and scale `W^{ε/2} W g²` ((8.38)
[up:eq:small-transfer-scales]) give (8.11) [up:eq:input] at one length `n ≤ C W^{ε/2} W g² log W`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Regime (ii) of the proof of Theorem 3.2 [thm:sharp-small-upper]: for `κ, c_*, θ > 0`, the
contraction (8.30) [up:eq:P-contraction] with factor `1 - c/W^{18θ}`, `0 < c ≤ 1/4`, at one length
`q ≥ 1000` divisible by `1000`, for `g` in the critical window (8.37) [eq:critical-window] and
every `E ∈ [-2+κ, 2-κ]`, gives, for every `D′ > 0`, (8.11) [up:eq:input] on the window at one
length `1 ≤ n ≤ C W^{18θ} log W`. -/
theorem critical_length_of_contraction (hsplit : GoodBadSplit) {κ cs θ : ℝ} (hκ : 0 < κ)
    (hcs : 0 < cs) (hθ : 0 < θ) {q : ℕ} (hq : 1000 ≤ q) (hq' : 1000 ∣ q) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 4)
    (hcon : ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ g : ℝ, cs * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ g →
      g ≤ (W : ℝ) ^ (-(1 / 2 : ℝ) + θ / 2) → ∀ E ∈ Set.Icc (-2 + κ) (2 - κ),
        AngContractionAt W g E q (1 - c / (W : ℝ) ^ (18 * θ)))
    (D' : ℝ) (hD' : 0 < D') :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ,
      cs * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ g → g ≤ (W : ℝ) ^ (-(1 / 2 : ℝ) + θ / 2) →
        ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ C * (W : ℝ) ^ (18 * θ) * Real.log W ∧
          TransferInputAt W g (Set.Icc (-2 + κ) (2 - κ)) D' n := by
  obtain ⟨W₁, hW₁⟩ := hcon
  obtain ⟨C, hC, W₀, h⟩ := transferLength_of_contraction hsplit (B := 1 + θ) (E₀ := 2)
    (by linarith) two_pos
    (adm := fun W g b J => 1 ≤ W ∧ (cs⁻¹) ^ 2 ≤ (W : ℝ) ∧
      cs * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ g ∧ g ≤ (W : ℝ) ^ (-(1 / 2 : ℝ) + θ / 2) ∧
      b = (W : ℝ) ^ (18 * θ) ∧ J = Set.Icc (-2 + κ) (2 - κ))
    (by
      rintro W g b J ⟨hW, hcsW, hg1, hg2, rfl, rfl⟩
      have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
      have hWpos : (0 : ℝ) < W := by linarith
      have hsq : (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ cs := by
        have h1 : cs⁻¹ ≤ (W : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.sqrt_eq_rpow]
          calc cs⁻¹ = Real.sqrt (cs⁻¹ ^ 2) := (Real.sqrt_sq (inv_nonneg.2 hcs.le)).symm
            _ ≤ Real.sqrt W := Real.sqrt_le_sqrt hcsW
        rw [Real.rpow_neg hWpos.le]
        calc ((W : ℝ) ^ (1 / 2 : ℝ))⁻¹ ≤ (cs⁻¹)⁻¹ :=
              inv_anti₀ (inv_pos.2 hcs) h1
          _ = cs := inv_inv cs
      refine ⟨?_, ?_, Real.one_le_rpow hW1 (by linarith), ?_⟩
      · have h2 : (W : ℝ) ^ (-(1 + θ)) = (W : ℝ) ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (-(1 / 2 + θ)) := by
          rw [← Real.rpow_add hWpos]; congr 1; ring
        have h3 : (W : ℝ) ^ (-(1 / 2 + θ)) ≤ cs :=
          le_trans (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)) hsq
        rw [h2, mul_comm]
        exact le_trans (mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hWpos.le _)) hg1
      · exact le_trans hg2 (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith))
      · exact Set.Icc_subset_Icc (by linarith) (by linarith))
    hq hq' hc0 hc
    ⟨W₁, by
      rintro W hW g b J ⟨-, -, hg1, hg2, rfl, rfl⟩ E hE
      exact hW₁ W hW g hg1 hg2 E hE⟩ D' hD'
  refine ⟨C, hC, max (max W₀ 1) ⌈(cs⁻¹) ^ 2⌉₊, fun W hW g hg1 hg2 => ?_⟩
  have hW1 : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW0 : W₀ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWc : (cs⁻¹) ^ 2 ≤ (W : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hW)
  exact h W hW0 g _ _ ⟨hW1, hWc, hg1, hg2, rfl, rfl⟩

/-- Regime (i) of the proof of Theorem 3.2 [thm:sharp-small-upper]: for `κ > 0`,
`0 < α < β < 1/2` and `ε > 0`, the contraction (8.30) [up:eq:P-contraction] at `g = W^{-a}`,
`a ∈ [α, β]`, with factor `1 - c/𝔟`, `𝔟 = W^{ε/2} W g²` ((8.38) [up:eq:small-transfer-scales]),
`0 < c ≤ 1/4`, at one length `q ≥ 1000` divisible by `1000` and every `E ∈ [-2+κ, 2-κ]`, gives, for
every `D′ > 0`, (8.11) [up:eq:input] for `W^{-β} ≤ g ≤ W^{-α}` at one length
`1 ≤ n ≤ C W^{ε/2} W g² log W`. -/
theorem weak_length_of_contraction (hsplit : GoodBadSplit) {κ α β ε : ℝ} (hκ : 0 < κ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 2) (hε : 0 < ε) {q : ℕ} (hq : 1000 ≤ q)
    (hq' : 1000 ∣ q) {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 4)
    (hcon : ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ a ∈ Set.Icc α β, ∀ E ∈ Set.Icc (-2 + κ) (2 - κ),
      AngContractionAt W ((W : ℝ) ^ (-a)) E q
        (1 - c / ((W : ℝ) ^ (ε / 2) * W * ((W : ℝ) ^ (-a)) ^ 2)))
    (D' : ℝ) (hD' : 0 < D') :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ,
      (W : ℝ) ^ (-β) ≤ g → g ≤ (W : ℝ) ^ (-α) →
        ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ C * ((W : ℝ) ^ (ε / 2) * W * g ^ 2) * Real.log W ∧
          TransferInputAt W g (Set.Icc (-2 + κ) (2 - κ)) D' n := by
  obtain ⟨W₁, hW₁⟩ := hcon
  obtain ⟨C, hC, W₀, h⟩ := transferLength_of_contraction hsplit (B := 1) (E₀ := 2)
    one_pos two_pos
    (adm := fun W g b J => 2 ≤ W ∧ (W : ℝ) ^ (-β) ≤ g ∧ g ≤ (W : ℝ) ^ (-α) ∧
      b = (W : ℝ) ^ (ε / 2) * W * g ^ 2 ∧ J = Set.Icc (-2 + κ) (2 - κ))
    (by
      rintro W g b J ⟨hW, hg1, hg2, rfl, rfl⟩
      have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
      have hW1 : (1 : ℝ) ≤ W := by linarith
      have hWpos : (0 : ℝ) < W := by linarith
      have hgpos : 0 < g := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hg1
      have hg1' : g ≤ 1 :=
        le_trans hg2 (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact le_trans (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)) hg1
      · calc g ≤ 1 := hg1'
          _ ≤ (W : ℝ) := hW1
          _ = (W : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      · have e : (W : ℝ) ^ (ε / 2) * W * ((W : ℝ) ^ (-β)) ^ 2 =
            (W : ℝ) ^ (ε / 2 + 1 + (-β) * 2) := by
          rw [Real.rpow_add hWpos, Real.rpow_add hWpos, Real.rpow_mul hWpos.le, Real.rpow_two,
            Real.rpow_one]
        have h4 : ((W : ℝ) ^ (-β)) ^ 2 ≤ g ^ 2 :=
          pow_le_pow_left₀ (Real.rpow_nonneg hWpos.le _) hg1 2
        calc (1 : ℝ) ≤ (W : ℝ) ^ (ε / 2 + 1 + (-β) * 2) :=
              Real.one_le_rpow hW1 (by linarith)
          _ = (W : ℝ) ^ (ε / 2) * W * ((W : ℝ) ^ (-β)) ^ 2 := e.symm
          _ ≤ (W : ℝ) ^ (ε / 2) * W * g ^ 2 :=
              mul_le_mul_of_nonneg_left h4 (mul_nonneg (Real.rpow_nonneg hWpos.le _) hWpos.le)
      · exact Set.Icc_subset_Icc (by linarith) (by linarith))
    hq hq' hc0 hc
    ⟨W₁, by
      rintro W hW g b J ⟨hW2, hg1, hg2, rfl, rfl⟩ E hE
      have hW2' : (2 : ℝ) ≤ W := by exact_mod_cast hW2
      have hWpos : (0 : ℝ) < W := by linarith
      have hgpos : 0 < g := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hg1
      have hWgt : (1 : ℝ) < W := by linarith
      have hlog : (W : ℝ) ^ (-(-Real.logb W g)) = g := by
        rw [neg_neg]; exact Real.rpow_logb hWpos hWgt.ne' hgpos
      have hα' : α ≤ -Real.logb W g := by
        have := (Real.logb_le_iff_le_rpow hWgt hgpos).2 hg2
        linarith
      have hβ' : -Real.logb W g ≤ β := by
        have := (Real.le_logb_iff_rpow_le hWgt hgpos).2 hg1
        linarith
      have key := hW₁ W hW (-Real.logb W g) ⟨hα', hβ'⟩ E hE
      rwa [hlog] at key⟩ D' hD'
  refine ⟨C, hC, max W₀ 2, fun W hW g hg1 hg2 => ?_⟩
  exact h W (le_trans (le_max_left _ _) hW) g _ _
    ⟨le_trans (le_max_right _ _) hW, hg1, hg2, rfl, rfl⟩

end LSBA
