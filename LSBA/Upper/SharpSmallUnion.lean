import LSBA.Upper.ConversionEndpoint
import LSBA.Upper.ConversionCycle
import LSBA.Upper.CorrelatorDecay
import LSBA.Upper.CorrelatorCount
import LSBA.Upper.Interface
import LSBA.Upper.OperatorLength
import LSBA.Upper.OperatorIteration
import LSBA.Upper.SharpSmallLength
import LSBA.Analysis.LogAbsorb

/-!
# Theorem 3.2 [thm:sharp-small-upper] from the contraction in the two regimes

The proof of Theorem 3.2 [thm:sharp-small-upper] (Section 8.5 [sec:upper-center-completion]) from
Lemma 8.9 [up:lem:good-bad] in operator form and the contraction (8.30) [up:eq:P-contraction] in
the two regimes of Lemma 8.12 [up:lem:small-contraction] at a batch length `q ≥ 1000` divisible by
`1000`: with `θ = min{ε/200, (1-2α)/4, 1/100}` and `β = 1/2 - θ/2 > α`, fixed before `W, g, L`,
regime (ii) covers `c_* W^{-1/2} ≤ g ≤ W^{-β}`, regime (i) covers `W^{-β} ≤ g ≤ W^{-α}`, the two
ranges meet at `g = W^{-β}`, and each gives (8.11) [up:eq:input] at a length `n ≤ C 𝔟 log W` with
one scale `𝔟 = W^{ε/2} max{1, W g²}`. The chain Proposition 8.4(i) [up:prop:conversion] →
Proposition 8.2 [up:prop:fr-concentration] → Lemma 8.1(i) [uva:thm:upper-audit] then gives (3.6)
[eq:averaged-tail] with `R = ⌈C_D 𝔟 log W⌉`, and `C_D log W` is absorbed into `W^{ε/2}`, which is
(3.8) [eq:sharp-small-radius].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Theorem 3.2 [thm:sharp-small-upper] from Lemma 8.9 [up:lem:good-bad] in operator form and
the contraction (8.30) [up:eq:P-contraction] in the two regimes of Lemma 8.12
[up:lem:small-contraction]: (ii) in the critical window (8.37) [eq:critical-window] with factor
`1 - c/W^{18θ}`; (i) at `g = W^{-a}`, `a ∈ [α, β]`, with factor `1 - c/(W^{ε/2} W g²)`; each at
one length `q ≥ 1000` divisible by `1000`, with `0 < c ≤ 1/4`, at every `E ∈ [-2+κ, 2-κ]` and
every large `W`. -/
theorem sharpSmallUpper_of_contraction (hsplit : GoodBadSplit)
    (hcrit : ∀ κ cs θ : ℝ, 0 < κ → κ < 2 → 0 < cs → 0 < θ → θ ≤ 1 / 100 →
      ∃ q : ℕ, 1000 ≤ q ∧ 1000 ∣ q ∧ ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 4 ∧ ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W →
        ∀ g : ℝ, cs * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ g → g ≤ (W : ℝ) ^ (-(1 / 2 : ℝ) + θ / 2) →
          ∀ E ∈ Set.Icc (-2 + κ) (2 - κ),
            AngContractionAt W g E q (1 - c / (W : ℝ) ^ (18 * θ)))
    (hweak : ∀ κ α β ε : ℝ, 0 < κ → κ < 2 → 0 < α → α < β → β < 1 / 2 → 0 < ε →
      ∃ q : ℕ, 1000 ≤ q ∧ 1000 ∣ q ∧ ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 4 ∧ ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W →
        ∀ a ∈ Set.Icc α β, ∀ E ∈ Set.Icc (-2 + κ) (2 - κ),
          AngContractionAt W ((W : ℝ) ^ (-a)) E q
            (1 - c / ((W : ℝ) ^ (ε / 2) * W * ((W : ℝ) ^ (-a)) ^ 2))) :
    SharpSmallUpper := by
  intro α cs A D ε κ hα hα2 hcs hA hD hε hκ hκ2
  obtain ⟨θ, hθ0, hθ1, hθε, hθα⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 100 ∧ θ ≤ ε / 200 ∧
      θ ≤ (1 - 2 * α) / 4 :=
    ⟨min (min (ε / 200) ((1 - 2 * α) / 4)) (1 / 100),
      lt_min (lt_min (by positivity) (by linarith)) (by norm_num), min_le_right _ _,
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _)⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = 1 / 2 - θ / 2 := ⟨_, rfl⟩
  have hαβ : α < β := by rw [hβdef]; linarith
  have hβ2 : β < 1 / 2 := by rw [hβdef]; linarith
  have hseam : -(1 / 2 : ℝ) + θ / 2 = -β := by rw [hβdef]; ring
  -- the exponent `D′` comes from the range of `g` alone
  obtain ⟨D', hD', hchain⟩ := frac_tail_of_transfer (B := 1) (Bb := 1 + ε / 2) (E₀ := 2) two_pos
  obtain ⟨q₁, hq₁, hq₁', c₁, hc₁0, hc₁, W₁, hW₁⟩ := hcrit κ cs θ hκ hκ2 hcs hθ0 hθ1
  obtain ⟨q₂, hq₂, hq₂', c₂, hc₂0, hc₂, W₂, hW₂⟩ := hweak κ α β ε hκ hκ2 hα hαβ hβ2 hε
  obtain ⟨C₁, hC₁, W₃, h₁⟩ := critical_length_of_contraction hsplit hκ hcs hθ0 hq₁ hq₁' hc₁0 hc₁
    ⟨W₁, hW₁⟩ D' hD'
  obtain ⟨C₂, hC₂, W₄, h₂⟩ := weak_length_of_contraction hsplit hκ hα hαβ hβ2 hε hq₂ hq₂' hc₂0 hc₂
    ⟨W₂, hW₂⟩ D' hD'
  obtain ⟨CD, -, W₅, hT⟩ := hchain (max C₁ C₂) (lt_max_of_lt_left hC₁) A D hA hD
  obtain ⟨W₆, h₃⟩ := ceil_mul_log_le_rpow_mul CD (ε / 2) (by positivity)
  refine ⟨max (max (max W₃ W₄) (max W₅ W₆)) 1, fun W hW L hL g hg1 hg2 => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (show 1 ≤ W by omega)
  have hWpos : (0 : ℝ) < W := by linarith
  have hgpos : 0 < g :=
    lt_of_lt_of_le (mul_pos hcs (Real.rpow_pos_of_pos hWpos _)) hg1
  have hg1' : g ≤ 1 :=
    hg2.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
  have hlog : 0 ≤ Real.log W := Real.log_nonneg hW1
  -- the common scale `𝔟 = W^{ε/2} max{1, W g²}`
  set b : ℝ := (W : ℝ) ^ (ε / 2) * max 1 ((W : ℝ) * g ^ 2) with hb
  have hε2 : 1 ≤ (W : ℝ) ^ (ε / 2) := Real.one_le_rpow hW1 (by linarith)
  have hmax1 : 1 ≤ max 1 ((W : ℝ) * g ^ 2) := le_max_left _ _
  have hb1 : 1 ≤ b := one_le_mul_of_one_le_of_one_le hε2 hmax1
  have hbB : b ≤ (W : ℝ) ^ (1 + ε / 2) := by
    have h1 : max 1 ((W : ℝ) * g ^ 2) ≤ (W : ℝ) := by
      refine max_le hW1 ?_
      have : g ^ 2 ≤ 1 := pow_le_one₀ hgpos.le hg1'
      nlinarith
    calc b ≤ (W : ℝ) ^ (ε / 2) * W := by rw [hb]; gcongr
      _ = (W : ℝ) ^ (1 + ε / 2) := by rw [Real.rpow_add hWpos, Real.rpow_one]; ring
  have hgB : g ≤ (W : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    linarith
  obtain ⟨n, hn1, hn, hin⟩ : ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ max C₁ C₂ * b * Real.log W ∧
      TransferInputAt W g (Set.Icc (-2 + κ) (2 - κ)) D' n := by
    by_cases hcase : g ≤ (W : ℝ) ^ (-β)
    · -- regime (ii): the scale `W^{18θ}` is at most `𝔟`
      obtain ⟨n, hn1, hn, hin⟩ := h₁ W (by omega) g hg1 (by rw [hseam]; exact hcase)
      refine ⟨n, hn1, hn.trans ?_, hin⟩
      have h18 : (W : ℝ) ^ (18 * θ) ≤ b := by
        calc (W : ℝ) ^ (18 * θ) ≤ (W : ℝ) ^ (ε / 2) :=
              Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
          _ ≤ b := le_mul_of_one_le_right (by positivity) hmax1
      have hmx : C₁ ≤ max C₁ C₂ := le_max_left _ _
      gcongr
    · -- regime (i): the scale `W^{ε/2} W g²` is at most `𝔟`
      have hgβ : (W : ℝ) ^ (-β) ≤ g := (not_le.1 hcase).le
      obtain ⟨n, hn1, hn, hin⟩ := h₂ W (by omega) g hgβ hg2
      refine ⟨n, hn1, hn.trans ?_, hin⟩
      have h18 : (W : ℝ) ^ (ε / 2) * W * g ^ 2 ≤ b := by
        rw [hb, mul_assoc]
        exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      have hmx : C₂ ≤ max C₁ C₂ := le_max_right _ _
      gcongr
  have hrad : (⌈CD * b * Real.log W⌉₊ : ℝ) ≤ (W : ℝ) ^ ε * max 1 ((W : ℝ) * g ^ 2) :=
    calc (⌈CD * b * Real.log W⌉₊ : ℝ) ≤ (W : ℝ) ^ (ε / 2) * b := h₃ W (by omega) _ hb1
      _ = (W : ℝ) ^ ε * max 1 ((W : ℝ) * g ^ 2) := by
          rw [hb, ← mul_assoc, ← Real.rpow_add hWpos]
          congr 2
          ring
  exact averagedTailBound_mono (Set.Subset.refl _) measurableSet_Icc hrad
    (hT W (by omega) L hL g b hgpos hgB hb1 hbB _ measurableSet_Icc
      (Set.Icc_subset_Icc (by linarith) (by linarith)) n hn1 hn hin)

end LSBA
