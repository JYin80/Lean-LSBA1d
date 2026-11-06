import LSBA.Upper.FracCriterion
import LSBA.Upper.FracLocal
import LSBA.Upper.OperatorLength
import LSBA.Upper.OperatorIteration
import LSBA.Upper.GoodBad
import LSBA.Upper.DensityContraction
import LSBA.Upper.Angular

/-!
# Fixed-energy fractional moments below `g = W`

The range `W^ε ≤ g < W` of the proof of Theorem 3.4 [thm:large-upper]. Lemma 11.5
[up:lem:center-transfer] gives the transfer input (8.11) [up:eq:input] on `[-2κ₁, 2κ₁]`;
Lemma 8.13 [up:lem:density-contraction] (ii) with Lemmas 8.11 [up:lem:angular], 8.10
[up:lem:operator-iteration] and 8.6 [up:lem:operator-reduction], at batch length `1000`, gives it
on `[κ₁, 2 - κ]` and on `[-2 + κ, -κ₁]`. On each interval Proposition 8.4 [up:prop:conversion] (i)
and Proposition 8.2 [up:prop:fr-concentration] give (8.2) [up:eq:fmr-pointwise] at the exponent
`q = 1/8` and scale `𝔟 = W g²`, with one prefactor and one rate.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The field hypotheses of Lemma 8.11 [up:lem:angular] with `K_out = 0` pass to a larger
constant. -/
private theorem largeFracCycle_fieldZero_mono {W : ℕ} {g E : ℝ} {q : ℕ} {b C C' : ℝ}
    {x : IsoFlag W} {χ : Ω W q → ℝ} {Y : Ω W q → Ω W q} (hb : 0 ≤ b) (hCC : C ≤ C')
    (h : AngularFieldZeroAt W g E q b C x χ Y) : AngularFieldZeroAt W g E q b C' x χ Y := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCC hb))⟩

/-- The transfer input (8.11) [up:eq:input] away from zero energy, in the proof of Theorem 3.4
[thm:large-upper]: for `κ < 2`, `κ₁ > 0` and `D′ > 0` there are `C` and a width threshold,
independent of `g`, such that for `1 ≤ g ≤ W` each of `[κ₁, 2 - κ]`, `[-2 + κ, -κ₁]` has one
length `1 ≤ n ≤ C W g² log W` with (8.11) [up:eq:input] at exponent `D′`. -/
theorem large_away_length {κ κ₁ D' : ℝ} (hκ2 : κ < 2) (hκ₁ : 0 < κ₁) (hD' : 0 < D') :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, 1 ≤ g → g ≤ W →
      (∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ C * W * g ^ 2 * Real.log W ∧
        TransferInputAt W g (Set.Icc κ₁ (2 - κ)) D' n) ∧
      (∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ C * W * g ^ 2 * Real.log W ∧
        TransferInputAt W g (Set.Icc (-2 + κ) (-κ₁)) D' n) := by
  have hE₀ : 0 < 2 - κ := by linarith
  obtain ⟨Cd, hCd, Wd, hWd⟩ := density_contraction 1 (2 - κ) one_pos hE₀
  set C₂ : ℝ := Cd * (1 + κ₁⁻¹) ^ 2 with hC₂def
  have hC₂ : 0 < C₂ := by positivity
  obtain ⟨hc0, hc⟩ := angularConst_pos_le hC₂
  obtain ⟨C₃, W₃, hpd⟩ := powerDecay_of_contraction good_bad_split (B := 1) (E₀ := 2 - κ)
    one_pos hE₀ (q := 1000) le_rfl dvd_rfl hc0 hc
  let adm : ℕ → ℝ → ℝ → Set ℝ → Prop := fun W g b J =>
    1 ≤ W ∧ 1 ≤ g ∧ g ≤ W ∧ b = W * g ^ 2 ∧
      (J = Set.Icc κ₁ (2 - κ) ∨ J = Set.Icc (-2 + κ) (-κ₁))
  have hJ : ∀ J : Set ℝ, (J = Set.Icc κ₁ (2 - κ) ∨ J = Set.Icc (-2 + κ) (-κ₁)) →
      J ⊆ Set.Icc (-(2 - κ)) (2 - κ) ∧ ∀ E ∈ J, E ≠ 0 ∧ κ₁ ≤ |E| ∧ |E| ≤ 2 - κ := by
    rintro J (rfl | rfl)
    · refine ⟨Set.Icc_subset_Icc (by linarith) le_rfl, fun E hE => ?_⟩
      have hE0 : 0 < E := lt_of_lt_of_le hκ₁ hE.1
      rw [abs_of_pos hE0]
      exact ⟨hE0.ne', hE.1, hE.2⟩
    · refine ⟨Set.Icc_subset_Icc (by linarith) (by linarith), fun E hE => ?_⟩
      have hE0 : E < 0 := lt_of_le_of_lt hE.2 (neg_lt_zero.mpr hκ₁)
      rw [abs_of_neg hE0]
      exact ⟨hE0.ne, by linarith [hE.2], by linarith [hE.1]⟩
  have hwin : ∀ W g b J, adm W g b J → (W : ℝ) ^ (-(1 : ℝ)) ≤ g ∧ g ≤ (W : ℝ) ^ (1 : ℝ) ∧
      1 ≤ b ∧ J ⊆ Set.Icc (-(2 - κ)) (2 - κ) := by
    rintro W g b J ⟨hW, hg1, hg2, rfl, hJJ⟩
    have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
    exact ⟨(Real.rpow_le_one_of_one_le_of_nonpos hWr (by norm_num)).trans hg1,
      by rw [Real.rpow_one]; exact hg2, by nlinarith, (hJ J hJJ).1⟩
  obtain ⟨C, W₁, hC⟩ := transferGrowth_of_powerDecay one_pos hE₀ (q := 1000) (by norm_num) hwin
    ⟨angularConst C₂, C₃, hc0, max Wd W₃, fun W hW g b J hadm E hE => by
      obtain ⟨hgl, hgu, hb, -⟩ := hwin W g b J hadm
      obtain ⟨-, hg1, hg2, hbW, hJJ⟩ := hadm
      obtain ⟨-, hEJ⟩ := hJ J hJJ
      obtain ⟨hE0, hEκ, hEu⟩ := hEJ E hE
      refine hpd W (le_trans (le_max_right _ _) hW) g E b hgl hgu hEu hb ?_
      refine (angContractionAllAt_of_field_zero hb hC₂ fun x => ?_).angContractionAt
      obtain ⟨χ, -, h2⟩ := hWd W (le_trans (le_max_left _ _) hW)
      obtain ⟨Y, hY⟩ := h2 g E hg1 (by rw [Real.rpow_one]; exact hg2) hE0 hEu x
      refine ⟨χ, Y, ?_⟩
      rw [hbW]
      refine largeFracCycle_fieldZero_mono (by positivity) ?_ hY
      have hi : |E|⁻¹ ≤ κ₁⁻¹ := inv_anti₀ hκ₁ hEκ
      have : (1 + |E|⁻¹) ^ 2 ≤ (1 + κ₁⁻¹) ^ 2 := by
        gcongr
      exact mul_le_mul_of_nonneg_left this hCd.le⟩ D' hD'
  refine ⟨max C 1, by positivity, max W₁ 3, fun W hW g hg1 hg2 => ?_⟩
  have hW₁ : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW3 : (3 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
  have hW1 : 1 ≤ W := by exact_mod_cast (by linarith : (1 : ℝ) ≤ W)
  have hlog : 1 ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_three]
  have key : ∀ J : Set ℝ, (J = Set.Icc κ₁ (2 - κ) ∨ J = Set.Icc (-2 + κ) (-κ₁)) →
      ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ max C 1 * W * g ^ 2 * Real.log W ∧
        TransferInputAt W g J D' n := by
    intro J hJJ
    obtain ⟨n, h2n, hn, hT⟩ := hC W hW₁ g (W * g ^ 2) J ⟨hW1, hg1, hg2, rfl, hJJ⟩
    have hn1 : 1 ≤ n := by
      by_contra h
      have h0 : n = 0 := by omega
      subst h0
      simp only [Nat.cast_zero] at h2n
      linarith
    refine ⟨n, hn1, hn.trans ?_, hT⟩
    have hbl : 0 ≤ (W : ℝ) * g ^ 2 * Real.log W := by positivity
    calc C * ((W : ℝ) * g ^ 2) * Real.log W = C * ((W : ℝ) * g ^ 2 * Real.log W) := by ring
      _ ≤ max C 1 * ((W : ℝ) * g ^ 2 * Real.log W) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hbl
      _ = _ := by ring
  exact ⟨key _ (Or.inl rfl), key _ (Or.inr rfl)⟩

/-- The fixed-energy step of the proof of Theorem 3.4 [thm:large-upper] for `W^ε ≤ g < W`: for
`κ ∈ (0, 2)` and `0 < ε < 1` there are `C, c > 0` and a width threshold, independent of `g, L`,
such that (8.2) [up:eq:fmr-pointwise] holds at the exponent `q = 1/8` and scale `𝔟 = W g²` on
`[-2 + κ, 2 - κ]`, on every cycle of `L ≥ 3` blocks. -/
theorem large_frac_cycle {κ ε : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, (W : ℝ) ^ ε ≤ g → g < W →
      ∀ L : ℕ, 3 ≤ L → FracCycle W L g (Set.Icc (-2 + κ) (2 - κ)) (1 / 8) C c (W * g ^ 2) := by
  obtain ⟨D', hD', W₁, hloc⟩ := frac_local_of_growth (C₀ := 1) (t := 1 / 4) le_rfl (by norm_num)
    (by norm_num)
  obtain ⟨κ₁, hκ₁, hκ₁2, C₁, hC₁, hct⟩ := center_transfer (Bg := 1) (κ₀ := κ) (D' := D') hε hε1 hκ
    hκ2 hD'
  obtain ⟨W₂, hW₂⟩ := hct C₁ le_rfl
  obtain ⟨Ca, hCa, W₃, haway⟩ := large_away_length (κ := κ) (κ₁ := κ₁) hκ2 hκ₁ hD'
  set C₀ : ℝ := max 1 (max (C₁ + 1) Ca) with hC₀
  have hC₀1 : 1 ≤ C₀ := le_max_left _ _
  have hC₀c : C₁ + 1 ≤ C₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hC₀a : Ca ≤ C₀ := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨C, c, hC, hc, W₄, hcrit⟩ := frac_criterion (C₀ := C₀) (s := 1 / 4) hC₀1 (by norm_num)
    (by norm_num)
  refine ⟨C, c, hC, hc, max (max W₁ W₂) (max W₃ (max W₄ 3)), ?_⟩
  intro W hW g hg1 hg2 L hL
  have hW₁ : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW₂' : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW₃ : W₃ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW₄ : W₄ ≤ W := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hW
  have hW3 : (3 : ℝ) ≤ W := by
    exact_mod_cast le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hW
  have hW1' : (1 : ℝ) ≤ W := by linarith
  have hW1 : 1 ≤ W := by exact_mod_cast hW1'
  have hg : 1 ≤ g := le_trans (Real.one_le_rpow hW1' hε.le) hg1
  have hg0 : 0 < g := by linarith
  have hgW1 : g ≤ (W : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hg2.le
  have hgC₀ : g ≤ (W : ℝ) ^ C₀ := hgW1.trans (Real.rpow_le_rpow_of_exponent_le hW1' hC₀1)
  have hlog : 1 ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_three]
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (W : ℝ) * g ^ 2 := ⟨_, rfl⟩
  have hb1 : 1 ≤ b := by rw [hb]; nlinarith
  have hbl : 1 ≤ b * Real.log W := one_le_mul_of_one_le_of_one_le hb1 hlog
  -- each interval: transfer input, Proposition 8.4 (i) [up:prop:conversion], Proposition 8.2
  -- [up:prop:fr-concentration]
  have step : ∀ (J : Set ℝ) (n : ℕ), 1 ≤ n → (n : ℝ) ≤ C₀ * b * Real.log W →
      TransferInputAt W g J D' n → FracCycle W L g J (1 / 8) C c b := by
    intro J n hn hnb hT
    have h := (hcrit W hW₄ g b hg0 hgC₀ hb1 J n hn hnb
      (hloc W hW₁ g hg0 hgW1 J n hn hT)).2 L hL
    rwa [show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] at h
  obtain ⟨⟨n₂, hn₂1, hn₂, hT₂⟩, ⟨n₃, hn₃1, hn₃, hT₃⟩⟩ := haway W hW₃ g hg hg2.le
  have hle : ∀ x : ℝ, x ≤ C₀ → x * b * Real.log W ≤ C₀ * b * Real.log W := fun x hx => by
    have : 0 ≤ b * Real.log W := by positivity
    calc x * b * Real.log W = x * (b * Real.log W) := by ring
      _ ≤ C₀ * (b * Real.log W) := mul_le_mul_of_nonneg_right hx this
      _ = _ := by ring
  have hx0 : 0 < C₁ * b * Real.log W := by positivity
  have h₁ := step (Set.Icc (-(2 * κ₁)) (2 * κ₁)) ⌈C₁ * W * g ^ 2 * Real.log W⌉₊
    (by
      rw [show C₁ * W * g ^ 2 * Real.log W = C₁ * b * Real.log W by rw [hb]; ring]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hx0).ne')
    (by
      rw [show C₁ * W * g ^ 2 * Real.log W = C₁ * b * Real.log W by rw [hb]; ring]
      refine le_trans (Nat.ceil_lt_add_one hx0.le).le (le_trans ?_ (hle _ hC₀c))
      nlinarith)
    (hW₂ W hW₂' g hg1 (by rwa [Real.rpow_one]))
  have h₂ := step _ n₂ hn₂1
    (by
      refine hn₂.trans (le_trans (le_of_eq ?_) (hle _ hC₀a))
      rw [hb]; ring) hT₂
  have h₃ := step _ n₃ hn₃1
    (by
      refine hn₃.trans (le_trans (le_of_eq ?_) (hle _ hC₀a))
      rw [hb]; ring) hT₃
  rw [← hb]
  refine ((h₁.union h₂).union h₃).mono hW1 (fun E hE => ?_) le_rfl hc.le le_rfl (by linarith) le_rfl
  obtain ⟨hE1, hE2⟩ := hE
  by_cases hA1 : |E| ≤ 2 * κ₁
  · exact Or.inl (Or.inl (abs_le.mp hA1))
  · replace hA1 := not_le.mp hA1
    rcases lt_abs.mp hA1 with h | h
    · exact Or.inl (Or.inr ⟨by linarith, hE2⟩)
    · exact Or.inr ⟨hE1, by linarith⟩

end LSBA
