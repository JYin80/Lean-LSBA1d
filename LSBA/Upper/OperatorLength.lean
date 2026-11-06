import LSBA.Upper.OperatorReduction
import LSBA.Upper.ConversionEndpoint

/-!
# The transfer length

(8.22) [up:eq:transfer-length]: from (8.21) [up:eq:power-input] for every energy of `J`, Markov at
`n₀ = ⌈C_{D′} 𝔟 log W⌉` gives the transfer input (8.11) [up:eq:input], with `2 log W ≤ n₀ ≤ 2 C_{D′}
𝔟 log
W`; uniformly over a class, this is the body of the transfer-growth input of Proposition 8.4(i)
[up:prop:conversion] (Lemma 8.6 [up:lem:operator-reduction]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The constant `C_{D′} = max{2, (q/c)(C + 1 + (B/2+1) q + 3D′/2 + 1)}` of (8.22)
[up:eq:transfer-length]. -/
def reductionConst (B : ℝ) (q : ℕ) (c C D' : ℝ) : ℝ :=
  max 2 ((q / c) * (C + 1 + (B / 2 + 1) * q + 3 * D' / 2 + 1))

/-- (8.22) [up:eq:transfer-length] at one width: (8.21) [up:eq:power-input] for every `E ∈ J`
gives (8.11) [up:eq:input] at `n₀ = ⌈C_{D′} 𝔟 log W⌉`, with `2 log W ≤ n₀ ≤ 2 C_{D′} 𝔟 log W`,
for `W ≥ max{(4(E₀+1))^{2/3}, C e^c}` (Lemma 8.6 [up:lem:operator-reduction]). -/
theorem transferInputAt_of_powerDecay {B E₀ b c C D' : ℝ} (hB : 0 < B) (hE₀ : 0 < E₀)
    (hb : 1 ≤ b) (hc : 0 < c) (hD' : 0 < D') {q : ℕ} (hq : 0 < q) {W : ℕ}
    (hW : (4 * (E₀ + 1)) ^ (2 / 3 : ℝ) ≤ W) (hWC : C * Real.exp c ≤ W) {g : ℝ}
    (hg1 : (W : ℝ) ^ (-B) ≤ g) (hg2 : g ≤ (W : ℝ) ^ B) {J : Set ℝ} (hJ : J ⊆ Set.Icc (-E₀) E₀)
    (hpow : ∀ E ∈ J, PowerDecayAt W g E q b c C) :
    TransferInputAt W g J D' ⌈reductionConst B q c C D' * b * Real.log W⌉₊ ∧
      2 * Real.log W ≤ ⌈reductionConst B q c C D' * b * Real.log W⌉₊ ∧
      (⌈reductionConst B q c C D' * b * Real.log W⌉₊ : ℝ) ≤
        2 * reductionConst B q c C D' * b * Real.log W := by
  -- the matrix inverse is measurable
  have hinv : ∀ W : ℕ, Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A⁻¹ := by
    intro W
    refine Measurable.of_eval_matrix _ fun i j => ?_
    have hdet : Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A.det :=
      (Continuous.matrix_det continuous_id).measurable
    have hadj : Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A.adjugate i j :=
      ((Continuous.matrix_adjugate continuous_id).matrix_elem i j).measurable
    have : (fun A : Matrix (Fin W) (Fin W) ℂ => A⁻¹ i j) =
        fun A => (A.det)⁻¹ * A.adjugate i j := by
      funext A
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
      simp [Matrix.smul_apply]
    rw [this]
    exact hdet.inv.mul hadj
  -- the norm of the inverse of `D_n(Φ; E)` is measurable in the sample
  have hmeas : ∀ (W : ℕ) (g E : ℝ) (n : ℕ) (Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ),
      Measurable fun ω : Ω W n => ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n) Φ)⁻¹‖ₑ ^ (1 / 2 : ℝ) := by
    intro W g E n Φ
    have hF : Measurable fun ω : Ω W n => frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n) Φ := by
      refine Measurable.of_eval_matrix _ fun α β => ?_
      have hb := measurable_batchMat W g E n
      have : (fun ω : Ω W n => frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
          (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n) Φ α β) =
          fun ω => ((Real.sqrt 2 : ℝ) : ℂ) * ∑ x, batchMat W g E n ω (0, α) x * Φ x β := by
        funext ω
        simp only [frameD, Matrix.of_apply, Matrix.mul_apply]
        rfl
      rw [this]
      refine measurable_const.mul (Finset.measurable_sum _ fun x _ => ?_)
      exact (hb.eval_matrix).mul_const _
    exact ((hinv W).comp hF).enorm.pow_const _
  -- `W ≥ 3` and `log W ≥ 1` from `W ≥ (4(E₀+1))^{2/3}`
  have hsmall : (3 : ℝ) ≤ W ∧ 1 ≤ Real.log W := by
    have hx : (16 : ℝ) < (4 * (E₀ + 1)) ^ 2 := by nlinarith
    set y := (4 * (E₀ + 1)) ^ (2 / 3 : ℝ) with hy
    have hy0 : 0 ≤ y := Real.rpow_nonneg (by positivity) _
    have hy3 : y ^ 3 = (4 * (E₀ + 1)) ^ 2 := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      rw [show (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hy2 : 2 < y := by
      by_contra h
      push Not at h
      have : y ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hy0 h 3
      nlinarith
    have hW2 : 2 < W := by exact_mod_cast hy2.trans_le hW
    have hW3 : (3 : ℝ) ≤ W := by exact_mod_cast hW2
    refine ⟨hW3, ?_⟩
    have : (1 : ℝ) < Real.log W := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    exact this.le
  obtain ⟨hW3, hL1⟩ := hsmall
  have hw0 : (0 : ℝ) < W := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set L := Real.log W with hL
  set r := reductionConst B q c C D' with hr
  set n₀ := ⌈r * b * L⌉₊ with hn₀
  have hr2 : 2 ≤ r := le_max_left _ _
  have hrS : (q / c) * (C + 1 + (B / 2 + 1) * q + 3 * D' / 2 + 1) ≤ r := le_max_right _ _
  have hrb : 2 ≤ r * b := by nlinarith
  have hx2 : 2 ≤ r * b * L := by nlinarith
  have hn_ge : r * b * L ≤ n₀ := Nat.le_ceil _
  have hn_lt : (n₀ : ℝ) < r * b * L + 1 := Nat.ceil_lt_add_one (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · intro E hE Φ hΦ
    have hE' := hJ hE
    have hEabs : |E| ≤ E₀ := abs_le.mpr ⟨(Set.mem_Icc.mp hE').1, (Set.mem_Icc.mp hE').2⟩
    have hmom := frameD_moment_le hB hE₀ hb hc hq hW hg1 hg2 hEabs (hpow E hE) hΦ n₀
    -- the exponent decay
    set S : ℝ := C + 1 + (B / 2 + 1) * q + 3 * D' / 2 + 1 with hS
    have hcr : S ≤ c / q * r := by
      have : q / c * S ≤ r := hrS
      have h2 : S = c / q * (q / c * S) := by field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hexp : (c / q) * (n₀ : ℝ) / b ≥ S * L := by
      have h1 : (c / q) * (r * b * L) / b = c / q * r * L := by field_simp
      have h2 : (c / q) * (r * b * L) / b ≤ (c / q) * (n₀ : ℝ) / b := by
        gcongr
      rw [h1] at h2
      nlinarith
    have hexp2 : Real.exp (-(c / q) * n₀ / b) ≤ (W : ℝ) ^ (-S) := by
      rw [Real.rpow_def_of_pos hw0]
      refine Real.exp_le_exp.mpr ?_
      have : -(c / q) * n₀ / b = -((c / q) * n₀ / b) := by ring
      rw [this]
      nlinarith
    -- the bound on `K`
    set C₂ : ℝ := C + 1 + (B / 2 + 1) * q with hC₂
    set K : ℝ := C * Real.exp c * (W : ℝ) ^ C₂ * Real.exp (-(c / q) * n₀ / b) with hK
    have hKle : K ≤ (W : ℝ) ^ (-(3 * D' / 2)) := by
      have hWp : (W : ℝ) ^ C₂ * Real.exp (-(c / q) * n₀ / b) ≤ (W : ℝ) ^ (-(3 * D' / 2 + 1)) := by
        calc (W : ℝ) ^ C₂ * Real.exp (-(c / q) * n₀ / b) ≤ (W : ℝ) ^ C₂ * (W : ℝ) ^ (-S) :=
              mul_le_mul_of_nonneg_left hexp2 (Real.rpow_nonneg hw0.le _)
          _ = (W : ℝ) ^ (-(3 * D' / 2 + 1)) := by
              rw [← Real.rpow_add hw0]
              congr 1
              rw [hS, hC₂]
              ring
      have hK' : K = C * Real.exp c * ((W : ℝ) ^ C₂ * Real.exp (-(c / q) * n₀ / b)) := by
        rw [hK]; ring
      rcases le_or_gt 0 C with hC0 | hC0
      · have hCe : 0 ≤ C * Real.exp c := by positivity
        calc K = C * Real.exp c * ((W : ℝ) ^ C₂ * Real.exp (-(c / q) * n₀ / b)) := hK'
          _ ≤ W * (W : ℝ) ^ (-(3 * D' / 2 + 1)) :=
              mul_le_mul hWC hWp (by positivity) hw0.le
          _ = (W : ℝ) ^ (-(3 * D' / 2)) := by
              rw [show (W : ℝ) * (W : ℝ) ^ (-(3 * D' / 2 + 1)) =
                (W : ℝ) ^ (1 : ℝ) * (W : ℝ) ^ (-(3 * D' / 2 + 1)) by rw [Real.rpow_one],
                ← Real.rpow_add hw0]
              congr 1
              ring
      · have h1 : C * Real.exp c < 0 := mul_neg_of_neg_of_pos hC0 (Real.exp_pos _)
        have h2 : 0 < (W : ℝ) ^ C₂ * Real.exp (-(c / q) * n₀ / b) := by positivity
        have : K < 0 := by rw [hK']; exact mul_neg_of_neg_of_pos h1 h2
        exact this.le.trans (Real.rpow_nonneg hw0.le _)
    -- Markov
    have hε0 : (0 : ℝ) < (W : ℝ) ^ (-(D' / 2)) := Real.rpow_pos_of_pos hw0 _
    have hsub : {ω | (W : ℝ) ^ (-D') < ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
          (seqBlocks (gueBlock W n₀ ω)) n₀) Φ)⁻¹‖}
        ⊆ {ω | ENNReal.ofReal ((W : ℝ) ^ (-(D' / 2))) ≤
          ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
            (fun i => if h : i < n₀ then gueBlock W n₀ ω ⟨i, h⟩ else 0) n₀) Φ)⁻¹‖ₑ ^
            (1 / 2 : ℝ)} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (W : ℝ) ^ (-(D' / 2)) = ((W : ℝ) ^ (-D')) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_mul hw0.le]
        congr 1
        ring
      rw [h1]
      refine Real.rpow_le_rpow (Real.rpow_nonneg hw0.le _) ?_ (by norm_num)
      exact hω.le
    have hmk := meas_ge_le_lintegral_div
      (μ := μ W n₀) (hmeas W g E n₀ Φ).aemeasurable
      (ENNReal.ofReal_pos.mpr hε0).ne' ENNReal.ofReal_ne_top
    refine (measure_mono hsub).trans (hmk.trans ?_)
    refine (ENNReal.div_le_div_right hmom _).trans ?_
    rw [← ENNReal.ofReal_div_of_pos hε0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hε0, ← Real.rpow_add hw0]
    refine hKle.trans (le_of_eq ?_)
    congr 1
    ring
  · have h1 : 2 * L ≤ r * b * L := by nlinarith
    exact_mod_cast h1.trans hn_ge
  · linarith

/-- Lemma 8.6 [up:lem:operator-reduction], (8.22) [up:eq:transfer-length]: (8.21)
[up:eq:power-input] uniformly over a class with `W^{-B} ≤ g ≤ W^B`, `𝔟 ≥ 1`,
`J ⊆ [-E₀, E₀]` gives the transfer input (8.11) [up:eq:input] of Proposition 8.4(i)
[up:prop:conversion] uniformly over the class. -/
theorem transferGrowth_of_powerDecay {B E₀ : ℝ} (hB : 0 < B) (hE₀ : 0 < E₀) {q : ℕ}
    (hq : 0 < q) {adm : ℕ → ℝ → ℝ → Set ℝ → Prop}
    (hadm : ∀ W g b J, adm W g b J →
      (W : ℝ) ^ (-B) ≤ g ∧ g ≤ (W : ℝ) ^ B ∧ 1 ≤ b ∧ J ⊆ Set.Icc (-E₀) E₀)
    (hpow : ∃ c C : ℝ, 0 < c ∧ ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ g b : ℝ, ∀ J : Set ℝ,
      adm W g b J → ∀ E ∈ J, PowerDecayAt W g E q b c C) :
    ∀ D' : ℝ, 0 < D' → ∃ C : ℝ, ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ g b : ℝ, ∀ J : Set ℝ,
      adm W g b J → ∃ n₀ : ℕ, 2 * Real.log W ≤ n₀ ∧ (n₀ : ℝ) ≤ C * b * Real.log W ∧
        TransferInputAt W g J D' n₀ := by
  obtain ⟨c, C, hc, W₀, hW₀⟩ := hpow
  intro D' hD'
  refine ⟨2 * reductionConst B q c C D', max W₀ ⌈max ((4 * (E₀ + 1)) ^ (2 / 3 : ℝ))
    (C * Real.exp c)⌉₊, ?_⟩
  intro W hW g b J hJ
  obtain ⟨hg1, hg2, hb, hJ'⟩ := hadm W g b J hJ
  have hW0 : W₀ ≤ W := (le_max_left _ _).trans hW
  have hWc : max ((4 * (E₀ + 1)) ^ (2 / 3 : ℝ)) (C * Real.exp c) ≤ (W : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hW)
  obtain ⟨h1, h2, h3⟩ := transferInputAt_of_powerDecay hB hE₀ hb hc hD' hq
    (le_max_left _ _ |>.trans hWc) ((le_max_right _ _).trans hWc) hg1 hg2 hJ'
    (hW₀ W hW0 g b J hJ)
  exact ⟨_, h2, by linarith, h1⟩

end LSBA
