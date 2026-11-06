import LSBA.Upper.NearZeroGrowth
import LSBA.Transfer.NormalComparison
import LSBA.Upper.ConversionEndpoint

/-!
# Transfer growth near zero energy

Lemma 11.5 [up:lem:center-transfer]: for `0 < ε < B_g`, `κ_0 ∈ (0, 2)` and `D' > 0` there are
`0 < κ_1 < (2 − κ_0)/2` and `C_1^0` such that for every `C_1 ≥ C_1^0` there is `W_0` with (8.11)
[up:eq:input] on `J = [−2κ_1, 2κ_1]` at the length `n_0 = ⌈C_1 W g² log W⌉` (`𝔟 = W g²`) for all
`W ≥ W_0` and `W^ε ≤ g < W^{B_g}`. The proof is the reduction (11.9) [lg:eq:scalar-reduction]
through the coordinate comparison (11.6) [lg:eq:coordinate-comparison] and a union bound over the
standard basis.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Squared form of the reduction (11.9) [lg:eq:scalar-reduction] with the coordinate comparison
(11.6) [lg:eq:coordinate-comparison]: if every coordinate growth `ℓ_n(C₀, e_a)` is at least
`(D′ + 3) log W`, then `‖D_n(Φ; E)⁻¹‖ ≤ W^{−D′}`, for `W ≥ 2` and `|E| ≤ 1/2`. -/
private lemma nzt_norm_inv_le {W : ℕ} (hW : 2 ≤ W) {E : ℝ} (hE : |E| ≤ 1 / 2) (g : ℝ) {D' : ℝ}
    {Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ} (hΦ : IsBoundaryFrame Φ)
    {C₀ B : Matrix (Fin W) (Fin W) ℂ} (hC₀ : C₀ ∈ Matrix.unitaryGroup (Fin W) ℂ)
    (hB : (freeConj W E)⁻¹ * freeConj W 0 * Φ = colStack B (C₀ * B))
    {V : ℕ → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ k, (V k).IsHermitian) (n : ℕ)
    (hcol : ∀ a : Fin W,
      (D' + 3) * Real.log W ≤ ellN g E C₀ (EuclideanSpace.single a (1 : ℂ)) V n) :
    ‖(frameD (transferProd g (E : ℂ) V n) Φ)⁻¹‖ ≤ (W : ℝ) ^ (-D') := by
  have hE2 : |E| < 2 := by linarith
  have hw2 : (2 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  have hw0 : (0 : ℝ) < (W : ℝ) := by linarith
  set Dn := normalD g E C₀ V n with hDn
  have hcol' : ∀ a : Fin W,
      ‖Matrix.toEuclideanLin (Dn⁻¹ᴴ) (EuclideanSpace.single a (1 : ℂ))‖ ≤
        (W : ℝ) ^ (-(D' + 3)) := by
    intro a
    have h := hcol a
    unfold ellN at h
    set c := ‖Matrix.toEuclideanLin (Dn⁻¹ᴴ) (EuclideanSpace.single a (1 : ℂ))‖ with hc
    by_cases h0 : c = 0
    · rw [h0]
      positivity
    · have hpos : 0 < c := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have hlog : Real.log c ≤ Real.log ((W : ℝ) ^ (-(D' + 3))) := by
        rw [Real.log_rpow hw0]
        linarith
      exact (Real.log_le_log_iff hpos (by positivity)).mp hlog
  have hsum := norm_inv_rpow_le_sum Dn (s := 2) (by norm_num) le_rfl
  simp only [Real.rpow_two] at hsum
  have hsq : ‖Dn⁻¹‖ ^ 2 ≤ (W : ℝ) * ((W : ℝ) ^ (-(D' + 3))) ^ 2 := by
    calc ‖Dn⁻¹‖ ^ 2 ≤ _ := hsum
      _ ≤ ∑ _a : Fin W, ((W : ℝ) ^ (-(D' + 3))) ^ 2 :=
          Finset.sum_le_sum fun a _ => pow_le_pow_left₀ (norm_nonneg _) (hcol' a) 2
      _ = (W : ℝ) * ((W : ℝ) ^ (-(D' + 3))) ^ 2 := by simp
  obtain ⟨hle, -⟩ := norm_inv_frameD_le hE2 g hΦ hC₀ hB hV n
  have hK2 : coordConst E ^ 2 ≤ 3 := by
    unfold coordConst
    have hpos : 0 < 2 - |E| := by linarith
    rw [Real.sq_sqrt (div_nonneg (by linarith [abs_nonneg E]) hpos.le), div_le_iff₀ hpos]
    linarith
  have hK0 : 0 ≤ coordConst E := Real.sqrt_nonneg _
  have hexp : (W : ℝ) ^ (-D') = (W : ℝ) ^ (-(D' + 3)) * (W : ℝ) ^ 3 := by
    have h3 : (W : ℝ) ^ ((3 : ℕ) : ℝ) = (W : ℝ) ^ 3 := Real.rpow_natCast _ 3
    rw [← h3, ← Real.rpow_add hw0]
    congr 1
    push_cast
    ring
  have ha0 : 0 ≤ (W : ℝ) ^ (-(D' + 3)) := by positivity
  have hsq2 : ‖(frameD (transferProd g (E : ℂ) V n) Φ)⁻¹‖ ^ 2 ≤ ((W : ℝ) ^ (-D')) ^ 2 := by
    calc ‖(frameD (transferProd g (E : ℂ) V n) Φ)⁻¹‖ ^ 2
        ≤ (coordConst E * ‖Dn⁻¹‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = coordConst E ^ 2 * ‖Dn⁻¹‖ ^ 2 := mul_pow _ _ _
      _ ≤ 3 * ((W : ℝ) * ((W : ℝ) ^ (-(D' + 3))) ^ 2) :=
          mul_le_mul hK2 hsq (by positivity) (by norm_num)
      _ ≤ (W : ℝ) ^ 6 * ((W : ℝ) ^ (-(D' + 3))) ^ 2 := by
          have h1 : 3 * (W : ℝ) ≤ (W : ℝ) ^ 6 := by nlinarith [pow_le_pow_left₀ (by norm_num) hw2 5]
          have h2 : 0 ≤ ((W : ℝ) ^ (-(D' + 3))) ^ 2 := sq_nonneg _
          nlinarith
      _ = ((W : ℝ) ^ (-D')) ^ 2 := by rw [hexp]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq2

/-- Lemma 11.5 [up:lem:center-transfer]: (8.11) [up:eq:input] on `[−2κ_1, 2κ_1]` at the length
`⌈C_1 W g² log W⌉`; the threshold `W_0` is chosen after `C_1`. -/
theorem center_transfer {ε Bg κ₀ D' : ℝ} (hε : 0 < ε) (hεB : ε < Bg) (hκ₀ : 0 < κ₀)
    (hκ₀2 : κ₀ < 2) (hD' : 0 < D') :
    ∃ κ₁ : ℝ, 0 < κ₁ ∧ κ₁ < (2 - κ₀) / 2 ∧ ∃ C₁₀ : ℝ, 0 < C₁₀ ∧ ∀ C₁ : ℝ, C₁₀ ≤ C₁ →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, (W : ℝ) ^ ε ≤ g → g < (W : ℝ) ^ Bg →
        TransferInputAt W g (Set.Icc (-(2 * κ₁)) (2 * κ₁)) D'
          ⌈C₁ * W * g ^ 2 * Real.log W⌉₊ := by
  have hD0 : 0 < D' + 3 := by linarith
  obtain ⟨E₁, hE₁, CD, hCD, hsg⟩ := scalar_growth hε hεB hD0
  obtain ⟨κ₁, hκdef⟩ : ∃ κ₁ : ℝ, κ₁ = min (min (E₁ / 4) ((2 - κ₀) / 4)) (1 / 4) := ⟨_, rfl⟩
  have hκ0 : 0 < κ₁ := by
    rw [hκdef]
    exact lt_min (lt_min (by positivity) (by linarith)) (by norm_num)
  have hκE : κ₁ ≤ E₁ / 4 := hκdef ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hκ2 : κ₁ ≤ (2 - κ₀) / 4 := hκdef ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hκ4 : κ₁ ≤ 1 / 4 := hκdef ▸ min_le_right _ _
  refine ⟨κ₁, hκ0, by linarith, CD, hCD, fun C₁ hC₁ => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hsg C₁ hC₁
  refine ⟨max W₀ 2, fun W hW g hg1 hg2 => ?_⟩
  have hWsg : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hW2 : 2 ≤ W := le_trans (le_max_right _ _) hW
  have hwr : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast (by omega : 1 ≤ W)
  have hg1' : 1 ≤ g := le_trans (Real.one_le_rpow hwr hε.le) hg1
  set n := ⌈C₁ * W * g ^ 2 * Real.log W⌉₊ with hn
  intro E hE Φ hΦ
  have hEabs : |E| ≤ 2 * κ₁ := abs_le.mpr ⟨hE.1, hE.2⟩
  have hEh : |E| ≤ 1 / 2 := by linarith
  have hEsg : |E| ≤ E₁ := by linarith
  have hcast : max 1 g * E / g = E := by
    rw [max_eq_right hg1', mul_div_cancel_left₀ _ (by linarith : g ≠ 0)]
  rw [hcast]
  obtain ⟨C₀, hC₀, B, -, hB⟩ := exists_normalFrame (W := W) (by linarith : |E| < 2) hΦ
  let S : Fin W → Set (Ω W n) := fun a =>
    {ω | ellN g E C₀ (EuclideanSpace.single a (1 : ℂ))
        (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n < (D' + 3) * Real.log W}
  have hsub : {ω : Ω W n | (W : ℝ) ^ (-D') <
      ‖(frameD (transferProd g (E : ℂ) (seqBlocks (gueBlock W n ω)) n) Φ)⁻¹‖} ⊆ ⋃ a, S a := by
    intro ω hω
    by_contra hne
    simp only [Set.mem_iUnion, not_exists] at hne
    have hV : ∀ k, (seqBlocks (gueBlock W n ω) k).IsHermitian := by
      intro k
      unfold seqBlocks
      split_ifs
      · exact gueBlock_isHermitian W n ω _
      · exact Matrix.isHermitian_zero
    have := nzt_norm_inv_le hW2 hEh g hΦ hC₀ hB hV n fun a => not_lt.mp (hne a)
    exact absurd hω (not_lt.mpr this)
  have hbound : ∀ a : Fin W, μ W n (S a) ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D' + 3))) := fun a =>
    hW₀ W hWsg g hg1 hg2 E hEsg (C₀, EuclideanSpace.single a (1 : ℂ))
      ⟨hC₀, by simp⟩ n hn
  have hw0 : (0 : ℝ) < (W : ℝ) := by linarith
  calc _ ≤ μ W n (⋃ a, S a) := measure_mono hsub
    _ ≤ ∑ a, μ W n (S a) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _a : Fin W, ENNReal.ofReal ((W : ℝ) ^ (-(D' + 3))) :=
        Finset.sum_le_sum fun a _ => hbound a
    _ = ENNReal.ofReal ((W : ℝ) * (W : ℝ) ^ (-(D' + 3))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D')) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h3 : (W : ℝ) ^ ((3 : ℕ) : ℝ) = (W : ℝ) ^ 3 := Real.rpow_natCast _ 3
        have hexp : (W : ℝ) ^ (-D') = (W : ℝ) ^ (-(D' + 3)) * (W : ℝ) ^ 3 := by
          rw [← h3, ← Real.rpow_add hw0]
          congr 1
          push_cast
          ring
        rw [hexp]
        have ha0 : 0 ≤ (W : ℝ) ^ (-(D' + 3)) := by positivity
        have : (W : ℝ) ≤ (W : ℝ) ^ 3 := by
          simpa using pow_le_pow_right₀ hwr (by norm_num : 1 ≤ 3)
        nlinarith

end LSBA
