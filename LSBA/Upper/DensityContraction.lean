import LSBA.Upper.LiftAway
import LSBA.Upper.FlagFlow
import LSBA.Analysis.FlagDerivative
import LSBA.Upper.AngularField

/-!
# Lemma 8.13 [up:lem:density-contraction]: Gaussian divergence bounds from the product differential

Lemma 8.13 [up:lem:density-contraction] with `q = 1000`: for fixed `B, E₀ > 0` and all large
`W` there is one cutoff, independent of `g`, `E` and the incoming flag, such that every flag
`x` carries a field with `K_out = 0`: (8.34) [up:eq:angular-geometry] in projection form
(the terminal flag does not move and the cocycle has derivative one, from `D_Y T = √2 T M₀`
with the direction `M₀` of (10.2) [up:eq:lift-flag-flow], Section 10 [sec:compact-proof]),
Gaussian integration by parts, `𝔼 χ ≥ ½`, and (i) (8.39) [eq:c-common-scale]
`𝔼 |δ_G(χ Y)|² ≤ C W max{g⁻², g⁴}` for `W^{-B} ≤ g ≤ W^B`, `|E| ≤ E₀`; (ii) for `g ≥ 1` and
`0 < |E| ≤ E₀`, `𝔼 |δ_G(χ Y)|² ≤ C (1 + |E|⁻¹)² W g²`. The cutoff is that of Lemma G.4
[lem:c-gaussian] at the pairs in the batch order; the fields are those of Lemma 10.1
[lem:c-gaussian-lift] after the reversal of the inputs (Section 10 [sec:compact-proof]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `batchLayout` is orthonormal, `d dᵀ = I`: its pairs are disjoint. -/
private theorem DensityContraction_layout : batchLayout * batchLayoutᵀ = 1 := by
  have hI : Function.Injective liftPairI := fun a b h => by
    simp [liftPairI, Fin.ext_iff] at h; omega
  have hK : Function.Injective liftPairK := fun a b h => by
    simp [liftPairK, Fin.ext_iff] at h; omega
  have hik : ∀ a b, liftPairI a ≠ liftPairK b := fun a b h => by
    simp [liftPairI, liftPairK, Fin.ext_iff] at h; omega
  exact pairLayout_mul_transpose (Fin.rev_injective.comp hI) (Fin.rev_injective.comp hK)
    fun a b h => hik a b (Fin.rev_injective h)

/-- A cutoff with `0 ≤ χ ≤ 1` and `μ{χ ≠ 1} ≤ C' e^{-cW}` has `𝔼 χ ≥ 1 - C' e^{-cW}`
((10.5) [eq:c-main-cutoff]). -/
private theorem DensityContraction_mean {W n : ℕ} {d : Matrix (Fin 128) (Fin n) ℝ}
    {c₁ ρ K₁ L c C' : ℝ} {χ : Ω W n → ℝ} (hC' : 0 ≤ C')
    (h : IsCoercivityCutoff W n d c₁ ρ K₁ L c C' χ) :
    1 - C' * Real.exp (-c * W) ≤ ∫ ω, χ ω ∂(μ W n) := by
  obtain ⟨hsm, -, h01, hμ, -, -⟩ := h
  have hmeas : Measurable χ := hsm.continuous.measurable
  have hint : Integrable χ (μ W n) :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h01 ω).1]; exact (h01 ω).2)
  have hS : MeasurableSet {ω | χ ω ≠ 1} := (measurableSet_singleton (1 : ℝ)).compl.preimage hmeas
  have hind : Integrable ({ω | χ ω ≠ 1}.indicator (fun _ => (1 : ℝ))) (μ W n) :=
    (integrable_const (1 : ℝ)).indicator hS
  have h1 : ∫ ω, (1 - χ ω) ∂(μ W n) ≤
      ∫ ω, {ω | χ ω ≠ 1}.indicator (fun _ => (1 : ℝ)) ω ∂(μ W n) := by
    refine integral_mono ((integrable_const (1 : ℝ)).sub hint) hind fun ω => ?_
    by_cases hω : χ ω = 1
    · simp [hω]
    · rw [Set.indicator_of_mem (show ω ∈ {ω | χ ω ≠ 1} from hω)]
      linarith [(h01 ω).1]
  rw [integral_indicator_const _ hS, integral_sub (integrable_const _) hint] at h1
  simp only [integral_const, smul_eq_mul, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one] at h1
  have h2 : (μ W n {ω | χ ω ≠ 1}).toReal ≤ C' * Real.exp (-c * W) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hμ
  linarith

/-- `W ≥ log (2 C') / c` gives `C' e^{-cW} ≤ ½`. -/
private theorem DensityContraction_tail {c C' : ℝ} (hc : 0 < c) (hC' : 0 < C') {W : ℕ}
    (hW : Real.log (2 * C') / c ≤ W) : C' * Real.exp (-c * W) ≤ 1 / 2 := by
  have h1 : Real.log (2 * C') ≤ c * W := by linarith [(div_le_iff₀ hc).1 hW]
  have h2 : Real.exp (-c * W) ≤ (2 * C')⁻¹ := by
    rw [← Real.exp_log (show 0 < 2 * C' by positivity), ← Real.exp_neg]
    exact Real.exp_le_exp.2 (by linarith)
  calc C' * Real.exp (-c * W) ≤ C' * (2 * C')⁻¹ := by gcongr
    _ = 1 / 2 := by field_simp

/-- (8.34) [up:eq:angular-geometry] with `K_out = 0` at the sample `ω`: if `D_Y T = √2 T M₀`
for `M₀ = flagDir x` ((10.2) [up:eq:lift-flag-flow]), the terminal flag does not move and the
cocycle
has derivative one. -/
private theorem DensityContraction_geom {W : ℕ} (hW : 1 ≤ W) (g E : ℝ) (x : IsoFlag W)
    (ω : Ω W 1000) (Y : Ω W 1000 → Ω W 1000)
    (hD : HasLineDerivAt ℝ (batchMat W g E 1000)
      (((Real.sqrt 2 : ℝ) : ℂ) • (batchMat W g E 1000 ω * flagDir x)) ω (Y ω)) :
    FlagFieldGeom W g E 1000 x Y ω 0 := by
  obtain ⟨-, -, -, hMU, hUM, hMY, htr⟩ := flagDir_spec hW x
  obtain ⟨⟨hUh, hUU, -, -⟩, hYh, hYY, -, -, -⟩ := x.2
  have hu : IsUnit (batchMat W g E 1000 ω) := by
    rw [Matrix.isUnit_iff_isUnit_det, (batchMat_mem_isoGroup W g E 1000 ω).2]
    exact isUnit_one
  have hJ : ∀ η, (batchMat W g E 1000 η)ᴴ * isoJ W * batchMat W g E 1000 η = isoJ W :=
    fun η => (batchMat_mem_isoGroup W g E 1000 η).1
  set N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := ((Real.sqrt 2 : ℝ) : ℂ) • flagDir x
    with hN
  have hD' : HasLineDerivAt ℝ (batchMat W g E 1000) (batchMat W g E 1000 ω * N) ω (Y ω) := by
    rw [hN, Matrix.mul_smul]; exact hD
  have hUN : N * x.1.1 = x.1.1 * N * x.1.1 := by
    simp only [hN, Matrix.smul_mul, Matrix.mul_smul, hMU, hUM, smul_zero, Matrix.zero_mul]
  have hYN : N * x.1.2 = x.1.2 * N * x.1.2 := by
    simp only [hN, Matrix.smul_mul, Matrix.mul_smul, hMY]
  have hUt : (x.1.1 * N).trace.re = 0 := by
    simp [hN, hUM]
  have hYt : (x.1.2 * N).trace.re = 1 := by
    rw [hN, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, htr,
      mul_inv_cancel₀ (by positivity)]
  obtain ⟨hU1, hU2⟩ := hasLineDerivAt_flagProj_logVol_of_mul hD' hu hUh hUU hUN
  obtain ⟨hY1, hY2⟩ := hasLineDerivAt_flagProj_logVol_of_mul hD' hu hYh hYY hYN
  unfold FlagFieldGeom
  constructor
  · unfold HasLineDerivAt at hU2 hY2 ⊢
    have h := hY2.sub hU2
    rw [hUt, hYt, sub_zero] at h
    exact h
  · have hfun : (fun η : Ω W 1000 => ((flagAct (batchMat W g E 1000 η) x : IsoFlag W) :
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) =
        fun η => (flagProj (batchMat W g E 1000 η) x.1.1,
          flagProj (batchMat W g E 1000 η) x.1.2) := by
      funext η
      exact flagAct_coe (hJ η) x
    rw [hfun, flagAct_coe (hJ ω) x]
    have h0 : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (0 : Matrix (Fin W) (Fin W) ℂ)) = 0 :=
      Matrix.kronecker_zero _
    simp only [h0, Matrix.zero_mul, Matrix.mul_zero, sub_self, Prod.mk_zero_zero]
    unfold HasLineDerivAt at hU1 hY1 ⊢
    exact hU1.prodMk hY1

/-- The clauses of `AngularFieldZeroAt` for a cutoff with the properties (10.5)
[eq:c-main-cutoff], mean at least `½`, and a cut lift of `M₀ = flagDir x` of Lemma 10.1
[lem:c-gaussian-lift] whose bound is at most `C 𝔟`. -/
private theorem DensityContraction_field {W : ℕ} (hW : 1 ≤ W) {c₁ ρ K₁ L c C' : ℝ}
    {χ : Ω W 1000 → ℝ} (hχ : IsCoercivityCutoff W 1000 batchLayout c₁ ρ K₁ L c C' χ)
    (hmean : (1 / 2 : ℝ) ≤ ∫ ω, χ ω ∂(μ W 1000)) (g E : ℝ) (x : IsoFlag W)
    {Y : Ω W 1000 → Ω W 1000} {b C 𝔟 : ℝ}
    (hY : IsCutLift W 1000 (batchMat W g E 1000) (flagDir x) b χ Y) (hb : b ≤ C * 𝔟) :
    AngularFieldZeroAt W g E 1000 𝔟 C x χ Y := by
  obtain ⟨hD, -, hibp, hbd⟩ := hY
  obtain ⟨hsm, -, h01, -⟩ := hχ
  exact ⟨hsm.continuous.measurable, h01,
    fun ω hω => DensityContraction_geom hW g E x ω Y (hD ω (subset_tsupport _ hω)), hibp,
    hmean, hbd.trans (ENNReal.ofReal_le_ofReal hb)⟩

/-- Lemma 8.13 [up:lem:density-contraction] in the form consumed by Lemma 8.11 [up:lem:angular]
with `K_out = 0`: one cutoff for all `g`, `E` and flags; (i) with `𝔟 = W max{g⁻², g⁴}`;
(ii) with `𝔟 = W g²` and the constant `C (1 + |E|⁻¹)²`, which is at most `C (1 + κ₁⁻¹)²` for
`κ₁ ≤ |E|`. -/
theorem density_contraction (B E₀ : ℝ) (hB : 0 < B) (hE₀ : 0 < E₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∃ χ : Ω W 1000 → ℝ,
      (∀ g E : ℝ, (W : ℝ) ^ (-B) ≤ g → g ≤ (W : ℝ) ^ B → |E| ≤ E₀ →
        ∀ x : IsoFlag W, ∃ Y : Ω W 1000 → Ω W 1000,
          AngularFieldZeroAt W g E 1000 (W * max (g⁻¹ ^ 2) (g ^ 4)) C x χ Y) ∧
      (∀ g E : ℝ, 1 ≤ g → g ≤ (W : ℝ) ^ B → E ≠ 0 → |E| ≤ E₀ →
        ∀ x : IsoFlag W, ∃ Y : Ω W 1000 → Ω W 1000,
          AngularFieldZeroAt W g E 1000 (W * g ^ 2) (C * (1 + |E|⁻¹) ^ 2) x χ Y) := by
  obtain ⟨c₁, ρ, K₁, L, hc₁, -, hK₁, hL, hcut⟩ := coercivity_cutoff
  obtain ⟨c, C', hc, hC', W₀', hW₀'⟩ := hcut 1000
  obtain ⟨C₁, hC₁, h₁⟩ := gaussian_lift_general_batch E₀ c₁ ρ K₁ L hE₀ hc₁ hK₁ hL
  obtain ⟨C₂, hC₂, h₂⟩ := gaussian_lift_away_batch E₀ c₁ ρ K₁ L hE₀ hc₁ hK₁ hL
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁,
    max W₀' (max 1 ⌈Real.log (2 * C') / c⌉₊), fun W hW => ?_⟩
  have hW' : W₀' ≤ W := (le_max_left _ _).trans hW
  have hW1 : 1 ≤ W := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hWt : Real.log (2 * C') / c ≤ W :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)).trans hW)
  obtain ⟨χ, hχ⟩ := hW₀' batchLayout DensityContraction_layout W hW'
  have hmean : (1 / 2 : ℝ) ≤ ∫ ω, χ ω ∂(μ W 1000) := by
    linarith [DensityContraction_mean hC'.le hχ, DensityContraction_tail hc hC' hWt]
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  refine ⟨χ, fun g E hg _ hE x => ?_, fun g E hg _ hE0 hE x => ?_⟩
  · have hg0 : 0 < g := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hg
    obtain ⟨-, hH, hn, -⟩ := flagDir_spec hW1 x
    obtain ⟨Y, hY⟩ := h₁ W c C' χ hχ g E hg0 hE (flagDir x) (flagDir_spec hW1 x).1 hn
    exact ⟨Y, DensityContraction_field hW1 hχ hmean g E x hY
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩
  · obtain ⟨hM, hH, hn, -⟩ := flagDir_spec hW1 x
    obtain ⟨Y, hY⟩ := h₂ W c C' χ hχ g E hg hE0 hE (flagDir x) hM hH hn
    exact ⟨Y, DensityContraction_field hW1 hχ hmean g E x hY
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (by positivity)) (by positivity))⟩

end LSBA
