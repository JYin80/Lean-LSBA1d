import LSBA.Main.HaarVector
import LSBA.Spectral.SimpleSpectrum

/-!
# Unitary invariance and short cycles

Lemma 2.1 [thm:orbital], (2.2) [eq:haar-count], in the basis-free count form, with explicit
constants, and its two uses in the proof of the lower bound: the region (2.4)
[uv:eq:haar-lower-region] and the short cycles `L < L₀`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Lemma 2.1 [thm:orbital], the Haar average: the expectation of the bad count of the model is
the expectation, over the model and an independent Haar unitary, of the bad count of the model
conjugated by `I_L ⊗ U` (Appendix D.1 [subsec:pf_thm31]), which is bounded for each simple-spectrum
sample by `lintegral_badCount_conj_le`. -/
private theorem simpleRanges_lintegral_le (W L : ℕ) (g : ℝ) {J : Set ℝ} (hJ : MeasurableSet J)
    {r : ℝ} (hr : r ≤ (W : ℝ) / 8) :
    ∫⁻ ω, (badCount W L (Hmat g W L ω) J r : ℝ≥0∞) ∂(μ W L) ≤
      ENNReal.ofReal ((L : ℝ) * W * (4 * W * Real.exp (-(W : ℝ) / 25))) := by
  set f : Ω W L → ℝ≥0∞ := fun ω => (badCount W L (Hmat g W L ω) J r : ℝ≥0∞) with hf
  have hfm : AEMeasurable f (μ W L) := by
    have h := (aemeasurable_badCount_Hmat g W L hJ r).ennreal_ofReal
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [hf, ENNReal.ofReal_natCast]
  set P := (μ W L).prod (haarU W) with hP
  set Φ : Ω W L × Matrix.unitaryGroup (Fin W) ℂ → Ω W L × Matrix.unitaryGroup (Fin W) ℂ :=
    fun p => (conjMap W L p.2 p.1, p.2) with hΦ
  have hΦmp : MeasurePreserving Φ P P := measurePreserving_conj_haar W L
  have hFm : AEMeasurable (fun p : Ω W L × Matrix.unitaryGroup (Fin W) ℂ => f p.1) P :=
    hfm.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_fst)
  have hFΦm : AEMeasurable (fun p : Ω W L × Matrix.unitaryGroup (Fin W) ℂ => f (Φ p).1) P :=
    (hFm.comp_quasiMeasurePreserving hΦmp.quasiMeasurePreserving :)
  calc ∫⁻ ω, f ω ∂(μ W L)
      = ∫⁻ ω, ∫⁻ _U, f ω ∂(haarU W) ∂(μ W L) := by
        simp
    _ = ∫⁻ p, f p.1 ∂P := (lintegral_prod _ hFm).symm
    _ = ∫⁻ p, f (Φ p).1 ∂P := by
        rw [← lintegral_map' (f := fun p : Ω W L × Matrix.unitaryGroup (Fin W) ℂ => f p.1)
          (by rw [hΦmp.map_eq]; exact hFm) hΦmp.measurable.aemeasurable, hΦmp.map_eq]
    _ = ∫⁻ ω, ∫⁻ U, f (conjMap W L U ω) ∂(haarU W) ∂(μ W L) := lintegral_prod _ hFΦm
    _ ≤ ∫⁻ _ω, ENNReal.ofReal ((L : ℝ) * W * (4 * W * Real.exp (-(W : ℝ) / 25))) ∂(μ W L) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_injective_eigenvalues g W L] with ω hω
        have h := lintegral_badCount_conj_le W L (Hmat_isHermitian g W L ω) hω J hr
        refine le_trans (le_of_eq ?_) h
        refine lintegral_congr fun U => ?_
        simp only [hf, Hmat_conjMap]
    _ = ENNReal.ofReal ((L : ℝ) * W * (4 * W * Real.exp (-(W : ℝ) / 25))) := by
        simp

/-- (2.2) [eq:haar-count] of Lemma 2.1 [thm:orbital] with `c₀ = 1/8`, `c = 1/25`, for every
`W`, `L`, `g`, every measurable energy set and every threshold `r ≤ W/8`. -/
theorem haar_count_le (W L : ℕ) (g : ℝ) {J : Set ℝ} (hJ : MeasurableSet J) {r : ℝ}
    (hr : r ≤ (W : ℝ) / 8) :
    ((W : ℝ) * L)⁻¹ * ∫ ω, (badCount W L (Hmat g W L ω) J r : ℝ) ∂(μ W L) ≤
      4 * W * Real.exp (-(W : ℝ) / 25) := by
  have hc : 0 ≤ 4 * (W : ℝ) * Real.exp (-(W : ℝ) / 25) := by positivity
  have hI : ∫ ω, (badCount W L (Hmat g W L ω) J r : ℝ) ∂(μ W L) ≤
      (L : ℝ) * W * (4 * W * Real.exp (-(W : ℝ) / 25)) := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg _)
      (aemeasurable_badCount_Hmat g W L hJ r).aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine le_trans (le_of_eq ?_) (simpleRanges_lintegral_le W L g hJ hr)
    refine lintegral_congr fun ω => ?_
    simp [ENNReal.ofReal_natCast]
  by_cases h0 : (W : ℝ) * L = 0
  · rw [h0, inv_zero, zero_mul]
    exact hc
  · calc ((W : ℝ) * L)⁻¹ * ∫ ω, (badCount W L (Hmat g W L ω) J r : ℝ) ∂(μ W L)
        ≤ ((W : ℝ) * L)⁻¹ * ((L : ℝ) * W * (4 * W * Real.exp (-(W : ℝ) / 25))) :=
          mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr (by positivity))
      _ = 4 * W * Real.exp (-(W : ℝ) / 25) := by
          have hW : (W : ℝ) ≠ 0 := left_ne_zero_of_mul h0
          have hL : (L : ℝ) ≠ 0 := right_ne_zero_of_mul h0
          field_simp

/-- The tail `4 W e^{-W/25} ≤ W^{-D}` for large `W`, which turns the constant of (2.2)
[eq:haar-count] into the polynomial error of (2.12) [uv:eq:lower-regions-output]. -/
private theorem simpleRanges_tail (D : ℝ) :
    ∃ W₀ : ℕ, 1 ≤ W₀ ∧ ∀ W : ℕ, W₀ ≤ W →
      4 * (W : ℝ) * Real.exp (-(W : ℝ) / 25) ≤ (W : ℝ) ^ (-D) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 + D) (1 / 25) (by norm_num)
  have h' := h.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (h'.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num)))
  refine ⟨max N 1, le_max_right _ _, fun W hW => ?_⟩
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWN : N ≤ W := le_trans (le_max_left _ _) hW
  have hpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hlt : (W : ℝ) ^ (1 + D) * Real.exp (-(1 / 25) * (W : ℝ)) < 1 / 4 := hN W hWN
  have hsplit : (W : ℝ) ^ (1 + D) = W * (W : ℝ) ^ D := by
    rw [Real.rpow_add hpos, Real.rpow_one]
  have hexp : Real.exp (-(1 / 25) * (W : ℝ)) = Real.exp (-(W : ℝ) / 25) := by
    congr 1; ring
  rw [hsplit, hexp] at hlt
  have hDpos : 0 < (W : ℝ) ^ D := Real.rpow_pos_of_pos hpos D
  have hmul : 4 * (W : ℝ) * Real.exp (-(W : ℝ) / 25) * (W : ℝ) ^ D ≤ 1 := by
    nlinarith
  rw [Real.rpow_neg hpos.le]
  calc 4 * (W : ℝ) * Real.exp (-(W : ℝ) / 25)
      = 4 * (W : ℝ) * Real.exp (-(W : ℝ) / 25) * (W : ℝ) ^ D * ((W : ℝ) ^ D)⁻¹ := by
        field_simp
    _ ≤ 1 * ((W : ℝ) ^ D)⁻¹ := mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr hDpos.le)
    _ = ((W : ℝ) ^ D)⁻¹ := one_mul _

/-- The lower bound in the region (2.4) [uv:eq:haar-lower-region] with `c₀ = 1/8`. -/
theorem haar_region_count (τ D : ℝ) (hτ : 0 < τ) (hD : 0 < D) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, ∀ g : ℝ, ellStar W L g ≤ (W : ℝ) ^ (1 + τ) / 8 →
      ∀ J : Set ℝ, MeasurableSet J →
        ((W : ℝ) * L)⁻¹ * ∫ ω, (badCount W L (Hmat g W L ω) J
            ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ) ∂(μ W L) ≤ (W : ℝ) ^ (-D) := by
  have _ : 0 < τ ∧ 0 < D := ⟨hτ, hD⟩
  obtain ⟨W₀, hW₀, htail⟩ := simpleRanges_tail D
  refine ⟨W₀, fun W hW L g hreg J hJ => ?_⟩
  have hpos : (0 : ℝ) < W := by exact_mod_cast lt_of_lt_of_le hW₀ hW
  have hr : (W : ℝ) ^ (-τ) * ellStar W L g ≤ (W : ℝ) / 8 := by
    calc (W : ℝ) ^ (-τ) * ellStar W L g
        ≤ (W : ℝ) ^ (-τ) * ((W : ℝ) ^ (1 + τ) / 8) :=
          mul_le_mul_of_nonneg_left hreg (Real.rpow_nonneg hpos.le _)
      _ = (W : ℝ) / 8 := by
          rw [← mul_div_assoc, ← Real.rpow_add hpos]
          simp
  exact (haar_count_le W L g hJ hr).trans (htail W hW)

/-- Short cycles `L < L₀` lie in the region (2.4) [uv:eq:haar-lower-region] for large `W`. -/
theorem haar_short_cycle_count (τ D : ℝ) (hτ : 0 < τ) (hD : 0 < D) (L₀ : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, L < L₀ → ∀ g : ℝ, ∀ J : Set ℝ, MeasurableSet J →
      ((W : ℝ) * L)⁻¹ * ∫ ω, (badCount W L (Hmat g W L ω) J
          ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ) ∂(μ W L) ≤ (W : ℝ) ^ (-D) := by
  obtain ⟨W₁, h1⟩ := haar_region_count τ D hτ hD
  have hlim := (tendsto_rpow_atTop hτ).comp tendsto_natCast_atTop_atTop
  obtain ⟨W₂, h2⟩ := Filter.eventually_atTop.mp (hlim.eventually_ge_atTop (8 * (L₀ : ℝ)))
  refine ⟨max (max W₁ W₂) 1, fun W hW L hL g J hJ => ?_⟩
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hW₁ : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW₂ : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hWτ : 8 * (L₀ : ℝ) ≤ (W : ℝ) ^ τ := h2 W hW₂
  refine h1 W hW₁ L g ?_ J hJ
  have hL' : (L : ℝ) ≤ L₀ := by exact_mod_cast hL.le
  calc ellStar W L g ≤ (W : ℝ) * L := min_le_left _ _
    _ ≤ (W : ℝ) * L₀ := mul_le_mul_of_nonneg_left hL' hpos.le
    _ ≤ (W : ℝ) ^ (1 + τ) / 8 := by
        rw [Real.rpow_add hpos, Real.rpow_one]
        nlinarith

end LSBA
