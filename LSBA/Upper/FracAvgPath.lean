import LSBA.Upper.FracMoment
import LSBA.Upper.LargeGreenPath

/-!
# From negative transfer moments to energy-averaged fractional moments

Proposition 8.4 [up:prop:conversion] (ii): the negative-moment bound (8.12)
[up:eq:negative-transfer-input] over the boundary frames of Definition 8.3 [def:boundary-frames]
gives the energy-averaged bound (8.3) [uva:eq:conversion-input] with `q = s/4` on every Dirichlet
path, through (8.15) [uvg:eq:boundary], (8.16) [uvg:eq:energyapriori] and Hölder on `J × Ω`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Cauchy–Schwarz against `1` on a measure space of mass at most `4`. -/
private lemma fracAvgPath_holder {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (hν : ν Set.univ ≤ ENNReal.ofReal 4) {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ^ (1 / 2 : ℝ) ∂ν ≤ ENNReal.ofReal 2 * (∫⁻ z, f z ∂ν) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
    (f := fun z => f z ^ (1 / 2 : ℝ)) (g := fun _ => 1) (hf.pow_const _).aemeasurable
    aemeasurable_const
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have h2 : ∀ z, (f z ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = f z := fun z => by
    rw [← ENNReal.rpow_mul]
    norm_num
  simp only [h2] at h
  have h4 : ν Set.univ ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal 2 := by
    calc ν Set.univ ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal 4) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hν (by norm_num)
      _ = ENNReal.ofReal 2 := by
          rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]
          congr 1
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
  calc _ ≤ (∫⁻ z, f z ∂ν) ^ (1 / (2 : ℝ)) * ν Set.univ ^ (1 / (2 : ℝ)) := h
    _ ≤ (∫⁻ z, f z ∂ν) ^ (1 / (2 : ℝ)) * ENNReal.ofReal 2 := by gcongr
    _ = _ := by rw [mul_comm]

/-- Proposition 8.4 [up:prop:conversion] (ii): for fixed `E₀ < 2`, `s ∈ (0, 1)` and `C, c > 0`
there are `C′, c′ > 0` and a width threshold, independent of `g` and of the path length, such
that for `g ≥ W` the bound (8.12) [up:eq:negative-transfer-input] on `J = [-E₀, E₀]` gives (8.3)
[uva:eq:conversion-input] with `q = s/4` and `𝔟 = W g²` on every Dirichlet path. -/
theorem frac_avg_of_negative_moment {E₀ s C c : ℝ} (hE₀ : E₀ < 2) (hs0 : 0 < s) (hs1 : s < 1)
    (hC : 0 < C) (hc : 0 < c) :
    ∃ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, (W : ℝ) ≤ g →
      NegTransfer W g (Set.Icc (-E₀) E₀) s C c →
        ∀ m : ℕ, AvgFracPath W m g (Set.Icc (-E₀) E₀) (s / 4) C' c' (W * g ^ 2) := by
  have hBs : 0 < booleConst s := by
    unfold booleConst
    exact div_pos (by positivity) (by linarith)
  have hBq : 0 < booleConst (s / 2) := by
    unfold booleConst
    exact div_pos (by positivity) (by linarith)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * C + 8 * booleConst s + 4 * booleConst (s / 2) := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  refine ⟨2, c / 4, two_pos, by positivity, max 1 ⌈2 * Real.sqrt K⌉₊, ?_⟩
  intro W hW g hgW hT m x y
  have hW1 : 1 ≤ W := le_trans (le_max_left _ _) hW
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWK : 2 * Real.sqrt K ≤ W :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hW)
  have hg0 : 0 < g := by linarith
  have hb : 0 < (W : ℝ) * g ^ 2 := by positivity
  set d : ℝ := |((x : ℕ) : ℝ) - (y : ℕ)| with hd
  have hJ4 : volume (Set.Icc (-E₀) E₀) ≤ ENNReal.ofReal 4 := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have h2 := green_path_of_transfer hE₀ hC hs0 hs1
    (fun n hn E hE Φ hΦ => hT n hn E (abs_le.mp hE) Φ hΦ) hW1 hg0 m 0 0
    Matrix.isHermitian_zero Matrix.isHermitian_zero measurableSet_Icc subset_rfl x y
  rw [← hK, ← hd] at h2
  have hmeas := greenPath_measurable_entry (W := W) (m := m) g 0 0 x y (s / 2)
  have hν : ((volume.restrict (Set.Icc (-E₀) E₀)).prod (μ W m)) Set.univ ≤ ENNReal.ofReal 4 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ (μ := μ W m), mul_one,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hJ4
  have h4 := fracAvgPath_holder hν hmeas
  have hl : ∀ f : ℝ × Ω W m → ℝ≥0∞, Measurable f →
      ∫⁻ z, f z ∂((volume.restrict (Set.Icc (-E₀) E₀)).prod (μ W m)) =
        ∫⁻ E in Set.Icc (-E₀) E₀, ∫⁻ ω, f (E, ω) ∂(μ W m) := fun f hf =>
    lintegral_prod _ hf.aemeasurable
  rw [hl _ hmeas, hl _ (hmeas.pow_const _)] at h4
  simp only [← ENNReal.rpow_mul] at h4
  rw [show s / 2 * (1 / 2) = s / 4 by ring] at h4
  have hexp : Real.sqrt (Real.exp (-(c / 2) * d / (W * g ^ 2))) =
      Real.exp (-(c / 4) * d / (W * g ^ 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    field_simp
    ring
  have hsq : Real.sqrt (K * (W : ℝ) ^ 2 * Real.exp (-(c / 2) * d / (W * g ^ 2))) =
      Real.sqrt K * W * Real.exp (-(c / 4) * d / (W * g ^ 2)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hK0.le, Real.sqrt_sq (by positivity), hexp]
  have hX0 : 0 ≤ K * (W : ℝ) ^ 2 * Real.exp (-(c / 2) * d / (W * g ^ 2)) := by positivity
  refine h4.trans ?_
  calc ENNReal.ofReal 2 * _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal
          (K * (W : ℝ) ^ 2 * Real.exp (-(c / 2) * d / (W * g ^ 2)))) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = ENNReal.ofReal (2 * (Real.sqrt K * W * Real.exp (-(c / 4) * d / (W * g ^ 2)))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hX0 (by norm_num), ← Real.sqrt_eq_rpow, hsq,
          ENNReal.ofReal_mul (p := 2) (by norm_num)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.rpow_two]
        have hE : 0 ≤ Real.exp (-(c / 4) * d / (W * g ^ 2)) := (Real.exp_pos _).le
        have h1 : 2 * Real.sqrt K * W ≤ (W : ℝ) * W := by gcongr
        calc 2 * (Real.sqrt K * W * Real.exp (-(c / 4) * d / (W * g ^ 2)))
            = 2 * Real.sqrt K * W * Real.exp (-(c / 4) * d / (W * g ^ 2)) := by ring
          _ ≤ (W : ℝ) * W * Real.exp (-(c / 4) * d / (W * g ^ 2)) :=
              mul_le_mul_of_nonneg_right h1 hE
          _ = _ := by ring

end LSBA
