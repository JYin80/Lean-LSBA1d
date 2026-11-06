import Mathlib

/-!
# Absolute moments and the density bound of a centered real Gaussian

For `t ~ N(0, 1)` and `c ∈ ℝ`: `𝔼|c t|^u = C_u |c|^u` with `C_u = 2^{u/2} Γ((u+1)/2)/√π`; and the
law of `c t` has density at most `1/(|c| √(2π))`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

namespace LSBA

/-- `C_u = 2^{u/2} Γ((u+1)/2) / √π`, so that `𝔼|v|^u = C_u σ^u` for `v ~ N(0, σ²)`. -/
def absMomentConst (u : ℝ) : ℝ := 2 ^ (u / 2) * Real.Gamma ((u + 1) / 2) / Real.sqrt π

/-- If `f` is integrable on `(0, ∞)`, then `x ↦ f |x|` is integrable on `ℝ`. -/
private lemma absMoment_integrable_comp_abs {f : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Ioi 0)) : Integrable (fun x => f |x|) := by
  have hf' : IntegrableOn (fun x => f |x|) (Set.Ioi 0) :=
    hf.congr_fun (fun x hx => by rw [abs_eq_self.mpr (le_of_lt (by exact hx))])
      measurableSet_Ioi
  have int_Iic : IntegrableOn (fun x ↦ f |x|) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf'
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact int_Iic.union hf'

/-- `∫_ℝ |x|^u e^{-x²/2} dx = 2 · (1/2)^{-(u+1)/2} · (1/2) · Γ((u+1)/2)` for `u > 0`. -/
private lemma absMoment_integral_main {u : ℝ} (hu : 0 < u) :
    ∫ x : ℝ, (|x| ^ u * rexp (-(1 / 2) * x ^ 2)) =
      2 * (((1 / 2 : ℝ) ^ (-(u + 1) / 2) * (1 / 2) * Real.Gamma ((u + 1) / 2))) := by
  have key := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := u) (b := 1 / 2)
    two_pos (by linarith) (by norm_num)
  have e1 : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := fun x => Real.rpow_two x
  simp only [e1] at key
  have := integral_comp_abs (f := fun x : ℝ => x ^ u * rexp (-(1 / 2) * x ^ 2))
  simp only [sq_abs] at this
  rw [this, key]

/-- `x ↦ |x|^u e^{-x²/2}` is integrable on `ℝ` for `u > 0`. -/
private lemma absMoment_integrable {u : ℝ} (hu : 0 < u) :
    Integrable (fun x : ℝ => (|x| ^ u * rexp (-(1 / 2) * x ^ 2))) := by
  have h := absMoment_integrable_comp_abs
    (f := fun x : ℝ => x ^ u * rexp (-(1 / 2) * x ^ 2))
    (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (by linarith))
  simpa only [sq_abs] using h

/-- `𝔼|c t|^u = C_u |c|^u` for `t ~ N(0, 1)` and `u > 0`. -/
theorem lintegral_enorm_const_mul_rpow_gaussianReal (c : ℝ) {u : ℝ} (hu : 0 < u) :
    ∫⁻ t, ‖c * t‖ₑ ^ u ∂(gaussianReal 0 1) = ENNReal.ofReal (absMomentConst u * |c| ^ u) := by
  have h1 : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  rw [gaussianReal_of_var_ne_zero _ h1]
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  set K : ℝ := (Real.sqrt (2 * π))⁻¹ * |c| ^ u with hK
  have hpt : ∀ t : ℝ, (gaussianPDF 0 1 * fun t => ‖c * t‖ₑ ^ u) t =
      ENNReal.ofReal (K * (|t| ^ u * rexp (-(1 / 2) * t ^ 2))) := by
    intro t
    rw [Pi.mul_apply, gaussianPDF_def, gaussianPDFReal_def, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hu.le, ← ENNReal.ofReal_mul (by positivity),
      abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    congr 1
    beta_reduce
    have e1 : -(t - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) = -(1 / 2) * t ^ 2 := by
      simp only [NNReal.coe_one, sub_zero]; ring
    rw [e1, hK]
    simp only [NNReal.coe_one, mul_one]
    ring
  simp_rw [hpt]
  have hint : Integrable (fun t : ℝ => K * (|t| ^ u * rexp (-(1 / 2) * t ^ 2))) :=
    (absMoment_integrable hu).const_mul K
  have hnn : 0 ≤ᵐ[volume] (fun t : ℝ => K * (|t| ^ u * rexp (-(1 / 2) * t ^ 2))) :=
    Filter.Eventually.of_forall fun t => by simp only [hK, Pi.zero_apply]; positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
    absMoment_integral_main hu]
  congr 1
  have e2 : ((1 / 2 : ℝ) ^ (-(u + 1) / 2)) = (2 : ℝ) ^ (u / 2) * Real.sqrt 2 := by
    rw [one_div, Real.inv_rpow (by norm_num), neg_div, Real.rpow_neg (by norm_num), inv_inv,
      add_div, Real.rpow_add (by norm_num), Real.sqrt_eq_rpow, one_div]
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have hspi : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  rw [e2, hK, absMomentConst, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp

/-- The law of `c t`, `t ~ N(0, 1)`, `c ≠ 0`, has density at most `1/(|c| √(2π))`. -/
theorem map_const_mul_gaussianReal_le {c : ℝ} (hc : c ≠ 0) :
    (gaussianReal 0 1).map (fun t => c * t) ≤
      ENNReal.ofReal (1 / (|c| * Real.sqrt (2 * π))) • (volume : Measure ℝ) := by
  set v : ℝ≥0 := NNReal.mk (c ^ 2) (sq_nonneg _) * 1 with hvdef
  have hv2 : (v : ℝ) = c ^ 2 := by simp [hvdef]
  have hv : v ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hv2
    exact hc (pow_eq_zero_iff two_ne_zero |>.mp hv2.symm)
  have hmap : (gaussianReal 0 1).map (fun t => c * t) =
      volume.withDensity (gaussianPDF (c * 0) v) := by
    rw [gaussianReal_map_const_mul, gaussianReal_of_var_ne_zero _ hv]
  rw [hmap, ← withDensity_const]
  refine withDensity_mono (Filter.Eventually.of_forall fun x => ?_)
  rw [gaussianPDF_def]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : Real.sqrt (2 * π * (v : ℝ)) = |c| * Real.sqrt (2 * π) := by
    rw [hv2, mul_comm (2 * π), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rw [gaussianPDFReal_def]
  simp only
  rw [hsq]
  have hexp : rexp (-(x - c * 0) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    have : 0 ≤ (x - c * 0) ^ 2 / (2 * (v : ℝ)) := by positivity
    linarith
  have hnn : 0 ≤ (|c| * Real.sqrt (2 * π))⁻¹ := by positivity
  calc _ ≤ (|c| * Real.sqrt (2 * π))⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp hnn
    _ = _ := by rw [mul_one, one_div]

end LSBA
