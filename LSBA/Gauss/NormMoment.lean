import LSBA.Gauss.GUELaw

/-!
# Norm moments of a GUE block

A fractional moment bound for the operator norm of one GUE block (1.2) [eq:covariance], used for the
incomplete batch in the proof of Lemma 8.6 [up:lem:operator-reduction].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

private theorem normMoment_opNorm_sq_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    ‖A‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have hS : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hle : ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
    rw [Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have hx : ‖x‖ = Real.sqrt (∑ j, ‖x.ofLp j‖ ^ 2) := EuclideanSpace.norm_eq x
    rw [EuclideanSpace.norm_eq, hx, ← Real.sqrt_mul hS]
    change √(∑ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2) ≤ _
    refine Real.sqrt_le_sqrt ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : ‖(A *ᵥ x.ofLp) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 := by
      calc ‖(A *ᵥ x.ofLp) i‖ ^ 2 = ‖∑ j, A i j * x.ofLp j‖ ^ 2 := by
            simp [Matrix.mulVec, dotProduct]
        _ ≤ (∑ j, ‖A i j * x.ofLp j‖) ^ 2 := by
            gcongr; exact norm_sum_le _ _
        _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 := by
            simp_rw [norm_mul]
            exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    exact h1
  calc ‖A‖ ^ 2 ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt hS

private theorem normMoment_entry (W L : ℕ) (a : Fin L) (α β : Fin W) :
    Integrable (fun ω => ‖gueBlock W L ω a α β‖ ^ 2) (μ W L) ∧
      ∫ ω, ‖gueBlock W L ω a α β‖ ^ 2 ∂(μ W L) = (W : ℝ)⁻¹ := by
  have hW : 0 < W := Fin.pos α
  have hc : ∫ ω, ((‖gueBlock W L ω a α β‖ ^ 2 : ℝ) : ℂ) ∂(μ W L) = (W : ℂ)⁻¹ := by
    have := gueBlock_covariance W L a a α β β α
    simp only [and_self, ite_true] at this
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have h := (gueBlock_isHermitian W L ω a).apply β α
    simp only at h ⊢
    rw [← h, Complex.star_def, Complex.mul_conj']
    push_cast
    rfl
  rw [integral_complex_ofReal] at hc
  have hr : ∫ ω, ‖gueBlock W L ω a α β‖ ^ 2 ∂(μ W L) = (W : ℝ)⁻¹ := by
    have := congrArg Complex.re hc
    simpa using this
  refine ⟨?_, hr⟩
  by_contra hni
  rw [integral_undef hni] at hr
  have : (0 : ℝ) < (W : ℝ)⁻¹ := by positivity
  linarith

private theorem normMoment_lintegral_sq (W L : ℕ) (a : Fin L) :
    ∫⁻ ω, ‖gueBlock W L ω a‖ₑ ^ (2 : ℝ) ∂(μ W L) ≤ ENNReal.ofReal (W : ℝ) := by
  have hle : ∀ ω, ‖gueBlock W L ω a‖ₑ ^ (2 : ℝ) ≤
      ∑ α, ∑ β, ENNReal.ofReal (‖gueBlock W L ω a α β‖ ^ 2) := by
    intro ω
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.rpow_two]
    calc ENNReal.ofReal (‖gueBlock W L ω a‖ ^ 2)
        ≤ ENNReal.ofReal (∑ α, ∑ β, ‖gueBlock W L ω a α β‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (normMoment_opNorm_sq_le _)
      _ = ∑ α, ∑ β, ENNReal.ofReal (‖gueBlock W L ω a α β‖ ^ 2) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun α _ =>
            Finset.sum_nonneg fun β _ => by positivity]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg fun β _ => by positivity]
  have hint : ∀ α β : Fin W, ∫⁻ ω, ENNReal.ofReal (‖gueBlock W L ω a α β‖ ^ 2) ∂(μ W L) =
      ENNReal.ofReal (W : ℝ)⁻¹ := by
    intro α β
    obtain ⟨h1, h2⟩ := normMoment_entry W L a α β
    rw [← h2, ofReal_integral_eq_lintegral_ofReal h1
      (Filter.Eventually.of_forall fun ω => by positivity)]
  have hmeas : ∀ α β : Fin W,
      AEMeasurable (fun ω => ENNReal.ofReal (‖gueBlock W L ω a α β‖ ^ 2)) (μ W L) :=
    fun α β => (normMoment_entry W L a α β).1.aemeasurable.ennreal_ofReal
  calc ∫⁻ ω, ‖gueBlock W L ω a‖ₑ ^ (2 : ℝ) ∂(μ W L)
      ≤ ∫⁻ ω, ∑ α, ∑ β, ENNReal.ofReal (‖gueBlock W L ω a α β‖ ^ 2) ∂(μ W L) :=
        lintegral_mono hle
    _ = ∑ α : Fin W, ∑ β : Fin W, ENNReal.ofReal (W : ℝ)⁻¹ := by
        rw [lintegral_finsetSum' (f := fun α ω =>
          ∑ β, ENNReal.ofReal (‖gueBlock W L ω a α β‖ ^ 2)) _
          fun α _ => Finset.aemeasurable_fun_sum _ fun β _ => hmeas α β]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [lintegral_finsetSum' (f := fun β ω =>
          ENNReal.ofReal (‖gueBlock W L ω a α β‖ ^ 2)) _ fun β _ => hmeas α β]
        exact Finset.sum_congr rfl fun β _ => hint α β
    _ ≤ ENNReal.ofReal (W : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rcases Nat.eq_zero_or_pos W with h0 | hpos
        · subst h0; simp
        · have hW : (0 : ℝ) < W := by exact_mod_cast hpos
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            mul_inv_cancel₀ hW.ne']
          simp

/-- `𝔼‖V_a‖^s ≤ W^{s/2}` for `0 < s ≤ 2`, from `𝔼‖V_a‖²_HS = W` (1.2) [eq:covariance]. -/
theorem lintegral_norm_gueBlock_rpow_le (W L : ℕ) (a : Fin L) {s : ℝ} (hs0 : 0 < s)
    (hs2 : s ≤ 2) :
    ∫⁻ ω, ‖gueBlock W L ω a‖ₑ ^ s ∂(μ W L) ≤ ENNReal.ofReal ((W : ℝ) ^ (s / 2)) := by
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hrhs : ENNReal.ofReal ((W : ℝ) ^ (s / 2)) = ENNReal.ofReal (W : ℝ) ^ (s / 2) :=
    (ENNReal.ofReal_rpow_of_nonneg hW (by positivity)).symm
  rw [hrhs]
  have hX : AEMeasurable (fun ω => ‖gueBlock W L ω a‖ₑ) (μ W L) := by
    have h : AEMeasurable (fun ω => gueBlock W L ω a) (μ W L) := by
      refine aemeasurable_pi_iff.2 fun α => aemeasurable_pi_iff.2 fun β => ?_
      exact (integrable_gueBlock W L a α β).aestronglyMeasurable.aemeasurable
    exact h.enorm
  have hsq := normMoment_lintegral_sq W L a
  rcases hs2.lt_or_eq with hlt | rfl
  · have hp : (1 : ℝ) < 2 / s := by rw [lt_div_iff₀ hs0]; linarith
    have hpq := Real.HolderConjugate.conjExponent hp
    have hf : AEMeasurable (fun ω => ‖gueBlock W L ω a‖ₑ ^ s) (μ W L) :=
      hX.pow_const s
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ W L) hpq hf
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    have h1 : ∀ ω, (fun ω => ‖gueBlock W L ω a‖ₑ ^ s) ω * (1 : ℝ≥0∞) =
        ‖gueBlock W L ω a‖ₑ ^ s := fun ω => mul_one _
    simp only [Pi.mul_apply, mul_one] at hH
    have h2 : ∀ ω, (‖gueBlock W L ω a‖ₑ ^ s) ^ (2 / s) = ‖gueBlock W L ω a‖ₑ ^ (2 : ℝ) := by
      intro ω
      rw [← ENNReal.rpow_mul]
      congr 1
      field_simp
    simp only [h2, ENNReal.one_rpow, lintegral_const, measure_univ, mul_one] at hH
    refine hH.trans ?_
    have : 1 / (2 / s) = s / 2 := by field_simp
    rw [this]
    exact ENNReal.rpow_le_rpow hsq (by positivity)
  · simpa using hsq

end LSBA
