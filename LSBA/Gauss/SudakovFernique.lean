import LSBA.Gauss.StdGauss

/-!
# Sudakov–Fernique comparison for finitely many indices

For centered Gaussian processes `X_t = ⟨A_t, ξ⟩` and `Y_t = ⟨B_t, η⟩` on a finite nonempty
index set, with standard Gaussian `ξ`, `η`, the increment comparison
`𝔼(X_s - X_t)² ≤ 𝔼(Y_s - Y_t)²` for all `s, t` gives `𝔼 max_t X_t ≤ 𝔼 max_t Y_t`. This is the
comparison behind the bound `𝔼 λ_max(G) ≤ 2` for the GUE norm inputs of Appendix G.4
[app:compact-gaussian].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

namespace LSBA

/-! ### Linear maps given by coefficient arrays -/

/-- The continuous linear map `z ↦ (∑_j M t j * z j)_t`. -/
private def sfLin {T J : Type*} [Fintype J] (M : T → J → ℝ) : (J → ℝ) →L[ℝ] (T → ℝ) :=
  ContinuousLinearMap.pi fun t => ∑ j, M t j • ContinuousLinearMap.proj j

private lemma sfLin_apply {T J : Type*} [Fintype J] (M : T → J → ℝ) (z : J → ℝ) (t : T) :
    sfLin M z t = ∑ j, M t j * z j := by
  simp [sfLin]

/-- `|∑_j c_j z_j| ≤ ∑_j K_j |z_j|` when `|c_j| ≤ K_j`. -/
private lemma sf_abs_sum_le {J : Type*} [Fintype J] (c K z : J → ℝ) (hc : ∀ j, |c j| ≤ K j) :
    |∑ j, c j * z j| ≤ ∑ j, K j * |z j| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hc j) (abs_nonneg _)

/-! ### Log-sum-exp and soft-max weights -/

/-- The log-sum-exp `β⁻¹ log ∑_t exp (β u_t)`. -/
private def sfLse {T : Type*} [Fintype T] (β : ℝ) (u : T → ℝ) : ℝ :=
  β⁻¹ * Real.log (∑ t, Real.exp (β * u t))

/-- The soft-max weight `exp (β (u_t - lse_β u)) = exp (β u_t) / ∑_s exp (β u_s)`. -/
private def sfW {T : Type*} [Fintype T] (β : ℝ) (u : T → ℝ) (t : T) : ℝ :=
  Real.exp (β * (u t - sfLse β u))

section SoftMax

variable {T : Type*} [Fintype T] [Nonempty T] {β : ℝ}

private lemma sf_sum_exp_pos (β : ℝ) (u : T → ℝ) : 0 < ∑ t, Real.exp (β * u t) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

private lemma sfW_eq (hβ : β ≠ 0) (u : T → ℝ) (t : T) :
    sfW β u t = Real.exp (β * u t) / ∑ s, Real.exp (β * u s) := by
  rw [sfW, mul_sub, sfLse, ← mul_assoc, mul_inv_cancel₀ hβ, one_mul, Real.exp_sub,
    Real.exp_log (sf_sum_exp_pos β u)]

omit [Nonempty T] in
private lemma sfW_nonneg (β : ℝ) (u : T → ℝ) (t : T) : 0 ≤ sfW β u t := (Real.exp_pos _).le

private lemma sfW_sum (hβ : β ≠ 0) (u : T → ℝ) : ∑ t, sfW β u t = 1 := by
  simp_rw [sfW_eq hβ]
  rw [← Finset.sum_div, div_self (sf_sum_exp_pos β u).ne']

private lemma sfW_le_one (hβ : β ≠ 0) (u : T → ℝ) (t : T) : sfW β u t ≤ 1 := by
  rw [← sfW_sum hβ u]
  exact Finset.single_le_sum (fun s _ => sfW_nonneg β u s) (Finset.mem_univ t)

private lemma sf_log_card_nonneg : 0 ≤ Real.log (Fintype.card T) :=
  Real.log_nonneg (by exact_mod_cast Fintype.card_pos)

omit [Fintype T] [Nonempty T] in
private lemma sf_le_iSup [Finite T] (u : T → ℝ) (t : T) : u t ≤ ⨆ s, u s :=
  le_ciSup (Set.finite_range u).bddAbove t

/-- `max_t u_t ≤ lse_β u`. -/
private lemma sf_iSup_le_lse (hβ : 0 < β) (u : T → ℝ) : (⨆ t, u t) ≤ sfLse β u := by
  obtain ⟨t, ht⟩ := exists_eq_ciSup_of_finite (f := u)
  rw [← ht, sfLse, le_inv_mul_iff₀ hβ]
  rw [← Real.log_exp (β * u t)]
  exact Real.log_le_log (Real.exp_pos _)
    (Finset.single_le_sum (fun s _ => (Real.exp_pos (β * u s)).le) (Finset.mem_univ t))

/-- `lse_β u ≤ max_t u_t + log |T| / β`. -/
private lemma sf_lse_le (hβ : 0 < β) (u : T → ℝ) :
    sfLse β u ≤ (⨆ t, u t) + Real.log (Fintype.card T) / β := by
  set m := ⨆ t, u t
  have hS : ∑ t, Real.exp (β * u t) ≤ Fintype.card T * Real.exp (β * m) := by
    have := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) =>
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sf_le_iSup u t) hβ.le)
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hlog : Real.log (∑ t, Real.exp (β * u t)) ≤ Real.log (Fintype.card T) + β * m := by
    have hc : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
    calc Real.log (∑ t, Real.exp (β * u t)) ≤ Real.log (Fintype.card T * Real.exp (β * m)) :=
          Real.log_le_log (sf_sum_exp_pos β u) hS
      _ = Real.log (Fintype.card T) + β * m := by
          rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [sfLse, inv_mul_le_iff₀ hβ]
  calc Real.log (∑ t, Real.exp (β * u t)) ≤ Real.log (Fintype.card T) + β * m := hlog
    _ = β * (m + Real.log (Fintype.card T) / β) := by field_simp; ring

private lemma sf_abs_iSup_le (u : T → ℝ) : |⨆ t, u t| ≤ ∑ t, |u t| := by
  obtain ⟨t, ht⟩ := exists_eq_ciSup_of_finite (f := u)
  rw [← ht]
  exact Finset.single_le_sum (fun s _ => abs_nonneg (u s)) (Finset.mem_univ t)

private lemma sf_abs_lse_le (hβ : 0 < β) (u : T → ℝ) :
    |sfLse β u| ≤ ∑ t, |u t| + Real.log (Fintype.card T) / β := by
  have h1 := sf_iSup_le_lse hβ u
  have h2 := sf_lse_le hβ u
  have h3 := sf_abs_iSup_le u
  have h4 : 0 ≤ Real.log (Fintype.card T) / β := div_nonneg sf_log_card_nonneg hβ.le
  rw [abs_le] at h3 ⊢
  constructor <;> linarith [h3.1, h3.2]

/-- The gradient of the log-sum-exp is the vector of soft-max weights. -/
private lemma sfLse_hasFDerivAt (hβ : β ≠ 0) (u : T → ℝ) :
    HasFDerivAt (sfLse β)
      (∑ t, sfW β u t • (ContinuousLinearMap.proj t : (T → ℝ) →L[ℝ] ℝ)) u := by
  have hS : HasFDerivAt (fun v : T → ℝ => ∑ t, Real.exp (β * v t))
      (∑ t, Real.exp (β * u t) • (β • (ContinuousLinearMap.proj t : (T → ℝ) →L[ℝ] ℝ))) u :=
    HasFDerivAt.fun_sum fun t _ => ((hasFDerivAt_apply t u).const_mul β).exp
  have h := (hS.log (sf_sum_exp_pos β u).ne').const_mul β⁻¹
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, sfW_eq hβ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  field_simp

/-- The derivative of a soft-max weight: `∂ p_t = β p_t (e_t - p)`. -/
private lemma sfW_hasFDerivAt (hβ : β ≠ 0) (u : T → ℝ) (t : T) :
    HasFDerivAt (fun v => sfW β v t)
      (sfW β u t • β • ((ContinuousLinearMap.proj t : (T → ℝ) →L[ℝ] ℝ) -
        ∑ s, sfW β u s • (ContinuousLinearMap.proj s : (T → ℝ) →L[ℝ] ℝ))) u :=
  (((hasFDerivAt_apply t u).sub (sfLse_hasFDerivAt hβ u)).const_mul β).exp

private lemma sfW_deriv_norm_le (hβ : 0 < β) (u : T → ℝ) (t : T) :
    ‖sfW β u t • β • ((ContinuousLinearMap.proj t : (T → ℝ) →L[ℝ] ℝ) -
        ∑ s, sfW β u s • (ContinuousLinearMap.proj s : (T → ℝ) →L[ℝ] ℝ))‖ ≤ 2 * β := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv : ∀ s, |v s| ≤ ‖v‖ := fun s => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm v s
  have h1 : |∑ s, sfW β u s * v s| ≤ ‖v‖ := by
    have h1a : |∑ s, sfW β u s * v s| ≤ ∑ s, sfW β u s * |v s| :=
      sf_abs_sum_le _ _ _ fun s => (abs_of_nonneg (sfW_nonneg β u s)).le
    have h1b : ∑ s, sfW β u s * |v s| ≤ ∑ s, sfW β u s * ‖v‖ :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hv s) (sfW_nonneg β u s)
    rw [← Finset.sum_mul, sfW_sum hβ.ne', one_mul] at h1b
    exact h1a.trans h1b
  simp only [FunLike.coe_smul, FunLike.coe_sub,
    FunLike.coe_sum, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Real.norm_eq_abs]
  rw [abs_mul, abs_mul, abs_of_nonneg (sfW_nonneg β u t), abs_of_pos hβ]
  have h2 : |v t - ∑ s, sfW β u s * v s| ≤ 2 * ‖v‖ := by
    have := abs_sub (v t) (∑ s, sfW β u s * v s)
    linarith [hv t]
  have h3 := sfW_le_one hβ.ne' u t
  have h4 : 0 ≤ |v t - ∑ s, sfW β u s * v s| := abs_nonneg _
  calc sfW β u t * (β * |v t - ∑ s, sfW β u s * v s|)
      ≤ 1 * (β * (2 * ‖v‖)) := by
        gcongr
    _ = 2 * β * ‖v‖ := by ring

private lemma sfLse_continuous (hβ : β ≠ 0) : Continuous (sfLse (T := T) β) :=
  continuous_iff_continuousAt.2 fun u => (sfLse_hasFDerivAt hβ u).continuousAt

private lemma sfW_continuous (hβ : β ≠ 0) (t : T) : Continuous fun u : T → ℝ => sfW β u t :=
  continuous_iff_continuousAt.2 fun u => (sfW_hasFDerivAt hβ u t).continuousAt

private lemma sfW_contDiff (β : ℝ) (t : T) : ContDiff ℝ 1 fun u : T → ℝ => sfW β u t := by
  have hS : ContDiff ℝ 1 fun u : T → ℝ => ∑ s, Real.exp (β * u s) :=
    ContDiff.sum fun s _ => (contDiff_const.mul (contDiff_apply ℝ (fun _ : T => ℝ) s)).exp
  have hL : ContDiff ℝ 1 fun u : T → ℝ => sfLse β u :=
    contDiff_const.mul (hS.log fun u => (sf_sum_exp_pos β u).ne')
  exact (contDiff_const.mul ((contDiff_apply ℝ (fun _ : T => ℝ) t).sub hL)).exp

omit [Nonempty T] in
/-- Algebraic sign: for a probability vector `p` and an array `D` with
`D t t + D s s - 2 D s t ≥ 0`, `∑_t p_t (D t t - ∑_s p_s D s t) ≥ 0`. -/
private lemma sf_sign (p : T → ℝ) (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∑ t, p t = 1) (D : T → T → ℝ)
    (hD : ∀ s t, 0 ≤ D t t + D s s - 2 * D s t) :
    0 ≤ ∑ t, p t * (D t t - ∑ s, p s * D s t) := by
  have key : 2 * ∑ t, p t * (D t t - ∑ s, p s * D s t) =
      ∑ t, ∑ s, p t * p s * (D t t + D s s - 2 * D s t) := by
    have e1 : ∑ t, ∑ s, p t * p s * D t t = ∑ t, p t * D t t := by
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [show (∑ s, p t * p s * D t t) = p t * D t t * ∑ s, p s by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring, hp1, mul_one]
    have e2 : ∑ t, ∑ s, p t * p s * D s s = ∑ t, p t * D t t := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [show (∑ s, p s * p t * D t t) = p t * D t t * ∑ s, p s by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring, hp1, mul_one]
    have e3 : ∑ t, ∑ s, p t * p s * D s t = ∑ t, p t * ∑ s, p s * D s t := by
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    have e4 : ∑ t, ∑ s, p t * p s * (D t t + D s s - 2 * D s t) =
        ∑ t, ∑ s, p t * p s * D t t + ∑ t, ∑ s, p t * p s * D s s -
          2 * ∑ t, ∑ s, p t * p s * D s t := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
    rw [e4, e1, e2, e3, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have : 0 ≤ ∑ t, ∑ s, p t * p s * (D t t + D s s - 2 * D s t) :=
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun s _ =>
      mul_nonneg (mul_nonneg (hp0 t) (hp0 s)) (hD s t)
  linarith

end SoftMax

/-! ### Gaussian integrals -/

section Gauss

variable {J : Type*} [Fintype J]

private lemma sf_integrable_coord (j : J) : Integrable (fun z : J → ℝ => z j) (stdGauss J) := by
  have hg : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.mp (by simpa using memLp_id_gaussianReal (μ := 0) (v := 1) 1)
  have hmp := measurePreserving_eval (fun _ : J => gaussianReal 0 1) j
  exact Integrable.comp_measurable (g := id) (by unfold stdGauss; rw [hmp.map_eq]; exact hg)
    (measurable_pi_apply j)

private lemma sf_integrable_bound (K : J → ℝ) :
    Integrable (fun z : J → ℝ => ∑ j, K j * |z j|) (stdGauss J) :=
  integrable_finsetSum _ fun j _ => ((sf_integrable_coord j).abs).const_mul (K j)

/-- `∫ ∑_t ∑_j c_tj f_tj = ∑_t ∑_j c_tj ∫ f_tj` for integrable `f_tj`. -/
private lemma sf_integral_sum_sum {T α : Type*} [Fintype T] [MeasurableSpace α] {μ : Measure α}
    (c : T → J → ℝ) (f : T → J → α → ℝ) (hf : ∀ t j, Integrable (f t j) μ) :
    ∫ z, ∑ t, ∑ j, c t j * f t j z ∂μ = ∑ t, ∑ j, c t j * ∫ z, f t j z ∂μ := by
  rw [integral_finsetSum _ fun t _ => integrable_finsetSum _ fun j _ => (hf t j).const_mul _]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_finsetSum _ fun j _ => (hf t j).const_mul _]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- Gaussian integration by parts for a soft-max weight of a linear image:
`𝔼[z_j p_t(Mz)] = 𝔼[β p_t(Mz) (M t j - ∑_s p_s(Mz) M s j)]`. -/
private lemma sf_stein {T : Type*} [Fintype T] [Nonempty T] {β : ℝ} (hβ : 0 < β)
    (M : T → J → ℝ) (t : T) (j : J) :
    ∫ z, z j * sfW β (sfLin M z) t ∂(stdGauss J) =
      ∫ z, sfW β (sfLin M z) t * β * (M t j - ∑ s, sfW β (sfLin M z) s * M s j)
        ∂(stdGauss J) := by
  classical
  set L := sfLin (T := T) M
  set D : (J → ℝ) → ((J → ℝ) →L[ℝ] ℝ) := fun z =>
    (sfW β (L z) t • β • ((ContinuousLinearMap.proj t : (T → ℝ) →L[ℝ] ℝ) -
        ∑ s, sfW β (L z) s • (ContinuousLinearMap.proj s : (T → ℝ) →L[ℝ] ℝ))).comp L with hDdef
  have hD : ∀ z, HasFDerivAt (fun z => sfW β (L z) t) (D z) z := fun z =>
    (sfW_hasFDerivAt hβ.ne' (L z) t).comp z L.hasFDerivAt
  set F : (J → ℝ) → ℂ := fun z => ((sfW β (L z) t : ℝ) : ℂ) with hFdef
  have hF : ∀ z, HasFDerivAt F (Complex.ofRealCLM.comp (D z)) z := fun z =>
    Complex.ofRealCLM.hasFDerivAt.comp z (hD z)
  have hFc : ContDiff ℝ 1 F :=
    Complex.ofRealCLM.contDiff.comp ((sfW_contDiff β t).comp L.contDiff)
  set C : ℝ := 1 + 2 * β * ‖L‖
  have hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ 0 := fun z => by
    rw [pow_zero, mul_one, hFdef, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sfW_nonneg _ _ _)]
    have := sfW_le_one hβ.ne' (L z) t
    have : 0 ≤ 2 * β * ‖L‖ := by positivity
    linarith
  have hb' : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ 0 := fun z => by
    rw [pow_zero, mul_one, (hF z).fderiv]
    calc ‖Complex.ofRealCLM.comp (D z)‖ ≤ ‖Complex.ofRealCLM‖ * ‖D z‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (2 * β * ‖L‖) := by
          gcongr
          · exact Complex.ofRealCLM_norm.le
          · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_right (sfW_deriv_norm_le hβ (L z) t) (norm_nonneg _))
      _ ≤ C := by simp [C]
  have key := integral_coord_mul_stdGauss F hFc hb hb' j
  have hL1 : ∫ z, (z j : ℂ) * F z ∂(stdGauss J) =
      ((∫ z, z j * sfW β (L z) t ∂(stdGauss J) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp [hFdef])
  have hR1 : ∫ z, fderiv ℝ F z (Pi.single j 1) ∂(stdGauss J) =
      ((∫ z, sfW β (L z) t * β * (M t j - ∑ s, sfW β (L z) s * M s j) ∂(stdGauss J) : ℝ) :
        ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    change fderiv ℝ F z (Pi.single j 1) =
      ((sfW β (L z) t * β * (M t j - ∑ s, sfW β (L z) s * M s j) : ℝ) : ℂ)
    rw [(hF z).fderiv]
    have hLe : ∀ r, L (Pi.single j 1) r = M r j := fun r => by
      rw [sfLin_apply]
      simp [Pi.single_apply]
    simp [hDdef, hLe, mul_assoc]
  rw [hL1, hR1] at key
  exact_mod_cast key

end Gauss

/-- Change of variables along a measure-preserving map. -/
private lemma sf_integral_comp {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure γ} {f : α → γ} (hf : MeasurePreserving f μ ν) {g : γ → ℝ}
    (hg : AEStronglyMeasurable g ν) : ∫ x, g x ∂ν = ∫ z, g (f z) ∂μ := by
  rw [← integral_map hf.measurable.aemeasurable (by rw [hf.map_eq]; exact hg), hf.map_eq]

/-! ### Interpolation -/

/-- Interpolated coefficients `cos θ · a + sin θ · b`. -/
private def sfM {T J : Type*} (a b : T → J → ℝ) (θ : ℝ) : T → J → ℝ :=
  fun t j => Real.cos θ * a t j + Real.sin θ * b t j

/-- The `θ`-derivative `-sin θ · a + cos θ · b` of `sfM a b θ`. -/
private def sfN {T J : Type*} (a b : T → J → ℝ) (θ : ℝ) : T → J → ℝ :=
  fun t j => -Real.sin θ * a t j + Real.cos θ * b t j

private lemma sfLin_sfM_hasDerivAt {T J : Type*} [Fintype J] (a b : T → J → ℝ) (z : J → ℝ)
    (θ : ℝ) : HasDerivAt (fun θ => sfLin (sfM a b θ) z) (sfLin (sfN a b θ) z) θ := by
  rw [hasDerivAt_pi]
  intro t
  simp only [sfLin_apply, sfM, sfN]
  exact HasDerivAt.fun_sum fun j _ =>
    (((Real.hasDerivAt_cos θ).mul_const (a t j)).add
      ((Real.hasDerivAt_sin θ).mul_const (b t j))).mul_const (z j)

/-- Sudakov–Fernique on one Gaussian space, for coefficient arrays with disjoint supports, with
the soft-max error `log |T| / β`. -/
private lemma sf_core {T J : Type*} [Fintype T] [Nonempty T] [Fintype J]
    (a b : T → J → ℝ) (hab : ∀ s t j, a s j * b t j = 0)
    (h : ∀ s t, ∑ j, (a s j - a t j) ^ 2 ≤ ∑ j, (b s j - b t j) ^ 2) {β : ℝ} (hβ : 0 < β) :
    ∫ z, (⨆ t, sfLin a z t) ∂(stdGauss J) ≤
      ∫ z, (⨆ t, sfLin b z t) ∂(stdGauss J) + Real.log (Fintype.card T) / β := by
  classical
  set F : ℝ → (J → ℝ) → ℝ := fun θ z => sfLse β (sfLin (sfM a b θ) z) with hFdef
  set F' : ℝ → (J → ℝ) → ℝ := fun θ z =>
    ∑ t, sfW β (sfLin (sfM a b θ) z) t * sfLin (sfN a b θ) z t with hF'def
  set K : T → J → ℝ := fun t j => |a t j| + |b t j| with hKdef
  set bnd : (J → ℝ) → ℝ := fun z => ∑ t, ∑ j, K t j * |z j| with hbnddef
  have hbnd : Integrable bnd (stdGauss J) :=
    integrable_finsetSum _ fun t _ => sf_integrable_bound (K t)
  have hcs : ∀ θ x y : ℝ, |Real.cos θ * x + Real.sin θ * y| ≤ |x| + |y| := fun θ x y => by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one θ)
    · exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one θ)
  have hlinM : ∀ θ z t, |sfLin (sfM a b θ) z t| ≤ ∑ j, K t j * |z j| := fun θ z t => by
    rw [sfLin_apply]
    exact sf_abs_sum_le _ _ _ fun j => hcs θ _ _
  have hlinN : ∀ θ z t, |sfLin (sfN a b θ) z t| ≤ ∑ j, K t j * |z j| := fun θ z t => by
    rw [sfLin_apply]
    refine sf_abs_sum_le _ _ _ fun j => ?_
    have := hcs (θ + π / 2) (a t j) (b t j)
    simpa [sfN, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] using this
  have hFc : ∀ θ, Continuous (F θ) := fun θ =>
    (sfLse_continuous hβ.ne').comp (sfLin (sfM a b θ)).continuous
  have hF'c : ∀ θ, Continuous (F' θ) := fun θ =>
    continuous_finsetSum _ fun t _ =>
      ((sfW_continuous hβ.ne' t).comp (sfLin (sfM a b θ)).continuous).mul
        ((continuous_apply t).comp (sfLin (sfN a b θ)).continuous)
  have hlog : 0 ≤ Real.log (Fintype.card T) / β := div_nonneg sf_log_card_nonneg hβ.le
  have hFint : ∀ θ, Integrable (F θ) (stdGauss J) := fun θ =>
    (hbnd.add (integrable_const (Real.log (Fintype.card T) / β))).mono'
      (hFc θ).aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        refine (sf_abs_lse_le hβ _).trans ?_
        simp only [Pi.add_apply, hbnddef]
        exact add_le_add (Finset.sum_le_sum fun t _ => hlinM θ z t) le_rfl)
  have hF'b : ∀ θ z, ‖F' θ z‖ ≤ bnd z := fun θ z => by
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [abs_mul, abs_of_nonneg (sfW_nonneg _ _ _)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (sfW_le_one hβ.ne' _ t)).trans (hlinN θ z t)
  have hderiv : ∀ θ z, HasDerivAt (fun θ => F θ z) (F' θ z) θ := fun θ z => by
    have := (sfLse_hasFDerivAt hβ.ne' (sfLin (sfM a b θ) z)).comp_hasDerivAt θ
      (sfLin_sfM_hasDerivAt a b z θ)
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul] at this
    exact this
  set ψ : ℝ → ℝ := fun θ => ∫ z, F θ z ∂(stdGauss J) with hψdef
  have hψ : ∀ θ, HasDerivAt ψ (∫ z, F' θ z ∂(stdGauss J)) θ := fun θ =>
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le Filter.univ_mem
      (Filter.Eventually.of_forall fun θ => (hFc θ).aestronglyMeasurable) (hFint θ)
      (hF'c θ).aestronglyMeasurable (ae_of_all _ fun z θ _ => hF'b θ z) hbnd
      (ae_of_all _ fun z θ _ => hderiv θ z)).2
  -- the derivative is nonnegative on `[0, π/2]`
  have hpos : ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2), 0 ≤ ∫ z, F' θ z ∂(stdGauss J) := by
    intro θ hθ
    set M := sfM a b θ
    set N := sfN a b θ
    have hint1 : ∀ t j, Integrable (fun z => z j * sfW β (sfLin M z) t) (stdGauss J) :=
      fun t j => (sf_integrable_coord j).abs.mono'
        (((continuous_apply j).mul
          ((sfW_continuous hβ.ne' t).comp (sfLin M).continuous)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sfW_nonneg _ _ _)]
          exact mul_le_of_le_one_right (abs_nonneg _) (sfW_le_one hβ.ne' _ t))
    have hint2 : ∀ t j, Integrable
        (fun z => sfW β (sfLin M z) t * β * (M t j - ∑ s, sfW β (sfLin M z) s * M s j))
        (stdGauss J) := fun t j =>
      Integrable.of_bound
        ((((sfW_continuous hβ.ne' t).comp (sfLin M).continuous).mul continuous_const).mul
          (continuous_const.sub (continuous_finsetSum _ fun s _ =>
            ((sfW_continuous hβ.ne' s).comp (sfLin M).continuous).mul
              continuous_const))).aestronglyMeasurable
        (β * (|M t j| + ∑ s, |M s j|))
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sfW_nonneg _ _ _),
            abs_of_pos hβ]
          have h1 : |M t j - ∑ s, sfW β (sfLin M z) s * M s j| ≤ |M t j| + ∑ s, |M s j| := by
            refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
            rw [abs_mul, abs_of_nonneg (sfW_nonneg _ _ _)]
            exact mul_le_of_le_one_left (abs_nonneg _) (sfW_le_one hβ.ne' _ s)
          have h2 := sfW_le_one hβ.ne' (sfLin M z) t
          have h3 := sfW_nonneg β (sfLin M z) t
          calc sfW β (sfLin M z) t * β * |M t j - ∑ s, sfW β (sfLin M z) s * M s j|
              ≤ 1 * β * (|M t j| + ∑ s, |M s j|) := by gcongr
            _ = β * (|M t j| + ∑ s, |M s j|) := by ring)
    have e1 : ∫ z, F' θ z ∂(stdGauss J) =
        ∑ t, ∑ j, N t j * ∫ z, z j * sfW β (sfLin M z) t ∂(stdGauss J) := by
      rw [← sf_integral_sum_sum N _ hint1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hF'def, sfLin_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e1]
    simp_rw [sf_stein hβ M]
    rw [← sf_integral_sum_sum N _ hint2]
    refine integral_nonneg fun z => ?_
    -- pointwise sign
    set p := fun t => sfW β (sfLin M z) t
    set G : T → T → ℝ := fun s t => ∑ j, M s j * N t j
    have hG : ∀ s t, G s t =
        Real.sin θ * Real.cos θ * (∑ j, b s j * b t j - ∑ j, a s j * a t j) := by
      intro s t
      simp only [G, M, N, sfM, sfN, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination Real.cos θ ^ 2 * hab s t j - Real.sin θ ^ 2 * hab t s j
    have hexp : ∑ t, ∑ j, N t j * (p t * β * (M t j - ∑ s, p s * M s j)) =
        β * ∑ t, p t * (G t t - ∑ s, p s * G s t) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      have e1 : ∑ j, N t j * (∑ s, p s * M s j) = ∑ s, p s * G s t := by
        simp only [G, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring
      have e2 : ∀ j, N t j * (p t * β * (M t j - ∑ s, p s * M s j)) =
          p t * β * (M t j * N t j) - p t * β * (N t j * ∑ s, p s * M s j) := fun j => by ring
      simp_rw [e2]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e1]
      simp only [G]
      ring
    change 0 ≤ ∑ t, ∑ j, N t j * (p t * β * (M t j - ∑ s, p s * M s j))
    rw [hexp]
    have hsc : 0 ≤ Real.sin θ * Real.cos θ :=
      mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
    refine mul_nonneg hβ.le ?_
    simp_rw [hG]
    set D : T → T → ℝ := fun s t => ∑ j, b s j * b t j - ∑ j, a s j * a t j
    have hsign := sf_sign p (fun t => sfW_nonneg _ _ _) (sfW_sum hβ.ne' _) D (fun s t => by
      have := h s t
      have ea : ∑ j, (a s j - a t j) ^ 2 =
          ∑ j, a t j * a t j + ∑ j, a s j * a s j - 2 * ∑ j, a s j * a t j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      have eb : ∑ j, (b s j - b t j) ^ 2 =
          ∑ j, b t j * b t j + ∑ j, b s j * b s j - 2 * ∑ j, b s j * b t j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      simp only [D]
      linarith)
    have : ∑ t, p t * (Real.sin θ * Real.cos θ * D t t -
        ∑ s, p s * (Real.sin θ * Real.cos θ * D s t)) =
        Real.sin θ * Real.cos θ * ∑ t, p t * (D t t - ∑ s, p s * D s t) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [show ∑ s, p s * (Real.sin θ * Real.cos θ * D s t) =
          Real.sin θ * Real.cos θ * ∑ s, p s * D s t by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring]
      ring
    simp only [D] at this hsign
    rw [this]
    exact mul_nonneg hsc hsign
  have hmono : MonotoneOn ψ (Set.Icc 0 (π / 2)) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun θ _ => (hψ θ).continuousAt.continuousWithinAt)
      (fun θ _ => (hψ θ).differentiableAt.differentiableWithinAt)
      (fun θ hθ => by rw [(hψ θ).deriv]; exact hpos θ (interior_subset hθ))
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have h0 : ψ 0 ≤ ψ (π / 2) := hmono ⟨le_rfl, hpi⟩ ⟨hpi, le_rfl⟩ hpi
  have hM0 : sfM a b 0 = a := by funext t j; simp [sfM]
  have hM1 : sfM a b (π / 2) = b := by funext t j; simp [sfM]
  have hF0 : F 0 = fun z => sfLse β (sfLin a z) := by
    funext z; simp only [hFdef, hM0]
  have hF1 : F (π / 2) = fun z => sfLse β (sfLin b z) := by
    funext z; simp only [hFdef, hM1]
  have hmaxa : Integrable (fun z => ⨆ t, sfLin a z t) (stdGauss J) :=
    hbnd.mono' (Measurable.iSup fun t =>
        ((continuous_apply t).comp (sfLin a).continuous).measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        refine (sf_abs_iSup_le _).trans (Finset.sum_le_sum fun t _ => ?_)
        rw [sfLin_apply]
        exact sf_abs_sum_le _ _ _ fun j => le_add_of_nonneg_right (abs_nonneg _))
  have hmaxb : Integrable (fun z => ⨆ t, sfLin b z t) (stdGauss J) :=
    hbnd.mono' (Measurable.iSup fun t =>
        ((continuous_apply t).comp (sfLin b).continuous).measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        refine (sf_abs_iSup_le _).trans (Finset.sum_le_sum fun t _ => ?_)
        rw [sfLin_apply]
        exact sf_abs_sum_le _ _ _ fun j => le_add_of_nonneg_left (abs_nonneg _))
  calc ∫ z, (⨆ t, sfLin a z t) ∂(stdGauss J) ≤ ψ 0 := by
        refine integral_mono hmaxa (hFint 0) fun z => ?_
        rw [hF0]
        exact sf_iSup_le_lse hβ _
    _ ≤ ψ (π / 2) := h0
    _ ≤ ∫ z, ((⨆ t, sfLin b z t) + Real.log (Fintype.card T) / β) ∂(stdGauss J) := by
        refine integral_mono (hFint _) (hmaxb.add (integrable_const _)) fun z => ?_
        simp only [hF1]
        exact sf_lse_le hβ _
    _ = ∫ z, (⨆ t, sfLin b z t) ∂(stdGauss J) + Real.log (Fintype.card T) / β := by
        rw [integral_add hmaxb (integrable_const _), integral_const]
        simp

/-- Sudakov–Fernique: if `Σ_i (A_s i - A_t i)² ≤ Σ_k (B_s k - B_t k)²` for all `s, t`, then
`𝔼 max_t ⟨A_t, ξ⟩ ≤ 𝔼 max_t ⟨B_t, η⟩` for standard Gaussian `ξ`, `η`. -/
theorem sudakov_fernique {T ι κ : Type*} [Fintype T] [Nonempty T] [Fintype ι] [Fintype κ]
    (A : T → ι → ℝ) (B : T → κ → ℝ)
    (h : ∀ s t, ∑ i, (A s i - A t i) ^ 2 ≤ ∑ k, (B s k - B t k) ^ 2) :
    ∫ x, (⨆ t, ∑ i, A t i * x i) ∂(stdGauss ι) ≤
      ∫ y, (⨆ t, ∑ k, B t k * y k) ∂(stdGauss κ) := by
  classical
  -- both processes on the Gaussian space `ℝ^(ι ⊕ κ)`, with disjoint coefficient supports
  set a : T → ι ⊕ κ → ℝ := fun t => Sum.elim (A t) 0 with hadef
  set b : T → ι ⊕ κ → ℝ := fun t => Sum.elim 0 (B t) with hbdef
  have hab : ∀ s t j, a s j * b t j = 0 := by
    intro s t j
    rcases j with i | k <;> simp [a, b]
  have hh : ∀ s t, ∑ j, (a s j - a t j) ^ 2 ≤ ∑ j, (b s j - b t j) ^ 2 := by
    intro s t
    simpa [a, b, Fintype.sum_sum_type] using h s t
  have hmp := measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ κ => gaussianReal 0 1)
  have hl : MeasurePreserving (fun z : ι ⊕ κ → ℝ => fun i => z (Sum.inl i))
      (stdGauss (ι ⊕ κ)) (stdGauss ι) :=
    measurePreserving_fst.comp hmp
  have hr : MeasurePreserving (fun z : ι ⊕ κ → ℝ => fun k => z (Sum.inr k))
      (stdGauss (ι ⊕ κ)) (stdGauss κ) :=
    measurePreserving_snd.comp hmp
  have hA : ∫ x, (⨆ t, ∑ i, A t i * x i) ∂(stdGauss ι) =
      ∫ z, (⨆ t, sfLin a z t) ∂(stdGauss (ι ⊕ κ)) := by
    have hm : Measurable fun x : ι → ℝ => ⨆ t, ∑ i, A t i * x i :=
      Measurable.iSup fun t => (continuous_finsetSum _ fun i _ =>
        continuous_const.mul (continuous_apply i)).measurable
    rw [sf_integral_comp hl hm.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [sfLin_apply, a, Fintype.sum_sum_type]
  have hB : ∫ y, (⨆ t, ∑ k, B t k * y k) ∂(stdGauss κ) =
      ∫ z, (⨆ t, sfLin b z t) ∂(stdGauss (ι ⊕ κ)) := by
    have hm : Measurable fun x : κ → ℝ => ⨆ t, ∑ k, B t k * x k :=
      Measurable.iSup fun t => (continuous_finsetSum _ fun k _ =>
        continuous_const.mul (continuous_apply k)).measurable
    rw [sf_integral_comp hr hm.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [sfLin_apply, b, Fintype.sum_sum_type]
  rw [hA, hB]
  -- let the soft-max parameter `β` tend to infinity
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hL := sf_log_card_nonneg (T := T)
  set β : ℝ := (Real.log (Fintype.card T) + 1) / ε with hβdef
  have hβ : 0 < β := div_pos (by linarith) hε
  refine (sf_core a b hab hh hβ).trans (add_le_add le_rfl ?_)
  rw [div_le_iff₀ hβ, hβdef]
  field_simp
  linarith

end LSBA
