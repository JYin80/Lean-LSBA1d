import LSBA.Upper.CorrectorSolve
import LSBA.Upper.CorrectorRemainder

/-!
# The corrected drift on the good set

The deterministic part of Lemma 11.9 [lg:lem:centerQ] (Section 11.3.4 [lg:sec:cocycle-correction],
(11.64) [lg:eq:corrector-coefficient-cancellation], (11.66) [lg:eq:centerdefect], (11.70)
[lg:eq:smalldefect]): for `ε > 0` and `R` with `2εR > 1` there are a finite index set and
coefficients `q(g, E)` with `Σ |q_k| ≤ C g⁻²` such that, for `0 < η < min(ε, 1/4)` and large `W`,
every state of the good set with exponent `η/2` satisfies
`|P_g c − (P_g − I) Q_g − ½ h_θ² g⁻² W⁻¹| ≤ ⅙ h_θ² g⁻² W⁻¹` for all `g ≥ W^ε`.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Measurability and linearity of `P_g` on the corrected observables -/

private lemma cd_measurable_gb (W : ℕ) : Measurable fun ω : Ω W 1 => gueBlock W 1 ω 0 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma cd_cont_vecForm {W : ℕ} :
    Continuous fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) => vecForm q.1 q.2 := by
  have hc : Continuous (fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) =>
      Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) q.1 q.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM
  exact continuous_snd.inner hc

private lemma cd_measurable_inv {W : ℕ} :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => X⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have h : (fun X : Matrix (Fin W) (Fin W) ℂ => X⁻¹ i j) =
      fun X => (X.det)⁻¹ * X.adjugate i j := by
    funext X
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [h]
  have hd : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => X.det := continuous_id.matrix_det
  have ha : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => X.adjugate i j :=
    (continuous_id.matrix_adjugate).matrix_elem i j
  exact hd.measurable.inv.mul ha.measurable

private lemma cd_measurable_zpow {W : ℕ} (k : ℤ) :
    Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A ^ k := by
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact (continuous_id.pow n).measurable
  | negSucc n =>
    simp only [zpow_negSucc]
    exact cd_measurable_inv.comp (continuous_id.pow _).measurable

private lemma cd_measurable_obsEval (g : ℝ) (W : ℕ) (p : ObsPoly) :
    Measurable fun X : State W => obsEval g X p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [obsEval, aeval_C]; exact measurable_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p v hp =>
    simp only [map_mul]
    refine hp.mul ?_
    cases v with
    | m k =>
      simp only [obsEval, aeval_X, obsM]
      exact measurable_const.mul ((continuous_id.matrix_trace).measurable.comp
        ((cd_measurable_zpow k.1).comp measurable_fst))
    | f k =>
      simp only [obsEval, aeval_X, obsF]
      have h1 : Measurable fun X : State W => (X.1 ^ k.1, X.2) :=
        ((cd_measurable_zpow k.1).comp measurable_fst).prodMk measurable_snd
      have h2 := (cd_cont_vecForm (W := W)).measurable.comp h1
      exact h2
    | w => simp only [obsEval, aeval_X]; exact measurable_const
    | γ => simp only [obsEval, aeval_X]; exact measurable_const

private lemma cd_integrable (g E : ℝ) {W : ℕ} (hW : 1 ≤ W) (hg : 1 ≤ g) {X : State W}
    (hX : IsState X) (p : ObsPoly) :
    Integrable (fun ω : Ω W 1 => obsEval g (stepState g E X (gueBlock W 1 ω 0)) p) (μ W 1) := by
  have hS : Measurable fun V : Matrix (Fin W) (Fin W) ℂ => (X, V) :=
    Measurable.prodMk measurable_const measurable_id
  have hm : Measurable fun ω : Ω W 1 => obsEval g (stepState g E X (gueBlock W 1 ω 0)) p :=
    (cd_measurable_obsEval g W p).comp (((measurable_stepState g E W).comp hS).comp
      (cd_measurable_gb W))
  exact Integrable.of_bound hm.aestronglyMeasurable (∑ d ∈ p.support, ‖p.coeff d‖)
    (Filter.Eventually.of_forall fun ω =>
      norm_obsEval_le hW hg (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)) p)

/-- `(P_g − I) Q_g` is `Re Σ q_r (P_g F_r − F_r)`. -/
private lemma cd_Q_sub (g E : ℝ) {W : ℕ} (hW : 1 ≤ W) (hg : 1 ≤ g) {X : State W}
    (hX : IsState X) (R : ℕ) (Ks : Finset NzInt) (q : NzInt → ℂ) :
    transOp g E (corrQ g E R Ks q) X - corrQ g E R Ks q X =
      (∑ r ∈ Ks, q r * (transOp g E (fun Y => obsEval g Y (corrObsF E R r)) X -
        obsEval g X (corrObsF E R r))).re := by
  have hint : ∀ r ∈ Ks, Integrable (fun ω : Ω W 1 =>
      q r * obsEval g (stepState g E X (gueBlock W 1 ω 0)) (corrObsF E R r)) (μ W 1) :=
    fun r _ => (cd_integrable g E hW hg hX _).const_mul _
  have h1 : transOp g E (corrQ g E R Ks q) X =
      (∑ r ∈ Ks, q r * transOp g E (fun Y => obsEval g Y (corrObsF E R r)) X).re := by
    unfold transOp corrQ
    have h2 := integral_re (μ := μ W 1) (𝕜 := ℂ) (f := fun ω : Ω W 1 => ∑ r ∈ Ks,
      q r * obsEval g (stepState g E X (gueBlock W 1 ω 0)) (corrObsF E R r))
      (integrable_finsetSum _ hint)
    simp only [RCLike.re_to_complex] at h2
    rw [h2, integral_finsetSum _ hint]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    exact integral_const_mul _ _
  rw [h1]
  simp only [corrQ, mul_sub, Finset.sum_sub_distrib, Complex.sub_re]

/-- The cancellation of (11.64) [lg:eq:corrector-coefficient-cancellation] on one state: if
`q` is supported in `S ⊆ Ks`, solves the coefficient equation outside `S` exactly and up to
`Bs` on `S`, and the remainders of the linear expansions (11.62)
[lg:eq:corrector-linear-expansions] are bounded by `B₀` and `BT`, then the corrected drift
is at most `B₀ + Bs + (Σ |q_k|) BT`. -/
private lemma cd_core (g E : ℝ) {W : ℕ} (hW : 1 ≤ W) (hg : 1 ≤ g) {X : State W}
    (hX : IsState X) (R : ℕ) (Ks S : Finset NzInt) (hS : S ⊆ Ks) (q : NzInt → ℂ)
    (hq0 : ∀ k ∉ S, q k = 0)
    (hdrift : ∀ k ∉ S, driftCoeff g E R k = ∑ r ∈ S, corrMat g E R k r * q r)
    {B₀ BT Bs Sq : ℝ} (hBT : 0 ≤ BT)
    (hF : ∀ k ∈ S, ‖obsEval g X (corrObsF E R k)‖ ≤ 1)
    (hT₀ : ‖((incMean g E X : ℝ) : ℂ) - ((normalH E ^ 2 / (2 * W * g ^ 2) : ℝ) : ℂ) -
        ∑ k ∈ Ks, driftCoeff g E R k * obsEval g X (corrObsF E R k)‖ ≤ B₀)
    (hTr : ∀ r ∈ S, ‖transOp g E (fun Y => obsEval g Y (corrObsF E R r)) X -
        obsEval g X (corrObsF E R r) -
        ∑ k ∈ Ks, corrMat g E R k r * obsEval g X (corrObsF E R k)‖ ≤ BT)
    (hres : ∑ k ∈ S, ‖driftCoeff g E R k - ∑ r ∈ S, corrMat g E R k r * q r‖ ≤ Bs)
    (hsq : ∑ k ∈ S, ‖q k‖ ≤ Sq) :
    |incMean g E X - (transOp g E (corrQ g E R Ks q) X - corrQ g E R Ks q X) -
        normalH E ^ 2 / (2 * W * g ^ 2)| ≤ B₀ + Bs + Sq * BT := by
  rw [cd_Q_sub g E hW hg hX R Ks q]
  set F : NzInt → ℂ := fun k => obsEval g X (corrObsF E R k) with hFdef
  set PF : NzInt → ℂ := fun r => transOp g E (fun Y => obsEval g Y (corrObsF E R r)) X with hPF
  set Aq : NzInt → ℂ := fun k => ∑ r ∈ S, corrMat g E R k r * q r with hAq
  set D : NzInt → ℂ := fun k => driftCoeff g E R k with hD
  set T : NzInt → ℂ := fun r => PF r - F r - ∑ k ∈ Ks, corrMat g E R k r * F k with hT
  set T₀ : ℂ := ((incMean g E X : ℝ) : ℂ) - ((normalH E ^ 2 / (2 * W * g ^ 2) : ℝ) : ℂ) -
    ∑ k ∈ Ks, D k * F k with hT₀def
  have hsumKs : ∑ r ∈ Ks, q r * (PF r - F r) = ∑ r ∈ S, q r * (PF r - F r) :=
    (Finset.sum_subset hS fun r _ hr => by rw [hq0 r hr, zero_mul]).symm
  have hexp : ∑ r ∈ S, q r * (PF r - F r) = ∑ r ∈ S, q r * T r + ∑ k ∈ Ks, Aq k * F k := by
    have e1 : ∑ r ∈ S, q r * (∑ k ∈ Ks, corrMat g E R k r * F k) =
        ∑ k ∈ Ks, Aq k * F k := by
      simp only [hAq, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ => by ring
    rw [← e1, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by simp only [hT]; ring
  have hmid : ∑ k ∈ Ks, (D k - Aq k) * F k = ∑ k ∈ S, (D k - Aq k) * F k :=
    (Finset.sum_subset hS fun k _ hk => by
      simp only [hD, hAq]
      rw [hdrift k hk, sub_self, zero_mul]).symm
  have hsplit : ∑ k ∈ Ks, (D k - Aq k) * F k = ∑ k ∈ Ks, D k * F k - ∑ k ∈ Ks, Aq k * F k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hz : ((incMean g E X : ℝ) : ℂ) - ((normalH E ^ 2 / (2 * W * g ^ 2) : ℝ) : ℂ) -
      ∑ r ∈ Ks, q r * (PF r - F r) =
      T₀ + ∑ k ∈ S, (D k - Aq k) * F k - ∑ r ∈ S, q r * T r := by
    rw [hsumKs, hexp, ← hmid, hsplit, hT₀def]
    ring
  have hre : incMean g E X - (∑ r ∈ Ks, q r * (PF r - F r)).re -
      normalH E ^ 2 / (2 * W * g ^ 2) =
      (((incMean g E X : ℝ) : ℂ) - ((normalH E ^ 2 / (2 * W * g ^ 2) : ℝ) : ℂ) -
        ∑ r ∈ Ks, q r * (PF r - F r)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    ring
  rw [hre, hz]
  refine (Complex.abs_re_le_norm _).trans ?_
  have h1 : ‖∑ k ∈ S, (D k - Aq k) * F k‖ ≤ Bs :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k hk => by
      rw [norm_mul]
      calc ‖D k - Aq k‖ * ‖F k‖ ≤ ‖D k - Aq k‖ * 1 :=
            mul_le_mul_of_nonneg_left (hF k hk) (norm_nonneg _)
        _ = ‖D k - Aq k‖ := mul_one _).trans hres)
  have h2 : ‖∑ r ∈ S, q r * T r‖ ≤ Sq * BT := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ r ∈ S, ‖q r * T r‖ ≤ ∑ r ∈ S, ‖q r‖ * BT := Finset.sum_le_sum fun r hr => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hTr r hr) (norm_nonneg _)
      _ = (∑ r ∈ S, ‖q r‖) * BT := by rw [Finset.sum_mul]
      _ ≤ Sq * BT := mul_le_mul_of_nonneg_right hsq hBT
  calc ‖T₀ + ∑ k ∈ S, (D k - Aq k) * F k - ∑ r ∈ S, q r * T r‖
      ≤ ‖T₀ + ∑ k ∈ S, (D k - Aq k) * F k‖ + ‖∑ r ∈ S, q r * T r‖ := norm_sub_le _ _
    _ ≤ (‖T₀‖ + ‖∑ k ∈ S, (D k - Aq k) * F k‖) + ‖∑ r ∈ S, q r * T r‖ :=
        by gcongr; exact norm_add_le _ _
    _ ≤ B₀ + Bs + Sq * BT := add_le_add (add_le_add hT₀ h1) h2

/-! ### The exponent arithmetic -/

/-- `1/4 ≤ h_θ²` on `|E| ≤ 1`, with `h_θ = (2 sin ϑ)⁻¹` of (11.1) [lg:eq:normal]. -/
private lemma cd_normalH_sq {E : ℝ} (hE : |E| ≤ 1) : 1 / 4 ≤ normalH E ^ 2 := by
  unfold normalH freeAngle
  rw [Real.sin_arccos]
  have h1 : (E / 2) ^ 2 ≤ 1 / 4 := by
    have := sq_abs E
    nlinarith [abs_nonneg E]
  have h2 : 0 < √(1 - (E / 2) ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have h3 : √(1 - (E / 2) ^ 2) ≤ 1 :=
    Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg (E / 2)])
  have h4 : (2 * √(1 - (E / 2) ^ 2)) ^ 2 ≤ 4 := by nlinarith
  rw [inv_pow, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) h4

/-- `g ≥ W^ε` gives `g^n ≥ W^{nε}`. -/
private lemma cd_pow_ge {W g ε : ℝ} (hW : 1 ≤ W) (hg : W ^ ε ≤ g) (n : ℕ) :
    W ^ ((n : ℝ) * ε) ≤ g ^ n := by
  have h0 : 0 < W := by linarith
  rw [mul_comm, Real.rpow_mul h0.le, Real.rpow_natCast]
  exact pow_le_pow_left₀ (Real.rpow_nonneg h0.le _) hg n

/-- `W^a / g^{n+2} ≤ W^b / (W g²)` when `a + 1 − nε ≤ b` and `g ≥ W^ε`. -/
private lemma cd_term {W g ε a b : ℝ} (hW : 1 ≤ W) (hg : W ^ ε ≤ g) (n : ℕ)
    (hab : a + 1 - n * ε ≤ b) : W ^ a / g ^ (n + 2) ≤ W ^ b / (W * g ^ 2) := by
  have h0 : 0 < W := by linarith
  have hgpos : 0 < g := lt_of_lt_of_le (Real.rpow_pos_of_pos h0 _) hg
  have hgn := cd_pow_ge hW hg n
  have hpos : 0 < W ^ ((n : ℝ) * ε) := Real.rpow_pos_of_pos h0 _
  have e : W ^ a / g ^ (n + 2) = (W ^ (a + 1) / g ^ n) / (W * g ^ 2) := by
    rw [Real.rpow_add_one h0.ne']
    field_simp
    ring
  rw [e]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc W ^ (a + 1) / g ^ n ≤ W ^ (a + 1) / W ^ ((n : ℝ) * ε) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg h0.le _) hpos hgn
    _ = W ^ (a + 1 - n * ε) := (Real.rpow_sub h0 _ _).symm
    _ ≤ W ^ b := Real.rpow_le_rpow_of_exponent_le hW hab

/-- The sum of the remainder bounds of (11.65) [lg:eq:corrector-remainder-bounds] at `g ≥ W^ε`,
`η < min(ε, 1/4)`, `2εR > 1`, is at most `C W^{-min(1/4, ε)} (W g²)⁻¹`. -/
private lemma cd_arith {ε η : ℝ} (R : ℕ) (hε : 0 < ε) (hη1 : η < ε) (hη2 : η < 1 / 4)
    (hεR : 1 < 2 * ε * R) {W g : ℝ} (hW : 1 ≤ W) (hg : W ^ ε ≤ g) {Kb Ks K' : ℝ}
    (hKb : 0 ≤ Kb) (hKs : 0 ≤ Ks) (hK' : 0 ≤ K') :
    Kb * (W ^ (η - 3 / 2) / g ^ 2 + W ^ (η - 1) / g ^ 4 + 1 / g ^ (2 * R + 6)) +
      Ks / g ^ (2 * R + 6) +
      Ks / g ^ 2 * (K' * (W ^ (η - 1) / g ^ 2 + 1 / (W * g ^ 2) + 1 / g ^ (2 * R + 2))) ≤
    (3 * Kb + Ks + 3 * Ks * K') * (W ^ (-min (1 / 4) ε) / (W * g ^ 2)) := by
  have h0 : 0 < W := by linarith
  have hgpos : 0 < g := lt_of_lt_of_le (Real.rpow_pos_of_pos h0 _) hg
  set ν : ℝ := min (1 / 4) ε with hν
  have hν1 : ν ≤ 1 / 4 := min_le_left _ _
  have hν2 : ν ≤ ε := min_le_right _ _
  set U : ℝ := W ^ (-ν) / (W * g ^ 2) with hU
  have hU0 : 0 ≤ U := by positivity
  have t1 : W ^ (η - 3 / 2) / g ^ 2 ≤ U := by
    have := cd_term (ε := ε) hW hg 0 (a := η - 3 / 2) (b := -ν) (by push_cast; linarith)
    simpa using this
  have t2 : W ^ (η - 1) / g ^ 4 ≤ U := by
    have := cd_term (ε := ε) hW hg 2 (a := η - 1) (b := -ν) (by push_cast; linarith)
    simpa using this
  have t3 : 1 / g ^ (2 * R + 6) ≤ U := by
    have := cd_term (ε := ε) hW hg (2 * R + 4) (a := 0) (b := -ν)
      (by push_cast; nlinarith)
    simpa [Real.rpow_zero] using this
  have t7 : 1 / g ^ (2 * R + 4) ≤ U := by
    have := cd_term (ε := ε) hW hg (2 * R + 2) (a := 0) (b := -ν)
      (by push_cast; nlinarith)
    simpa [Real.rpow_zero] using this
  have t6 : (1 / g ^ 2) * (1 / (W * g ^ 2)) ≤ U := by
    have h2 := cd_pow_ge hW hg 2
    have hp : 0 < W ^ (((2 : ℕ) : ℝ) * ε) := Real.rpow_pos_of_pos h0 _
    have h3 : 1 / g ^ 2 ≤ W ^ (-ν) := by
      calc 1 / g ^ 2 ≤ 1 / W ^ (((2 : ℕ) : ℝ) * ε) :=
            one_div_le_one_div_of_le hp h2
        _ = W ^ (-(((2 : ℕ) : ℝ) * ε)) := by rw [Real.rpow_neg h0.le, one_div]
        _ ≤ W ^ (-ν) := Real.rpow_le_rpow_of_exponent_le hW (by push_cast; linarith)
    calc (1 / g ^ 2) * (1 / (W * g ^ 2)) ≤ W ^ (-ν) * (1 / (W * g ^ 2)) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = U := by rw [hU]; ring
  have e : Ks / g ^ 2 * (K' * (W ^ (η - 1) / g ^ 2 + 1 / (W * g ^ 2) + 1 / g ^ (2 * R + 2))) =
      Ks * K' * (W ^ (η - 1) / g ^ 4 + (1 / g ^ 2) * (1 / (W * g ^ 2)) + 1 / g ^ (2 * R + 4)) := by
    field_simp
    ring
  have e' : Ks / g ^ (2 * R + 6) = Ks * (1 / g ^ (2 * R + 6)) := by ring
  rw [e, e']
  have hKK : 0 ≤ Ks * K' := mul_nonneg hKs hK'
  calc _ ≤ Kb * (U + U + U) + Ks * U + Ks * K' * (U + U + U) := by gcongr
    _ = _ := by ring

/-- The corrected drift (11.70) [lg:eq:smalldefect] on the good set of (11.44)
[lg:eq:burnevent] with exponent `η/2`. -/
theorem corrector_drift {ε : ℝ} (hε : 0 < ε) (R : ℕ) (hεR : 1 < 2 * ε * R) :
    ∃ Ks : Finset NzInt, ∃ q : ℝ → ℝ → NzInt → ℂ, ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ CQ : ℝ, 0 < CQ ∧
      ∀ η : ℝ, 0 < η → η < min ε (1 / 4) → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        ∀ g : ℝ, (W : ℝ) ^ ε ≤ g → ∀ E : ℝ, |E| ≤ E₁ →
          ∑ k ∈ Ks, ‖q g E k‖ ≤ CQ / g ^ 2 ∧
            ∀ X : State W, IsState X → corrGood g E R Ks (η / 2) X →
              |incMean g E X - (transOp g E (corrQ g E R Ks (q g E)) X -
                  corrQ g E R Ks (q g E) X) - normalH E ^ 2 / (2 * W * g ^ 2)| ≤
                normalH E ^ 2 / (6 * W * g ^ 2) := by
  obtain ⟨Ks₁, Es, hEs, Kq, gs, hKq, hgs, q, hq⟩ := corrCoeff_solve R
  obtain ⟨Ks₂, hsub, E₂, hE₂, K₂, g₂, hK₂, hg₂, h₂⟩ := transOp_corrF_lin_sub_le R Ks₁
  obtain ⟨Ks₃, E₃, hE₃, K₃, g₃, hK₃, hg₃, h₃⟩ := incMean_lin_sub_le R
  set Ks : Finset NzInt := Ks₂ ∪ Ks₃ with hKs
  set E₁ : ℝ := min (min Es E₂) (min E₃ 1) with hE₁
  set ν : ℝ := min (1 / 4) ε with hν
  have hν0 : 0 < ν := lt_min (by norm_num) hε
  set Ctot : ℝ := 3 * K₃ + Kq + 3 * Kq * K₂ with hC
  have hev : ∀ᶠ W : ℕ in Filter.atTop, 1 ≤ W ∧ max gs (max g₂ g₃) ≤ (W : ℝ) ^ ε ∧
      Ctot * (W : ℝ) ^ (-ν) ≤ 1 / 24 := by
    have a1 : ∀ᶠ W : ℕ in Filter.atTop, 1 ≤ W := Filter.eventually_ge_atTop 1
    have a2 : ∀ᶠ W : ℕ in Filter.atTop, max gs (max g₂ g₃) ≤ (W : ℝ) ^ ε :=
      ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
    have a3 : ∀ᶠ W : ℕ in Filter.atTop, Ctot * (W : ℝ) ^ (-ν) < 1 / 24 := by
      have h := ((tendsto_rpow_neg_atTop hν0).comp tendsto_natCast_atTop_atTop).const_mul Ctot
      rw [mul_zero] at h
      exact h.eventually_lt_const (by norm_num)
    filter_upwards [a1, a2, a3] with W h1 h2 h3 using ⟨h1, h2, h3.le⟩
  obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨Ks, q, E₁, lt_min (lt_min hEs hE₂) (lt_min hE₃ one_pos), Kq, hKq,
    fun η hη0 hη => ⟨W₀, fun W hW g hg E hE => ?_⟩⟩
  obtain ⟨hW1, hgg, hCt⟩ := hW₀ W hW
  have hη1 : η < ε := lt_of_lt_of_le hη (min_le_left _ _)
  have hη2 : η < 1 / 4 := lt_of_lt_of_le hη (min_le_right _ _)
  have hgs' : gs ≤ g := (le_max_left _ _).trans (hgg.trans hg)
  have hg2' : g₂ ≤ g := ((le_max_left _ _).trans (le_max_right _ _)).trans (hgg.trans hg)
  have hg3' : g₃ ≤ g := ((le_max_right _ _).trans (le_max_right _ _)).trans (hgg.trans hg)
  have hEs' : |E| ≤ Es := hE.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hE2' : |E| ≤ E₂ := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hE3' : |E| ≤ E₃ := hE.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hE1' : |E| ≤ 1 := hE.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hg1 : 1 ≤ g := hgs.trans hgs'
  have hg0 : 0 < g := by linarith
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWg : (W : ℝ) ^ ε ≤ g := hg
  have hKs₁ : Ks₁ ⊆ Ks := hsub.trans Finset.subset_union_left
  obtain ⟨hq0, hqs, hdrift, hres⟩ := hq g hgs' E hEs'
  refine ⟨?_, fun X hX hgood => ?_⟩
  · rw [← Finset.sum_subset hKs₁ fun k _ hk => by rw [hq0 k hk, norm_zero]]
    exact hqs
  · have hη'0 : 0 ≤ η / 2 := by linarith
    have hη'1 : η / 2 ≤ 1 / 2 := by linarith
    have hT₀ := h₃ Ks Finset.subset_union_right W hW1 g hg3' E hE3' (η / 2) hη'0 hη'1 X hX hgood
    have hTr := h₂ Ks Finset.subset_union_left W hW1 g hg2' E hE2' (η / 2) hη'0 hη'1 X hX hgood
    have hF : ∀ k ∈ Ks₁, ‖obsEval g X (corrObsF E R k)‖ ≤ 1 := fun k hk =>
      (hgood k (hKs₁ hk)).2.trans (Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith))
    have core := cd_core g E hW1 hg1 hX R Ks Ks₁ hKs₁ (q g E) hq0 hdrift
      (hBT := by positivity) hF hT₀ hTr hres hqs
    refine core.trans ?_
    have e2 : 2 * (η / 2) = η := by ring
    simp only [e2]
    have key := cd_arith (ε := ε) (η := η) R hε hη1 hη2 hεR hWr hWg hK₃.le hKq.le hK₂.le
    refine key.trans ?_
    have hwg : 0 < (W : ℝ) * g ^ 2 := by positivity
    have hh := cd_normalH_sq hE1'
    calc Ctot * ((W : ℝ) ^ (-ν) / (W * g ^ 2))
        = (Ctot * (W : ℝ) ^ (-ν)) * (1 / (W * g ^ 2)) := by ring
      _ ≤ (1 / 24) * (1 / (W * g ^ 2)) :=
          mul_le_mul_of_nonneg_right hCt (by positivity)
      _ ≤ (normalH E ^ 2 / 6) * (1 / (W * g ^ 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = normalH E ^ 2 / (6 * W * g ^ 2) := by field_simp

end LSBA
