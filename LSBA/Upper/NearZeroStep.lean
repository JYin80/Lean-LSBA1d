import LSBA.Upper.CorrectorQ
import LSBA.Upper.CenterInnovation
import LSBA.Upper.LargeGradient
import LSBA.Upper.LargeIncrement
import LSBA.Analysis.ExpMoment

/-!
# One-step exponential moments near zero energy

The one-step bounds behind Lemma 11.10 [lg:lem:scalar-growth] (Section 11.3
[lg:sec:drift-to-growth]), in exponential-moment form: for `0 ≤ s ≤ 1`,
`𝔼 e^{−s c} ≤ exp(K g⁻²)` at every state (from (11.31) [lg:eq:coarse-drift] and the global bound
(11.13) [uvg:eq:global]); and, for the corrected increment `Y = c − Q_g(X') + Q_g(X)` with
`Q_g = Re Σ_k q_k F_k`, `Σ |q_k| ≤ C_Q g⁻²`, at a state where the corrected drift is at least
`(12 W g²)⁻¹`, `𝔼 e^{−s Y} ≤ exp(−s (48 W g²)⁻¹)` for one fixed `s > 0` and `g ≥ W^ε`, `W` large.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Measurability of the block, the increment and the observables -/

private lemma nzs_measurable_gb (W : ℕ) : Measurable fun ω : Ω W 1 => gueBlock W 1 ω 0 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma nzs_measurable_next (g E : ℝ) {W : ℕ} (X : State W) :
    Measurable fun ω : Ω W 1 => stepState g E X (gueBlock W 1 ω 0) := by
  have hS : Measurable fun V : Matrix (Fin W) (Fin W) ℂ => (X, V) :=
    Measurable.prodMk measurable_const measurable_id
  exact ((measurable_stepState g E W).comp hS).comp (nzs_measurable_gb W)

private lemma nzs_measurable_inc (g E : ℝ) {W : ℕ} (X : State W) :
    Measurable fun ω : Ω W 1 => stepInc g E X (gueBlock W 1 ω 0) := by
  have hS : Measurable fun V : Matrix (Fin W) (Fin W) ℂ => (X, V) :=
    Measurable.prodMk measurable_const measurable_id
  exact ((measurable_stepInc g E W).comp hS).comp (nzs_measurable_gb W)

private lemma nzs_cont_vecForm {W : ℕ} :
    Continuous fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) => vecForm q.1 q.2 := by
  have hc : Continuous (fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) =>
      Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) q.1 q.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM
  exact continuous_snd.inner hc

private lemma nzs_measurable_inv {W : ℕ} :
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

private lemma nzs_measurable_zpow {W : ℕ} (k : ℤ) :
    Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A ^ k := by
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact (continuous_id.pow n).measurable
  | negSucc n =>
    simp only [zpow_negSucc]
    exact nzs_measurable_inv.comp (continuous_id.pow _).measurable

private lemma nzs_measurable_obsEval (g : ℝ) (W : ℕ) (p : ObsPoly) :
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
        ((nzs_measurable_zpow k.1).comp measurable_fst))
    | f k =>
      simp only [obsEval, aeval_X, obsF]
      have h1 : Measurable fun X : State W => (X.1 ^ k.1, X.2) :=
        ((nzs_measurable_zpow k.1).comp measurable_fst).prodMk measurable_snd
      have h2 := (nzs_cont_vecForm (W := W)).measurable.comp h1
      exact h2
    | w => simp only [obsEval, aeval_X]; exact measurable_const
    | γ => simp only [obsEval, aeval_X]; exact measurable_const

private lemma nzs_measurable_corrQ (g E : ℝ) (R : ℕ) (Ks : Finset NzInt) (q : NzInt → ℂ)
    (W : ℕ) : Measurable fun X : State W => corrQ g E R Ks q X := by
  unfold corrQ
  exact Complex.measurable_re.comp (Finset.measurable_sum _ fun k _ =>
    measurable_const.mul (nzs_measurable_obsEval g W _))

private lemma nzs_integrable_obs (g E : ℝ) {W : ℕ} (hW : 1 ≤ W) (hg : 1 ≤ g) {X : State W}
    (hX : IsState X) (p : ObsPoly) :
    Integrable (fun ω : Ω W 1 => obsEval g (stepState g E X (gueBlock W 1 ω 0)) p) (μ W 1) :=
  Integrable.of_bound ((nzs_measurable_obsEval g W p).comp
    (nzs_measurable_next g E X)).aestronglyMeasurable (∑ d ∈ p.support, ‖p.coeff d‖)
    (Filter.Eventually.of_forall fun ω =>
      norm_obsEval_le hW hg (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)) p)

/-- `P_g Q_g = Re Σ q_k P_g F_k`. -/
private lemma nzs_transOp_corrQ (g E : ℝ) {W : ℕ} (hW : 1 ≤ W) (hg : 1 ≤ g) {X : State W}
    (hX : IsState X) (R : ℕ) (Ks : Finset NzInt) (q : NzInt → ℂ) :
    transOp g E (corrQ g E R Ks q) X =
      (∑ r ∈ Ks, q r * transOp g E (fun Y => obsEval g Y (corrObsF E R r)) X).re := by
  have hint : ∀ r ∈ Ks, Integrable (fun ω : Ω W 1 =>
      q r * obsEval g (stepState g E X (gueBlock W 1 ω 0)) (corrObsF E R r)) (μ W 1) :=
    fun r _ => (nzs_integrable_obs g E hW hg hX _).const_mul _
  unfold transOp corrQ
  have h2 := integral_re (μ := μ W 1) (𝕜 := ℂ) (f := fun ω : Ω W 1 => ∑ r ∈ Ks,
    q r * obsEval g (stepState g E X (gueBlock W 1 ω 0)) (corrObsF E R r))
    (integrable_finsetSum _ hint)
  simp only [RCLike.re_to_complex] at h2
  rw [h2, integral_finsetSum _ hint]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  exact integral_const_mul _ _

/-! ### Elementary bounds -/

private lemma nzs_normalH_nonneg (E : ℝ) : 0 ≤ normalH E := by
  unfold normalH freeAngle
  rw [Real.sin_arccos]
  positivity

/-- `h_θ ≤ 1` for `|E| ≤ 1`, with `h_θ` of (11.1) [lg:eq:normal]. -/
private lemma nzs_normalH_le {E : ℝ} (hE : |E| ≤ 1) : normalH E ≤ 1 := by
  unfold normalH freeAngle
  rw [Real.sin_arccos]
  have h1 : (E / 2) ^ 2 ≤ 1 / 4 := by
    rw [div_pow]
    nlinarith [sq_abs E, abs_nonneg E]
  have h2 : 1 / 2 ≤ √(1 - (E / 2) ^ 2) := by
    rw [show (1 : ℝ) / 2 = √((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [inv_le_one₀ (by linarith)]
  linarith

/-- (11.13) [uvg:eq:global] on `|E| ≤ 1`: `|c| ≤ log(1 + 2 ‖V‖ / g)`. -/
private lemma nzs_abs_inc_le {g : ℝ} (hg : 1 ≤ g) {E : ℝ} (hE : |E| ≤ 1) {W : ℕ} {X : State W}
    (hX : IsState X) {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    |stepInc g E X V| ≤ Real.log (1 + 2 * ‖V‖ / g) := by
  have hg0 : 0 < g := by linarith
  refine (abs_stepInc_le hg0 E hX hV).trans ?_
  have hh := nzs_normalH_le hE
  have hh0 := nzs_normalH_nonneg E
  have h1 : 0 < 1 + 2 * normalH E * ‖V‖ / g := by positivity
  refine Real.log_le_log h1 ?_
  have : 2 * normalH E * ‖V‖ / g ≤ 2 * ‖V‖ / g := by
    gcongr
    nlinarith [norm_nonneg V]
  linarith

/-- `|c| ≤ log(1 + t)` gives `|c| ≤ t` and `e^{|c|} ≤ 1 + t`. -/
private lemma nzs_log_bounds {t c : ℝ} (ht : 0 ≤ t) (hc : |c| ≤ Real.log (1 + t)) :
    |c| ≤ t ∧ Real.exp |c| ≤ 1 + t := by
  have h1 : 0 < 1 + t := by linarith
  refine ⟨hc.trans ?_, ?_⟩
  · have := Real.log_le_sub_one_of_pos h1
    linarith
  · calc Real.exp |c| ≤ Real.exp (Real.log (1 + t)) := Real.exp_le_exp.mpr hc
      _ = 1 + t := Real.exp_log h1

/-- On `|c| > 1/2` with `|c| ≤ log(1 + t)`: `2 (1 + t) ≤ 3 (2t)^p` for `p ≥ 1`. -/
private lemma nzs_tail_le {t c : ℝ} (ht : 0 ≤ t) (hc : |c| ≤ Real.log (1 + t))
    (h : 1 / 2 < |c|) {p : ℕ} (hp : 1 ≤ p) : 2 * (1 + t) ≤ 3 * (2 * t) ^ p := by
  have h1 : 0 < 1 + t := by linarith
  have h2 : Real.exp (1 / 2) < 1 + t := by
    calc Real.exp (1 / 2) < Real.exp |c| := Real.exp_lt_exp.mpr h
      _ ≤ 1 + t := (nzs_log_bounds ht hc).2
  have h3 := Real.add_one_le_exp (1 / 2 : ℝ)
  have h4 : 1 ≤ 2 * t := by linarith
  have h5 : 2 * t ≤ (2 * t) ^ p := le_self_pow₀ h4 (by omega)
  linarith

/-- `𝔼 ‖V‖^p ≤ C_p` as a Bochner integral. -/
private lemma nzs_integral_pow_le (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ, ∫ ω, ‖gueBlock W 1 ω 0‖ ^ p ∂(μ W 1) ≤ C := by
  obtain ⟨C, hC, h⟩ := lintegral_norm_gueBlock_pow_le p
  refine ⟨C, hC, fun W => ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => by positivity)
    (integrable_norm_gueBlock_pow W p).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hC.le ?_
  refine le_trans (le_of_eq ?_) (h W)
  refine lintegral_congr fun ω => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- `|P_g c| ≤ K g⁻²` on `|E| ≤ 1`, from (11.12) [lg:eq:c2]. -/
private lemma nzs_incMean_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ 1 →
      ∀ X : State W, IsState X → |incMean g E X| ≤ K / g ^ 2 := by
  obtain ⟨Ke, hKe, hexp⟩ := incMean_expansion (E₀ := 1) (by norm_num)
  refine ⟨3 + Ke, by positivity, fun W hW g hg E hE X hX => ?_⟩
  have h := hexp W hW g hg E hE X hX
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg
  have hg4 : g ^ 2 ≤ g ^ 4 := pow_le_pow_right₀ hg (by norm_num)
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hw0 : 0 ≤ 1 / (2 * (W : ℝ)) := by positivity
  have hw1 : 1 / (2 * (W : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hF := norm_obsF_le_one 1 hX
  have hM := norm_obsM_le_one 1 hX
  have hr1 : |(obsF 1 X).re| ≤ 1 := (Complex.abs_re_le_norm _).trans hF
  have hr2 : |(obsM 1 X * obsF 1 X).re| ≤ 1 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    nlinarith [norm_nonneg (obsM 1 X), norm_nonneg (obsF 1 X)]
  have hr3 : |(obsF 1 X ^ 2).re| ≤ 1 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_pow]
    nlinarith [norm_nonneg (obsF 1 X)]
  set B : ℝ := 1 / (2 * (W : ℝ)) + (obsF 1 X).re + (obsM 1 X * obsF 1 X).re -
    1 / (2 * (W : ℝ)) * (obsF 1 X ^ 2).re with hB
  have hBb : |B| ≤ 3 := by
    have h3 : |1 / (2 * (W : ℝ)) * (obsF 1 X ^ 2).re| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_nonneg hw0]
      nlinarith [abs_nonneg (obsF 1 X ^ 2).re]
    rw [hB]
    calc |1 / (2 * (W : ℝ)) + (obsF 1 X).re + (obsM 1 X * obsF 1 X).re -
          1 / (2 * (W : ℝ)) * (obsF 1 X ^ 2).re|
        ≤ |1 / (2 * (W : ℝ))| + |(obsF 1 X).re| + |(obsM 1 X * obsF 1 X).re| +
          |1 / (2 * (W : ℝ)) * (obsF 1 X ^ 2).re| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ 1 / 2 + 1 + 1 + 1 / 2 := by
          rw [abs_of_nonneg hw0]
          gcongr
      _ = 3 := by norm_num
  have hh := nzs_normalH_le hE
  have hh0 := nzs_normalH_nonneg E
  have hh2 : normalH E ^ 2 ≤ 1 := by nlinarith
  have hA : |normalH E ^ 2 / g ^ 2 * B| ≤ 3 / g ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc normalH E ^ 2 / g ^ 2 * |B| ≤ 1 / g ^ 2 * 3 := by
          gcongr
      _ = 3 / g ^ 2 := by ring
  have hK4 : Ke / g ^ 4 ≤ Ke / g ^ 2 := div_le_div_of_nonneg_left hKe.le (by positivity) hg4
  calc |incMean g E X| ≤ |incMean g E X - normalH E ^ 2 / g ^ 2 * B| +
        |normalH E ^ 2 / g ^ 2 * B| := by
        have := abs_add_le (incMean g E X - normalH E ^ 2 / g ^ 2 * B)
          (normalH E ^ 2 / g ^ 2 * B)
        simpa using this
    _ ≤ Ke / g ^ 2 + 3 / g ^ 2 := add_le_add (h.trans hK4) hA
    _ = (3 + Ke) / g ^ 2 := by ring

/-- `𝔼 e^{−Y} ≤ 1 − 𝔼Y + 𝔼Y² + 𝔼T` when `e^{−Y} ≤ T` on `{Y < −1}`. -/
private lemma nzs_mgf_le {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'}
    [IsProbabilityMeasure P] {Y T : Ω' → ℝ} (hYm : Measurable Y) (hY : Integrable Y P)
    (hY2 : Integrable (fun ω => Y ω ^ 2) P) (hT : Integrable T P) (hT0 : ∀ ω, 0 ≤ T ω)
    (htail : ∀ ω, Y ω < -1 → Real.exp (-Y ω) ≤ T ω) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-Y ω)) ∂P ≤
      ENNReal.ofReal (1 - ∫ ω, Y ω ∂P + ∫ ω, Y ω ^ 2 ∂P + ∫ ω, T ω ∂P) := by
  have h := lintegral_exp_neg_le hY hY2
  have ha : 0 ≤ 1 - ∫ ω, Y ω ∂P + ∫ ω, Y ω ^ 2 ∂P := by
    have h1 : ∫ ω, (1 - Y ω + Y ω ^ 2) ∂P = 1 - ∫ ω, Y ω ∂P + ∫ ω, Y ω ^ 2 ∂P := by
      have e1 := integral_add ((integrable_const (1 : ℝ)).sub hY) hY2
      have e2 := integral_sub (integrable_const (1 : ℝ)) hY
      simp only [Pi.sub_apply] at e1
      rw [e1, e2]
      simp
    rw [← h1]
    exact integral_nonneg fun ω => by
      change (0 : ℝ) ≤ 1 - Y ω + Y ω ^ 2
      nlinarith [sq_nonneg (Y ω - 1 / 2)]
  have hS : MeasurableSet {ω | Y ω < -1} := measurableSet_lt hYm measurable_const
  have htl : ∫⁻ ω in {ω | Y ω < -1}, ENNReal.ofReal (Real.exp (-Y ω)) ∂P ≤
      ENNReal.ofReal (∫ ω, T ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hT (Filter.Eventually.of_forall hT0)]
    calc _ ≤ ∫⁻ ω in {ω | Y ω < -1}, ENNReal.ofReal (T ω) ∂P :=
          setLIntegral_mono' hS fun ω hω => ENNReal.ofReal_le_ofReal (htail ω hω)
      _ ≤ _ := setLIntegral_le_lintegral _ _
  calc _ ≤ _ := h
    _ ≤ ENNReal.ofReal (1 - ∫ ω, Y ω ∂P + ∫ ω, Y ω ^ 2 ∂P) + ENNReal.ofReal (∫ ω, T ω ∂P) :=
        add_le_add le_rfl htl
    _ = _ := (ENNReal.ofReal_add ha (integral_nonneg hT0)).symm

/-- `(A − B + m)² ≤ 4A² + 4X + 2m²` when `B² ≤ X`. -/
private lemma nzs_sq_le {A B m X : ℝ} (h : B ^ 2 ≤ X) :
    (A - B + m) ^ 2 ≤ 4 * A ^ 2 + 4 * X + 2 * m ^ 2 := by
  nlinarith [sq_nonneg (A - B - m), sq_nonneg (A + B)]

private lemma nzs_alg (Kv KF n CQ P m : ℝ) :
    4 * (Kv / P) + 4 * (n * CQ ^ 2) * (n * (KF / P)) + 2 * m ^ 2 =
      (4 * Kv + 4 * n ^ 2 * CQ ^ 2 * KF) / P + 2 * m ^ 2 := by
  ring

/-- `e^{1/2} ≤ 2`. -/
private lemma nzs_exp_half_le : Real.exp (1 / 2) ≤ 2 := by
  have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_pos (1 / 2)
  nlinarith

/-- `g ≥ W^ε` with `W ≥ 1` gives `W² ≤ g^{⌈2/ε⌉}`. -/
private lemma nzs_pow_ge {W g ε : ℝ} (hε : 0 < ε) (hW : 1 ≤ W) (hg : W ^ ε ≤ g) :
    W ^ 2 ≤ g ^ ⌈2 / ε⌉₊ := by
  have h0 : 0 < W := by linarith
  have h1 : (W ^ ε) ^ ⌈2 / ε⌉₊ ≤ g ^ ⌈2 / ε⌉₊ :=
    pow_le_pow_left₀ (Real.rpow_nonneg h0.le _) hg _
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le] at h1
  have h2 : (2 : ℝ) ≤ ε * (⌈2 / ε⌉₊ : ℝ) := by
    have := Nat.le_ceil (2 / ε)
    rw [div_le_iff₀ hε] at this
    linarith
  calc W ^ 2 = W ^ (2 : ℝ) := by norm_cast
    _ ≤ W ^ (ε * (⌈2 / ε⌉₊ : ℝ)) := Real.rpow_le_rpow_of_exponent_le hW h2
    _ ≤ _ := h1

/-- The closing arithmetic of the corrected bound: with `P = W g²`, drift `m ≥ (12P)⁻¹`,
`m ≤ M`, `4sM ≤ 1`, `96 s V₀ ≤ 1`, second moment `≤ V₀/P + 2m²` and tail `≤ s/(96P)`. -/
private lemma nzs_final {s m P V₀ M I2 IT : ℝ} (hs0 : 0 < s) (hP : 0 < P)
    (hm : 1 / (12 * P) ≤ m) (hmM : m ≤ M) (hsM : s * (4 * M) ≤ 1) (hsV : s * (96 * V₀) ≤ 1)
    (hI2 : I2 ≤ V₀ / P + 2 * m ^ 2) (hIT : IT ≤ s / (96 * P)) :
    1 - s * m + s ^ 2 * I2 + IT ≤ Real.exp (-(s / (48 * P))) := by
  set a : ℝ := 1 / P with ha
  have ha0 : 0 < a := by positivity
  have e1 : 1 / (12 * P) = a / 12 := by rw [ha]; field_simp
  have e2 : V₀ / P = V₀ * a := by rw [ha]; field_simp
  have e3 : s / (96 * P) = s * a / 96 := by rw [ha]; field_simp
  have e4 : s / (48 * P) = s * a / 48 := by rw [ha]; field_simp
  rw [e1] at hm
  rw [e2] at hI2
  rw [e3] at hIT
  rw [e4]
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have h4 : 4 * s * m ≤ 1 := by nlinarith
  have hA : s ^ 2 * I2 ≤ s ^ 2 * (V₀ * a) + 2 * s ^ 2 * m ^ 2 := by
    have := mul_le_mul_of_nonneg_left hI2 (sq_nonneg s)
    linarith
  have hB : 2 * s ^ 2 * m ^ 2 ≤ s * m / 2 := by
    have : 0 ≤ s * m := by positivity
    nlinarith
  have hC : s ^ 2 * (V₀ * a) ≤ s * a / 96 := by
    have : s * (s * V₀) ≤ s * (1 / 96) := mul_le_mul_of_nonneg_left (by linarith) hs0.le
    nlinarith
  have hD : s * a / 24 ≤ s * m / 2 := by nlinarith
  have := Real.add_one_le_exp (-(s * a / 48))
  linarith

/-- The tail integral `3 (4/g)^p 𝔼‖V‖^p ≤ s/(96 W g²)` with `p = ⌈2/ε⌉ + 2`, once
`W ≥ 96 · 3 · 4^p C_p / s` and `g ≥ W^ε`. -/
private lemma nzs_tail_int {ε s Cp W g I : ℝ} (hε : 0 < ε) (hs0 : 0 < s) (hW : 1 ≤ W)
    (hLW : 96 * (3 * 4 ^ (⌈2 / ε⌉₊ + 2) * Cp) / s ≤ W) (hg : 1 ≤ g) (hgW : W ^ ε ≤ g)
    (hI : I ≤ Cp) :
    3 * (4 / g) ^ (⌈2 / ε⌉₊ + 2) * I ≤ s / (96 * (W * g ^ 2)) := by
  have hg0 : 0 < g := by linarith
  have hW0 : 0 < W := by linarith
  set p : ℕ := ⌈2 / ε⌉₊ + 2 with hp
  have h1 : 3 * (4 / g) ^ p * I ≤ 3 * (4 / g) ^ p * Cp := by gcongr
  refine h1.trans ?_
  have h2 : W ^ 2 ≤ g ^ ⌈2 / ε⌉₊ := nzs_pow_ge hε hW hgW
  have h3 : 96 * (3 * 4 ^ p * Cp) ≤ s * W := by
    have := mul_le_mul_of_nonneg_left hLW hs0.le
    rw [mul_div_cancel₀ _ hs0.ne'] at this
    exact this
  have hgp : g ^ p = g ^ ⌈2 / ε⌉₊ * g ^ 2 := by rw [hp, pow_add]
  have hgp0 : 0 < g ^ p := by positivity
  rw [div_pow, le_div_iff₀ (by positivity)]
  calc 3 * (4 ^ p / g ^ p) * Cp * (96 * (W * g ^ 2))
      = 96 * (3 * 4 ^ p * Cp) * W * g ^ 2 / g ^ p := by field_simp
    _ ≤ s * W * W * g ^ 2 / g ^ p := by gcongr
    _ = s * W ^ 2 * g ^ 2 / g ^ p := by ring
    _ ≤ s * g ^ ⌈2 / ε⌉₊ * g ^ 2 / g ^ p := by gcongr
    _ = s := by rw [hgp]; field_simp

/-- The pointwise tail of the corrected increment: if `s (c − Q₁ + Q₀) < −1` with
`|Q₀|, |Q₁| ≤ K`, `4 s K ≤ 1`, `s ≤ 1` and `|c| ≤ log(1 + t)`, then
`e^{−s(c − Q₁ + Q₀)} ≤ 3 (2t)^p`. -/
private lemma nzs_corr_tail_pt {s c Q1 Q0 t K : ℝ} {p : ℕ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (ht : 0 ≤ t) (hc : |c| ≤ Real.log (1 + t)) (hQ1 : |Q1| ≤ K) (hQ0 : |Q0| ≤ K)
    (hsK : s * (4 * K) ≤ 1) (hp : 1 ≤ p) (h : s * (c - Q1 + Q0) < -1) :
    Real.exp (-(s * (c - Q1 + Q0))) ≤ 3 * (2 * t) ^ p := by
  have hQQ : Q1 - Q0 ≤ 2 * K := by
    linarith [le_abs_self Q1, neg_abs_le Q0]
  have hsq : s * (Q1 - Q0) ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hQQ hs0.le
    linarith
  have hsc : s * (-c) ≤ s * |c| := mul_le_mul_of_nonneg_left (neg_le_abs _) hs0.le
  have hcs : s * |c| ≤ |c| := by nlinarith [abs_nonneg c]
  have hneg : -(s * (c - Q1 + Q0)) = s * (-c) + s * (Q1 - Q0) := by ring
  have hc1 : 1 / 2 < |c| := by linarith
  calc Real.exp (-(s * (c - Q1 + Q0))) ≤ Real.exp (|c| + 1 / 2) := by
        refine Real.exp_le_exp.mpr ?_
        linarith
    _ = Real.exp |c| * Real.exp (1 / 2) := Real.exp_add _ _
    _ ≤ (1 + t) * 2 :=
        mul_le_mul (nzs_log_bounds ht hc).2 nzs_exp_half_le (Real.exp_pos _).le (by linarith)
    _ = 2 * (1 + t) := by ring
    _ ≤ _ := nzs_tail_le ht hc hc1 hp

/-- `𝔼 e^{−s c} ≤ exp(K g⁻²)` for `0 ≤ s ≤ 1`, uniformly in `W ≥ 1`, `g ≥ 1`, `|E| ≤ 1` and the
state. -/
theorem incStep_mgf_le :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ 1 →
      ∀ X : State W, IsState X → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * stepInc g E X (gueBlock W 1 ω 0)))) ∂(μ W 1) ≤
          ENNReal.ofReal (Real.exp (K / g ^ 2)) := by
  obtain ⟨Ki, hKi, hinc⟩ := nzs_incMean_bound
  obtain ⟨C2, hC2, hm2⟩ := nzs_integral_pow_le 2
  refine ⟨Ki + 52 * C2, by positivity, fun W hW g hg E hE X hX s hs0 hs1 => ?_⟩
  have hg0 : 0 < g := by linarith
  set c : Ω W 1 → ℝ := fun ω => stepInc g E X (gueBlock W 1 ω 0) with hc
  set u : Ω W 1 → ℝ := fun ω => ‖gueBlock W 1 ω 0‖ with hu
  have hcm : Measurable c := nzs_measurable_inc g E X
  have hu0 : ∀ ω, 0 ≤ u ω := fun ω => norm_nonneg _
  have hx0 : ∀ ω, 0 ≤ 2 * u ω / g := fun ω => by have := hu0 ω; positivity
  have hcb : ∀ ω, |c ω| ≤ Real.log (1 + 2 * u ω / g) := fun ω =>
    nzs_abs_inc_le hg hE hX (gueBlock_isHermitian W 1 ω 0)
  have hcx : ∀ ω, |c ω| ≤ 2 * u ω / g := fun ω => (nzs_log_bounds (hx0 ω) (hcb ω)).1
  have hu1 : Integrable u (μ W 1) := by simpa using integrable_norm_gueBlock_pow W 1
  have hu2 : Integrable (fun ω => u ω ^ 2) (μ W 1) := integrable_norm_gueBlock_pow W 2
  have hcsq : ∀ ω, c ω ^ 2 ≤ 4 / g ^ 2 * u ω ^ 2 := by
    intro ω
    have := sq_le_sq' (abs_le.mp (hcx ω)).1 (abs_le.mp (hcx ω)).2
    calc c ω ^ 2 ≤ (2 * u ω / g) ^ 2 := this
      _ = 4 / g ^ 2 * u ω ^ 2 := by ring
  have hcI : Integrable c (μ W 1) :=
    Integrable.mono' (hu1.const_mul (2 / g)) hcm.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        calc |c ω| ≤ 2 * u ω / g := hcx ω
          _ = 2 / g * u ω := by ring)
  have hc2I : Integrable (fun ω => c ω ^ 2) (μ W 1) :=
    Integrable.mono' (hu2.const_mul (4 / g ^ 2)) (hcm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hcsq ω)
  have hY2 : (fun ω => (s * c ω) ^ 2) = fun ω => s ^ 2 * c ω ^ 2 := by
    funext ω; ring
  have hT : (fun ω => 3 * (2 * (2 * u ω / g)) ^ 2) = fun ω => 48 / g ^ 2 * u ω ^ 2 := by
    funext ω; ring
  have hmain := nzs_mgf_le (P := μ W 1) (Y := fun ω => s * c ω)
    (T := fun ω => 3 * (2 * (2 * u ω / g)) ^ 2) (measurable_const.mul hcm) (hcI.const_mul s)
    (by rw [hY2]; exact hc2I.const_mul _) (by rw [hT]; exact hu2.const_mul _)
    (fun ω => by positivity) (fun ω hω => ?_)
  · refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    have e1 : ∫ ω, s * c ω ∂(μ W 1) = s * incMean g E X := by
      rw [integral_const_mul]; rfl
    have e2 : ∫ ω, (s * c ω) ^ 2 ∂(μ W 1) = s ^ 2 * ∫ ω, c ω ^ 2 ∂(μ W 1) := by
      rw [hY2, integral_const_mul]
    have e3 : ∫ ω, 3 * (2 * (2 * u ω / g)) ^ 2 ∂(μ W 1) = 48 / g ^ 2 * ∫ ω, u ω ^ 2 ∂(μ W 1) := by
      rw [hT, integral_const_mul]
    have hM2 : ∫ ω, u ω ^ 2 ∂(μ W 1) ≤ C2 := hm2 W
    have hc2 : ∫ ω, c ω ^ 2 ∂(μ W 1) ≤ 4 / g ^ 2 * C2 := by
      calc ∫ ω, c ω ^ 2 ∂(μ W 1) ≤ ∫ ω, 4 / g ^ 2 * u ω ^ 2 ∂(μ W 1) :=
            integral_mono hc2I (hu2.const_mul _) hcsq
        _ = 4 / g ^ 2 * ∫ ω, u ω ^ 2 ∂(μ W 1) := integral_const_mul _ _
        _ ≤ 4 / g ^ 2 * C2 := by gcongr
    have hc20 : 0 ≤ ∫ ω, c ω ^ 2 ∂(μ W 1) := integral_nonneg fun ω => sq_nonneg _
    have hI := hinc W hW g hg E hE X hX
    have hsI : -(s * incMean g E X) ≤ Ki / g ^ 2 := by
      have h1 : -(s * incMean g E X) ≤ s * |incMean g E X| := by
        rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs _) hs0
      have h2 : s * |incMean g E X| ≤ |incMean g E X| := by
        nlinarith [abs_nonneg (incMean g E X)]
      linarith
    have hs2 : s ^ 2 * ∫ ω, c ω ^ 2 ∂(μ W 1) ≤ 4 / g ^ 2 * C2 := by
      have : s ^ 2 ≤ 1 := by nlinarith
      nlinarith
    rw [e1, e2, e3]
    have hT3 : 48 / g ^ 2 * ∫ ω, u ω ^ 2 ∂(μ W 1) ≤ 48 / g ^ 2 * C2 := by gcongr
    have hsum : 1 - s * incMean g E X + s ^ 2 * ∫ ω, c ω ^ 2 ∂(μ W 1) +
        48 / g ^ 2 * ∫ ω, u ω ^ 2 ∂(μ W 1) ≤ (Ki + 52 * C2) / g ^ 2 + 1 := by
      have : (Ki + 52 * C2) / g ^ 2 = Ki / g ^ 2 + 4 / g ^ 2 * C2 + 48 / g ^ 2 * C2 := by ring
      linarith
    exact hsum.trans (Real.add_one_le_exp _)
  · have hω' : s * c ω < -1 := hω
    change Real.exp (-(s * c ω)) ≤ 3 * (2 * (2 * u ω / g)) ^ 2
    have hc1 : 1 / 2 < |c ω| := by
      by_contra hcon
      rw [not_lt] at hcon
      have h1 : -(1 / 2) ≤ c ω := by linarith [neg_abs_le (c ω)]
      nlinarith [mul_nonneg hs0 (by linarith : 0 ≤ c ω + 1 / 2)]
    have hle : -(s * c ω) ≤ |c ω| := by
      have h1 : -(s * c ω) ≤ s * |c ω| := by
        rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs _) hs0
      nlinarith [abs_nonneg (c ω)]
    calc Real.exp (-(s * c ω)) ≤ Real.exp |c ω| := Real.exp_le_exp.mpr hle
      _ ≤ 1 + 2 * u ω / g := (nzs_log_bounds (hx0 ω) (hcb ω)).2
      _ ≤ 2 * (1 + 2 * u ω / g) := by linarith [hx0 ω]
      _ ≤ 3 * (2 * (2 * u ω / g)) ^ 2 := nzs_tail_le (hx0 ω) (hcb ω) hc1 (by norm_num)

/-- The increment and its square are integrable on `|E| ≤ 1`, `g ≥ 1`, with
`|c| ≤ log(1 + 2‖V‖/g)` and `c² ≤ 4 g⁻² ‖V‖²`. -/
private lemma nzs_inc_int {W : ℕ} {g : ℝ} (hg : 1 ≤ g) {E : ℝ} (hE1 : |E| ≤ 1) {X : State W}
    (hX : IsState X) :
    Integrable (fun ω => stepInc g E X (gueBlock W 1 ω 0)) (μ W 1) ∧
      Integrable (fun ω => stepInc g E X (gueBlock W 1 ω 0) ^ 2) (μ W 1) := by
  have hg0 : 0 < g := by linarith
  set c : Ω W 1 → ℝ := fun ω => stepInc g E X (gueBlock W 1 ω 0) with hc
  set u : Ω W 1 → ℝ := fun ω => ‖gueBlock W 1 ω 0‖ with hu
  have hcm : Measurable c := nzs_measurable_inc g E X
  have hx0 : ∀ ω, 0 ≤ 2 * u ω / g := fun ω => by
    have : 0 ≤ u ω := norm_nonneg _
    positivity
  have hcx : ∀ ω, |c ω| ≤ 2 * u ω / g := fun ω =>
    (nzs_log_bounds (hx0 ω) (nzs_abs_inc_le hg hE1 hX (gueBlock_isHermitian W 1 ω 0))).1
  have hu1 : Integrable u (μ W 1) := by simpa using integrable_norm_gueBlock_pow W 1
  have hu2 : Integrable (fun ω => u ω ^ 2) (μ W 1) := integrable_norm_gueBlock_pow W 2
  refine ⟨Integrable.mono' (hu1.const_mul (2 / g)) hcm.aestronglyMeasurable
      (ae_of_all _ fun ω => ?_),
    Integrable.mono' (hu2.const_mul (4 / g ^ 2)) (hcm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)⟩
  · rw [Real.norm_eq_abs]
    calc |c ω| ≤ 2 * u ω / g := hcx ω
      _ = 2 / g * u ω := by ring
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := sq_le_sq' (abs_le.mp (hcx ω)).1 (abs_le.mp (hcx ω)).2
    calc c ω ^ 2 ≤ (2 * u ω / g) ^ 2 := this
      _ = 4 / g ^ 2 * u ω ^ 2 := by ring

/-- The innovations `Δ_k = F_k(X') − P_g F_k(X)` of the corrected observables: `|Δ_k|²` is
integrable, and `(Q_g(X') − P_g Q_g(X))² ≤ |Ks| (Σ |q_k|)² Σ_k |Δ_k|²`. -/
private lemma nzs_innov (g E : ℝ) {W : ℕ} (hW1 : 1 ≤ W) (hg : 1 ≤ g) {X : State W}
    (hX : IsState X) (R : ℕ) (Ks : Finset NzInt) (q : NzInt → ℂ) :
    (∀ k ∈ Ks, Integrable (fun ω => ‖obsEval g (stepState g E X (gueBlock W 1 ω 0))
        (corrObsF E R k) - transOp g E (fun Y => obsEval g Y (corrObsF E R k)) X‖ ^ 2)
        (μ W 1)) ∧
      ∀ ω, (corrQ g E R Ks q (stepState g E X (gueBlock W 1 ω 0)) -
          transOp g E (corrQ g E R Ks q) X) ^ 2 ≤
        (Ks.card : ℝ) * (∑ k ∈ Ks, ‖q k‖) ^ 2 *
          ∑ k ∈ Ks, ‖obsEval g (stepState g E X (gueBlock W 1 ω 0)) (corrObsF E R k) -
            transOp g E (fun Y => obsEval g Y (corrObsF E R k)) X‖ ^ 2 := by
  set X' : Ω W 1 → State W := fun ω => stepState g E X (gueBlock W 1 ω 0) with hX'
  have hX's : ∀ ω, IsState (X' ω) := fun ω =>
    isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)
  set F' : NzInt → Ω W 1 → ℂ := fun k ω => obsEval g (X' ω) (corrObsF E R k) with hF'
  set PF : NzInt → ℂ := fun k => transOp g E (fun Y => obsEval g Y (corrObsF E R k)) X
    with hPF
  set Δ : NzInt → Ω W 1 → ℂ := fun k ω => F' k ω - PF k with hΔ
  set δ : ℝ := ∑ k ∈ Ks, ‖q k‖ with hδ
  have hn0 : 0 ≤ (Ks.card : ℝ) := Nat.cast_nonneg _
  refine ⟨fun k _ => ?_, fun ω => ?_⟩
  · set N : ℝ := ∑ d ∈ (corrObsF E R k).support, ‖(corrObsF E R k).coeff d‖ with hN
    have hb : ∀ ω, ‖F' k ω‖ ≤ N := fun ω => norm_obsEval_le hW1 hg (hX's ω) _
    have hPb : ‖PF k‖ ≤ N := by
      have := norm_integral_le_of_norm_le_const (μ := μ W 1) (f := fun ω => F' k ω)
        (C := N) (ae_of_all _ hb)
      have h' : ‖∫ ω, F' k ω ∂(μ W 1)‖ ≤ N := by simpa using this
      exact h'
    have hmeas : Measurable fun ω => ‖Δ k ω‖ ^ 2 :=
      ((((nzs_measurable_obsEval g W (corrObsF E R k)).comp
        (nzs_measurable_next g E X)).sub_const (PF k)).norm).pow_const 2
    refine Integrable.of_bound hmeas.aestronglyMeasurable ((2 * N) ^ 2)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : ‖Δ k ω‖ ≤ 2 * N := (norm_sub_le _ _).trans (by linarith [hb ω])
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  · have hPQ := nzs_transOp_corrQ g E hW1 hg hX R Ks q
    have hQd : corrQ g E R Ks q (X' ω) - transOp g E (corrQ g E R Ks q) X =
        (∑ k ∈ Ks, q k * Δ k ω).re := by
      rw [hPQ]
      simp only [corrQ, hΔ, hF', hPF, mul_sub, Finset.sum_sub_distrib, Complex.sub_re]
    rw [hQd]
    have h1 : |(∑ k ∈ Ks, q k * Δ k ω).re| ≤ ∑ k ∈ Ks, ‖q k‖ * ‖Δ k ω‖ := by
      refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (le_of_eq ?_))
      exact Finset.sum_congr rfl fun k _ => norm_mul _ _
    have h2 : (∑ k ∈ Ks, ‖q k‖ * ‖Δ k ω‖) ^ 2 ≤
        (Ks.card : ℝ) * ∑ k ∈ Ks, (‖q k‖ * ‖Δ k ω‖) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ∑ k ∈ Ks, (‖q k‖ * ‖Δ k ω‖) ^ 2 ≤ δ ^ 2 * ∑ k ∈ Ks, ‖Δ k ω‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hqk : ‖q k‖ ≤ δ := Finset.single_le_sum (fun j _ => norm_nonneg (q j)) hk
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hqk 2)
        (sq_nonneg _)
    have h4 : (∑ k ∈ Ks, q k * Δ k ω).re ^ 2 ≤ (∑ k ∈ Ks, ‖q k‖ * ‖Δ k ω‖) ^ 2 :=
      sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    calc _ ≤ _ := h4
      _ ≤ _ := h2
      _ ≤ (Ks.card : ℝ) * (δ ^ 2 * ∑ k ∈ Ks, ‖Δ k ω‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 hn0
      _ = _ := by ring

/-- The second moment of the corrected increment `Z = c − Q_g(X') + Q_g(X)` with mean
`m = P_g c − (P_g − I) Q_g`: `𝔼 Z² ≤ (4K_v + 4|Ks|² C_Q² K_F)/(W g²) + 2m²`, from the
variance of `c` and the innovations of the corrected observables. -/
private lemma nzs_corr_sq {W : ℕ} (hW1 : 1 ≤ W) {g : ℝ} (hg : 1 ≤ g) {E : ℝ} (hE1 : |E| ≤ 1)
    {X : State W} (hX : IsState X) (R : ℕ) (Ks : Finset NzInt) (q : NzInt → ℂ)
    {Kv KF CQ : ℝ}
    (hvar : ∫ ω, (stepInc g E X (gueBlock W 1 ω 0) - incMean g E X) ^ 2 ∂(μ W 1) ≤
      Kv / (g ^ 2 * W))
    (hmom : ∀ k ∈ Ks, ∫ ω, ‖obsEval g (stepState g E X (gueBlock W 1 ω 0)) (corrObsF E R k) -
        transOp g E (fun Y => obsEval g Y (corrObsF E R k)) X‖ ^ (2 * 1) ∂(μ W 1) ≤
      KF * (1 / (g * Real.sqrt W)) ^ (2 * 1))
    (hq0 : 0 ≤ ∑ k ∈ Ks, ‖q k‖) (hq : ∑ k ∈ Ks, ‖q k‖ ≤ CQ)
    (hZm : Measurable fun ω => stepInc g E X (gueBlock W 1 ω 0) -
      corrQ g E R Ks q (stepState g E X (gueBlock W 1 ω 0)) + corrQ g E R Ks q X) :
    Integrable (fun ω => (stepInc g E X (gueBlock W 1 ω 0) -
      corrQ g E R Ks q (stepState g E X (gueBlock W 1 ω 0)) + corrQ g E R Ks q X) ^ 2)
        (μ W 1) ∧
      ∫ ω, (stepInc g E X (gueBlock W 1 ω 0) -
        corrQ g E R Ks q (stepState g E X (gueBlock W 1 ω 0)) + corrQ g E R Ks q X) ^ 2
          ∂(μ W 1) ≤
        (4 * Kv + 4 * (Ks.card : ℝ) ^ 2 * CQ ^ 2 * KF) / ((W : ℝ) * g ^ 2) +
          2 * (incMean g E X - (transOp g E (corrQ g E R Ks q) X - corrQ g E R Ks q X)) ^ 2 := by
  have hg0 : 0 < g := by linarith
  obtain ⟨hcI, hc2I⟩ := nzs_inc_int (W := W) hg hE1 hX
  obtain ⟨hΔI, hQd2⟩ := nzs_innov g E hW1 hg hX R Ks q
  set c : Ω W 1 → ℝ := fun ω => stepInc g E X (gueBlock W 1 ω 0) with hc
  set Qf : State W → ℝ := corrQ g E R Ks q with hQf
  set X' : Ω W 1 → State W := fun ω => stepState g E X (gueBlock W 1 ω 0) with hX'
  set Δ : NzInt → Ω W 1 → ℂ := fun k ω => obsEval g (X' ω) (corrObsF E R k) -
    transOp g E (fun Y => obsEval g Y (corrObsF E R k)) X with hΔ
  set δ : ℝ := ∑ k ∈ Ks, ‖q k‖ with hδ
  set n : ℝ := (Ks.card : ℝ) with hn
  set a : ℝ := incMean g E X with ha
  set m : ℝ := a - (transOp g E Qf X - Qf X) with hm
  have hcm : Measurable c := nzs_measurable_inc g E X
  have hvI : Integrable (fun ω => (c ω - a) ^ 2) (μ W 1) :=
    Integrable.mono' ((hc2I.const_mul 2).add (integrable_const (2 * a ^ 2)))
      ((hcm.sub_const a).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        change (c ω - a) ^ 2 ≤ 2 * c ω ^ 2 + 2 * a ^ 2
        nlinarith [sq_nonneg (c ω + a)])
  have hZ2 : ∀ ω, (c ω - Qf (X' ω) + Qf X) ^ 2 ≤ 4 * (c ω - a) ^ 2 +
      4 * (n * δ ^ 2) * ∑ k ∈ Ks, ‖Δ k ω‖ ^ 2 + 2 * m ^ 2 := by
    intro ω
    have hZe : c ω - Qf (X' ω) + Qf X = (c ω - a) - (Qf (X' ω) - transOp g E Qf X) + m := by
      rw [hm]; ring
    rw [hZe]
    calc _ ≤ 4 * (c ω - a) ^ 2 + 4 * (n * δ ^ 2 * ∑ k ∈ Ks, ‖Δ k ω‖ ^ 2) + 2 * m ^ 2 :=
          nzs_sq_le (hQd2 ω)
      _ = _ := by ring
  have hS : Integrable (fun ω => ∑ k ∈ Ks, ‖Δ k ω‖ ^ 2) (μ W 1) :=
    integrable_finsetSum _ hΔI
  have hBI : Integrable (fun ω => 4 * (c ω - a) ^ 2 +
      4 * (n * δ ^ 2) * ∑ k ∈ Ks, ‖Δ k ω‖ ^ 2 + 2 * m ^ 2) (μ W 1) :=
    ((hvI.const_mul 4).add (hS.const_mul _)).add (integrable_const _)
  have hZ2I : Integrable (fun ω => (c ω - Qf (X' ω) + Qf X) ^ 2) (μ W 1) :=
    Integrable.mono' hBI (hZm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hZ2 ω)
  refine ⟨hZ2I, ?_⟩
  have hvar' : ∫ ω, (c ω - a) ^ 2 ∂(μ W 1) ≤ Kv / ((W : ℝ) * g ^ 2) := by
    rw [mul_comm ((W : ℝ)) (g ^ 2)]
    exact hvar
  have hmom' : ∀ k ∈ Ks, ∫ ω, ‖Δ k ω‖ ^ 2 ∂(μ W 1) ≤ KF / ((W : ℝ) * g ^ 2) := by
    intro k hk
    have := hmom k hk
    have e : (1 / (g * Real.sqrt W)) ^ (2 * 1) = 1 / ((W : ℝ) * g ^ 2) := by
      rw [mul_one, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    rw [e] at this
    calc ∫ ω, ‖Δ k ω‖ ^ 2 ∂(μ W 1) ≤ KF * (1 / ((W : ℝ) * g ^ 2)) := by
          simpa using this
      _ = KF / ((W : ℝ) * g ^ 2) := by ring
  have e : ∫ ω, (4 * (c ω - a) ^ 2 + 4 * (n * δ ^ 2) * ∑ k ∈ Ks, ‖Δ k ω‖ ^ 2 + 2 * m ^ 2)
      ∂(μ W 1) = 4 * ∫ ω, (c ω - a) ^ 2 ∂(μ W 1) +
        4 * (n * δ ^ 2) * ∑ k ∈ Ks, ∫ ω, ‖Δ k ω‖ ^ 2 ∂(μ W 1) + 2 * m ^ 2 := by
    have h1 : ∫ ω, (4 * (c ω - a) ^ 2 + 4 * (n * δ ^ 2) * ∑ k ∈ Ks, ‖Δ k ω‖ ^ 2 +
        2 * m ^ 2) ∂(μ W 1) = ∫ ω, (4 * (c ω - a) ^ 2 +
          4 * (n * δ ^ 2) * ∑ k ∈ Ks, ‖Δ k ω‖ ^ 2) ∂(μ W 1) + ∫ _ω, 2 * m ^ 2 ∂(μ W 1) :=
      integral_add ((hvI.const_mul 4).add (hS.const_mul _)) (integrable_const _)
    have h2 : ∫ ω, (4 * (c ω - a) ^ 2 + 4 * (n * δ ^ 2) * ∑ k ∈ Ks, ‖Δ k ω‖ ^ 2) ∂(μ W 1) =
        ∫ ω, 4 * (c ω - a) ^ 2 ∂(μ W 1) +
          ∫ ω, 4 * (n * δ ^ 2) * ∑ k ∈ Ks, ‖Δ k ω‖ ^ 2 ∂(μ W 1) :=
      integral_add (hvI.const_mul 4) (hS.const_mul _)
    have h3 : ∫ ω, 4 * (n * δ ^ 2) * ∑ k ∈ Ks, ‖Δ k ω‖ ^ 2 ∂(μ W 1) =
        4 * (n * δ ^ 2) * ∑ k ∈ Ks, ∫ ω, ‖Δ k ω‖ ^ 2 ∂(μ W 1) := by
      rw [integral_const_mul, integral_finsetSum _ hΔI]
    have h4 : ∫ _ω, 2 * m ^ 2 ∂(μ W 1) = 2 * m ^ 2 := by
      rw [integral_const, probReal_univ, one_smul]
    rw [h1, h2, h3, integral_const_mul, h4]
  have hsum : ∑ k ∈ Ks, ∫ ω, ‖Δ k ω‖ ^ 2 ∂(μ W 1) ≤ n * (KF / ((W : ℝ) * g ^ 2)) := by
    calc ∑ k ∈ Ks, ∫ ω, ‖Δ k ω‖ ^ 2 ∂(μ W 1) ≤ ∑ k ∈ Ks, KF / ((W : ℝ) * g ^ 2) :=
          Finset.sum_le_sum hmom'
      _ = n * (KF / ((W : ℝ) * g ^ 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hδ2 : δ ^ 2 ≤ CQ ^ 2 := pow_le_pow_left₀ hq0 hq 2
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hsum0 : 0 ≤ ∑ k ∈ Ks, ∫ ω, ‖Δ k ω‖ ^ 2 ∂(μ W 1) :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun ω => sq_nonneg _
  calc ∫ ω, (c ω - Qf (X' ω) + Qf X) ^ 2 ∂(μ W 1) ≤ _ := integral_mono hZ2I hBI hZ2
    _ = _ := e
    _ ≤ 4 * (Kv / ((W : ℝ) * g ^ 2)) + 4 * (n * CQ ^ 2) * (n * (KF / ((W : ℝ) * g ^ 2))) +
        2 * m ^ 2 := by
      gcongr
    _ = _ := nzs_alg _ _ _ _ _ _

/-- The corrected one-step exponential moment at a state with corrected drift at least
`(12 W g²)⁻¹` (the statement of Section 11.3 [lg:sec:drift-to-growth] in one-step form). -/
private lemma nzs_corrStep {ε : ℝ} (hε : 0 < ε) (R : ℕ) (Ks : Finset NzInt) {CQ : ℝ}
    (hCQ : 0 < CQ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ g : ℝ, (W : ℝ) ^ ε ≤ g → ∀ E : ℝ, |E| ≤ E₁ → ∀ q : NzInt → ℂ,
        ∑ k ∈ Ks, ‖q k‖ ≤ CQ / g ^ 2 → ∀ X : State W, IsState X →
          1 / (12 * W * g ^ 2) ≤
            incMean g E X - (transOp g E (corrQ g E R Ks q) X - corrQ g E R Ks q X) →
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * (stepInc g E X (gueBlock W 1 ω 0) -
              corrQ g E R Ks q (stepState g E X (gueBlock W 1 ω 0)) + corrQ g E R Ks q X))))
              ∂(μ W 1) ≤
            ENNReal.ofReal (Real.exp (-(s / (48 * W * g ^ 2)))) := by
  obtain ⟨Ki, hKi, hinc⟩ := nzs_incMean_bound
  obtain ⟨Kv, hKv, hvar⟩ := innovation_var (E₀ := 1) (by norm_num)
  obtain ⟨EQ, hEQ, KQ, hKQ, hQb⟩ := corrQ_bounds R Ks
  obtain ⟨EF, hEF, KF, hKF, hmom⟩ := innovation_moment_corrObs R Ks 1
  obtain ⟨Cp, hCp, hmp⟩ := nzs_integral_pow_le (⌈2 / ε⌉₊ + 2)
  set p : ℕ := ⌈2 / ε⌉₊ + 2 with hp
  set n : ℝ := (Ks.card : ℝ) with hn
  set M : ℝ := Ki + 2 * KQ * CQ with hM
  set V₀ : ℝ := 4 * Kv + 4 * n ^ 2 * CQ ^ 2 * KF with hV₀
  set D : ℝ := 1 + 4 * M + 96 * V₀ + 4 * KQ * CQ with hD
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hM0 : 0 < M := by positivity
  have hV0 : 0 ≤ V₀ := by positivity
  have hD0 : 0 < D := by positivity
  set s : ℝ := 1 / D with hs
  have hs0 : 0 < s := by positivity
  have hsle : ∀ x : ℝ, x ≤ D → s * x ≤ 1 := fun x hx => by
    rw [hs, one_div_mul_eq_div, div_le_one hD0]; exact hx
  have hKC : 0 < 4 * KQ * CQ := by positivity
  have hs1 : s ≤ 1 := by simpa using hsle 1 (by linarith)
  have hsM : s * (4 * M) ≤ 1 := hsle _ (by linarith)
  have hsV : s * (96 * V₀) ≤ 1 := hsle _ (by linarith)
  have hsQ : s * (4 * (KQ * CQ)) ≤ 1 := hsle _ (by linarith)
  set L : ℝ := 96 * (3 * 4 ^ p * Cp) / s with hL
  refine ⟨s, hs0, hs1, min 1 (min EQ EF), by positivity, ⌈L⌉₊ + 1, ?_⟩
  intro W hW g hgW E hE q hq X hX hdrift
  have hW1 : 1 ≤ W := by omega
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hLW : L ≤ W := (Nat.le_ceil L).trans (by exact_mod_cast (by omega : ⌈L⌉₊ ≤ W))
  have hg : 1 ≤ g := (Real.one_le_rpow hWr hε.le).trans hgW
  have hg0 : 0 < g := by linarith
  have hE1 : |E| ≤ 1 := hE.trans (min_le_left _ _)
  have hEQ' : |E| ≤ EQ := hE.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hEF' : |E| ≤ EF := hE.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hcI, -⟩ := nzs_inc_int (W := W) hg hE1 hX
  set c : Ω W 1 → ℝ := fun ω => stepInc g E X (gueBlock W 1 ω 0) with hc
  set u : Ω W 1 → ℝ := fun ω => ‖gueBlock W 1 ω 0‖ with hu
  set Qf : State W → ℝ := corrQ g E R Ks q with hQf
  set X' : Ω W 1 → State W := fun ω => stepState g E X (gueBlock W 1 ω 0) with hX'
  have hX's : ∀ ω, IsState (X' ω) := fun ω =>
    isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)
  have hcm : Measurable c := nzs_measurable_inc g E X
  have hu0 : ∀ ω, 0 ≤ u ω := fun ω => norm_nonneg _
  have hx0 : ∀ ω, 0 ≤ 2 * u ω / g := fun ω => by have := hu0 ω; positivity
  have hcb : ∀ ω, |c ω| ≤ Real.log (1 + 2 * u ω / g) := fun ω =>
    nzs_abs_inc_le hg hE1 hX (gueBlock_isHermitian W 1 ω 0)
  have hup : Integrable (fun ω => u ω ^ p) (μ W 1) := integrable_norm_gueBlock_pow W p
  -- the corrector
  set δ : ℝ := ∑ k ∈ Ks, ‖q k‖ with hδ
  have hδ0 : 0 ≤ δ := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg
  have hδC : δ ≤ CQ := hq.trans (div_le_self hCQ.le hg2)
  have hQX : |Qf X| ≤ KQ * δ := (hQb W hW1 g hg E hEQ' q X X hX hX).1
  have hQ' : ∀ ω, |Qf (X' ω)| ≤ KQ * δ := fun ω =>
    (hQb W hW1 g hg E hEQ' q (X' ω) (X' ω) (hX's ω) (hX's ω)).1
  have hQm : Measurable fun ω => Qf (X' ω) :=
    (nzs_measurable_corrQ g E R Ks q W).comp (nzs_measurable_next g E X)
  have hQI : Integrable (fun ω => Qf (X' ω)) (μ W 1) :=
    Integrable.of_bound hQm.aestronglyMeasurable (KQ * δ)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hQ' ω)
  have hPQb : |transOp g E Qf X| ≤ KQ * δ := by
    have := norm_integral_le_of_norm_le_const (μ := μ W 1) (f := fun ω => Qf (X' ω))
      (C := KQ * δ) (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hQ' ω)
    change |∫ ω, Qf (X' ω) ∂(μ W 1)| ≤ KQ * δ
    simpa using this
  -- the corrected increment and its mean
  set m : ℝ := incMean g E X - (transOp g E Qf X - Qf X) with hm
  set Z : Ω W 1 → ℝ := fun ω => c ω - Qf (X' ω) + Qf X with hZ
  have hZm : Measurable Z := (hcm.sub hQm).add measurable_const
  have hZI : Integrable Z (μ W 1) := (hcI.sub hQI).add (integrable_const _)
  have hZint : ∫ ω, Z ω ∂(μ W 1) = m := by
    have e1 : incMean g E X = ∫ ω, c ω ∂(μ W 1) := rfl
    have e2 : transOp g E Qf X = ∫ ω, Qf (X' ω) ∂(μ W 1) := rfl
    have h1 : ∫ ω, Z ω ∂(μ W 1) =
        ∫ ω, (c ω - Qf (X' ω)) ∂(μ W 1) + ∫ _ω, Qf X ∂(μ W 1) :=
      integral_add (hcI.sub hQI) (integrable_const _)
    have h2 : ∫ ω, (c ω - Qf (X' ω)) ∂(μ W 1) =
        ∫ ω, c ω ∂(μ W 1) - ∫ ω, Qf (X' ω) ∂(μ W 1) := integral_sub hcI hQI
    have h3 : ∫ _ω, Qf X ∂(μ W 1) = Qf X := by
      rw [integral_const, probReal_univ, one_smul]
    rw [h1, h2, h3, hm, e1, e2]
    ring
  have hmM : m ≤ M := by
    have h1 := hinc W hW1 g hg E hE1 X hX
    have h2 : Ki / g ^ 2 ≤ Ki := div_le_self hKi.le hg2
    have h3 : KQ * δ ≤ KQ * CQ := mul_le_mul_of_nonneg_left hδC hKQ.le
    rw [hm, hM]
    linarith [le_abs_self (incMean g E X), neg_abs_le (transOp g E Qf X), le_abs_self (Qf X)]
  -- the second moment
  obtain ⟨hZ2I, hI2⟩ := nzs_corr_sq hW1 hg hE1 hX R Ks q (Kv := Kv) (KF := KF)
    (hvar W hW1 g hg E hE1 X hX).2.2 (fun k hk => (hmom W hW1 g hg E hEF' X hX k hk).2)
    hδ0 hδC hZm
  have hP : 0 < (W : ℝ) * g ^ 2 := by positivity
  -- the tail
  have hp1 : 1 ≤ p := by omega
  have hTe : ∀ ω, 3 * (2 * (2 * u ω / g)) ^ p = 3 * (4 / g) ^ p * u ω ^ p := by
    intro ω
    rw [show 2 * (2 * u ω / g) = 4 / g * u ω by ring, mul_pow, mul_assoc]
  have hIT : ∫ ω, 3 * (4 / g) ^ p * u ω ^ p ∂(μ W 1) ≤ s / (96 * ((W : ℝ) * g ^ 2)) := by
    rw [integral_const_mul]
    exact nzs_tail_int hε hs0 hWr hLW hg hgW (hmp W)
  have htail : ∀ ω, s * Z ω < -1 → Real.exp (-(s * Z ω)) ≤ 3 * (4 / g) ^ p * u ω ^ p := by
    intro ω hω
    rw [← hTe ω]
    have hK : KQ * δ ≤ KQ * CQ := mul_le_mul_of_nonneg_left hδC hKQ.le
    exact nzs_corr_tail_pt hs0 hs1 (hx0 ω) (hcb ω) ((hQ' ω).trans hK) (hQX.trans hK) hsQ hp1 hω
  have hTI : Integrable (fun ω => 3 * (4 / g) ^ p * u ω ^ p) (μ W 1) := hup.const_mul _
  have hY2 : (fun ω => (s * Z ω) ^ 2) = fun ω => s ^ 2 * Z ω ^ 2 := by funext ω; ring
  have hmain := nzs_mgf_le (P := μ W 1) (Y := fun ω => s * Z ω)
    (T := fun ω => 3 * (4 / g) ^ p * u ω ^ p) (measurable_const.mul hZm) (hZI.const_mul s)
    (by rw [hY2]; exact hZ2I.const_mul _) hTI (fun ω => by have := hu0 ω; positivity) htail
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have e1 : ∫ ω, s * Z ω ∂(μ W 1) = s * m := by rw [integral_const_mul, hZint]
  have e2 : ∫ ω, (s * Z ω) ^ 2 ∂(μ W 1) = s ^ 2 * ∫ ω, Z ω ^ 2 ∂(μ W 1) := by
    rw [hY2, integral_const_mul]
  rw [e1, e2, show (48 : ℝ) * W * g ^ 2 = 48 * ((W : ℝ) * g ^ 2) by ring]
  have hdr : 1 / (12 * ((W : ℝ) * g ^ 2)) ≤ m := by
    rw [show (12 : ℝ) * ((W : ℝ) * g ^ 2) = 12 * W * g ^ 2 by ring]; exact hdrift
  exact nzs_final hs0 hP hdr hmM hsM hsV hI2 hIT

/-- The corrected one-step exponential moment: at a state where
`P_g c − (P_g − I) Q_g ≥ (12 W g²)⁻¹`, `𝔼 e^{−s(c − Q_g(X') + Q_g(X))} ≤ exp(−s (48 W g²)⁻¹)`. -/
theorem corrStep_mgf_le {ε : ℝ} (hε : 0 < ε) (R : ℕ) (Ks : Finset NzInt) {CQ : ℝ}
    (hCQ : 0 < CQ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ g : ℝ, (W : ℝ) ^ ε ≤ g → ∀ E : ℝ, |E| ≤ E₁ → ∀ q : NzInt → ℂ,
        ∑ k ∈ Ks, ‖q k‖ ≤ CQ / g ^ 2 → ∀ X : State W, IsState X →
          1 / (12 * W * g ^ 2) ≤
            incMean g E X - (transOp g E (corrQ g E R Ks q) X - corrQ g E R Ks q X) →
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * (stepInc g E X (gueBlock W 1 ω 0) -
              corrQ g E R Ks q (stepState g E X (gueBlock W 1 ω 0)) + corrQ g E R Ks q X))))
              ∂(μ W 1) ≤
            ENNReal.ofReal (Real.exp (-(s / (48 * W * g ^ 2)))) := by
  exact nzs_corrStep hε R Ks hCQ

end LSBA
