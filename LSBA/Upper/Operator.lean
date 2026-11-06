import LSBA.Transfer.VolCocycle
import LSBA.Gauss.BlockAppend
import LSBA.Gauss.NormMoment

/-!
# The half-power transfer operator

The transfer batches (8.18) [up:eq:transfer-batches] as `batchMat`: in 𝒢 for every sample,
measurable, and concatenated through `blockAppend` with the first blocks acting first. The operator
`P_{1/2}` of (8.19) [cc:eq:Ps] on bounded measurable functions of the flag, as an expectation over
the `q` input blocks: integrable, closed on bounded measurable functions, linear and positive, with
`|P_{1/2} h| ≤ P_{1/2}|h|`. The hypothesis (8.21) [up:eq:power-input] at one point as `PowerDecayAt`
(Definition 8.5 [up:def:transfer-operator]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `S* T_n ⋯ T_1 S` over `n` fresh GUE blocks, with `T_i = T_i(max{1,g} E / g)` of (8.9)
[eq:c-transfer] and `S = S_0`; for `n = q` this is the batch `F_1` of (8.18)
[up:eq:transfer-batches]. -/
def batchMat (W : ℕ) (g E : ℝ) (n : ℕ) (ω : Ω W n) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (freeConj W 0)ᴴ *
      transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) n *
    freeConj W 0

/-- Bounded measurable functions of the flag. -/
def IsBddMeas {W : ℕ} (h : IsoFlag W → ℝ) : Prop :=
  Measurable h ∧ ∃ M : ℝ, ∀ x, |h x| ≤ M

/-- The operator `P_{1/2}` of (8.19) [cc:eq:Ps], as an expectation over the `q` input blocks of
the batch (8.18) [up:eq:transfer-batches]. -/
def halfOp (W : ℕ) (g E : ℝ) (q : ℕ) (h : IsoFlag W → ℝ) (x : IsoFlag W) : ℝ :=
  ∫ ω, Real.exp (-volCocycle (batchMat W g E q ω) x / 2) * h (flagAct (batchMat W g E q ω) x)
    ∂(μ W q)

/-- (8.21) [up:eq:power-input] at one point: `‖P_{1/2}^k 1‖_∞ ≤ C W^C e^{-ck/𝔟}` for all `k`. -/
def PowerDecayAt (W : ℕ) (g E : ℝ) (q : ℕ) (b c C : ℝ) : Prop :=
  ∀ k : ℕ, ∀ x : IsoFlag W,
    |(halfOp W g E q)^[k] (fun _ => 1) x| ≤ C * (W : ℝ) ^ C * Real.exp (-c * k / b)

/-- Every batch lies in `𝒢` (Definition 8.5 [up:def:transfer-operator]), for every sample. -/
theorem batchMat_mem_isoGroup (W : ℕ) (g E : ℝ) (n : ℕ) (ω : Ω W n) :
    batchMat W g E n ω ∈ isoGroup W := by
  refine conj_transferProd_mem_isoGroup g (max 1 g * E / g) _ (fun k => ?_) n
  by_cases h : k < n
  · simp only [h, dite_true]
    exact gueBlock_isHermitian W n ω ⟨k, h⟩
  · simp only [h, dite_false]
    exact Matrix.isHermitian_zero

private theorem operator_continuous_gueBlock {W L : ℕ} (b : Fin L) :
    Continuous fun ω : Ω W L => gueBlock W L ω b := by
  refine continuous_matrix fun α β => ?_
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

private theorem operator_continuous_kronecker_left {W : ℕ} (P : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => P ⊗ₖ V := by
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.kroneckerMap_apply]
  exact continuous_const.mul (continuous_id.matrix_elem i.2 j.2)

private theorem operator_continuous_transferMat {W : ℕ} (g : ℝ) (z : ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => transferMat g z V := by
  unfold transferMat
  exact continuous_const.sub
    ((continuous_const_smul _).comp (operator_continuous_kronecker_left _))

private theorem operator_continuous_transferProd {W : ℕ} {X : Type*} [TopologicalSpace X]
    (g : ℝ) (z : ℂ) (V : X → ℕ → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ k, Continuous fun x => V x k)
    (n : ℕ) : Continuous fun x => transferProd g z (V x) n := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact ((operator_continuous_transferMat g z).comp (hV n)).mul ih

theorem measurable_batchMat (W : ℕ) (g E : ℝ) (n : ℕ) : Measurable (batchMat W g E n) := by
  have hP : Continuous fun ω : Ω W n =>
      transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) n := by
    refine operator_continuous_transferProd g _
      (fun (ω : Ω W n) k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) (fun k => ?_) n
    by_cases h : k < n
    · simp only [h, dite_true]
      exact operator_continuous_gueBlock _
    · simp only [h, dite_false]
      exact continuous_const
  refine Continuous.measurable ?_
  unfold batchMat
  exact (continuous_const.mul hP).mul continuous_const

private theorem operator_transferProd_congr {W : ℕ} (g : ℝ) (z : ℂ)
    (V V' : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) (h : ∀ k < n, V k = V' k) :
    transferProd g z V n = transferProd g z V' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change transferMat g z (V n) * transferProd g z V n =
      transferMat g z (V' n) * transferProd g z V' n
    rw [h n (Nat.lt_succ_self n), ih fun k hk => h k (Nat.lt_succ_of_lt hk)]

private theorem operator_transferProd_add {W : ℕ} (g : ℝ) (z : ℂ)
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (m n : ℕ) :
    transferProd g z V (m + n) =
      transferProd g z (fun k => V (m + k)) n * transferProd g z V m := by
  induction n with
  | zero => simp [transferProd]
  | succ n ih =>
    change transferMat g z (V (m + n)) * transferProd g z V (m + n) =
      transferMat g z (V (m + n)) * transferProd g z (fun k => V (m + k)) n *
        transferProd g z V m
    rw [ih, Matrix.mul_assoc]

/-- Concatenation: the first `m` blocks act first (Definition 8.5 [up:def:transfer-operator]). -/
theorem batchMat_add (W : ℕ) (g E : ℝ) (m n : ℕ) (ω : Ω W (m + n)) :
    batchMat W g E (m + n) ω =
      batchMat W g E n (blockAppend W m n ω).2 * batchMat W g E m (blockAppend W m n ω).1 := by
  have hS : freeConj W 0 * (freeConj W 0)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp (freeConj_zero_mem_unitaryGroup W)
    rwa [Matrix.star_eq_conjTranspose] at this
  unfold batchMat
  rw [operator_transferProd_add]
  have h2 : transferProd g ((max 1 g * E / g : ℝ) : ℂ)
      (fun k => (fun k => if h : k < m + n then gueBlock W (m + n) ω ⟨k, h⟩ else 0) (m + k)) n =
      transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun k => if h : k < n then gueBlock W n (blockAppend W m n ω).2 ⟨k, h⟩ else 0) n := by
    refine operator_transferProd_congr _ _ _ _ n fun k hk => ?_
    have h1 : m + k < m + n := by omega
    simp only [h1, hk, dite_true]
    rw [gueBlock_blockAppend_snd]
    rfl
  have h3 : transferProd g ((max 1 g * E / g : ℝ) : ℂ)
      (fun k => if h : k < m + n then gueBlock W (m + n) ω ⟨k, h⟩ else 0) m =
      transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun k => if h : k < m then gueBlock W m (blockAppend W m n ω).1 ⟨k, h⟩ else 0) m := by
    refine operator_transferProd_congr _ _ _ _ m fun k hk => ?_
    have h1 : k < m + n := by omega
    simp only [h1, hk, dite_true]
    rw [gueBlock_blockAppend_fst]
    rfl
  rw [h2, h3]
  have : (freeConj W 0)ᴴ * transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun k => if h : k < n then gueBlock W n (blockAppend W m n ω).2 ⟨k, h⟩ else 0) n *
        freeConj W 0 *
      ((freeConj W 0)ᴴ * transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun k => if h : k < m then gueBlock W m (blockAppend W m n ω).1 ⟨k, h⟩ else 0) m *
        freeConj W 0) =
      (freeConj W 0)ᴴ * transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun k => if h : k < n then gueBlock W n (blockAppend W m n ω).2 ⟨k, h⟩ else 0) n *
        (freeConj W 0 * (freeConj W 0)ᴴ) *
        transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun k => if h : k < m then gueBlock W m (blockAppend W m n ω).1 ⟨k, h⟩ else 0) m *
        freeConj W 0 := by
    simp only [Matrix.mul_assoc]
  rw [this, hS, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

private theorem operator_norm_kron_le {W : ℕ} (V : Matrix (Fin W) (Fin W) ℂ) :
    ‖(!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V‖ ≤ ‖V‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg V) fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  set y : EuclideanSpace ℂ (Fin W) := WithLp.toLp 2 (fun β => x.ofLp (0, β)) with hy
  have hVy : ‖Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) V y‖ ≤ ‖V‖ * ‖y‖ := by
    have := (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) V).le_opNorm y
    rwa [Matrix.l2_opNorm_toEuclideanCLM] at this
  have hyx : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    have : 0 ≤ ∑ β, ‖x.ofLp (1, β)‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    simp only [hy]
    linarith
  have key : ∀ (i : Fin 2) (β : Fin W),
      (((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) *ᵥ x.ofLp) (i, β) =
        if i = 0 then (V *ᵥ y.ofLp) β else 0 := by
    intro i β
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, hy]
  rw [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM]
  simp only [key, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Finset.sum_const_zero, add_zero]
  have h1 : ∑ β, ‖(V *ᵥ y.ofLp) β‖ ^ 2 = ‖Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) V y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM]
  rw [h1]
  calc _ ≤ (‖V‖ * ‖y‖) ^ 2 := by gcongr
    _ = ‖V‖ ^ 2 * ‖y‖ ^ 2 := by ring
    _ ≤ ‖V‖ ^ 2 * ‖x‖ ^ 2 := by gcongr
    _ = _ := by ring

private theorem operator_norm_transferMat_le {W : ℕ} (g : ℝ) (z : ℂ)
    (V : Matrix (Fin W) (Fin W) ℂ) :
    ‖transferMat g z V‖ ≤ ‖transferFree W z‖ + |g|⁻¹ * ‖V‖ := by
  unfold transferMat
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  exact operator_norm_kron_le V

private theorem operator_norm_batchMat_one_le {W : ℕ} (g E : ℝ) (ω : Ω W 1) :
    ‖batchMat W g E 1 ω‖ ≤ ‖(freeConj W 0)ᴴ‖ *
      (‖transferFree W ((max 1 g * E / g : ℝ) : ℂ)‖ + |g|⁻¹ * ‖gueBlock W 1 ω 0‖) *
        ‖freeConj W 0‖ := by
  have h1 : batchMat W g E 1 ω = (freeConj W 0)ᴴ *
      transferMat g ((max 1 g * E / g : ℝ) : ℂ) (gueBlock W 1 ω 0) * freeConj W 0 := by
    unfold batchMat
    simp [transferProd]
  rw [h1]
  refine (norm_mul_le _ _).trans ?_
  refine mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans ?_) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left (operator_norm_transferMat_le _ _ _) (norm_nonneg _)

private theorem operator_integrable_norm_gueBlock (W : ℕ) :
    Integrable (fun ω : Ω W 1 => ‖gueBlock W 1 ω 0‖) (μ W 1) := by
  refine ⟨(operator_continuous_gueBlock 0).norm.aestronglyMeasurable, ?_⟩
  have h := lintegral_norm_gueBlock_rpow_le W 1 0 (s := 1) one_pos (by norm_num)
  simp only [ENNReal.rpow_one] at h
  unfold HasFiniteIntegral
  simp only [enorm_norm]
  exact lt_of_le_of_lt h ENNReal.ofReal_lt_top

private theorem operator_integrable_norm_batchMat (W : ℕ) (g E : ℝ) (n : ℕ) :
    Integrable (fun ω => ‖batchMat W g E n ω‖) (μ W n) := by
  induction n with
  | zero =>
    have h : (fun ω : Ω W 0 => ‖batchMat W g E 0 ω‖) =
        fun _ => ‖(freeConj W 0)ᴴ * 1 * freeConj W 0‖ := by
      funext ω
      simp [batchMat, transferProd]
    rw [h]
    exact integrable_const _
  | succ n ih =>
    have h1 : Integrable (fun ω : Ω W 1 => ‖batchMat W g E 1 ω‖) (μ W 1) := by
      refine Integrable.mono' (g := fun ω : Ω W 1 => ‖(freeConj W 0)ᴴ‖ *
        (‖transferFree W ((max 1 g * E / g : ℝ) : ℂ)‖ + |g|⁻¹ * ‖gueBlock W 1 ω 0‖) *
          ‖freeConj W 0‖) ?_ ((measurable_batchMat W g E 1).norm.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => ?_)
      · exact (((integrable_const _).add
          ((operator_integrable_norm_gueBlock W).const_mul _)).const_mul _).mul_const _
      · rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact operator_norm_batchMat_one_le g E ω
    have h2 := (ih.mul_prod h1)
    have h3 := (measurePreserving_blockAppend W n 1).integrable_comp_of_integrable h2
    refine Integrable.mono' (g := ((fun z : Ω W n × Ω W 1 =>
      ‖batchMat W g E n z.1‖ * ‖batchMat W g E 1 z.2‖) ∘ blockAppend W n 1))
      h3 ((measurable_batchMat W g E (n + 1)).norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _), batchMat_add, Function.comp_apply, mul_comm]
    exact norm_mul_le _ _

private theorem operator_integrand_le {W : ℕ} (g E : ℝ) (n : ℕ) (ω : Ω W n) (x : IsoFlag W)
    {h : IsoFlag W → ℝ} {M : ℝ} (hM : ∀ y, |h y| ≤ M) :
    |Real.exp (-volCocycle (batchMat W g E n ω) x / 2) * h (flagAct (batchMat W g E n ω) x)| ≤
      M * (1 + ‖batchMat W g E n ω‖) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x)
  set F := batchMat W g E n ω with hF
  have hc := abs_volCocycle_le (batchMat_mem_isoGroup W g E n ω).1 x
  rw [← hF] at hc
  have hexp : Real.exp (-volCocycle F x / 2) ≤ 1 + ‖F‖ := by
    rcases (norm_nonneg F).eq_or_lt with h0 | hpos
    · rw [← h0, Real.log_zero] at hc
      have : volCocycle F x = 0 := abs_nonpos_iff.mp hc
      rw [this, ← h0]
      simp
    · calc Real.exp (-volCocycle F x / 2) ≤ Real.exp (Real.log ‖F‖) := by
            refine Real.exp_le_exp.mpr ?_
            have h1 := abs_le.mp hc
            have h2 : 0 ≤ Real.log ‖F‖ := (abs_nonneg _).trans hc
            linarith [h1.1, h1.2]
        _ = ‖F‖ := Real.exp_log hpos
        _ ≤ 1 + ‖F‖ := by linarith
  rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm M]
  exact mul_le_mul hexp (hM _) (abs_nonneg _) (by positivity)

private theorem operator_measurable_integrand {W : ℕ} (g E : ℝ) (q : ℕ) {h : IsoFlag W → ℝ}
    (hh : Measurable h) :
    Measurable fun p : Ω W q × IsoFlag W =>
      Real.exp (-volCocycle (batchMat W g E q p.1) p.2 / 2) *
        h (flagAct (batchMat W g E q p.1) p.2) := by
  have hB : Measurable fun p : Ω W q × IsoFlag W => (batchMat W g E q p.1, p.2) :=
    ((measurable_batchMat W g E q).comp measurable_fst).prodMk measurable_snd
  have h1 := (measurable_volCocycle W).comp hB
  have h2 := (measurable_flagAct W).comp hB
  exact (Real.measurable_exp.comp (h1.neg.div_const 2)).mul (hh.comp h2)

/-- For bounded measurable `h`, the integrand of (8.19) [cc:eq:Ps] is integrable. -/
theorem integrable_halfOp {W : ℕ} (g E : ℝ) (q : ℕ) {h : IsoFlag W → ℝ} (hh : IsBddMeas h)
    (x : IsoFlag W) :
    Integrable (fun ω => Real.exp (-volCocycle (batchMat W g E q ω) x / 2) *
      h (flagAct (batchMat W g E q ω) x)) (μ W q) := by
  obtain ⟨hm, M, hM⟩ := hh
  have hmeas := (operator_measurable_integrand g E q hm).comp
    (measurable_id.prodMk (measurable_const : Measurable fun _ : Ω W q => x))
  refine Integrable.mono' (g := fun ω => M * (1 + ‖batchMat W g E q ω‖)) ?_
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((integrable_const _).add (operator_integrable_norm_batchMat W g E q)).const_mul M
  · rw [Real.norm_eq_abs]
    exact operator_integrand_le g E q ω x hM

/-- `P_{1/2}` maps bounded measurable functions to bounded measurable functions. -/
theorem halfOp_isBddMeas {W : ℕ} (g E : ℝ) (q : ℕ) {h : IsoFlag W → ℝ} (hh : IsBddMeas h) :
    IsBddMeas (halfOp W g E q h) := by
  obtain ⟨hm, M, hM⟩ := hh
  refine ⟨?_, ∫ ω, M * (1 + ‖batchMat W g E q ω‖) ∂(μ W q), fun x => ?_⟩
  · have := ((operator_measurable_integrand g E q hm).stronglyMeasurable).integral_prod_left'
      (μ := μ W q)
    exact this.measurable
  · rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((integrable_const _).add (operator_integrable_norm_batchMat W g E q)).const_mul M
    · rw [Real.norm_eq_abs]
      exact operator_integrand_le g E q ω x hM

theorem halfOp_smul {W : ℕ} (g E : ℝ) (q : ℕ) (r : ℝ) (h : IsoFlag W → ℝ) :
    halfOp W g E q (r • h) = r • halfOp W g E q h := by
  funext x
  simp only [halfOp, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  ring

/-- Positivity: `P_{1/2}` is monotone on bounded measurable functions. -/
theorem halfOp_mono {W : ℕ} (g E : ℝ) (q : ℕ) {h h' : IsoFlag W → ℝ} (hh : IsBddMeas h)
    (hh' : IsBddMeas h') (hle : h ≤ h') : halfOp W g E q h ≤ halfOp W g E q h' := by
  intro x
  exact integral_mono (integrable_halfOp g E q hh x) (integrable_halfOp g E q hh' x)
    fun ω => mul_le_mul_of_nonneg_left (hle _) (Real.exp_pos _).le

/-- `|P_{1/2} h| ≤ P_{1/2} |h|` (proof of Lemma 8.11 [up:lem:angular]). -/
theorem abs_halfOp_le {W : ℕ} (g E : ℝ) (q : ℕ) {h : IsoFlag W → ℝ} (hh : IsBddMeas h)
    (x : IsoFlag W) : |halfOp W g E q h x| ≤ halfOp W g E q (fun y => |h y|) x := by
  have _ := hh
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

end LSBA
