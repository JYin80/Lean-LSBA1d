import LSBA.Upper.BatchCutoff
import LSBA.Gauss.GUENormMoment

/-!
# The bad mass of a transfer batch

Step 1 of Appendix G.5 [sec:c-component-proof]: fixed GUE norm moments give
`𝔼‖F‖ ≤ (max{1, g⁻¹} (1 + |E| + C₁))^n` for a batch of `n` inputs (independence of the inputs
and `‖T_i‖ ≤ max{1, g⁻¹} (1 + |E| + ‖V_i‖)`), and with the weight bound of the batch cutoff and
the Cauchy–Schwarz inequality the bad mass of (8.27) [up:eq:coarse-density],
`𝔼[(1 - χ_q) ‖F‖^{1/2}] ≤ ½`, for all large `W`, uniformly in `W^{-B} ≤ g ≤ W^B` and `|E| ≤ E₀`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The identity has operator norm at most one. -/
private theorem bbm_norm_one_le {n : Type*} [Fintype n] [DecidableEq n] :
    ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp

/-- A unitary matrix has operator norm at most one. -/
private theorem bbm_norm_unitary_le {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : ‖U‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hU] at h
  have h1 := bbm_norm_one_le (n := n)
  nlinarith [norm_nonneg U]

/-- `‖P₁ ⊗ V‖ ≤ ‖V‖` for the projection `P₁ = diag(1, 0)`. -/
private theorem bbm_norm_kron_le {W : ℕ} (V : Matrix (Fin W) (Fin W) ℂ) :
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
  have h1 : ∑ β, ‖(V *ᵥ y.ofLp) β‖ ^ 2 =
      ‖Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) V y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM]
  rw [h1]
  calc _ ≤ (‖V‖ * ‖y‖) ^ 2 := by gcongr
    _ = ‖V‖ ^ 2 * ‖y‖ ^ 2 := by ring
    _ ≤ ‖V‖ ^ 2 * ‖x‖ ^ 2 := by gcongr
    _ = _ := by ring

/-- The rotation `[[0, -1], [1, 0]] ⊗ I_W` has operator norm at most one. -/
private theorem bbm_norm_rot_le (W : ℕ) :
    ‖(!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := by
  refine bbm_norm_unitary_le ?_
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one, Matrix.one_mul]
  have : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * !![0, -1; 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  rw [this, Matrix.one_kronecker_one]

/-- `‖T(V)‖ ≤ 1 + |z| + |g|⁻¹ ‖V‖` for the transfer matrix `T_j(z)` of (8.9) [eq:c-transfer]. -/
private theorem bbm_norm_transferMat_le {W : ℕ} (g : ℝ) (z : ℂ) (V : Matrix (Fin W) (Fin W) ℂ) :
    ‖transferMat g z V‖ ≤ 1 + ‖z‖ + |g|⁻¹ * ‖V‖ := by
  have hdec : transferMat g z V =
      (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) +
        z • ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) -
        ((g : ℂ)⁻¹) • ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) := by
    unfold transferMat transferFree
    have : (!![z, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) =
        !![0, -1; 1, 0] + z • !![1, 0; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [this, Matrix.add_kronecker, Matrix.smul_kronecker]
  rw [hdec]
  refine (norm_sub_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans ?_) ?_
  · refine add_le_add (bbm_norm_rot_le W) ?_
    rw [norm_smul]
    calc ‖z‖ * ‖(!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)‖
        ≤ ‖z‖ * 1 := by gcongr; exact (bbm_norm_kron_le _).trans bbm_norm_one_le
      _ = ‖z‖ := mul_one _
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact bbm_norm_kron_le V

/-- `‖T_j‖ ≤ max{1, g⁻¹} (1 + |E| + ‖V‖)` for `g > 0` and `T_j = T_j(max{1,g} E / g)`
(8.9) [eq:c-transfer]. -/
private theorem bbm_norm_transferMat_le_max {W : ℕ} {g : ℝ} (hg : 0 < g) (E : ℝ)
    (V : Matrix (Fin W) (Fin W) ℂ) :
    ‖transferMat g ((max 1 g * E / g : ℝ) : ℂ) V‖ ≤ max 1 g⁻¹ * (1 + |E| + ‖V‖) := by
  refine (bbm_norm_transferMat_le g _ V).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hg,
    abs_of_pos (lt_max_of_lt_left one_pos)]
  have hh : max 1 g / g = max 1 g⁻¹ := by
    rcases le_total 1 g with h | h
    · rw [max_eq_right h, div_self hg.ne', max_eq_left (inv_le_one_of_one_le₀ h)]
    · rw [max_eq_left h, one_div, max_eq_right (one_le_inv₀ hg |>.2 h)]
  have h1 : (1 : ℝ) ≤ max 1 g⁻¹ := le_max_left _ _
  have h2 : g⁻¹ ≤ max 1 g⁻¹ := le_max_right _ _
  rw [mul_div_right_comm, hh]
  nlinarith [norm_nonneg V, abs_nonneg E]

/-- A batch of no inputs has norm at most one: `‖S* S‖ ≤ 1`. -/
private theorem bbm_norm_batchMat_zero_le (W : ℕ) (g E : ℝ) (ω : Ω W 0) :
    ‖batchMat W g E 0 ω‖ ≤ 1 := by
  have hS := bbm_norm_unitary_le (freeConj_zero_mem_unitaryGroup W)
  have hSH : ‖(freeConj W 0)ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]; exact hS
  unfold batchMat
  simp only [transferProd, Matrix.mul_one]
  calc ‖(freeConj W 0)ᴴ * freeConj W 0‖ ≤ ‖(freeConj W 0)ᴴ‖ * ‖freeConj W 0‖ := norm_mul_le _ _
    _ ≤ 1 * 1 := by gcongr
    _ = 1 := one_mul 1

/-- One input: `‖F‖ ≤ max{1, g⁻¹} (1 + |E| + ‖V‖)` for `g > 0` (Step 1 of Appendix G.5
[sec:c-component-proof]). -/
private theorem bbm_norm_batchMat_one_le {W : ℕ} {g : ℝ} (hg : 0 < g) (E : ℝ) (ω : Ω W 1) :
    ‖batchMat W g E 1 ω‖ ≤ max 1 g⁻¹ * (1 + |E| + ‖gueBlock W 1 ω 0‖) := by
  have h1 : batchMat W g E 1 ω = (freeConj W 0)ᴴ *
      transferMat g ((max 1 g * E / g : ℝ) : ℂ) (gueBlock W 1 ω 0) * freeConj W 0 := by
    unfold batchMat
    simp [transferProd]
  have hS := bbm_norm_unitary_le (freeConj_zero_mem_unitaryGroup W)
  have hSH : ‖(freeConj W 0)ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]; exact hS
  rw [h1]
  calc ‖(freeConj W 0)ᴴ * transferMat g ((max 1 g * E / g : ℝ) : ℂ) (gueBlock W 1 ω 0) *
        freeConj W 0‖
      ≤ ‖(freeConj W 0)ᴴ‖ * ‖transferMat g ((max 1 g * E / g : ℝ) : ℂ) (gueBlock W 1 ω 0)‖ *
        ‖freeConj W 0‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ 1 * (max 1 g⁻¹ * (1 + |E| + ‖gueBlock W 1 ω 0‖)) * 1 := by
        gcongr; exact bbm_norm_transferMat_le_max hg E _
    _ = _ := by rw [one_mul, mul_one]

/-- One input: `𝔼‖F‖ ≤ max{1, g⁻¹} (1 + |E| + C₁)` when `𝔼‖V‖ ≤ C₁` (Step 1 of Appendix G.5
[sec:c-component-proof]). -/
private theorem bbm_lintegral_one_le {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hmom : ∀ W : ℕ, ∫⁻ ω, ‖gueBlock W 1 ω 0‖ₑ ^ 1 ∂(μ W 1) ≤ ENNReal.ofReal C₁)
    (W : ℕ) {g : ℝ} (hg : 0 < g) (E : ℝ) :
    ∫⁻ ω, ‖batchMat W g E 1 ω‖ₑ ∂(μ W 1) ≤
      ENNReal.ofReal (max 1 g⁻¹ * (1 + |E| + C₁)) := by
  have h0 : 0 ≤ max 1 g⁻¹ := zero_le_one.trans (le_max_left _ _)
  calc ∫⁻ ω, ‖batchMat W g E 1 ω‖ₑ ∂(μ W 1)
      ≤ ∫⁻ ω, ENNReal.ofReal (max 1 g⁻¹) *
          (ENNReal.ofReal (1 + |E|) + ‖gueBlock W 1 ω 0‖ₑ) ∂(μ W 1) := by
        refine lintegral_mono fun ω => ?_
        rw [← ofReal_norm]
        calc ENNReal.ofReal ‖batchMat W g E 1 ω‖
            ≤ ENNReal.ofReal (max 1 g⁻¹ * (1 + |E| + ‖gueBlock W 1 ω 0‖)) :=
              ENNReal.ofReal_le_ofReal (bbm_norm_batchMat_one_le hg E ω)
          _ = _ := by
              rw [ENNReal.ofReal_mul h0, ENNReal.ofReal_add (by positivity) (norm_nonneg _),
                ofReal_norm]
    _ = ENNReal.ofReal (max 1 g⁻¹) *
          (ENNReal.ofReal (1 + |E|) + ∫⁻ ω, ‖gueBlock W 1 ω 0‖ₑ ∂(μ W 1)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (max 1 g⁻¹) * (ENNReal.ofReal (1 + |E|) + ENNReal.ofReal C₁) := by
        gcongr
        simpa using hmom W
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) hC₁.le, ← ENNReal.ofReal_mul h0]

/-- The batch cutoff is nonnegative when `χ` is. -/
private theorem bbm_batchCut_nonneg {W n : ℕ} {χ : Ω W 1000 → ℝ} (hχ : ∀ ω, 0 ≤ χ ω)
    (ω : Ω W (1000 + n)) : 0 ≤ batchCut W n χ ω :=
  mul_nonneg (hχ _) (Finset.prod_nonneg fun _ _ => Real.smoothTransition.nonneg _)

/-- The batch cutoff is measurable when `χ` is. -/
private theorem bbm_measurable_batchCut {W n : ℕ} {χ : Ω W 1000 → ℝ} (hχ : Measurable χ) :
    Measurable (batchCut W n χ) := by
  unfold batchCut
  refine (hχ.comp (measurable_fst.comp (measurePreserving_blockAppend W 1000 n).measurable)).mul ?_
  refine Finset.measurable_prod _ fun i _ => ?_
  have hc : Continuous (blockCut W) := by
    unfold blockCut
    exact Real.smoothTransition.continuous.comp (by fun_prop)
  exact hc.measurable.comp (measurable_pi_iff.2 fun k => measurable_pi_apply (Fin.natAdd 1000 i, k))

/-- For large `W`, `(C e^{-cW} + n e^{-W²/8}) (W^B a)^q ≤ ¼`: the polynomial factor `W^{Bq}` is
beaten by `e^{-min{c,1} W}`. -/
private theorem bbm_decay (B c C a : ℝ) (n q : ℕ) (hc : 0 < c) (hC : 0 < C) (ha : 0 < a) :
    ∃ W₀ : ℕ, 8 ≤ W₀ ∧ ∀ W : ℕ, W₀ ≤ W →
      (C * Real.exp (-c * W) + (n : ℝ) * Real.exp (-((W : ℝ) * W) / 8)) *
        (((W : ℝ) ^ B) * a) ^ q ≤ 1 / 4 := by
  set c' := min c 1 with hc'
  have hc'0 : 0 < c' := lt_min hc one_pos
  set N := ⌈B * q⌉₊ with hN
  set K := (C + n) * a ^ q / c' ^ N with hK
  have htend : Filter.Tendsto (fun W : ℕ => K * ((c' * W) ^ N * Real.exp (-(c' * W))))
      Filter.atTop (nhds 0) := by
    have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N
    have h2 : Filter.Tendsto (fun W : ℕ => c' * (W : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hc'0
    simpa using (h1.comp h2).const_mul K
  obtain ⟨W₁, hW₁⟩ := Filter.eventually_atTop.1
    (htend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  refine ⟨max W₁ 8, le_max_right _ _, fun W hW => ?_⟩
  have hW8 : (8 : ℝ) ≤ W := by exact_mod_cast (le_max_right _ _).trans hW
  have hWW1 : W₁ ≤ W := (le_max_left _ _).trans hW
  have hw0 : (0 : ℝ) < W := by linarith
  have hw1 : (1 : ℝ) ≤ W := by linarith
  have e1 : Real.exp (-c * W) ≤ Real.exp (-(c' * W)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left c 1])
  have e2 : Real.exp (-((W : ℝ) * W) / 8) ≤ Real.exp (-(c' * W)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right c 1])
  have hm : C * Real.exp (-c * W) + (n : ℝ) * Real.exp (-((W : ℝ) * W) / 8) ≤
      (C + n) * Real.exp (-(c' * W)) := by
    have h1 : C * Real.exp (-c * W) ≤ C * Real.exp (-(c' * W)) := by gcongr
    have h2 : (n : ℝ) * Real.exp (-((W : ℝ) * W) / 8) ≤ n * Real.exp (-(c' * W)) := by gcongr
    linarith
  have hp : (((W : ℝ) ^ B) * a) ^ q ≤ (W : ℝ) ^ N * a ^ q := by
    rw [mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ B) q, ← Real.rpow_mul hw0.le]
    gcongr
    calc (W : ℝ) ^ (B * q) ≤ (W : ℝ) ^ (N : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hw1 (Nat.le_ceil _)
      _ = (W : ℝ) ^ N := Real.rpow_natCast _ _
  calc (C * Real.exp (-c * W) + (n : ℝ) * Real.exp (-((W : ℝ) * W) / 8)) *
        (((W : ℝ) ^ B) * a) ^ q
      ≤ ((C + n) * Real.exp (-(c' * W))) * ((W : ℝ) ^ N * a ^ q) :=
        mul_le_mul hm hp (by positivity) (by positivity)
    _ = K * ((c' * W) ^ N * Real.exp (-(c' * W))) := by
        rw [hK, mul_pow]
        field_simp
    _ ≤ 1 / 4 := (hW₁ W hWW1).le

/-- `𝔼‖F‖ ≤ (max{1, g⁻¹} (1 + |E| + C₁))^n` for a batch of `n` inputs and `g > 0`, with `C₁`
a uniform bound on `𝔼‖V‖` for one GUE block (Step 1 of Appendix G.5
[sec:c-component-proof]). -/
theorem lintegral_norm_batchMat_le :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (W n : ℕ) (g E : ℝ), 0 < g →
      ∫⁻ ω, ‖batchMat W g E n ω‖ₑ ∂(μ W n) ≤
        ENNReal.ofReal ((max 1 g⁻¹ * (1 + |E| + C₁)) ^ n) := by
  obtain ⟨C₁, hC₁, hmom⟩ := lintegral_norm_gueBlock_pow_le 1
  refine ⟨C₁, hC₁, fun W n g E hg => ?_⟩
  have ha : 0 ≤ max 1 g⁻¹ * (1 + |E| + C₁) :=
    mul_nonneg (zero_le_one.trans (le_max_left _ _)) (by positivity)
  induction n with
  | zero =>
    calc ∫⁻ ω, ‖batchMat W g E 0 ω‖ₑ ∂(μ W 0) ≤ ∫⁻ _, 1 ∂(μ W 0) := by
          refine lintegral_mono fun ω => ?_
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_one.2 (bbm_norm_batchMat_zero_le W g E ω)
      _ = _ := by simp
  | succ n ih =>
    have hmp := measurePreserving_blockAppend W n 1
    have hm1 : Measurable fun z : Ω W n × Ω W 1 =>
        ‖batchMat W g E n z.1‖ₑ * ‖batchMat W g E 1 z.2‖ₑ :=
      ((measurable_batchMat W g E n).comp measurable_fst).enorm.mul
        ((measurable_batchMat W g E 1).comp measurable_snd).enorm
    calc ∫⁻ ω, ‖batchMat W g E (n + 1) ω‖ₑ ∂(μ W (n + 1))
        ≤ ∫⁻ ω, (fun z : Ω W n × Ω W 1 =>
            ‖batchMat W g E n z.1‖ₑ * ‖batchMat W g E 1 z.2‖ₑ) (blockAppend W n 1 ω)
            ∂(μ W (n + 1)) := by
          refine lintegral_mono fun ω => ?_
          beta_reduce
          rw [batchMat_add, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul
            (norm_nonneg _), mul_comm]
          exact ENNReal.ofReal_le_ofReal (norm_mul_le _ _)
      _ = ∫⁻ z, ‖batchMat W g E n z.1‖ₑ * ‖batchMat W g E 1 z.2‖ₑ ∂((μ W n).prod (μ W 1)) :=
          hmp.lintegral_comp hm1
      _ = (∫⁻ x, ‖batchMat W g E n x‖ₑ ∂(μ W n)) * ∫⁻ y, ‖batchMat W g E 1 y‖ₑ ∂(μ W 1) :=
          lintegral_prod_mul (measurable_batchMat W g E n).enorm.aemeasurable
            (measurable_batchMat W g E 1).enorm.aemeasurable
      _ ≤ ENNReal.ofReal ((max 1 g⁻¹ * (1 + |E| + C₁)) ^ n) *
            ENNReal.ofReal (max 1 g⁻¹ * (1 + |E| + C₁)) :=
          mul_le_mul' ih (bbm_lintegral_one_le hC₁ hmom W hg E)
      _ = _ := by rw [← ENNReal.ofReal_mul (pow_nonneg ha n), ← pow_succ]

/-- The bad mass of (8.27) [up:eq:coarse-density]: `𝔼[(1 - χ_q) ‖F‖^{1/2}] ≤ ½` for all large
`W`, uniformly in `W^{-B} ≤ g ≤ W^B`, `|E| ≤ E₀` and in the measurable cutoff `0 ≤ χ ≤ 1` of
the first `1000` inputs with `P(χ ≠ 1) ≤ C e^{-cW}` (Step 1 of Appendix G.5
[sec:c-component-proof]). -/
theorem lintegral_badMass_le (B E₀ c C : ℝ) (hB : 0 < B) (hE₀ : 0 < E₀) (hc : 0 < c)
    (hC : 0 < C) (n : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ χ : Ω W 1000 → ℝ, Measurable χ →
      (∀ ω, 0 ≤ χ ω ∧ χ ω ≤ 1) →
      μ W 1000 {ω | χ ω ≠ 1} ≤ ENNReal.ofReal (C * Real.exp (-c * W)) →
      ∀ g E : ℝ, (W : ℝ) ^ (-B) ≤ g → g ≤ (W : ℝ) ^ B → |E| ≤ E₀ →
        ∫⁻ ω, ENNReal.ofReal ((1 - batchCut W n χ ω) *
            Real.sqrt ‖batchMat W g E (1000 + n) ω‖) ∂(μ W (1000 + n)) ≤
          ENNReal.ofReal (1 / 2) := by
  obtain ⟨C₁, hC₁, hT1⟩ := lintegral_norm_batchMat_le
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 1 + E₀ + C₁ := ⟨_, rfl⟩
  have ha : 0 < a := by rw [ha_def]; positivity
  obtain ⟨W₀, hW₀8, hW₀⟩ := bbm_decay B c C a n (1000 + n) hc hC ha
  refine ⟨W₀, fun W hW χ hχm hχ01 hχA g E hgl hgu hE => ?_⟩
  have hW8 : (8 : ℝ) ≤ W := by exact_mod_cast hW₀8.trans hW
  have hw1 : (1 : ℝ) ≤ W := by linarith
  have hw0 : (0 : ℝ) < W := by linarith
  have hg : 0 < g := lt_of_lt_of_le (Real.rpow_pos_of_pos hw0 _) hgl
  have hh : max 1 g⁻¹ ≤ (W : ℝ) ^ B := by
    refine max_le (Real.one_le_rpow hw1 hB.le) ?_
    calc g⁻¹ ≤ ((W : ℝ) ^ (-B))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hw0 _) hgl
      _ = (W : ℝ) ^ B := by rw [Real.rpow_neg hw0.le, inv_inv]
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ,
      m = C * Real.exp (-c * W) + (n : ℝ) * Real.exp (-((W : ℝ) * W) / 8) := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm_def]; positivity
  obtain ⟨M, hM_def⟩ : ∃ M : ℝ, M = (((W : ℝ) ^ B) * a) ^ (1000 + n) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM_def]; positivity
  have hmM : m * M ≤ 1 / 4 := by rw [hm_def, hM_def]; exact hW₀ W hW
  have hM : ∫⁻ ω, ‖batchMat W g E (1000 + n) ω‖ₑ ∂(μ W (1000 + n)) ≤ ENNReal.ofReal M := by
    refine (hT1 W (1000 + n) g E hg).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hM_def]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    exact mul_le_mul hh (by rw [ha_def]; linarith [(abs_le.1 hE).2]) (by positivity)
      (Real.rpow_nonneg hw0.le _)
  have hA : μ W (1000 + n) {ω | batchCut W n χ ω ≠ 1} ≤ ENNReal.ofReal m :=
    hm_def ▸ measure_batchCut_ne_one_le (by exact_mod_cast hw1) hC.le hχA
  have hmeasA : MeasurableSet {ω : Ω W (1000 + n) | batchCut W n χ ω ≠ 1} :=
    (bbm_measurable_batchCut hχm) (measurableSet_singleton (1 : ℝ)).compl
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = 1 / (2 * m) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hpt : ∀ ω : Ω W (1000 + n),
      ENNReal.ofReal ((1 - batchCut W n χ ω) * Real.sqrt ‖batchMat W g E (1000 + n) ω‖) ≤
        {ω | batchCut W n χ ω ≠ 1}.indicator (fun _ => ENNReal.ofReal (lam / 2)) ω +
          ENNReal.ofReal (1 / (2 * lam)) * ‖batchMat W g E (1000 + n) ω‖ₑ := by
    intro ω
    by_cases hω : batchCut W n χ ω = 1
    · have h0 : (1 - batchCut W n χ ω) * Real.sqrt ‖batchMat W g E (1000 + n) ω‖ = 0 := by
        rw [hω]; ring
      rw [h0, ENNReal.ofReal_zero]
      exact bot_le
    · have hω' : ω ∈ {ω : Ω W (1000 + n) | batchCut W n χ ω ≠ 1} := hω
      rw [Set.indicator_of_mem hω', ← ofReal_norm,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hb := bbm_batchCut_nonneg (fun ω => (hχ01 ω).1) (n := n) ω
      obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ‖batchMat W g E (1000 + n) ω‖ := ⟨_, rfl⟩
      rw [← hx]
      have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
      have hss : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by rw [hx]; exact norm_nonneg _)
      have h1 : Real.sqrt x ≤ lam / 2 + 1 / (2 * lam) * x := by
        have h2 : lam / 2 + 1 / (2 * lam) * Real.sqrt x ^ 2 - Real.sqrt x =
            (Real.sqrt x - lam) ^ 2 / (2 * lam) := by field_simp; ring
        have h3 : 0 ≤ (Real.sqrt x - lam) ^ 2 / (2 * lam) := by positivity
        rw [hss] at h2
        linarith
      nlinarith [mul_nonneg hb hs]
  calc ∫⁻ ω, ENNReal.ofReal ((1 - batchCut W n χ ω) *
          Real.sqrt ‖batchMat W g E (1000 + n) ω‖) ∂(μ W (1000 + n))
      ≤ ∫⁻ ω, ({ω | batchCut W n χ ω ≠ 1}.indicator (fun _ => ENNReal.ofReal (lam / 2)) ω +
          ENNReal.ofReal (1 / (2 * lam)) * ‖batchMat W g E (1000 + n) ω‖ₑ)
            ∂(μ W (1000 + n)) := lintegral_mono hpt
    _ = ENNReal.ofReal (lam / 2) * μ W (1000 + n) {ω | batchCut W n χ ω ≠ 1} +
          ENNReal.ofReal (1 / (2 * lam)) *
            ∫⁻ ω, ‖batchMat W g E (1000 + n) ω‖ₑ ∂(μ W (1000 + n)) := by
        rw [lintegral_add_left (measurable_const.indicator hmeasA),
          lintegral_indicator_const hmeasA, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (lam / 2) * ENNReal.ofReal m +
          ENNReal.ofReal (1 / (2 * lam)) * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (lam / 2 * m + 1 / (2 * lam) * M) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (show 0 ≤ lam / 2 by positivity),
          ENNReal.ofReal_mul (show 0 ≤ 1 / (2 * lam) by positivity)]
    _ ≤ ENNReal.ofReal (1 / 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : lam / 2 * m = 1 / 4 := by rw [hlam]; field_simp; norm_num
        have h2 : 1 / (2 * lam) * M = m * M := by rw [hlam]; field_simp
        rw [h1, h2]
        linarith

end LSBA
