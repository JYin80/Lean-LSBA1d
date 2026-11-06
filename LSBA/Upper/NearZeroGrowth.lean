import LSBA.Upper.CenterCorrector
import LSBA.Upper.NearZeroStep
import LSBA.Transfer.ChainProduct

/-!
# Scalar growth near zero energy

Lemma 11.10 [lg:lem:scalar-growth], (11.71) [lg:eq:scalar-growth]: for `0 < ε < B_g` and `D > 0`
there are an energy window and `C_D` such that for every `C_1 ≥ C_D`, all large `W`,
`W^ε ≤ g < W^{B_g}`, `|E|` in the window and every state `(C_0, v_0)`, the additive growth (11.8)
[lg:eq:additive-growth] at the length `n = ⌈C_1 W g² log W⌉` satisfies
`P(ℓ_n(C_0, v_0) < D log W) ≤ W^{−D}`.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Measurability of the observables, the blocks and the chain -/

private lemma nzg_cont_vecForm {W : ℕ} :
    Continuous fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) => vecForm q.1 q.2 := by
  have hc : Continuous (fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) =>
      Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) q.1 q.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM
  exact continuous_snd.inner hc

private lemma nzg_measurable_inv {W : ℕ} :
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

private lemma nzg_measurable_zpow {W : ℕ} (k : ℤ) :
    Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A ^ k := by
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact (continuous_id.pow n).measurable
  | negSucc n =>
    simp only [zpow_negSucc]
    exact nzg_measurable_inv.comp (continuous_id.pow _).measurable

private lemma nzg_measurable_obsEval (g : ℝ) (W : ℕ) (p : ObsPoly) :
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
        ((nzg_measurable_zpow k.1).comp measurable_fst))
    | f k =>
      simp only [obsEval, aeval_X, obsF]
      have h1 : Measurable fun X : State W => (X.1 ^ k.1, X.2) :=
        ((nzg_measurable_zpow k.1).comp measurable_fst).prodMk measurable_snd
      have h2 := (nzg_cont_vecForm (W := W)).measurable.comp h1
      exact h2
    | w => simp only [obsEval, aeval_X]; exact measurable_const
    | γ => simp only [obsEval, aeval_X]; exact measurable_const

private lemma nzg_measurable_corrQ (g E : ℝ) (R : ℕ) (Ks : Finset NzInt) (q : NzInt → ℂ)
    (W : ℕ) : Measurable fun X : State W => corrQ g E R Ks q X := by
  unfold corrQ
  exact Complex.measurable_re.comp (Finset.measurable_sum _ fun k _ =>
    measurable_const.mul (nzg_measurable_obsEval g W _))

/-- The good set of (11.44) [lg:eq:burnevent] at one time is measurable. -/
private lemma nzg_measurableSet_good (g E : ℝ) (R : ℕ) (Ks : Finset NzInt) (η : ℝ) (W : ℕ) :
    MeasurableSet {X : State W | corrGood g E R Ks η X} := by
  have h : {X : State W | corrGood g E R Ks η X} = ⋂ k ∈ Ks,
      ({X : State W | ‖obsEval g X (corrObsM E R k) - center g E R k.1‖ ≤ (W : ℝ) ^ (η - 1)} ∩
        {X : State W | ‖obsEval g X (corrObsF E R k)‖ ≤ (W : ℝ) ^ (η - 1 / 2)}) := by
    ext X
    simp only [corrGood, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [h]
  refine Finset.measurableSet_biInter Ks fun k _ => ?_
  exact (measurableSet_le ((nzg_measurable_obsEval g W _).sub_const _).norm
    measurable_const).inter (measurableSet_le (nzg_measurable_obsEval g W _).norm measurable_const)

private lemma nzg_measurable_gb (W L : ℕ) (a : Fin L) :
    Measurable fun ω : Ω W L => gueBlock W L ω a := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The blocks of a sample of `n` blocks as a sequence, padded by `0`. -/
private def nzgBlocks {W : ℕ} (n : ℕ) (ω : Ω W n) : ℕ → Matrix (Fin W) (Fin W) ℂ :=
  fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0

private lemma nzg_measurable_block (W n i : ℕ) :
    Measurable fun ω : Ω W n => nzgBlocks n ω i := by
  unfold nzgBlocks
  by_cases h : i < n
  · simp only [h, dite_true]
    exact nzg_measurable_gb W n ⟨i, h⟩
  · simp only [h, dite_false]
    exact measurable_const

private lemma nzg_herm {W n : ℕ} (ω : Ω W n) (k : ℕ) : (nzgBlocks n ω k).IsHermitian := by
  unfold nzgBlocks
  split_ifs
  · exact gueBlock_isHermitian W n ω _
  · exact Matrix.isHermitian_zero

private lemma nzg_measurable_chain (g E : ℝ) {W : ℕ} (X₀ : State W) (n i : ℕ) :
    Measurable fun ω : Ω W n => chainState g E X₀ (nzgBlocks n ω) i := by
  induction i with
  | zero => exact measurable_const
  | succ i ih =>
    have h := (measurable_stepState g E W).comp (ih.prodMk (nzg_measurable_block W n i))
    exact h

private lemma nzg_isState_chain (g E : ℝ) {W : ℕ} {X₀ : State W} (hX₀ : IsState X₀) {n : ℕ}
    (ω : Ω W n) (i : ℕ) : IsState (chainState g E X₀ (nzgBlocks n ω) i) := by
  induction i with
  | zero => exact hX₀
  | succ i ih => exact isState_stepState g E ih (nzg_herm ω i)

/-! ### The factors of the exponential product -/

/-- The exponent of the factor at time `i`: `−s c` before `n_*`; after `n_*`, `−s(c − Q(X') + Q(X))`
on the good set and the constant `−s (48 W g²)⁻¹` off it. -/
private def nzgExp (g E s : ℝ) (R : ℕ) (Ks : Finset NzInt) (q : NzInt → ℂ) (η : ℝ) {W : ℕ}
    (ns i : ℕ) (X : State W) (V : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  if i < ns then -(s * stepInc g E X V)
  else if corrGood g E R Ks η X then
    -(s * (stepInc g E X V - corrQ g E R Ks q (stepState g E X V) + corrQ g E R Ks q X))
  else -(s / (48 * W * g ^ 2))

private lemma nzg_measurable_exp (g E s : ℝ) (R : ℕ) (Ks : Finset NzInt) (q : NzInt → ℂ)
    (η : ℝ) (W ns i : ℕ) :
    Measurable fun p : State W × Matrix (Fin W) (Fin W) ℂ =>
      nzgExp g E s R Ks q η ns i p.1 p.2 := by
  have hc := measurable_stepInc g E W
  have hQ := nzg_measurable_corrQ g E R Ks q W
  unfold nzgExp
  by_cases hi : i < ns
  · simp only [hi, ↓reduceIte]
    exact (measurable_const.mul hc).neg
  · simp only [hi, ↓reduceIte]
    refine Measurable.ite (p := fun p : State W × Matrix (Fin W) (Fin W) ℂ =>
      corrGood g E R Ks η p.1) ?_ ?_ measurable_const
    · exact measurable_fst (nzg_measurableSet_good g E R Ks η W)
    · exact (measurable_const.mul ((hc.sub (hQ.comp (measurable_stepState g E W))).add
        (hQ.comp measurable_fst))).neg

/-! ### Elementary bounds -/

/-- `h_θ² ≥ 1/4` for `|E| ≤ 1`, with `h_θ` of (11.1) [lg:eq:normal]. -/
private lemma nzg_normalH_sq {E : ℝ} (hE : |E| ≤ 1) : 1 / 4 ≤ normalH E ^ 2 := by
  obtain ⟨h1, h2⟩ := abs_le.mp hE
  have hx : (E / 2) ^ 2 ≤ 1 / 4 := by nlinarith
  have hpos : 0 < 1 - (E / 2) ^ 2 := by linarith
  have h0 : 0 < √(1 - (E / 2) ^ 2) := Real.sqrt_pos.mpr hpos
  have hs1 : √(1 - (E / 2) ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg (E / 2)])
  have hh : 1 / 2 ≤ normalH E := by
    simp only [normalH, freeAngle, Real.sin_arccos]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    exact inv_anti₀ (by positivity) (by linarith)
  nlinarith

/-- The horizon: `C_1 W g² log W + 1 ≤ W^{2 + 2B_g}` when `W ≥ (2C_1 + 1)²` and
`1 ≤ g < W^{B_g}`. -/
private lemma nzg_horizon {C₁ W g Bg : ℝ} (hC₁ : 0 ≤ C₁) (hW : (2 * C₁ + 1) ^ 2 ≤ W)
    (hW1 : 1 ≤ W) (hg : 1 ≤ g) (hgB : g < W ^ Bg) :
    C₁ * W * g ^ 2 * Real.log W + 1 ≤ W ^ (2 + 2 * Bg) := by
  have hW0 : 0 < W := by linarith
  have hsq := Real.mul_self_sqrt hW0.le
  have hs1 : 2 * C₁ + 1 ≤ √W := (Real.le_sqrt (by positivity) hW0.le).mpr hW
  have hLs : Real.log W ≤ 2 * √W - 2 := by
    have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hW0)
    rw [Real.log_sqrt hW0.le] at this
    linarith
  have hL0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  have hCL : C₁ * Real.log W + 1 ≤ W := by
    have a : C₁ * Real.log W ≤ C₁ * (2 * √W - 2) := mul_le_mul_of_nonneg_left hLs hC₁
    have b : (2 * C₁ + 1) * √W ≤ √W * √W := mul_le_mul_of_nonneg_right hs1 (Real.sqrt_nonneg _)
    nlinarith
  have hWg : 1 ≤ W * g ^ 2 := by nlinarith
  have hpow : W ^ (2 + 2 * Bg) = W ^ 2 * (W ^ Bg) ^ 2 := by
    rw [Real.rpow_add hW0, show (2 : ℝ) * Bg = Bg * 2 by ring, Real.rpow_mul hW0.le]
    norm_cast
  have hg2 : g ^ 2 ≤ (W ^ Bg) ^ 2 := pow_le_pow_left₀ (by linarith) hgB.le 2
  calc C₁ * W * g ^ 2 * Real.log W + 1 ≤ (C₁ * Real.log W + 1) * (W * g ^ 2) := by nlinarith
    _ ≤ W * (W * g ^ 2) := mul_le_mul_of_nonneg_right hCL (by positivity)
    _ ≤ W * (W * (W ^ Bg) ^ 2) := by gcongr
    _ = W ^ (2 + 2 * Bg) := by rw [hpow]; ring

/-- The Markov exponent: with `C_1 ≥ C_D = C_s + 48(D + (K C_s + D + 1)/s)`, `n ≥ C_1 W g² L`,
`n_* ≤ C_s g² L + 1` and `L ≥ K + 2C_Q + 2`,
`n_* K g⁻² − (n − n_*) s (48 W g²)⁻¹ + s D L + 2 s C_Q ≤ −D L − log 2`. -/
private lemma nzg_exponent {K Cs CQ s D C₁ W g L ns n : ℝ} (hK : 0 < K) (hCs : 0 < Cs)
    (hCQ : 0 < CQ) (hs0 : 0 < s) (hs1 : s ≤ 1) (hD : 0 < D)
    (hC₁ : Cs + 48 * (D + (K * Cs + D + 1) / s) ≤ C₁) (hW : 1 ≤ W) (hg : 1 ≤ g)
    (hL : K + 2 * CQ + 2 ≤ L) (hns : ns ≤ Cs * g ^ 2 * L + 1) (hn : C₁ * W * g ^ 2 * L ≤ n) :
    ns * (K / g ^ 2) + (n - ns) * (-(s / (48 * W * g ^ 2))) + (s * D * L + 2 * s * CQ) ≤
      -(D * L) - Real.log 2 := by
  have hg2 : 1 ≤ g ^ 2 := by nlinarith
  have hg0 : 0 < g ^ 2 := by linarith
  have hW0 : 0 < W := by linarith
  have hL0 : 0 ≤ L := by linarith
  have h1 : ns * (K / g ^ 2) ≤ K * Cs * L + K := by
    have a : ns * (K / g ^ 2) ≤ (Cs * g ^ 2 * L + 1) * (K / g ^ 2) :=
      mul_le_mul_of_nonneg_right hns (by positivity)
    have e : (Cs * g ^ 2 * L + 1) * (K / g ^ 2) = K * Cs * L + K / g ^ 2 := by
      field_simp
    have b : K / g ^ 2 ≤ K := div_le_self hK.le hg2
    linarith
  have h2 : s * C₁ * L / 48 - s * Cs * L / 48 - 1 / 48 ≤ (n - ns) * (s / (48 * W * g ^ 2)) := by
    have hC0 : 0 ≤ C₁ := by
      have : 0 ≤ (K * Cs + D + 1) / s := by positivity
      linarith
    have hWC : C₁ * g ^ 2 * L ≤ C₁ * W * g ^ 2 * L := by
      have : C₁ * g ^ 2 * L * 1 ≤ C₁ * g ^ 2 * L * W :=
        mul_le_mul_of_nonneg_left hW (by positivity)
      linarith
    have hnn : C₁ * W * g ^ 2 * L - Cs * g ^ 2 * L - 1 ≤ n - ns := by linarith
    have a : (C₁ * W * g ^ 2 * L - Cs * g ^ 2 * L - 1) * (s / (48 * W * g ^ 2)) ≤
        (n - ns) * (s / (48 * W * g ^ 2)) := mul_le_mul_of_nonneg_right hnn (by positivity)
    have e : (C₁ * W * g ^ 2 * L - Cs * g ^ 2 * L - 1) * (s / (48 * W * g ^ 2)) =
        s * C₁ * L / 48 - s * Cs * L / (48 * W) - s / (48 * W * g ^ 2) := by
      field_simp
    have a1 : s * Cs * L / (48 * W) ≤ s * Cs * L / 48 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    have a2 : s / (48 * W * g ^ 2) ≤ 1 / 48 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 1 ≤ W * g ^ 2 := by nlinarith
      nlinarith
    linarith
  have h3 : s * D + K * Cs + D + 1 ≤ s * (C₁ - Cs) / 48 := by
    have a : 48 * (D + (K * Cs + D + 1) / s) ≤ C₁ - Cs := by linarith
    have e : s * (48 * (D + (K * Cs + D + 1) / s)) / 48 = s * D + K * Cs + D + 1 := by
      field_simp
      ring
    have b := mul_le_mul_of_nonneg_left a hs0.le
    have c := div_le_div_of_nonneg_right b (by norm_num : (0 : ℝ) ≤ 48)
    linarith
  have h4 : (s * D + K * Cs + D + 1) * L ≤ s * (C₁ - Cs) / 48 * L :=
    mul_le_mul_of_nonneg_right h3 hL0
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  have h5 : 2 * s * CQ ≤ 2 * CQ := by nlinarith
  have e2 : (n - ns) * (-(s / (48 * W * g ^ 2))) = -((n - ns) * (s / (48 * W * g ^ 2))) := by
    ring
  rw [e2]
  nlinarith

/-- `W^{−(D+1)} + e^A ≤ W^{−D}` in exponential form, when `L ≥ 2` and `A ≤ −D L − log 2`. -/
private lemma nzg_prob {D L A : ℝ} (hL : 2 ≤ L) (hA : A ≤ -(D * L) - Real.log 2) :
    Real.exp (L * (-(D + 1))) + Real.exp A ≤ Real.exp (L * (-D)) := by
  have e1 : Real.exp (L * (-(D + 1))) = Real.exp (L * (-D)) * Real.exp (-L) := by
    rw [← Real.exp_add]
    ring_nf
  have e2 : Real.exp (-(D * L) - Real.log 2) = Real.exp (L * (-D)) / 2 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num), show -(D * L) = L * (-D) by ring]
  have h1 : Real.exp A ≤ Real.exp (L * (-D)) / 2 := e2 ▸ Real.exp_le_exp.mpr hA
  have h2 : Real.exp (-L) * 2 ≤ 1 := by
    have hm : Real.exp (-L) * Real.exp L = 1 := by rw [← Real.exp_add]; simp
    have := Real.add_one_le_exp L
    have hp := Real.exp_pos (-L)
    nlinarith
  have hp := Real.exp_pos (L * (-D))
  rw [e1]
  nlinarith

/-- Lemma 11.10 [lg:lem:scalar-growth], (11.71) [lg:eq:scalar-growth]. -/
theorem scalar_growth {ε Bg : ℝ} (hε : 0 < ε) (hεB : ε < Bg) {D : ℝ} (hD : 0 < D) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ CD : ℝ, 0 < CD ∧ ∀ C₁ : ℝ, CD ≤ C₁ → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ g : ℝ, (W : ℝ) ^ ε ≤ g → g < (W : ℝ) ^ Bg → ∀ E : ℝ, |E| ≤ E₁ →
        ∀ X₀ : State W, IsState X₀ → ∀ n : ℕ, n = ⌈C₁ * W * g ^ 2 * Real.log W⌉₊ →
          μ W n {ω | ellN g E X₀.1 X₀.2
              (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n < D * Real.log W} ≤
            ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  set η : ℝ := min ε (1 / 4) / 2 with hηdef
  have hm0 : 0 < min ε (1 / 4) := lt_min hε (by norm_num)
  have hη0 : 0 < η := half_pos hm0
  have hη : η < min ε (1 / 4) := half_lt_self hm0
  obtain ⟨R, Ks, q, Ec, hEc, Cs, CQ, hCs, hCQ, Wc, hcc⟩ :=
    center_corrector hε hεB (D := D + 1) (B₁ := 2 + 2 * Bg) (by linarith) (by linarith) hη0 hη
  obtain ⟨s, hs0, hs1, Es, hEs, Ws, hstep⟩ := corrStep_mgf_le hε R Ks hCQ
  obtain ⟨K, hK, hinc⟩ := incStep_mgf_le
  refine ⟨min (min Ec Es) 1, lt_min (lt_min hEc hEs) one_pos,
    Cs + 48 * (D + (K * Cs + D + 1) / s), by positivity, fun C₁ hC₁ => ?_⟩
  refine ⟨max (max Wc Ws) (max ⌈(2 * C₁ + 1) ^ 2⌉₊ ⌈Real.exp (K + 2 * CQ + 2)⌉₊), ?_⟩
  intro W hW g hg hgB E hE X₀ hX₀ n hn
  -- the thresholds
  have hWc : Wc ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWs : Ws ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWsq : (2 * C₁ + 1) ^ 2 ≤ (W : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW)
  have hWe : Real.exp (K + 2 * CQ + 2) ≤ (W : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW)
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le (Real.exp_pos _) hWe
  have hL : K + 2 * CQ + 2 ≤ Real.log W := by
    rw [← Real.log_exp (K + 2 * CQ + 2)]
    exact Real.log_le_log (Real.exp_pos _) hWe
  have hW1r : (1 : ℝ) ≤ W := by
    have := Real.add_one_le_exp (K + 2 * CQ + 2)
    linarith
  have hW1 : 1 ≤ W := by exact_mod_cast hW1r
  have hg1 : 1 ≤ g := (Real.one_le_rpow hW1r hε.le).trans hg
  have hg0 : 0 < g ^ 2 := by positivity
  have hE1 : |E| ≤ 1 := hE.trans (min_le_right _ _)
  have hEc' : |E| ≤ Ec := hE.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hEs' : |E| ≤ Es := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hCD0 : 0 ≤ (K * Cs + D + 1) / s := by positivity
  have hC48 : Cs + 48 ≤ C₁ := by
    have : 1 ≤ (K * Cs + D + 1) / s := by
      rw [le_div_iff₀ hs0]
      nlinarith
    linarith
  have hC₁0 : 0 ≤ C₁ := by linarith
  obtain ⟨hsum, hQb, -, hdr, hbad⟩ := hcc W hWc g hg hgB E hEc'
  set L : ℝ := Real.log W with hLdef
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨ns, hnsdef⟩ : ∃ m : ℕ, m = ⌈Cs * g ^ 2 * L⌉₊ := ⟨_, rfl⟩
  have hns : (ns : ℝ) ≤ Cs * g ^ 2 * L + 1 := by
    rw [hnsdef]; exact (Nat.ceil_lt_add_one (mul_nonneg (by positivity) hL0)).le
  have hnr : C₁ * W * g ^ 2 * L ≤ n := by rw [hn]; exact Nat.le_ceil _
  have hnle : (n : ℝ) ≤ C₁ * W * g ^ 2 * L + 1 := by
    rw [hn]; exact (Nat.ceil_lt_add_one (mul_nonneg (by positivity) hL0)).le
  have hnsn : ns ≤ n := by
    have h48 : (Cs + 48) * g ^ 2 * L ≤ C₁ * W * g ^ 2 * L := by
      have : (Cs + 48) * 1 ≤ C₁ * W := mul_le_mul hC48 hW1r zero_le_one hC₁0
      have h' := mul_le_mul_of_nonneg_right this (mul_nonneg hg0.le hL0)
      nlinarith
    have hgL : 2 ≤ g ^ 2 * L := by nlinarith
    have : (ns : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hhor : (n : ℝ) ≤ (W : ℝ) ^ (2 + 2 * Bg) :=
    hnle.trans (nzg_horizon hC₁0 hWsq hW1r hg1 hgB)
  -- the factors and the one-step bounds
  set Zf : ℕ → State W → Matrix (Fin W) (Fin W) ℂ → ℝ≥0∞ := fun i X V =>
    ENNReal.ofReal (Real.exp (nzgExp g E s R Ks (q g E) (η / 2) ns i X V)) with hZf
  set r : ℕ → ℝ := fun i => if i < ns then K / g ^ 2 else -(s / (48 * W * g ^ 2)) with hr
  have hZm : ∀ i, Measurable (fun p : State W × Matrix (Fin W) (Fin W) ℂ => Zf i p.1 p.2) :=
    fun i => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (nzg_measurable_exp g E s R Ks (q g E) (η / 2) W ns i))
  have hq : ∀ i, ∀ X : State W, IsState X →
      ∫⁻ ω, Zf i X (gueBlock W 1 ω 0) ∂(μ W 1) ≤ ENNReal.ofReal (Real.exp (r i)) := by
    intro i X hX
    by_cases hi : i < ns
    · simp only [hZf, hr, nzgExp, hi, ↓reduceIte]
      exact hinc W hW1 g hg1 E hE1 X hX s hs0.le hs1
    · by_cases hG : corrGood g E R Ks (η / 2) X
      · simp only [hZf, hr, nzgExp, hi, hG, ↓reduceIte]
        refine hstep W hWs g hg E hEs' (q g E) hsum X hX ?_
        have hd := (abs_le.mp (hdr X hX hG)).1
        have hh := nzg_normalH_sq hE1
        have hP : 0 < (W : ℝ) * g ^ 2 := by positivity
        have e1 : normalH E ^ 2 / (2 * W * g ^ 2) - normalH E ^ 2 / (6 * W * g ^ 2) =
            normalH E ^ 2 / (3 * W * g ^ 2) := by
          field_simp
          ring
        have e2 : 1 / (12 * W * g ^ 2) ≤ normalH E ^ 2 / (3 * W * g ^ 2) := by
          rw [show (1 : ℝ) / (12 * W * g ^ 2) = (1 / 4) / (3 * W * g ^ 2) by
            field_simp; ring]
          exact div_le_div_of_nonneg_right hh (by positivity)
        linarith
      · simp only [hZf, hr, nzgExp, hi, hG, ↓reduceIte]
        rw [lintegral_const, measure_univ, mul_one]
  have hprod := lintegral_prodSeq_chainState_le g E Zf hZm
    (fun i => ENNReal.ofReal (Real.exp (r i))) hq hX₀ n
  -- the sum of the one-step exponents
  have hrsum : ∑ i ∈ Finset.range n, r i =
      ns * (K / g ^ 2) + (n - ns) * (-(s / (48 * W * g ^ 2))) := by
    rw [← Finset.sum_range_add_sum_Ico _ hnsn]
    have a : ∑ i ∈ Finset.range ns, r i = ∑ i ∈ Finset.range ns, K / g ^ 2 :=
      Finset.sum_congr rfl fun i hi => by simp [hr, Finset.mem_range.mp hi]
    have b : ∑ i ∈ Finset.Ico ns n, r i = ∑ i ∈ Finset.Ico ns n, -(s / (48 * W * g ^ 2)) :=
      Finset.sum_congr rfl fun i hi => by
        simp [hr, not_lt.mpr (Finset.mem_Ico.mp hi).1]
    rw [a, b, Finset.sum_const, Finset.sum_const, Finset.card_range, Nat.card_Ico,
      nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub hnsn]
  have hqprod : ∏ i ∈ Finset.range n, ENNReal.ofReal (Real.exp (r i)) =
      ENNReal.ofReal (Real.exp (ns * (K / g ^ 2) + (n - ns) * (-(s / (48 * W * g ^ 2))))) := by
    rw [← hrsum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
  -- the pointwise lower bound off the bad event
  set t : ℝ := Real.exp (-(s * D * L + 2 * s * CQ)) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have hE2 : |E| < 2 := by linarith
  have hsub : {ω | ellN g E X₀.1 X₀.2
      (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n < D * L} ⊆
      {ω | ∃ m : ℕ, ns ≤ m ∧ m ≤ n ∧
          ¬ corrGood g E R Ks (η / 2) (chainState g E X₀
            (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) m)} ∪
        {ω | ENNReal.ofReal t ≤ ∏ i ∈ Finset.range n,
          Zf i (chainState g E X₀ (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) i)
            (if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0)} := by
    intro ω hω
    by_cases hb : ∃ m : ℕ, ns ≤ m ∧ m ≤ n ∧
        ¬ corrGood g E R Ks (η / 2) (chainState g E X₀
          (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) m)
    · exact Or.inl hb
    refine Or.inr ?_
    push Not at hb
    change ellN g E X₀.1 X₀.2 (nzgBlocks n ω) n < D * L at hω
    change ∀ m, ns ≤ m → m ≤ n → corrGood g E R Ks (η / 2)
      (chainState g E X₀ (nzgBlocks n ω) m) at hb
    change ENNReal.ofReal t ≤ ∏ i ∈ Finset.range n,
      Zf i (chainState g E X₀ (nzgBlocks n ω) i) (nzgBlocks n ω i)
    rw [ellN_eq_sum hE2 g hX₀ (nzg_herm ω) n] at hω
    set Xc : ℕ → State W := fun i => chainState g E X₀ (nzgBlocks n ω) i with hXc
    set c : ℕ → ℝ := fun i => stepInc g E (Xc i) (nzgBlocks n ω i) with hc
    set Qc : ℕ → ℝ := fun i => corrQ g E R Ks (q g E) (Xc i) with hQc
    change ∑ i ∈ Finset.range n, c i < D * L at hω
    change ∀ m, ns ≤ m → m ≤ n → corrGood g E R Ks (η / 2) (Xc m) at hb
    change ENNReal.ofReal t ≤ ∏ i ∈ Finset.range n, Zf i (Xc i) (nzgBlocks n ω i)
    simp only [hZf]
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le, ← Real.exp_sum]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have h1 : ∀ i ∈ Finset.range ns,
        nzgExp g E s R Ks (q g E) (η / 2) ns i (Xc i) (nzgBlocks n ω i) = -(s * c i) := by
      intro i hi
      unfold nzgExp
      simp only [Finset.mem_range.mp hi, ↓reduceIte]
      rfl
    have h2 : ∀ i ∈ Finset.Ico ns n,
        nzgExp g E s R Ks (q g E) (η / 2) ns i (Xc i) (nzgBlocks n ω i) =
          -(s * c i) + s * (Qc (i + 1) - Qc i) := by
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
      have hG := hb i hi1 hi2.le
      unfold nzgExp
      simp only [not_lt.mpr hi1, hG, ↓reduceIte]
      change _ = -(s * stepInc g E (Xc i) (nzgBlocks n ω i)) +
        s * (corrQ g E R Ks (q g E) (stepState g E (Xc i) (nzgBlocks n ω i)) -
          corrQ g E R Ks (q g E) (Xc i))
      ring
    have hsplit : ∑ i ∈ Finset.range n,
        nzgExp g E s R Ks (q g E) (η / 2) ns i (Xc i) (nzgBlocks n ω i) =
        -(s * ∑ i ∈ Finset.range n, c i) + s * (Qc n - Qc ns) := by
      have htel : ∑ i ∈ Finset.Ico ns n, (Qc (i + 1) - Qc i) = Qc n - Qc ns := by
        rw [Finset.sum_Ico_eq_sub _ hnsn, Finset.sum_range_sub, Finset.sum_range_sub]
        ring
      have hcs : ∑ i ∈ Finset.range n, c i =
          ∑ i ∈ Finset.range ns, c i + ∑ i ∈ Finset.Ico ns n, c i :=
        (Finset.sum_range_add_sum_Ico c hnsn).symm
      rw [← Finset.sum_range_add_sum_Ico _ hnsn, Finset.sum_congr rfl h1, Finset.sum_congr rfl h2,
        Finset.sum_add_distrib, ← Finset.mul_sum, htel, hcs]
      simp only [Finset.sum_neg_distrib, ← Finset.mul_sum]
      ring
    rw [hsplit]
    have hQn : |Qc n| ≤ CQ / g ^ 2 := hQb (Xc n) (nzg_isState_chain g E hX₀ ω n)
    have hQns : |Qc ns| ≤ CQ / g ^ 2 := hQb (Xc ns) (nzg_isState_chain g E hX₀ ω ns)
    have hCQg : CQ / g ^ 2 ≤ CQ := div_le_self hCQ.le (one_le_pow₀ hg1)
    have hQd : -(2 * CQ) ≤ Qc n - Qc ns := by
      have a := (abs_le.mp hQn).1
      have b := (abs_le.mp hQns).2
      linarith
    have hl : s * ∑ i ∈ Finset.range n, c i ≤ s * (D * L) :=
      mul_le_mul_of_nonneg_left hω.le hs0.le
    have hs2 : s * (-(2 * CQ)) ≤ s * (Qc n - Qc ns) := mul_le_mul_of_nonneg_left hQd hs0.le
    have e : -(s * D * L + 2 * s * CQ) = -(s * (D * L)) + s * (-(2 * CQ)) := by ring
    rw [e]
    exact add_le_add (neg_le_neg hl) hs2
  -- Markov's inequality and the bad event
  have hmeas : AEMeasurable (fun ω : Ω W n => ∏ i ∈ Finset.range n,
      Zf i (chainState g E X₀ (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) i)
        (if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0)) (μ W n) := by
    change AEMeasurable (fun ω : Ω W n => ∏ i ∈ Finset.range n,
      Zf i (chainState g E X₀ (nzgBlocks n ω) i) (nzgBlocks n ω i)) (μ W n)
    refine Measurable.aemeasurable ?_
    refine Finset.measurable_prod
      (f := fun i ω => Zf i (chainState g E X₀ (nzgBlocks n ω) i) (nzgBlocks n ω i)) _
      fun i _ => ?_
    exact Measurable.comp (g := fun p : State W × Matrix (Fin W) (Fin W) ℂ => Zf i p.1 p.2)
      (f := fun ω : Ω W n => (chainState g E X₀ (nzgBlocks n ω) i, nzgBlocks n ω i)) (hZm i)
      ((nzg_measurable_chain g E X₀ n i).prodMk (nzg_measurable_block W n i))
  have hmk := meas_ge_le_lintegral_div hmeas (ε := ENNReal.ofReal t)
    (ENNReal.ofReal_pos.mpr ht0).ne' ENNReal.ofReal_ne_top
  have hbad' := hbad X₀ hX₀ n hhor
  rw [← hnsdef] at hbad'
  have hexp := nzg_exponent hK hCs hCQ hs0 hs1 hD hC₁ hW1r hg1 hL hns hnr
  have hfin := nzg_prob (A := ns * (K / g ^ 2) + (n - ns) * (-(s / (48 * W * g ^ 2))) +
    (s * D * L + 2 * s * CQ)) (by linarith) hexp
  have hdiv : ENNReal.ofReal (Real.exp (ns * (K / g ^ 2) + (n - ns) * (-(s / (48 * W * g ^ 2))))) /
      ENNReal.ofReal t = ENNReal.ofReal (Real.exp (ns * (K / g ^ 2) +
        (n - ns) * (-(s / (48 * W * g ^ 2))) + (s * D * L + 2 * s * CQ))) := by
    rw [← ENNReal.ofReal_div_of_pos ht0, ht, ← Real.exp_sub]
    congr 2
    ring
  calc μ W n {ω | ellN g E X₀.1 X₀.2
          (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n < D * L}
      ≤ μ W n {ω | ∃ m : ℕ, ns ≤ m ∧ m ≤ n ∧
          ¬ corrGood g E R Ks (η / 2) (chainState g E X₀
            (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) m)} +
        μ W n {ω | ENNReal.ofReal t ≤ ∏ i ∈ Finset.range n,
          Zf i (chainState g E X₀ (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) i)
            (if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0)} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) +
        ENNReal.ofReal (Real.exp (ns * (K / g ^ 2) + (n - ns) * (-(s / (48 * W * g ^ 2))) +
          (s * D * L + 2 * s * CQ))) := by
        gcongr
        refine hmk.trans ?_
        rw [← hdiv, ← hqprod]
        gcongr
    _ = ENNReal.ofReal (Real.exp (L * (-(D + 1))) +
        Real.exp (ns * (K / g ^ 2) + (n - ns) * (-(s / (48 * W * g ^ 2))) +
          (s * D * L + 2 * s * CQ))) := by
        rw [ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
          Real.rpow_def_of_pos hW0]
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
        rw [Real.rpow_def_of_pos hW0]
        exact ENNReal.ofReal_le_ofReal hfin

end LSBA
