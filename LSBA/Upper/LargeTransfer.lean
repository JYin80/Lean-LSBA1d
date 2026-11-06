import LSBA.Upper.LargeMGF
import LSBA.Transfer.NormalComparison
import LSBA.Transfer.Transition
import LSBA.Upper.ConversionEndpoint

/-!
# Negative transfer moments at large coupling

(11.24) [uvg:eq:scalarfraction]: `𝔼 e^{−sℓ_n} ≤ C e^{−cn/(Wg²)}` for every state and every `n`; and
Theorem 11.1 [uvg:thm:transfer]: for `g ≥ C_*√W`, `𝔼‖D_n(Φ; E)⁻¹‖^s ≤ C W e^{−cn/(Wg²)}` uniformly
in `|E| ≤ E₀ < 2` and in deterministic boundary frames.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Measurability of the chain and of `Y` -/

/-- Matrix inversion is measurable (the adjugate formula, with `0⁻¹ = 0` on singular matrices). -/
private lemma lt_measurable_inv {W : ℕ} :
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

private lemma lt_measurable_zpow {W : ℕ} (k : ℤ) :
    Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A ^ k := by
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact (continuous_id.pow n).measurable
  | negSucc n =>
    simp only [zpow_negSucc]
    exact lt_measurable_inv.comp (continuous_id.pow _).measurable

private lemma lt_measurable_obsM (W : ℕ) (k : ℤ) : Measurable fun X : State W => obsM k X :=
  measurable_const.mul ((continuous_id.matrix_trace).measurable.comp
    ((lt_measurable_zpow k).comp measurable_fst))

private lemma lt_cont_vecForm {W : ℕ} :
    Continuous fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) => vecForm q.1 q.2 := by
  have hc : Continuous (fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) =>
      Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) q.1 q.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM
  exact continuous_snd.inner hc

private lemma lt_measurable_obsF (W : ℕ) (k : ℤ) : Measurable fun X : State W => obsF k X := by
  unfold obsF
  have h1 : Measurable fun X : State W => (X.1 ^ k, X.2) :=
    ((lt_measurable_zpow k).comp measurable_fst).prodMk measurable_snd
  have h2 := (lt_cont_vecForm (W := W)).measurable.comp h1
  exact h2

private lemma lt_measurable_driftCorr (g E A B : ℝ) (W : ℕ) :
    Measurable fun X : State W => driftCorr g E A B X := by
  have m1 := lt_measurable_obsM W 1
  have m2 := lt_measurable_obsM W 2
  have f1 := lt_measurable_obsF W 1
  have f2 := lt_measurable_obsF W 2
  have f3 := lt_measurable_obsF W (-1)
  unfold driftCorr linCorr corrM corrF
  fun_prop

private lemma lt_measurable_driftY (g E A B : ℝ) (W : ℕ) :
    Measurable fun p : State W × Matrix (Fin W) (Fin W) ℂ => driftY g E A B p.1 p.2 := by
  unfold driftY
  have hQ := lt_measurable_driftCorr g E A B W
  exact (((measurable_stepInc g E W).sub (hQ.comp (measurable_stepState g E W))).add
    (hQ.comp measurable_fst))

private lemma lt_measurable_gueBlock (W L : ℕ) (a : Fin L) :
    Measurable fun ω : Ω W L => gueBlock W L ω a := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The blocks of a sample of `n` blocks as a sequence, padded by `0`. -/
private def ltBlocks {W : ℕ} (n : ℕ) (ω : Ω W n) : ℕ → Matrix (Fin W) (Fin W) ℂ :=
  fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0

private lemma lt_measurable_blocks (W n : ℕ) : Measurable (ltBlocks (W := W) n) := by
  refine measurable_pi_iff.mpr fun k => ?_
  unfold ltBlocks
  by_cases h : k < n
  · simp only [h, dite_true]
    exact lt_measurable_gueBlock W n ⟨k, h⟩
  · simp only [h, dite_false]
    exact measurable_const

private lemma lt_measurable_chain (g E : ℝ) {W : ℕ} (X₀ : State W) (n : ℕ) (i : ℕ) :
    Measurable fun ω : Ω W n => chainState g E X₀ (ltBlocks n ω) i := by
  induction i with
  | zero => exact measurable_const
  | succ i ih =>
    have hb : Measurable fun ω : Ω W n => ltBlocks n ω i :=
      (measurable_pi_apply i).comp (lt_measurable_blocks W n)
    have h := (measurable_stepState g E W).comp (ih.prodMk hb)
    exact h

private lemma lt_hermitian_blocks (W n : ℕ) (ω : Ω W n) (k : ℕ) :
    (ltBlocks n ω k).IsHermitian := by
  unfold ltBlocks
  by_cases h : k < n
  · simp only [h, dite_true]
    exact gueBlock_isHermitian W n ω ⟨k, h⟩
  · simp only [h, dite_false]
    exact Matrix.isHermitian_zero

/-- (11.24) [uvg:eq:scalarfraction]: `𝔼 e^{-s ℓ_n(C₀, v₀)} ≤ C e^{-c n/(W g²)}` for every `n`,
every unitary `C₀` and unit `v₀`, `W ≥ W₀`, `g ≥ C_* √W`, `|E| ≤ E₀`. -/
theorem large_scalar_fraction {E₀ : ℝ} (hE₀ : E₀ < 2) :
    ∃ Cs C c s : ℝ, 1 ≤ Cs ∧ 0 < C ∧ 0 < c ∧ 0 < s ∧ s < 1 ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, Cs * Real.sqrt W ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
        ∀ X₀ : State W, IsState X₀ → ∀ n : ℕ,
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * ellN g E X₀.1 X₀.2
              (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) n)) ∂(μ W n) ≤
            ENNReal.ofReal (C * Real.exp (-c * n / (W * g ^ 2))) := by
  obtain ⟨A, B, K, Cs, s, c, hA, hB, hK, hCs, hs0, hs1, hc, hbd, W₀, hmgf⟩ := large_mgf hE₀
  refine ⟨Cs, Real.exp (2 * s * K), c, s, hCs, Real.exp_pos _, hc, hs0, hs1, max W₀ 1, ?_⟩
  intro W hW g hg E hE X₀ hX₀ n
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hg1 : 1 ≤ g := by
    refine le_trans ?_ hg
    have hsq : (1 : ℝ) ≤ Real.sqrt W := by
      rw [Real.one_le_sqrt]
      exact_mod_cast hW1
    nlinarith
  have hE2 : |E| < 2 := lt_of_le_of_lt hE hE₀
  set Y : State W → Matrix (Fin W) (Fin W) ℂ → ℝ := fun X V => driftY g E A B X V with hY
  set Z : State W → Matrix (Fin W) (Fin W) ℂ → ℝ≥0∞ :=
    fun X V => ENNReal.ofReal (Real.exp (-s * Y X V)) with hZ
  have hZm : Measurable (fun p : State W × Matrix (Fin W) (Fin W) ℂ => Z p.1 p.2) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (lt_measurable_driftY g E A B W)))
  have hq : ∀ X : State W, IsState X →
      ∫⁻ ω, Z X (gueBlock W 1 ω 0) ∂(μ W 1) ≤ ENNReal.ofReal (Real.exp (-c / (W * g ^ 2))) :=
    fun X hX => hmgf W ((le_max_left _ _).trans hW) g hg E hE X hX
  have hprod := lintegral_prod_chainState_le g E Z hZm hq hX₀ n
  have hpt : ∀ ω : Ω W n, ENNReal.ofReal (Real.exp (-s * ellN g E X₀.1 X₀.2
      (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) n)) ≤
      ENNReal.ofReal (Real.exp (2 * s * K)) *
        ∏ i ∈ Finset.range n,
          Z (chainState g E X₀ (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) i)
            (if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) := by
    intro ω
    have hV : ∀ k, (ltBlocks n ω k).IsHermitian := lt_hermitian_blocks W n ω
    have hstate : ∀ i, IsState (chainState g E X₀ (ltBlocks n ω) i) := by
      intro i
      induction i with
      | zero => exact hX₀
      | succ i ih => exact isState_stepState g E ih (hV i)
    have hsum := ellN_eq_sum hE2 g hX₀ hV n
    have hYsum : ∑ i ∈ Finset.range n, Y (chainState g E X₀ (ltBlocks n ω) i) (ltBlocks n ω i) =
        ellN g E X₀.1 X₀.2 (ltBlocks n ω) n -
          driftCorr g E A B (chainState g E X₀ (ltBlocks n ω) n) +
          driftCorr g E A B X₀ := by
      rw [hsum]
      have : ∀ i, Y (chainState g E X₀ (ltBlocks n ω) i) (ltBlocks n ω i) =
          stepInc g E (chainState g E X₀ (ltBlocks n ω) i) (ltBlocks n ω i) +
            (driftCorr g E A B (chainState g E X₀ (ltBlocks n ω) i) -
              driftCorr g E A B (chainState g E X₀ (ltBlocks n ω) (i + 1))) := by
        intro i
        simp only [hY, driftY]
        change stepInc g E (chainState g E X₀ (ltBlocks n ω) i) (ltBlocks n ω i) -
            driftCorr g E A B (chainState g E X₀ (ltBlocks n ω) (i + 1)) +
            driftCorr g E A B (chainState g E X₀ (ltBlocks n ω) i) = _
        ring
      simp_rw [this]
      rw [Finset.sum_add_distrib, Finset.sum_range_sub']
      simp only [chainState]
      ring
    have hQn := hbd W hW1 g hg1 E hE _ (hstate n)
    have hQ0 := hbd W hW1 g hg1 E hE _ hX₀
    have hℓ : -s * ellN g E X₀.1 X₀.2 (ltBlocks n ω) n ≤
        2 * s * K + ∑ i ∈ Finset.range n,
          (-s * Y (chainState g E X₀ (ltBlocks n ω) i) (ltBlocks n ω i)) := by
      rw [← Finset.mul_sum]
      have h1 := (abs_le.mp hQn).1
      have h2 := (abs_le.mp hQ0).2
      have h3 : -s * driftCorr g E A B (chainState g E X₀ (ltBlocks n ω) n) ≤ s * K := by
        nlinarith
      have h4 : s * driftCorr g E A B X₀ ≤ s * K := by nlinarith
      have h5 : ∑ i ∈ Finset.range n, Y (chainState g E X₀ (ltBlocks n ω) i) (ltBlocks n ω i) =
          ellN g E X₀.1 X₀.2 (ltBlocks n ω) n -
            driftCorr g E A B (chainState g E X₀ (ltBlocks n ω) n) +
            driftCorr g E A B X₀ := hYsum
      rw [h5]
      nlinarith
    calc ENNReal.ofReal (Real.exp (-s * ellN g E X₀.1 X₀.2 (ltBlocks n ω) n))
        ≤ ENNReal.ofReal (Real.exp (2 * s * K + ∑ i ∈ Finset.range n,
          (-s * Y (chainState g E X₀ (ltBlocks n ω) i) (ltBlocks n ω i)))) :=
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hℓ)
      _ = ENNReal.ofReal (Real.exp (2 * s * K)) *
          ∏ i ∈ Finset.range n, Z (chainState g E X₀ (ltBlocks n ω) i) (ltBlocks n ω i) := by
          rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, Real.exp_sum,
            ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * ellN g E X₀.1 X₀.2
          (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) n)) ∂(μ W n)
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * s * K)) *
        ∏ i ∈ Finset.range n,
          Z (chainState g E X₀ (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) i)
            (if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) ∂(μ W n) := lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (2 * s * K)) * ∫⁻ ω, ∏ i ∈ Finset.range n,
          Z (chainState g E X₀ (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) i)
            (if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) ∂(μ W n) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (2 * s * K)) *
          ENNReal.ofReal (Real.exp (-c / (W * g ^ 2))) ^ n := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (2 * s * K) * Real.exp (-c * n / (W * g ^ 2))) := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 3
        ring

/-- Theorem 11.1 [uvg:thm:transfer]: there are `C_*, W₀, C, c > 0` and `s ∈ (0, 1)` such that
for every `W ≥ W₀`, finite `g ≥ C_* √W`, `n ≥ 0`, `|E| ≤ E₀` and every frame `Φ` with
(8.8) [up:eq:boundary-frame], `𝔼‖D_n(Φ; E)⁻¹‖^s ≤ C W exp(-c n/(W g²))`, with `D_n` of (8.10)
[up:eq:D-definition] built from `T_i` of (8.9) [eq:c-transfer] over `n` fresh GUE blocks. -/
theorem negative_transfer_moment {E₀ : ℝ} (hE₀ : E₀ < 2) :
    ∃ Cs C c s : ℝ, 0 < Cs ∧ 0 < C ∧ 0 < c ∧ 0 < s ∧ s < 1 ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, Cs * Real.sqrt W ≤ g → ∀ n : ℕ, ∀ E : ℝ, |E| ≤ E₀ →
        ∀ Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ, IsBoundaryFrame Φ →
          ∫⁻ ω, ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
              (seqBlocks (gueBlock W n ω)) n) Φ)⁻¹‖ₑ ^ s ∂(μ W n) ≤
            ENNReal.ofReal (C * W * Real.exp (-c * n / (W * g ^ 2))) := by
  obtain ⟨Cs, C, c, s, hCs, hC, hc, hs0, hs1, W₀, hmain⟩ := large_scalar_fraction hE₀
  set E₁ : ℝ := max E₀ 0 with hE₁
  have hE₁2 : E₁ < 2 := max_lt hE₀ (by norm_num)
  have hE₁0 : 0 ≤ E₁ := le_max_right _ _
  have hE₀E₁ : E₀ ≤ E₁ := le_max_left _ _
  set Kc : ℝ := Real.sqrt ((2 + E₁) / (2 - E₁)) with hKc
  have hKc0 : 0 < Kc := Real.sqrt_pos.mpr (div_pos (by linarith) (by linarith))
  have hcc : ∀ E : ℝ, |E| ≤ E₀ → coordConst E ≤ Kc := by
    intro E hE
    have hEE : |E| ≤ E₁ := hE.trans hE₀E₁
    have h0 := abs_nonneg E
    unfold coordConst
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hrp : ∀ t : ℝ, 0 ≤ t → ∀ ℓ : ℝ, ℓ = -Real.log t → t ^ s ≤ Real.exp (-s * ℓ) := by
    intro t ht ℓ hℓ
    rcases ht.eq_or_lt with h | h
    · rw [← h, Real.zero_rpow hs0.ne']
      exact (Real.exp_pos _).le
    · rw [Real.rpow_def_of_pos h, hℓ]
      exact (Real.exp_le_exp.mpr (le_of_eq (by ring)))
  refine ⟨Cs, Kc ^ s * C, c, s, by linarith, mul_pos (Real.rpow_pos_of_pos hKc0 _) hC, hc, hs0,
    hs1, max W₀ 1, ?_⟩
  intro W hW g hg n E hE Φ hΦ
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hg1 : 1 ≤ g := by
    refine le_trans ?_ hg
    have hsq : (1 : ℝ) ≤ Real.sqrt W := by
      rw [Real.one_le_sqrt]
      exact_mod_cast hW1
    nlinarith
  have hE2 : |E| < 2 := lt_of_le_of_lt hE hE₀
  have hz : (max 1 g * E / g : ℝ) = E := by
    rw [max_eq_right hg1]
    field_simp
  rw [hz]
  obtain ⟨C₀, hC₀, B, -, hfr⟩ := exists_normalFrame hE2 hΦ
  have hst : ∀ j : Fin W, IsState ((C₀, EuclideanSpace.single j (1 : ℂ)) : State W) :=
    fun j => ⟨hC₀, by simp⟩
  set F : Fin W → Ω W n → ℝ≥0∞ := fun j ω => ENNReal.ofReal (Real.exp (-s *
    ellN g E C₀ (EuclideanSpace.single j (1 : ℂ)) (ltBlocks n ω) n)) with hF
  have hFm : ∀ j : Fin W, Measurable (F j) := by
    intro j
    have heq : (fun ω : Ω W n => ellN g E C₀ (EuclideanSpace.single j (1 : ℂ)) (ltBlocks n ω) n) =
        fun ω => ∑ i ∈ Finset.range n, stepInc g E
          (chainState g E ((C₀, EuclideanSpace.single j (1 : ℂ)) : State W) (ltBlocks n ω) i)
          (ltBlocks n ω i) := by
      funext ω
      exact ellN_eq_sum hE2 g (hst j) (lt_hermitian_blocks W n ω) n
    have hsum : Measurable (fun ω : Ω W n => ellN g E C₀ (EuclideanSpace.single j (1 : ℂ))
        (ltBlocks n ω) n) := by
      rw [heq]
      refine Finset.measurable_sum _ fun i _ => ?_
      have hb : Measurable fun ω : Ω W n => ltBlocks n ω i :=
        (measurable_pi_apply i).comp (lt_measurable_blocks W n)
      have h := (measurable_stepInc g E W).comp
        ((lt_measurable_chain g E ((C₀, EuclideanSpace.single j (1 : ℂ)) : State W) n i).prodMk hb)
      exact h
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hsum))
  have hpt : ∀ ω : Ω W n, ‖(frameD (transferProd g (E : ℂ) (seqBlocks (gueBlock W n ω)) n)
      Φ)⁻¹‖ₑ ^ s ≤ ENNReal.ofReal (Kc ^ s) * ∑ j : Fin W, F j ω := by
    intro ω
    have hV : ∀ k, (ltBlocks n ω k).IsHermitian := lt_hermitian_blocks W n ω
    have hseq : seqBlocks (gueBlock W n ω) = ltBlocks n ω := rfl
    rw [hseq]
    have hle := (norm_inv_frameD_le hE2 g hΦ hC₀ hfr hV n).1
    have hsum := norm_inv_rpow_le_sum (normalD g E C₀ (ltBlocks n ω) n) hs0 (by linarith)
    have hreal : ‖(frameD (transferProd g (E : ℂ) (ltBlocks n ω) n) Φ)⁻¹‖ ^ s ≤
        Kc ^ s * ∑ j : Fin W, Real.exp (-s * ellN g E C₀ (EuclideanSpace.single j (1 : ℂ))
          (ltBlocks n ω) n) := by
      calc ‖(frameD (transferProd g (E : ℂ) (ltBlocks n ω) n) Φ)⁻¹‖ ^ s
          ≤ (coordConst E * ‖(normalD g E C₀ (ltBlocks n ω) n)⁻¹‖) ^ s :=
            Real.rpow_le_rpow (norm_nonneg _) hle hs0.le
        _ ≤ (Kc * ‖(normalD g E C₀ (ltBlocks n ω) n)⁻¹‖) ^ s :=
            Real.rpow_le_rpow (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
              (mul_le_mul_of_nonneg_right (hcc E hE) (norm_nonneg _)) hs0.le
        _ = Kc ^ s * ‖(normalD g E C₀ (ltBlocks n ω) n)⁻¹‖ ^ s :=
            Real.mul_rpow hKc0.le (norm_nonneg _)
        _ ≤ Kc ^ s * ∑ j : Fin W, ‖Matrix.toEuclideanLin ((normalD g E C₀ (ltBlocks n ω) n)⁻¹ᴴ)
              (EuclideanSpace.single j 1)‖ ^ s :=
            mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hKc0.le _)
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_)
              (Real.rpow_nonneg hKc0.le _)
            exact hrp _ (norm_nonneg _) _ rfl
    calc ‖(frameD (transferProd g (E : ℂ) (ltBlocks n ω) n) Φ)⁻¹‖ₑ ^ s
        = ENNReal.ofReal (‖(frameD (transferProd g (E : ℂ) (ltBlocks n ω) n) Φ)⁻¹‖ ^ s) := by
          rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs0.le]
      _ ≤ ENNReal.ofReal (Kc ^ s * ∑ j : Fin W, Real.exp (-s * ellN g E C₀
          (EuclideanSpace.single j (1 : ℂ)) (ltBlocks n ω) n)) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (Kc ^ s) * ∑ j : Fin W, F j ω := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hKc0.le _),
            ENNReal.ofReal_sum_of_nonneg (fun j _ => (Real.exp_pos _).le)]
  have hbound : ∀ j : Fin W, ∫⁻ ω, F j ω ∂(μ W n) ≤
      ENNReal.ofReal (C * Real.exp (-c * n / (W * g ^ 2))) := fun j =>
    hmain W ((le_max_left _ _).trans hW) g hg E hE _ (hst j) n
  calc ∫⁻ ω, ‖(frameD (transferProd g (E : ℂ) (seqBlocks (gueBlock W n ω)) n) Φ)⁻¹‖ₑ ^ s
        ∂(μ W n)
      ≤ ∫⁻ ω, ENNReal.ofReal (Kc ^ s) * ∑ j : Fin W, F j ω ∂(μ W n) := lintegral_mono hpt
    _ = ENNReal.ofReal (Kc ^ s) * ∑ j : Fin W, ∫⁻ ω, F j ω ∂(μ W n) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum _ fun j _ => hFm j]
    _ ≤ ENNReal.ofReal (Kc ^ s) * ∑ j : Fin W,
          ENNReal.ofReal (C * Real.exp (-c * n / (W * g ^ 2))) := by
        gcongr with j _
        exact hbound j
    _ = ENNReal.ofReal (Kc ^ s * C * W * Real.exp (-c * n / (W * g ^ 2))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 : Kc ^ s * C * W * Real.exp (-c * n / (W * g ^ 2)) =
            Kc ^ s * (W * (C * Real.exp (-c * n / (W * g ^ 2)))) := by ring
        rw [h1, ENNReal.ofReal_mul (Real.rpow_nonneg hKc0.le _),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end LSBA
