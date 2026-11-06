import LSBA.Upper.CenterMoments

/-!
# Stability of `M_k` and `F_k`

Lemma 11.8 [lg:lem:dynamic]: the moment bounds (11.60) [lg:eq:momentout] along the chain and the
event (11.44) [lg:eq:burnevent]: for `ε > 0`, an order `R ≥ 2` with `2εR > 1`, a finite set of
nonzero indices and `D, η, B_1 > 0`, there are an energy window, `C_*` and `W_0` with, for
`W ≥ W_0`, `g ≥ W^ε`, `|E|` in the window and every initial state, probability at
least `1 − W^{−D}` that `|M_k(C_n) − a_k| ≤ W^{η−1}` and `|F_k(C_n, v_n)| ≤ W^{η−1/2}` for all
indices and all `n_* ≤ n ≤ N`, `N ≤ W^{B_1}`, `n_* = ⌈C_* g² log W⌉` (11.25)
[lg:eq:initial-time]. The polynomials `M_k`, `F_k` and the centers `a_k` do not depend on `D`,
`η`, `B_1`.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Measurability and integrability along the chain -/

/-- The blocks of a sample of `n` blocks as a sequence, padded by `0`. -/
private def csBlocks {W : ℕ} (n : ℕ) (ω : Ω W n) : ℕ → Matrix (Fin W) (Fin W) ℂ :=
  fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0

/-- The expectation of `φ` at step `n` of the chain along `n` blocks. -/
private def csE (g E : ℝ) {W : ℕ} (X₀ : State W) (n : ℕ) (φ : State W → ℝ) : ℝ :=
  ∫ ω, φ (chainState g E X₀ (csBlocks n ω) n) ∂(μ W n)

private lemma cs_measurable_gueBlock (W L : ℕ) (a : Fin L) :
    Measurable fun ω : Ω W L => gueBlock W L ω a := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma cs_measurable_blocks (W n : ℕ) : Measurable (csBlocks (W := W) n) := by
  refine measurable_pi_iff.mpr fun k => ?_
  unfold csBlocks
  by_cases h : k < n
  · simp only [h, dite_true]
    exact cs_measurable_gueBlock W n ⟨k, h⟩
  · simp only [h, dite_false]
    exact measurable_const

private lemma cs_measurable_chain (g E : ℝ) {W : ℕ} (X₀ : State W) (n i : ℕ) :
    Measurable fun ω : Ω W n => chainState g E X₀ (csBlocks n ω) i := by
  induction i with
  | zero => exact measurable_const
  | succ i ih =>
    have hb : Measurable fun ω : Ω W n => csBlocks n ω i :=
      (measurable_pi_apply i).comp (cs_measurable_blocks W n)
    have h := (measurable_stepState g E W).comp (ih.prodMk hb)
    exact h

private lemma cs_isState_chain (g E : ℝ) {W : ℕ} {X₀ : State W} (hX₀ : IsState X₀) (n : ℕ)
    (ω : Ω W n) (i : ℕ) : IsState (chainState g E X₀ (csBlocks n ω) i) := by
  induction i with
  | zero => exact hX₀
  | succ i ih =>
    refine isState_stepState g E ih ?_
    unfold csBlocks
    split_ifs
    · exact gueBlock_isHermitian W n ω _
    · exact Matrix.isHermitian_zero

private lemma cs_cont_vecForm {W : ℕ} :
    Continuous fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) => vecForm q.1 q.2 := by
  have hc : Continuous (fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) =>
      Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) q.1 q.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM
  exact continuous_snd.inner hc

private lemma cs_measurable_inv {W : ℕ} : Measurable fun X : Matrix (Fin W) (Fin W) ℂ => X⁻¹ := by
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

private lemma cs_measurable_zpow {W : ℕ} (k : ℤ) :
    Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A ^ k := by
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact (continuous_id.pow n).measurable
  | negSucc n =>
    simp only [zpow_negSucc]
    exact cs_measurable_inv.comp (continuous_id.pow _).measurable

private lemma cs_measurable_obsEval (g : ℝ) (W : ℕ) (p : ObsPoly) :
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
        ((cs_measurable_zpow k.1).comp measurable_fst))
    | f k =>
      simp only [obsEval, aeval_X, obsF]
      have h1 : Measurable fun X : State W => (X.1 ^ k.1, X.2) :=
        ((cs_measurable_zpow k.1).comp measurable_fst).prodMk measurable_snd
      have h2 := (cs_cont_vecForm (W := W)).measurable.comp h1
      exact h2
    | w => simp only [obsEval, aeval_X]; exact measurable_const
    | γ => simp only [obsEval, aeval_X]; exact measurable_const

/-- A measurable real function of the states, bounded on the states. -/
private def CsTame {W : ℕ} (φ : State W → ℝ) : Prop :=
  Measurable φ ∧ ∃ B : ℝ, ∀ X : State W, IsState X → |φ X| ≤ B

private lemma cs_tame_const {W : ℕ} (c : ℝ) : CsTame (fun _ : State W => c) :=
  ⟨measurable_const, |c|, fun _ _ => le_rfl⟩

private lemma cs_tame_add {W : ℕ} {φ ψ : State W → ℝ} (hφ : CsTame φ) (hψ : CsTame ψ) :
    CsTame (fun X => φ X + ψ X) := by
  obtain ⟨hm, B, hB⟩ := hφ
  obtain ⟨hm', B', hB'⟩ := hψ
  exact ⟨hm.add hm', B + B', fun X hX => (abs_add_le _ _).trans (add_le_add (hB X hX) (hB' X hX))⟩

private lemma cs_tame_mul_left {W : ℕ} {φ : State W → ℝ} (c : ℝ) (hφ : CsTame φ) :
    CsTame (fun X => c * φ X) := by
  obtain ⟨hm, B, hB⟩ := hφ
  exact ⟨hm.const_mul c, |c| * B, fun X hX => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB X hX) (abs_nonneg c)⟩

private lemma cs_tame_sum {W : ℕ} {ι : Type*} (J : Finset ι) {φ : ι → State W → ℝ}
    (hφ : ∀ k, CsTame (φ k)) : CsTame (fun X => ∑ k ∈ J, φ k X) := by
  induction J using Finset.induction_on with
  | empty => simpa using cs_tame_const (W := W) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact cs_tame_add (hφ a) ih

private lemma cs_tame_normpow {W : ℕ} {ψ : State W → ℂ} (hψ : Measurable ψ)
    (hB : ∃ B : ℝ, ∀ X : State W, IsState X → ‖ψ X‖ ≤ B) (m : ℕ) :
    CsTame (fun X => ‖ψ X‖ ^ m) := by
  obtain ⟨B, hB⟩ := hB
  refine ⟨(hψ.norm).pow_const m, (max B 0) ^ m, fun X hX => ?_⟩
  rw [abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) ((hB X hX).trans (le_max_left _ _)) m


private lemma cs_integrable (g E : ℝ) {W : ℕ} {X₀ : State W} (hX₀ : IsState X₀) {φ : State W → ℝ}
    (hφ : CsTame φ) (n : ℕ) :
    Integrable (fun ω : Ω W n => φ (chainState g E X₀ (csBlocks n ω) n)) (μ W n) := by
  obtain ⟨hm, B, hB⟩ := hφ
  exact Integrable.of_bound (hm.comp (cs_measurable_chain g E X₀ n n)).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ω => by
      simpa using hB _ (cs_isState_chain g E hX₀ n ω n))

private lemma csE_add (g E : ℝ) {W : ℕ} {X₀ : State W} (hX₀ : IsState X₀) {φ ψ : State W → ℝ}
    (hφ : CsTame φ) (hψ : CsTame ψ) (n : ℕ) :
    csE g E X₀ n (fun X => φ X + ψ X) = csE g E X₀ n φ + csE g E X₀ n ψ :=
  integral_add (cs_integrable g E hX₀ hφ n) (cs_integrable g E hX₀ hψ n)

private lemma csE_mul_left (g E : ℝ) {W : ℕ} (X₀ : State W) (c : ℝ) (φ : State W → ℝ) (n : ℕ) :
    csE g E X₀ n (fun X => c * φ X) = c * csE g E X₀ n φ :=
  integral_const_mul c _

private lemma csE_const (g E : ℝ) {W : ℕ} (X₀ : State W) (c : ℝ) (n : ℕ) :
    csE g E X₀ n (fun _ => c) = c := by
  simp [csE]

private lemma csE_sum (g E : ℝ) {W : ℕ} {X₀ : State W} (hX₀ : IsState X₀) {ι : Type*}
    (J : Finset ι) {φ : ι → State W → ℝ} (hφ : ∀ k, CsTame (φ k)) (n : ℕ) :
    csE g E X₀ n (fun X => ∑ k ∈ J, φ k X) = ∑ k ∈ J, csE g E X₀ n (φ k) :=
  integral_finsetSum J fun k _ => cs_integrable g E hX₀ (hφ k) n

private lemma csE_nonneg (g E : ℝ) {W : ℕ} (X₀ : State W) {φ : State W → ℝ}
    (h : ∀ X, 0 ≤ φ X) (n : ℕ) : 0 ≤ csE g E X₀ n φ :=
  integral_nonneg fun _ => h _

private lemma csE_le (g E : ℝ) {W : ℕ} {X₀ : State W} (hX₀ : IsState X₀) {φ : State W → ℝ}
    (hφ : CsTame φ) {B : ℝ} (h : ∀ X, IsState X → φ X ≤ B) (n : ℕ) : csE g E X₀ n φ ≤ B := by
  have := integral_mono (cs_integrable g E hX₀ hφ n) (integrable_const B)
    (fun ω => h _ (cs_isState_chain g E hX₀ n ω n))
  simpa [csE] using this

private lemma cs_transOpL_eq (g E : ℝ) {W : ℕ} {Φ : State W → ℝ} (hΦ : CsTame Φ)
    (h0 : ∀ X, 0 ≤ Φ X) {X : State W} (hX : IsState X) :
    transOpL g E (fun Y => ENNReal.ofReal (Φ Y)) X = ENNReal.ofReal (transOp g E Φ X) := by
  obtain ⟨hm, B, hB⟩ := hΦ
  unfold transOpL transOp
  have hS : Measurable fun V : Matrix (Fin W) (Fin W) ℂ => (X, V) :=
    Measurable.prodMk measurable_const measurable_id
  have hm' : Measurable fun ω : Ω W 1 => Φ (stepState g E X (gueBlock W 1 ω 0)) :=
    hm.comp (((measurable_stepState g E W).comp hS).comp (cs_measurable_gueBlock W 1 0))
  have hint : Integrable (fun ω : Ω W 1 => Φ (stepState g E X (gueBlock W 1 ω 0))) (μ W 1) :=
    Integrable.of_bound hm'.aestronglyMeasurable B (Filter.Eventually.of_forall fun ω =>
      hB _ (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)))
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω => h0 _)]

private lemma cs_step (g E : ℝ) {W : ℕ} {X₀ : State W} (hX₀ : IsState X₀) {Φ ψ : State W → ℝ}
    (hΦ : CsTame Φ) (hΦ0 : ∀ X, 0 ≤ Φ X) (hψ : CsTame ψ) {γ : ℝ}
    (h : ∀ X : State W, IsState X → transOp g E Φ X ≤ (1 - γ) * Φ X + ψ X) (n : ℕ) :
    csE g E X₀ (n + 1) Φ ≤ (1 - γ) * csE g E X₀ n Φ + csE g E X₀ n ψ := by
  have hΨ : CsTame (fun X => (1 - γ) * Φ X + ψ X) :=
    cs_tame_add (cs_tame_mul_left _ hΦ) hψ
  have hnn : ∀ ω : Ω W n, 0 ≤ (1 - γ) * Φ (chainState g E X₀ (csBlocks n ω) n) +
      ψ (chainState g E X₀ (csBlocks n ω) n) := fun ω =>
    (integral_nonneg fun _ => hΦ0 _).trans (h _ (cs_isState_chain g E hX₀ n ω n))
  have h1 : ENNReal.ofReal (csE g E X₀ (n + 1) Φ) =
      ∫⁻ ω, ENNReal.ofReal (Φ (chainState g E X₀ (csBlocks (n + 1) ω) (n + 1))) ∂(μ W (n + 1)) :=
    ofReal_integral_eq_lintegral_ofReal (cs_integrable g E hX₀ hΦ (n + 1))
      (Filter.Eventually.of_forall fun ω => hΦ0 _)
  have hmeas : Measurable fun X : State W => ENNReal.ofReal (Φ X) :=
    ENNReal.measurable_ofReal.comp hΦ.1
  have h2 := lintegral_mul_chainState_succ g E X₀ (n := n) (G := fun _ => 1) measurable_const
    hmeas
  simp only [one_mul] at h2
  have h3 : ∫⁻ ω, ENNReal.ofReal (Φ (chainState g E X₀ (csBlocks (n + 1) ω) (n + 1)))
      ∂(μ W (n + 1)) ≤ ∫⁻ ω, ENNReal.ofReal ((1 - γ) * Φ (chainState g E X₀ (csBlocks n ω) n) +
        ψ (chainState g E X₀ (csBlocks n ω) n)) ∂(μ W n) := by
    refine (le_of_eq h2).trans ?_
    refine lintegral_mono fun ω => ?_
    exact (le_of_eq (cs_transOpL_eq g E hΦ hΦ0 (cs_isState_chain g E hX₀ n ω n))).trans
      (ENNReal.ofReal_le_ofReal (h _ (cs_isState_chain g E hX₀ n ω n)))
  have h4 : ENNReal.ofReal (∫ ω, ((1 - γ) * Φ (chainState g E X₀ (csBlocks n ω) n) +
      ψ (chainState g E X₀ (csBlocks n ω) n)) ∂(μ W n)) =
      ∫⁻ ω, ENNReal.ofReal ((1 - γ) * Φ (chainState g E X₀ (csBlocks n ω) n) +
        ψ (chainState g E X₀ (csBlocks n ω) n)) ∂(μ W n) :=
    ofReal_integral_eq_lintegral_ofReal (cs_integrable g E hX₀ hΨ n)
      (Filter.Eventually.of_forall hnn)
  have h5 := (h1.trans_le h3).trans_eq h4.symm
  have h6 : 0 ≤ ∫ ω, ((1 - γ) * Φ (chainState g E X₀ (csBlocks n ω) n) +
      ψ (chainState g E X₀ (csBlocks n ω) n)) ∂(μ W n) := integral_nonneg hnn
  have h7 := (ENNReal.ofReal_le_ofReal_iff h6).mp h5
  have h8 := csE_add g E hX₀ (cs_tame_mul_left (1 - γ) hΦ) hψ n
  rw [csE_mul_left] at h8
  exact h7.trans (le_of_eq h8)

private lemma cs_wrec (g E : ℝ) {W : ℕ} {X₀ : State W} (hX₀ : IsState X₀) {ι : Type*}
    (J : Finset ι) {φ : ι → State W → ℝ} (hφ : ∀ k, CsTame (φ k)) (hφ0 : ∀ k X, 0 ≤ φ k X)
    (u : ι → ℝ) (hu : ∀ k, 0 < u k) {ψ : State W → ℝ} (hψ : CsTame ψ) {γ : ℝ}
    (h : ∀ X : State W, IsState X →
      ∑ k ∈ J, u k * transOp g E (φ k) X ≤ (1 - γ) * ∑ k ∈ J, u k * φ k X + ψ X) (n : ℕ) :
    ∑ k ∈ J, u k * csE g E X₀ (n + 1) (φ k) ≤
      (1 - γ) * ∑ k ∈ J, u k * csE g E X₀ n (φ k) + csE g E X₀ n ψ := by
  have hΦ : CsTame (fun X => ∑ k ∈ J, u k * φ k X) :=
    cs_tame_sum J fun k => cs_tame_mul_left _ (hφ k)
  have hΦ0 : ∀ X, 0 ≤ ∑ k ∈ J, u k * φ k X := fun X =>
    Finset.sum_nonneg fun k _ => mul_nonneg (hu k).le (hφ0 k X)
  have hlin : ∀ X : State W, IsState X → transOp g E (fun X => ∑ k ∈ J, u k * φ k X) X =
      ∑ k ∈ J, u k * transOp g E (φ k) X := by
    intro X hX
    unfold transOp
    have hS : Measurable fun V : Matrix (Fin W) (Fin W) ℂ => (X, V) :=
      Measurable.prodMk measurable_const measurable_id
    have hint : ∀ k, Integrable (fun ω : Ω W 1 => u k * φ k (stepState g E X (gueBlock W 1 ω 0)))
        (μ W 1) := fun k => by
      obtain ⟨hm, B, hB⟩ := hφ k
      have hm' : Measurable fun ω : Ω W 1 => φ k (stepState g E X (gueBlock W 1 ω 0)) :=
        hm.comp (((measurable_stepState g E W).comp hS).comp (cs_measurable_gueBlock W 1 0))
      exact (Integrable.of_bound hm'.aestronglyMeasurable B (Filter.Eventually.of_forall fun ω =>
        hB _ (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)))).const_mul _
    rw [integral_finsetSum J fun k _ => hint k]
    exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  have := cs_step g E hX₀ hΦ hΦ0 hψ (γ := γ) (fun X hX => by rw [hlin X hX]; exact h X hX) n
  rw [csE_sum g E hX₀ J (fun k => cs_tame_mul_left _ (hφ k)),
    csE_sum g E hX₀ J (fun k => cs_tame_mul_left _ (hφ k))] at this
  simpa only [csE_mul_left] using this

/-! ### Real recursion -/

/-- `x_{n+1} ≤ (1 − γ) x_n + b + B e^{−α n}` with `α ≤ γ/2` gives
`x_n ≤ e^{−α n}(x_0 + 2B/γ) + b/γ`. -/
private lemma cs_rec {γ α b B : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hα : 0 < α) (hαγ : α ≤ γ / 2)
    (hb : 0 ≤ b) (hB : 0 ≤ B) {x : ℕ → ℝ} (hx0 : 0 ≤ x 0)
    (hx : ∀ n, x (n + 1) ≤ (1 - γ) * x n + (b + B * Real.exp (-(α * n)))) (n : ℕ) :
    x n ≤ Real.exp (-(α * n)) * (x 0 + 2 * B / γ) + b / γ := by
  have key : ∀ n : ℕ, x n ≤ (1 - γ) ^ n * x 0 + b / γ + 2 * B / γ * Real.exp (-(α * n)) := by
    intro n
    induction n with
    | zero =>
      have h1 : 0 ≤ b / γ := by positivity
      have h2 : 0 ≤ 2 * B / γ := by positivity
      simp
      linarith
    | succ n ih =>
      have h1 : 0 ≤ 1 - γ := by linarith
      have h2 := mul_le_mul_of_nonneg_left ih h1
      have he : 1 - α ≤ Real.exp (-α) := by linarith [Real.add_one_le_exp (-α)]
      have hexp : Real.exp (-(α * ((n + 1 : ℕ) : ℝ))) = Real.exp (-(α * n)) * Real.exp (-α) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have hen : 0 < Real.exp (-(α * n)) := Real.exp_pos _
      have hL : (1 - γ) * (2 * B / γ) + B ≤ 2 * B / γ * Real.exp (-α) := by
        have : (1 - γ) * (2 * B / γ) + B = 2 * B / γ * (1 - γ / 2) := by field_simp; ring
        rw [this]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
      have hb' : b / γ * (1 - γ) + b = b / γ := by field_simp; ring
      calc x (n + 1) ≤ (1 - γ) * x n + (b + B * Real.exp (-(α * n))) := hx n
        _ ≤ (1 - γ) * ((1 - γ) ^ n * x 0 + b / γ + 2 * B / γ * Real.exp (-(α * n))) +
            (b + B * Real.exp (-(α * n))) := by linarith
        _ = (1 - γ) ^ (n + 1) * x 0 + b / γ +
            ((1 - γ) * (2 * B / γ) + B) * Real.exp (-(α * n)) := by
          rw [pow_succ]; linarith [hb']
        _ ≤ (1 - γ) ^ (n + 1) * x 0 + b / γ + 2 * B / γ * Real.exp (-(α * n)) * Real.exp (-α) := by
          have := mul_le_mul_of_nonneg_right hL hen.le
          nlinarith
        _ = _ := by rw [hexp]; ring
  have hpow : (1 - γ) ^ n ≤ Real.exp (-(α * n)) := by
    have h1 : 1 - γ ≤ Real.exp (-γ) := by linarith [Real.add_one_le_exp (-γ)]
    calc (1 - γ) ^ n ≤ Real.exp (-γ) ^ n := pow_le_pow_left₀ (by linarith) h1 n
      _ = Real.exp (-(γ * n)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp (-(α * n)) := by
        apply Real.exp_le_exp.mpr
        have : α * n ≤ γ * n := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
        linarith
  have := key n
  nlinarith [mul_le_mul_of_nonneg_right hpow hx0]

/-- The closing estimate of one level: the weighted sums `x` satisfy a recursion with a source `r`
that decays up to a constant; the unweighted sums `a` are at most `x/δ`. -/
private lemma cs_close {c₁ c₂ K₁ g A C δ X0 : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hK₁ : 0 < K₁)
    (hg : 1 ≤ g) (hcg : c₁ ≤ g) (hA : 0 ≤ A) (hC : 0 ≤ C) (hδ : 0 < δ) {x a r : ℕ → ℝ}
    (hx0 : 0 ≤ x 0) (hx0b : x 0 ≤ X0)
    (hx : ∀ n, x (n + 1) ≤ (1 - c₁ / g ^ 2) * x n + K₁ / g ^ 2 * r n)
    (hr : ∀ n, r n ≤ A * Real.exp (-(c₂ * n / g ^ 2)) + C)
    (hax : ∀ n, δ * a n ≤ x n) (n : ℕ) :
    a n ≤ 1 / δ * (Real.exp (-(min c₁ c₂ / 2 * n / g ^ 2)) * (X0 + 2 * K₁ * A / c₁) +
      K₁ * C / c₁) := by
  have hg0 : 0 < g := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have hγ : 0 < c₁ / g ^ 2 := by positivity
  have hγ1 : c₁ / g ^ 2 ≤ 1 := by
    rw [div_le_one hg2]; nlinarith
  set α := min c₁ c₂ / 2 / g ^ 2 with hα
  have hm0 : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  have hα0 : 0 < α := by positivity
  have hαγ : α ≤ c₁ / g ^ 2 / 2 := by
    rw [hα, div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [min_le_left c₁ c₂, hg2]
  have hexp : ∀ n : ℕ, Real.exp (-(c₂ * n / g ^ 2)) ≤ Real.exp (-(α * n)) := fun n => by
    apply Real.exp_le_exp.mpr
    have : α * n ≤ c₂ * n / g ^ 2 := by
      rw [hα, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hg2]
      have := min_le_right c₁ c₂
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  have hx' : ∀ n, x (n + 1) ≤ (1 - c₁ / g ^ 2) * x n +
      (K₁ * C / g ^ 2 + K₁ * A / g ^ 2 * Real.exp (-(α * n))) := by
    intro n
    refine (hx n).trans ?_
    have h1 : K₁ / g ^ 2 * r n ≤ K₁ / g ^ 2 * (A * Real.exp (-(c₂ * n / g ^ 2)) + C) :=
      mul_le_mul_of_nonneg_left (hr n) (by positivity)
    have h2 : A * Real.exp (-(c₂ * n / g ^ 2)) ≤ A * Real.exp (-(α * n)) :=
      mul_le_mul_of_nonneg_left (hexp n) hA
    have h3 : K₁ / g ^ 2 * (A * Real.exp (-(α * n)) + C) =
        K₁ * C / g ^ 2 + K₁ * A / g ^ 2 * Real.exp (-(α * n)) := by ring
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ K₁ / g ^ 2)]
  have hr' := cs_rec hγ hγ1 hα0 hαγ (by positivity) (by positivity) hx0 hx' n
  have e1 : 2 * (K₁ * A / g ^ 2) / (c₁ / g ^ 2) = 2 * K₁ * A / c₁ := by field_simp
  have e2 : K₁ * C / g ^ 2 / (c₁ / g ^ 2) = K₁ * C / c₁ := by field_simp
  rw [e1, e2] at hr'
  have e3 : min c₁ c₂ / 2 * n / g ^ 2 = α * n := by rw [hα]; ring
  rw [e3]
  have hxn : x n ≤ Real.exp (-(α * n)) * (X0 + 2 * K₁ * A / c₁) + K₁ * C / c₁ := by
    refine hr'.trans ?_
    have : x 0 + 2 * K₁ * A / c₁ ≤ X0 + 2 * K₁ * A / c₁ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this (Real.exp_pos (-(α * n))).le]
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ]
  linarith [hax n]

private lemma cs_exists_min (J : Finset NzInt) (u : NzInt → ℝ) (hu : ∀ k, 0 < u k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k ∈ J, δ ≤ u k := by
  rcases J.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨x, hx, hmin⟩ := J.exists_min_image u hne
    exact ⟨u x, hu x, hmin⟩

/-! ### The moment functions and the index sets -/

/-- `|M_k − a_k|^{2p}` as a function of the state. -/
private def csY (g E : ℝ) (R p : ℕ) {W : ℕ} (k : NzInt) (X : State W) : ℝ :=
  ‖obsEval g X (corrObsM E R k) - center g E R k.1‖ ^ (2 * p)

/-- `|F_k|^{2p}` as a function of the state. -/
private def csZ (g E : ℝ) (R p : ℕ) {W : ℕ} (k : NzInt) (X : State W) : ℝ :=
  ‖obsEval g X (corrObsF E R k)‖ ^ (2 * p)

private lemma cs_tame_Y (g E : ℝ) (R p : ℕ) {W : ℕ} (hW : 1 ≤ W) (hg : 1 ≤ g) (k : NzInt) :
    CsTame (csY g E R p (W := W) k) := by
  refine cs_tame_normpow (ψ := fun X => obsEval g X (corrObsM E R k) - center g E R k.1)
    ((cs_measurable_obsEval g W _).sub_const _)
    ⟨∑ d ∈ (corrObsM E R k).support, ‖(corrObsM E R k).coeff d‖ + ‖center g E R k.1‖,
      fun X hX => (norm_sub_le _ _).trans
        (add_le_add (norm_obsEval_le hW hg hX _) le_rfl)⟩ _

private lemma cs_tame_Z (g E : ℝ) (R p : ℕ) {W : ℕ} (hW : 1 ≤ W) (hg : 1 ≤ g) (k : NzInt) :
    CsTame (csZ g E R p (W := W) k) :=
  cs_tame_normpow (ψ := fun X => obsEval g X (corrObsF E R k)) (cs_measurable_obsEval g W _)
    ⟨_, fun _ hX => norm_obsEval_le hW hg hX _⟩ _

private lemma cs_Y_nonneg (g E : ℝ) (R p : ℕ) {W : ℕ} (k : NzInt) (X : State W) :
    0 ≤ csY g E R p k X := by unfold csY; positivity

private lemma cs_Z_nonneg (g E : ℝ) (R p : ℕ) {W : ℕ} (k : NzInt) (X : State W) :
    0 ≤ csZ g E R p k X := by unfold csZ; positivity

/-- The closed index set `{k ≠ 0 : |k| ≤ N}`. -/
private def csCl (N : ℕ) : Finset NzInt := (Finset.Icc (-(N : ℤ)) N).subtype (· ≠ 0)

private lemma cs_mem_cl {N : ℕ} {k : NzInt} : k ∈ csCl N ↔ |k.1| ≤ N := by
  unfold csCl
  rw [Finset.mem_subtype, Finset.mem_Icc, abs_le]

private lemma cs_cl_closed (N : ℕ) :
    ∀ k ∈ csCl N, ∀ j : NzInt, |j.1| ≤ |k.1| → j ∈ csCl N :=
  fun _ hk _ hj => cs_mem_cl.mpr (hj.trans (cs_mem_cl.mp hk))

private lemma cs_sub_cl (J : Finset NzInt) : J ⊆ csCl (J.sup fun k => k.1.natAbs) := by
  intro k hk
  rw [cs_mem_cl, Int.abs_eq_natAbs]
  exact_mod_cast Finset.le_sup (f := fun k : NzInt => k.1.natAbs) hk

/-- A uniform pointwise bound for `|M_k − a_k|^{2p}` and `|F_k|^{2p}` on the states, for `k` in a
closed index set (`|m_k|, |f_k| ≤ 1` and the `O(g⁻²)` and center bounds). -/
private lemma cs_crude (R p N : ℕ) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ B g₀ : ℝ, 0 < B ∧ 1 ≤ g₀ ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, g₀ ≤ g →
      ∀ E : ℝ, |E| ≤ E₁ → ∀ X : State W, IsState X → ∀ k ∈ csCl N,
        csY g E R p k X ≤ B ∧ csZ g E R p k X ≤ B := by
  obtain ⟨E₁, hE₁, K₁, hK₁, h1⟩ := norm_obsEval_corrObs_sub_le R (csCl N)
  obtain ⟨E₂, hE₂, c, K₂, g₂, hc, hK₂, hg₂, h2⟩ := center_bounds R (csCl N)
  refine ⟨min E₁ E₂, lt_min hE₁ hE₂, (K₁ + 1 + K₂) ^ (2 * p), max g₂ 1, by positivity,
    le_max_right _ _, fun W hW g hg E hE X hX k hk => ?_⟩
  have hg1 : 1 ≤ g := (le_max_right _ _).trans hg
  have hg2' : g₂ ≤ g := (le_max_left _ _).trans hg
  obtain ⟨hM, hF, -, -⟩ := h1 W hW g hg1 E (hE.trans (min_le_left _ _)) X hX k hk
  have hcen := (h2 g hg2' E (hE.trans (min_le_right _ _))).2 k hk
  have hdiv : K₁ / g ^ 2 ≤ K₁ := div_le_self hK₁.le (one_le_pow₀ hg1)
  have hm1 := norm_obsM_le_one k.1 hX
  have hf1 := norm_obsF_le_one k.1 hX
  constructor
  · unfold csY
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    set M := obsEval g X (corrObsM E R k)
    have e : M - center g E R k.1 = (M - obsM k.1 X) + obsM k.1 X - center g E R k.1 := by ring
    have h3 := norm_sub_le ((M - obsM k.1 X) + obsM k.1 X) (center g E R k.1)
    have h4 := norm_add_le (M - obsM k.1 X) (obsM k.1 X)
    rw [e]
    linarith [hcen.2.1]
  · unfold csZ
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    set F := obsEval g X (corrObsF E R k)
    have e : F = (F - obsF k.1 X) + obsF k.1 X := by ring
    have h4 := norm_add_le (F - obsF k.1 X) (obsF k.1 X)
    rw [e]
    linarith [hcen.2.1, norm_nonneg (center g E R k.1)]

/-- The moment bound for `|M_k − a_k|^{2p}` on the closed index set of radius `N`, with the
`g^{−4pm}` term of the `m`-th level. -/
private def CsPM (R p m : ℕ) : Prop :=
  ∀ N : ℕ, ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ c K g₀ : ℝ, 0 < c ∧ 0 < K ∧ 1 ≤ g₀ ∧
    ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ → ∀ X₀ : State W, IsState X₀ →
      ∀ n : ℕ, ∑ k ∈ csCl N, csE g E X₀ n (csY g E R p k) ≤
        K * (Real.exp (-(c * n / g ^ 2)) + 1 / (W : ℝ) ^ (2 * p) + 1 / g ^ (4 * p * m) +
          1 / g ^ (4 * p * R))

/-- The moment bound for `|F_k|^{2p}` on the closed index set of radius `N`, with the
`g^{−4pm}` term of the `m`-th level. -/
private def CsPF (R p m : ℕ) : Prop :=
  ∀ N : ℕ, ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ c K g₀ : ℝ, 0 < c ∧ 0 < K ∧ 1 ≤ g₀ ∧
    ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ → ∀ X₀ : State W, IsState X₀ →
      ∀ n : ℕ, ∑ k ∈ csCl N, csE g E X₀ n (csZ g E R p k) ≤
        K * (Real.exp (-(c * n / g ^ 2)) + 1 / (W : ℝ) ^ p + 1 / g ^ (4 * p * m) +
          1 / g ^ (4 * p * R))

private lemma cs_PM_zero (R p : ℕ) : CsPM R p 0 := by
  intro N
  obtain ⟨E₁, hE₁, B, g₀, hB, hg₀, hcr⟩ := cs_crude R p N
  refine ⟨E₁, hE₁, 1, (csCl N).card * B + 1, g₀, one_pos, by positivity, hg₀,
    fun W hW g hg E hE X₀ hX₀ n => ?_⟩
  have hg1 : 1 ≤ g := hg₀.trans hg
  have h1 : ∑ k ∈ csCl N, csE g E X₀ n (csY g E R p k) ≤ ∑ k ∈ csCl N, B :=
    Finset.sum_le_sum fun k hk => csE_le g E hX₀ (cs_tame_Y g E R p hW hg1 k)
      (fun X hX => (hcr W hW g hg E hE X hX k hk).1) n
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have e1 : 0 ≤ Real.exp (-(1 * n / g ^ 2)) := (Real.exp_pos _).le
  have e2 : 0 ≤ 1 / (W : ℝ) ^ (2 * p) := by positivity
  have e3 : 0 ≤ 1 / g ^ (4 * p * R) := by
    have : 0 < g := by linarith
    positivity
  simp only [Nat.mul_zero, pow_zero, div_one]
  have hc : (0 : ℝ) ≤ (csCl N).card * B := by positivity
  nlinarith

private lemma cs_PF_zero (R p : ℕ) : CsPF R p 0 := by
  intro N
  obtain ⟨E₁, hE₁, B, g₀, hB, hg₀, hcr⟩ := cs_crude R p N
  refine ⟨E₁, hE₁, 1, (csCl N).card * B + 1, g₀, one_pos, by positivity, hg₀,
    fun W hW g hg E hE X₀ hX₀ n => ?_⟩
  have hg1 : 1 ≤ g := hg₀.trans hg
  have h1 : ∑ k ∈ csCl N, csE g E X₀ n (csZ g E R p k) ≤ ∑ k ∈ csCl N, B :=
    Finset.sum_le_sum fun k hk => csE_le g E hX₀ (cs_tame_Z g E R p hW hg1 k)
      (fun X hX => (hcr W hW g hg E hE X hX k hk).2) n
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have e1 : 0 ≤ Real.exp (-(1 * n / g ^ 2)) := (Real.exp_pos _).le
  have e2 : 0 ≤ 1 / (W : ℝ) ^ p := by positivity
  have e3 : 0 ≤ 1 / g ^ (4 * p * R) := by
    have : 0 < g := by linarith
    positivity
  simp only [Nat.mul_zero, pow_zero, div_one]
  have hc : (0 : ℝ) ≤ (csCl N).card * B := by positivity
  nlinarith

/-! ### The induction on the order of the Taylor term -/

private lemma cs_pow_succ (g : ℝ) (p m : ℕ) :
    1 / g ^ (4 * p * (m + 1)) = 1 / g ^ (4 * p) * (1 / g ^ (4 * p * m)) := by
  rw [show 4 * p * (m + 1) = 4 * p + 4 * p * m by ring, pow_add, one_div_mul_one_div]

private lemma cs_weighted_ge {J : Finset NzInt} {u : NzInt → ℝ} {δ : ℝ} (hδ : ∀ k ∈ J, δ ≤ u k)
    {a : NzInt → ℝ} (ha : ∀ k, 0 ≤ a k) : δ * ∑ k ∈ J, a k ≤ ∑ k ∈ J, u k * a k := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hδ k hk) (ha k)

private lemma cs_final {δ Xe Cc e w q t Kc a : ℝ} (hδ : 0 < δ) (hXe : 0 ≤ Xe) (hCc : 0 ≤ Cc)
    (he : 0 ≤ e) (hw : 0 ≤ w) (hq : 0 ≤ q) (ht : 0 ≤ t) (hKc : Kc ≤ Cc * (w + q + t))
    (ha : a ≤ 1 / δ * (e * Xe + Kc)) : a ≤ 1 / δ * (Xe + Cc) * (e + w + q + t) := by
  have h1 : e * Xe + Kc ≤ (Xe + Cc) * (e + w + q + t) := by
    nlinarith [mul_nonneg hXe (add_nonneg (add_nonneg hw hq) ht), mul_nonneg hCc he]
  rw [mul_assoc]
  exact ha.trans (mul_le_mul_of_nonneg_left h1 (by positivity))

private lemma cs_E_srcM (g E : ℝ) (R p : ℕ) {W : ℕ} (hW : 1 ≤ W) (hg : 1 ≤ g) {X₀ : State W}
    (hX₀ : IsState X₀) (J' : Finset NzInt) (κ a b c : ℝ) (n : ℕ) :
    csE g E X₀ n (fun X => κ * (a + b * ∑ k ∈ J', csY g E R p k X + c)) =
      κ * (a + b * ∑ k ∈ J', csE g E X₀ n (csY g E R p k) + c) := by
  have hS : CsTame (fun X => ∑ k ∈ J', csY g E R p k X) :=
    cs_tame_sum J' fun k => cs_tame_Y g E R p hW hg k
  have h1 : CsTame (fun X => a + b * ∑ k ∈ J', csY g E R p k X) :=
    cs_tame_add (cs_tame_const a) (cs_tame_mul_left b hS)
  rw [csE_mul_left, csE_add g E hX₀ h1 (cs_tame_const c),
    csE_add g E hX₀ (cs_tame_const a) (cs_tame_mul_left b hS), csE_const, csE_const,
    csE_mul_left, csE_sum g E hX₀ J' fun k => cs_tame_Y g E R p hW hg k]

private lemma cs_src_boundM {a s K₂ e w q t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hK₂ : 0 ≤ K₂)
    (he : 0 ≤ e) (hw : 0 ≤ w) (ht : 0 ≤ t) (hs : s ≤ K₂ * (e + w + q + t)) :
    w + a * s + t ≤ K₂ * e + (1 + K₂) * w + K₂ * (a * q) + (1 + K₂) * t := by
  have h1 : a * s ≤ a * (K₂ * (e + w + q + t)) := mul_le_mul_of_nonneg_left hs ha0
  have h2 : a * (K₂ * (e + w + q + t)) = K₂ * (a * e) + K₂ * (a * w) + K₂ * (a * q) +
    K₂ * (a * t) := by ring
  have h3 : a * e ≤ e := by nlinarith
  have h4 : a * w ≤ w := by nlinarith
  have h5 : a * t ≤ t := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hK₂, mul_le_mul_of_nonneg_left h4 hK₂,
    mul_le_mul_of_nonneg_left h5 hK₂]

private lemma cs_PM_succ (R : ℕ) (hR : 2 ≤ R) {p : ℕ} (hp : 1 ≤ p) {m : ℕ} (hm : CsPM R p m) :
    CsPM R p (m + 1) := by
  intro N
  obtain ⟨J', hJJ', u, v, huv, E₁, hE₁, c₁, K₁, g₁, hc₁, hK₁, hg₁, hcon⟩ :=
    moment_contraction_corrObs R hR (csCl N) (cs_cl_closed N) hp
  obtain ⟨E₂, hE₂, c₂, K₂, g₂, hc₂, hK₂, hg₂, hIH⟩ := hm (J'.sup fun k => k.1.natAbs)
  obtain ⟨E₃, hE₃, B, g₃, hB, hg₃, hcr⟩ := cs_crude R p N
  obtain ⟨δ, hδ, hδu⟩ := cs_exists_min (csCl N) u fun k => (huv k).1
  set S : ℝ := ∑ k ∈ csCl N, u k with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => (huv k).1.le
  have hXe : 0 ≤ S * B + 2 * K₁ * K₂ / c₁ := by positivity
  have hCc : 0 < K₁ * (1 + K₂) / c₁ := by positivity
  refine ⟨min (min E₁ E₂) E₃, lt_min (lt_min hE₁ hE₂) hE₃, min c₁ c₂ / 2,
    1 / δ * (S * B + 2 * K₁ * K₂ / c₁ + K₁ * (1 + K₂) / c₁), max (max g₁ g₂) (max g₃ c₁),
    half_pos (lt_min hc₁ hc₂), by positivity, le_max_of_le_left (le_max_of_le_left hg₁),
    fun W hW g hg E hE X₀ hX₀ n => ?_⟩
  have hg₁' : g₁ ≤ g := (le_max_left _ _).trans ((le_max_left _ _).trans hg)
  have hg₂' : g₂ ≤ g := (le_max_right _ _).trans ((le_max_left _ _).trans hg)
  have hg₃' : g₃ ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hcg : c₁ ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have hg1 : 1 ≤ g := hg₁.trans hg₁'
  have hg0 : 0 < g := by linarith
  have hE₁' : |E| ≤ E₁ := hE.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hE₂' : |E| ≤ E₂ := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hE₃' : |E| ≤ E₃ := hE.trans (min_le_right _ _)
  have hY : ∀ k, CsTame (csY g E R p (W := W) k) := fun k => cs_tame_Y g E R p hW hg1 k
  have hψ : CsTame (fun X : State W => K₁ / g ^ 2 * (1 / (W : ℝ) ^ (2 * p) +
      1 / g ^ (4 * p) * ∑ k ∈ J', csY g E R p k X + 1 / g ^ (4 * p * R))) :=
    cs_tame_mul_left _ (cs_tame_add (cs_tame_add (cs_tame_const _)
      (cs_tame_mul_left _ (cs_tame_sum J' hY))) (cs_tame_const _))
  have hrec := fun n => cs_wrec g E hX₀ (csCl N) hY (fun k X => cs_Y_nonneg g E R p k X) u
    (fun k => (huv k).1) hψ (γ := c₁ / g ^ 2) (fun X hX => (hcon W hW g hg₁' E hE₁' X hX).1) n
  have hnn : ∀ n k, 0 ≤ csE g E X₀ n (csY g E R p k) := fun n k =>
    csE_nonneg g E X₀ (cs_Y_nonneg g E R p k) n
  set x : ℕ → ℝ := fun n => ∑ k ∈ csCl N, u k * csE g E X₀ n (csY g E R p k) with hx
  set a : ℕ → ℝ := fun n => ∑ k ∈ csCl N, csE g E X₀ n (csY g E R p k) with ha
  set r : ℕ → ℝ := fun n => 1 / (W : ℝ) ^ (2 * p) +
    1 / g ^ (4 * p) * ∑ k ∈ J', csE g E X₀ n (csY g E R p k) + 1 / g ^ (4 * p * R) with hr
  have hxrec : ∀ n, x (n + 1) ≤ (1 - c₁ / g ^ 2) * x n + K₁ / g ^ 2 * r n := by
    intro n
    have := hrec n
    rw [cs_E_srcM g E R p hW hg1 hX₀ J' _ _ _ _ n] at this
    exact this
  have hx0 : 0 ≤ x 0 := Finset.sum_nonneg fun k _ => mul_nonneg (huv k).1.le (hnn 0 k)
  have hx0b : x 0 ≤ S * B := by
    calc x 0 ≤ ∑ k ∈ csCl N, u k * B := Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_left (csE_le g E hX₀ (hY k)
            (fun X hX => (hcr W hW g hg₃' E hE₃' X hX k hk).1) 0) (huv k).1.le
      _ = S * B := by rw [← Finset.sum_mul]
  have hw0 : 0 ≤ 1 / (W : ℝ) ^ (2 * p) := by positivity
  have hq0 : 0 ≤ 1 / g ^ (4 * p * (m + 1)) := by positivity
  have ht0 : 0 ≤ 1 / g ^ (4 * p * R) := by positivity
  have hrb : ∀ n, r n ≤ K₂ * Real.exp (-(c₂ * n / g ^ 2)) +
      ((1 + K₂) * (1 / (W : ℝ) ^ (2 * p)) + K₂ * (1 / g ^ (4 * p * (m + 1))) +
        (1 + K₂) * (1 / g ^ (4 * p * R))) := by
    intro n
    have hs : ∑ k ∈ J', csE g E X₀ n (csY g E R p k) ≤ K₂ * (Real.exp (-(c₂ * n / g ^ 2)) +
        1 / (W : ℝ) ^ (2 * p) + 1 / g ^ (4 * p * m) + 1 / g ^ (4 * p * R)) :=
      (Finset.sum_le_sum_of_subset_of_nonneg (cs_sub_cl J') fun k _ _ => hnn n k).trans
        (hIH W hW g hg₂' E hE₂' X₀ hX₀ n)
    have h1 := cs_src_boundM (a := 1 / g ^ (4 * p)) (by positivity)
      ((div_le_one (pow_pos hg0 _)).mpr (one_le_pow₀ hg1)) hK₂.le (Real.exp_pos _).le hw0 ht0 hs
    have h2 := cs_pow_succ g p m
    simp only [hr, h2]
    linarith
  have hax : ∀ n, δ * a n ≤ x n := fun n =>
    cs_weighted_ge (J := csCl N) (u := u) hδu (a := fun k => csE g E X₀ n (csY g E R p k)) (hnn n)
  have hclose := cs_close hc₁ hc₂ hK₁ hg1 hcg hK₂.le (by positivity) hδ hx0 hx0b hxrec hrb hax n
  refine cs_final hδ hXe hCc.le (Real.exp_pos _).le hw0 hq0 ht0 ?_ hclose
  calc K₁ * ((1 + K₂) * (1 / (W : ℝ) ^ (2 * p)) + K₂ * (1 / g ^ (4 * p * (m + 1))) +
        (1 + K₂) * (1 / g ^ (4 * p * R))) / c₁
      ≤ K₁ * (1 + K₂) * (1 / (W : ℝ) ^ (2 * p) + 1 / g ^ (4 * p * (m + 1)) +
        1 / g ^ (4 * p * R)) / c₁ :=
        div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hK₁.le hq0]) hc₁.le
    _ = _ := by ring

private lemma cs_E_srcF (g E : ℝ) (R p : ℕ) {W : ℕ} (hW : 1 ≤ W) (hg : 1 ≤ g) {X₀ : State W}
    (hX₀ : IsState X₀) (J' : Finset NzInt) (κ a b c : ℝ) (n : ℕ) :
    csE g E X₀ n (fun X => κ * (a + ∑ k ∈ J', csY g E R p k X +
        b * ∑ k ∈ J', csZ g E R p k X + c)) =
      κ * (a + ∑ k ∈ J', csE g E X₀ n (csY g E R p k) +
        b * ∑ k ∈ J', csE g E X₀ n (csZ g E R p k) + c) := by
  have hSY : CsTame (fun X => ∑ k ∈ J', csY g E R p k X) :=
    cs_tame_sum J' fun k => cs_tame_Y g E R p hW hg k
  have hSZ : CsTame (fun X => ∑ k ∈ J', csZ g E R p k X) :=
    cs_tame_sum J' fun k => cs_tame_Z g E R p hW hg k
  have h1 : CsTame (fun X => a + ∑ k ∈ J', csY g E R p k X) :=
    cs_tame_add (cs_tame_const a) hSY
  have h2 : CsTame (fun X => a + ∑ k ∈ J', csY g E R p k X + b * ∑ k ∈ J', csZ g E R p k X) :=
    cs_tame_add h1 (cs_tame_mul_left b hSZ)
  rw [csE_mul_left, csE_add g E hX₀ h2 (cs_tame_const c),
    csE_add g E hX₀ h1 (cs_tame_mul_left b hSZ), csE_add g E hX₀ (cs_tame_const a) hSY,
    csE_const, csE_const, csE_mul_left, csE_sum g E hX₀ J' fun k => cs_tame_Y g E R p hW hg k,
    csE_sum g E hX₀ J' fun k => cs_tame_Z g E R p hW hg k]

private lemma cs_src_boundF {a sM sF KM KF e w q t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hKF : 0 ≤ KF) (he : 0 ≤ e) (hw : 0 ≤ w) (ht : 0 ≤ t)
    (hsM : sM ≤ KM * (e + w + t + t)) (hsF : sF ≤ KF * (e + w + q + t)) :
    w + sM + a * sF + t ≤
      (KM + KF) * e + (1 + KM + KF) * w + KF * (a * q) + (1 + 2 * KM + KF) * t := by
  have h1 : a * sF ≤ a * (KF * (e + w + q + t)) := mul_le_mul_of_nonneg_left hsF ha0
  have h2 : a * (KF * (e + w + q + t)) = KF * (a * e) + KF * (a * w) + KF * (a * q) +
    KF * (a * t) := by ring
  have h3 : a * e ≤ e := by nlinarith
  have h4 : a * w ≤ w := by nlinarith
  have h5 : a * t ≤ t := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hKF, mul_le_mul_of_nonneg_left h4 hKF,
    mul_le_mul_of_nonneg_left h5 hKF]

private lemma cs_exp_mono {c c' g : ℝ} (hc : c' ≤ c) (n : ℕ) :
    Real.exp (-(c * n / g ^ 2)) ≤ Real.exp (-(c' * n / g ^ 2)) := by
  apply Real.exp_le_exp.mpr
  have : c' * n / g ^ 2 ≤ c * n / g ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg n)) (sq_nonneg g)
  linarith

private lemma cs_PF_succ (R : ℕ) (hR : 2 ≤ R) {p : ℕ} (hp : 1 ≤ p) (hM : CsPM R p R) {m : ℕ}
    (hm : CsPF R p m) : CsPF R p (m + 1) := by
  intro N
  obtain ⟨J', hJJ', u, v, huv, E₁, hE₁, c₁, K₁, g₁, hc₁, hK₁, hg₁, hcon⟩ :=
    moment_contraction_corrObs R hR (csCl N) (cs_cl_closed N) hp
  obtain ⟨E₂, hE₂, cM, KM, g₂, hcM, hKM, hg₂, hIHM⟩ := hM (J'.sup fun k => k.1.natAbs)
  obtain ⟨E₃, hE₃, cF, KF, g₃, hcF, hKF, hg₃, hIHF⟩ := hm (J'.sup fun k => k.1.natAbs)
  obtain ⟨E₄, hE₄, B, g₄, hB, hg₄, hcr⟩ := cs_crude R p N
  obtain ⟨δ, hδ, hδv⟩ := cs_exists_min (csCl N) v fun k => (huv k).2
  set S : ℝ := ∑ k ∈ csCl N, v k with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => (huv k).2.le
  have hXe : 0 ≤ S * B + 2 * K₁ * (KM + KF) / c₁ := by positivity
  have hCc : 0 < K₁ * (1 + 2 * KM + KF) / c₁ := by positivity
  refine ⟨min (min E₁ E₂) (min E₃ E₄), lt_min (lt_min hE₁ hE₂) (lt_min hE₃ hE₄),
    min c₁ (min cM cF) / 2,
    1 / δ * (S * B + 2 * K₁ * (KM + KF) / c₁ + K₁ * (1 + 2 * KM + KF) / c₁),
    max (max g₁ g₂) (max (max g₃ g₄) c₁), half_pos (lt_min hc₁ (lt_min hcM hcF)), by positivity,
    le_max_of_le_left (le_max_of_le_left hg₁), fun W hW g hg E hE X₀ hX₀ n => ?_⟩
  have hg₁' : g₁ ≤ g := (le_max_left _ _).trans ((le_max_left _ _).trans hg)
  have hg₂' : g₂ ≤ g := (le_max_right _ _).trans ((le_max_left _ _).trans hg)
  have hg₃' : g₃ ≤ g := (le_max_left _ _).trans ((le_max_left _ _).trans
    ((le_max_right _ _).trans hg))
  have hg₄' : g₄ ≤ g := (le_max_right _ _).trans ((le_max_left _ _).trans
    ((le_max_right _ _).trans hg))
  have hcg : c₁ ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have hg1 : 1 ≤ g := hg₁.trans hg₁'
  have hg0 : 0 < g := by linarith
  have hE₁' : |E| ≤ E₁ := hE.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hE₂' : |E| ≤ E₂ := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hE₃' : |E| ≤ E₃ := hE.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hE₄' : |E| ≤ E₄ := hE.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hY : ∀ k, CsTame (csY g E R p (W := W) k) := fun k => cs_tame_Y g E R p hW hg1 k
  have hZ : ∀ k, CsTame (csZ g E R p (W := W) k) := fun k => cs_tame_Z g E R p hW hg1 k
  have hψ : CsTame (fun X : State W => K₁ / g ^ 2 * (1 / (W : ℝ) ^ p +
      ∑ k ∈ J', csY g E R p k X + 1 / g ^ (4 * p) * ∑ k ∈ J', csZ g E R p k X +
        1 / g ^ (4 * p * R))) :=
    cs_tame_mul_left _ (cs_tame_add (cs_tame_add (cs_tame_add (cs_tame_const _)
      (cs_tame_sum J' hY)) (cs_tame_mul_left _ (cs_tame_sum J' hZ))) (cs_tame_const _))
  have hrec := fun n => cs_wrec g E hX₀ (csCl N) hZ (fun k X => cs_Z_nonneg g E R p k X) v
    (fun k => (huv k).2) hψ (γ := c₁ / g ^ 2) (fun X hX => (hcon W hW g hg₁' E hE₁' X hX).2) n
  have hnnY : ∀ n k, 0 ≤ csE g E X₀ n (csY g E R p k) := fun n k =>
    csE_nonneg g E X₀ (cs_Y_nonneg g E R p k) n
  have hnn : ∀ n k, 0 ≤ csE g E X₀ n (csZ g E R p k) := fun n k =>
    csE_nonneg g E X₀ (cs_Z_nonneg g E R p k) n
  set x : ℕ → ℝ := fun n => ∑ k ∈ csCl N, v k * csE g E X₀ n (csZ g E R p k) with hx
  set a : ℕ → ℝ := fun n => ∑ k ∈ csCl N, csE g E X₀ n (csZ g E R p k) with ha
  set r : ℕ → ℝ := fun n => 1 / (W : ℝ) ^ p + ∑ k ∈ J', csE g E X₀ n (csY g E R p k) +
    1 / g ^ (4 * p) * ∑ k ∈ J', csE g E X₀ n (csZ g E R p k) + 1 / g ^ (4 * p * R) with hr
  have hxrec : ∀ n, x (n + 1) ≤ (1 - c₁ / g ^ 2) * x n + K₁ / g ^ 2 * r n := by
    intro n
    have := hrec n
    rw [cs_E_srcF g E R p hW hg1 hX₀ J' _ _ _ _ n] at this
    exact this
  have hx0 : 0 ≤ x 0 := Finset.sum_nonneg fun k _ => mul_nonneg (huv k).2.le (hnn 0 k)
  have hx0b : x 0 ≤ S * B := by
    calc x 0 ≤ ∑ k ∈ csCl N, v k * B := Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_left (csE_le g E hX₀ (hZ k)
            (fun X hX => (hcr W hW g hg₄' E hE₄' X hX k hk).2) 0) (huv k).2.le
      _ = S * B := by rw [← Finset.sum_mul]
  have hw0 : 0 ≤ 1 / (W : ℝ) ^ p := by positivity
  have hq0 : 0 ≤ 1 / g ^ (4 * p * (m + 1)) := by positivity
  have ht0 : 0 ≤ 1 / g ^ (4 * p * R) := by positivity
  have hWle : 1 / (W : ℝ) ^ (2 * p) ≤ 1 / (W : ℝ) ^ p :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by exact_mod_cast hW) (by omega))
  have hrb : ∀ n, r n ≤ (KM + KF) * Real.exp (-(min cM cF * n / g ^ 2)) +
      ((1 + KM + KF) * (1 / (W : ℝ) ^ p) + KF * (1 / g ^ (4 * p * (m + 1))) +
        (1 + 2 * KM + KF) * (1 / g ^ (4 * p * R))) := by
    intro n
    have hsM : ∑ k ∈ J', csE g E X₀ n (csY g E R p k) ≤ KM * (Real.exp (-(min cM cF * n / g ^ 2)) +
        1 / (W : ℝ) ^ p + 1 / g ^ (4 * p * R) + 1 / g ^ (4 * p * R)) := by
      refine ((Finset.sum_le_sum_of_subset_of_nonneg (cs_sub_cl J') fun k _ _ => hnnY n k).trans
        (hIHM W hW g hg₂' E hE₂' X₀ hX₀ n)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hKM.le
      have := cs_exp_mono (g := g) (min_le_left cM cF) n
      linarith
    have hsF : ∑ k ∈ J', csE g E X₀ n (csZ g E R p k) ≤ KF * (Real.exp (-(min cM cF * n / g ^ 2)) +
        1 / (W : ℝ) ^ p + 1 / g ^ (4 * p * m) + 1 / g ^ (4 * p * R)) := by
      refine ((Finset.sum_le_sum_of_subset_of_nonneg (cs_sub_cl J') fun k _ _ => hnn n k).trans
        (hIHF W hW g hg₃' E hE₃' X₀ hX₀ n)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hKF.le
      have := cs_exp_mono (g := g) (min_le_right cM cF) n
      linarith
    have h1 := cs_src_boundF (a := 1 / g ^ (4 * p)) (by positivity)
      ((div_le_one (pow_pos hg0 _)).mpr (one_le_pow₀ hg1)) hKF.le (Real.exp_pos _).le hw0
      ht0 hsM hsF
    have h2 := cs_pow_succ g p m
    simp only [hr, h2]
    linarith
  have hax : ∀ n, δ * a n ≤ x n := fun n =>
    cs_weighted_ge (J := csCl N) (u := v) hδv (a := fun k => csE g E X₀ n (csZ g E R p k)) (hnn n)
  have hclose := cs_close (c₂ := min cM cF) hc₁ (lt_min hcM hcF) hK₁ hg1 hcg
    (by positivity : 0 ≤ KM + KF) (by positivity) hδ hx0 hx0b hxrec hrb hax n
  refine cs_final hδ hXe hCc.le (Real.exp_pos _).le hw0 hq0 ht0 ?_ hclose
  have hdiff := mul_nonneg hK₁.le (add_nonneg (mul_nonneg hKM.le hw0)
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + 2 * KM) hq0))
  calc K₁ * ((1 + KM + KF) * (1 / (W : ℝ) ^ p) + KF * (1 / g ^ (4 * p * (m + 1))) +
        (1 + 2 * KM + KF) * (1 / g ^ (4 * p * R))) / c₁
      ≤ K₁ * (1 + 2 * KM + KF) * (1 / (W : ℝ) ^ p + 1 / g ^ (4 * p * (m + 1)) +
        1 / g ^ (4 * p * R)) / c₁ := div_le_div_of_nonneg_right (by nlinarith [hdiff]) hc₁.le
    _ = _ := by ring

/-! ### The event (11.44) [lg:eq:burnevent] -/

private lemma cs_chain_congr (g E : ℝ) {W : ℕ} (X₀ : State W)
    {V V' : ℕ → Matrix (Fin W) (Fin W) ℂ} {i : ℕ} (h : ∀ k < i, V k = V' k) :
    chainState g E X₀ V i = chainState g E X₀ V' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change stepState g E (chainState g E X₀ V i) (V i) =
      stepState g E (chainState g E X₀ V' i) (V' i)
    rw [ih fun k hk => h k (Nat.lt_succ_of_lt hk), h i (Nat.lt_succ_self i)]

/-- The law of the first `n` blocks under `μ W N` is `μ W n`, and the chain at step `n` reads
only the first `n` blocks. -/
private lemma cs_marginal (g E : ℝ) {W : ℕ} (X₀ : State W) {n N : ℕ} (hnN : n ≤ N)
    {f : State W → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (chainState g E X₀ (csBlocks N ω) n) ∂(μ W N) =
      ∫⁻ ω, f (chainState g E X₀ (csBlocks n ω) n) ∂(μ W n) := by
  let s : Fin n → Fin N := fun i => ⟨i.1, lt_of_lt_of_le i.2 hnN⟩
  have hs : Function.Injective s := fun i j h => Fin.ext (by simpa [s] using congrArg Fin.val h)
  have hmp := measurePreserving_windowSample W N n hs
  have hmeas : Measurable fun ω : Ω W n => f (chainState g E X₀ (csBlocks n ω) n) :=
    hf.comp (cs_measurable_chain g E X₀ n n)
  rw [← hmp.lintegral_comp hmeas]
  refine lintegral_congr fun ω => ?_
  have hc := cs_chain_congr g E X₀ (V := csBlocks N ω) (V' := csBlocks n (windowSample s ω))
    (i := n) fun k hk => by
      have hkN : k < N := lt_of_lt_of_le hk hnN
      simp only [csBlocks, hk, hkN, dite_true]
      exact (gueBlock_windowSample s ω ⟨k, hk⟩).symm
  rw [hc]

/-- Markov's inequality for `φ(X_n)` under `μ W N`, `n ≤ N`. -/
private lemma cs_markov (g E : ℝ) {W : ℕ} {X₀ : State W} (hX₀ : IsState X₀) {φ : State W → ℝ}
    (hφ : CsTame φ) (h0 : ∀ X, 0 ≤ φ X) {n N : ℕ} (hnN : n ≤ N) {t : ℝ} (ht : 0 < t) :
    μ W N {ω | t ≤ φ (chainState g E X₀ (csBlocks N ω) n)} ≤
      ENNReal.ofReal (csE g E X₀ n φ / t) := by
  have hmeas : Measurable fun ω : Ω W N =>
      ENNReal.ofReal (φ (chainState g E X₀ (csBlocks N ω) n)) :=
    ENNReal.measurable_ofReal.comp (hφ.1.comp (cs_measurable_chain g E X₀ N n))
  have h1 := meas_ge_le_lintegral_div (μ := μ W N) hmeas.aemeasurable
    (ε := ENNReal.ofReal t) (by simpa using ht) ENNReal.ofReal_ne_top
  have h2 : {ω | t ≤ φ (chainState g E X₀ (csBlocks N ω) n)} ⊆
      {ω | ENNReal.ofReal t ≤ ENNReal.ofReal (φ (chainState g E X₀ (csBlocks N ω) n))} :=
    fun ω hω => ENNReal.ofReal_le_ofReal hω
  refine (measure_mono h2).trans (h1.trans (le_of_eq ?_))
  have hm := cs_marginal g E X₀ hnN (f := fun X => ENNReal.ofReal (φ X))
    (ENNReal.measurable_ofReal.comp hφ.1)
  beta_reduce at hm
  rw [hm, ENNReal.ofReal_div_of_pos ht,
    ← ofReal_integral_eq_lintegral_ofReal (cs_integrable g E hX₀ hφ n)
      (Filter.Eventually.of_forall fun ω => h0 _)]
  rfl

private lemma cs_tail {K L Q θ a₁ a₂ a₃ x E₁ E₂ E₃ : ℝ} (hK : 0 ≤ K)
    (hx : x ≤ K * (E₁ + E₂ + E₃)) (h1 : E₁ ≤ Real.exp (-(a₁ * L)))
    (h2 : E₂ ≤ Real.exp (-(a₂ * L))) (h3 : E₃ ≤ Real.exp (-(a₃ * L))) (hL : 0 ≤ L)
    (c₁ : Q ≤ a₁ + θ) (c₂ : Q ≤ a₂ + θ) (c₃ : Q ≤ a₃ + θ) :
    x / Real.exp (θ * L) ≤ 3 * K * Real.exp (-(Q * L)) := by
  have hp : 0 < Real.exp (θ * L) := Real.exp_pos _
  have key : ∀ {E a : ℝ}, E ≤ Real.exp (-(a * L)) → Q ≤ a + θ →
      E / Real.exp (θ * L) ≤ Real.exp (-(Q * L)) := by
    intro E a hE hc
    rw [div_le_iff₀ hp, ← Real.exp_add]
    refine hE.trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  have := div_le_div_of_nonneg_right hx hp.le
  have e : K * (E₁ + E₂ + E₃) / Real.exp (θ * L) =
      K * (E₁ / Real.exp (θ * L) + E₂ / Real.exp (θ * L) + E₃ / Real.exp (θ * L)) := by
    field_simp
  rw [e] at this
  refine this.trans ?_
  nlinarith [mul_le_mul_of_nonneg_left (key h1 c₁) hK, mul_le_mul_of_nonneg_left (key h2 c₂) hK,
    mul_le_mul_of_nonneg_left (key h3 c₃) hK]

private lemma cs_union {Ks : Finset NzInt} {W N : ℕ} (nstar : ℕ) {S : Set (Ω W N)}
    {SA SB : NzInt → ℕ → Set (Ω W N)}
    (hS : S ⊆ ⋃ k ∈ Ks, ⋃ n ∈ Finset.Icc nstar N, (SA k n ∪ SB k n)) {τ : ℝ≥0∞}
    (hA : ∀ k ∈ Ks, ∀ n ∈ Finset.Icc nstar N, μ W N (SA k n) ≤ τ)
    (hB : ∀ k ∈ Ks, ∀ n ∈ Finset.Icc nstar N, μ W N (SB k n) ≤ τ) :
    μ W N S ≤ (Ks.card : ℝ≥0∞) * ((N : ℝ≥0∞) + 1) * (τ + τ) := by
  calc μ W N S ≤ μ W N (⋃ k ∈ Ks, ⋃ n ∈ Finset.Icc nstar N, (SA k n ∪ SB k n)) :=
        measure_mono hS
    _ ≤ ∑ k ∈ Ks, μ W N (⋃ n ∈ Finset.Icc nstar N, (SA k n ∪ SB k n)) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Ks, ∑ n ∈ Finset.Icc nstar N, μ W N (SA k n ∪ SB k n) :=
        Finset.sum_le_sum fun k _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Ks, ∑ n ∈ Finset.Icc nstar N, (τ + τ) :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun n hn =>
          (measure_union_le _ _).trans (add_le_add (hA k hk n hn) (hB k hk n hn))
    _ = (Ks.card : ℝ≥0∞) * (((Finset.Icc nstar N).card : ℕ) : ℝ≥0∞) * (τ + τ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (Ks.card : ℝ≥0∞) * ((N : ℝ≥0∞) + 1) * (τ + τ) := by
        gcongr
        have : (Finset.Icc nstar N).card ≤ N + 1 := by
          rw [Nat.card_Icc]; omega
        exact_mod_cast this

/-- `1 / w^m = e^{−m log w}`. -/
private lemma cs_inv_pow {w : ℝ} (hw : 0 < w) (m : ℕ) :
    1 / w ^ m = Real.exp (-(m * Real.log w)) := by
  rw [Real.exp_neg, ← one_div, Real.exp_nat_mul, Real.exp_log hw]

private lemma cs_rpow_exp {w : ℝ} (hw : 0 < w) (x : ℝ) : w ^ x = Real.exp (x * Real.log w) := by
  rw [Real.rpow_def_of_pos hw, mul_comm]

/-- The three terms of the moment bound, divided by the threshold power `e^{θ log w}`, are at most
`w^{−Q}`: the transient term for `n ≥ (2p + Q)/c · g² log w`, the width term `w^{−lam}` and the
Taylor term `g^{−4pR}` for `g ≥ w^ε`, `2εR > 1`. -/
private lemma cs_tail_all {w g c K x ε Q θ : ℝ} {p R lam : ℕ} (hK : 0 ≤ K) (hc : 0 < c)
    (hw : 1 < w) (hεR : 1 < 2 * ε * R) (hp : 1 ≤ p) (hg : w ^ ε ≤ g) {n : ℕ}
    (hn : (2 * p + Q) / c * g ^ 2 * Real.log w ≤ n)
    (hx : x ≤ K * (Real.exp (-(c * n / g ^ 2)) + 1 / w ^ lam + 1 / g ^ (4 * p * R)))
    (hθ1 : -(2 * p) ≤ θ) (hθ2 : Q ≤ lam + θ) (hθ3 : Q ≤ 2 * p + θ) :
    x / Real.exp (θ * Real.log w) ≤ 3 * K * Real.exp (-(Q * Real.log w)) := by
  have hw0 : 0 < w := by linarith
  have hL : 0 < Real.log w := Real.log_pos hw
  have hg0 : 0 < g := lt_of_lt_of_le (Real.rpow_pos_of_pos hw0 ε) hg
  have hp0 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  refine cs_tail (a₁ := 2 * p + Q) (a₂ := lam) (a₃ := 2 * p) hK hx ?_ ?_ ?_ hL.le (by linarith)
    hθ2 hθ3
  · apply Real.exp_le_exp.mpr
    have h1 : c * ((2 * p + Q) / c * g ^ 2 * Real.log w) / g ^ 2 ≤ c * n / g ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn hc.le) (sq_nonneg g)
    have h2 : c * ((2 * p + Q) / c * g ^ 2 * Real.log w) / g ^ 2 = (2 * p + Q) * Real.log w := by
      field_simp
    linarith
  · exact (cs_inv_pow hw0 lam).le
  · have h2 : Real.exp (2 * p * Real.log w) ≤ g ^ (4 * p * R) := by
      have h3 : (w ^ ε) ^ (4 * p * R) ≤ g ^ (4 * p * R) :=
        pow_le_pow_left₀ (Real.rpow_pos_of_pos hw0 ε).le hg _
      refine le_trans ?_ h3
      rw [cs_rpow_exp hw0 ε, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < p) hL) (sub_pos.mpr hεR)]
    calc 1 / g ^ (4 * p * R) ≤ 1 / Real.exp (2 * p * Real.log w) :=
          one_div_le_one_div_of_le (Real.exp_pos _) h2
      _ = Real.exp (-(2 * p * Real.log w)) := by rw [one_div, Real.exp_neg]

/-- (11.60) [lg:eq:momentout]: `𝔼|M_{k,n} − a_k|^{2p} ≤ K(e^{−c n/g²} + W^{−2p} + g^{−4pR})` and
`𝔼|F_{k,n}|^{2p} ≤ K(e^{−c n/g²} + W^{−p} + g^{−4pR})` along the chain started at any state. -/
theorem moment_bound_corrObs (R : ℕ) (hR : 2 ≤ R) (J : Finset NzInt) {p : ℕ} (hp : 1 ≤ p) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ c K g₀ : ℝ, 0 < c ∧ 0 < K ∧ 1 ≤ g₀ ∧
      ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ → ∀ X₀ : State W, IsState X₀ →
        ∀ n : ℕ, ∀ k ∈ J,
          ∫ ω, ‖obsEval g (chainState g E X₀
              (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n) (corrObsM E R k) -
              center g E R k.1‖ ^ (2 * p) ∂(μ W n) ≤
            K * (Real.exp (-(c * n / g ^ 2)) + 1 / (W : ℝ) ^ (2 * p) + 1 / g ^ (4 * p * R)) ∧
          ∫ ω, ‖obsEval g (chainState g E X₀
              (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n)
                (corrObsF E R k)‖ ^ (2 * p) ∂(μ W n) ≤
            K * (Real.exp (-(c * n / g ^ 2)) + 1 / (W : ℝ) ^ p + 1 / g ^ (4 * p * R)) := by
  have hM : ∀ m, CsPM R p m := fun m =>
    Nat.rec (cs_PM_zero R p) (fun m ih => cs_PM_succ R hR hp ih) m
  have hF : ∀ m, CsPF R p m := fun m =>
    Nat.rec (cs_PF_zero R p) (fun m ih => cs_PF_succ R hR hp (hM R) ih) m
  obtain ⟨E₁, hE₁, cM, KM, gM, hcM, hKM, hgM, hIHM⟩ := hM R (J.sup fun k => k.1.natAbs)
  obtain ⟨E₂, hE₂, cF, KF, gF, hcF, hKF, hgF, hIHF⟩ := hF R (J.sup fun k => k.1.natAbs)
  refine ⟨min E₁ E₂, lt_min hE₁ hE₂, min cM cF, 2 * (KM + KF), max gM gF, lt_min hcM hcF,
    by positivity, le_max_of_le_left hgM, fun W hW g hg E hE X₀ hX₀ n k hk => ?_⟩
  have hg1 : 1 ≤ g := hgM.trans ((le_max_left _ _).trans hg)
  have hg0 : 0 < g := by linarith
  have hkN : k ∈ csCl (J.sup fun k => k.1.natAbs) := cs_sub_cl J hk
  have he : 0 ≤ Real.exp (-(min cM cF * n / g ^ 2)) := (Real.exp_pos _).le
  have ht : 0 ≤ 1 / g ^ (4 * p * R) := by positivity
  constructor
  · change csE g E X₀ n (csY g E R p k) ≤ _
    have h1 : csE g E X₀ n (csY g E R p k) ≤
        ∑ j ∈ csCl (J.sup fun k => k.1.natAbs), csE g E X₀ n (csY g E R p j) :=
      Finset.single_le_sum (f := fun j => csE g E X₀ n (csY g E R p j))
        (fun j _ => csE_nonneg g E X₀ (cs_Y_nonneg g E R p j) n) hkN
    have h2 := hIHM W hW g ((le_max_left _ _).trans hg) E (hE.trans (min_le_left _ _)) X₀ hX₀ n
    have h3 := cs_exp_mono (g := g) (min_le_left cM cF) n
    have h4 : (0 : ℝ) ≤ 1 / (W : ℝ) ^ (2 * p) := by positivity
    have h5 : 1 / g ^ (4 * p * R) ≤ 1 / g ^ (4 * p * R) + 1 / (W : ℝ) ^ (2 * p) := by linarith
    nlinarith [mul_nonneg hKM.le he, mul_nonneg hKM.le h4, mul_nonneg hKM.le ht,
      mul_nonneg hKF.le he, mul_nonneg hKF.le h4, mul_nonneg hKF.le ht]
  · change csE g E X₀ n (csZ g E R p k) ≤ _
    have h1 : csE g E X₀ n (csZ g E R p k) ≤
        ∑ j ∈ csCl (J.sup fun k => k.1.natAbs), csE g E X₀ n (csZ g E R p j) :=
      Finset.single_le_sum (f := fun j => csE g E X₀ n (csZ g E R p j))
        (fun j _ => csE_nonneg g E X₀ (cs_Z_nonneg g E R p j) n) hkN
    have h2 := hIHF W hW g ((le_max_right _ _).trans hg) E (hE.trans (min_le_right _ _)) X₀ hX₀ n
    have h3 := cs_exp_mono (g := g) (min_le_right cM cF) n
    have h4 : (0 : ℝ) ≤ 1 / (W : ℝ) ^ p := by positivity
    nlinarith [mul_nonneg hKM.le he, mul_nonneg hKM.le h4, mul_nonneg hKM.le ht,
      mul_nonneg hKF.le he, mul_nonneg hKF.le h4, mul_nonneg hKF.le ht]

/-- Lemma 11.8 [lg:lem:dynamic], the event (11.44) [lg:eq:burnevent]. -/
theorem corrObs_stability {ε : ℝ} (hε : 0 < ε) (R : ℕ) (hR : 2 ≤ R) (hεR : 1 < 2 * ε * R)
    (Ks : Finset NzInt) :
    ∀ D η B₁ : ℝ, 0 < D → 0 < η → 0 < B₁ →
      ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ Cs : ℝ, 0 < Cs ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, (W : ℝ) ^ ε ≤ g →
        ∀ E : ℝ, |E| ≤ E₁ → ∀ X₀ : State W, IsState X₀ → ∀ N : ℕ, (N : ℝ) ≤ (W : ℝ) ^ B₁ →
          μ W N {ω | ∃ k ∈ Ks, ∃ n : ℕ, ⌈Cs * g ^ 2 * Real.log W⌉₊ ≤ n ∧ n ≤ N ∧
              ((W : ℝ) ^ (η - 1) < ‖obsEval g (chainState g E X₀
                  (fun i => if h : i < N then gueBlock W N ω ⟨i, h⟩ else 0) n) (corrObsM E R k) -
                  center g E R k.1‖ ∨
                (W : ℝ) ^ (η - 1 / 2) < ‖obsEval g (chainState g E X₀
                  (fun i => if h : i < N then gueBlock W N ω ⟨i, h⟩ else 0) n) (corrObsF E R k)‖)} ≤
            ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  intro D η B₁ hD hη hB₁
  set Q : ℝ := B₁ + D + 2 with hQ
  have hQ0 : 0 < Q := by positivity
  set p : ℕ := ⌈Q / (2 * η)⌉₊ + 1 with hp
  have hp1 : 1 ≤ p := Nat.le_add_left 1 _
  have hpη : Q ≤ 2 * p * η := by
    have h1 : Q / (2 * η) ≤ p := by
      have := Nat.le_ceil (Q / (2 * η))
      rw [hp]; push_cast; linarith
    have h2 := (div_le_iff₀ (by positivity : 0 < 2 * η)).mp h1
    linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  have hpη0 : 0 < (p : ℝ) * η := mul_pos hp0 hη
  obtain ⟨E₁, hE₁, c, K, g₀, hc, hK, hg₀, hmom⟩ := moment_bound_corrObs R hR Ks hp1
  refine ⟨E₁, hE₁, (2 * p + Q) / c, by positivity,
    max 2 (max ⌈g₀ ^ (1 / ε)⌉₊ ⌈12 * Ks.card * K⌉₊), ?_⟩
  intro W hW g hg E hE X₀ hX₀ N hN
  have hW2 : 2 ≤ W := (le_max_left _ _).trans hW
  have hWr : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  have hw1 : 1 < (W : ℝ) := by linarith
  have hw0 : 0 < (W : ℝ) := by linarith
  have hL : 0 < Real.log (W : ℝ) := Real.log_pos hw1
  have hg0 : g₀ ≤ g := by
    have h1 : g₀ ^ (1 / ε) ≤ (W : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_left _ _).trans
        ((le_max_right _ _).trans hW)))
    calc g₀ = (g₀ ^ (1 / ε)) ^ ε := by
          rw [← Real.rpow_mul (by linarith), one_div_mul_cancel hε.ne', Real.rpow_one]
      _ ≤ (W : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) h1 hε.le
      _ ≤ g := hg
  have hg1 : 1 ≤ g := hg₀.trans hg0
  have hWK : 12 * Ks.card * K ≤ (W : ℝ) ^ 2 := by
    have h1 : 12 * (Ks.card : ℝ) * K ≤ W :=
      (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans
        ((le_max_right _ _).trans hW)))
    nlinarith
  have hn' : ∀ n : ℕ, ⌈(2 * p + Q) / c * g ^ 2 * Real.log (W : ℝ)⌉₊ ≤ n →
      (2 * p + Q) / c * g ^ 2 * Real.log (W : ℝ) ≤ n := fun n hn =>
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  set τ : ℝ := 3 * K * Real.exp (-(Q * Real.log (W : ℝ))) with hτ
  have hτ0 : 0 ≤ τ := by positivity
  have hEY : ∀ k ∈ Ks, ∀ n ∈ Finset.Icc ⌈(2 * p + Q) / c * g ^ 2 * Real.log (W : ℝ)⌉₊ N,
      μ W N {ω | (W : ℝ) ^ (η - 1) < ‖obsEval g (chainState g E X₀
          (fun i => if h : i < N then gueBlock W N ω ⟨i, h⟩ else 0) n) (corrObsM E R k) -
          center g E R k.1‖} ≤ ENNReal.ofReal τ := by
    intro k hk n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have ht₀ : 0 < (W : ℝ) ^ (η - 1) := Real.rpow_pos_of_pos hw0 _
    have hT : 0 < ((W : ℝ) ^ (η - 1)) ^ (2 * p) := pow_pos ht₀ _
    have hsub : {ω | (W : ℝ) ^ (η - 1) < ‖obsEval g (chainState g E X₀
          (fun i => if h : i < N then gueBlock W N ω ⟨i, h⟩ else 0) n) (corrObsM E R k) -
          center g E R k.1‖} ⊆ {ω | ((W : ℝ) ^ (η - 1)) ^ (2 * p) ≤
            csY g E R p k (chainState g E X₀ (csBlocks N ω) n)} :=
      fun ω hω => pow_le_pow_left₀ ht₀.le hω.le _
    refine (measure_mono hsub).trans ((cs_markov g E hX₀ (cs_tame_Y g E R p (by omega) hg1 k)
      (cs_Y_nonneg g E R p k) hn2 hT).trans (ENNReal.ofReal_le_ofReal ?_))
    have hm : csE g E X₀ n (csY g E R p k) ≤ K * (Real.exp (-(c * n / g ^ 2)) +
        1 / (W : ℝ) ^ (2 * p) + 1 / g ^ (4 * p * R)) :=
      (hmom W (by omega) g hg0 E hE X₀ hX₀ n k hk).1
    have hTe : ((W : ℝ) ^ (η - 1)) ^ (2 * p) = Real.exp ((2 * p * (η - 1)) * Real.log (W : ℝ)) := by
      rw [cs_rpow_exp hw0, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hTe]
    exact cs_tail_all (θ := 2 * p * (η - 1)) (lam := 2 * p) hK.le hc hw1 hεR hp1 hg (hn' n hn1) hm
      (by linarith) (by push_cast; linarith) (by linarith)
  have hEF : ∀ k ∈ Ks, ∀ n ∈ Finset.Icc ⌈(2 * p + Q) / c * g ^ 2 * Real.log (W : ℝ)⌉₊ N,
      μ W N {ω | (W : ℝ) ^ (η - 1 / 2) < ‖obsEval g (chainState g E X₀
          (fun i => if h : i < N then gueBlock W N ω ⟨i, h⟩ else 0) n) (corrObsF E R k)‖} ≤
        ENNReal.ofReal τ := by
    intro k hk n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have ht₀ : 0 < (W : ℝ) ^ (η - 1 / 2) := Real.rpow_pos_of_pos hw0 _
    have hT : 0 < ((W : ℝ) ^ (η - 1 / 2)) ^ (2 * p) := pow_pos ht₀ _
    have hsub : {ω | (W : ℝ) ^ (η - 1 / 2) < ‖obsEval g (chainState g E X₀
          (fun i => if h : i < N then gueBlock W N ω ⟨i, h⟩ else 0) n) (corrObsF E R k)‖} ⊆
          {ω | ((W : ℝ) ^ (η - 1 / 2)) ^ (2 * p) ≤
            csZ g E R p k (chainState g E X₀ (csBlocks N ω) n)} :=
      fun ω hω => pow_le_pow_left₀ ht₀.le hω.le _
    refine (measure_mono hsub).trans ((cs_markov g E hX₀ (cs_tame_Z g E R p (by omega) hg1 k)
      (cs_Z_nonneg g E R p k) hn2 hT).trans (ENNReal.ofReal_le_ofReal ?_))
    have hm : csE g E X₀ n (csZ g E R p k) ≤ K * (Real.exp (-(c * n / g ^ 2)) +
        1 / (W : ℝ) ^ p + 1 / g ^ (4 * p * R)) :=
      (hmom W (by omega) g hg0 E hE X₀ hX₀ n k hk).2
    have hTe : ((W : ℝ) ^ (η - 1 / 2)) ^ (2 * p) =
        Real.exp ((2 * p * (η - 1 / 2)) * Real.log (W : ℝ)) := by
      rw [cs_rpow_exp hw0, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hTe]
    exact cs_tail_all (θ := 2 * p * (η - 1 / 2)) (lam := p) hK.le hc hw1 hεR hp1 hg (hn' n hn1) hm
      (by linarith) (by linarith) (by linarith)
  clear_value τ
  have hmain := cs_union (Ks := Ks) (N := N)
    ⌈(2 * p + Q) / c * g ^ 2 * Real.log (W : ℝ)⌉₊
    (SA := fun k n => {ω | (W : ℝ) ^ (η - 1) < ‖obsEval g (chainState g E X₀
          (fun i => if h : i < N then gueBlock W N ω ⟨i, h⟩ else 0) n) (corrObsM E R k) -
          center g E R k.1‖})
    (SB := fun k n => {ω | (W : ℝ) ^ (η - 1 / 2) < ‖obsEval g (chainState g E X₀
          (fun i => if h : i < N then gueBlock W N ω ⟨i, h⟩ else 0) n) (corrObsF E R k)‖})
    (S := {ω | ∃ k ∈ Ks, ∃ n : ℕ, ⌈(2 * p + Q) / c * g ^ 2 * Real.log (W : ℝ)⌉₊ ≤ n ∧ n ≤ N ∧
        ((W : ℝ) ^ (η - 1) < ‖obsEval g (chainState g E X₀
          (fun i => if h : i < N then gueBlock W N ω ⟨i, h⟩ else 0) n) (corrObsM E R k) -
          center g E R k.1‖ ∨
        (W : ℝ) ^ (η - 1 / 2) < ‖obsEval g (chainState g E X₀
          (fun i => if h : i < N then gueBlock W N ω ⟨i, h⟩ else 0) n) (corrObsF E R k)‖)})
    (by
      rintro ω ⟨k, hk, n, hn1, hn2, h⟩
      simp only [Set.mem_iUnion]
      exact ⟨k, hk, n, Finset.mem_Icc.mpr ⟨hn1, hn2⟩, h⟩)
    hEY hEF
  refine hmain.trans ?_
  have hcount : (Ks.card : ℝ≥0∞) * ((N : ℝ≥0∞) + 1) * (ENNReal.ofReal τ + ENNReal.ofReal τ) =
      ENNReal.ofReal (Ks.card * ((N : ℝ) + 1) * (τ + τ)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add hτ0 hτ0, ENNReal.ofReal_natCast, ENNReal.ofReal_add (Nat.cast_nonneg _)
        zero_le_one]
    simp
  rw [hcount]
  refine ENNReal.ofReal_le_ofReal ?_
  have hL := Real.log_pos hw1
  have hN1 : (N : ℝ) + 1 ≤ 2 * Real.exp (B₁ * Real.log (W : ℝ)) := by
    have h1 : (N : ℝ) ≤ Real.exp (B₁ * Real.log (W : ℝ)) := by
      rw [← cs_rpow_exp hw0]; exact hN
    have h2 : 1 ≤ Real.exp (B₁ * Real.log (W : ℝ)) := Real.one_le_exp (by positivity)
    linarith
  have hw2 := cs_inv_pow hw0 2
  have hwD : (W : ℝ) ^ (-D) = Real.exp (-(D * Real.log (W : ℝ))) := by
    rw [cs_rpow_exp hw0]; congr 1; ring
  have hprod : Real.exp (B₁ * Real.log (W : ℝ)) * Real.exp (-(Q * Real.log (W : ℝ))) =
      Real.exp (-(D * Real.log (W : ℝ))) * (1 / (W : ℝ) ^ 2) := by
    rw [hw2, ← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; rw [hQ]; ring
  rw [hwD]
  have hK' : 0 ≤ (Ks.card : ℝ) := Nat.cast_nonneg _
  have hE0 := Real.exp_pos (-(D * Real.log (W : ℝ)))
  calc (Ks.card : ℝ) * ((N : ℝ) + 1) * (τ + τ)
      ≤ (Ks.card : ℝ) * (2 * Real.exp (B₁ * Real.log (W : ℝ))) * (τ + τ) := by gcongr
    _ = 12 * Ks.card * K * (Real.exp (B₁ * Real.log (W : ℝ)) *
          Real.exp (-(Q * Real.log (W : ℝ)))) := by rw [hτ]; ring
    _ = 12 * Ks.card * K / (W : ℝ) ^ 2 * Real.exp (-(D * Real.log (W : ℝ))) := by
          rw [hprod]; ring
    _ ≤ Real.exp (-(D * Real.log (W : ℝ))) := by
          have : 12 * Ks.card * K / (W : ℝ) ^ 2 ≤ 1 := by
            rw [div_le_one (by positivity)]; exact hWK
          nlinarith

end LSBA
