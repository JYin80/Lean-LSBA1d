import LSBA.Flow.NoExitMul
import LSBA.Flow.LemmaNRates
import LSBA.Flow.LemmaNOffset

/-!
# The mixed-pair bound

The mixed-pair bound at a fixed time on an admissible step: `max |D₂^{+−}| ≺ R^M ζ_u² w_u` with
`M = c_*/2 + 4`, from the pair input at the start of the step, the Step 1 envelopes at every
intermediate time, the crude moments and weighted sampling of the inputs and the regime bounds,
through the no-exit lemma with multiplicative rates applied to the surrogate of the mixed-pair
errors, with the barrier `J₀ = W^ε R^M` in place of the stopping barrier (C.17) [gc:eq:spatialstop].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Elementary facts on distances, weights and scales -/

/-- The cyclic distance is symmetric. -/
private theorem lemmaN_cycDist_comm {L : ℕ} (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

private theorem lemmaN_weight_pos (c θ F : ℝ) {W : ℕ} (hW : 1 ≤ W) (ℓ r : ℝ) :
    0 < weightFn c θ F W ℓ r := by
  unfold weightFn
  have : (0 : ℝ) < W := by exact_mod_cast hW
  positivity

private theorem lemmaN_weight_ge (c θ F : ℝ) {W : ℕ} (ℓ r : ℝ) :
    (W : ℝ) ^ (-F) ≤ weightFn c θ F W ℓ r := by
  unfold weightFn
  linarith [Real.exp_pos (-(c * (r / ℓ) ^ θ))]

private theorem lemmaN_weight_le_two {c θ F : ℝ} (hc : 0 ≤ c) (hF : 0 ≤ F) {W : ℕ} (hW : 1 ≤ W)
    {ℓ r : ℝ} (hℓ : 0 < ℓ) (hr : 0 ≤ r) : weightFn c θ F W ℓ r ≤ 2 := by
  unfold weightFn
  have h1 : Real.exp (-(c * (r / ℓ) ^ θ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (r / ℓ) ^ θ := Real.rpow_nonneg (div_nonneg hr hℓ.le) θ
    nlinarith
  have h2 : (W : ℝ) ^ (-F) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hW) (by linarith)
  linarith

/-- The weight increases with the scale. -/
private theorem lemmaN_weight_mono_ell {c θ F : ℝ} (hc : 0 ≤ c) (hθ : 0 ≤ θ) {W : ℕ}
    {ℓ ℓ' r : ℝ} (hℓ : 0 < ℓ) (hℓℓ : ℓ ≤ ℓ') (hr : 0 ≤ r) :
    weightFn c θ F W ℓ r ≤ weightFn c θ F W ℓ' r := by
  unfold weightFn
  have hℓ' : 0 < ℓ' := lt_of_lt_of_le hℓ hℓℓ
  have h1 : r / ℓ' ≤ r / ℓ := div_le_div_of_nonneg_left hr hℓ hℓℓ
  have h2 : (r / ℓ') ^ θ ≤ (r / ℓ) ^ θ := Real.rpow_le_rpow (div_nonneg hr hℓ'.le) h1 hθ
  have h3 : c * (r / ℓ') ^ θ ≤ c * (r / ℓ) ^ θ := mul_le_mul_of_nonneg_left h2 hc
  gcongr

/-- The weight decreases in the profile constant. -/
private theorem lemmaN_weight_anti_c {c c' θ F : ℝ} (hcc : c ≤ c') {W : ℕ} {ℓ r : ℝ}
    (hℓ : 0 < ℓ) (hr : 0 ≤ r) :
    weightFn c' θ F W ℓ r ≤ weightFn c θ F W ℓ r := by
  unfold weightFn
  have h0 : 0 ≤ (r / ℓ) ^ θ := Real.rpow_nonneg (div_nonneg hr hℓ.le) θ
  have : c * (r / ℓ) ^ θ ≤ c' * (r / ℓ) ^ θ := mul_le_mul_of_nonneg_right hcc h0
  gcongr

/-- The weight decreases in the floor exponent. -/
private theorem lemmaN_weight_anti_F {c θ F F' : ℝ} (hFF : F ≤ F') {W : ℕ} (hW : 1 ≤ W)
    (ℓ r : ℝ) : weightFn c θ F' W ℓ r ≤ weightFn c θ F W ℓ r := by
  unfold weightFn
  have : (W : ℝ) ^ (-F') ≤ (W : ℝ) ^ (-F) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hW) (by linarith)
  linarith

/-- The scale ratio in squared form: `ζ_u²(1 - u) ≤ ζ_v²(1 - v)` for `u ≤ v < 1`. -/
private theorem lemmaN_zeta_sq_ratio (g : ℝ) (hg : 0 ≤ g) (W L : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v < 1) :
    zetaProp g W L u ^ 2 * (1 - u) ≤ zetaProp g W L v ^ 2 * (1 - v) := by
  have hr := lemmaNRates_ell_ratio g hg L huv hv
  obtain ⟨hℓ1, -, -, -, -, -, -⟩ := scale_facts g hg W L hW hL u u hu le_rfl (by linarith)
  obtain ⟨hℓ1', -, -, -, -, -, -⟩ := scale_facts g hg W L hW hL v v (by linarith) le_rfl hv
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h1u : 0 < 1 - u := by linarith
  have h1v : 0 < 1 - v := by linarith
  set ℓu := ellProp g L u
  set ℓv := ellProp g L v
  have hsq : ℓv ^ 2 * (1 - v) ≤ ℓu ^ 2 * (1 - u) := by
    have h0 : 0 ≤ ℓv := by linarith
    have h2 : ℓv ^ 2 ≤ (Real.sqrt ((1 - u) / (1 - v)) * ℓu) ^ 2 := pow_le_pow_left₀ h0 hr 2
    rw [mul_pow, Real.sq_sqrt (div_nonneg h1u.le h1v.le)] at h2
    have h3 : ℓv ^ 2 * (1 - v) ≤ (1 - u) / (1 - v) * ℓu ^ 2 * (1 - v) :=
      mul_le_mul_of_nonneg_right h2 h1v.le
    have h4 : (1 - u) / (1 - v) * ℓu ^ 2 * (1 - v) = ℓu ^ 2 * (1 - u) := by
      field_simp
    linarith
  unfold zetaProp
  rw [inv_pow, inv_pow, ← div_eq_inv_mul, ← div_eq_inv_mul]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e1 : ((W : ℝ) * ℓu * (1 - u) * gammaG g) ^ 2 = ((W : ℝ) * gammaG g) ^ 2 * (1 - u) *
      (ℓu ^ 2 * (1 - u)) := by ring
  have e2 : ((W : ℝ) * ℓv * (1 - v) * gammaG g) ^ 2 = ((W : ℝ) * gammaG g) ^ 2 * (1 - v) *
      (ℓv ^ 2 * (1 - v)) := by ring
  rw [e1, e2]
  have hA : 0 ≤ ((W : ℝ) * gammaG g) ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_left hsq (mul_nonneg hA (mul_nonneg h1u.le h1v.le))
  nlinarith [this]

/-! ### Matrices -/

open scoped Matrix.Norms.L2Operator in
/-- The operator norm of a square block is at most its Hilbert–Schmidt norm. -/
private theorem lemmaN_opNorm_le_hs {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp only [Matrix.ofLp_toEuclideanCLM]
  have h : ∀ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 := by
    intro i
    have h1 : ‖(A *ᵥ x.ofLp) i‖ ≤ ∑ j, ‖A i j‖ * ‖x.ofLp j‖ := by
      simp only [Matrix.mulVec, dotProduct]
      exact (norm_sum_le _ _).trans (by simp)
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖)
      (fun j => ‖x.ofLp j‖)
    calc _ ≤ (∑ j, ‖A i j‖ * ‖x.ofLp j‖) ^ 2 := by gcongr
      _ ≤ _ := h2
  calc ∑ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2 ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => h i
    _ = _ := by rw [Finset.sum_mul]

open scoped Matrix.Norms.L2Operator in
/-- `‖G_{xy}‖ ≤ ‖G_{xy}‖_HS`. -/
private theorem lemmaN_blockOf_le_hs {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : ‖blockOf X a b‖ ≤ Real.sqrt (blockHS2 X a b) := by
  refine (lemmaN_opNorm_le_hs _).trans (le_of_eq ?_)
  rfl

/-- `ℒ₂(a, b; +, -) = W⁻² ‖G_{ba}‖²_HS`. -/
private theorem lemmaN_loopTr_two_hs {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) :
    loopTr X ![a, b] ![true, false] = ((((W : ℝ) ^ 2)⁻¹ * blockHS2 X b a : ℝ) : ℂ) := by
  rw [loopTr_two]
  rfl

/-- The length-one loops against `m^σ` are the centered block traces. -/
private theorem lemmaN_loop_one_sub (g E : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c : Fin L) (s : Bool) :
    ‖loopTr G ![c] ![s] - sgnScalar m s‖ =
      ‖blockTr (G - dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c‖ := by
  have hM := loopTr_one_dysonMat g E W L hW hL m hm c true
  simp only [ite_true] at hM
  have hbt : ∀ X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ,
      blockTr X c c = loopTr X ![c] ![true] := by
    intro X; rw [loopTr_one]; rfl
  have hsub : blockTr (G - dysonMat (hopB g) (gammaG g) L E m ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ)) c c = loopTr G ![c] ![true] - m := by
    have e : blockTr (G - dysonMat (hopB g) (gammaG g) L E m ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ)) c c = blockTr G c c -
          blockTr (dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c := by
      unfold blockTr
      simp only [Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]
    rw [e, hbt G, hbt, hM]
  rw [hsub]
  cases s
  · have h1 : loopTr G ![c] ![false] = star (loopTr G ![c] ![true]) := by
      rw [loopTr_one]
      have : loopTr G ![c] ![false] = loopTr Gᴴ ![c] ![true] := by simp [loopTr, sgnMat]
      rw [this, loopTr_one]
      simp [Matrix.conjTranspose_apply, star_sum]
    rw [h1, sgnScalar]
    simp only [Bool.false_eq_true, ite_false]
    rw [← star_sub, norm_star]
  · simp [sgnScalar]

/-- The Dyson matrix is symmetric. -/
private theorem lemmaN_dysonMat_symm (b β : ℝ) (L : ℕ) (z m : ℂ) (i j : Fin L) :
    dysonMat b β L z m i j = dysonMat b β L z m j i := by
  have hA : (cycleAdj L).transpose = cycleAdj L := by
    ext i j
    simp only [Matrix.transpose_apply, cycleAdj, Matrix.of_apply]
    rw [add_comm]
  have h : (dysonMat b β L z m).transpose = dysonMat b β L z m := by
    unfold dysonMat
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_smul, Matrix.transpose_one, hA]
  conv_lhs => rw [← h]
  rfl

/-- The mixed kernel of a symmetric matrix is symmetric. -/
private theorem lemmaN_mixedKer_symm {L : ℕ} (P : Matrix (Fin L) (Fin L) ℝ)
    (hP : ∀ a b, P a b = P b a) (u : ℝ) (a b : Fin L) :
    mixedKer P u a b = mixedKer P u b a := by
  have hPt : P.transpose = P := by ext i j; exact (hP j i)
  set B := (1 : Matrix (Fin L) (Fin L) ℝ) - u • P with hB
  have hBt : B.transpose = B := by
    rw [hB, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hPt]
  have hcomm : P * B = B * P := by
    rw [hB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  have hinv : P * B⁻¹ = B⁻¹ * P := by
    by_cases hd : IsUnit B.det
    · calc P * B⁻¹ = B⁻¹ * B * (P * B⁻¹) := by rw [Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
        _ = B⁻¹ * (B * P) * B⁻¹ := by simp only [Matrix.mul_assoc]
        _ = B⁻¹ * (P * B) * B⁻¹ := by rw [hcomm]
        _ = B⁻¹ * P * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
        _ = B⁻¹ * P := by rw [Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ hd, Matrix.mul_zero, Matrix.zero_mul]
  have hK : (mixedKer P u).transpose = mixedKer P u := by
    unfold mixedKer
    rw [← hB, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hBt, hPt, hinv]
  conv_lhs => rw [← hK]
  rfl

/-- `P_ab = γ|M_ab|²` is symmetric. -/
private theorem lemmaN_pairP_symm (b β : ℝ) (L : ℕ) (z m : ℂ) (x y : Fin L) :
    pairP β (dysonMat b β L z m) x y = pairP β (dysonMat b β L z m) y x := by
  simp only [pairP, Matrix.of_apply, lemmaN_dysonMat_symm b β L z m x y]

/-! ### Fields in the bounded `C^{1,2}` class -/

/-- At a time inside the class interval a field is continuous, `C²` in space and differentiable in
time. -/
private theorem lemmaN_heat_slice {ι : Type*} [Fintype ι] {F : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (hF : HeatClass F a b) {u : ℝ} (hu : u ∈ Set.Ioo a b) :
    Continuous (F u) ∧ ContDiff ℝ 2 (F u) ∧ ∀ y, DifferentiableAt ℝ (fun r => F r y) u := by
  obtain ⟨hc, -, ⟨Fu, hFu, -, -⟩, ⟨DF, D2F, hD, hD2, -, hcD2, -⟩⟩ := hF
  have hc2 : Continuous (D2F u) :=
    hcD2.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hu, trivial⟩
  have h1 : ContDiff ℝ 1 (DF u) := contDiff_one_iff_hasFDerivAt.2 ⟨D2F u, hc2, hD2 u hu⟩
  have h2 : ContDiff ℝ (1 + 1) (F u) :=
    contDiff_succ_iff_hasFDerivAt (n := 1).2 ⟨DF u, h1, hD u hu⟩
  have h3 : ContDiff ℝ 2 (F u) := by rw [← one_add_one_eq_two]; exact h2
  exact ⟨h3.continuous, h3, fun y => (hFu u hu y).differentiableAt⟩

/-- A real field in the class is continuous at a time inside the interval. -/
private theorem lemmaN_heat_cont_re {ι : Type*} [Fintype ι] {X : ℝ → (ι → ℝ) → ℝ} {a b : ℝ}
    (hX : HeatClass (fun r y => ((X r y : ℝ) : ℂ)) a b) {u : ℝ} (hu : u ∈ Set.Ioo a b) :
    Continuous (X u) := by
  have h := (lemmaN_heat_slice hX hu).1
  have := Complex.continuous_re.comp h
  simpa [Function.comp_def] using this

/-- The carré du champ `Γ(F, F)` is real and nonnegative: its real part is its norm. -/
private theorem lemmaN_gamma_re_eq_norm {ι : Type*} [Fintype ι] {σ2 : ℝ} (hσ2 : 0 ≤ σ2)
    (F : (ι → ℝ) → ℂ) (y : ι → ℝ) :
    (coordGamma σ2 F F y).re = ‖coordGamma σ2 F F y‖ := by
  have e : coordGamma σ2 F F y =
      ((σ2 * ∑ i, ‖deriv (fun e : ℝ => F (y + e • Pi.single i 1)) 0‖ ^ 2 : ℝ) : ℂ) := by
    simp only [coordGamma, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [e, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg hσ2 (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-! ### Uniform derivative bounds of the cutoffs -/

section CutBounds

variable {ε : ℝ} {ρ : ℝ → ℝ}

private theorem lemmaN_ramp_mem (hρ : IsRamp ε ρ) (y : ℝ) : 0 ≤ ρ y ∧ ρ y ≤ 1 := by
  have h := cutPhi_props hρ one_pos one_pos 0 (y + 1)
  have e : cutPhi ρ 1 1 (y + 1) = ρ y := by unfold cutPhi; congr 1; ring
  rw [e] at h
  exact ⟨h.1, h.2.1⟩

private theorem lemmaN_ramp_hasDerivAt (hρ : IsRamp ε ρ) (y : ℝ) :
    HasDerivAt ρ (deriv ρ y) y :=
  ((hρ.smooth.differentiable (by norm_num)) y).hasDerivAt

private theorem lemmaN_ramp_hasDerivAt2 (hρ : IsRamp ε ρ) (y : ℝ) :
    HasDerivAt (deriv ρ) (iteratedDeriv 2 ρ y) y := by
  have hd : Differentiable ℝ (iteratedDeriv 1 ρ) :=
    hρ.smooth.differentiable_iteratedDeriv 1 (by norm_num)
  rw [iteratedDeriv_one] at hd
  have e : iteratedDeriv 2 ρ = deriv (deriv ρ) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [e]
  exact (hd y).hasDerivAt

private theorem lemmaN_iteratedDeriv_two (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- A function equal to a constant near `x` has vanishing first and second derivative at `x`. -/
private theorem lemmaN_deriv_zero_of_eventually {f : ℝ → ℝ} {x c : ℝ}
    (hf : f =ᶠ[𝓝 x] fun _ => c) : deriv f x = 0 ∧ iteratedDeriv 2 f x = 0 := by
  have h1 : deriv f =ᶠ[𝓝 x] deriv (fun _ : ℝ => c) := hf.deriv
  refine ⟨by rw [hf.deriv_eq, deriv_const], ?_⟩
  rw [lemmaN_iteratedDeriv_two, h1.deriv_eq]
  simp

private theorem lemmaN_abs_mul_le {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

private theorem lemmaN_le_mul3 {x y z : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    x ≤ x * y * z ∧ y ≤ x * y * z ∧ z ≤ x * y * z := by
  have hxy : 1 ≤ x * y := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have : x ≤ x * y := by nlinarith
    nlinarith
  · have : y ≤ x * y := by nlinarith
    nlinarith
  · nlinarith

/-- The constant of the uniform derivative bounds of the cutoffs for `J ≥ 1`. -/
private def lemmaNCutC (ε β : ℝ) (r : ℕ) : ℝ :=
  9 * (1 + 2 * β) ^ (2 * r) *
    ((2 * r + 1) * (1 + (1 - ε)⁻¹ + 3 / (2 * ε * (1 - ε))) * (1 + β⁻¹)) ^ 3

set_option maxHeartbeats 3000000 in
/-- For `J ≥ 1` the first and second derivatives of `ψ` and `Φ` are bounded by a constant that
depends only on `(ε, β, r)`. -/
private theorem lemmaN_cut_bounds (hρ : IsRamp ε ρ) {J β : ℝ} (hJ : 1 ≤ J) (hβ : 0 < β)
    (r : ℕ) (hr : 1 ≤ r) (x : ℝ) :
    (|deriv (cutPsi ρ J β r) x| ≤ lemmaNCutC ε β r ∧
      |iteratedDeriv 2 (cutPsi ρ J β r) x| ≤ lemmaNCutC ε β r) ∧
    (|deriv (cutPhi ρ J β) x| ≤ lemmaNCutC ε β r ∧
      |iteratedDeriv 2 (cutPhi ρ J β) x| ≤ lemmaNCutC ε β r) := by
  obtain ⟨hε0, hε1⟩ := hρ.eps
  have hJ0 : 0 < J := by linarith
  have hm : 0 < β * J := mul_pos hβ hJ0
  set s1 : ℝ := (1 - ε)⁻¹ with hs1
  set s2 : ℝ := 3 / (2 * ε * (1 - ε)) with hs2
  have h1ε : 0 < 1 - ε := by linarith
  have hs10 : 0 ≤ s1 := by positivity
  have hs20 : 0 ≤ s2 := by positivity
  set B : ℝ := 1 + 2 * β with hB
  have hB1 : 1 ≤ B := by linarith
  set T : ℝ := (2 * r + 1) * (1 + s1 + s2) * (1 + β⁻¹) with hT
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hbi : 0 ≤ β⁻¹ := inv_nonneg.2 hβ.le
  have hA1 : 1 ≤ 2 * (r : ℝ) + 1 := by linarith
  have hA2 : 1 ≤ 1 + s1 + s2 := by linarith
  have hA3 : 1 ≤ 1 + β⁻¹ := by linarith
  have h3 := lemmaN_le_mul3 hA1 hA2 hA3
  have hT1 : 1 ≤ T := by simp only [hT]; linarith [h3.1]
  have hT0 : 0 ≤ T := by linarith
  have hTr : 2 * (r : ℝ) ≤ T := by simp only [hT]; linarith [h3.1]
  have hTs1 : s1 ≤ T := by simp only [hT]; linarith [h3.2.1]
  have hTs2 : s2 ≤ T := by simp only [hT]; linarith [h3.2.1]
  have hTb : β⁻¹ ≤ T := by simp only [hT]; linarith [h3.2.2]
  have hBr : 1 ≤ B ^ (2 * r) := one_le_pow₀ hB1
  have hC : lemmaNCutC ε β r = 9 * B ^ (2 * r) * T ^ 3 := by
    simp only [lemmaNCutC, hB, hT, hs1, hs2]
  -- inverse scale bounds
  have hiJ : (β * J)⁻¹ ≤ β⁻¹ := by
    rw [mul_inv]
    have : J⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hJ
    have := mul_le_mul_of_nonneg_left this hbi
    linarith
  have hiJ0 : 0 ≤ (β * J)⁻¹ := by positivity
  have hiJabs : |(β * J)⁻¹| ≤ β⁻¹ := by rw [abs_of_nonneg hiJ0]; exact hiJ
  -- the ramp bounds
  have hd1 : ∀ y, |deriv ρ y| ≤ s1 := fun y => by
    rw [abs_of_nonneg (hρ.slope y).1]; exact (hρ.slope y).2
  have hd2 : ∀ y, |iteratedDeriv 2 ρ y| ≤ s2 := fun y => hρ.curv y
  have hd0 : ∀ y, |ρ y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (lemmaN_ramp_mem hρ y).1]; exact (lemmaN_ramp_mem hρ y).2
  -- the cutPhi part
  have hΦ1 : ∀ x, HasDerivAt (cutPhi ρ J β) (deriv ρ ((x - J) / (β * J)) * (β * J)⁻¹) x := by
    intro x
    have ha : HasDerivAt (fun x : ℝ => (x - J) / (β * J)) (1 / (β * J)) x :=
      ((hasDerivAt_id' x).sub_const J).div_const (β * J)
    have := (lemmaN_ramp_hasDerivAt hρ ((x - J) / (β * J))).comp x ha
    rw [one_div] at this
    exact this
  have hΦ2 : ∀ x, HasDerivAt (fun x => deriv ρ ((x - J) / (β * J)) * (β * J)⁻¹)
      (iteratedDeriv 2 ρ ((x - J) / (β * J)) * (β * J)⁻¹ * (β * J)⁻¹) x := by
    intro x
    have ha : HasDerivAt (fun x : ℝ => (x - J) / (β * J)) (1 / (β * J)) x :=
      ((hasDerivAt_id' x).sub_const J).div_const (β * J)
    have := ((lemmaN_ramp_hasDerivAt2 hρ ((x - J) / (β * J))).comp x ha).mul_const (β * J)⁻¹
    rw [one_div] at this
    exact this
  have hdΦ : deriv (cutPhi ρ J β) = fun x => deriv ρ ((x - J) / (β * J)) * (β * J)⁻¹ :=
    funext fun x => (hΦ1 x).deriv
  have hTT : T ≤ T * T := le_mul_of_one_le_right hT0 hT1
  have hTTT : T * T ≤ T * T * T := le_mul_of_one_le_right (by positivity) hT1
  have hT3e : T ^ 3 = T * T * T := by ring
  have hBpos : 0 ≤ B ^ (2 * r) := by positivity
  have hfin : ∀ z, z ≤ T * T * T → z ≤ 9 * B ^ (2 * r) * T ^ 3 := by
    intro z hz
    have h1 : T * T * T ≤ B ^ (2 * r) * (T * T * T) :=
      le_mul_of_one_le_left (by positivity) hBr
    have h2 : 0 ≤ B ^ (2 * r) * (T * T * T) := by positivity
    rw [hT3e]
    linarith
  refine ⟨?_, ?_⟩
  swap
  · rw [hC]
    constructor
    · rw [hdΦ]
      have := lemmaN_abs_mul_le (hd1 ((x - J) / (β * J))) hiJabs
      refine this.trans (hfin _ ?_)
      have : s1 * β⁻¹ ≤ T * T := mul_le_mul hTs1 hTb hbi hT0
      linarith
    · rw [lemmaN_iteratedDeriv_two, hdΦ, (hΦ2 x).deriv]
      have h1 := lemmaN_abs_mul_le (lemmaN_abs_mul_le (hd2 ((x - J) / (β * J)))
        hiJabs) hiJabs
      refine h1.trans (hfin _ ?_)
      have : s2 * β⁻¹ ≤ T * T := mul_le_mul hTs2 hTb hbi hT0
      exact mul_le_mul this hTb hbi (by positivity)
  -- the cutPsi part
  set P : ℝ → ℝ := fun x => (x / J) ^ (2 * r) with hPdef
  set P1 : ℝ → ℝ := fun x => (2 * r : ℕ) * (x / J) ^ (2 * r - 1) * J⁻¹ with hP1def
  set P2 : ℝ → ℝ := fun x => (2 * r : ℕ) * ((2 * r - 1 : ℕ) * (x / J) ^ (2 * r - 1 - 1) * J⁻¹) *
    J⁻¹ with hP2def
  set χ : ℝ → ℝ := fun x => 1 - ρ ((x - J * (1 + β)) / (β * J)) with hχdef
  set χ1 : ℝ → ℝ := fun x => -(deriv ρ ((x - J * (1 + β)) / (β * J)) * (β * J)⁻¹) with hχ1def
  set χ2 : ℝ → ℝ := fun x => -(iteratedDeriv 2 ρ ((x - J * (1 + β)) / (β * J)) * (β * J)⁻¹ *
    (β * J)⁻¹) with hχ2def
  set σ : ℝ → ℝ := fun x => ρ (x + 1) with hσdef
  set σ1 : ℝ → ℝ := fun x => deriv ρ (x + 1) with hσ1def
  set σ2 : ℝ → ℝ := fun x => iteratedDeriv 2 ρ (x + 1) with hσ2def
  have hP : ∀ x, HasDerivAt P (P1 x) x := by
    intro x
    have ha : HasDerivAt (fun x : ℝ => x / J) (1 / J) x := (hasDerivAt_id' x).div_const J
    have := (hasDerivAt_pow (2 * r) (x / J)).comp x ha
    simpa [hPdef, hP1def, Function.comp_def, one_div] using this
  have hP' : ∀ x, HasDerivAt P1 (P2 x) x := by
    intro x
    have ha : HasDerivAt (fun x : ℝ => x / J) (1 / J) x := (hasDerivAt_id' x).div_const J
    have := (((hasDerivAt_pow (2 * r - 1) (x / J)).comp x ha).const_mul
      ((2 * r : ℕ) : ℝ)).mul_const J⁻¹
    simpa [hP1def, hP2def, Function.comp_def, one_div, mul_assoc] using this
  have hχ : ∀ x, HasDerivAt χ (χ1 x) x := by
    intro x
    have ha : HasDerivAt (fun x : ℝ => (x - J * (1 + β)) / (β * J)) (1 / (β * J)) x :=
      ((hasDerivAt_id' x).sub_const _).div_const (β * J)
    have := ((lemmaN_ramp_hasDerivAt hρ _).comp x ha).const_sub 1
    rw [one_div] at this
    exact this
  have hχ' : ∀ x, HasDerivAt χ1 (χ2 x) x := by
    intro x
    have ha : HasDerivAt (fun x : ℝ => (x - J * (1 + β)) / (β * J)) (1 / (β * J)) x :=
      ((hasDerivAt_id' x).sub_const _).div_const (β * J)
    have := (((lemmaN_ramp_hasDerivAt2 hρ _).comp x ha).mul_const (β * J)⁻¹).neg
    rw [one_div] at this
    exact this
  have hσ : ∀ x, HasDerivAt σ (σ1 x) x := by
    intro x
    have := (lemmaN_ramp_hasDerivAt hρ (x + 1)).comp x ((hasDerivAt_id' x).add_const 1)
    rw [mul_one] at this
    exact this
  have hσ' : ∀ x, HasDerivAt σ1 (σ2 x) x := by
    intro x
    have := (lemmaN_ramp_hasDerivAt2 hρ (x + 1)).comp x ((hasDerivAt_id' x).add_const 1)
    rw [mul_one] at this
    exact this
  have hψ : cutPsi ρ J β r = fun x => P x * χ x * σ x := by
    funext x; simp [cutPsi, hPdef, hχdef, hσdef]
  have hD1 : ∀ x, HasDerivAt (cutPsi ρ J β r)
      ((P1 x * χ x + P x * χ1 x) * σ x + P x * χ x * σ1 x) x := by
    intro x; rw [hψ]; exact ((hP x).mul (hχ x)).mul (hσ x)
  have hdψ : deriv (cutPsi ρ J β r) =
      fun x => (P1 x * χ x + P x * χ1 x) * σ x + P x * χ x * σ1 x :=
    funext fun x => (hD1 x).deriv
  have hD2 : ∀ x, HasDerivAt (fun x => (P1 x * χ x + P x * χ1 x) * σ x + P x * χ x * σ1 x)
      (((P2 x * χ x + P1 x * χ1 x) + (P1 x * χ1 x + P x * χ2 x)) * σ x +
        (P1 x * χ x + P x * χ1 x) * σ1 x +
        ((P1 x * χ x + P x * χ1 x) * σ1 x + P x * χ x * σ2 x)) x := by
    intro x
    exact ((((hP' x).mul (hχ x)).add ((hP x).mul (hχ' x))).mul (hσ x)).add
      (((hP x).mul (hχ x)).mul (hσ' x))
  -- outside the window both derivatives vanish
  rcases lt_or_ge x (-1) with hxl | hxl
  · have hev : cutPsi ρ J β r =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [gt_mem_nhds hxl] with z hz
      have : ρ (z + 1) = 0 := hρ.zero _ (by linarith)
      simp [cutPsi, this]
    obtain ⟨h1, h2⟩ := lemmaN_deriv_zero_of_eventually hev
    rw [h1, h2, abs_zero, hC]
    exact ⟨by positivity, by positivity⟩
  rcases lt_or_ge (J * (1 + 2 * β)) x with hxr | hxr
  · have hev : cutPsi ρ J β r =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [lt_mem_nhds hxr] with z hz
      have : ρ ((z - J * (1 + β)) / (β * J)) = 1 :=
        hρ.one _ ((le_div_iff₀ hm).2 (by linarith))
      simp [cutPsi, this]
    obtain ⟨h1, h2⟩ := lemmaN_deriv_zero_of_eventually hev
    rw [h1, h2, abs_zero, hC]
    exact ⟨by positivity, by positivity⟩
  -- inside: `|x/J| ≤ 1 + 2β`
  have hxJ : |x / J| ≤ B := by
    rw [abs_le]
    constructor
    · have : 1 ≤ B * J := one_le_mul_of_one_le_of_one_le hB1 hJ
      rw [le_div_iff₀ hJ0]; linarith
    · rw [div_le_iff₀ hJ0, hB]; linarith
  have hJi : |J⁻¹| ≤ 1 := by rw [abs_of_pos (inv_pos.2 hJ0)]; exact inv_le_one_of_one_le₀ hJ
  have hpow : ∀ k : ℕ, k ≤ 2 * r → |(x / J) ^ k| ≤ B ^ (2 * r) := by
    intro k hk
    rw [abs_pow]
    calc |x / J| ^ k ≤ B ^ k := pow_le_pow_left₀ (abs_nonneg _) hxJ k
      _ ≤ B ^ (2 * r) := pow_le_pow_right₀ hB1 hk
  have hp0 : |P x| ≤ B ^ (2 * r) := hpow _ le_rfl
  have hp1 : |P1 x| ≤ 2 * r * B ^ (2 * r) := by
    have h := lemmaN_abs_mul_le (lemmaN_abs_mul_le (le_of_eq (abs_of_nonneg
      (Nat.cast_nonneg (2 * r)))) (hpow (2 * r - 1) (by omega))) hJi
    simp only [hP1def]
    push_cast at h ⊢
    linarith
  have hp2 : |P2 x| ≤ 2 * r * (2 * r) * B ^ (2 * r) := by
    have hk : ((2 * r - 1 : ℕ) : ℝ) ≤ 2 * r := by
      have : 2 * r - 1 ≤ 2 * r := Nat.sub_le _ _
      exact_mod_cast this
    have h := lemmaN_abs_mul_le (lemmaN_abs_mul_le (le_of_eq (abs_of_nonneg
      (Nat.cast_nonneg (2 * r)))) (lemmaN_abs_mul_le (lemmaN_abs_mul_le (le_of_eq (abs_of_nonneg
      (Nat.cast_nonneg (2 * r - 1)))) (hpow (2 * r - 1 - 1) (by omega))) hJi)) hJi
    simp only [hP2def]
    have h2 : ((2 * r : ℕ) : ℝ) * (((2 * r - 1 : ℕ) : ℝ) * B ^ (2 * r) * 1) * 1 ≤
        2 * r * (2 * r) * B ^ (2 * r) := by
      push_cast
      have : (0 : ℝ) ≤ 2 * r := by positivity
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk (by positivity)) this
      push_cast at this
      nlinarith
    linarith
  have hc0 : |χ x| ≤ 1 := by
    have := lemmaN_ramp_mem hρ ((x - J * (1 + β)) / (β * J))
    simp only [hχdef]; rw [abs_le]; constructor <;> linarith
  have hc1 : |χ1 x| ≤ s1 * β⁻¹ := by
    simp only [hχ1def, abs_neg]
    exact lemmaN_abs_mul_le (hd1 _) hiJabs
  have hc2 : |χ2 x| ≤ s2 * β⁻¹ * β⁻¹ := by
    simp only [hχ2def, abs_neg]
    exact lemmaN_abs_mul_le (lemmaN_abs_mul_le (hd2 _) hiJabs)
      hiJabs
  have hq0 : |σ x| ≤ 1 := hd0 _
  have hq1 : |σ1 x| ≤ s1 := hd1 _
  have hq2 : |σ2 x| ≤ s2 := hd2 _
  have k1 : s1 * β⁻¹ ≤ T * T := mul_le_mul hTs1 hTb hbi hT0
  have k2 : s2 * β⁻¹ * β⁻¹ ≤ T * T * T :=
    mul_le_mul (mul_le_mul hTs2 hTb hbi hT0) hTb hbi (by positivity)
  have k3 : (2 * r : ℝ) * (2 * r) ≤ T * T := mul_le_mul hTr hTr (by positivity) hT0
  have k4 : (2 * r : ℝ) * (s1 * β⁻¹) ≤ T * (T * T) :=
    mul_le_mul hTr k1 (by positivity) hT0
  have k5 : (2 * r : ℝ) * s1 ≤ T * T := mul_le_mul hTr hTs1 hs10 hT0
  have k6 : s1 * β⁻¹ * s1 ≤ T * T * T := mul_le_mul k1 hTs1 hs10 (by positivity)
  have k7 : T * (T * T) = T * T * T := by ring
  have hr0 : (0 : ℝ) ≤ 2 * r := by positivity
  constructor
  · rw [hdψ]
    have e1 := lemmaN_abs_mul_le (abs_add_le _ _ |>.trans (add_le_add
      (lemmaN_abs_mul_le hp1 hc0) (lemmaN_abs_mul_le hp0 hc1))) hq0
    have e2 := lemmaN_abs_mul_le (lemmaN_abs_mul_le hp0 hc0) hq1
    refine (abs_add_le _ _).trans ((add_le_add e1 e2).trans ?_)
    have key : (2 * r * B ^ (2 * r) * 1 + B ^ (2 * r) * (s1 * β⁻¹)) * 1 + B ^ (2 * r) * 1 * s1 =
        B ^ (2 * r) * (2 * r + s1 * β⁻¹ + s1) := by ring
    rw [key, hC]
    have hs : 2 * (r : ℝ) + s1 * β⁻¹ + s1 ≤ 9 * (T * T * T) := by
      have : 2 * (r : ℝ) ≤ T * T * T := hTr.trans (hTT.trans hTTT)
      have : s1 ≤ T * T * T := hTs1.trans (hTT.trans hTTT)
      have : s1 * β⁻¹ ≤ T * T * T := k1.trans hTTT
      have : 0 ≤ T * T * T := by positivity
      linarith
    calc B ^ (2 * r) * _ ≤ B ^ (2 * r) * (9 * (T * T * T)) := mul_le_mul_of_nonneg_left hs hBpos
      _ = 9 * B ^ (2 * r) * T ^ 3 := by ring
  · rw [lemmaN_iteratedDeriv_two, hdψ, (hD2 x).deriv]
    have t1 := lemmaN_abs_mul_le hp2 hc0
    have t2 := lemmaN_abs_mul_le hp1 hc1
    have t3 := lemmaN_abs_mul_le hp0 hc2
    have t4 := lemmaN_abs_mul_le hp1 hc0
    have t5 := lemmaN_abs_mul_le hp0 hc1
    have t6 := lemmaN_abs_mul_le hp0 hc0
    have u1 := lemmaN_abs_mul_le ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add t1 t2)) ((abs_add_le _ _).trans (add_le_add t2 t3))))
      hq0
    have u2 := lemmaN_abs_mul_le ((abs_add_le _ _).trans (add_le_add t4 t5)) hq1
    have u3 := lemmaN_abs_mul_le t6 hq2
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add u1 u2))
      ((abs_add_le _ _).trans (add_le_add u2 u3))) |>.trans ?_
    have key : ((2 * r * (2 * r) * B ^ (2 * r) * 1 + 2 * r * B ^ (2 * r) * (s1 * β⁻¹)) +
          (2 * r * B ^ (2 * r) * (s1 * β⁻¹) + B ^ (2 * r) * (s2 * β⁻¹ * β⁻¹))) * 1 +
        (2 * r * B ^ (2 * r) * 1 + B ^ (2 * r) * (s1 * β⁻¹)) * s1 +
        ((2 * r * B ^ (2 * r) * 1 + B ^ (2 * r) * (s1 * β⁻¹)) * s1 + B ^ (2 * r) * 1 * s2) =
        B ^ (2 * r) * ((2 * r) * (2 * r) + 2 * ((2 * r) * (s1 * β⁻¹)) + s2 * β⁻¹ * β⁻¹ +
          2 * ((2 * r) * s1) + 2 * (s1 * β⁻¹ * s1) + s2) := by ring
    rw [key, hC]
    have hsum : (2 * r : ℝ) * (2 * r) + 2 * ((2 * r) * (s1 * β⁻¹)) + s2 * β⁻¹ * β⁻¹ +
        2 * ((2 * r) * s1) + 2 * (s1 * β⁻¹ * s1) + s2 ≤ 9 * (T * T * T) := by
      have : s2 ≤ T * T * T := hTs2.trans (hTT.trans hTTT)
      have : (2 * r : ℝ) * (2 * r) ≤ T * T * T := k3.trans hTTT
      have : (2 * r : ℝ) * s1 ≤ T * T * T := k5.trans hTTT
      rw [k7] at k4
      linarith
    calc B ^ (2 * r) * _ ≤ B ^ (2 * r) * (9 * (T * T * T)) := mul_le_mul_of_nonneg_left hsum hBpos
      _ = 9 * B ^ (2 * r) * T ^ 3 := by ring

end CutBounds

/-! ### Raw rows at a good point -/

section RawRows

open scoped Matrix.Norms.L2Operator

/-- Kernel row on both sides: `|Σ_c K(a,c)D(c,b) + D(a,c)K(c,b)| ≤ 2κΛ w(a,b)` for a symmetric
nonnegative kernel with `Σ_x K(a,x)w(x,b) ≤ κ w(a,b)`. -/
private theorem lemmaN_row_kernel {L : ℕ} (K : Matrix (Fin L) (Fin L) ℝ) (D : Fin L → Fin L → ℂ)
    (w : Fin L → Fin L → ℝ) {Λ κ : ℝ} (hΛ : 0 ≤ Λ) (hK0 : ∀ x y, 0 ≤ K x y)
    (hKs : ∀ x y, K x y = K y x) (hws : ∀ x y, w x y = w y x)
    (hD : ∀ x y, ‖D x y‖ ≤ Λ * w x y) (hrow : ∀ x y, ∑ c, K x c * w c y ≤ κ * w x y)
    (a b : Fin L) :
    ‖∑ c, (((K a c : ℝ) : ℂ) * D c b + D a c * ((K c b : ℝ) : ℂ))‖ ≤ 2 * κ * Λ * w a b := by
  have h1 : ‖∑ c, (((K a c : ℝ) : ℂ) * D c b + D a c * ((K c b : ℝ) : ℂ))‖ ≤
      ∑ c, (K a c * (Λ * w c b) + (Λ * w a c) * K c b) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 a c)]
      exact mul_le_mul_of_nonneg_left (hD c b) (hK0 a c)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 c b)]
      exact mul_le_mul_of_nonneg_right (hD a c) (hK0 c b)
  have h2 : ∑ c, (K a c * (Λ * w c b) + (Λ * w a c) * K c b) =
      Λ * (∑ c, K a c * w c b + ∑ c, K b c * w c a) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hKs c b, hws a c]; ring
  rw [h2] at h1
  have h3 := hrow a b
  have h4 := hrow b a
  rw [hws b a] at h4
  have : Λ * (∑ c, K a c * w c b + ∑ c, K b c * w c a) ≤ Λ * (κ * w a b + κ * w a b) :=
    mul_le_mul_of_nonneg_left (add_le_add h3 h4) hΛ
  linarith

/-- The long-edge Hilbert–Schmidt bound from `ℒ₂ = 𝒦₂ + D₂`: if `|𝒦₂(y,x)| ≤ C'ζ²w` and
`|D₂(y,x)| ≤ Λζ²w`, then `‖G_{xy}‖²_HS ≤ W²(C'+Λ)ζ²w(x,y)`. -/
private theorem lemmaN_hs_long {W L : ℕ} (hW : 1 ≤ W) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (P : ℂ) {x y : Fin L} {C' Λ ζ w : ℝ}
    (hP : ‖P‖ ≤ C' * ζ ^ 2 * w) (hD : ‖loopTr G ![y, x] ![true, false] - P‖ ≤ Λ * ζ ^ 2 * w) :
    blockHS2 G x y ≤ (W : ℝ) ^ 2 * (C' + Λ) * ζ ^ 2 * w := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have e := lemmaN_loopTr_two_hs G y x
  have hHS0 : 0 ≤ blockHS2 G x y := by unfold blockHS2; positivity
  have hn : ‖loopTr G ![y, x] ![true, false]‖ = ((W : ℝ) ^ 2)⁻¹ * blockHS2 G x y := by
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : ‖loopTr G ![y, x] ![true, false]‖ ≤ (C' + Λ) * ζ ^ 2 * w := by
    calc _ ≤ ‖loopTr G ![y, x] ![true, false] - P‖ + ‖P‖ := norm_le_norm_sub_add _ _
      _ ≤ Λ * ζ ^ 2 * w + C' * ζ ^ 2 * w := add_le_add hD hP
      _ = _ := by ring
  rw [hn] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (W : ℝ) ^ 2)
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at h2
  linarith

/-- `√(Λζ²w) = √Λ ζ √w`. -/
private theorem lemmaN_sqrt_split {Λ ζ w : ℝ} (hΛ : 0 ≤ Λ) (hζ : 0 ≤ ζ) (hw : 0 ≤ w) :
    Real.sqrt (Λ * ζ ^ 2 * w) = Real.sqrt Λ * ζ * Real.sqrt w := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hΛ, Real.sqrt_sq hζ]

/-- Weighted operator bound with the terminal weight: on short edges from the unweighted operator
bound and `w ≥ ω⁻¹`, on long edges from the Hilbert–Schmidt bound. -/
private theorem lemmaN_hop_dist {W L : ℕ} (hW : 1 ≤ W) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (w : Fin L → Fin L → ℝ) {o₁ ω h C' Λ ζ : ℝ} (ho₁ : 0 ≤ o₁) (hω : 1 ≤ ω) (hCΛ : 0 ≤ C' + Λ)
    (hζ : 0 ≤ ζ) (hw0 : ∀ x y, 0 ≤ w x y)
    (hop : ∀ x y, ‖blockOf G x y‖ ≤ W * o₁)
    (hshort : ∀ x y, (cycDist x y : ℝ) ≤ 2 * h → ω⁻¹ ≤ w x y)
    (hlong : ∀ x y, h < cycDist x y → blockHS2 G x y ≤ (W : ℝ) ^ 2 * (C' + Λ) * ζ ^ 2 * w x y)
    (hh : 0 ≤ h) (x y : Fin L) :
    ‖blockOf G x y‖ ≤ W * max (ω * o₁) (Real.sqrt (C' + Λ) * ζ) * Real.sqrt (w x y) := by
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  rcases le_or_gt (cycDist x y : ℝ) h with hxy | hxy
  · have hw := hshort x y (by linarith)
    have hω0 : 0 < ω := by linarith
    have h1 : ω * o₁ * Real.sqrt (w x y) ≥ o₁ := by
      have hs : Real.sqrt ω⁻¹ ≤ Real.sqrt (w x y) := Real.sqrt_le_sqrt hw
      have hs2 : Real.sqrt ω * Real.sqrt ω⁻¹ = 1 := by
        rw [← Real.sqrt_mul hω0.le, mul_inv_cancel₀ hω0.ne', Real.sqrt_one]
      have hs3 : 1 ≤ Real.sqrt ω := by rw [Real.one_le_sqrt]; exact hω
      have : o₁ ≤ o₁ * (Real.sqrt ω * (Real.sqrt ω * Real.sqrt ω⁻¹)) := by
        rw [hs2, mul_one]; exact le_mul_of_one_le_right ho₁ hs3
      have hsω : Real.sqrt ω * Real.sqrt ω = ω := Real.mul_self_sqrt hω0.le
      calc o₁ ≤ o₁ * (Real.sqrt ω * (Real.sqrt ω * Real.sqrt ω⁻¹)) := this
        _ = ω * o₁ * Real.sqrt ω⁻¹ := by rw [← mul_assoc (Real.sqrt ω), hsω]; ring
        _ ≤ ω * o₁ * Real.sqrt (w x y) := mul_le_mul_of_nonneg_left hs (by positivity)
    calc ‖blockOf G x y‖ ≤ W * o₁ := hop x y
      _ ≤ W * (ω * o₁ * Real.sqrt (w x y)) := mul_le_mul_of_nonneg_left h1 hW0
      _ ≤ W * (max (ω * o₁) (Real.sqrt (C' + Λ) * ζ) * Real.sqrt (w x y)) := by
          gcongr; exact le_max_left _ _
      _ = _ := by ring
  · have h1 := lemmaN_blockOf_le_hs G x y
    have h2 : Real.sqrt (blockHS2 G x y) ≤ W * (Real.sqrt (C' + Λ) * ζ * Real.sqrt (w x y)) := by
      calc Real.sqrt (blockHS2 G x y) ≤ Real.sqrt ((W : ℝ) ^ 2 * ((C' + Λ) * ζ ^ 2 * w x y)) :=
            Real.sqrt_le_sqrt (by have := hlong x y hxy; linarith)
        _ = W * (Real.sqrt (C' + Λ) * ζ * Real.sqrt (w x y)) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hW0,
              lemmaN_sqrt_split hCΛ hζ (hw0 x y)]
    calc ‖blockOf G x y‖ ≤ W * (Real.sqrt (C' + Λ) * ζ * Real.sqrt (w x y)) := h1.trans h2
      _ ≤ W * (max (ω * o₁) (Real.sqrt (C' + Λ) * ζ) * Real.sqrt (w x y)) := by
          gcongr; exact le_max_right _ _
      _ = _ := by ring

/-- The capped weight `w̃ = min{2, K w}` of the near rows. -/
private def lemmaNCap (K₀ : ℝ) {L : ℕ} (w : Fin L → Fin L → ℝ) (x y : Fin L) : ℝ :=
  min 2 (K₀ * w x y)

/-- Weighted operator bound with the capped weight. -/
private theorem lemmaN_hop_cap {W L : ℕ} (hW : 1 ≤ W) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (w : Fin L → Fin L → ℝ) {o₁ ω h C' Λ ζ K₀ : ℝ} (ho₁ : 0 < o₁) (hω : 1 ≤ ω) (hCΛ : 0 ≤ C' + Λ)
    (hζ : 0 ≤ ζ) (hw0 : ∀ x y, 0 ≤ w x y) (hK₀ω : ω ≤ K₀)
    (hK₀ : (C' + Λ) * ζ ^ 2 ≤ o₁ ^ 2 * K₀)
    (hop : ∀ x y, ‖blockOf G x y‖ ≤ W * o₁)
    (hshort : ∀ x y, (cycDist x y : ℝ) ≤ 2 * h → ω⁻¹ ≤ w x y)
    (hlong : ∀ x y, h < cycDist x y → blockHS2 G x y ≤ (W : ℝ) ^ 2 * (C' + Λ) * ζ ^ 2 * w x y)
    (x y : Fin L) :
    ‖blockOf G x y‖ ≤ W * o₁ * Real.sqrt (lemmaNCap K₀ w x y) := by
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hω0 : 0 < ω := by linarith
  have hK0 : 0 < K₀ := by linarith
  rcases le_or_gt 1 (K₀ * w x y) with h1 | h1
  · have hc : 1 ≤ lemmaNCap K₀ w x y := le_min (by norm_num) h1
    have hs : 1 ≤ Real.sqrt (lemmaNCap K₀ w x y) := by rw [Real.one_le_sqrt]; exact hc
    calc ‖blockOf G x y‖ ≤ W * o₁ := hop x y
      _ ≤ W * o₁ * Real.sqrt (lemmaNCap K₀ w x y) := le_mul_of_one_le_right (by positivity) hs
  · have hlong' : h < cycDist x y := by
      by_contra hc
      push Not at hc
      have := hshort x y (by linarith)
      have : 1 ≤ K₀ * w x y := by
        calc (1 : ℝ) = ω * ω⁻¹ := (mul_inv_cancel₀ hω0.ne').symm
          _ ≤ K₀ * w x y := mul_le_mul hK₀ω this (by positivity) hK0.le
      linarith
    have hcap : lemmaNCap K₀ w x y = K₀ * w x y := min_eq_right (by linarith)
    have h2 := lemmaN_blockOf_le_hs G x y
    have h3 : blockHS2 G x y ≤ (W : ℝ) ^ 2 * (o₁ ^ 2 * (K₀ * w x y)) := by
      have := hlong x y hlong'
      have h4 : (C' + Λ) * ζ ^ 2 * w x y ≤ o₁ ^ 2 * K₀ * w x y :=
        mul_le_mul_of_nonneg_right hK₀ (hw0 x y)
      calc blockHS2 G x y ≤ (W : ℝ) ^ 2 * ((C' + Λ) * ζ ^ 2 * w x y) := by linarith
        _ ≤ (W : ℝ) ^ 2 * (o₁ ^ 2 * K₀ * w x y) := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := by ring
    rw [hcap]
    calc ‖blockOf G x y‖ ≤ Real.sqrt (blockHS2 G x y) := h2
      _ ≤ Real.sqrt ((W : ℝ) ^ 2 * (o₁ ^ 2 * (K₀ * w x y))) := Real.sqrt_le_sqrt h3
      _ = W * o₁ * Real.sqrt (K₀ * w x y) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hW0,
            Real.sqrt_sq ho₁.le, mul_assoc]

end RawRows


section PointRates

open scoped Matrix.Norms.L2Operator

/-- Row sums of a symmetric weight from the square-root convolution bound at the diagonal. -/
private theorem lemmaN_weight_rowsum {L : ℕ} (w : Fin L → Fin L → ℝ) (hw0 : ∀ x y, 0 ≤ w x y)
    (hw2 : ∀ x y, w x y ≤ 2) (hws : ∀ x y, w x y = w y x) {Cc ℓ : ℝ} (hCℓ : 0 ≤ Cc * ℓ)
    (hconv : ∀ x y, ∑ c, Real.sqrt (w x c * w c y) ≤ Cc * ℓ * Real.sqrt (w x y)) (y : Fin L) :
    ∑ c, w c y ≤ Real.sqrt 2 * (Cc * ℓ) := by
  have h1 := hconv y y
  have e : ∑ c, Real.sqrt (w y c * w c y) = ∑ c, w c y := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hws y c, Real.sqrt_mul_self (hw0 c y)]
  rw [e] at h1
  have h2 : Real.sqrt (w y y) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (hw2 y y)
  calc ∑ c, w c y ≤ Cc * ℓ * Real.sqrt (w y y) := h1
    _ ≤ Cc * ℓ * Real.sqrt 2 := mul_le_mul_of_nonneg_left h2 hCℓ
    _ = _ := by ring

/-- Convolution bound of the capped weight: `Σ_c w̃(x,c) w̃(c,y) ≤ √2 K₀ Cℓ w̃(x,y)`. -/
private theorem lemmaN_cap_conv {L : ℕ} (w : Fin L → Fin L → ℝ) (hw0 : ∀ x y, 0 ≤ w x y)
    (hw2 : ∀ x y, w x y ≤ 2) (hws : ∀ x y, w x y = w y x) {Cc ℓ K₀ : ℝ} (hCℓ : 0 ≤ Cc * ℓ)
    (hK₀ : 0 ≤ K₀)
    (hconv : ∀ x y, ∑ c, w x c * w c y ≤ Cc * ℓ * w x y ∧
      ∑ c, Real.sqrt (w x c * w c y) ≤ Cc * ℓ * Real.sqrt (w x y)) (x y : Fin L) :
    ∑ c, lemmaNCap K₀ w x c * lemmaNCap K₀ w c y ≤
      Real.sqrt 2 * K₀ * Cc * ℓ * lemmaNCap K₀ w x y := by
  have hcap0 : ∀ x y, 0 ≤ lemmaNCap K₀ w x y := fun x y =>
    le_min (by norm_num) (mul_nonneg hK₀ (hw0 x y))
  have hcapK : ∀ x y, lemmaNCap K₀ w x y ≤ K₀ * w x y := fun x y => min_le_right _ _
  have hcap2 : ∀ x y, lemmaNCap K₀ w x y ≤ 2 := fun x y => min_le_left _ _
  have hs2 : 1 ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
  rcases le_or_gt (K₀ * w x y) 2 with h | h
  · have hc : lemmaNCap K₀ w x y = K₀ * w x y := min_eq_right h
    calc ∑ c, lemmaNCap K₀ w x c * lemmaNCap K₀ w c y ≤ ∑ c, (K₀ * w x c) * (K₀ * w c y) :=
          Finset.sum_le_sum fun c _ => mul_le_mul (hcapK x c) (hcapK c y) (hcap0 c y)
            (mul_nonneg hK₀ (hw0 x c))
      _ = K₀ * K₀ * ∑ c, w x c * w c y := by rw [Finset.mul_sum]; congr 1; ext c; ring
      _ ≤ K₀ * K₀ * (Cc * ℓ * w x y) := mul_le_mul_of_nonneg_left (hconv x y).1 (by positivity)
      _ = 1 * K₀ * Cc * ℓ * lemmaNCap K₀ w x y := by rw [hc]; ring
      _ ≤ Real.sqrt 2 * K₀ * Cc * ℓ * lemmaNCap K₀ w x y := by
          have : 0 ≤ K₀ * Cc * ℓ * lemmaNCap K₀ w x y := by
            have := hcap0 x y
            have : 0 ≤ K₀ * (Cc * ℓ) := mul_nonneg hK₀ hCℓ
            nlinarith
          nlinarith
  · have hc : lemmaNCap K₀ w x y = 2 := min_eq_left h.le
    have hrs := lemmaN_weight_rowsum w hw0 hw2 hws hCℓ (fun x y => (hconv x y).2) y
    calc ∑ c, lemmaNCap K₀ w x c * lemmaNCap K₀ w c y ≤ ∑ c, 2 * (K₀ * w c y) :=
          Finset.sum_le_sum fun c _ => mul_le_mul (hcap2 x c) (hcapK c y) (hcap0 c y)
            (by norm_num)
      _ = 2 * K₀ * ∑ c, w c y := by rw [Finset.mul_sum]; congr 1; ext c; ring
      _ ≤ 2 * K₀ * (Real.sqrt 2 * (Cc * ℓ)) := mul_le_mul_of_nonneg_left hrs (by positivity)
      _ = Real.sqrt 2 * K₀ * Cc * ℓ * lemmaNCap K₀ w x y := by rw [hc]; ring

/-- The raw rows of the generator and the bracket of the mixed-pair error at a good point:
the decomposition (C.16) [fo:eq:pair-error], the light term (C.18) [fo:eq:pair-far-light] at
distant pairs and (C.20) [fo:eq:pair-near-sources] at every pair (capped weight), and the bracket
(C.19) [fo:eq:pair-far-bracket] at distant pairs and (C.20) [fo:eq:pair-near-sources] at every
pair. -/
private theorem lemmaN_point_rows (g E : ℝ) (m : ℂ) {W L : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (w : Fin L → Fin L → ℝ) (hw0 : ∀ x y, 0 ≤ w x y) (hw2 : ∀ x y, w x y ≤ 2)
    (hws : ∀ x y, w x y = w y x) {wmin : ℝ} (hwmin0 : 0 < wmin) (hwmin : ∀ x y, wmin ≤ w x y)
    {Λ ζ Cc ℓ κK o₁ s₀ τ ω h H εw C' K₀ : ℝ} (hΛ : 0 ≤ Λ) (hζ : 0 ≤ ζ) (hCℓ : 0 ≤ Cc * ℓ)
    (ho₁ : 0 < o₁) (hs₀ : 0 ≤ s₀) (hτ : 0 ≤ τ) (hω : 1 ≤ ω) (hh : 0 ≤ h) (hhH : h ≤ H)
    (hC' : 0 ≤ C') (hK₀ω : ω ≤ K₀) (hK₀ : (C' + Λ) * ζ ^ 2 ≤ o₁ ^ 2 * K₀)
    (hD : ∀ x y, ‖resLoop g E m ![x, y] ![true, false] u M -
      primLoop g W L E m u ![x, y] ![true, false]‖ ≤ Λ * ζ ^ 2 * w x y)
    (hconv : ∀ x y, ∑ c, w x c * w c y ≤ Cc * ℓ * w x y ∧
      ∑ c, Real.sqrt (w x c * w c y) ≤ Cc * ℓ * Real.sqrt (w x y))
    (hker : ∀ x y, ∑ c, mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) u x c *
      w c y ≤ κK * w x y)
    (hop : ∀ x y, ‖blockOf (resolventMat M (zChar g E m u)) x y‖ ≤ W * o₁)
    (hhs : ∀ x y, blockHS2 (resolventMat M (zChar g E m u)) x y ≤ (W : ℝ) ^ 2 * s₀)
    (havg : ∀ c, ‖blockTr (resolventMat M (zChar g E m u) -
      dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c‖ ≤ τ)
    (hprim : ∀ x y, h < cycDist x y →
      ‖primLoop g W L E m u ![x, y] ![true, false]‖ ≤ C' * ζ ^ 2 * w x y)
    (hshort : ∀ x y, (cycDist x y : ℝ) ≤ 2 * h → ω⁻¹ ≤ w x y)
    (hfar : ∀ x y, H < cycDist x y → w x y ≤ εw) (a b : Fin L) :
    ‖blockGen W L (gammaG g) (fun r N => resLoop g E m ![a, b] ![true, false] r N -
        primLoop g W L E m r ![a, b] ![true, false]) u M‖ ≤
      ‖lightW g E m ![a, b] ![true, false] u M‖ + 2 * κK * (Λ * ζ ^ 2) * w a b +
        gammaG g * W * ((Λ * ζ ^ 2) ^ 2 * Cc * ℓ * w a b) ∧
    (2 * h < cycDist a b → ‖lightW g E m ![a, b] ![true, false] u M‖ ≤
      2 * gammaG g * W * τ * (C' + Λ) * ζ ^ 2 * max (ω * o₁) (Real.sqrt (C' + Λ) * ζ) * Cc *
        ℓ * w a b) ∧
    ‖lightW g E m ![a, b] ![true, false] u M‖ ≤ 2 * Real.sqrt 2 * gammaG g * W * τ * o₁ *
      ((4 * H + 2) * s₀ + L * Real.sqrt (s₀ * max ((C' + Λ) * ζ ^ 2 / K₀) (s₀ / 2) * 1 ^ 2 *
        (K₀ * εw))) ∧
    (2 * h < cycDist a b → (blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, false] u)
        (resLoop g E m ![a, b] ![true, false] u) M).re ≤
      4 * gammaG g * W * ((C' + Λ) * ζ ^ 2 * w a b) *
        max (ω * o₁) (Real.sqrt (C' + Λ) * ζ) ^ 4 * Cc * ℓ * w a b) ∧
    (blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, false] u)
        (resLoop g E m ![a, b] ![true, false] u) M).re ≤
      4 * gammaG g * W * s₀ * o₁ ^ 4 * (Real.sqrt 2 * K₀ * Cc) * ℓ * 2 := by
  set G := resolventMat M (zChar g E m u) with hG
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hL1 : 1 ≤ L := by omega
  have hK0 : 0 < K₀ := by linarith
  have hCΛ : 0 ≤ C' + Λ := by linarith
  -- the long-edge Hilbert–Schmidt bound
  have hlong : ∀ x y, h < cycDist x y →
      blockHS2 G x y ≤ (W : ℝ) ^ 2 * (C' + Λ) * ζ ^ 2 * w x y := by
    intro x y hxy
    have hyx : h < cycDist y x := by rw [lemmaN_cycDist_comm]; exact hxy
    have hP := hprim y x hyx
    have hDyx := hD y x
    rw [hws y x] at hP hDyx
    exact lemmaN_hs_long hW G _ hP hDyx
  have havg' : ∀ (c : Fin L) (s : Bool), ‖loopTr G ![c] ![s] - sgnScalar m s‖ ≤ τ := by
    intro c s
    rw [lemmaN_loop_one_sub g E W L hW hL1 m hm G c s]
    exact havg c
  -- the distant weighted operator bound
  have hopd := lemmaN_hop_dist hW G w ho₁.le hω hCΛ hζ hw0 hop hshort hlong hh
  -- the capped weight
  set wc := lemmaNCap K₀ w with hwc
  have hwc0 : ∀ x y, 0 ≤ wc x y := fun x y => le_min (by norm_num) (mul_nonneg hK0.le (hw0 x y))
  have hwc2 : ∀ x y, wc x y ≤ 2 := fun x y => min_le_left _ _
  have hwcs : ∀ x y, wc x y = wc y x := fun x y => by simp only [hwc, lemmaNCap, hws x y]
  have hwcK : ∀ x y, wc x y ≤ K₀ * w x y := fun x y => min_le_right _ _
  have hopc := lemmaN_hop_cap hW G w ho₁ hω hCΛ hζ hw0 hK₀ω hK₀ hop hshort hlong
  -- the decomposition of the generator
  have hgen := blockGen_pairErr g E m W L hW hL hm ⟨by linarith, hu1⟩ hM a b
  set K := mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) u with hK
  set Dm : Fin L → Fin L → ℂ := fun x y => resLoop g E m ![x, y] ![true, false] u M -
    primLoop g W L E m u ![x, y] ![true, false] with hDm
  have hKs : ∀ x y, K x y = K y x := fun x y =>
    lemmaN_mixedKer_symm _ (lemmaN_pairP_symm _ _ _ _ _) u x y
  have hP0 : ∀ x y, 0 ≤ pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) x y := by
    intro x y; simp only [pairP, Matrix.of_apply]; positivity
  have hProw : ∀ x, ∑ y, pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) x y = 1 :=
    fun x => pairP_row_sum (hopB g) (gammaG g) hγ L hL1 E m hm x
  have hK0' : ∀ x y, 0 ≤ K x y := (mixedKer_nonneg_row _ hP0 hProw u hu0 hu1).1
  have hrowK := lemmaN_row_kernel K Dm w (mul_nonneg hΛ (sq_nonneg ζ)) hK0' hKs hws
    (fun x y => by have := hD x y; simp only [hDm]; linarith) hker a b
  have hquad := lemmaNRates_quad Dm w (mul_nonneg hΛ (sq_nonneg ζ)) hw0
    (fun x y => by have := hD x y; simp only [hDm]; linarith) (fun x y => (hconv x y).1) a b
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hgen]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) ?_
    · have : 2 * κK * (Λ * ζ ^ 2) * w a b = 2 * κK * (Λ * ζ ^ 2) * w a b := rfl
      calc _ ≤ 2 * κK * (Λ * ζ ^ 2) * w a b := hrowK
        _ = _ := rfl
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hquad (by positivity)
  · intro hab
    have hl := (lemmaNRates_light g E m hW u M w hw0 hw2 hws (Cw := Cc) (ℓ := ℓ) (h := h) (H := h)
      (τ := τ) (o := max (ω * o₁) (Real.sqrt (C' + Λ) * ζ)) (s₀ := s₀) (Λ := C' + Λ) (ζ := ζ)
      (ε₀ := 2) hτ (le_max_of_le_left (by positivity)) hs₀ hCΛ hh le_rfl
      (fun x y => (hconv x y).2) havg' hopd hhs (fun x y hxy => hlong x y hxy)
      (fun x y _ => hw2 x y) a b).1 hab
    calc _ ≤ _ := hl
      _ = _ := by ring
  · set Λt := max ((C' + Λ) * ζ ^ 2 / K₀) (s₀ / 2) with hΛt
    have hΛt0 : 0 ≤ Λt := le_max_of_le_right (by positivity)
    have hwlow : ∀ x y, min 2 (K₀ * wmin) ≤ wc x y := fun x y =>
      min_le_min le_rfl (mul_le_mul_of_nonneg_left (hwmin x y) hK0.le)
    have hwl0 : 0 < min 2 (K₀ * wmin) := lt_min (by norm_num) (mul_pos hK0 hwmin0)
    have hconvc : ∀ x y, ∑ c, Real.sqrt (wc x c * wc c y) ≤
        (2 * L / Real.sqrt (min 2 (K₀ * wmin))) * 1 * Real.sqrt (wc x y) := by
      intro x y
      have hs : 0 < Real.sqrt (min 2 (K₀ * wmin)) := Real.sqrt_pos.2 hwl0
      have h1 : ∑ c, Real.sqrt (wc x c * wc c y) ≤ ∑ _c : Fin L, (2 : ℝ) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [Real.sqrt_le_left (by norm_num)]
        nlinarith [hwc2 x c, hwc2 c y, hwc0 x c, hwc0 c y]
      have h2 : ∑ _c : Fin L, (2 : ℝ) = 2 * L := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      have h3 : Real.sqrt (min 2 (K₀ * wmin)) ≤ Real.sqrt (wc x y) := Real.sqrt_le_sqrt (hwlow x y)
      rw [h2] at h1
      calc _ ≤ 2 * (L : ℝ) := h1
        _ = 2 * L / Real.sqrt (min 2 (K₀ * wmin)) * 1 * Real.sqrt (min 2 (K₀ * wmin)) := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hhsc : ∀ x y, h < cycDist x y → blockHS2 G x y ≤ (W : ℝ) ^ 2 * Λt * 1 ^ 2 * wc x y := by
      intro x y hxy
      rw [one_pow, mul_one]
      rcases le_or_gt (K₀ * w x y) 2 with h2 | h2
      · have hc : wc x y = K₀ * w x y := min_eq_right h2
        rw [hc]
        have h3 := hlong x y hxy
        have h5 : (C' + Λ) * ζ ^ 2 / K₀ ≤ Λt := le_max_left _ _
        calc blockHS2 G x y ≤ (W : ℝ) ^ 2 * ((C' + Λ) * ζ ^ 2) * w x y := by linarith
          _ = (W : ℝ) ^ 2 * ((C' + Λ) * ζ ^ 2 / K₀) * (K₀ * w x y) := by field_simp
          _ ≤ (W : ℝ) ^ 2 * Λt * (K₀ * w x y) := by gcongr; exact mul_nonneg hK0.le (hw0 x y)
      · have hc : wc x y = 2 := min_eq_left h2.le
        rw [hc]
        have h5 : s₀ / 2 ≤ Λt := le_max_right _ _
        calc blockHS2 G x y ≤ (W : ℝ) ^ 2 * s₀ := hhs x y
          _ = (W : ℝ) ^ 2 * (s₀ / 2) * 2 := by ring
          _ ≤ (W : ℝ) ^ 2 * Λt * 2 := by gcongr
    have hfarc : ∀ x y, H < cycDist x y → wc x y ≤ K₀ * εw := fun x y hxy =>
      (hwcK x y).trans (mul_le_mul_of_nonneg_left (hfar x y hxy) hK0.le)
    have hl := (lemmaNRates_light g E m hW u M wc hwc0 hwc2 hwcs
      (Cw := 2 * L / Real.sqrt (min 2 (K₀ * wmin))) (ℓ := 1) (h := h) (H := H) (τ := τ) (o := o₁)
      (s₀ := s₀) (Λ := Λt) (ζ := 1) (ε₀ := K₀ * εw) hτ ho₁.le hs₀ hΛt0 (hh.trans hhH) hhH
      hconvc havg' hopc hhs hhsc hfarc a b).2
    exact hl
  · intro hab
    have hab' : h < cycDist b a := by
      rw [lemmaN_cycDist_comm]
      have : (0 : ℝ) ≤ 2 * h - h := by linarith
      linarith
    have hη := hlong b a hab'
    rw [hws b a] at hη
    have hb := lemmaNRates_bracket g E m hm.1 hW hu1 hM w hw0 hws
      (Cw := Cc) (ℓ := ℓ) (o := max (ω * o₁) (Real.sqrt (C' + Λ) * ζ))
      (η := (C' + Λ) * ζ ^ 2 * w a b) (le_max_of_le_left (by positivity))
      (fun x y => (hconv x y).1) hopd a b (by linarith)
    calc _ ≤ _ := hb
      _ = _ := by ring
  · have hcc : ∀ x y, ∑ c, wc x c * wc c y ≤ (Real.sqrt 2 * K₀ * Cc) * ℓ * wc x y := by
      intro x y
      have := lemmaN_cap_conv w hw0 hw2 hws hCℓ hK0.le hconv x y
      calc _ ≤ _ := this
        _ = _ := by ring
    have hb := lemmaNRates_bracket g E m hm.1 hW hu1 hM wc hwc0 hwcs
      (Cw := Real.sqrt 2 * K₀ * Cc) (ℓ := ℓ) (o := o₁) (η := s₀) ho₁.le hcc hopc a b (hhs b a)
    refine hb.trans ?_
    have h4 : 0 ≤ 4 * gammaG g * W * s₀ * o₁ ^ 4 * (Real.sqrt 2 * K₀ * Cc) * ℓ := by
      have : 0 ≤ Real.sqrt 2 * K₀ * (Cc * ℓ) := by positivity
      have e : 4 * gammaG g * W * s₀ * o₁ ^ 4 * (Real.sqrt 2 * K₀ * Cc) * ℓ =
          4 * gammaG g * W * s₀ * o₁ ^ 4 * (Real.sqrt 2 * K₀ * (Cc * ℓ)) := by ring
      rw [e]; positivity
    exact mul_le_mul_of_nonneg_left (hwc2 a b) h4

end PointRates

/-! ### Normalized rows

Notation: `ω = W^a` is the unit of small losses, `P = R^M`, `ζu ≤ ζv ≤ ζt` the scales at the
current, terminal and final times, `eu = 1 - u`, `ev = 1 - v`, `Γ = γ_g W ℓ_v` with
`Γ ζv ev = 1`, and `X ∈ [R⁴ω²⁵, ω¹⁰⁰P]` the value of the surrogate. -/

section NumRows

variable {ω R P X ζu ζv ζt Γ eu ev : ℝ}

/-- `1/ev ≤ R/eu`. -/
private theorem lemmaN_inv_ev (heu : 0 < eu) (hev : 0 < ev) (h4 : eu ≤ R * ev) : ev⁻¹ ≤ R * eu⁻¹ := by
  rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hev heu]
  linarith

/-- Quadratic row. -/
private theorem lemmaN_num_quad (hω : 2 ≤ ω) (hR : 1 ≤ R) (hP : 0 ≤ P) (hX : 1 ≤ X) (hζv : 0 < ζv)
    (hζt : ζv ≤ ζt) (heu : 0 < eu) (hev : 0 < ev) (hΓ : Γ * ζv * ev = 1) (h4 : eu ≤ R * ev)
    (hRP : R ^ 3 * P * ζt * ω ^ 400 ≤ 1) (hXP : X ≤ ω ^ 100 * P) {Cc Λ : ℝ} (hCc : 0 ≤ Cc)
    (hCcω : Cc ≤ ω) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ ω * X) :
    Γ * (Λ ^ 2 * Cc) * ζv ^ 2 ≤ X / (4 * ω) * eu⁻¹ := by
  have hω0 : 0 < ω := by linarith
  have hζt0 : 0 < ζt := lt_of_lt_of_le hζv hζt
  have hΓ' : Γ * ζv = ev⁻¹ := by field_simp; linarith
  have hie := lemmaN_inv_ev heu hev h4
  have hR3 : R * P * ζt ≤ R ^ 3 * P * ζt := by
    have : R ≤ R ^ 3 := le_self_pow₀ hR (by norm_num)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hP) hζt0.le
  calc Γ * (Λ ^ 2 * Cc) * ζv ^ 2 = (Γ * ζv) * (Λ ^ 2 * Cc * ζv) := by ring
    _ = ev⁻¹ * (Λ ^ 2 * Cc * ζv) := by rw [hΓ']
    _ ≤ (R * eu⁻¹) * ((ω * X) ^ 2 * ω * ζt) := by
        gcongr
    _ = ω ^ 3 * X * (X * R * ζt) * eu⁻¹ := by ring
    _ ≤ ω ^ 3 * X * (ω ^ 100 * P * R * ζt) * eu⁻¹ := by gcongr
    _ = ω ^ 103 * (R * P * ζt) * X * eu⁻¹ := by ring
    _ ≤ ω ^ 103 * (R ^ 3 * P * ζt) * X * eu⁻¹ := by gcongr
    _ ≤ X / (4 * ω) * eu⁻¹ := by
        have h1 : ω ^ 103 * (R ^ 3 * P * ζt) * (4 * ω) ≤ 1 := by
          have h2 : 4 * ω ^ 104 ≤ ω ^ 400 := by
            have : (4 : ℝ) ≤ ω ^ 296 := by
              calc (4 : ℝ) = 2 ^ 2 := by norm_num
                _ ≤ ω ^ 2 := by gcongr
                _ ≤ ω ^ 296 := pow_le_pow_right₀ (by linarith) (by norm_num)
            calc 4 * ω ^ 104 ≤ ω ^ 296 * ω ^ 104 := by gcongr
              _ = ω ^ 400 := by ring
          have h3 : 0 ≤ R ^ 3 * P * ζt := by positivity
          calc ω ^ 103 * (R ^ 3 * P * ζt) * (4 * ω) = (4 * ω ^ 104) * (R ^ 3 * P * ζt) := by ring
            _ ≤ ω ^ 400 * (R ^ 3 * P * ζt) := by gcongr
            _ = R ^ 3 * P * ζt * ω ^ 400 := by ring
            _ ≤ 1 := hRP
        have h5 : ω ^ 103 * (R ^ 3 * P * ζt) ≤ 1 / (4 * ω) := by
          rw [le_div_iff₀ (by positivity)]; exact h1
        calc ω ^ 103 * (R ^ 3 * P * ζt) * X * eu⁻¹ ≤ 1 / (4 * ω) * X * eu⁻¹ := by gcongr
          _ = X / (4 * ω) * eu⁻¹ := by ring

/-- `ω^k` is large: `c ≤ ω^n` from `2 ≤ ω` and `c ≤ 2^n`. -/
private theorem lemmaN_pow_big (hω : 2 ≤ ω) {c : ℝ} (n : ℕ) (hc : c ≤ 2 ^ n) : c ≤ ω ^ n :=
  hc.trans (pow_le_pow_left₀ (by norm_num) hω n)

/-- `(a + b)⁴ ≤ 8(a⁴ + b⁴)`. -/
private theorem lemmaN_add_pow_four {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb, sq_nonneg (a ^ 2 - b ^ 2),
    mul_nonneg (mul_nonneg ha hb) (sq_nonneg (a - b))]

/-- `max (ω o₁) (√Λ' ζv) ≤ ω o₁ + Λ' ζv` for `Λ' ≥ 1`. -/
private theorem lemmaN_od_le {o₁ Λ' : ℝ} (hω : 0 ≤ ω) (ho₁ : 0 ≤ o₁) (hΛ' : 1 ≤ Λ') (hζv : 0 ≤ ζv) :
    max (ω * o₁) (Real.sqrt Λ' * ζv) ≤ ω * o₁ + Λ' * ζv := by
  have hs : Real.sqrt Λ' ≤ Λ' := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h0 : 0 ≤ Λ' * ζv := mul_nonneg (by linarith) hζv
  refine max_le (by linarith) ?_
  have : Real.sqrt Λ' * ζv ≤ Λ' * ζv := mul_le_mul_of_nonneg_right hs hζv
  nlinarith [mul_nonneg hω ho₁]

/-- `c ω^m ≤ ω^n` from `c ≤ 2^k`, `m + k ≤ n`, `ω ≥ 2`. -/
private theorem lemmaN_cpow (hω : 2 ≤ ω) {c : ℝ} {k m n : ℕ} (hc : c ≤ 2 ^ k) (hmn : m + k ≤ n) :
    c * ω ^ m ≤ ω ^ n := by
  have hω0 : 0 ≤ ω := by linarith
  have h1 : c ≤ ω ^ k := lemmaN_pow_big hω k hc
  calc c * ω ^ m ≤ ω ^ k * ω ^ m := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ω ^ (m + k) := by rw [pow_add, mul_comm]
    _ ≤ ω ^ n := pow_le_pow_right₀ (by linarith) hmn

/-- `c ω^m A ≤ 1` from `A ω^n ≤ 1` and `c ω^m ≤ ω^n`. -/
private theorem lemmaN_small {A c : ℝ} {m n : ℕ} (hA0 : 0 ≤ A) (hA : A * ω ^ n ≤ 1)
    (hc : c * ω ^ m ≤ ω ^ n) : c * ω ^ m * A ≤ 1 := by
  calc c * ω ^ m * A ≤ ω ^ n * A := mul_le_mul_of_nonneg_right hc hA0
    _ = A * ω ^ n := mul_comm _ _
    _ ≤ 1 := hA

/-- The final normalization `K X eu⁻¹ ≤ X/(4ω) eu⁻¹` from `4ωK ≤ 1`. -/
private theorem lemmaN_fin {K X eu : ℝ} (hω : 0 < ω) (hK : K * (4 * ω) ≤ 1) (hX : 0 ≤ X)
    (heu : 0 < eu) : K * X * eu⁻¹ ≤ X / (4 * ω) * eu⁻¹ := by
  have h1 : K ≤ 1 / (4 * ω) := by rw [le_div_iff₀ (by positivity)]; exact hK
  calc K * X * eu⁻¹ ≤ 1 / (4 * ω) * X * eu⁻¹ := by gcongr
    _ = X / (4 * ω) * eu⁻¹ := by ring

/-- Distant light row. -/
private theorem lemmaN_num_dlight (hω : 2 ≤ ω) (hR : 1 ≤ R) (hP : 0 ≤ P) (hX : 1 ≤ X) (hζu : 0 < ζu)
    (hζuv : ζu ≤ ζv) (hζt : ζv ≤ ζt) (heu : 0 < eu) (hev : 0 < ev) (h4 : eu ≤ R * ev)
    (hRP : R ^ 3 * P * ζt * ω ^ 400 ≤ 1) (hR5 : R ^ 5 * ζt * ω ^ 400 ≤ 1)
    (hXP : X ≤ ω ^ 100 * P) {γ Wr ℓv Cc Λ' wab : ℝ} (hΓ : γ * Wr * ℓv * ζv * ev = 1)
    (hCc : 0 ≤ Cc) (hCcω : Cc ≤ ω) (hΛ1 : 1 ≤ Λ') (hΛ : Λ' ≤ ω ^ 2 * X)
    (hw : 0 ≤ wab) :
    2 * γ * Wr * (ω * R ^ 2 * ζu) * Λ' * ζv ^ 2 * max (ω * (ω * R * ζu)) (Real.sqrt Λ' * ζv) *
        Cc * ℓv * wab ≤ X / (4 * ω) * eu⁻¹ * (ζv ^ 2 * wab) := by
  have hω0 : 0 < ω := by linarith
  have hζv : 0 < ζv := lt_of_lt_of_le hζu hζuv
  have hζt0 : 0 < ζt := lt_of_lt_of_le hζv hζt
  have hζut : ζu ≤ ζt := hζuv.trans hζt
  have hie := lemmaN_inv_ev heu hev h4
  have hΓ' : γ * Wr * ℓv = ζv⁻¹ * ev⁻¹ := by field_simp; linarith
  have hod := lemmaN_od_le hω0.le (by positivity : 0 ≤ ω * R * ζu) hΛ1 hζv.le
  have hq : ζu * ζv⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hζv]; exact hζuv
  have hR45 : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR (by norm_num)
  have hXΛ : Λ' * ζv ≤ ω ^ 2 * X * ζt := mul_le_mul hΛ hζt hζv.le (by positivity)
  -- the coefficient
  have key : 2 * (γ * Wr * ℓv) * (ω * R ^ 2 * ζu) * Λ' *
      max (ω * (ω * R * ζu)) (Real.sqrt Λ' * ζv) * Cc ≤ X / (4 * ω) * eu⁻¹ := by
    rw [hΓ']
    calc 2 * (ζv⁻¹ * ev⁻¹) * (ω * R ^ 2 * ζu) * Λ' * max (ω * (ω * R * ζu)) (Real.sqrt Λ' * ζv) *
          Cc = 2 * ω * R ^ 2 * (ζu * ζv⁻¹) * ev⁻¹ * Λ' *
            max (ω * (ω * R * ζu)) (Real.sqrt Λ' * ζv) * Cc := by ring
      _ ≤ 2 * ω * R ^ 2 * 1 * (R * eu⁻¹) * (ω ^ 2 * X) * (ω * (ω * R * ζu) + Λ' * ζv) * ω := by
          gcongr
      _ ≤ 2 * ω * R ^ 2 * 1 * (R * eu⁻¹) * (ω ^ 2 * X) * (ω * (ω * R * ζt) + ω ^ 2 * X * ζt) *
            ω := by gcongr
      _ = 2 * ω ^ 6 * (R ^ 4 * ζt + R ^ 3 * X * ζt) * X * eu⁻¹ := by ring
      _ ≤ 2 * ω ^ 6 * (R ^ 5 * ζt + R ^ 3 * (ω ^ 100 * P) * ζt) * X * eu⁻¹ := by gcongr
      _ ≤ X / (4 * ω) * eu⁻¹ := by
          refine lemmaN_fin hω0 ?_ (by linarith) heu
          have h1 : 16 * ω ^ 7 * (R ^ 5 * ζt) ≤ 1 :=
            lemmaN_small (by positivity) hR5 (lemmaN_cpow hω (k := 4) (by norm_num) (by norm_num))
          have h2 : 16 * ω ^ 7 * (R ^ 3 * P * ζt) * ω ^ 100 ≤ 1 := by
            have := lemmaN_small (n := 400) (m := 107) (c := 16) (A := R ^ 3 * P * ζt)
              (by positivity) hRP (lemmaN_cpow hω (k := 4) (by norm_num) (by norm_num))
            calc 16 * ω ^ 7 * (R ^ 3 * P * ζt) * ω ^ 100 = 16 * ω ^ 107 * (R ^ 3 * P * ζt) := by
                  ring
              _ ≤ 1 := this
          nlinarith [h1, h2]
  calc _ = (2 * (γ * Wr * ℓv) * (ω * R ^ 2 * ζu) * Λ' *
        max (ω * (ω * R * ζu)) (Real.sqrt Λ' * ζv) * Cc) * (ζv ^ 2 * wab) := by ring
    _ ≤ X / (4 * ω) * eu⁻¹ * (ζv ^ 2 * wab) := by gcongr

/-- `ζu² ev⁻¹ ≤ ζv² eu⁻¹` from `ζu² eu ≤ ζv² ev`. -/
private theorem lemmaN_zeta_inv (heu : 0 < eu) (hev : 0 < ev) (hZ : ζu ^ 2 * eu ≤ ζv ^ 2 * ev) :
    ζu ^ 2 * ev⁻¹ ≤ ζv ^ 2 * eu⁻¹ := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hev heu]
  linarith

/-- Near light row (capped weight, halo `H = ℓ_v λ_H`). -/
private theorem lemmaN_num_nlight (hω : 2 ≤ ω) (hR : 1 ≤ R) (hζu : 0 < ζu) (hζuv : ζu ≤ ζv)
    (heu : 0 < eu) (hev : 0 < ev) (hZ : ζu ^ 2 * eu ≤ ζv ^ 2 * ev) (hX1 : R ^ 4 * ω ^ 25 ≤ X)
    {γ Wr ℓv Λt K₀εw lH Lr wab : ℝ} (hΓ : γ * Wr * ℓv * ζv * ev = 1) (hℓv : 1 ≤ ℓv)
    (hΛt0 : 0 ≤ Λt) (hΛt : Λt ≤ ω * R * ζu) (hKε : 0 ≤ K₀εw) (hLr : Lr * Real.sqrt K₀εw ≤ ℓv)
    (hlH0 : 0 ≤ lH) (hlH : lH ≤ ω) (hw : ω⁻¹ ≤ wab) :
    2 * Real.sqrt 2 * γ * Wr * (ω * R ^ 2 * ζu) * (ω * R * ζu) *
        ((4 * (ℓv * lH) + 2) * (ω * R * ζu) +
          Lr * Real.sqrt ((ω * R * ζu) * Λt * 1 ^ 2 * K₀εw)) ≤
      X / (4 * ω) * eu⁻¹ * (ζv ^ 2 * wab) := by
  have hω0 : 0 < ω := by linarith
  have hζv : 0 < ζv := lt_of_lt_of_le hζu hζuv
  set s₀ := ω * R * ζu with hs₀
  have hs₀0 : 0 ≤ s₀ := by positivity
  have hΓ' : γ * Wr * ℓv = ζv⁻¹ * ev⁻¹ := by field_simp; linarith
  have hsq : Lr * Real.sqrt (s₀ * Λt * 1 ^ 2 * K₀εw) ≤ s₀ * ℓv := by
    rcases le_or_gt Lr 0 with hL | hL
    · have : Lr * Real.sqrt (s₀ * Λt * 1 ^ 2 * K₀εw) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hL (Real.sqrt_nonneg _)
      have : 0 ≤ s₀ * ℓv := by positivity
      linarith
    · have hin : s₀ * Λt * 1 ^ 2 * K₀εw ≤ s₀ ^ 2 * K₀εw := by
        have : s₀ * Λt ≤ s₀ * s₀ := mul_le_mul_of_nonneg_left hΛt hs₀0
        rw [one_pow, mul_one, sq]
        exact mul_le_mul_of_nonneg_right this hKε
      calc Lr * Real.sqrt (s₀ * Λt * 1 ^ 2 * K₀εw) ≤ Lr * Real.sqrt (s₀ ^ 2 * K₀εw) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hin) hL.le
        _ = s₀ * (Lr * Real.sqrt K₀εw) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs₀0]; ring
        _ ≤ s₀ * ℓv := mul_le_mul_of_nonneg_left hLr hs₀0
  have hbr : (4 * (ℓv * lH) + 2) * s₀ + Lr * Real.sqrt (s₀ * Λt * 1 ^ 2 * K₀εw) ≤
      7 * ω * ℓv * s₀ := by
    have h1 : ℓv * lH ≤ ℓv * ω := mul_le_mul_of_nonneg_left hlH (by linarith)
    have h2 : (4 * (ℓv * lH) + 2) * s₀ ≤ (4 * (ℓv * ω) + 2 * (ℓv * ω)) * s₀ := by
      gcongr
      nlinarith
    have h3 : s₀ * ℓv ≤ s₀ * (ℓv * ω) := by
      have : ℓv ≤ ℓv * ω := le_mul_of_one_le_right (by linarith) (by linarith)
      exact mul_le_mul_of_nonneg_left this hs₀0
    nlinarith
  have hzi := lemmaN_zeta_inv heu hev hZ
  calc 2 * Real.sqrt 2 * γ * Wr * (ω * R ^ 2 * ζu) * s₀ *
        ((4 * (ℓv * lH) + 2) * s₀ + Lr * Real.sqrt (s₀ * Λt * 1 ^ 2 * K₀εw))
      ≤ 2 * Real.sqrt 2 * γ * Wr * (ω * R ^ 2 * ζu) * s₀ * (7 * ω * ℓv * s₀) := by
        have : 0 ≤ γ * Wr * ℓv := by rw [hΓ']; positivity
        have h0 : 0 ≤ 2 * Real.sqrt 2 * γ * Wr * (ω * R ^ 2 * ζu) * s₀ := by
          have hγW : 0 ≤ γ * Wr := by
            have := mul_nonneg this (inv_nonneg.2 (by linarith : (0 : ℝ) ≤ ℓv))
            rwa [mul_assoc, mul_inv_cancel₀ (by linarith), mul_one] at this
          have : 0 ≤ 2 * Real.sqrt 2 * (γ * Wr) * (ω * R ^ 2 * ζu) * s₀ := by positivity
          linarith [show 2 * Real.sqrt 2 * γ * Wr * (ω * R ^ 2 * ζu) * s₀ =
            2 * Real.sqrt 2 * (γ * Wr) * (ω * R ^ 2 * ζu) * s₀ by ring]
        exact mul_le_mul_of_nonneg_left hbr h0
    _ = 14 * Real.sqrt 2 * ω ^ 4 * R ^ 4 * ζu * (ζu ^ 2 * ev⁻¹) * (γ * Wr * ℓv * ev) := by
        rw [hs₀]; field_simp; ring
    _ = 14 * Real.sqrt 2 * ω ^ 4 * R ^ 4 * ζu * (ζu ^ 2 * ev⁻¹) * ζv⁻¹ := by
        rw [hΓ']; field_simp
    _ ≤ 14 * Real.sqrt 2 * ω ^ 4 * R ^ 4 * ζv * (ζv ^ 2 * eu⁻¹) * ζv⁻¹ := by gcongr
    _ = (14 * Real.sqrt 2 * ω ^ 4 * R ^ 4) * ζv ^ 2 * eu⁻¹ := by field_simp
    _ ≤ X / (4 * ω) * eu⁻¹ * (ζv ^ 2 * ω⁻¹) := by
        have hc : 14 * Real.sqrt 2 * ω ^ 4 * R ^ 4 * (4 * ω * ω) ≤ X := by
          have hs2 : Real.sqrt 2 ≤ 2 := by
            rw [Real.sqrt_le_left (by norm_num)]; norm_num
          have h1 : 14 * Real.sqrt 2 * 4 * ω ^ 6 ≤ ω ^ 25 := by
            have : 14 * Real.sqrt 2 * 4 ≤ 2 ^ 7 := by nlinarith
            exact lemmaN_cpow hω this (by norm_num)
          calc 14 * Real.sqrt 2 * ω ^ 4 * R ^ 4 * (4 * ω * ω) =
                (14 * Real.sqrt 2 * 4 * ω ^ 6) * R ^ 4 := by ring
            _ ≤ ω ^ 25 * R ^ 4 := by gcongr
            _ = R ^ 4 * ω ^ 25 := by ring
            _ ≤ X := hX1
        have h4 : 14 * Real.sqrt 2 * ω ^ 4 * R ^ 4 ≤ X / (4 * ω) * ω⁻¹ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), ← div_eq_mul_inv,
            le_div_iff₀ hω0]
          linarith [hc, show 14 * Real.sqrt 2 * ω ^ 4 * R ^ 4 * (4 * ω * ω) =
            14 * Real.sqrt 2 * ω ^ 4 * R ^ 4 * (4 * ω) * ω by ring]
        calc (14 * Real.sqrt 2 * ω ^ 4 * R ^ 4) * ζv ^ 2 * eu⁻¹ ≤
              (X / (4 * ω) * ω⁻¹) * ζv ^ 2 * eu⁻¹ := by gcongr
          _ = X / (4 * ω) * eu⁻¹ * (ζv ^ 2 * ω⁻¹) := by ring
    _ ≤ X / (4 * ω) * eu⁻¹ * (ζv ^ 2 * wab) := by
        have : 0 ≤ X := by have := pow_pos (lt_of_lt_of_le one_pos hR) 4; nlinarith [pow_pos hω0 25]
        gcongr

/-- Distant bracket row. -/
private theorem lemmaN_num_dbracket (hω : 2 ≤ ω) (hR : 1 ≤ R) (hP : 0 ≤ P) (hX : 1 ≤ X) (hζu : 0 < ζu)
    (hζuv : ζu ≤ ζv) (hζt : ζv ≤ ζt) (heu : 0 < eu) (hev : 0 < ev) (h4 : eu ≤ R * ev)
    (hRP : R ^ 3 * P * ζt * ω ^ 400 ≤ 1) (hR5 : R ^ 5 * ζt * ω ^ 400 ≤ 1)
    (hXP : X ≤ ω ^ 100 * P) {γ Wr ℓv Cc Λ' wab : ℝ} (hΓ : γ * Wr * ℓv * ζv * ev = 1)
    (hCc : 0 ≤ Cc) (hCcω : Cc ≤ ω) (hΛ1 : 1 ≤ Λ') (hΛ : Λ' ≤ ω ^ 2 * X) (hw : 0 ≤ wab) :
    4 * γ * Wr * (Λ' * ζv ^ 2 * wab) * max (ω * (ω * R * ζu)) (Real.sqrt Λ' * ζv) ^ 4 * Cc *
        ℓv * wab ≤ X ^ 2 / (2 * ω) * eu⁻¹ * (ζv ^ 2 * wab) ^ 2 := by
  have hω0 : 0 < ω := by linarith
  have hζv : 0 < ζv := lt_of_lt_of_le hζu hζuv
  have hζt0 : 0 < ζt := lt_of_lt_of_le hζv hζt
  have hζut : ζu ≤ ζt := hζuv.trans hζt
  have hie := lemmaN_inv_ev heu hev h4
  have hΓ' : γ * Wr * ℓv = ζv⁻¹ * ev⁻¹ := by field_simp; linarith
  have hΛ0 : 0 ≤ Λ' := by linarith
  have hod : max (ω * (ω * R * ζu)) (Real.sqrt Λ' * ζv) ≤ ω * (ω * R * ζu) + Real.sqrt Λ' * ζv := by
    have h1 : 0 ≤ Real.sqrt Λ' * ζv := by positivity
    have h2 : 0 ≤ ω * (ω * R * ζu) := by positivity
    exact max_le (by linarith) (by linarith)
  have hod4 : max (ω * (ω * R * ζu)) (Real.sqrt Λ' * ζv) ^ 4 ≤
      8 * ((ω * (ω * R * ζu)) ^ 4 + Λ' ^ 2 * ζv ^ 4) := by
    have h1 := lemmaN_add_pow_four (by positivity : 0 ≤ ω * (ω * R * ζu))
      (by positivity : 0 ≤ Real.sqrt Λ' * ζv)
    have h2 : (Real.sqrt Λ' * ζv) ^ 4 = Λ' ^ 2 * ζv ^ 4 := by
      rw [mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hΛ0]
    rw [h2] at h1
    exact (pow_le_pow_left₀ (le_max_of_le_left (by positivity)) hod 4).trans h1
  have key : 4 * (γ * Wr * ℓv) * Λ' * max (ω * (ω * R * ζu)) (Real.sqrt Λ' * ζv) ^ 4 * Cc ≤
      X ^ 2 / (2 * ω) * eu⁻¹ * ζv ^ 2 := by
    rw [hΓ']
    have hu4 : ζu ^ 4 ≤ ζv ^ 3 * ζt := by
      calc ζu ^ 4 = ζu ^ 3 * ζu := by ring
        _ ≤ ζv ^ 3 * ζt := by gcongr
    calc 4 * (ζv⁻¹ * ev⁻¹) * Λ' * max (ω * (ω * R * ζu)) (Real.sqrt Λ' * ζv) ^ 4 * Cc
        ≤ 4 * (ζv⁻¹ * (R * eu⁻¹)) * Λ' * (8 * ((ω * (ω * R * ζu)) ^ 4 + Λ' ^ 2 * ζv ^ 4)) * ω := by
          gcongr
      _ = 32 * ω ^ 9 * R ^ 5 * Λ' * (ζu ^ 4 * ζv⁻¹) * eu⁻¹ +
            32 * ω * R * Λ' ^ 3 * (ζv ^ 4 * ζv⁻¹) * eu⁻¹ := by ring
      _ ≤ 32 * ω ^ 9 * R ^ 5 * (ω ^ 2 * X) * (ζv ^ 3 * ζt * ζv⁻¹) * eu⁻¹ +
            32 * ω * R * (ω ^ 2 * X) ^ 3 * (ζv ^ 4 * ζv⁻¹) * eu⁻¹ := by gcongr
      _ = (32 * ω ^ 11 * (R ^ 5 * ζt) * X + 32 * ω ^ 7 * R * (X ^ 2 * X) * ζv) * ζv ^ 2 * eu⁻¹ := by
          field_simp
      _ ≤ (32 * ω ^ 11 * (R ^ 5 * ζt) * X ^ 2 + 32 * ω ^ 7 * R * (X ^ 2 * (ω ^ 100 * P)) * ζt) *
            ζv ^ 2 * eu⁻¹ := by
          have hXX : X ≤ X ^ 2 := by nlinarith
          gcongr
      _ = ((32 * ω ^ 11 * (R ^ 5 * ζt) + 32 * ω ^ 107 * (R * P * ζt)) * (2 * ω)) *
            (X ^ 2 / (2 * ω) * eu⁻¹ * ζv ^ 2) := by
          field_simp
      _ ≤ 1 * (X ^ 2 / (2 * ω) * eu⁻¹ * ζv ^ 2) := by
          gcongr
          have h1 : 128 * ω ^ 12 * (R ^ 5 * ζt) ≤ 1 :=
            lemmaN_small (by positivity) hR5 (lemmaN_cpow hω (k := 7) (by norm_num) (by norm_num))
          have hRP' : R * P * ζt ≤ R ^ 3 * P * ζt := by
            have : R ≤ R ^ 3 := le_self_pow₀ hR (by norm_num)
            gcongr
          have h2 : 128 * ω ^ 108 * (R ^ 3 * P * ζt) ≤ 1 :=
            lemmaN_small (by positivity) hRP (lemmaN_cpow hω (k := 7) (by norm_num) (by norm_num))
          have h3 : 128 * ω ^ 108 * (R * P * ζt) ≤ 1 :=
            le_trans (by gcongr) h2
          have e : (32 * ω ^ 11 * (R ^ 5 * ζt) + 32 * ω ^ 107 * (R * P * ζt)) * (2 * ω) =
              (128 * ω ^ 12 * (R ^ 5 * ζt) + 128 * ω ^ 108 * (R * P * ζt)) / 2 := by ring
          rw [e]
          linarith
      _ = X ^ 2 / (2 * ω) * eu⁻¹ * ζv ^ 2 := one_mul _
  calc _ = (4 * (γ * Wr * ℓv) * Λ' * max (ω * (ω * R * ζu)) (Real.sqrt Λ' * ζv) ^ 4 * Cc) *
        (ζv ^ 2 * wab ^ 2) := by ring
    _ ≤ X ^ 2 / (2 * ω) * eu⁻¹ * ζv ^ 2 * (ζv ^ 2 * wab ^ 2) := by gcongr
    _ = X ^ 2 / (2 * ω) * eu⁻¹ * (ζv ^ 2 * wab) ^ 2 := by ring

/-- Near bracket row (capped weight). -/
private theorem lemmaN_num_nbracket (hω : 2 ≤ ω) (hR : 1 ≤ R) (hX : 1 ≤ X) (hζu : 0 < ζu)
    (hζuv : ζu ≤ ζv) (heu : 0 < eu) (hev : 0 < ev) (hZ : ζu ^ 2 * eu ≤ ζv ^ 2 * ev)
    (hX1 : R ^ 4 * ω ^ 25 ≤ X) {γ Wr ℓv Cc Λ' K₀ wab : ℝ} (hΓ : γ * Wr * ℓv * ζv * ev = 1)
    (hCc : 0 ≤ Cc) (hCcω : Cc ≤ ω) (hΛ0 : 0 ≤ Λ') (hΛ : Λ' ≤ ω ^ 2 * X) (hK0 : 0 ≤ K₀)
    (hK : K₀ ≤ ω ^ 2 + Λ' * ζv ^ 2 / (ω * R * ζu) ^ 2) (hw : ω⁻¹ ≤ wab) :
    4 * γ * Wr * (ω * R * ζu) * (ω * R * ζu) ^ 4 * (Real.sqrt 2 * K₀ * Cc) * ℓv * 2 ≤
      X ^ 2 / (2 * ω) * eu⁻¹ * (ζv ^ 2 * wab) ^ 2 := by
  have hω0 : 0 < ω := by linarith
  have hζv : 0 < ζv := lt_of_lt_of_le hζu hζuv
  have hR0 : 0 < R := by linarith
  have hΓ' : γ * Wr * ℓv = ζv⁻¹ * ev⁻¹ := by field_simp; linarith
  have hzi := lemmaN_zeta_inv heu hev hZ
  have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hX2 : R ^ 8 * ω ^ 50 ≤ X ^ 2 := by
    calc R ^ 8 * ω ^ 50 = (R ^ 4 * ω ^ 25) ^ 2 := by ring
      _ ≤ X ^ 2 := by gcongr
  have hR58 : R ^ 5 ≤ R ^ 8 := pow_le_pow_right₀ hR (by norm_num)
  have hR34 : R ^ 3 ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  -- the coefficient in units of `ζv⁴ eu⁻¹`
  have key : 4 * (γ * Wr * ℓv) * (ω * R * ζu) * (ω * R * ζu) ^ 4 * (Real.sqrt 2 * K₀ * Cc) * 2 ≤
      (16 * ω ^ 8 * R ^ 5 + 16 * ω ^ 6 * R ^ 3 * X) * ζv ^ 4 * eu⁻¹ := by
    rw [hΓ']
    have hK' : K₀ * (ω * R * ζu) ^ 2 ≤ ω ^ 2 * (ω * R * ζu) ^ 2 + Λ' * ζv ^ 2 := by
      have hp : 0 < (ω * R * ζu) ^ 2 := by positivity
      calc K₀ * (ω * R * ζu) ^ 2 ≤ (ω ^ 2 + Λ' * ζv ^ 2 / (ω * R * ζu) ^ 2) * (ω * R * ζu) ^ 2 :=
            mul_le_mul_of_nonneg_right hK hp.le
        _ = _ := by field_simp
    have hK'' : K₀ * (ω * R * ζu) ^ 2 ≤ ω ^ 2 * (ω * R * ζv) ^ 2 + (ω ^ 2 * X) * ζv ^ 2 := by
      have h1 : ω ^ 2 * (ω * R * ζu) ^ 2 ≤ ω ^ 2 * (ω * R * ζv) ^ 2 := by gcongr
      have h2 : Λ' * ζv ^ 2 ≤ (ω ^ 2 * X) * ζv ^ 2 := by gcongr
      linarith
    calc 4 * (ζv⁻¹ * ev⁻¹) * (ω * R * ζu) * (ω * R * ζu) ^ 4 * (Real.sqrt 2 * K₀ * Cc) * 2
        = 8 * Real.sqrt 2 * Cc * ω ^ 3 * R ^ 3 * ζu * (ζu ^ 2 * ev⁻¹) * ζv⁻¹ *
            (K₀ * (ω * R * ζu) ^ 2) := by ring
      _ ≤ 8 * 2 * ω * ω ^ 3 * R ^ 3 * ζv * (ζv ^ 2 * eu⁻¹) * ζv⁻¹ *
            (ω ^ 2 * (ω * R * ζv) ^ 2 + (ω ^ 2 * X) * ζv ^ 2) := by
          gcongr
      _ = (16 * ω ^ 8 * R ^ 5 + 16 * ω ^ 6 * R ^ 3 * X) * ζv ^ 4 * eu⁻¹ := by
          field_simp; ring
  have hfin : (16 * ω ^ 8 * R ^ 5 + 16 * ω ^ 6 * R ^ 3 * X) * (2 * ω * ω ^ 2) ≤ X ^ 2 := by
    have h1 : 32 * ω ^ 11 * R ^ 5 ≤ X ^ 2 / 2 := by
      have : 64 * ω ^ 11 ≤ ω ^ 50 := lemmaN_cpow hω (k := 6) (by norm_num) (by norm_num)
      have : 64 * ω ^ 11 * R ^ 5 ≤ ω ^ 50 * R ^ 8 := by gcongr
      nlinarith
    have h2 : 32 * ω ^ 9 * R ^ 3 * X ≤ X ^ 2 / 2 := by
      have : 64 * ω ^ 9 ≤ ω ^ 25 := lemmaN_cpow hω (k := 6) (by norm_num) (by norm_num)
      have : 64 * ω ^ 9 * R ^ 3 ≤ X := by
        calc 64 * ω ^ 9 * R ^ 3 ≤ ω ^ 25 * R ^ 4 := by gcongr
          _ = R ^ 4 * ω ^ 25 := by ring
          _ ≤ X := hX1
      have hX0 : 0 ≤ X := by linarith
      nlinarith
    nlinarith
  calc _ = 4 * (γ * Wr * ℓv) * (ω * R * ζu) * (ω * R * ζu) ^ 4 * (Real.sqrt 2 * K₀ * Cc) * 2 := by
        ring
    _ ≤ (16 * ω ^ 8 * R ^ 5 + 16 * ω ^ 6 * R ^ 3 * X) * ζv ^ 4 * eu⁻¹ := key
    _ ≤ X ^ 2 / (2 * ω * ω ^ 2) * ζv ^ 4 * eu⁻¹ := by
        gcongr
        rw [le_div_iff₀ (by positivity)]; exact hfin
    _ = X ^ 2 / (2 * ω) * eu⁻¹ * (ζv ^ 2 * ω⁻¹) ^ 2 := by field_simp
    _ ≤ X ^ 2 / (2 * ω) * eu⁻¹ * (ζv ^ 2 * wab) ^ 2 := by
        have : 0 ≤ ζv ^ 2 * ω⁻¹ := by positivity
        gcongr

end NumRows


section GoodRates

open scoped Matrix.Norms.L2Operator

set_option maxHeartbeats 800000 in
/-- The generator and bracket of the mixed-pair error at a good point, normalized by the envelope
`env = ζ_v² w(a,b)`: `‖𝒢D₂(a,b)‖ ≤ (2κ_K Λ + X/(2ω)(1-u)⁻¹) env` and
`Re Γ(ℒ₂(a,b)) ≤ X²/(2ω) (1-u)⁻¹ env²`. -/
private theorem lemmaN_good_rates (g E : ℝ) (m : ℂ) {W L : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (w : Fin L → Fin L → ℝ) (hw0 : ∀ x y, 0 ≤ w x y) (hw2 : ∀ x y, w x y ≤ 2)
    (hws : ∀ x y, w x y = w y x) {wmin : ℝ} (hwmin0 : 0 < wmin) (hwmin : ∀ x y, wmin ≤ w x y)
    {ω R P X ζu ζv ζt ev Λ Cc ℓv κK h H εw C' lH : ℝ}
    (hω : 2 ≤ ω) (hR : 1 ≤ R) (hP : 0 ≤ P) (hX : 1 ≤ X) (hζu : 0 < ζu) (hζuv : ζu ≤ ζv)
    (hζt : ζv ≤ ζt) (hev : 0 < ev) (h4 : 1 - u ≤ R * ev)
    (hZ : ζu ^ 2 * (1 - u) ≤ ζv ^ 2 * ev)
    (hRP : R ^ 3 * P * ζt * ω ^ 400 ≤ 1) (hR5 : R ^ 5 * ζt * ω ^ 400 ≤ 1)
    (hX1 : R ^ 4 * ω ^ 25 ≤ X) (hXP : X ≤ ω ^ 100 * P)
    (hΓ : gammaG g * W * ℓv * ζv * ev = 1) (hℓv : 1 ≤ ℓv)
    (hΛ0 : 0 ≤ Λ) (hΛωX : Λ ≤ ω * X) (hCc : 0 ≤ Cc) (hCcω : Cc ≤ ω) (hC' : 0 ≤ C') (hΛ1 : 1 ≤ C' + Λ)
    (hΛω : C' + Λ ≤ ω ^ 2 * X) (hh : 0 ≤ h) (hhH : h ≤ H) (hH : H = ℓv * lH) (hlH0 : 0 ≤ lH)
    (hlH : lH ≤ ω)
    (hLr : (L : ℝ) * Real.sqrt (max (ω ^ 2) ((C' + Λ) * ζv ^ 2 / (ω * R * ζu) ^ 2) * εw) ≤ ℓv)
    (hεw : 0 ≤ εw)
    (hD : ∀ x y, ‖resLoop g E m ![x, y] ![true, false] u M -
      primLoop g W L E m u ![x, y] ![true, false]‖ ≤ Λ * ζv ^ 2 * w x y)
    (hconv : ∀ x y, ∑ c, w x c * w c y ≤ Cc * ℓv * w x y ∧
      ∑ c, Real.sqrt (w x c * w c y) ≤ Cc * ℓv * Real.sqrt (w x y))
    (hker : ∀ x y, ∑ c, mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) u x c *
      w c y ≤ κK * w x y)
    (hop : ∀ x y, ‖blockOf (resolventMat M (zChar g E m u)) x y‖ ≤ W * (ω * R * ζu))
    (hhs : ∀ x y, blockHS2 (resolventMat M (zChar g E m u)) x y ≤ (W : ℝ) ^ 2 * (ω * R * ζu))
    (havg : ∀ c, ‖blockTr (resolventMat M (zChar g E m u) -
      dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c‖ ≤
        ω * R ^ 2 * ζu)
    (hprim : ∀ x y, h < cycDist x y →
      ‖primLoop g W L E m u ![x, y] ![true, false]‖ ≤ C' * ζv ^ 2 * w x y)
    (hshort : ∀ x y, (cycDist x y : ℝ) ≤ 2 * h → ω⁻¹ ≤ w x y)
    (hfar : ∀ x y, H < cycDist x y → w x y ≤ εw) (a b : Fin L) :
    ‖blockGen W L (gammaG g) (fun r N => resLoop g E m ![a, b] ![true, false] r N -
        primLoop g W L E m r ![a, b] ![true, false]) u M‖ ≤
      (2 * κK * Λ + X / (2 * ω) * (1 - u)⁻¹) * (ζv ^ 2 * w a b) ∧
    (blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, false] u)
        (resLoop g E m ![a, b] ![true, false] u) M).re ≤
      X ^ 2 / (2 * ω) * (1 - u)⁻¹ * (ζv ^ 2 * w a b) ^ 2 := by
  have hω0 : 0 < ω := by linarith
  have hω1 : 1 ≤ ω := by linarith
  have heu : 0 < 1 - u := by linarith
  have hζv : 0 < ζv := lt_of_lt_of_le hζu hζuv
  have hζt0 : 0 < ζt := lt_of_lt_of_le hζv hζt
  have ho₁ : 0 < ω * R * ζu := by positivity
  set K₀ := max (ω ^ 2) ((C' + Λ) * ζv ^ 2 / (ω * R * ζu) ^ 2) with hK₀
  have hK₀ω : ω ≤ K₀ := le_max_of_le_left (by nlinarith)
  have hK₀b : (C' + Λ) * ζv ^ 2 ≤ (ω * R * ζu) ^ 2 * K₀ := by
    have : (C' + Λ) * ζv ^ 2 / (ω * R * ζu) ^ 2 ≤ K₀ := le_max_right _ _
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hCℓ : 0 ≤ Cc * ℓv := mul_nonneg hCc (by linarith)
  obtain ⟨hg1, hg2, hg3, hg4, hg5⟩ := lemmaN_point_rows g E m hW hL hm hu0 hu1 hM w hw0 hw2 hws
    hwmin0 hwmin (Λ := Λ) (ζ := ζv) (Cc := Cc) (ℓ := ℓv) (κK := κK) (o₁ := ω * R * ζu)
    (s₀ := ω * R * ζu) (τ := ω * R ^ 2 * ζu) (ω := ω) (h := h) (H := H) (εw := εw) (C' := C')
    (K₀ := K₀) hΛ0 hζv.le hCℓ ho₁ ho₁.le (by positivity) hω1 hh hhH hC' hK₀ω hK₀b hD hconv hker
    hop hhs havg hprim hshort hfar a b
  have hwab := hw0 a b
  have hΓ' : gammaG g * W * ℓv * ζv * ev = 1 := hΓ
  -- the light term, `‖𝒲₂‖ ≤ X/(4ω)(1-u)⁻¹ env`
  have hlight : ‖lightW g E m ![a, b] ![true, false] u M‖ ≤
      X / (4 * ω) * (1 - u)⁻¹ * (ζv ^ 2 * w a b) := by
    rcases lt_or_ge (2 * h) (cycDist a b : ℝ) with hd | hd
    · refine (hg2 hd).trans ?_
      exact lemmaN_num_dlight hω hR hP hX hζu hζuv hζt heu hev h4 hRP hR5 hXP hΓ' hCc hCcω hΛ1
        hΛω hwab
    · refine hg3.trans ?_
      have hwl := hshort a b hd
      have hΛt : max ((C' + Λ) * ζv ^ 2 / K₀) ((ω * R * ζu) / 2) ≤ ω * R * ζu := by
        have hs1 : ω * R * ζu ≤ 1 := by
          have h1 : ω * R * ζu ≤ ω * (R ^ 5 * ζt) := by
            have : R ≤ R ^ 5 := le_self_pow₀ hR (by norm_num)
            have : R * ζu ≤ R ^ 5 * ζt := mul_le_mul this (hζuv.trans hζt) hζu.le (by positivity)
            nlinarith
          have h2 : ω * (R ^ 5 * ζt) ≤ 1 := by
            have := lemmaN_small (c := 1) (m := 1) (n := 400) (by positivity) hR5
              (lemmaN_cpow hω (k := 0) (by norm_num) (by norm_num))
            linarith [show 1 * ω ^ 1 * (R ^ 5 * ζt) = ω * (R ^ 5 * ζt) by ring]
          linarith
        refine max_le ?_ (by linarith)
        have hK0 : 0 < K₀ := by linarith
        rw [div_le_iff₀ hK0]
        calc (C' + Λ) * ζv ^ 2 ≤ (ω * R * ζu) ^ 2 * K₀ := hK₀b
          _ = (ω * R * ζu) * (ω * R * ζu) * K₀ := by ring
          _ ≤ (ω * R * ζu) * 1 * K₀ := by gcongr
          _ = ω * R * ζu * K₀ := by ring
      have hΛt0 : 0 ≤ max ((C' + Λ) * ζv ^ 2 / K₀) ((ω * R * ζu) / 2) :=
        le_max_of_le_right (by positivity)
      have := lemmaN_num_nlight hω hR hζu hζuv heu hev hZ hX1 hΓ' hℓv hΛt0 hΛt
        (mul_nonneg (by positivity : (0 : ℝ) ≤ K₀) hεw) hLr hlH0 hlH hwl
      rw [hH]
      calc _ = 2 * Real.sqrt 2 * gammaG g * W * (ω * R ^ 2 * ζu) * (ω * R * ζu) *
          ((4 * (ℓv * lH) + 2) * (ω * R * ζu) + L * Real.sqrt ((ω * R * ζu) *
            max ((C' + Λ) * ζv ^ 2 / K₀) ((ω * R * ζu) / 2) * 1 ^ 2 * (K₀ * εw))) := by
            rfl
        _ ≤ _ := this
  have hquad : gammaG g * W * ((Λ * ζv ^ 2) ^ 2 * Cc * ℓv * w a b) ≤
      X / (4 * ω) * (1 - u)⁻¹ * (ζv ^ 2 * w a b) := by
    have hq := lemmaN_num_quad hω hR hP hX hζv hζt heu hev (Γ := gammaG g * W * ℓv)
      hΓ' h4 hRP hXP hCc hCcω hΛ0 hΛωX
    calc gammaG g * W * ((Λ * ζv ^ 2) ^ 2 * Cc * ℓv * w a b) =
        (gammaG g * W * ℓv * (Λ ^ 2 * Cc) * ζv ^ 2) * (ζv ^ 2 * w a b) := by ring
      _ ≤ X / (4 * ω) * (1 - u)⁻¹ * (ζv ^ 2 * w a b) := by gcongr
  refine ⟨?_, ?_⟩
  · refine hg1.trans ?_
    have e : (2 * κK * Λ + X / (2 * ω) * (1 - u)⁻¹) * (ζv ^ 2 * w a b) =
        X / (4 * ω) * (1 - u)⁻¹ * (ζv ^ 2 * w a b) + 2 * κK * (Λ * ζv ^ 2) * w a b +
          X / (4 * ω) * (1 - u)⁻¹ * (ζv ^ 2 * w a b) := by
      field_simp; ring
    rw [e]
    linarith
  · rcases lt_or_ge (2 * h) (cycDist a b : ℝ) with hd | hd
    · refine (hg4 hd).trans ?_
      exact lemmaN_num_dbracket hω hR hP hX hζu hζuv hζt heu hev h4 hRP hR5 hXP hΓ' hCc hCcω
        hΛ1 hΛω hwab
    · refine hg5.trans ?_
      have hwl := hshort a b hd
      have hK : K₀ ≤ ω ^ 2 + (C' + Λ) * ζv ^ 2 / (ω * R * ζu) ^ 2 := by
        have h1 : 0 ≤ (C' + Λ) * ζv ^ 2 / (ω * R * ζu) ^ 2 := by
          have : 0 ≤ C' + Λ := by linarith
          positivity
        exact max_le (by linarith) (by nlinarith [sq_nonneg ω])
      exact lemmaN_num_nbracket hω hR hX hζu hζuv heu hev hZ hX1 hΓ' hCc hCcω (by linarith) hΛω
        (by positivity) hK hwl

end GoodRates


section Bridge

/-- The block slice of `A_g ⊗ I` is Hermitian. -/
private theorem lemmaN_slice_herm (g : ℝ) {W L : ℕ} (hW : 1 ≤ W) (y : Ω W L) :
    (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y).IsHermitian := by
  have hA : (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
    have h := flowH_isHermitian g W L 0 0
    simpa [flowH, blockFlow] using h
  have e := blockFlow_eq_blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
    (s := W) (Nat.cast_nonneg W) y
  have hW0 : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_self hW0, Real.sqrt_one, one_smul] at e
  rw [← e]
  exact blockFlow_isHermitian W L hA _ y

/-- The coordinate generator of the mixed-pair field is the block generator at the slice. -/
private theorem lemmaN_coordGen_eq (g E : ℝ) (m : ℂ) (W L : ℕ) (ab : Fin L × Fin L) (u : ℝ)
    (y : Ω W L) :
    coordGen (gammaG g / W) (fun r x => pairErrField g E m W L r x ab) u y =
      blockGen W L (gammaG g) (fun r N => resLoop g E m ![ab.1, ab.2] ![true, false] r N -
        primLoop g W L E m r ![ab.1, ab.2] ![true, false]) u
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) := by
  rw [blockGen_slice]
  rfl

/-- The carré du champ of the mixed-pair field is the bracket of the loop at the slice. -/
private theorem lemmaN_coordGamma_eq (g E : ℝ) (m : ℂ) (W L : ℕ) (ab : Fin L × Fin L) (u : ℝ)
    (y : Ω W L) :
    coordGamma (gammaG g / W) (fun x => pairErrField g E m W L u x ab)
        (fun x => pairErrField g E m W L u x ab) y =
      blockGamma W L (gammaG g) (resLoop g E m ![ab.1, ab.2] ![true, false] u)
        (resLoop g E m ![ab.1, ab.2] ![true, false] u)
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) := by
  rw [← blockGamma_pairErr, blockGamma_slice]
  rfl

end Bridge

section SurrRates

/-- Rates of the surrogate of the mixed-pair errors from the normalized rates of its components:
`|Re 𝒢X| ≤ κ X/(1-u)` and `Re Γ(X) ≤ b X²/(1-u)` when `|S|^{1/(2q)} ≤ 1.001`,
`‖𝒢Y_s‖/env_s ≤ κ_l X/(1-u)`, `Re Γ(Y_s)/env_s² ≤ b_h X²/(1-u)`,
`1.001 κ_l + 1.003 q b_h ≤ κ` and `1.003 b_h ≤ b`. -/
private theorem lemmaN_surr_rates {ι S : Type*} [Fintype ι] [Fintype S] (σ2 : ℝ) (hσ2 : 0 ≤ σ2)
    {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ} (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ)
    (Y : S → ℝ → (ι → ℝ) → ℂ) {a b u : ℝ} (hY : ∀ s, HeatClass (Y s) a b)
    (hu : u ∈ Set.Ioo a b) (hu1 : u < 1) (y : ι → ℝ)
    (hS : (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) ≤ 1.001) {κl bh κ bΓ : ℝ}
    (hκl : 0 ≤ κl) (hbh : 0 ≤ bh)
    (hgen : ∀ s, ‖coordGen σ2 (Y s) u y‖ / env s ≤
      κl * lqSurr q env δ (fun s => Y s u y) / (1 - u))
    (hgam : ∀ s, (coordGamma σ2 (Y s u) (Y s u) y).re / env s ^ 2 ≤
      bh * lqSurr q env δ (fun s => Y s u y) ^ 2 / (1 - u))
    (hκ : 1.001 * κl + 1.003 * q * bh ≤ κ) (hb : 1.003 * bh ≤ bΓ) :
    |(coordGen σ2 (fun r z => ((lqSurr q env δ (fun s => Y s r z) : ℝ) : ℂ)) u y).re| ≤
        κ * lqSurr q env δ (fun s => Y s u y) / (1 - u) ∧
      (coordGamma σ2 (fun z => ((lqSurr q env δ (fun s => Y s u z) : ℝ) : ℂ))
          (fun z => ((lqSurr q env δ (fun s => Y s u z) : ℝ) : ℂ)) y).re ≤
        bΓ * lqSurr q env δ (fun s => Y s u y) ^ 2 / (1 - u) := by
  set X := lqSurr q env δ (fun s => Y s u y) with hXdef
  have heu : 0 < 1 - u := by linarith
  have hX0 : 0 ≤ X := by
    simp only [hXdef, lqSurr]; positivity
  have hsl := fun s => lemmaN_heat_slice (hY s) hu
  obtain ⟨h1, h2⟩ := coordGen_lqSurr_le σ2 hσ2 hq henv hδ Y u y (fun s => (hsl s).2.2 y)
    (fun s => (hsl s).2.1) hgen hgam
  rw [← hXdef] at h1
  have hc0 : 0 ≤ (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) := by positivity
  have hS2 : (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) ≤ 1.003 := by
    have e : (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) =
        ((Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q))) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1
      have : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
      norm_num
    rw [e]
    calc ((Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q))) ^ 2 ≤ 1.001 ^ 2 := by gcongr
      _ ≤ 1.003 := by norm_num
  have hc1 : 0 ≤ (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) := by positivity
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  refine ⟨?_, ?_⟩
  · refine h1.trans ?_
    rcases eq_or_lt_of_le hX0 with hX | hX
    · rw [← hX]; simp
    · have e1 : (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) * (κl * X / (1 - u)) +
          q * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * (bh * X ^ 2 / (1 - u)) / X =
          ((Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) * κl +
            q * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * bh) * X / (1 - u) := by
        field_simp
      rw [e1]
      have hcoef : (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) * κl +
          q * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * bh ≤ κ := by
        have a1 : (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) * κl ≤ 1.001 * κl :=
          mul_le_mul_of_nonneg_right hS hκl
        have a2 : q * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * bh ≤ 1.003 * q * bh := by
          have := mul_le_mul_of_nonneg_left hS2 hq0
          have := mul_le_mul_of_nonneg_right this hbh
          linarith
        linarith
      gcongr
  · refine h2.trans ?_
    calc (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * (bh * X ^ 2 / (1 - u)) ≤
        1.003 * (bh * X ^ 2 / (1 - u)) := by gcongr
      _ ≤ bΓ * X ^ 2 / (1 - u) := by
        rw [← mul_div_assoc, ← mul_assoc]
        gcongr

end SurrRates


section Core

variable {ε : ℝ} {ρ : ℝ → ℝ}

/-- `ψ(x) ≤ (x/J)^{2r}` and `ψ(x) ≤ (1+2β)^{2r}` for `x ≥ 0`. -/
private theorem lemmaN_psi_le (hρ : IsRamp ε ρ) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) (r : ℕ) {x : ℝ}
    (hx : 0 ≤ x) :
    cutPsi ρ J β r x ≤ (x / J) ^ (2 * r) ∧ cutPsi ρ J β r x ≤ (1 + 2 * β) ^ (2 * r) := by
  have hm : 0 < β * J := mul_pos hβ hJ
  have h1 := lemmaN_ramp_mem hρ ((x - J * (1 + β)) / (β * J))
  have h2 := lemmaN_ramp_mem hρ (x + 1)
  have hP : 0 ≤ (x / J) ^ (2 * r) := by positivity
  have hle : cutPsi ρ J β r x ≤ (x / J) ^ (2 * r) := by
    unfold cutPsi
    have : (1 - ρ ((x - J * (1 + β)) / (β * J))) * ρ (x + 1) ≤ 1 := by
      have : 0 ≤ 1 - ρ ((x - J * (1 + β)) / (β * J)) := by linarith
      nlinarith
    calc (x / J) ^ (2 * r) * (1 - ρ ((x - J * (1 + β)) / (β * J))) * ρ (x + 1) =
        (x / J) ^ (2 * r) * ((1 - ρ ((x - J * (1 + β)) / (β * J))) * ρ (x + 1)) := by ring
      _ ≤ (x / J) ^ (2 * r) * 1 := mul_le_mul_of_nonneg_left this hP
      _ = _ := mul_one _
  refine ⟨hle, ?_⟩
  rcases le_or_gt x (J * (1 + 2 * β)) with hx2 | hx2
  · refine hle.trans ?_
    have : x / J ≤ 1 + 2 * β := by rw [div_le_iff₀ hJ]; linarith
    exact pow_le_pow_left₀ (by positivity) this _
  · have : ρ ((x - J * (1 + β)) / (β * J)) = 1 := hρ.one _ ((le_div_iff₀ hm).2 (by nlinarith))
    have h0 : cutPsi ρ J β r x = 0 := by simp [cutPsi, this]
    rw [h0]; positivity

/-- `Φ(x) = 0` for `x ≤ J`. -/
private theorem lemmaN_phi_zero (hρ : IsRamp ε ρ) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {x : ℝ}
    (hx : x ≤ J) : cutPhi ρ J β x = 0 := by
  unfold cutPhi
  exact hρ.zero _ (div_nonpos_of_nonpos_of_nonneg (by linarith) (mul_pos hβ hJ).le)

/-- An integral bound from a pointwise bound off a measurable set of small measure. -/
private theorem lemmaN_integral_split {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    {C c δ : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfC : ∀ x, f x ≤ C) {T : Set (ι → ℝ)}
    (hT : MeasurableSet T) (hTδ : stdGauss ι T ≤ ENNReal.ofReal δ) (hδ : 0 ≤ δ)
    (hc : ∀ x, x ∉ T → f x ≤ c) (hc0 : 0 ≤ c) :
    ∫ x, f x ∂(stdGauss ι) ≤ c + C * δ := by
  have hC0 : 0 ≤ C := (hf0 0).trans (hfC 0)
  have hint : Integrable f (stdGauss ι) :=
    Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]; exact hfC x)
  have hind : Integrable (T.indicator fun _ => C) (stdGauss ι) :=
    (integrable_const C).indicator hT
  have hpt : ∀ x, f x ≤ c + T.indicator (fun _ => C) x := by
    intro x
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx]; linarith [hfC x]
    · rw [Set.indicator_of_notMem hx]; linarith [hc x hx]
  calc ∫ x, f x ∂(stdGauss ι) ≤ ∫ x, (c + T.indicator (fun _ => C) x) ∂(stdGauss ι) :=
        integral_mono hint ((integrable_const c).add hind) hpt
    _ = c + C * (stdGauss ι).real T := by
        rw [integral_add (integrable_const c) hind, integral_const, integral_indicator_const _ hT]
        simp [smul_eq_mul, mul_comm]
    _ ≤ c + C * δ := by
        have : (stdGauss ι).real T ≤ δ := by
          rw [measureReal_def]
          exact ENNReal.toReal_le_of_le_ofReal hδ hTδ
        gcongr

/-- The no-exit lemma with multiplicative rates applied with bad sets of small probability, the
`L²` off-set bound, and an initial value below `2δ_s ≤ J` off a set of small probability. -/
private theorem lemmaN_core {ι : Type*} [Fintype ι] (σ2 : ℝ) (hσ2 : 0 < σ2) (X : ℝ → (ι → ℝ) → ℝ)
    {a b s v : ℝ} (ha : a < 0) (hs : 0 < s) (hsv : s < v) (hvb : v < b) (hv1 : v < 1)
    (hX : HeatClass (fun r y => ((X r y : ℝ) : ℂ)) a b) (hX0 : ∀ r y, 0 ≤ X r y)
    (hρ : IsRamp ε ρ) {J β κ bΓ K δb δs : ℝ} (r : ℕ) (hr : 1 ≤ r) (hJ : 0 < J) (hβ : 0 < β)
    (hκ : 0 < κ) (hbΓ : 0 ≤ bΓ) (hK : 0 ≤ K) (hδb : 0 ≤ δb) (hδs : 0 ≤ δs) (hδsJ : 2 * δs ≤ J)
    (Bad : ℝ → Set (ι → ℝ))
    (hbad : ∀ u ∈ Set.Ioo s v,
      stdGauss ι {x | Real.sqrt (u * σ2) • x ∈ Bad u} ≤ ENNReal.ofReal δb)
    (hrate : ∀ u ∈ Set.Ioo s v, ∀ y, y ∉ Bad u → X u y ≤ J * (1 + 2 * β) →
      |(coordGen σ2 (fun t z => ((X t z : ℝ) : ℂ)) u y).re| ≤ κ * X u y / (1 - u) ∧
        (coordGamma σ2 (fun z => ((X u z : ℝ) : ℂ)) (fun z => ((X u z : ℝ) : ℂ)) y).re ≤
          bΓ * X u y ^ 2 / (1 - u))
    (hL2 : ∀ u ∈ Set.Ioo s v, ∀ φ : ℝ → ℝ, (φ = cutPsi ρ J β r ∨ φ = cutPhi ρ J β) →
      MemLp (fun x => (coordGen σ2 (fun t z => ((φ (X t z) : ℝ) : ℂ)) u
        (Real.sqrt (u * σ2) • x)).re) 2 (stdGauss ι) ∧
      ∫ x, ((coordGen σ2 (fun t z => ((φ (X t z) : ℝ) : ℂ)) u
        (Real.sqrt (u * σ2) • x)).re) ^ 2 ∂(stdGauss ι) ≤ K ^ 2)
    (hinit : stdGauss ι {x | 2 * δs < X s (Real.sqrt (s * σ2) • x)} ≤ ENNReal.ofReal δb) :
    stdGauss ι {x | J * (1 + β) ≤ X v (Real.sqrt (v * σ2) • x)} ≤
      ENNReal.ofReal ((perronMul ε β κ bΓ r / rateMulA12 ε β κ bΓ r) *
        (((1 - s) / (1 - v)) ^ perronMul ε β κ bΓ r *
          ((2 * δs / J) ^ (2 * r) + ((1 + 2 * β) ^ (2 * r) +
            rateMulA12 ε β κ bΓ r / perronMul ε β κ bΓ r) * δb +
            (1 + rateMulA12 ε β κ bΓ r / perronMul ε β κ bΓ r) * (K * Real.sqrt δb)))) := by
  obtain ⟨hε0, hε1⟩ := hρ.eps
  set sc : ℝ → ℝ := fun u => Real.sqrt (u * σ2) with hsc
  -- measurable good sets
  set T : ℝ → Set (ι → ℝ) := fun u => toMeasurable (stdGauss ι) {x | sc u • x ∈ Bad u} with hT
  set G : ℝ → Set (ι → ℝ) := fun u => {y | (sc u)⁻¹ • y ∉ T u} with hG
  have hGm : ∀ u, MeasurableSet (G u) := fun u =>
    ((measurableSet_toMeasurable _ _).compl).preimage (measurable_const_smul _)
  have hsc0 : ∀ u ∈ Set.Ioo s v, sc u ≠ 0 := fun u hu => by
    simp only [hsc]
    exact (Real.sqrt_pos.2 (mul_pos (hs.trans hu.1) hσ2)).ne'
  have hGT : ∀ u ∈ Set.Ioo s v, {x | sc u • x ∉ G u} = T u := by
    intro u hu
    ext x
    simp only [hG, Set.mem_setOf_eq, not_not, smul_smul, inv_mul_cancel₀ (hsc0 u hu), one_smul]
  have hGbad : ∀ u ∈ Set.Ioo s v, ∀ y ∈ G u, y ∉ Bad u := by
    intro u hu y hy hb
    apply hy
    apply subset_toMeasurable
    simp only [Set.mem_setOf_eq, smul_smul, mul_inv_cancel₀ (hsc0 u hu), one_smul]
    exact hb
  -- the cutoffs
  have hψb := fun x (hx : 0 ≤ x) => lemmaN_psi_le hρ hJ hβ r hx
  have hprops := cutPhi_props hρ hJ hβ r
  -- off-set bound
  have hoff : ∀ u ∈ Set.Ioo s v,
      ∫ x, Set.indicator {x | Real.sqrt (u * σ2) • x ∉ G u}
          (fun x => |(coordGen σ2 (fun t z => ((cutPsi ρ J β r (X t z) : ℝ) : ℂ)) u
            (Real.sqrt (u * σ2) • x)).re|) x ∂(stdGauss ι) ≤ K * Real.sqrt δb ∧
        ∫ x, Set.indicator {x | Real.sqrt (u * σ2) • x ∉ G u}
          (fun x => |(coordGen σ2 (fun t z => ((cutPhi ρ J β (X t z) : ℝ) : ℂ)) u
            (Real.sqrt (u * σ2) • x)).re|) x ∂(stdGauss ι) ≤ K * Real.sqrt δb := by
    intro u hu
    have hTm : MeasurableSet (T u) := measurableSet_toMeasurable _ _
    have hTδ : (stdGauss ι).real (T u) ≤ δb := by
      rw [measureReal_def]
      refine ENNReal.toReal_le_of_le_ofReal hδb ?_
      simp only [hT, measure_toMeasurable]
      exact hbad u hu
    have e := hGT u hu
    simp only [hsc] at e
    rw [e]
    obtain ⟨hψ1, hψ2⟩ := hL2 u hu _ (Or.inl rfl)
    obtain ⟨hΦ1, hΦ2⟩ := hL2 u hu _ (Or.inr rfl)
    exact ⟨lemmaNOffset_cs _ _ hψ1 hTm hK hψ2 hTδ, lemmaNOffset_cs _ _ hΦ1 hTm hK hΦ2 hTδ⟩
  -- the no-exit lemma
  have hrate' : ∀ u ∈ Set.Ioo s v, ∀ y ∈ G u, X u y ≤ J * (1 + 2 * β) →
      |(coordGen σ2 (fun t z => ((X t z : ℝ) : ℂ)) u y).re| ≤ κ * X u y / (1 - u) ∧
        (coordGamma σ2 (fun z => ((X u z : ℝ) : ℂ)) (fun z => ((X u z : ℝ) : ℂ)) y).re ≤
          bΓ * X u y ^ 2 / (1 - u) := fun u hu y hy hXy =>
    hrate u hu y (hGbad u hu y hy) hXy
  obtain ⟨hN1, hN2⟩ := noExit' σ2 hσ2.le X ha hs.le hsv hvb hv1 hX hX0 hρ r hr hJ hβ hκ hbΓ
    (mul_nonneg hK (Real.sqrt_nonneg _)) G hGm hrate' hoff
  -- the initial values
  have hsab : s ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have hXs : Continuous (fun x : ι → ℝ => X s (Real.sqrt (s * σ2) • x)) :=
    (lemmaN_heat_cont_re hX hsab).comp (continuous_const_smul _)
  set Ts := toMeasurable (stdGauss ι) {x | 2 * δs < X s (Real.sqrt (s * σ2) • x)} with hTs
  have hTsm : MeasurableSet Ts := measurableSet_toMeasurable _ _
  have hTsδ : stdGauss ι Ts ≤ ENNReal.ofReal δb := by rw [hTs, measure_toMeasurable]; exact hinit
  have hoffTs : ∀ x, x ∉ Ts → X s (Real.sqrt (s * σ2) • x) ≤ 2 * δs := by
    intro x hx
    by_contra h
    exact hx (subset_toMeasurable _ _ (lt_of_not_ge h))
  have hFs : ∫ x, cutPsi ρ J β r (X s (Real.sqrt (s * σ2) • x)) ∂(stdGauss ι) ≤
      (2 * δs / J) ^ (2 * r) + (1 + 2 * β) ^ (2 * r) * δb := by
    refine lemmaN_integral_split ((cutPsi_C2b hρ hJ hβ r).1.continuous.comp hXs)
      (fun x => hprops _ |>.2.2.2) (fun x => (hψb _ (hX0 _ _)).2) hTsm hTsδ hδb
      (fun x hx => ?_) (by positivity)
    refine (hψb _ (hX0 _ _)).1.trans ?_
    exact pow_le_pow_left₀ (div_nonneg (hX0 _ _) hJ.le)
      (div_le_div_of_nonneg_right (hoffTs x hx) hJ.le) _
  have hes : ∫ x, cutPhi ρ J β (X s (Real.sqrt (s * σ2) • x)) ∂(stdGauss ι) ≤ 0 + 1 * δb := by
    refine lemmaN_integral_split ((cutPhi_C2b hρ hJ hβ).1.continuous.comp hXs)
      (fun x => (hprops _).1) (fun x => (hprops _).2.1) hTsm hTsδ hδb (fun x hx => ?_) le_rfl
    show cutPhi ρ J β (X s (Real.sqrt (s * σ2) • x)) ≤ 0
    rw [lemmaN_phi_zero hρ hJ hβ ((hoffTs x hx).trans hδsJ)]
  -- the final estimate
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hA12 : 0 < rateMulA12 ε β κ bΓ r := by
    unfold rateMulA12 rateA12 rateMulC12
    have : 0 < 1 - ε := by linarith
    have h1 : 0 < (1 + 2 * β) ^ (2 * r + 1) * (1 - ε)⁻¹ * κ / β := by positivity
    have h2 : 0 ≤ (2 * r * (1 + 2 * β) ^ (2 * r + 1) * (1 - ε)⁻¹ / β +
        3 * (1 + 2 * β) ^ (2 * r + 2) / (4 * ε * (1 - ε) * β ^ 2)) * bΓ := by positivity
    linarith
  have hA11 : 0 < rateMulA11 κ bΓ r := by
    unfold rateMulA11
    have : 0 ≤ (r : ℝ) * (2 * r - 1) * bΓ := by
      have : (0 : ℝ) ≤ 2 * r - 1 := by linarith
      positivity
    have : 0 < 2 * (r : ℝ) * κ := by positivity
    linarith
  have hρ' : 0 < perronMul ε β κ bΓ r := by
    unfold perronMul
    have := Real.sqrt_nonneg ((rateMulA11 κ bΓ r / 2) ^ 2 + rateMulA12 ε β κ bΓ r *
      rateMulA21 ε β κ bΓ)
    linarith
  set ρ' := perronMul ε β κ bΓ r with hρ'def
  set a12 := rateMulA12 ε β κ bΓ r with ha12def
  set lam := a12 / ρ' with hlam
  have hlam0 : 0 < lam := div_pos hA12 hρ'
  have hψv0 : 0 ≤ ∫ x, cutPsi ρ J β r (X v (Real.sqrt (v * σ2) • x)) ∂(stdGauss ι) :=
    integral_nonneg fun x => (hprops _).2.2.2
  set Rp := ((1 - s) / (1 - v)) ^ ρ' with hRp
  have hRp0 : 0 ≤ Rp := Real.rpow_nonneg (div_nonneg (by linarith) (by linarith)) _
  have hvs : 0 ≤ v - s := by linarith
  have hvs1 : v - s ≤ 1 := by linarith
  have hKo : 0 ≤ K * Real.sqrt δb := mul_nonneg hK (Real.sqrt_nonneg _)
  have hmain : lam * ∫ x, cutPhi ρ J β (X v (Real.sqrt (v * σ2) • x)) ∂(stdGauss ι) ≤
      Rp * ((2 * δs / J) ^ (2 * r) + ((1 + 2 * β) ^ (2 * r) + lam) * δb +
        (1 + lam) * (K * Real.sqrt δb)) := by
    have h1 : (v - s) * ((1 + lam) * (K * Real.sqrt δb)) ≤ (1 + lam) * (K * Real.sqrt δb) := by
      have : 0 ≤ (1 + lam) * (K * Real.sqrt δb) := by positivity
      nlinarith
    have h2 : lam * ∫ x, cutPhi ρ J β (X s (Real.sqrt (s * σ2) • x)) ∂(stdGauss ι) ≤
        lam * δb := by
      have := mul_le_mul_of_nonneg_left hes hlam0.le
      linarith
    have h3 : (∫ x, cutPsi ρ J β r (X s (Real.sqrt (s * σ2) • x)) ∂(stdGauss ι)) +
        lam * (∫ x, cutPhi ρ J β (X s (Real.sqrt (s * σ2) • x)) ∂(stdGauss ι)) +
        (v - s) * ((1 + lam) * (K * Real.sqrt δb)) ≤
        (2 * δs / J) ^ (2 * r) + ((1 + 2 * β) ^ (2 * r) + lam) * δb +
          (1 + lam) * (K * Real.sqrt δb) := by
      nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 hRp0
    linarith [hN2]
  have hΦv : ∫ x, cutPhi ρ J β (X v (Real.sqrt (v * σ2) • x)) ∂(stdGauss ι) ≤
      (ρ' / a12) * (Rp * ((2 * δs / J) ^ (2 * r) + ((1 + 2 * β) ^ (2 * r) + lam) * δb +
        (1 + lam) * (K * Real.sqrt δb))) := by
    have e : ρ' / a12 = lam⁻¹ := by rw [hlam, inv_div]
    rw [e, ← div_eq_inv_mul, le_div_iff₀ hlam0, mul_comm]
    exact hmain
  exact hN1.trans (ENNReal.ofReal_le_ofReal hΦv)

end Core


section AtPoint

open scoped Matrix.Norms.L2Operator

/-- The surrogate is at least its floor when the sample set is nonempty. -/
private theorem lemmaN_lqSurr_ge {S : Type*} [Fintype S] [Nonempty S] {q : ℕ} (hq : 1 ≤ q)
    {env : S → ℝ} (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ) (y : S → ℂ) :
    δ ≤ lqSurr q env δ y := by
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : (δ ^ 2) ^ q ≤ ∑ s, (‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2) ^ q := by
    calc (δ ^ 2) ^ q ≤ (‖y s₀‖ ^ 2 / env s₀ ^ 2 + δ ^ 2) ^ q := by
          exact pow_le_pow_left₀ (sq_nonneg δ)
            (le_add_of_nonneg_left (by have := henv s₀; positivity)) q
      _ ≤ _ := Finset.single_le_sum (f := fun s => (‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2) ^ q)
          (fun s _ => by have := henv s; positivity) (Finset.mem_univ s₀)
  have e : ((δ ^ 2) ^ q) ^ ((1 : ℝ) / (2 * q)) = δ := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    have : ((2 * q : ℕ) : ℝ) * (1 / (2 * q)) = 1 := by push_cast; field_simp
    rw [this, Real.rpow_one]
  calc δ = ((δ ^ 2) ^ q) ^ ((1 : ℝ) / (2 * q)) := e.symm
    _ ≤ lqSurr q env δ y := by
        unfold lqSurr
        exact Real.rpow_le_rpow (by positivity) h1 (by positivity)

/-- The surrogate is nonnegative. -/
private theorem lemmaN_lqSurr_nonneg {S : Type*} [Fintype S] (q : ℕ) (env : S → ℝ) (δ : ℝ)
    (y : S → ℂ) : 0 ≤ lqSurr q env δ y := by
  unfold lqSurr
  positivity

set_option maxHeartbeats 1000000 in
/-- The rates of the surrogate of the mixed-pair errors at a good point `y` at a time `u`: from the
Step 1 envelopes, the weighted sampling at `(u, v)` and the deterministic rows,
`|Re 𝒢X| ≤ κX/(1-u)` and `Re Γ(X) ≤ bΓX²/(1-u)`. -/
private theorem lemmaN_surr_good (g E : ℝ) (m : ℂ) {W L : ℕ} (hW : 4 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (S' S₀ : Finset (Fin L × Fin L))
    (hS₀ : S₀ ⊆ S') (hS'ne : S'.Nonempty) {q : ℕ} (hq : 1 ≤ q)
    (hS : ((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / (2 * q)) ≤ 1.001)
    {a b u : ℝ} (hab : ∀ s : Fin L × Fin L, HeatClass (fun r x => pairErrField g E m W L r x s) a b)
    (hu : u ∈ Set.Ioo a b) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (w : Fin L → Fin L → ℝ) (hw0 : ∀ x y, 0 ≤ w x y) (hw2 : ∀ x y, w x y ≤ 2)
    (hws : ∀ x y, w x y = w y x) {wmin : ℝ} (hwmin0 : 0 < wmin) (hwmin : ∀ x y, wmin ≤ w x y)
    {ω R P ζu ζv ζt ev Cw Cc ℓv κK h H εw C' lH κ bΓ : ℝ}
    (hω : 2 ≤ ω) (hR : 1 ≤ R) (hP : 0 ≤ P) (hζu : 0 < ζu) (hζuv : ζu ≤ ζv)
    (hζt : ζv ≤ ζt) (hζvW : (2 * (W : ℝ))⁻¹ ≤ ζv) (hev : 0 < ev) (h4 : 1 - u ≤ R * ev)
    (hZ : ζu ^ 2 * (1 - u) ≤ ζv ^ 2 * ev)
    (hRP : R ^ 3 * P * ζt * ω ^ 400 ≤ 1) (hR5 : R ^ 5 * ζt * ω ^ 400 ≤ 1)
    (hΓ : gammaG g * W * ℓv * ζv * ev = 1) (hℓv : 1 ≤ ℓv)
    (hCw : 1 ≤ Cw) (hCwω : 2 * Cw ≤ ω) (hCc : 0 ≤ Cc) (hCcω : Cc ≤ ω) (hC' : 0 ≤ C')
    (hC'ω : C' ≤ ω) (hh : 0 ≤ h) (hhH : h ≤ H) (hH : H = ℓv * lH) (hlH0 : 0 ≤ lH) (hlH : lH ≤ ω)
    (hεw : 0 ≤ εw)
    (hκK : κK ≤ (1.001 + 2 / (W : ℝ) ^ 2) * (1 - u)⁻¹)
    (hκ : 1.001 * (2 * (1.001 + 2 / (W : ℝ) ^ 2) * (Cw * (1 + 1 / (W : ℝ))) + 1 / (2 * ω)) +
      1.003 * q * (1 / (2 * ω)) ≤ κ) (hbΓ : 1.003 * (1 / (2 * ω)) ≤ bΓ)
    (hconv : ∀ x y, ∑ c, w x c * w c y ≤ Cc * ℓv * w x y ∧
      ∑ c, Real.sqrt (w x c * w c y) ≤ Cc * ℓv * Real.sqrt (w x y))
    (hker : ∀ x y, ∑ c, mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) u x c *
      w c y ≤ κK * w x y)
    (hprim : ∀ x y, h < cycDist x y →
      ‖primLoop g W L E m u ![x, y] ![true, false]‖ ≤ C' * ζv ^ 2 * w x y)
    (hshort : ∀ x y, (cycDist x y : ℝ) ≤ 2 * h → ω⁻¹ ≤ w x y)
    (hfar : ∀ x y, H < cycDist x y → w x y ≤ εw)
    (y : Ω W L)
    (hop : ∀ x z, ‖blockOf (resolventMat (blockSlice W L (Ag g L ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ)) y) (zChar g E m u)) x z‖ ≤ ω * (W * R * ζu))
    (hhs : ∀ x z, blockHS2 (resolventMat (blockSlice W L (Ag g L ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ)) y) (zChar g E m u)) x z ≤ ω * ((W : ℝ) ^ 2 * R * ζu))
    (havg : ∀ c, ‖blockTr (resolventMat (blockSlice W L (Ag g L ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ)) y) (zChar g E m u) -
      dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c‖ ≤
        ω * (R ^ 2 * ζu))
    (hsw : ∀ l : Fin L × Fin L, ‖pairErrField g E m W L u y l‖ / w l.1 l.2 ≤
      Cw * (⨆ s : S₀, ‖pairErrField g E m W L u y s‖ / w s.1.1 s.1.2) + (W : ℝ) ^ (-4 : ℝ))
    (hXP : lqSurr q (fun s : S' => ζv ^ 2 * w s.1.1 s.1.2) (R ^ 4 * ω ^ 25)
      (fun s : S' => pairErrField g E m W L u y s) ≤ ω ^ 100 * P)
    (hLr : (L : ℝ) * Real.sqrt (max (ω ^ 2) ((C' + Cw * (1 + 1 / (W : ℝ)) *
      lqSurr q (fun s : S' => ζv ^ 2 * w s.1.1 s.1.2) (R ^ 4 * ω ^ 25)
        (fun s : S' => pairErrField g E m W L u y s)) * ζv ^ 2 / (ω * R * ζu) ^ 2) * εw) ≤ ℓv) :
    |(coordGen (gammaG g / W) (fun r z => ((lqSurr q (fun s : S' => ζv ^ 2 * w s.1.1 s.1.2)
        (R ^ 4 * ω ^ 25) (fun s : S' => pairErrField g E m W L r z s) : ℝ) : ℂ)) u y).re| ≤
        κ * lqSurr q (fun s : S' => ζv ^ 2 * w s.1.1 s.1.2) (R ^ 4 * ω ^ 25)
          (fun s : S' => pairErrField g E m W L u y s) / (1 - u) ∧
      (coordGamma (gammaG g / W)
          (fun z => ((lqSurr q (fun s : S' => ζv ^ 2 * w s.1.1 s.1.2) (R ^ 4 * ω ^ 25)
            (fun s : S' => pairErrField g E m W L u z s) : ℝ) : ℂ))
          (fun z => ((lqSurr q (fun s : S' => ζv ^ 2 * w s.1.1 s.1.2) (R ^ 4 * ω ^ 25)
            (fun s : S' => pairErrField g E m W L u z s) : ℝ) : ℂ)) y).re ≤
        bΓ * lqSurr q (fun s : S' => ζv ^ 2 * w s.1.1 s.1.2) (R ^ 4 * ω ^ 25)
          (fun s : S' => pairErrField g E m W L u y s) ^ 2 / (1 - u) := by
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW4 : (4 : ℝ) ≤ W := by exact_mod_cast hW
  have hω0 : 0 < ω := by linarith
  have hζv : 0 < ζv := lt_of_lt_of_le hζu hζuv
  have heu : 0 < 1 - u := by linarith
  have hσ2 : 0 ≤ gammaG g / W := by
    have : 0 < gammaG g := by unfold gammaG; positivity
    positivity
  set env : S' → ℝ := fun s => ζv ^ 2 * w s.1.1 s.1.2 with henvdef
  have henv : ∀ s, 0 < env s := fun s => by
    simp only [henvdef]; exact mul_pos (by positivity) (lt_of_lt_of_le hwmin0 (hwmin _ _))
  set δs := R ^ 4 * ω ^ 25 with hδs
  have hδs0 : 0 < δs := by positivity
  have : Nonempty S' := hS'ne.to_subtype
  set X := lqSurr q env δs (fun s : S' => pairErrField g E m W L u y s) with hXdef
  have hX1 : δs ≤ X := lemmaN_lqSurr_ge hq henv hδs0 _
  have hX : 1 ≤ X := by
    have : 1 ≤ δs := by
      have h1 : 1 ≤ R ^ 4 := one_le_pow₀ hR
      have h2 : 1 ≤ ω ^ 25 := one_le_pow₀ (by linarith)
      nlinarith
    linarith
  set Λ := Cw * (1 + 1 / (W : ℝ)) * X with hΛdef
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΛωX : Λ ≤ ω * X := by
    have : Cw * (1 + 1 / (W : ℝ)) ≤ ω := by
      have : 1 / (W : ℝ) ≤ 1 := by rw [div_le_one hW0]; linarith
      nlinarith
    calc Λ = Cw * (1 + 1 / (W : ℝ)) * X := rfl
      _ ≤ ω * X := by gcongr
  have hΛ1 : 1 ≤ C' + Λ := by
    have : 1 ≤ Cw * (1 + 1 / (W : ℝ)) := by
      have : 0 ≤ 1 / (W : ℝ) := by positivity
      nlinarith
    have : 1 ≤ Λ := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ Cw * (1 + 1 / (W : ℝ)) * X := mul_le_mul this hX zero_le_one (by positivity)
    linarith
  have hΛω : C' + Λ ≤ ω ^ 2 * X := by
    have : C' ≤ ω * X := by nlinarith
    nlinarith
  -- the pair bound from the weighted sampling
  have hsup : (⨆ s : S₀, ‖pairErrField g E m W L u y s‖ / w s.1.1 s.1.2) ≤ ζv ^ 2 * X := by
    refine Real.iSup_le (fun s => ?_) (by positivity)
    have hs' : s.1 ∈ S' := hS₀ s.2
    have h1 := lqSurr_label_le hq henv hδs0 (fun s : S' => pairErrField g E m W L u y s) ⟨s.1, hs'⟩
    rw [← hXdef] at h1
    have hw : 0 < w s.1.1 s.1.2 := lt_of_lt_of_le hwmin0 (hwmin _ _)
    simp only [henvdef] at h1
    rw [div_le_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ hw]
    calc ‖pairErrField g E m W L u y s‖ ≤ X * (ζv ^ 2 * w s.1.1 s.1.2) := h1
      _ = ζv ^ 2 * X * w s.1.1 s.1.2 := by ring
  have hD : ∀ x z, ‖resLoop g E m ![x, z] ![true, false] u (blockSlice W L (Ag g L ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ)) y) - primLoop g W L E m u ![x, z] ![true, false]‖ ≤
      Λ * ζv ^ 2 * w x z := by
    intro x z
    have hw : 0 < w x z := lt_of_lt_of_le hwmin0 (hwmin _ _)
    have h1 := hsw (x, z)
    show ‖pairErrField g E m W L u y (x, z)‖ ≤ Λ * ζv ^ 2 * w x z
    rw [div_le_iff₀ hw] at h1
    have h2 : (W : ℝ) ^ (-4 : ℝ) ≤ Cw * (1 / (W : ℝ)) * X * ζv ^ 2 := by
      have e : (W : ℝ) ^ (-4 : ℝ) = ((W : ℝ) ^ 4)⁻¹ := by
        rw [Real.rpow_neg hW0.le]; norm_cast
      rw [e]
      have hz : (4 * (W : ℝ) ^ 2)⁻¹ ≤ ζv ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hζvW 2
        calc (4 * (W : ℝ) ^ 2)⁻¹ = ((2 * (W : ℝ))⁻¹) ^ 2 := by field_simp; ring
          _ ≤ ζv ^ 2 := this
      have h3 : ((W : ℝ) ^ 4)⁻¹ ≤ 1 * (1 / (W : ℝ)) * 1 * (4 * (W : ℝ) ^ 2)⁻¹ := by
        rw [inv_le_comm₀ (by positivity) (by positivity)]
        field_simp
        nlinarith
      calc ((W : ℝ) ^ 4)⁻¹ ≤ 1 * (1 / (W : ℝ)) * 1 * (4 * (W : ℝ) ^ 2)⁻¹ := h3
        _ ≤ Cw * (1 / (W : ℝ)) * X * ζv ^ 2 := by gcongr
    calc ‖pairErrField g E m W L u y (x, z)‖ ≤
        (Cw * (⨆ s : S₀, ‖pairErrField g E m W L u y s‖ / w s.1.1 s.1.2) +
          (W : ℝ) ^ (-4 : ℝ)) * w x z := h1
      _ ≤ (Cw * (ζv ^ 2 * X) + Cw * (1 / (W : ℝ)) * X * ζv ^ 2) * w x z := by
          gcongr
      _ = Λ * ζv ^ 2 * w x z := by simp only [hΛdef]; ring
  -- the rows for each sample pair
  have hM := lemmaN_slice_herm g hW1 y
  have hrows := fun (s : S') => lemmaN_good_rates g E m hW1 hL hm hu0 hu1 hM w hw0 hw2 hws hwmin0
    hwmin (ω := ω) (R := R) (P := P) (X := X) (ζu := ζu) (ζv := ζv) (ζt := ζt) (ev := ev)
    (Λ := Λ) (Cc := Cc) (ℓv := ℓv) (κK := κK) (h := h) (H := H) (εw := εw) (C' := C') (lH := lH)
    hω hR hP hX hζu hζuv hζt hev h4 hZ hRP hR5 hX1 hXP hΓ hℓv hΛ0 hΛωX hCc hCcω hC' hΛ1 hΛω hh
    hhH hH hlH0 hlH hLr hεw hD hconv hker
    (fun x z => by have := hop x z; linarith [show ω * (W * R * ζu) = W * (ω * R * ζu) by ring])
    (fun x z => by
      have := hhs x z; linarith [show ω * ((W : ℝ) ^ 2 * R * ζu) = (W : ℝ) ^ 2 * (ω * R * ζu) by
        ring])
    (fun c => by have := havg c; linarith [show ω * (R ^ 2 * ζu) = ω * R ^ 2 * ζu by ring])
    hprim hshort hfar s.1.1 s.1.2
  set κl := 2 * (1.001 + 2 / (W : ℝ) ^ 2) * (Cw * (1 + 1 / (W : ℝ))) + 1 / (2 * ω) with hκl
  have hκl0 : 0 ≤ κl := by positivity
  refine lemmaN_surr_rates (gammaG g / W) hσ2 hq henv hδs0
    (fun s : S' => fun r x => pairErrField g E m W L r x s) (fun s => hab s) hu hu1 y hS
    hκl0 (by positivity : (0 : ℝ) ≤ 1 / (2 * ω)) ?_ ?_ hκ hbΓ
  · intro s
    have hgen := (hrows s).1
    rw [← lemmaN_coordGen_eq] at hgen
    rw [← hXdef, div_le_iff₀ (henv s)]
    refine hgen.trans ?_
    have : 2 * κK * Λ + X / (2 * ω) * (1 - u)⁻¹ ≤ κl * X / (1 - u) := by
      have h1 : 2 * κK * Λ ≤ 2 * ((1.001 + 2 / (W : ℝ) ^ 2) * (1 - u)⁻¹) * Λ := by gcongr
      calc 2 * κK * Λ + X / (2 * ω) * (1 - u)⁻¹ ≤
          2 * ((1.001 + 2 / (W : ℝ) ^ 2) * (1 - u)⁻¹) * Λ + X / (2 * ω) * (1 - u)⁻¹ := by
            linarith
        _ = κl * X / (1 - u) := by simp only [hκl, hΛdef]; field_simp
    calc (2 * κK * Λ + X / (2 * ω) * (1 - u)⁻¹) * (ζv ^ 2 * w s.1.1 s.1.2) ≤
        κl * X / (1 - u) * (ζv ^ 2 * w s.1.1 s.1.2) := by
          gcongr; exact le_of_lt (henv s)
      _ = κl * X / (1 - u) * env s := rfl
  · intro s
    have hgam := (hrows s).2
    rw [← lemmaN_coordGamma_eq] at hgam
    rw [← hXdef, div_le_iff₀ (by have := henv s; positivity)]
    refine hgam.trans (le_of_eq ?_)
    simp only [henvdef]
    field_simp

end AtPoint


section OffSet

/-- The single-time realization at the scaled coordinates is the block slice. -/
private theorem lemmaN_flowH_eq (g : ℝ) (W L : ℕ) {u : ℝ} (hu : 0 ≤ u) (ω : Ω W L) :
    flowH g W L u ω = blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
      (Real.sqrt (u * (gammaG g / W)) • ω) := by
  have hγ : 0 ≤ gammaG g := by unfold gammaG; positivity
  unfold flowH
  rw [blockFlow_eq_blockSlice _ _ _ (mul_nonneg hu hγ), mul_div_assoc]

/-- `μ W L` is the standard Gaussian on the block coordinates. -/
private theorem lemmaN_mu_eq (W L : ℕ) : μ W L = stdGauss (Fin L × Fin W × Fin W) := rfl

/-- A nonnegative function whose `p`-th power is integrable is a.e. strongly measurable. -/
private theorem lemmaN_aesm_of_pow {α : Type*} [MeasurableSpace α] {P : Measure α} {f : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {p : ℕ} (hp : 1 ≤ p) (hf : Integrable (fun x => f x ^ p) P) :
    AEStronglyMeasurable f P := by
  have h1 : AEStronglyMeasurable (fun x => (f x ^ p) ^ ((1 : ℝ) / p)) P :=
    (Real.continuous_rpow_const (by positivity)).comp_aestronglyMeasurable hf.aestronglyMeasurable
  refine h1.congr (Eventually.of_forall fun x => ?_)
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only
  rw [← Real.rpow_natCast, ← Real.rpow_mul (hf0 x), mul_one_div_cancel hp0, Real.rpow_one]

/-- The `L²` bound of the generator of a cutoff of the surrogate of the mixed-pair errors from
the moments of the generator and the bracket of the mixed two-loop errors. -/
private theorem lemmaN_offset_L2 (g E : ℝ) {W L : ℕ} (hW : 1 ≤ W) (S' : Finset (Fin L × Fin L))
    {q : ℕ} (hq : 1 ≤ q) {env : S' → ℝ} {e₀ : ℝ} (he₀ : 0 < e₀) (he₀1 : e₀ ≤ 1)
    (henv : ∀ s, e₀ ≤ env s) {δ : ℝ} (hδ : 1 ≤ δ) {a b u : ℝ} (hu0 : 0 ≤ u)
    (hY : ∀ s : Fin L × Fin L,
      HeatClass (fun r x => pairErrField g E (mRoot g L E) W L r x s) a b)
    (hu : u ∈ Set.Ioo a b) (φ : ℝ → ℝ) (hφ : C2b φ) {Cφ : ℝ}
    (hCφ : ∀ x, |deriv φ x| ≤ Cφ ∧ |iteratedDeriv 2 φ x| ≤ Cφ) (p : ℕ) (hp : 2 ≤ p) {Cp C₁ : ℝ}
    (hmom : ∀ a b : Fin L,
      Integrable (fun ω => ‖blockGen W L (gammaG g) (fun r N =>
          resLoop g E (mRoot g L E) ![a, b] ![true, false] r N -
            primLoop g W L E (mRoot g L E) r ![a, b] ![true, false]) u
          (flowH g W L u ω)‖ ^ p) (μ W L) ∧
      ∫ ω, ‖blockGen W L (gammaG g) (fun r N =>
          resLoop g E (mRoot g L E) ![a, b] ![true, false] r N -
            primLoop g W L E (mRoot g L E) r ![a, b] ![true, false]) u
          (flowH g W L u ω)‖ ^ p ∂(μ W L) ≤ Cp * (W : ℝ) ^ (C₁ * p) ∧
      Integrable (fun ω => ‖blockGamma W L (gammaG g)
          (resLoop g E (mRoot g L E) ![a, b] ![true, false] u)
          (resLoop g E (mRoot g L E) ![a, b] ![true, false] u)
          (flowH g W L u ω)‖ ^ p) (μ W L) ∧
      ∫ ω, ‖blockGamma W L (gammaG g)
          (resLoop g E (mRoot g L E) ![a, b] ![true, false] u)
          (resLoop g E (mRoot g L E) ![a, b] ![true, false] u)
          (flowH g W L u ω)‖ ^ p ∂(μ W L) ≤ Cp * (W : ℝ) ^ (C₁ * p)) :
    MemLp (fun x => (coordGen (gammaG g / W) (fun r z => ((φ (lqSurr q env δ
        (fun s : S' => pairErrField g E (mRoot g L E) W L r z s)) : ℝ) : ℂ)) u
        (Real.sqrt (u * (gammaG g / W)) • x)).re) 2 (stdGauss (Fin L × Fin W × Fin W)) ∧
      ∫ x, ((coordGen (gammaG g / W) (fun r z => ((φ (lqSurr q env δ
        (fun s : S' => pairErrField g E (mRoot g L E) W L r z s)) : ℝ) : ℂ)) u
        (Real.sqrt (u * (gammaG g / W)) • x)).re) ^ 2 ∂(stdGauss (Fin L × Fin W × Fin W)) ≤
      (Cφ * (q + 2) * ((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / q) *
        ((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / p) *
        (2 * (e₀ ^ 2)⁻¹ * (max Cp 0 + 1) * (W : ℝ) ^ C₁)) ^ 2 := by
  have hσ2 : 0 ≤ gammaG g / W := by
    have : 0 < gammaG g := by unfold gammaG; positivity
    positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set B := 2 * (e₀ ^ 2)⁻¹ * (max Cp 0 + 1) * (W : ℝ) ^ C₁ with hB
  have hB0 : 0 ≤ B := by positivity
  have hp1 : 1 ≤ p := by omega
  have henv0 : ∀ s, 0 < env s := fun s => lt_of_lt_of_le he₀ (henv s)
  have key : ∀ s : S', Integrable (fun x : Fin L × Fin W × Fin W → ℝ =>
        (‖coordGen (gammaG g / W) (fun r x => pairErrField g E (mRoot g L E) W L r x s) u
          (Real.sqrt (u * (gammaG g / W)) • x)‖ / env s +
          (coordGamma (gammaG g / W) (fun x => pairErrField g E (mRoot g L E) W L u x s)
            (fun x => pairErrField g E (mRoot g L E) W L u x s) (Real.sqrt (u * (gammaG g / W)) • x)).re / env s ^ 2) ^ p)
        (stdGauss (Fin L × Fin W × Fin W)) ∧
      ∫ x, (‖coordGen (gammaG g / W) (fun r x => pairErrField g E (mRoot g L E) W L r x s) u
          (Real.sqrt (u * (gammaG g / W)) • x)‖ / env s +
          (coordGamma (gammaG g / W) (fun x => pairErrField g E (mRoot g L E) W L u x s)
            (fun x => pairErrField g E (mRoot g L E) W L u x s) (Real.sqrt (u * (gammaG g / W)) • x)).re / env s ^ 2) ^ p
        ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ B ^ p := by
    intro s
    obtain ⟨hi1, hb1, hi2, hb2⟩ := hmom s.1.1 s.1.2
    set fG : (Fin L × Fin W × Fin W → ℝ) → ℝ := fun x => ‖blockGen W L (gammaG g) (fun r N =>
          resLoop g E (mRoot g L E) ![s.1.1, s.1.2] ![true, false] r N -
            primLoop g W L E (mRoot g L E) r ![s.1.1, s.1.2] ![true, false]) u
          (flowH g W L u x)‖ with hfG
    set fΓ : (Fin L × Fin W × Fin W → ℝ) → ℝ := fun x => ‖blockGamma W L (gammaG g)
          (resLoop g E (mRoot g L E) ![s.1.1, s.1.2] ![true, false] u)
          (resLoop g E (mRoot g L E) ![s.1.1, s.1.2] ![true, false] u)
          (flowH g W L u x)‖ with hfΓ
    have eG : ∀ x, ‖coordGen (gammaG g / W) (fun r x => pairErrField g E (mRoot g L E) W L r x s) u
        (Real.sqrt (u * (gammaG g / W)) • x)‖ = fG x := by
      intro x
      simp only [hfG, lemmaN_flowH_eq g W L hu0, lemmaN_coordGen_eq]
    have eΓ : ∀ x, (coordGamma (gammaG g / W) (fun x => pairErrField g E (mRoot g L E) W L u x s)
        (fun x => pairErrField g E (mRoot g L E) W L u x s) (Real.sqrt (u * (gammaG g / W)) • x)).re = fΓ x := by
      intro x
      rw [lemmaN_gamma_re_eq_norm hσ2]
      simp only [hfΓ, lemmaN_flowH_eq g W L hu0, lemmaN_coordGamma_eq]
    simp only [eG, eΓ]
    rw [lemmaN_mu_eq] at hi1 hb1 hi2 hb2
    have hfG0 : ∀ x, 0 ≤ fG x := fun x => norm_nonneg _
    have hfΓ0 : ∀ x, 0 ≤ fΓ x := fun x => norm_nonneg _
    have hmG := lemmaN_aesm_of_pow hfG0 hp1 hi1
    have hmΓ := lemmaN_aesm_of_pow hfΓ0 hp1 hi2
    have he := henv s
    have hpt : ∀ x, (fG x / env s + fΓ x / env s ^ 2) ^ p ≤
        ((e₀ ^ 2)⁻¹) ^ p * (2 ^ (p - 1) * (fG x ^ p + fΓ x ^ p)) := by
      intro x
      have h1 : fG x / env s ≤ (e₀ ^ 2)⁻¹ * fG x := by
        rw [div_le_iff₀ (henv0 s)]
        have : 1 ≤ (e₀ ^ 2)⁻¹ * env s := by
          rw [← div_eq_inv_mul, le_div_iff₀ (by positivity)]
          nlinarith
        nlinarith [hfG0 x]
      have h2 : fΓ x / env s ^ 2 ≤ (e₀ ^ 2)⁻¹ * fΓ x := by
        rw [div_le_iff₀ (by have := henv0 s; positivity)]
        have : 1 ≤ (e₀ ^ 2)⁻¹ * env s ^ 2 := by
          rw [← div_eq_inv_mul, le_div_iff₀ (by positivity)]
          nlinarith
        nlinarith [hfΓ0 x]
      calc (fG x / env s + fΓ x / env s ^ 2) ^ p ≤ ((e₀ ^ 2)⁻¹ * fG x + (e₀ ^ 2)⁻¹ * fΓ x) ^ p := by
            gcongr
            have := hfG0 x; have := hfΓ0 x; have := henv0 s; positivity
        _ = ((e₀ ^ 2)⁻¹) ^ p * (fG x + fΓ x) ^ p := by rw [← mul_add, mul_pow]
        _ ≤ ((e₀ ^ 2)⁻¹) ^ p * (2 ^ (p - 1) * (fG x ^ p + fΓ x ^ p)) := by
            gcongr; exact add_pow_le (hfG0 x) (hfΓ0 x) p
    have hdom : Integrable (fun x => ((e₀ ^ 2)⁻¹) ^ p * (2 ^ (p - 1) * (fG x ^ p + fΓ x ^ p)))
        (stdGauss (Fin L × Fin W × Fin W)) := ((hi1.add hi2).const_mul _).const_mul _
    have hmeas : AEStronglyMeasurable (fun x => (fG x / env s + fΓ x / env s ^ 2) ^ p)
        (stdGauss (Fin L × Fin W × Fin W)) :=
      (((hmG.aemeasurable.div_const (env s)).add
        (hmΓ.aemeasurable.div_const (env s ^ 2))).pow_const p).aestronglyMeasurable
    refine ⟨hdom.mono' hmeas (Eventually.of_forall fun x => ?_), ?_⟩
    · rw [Real.norm_eq_abs, abs_of_nonneg (by have := hfG0 x; have := hfΓ0 x; have := henv0 s; positivity)]
      exact hpt x
    · calc ∫ x, (fG x / env s + fΓ x / env s ^ 2) ^ p ∂(stdGauss (Fin L × Fin W × Fin W)) ≤
          ∫ x, ((e₀ ^ 2)⁻¹) ^ p * (2 ^ (p - 1) * (fG x ^ p + fΓ x ^ p))
            ∂(stdGauss (Fin L × Fin W × Fin W)) :=
            integral_mono (hdom.mono' hmeas (Eventually.of_forall fun x => by
              rw [Real.norm_eq_abs, abs_of_nonneg (by have := hfG0 x; have := hfΓ0 x; have := henv0 s; positivity)]
              exact hpt x)) hdom hpt
        _ = ((e₀ ^ 2)⁻¹) ^ p * (2 ^ (p - 1) *
              ((∫ x, fG x ^ p ∂(stdGauss (Fin L × Fin W × Fin W))) +
                ∫ x, fΓ x ^ p ∂(stdGauss (Fin L × Fin W × Fin W)))) := by
            rw [integral_const_mul, integral_const_mul, integral_add hi1 hi2]
        _ ≤ ((e₀ ^ 2)⁻¹) ^ p * (2 ^ (p - 1) *
              (max Cp 0 * (W : ℝ) ^ (C₁ * p) + max Cp 0 * (W : ℝ) ^ (C₁ * p))) := by
            have hWp : 0 ≤ (W : ℝ) ^ (C₁ * p) := by positivity
            have h1 : Cp * (W : ℝ) ^ (C₁ * p) ≤ max Cp 0 * (W : ℝ) ^ (C₁ * p) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hWp
            gcongr <;> linarith
        _ = (2 * (e₀ ^ 2)⁻¹) ^ p * max Cp 0 * ((W : ℝ) ^ C₁) ^ p := by
            rw [← Real.rpow_natCast ((W : ℝ) ^ C₁), ← Real.rpow_mul hW0.le]
            have h2 : (2 : ℝ) ^ p = 2 ^ (p - 1) * 2 := by
              rw [← pow_succ]; congr 1; omega
            rw [mul_pow, h2]
            ring
        _ ≤ B ^ p := by
            have hm : max Cp 0 ≤ (max Cp 0 + 1) ^ p := by
              have h1 : max Cp 0 ≤ max Cp 0 + 1 := by linarith
              have h2 : max Cp 0 + 1 ≤ (max Cp 0 + 1) ^ p :=
                le_self_pow₀ (by linarith [le_max_right Cp 0]) (by omega)
              linarith
            have : 0 ≤ (2 * (e₀ ^ 2)⁻¹) ^ p := by positivity
            have : 0 ≤ ((W : ℝ) ^ C₁) ^ p := by positivity
            calc (2 * (e₀ ^ 2)⁻¹) ^ p * max Cp 0 * ((W : ℝ) ^ C₁) ^ p ≤
                (2 * (e₀ ^ 2)⁻¹) ^ p * (max Cp 0 + 1) ^ p * ((W : ℝ) ^ C₁) ^ p := by gcongr
              _ = B ^ p := by rw [hB, mul_pow (2 * (e₀ ^ 2)⁻¹ * (max Cp 0 + 1)), mul_pow (2 * (e₀ ^ 2)⁻¹)]
  have hL2 := lemmaNOffset_L2 (gammaG g / W) hσ2 hq henv0 hδ
    (fun s : S' => fun r x => pairErrField g E (mRoot g L E) W L r x s) (fun s => hY s) hu φ hφ
    hCφ p hp hB0 key
  refine ⟨hL2.1, hL2.2.trans (le_of_eq ?_)⟩
  have hc : (0 : ℝ) ≤ ((Fintype.card S' : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / p)) ^ 2 =
      ((Fintype.card S' : ℕ) : ℝ) ^ ((2 : ℝ) / p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc]
    congr 1
    push_cast
    ring
  rw [← h2]
  ring

end OffSet


section AtW

open scoped Matrix.Norms.L2Operator

/-- The resolvent along the flow at the scaled coordinates. -/
private theorem lemmaN_flowG_eq (g E : ℝ) (W L : ℕ) {u : ℝ} (hu : 0 ≤ u) (ω : Ω W L) :
    flowG W ⟨g, E, L, u⟩ ω = resolventMat (blockSlice W L (Ag g L ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ)) (Real.sqrt (u * (gammaG g / W)) • ω))
      (zChar g E (mRoot g L E) u) := by
  unfold flowG
  rw [lemmaN_flowH_eq g W L hu]

/-- The mixed-pair error along the flow at the scaled coordinates. -/
private theorem lemmaN_flowErr_eq (g E : ℝ) (W L : ℕ) {u : ℝ} (hu : 0 ≤ u) (l : Fin L × Fin L)
    (ω : Ω W L) :
    flowErr W ⟨g, E, L, u⟩ ![l.1, l.2] ![true, false] ω =
      pairErrField g E (mRoot g L E) W L u (Real.sqrt (u * (gammaG g / W)) • ω) l :=
  flowErr_eq_pairErrField W ⟨g, E, L, u⟩ hu l.1 l.2 ω

/-- The good events at a time `u` in the scaled coordinates: the Step 1 envelopes with loss `ω`
and the weighted sampling at `(u, v)`. -/
private def lemmaNGood (g E : ℝ) (W L : ℕ) (u R ω Cw cpN θ F₁ ℓv : ℝ) (S₀ : Finset (Fin L × Fin L))
    (y : Ω W L) : Prop :=
  (∀ l : Fin L × Fin L, ‖blockOf (resolventMat (blockSlice W L (Ag g L ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ)) y) (zChar g E (mRoot g L E) u)) l.1 l.2‖ ≤
      ω * (W * R * zetaProp g W L u)) ∧
  (∀ l : Fin L × Fin L, blockHS2 (resolventMat (blockSlice W L (Ag g L ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ)) y) (zChar g E (mRoot g L E) u)) l.1 l.2 ≤
      ω * ((W : ℝ) ^ 2 * R * zetaProp g W L u)) ∧
  (∀ c : Fin L, ‖blockTr (resolventMat (blockSlice W L (Ag g L ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ)) y) (zChar g E (mRoot g L E) u) -
      dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c‖ ≤
      ω * (R ^ 2 * zetaProp g W L u)) ∧
  (∀ l : Fin L × Fin L, ‖pairErrField g E (mRoot g L E) W L u y l‖ /
      weightFn cpN θ F₁ W ℓv (cycDist l.1 l.2) ≤
    Cw * (⨆ s : S₀, ‖pairErrField g E (mRoot g L E) W L u y s‖ /
      weightFn cpN θ F₁ W ℓv (cycDist s.1.1 s.1.2)) + (W : ℝ) ^ (-4 : ℝ))

/-- The bad events in the scaled coordinates are the failures of the four inputs. -/
private theorem lemmaN_bad_measure (g E : ℝ) (W L : ℕ) {u : ℝ} (hu : 0 ≤ u) (R ω Cw cpN θ F₁ ℓv : ℝ)
    (S₀ : Finset (Fin L × Fin L)) {δ₁ : ℝ}
    (hop : μ W L {x | ∃ l : Fin L × Fin L, ω * (W * R * zetaProp g W L u) <
      ‖((‖blockOf (flowG W ⟨g, E, L, u⟩ x) l.1 l.2‖ : ℝ) : ℂ)‖} ≤ ENNReal.ofReal δ₁)
    (hhs : μ W L {x | ∃ l : Fin L × Fin L, ω * ((W : ℝ) ^ 2 * R * zetaProp g W L u) <
      ‖((blockHS2 (flowG W ⟨g, E, L, u⟩ x) l.1 l.2 : ℝ) : ℂ)‖} ≤ ENNReal.ofReal δ₁)
    (havg : μ W L {x | ∃ c : Fin L, ω * (R ^ 2 * zetaProp g W L u) <
      ‖blockTr (flowG W ⟨g, E, L, u⟩ x - flowM W ⟨g, E, L, u⟩) c c‖} ≤ ENNReal.ofReal δ₁)
    (hsw : SampleBound (μ W L)
      (fun ab x => flowErr W ⟨g, E, L, u⟩ ![ab.1, ab.2] ![true, false] x)
      (fun ab => weightFn cpN θ F₁ W ℓv (cycDist ab.1 ab.2)) S₀ Cw ((W : ℝ) ^ (-4 : ℝ)) δ₁) :
    stdGauss (Fin L × Fin W × Fin W)
      {x | Real.sqrt (u * (gammaG g / W)) • x ∈
        {y | ¬ lemmaNGood g E W L u R ω Cw cpN θ F₁ ℓv S₀ y}} ≤ ENNReal.ofReal (4 * δ₁) := by
  set sc := Real.sqrt (u * (gammaG g / W)) with hsc
  have hsub : {x : Fin L × Fin W × Fin W → ℝ | sc • x ∈
      {y | ¬ lemmaNGood g E W L u R ω Cw cpN θ F₁ ℓv S₀ y}} ⊆
      (({x | ∃ l : Fin L × Fin L, ω * (W * R * zetaProp g W L u) <
        ‖((‖blockOf (flowG W ⟨g, E, L, u⟩ x) l.1 l.2‖ : ℝ) : ℂ)‖} ∪
      {x | ∃ l : Fin L × Fin L, ω * ((W : ℝ) ^ 2 * R * zetaProp g W L u) <
        ‖((blockHS2 (flowG W ⟨g, E, L, u⟩ x) l.1 l.2 : ℝ) : ℂ)‖}) ∪
      {x | ∃ c : Fin L, ω * (R ^ 2 * zetaProp g W L u) <
        ‖blockTr (flowG W ⟨g, E, L, u⟩ x - flowM W ⟨g, E, L, u⟩) c c‖}) ∪
      {x | ∃ l : Fin L × Fin L, Cw * (⨆ s : S₀, ‖flowErr W ⟨g, E, L, u⟩ ![s.1.1, s.1.2] ![true, false] x‖ /
          weightFn cpN θ F₁ W ℓv (cycDist s.1.1 s.1.2)) + (W : ℝ) ^ (-4 : ℝ) <
        ‖flowErr W ⟨g, E, L, u⟩ ![l.1, l.2] ![true, false] x‖ /
          weightFn cpN θ F₁ W ℓv (cycDist l.1 l.2)} := by
    intro x hx
    simp only [Set.mem_setOf_eq, lemmaNGood, not_and_or, not_forall, not_le] at hx
    have eG := lemmaN_flowG_eq g E W L hu x
    have eE : ∀ l : Fin L × Fin L, flowErr W ⟨g, E, L, u⟩ ![l.1, l.2] ![true, false] x =
        pairErrField g E (mRoot g L E) W L u (sc • x) l := fun l =>
      lemmaN_flowErr_eq g E W L hu l x
    rcases hx with ⟨l, hl⟩ | ⟨l, hl⟩ | ⟨c, hc⟩ | ⟨l, hl⟩
    · left; left; left
      refine ⟨l, ?_⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), eG]
      exact hl
    · left; left; right
      refine ⟨l, ?_⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by unfold blockHS2; positivity), eG]
      exact hl
    · left; right
      refine ⟨c, ?_⟩
      rw [eG]
      exact hc
    · right
      refine ⟨l, ?_⟩
      simp only [eE]
      exact hl
  calc stdGauss (Fin L × Fin W × Fin W) {x | sc • x ∈
        {y | ¬ lemmaNGood g E W L u R ω Cw cpN θ F₁ ℓv S₀ y}}
      ≤ μ W L _ := measure_mono hsub
    _ ≤ ENNReal.ofReal δ₁ + ENNReal.ofReal δ₁ + ENNReal.ofReal δ₁ + ENNReal.ofReal δ₁ := by
        refine (measure_union_le _ _).trans (add_le_add ?_ hsw)
        refine (measure_union_le _ _).trans (add_le_add ?_ havg)
        exact (measure_union_le _ _).trans (add_le_add hop hhs)
    _ ≤ ENNReal.ofReal (4 * δ₁) := by
        rcases le_or_gt 0 δ₁ with hδ | hδ
        · rw [← ENNReal.ofReal_add hδ hδ, ← ENNReal.ofReal_add (by linarith) hδ,
            ← ENNReal.ofReal_add (by linarith) hδ]
          exact le_of_eq (by congr 1; ring)
        · rw [ENNReal.ofReal_of_nonpos hδ.le]; simp

end AtW


section AtWHelpers

/-- `1 - u ≤ R(1 - v)` for `s ≤ u`, `v ≤ t`, `R = (1-s)/(1-t)`. -/
private theorem lemmaN_h4 {s t u v : ℝ} (hsu : s ≤ u) (huv : u ≤ v) (hvt : v ≤ t) (ht : t < 1) :
    1 - u ≤ (1 - s) / (1 - t) * (1 - v) := by
  have h1t : 0 < 1 - t := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1t]
  have hs1 : 0 ≤ 1 - s := by linarith
  have h1 : (1 - u) * (1 - t) ≤ (1 - s) * (1 - t) := by
    apply mul_le_mul_of_nonneg_right _ h1t.le; linarith
  have h2 : (1 - s) * (1 - t) ≤ (1 - s) * (1 - v) := by
    apply mul_le_mul_of_nonneg_left _ hs1; linarith
  linarith

/-- `1 ≤ (1-s)/(1-t)` for `s ≤ t < 1`. -/
private theorem lemmaN_R_ge {s t : ℝ} (hst : s ≤ t) (ht : t < 1) : 1 ≤ (1 - s) / (1 - t) := by
  rw [le_div_iff₀ (by linarith)]; linarith

/-- The kernel constant: `κ_K = (1-u)⁻¹(1 + c_pK) + 2(L/ℓ_u)W^{F-A} ≤ (1.001 + 2W⁻²)(1-u)⁻¹`. -/
private theorem lemmaN_kappaK {W : ℕ} (hW : 1 ≤ W) {u Lr ℓu RC F₁ A kE : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hkE : kE ≤ 1 / 1000) (hA : A = F₁ + RC + 2) (hℓ : 0 < ℓu) (hL0 : 0 ≤ Lr)
    (hbud : Lr / ℓu ≤ (W : ℝ) ^ RC) :
    (1 - u)⁻¹ * (1 + kE) + 2 * Lr / ℓu * (W : ℝ) ^ (F₁ - A) ≤
      (1.001 + 2 / (W : ℝ) ^ 2) * (1 - u)⁻¹ := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have heu : 0 < 1 - u := by linarith
  have h1u : 1 ≤ (1 - u)⁻¹ := by
    rw [le_inv_comm₀ one_pos heu, inv_one]; linarith
  have e : (W : ℝ) ^ RC * (W : ℝ) ^ (F₁ - A) = ((W : ℝ) ^ 2)⁻¹ := by
    rw [← Real.rpow_add hW0, hA, show RC + (F₁ - (F₁ + RC + 2)) = -2 by ring,
      Real.rpow_neg hW0.le]
    norm_cast
  have hrem : 2 * Lr / ℓu * (W : ℝ) ^ (F₁ - A) ≤ 2 / (W : ℝ) ^ 2 := by
    calc 2 * Lr / ℓu * (W : ℝ) ^ (F₁ - A) = 2 * (Lr / ℓu * (W : ℝ) ^ (F₁ - A)) := by ring
      _ ≤ 2 * ((W : ℝ) ^ RC * (W : ℝ) ^ (F₁ - A)) := by gcongr
      _ = 2 / (W : ℝ) ^ 2 := by rw [e]; ring
  have h0 : 0 ≤ 2 / (W : ℝ) ^ 2 := by positivity
  have h2 : 2 / (W : ℝ) ^ 2 ≤ 2 / (W : ℝ) ^ 2 * (1 - u)⁻¹ := le_mul_of_one_le_right h0 h1u
  have h3 : (1 - u)⁻¹ * (1 + kE) ≤ (1 - u)⁻¹ * 1.001 :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc (1 - u)⁻¹ * (1 + kE) + 2 * Lr / ℓu * (W : ℝ) ^ (F₁ - A) ≤
      (1 - u)⁻¹ * 1.001 + 2 / (W : ℝ) ^ 2 * (1 - u)⁻¹ := by linarith
    _ = (1.001 + 2 / (W : ℝ) ^ 2) * (1 - u)⁻¹ := by ring

/-- `X ≤ J(1 + 2β)` gives `X ≤ ω¹⁰⁰P` for `J = ω¹⁰⁰P/(2C_w(1+β))`. -/
private theorem lemmaN_XP {X ω P Cw β : ℝ} (hCw : 1 ≤ Cw) (hβ : 0 < β) (hωP : 0 ≤ ω ^ 100 * P)
    (hX : X ≤ ω ^ 100 * P / (2 * Cw * (1 + β)) * (1 + 2 * β)) : X ≤ ω ^ 100 * P := by
  refine hX.trans ?_
  have h1 : (1 + 2 * β) ≤ 2 * Cw * (1 + β) := by nlinarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- The near-pair tail condition `L √(K₀ ε_w) ≤ ℓ_v` from its uniform form. -/
private theorem lemmaN_Lr {W : ℕ} (hW : 1 ≤ W) {Lr ℓv ω P R C' Cw X ζu ζv εw : ℝ} (hL0 : 0 ≤ Lr)
    (hℓv : 0 < ℓv) (hω : 2 ≤ ω) (hR : 1 ≤ R) (hP : 0 ≤ P) (hC' : 0 ≤ C') (hCw : 1 ≤ Cw)
    (hCwω : 2 * Cw ≤ ω) (hX0 : 0 ≤ X) (hXP : X ≤ ω ^ 100 * P) (hζu : (2 * (W : ℝ))⁻¹ ≤ ζu)
    (hζv0 : 0 ≤ ζv) (hζv1 : ζv ≤ 1) (hεw : 0 ≤ εw)
    (hLr : (Lr / ℓv) ^ 2 * (ω ^ 2 + (C' + ω * (ω ^ 100 * P)) * (4 * (W : ℝ) ^ 2)) * εw ≤ 1) :
    Lr * Real.sqrt (max (ω ^ 2) ((C' + Cw * (1 + 1 / (W : ℝ)) * X) * ζv ^ 2 /
      (ω * R * ζu) ^ 2) * εw) ≤ ℓv := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hω0 : 0 < ω := by linarith
  have hζu0 : 0 < ζu := lt_of_lt_of_le (by positivity) hζu
  have hCwW : Cw * (1 + 1 / (W : ℝ)) ≤ ω := by
    have : 1 / (W : ℝ) ≤ 1 := by rw [div_le_one hW0]; linarith
    nlinarith
  have hΛ : C' + Cw * (1 + 1 / (W : ℝ)) * X ≤ C' + ω * (ω ^ 100 * P) := by
    have := mul_le_mul hCwW hXP hX0 hω0.le
    linarith
  have hden : (4 * (W : ℝ) ^ 2)⁻¹ ≤ (ω * R * ζu) ^ 2 := by
    have h1 : (2 * (W : ℝ))⁻¹ ≤ ω * R * ζu := by
      have : 1 ≤ ω * R := by nlinarith
      calc (2 * (W : ℝ))⁻¹ ≤ ζu := hζu
        _ = 1 * ζu := (one_mul _).symm
        _ ≤ ω * R * ζu := mul_le_mul_of_nonneg_right this hζu0.le
    have := pow_le_pow_left₀ (by positivity) h1 2
    calc (4 * (W : ℝ) ^ 2)⁻¹ = ((2 * (W : ℝ))⁻¹) ^ 2 := by field_simp; ring
      _ ≤ _ := this
  have hn : 0 ≤ C' + Cw * (1 + 1 / (W : ℝ)) * X := by positivity
  have hp : 0 < (ω * R * ζu) ^ 2 := by positivity
  have hmax : max (ω ^ 2) ((C' + Cw * (1 + 1 / (W : ℝ)) * X) * ζv ^ 2 / (ω * R * ζu) ^ 2) ≤
      ω ^ 2 + (C' + ω * (ω ^ 100 * P)) * (4 * (W : ℝ) ^ 2) := by
    have hB : 0 ≤ (C' + ω * (ω ^ 100 * P)) * (4 * (W : ℝ) ^ 2) := by positivity
    refine max_le (by linarith) ?_
    have hζv2 : ζv ^ 2 ≤ 1 := by nlinarith
    rw [div_le_iff₀ hp]
    have h4 : 1 ≤ (4 * (W : ℝ) ^ 2) * (ω * R * ζu) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℝ) ≤ 4 * (W : ℝ) ^ 2)
      rwa [mul_inv_cancel₀ (by positivity)] at this
    have hω2 : 0 ≤ ω ^ 2 * (ω * R * ζu) ^ 2 := by positivity
    calc (C' + Cw * (1 + 1 / (W : ℝ)) * X) * ζv ^ 2 ≤ (C' + ω * (ω ^ 100 * P)) * 1 := by
          gcongr
      _ ≤ (C' + ω * (ω ^ 100 * P)) * ((4 * (W : ℝ) ^ 2) * (ω * R * ζu) ^ 2) := by
          gcongr
      _ ≤ _ := by nlinarith
  have hsq : Lr ^ 2 * (max (ω ^ 2) ((C' + Cw * (1 + 1 / (W : ℝ)) * X) * ζv ^ 2 /
      (ω * R * ζu) ^ 2) * εw) ≤ ℓv ^ 2 := by
    have h1 : Lr ^ 2 * ((ω ^ 2 + (C' + ω * (ω ^ 100 * P)) * (4 * (W : ℝ) ^ 2)) * εw) ≤ ℓv ^ 2 := by
      have := hLr
      rw [div_pow] at this
      have e : Lr ^ 2 / ℓv ^ 2 * (ω ^ 2 + (C' + ω * (ω ^ 100 * P)) * (4 * (W : ℝ) ^ 2)) *
          εw = Lr ^ 2 * ((ω ^ 2 + (C' + ω * (ω ^ 100 * P)) * (4 * (W : ℝ) ^ 2)) * εw) /
            ℓv ^ 2 := by ring
      rw [e, div_le_one (by positivity)] at this
      exact this
    refine le_trans ?_ h1
    gcongr
  calc Lr * Real.sqrt (max (ω ^ 2) ((C' + Cw * (1 + 1 / (W : ℝ)) * X) * ζv ^ 2 /
        (ω * R * ζu) ^ 2) * εw) =
      Real.sqrt (Lr ^ 2 * (max (ω ^ 2) ((C' + Cw * (1 + 1 / (W : ℝ)) * X) * ζv ^ 2 /
        (ω * R * ζu) ^ 2) * εw)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hL0]
    _ ≤ Real.sqrt (ℓv ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ℓv := Real.sqrt_sq hℓv.le

/-- The long primitive pairs at the earlier time against the terminal weight. -/
private theorem lemmaN_prim_le {W : ℕ} (hW : 1 ≤ W) {cpN θ F₁ ℓu ℓv ζu ζv C' d P : ℝ} (hcpN : 0 ≤ cpN)
    (hθ : 0 ≤ θ) (hℓu : 0 < ℓu) (hℓuv : ℓu ≤ ℓv) (hζu : 0 ≤ ζu) (hζuv : ζu ≤ ζv) (hC' : 0 ≤ C')
    (hd : 0 ≤ d) (hP : P ≤ C' * ζu ^ 2 * weightFn cpN θ F₁ W ℓu d) :
    P ≤ C' * ζv ^ 2 * weightFn cpN θ F₁ W ℓv d := by
  have h1 : ζu ^ 2 ≤ ζv ^ 2 := pow_le_pow_left₀ hζu hζuv 2
  have h2 : weightFn cpN θ F₁ W ℓu d ≤ weightFn cpN θ F₁ W ℓv d :=
    lemmaN_weight_mono_ell hcpN hθ hℓu hℓuv hd
  have h3 : 0 ≤ weightFn cpN θ F₁ W ℓu d := (lemmaN_weight_pos cpN θ F₁ hW _ _).le
  refine hP.trans ?_
  gcongr

/-- The initial value of the surrogate on the event of the one-step input: `X_s ≤ 2δ_s`. -/
private theorem lemmaN_init_le {S : Type*} [Fintype S] {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ}
    (henv : ∀ s, 0 < env s) {δs ω : ℝ} (hδs : 0 < δs) (hω : 0 ≤ ω) (hωδ : 1.001 * ω ≤ 0.999 * δs)
    (hS : (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) ≤ 1.001) (y : S → ℂ)
    (hy : ∀ s, ‖y s‖ ≤ ω * env s) : lqSurr q env δs y ≤ 2 * δs := by
  have hsup : (⨆ s, ‖y s‖ / env s) ≤ ω :=
    Real.iSup_le (fun s => by rw [div_le_iff₀ (henv s)]; exact hy s) hω
  have h1 := lqSurr_le hq henv hδs y
  have h0 : 0 ≤ (⨆ s, ‖y s‖ / env s) + δs := by
    have : 0 ≤ ⨆ s, ‖y s‖ / env s := Real.iSup_nonneg fun s => by have := henv s; positivity
    linarith
  calc lqSurr q env δs y ≤ (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) *
        ((⨆ s, ‖y s‖ / env s) + δs) := h1
    _ ≤ 1.001 * (ω + δs) := by
        gcongr
    _ ≤ 2 * δs := by linarith

/-- The final step: off the event `X_v ≥ J(1+β)` and on the weighted sampling event at `(v, v)`,
every mixed-pair error is at most `W^ε R^M ζ_v² w_v`. -/
private theorem lemmaN_final_le {S S₀ : Type*} [Fintype S] (f : S₀ → S) {q : ℕ} (hq : 1 ≤ q)
    {env : S → ℝ} (henv : ∀ s, 0 < env s) {δs Cw J β ζv wl Dl Wm4 Wε P ω : ℝ} (hδs : 0 < δs)
    (y : S → ℂ) (yl : S₀ → ℂ) (wf : S₀ → ℝ) (hwf : ∀ s, 0 < wf s)
    (hyl : ∀ s, yl s = y (f s)) (henvf : ∀ s, env (f s) = ζv ^ 2 * wf s) (hζv : 0 < ζv)
    (hCw : 1 ≤ Cw) (hX : lqSurr q env δs y < J * (1 + β))
    (hJ : Cw * (J * (1 + β)) = ω ^ 100 * P / 2) (hwl : 0 < wl)
    (hsw : Dl / wl ≤ Cw * (⨆ s, ‖yl s‖ / wf s) + Wm4)
    (hW4 : Wm4 ≤ ζv ^ 2 * (ω ^ 100 * P / 2)) (hεω : ω ^ 100 * P * ζv ^ 2 * wl ≤ Wε) :
    Dl ≤ Wε := by
  set X := lqSurr q env δs y with hXdef
  have hX0 : 0 ≤ X := by simp only [hXdef, lqSurr]; positivity
  have hsup : (⨆ s, ‖yl s‖ / wf s) ≤ ζv ^ 2 * X := by
    refine Real.iSup_le (fun s => ?_) (by positivity)
    have h1 := lqSurr_label_le hq henv hδs y (f s)
    rw [← hXdef, henvf s, div_le_iff₀ (by have := hwf s; positivity)] at h1
    rw [hyl s, div_le_iff₀ (hwf s)]
    calc ‖y (f s)‖ ≤ X * (ζv ^ 2 * wf s) := h1
      _ = ζv ^ 2 * X * wf s := by ring
  rw [div_le_iff₀ hwl] at hsw
  have hCwX : Cw * X ≤ ω ^ 100 * P / 2 := by
    rw [← hJ]; exact mul_le_mul_of_nonneg_left hX.le (by linarith)
  calc Dl ≤ (Cw * (⨆ s, ‖yl s‖ / wf s) + Wm4) * wl := hsw
    _ ≤ (Cw * (ζv ^ 2 * X) + ζv ^ 2 * (ω ^ 100 * P / 2)) * wl := by
        gcongr
    _ = (ζv ^ 2 * (Cw * X) + ζv ^ 2 * (ω ^ 100 * P / 2)) * wl := by ring
    _ ≤ (ζv ^ 2 * (ω ^ 100 * P / 2) + ζv ^ 2 * (ω ^ 100 * P / 2)) * wl := by gcongr
    _ = ω ^ 100 * P * ζv ^ 2 * wl := by ring
    _ ≤ Wε := hεω

/-- Positivity of the off-diagonal rate and of the Perron root of the multiplicative system. -/
private theorem lemmaN_rates_pos {ε β κ bΓ : ℝ} (r : ℕ) (hr : 1 ≤ r) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hβ : 0 < β) (hκ : 0 < κ) (hbΓ : 0 ≤ bΓ) :
    0 < rateMulA12 ε β κ bΓ r ∧ 0 < perronMul ε β κ bΓ r := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hA12 : 0 < rateMulA12 ε β κ bΓ r := by
    unfold rateMulA12 rateA12 rateMulC12
    have : 0 < 1 - ε := by linarith
    have h1 : 0 < (1 + 2 * β) ^ (2 * r + 1) * (1 - ε)⁻¹ * κ / β := by positivity
    have h2 : 0 ≤ (2 * r * (1 + 2 * β) ^ (2 * r + 1) * (1 - ε)⁻¹ / β +
        3 * (1 + 2 * β) ^ (2 * r + 2) / (4 * ε * (1 - ε) * β ^ 2)) * bΓ := by positivity
    linarith
  have hA11 : 0 < rateMulA11 κ bΓ r := by
    unfold rateMulA11
    have : 0 ≤ (r : ℝ) * (2 * r - 1) * bΓ := by
      have : (0 : ℝ) ≤ 2 * r - 1 := by linarith
      positivity
    have : 0 < 2 * (r : ℝ) * κ := by positivity
    linarith
  refine ⟨hA12, ?_⟩
  unfold perronMul
  have := Real.sqrt_nonneg ((rateMulA11 κ bΓ r / 2) ^ 2 + rateMulA12 ε β κ bΓ r *
    rateMulA21 ε β κ bΓ)
  linarith

end AtWHelpers


section AtW2

open scoped Matrix.Norms.L2Operator

/-- The total failure probability of the mixed pair at the terminal time, at fixed `W`. -/
private def lemmaNTotal (Cw ω P δs δ₁ bΓ K : ℝ) (r : ℕ) (s v : ℝ) : ℝ :=
  (perronMul (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) bΓ r /
      rateMulA12 (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) bΓ r) *
    (((1 - s) / (1 - v)) ^ perronMul (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) bΓ r *
      ((2 * δs / (ω ^ 100 * P / (2 * Cw * (1 + 1 / (2 * r))))) ^ (2 * r) +
        ((1 + 2 * (1 / (2 * r))) ^ (2 * r) +
          rateMulA12 (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) bΓ r /
            perronMul (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) bΓ r) * (4 * δ₁) +
        (1 + rateMulA12 (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) bΓ r /
            perronMul (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) bΓ r) *
          (K * Real.sqrt (4 * δ₁)))) + δ₁

set_option maxHeartbeats 4000000 in
/-- The mixed-pair bound at fixed `W` on an admissible step with `s < v`: the mixed-pair error at
the terminal time `v` exceeds `W^ε R^M ζ_v² w_v` with probability at most the total of the no-exit
lemma with multiplicative rates and of the weighted sampling at `(v, v)`. -/
private theorem lemmaN_atW (g E : ℝ) (W L : ℕ) (s t v : ℝ) (hW : 4 ≤ W) (hL : 3 ≤ L) (hg : 0 ≤ g)
    (hroot : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E))
    (hs : 1 / 2 ≤ s) (hsv : s < v) (hvt : v ≤ t) (ht : t < 1)
    {Cw cp cpN θ F F₁ ε ω M C₀ c₀ A RC C' Cc lH εw bΓ δ₁ Cp C₁ : ℝ} {r q p : ℕ}
    (hCw : 1 ≤ Cw) (hCc0 : 0 ≤ Cc) (hcpN : 0 < cpN) (hcpNcp : cpN ≤ cp) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (hF : 0 < F) (hFF : F ≤ F₁) (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hcpc : cpN ≤ c₀ / 2)
    (hkE : cpN * kerExcess C₀ c₀ ≤ 1 / 1000) (hA : A = F₁ + RC + 2)
    (hr : 1 ≤ r) (hq : 1 ≤ q) (hp : 2 ≤ p) (hδ₁ : 0 ≤ δ₁) (hbΓ0 : 0 ≤ bΓ)
    (S₀ S' : Finset (Fin L × Fin L)) (hS₀ : S₀ ⊆ S') (hS'ne : S'.Nonempty)
    (hS : ((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / (2 * q)) ≤ 1.001)
    -- regime facts on `[s, v]`
    (hker : ∀ u ∈ Set.Icc s v, ∀ a b : Fin L,
      mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E (mRoot g L E))) u a b ≤
        C₀ / ((1 - u) * ellProp g L u) * Real.exp (-(c₀ * cycDist a b / ellProp g L u)) +
          (ellProp g L u)⁻¹ * (W : ℝ) ^ (-A))
    (hlong : ∀ u ∈ Set.Icc s v, ∀ a b : Fin L,
      ellProp g L u * Real.log W ^ ((3 : ℝ) / 2) ≤ cycDist a b →
        ‖primLoop g W L E (mRoot g L E) u ![a, b] ![true, false]‖ ≤
          C' * zetaProp g W L u ^ 2 * weightFn cpN θ F₁ W (ellProp g L u) (cycDist a b))
    (hbud : (L : ℝ) / ellProp g L s ≤ (W : ℝ) ^ RC)
    (hmom : ∀ u ∈ Set.Icc s v, ∀ a b : Fin L,
      Integrable (fun x => ‖blockGen W L (gammaG g) (fun r N =>
          resLoop g E (mRoot g L E) ![a, b] ![true, false] r N -
            primLoop g W L E (mRoot g L E) r ![a, b] ![true, false]) u
          (flowH g W L u x)‖ ^ p) (μ W L) ∧
      ∫ x, ‖blockGen W L (gammaG g) (fun r N =>
          resLoop g E (mRoot g L E) ![a, b] ![true, false] r N -
            primLoop g W L E (mRoot g L E) r ![a, b] ![true, false]) u
          (flowH g W L u x)‖ ^ p ∂(μ W L) ≤ Cp * (W : ℝ) ^ (C₁ * p) ∧
      Integrable (fun x => ‖blockGamma W L (gammaG g)
          (resLoop g E (mRoot g L E) ![a, b] ![true, false] u)
          (resLoop g E (mRoot g L E) ![a, b] ![true, false] u)
          (flowH g W L u x)‖ ^ p) (μ W L) ∧
      ∫ x, ‖blockGamma W L (gammaG g)
          (resLoop g E (mRoot g L E) ![a, b] ![true, false] u)
          (resLoop g E (mRoot g L E) ![a, b] ![true, false] u)
          (flowH g W L u x)‖ ^ p ∂(μ W L) ≤ Cp * (W : ℝ) ^ (C₁ * p))
    (hconv : ∀ x y : Fin L,
      ∑ c, weightFn cpN θ F₁ W (ellProp g L v) (cycDist x c) *
          weightFn cpN θ F₁ W (ellProp g L v) (cycDist c y) ≤
        Cc * ellProp g L v * weightFn cpN θ F₁ W (ellProp g L v) (cycDist x y) ∧
      ∑ c, Real.sqrt (weightFn cpN θ F₁ W (ellProp g L v) (cycDist x c) *
          weightFn cpN θ F₁ W (ellProp g L v) (cycDist c y)) ≤
        Cc * ellProp g L v * Real.sqrt (weightFn cpN θ F₁ W (ellProp g L v) (cycDist x y)))
    (hshort : ∀ x y : Fin L, (cycDist x y : ℝ) ≤ 2 * (ellProp g L v * Real.log W ^ ((3 : ℝ) / 2)) →
      ω⁻¹ ≤ weightFn cpN θ F₁ W (ellProp g L v) (cycDist x y))
    (hfar : ∀ x y : Fin L, ellProp g L v * lH < cycDist x y →
      weightFn cpN θ F₁ W (ellProp g L v) (cycDist x y) ≤ εw)
    -- the inputs at fixed `W`
    (hop : ∀ u ∈ Set.Ioo s v, μ W L {x | ∃ l : Fin L × Fin L,
      ω * (W * ((1 - s) / (1 - t)) * zetaProp g W L u) <
        ‖((‖blockOf (flowG W ⟨g, E, L, u⟩ x) l.1 l.2‖ : ℝ) : ℂ)‖} ≤ ENNReal.ofReal δ₁)
    (hhs : ∀ u ∈ Set.Ioo s v, μ W L {x | ∃ l : Fin L × Fin L,
      ω * ((W : ℝ) ^ 2 * ((1 - s) / (1 - t)) * zetaProp g W L u) <
        ‖((blockHS2 (flowG W ⟨g, E, L, u⟩ x) l.1 l.2 : ℝ) : ℂ)‖} ≤ ENNReal.ofReal δ₁)
    (havg : ∀ u ∈ Set.Ioo s v, μ W L {x | ∃ c : Fin L,
      ω * (((1 - s) / (1 - t)) ^ 2 * zetaProp g W L u) <
        ‖blockTr (flowG W ⟨g, E, L, u⟩ x - flowM W ⟨g, E, L, u⟩) c c‖} ≤ ENNReal.ofReal δ₁)
    (hsw : ∀ u, 1 / 2 ≤ u → u ≤ v → SampleBound (μ W L)
      (fun ab x => flowErr W ⟨g, E, L, u⟩ ![ab.1, ab.2] ![true, false] x)
      (fun ab => weightFn cpN θ F₁ W (ellProp g L v) (cycDist ab.1 ab.2)) S₀ Cw
      ((W : ℝ) ^ (-4 : ℝ)) δ₁)
    (hN1 : μ W L {x | ∃ ab : Fin L × Fin L, ω * (zetaProp g W L s ^ 2 *
        weightFn cp θ F₁ W (ellProp g L s) (cycDist ab.1 ab.2)) <
      ‖flowErr W ⟨g, E, L, s⟩ ![ab.1, ab.2] ![true, false] x‖} ≤ ENNReal.ofReal δ₁)
    -- numerics at `W`
    (hω : 2 ≤ ω) (hωε : ω ^ 100 ≤ (W : ℝ) ^ ε) (hCwω : 2 * Cw ≤ ω) (hCcω : Cc ≤ ω)
    (hC'0 : 0 ≤ C') (hC'ω : C' ≤ ω) (hlH : lH ≤ ω) (hlH32 : Real.log W ^ ((3 : ℝ) / 2) ≤ lH)
    (hεw : 0 ≤ εw) (hM4 : 4 ≤ M)
    (hRP : ((1 - s) / (1 - t)) ^ 3 * ((1 - s) / (1 - t)) ^ M * zetaProp g W L t * ω ^ 400 ≤ 1)
    (hR5 : ((1 - s) / (1 - t)) ^ 5 * zetaProp g W L t * ω ^ 400 ≤ 1)
    (hJ : 2 * (((1 - s) / (1 - t)) ^ 4 * ω ^ 25) ≤
      ω ^ 100 * ((1 - s) / (1 - t)) ^ M / (2 * Cw * (1 + 1 / (2 * r))))
    (hJ1 : 1 ≤ ω ^ 100 * ((1 - s) / (1 - t)) ^ M / (2 * Cw * (1 + 1 / (2 * r))))
    (hκ : 1.001 * (2 * (1.001 + 2 / (W : ℝ) ^ 2) * (Cw * (1 + 1 / (W : ℝ))) + 1 / (2 * ω)) +
      1.003 * q * (1 / (2 * ω)) ≤ 2 * (1 + 1 / 100) * Cw) (hbΓ : 1.003 * (1 / (2 * ω)) ≤ bΓ)
    (hLr : ((L : ℝ) / ellProp g L v) ^ 2 *
      (ω ^ 2 + (C' + ω * (ω ^ 100 * ((1 - s) / (1 - t)) ^ M)) * (4 * (W : ℝ) ^ 2)) * εw ≤ 1) :
    μ W L {x | ∃ ab : Fin L × Fin L, (W : ℝ) ^ ε * (((1 - s) / (1 - t)) ^ M *
        zetaProp g W L v ^ 2 * weightFn cpN θ F W (ellProp g L v) (cycDist ab.1 ab.2)) <
      ‖flowErr W ⟨g, E, L, v⟩ ![ab.1, ab.2] ![true, false] x‖} ≤
    ENNReal.ofReal (lemmaNTotal Cw ω (((1 - s) / (1 - t)) ^ M)
      (((1 - s) / (1 - t)) ^ 4 * ω ^ 25) δ₁ bΓ
      (lemmaNCutC (1 / 100) (1 / (2 * r)) r * (q + 2) *
        ((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / q) * ((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / p) *
        (2 * ((((2 * (W : ℝ))⁻¹) ^ 2 * (W : ℝ) ^ (-F₁)) ^ 2)⁻¹ * (max Cp 0 + 1) * (W : ℝ) ^ C₁))
      r s v) := by
  -- basic quantities
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hv1 : v < 1 := lt_of_le_of_lt hvt ht
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hL1 : 1 ≤ L := by omega
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hσ2 : 0 < gammaG g / W := div_pos hγ hW0
  have hω0 : 0 < ω := lt_of_lt_of_le (by norm_num) hω
  have hω1 : 1 ≤ ω := le_trans (by norm_num) hω
  have h1v : 0 < 1 - v := by linarith only [hv1]
  set R := (1 - s) / (1 - t) with hRdef
  have hR : 1 ≤ R := lemmaN_R_ge (by linarith only [hsv, hvt]) ht
  set P := R ^ M with hPdef
  have hP1 : 1 ≤ P := Real.one_le_rpow hR (by linarith only [hM4])
  have hP0 : 0 ≤ P := le_trans zero_le_one hP1
  set ℓv := ellProp g L v with hℓvdef
  set ζv := zetaProp g W L v with hζvdef
  set ζt := zetaProp g W L t with hζtdef
  obtain ⟨hℓv1, -, hℓvL, hζvW, hζvt, -, -⟩ :=
    scale_facts g hg W L hW1 hL1 v t (by linarith only [hs, hsv]) hvt ht
  obtain ⟨-, -, -, -, -, -, hΓv⟩ :=
    scale_facts g hg W L hW1 hL1 v v (by linarith only [hs, hsv]) le_rfl hv1
  obtain ⟨hℓs1, -, -, -, -, -, -⟩ :=
    scale_facts g hg W L hW1 hL1 s s hs0.le le_rfl (by linarith only [hsv, hv1])
  have hζv0 : 0 < ζv := lt_of_lt_of_le (by positivity) hζvW
  have hζt0 : 0 < ζt := lt_of_lt_of_le hζv0 hζvt
  have hζt1 : ζt ≤ 1 := by
    have h1 : 1 ≤ R ^ 5 * ω ^ 400 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR)
      (one_le_pow₀ hω1)
    by_contra h
    push Not at h
    have : R ^ 5 * ω ^ 400 < R ^ 5 * ζt * ω ^ 400 := by
      have h2 : R ^ 5 * ω ^ 400 * 1 < R ^ 5 * ω ^ 400 * ζt :=
        mul_lt_mul_of_pos_left h (by positivity)
      linarith only [h2]
    linarith only [this, hR5, h1]
  have hζv1 : ζv ≤ 1 := hζvt.trans hζt1
  set w : Fin L → Fin L → ℝ := fun x y => weightFn cpN θ F₁ W ℓv (cycDist x y) with hwdef
  have hF₁ : 0 ≤ F₁ := le_trans hF.le hFF
  have hℓv0 : 0 < ℓv := lt_of_lt_of_le one_pos hℓv1
  have hw0 : ∀ x y, 0 ≤ w x y := fun x y => (lemmaN_weight_pos cpN θ F₁ hW1 _ _).le
  have hw2 : ∀ x y, w x y ≤ 2 := fun x y =>
    lemmaN_weight_le_two hcpN.le hF₁ hW1 hℓv0 (Nat.cast_nonneg _)
  have hws : ∀ x y, w x y = w y x := fun x y => by simp only [hwdef, lemmaN_cycDist_comm x y]
  have hwmin0 : 0 < (W : ℝ) ^ (-F₁) := Real.rpow_pos_of_pos hW0 _
  have hwmin : ∀ x y, (W : ℝ) ^ (-F₁) ≤ w x y := fun x y => lemmaN_weight_ge cpN θ F₁ _ _
  set env : S' → ℝ := fun s => ζv ^ 2 * w s.1.1 s.1.2 with henvdef
  have henv : ∀ s, 0 < env s := fun s =>
    mul_pos (by positivity) (lt_of_lt_of_le hwmin0 (hwmin _ _))
  set δs := R ^ 4 * ω ^ 25 with hδsdef
  have hδs1 : 1 ≤ δs := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) (one_le_pow₀ hω1)
  have hδs0 : 0 < δs := lt_of_lt_of_le one_pos hδs1
  set X : ℝ → (Fin L × Fin W × Fin W → ℝ) → ℝ :=
    fun r y => lqSurr q env δs (fun s : S' => pairErrField g E (mRoot g L E) W L r y s) with hXdef
  have hX0 : ∀ r y, 0 ≤ X r y := fun r y => lemmaN_lqSurr_nonneg _ _ _ _
  set β : ℝ := 1 / (2 * r) with hβdef
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hβ0 : 0 < β := by positivity
  set J := ω ^ 100 * P / (2 * Cw * (1 + 1 / (2 * r))) with hJdef
  have hJ0 : 0 < J := lt_of_lt_of_le one_pos hJ1
  set κ := 2 * (1 + 1 / 100) * Cw with hκdef
  have hκ0 : 0 < κ := by positivity
  obtain ⟨ρ, hρ⟩ := exists_isRamp (1 / 100) (by norm_num) (by norm_num)
  -- the heat class
  have hY : ∀ ab : Fin L × Fin L,
      HeatClass (fun r x => pairErrField g E (mRoot g L E) W L r x ab) (-1 / 2) ((1 + v) / 2) :=
    fun ab => heatClass_pairErrField g E (mRoot g L E) W L hW1 hL hroot ab (by norm_num)
      (by linarith only [hv1])
  have hXc : HeatClass (fun r y => ((X r y : ℝ) : ℂ)) (-1 / 2) ((1 + v) / 2) :=
    heatClass_lqSurr hq henv hδs0 (fun s : S' => fun r x => pairErrField g E (mRoot g L E) W L r x s)
      (fun s => hY s)
  -- the bad sets
  set Bad : ℝ → Set (Fin L × Fin W × Fin W → ℝ) :=
    fun u => {y | ¬ lemmaNGood g E W L u R ω Cw cpN θ F₁ ℓv S₀ y} with hBad
  have hbad : ∀ u ∈ Set.Ioo s v, stdGauss (Fin L × Fin W × Fin W)
      {x | Real.sqrt (u * (gammaG g / W)) • x ∈ Bad u} ≤ ENNReal.ofReal (4 * δ₁) := fun u hu =>
    lemmaN_bad_measure g E W L (le_of_lt (lt_trans hs0 hu.1)) R ω Cw cpN θ F₁ ℓv S₀ (hop u hu)
      (hhs u hu) (havg u hu) (hsw u (le_trans hs hu.1.le) hu.2.le)
  -- the rates on the good sets
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg (by exact_mod_cast hW1)
  have hlH0 : 0 ≤ lH := le_trans (by positivity) hlH32
  have hrate : ∀ u ∈ Set.Ioo s v, ∀ y, y ∉ Bad u → X u y ≤ J * (1 + 2 * β) →
      |(coordGen (gammaG g / W) (fun t z => ((X t z : ℝ) : ℂ)) u y).re| ≤ κ * X u y / (1 - u) ∧
        (coordGamma (gammaG g / W) (fun z => ((X u z : ℝ) : ℂ)) (fun z => ((X u z : ℝ) : ℂ))
          y).re ≤ bΓ * X u y ^ 2 / (1 - u) := by
    intro u hu y hy hXJ
    have hsu : s < u := hu.1
    have huv : u < v := hu.2
    have hu0 : 0 ≤ u := le_of_lt (lt_trans hs0 hsu)
    have hu1 : u < 1 := lt_trans huv hv1
    simp only [hBad, Set.mem_setOf_eq, not_not] at hy
    obtain ⟨gop, ghs, gavg, gsw⟩ := hy
    obtain ⟨hℓu1, hℓuv, -, hζuW, hζuv, -, -⟩ :=
      scale_facts g hg W L hW1 hL1 u v hu0 huv.le hv1
    obtain ⟨-, hℓsu, -, -, -, -, -⟩ := scale_facts g hg W L hW1 hL1 s u hs0.le hsu.le hu1
    have hζu0 : 0 < zetaProp g W L u := lt_of_lt_of_le (by positivity) hζuW
    have hZ := lemmaN_zeta_sq_ratio g hg W L hW1 hL1 hu0 huv.le hv1
    have h4 : 1 - u ≤ R * (1 - v) := lemmaN_h4 hsu.le huv.le hvt ht
    -- the kernel row
    have hP0' : ∀ x y, 0 ≤ pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E (mRoot g L E)) x y :=
      by intro x y; simp only [pairP, Matrix.of_apply]; positivity
    have hProw : ∀ x, ∑ y, pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E (mRoot g L E)) x y
        = 1 := fun x => pairP_row_sum (hopB g) (gammaG g) hγ L hL1 E _ hroot x
    obtain ⟨hK0, hKrow⟩ := mixedKer_nonneg_row _ hP0' hProw u hu0 hu1
    have hkerrow : ∀ x y, ∑ c, mixedKer (pairP (gammaG g)
        (dysonMat (hopB g) (gammaG g) L E (mRoot g L E))) u x c * w c y ≤
        ((1 - u)⁻¹ * (1 + cpN * kerExcess C₀ c₀) +
          2 * L / ellProp g L u * (W : ℝ) ^ (F₁ - A)) * w x y := fun x y =>
      lemmaNRates_kernel W hW1 _ hu1 hC₀ hc₀ hcpN hcpc hθ (le_trans hθ2 (by norm_num)) hF₁ hℓu1
        hℓuv hK0 hKrow (hker u ⟨hsu.le, huv.le⟩) x y
    have hLu : (L : ℝ) / ellProp g L u ≤ (W : ℝ) ^ RC :=
      le_trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (lt_of_lt_of_le one_pos hℓs1) hℓsu)
        hbud
    have hκK := lemmaN_kappaK hW1 hu0 hu1 hkE hA (lt_of_lt_of_le one_pos hℓu1)
      (Nat.cast_nonneg L) hLu
    have hprim : ∀ x y, ℓv * Real.log W ^ ((3 : ℝ) / 2) < cycDist x y →
        ‖primLoop g W L E (mRoot g L E) u ![x, y] ![true, false]‖ ≤ C' * ζv ^ 2 * w x y := by
      intro x y hxy
      have hl : ellProp g L u * Real.log W ^ ((3 : ℝ) / 2) ≤ cycDist x y :=
        le_trans (mul_le_mul_of_nonneg_right hℓuv (by positivity)) hxy.le
      exact lemmaN_prim_le hW1 hcpN.le hθ.le (lt_of_lt_of_le one_pos hℓu1) hℓuv hζu0.le hζuv hC'0
        (Nat.cast_nonneg _) (hlong u ⟨hsu.le, huv.le⟩ x y hl)
    have hXP : X u y ≤ ω ^ 100 * P := lemmaN_XP hCw hβ0 (by positivity) hXJ
    have hLr' := lemmaN_Lr hW1 (Nat.cast_nonneg L) hℓv0 hω hR hP0 hC'0 hCw hCwω (hX0 u y) hXP
      hζuW hζv0.le hζv1 hεw hLr (X := X u y)
    have hΓ' : gammaG g * W * ℓv * ζv * (1 - v) = 1 := by
      rw [hΓv]; exact inv_mul_cancel₀ h1v.ne'
    exact lemmaN_surr_good g E (mRoot g L E) hW hL hroot S' S₀ hS₀ hS'ne hq hS hY
      ⟨by linarith only [hu0], by linarith only [huv, hv1]⟩ hu0 hu1 w hw0 hw2 hws hwmin0 hwmin
      (ω := ω) (R := R) (P := P) (ζu := zetaProp g W L u) (ζv := ζv) (ζt := ζt) (ev := 1 - v)
      (Cw := Cw) (Cc := Cc) (ℓv := ℓv) (h := ℓv * Real.log W ^ ((3 : ℝ) / 2))
      (H := ℓv * lH) (εw := εw) (C' := C') (lH := lH) (κ := κ) (bΓ := bΓ)
      hω hR hP0 hζu0 hζuv hζvt hζvW h1v h4 hZ hRP hR5 hΓ' hℓv1
      hCw hCwω hCc0 hCcω hC'0 hC'ω (by positivity) (mul_le_mul_of_nonneg_left hlH32 hℓv0.le) rfl
      hlH0 hlH hεw hκK hκ hbΓ hconv hkerrow hprim (fun x y hxy => hshort x y hxy) hfar y
      (fun x z => gop (x, z)) (fun x z => ghs (x, z)) gavg gsw hXP hLr'
  -- the off-set bound
  set e₀ : ℝ := ((2 * (W : ℝ))⁻¹) ^ 2 * (W : ℝ) ^ (-F₁) with he₀def
  have he₀ : 0 < e₀ := by positivity
  have he₀1 : e₀ ≤ 1 := by
    have h1 : ((2 * (W : ℝ))⁻¹) ^ 2 ≤ 1 := by
      have : (2 * (W : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
        have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
        linarith only [this])
      exact pow_le_one₀ (by positivity) this
    have h2 : (W : ℝ) ^ (-F₁) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hW1) (by linarith only [hF₁])
    calc e₀ ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have henv₀ : ∀ s, e₀ ≤ env s := fun s =>
    mul_le_mul (pow_le_pow_left₀ (by positivity) hζvW 2) (hwmin _ _) hwmin0.le (by positivity)
  set K := lemmaNCutC (1 / 100) (1 / (2 * r)) r * (q + 2) *
    ((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / q) * ((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / p) *
    (2 * (e₀ ^ 2)⁻¹ * (max Cp 0 + 1) * (W : ℝ) ^ C₁) with hKdef
  have hCcut : 0 ≤ lemmaNCutC (1 / 100) (1 / (2 * r)) r := by unfold lemmaNCutC; positivity
  have hK0 : 0 ≤ K := by
    have : 0 ≤ max Cp 0 := le_max_right _ _
    positivity
  have hL2 : ∀ u ∈ Set.Ioo s v, ∀ φ : ℝ → ℝ, (φ = cutPsi ρ J β r ∨ φ = cutPhi ρ J β) →
      MemLp (fun x => (coordGen (gammaG g / W) (fun t z => ((φ (X t z) : ℝ) : ℂ)) u
        (Real.sqrt (u * (gammaG g / W)) • x)).re) 2 (stdGauss (Fin L × Fin W × Fin W)) ∧
      ∫ x, ((coordGen (gammaG g / W) (fun t z => ((φ (X t z) : ℝ) : ℂ)) u
        (Real.sqrt (u * (gammaG g / W)) • x)).re) ^ 2 ∂(stdGauss (Fin L × Fin W × Fin W)) ≤
        K ^ 2 := by
    intro u hu φ hφ
    have hu0 : 0 ≤ u := le_of_lt (lt_trans hs0 hu.1)
    have huI : u ∈ Set.Ioo (-1 / 2 : ℝ) ((1 + v) / 2) :=
      ⟨by linarith only [hu0], by linarith only [hu.2, hv1]⟩
    have hmomu := hmom u ⟨hu.1.le, hu.2.le⟩
    rcases hφ with rfl | rfl
    · exact lemmaN_offset_L2 g E hW1 S' hq he₀ he₀1 henv₀ hδs1 hu0 hY huI _
        (cutPsi_C2b hρ hJ0 hβ0 r) (fun x => (lemmaN_cut_bounds hρ hJ1 hβ0 r hr x).1) p hp hmomu
    · exact lemmaN_offset_L2 g E hW1 S' hq he₀ he₀1 henv₀ hδs1 hu0 hY huI _
        (cutPhi_C2b hρ hJ0 hβ0) (fun x => (lemmaN_cut_bounds hρ hJ1 hβ0 r hr x).2) p hp hmomu
  -- the initial value
  obtain ⟨-, hℓsv, -, -, hζsv, -, -⟩ :=
    scale_facts g hg W L hW1 hL1 s v hs0.le hsv.le hv1
  have hωδ : 1.001 * ω ≤ 0.999 * δs := by
    have h1 : 2 ^ 24 * ω ≤ ω ^ 25 := by
      have : (2 : ℝ) ^ 24 ≤ ω ^ 24 := pow_le_pow_left₀ (by norm_num) hω 24
      calc (2 : ℝ) ^ 24 * ω ≤ ω ^ 24 * ω := mul_le_mul_of_nonneg_right this hω0.le
        _ = ω ^ 25 := by ring
    have h2 : ω ^ 25 ≤ δs := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hR)
    nlinarith only [h1, h2, hω0]
  have hinit : stdGauss (Fin L × Fin W × Fin W)
      {x | 2 * δs < X s (Real.sqrt (s * (gammaG g / W)) • x)} ≤ ENNReal.ofReal (4 * δ₁) := by
    refine le_trans (measure_mono ?_) (hN1.trans (ENNReal.ofReal_le_ofReal
      (by linarith only [hδ₁])))
    intro x hx
    by_contra hcon
    simp only [Set.mem_setOf_eq, not_exists, not_lt] at hcon
    have hle : X s (Real.sqrt (s * (gammaG g / W)) • x) ≤ 2 * δs := by
      refine lemmaN_init_le hq henv hδs0 hω0.le hωδ hS _ (fun s' => ?_)
      rw [← lemmaN_flowErr_eq g E W L hs0.le s'.1 x]
      refine (hcon s'.1).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hω0.le
      have hws1 : weightFn cp θ F₁ W (ellProp g L s) (cycDist s'.1.1 s'.1.2) ≤
          weightFn cpN θ F₁ W (ellProp g L s) (cycDist s'.1.1 s'.1.2) :=
        lemmaN_weight_anti_c hcpNcp (lt_of_lt_of_le one_pos hℓs1) (Nat.cast_nonneg _)
      have hws2 : weightFn cpN θ F₁ W (ellProp g L s) (cycDist s'.1.1 s'.1.2) ≤
          w s'.1.1 s'.1.2 :=
        lemmaN_weight_mono_ell hcpN.le hθ.le (lt_of_lt_of_le one_pos hℓs1) hℓsv
          (Nat.cast_nonneg _)
      have hz : zetaProp g W L s ^ 2 ≤ ζv ^ 2 :=
        pow_le_pow_left₀ (lt_of_lt_of_le (by positivity)
          (scale_facts g hg W L hW1 hL1 s s hs0.le le_rfl (by linarith only [hsv, hv1])).2.2.2.1).le
          hζsv 2
      exact mul_le_mul hz (hws1.trans hws2) (lemmaN_weight_pos cp θ F₁ hW1 _ _).le (by positivity)
    exact absurd hx (not_lt.2 hle)
  -- the no-exit lemma
  have hcore := lemmaN_core (gammaG g / W) hσ2 X (a := -1 / 2) (b := (1 + v) / 2) (by norm_num)
    hs0 hsv (by linarith only [hv1]) hv1 hXc hX0 hρ r hr hJ0 hβ0 hκ0 hbΓ0 hK0
    (by linarith only [hδ₁] : (0 : ℝ) ≤ 4 * δ₁) hδs0.le hJ Bad hbad hrate hL2 hinit
  -- the final step
  set A₁ := {x : Fin L × Fin W × Fin W → ℝ | J * (1 + β) ≤ X v (Real.sqrt (v * (gammaG g / W)) • x)}
    with hA₁
  set B₁ := {x : Fin L × Fin W × Fin W → ℝ | ∃ l : Fin L × Fin L,
    Cw * (⨆ s : S₀, ‖flowErr W ⟨g, E, L, v⟩ ![s.1.1, s.1.2] ![true, false] x‖ /
      weightFn cpN θ F₁ W (ellProp g L v) (cycDist s.1.1 s.1.2)) + (W : ℝ) ^ (-4 : ℝ) <
    ‖flowErr W ⟨g, E, L, v⟩ ![l.1, l.2] ![true, false] x‖ /
      weightFn cpN θ F₁ W (ellProp g L v) (cycDist l.1 l.2)} with hB₁
  have hB₁m : μ W L B₁ ≤ ENNReal.ofReal δ₁ := hsw v (le_trans hs hsv.le) le_rfl
  have hJβ : Cw * (J * (1 + β)) = ω ^ 100 * P / 2 := by
    rw [hJdef, hβdef]
    have : (2 * Cw * (1 + 1 / (2 * (r : ℝ)))) ≠ 0 := by positivity
    field_simp
  have hW4 : (W : ℝ) ^ (-4 : ℝ) ≤ ζv ^ 2 * (ω ^ 100 * P / 2) := by
    have hWr : (W : ℝ) ^ (-4 : ℝ) = ((W : ℝ) ^ 4)⁻¹ := by
      rw [Real.rpow_neg hW0.le]; norm_cast
    have hz : (4 * (W : ℝ) ^ 2)⁻¹ ≤ ζv ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hζvW 2
      calc (4 * (W : ℝ) ^ 2)⁻¹ = ((2 * (W : ℝ))⁻¹) ^ 2 := by field_simp; ring
        _ ≤ _ := this
    have hωP : 1 ≤ ω ^ 100 * P := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hω1) hP1
    have hW4' : (4 : ℝ) ≤ W := by exact_mod_cast hW
    rw [hWr]
    have h8 : 8 * (W : ℝ) ^ 2 ≤ (W : ℝ) ^ 4 := by
      have h16 : (16 : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith only [hW4']
      nlinarith only [h16]
    calc ((W : ℝ) ^ 4)⁻¹ ≤ (8 * (W : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) h8
      _ = (4 * (W : ℝ) ^ 2)⁻¹ * (1 / 2) := by field_simp; ring
      _ ≤ ζv ^ 2 * (ω ^ 100 * P / 2) := by
          gcongr
  have hsub : {x : Fin L × Fin W × Fin W → ℝ | ∃ ab : Fin L × Fin L, (W : ℝ) ^ ε * (P *
        ζv ^ 2 * weightFn cpN θ F W ℓv (cycDist ab.1 ab.2)) <
      ‖flowErr W ⟨g, E, L, v⟩ ![ab.1, ab.2] ![true, false] x‖} ⊆ A₁ ∪ B₁ := by
    intro x ⟨ab, hab⟩
    by_contra hc
    simp only [hA₁, hB₁, Set.mem_union, Set.mem_setOf_eq, not_or, not_le, not_exists,
      not_lt] at hc
    obtain ⟨hXv, hswv⟩ := hc
    have hwl : 0 < w ab.1 ab.2 := lemmaN_weight_pos cpN θ F₁ hW1 _ _
    have hle := lemmaN_final_le (S := S') (S₀ := S₀) (fun s => ⟨s.1, hS₀ s.2⟩) hq henv hδs0
      (fun s : S' => pairErrField g E (mRoot g L E) W L v (Real.sqrt (v * (gammaG g / W)) • x) s)
      (fun s : S₀ => flowErr W ⟨g, E, L, v⟩ ![s.1.1, s.1.2] ![true, false] x)
      (fun s : S₀ => w s.1.1 s.1.2) (fun s => lemmaN_weight_pos cpN θ F₁ hW1 _ _)
      (fun s => lemmaN_flowErr_eq g E W L (le_trans hs0.le hsv.le) s.1 x) (fun s => rfl) hζv0
      hCw hXv hJβ hwl (hswv ab) hW4
      (Wε := (W : ℝ) ^ ε * (P * ζv ^ 2 * weightFn cpN θ F W ℓv (cycDist ab.1 ab.2))) (by
        have h1 : w ab.1 ab.2 ≤ weightFn cpN θ F W ℓv (cycDist ab.1 ab.2) :=
          lemmaN_weight_anti_F hFF hW1 _ _
        calc ω ^ 100 * P * ζv ^ 2 * w ab.1 ab.2 ≤
            (W : ℝ) ^ ε * (P * ζv ^ 2 * weightFn cpN θ F W ℓv (cycDist ab.1 ab.2)) := by
              rw [show ω ^ 100 * P * ζv ^ 2 * w ab.1 ab.2 =
                ω ^ 100 * (P * ζv ^ 2 * w ab.1 ab.2) by ring]
              gcongr)
    exact absurd hab (not_lt.2 hle)
  have hpos := lemmaN_rates_pos (ε := 1 / 100) (β := 1 / (2 * r)) (κ := κ) (bΓ := bΓ) r hr
    (by norm_num) (by norm_num) hβ0 hκ0 hbΓ0
  have hcore0 : 0 ≤ (perronMul (1 / 100) β κ bΓ r / rateMulA12 (1 / 100) β κ bΓ r) *
      (((1 - s) / (1 - v)) ^ perronMul (1 / 100) β κ bΓ r *
        ((2 * δs / J) ^ (2 * r) + ((1 + 2 * β) ^ (2 * r) +
          rateMulA12 (1 / 100) β κ bΓ r / perronMul (1 / 100) β κ bΓ r) * (4 * δ₁) +
          (1 + rateMulA12 (1 / 100) β κ bΓ r / perronMul (1 / 100) β κ bΓ r) *
            (K * Real.sqrt (4 * δ₁)))) := by
    have h1v' : 0 < (1 - s) / (1 - v) := div_pos (by linarith only [hsv, hv1]) h1v
    have hδ4 : 0 ≤ 4 * δ₁ := by linarith only [hδ₁]
    have := hpos.1
    have := hpos.2
    positivity
  calc μ W L _ ≤ μ W L (A₁ ∪ B₁) := measure_mono hsub
    _ ≤ μ W L A₁ + μ W L B₁ := measure_union_le _ _
    _ ≤ ENNReal.ofReal _ + ENNReal.ofReal δ₁ := add_le_add hcore hB₁m
    _ = ENNReal.ofReal _ := (ENNReal.ofReal_add hcore0 hδ₁).symm

end AtW2

/-! ### Thresholds in `W` -/

section Large

/-- `C ≤ W^a` for all large `W`. -/
private theorem lemmaN_large_const (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → C ≤ (W : ℝ) ^ a := by
  refine ⟨⌈(max C 1) ^ (1 / a)⌉₊ + 1, fun W hW => ?_⟩
  have hC1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  have hb : (max C 1) ^ (1 / a) ≤ (W : ℝ) := by
    have := Nat.le_ceil ((max C 1) ^ (1 / a))
    have h2 : ((⌈(max C 1) ^ (1 / a)⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at h2
    linarith
  have h0 : 0 ≤ (max C 1) ^ (1 / a) := by positivity
  calc C ≤ max C 1 := le_max_left _ _
    _ = ((max C 1) ^ (1 / a)) ^ a := by
        rw [← Real.rpow_mul (by linarith), one_div_mul_cancel ha.ne', Real.rpow_one]
    _ ≤ (W : ℝ) ^ a := Real.rpow_le_rpow h0 hb ha.le

/-- `log W ≤ W^a / K` for all large `W`. -/
private theorem lemmaN_large_log (K : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → K * Real.log W ≤ (W : ℝ) ^ a := by
  obtain ⟨W₁, hW₁⟩ := lemmaN_large_const (2 * |K| / a) (half_pos ha)
  refine ⟨max W₁ 1, fun W hW => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  have h1 : Real.log W ≤ (W : ℝ) ^ (a / 2) / (a / 2) := Real.log_le_rpow_div hW0.le (half_pos ha)
  have h2 := hW₁ W (le_of_max_le_left hW)
  have hpos : 0 < (W : ℝ) ^ (a / 2) := Real.rpow_pos_of_pos hW0 _
  calc K * Real.log W ≤ |K| * Real.log W := mul_le_mul_of_nonneg_right (le_abs_self K) hlog0
    _ ≤ |K| * ((W : ℝ) ^ (a / 2) / (a / 2)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg K)
    _ = (2 * |K| / a) * (W : ℝ) ^ (a / 2) := by field_simp
    _ ≤ (W : ℝ) ^ (a / 2) * (W : ℝ) ^ (a / 2) := mul_le_mul_of_nonneg_right h2 hpos.le
    _ = (W : ℝ) ^ a := by rw [← Real.rpow_add hW0]; ring_nf

/-- `(log W)^k ≤ W^a` for all large `W`. -/
private theorem lemmaN_large_logpow {k : ℝ} (hk : 0 < k) {a : ℝ} (ha : 0 < a) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → Real.log W ^ k ≤ (W : ℝ) ^ a := by
  obtain ⟨W₁, hW₁⟩ := lemmaN_large_log 1 (div_pos ha hk)
  refine ⟨max W₁ 1, fun W hW => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  have h1 := hW₁ W (le_of_max_le_left hW)
  rw [one_mul] at h1
  calc Real.log W ^ k ≤ ((W : ℝ) ^ (a / k)) ^ k := Real.rpow_le_rpow hlog0 h1 hk.le
    _ = (W : ℝ) ^ a := by
        rw [← Real.rpow_mul (by linarith)]; congr 1; field_simp

/-- `C exp(-c (log W)²) ≤ W^{-K}` for all large `W`. -/
private theorem lemmaN_large_exp (C K : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → C * Real.exp (-(c * Real.log W ^ (2 : ℝ))) ≤ (W : ℝ) ^ (-K) := by
  set T := max 1 ((|K| + |Real.log (max C 1)| + 1) / c) with hT
  refine ⟨⌈Real.exp T⌉₊ + 1, fun W hW => ?_⟩
  have hb : Real.exp T ≤ (W : ℝ) := by
    have := Nat.le_ceil (Real.exp T)
    have h2 : ((⌈Real.exp T⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at h2
    linarith
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le (Real.exp_pos _) hb
  set ℓ := Real.log W with hℓ
  have hℓT : T ≤ ℓ := by rw [hℓ, Real.le_log_iff_exp_le hW0]; exact hb
  have hℓ1 : 1 ≤ ℓ := le_trans (le_max_left _ _) hℓT
  have hℓb : (|K| + |Real.log (max C 1)| + 1) / c ≤ ℓ := le_trans (le_max_right _ _) hℓT
  have hsq : ℓ ^ (2 : ℝ) = ℓ * ℓ := by rw [Real.rpow_two, sq]
  have h1 : |K| + |Real.log (max C 1)| + 1 ≤ c * ℓ := by
    rw [div_le_iff₀ hc] at hℓb; linarith
  have key : Real.log (max C 1) + K * ℓ ≤ c * ℓ ^ (2 : ℝ) := by
    rw [hsq]
    have h2 : (|K| + |Real.log (max C 1)| + 1) * ℓ ≤ c * ℓ * ℓ :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have h3 : Real.log (max C 1) ≤ |Real.log (max C 1)| * ℓ := by
      have := le_abs_self (Real.log (max C 1))
      have := mul_le_mul_of_nonneg_left hℓ1 (abs_nonneg (Real.log (max C 1)))
      linarith
    have h4 : K * ℓ ≤ |K| * ℓ := mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
    nlinarith
  have hC : C ≤ Real.exp (Real.log (max C 1)) := by
    rw [Real.exp_log (by positivity)]; exact le_max_left _ _
  have hWK : (W : ℝ) ^ (-K) = Real.exp (-(K * ℓ)) := by
    rw [Real.rpow_def_of_pos hW0, hℓ]; ring_nf
  rw [hWK]
  calc C * Real.exp (-(c * ℓ ^ (2 : ℝ))) ≤ Real.exp (Real.log (max C 1)) *
        Real.exp (-(c * ℓ ^ (2 : ℝ))) := mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
    _ = Real.exp (Real.log (max C 1) - c * ℓ ^ (2 : ℝ)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(K * ℓ)) := Real.exp_le_exp.2 (by linarith)

end Large


section Total

/-- The excess constant `E₀ = (3/4)e^{3/2}(2e/(1-ε))κ` of the Perron root at `ε = 1/100`,
`κ = 2(1+1/100)C_w`. -/
private def lemmaNE0 (Cw : ℝ) : ℝ :=
  3 / 4 * Real.exp (3 / 2) * (2 * Real.exp 1 / (1 - 1 / 100)) * (2 * (1 + 1 / 100) * Cw)

/-- The bracket rate `b₀(r) = min{1, 1/(r(2r-1)), 1/(4B(r))}` at which the Perron root moves by at
most one. -/
private def lemmaNb0 (Cw : ℝ) (r : ℕ) : ℝ :=
  min 1 (min (1 / (r * (2 * r - 1))) (1 / (4 * perronMulB (1 / 100) (1 / (2 * r))
    (2 * (1 + 1 / 100) * Cw) r)))

private theorem lemmaN_b0_pos {Cw : ℝ} (hCw : 1 ≤ Cw) {r : ℕ} (hr : 1 ≤ r) : 0 < lemmaNb0 Cw r := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h2 : (0 : ℝ) < r * (2 * r - 1) := by nlinarith
  have hB : 0 < perronMulB (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) r := by
    have h2r : (0 : ℝ) < 2 * r - 1 := by linarith
    have c12 : 0 ≤ rateMulC12 (1 / 100) (1 / (2 * r)) r := by unfold rateMulC12; positivity
    have a21 : 0 ≤ rateA21 (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) := by
      unfold rateA21; positivity
    have c21 : 0 ≤ rateMulC21 (1 / 100) (1 / (2 * r)) := by unfold rateMulC21; positivity
    have a12 : 0 ≤ rateA12 (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) r := by
      unfold rateA12; positivity
    unfold perronMulB
    have h1 : 0 < (r : ℝ) ^ 2 * (2 * r - 1) * (2 * (1 + 1 / 100) * Cw) := by positivity
    have h3 : 0 ≤ (r : ℝ) ^ 2 * (2 * r - 1) ^ 2 / 4 := by positivity
    have := mul_nonneg c12 a21
    have := mul_nonneg c21 a12
    have := mul_nonneg c12 c21
    linarith
  unfold lemmaNb0
  refine lt_min one_pos (lt_min (by positivity) (by positivity))

/-- Bounds on the Perron root and on `λ = a₁₂'/ρ'` at `b_Γ ∈ (0, b₀(r)]`:
`rκ ≤ ρ' ≤ c_* r + E₀ + 1` and `rateA12 ≤ a₁₂' ≤ rateA12 + rateMulC12`. -/
private theorem lemmaN_perron_bounds {Cw : ℝ} (hCw : 1 ≤ Cw) {r : ℕ} (hr : 1 ≤ r) {bΓ : ℝ}
    (hb0 : 0 ≤ bΓ) (hb : bΓ ≤ lemmaNb0 Cw r) :
    r * (2 * (1 + 1 / 100) * Cw) ≤ perronMul (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) bΓ r ∧
    perronMul (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) bΓ r ≤
      cstarN Cw * r + lemmaNE0 Cw + 1 ∧
    rateA12 (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) r ≤
      rateMulA12 (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) bΓ r ∧
    rateMulA12 (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) bΓ r ≤
      rateA12 (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) r +
        rateMulC12 (1 / 100) (1 / (2 * r)) r := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set κ := 2 * (1 + 1 / 100) * Cw with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hβ : (0 : ℝ) < 1 / (2 * r) := by positivity
  have hb1 : bΓ ≤ 1 := hb.trans (min_le_left _ _)
  have hbr : bΓ ≤ 1 / (r * (2 * r - 1)) := hb.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbB : bΓ ≤ 1 / (4 * perronMulB (1 / 100) (1 / (2 * r)) κ r) :=
    hb.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h2r : (0 : ℝ) < r * (2 * r - 1) := by nlinarith
  have hbr' : r * (2 * r - 1) * bΓ ≤ 1 := by
    rw [le_div_iff₀ h2r] at hbr; linarith
  have hB0 : 0 ≤ perronMulB (1 / 100) (1 / (2 * r)) κ r := by
    have := lemmaN_b0_pos hCw hr
    by_contra h
    push Not at h
    have : 1 / (4 * perronMulB (1 / 100) (1 / (2 * r)) κ r) < 0 :=
      div_neg_of_pos_of_neg one_pos (by linarith)
    have hb' : lemmaNb0 Cw r ≤ 1 / (4 * perronMulB (1 / 100) (1 / (2 * r)) κ r) :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hbB' : 4 * perronMulB (1 / 100) (1 / (2 * r)) κ r * bΓ ≤ 1 := by
    rcases hB0.eq_or_lt with h | h
    · rw [← h]; simp
    · rw [le_div_iff₀ (by positivity)] at hbB; linarith
  have hP := perronMul_le (ε := 1 / 100) (β := 1 / (2 * r)) (κ := κ) (bΓ := bΓ) r hr
    (by norm_num) (by norm_num) hβ hκ0 hb0 hb1 hbr' hbB'
  have hE := perron_excess_le (ε := 1 / 100) (κ := κ) (by norm_num) (by norm_num) hκ0 r hr
  have hc : (1 + Real.sqrt (1 + 4 * Real.exp 2 / (1 - 1 / 100) ^ 2)) * κ * r = cstarN Cw * r := by
    simp only [cstarN, hκ]
  have hC12 : 0 ≤ rateMulC12 (1 / 100) (1 / (2 * r)) r := by unfold rateMulC12; positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold perronMul rateMulA11
    have h1 : 0 ≤ Real.sqrt (((2 * r * κ + r * (2 * r - 1) * bΓ) / 2) ^ 2 +
        rateMulA12 (1 / 100) (1 / (2 * r)) κ bΓ r * rateMulA21 (1 / 100) (1 / (2 * r)) κ bΓ) :=
      Real.sqrt_nonneg _
    have h2 : 0 ≤ (r : ℝ) * (2 * r - 1) * bΓ := by positivity
    linarith
  · have : lemmaNE0 Cw = 3 / 4 * Real.exp (3 / 2) * (2 * Real.exp 1 / (1 - 1 / 100)) * κ := rfl
    linarith
  · unfold rateMulA12
    have : 0 ≤ rateMulC12 (1 / 100) (1 / (2 * r)) r * bΓ := mul_nonneg hC12 hb0
    linarith
  · unfold rateMulA12
    have : rateMulC12 (1 / 100) (1 / (2 * r)) r * bΓ ≤ rateMulC12 (1 / 100) (1 / (2 * r)) r :=
      mul_le_of_le_one_right hC12 hb1
    linarith

/-- The main term `R^{ρ'} (2δ_s/J)^{2r} ≤ W^{3(E₀+1)} ω^{-148 r}`. -/
private theorem lemmaN_main_term {W : ℕ} (hW : 1 ≤ W) {Cw ω R Rsv ρ' : ℝ} {r : ℕ} (hCw : 1 ≤ Cw)
    (hr : 1 ≤ r) (hω : 6 * Cw ≤ ω) (hR : 1 ≤ R) (hR3 : R ≤ (W : ℝ) ^ 3) (hRsv1 : 1 ≤ Rsv)
    (hRsv : Rsv ≤ R) (hρ0 : 0 ≤ ρ') (hρ : ρ' ≤ cstarN Cw * r + lemmaNE0 Cw + 1)
    (hE0 : 0 ≤ lemmaNE0 Cw) :
    Rsv ^ ρ' * (2 * (R ^ 4 * ω ^ 25) /
        (ω ^ 100 * R ^ lemmaNM Cw / (2 * Cw * (1 + 1 / (2 * r))))) ^ (2 * r) ≤
      (W : ℝ) ^ (3 * (lemmaNE0 Cw + 1)) / ω ^ (148 * r) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hR0 : 0 < R := by linarith
  have hω0 : 0 < ω := by linarith
  set ρm := cstarN Cw * r + lemmaNE0 Cw + 1 with hρm
  set β : ℝ := 1 / (2 * r) with hβ
  have hβ0 : 0 < β := by positivity
  have hβ1 : β ≤ 1 / 2 := by
    rw [hβ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- the power of `R`
  have hRρ : Rsv ^ ρ' ≤ R ^ ρm :=
    (Real.rpow_le_rpow_of_exponent_le hRsv1 hρ).trans
      (Real.rpow_le_rpow (by linarith) hRsv (by linarith))
  have hsplit : 2 * (R ^ 4 * ω ^ 25) / (ω ^ 100 * R ^ lemmaNM Cw / (2 * Cw * (1 + β))) =
      (4 * Cw * (1 + β) / ω ^ 75) * (R ^ (4 : ℝ) / R ^ lemmaNM Cw) := by
    rw [show (R : ℝ) ^ (4 : ℝ) = R ^ (4 : ℕ) by norm_cast]
    have : R ^ lemmaNM Cw ≠ 0 := (Real.rpow_pos_of_pos hR0 _).ne'
    field_simp
    ring
  have hRpow : R ^ ρm * (R ^ (4 : ℝ) / R ^ lemmaNM Cw) ^ (2 * r) = R ^ (lemmaNE0 Cw + 1) := by
    rw [← Real.rpow_sub hR0, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le, ← Real.rpow_add hR0]
    congr 1
    simp only [hρm, lemmaNM]
    push_cast
    ring
  have hRW : R ^ (lemmaNE0 Cw + 1) ≤ (W : ℝ) ^ (3 * (lemmaNE0 Cw + 1)) := by
    calc R ^ (lemmaNE0 Cw + 1) ≤ ((W : ℝ) ^ (3 : ℝ)) ^ (lemmaNE0 Cw + 1) := by
          refine Real.rpow_le_rpow hR0.le ?_ (by linarith)
          rw [show ((W : ℝ) ^ (3 : ℝ)) = (W : ℝ) ^ (3 : ℕ) by norm_cast]; exact hR3
      _ = (W : ℝ) ^ (3 * (lemmaNE0 Cw + 1)) := by rw [← Real.rpow_mul hW0.le]
  have hc : 4 * Cw * (1 + β) / ω ^ 75 ≤ 1 / ω ^ 74 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 4 * Cw * (1 + β) ≤ ω := by nlinarith
    calc 4 * Cw * (1 + β) * ω ^ 74 ≤ ω * ω ^ 74 := by gcongr
      _ = 1 * ω ^ 75 := by ring
  have hc0 : 0 ≤ 4 * Cw * (1 + β) / ω ^ 75 := by positivity
  have hq0 : 0 ≤ R ^ (4 : ℝ) / R ^ lemmaNM Cw := by positivity
  rw [hsplit, mul_pow]
  calc Rsv ^ ρ' * ((4 * Cw * (1 + β) / ω ^ 75) ^ (2 * r) * (R ^ (4 : ℝ) / R ^ lemmaNM Cw) ^ (2 * r))
      ≤ R ^ ρm * ((1 / ω ^ 74) ^ (2 * r) * (R ^ (4 : ℝ) / R ^ lemmaNM Cw) ^ (2 * r)) := by
        gcongr
    _ = (1 / ω ^ 74) ^ (2 * r) * (R ^ ρm * (R ^ (4 : ℝ) / R ^ lemmaNM Cw) ^ (2 * r)) := by ring
    _ = (1 / ω ^ 74) ^ (2 * r) * R ^ (lemmaNE0 Cw + 1) := by rw [hRpow]
    _ ≤ (1 / ω ^ 74) ^ (2 * r) * (W : ℝ) ^ (3 * (lemmaNE0 Cw + 1)) := by gcongr
    _ = (W : ℝ) ^ (3 * (lemmaNE0 Cw + 1)) / ω ^ (148 * r) := by
        rw [div_pow, one_pow, ← pow_mul]; ring_nf

set_option maxHeartbeats 1000000 in
/-- The total failure probability is at most `W^{-D}` once the failure exponent `D'` of the inputs
is `2(3ρ_max + C_K + D + 10)` and `r` is large against `D/ε`. -/
private theorem lemmaN_total_le {W : ℕ} (hW : 2 ≤ W) {Cw a bΓ K D Dp CK : ℝ} {r : ℕ} {s t v : ℝ}
    (hCw : 1 ≤ Cw) (hr : 1 ≤ r) (ha : 0 < a) (hb0 : 0 ≤ bΓ) (hb : bΓ ≤ lemmaNb0 Cw r)
    (hsv : s ≤ v) (hvt : v ≤ t) (ht : t < 1) (hR3 : (1 - s) / (1 - t) ≤ (W : ℝ) ^ 3)
    (hω6 : 6 * Cw ≤ (W : ℝ) ^ a)
    (hmain : 4 * ((cstarN Cw * r + lemmaNE0 Cw + 1) /
        rateA12 (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) r) *
        (W : ℝ) ^ (3 * (lemmaNE0 Cw + 1)) ≤ ((W : ℝ) ^ a) ^ (148 * r) * (W : ℝ) ^ (-D))
    (hK0 : 0 ≤ K) (hK : K ≤ (W : ℝ) ^ CK) (hCK : 0 ≤ CK) (hD : 0 < D)
    (hDp : Dp = 2 * (3 * (cstarN Cw * r + lemmaNE0 Cw + 1) + CK + D + 10))
    (hΛ1 : (cstarN Cw * r + lemmaNE0 Cw + 1) /
        rateA12 (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) r ≤ W)
    (hΛ2 : 4 * (2 ^ (2 * r) + (rateA12 (1 / 100) (1 / (2 * r)) (2 * (1 + 1 / 100) * Cw) r +
        rateMulC12 (1 / 100) (1 / (2 * r)) r) / (r * (2 * (1 + 1 / 100) * Cw))) ≤ W) :
    lemmaNTotal Cw ((W : ℝ) ^ a) (((1 - s) / (1 - t)) ^ lemmaNM Cw)
      (((1 - s) / (1 - t)) ^ 4 * ((W : ℝ) ^ a) ^ 25) ((W : ℝ) ^ (-(Dp + 1))) bΓ K r s v ≤
      (W : ℝ) ^ (-D) := by
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set κ := 2 * (1 + 1 / 100) * Cw with hκ
  have hκ0 : 0 < κ := by positivity
  set β : ℝ := 1 / (2 * r) with hβ
  have hβ0 : 0 < β := by positivity
  set ρm := cstarN Cw * r + lemmaNE0 Cw + 1 with hρm
  set ρ' := perronMul (1 / 100) β κ bΓ r with hρ'
  set a12 := rateMulA12 (1 / 100) β κ bΓ r with ha12
  set A12 := rateA12 (1 / 100) β κ r with hA12
  set C12 := rateMulC12 (1 / 100) β r with hC12
  obtain ⟨hρlow, hρup, ha12low, ha12up⟩ := lemmaN_perron_bounds hCw hr hb0 hb
  have hA120 : 0 < A12 := by
    simp only [hA12, rateA12]; positivity
  have hρ'0 : 0 < ρ' := lt_of_lt_of_le (by positivity) hρlow
  have ha120 : 0 < a12 := lt_of_lt_of_le hA120 ha12low
  have hE0 : 0 ≤ lemmaNE0 Cw := by unfold lemmaNE0; positivity
  have hcst : 0 ≤ cstarN Cw := by unfold cstarN; positivity
  have hρm0 : 0 ≤ ρm := by positivity
  set Λ₁ := ρm / A12 with hΛ₁
  set Λ₂ := (A12 + C12) / (r * κ) with hΛ₂
  have hlinv : ρ' / a12 ≤ Λ₁ := by
    rw [hΛ₁, div_le_div_iff₀ ha120 hA120]
    calc ρ' * A12 ≤ ρm * A12 := mul_le_mul_of_nonneg_right hρup hA120.le
      _ ≤ ρm * a12 := mul_le_mul_of_nonneg_left ha12low hρm0
  have hlam : a12 / ρ' ≤ Λ₂ := by
    rw [hΛ₂, div_le_div_iff₀ hρ'0 (by positivity)]
    calc a12 * (r * κ) ≤ (A12 + C12) * (r * κ) := mul_le_mul_of_nonneg_right ha12up (by positivity)
      _ ≤ (A12 + C12) * ρ' := by
          have : 0 ≤ A12 + C12 := by linarith
          exact mul_le_mul_of_nonneg_left hρlow this
  have hlam0 : 0 ≤ a12 / ρ' := by positivity
  have hΛ₂0 : 0 ≤ Λ₂ := le_trans hlam0 hlam
  -- the ratios
  have h1t : 0 < 1 - t := by linarith
  have h1v : 0 < 1 - v := by linarith
  set R := (1 - s) / (1 - t) with hR
  have hR1 : 1 ≤ R := lemmaN_R_ge (hsv.trans hvt) ht
  set Rsv := (1 - s) / (1 - v) with hRsv
  have hRsv1 : 1 ≤ Rsv := lemmaN_R_ge hsv (lt_of_le_of_lt hvt ht)
  have hRsvR : Rsv ≤ R := by
    rw [hRsv, hR]
    exact div_le_div_of_nonneg_left (by linarith) h1t (by linarith)
  have hRsvρ : Rsv ^ ρ' ≤ (W : ℝ) ^ (3 * ρm) := by
    calc Rsv ^ ρ' ≤ R ^ ρm := (Real.rpow_le_rpow_of_exponent_le hRsv1 hρup).trans
          (Real.rpow_le_rpow (by linarith) hRsvR hρm0)
      _ ≤ ((W : ℝ) ^ (3 : ℝ)) ^ ρm := by
          refine Real.rpow_le_rpow (by linarith) ?_ hρm0
          rw [show ((W : ℝ) ^ (3 : ℝ)) = (W : ℝ) ^ (3 : ℕ) by norm_cast]; exact hR3
      _ = (W : ℝ) ^ (3 * ρm) := by rw [← Real.rpow_mul hW0.le]
  -- the main term
  have hmt := lemmaN_main_term hW1 hCw hr hω6 hR1 hR3 hRsv1 hRsvR hρ'0.le hρup hE0
  -- the remaining terms
  set δ₁ := (W : ℝ) ^ (-(Dp + 1)) with hδ₁
  have hδ₁0 : 0 ≤ δ₁ := by positivity
  have hsq : Real.sqrt (4 * δ₁) = 2 * (W : ℝ) ^ (-(Dp + 1) / 2) := by
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)], hδ₁,
      Real.sqrt_eq_rpow, ← Real.rpow_mul hW0.le]
    ring_nf
  have hpow2 : (1 + 2 * β) ^ (2 * r) ≤ 2 ^ (2 * r) := by
    have : 1 + 2 * β ≤ 2 := by
      rw [hβ]; have : 2 * (1 / (2 * (r : ℝ))) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]; linarith
      linarith
    exact pow_le_pow_left₀ (by positivity) this _
  have hT2 : ((1 + 2 * β) ^ (2 * r) + a12 / ρ') * (4 * δ₁) ≤ W * δ₁ := by
    calc ((1 + 2 * β) ^ (2 * r) + a12 / ρ') * (4 * δ₁) ≤ (2 ^ (2 * r) + Λ₂) * (4 * δ₁) := by
          gcongr
      _ = 4 * (2 ^ (2 * r) + Λ₂) * δ₁ := by ring
      _ ≤ W * δ₁ := by gcongr
  have hT3 : (1 + a12 / ρ') * (K * Real.sqrt (4 * δ₁)) ≤
      W * ((W : ℝ) ^ CK * (W : ℝ) ^ (-(Dp + 1) / 2)) := by
    rw [hsq]
    have h2Λ : 2 * (1 + Λ₂) ≤ W := by
      have : (1 : ℝ) ≤ 2 ^ (2 * r) := one_le_pow₀ (by norm_num)
      linarith only [this, hΛ2, hΛ₂0]
    calc (1 + a12 / ρ') * (K * (2 * (W : ℝ) ^ (-(Dp + 1) / 2))) =
        2 * (1 + a12 / ρ') * (K * (W : ℝ) ^ (-(Dp + 1) / 2)) := by ring
      _ ≤ 2 * (1 + Λ₂) * ((W : ℝ) ^ CK * (W : ℝ) ^ (-(Dp + 1) / 2)) := by gcongr
      _ ≤ W * ((W : ℝ) ^ CK * (W : ℝ) ^ (-(Dp + 1) / 2)) := by gcongr
  -- assemble
  have hWa : (0 : ℝ) < (W : ℝ) ^ a := Real.rpow_pos_of_pos hW0 _
  have hmain' : ρ' / a12 * ((W : ℝ) ^ (3 * (lemmaNE0 Cw + 1)) / ((W : ℝ) ^ a) ^ (148 * r)) ≤
      (W : ℝ) ^ (-D) / 4 := by
    have hp : 0 < ((W : ℝ) ^ a) ^ (148 * r) := by positivity
    calc ρ' / a12 * ((W : ℝ) ^ (3 * (lemmaNE0 Cw + 1)) / ((W : ℝ) ^ a) ^ (148 * r)) ≤
        Λ₁ * ((W : ℝ) ^ (3 * (lemmaNE0 Cw + 1)) / ((W : ℝ) ^ a) ^ (148 * r)) := by gcongr
      _ ≤ (W : ℝ) ^ (-D) / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ hp (by norm_num)]
          linarith [hmain]
  have hrest : ρ' / a12 * (Rsv ^ ρ' * (W * δ₁ +
      W * ((W : ℝ) ^ CK * (W : ℝ) ^ (-(Dp + 1) / 2)))) + δ₁ ≤ 3 * (W : ℝ) ^ (-D - 8) := by
    have hmulW : ∀ x : ℝ, (W : ℝ) * (W : ℝ) ^ x = (W : ℝ) ^ (1 + x) := fun x => by
      rw [Real.rpow_add hW0, Real.rpow_one]
    have e1 : W * δ₁ = (W : ℝ) ^ (-Dp) := by
      rw [hδ₁, hmulW]; ring_nf
    have e2 : W * ((W : ℝ) ^ CK * (W : ℝ) ^ (-(Dp + 1) / 2)) =
        (W : ℝ) ^ (1 + CK - (Dp + 1) / 2) := by
      rw [← Real.rpow_add hW0, hmulW]; ring_nf
    rw [e1, e2]
    have hle1 : (W : ℝ) ^ (3 * ρm) * (W : ℝ) ^ (-Dp) ≤ (W : ℝ) ^ (-D - 9) := by
      rw [← Real.rpow_add hW0]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hDp]; linarith)
    have hle2 : (W : ℝ) ^ (3 * ρm) * (W : ℝ) ^ (1 + CK - (Dp + 1) / 2) ≤ (W : ℝ) ^ (-D - 9) := by
      rw [← Real.rpow_add hW0]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hDp]; linarith)
    have hle3 : δ₁ ≤ (W : ℝ) ^ (-D - 8) := by
      rw [hδ₁]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hDp]; linarith)
    have hΛ1' : ρ' / a12 ≤ W := hlinv.trans hΛ1
    have hW9 : (W : ℝ) * (W : ℝ) ^ (-D - 9) = (W : ℝ) ^ (-D - 8) := by
      rw [hmulW]; ring_nf
    have hp1 : 0 ≤ (W : ℝ) ^ (-Dp) := by positivity
    have hp2 : 0 ≤ (W : ℝ) ^ (1 + CK - (Dp + 1) / 2) := by positivity
    have hRs0 : 0 ≤ Rsv ^ ρ' := by positivity
    calc ρ' / a12 * (Rsv ^ ρ' * ((W : ℝ) ^ (-Dp) + (W : ℝ) ^ (1 + CK - (Dp + 1) / 2))) + δ₁ ≤
        W * ((W : ℝ) ^ (3 * ρm) * ((W : ℝ) ^ (-Dp) + (W : ℝ) ^ (1 + CK - (Dp + 1) / 2))) +
          (W : ℝ) ^ (-D - 8) := by gcongr
      _ ≤ W * ((W : ℝ) ^ (-D - 9) + (W : ℝ) ^ (-D - 9)) + (W : ℝ) ^ (-D - 8) := by
          rw [mul_add ((W : ℝ) ^ (3 * ρm))]
          gcongr
      _ = 3 * (W : ℝ) ^ (-D - 8) := by rw [mul_add, hW9]; ring
  have hfin : 3 * (W : ℝ) ^ (-D - 8) ≤ 3 / 4 * (W : ℝ) ^ (-D) := by
    have : (W : ℝ) ^ (-D - 8) = (W : ℝ) ^ (-D) * ((W : ℝ) ^ (8 : ℝ))⁻¹ := by
      rw [← Real.rpow_neg hW0.le, ← Real.rpow_add hW0]; ring_nf
    rw [this]
    have h8 : (4 : ℝ) ≤ (W : ℝ) ^ (8 : ℝ) := by
      rw [show ((W : ℝ) ^ (8 : ℝ)) = (W : ℝ) ^ (8 : ℕ) by norm_cast]
      calc (4 : ℝ) ≤ 2 ^ 8 := by norm_num
        _ ≤ (W : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) hW2 8
    have hinv : ((W : ℝ) ^ (8 : ℝ))⁻¹ ≤ 1 / 4 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num), one_div, inv_inv]; exact h8
    have hWD : 0 ≤ (W : ℝ) ^ (-D) := by positivity
    nlinarith
  -- unfold the total
  unfold lemmaNTotal
  rw [← hRsv]
  calc ρ' / a12 * (Rsv ^ ρ' * ((2 * (R ^ 4 * ((W : ℝ) ^ a) ^ 25) /
        (((W : ℝ) ^ a) ^ 100 * R ^ lemmaNM Cw / (2 * Cw * (1 + β)))) ^ (2 * r) +
        ((1 + 2 * β) ^ (2 * r) + a12 / ρ') * (4 * δ₁) + (1 + a12 / ρ') * (K * Real.sqrt (4 * δ₁))))
        + δ₁ =
      ρ' / a12 * (Rsv ^ ρ' * (2 * (R ^ 4 * ((W : ℝ) ^ a) ^ 25) /
        (((W : ℝ) ^ a) ^ 100 * R ^ lemmaNM Cw / (2 * Cw * (1 + β)))) ^ (2 * r)) +
      (ρ' / a12 * (Rsv ^ ρ' * (((1 + 2 * β) ^ (2 * r) + a12 / ρ') * (4 * δ₁) +
        (1 + a12 / ρ') * (K * Real.sqrt (4 * δ₁))))) + δ₁ := by ring
    _ ≤ ρ' / a12 * ((W : ℝ) ^ (3 * (lemmaNE0 Cw + 1)) / ((W : ℝ) ^ a) ^ (148 * r)) +
      (ρ' / a12 * (Rsv ^ ρ' * (W * δ₁ + W * ((W : ℝ) ^ CK * (W : ℝ) ^ (-(Dp + 1) / 2))))) +
        δ₁ := by
        have h0 : 0 ≤ ρ' / a12 := by positivity
        have hRs : 0 ≤ Rsv ^ ρ' := by positivity
        gcongr
    _ ≤ (W : ℝ) ^ (-D) / 4 + 3 / 4 * (W : ℝ) ^ (-D) := by
        linarith only [hmain', hrest, hfin]
    _ = (W : ℝ) ^ (-D) := by ring

end Total


section WeightThresholds

/-- Far beyond the halo `ℓ (log W)^{2/θ}` the weight is at most `e^{-c(log W)²} + W^{-F}`. -/
private theorem lemmaN_weight_far {c θ F : ℝ} (hc : 0 ≤ c) (hθ : 0 < θ) {W : ℕ} (hW : 1 ≤ W) {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : ℓ * Real.log W ^ (2 / θ) < d) :
    weightFn c θ F W ℓ d ≤ Real.exp (-(c * Real.log W ^ (2 : ℝ))) + (W : ℝ) ^ (-F) := by
  unfold weightFn
  have hlog : 0 ≤ Real.log W := Real.log_nonneg (by exact_mod_cast hW)
  have h1 : Real.log W ^ (2 / θ) < d / ℓ := by rw [lt_div_iff₀ hℓ]; linarith
  have h2 : Real.log W ^ (2 : ℝ) ≤ (d / ℓ) ^ θ := by
    have e : Real.log W ^ (2 : ℝ) = (Real.log W ^ (2 / θ)) ^ θ := by
      rw [← Real.rpow_mul hlog]; congr 1; field_simp
    rw [e]
    exact Real.rpow_le_rpow (by positivity) h1.le hθ.le
  have h3 : c * Real.log W ^ (2 : ℝ) ≤ c * (d / ℓ) ^ θ := mul_le_mul_of_nonneg_left h2 hc
  gcongr

/-- Within twice the short range `ℓ (log W)^{3/2}` the weight is at least `W^{-a}`. -/
private theorem lemmaN_weight_short {a : ℝ} (ha : 0 < a) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ c θ F : ℝ, 0 ≤ c → c ≤ 1 → 0 < θ → θ ≤ 1 / 2 →
      ∀ ℓ d : ℝ, 0 < ℓ → 0 ≤ d → d ≤ 2 * (ℓ * Real.log W ^ ((3 : ℝ) / 2)) →
        ((W : ℝ) ^ a)⁻¹ ≤ weightFn c θ F W ℓ d := by
  set T := max (2 / a) ((4 / a) ^ (4 : ℝ)) with hT
  refine ⟨⌈Real.exp T⌉₊ + 1, fun W hW c θ F hc0 hc1 hθ hθ2 ℓ d hℓ hd hdh => ?_⟩
  have hb : Real.exp T ≤ (W : ℝ) := by
    have := Nat.le_ceil (Real.exp T)
    have h2 : ((⌈Real.exp T⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at h2
    linarith
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le (Real.exp_pos _) hb
  set lgW := Real.log W with hlgW
  have hlgT : T ≤ lgW := by rw [hlgW, Real.le_log_iff_exp_le hW0]; exact hb
  have hlg1 : 2 / a ≤ lgW := le_trans (le_max_left _ _) hlgT
  have hlg4 : (4 / a) ^ (4 : ℝ) ≤ lgW := le_trans (le_max_right _ _) hlgT
  have hlg0 : 0 < lgW := lt_of_lt_of_le (by positivity) hlg1
  -- `(d/ℓ)^θ ≤ 1 + 2 λ^{3/4}`
  set x := d / ℓ with hx
  have hx0 : 0 ≤ x := div_nonneg hd hℓ.le
  have hxb : x ≤ 2 * lgW ^ ((3 : ℝ) / 2) := by
    rw [hx, div_le_iff₀ hℓ]; linarith
  have hxθ : x ^ θ ≤ 1 + 2 * lgW ^ ((3 : ℝ) / 4) := by
    have hlg34 : 0 ≤ lgW ^ ((3 : ℝ) / 4) := by positivity
    rcases le_or_gt x 1 with h1 | h1
    · have : x ^ θ ≤ 1 := Real.rpow_le_one hx0 h1 hθ.le
      linarith
    · have h2 : x ^ θ ≤ x ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
      have h3 : x ^ ((1 : ℝ) / 2) ≤ (2 * lgW ^ ((3 : ℝ) / 2)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow hx0 hxb (by norm_num)
      have h4 : (2 * lgW ^ ((3 : ℝ) / 2)) ^ ((1 : ℝ) / 2) ≤ 2 * lgW ^ ((3 : ℝ) / 4) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hlg0.le]
        have : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
          calc (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
        rw [show (3 : ℝ) / 2 * (1 / 2) = 3 / 4 by norm_num]
        gcongr
      linarith
  -- `1 + 2 λ^{3/4} ≤ a λ`
  have hkey : 1 + 2 * lgW ^ ((3 : ℝ) / 4) ≤ a * lgW := by
    have h1 : 1 ≤ a / 2 * lgW := by
      rw [div_le_iff₀ ha] at hlg1
      linarith
    have h2 : 2 * lgW ^ ((3 : ℝ) / 4) ≤ a / 2 * lgW := by
      have h14 : 4 / a ≤ lgW ^ ((1 : ℝ) / 4) := by
        have := Real.rpow_le_rpow (by positivity) hlg4 (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rwa [← Real.rpow_mul (by positivity), show (4 : ℝ) * (1 / 4) = 1 by norm_num,
          Real.rpow_one] at this
      have hsplit : lgW = lgW ^ ((3 : ℝ) / 4) * lgW ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_add hlg0]; norm_num
      have hp : 0 ≤ lgW ^ ((3 : ℝ) / 4) := by positivity
      calc 2 * lgW ^ ((3 : ℝ) / 4) = a / 2 * (lgW ^ ((3 : ℝ) / 4) * (4 / a)) := by
            field_simp; ring
        _ ≤ a / 2 * (lgW ^ ((3 : ℝ) / 4) * lgW ^ ((1 : ℝ) / 4)) := by gcongr
        _ = a / 2 * lgW := by rw [← hsplit]
    linarith
  -- the weight
  have hexp : ((W : ℝ) ^ a)⁻¹ = Real.exp (-(a * lgW)) := by
    rw [Real.rpow_def_of_pos hW0, ← Real.exp_neg, hlgW]; ring_nf
  rw [hexp]
  unfold weightFn
  have h1 : c * x ^ θ ≤ a * lgW := by
    have : c * x ^ θ ≤ 1 * x ^ θ := mul_le_mul_of_nonneg_right hc1 (by positivity)
    linarith
  have h2 : Real.exp (-(a * lgW)) ≤ Real.exp (-(c * x ^ θ)) := Real.exp_le_exp.2 (by linarith)
  have h3 : 0 ≤ (W : ℝ) ^ (-F) := by positivity
  rw [← hx]
  linarith

end WeightThresholds


section Numerics

/-- `R^k ζ_t W^{c} ≤ 1` from the strengthened (5.38) [gc:eq:one-step] `R^N ζ_t ≤ W^{-c}` for
`k ≤ N`. -/
private theorem lemmaN_RN {W : ℕ} (hW : 1 ≤ W) {R ζt N c k e : ℝ} (hR : 1 ≤ R) (hζt : 0 ≤ ζt)
    (hRN : R ^ N * ζt ≤ (W : ℝ) ^ (-c)) (hk : k ≤ N) (he : e ≤ c) :
    R ^ k * ζt * (W : ℝ) ^ e ≤ 1 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1 : R ^ k ≤ R ^ N := Real.rpow_le_rpow_of_exponent_le hR hk
  have h2 : (W : ℝ) ^ e ≤ (W : ℝ) ^ c := Real.rpow_le_rpow_of_exponent_le hW1 he
  have h3 : (W : ℝ) ^ (-c) * (W : ℝ) ^ c = 1 := by
    rw [← Real.rpow_add hW0]; simp
  calc R ^ k * ζt * (W : ℝ) ^ e ≤ R ^ N * ζt * (W : ℝ) ^ c := by gcongr
    _ ≤ (W : ℝ) ^ (-c) * (W : ℝ) ^ c := by gcongr
    _ = 1 := h3

/-- `(W^a)^n = W^{na}`. -/
private theorem lemmaN_pow_rpow {W : ℕ} (a : ℝ) (n : ℕ) : ((W : ℝ) ^ a) ^ n = (W : ℝ) ^ (n * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; ring_nf

/-- `log W ≥ 1` for `W ≥ 3`. -/
private theorem lemmaN_log_ge_one {W : ℕ} (hW : 3 ≤ W) : 1 ≤ Real.log W := by
  have hW3 : (3 : ℝ) ≤ W := by exact_mod_cast hW
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- The drift condition of the surrogate: `1.001(2(1.001 + 2W⁻²)C_w(1+W⁻¹) + 1/(2ω)) +
1.003 q/(2ω) ≤ 2.02 C_w` for `W ≥ 1000` and `ω ≥ 1000(q+1)`. -/
private theorem lemmaN_kappa_num {W : ℕ} (hW : 1000 ≤ W) {Cw ω : ℝ} {q : ℕ} (hCw : 1 ≤ Cw)
    (hω : 1000 * (q + 1) ≤ ω) :
    1.001 * (2 * (1.001 + 2 / (W : ℝ) ^ 2) * (Cw * (1 + 1 / (W : ℝ))) + 1 / (2 * ω)) +
      1.003 * q * (1 / (2 * ω)) ≤ 2 * (1 + 1 / 100) * Cw := by
  have hW0 : (1000 : ℝ) ≤ W := by exact_mod_cast hW
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hω0 : 0 < ω := by linarith
  have h1 : 1 / (W : ℝ) ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h2 : 2 / (W : ℝ) ^ 2 ≤ 2 / 1000000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h3 : 1 / (2 * ω) ≤ 1 / (2000 * (q + 1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have h4 : (1.001 + 1.003 * (q : ℝ)) * (1 / (2000 * ((q : ℝ) + 1))) ≤ 1 / 1000 := by
    rw [← div_eq_mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h5 : (1.001 + 2 / (W : ℝ) ^ 2) * (1 + 1 / (W : ℝ)) ≤ 1.001002 * 1.001 := by
    have : 0 ≤ 1 / (W : ℝ) := by positivity
    have : 0 ≤ 2 / (W : ℝ) ^ 2 := by positivity
    calc (1.001 + 2 / (W : ℝ) ^ 2) * (1 + 1 / (W : ℝ)) ≤ (1.001 + 2 / 1000000) * (1 + 1 / 1000) := by
          gcongr
      _ = 1.001002 * 1.001 := by norm_num
  have h6 : 0 ≤ 1 / (2 * ω) := by positivity
  have e : 1.001 * (2 * (1.001 + 2 / (W : ℝ) ^ 2) * (Cw * (1 + 1 / (W : ℝ))) + 1 / (2 * ω)) +
      1.003 * q * (1 / (2 * ω)) = 2.002 * Cw * ((1.001 + 2 / (W : ℝ) ^ 2) * (1 + 1 / (W : ℝ))) +
        (1.001 + 1.003 * q) * (1 / (2 * ω)) := by ring
  rw [e]
  have h7 : (1.001 + 1.003 * (q : ℝ)) * (1 / (2 * ω)) ≤
      (1.001 + 1.003 * (q : ℝ)) * (1 / (2000 * ((q : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h8 : 2.002 * Cw * ((1.001 + 2 / (W : ℝ) ^ 2) * (1 + 1 / (W : ℝ))) ≤
      2.002 * Cw * (1.001002 * 1.001) := mul_le_mul_of_nonneg_left h5 (by positivity)
  nlinarith

/-- The off-set constant is a fixed power of `W`, uniformly in the coupling:
`K ≤ W^{15 + 2F₁ + max(C₁, 0)}`. -/
private theorem lemmaN_K_le {W : ℕ} (hW : 2 ≤ W) {Ccut q2 s1 s2 Cp C₁ F₁ : ℝ} (hCcut0 : 0 ≤ Ccut)
    (hCcut : Ccut ≤ W) (hq0 : 0 ≤ q2) (hq : q2 ≤ W) (hs10 : 0 ≤ s1) (hs1 : s1 ≤ 2)
    (hs20 : 0 ≤ s2) (hs2 : s2 ≤ 2 * W) (hCp : max Cp 0 + 1 ≤ W) :
    Ccut * q2 * s1 * s2 * (2 * ((((2 * (W : ℝ))⁻¹) ^ 2 * (W : ℝ) ^ (-F₁)) ^ 2)⁻¹ *
      (max Cp 0 + 1) * (W : ℝ) ^ C₁) ≤ (W : ℝ) ^ (15 + 2 * F₁ + max C₁ 0) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 1 ≤ W)
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  have he : ((((2 * (W : ℝ))⁻¹) ^ 2 * (W : ℝ) ^ (-F₁)) ^ 2)⁻¹ = 16 * (W : ℝ) ^ 4 *
      (W : ℝ) ^ (2 * F₁) := by
    rw [mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ (-F₁)), ← Real.rpow_mul hW0.le, mul_inv,
      ← Real.rpow_neg hW0.le]
    push_cast
    rw [show -(-F₁ * 2) = 2 * F₁ by ring]
    field_simp
    ring
  have hC1 : (W : ℝ) ^ C₁ ≤ (W : ℝ) ^ (max C₁ 0) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hmax0 : 0 ≤ max Cp 0 := le_max_right _ _
  rw [he]
  have h128 : (128 : ℝ) ≤ (W : ℝ) ^ (7 : ℕ) := by
    calc (128 : ℝ) = 2 ^ 7 := by norm_num
      _ ≤ (W : ℝ) ^ 7 := pow_le_pow_left₀ (by norm_num) hW2 7
  calc Ccut * q2 * s1 * s2 * (2 * (16 * (W : ℝ) ^ 4 * (W : ℝ) ^ (2 * F₁)) * (max Cp 0 + 1) *
        (W : ℝ) ^ C₁)
      ≤ W * W * 2 * (2 * W) * (2 * (16 * (W : ℝ) ^ 4 * (W : ℝ) ^ (2 * F₁)) * W *
        (W : ℝ) ^ (max C₁ 0)) := by gcongr
    _ = 128 * ((W : ℝ) ^ 8 * (W : ℝ) ^ (2 * F₁) * (W : ℝ) ^ (max C₁ 0)) := by ring
    _ ≤ (W : ℝ) ^ (7 : ℕ) * ((W : ℝ) ^ 8 * (W : ℝ) ^ (2 * F₁) * (W : ℝ) ^ (max C₁ 0)) := by
        gcongr
    _ = (W : ℝ) ^ (15 + 2 * F₁ + max C₁ 0) := by
        have e7 : (W : ℝ) ^ (7 : ℕ) = (W : ℝ) ^ (7 : ℝ) := by norm_cast
        have e8 : (W : ℝ) ^ (8 : ℕ) = (W : ℝ) ^ (8 : ℝ) := by norm_cast
        rw [e7, e8, ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
        ring_nf

/-- The near-pair tail condition at `W`: `(L/ℓ_v)²(ω² + (C' + ω ω¹⁰⁰R^M)4W²)ε_w ≤ 1`. -/
private theorem lemmaN_Lr_num {W : ℕ} (hW : 5 ≤ W) {Lr ℓv ω RM C' RC M F₁ εe : ℝ}
    (hLr0 : 0 ≤ Lr) (hℓv : 0 < ℓv) (hLℓ : Lr / ℓv ≤ (W : ℝ) ^ RC) (hRC : 0 ≤ RC)
    (hω0 : 0 ≤ ω) (hωW : ω ≤ W) (hω100 : ω ^ 100 ≤ W) (hRM0 : 0 ≤ RM) (hRM : RM ≤ (W : ℝ) ^ (3 * M))
    (hM : 0 ≤ M) (hC'0 : 0 ≤ C') (hC' : C' ≤ W) (hF₁ : 2 * RC + 3 * M + 6 ≤ F₁) (hεe0 : 0 ≤ εe)
    (hεe : 18 * εe ≤ (W : ℝ) ^ (-(2 * RC + 4 + 3 * M))) :
    (Lr / ℓv) ^ 2 * (ω ^ 2 + (C' + ω * (ω ^ 100 * RM)) * (4 * (W : ℝ) ^ 2)) *
      (εe + (W : ℝ) ^ (-F₁)) ≤ 1 := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hW5 : (5 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set K := 2 * RC + 4 + 3 * M with hK
  have hK0 : 0 ≤ K := by positivity
  have hpow : ∀ x y : ℝ, (W : ℝ) ^ x * (W : ℝ) ^ y = (W : ℝ) ^ (x + y) := fun x y =>
    (Real.rpow_add hW0 x y).symm
  have hn : ∀ n : ℕ, (W : ℝ) ^ n = (W : ℝ) ^ (n : ℝ) := fun n => (Real.rpow_natCast _ n).symm
  have hL2 : (Lr / ℓv) ^ 2 ≤ (W : ℝ) ^ (2 * RC) := by
    calc (Lr / ℓv) ^ 2 ≤ ((W : ℝ) ^ RC) ^ 2 := pow_le_pow_left₀ (by positivity) hLℓ 2
      _ = (W : ℝ) ^ (2 * RC) := by
          rw [← Real.rpow_natCast ((W : ℝ) ^ RC) 2, ← Real.rpow_mul hW0.le]; ring_nf
  have hW43M : 1 ≤ (W : ℝ) ^ (3 * M) := Real.one_le_rpow hW1 (by positivity)
  have hbr : ω ^ 2 + (C' + ω * (ω ^ 100 * RM)) * (4 * (W : ℝ) ^ 2) ≤
      9 * (W : ℝ) ^ (4 + 3 * M) := by
    have e : (W : ℝ) ^ (4 + 3 * M) = (W : ℝ) ^ 4 * (W : ℝ) ^ (3 * M) := by
      rw [hn 4, hpow]; norm_num
    rw [e]
    have h1 : ω ^ 2 ≤ (W : ℝ) ^ 2 := pow_le_pow_left₀ hω0 hωW 2
    have h2 : ω * (ω ^ 100 * RM) ≤ (W : ℝ) * ((W : ℝ) * (W : ℝ) ^ (3 * M)) := by gcongr
    have hW2 : (W : ℝ) ^ 2 ≤ (W : ℝ) ^ 4 := pow_le_pow_right₀ hW1 (by norm_num)
    have hW3 : (W : ℝ) * (W : ℝ) ^ 2 ≤ (W : ℝ) ^ 4 := by
      have : (W : ℝ) * (W : ℝ) ^ 2 = (W : ℝ) ^ 3 := by ring
      rw [this]; exact pow_le_pow_right₀ hW1 (by norm_num)
    have hp4 : 0 ≤ (W : ℝ) ^ 4 := by positivity
    nlinarith
  have hfin1 : (W : ℝ) ^ (2 * RC) * (9 * (W : ℝ) ^ (4 + 3 * M)) * εe ≤ 1 / 2 := by
    have e : (W : ℝ) ^ (2 * RC) * (9 * (W : ℝ) ^ (4 + 3 * M)) = 9 * (W : ℝ) ^ K := by
      calc (W : ℝ) ^ (2 * RC) * (9 * (W : ℝ) ^ (4 + 3 * M)) =
          9 * ((W : ℝ) ^ (2 * RC) * (W : ℝ) ^ (4 + 3 * M)) := by ring
        _ = 9 * (W : ℝ) ^ (2 * RC + (4 + 3 * M)) := by rw [hpow]
        _ = 9 * (W : ℝ) ^ K := by rw [hK]; ring_nf
    rw [e]
    have h1 : (W : ℝ) ^ K * (W : ℝ) ^ (-K) = 1 := by rw [hpow]; simp
    calc 9 * (W : ℝ) ^ K * εe = (W : ℝ) ^ K * (18 * εe) / 2 := by ring
      _ ≤ (W : ℝ) ^ K * (W : ℝ) ^ (-K) / 2 := by gcongr
      _ = 1 / 2 := by rw [h1]
  have hfin2 : (W : ℝ) ^ (2 * RC) * (9 * (W : ℝ) ^ (4 + 3 * M)) * (W : ℝ) ^ (-F₁) ≤ 1 / 2 := by
    have e : (W : ℝ) ^ (2 * RC) * (9 * (W : ℝ) ^ (4 + 3 * M)) * (W : ℝ) ^ (-F₁) =
        9 * (W : ℝ) ^ (2 * RC + (4 + 3 * M) + -F₁) := by
      calc (W : ℝ) ^ (2 * RC) * (9 * (W : ℝ) ^ (4 + 3 * M)) * (W : ℝ) ^ (-F₁) =
          9 * ((W : ℝ) ^ (2 * RC) * (W : ℝ) ^ (4 + 3 * M) * (W : ℝ) ^ (-F₁)) := by ring
        _ = 9 * (W : ℝ) ^ (2 * RC + (4 + 3 * M) + -F₁) := by rw [hpow, hpow]
    rw [e]
    have h1 : (W : ℝ) ^ (2 * RC + (4 + 3 * M) + -F₁) ≤ (W : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    have h2 : (W : ℝ) ^ (-2 : ℝ) = ((W : ℝ) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hW0.le]; norm_cast
    rw [h2] at h1
    have h3 : 9 * ((W : ℝ) ^ 2)⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hεW : 0 ≤ (W : ℝ) ^ (-F₁) := by positivity
  calc (Lr / ℓv) ^ 2 * (ω ^ 2 + (C' + ω * (ω ^ 100 * RM)) * (4 * (W : ℝ) ^ 2)) *
        (εe + (W : ℝ) ^ (-F₁)) ≤
      (W : ℝ) ^ (2 * RC) * (9 * (W : ℝ) ^ (4 + 3 * M)) * (εe + (W : ℝ) ^ (-F₁)) := by gcongr
    _ = (W : ℝ) ^ (2 * RC) * (9 * (W : ℝ) ^ (4 + 3 * M)) * εe +
        (W : ℝ) ^ (2 * RC) * (9 * (W : ℝ) ^ (4 + 3 * M)) * (W : ℝ) ^ (-F₁) := by ring
    _ ≤ 1 / 2 + 1 / 2 := add_le_add hfin1 hfin2
    _ = 1 := by norm_num

end Numerics


set_option maxHeartbeats 4000000 in
/-- The mixed-pair bound at a fixed time on the admissible steps, with the barrier `J₀ = W^ε R^M` in
place of (C.17) [gc:eq:spatialstop]: the choice of the constants, of the thresholds in `W`, and the
two cases `u = s` (the input (5.22) [gc:eq:one-step-input]) and `s < u` (the no-exit lemma with
multiplicative rates). -/
private theorem lemmaN_mixed_aux (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N : ℝ) (hc : 0 < c)
    (hcp : 0 < cp) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hN : lemmaNN0 I.Cw ≤ N) :
    ∃ cpN : ℝ, 0 < cpN ∧ cpN ≤ cp ∧ ∀ S : ℕ → Set StepPt, (∀ W, S W ⊆ {q | StepAdm R c N W q}) →
      (∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
        (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W) →
      OneStepInput cp θ (fun q : StepPt => q.at q.s) S → Step1Out S →
      ∀ F : ℝ, 0 < F → PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
        (fun W q ab ω => flowErr W (q.at q.u) ![ab.1, ab.2] ![true, false] ω)
        (fun W q ab => q.ratio ^ lemmaNM I.Cw * zetaProp q.g W q.L q.u ^ 2 *
          weightFn cpN θ F W (ellProp q.g q.L q.u) (cycDist ab.1 ab.2)) := by
  -- constants fixed with the data
  set Cw := I.Cw with hCwdef
  have hCw : 1 ≤ Cw := I.one_le_Cw
  have hRc : 0 < R.c := R.c_pos
  have hRC : 1 ≤ R.C := R.one_le_C
  have hkE : 0 < kerExcess R.C R.c := by unfold kerExcess; positivity
  set cpN := min (min cp 1) (min (R.c / 2) (1 / (1000 * kerExcess R.C R.c))) with hcpNdef
  have hcpN0 : 0 < cpN := lt_min (lt_min hcp one_pos) (lt_min (by positivity) (by positivity))
  have hcpNcp : cpN ≤ cp := (min_le_left _ _).trans (min_le_left _ _)
  have hcpN1 : cpN ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hcpNc : cpN ≤ R.c / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hcpNk : cpN * kerExcess R.C R.c ≤ 1 / 1000 := by
    have h1 : cpN ≤ 1 / (1000 * kerExcess R.C R.c) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  refine ⟨cpN, hcpN0, hcpNcp, ?_⟩
  intro S hadm hSu hN1 hN2 F hF ε D hε hD
  -- constants of the barrier and of the loss
  set M := lemmaNM Cw with hMdef
  have hcst : 0 ≤ cstarN Cw := by unfold cstarN; positivity
  have hM4 : 4 ≤ M := by simp only [hMdef, lemmaNM]; linarith
  have hNM : M + 3 ≤ N := by
    have h1 : 3 * cstarN Cw / 2 + 7 ≤ N := le_trans (le_max_right _ _) hN
    simp only [hMdef, lemmaNM]; linarith
  have hN5 : 5 ≤ N := by
    have h1 : (20 : ℝ) ≤ N := le_trans (le_max_left _ _) hN
    linarith
  set ε₁ := min (min ε (c / 4)) 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (lt_min hε (by positivity)) one_pos
  have hε₁ε : ε₁ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hε₁c : 4 * ε₁ ≤ c := by
    have : ε₁ ≤ c / 4 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  set a := ε₁ / 100 with ha
  have ha0 : 0 < a := by positivity
  set F₁ := max F (2 * R.C + 3 * M + 6) with hF₁
  have hF₁F : F ≤ F₁ := le_max_left _ _
  have hF₁0 : 0 < F₁ := lt_of_lt_of_le hF hF₁F
  have hF₁C : 2 * R.C + 3 * M + 6 ≤ F₁ := le_max_right _ _
  set A := F₁ + R.C + 2 with hA
  have hA0 : 0 < A := by positivity
  -- the regime and the weights
  obtain ⟨Cc, hCc0, hconvAll⟩ := weight_convolution cpN θ F₁ hcpN0 hθ hθ2 hF₁0
  obtain ⟨C'₀, Wlp, hlp⟩ := R.longPair θ cpN F₁ hθ hθ2 hcpN0 hF₁0
  set C' := max C'₀ 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  obtain ⟨Wdy, hdy⟩ := R.dyson
  obtain ⟨Wker, hkerR⟩ := R.kernel A hA0
  obtain ⟨Wbud, hbudR⟩ := R.budget
  obtain ⟨C₁, hgm⟩ := lemmaNOffset_gen_moment R I
  -- the exponent `r`, the bracket rate and the failure exponent of the inputs
  set E₀ := lemmaNE0 Cw with hE₀
  have hE₀0 : 0 ≤ E₀ := by simp only [hE₀, lemmaNE0]; positivity
  set r : ℕ := ⌈(3 * (E₀ + 1) + D + 2) / (148 * a)⌉₊ + 1 with hrdef
  have hr : 1 ≤ r := by omega
  have hr148 : 3 * (E₀ + 1) + D + 2 ≤ 148 * a * r := by
    have h1 := Nat.le_ceil ((3 * (E₀ + 1) + D + 2) / (148 * a))
    have h2 : ((3 * (E₀ + 1) + D + 2) / (148 * a)) ≤ r := by
      simp only [hrdef]; push_cast; linarith
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  set bΓ := lemmaNb0 Cw r with hbΓ
  have hbΓ0 : 0 < bΓ := lemmaN_b0_pos hCw hr
  set ρm := cstarN Cw * r + E₀ + 1 with hρm
  set CK := 15 + 2 * F₁ + max C₁ 0 with hCK
  have hCK0 : 0 ≤ CK := by
    have := le_max_right C₁ 0
    positivity
  set Dp := 2 * (3 * ρm + CK + D + 10) with hDp
  have hDp0 : 0 < Dp + 1 := by positivity
  -- the weighted sampling and the moments
  obtain ⟨CS, Wsw, hswI⟩ := I.sw cpN θ F₁ 4 (Dp + 1) hcpN0 hcpN1 hθ hθ2 hF₁0 (by norm_num) hDp0
  set CS' := max CS 0 with hCS'
  set p : ℕ := ⌈CS'⌉₊ + 2 with hpdef
  have hp : 2 ≤ p := by omega
  have hpCS : CS' ≤ p := by
    have := Nat.le_ceil CS'
    simp only [hpdef]; push_cast; linarith
  obtain ⟨Cp, Wgm, hgmp⟩ := hgm p (by omega)
  -- the inputs at loss `W^a` and failure `W^{-(D'+1)}`
  obtain ⟨Wop, hopW⟩ := hN2.op a (Dp + 1) ha0 hDp0
  obtain ⟨Whs, hhsW⟩ := hN2.hs a (Dp + 1) ha0 hDp0
  obtain ⟨Wavg, havgW⟩ := hN2.avg a (Dp + 1) ha0 hDp0
  obtain ⟨WN1, hN1W⟩ := hN1.pair F₁ hF₁0 a (Dp + 1) ha0 hDp0
  obtain ⟨WN1', hN1W'⟩ := hN1.pair F hF ε D hε hD
  -- thresholds in `W`
  set κ := 2 * (1 + 1 / 100) * Cw with hκ
  set Λ₁ := ρm / rateA12 (1 / 100) (1 / (2 * r)) κ r with hΛ₁
  set Λ₂ := (rateA12 (1 / 100) (1 / (2 * r)) κ r + rateMulC12 (1 / 100) (1 / (2 * r)) r) /
    (r * κ) with hΛ₂
  set Ccut := lemmaNCutC (1 / 100) (1 / (2 * r)) r with hCcut
  set lq : ℝ := Real.log 1.001 with hlq
  have hlq0 : 0 < lq := Real.log_pos (by norm_num)
  set K₁ := 1000 * CS' / (2 * lq) with hK₁
  set K₂ := 1000 * (Real.log 2 / (2 * lq) + 3) with hK₂
  set Cbig := max 2 (max (8 * Cw) (max Cc (max C' (max (1 / bΓ) (2 * K₂))))) with hCbig
  obtain ⟨Wbig, hbig⟩ := lemmaN_large_const Cbig ha0
  obtain ⟨Wql, hql⟩ := lemmaN_large_log (2 * K₁) ha0
  obtain ⟨Wlg, hlg⟩ := lemmaN_large_logpow (k := 2 / θ) (by positivity) ha0
  obtain ⟨Wsh, hsh⟩ := lemmaN_weight_short ha0
  obtain ⟨Wex, hex⟩ := lemmaN_large_exp 18 (2 * R.C + 4 + 3 * M) hcpN0
  set Wpl := max 1000 (max ⌈4 * Λ₁⌉₊ (max ⌈4 * (2 ^ (2 * r) + Λ₂)⌉₊ (max ⌈Ccut⌉₊
    ⌈max Cp 0 + 1⌉₊))) with hWpl
  refine ⟨max Wpl (max (max Wbig (max Wql (max Wlg (max Wsh Wex))))
    (max (max Wlp (max Wdy (max Wker Wbud))) (max (max Wsw Wgm)
      (max (max Wop Whs) (max Wavg (max WN1 WN1')))))), fun W hW q hq => ?_⟩
  simp only [hWpl, max_le_iff] at hW
  obtain ⟨⟨hW1000, hWΛ₁, hWΛ₂, hWCcut, hWCp⟩, ⟨hWbig, hWql, hWlg, hWsh, hWex⟩,
    ⟨hWlp, hWdy, hWker, hWbud⟩, ⟨hWsw, hWgm⟩, ⟨hWop, hWhs⟩, hWavg, hWN1, hWN1'⟩ := hW
  -- the step point
  have hadmq := hadm W hq
  rcases q with ⟨g, E, L, s, t, v⟩
  obtain ⟨⟨d, hdJ, hreach⟩, hs, hsv, hvt, hst, ht3, hRN⟩ := hadmq
  change 1 / 2 ≤ s at hs
  change s ≤ v at hsv
  change v ≤ t at hvt
  change s < t at hst
  change (W : ℝ) ^ (-3 : ℝ) ≤ 1 - t at ht3
  change ((1 - s) / (1 - t)) ^ N * zetaProp g W L t ≤ (W : ℝ) ^ (-c) at hRN
  change CmpReach R.base W d ⟨g, E, L, t⟩ at hreach
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have ht1 : t < 1 := by
    have : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
    linarith only [this, ht3]
  have hreachu : ∀ u : ℝ, 1 / 2 ≤ u → u ≤ t → CmpReach R.base W d ⟨g, E, L, u⟩ :=
    fun u hu1 hu2 => CmpReach.earlier u hreach hu1 hu2
  obtain ⟨hL, hg, hroot, -⟩ := hdy W hWdy d ⟨g, E, L, t⟩ hdJ.le hreach
  change 3 ≤ L at hL
  change 0 ≤ g at hg
  -- the target in explicit form
  have hR1 : 1 ≤ (1 - s) / (1 - t) := lemmaN_R_ge hst.le ht1
  have hRM1 : 1 ≤ ((1 - s) / (1 - t)) ^ M := Real.one_le_rpow hR1 (by linarith only [hM4])
  show μ W L {ω | ∃ ab : Fin L × Fin L, (W : ℝ) ^ ε * (((1 - s) / (1 - t)) ^ M *
      zetaProp g W L v ^ 2 * weightFn cpN θ F W (ellProp g L v) (cycDist ab.1 ab.2)) <
    ‖flowErr W ⟨g, E, L, v⟩ ![ab.1, ab.2] ![true, false] ω‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D))
  rcases eq_or_lt_of_le hsv with hsv' | hsv'
  · -- at the start of the step the bound is (N1)
    subst hsv'
    refine le_trans (measure_mono ?_) (hN1W' W hWN1' _ hq)
    rintro ω ⟨ab, hab⟩
    refine ⟨ab, lt_of_le_of_lt ?_ hab⟩
    change (W : ℝ) ^ ε * (zetaProp g W L s ^ 2 *
      weightFn cp θ F W (ellProp g L s) (cycDist ab.1 ab.2)) ≤ _
    have hℓ : 0 < ellProp g L s := lt_of_lt_of_le one_pos
      (scale_facts g hg W L hW1 (by omega) s s (by linarith only [hs]) le_rfl
        (lt_of_le_of_lt hst.le ht1)).1
    have hw1 : weightFn cp θ F W (ellProp g L s) (cycDist ab.1 ab.2) ≤
        weightFn cpN θ F W (ellProp g L s) (cycDist ab.1 ab.2) :=
      lemmaN_weight_anti_c hcpNcp hℓ (Nat.cast_nonneg _)
    have hw0 : 0 ≤ weightFn cp θ F W (ellProp g L s) (cycDist ab.1 ab.2) :=
      (lemmaN_weight_pos cp θ F hW1 _ _).le
    have hz : 0 ≤ zetaProp g W L s ^ 2 := sq_nonneg _
    have hWε : 0 ≤ (W : ℝ) ^ ε := by positivity
    calc (W : ℝ) ^ ε * (zetaProp g W L s ^ 2 * weightFn cp θ F W (ellProp g L s) (cycDist ab.1 ab.2))
        ≤ (W : ℝ) ^ ε * (1 * zetaProp g W L s ^ 2 *
          weightFn cpN θ F W (ellProp g L s) (cycDist ab.1 ab.2)) := by
          rw [one_mul]; gcongr
      _ ≤ (W : ℝ) ^ ε * (((1 - s) / (1 - t)) ^ M * zetaProp g W L s ^ 2 *
          weightFn cpN θ F W (ellProp g L s) (cycDist ab.1 ab.2)) := by
          have : 0 ≤ weightFn cpN θ F W (ellProp g L s) (cycDist ab.1 ab.2) :=
            (lemmaN_weight_pos cpN θ F hW1 _ _).le
          gcongr
  -- the main case `s < v`
  have hL1 : 1 ≤ L := by omega
  have hW4 : 4 ≤ W := by omega
  have hW2 : 2 ≤ W := by omega
  have hv1 : v < 1 := lt_of_le_of_lt hvt ht1
  obtain ⟨S₀, hS₀card, hS₀b⟩ := hswI W hWsw d ⟨g, E, L, t⟩ hdJ.le hreach
  set p₀ : Fin L × Fin L := (⟨0, by omega⟩, ⟨0, by omega⟩) with hp₀
  set S' := insert p₀ S₀ with hS'
  have hS₀S' : S₀ ⊆ S' := Finset.subset_insert _ _
  have hS'ne : S'.Nonempty := Finset.insert_nonempty _ _
  -- the exponent of the surrogate
  set Xq := (Real.log 2 + CS' * Real.log W) / (2 * lq) with hXq
  set qq : ℕ := ⌈Xq⌉₊ + 1 with hqq
  have hqq1 : 1 ≤ qq := by omega
  have hlogW : 0 ≤ Real.log W := Real.log_nonneg hW1r
  have hcard : ((Fintype.card S' : ℕ) : ℝ) ≤ 2 * (W : ℝ) ^ CS' := by
    have h1 : (Fintype.card S' : ℕ) ≤ S₀.card + 1 := by
      rw [Fintype.card_coe]; exact Finset.card_insert_le _ _
    have h2 : (S₀.card : ℝ) ≤ (W : ℝ) ^ CS' :=
      hS₀card.trans (Real.rpow_le_rpow_of_exponent_le hW1r (le_max_left _ _))
    have h3 : (1 : ℝ) ≤ (W : ℝ) ^ CS' := Real.one_le_rpow hW1r (le_max_right _ _)
    have : ((Fintype.card S' : ℕ) : ℝ) ≤ (S₀.card : ℝ) + 1 := by exact_mod_cast h1
    linarith only [this, h2, h3]
  have hcard1 : 1 ≤ Fintype.card S' := by
    rw [Fintype.card_coe]; exact Finset.card_pos.2 hS'ne
  have hS : ((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / (2 * qq)) ≤ 1.001 := by
    have h := card_rpow_le_of_q (Fintype.card S') hcard1 (δq := 0.001) (by norm_num) hqq1 ?_
    · rw [show (1 : ℝ) + 0.001 = 1.001 by norm_num] at h; exact h
    have hlogc : Real.log (Fintype.card S' : ℕ) ≤ Real.log 2 + CS' * Real.log W := by
      have hc0 : (0 : ℝ) < (Fintype.card S' : ℕ) := by exact_mod_cast hcard1
      calc Real.log (Fintype.card S' : ℕ) ≤ Real.log (2 * (W : ℝ) ^ CS') :=
            Real.log_le_log hc0 hcard
        _ = Real.log 2 + CS' * Real.log W := by
            rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hW0 _).ne',
              Real.log_rpow hW0]
    have h1 : Real.log (Fintype.card S' : ℕ) / (2 * Real.log (1 + 0.001)) ≤ Xq := by
      rw [hXq, hlq, show (1 : ℝ) + 0.001 = 1.001 by norm_num]
      exact div_le_div_of_nonneg_right hlogc (by positivity)
    have h2 : Xq ≤ qq := by
      have := Nat.le_ceil Xq
      simp only [hqq]; push_cast; linarith only [this]
    linarith only [h1, h2]
  -- `ω = W^a` is large
  set ω := (W : ℝ) ^ a with hωdef
  have hbigW := hbig W hWbig
  have hω2 : 2 ≤ ω := le_trans (le_max_left _ _) hbigW
  have hω8 : 8 * Cw ≤ ω := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hbigW
  have hωCc : Cc ≤ ω :=
    le_trans (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hbigW
  have hωC' : C' ≤ ω := le_trans ((((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)) hbigW
  have hωb : 1 / bΓ ≤ ω := le_trans (((((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)) hbigW
  have hωK₂ : 2 * K₂ ≤ ω := le_trans (((((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)) hbigW
  have hωq : 1000 * ((qq : ℝ) + 1) ≤ ω := by
    have h1 : (qq : ℝ) ≤ Xq + 2 := by
      have := Nat.ceil_lt_add_one (show 0 ≤ Xq by positivity)
      simp only [hqq]; push_cast; linarith only [this]
    have h2 := hql W hWql
    have h3 : 1000 * (Xq + 3) = K₂ + K₁ * Real.log W := by
      simp only [hXq, hK₁, hK₂]; ring
    have h4 : 0 ≤ K₁ * Real.log W := by
      have : 0 ≤ CS' := le_max_right _ _
      positivity
    nlinarith only [h1, h2, h3, hωK₂, h4]
  -- scales and the regime at the terminal time
  obtain ⟨hℓv1, -, hℓvL, -, -, -, -⟩ :=
    scale_facts g hg W L hW1 hL1 v v (by linarith only [hs, hsv']) le_rfl hv1
  have hℓv0 : 0 < ellProp g L v := lt_of_lt_of_le one_pos hℓv1
  have hbudv := hbudR W hWbud d ⟨g, E, L, v⟩ hdJ.le (hreachu v (by linarith only [hs, hsv']) hvt)
  change gammaG g * L + L / ellProp g L v ≤ (W : ℝ) ^ R.C at hbudv
  have hγL : 0 ≤ gammaG g * L := by
    have : 0 < gammaG g := by unfold gammaG; positivity
    positivity
  have hLℓv : (L : ℝ) / ellProp g L v ≤ (W : ℝ) ^ R.C := by linarith only [hbudv, hγL]
  have hbuds := hbudR W hWbud d ⟨g, E, L, s⟩ hdJ.le (hreachu s hs (hsv.trans hvt))
  change gammaG g * L + L / ellProp g L s ≤ (W : ℝ) ^ R.C at hbuds
  have hLℓs : (L : ℝ) / ellProp g L s ≤ (W : ℝ) ^ R.C := by linarith only [hbuds, hγL]
  have hζt0 : 0 ≤ zetaProp g W L t := by
    unfold zetaProp
    have hℓt : 0 ≤ ellProp g L t := le_trans zero_le_one
      (scale_facts g hg W L hW1 hL1 t t (by linarith only [hs, hst]) le_rfl ht1).1
    have : 0 ≤ 1 - t := by linarith only [ht1]
    have : 0 < gammaG g := by unfold gammaG; positivity
    positivity
  have hR3 : (1 - s) / (1 - t) ≤ (W : ℝ) ^ 3 := by
    have h1t : 0 < 1 - t := by linarith only [ht1]
    have hW3 : (W : ℝ) ^ (-3 : ℝ) = ((W : ℝ) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hW0.le]; norm_cast
    rw [hW3] at ht3
    rw [div_le_iff₀ h1t]
    have h1 : 1 ≤ (W : ℝ) ^ 3 * (1 - t) := by
      have := mul_le_mul_of_nonneg_left ht3 (by positivity : (0 : ℝ) ≤ (W : ℝ) ^ 3)
      rwa [mul_inv_cancel₀ (by positivity)] at this
    linarith only [h1, hs]
  -- numerics at `W`
  have hωW : ω ≤ W := by
    calc ω = (W : ℝ) ^ a := rfl
      _ ≤ (W : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1r (by
          simp only [ha]; linarith only [hε₁1])
      _ = W := Real.rpow_one _
  have hω100 : ω ^ 100 = (W : ℝ) ^ ε₁ := by
    rw [hωdef, lemmaN_pow_rpow]; congr 1; simp only [ha]; push_cast; ring
  have hωε : ω ^ 100 ≤ (W : ℝ) ^ ε := by
    rw [hω100]; exact Real.rpow_le_rpow_of_exponent_le hW1r hε₁ε
  have hω100W : ω ^ 100 ≤ W := by
    rw [hω100]
    calc (W : ℝ) ^ ε₁ ≤ (W : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1r hε₁1
      _ = W := Real.rpow_one _
  have hω400 : ω ^ 400 = (W : ℝ) ^ (4 * ε₁) := by
    rw [hωdef, lemmaN_pow_rpow]; congr 1; simp only [ha]; push_cast; ring
  have hRP : ((1 - s) / (1 - t)) ^ 3 * ((1 - s) / (1 - t)) ^ M * zetaProp g W L t * ω ^ 400 ≤ 1 := by
    rw [hω400, show ((1 - s) / (1 - t)) ^ 3 * ((1 - s) / (1 - t)) ^ M =
      ((1 - s) / (1 - t)) ^ (3 + M) by
        rw [Real.rpow_add (by linarith only [hR1])]; norm_cast]
    exact lemmaN_RN hW1 hR1 hζt0 hRN (by linarith only [hNM]) hε₁c
  have hR5 : ((1 - s) / (1 - t)) ^ 5 * zetaProp g W L t * ω ^ 400 ≤ 1 := by
    rw [hω400, show ((1 - s) / (1 - t)) ^ 5 = ((1 - s) / (1 - t)) ^ (5 : ℝ) by norm_cast]
    exact lemmaN_RN hW1 hR1 hζt0 hRN hN5 hε₁c
  have hβ1 : (1 : ℝ) + 1 / (2 * r) ≤ 3 / 2 := by
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have : 1 / (2 * (r : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hr1]
    linarith only [this]
  have hden : 0 < 2 * Cw * (1 + 1 / (2 * r)) := by positivity
  have hR4M : ((1 - s) / (1 - t)) ^ 4 ≤ ((1 - s) / (1 - t)) ^ M := by
    rw [show ((1 - s) / (1 - t)) ^ 4 = ((1 - s) / (1 - t)) ^ (4 : ℝ) by norm_cast]
    exact Real.rpow_le_rpow_of_exponent_le hR1 hM4
  have hω26 : ω ^ 26 ≤ ω ^ 100 := pow_le_pow_right₀ (by linarith only [hω2]) (by norm_num)
  have hJ : 2 * (((1 - s) / (1 - t)) ^ 4 * ω ^ 25) ≤
      ω ^ 100 * ((1 - s) / (1 - t)) ^ M / (2 * Cw * (1 + 1 / (2 * r))) := by
    rw [le_div_iff₀ hden]
    have h1 : 2 * (2 * Cw * (1 + 1 / (2 * r))) ≤ ω := by nlinarith only [hβ1, hω8, hCw]
    have h2 : 2 * (((1 - s) / (1 - t)) ^ 4 * ω ^ 25) * (2 * Cw * (1 + 1 / (2 * r))) ≤
        ((1 - s) / (1 - t)) ^ 4 * ω ^ 26 := by
      have : 0 ≤ ((1 - s) / (1 - t)) ^ 4 * ω ^ 25 := by positivity
      calc 2 * (((1 - s) / (1 - t)) ^ 4 * ω ^ 25) * (2 * Cw * (1 + 1 / (2 * r))) =
          (((1 - s) / (1 - t)) ^ 4 * ω ^ 25) * (2 * (2 * Cw * (1 + 1 / (2 * r)))) := by ring
        _ ≤ (((1 - s) / (1 - t)) ^ 4 * ω ^ 25) * ω := by gcongr
        _ = ((1 - s) / (1 - t)) ^ 4 * ω ^ 26 := by ring
    calc _ ≤ ((1 - s) / (1 - t)) ^ 4 * ω ^ 26 := h2
      _ ≤ ((1 - s) / (1 - t)) ^ M * ω ^ 100 := by
          have : 0 ≤ ((1 - s) / (1 - t)) ^ 4 := by positivity
          gcongr
      _ = ω ^ 100 * ((1 - s) / (1 - t)) ^ M := by ring
  have hJ1 : 1 ≤ ω ^ 100 * ((1 - s) / (1 - t)) ^ M / (2 * Cw * (1 + 1 / (2 * r))) := by
    rw [le_div_iff₀ hden, one_mul]
    have h1 : 2 * Cw * (1 + 1 / (2 * r)) ≤ ω := by nlinarith only [hβ1, hω8, hCw]
    have h2 : ω ≤ ω ^ 100 := le_self_pow₀ (by linarith only [hω2]) (by norm_num)
    have h3 : ω ^ 100 ≤ ω ^ 100 * ((1 - s) / (1 - t)) ^ M :=
      le_mul_of_one_le_right (by positivity) hRM1
    linarith only [h1, h2, h3]
  have hκnum := lemmaN_kappa_num hW1000 hCw hωq
  have hbΓnum : 1.003 * (1 / (2 * ω)) ≤ bΓ := by
    have h1 : 1 / ω ≤ bΓ := by
      rw [div_le_iff₀ (by linarith only [hω2])]
      rw [div_le_iff₀ hbΓ0] at hωb
      linarith only [hωb]
    have h2 : 1.003 * (1 / (2 * ω)) ≤ 1 / ω := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by linarith only [hω2])]
      nlinarith only [hω2]
    linarith only [h1, h2]
  have hlH := hlg W hWlg
  have hlH32 : Real.log W ^ ((3 : ℝ) / 2) ≤ Real.log W ^ (2 / θ) :=
    Real.rpow_le_rpow_of_exponent_le (lemmaN_log_ge_one (by omega)) (by
      rw [le_div_iff₀ hθ]; linarith only [hθ2])
  have hRMW : ((1 - s) / (1 - t)) ^ M ≤ (W : ℝ) ^ (3 * M) := by
    calc ((1 - s) / (1 - t)) ^ M ≤ ((W : ℝ) ^ (3 : ℝ)) ^ M := by
          refine Real.rpow_le_rpow (by linarith only [hR1]) ?_ (by linarith only [hM4])
          rw [show ((W : ℝ) ^ (3 : ℝ)) = (W : ℝ) ^ (3 : ℕ) by norm_cast]; exact hR3
      _ = (W : ℝ) ^ (3 * M) := by rw [← Real.rpow_mul hW0.le]
  have hLr := lemmaN_Lr_num (by omega) (Nat.cast_nonneg L) hℓv0 hLℓv
    (by linarith only [hRC]) (by positivity) hωW hω100W (by positivity) hRMW
    (by linarith only [hM4]) hC'0 (hωC'.trans hωW) hF₁C (by positivity) (hex W hWex)
  -- the off-set constant
  have hq2W : (qq : ℝ) + 2 ≤ W := by linarith only [hωq, hωW]
  have hS1 : ((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / qq) ≤ 2 := by
    have e : ((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / qq) =
        (((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / (2 * qq))) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1
      have : (qq : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
      norm_num
    rw [e]
    calc (((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / (2 * qq))) ^ 2 ≤ 1.001 ^ 2 := by gcongr
      _ ≤ 2 := by norm_num
  have hS2 : ((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / p) ≤ 2 * W := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    calc ((Fintype.card S' : ℕ) : ℝ) ^ ((1 : ℝ) / p) ≤ (2 * (W : ℝ) ^ CS') ^ ((1 : ℝ) / p) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hcard (by positivity)
      _ = (2 : ℝ) ^ ((1 : ℝ) / p) * (W : ℝ) ^ (CS' / p) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hW0.le]; ring_nf
      _ ≤ 2 * W := by
          gcongr
          · calc (2 : ℝ) ^ ((1 : ℝ) / p) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
                    rw [div_le_one hp0]; exact_mod_cast (by omega : 1 ≤ p))
              _ = 2 := Real.rpow_one 2
          · calc (W : ℝ) ^ (CS' / p) ≤ (W : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hW1r (by rw [div_le_one hp0]; exact hpCS)
              _ = W := Real.rpow_one _
  have hCcutW : Ccut ≤ W := (Nat.le_ceil Ccut).trans (by exact_mod_cast hWCcut)
  have hCpW : max Cp 0 + 1 ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWCp)
  have hCcut0 : 0 ≤ Ccut := by simp only [hCcut, lemmaNCutC]; positivity
  have hK := lemmaN_K_le hW2 hCcut0 hCcutW (by positivity) hq2W (by positivity) hS1
    (by positivity) hS2 hCpW (F₁ := F₁) (C₁ := C₁)
  -- the thresholds of the total
  have hΛ₁W : 4 * Λ₁ ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWΛ₁)
  have hΛ₂W : 4 * (2 ^ (2 * r) + Λ₂) ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWΛ₂)
  have hA12 : 0 < rateA12 (1 / 100) (1 / (2 * r)) κ r := by unfold rateA12; positivity
  have hΛ₁0 : 0 ≤ Λ₁ := by
    have : 0 ≤ ρm := by positivity
    positivity
  have hmain : 4 * Λ₁ * (W : ℝ) ^ (3 * (E₀ + 1)) ≤ ((W : ℝ) ^ a) ^ (148 * r) * (W : ℝ) ^ (-D) := by
    rw [lemmaN_pow_rpow, ← Real.rpow_add hW0]
    have h1 : (W : ℝ) ^ (3 * (E₀ + 1) + 2) ≤ (W : ℝ) ^ (((148 * r : ℕ) : ℝ) * a + -D) :=
      Real.rpow_le_rpow_of_exponent_le hW1r (by push_cast; linarith only [hr148])
    have h2 : (W : ℝ) ^ (3 * (E₀ + 1) + 2) = (W : ℝ) ^ (3 * (E₀ + 1)) * (W : ℝ) ^ 2 := by
      rw [Real.rpow_add hW0]; norm_cast
    have h3 : 4 * Λ₁ ≤ (W : ℝ) ^ 2 := by nlinarith only [hΛ₁W, hW1r]
    have h4 : 0 ≤ (W : ℝ) ^ (3 * (E₀ + 1)) := by positivity
    calc 4 * Λ₁ * (W : ℝ) ^ (3 * (E₀ + 1)) ≤ (W : ℝ) ^ 2 * (W : ℝ) ^ (3 * (E₀ + 1)) := by gcongr
      _ = (W : ℝ) ^ (3 * (E₀ + 1) + 2) := by rw [h2]; ring
      _ ≤ _ := h1
  have hΛ1 : Λ₁ ≤ W := by linarith only [hΛ₁W, hΛ₁0]
  -- the weight convolution at the terminal scale
  have hLW : (L : ℝ) * (W : ℝ) ^ (-(F₁ / 2)) ≤ ellProp g L v := by
    have h1 : (L : ℝ) ≤ (W : ℝ) ^ R.C * ellProp g L v := by
      rw [div_le_iff₀ hℓv0] at hLℓv; linarith only [hLℓv]
    have h2 : (W : ℝ) ^ R.C * (W : ℝ) ^ (-(F₁ / 2)) ≤ 1 := by
      rw [← Real.rpow_add hW0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith only [hF₁C, hM4, hRC])
    calc (L : ℝ) * (W : ℝ) ^ (-(F₁ / 2)) ≤ (W : ℝ) ^ R.C * ellProp g L v * (W : ℝ) ^ (-(F₁ / 2)) :=
          by gcongr
      _ = ((W : ℝ) ^ R.C * (W : ℝ) ^ (-(F₁ / 2))) * ellProp g L v := by ring
      _ ≤ 1 * ellProp g L v := by gcongr
      _ = ellProp g L v := one_mul _
  have hζu1 : ∀ u ∈ Set.Icc s v, zetaProp g W L u ≤ 1 := by
    intro u hu
    have h1 := (scale_facts g hg W L hW1 hL1 u t (by linarith only [hu.1, hs])
      (hu.2.trans hvt) ht1).2.2.2.2.1
    have h2 : zetaProp g W L t ≤ 1 := by
      have hRN1 : 1 ≤ ((1 - s) / (1 - t)) ^ N := Real.one_le_rpow hR1 (by linarith only [hN5])
      have hWc : (W : ℝ) ^ (-c) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1r
        (by linarith only [hc])
      nlinarith only [hRN, hRN1, hWc, hζt0]
    exact h1.trans h2
  -- The mixed-pair bound at fixed `W`
  have hatW := lemmaN_atW g E W L s t v hW4 hL hg hroot hs hsv' hvt ht1
    (Cw := Cw) (cp := cp) (cpN := cpN) (θ := θ) (F := F) (F₁ := F₁) (ε := ε) (ω := ω) (M := M)
    (C₀ := R.C) (c₀ := R.c) (A := A) (RC := R.C) (C' := C') (Cc := Cc)
    (lH := Real.log W ^ (2 / θ)) (εw := Real.exp (-(cpN * Real.log W ^ (2 : ℝ))) +
      (W : ℝ) ^ (-F₁)) (bΓ := bΓ) (δ₁ := (W : ℝ) ^ (-(Dp + 1))) (Cp := Cp) (C₁ := C₁)
    (r := r) (q := qq) (p := p)
    hCw hCc0.le hcpN0 hcpNcp hθ hθ2 hF hF₁F hRc (by linarith only [hRC]) hcpNc hcpNk rfl hr hqq1 hp
    (by positivity) hbΓ0.le S₀ S' hS₀S' hS'ne hS
    (fun u hu a b => (hkerR W hWker d ⟨g, E, L, u⟩ hdJ.le
      (hreachu u (by linarith only [hu.1, hs]) (hu.2.trans hvt)) a b).2)
    (fun u hu a b hab => by
      have h1 := hlp W hWlp d ⟨g, E, L, u⟩ hdJ.le
        (hreachu u (by linarith only [hu.1, hs]) (hu.2.trans hvt)) a b true false hab
      refine h1.trans ?_
      have : 0 ≤ zetaProp g W L u ^ 2 * weightFn cpN θ F₁ W (ellProp g L u) (cycDist a b) :=
        mul_nonneg (sq_nonneg _) (lemmaN_weight_pos cpN θ F₁ hW1 _ _).le
      calc C'₀ * zetaProp g W L u ^ 2 * weightFn cpN θ F₁ W (ellProp g L u) (cycDist a b) =
          C'₀ * (zetaProp g W L u ^ 2 * weightFn cpN θ F₁ W (ellProp g L u) (cycDist a b)) := by
            ring
        _ ≤ C' * (zetaProp g W L u ^ 2 * weightFn cpN θ F₁ W (ellProp g L u) (cycDist a b)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) this
        _ = _ := by ring)
    hLℓs
    (fun u hu a b => hgmp W hWgm d ⟨g, E, L, u⟩ hdJ.le
      (hreachu u (by linarith only [hu.1, hs]) (hu.2.trans hvt)) (hζu1 u hu) a b)
    (fun x y => hconvAll W L hW1 hL1 (ellProp g L v) hℓv1 hℓvL hLW x y)
    (fun x y hxy => hsh W hWsh cpN θ F₁ hcpN0.le hcpN1 hθ hθ2 (ellProp g L v) (cycDist x y)
      hℓv0 (Nat.cast_nonneg _) hxy)
    (fun x y hxy => lemmaN_weight_far hcpN0.le hθ hW1 hℓv0 hxy)
    (fun u hu => hopW W hWop ⟨g, E, L, s, t, u⟩ (hSu W _ hq u hu.1.le hu.2.le))
    (fun u hu => hhsW W hWhs ⟨g, E, L, s, t, u⟩ (hSu W _ hq u hu.1.le hu.2.le))
    (fun u hu => havgW W hWavg ⟨g, E, L, s, t, u⟩ (hSu W _ hq u hu.1.le hu.2.le))
    (fun u hu1 huv => hS₀b u v hu1 huv hvt)
    (hN1W W hWN1 _ hq)
    hω2 hωε (by linarith only [hω8, hCw]) hωCc hC'0 hωC' hlH hlH32 (by positivity) hM4 hRP hR5
    hJ hJ1 hκnum hbΓnum hLr
  have htot := lemmaN_total_le hW2 hCw hr ha0 hbΓ0.le le_rfl hsv hvt ht1 hR3
    (by linarith only [hω8, hCw]) hmain (by positivity) hK hCK0 hD rfl hΛ1 hΛ₂W
  exact hatW.trans (ENNReal.ofReal_le_ofReal htot)


/-- The mixed-pair bound at a fixed time: under the strengthened (5.38) [gc:eq:one-step] with
`N ≥ N₀(C_w)`, the pair component of (5.22) [gc:eq:one-step-input] at the start (N1) and the Step 1
envelopes (N2), with the crude moments (N3) and the weighted sampling (5.34)
[fo:eq:weighted-sampling-input] (N4) from the inputs and the regime bounds (N5), give
`|D₂(u; a, b; +, -)| ≺ R^M ζ_u² w_u(a - b)`, `M = c_*/2 + 4`, the barrier `J₀ = W^εR^M` replacing
(C.17) [gc:eq:spatialstop]. -/
theorem lemmaN_mixed (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N : ℝ) (hc : 0 < c)
    (hcp : 0 < cp) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hN : lemmaNN0 I.Cw ≤ N) :
    ∃ cpN : ℝ, 0 < cpN ∧ cpN ≤ cp ∧ ∀ S : ℕ → Set StepPt, (∀ W, S W ⊆ {q | StepAdm R c N W q}) →
      (∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
        (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W) →
      OneStepInput cp θ (fun q : StepPt => q.at q.s) S → Step1Out S →
      ∀ F : ℝ, 0 < F → PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
        (fun W q ab ω => flowErr W (q.at q.u) ![ab.1, ab.2] ![true, false] ω)
        (fun W q ab => q.ratio ^ lemmaNM I.Cw * zetaProp q.g W q.L q.u ^ 2 *
          weightFn cpN θ F W (ellProp q.g q.L q.u) (cycDist ab.1 ab.2)) := by
  exact lemmaN_mixed_aux R I c cp θ N hc hcp hθ hθ2 hN

end LSBA
