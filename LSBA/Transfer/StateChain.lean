import LSBA.Transfer.AdaptedProduct

/-!
# The state chain

States `X = (C, v)` with `C` unitary and `‖v‖ = 1`; the state update (11.7) [lg:eq:update] and its
one-step increment `c`; the chain `X_i` driven by the blocks; the additive growth (11.8)
[lg:eq:additive-growth] `ℓ_n = Σ_{i<n} c_i`; the bound (11.13) [uvg:eq:global] for `c`; the
observables `m_k`, `f_k` (`k ∈ ℤ`) of (11.10) [lg:eq:observables] with their bounds, values at `k =
0` and conjugation; joint measurability of the update and the increment.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- A state `(C, v)` of the chain of Section 11.1 [lg:sec:scalar-growth]. -/
abbrev State (W : ℕ) : Type := Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W)

/-- `C` is unitary and `v` is a unit vector. -/
def IsState {W : ℕ} (X : State W) : Prop :=
  X.1 ∈ Matrix.unitaryGroup (Fin W) ℂ ∧ ‖X.2‖ = 1

/-- The quadratic form `v* A v`. -/
def vecForm {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) : ℂ :=
  inner ℂ v (Matrix.toEuclideanLin A v)

/-- `F(C, V)^{-*} v`, the unnormalized direction of (11.7) [lg:eq:update]. -/
def stepVec (g E : ℝ) {W : ℕ} (X : State W) (V : Matrix (Fin W) (Fin W) ℂ) :
    EuclideanSpace ℂ (Fin W) :=
  Matrix.toEuclideanLin ((stepF g E X.1 V)⁻¹ᴴ) X.2

/-- The increment `c = -log ‖F(C, V)^{-*} v‖` of (11.7) [lg:eq:update]. -/
def stepInc (g E : ℝ) {W : ℕ} (X : State W) (V : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  -Real.log ‖stepVec g E X V‖

/-- The state update `(C, v) ↦ (C', v')` of (11.3) [lg:eq:matrix-update] and (11.7)
[lg:eq:update]. -/
def stepState (g E : ℝ) {W : ℕ} (X : State W) (V : Matrix (Fin W) (Fin W) ℂ) : State W :=
  (stepC g E X.1 V, (stepPhase E * ((‖stepVec g E X V‖⁻¹ : ℝ) : ℂ)) • stepVec g E X V)

/-- The states `(C_i, v_i)` along the blocks `V 0, V 1, …` (Section 11.1
[lg:sec:scalar-growth]). -/
def chainState (g E : ℝ) {W : ℕ} (X₀ : State W) (V : ℕ → Matrix (Fin W) (Fin W) ℂ) :
    ℕ → State W
  | 0 => X₀
  | i + 1 => stepState g E (chainState g E X₀ V i) (V i)

theorem chainState_fst (g E : ℝ) {W : ℕ} (X₀ : State W) (V : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (i : ℕ) : (chainState g E X₀ V i).1 = chainC g E X₀.1 V i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change stepC g E (chainState g E X₀ V i).1 (V i) = stepC g E (chainC g E X₀.1 V i) (V i)
    rw [ih]

private theorem sc_norm_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) :
    ‖Matrix.toEuclideanLin A v‖ ≤ ‖A‖ * ‖v‖ :=
  (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) A).le_opNorm v

private theorem sc_lin_mul {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) :
    Matrix.toEuclideanLin (A * B) v = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

private theorem sc_lin_one {W : ℕ} (v : EuclideanSpace ℂ (Fin W)) :
    Matrix.toEuclideanLin (1 : Matrix (Fin W) (Fin W) ℂ) v = v := by
  simp

private theorem sc_lin_smul {W : ℕ} (a : ℂ) (A : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) :
    Matrix.toEuclideanLin (a • A) v = a • Matrix.toEuclideanLin A v := by
  simp

private theorem sc_inner_lin_conjTranspose {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v w : EuclideanSpace ℂ (Fin W)) :
    inner ℂ v (Matrix.toEuclideanLin Aᴴ w) = inner ℂ (Matrix.toEuclideanLin A v) w := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

private theorem sc_norm_stepPhase (E : ℝ) : ‖stepPhase E‖ = 1 := by
  unfold stepPhase
  rw [show -((freeAngle E : ℂ) * Complex.I) = ((-freeAngle E : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem sc_normalH_nonneg (E : ℝ) : 0 ≤ normalH E := by
  unfold normalH freeAngle
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg (E / 2))
    (Real.arccos_le_pi (E / 2))
  positivity

/-- `F(C, V)* · (F(C, V)^{-*} v) = v`. -/
private theorem sc_stepVec_adj (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    Matrix.toEuclideanLin (stepF g E X.1 V)ᴴ (stepVec g E X V) = X.2 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_stepF g E hX.1 hV)
  unfold stepVec
  rw [← sc_lin_mul, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hdet,
    Matrix.conjTranspose_one, sc_lin_one]

private theorem sc_norm_stepVec_pos (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) : 0 < ‖stepVec g E X V‖ := by
  refine norm_pos_iff.mpr fun h0 => ?_
  have h1 := sc_stepVec_adj g E hX hV
  rw [h0, map_zero] at h1
  have h2 : ‖X.2‖ = 0 := by rw [← h1, norm_zero]
  rw [hX.2] at h2
  exact one_ne_zero h2

/-- The update of (11.3) [lg:eq:matrix-update] and (11.7) [lg:eq:update] maps states to
states. -/
theorem isState_stepState (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) : IsState (stepState g E X V) := by
  refine ⟨stepC_mem_unitaryGroup g E hX.1 hV, ?_⟩
  have hw := sc_norm_stepVec_pos g E hX hV
  change ‖(stepPhase E * ((‖stepVec g E X V‖⁻¹ : ℝ) : ℂ)) • stepVec g E X V‖ = 1
  rw [norm_smul, norm_mul, sc_norm_stepPhase, Complex.norm_real, norm_inv, norm_norm, one_mul,
    inv_mul_cancel₀ hw.ne']

/-- `ℓ_n(C₀, v₀) = -log ‖D_n(C₀; E)^{-*} v₀‖` of (11.8) [lg:eq:additive-growth]. -/
def ellN (g E : ℝ) {W : ℕ} (C₀ : Matrix (Fin W) (Fin W) ℂ) (v₀ : EuclideanSpace ℂ (Fin W))
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) : ℝ :=
  -Real.log ‖Matrix.toEuclideanLin ((normalD g E C₀ V n)⁻¹ᴴ) v₀‖

private theorem sc_isState_chainState (g E : ℝ) {W : ℕ} {X₀ : State W} (hX₀ : IsState X₀)
    {V : ℕ → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ k, (V k).IsHermitian) (i : ℕ) :
    IsState (chainState g E X₀ V i) := by
  induction i with
  | zero => exact hX₀
  | succ i ih => exact isState_stepState g E ih (hV i)

private theorem sc_isUnit_stepProd (g E : ℝ) {W : ℕ} {C₀ : Matrix (Fin W) (Fin W) ℂ}
    (hC₀ : C₀ ∈ Matrix.unitaryGroup (Fin W) ℂ) {V : ℕ → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ k, (V k).IsHermitian) (n : ℕ) : IsUnit (stepProd g E C₀ V n) := by
  induction n with
  | zero => exact isUnit_one
  | succ n ih => exact (isUnit_stepF g E (chainC_mem_unitaryGroup g E hC₀ hV n) (hV n)).mul ih

/-- `P_n^{-*} v₀ = s v_n` with `|s| = ∏_{i<n} ‖F_i^{-*} v_i‖`, for the adapted product `P_n`. -/
private theorem sc_stepProd_inv (g E : ℝ) {W : ℕ} {X₀ : State W} (hX₀ : IsState X₀)
    {V : ℕ → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ k, (V k).IsHermitian) (n : ℕ) :
    ∃ s : ℂ, ‖s‖ = ∏ i ∈ Finset.range n, ‖stepVec g E (chainState g E X₀ V i) (V i)‖ ∧
      Matrix.toEuclideanLin ((stepProd g E X₀.1 V n)⁻¹ᴴ) X₀.2 =
        s • (chainState g E X₀ V n).2 := by
  induction n with
  | zero =>
    refine ⟨1, by simp, ?_⟩
    simp [stepProd, chainState]
  | succ n ih =>
    obtain ⟨s, hs, hsv⟩ := ih
    have hst := sc_isState_chainState g E hX₀ hV n
    have hw := sc_norm_stepVec_pos g E hst (hV n)
    have hμ : stepPhase E ≠ 0 := by
      intro h
      have := sc_norm_stepPhase E
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have hwc : ((‖stepVec g E (chainState g E X₀ V n) (V n)‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hw.ne'
    refine ⟨s * (((‖stepVec g E (chainState g E X₀ V n) (V n)‖ : ℝ) : ℂ) * (stepPhase E)⁻¹),
      ?_, ?_⟩
    · rw [norm_mul, norm_mul, norm_inv, sc_norm_stepPhase, hs, Finset.prod_range_succ,
        Complex.norm_real, norm_norm]
      simp
    · have hP : (stepProd g E X₀.1 V (n + 1))⁻¹ᴴ =
          (stepF g E (chainState g E X₀ V n).1 (V n))⁻¹ᴴ * (stepProd g E X₀.1 V n)⁻¹ᴴ := by
        rw [stepProd, ← chainState_fst, Matrix.mul_inv_rev, Matrix.conjTranspose_mul]
      rw [hP, sc_lin_mul, hsv, map_smul]
      change s • stepVec g E (chainState g E X₀ V n) (V n) = _
      change _ = _ • ((stepPhase E * ((‖stepVec g E (chainState g E X₀ V n) (V n)‖⁻¹ : ℝ) : ℂ)) •
        stepVec g E (chainState g E X₀ V n) (V n))
      rw [smul_smul]
      congr 1
      push_cast
      field_simp

/-- (11.8) [lg:eq:additive-growth]: `ℓ_n(C₀, v₀) = Σ_{i=1}^n c_i`. -/
theorem ellN_eq_sum {W : ℕ} {E : ℝ} (hE : |E| < 2) (g : ℝ) {X₀ : State W} (hX₀ : IsState X₀)
    {V : ℕ → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ k, (V k).IsHermitian) (n : ℕ) :
    ellN g E X₀.1 X₀.2 V n = ∑ i ∈ Finset.range n, stepInc g E (chainState g E X₀ V i) (V i) := by
  obtain ⟨s, hs, hsv⟩ := sc_stepProd_inv g E hX₀ hV n
  have hC₀ := hX₀.1
  have hPu : IsUnit (stepProd g E X₀.1 V n).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (sc_isUnit_stepProd g E hC₀ hV n)
  have hμ : stepPhase E ≠ 0 := by
    intro h
    have := sc_norm_stepPhase E
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hDinv : (normalD g E X₀.1 V n)⁻¹ =
      ((stepPhase E ^ n)⁻¹ : ℂ) • (stepProd g E X₀.1 V n)⁻¹ := by
    rw [normalD_eq hE g hC₀ hV n]
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (pow_ne_zero n hμ),
      one_smul, Matrix.mul_nonsing_inv _ hPu]
  have hnorm : ‖Matrix.toEuclideanLin ((normalD g E X₀.1 V n)⁻¹ᴴ) X₀.2‖ =
      ∏ i ∈ Finset.range n, ‖stepVec g E (chainState g E X₀ V i) (V i)‖ := by
    rw [hDinv, Matrix.conjTranspose_smul, sc_lin_smul, hsv, smul_smul, norm_smul, norm_mul,
      norm_star, norm_inv, norm_pow, sc_norm_stepPhase, hs, (sc_isState_chainState g E hX₀ hV n).2]
    simp
  have hpos : ∀ i ∈ Finset.range n,
      ‖stepVec g E (chainState g E X₀ V i) (V i)‖ ≠ 0 := fun i _ =>
    (sc_norm_stepVec_pos g E (sc_isState_chainState g E hX₀ hV i) (hV i)).ne'
  unfold ellN stepInc
  rw [hnorm, Real.log_prod hpos, Finset.sum_neg_distrib]

/-- The second half of (11.13) [uvg:eq:global]: `|c| ≤ log(1 + 2 h_θ g⁻¹ ‖V‖)`. -/
theorem abs_stepInc_le {g : ℝ} (hg : 0 < g) (E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    |stepInc g E X V| ≤ Real.log (1 + 2 * normalH E * ‖V‖ / g) := by
  have hF := norm_stepF_le hg E hX.1 hV
  have hw := sc_norm_stepVec_pos g E hX hV
  have hh := sc_normalH_nonneg E
  have hL : 1 ≤ 1 + 2 * normalH E * ‖V‖ / g := by
    have : 0 ≤ 2 * normalH E * ‖V‖ / g := by positivity
    linarith
  have hLpos : 0 < 1 + 2 * normalH E * ‖V‖ / g := lt_of_lt_of_le one_pos hL
  have hup : ‖stepVec g E X V‖ ≤ 1 + 2 * normalH E * ‖V‖ / g := by
    calc ‖stepVec g E X V‖ ≤ ‖(stepF g E X.1 V)⁻¹ᴴ‖ * ‖X.2‖ := sc_norm_le _ _
      _ = ‖(stepF g E X.1 V)⁻¹‖ := by rw [hX.2, mul_one, Matrix.l2_opNorm_conjTranspose]
      _ ≤ _ := hF.2
  have hlow : (1 + 2 * normalH E * ‖V‖ / g)⁻¹ ≤ ‖stepVec g E X V‖ := by
    have h1 : 1 ≤ (1 + 2 * normalH E * ‖V‖ / g) * ‖stepVec g E X V‖ := by
      calc (1 : ℝ) = ‖X.2‖ := hX.2.symm
        _ = ‖Matrix.toEuclideanLin (stepF g E X.1 V)ᴴ (stepVec g E X V)‖ := by
          rw [sc_stepVec_adj g E hX hV]
        _ ≤ ‖(stepF g E X.1 V)ᴴ‖ * ‖stepVec g E X V‖ := sc_norm_le _ _
        _ = ‖stepF g E X.1 V‖ * ‖stepVec g E X V‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ _ := by gcongr; exact hF.1
    rw [inv_le_iff_one_le_mul₀ hLpos]
    linarith
  unfold stepInc
  rw [abs_neg, abs_le]
  constructor
  · have := Real.log_le_log (inv_pos.mpr hLpos) hlow
    rw [Real.log_inv] at this
    linarith
  · exact Real.log_le_log hw hup

/-- `m_k(C) = W⁻¹ Tr C^k` of (11.10) [lg:eq:observables], `k ∈ ℤ`. -/
def obsM (k : ℤ) {W : ℕ} (X : State W) : ℂ := (W : ℂ)⁻¹ * (X.1 ^ k).trace

/-- `f_k(C) = v* C^k v` of (11.10) [lg:eq:observables], `k ∈ ℤ`. -/
def obsF (k : ℤ) {W : ℕ} (X : State W) : ℂ := vecForm (X.1 ^ k) X.2

private theorem sc_isUnit_det_of_mem {W : ℕ} {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) : IsUnit C.det :=
  Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hC)

private theorem sc_inv_eq_conjTranspose {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ) : U⁻¹ = Uᴴ := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff.mp hU

/-- Integer powers of a unitary matrix are unitary. -/
private theorem sc_zpow_mem {W : ℕ} {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (k : ℤ) : C ^ k ∈ Matrix.unitaryGroup (Fin W) ℂ := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast]
    exact pow_mem hC n
  · rw [Matrix.zpow_neg (sc_isUnit_det_of_mem hC), zpow_natCast,
      sc_inv_eq_conjTranspose (pow_mem hC n), ← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem (pow_mem hC n)

/-- `C^{-k} = (C^k)*` for unitary `C`. -/
private theorem sc_zpow_neg {W : ℕ} {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (k : ℤ) : C ^ (-k) = (C ^ k)ᴴ := by
  rw [Matrix.zpow_neg (sc_isUnit_det_of_mem hC), sc_inv_eq_conjTranspose (sc_zpow_mem hC k)]

/-- A unitary matrix preserves the Euclidean norm. -/
private theorem sc_norm_lin_unitary {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) :
    ‖Matrix.toEuclideanLin U v‖ = ‖v‖ := by
  have hUU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have h : inner ℂ (Matrix.toEuclideanLin U v) (Matrix.toEuclideanLin U v) = inner ℂ v v := by
    rw [← sc_inner_lin_conjTranspose, ← sc_lin_mul, hUU, sc_lin_one]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖Matrix.toEuclideanLin U v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h'

private theorem sc_norm_vecForm_le {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ) {v : EuclideanSpace ℂ (Fin W)} (hv : ‖v‖ = 1) :
    ‖vecForm U v‖ ≤ 1 := by
  unfold vecForm
  calc ‖inner ℂ v (Matrix.toEuclideanLin U v)‖ ≤ ‖v‖ * ‖Matrix.toEuclideanLin U v‖ :=
        norm_inner_le_norm _ _
    _ = 1 := by rw [sc_norm_lin_unitary hU, hv, mul_one]

/-- The diagonal entry `U i i` is the quadratic form of `U` at the basis vector `e_i`. -/
private theorem sc_diag_eq_vecForm {W : ℕ} (U : Matrix (Fin W) (Fin W) ℂ) (i : Fin W) :
    U i i = vecForm U (EuclideanSpace.single i (1 : ℂ)) := by
  unfold vecForm
  simp [Matrix.toLpLin_apply, EuclideanSpace.inner_single_left]

/-- `|m_k| ≤ 1` (11.10) [lg:eq:observables]. -/
theorem norm_obsM_le_one (k : ℤ) {W : ℕ} {X : State W} (hX : IsState X) : ‖obsM k X‖ ≤ 1 := by
  have hU := sc_zpow_mem hX.1 k
  have hdiag : ∀ i : Fin W, ‖(X.1 ^ k) i i‖ ≤ 1 := fun i => by
    rw [sc_diag_eq_vecForm (X.1 ^ k) i]
    exact sc_norm_vecForm_le hU (by simp)
  have htr : ‖(X.1 ^ k).trace‖ ≤ W := by
    calc ‖(X.1 ^ k).trace‖ = ‖∑ i, (X.1 ^ k) i i‖ := rfl
      _ ≤ ∑ i, ‖(X.1 ^ k) i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin W, (1 : ℝ) := Finset.sum_le_sum fun i _ => hdiag i
      _ = W := by simp
  unfold obsM
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos W with h0 | hpos
  · subst h0
    simp
  · calc (W : ℝ)⁻¹ * ‖(X.1 ^ k).trace‖ ≤ (W : ℝ)⁻¹ * W := by gcongr
      _ = 1 := inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hpos.ne')

/-- `|f_k| ≤ 1` (11.10) [lg:eq:observables]. -/
theorem norm_obsF_le_one (k : ℤ) {W : ℕ} {X : State W} (hX : IsState X) : ‖obsF k X‖ ≤ 1 := by
  exact sc_norm_vecForm_le (sc_zpow_mem hX.1 k) hX.2

/-- `m_0 = 1` and `m_{-k} = \overline{m_k}` (Section 11.1 [lg:sec:scalar-growth]). -/
theorem obsM_zero_neg {W : ℕ} (hW : 1 ≤ W) {X : State W} (hX : IsState X) (k : ℤ) :
    obsM 0 X = 1 ∧ obsM (-k) X = star (obsM k X) := by
  refine ⟨?_, ?_⟩
  · unfold obsM
    rw [zpow_zero, Matrix.trace_one, Fintype.card_fin]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega))
  · unfold obsM
    rw [sc_zpow_neg hX.1, Matrix.trace_conjTranspose, star_mul', star_inv₀, star_natCast]

/-- `f_0 = 1` and `f_{-k} = \overline{f_k}` (Section 11.1 [lg:sec:scalar-growth]). -/
theorem obsF_zero_neg {W : ℕ} {X : State W} (hX : IsState X) (k : ℤ) :
    obsF 0 X = 1 ∧ obsF (-k) X = star (obsF k X) := by
  refine ⟨?_, ?_⟩
  · unfold obsF vecForm
    rw [zpow_zero, sc_lin_one, inner_self_eq_norm_sq_to_K, hX.2]
    simp
  · unfold obsF vecForm
    rw [sc_zpow_neg hX.1, sc_inner_lin_conjTranspose, ← inner_conj_symm]
    rfl

/-- Matrix inversion is measurable (the adjugate formula, with `0⁻¹ = 0` on singular matrices). -/
private theorem sc_measurable_inv {W : ℕ} :
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

private theorem sc_measurable_stepF (g E : ℝ) (W : ℕ) :
    Measurable (fun p : State W × Matrix (Fin W) (Fin W) ℂ => stepF g E p.1.1 p.2) := by
  have : Continuous (fun p : State W × Matrix (Fin W) (Fin W) ℂ => stepF g E p.1.1 p.2) := by
    unfold stepF
    fun_prop
  exact this.measurable

private theorem sc_measurable_stepVec (g E : ℝ) (W : ℕ) :
    Measurable (fun p : State W × Matrix (Fin W) (Fin W) ℂ => stepVec g E p.1 p.2) := by
  have hF : Measurable
      (fun p : State W × Matrix (Fin W) (Fin W) ℂ => (stepF g E p.1.1 p.2)⁻¹ᴴ) :=
    (continuous_id.matrix_conjTranspose).measurable.comp
      (sc_measurable_inv.comp (sc_measurable_stepF g E W))
  have hv : Measurable (fun p : State W × Matrix (Fin W) (Fin W) ℂ => p.1.2) :=
    measurable_snd.comp measurable_fst
  have hc : Continuous (fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) =>
      Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) q.1 q.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM
  have e : (fun p : State W × Matrix (Fin W) (Fin W) ℂ => stepVec g E p.1 p.2) =
      (fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) =>
        Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) q.1 q.2) ∘
        (fun p : State W × Matrix (Fin W) (Fin W) ℂ => ((stepF g E p.1.1 p.2)⁻¹ᴴ, p.1.2)) := by
    funext p
    rfl
  rw [e]
  exact hc.measurable.comp (hF.prodMk hv)

/-- The state update is jointly measurable in the state and the block. -/
theorem measurable_stepState (g E : ℝ) (W : ℕ) :
    Measurable (fun p : State W × Matrix (Fin W) (Fin W) ℂ => stepState g E p.1 p.2) := by
  unfold stepState
  refine Measurable.prodMk ?_ ?_
  · have h1 : Continuous (fun p : State W × Matrix (Fin W) (Fin W) ℂ =>
        (p.1.1 + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (p.2 * (1 + p.1.1)))) := by
      fun_prop
    have h2 := sc_measurable_inv.comp (sc_measurable_stepF g E W)
    have h3 : Continuous (fun q : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
        q.1 * q.2) := by
      fun_prop
    have h4 := h3.measurable.comp (h1.measurable.prodMk h2)
    have h5 : Continuous (fun M : Matrix (Fin W) (Fin W) ℂ => -normalPhase E • M) := by
      fun_prop
    exact h5.measurable.comp h4
  · have hw := sc_measurable_stepVec g E W
    have hs : Measurable (fun p : State W × Matrix (Fin W) (Fin W) ℂ =>
        (stepPhase E * ((‖stepVec g E p.1 p.2‖⁻¹ : ℝ) : ℂ))) :=
      measurable_const.mul (Complex.measurable_ofReal.comp (measurable_norm.comp hw).inv)
    have hc : Continuous (fun q : ℂ × EuclideanSpace ℂ (Fin W) => q.1 • q.2) := by
      fun_prop
    exact hc.measurable.comp (hs.prodMk hw)

/-- The increment is jointly measurable in the state and the block. -/
theorem measurable_stepInc (g E : ℝ) (W : ℕ) :
    Measurable (fun p : State W × Matrix (Fin W) (Fin W) ℂ => stepInc g E p.1 p.2) := by
  unfold stepInc
  exact (Real.measurable_log.comp (measurable_norm.comp (sc_measurable_stepVec g E W))).neg

end LSBA
