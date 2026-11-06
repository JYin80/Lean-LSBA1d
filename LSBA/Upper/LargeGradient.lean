import LSBA.Upper.LargeGradState
import LSBA.Upper.LargeCorrector
import LSBA.Gauss.PoincarePoly

/-!
# Gradients and innovation variances

The conditional innovation variances `𝔼|M′ − P_g M|² ≤ C g⁻²W⁻²`, `𝔼|F′ − P_g F|² ≤ C g⁻²W⁻¹`,
`𝔼|c − P_g c|² ≤ C g⁻²W⁻¹` (proof of Lemma 11.2 [uvg:lem:drifts]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Hilbert–Schmidt sums -/

/-- The squared Hilbert–Schmidt norm `Σ_{i,j} |A_{ij}|²`. -/
private def lgrHs {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

private theorem lgr_norm_lin_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : ‖Matrix.toEuclideanLin A v‖ ≤ ‖A‖ * ‖v‖ :=
  (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) A).le_opNorm v

private theorem lgr_lin_apply {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) (i : Fin W) :
    Matrix.toEuclideanLin A v i = ∑ j, A i j * v j := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

/-- The operator norm is at most the Hilbert–Schmidt norm. -/
private theorem lgr_norm_sq_le_hs {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    ‖A‖ ^ 2 ≤ lgrHs A := by
  have h0 : 0 ≤ lgrHs A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hb : ‖A‖ ≤ Real.sqrt (lgrHs A) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
    change ‖Matrix.toEuclideanLin A v‖ ≤ _
    rw [← Real.sqrt_sq (norm_nonneg (Matrix.toEuclideanLin A v)), ← Real.sqrt_sq (norm_nonneg v),
      ← Real.sqrt_mul h0]
    refine Real.sqrt_le_sqrt ?_
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, lgrHs, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [lgr_lin_apply]
    calc ‖∑ j, A i j * v j‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 := by
          gcongr
          exact (norm_sum_le _ _).trans (le_of_eq (by simp))
      _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ‖A‖ ^ 2 ≤ Real.sqrt (lgrHs A) ^ 2 := by gcongr
    _ = lgrHs A := Real.sq_sqrt h0

/-- The Hilbert–Schmidt norm is at most `W` times the squared operator norm. -/
private theorem lgr_hs_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) : lgrHs A ≤ W * ‖A‖ ^ 2 := by
  unfold lgrHs
  rw [Finset.sum_comm]
  calc ∑ j, ∑ i, ‖A i j‖ ^ 2 ≤ ∑ _j : Fin W, ‖A‖ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h := lgr_norm_lin_le A (EuclideanSpace.single j 1)
        rw [show ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 by simp, mul_one] at h
        have h2 : ‖Matrix.toEuclideanLin A (EuclideanSpace.single j 1)‖ ^ 2 ≤ ‖A‖ ^ 2 := by
          gcongr
        rw [EuclideanSpace.norm_sq_eq] at h2
        simpa [lgr_lin_apply] using h2
    _ = W * ‖A‖ ^ 2 := by simp

/-- Cauchy–Schwarz for the trace pairing. -/
private theorem lgr_norm_trace_mul_sq_le {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) :
    ‖(A * B).trace‖ ^ 2 ≤ lgrHs A * lgrHs B := by
  have h1 : (A * B).trace = ∑ p : Fin W × Fin W, A p.1 p.2 * B p.2 p.1 := by
    simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]
  have hA : lgrHs A = ∑ p : Fin W × Fin W, ‖A p.1 p.2‖ ^ 2 := by
    simp [lgrHs, Fintype.sum_prod_type]
  have hB : lgrHs B = ∑ p : Fin W × Fin W, ‖B p.2 p.1‖ ^ 2 := by
    simp only [lgrHs, Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [h1, hA, hB]
  calc ‖∑ p : Fin W × Fin W, A p.1 p.2 * B p.2 p.1‖ ^ 2
      ≤ (∑ p : Fin W × Fin W, ‖A p.1 p.2‖ * ‖B p.2 p.1‖) ^ 2 := by
        gcongr
        exact (norm_sum_le _ _).trans (le_of_eq (by simp))
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- The Hilbert–Schmidt norm of the fresh block: `Σ |V_{ij}|² = W⁻¹ Σ_k ω_k²`. -/
private theorem lgr_hs_gueBlock (W : ℕ) (y : Ω W 1) :
    lgrHs (gueBlock W 1 y 0) = (W : ℝ)⁻¹ * ∑ k, y k ^ 2 := by
  have hpt : ∀ i j : Fin W, ‖gueBlock W 1 y 0 i j‖ ^ 2 =
      (W : ℝ)⁻¹ * ((y (0, i, j) ^ 2 + y (0, j, i) ^ 2) / 2) := by
    intro i j
    have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
    have hs : Real.sqrt (2 * W) ^ 2 = 2 * W := Real.sq_sqrt (by positivity)
    have hs1 : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW
    simp only [gueBlock, Matrix.of_apply]
    split_ifs with h1 h2
    · subst h1
      rw [norm_div, Complex.norm_real, Complex.norm_real, div_pow, Real.norm_eq_abs, sq_abs,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hs1]
      ring
    · rw [norm_div, Complex.norm_real, div_pow, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), hs, Complex.sq_norm]
      simp [Complex.normSq_apply]
      rcases eq_or_lt_of_le hW with h0 | h0
      · rw [← h0]; simp
      · field_simp
    · rw [norm_div, Complex.norm_real, div_pow, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), hs, Complex.sq_norm]
      simp [Complex.normSq_apply]
      rcases eq_or_lt_of_le hW with h0 | h0
      · rw [← h0]; simp
      · field_simp; ring
  simp only [lgrHs, hpt, ← Finset.mul_sum]
  congr 1
  rw [Fintype.sum_prod_type, Fin.sum_univ_one, Fintype.sum_prod_type]
  simp only [add_div, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y_1 => y (0, y_1, x) ^ 2 / 2)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (0 : Fin 1) = (0 : Fin 1) := rfl
  ring

/-! ### Coordinate gradients -/

private theorem lgr_sq_le_of_le {S c : ℝ} (hS : 0 ≤ S) (h : S ≤ c * Real.sqrt S) :
    S ≤ c ^ 2 := by
  have hr := Real.sqrt_nonneg S
  have hrr : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS
  nlinarith

/-- If a real-linear functional `L` on `ℝ^ι` satisfies `|L y| ≤ c |y|₂`, then
`Σ_i |L e_i|² ≤ 2 c²`. -/
private theorem lgr_sum_sq_le {ι : Type*} [Fintype ι] (L : (ι → ℝ) →L[ℝ] ℂ) {c : ℝ}
    (h : ∀ y, ‖L y‖ ≤ c * Real.sqrt (∑ i, y i ^ 2)) :
    ∑ i, ‖L (Pi.single i 1)‖ ^ 2 ≤ 2 * c ^ 2 := by
  have key : ∀ (a : ι → ℝ), (∀ i, a i = (L (Pi.single i 1)).re) ∨
      (∀ i, a i = (L (Pi.single i 1)).im) → ∑ i, a i ^ 2 ≤ c ^ 2 := by
    intro a ha
    have hLa : L a = ∑ i, (a i : ℂ) * L (Pi.single i 1) := by
      conv_lhs => rw [← Finset.univ_sum_single a]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (Pi.single i (a i) : ι → ℝ) = a i • Pi.single i 1 by
        rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, Complex.real_smul]
    have hS : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine lgr_sq_le_of_le hS (le_trans ?_ (h a))
    rcases ha with ha | ha
    · calc ∑ i, a i ^ 2 = (L a).re := by
            rw [hLa, Complex.re_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Complex.re_ofReal_mul, ← ha i, sq]
        _ ≤ ‖L a‖ := Complex.re_le_norm _
    · calc ∑ i, a i ^ 2 = (L a).im := by
            rw [hLa, Complex.im_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Complex.im_ofReal_mul, ← ha i, sq]
        _ ≤ ‖L a‖ := Complex.im_le_norm _
  have h1 := key (fun i => (L (Pi.single i 1)).re) (Or.inl fun _ => rfl)
  have h2 := key (fun i => (L (Pi.single i 1)).im) (Or.inr fun _ => rfl)
  calc ∑ i, ‖L (Pi.single i 1)‖ ^ 2
      = ∑ i, (L (Pi.single i 1)).re ^ 2 + ∑ i, (L (Pi.single i 1)).im ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
    _ ≤ 2 * c ^ 2 := by linarith

/-- The same hypothesis bounds the operator norm by `c √|ι|`. -/
private theorem lgr_opNorm_le {ι : Type*} [Fintype ι] (L : (ι → ℝ) →L[ℝ] ℂ) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ y, ‖L y‖ ≤ c * Real.sqrt (∑ i, y i ^ 2)) :
    ‖L‖ ≤ c * Real.sqrt (Fintype.card ι) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => (h y).trans ?_
  rw [mul_assoc]
  gcongr
  rw [← Real.sqrt_sq (norm_nonneg y), ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, y i ^ 2 ≤ ∑ _i : ι, ‖y‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sq_abs, ← Real.norm_eq_abs]
        gcongr
        exact norm_le_pi_norm y i
    _ = _ := by simp

/-- The fresh block is real-linear in the coordinates. -/
private theorem lgr_gueBlock_add_smul (W : ℕ) (ω y : Ω W 1) (s : ℝ) :
    gueBlock W 1 (ω + s • y) 0 = gueBlock W 1 ω 0 + (s : ℂ) • gueBlock W 1 y 0 := by
  ext α β
  simp only [gueBlock, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

/-- The directional derivative of a function of the fresh block is the derivative along the line
`V + s H` in the matrix variable. -/
private theorem lgr_fderiv_apply {W : ℕ} {Z : Matrix (Fin W) (Fin W) ℂ → ℂ}
    (hZ : Differentiable ℝ (fun ω : Ω W 1 => Z (gueBlock W 1 ω 0))) (ω y : Ω W 1) {D : ℂ}
    (hD : HasDerivAt (fun s : ℝ => Z (gueBlock W 1 ω 0 + (s : ℂ) • gueBlock W 1 y 0)) D 0) :
    fderiv ℝ (fun ω : Ω W 1 => Z (gueBlock W 1 ω 0)) ω y = D := by
  have h1 : HasDerivAt (fun s : ℝ => ω + s • y) y 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const y).const_add ω
  have h2 := (hZ (ω + (0 : ℝ) • y)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  rw [zero_smul, add_zero] at h2
  refine h2.unique ?_
  convert hD using 1
  funext s
  simp [Function.comp, lgr_gueBlock_add_smul]

/-- A line `V + s H` of Hermitian matrices. -/
private theorem lgr_isHermitian_line {W : ℕ} {V H : Matrix (Fin W) (Fin W) ℂ}
    (hV : V.IsHermitian) (hH : H.IsHermitian) (s : ℝ) : (V + (s : ℂ) • H).IsHermitian := by
  unfold Matrix.IsHermitian at *
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hV, hH, Complex.star_def,
    Complex.conj_ofReal]

/-! ### Matrix facts -/

private theorem lgr_lin_mul {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) :
    Matrix.toEuclideanLin (A * B) v = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

private theorem lgr_inner_lin_conjTranspose {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v w : EuclideanSpace ℂ (Fin W)) :
    inner ℂ v (Matrix.toEuclideanLin Aᴴ w) = inner ℂ (Matrix.toEuclideanLin A v) w := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

private theorem lgr_norm_lin_unitary {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) :
    ‖Matrix.toEuclideanLin U v‖ = ‖v‖ := by
  have hUU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have h : inner ℂ (Matrix.toEuclideanLin U v) (Matrix.toEuclideanLin U v) = inner ℂ v v := by
    rw [← lgr_inner_lin_conjTranspose, ← lgr_lin_mul, hUU]
    simp
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖Matrix.toEuclideanLin U v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h'

/-- A unitary matrix has operator norm at most one. -/
private theorem lgr_norm_unitary_le {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ) : ‖U‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    change ‖Matrix.toEuclideanLin U v‖ ≤ 1 * ‖v‖
    rw [lgr_norm_lin_unitary hU, one_mul]

/-- `‖(I + C) F(C, V)⁻¹‖ ≤ 2` for unitary `C` and Hermitian `V`, uniformly in `V`: with
`x = (I + C) y` one has `Re ⟨x, F y⟩ = ‖x‖² / 2`. -/
private theorem lgr_norm_one_add_mul_inv_le (g E : ℝ) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) :
    ‖(1 + C) * (stepF g E C V)⁻¹‖ ≤ 2 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_stepF g E hC hV)
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_two fun z => ?_
  change ‖Matrix.toEuclideanLin ((1 + C) * (stepF g E C V)⁻¹) z‖ ≤ 2 * ‖z‖
  rw [lgr_lin_mul]
  set y := Matrix.toEuclideanLin (stepF g E C V)⁻¹ z with hy
  have h1 : z = Matrix.toEuclideanLin (stepF g E C V) y := by
    rw [hy, ← lgr_lin_mul, Matrix.mul_nonsing_inv _ hdet]; simp
  clear_value y
  set x := Matrix.toEuclideanLin (1 + C) y with hx
  have hx' : x = y + Matrix.toEuclideanLin C y := by rw [hx]; simp
  set τ : ℂ := Complex.I * ((normalH E / g : ℝ) : ℂ) with hτ
  have hz : z = y - τ • Matrix.toEuclideanLin V x := by
    have hone : Matrix.toEuclideanLin (1 : Matrix (Fin W) (Fin W) ℂ) y = y := by simp
    rw [h1, hx, stepF, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, lgr_lin_mul,
      hone]
  clear_value x
  have hxV : (inner ℂ x (Matrix.toEuclideanLin V x)).im = 0 := by
    have h1 : inner ℂ x (Matrix.toEuclideanLin V x) = inner ℂ (Matrix.toEuclideanLin V x) x := by
      conv_lhs => rw [← hV.eq]
      exact lgr_inner_lin_conjTranspose V x x
    have h2 := inner_conj_symm (𝕜 := ℂ) x (Matrix.toEuclideanLin V x)
    rw [← h1] at h2
    have := congrArg Complex.im h2
    rw [Complex.conj_im] at this
    linarith
  have hre : (inner ℂ x z).re = ‖x‖ ^ 2 / 2 := by
    have hCy : ‖Matrix.toEuclideanLin C y‖ = ‖y‖ := lgr_norm_lin_unitary hC y
    have hn : ‖x‖ ^ 2 = ‖y‖ ^ 2 + 2 * (inner ℂ y (Matrix.toEuclideanLin C y)).re + ‖y‖ ^ 2 := by
      rw [hx', @norm_add_sq ℂ, hCy]; rfl
    rw [hz, inner_sub_right, inner_smul_right, Complex.sub_re, hx', inner_add_left,
      Complex.add_re, ← hx']
    have hτre : (τ * inner ℂ x (Matrix.toEuclideanLin V x)).re = 0 := by
      rw [Complex.mul_re, hxV, hτ]; simp
    rw [hτre, show (inner ℂ y y).re = ‖y‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) y, hn]
    have hsymm : (inner ℂ (Matrix.toEuclideanLin C y) y).re =
        (inner ℂ y (Matrix.toEuclideanLin C y)).re :=
      inner_re_symm (𝕜 := ℂ) (Matrix.toEuclideanLin C y) y
    rw [hsymm]
    ring
  have hle : ‖x‖ ^ 2 / 2 ≤ ‖x‖ * ‖z‖ := by
    rw [← hre]; exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  nlinarith [norm_nonneg x, norm_nonneg z]

/-! ### Derivatives along a line -/

/-- A real-linear map of matrices transports derivatives along a real parameter. -/
private theorem lgr_hasDerivAt_linear {W : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (ℓ : Matrix (Fin W) (Fin W) ℂ →ₗ[ℝ] G) {A : ℝ → Matrix (Fin W) (Fin W) ℂ}
    {A' : Matrix (Fin W) (Fin W) ℂ} {s : ℝ} (hA : HasDerivAt A A' s) :
    HasDerivAt (fun x => ℓ (A x)) (ℓ A') s :=
  (LinearMap.toContinuousLinearMap ℓ).hasFDerivAt.comp_hasDerivAt s hA

/-- The action `(A, u) ↦ A u` as a bounded real-bilinear map. -/
private def lgrAct (W : ℕ) :
    Matrix (Fin W) (Fin W) ℂ →L[ℝ] EuclideanSpace ℂ (Fin W) →L[ℝ] EuclideanSpace ℂ (Fin W) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun A u => Matrix.toEuclideanLin A u)
      (fun A B u => by simp)
      (fun c A u => by rw [← Complex.coe_smul, map_smul, LinearMap.smul_apply, Complex.coe_smul])
      (fun A u w => by simp) (fun c A u => LinearMap.map_smul_of_tower _ c u)) 1
    (fun A u => by simpa [one_mul] using lgr_norm_lin_le A u)

private theorem lgrAct_apply (W : ℕ) (A : Matrix (Fin W) (Fin W) ℂ) (u : EuclideanSpace ℂ (Fin W)) :
    lgrAct W A u = Matrix.toEuclideanLin A u := rfl

/-- Derivative of `s ↦ u(s)* A(s) u(s)` along a real parameter, with the bound
`2 ‖u'‖ + ‖A'‖` when `‖A(0)‖ ≤ 1` and `‖u(0)‖ = 1`. -/
private theorem lgr_hasDerivAt_vecForm {W : ℕ} {A : ℝ → Matrix (Fin W) (Fin W) ℂ}
    {A' : Matrix (Fin W) (Fin W) ℂ} {u : ℝ → EuclideanSpace ℂ (Fin W)}
    {u' : EuclideanSpace ℂ (Fin W)} (hA : HasDerivAt A A' 0) (hu : HasDerivAt u u' 0)
    (hA0 : ‖A 0‖ ≤ 1) (hu0 : ‖u 0‖ = 1) :
    ∃ D : ℂ, HasDerivAt (fun s => vecForm (A s) (u s)) D 0 ∧ ‖D‖ ≤ 2 * ‖u'‖ + ‖A'‖ := by
  have hB : HasDerivAt (fun s => lgrAct W (A s) (u s))
      (lgrAct W (A 0) u' + lgrAct W A' (u 0)) 0 :=
    (lgrAct W).hasDerivAt_of_bilinear (fun _ => hA) (fun _ => hu)
  have hI := hu.inner ℂ hB
  refine ⟨_, hI, ?_⟩
  simp only [lgrAct_apply]
  calc ‖inner ℂ (u 0) (Matrix.toEuclideanLin (A 0) u' + Matrix.toEuclideanLin A' (u 0)) +
        inner ℂ u' (Matrix.toEuclideanLin (A 0) (u 0))‖
      ≤ ‖u 0‖ * (‖A 0‖ * ‖u'‖ + ‖A'‖ * ‖u 0‖) + ‖u'‖ * (‖A 0‖ * ‖u 0‖) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (norm_inner_le_norm _ _).trans ?_
          gcongr
          exact (norm_add_le _ _).trans (add_le_add (lgr_norm_lin_le _ _) (lgr_norm_lin_le _ _))
        · refine (norm_inner_le_norm _ _).trans ?_
          gcongr
          exact lgr_norm_lin_le _ _
    _ ≤ 2 * ‖u'‖ + ‖A'‖ := by
        rw [hu0]
        have := norm_nonneg u'
        have := norm_nonneg A'
        nlinarith [norm_nonneg (A 0)]

/-! ### The update along a line `V + s H` -/

private theorem lgr_normalH_nonneg (E : ℝ) : 0 ≤ normalH E := by
  unfold normalH freeAngle
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg (E / 2))
    (Real.arccos_le_pi (E / 2))
  positivity

private theorem lgr_norm_stepPhase (E : ℝ) : ‖stepPhase E‖ = 1 := by
  unfold stepPhase
  rw [show -((freeAngle E : ℂ) * Complex.I) = ((-freeAngle E : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem lgr_norm_normalPhase (E : ℝ) : ‖normalPhase E‖ = 1 := by
  unfold normalPhase
  rw [norm_neg, show 2 * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `‖i h_θ g⁻¹‖ = h_θ g⁻¹` for `g > 0`. -/
private theorem lgr_norm_tau (E : ℝ) {g : ℝ} (hg : 0 < g) :
    ‖Complex.I * ((normalH E / g : ℝ) : ℂ)‖ = normalH E / g := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (lgr_normalH_nonneg E) hg.le)]

/-- `d F(C, V + sH)⁻¹ = F⁻¹ (i h_θ g⁻¹ H (I + C)) F⁻¹`. -/
private theorem lgr_hasDerivAt_inv (g E : ℝ) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian)
    (H : Matrix (Fin W) (Fin W) ℂ) :
    HasDerivAt (fun s : ℝ => (stepF g E C (V + (s : ℂ) • H))⁻¹)
      ((stepF g E C V)⁻¹ * ((Complex.I * ((normalH E / g : ℝ) : ℂ)) • (H * (1 + C))) *
        (stepF g E C V)⁻¹) 0 := by
  set t : ℂ := Complex.I * ((normalH E / g : ℝ) : ℂ)
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 0 :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_id (0 : ℝ))
  have hG : HasDerivAt (fun s : ℝ => V + (s : ℂ) • H) H 0 := by
    simpa using (h1.smul_const H).const_add V
  have hF : HasDerivAt (fun s : ℝ => stepF g E C (V + (s : ℂ) • H))
      (-(t • (H * (1 + C)))) 0 :=
    ((hG.mul_const (1 + C)).const_smul t).const_sub (1 : Matrix (Fin W) (Fin W) ℂ)
  obtain ⟨u, hu⟩ := isUnit_stepF g E hC hV
  have hui : ((u⁻¹ : (Matrix (Fin W) (Fin W) ℂ)ˣ) : Matrix (Fin W) (Fin W) ℂ) =
      (stepF g E C V)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  have hl : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℂ (Matrix (Fin W) (Fin W) ℂ) ↑u⁻¹ ↑u⁻¹)
      (stepF g E C (V + ((0 : ℝ) : ℂ) • H)) := by
    have h0 : stepF g E C (V + ((0 : ℝ) : ℂ) • H) = ↑u := by simp [hu]
    rw [h0]
    exact hasFDerivAt_ringInverse (𝕜 := ℂ) u
  have hd := (hl.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hF
  have hfun : (fun s : ℝ => (stepF g E C (V + (s : ℂ) • H))⁻¹) =
      Ring.inverse ∘ fun s : ℝ => stepF g E C (V + (s : ℂ) • H) := by
    funext s
    exact Matrix.nonsing_inv_eq_ringInverse _
  rw [hfun]
  exact hd.congr_deriv (by simp [hui])

/-- `M ↦ M^* v` as a real-linear map. -/
private def lgrAdjApply {W : ℕ} (v : EuclideanSpace ℂ (Fin W)) :
    Matrix (Fin W) (Fin W) ℂ →ₗ[ℝ] EuclideanSpace ℂ (Fin W) where
  toFun M := Matrix.toEuclideanLin Mᴴ v
  map_add' M N := by simp [Matrix.conjTranspose_add]
  map_smul' c M := by
    rw [← Complex.coe_smul, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      map_smul, LinearMap.smul_apply, RingHom.id_apply, Complex.coe_smul]

/-- `d (F^{-*} v) = (i h_θ g⁻¹ H (I + C) F⁻¹)^* (F^{-*} v)` along `V + sH`. -/
private theorem lgr_hasDerivAt_stepVec (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) (H : Matrix (Fin W) (Fin W) ℂ) :
    HasDerivAt (fun s : ℝ => stepVec g E X (V + (s : ℂ) • H))
      (Matrix.toEuclideanLin ((Complex.I * ((normalH E / g : ℝ) : ℂ)) •
        (H * ((1 + X.1) * (stepF g E X.1 V)⁻¹)))ᴴ (stepVec g E X V)) 0 := by
  have h := lgr_hasDerivAt_linear (lgrAdjApply X.2) (lgr_hasDerivAt_inv g E hX.1 hV H)
  refine h.congr_deriv ?_
  change Matrix.toEuclideanLin (_)ᴴ X.2 = _
  unfold stepVec
  rw [← lgr_lin_mul, ← Matrix.conjTranspose_mul]
  congr 3
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

/-- `‖dw‖ ≤ 2 h_θ g⁻¹ ‖H‖ ‖w‖`, by `‖(I + C) F⁻¹‖ ≤ 2`. -/
private theorem lgr_norm_dStepVec_le (g E : ℝ) (hg : 0 < g) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) (H : Matrix (Fin W) (Fin W) ℂ)
    (w : EuclideanSpace ℂ (Fin W)) :
    ‖Matrix.toEuclideanLin ((Complex.I * ((normalH E / g : ℝ) : ℂ)) •
        (H * ((1 + C) * (stepF g E C V)⁻¹)))ᴴ w‖ ≤ 2 * (normalH E / g) * ‖H‖ * ‖w‖ := by
  refine (lgr_norm_lin_le _ _).trans ?_
  rw [Matrix.l2_opNorm_conjTranspose, norm_smul, lgr_norm_tau E hg]
  have h1 := Matrix.l2_opNorm_mul H ((1 + C) * (stepF g E C V)⁻¹)
  have h2 := lgr_norm_one_add_mul_inv_le g E hC hV
  have ht := div_nonneg (lgr_normalH_nonneg E) hg.le
  have hH := norm_nonneg H
  have hw := norm_nonneg w
  calc normalH E / g * ‖H * ((1 + C) * (stepF g E C V)⁻¹)‖ * ‖w‖
      ≤ normalH E / g * (‖H‖ * 2) * ‖w‖ := by gcongr; exact h1.trans (by gcongr)
    _ = 2 * (normalH E / g) * ‖H‖ * ‖w‖ := by ring

/-- `‖dC'‖ ≤ 4 h_θ g⁻¹ ‖H‖` for the derivative of `hasDerivAt_stepC`. -/
private theorem lgr_norm_dStepC_le (g E : ℝ) (hg : 0 < g) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) (H : Matrix (Fin W) (Fin W) ℂ) :
    ‖(Complex.I * ((normalH E / g : ℝ) : ℂ)) •
        ((stepC g E C V - normalPhase E • (1 : Matrix (Fin W) (Fin W) ℂ)) * H * (1 + C) *
          (stepF g E C V)⁻¹)‖ ≤ 4 * (normalH E / g) * ‖H‖ := by
  have hA : ‖stepC g E C V - normalPhase E • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, lgr_norm_normalPhase, one_mul]
    have := lgr_norm_unitary_le (stepC_mem_unitaryGroup g E hC hV)
    have := lgr_norm_unitary_le (one_mem (Matrix.unitaryGroup (Fin W) ℂ))
    linarith
  rw [norm_smul, lgr_norm_tau E hg, Matrix.mul_assoc]
  have h2 := lgr_norm_one_add_mul_inv_le g E hC hV
  have ht := div_nonneg (lgr_normalH_nonneg E) hg.le
  calc normalH E / g * ‖(stepC g E C V - normalPhase E • 1) * H * ((1 + C) * (stepF g E C V)⁻¹)‖
      ≤ normalH E / g * (2 * ‖H‖ * 2) := by
        gcongr
        refine (Matrix.l2_opNorm_mul _ _).trans ?_
        gcongr
        refine (Matrix.l2_opNorm_mul _ _).trans ?_
        gcongr
    _ = 4 * (normalH E / g) * ‖H‖ := by ring

/-- Derivatives of `‖w‖`, of the normalized vector `φ w/‖w‖` (`|φ| = 1`) and of `-log ‖w‖`. -/
private theorem lgr_hasDerivAt_normalize {W : ℕ} {w : ℝ → EuclideanSpace ℂ (Fin W)}
    {w' : EuclideanSpace ℂ (Fin W)} (hw : HasDerivAt w w' 0) (h0 : w 0 ≠ 0) (φ : ℂ)
    (hφ : ‖φ‖ = 1) :
    (∃ D, HasDerivAt (fun s => (φ * ((‖w s‖⁻¹ : ℝ) : ℂ)) • w s) D 0 ∧
        ‖D‖ ≤ 2 * ‖w'‖ / ‖w 0‖) ∧
      ∃ d : ℝ, HasDerivAt (fun s => -Real.log ‖w s‖) d 0 ∧ |d| ≤ ‖w'‖ / ‖w 0‖ := by
  have hn0 : 0 < ‖w 0‖ := norm_pos_iff.mpr h0
  have hq := hw.norm_sq
  have hs := hq.sqrt (pow_ne_zero 2 hn0.ne')
  have hfun : (fun s => √(‖w s‖ ^ 2)) = fun s => ‖w s‖ := by
    funext s; exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun, Real.sqrt_sq (norm_nonneg _)] at hs
  set d := 2 * inner ℝ (w 0) w' / (2 * ‖w 0‖) with hd
  have hdb : |d| ≤ ‖w'‖ := by
    rw [hd, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ‖w 0‖), abs_two,
      div_le_iff₀ (by positivity)]
    have := abs_real_inner_le_norm (w 0) w'
    nlinarith
  refine ⟨?_, ⟨-(d / ‖w 0‖), (hs.log hn0.ne').neg, ?_⟩⟩
  · have hc := (hs.inv hn0.ne').ofReal_comp.const_mul φ
    refine ⟨_, hc.smul hw, ?_⟩
    refine (norm_add_le _ _).trans ?_
    simp only [Pi.inv_apply, norm_smul, norm_mul, hφ, one_mul, Complex.norm_real, norm_inv,
      Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < ‖w 0‖ ^ 2),
      abs_of_pos hn0]
    have e1 : |d| / ‖w 0‖ ^ 2 * ‖w 0‖ = |d| / ‖w 0‖ := by field_simp
    rw [e1, ← div_eq_inv_mul, show 2 * ‖w'‖ / ‖w 0‖ = ‖w'‖ / ‖w 0‖ + ‖w'‖ / ‖w 0‖ by ring]
    gcongr
  · rw [abs_neg, abs_div, abs_of_pos hn0]
    gcongr

private theorem lgr_stepVec_ne_zero (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) : stepVec g E X V ≠ 0 := by
  intro h
  have h1 := (isState_stepState g E hX hV).2
  change ‖(stepPhase E * ((‖stepVec g E X V‖⁻¹ : ℝ) : ℂ)) • stepVec g E X V‖ = 1 at h1
  rw [h] at h1
  simp at h1

/-- Along `V + sH`: the derivatives of `C'`, of `v'` and of `c` at `s = 0`, bounded by
`4 h_θ g⁻¹ ‖H‖`, `4 h_θ g⁻¹ ‖H‖` and `2 h_θ g⁻¹ ‖H‖` (proof of Lemma 11.2 [uvg:lem:drifts]). -/
private theorem lgr_line_state (g E : ℝ) (hg : 0 < g) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) (H : Matrix (Fin W) (Fin W) ℂ) :
    (∃ D, HasDerivAt (fun s : ℝ => (stepState g E X (V + (s : ℂ) • H)).1) D 0 ∧
        ‖D‖ ≤ 4 * (normalH E / g) * ‖H‖) ∧
      (∃ D, HasDerivAt (fun s : ℝ => (stepState g E X (V + (s : ℂ) • H)).2) D 0 ∧
        ‖D‖ ≤ 4 * (normalH E / g) * ‖H‖) ∧
      ∃ d : ℝ, HasDerivAt (fun s : ℝ => stepInc g E X (V + (s : ℂ) • H)) d 0 ∧
        |d| ≤ 2 * (normalH E / g) * ‖H‖ := by
  have hw := lgr_hasDerivAt_stepVec g E hX hV H
  have hw0 : (fun s : ℝ => stepVec g E X (V + (s : ℂ) • H)) 0 = stepVec g E X V := by simp
  have hne : (fun s : ℝ => stepVec g E X (V + (s : ℂ) • H)) 0 ≠ 0 := by
    rw [hw0]; exact lgr_stepVec_ne_zero g E hX hV
  have hpos : 0 < ‖stepVec g E X V‖ := norm_pos_iff.mpr (lgr_stepVec_ne_zero g E hX hV)
  have hdw := lgr_norm_dStepVec_le g E hg hX.1 hV H (stepVec g E X V)
  have hq : ‖Matrix.toEuclideanLin ((Complex.I * ((normalH E / g : ℝ) : ℂ)) •
        (H * ((1 + X.1) * (stepF g E X.1 V)⁻¹)))ᴴ (stepVec g E X V)‖ /
      ‖stepVec g E X V‖ ≤ 2 * (normalH E / g) * ‖H‖ := by
    rw [div_le_iff₀ hpos]; exact hdw
  obtain ⟨⟨D, hD, hDb⟩, ⟨d, hd, hdb⟩⟩ := lgr_hasDerivAt_normalize hw hne (stepPhase E)
    (lgr_norm_stepPhase E)
  have hv0 : stepVec g E X (V + ((0 : ℝ) : ℂ) • H) = stepVec g E X V := by simp
  rw [hv0] at hDb hdb
  refine ⟨⟨_, hasDerivAt_stepC g E hX.1 hV H, lgr_norm_dStepC_le g E hg hX.1 hV H⟩,
    ⟨D, hD, ?_⟩, ⟨d, hd, hdb.trans hq⟩⟩
  calc ‖D‖ ≤ 2 * (‖Matrix.toEuclideanLin ((Complex.I * ((normalH E / g : ℝ) : ℂ)) •
        (H * ((1 + X.1) * (stepF g E X.1 V)⁻¹)))ᴴ (stepVec g E X V)‖ /
      ‖stepVec g E X V‖) := by rw [← mul_div_assoc]; exact hDb
    _ ≤ 2 * (2 * (normalH E / g) * ‖H‖) := by gcongr
    _ = 4 * (normalH E / g) * ‖H‖ := by ring

/-- `|Tr(Y dC')| ≤ 4 h_θ g⁻¹ ‖Y‖ |y|₂` for the derivative of `hasDerivAt_stepC` in the direction
`H = V(y)` of the fresh block. -/
private theorem lgr_norm_trace_dStepC_le (g E : ℝ) (hg : 0 < g) {W : ℕ} (hW : 1 ≤ W)
    {C V : Matrix (Fin W) (Fin W) ℂ} (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian)
    (y : Ω W 1) (Y : Matrix (Fin W) (Fin W) ℂ) :
    ‖(Y * ((Complex.I * ((normalH E / g : ℝ) : ℂ)) •
        ((stepC g E C V - normalPhase E • (1 : Matrix (Fin W) (Fin W) ℂ)) * gueBlock W 1 y 0 *
          (1 + C) * (stepF g E C V)⁻¹))).trace‖ ≤
      4 * (normalH E / g) * ‖Y‖ * √(∑ k, y k ^ 2) := by
  set A := stepC g E C V - normalPhase E • (1 : Matrix (Fin W) (Fin W) ℂ)
  set P := (1 + C) * (stepF g E C V)⁻¹
  set H := gueBlock W 1 y 0
  have hA : ‖A‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, lgr_norm_normalPhase, one_mul]
    have := lgr_norm_unitary_le (stepC_mem_unitaryGroup g E hC hV)
    have := lgr_norm_unitary_le (one_mem (Matrix.unitaryGroup (Fin W) ℂ))
    linarith
  have hP : ‖P‖ ≤ 2 := lgr_norm_one_add_mul_inv_le g E hC hV
  have htr : (Y * ((Complex.I * ((normalH E / g : ℝ) : ℂ)) • (A * H * (1 + C) *
      (stepF g E C V)⁻¹))).trace = (Complex.I * ((normalH E / g : ℝ) : ℂ)) *
      (H * (P * Y * A)).trace := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc A H, ← Matrix.mul_assoc,
      Matrix.trace_mul_cycle, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    simp only [P, Matrix.mul_assoc]
  rw [htr, norm_mul, lgr_norm_tau E hg]
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hM : ‖(H * (P * Y * A)).trace‖ ≤ ‖P * Y * A‖ * √(∑ k, y k ^ 2) := by
    have h1 := lgr_norm_trace_mul_sq_le H (P * Y * A)
    rw [lgr_hs_gueBlock] at h1
    have h2 := lgr_hs_le (P * Y * A)
    have h3 : ‖(H * (P * Y * A)).trace‖ ^ 2 ≤ (‖P * Y * A‖ * √(∑ k, y k ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      calc _ ≤ ((W : ℝ)⁻¹ * ∑ k, y k ^ 2) * lgrHs (P * Y * A) := h1
        _ ≤ ((W : ℝ)⁻¹ * ∑ k, y k ^ 2) * (W * ‖P * Y * A‖ ^ 2) := by
            have : 0 ≤ (W : ℝ)⁻¹ * ∑ k, y k ^ 2 :=
              mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
            gcongr
        _ = (‖P * Y * A‖ ^ 2 * ∑ k, y k ^ 2) * ((W : ℝ)⁻¹ * W) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hW'.ne', mul_one]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3
  have hPYA : ‖P * Y * A‖ ≤ 4 * ‖Y‖ := by
    calc ‖P * Y * A‖ ≤ ‖P‖ * ‖Y‖ * ‖A‖ :=
          (Matrix.l2_opNorm_mul _ _).trans (by gcongr; exact Matrix.l2_opNorm_mul _ _)
      _ ≤ 2 * ‖Y‖ * 2 := by gcongr
      _ = 4 * ‖Y‖ := by ring
  have ht := div_nonneg (lgr_normalH_nonneg E) hg.le
  calc normalH E / g * ‖(H * (P * Y * A)).trace‖
      ≤ normalH E / g * (4 * ‖Y‖ * √(∑ k, y k ^ 2)) := by
        gcongr; exact hM.trans (by gcongr)
    _ = _ := by ring

/-- `‖V(y)‖ ≤ W^{-1/2} |y|₂` for the fresh block. -/
private theorem lgr_norm_gueBlock_le (W : ℕ) (y : Ω W 1) :
    ‖gueBlock W 1 y 0‖ ≤ (√W)⁻¹ * √(∑ k, y k ^ 2) := by
  have h := lgr_norm_sq_le_hs (gueBlock W 1 y 0)
  rw [lgr_hs_gueBlock] at h
  have h2 : ‖gueBlock W 1 y 0‖ ≤ √((W : ℝ)⁻¹ * ∑ k, y k ^ 2) :=
    Real.le_sqrt_of_sq_le h
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_inv] at h2

/-- Derivatives of `m_1`, `m_2`, `f_1`, `f_2`, `f_{-1}` at `(C', v')` along `V + sH`,
`H = V(y)` the fresh block at `y` (proof of Lemma 11.2 [uvg:lem:drifts]). -/
private theorem lgr_line_obs (g E : ℝ) (hg : 0 < g) {W : ℕ} (hW : 1 ≤ W) {X : State W}
    (hX : IsState X) {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) (y : Ω W 1) :
    (∃ D, HasDerivAt (fun s : ℝ => obsM 1 (stepState g E X (V + (s : ℂ) • gueBlock W 1 y 0))) D 0 ∧
        ‖D‖ ≤ 4 * (normalH E / g) * √(∑ k, y k ^ 2) / W) ∧
      (∃ D, HasDerivAt (fun s : ℝ => obsM 2 (stepState g E X (V + (s : ℂ) • gueBlock W 1 y 0)))
        D 0 ∧ ‖D‖ ≤ 8 * (normalH E / g) * √(∑ k, y k ^ 2) / W) ∧
      (∃ D, HasDerivAt (fun s : ℝ => obsF 1 (stepState g E X (V + (s : ℂ) • gueBlock W 1 y 0)))
        D 0 ∧ ‖D‖ ≤ 12 * (normalH E / g) * ‖gueBlock W 1 y 0‖) ∧
      (∃ D, HasDerivAt (fun s : ℝ => obsF 2 (stepState g E X (V + (s : ℂ) • gueBlock W 1 y 0)))
        D 0 ∧ ‖D‖ ≤ 16 * (normalH E / g) * ‖gueBlock W 1 y 0‖) ∧
      ∃ D, HasDerivAt (fun s : ℝ => obsF (-1) (stepState g E X (V + (s : ℂ) • gueBlock W 1 y 0)))
        D 0 ∧ ‖D‖ ≤ 12 * (normalH E / g) * ‖gueBlock W 1 y 0‖ := by
  set H := gueBlock W 1 y 0 with hHdef
  have hH : H.IsHermitian := gueBlock_isHermitian W 1 y 0
  set t := normalH E / g with htdef
  have ht : 0 ≤ t := div_nonneg (lgr_normalH_nonneg E) hg.le
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hC := hasDerivAt_stepC g E hX.1 hV H
  set dC := (Complex.I * ((normalH E / g : ℝ) : ℂ)) •
    ((stepC g E X.1 V - normalPhase E • (1 : Matrix (Fin W) (Fin W) ℂ)) * H * (1 + X.1) *
      (stepF g E X.1 V)⁻¹) with hdC
  have hdC : ‖dC‖ ≤ 4 * t * ‖H‖ := lgr_norm_dStepC_le g E hg hX.1 hV H
  have hU : stepC g E X.1 V ∈ Matrix.unitaryGroup (Fin W) ℂ := stepC_mem_unitaryGroup g E hX.1 hV
  have hU1 : ‖stepC g E X.1 V‖ ≤ 1 := lgr_norm_unitary_le hU
  have hC0 : stepC g E X.1 (V + ((0 : ℝ) : ℂ) • H) = stepC g E X.1 V := by simp
  have hT : ∀ Y : Matrix (Fin W) (Fin W) ℂ, ‖Y‖ ≤ 1 → ‖(Y * dC).trace‖ ≤ 4 * t * √(∑ k, y k ^ 2) :=
    fun Y hY => (lgr_norm_trace_dStepC_le g E hg hW hX.1 hV y Y).trans (by
      have := Real.sqrt_nonneg (∑ k, y k ^ 2)
      calc 4 * t * ‖Y‖ * √(∑ k, y k ^ 2) ≤ 4 * t * 1 * √(∑ k, y k ^ 2) := by gcongr
        _ = _ := by ring)
  have hsq : HasDerivAt
      (fun s : ℝ => stepC g E X.1 (V + (s : ℂ) • H) * stepC g E X.1 (V + (s : ℂ) • H))
      (dC * stepC g E X.1 V + stepC g E X.1 V * dC) 0 := by
    have := hC.mul hC
    rwa [hC0] at this
  obtain ⟨_, ⟨D2, hD2, hD2b⟩, -⟩ := lgr_line_state g E hg hX hV H
  have hv0 : ‖(stepState g E X (V + ((0 : ℝ) : ℂ) • H)).2‖ = 1 := by
    simpa using (isState_stepState g E hX hV).2
  have hC0' : ‖stepC g E X.1 (V + ((0 : ℝ) : ℂ) • H)‖ ≤ 1 := by rw [hC0]; exact hU1
  have hCC0 :
      ‖stepC g E X.1 (V + ((0 : ℝ) : ℂ) • H) * stepC g E X.1 (V + ((0 : ℝ) : ℂ) • H)‖ ≤ 1 := by
    rw [hC0]; exact lgr_norm_unitary_le (mul_mem hU hU)
  have hf1 := lgr_hasDerivAt_vecForm hC hD2 hC0' hv0
  have hf2 := lgr_hasDerivAt_vecForm hsq hD2 hCC0 hv0
  have hdsq : ‖dC * stepC g E X.1 V + stepC g E X.1 V * dC‖ ≤ 8 * t * ‖H‖ := by
    calc _ ≤ ‖dC‖ * ‖stepC g E X.1 V‖ + ‖stepC g E X.1 V‖ * ‖dC‖ :=
          (norm_add_le _ _).trans (add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _))
      _ ≤ 4 * t * ‖H‖ * 1 + 1 * (4 * t * ‖H‖) := by gcongr
      _ = 8 * t * ‖H‖ := by ring
  have hfun1 : (fun s : ℝ => obsF 1 (stepState g E X (V + (s : ℂ) • H))) =
      fun s : ℝ => vecForm (stepC g E X.1 (V + (s : ℂ) • H))
        (stepState g E X (V + (s : ℂ) • H)).2 := by
    funext s; simp [obsF, stepState]
  obtain ⟨F1, hF1, hF1b⟩ := hf1
  have hF1b' : ‖F1‖ ≤ 12 * t * ‖H‖ := hF1b.trans (by linarith)
  refine ⟨?_, ?_, ⟨F1, hfun1 ▸ hF1, hF1b'⟩, ?_, ?_⟩
  · have h := (lgr_hasDerivAt_linear (Matrix.traceLinearMap (Fin W) ℝ ℂ) hC).const_mul
      ((W : ℂ)⁻¹)
    refine ⟨(W : ℂ)⁻¹ * dC.trace, ?_, ?_⟩
    · convert h using 1
      · funext s; simp [obsM, stepState]
      · rfl
    · rw [norm_mul, norm_inv, Complex.norm_natCast]
      have := hT 1 (lgr_norm_unitary_le (one_mem (Matrix.unitaryGroup (Fin W) ℂ)))
      rw [Matrix.one_mul] at this
      change (W : ℝ)⁻¹ * ‖dC.trace‖ ≤ _
      rw [inv_mul_le_iff₀ hW', mul_div_cancel₀ _ hW'.ne']
      exact this
  · have h := (lgr_hasDerivAt_linear (Matrix.traceLinearMap (Fin W) ℝ ℂ) hsq).const_mul
      ((W : ℂ)⁻¹)
    refine ⟨(W : ℂ)⁻¹ * (dC * stepC g E X.1 V + stepC g E X.1 V * dC).trace, ?_, ?_⟩
    · convert h using 1
      · funext s; simp [obsM, stepState, sq]
      · rfl
    · rw [norm_mul, norm_inv, Complex.norm_natCast]
      rw [Matrix.trace_add, Matrix.trace_mul_comm dC, inv_mul_le_iff₀ hW',
        mul_div_cancel₀ _ hW'.ne']
      have := hT _ hU1
      calc _ ≤ ‖(stepC g E X.1 V * dC).trace‖ + ‖(stepC g E X.1 V * dC).trace‖ := norm_add_le _ _
        _ ≤ _ := by linarith
  · obtain ⟨F2, hF2, hF2b⟩ := hf2
    refine ⟨F2, ?_, hF2b.trans (by linarith)⟩
    convert hF2 using 1
    funext s; simp [obsF, stepState, sq]
  · refine ⟨star F1, ?_, by rw [norm_star]; exact hF1b'⟩
    have h := (hfun1 ▸ hF1).star
    convert h using 1
    funext s
    exact (obsF_zero_neg (isState_stepState g E hX (lgr_isHermitian_line hV hH s)) 1).2

private theorem lgr_sin_pos {E : ℝ} (hE : |E| < 2) : 0 < Real.sin (freeAngle E) := by
  unfold freeAngle
  rw [Real.sin_arccos]
  apply Real.sqrt_pos.mpr
  have h : E ^ 2 < 4 := by
    have := sq_abs E
    nlinarith [abs_nonneg E]
  nlinarith

/-- `|1 + e^{-2iθ}| = 2 sin ϑ = h_θ⁻¹` for `|E| < 2`. -/
private theorem lgr_norm_one_add {E : ℝ} (hE : |E| < 2) :
    ‖1 + normalPhase E‖ = (normalH E)⁻¹ := by
  have hs := lgr_sin_pos hE
  have h1 : 1 + normalPhase E = -(Complex.exp (freeAngle E * Complex.I) *
      (2 * Complex.I * (Real.sin (freeAngle E) : ℂ))) := by
    unfold normalPhase
    rw [Complex.ofReal_sin, Complex.sin]
    set z : ℂ := Complex.exp ((freeAngle E : ℂ) * Complex.I) with hz
    set w : ℂ := Complex.exp (-(freeAngle E : ℂ) * Complex.I) with hw
    have h2 : Complex.exp (2 * ((freeAngle E : ℂ) * Complex.I)) = z * z := by
      rw [hz, ← Complex.exp_add]; ring_nf
    have h3 : w * z = 1 := by
      rw [hw, hz, ← Complex.exp_add]; simp
    rw [h2]
    linear_combination (-1 : ℂ) * h3 + (z * w - z ^ 2) * Complex.I_sq
  rw [h1, norm_neg, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  simp only [Complex.norm_I, Complex.norm_ofNat]
  unfold normalH
  rw [inv_inv, mul_one]

/-- `‖h_θ² g⁻² / (1 + e^{-2iθ})‖ = h_θ³ g⁻²`. -/
private theorem lgr_norm_ratio {E : ℝ} (hE : |E| < 2) (g : ℝ) :
    ‖((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ)‖ / ‖1 + normalPhase E‖ = normalH E ^ 3 / g ^ 2 := by
  rw [lgr_norm_one_add hE, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := (lgr_sin_pos hE).ne'
  unfold normalH
  field_simp

/-- The norm bound behind the derivative of `M`. -/
private theorem lgr_norm_comb_M (D1 D2 m ρ q : ℂ) {a r : ℝ} (hD1 : ‖D1‖ ≤ a)
    (hD2 : ‖D2‖ ≤ 2 * a) (hm : ‖m‖ ≤ 1) (hr : ‖ρ‖ / ‖q‖ = r) :
    ‖D1 - ρ * ((D2 + 2 * ((2 : ℕ) * m ^ (2 - 1) * D1)) / q)‖ ≤ a * (1 + 6 * r) := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hD1
  have hr0 : 0 ≤ r := hr ▸ by positivity
  have hx : ‖D2 + 2 * ((2 : ℕ) * m ^ (2 - 1) * D1)‖ ≤ 6 * a := by
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_ofNat, Nat.cast_ofNat, pow_one, Nat.add_one_sub_one]
    have : ‖m‖ * ‖D1‖ ≤ 1 * a := mul_le_mul hm hD1 (norm_nonneg _) zero_le_one
    linarith
  have hρ : ‖ρ * ((D2 + 2 * ((2 : ℕ) * m ^ (2 - 1) * D1)) / q)‖ ≤ r * (6 * a) := by
    rw [norm_mul, norm_div, ← mul_div_assoc, mul_div_right_comm, hr]
    exact mul_le_mul_of_nonneg_left hx hr0
  calc _ ≤ ‖D1‖ + ‖ρ * ((D2 + 2 * ((2 : ℕ) * m ^ (2 - 1) * D1)) / q)‖ := norm_sub_le _ _
    _ ≤ a + r * (6 * a) := add_le_add hD1 hρ
    _ = a * (1 + 6 * r) := by ring

/-- Derivative of `M` of (11.16) [uvg:eq:M] at `(C', v')` along the fresh block. -/
private theorem lgr_line_corrM (g E : ℝ) (hg : 0 < g) (hE : |E| < 2) {W : ℕ} (hW : 1 ≤ W)
    {X : State W} (hX : IsState X) {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian)
    (y : Ω W 1) :
    ∃ D, HasDerivAt (fun s : ℝ => corrM g E (stepState g E X (V + (s : ℂ) • gueBlock W 1 y 0)))
      D 0 ∧ ‖D‖ ≤ 4 * (normalH E / g) * (1 + 6 * (normalH E ^ 3 / g ^ 2)) / W *
        √(∑ k, y k ^ 2) := by
  obtain ⟨⟨D1, h1, b1⟩, ⟨D2, h2, b2⟩, -⟩ := lgr_line_obs g E hg hW hX hV y
  have h := h1.sub ((((h2.const_add (normalPhase E)).add ((h1.pow 2).const_mul 2)).div_const
    (1 + normalPhase E)).const_mul ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ))
  refine ⟨_, h, ?_⟩
  have hm := norm_obsM_le_one 1 (isState_stepState g E hX
    (lgr_isHermitian_line hV (gueBlock_isHermitian W 1 y 0) 0))
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set a := 4 * (normalH E / g) * √(∑ k, y k ^ 2) / W
  have hD1 : ‖D1‖ ≤ a := b1
  have hD2 : ‖D2‖ ≤ 2 * a := b2.trans (le_of_eq (by simp only [a]; ring))
  refine (lgr_norm_comb_M D1 D2 _ _ _ hD1 hD2 hm (lgr_norm_ratio hE g)).trans (le_of_eq ?_)
  simp only [a]; ring

/-- The norm bound behind the derivative of `F`. -/
private theorem lgr_norm_comb_F (D1 F1 F2 G1 f m fm e ρ q : ℂ) {b r : ℝ} (hD1 : ‖D1‖ ≤ 4 * b)
    (hF1 : ‖F1‖ ≤ 12 * b) (hF2 : ‖F2‖ ≤ 16 * b) (hG1 : ‖G1‖ ≤ 12 * b) (hf : ‖f‖ ≤ 1)
    (hm : ‖m‖ ≤ 1) (hfm : ‖fm‖ ≤ 1) (he : ‖e‖ = 1) (hr : ‖ρ‖ / ‖q‖ = r) :
    ‖F1 - ρ * ((4 * D1 * f + 4 * m * F1 + 2 * F2 - (2 : ℕ) * f ^ (2 - 1) * F1 -
      (e * F1 * fm + e * f * G1)) / q)‖ ≤ (12 + 144 * r) * b := by
  have hb : 0 ≤ b := by linarith [norm_nonneg D1]
  have hr0 : 0 ≤ r := hr ▸ by positivity
  have p1 : ∀ {x y : ℂ} {c : ℝ}, ‖x‖ ≤ 1 → ‖y‖ ≤ c → ‖x * y‖ ≤ c := fun hx hy => by
    rw [norm_mul]
    exact (mul_le_mul hx hy (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
  have p2 : ∀ {x y : ℂ} {c : ℝ}, ‖x‖ ≤ c → ‖y‖ ≤ 1 → ‖x * y‖ ≤ c := fun hx hy => by
    rw [mul_comm]; exact p1 hy hx
  have hx : ‖4 * D1 * f + 4 * m * F1 + 2 * F2 - (2 : ℕ) * f ^ (2 - 1) * F1 -
      (e * F1 * fm + e * f * G1)‖ ≤ 144 * b := by
    have t1 : ‖4 * D1 * f‖ ≤ 16 * b := p2 (by rw [norm_mul]; norm_num; linarith) hf
    have t2 : ‖4 * m * F1‖ ≤ 48 * b := by
      rw [mul_assoc, norm_mul, Complex.norm_ofNat]
      have := p1 hm hF1; linarith
    have t3 : ‖2 * F2‖ ≤ 32 * b := by rw [norm_mul]; norm_num; linarith
    have t4 : ‖(2 : ℕ) * f ^ (2 - 1) * F1‖ ≤ 24 * b := by
      simp only [Nat.add_one_sub_one, pow_one]
      rw [mul_assoc, norm_mul, Complex.norm_natCast]
      have := p1 hf hF1; push_cast; linarith
    have t5 : ‖e * F1 * fm‖ ≤ 12 * b := p2 (p1 he.le hF1) hfm
    have t6 : ‖e * f * G1‖ ≤ 12 * b := p1 (p1 he.le hf) hG1
    calc _ ≤ ‖4 * D1 * f‖ + ‖4 * m * F1‖ + ‖2 * F2‖ + ‖(2 : ℕ) * f ^ (2 - 1) * F1‖ +
          (‖e * F1 * fm‖ + ‖e * f * G1‖) := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl))
            (norm_add_le _ _))
      _ ≤ 144 * b := by linarith
  have hρ : ‖ρ * ((4 * D1 * f + 4 * m * F1 + 2 * F2 - (2 : ℕ) * f ^ (2 - 1) * F1 -
      (e * F1 * fm + e * f * G1)) / q)‖ ≤ r * (144 * b) := by
    rw [norm_mul, norm_div, ← mul_div_assoc, mul_div_right_comm, hr]
    exact mul_le_mul_of_nonneg_left hx hr0
  calc _ ≤ ‖F1‖ + _ := norm_sub_le _ _
    _ ≤ 12 * b + r * (144 * b) := add_le_add hF1 hρ
    _ = (12 + 144 * r) * b := by ring

/-- Derivative of `F` of (11.17) [uvg:eq:F] at `(C', v')` along the fresh block. -/
private theorem lgr_line_corrF (g E : ℝ) (hg : 0 < g) (hE : |E| < 2) {W : ℕ} (hW : 1 ≤ W)
    {X : State W} (hX : IsState X) {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian)
    (y : Ω W 1) :
    ∃ D, HasDerivAt (fun s : ℝ => corrF g E (stepState g E X (V + (s : ℂ) • gueBlock W 1 y 0)))
      D 0 ∧ ‖D‖ ≤ (12 + 144 * (normalH E ^ 3 / g ^ 2)) * (normalH E / g) / √W *
        √(∑ k, y k ^ 2) := by
  obtain ⟨⟨D1, h1, b1⟩, -, ⟨F1, k1, c1⟩, ⟨F2, k2, c2⟩, ⟨G1, l1, d1⟩⟩ :=
    lgr_line_obs g E hg hW hX hV y
  have hA := (((h1.const_mul 4).mul k1).add (k2.const_mul 2)).sub (k1.pow 2)
  have hB := hA.sub ((k1.const_mul (normalPhase E)).mul l1)
  have h := k1.sub ((hB.div_const (1 + normalPhase E)).const_mul
    ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ))
  refine ⟨_, h, ?_⟩
  have hY := isState_stepState g E hX (lgr_isHermitian_line hV (gueBlock_isHermitian W 1 y 0) 0)
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hsW : (0 : ℝ) < √W := Real.sqrt_pos.mpr hW'
  have ht : 0 ≤ normalH E / g := div_nonneg (lgr_normalH_nonneg E) hg.le
  have hσ := Real.sqrt_nonneg (∑ k, y k ^ 2)
  set b := normalH E / g / √W * √(∑ k, y k ^ 2) with hbdef
  have hH : normalH E / g * ‖gueBlock W 1 y 0‖ ≤ b := by
    rw [hbdef, div_eq_mul_inv (normalH E / g), mul_assoc]
    exact mul_le_mul_of_nonneg_left (lgr_norm_gueBlock_le W y) ht
  have hWW : √(W : ℝ) ≤ W := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [show (1 : ℝ) ≤ W by exact_mod_cast hW]
  have hD1 : ‖D1‖ ≤ 4 * b := b1.trans (by
    calc 4 * (normalH E / g) * √(∑ k, y k ^ 2) / W
        ≤ 4 * (normalH E / g) * √(∑ k, y k ^ 2) / √W :=
          div_le_div_of_nonneg_left (by positivity) hsW hWW
      _ = 4 * b := by rw [hbdef]; ring)
  refine (lgr_norm_comb_F D1 F1 F2 G1 _ _ _ _ _ _ hD1 (c1.trans (by nlinarith))
    (c2.trans (by nlinarith)) (d1.trans (by nlinarith)) (norm_obsF_le_one 1 hY)
    (norm_obsM_le_one 1 hY) (norm_obsF_le_one (-1) hY) (lgr_norm_normalPhase E)
    (lgr_norm_ratio hE g)).trans (le_of_eq ?_)
  rw [hbdef]; ring

/-! ### Directional derivatives in the coordinates of the fresh block -/

private theorem lgr_contDiff_corrM (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) :
    ContDiff ℝ 1 (fun ω : Ω W 1 => corrM g E (stepState g E X (gueBlock W 1 ω 0))) := by
  unfold corrM
  have h1 := contDiff_obsM_stepState g E hX 1
  have h2 := contDiff_obsM_stepState g E hX 2
  fun_prop

private theorem lgr_contDiff_corrF (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) :
    ContDiff ℝ 1 (fun ω : Ω W 1 => corrF g E (stepState g E X (gueBlock W 1 ω 0))) := by
  unfold corrF
  have m1 := contDiff_obsM_stepState g E hX 1
  have f1 := contDiff_obsF_stepState g E hX 1
  have f2 := contDiff_obsF_stepState g E hX 2
  have fm := contDiff_obsF_stepState g E hX (-1)
  fun_prop

private theorem lgr_contDiff_stepInc (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) :
    ContDiff ℝ 1 (fun ω : Ω W 1 => ((stepInc g E X (gueBlock W 1 ω 0) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_stepInc g E hX)

/-- Directional derivatives of `M`, `F`, `f_1` and `c` after one step, in the coordinates `ω` of
the fresh block: `|∂_y Z| ≤ c_Z |y|₂` (proof of Lemma 11.2 [uvg:lem:drifts]). -/
private theorem lgr_fderiv_le (g E : ℝ) (hg : 0 < g) (hE : |E| < 2) {W : ℕ} (hW : 1 ≤ W)
    {X : State W} (hX : IsState X) (ω y : Ω W 1) :
    ‖fderiv ℝ (fun ω : Ω W 1 => corrM g E (stepState g E X (gueBlock W 1 ω 0))) ω y‖ ≤
        4 * (normalH E / g) * (1 + 6 * (normalH E ^ 3 / g ^ 2)) / W * √(∑ k, y k ^ 2) ∧
      ‖fderiv ℝ (fun ω : Ω W 1 => corrF g E (stepState g E X (gueBlock W 1 ω 0))) ω y‖ ≤
        (12 + 144 * (normalH E ^ 3 / g ^ 2)) * (normalH E / g) / √W * √(∑ k, y k ^ 2) ∧
      ‖fderiv ℝ (fun ω : Ω W 1 => obsF 1 (stepState g E X (gueBlock W 1 ω 0))) ω y‖ ≤
        12 * (normalH E / g) / √W * √(∑ k, y k ^ 2) ∧
      ‖fderiv ℝ (fun ω : Ω W 1 => ((stepInc g E X (gueBlock W 1 ω 0) : ℝ) : ℂ)) ω y‖ ≤
        2 * (normalH E / g) / √W * √(∑ k, y k ^ 2) := by
  have hV := gueBlock_isHermitian W 1 ω 0
  have ht : 0 ≤ normalH E / g := div_nonneg (lgr_normalH_nonneg E) hg.le
  have hH : normalH E / g * ‖gueBlock W 1 y 0‖ ≤ normalH E / g / √W * √(∑ k, y k ^ 2) := by
    rw [div_eq_mul_inv (normalH E / g), mul_assoc]
    exact mul_le_mul_of_nonneg_left (lgr_norm_gueBlock_le W y) ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨D, hD, hDb⟩ := lgr_line_corrM g E hg hE hW hX hV y
    rw [lgr_fderiv_apply (Z := fun V => corrM g E (stepState g E X V))
      ((lgr_contDiff_corrM g E hX).differentiable one_ne_zero) ω y hD]
    exact hDb
  · obtain ⟨D, hD, hDb⟩ := lgr_line_corrF g E hg hE hW hX hV y
    rw [lgr_fderiv_apply (Z := fun V => corrF g E (stepState g E X V))
      ((lgr_contDiff_corrF g E hX).differentiable one_ne_zero) ω y hD]
    exact hDb
  · obtain ⟨-, -, ⟨D, hD, hDb⟩, -⟩ := lgr_line_obs g E hg hW hX hV y
    rw [lgr_fderiv_apply (Z := fun V => obsF 1 (stepState g E X V))
      ((contDiff_obsF_stepState g E hX 1).differentiable one_ne_zero) ω y hD]
    calc ‖D‖ ≤ 12 * (normalH E / g * ‖gueBlock W 1 y 0‖) := by rw [← mul_assoc]; exact hDb
      _ ≤ 12 * (normalH E / g / √W * √(∑ k, y k ^ 2)) := by gcongr
      _ = _ := by ring
  · obtain ⟨-, -, ⟨d, hd, hdb⟩⟩ := lgr_line_state g E hg hX hV (gueBlock W 1 y 0)
    rw [lgr_fderiv_apply (Z := fun V => ((stepInc g E X V : ℝ) : ℂ))
      ((lgr_contDiff_stepInc g E hX).differentiable one_ne_zero) ω y hd.ofReal_comp]
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc |d| ≤ 2 * (normalH E / g * ‖gueBlock W 1 y 0‖) := by rw [← mul_assoc]; exact hdb
      _ ≤ 2 * (normalH E / g / √W * √(∑ k, y k ^ 2)) := by gcongr
      _ = _ := by ring

/-! ### Constants -/

private theorem lgr_normalH_le {E₀ E : ℝ} (hE₀ : E₀ < 2) (hE : |E| ≤ E₀) :
    normalH E ≤ (2 * √(1 - E₀ ^ 2 / 4))⁻¹ := by
  unfold normalH freeAngle
  rw [Real.sin_arccos]
  have ha := abs_nonneg E
  have h1 : E ^ 2 ≤ E₀ ^ 2 := by
    rw [← sq_abs E]
    exact pow_le_pow_left₀ ha hE 2
  have h2 : 0 < 1 - E₀ ^ 2 / 4 := by nlinarith
  have h3 : √(1 - E₀ ^ 2 / 4) ≤ √(1 - (E / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have h4 : 0 < √(1 - E₀ ^ 2 / 4) := Real.sqrt_pos.mpr h2
  exact inv_anti₀ (by positivity) (by linarith)

/-- `(12 + 144 h³ g⁻²) h g⁻¹ ≤ h₀ (12 + 144 h₀³) g⁻¹` for `0 ≤ h ≤ h₀` and `g ≥ 1`. -/
private theorem lgr_coef_le {h h₀ g : ℝ} (hh : 0 ≤ h) (hh₀ : h ≤ h₀) (hg : 1 ≤ g) :
    (12 + 144 * (h ^ 3 / g ^ 2)) * (h / g) ≤ h₀ * (12 + 144 * h₀ ^ 3) / g := by
  have hg0 : 0 < g := by linarith
  have h1 : h ^ 3 / g ^ 2 ≤ h₀ ^ 3 := by
    calc h ^ 3 / g ^ 2 ≤ h ^ 3 := div_le_self (by positivity) (one_le_pow₀ hg)
      _ ≤ h₀ ^ 3 := pow_le_pow_left₀ hh hh₀ 3
  rw [← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ hg0.le
  have hh0 : 0 ≤ h₀ := hh.trans hh₀
  calc (12 + 144 * (h ^ 3 / g ^ 2)) * h ≤ (12 + 144 * h₀ ^ 3) * h₀ := by gcongr
    _ = h₀ * (12 + 144 * h₀ ^ 3) := by ring

private theorem lgr_two_sq_le {c A g D K : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ A / g / D) (hg : 0 < g)
    (hD : 0 < D) (hK : 2 * A ^ 2 ≤ K) : 2 * c ^ 2 ≤ K / (g ^ 2 * D ^ 2) := by
  calc 2 * c ^ 2 ≤ 2 * (A / g / D) ^ 2 := by gcongr
    _ = 2 * A ^ 2 / (g ^ 2 * D ^ 2) := by field_simp
    _ ≤ K / (g ^ 2 * D ^ 2) := by gcongr

/-- The four gradient bounds with explicit `r = 0` (proof of Lemma 11.2 [uvg:lem:drifts]). -/
private theorem lgr_gradSq_core {E₀ : ℝ} (hE₀ : E₀ < 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X → ∀ ω : Ω W 1,
        gradSq (fun ω => corrM g E (stepState g E X (gueBlock W 1 ω 0))) ω ≤
            K / (g ^ 2 * (W : ℝ) ^ 2) ∧
          gradSq (fun ω => corrF g E (stepState g E X (gueBlock W 1 ω 0))) ω ≤ K / (g ^ 2 * W) ∧
          gradSq (fun ω => obsF 1 (stepState g E X (gueBlock W 1 ω 0))) ω ≤ K / (g ^ 2 * W) ∧
          gradSq (fun ω => ((stepInc g E X (gueBlock W 1 ω 0) : ℝ) : ℂ)) ω ≤ K / (g ^ 2 * W) := by
  set h₀ := (2 * √(1 - E₀ ^ 2 / 4))⁻¹
  set A := h₀ * (12 + 144 * h₀ ^ 3)
  refine ⟨2 * A ^ 2 + 1, by positivity, fun W hW g hg E hE X hX ω => ?_⟩
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have hg0 : 0 < g := by linarith
  have hh := lgr_normalH_nonneg E
  have hh₀ := lgr_normalH_le hE₀ hE
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hsW : (0 : ℝ) < √W := Real.sqrt_pos.mpr hW'
  have hsW2 : √(W : ℝ) ^ 2 = W := Real.sq_sqrt hW'.le
  have hK : 2 * A ^ 2 ≤ 2 * A ^ 2 + 1 := by linarith
  have hcoef := lgr_coef_le hh hh₀ hg
  have ht : 0 ≤ normalH E / g := div_nonneg hh hg0.le
  have hρ : 0 ≤ normalH E ^ 3 / g ^ 2 := by positivity
  have key : ∀ (f : Ω W 1 → ℂ) (c : ℝ), 0 ≤ c →
      (∀ y : Ω W 1, ‖fderiv ℝ f ω y‖ ≤ c * √(∑ k, y k ^ 2)) → gradSq f ω ≤ 2 * c ^ 2 :=
    fun f c _ hb => lgr_sum_sq_le (fderiv ℝ f ω) hb
  have hb := fun y => lgr_fderiv_le g E hg0 hE' hW hX ω y
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (key _ _ (by positivity) fun y => (hb y).1).trans (lgr_two_sq_le (by positivity) ?_ hg0
      hW' hK)
    rw [div_le_div_iff_of_pos_right hW']
    nlinarith
  · refine (key _ _ (by positivity) fun y => (hb y).2.1).trans
      ((lgr_two_sq_le (by positivity) ?_ hg0 hsW hK).trans_eq (by rw [hsW2]))
    rw [div_le_div_iff_of_pos_right hsW]
    linarith
  · refine (key _ _ (by positivity) fun y => (hb y).2.2.1).trans
      ((lgr_two_sq_le (by positivity) ?_ hg0 hsW hK).trans_eq (by rw [hsW2]))
    rw [div_le_div_iff_of_pos_right hsW]
    nlinarith
  · refine (key _ _ (by positivity) fun y => (hb y).2.2.2).trans
      ((lgr_two_sq_le (by positivity) ?_ hg0 hsW hK).trans_eq (by rw [hsW2]))
    rw [div_le_div_iff_of_pos_right hsW]
    nlinarith

/-- The Gaussian Poincaré inequality on one fresh block for a `C¹` function with
`|∂_y f| ≤ c |y|₂` and `gradSq f ≤ B`. -/
private theorem lgr_var_le {W : ℕ} (f : Ω W 1 → ℂ) {c B : ℝ} (hf : ContDiff ℝ 1 f) (hc : 0 ≤ c)
    (hd : ∀ ω y : Ω W 1, ‖fderiv ℝ f ω y‖ ≤ c * √(∑ k, y k ^ 2)) (hB : ∀ ω, gradSq f ω ≤ B) :
    ∫ ω, ‖f ω - ∫ ω', f ω' ∂(μ W 1)‖ ^ 2 ∂(μ W 1) ≤ π ^ 2 / 8 * B := by
  have hb : ∀ x, ‖fderiv ℝ f x‖ ≤ (c * √(Fintype.card (Fin 1 × Fin W × Fin W))) * (1 + ‖x‖) ^ 0 :=
    fun x => by rw [pow_zero, mul_one]; exact lgr_opNorm_le _ hc (hd x)
  refine (poincare_grad_poly f hf hb).trans ?_
  gcongr
  calc ∫ x, gradSq f x ∂(stdGauss (Fin 1 × Fin W × Fin W))
      ≤ ∫ _x, B ∂(stdGauss (Fin 1 × Fin W × Fin W)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
          Finset.sum_nonneg fun _ _ => sq_nonneg _) (integrable_const B)
          (Filter.Eventually.of_forall hB)
    _ = B := by simp

/-- Conditional innovation variances (proof of Lemma 11.2 [uvg:lem:drifts]):
`𝔼|M' - P_g M|² ≤ C g⁻² W⁻²`, `𝔼|F' - P_g F|² ≤ C g⁻² W⁻¹` and `𝔼|c - P_g c|² ≤ C g⁻² W⁻¹`. -/
theorem innovation_var {E₀ : ℝ} (hE₀ : E₀ < 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X →
        ∫ ω, ‖corrM g E (stepState g E X (gueBlock W 1 ω 0)) - transOp g E (corrM g E) X‖ ^ 2
            ∂(μ W 1) ≤ K / (g ^ 2 * (W : ℝ) ^ 2) ∧
          ∫ ω, ‖corrF g E (stepState g E X (gueBlock W 1 ω 0)) - transOp g E (corrF g E) X‖ ^ 2
            ∂(μ W 1) ≤ K / (g ^ 2 * W) ∧
          ∫ ω, (stepInc g E X (gueBlock W 1 ω 0) - incMean g E X) ^ 2 ∂(μ W 1) ≤
            K / (g ^ 2 * W) := by
  obtain ⟨K, hK, h⟩ := lgr_gradSq_core hE₀
  refine ⟨π ^ 2 / 8 * K, by positivity, fun W hW g hg E hE X hX => ?_⟩
  have hE' : |E| < 2 := lt_of_le_of_lt hE hE₀
  have hg0 : 0 < g := by linarith
  have hh := lgr_normalH_nonneg E
  have ht : 0 ≤ normalH E / g := div_nonneg hh hg0.le
  have hd := fun ω y => lgr_fderiv_le g E hg0 hE' hW hX ω y
  have hB := fun ω => h W hW g hg E hE X hX ω
  refine ⟨?_, ?_, ?_⟩
  · have := lgr_var_le _ (lgr_contDiff_corrM g E hX) (by positivity) (fun ω y => (hd ω y).1)
      (fun ω => (hB ω).1)
    rw [mul_div_assoc]
    exact this
  · have := lgr_var_le _ (lgr_contDiff_corrF g E hX) (by positivity) (fun ω y => (hd ω y).2.1)
      (fun ω => (hB ω).2.1)
    rw [mul_div_assoc]
    exact this
  · have := lgr_var_le _ (lgr_contDiff_stepInc g E hX) (by positivity)
      (fun ω y => (hd ω y).2.2.2) (fun ω => (hB ω).2.2.2)
    rw [mul_div_assoc]
    refine le_of_eq_of_le ?_ this
    unfold incMean
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [integral_complex_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end LSBA
