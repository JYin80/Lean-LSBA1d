import LSBA.Gauss.GUELaw

/-!
# The sum of squares `Σ_j ‖G_j y‖²` of a GUE family

For `m` independent GUE blocks with the covariance (1.2) [eq:covariance] and a unit vector `y`,
`Q_y = Σ_j ‖G_j y‖²` has the law of `Σ_j (W⁻¹ ξ_{j,0}² + (2W)⁻¹ Σ_{i < 2(W-1)} ξ_{j,i}²)`;
its exact moment generating function, and the two Chernoff bounds it gives. These are the
pointwise inputs of the lower spectral bound in Appendix G.4 [app:compact-gaussian].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `𝔼 e^{b ξ²} = (1 - 2b)^{-1/2}` for a standard real Gaussian `ξ` and `b < 1/2`. -/
private theorem gueQuadSum_integral_exp_sq {b : ℝ} (hb : b < 1 / 2) :
    ∫ u, Real.exp (b * u ^ 2) ∂(gaussianReal 0 1) = (1 - 2 * b) ^ (-(1 / 2 : ℝ)) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have h : ∀ x : ℝ, gaussianPDFReal 0 1 x • Real.exp (b * x ^ 2) =
      (√(2 * π))⁻¹ * Real.exp (-(1 / 2 - b) * x ^ 2) := by
    intro x
    rw [gaussianPDFReal, smul_eq_mul, mul_assoc, ← Real.exp_add]
    congr 2
    · simp
    · push_cast; ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian]
  have h1 : 0 < 1 - 2 * b := by linarith
  have h2 : π / (1 / 2 - b) = (2 * π) * (1 - 2 * b)⁻¹ := by
    field_simp
  have h3 : (0 : ℝ) < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  rw [h2, Real.sqrt_mul (x := 2 * π) (by positivity), inv_mul_cancel_left₀ h3.ne',
    Real.sqrt_eq_rpow, Real.inv_rpow h1.le, ← Real.rpow_neg h1.le]

/-- A unit vector `y` is the image of a basis vector under a unitary matrix. -/
private theorem gueQuadSum_exists_unitary {W : ℕ} (i₀ : Fin W) {y : Fin W → ℂ}
    (hy : ∑ a, ‖y a‖ ^ 2 = 1) :
    ∃ M : Matrix.unitaryGroup (Fin W) ℂ, (M : Matrix (Fin W) (Fin W) ℂ) *ᵥ Pi.single i₀ 1 = y := by
  set v : EuclideanSpace ℂ (Fin W) := WithLp.toLp 2 y
  have hv : ‖v‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [v, hy]
  have hon : Orthonormal ℂ (({i₀} : Set (Fin W)).domRestrict (fun _ => v)) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi hj
    simp [Set.domRestrict_apply, hv]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨⟨(EuclideanSpace.basisFun (Fin W) ℂ).toBasis.toMatrix b,
    (EuclideanSpace.basisFun _ _).toMatrix_orthonormalBasis_mem_unitary b⟩, ?_⟩
  ext a
  simp [Module.Basis.toMatrix_apply, hb i₀ rfl, v]

/-- `Σ_a |z_a|² = z* z`. -/
private theorem gueQuadSum_sum_sq {W : ℕ} (z : Fin W → ℂ) :
    ((∑ a, ‖z a‖ ^ 2 : ℝ) : ℂ) = star z ⬝ᵥ z := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- A unitary matrix preserves `Σ_a |z_a|²`. -/
private theorem gueQuadSum_sum_sq_mulVec {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ}
    (hU : star U * U = 1) (z : Fin W → ℂ) :
    ∑ a, ‖(U *ᵥ z) a‖ ^ 2 = ∑ a, ‖z a‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [gueQuadSum_sum_sq, gueQuadSum_sum_sq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hU, Matrix.one_mulVec]

/-- The weight of the coordinate `ω (j, α, β) ^ 2` in `‖G_j e₀‖²`: `W⁻¹` on the diagonal entry
`(0, 0)`, `(2W)⁻¹` on the other entries of row or column `0`, and `0` elsewhere. -/
private def gueQuadSum_coef (W : ℕ) (α β : Fin W) : ℝ :=
  if α.val = 0 ∧ β.val = 0 then (W : ℝ)⁻¹
  else if α.val = 0 ∨ β.val = 0 then (2 * W : ℝ)⁻¹ else 0

/-- `‖G_j e₀‖²` in the Gaussian coordinates of the block `G_j`. -/
private theorem gueQuadSum_sum_e₀ (n m : ℕ) (ω : Ω (n + 1) m) (j : Fin m) :
    ∑ a, ‖(gueBlock (n + 1) m ω j *ᵥ Pi.single 0 1) a‖ ^ 2 =
      ∑ α, ∑ β, gueQuadSum_coef (n + 1) α β * ω (j, α, β) ^ 2 := by
  simp only [Matrix.mulVec_single_one, Fin.sum_univ_succ]
  simp only [gueBlock, Nat.cast_add, Nat.cast_one, Nat.ofNat_nonneg, sqrt_mul,
    Complex.ofReal_mul, Matrix.col_apply, Matrix.of_apply, ↓reduceIte, Complex.norm_div,
    Complex.norm_real, norm_eq_abs, Fin.succ_ne_zero, not_lt_zero, Complex.norm_mul,
    gueQuadSum_coef, Fin.coe_ofNat_eq_mod, Nat.zero_mod, and_self, Fin.val_succ,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, or_false, mul_inv_rev, and_true, or_true,
    or_self, zero_mul, sum_const_zero, add_zero]
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hpq : ∀ p q : ℝ, ‖(p : ℂ) - Complex.I * q‖ ^ 2 = p ^ 2 + q ^ 2 := by
    intro p q
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  simp only [div_pow, mul_pow, sq_abs, Real.sq_sqrt hn, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    hpq]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun x _ => ?_
    field_simp

/-- Exact moment generating function of `Q_y = Σ_j ‖G_j y‖²` for a unit vector `y` and
`t < W/2`: `𝔼 e^{t Q_y} = (1 - 2t/W)^{-m/2} (1 - t/W)^{-m(W-1)}`. -/
theorem integral_exp_quadSum_gueBlock {W : ℕ} (hW : 1 ≤ W) (m : ℕ) {y : Fin W → ℂ}
    (hy : ∑ a, ‖y a‖ ^ 2 = 1) {t : ℝ} (ht : t < W / 2) :
    ∫ ω, Real.exp (t * ∑ j, ∑ a, ‖(gueBlock W m ω j *ᵥ y) a‖ ^ 2) ∂(μ W m) =
      (1 - 2 * t / W) ^ (-(m : ℝ) / 2) * (1 - t / W) ^ (-((m : ℝ) * ((W : ℝ) - 1))) := by
  obtain ⟨n, rfl⟩ : ∃ n, W = n + 1 := ⟨W - 1, by omega⟩
  obtain ⟨M, hM⟩ := gueQuadSum_exists_unitary (0 : Fin (n + 1)) hy
  set R : Ω (n + 1) m → ℝ := fun ω => ∑ x : Fin m × Fin (n + 1) × Fin (n + 1),
    gueQuadSum_coef (n + 1) x.2.1 x.2.2 * ω x ^ 2 with hR
  have hQ : ∀ ω, ∑ j, ∑ a, ‖(gueBlock (n + 1) m ω j *ᵥ y) a‖ ^ 2 =
      R (conjMap (n + 1) m (star M) ω) := by
    intro ω
    simp only [hR, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← gueQuadSum_sum_e₀, gueBlock_conjMap, Unitary.coe_star, star_star,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM,
      gueQuadSum_sum_sq_mulVec (U := star (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
        (by rw [star_star]; exact Unitary.coe_mul_star_self M)]
  simp_rw [hQ]
  have hmp := measurePreserving_conjMap (n + 1) m (star M)
  have hcont : Continuous fun ω => Real.exp (t * R ω) := by fun_prop
  rw [← integral_map hmp.measurable.aemeasurable (f := fun ω => Real.exp (t * R ω))
    (by rw [hmp.map_eq]; exact hcont.aestronglyMeasurable), hmp.map_eq]
  have hprod : ∀ ω, Real.exp (t * R ω) =
      ∏ x : Fin m × Fin (n + 1) × Fin (n + 1),
        Real.exp (t * gueQuadSum_coef (n + 1) x.2.1 x.2.2 * ω x ^ 2) := by
    intro ω
    rw [hR, Finset.mul_sum, Real.exp_sum]
    simp only [mul_assoc]
  simp_rw [hprod]
  have hfp := integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (μ := fun _ : Fin m × Fin (n + 1) × Fin (n + 1) => gaussianReal (0 : ℝ) 1)
    (fun x u => Real.exp (t * gueQuadSum_coef (n + 1) x.2.1 x.2.2 * u ^ 2))
  rw [μ, hfp]
  have hc : ∀ α β : Fin (n + 1), t * gueQuadSum_coef (n + 1) α β < 1 / 2 := by
    intro α β
    have hW : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    unfold gueQuadSum_coef
    split_ifs
    · rw [← div_eq_mul_inv, div_lt_iff₀ hW]; linarith
    · rw [← div_eq_mul_inv, div_lt_iff₀ (by positivity)]; nlinarith
    · norm_num
  rw [Finset.prod_congr rfl fun x _ => gueQuadSum_integral_exp_sq (hc x.2.1 x.2.2)]
  simp only [Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fin.prod_univ_succ]
  have hW0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have ha : 0 < 1 - 2 * t / ((n + 1 : ℕ) : ℝ) := by
    rw [sub_pos, div_lt_one hW0]
    linarith
  have hb : 0 < 1 - t / ((n + 1 : ℕ) : ℝ) := by
    rw [sub_pos, div_lt_one hW0]
    linarith
  have h00 : 1 - 2 * (t * gueQuadSum_coef (n + 1) 0 0) = 1 - 2 * t / ((n + 1 : ℕ) : ℝ) := by
    simp only [gueQuadSum_coef, Fin.val_zero, and_self, ite_true]
    ring
  have h0s : ∀ i : Fin n,
      1 - 2 * (t * gueQuadSum_coef (n + 1) 0 i.succ) = 1 - t / ((n + 1 : ℕ) : ℝ) := by
    intro i
    simp only [gueQuadSum_coef, Fin.val_zero, Fin.val_succ, true_or, ite_true,
      Nat.add_one_ne_zero, and_false, ite_false]
    field_simp
  have hs0 : ∀ i : Fin n,
      1 - 2 * (t * gueQuadSum_coef (n + 1) i.succ 0) = 1 - t / ((n + 1 : ℕ) : ℝ) := by
    intro i
    simp only [gueQuadSum_coef, Fin.val_zero, Fin.val_succ, or_true, ite_true,
      Nat.add_one_ne_zero, false_and, ite_false]
    field_simp
  have hss : ∀ i k : Fin n, 1 - 2 * (t * gueQuadSum_coef (n + 1) i.succ k.succ) = 1 := by
    intro i k
    simp [gueQuadSum_coef]
  simp only [h00, h0s, hs0, hss, Real.one_rpow, Finset.prod_const_one, mul_one,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, Real.rpow_def_of_pos ha,
    Real.rpow_def_of_pos hb]
  simp only [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- `e^{t Q_y}` is integrable for `t < W/2`. -/
private theorem gueQuadSum_integrable {W : ℕ} (hW : 1 ≤ W) (m : ℕ) {y : Fin W → ℂ}
    (hy : ∑ a, ‖y a‖ ^ 2 = 1) {t : ℝ} (ht : t < W / 2) :
    Integrable (fun ω => Real.exp (t * ∑ j, ∑ a, ‖(gueBlock W m ω j *ᵥ y) a‖ ^ 2)) (μ W m) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : 0 < 1 - 2 * t / W := by
    rw [sub_pos, div_lt_one hW0]
    linarith
  have h2 : 0 < 1 - t / W := by
    rw [sub_pos, div_lt_one hW0]
    linarith
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_quadSum_gueBlock hW m hy ht]
  exact (mul_pos (Real.rpow_pos_of_pos h1 _) (Real.rpow_pos_of_pos h2 _)).ne'

/-- Lower Chernoff bound: for `0 < ε < 1`,
`P(Q_y ≤ (1 - ε) m) ≤ exp(-m (W - 1) (-ε - log(1 - ε)) + m ε)`. -/
theorem gueBlock_quadSum_lower_tail {W : ℕ} (hW : 1 ≤ W) (m : ℕ) {y : Fin W → ℂ}
    (hy : ∑ a, ‖y a‖ ^ 2 = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    μ W m {ω | ∑ j, ∑ a, ‖(gueBlock W m ω j *ᵥ y) a‖ ^ 2 ≤ (1 - ε) * m} ≤
      ENNReal.ofReal (Real.exp (-((m : ℝ) * ((W : ℝ) - 1)) * (-ε - Real.log (1 - ε)) +
        m * ε)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h1ε : 0 < 1 - ε := by linarith
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = -(ε / (1 - ε) * W) := ⟨_, rfl⟩
  have ht0 : t ≤ 0 := by
    rw [ht_def, neg_nonpos]
    positivity
  have ht : t < W / 2 := by linarith
  have hch := measure_le_le_exp_mul_mgf (μ := μ W m)
    (X := fun ω => ∑ j, ∑ a, ‖(gueBlock W m ω j *ᵥ y) a‖ ^ 2) ((1 - ε) * m) ht0
    (gueQuadSum_integrable hW m hy ht)
  simp only [mgf] at hch
  rw [integral_exp_quadSum_gueBlock hW m hy ht] at hch
  have ha1 : 1 ≤ 1 - 2 * t / W := by
    have : 2 * t / W ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hW0.le
    linarith
  have hb1 : 1 - t / W = (1 - ε)⁻¹ := by
    rw [ht_def]
    field_simp
    ring
  have hlin : -t * ((1 - ε) * m) = ε * W * m := by
    rw [ht_def]
    field_simp
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal (hch.trans ?_)
  rw [hb1, Real.rpow_def_of_pos (inv_pos.2 h1ε), Real.log_inv, hlin]
  calc rexp (ε * W * m) * ((1 - 2 * t / W) ^ (-(m : ℝ) / 2) *
        rexp (-Real.log (1 - ε) * -((m : ℝ) * ((W : ℝ) - 1))))
      ≤ rexp (ε * W * m) * (1 * rexp (-Real.log (1 - ε) * -((m : ℝ) * ((W : ℝ) - 1)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
          (Real.exp_pos _).le
        exact Real.rpow_le_one_of_one_le_of_nonpos ha1 (by linarith)
    _ = _ := by
        rw [one_mul, ← Real.exp_add]
        congr 1
        ring

/-- Upper Chernoff bound: for `0 < ε < 1`, `P(Q_y ≥ (1 + ε) m)
≤ exp(-m (W - 1) (ε - log(1 + ε)) - m ε - (m/2) log((1 - ε)/(1 + ε)))`. -/
theorem gueBlock_quadSum_upper_tail {W : ℕ} (hW : 1 ≤ W) (m : ℕ) {y : Fin W → ℂ}
    (hy : ∑ a, ‖y a‖ ^ 2 = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    μ W m {ω | (1 + ε) * m ≤ ∑ j, ∑ a, ‖(gueBlock W m ω j *ᵥ y) a‖ ^ 2} ≤
      ENNReal.ofReal (Real.exp (-((m : ℝ) * ((W : ℝ) - 1)) * (ε - Real.log (1 + ε)) -
        m * ε - m / 2 * Real.log ((1 - ε) / (1 + ε)))) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h1ε : 0 < 1 + ε := by linarith
  have h2ε : 0 < 1 - ε := by linarith
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = ε / (1 + ε) * W := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by
    rw [ht_def]
    positivity
  have hs : ε / (1 + ε) < 1 / 2 := by
    rw [div_lt_iff₀ h1ε]
    linarith
  have ht : t < W / 2 := by
    rw [ht_def]
    nlinarith
  have hch := measure_ge_le_exp_mul_mgf (μ := μ W m)
    (X := fun ω => ∑ j, ∑ a, ‖(gueBlock W m ω j *ᵥ y) a‖ ^ 2) ((1 + ε) * m) ht0
    (gueQuadSum_integrable hW m hy ht)
  simp only [mgf] at hch
  rw [integral_exp_quadSum_gueBlock hW m hy ht] at hch
  have ha : 1 - 2 * t / W = (1 - ε) / (1 + ε) := by
    rw [ht_def]
    field_simp
    ring
  have hb : 1 - t / W = (1 + ε)⁻¹ := by
    rw [ht_def]
    field_simp
    ring
  have hlin : t * (1 + ε) = ε * W := by
    rw [ht_def]
    field_simp
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal (hch.trans (le_of_eq ?_))
  rw [ha, hb, Real.rpow_def_of_pos (div_pos h2ε h1ε), Real.rpow_def_of_pos (inv_pos.2 h1ε),
    Real.log_inv, ← Real.exp_add, ← Real.exp_add]
  congr 1
  linear_combination (-(m : ℝ)) * hlin

end LSBA
