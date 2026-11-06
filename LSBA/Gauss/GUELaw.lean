import LSBA.Gauss.StdGauss
import LSBA.Gauss.GUE

/-!
# The law of the GUE blocks

Moments and covariance (1.2) [eq:covariance] of the blocks `gueBlock`, and the two symmetries of
their joint law: common conjugation `V_a ↦ U V_a U*` by a fixed unitary (Appendix D.1
[subsec:pf_thm31], Section 7.5 [app:uniform-continuation]) and relabelling of the blocks
(translation invariance in Appendix D.2 [sec:rough-density-proof]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

open scoped Classical

namespace LSBA

theorem μ_eq_stdGauss (W L : ℕ) : μ W L = stdGauss (Fin L × Fin W × Fin W) := rfl

/-- Common conjugation `V_a ↦ U V_a U*` on the coordinates. -/
def conjMap (W L : ℕ) (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W L) : Ω W L :=
  gueCoord W L fun a =>
    (U : Matrix (Fin W) (Fin W) ℂ) * gueBlock W L ω a * star (U : Matrix (Fin W) (Fin W) ℂ)

/-- Block relabelling `V_a ↦ V_{σ a}` on the coordinates. -/
def shiftMap (W L : ℕ) (σ : Equiv.Perm (Fin L)) (ω : Ω W L) : Ω W L :=
  fun x => ω (σ x.1, x.2)

/-! ### Moments of the coordinates -/

private theorem gueLaw_memLp_coord (W L : ℕ) (x : Fin L × Fin W × Fin W) (p : ℝ≥0∞)
    (hp : p ≠ ∞) : MemLp (fun ω : Ω W L => ω x) p (μ W L) := by
  have h : MemLp id p (gaussianReal (0 : ℝ) 1) := memLp_id_gaussianReal' p hp
  exact h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin L × Fin W × Fin W =>
    gaussianReal (0 : ℝ) 1) x)

private theorem gueLaw_integrable_coord (W L : ℕ) (x : Fin L × Fin W × Fin W) :
    Integrable (fun ω : Ω W L => ω x) (μ W L) :=
  (gueLaw_memLp_coord W L x 1 ENNReal.one_ne_top).integrable le_rfl

private theorem gueLaw_integrable_coord_mul (W L : ℕ) (x y : Fin L × Fin W × Fin W) :
    Integrable (fun ω : Ω W L => ω x * ω y) (μ W L) := by
  have hx := gueLaw_memLp_coord W L x 2 ENNReal.ofNat_ne_top
  have hy := gueLaw_memLp_coord W L y 2 ENNReal.ofNat_ne_top
  exact hx.integrable_mul hy

private theorem gueLaw_integral_coord (W L : ℕ) (x : Fin L × Fin W × Fin W) :
    ∫ ω : Ω W L, ω x ∂(μ W L) = 0 := by
  have h := measurePreserving_eval (fun _ : Fin L × Fin W × Fin W => gaussianReal (0 : ℝ) 1) x
  have h2 := integral_map h.measurable.aemeasurable (f := id)
    (by rw [h.map_eq]; exact aestronglyMeasurable_id)
  have h3 : ∫ y : ℝ, id y ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal
  rw [h.map_eq, h3] at h2
  exact h2.symm

private theorem gueLaw_integral_coord_mul (W L : ℕ) (x y : Fin L × Fin W × Fin W) :
    ∫ ω : Ω W L, ω x * ω y ∂(μ W L) = if x = y then 1 else 0 := by
  by_cases hxy : x = y
  · subst hxy
    have h := measurePreserving_eval (fun _ : Fin L × Fin W × Fin W => gaussianReal (0 : ℝ) 1) x
    have h2 := integral_map h.measurable.aemeasurable (f := fun t : ℝ => t * t)
      (by rw [h.map_eq]; exact (by fun_prop : Continuous fun t : ℝ => t * t).aestronglyMeasurable)
    rw [h.map_eq] at h2
    have h3 : ∫ t : ℝ, t * t ∂(gaussianReal 0 1) = 1 := by
      have hv := variance_id_gaussianReal (μ := (0 : ℝ)) (v := 1)
      have h0 : (gaussianReal (0 : ℝ) 1)[id] = 0 := integral_id_gaussianReal
      rw [variance_of_integral_eq_zero aemeasurable_id h0] at hv
      simpa [sq] using hv
    simp only [↓reduceIte]
    rw [h3] at h2
    exact h2.symm
  · simp only [hxy, ↓reduceIte]
    have hind : IndepFun (fun ω : Ω W L => ω x) (fun ω : Ω W L => ω y) (μ W L) :=
      (iIndepFun_pi (μ := fun _ : Fin L × Fin W × Fin W => gaussianReal (0 : ℝ) 1)
        (X := fun _ t => t) (fun _ => aemeasurable_id)).indepFun hxy
    rw [hind.integral_fun_mul_eq_mul_integral
      (gueLaw_integrable_coord W L x).aestronglyMeasurable
      (gueLaw_integrable_coord W L y).aestronglyMeasurable,
      gueLaw_integral_coord, zero_mul]

/-! ### Moments and covariance of the blocks -/

/-- An entry of a block as a linear combination of its Gaussian coordinates. -/
private theorem gueLaw_gueBlock_apply (W L : ℕ) (ω : Ω W L) (a : Fin L) (α β : Fin W) :
    gueBlock W L ω a α β = ((Real.sqrt W : ℝ) : ℂ)⁻¹ *
      ∑ k : Fin W × Fin W, (ω (a, k.1, k.2) : ℂ) * hermBasis W k α β := by
  rw [gueBlock_eq_sum_hermBasis]
  simp [Matrix.smul_apply, Matrix.sum_apply]

private theorem gueLaw_integrable_term (W L : ℕ) (a : Fin L) (α β : Fin W)
    (k : Fin W × Fin W) :
    Integrable (fun ω : Ω W L => (ω (a, k.1, k.2) : ℂ) * hermBasis W k α β) (μ W L) :=
  (gueLaw_integrable_coord W L (a, k.1, k.2)).ofReal.mul_const _

theorem integrable_gueBlock (W L : ℕ) (a : Fin L) (α β : Fin W) :
    Integrable (fun ω => gueBlock W L ω a α β) (μ W L) := by
  simp_rw [gueLaw_gueBlock_apply]
  exact (integrable_finsetSum _ fun k _ => gueLaw_integrable_term W L a α β k).const_mul _

/-- (1.2) [eq:covariance]. -/
theorem gueBlock_covariance (W L : ℕ) (a b : Fin L) (α β γ δ : Fin W) :
    ∫ ω, gueBlock W L ω a α β * gueBlock W L ω b γ δ ∂(μ W L) =
      if a = b ∧ α = δ ∧ β = γ then ((W : ℂ))⁻¹ else 0 := by
  have hprod : ∀ ω : Ω W L, gueBlock W L ω a α β * gueBlock W L ω b γ δ =
      ((Real.sqrt W : ℝ) : ℂ)⁻¹ * ((Real.sqrt W : ℝ) : ℂ)⁻¹ *
        ∑ k : Fin W × Fin W, ∑ l : Fin W × Fin W,
          ((ω (a, k.1, k.2) * ω (b, l.1, l.2) : ℝ) : ℂ) *
            (hermBasis W k α β * hermBasis W l γ δ) := by
    intro ω
    rw [gueLaw_gueBlock_apply, gueLaw_gueBlock_apply, mul_mul_mul_comm, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    push_cast
    ring
  have hint : ∀ k l : Fin W × Fin W, Integrable (fun ω : Ω W L =>
      ((ω (a, k.1, k.2) * ω (b, l.1, l.2) : ℝ) : ℂ) *
        (hermBasis W k α β * hermBasis W l γ δ)) (μ W L) := fun k l =>
    (gueLaw_integrable_coord_mul W L _ _).ofReal.mul_const _
  have hint' : ∀ k : Fin W × Fin W, Integrable (fun ω : Ω W L =>
      ∑ l : Fin W × Fin W, ((ω (a, k.1, k.2) * ω (b, l.1, l.2) : ℝ) : ℂ) *
        (hermBasis W k α β * hermBasis W l γ δ)) (μ W L) := fun k =>
    integrable_finsetSum _ fun l _ => hint k l
  simp_rw [hprod]
  rw [integral_const_mul, integral_finsetSum _ fun k _ => hint' k]
  have h : ∀ k l : Fin W × Fin W,
      ∫ ω : Ω W L, ((ω (a, k.1, k.2) * ω (b, l.1, l.2) : ℝ) : ℂ) *
        (hermBasis W k α β * hermBasis W l γ δ) ∂(μ W L) =
      if a = b ∧ k = l then hermBasis W k α β * hermBasis W l γ δ else 0 := by
    intro k l
    rw [integral_mul_const, integral_complex_ofReal, gueLaw_integral_coord_mul]
    by_cases hab : a = b <;> by_cases hkl : k = l <;> simp [hab, hkl, Prod.ext_iff]
  have h2 : ∀ k : Fin W × Fin W, ∫ ω : Ω W L, ∑ l : Fin W × Fin W,
      ((ω (a, k.1, k.2) * ω (b, l.1, l.2) : ℝ) : ℂ) *
        (hermBasis W k α β * hermBasis W l γ δ) ∂(μ W L) =
      if a = b then hermBasis W k α β * hermBasis W k γ δ else 0 := by
    intro k
    rw [integral_finsetSum _ fun l _ => hint k l]
    simp only [h]
    by_cases hab : a = b <;> simp [hab]
  simp only [h2]
  by_cases hab : a = b
  · subst hab
    simp only [ite_true, sum_hermBasis_apply_mul_apply, true_and]
    have hs : ((Real.sqrt W : ℝ) : ℂ)⁻¹ * ((Real.sqrt W : ℝ) : ℂ)⁻¹ = (W : ℂ)⁻¹ := by
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg W)]
      simp
    rw [hs]
    split_ifs <;> simp
  · simp [hab]

/-! ### Block relabelling -/

theorem gueBlock_shiftMap (W L : ℕ) (σ : Equiv.Perm (Fin L)) (ω : Ω W L) (a : Fin L) :
    gueBlock W L (shiftMap W L σ ω) a = gueBlock W L ω (σ a) := rfl

theorem measurePreserving_shiftMap (W L : ℕ) (σ : Equiv.Perm (Fin L)) :
    MeasurePreserving (shiftMap W L σ) (μ W L) (μ W L) := by
  let e : Fin L × Fin W × Fin W ≃ Fin L × Fin W × Fin W := Equiv.prodCongr σ (Equiv.refl _)
  have h := measurePreserving_arrowCongr'
    (fun _ : Fin L × Fin W × Fin W => gaussianReal (0 : ℝ) 1)
    (fun _ : Fin L × Fin W × Fin W => gaussianReal (0 : ℝ) 1) e.symm (MeasurableEquiv.refl ℝ)
    (fun _ => MeasurePreserving.id _)
  exact h

/-! ### Common conjugation -/

private theorem gueLaw_conj_isHermitian {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    ((U : Matrix (Fin W) (Fin W) ℂ) * V * star (U : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian at hV ⊢
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hV, Matrix.mul_assoc]

/-- Common conjugation of Appendix D.1 [subsec:pf_thm31], coordinate form. -/
theorem gueBlock_conjMap (W L : ℕ) (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W L) (a : Fin L) :
    gueBlock W L (conjMap W L U ω) a =
      (U : Matrix (Fin W) (Fin W) ℂ) * gueBlock W L ω a * star (U : Matrix (Fin W) (Fin W) ℂ) :=
  congrFun (gueBlock_gueCoord W L _
    fun a => gueLaw_conj_isHermitian U (gueBlock_isHermitian W L ω a)) a

private theorem gueLaw_gueBlock_add (W L : ℕ) (ω ω' : Ω W L) (a : Fin L) :
    gueBlock W L (ω + ω') a = gueBlock W L ω a + gueBlock W L ω' a := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

private theorem gueLaw_gueBlock_smul (W L : ℕ) (c : ℝ) (ω : Ω W L) (a : Fin L) :
    gueBlock W L (c • ω) a = (c : ℂ) • gueBlock W L ω a := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

private theorem gueLaw_gueCoord_add (W L : ℕ) (V V' : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    gueCoord W L (V + V') = gueCoord W L V + gueCoord W L V' := by
  funext x
  simp only [gueCoord, Pi.add_apply, Matrix.add_apply, Complex.add_re, Complex.add_im]
  split_ifs <;> ring

private theorem gueLaw_gueCoord_smul (W L : ℕ) (c : ℝ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    gueCoord W L (fun a => (c : ℂ) • V a) = c • gueCoord W L V := by
  funext x
  simp only [gueCoord, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  split_ifs <;> ring

private theorem gueLaw_conjMap_add (W L : ℕ) (U : Matrix.unitaryGroup (Fin W) ℂ)
    (ω ω' : Ω W L) : conjMap W L U (ω + ω') = conjMap W L U ω + conjMap W L U ω' := by
  rw [conjMap, conjMap, conjMap, ← gueLaw_gueCoord_add]
  congr 1
  funext a
  simp only [gueLaw_gueBlock_add, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]

private theorem gueLaw_conjMap_smul (W L : ℕ) (U : Matrix.unitaryGroup (Fin W) ℂ)
    (c : ℝ) (ω : Ω W L) : conjMap W L U (c • ω) = c • conjMap W L U ω := by
  rw [conjMap, conjMap, ← gueLaw_gueCoord_smul]
  congr 1
  funext a
  simp only [gueLaw_gueBlock_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- The trace of the square of a block, in terms of its Gaussian coordinates. -/
private theorem gueLaw_trace_gueBlock_mul_self (W L : ℕ) (ω : Ω W L) (a : Fin L) :
    (gueBlock W L ω a * gueBlock W L ω a).trace =
      (W : ℂ)⁻¹ * ∑ k : Fin W × Fin W, (ω (a, k.1, k.2) : ℂ) ^ 2 := by
  rw [gueBlock_eq_sum_hermBasis]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Finset.sum_mul_sum,
    Matrix.trace_sum, smul_eq_mul, trace_hermBasis_mul]
  have hs : ((Real.sqrt W : ℝ) : ℂ)⁻¹ * ((Real.sqrt W : ℝ) : ℂ)⁻¹ = (W : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg W)]
    simp
  rw [← mul_assoc, hs]
  congr 1
  simp [mul_ite, sq]

private theorem gueLaw_sum_sq_block (W L : ℕ) (ω : Ω W L) (a : Fin L) :
    (W : ℂ) * (gueBlock W L ω a * gueBlock W L ω a).trace =
      ∑ k : Fin W × Fin W, (ω (a, k.1, k.2) : ℂ) ^ 2 := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp
  · have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
    rw [gueLaw_trace_gueBlock_mul_self, ← mul_assoc, mul_inv_cancel₀ hW', one_mul]

private theorem gueLaw_trace_conj {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ)
    (V : Matrix (Fin W) (Fin W) ℂ) :
    ((U : Matrix (Fin W) (Fin W) ℂ) * V * star (U : Matrix (Fin W) (Fin W) ℂ) *
        ((U : Matrix (Fin W) (Fin W) ℂ) * V * star (U : Matrix (Fin W) (Fin W) ℂ))).trace =
      (V * V).trace := by
  have h1 : star (U : Matrix (Fin W) (Fin W) ℂ) * U = 1 := Unitary.coe_star_mul_self U
  calc _ = ((U : Matrix (Fin W) (Fin W) ℂ) *
          (V * (star (U : Matrix (Fin W) (Fin W) ℂ) * U) * V *
            star (U : Matrix (Fin W) (Fin W) ℂ))).trace := by simp only [Matrix.mul_assoc]
    _ = ((V * (star (U : Matrix (Fin W) (Fin W) ℂ) * U) * V *
            star (U : Matrix (Fin W) (Fin W) ℂ)) * U).trace := Matrix.trace_mul_comm _ _
    _ = (V * (star (U : Matrix (Fin W) (Fin W) ℂ) * U) * V *
          (star (U : Matrix (Fin W) (Fin W) ℂ) * U)).trace := by simp only [Matrix.mul_assoc]
    _ = (V * V).trace := by rw [h1]; simp

/-- Conjugation preserves the Euclidean norm of the coordinates. -/
private theorem gueLaw_sum_sq_conjMap (W L : ℕ) (U : Matrix.unitaryGroup (Fin W) ℂ)
    (ω : Ω W L) : ∑ x, conjMap W L U ω x ^ 2 = ∑ x, ω x ^ 2 := by
  apply Complex.ofReal_injective
  have h : ∀ ω : Ω W L, ((∑ x, ω x ^ 2 : ℝ) : ℂ) =
      ∑ a : Fin L, (W : ℂ) * (gueBlock W L ω a * gueBlock W L ω a).trace := by
    intro ω
    simp only [gueLaw_sum_sq_block, Fintype.sum_prod_type, Complex.ofReal_sum, Complex.ofReal_pow]
  rw [h, h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [gueBlock_conjMap, gueLaw_trace_conj]

/-- Conjugation by `U` as a linear isometry of the coordinate space. -/
private def gueLaw_linIso (W L : ℕ) (U : Matrix.unitaryGroup (Fin W) ℂ) :
    EuclideanSpace ℝ (Fin L × Fin W × Fin W) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin L × Fin W × Fin W) where
  toFun z := WithLp.toLp 2 (conjMap W L U z.ofLp)
  map_add' z z' := by
    ext x
    exact congrFun (gueLaw_conjMap_add W L U z.ofLp z'.ofLp) x
  map_smul' c z := by
    ext x
    exact congrFun (gueLaw_conjMap_smul W L U c z.ofLp) x
  norm_map' z := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simpa [Real.norm_eq_abs, sq_abs] using gueLaw_sum_sq_conjMap W L U z.ofLp

/-- Unitary invariance of the block GUE law under common conjugation. -/
theorem measurePreserving_conjMap (W L : ℕ) (U : Matrix.unitaryGroup (Fin W) ℂ) :
    MeasurePreserving (conjMap W L U) (μ W L) (μ W L) :=
  measurePreserving_stdGauss_linearIsometry ((gueLaw_linIso W L U).toLinearIsometryEquiv rfl)

end LSBA
