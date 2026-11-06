import LSBA.Gauss.Stein
import Mathlib

/-!
# The standard Gaussian measure on `ℝ^ι`

The product `Measure.pi` of standard real Gaussians on `ι → ℝ` for a finite `ι`: the vector form
of Gaussian integration by parts (Appendix C.1 [sec:classical-random-matrix]), invariance under
Euclidean isometries, invariance of a pair of independent copies under rotation, and the χ²
tail used in Appendix D.2 [sec:rough-density-proof].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- Standard Gaussian product measure on `ι → ℝ`. -/
def stdGauss (ι : Type*) [Fintype ι] : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (stdGauss ι) := by
  unfold stdGauss; infer_instance

/-! ### Polynomial moments -/

private lemma stdGauss_one_add_abs_pow_le (m : ℕ) (x : ℝ) :
    (1 + |x|) ^ m ≤ 2 ^ m * (1 + |x| ^ m) := by
  have h2 : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hx : (0 : ℝ) ≤ |x| ^ m := by positivity
  rcases le_total |x| 1 with h | h
  · calc (1 + |x|) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
  · calc (1 + |x|) ^ m ≤ (2 * |x|) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = 2 ^ m * |x| ^ m := by rw [mul_pow]
      _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith

/-- Every polynomial moment of `|x|` is finite under the standard Gaussian on `ℝ`. -/
private lemma stdGauss_integrable_one_add_abs_pow (m : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 1) := by
  have hm : MemLp id (m : ENNReal) (gaussianReal (0 : ℝ) 1) :=
    memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) m (ENNReal.natCast_ne_top m)
  have hm' : MemLp id (m : ℕ) (gaussianReal (0 : ℝ) 1) := by simpa using hm
  have h1 : Integrable (fun x : ℝ => ‖id x‖ ^ m) (gaussianReal 0 1) := hm'.integrable_norm_pow'
  have h2 : Integrable (fun x : ℝ => (2 : ℝ) ^ m * (1 + |x| ^ m)) (gaussianReal 0 1) :=
    ((integrable_const (1 : ℝ)).add (by simpa using h1)).const_mul _
  refine h2.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ℝ => (1 + |x|) ^ m).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    exact stdGauss_one_add_abs_pow_le m x

/-- The sup norm is dominated through a product of coordinatewise factors. -/
private lemma stdGauss_one_add_norm_le_prod {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    1 + ‖x‖ ≤ ∏ j, (1 + |x j|) := by
  have hone : ∀ s : Finset ι, (1 : ℝ) ≤ ∏ l ∈ s, (1 + |x l|) := fun s =>
    Finset.one_le_prod₀ fun l _ => by linarith [abs_nonneg (x l)]
  have : ‖x‖ ≤ (∏ j, (1 + |x j|)) - 1 := by
    refine (pi_norm_le_iff_of_nonneg (by linarith [hone Finset.univ])).mpr fun j => ?_
    have hj : 1 + |x j| ≤ ∏ l, (1 + |x l|) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      exact le_mul_of_one_le_right (by positivity) (hone _)
    rw [Real.norm_eq_abs]
    linarith
  linarith

/-- Polynomial functions of the sup norm are integrable under the standard Gaussian on `ℝ^ι`. -/
private lemma stdGauss_integrable_poly (ι : Type*) [Fintype ι] (m : ℕ) :
    Integrable (fun x : ι → ℝ => (1 + ‖x‖) ^ m) (stdGauss ι) := by
  have hprod : Integrable (fun x : ι → ℝ => ∏ j, (1 + |x j|) ^ m) (stdGauss ι) :=
    Integrable.fintype_prod (f := fun _ (t : ℝ) => (1 + |t|) ^ m)
      (fun _ => stdGauss_integrable_one_add_abs_pow m)
  refine hprod.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ι → ℝ => (1 + ‖x‖) ^ m).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity), Finset.prod_pow]
    exact pow_le_pow_left₀ (by positivity) (stdGauss_one_add_norm_le_prod x) m

/-! ### Resampling one coordinate -/

/-- `x` with its `i`-th coordinate replaced by `t`, on pairs `(x, t)`. -/
private def stdGauss_upd {ι : Type*} [DecidableEq ι] (i : ι) (p : (ι → ℝ) × ℝ) : ι → ℝ :=
  Function.update p.1 i p.2

private lemma stdGauss_measurable_upd {ι : Type*} [DecidableEq ι] (i : ι) :
    Measurable (stdGauss_upd i) := by
  refine measurable_pi_iff.mpr fun j => ?_
  by_cases h : j = i
  · subst h
    simpa [stdGauss_upd] using measurable_snd
  · simp only [stdGauss_upd, Function.update_of_ne h]
    exact (measurable_pi_apply j).comp measurable_fst

/-- Replacing the `i`-th coordinate by an independent standard Gaussian leaves `stdGauss ι`
invariant. -/
private lemma stdGauss_map_upd {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    ((stdGauss ι).prod (gaussianReal 0 1)).map (stdGauss_upd i) = stdGauss ι := by
  symm
  unfold stdGauss
  refine Measure.pi_eq fun s hs => ?_
  have hm : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [Measure.map_apply (stdGauss_measurable_upd i) hm]
  have hpre : stdGauss_upd i ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext ⟨ω, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod,
      stdGauss_upd]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [Function.update_of_ne hj] using h1 j
  have hfun : (Measure.pi fun _ : ι => gaussianReal 0 1)
        (Set.univ.pi (Function.update s i Set.univ)) =
      ∏ j ∈ Finset.univ.erase i, gaussianReal 0 1 (s j) := by
    rw [Measure.pi_pi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [Function.update_self, measure_univ, one_mul]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hpre, Measure.prod_prod, hfun, mul_comm,
    Finset.mul_prod_erase Finset.univ (fun j => gaussianReal 0 1 (s j)) (Finset.mem_univ i)]

/-- Vector Stein identity `E[x_i F] = E[∂_i F]` on `ℝ^ι`. -/
theorem integral_coord_mul_stdGauss {ι : Type*} [Fintype ι] [DecidableEq ι] (F : (ι → ℝ) → ℂ)
    (hF : ContDiff ℝ 1 F) {C : ℝ} {k : ℕ} (hb : ∀ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ k)
    (hb' : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ k) (i : ι) :
    ∫ x, (x i : ℂ) * F x ∂(stdGauss ι) = ∫ x, fderiv ℝ F x (Pi.single i 1) ∂(stdGauss ι) := by
  have hFc : Continuous F := hF.continuous
  have hDc : Continuous fun x => fderiv ℝ F x := hF.continuous_fderiv one_ne_zero
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hC : 0 ≤ C := by simpa using (norm_nonneg (F 0)).trans (hb 0)
  have hei : ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ ≤ 1 := by
    rw [Pi.norm_single]; simp
  -- the two integrands and their integrability
  have hGc : Continuous fun x : ι → ℝ => (x i : ℂ) * F x :=
    (Complex.continuous_ofReal.comp (continuous_apply i)).mul hFc
  have hHc : Continuous fun x : ι → ℝ => fderiv ℝ F x (Pi.single i 1) :=
    hDc.clm_apply continuous_const
  have hGint : Integrable (fun x : ι → ℝ => (x i : ℂ) * F x) (stdGauss ι) := by
    refine ((stdGauss_integrable_poly ι (k + 1)).const_mul C).mono' hGc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have hxi : |x i| ≤ 1 + ‖x‖ := by
      have := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at this
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, pow_succ']
    calc |x i| * ‖F x‖ ≤ (1 + ‖x‖) * (C * (1 + ‖x‖) ^ k) :=
          mul_le_mul hxi (hb x) (norm_nonneg _) (by positivity)
      _ = C * ((1 + ‖x‖) * (1 + ‖x‖) ^ k) := by ring
  have hHint : Integrable (fun x : ι → ℝ => fderiv ℝ F x (Pi.single i 1)) (stdGauss ι) := by
    refine ((stdGauss_integrable_poly ι k).const_mul C).mono' hHc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    calc ‖fderiv ℝ F x (Pi.single i 1)‖ ≤ ‖fderiv ℝ F x‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ :=
          (fderiv ℝ F x).le_opNorm _
      _ ≤ ‖fderiv ℝ F x‖ * 1 := by gcongr
      _ ≤ C * (1 + ‖x‖) ^ k := by rw [mul_one]; exact hb' x
  -- transport through the resampling map
  have hmp : MeasurePreserving (stdGauss_upd i) ((stdGauss ι).prod (gaussianReal 0 1))
      (stdGauss ι) := ⟨stdGauss_measurable_upd i, stdGauss_map_upd i⟩
  have hint1 : Integrable (fun p => (stdGauss_upd i p i : ℂ) * F (stdGauss_upd i p))
      ((stdGauss ι).prod (gaussianReal 0 1)) :=
    (hmp.integrable_comp hGc.aestronglyMeasurable).mpr hGint
  have hint2 : Integrable (fun p => fderiv ℝ F (stdGauss_upd i p) (Pi.single i 1))
      ((stdGauss ι).prod (gaussianReal 0 1)) :=
    (hmp.integrable_comp hHc.aestronglyMeasurable).mpr hHint
  have hL : ∫ x, (x i : ℂ) * F x ∂(stdGauss ι) =
      ∫ p, (stdGauss_upd i p i : ℂ) * F (stdGauss_upd i p)
        ∂((stdGauss ι).prod (gaussianReal 0 1)) := by
    have := integral_map (μ := (stdGauss ι).prod (gaussianReal 0 1))
      (stdGauss_measurable_upd i).aemeasurable
      (f := fun x : ι → ℝ => (x i : ℂ) * F x)
      (by rw [hmp.map_eq]; exact hGc.aestronglyMeasurable)
    rw [hmp.map_eq] at this
    exact this
  have hR : ∫ x, fderiv ℝ F x (Pi.single i 1) ∂(stdGauss ι) =
      ∫ p, fderiv ℝ F (stdGauss_upd i p) (Pi.single i 1)
        ∂((stdGauss ι).prod (gaussianReal 0 1)) := by
    have := integral_map (μ := (stdGauss ι).prod (gaussianReal 0 1))
      (stdGauss_measurable_upd i).aemeasurable
      (f := fun x : ι → ℝ => fderiv ℝ F x (Pi.single i 1))
      (by rw [hmp.map_eq]; exact hHc.aestronglyMeasurable)
    rw [hmp.map_eq] at this
    exact this
  rw [hL, hR, integral_prod _ hint1, integral_prod _ hint2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  -- the inner one-dimensional identity along the fibre through `ω`
  have hupd : ∀ t : ℝ, 1 + ‖Function.update ω i t‖ ≤ (1 + ‖ω‖) * (1 + |t|) := by
    intro t
    have : ‖Function.update ω i t‖ ≤ ‖ω‖ + |t| := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self, Real.norm_eq_abs]
        linarith [norm_nonneg ω]
      · rw [Function.update_of_ne hj]
        linarith [norm_le_pi_norm ω j, abs_nonneg t]
    nlinarith [norm_nonneg ω, abs_nonneg t]
  have hpow : ∀ t : ℝ, (1 + ‖Function.update ω i t‖) ^ k ≤ (1 + ‖ω‖) ^ k * (1 + |t|) ^ k := by
    intro t
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (hupd t) k
  have hfd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => F (Function.update ω i s))
      (fderiv ℝ F (Function.update ω i t) (Pi.single i 1)) t := fun t =>
    (hFd (Function.update ω i t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update ω i t)
  have hcont : Continuous fun t : ℝ => fderiv ℝ F (Function.update ω i t) (Pi.single i 1) :=
    (hDc.comp (continuous_const.update i continuous_id)).clm_apply continuous_const
  have key := integral_mul_gaussianReal_poly 1 (f := fun s : ℝ => F (Function.update ω i s))
    (f' := fun t => fderiv ℝ F (Function.update ω i t) (Pi.single i 1)) hfd hcont
    (C := C * (1 + ‖ω‖) ^ k) (k := k)
    (fun t => by
      calc ‖F (Function.update ω i t)‖ ≤ C * (1 + ‖Function.update ω i t‖) ^ k := hb _
        _ ≤ C * ((1 + ‖ω‖) ^ k * (1 + |t|) ^ k) := by gcongr; exact hpow t
        _ = C * (1 + ‖ω‖) ^ k * (1 + |t|) ^ k := by ring)
    (fun t => by
      calc ‖fderiv ℝ F (Function.update ω i t) (Pi.single i 1)‖
          ≤ ‖fderiv ℝ F (Function.update ω i t)‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ :=
            (fderiv ℝ F _).le_opNorm _
        _ ≤ ‖fderiv ℝ F (Function.update ω i t)‖ * 1 := by gcongr
        _ ≤ C * (1 + ‖Function.update ω i t‖) ^ k := by rw [mul_one]; exact hb' _
        _ ≤ C * ((1 + ‖ω‖) ^ k * (1 + |t|) ^ k) := by gcongr; exact hpow t
        _ = C * (1 + ‖ω‖) ^ k * (1 + |t|) ^ k := by ring)
  simpa [stdGauss_upd] using key

/-- Orthogonal invariance of the standard Gaussian on `ℝ^ι`. -/
theorem measurePreserving_stdGauss_linearIsometry {ι : Type*} [Fintype ι]
    (Q : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    MeasurePreserving (fun x : ι → ℝ => (Q (WithLp.toLp 2 x)).ofLp) (stdGauss ι) (stdGauss ι) := by
  have hto : Measurable (fun x : ι → ℝ => WithLp.toLp 2 x) :=
    (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).measurable
  have hof : Measurable (fun z : EuclideanSpace ℝ ι => z.ofLp) := WithLp.measurable_ofLp 2 _
  have hQ : Measurable (fun z : EuclideanSpace ℝ ι => Q z) := Q.continuous.measurable
  have h1 : (stdGauss ι).map (fun x : ι → ℝ => WithLp.toLp 2 x) =
      stdGaussian (EuclideanSpace ℝ ι) := map_pi_eq_stdGaussian
  refine ⟨(hof.comp (hQ.comp hto)), ?_⟩
  have h2 : (fun x : ι → ℝ => (Q (WithLp.toLp 2 x)).ofLp) =
      (fun z : EuclideanSpace ℝ ι => z.ofLp) ∘ (fun z => Q z) ∘
        (fun x : ι → ℝ => WithLp.toLp 2 x) :=
    rfl
  rw [h2, ← Measure.map_map hof (hQ.comp hto), ← Measure.map_map hQ hto, h1,
    stdGaussian_map Q, ← h1, Measure.map_map hof hto]
  have : (fun z : EuclideanSpace ℝ ι => z.ofLp) ∘ (fun x : ι → ℝ => WithLp.toLp 2 x) = id := rfl
  rw [this, Measure.map_id]

/-- Rotation of a pair of independent standard Gaussian vectors:
`(x, y) ↦ (x sin θ + y cos θ, x cos θ - y sin θ)` preserves the product law. -/
theorem measurePreserving_stdGauss_rotation {ι : Type*} [Fintype ι] (θ : ℝ) :
    MeasurePreserving
      (fun q : (ι → ℝ) × (ι → ℝ) =>
        (Real.sin θ • q.1 + Real.cos θ • q.2, Real.cos θ • q.1 - Real.sin θ • q.2))
      ((stdGauss ι).prod (stdGauss ι)) ((stdGauss ι).prod (stdGauss ι)) := by
  -- the rotation as a map of `ι ⊕ ι → ℝ`
  let rot : (ι ⊕ ι → ℝ) → (ι ⊕ ι → ℝ) := fun z j =>
    Sum.elim (fun i => Real.sin θ * z (Sum.inl i) + Real.cos θ * z (Sum.inr i))
      (fun i => Real.cos θ * z (Sum.inl i) - Real.sin θ * z (Sum.inr i)) j
  have hrot : ∀ z, rot (rot z) = z := by
    intro z
    funext j
    rcases j with i | i
    · simp only [rot, Sum.elim_inl, Sum.elim_inr]
      have := Real.sin_sq_add_cos_sq θ
      linear_combination (z (Sum.inl i)) * this
    · simp only [rot, Sum.elim_inl, Sum.elim_inr]
      have := Real.sin_sq_add_cos_sq θ
      linear_combination (z (Sum.inr i)) * this
  have hsq : ∀ z, ∑ j, rot z j ^ 2 = ∑ j, z j ^ 2 := by
    intro z
    simp only [Fintype.sum_sum_type, rot, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Real.sin_sq_add_cos_sq θ
    linear_combination ((z (Sum.inl i)) ^ 2 + (z (Sum.inr i)) ^ 2) * this
  let Q : EuclideanSpace ℝ (ι ⊕ ι) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ι ⊕ ι) :=
    { toFun := fun z => WithLp.toLp 2 (rot z.ofLp)
      invFun := fun z => WithLp.toLp 2 (rot z.ofLp)
      map_add' := by
        intro a b
        ext j
        rcases j with i | i <;> simp [rot] <;> ring
      map_smul' := by
        intro c a
        ext j
        rcases j with i | i <;> simp [rot] <;> ring
      left_inv := fun z => by simp [hrot]
      right_inv := fun z => by simp [hrot]
      norm_map' := by
        intro z
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        simp only [Real.norm_eq_abs, sq_abs]
        exact congrArg Real.sqrt (hsq z.ofLp) }
  have hQ := measurePreserving_stdGauss_linearIsometry Q
  have he := measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ ι => gaussianReal 0 1)
  have hcomp := he.comp (hQ.comp (he.symm (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι => ℝ)))
  have hfun : (fun q : (ι → ℝ) × (ι → ℝ) =>
        (Real.sin θ • q.1 + Real.cos θ • q.2, Real.cos θ • q.1 - Real.sin θ • q.2)) =
      (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι => ℝ) ∘
        (fun x : ι ⊕ ι → ℝ => (Q (WithLp.toLp 2 x)).ofLp) ∘
          (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι => ℝ).symm := by
    funext q
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · change _ = Real.sin θ * q.1 i + Real.cos θ * q.2 i
      simp
    · change _ = Real.cos θ * q.1 i - Real.sin θ * q.2 i
      simp
  rw [hfun]
  exact hcomp

/-- The standard Gaussian density times `exp (x ^ 2 / 4)` equals `(2π)^{-1/2} exp (-x ^ 2 / 4)`. -/
private lemma stdGauss_pdf_mul_exp (x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (x ^ 2 / 4) =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 4) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- `exp (x ^ 2 / 4)` is integrable against the standard Gaussian. -/
private lemma stdGauss_integrable_exp_sq :
    Integrable (fun x : ℝ => Real.exp (x ^ 2 / 4)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)]
  have h := (integrable_exp_neg_mul_sq (b := 1 / 4) (by norm_num)).const_mul
    ((Real.sqrt (2 * π))⁻¹)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x), smul_eq_mul]
  exact (stdGauss_pdf_mul_exp x).symm

/-- `E exp (x ^ 2 / 4) = √2` for the standard Gaussian. -/
private lemma stdGauss_integral_exp_sq :
    ∫ x : ℝ, Real.exp (x ^ 2 / 4) ∂(gaussianReal 0 1) = Real.sqrt 2 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul, stdGauss_pdf_mul_exp]
  rw [integral_const_mul, integral_gaussian]
  have h4 : Real.sqrt (π / (1 / 4)) = Real.sqrt 2 * Real.sqrt (2 * π) := by
    rw [← Real.sqrt_mul (by norm_num)]
    congr 1
    ring
  rw [h4]
  have : Real.sqrt (2 * π) ≠ 0 := by positivity
  field_simp

/-- χ² tail with Chernoff exponent `1/8 < (1 - log 2)/2`. -/
theorem chiSq_tail (ι : Type*) [Fintype ι] :
    stdGauss ι {x | 2 * (Fintype.card ι : ℝ) < ∑ i, x i ^ 2} ≤
      ENNReal.ofReal (Real.exp (-(Fintype.card ι : ℝ) / 8)) := by
  set n : ℕ := Fintype.card ι with hn
  have hprod : (fun x : ι → ℝ => Real.exp ((∑ i, x i ^ 2) / 4)) =
      fun x => ∏ i, Real.exp (x i ^ 2 / 4) := by
    funext x
    rw [Finset.sum_div, Real.exp_sum]
  have hI : Integrable (fun x : ι → ℝ => Real.exp ((∑ i, x i ^ 2) / 4)) (stdGauss ι) := by
    rw [hprod]
    exact Integrable.fintype_prod (fun _ => stdGauss_integrable_exp_sq)
  have hE : ∫ x : ι → ℝ, Real.exp ((∑ i, x i ^ 2) / 4) ∂(stdGauss ι) = Real.sqrt 2 ^ n := by
    rw [hprod]
    unfold stdGauss
    rw [integral_fintype_prod_eq_prod (fun _ (t : ℝ) => Real.exp (t ^ 2 / 4))]
    simp only [stdGauss_integral_exp_sq, Finset.prod_const, Finset.card_univ]
    rfl
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := stdGauss ι)
    (f := fun x : ι → ℝ => Real.exp ((∑ i, x i ^ 2) / 4))
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) hI (Real.exp ((n : ℝ) / 2))
  rw [hE] at hM
  have hsub : {x : ι → ℝ | 2 * (n : ℝ) < ∑ i, x i ^ 2} ⊆
      {x : ι → ℝ | Real.exp ((n : ℝ) / 2) ≤ Real.exp ((∑ i, x i ^ 2) / 4)} := by
    intro x hx
    have hx' : 2 * (n : ℝ) < ∑ i, x i ^ 2 := hx
    exact Real.exp_le_exp.mpr (by linarith)
  have hmono := measure_mono (μ := stdGauss ι) hsub
  have hfin : stdGauss ι {x : ι → ℝ | Real.exp ((n : ℝ) / 2) ≤ Real.exp ((∑ i, x i ^ 2) / 4)}
      = ENNReal.ofReal ((stdGauss ι).real
          {x : ι → ℝ | Real.exp ((n : ℝ) / 2) ≤ Real.exp ((∑ i, x i ^ 2) / 4)}) :=
    (ofReal_measureReal (measure_ne_top _ _)).symm
  refine hmono.trans (hfin.le.trans (ENNReal.ofReal_le_ofReal ?_))
  have h2 : Real.sqrt 2 = Real.exp (Real.log 2 / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  rw [h2, ← Real.exp_nat_mul] at hM
  have hlog := Real.log_two_lt_d9
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos : 0 < Real.exp ((n : ℝ) / 2) := Real.exp_pos _
  refine ((le_div_iff₀' hpos).mpr hM).trans ?_
  rw [← Real.exp_sub]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [mul_le_mul_of_nonneg_left hlog.le hn0]

end LSBA
