import LSBA.Gauss.StdGauss
import LSBA.Spectral.BorderInverse

/-!
# The standard complex Gaussian vector

The standard complex Gaussian law on `ℂ` (real and imaginary parts independent `N(0, 1/2)`) and
its product on `ℂ^ι`; the law in real coordinates, unitary invariance, and the second moment
`E‖M(x + b)‖₂² = ‖M‖_F² + ‖M b‖₂²`. The first row of the GUE matrix of (1.2) [eq:covariance],
rescaled, has this law ([APSSS, (2.8)]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The standard complex Gaussian law on `ℂ`: `z = (y₀ + i y₁)/√2` with `y₀, y₁` independent
`N(0, 1)`, so that `E|z|² = 1`. -/
def cGauss : Measure ℂ :=
  (stdGauss (Fin 2)).map fun y => ((Real.sqrt 2)⁻¹ : ℂ) * ⟨y 0, y 1⟩

instance : IsProbabilityMeasure cGauss := by
  unfold cGauss
  infer_instance

/-- The standard complex Gaussian vector on `ℂ^ι`: independent coordinates of law `cGauss`. -/
def stdCGauss (ι : Type*) [Fintype ι] : Measure (ι → ℂ) := Measure.pi fun _ : ι => cGauss

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (stdCGauss ι) := by
  unfold stdCGauss
  infer_instance

/-! ### The law in real coordinates -/

/-- The map `y ↦ (√2)⁻¹ (y₀ + i y₁)` defining `cGauss` is continuous. -/
private lemma cGauss_continuous_mk : Continuous fun y : Fin 2 → ℝ =>
    ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y 0, y 1⟩ : ℂ) := by
  have : (fun y : Fin 2 → ℝ => ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y 0, y 1⟩ : ℂ)) =
      fun y => ((Real.sqrt 2)⁻¹ : ℂ) * ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) := by
    funext y
    rw [Complex.mk_eq_add_mul_I]
  rw [this]
  fun_prop

/-- The coordinate map `y ↦ ((√2)⁻¹ (y_{i,0} + i y_{i,1}))ᵢ` from `ℝ^{ι × 2}` to `ℂ^ι` is
continuous. -/
private lemma cGauss_continuous_coord (ι : Type*) :
    Continuous fun (y : ι × Fin 2 → ℝ) (i : ι) =>
      ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y (i, 0), y (i, 1)⟩ : ℂ) := by
  refine continuous_pi fun i => ?_
  have : (fun y : ι × Fin 2 → ℝ => ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y (i, 0), y (i, 1)⟩ : ℂ)) =
      fun y => ((Real.sqrt 2)⁻¹ : ℂ) * ((y (i, 0) : ℂ) + (y (i, 1) : ℂ) * Complex.I) := by
    funext y
    rw [Complex.mk_eq_add_mul_I]
  rw [this]
  fun_prop

/-- Grouping the coordinates `ℝ^{ι × 2}` as `ι` blocks of `ℝ²` carries the product of `ι` copies
of `stdGauss (Fin 2)` to `stdGauss (ι × Fin 2)`. -/
private lemma cGauss_map_uncurry (ι : Type*) [Fintype ι] :
    (Measure.pi fun _ : ι => stdGauss (Fin 2)).map
      (fun (x : ι → Fin 2 → ℝ) (p : ι × Fin 2) => x p.1 p.2) = stdGauss (ι × Fin 2) := by
  have hm : Measurable (fun (x : ι → Fin 2 → ℝ) (p : ι × Fin 2) => x p.1 p.2) := by
    refine measurable_pi_iff.mpr fun p => ?_
    exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  symm
  unfold stdGauss
  refine Measure.pi_eq fun s hs => ?_
  have hm' : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [Measure.map_apply hm hm']
  have hpre : (fun (x : ι → Fin 2 → ℝ) (p : ι × Fin 2) => x p.1 p.2) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun i : ι => Set.univ.pi fun j : Fin 2 => s (i, j) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp only [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- `stdCGauss ι` in real coordinates: `x_i = (y_{i,0} + i y_{i,1}) / √2` with `y` standard
Gaussian on `ℝ^{ι × 2}`. -/
theorem stdCGauss_eq_map (ι : Type*) [Fintype ι] :
    stdCGauss ι =
      (stdGauss (ι × Fin 2)).map fun y i => ((Real.sqrt 2)⁻¹ : ℂ) * ⟨y (i, 0), y (i, 1)⟩ := by
  have hm : Measurable (fun (x : ι → Fin 2 → ℝ) (p : ι × Fin 2) => x p.1 p.2) := by
    refine measurable_pi_iff.mpr fun p => ?_
    exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  rw [← cGauss_map_uncurry ι, Measure.map_map (cGauss_continuous_coord ι).measurable hm]
  unfold stdCGauss cGauss
  rw [← Measure.pi_map_pi (fun _ => cGauss_continuous_mk.measurable.aemeasurable)]
  rfl

/-! ### Unitary invariance -/

/-- Complex vector from the real coordinates `ι × Fin 2`. -/
private def cGauss_cplx {ι : Type*} (x : ι × Fin 2 → ℝ) : ι → ℂ := fun i => ⟨x (i, 0), x (i, 1)⟩

/-- The real coordinates of a complex vector (inverse of `cGauss_cplx`). -/
private def cGauss_realify {ι : Type*} (y : ι → ℂ) : ι × Fin 2 → ℝ :=
  fun p => if p.2 = 0 then (y p.1).re else (y p.1).im

private lemma cGauss_cplx_realify {ι : Type*} (y : ι → ℂ) :
    cGauss_cplx (cGauss_realify y) = y := by
  funext i
  apply Complex.ext <;> simp [cGauss_cplx, cGauss_realify]

private lemma cGauss_realify_cplx {ι : Type*} (x : ι × Fin 2 → ℝ) :
    cGauss_realify (cGauss_cplx x) = x := by
  funext p
  rcases p with ⟨i, k⟩
  fin_cases k <;> simp [cGauss_cplx, cGauss_realify]

private lemma cGauss_cplx_add {ι : Type*} (x y : ι × Fin 2 → ℝ) :
    cGauss_cplx (x + y) = cGauss_cplx x + cGauss_cplx y := by
  funext i
  apply Complex.ext <;> simp [cGauss_cplx]

private lemma cGauss_cplx_smul {ι : Type*} (c : ℝ) (x : ι × Fin 2 → ℝ) :
    cGauss_cplx (c • x) = (c : ℂ) • cGauss_cplx x := by
  funext i
  apply Complex.ext <;> simp [cGauss_cplx]

private lemma cGauss_realify_add {ι : Type*} (y z : ι → ℂ) :
    cGauss_realify (y + z) = cGauss_realify y + cGauss_realify z := by
  funext p
  by_cases h : p.2 = 0 <;> simp [cGauss_realify, h]

private lemma cGauss_realify_smul {ι : Type*} (c : ℝ) (y : ι → ℂ) :
    cGauss_realify ((c : ℂ) • y) = c • cGauss_realify y := by
  funext p
  by_cases h : p.2 = 0 <;> simp [cGauss_realify, h]

/-- `∑ₚ xₚ² = ∑ᵢ |gᵢ|²` for `g = cGauss_cplx x`. -/
private lemma cGauss_sum_sq {ι : Type*} [Fintype ι] (x : ι × Fin 2 → ℝ) :
    ∑ p, x p ^ 2 = ∑ i, ‖cGauss_cplx x i‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two, Complex.sq_norm]
  simp [cGauss_cplx, Complex.normSq_mk]
  ring

/-- `z* z = ∑ᵢ |zᵢ|²`. -/
private lemma cGauss_star_dotProduct {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    star z ⬝ᵥ z = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
  push_cast
  rfl

/-- A unitary matrix preserves `∑ᵢ |yᵢ|²`. -/
private lemma cGauss_sum_norm_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (y : ι → ℂ) :
    ∑ i, ‖((U : Matrix ι ι ℂ) *ᵥ y) i‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
  have hU : star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  have h : star ((U : Matrix ι ι ℂ) *ᵥ y) ⬝ᵥ ((U : Matrix ι ι ℂ) *ᵥ y) = star y ⬝ᵥ y := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, hU, Matrix.one_mulVec]
  rw [cGauss_star_dotProduct, cGauss_star_dotProduct] at h
  exact_mod_cast h

/-- A unitary `U` of `ℂ^ι` acting on the `2|ι|` real coordinates, as a real isometry. -/
private def cGauss_iso {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) :
    EuclideanSpace ℝ (ι × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ι × Fin 2) where
  toFun z := WithLp.toLp 2
    (cGauss_realify ((U : Matrix ι ι ℂ) *ᵥ (cGauss_cplx z.ofLp)))
  invFun z := WithLp.toLp 2
    (cGauss_realify ((star (U : Matrix ι ι ℂ)) *ᵥ (cGauss_cplx z.ofLp)))
  map_add' a b := by
    simp only [WithLp.ofLp_add, cGauss_cplx_add, Matrix.mulVec_add, cGauss_realify_add,
      WithLp.toLp_add]
  map_smul' c a := by
    simp only [WithLp.ofLp_smul, cGauss_cplx_smul, Matrix.mulVec_smul, cGauss_realify_smul,
      WithLp.toLp_smul, RingHom.id_apply]
  left_inv z := by
    have hU : star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp U.2
    simp only [cGauss_cplx_realify, Matrix.mulVec_mulVec, hU,
      Matrix.one_mulVec, cGauss_realify_cplx, WithLp.toLp_ofLp]
  right_inv z := by
    have hU : (U : Matrix ι ι ℂ) * star (U : Matrix ι ι ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp U.2
    simp only [cGauss_cplx_realify, Matrix.mulVec_mulVec, hU,
      Matrix.one_mulVec, cGauss_realify_cplx, WithLp.toLp_ofLp]
  norm_map' z := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [Real.norm_eq_abs, sq_abs]
    rw [cGauss_sum_sq, cGauss_cplx_realify, cGauss_sum_norm_mulVec, ← cGauss_sum_sq]

/-- `cGauss_iso U` acts on the complex vector of the real coordinates as `U`. -/
private lemma cGauss_iso_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (x : ι × Fin 2 → ℝ) :
    cGauss_cplx (cGauss_iso U (WithLp.toLp 2 x)).ofLp = (U : Matrix ι ι ℂ) *ᵥ (cGauss_cplx x) := by
  change cGauss_cplx (cGauss_realify ((U : Matrix ι ι ℂ) *ᵥ (cGauss_cplx x))) = _
  rw [cGauss_cplx_realify]

/-- Unitary invariance of the standard complex Gaussian vector. -/
theorem measurePreserving_stdCGauss_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    MeasurePreserving (fun x => (U : Matrix ι ι ℂ) *ᵥ x) (stdCGauss ι) (stdCGauss ι) := by
  have hU : Measurable (fun w : ι → ℂ => (U : Matrix ι ι ℂ) *ᵥ w) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hΦ := (cGauss_continuous_coord ι).measurable
  have hR : Measurable (fun x : ι × Fin 2 → ℝ => (cGauss_iso U (WithLp.toLp 2 x)).ofLp) :=
    (WithLp.measurable_ofLp 2 _).comp ((cGauss_iso U).continuous.measurable.comp
      (PiLp.continuous_toLp 2 (fun _ : ι × Fin 2 => ℝ)).measurable)
  rw [stdCGauss_eq_map ι]
  refine ⟨hU, ?_⟩
  rw [Measure.map_map hU hΦ]
  have hcomp : ((fun w : ι → ℂ => (U : Matrix ι ι ℂ) *ᵥ w) ∘ fun (y : ι × Fin 2 → ℝ) (i : ι) =>
      ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y (i, 0), y (i, 1)⟩ : ℂ)) =
      (fun (y : ι × Fin 2 → ℝ) (i : ι) =>
        ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y (i, 0), y (i, 1)⟩ : ℂ)) ∘
        (fun x : ι × Fin 2 → ℝ => (cGauss_iso U (WithLp.toLp 2 x)).ofLp) := by
    funext y
    have h2 : ∀ z : ι × Fin 2 → ℝ, (fun i => ((Real.sqrt 2)⁻¹ : ℂ) * (⟨z (i, 0), z (i, 1)⟩ : ℂ)) =
        ((Real.sqrt 2)⁻¹ : ℂ) • cGauss_cplx z := fun z => by
      funext i
      rfl
    simp only [Function.comp_apply]
    rw [h2, h2, cGauss_iso_apply, Matrix.mulVec_smul]
  rw [hcomp, ← Measure.map_map hΦ hR,
    (measurePreserving_stdGauss_linearIsometry (cGauss_iso U)).map_eq]

/-! ### The second moment -/

/-- A coordinate of `stdGauss Q` is in `L²`. -/
private lemma cGauss_memLp_coord {Q : Type*} [Fintype Q] (p : Q) :
    MemLp (fun y : Q → ℝ => y p) 2 (stdGauss Q) :=
  (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Q => gaussianReal 0 1) p)

/-- `E (∑ₚ rₚ yₚ + r₀)² = ∑ₚ rₚ² + r₀²` under `stdGauss Q`, with integrability. -/
private lemma cGauss_real_aux {Q : Type*} [Fintype Q] (r : Q → ℝ) (r₀ : ℝ) :
    Integrable (fun y : Q → ℝ => (∑ p, r p * y p + r₀) ^ 2) (stdGauss Q) ∧
    ∫ y, (∑ p, r p * y p + r₀) ^ 2 ∂(stdGauss Q) = ∑ p, r p ^ 2 + r₀ ^ 2 := by
  have hL : MemLp (fun y : Q → ℝ => ∑ p, r p * y p) 2 (stdGauss Q) := by
    refine memLp_finsetSum (f := fun p (y : Q → ℝ) => r p * y p) Finset.univ fun p _ => ?_
    exact (cGauss_memLp_coord p).const_mul (r p)
  have hX : MemLp (fun y : Q → ℝ => ∑ p, r p * y p + r₀) 2 (stdGauss Q) :=
    hL.add (memLp_const r₀)
  refine ⟨hX.integrable_sq, ?_⟩
  have hint : ∀ p, Integrable (fun y : Q → ℝ => y p) (stdGauss Q) := fun p =>
    (cGauss_memLp_coord p).integrable one_le_two
  have hmean : ∫ y, (∑ p, r p * y p + r₀) ∂(stdGauss Q) = r₀ := by
    rw [integral_add (hL.integrable one_le_two) (integrable_const _), integral_finsetSum]
    · have : ∀ p, ∫ y, r p * y p ∂(stdGauss Q) = 0 := fun p => by
        rw [integral_const_mul]
        have := integral_comp_eval (μ := fun _ : Q => gaussianReal 0 1) (i := p) (f := id)
          aestronglyMeasurable_id
        simp only [id] at this
        change r p * ∫ y, (fun x : Q → ℝ => x p) y ∂(Measure.pi fun _ : Q => gaussianReal 0 1) = 0
        rw [this, integral_id_gaussianReal, mul_zero]
      simp [this]
    · exact fun p _ => (hint p).const_mul _
  have hvar : Var[fun y : Q → ℝ => ∑ p, r p * y p + r₀; stdGauss Q] = ∑ p, r p ^ 2 := by
    rw [variance_add_const hL.aestronglyMeasurable]
    have := variance_sum_pi (μ := fun _ : Q => gaussianReal 0 1)
      (X := fun p (t : ℝ) => r p * t) (fun p => (memLp_id_gaussianReal' (μ := 0) (v := 1) 2
        (by simp)).const_mul (r p))
    have h2 : (∑ p, fun y : Q → ℝ => r p * y p) = fun y : Q → ℝ => ∑ p, r p * y p := by
      funext y
      simp
    rw [h2] at this
    change Var[fun y : Q → ℝ => ∑ p, r p * y p; Measure.pi fun _ : Q => gaussianReal 0 1] = _
    rw [this]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [variance_const_mul]
    simp
  have := variance_eq_sub hX
  rw [hvar, hmean] at this
  simp only [Pi.pow_apply] at this
  linarith [this]

/-- `E ‖∑ₚ wₚ yₚ + c‖² = ∑ₚ ‖wₚ‖² + ‖c‖²` for complex weights `w` and `y` standard Gaussian on
`ℝ^Q`, with integrability. -/
private lemma cGauss_cplx_aux {Q : Type*} [Fintype Q] (w : Q → ℂ) (c : ℂ) :
    Integrable (fun y : Q → ℝ => ‖∑ p, w p * (y p : ℂ) + c‖ ^ 2) (stdGauss Q) ∧
    ∫ y, ‖∑ p, w p * (y p : ℂ) + c‖ ^ 2 ∂(stdGauss Q) = ∑ p, ‖w p‖ ^ 2 + ‖c‖ ^ 2 := by
  have hre : ∀ y : Q → ℝ, ‖∑ p, w p * (y p : ℂ) + c‖ ^ 2 =
      (∑ p, (w p).re * y p + c.re) ^ 2 + (∑ p, (w p).im * y p + c.im) ^ 2 := by
    intro y
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.re_sum, Complex.im_sum]
    ring
  simp_rw [hre]
  obtain ⟨h1, e1⟩ := cGauss_real_aux (fun p => (w p).re) c.re
  obtain ⟨h2, e2⟩ := cGauss_real_aux (fun p => (w p).im) c.im
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2, e1, e2]
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp only [hsq, Finset.sum_add_distrib]
  ring

/-- Second moment: `E‖M(x + b)‖₂² = ∑ᵢⱼ |M_{ij}|² + ‖M b‖₂²` for a standard complex Gaussian
vector `x`. -/
theorem lintegral_l2Norm_sq_stdCGauss {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix κ ι ℂ) (b : ι → ℂ) :
    ∫⁻ x, ENNReal.ofReal (l2Norm (M *ᵥ (x + b)) ^ 2) ∂(stdCGauss ι) =
      ENNReal.ofReal (∑ i, ∑ j, ‖M i j‖ ^ 2 + l2Norm (M *ᵥ b) ^ 2) := by
  have hΦ := (cGauss_continuous_coord ι).measurable
  have hl : ∀ v : κ → ℂ, l2Norm v ^ 2 = ∑ k, ‖v k‖ ^ 2 := fun v =>
    Real.sq_sqrt (Finset.sum_nonneg fun k _ => by positivity)
  have hmeas : Measurable (fun x : ι → ℂ => ENNReal.ofReal (l2Norm (M *ᵥ (x + b)) ^ 2)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have hc : Continuous (fun x : ι → ℂ => M *ᵥ (x + b)) :=
      Continuous.matrix_mulVec continuous_const (continuous_id.add continuous_const)
    have : Continuous (fun v : κ → ℂ => l2Norm v ^ 2) := by
      have : (fun v : κ → ℂ => l2Norm v ^ 2) = fun v => ∑ k, ‖v k‖ ^ 2 := funext hl
      rw [this]
      fun_prop
    exact (this.comp hc).measurable
  -- the weights of the real coordinates `y_{j,0}`, `y_{j,1}` in the `k`-th row of `M x`
  let w : κ → ι × Fin 2 → ℂ := fun k p => M k p.1 * ((Real.sqrt 2)⁻¹ : ℂ) * (![1, Complex.I] p.2)
  have hrow : ∀ (k : κ) (y : ι × Fin 2 → ℝ),
      (M *ᵥ ((fun i => ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y (i, 0), y (i, 1)⟩ : ℂ)) + b)) k =
        ∑ p, w k p * (y p : ℂ) + (M *ᵥ b) k := by
    intro k y
    rw [Matrix.mulVec_add]
    simp only [Pi.add_apply, w]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mk_eq_add_mul_I]
    ring
  have hw : ∀ k : κ, ∑ p, ‖w k p‖ ^ 2 = ∑ j, ‖M k j‖ ^ 2 := by
    intro k
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, w]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_pow]
    ring
  have hF := fun k => cGauss_cplx_aux (w k) ((M *ᵥ b) k)
  rw [stdCGauss_eq_map ι, lintegral_map hmeas hΦ]
  calc ∫⁻ y, ENNReal.ofReal (l2Norm (M *ᵥ ((fun i => ((Real.sqrt 2)⁻¹ : ℂ) *
            (⟨y (i, 0), y (i, 1)⟩ : ℂ)) + b)) ^ 2) ∂(stdGauss (ι × Fin 2))
      = ∫⁻ y, ENNReal.ofReal (∑ k, ‖∑ p, w k p * (y p : ℂ) + (M *ᵥ b) k‖ ^ 2)
          ∂(stdGauss (ι × Fin 2)) := by
        refine lintegral_congr fun y => ?_
        rw [hl]
        simp_rw [hrow]
    _ = ENNReal.ofReal (∫ y, ∑ k, ‖∑ p, w k p * (y p : ℂ) + (M *ᵥ b) k‖ ^ 2
          ∂(stdGauss (ι × Fin 2))) := by
        symm
        refine ofReal_integral_eq_lintegral_ofReal ?_ (Filter.Eventually.of_forall fun y => ?_)
        · exact integrable_finsetSum _ fun k _ => (hF k).1
        · exact Finset.sum_nonneg fun k _ => by positivity
    _ = _ := by
        rw [integral_finsetSum _ fun k _ => (hF k).1]
        congr 1
        rw [hl (M *ᵥ b), ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [(hF k).2, hw k]

end LSBA
