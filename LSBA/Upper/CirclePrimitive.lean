import LSBA.Upper.CircleRotation
import LSBA.Analysis.Sawtooth

/-!
# The canonical primitive along the circles

For a function `p` of the projection pair, the primitive along the circles
`ψ_p(P_U, P_Y) = (2π)⁻¹ ∫_0^{2π} (t - π) p(R_t P_U R_t*, R_t P_Y R_t*) dt`, with `R_t` the
rotation of the circle of `U` (proof of Lemma F.3 [lem:c-operators]). It needs no frame of the
circle and is `C¹` when `p` is; on the isotropic flags its derivative along the circle is
`p - ∫ p dm_U`, and `|ψ_p| ≤ 2π (∫ p dm_U + ε)` on the circle of `U` when `p ≥ -ε` on the flags.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The primitive `ψ_p(P_U, P_Y) = (2π)⁻¹ ∫_0^{2π} (t - π) p(R_t P_U R_t*, R_t P_Y R_t*) dt`
along the circles (proof of Lemma F.3 [lem:c-operators]). -/
def circlePrim {W : ℕ}
    (p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ)
    (z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ℝ :=
  (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), (t - π) *
    p (circleRot z.1 t * z.1 * (circleRot z.1 t)ᴴ, circleRot z.1 t * z.2 * (circleRot z.1 t)ᴴ)

/-- A `C¹` function of `(x, t)` has a `C¹` interval integral in `x`. -/
private theorem circlePrimitive_contDiff_integral {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] {G : X × ℝ → ℝ} (hG : ContDiff ℝ 1 G) (a b : ℝ) :
    ContDiff ℝ 1 (fun x => ∫ t in a..b, G (x, t)) := by
  have : ProperSpace X := FiniteDimensional.proper_real X
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  set F' : X → ℝ → X →L[ℝ] ℝ := fun x t =>
    (fderiv ℝ G (x, t)).comp (ContinuousLinearMap.inl ℝ X ℝ)
  have hF'c : Continuous (fun q : X × ℝ => F' q.1 q.2) := by
    refine Continuous.clm_comp ?_ continuous_const
    exact hD
  have hdiff : ∀ x t, HasFDerivAt (fun x => G (x, t)) (F' x t) x := fun x t =>
    ((hG.differentiable one_ne_zero (x, t)).hasFDerivAt).comp x (hasFDerivAt_prodMk_left x t)
  have hGc : Continuous G := hG.continuous
  have key : ∀ x₀, HasFDerivAt (fun x => ∫ t in a..b, G (x, t)) (∫ t in a..b, F' x₀ t) x₀ := by
    intro x₀
    have hK : IsCompact (Metric.closedBall x₀ 1 ×ˢ Set.uIcc a b) :=
      (isCompact_closedBall x₀ 1).prod isCompact_uIcc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (f := fun q : X × ℝ => F' q.1 q.2) hF'c.continuousOn
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
      (Metric.closedBall_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun x => ?_
      exact (hGc.comp (Continuous.prodMk_right x)).aestronglyMeasurable
    · exact (hGc.comp (Continuous.prodMk_right x₀)).intervalIntegrable _ _
    · exact (hF'c.comp (Continuous.prodMk_right x₀)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t ht x hx => ?_
      exact hC (x, t) ⟨hx, Set.uIoc_subset_uIcc ht⟩
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t _ x _ => hdiff x t
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (key x).differentiableAt, ?_⟩
  have : fderiv ℝ (fun x => ∫ t in a..b, G (x, t)) = fun x => ∫ t in a..b, F' x t :=
    funext fun x => (key x).fderiv
  rw [this]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF'c a b

/-- Conjugate transpose is a real-linear map, hence smooth. -/
private theorem circlePrimitive_contDiff_conjTranspose {m : Type*} [Fintype m] [DecidableEq m]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞}
    {f : X → Matrix m m ℂ} (hf : ContDiff ℝ n f) : ContDiff ℝ n (fun x => (f x)ᴴ) := by
  let L : Matrix m m ℂ →ₗ[ℝ] Matrix m m ℂ :=
    { toFun := fun A => Aᴴ
      map_add' := fun A B => Matrix.conjTranspose_add A B
      map_smul' := fun r A => by simp [Matrix.conjTranspose_smul] }
  exact (⟨L, LinearMap.continuous_of_finiteDimensional L⟩ :
    Matrix m m ℂ →L[ℝ] Matrix m m ℂ).contDiff.comp hf

/-- `(P, t) ↦ R_t` is smooth. -/
private theorem circlePrimitive_contDiff_rot {W : ℕ} {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ => circleRot q.1 q.2) := by
  have hQ : ContDiff ℝ n
      (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ => quotProj q.1) := by
    unfold quotProj
    have h1 : ContDiff ℝ n (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ => q.1) :=
      contDiff_fst
    have h2 := (contDiff_const (c := isoJ W)).mul h1
    have h3 := h2.mul (contDiff_const (c := isoJ W))
    exact ((contDiff_const (c := (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))).sub h1).sub h3
  have h1 : ContDiff ℝ n
      (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ => ((q.2 / 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_snd.div_const 2)
  have he1 : ContDiff ℝ n (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ =>
      Complex.exp (-(((q.2 / 2 : ℝ) : ℂ) * Complex.I))) :=
    ((h1.mul contDiff_const).neg).cexp
  have he2 : ContDiff ℝ n (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ =>
      Complex.exp (((q.2 / 2 : ℝ) : ℂ) * Complex.I)) :=
    ((h1.mul contDiff_const)).cexp
  have hA : ContDiff ℝ n (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ =>
      (1 / 2 : ℂ) • (quotProj q.1 * (1 + isoJ W))) :=
    (contDiff_const (c := (1 / 2 : ℂ))).smul (hQ.mul contDiff_const)
  have hB : ContDiff ℝ n (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ =>
      (1 / 2 : ℂ) • (quotProj q.1 * (1 - isoJ W))) :=
    (contDiff_const (c := (1 / 2 : ℂ))).smul (hQ.mul contDiff_const)
  have hC := (contDiff_const (c := (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))).sub hQ
  have hD := he1.smul hA
  have hE := he2.smul hB
  exact (hC.add hD).add hE

/-- `R_t P_Y R_t*` is smooth in `t`. -/
private theorem circlePrimitive_contDiff_conj {W : ℕ} {n : WithTop ℕ∞}
    (P Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ContDiff ℝ n (fun t : ℝ => circleRot P t * Y * (circleRot P t)ᴴ) := by
  have hpair : ContDiff ℝ n
      (fun t : ℝ => ((P, t) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ)) :=
    contDiff_const.prodMk contDiff_id
  have hR0 := ContDiff.comp (g := fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ =>
      circleRot q.1 q.2) (circlePrimitive_contDiff_rot (W := W) (n := n)) hpair
  have hR : ContDiff ℝ n (fun t : ℝ => circleRot P t) := by
    simpa only [Function.comp_def] using hR0
  exact (hR.mul contDiff_const).mul (circlePrimitive_contDiff_conjTranspose hR)

/-- `R_t P_Y R_t*` is continuous in `t`. -/
private theorem circlePrimitive_continuous_conj {W : ℕ}
    (P Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Continuous (fun t : ℝ => circleRot P t * Y * (circleRot P t)ᴴ) :=
  (circlePrimitive_contDiff_conj (n := 0) P Y).continuous

/-- The derivative of `t ↦ R_t Y R_t*` is `[K, R_t Y R_t*]`. -/
private theorem circlePrimitive_hasDerivAt_conj {W : ℕ} (hW : 1 ≤ W)
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hP : P ∈ isoBases W)
    (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (t : ℝ) :
    HasDerivAt (fun t => circleRot P t * Y * (circleRot P t)ᴴ)
      (circleGen P * (circleRot P t * Y * (circleRot P t)ᴴ) -
        circleRot P t * Y * (circleRot P t)ᴴ * circleGen P) t := by
  have hKh : (circleGen P)ᴴ = -circleGen P := by
    obtain ⟨hQh, -, hJQ, -, -⟩ := quotProj_spec hW hP
    unfold circleGen
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hQh.eq, isoJ_conjTranspose, hJQ,
      ← neg_smul]
    congr 1
    simp only [star_neg, star_div₀, Complex.star_def, Complex.conj_I, map_ofNat]
    ring
  have hR := (circleRot_spec hW hP 0 t).2.2.2.2.2
  have hRs : HasDerivAt (fun t => (circleRot P t)ᴴ) ((circleGen P * circleRot P t)ᴴ) t := hR.star
  convert (hR.mul_const Y).mul hRs using 1
  rw [Matrix.conjTranspose_mul, hKh]
  simp only [Matrix.mul_neg, Matrix.mul_assoc]
  abel

/-- For a flag `y`, `R_t y` is the flag `(P_U, R_t P_Y R_t*)`. -/
private theorem circlePrimitive_flagAct {W : ℕ} (hW : 1 ≤ W) (y : IsoFlag W) (t : ℝ) :
    ((flagAct (circleRot y.1.1 t) y : IsoFlag W) :
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) =
      (y.1.1, circleRot y.1.1 t * y.1.2 * (circleRot y.1.1 t)ᴴ) := by
  have hP := y.2.1
  have hYY : y.1.2 * y.1.2 = y.1.2 := y.2.2.2.1
  have spec := circleRot_spec hW hP 0 t
  have hPR : y.1.1 * (circleRot y.1.1 t)ᴴ = y.1.1 := by
    have h := congrArg Matrix.conjTranspose spec.2.2.2.2.1
    rwa [Matrix.conjTranspose_mul, hP.1.eq] at h
  rw [flagAct_coe spec.2.1, flagProj_of_mem_unitaryGroup spec.1 hP.2.1,
    flagProj_of_mem_unitaryGroup spec.1 hYY, Matrix.mul_assoc _ y.1.1, hPR, spec.2.2.2.2.1]

/-- On a flag, `t ↦ R_t P_Y R_t*` is `2π`-periodic. -/
private theorem circlePrimitive_periodic {W : ℕ} (hW : 1 ≤ W) (y : IsoFlag W) (u : ℝ) :
    circleRot y.1.1 (u + 2 * π) * y.1.2 * (circleRot y.1.1 (u + 2 * π))ᴴ =
      circleRot y.1.1 u * y.1.2 * (circleRot y.1.1 u)ᴴ := by
  obtain ⟨e, f, hef⟩ := exists_isCircleBasis hW y.2.1
  obtain ⟨θ₀, hθ₀⟩ := exists_circlePair_eq y hef
  have hx : y = ⟨circlePair y.1.1 e f θ₀, circlePair_mem_isoFlags y.2.1 hef θ₀⟩ :=
    Subtype.ext hθ₀
  have hφ1 : ∀ t : ℝ, ((flagAct (circleRot y.1.1 t) y : IsoFlag W) :
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) =
      circlePair y.1.1 e f (θ₀ + t) := by
    intro t
    calc _ = ((flagAct (circleRot y.1.1 t)
          ⟨circlePair y.1.1 e f θ₀, circlePair_mem_isoFlags y.2.1 hef θ₀⟩ : IsoFlag W) :
          Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
            Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :=
        congrArg (fun y' => ((flagAct (circleRot y.1.1 t) y' : IsoFlag W) :
          Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
            Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) hx
      _ = _ := flagAct_circleRot_circlePair hW y hef θ₀ t
  have hper : circlePair y.1.1 e f (θ₀ + (u + 2 * π)) = circlePair y.1.1 e f (θ₀ + u) := by
    have h : Complex.exp (((θ₀ + (u + 2 * π) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((θ₀ + u : ℝ) : ℂ) * Complex.I) := by
      have h' : ((θ₀ + (u + 2 * π) : ℝ) : ℂ) * Complex.I =
          ((θ₀ + u : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I := by
        push_cast
        ring
      rw [h']
      exact Complex.exp_periodic _
    unfold circlePair circleVec
    rw [h]
  have h2 := congrArg Prod.snd (hφ1 (u + 2 * π))
  have h3 := congrArg Prod.snd (hφ1 u)
  rw [circlePrimitive_flagAct hW y] at h2 h3
  exact h2.trans ((congrArg Prod.snd hper).trans h3.symm)

/-- The mean of a continuous function of the flag over the circle of `y`:
`∫ g dm_U = (2π)⁻¹ ∫_0^{2π} g(P_U, R_t P_Y R_t*) dt`. -/
private theorem circlePrimitive_integral_circleMeasure {W : ℕ} (hW : 1 ≤ W)
    {g : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ}
    (hg : Continuous g) (y : IsoFlag W) :
    ∫ z, g z.1 ∂(circleMeasure y) =
      (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π),
        g (y.1.1, circleRot y.1.1 t * y.1.2 * (circleRot y.1.1 t)ᴴ) := by
  have hφc : Continuous (fun t => flagAct (circleRot y.1.1 t) y) := by
    refine continuous_induced_rng.2 ?_
    have h : (Subtype.val ∘ fun t => flagAct (circleRot y.1.1 t) y) =
        fun t => (y.1.1, circleRot y.1.1 t * y.1.2 * (circleRot y.1.1 t)ᴴ) :=
      funext (circlePrimitive_flagAct hW y)
    rw [h]
    exact continuous_const.prodMk (circlePrimitive_continuous_conj _ _)
  have hgc : Continuous (fun z : IsoFlag W => g z.1) := hg.comp continuous_subtype_val
  rw [circleMeasure_eq_map_circleRot hW y,
    integral_map hφc.measurable.aemeasurable hgc.aestronglyMeasurable]
  unfold angleMeas
  rw [integral_smul_measure, ← intervalIntegral.integral_of_le (by positivity),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  congr 2
  funext t
  rw [circlePrimitive_flagAct hW y]

/-- `ψ_p(P, R_s Y R_s*) = S f (s)` for `f(u) = p(P, R_u Y R_u*)`. -/
private theorem circlePrim_conj {W : ℕ} (hW : 1 ≤ W)
    {p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ}
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hP : P ∈ isoBases W)
    (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (s : ℝ) :
    circlePrim p (P, circleRot P s * Y * (circleRot P s)ᴴ) =
      sawtooth (fun u => p (P, circleRot P u * Y * (circleRot P u)ᴴ)) s := by
  unfold circlePrim sawtooth
  congr 2
  funext t
  have spec := circleRot_spec hW hP t s
  have hRP := (circleRot_spec hW hP 0 t).2.2.2.2.1
  have hPR : P * (circleRot P t)ᴴ = P := by
    have h := congrArg Matrix.conjTranspose hRP
    rwa [Matrix.conjTranspose_mul, hP.1.eq] at h
  have h1 : circleRot P t * P * (circleRot P t)ᴴ = P := by
    rw [Matrix.mul_assoc, hPR, hRP]
  have h2 : circleRot P t * (circleRot P s * Y * (circleRot P s)ᴴ) * (circleRot P t)ᴴ =
      circleRot P (s + t) * Y * (circleRot P (s + t))ᴴ := by
    have hc : circleRot P (s + t) = circleRot P t * circleRot P s := by
      rw [add_comm]; exact spec.2.2.1
    rw [hc, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  change (t - π) * p (circleRot P t * P * (circleRot P t)ᴴ,
      circleRot P t * (circleRot P s * Y * (circleRot P s)ᴴ) * (circleRot P t)ᴴ) = _
  rw [h1, h2]

/-- `ψ_p` is `C¹` when `p` is. -/
theorem contDiff_circlePrim {W : ℕ}
    {p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ}
    (hp : ContDiff ℝ 1 p) : ContDiff ℝ 1 (circlePrim p) := by
  have hg : ContDiff ℝ 1 (fun q : (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) × ℝ => (q.1.1, q.2)) :=
    contDiff_fst.fst.prodMk contDiff_snd
  have hR0 := ContDiff.comp (g := fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ =>
      circleRot q.1 q.2) (circlePrimitive_contDiff_rot (W := W) (n := 1)) hg
  have hR : ContDiff ℝ 1 (fun q : (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) × ℝ => circleRot q.1.1 q.2) := by
    simpa only [Function.comp_def] using hR0
  have hRh := circlePrimitive_contDiff_conjTranspose hR
  have hΦ : ContDiff ℝ 1 (fun q : (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) × ℝ =>
      (circleRot q.1.1 q.2 * q.1.1 * (circleRot q.1.1 q.2)ᴴ,
        circleRot q.1.1 q.2 * q.1.2 * (circleRot q.1.1 q.2)ᴴ)) :=
    ((hR.mul contDiff_fst.fst).mul hRh).prodMk ((hR.mul contDiff_fst.snd).mul hRh)
  have hG : ContDiff ℝ 1 (fun q : (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) × ℝ =>
      (q.2 - π) * p (circleRot q.1.1 q.2 * q.1.1 * (circleRot q.1.1 q.2)ᴴ,
        circleRot q.1.1 q.2 * q.1.2 * (circleRot q.1.1 q.2)ᴴ)) :=
    (contDiff_snd.sub contDiff_const).mul (hp.comp hΦ)
  exact contDiff_const.mul (circlePrimitive_contDiff_integral hG 0 (2 * π))

/-- On the flags, the derivative of `ψ_p` along the circle is `p - ∫ p dm_U` (proof of Lemma F.3
[lem:c-operators]). -/
theorem circleDeriv_circlePrim {W : ℕ} (hW : 1 ≤ W)
    {p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ}
    (hp : ContDiff ℝ 1 p) (y : IsoFlag W) :
    circleDeriv (circlePrim p) y = p y.1 - ∫ z, p z.1 ∂(circleMeasure y) := by
  have hP := y.2.1
  have hψd : HasFDerivAt (circlePrim p) (fderiv ℝ (circlePrim p) y.1) y.1 :=
    (((contDiff_circlePrim hp).differentiable one_ne_zero) y.1).hasFDerivAt
  have hR0 := (circleRot_spec hW hP 0 0).2.2.2.1
  have hy0 : (y.1.1, circleRot y.1.1 0 * y.1.2 * (circleRot y.1.1 0)ᴴ) = y.1 := by
    rw [hR0, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  have hγ : HasDerivAt (fun s => (y.1.1, circleRot y.1.1 s * y.1.2 * (circleRot y.1.1 s)ᴴ))
      (0, circleGen y.1.1 * y.1.2 - y.1.2 * circleGen y.1.1) 0 := by
    have h := circlePrimitive_hasDerivAt_conj hW hP y.1.2 0
    rw [hR0, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] at h
    exact (hasDerivAt_const 0 y.1.1).prodMk h
  have hψd' : HasFDerivAt (circlePrim p) (fderiv ℝ (circlePrim p) y.1)
      (y.1.1, circleRot y.1.1 0 * y.1.2 * (circleRot y.1.1 0)ᴴ) := by
    rw [hy0]; exact hψd
  have hcomp := hψd'.comp_hasDerivAt (0 : ℝ) hγ
  have hfc : Continuous (fun u => p (y.1.1, circleRot y.1.1 u * y.1.2 * (circleRot y.1.1 u)ᴴ)) :=
    hp.continuous.comp (continuous_const.prodMk (circlePrimitive_continuous_conj _ _))
  have hfper : Function.Periodic
      (fun u => p (y.1.1, circleRot y.1.1 u * y.1.2 * (circleRot y.1.1 u)ᴴ)) (2 * π) := fun u => by
    simp only [circlePrimitive_periodic hW y u]
  have hsaw := hasDerivAt_sawtooth hfc hfper 0
  have hfun : (circlePrim p ∘ fun s => (y.1.1, circleRot y.1.1 s * y.1.2 * (circleRot y.1.1 s)ᴴ)) =
      sawtooth (fun u => p (y.1.1, circleRot y.1.1 u * y.1.2 * (circleRot y.1.1 u)ᴴ)) :=
    funext fun s => circlePrim_conj hW hP y.1.2 s
  rw [hfun] at hcomp
  have huniq := hcomp.unique hsaw
  unfold circleDeriv
  rw [huniq, circlePrimitive_integral_circleMeasure hW hp.continuous y]
  simp only [hy0]

/-- If `p ≥ -ε` on the flags, then `|ψ_p| ≤ 2π (∫ p dm_U + ε)` on the circle of `U` (proof of
Lemma F.3 [lem:c-operators]). -/
theorem abs_circlePrim_le {W : ℕ} (hW : 1 ≤ W)
    {p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ}
    (hp : Continuous p) {ε : ℝ} (hpε : ∀ z : IsoFlag W, -ε ≤ p z.1) (y : IsoFlag W) :
    |circlePrim p y.1| ≤ 2 * π * (∫ z, p z.1 ∂(circleMeasure y) + ε) := by
  have hP := y.2.1
  have hR0 := (circleRot_spec hW hP 0 0).2.2.2.1
  have hy0 : (y.1.1, circleRot y.1.1 0 * y.1.2 * (circleRot y.1.1 0)ᴴ) = y.1 := by
    rw [hR0, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  have hfc : Continuous (fun u => p (y.1.1, circleRot y.1.1 u * y.1.2 * (circleRot y.1.1 u)ᴴ)) :=
    hp.comp (continuous_const.prodMk (circlePrimitive_continuous_conj _ _))
  have hfper : Function.Periodic
      (fun u => p (y.1.1, circleRot y.1.1 u * y.1.2 * (circleRot y.1.1 u)ᴴ)) (2 * π) := fun u => by
    simp only [circlePrimitive_periodic hW y u]
  have hfε : ∀ u, -ε ≤ p (y.1.1, circleRot y.1.1 u * y.1.2 * (circleRot y.1.1 u)ᴴ) := fun u => by
    rw [← circlePrimitive_flagAct hW y u]
    exact hpε _
  have h0 := circlePrim_conj (p := p) hW hP y.1.2 0
  rw [hy0] at h0
  rw [h0, circlePrimitive_integral_circleMeasure hW hp y]
  exact abs_sawtooth_le hfc hfper hfε 0

end LSBA
