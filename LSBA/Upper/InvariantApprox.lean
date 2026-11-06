import LSBA.Upper.FlagApprox
import LSBA.Upper.OperatorInvariance
import LSBA.Gauss.Haar
import LSBA.Transfer.CircleMeasure
import LSBA.Upper.CircleRotation

/-!
# Smooth invariant approximation of invariant functions of the flag

A bounded measurable function of the flag satisfying (8.25) [up:eq:invariant-function] is an
`L¹(ν)` limit of restrictions of `C¹` functions of the projection pair that are invariant under
`(P, P') ↦ (D P D*, D P' D*)`, `D = diag(Ṽ, Ṽ)`, for every unitary `Ṽ`: the approximants of the
flag approximation are averaged over the Haar measure of `U(W)` (used in the proof of
Lemma 8.11 [up:lem:angular]).
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `D = 1 ⊗ Ṽ = diag(Ṽ, Ṽ)` for a unitary `Ṽ`. -/
private def invApprox_D {W : ℕ} (V : Matrix.unitaryGroup (Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (V : Matrix (Fin W) (Fin W) ℂ)

/-- `c_Ṽ (P, P') = (D P D*, D P' D*)` with `D = diag(Ṽ, Ṽ)`. -/
private def invApprox_L {W : ℕ} (V : Matrix.unitaryGroup (Fin W) ℂ)
    (z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (invApprox_D V * z.1 * (invApprox_D V)ᴴ, invApprox_D V * z.2 * (invApprox_D V)ᴴ)

private theorem invApprox_L_apply {W : ℕ} (V : Matrix.unitaryGroup (Fin W) ℂ)
    (z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    invApprox_L V z = (invApprox_D V * z.1 * (invApprox_D V)ᴴ,
      invApprox_D V * z.2 * (invApprox_D V)ᴴ) := rfl

/-- `c_Ṽ` is `ℝ`-linear. -/
private theorem invApprox_L_isLinearMap {W : ℕ} (V : Matrix.unitaryGroup (Fin W) ℂ) :
    IsLinearMap ℝ (invApprox_L V) := by
  refine ⟨fun a b => ?_, fun r a => ?_⟩
  · simp only [invApprox_L_apply, Prod.fst_add, Prod.snd_add, Matrix.mul_add, Matrix.add_mul,
      Prod.mk_add_mk]
  · simp only [invApprox_L_apply, Prod.smul_fst, Prod.smul_snd, Matrix.mul_smul, Matrix.smul_mul,
      Prod.smul_mk]

private theorem invApprox_D_mul {W : ℕ} (V V' : Matrix.unitaryGroup (Fin W) ℂ) :
    invApprox_D (V * V') = invApprox_D V * invApprox_D V' := by
  unfold invApprox_D
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rfl

/-- `c_{Ṽ Ṽ'} = c_Ṽ ∘ c_Ṽ'`. -/
private theorem invApprox_L_mul {W : ℕ} (V V' : Matrix.unitaryGroup (Fin W) ℂ)
    (z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    invApprox_L (V * V') z = invApprox_L V (invApprox_L V' z) := by
  simp only [invApprox_L_apply, invApprox_D_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- `D* (A ⊗ I) D = A ⊗ I` for `D = 1 ⊗ Ṽ`. -/
private theorem invApprox_D_conj_kron {W : ℕ} (V : Matrix.unitaryGroup (Fin W) ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (invApprox_D V)ᴴ * (A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * invApprox_D V =
      A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
  have h2 := Matrix.mem_unitaryGroup_iff'.mp V.2
  rw [Matrix.star_eq_conjTranspose] at h2
  unfold invApprox_D
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, h2]

private theorem invApprox_D_mem {W : ℕ} (V : Matrix.unitaryGroup (Fin W) ℂ) :
    invApprox_D V ∈ Matrix.unitaryGroup (Fin 2 × Fin W) ℂ := by
  have h1 := Matrix.mem_unitaryGroup_iff.mp V.2
  rw [Matrix.star_eq_conjTranspose] at h1
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  unfold invApprox_D
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, h1, Matrix.one_kronecker_one]

/-- For `D = diag(Ṽ, Ṽ)` the image flag is `c_Ṽ (P_U, P_Y)`. -/
private theorem invApprox_flagAct {W : ℕ} (V : Matrix.unitaryGroup (Fin W) ℂ) (x : IsoFlag W) :
    ((flagAct (invApprox_D V) x : IsoFlag W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) = invApprox_L V x.1 := by
  have hJ : (invApprox_D V)ᴴ * isoJ W * invApprox_D V = isoJ W :=
    invApprox_D_conj_kron V !![1, 0; 0, -1]
  rw [flagAct_coe hJ, flagProj_of_mem_unitaryGroup (invApprox_D_mem V) x.2.1.2.1,
    flagProj_of_mem_unitaryGroup (invApprox_D_mem V) x.2.2.2.1, invApprox_L_apply]

private theorem invApprox_continuous_D {W : ℕ} : Continuous (invApprox_D (W := W)) := by
  refine continuous_matrix fun i j => ?_
  simp only [invApprox_D, Matrix.kroneckerMap_apply]
  exact continuous_const.mul (continuous_subtype_val.matrix_elem i.2 j.2)

private theorem invApprox_continuous_L {W : ℕ} :
    Continuous fun q : (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) × Matrix.unitaryGroup (Fin W) ℂ =>
      invApprox_L q.2 q.1 := by
  have hD := (invApprox_continuous_D (W := W)).comp (continuous_snd (X := (Matrix (Fin 2 × Fin W)
    (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)))
  simp only [invApprox_L_apply]
  exact ((hD.matrix_mul (continuous_fst.comp continuous_fst)).matrix_mul
    hD.matrix_conjTranspose).prodMk
    ((hD.matrix_mul (continuous_snd.comp continuous_fst)).matrix_mul hD.matrix_conjTranspose)

/-- For a finite measure `μ` on a compact space `G` and a jointly continuous family `c g` of
linear maps of a finite-dimensional space, the average `z ↦ ∫ f (c g z) dμ(g)` of a `C¹`
function `f` is `C¹`. -/
private theorem invApprox_contDiff_avg {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ] {c : G → E → E}
    (hlin : ∀ g, IsLinearMap ℝ (c g)) (hc : Continuous fun q : E × G => c q.2 q.1)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 fun z => ∫ g, f (c g z) ∂μ := by
  have hfc : Continuous f := hf.continuous
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  let L : G → E →L[ℝ] E := fun g =>
    LinearMap.toContinuousLinearMap (IsLinearMap.mk' (c g) (hlin g))
  have hcL : Continuous fun q : E × G => L q.2 q.1 := hc
  have hL : Continuous L := continuous_clm_apply.mpr fun y =>
    hcL.comp (continuous_const.prodMk continuous_id)
  let F' : E → G → (E →L[ℝ] ℝ) := fun z g => (fderiv ℝ f (L g z)).comp (L g)
  have hF'c : Continuous (Function.uncurry F') :=
    (hdf.comp hcL).clm_comp (hL.comp continuous_snd)
  have hFc : ∀ z, Continuous fun g : G => f (c g z) :=
    fun z => hfc.comp (hc.comp (continuous_const.prodMk continuous_id))
  have hder : ∀ z₀, HasFDerivAt (fun z => ∫ g, f (c g z) ∂μ) (∫ g, F' z₀ g ∂μ) z₀ := by
    intro z₀
    obtain ⟨C, hC⟩ := ((isCompact_closedBall z₀ 1).prod
      (isCompact_univ (X := G))).exists_bound_of_continuousOn hF'c.continuousOn
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
      (Metric.ball_mem_nhds z₀ one_pos) ?_ ?_ ?_ ?_ (integrable_const C) ?_
    · exact Filter.Eventually.of_forall fun z => (hFc z).aestronglyMeasurable
    · obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (hFc z₀).continuousOn
      exact Integrable.of_bound (hFc z₀).aestronglyMeasurable B
        (Filter.Eventually.of_forall fun g => hB g (Set.mem_univ g))
    · exact (hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun g z hz =>
        hC (z, g) ⟨Metric.ball_subset_closedBall hz, Set.mem_univ g⟩
    · exact Filter.Eventually.of_forall fun g z _ =>
        (hfd (L g z)).hasFDerivAt.comp z (L g).hasFDerivAt
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun z => (hder z).differentiableAt, ?_⟩
  have e : fderiv ℝ (fun z => ∫ g, f (c g z) ∂μ) = fun z => ∫ g, F' z g ∂μ :=
    funext fun z => (hder z).fderiv
  rw [e]
  have := continuous_parametric_integral_of_continuous (μ := μ) hF'c (isCompact_univ (X := G))
  simpa only [Measure.restrict_univ] using this

/-- For bounded measurable `β` satisfying (8.25) [up:eq:invariant-function] and every finite
measure `ν` on the flags, there are `C¹` functions `p n` of the projection pair, invariant under
simultaneous conjugation by `diag(Ṽ, Ṽ)` for every unitary `Ṽ`, with `∫ |p n - β| dν → 0`. -/
theorem exists_invariant_contDiff_flagApprox {W : ℕ} (ν : Measure (IsoFlag W))
    [IsFiniteMeasure ν] {β : IsoFlag W → ℝ} (hβ : IsBddMeas β) (hinv : IsSimulInvariant β) :
    ∃ p : ℕ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ,
      (∀ n, ContDiff ℝ 1 (p n)) ∧
      (∀ n, ∀ V ∈ Matrix.unitaryGroup (Fin W) ℂ,
        ∀ z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
          p n (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) * z.1 * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)ᴴ,
            ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) * z.2 * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)ᴴ) =
            p n z) ∧
      Tendsto (fun n => ∫ x, |p n x.1 - β x| ∂ν) atTop (𝓝 0) := by
  have : CompactSpace (IsoFlag W) := isCompact_iff_compactSpace.mp (isCompact_isoFlags W)
  have hDm : Measurable (invApprox_D (W := W)) := by
    refine Measurable.of_eval_matrix _ fun i j => ?_
    exact (invApprox_continuous_D.matrix_elem i j).measurable
  have h2 : Measurable fun q : Matrix.unitaryGroup (Fin W) ℂ × IsoFlag W =>
      (invApprox_D q.1, q.2) := (hDm.comp measurable_fst).prodMk measurable_snd
  set Φ := (fun p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × IsoFlag W => flagAct p.1 p.2) ∘
    fun q : Matrix.unitaryGroup (Fin W) ℂ × IsoFlag W => (invApprox_D q.1, q.2) with hΦdef
  have hΦ : Measurable Φ := (measurable_flagAct W).comp h2
  set ν' : Measure (IsoFlag W) := ((haarU W).prod ν).map Φ with hν'
  obtain ⟨p, hpC, hpT⟩ := exists_contDiff_flagApprox ν' hβ
  obtain ⟨hβm, M, hM⟩ := hβ
  refine ⟨fun n z => ∫ V, p n (invApprox_L V z) ∂haarU W, fun n =>
    invApprox_contDiff_avg (haarU W) invApprox_L_isLinearMap invApprox_continuous_L (hpC n),
    ?_, ?_⟩
  · intro n V hV z
    have := isMulRightInvariant_haarU W
    change ∫ V', p n (invApprox_L V' (invApprox_L ⟨V, hV⟩ z)) ∂haarU W =
      ∫ V', p n (invApprox_L V' z) ∂haarU W
    simp_rw [← invApprox_L_mul]
    exact integral_mul_right_eq_self (fun V' => p n (invApprox_L V' z)) ⟨V, hV⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpT
      (fun n => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_)
    have hpc : Continuous (p n) := (hpC n).continuous
    set G : Matrix.unitaryGroup (Fin W) ℂ × IsoFlag W → ℝ :=
      fun q => |p n (invApprox_L q.1 q.2.1) - β q.2| with hG
    have hc1 : Continuous fun q : Matrix.unitaryGroup (Fin W) ℂ × IsoFlag W =>
        invApprox_L q.1 q.2.1 :=
      invApprox_continuous_L.comp (f := fun q : Matrix.unitaryGroup (Fin W) ℂ × IsoFlag W =>
        ((q.2 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
          Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), q.1))
        ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
    have hGc : Continuous fun q : Matrix.unitaryGroup (Fin W) ℂ × IsoFlag W =>
        p n (invApprox_L q.1 q.2.1) := hpc.comp hc1
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hGc.continuousOn
    have : OpensMeasurableSpace (Matrix.unitaryGroup (Fin W) ℂ × IsoFlag W) :=
      Prod.opensMeasurableSpace
    have hGm : Measurable G := (hGc.measurable.sub (hβm.comp measurable_snd)).abs
    have hGb : ∀ q, ‖G q‖ ≤ B + M := fun q => by
      rw [Real.norm_eq_abs, abs_abs]
      have h1 := hB q (Set.mem_univ q)
      rw [Real.norm_eq_abs] at h1
      exact (abs_sub _ _).trans (add_le_add h1 (hM q.2))
    have hGint : Integrable G ((haarU W).prod ν) :=
      Integrable.of_bound hGm.aestronglyMeasurable (B + M) (Filter.Eventually.of_forall hGb)
    have hFm : Measurable fun y : IsoFlag W => |p n y.1 - β y| :=
      ((hpc.comp continuous_subtype_val).measurable.sub hβm).abs
    have hR : ∫ y, |p n y.1 - β y| ∂ν' = ∫ q, G q ∂((haarU W).prod ν) := by
      rw [hν', integral_map hΦ.aemeasurable hFm.aestronglyMeasurable]
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      have e1 : (Φ q).1 = invApprox_L q.1 q.2.1 := invApprox_flagAct q.1 q.2
      have e2 : β (Φ q) = β q.2 := hinv _ q.1.2 q.2
      simp only [hG, e1, e2]
    rw [hR, integral_prod_symm G hGint]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      hGint.integral_prod_right (Filter.Eventually.of_forall fun x => ?_)
    have hi : Integrable (fun V => p n (invApprox_L V x.1)) (haarU W) :=
      Integrable.of_bound (hGc.comp (Continuous.prodMk_left x)).aestronglyMeasurable B
        (Filter.Eventually.of_forall fun V => hB (V, x) (Set.mem_univ _))
    have e : ∫ V, p n (invApprox_L V x.1) ∂haarU W - β x =
        ∫ V, (p n (invApprox_L V x.1) - β x) ∂haarU W := by
      rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul]
    simp only [hG]
    rw [e, ← Real.norm_eq_abs]
    exact (norm_integral_le_integral_norm _).trans_eq rfl

end LSBA
