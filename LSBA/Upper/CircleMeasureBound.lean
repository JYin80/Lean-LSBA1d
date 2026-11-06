import LSBA.Upper.CirclePrimitive
import LSBA.Upper.FlagApprox

/-!
# Measures on the flags with a vertical bound

Lemma F.3 [lem:c-operators] at the level of sets, in the lift form: if a measure `ν` of mass at
most one on the isotropic flags satisfies `|∫ ∂_θ ψ dν| ≤ A₀ sup |ψ|` for every `C¹` function
`ψ` of the projection pair (the form of (F.8) [cc:eq:vertical]), then
`ν(A) ≤ (1 + 2π A₀) sup_U m_U(A)` for every Borel set `A` of flags. The bound is applied to the
primitives along the circles of smooth uniform approximants of a continuous function, then
extended to closed sets by monotone limits and compactness of the flags, and to Borel sets by
regularity, in place of the disintegration and the densities `k_V` of the proof of Lemma F.3
[lem:c-operators].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Helpers for the uniform approximation -/

/-- The real part of an entry is a `C^∞` function of the matrix. -/
private theorem circleMeasureBound_contDiff_entry_re {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) : ContDiff ℝ (⊤ : ℕ∞) fun P : Matrix ι ι ℂ => (P i j).re := by
  let L : Matrix ι ι ℂ →ₗ[ℝ] ℝ := Complex.reLm ∘ₗ (Matrix.entryLinearMap ℝ ℂ i j)
  exact (LinearMap.toContinuousLinearMap L).contDiff

/-- The imaginary part of an entry is a `C^∞` function of the matrix. -/
private theorem circleMeasureBound_contDiff_entry_im {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) : ContDiff ℝ (⊤ : ℕ∞) fun P : Matrix ι ι ℂ => (P i j).im := by
  let L : Matrix ι ι ℂ →ₗ[ℝ] ℝ := Complex.imLm ∘ₗ (Matrix.entryLinearMap ℝ ℂ i j)
  exact (LinearMap.toContinuousLinearMap L).contDiff

/-- The continuous functions on the flags that are restrictions of `C^∞` functions of the
projection pair. -/
private def circleMeasureBound_alg (W : ℕ) : Subalgebra ℝ C(IsoFlag W, ℝ) where
  carrier := {f | ∃ p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧
      ∀ x : IsoFlag W, f x = p x.1}
  mul_mem' := by
    rintro f g ⟨p, hp, hf⟩ ⟨q, hq, hg⟩
    exact ⟨fun z => p z * q z, hp.mul hq, fun x => by simp [hf x, hg x]⟩
  add_mem' := by
    rintro f g ⟨p, hp, hf⟩ ⟨q, hq, hg⟩
    exact ⟨fun z => p z + q z, hp.add hq, fun x => by simp [hf x, hg x]⟩
  one_mem' := ⟨fun _ => 1, contDiff_const, fun x => by simp⟩
  zero_mem' := ⟨fun _ => 0, contDiff_const, fun x => by simp⟩
  algebraMap_mem' c := ⟨fun _ => c, contDiff_const, fun x => by simp⟩

/-- The restrictions of `C^∞` functions of the projection pair separate the flags: the real and
imaginary parts of the entries of `(P_U, P_Y)` are such functions. -/
private theorem circleMeasureBound_separates (W : ℕ) :
    (circleMeasureBound_alg W).SeparatesPoints := by
  intro x y hxy
  have hxy' : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  have key : ∃ q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) q ∧ q x.1 ≠ q y.1 := by
    by_contra hcon0
    have hcon : ∀ q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) q → q x.1 = q y.1 :=
      fun q hq => by_contra fun h => hcon0 ⟨q, hq, h⟩
    apply hxy'
    have hc : ∀ i j : Fin 2 × Fin W, x.1.1 i j = y.1.1 i j ∧ x.1.2 i j = y.1.2 i j := by
      intro i j
      have a1 := hcon (fun z => (z.1 i j).re)
        ((circleMeasureBound_contDiff_entry_re i j).comp contDiff_fst)
      have a2 := hcon (fun z => (z.1 i j).im)
        ((circleMeasureBound_contDiff_entry_im i j).comp contDiff_fst)
      have a3 := hcon (fun z => (z.2 i j).re)
        ((circleMeasureBound_contDiff_entry_re i j).comp contDiff_snd)
      have a4 := hcon (fun z => (z.2 i j).im)
        ((circleMeasureBound_contDiff_entry_im i j).comp contDiff_snd)
      exact ⟨Complex.ext a1 a2, Complex.ext a3 a4⟩
    exact Prod.ext (by ext i j; exact (hc i j).1) (by ext i j; exact (hc i j).2)
  obtain ⟨q, hq, hne⟩ := key
  exact ⟨_, ⟨⟨fun z => q z.1, hq.continuous.comp continuous_subtype_val⟩, ⟨q, hq, fun _ => rfl⟩,
    rfl⟩, hne⟩

/-- Every continuous function of the flag is uniformly within `ε` of the restriction of a `C^∞`
function of the projection pair (Stone–Weierstrass on the compact set of flags). -/
theorem exists_contDiff_near_flag {W : ℕ} {φ : IsoFlag W → ℝ} (hφ : Continuous φ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) p ∧ ∀ y : IsoFlag W, |p y.1 - φ y| ≤ ε := by
  have : CompactSpace (IsoFlag W) := isCompact_iff_compactSpace.mp (isCompact_isoFlags W)
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (circleMeasureBound_alg W) (circleMeasureBound_separates W) ⟨φ, hφ⟩ ε hε
  obtain ⟨p, hp, hgp⟩ := g.2
  refine ⟨p, hp, fun y => ?_⟩
  have h1 := ContinuousMap.norm_coe_le_norm ((g : C(IsoFlag W, ℝ)) - ⟨φ, hφ⟩) y
  rw [← hgp y]
  have h2 : ‖((g : C(IsoFlag W, ℝ)) - ⟨φ, hφ⟩) y‖ = |(g : C(IsoFlag W, ℝ)) y - φ y| := by
    rw [Real.norm_eq_abs]
    rfl
  rw [← h2]
  exact h1.trans hg.le

/-! ### Helpers for the bound on sets -/

/-- `(P, t) ↦ R_t` is continuous. -/
private theorem circleMeasureBound_continuous_rot {W : ℕ} :
    Continuous (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ => circleRot q.1 q.2) := by
  unfold circleRot quotProj
  fun_prop

/-- For a flag `y`, `R_t y` is the flag `(P_U, R_t P_Y R_t*)`. -/
private theorem circleMeasureBound_flagAct {W : ℕ} (hW : 1 ≤ W) (y : IsoFlag W) (t : ℝ) :
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

/-- `(y, t) ↦ R_t y` is continuous on the flags. -/
private theorem circleMeasureBound_continuous_act {W : ℕ} (hW : 1 ≤ W) :
    Continuous (fun q : IsoFlag W × ℝ => flagAct (circleRot q.1.1.1 q.2) q.1) := by
  refine continuous_induced_rng.2 ?_
  have h : (Subtype.val ∘ fun q : IsoFlag W × ℝ => flagAct (circleRot q.1.1.1 q.2) q.1) =
      fun q => (q.1.1.1, circleRot q.1.1.1 q.2 * q.1.1.2 * (circleRot q.1.1.1 q.2)ᴴ) :=
    funext fun q => circleMeasureBound_flagAct hW q.1 q.2
  rw [h]
  have hU : Continuous (fun q : IsoFlag W × ℝ => q.1.1.1) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
  have hY : Continuous (fun q : IsoFlag W × ℝ => q.1.1.2) :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_fst)
  have hR : Continuous (fun q : IsoFlag W × ℝ => circleRot q.1.1.1 q.2) :=
    Continuous.comp (g := fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ =>
      circleRot q.1 q.2) (f := fun q : IsoFlag W × ℝ => (q.1.1.1, q.2))
      circleMeasureBound_continuous_rot (hU.prodMk continuous_snd)
  exact hU.prodMk ((hR.matrix_mul hY).matrix_mul hR.matrix_conjTranspose)

/-- `∫ f dm_y = (2π)⁻¹ ∫_0^{2π} f(R_t y) dt` for continuous `f` on the flags. -/
private theorem circleMeasureBound_integral_eq {W : ℕ} (hW : 1 ≤ W) {f : IsoFlag W → ℝ}
    (hf : Continuous f) (y : IsoFlag W) :
    ∫ z, f z ∂(circleMeasure y) =
      (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), f (flagAct (circleRot y.1.1 t) y) := by
  have hφc : Continuous (fun t => flagAct (circleRot y.1.1 t) y) :=
    Continuous.comp (g := fun q : IsoFlag W × ℝ => flagAct (circleRot q.1.1.1 q.2) q.1)
      (f := fun t : ℝ => (y, t)) (circleMeasureBound_continuous_act hW)
      (continuous_const.prodMk continuous_id)
  rw [circleMeasure_eq_map_circleRot hW y,
    integral_map hφc.measurable.aemeasurable hf.aestronglyMeasurable]
  unfold angleMeas
  rw [integral_smul_measure, ← intervalIntegral.integral_of_le (by positivity),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- `y ↦ ∫ f dm_y` is continuous for continuous `f` on the flags. -/
private theorem circleMeasureBound_continuous_integral {W : ℕ} (hW : 1 ≤ W)
    {f : IsoFlag W → ℝ} (hf : Continuous f) :
    Continuous (fun y : IsoFlag W => ∫ z, f z ∂(circleMeasure y)) := by
  have e : (fun y : IsoFlag W => ∫ z, f z ∂(circleMeasure y)) = fun y =>
      (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), f (flagAct (circleRot y.1.1 t) y) :=
    funext (circleMeasureBound_integral_eq hW hf)
  rw [e]
  set G : IsoFlag W → ℝ → ℝ := fun y t => f (flagAct (circleRot y.1.1 t) y) with hGdef
  have hF : Continuous (Function.uncurry G) := by
    have h := Continuous.comp' hf (circleMeasureBound_continuous_act hW)
    exact h
  have hI : Continuous (fun y : IsoFlag W => ∫ t in (0 : ℝ)..(2 * π), G y t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 (2 * π)
  exact continuous_const.mul hI

/-- Continuous functions on the flags are integrable for every finite measure. -/
private theorem circleMeasureBound_integrable {W : ℕ} {μ : Measure (IsoFlag W)}
    [IsFiniteMeasure μ] {f : IsoFlag W → ℝ} (hf : Continuous f) : Integrable f μ := by
  have : CompactSpace (IsoFlag W) := isCompact_iff_compactSpace.mp (isCompact_isoFlags W)
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The bound for continuous `φ ≥ 0`: if `∫ φ dm_y ≤ M` for every flag `y`, then
`∫ φ dν ≤ (1 + 2π A₀) M`. -/
private theorem circleMeasureBound_continuous_case {W : ℕ} (hW : 1 ≤ W)
    {ν : Measure (IsoFlag W)} [IsFiniteMeasure ν] (hν : ν Set.univ ≤ 1) {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hvert : ∀ ψ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ, ContDiff ℝ 1 ψ →
      ∀ S : ℝ, (∀ y : IsoFlag W, |ψ y.1| ≤ S) → |∫ y, circleDeriv ψ y ∂ν| ≤ A₀ * S)
    {φ : IsoFlag W → ℝ} (hφ : Continuous φ) (hφ0 : ∀ y, 0 ≤ φ y) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, ∫ z, φ z ∂(circleMeasure y) ≤ M) :
    ∫ y, φ y ∂ν ≤ (1 + 2 * π * A₀) * M := by
  have hν1 : ν.real Set.univ ≤ 1 := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hν)
  have hνnn : 0 ≤ ν.real Set.univ := measureReal_nonneg
  have hK : 0 < 2 + 4 * π * A₀ := by positivity
  refine le_of_forall_pos_le_add fun η hη => ?_
  set ε := η / (2 + 4 * π * A₀) with hεdef
  have hε : 0 < ε := div_pos hη hK
  obtain ⟨p, hp, hpφ⟩ := exists_contDiff_near_flag hφ hε
  have hp1 : ContDiff ℝ 1 p := hp.of_le (by exact_mod_cast le_top)
  have hpc : Continuous p := hp1.continuous
  have hpvc : Continuous (fun y : IsoFlag W => p y.1) := hpc.comp continuous_subtype_val
  set g : IsoFlag W → ℝ := fun y => ∫ z, p z.1 ∂(circleMeasure y) with hgdef
  have hgc : Continuous g := circleMeasureBound_continuous_integral hW hpvc
  have hderiv : ∀ y, circleDeriv (circlePrim p) y = p y.1 - g y := circleDeriv_circlePrim hW hp1
  have hpε : ∀ y : IsoFlag W, -ε ≤ p y.1 := fun y => by
    have := (abs_le.1 (hpφ y)).1
    linarith [hφ0 y]
  have hg : ∀ y, g y ≤ M + ε := fun y => by
    have := isProbabilityMeasure_circleMeasure y
    calc g y ≤ ∫ z, (φ z + ε) ∂(circleMeasure y) :=
          integral_mono (circleMeasureBound_integrable hpvc)
            (circleMeasureBound_integrable (hφ.add continuous_const))
            (fun z => by have := (abs_le.1 (hpφ z)).2; linarith)
      _ = ∫ z, φ z ∂(circleMeasure y) + ε := by
          rw [integral_add (circleMeasureBound_integrable hφ) (integrable_const _),
            integral_const]
          simp
      _ ≤ M + ε := by linarith [hM y]
  have hS : ∀ y : IsoFlag W, |circlePrim p y.1| ≤ 2 * π * (M + 2 * ε) := fun y => by
    calc _ ≤ 2 * π * (g y + ε) := abs_circlePrim_le hW hpc hpε y
      _ ≤ _ := by
          have := hg y
          have : g y + ε ≤ M + 2 * ε := by linarith
          gcongr
  have hv := hvert (circlePrim p) (contDiff_circlePrim hp1) _ hS
  have hdc : Continuous (circleDeriv (circlePrim p)) := by
    have : circleDeriv (circlePrim p) = fun y => p y.1 - g y := funext hderiv
    rw [this]
    exact hpvc.sub hgc
  have hsplit : ∫ y, p y.1 ∂ν = ∫ y, g y ∂ν + ∫ y, circleDeriv (circlePrim p) y ∂ν := by
    rw [← integral_add (circleMeasureBound_integrable hgc) (circleMeasureBound_integrable hdc)]
    congr 1
    funext y
    rw [hderiv]
    ring
  have hgν : ∫ y, g y ∂ν ≤ M + ε := by
    calc ∫ y, g y ∂ν ≤ ∫ _y, (M + ε) ∂ν :=
          integral_mono (circleMeasureBound_integrable hgc) (integrable_const _) hg
      _ = ν.real Set.univ * (M + ε) := by rw [integral_const, smul_eq_mul]
      _ ≤ 1 * (M + ε) := by gcongr
      _ = M + ε := one_mul _
  have hφν : ∫ y, φ y ∂ν ≤ ∫ y, p y.1 ∂ν + ε := by
    calc ∫ y, φ y ∂ν ≤ ∫ y, (p y.1 + ε) ∂ν :=
          integral_mono (circleMeasureBound_integrable hφ)
            (circleMeasureBound_integrable (hpvc.add continuous_const))
            (fun y => by have := (abs_le.1 (hpφ y)).1; linarith)
      _ = ∫ y, p y.1 ∂ν + ν.real Set.univ * ε := by
          rw [integral_add (circleMeasureBound_integrable hpvc) (integrable_const _),
            integral_const, smul_eq_mul]
      _ ≤ ∫ y, p y.1 ∂ν + ε := by nlinarith
  have hdν : ∫ y, circleDeriv (circlePrim p) y ∂ν ≤ A₀ * (2 * π * (M + 2 * ε)) :=
    (le_abs_self _).trans hv
  have hη' : η = ε * (2 + 4 * π * A₀) := by
    rw [hεdef]
    field_simp
  calc ∫ y, φ y ∂ν ≤ (M + ε) + A₀ * (2 * π * (M + 2 * ε)) + ε := by linarith
    _ = (1 + 2 * π * A₀) * M + ε * (2 + 4 * π * A₀) := by ring
    _ = (1 + 2 * π * A₀) * M + η := by rw [hη']

/-- The bound for closed sets `F`: `ν(F) ≤ (1 + 2π A₀) sup_y m_y(F)`. -/
private theorem circleMeasureBound_closed {W : ℕ} (hW : 1 ≤ W)
    {ν : Measure (IsoFlag W)} [IsFiniteMeasure ν] (hν : ν Set.univ ≤ 1) {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hvert : ∀ ψ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ, ContDiff ℝ 1 ψ →
      ∀ S : ℝ, (∀ y : IsoFlag W, |ψ y.1| ≤ S) → |∫ y, circleDeriv ψ y ∂ν| ≤ A₀ * S)
    {F : Set (IsoFlag W)} (hF : IsClosed F) :
    ν F ≤ ENNReal.ofReal (1 + 2 * π * A₀) * ⨆ y, circleMeasure y F := by
  have : CompactSpace (IsoFlag W) := isCompact_iff_compactSpace.mp (isCompact_isoFlags W)
  set M : ℝ≥0∞ := ⨆ y, circleMeasure y F with hMdef
  have hM1 : M ≤ 1 := iSup_le fun y => by
    have := isProbabilityMeasure_circleMeasure y
    exact prob_le_one
  have hMt : M ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hM1
  have hyM : ∀ y, (circleMeasure y F).toReal ≤ M.toReal := fun y =>
    ENNReal.toReal_mono hMt (le_iSup (fun y => circleMeasure y F) y)
  have hc : 0 < 1 + 2 * π * A₀ := by positivity
  have hδk : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  set φ : ℕ → IsoFlag W → ℝ := fun k y => (thickenedIndicator (hδk k) F y : ℝ) with hφdef
  have hφc : ∀ k, Continuous (φ k) := fun k =>
    NNReal.continuous_coe.comp (thickenedIndicator (hδk k) F).continuous
  have hφ0 : ∀ k y, 0 ≤ φ k y := fun k y => NNReal.coe_nonneg _
  have hφ1 : ∀ k y, φ k y ≤ 1 := fun k y => by
    simp only [hφdef]
    exact_mod_cast thickenedIndicator_le_one (hδk k) F y
  have hφanti : ∀ k y, φ (k + 1) y ≤ φ k y := fun k y => by
    simp only [hφdef]
    have hle : 1 / (((k + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      gcongr
      linarith
    exact_mod_cast thickenedIndicator_mono (hδk (k + 1)) (hδk k) hle F y
  have hind : ∀ k y, F.indicator (fun _ => (1 : ℝ)) y ≤ φ k y := fun k y => by
    have h := indicator_le_thickenedIndicator (hδk k) F y
    by_cases hy : y ∈ F
    · rw [Set.indicator_of_mem hy] at h ⊢
      have h' : ((1 : ℝ≥0) : ℝ) ≤ (thickenedIndicator (hδk k) F y : ℝ) := NNReal.coe_le_coe.2 h
      simpa [hφdef] using h'
    · rw [Set.indicator_of_notMem hy]
      exact hφ0 k y
  set g : ℕ → IsoFlag W → ℝ := fun k y => ∫ z, φ k z ∂(circleMeasure y) with hgdef
  have hgc : ∀ k, Continuous (g k) := fun k => circleMeasureBound_continuous_integral hW (hφc k)
  have hganti : ∀ k y, g (k + 1) y ≤ g k y := fun k y => by
    have := isProbabilityMeasure_circleMeasure y
    exact integral_mono (circleMeasureBound_integrable (hφc _))
      (circleMeasureBound_integrable (hφc _)) (hφanti k)
  have hlim : ∀ y, Filter.Tendsto (fun k => g k y) Filter.atTop
      (nhds (circleMeasure y F).toReal) := fun y => by
    have := isProbabilityMeasure_circleMeasure y
    have hpt := thickenedIndicator_tendsto_indicator_closure hδk
      tendsto_one_div_add_atTop_nhds_zero_nat F
    rw [tendsto_pi_nhds] at hpt
    have hconv : ∀ z, Filter.Tendsto (fun k => φ k z) Filter.atTop
        (nhds (F.indicator (fun _ => (1 : ℝ)) z)) := fun z => by
      have h : Filter.Tendsto (fun k => φ k z) Filter.atTop
          (nhds (((closure F).indicator (fun _ => (1 : ℝ≥0)) z : ℝ≥0) : ℝ)) :=
        NNReal.tendsto_coe.2 (hpt z)
      convert h using 2
      rw [hF.closure_eq]
      by_cases hz : z ∈ F <;> simp [hz]
    have h := tendsto_integral_of_dominated_convergence (μ := circleMeasure y) (fun _ => (1 : ℝ))
      (fun k => (hφc k).aestronglyMeasurable) (integrable_const _)
      (fun k => Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 k z)]
        exact hφ1 k z)
      (Filter.Eventually.of_forall hconv)
    have hi : ∫ z, F.indicator (fun _ => (1 : ℝ)) z ∂(circleMeasure y) =
        (circleMeasure y F).toReal := by
      rw [integral_indicator hF.measurableSet, setIntegral_const, smul_eq_mul, mul_one,
        measureReal_def]
    rw [hi] at h
    exact h
  have key : ν.real F ≤ (1 + 2 * π * A₀) * M.toReal := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    set δ := η / (1 + 2 * π * A₀) with hδdef
    have hδ : 0 < δ := div_pos hη hc
    set L := M.toReal + δ with hLdef
    obtain ⟨k, hk⟩ : ∃ k, ∀ y, g k y ≤ L := by
      by_contra hcon
      push Not at hcon
      set t : ℕ → Set (IsoFlag W) := fun k => {y | L ≤ g k y} with htdef
      have htcl : ∀ k, IsClosed (t k) := fun k => isClosed_le continuous_const (hgc k)
      obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t
        (fun k y hy => le_trans hy (hganti k y)) (fun k => (hcon k).imp fun y hy => hy.le)
        (htcl 0).isCompact htcl
      rw [Set.mem_iInter] at hy
      have hge := ge_of_tendsto (hlim y) (Filter.Eventually.of_forall hy)
      linarith [hyM y]
    have h1 := circleMeasureBound_continuous_case hW hν hA₀ hvert (hφc k) (hφ0 k)
      (by positivity) hk
    have h2 : ν.real F ≤ ∫ y, φ k y ∂ν := by
      rw [← integral_indicator_one hF.measurableSet]
      exact integral_mono ((integrable_const _).indicator hF.measurableSet)
        (circleMeasureBound_integrable (hφc k)) (hind k)
    calc ν.real F ≤ (1 + 2 * π * A₀) * L := h2.trans h1
      _ = (1 + 2 * π * A₀) * M.toReal + η := by
          rw [hLdef, hδdef, mul_add, mul_div_cancel₀ _ hc.ne']
  calc ν F = ENNReal.ofReal (ν.real F) := (ofReal_measureReal (measure_ne_top ν F)).symm
    _ ≤ ENNReal.ofReal ((1 + 2 * π * A₀) * M.toReal) := ENNReal.ofReal_le_ofReal key
    _ = ENNReal.ofReal (1 + 2 * π * A₀) * M := by
        rw [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_toReal hMt]

/-- Lemma F.3 [lem:c-operators] for sets, lift form: a measure `ν` on the flags with
`ν(univ) ≤ 1` and `|∫ ∂_θ ψ dν| ≤ A₀ S` whenever `|ψ| ≤ S` on the flags satisfies
`ν(A) ≤ (1 + 2π A₀) sup_U m_U(A)` for Borel `A`. -/
theorem measure_le_of_circleDeriv_le {W : ℕ} (hW : 1 ≤ W) {ν : Measure (IsoFlag W)}
    [IsFiniteMeasure ν] (hν : ν Set.univ ≤ 1) {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hvert : ∀ ψ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ, ContDiff ℝ 1 ψ →
      ∀ S : ℝ, (∀ y : IsoFlag W, |ψ y.1| ≤ S) → |∫ y, circleDeriv ψ y ∂ν| ≤ A₀ * S)
    {A : Set (IsoFlag W)} (hA : MeasurableSet A) :
    ν A ≤ ENNReal.ofReal (1 + 2 * π * A₀) * ⨆ y, circleMeasure y A := by
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  obtain ⟨F, hFA, hFc, hlt⟩ :=
    hA.exists_isClosed_lt_add (measure_ne_top ν A) (ENNReal.coe_ne_zero.2 hδ.ne')
  calc ν A ≤ ν F + δ := hlt.le
    _ ≤ ENNReal.ofReal (1 + 2 * π * A₀) * (⨆ y, circleMeasure y F) + δ := by
        gcongr
        exact circleMeasureBound_closed hW hν hA₀ hvert hFc
    _ ≤ ENNReal.ofReal (1 + 2 * π * A₀) * (⨆ y, circleMeasure y A) + δ := by
        gcongr

end LSBA
