import LSBA.Upper.Operator

/-!
# Smooth approximation of functions of the flag

The isotropic flags form a compact set of projection pairs, and every bounded measurable
function of the flag is an `L¹(ν)` limit of restrictions of `C¹` functions of the projection
pair, for every finite measure `ν` (used in the proof of Lemma 8.11 [up:lem:angular]).
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The isotropic flags of Definition 8.5 [up:def:transfer-operator] form a compact set of
projection pairs. -/
theorem isCompact_isoFlags (W : ℕ) : IsCompact (isoFlags W) := by
  have hcl : IsClosed (isoFlags W) := by
    have e : isoFlags W =
        {x | x.1ᴴ = x.1} ∩ ({x | x.1 * x.1 = x.1} ∩ ({x | x.1.trace = ((W - 1 : ℕ) : ℂ)} ∩
          ({x | x.1 * isoJ W * x.1 = 0} ∩ ({x | x.2ᴴ = x.2} ∩ ({x | x.2 * x.2 = x.2} ∩
          ({x | x.2.trace = (W : ℂ)} ∩ ({x | x.2 * x.1 = x.1} ∩
          {x | x.2 * isoJ W * x.2 = 0}))))))) := by
      ext x
      simp only [isoFlags, isoBases, Matrix.IsHermitian, Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [e]
    have c1 : Continuous fun z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => z.1 := continuous_fst
    have c2 : Continuous fun z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => z.2 := continuous_snd
    have cJ : ∀ c : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
        Continuous c → Continuous fun z => c z * isoJ W * c z := fun c hc =>
      (hc.matrix_mul continuous_const).matrix_mul hc
    refine (isClosed_eq c1.matrix_conjTranspose c1).inter <|
      (isClosed_eq (c1.matrix_mul c1) c1).inter <|
      (isClosed_eq c1.matrix_trace continuous_const).inter <|
      (isClosed_eq (cJ _ c1) continuous_const).inter <|
      (isClosed_eq c2.matrix_conjTranspose c2).inter <|
      (isClosed_eq (c2.matrix_mul c2) c2).inter <|
      (isClosed_eq c2.matrix_trace continuous_const).inter <|
      (isClosed_eq (c2.matrix_mul c1) c1).inter (isClosed_eq (cJ _ c2) continuous_const)
  have hnorm : ∀ P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, P.IsHermitian → P * P = P →
      ‖P‖ ≤ 1 := fun P hP hPP =>
    IsStarProjection.norm_le P ⟨hPP, Matrix.isHermitian_iff_isSelfAdjoint.mp hP⟩
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  refine (Metric.isBounded_closedBall (x := (0 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) (r := 1)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  exact max_le (hnorm _ hx.1.1 hx.1.2.1) (hnorm _ hx.2.1 hx.2.2.1)

/-- The real part of an entry is a `C¹` function of the matrix. -/
private theorem flagApprox_contDiff_entry_re {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    ContDiff ℝ 1 fun P : Matrix ι ι ℂ => (P i j).re := by
  let L : Matrix ι ι ℂ →ₗ[ℝ] ℝ := Complex.reLm ∘ₗ (Matrix.entryLinearMap ℝ ℂ i j)
  exact (LinearMap.toContinuousLinearMap L).contDiff

/-- The imaginary part of an entry is a `C¹` function of the matrix. -/
private theorem flagApprox_contDiff_entry_im {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    ContDiff ℝ 1 fun P : Matrix ι ι ℂ => (P i j).im := by
  let L : Matrix ι ι ℂ →ₗ[ℝ] ℝ := Complex.imLm ∘ₗ (Matrix.entryLinearMap ℝ ℂ i j)
  exact (LinearMap.toContinuousLinearMap L).contDiff

/-- The continuous functions on the flags that are restrictions of `C¹` functions of the
projection pair. -/
private def flagApprox_alg (W : ℕ) : Subalgebra ℝ C(IsoFlag W, ℝ) where
  carrier := {f | ∃ p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ, ContDiff ℝ 1 p ∧ ∀ x : IsoFlag W, f x = p x.1}
  mul_mem' := by
    rintro f g ⟨p, hp, hf⟩ ⟨q, hq, hg⟩
    exact ⟨fun z => p z * q z, hp.mul hq, fun x => by simp [hf x, hg x]⟩
  add_mem' := by
    rintro f g ⟨p, hp, hf⟩ ⟨q, hq, hg⟩
    exact ⟨fun z => p z + q z, hp.add hq, fun x => by simp [hf x, hg x]⟩
  one_mem' := ⟨fun _ => 1, contDiff_const, fun x => by simp⟩
  zero_mem' := ⟨fun _ => 0, contDiff_const, fun x => by simp⟩
  algebraMap_mem' c := ⟨fun _ => c, contDiff_const, fun x => by simp⟩

/-- The restrictions of `C¹` functions of the projection pair separate the flags: the real and
imaginary parts of the entries of `(P_U, P_Y)` are such functions. -/
private theorem flagApprox_separates (W : ℕ) : (flagApprox_alg W).SeparatesPoints := by
  intro x y hxy
  have hxy' : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  have key : ∃ q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ, ContDiff ℝ 1 q ∧ q x.1 ≠ q y.1 := by
    by_contra hcon0
    have hcon : ∀ q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ, ContDiff ℝ 1 q → q x.1 = q y.1 :=
      fun q hq => by_contra fun h => hcon0 ⟨q, hq, h⟩
    apply hxy'
    have hc : ∀ i j : Fin 2 × Fin W, x.1.1 i j = y.1.1 i j ∧ x.1.2 i j = y.1.2 i j := by
      intro i j
      have a1 := hcon (fun z => (z.1 i j).re)
        ((flagApprox_contDiff_entry_re i j).comp contDiff_fst)
      have a2 := hcon (fun z => (z.1 i j).im)
        ((flagApprox_contDiff_entry_im i j).comp contDiff_fst)
      have a3 := hcon (fun z => (z.2 i j).re)
        ((flagApprox_contDiff_entry_re i j).comp contDiff_snd)
      have a4 := hcon (fun z => (z.2 i j).im)
        ((flagApprox_contDiff_entry_im i j).comp contDiff_snd)
      exact ⟨Complex.ext a1 a2, Complex.ext a3 a4⟩
    exact Prod.ext (by ext i j; exact (hc i j).1) (by ext i j; exact (hc i j).2)
  obtain ⟨q, hq, hne⟩ := key
  exact ⟨_, ⟨⟨fun z => q z.1, hq.continuous.comp continuous_subtype_val⟩, ⟨q, hq, fun _ => rfl⟩,
    rfl⟩, hne⟩

/-- Every bounded measurable `β` on the flags is an `L¹(ν)` limit of restrictions of `C¹`
functions of the projection pair `(P_U, P_Y)`, for every finite measure `ν`. -/
theorem exists_contDiff_flagApprox {W : ℕ} (ν : Measure (IsoFlag W)) [IsFiniteMeasure ν]
    {β : IsoFlag W → ℝ} (hβ : IsBddMeas β) :
    ∃ p : ℕ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ,
      (∀ n, ContDiff ℝ 1 (p n)) ∧
      Tendsto (fun n => ∫ x, |p n x.1 - β x| ∂ν) atTop (𝓝 0) := by
  have : CompactSpace (IsoFlag W) := isCompact_iff_compactSpace.mp (isCompact_isoFlags W)
  obtain ⟨hmeas, M, hM⟩ := hβ
  have hint : Integrable β ν :=
    Integrable.of_bound hmeas.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun x => by simpa using hM x)
  set R : ℝ := ν.real Set.univ with hRdef
  have hR : 0 ≤ R := measureReal_nonneg
  have hδ : ∀ n : ℕ, 0 < 1 / (2 * ((n : ℝ) + 1)) := fun n => by positivity
  have hη : ∀ n : ℕ, 0 < 1 / (2 * ((n : ℝ) + 1) * (R + 1)) := fun n => by positivity
  choose g hg using fun n : ℕ => hint.exists_boundedContinuous_integral_sub_le (hδ n)
  choose a ha using fun n : ℕ =>
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints (flagApprox_alg W)
      (flagApprox_separates W) (g n).toContinuousMap _ (hη n)
  have hmem : ∀ n, ∃ p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ,
      ContDiff ℝ 1 p ∧ ∀ x : IsoFlag W, (a n : C(IsoFlag W, ℝ)) x = p x.1 := fun n => (a n).2
  choose p hp hpa using hmem
  refine ⟨p, hp, ?_⟩
  have hbound : ∀ n : ℕ, ∫ x, |p n x.1 - β x| ∂ν ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have hpt : ∀ x : IsoFlag W,
        |p n x.1 - β x| ≤ 1 / (2 * ((n : ℝ) + 1) * (R + 1)) + ‖β x - g n x‖ := by
      intro x
      have h1 : |(a n : C(IsoFlag W, ℝ)) x - g n x| ≤ ‖(a n : C(IsoFlag W, ℝ)) -
          (g n).toContinuousMap‖ := by
        have := ContinuousMap.norm_coe_le_norm ((a n : C(IsoFlag W, ℝ)) - (g n).toContinuousMap) x
        simpa using this
      have h2 := (ha n).le
      rw [← hpa n x] at *
      calc |(a n : C(IsoFlag W, ℝ)) x - β x|
          ≤ |(a n : C(IsoFlag W, ℝ)) x - g n x| + |g n x - β x| := abs_sub_le _ _ _
        _ ≤ _ := by
          rw [Real.norm_eq_abs, abs_sub_comm (β x)]
          linarith
    have hnorm : Integrable (fun x => ‖β x - g n x‖) ν := (hint.sub (hg n).2).norm
    have hrhs : Integrable (fun x => 1 / (2 * ((n : ℝ) + 1) * (R + 1)) + ‖β x - g n x‖) ν :=
      (integrable_const _).add hnorm
    calc ∫ x, |p n x.1 - β x| ∂ν
        ≤ ∫ x, (1 / (2 * ((n : ℝ) + 1) * (R + 1)) + ‖β x - g n x‖) ∂ν :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) hrhs
            (Filter.Eventually.of_forall hpt)
      _ = 1 / (2 * ((n : ℝ) + 1) * (R + 1)) * R + ∫ x, ‖β x - g n x‖ ∂ν := by
          rw [integral_add (integrable_const _) hnorm]
          simp [hRdef, mul_comm]
      _ ≤ 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) := by
          refine add_le_add ?_ (hg n).1
          have hc : 0 < 2 * ((n : ℝ) + 1) := by positivity
          calc 1 / (2 * ((n : ℝ) + 1) * (R + 1)) * R
              = 1 / (2 * ((n : ℝ) + 1)) * (R / (R + 1)) := by field_simp
            _ ≤ 1 / (2 * ((n : ℝ) + 1)) * 1 := by
                gcongr
                exact (div_le_one (by linarith)).2 (by linarith)
            _ = _ := mul_one _
      _ = 1 / ((n : ℝ) + 1) := by field_simp; ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n => integral_nonneg fun x => abs_nonneg _) hbound

end LSBA
