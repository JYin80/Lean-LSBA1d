import LSBA.Gauss.Divergence

/-!
# Gaussian integration by parts with frozen coordinates

(8.33) [up:eq:gaussian-divergence] for fields whose components vanish off a set `A` of active
coordinates and which are `C¹` of polynomial growth in the active coordinates for almost every
value of the others, as allowed in Lemma 8.11 [up:lem:angular].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

namespace LSBA

/-- The map `(z, x) ↦ A.piecewise z x` is measurable. -/
private lemma divFrozen_measurable_mix {ι : Type*} [DecidableEq ι] (A : Finset ι) :
    Measurable (fun p : (ι → ℝ) × (ι → ℝ) => A.piecewise p.1 p.2) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases hi : i ∈ A
  · simp only [Finset.piecewise_eq_of_mem _ _ _ hi]
    exact (measurable_pi_apply i).comp measurable_fst
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ hi]
    exact (measurable_pi_apply i).comp measurable_snd

/-- The map `(z, x) ↦ A.piecewise z x` pushes the product of two copies of `stdGauss ι` to
`stdGauss ι`: each coordinate keeps the law `N(0, 1)` and the coordinates stay independent. -/
private lemma divFrozen_mix_mp {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) :
    MeasurePreserving (fun p : (ι → ℝ) × (ι → ℝ) => A.piecewise p.1 p.2)
      ((stdGauss ι).prod (stdGauss ι)) (stdGauss ι) := by
  refine ⟨divFrozen_measurable_mix A, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (divFrozen_measurable_mix A) (MeasurableSet.univ_pi hs)]
  let t₁ : ι → Set ℝ := fun i => if i ∈ A then s i else Set.univ
  let t₂ : ι → Set ℝ := fun i => if i ∈ A then Set.univ else s i
  have hpre : (fun p : (ι → ℝ) × (ι → ℝ) => A.piecewise p.1 p.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi t₁ ×ˢ Set.univ.pi t₂ := by
    ext ⟨z, x⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod, t₁, t₂]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i ∈ A
        · have := h i
          rw [Finset.piecewise_eq_of_mem _ _ _ hi] at this
          simpa [hi] using this
        · simp [hi]
      · by_cases hi : i ∈ A
        · simp [hi]
        · have := h i
          rw [Finset.piecewise_eq_of_notMem _ _ _ hi] at this
          simpa [hi] using this
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ A
      · rw [Finset.piecewise_eq_of_mem _ _ _ hi]
        simpa [hi] using h1 i
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hi]
        simpa [hi] using h2 i
  rw [hpre, Measure.prod_prod]
  unfold stdGauss
  rw [Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ A <;> simp [t₁, t₂, hi]

/-- The coordinate projection onto `A`. -/
private def divFrozenProj {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i => if i ∈ A then ContinuousLinearMap.proj i else 0

/-- The coordinates of the projection onto `A`. -/
private lemma divFrozenProj_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι)
    (z : ι → ℝ) (i : ι) : divFrozenProj A z i = if i ∈ A then z i else 0 := by
  unfold divFrozenProj
  by_cases hi : i ∈ A <;> simp [hi]

/-- The projection onto `A` has operator norm at most `1`. -/
private lemma divFrozenProj_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) :
    ‖divFrozenProj A‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun i => ?_
  rw [divFrozenProj_apply]
  split_ifs
  · exact norm_le_pi_norm v i
  · simp

/-- `z ↦ A.piecewise z x` is the projection onto `A` plus a constant. -/
private lemma divFrozen_piecewise_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι)
    (x : ι → ℝ) :
    (fun z => A.piecewise z x) = fun z => divFrozenProj A z + A.piecewise (0 : ι → ℝ) x := by
  funext z
  ext i
  rw [Pi.add_apply, divFrozenProj_apply]
  by_cases hi : i ∈ A <;> simp [hi, Finset.piecewise_eq_of_mem, Finset.piecewise_eq_of_notMem]

/-- The derivative of `z ↦ A.piecewise z x` is the projection onto `A`. -/
private lemma divFrozen_hasFDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι)
    (x z : ι → ℝ) : HasFDerivAt (fun z => A.piecewise z x) (divFrozenProj A) z := by
  rw [divFrozen_piecewise_eq]
  exact (divFrozenProj A).hasFDerivAt.add_const _

/-- `z ↦ A.piecewise z x` is `C¹`. -/
private lemma divFrozen_contDiff {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι)
    (x : ι → ℝ) : ContDiff ℝ 1 (fun z : ι → ℝ => A.piecewise z x) := by
  rw [divFrozen_piecewise_eq]
  exact (divFrozenProj A).contDiff.add contDiff_const

/-- `1 + ‖A.piecewise z x‖ ≤ (1 + ‖x‖) (1 + ‖z‖)`. -/
private lemma divFrozen_norm_piecewise_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι)
    (z x : ι → ℝ) : 1 + ‖A.piecewise z x‖ ≤ (1 + ‖x‖) * (1 + ‖z‖) := by
  have h : ‖A.piecewise z x‖ ≤ ‖z‖ + ‖x‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    by_cases hi : i ∈ A
    · rw [Finset.piecewise_eq_of_mem _ _ _ hi]
      linarith [norm_le_pi_norm z i, norm_nonneg x]
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hi]
      linarith [norm_le_pi_norm x i, norm_nonneg z]
  nlinarith [norm_nonneg x, norm_nonneg z]

/-- Moving the `i`-th coordinate line commutes with `A.piecewise` for `i ∈ A`. -/
private lemma divFrozen_piecewise_add_single {ι : Type*} [DecidableEq ι] (A : Finset ι)
    {i : ι} (hi : i ∈ A) (z x : ι → ℝ) (t : ℝ) :
    A.piecewise (z + t • (Pi.single i 1 : ι → ℝ)) x = A.piecewise z x + t • Pi.single i 1 := by
  ext j
  by_cases hj : j ∈ A
  · simp [Finset.piecewise_eq_of_mem _ _ _ hj]
  · have : j ≠ i := fun h => hj (h ▸ hi)
    simp [Finset.piecewise_eq_of_notMem _ _ _ hj, Pi.single_eq_of_ne this]

/-- For a field vanishing off `A`, the Gaussian divergence of the slice
`z ↦ Y (A.piecewise z x)` at `z` is that of `Y` at `A.piecewise z x`. -/
private lemma divFrozen_gaussDiv_slice {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : (ι → ℝ) → ι → ℝ} (A : Finset ι) (hzero : ∀ x, ∀ i ∉ A, Y x i = 0) (x z : ι → ℝ) :
    gaussDiv (fun z => Y (A.piecewise z x)) z = gaussDiv Y (A.piecewise z x) := by
  unfold gaussDiv
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ A
  · rw [Finset.piecewise_eq_of_mem _ _ _ hi]
    congr 1
    unfold lineDeriv
    congr 1
    funext t
    change Y (A.piecewise (z + t • (Pi.single i 1 : ι → ℝ)) x) i =
      Y (A.piecewise z x + t • (Pi.single i 1 : ι → ℝ)) i
    rw [divFrozen_piecewise_add_single A hi]
  · have h0 : (fun y => Y y i) = fun _ => 0 := funext fun y => hzero y i hi
    have h1 : (fun y => Y (A.piecewise y x) i) = fun _ => 0 :=
      funext fun y => hzero _ i hi
    rw [h1, h0]
    simp [lineDeriv, hzero _ i hi]

/-- A test function composed with `z ↦ A.piecewise z x` is a test function. -/
private lemma divFrozen_isIBPTest_slice {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι)
    (x : ι → ℝ) {φ : (ι → ℝ) → ℝ} (hφ : IsIBPTest φ) :
    IsIBPTest (fun z => φ (A.piecewise z x)) := by
  obtain ⟨hφc, ⟨M, hM⟩, ⟨C₂, k₂, hC₂⟩⟩ := hφ
  have hC₂0 : 0 ≤ C₂ := by simpa using (norm_nonneg _).trans (hC₂ 0)
  refine ⟨hφc.comp (divFrozen_contDiff A x), ⟨M, fun z => hM _⟩, ⟨C₂ * (1 + ‖x‖) ^ k₂, k₂, ?_⟩⟩
  intro z
  have hd : fderiv ℝ (fun z => φ (A.piecewise z x)) z =
      (fderiv ℝ φ (A.piecewise z x)).comp (divFrozenProj A) :=
    (((hφc.differentiable one_ne_zero) _).hasFDerivAt.comp z (divFrozen_hasFDerivAt A x z)).fderiv
  rw [hd]
  have h1 := divFrozen_norm_piecewise_le A z x
  have h2 : (1 + ‖A.piecewise z x‖) ^ k₂ ≤ ((1 + ‖x‖) * (1 + ‖z‖)) ^ k₂ :=
    pow_le_pow_left₀ (by positivity) h1 k₂
  calc ‖(fderiv ℝ φ (A.piecewise z x)).comp (divFrozenProj A)‖
      ≤ ‖fderiv ℝ φ (A.piecewise z x)‖ * ‖divFrozenProj A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (C₂ * (1 + ‖A.piecewise z x‖) ^ k₂) * 1 :=
        mul_le_mul (hC₂ _) (divFrozenProj_norm_le A) (norm_nonneg _) (by positivity)
    _ ≤ C₂ * ((1 + ‖x‖) * (1 + ‖z‖)) ^ k₂ := by rw [mul_one]; gcongr
    _ = C₂ * (1 + ‖x‖) ^ k₂ * (1 + ‖z‖) ^ k₂ := by rw [mul_pow]; ring

/-- For a field vanishing off `A`, the derivative of a slice of `φ` along the slice of `Y`
is the derivative of `φ` along `Y`. -/
private lemma divFrozen_fderiv_slice {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : (ι → ℝ) → ι → ℝ} (A : Finset ι) (hzero : ∀ x, ∀ i ∉ A, Y x i = 0) (x z : ι → ℝ)
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    fderiv ℝ (fun z => φ (A.piecewise z x)) z (Y (A.piecewise z x)) =
      fderiv ℝ φ (A.piecewise z x) (Y (A.piecewise z x)) := by
  have hd : fderiv ℝ (fun z => φ (A.piecewise z x)) z =
      (fderiv ℝ φ (A.piecewise z x)).comp (divFrozenProj A) :=
    (((hφ.differentiable one_ne_zero) _).hasFDerivAt.comp z (divFrozen_hasFDerivAt A x z)).fderiv
  rw [hd, ContinuousLinearMap.comp_apply]
  congr 1
  ext i
  rw [divFrozenProj_apply]
  split_ifs with hi
  · rfl
  · exact (hzero _ i hi).symm

/-- Gaussian integration by parts on one slice. -/
private lemma divFrozen_slice_ibp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : (ι → ℝ) → ι → ℝ} (A : Finset ι) (hzero : ∀ x, ∀ i ∉ A, Y x i = 0) {x : ι → ℝ}
    (hx : ContDiff ℝ 1 (fun z => Y (A.piecewise z x)) ∧
      PolyGrowth (fun z => Y (A.piecewise z x)) ∧
      PolyGrowth (fderiv ℝ (fun z => Y (A.piecewise z x))))
    {φ : (ι → ℝ) → ℝ} (hφ : IsIBPTest φ) :
    ∫ z, fderiv ℝ φ (A.piecewise z x) (Y (A.piecewise z x)) ∂(stdGauss ι) =
      ∫ z, φ (A.piecewise z x) * gaussDiv Y (A.piecewise z x) ∂(stdGauss ι) := by
  have h := (ibpAdmissible_of_contDiff hx.1 hx.2.1 hx.2.2).2 _
    (divFrozen_isIBPTest_slice A x hφ)
  have e1 : (fun z => fderiv ℝ (fun z => φ (A.piecewise z x)) z (Y (A.piecewise z x))) =
      fun z => fderiv ℝ φ (A.piecewise z x) (Y (A.piecewise z x)) :=
    funext fun z => divFrozen_fderiv_slice A hzero x z hφ.1
  have e2 : (fun z => φ (A.piecewise z x) * gaussDiv (fun z => Y (A.piecewise z x)) z) =
      fun z => φ (A.piecewise z x) * gaussDiv Y (A.piecewise z x) :=
    funext fun z => by rw [divFrozen_gaussDiv_slice A hzero]
  rw [e1, e2] at h
  exact h.2.2

/-- Splitting the integral over `stdGauss ι` along `A.piecewise`. -/
private lemma divFrozen_integral_split {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι)
    {F : (ι → ℝ) → ℝ} (hF : Integrable F (stdGauss ι)) :
    ∫ x, F x ∂(stdGauss ι) = ∫ x, ∫ z, F (A.piecewise z x) ∂(stdGauss ι) ∂(stdGauss ι) := by
  have hmp := divFrozen_mix_mp A
  have hI : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => F (A.piecewise p.1 p.2))
      ((stdGauss ι).prod (stdGauss ι)) := hmp.integrable_comp_of_integrable hF
  have h1 : ∫ x, F x ∂(stdGauss ι) =
      ∫ p, F (A.piecewise p.1 p.2) ∂((stdGauss ι).prod (stdGauss ι)) := by
    have h := integral_map (μ := (stdGauss ι).prod (stdGauss ι)) hmp.measurable.aemeasurable
      (f := F) (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable)
    rw [hmp.map_eq] at h
    exact h
  rw [h1]
  exact integral_prod_symm (fun p : (ι → ℝ) × (ι → ℝ) => F (A.piecewise p.1 p.2)) hI

/-- A linear form on `ℝ^ι` is the sum of its values on the coordinate vectors. -/
private lemma divFrozen_clm_apply_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) : L v = ∑ i, v i * L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (Pi.single i (v i) : ι → ℝ) = v i • Pi.single i 1 := by
    rw [← Pi.single_smul]; simp
  rw [h, map_smul, smul_eq_mul]

/-- `x ↦ D_{Y x} φ (x)` is measurable for `φ ∈ C¹` and measurable `Y`. -/
private lemma divFrozen_measurable_fderiv_apply {ι : Type*} [Fintype ι]
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) {Y : (ι → ℝ) → ι → ℝ} (hY : Measurable Y) :
    Measurable (fun x => fderiv ℝ φ x (Y x)) := by
  classical
  have hD : Continuous (fun x => fderiv ℝ φ x) := hφ.continuous_fderiv one_ne_zero
  have h : (fun x => fderiv ℝ φ x (Y x)) =
      fun x => ∑ i, Y x i * fderiv ℝ φ x (Pi.single i 1) :=
    funext fun x => divFrozen_clm_apply_eq _ _
  rw [h]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).comp hY).mul
    (hD.clm_apply continuous_const).measurable

/-- (8.33) [up:eq:gaussian-divergence] after conditioning on frozen coordinates (Lemma 8.11
[up:lem:angular]): the components of `Y` off `A` vanish; for almost every `x`, the slice
`z ↦ Y (A.piecewise z x)` is `C¹` with polynomial growth of the slice and its derivative;
`Y` and `δ_G Y` are measurable, `‖Y‖ (1 + ‖x‖)^k` is integrable for every `k`, and `δ_G Y` is
integrable. -/
theorem ibpAdmissible_of_frozen {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : (ι → ℝ) → ι → ℝ} (A : Finset ι) (hzero : ∀ x, ∀ i ∉ A, Y x i = 0)
    (hslice : ∀ᵐ x ∂(stdGauss ι), ContDiff ℝ 1 (fun z => Y (A.piecewise z x)) ∧
      PolyGrowth (fun z => Y (A.piecewise z x)) ∧
      PolyGrowth (fderiv ℝ (fun z => Y (A.piecewise z x))))
    (hY : Measurable Y) (hdiv : Measurable (gaussDiv Y))
    (hint : ∀ k : ℕ, Integrable (fun x => ‖Y x‖ * (1 + ‖x‖) ^ k) (stdGauss ι))
    (hdivint : Integrable (gaussDiv Y) (stdGauss ι)) : IBPAdmissible Y := by
  refine ⟨hdiv, fun φ hφ => ?_⟩
  obtain ⟨hφc, ⟨M, hM⟩, ⟨C₂, k₂, hC₂⟩⟩ := id hφ
  have hI1 : Integrable (fun x => fderiv ℝ φ x (Y x)) (stdGauss ι) := by
    refine ((hint k₂).const_mul C₂).mono'
      (divFrozen_measurable_fderiv_apply hφc hY).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    calc ‖fderiv ℝ φ x (Y x)‖ ≤ ‖fderiv ℝ φ x‖ * ‖Y x‖ := (fderiv ℝ φ x).le_opNorm _
      _ ≤ C₂ * (1 + ‖x‖) ^ k₂ * ‖Y x‖ := by gcongr; exact hC₂ x
      _ = C₂ * (‖Y x‖ * (1 + ‖x‖) ^ k₂) := by ring
  have hI2 : Integrable (fun x => φ x * gaussDiv Y x) (stdGauss ι) :=
    hdivint.bdd_mul hφc.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)
  refine ⟨hI1, hI2, ?_⟩
  rw [divFrozen_integral_split A hI1, divFrozen_integral_split A hI2]
  refine integral_congr_ae ?_
  filter_upwards [hslice] with x hx
  exact divFrozen_slice_ibp A hzero hx hφ

end LSBA
