import LSBA.Spectral.Counts
import LSBA.Dyson.Distribution

/-!
# From Stieltjes transforms to distribution functions

The empirical spectral measure of a Hermitian matrix is a probability measure with a
second-moment tail bound; the Stieltjes transform of a probability measure is `η⁻²`-Lipschitz
along horizontal lines; closeness on a grid extends to an interval; and closeness of two
transforms at height `η` on `[-R - 1, R + 1]`, with tails and an atom bound, controls the
distance of the distribution functions (the last paragraph of Appendix D.2
[sec:rough-density-proof]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

section G41

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The empirical spectral measure of a Hermitian matrix on a nonempty index type is a
probability measure. -/
theorem isProbabilityMeasure_empMeasure {A : Matrix n n ℂ} (hA : A.IsHermitian) [Nonempty n] :
    IsProbabilityMeasure (empMeasure A) := by
  refine ⟨?_⟩
  simp only [empMeasure, hA, ↓reduceDIte, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

/-- The sum of squares of the eigenvalues is the real part of `Tr A²`. -/
private lemma stieltjesCDF_sum_sq_eigenvalues {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∑ k, hA.eigenvalues k ^ 2 = (A * A).trace.re := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have h1 : A = U * D * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h2 : star U * U = 1 := by
    have := Unitary.coe_star_mul_self (hA.eigenvectorUnitary)
    simp [hU]
  have h3 : A * A = U * (D * D) * star U := by
    calc A * A = (U * D * star U) * (U * D * star U) := by rw [← h1]
      _ = U * D * (star U * U) * D * star U := by simp only [Matrix.mul_assoc]
      _ = U * (D * D) * star U := by rw [h2]; simp [Matrix.mul_assoc]
  have h4 : (A * A).trace = (D * D).trace := by
    rw [h3, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have h5 : D * D = Matrix.diagonal (fun k => ((hA.eigenvalues k ^ 2 : ℝ) : ℂ)) := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    congr 1
    ext k
    simp [sq]
  rw [h4, h5, Matrix.trace_diagonal, Complex.re_sum]
  simp only [Complex.ofReal_re]

/-- Second-moment tail of the empirical spectral measure: the mass outside `[-R, R]` is at most
`N⁻¹ Tr A² / R²` (Appendix D.2 [sec:rough-density-proof]). -/
theorem empMeasure_abs_gt_le {A : Matrix n n ℂ} (hA : A.IsHermitian) {R : ℝ} (hR : 0 < R) :
    (empMeasure A {t | R < |t|}).toReal ≤
      (Fintype.card n : ℝ)⁻¹ * (A * A).trace.re / R ^ 2 := by
  have hS : MeasurableSet {t : ℝ | R < |t|} := measurableSet_lt measurable_const measurable_abs
  have hm : empMeasure A {t | R < |t|} =
      (Fintype.card n : ℝ≥0∞)⁻¹ * ∑ k, ({t : ℝ | R < |t|}.indicator (fun _ => (1 : ℝ≥0∞))
        (hA.eigenvalues k)) := by
    simp only [empMeasure, hA, ↓reduceDIte, Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ hS, smul_eq_mul]
    rfl
  have hfin : ∀ k, ({t : ℝ | R < |t|}.indicator (fun _ => (1 : ℝ≥0∞)) (hA.eigenvalues k)) ≠ ⊤ :=
    fun k => by
      by_cases h : hA.eigenvalues k ∈ {t : ℝ | R < |t|} <;> simp [Set.indicator, h]
  rw [hm, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun k _ => hfin k), ← stieltjesCDF_sum_sq_eigenvalues hA, mul_div_assoc,
    Finset.sum_div]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
  by_cases h : R < |hA.eigenvalues k|
  · have : ({t : ℝ | R < |t|}.indicator (fun _ => (1 : ℝ≥0∞)) (hA.eigenvalues k)) = 1 := by
      simp [Set.indicator, h]
    rw [this, ENNReal.toReal_one, le_div_iff₀ (by positivity), one_mul]
    nlinarith [sq_abs (hA.eigenvalues k), abs_nonneg (hA.eigenvalues k)]
  · have : ({t : ℝ | R < |t|}.indicator (fun _ => (1 : ℝ≥0∞)) (hA.eigenvalues k)) = 0 := by
      simp [Set.indicator, h]
    rw [this, ENNReal.toReal_zero]
    positivity

end G41

/-! ### Lipschitz and grid bounds -/

/-- `Im z ≤ ‖t - z‖` for `Im z > 0`. -/
private lemma im_le_norm_sub' {z : ℂ} (hz : 0 < z.im) (t : ℝ) : z.im ≤ ‖(t : ℂ) - z‖ := by
  have := Complex.abs_im_le_norm ((t : ℂ) - z)
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hz] at this
  exact this

/-- `(t - z)⁻¹` has norm at most `(Im z)⁻¹` for `Im z > 0`. -/
private lemma norm_inv_sub_le' {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    ‖((t : ℂ) - z)⁻¹‖ ≤ z.im⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ hz (im_le_norm_sub' hz t)

/-- `t ↦ (t - z)⁻¹` is integrable for a finite measure when `Im z > 0`. -/
private lemma integrable_inv_sub'' (ρ : Measure ℝ) [IsFiniteMeasure ρ] {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹) ρ := by
  have hne : ∀ t : ℝ, (t : ℂ) - z ≠ 0 := fun t h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  exact Integrable.of_bound
    ((Complex.continuous_ofReal.sub continuous_const).inv₀ hne).aestronglyMeasurable z.im⁻¹
    (Filter.Eventually.of_forall (norm_inv_sub_le' hz))

/-- Horizontal Lipschitz bound `|s(E + iη) - s(E' + iη)| ≤ η⁻² |E - E'|` of the Stieltjes
transform of a probability measure (the resolvent derivative bound of Appendix D.2
[sec:rough-density-proof]). -/
theorem norm_stieltjes_sub_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {η : ℝ} (hη : 0 < η)
    (E E' : ℝ) :
    ‖stieltjes ρ (E + η * Complex.I) - stieltjes ρ (E' + η * Complex.I)‖ ≤ |E - E'| / η ^ 2 := by
  have hz : 0 < ((E : ℂ) + η * Complex.I).im := by simpa using hη
  have hz' : 0 < ((E' : ℂ) + η * Complex.I).im := by simpa using hη
  unfold stieltjes
  rw [← integral_sub (integrable_inv_sub'' ρ hz) (integrable_inv_sub'' ρ hz')]
  have h := norm_integral_le_of_norm_le_const (μ := ρ)
    (f := fun t : ℝ => ((t : ℂ) - (E + η * Complex.I))⁻¹ - ((t : ℂ) - (E' + η * Complex.I))⁻¹)
    (C := |E - E'| / η ^ 2) (Filter.Eventually.of_forall fun t => ?_)
  · simpa using h
  · set u : ℂ := (t : ℂ) - (E + η * Complex.I) with hu
    set v : ℂ := (t : ℂ) - (E' + η * Complex.I) with hv
    have hu1 : η ≤ ‖u‖ := by simpa using im_le_norm_sub' hz t
    have hv1 : η ≤ ‖v‖ := by simpa using im_le_norm_sub' hz' t
    have hu0 : u ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hη hu1)
    have hv0 : v ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hη hv1)
    have huv : u⁻¹ - v⁻¹ = (v - u) / (u * v) := by field_simp
    have hvu : v - u = ((E - E' : ℝ) : ℂ) := by
      rw [hu, hv]; push_cast; ring
    rw [huv, norm_div, hvu, Complex.norm_real, norm_mul, Real.norm_eq_abs]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : η * η ≤ ‖u‖ * ‖v‖ := mul_le_mul hu1 hv1 hη.le (norm_nonneg _)
    nlinarith [abs_nonneg (E - E')]

/-- From a grid of spacing `σ` to the whole interval `[x₀, x₀ + (K - 1)σ]`: the gaps cost
`2σ/η²` (Appendix D.2 [sec:rough-density-proof]). -/
theorem norm_stieltjes_sub_le_of_grid (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {η σ ε₀ : ℝ} (hη : 0 < η) (hσ : 0 < σ) (x₀ : ℝ) (K : ℕ)
    (hgrid : ∀ j : ℕ, j < K →
      ‖stieltjes μ ((x₀ + j * σ : ℝ) + η * Complex.I) -
        stieltjes ν ((x₀ + j * σ : ℝ) + η * Complex.I)‖ ≤ ε₀)
    (E : ℝ) (hE : E ∈ Set.Icc x₀ (x₀ + ((K : ℝ) - 1) * σ)) :
    ‖stieltjes μ (E + η * Complex.I) - stieltjes ν (E + η * Complex.I)‖ ≤
      ε₀ + 2 * σ / η ^ 2 := by
  obtain ⟨hE1, hE2⟩ := hE
  set t : ℝ := (E - x₀) / σ with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hσ.le
  have htK : t ≤ (K : ℝ) - 1 := by
    rw [ht, div_le_iff₀ hσ]; linarith
  have hK : 1 ≤ K := by
    have : (0 : ℝ) ≤ (K : ℝ) - 1 := le_trans ht0 htK
    have : (1 : ℝ) ≤ K := by linarith
    exact_mod_cast this
  set j : ℕ := ⌈t⌉₊ with hj
  have hjt : t ≤ j := Nat.le_ceil t
  have hjlt : (j : ℝ) < t + 1 := Nat.ceil_lt_add_one ht0
  have hjK : j < K := by
    have : j ≤ K - 1 := Nat.ceil_le.mpr (by
      rw [Nat.cast_sub hK]; simpa using htK)
    omega
  have hEj : E ≤ x₀ + j * σ := by
    have := mul_le_mul_of_nonneg_right hjt hσ.le
    rw [ht, div_mul_cancel₀ _ hσ.ne'] at this
    linarith
  have hEj' : x₀ + j * σ - E ≤ σ := by
    have := mul_le_mul_of_nonneg_right hjlt.le hσ.le
    rw [ht, add_mul, div_mul_cancel₀ _ hσ.ne'] at this
    linarith
  have hμ := norm_stieltjes_sub_le μ hη E (x₀ + j * σ)
  have hν := norm_stieltjes_sub_le ν hη (x₀ + j * σ) E
  have hg := hgrid j hjK
  have hab : |E - (x₀ + j * σ)| ≤ σ := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; exact hEj'
  have hab' : |(x₀ + j * σ) - E| ≤ σ := by
    rw [abs_of_nonneg (by linarith)]; exact hEj'
  have hμ' : ‖stieltjes μ (E + η * Complex.I) - stieltjes μ ((x₀ + j * σ : ℝ) + η * Complex.I)‖
      ≤ σ / η ^ 2 := hμ.trans (div_le_div_of_nonneg_right hab (by positivity))
  have hν' : ‖stieltjes ν ((x₀ + j * σ : ℝ) + η * Complex.I) - stieltjes ν (E + η * Complex.I)‖
      ≤ σ / η ^ 2 := hν.trans (div_le_div_of_nonneg_right hab' (by positivity))
  calc ‖stieltjes μ (E + η * Complex.I) - stieltjes ν (E + η * Complex.I)‖
      = ‖(stieltjes μ (E + η * Complex.I) - stieltjes μ ((x₀ + j * σ : ℝ) + η * Complex.I)) +
        (stieltjes μ ((x₀ + j * σ : ℝ) + η * Complex.I) -
          stieltjes ν ((x₀ + j * σ : ℝ) + η * Complex.I)) +
        (stieltjes ν ((x₀ + j * σ : ℝ) + η * Complex.I) - stieltjes ν (E + η * Complex.I))‖ := by
        congr 1; ring
    _ ≤ ‖stieltjes μ (E + η * Complex.I) - stieltjes μ ((x₀ + j * σ : ℝ) + η * Complex.I)‖ +
        ‖stieltjes μ ((x₀ + j * σ : ℝ) + η * Complex.I) -
          stieltjes ν ((x₀ + j * σ : ℝ) + η * Complex.I)‖ +
        ‖stieltjes ν ((x₀ + j * σ : ℝ) + η * Complex.I) - stieltjes ν (E + η * Complex.I)‖ :=
        (norm_add₃_le)
    _ ≤ σ / η ^ 2 + ε₀ + σ / η ^ 2 := by gcongr
    _ = ε₀ + 2 * σ / η ^ 2 := by ring

/-! ### Poisson smoothing of a distribution function -/

/-- `Im S_ρ(E + iη) = ∫ η / ((t - E)² + η²) dρ(t)`. -/
private lemma im_stieltjes'' (ρ : Measure ℝ) [IsFiniteMeasure ρ] (E : ℝ) {η : ℝ} (hη : 0 < η) :
    (stieltjes ρ (E + η * Complex.I)).im = ∫ t, η / ((t - E) ^ 2 + η ^ 2) ∂ρ := by
  have hz : 0 < ((E : ℂ) + η * Complex.I).im := by simpa using hη
  unfold stieltjes
  have h := integral_im (integrable_inv_sub'' ρ hz)
  simp only [RCLike.im_to_complex] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [Complex.inv_im, Complex.normSq_apply]
  ring

/-- The Poisson kernel is bounded by `η⁻¹`. -/
private lemma poisson_le' (t E : ℝ) {η : ℝ} (hη : 0 < η) : η / ((t - E) ^ 2 + η ^ 2) ≤ η⁻¹ := by
  have hpos : 0 < (t - E) ^ 2 + η ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  have : η⁻¹ * η ^ 2 = η := by field_simp
  nlinarith [sq_nonneg (t - E), inv_pos.mpr hη]

/-- The Poisson kernel is an `E`-derivative of `arctan ((E - t) / η)`. -/
private lemma hasDerivAt_arctan_poisson' (t E : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun E => Real.arctan ((E - t) / η)) (η / ((t - E) ^ 2 + η ^ 2)) E := by
  have h := (((hasDerivAt_id' E).sub_const t).div_const η).arctan
  convert h using 1
  have hpos : 0 < (t - E) ^ 2 + η ^ 2 := by positivity
  field_simp
  ring

/-- The smoothed Heaviside function `u ↦ 1/2 + π⁻¹ arctan (u / η)`: the distribution function of
the Cauchy law of scale `η`. -/
private def poissonStep (η u : ℝ) : ℝ := 1 / 2 + π⁻¹ * Real.arctan (u / η)

private lemma poissonStep_nonneg (η u : ℝ) : 0 ≤ poissonStep η u := by
  unfold poissonStep
  have := Real.neg_pi_div_two_lt_arctan (u / η)
  have hπ := Real.pi_pos
  have : -(1 / 2) ≤ π⁻¹ * Real.arctan (u / η) := by
    rw [← neg_div, le_inv_mul_iff₀ hπ] at *
    nlinarith
  linarith

private lemma poissonStep_le_one (η u : ℝ) : poissonStep η u ≤ 1 := by
  unfold poissonStep
  have := Real.arctan_lt_pi_div_two (u / η)
  have hπ := Real.pi_pos
  have : π⁻¹ * Real.arctan (u / η) ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ hπ]
    nlinarith
  linarith

private lemma poissonStep_mono {η : ℝ} (hη : 0 < η) : Monotone (poissonStep η) := by
  intro u v huv
  unfold poissonStep
  have := Real.arctan_mono (div_le_div_of_nonneg_right huv hη.le)
  have hπ := Real.pi_pos
  have := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hπ.le)
  linarith

private lemma poissonStep_continuous (η : ℝ) : Continuous (poissonStep η) := by
  unfold poissonStep
  fun_prop

/-- `Φ_η(-c) ≤ η / (π c)` for `c > 0`. -/
private lemma poissonStep_neg_le {η : ℝ} (hη : 0 < η) {c : ℝ} (hc : 0 < c) :
    poissonStep η (-c) ≤ η / (π * c) := by
  unfold poissonStep
  have h1 : Real.arctan (c / η) = π / 2 - Real.arctan (η / c) := by
    rw [← Real.arctan_inv_of_pos (by positivity), inv_div]
  have h2 : Real.arctan (η / c) ≤ η / c := Real.arctan_le_self (by positivity)
  rw [neg_div, Real.arctan_neg, h1]
  have hπ := Real.pi_pos
  have : η / (π * c) = π⁻¹ * (η / c) := by field_simp
  rw [this]
  have := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hπ.le)
  have e : (1 : ℝ) / 2 + π⁻¹ * -(π / 2 - Real.arctan (η / c)) = π⁻¹ * Real.arctan (η / c) := by
    field_simp
    ring
  linarith

/-- `Φ_η(c) ≥ 1 - η / (π c)` for `c > 0`. -/
private lemma one_sub_le_poissonStep {η : ℝ} (hη : 0 < η) {c : ℝ} (hc : 0 < c) :
    1 - η / (π * c) ≤ poissonStep η c := by
  unfold poissonStep
  have h1 : Real.arctan (c / η) = π / 2 - Real.arctan (η / c) := by
    rw [← Real.arctan_inv_of_pos (by positivity), inv_div]
  have h2 : Real.arctan (η / c) ≤ η / c := Real.arctan_le_self (by positivity)
  rw [h1]
  have hπ := Real.pi_pos
  have : η / (π * c) = π⁻¹ * (η / c) := by field_simp
  rw [this]
  have := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hπ.le)
  have e : (1 : ℝ) / 2 + π⁻¹ * (π / 2 - Real.arctan (η / c)) = 1 - π⁻¹ * Real.arctan (η / c) := by
    field_simp
    ring
  linarith

private lemma integrable_poissonStep (ρ : Measure ℝ) [IsFiniteMeasure ρ] (η y : ℝ) :
    Integrable (fun t : ℝ => poissonStep η (y - t)) ρ :=
  Integrable.of_bound ((poissonStep_continuous η).comp (continuous_const.sub continuous_id)
    ).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (poissonStep_nonneg _ _)]
      exact poissonStep_le_one _ _)

/-- The Poisson smoothing `∫ Φ_η(y - t) dρ(t)` of the distribution function of `ρ`. -/
private def smoothCDF (ρ : Measure ℝ) (η y : ℝ) : ℝ := ∫ t, poissonStep η (y - t) ∂ρ

private lemma smoothCDF_nonneg (ρ : Measure ℝ) (η y : ℝ) : 0 ≤ smoothCDF ρ η y :=
  integral_nonneg fun _ => poissonStep_nonneg _ _

/-- The smoothing is the integral of the imaginary part of the transform (Fubini). -/
private lemma smoothCDF_sub (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {η : ℝ} (hη : 0 < η)
    {y₁ y₂ : ℝ} (h : y₁ ≤ y₂) :
    smoothCDF ρ η y₂ - smoothCDF ρ η y₁ =
      ∫ E in y₁..y₂, π⁻¹ * (stieltjes ρ (E + η * Complex.I)).im := by
  unfold smoothCDF
  rw [← integral_sub (integrable_poissonStep ρ η y₂) (integrable_poissonStep ρ η y₁)]
  have hπ := Real.pi_pos
  have hcont : ∀ t : ℝ, Continuous fun E : ℝ => π⁻¹ * (η / ((t - E) ^ 2 + η ^ 2)) := fun t =>
    continuous_const.mul (continuous_const.div (by fun_prop) (fun E => by positivity))
  have key : ∀ t : ℝ, poissonStep η (y₂ - t) - poissonStep η (y₁ - t) =
      ∫ E in Set.Ioc y₁ y₂, π⁻¹ * (η / ((t - E) ^ 2 + η ^ 2)) := by
    intro t
    rw [← intervalIntegral.integral_of_le h]
    have hd : ∀ E ∈ Set.uIcc y₁ y₂, HasDerivAt (fun E : ℝ => poissonStep η (E - t))
        (π⁻¹ * (η / ((t - E) ^ 2 + η ^ 2))) E := fun E _ =>
      ((hasDerivAt_arctan_poisson' t E hη).const_mul π⁻¹).const_add (1 / 2)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((hcont t).intervalIntegrable _ _)]
  simp_rw [key]
  have hint : Integrable (Function.uncurry fun (t E : ℝ) => π⁻¹ * (η / ((t - E) ^ 2 + η ^ 2)))
      (ρ.prod (volume.restrict (Set.Ioc y₁ y₂))) := by
    refine Integrable.of_bound ?_ (π⁻¹ * η⁻¹) (Filter.Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact continuous_const.mul (continuous_const.div (by fun_prop) (fun p => by positivity))
    · dsimp only [Function.uncurry]
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (poisson_le' _ _ hη) (inv_nonneg.mpr hπ.le)
  rw [integral_integral_swap hint, intervalIntegral.integral_of_le h]
  refine setIntegral_congr_fun measurableSet_Ioc fun E _ => ?_
  rw [integral_const_mul, im_stieltjes'' ρ E hη]

private lemma real_le_one (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (S : Set ℝ) : ρ.real S ≤ 1 := by
  have := measureReal_mono (μ := ρ) (Set.subset_univ S)
  rwa [probReal_univ] at this

/-- Upper bound for the smoothing: if `y - t ≤ -c` off `S`, then the smoothing at `y` is at most
`ρ(S) + η / (π c)`. -/
private lemma smoothCDF_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {η : ℝ} (hη : 0 < η)
    {S : Set ℝ} (hS : MeasurableSet S) {y c : ℝ} (hc : 0 < c) (h : ∀ t, t ∉ S → y - t ≤ -c) :
    smoothCDF ρ η y ≤ ρ.real S + η / (π * c) := by
  have hpt : ∀ t, poissonStep η (y - t) ≤ S.indicator (fun _ => (1 : ℝ)) t + poissonStep η (-c) :=
    fun t => by
      by_cases ht : t ∈ S
      · rw [Set.indicator_of_mem ht]
        linarith [poissonStep_le_one η (y - t), poissonStep_nonneg η (-c)]
      · rw [Set.indicator_of_notMem ht, zero_add]
        exact poissonStep_mono hη (h t ht)
  have hi : Integrable (S.indicator (fun _ => (1 : ℝ))) ρ := (integrable_const (1 : ℝ)).indicator hS
  calc smoothCDF ρ η y
      ≤ ∫ t, (S.indicator (fun _ => (1 : ℝ)) t + poissonStep η (-c)) ∂ρ :=
        integral_mono (integrable_poissonStep ρ η y) (hi.add (integrable_const _)) hpt
    _ = ρ.real S + poissonStep η (-c) := by
        rw [integral_add hi (integrable_const _), integral_indicator_const _ hS]
        simp
    _ ≤ ρ.real S + η / (π * c) := by linarith [poissonStep_neg_le hη hc]

/-- Lower bound for the smoothing: if `c ≤ y - t` on `S`, then the smoothing at `y` is at least
`ρ(S) - η / (π c)`. -/
private lemma le_smoothCDF (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {η : ℝ} (hη : 0 < η)
    {S : Set ℝ} (hS : MeasurableSet S) {y c : ℝ} (hc : 0 < c) (h : ∀ t, t ∈ S → c ≤ y - t) :
    ρ.real S - η / (π * c) ≤ smoothCDF ρ η y := by
  have hpt : ∀ t, S.indicator (fun _ => poissonStep η c) t ≤ poissonStep η (y - t) := fun t => by
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ht]
      exact poissonStep_mono hη (h t ht)
    · rw [Set.indicator_of_notMem ht]
      exact poissonStep_nonneg _ _
  have hi : Integrable (S.indicator (fun _ => poissonStep η c)) ρ :=
    (integrable_const _).indicator hS
  have h1 : ∫ t, S.indicator (fun _ => poissonStep η c) t ∂ρ ≤ smoothCDF ρ η y :=
    integral_mono hi (integrable_poissonStep ρ η y) hpt
  rw [integral_indicator_const _ hS, smul_eq_mul] at h1
  have he : 0 ≤ η / (π * c) := by positivity
  have hs1 := real_le_one ρ S
  have hs0 : 0 ≤ ρ.real S := measureReal_nonneg
  have := one_sub_le_poissonStep hη hc
  nlinarith

/-- The smoothing at `x - c` is at most `F_ρ(x) + η / (π c)`. -/
private lemma smoothCDF_le_cdf (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {η : ℝ} (hη : 0 < η)
    {c : ℝ} (hc : 0 < c) (x : ℝ) :
    smoothCDF ρ η (x - c) ≤ ρ.real (Set.Iic x) + η / (π * c) :=
  smoothCDF_le ρ hη measurableSet_Iic hc fun t ht => by
    simp only [Set.mem_Iic, not_le] at ht
    linarith

/-- The smoothing at `x + c` is at least `F_ρ(x) - η / (π c)`. -/
private lemma cdf_le_smoothCDF (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {η : ℝ} (hη : 0 < η)
    {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ρ.real (Set.Iic x) - η / (π * c) ≤ smoothCDF ρ η (x + c) :=
  le_smoothCDF ρ hη measurableSet_Iic hc fun t ht => by
    simp only [Set.mem_Iic] at ht
    linarith

/-- `E ↦ s_ρ(E + iη)` is continuous (it is `η⁻²`-Lipschitz). -/
private lemma continuous_stieltjes_horizontal (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {η : ℝ}
    (hη : 0 < η) : Continuous fun E : ℝ => stieltjes ρ (E + η * Complex.I) := by
  have hK : (0 : ℝ) ≤ (η ^ 2)⁻¹ := by positivity
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (η ^ 2)⁻¹) fun E E' => ?_).continuous
  rw [Real.coe_toNNReal _ hK, dist_eq_norm, Real.dist_eq]
  refine (norm_stieltjes_sub_le ρ hη E E').trans ?_
  rw [div_eq_inv_mul, mul_comm]

/-- The smoothing is at most `τ + η/π` at `-R - 1`, when the left tail is at most `τ`. -/
private lemma smoothCDF_left_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {η R τ : ℝ} (hη : 0 < η)
    (hl : (ρ (Set.Iio (-R))).toReal ≤ τ) : smoothCDF ρ η (-R - 1) ≤ τ + η / π := by
  have := smoothCDF_le ρ hη (S := Set.Iio (-R)) measurableSet_Iio (y := -R - 1) (c := 1)
    one_pos fun t ht => by
    simp only [Set.mem_Iio, not_lt] at ht
    linarith
  rw [mul_one] at this
  have h2 : ρ.real (Set.Iio (-R)) ≤ τ := hl
  linarith

/-- Closeness of the smoothings on `[-R - 1, R + 1]` from closeness of the transforms. -/
private lemma smoothCDF_sub_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {R η τ ε : ℝ} (hη : 0 < η)
    (hμl : (μ (Set.Iio (-R))).toReal ≤ τ) (hνl : (ν (Set.Iio (-R))).toReal ≤ τ)
    (hs : ∀ E ∈ Set.Icc (-R - 1) (R + 1),
      ‖stieltjes μ (E + η * Complex.I) - stieltjes ν (E + η * Complex.I)‖ ≤ ε)
    {y : ℝ} (hy : y ∈ Set.Icc (-R - 1) (R + 1)) :
    |smoothCDF μ η y - smoothCDF ν η y| ≤ τ + η / π + π⁻¹ * ε * (y + R + 1) := by
  have hπ := Real.pi_pos
  obtain ⟨hy1, hy2⟩ := hy
  have hcont : ∀ ρ : Measure ℝ, IsProbabilityMeasure ρ →
      Continuous fun E : ℝ => π⁻¹ * (stieltjes ρ (E + η * Complex.I)).im := fun ρ _ =>
    continuous_const.mul (Complex.continuous_im.comp (continuous_stieltjes_horizontal ρ hη))
  have hμ := smoothCDF_sub μ hη hy1
  have hν := smoothCDF_sub ν hη hy1
  have hdiff : (smoothCDF μ η y - smoothCDF ν η y) =
      (smoothCDF μ η (-R - 1) - smoothCDF ν η (-R - 1)) +
        ∫ E in (-R - 1)..y, (π⁻¹ * (stieltjes μ (E + η * Complex.I)).im -
          π⁻¹ * (stieltjes ν (E + η * Complex.I)).im) := by
    rw [intervalIntegral.integral_sub ((hcont μ ‹_›).intervalIntegrable _ _)
      ((hcont ν ‹_›).intervalIntegrable _ _)]
    linarith
  have hint : ‖∫ E in (-R - 1)..y, (π⁻¹ * (stieltjes μ (E + η * Complex.I)).im -
          π⁻¹ * (stieltjes ν (E + η * Complex.I)).im)‖ ≤ π⁻¹ * ε * (y + R + 1) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -R - 1) (b := y)
      (f := fun E => π⁻¹ * (stieltjes μ (E + η * Complex.I)).im -
          π⁻¹ * (stieltjes ν (E + η * Complex.I)).im) (C := π⁻¹ * ε) fun E hE => by
      rw [Set.uIoc_of_le hy1] at hE
      have hE' : E ∈ Set.Icc (-R - 1) (R + 1) := ⟨hE.1.le, hE.2.trans hy2⟩
      have h1 := hs E hE'
      have h2 : |(stieltjes μ (E + η * Complex.I)).im - (stieltjes ν (E + η * Complex.I)).im| ≤ ε :=
        (Complex.abs_im_le_norm _).trans h1 |> fun h => by simpa using h
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hπ)]
      exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hπ.le)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - (-R - 1)), show y - (-R - 1) = y + R + 1 by ring]
      at this
    exact this
  have h0μ := smoothCDF_nonneg μ η (-R - 1)
  have h0ν := smoothCDF_nonneg ν η (-R - 1)
  have hμe := smoothCDF_left_le μ hη hμl
  have hνe := smoothCDF_left_le ν hη hνl
  rw [hdiff]
  calc |(smoothCDF μ η (-R - 1) - smoothCDF ν η (-R - 1)) + ∫ E in (-R - 1)..y,
        (π⁻¹ * (stieltjes μ (E + η * Complex.I)).im - π⁻¹ * (stieltjes ν (E + η * Complex.I)).im)|
      ≤ |smoothCDF μ η (-R - 1) - smoothCDF ν η (-R - 1)| + ‖∫ E in (-R - 1)..y,
        (π⁻¹ * (stieltjes μ (E + η * Complex.I)).im -
          π⁻¹ * (stieltjes ν (E + η * Complex.I)).im)‖ :=
        abs_add_le _ _
    _ ≤ (τ + η / π) + π⁻¹ * ε * (y + R + 1) := by
        refine add_le_add ?_ hint
        rw [abs_le]
        constructor <;> linarith

/-- An atom bound on intervals of length `2h` gives `F(x + 2h) ≤ F(x) + a`. -/
private lemma cdf_add_le (ν : Measure ℝ) [IsProbabilityMeasure ν] {h a : ℝ}
    (hν : ∀ y : ℝ, (ν (Set.Icc (y - h) (y + h))).toReal ≤ a) (x : ℝ) :
    ν.real (Set.Iic (x + 2 * h)) ≤ ν.real (Set.Iic x) + a := by
  have hsub : Set.Iic (x + 2 * h) ⊆ Set.Iic x ∪ Set.Icc ((x + h) - h) ((x + h) + h) := by
    intro t ht
    simp only [Set.mem_Iic] at ht
    by_cases hx : t ≤ x
    · exact Or.inl hx
    · refine Or.inr ⟨by linarith, by linarith⟩
  calc ν.real (Set.Iic (x + 2 * h))
      ≤ ν.real (Set.Iic x ∪ Set.Icc ((x + h) - h) ((x + h) + h)) := measureReal_mono hsub
    _ ≤ ν.real (Set.Iic x) + ν.real (Set.Icc ((x + h) - h) ((x + h) + h)) :=
        measureReal_union_le _ _
    _ ≤ ν.real (Set.Iic x) + a := by
        have := hν (x + h)
        exact add_le_add_right this _

/-- An atom bound on intervals of length `2h` gives `F(x) ≤ F(x - 2h) + a`. -/
private lemma cdf_le_sub_add (ν : Measure ℝ) [IsProbabilityMeasure ν] {h a : ℝ}
    (hν : ∀ y : ℝ, (ν (Set.Icc (y - h) (y + h))).toReal ≤ a) (x : ℝ) :
    ν.real (Set.Iic x) ≤ ν.real (Set.Iic (x - 2 * h)) + a := by
  have hsub : Set.Iic x ⊆ Set.Iic (x - 2 * h) ∪ Set.Icc ((x - h) - h) ((x - h) + h) := by
    intro t ht
    simp only [Set.mem_Iic] at ht
    by_cases hx : t ≤ x - 2 * h
    · exact Or.inl hx
    · refine Or.inr ⟨by linarith, by linarith⟩
  calc ν.real (Set.Iic x)
      ≤ ν.real (Set.Iic (x - 2 * h) ∪ Set.Icc ((x - h) - h) ((x - h) + h)) := measureReal_mono hsub
    _ ≤ ν.real (Set.Iic (x - 2 * h)) + ν.real (Set.Icc ((x - h) - h) ((x - h) + h)) :=
        measureReal_union_le _ _
    _ ≤ ν.real (Set.Iic (x - 2 * h)) + a := by
        have := hν (x - h)
        exact add_le_add_right this _

/-- From Stieltjes transforms at height `η` to distribution functions (Appendix D.2
[sec:rough-density-proof], last paragraph): tails `τ` outside `[-R, R]`, the atom bound `a` of
`ν` on intervals of length `2h` (cf. (1.13) [rd:eq:noatoms]), and closeness `ε` of the
transforms on `[-R - 1, R + 1]`. -/
theorem cdf_sub_le_of_stieltjes (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {R η h τ a ε : ℝ} (hR : 0 < R) (hη : 0 < η) (hh : 0 < h)
    (hh1 : h ≤ 1)
    (hμl : (μ (Set.Iio (-R))).toReal ≤ τ) (hμr : (μ (Set.Ioi R)).toReal ≤ τ)
    (hνl : (ν (Set.Iio (-R))).toReal ≤ τ) (hνr : (ν (Set.Ioi R)).toReal ≤ τ)
    (hν : ∀ y : ℝ, (ν (Set.Icc (y - h) (y + h))).toReal ≤ a)
    (hs : ∀ E ∈ Set.Icc (-R - 1) (R + 1),
      ‖stieltjes μ (E + η * Complex.I) - stieltjes ν (E + η * Complex.I)‖ ≤ ε) (x : ℝ) :
    |(μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal| ≤
      2 * τ + 2 * η / π + (2 * R + 2) * ε / π + 2 * η / (π * h) + a := by
  have hπ := Real.pi_pos
  have hτ : 0 ≤ τ := (ENNReal.toReal_nonneg).trans hμl
  have ha : 0 ≤ a := (ENNReal.toReal_nonneg).trans (hν 0)
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hs 0 ⟨by linarith, by linarith⟩)
  have e1 : 0 ≤ η / π := by positivity
  have e2 : 0 ≤ η / (π * h) := by positivity
  have e3 : 0 ≤ (2 * R + 2) * ε / π := by positivity
  have hB : 2 * η / π = 2 * (η / π) := by ring
  have hB' : 2 * η / (π * h) = 2 * (η / (π * h)) := by ring
  rw [hB, hB']
  change |μ.real (Set.Iic x) - ν.real (Set.Iic x)| ≤ _
  by_cases hx : |x| ≤ R
  · rw [abs_le] at hx
    obtain ⟨hx1, hx2⟩ := hx
    -- closeness of the smoothings at `x ± h`
    have hΔ : ∀ y ∈ Set.Icc (-R - 1) (R + 1),
        |smoothCDF μ η y - smoothCDF ν η y| ≤ τ + η / π + (2 * R + 2) * ε / π := by
      intro y hy
      refine (smoothCDF_sub_le μ ν hη hμl hνl hs hy).trans ?_
      have : π⁻¹ * ε * (y + R + 1) ≤ π⁻¹ * ε * (2 * R + 2) :=
        mul_le_mul_of_nonneg_left (by linarith [hy.2]) (by positivity)
      have e : (2 * R + 2) * ε / π = π⁻¹ * ε * (2 * R + 2) := by ring
      linarith
    have hp := hΔ (x + h) ⟨by linarith, by linarith⟩
    have hm := hΔ (x - h) ⟨by linarith, by linarith⟩
    rw [abs_le] at hp hm
    have u1 := cdf_le_smoothCDF μ hη hh x
    have u2 := smoothCDF_le_cdf ν hη hh (x + 2 * h)
    rw [show x + 2 * h - h = x + h by ring] at u2
    have u3 := cdf_add_le ν hν x
    have l1 := cdf_le_sub_add ν hν x
    have l2 := cdf_le_smoothCDF ν hη hh (x - 2 * h)
    rw [show x - 2 * h + h = x - h by ring] at l2
    have l3 := smoothCDF_le_cdf μ hη hh x
    rw [abs_le]
    constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]
  · have hx := not_le.mp hx
    have hμ1 := real_le_one μ (Set.Iic x)
    have hν1 := real_le_one ν (Set.Iic x)
    have hμ0 : 0 ≤ μ.real (Set.Iic x) := measureReal_nonneg
    have hν0 : 0 ≤ ν.real (Set.Iic x) := measureReal_nonneg
    rcases lt_abs.mp hx with hxR | hxR
    · -- `x > R`
      have key : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ], (ρ (Set.Ioi R)).toReal ≤ τ →
          1 - τ ≤ ρ.real (Set.Iic x) := by
        intro ρ _ hr
        have h1 : ρ.real (Set.Ioi x) ≤ ρ.real (Set.Ioi R) :=
          measureReal_mono (Set.Ioi_subset_Ioi hxR.le)
        have h2 : ρ.real (Set.Ioi R) ≤ τ := hr
        have h3 := probReal_compl_eq_one_sub (μ := ρ) (measurableSet_Iic (a := x))
        rw [Set.compl_Iic] at h3
        linarith
      have a1 := key μ hμr
      have a2 := key ν hνr
      rw [abs_le]
      constructor <;> linarith
    · -- `x < -R`
      have key : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ], (ρ (Set.Iio (-R))).toReal ≤ τ →
          ρ.real (Set.Iic x) ≤ τ := by
        intro ρ _ hl
        have h1 : ρ.real (Set.Iic x) ≤ ρ.real (Set.Iio (-R)) :=
          measureReal_mono (Set.Iic_subset_Iio.mpr (by linarith))
        have h2 : ρ.real (Set.Iio (-R)) ≤ τ := hl
        linarith
      have a1 := key μ hμl
      have a2 := key ν hνl
      rw [abs_le]
      constructor <;> linarith

end LSBA
