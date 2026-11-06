import LSBA.Gauss.StdGauss

/-!
# Gaussian divergence on `ℝ^ι`

The Gaussian divergence `δ_G Y = Σ_i (x_i Y_i - ∂_i Y_i)` of a vector field on `ℝ^ι` under the
standard Gaussian law, the class of test functions, Gaussian integration by parts
`𝔼 D_Y φ = 𝔼[φ δ_G Y]` of (8.33) [up:eq:gaussian-divergence] for `C¹` fields of polynomial
growth, and the product rule for `δ_G`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

namespace LSBA

/-- Polynomial growth: `‖f x‖ ≤ C (1 + ‖x‖)^k` for some `C` and `k`. -/
def PolyGrowth {E F : Type*} [Norm E] [Norm F] (f : E → F) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k

/-- The Gaussian divergence `δ_G Y = Σ_i (x_i Y_i - ∂_i Y_i)` of (8.33)
[up:eq:gaussian-divergence] under the standard Gaussian law on `ℝ^ι`; `∂_i Y_i` is the
derivative along the `i`-th coordinate line. -/
def gaussDiv {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : (ι → ℝ) → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, (x i * Y x i - lineDeriv ℝ (fun y => Y y i) x (Pi.single i 1))

/-- Test functions for Gaussian integration by parts: `C¹`, bounded, with polynomially bounded
derivative. -/
def IsIBPTest {ι : Type*} [Fintype ι] (φ : (ι → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 1 φ ∧ (∃ M : ℝ, ∀ x, |φ x| ≤ M) ∧ PolyGrowth (fderiv ℝ φ)

/-- Gaussian integration by parts for the field `Y`, the regularity clause of Lemma 8.11
[up:lem:angular]: `δ_G Y` is measurable and, for every test function `φ`, `D_Y φ` and
`φ δ_G Y` are integrable with `𝔼 D_Y φ = 𝔼[φ δ_G Y]` ((8.33) [up:eq:gaussian-divergence]). -/
def IBPAdmissible {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : (ι → ℝ) → ι → ℝ) : Prop :=
  Measurable (gaussDiv Y) ∧ ∀ φ : (ι → ℝ) → ℝ, IsIBPTest φ →
    Integrable (fun x => fderiv ℝ φ x (Y x)) (stdGauss ι) ∧
    Integrable (fun x => φ x * gaussDiv Y x) (stdGauss ι) ∧
    ∫ x, fderiv ℝ φ x (Y x) ∂(stdGauss ι) = ∫ x, φ x * gaussDiv Y x ∂(stdGauss ι)

/-- (8.33) [up:eq:gaussian-divergence] for `C¹` fields whose values and derivatives grow at
most polynomially. -/
theorem ibpAdmissible_of_contDiff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : (ι → ℝ) → ι → ℝ} (hY : ContDiff ℝ 1 Y) (hb : PolyGrowth Y)
    (hb' : PolyGrowth (fderiv ℝ Y)) : IBPAdmissible Y := by
  obtain ⟨C₁, k₁, hC₁⟩ := hb
  obtain ⟨C₃, k₃, hC₃⟩ := hb'
  -- polynomial moments of the sup norm are finite under the standard Gaussian
  have hpow1 : ∀ m : ℕ, Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 1) := by
    intro m
    have hm : MemLp id (m : ENNReal) (gaussianReal (0 : ℝ) 1) :=
      memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) m (ENNReal.natCast_ne_top m)
    have hm' : MemLp id (m : ℕ) (gaussianReal (0 : ℝ) 1) := by simpa using hm
    have h1 : Integrable (fun x : ℝ => ‖id x‖ ^ m) (gaussianReal 0 1) := hm'.integrable_norm_pow'
    have h2 : Integrable (fun x : ℝ => (2 : ℝ) ^ m * (1 + |x| ^ m)) (gaussianReal 0 1) :=
      ((integrable_const (1 : ℝ)).add (by simpa using h1)).const_mul _
    refine h2.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (by fun_prop : Continuous fun x : ℝ => (1 + |x|) ^ m).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
      have hx : (0 : ℝ) ≤ |x| ^ m := by positivity
      rcases le_total |x| 1 with h | h
      · calc (1 + |x|) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
      · calc (1 + |x|) ^ m ≤ (2 * |x|) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ = 2 ^ m * |x| ^ m := by rw [mul_pow]
          _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
  have hprod : ∀ x : ι → ℝ, 1 + ‖x‖ ≤ ∏ j, (1 + |x j|) := by
    intro x
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
  have hpoly : ∀ m : ℕ, Integrable (fun x : ι → ℝ => (1 + ‖x‖) ^ m) (stdGauss ι) := by
    intro m
    have hp : Integrable (fun x : ι → ℝ => ∏ j, (1 + |x j|) ^ m) (stdGauss ι) :=
      Integrable.fintype_prod (f := fun _ (t : ℝ) => (1 + |t|) ^ m) (fun _ => hpow1 m)
    refine hp.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (by fun_prop : Continuous fun x : ι → ℝ => (1 + ‖x‖) ^ m).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity), Finset.prod_pow]
      exact pow_le_pow_left₀ (by positivity) (hprod x) m
  -- a continuous function of polynomial growth is Gaussian integrable
  have hint : ∀ {g : (ι → ℝ) → ℝ} {C : ℝ} {k : ℕ}, Continuous g →
      (∀ x, |g x| ≤ C * (1 + ‖x‖) ^ k) → Integrable g (stdGauss ι) := by
    intro g C k hg hgb
    refine ((hpoly k).const_mul C).mono' hg.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hgb x
  -- real-valued Stein identity, from the complex-valued one
  have hstein : ∀ (g : (ι → ℝ) → ℝ) {C : ℝ} {k : ℕ}, ContDiff ℝ 1 g →
      (∀ x, |g x| ≤ C * (1 + ‖x‖) ^ k) → (∀ x, ‖fderiv ℝ g x‖ ≤ C * (1 + ‖x‖) ^ k) →
      ∀ i, ∫ x, x i * g x ∂(stdGauss ι) = ∫ x, fderiv ℝ g x (Pi.single i 1) ∂(stdGauss ι) := by
    intro g C k hg hgb hgb' i
    have hF : ContDiff ℝ 1 (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have hFd : ∀ x, fderiv ℝ (fun x => ((g x : ℝ) : ℂ)) x =
        Complex.ofRealCLM.comp (fderiv ℝ g x) := fun x =>
      (Complex.ofRealCLM.hasFDerivAt.comp x ((hg.differentiable one_ne_zero) x).hasFDerivAt).fderiv
    have h := integral_coord_mul_stdGauss (fun x => ((g x : ℝ) : ℂ)) hF (C := C) (k := k)
      (fun x => by simpa using hgb x)
      (fun x => by
        rw [hFd x]
        refine ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans (hgb' x)) fun v => ?_
        rw [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real]
        calc ‖fderiv ℝ g x v‖ ≤ ‖fderiv ℝ g x‖ * ‖v‖ := (fderiv ℝ g x).le_opNorm v
          _ ≤ C * (1 + ‖x‖) ^ k * ‖v‖ := by gcongr; exact hgb' x) i
    simp only [hFd, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
      ← Complex.ofReal_mul, integral_complex_ofReal] at h
    exact_mod_cast h
  -- a linear form on `ℝ^ι` is the sum of its values on the coordinate vectors
  have hexp : ∀ (L : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ), L v = ∑ i, v i * L (Pi.single i 1) := by
    intro L v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : (Pi.single i (v i) : ι → ℝ) = v i • Pi.single i 1 := by
      rw [← Pi.single_smul]; simp
    rw [h, map_smul, smul_eq_mul]
  -- the coordinates of `Y` and their derivatives
  have hYi : ∀ i, ContDiff ℝ 1 (fun y => Y y i) := fun i => contDiff_pi.mp hY i
  have hDY : ∀ i x, fderiv ℝ (fun y => Y y i) x =
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).comp (fderiv ℝ Y x) := by
    intro i x
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).hasFDerivAt.comp x
      ((hY.differentiable one_ne_zero) x).hasFDerivAt).fderiv
  have hDYle : ∀ i x v, |fderiv ℝ (fun y => Y y i) x v| ≤ C₃ * (1 + ‖x‖) ^ k₃ * ‖v‖ := by
    intro i x v
    rw [hDY, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ← Real.norm_eq_abs]
    calc ‖fderiv ℝ Y x v i‖ ≤ ‖fderiv ℝ Y x v‖ := norm_le_pi_norm _ i
      _ ≤ ‖fderiv ℝ Y x‖ * ‖v‖ := (fderiv ℝ Y x).le_opNorm v
      _ ≤ C₃ * (1 + ‖x‖) ^ k₃ * ‖v‖ := by gcongr; exact hC₃ x
  have hYle : ∀ i x, |Y x i| ≤ C₁ * (1 + ‖x‖) ^ k₁ := by
    intro i x
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (Y x) i).trans (hC₁ x)
  have hei : ∀ i : ι, ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ ≤ 1 := by
    intro i
    rw [Pi.norm_single]; simp
  have hC₁0 : 0 ≤ C₁ := by simpa using (norm_nonneg _).trans (hC₁ 0)
  have hC₃0 : 0 ≤ C₃ := by simpa using (norm_nonneg _).trans (hC₃ 0)
  have hDYi : ∀ i x, |fderiv ℝ (fun y => Y y i) x (Pi.single i 1)| ≤ C₃ * (1 + ‖x‖) ^ k₃ := by
    intro i x
    calc |fderiv ℝ (fun y => Y y i) x (Pi.single i 1)|
        ≤ C₃ * (1 + ‖x‖) ^ k₃ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ := hDYle i x _
      _ ≤ C₃ * (1 + ‖x‖) ^ k₃ * 1 := by gcongr; exact hei i
      _ = C₃ * (1 + ‖x‖) ^ k₃ := mul_one _
  have hYc : ∀ i, Continuous fun x => Y x i := fun i => (continuous_apply i).comp hY.continuous
  have hDc : ∀ i, Continuous fun x => fderiv ℝ (fun y => Y y i) x (Pi.single i 1) := fun i =>
    ((hYi i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- for a `C¹` field the line derivatives are the partial derivatives
  have hgd : ∀ x, gaussDiv Y x =
      ∑ i, (x i * Y x i - fderiv ℝ (fun y => Y y i) x (Pi.single i 1)) := by
    intro x
    unfold gaussDiv
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [((hYi i).differentiable one_ne_zero x).lineDeriv_eq_fderiv]
  unfold IBPAdmissible
  refine ⟨?_, fun φ hφt => ?_⟩
  · have hc : Continuous (gaussDiv Y) := by
      rw [show gaussDiv Y = fun x => ∑ i, (x i * Y x i -
        fderiv ℝ (fun y => Y y i) x (Pi.single i 1)) from funext hgd]
      exact continuous_finsetSum _ fun i _ => ((continuous_apply i).mul (hYc i)).sub (hDc i)
    exact hc.measurable
  obtain ⟨hφ, ⟨M, hM⟩, ⟨C₂, k₂, hC₂⟩⟩ := hφt
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hC₂0 : 0 ≤ C₂ := by simpa using (norm_nonneg _).trans (hC₂ 0)
  have hφc : Continuous φ := hφ.continuous
  have hφd : ∀ x, HasFDerivAt φ (fderiv ℝ φ x) x := fun x =>
    ((hφ.differentiable one_ne_zero) x).hasFDerivAt
  have hDφc : Continuous fun x => fderiv ℝ φ x := hφ.continuous_fderiv one_ne_zero
  have hDφle : ∀ x v, |fderiv ℝ φ x v| ≤ C₂ * (1 + ‖x‖) ^ k₂ * ‖v‖ := by
    intro x v
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ φ x v‖ ≤ ‖fderiv ℝ φ x‖ * ‖v‖ := (fderiv ℝ φ x).le_opNorm v
      _ ≤ C₂ * (1 + ‖x‖) ^ k₂ * ‖v‖ := by gcongr; exact hC₂ x
  -- the product `φ Y_i`
  have hg_cd : ∀ i, ContDiff ℝ 1 (fun x => φ x * Y x i) := fun i => hφ.mul (hYi i)
  have hg_fd : ∀ i x v, fderiv ℝ (fun y => φ y * Y y i) x v =
      φ x * fderiv ℝ (fun y => Y y i) x v + Y x i * fderiv ℝ φ x v := by
    intro i x v
    have h : HasFDerivAt (fun y => φ y * Y y i)
        (φ x • fderiv ℝ (fun y => Y y i) x + Y x i • fderiv ℝ φ x) x :=
      (hφd x).mul (((hYi i).differentiable one_ne_zero x).hasFDerivAt)
    rw [h.fderiv]
    simp [smul_eq_mul]
  -- common polynomial bound for `φ Y_i` and its derivative
  obtain ⟨K, hK3, hK12⟩ : ∃ K : ℕ, k₃ ≤ K ∧ k₁ + k₂ ≤ K := ⟨max (k₁ + k₂) k₃, le_max_right _ _,
    le_max_left _ _⟩
  have hs : ∀ x : ι → ℝ, 1 ≤ 1 + ‖x‖ := fun x => by linarith [norm_nonneg x]
  have hg_le : ∀ i x, |φ x * Y x i| ≤
      (M * C₁ + M * C₃ + C₁ * C₂) * (1 + ‖x‖) ^ K := by
    intro i x
    have hk1 : (1 + ‖x‖) ^ k₁ ≤ (1 + ‖x‖) ^ K :=
      pow_le_pow_right₀ (hs x) (le_trans (Nat.le_add_right _ _) hK12)
    have hp : (0 : ℝ) ≤ (1 + ‖x‖) ^ K := by positivity
    calc |φ x * Y x i| = |φ x| * |Y x i| := abs_mul _ _
      _ ≤ M * (C₁ * (1 + ‖x‖) ^ k₁) := mul_le_mul (hM x) (hYle i x) (abs_nonneg _) hM0
      _ ≤ M * (C₁ * (1 + ‖x‖) ^ K) := by gcongr
      _ ≤ (M * C₁ + M * C₃ + C₁ * C₂) * (1 + ‖x‖) ^ K := by
          nlinarith [mul_nonneg hM0 hC₃0, mul_nonneg hC₁0 hC₂0, mul_nonneg hM0 hC₁0]
  have hg_le' : ∀ i x, ‖fderiv ℝ (fun y => φ y * Y y i) x‖ ≤
      (M * C₁ + M * C₃ + C₁ * C₂) * (1 + ‖x‖) ^ K := by
    intro i x
    have hk3 : (1 + ‖x‖) ^ k₃ ≤ (1 + ‖x‖) ^ K := pow_le_pow_right₀ (hs x) hK3
    have hk12 : (1 + ‖x‖) ^ k₁ * (1 + ‖x‖) ^ k₂ ≤ (1 + ‖x‖) ^ K := by
      rw [← pow_add]; exact pow_le_pow_right₀ (hs x) hK12
    have hp : (0 : ℝ) ≤ (1 + ‖x‖) ^ K := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hg_fd, Real.norm_eq_abs]
    have hv : 0 ≤ ‖v‖ := norm_nonneg v
    have ha := mul_le_mul (hM x) (hDYle i x v) (abs_nonneg _) hM0
    have hb := mul_le_mul (hYle i x) (hDφle x v) (abs_nonneg _)
      (mul_nonneg hC₁0 (by positivity))
    have e1 : M * (C₃ * (1 + ‖x‖) ^ k₃ * ‖v‖) ≤ M * (C₃ * (1 + ‖x‖) ^ K * ‖v‖) := by gcongr
    have e2 : C₁ * (1 + ‖x‖) ^ k₁ * (C₂ * (1 + ‖x‖) ^ k₂ * ‖v‖) ≤
        C₁ * C₂ * (1 + ‖x‖) ^ K * ‖v‖ := by
      have : C₁ * (1 + ‖x‖) ^ k₁ * (C₂ * (1 + ‖x‖) ^ k₂ * ‖v‖) =
          C₁ * C₂ * ((1 + ‖x‖) ^ k₁ * (1 + ‖x‖) ^ k₂) * ‖v‖ := by ring
      rw [this]
      gcongr
    have e3 : 0 ≤ M * C₁ * (1 + ‖x‖) ^ K * ‖v‖ := by positivity
    calc |φ x * fderiv ℝ (fun y => Y y i) x v + Y x i * fderiv ℝ φ x v|
        ≤ |φ x * fderiv ℝ (fun y => Y y i) x v| + |Y x i * fderiv ℝ φ x v| := abs_add_le _ _
      _ = |φ x| * |fderiv ℝ (fun y => Y y i) x v| + |Y x i| * |fderiv ℝ φ x v| := by
          rw [abs_mul, abs_mul]
      _ ≤ (M * C₁ + M * C₃ + C₁ * C₂) * (1 + ‖x‖) ^ K * ‖v‖ := by nlinarith
  -- Stein for `φ Y_i`
  have hS : ∀ i, ∫ x, x i * (φ x * Y x i) ∂(stdGauss ι) =
      ∫ x, (φ x * fderiv ℝ (fun y => Y y i) x (Pi.single i 1) +
        Y x i * fderiv ℝ φ x (Pi.single i 1)) ∂(stdGauss ι) := by
    intro i
    have h := hstein _ (hg_cd i) (hg_le i) (hg_le' i) i
    simpa only [hg_fd] using h
  -- integrability of the three kinds of terms
  have hI1 : ∀ i, Integrable (fun x => x i * (φ x * Y x i)) (stdGauss ι) := by
    intro i
    refine hint (C := M * C₁ + M * C₃ + C₁ * C₂) (k := K + 1)
      ((continuous_apply i).mul (hφc.mul (hYc i))) fun x => ?_
    have hxi : |x i| ≤ 1 + ‖x‖ := by
      have := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at this
      linarith
    calc |x i * (φ x * Y x i)| = |x i| * |φ x * Y x i| := abs_mul _ _
      _ ≤ (1 + ‖x‖) * ((M * C₁ + M * C₃ + C₁ * C₂) * (1 + ‖x‖) ^ K) :=
          mul_le_mul hxi (hg_le i x) (abs_nonneg _) (by linarith [hs x])
      _ = (M * C₁ + M * C₃ + C₁ * C₂) * (1 + ‖x‖) ^ (K + 1) := by ring
  have hI2 : ∀ i, Integrable
      (fun x => φ x * fderiv ℝ (fun y => Y y i) x (Pi.single i 1)) (stdGauss ι) := by
    intro i
    refine hint (C := M * C₃) (k := k₃) (hφc.mul (hDc i)) fun x => ?_
    calc |φ x * fderiv ℝ (fun y => Y y i) x (Pi.single i 1)|
        = |φ x| * |fderiv ℝ (fun y => Y y i) x (Pi.single i 1)| := abs_mul _ _
      _ ≤ M * (C₃ * (1 + ‖x‖) ^ k₃) := mul_le_mul (hM x) (hDYi i x) (abs_nonneg _) hM0
      _ = M * C₃ * (1 + ‖x‖) ^ k₃ := by ring
  have hI3 : ∀ i, Integrable (fun x => Y x i * fderiv ℝ φ x (Pi.single i 1)) (stdGauss ι) := by
    intro i
    refine hint (C := C₁ * C₂) (k := k₁ + k₂)
      ((hYc i).mul (hDφc.clm_apply continuous_const)) fun x => ?_
    have hd : |fderiv ℝ φ x (Pi.single i 1)| ≤ C₂ * (1 + ‖x‖) ^ k₂ :=
      calc |fderiv ℝ φ x (Pi.single i 1)|
          ≤ C₂ * (1 + ‖x‖) ^ k₂ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ := hDφle x _
        _ ≤ C₂ * (1 + ‖x‖) ^ k₂ * 1 := by gcongr; exact hei i
        _ = C₂ * (1 + ‖x‖) ^ k₂ := mul_one _
    calc |Y x i * fderiv ℝ φ x (Pi.single i 1)| = |Y x i| * |fderiv ℝ φ x (Pi.single i 1)| :=
          abs_mul _ _
      _ ≤ (C₁ * (1 + ‖x‖) ^ k₁) * (C₂ * (1 + ‖x‖) ^ k₂) :=
          mul_le_mul (hYle i x) hd (abs_nonneg _) (mul_nonneg hC₁0 (by positivity))
      _ = C₁ * C₂ * (1 + ‖x‖) ^ (k₁ + k₂) := by ring
  -- the two integrands as finite sums
  have hsum_l : (fun x => fderiv ℝ φ x (Y x)) =
      fun x => ∑ i, Y x i * fderiv ℝ φ x (Pi.single i 1) := funext fun x => hexp _ _
  have hsum_r : (fun x => φ x * gaussDiv Y x) = fun x => ∑ i, (x i * (φ x * Y x i) -
      φ x * fderiv ℝ (fun y => Y y i) x (Pi.single i 1)) := by
    funext x
    rw [hgd x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hI4 : ∀ i, Integrable (fun x => x i * (φ x * Y x i) -
      φ x * fderiv ℝ (fun y => Y y i) x (Pi.single i 1)) (stdGauss ι) := fun i =>
    (hI1 i).sub (hI2 i)
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum_l]
    exact integrable_finsetSum _ fun i _ => hI3 i
  · rw [hsum_r]
    exact integrable_finsetSum _ fun i _ => hI4 i
  · rw [hsum_l, hsum_r, integral_finsetSum _ fun i _ => hI3 i,
      integral_finsetSum _ fun i _ => hI4 i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_sub (hI1 i) (hI2 i), hS i, integral_add (hI2 i) (hI3 i)]
    ring

/-- The product rule `δ_G (f Y) = f δ_G Y - D_Y f`. -/
theorem gaussDiv_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    {Y : (ι → ℝ) → ι → ℝ} {x : ι → ℝ} (hf : DifferentiableAt ℝ f x)
    (hY : ∀ i, LineDifferentiableAt ℝ (fun y => Y y i) x (Pi.single i 1)) :
    gaussDiv (fun y => f y • Y y) x = f x * gaussDiv Y x - fderiv ℝ f x (Y x) := by
  -- a linear form on `ℝ^ι` is the sum of its values on the coordinate vectors
  have hexp : ∀ (L : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ), L v = ∑ i, v i * L (Pi.single i 1) := by
    intro L v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : (Pi.single i (v i) : ι → ℝ) = v i • Pi.single i 1 := by
      rw [← Pi.single_smul]; simp
    rw [h, map_smul, smul_eq_mul]
  -- the product rule along the `i`-th coordinate line
  have hline : ∀ i, lineDeriv ℝ (fun y => f y * Y y i) x (Pi.single i 1) =
      fderiv ℝ f x (Pi.single i 1) * Y x i +
        f x * lineDeriv ℝ (fun y => Y y i) x (Pi.single i 1) := by
    intro i
    have h1 : HasLineDerivAt ℝ f (fderiv ℝ f x (Pi.single i 1)) x (Pi.single i 1) :=
      hf.hasFDerivAt.hasLineDerivAt _
    have h2 := (hY i).hasLineDerivAt
    unfold HasLineDerivAt at h1 h2
    have h3 := h1.mul h2
    simp only [zero_smul, add_zero] at h3
    exact h3.deriv
  unfold gaussDiv
  simp only [Pi.smul_apply, smul_eq_mul, hline]
  rw [hexp (fderiv ℝ f x) (Y x), Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end LSBA
