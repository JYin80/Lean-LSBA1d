import LSBA.Gauss.ComplexAnnulus
import LSBA.Gauss.QuadCharFun

/-!
# Small-ball bound for a weighted sum of shifted complex Gaussian moduli

For independent standard complex Gaussians `γ_j`, shifts `b_j` and real weights `E_j`, the sum
`Y = ∑ E_j |γ_j + b_j|²` satisfies `P(|Y - a| ≤ ε) ≤ C ε / ν` with
`ν² = ∑ E_j² (1 + |b_j|²)`: first when no index carries more than half of `ν²` (Fourier bound and
Hölder's inequality), then in general (one dominant index, by conditioning). In the complex case
this is used in place of [APSSS, Claim 6.2] and the contour argument of [APSSS, Section 6].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### One factor: the `L^p` norm of `|φ_β|` -/

/-- Pointwise bound for `p ≥ 2`, with `u = η²` and `B = |β|²`:
`((1 + u)^{-1/2} e^{-uB/(1+u)})^p ≤ e^{-p(1+B)u/4} + (3/p) e^{-pB/2} (1 + u)⁻¹`. -/
private lemma quadSmallBall_rpow_le {B u p : ℝ} (hB : 0 ≤ B) (hu : 0 ≤ u) (hp : 2 ≤ p) :
    ((1 + u) ^ (-(1 / 2 : ℝ)) * Real.exp (-(u * B / (1 + u)))) ^ p ≤
      Real.exp (-(p * (1 + B) / 4) * u) + 3 / p * Real.exp (-(p * B / 2)) * (1 + u)⁻¹ := by
  have h1u : 0 < 1 + u := by linarith
  have hp0 : 0 < p := by linarith
  have hlhs : ((1 + u) ^ (-(1 / 2 : ℝ)) * Real.exp (-(u * B / (1 + u)))) ^ p =
      Real.exp (Real.log (1 + u) * (-(1 / 2) * p) + -(u * B / (1 + u)) * p) := by
    rw [Real.mul_rpow (Real.rpow_nonneg h1u.le _) (Real.exp_pos _).le, ← Real.rpow_mul h1u.le,
      Real.rpow_def_of_pos h1u, ← Real.exp_mul, ← Real.exp_add]
  rw [hlhs]
  have hT : 0 ≤ 3 / p * Real.exp (-(p * B / 2)) * (1 + u)⁻¹ := by positivity
  rcases le_or_gt u 1 with hu1 | hu1
  · have hlog : u / 2 ≤ Real.log (1 + u) := by
      have h := Real.one_sub_inv_le_log_of_pos h1u
      have h' : u / 2 ≤ 1 - (1 + u)⁻¹ := by
        rw [show 1 - (1 + u)⁻¹ = u / (1 + u) by field_simp; ring,
          div_le_div_iff₀ (by norm_num) h1u]
        nlinarith
      linarith
    have hfrac : u * B / 2 ≤ u * B / (1 + u) :=
      div_le_div_of_nonneg_left (by positivity) h1u (by linarith)
    have hexp : Real.log (1 + u) * (-(1 / 2) * p) + -(u * B / (1 + u)) * p ≤
        -(p * (1 + B) / 4) * u := by
      nlinarith [mul_le_mul_of_nonneg_left hlog hp0.le, mul_le_mul_of_nonneg_left hfrac hp0.le,
        mul_nonneg hp0.le (mul_nonneg hu hB)]
    exact (Real.exp_le_exp.mpr hexp).trans (le_add_of_nonneg_right hT)
  · set L := Real.log (1 + u) with hL
    have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    have h2 := Real.log_two_gt_d9
    have hpow : Real.exp (-((p - 2) / 2 * L)) ≤ 3 / p := by
      have hexp := Real.add_one_le_exp ((p - 2) / 2 * L)
      have hge : p / 3 ≤ Real.exp ((p - 2) / 2 * L) := by
        nlinarith [mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ p - 2 by linarith)]
      rw [Real.exp_neg, show 3 / p = (p / 3)⁻¹ by field_simp]
      exact inv_anti₀ (by positivity) hge
    have hB2 : B / 2 ≤ u * B / (1 + u) := by
      rw [div_le_div_iff₀ (by norm_num) h1u]; nlinarith
    have hsplit : L * (-(1 / 2) * p) + -(u * B / (1 + u)) * p =
        -L + -((p - 2) / 2 * L) + -(u * B / (1 + u)) * p := by ring
    rw [hsplit, Real.exp_add, Real.exp_add, Real.exp_neg L, hL, Real.exp_log h1u]
    have h3 : Real.exp (-(u * B / (1 + u)) * p) ≤ Real.exp (-(p * B / 2)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hB2 hp0.le])
    have hinv : 0 ≤ (1 + u)⁻¹ := by positivity
    calc (1 + u)⁻¹ * Real.exp (-((p - 2) / 2 * Real.log (1 + u))) *
          Real.exp (-(u * B / (1 + u)) * p)
        ≤ (1 + u)⁻¹ * (3 / p) * Real.exp (-(p * B / 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow hinv) h3 (Real.exp_pos _).le
            (by positivity)
      _ = 3 / p * Real.exp (-(p * B / 2)) * (1 + u)⁻¹ := by ring
      _ ≤ _ := le_add_of_nonneg_left (Real.exp_pos _).le

/-- `∫ |φ_β(e ξ)|^p dξ ≤ 14 / √(p e² (1 + |β|²))` for `e ≠ 0` and `p ≥ 2`, where `φ_β` is the
characteristic function of `|γ + β|²`. -/
private lemma quadSmallBall_lintegral_le (β : ℂ) {e p : ℝ} (he : e ≠ 0) (hp : 2 ≤ p) :
    ∫⁻ ξ, ‖charFun (cGauss.map fun z => ‖z + β‖ ^ 2) (e * ξ)‖ₑ ^ p ≤
      ENNReal.ofReal (14 / Real.sqrt (p * (e ^ 2 * (1 + ‖β‖ ^ 2)))) := by
  set B := ‖β‖ ^ 2 with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hp0 : 0 < p := by linarith
  set c := 3 / p * Real.exp (-(p * B / 2)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hb : 0 < p * (1 + B) * e ^ 2 / 4 := by positivity
  set g : ℝ → ℝ := fun ξ =>
    Real.exp (-(p * (1 + B) * e ^ 2 / 4) * ξ ^ 2) + c * (1 + (e * ξ) ^ 2)⁻¹ with hg
  have hgi₁ := integrable_exp_neg_mul_sq hb
  have hgi₂ := (integrable_inv_one_add_mul_sq he).const_mul c
  have hgi : Integrable g := hgi₁.add hgi₂
  have hg0 : ∀ ξ, 0 ≤ g ξ := fun ξ => by simp only [hg]; positivity
  have hpt : ∀ ξ, ‖charFun (cGauss.map fun z => ‖z + β‖ ^ 2) (e * ξ)‖ₑ ^ p ≤
      ENNReal.ofReal (g ξ) := by
    intro ξ
    rw [← ofReal_norm, norm_charFun_normSq_cGauss,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le]
    refine ENNReal.ofReal_le_ofReal ((quadSmallBall_rpow_le hB0 (sq_nonneg (e * ξ)) hp).trans
      (le_of_eq ?_))
    simp only [hg, hc]
    congr 2
    ring
  have hN : 0 < p * (e ^ 2 * (1 + B)) := by positivity
  have hs : 0 < Real.sqrt (p * (e ^ 2 * (1 + B))) := Real.sqrt_pos.mpr hN
  have hint : ∫ ξ, g ξ = Real.sqrt (π / (p * (1 + B) * e ^ 2 / 4)) + c * (π / |e|) := by
    simp only [hg]
    rw [integral_add hgi₁ hgi₂, integral_gaussian, integral_const_mul,
      integral_univ_inv_one_add_mul_sq]
  -- the Gaussian part
  have hI₁ : Real.sqrt (π / (p * (1 + B) * e ^ 2 / 4)) ≤
      4 / Real.sqrt (p * (e ^ 2 * (1 + B))) := by
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h1 : Real.sqrt (π / (p * (1 + B) * e ^ 2 / 4)) ≤
        Real.sqrt (16 / (p * (e ^ 2 * (1 + B)))) := by
      apply Real.sqrt_le_sqrt
      rw [show π / (p * (1 + B) * e ^ 2 / 4) = 4 * π / (p * (e ^ 2 * (1 + B))) by
        field_simp]
      exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_le_four]) hN.le
    rwa [Real.sqrt_div' _ hN.le, h16] at h1
  -- the tail part
  have hI₂ : c * (π / |e|) ≤ 10 / Real.sqrt (p * (e ^ 2 * (1 + B))) := by
    have he0 : 0 < |e| := abs_pos.mpr he
    have hsq : Real.sqrt (p * (e ^ 2 * (1 + B))) =
        Real.sqrt p * (|e| * Real.sqrt (1 + B)) := by
      rw [Real.sqrt_mul hp0.le, Real.sqrt_mul (sq_nonneg e), Real.sqrt_sq_eq_abs]
    have hsp : Real.sqrt p ≤ p := by
      nlinarith [Real.sq_sqrt hp0.le, Real.sqrt_nonneg p]
    have hsB : Real.sqrt (1 + B) ≤ 1 + B := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 + B by positivity), Real.sqrt_nonneg (1 + B)]
    have hX : Real.exp (-(p * B / 2)) * (1 + B) ≤ 1 := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one]
      nlinarith [Real.add_one_le_exp (p * B / 2), mul_le_mul_of_nonneg_right
        (show (2 : ℝ) ≤ p from hp) hB0]
    have hX0 : 0 ≤ Real.exp (-(p * B / 2)) := (Real.exp_pos _).le
    have hXs : Real.exp (-(p * B / 2)) * Real.sqrt (1 + B) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hsB hX0).trans hX
    have hpi := Real.pi_lt_d2
    have hsB0 := Real.sqrt_nonneg (1 + B)
    have hsp0 := Real.sqrt_nonneg p
    rw [hsq, hc, le_div_iff₀ (by positivity)]
    have key : 3 * π * (Real.exp (-(p * B / 2)) * Real.sqrt (1 + B)) * Real.sqrt p ≤ 10 * p := by
      have h1 : 3 * π * (Real.exp (-(p * B / 2)) * Real.sqrt (1 + B)) ≤ 3 * π :=
        by nlinarith [Real.pi_pos]
      have h2 : 3 * π * (Real.exp (-(p * B / 2)) * Real.sqrt (1 + B)) * Real.sqrt p ≤
          3 * π * p :=
        mul_le_mul h1 hsp hsp0 (by positivity)
      nlinarith [Real.pi_pos]
    calc 3 / p * Real.exp (-(p * B / 2)) * (π / |e|) *
          (Real.sqrt p * (|e| * Real.sqrt (1 + B)))
        = (3 * π * (Real.exp (-(p * B / 2)) * Real.sqrt (1 + B)) * Real.sqrt p) / p := by
          field_simp
      _ ≤ 10 * p / p := div_le_div_of_nonneg_right key hp0.le
      _ = 10 := by field_simp
  calc ∫⁻ ξ, ‖charFun (cGauss.map fun z => ‖z + β‖ ^ 2) (e * ξ)‖ₑ ^ p
      ≤ ∫⁻ ξ, ENNReal.ofReal (g ξ) := lintegral_mono hpt
    _ = ENNReal.ofReal (∫ ξ, g ξ) :=
      (ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)).symm
    _ ≤ ENNReal.ofReal (14 / Real.sqrt (p * (e ^ 2 * (1 + B)))) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hint]
      calc _ ≤ 4 / Real.sqrt (p * (e ^ 2 * (1 + B))) +
            10 / Real.sqrt (p * (e ^ 2 * (1 + B))) := add_le_add hI₁ hI₂
        _ = _ := by ring

/-! ### The characteristic function of the weighted sum -/

/-- The characteristic function of `Y = ∑ E_j |x_j + b_j|²` under `stdCGauss ι` is the product
`∏ φ_{b_j}(E_j ξ)`. -/
private lemma quadSmallBall_charFun_eq {ι : Type*} [Fintype ι] (E : ι → ℝ) (b : ι → ℂ)
    (ξ : ℝ) :
    charFun ((stdCGauss ι).map fun x => ∑ j, E j * ‖x j + b j‖ ^ 2) ξ =
      ∏ j, charFun (cGauss.map fun z => ‖z + b j‖ ^ 2) (E j * ξ) := by
  have hY : Measurable fun x : ι → ℂ => ∑ j, E j * ‖x j + b j‖ ^ 2 :=
    (continuous_finsetSum _ fun j _ => by fun_prop).measurable
  rw [charFun_apply_real, integral_map hY.aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop))]
  have hfac : ∀ j, charFun (cGauss.map fun z => ‖z + b j‖ ^ 2) (E j * ξ) =
      ∫ z, Complex.exp (((E j * ξ : ℝ) : ℂ) * ((‖z + b j‖ ^ 2 : ℝ) : ℂ) * Complex.I)
        ∂cGauss := by
    intro j
    rw [charFun_apply_real, integral_map (by fun_prop)
      (Continuous.aestronglyMeasurable (by fun_prop))]
  simp_rw [hfac]
  unfold stdCGauss
  rw [← integral_fintype_prod_eq_prod (fun j z =>
    Complex.exp (((E j * ξ : ℝ) : ℂ) * ((‖z + b j‖ ^ 2 : ℝ) : ℂ) * Complex.I))]
  congr 1
  ext x
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### The spread case -/

/-- The spread case with the constant `14 C₅`, for a constant `C₅` of the Fourier small-ball
bound. -/
private lemma quadSmallBall_spread {C₅ : ℝ} (hC₅ : 0 < C₅)
    (h₅ : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (a ε : ℝ), 0 < ε →
      ν (Set.Icc (a - ε) (a + ε)) ≤ ENNReal.ofReal (C₅ * ε) * ∫⁻ ξ, ‖charFun ν ξ‖ₑ)
    {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ) (b : ι → ℂ) (a ε : ℝ) (hε : 0 < ε)
    (hE : ∀ j, E j ≠ 0)
    (hsp : ∀ j, E j ^ 2 * (1 + ‖b j‖ ^ 2) ≤ (∑ k, E k ^ 2 * (1 + ‖b k‖ ^ 2)) / 2) :
    stdCGauss ι {x | |∑ j, E j * ‖x j + b j‖ ^ 2 - a| ≤ ε} ≤
      ENNReal.ofReal (C₅ * 14 * ε / Real.sqrt (∑ k, E k ^ 2 * (1 + ‖b k‖ ^ 2))) := by
  set ν2 := ∑ k, E k ^ 2 * (1 + ‖b k‖ ^ 2) with hν2
  have hw0 : ∀ k, 0 < E k ^ 2 * (1 + ‖b k‖ ^ 2) := fun k => by
    have := hE k; positivity
  have hν0 : 0 < ν2 := Finset.sum_pos (fun k _ => hw0 k) Finset.univ_nonempty
  have hY : Measurable fun x : ι → ℂ => ∑ j, E j * ‖x j + b j‖ ^ 2 :=
    (continuous_finsetSum _ fun j _ => by fun_prop).measurable
  have hset : {x : ι → ℂ | |∑ j, E j * ‖x j + b j‖ ^ 2 - a| ≤ ε} =
      (fun x : ι → ℂ => ∑ j, E j * ‖x j + b j‖ ^ 2) ⁻¹' Set.Icc (a - ε) (a + ε) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, abs_sub_le_iff]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hset, ← Measure.map_apply hY measurableSet_Icc]
  refine (h₅ _ a ε hε).trans ?_
  -- Hölder with exponents `α_j = w_j / ν²`
  set α : ι → ℝ := fun j => E j ^ 2 * (1 + ‖b j‖ ^ 2) / ν2 with hα
  set p : ι → ℝ := fun j => ν2 / (E j ^ 2 * (1 + ‖b j‖ ^ 2)) with hp
  have hpα : ∀ j, p j * α j = 1 := fun j => by
    simp only [hp, hα]; field_simp [(hw0 j).ne', hE j]
  have hα1 : ∑ j, α j = 1 := by
    simp only [hα]; rw [← Finset.sum_div, ← hν2, div_self hν0.ne']
  have hα0 : ∀ j ∈ Finset.univ, 0 ≤ α j := fun j _ => by
    simp only [hα]; exact div_nonneg (hw0 j).le hν0.le
  have hp2 : ∀ j, 2 ≤ p j := fun j => by
    simp only [hp]; rw [le_div_iff₀ (hw0 j)]; linarith [hsp j]
  have hcf : ∀ ξ, ‖charFun ((stdCGauss ι).map fun x : ι → ℂ => ∑ j, E j * ‖x j + b j‖ ^ 2)
      ξ‖ₑ = ∏ j, (‖charFun (cGauss.map fun z => ‖z + b j‖ ^ 2) (E j * ξ)‖ₑ ^ p j) ^ α j := by
    intro ξ
    rw [quadSmallBall_charFun_eq, enorm_eq_nnnorm, nnnorm_prod, ENNReal.ofNNReal_finsetProd]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← ENNReal.rpow_mul, hpα j, ENNReal.rpow_one, enorm_eq_nnnorm]
  have hmeas : ∀ j ∈ Finset.univ, AEMeasurable
      (fun ξ => ‖charFun (cGauss.map fun z => ‖z + b j‖ ^ 2) (E j * ξ)‖ₑ ^ p j) := by
    intro j _
    exact ((continuous_charFun.comp (continuous_const.mul continuous_id)).enorm.measurable.pow_const
      _).aemeasurable
  have hfac : ∀ j ∈ Finset.univ,
      ∫⁻ ξ, ‖charFun (cGauss.map fun z => ‖z + b j‖ ^ 2) (E j * ξ)‖ₑ ^ p j ≤
        ENNReal.ofReal (14 / Real.sqrt ν2) := by
    intro j _
    refine (quadSmallBall_lintegral_le (b j) (hE j) (hp2 j)).trans (le_of_eq ?_)
    congr 3
    simp only [hp]; field_simp [(hw0 j).ne', hE j]
  have hr : 0 < 14 / Real.sqrt ν2 := div_pos (by norm_num) (Real.sqrt_pos.mpr hν0)
  have hint : ∫⁻ ξ, ‖charFun ((stdCGauss ι).map fun x : ι → ℂ =>
      ∑ j, E j * ‖x j + b j‖ ^ 2) ξ‖ₑ ≤ ENNReal.ofReal (14 / Real.sqrt ν2) := by
    simp_rw [hcf]
    calc ∫⁻ ξ, ∏ j, (‖charFun (cGauss.map fun z => ‖z + b j‖ ^ 2) (E j * ξ)‖ₑ ^ p j) ^ α j
        ≤ ∏ j, (∫⁻ ξ, ‖charFun (cGauss.map fun z => ‖z + b j‖ ^ 2) (E j * ξ)‖ₑ ^ p j) ^ α j :=
          ENNReal.lintegral_prod_norm_pow_le Finset.univ hmeas hα1 hα0
      _ ≤ ∏ j, ENNReal.ofReal (14 / Real.sqrt ν2) ^ α j :=
          Finset.prod_le_prod fun j hj => ENNReal.rpow_le_rpow (hfac j hj) (hα0 j hj)
      _ = ENNReal.ofReal (14 / Real.sqrt ν2) := by
          simp_rw [ENNReal.ofReal_rpow_of_pos hr]
          rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => by positivity),
            ← Real.rpow_sum_of_pos hr, hα1, Real.rpow_one]
  calc ENNReal.ofReal (C₅ * ε) * ∫⁻ ξ, ‖charFun ((stdCGauss ι).map fun x : ι → ℂ =>
        ∑ j, E j * ‖x j + b j‖ ^ 2) ξ‖ₑ
      ≤ ENNReal.ofReal (C₅ * ε) * ENNReal.ofReal (14 / Real.sqrt ν2) := by gcongr
    _ = ENNReal.ofReal (C₅ * 14 * ε / Real.sqrt ν2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-! ### Conditioning on all coordinates but some -/

/-- If, for every value of the other coordinates, the conditional probability of `S` given the
coordinates outside `s` is at most `c`, then `P(S) ≤ c`. -/
private lemma quadSmallBall_le_of_lmarginal_le {ι : Type*} [Fintype ι] (s : Finset ι)
    {S : Set (ι → ℂ)} (hS : MeasurableSet S) {c : ℝ≥0∞}
    (h : ∀ x, (∫⋯∫⁻_s, S.indicator 1 ∂fun _ : ι => cGauss) x ≤ c) : stdCGauss ι S ≤ c := by
  have hconst : (∫⋯∫⁻_s, (fun _ => c) ∂fun _ : ι => cGauss) = fun _ => c := by
    ext x
    simp [lmarginal]
  calc stdCGauss ι S = ∫⁻ x, S.indicator 1 x ∂stdCGauss ι := (lintegral_indicator_one hS).symm
    _ ≤ ∫⁻ _, c ∂stdCGauss ι := by
      unfold stdCGauss
      exact lintegral_le_of_lmarginal_le s (measurable_one.indicator hS) measurable_const
        (by rw [hconst]; exact h)
    _ = c := by simp

/-! ### The general case -/

/-- The general case with the constant `3 C₂ + 14 C₅`, for constants `C₂` of the annulus bound
and `C₅` of the Fourier small-ball bound. -/
private lemma quadSmallBall_general {C₂ C₅ : ℝ} (hC₂ : 0 < C₂) (hC₅ : 0 < C₅)
    (h₂ : ∀ (β : ℂ) (c δ : ℝ), 0 < δ →
      cGauss {z | ‖z + β‖ ^ 2 ∈ Set.Icc c (c + δ)} ≤ ENNReal.ofReal (C₂ * δ / (1 + ‖β‖)))
    (h₅ : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (a ε : ℝ), 0 < ε →
      ν (Set.Icc (a - ε) (a + ε)) ≤ ENNReal.ofReal (C₅ * ε) * ∫⁻ ξ, ‖charFun ν ξ‖ₑ)
    {ι : Type*} [Fintype ι] (E : ι → ℝ) (b : ι → ℂ) (a ε : ℝ) (hε : 0 < ε)
    (hE : ∃ j, E j ≠ 0) :
    stdCGauss ι {x | |∑ j, E j * ‖x j + b j‖ ^ 2 - a| ≤ ε} ≤
      ENNReal.ofReal ((3 * C₂ + C₅ * 14) * ε /
        Real.sqrt (∑ k, E k ^ 2 * (1 + ‖b k‖ ^ 2))) := by
  obtain ⟨j₀, hj₀⟩ := hE
  set ν2 := ∑ k, E k ^ 2 * (1 + ‖b k‖ ^ 2) with hν2
  have hw0 : ∀ k, 0 ≤ E k ^ 2 * (1 + ‖b k‖ ^ 2) := fun k => by positivity
  have hν0 : 0 < ν2 := by
    have h1 : 0 < E j₀ ^ 2 * (1 + ‖b j₀‖ ^ 2) := by positivity
    exact h1.trans_le (Finset.single_le_sum (fun k _ => hw0 k) (Finset.mem_univ j₀))
  have hsν := Real.sqrt_pos.mpr hν0
  set S := {x : ι → ℂ | |∑ j, E j * ‖x j + b j‖ ^ 2 - a| ≤ ε} with hS
  have hSm : MeasurableSet S :=
    measurableSet_le ((continuous_finsetSum _ fun j _ => by fun_prop).sub
      continuous_const).abs.measurable measurable_const
  by_cases hdom : ∃ j, ν2 / 2 < E j ^ 2 * (1 + ‖b j‖ ^ 2)
  · -- one dominant index: condition on the other coordinates
    obtain ⟨j, hj⟩ := hdom
    have hEj : E j ≠ 0 := by
      rintro h0
      rw [h0] at hj
      simp at hj
      linarith
    have hEa : 0 < |E j| := abs_pos.mpr hEj
    have hδ : 0 < 2 * ε / |E j| := by positivity
    refine quadSmallBall_le_of_lmarginal_le {j} hSm fun x => ?_
    rw [lmarginal_singleton]
    dsimp only
    set R := ∑ i ∈ Finset.univ.erase j, E i * ‖x i + b i‖ ^ 2 with hR
    set m := (a - R) / E j with hm
    have hsub : (fun z => Function.update x j z) ⁻¹' S ⊆
        {z | ‖z + b j‖ ^ 2 ∈ Set.Icc (m - ε / |E j|) (m - ε / |E j| + 2 * ε / |E j|)} := by
      intro z hz
      simp only [Set.mem_preimage, hS, Set.mem_ofPred_eq] at hz
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self] at hz
      have hrest : ∑ i ∈ Finset.univ.erase j, E i * ‖Function.update x j z i + b i‖ ^ 2 = R := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [hrest] at hz
      have heq : E j * ‖z + b j‖ ^ 2 + R - a = E j * (‖z + b j‖ ^ 2 - m) := by
        simp only [hm]; field_simp; ring
      rw [heq, abs_mul, ← le_div_iff₀' hEa, abs_sub_le_iff] at hz
      simp only [Set.mem_ofPred_eq, Set.mem_Icc]
      constructor
      · linarith [hz.2]
      · have : m - ε / |E j| + 2 * ε / |E j| = m + ε / |E j| := by ring
        rw [this]; linarith [hz.1]
    have hind : ∫⁻ z, S.indicator 1 (Function.update x j z) ∂cGauss =
        cGauss ((fun z => Function.update x j z) ⁻¹' S) := by
      rw [← lintegral_indicator_one (measurable_update x hSm)]
      rfl
    rw [hind]
    refine (measure_mono hsub).trans ((h₂ (b j) _ _ hδ).trans (ENNReal.ofReal_le_ofReal ?_))
    -- `2 C₂ ε / (|E_j| (1 + |b_j|)) ≤ 3 C₂ ε / ν`
    have hb0 := norm_nonneg (b j)
    have hsq : Real.sqrt ν2 ≤ 3 / 2 * (|E j| * (1 + ‖b j‖)) := by
      rw [← Real.sqrt_sq (show 0 ≤ 3 / 2 * (|E j| * (1 + ‖b j‖)) by positivity)]
      apply Real.sqrt_le_sqrt
      have hE2 : |E j| ^ 2 = E j ^ 2 := sq_abs _
      nlinarith [sq_nonneg (E j), mul_nonneg (sq_nonneg (E j)) hb0]
    have hpos : 0 < |E j| * (1 + ‖b j‖) := by positivity
    calc C₂ * (2 * ε / |E j|) / (1 + ‖b j‖) = 2 * C₂ * ε / (|E j| * (1 + ‖b j‖)) := by
          field_simp
      _ ≤ 3 * C₂ * ε / Real.sqrt ν2 := by
          rw [div_le_div_iff₀ hpos hsν]
          nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2 * C₂ * ε by positivity)]
      _ ≤ (3 * C₂ + C₅ * 14) * ε / Real.sqrt ν2 := by
          apply div_le_div_of_nonneg_right _ hsν.le
          nlinarith
  · -- spread: restrict to the indices with `E_j ≠ 0`
    push Not at hdom
    set J := Finset.univ.filter fun i => E i ≠ 0 with hJ
    have hj₀J : j₀ ∈ J := by simp [hJ, hj₀]
    have : Nonempty J := ⟨⟨j₀, hj₀J⟩⟩
    have hsumJ : ∀ g : ι → ℝ, (∀ i, E i = 0 → g i = 0) → ∑ i : J, g i = ∑ i, g i := by
      intro g hg
      rw [Finset.sum_coe_sort J g, hJ, Finset.sum_filter_of_ne]
      intro i _ hgi h0
      exact hgi (hg i h0)
    have hνJ : ∑ k : J, E k ^ 2 * (1 + ‖b k‖ ^ 2) = ν2 :=
      hsumJ (fun k => E k ^ 2 * (1 + ‖b k‖ ^ 2)) fun i h0 => by simp [h0]
    have hspJ := quadSmallBall_spread hC₅ h₅ (ι := J) (fun j => E j) (fun j => b j) a ε hε
      (fun j => (Finset.mem_filter.mp j.2).2) (fun j => by rw [hνJ]; exact hdom j)
    rw [hνJ] at hspJ
    refine quadSmallBall_le_of_lmarginal_le J hSm fun x => ?_
    have hset : (fun y : J → ℂ => Function.updateFinset x J y) ⁻¹' S =
        {y : J → ℂ | |∑ j : J, E j * ‖y j + b j‖ ^ 2 - a| ≤ ε} := by
      ext y
      simp only [Set.mem_preimage, hS, Set.mem_ofPred_eq]
      have hsum : ∑ i, E i * ‖Function.updateFinset x J y i + b i‖ ^ 2 =
          ∑ j : J, E j * ‖y j + b j‖ ^ 2 := by
        rw [← hsumJ (fun i => E i * ‖Function.updateFinset x J y i + b i‖ ^ 2)
          fun i h0 => by simp [h0]]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [Function.updateFinset_def, j.2]
      rw [hsum]
    calc (∫⋯∫⁻_J, S.indicator 1 ∂fun _ : ι => cGauss) x
        = stdCGauss J ((fun y : J → ℂ => Function.updateFinset x J y) ⁻¹' S) := by
          rw [← lintegral_indicator_one (measurable_updateFinset hSm)]
          rfl
      _ ≤ ENNReal.ofReal (C₅ * 14 * ε / Real.sqrt ν2) := by rw [hset]; exact hspJ
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          apply div_le_div_of_nonneg_right _ hsν.le
          nlinarith

/-- General case: if some `E_j ≠ 0`, then `P(|∑ E_j |x_j + b_j|² - a| ≤ ε) ≤ C ε / ν`,
`ν² = ∑ E_j² (1 + |b_j|²)`. -/
theorem stdCGauss_abs_quadSum_sub_le : ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type*} [Fintype ι] (E : ι → ℝ) (b : ι → ℂ) (a ε : ℝ), 0 < ε → (∃ j, E j ≠ 0) →
      stdCGauss ι {x | |∑ j, E j * ‖x j + b j‖ ^ 2 - a| ≤ ε} ≤
        ENNReal.ofReal (C * ε / Real.sqrt (∑ k, E k ^ 2 * (1 + ‖b k‖ ^ 2))) := by
  obtain ⟨C₂, hC₂, h₂⟩ := cGauss_normSq_mem_Icc_le
  obtain ⟨C₅, hC₅, h₅⟩ := measure_Icc_le_lintegral_charFun
  refine ⟨3 * C₂ + C₅ * 14, by positivity, ?_⟩
  intro ι _ E b a ε hε hE
  exact quadSmallBall_general hC₂ hC₅ h₂ h₅ E b a ε hε hE

end LSBA
