import LSBA.Gauss.CGauss

/-!
# Characteristic function of `|γ + β|²` and the Fourier small-ball bound

The modulus of the characteristic function of `|γ + β|²`, `γ` standard complex Gaussian,
is `(1 + η²)^{-1/2} exp(-η²|β|²/(1 + η²))` (the complex form of the computation in [APSSS,
Section 6]); and for a real law `ν`, `ν([a - ε, a + ε]) ≤ C ε ∫ |φ_ν|`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- One real coordinate of `γ + β`, `γ` standard complex Gaussian: for `t` standard Gaussian,
`|E exp(iη(t/√2 + m)²)| = (1 + η²)^{-1/4} exp(-η²m²/(1 + η²))`. -/
private lemma quadCharFun_coord (η m : ℝ) :
    ‖∫ t : ℝ, Complex.exp ((η : ℂ) * (((t / √2 + m) ^ 2 : ℝ) : ℂ) * Complex.I)
        ∂(gaussianReal 0 1)‖ =
      (1 + η ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-(η ^ 2 * m ^ 2 / (1 + η ^ 2))) := by
  set b : ℂ := (Complex.I * η - 1) / 2 with hb
  set c : ℂ := ((√2 * η * m : ℝ) : ℂ) * Complex.I with hc
  set d : ℂ := ((η * m ^ 2 : ℝ) : ℂ) * Complex.I with hd
  have hbre : b.re < 0 := by simp [hb]; norm_num
  have h1 : ∀ t : ℝ, gaussianPDFReal 0 1 t •
      Complex.exp ((η : ℂ) * (((t / √2 + m) ^ 2 : ℝ) : ℂ) * Complex.I) =
        ((√(2 * π))⁻¹ : ℝ) * Complex.exp (b * t ^ 2 + c * t + d) := by
    intro t
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Complex.real_smul]
    have hs : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have hs0 : ((√2 : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      positivity
    have hinv : (((√2 : ℝ) : ℂ))⁻¹ = ((√2 : ℝ) : ℂ) / 2 := by
      field_simp
      linear_combination -hs
    rw [Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    rw [div_eq_mul_inv (t : ℂ), hinv]
    simp only [hb, hc, hd]
    push_cast
    linear_combination ((η : ℂ) * Complex.I * (t : ℂ) ^ 2 / 4) * hs
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp_rw [h1]
  rw [integral_const_mul, integral_cexp_quadratic hbre]
  have hA : (0 : ℝ) < 1 + η ^ 2 := by positivity
  have hs : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  -- the exponent
  have hw : d - c ^ 2 / (4 * b) = ((-(η ^ 2 * m ^ 2 / (1 + η ^ 2)) : ℝ) : ℂ) +
      ((η * m ^ 2 / (1 + η ^ 2) : ℝ) : ℂ) * Complex.I := by
    have h1 : (1 + (η : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hA.ne'
    have h2 : (η : ℂ) * Complex.I - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    have hc2 : c ^ 2 = -(2 * (η : ℂ) ^ 2 * (m : ℂ) ^ 2) := by
      rw [hc, mul_pow, Complex.I_sq]
      push_cast
      rw [mul_pow, mul_pow, hs]
      ring
    rw [hc2, hb, hd]
    push_cast
    field_simp
    linear_combination (4 * (η : ℂ) ^ 4 * (m : ℂ) ^ 2) * Complex.I_sq
  have hnb : ‖-b‖ = √(1 + η ^ 2) / 2 := by
    rw [norm_neg, hb, norm_div, Complex.norm_def, Complex.normSq_apply]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    congr 2
    simp
    ring
  have hX : ‖((π : ℂ) / -b) ^ (1 / 2 : ℂ)‖ =
      (2 * π / √(1 + η ^ 2)) ^ (1 / 2 : ℝ) := by
    have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_cpow_real, norm_div, hnb, Complex.norm_real,
      Real.norm_of_nonneg pi_pos.le]
    congr 1
    field_simp
  have hre : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by intro x y; simp
  rw [hw, norm_mul, norm_mul, Complex.norm_exp, hX, hre, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have key : (√(2 * π))⁻¹ * (2 * π / √(1 + η ^ 2)) ^ (1 / 2 : ℝ) =
      (1 + η ^ 2) ^ (-(1 / 4 : ℝ)) := by
    have h2π : (0 : ℝ) < 2 * π := by positivity
    have hx : 0 < (2 * π) ^ (1 / 2 : ℝ) := by positivity
    have hy : 0 < (1 + η ^ 2) ^ (1 / 2 * (1 / 2) : ℝ) := by positivity
    rw [Real.div_rpow h2π.le (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hA.le]
    have : (1 + η ^ 2) ^ (-(1 / 4) : ℝ) = ((1 + η ^ 2) ^ (1 / 2 * (1 / 2) : ℝ))⁻¹ := by
      rw [← Real.rpow_neg hA.le]
      norm_num
    rw [this]
    field_simp
  rw [← mul_assoc, key]

/-- The map `y ↦ (√2)⁻¹ (y₀ + i y₁)` from `ℝ²` to `ℂ` is continuous. -/
private lemma quadCharFun_continuous_mk : Continuous fun y : Fin 2 → ℝ =>
    ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y 0, y 1⟩ : ℂ) := by
  have : (fun y : Fin 2 → ℝ => ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y 0, y 1⟩ : ℂ)) =
      fun y => ((Real.sqrt 2)⁻¹ : ℂ) * ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) := by
    funext y
    rw [Complex.mk_eq_add_mul_I]
  rw [this]
  fun_prop

/-- `‖(√2)⁻¹ (y₀ + i y₁) + β‖² = (y₀/√2 + Re β)² + (y₁/√2 + Im β)²`. -/
private lemma quadCharFun_norm_sq (β : ℂ) (y : Fin 2 → ℝ) :
    ‖((Real.sqrt 2)⁻¹ : ℂ) * (⟨y 0, y 1⟩ : ℂ) + β‖ ^ 2 =
      (y 0 / √2 + β.re) ^ 2 + (y 1 / √2 + β.im) ^ 2 := by
  have hinv : (√2)⁻¹ = √2 / 2 := by
    have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 : √2 ≠ 0 := by positivity
    field_simp
    linear_combination -hs
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Fin.isValue, Complex.add_re, Complex.mul_re, Complex.inv_re, Complex.ofReal_re,
    Complex.normSq_ofReal, Nat.ofNat_nonneg, mul_self_sqrt, Complex.inv_im, Complex.ofReal_im,
    neg_zero, Complex.add_im, Complex.mul_im, div_eq_inv_mul]
  rw [hinv]
  ring

/-- Fourier transform of a Gaussian:
`∫ e^{iξt} e^{-ε²ξ²/2} dξ = (√(2π)/ε) e^{-t²/(2ε²)}`. -/
private lemma quadCharFun_gauss_fourier {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∫ ξ : ℝ, Complex.exp (Complex.I * (t : ℂ) * ξ) *
        Complex.exp (-((ε ^ 2 / 2 : ℝ) : ℂ) * ξ ^ 2) =
      ((√(2 * π) / ε : ℝ) : ℂ) * Complex.exp ((-(t ^ 2 / (2 * ε ^ 2)) : ℝ)) := by
  have hb : 0 < (((ε ^ 2 / 2 : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]; positivity
  rw [fourierIntegral_gaussian hb (t : ℂ)]
  have h1 : (π / ((ε ^ 2 / 2 : ℝ) : ℂ) : ℂ) = ((2 * π / ε ^ 2 : ℝ) : ℂ) := by
    push_cast
    have : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    field_simp
  have h2 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, h2, ← Complex.ofReal_cpow (by positivity)]
  congr 1
  · norm_cast
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by positivity), Real.sqrt_sq hε.le]
  · congr 1
    push_cast
    have : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    field_simp
    ring

/-- The real part of `-b ξ²` for real `b`, `ξ`. -/
private lemma quadCharFun_re_gauss (b ξ : ℝ) :
    (-(b : ℂ) * (ξ : ℂ) ^ 2).re = -b * ξ ^ 2 := by
  rw [← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- `1 ≤ 2 exp (-(y - a)²/(2ε²))` on `[a - ε, a + ε]`. -/
private lemma quadCharFun_one_le {a ε y : ℝ} (hε : 0 < ε)
    (hy : y ∈ Set.Icc (a - ε) (a + ε)) :
    1 ≤ 2 * Real.exp (-((y - a) ^ 2 / (2 * ε ^ 2))) := by
  have h1 : (y - a) ^ 2 ≤ ε ^ 2 := by
    have := abs_le.mpr
      (⟨by linarith [hy.1], by linarith [hy.2]⟩ : -ε ≤ y - a ∧ y - a ≤ ε)
    nlinarith [sq_abs (y - a), abs_nonneg (y - a)]
  have h2 : (y - a) ^ 2 / (2 * ε ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h3 := Real.add_one_le_exp (-((y - a) ^ 2 / (2 * ε ^ 2)))
  have h4 := Real.exp_le_exp.mpr (show -(1 / 2 : ℝ) ≤ -((y - a) ^ 2 / (2 * ε ^ 2)) by linarith)
  have h5 := Real.add_one_le_exp (-(1 / 2 : ℝ))
  linarith

/-- `|E e^{iη|γ + β|²}| = (1 + η²)^{-1/2} exp(-η²|β|²/(1 + η²))`. -/
theorem norm_charFun_normSq_cGauss (β : ℂ) (η : ℝ) :
    ‖charFun (cGauss.map fun z => ‖z + β‖ ^ 2) η‖ =
      (1 + η ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-(η ^ 2 * ‖β‖ ^ 2 / (1 + η ^ 2))) := by
  have hA : (0 : ℝ) < 1 + η ^ 2 := by positivity
  have hg : Continuous fun z : ℂ => ‖z + β‖ ^ 2 := by fun_prop
  have hmap : cGauss.map (fun z : ℂ => ‖z + β‖ ^ 2) = (stdGauss (Fin 2)).map
      ((fun z : ℂ => ‖z + β‖ ^ 2) ∘
        fun y : Fin 2 → ℝ => ((Real.sqrt 2)⁻¹ : ℂ) * ⟨y 0, y 1⟩) := by
    unfold cGauss
    rw [Measure.map_map hg.measurable quadCharFun_continuous_mk.measurable]
  rw [hmap, charFun_apply_real,
    integral_map (hg.measurable.comp quadCharFun_continuous_mk.measurable).aemeasurable
      (by fun_prop)]
  have hint : ∀ y : Fin 2 → ℝ, Complex.exp ((η : ℂ) * (((fun z : ℂ => ‖z + β‖ ^ 2) ∘
      fun y : Fin 2 → ℝ => ((Real.sqrt 2)⁻¹ : ℂ) * ⟨y 0, y 1⟩) y : ℝ) * Complex.I) =
      ∏ i : Fin 2, Complex.exp
        ((η : ℂ) * (((y i / √2 + ![β.re, β.im] i) ^ 2 : ℝ) : ℂ) * Complex.I) := by
    intro y
    rw [Fin.prod_univ_two, ← Complex.exp_add]
    congr 1
    simp only [Function.comp_apply, quadCharFun_norm_sq]
    simp
    ring
  simp_rw [hint]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod
    (fun i t => Complex.exp ((η : ℂ) * (((t / √2 + ![β.re, β.im] i) ^ 2 : ℝ) : ℂ) * Complex.I))
    (μ := fun _ => gaussianReal 0 1)]
  rw [Fin.prod_univ_two, norm_mul, quadCharFun_coord, quadCharFun_coord]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← mul_mul_mul_comm, ← Real.rpow_add hA, ← Real.exp_add]
  congr 2
  · norm_num
  · rw [Complex.sq_norm, Complex.normSq_apply]
    field_simp
    ring

/-- Fourier small-ball bound: `ν([a - ε, a + ε]) ≤ C ε ∫ |φ_ν(ξ)| dξ` for every probability
measure `ν` on `ℝ`, `a ∈ ℝ` and `ε > 0`. -/
theorem measure_Icc_le_lintegral_charFun : ∃ C : ℝ, 0 < C ∧
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (a ε : ℝ), 0 < ε →
      ν (Set.Icc (a - ε) (a + ε)) ≤ ENNReal.ofReal (C * ε) * ∫⁻ ξ, ‖charFun ν ξ‖ₑ := by
  refine ⟨1, one_pos, fun ν _ a ε hε => ?_⟩
  set G : ℝ → ℝ := fun y => Real.exp (-((y - a) ^ 2 / (2 * ε ^ 2))) with hG
  have hGc : Continuous G := by rw [hG]; fun_prop
  have hGnn : ∀ y, 0 ≤ G y := fun y => (Real.exp_pos _).le
  have hGint : Integrable G ν := by
    refine (integrable_const (1 : ℝ)).mono' hGc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (hGnn y), hG]
    simp only
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (y - a) ^ 2 / (2 * ε ^ 2) := by positivity
    linarith
  -- the indicator is dominated by `2 G`
  have step1 : ν (Set.Icc (a - ε) (a + ε)) ≤ ENNReal.ofReal (2 * ∫ y, G y ∂ν) := by
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hGint.const_mul 2)
      (Filter.Eventually.of_forall fun y => by have := hGnn y; positivity)]
    calc ν (Set.Icc (a - ε) (a + ε))
        = ∫⁻ y, (Set.Icc (a - ε) (a + ε)).indicator 1 y ∂ν :=
          (lintegral_indicator_one measurableSet_Icc).symm
      _ ≤ ∫⁻ y, ENNReal.ofReal (2 * G y) ∂ν := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ Set.Icc (a - ε) (a + ε)
          · rw [Set.indicator_of_mem hy]
            exact ENNReal.one_le_ofReal.mpr (quadCharFun_one_le hε hy)
          · rw [Set.indicator_of_notMem hy]
            exact zero_le
  set c : ℝ := ε / √(2 * π) with hc
  have hcpos : 0 < c := by positivity
  set F : ℝ → ℝ → ℂ := fun y ξ => Complex.exp (Complex.I * ((y - a : ℝ) : ℂ) * ξ) *
    Complex.exp (-((ε ^ 2 / 2 : ℝ) : ℂ) * ξ ^ 2) with hF
  have hFG : ∀ y, ((G y : ℝ) : ℂ) = (c : ℂ) * ∫ ξ, F y ξ := by
    intro y
    simp only [hF]
    rw [quadCharFun_gauss_fourier hε (y - a), ← mul_assoc, ← Complex.ofReal_mul]
    have : c * (√(2 * π) / ε) = 1 := by
      rw [hc]
      have : √(2 * π) ≠ 0 := by positivity
      field_simp
    rw [this, Complex.ofReal_one, one_mul, hG, Complex.ofReal_exp]
  have hb : 0 < ε ^ 2 / 2 := by positivity
  have hFint : Integrable (Function.uncurry F) (ν.prod volume) := by
    have hbound : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * Real.exp (-(ε ^ 2 / 2) * z.2 ^ 2))
        (ν.prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod (integrable_exp_neg_mul_sq hb)
    refine hbound.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · simp only [hF]
      fun_prop
    · simp only [hF, Function.uncurry, norm_mul, Complex.norm_exp]
      have h1 : (Complex.I * ((z.1 - a : ℝ) : ℂ) * (z.2 : ℂ)).re = 0 := by simp
      rw [h1, quadCharFun_re_gauss, Real.exp_zero, one_mul]
  set H : ℝ → ℂ := fun ξ => Complex.exp (-(Complex.I * (a : ℂ) * ξ)) * charFun ν ξ *
    Complex.exp (-((ε ^ 2 / 2 : ℝ) : ℂ) * ξ ^ 2) with hH
  have hFy : ∀ ξ : ℝ, ∫ y, F y ξ ∂ν = H ξ := by
    intro ξ
    simp only [hH]
    simp only [hF]
    rw [integral_mul_const, charFun_apply_real, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hswap : ((∫ y, G y ∂ν : ℝ) : ℂ) = (c : ℂ) * ∫ ξ : ℝ, H ξ := by
    rw [← integral_complex_ofReal]
    simp_rw [hFG]
    rw [integral_const_mul, integral_integral_swap hFint]
    simp_rw [hFy]
  have step3 : ENNReal.ofReal (∫ y, G y ∂ν) ≤ ENNReal.ofReal c * ∫⁻ ξ, ‖charFun ν ξ‖ₑ := by
    have h0 : 0 ≤ ∫ y, G y ∂ν := integral_nonneg hGnn
    have hcE : ‖(c : ℂ)‖ₑ = ENNReal.ofReal c := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
    calc ENNReal.ofReal (∫ y, G y ∂ν) = ‖((∫ y, G y ∂ν : ℝ) : ℂ)‖ₑ := by
          rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg h0]
      _ = ENNReal.ofReal c * ‖∫ ξ : ℝ, H ξ‖ₑ := by
          rw [hswap, enorm_mul, hcE]
      _ ≤ ENNReal.ofReal c * ∫⁻ ξ : ℝ, ‖H ξ‖ₑ := by
          gcongr
          exact enorm_integral_le_lintegral_enorm _
      _ ≤ ENNReal.ofReal c * ∫⁻ ξ, ‖charFun ν ξ‖ₑ := by
          gcongr with ξ
          simp only [hH]
          rw [← ofReal_norm, ← ofReal_norm]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
          have h1 : (-(Complex.I * (a : ℂ) * ξ)).re = 0 := by simp
          have h2 : (-((ε ^ 2 / 2 : ℝ) : ℂ) * (ξ : ℂ) ^ 2).re ≤ 0 := by
            rw [quadCharFun_re_gauss]
            nlinarith [sq_nonneg ξ, sq_nonneg ε]
          rw [h1, Real.exp_zero, one_mul]
          calc ‖charFun ν ξ‖ * Real.exp (-((ε ^ 2 / 2 : ℝ) : ℂ) * ξ ^ 2).re
              ≤ ‖charFun ν ξ‖ * 1 := by
                gcongr
                exact Real.exp_le_one_iff.mpr h2
            _ = _ := mul_one _
  calc ν (Set.Icc (a - ε) (a + ε)) ≤ ENNReal.ofReal (2 * ∫ y, G y ∂ν) := step1
    _ = ENNReal.ofReal 2 * ENNReal.ofReal (∫ y, G y ∂ν) := ENNReal.ofReal_mul (by norm_num)
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal c * ∫⁻ ξ, ‖charFun ν ξ‖ₑ) := by gcongr
    _ = ENNReal.ofReal (2 * c) * ∫⁻ ξ, ‖charFun ν ξ‖ₑ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
    _ ≤ ENNReal.ofReal (1 * ε) * ∫⁻ ξ, ‖charFun ν ξ‖ₑ := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          rw [hc, one_mul]
          have h2 : (2 : ℝ) ≤ √(2 * π) := by
            refine (Real.le_sqrt' (by norm_num)).mpr ?_
            nlinarith [Real.pi_gt_three]
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith

end LSBA
