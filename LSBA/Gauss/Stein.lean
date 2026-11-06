/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian integration by parts (Stein's identity)

For a centred Gaussian of variance `v`, the density `p` satisfies `p' = -(x/v) p`, so one
integration by parts on the line turns a factor `x` into a derivative:
`E[X f(X)] = v E[f'(X)]`.  This is the one-coordinate Gaussian integration by parts used in
Appendix C.1 [sec:classical-random-matrix] (before and after (C.1) [gc:eq:divergence]) and in
Appendix D.2 [sec:rough-density-proof] (before (D.3) [rd:eq:mean]).

## Main results

* `LSBA.hasDerivAt_gaussianPDFReal_zero` : `p' = -(x/v) p`
* `LSBA.integral_mul_gaussianPDF` : the identity in density form
* `LSBA.integral_mul_gaussianReal` : the identity `E[X f(X)] = v E[f'(X)]`, real valued, with
  integrability as explicit hypotheses

* `LSBA.integral_mul_gaussianReal_poly` : complex valued, `f` and `f'` of polynomial growth,
  every variance `v ≥ 0`
-/

namespace LSBA

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {var : ℝ≥0}

/-- The centred Gaussian density solves the first-order ODE `p' = -(x/v) p`. -/
theorem hasDerivAt_gaussianPDFReal_zero (hv : (var : ℝ) ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 var) (-(x / (var : ℝ)) * gaussianPDFReal 0 var x) x := by
  have key : gaussianPDFReal 0 var
      = fun y : ℝ => (Real.sqrt (2 * π * (var : ℝ)))⁻¹ * Real.exp (-(y ^ 2) / (2 * (var : ℝ))) := by
    funext y
    simp [gaussianPDFReal]
  have hp : HasDerivAt (fun y : ℝ => -(y ^ 2) / (2 * (var : ℝ)))
      (-(2 * x) / (2 * (var : ℝ))) x := by
    simpa using ((hasDerivAt_pow 2 x).neg).div_const (2 * (var : ℝ))
  have hc := (hp.exp).const_mul ((Real.sqrt (2 * π * (var : ℝ)))⁻¹)
  rw [key]
  convert hc using 1
  simp only
  field_simp
  try ring

/-- **Stein's identity**, density form:
`∫ x f(x) p(x) dx = v ∫ f'(x) p(x) dx`.

One integration by parts on `(-∞, ∞)`; the boundary terms vanish because the total
function is integrable. -/
theorem integral_mul_gaussianPDF (hv : (var : ℝ) ≠ 0) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (h1 : Integrable fun x : ℝ => f x * (-(x / (var : ℝ)) * gaussianPDFReal 0 var x))
    (h2 : Integrable fun x : ℝ => f' x * gaussianPDFReal 0 var x)
    (h3 : Integrable fun x : ℝ => f x * gaussianPDFReal 0 var x) :
    ∫ x : ℝ, x * f x * gaussianPDFReal 0 var x
      = (var : ℝ) * ∫ x : ℝ, f' x * gaussianPDFReal 0 var x := by
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := gaussianPDFReal 0 var) (u' := f')
    (v' := fun x : ℝ => -(x / (var : ℝ)) * gaussianPDFReal 0 var x)
    (fun x _ => hf x) (fun x _ => hasDerivAt_gaussianPDFReal_zero hv x) h1 h2 h3
  have hL : (fun x : ℝ => f x * (-(x / (var : ℝ)) * gaussianPDFReal 0 var x))
      = fun x : ℝ => (-(1 / (var : ℝ))) * (x * f x * gaussianPDFReal 0 var x) := by
    funext x
    field_simp
    try ring
  rw [hL, integral_const_mul] at key
  field_simp at key
  linarith

/-- **Stein's identity** for the Gaussian measure: `E[X f(X)] = v E[f'(X)]`. -/
theorem integral_mul_gaussianReal (hv : var ≠ 0) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (h1 : Integrable fun x : ℝ => f x * (-(x / (var : ℝ)) * gaussianPDFReal 0 var x))
    (h2 : Integrable fun x : ℝ => f' x * gaussianPDFReal 0 var x)
    (h3 : Integrable fun x : ℝ => f x * gaussianPDFReal 0 var x) :
    ∫ x : ℝ, x * f x ∂(gaussianReal 0 var) = (var : ℝ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  have hv' : (var : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have h := integral_mul_gaussianPDF hv' hf h1 h2 h3
  rw [integral_gaussianReal_eq_integral_smul (f := fun x : ℝ => x * f x) hv,
    integral_gaussianReal_eq_integral_smul (f := f') hv]
  simp only [smul_eq_mul]
  rw [show (fun x : ℝ => gaussianPDFReal 0 var x * (x * f x))
        = fun x : ℝ => x * f x * gaussianPDFReal 0 var x from by funext x; ring,
    show (fun x : ℝ => gaussianPDFReal 0 var x * f' x)
        = fun x : ℝ => f' x * gaussianPDFReal 0 var x from by funext x; ring]
  exact h

/-! ### Integrability of the identity -/

/-- The identity function has a finite first absolute moment under a Gaussian. -/
theorem integrable_id_gaussianReal :
    Integrable (fun x : ℝ => x) (gaussianReal 0 var) := by
  have h : MemLp id 1 (gaussianReal (0 : ℝ) var) := by
    simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := var) 1
  exact memLp_one_iff_integrable.mp h

/-! ### Polynomial growth

For `f` and `f'` dominated by `C (1 + |x|)^k`, the integrability hypotheses of
`integral_mul_gaussianReal` follow from finiteness of all absolute moments of a Gaussian. -/

private lemma Stein_one_add_abs_pow_le (m : ℕ) (x : ℝ) :
    (1 + |x|) ^ m ≤ 2 ^ m * (1 + |x| ^ m) := by
  have h2 : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hx : (0 : ℝ) ≤ |x| ^ m := by positivity
  rcases le_total |x| 1 with h | h
  · calc (1 + |x|) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
  · calc (1 + |x|) ^ m ≤ (2 * |x|) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = 2 ^ m * |x| ^ m := by rw [mul_pow]
      _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith

private lemma Stein_integrable_one_add_abs_pow (m : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 var) := by
  have hm : MemLp id (m : ENNReal) (gaussianReal (0 : ℝ) var) :=
    memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := var) m (ENNReal.natCast_ne_top m)
  have hm' : MemLp id (m : ℕ) (gaussianReal (0 : ℝ) var) := by simpa using hm
  have h1 : Integrable (fun x : ℝ => ‖id x‖ ^ m) (gaussianReal 0 var) := hm'.integrable_norm_pow'
  have h2 : Integrable (fun x : ℝ => (2 : ℝ) ^ m * (1 + |x| ^ m)) (gaussianReal 0 var) :=
    ((integrable_const (1 : ℝ)).add (by simpa using h1)).const_mul _
  refine h2.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ℝ => (1 + |x|) ^ m).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    exact Stein_one_add_abs_pow_le m x

/-- A continuous function of polynomial growth is integrable against a Gaussian. -/
private lemma Stein_integrable_of_poly {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    {D : ℝ} {m : ℕ} (hg : Continuous g) (hb : ∀ x, ‖g x‖ ≤ D * (1 + |x|) ^ m) :
    Integrable g (gaussianReal 0 var) :=
  ((Stein_integrable_one_add_abs_pow (var := var) m).const_mul D).mono'
    hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)

/-- Integrability against a non-degenerate Gaussian gives integrability against its density. -/
private lemma Stein_integrable_mul_pdf (hv : var ≠ 0) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 var)) :
    Integrable fun x : ℝ => g x * gaussianPDFReal 0 var x := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 var)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at hg
  refine hg.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 var x), mul_comm]

/-- The real-valued case of `integral_mul_gaussianReal_poly` for a non-degenerate variance. -/
private lemma Stein_poly_real (hv : var ≠ 0) {f f' : ℝ → ℝ} {C : ℝ} {k : ℕ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f')
    (hb : ∀ x, ‖f x‖ ≤ C * (1 + |x|) ^ k) (hb' : ∀ x, ‖f' x‖ ≤ C * (1 + |x|) ^ k) :
    ∫ x : ℝ, x * f x ∂(gaussianReal 0 var) = (var : ℝ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  have hv' : (0 : ℝ) < (var : ℝ) :=
    lt_of_le_of_ne var.coe_nonneg (Ne.symm (NNReal.coe_ne_zero.mpr hv))
  have hC : 0 ≤ C := by simpa using (norm_nonneg (f 0)).trans (hb 0)
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hI : Integrable f (gaussianReal 0 var) := Stein_integrable_of_poly hfc hb
  have hI' : Integrable f' (gaussianReal 0 var) := Stein_integrable_of_poly hf'c hb'
  have hI1 : Integrable (fun x : ℝ => f x * (-(x / (var : ℝ)))) (gaussianReal 0 var) := by
    refine Stein_integrable_of_poly (D := C / (var : ℝ)) (m := k + 1)
      (hfc.mul (by fun_prop)) fun x => ?_
    have hx : |x| ≤ 1 + |x| := by linarith [abs_nonneg x]
    have hpk : (0 : ℝ) ≤ (1 + |x|) ^ k := by positivity
    simp only [norm_mul, norm_neg, norm_div, Real.norm_eq_abs, abs_of_pos hv', pow_succ]
    calc ‖f x‖ * (|x| / (var : ℝ)) ≤ C * (1 + |x|) ^ k * ((1 + |x|) / (var : ℝ)) := by
          gcongr; exact hb x
      _ = C / (var : ℝ) * ((1 + |x|) ^ k * (1 + |x|)) := by ring
  refine integral_mul_gaussianReal hv hf ?_ ?_ ?_
  · simpa [mul_assoc] using Stein_integrable_mul_pdf hv hI1
  · exact Stein_integrable_mul_pdf hv hI'
  · exact Stein_integrable_mul_pdf hv hI

/-- **One-dimensional Stein identity under polynomial growth**: `E[x f(x)] = v E[f'(x)]` for
the centred Gaussian of variance `v`, for `f : ℝ → ℂ` differentiable with continuous derivative,
where `f` and `f'` are bounded by `C (1 + |x|)^k`.  The case `v = 0` is the Dirac mass. -/
theorem integral_mul_gaussianReal_poly (v : ℝ≥0) {f f' : ℝ → ℂ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') {C : ℝ} {k : ℕ}
    (hb : ∀ x, ‖f x‖ ≤ C * (1 + |x|) ^ k) (hb' : ∀ x, ‖f' x‖ ≤ C * (1 + |x|) ^ k) :
    ∫ x, (x : ℂ) * f x ∂(gaussianReal 0 v) = ((v : ℝ) : ℂ) * ∫ x, f' x ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv
    simp
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hre : ∀ x, HasDerivAt (fun y => (f y).re) (f' x).re x := fun x => by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hf x)
    simp only [Function.comp_def, Complex.reCLM_apply] at h
    exact h
  have him : ∀ x, HasDerivAt (fun y => (f y).im) (f' x).im x := fun x => by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hf x)
    simp only [Function.comp_def, Complex.imCLM_apply] at h
    exact h
  have hbre : ∀ x, ‖(f x).re‖ ≤ C * (1 + |x|) ^ k := fun x =>
    le_trans (by simpa using Complex.abs_re_le_norm (f x)) (hb x)
  have hbim : ∀ x, ‖(f x).im‖ ≤ C * (1 + |x|) ^ k := fun x =>
    le_trans (by simpa using Complex.abs_im_le_norm (f x)) (hb x)
  have hb're : ∀ x, ‖(f' x).re‖ ≤ C * (1 + |x|) ^ k := fun x =>
    le_trans (by simpa using Complex.abs_re_le_norm (f' x)) (hb' x)
  have hb'im : ∀ x, ‖(f' x).im‖ ≤ C * (1 + |x|) ^ k := fun x =>
    le_trans (by simpa using Complex.abs_im_le_norm (f' x)) (hb' x)
  have Hre := Stein_poly_real hv hre (Complex.continuous_re.comp hf') hbre hb're
  have Him := Stein_poly_real hv him (Complex.continuous_im.comp hf') hbim hb'im
  have hIl : Integrable (fun x : ℝ => (x : ℂ) * f x) (gaussianReal 0 v) := by
    refine Stein_integrable_of_poly (D := C) (m := k + 1) (by fun_prop) fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, pow_succ']
    calc |x| * ‖f x‖ ≤ (1 + |x|) * (C * (1 + |x|) ^ k) := by
          gcongr
          · linarith [abs_nonneg x]
          · exact hb x
      _ = C * ((1 + |x|) * (1 + |x|) ^ k) := by ring
  have hIr : Integrable f' (gaussianReal 0 v) := Stein_integrable_of_poly hf' hb'
  have hLre : (∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 v)).re
      = ∫ x : ℝ, x * (f x).re ∂(gaussianReal 0 v) := by
    simpa using (Complex.reCLM.integral_comp_comm hIl).symm
  have hLim : (∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 v)).im
      = ∫ x : ℝ, x * (f x).im ∂(gaussianReal 0 v) := by
    simpa using (Complex.imCLM.integral_comp_comm hIl).symm
  have hFre : (∫ x : ℝ, f' x ∂(gaussianReal 0 v)).re
      = ∫ x : ℝ, (f' x).re ∂(gaussianReal 0 v) := by
    simpa using (Complex.reCLM.integral_comp_comm hIr).symm
  have hFim : (∫ x : ℝ, f' x ∂(gaussianReal 0 v)).im
      = ∫ x : ℝ, (f' x).im ∂(gaussianReal 0 v) := by
    simpa using (Complex.imCLM.integral_comp_comm hIr).symm
  refine Complex.ext ?_ ?_
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hLre, hFre]
    exact Hre
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      hLim, hFim]
    exact Him

end LSBA
