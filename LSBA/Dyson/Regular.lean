import LSBA.Dyson.Density
import LSBA.Dyson.Perturb

/-!
# Regularity of `m_g` (Lemma A.2 [bl:lem:regular])

The third inequality of (A.6) [da:eq:ward] on `ℂ_+`, the first `z`-derivative bound, and Lemma A.2
[bl:lem:regular] in quantile form at `γ = γ_g`: (A.7) [bl:eq:regular-domain] and the lower bound of
(A.8) [bl:eq:regular-bounds].
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-! ### The resolvent `R_w(p) = (2b cos p − w)⁻¹` and its averages -/

/-- `R_w(p) = (2b cos p − w)⁻¹`. -/
private def regRes (b : ℝ) (w : ℂ) (p : ℝ) : ℂ := ((2 * b * Real.cos p : ℝ) - w)⁻¹

private lemma regular_res_ne {b : ℝ} {w : ℂ} (hw : 0 < w.im) (p : ℝ) :
    ((2 * b * Real.cos p : ℝ) : ℂ) - w ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

private lemma regular_res_cont {b : ℝ} {w : ℂ} (hw : 0 < w.im) : Continuous (regRes b w) := by
  unfold regRes
  exact Continuous.inv₀ (by fun_prop) (regular_res_ne hw)

private lemma regular_norm_res_le (b : ℝ) {w : ℂ} (hw : 0 < w.im) (p : ℝ) :
    ‖regRes b w p‖ ≤ w.im⁻¹ := by
  unfold regRes
  rw [norm_inv]
  refine inv_anti₀ hw ?_
  calc w.im = |(((2 * b * Real.cos p : ℝ) : ℂ) - w).im| := by simp [abs_of_pos hw]
    _ ≤ ‖((2 * b * Real.cos p : ℝ) : ℂ) - w‖ := Complex.abs_im_le_norm _

/-- Resolvent identity `R_{w'} − R_w = (w' − w) R_{w'} R_w`. -/
private lemma regular_res_sub (b : ℝ) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) (p : ℝ) :
    regRes b w' p - regRes b w p = (w' - w) * (regRes b w' p * regRes b w p) := by
  have h1 := regular_res_ne (b := b) hw p
  have h2 := regular_res_ne (b := b) hw' p
  unfold regRes
  field_simp
  ring

/-- Jensen's inequality for the average over `[-π, π]`: `⟨f⟩² ≤ ⟨f²⟩`. -/
private lemma regular_avg_sq_le {f : ℝ → ℝ} (hf : Continuous f) :
    ((2 * π)⁻¹ * ∫ p in (-π)..π, f p) ^ 2 ≤ (2 * π)⁻¹ * ∫ p in (-π)..π, f p ^ 2 := by
  set c := (2 * π)⁻¹ * ∫ p in (-π)..π, f p with hc
  have hpi := Real.pi_pos
  have h0 : 0 ≤ ∫ p in (-π)..π, (f p - c) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun p _ => sq_nonneg _)
  have e : ∫ p in (-π)..π, (f p - c) ^ 2 =
      (∫ p in (-π)..π, f p ^ 2) - 2 * c * (∫ p in (-π)..π, f p) + (2 * π) * c ^ 2 := by
    have i1 : IntervalIntegrable (fun p => f p ^ 2) volume (-π) π :=
      (by fun_prop : Continuous fun p => f p ^ 2).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun p => 2 * c * f p) volume (-π) π :=
      (by fun_prop : Continuous fun p => 2 * c * f p).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume (-π) π := intervalIntegrable_const
    have : (fun p => (f p - c) ^ 2) = fun p => (f p ^ 2 - 2 * c * f p) + c ^ 2 := by
      funext p; ring
    rw [this, intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [e] at h0
  have hI : ∫ p in (-π)..π, f p = (2 * π) * c := by
    rw [hc]; field_simp
  rw [hI] at h0
  have : (2 * π) * c ^ 2 ≤ ∫ p in (-π)..π, f p ^ 2 := by nlinarith
  calc c ^ 2 = (2 * π)⁻¹ * ((2 * π) * c ^ 2) := by field_simp
    _ ≤ (2 * π)⁻¹ * ∫ p in (-π)..π, f p ^ 2 := by gcongr

/-- The stability bound of (A.6) [da:eq:ward] for the free transform:
`γ ⟨|R|²⟩ ≤ 1` gives `Re(1 − γ ⟨R²⟩) ≥ 2γ (Im ⟨R⟩)²`. -/
private lemma regular_stab_core (b γ : ℝ) (hγ : 0 ≤ γ) {w : ℂ} (hw : 0 < w.im)
    (hθ : γ * ((2 * π)⁻¹ * ∫ p in (-π)..π, ‖regRes b w p‖ ^ 2) ≤ 1) :
    2 * γ * (freeT b w).im ^ 2 ≤
      (1 - γ * ((((2 * π)⁻¹ : ℝ) : ℂ) * ∫ p in (-π)..π, regRes b w p ^ 2)).re := by
  rw [show (((2 * π)⁻¹ : ℝ) : ℂ) = (2 * π : ℂ)⁻¹ by push_cast; ring]
  have hc := regular_res_cont (b := b) hw
  have hpi := Real.pi_pos
  have e2 : (2 * π : ℂ)⁻¹ = (((2 * π)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  -- `Im ⟨R⟩ = ⟨Im R⟩`
  have him : (freeT b w).im = (2 * π)⁻¹ * ∫ p in (-π)..π, (regRes b w p).im := by
    unfold freeT
    rw [e2, Complex.im_ofReal_mul]
    congr 1
    exact (intervalIntegral.intervalIntegral_im (hc.intervalIntegrable _ _)).symm
  -- `Re ⟨R²⟩ = ⟨|R|²⟩ − 2 ⟨(Im R)²⟩`
  have hre : ((2 * π : ℂ)⁻¹ * ∫ p in (-π)..π, regRes b w p ^ 2).re =
      (2 * π)⁻¹ * (∫ p in (-π)..π, ‖regRes b w p‖ ^ 2) -
        2 * ((2 * π)⁻¹ * ∫ p in (-π)..π, (regRes b w p).im ^ 2) := by
    have hre0 := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (μ := volume) (a := -π) (b := π)
      ((by fun_prop : Continuous fun p => regRes b w p ^ 2).intervalIntegrable _ _)
    simp only [RCLike.re_to_complex] at hre0
    rw [e2, Complex.re_ofReal_mul, ← hre0]
    have hpt : ∀ p, (regRes b w p ^ 2).re =
        ‖regRes b w p‖ ^ 2 - 2 * (regRes b w p).im ^ 2 := by
      intro p
      rw [Complex.sq_norm, Complex.normSq_apply, sq, Complex.mul_re]
      ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun p => ‖regRes b w p‖ ^ 2).intervalIntegrable _ _)
      ((show Continuous fun p => 2 * (regRes b w p).im ^ 2 from
        ((Complex.continuous_im.comp hc).pow 2).const_mul 2).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
    ring
  have hJ := regular_avg_sq_le (f := fun p => (regRes b w p).im) (Complex.continuous_im.comp hc)
  rw [← him] at hJ
  have hr : (1 - (γ : ℂ) * ((2 * π : ℂ)⁻¹ * ∫ p in (-π)..π, regRes b w p ^ 2)).re =
      1 - γ * ((2 * π : ℂ)⁻¹ * ∫ p in (-π)..π, regRes b w p ^ 2).re := by
    rw [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul]
  rw [hr, hre]
  nlinarith

/-! ### The parameters `γ_g`, `b = √γ_g g` -/

private lemma regular_max_pos (g : ℝ) : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)

private lemma regular_gamma_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have := regular_max_pos g
  positivity

private lemma regular_hopB_nonneg {g : ℝ} (hg : 0 ≤ g) : 0 ≤ hopB g := by
  unfold hopB
  exact div_nonneg hg (regular_max_pos g).le

private lemma regular_hopB_le_one (g : ℝ) : hopB g ≤ 1 := by
  unfold hopB
  rw [div_le_one (regular_max_pos g)]
  exact le_max_right _ _

/-- `γ_g ‖u‖ ≤ 1` when `‖u‖ ≤ max{1, g}`. -/
private lemma regular_gamma_mul_le {g r : ℝ} (hr : r ≤ max 1 g) : gammaG g * r ≤ 1 := by
  have hM := regular_max_pos g
  have hγ := regular_gamma_pos g
  calc gammaG g * r ≤ gammaG g * max 1 g := mul_le_mul_of_nonneg_left hr hγ.le
    _ = (max 1 g)⁻¹ := by unfold gammaG; field_simp
    _ ≤ 1 := inv_le_one_of_one_le₀ (le_max_left _ _)

/-- The integrand of (A.6) [da:eq:ward] is `R_w` at `w = z + γ_g u`. -/
private lemma regular_integrand (g : ℝ) (z u : ℂ) (p : ℝ) :
    (((2 * hopB g * Real.cos p : ℝ) : ℂ) - z - gammaG g * u)⁻¹ =
      regRes (hopB g) (z + gammaG g * u) p := by
  simp only [regRes, sub_sub]

/-! ### Stability, (A.6) [da:eq:ward] -/

/-- (A.6) [da:eq:ward], third inequality: `Re(1 - γ f'(w)) ≥ 2γ (Im m)²`, `f'(w) = ⟨R²⟩`. -/
theorem mDyson_stab (g : ℝ) (hg : 0 ≤ g) (z : ℂ) (hz : 0 < z.im) :
    2 * gammaG g * (mDyson g z).im ^ 2 ≤
      (1 - gammaG g * ((2 * π)⁻¹ * ∫ p in (-π)..π,
        (((2 * hopB g * Real.cos p : ℝ) - z - gammaG g * mDyson g z)⁻¹) ^ 2)).re := by
  obtain ⟨hm, hfix⟩ := mDyson_spec g hg z hz
  have hγ := regular_gamma_pos g
  have hw : 0 < (z + gammaG g * mDyson g z).im := by
    rw [Complex.add_im, Complex.im_ofReal_mul]; positivity
  have hward := mDyson_ward g hg z hz
  simp_rw [regular_integrand] at hward ⊢
  have hθ : gammaG g * ((2 * π)⁻¹ * ∫ p in (-π)..π,
      ‖regRes (hopB g) (z + gammaG g * mDyson g z) p‖ ^ 2) ≤ 1 := by
    rw [hward, mul_div_assoc', div_le_one (by positivity)]
    linarith
  have h := regular_stab_core (hopB g) (gammaG g) hγ.le hw hθ
  rwa [← dysonRHS_eq_freeT, ← hfix] at h

/-! ### The first `z`-derivative -/

/-- `‖(2π)⁻¹ ∫_{-π}^{π} f‖ ≤ C` when `‖f‖ ≤ C`. -/
private lemma regular_norm_avg_le {f : ℝ → ℂ} {C : ℝ} (h : ∀ p, ‖f p‖ ≤ C) :
    ‖(((2 * π)⁻¹ : ℝ) : ℂ) * ∫ p in (-π)..π, f p‖ ≤ C := by
  have hpi := Real.pi_pos
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := -π) (b := π)
    (fun p _ => h p)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [show |π - -π| = 2 * π by rw [abs_of_pos (by linarith)]; ring] at h1
  calc (2 * π)⁻¹ * ‖∫ p in (-π)..π, f p‖ ≤ (2 * π)⁻¹ * (C * (2 * π)) := by gcongr
    _ = C := by field_simp

/-- `‖⟨R²⟩‖ ≤ ⟨|R|²⟩`. -/
private lemma regular_norm_avg_sq_le (b : ℝ) (w : ℂ) :
    ‖(((2 * π)⁻¹ : ℝ) : ℂ) * ∫ p in (-π)..π, regRes b w p ^ 2‖ ≤
      (2 * π)⁻¹ * ∫ p in (-π)..π, ‖regRes b w p‖ ^ 2 := by
  have hpi := Real.pi_pos
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  gcongr
  calc ‖∫ p in (-π)..π, regRes b w p ^ 2‖ ≤ ∫ p in (-π)..π, ‖regRes b w p ^ 2‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ = ∫ p in (-π)..π, ‖regRes b w p‖ ^ 2 := by simp_rw [norm_pow]

/-- The free transform is holomorphic on `ℂ_+` with `f'(w) = ⟨R_w²⟩`. -/
private lemma regular_freeT_hasDerivAt (b : ℝ) {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (freeT b) ((((2 * π)⁻¹ : ℝ) : ℂ) * ∫ p in (-π)..π, regRes b w p ^ 2) w := by
  have hpi := Real.pi_pos
  have e2 : (2 * π : ℂ)⁻¹ = (((2 * π)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  set P : ℂ → ℂ := fun w' =>
    (((2 * π)⁻¹ : ℝ) : ℂ) * ∫ p in (-π)..π, regRes b w' p * regRes b w p with hP
  have hPw : P w = (((2 * π)⁻¹ : ℝ) : ℂ) * ∫ p in (-π)..π, regRes b w p ^ 2 := by
    simp only [hP, sq]
  have hc := regular_res_cont (b := b) hw
  have hev : ∀ᶠ w' in 𝓝 w, w.im / 2 < w'.im :=
    (Complex.continuous_im.tendsto w).eventually (lt_mem_nhds (by linarith))
  -- slope of `freeT` is `P`
  have hslope : ∀ w', 0 < w'.im → freeT b w' - freeT b w = (w' - w) * P w' := by
    intro w' hw'
    have hc' := regular_res_cont (b := b) hw'
    have hfT : ∀ v, freeT b v = (((2 * π)⁻¹ : ℝ) : ℂ) * ∫ p in (-π)..π, regRes b v p :=
      fun v => by unfold freeT regRes; rw [e2]
    rw [hfT, hfT, ← mul_sub, ← intervalIntegral.integral_sub (f := fun p => regRes b w' p)
      (g := fun p => regRes b w p) (hc'.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    simp only [hP]
    rw [show (w' - w) * ((((2 * π)⁻¹ : ℝ) : ℂ) *
        ∫ p in (-π)..π, regRes b w' p * regRes b w p) = (((2 * π)⁻¹ : ℝ) : ℂ) *
        ∫ p in (-π)..π, (w' - w) * (regRes b w' p * regRes b w p) by
      rw [intervalIntegral.integral_const_mul]; ring]
    congr 1
    exact intervalIntegral.integral_congr fun p _ => regular_res_sub b hw hw' p
  -- continuity of `P` at `w`
  have hPc : Tendsto P (𝓝 w) (𝓝 (P w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun w' => ‖w' - w‖ * (2 / w.im * w.im⁻¹ * w.im⁻¹)) (𝓝 w) (𝓝 0) := by
      have hcont : Continuous fun w' : ℂ => ‖w' - w‖ * (2 / w.im * w.im⁻¹ * w.im⁻¹) := by
        fun_prop
      simpa using hcont.tendsto w
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    filter_upwards [hev] with w' hw2
    have hw' : 0 < w'.im := by linarith
    have hc' := regular_res_cont (b := b) hw'
    have e : P w' - P w = (((2 * π)⁻¹ : ℝ) : ℂ) * ∫ p in (-π)..π,
        (w' - w) * (regRes b w' p * regRes b w p * regRes b w p) := by
      simp only [hP]
      rw [← mul_sub, ← intervalIntegral.integral_sub (f := fun p => regRes b w' p * regRes b w p)
        (g := fun p => regRes b w p * regRes b w p) ((hc'.mul hc).intervalIntegrable _ _)
        ((hc.mul hc).intervalIntegrable _ _)]
      congr 2
      funext p
      rw [← sub_mul, regular_res_sub b hw hw' p]
      ring
    rw [e]
    apply regular_norm_avg_le
    intro p
    have hr1 : ‖regRes b w' p‖ ≤ 2 / w.im :=
      (regular_norm_res_le b hw' p).trans (by
        rw [show 2 / w.im = (w.im / 2)⁻¹ by rw [inv_div]]
        exact inv_anti₀ (by positivity) hw2.le)
    have hr2 := regular_norm_res_le b hw p
    rw [norm_mul, norm_mul, norm_mul]
    gcongr
  rw [hasDerivAt_iff_tendsto_slope, ← hPw]
  refine (hPc.mono_left nhdsWithin_le_nhds).congr' ?_
  rw [EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [hev] with w' hw2 hne
  have hw' : 0 < w'.im := by linarith
  have hne' : w' - w ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hne)
  rw [slope_def_field, hslope w' hw', mul_div_cancel_left₀ _ hne']

/-- First `z`-derivative bound of Lemma A.2 [bl:lem:regular]: `|m_g'| ≤ (2γ²(Im m_g)²)⁻¹`. -/
theorem mDyson_deriv_le (g : ℝ) (hg : 0 ≤ g) (z : ℂ) (hz : 0 < z.im) :
    ‖deriv (mDyson g) z‖ ≤ (2 * gammaG g ^ 2 * (mDyson g z).im ^ 2)⁻¹ := by
  obtain ⟨hm, hfix⟩ := mDyson_spec g hg z hz
  have hγ := regular_gamma_pos g
  set γ := gammaG g with hγdef
  set b := hopB g with hbdef
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hd : HasDerivAt (mDyson g) (deriv (mDyson g) z) z :=
    ((mDyson_differentiableOn g hg z hz).differentiableAt (hopen.mem_nhds hz)).hasDerivAt
  set d := deriv (mDyson g) z
  set W : ℂ → ℂ := fun z' => z' + (γ : ℂ) * mDyson g z' with hW
  have hw : 0 < (W z).im := by
    simp only [hW, Complex.add_im, Complex.im_ofReal_mul]; positivity
  have hWd : HasDerivAt W (1 + γ * d) z := (hasDerivAt_id z).add (hd.const_mul (γ : ℂ))
  set P := (((2 * π)⁻¹ : ℝ) : ℂ) * ∫ p in (-π)..π, regRes b (W z) p ^ 2 with hP
  have hcomp := (regular_freeT_hasDerivAt b hw).comp z hWd
  have heq : mDyson g =ᶠ[𝓝 z] (freeT b ∘ W) := by
    filter_upwards [hopen.mem_nhds hz] with z' hz'
    simp only [Function.comp, hW]
    rw [← dysonRHS_eq_freeT]
    exact (mDyson_spec g hg z' hz').2
  have hdu : d = P * (1 + γ * d) := hd.unique (hcomp.congr_of_eventuallyEq heq)
  have hid : d * (1 - γ * P) = P := by linear_combination hdu
  -- stability and Ward
  have hst := mDyson_stab g hg z hz
  have hward := mDyson_ward g hg z hz
  simp_rw [regular_integrand] at hst hward
  have hA : γ * ((2 * π)⁻¹ * ∫ p in (-π)..π, ‖regRes b (W z) p‖ ^ 2) ≤ 1 := by
    rw [hward, mul_div_assoc', div_le_one (by positivity)]
    linarith
  have hPn : ‖P‖ ≤ γ⁻¹ := by
    refine (regular_norm_avg_sq_le b (W z)).trans ?_
    set A := (2 * π)⁻¹ * ∫ p in (-π)..π, ‖regRes b (W z) p‖ ^ 2
    calc A = γ⁻¹ * (γ * A) := by field_simp
      _ ≤ γ⁻¹ * 1 := by gcongr
      _ = γ⁻¹ := mul_one _
  have hst' : 2 * γ * (mDyson g z).im ^ 2 ≤ (1 - γ * P).re := hst
  have hpos : 0 < 2 * γ * (mDyson g z).im ^ 2 := by positivity
  have hre : (1 - γ * P).re ≤ ‖1 - γ * P‖ := Complex.re_le_norm _
  have key : ‖d‖ * (2 * γ * (mDyson g z).im ^ 2) ≤ γ⁻¹ :=
    calc ‖d‖ * (2 * γ * (mDyson g z).im ^ 2) ≤ ‖d‖ * ‖1 - γ * P‖ := by
          gcongr; exact hst'.trans hre
      _ = ‖P‖ := by rw [← norm_mul, hid]
      _ ≤ γ⁻¹ := hPn
  rw [← le_div_iff₀ hpos] at key
  refine key.trans (le_of_eq ?_)
  field_simp

/-! ### Lower bounds on `Im m` from the quartic form of (1.9) [eq:dyson]

Write `s = −1/u = σ + iτ` and `w = z + γu = a + iβ`. The quartic `u²(w² − 4b²) = 1` reads
`s² = w² − 4b²`, and `E = Re z = a + γσ/|s|²`. -/

/-- Real form of the band-edge argument in the proof of Lemma A.2 [bl:lem:regular]: from
`s² = w² − 4b²` and `E = a + γσ/|s|²`, one has `E² + τ² ≥ 4b²`, and, if `τ ≤ |σ|`, a point
`X > 2b` with `X + γ (X² − 4b²)^{-1/2} ≤ |E| + 2τ`. -/
private lemma regular_core {b γ σ τ a β E : ℝ} (hb : 0 ≤ b) (hγ : 0 < γ) (hτ : 0 < τ)
    (hβ : 0 ≤ β) (h1 : σ ^ 2 - τ ^ 2 = a ^ 2 - β ^ 2 - 4 * b ^ 2) (h2 : σ * τ = a * β)
    (h3 : E = a + γ * σ / (σ ^ 2 + τ ^ 2)) :
    4 * b ^ 2 ≤ E ^ 2 + τ ^ 2 ∧ (τ ≤ |σ| → ∃ X : ℝ, 2 * b < X ∧
      X + γ / Real.sqrt (X ^ 2 - 4 * b ^ 2) ≤ |E| + 2 * τ) := by
  have hq : 0 < σ ^ 2 + τ ^ 2 := by positivity
  set q := σ ^ 2 + τ ^ 2 with hqdef
  have haσ : 0 ≤ a * σ := by
    have e : a * σ * τ = a ^ 2 * β := by linear_combination a * h2
    have : 0 ≤ a * σ * τ := by rw [e]; positivity
    exact nonneg_of_mul_nonneg_left this hτ
  set c := γ * σ / q with hc
  have hac : 0 ≤ a * c := by
    rw [hc, mul_div_assoc', ← mul_assoc, mul_comm a γ, mul_assoc]
    positivity
  have hE2 : a ^ 2 ≤ E ^ 2 := by rw [h3]; nlinarith [sq_nonneg c]
  refine ⟨by nlinarith [sq_nonneg σ, sq_nonneg β], fun hr => ?_⟩
  have hσ : 0 < |σ| := lt_of_lt_of_le hτ hr
  have hσ2 : σ ^ 2 = |σ| ^ 2 := (sq_abs σ).symm
  -- `|E| = |a| + γ|σ|/q`
  have hEabs : |a| + γ * |σ| / q ≤ |E| := by
    rcases lt_or_gt_of_ne (abs_pos.mp hσ) with hneg | hpos
    · have ha : a ≤ 0 := by nlinarith
      have hc0 : c ≤ 0 := by
        rw [hc]; exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hq.le
      rw [abs_of_nonpos ha, abs_of_neg hneg, h3, abs_of_nonpos (by linarith)]
      rw [hc]; ring_nf; rfl
    · have ha : 0 ≤ a := by nlinarith
      have hc0 : 0 ≤ c := by rw [hc]; positivity
      rw [abs_of_nonneg ha, abs_of_pos hpos, h3, abs_of_nonneg (by linarith)]
  set ρ := q / |σ| with hρ
  have hρ0 : 0 < ρ := by positivity
  refine ⟨Real.sqrt (ρ ^ 2 + 4 * b ^ 2), ?_, ?_⟩
  · rw [Real.lt_sqrt (by positivity)]
    nlinarith
  · have hX2 : Real.sqrt (ρ ^ 2 + 4 * b ^ 2) ^ 2 = ρ ^ 2 + 4 * b ^ 2 :=
      Real.sq_sqrt (by positivity)
    rw [hX2, show ρ ^ 2 + 4 * b ^ 2 - 4 * b ^ 2 = ρ ^ 2 by ring, Real.sqrt_sq hρ0.le]
    have hγρ : γ / ρ = γ * |σ| / q := by rw [hρ]; field_simp
    have hρ2 : ρ ^ 2 ≤ σ ^ 2 + 3 * τ ^ 2 := by
      rw [hρ, div_pow, div_le_iff₀ (by positivity), ← hσ2, hqdef]
      have : τ ^ 2 ≤ σ ^ 2 := by rw [hσ2]; exact pow_le_pow_left₀ hτ.le hr 2
      nlinarith [sq_nonneg τ]
    have hX : Real.sqrt (ρ ^ 2 + 4 * b ^ 2) ≤ |a| + 2 * τ := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
      nlinarith [abs_nonneg a, sq_nonneg β]
    rw [hγρ]
    linarith

/-- `e_g ≤ X + γ_g (X² − 4b²)^{-1/2}` for every `X > 2b`. -/
private lemma regular_bandEdge_le {g X : ℝ} (hg : 0 ≤ g) (hX : 2 * hopB g < X) :
    bandEdge g ≤ X + gammaG g / Real.sqrt (X ^ 2 - 4 * hopB g ^ 2) := by
  unfold bandEdge
  refine ciInf_le ⟨0, ?_⟩ (⟨X, hX⟩ : Set.Ioi (2 * hopB g))
  rintro _ ⟨y, rfl⟩
  have hy : 0 ≤ (y : ℝ) := le_trans (by linarith [regular_hopB_nonneg hg]) y.2.le
  have := regular_gamma_pos g
  positivity

/-- Lower bound on `Im u` for a root `u ∈ ℂ_+` of the quartic form of (1.9) [eq:dyson] at
`Im z ≥ 0` with `‖u‖ ≤ max{1, g}`: with `τ = Im(−1/u) > 0`, one has
`τ ≤ Im u (‖z + γ_g u‖² + 4b²)`, `4b² ≤ (Re z)² + τ²`, and either `e_g ≤ |Re z| + 2τ` or
`γ_g < 2τ²`. -/
private lemma regular_root_bounds (g : ℝ) (hg : 0 ≤ g) (z u : ℂ) (hz : 0 ≤ z.im)
    (hu : 0 < u.im)
    (hq : u ^ 2 * ((z + gammaG g * u) ^ 2 - 4 * (hopB g : ℂ) ^ 2) = 1)
    (hM : ‖u‖ ≤ max 1 g) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ u.im * (‖z + gammaG g * u‖ ^ 2 + 4 * hopB g ^ 2) ∧
      4 * hopB g ^ 2 ≤ z.re ^ 2 + τ ^ 2 ∧
      (bandEdge g ≤ |z.re| + 2 * τ ∨ gammaG g < 2 * τ ^ 2) := by
  have hγ := regular_gamma_pos g
  have hb := regular_hopB_nonneg hg
  set γ := gammaG g with hγdef
  set b := hopB g with hbdef
  have hu0 : u ≠ 0 := fun h => by rw [h] at hu; simp at hu
  have hnu : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu0
  set w := z + (γ : ℂ) * u with hw
  set s := -u⁻¹ with hs
  have hs2 : s ^ 2 = w ^ 2 - 4 * (b : ℂ) ^ 2 := by
    rw [hs, neg_sq, inv_pow]
    exact (eq_inv_of_mul_eq_one_right hq).symm
  have hus : u = -s⁻¹ := by rw [hs, inv_neg, inv_inv, neg_neg]
  have hns : Complex.normSq s = (Complex.normSq u)⁻¹ := by
    rw [hs, Complex.normSq_neg, Complex.normSq_inv]
  set σ := s.re with hσ
  set τ := s.im with hτ
  have hτu : τ = u.im / Complex.normSq u := by
    rw [hτ, hs, Complex.neg_im, Complex.inv_im]; ring
  have hτ0 : 0 < τ := by rw [hτu]; positivity
  have hnsq : Complex.normSq s = σ ^ 2 + τ ^ 2 := by rw [Complex.normSq_apply]; ring
  have hns0 : 0 < Complex.normSq s := by rw [hns]; positivity
  -- real and imaginary parts
  have hre := congrArg Complex.re hs2
  have him := congrArg Complex.im hs2
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat] at hre him
  have hwre : w.re = z.re + γ * u.re := by simp [hw]
  have hwim : w.im = z.im + γ * u.im := by simp [hw]
  have hure : u.re = -σ / (σ ^ 2 + τ ^ 2) := by
    rw [hus, Complex.neg_re, Complex.inv_re, hnsq]; ring
  have hβ : 0 ≤ w.im := by rw [hwim]; positivity
  have h1 : σ ^ 2 - τ ^ 2 = w.re ^ 2 - w.im ^ 2 - 4 * b ^ 2 := by
    rw [hσ, hτ]; linear_combination hre
  have h2 : σ * τ = w.re * w.im := by rw [hσ, hτ]; linear_combination him / 2
  have h3 : z.re = w.re + γ * σ / (σ ^ 2 + τ ^ 2) := by
    rw [hwre, hure]; ring
  obtain ⟨hA, hB⟩ := regular_core hb hγ hτ0 hβ h1 h2 h3
  refine ⟨τ, hτ0, ?_, hA, ?_⟩
  · -- `τ = Im u · |s|²` and `|s|² = |w² − 4b²| ≤ ‖w‖² + 4b²`
    have e : τ = u.im * Complex.normSq s := by rw [hτu, hns]; ring
    have hle : Complex.normSq s ≤ ‖w‖ ^ 2 + 4 * b ^ 2 := by
      rw [← Complex.sq_norm, ← norm_pow, hs2]
      calc ‖w ^ 2 - 4 * (b : ℂ) ^ 2‖ ≤ ‖w ^ 2‖ + ‖4 * (b : ℂ) ^ 2‖ := norm_sub_le _ _
        _ = ‖w‖ ^ 2 + 4 * b ^ 2 := by
          rw [norm_pow, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
          norm_num
    rw [e]
    exact mul_le_mul_of_nonneg_left hle hu.le
  · rcases le_or_gt τ |σ| with hr | hr
    · obtain ⟨X, hX, hXle⟩ := hB hr
      exact Or.inl ((regular_bandEdge_le hg hX).trans hXle)
    · right
      -- `|s|² = 1/|u|² ≥ (max 1 g)⁻² = γ`
      have hγs : γ ≤ Complex.normSq s := by
        rw [hns, hγdef, gammaG]
        refine inv_anti₀ hnu ?_
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) hM 2
      have : σ ^ 2 < τ ^ 2 := by
        rw [← sq_abs σ]; exact pow_lt_pow_left₀ hr (abs_nonneg _) (by norm_num)
      linarith [hnsq]

/-- A lower bound `t ≤ τ` on `τ = Im(−1/u)` gives `Im u ≥ t/((K + 2)² + 4)` when `|Re z| ≤ K`
and `0 ≤ Im z ≤ 1`. -/
private lemma regular_im_ge (g : ℝ) (hg : 0 ≤ g) (z u : ℂ) (hz : 0 ≤ z.im) (hz1 : z.im ≤ 1)
    (hu : 0 < u.im)
    (hq : u ^ 2 * ((z + gammaG g * u) ^ 2 - 4 * (hopB g : ℂ) ^ 2) = 1)
    (hM : ‖u‖ ≤ max 1 g) {K t : ℝ} (hK : |z.re| ≤ K)
    (ht : ∀ τ : ℝ, 0 < τ → 4 * hopB g ^ 2 ≤ z.re ^ 2 + τ ^ 2 →
      (bandEdge g ≤ |z.re| + 2 * τ ∨ gammaG g < 2 * τ ^ 2) → t ≤ τ) :
    t / ((K + 2) ^ 2 + 4) ≤ u.im := by
  obtain ⟨τ, hτ, hτle, hA, hB⟩ := regular_root_bounds g hg z u hz hu hq hM
  have htτ := ht τ hτ hA hB
  have hb0 := regular_hopB_nonneg hg
  have hb1 := regular_hopB_le_one g
  have hK0 : 0 ≤ K := (abs_nonneg _).trans hK
  have hw : ‖z + gammaG g * u‖ ≤ K + 2 := by
    have h1 : ‖z‖ ≤ K + 1 := by
      have := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_nonneg hz] at this
      linarith
    have h2 : ‖(gammaG g : ℂ) * u‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (regular_gamma_pos g).le]
      exact regular_gamma_mul_le hM
    calc ‖z + gammaG g * u‖ ≤ ‖z‖ + ‖(gammaG g : ℂ) * u‖ := norm_add_le _ _
      _ ≤ K + 2 := by linarith
  have hQ : ‖z + gammaG g * u‖ ^ 2 + 4 * hopB g ^ 2 ≤ (K + 2) ^ 2 + 4 := by
    have : ‖z + gammaG g * u‖ ^ 2 ≤ (K + 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  calc t ≤ τ := htτ
    _ ≤ u.im * (‖z + gammaG g * u‖ ^ 2 + 4 * hopB g ^ 2) := hτle
    _ ≤ u.im * ((K + 2) ^ 2 + 4) := mul_le_mul_of_nonneg_left hQ hu.le

/-! ### Lemma A.2 [bl:lem:regular] in quantile form -/

/-- Quantile margin: `κ ≤ F_g(−|E|)` forces `πκ ≤ max{1, g} (e_g − |E|)`, since by (1.10)
[eq:distribution] the density `π⁻¹ Im m_g(t + i0)` is at most `π⁻¹ max{1, g}` and vanishes for
`|t| ≥ e_g`. -/
private lemma regular_margin (g : ℝ) (hg : 0 ≤ g) {κ E : ℝ} (hκ : 0 < κ)
    (h : κ ≤ Fdist g (-|E|)) : π * κ ≤ max 1 g * (bandEdge g - |E|) := by
  rw [Fdist_eq_integral_bdry g hg] at h
  set e := bandEdge g with he
  set M := max 1 g with hMdef
  set x := -|E| with hx
  have hM := regular_max_pos g
  have hle : ∫ t in Set.Iic x, (mDysonBdry g t).im ≤
      ∫ t in Set.Iic x, (Set.Ioc (-e) x).indicator (fun _ => M) t := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · exact Eventually.of_forall fun t => (mDysonBdry_norm_le g hg t).2
    · refine Integrable.integrableOn ?_
      exact (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
    · refine ae_restrict_of_forall_mem measurableSet_Iic fun t ht => ?_
      by_cases hmem : t ∈ Set.Ioc (-e) x
      · rw [Set.indicator_of_mem hmem]
        exact (Complex.im_le_norm _).trans (mDysonBdry_norm_le g hg t).1
      · rw [Set.indicator_of_notMem hmem]
        have hte : t ≤ -e := by
          by_contra hc
          exact hmem ⟨not_le.mp hc, ht⟩
        have hnot : ¬ |t| < e := by
          rw [not_lt, abs_of_nonpos (by linarith [(bandEdge_ge_two g hg).1])]
          linarith
        exact not_lt.mp fun hpos => hnot ((mDysonBdry_im_pos_iff g hg t).1 hpos)
  rw [setIntegral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul,
    Set.inter_eq_right.mpr Set.Ioc_subset_Iic_self, Real.volume_real_Ioc] at hle
  have hpi := Real.pi_pos
  have h' : π * κ ≤ max (x - -e) 0 * M := by
    have := mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hle
      (inv_nonneg.mpr hpi.le))) hpi.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul] at this
  rcases le_total (x - -e) 0 with h0 | h0
  · rw [max_eq_right h0, zero_mul] at h'
    nlinarith
  · rw [max_eq_left h0] at h'
    rw [hx] at h'
    linarith

/-- Lemma A.2 [bl:lem:regular], quantile form at `γ = γ_g`: (A.7) [bl:eq:regular-domain] and
the lower bound of (A.8) [bl:eq:regular-bounds]. -/
theorem regular_quantile (C κ : ℝ) (hC : 0 < C) (hκ : 0 < κ ∧ κ < 1 / 2) :
    ∃ b a : ℝ, 0 < b ∧ 0 < a ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ x : ℝ,
      (∃ E : ℝ, κ ≤ Fdist g (-|E|) ∧ |x - E| ≤ b) →
      |x| ≤ 2 * C + 2 ∧ |x| + b ≤ bandEdge g ∧ a ≤ (mDysonBdry g x).im ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → a ≤ (mDyson g (x + η * I)).im := by
  have hpi := Real.pi_pos
  set M := max 1 C with hMdef
  have hM : 0 < M := regular_max_pos C
  set b₀ := π * κ / (2 * M) with hb₀
  have hb₀0 : 0 < b₀ := by have := hκ.1; positivity
  set t := min (b₀ / 2) (1 / (2 * M)) with htdef
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  refine ⟨b₀, t / ((2 * C + 2 + 2) ^ 2 + 4), hb₀0, by positivity, ?_⟩
  rintro g hg hgC x ⟨E, hFE, hxE⟩
  have hmg : max 1 g ≤ M := max_le_max le_rfl hgC
  have hmg0 := regular_max_pos g
  have hmarg := regular_margin g hg hκ.1 hFE
  have hpos : 0 < bandEdge g - |E| := by
    by_contra hc
    rw [not_lt] at hc
    have : max 1 g * (bandEdge g - |E|) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmg0.le hc
    nlinarith [hκ.1]
  have h2b : 2 * b₀ ≤ bandEdge g - |E| := by
    have h1 : π * κ ≤ M * (bandEdge g - |E|) :=
      hmarg.trans (mul_le_mul_of_nonneg_right hmg hpos.le)
    rw [hb₀, show 2 * (π * κ / (2 * M)) = π * κ / M by field_simp, div_le_iff₀ hM]
    linarith
  have hxE' : |x| ≤ |E| + b₀ := by
    have := abs_sub_abs_le_abs_sub x E
    linarith
  have hxb : |x| + b₀ ≤ bandEdge g := by linarith
  have heC : bandEdge g ≤ 2 * C + 2 := by
    refine (bandEdge_le g hg).trans ?_
    rcases le_total g 1 with h1 | h1
    · rw [max_eq_left h1, div_one]; linarith
    · have := support_bound_le_four g hg
      linarith
  have hx : |x| ≤ 2 * C + 2 := by linarith
  have hγM : (M ^ 2)⁻¹ ≤ gammaG g := by
    unfold gammaG
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hmg0.le hmg 2)
  have htau : ∀ τ : ℝ, 0 < τ → (bandEdge g ≤ |x| + 2 * τ ∨ gammaG g < 2 * τ ^ 2) → t ≤ τ := by
    intro τ hτ hB
    rcases hB with hB | hB
    · exact (min_le_left _ _).trans (by linarith)
    · refine (min_le_right _ _).trans ?_
      by_contra hc
      rw [not_le] at hc
      have h1 : τ * (2 * M) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hc
      have h2 : 1 ≤ gammaG g * M ^ 2 := by
        rw [← inv_mul_cancel₀ (by positivity : M ^ 2 ≠ 0)]
        exact mul_le_mul_of_nonneg_right hγM (by positivity)
      have h3 : gammaG g * M ^ 2 ≤ 2 * τ ^ 2 * M ^ 2 :=
        mul_le_mul_of_nonneg_right hB.le (by positivity)
      have h4 : τ * M < 1 / 2 := by linarith
      have h5 : (τ * M) ^ 2 < 1 / 4 := by nlinarith [mul_pos hτ hM]
      nlinarith
  refine ⟨hx, hxb, ?_, fun η hη hη1 => ?_⟩
  · have hxe : |x| < bandEdge g := by linarith
    obtain ⟨hm, -⟩ := mDysonBdry_spec g hg x hxe
    refine regular_im_ge g hg (x : ℂ) _ (by simp) (by simp) hm (mDysonBdry_quartic g hg x)
      (mDysonBdry_norm_le g hg x).1 (K := 2 * C + 2) (by simpa using hx) ?_
    intro τ hτ _ hB
    simp only [Complex.ofReal_re] at hB
    exact htau τ hτ hB
  · have hz : 0 < ((x : ℂ) + η * I).im := by simpa using hη
    obtain ⟨hm, hfix⟩ := mDyson_spec g hg _ hz
    have hq := (dyson_iff_quartic g hg _ hz _ hm).1 hfix
    refine regular_im_ge g hg ((x : ℂ) + η * I) _ hz.le (by simpa using hη1) hm hq
      (mDyson_norm_le_max g hg _ hz) (K := 2 * C + 2) (by simpa using hx) ?_
    intro τ hτ _ hB
    have hre : ((x : ℂ) + η * I).re = x := by simp
    rw [hre] at hB
    exact htau τ hτ hB

end LSBA
