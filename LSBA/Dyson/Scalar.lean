import LSBA.Model.Basic

/-!
# The Dyson equation on the line

The right side of (1.9) [eq:dyson], its unique solution `m_g` in `ℂ_+`, the free transforms of the
law of `2b cos p` (integral and finite Fourier average, (A.1) [bl:eq:physical]), and the basic
bounds (A.6) [da:eq:ward].
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- Right side of (1.9) [eq:dyson]. -/
def dysonRHS (g : ℝ) (z u : ℂ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ p in (-π)..π,
    ((2 * g * Real.cos p / max 1 g : ℝ) - z - u / ((max 1 g : ℝ) : ℂ) ^ 2)⁻¹

/-- `m_g(z)`: the unique solution in `ℂ_+` (junk value `0` if there is none). -/
def mDyson (g : ℝ) (z : ℂ) : ℂ :=
  if h : ∃! u : ℂ, 0 < u.im ∧ u = dysonRHS g z u then h.exists.choose else 0

/-- Hopping `√γ_g g = g / max{1,g}`, (5.1) [fo:eq:flow]. -/
def hopB (g : ℝ) : ℝ := g / max 1 g

/-- Free transform `⟨(2b cos p - w)⁻¹⟩` of the law of `2b cos p`, (A.1) [bl:eq:physical]
(with `b = √γ g`). -/
def freeT (b : ℝ) (w : ℂ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ p in (-π)..π, ((2 * b * Real.cos p : ℝ) - w)⁻¹

/-- Finite Fourier average `L⁻¹ Σ_{p ∈ (2π/L)ℤ_L} (2b cos p - w)⁻¹`, (A.1) [bl:eq:physical]. -/
def freeTL (b : ℝ) (L : ℕ) (w : ℂ) : ℂ :=
  (L : ℂ)⁻¹ * ∑ k : Fin L, ((2 * b * Real.cos (2 * π * k / L) : ℝ) - w)⁻¹

/-! ### Averages `⟨·⟩ = (2π)⁻¹ ∫_{-π}^{π}` of continuous functions -/

/-- Average of a complex function over `[-π, π]`. -/
private def avgC (f : ℝ → ℂ) : ℂ := (2 * π : ℂ)⁻¹ * ∫ p in (-π)..π, f p

/-- Average of a real function over `[-π, π]`. -/
private def avgR (f : ℝ → ℝ) : ℝ := (2 * π)⁻¹ * ∫ p in (-π)..π, f p

private lemma avgR_const (c : ℝ) : avgR (fun _ => c) = c := by
  have hπ := Real.pi_pos
  unfold avgR
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

private lemma avgC_const (c : ℂ) : avgC (fun _ => c) = c := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold avgC
  rw [intervalIntegral.integral_const, Complex.real_smul]
  push_cast
  field_simp
  ring

private lemma avgR_mono {f h : ℝ → ℝ} (hf : Continuous f) (hh : Continuous h)
    (hle : ∀ p, f p ≤ h p) : avgR f ≤ avgR h := by
  unfold avgR
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    (hf.intervalIntegrable _ _) (hh.intervalIntegrable _ _) (fun p _ => hle p)

private lemma avgR_add {f h : ℝ → ℝ} (hf : Continuous f) (hh : Continuous h) :
    avgR (fun p => f p + h p) = avgR f + avgR h := by
  unfold avgR
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hh.intervalIntegrable _ _)]
  ring

private lemma avgR_const_mul (c : ℝ) (f : ℝ → ℝ) : avgR (fun p => c * f p) = c * avgR f := by
  unfold avgR
  rw [intervalIntegral.integral_const_mul]
  ring

private lemma avgC_add {f h : ℝ → ℂ} (hf : Continuous f) (hh : Continuous h) :
    avgC (fun p => f p + h p) = avgC f + avgC h := by
  unfold avgC
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hh.intervalIntegrable _ _)]
  ring

private lemma avgC_sub {f h : ℝ → ℂ} (hf : Continuous f) (hh : Continuous h) :
    avgC (fun p => f p - h p) = avgC f - avgC h := by
  unfold avgC
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hh.intervalIntegrable _ _)]
  ring

private lemma avgC_const_mul (c : ℂ) (f : ℝ → ℂ) : avgC (fun p => c * f p) = c * avgC f := by
  unfold avgC
  rw [intervalIntegral.integral_const_mul]
  ring

private lemma norm_two_pi : ‖(2 * π : ℂ)‖ = 2 * π := by
  rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

private lemma norm_avgC_le_const {f : ℝ → ℂ} {C : ℝ} (h : ∀ p, ‖f p‖ ≤ C) :
    ‖avgC f‖ ≤ C := by
  have hπ := Real.pi_pos
  unfold avgC
  rw [norm_mul, norm_inv, norm_two_pi]
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := -π) (b := π) (f := f)
    (fun p _ => h p)
  rw [show |π - -π| = 2 * π by rw [abs_of_pos (by linarith)]; ring] at h1
  calc (2 * π)⁻¹ * ‖∫ p in (-π)..π, f p‖ ≤ (2 * π)⁻¹ * (C * (2 * π)) := by gcongr
    _ = C := by field_simp

private lemma norm_avgC_le (f : ℝ → ℂ) :
    ‖avgC f‖ ≤ avgR (fun p => ‖f p‖) := by
  have hπ := Real.pi_pos
  unfold avgC avgR
  rw [norm_mul, norm_inv, norm_two_pi]
  gcongr
  exact intervalIntegral.norm_integral_le_integral_norm (by linarith)

private lemma im_avgC {f : ℝ → ℂ} (hf : Continuous f) :
    (avgC f).im = avgR (fun p => (f p).im) := by
  unfold avgC avgR
  rw [show (2 * π : ℂ)⁻¹ = (((2 * π)⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul]
  congr 1
  exact (intervalIntegral.intervalIntegral_im (hf.intervalIntegrable _ _)).symm

/-- Cauchy–Schwarz for averages: `‖⟨f h⟩‖² ≤ ⟨‖f‖²⟩ ⟨‖h‖²⟩`. -/
private lemma avg_cs {f h : ℝ → ℂ} (hf : Continuous f) (hh : Continuous h)
    (hA : 0 < avgR (fun p => ‖f p‖ ^ 2)) :
    ‖avgC (fun p => f p * h p)‖ ^ 2 ≤
      avgR (fun p => ‖f p‖ ^ 2) * avgR (fun p => ‖h p‖ ^ 2) := by
  set A := avgR (fun p => ‖f p‖ ^ 2) with hAdef
  set B := avgR (fun p => ‖h p‖ ^ 2) with hBdef
  set C := ‖avgC (fun p => f p * h p)‖ with hCdef
  have hB : 0 ≤ B := by
    have := avgR_mono (f := fun _ => (0 : ℝ)) (h := fun p => ‖h p‖ ^ 2) continuous_const
      (by fun_prop) (fun p => by positivity)
    rwa [avgR_const] at this
  have key : ∀ t : ℝ, 0 < t → 2 * t * C ≤ t ^ 2 * A + B := by
    intro t ht
    have h1 : C ≤ avgR (fun p => ‖f p * h p‖) := norm_avgC_le _
    have h2 : avgR (fun p => (2 * t) * ‖f p * h p‖) ≤
        avgR (fun p => t ^ 2 * ‖f p‖ ^ 2 + ‖h p‖ ^ 2) :=
      avgR_mono (by fun_prop) (by fun_prop) (fun p => by
        rw [norm_mul]; nlinarith [sq_nonneg (t * ‖f p‖ - ‖h p‖)])
    rw [avgR_const_mul, avgR_add (by fun_prop) (by fun_prop), avgR_const_mul] at h2
    nlinarith
  rcases (norm_nonneg _ : (0 : ℝ) ≤ C).eq_or_lt with h0 | h0
  · have hC0 : C = 0 := by rw [hCdef]; exact h0.symm
    rw [hC0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg hA.le hB
  · have h3 := key (C / A) (div_pos h0 hA)
    have h4 : C ^ 2 / A ≤ B := by
      have e1 : 2 * (C / A) * C = 2 * (C ^ 2 / A) := by ring
      have e2 : (C / A) ^ 2 * A = C ^ 2 / A := by field_simp
      rw [e1, e2] at h3
      linarith
    rwa [div_le_iff₀ hA, mul_comm] at h4

/-! ### The resolvent `R_w(p) = (2b cos p - w)⁻¹` -/

/-- Integrand of `freeT b w`. -/
private def res (b : ℝ) (w : ℂ) (p : ℝ) : ℂ := ((2 * b * Real.cos p : ℝ) - w)⁻¹

private lemma freeT_eq_avgC (b : ℝ) (w : ℂ) : freeT b w = avgC (res b w) := rfl

private lemma res_base_ne {b : ℝ} {w : ℂ} (hw : 0 < w.im) (p : ℝ) :
    ((2 * b * Real.cos p : ℝ) : ℂ) - w ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

private lemma continuous_res {b : ℝ} {w : ℂ} (hw : 0 < w.im) : Continuous (res b w) := by
  unfold res
  exact Continuous.inv₀ (by fun_prop) (res_base_ne hw)

private lemma norm_res_le (b : ℝ) {w : ℂ} (hw : 0 < w.im) (p : ℝ) : ‖res b w p‖ ≤ w.im⁻¹ := by
  unfold res
  rw [norm_inv]
  apply inv_anti₀ hw
  calc w.im = |(((2 * b * Real.cos p : ℝ) : ℂ) - w).im| := by simp [abs_of_pos hw]
    _ ≤ ‖((2 * b * Real.cos p : ℝ) : ℂ) - w‖ := Complex.abs_im_le_norm _

/-- Pointwise Ward identity: `Im R_w = Im w · |R_w|²`. -/
private lemma im_res (b : ℝ) (w : ℂ) (p : ℝ) : (res b w p).im = w.im * ‖res b w p‖ ^ 2 := by
  unfold res
  rw [Complex.inv_im, Complex.sq_norm, Complex.normSq_inv]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  ring

/-- Resolvent identity `R_w - R_{w'} = (w - w') R_w R_{w'}`. -/
private lemma res_sub_res (b : ℝ) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) (p : ℝ) :
    res b w p - res b w' p = (w - w') * (res b w p * res b w' p) := by
  unfold res
  have h1 := res_base_ne (b := b) hw p
  have h2 := res_base_ne (b := b) hw' p
  field_simp
  ring

private lemma norm_res_ge {b : ℝ} {w : ℂ} (hw : 0 < w.im) (p : ℝ) :
    (2 * |b| + ‖w‖)⁻¹ ≤ ‖res b w p‖ := by
  unfold res
  rw [norm_inv]
  apply inv_anti₀ (norm_pos_iff.mpr (res_base_ne hw p))
  calc ‖((2 * b * Real.cos p : ℝ) : ℂ) - w‖ ≤ ‖((2 * b * Real.cos p : ℝ) : ℂ)‖ + ‖w‖ :=
        norm_sub_le _ _
    _ ≤ 2 * |b| + ‖w‖ := by
        gcongr
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
        have := Real.abs_cos_le_one p
        have := abs_nonneg b
        norm_num
        nlinarith

/-- `⟨|R_w|²⟩`. -/
private def nsq (b : ℝ) (w : ℂ) : ℝ := avgR (fun p => ‖res b w p‖ ^ 2)

private lemma freeT_sub_freeT (b : ℝ) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) :
    freeT b w - freeT b w' = (w - w') * avgC (fun p => res b w p * res b w' p) := by
  rw [freeT_eq_avgC, freeT_eq_avgC, ← avgC_sub (continuous_res hw) (continuous_res hw'),
    ← avgC_const_mul]
  congr 1
  funext p
  exact res_sub_res b hw hw' p

/-- Ward identity for `freeT`: `Im f(w) = Im w · ⟨|R_w|²⟩`. -/
private lemma im_freeT (b : ℝ) {w : ℂ} (hw : 0 < w.im) : (freeT b w).im = w.im * nsq b w := by
  rw [freeT_eq_avgC, im_avgC (continuous_res hw), nsq, ← avgR_const_mul]
  congr 1
  funext p
  exact im_res b w p

private lemma norm_freeT_le (b : ℝ) {w : ℂ} (hw : 0 < w.im) : ‖freeT b w‖ ≤ w.im⁻¹ :=
  norm_avgC_le_const (norm_res_le b hw)

private lemma nsq_ge (b : ℝ) {w : ℂ} (hw : 0 < w.im) : ((2 * |b| + ‖w‖) ^ 2)⁻¹ ≤ nsq b w := by
  have hpos : 0 < 2 * |b| + ‖w‖ := by
    have : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw)
    linarith [abs_nonneg b]
  calc ((2 * |b| + ‖w‖) ^ 2)⁻¹ = avgR (fun _ => ((2 * |b| + ‖w‖) ^ 2)⁻¹) := (avgR_const _).symm
    _ ≤ nsq b w := by
      apply avgR_mono continuous_const (by have := continuous_res (b := b) hw; fun_prop)
      intro p
      rw [← inv_pow]
      exact pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) (norm_res_ge hw p) 2

private lemma nsq_pos (b : ℝ) {w : ℂ} (hw : 0 < w.im) : 0 < nsq b w := by
  have hpos : 0 < 2 * |b| + ‖w‖ := by
    have : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw)
    linarith [abs_nonneg b]
  exact lt_of_lt_of_le (inv_pos.mpr (pow_pos hpos 2)) (nsq_ge b hw)

private lemma norm_avg_resres_le (b : ℝ) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) :
    ‖avgC (fun p => res b w p * res b w' p)‖ ≤ w.im⁻¹ * w'.im⁻¹ :=
  norm_avgC_le_const (fun p => by
    rw [norm_mul]
    exact mul_le_mul (norm_res_le b hw p) (norm_res_le b hw' p) (norm_nonneg _)
      (inv_nonneg.mpr hw.le))

private lemma cs_resres (b : ℝ) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) :
    ‖avgC (fun p => res b w p * res b w' p)‖ ^ 2 ≤ nsq b w * nsq b w' :=
  avg_cs (continuous_res hw) (continuous_res hw') (nsq_pos b hw)

private lemma normsq_freeT_le (b : ℝ) {w : ℂ} (hw : 0 < w.im) : ‖freeT b w‖ ^ 2 ≤ nsq b w := by
  have := avg_cs (h := fun _ => (1 : ℂ)) (continuous_res (b := b) hw) continuous_const
    (nsq_pos b hw)
  simp only [mul_one, norm_one, one_pow] at this
  rw [avgR_const, mul_one] at this
  exact this

/-! ### The parameters `γ_g = max{1,g}⁻²` and `b = g / max{1,g}` -/

private lemma max_one_pos (g : ℝ) : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)

private lemma gammaG_pos (g : ℝ) : 0 < gammaG g := by
  have := max_one_pos g
  unfold gammaG
  positivity

private lemma gammaG_le_one (g : ℝ) : gammaG g ≤ 1 := by
  unfold gammaG
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_max_left _ _))

private lemma gammaG_mul_sq (g : ℝ) : gammaG g * (max 1 g) ^ 2 = 1 := by
  have := (max_one_pos g).ne'
  unfold gammaG
  field_simp

private lemma abs_hopB_le_one {g : ℝ} (hg : 0 ≤ g) : |hopB g| ≤ 1 := by
  unfold hopB
  rw [abs_of_nonneg (div_nonneg hg (max_one_pos g).le)]
  exact div_le_one_of_le₀ (le_max_right _ _) (max_one_pos g).le

/-- `2 g / max{1,g} + γ_g max{1,g} = (2g + 1) / max{1,g} ≤ 3`. -/
private lemma hop_gamma_le_three (g : ℝ) : 2 * hopB g + gammaG g * max 1 g ≤ 3 := by
  unfold hopB gammaG
  rcases le_total g 1 with h | h
  · rw [max_eq_left h]
    norm_num
    linarith
  · rw [max_eq_right h]
    have hg0 : 0 < g := by linarith
    have e : 2 * (g / g) + (g ^ 2)⁻¹ * g = 2 + g⁻¹ := by field_simp
    rw [e]
    have : g⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
    linarith

/-! ### The right side of (1.9) [eq:dyson] as a map on `ℂ_+` -/

theorem dysonRHS_eq_freeT (g : ℝ) (z u : ℂ) :
    dysonRHS g z u = freeT (hopB g) (z + gammaG g * u) := by
  unfold dysonRHS freeT hopB gammaG
  congr 1
  refine intervalIntegral.integral_congr (fun p _ => ?_)
  congr 1
  push_cast
  ring

private lemma im_shift (g : ℝ) (z u : ℂ) :
    (z + gammaG g * u).im = z.im + gammaG g * u.im := by
  simp

private lemma im_shift_pos (g : ℝ) {z u : ℂ} (hz : 0 < z.im) (hu : 0 ≤ u.im) :
    0 < (z + gammaG g * u).im := by
  rw [im_shift]
  have := gammaG_pos g
  positivity

/-- Ward identity for the right side of (1.9) [eq:dyson]: `Im Φ(u) = (Im z + γ Im u) ⟨|R|²⟩`. -/
private lemma dyson_im_eq (g : ℝ) {z u : ℂ} (hz : 0 < z.im) (hu : 0 ≤ u.im) :
    (dysonRHS g z u).im = (z.im + gammaG g * u.im) * nsq (hopB g) (z + gammaG g * u) := by
  rw [dysonRHS_eq_freeT, im_freeT _ (im_shift_pos g hz hu), im_shift]

private lemma dyson_im_pos (g : ℝ) {z u : ℂ} (hz : 0 < z.im) (hu : 0 ≤ u.im) :
    0 < (dysonRHS g z u).im := by
  rw [dyson_im_eq g hz hu]
  exact mul_pos (by rw [← im_shift]; exact im_shift_pos g hz hu)
    (nsq_pos _ (im_shift_pos g hz hu))

private lemma dyson_norm_le (g : ℝ) {z u : ℂ} (hz : 0 < z.im) (hu : 0 ≤ u.im) :
    ‖dysonRHS g z u‖ ≤ z.im⁻¹ := by
  rw [dysonRHS_eq_freeT]
  refine (norm_freeT_le _ (im_shift_pos g hz hu)).trans (inv_anti₀ hz ?_)
  rw [im_shift]
  have := gammaG_pos g
  nlinarith

private lemma dyson_im_ge (g : ℝ) (hg : 0 ≤ g) {z u : ℂ} (hz : 0 < z.im) (hu : 0 ≤ u.im) :
    z.im * ((2 + ‖z‖ + ‖u‖) ^ 2)⁻¹ ≤ (dysonRHS g z u).im := by
  have hw := im_shift_pos g hz hu
  rw [dyson_im_eq g hz hu]
  have hγ := gammaG_pos g
  have hγ1 := gammaG_le_one g
  have h1 := nsq_ge (hopB g) hw
  have h2 : 2 * |hopB g| + ‖z + gammaG g * u‖ ≤ 2 + ‖z‖ + ‖u‖ := by
    have hb := abs_hopB_le_one hg
    have : ‖z + gammaG g * u‖ ≤ ‖z‖ + ‖u‖ := by
      calc ‖z + gammaG g * u‖ ≤ ‖z‖ + ‖(gammaG g : ℂ) * u‖ := norm_add_le _ _
        _ = ‖z‖ + gammaG g * ‖u‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le]
        _ ≤ ‖z‖ + ‖u‖ := by nlinarith [norm_nonneg u]
    linarith
  have hpos : 0 < 2 * |hopB g| + ‖z + gammaG g * u‖ := by
    have : 0 < ‖z + gammaG g * u‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw)
    linarith [abs_nonneg (hopB g)]
  have h3 : ((2 + ‖z‖ + ‖u‖) ^ 2)⁻¹ ≤ ((2 * |hopB g| + ‖z + gammaG g * u‖) ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le h2 2)
  have h4 : 0 ≤ nsq (hopB g) (z + gammaG g * u) := (nsq_pos _ hw).le
  have h5 : 0 ≤ gammaG g * u.im := by positivity
  calc z.im * ((2 + ‖z‖ + ‖u‖) ^ 2)⁻¹ ≤ z.im * nsq (hopB g) (z + gammaG g * u) :=
        mul_le_mul_of_nonneg_left (h3.trans h1) hz.le
    _ ≤ (z.im + gammaG g * u.im) * nsq (hopB g) (z + gammaG g * u) := by
        gcongr; linarith

/-- Contraction estimate of the proof of uniqueness in (A.6) [da:eq:ward]:
`|Φu - Φv|² (Im z + γ Im u)(Im z + γ Im v) ≤ γ² |u - v|² Im Φu Im Φv`. -/
private lemma dyson_contr (g : ℝ) {z u v : ℂ} (hz : 0 < z.im) (hu : 0 ≤ u.im) (hv : 0 ≤ v.im) :
    ‖dysonRHS g z u - dysonRHS g z v‖ ^ 2 *
        ((z.im + gammaG g * u.im) * (z.im + gammaG g * v.im)) ≤
      gammaG g ^ 2 * ‖u - v‖ ^ 2 * ((dysonRHS g z u).im * (dysonRHS g z v).im) := by
  have hwu := im_shift_pos g hz hu
  have hwv := im_shift_pos g hz hv
  rw [dyson_im_eq g hz hu, dyson_im_eq g hz hv, dysonRHS_eq_freeT, dysonRHS_eq_freeT,
    freeT_sub_freeT _ hwu hwv]
  have hcs := cs_resres (hopB g) hwu hwv
  have e : z + gammaG g * u - (z + gammaG g * v) = (gammaG g : ℂ) * (u - v) := by ring
  rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (gammaG_pos g).le]
  rw [← im_shift, ← im_shift]
  have h1 : 0 ≤ (z + gammaG g * u).im * (z + gammaG g * v).im := by positivity
  have h2 : 0 ≤ gammaG g ^ 2 * ‖u - v‖ ^ 2 := by positivity
  calc (gammaG g * ‖u - v‖ * ‖avgC fun p => res (hopB g) (z + gammaG g * u) p *
          res (hopB g) (z + gammaG g * v) p‖) ^ 2 *
        ((z + gammaG g * u).im * (z + gammaG g * v).im)
      = gammaG g ^ 2 * ‖u - v‖ ^ 2 * ‖avgC fun p => res (hopB g) (z + gammaG g * u) p *
          res (hopB g) (z + gammaG g * v) p‖ ^ 2 *
        ((z + gammaG g * u).im * (z + gammaG g * v).im) := by ring
    _ ≤ gammaG g ^ 2 * ‖u - v‖ ^ 2 *
          (nsq (hopB g) (z + gammaG g * u) * nsq (hopB g) (z + gammaG g * v)) *
        ((z + gammaG g * u).im * (z + gammaG g * v).im) := by gcongr
    _ = _ := by ring

/-- Lipschitz bound `|Φu - Φv| ≤ (Im z)⁻² |u - v|` on the closed upper half-plane. -/
private lemma dyson_lip (g : ℝ) {z u v : ℂ} (hz : 0 < z.im) (hu : 0 ≤ u.im) (hv : 0 ≤ v.im) :
    ‖dysonRHS g z u - dysonRHS g z v‖ ≤ z.im⁻¹ ^ 2 * ‖u - v‖ := by
  have hwu := im_shift_pos g hz hu
  have hwv := im_shift_pos g hz hv
  have hγ := gammaG_pos g
  have hγ1 := gammaG_le_one g
  rw [dysonRHS_eq_freeT, dysonRHS_eq_freeT, freeT_sub_freeT _ hwu hwv]
  have e : z + gammaG g * u - (z + gammaG g * v) = (gammaG g : ℂ) * (u - v) := by ring
  rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le]
  have h1 := norm_avg_resres_le (hopB g) hwu hwv
  have h2 : (z + gammaG g * u).im⁻¹ ≤ z.im⁻¹ :=
    inv_anti₀ hz (by rw [im_shift]; nlinarith)
  have h3 : (z + gammaG g * v).im⁻¹ ≤ z.im⁻¹ :=
    inv_anti₀ hz (by rw [im_shift]; nlinarith)
  have h4 : ‖avgC fun p => res (hopB g) (z + gammaG g * u) p *
      res (hopB g) (z + gammaG g * v) p‖ ≤ z.im⁻¹ ^ 2 := by
    refine h1.trans ?_
    rw [sq]
    exact mul_le_mul h2 h3 (inv_nonneg.mpr hwv.le) (inv_nonneg.mpr hz.le)
  have h5 : 0 ≤ ‖u - v‖ := norm_nonneg _
  calc gammaG g * ‖u - v‖ * ‖avgC fun p => res (hopB g) (z + gammaG g * u) p *
        res (hopB g) (z + gammaG g * v) p‖
      ≤ 1 * ‖u - v‖ * z.im⁻¹ ^ 2 := by gcongr
    _ = z.im⁻¹ ^ 2 * ‖u - v‖ := by ring

/-- Existence of a solution of (1.9) [eq:dyson] in `ℂ_+` by fixed-point iteration from `u₀ = i`. -/
private lemma dyson_exists (g : ℝ) (hg : 0 ≤ g) (z : ℂ) (hz : 0 < z.im) :
    ∃ u : ℂ, 0 < u.im ∧ u = dysonRHS g z u := by
  set Φ : ℂ → ℂ := fun u => dysonRHS g z u with hΦ
  set η := z.im with hη
  set γ := gammaG g with hγdef
  have hγ : 0 < γ := gammaG_pos g
  have hγ1 : γ ≤ 1 := gammaG_le_one g
  set u : ℕ → ℂ := fun n => Φ^[n] I with hu
  have hsucc : ∀ n, u (n + 1) = Φ (u n) := fun n => Function.iterate_succ_apply' Φ n I
  have him : ∀ n, 0 < (u n).im := by
    intro n
    induction n with
    | zero => simp [u]
    | succ n ih => rw [hsucc]; exact dyson_im_pos g hz ih.le
  set v : ℕ → ℂ := fun n => u (n + 1) with hv
  have hvs : ∀ n, v (n + 1) = Φ (v n) := fun n => hsucc (n + 1)
  have hvim : ∀ n, 0 < (v n).im := fun n => him (n + 1)
  have hvnorm : ∀ n, ‖v n‖ ≤ η⁻¹ := fun n => by
    change ‖u (n + 1)‖ ≤ η⁻¹
    rw [hsucc]; exact dyson_norm_le g hz (him n).le
  have hvimle : ∀ n, (v n).im ≤ η⁻¹ := fun n =>
    (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans (hvnorm n))
  -- lower bound on the imaginary parts
  set c₀ := η * ((2 + ‖z‖ + η⁻¹) ^ 2)⁻¹ with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  have hvlb : ∀ n, c₀ ≤ (v (n + 1)).im := by
    intro n
    rw [hvs]
    refine le_trans ?_ (dyson_im_ge g hg hz (hvim n).le)
    have hp : 0 < 2 + ‖z‖ + ‖v n‖ := by positivity
    have : ((2 + ‖z‖ + η⁻¹) ^ 2)⁻¹ ≤ ((2 + ‖z‖ + ‖v n‖) ^ 2)⁻¹ :=
      inv_anti₀ (pow_pos hp 2) (pow_le_pow_left₀ hp.le (by linarith [hvnorm n]) 2)
    exact mul_le_mul_of_nonneg_left this hz.le
  -- the contraction factor `θ ≤ (1 + η²)⁻¹`, in multiplied form
  set s := 1 + η ^ 2 with hs
  have hspos : 0 < s := by positivity
  have htheta : ∀ n, γ * (v n).im * s ≤ η + γ * (v n).im := by
    intro n
    have h1 : (v n).im * η ≤ 1 := by
      have := mul_le_mul_of_nonneg_right (hvimle n) hz.le
      rwa [inv_mul_cancel₀ hz.ne'] at this
    have h2 : γ * ((v n).im * η) ≤ 1 := by nlinarith [hvim n]
    rw [hs]
    nlinarith
  -- the potential `D n = |v_{n+1} - v_n|² / (Im v_{n+1} Im v_n)`
  set D : ℕ → ℝ := fun n => ‖v (n + 1) - v n‖ ^ 2 / ((v (n + 1)).im * (v n).im) with hD
  have hDstep : ∀ n, D (n + 1) ≤ (s ^ 2)⁻¹ * D n := by
    intro n
    have hc := dyson_contr g hz (hvim (n + 1)).le (hvim n).le
    have hvs' : ∀ k, v (k + 1) = dysonRHS g z (v k) := hvs
    rw [← hvs' (n + 1), ← hvs' n] at hc
    set X := ‖v (n + 2) - v (n + 1)‖ ^ 2
    set Y := ‖v (n + 1) - v n‖ ^ 2
    set y0 := (v n).im
    set y1 := (v (n + 1)).im
    set y2 := (v (n + 2)).im
    have hy0 : 0 < y0 := hvim n
    have hy1 : 0 < y1 := hvim (n + 1)
    have hy2 : 0 < y2 := hvim (n + 2)
    have hX : 0 ≤ X := by positivity
    have hY : 0 ≤ Y := by positivity
    have ht0 := htheta n
    have ht1 := htheta (n + 1)
    have h1 : X * (γ * y1 * s) * (γ * y0 * s) ≤ X * (η + γ * y1) * (η + γ * y0) := by
      have : 0 ≤ γ * y1 * s := by positivity
      have : 0 ≤ γ * y0 * s := by positivity
      gcongr
    have h2 : γ ^ 2 * (X * y0 * s ^ 2 * y1) ≤ γ ^ 2 * (Y * y2 * y1) := by
      have : X * (γ * y1 * s) * (γ * y0 * s) = γ ^ 2 * (X * y0 * s ^ 2 * y1) := by ring
      have hc' : X * ((η + γ * y1) * (η + γ * y0)) ≤ γ ^ 2 * Y * (y2 * y1) := hc
      nlinarith
    have h3 : X * y0 * s ^ 2 * y1 ≤ Y * y2 * y1 := le_of_mul_le_mul_left h2 (by positivity)
    have h4 : X * y0 * s ^ 2 ≤ Y * y2 := le_of_mul_le_mul_right h3 hy1
    change X / (y2 * y1) ≤ (s ^ 2)⁻¹ * (Y / (y1 * y0))
    rw [div_le_iff₀ (by positivity)]
    calc X = X * y0 * s ^ 2 / (y0 * s ^ 2) := by field_simp
      _ ≤ Y * y2 / (y0 * s ^ 2) := by gcongr
      _ = (s ^ 2)⁻¹ * (Y / (y1 * y0)) * (y2 * y1) := by field_simp
  have hD0 : 0 ≤ D 0 := by
    have := hvim 0; have := hvim 1
    positivity
  set r := s⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr]; apply inv_lt_one_of_one_lt₀; rw [hs]; nlinarith
  have hDn : ∀ n, D n ≤ (r ^ 2) ^ n * D 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc D (n + 1) ≤ (s ^ 2)⁻¹ * D n := hDstep n
        _ ≤ (s ^ 2)⁻¹ * ((r ^ 2) ^ n * D 0) := by gcongr
        _ = (r ^ 2) ^ (n + 1) * D 0 := by rw [hr, inv_pow]; ring
  set K := Real.sqrt (D 0) * η⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  have hdist : ∀ n, dist (v n) (v (n + 1)) ≤ K * r ^ n := by
    intro n
    rw [dist_eq_norm, norm_sub_rev]
    have hy0 := hvim n
    have hy1 := hvim (n + 1)
    have e : ‖v (n + 1) - v n‖ ^ 2 = D n * ((v (n + 1)).im * (v n).im) := by
      simp only [hD]; field_simp
    have hprod : (v (n + 1)).im * (v n).im ≤ η⁻¹ ^ 2 := by
      rw [sq]; exact mul_le_mul (hvimle _) (hvimle _) hy0.le (by positivity)
    have hDn0 : 0 ≤ D n := by simp only [hD]; positivity
    have hsq : ‖v (n + 1) - v n‖ ^ 2 ≤ (K * r ^ n) ^ 2 := by
      rw [e, mul_pow, hK, mul_pow, Real.sq_sqrt hD0]
      calc D n * ((v (n + 1)).im * (v n).im) ≤ ((r ^ 2) ^ n * D 0) * η⁻¹ ^ 2 :=
            mul_le_mul (hDn n) hprod (by positivity) (by positivity)
        _ = D 0 * η⁻¹ ^ 2 * (r ^ n) ^ 2 := by ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
  have hcs : CauchySeq v := cauchySeq_of_le_geometric r K hr1 hdist
  obtain ⟨ustar, hlim⟩ := cauchySeq_tendsto_of_complete hcs
  have hlim1 : Tendsto (fun n => v (n + 1)) atTop (𝓝 ustar) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have himstar : c₀ ≤ ustar.im :=
    ge_of_tendsto ((Complex.continuous_im.tendsto ustar).comp hlim1)
      (Eventually.of_forall hvlb)
  have hstar0 : 0 < ustar.im := lt_of_lt_of_le hc₀pos himstar
  have hlim2 : Tendsto (fun n => Φ (v n)) atTop (𝓝 (Φ ustar)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 := (tendsto_iff_norm_sub_tendsto_zero.mp hlim).const_mul (η⁻¹ ^ 2)
    rw [mul_zero] at h0
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => dyson_lip g hz (hvim n).le hstar0.le) h0
  have hfix : ustar = Φ ustar := by
    refine tendsto_nhds_unique hlim1 ?_
    simpa only [hvs] using hlim2
  exact ⟨ustar, hstar0, hfix⟩

/-- Uniqueness of the solution of (1.9) [eq:dyson] in `ℂ_+`, by the contraction estimate. -/
private lemma dyson_unique' (g : ℝ) {z u v : ℂ} (hz : 0 < z.im) (hu : 0 < u.im)
    (hv : 0 < v.im) (hu' : u = dysonRHS g z u) (hv' : v = dysonRHS g z v) : u = v := by
  have hc := dyson_contr g hz hu.le hv.le
  rw [← hu', ← hv'] at hc
  have hγ := gammaG_pos g
  have hpos : 0 < (z.im + gammaG g * u.im) * (z.im + gammaG g * v.im) -
      gammaG g ^ 2 * (u.im * v.im) := by
    have : 0 < gammaG g * u.im := by positivity
    have : 0 < gammaG g * v.im := by positivity
    nlinarith
  have h0 : ‖u - v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖u - v‖]
  have : ‖u - v‖ = 0 := by
    have := le_antisymm h0 (sq_nonneg _)
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

theorem dyson_existsUnique (g : ℝ) (hg : 0 ≤ g) (z : ℂ) (hz : 0 < z.im) :
    ∃! u : ℂ, 0 < u.im ∧ u = dysonRHS g z u := by
  obtain ⟨u, hu, hfix⟩ := dyson_exists g hg z hz
  exact ⟨u, ⟨hu, hfix⟩, fun v ⟨hv, hvfix⟩ => dyson_unique' g hz hv hu hvfix hfix⟩

/-- `m_g(z)` lies in `ℂ_+` and solves (1.9) [eq:dyson], for `g ≥ 0` and `z ∈ ℂ_+`. -/
theorem mDyson_spec (g : ℝ) (hg : 0 ≤ g) (z : ℂ) (hz : 0 < z.im) :
    0 < (mDyson g z).im ∧ mDyson g z = dysonRHS g z (mDyson g z) := by
  have h := dyson_existsUnique g hg z hz
  have e : mDyson g z = h.exists.choose := by
    unfold mDyson
    split_ifs
    rfl
  rw [e]
  exact h.exists.choose_spec

/-- Uniqueness of the solution of (1.9) [eq:dyson] in `ℂ_+`. -/
theorem mDyson_unique (g : ℝ) (hg : 0 ≤ g) (z : ℂ) (hz : 0 < z.im) (u : ℂ) (hu : 0 < u.im)
    (h : u = dysonRHS g z u) : u = mDyson g z :=
  (dyson_existsUnique g hg z hz).unique ⟨hu, h⟩ (mDyson_spec g hg z hz)

/-- (A.6) [da:eq:ward], first identity. -/
theorem mDyson_ward (g : ℝ) (hg : 0 ≤ g) (z : ℂ) (hz : 0 < z.im) :
    (2 * π)⁻¹ * ∫ p in (-π)..π,
        ‖((2 * hopB g * Real.cos p : ℝ) - z - gammaG g * mDyson g z)⁻¹‖ ^ 2 =
      (mDyson g z).im / (z.im + gammaG g * (mDyson g z).im) := by
  obtain ⟨hm, hfix⟩ := mDyson_spec g hg z hz
  have him := dyson_im_eq g hz hm.le
  rw [← hfix] at him
  have hpos : 0 < z.im + gammaG g * (mDyson g z).im := by
    have := gammaG_pos g
    positivity
  have hN : nsq (hopB g) (z + gammaG g * mDyson g z) =
      (mDyson g z).im / (z.im + gammaG g * (mDyson g z).im) := by
    rw [eq_div_iff hpos.ne', mul_comm]
    exact him.symm
  rw [← hN]
  unfold nsq avgR res
  congr 1
  refine intervalIntegral.integral_congr (fun p _ => ?_)
  simp only [sub_sub]

theorem mDyson_norm_le_max (g : ℝ) (hg : 0 ≤ g) (z : ℂ) (hz : 0 < z.im) :
    ‖mDyson g z‖ ≤ max 1 g := by
  obtain ⟨hm, hfix⟩ := mDyson_spec g hg z hz
  have hw := im_shift_pos g hz hm.le
  have h1 : ‖mDyson g z‖ ^ 2 ≤ nsq (hopB g) (z + gammaG g * mDyson g z) := by
    have := normsq_freeT_le (hopB g) hw
    rwa [← dysonRHS_eq_freeT, ← hfix] at this
  have him := dyson_im_eq g hz hm.le
  rw [← hfix] at him
  have hγ := gammaG_pos g
  have hN := (nsq_pos (hopB g) hw).le
  have h2 : gammaG g * nsq (hopB g) (z + gammaG g * mDyson g z) ≤ 1 := by
    by_contra hc'
    have hc := not_le.mp hc'
    have hp : 0 < z.im + gammaG g * (mDyson g z).im := by positivity
    have := mul_lt_mul_of_pos_left hc hp
    nlinarith
  have hM := max_one_pos g
  have h3 : ‖mDyson g z‖ ^ 2 ≤ (max 1 g) ^ 2 := by
    have e := gammaG_mul_sq g
    calc ‖mDyson g z‖ ^ 2 = ‖mDyson g z‖ ^ 2 * (gammaG g * (max 1 g) ^ 2) := by rw [e, mul_one]
      _ = (gammaG g * ‖mDyson g z‖ ^ 2) * (max 1 g) ^ 2 := by ring
      _ ≤ (gammaG g * nsq (hopB g) (z + gammaG g * mDyson g z)) * (max 1 g) ^ 2 := by gcongr
      _ ≤ 1 * (max 1 g) ^ 2 := by gcongr
      _ = (max 1 g) ^ 2 := one_mul _
  exact (sq_le_sq₀ (norm_nonneg _) hM.le).mp h3

theorem mDyson_norm_le_inv_im (g : ℝ) (hg : 0 ≤ g) (z : ℂ) (hz : 0 < z.im) :
    ‖mDyson g z‖ ≤ z.im⁻¹ := by
  obtain ⟨hm, hfix⟩ := mDyson_spec g hg z hz
  calc ‖mDyson g z‖ = ‖dysonRHS g z (mDyson g z)‖ := by rw [← hfix]
    _ ≤ z.im⁻¹ := dyson_norm_le g hz hm.le

/-- `m_g(z) ∼ -1/z` as `|z| → ∞`, the normalization in (1.9) [eq:dyson]. -/
theorem mDyson_asymp (g : ℝ) (hg : 0 ≤ g) (z : ℂ) (hz : 0 < z.im) (hz3 : 3 < ‖z‖) :
    ‖z * mDyson g z + 1‖ ≤ 3 / (‖z‖ - 3) := by
  obtain ⟨hm, hfix⟩ := mDyson_spec g hg z hz
  have hw := im_shift_pos g hz hm.le
  have hmax := mDyson_norm_le_max g hg z hz
  have h3 := hop_gamma_le_three g
  have hγ := gammaG_pos g
  have hb0 : 0 ≤ hopB g := div_nonneg hg (max_one_pos g).le
  have hpos : 0 < ‖z‖ - 3 := by linarith
  have hpt : ∀ p, ‖(((2 * hopB g * Real.cos p : ℝ) : ℂ) - gammaG g * mDyson g z) *
      res (hopB g) (z + gammaG g * mDyson g z) p‖ ≤ 3 / (‖z‖ - 3) := by
    intro p
    have hA : ‖((2 * hopB g * Real.cos p : ℝ) : ℂ) - gammaG g * mDyson g z‖ ≤ 3 := by
      calc ‖((2 * hopB g * Real.cos p : ℝ) : ℂ) - gammaG g * mDyson g z‖
          ≤ ‖((2 * hopB g * Real.cos p : ℝ) : ℂ)‖ + ‖(gammaG g : ℂ) * mDyson g z‖ :=
            norm_sub_le _ _
        _ ≤ 2 * hopB g + gammaG g * max 1 g := by
            gcongr
            · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hb0]
              have := Real.abs_cos_le_one p
              norm_num
              nlinarith
            · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le]
              gcongr
        _ ≤ 3 := h3
    have hB : ‖z‖ - 3 ≤ ‖((2 * hopB g * Real.cos p : ℝ) : ℂ) - (z + gammaG g * mDyson g z)‖ := by
      have e : ((2 * hopB g * Real.cos p : ℝ) : ℂ) - (z + gammaG g * mDyson g z) =
          -(z - (((2 * hopB g * Real.cos p : ℝ) : ℂ) - gammaG g * mDyson g z)) := by ring
      rw [e, norm_neg]
      have := norm_sub_norm_le z (((2 * hopB g * Real.cos p : ℝ) : ℂ) - gammaG g * mDyson g z)
      linarith
    unfold res
    rw [norm_mul, norm_inv, div_eq_mul_inv]
    exact mul_le_mul hA (inv_anti₀ hpos hB) (inv_nonneg.mpr (norm_nonneg _)) (by norm_num)
  have hc := continuous_res (b := hopB g) hw
  have hid : z * mDyson g z + 1 = avgC (fun p => (((2 * hopB g * Real.cos p : ℝ) : ℂ) -
      gammaG g * mDyson g z) * res (hopB g) (z + gammaG g * mDyson g z) p) := by
    have e1 : mDyson g z = avgC (res (hopB g) (z + gammaG g * mDyson g z)) :=
      hfix.trans (dysonRHS_eq_freeT g z _)
    have e2 : avgC (fun p => z * res (hopB g) (z + gammaG g * mDyson g z) p + 1) =
        z * avgC (res (hopB g) (z + gammaG g * mDyson g z)) + 1 := by
      rw [avgC_add (by fun_prop) continuous_const, avgC_const_mul, avgC_const]
    conv_lhs => rw [e1]
    rw [← e2]
    congr 1
    funext p
    have hne := res_base_ne (b := hopB g) hw p
    unfold res
    field_simp
    ring
  rw [hid]
  exact norm_avgC_le_const hpt

/-! ### Holomorphy of `m_g` on `ℂ_+` -/

private lemma continuousAt_of_lip {f : ℂ → ℂ} {z : ℂ} {K : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ‖f z' - f z‖ ≤ K * ‖z' - z‖) : ContinuousAt f z := by
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun z' => K * ‖z' - z‖) (𝓝 z) (𝓝 0) := by
    have hc : Continuous fun z' : ℂ => K * ‖z' - z‖ := by fun_prop
    simpa using hc.tendsto z
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) h h0

/-- `γ ⟨|R|²⟩ (1 + (Im z)²) ≤ 1` at the solution of (1.9) [eq:dyson]. -/
private lemma theta_le (g : ℝ) (hg : 0 ≤ g) {z : ℂ} (hz : 0 < z.im) :
    gammaG g * nsq (hopB g) (z + gammaG g * mDyson g z) * (1 + z.im ^ 2) ≤ 1 := by
  obtain ⟨hm, hfix⟩ := mDyson_spec g hg z hz
  have him := dyson_im_eq g hz hm.le
  rw [← hfix] at him
  have hn := mDyson_norm_le_inv_im g hg z hz
  have hγ := gammaG_pos g
  have hγ1 := gammaG_le_one g
  have hy : (mDyson g z).im * z.im ≤ 1 := by
    have h1 := (le_abs_self (mDyson g z).im).trans ((Complex.abs_im_le_norm _).trans hn)
    have h2 := mul_le_mul_of_nonneg_right h1 hz.le
    rwa [inv_mul_cancel₀ hz.ne'] at h2
  have hpos : 0 < z.im + gammaG g * (mDyson g z).im := by positivity
  have e : (z.im + gammaG g * (mDyson g z).im) *
      (gammaG g * nsq (hopB g) (z + gammaG g * mDyson g z) * (1 + z.im ^ 2)) =
      gammaG g * (mDyson g z).im * (1 + z.im ^ 2) := by
    linear_combination (-(gammaG g) * (1 + z.im ^ 2)) * him
  have key : (z.im + gammaG g * (mDyson g z).im) *
      (gammaG g * nsq (hopB g) (z + gammaG g * mDyson g z) * (1 + z.im ^ 2)) ≤
      (z.im + gammaG g * (mDyson g z).im) * 1 := by
    rw [e]
    have h1 : gammaG g * ((mDyson g z).im * z.im) ≤ 1 := by nlinarith
    nlinarith
  exact le_of_mul_le_mul_left key hpos

private lemma mDyson_hasDerivAt (g : ℝ) (hg : 0 ≤ g) {z : ℂ} (hz : 0 < z.im) :
    ∃ d, HasDerivAt (mDyson g) d z := by
  set η := z.im with hη
  set γ := gammaG g with hγdef
  set b := hopB g with hb
  have hγ : 0 < γ := gammaG_pos g
  have hγ1 : γ ≤ 1 := gammaG_le_one g
  set W : ℂ → ℂ := fun z' => z' + (γ : ℂ) * mDyson g z' with hW
  have hWim : ∀ z', 0 < z'.im → z'.im ≤ (W z').im ∧ 0 < (W z').im := by
    intro z' hz'
    have hm := (mDyson_spec g hg z' hz').1
    have e : (W z').im = z'.im + γ * (mDyson g z').im := im_shift g z' _
    have : 0 < γ * (mDyson g z').im := by positivity
    constructor <;> linarith
  have hfixW : ∀ z', 0 < z'.im → mDyson g z' = freeT b (W z') := fun z' hz' =>
    (mDyson_spec g hg z' hz').2.trans (dysonRHS_eq_freeT g z' _)
  set P : ℂ → ℂ := fun z' => avgC (fun p => res b (W z') p * res b (W z) p) with hP
  have hWz := hWim z hz
  have hid : ∀ z', 0 < z'.im →
      (mDyson g z' - mDyson g z) * (1 - γ * P z') = (z' - z) * P z' := by
    intro z' hz'
    have h1 : mDyson g z' - mDyson g z = (W z' - W z) * P z' := by
      rw [hfixW z' hz', hfixW z hz]
      exact freeT_sub_freeT b (hWim z' hz').2 hWz.2
    have h2 : W z' - W z = (z' - z) + γ * (mDyson g z' - mDyson g z) := by
      simp only [hW]; ring
    rw [h2] at h1
    linear_combination h1
  set ρ := (1 + η ^ 2 / 4)⁻¹ with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ (by have := sq_pos_of_pos hz; linarith)
  have hθz := theta_le g hg hz
  have hgP : ∀ z', η / 2 ≤ z'.im → ‖(γ : ℂ) * P z'‖ ≤ ρ := by
    intro z' hz2
    have hz' : 0 < z'.im := by linarith
    have hθ' := theta_le g hg hz'
    have hcs := cs_resres b (hWim z' hz').2 hWz.2
    have hN'0 := (nsq_pos b (hWim z' hz').2).le
    have hN0 := (nsq_pos b hWz.2).le
    have hA : γ * nsq b (W z') ≤ ρ := by
      rw [hρ, ← one_div, le_div_iff₀ (by positivity)]
      have : η ^ 2 / 4 ≤ z'.im ^ 2 := by nlinarith
      have h0 : 0 ≤ γ * nsq b (W z') := by positivity
      calc γ * nsq b (W z') * (1 + η ^ 2 / 4) ≤ γ * nsq b (W z') * (1 + z'.im ^ 2) := by gcongr
        _ ≤ 1 := hθ'
    have hB : γ * nsq b (W z) ≤ ρ := by
      rw [hρ, ← one_div, le_div_iff₀ (by positivity)]
      have : η ^ 2 / 4 ≤ η ^ 2 := by nlinarith
      have h0 : 0 ≤ γ * nsq b (W z) := by positivity
      calc γ * nsq b (W z) * (1 + η ^ 2 / 4) ≤ γ * nsq b (W z) * (1 + η ^ 2) := by gcongr
        _ ≤ 1 := hθz
    have hsq : ‖(γ : ℂ) * P z'‖ ^ 2 ≤ ρ ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le, mul_pow]
      calc γ ^ 2 * ‖P z'‖ ^ 2 ≤ γ ^ 2 * (nsq b (W z') * nsq b (W z)) := by gcongr
        _ = (γ * nsq b (W z')) * (γ * nsq b (W z)) := by ring
        _ ≤ ρ * ρ := mul_le_mul hA hB (by positivity) hρ0.le
        _ = ρ ^ 2 := by ring
    exact (sq_le_sq₀ (norm_nonneg _) hρ0.le).mp hsq
  have hden : ∀ z', η / 2 ≤ z'.im → 1 - ρ ≤ ‖1 - (γ : ℂ) * P z'‖ := by
    intro z' hz2
    have := norm_sub_norm_le (1 : ℂ) ((γ : ℂ) * P z')
    rw [norm_one] at this
    linarith [hgP z' hz2]
  have hinv' : ∀ z', η / 2 ≤ z'.im → (W z').im⁻¹ ≤ 2 / η := by
    intro z' hz2
    have hz' : 0 < z'.im := by linarith
    calc (W z').im⁻¹ ≤ (η / 2)⁻¹ := inv_anti₀ (by positivity) (hz2.trans (hWim z' hz').1)
      _ = 2 / η := by rw [inv_div]
  have hinv : (W z).im⁻¹ ≤ η⁻¹ := inv_anti₀ hz hWz.1
  have hPnorm : ∀ z', η / 2 ≤ z'.im → ‖P z'‖ ≤ 2 / η * η⁻¹ := by
    intro z' hz2
    have hz' : 0 < z'.im := by linarith
    exact (norm_avg_resres_le b (hWim z' hz').2 hWz.2).trans
      (mul_le_mul (hinv' z' hz2) hinv (inv_nonneg.mpr hWz.2.le) (by positivity))
  set K₁ := 2 / η * η⁻¹ / (1 - ρ) with hK₁
  have h1ρ : 0 < 1 - ρ := by linarith
  have hlipm : ∀ z', η / 2 ≤ z'.im → ‖mDyson g z' - mDyson g z‖ ≤ K₁ * ‖z' - z‖ := by
    intro z' hz2
    have hz' : 0 < z'.im := by linarith
    have h := congrArg norm (hid z' hz')
    rw [norm_mul, norm_mul] at h
    have h2 : ‖mDyson g z' - mDyson g z‖ * (1 - ρ) ≤ ‖z' - z‖ * (2 / η * η⁻¹) :=
      calc ‖mDyson g z' - mDyson g z‖ * (1 - ρ)
          ≤ ‖mDyson g z' - mDyson g z‖ * ‖1 - (γ : ℂ) * P z'‖ := by gcongr; exact hden z' hz2
        _ = ‖z' - z‖ * ‖P z'‖ := h
        _ ≤ ‖z' - z‖ * (2 / η * η⁻¹) := by gcongr; exact hPnorm z' hz2
    rw [show K₁ * ‖z' - z‖ = ‖z' - z‖ * (2 / η * η⁻¹) / (1 - ρ) by rw [hK₁]; ring,
      le_div_iff₀ h1ρ]
    exact h2
  set K₂ := (1 + γ * K₁) * (2 / η * η⁻¹ * η⁻¹) with hK₂
  have hlipP : ∀ z', η / 2 ≤ z'.im → ‖P z' - P z‖ ≤ K₂ * ‖z' - z‖ := by
    intro z' hz2
    have hz' : 0 < z'.im := by linarith
    have hW' := hWim z' hz'
    have hc1 := continuous_res (b := b) hW'.2
    have hc2 := continuous_res (b := b) hWz.2
    have e : P z' - P z = avgC (fun p => (W z' - W z) *
        (res b (W z') p * res b (W z) p * res b (W z) p)) := by
      simp only [hP]
      rw [← avgC_sub (by fun_prop) (by fun_prop)]
      congr 1
      funext p
      rw [← sub_mul, res_sub_res b hW'.2 hWz.2 p]
      ring
    have hWd : ‖W z' - W z‖ ≤ (1 + γ * K₁) * ‖z' - z‖ := by
      have e2 : W z' - W z = (z' - z) + γ * (mDyson g z' - mDyson g z) := by
        simp only [hW]; ring
      rw [e2]
      calc ‖(z' - z) + γ * (mDyson g z' - mDyson g z)‖
          ≤ ‖z' - z‖ + ‖(γ : ℂ) * (mDyson g z' - mDyson g z)‖ := norm_add_le _ _
        _ = ‖z' - z‖ + γ * ‖mDyson g z' - mDyson g z‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le]
        _ ≤ ‖z' - z‖ + γ * (K₁ * ‖z' - z‖) := by gcongr; exact hlipm z' hz2
        _ = (1 + γ * K₁) * ‖z' - z‖ := by ring
    rw [e]
    apply norm_avgC_le_const
    intro p
    have hr1 := (norm_res_le b hW'.2 p).trans (hinv' z' hz2)
    have hr2 := (norm_res_le b hWz.2 p).trans hinv
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖W z' - W z‖ * (‖res b (W z') p‖ * ‖res b (W z) p‖ * ‖res b (W z) p‖)
        ≤ ((1 + γ * K₁) * ‖z' - z‖) * (2 / η * η⁻¹ * η⁻¹) := by gcongr
      _ = K₂ * ‖z' - z‖ := by rw [hK₂]; ring
  have hev : ∀ᶠ z' in 𝓝 z, η / 2 < z'.im :=
    (Complex.continuous_im.tendsto z).eventually (lt_mem_nhds (by linarith))
  have hPc : ContinuousAt P z := continuousAt_of_lip (hev.mono fun z' h => hlipP z' h.le)
  have hden0 : (1 : ℂ) - γ * P z ≠ 0 := by
    intro h0
    have := hden z (by linarith)
    rw [h0, norm_zero] at this
    linarith
  have hFc : ContinuousAt (fun z' => P z' / (1 - γ * P z')) z :=
    hPc.div (continuousAt_const.sub (continuousAt_const.mul hPc)) hden0
  refine ⟨P z / (1 - γ * P z), ?_⟩
  rw [hasDerivAt_iff_tendsto_slope]
  refine (hFc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  rw [EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [hev] with z' hz2 hne
  have hz' : 0 < z'.im := by linarith
  have hne' : z' - z ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hne)
  have hd : (1 : ℂ) - γ * P z' ≠ 0 := by
    intro h0
    have := hden z' hz2.le
    rw [h0, norm_zero] at this
    linarith
  rw [slope_def_field, div_eq_div_iff hd hne', hid z' hz']
  ring

theorem mDyson_differentiableOn (g : ℝ) (hg : 0 ≤ g) :
    DifferentiableOn ℂ (mDyson g) {z : ℂ | 0 < z.im} := by
  intro z hz
  obtain ⟨d, hd⟩ := mDyson_hasDerivAt g hg (z := z) hz
  exact hd.differentiableAt.differentiableWithinAt

/-! ### Symmetry `p ↦ p + π` -/

/-- `f(-w̄) = -conj f(w)`, from the shift `p ↦ p + π` in (A.1) [bl:eq:physical]. -/
private lemma freeT_neg_conj (b : ℝ) (w : ℂ) :
    freeT b (-(starRingEnd ℂ w)) = -(starRingEnd ℂ (freeT b w)) := by
  set F : ℝ → ℂ := fun p => (((2 * b * Real.cos p : ℝ) : ℂ) + starRingEnd ℂ w)⁻¹ with hF
  have hper : Function.Periodic F (2 * π) := fun p => by simp only [hF, Real.cos_add_two_pi]
  have hshift : ∫ p in (-π)..π, F (p + π) = ∫ p in (-π)..π, F p := by
    rw [intervalIntegral.integral_comp_add_right F π]
    have := hper.intervalIntegral_add_eq 0 (-π)
    convert this using 2 <;> ring
  have hc : starRingEnd ℂ ((2 * π : ℂ)⁻¹) = (2 * π : ℂ)⁻¹ := by
    rw [map_inv₀, map_mul, Complex.conj_ofReal, map_ofNat]
  unfold freeT
  rw [map_mul, hc, ← intervalIntegral.intervalIntegral_conj, ← mul_neg,
    ← intervalIntegral.integral_neg]
  congr 1
  refine (intervalIntegral.integral_congr (fun p _ => ?_)).trans
    (hshift.symm.trans (intervalIntegral.integral_congr (fun p _ => ?_)))
  · simp only [hF, sub_neg_eq_add]
  · simp only [hF, Real.cos_add_pi, map_inv₀, map_sub, Complex.conj_ofReal]
    rw [← inv_neg]
    congr 1
    push_cast
    ring

/-- Evenness at the level of `m_g`: `m_g(-z̄) = -conj m_g(z)`. -/
theorem mDyson_neg_conj (g : ℝ) (hg : 0 ≤ g) (z : ℂ) (hz : 0 < z.im) :
    mDyson g (-(starRingEnd ℂ z)) = -(starRingEnd ℂ (mDyson g z)) := by
  obtain ⟨hm, hfix⟩ := mDyson_spec g hg z hz
  have hz' : 0 < (-(starRingEnd ℂ z)).im := by simpa using hz
  have hv : 0 < (-(starRingEnd ℂ (mDyson g z))).im := by simpa using hm
  refine (mDyson_unique g hg _ hz' _ hv ?_).symm
  have e1 : -(starRingEnd ℂ (mDyson g z)) =
      -(starRingEnd ℂ (freeT (hopB g) (z + gammaG g * mDyson g z))) := by
    rw [← dysonRHS_eq_freeT, ← hfix]
  rw [dysonRHS_eq_freeT]
  conv_lhs => rw [e1]
  rw [← freeT_neg_conj]
  congr 1
  simp only [map_add, map_mul, Complex.conj_ofReal]
  ring

end LSBA
