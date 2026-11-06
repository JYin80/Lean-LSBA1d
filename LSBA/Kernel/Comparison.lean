import LSBA.Kernel.Bounded
import LSBA.Kernel.Large
import LSBA.Kernel.Scales

/-!
# Comparison parameters and positive height

The comparison map `(g, E) ↦ (g′, E′)` of Lemma 6.3 [da:lem:comparison-parameters] with the tube
(A.57) [bl:eq:tube] and the exact law (A.58) [bl:eq:exactlaw], chains of comparisons, and
Lemma 6.4 [da:lem:positive-height] on the comparison segments, at bounded and large coupling.
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- `g' = g√(s/u)`, Lemma 6.3(a) [da:lem:comparison-parameters]. -/
def gCmp (g s u : ℝ) : ℝ := g * Real.sqrt (s / u)

/-- `ξ = (sγ_{g'}/(uγ_g))^{1/2}`, Lemma 6.3(a) [da:lem:comparison-parameters]. -/
def xiCmp (g s u : ℝ) : ℝ := Real.sqrt (s * gammaG (gCmp g s u) / (u * gammaG g))

/-- The height `η_β` of (A.57) [bl:eq:tube]: the positive solution of `η = (β - a)ρ(η)`,
`ρ(y) = Im m(x + iy; a)` at hopping `b` (junk `0` if it is not unique). -/
def etaTube (b a β : ℝ) (L : ℕ) (x : ℝ) : ℝ :=
  if h : ∃! η : ℝ, 0 < η ∧ η = (β - a) * (mRootV b a L (x + η * I)).im then h.exists.choose
  else 0

/-- `e_β = x - (β - a)Re m(x + iη_β; a)`, (A.57) [bl:eq:tube]. -/
def eTube (b a β : ℝ) (L : ℕ) (x : ℝ) : ℝ :=
  x - (β - a) * (mRootV b a L (x + etaTube b a β L x * I)).re

/-- The comparison energy `E' = ξe_{b'}` of (A.58) [bl:eq:exactlaw], `a = uγ_g`, `b' = (u/s)γ_g`. -/
def ECmp (g : ℝ) (L : ℕ) (E : ℝ) (m : ℂ) (s u : ℝ) : ℝ :=
  xiCmp g s u * eTube (hopB g) (u * gammaG g) (u / s * gammaG g) L (zChar g E m u).re

/-- The comparison point `w = x + iη_{b'}` of (A.58) [bl:eq:exactlaw]. -/
def wCmp (g : ℝ) (L : ℕ) (E : ℝ) (m : ℂ) (s u : ℝ) : ℂ :=
  ((zChar g E m u).re : ℂ) +
    (etaTube (hopB g) (u * gammaG g) (u / s * gammaG g) L (zChar g E m u).re : ℂ) * I

/-- One comparison step `(g, E) ↦ (g', E')` of Lemma 6.3(a) [da:lem:comparison-parameters], with the
anchor `m(g,E)`. -/
def cmpStep (L : ℕ) (p su : ℝ × ℝ) : ℝ × ℝ :=
  (gCmp p.1 su.1 su.2, ECmp p.1 L p.2 (mRoot p.1 L p.2) su.1 su.2)

/-- A chain of comparisons, Lemma 6.3(b) [da:lem:comparison-parameters]. -/
def cmpChain (L : ℕ) (p : ℝ × ℝ) (steps : List (ℝ × ℝ)) : ℝ × ℝ := steps.foldl (cmpStep L) p

/-- The Dyson matrix on the vertical segment `z = x + iγ_g r` at variance `uγ_g`, (5.27)
[gc:eq:positive-dyson]. -/
def segMat (g : ℝ) (L : ℕ) (x u r : ℝ) : Matrix (Fin L) (Fin L) ℂ :=
  dysonMat (hopB g) (u * gammaG g) L ((x : ℂ) + ((gammaG g * r : ℝ) : ℂ) * I)
    (mRootV (hopB g) (u * gammaG g) L ((x : ℂ) + ((gammaG g * r : ℝ) : ℂ) * I))

/-! ### Finite averages and the resolvent `R_w(k) = (2b cos(2πk/L) - w)⁻¹` -/

private def avgS (L : ℕ) (f : Fin L → ℂ) : ℂ := (L : ℂ)⁻¹ * ∑ k, f k

private def avgSR (L : ℕ) (f : Fin L → ℝ) : ℝ := (L : ℝ)⁻¹ * ∑ k, f k

private lemma avgSR_mono {L : ℕ} {f h : Fin L → ℝ} (hle : ∀ k, f k ≤ h k) :
    avgSR L f ≤ avgSR L h := by
  unfold avgSR
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hle k) (by positivity)

private lemma avgSR_nonneg {L : ℕ} {f : Fin L → ℝ} (h : ∀ k, 0 ≤ f k) : 0 ≤ avgSR L f := by
  unfold avgSR
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => h k)

private lemma avgSR_add {L : ℕ} (f h : Fin L → ℝ) :
    avgSR L (fun k => f k + h k) = avgSR L f + avgSR L h := by
  unfold avgSR
  rw [Finset.sum_add_distrib]
  ring

private lemma avgSR_const_mul {L : ℕ} (c : ℝ) (f : Fin L → ℝ) :
    avgSR L (fun k => c * f k) = c * avgSR L f := by
  unfold avgSR
  rw [← Finset.mul_sum]
  ring

private lemma avgSR_const {L : ℕ} (hL : 1 ≤ L) (c : ℝ) : avgSR L (fun _ => c) = c := by
  unfold avgSR
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  field_simp

private lemma avgS_sub {L : ℕ} (f h : Fin L → ℂ) :
    avgS L (fun k => f k - h k) = avgS L f - avgS L h := by
  unfold avgS
  rw [Finset.sum_sub_distrib]
  ring

private lemma avgS_const_mul {L : ℕ} (c : ℂ) (f : Fin L → ℂ) :
    avgS L (fun k => c * f k) = c * avgS L f := by
  unfold avgS
  rw [← Finset.mul_sum]
  ring

private lemma im_avgS {L : ℕ} (f : Fin L → ℂ) :
    (avgS L f).im = avgSR L (fun k => (f k).im) := by
  unfold avgS avgSR
  rw [show (L : ℂ)⁻¹ = (((L : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul,
    Complex.im_sum]

private lemma re_avgS {L : ℕ} (f : Fin L → ℂ) :
    (avgS L f).re = avgSR L (fun k => (f k).re) := by
  unfold avgS avgSR
  rw [show (L : ℂ)⁻¹ = (((L : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
    Complex.re_sum]

private lemma norm_avgS_le {L : ℕ} (f : Fin L → ℂ) :
    ‖avgS L f‖ ≤ avgSR L (fun k => ‖f k‖) := by
  unfold avgS avgSR
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  gcongr
  exact norm_sum_le _ _

private lemma avg_cs {L : ℕ} (f h : Fin L → ℂ) :
    ‖avgS L (fun k => f k * h k)‖ ^ 2 ≤
      avgSR L (fun k => ‖f k‖ ^ 2) * avgSR L (fun k => ‖h k‖ ^ 2) := by
  have h1 := norm_avgS_le (fun k => f k * h k)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖f k‖) (fun k => ‖h k‖)
  unfold avgSR at h1 ⊢
  simp only [norm_mul] at h1
  calc ‖avgS L fun k => f k * h k‖ ^ 2 ≤ ((L : ℝ)⁻¹ * ∑ k, ‖f k‖ * ‖h k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ((L : ℝ)⁻¹) ^ 2 * (∑ k, ‖f k‖ * ‖h k‖) ^ 2 := mul_pow _ _ _
    _ ≤ ((L : ℝ)⁻¹) ^ 2 * ((∑ k, ‖f k‖ ^ 2) * ∑ k, ‖h k‖ ^ 2) := by gcongr
    _ = _ := by ring

private lemma avg_sq_le {L : ℕ} (hL : 1 ≤ L) (x : Fin L → ℝ) :
    avgSR L x ^ 2 ≤ avgSR L (fun k => x k ^ 2) := by
  have hL' : (0 : ℝ) < L := by positivity
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)
  unfold avgSR
  rw [Finset.card_univ, Fintype.card_fin] at h
  calc ((L : ℝ)⁻¹ * ∑ k, x k) ^ 2 = ((L : ℝ)⁻¹) ^ 2 * (∑ k, x k) ^ 2 := mul_pow _ _ _
    _ ≤ ((L : ℝ)⁻¹) ^ 2 * (L * ∑ k, x k ^ 2) := by gcongr
    _ = (L : ℝ)⁻¹ * ∑ k, x k ^ 2 := by field_simp

private def resL (b : ℝ) (L : ℕ) (w : ℂ) (k : Fin L) : ℂ :=
  ((2 * b * Real.cos (2 * π * k / L) : ℝ) - w)⁻¹

private lemma freeTL_eq_avgS (b : ℝ) (L : ℕ) (w : ℂ) : freeTL b L w = avgS L (resL b L w) := rfl

private lemma resL_base_ne {b : ℝ} {L : ℕ} {w : ℂ} (hw : 0 < w.im) (k : Fin L) :
    ((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ) - w ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at this
  linarith

private lemma im_resL (b : ℝ) (L : ℕ) (w : ℂ) (k : Fin L) :
    (resL b L w k).im = w.im * ‖resL b L w k‖ ^ 2 := by
  unfold resL
  rw [Complex.inv_im, Complex.sq_norm, Complex.normSq_inv]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  ring

private lemma norm_resL_le (b : ℝ) (L : ℕ) {w : ℂ} (hw : 0 < w.im) (k : Fin L) :
    ‖resL b L w k‖ ≤ 1 / w.im := by
  unfold resL
  rw [norm_inv, one_div]
  refine inv_anti₀ hw ?_
  refine le_trans ?_ (Complex.abs_im_le_norm _)
  rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hw]

private lemma norm_resL_ge (b : ℝ) (L : ℕ) {w : ℂ} (hw : 0 < w.im) (k : Fin L) :
    1 / (2 * |b| + ‖w‖) ≤ ‖resL b L w k‖ := by
  unfold resL
  rw [norm_inv, one_div]
  have hne := resL_base_ne (b := b) (L := L) hw k
  have hpos : 0 < ‖((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ) - w‖ := norm_pos_iff.mpr hne
  refine inv_anti₀ hpos ?_
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
  have := Real.abs_cos_le_one (2 * π * k / L)
  have h2 : |(2 : ℝ)| = 2 := abs_two
  rw [h2]
  nlinarith [abs_nonneg b]

private lemma resL_sub_resL (b : ℝ) (L : ℕ) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im)
    (k : Fin L) :
    resL b L w k - resL b L w' k = (w - w') * (resL b L w k * resL b L w' k) := by
  unfold resL
  have h1 := resL_base_ne (b := b) (L := L) hw k
  have h2 := resL_base_ne (b := b) (L := L) hw' k
  field_simp
  ring

private def nsqL (b : ℝ) (L : ℕ) (w : ℂ) : ℝ := avgSR L (fun k => ‖resL b L w k‖ ^ 2)

private lemma nsqL_nonneg (b : ℝ) (L : ℕ) (w : ℂ) : 0 ≤ nsqL b L w :=
  avgSR_nonneg fun _ => sq_nonneg _

private lemma freeTL_sub_freeTL (b : ℝ) (L : ℕ) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) :
    freeTL b L w - freeTL b L w' = (w - w') * avgS L (fun k => resL b L w k * resL b L w' k) := by
  rw [freeTL_eq_avgS, freeTL_eq_avgS, ← avgS_sub, ← avgS_const_mul]
  congr 1
  funext k
  exact resL_sub_resL b L hw hw' k

private lemma im_freeTL (b : ℝ) (L : ℕ) (w : ℂ) : (freeTL b L w).im = w.im * nsqL b L w := by
  rw [freeTL_eq_avgS, im_avgS, nsqL, ← avgSR_const_mul]
  congr 1
  funext k
  exact im_resL b L w k

private lemma norm_freeTL_le (b : ℝ) {L : ℕ} (hL : 1 ≤ L) {w : ℂ} (hw : 0 < w.im) :
    ‖freeTL b L w‖ ≤ 1 / w.im := by
  rw [freeTL_eq_avgS]
  refine (norm_avgS_le _).trans ?_
  calc avgSR L (fun k => ‖resL b L w k‖) ≤ avgSR L (fun _ => 1 / w.im) :=
        avgSR_mono fun k => norm_resL_le b L hw k
    _ = 1 / w.im := avgSR_const hL _

private lemma norm_freeTL_sq_le (b : ℝ) {L : ℕ} (hL : 1 ≤ L) (w : ℂ) :
    ‖freeTL b L w‖ ^ 2 ≤ nsqL b L w := by
  rw [freeTL_eq_avgS]
  have h1 := norm_avgS_le (resL b L w)
  have h2 := avg_sq_le hL (fun k => ‖resL b L w k‖)
  calc ‖avgS L (resL b L w)‖ ^ 2 ≤ (avgSR L (fun k => ‖resL b L w k‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ nsqL b L w := h2

private lemma nsqL_ge (b : ℝ) {L : ℕ} (hL : 1 ≤ L) {w : ℂ} (hw : 0 < w.im) :
    (1 / (2 * |b| + ‖w‖)) ^ 2 ≤ nsqL b L w := by
  unfold nsqL
  calc (1 / (2 * |b| + ‖w‖)) ^ 2 = avgSR L (fun _ => (1 / (2 * |b| + ‖w‖)) ^ 2) :=
        (avgSR_const hL _).symm
    _ ≤ _ := avgSR_mono fun k => pow_le_pow_left₀ (by positivity) (norm_resL_ge b L hw k) 2

private lemma freeTL_scale (b : ℝ) (L : ℕ) (w : ℂ) {c : ℝ} (hc : c ≠ 0) :
    freeTL (c * b) L ((c : ℂ) * w) = (c : ℂ)⁻¹ * freeTL b L w := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  unfold freeTL
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ((2 * (c * b) * Real.cos (2 * π * k / L) : ℝ) : ℂ) - c * w =
      (c : ℂ) * (((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ) - w) := by
    push_cast; ring
  rw [e, mul_inv]
  ring

/-! ### Stability of roots -/

private lemma stab_core (b β : ℝ) (hβ : 0 < β) {L : ℕ} (hL : 1 ≤ L) {w₁ w₂ m₁ m₂ : ℂ}
    (hw₁ : 0 < w₁.im) (hw₂ : 0 < w₂.im) (hm₁ : 0 < m₁.im) (hm₂ : 0 < m₂.im)
    (e₁ : m₁ = freeTL b L w₁) (e₂ : m₂ = freeTL b L w₂) (hi₁ : β * m₁.im ≤ w₁.im)
    (hi₂ : β * m₂.im ≤ w₂.im) :
    ‖avgS L (fun k => resL b L w₁ k * resL b L w₂ k)‖ ≤ β⁻¹ ∧
      β * m₁.im ^ 2 / 2 ≤ (1 - (β : ℂ) * avgS L (fun k => resL b L w₁ k * resL b L w₂ k)).re ∧
      m₁ - m₂ = (w₁ - w₂) * avgS L (fun k => resL b L w₁ k * resL b L w₂ k) := by
  set A := avgS L (fun k => resL b L w₁ k * resL b L w₂ k) with hA
  have hward : ∀ {w m : ℂ}, 0 < m.im → m = freeTL b L w → β * m.im ≤ w.im →
      β * nsqL b L w ≤ 1 := by
    intro w m hm e hi
    have h1 : m.im = w.im * nsqL b L w := by rw [e]; exact im_freeTL b L w
    have h2 := mul_le_mul_of_nonneg_right hi (nsqL_nonneg b L w)
    have h3 : β * nsqL b L w * m.im ≤ 1 * m.im := by nlinarith
    exact le_of_mul_le_mul_right h3 hm
  have hn₁ := hward hm₁ e₁ hi₁
  have hn₂ := hward hm₂ e₂ hi₂
  have hn₁' := nsqL_nonneg b L w₁
  have hn₂' := nsqL_nonneg b L w₂
  refine ⟨?_, ?_, ?_⟩
  · have hcs : ‖A‖ ^ 2 ≤ nsqL b L w₁ * nsqL b L w₂ := avg_cs _ _
    have h0 : (β * nsqL b L w₁) * (β * nsqL b L w₂) ≤ 1 :=
      (mul_le_mul hn₁ hn₂ (by positivity) zero_le_one).trans (le_of_eq (one_mul 1))
    have h1 : (‖A‖ * β) ^ 2 ≤ 1 := by
      calc (‖A‖ * β) ^ 2 = ‖A‖ ^ 2 * β ^ 2 := by ring
        _ ≤ nsqL b L w₁ * nsqL b L w₂ * β ^ 2 := by gcongr
        _ = (β * nsqL b L w₁) * (β * nsqL b L w₂) := by ring
        _ ≤ 1 := h0
    have h2 : ‖A‖ * β ≤ 1 := (pow_le_one_iff_of_nonneg (by positivity) two_ne_zero).mp h1
    rw [← one_div, le_div_iff₀ hβ]
    exact h2
  · have hpt : ∀ k, 2 * (resL b L w₁ k * resL b L w₂ k).re + (resL b L w₁ k).im ^ 2 ≤
        ‖resL b L w₁ k‖ ^ 2 + ‖resL b L w₂ k‖ ^ 2 := by
      intro k
      have hq : 0 ≤ (resL b L w₁ k).im := by rw [im_resL]; positivity
      have hs : 0 ≤ (resL b L w₂ k).im := by rw [im_resL]; positivity
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
        Complex.mul_re]
      nlinarith [sq_nonneg ((resL b L w₁ k).re - (resL b L w₂ k).re)]
    have havg := avgSR_mono hpt
    rw [avgSR_add, avgSR_add, avgSR_const_mul] at havg
    have hre : A.re = avgSR L (fun k => (resL b L w₁ k * resL b L w₂ k).re) := re_avgS _
    have him : m₁.im = avgSR L (fun k => (resL b L w₁ k).im) := by
      rw [e₁, freeTL_eq_avgS, im_avgS]
    have hj := avg_sq_le hL (fun k => (resL b L w₁ k).im)
    rw [← him] at hj
    have hsum : 2 * A.re + m₁.im ^ 2 ≤ nsqL b L w₁ + nsqL b L w₂ := by
      rw [hre]; unfold nsqL; linarith
    have e : (1 - (β : ℂ) * A).re = 1 - β * A.re := by simp
    rw [e]
    nlinarith
  · rw [e₁, e₂]
    exact freeTL_sub_freeTL b L hw₁ hw₂

/-- Stability of roots in `ℂ_+` at `Im z ≥ 0`. -/
private lemma root_stab (b β : ℝ) (hβ : 0 < β) {L : ℕ} (hL : 1 ≤ L) {z₁ z₂ m₁ m₂ : ℂ}
    (hz₁ : 0 ≤ z₁.im) (hz₂ : 0 ≤ z₂.im) (h₁ : IsDysonRootV b β L z₁ m₁)
    (h₂ : IsDysonRootV b β L z₂ m₂) :
    ‖m₁ - m₂‖ * (β * m₁.im ^ 2 / 2) ≤ ‖z₁ - z₂‖ / β := by
  obtain ⟨hm₁, e₁⟩ := h₁
  obtain ⟨hm₂, e₂⟩ := h₂
  unfold dysonRHSV at e₁ e₂
  have hi : ∀ (z m : ℂ), (z + (β : ℂ) * m).im = z.im + β * m.im := fun z m => by simp
  have hw₁ : 0 < (z₁ + (β : ℂ) * m₁).im := by rw [hi]; positivity
  have hw₂ : 0 < (z₂ + (β : ℂ) * m₂).im := by rw [hi]; positivity
  obtain ⟨hAn, hAre, hd⟩ := stab_core b β hβ hL hw₁ hw₂ hm₁ hm₂ e₁ e₂
    (by rw [hi]; linarith) (by rw [hi]; linarith)
  set A := avgS L (fun k => resL b L (z₁ + (β : ℂ) * m₁) k * resL b L (z₂ + (β : ℂ) * m₂) k)
  have key : (m₁ - m₂) * (1 - (β : ℂ) * A) = (z₁ - z₂) * A := by
    linear_combination hd
  have h1 : ‖m₁ - m₂‖ * ‖1 - (β : ℂ) * A‖ = ‖z₁ - z₂‖ * ‖A‖ := by
    rw [← norm_mul, ← norm_mul, key]
  have h2 : β * m₁.im ^ 2 / 2 ≤ ‖1 - (β : ℂ) * A‖ := hAre.trans (Complex.re_le_norm _)
  calc ‖m₁ - m₂‖ * (β * m₁.im ^ 2 / 2) ≤ ‖m₁ - m₂‖ * ‖1 - (β : ℂ) * A‖ :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖z₁ - z₂‖ * ‖A‖ := h1
    _ ≤ ‖z₁ - z₂‖ * β⁻¹ := mul_le_mul_of_nonneg_left hAn (norm_nonneg _)
    _ = ‖z₁ - z₂‖ / β := by rw [div_eq_mul_inv]

/-! ### Roots: Ward bounds, scaling and shifts -/

private lemma gG_pos (g : ℝ) : 0 < gammaG g := by
  have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold gammaG; positivity

private lemma gG_le_one (g : ℝ) : gammaG g ≤ 1 := by
  unfold gammaG
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_max_left _ _))

private lemma hB_nonneg {g : ℝ} (hg : 0 ≤ g) : 0 ≤ hopB g :=
  div_nonneg hg (le_trans zero_le_one (le_max_left _ _))

private lemma hB_le_one (g : ℝ) : hopB g ≤ 1 := by
  unfold hopB
  rw [div_le_one (lt_of_lt_of_le one_pos (le_max_left _ _))]
  exact le_max_right _ _

private lemma hB_of_one_le {g : ℝ} (hg : 1 ≤ g) : hopB g = 1 := by
  unfold hopB; rw [max_eq_right hg, div_self (by linarith)]

private lemma gG_of_one_le {g : ℝ} (hg : 1 ≤ g) : gammaG g = (g ^ 2)⁻¹ := by
  unfold gammaG; rw [max_eq_right hg]

private lemma root_w_im (β : ℝ) (z m : ℂ) : (z + (β : ℂ) * m).im = z.im + β * m.im := by simp

private lemma root_im_eq {b β : ℝ} {L : ℕ} {z m : ℂ} (h : IsDysonRootV b β L z m) :
    m.im = (z.im + β * m.im) * nsqL b L (z + β * m) := by
  have e := h.2
  unfold dysonRHSV at e
  conv_lhs => rw [e]
  rw [im_freeTL, root_w_im]

private lemma root_ward {b β : ℝ} {L : ℕ} {z m : ℂ} (h : IsDysonRootV b β L z m)
    (hz : 0 ≤ z.im) : β * nsqL b L (z + β * m) ≤ 1 := by
  have e := root_im_eq h
  have hm := h.1
  have hN := nsqL_nonneg b L (z + β * m)
  have h1 : β * m.im * nsqL b L (z + β * m) ≤ m.im := by
    rw [e] at *; nlinarith [mul_nonneg hz hN]
  have h2 : β * nsqL b L (z + β * m) * m.im ≤ 1 * m.im := by linarith
  exact le_of_mul_le_mul_right h2 hm

private lemma root_norm_sq {b β : ℝ} (hβ : 0 ≤ β) {L : ℕ} (hL : 1 ≤ L) {z m : ℂ}
    (h : IsDysonRootV b β L z m) (hz : 0 ≤ z.im) : β * ‖m‖ ^ 2 ≤ 1 := by
  have e := h.2
  unfold dysonRHSV at e
  have h1 : ‖m‖ ^ 2 ≤ nsqL b L (z + β * m) := by
    conv_lhs => rw [e]
    exact norm_freeTL_sq_le b hL _
  have h2 := root_ward h hz
  nlinarith

private lemma root_norm_le {b β : ℝ} (hβ : 0 < β) {L : ℕ} (hL : 1 ≤ L) {z m : ℂ}
    (h : IsDysonRootV b β L z m) (hz : 0 ≤ z.im) : ‖m‖ ≤ 1 / (z.im + β * m.im) := by
  have e := h.2
  unfold dysonRHSV at e
  have hw : 0 < (z + (β : ℂ) * m).im := by rw [root_w_im]; have := h.1; positivity
  conv_lhs => rw [e]
  rw [← root_w_im]
  exact norm_freeTL_le b hL hw

private lemma root_im_ge {b β : ℝ} (hβ : 0 < β) {L : ℕ} (hL : 1 ≤ L) {z m : ℂ}
    (h : IsDysonRootV b β L z m) (hz : 0 ≤ z.im) :
    z.im * (1 / (2 * |b| + ‖z + (β : ℂ) * m‖)) ^ 2 ≤ m.im := by
  have e := root_im_eq h
  have hm := h.1
  have hw : 0 < (z + (β : ℂ) * m).im := by rw [root_w_im]; positivity
  have hN := nsqL_ge b hL hw
  have hN0 := nsqL_nonneg b L (z + β * m)
  rw [e]
  nlinarith [mul_nonneg (mul_nonneg hβ.le hm.le) hN0, mul_le_mul_of_nonneg_left hN hz]

private lemma root_scale {b β : ℝ} {L : ℕ} {z m : ℂ} (h : IsDysonRootV b β L z m) {c : ℝ}
    (hc : 0 < c) : IsDysonRootV (c * b) (c ^ 2 * β) L ((c : ℂ) * z) ((c : ℂ)⁻¹ * m) := by
  obtain ⟨hm, e⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]; positivity
  · unfold dysonRHSV at e ⊢
    have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have h1 : (c : ℂ) * z + ((c ^ 2 * β : ℝ) : ℂ) * ((c : ℂ)⁻¹ * m) =
        (c : ℂ) * (z + (β : ℂ) * m) := by
      push_cast; field_simp
    rw [h1, freeTL_scale b L _ hc.ne', ← e]

private lemma root_shift {b a β : ℝ} {L : ℕ} {z z' m : ℂ} (h : IsDysonRootV b a L z m)
    (e : z + (a : ℂ) * m = z' + (β : ℂ) * m) : IsDysonRootV b β L z' m := by
  obtain ⟨hm, e'⟩ := h
  refine ⟨hm, ?_⟩
  unfold dysonRHSV at e' ⊢
  rw [← e]; exact e'

private lemma mRootV_eq {b a : ℝ} (hb : 0 ≤ b) (ha : 0 < a) {L : ℕ} (hL : 3 ≤ L) {z m : ℂ}
    (hz : 0 ≤ z.im) (h : IsDysonRootV b a L z m) : mRootV b a L z = m :=
  (mRootV_spec b a hb ha L hL z hz).2 m h

private lemma mRootV_root {b a : ℝ} (hb : 0 ≤ b) (ha : 0 < a) {L : ℕ} (hL : 3 ≤ L) {z : ℂ}
    (hz : 0 < z.im) : IsDysonRootV b a L z (mRootV b a L z) :=
  (mRootV_spec b a hb ha L hL z hz.le).1 hz

/-- Pointwise Lipschitz bound of the root at a base point. -/
private lemma root_lip {b a : ℝ} (ha : 0 < a) {L : ℕ} (hL : 1 ≤ L) {z₀ z m₀ m : ℂ}
    (hz₀ : 0 ≤ z₀.im) (hz : 0 ≤ z.im) (h₀ : IsDysonRootV b a L z₀ m₀)
    (h : IsDysonRootV b a L z m) : ‖m₀ - m‖ ≤ 2 / (a ^ 2 * m₀.im ^ 2) * ‖z₀ - z‖ := by
  have hs := root_stab b a ha hL hz₀ hz h₀ h
  have hm := h₀.1
  have hp : 0 < a * m₀.im ^ 2 / 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have : ‖m₀ - m‖ * (a * m₀.im ^ 2 / 2) * (2 * a) ≤ ‖z₀ - z‖ / a * (2 * a) := by gcongr
  have e1 : ‖z₀ - z‖ / a * (2 * a) = 2 * ‖z₀ - z‖ := by field_simp
  nlinarith

private lemma norm_vert (x y y' : ℝ) :
    ‖((x : ℂ) + (y : ℂ) * I) - ((x : ℂ) + (y' : ℂ) * I)‖ = |y - y'| := by
  rw [add_sub_add_left_eq_sub, ← sub_mul, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]

private lemma vert_im (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).im = y := by simp

private lemma vert_re (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).re = x := by simp

/-- Continuity of `y ↦ m(x + iy; a)` on `y > 0`. -/
private lemma vert_continuousAt {b a : ℝ} (hb : 0 ≤ b) (ha : 0 < a) {L : ℕ} (hL : 3 ≤ L)
    (x : ℝ) {y₀ : ℝ} (hy₀ : 0 < y₀) :
    ContinuousAt (fun y : ℝ => mRootV b a L ((x : ℂ) + (y : ℂ) * I)) y₀ := by
  have h₀ := mRootV_root hb ha hL (z := (x : ℂ) + (y₀ : ℂ) * I) (by rw [vert_im]; exact hy₀)
  set m₀ := mRootV b a L ((x : ℂ) + (y₀ : ℂ) * I)
  set K := 2 / (a ^ 2 * m₀.im ^ 2)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hK : Tendsto (fun y : ℝ => K * |y₀ - y|) (𝓝 y₀) (𝓝 0) := by
    have : Continuous (fun y : ℝ => K * |y₀ - y|) := by fun_prop
    simpa using this.tendsto y₀
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hK
  filter_upwards [lt_mem_nhds hy₀] with y hy
  have h := mRootV_root hb ha hL (z := (x : ℂ) + (y : ℂ) * I) (by rw [vert_im]; exact hy)
  have := root_lip ha (by omega) (by rw [vert_im]; exact hy₀.le) (by rw [vert_im]; exact hy.le)
    h₀ h
  rw [norm_vert, norm_sub_rev] at this
  exact this

/-! ### The tube height (A.57) [bl:eq:tube] -/

/-- Uniqueness of the positive solution of `η = (β - a) Im m(x + iη; a)`. -/
private lemma tube_unique {b a β : ℝ} (hb : 0 ≤ b) (ha : 0 < a) (hβ : a < β) {L : ℕ}
    (hL : 3 ≤ L) (x : ℝ) {η₁ η₂ : ℝ} (h₁ : 0 < η₁) (h₂ : 0 < η₂)
    (e₁ : η₁ = (β - a) * (mRootV b a L (x + η₁ * I)).im)
    (e₂ : η₂ = (β - a) * (mRootV b a L (x + η₂ * I)).im) : η₁ = η₂ := by
  set c := β - a with hc
  have hcpos : 0 < c := by linarith
  have hβ0 : 0 < β := by linarith
  set μ₁ := mRootV b a L (x + η₁ * I) with hμ₁
  set μ₂ := mRootV b a L (x + η₂ * I) with hμ₂
  have hr₁ : IsDysonRootV b a L (x + η₁ * I) μ₁ := mRootV_root hb ha hL (by simpa using h₁)
  have hr₂ : IsDysonRootV b a L (x + η₂ * I) μ₂ := mRootV_root hb ha hL (by simpa using h₂)
  set d₁ := x - c * μ₁.re with hd₁
  set d₂ := x - c * μ₂.re with hd₂
  have hw : ∀ (η : ℝ) (μ : ℂ), η = c * μ.im →
      ((x : ℂ) + (η : ℂ) * I) + (a : ℂ) * μ = (((x - c * μ.re : ℝ) : ℂ)) + (β : ℂ) * μ := by
    intro η μ hη
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, mul_one]
      rw [hc]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, mul_one, zero_add]
      rw [hη, hc]; ring
  have hw₁ := hw η₁ μ₁ e₁
  have hw₂ := hw η₂ μ₂ e₂
  have hm₁ := hr₁.1
  have hm₂ := hr₂.1
  have ee₁ : μ₁ = freeTL b L ((d₁ : ℂ) + (β : ℂ) * μ₁) := by
    have := hr₁.2; unfold dysonRHSV at this; rw [← hw₁]; exact this
  have ee₂ : μ₂ = freeTL b L ((d₂ : ℂ) + (β : ℂ) * μ₂) := by
    have := hr₂.2; unfold dysonRHSV at this; rw [← hw₂]; exact this
  have hi : ∀ (d : ℝ) (μ : ℂ), ((d : ℂ) + (β : ℂ) * μ).im = β * μ.im := fun d μ => by simp
  obtain ⟨-, hAre, hd⟩ := stab_core b β hβ0 (by omega) (by rw [hi]; positivity)
    (by rw [hi]; positivity) hm₁ hm₂ ee₁ ee₂ (by rw [hi]) (by rw [hi])
  set A := avgS L (fun k => resL b L ((d₁ : ℂ) + (β : ℂ) * μ₁) k *
    resL b L ((d₂ : ℂ) + (β : ℂ) * μ₂) k)
  set D := 1 - (β : ℂ) * A with hD
  set Δ := μ₁ - μ₂ with hΔ
  have hdd : d₁ - d₂ = -c * Δ.re := by
    rw [hd₁, hd₂, hΔ, Complex.sub_re]; ring
  have key : (β : ℂ) * Δ * D = ((d₁ - d₂ : ℝ) : ℂ) * (1 - D) := by
    have e3 : ((d₁ : ℂ) + (β : ℂ) * μ₁) - ((d₂ : ℂ) + (β : ℂ) * μ₂) =
        ((d₁ - d₂ : ℝ) : ℂ) + (β : ℂ) * Δ := by
      rw [hΔ]; push_cast; ring
    rw [e3] at hd
    rw [hD, hΔ]
    rw [← hΔ]
    linear_combination (β : ℂ) * hd
  have hs : 0 < D.re := lt_of_lt_of_le (by positivity) hAre
  have hre := congrArg Complex.re key
  have him := congrArg Complex.im key
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, zero_mul, sub_zero, zero_sub,
    add_zero] at hre him
  rw [hdd] at hre him
  have hp : Δ.re * (a * (D.re ^ 2 + D.im ^ 2) + c * D.re) = 0 := by
    have hβc : β = a + c := by rw [hc]; ring
    rw [hβc] at hre him
    linear_combination D.re * hre + D.im * him
  have hpos : 0 < a * (D.re ^ 2 + D.im ^ 2) + c * D.re := by positivity
  have hp0 : Δ.re = 0 := by
    rcases mul_eq_zero.mp hp with h | h
    · exact h
    · linarith
  have hd0 : d₁ - d₂ = 0 := by rw [hdd, hp0, mul_zero]
  rw [hd0, Complex.ofReal_zero, zero_mul] at key
  have hD0 : D ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs; exact lt_irrefl _ hs
  have hβ' : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ0.ne'
  have hΔ0 : Δ = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hβ'
      · exact h'
    · exact absurd h hD0
  have : μ₁ = μ₂ := sub_eq_zero.mp hΔ0
  rw [e₁, e₂, this]

/-- Existence of a solution of `η = (β - a) Im m(x + iη; a)` above a subsolution `y₀`. -/
private lemma tube_exists {b a β : ℝ} (hb : 0 ≤ b) (ha : 0 < a) (hβ : a < β) {L : ℕ}
    (hL : 3 ≤ L) (x : ℝ) {y₀ : ℝ} (hy₀ : 0 < y₀)
    (h0 : y₀ ≤ (β - a) * (mRootV b a L (x + y₀ * I)).im) :
    ∃ η, y₀ ≤ η ∧ η = (β - a) * (mRootV b a L (x + η * I)).im := by
  set c := β - a with hc
  have hcpos : 0 < c := by linarith
  set f : ℝ → ℝ := fun y => y - c * (mRootV b a L (x + y * I)).im with hf
  set Y := y₀ + c + 1 with hY
  have hcont : ContinuousOn f (Set.Icc y₀ Y) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hy₀ hy.1
    have h1 := vert_continuousAt hb ha hL x hy0
    exact (continuousAt_id.sub (continuousAt_const.mul
      (Complex.continuous_im.continuousAt.comp h1))).continuousWithinAt
  have hYpos : 0 < Y := by positivity
  have hfY : 0 ≤ f Y := by
    have hr := mRootV_root hb ha hL (z := (x : ℂ) + (Y : ℂ) * I) (by rw [vert_im]; exact hYpos)
    have hn := root_norm_le ha (by omega) hr (by rw [vert_im]; exact hYpos.le)
    rw [vert_im] at hn
    have him := hr.1
    have hle : (mRootV b a L (x + Y * I)).im ≤ 1 / Y := by
      refine (Complex.im_le_norm _).trans (hn.trans ?_)
      exact one_div_le_one_div_of_le hYpos (by nlinarith)
    have h1 : c * (mRootV b a L (x + Y * I)).im ≤ c * (1 / Y) := by gcongr
    have h2 : c * (1 / Y) ≤ c := by
      rw [mul_one_div, div_le_iff₀ hYpos]; nlinarith
    simp only [hf]
    linarith
  have hf0 : f y₀ ≤ 0 := by simp only [hf]; linarith
  obtain ⟨η, hη, hfη⟩ := intermediate_value_Icc (by linarith) hcont ⟨hf0, hfY⟩
  refine ⟨η, hη.1, ?_⟩
  simp only [hf] at hfη
  linarith

/-- The tube height is the solution. -/
private lemma etaTube_eq {b a β : ℝ} (hb : 0 ≤ b) (ha : 0 < a) (hβ : a < β) {L : ℕ}
    (hL : 3 ≤ L) (x : ℝ) {η : ℝ} (hη : 0 < η)
    (e : η = (β - a) * (mRootV b a L (x + η * I)).im) : etaTube b a β L x = η := by
  have hu : ∃! η : ℝ, 0 < η ∧ η = (β - a) * (mRootV b a L (x + η * I)).im :=
    ⟨η, ⟨hη, e⟩, fun η' h' => tube_unique hb ha hβ hL x h'.1 hη h'.2 e⟩
  unfold etaTube
  simp only [hu, ↓reduceDIte]
  have := hu.exists.choose_spec
  exact tube_unique hb ha hβ hL x this.1 hη this.2 e

/-! ### The comparison couplings, Lemma 6.3(a) [da:lem:comparison-parameters] -/

private lemma xi_eq {g s u : ℝ} (hs : 0 < s) (hsu : s ≤ u) :
    xiCmp g s u = Real.sqrt (s / u) * max 1 g / max 1 (gCmp g s u) := by
  have hu : 0 < u := lt_of_lt_of_le hs hsu
  have hM : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hM' : 0 < max 1 (gCmp g s u) := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold xiCmp
  have e : s * gammaG (gCmp g s u) / (u * gammaG g) =
      (s / u) * (max 1 g / max 1 (gCmp g s u)) ^ 2 := by
    unfold gammaG; field_simp
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

private lemma gCmp_facts {g s u : ℝ} (hg : 0 ≤ g) (hs : 0 < s) (hsu : s ≤ u) :
    0 ≤ gCmp g s u ∧ gCmp g s u ≤ g ∧ gCmp g s u ^ 2 = g ^ 2 * (s / u) := by
  have hu : 0 < u := lt_of_lt_of_le hs hsu
  have hr : Real.sqrt (s / u) ≤ 1 := Real.sqrt_le_one.mpr (by rw [div_le_one hu]; exact hsu)
  have hr0 : 0 ≤ Real.sqrt (s / u) := Real.sqrt_nonneg _
  unfold gCmp
  refine ⟨mul_nonneg hg hr0, mul_le_of_le_one_right hg hr, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by positivity)]

private lemma xi_facts {g s u : ℝ} (hs : 0 < s) (hsu : s ≤ u) :
    0 < xiCmp g s u ∧ xiCmp g s u ≤ 1 ∧
      hopB (gCmp g s u) = xiCmp g s u * hopB g ∧
      gammaG (gCmp g s u) = xiCmp g s u ^ 2 * (u / s * gammaG g) := by
  have hu : 0 < u := lt_of_lt_of_le hs hsu
  set r := Real.sqrt (s / u) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr (by rw [div_le_one hu]; exact hsu)
  have hr2 : r ^ 2 = s / u := Real.sq_sqrt (by positivity)
  have hM : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hg' : gCmp g s u = g * r := rfl
  have hM' : 0 < max 1 (gCmp g s u) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hxi := xi_eq (g := g) hs hsu
  rw [← hr] at hxi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hxi]; positivity
  · rw [hxi, div_le_one hM', mul_max_of_nonneg _ _ hr0.le, mul_one, hg']
    exact max_le_max hr1 (le_of_eq (mul_comm r g))
  · rw [hxi]; unfold hopB; rw [hg']; field_simp
  · rw [hxi]; unfold gammaG
    field_simp
    rw [hr2]; field_simp

private lemma inv_smul_c {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) {c : ℂ}
    (hc : c ≠ 0) : (c • B)⁻¹ = c⁻¹ • B⁻¹ := by
  by_cases h : IsUnit B.det
  · have := Matrix.inv_smul' B (Units.mk0 c hc) h
    rw [Units.smul_def, Units.val_mk0] at this
    rw [this, Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0]
  · have h' : ¬ IsUnit (c • B).det := by
      rw [isUnit_iff_ne_zero] at h ⊢
      rw [Matrix.det_smul]
      exact fun h0 => h (by simpa [hc] using h0)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h',
      smul_zero]

/-- One comparison step at a real-energy root: the tube (A.57) [bl:eq:tube], the exact law
(A.58) [bl:eq:exactlaw] and the endpoint identity of Lemma 6.4 [da:lem:positive-height]. -/
private lemma step_core {g : ℝ} (hg : 0 ≤ g) {L : ℕ} (hL : 3 ≤ L) {E : ℝ} {m : ℂ}
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {s u : ℝ} (hs : 0 < s) (hsu : s ≤ u)
    (hu1 : u < 1) :
    let x := (zChar g E m u).re
    let η := etaTube (hopB g) (u * gammaG g) (u / s * gammaG g) L x
    let μ := mRootV (hopB g) (u * gammaG g) L ((x : ℂ) + (η : ℂ) * I)
    let ξ := xiCmp g s u
    zChar g E m u = (x : ℂ) + (etaChar g m u : ℂ) * I ∧
    IsDysonRootV (hopB g) (u * gammaG g) L (zChar g E m u) m ∧
    0 < etaChar g m u ∧ etaChar g m u ≤ η ∧ η = (u / s * gammaG g - u * gammaG g) * μ.im ∧
    IsDysonRootV (hopB g) (u * gammaG g) L ((x : ℂ) + (η : ℂ) * I) μ ∧
    IsDysonRootV (hopB g) (u / s * gammaG g) L
      ((x - (u / s * gammaG g - u * gammaG g) * μ.re : ℝ) : ℂ) μ ∧
    ECmp g L E m s u = ξ * (x - (u / s * gammaG g - u * gammaG g) * μ.re) ∧
    IsDysonRootV (hopB (gCmp g s u)) (gammaG (gCmp g s u)) L (ECmp g L E m s u)
      ((ξ : ℂ)⁻¹ * μ) ∧
    mRoot (gCmp g s u) L (ECmp g L E m s u) = (ξ : ℂ)⁻¹ * μ ∧
    wCmp g L E m s u = (x : ℂ) + (η : ℂ) * I ∧
    wCmp g L E m s u =
      (ξ : ℂ)⁻¹ * zChar (gCmp g s u) (ECmp g L E m s u) ((ξ : ℂ)⁻¹ * μ) s ∧
    dysonMat (hopB g) (u * gammaG g) L (wCmp g L E m s u)
        (mRootV (hopB g) (u * gammaG g) L (wCmp g L E m s u)) =
      (ξ : ℂ) • dysonMat (hopB (gCmp g s u)) (gammaG (gCmp g s u)) L (ECmp g L E m s u)
        ((ξ : ℂ)⁻¹ * μ) := by
  intro x η μ ξ
  have hu : 0 < u := lt_of_lt_of_le hs hsu
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu1
  set γ := gammaG g with hγdef
  set b := hopB g with hbdef
  have hγ : 0 < γ := gG_pos g
  have hb0 : 0 ≤ b := hB_nonneg hg
  set a := u * γ with hadef
  set β := u / s * γ with hβdef
  have ha : 0 < a := by positivity
  have hβa : a < β := by
    rw [hadef, hβdef]
    have : u < u / s := by rw [lt_div_iff₀ hs]; nlinarith
    nlinarith
  have hm0 := hm.1
  -- the characteristic point
  have hzx : zChar g E m u = (x : ℂ) + (etaChar g m u : ℂ) * I := by
    apply Complex.ext
    · simp [x]
    · simp [zChar, etaChar]
  have hroot_u : IsDysonRootV b a L (zChar g E m u) m := by
    refine root_shift hm ?_
    unfold zChar; rw [hadef]; push_cast; ring
  have hη0 : 0 < etaChar g m u := by
    unfold etaChar; have : 0 < 1 - u := by linarith
    positivity
  have hmu : mRootV b a L ((x : ℂ) + (etaChar g m u : ℂ) * I) = m := by
    rw [← hzx]; exact mRootV_eq hb0 ha hL (by rw [hzx, vert_im]; exact hη0.le) hroot_u
  have hsub : etaChar g m u ≤ (β - a) * (mRootV b a L (x + etaChar g m u * I)).im := by
    rw [hmu]; unfold etaChar
    have h1 : (1 - u) * γ ≤ β - a := by
      rw [hβdef, hadef]
      have : 1 ≤ u / s := by rw [le_div_iff₀ hs]; linarith
      nlinarith
    exact mul_le_mul_of_nonneg_right h1 hm0.le
  obtain ⟨η', hη'0, hη'⟩ := tube_exists hb0 ha hβa hL x hη0 hsub
  have hηeq : η = η' := etaTube_eq hb0 ha hβa hL x (lt_of_lt_of_le hη0 hη'0) hη'
  have hηpos : 0 < η := by rw [hηeq]; exact lt_of_lt_of_le hη0 hη'0
  have hηe : η = (β - a) * μ.im := by
    change η = (β - a) * (mRootV b a L ((x : ℂ) + (η : ℂ) * I)).im
    rw [hηeq]; exact hη'
  have hμr : IsDysonRootV b a L ((x : ℂ) + (η : ℂ) * I) μ :=
    mRootV_root hb0 ha hL (by rw [vert_im]; exact hηpos)
  set e := x - (β - a) * μ.re with hedef
  have hμβ : IsDysonRootV b β L (e : ℂ) μ := by
    refine root_shift hμr ?_
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, mul_one, hedef]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, mul_one, zero_add]
      rw [hηe]; ring
  obtain ⟨hξ0, hξ1, hbξ, hγξ⟩ := xi_facts (g := g) hs hsu
  have hE' : ECmp g L E m s u = ξ * e := rfl
  have hroot' : IsDysonRootV (hopB (gCmp g s u)) (gammaG (gCmp g s u)) L (ECmp g L E m s u)
      ((ξ : ℂ)⁻¹ * μ) := by
    have h := root_scale hμβ hξ0
    rw [hbξ, hγξ, hE']
    push_cast
    exact h
  obtain ⟨hg'0, -, -⟩ := gCmp_facts hg hs hsu
  have hmroot : mRoot (gCmp g s u) L (ECmp g L E m s u) = (ξ : ℂ)⁻¹ * μ :=
    mRootV_eq (hB_nonneg hg'0) (gG_pos _) hL (by simp) hroot'
  have hw : wCmp g L E m s u = (x : ℂ) + (η : ℂ) * I := rfl
  have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ0.ne'
  have hzs : zChar (gCmp g s u) (ECmp g L E m s u) ((ξ : ℂ)⁻¹ * μ) s =
      (ξ : ℂ) * ((x : ℂ) + (η : ℂ) * I) := by
    have h1 : zChar (gCmp g s u) (ECmp g L E m s u) ((ξ : ℂ)⁻¹ * μ) s =
        (ξ : ℂ) * ((e : ℂ) + (((1 - s) * β : ℝ) : ℂ) * μ) := by
      unfold zChar; rw [hγξ, hE']; push_cast
      rw [show ((xiCmp g s u : ℝ) : ℂ) = (ξ : ℂ) from rfl, hβdef]; push_cast; field_simp
      rw [hγdef]; ring
    have h2 : (e : ℂ) + (((1 - s) * β : ℝ) : ℂ) * μ = (x : ℂ) + (η : ℂ) * I := by
      have hsβ : (1 - s) * β = β - a := by rw [hβdef, hadef]; field_simp
      rw [hsβ]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, mul_one, hedef]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, mul_one, zero_add]
        rw [hηe]
    rw [h1, h2]
  refine ⟨hzx, hroot_u, hη0, hηeq ▸ hη'0, hηe, hμr, hμβ, hE', hroot', hmroot, hw, ?_, ?_⟩
  · rw [hzs, hw, ← mul_assoc, inv_mul_cancel₀ hξc, one_mul]
  · rw [hw]
    change dysonMat b a L ((x : ℂ) + (η : ℂ) * I) μ = _
    unfold dysonMat
    rw [hbξ, hγξ, hE']
    have h3 : ((ξ * b : ℝ) : ℂ) • cycleAdj L - (((ξ * e : ℝ) : ℂ) +
        ((ξ ^ 2 * β : ℝ) : ℂ) * ((ξ : ℂ)⁻¹ * μ)) • (1 : Matrix (Fin L) (Fin L) ℂ) =
        (ξ : ℂ) • ((b : ℂ) • cycleAdj L - ((x : ℂ) + (η : ℂ) * I + (a : ℂ) * μ) •
          (1 : Matrix (Fin L) (Fin L) ℂ)) := by
      have h4 : ((ξ * e : ℝ) : ℂ) + ((ξ ^ 2 * β : ℝ) : ℂ) * ((ξ : ℂ)⁻¹ * μ) =
          (ξ : ℂ) * ((x : ℂ) + (η : ℂ) * I + (a : ℂ) * μ) := by
        have h5 : (e : ℂ) + (β : ℂ) * μ = (x : ℂ) + (η : ℂ) * I + (a : ℂ) * μ := by
          apply Complex.ext
          · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, mul_one,
              hedef]
            ring
          · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
              Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, mul_one, zero_add]
            rw [hηe]; ring
        rw [← h5]; push_cast; field_simp
      rw [h4, smul_sub, smul_smul, smul_smul]
      push_cast; ring_nf
    rw [h3, inv_smul_c _ hξc, smul_smul, mul_inv_cancel₀ hξc, one_smul]

private lemma sq_bound {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 ≤ t) (h : a * t ^ 2 ≤ 1) :
    a * t ≤ 1 := by
  have h1 : (a * t) ^ 2 ≤ 1 := by
    calc (a * t) ^ 2 = a * (a * t ^ 2) := by ring
      _ ≤ 1 * 1 := mul_le_mul ha1 h (by positivity) zero_le_one
      _ = 1 := one_mul 1
  exact (pow_le_one_iff_of_nonneg (mul_nonneg ha ht) two_ne_zero).mp h1

/-- Lower bound for `Im m(x + iy; a)` on `y ≥ η₀` above a root anchored at `x + iη₀`. -/
private lemma rho_lower {b a a₀ c' X x η₀ y : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (ha₀ : 0 < a₀)
    (ha₀a : a₀ ≤ a) (ha1 : a ≤ 1) {L : ℕ} (hL : 3 ≤ L) (hη₀ : 0 < η₀) {m : ℂ}
    (hm : IsDysonRootV b a L ((x : ℂ) + (η₀ : ℂ) * I) m) (hc' : 0 < c') (hcm : c' ≤ m.im)
    (hX : |x| ≤ X) (hy : η₀ ≤ y) (hy1 : y ≤ 1) :
    min (c' / 2) (a₀ ^ 2 * c' ^ 3 / 4 / (X + 4) ^ 2) ≤
      (mRootV b a L ((x : ℂ) + (y : ℂ) * I)).im := by
  have ha : 0 < a := lt_of_lt_of_le ha₀ ha₀a
  have hy0 : 0 < y := lt_of_lt_of_le hη₀ hy
  have hX0 : 0 ≤ X := le_trans (abs_nonneg _) hX
  have hμ := mRootV_root hb0 ha hL (z := (x : ℂ) + (y : ℂ) * I) (by rw [vert_im]; exact hy0)
  set μ := mRootV b a L ((x : ℂ) + (y : ℂ) * I)
  by_cases hcase : y ≤ η₀ + a₀ ^ 2 * c' ^ 3 / 4
  · refine (min_le_left _ _).trans ?_
    have hl := root_lip ha (by omega) (by rw [vert_im]; exact hη₀.le)
      (by rw [vert_im]; exact hy0.le) hm hμ
    rw [norm_vert, abs_sub_comm, abs_of_nonneg (by linarith)] at hl
    have hmi : c' ^ 2 ≤ m.im ^ 2 := pow_le_pow_left₀ hc'.le hcm 2
    have h1 : 2 / (a ^ 2 * m.im ^ 2) * (y - η₀) ≤ c' / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by have := hm.1; positivity)]
      have h2 : a₀ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ ha₀.le ha₀a 2
      have h3 : 2 * (y - η₀) ≤ a₀ ^ 2 * c' ^ 3 / 2 := by linarith
      have h4 : a₀ ^ 2 * c' ^ 3 / 2 ≤ c' / 2 * (a ^ 2 * m.im ^ 2) := by
        have : a₀ ^ 2 * c' ^ 2 ≤ a ^ 2 * m.im ^ 2 :=
          mul_le_mul h2 hmi (by positivity) (by positivity)
        nlinarith
      linarith
    have h5 : m.im - μ.im ≤ ‖m - μ‖ := by
      rw [← Complex.sub_im]; exact (le_abs_self _).trans (Complex.abs_im_le_norm _)
    linarith
  · push Not at hcase
    refine (min_le_right _ _).trans ?_
    have hg := root_im_ge ha (by omega) hμ (by rw [vert_im]; exact hy0.le)
    rw [vert_im] at hg
    have hn2 := root_norm_sq ha.le (by omega) hμ (by rw [vert_im]; exact hy0.le)
    have haμ : a * ‖μ‖ ≤ 1 := by
      have : (a * ‖μ‖) ^ 2 ≤ 1 := by nlinarith
      nlinarith [norm_nonneg μ]
    have hw : 2 * |b| + ‖(x : ℂ) + (y : ℂ) * I + (a : ℂ) * μ‖ ≤ X + 4 := by
      have h1 : ‖(x : ℂ) + (y : ℂ) * I + (a : ℂ) * μ‖ ≤ |x| + y + a * ‖μ‖ := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans ?_) ?_
        · rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy0]
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
      rw [abs_of_nonneg hb0]
      linarith
    have hwpos : 0 < 2 * |b| + ‖(x : ℂ) + (y : ℂ) * I + (a : ℂ) * μ‖ := by
      have : 0 < ‖(x : ℂ) + (y : ℂ) * I + (a : ℂ) * μ‖ := by
        refine norm_pos_iff.mpr fun h => ?_
        have := congrArg Complex.im h
        rw [root_w_im, vert_im, Complex.zero_im] at this
        have := hμ.1
        nlinarith
      positivity
    have h6 : 1 / (X + 4) ≤ 1 / (2 * |b| + ‖(x : ℂ) + (y : ℂ) * I + (a : ℂ) * μ‖) :=
      one_div_le_one_div_of_le hwpos hw
    have h7 : (1 / (X + 4)) ^ 2 ≤ (1 / (2 * |b| + ‖(x : ℂ) + (y : ℂ) * I + (a : ℂ) * μ‖)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h6 2
    have h8 : a₀ ^ 2 * c' ^ 3 / 4 / (X + 4) ^ 2 ≤ y * (1 / (X + 4)) ^ 2 := by
      rw [div_pow, one_pow, mul_one_div]
      gcongr
      nlinarith [sq_nonneg a₀, pow_pos hc' 3]
    calc _ ≤ y * (1 / (X + 4)) ^ 2 := h8
      _ ≤ _ := mul_le_mul_of_nonneg_left h7 hy0.le
      _ ≤ μ.im := hg

/-- Bounded-coupling bookkeeping of one comparison step. -/
private lemma bdd_setup {C B₀ c' : ℝ} (hc' : 0 < c') {g : ℝ}
    (hg : 0 ≤ g) (hgC : g ≤ C) {L : ℕ} (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ B₀) {m : ℂ}
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (hcm : c' ≤ m.im) {s u : ℝ} (hs : 1 / 2 ≤ s)
    (hsu : s ≤ u) (hu1 : u < 1) :
    1 / (2 * max 1 C ^ 2) ≤ u * gammaG g ∧ u * gammaG g ≤ 1 ∧
      |(zChar g E m u).re| ≤ B₀ + 1 / c' ∧
      u / s * gammaG g - u * gammaG g ≤ u * gammaG g ∧
      etaTube (hopB g) (u * gammaG g) (u / s * gammaG g) L (zChar g E m u).re ≤ 1 ∧
      ∀ y : ℝ, etaChar g m u ≤ y → y ≤ 1 →
        min (c' / 2) ((1 / (2 * max 1 C ^ 2)) ^ 2 * c' ^ 3 / 4 / (B₀ + 1 / c' + 4) ^ 2) ≤
          (mRootV (hopB g) (u * gammaG g) L (((zChar g E m u).re : ℂ) + (y : ℂ) * I)).im := by
  have hs0 : 0 < s := by linarith
  have hu : 0 < u := by linarith
  have H := step_core hg hL hm hs0 hsu hu1
  dsimp only at H
  obtain ⟨hzx, hroot_u, hη0, hηge, hηe, hμr, -, -⟩ := H
  set x := (zChar g E m u).re with hx
  set γ := gammaG g with hγdef
  set η := etaTube (hopB g) (u * γ) (u / s * γ) L x with hηdef
  set μ := mRootV (hopB g) (u * γ) L ((x : ℂ) + (η : ℂ) * I) with hμdef
  have hγ : 0 < γ := gG_pos g
  have hγ1 : γ ≤ 1 := gG_le_one g
  have hM : 1 ≤ max 1 C := le_max_left _ _
  have hγC : 1 / max 1 C ^ 2 ≤ γ := by
    rw [hγdef]; unfold gammaG
    rw [one_div]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _))
      (max_le_max le_rfl hgC) 2)
  have ha₀ : 1 / (2 * max 1 C ^ 2) ≤ u * γ := by
    have : 1 / (2 * max 1 C ^ 2) = (1 / 2) * (1 / max 1 C ^ 2) := by field_simp
    rw [this]; exact mul_le_mul (by linarith) hγC (by positivity) hu.le
  have ha1 : u * γ ≤ 1 := by nlinarith
  have hm0 := hm.1
  have hnm := root_norm_le hγ (by omega) hm (by simp)
  simp only [Complex.ofReal_im, zero_add] at hnm
  have hγm : γ * ‖m‖ ≤ 1 / c' := by
    have h1 : γ * ‖m‖ ≤ 1 / m.im := by
      rw [le_div_iff₀ hm0]
      have := mul_le_mul_of_nonneg_left hnm (by positivity : 0 ≤ γ * m.im)
      rw [mul_one_div_cancel (by positivity)] at this
      nlinarith
    exact h1.trans (one_div_le_one_div_of_le hc' hcm)
  have hX : |x| ≤ B₀ + 1 / c' := by
    have e : x = E + (1 - u) * γ * m.re := by
      rw [hx, hγdef]; unfold zChar
      rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add hE ?_)
    rw [abs_mul, abs_of_nonneg (by nlinarith : 0 ≤ (1 - u) * γ)]
    have : |m.re| ≤ ‖m‖ := Complex.abs_re_le_norm m
    have h2 : (1 - u) * γ * |m.re| ≤ γ * ‖m‖ := by
      have : (1 - u) * γ ≤ γ := by nlinarith
      exact mul_le_mul this (Complex.abs_re_le_norm m) (abs_nonneg _) hγ.le
    linarith
  have hc0 : u / s * γ - u * γ ≤ u * γ := by
    have : u / s ≤ 2 * u := by rw [div_le_iff₀ hs0]; nlinarith
    have := mul_le_mul_of_nonneg_right this hγ.le
    linarith
  have hc0pos : 0 ≤ u / s * γ - u * γ := by
    have : u ≤ u / s := by rw [le_div_iff₀ hs0]; nlinarith
    have := mul_le_mul_of_nonneg_right this hγ.le
    linarith
  have hn2 := root_norm_sq (by positivity : 0 ≤ u * γ) (by omega) hμr
    (by rw [vert_im]; linarith)
  have hη1 : η ≤ 1 := by
    have h1 : η ≤ (u / s * γ - u * γ) * ‖μ‖ := by
      rw [hηe]; exact mul_le_mul_of_nonneg_left (Complex.im_le_norm μ) hc0pos
    have h2 : ((u / s * γ - u * γ) * ‖μ‖) ^ 2 ≤ 1 := by
      have h4 : (u / s * γ - u * γ) ^ 2 ≤ (u * γ) ^ 2 := pow_le_pow_left₀ hc0pos hc0 2
      calc ((u / s * γ - u * γ) * ‖μ‖) ^ 2 = (u / s * γ - u * γ) ^ 2 * ‖μ‖ ^ 2 := by ring
        _ ≤ (u * γ) ^ 2 * ‖μ‖ ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
        _ = (u * γ) * (u * γ * ‖μ‖ ^ 2) := by ring
        _ ≤ 1 * 1 := mul_le_mul ha1 hn2 (by positivity) zero_le_one
        _ = 1 := one_mul 1
    have h3 : (u / s * γ - u * γ) * ‖μ‖ ≤ 1 := by
      have h5 : 0 ≤ (u / s * γ - u * γ) * ‖μ‖ := mul_nonneg hc0pos (norm_nonneg μ)
      exact (pow_le_one_iff_of_nonneg h5 two_ne_zero).mp h2
    linarith
  refine ⟨ha₀, ha1, hX, hc0, hη1, fun y hy hy1 => ?_⟩
  have hroot0 : IsDysonRootV (hopB g) (u * γ) L ((x : ℂ) + (etaChar g m u : ℂ) * I) m := by
    rw [← hzx]; exact hroot_u
  exact rho_lower (hB_nonneg hg) (hB_le_one g) (by positivity) ha₀ ha1 hL hη0 hroot0 hc' hcm hX
    hy hy1

/-- Lemma 6.3(a) [da:lem:comparison-parameters], bounded coupling: (6.9)
[da:eq:comparison-parameters], (A.59) [bl:eq:backbuffer] and the endpoint identity of Lemma 6.4
[da:lem:positive-height]. -/
theorem cmpParams_bdd (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') :
    ∃ C'' : ℝ, ∃ L₀ : ℕ, 1 ≤ C'' ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      ∀ s u : ℝ, 1 / 2 ≤ s → s ≤ u → u < 1 →
      let g' := gCmp g s u
      let E' := ECmp g L E m s u
      let w := wCmp g L E m s u
      let m' := mRoot g' L E'
      RegBdd C C'' C''⁻¹ L g' E' ∧ g' ≤ g ∧
      w.re = (zChar g E m u).re ∧ etaChar g m u ≤ w.im ∧
      w.im ≤ C'' * ((1 - s) / (1 - u)) * etaChar g m u ∧
      w = ((xiCmp g s u : ℝ) : ℂ)⁻¹ * zChar g' E' m' s ∧
      dysonMat (hopB g) (u * gammaG g) L w (mRootV (hopB g) (u * gammaG g) L w) =
        ((xiCmp g s u : ℝ) : ℂ) • dysonMat (hopB g') (gammaG g') L E' m' := by
  set a₀ := 1 / (2 * max 1 C ^ 2) with ha₀def
  set X := B₀ + 1 / c' with hXdef
  set ρm := min (c' / 2) (a₀ ^ 2 * c' ^ 3 / 4 / (X + 4) ^ 2) with hρm
  have ha₀ : 0 < a₀ := by positivity
  have hX0 : 0 < X := by positivity
  have hρm0 : 0 < ρm := lt_min (by positivity) (by positivity)
  set K₁ := 1 / (a₀ * ρm) with hK₁
  set C'' := max 1 (max (X + 1) (max (2 * K₁ / c') (1 / ρm))) with hC''
  refine ⟨C'', 0, le_max_left _ _, ?_⟩
  intro g hg hgC L hL _ E hE m hm hcm s u hs hsu hu1 g' E' w m'
  have hs0 : 0 < s := by linarith
  have hu : 0 < u := by linarith
  obtain ⟨ha₀a, ha1, hX, hc0, hη1, hρ⟩ := bdd_setup hc' hg hgC hL hE hm hcm hs hsu hu1
  have H := step_core hg hL hm hs0 hsu hu1
  dsimp only at H
  obtain ⟨-, -, hη0, hηge, hηe, hμr, -, hE', hroot', hmroot, hw, hwz, hdys⟩ := H
  set x := (zChar g E m u).re with hx
  set γ := gammaG g with hγdef
  set η := etaTube (hopB g) (u * γ) (u / s * γ) L x with hηdef
  set μ := mRootV (hopB g) (u * γ) L ((x : ℂ) + (η : ℂ) * I) with hμdef
  set ξ := xiCmp g s u with hξdef
  obtain ⟨hξ0, hξ1, -, -⟩ := xi_facts (g := g) hs0 hsu
  obtain ⟨hg'0, hg'g, -⟩ := gCmp_facts hg hs0 hsu
  have hγ : 0 < γ := gG_pos g
  have ha : 0 < u * γ := by positivity
  have hm0 := hm.1
  have hμ0 := hμr.1
  have hρη : ρm ≤ μ.im := hρ η hηge hη1
  have hn2 := root_norm_sq ha.le (by omega) hμr (by rw [vert_im]; linarith)
  have haμ : u * γ * ‖μ‖ ≤ 1 := sq_bound ha.le ha1 (norm_nonneg μ) hn2
  have hμK : μ.im ≤ K₁ := by
    have h1 : u * γ * μ.im ^ 2 ≤ 1 := by
      have : μ.im ^ 2 ≤ ‖μ‖ ^ 2 := pow_le_pow_left₀ hμ0.le (Complex.im_le_norm μ) 2
      exact (mul_le_mul_of_nonneg_left this ha.le).trans hn2
    rw [hK₁, le_div_iff₀ (by positivity)]
    have h2 : a₀ * ρm * μ.im ≤ u * γ * μ.im * μ.im :=
      mul_le_mul (mul_le_mul ha₀a hρη hρm0.le ha.le) le_rfl hμ0.le (by positivity)
    have h3 : u * γ * μ.im * μ.im = u * γ * μ.im ^ 2 := by ring
    have h4 : μ.im * (a₀ * ρm) = a₀ * ρm * μ.im := by ring
    linarith
  have hm'eq : m' = (ξ : ℂ)⁻¹ * μ := hmroot
  have hm'im : m'.im = ξ⁻¹ * μ.im := by
    rw [hm'eq, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
  have hρm'le : μ.im ≤ m'.im := by
    rw [hm'im]; exact le_mul_of_one_le_left hμ0.le (one_le_inv₀ hξ0 |>.mpr hξ1)
  have hC''1 : 1 ≤ C'' := le_max_left _ _
  have hC''X : X + 1 ≤ C'' := (le_max_left _ _).trans (le_max_right _ _)
  have hC''K : 2 * K₁ / c' ≤ C'' :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hC''ρ : 1 / ρm ≤ C'' :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨⟨hg'0, hg'g.trans hgC, ?_, ?_, ?_⟩, hg'g, ?_, ?_, ?_, ?_, ?_⟩
  · -- the energy
    change |ECmp g L E m s u| ≤ C''
    rw [hE', abs_mul, abs_of_pos hξ0]
    have h1 : |x - (u / s * γ - u * γ) * μ.re| ≤ X + 1 := by
      refine (abs_sub _ _).trans (add_le_add hX ?_)
      have hc0pos : 0 ≤ u / s * γ - u * γ := by
        have : u ≤ u / s := by rw [le_div_iff₀ hs0]; nlinarith
        have := mul_le_mul_of_nonneg_right this hγ.le
        linarith
      rw [abs_mul, abs_of_nonneg hc0pos]
      calc (u / s * γ - u * γ) * |μ.re| ≤ (u * γ) * ‖μ‖ :=
            mul_le_mul hc0 (Complex.abs_re_le_norm μ) (abs_nonneg _) ha.le
        _ ≤ 1 := haμ
    calc ξ * |x - (u / s * γ - u * γ) * μ.re| ≤ 1 * (X + 1) :=
          mul_le_mul hξ1 h1 (abs_nonneg _) zero_le_one
      _ ≤ C'' := by linarith
  · show IsDysonRootV (hopB g') (gammaG g') L E' (mRoot g' L E')
    rw [show mRoot g' L E' = m' from rfl, hm'eq]; exact hroot'
  · show C''⁻¹ ≤ (mRoot g' L E').im
    rw [show mRoot g' L E' = m' from rfl]
    have : C''⁻¹ ≤ ρm := by
      rw [inv_le_comm₀ (by linarith) hρm0]; rw [one_div] at hC''ρ; exact hC''ρ
    linarith
  · rw [show w = (x : ℂ) + (η : ℂ) * I from hw, vert_re]
  · rw [show w = (x : ℂ) + (η : ℂ) * I from hw, vert_im]; exact hηge
  · rw [show w = (x : ℂ) + (η : ℂ) * I from hw, vert_im]
    have hs1 : s < 1 := lt_of_le_of_lt hsu hu1
    have h1u : 0 < 1 - u := by linarith
    have hc0' : u / s * γ - u * γ ≤ 2 * γ * (1 - s) := by
      have : u / s * γ - u * γ = u * γ * (1 - s) / s := by field_simp
      rw [this, div_le_iff₀ hs0]
      have h1s : 0 ≤ γ * (1 - s) := mul_nonneg hγ.le (by linarith)
      calc u * γ * (1 - s) = u * (γ * (1 - s)) := by ring
        _ ≤ (2 * s) * (γ * (1 - s)) := mul_le_mul_of_nonneg_right (by linarith) h1s
        _ = 2 * γ * (1 - s) * s := by ring
    have hη0' : etaChar g m u = (1 - u) * γ * m.im := rfl
    rw [hη0', hηe]
    have e1 : C'' * ((1 - s) / (1 - u)) * ((1 - u) * γ * m.im) = C'' * (1 - s) * γ * m.im := by
      field_simp
    rw [e1]
    have hμK' : (u / s * γ - u * γ) * μ.im ≤ 2 * γ * (1 - s) * K₁ :=
      mul_le_mul hc0' hμK hμ0.le (mul_nonneg (mul_nonneg zero_le_two hγ.le) (by linarith))
    have hK : 2 * K₁ ≤ C'' * c' := by rw [div_le_iff₀ hc'] at hC''K; linarith
    have h1s : 0 ≤ 1 - s := by linarith
    calc (u / s * γ - u * γ) * μ.im ≤ 2 * γ * (1 - s) * K₁ := hμK'
      _ = γ * (1 - s) * (2 * K₁) := by ring
      _ ≤ γ * (1 - s) * (C'' * c') := by gcongr
      _ ≤ γ * (1 - s) * (C'' * m.im) := by gcongr
      _ = C'' * (1 - s) * γ * m.im := by ring
  · rw [show m' = (ξ : ℂ)⁻¹ * μ from hm'eq]; exact hwz
  · rw [show m' = (ξ : ℂ)⁻¹ * μ from hm'eq]; exact hdys

/-! ### The Dyson matrix along a vertical segment -/

private lemma cycleAdj_transpose (L : ℕ) : (cycleAdj L).transpose = cycleAdj L := by
  ext i j
  simp only [Matrix.transpose_apply, cycleAdj, Matrix.of_apply]
  rw [add_comm]

/-- `bA_L - w` is invertible for `Im w > 0`. -/
private lemma cyc_isUnit (b : ℝ) (L : ℕ) {w : ℂ} (hw : 0 < w.im) :
    IsUnit ((b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ)).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 : dotProduct (star v)
      (Matrix.mulVec ((b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ)) v) = 0 := by
    rw [hBv, dotProduct_zero]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, dotProduct_smul] at h1
  have hH := (cycleAdj_isHermitian L).im_star_dotProduct_mulVec_self v
  have hS : dotProduct (star v) v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  rw [hS] at h1
  have him := congrArg Complex.im h1
  simp only [smul_eq_mul, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, mul_zero, Complex.zero_im] at him
  have hH' : (dotProduct (star v) (Matrix.mulVec (cycleAdj L) v)).im = 0 := hH
  rw [hH'] at him
  have him' : w.im * ∑ i, ‖v i‖ ^ 2 = 0 := by linarith
  have hsum : ∑ i, ‖v i‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp him' with h | h
    · linarith
    · exact h
  apply hv
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖v i‖)).mp hsum i
    (Finset.mem_univ i)
  simpa using this

/-- The Dyson matrix is symmetric. -/
private lemma dysonMat_symm (b β : ℝ) (L : ℕ) (z m : ℂ) (i j : Fin L) :
    dysonMat b β L z m i j = dysonMat b β L z m j i := by
  have h : (dysonMat b β L z m).transpose = dysonMat b β L z m := by
    unfold dysonMat
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_smul, Matrix.transpose_one, cycleAdj_transpose]
  conv_lhs => rw [← h]
  rfl

/-- Resolvent identity for `(bA_L - w)⁻¹`. -/
private lemma cyc_resolvent (b : ℝ) (L : ℕ) {w₁ w₂ : ℂ} (h₁ : 0 < w₁.im) (h₂ : 0 < w₂.im) :
    ((b : ℂ) • cycleAdj L - w₁ • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ -
      ((b : ℂ) • cycleAdj L - w₂ • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ =
      (w₁ - w₂) • (((b : ℂ) • cycleAdj L - w₁ • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ *
        ((b : ℂ) • cycleAdj L - w₂ • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹) := by
  set B₁ := (b : ℂ) • cycleAdj L - w₁ • (1 : Matrix (Fin L) (Fin L) ℂ)
  set B₂ := (b : ℂ) • cycleAdj L - w₂ • (1 : Matrix (Fin L) (Fin L) ℂ)
  have hu₁ := cyc_isUnit b L h₁
  have hu₂ := cyc_isUnit b L h₂
  have e : B₂ - B₁ = (w₁ - w₂) • (1 : Matrix (Fin L) (Fin L) ℂ) := by
    simp only [B₁, B₂, sub_smul]; abel
  calc B₁⁻¹ - B₂⁻¹ = B₁⁻¹ * (B₂ * B₂⁻¹) - (B₁⁻¹ * B₁) * B₂⁻¹ := by
        rw [Matrix.mul_nonsing_inv _ hu₂, Matrix.nonsing_inv_mul _ hu₁, Matrix.mul_one,
          Matrix.one_mul]
    _ = B₁⁻¹ * (B₂ - B₁) * B₂⁻¹ := by noncomm_ring
    _ = _ := by rw [e, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- The root is the scaled finite-cycle solution, so it is holomorphic on `ℂ_+`. -/
private lemma mRootV_diffAt {b a : ℝ} (hb : 0 ≤ b) (ha : 0 < a) {L : ℕ} (hL : 3 ≤ L) {z₀ : ℂ}
    (hz₀ : 0 < z₀.im) : DifferentiableAt ℂ (mRootV b a L) z₀ := by
  set G := b / Real.sqrt a with hG
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hG0 : 0 ≤ G := div_nonneg hb hsa.le
  set M := max 1 G with hM
  have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  set c := (M * Real.sqrt a)⁻¹ with hc
  have hcpos : 0 < c := by positivity
  have hcb : c * b = hopB G := by rw [hopB, ← hM, hc, hG]; field_simp
  have hcβ : c ^ 2 * a = gammaG G := by
    rw [gammaG, ← hM, hc, inv_pow, mul_pow, hsq]; field_simp
  have key : ∀ z : ℂ, 0 < z.im → mRootV b a L z = (c : ℂ) * mDysonL G L ((c : ℂ) * z) := by
    intro z hz
    have hcz : 0 < ((c : ℂ) * z).im := by
      rw [Complex.im_ofReal_mul]; positivity
    have h1 := mDysonL_spec G hG0 L (by omega) _ hcz
    have h2 : IsDysonRootV (hopB G) (gammaG G) L ((c : ℂ) * z) (mDysonL G L ((c : ℂ) * z)) := h1
    rw [← hcb, ← hcβ] at h2
    have h3 := root_scale h2 (inv_pos.mpr hcpos)
    have e1 : c⁻¹ * (c * b) = b := by field_simp
    have e2 : c⁻¹ ^ 2 * (c ^ 2 * a) = a := by field_simp
    have e3 : ((c⁻¹ : ℝ) : ℂ) * ((c : ℂ) * z) = z := by
      have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
      push_cast; field_simp
    rw [e1, e2, e3, Complex.ofReal_inv, inv_inv] at h3
    exact mRootV_eq hb ha hL hz.le h3
  have hd : DifferentiableAt ℂ (fun z => (c : ℂ) * mDysonL G L ((c : ℂ) * z)) z₀ := by
    have hcz : 0 < ((c : ℂ) * z₀).im := by rw [Complex.im_ofReal_mul]; positivity
    have h1 : DifferentiableAt ℂ (mDysonL G L) ((c : ℂ) * z₀) :=
      (mDysonL_differentiableOn G hG0 L (by omega)).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hcz)
    exact (h1.comp z₀ (differentiableAt_id.const_mul _)).const_mul _
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz₀] with z hz
  exact key z hz

/-- Carathéodory form of the derivative. -/
private lemma hasDerivAt_of_factor {f h φ : ℝ → ℂ} {r₀ : ℝ} {h' : ℂ} (hh : HasDerivAt h h' r₀)
    (hφ : ContinuousAt φ r₀) (hf : ∀ᶠ r in 𝓝 r₀, f r - f r₀ = (h r - h r₀) * φ r) :
    HasDerivAt f (h' * φ r₀) r₀ := by
  rw [hasDerivAt_iff_tendsto_slope] at hh ⊢
  have hφ' : Tendsto φ (𝓝[≠] r₀) (𝓝 (φ r₀)) := hφ.tendsto.mono_left nhdsWithin_le_nhds
  refine (hh.mul hφ').congr' ?_
  filter_upwards [nhdsWithin_le_nhds hf] with r hr
  rw [slope_def_module, slope_def_module, hr, smul_mul_assoc]

/-- The derivative of the Dyson matrix along `z = x + ihr`: `∂_r M = w'M²` with
`w'(1 - aM²_ii) = ih`, (A.66) [da:eq:height-derivative-identities]. -/
private lemma seg_deriv {b a h : ℝ} (hb : 0 ≤ b) (ha : 0 < a) (hh : 0 < h) {L : ℕ} (hL : 3 ≤ L)
    (x : ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ w' : ℂ,
      (∀ i j, HasDerivAt (fun r : ℝ => dysonMat b a L ((x : ℂ) + ((h * r : ℝ) : ℂ) * I)
          (mRootV b a L ((x : ℂ) + ((h * r : ℝ) : ℂ) * I)) i j)
        (w' * (dysonMat b a L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I)
          (mRootV b a L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I)) *
          dysonMat b a L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I)
          (mRootV b a L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I))) i j) r₀) ∧
      ∀ i, w' * (1 - (a : ℂ) * (dysonMat b a L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I)
          (mRootV b a L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I)) *
          dysonMat b a L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I)
          (mRootV b a L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I))) i i) = (h : ℂ) * I := by
  set zf : ℝ → ℂ := fun r => (x : ℂ) + ((h * r : ℝ) : ℂ) * I with hzf
  set μf : ℝ → ℂ := fun r => mRootV b a L (zf r) with hμf
  set wf : ℝ → ℂ := fun r => zf r + (a : ℂ) * μf r with hwf
  set Bf : ℝ → Matrix (Fin L) (Fin L) ℂ :=
    fun r => (b : ℂ) • cycleAdj L - wf r • (1 : Matrix (Fin L) (Fin L) ℂ) with hBf
  have hzim : ∀ r, (zf r).im = h * r := fun r => by simp [hzf]
  have hroot : ∀ r, 0 < r → IsDysonRootV b a L (zf r) (μf r) := fun r hr =>
    mRootV_root hb ha hL (by rw [hzim]; positivity)
  have hwim : ∀ r, 0 < r → 0 < (wf r).im := by
    intro r hr
    simp only [hwf]
    rw [root_w_im, hzim]
    have := (hroot r hr).1
    positivity
  have hS : ∀ r, dysonMat b a L (zf r) (μf r) = (Bf r)⁻¹ := fun r => rfl
  -- the derivative of the path and of the root
  have hz' : HasDerivAt zf ((h : ℂ) * I) r₀ := by
    have h1 : HasDerivAt (fun r : ℝ => ((h * r : ℝ) : ℂ)) (h : ℂ) r₀ := by
      have := ((hasDerivAt_id r₀).const_mul h).ofReal_comp
      simpa using this
    simpa [hzf] using (h1.mul_const I).const_add (x : ℂ)
  have hdμ : DifferentiableAt ℂ (mRootV b a L) (zf r₀) :=
    mRootV_diffAt hb ha hL (by rw [hzim]; positivity)
  set μ' := deriv (mRootV b a L) (zf r₀) * ((h : ℂ) * I) with hμ'
  have hμd : HasDerivAt μf μ' r₀ := hdμ.hasDerivAt.comp r₀ hz'
  set w' := (h : ℂ) * I + (a : ℂ) * μ' with hw'
  have hwd : HasDerivAt wf w' r₀ := hz'.add (hμd.const_mul (a : ℂ))
  -- continuity of the inverse
  have hBcont : ContinuousAt Bf r₀ := by
    have : ContinuousAt wf r₀ := hwd.continuousAt
    exact continuousAt_const.sub (this.smul continuousAt_const)
  have hdet : (Bf r₀).det ≠ 0 := (cyc_isUnit b L (hwim r₀ hr₀)).ne_zero
  have hinvc : ContinuousAt (fun r => (Bf r)⁻¹) r₀ := by
    have h1 : ContinuousAt Inv.inv (Bf r₀) := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hdet
    exact h1.comp hBcont
  have hder : ∀ i j, HasDerivAt (fun r => dysonMat b a L (zf r) (μf r) i j)
      (w' * ((Bf r₀)⁻¹ * (Bf r₀)⁻¹) i j) r₀ := by
    intro i j
    refine hasDerivAt_of_factor (φ := fun r => ((Bf r)⁻¹ * (Bf r₀)⁻¹) i j) hwd ?_ ?_
    · have h1 : ContinuousAt (fun r => (Bf r)⁻¹ * (Bf r₀)⁻¹) r₀ :=
        hinvc.mul continuousAt_const
      exact (continuous_apply_apply i j).continuousAt.comp h1
    · filter_upwards [lt_mem_nhds hr₀] with r hr
      have hres := cyc_resolvent b L (hwim r hr) (hwim r₀ hr₀)
      simp only [hS]
      have := congrFun (congrFun hres i) j
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
      exact this
  refine ⟨w', fun i j => hder i j, fun i => ?_⟩
  -- the diagonal is the root
  have hdiag : ∀ᶠ r in 𝓝 r₀, dysonMat b a L (zf r) (μf r) i i = μf r := by
    filter_upwards [lt_mem_nhds hr₀] with r hr
    rw [dysonMat_diag b a L (by omega) _ _ (by have := hwim r hr; simpa [hwf] using this)]
    exact ((hroot r hr).2).symm
  have h1 : HasDerivAt μf (w' * ((Bf r₀)⁻¹ * (Bf r₀)⁻¹) i i) r₀ :=
    (hder i i).congr_of_eventuallyEq (hdiag.mono fun r hr => hr.symm)
  have h2 : μ' = w' * ((Bf r₀)⁻¹ * (Bf r₀)⁻¹) i i := hμd.unique h1
  change w' * (1 - (a : ℂ) * (((Bf r₀)⁻¹ * (Bf r₀)⁻¹ : Matrix (Fin L) (Fin L) ℂ) i i)) =
    (h : ℂ) * I
  have h3 : w' = (h : ℂ) * I + (a : ℂ) * μ' := rfl
  linear_combination h3 + (a : ℂ) * h2

/-- Strict row dominance of `1 - Q`. -/
private lemma pairQ_isUnit {L : ℕ} {a : ℝ} (ha : 0 ≤ a) {S : Matrix (Fin L) (Fin L) ℂ}
    (h : ∀ i, a * ∑ j, ‖S i j‖ ^ 2 < 1) : IsUnit (1 - pairQ a S).det := by
  rw [isUnit_iff_ne_zero]
  refine det_ne_zero_of_sum_row_lt_diag fun k => ?_
  have hQ : ∀ j, ‖pairQ a S k j‖ = a * ‖S k j‖ ^ 2 := by
    intro j
    simp only [pairQ, Matrix.of_apply, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ha]
  have hoff : ∀ j ∈ Finset.univ.erase k, ‖(1 - pairQ a S) k j‖ = a * ‖S k j‖ ^ 2 := by
    intro j hj
    have hjk : k ≠ j := fun e => (Finset.mem_erase.mp hj).1 e.symm
    rw [Matrix.sub_apply, Matrix.one_apply_ne hjk, zero_sub, norm_neg, hQ]
  rw [Finset.sum_congr rfl hoff]
  have hdiag : 1 - a * ‖S k k‖ ^ 2 ≤ ‖(1 - pairQ a S) k k‖ := by
    rw [Matrix.sub_apply, Matrix.one_apply_eq]
    have := norm_sub_norm_le (1 : ℂ) (pairQ a S k k)
    rw [norm_one, hQ] at this
    linarith
  have hsum := Finset.add_sum_erase Finset.univ (fun j => a * ‖S k j‖ ^ 2) (Finset.mem_univ k)
  have h' : ∑ j, a * ‖S k j‖ ^ 2 < 1 := by rw [← Finset.mul_sum]; exact h k
  linarith

/-- Bounds for `∂_r M = w'M²` from bounds on `M` and a stable row of `(1 - Q)⁻¹`. -/
private lemma deriv_bounds {L : ℕ} (hL : 1 ≤ L) {S : Matrix (Fin L) (Fin L) ℂ}
    {a h CM CR CS : ℝ} {w' : ℂ} (hh : 0 < h) (hsym : ∀ i j, S i j = S j i)
    (hid : ∀ i, w' * (1 - (a : ℂ) * (S * S) i i) = (h : ℂ) * I)
    (hinv : IsUnit (1 - pairQ a S).det) (hM : ∀ i j, ‖S i j‖ ≤ CM)
    (hR : ∀ i, h * ∑ j, ‖S i j‖ ≤ CR) (hS : ∀ i, ∑ j, ‖(1 - pairQ a S)⁻¹ i j‖ ≤ CS) :
    ‖w'‖ ≤ h * CS ∧ (∀ i j, ‖w' * (S * S) i j‖ ≤ CS * CM * CR) ∧
      ∀ i, h * ∑ j, ‖w' * (S * S) i j‖ ≤ CS * CR ^ 2 := by
  have i0 : Fin L := ⟨0, by omega⟩
  have hhI : (h : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne') Complex.I_ne_zero
  have hw0 : w' ≠ 0 := by
    intro e; have := hid i0; rw [e, zero_mul] at this; exact hhI this.symm
  set lam : ℂ := (h : ℂ) * I / w' with hlam
  have hlam0 : lam ≠ 0 := div_ne_zero hhI hw0
  have hrow : ∀ i, 1 - (a : ℂ) * (S * S) i i = lam := by
    intro i; rw [hlam, eq_div_iff hw0, mul_comm]; exact hid i
  set Q := pairQ a S
  set K := (1 - Q)⁻¹
  have hone : Matrix.mulVec (1 - Q) (fun _ => (1 : ℂ)) = lam • (fun _ => (1 : ℂ)) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, mul_one, Pi.smul_apply, smul_eq_mul]
    rw [← hrow i]
    simp only [Matrix.sub_apply, Finset.sum_sub_distrib, Matrix.one_apply, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, Q, pairQ, Matrix.of_apply, Matrix.mul_apply]
    rw [Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsym j i]; ring
  have hK : Matrix.mulVec K (Matrix.mulVec (1 - Q) (fun _ => (1 : ℂ))) = fun _ => 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hinv, Matrix.one_mulVec]
  rw [hone, Matrix.mulVec_smul] at hK
  have hKrow : ∀ i, ∑ j, K i j = lam⁻¹ := by
    intro i
    have := congrFun hK i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, mul_one] at this
    rw [mul_comm] at this
    exact eq_inv_of_mul_eq_one_left this
  have hlamb : ‖lam⁻¹‖ ≤ CS := by
    rw [← hKrow i0]; exact (norm_sum_le _ _).trans (hS i0)
  have hw'eq : w' = (h : ℂ) * I * lam⁻¹ := by
    rw [hlam, inv_div, mul_div, mul_comm, mul_div_assoc, div_self hhI, mul_one]
  have hwn : ‖w'‖ ≤ h * CS := by
    rw [hw'eq, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left hlamb hh.le
  have hCS : 0 ≤ CS := le_trans (norm_nonneg _) hlamb
  have hCM : 0 ≤ CM := le_trans (norm_nonneg _) (hM i0 i0)
  have hrs : ∀ i, ∑ j, ‖S i j‖ ≤ CR / h := fun i => by
    rw [le_div_iff₀ hh, mul_comm]; exact hR i
  have hCR : 0 ≤ CR := le_trans (mul_nonneg hh.le (Finset.sum_nonneg fun j _ => norm_nonneg _))
    (hR i0)
  have hSS : ∀ i j, ‖(S * S) i j‖ ≤ ∑ c, ‖S i c‖ * ‖S c j‖ := by
    intro i j
    rw [Matrix.mul_apply]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => norm_mul _ _))
  refine ⟨hwn, fun i j => ?_, fun i => ?_⟩
  · have h1 : ‖(S * S) i j‖ ≤ CM * (CR / h) := by
      refine (hSS i j).trans ?_
      calc ∑ c, ‖S i c‖ * ‖S c j‖ ≤ ∑ c, ‖S i c‖ * CM :=
            Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hM c j) (norm_nonneg _)
        _ = (∑ c, ‖S i c‖) * CM := by rw [Finset.sum_mul]
        _ ≤ (CR / h) * CM := mul_le_mul_of_nonneg_right (hrs i) hCM
        _ = CM * (CR / h) := by ring
    rw [norm_mul]
    calc ‖w'‖ * ‖(S * S) i j‖ ≤ (h * CS) * (CM * (CR / h)) :=
          mul_le_mul hwn h1 (norm_nonneg _) (by positivity)
      _ = CS * CM * CR := by field_simp
  · have h1 : ∑ j, ‖(S * S) i j‖ ≤ (CR / h) ^ 2 := by
      calc ∑ j, ‖(S * S) i j‖ ≤ ∑ j, ∑ c, ‖S i c‖ * ‖S c j‖ := Finset.sum_le_sum fun j _ => hSS i j
        _ = ∑ c, ‖S i c‖ * ∑ j, ‖S c j‖ := by
            rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]
        _ ≤ ∑ c, ‖S i c‖ * (CR / h) :=
            Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hrs c) (norm_nonneg _)
        _ = (∑ c, ‖S i c‖) * (CR / h) := by rw [Finset.sum_mul]
        _ ≤ (CR / h) * (CR / h) := mul_le_mul_of_nonneg_right (hrs i) (by positivity)
        _ = (CR / h) ^ 2 := by ring
    simp only [norm_mul]
    rw [← Finset.mul_sum]
    calc h * (‖w'‖ * ∑ j, ‖(S * S) i j‖) ≤ h * ((h * CS) * (CR / h) ^ 2) := by
          gcongr
      _ = CS * CR ^ 2 := by field_simp

/-! ### Real-energy form of the vertical segment -/

private lemma pairQ_scale {L : ℕ} (M : Matrix (Fin L) (Fin L) ℂ) {a β : ℝ} (hβ : β ≠ 0) :
    pairQ a M = ((a / β : ℝ) : ℂ) • pairQ β M := by
  ext i j
  simp only [pairQ, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  push_cast; field_simp

private lemma dysonMat_scale (b β : ℝ) (L : ℕ) (z m : ℂ) {c : ℝ} (hc : 0 < c) :
    dysonMat (c * b) (c ^ 2 * β) L ((c : ℂ) * z) ((c : ℂ)⁻¹ * m) =
      (c : ℂ)⁻¹ • dysonMat b β L z m := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  unfold dysonMat
  have h1 : ((c * b : ℝ) : ℂ) • cycleAdj L - ((c : ℂ) * z + ((c ^ 2 * β : ℝ) : ℂ) *
      ((c : ℂ)⁻¹ * m)) • (1 : Matrix (Fin L) (Fin L) ℂ) =
      (c : ℂ) • ((b : ℂ) • cycleAdj L - (z + (β : ℂ) * m) • (1 : Matrix (Fin L) (Fin L) ℂ)) := by
    have h2 : (c : ℂ) * z + ((c ^ 2 * β : ℝ) : ℂ) * ((c : ℂ)⁻¹ * m) =
        (c : ℂ) * (z + (β : ℂ) * m) := by
      push_cast; field_simp
    rw [h2, smul_sub, smul_smul, smul_smul]
    push_cast; ring_nf
  rw [h1, inv_smul_c _ hc']

/-- Model scaling: `(λb, λ²β) = (√γ_G G, γ_G)` with `G = b/√β`. -/
private lemma model_scale {b β : ℝ} (hb : 0 ≤ b) (hβ : 0 < β) :
    ∃ G lam : ℝ, 0 ≤ G ∧ 0 < lam ∧ lam * b = hopB G ∧ lam ^ 2 * β = gammaG G ∧
      G ^ 2 * β = b ^ 2 ∧ lam ^ 2 * (max 1 G ^ 2 * β) = 1 := by
  set G := b / Real.sqrt β with hG
  have hsa : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hsq : Real.sqrt β ^ 2 = β := Real.sq_sqrt hβ.le
  have hG0 : 0 ≤ G := div_nonneg hb hsa.le
  set M := max 1 G with hM
  have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨G, (M * Real.sqrt β)⁻¹, hG0, by positivity, ?_, ?_, ?_, ?_⟩
  · rw [hopB, ← hM, hG]; field_simp
  · rw [gammaG, ← hM, inv_pow, mul_pow, hsq]; field_simp
  · rw [hG, div_pow, hsq]; field_simp
  · rw [← hM, inv_pow, mul_pow, hsq]; field_simp

/-- At `y > 0`, `m(x + iy; a)` is the real-energy root at variance `β = a + y/Im m` and energy
`e = x - (y/Im m) Re m`, with the same Dyson matrix. -/
private lemma vert_rep {b a : ℝ} (hb : 0 ≤ b) (ha : 0 < a) {L : ℕ} (hL : 3 ≤ L) (x y : ℝ)
    (hy : 0 < y) :
    IsDysonRootV b a L ((x : ℂ) + (y : ℂ) * I) (mRootV b a L ((x : ℂ) + (y : ℂ) * I)) ∧
    a < a + y / (mRootV b a L ((x : ℂ) + (y : ℂ) * I)).im ∧
    IsDysonRootV b (a + y / (mRootV b a L ((x : ℂ) + (y : ℂ) * I)).im) L
      ((x - y / (mRootV b a L ((x : ℂ) + (y : ℂ) * I)).im *
        (mRootV b a L ((x : ℂ) + (y : ℂ) * I)).re : ℝ) : ℂ)
      (mRootV b a L ((x : ℂ) + (y : ℂ) * I)) ∧
    dysonMat b a L ((x : ℂ) + (y : ℂ) * I) (mRootV b a L ((x : ℂ) + (y : ℂ) * I)) =
      dysonMat b (a + y / (mRootV b a L ((x : ℂ) + (y : ℂ) * I)).im) L
        ((x - y / (mRootV b a L ((x : ℂ) + (y : ℂ) * I)).im *
          (mRootV b a L ((x : ℂ) + (y : ℂ) * I)).re : ℝ) : ℂ)
        (mRootV b a L ((x : ℂ) + (y : ℂ) * I)) := by
  set μ := mRootV b a L ((x : ℂ) + (y : ℂ) * I) with hμ
  have hr : IsDysonRootV b a L ((x : ℂ) + (y : ℂ) * I) μ :=
    mRootV_root hb ha hL (by rw [vert_im]; exact hy)
  have hρ := hr.1
  have e : ((x : ℂ) + (y : ℂ) * I) + (a : ℂ) * μ =
      ((x - y / μ.im * μ.re : ℝ) : ℂ) + ((a + y / μ.im : ℝ) : ℂ) * μ := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, mul_one]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, mul_one, zero_add]
      field_simp
      ring
  refine ⟨hr, by have : 0 < y / μ.im := by positivity
                 linarith, root_shift hr e, ?_⟩
  unfold dysonMat
  rw [e]

/-- The conclusions of Lemma A.4 [uvp:prop:finite] in variance form (hopping `1`,
variance `β = g⁻²`). -/
private def LpcProp (κ Cκ R c C : ℝ) : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ (Cκ ^ 2)⁻¹ → ∀ L : ℕ, R / β ≤ L → ∀ e : ℝ, |e| ≤ 2 - κ →
    3 ≤ L ∧ IsDysonRootV 1 β L e (mRootV 1 β L e) ∧
    C⁻¹ ≤ (mRootV 1 β L e).im ∧ ‖mRootV 1 β L e‖ ≤ C ∧
    (∀ a b, ‖dysonMat 1 β L e (mRootV 1 β L e) a b‖ ≤ C) ∧
    (∀ a, ∑ b, ‖dysonMat 1 β L e (mRootV 1 β L e) a b‖ ≤ C * β⁻¹) ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ a, ∑ b, Real.exp (c * cycDist a b * β) *
        ‖(1 - (t : ℂ) • pairQ β (dysonMat 1 β L e (mRootV 1 β L e)))⁻¹ a b‖ ≤ C

/-- Lemma A.4 [uvp:prop:finite] in variance form. -/
private lemma lpc_var (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ R c C : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ 0 < c ∧ 0 < C ∧ LpcProp κ Cκ R c C := by
  obtain ⟨Cκ, R, c, C, hCκ, hR, hc, hC, H⟩ := large_periodic_comparison κ hκ hκ2
  refine ⟨Cκ, max R 3, c, C, hCκ, by positivity, hc, hC, ?_⟩
  intro β hβ hβC L hL e he
  have hβ1 : β ≤ 1 := hβC.trans (inv_le_one_of_one_le₀ (one_le_pow₀ hCκ))
  set G := (Real.sqrt β)⁻¹ with hG
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hG2 : G ^ 2 = β⁻¹ := by rw [hG, inv_pow, Real.sq_sqrt hβ.le]
  have hGpos : 0 < G := inv_pos.mpr hsβ
  have hCG : Cκ ≤ G := by
    have h1 : Cκ ^ 2 ≤ G ^ 2 := by
      rw [hG2]; exact (le_inv_comm₀ (by positivity : (0 : ℝ) < Cκ ^ 2) hβ).mpr hβC
    exact (pow_le_pow_iff_left₀ (by linarith) hGpos.le two_ne_zero).mp h1
  have hG1 : 1 ≤ G := hCκ.trans hCG
  have hb : hopB G = 1 := hB_of_one_le hG1
  have hγ : gammaG G = β := by rw [gG_of_one_le hG1, hG2, inv_inv]
  have hRL : R / β ≤ L := le_trans (div_le_div_of_nonneg_right (le_max_left _ _) hβ.le) hL
  have hL' : R * G ^ 2 ≤ L := by rw [hG2, ← div_eq_mul_inv]; exact hRL
  have hL3 : 3 ≤ L := by
    have h1 : (3 : ℝ) ≤ max R 3 / β := by
      rw [le_div_iff₀ hβ]
      calc 3 * β ≤ 3 * 1 := by gcongr
        _ ≤ max R 3 := by rw [mul_one]; exact le_max_right _ _
    exact_mod_cast h1.trans hL
  obtain ⟨m, mInf, hm, -, hmc, hmC, -, -, -, hP⟩ := H G hCG L hL' e he
  simp only [hb, hγ] at hm hP
  have hmeq : mRootV 1 β L e = m := mRootV_eq zero_le_one hβ hL3 (by simp) hm
  obtain ⟨-, -, -, -, hMb, hMrow, hst⟩ := hP
  rw [hmeq]
  have hdiv : ∀ x : ℝ, x / G ^ 2 = x * β := fun x => by rw [hG2, div_inv_eq_mul]
  refine ⟨hL3, hm, hmc, hmC, fun a b => ?_, fun a => ?_, fun t ht0 ht1 a => ?_⟩
  · refine (hMb a b).trans ?_
    have : Real.exp (-(c * cycDist a b / G ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]; positivity
    nlinarith
  · have h1 := hMrow a
    rw [hG2] at h1
    refine le_trans (Finset.sum_le_sum fun b _ => ?_) h1
    have : 1 ≤ Real.exp (c / 2 * cycDist a b / β⁻¹) := Real.one_le_exp (by positivity)
    nlinarith [norm_nonneg (dysonMat 1 β L e m a b)]
  · have h1 := hst t ht0 ht1 a
    simp only [hdiv] at h1
    exact h1

private lemma norm_real_sub_vert (x y : ℝ) (hy : 0 ≤ y) :
    ‖(x : ℂ) - ((x : ℂ) + (y : ℂ) * I)‖ = y := by
  rw [sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hy]

private lemma segMat_eq (g : ℝ) (L : ℕ) (x u y : ℝ) :
    segMat g L x u (y / gammaG g) = dysonMat (hopB g) (u * gammaG g) L ((x : ℂ) + (y : ℂ) * I)
      (mRootV (hopB g) (u * gammaG g) L ((x : ℂ) + (y : ℂ) * I)) := by
  have h : gammaG g * (y / gammaG g) = y := mul_div_cancel₀ y (gG_pos g).ne'
  unfold segMat; rw [h]


/-- Parameters at large coupling: `a = u/g²`. -/
private lemma large_ctx {RA CκA : ℝ} (hRA : 0 < RA) (hCκA : 1 ≤ CκA) {g : ℝ} (hg : CκA ≤ g)
    {L : ℕ} (hL : (2 * RA + 3) * g ^ 2 ≤ L) {u : ℝ} (hu : 1 / 2 ≤ u) (hu1 : u ≤ 1) :
    1 ≤ g ∧ 3 ≤ L ∧ 0 < u * (g ^ 2)⁻¹ ∧ u * (g ^ 2)⁻¹ ≤ (CκA ^ 2)⁻¹ ∧
      g ^ 2 * (u * (g ^ 2)⁻¹) = u ∧ ∀ β : ℝ, u * (g ^ 2)⁻¹ ≤ β → RA / β ≤ L := by
  have hg1 : 1 ≤ g := hCκA.trans hg
  have hg2 : 0 < g ^ 2 := by positivity
  have hu0 : 0 < u := by linarith
  have ha : 0 < u * (g ^ 2)⁻¹ := by positivity
  have hga : g ^ 2 * (u * (g ^ 2)⁻¹) = u := by field_simp
  refine ⟨hg1, ?_, ha, ?_, hga, fun β hβ => ?_⟩
  · have : (3 : ℝ) ≤ L := by
      have h1 : (2 * RA + 3) * 1 ≤ (2 * RA + 3) * g ^ 2 := by gcongr; nlinarith
      linarith
    exact_mod_cast this
  · have h1 : u * (g ^ 2)⁻¹ ≤ (g ^ 2)⁻¹ := mul_le_of_le_one_left (by positivity) hu1
    exact h1.trans (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hg 2))
  · have h1 : RA / β ≤ RA / (u * (g ^ 2)⁻¹) := div_le_div_of_nonneg_left hRA.le ha hβ
    have h2 : RA / (u * (g ^ 2)⁻¹) ≤ 2 * RA * g ^ 2 := by
      rw [div_le_iff₀ ha]
      have : 1 ≤ 2 * (g ^ 2 * (u * (g ^ 2)⁻¹)) := by rw [hga]; linarith
      nlinarith
    have h3 : 2 * RA * g ^ 2 ≤ (2 * RA + 3) * g ^ 2 := by nlinarith
    linarith

/-- The dichotomy of the large-coupling bootstrap: on `0 < y ≤ C₀/g²`, `Im m ≥ c₁/2` forces
`Im m ≥ c₁`, with the bounds of Lemma A.4 [uvp:prop:finite] at the real-energy form. -/
private lemma large_dich {κ C₀ CκA RA cA CA : ℝ} (H : LpcProp (κ / 4) CκA RA cA CA)
    (hκ : 0 < κ) (hC₀ : 0 < C₀) (hCκA : 1 ≤ CκA) (hRA : 0 < RA) (hCA : 0 < CA) {g : ℝ}
    (hgK : (1 + 2 * C₀ * CA) * CκA ≤ g) (hgκ : 16 * C₀ * CA / κ ≤ g) {L : ℕ}
    (hL : (2 * RA + 3) * g ^ 2 ≤ L) {x u : ℝ} (hx : |x| ≤ 2 - κ / 2) (hu : 1 / 2 ≤ u)
    (hu1 : u ≤ 1) {y : ℝ} (hy : 0 < y) (hyC : y ≤ C₀ / g ^ 2)
    (hρ : CA⁻¹ / 2 ≤ (mRootV 1 (u * (g ^ 2)⁻¹) L ((x : ℂ) + (y : ℂ) * I)).im) :
    let a := u * (g ^ 2)⁻¹
    let μ := mRootV 1 a L ((x : ℂ) + (y : ℂ) * I)
    let β := a + y / μ.im
    let e := x - y / μ.im * μ.re
    CA⁻¹ ≤ μ.im ∧ ‖μ‖ ≤ CA ∧ a < β ∧ IsDysonRootV 1 β L (e : ℂ) μ ∧
      dysonMat 1 a L ((x : ℂ) + (y : ℂ) * I) μ = dysonMat 1 β L (e : ℂ) μ ∧
      (∀ i j, ‖dysonMat 1 β L e μ i j‖ ≤ CA) ∧
      (∀ i, ∑ j, ‖dysonMat 1 β L e μ i j‖ ≤ CA * β⁻¹) ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ i, ∑ j, Real.exp (cA * cycDist i j * β) *
          ‖(1 - (t : ℂ) • pairQ β (dysonMat 1 β L e μ))⁻¹ i j‖ ≤ CA := by
  intro a μ β e
  have hK1 : 1 ≤ 1 + 2 * C₀ * CA := by have : 0 ≤ 2 * C₀ * CA := by positivity
                                       linarith
  have hCκAg : CκA ≤ g := le_trans (le_mul_of_one_le_left (by linarith) hK1) hgK
  obtain ⟨hg1, hL3, ha, -, hga, hRa⟩ := large_ctx hRA hCκA hCκAg hL hu hu1
  have hg0 : 0 < g := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  obtain ⟨hr, haβ, hrβ, hMeq⟩ := vert_rep zero_le_one ha hL3 x y hy
  have hρ0 : 0 < μ.im := hr.1
  have hn2 : a * ‖μ‖ ^ 2 ≤ 1 := root_norm_sq ha.le (by omega) hr (by rw [vert_im]; exact hy.le)
  have hμn : ‖μ‖ ≤ 2 * g := by
    have h1 : ‖μ‖ ^ 2 ≤ (2 * g) ^ 2 := by
      have h2 : g ^ 2 * (a * ‖μ‖ ^ 2) ≤ g ^ 2 * 1 := mul_le_mul_of_nonneg_left hn2 hg2.le
      rw [← mul_assoc, hga, mul_one] at h2
      have h3 : ‖μ‖ ^ 2 ≤ 2 * (u * ‖μ‖ ^ 2) := by
        have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * u by linarith) (sq_nonneg ‖μ‖)
        linarith
      have h4 : (2 * g) ^ 2 = 4 * g ^ 2 := by ring
      rw [h4]; linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1
  have hyρ : y / μ.im ≤ 2 * C₀ * CA / g ^ 2 := by
    rw [div_le_iff₀ hρ0]
    have h2 : C₀ / g ^ 2 = 2 * C₀ * CA / g ^ 2 * (CA⁻¹ / 2) := by field_simp
    rw [h2] at hyC
    exact hyC.trans (mul_le_mul_of_nonneg_left hρ (by positivity))
  have hβC : β ≤ (CκA ^ 2)⁻¹ := by
    have h1 : β ≤ (1 + 2 * C₀ * CA) / g ^ 2 := by
      have : a ≤ 1 / g ^ 2 := by rw [one_div]; exact mul_le_of_le_one_left (by positivity) hu1
      change a + y / μ.im ≤ (1 + 2 * C₀ * CA) / g ^ 2
      rw [add_div]
      linarith
    refine h1.trans ?_
    have h2 : ((1 + 2 * C₀ * CA) * CκA) ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ (by positivity) hgK 2
    have h3 : (1 + 2 * C₀ * CA) * CκA ^ 2 ≤ ((1 + 2 * C₀ * CA) * CκA) ^ 2 := by
      have : (1 + 2 * C₀ * CA) * CκA ^ 2 * 1 ≤ (1 + 2 * C₀ * CA) * CκA ^ 2 * (1 + 2 * C₀ * CA) :=
        mul_le_mul_of_nonneg_left hK1 (by positivity)
      nlinarith
    rw [div_le_iff₀ hg2, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    linarith
  have he : |e| ≤ 2 - κ / 4 := by
    have h1 : |e - x| ≤ 2 * C₀ * CA / g ^ 2 * (2 * g) := by
      change |x - y / μ.im * μ.re - x| ≤ _
      rw [sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < y / μ.im)]
      exact mul_le_mul hyρ ((Complex.abs_re_le_norm μ).trans hμn) (abs_nonneg _)
        (by positivity)
    have h2 : 2 * C₀ * CA / g ^ 2 * (2 * g) ≤ κ / 4 := by
      have e1 : 2 * C₀ * CA / g ^ 2 * (2 * g) = 4 * C₀ * CA / g := by field_simp; norm_num
      rw [e1, div_le_iff₀ hg0]
      rw [div_le_iff₀ hκ] at hgκ
      linarith
    have := abs_sub_abs_le_abs_sub e x
    linarith
  obtain ⟨-, -, hc, hnC, hMb, hMrow, hst⟩ := H β (by linarith) hβC L (hRa β haβ.le) e he
  have hμeq : mRootV 1 β L e = μ := mRootV_eq zero_le_one (by linarith) hL3 (by simp) hrβ
  rw [hμeq] at hc hnC hMb hMrow hst
  exact ⟨hc, hnC, haβ, hrβ, hMeq, hMb, hMrow, hst⟩

/-- The large-coupling bootstrap: `Im m(x + iy; u/g²) ≥ c₁` on `0 < y ≤ C₀/g²`. -/
private lemma large_boot {κ C₀ CκA RA cA CA : ℝ} (H : LpcProp (κ / 4) CκA RA cA CA)
    (hκ : 0 < κ) (hC₀ : 0 < C₀) (hCκA : 1 ≤ CκA) (hRA : 0 < RA) (hCA : 0 < CA) {g : ℝ}
    (hgK : (1 + 2 * C₀ * CA) * CκA ≤ g) (hgκ : 16 * C₀ * CA / κ ≤ g) {L : ℕ}
    (hL : (2 * RA + 3) * g ^ 2 ≤ L) {x u : ℝ} (hx : |x| ≤ 2 - κ / 2) (hu : 1 / 2 ≤ u)
    (hu1 : u ≤ 1) {y : ℝ} (hy : 0 < y) (hyC : y ≤ C₀ / g ^ 2) :
    CA⁻¹ ≤ (mRootV 1 (u * (g ^ 2)⁻¹) L ((x : ℂ) + (y : ℂ) * I)).im := by
  have hK1 : 1 ≤ 1 + 2 * C₀ * CA := by have : 0 ≤ 2 * C₀ * CA := by positivity
                                       linarith
  have hCκAg : CκA ≤ g := le_trans (le_mul_of_one_le_left (by linarith) hK1) hgK
  obtain ⟨hg1, hL3, ha, haC, hga, hRa⟩ := large_ctx hRA hCκA hCκAg hL hu hu1
  set a := u * (g ^ 2)⁻¹ with hadef
  set c₁ := CA⁻¹ with hc₁
  have hc₁0 : 0 < c₁ := inv_pos.mpr hCA
  have hx4 : |x| ≤ 2 - κ / 4 := by linarith
  obtain ⟨-, hm₀, hm₀c, -, -, -, -⟩ := H a ha haC L (hRa a le_rfl) x hx4
  set m₀ := mRootV 1 a L x with hm₀def
  have hdich : ∀ y' : ℝ, 0 < y' → y' ≤ C₀ / g ^ 2 →
      c₁ / 2 ≤ (mRootV 1 a L ((x : ℂ) + (y' : ℂ) * I)).im →
      c₁ ≤ (mRootV 1 a L ((x : ℂ) + (y' : ℂ) * I)).im := fun y' hy' hy'C h =>
    (large_dich H hκ hC₀ hCκA hRA hCA hgK hgκ hL hx hu hu1 hy' hy'C h).1
  by_contra hcon
  push Not at hcon
  have hρs2 : (mRootV 1 a L ((x : ℂ) + (y : ℂ) * I)).im < c₁ / 2 := by
    by_contra h; push Not at h
    have := hdich y hy hyC h
    linarith
  set δ := min y (a ^ 2 * c₁ ^ 3 / 4) with hδ
  have hδ0 : 0 < δ := lt_min hy (by positivity)
  have hδys : δ ≤ y := min_le_left _ _
  have hδ1 : δ ≤ a ^ 2 * c₁ ^ 3 / 4 := min_le_right _ _
  have hrδ := mRootV_root zero_le_one ha hL3 (z := (x : ℂ) + (δ : ℂ) * I)
    (by rw [vert_im]; exact hδ0)
  have hl := root_lip ha (by omega) (by simp) (by rw [vert_im]; exact hδ0.le) hm₀ hrδ
  rw [norm_real_sub_vert x δ hδ0.le] at hl
  have hm0i : c₁ ^ 2 ≤ m₀.im ^ 2 := pow_le_pow_left₀ hc₁0.le hm₀c 2
  have hl2 : 2 / (a ^ 2 * m₀.im ^ 2) * δ ≤ c₁ / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by have := hm₀.1; positivity)]
    have h1 : a ^ 2 * c₁ ^ 2 ≤ a ^ 2 * m₀.im ^ 2 := mul_le_mul_of_nonneg_left hm0i (by positivity)
    have h2 : 2 * δ ≤ a ^ 2 * c₁ ^ 3 / 2 := by linarith
    have h3 : a ^ 2 * c₁ ^ 3 / 2 = c₁ / 2 * (a ^ 2 * c₁ ^ 2) := by ring
    have h4 : c₁ / 2 * (a ^ 2 * c₁ ^ 2) ≤ c₁ / 2 * (a ^ 2 * m₀.im ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hδρ : c₁ / 2 ≤ (mRootV 1 a L ((x : ℂ) + (δ : ℂ) * I)).im := by
    have h5 : m₀.im - (mRootV 1 a L ((x : ℂ) + (δ : ℂ) * I)).im ≤
        ‖m₀ - mRootV 1 a L ((x : ℂ) + (δ : ℂ) * I)‖ := by
      rw [← Complex.sub_im]; exact (le_abs_self _).trans (Complex.abs_im_le_norm _)
    linarith
  have hδc := hdich δ hδ0 (hδys.trans hyC) hδρ
  have hcont : ContinuousOn (fun y' : ℝ => (mRootV 1 a L ((x : ℂ) + (y' : ℂ) * I)).im)
      (Set.Icc δ y) := by
    intro y' hy'
    exact (Complex.continuous_im.continuousAt.comp
      (vert_continuousAt zero_le_one ha hL3 x (lt_of_lt_of_le hδ0 hy'.1))).continuousWithinAt
  obtain ⟨y', hy', hy'v⟩ := intermediate_value_Icc' hδys hcont
    (show 3 * c₁ / 4 ∈ Set.Icc _ _ from ⟨by linarith, by linarith⟩)
  have hy'0 : 0 < y' := lt_of_lt_of_le hδ0 hy'.1
  simp only at hy'v
  have := hdich y' hy'0 (hy'.2.trans hyC) (by linarith)
  linarith

/-- Lemma 6.4 [da:lem:positive-height] at large coupling at one point of the direct domain. -/
private lemma large_point {κ C₀ CκA RA cA CA : ℝ} (H : LpcProp (κ / 4) CκA RA cA CA)
    (hκ : 0 < κ) (hC₀ : 0 < C₀) (hCκA : 1 ≤ CκA) (hRA : 0 < RA) (hcA : 0 < cA) (hCA : 0 < CA)
    {g : ℝ} (hgK : (1 + 2 * C₀ * CA) * CκA ≤ g) (hgκ : 16 * C₀ * CA / κ ≤ g) {L : ℕ}
    (hL : (2 * RA + 3) * g ^ 2 ≤ L) {x u : ℝ} (hx : |x| ≤ 2 - κ / 2) (hu : 1 / 2 ≤ u)
    (hu1 : u ≤ 1) {y : ℝ} (hy : 0 < y) (hyC : y ≤ C₀ / g ^ 2) :
    let c := min CA⁻¹ (cA / 2)
    let C' := 2 * CA + 2 + 4 * CA ^ 3
    let z : ℂ := (x : ℂ) + (y : ℂ) * I
    let mu := mRootV (hopB g) (u * gammaG g) L z
    let M := segMat g L x u (y / gammaG g)
    IsDysonRootV (hopB g) (u * gammaG g) L z mu ∧ c ≤ mu.im ∧ mu.im ≤ C' ∧
    (∀ a b, ‖M a b‖ ≤ C') ∧ (∀ a, gammaG g * ∑ b, (‖M a b‖ + ‖M a b‖ ^ 2) ≤ C') ∧
    (∀ a, ∑ b, Real.exp (c * cycDist a b / g ^ 2) *
      ‖(1 - pairQ (u * gammaG g) M)⁻¹ a b‖ ≤ C') ∧
    (∀ a b, DifferentiableAt ℝ (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)) ∧
    (∀ a b, ‖deriv (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)‖ ≤ C') ∧
    ∀ a, gammaG g * ∑ b, ‖deriv (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)‖ ≤ C' := by
  intro c C' z mu M
  have hK1 : 1 ≤ 1 + 2 * C₀ * CA := by have : 0 ≤ 2 * C₀ * CA := by positivity
                                       linarith
  have hCκAg : CκA ≤ g := le_trans (le_mul_of_one_le_left (by linarith) hK1) hgK
  obtain ⟨hg1, hL3, ha, -, hga, -⟩ := large_ctx hRA hCκA hCκAg hL hu hu1
  have hg0 : 0 < g := by linarith
  have hb : hopB g = 1 := hB_of_one_le hg1
  have hγ : gammaG g = (g ^ 2)⁻¹ := gG_of_one_le hg1
  have hu0 : 0 < u := by linarith
  have hboot := large_boot H hκ hC₀ hCκA hRA hCA hgK hgκ hL hx hu hu1 hy hyC
  obtain ⟨hρ, hμn, haβ, hrβ, hMeq, hMb, hMrow, hst⟩ :=
    large_dich H hκ hC₀ hCκA hRA hCA hgK hgκ hL hx hu hu1 hy hyC
      (by have := inv_pos.mpr hCA; linarith)
  obtain ⟨hr, -, -, -⟩ := vert_rep zero_le_one ha hL3 x y hy
  set a := u * (g ^ 2)⁻¹ with hadef
  set μ := mRootV 1 a L ((x : ℂ) + (y : ℂ) * I) with hμ
  set β := a + y / μ.im with hβ
  set e := x - y / μ.im * μ.re with he
  have hβ0 : 0 < β := by linarith
  have hmu : mu = μ := by simp only [mu, z, hb, hγ]; rfl
  have hM : M = dysonMat 1 β L (e : ℂ) μ := by
    simp only [M]; rw [segMat_eq, hb, hγ, ← hadef]; exact hMeq
  set MA := dysonMat 1 β L (e : ℂ) μ with hMA
  have hrowP := pairP_row_sum 1 β hβ0 L (by omega) e μ hrβ
  simp only [pairP, Matrix.of_apply] at hrowP
  have hsq : ∀ i, ∑ j, ‖MA i j‖ ^ 2 = β⁻¹ := by
    intro i
    have := hrowP i
    rw [← Finset.mul_sum, mul_comm] at this
    exact eq_inv_of_mul_eq_one_left this
  have hβa' : β⁻¹ ≤ a⁻¹ := inv_anti₀ ha haβ.le
  have hγa : (g ^ 2)⁻¹ * a⁻¹ ≤ 2 := by
    rw [hadef, mul_inv, inv_inv]
    have : (g ^ 2)⁻¹ * (u⁻¹ * g ^ 2) = u⁻¹ := by field_simp
    rw [this, inv_le_comm₀ hu0 (by norm_num)]; linarith
  have hrow1 : ∀ i, (g ^ 2)⁻¹ * ∑ j, ‖MA i j‖ ≤ 2 * CA := by
    intro i
    calc (g ^ 2)⁻¹ * ∑ j, ‖MA i j‖ ≤ (g ^ 2)⁻¹ * (CA * β⁻¹) :=
          mul_le_mul_of_nonneg_left (hMrow i) (by positivity)
      _ ≤ (g ^ 2)⁻¹ * (CA * a⁻¹) := by gcongr
      _ = CA * ((g ^ 2)⁻¹ * a⁻¹) := by ring
      _ ≤ CA * 2 := mul_le_mul_of_nonneg_left hγa hCA.le
      _ = 2 * CA := by ring
  have hrow2 : ∀ i, (g ^ 2)⁻¹ * ∑ j, ‖MA i j‖ ^ 2 ≤ 2 := by
    intro i
    rw [hsq i]
    calc (g ^ 2)⁻¹ * β⁻¹ ≤ (g ^ 2)⁻¹ * a⁻¹ := by gcongr
      _ ≤ 2 := hγa
  have hQ : pairQ (u * gammaG g) M = ((a / β : ℝ) : ℂ) • pairQ β MA := by
    rw [hM, hγ, ← hadef, pairQ_scale _ hβ0.ne']
  have ht0 : 0 ≤ a / β := by positivity
  have ht1 : a / β ≤ 1 := by rw [div_le_one hβ0]; exact haβ.le
  have hwt : ∀ i j : Fin L,
      Real.exp (c * cycDist i j / g ^ 2) ≤ Real.exp (cA * cycDist i j * β) := by
    intro i j
    apply Real.exp_le_exp.mpr
    have h1 : c / g ^ 2 ≤ cA * β := by
      have h2 : c ≤ cA / 2 := min_le_right _ _
      have h3 : 1 / (2 * g ^ 2) ≤ β := by
        have : 1 / (2 * g ^ 2) ≤ a := by
          rw [hadef, div_le_iff₀ (by positivity)]
          have : u * (g ^ 2)⁻¹ * (2 * g ^ 2) = 2 * u := by field_simp
          rw [this]; linarith
        linarith
      calc c / g ^ 2 ≤ cA / 2 / g ^ 2 := by gcongr
        _ = cA * (1 / (2 * g ^ 2)) := by field_simp
        _ ≤ cA * β := by gcongr
    have hd : (0 : ℝ) ≤ cycDist i j := Nat.cast_nonneg _
    calc c * cycDist i j / g ^ 2 = c / g ^ 2 * cycDist i j := by ring
      _ ≤ cA * β * cycDist i j := mul_le_mul_of_nonneg_right h1 hd
      _ = cA * cycDist i j * β := by ring
  have hstab : ∀ i, ∑ j, Real.exp (c * cycDist i j / g ^ 2) *
      ‖(1 - pairQ (u * gammaG g) M)⁻¹ i j‖ ≤ CA := by
    intro i
    rw [hQ]
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (hst (a / β) ht0 ht1 i)
    exact mul_le_mul_of_nonneg_right (hwt i j) (norm_nonneg _)
  have hstab0 : ∀ i, ∑ j, ‖(1 - pairQ (u * gammaG g) M)⁻¹ i j‖ ≤ CA := by
    intro i
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (hstab i)
    have hc0 : 0 ≤ c := le_min (inv_pos.mpr hCA).le (by positivity)
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))
  have hyγ : 0 < y / gammaG g := div_pos hy (gG_pos g)
  obtain ⟨w', hder, hid⟩ := seg_deriv (hB_nonneg hg0.le)
    (show (0 : ℝ) < u * gammaG g by rw [hγ]; positivity) (gG_pos g) hL3 x hyγ
  have hinv : IsUnit (1 - pairQ (u * gammaG g) M).det := by
    refine pairQ_isUnit (show (0 : ℝ) ≤ u * gammaG g by rw [hγ]; positivity) fun i => ?_
    rw [hM, hγ, ← hadef, hsq i]
    rw [← div_eq_mul_inv, div_lt_one hβ0]; exact haβ
  have hMbM : ∀ i j, ‖M i j‖ ≤ CA := fun i j => by rw [hM]; exact hMb i j
  have hRM : ∀ i, gammaG g * ∑ j, ‖M i j‖ ≤ 2 * CA := fun i => by rw [hM, hγ]; exact hrow1 i
  obtain ⟨-, hd1, hd2⟩ := deriv_bounds (by omega) (gG_pos g) (dysonMat_symm _ _ _ _ _) hid hinv
    hMbM hRM hstab0
  have hderiv : ∀ i j, deriv (fun r : ℝ => segMat g L x u r i j) (y / gammaG g) =
      w' * (M * M) i j := fun i j => (hder i j).deriv
  have hCA3 : 0 ≤ CA ^ 3 := by positivity
  have hC'1 : CA ≤ C' := by simp only [C']; nlinarith
  refine ⟨?_, ?_, ?_, fun i j => (hMbM i j).trans hC'1, fun i => ?_, fun i => (hstab i).trans hC'1,
    fun i j => (hder i j).differentiableAt, fun i j => ?_, fun i => ?_⟩
  · rw [hmu]; simp only [z]; rw [hb, hγ, ← hadef]; exact hr
  · rw [hmu]; exact (min_le_left _ _).trans hρ
  · rw [hmu]; exact (Complex.im_le_norm μ).trans (hμn.trans hC'1)
  · rw [hM, hγ, Finset.sum_add_distrib, mul_add]
    have h1 := hrow1 i; have h2 := hrow2 i
    simp only [C']; nlinarith
  · rw [hderiv]; refine (hd1 i j).trans ?_
    simp only [C']; nlinarith
  · simp only [hderiv]; refine (hd2 i).trans ?_
    simp only [C']; nlinarith

/-- Lemma 6.4 [da:lem:positive-height] at large coupling on the direct domain `|x| ≤ 2 - κ/2`,
`0 < y ≤ C₀/g²`, `1/2 ≤ u ≤ 1`. -/
private lemma ph_large_core (κ C₀ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC₀ : 0 < C₀) :
    ∃ Cκ R c C' : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ 0 < c ∧ 0 < C' ∧ ∀ g : ℝ, Cκ ≤ g →
      ∀ L : ℕ, R * g ^ 2 ≤ L → ∀ x y u : ℝ, |x| ≤ 2 - κ / 2 → 0 < y → y ≤ C₀ / g ^ 2 →
      1 / 2 ≤ u → u ≤ 1 →
      let z : ℂ := (x : ℂ) + (y : ℂ) * I
      let mu := mRootV (hopB g) (u * gammaG g) L z
      let M := segMat g L x u (y / gammaG g)
      IsDysonRootV (hopB g) (u * gammaG g) L z mu ∧ c ≤ mu.im ∧ mu.im ≤ C' ∧
      (∀ a b, ‖M a b‖ ≤ C') ∧ (∀ a, gammaG g * ∑ b, (‖M a b‖ + ‖M a b‖ ^ 2) ≤ C') ∧
      (∀ a, ∑ b, Real.exp (c * cycDist a b / g ^ 2) *
        ‖(1 - pairQ (u * gammaG g) M)⁻¹ a b‖ ≤ C') ∧
      (∀ a b, DifferentiableAt ℝ (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)) ∧
      (∀ a b, ‖deriv (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)‖ ≤ C') ∧
      ∀ a, gammaG g * ∑ b, ‖deriv (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)‖ ≤ C' := by
  obtain ⟨CκA, RA, cA, CA, hCκA, hRA, hcA, hCA, H⟩ := lpc_var (κ / 4) (by linarith) (by linarith)
  have hK1 : 1 ≤ 1 + 2 * C₀ * CA := by have : 0 ≤ 2 * C₀ * CA := by positivity
                                       linarith
  refine ⟨max ((1 + 2 * C₀ * CA) * CκA) (16 * C₀ * CA / κ), 2 * RA + 3, min CA⁻¹ (cA / 2),
    2 * CA + 2 + 4 * CA ^ 3, le_trans (one_le_mul_of_one_le_of_one_le hK1 hCκA) (le_max_left _ _),
    by positivity, lt_min (inv_pos.mpr hCA) (by positivity), by positivity, ?_⟩
  intro g hg L hL x y u hx hy hyC hu hu1
  exact large_point H hκ hC₀ hCκA hRA hcA hCA ((le_max_left _ _).trans hg)
    ((le_max_right _ _).trans hg) hL hx hu hu1 hy hyC

/-! ### Large coupling: moves of the real-energy root -/

private lemma rpow_inv_sq {G : ℝ} (hG : 0 < G) : ((G ^ 2)⁻¹) ^ (-(1 : ℝ) / 2) = G := by
  have h1 : (G ^ 2)⁻¹ = G ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hG.le, Real.rpow_two]
  rw [h1, ← Real.rpow_mul hG.le]
  norm_num

/-- A horizontal move at variance `β`, from (A.21) [fo:eq:terminal-anchor-derivative]. -/
private lemma horiz_move {κ' CκD RD : ℝ}
    (HD : ∀ β : ℝ, 0 < β → CκD ≤ β ^ (-(1 : ℝ) / 2) →
      ∀ L : ℕ, RD / β ≤ L → ∀ e : ℝ, |e| ≤ 2 - κ' →
        IsDysonRootV 1 β L e (mRootV 1 β L e) ∧
        HasDerivAt (fun e' : ℝ => mRootV 1 β L e') (deriv (fun e' : ℝ => mRootV 1 β L e') e) e ∧
        β * ‖deriv (fun e' : ℝ => mRootV 1 β L e') e‖ ≤ 1 / 2)
    {β : ℝ} (hβ : 0 < β) (hβC : CκD ≤ β ^ (-(1 : ℝ) / 2)) {L : ℕ} (hL : RD / β ≤ L)
    {E₁ E₂ : ℝ} (h₁ : |E₁| ≤ 2 - κ') (h₂ : |E₂| ≤ 2 - κ') :
    ‖mRootV 1 β L E₂ - mRootV 1 β L E₁‖ ≤ 1 / (2 * β) * |E₂ - E₁| := by
  have hseg : ∀ e ∈ Set.uIcc E₁ E₂, |e| ≤ 2 - κ' := by
    intro e he
    rw [Set.mem_uIcc] at he
    rw [abs_le] at h₁ h₂ ⊢
    rcases he with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> constructor <;> linarith
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun e' : ℝ => mRootV 1 β L e')
    (s := Set.uIcc E₁ E₂) (C := 1 / (2 * β))
    (fun e he => (HD β hβ hβC L hL e (hseg e he)).2.1.differentiableAt)
    (fun e he => by
      have := (HD β hβ hβC L hL e (hseg e he)).2.2
      rw [le_div_iff₀ (by positivity)]; linarith)
    (convex_uIcc E₁ E₂) Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs] at h
  exact h

/-- A vertical move `E₁ → E₁ + iy₀` at variance `γ_g`, from the height derivative of
Lemma 6.4 [da:lem:positive-height]. -/
private lemma vert_move {g K6 : ℝ} (hg1 : 1 ≤ g) {L : ℕ} (hL3 : 3 ≤ L) (i₀ : Fin L) {E₁ y₀ : ℝ}
    (hy₀ : 0 ≤ y₀) (hK6 : 0 ≤ K6)
    (hD : ∀ y : ℝ, 0 < y → y ≤ y₀ →
      DifferentiableAt ℝ (fun r : ℝ => segMat g L E₁ 1 r i₀ i₀) (y / gammaG g) ∧
      ‖deriv (fun r : ℝ => segMat g L E₁ 1 r i₀ i₀) (y / gammaG g)‖ ≤ K6)
    (hr0 : IsDysonRootV 1 (gammaG g) L E₁ (mRootV 1 (gammaG g) L E₁)) :
    ‖mRootV 1 (gammaG g) L ((E₁ : ℂ) + (y₀ : ℂ) * I) - mRootV 1 (gammaG g) L E₁‖ ≤
      K6 / gammaG g * y₀ := by
  have hγ := gG_pos g
  have hb : hopB g = 1 := hB_of_one_le hg1
  rcases hy₀.lt_or_eq with hy₀ | hy₀
  swap
  · subst hy₀; simp
  set F : ℝ → ℂ := fun y => mRootV 1 (gammaG g) L ((E₁ : ℂ) + (y : ℂ) * I) with hF
  set Φ : ℝ → ℂ := fun r => segMat g L E₁ 1 r i₀ i₀ with hΦ
  have hFΦ : ∀ y, 0 < y → Φ (y / gammaG g) = F y := by
    intro y hy
    simp only [hΦ, hF]
    rw [segMat_eq, hb, one_mul]
    have hr := mRootV_root zero_le_one hγ hL3 (z := (E₁ : ℂ) + (y : ℂ) * I)
      (by rw [vert_im]; exact hy)
    have hw : 0 < ((E₁ : ℂ) + (y : ℂ) * I + ((gammaG g : ℝ) : ℂ) *
        mRootV 1 (gammaG g) L ((E₁ : ℂ) + (y : ℂ) * I)).im := by
      rw [root_w_im, vert_im]; have := hr.1; positivity
    rw [dysonMat_diag 1 (gammaG g) L (by omega) _ _ hw]
    exact hr.2.symm
  set Gf : ℝ → ℂ := fun y => Φ (y / gammaG g) with hGf
  have hGd : ∀ y, 0 < y → y ≤ y₀ →
      HasDerivAt Gf ((1 / gammaG g) • deriv Φ (y / gammaG g)) y := by
    intro y hy hyy
    have h1 := (hD y hy hyy).1.hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => y / gammaG g) (1 / gammaG g) y := by
      simpa using (hasDerivAt_id y).div_const (gammaG g)
    exact h1.scomp y h2
  have hmvt : ∀ ε, 0 < ε → ε ≤ y₀ → ‖F y₀ - F ε‖ ≤ K6 / gammaG g * (y₀ - ε) := by
    intro ε hε hεy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Gf) (s := Set.Icc ε y₀)
      (C := K6 / gammaG g)
      (fun y hy => (hGd y (lt_of_lt_of_le hε hy.1) hy.2).differentiableAt)
      (fun y hy => by
        rw [(hGd y (lt_of_lt_of_le hε hy.1) hy.2).deriv, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity), one_div, inv_mul_eq_div]
        exact div_le_div_of_nonneg_right (hD y (lt_of_lt_of_le hε hy.1) hy.2).2 hγ.le)
      (convex_Icc ε y₀) ⟨le_rfl, hεy⟩ ⟨hεy, le_rfl⟩
    simp only [hGf, hFΦ y₀ hy₀, hFΦ ε hε] at h
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h
    exact h
  set K := 2 / (gammaG g ^ 2 * (mRootV 1 (gammaG g) L E₁).im ^ 2) with hK
  have hK0 : 0 < K := by have := hr0.1; positivity
  have hlip : ∀ ε, 0 < ε → ‖mRootV 1 (gammaG g) L E₁ - F ε‖ ≤ K * ε := by
    intro ε hε
    have hr := mRootV_root zero_le_one hγ hL3 (z := (E₁ : ℂ) + (ε : ℂ) * I)
      (by rw [vert_im]; exact hε)
    have := root_lip hγ (by omega) (by simp) (by rw [vert_im]; exact hε.le) hr0 hr
    rwa [norm_real_sub_vert E₁ ε hε.le] at this
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := min y₀ (δ / K) with hε
  have hε0 : 0 < ε := lt_min hy₀ (by positivity)
  have h1 := hmvt ε hε0 (min_le_left _ _)
  have h2 := hlip ε hε0
  have h3 : K * ε ≤ δ := by
    calc K * ε ≤ K * (δ / K) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK0.le
      _ = δ := by field_simp
  have h4 : K6 / gammaG g * (y₀ - ε) ≤ K6 / gammaG g * y₀ := by
    have : 0 ≤ K6 / gammaG g := by positivity
    nlinarith
  calc ‖F y₀ - mRootV 1 (gammaG g) L E₁‖ ≤ ‖F y₀ - F ε‖ + ‖F ε - mRootV 1 (gammaG g) L E₁‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ K6 / gammaG g * y₀ + δ := by rw [norm_sub_rev (F ε)]; linarith

/-- Couplings of one comparison at large coupling: `ξ = 1` and `sγ_{g'} = uγ_g`. -/
private lemma large_step_basic {g s u : ℝ} (hg : 2 ≤ g) (hs : 1 / 2 ≤ s) (hsu : s ≤ u)
    (hu1 : u < 1) :
    g / 2 ≤ gCmp g s u ∧ 1 ≤ gCmp g s u ∧ gCmp g s u ≤ g ∧
      gCmp g s u ^ 2 = g ^ 2 * (s / u) ∧ xiCmp g s u = 1 ∧
      gammaG (gCmp g s u) = u / s * gammaG g ∧ hopB (gCmp g s u) = 1 := by
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := by linarith
  obtain ⟨hg'0, hg'g, hg'2⟩ := gCmp_facts (g := g) (by linarith) hs0 hsu
  have hsu2 : 1 / 2 ≤ s / u := by
    rw [le_div_iff₀ hu0]; nlinarith
  have hg'h : g / 2 ≤ gCmp g s u := by
    have h1 : (g / 2) ^ 2 ≤ gCmp g s u ^ 2 := by
      rw [hg'2]
      have : (g / 2) ^ 2 = g ^ 2 * (1 / 4) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact (pow_le_pow_iff_left₀ (by linarith) hg'0 two_ne_zero).mp h1
  have hg'1 : 1 ≤ gCmp g s u := by linarith
  have hγ' : gammaG (gCmp g s u) = u / s * gammaG g := by
    rw [gG_of_one_le hg'1, gG_of_one_le (by linarith : (1 : ℝ) ≤ g), hg'2]
    field_simp
  obtain ⟨hξ0, -, -, hγξ⟩ := xi_facts (g := g) hs0 hsu
  have hξ1 : xiCmp g s u = 1 := by
    have hpos : 0 < u / s * gammaG g := by have := gG_pos g; positivity
    have h1 : xiCmp g s u ^ 2 = 1 := by
      have := hγξ.symm.trans hγ'
      field_simp at this
      nlinarith [this]
    exact (pow_eq_one_iff_of_nonneg hξ0.le two_ne_zero).mp h1
  exact ⟨hg'h, hg'1, hg'g, hg'2, hξ1, hγ', hB_of_one_le hg'1⟩

/-- The energy estimate (A.60) [bl:eq:large-matching-bounds] from the three moves. -/
private lemma large_energy {γ b' u E E' CA C6 : ℝ} {m μ μ₂ m₁ : ℂ} (hγ : 0 < γ) (hb' : γ ≤ b')
    (hu : 1 / 2 ≤ u) (hu1 : u ≤ 1) (hCA : 0 ≤ CA) (hC6 : 0 ≤ C6)
    (hE' : E' = E + (1 - u) * γ * m.re - (b' - u * γ) * μ.re) (hμ : ‖μ‖ ≤ CA)
    (h1 : ‖μ - μ₂‖ ≤ 1 / (2 * b') * |E' - E|) (h2 : ‖μ₂ - m₁‖ ≤ C6 / γ * ((b' - γ) * CA))
    (h3 : ‖m₁ - m‖ ≤ 1 / (2 * γ) * ((b' - γ) * CA)) :
    |E' - E| ≤ CA * (2 + C6) * (b' - γ) := by
  have hb'0 : 0 < b' := lt_of_lt_of_le hγ hb'
  set D := |E' - E| with hD
  set δ := b' - γ with hδ
  have hδ0 : 0 ≤ δ := by linarith
  have hsplit : E' - E = -(δ * μ.re) - (1 - u) * γ * (μ - m).re := by
    rw [hE', Complex.sub_re, hδ]; ring
  have hdiff : ‖μ - m‖ ≤ 1 / (2 * b') * D + C6 / γ * (δ * CA) + 1 / (2 * γ) * (δ * CA) := by
    calc ‖μ - m‖ = ‖(μ - μ₂) + (μ₂ - m₁) + (m₁ - m)‖ := by ring_nf
      _ ≤ ‖μ - μ₂‖ + ‖μ₂ - m₁‖ + ‖m₁ - m‖ := norm_add₃_le
      _ ≤ _ := by linarith
  have hre : |(μ - m).re| ≤ ‖μ - m‖ := Complex.abs_re_le_norm _
  have hμre : |μ.re| ≤ CA := (Complex.abs_re_le_norm μ).trans hμ
  have hu0 : 0 ≤ (1 - u) * γ := by nlinarith
  have hu2 : (1 - u) * γ ≤ γ / 2 := by nlinarith
  have hD1 : D ≤ δ * CA + γ / 2 * ‖μ - m‖ := by
    rw [hD, hsplit]
    calc |-(δ * μ.re) - (1 - u) * γ * (μ - m).re| ≤ |δ * μ.re| + |(1 - u) * γ * (μ - m).re| :=
          abs_sub _ _ |>.trans (by rw [abs_neg])
      _ = δ * |μ.re| + (1 - u) * γ * |(μ - m).re| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hδ0, abs_of_nonneg hu0]
      _ ≤ δ * CA + γ / 2 * ‖μ - m‖ := by
          gcongr
  have hγb : γ / 2 * (1 / (2 * b') * D) ≤ D / 4 := by
    have hD0 : 0 ≤ D := abs_nonneg _
    have : γ / 2 * (1 / (2 * b')) ≤ 1 / 4 := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  have hγ6 : γ / 2 * (C6 / γ * (δ * CA)) = C6 / 2 * (δ * CA) := by field_simp
  have hγ7 : γ / 2 * (1 / (2 * γ) * (δ * CA)) = 1 / 4 * (δ * CA) := by field_simp; ring
  have hmain : D ≤ δ * CA + D / 4 + C6 / 2 * (δ * CA) + 1 / 4 * (δ * CA) := by
    have := mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ γ / 2)
    rw [mul_add, mul_add, hγ6, hγ7] at this
    linarith
  have hδCA : 0 ≤ δ * CA := mul_nonneg hδ0 hCA
  have : CA * (2 + C6) * δ = δ * CA * 2 + C6 * (δ * CA) := by ring
  rw [this]
  nlinarith

/-- `(γ‖m‖)g ≤ 1` from `γ‖m‖² ≤ 1`, `γ = g⁻²`. -/
private lemma norm_root_le_inv {g γ t : ℝ} (hg : 0 < g) (hγ : γ = (g ^ 2)⁻¹) (ht : 0 ≤ t)
    (h : γ * t ^ 2 ≤ 1) : γ * t ≤ 1 / g := by
  rw [le_div_iff₀ hg]
  have h1 : (γ * t * g) ^ 2 ≤ 1 := by
    have : (γ * t * g) ^ 2 = γ * t ^ 2 * (γ * g ^ 2) := by ring
    rw [this, hγ, inv_mul_cancel₀ (by positivity), mul_one]
    rw [hγ] at h; exact h
  have h0 : 0 ≤ γ * t * g := by rw [hγ]; positivity
  exact (pow_le_one_iff_of_nonneg h0 two_ne_zero).mp h1

/-- Lemma 6.3(a) [da:lem:comparison-parameters], large coupling: `ξ = 1`, the equality
`sγ_{g'} = uγ_g` of (6.10) [fo:eq:large-time-domain], (A.60) [bl:eq:large-matching-bounds]. -/
theorem cmpParams_large (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ R C'' : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ 1 ≤ C'' ∧ ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, R * g ^ 2 ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ s u : ℝ, 1 / 2 ≤ s → s ≤ u → u < 1 →
      let g' := gCmp g s u
      let E' := ECmp g L E m s u
      let w := wCmp g L E m s u
      let m' := mRoot g' L E'
      xiCmp g s u = 1 ∧ s * gammaG g' = u * gammaG g ∧
      IsDysonRootV (hopB g') (gammaG g') L E' m' ∧ C''⁻¹ ≤ m'.im ∧
      |E' - E| ≤ C'' * ((g' ^ 2)⁻¹ - (g ^ 2)⁻¹) ∧ |E'| ≤ 2 - κ / 2 ∧
      w.re = (zChar g E m u).re ∧ etaChar g m u ≤ w.im ∧
      w.im ≤ C'' * ((1 - s) / (1 - u)) * etaChar g m u ∧
      w = zChar g' E' m' s ∧
      dysonMat (hopB g) (u * gammaG g) L w (mRootV (hopB g) (u * gammaG g) L w) =
        dysonMat (hopB g') (gammaG g') L E' m' := by
  obtain ⟨CκA, RA, cA, CA, hCκA, hRA, hcA, hCA, HA⟩ := lpc_var (κ / 2) (by linarith) (by linarith)
  obtain ⟨CκD, RD, hCκD, hRD, HD⟩ := anchor_derivative (κ / 2) (by linarith) (by linarith)
  obtain ⟨Cκ6, R6, c6, C6, hCκ6, hR6, hc6, hC6, H6⟩ := ph_large_core κ (2 * CA) hκ hκ2
    (by positivity)
  set Cκ := max (max 2 (2 * CκA)) (max (2 * CκD) (max Cκ6 (max (6 / κ) (4 * CA / κ)))) with hCκ
  set R := max (max RA RD) (max R6 3) with hR
  set C'' := max (max 1 (2 * CA ^ 2)) (CA * (2 + C6)) with hC''
  refine ⟨Cκ, R, C'', (by norm_num : (1 : ℝ) ≤ 2).trans ((le_max_left _ _).trans (le_max_left _ _)),
    by positivity, (le_max_left _ _).trans (le_max_left _ _), ?_⟩
  intro g hg L hL E hE m hm s u hs hsu hu1 g' E' w m'
  have hg2 : 2 ≤ g := ((le_max_left _ _).trans (le_max_left _ _)).trans hg
  have hgA : 2 * CκA ≤ g := ((le_max_right _ _).trans (le_max_left _ _)).trans hg
  have hgD : 2 * CκD ≤ g := ((le_max_left _ _).trans (le_max_right _ _)).trans hg
  have hg6 : Cκ6 ≤ g :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hg
  have hgκ : 6 / κ ≤ g :=
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans hg
  have hgκA : 4 * CA / κ ≤ g :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans hg
  have hg1 : 1 ≤ g := by linarith
  have hg0 : 0 < g := by linarith
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := by linarith
  have hgsq : 0 < g ^ 2 := by positivity
  have hRA' : RA ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRD' : RD ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hR6' : R6 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR3 : 3 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hL3 : 3 ≤ L := by
    have : (3 : ℝ) ≤ L := by
      have h1 : R * 1 ≤ R * g ^ 2 := by gcongr; exact one_le_pow₀ hg1
      linarith
    exact_mod_cast this
  have hb : hopB g = 1 := hB_of_one_le hg1
  have hγ : gammaG g = (g ^ 2)⁻¹ := gG_of_one_le hg1
  obtain ⟨hg'h, hg'1, hg'g, hg'2, hξ1, hγ', hb'⟩ := large_step_basic hg2 hs hsu hu1
  have H := step_core hg0.le hL3 hm hs0 hsu hu1
  dsimp only at H
  obtain ⟨-, -, hη0, hηge, hηe, hμr, hμβ, hE'e, hroot', hmroot, hw, hwz, hdys⟩ := H
  rw [hξ1] at hE'e hroot' hmroot hwz hdys
  simp only [Complex.ofReal_one, inv_one, one_mul, one_smul] at hE'e hroot' hmroot hwz hdys
  set x := (zChar g E m u).re with hx
  set η := etaTube (hopB g) (u * gammaG g) (u / s * gammaG g) L x with hηdef
  set μ := mRootV (hopB g) (u * gammaG g) L ((x : ℂ) + (η : ℂ) * I) with hμdef
  rw [hb] at hm hμβ
  rw [hb'] at hroot'
  have hγpos : 0 < gammaG g := gG_pos g
  set γ := gammaG g with hγdef
  set b' := u / s * γ with hb'def
  have hb'pos : 0 < b' := by positivity
  have hγb' : γ ≤ b' := by
    have : 1 ≤ u / s := by rw [le_div_iff₀ hs0]; linarith
    calc γ = 1 * γ := (one_mul γ).symm
      _ ≤ u / s * γ := mul_le_mul_of_nonneg_right this hγpos.le
  have hb'2 : b' ≤ 2 * γ := by
    have : u / s ≤ 2 := by rw [div_le_iff₀ hs0]; linarith
    exact mul_le_mul_of_nonneg_right this hγpos.le
  have hb'g' : b' = (g' ^ 2)⁻¹ := by rw [← hγ', gG_of_one_le hg'1]
  rw [hγ'] at hroot'
  -- Lemma A.4 [uvp:prop:finite] at `(g, E)`
  have hγA : γ ≤ (CκA ^ 2)⁻¹ := by
    rw [hγ]; exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  have hLγ : RA / γ ≤ L := by
    rw [hγ, div_inv_eq_mul]; exact le_trans (by gcongr) hL
  obtain ⟨-, -, hmc, hmC, -, -, -⟩ := HA γ hγpos hγA L hLγ E (by linarith)
  have hmeq : mRootV 1 γ L E = m := mRootV_eq zero_le_one hγpos hL3 (by simp) hm
  rw [hmeq] at hmc hmC
  -- the a priori bound on `E'`
  have hn1 := root_norm_sq hγpos.le (by omega) hm (by simp)
  have hn2 := root_norm_sq hb'pos.le (by omega) hμβ (by simp)
  have hγm : γ * ‖m‖ ≤ 1 / g := norm_root_le_inv hg0 hγ (norm_nonneg _) hn1
  have hb'μ : b' * ‖μ‖ ≤ 2 / g := by
    have h1 := norm_root_le_inv (by linarith : 0 < g') hb'g' (norm_nonneg _) hn2
    refine h1.trans ?_
    rw [div_le_div_iff₀ (by linarith) hg0]; linarith
  have hEx : x = E + (1 - u) * γ * m.re := by
    rw [hx, hγdef]; unfold zChar
    rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  have huγ : u * γ ≤ γ := mul_le_of_le_one_left hγpos.le (by linarith)
  have hc0pos : 0 ≤ b' - u * γ := by linarith only [huγ, hγb']
  have hc0le : b' - u * γ ≤ b' := by
    have : 0 ≤ u * γ := by positivity
    linarith only [this]
  have hEE : E' = E + (1 - u) * γ * m.re - (b' - u * γ) * μ.re := by
    change ECmp g L E m s u = _
    rw [hE'e, hEx]
  have hE'b : |E'| ≤ 2 - κ / 2 := by
    have h1 : |(1 - u) * γ * m.re| ≤ 1 / g := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (by linarith) hγpos.le : 0 ≤ (1 - u) * γ)]
      calc (1 - u) * γ * |m.re| ≤ γ * ‖m‖ :=
            mul_le_mul (mul_le_of_le_one_left hγpos.le (by linarith)) (Complex.abs_re_le_norm m)
              (abs_nonneg _) hγpos.le
        _ ≤ 1 / g := hγm
    have h2 : |(b' - u * γ) * μ.re| ≤ 2 / g := by
      rw [abs_mul, abs_of_nonneg hc0pos]
      calc (b' - u * γ) * |μ.re| ≤ b' * ‖μ‖ :=
            mul_le_mul hc0le (Complex.abs_re_le_norm μ) (abs_nonneg _) hb'pos.le
        _ ≤ 2 / g := hb'μ
    have h3 : 3 / g ≤ κ / 2 := by
      rw [div_le_iff₀ hg0]; rw [div_le_iff₀ hκ] at hgκ; linarith
    rw [hEE]
    have h4 := abs_add_le (E + (1 - u) * γ * m.re) (-((b' - u * γ) * μ.re))
    have h5 := abs_add_le E ((1 - u) * γ * m.re)
    rw [abs_neg, ← sub_eq_add_neg] at h4
    have : 1 / g + 2 / g = 3 / g := by ring
    linarith
  -- Lemma A.4 [uvp:prop:finite] at `(g', E')`
  have hb'A : b' ≤ (CκA ^ 2)⁻¹ := by
    rw [hb'g']; exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  have hLb' : RA / b' ≤ L := by
    rw [hb'g', div_inv_eq_mul]
    calc RA * g' ^ 2 ≤ R * g ^ 2 := by gcongr
      _ ≤ (L : ℝ) := hL
  obtain ⟨-, -, hμc, hμC, -, -, -⟩ := HA b' hb'pos hb'A L hLb' E' hE'b
  have hμeq : mRootV 1 b' L E' = μ := mRootV_eq zero_le_one hb'pos hL3 (by simp) hroot'
  rw [hμeq] at hμc hμC
  -- Lemma A.4 [uvp:prop:finite] at `(g', E)`
  obtain ⟨-, hμ₂r, -, hμ₂C, -, -, -⟩ := HA b' hb'pos hb'A L hLb' E (by linarith)
  set μ₂ := mRootV 1 b' L E with hμ₂def
  set δ := b' - γ with hδ
  have hδ0 : 0 ≤ δ := by linarith
  have hδ2 : δ ≤ 2 / g ^ 2 := by
    have : b' ≤ 2 / g ^ 2 := by rw [div_eq_mul_inv, ← hγ]; exact hb'2
    linarith
  set E₁ := E + δ * μ₂.re with hE₁
  set y₀ := δ * μ₂.im with hy₀
  have hy₀0 : 0 ≤ y₀ := mul_nonneg hδ0 hμ₂r.1.le
  have hδCA : δ * CA ≤ 2 * CA / g ^ 2 := by
    calc δ * CA ≤ 2 / g ^ 2 * CA := mul_le_mul_of_nonneg_right hδ2 hCA.le
      _ = 2 * CA / g ^ 2 := by ring
  have hy₀C : y₀ ≤ 2 * CA / g ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left ((Complex.im_le_norm μ₂).trans hμ₂C) hδ0) hδCA
  have hE₁E : |E₁ - E| ≤ δ * CA := by
    rw [hE₁, add_sub_cancel_left, abs_mul, abs_of_nonneg hδ0]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm μ₂).trans hμ₂C) hδ0
  have hE₁b : |E₁| ≤ 2 - κ / 2 := by
    have h1 : 2 * CA / g ^ 2 ≤ κ / 2 := by
      have hgg : g ≤ g ^ 2 := le_self_pow₀ hg1 two_ne_zero
      have h4 : 4 * CA ≤ κ * g := by rw [div_le_iff₀ hκ] at hgκA; linarith only [hgκA]
      have h5 := mul_le_mul_of_nonneg_left hgg hκ.le
      rw [div_le_iff₀ hgsq]
      linarith only [h4, h5]
    have := abs_sub_abs_le_abs_sub E₁ E
    linarith
  -- `μ₂` at variance `γ_g` and height `y₀`
  have hμ₂γ : IsDysonRootV 1 γ L ((E₁ : ℂ) + (y₀ : ℂ) * I) μ₂ := by
    refine root_shift hμ₂r ?_
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, mul_one, hE₁, hδ]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, mul_one, zero_add, hy₀, hδ]
      ring
  have hμ₂eq : mRootV 1 γ L ((E₁ : ℂ) + (y₀ : ℂ) * I) = μ₂ :=
    mRootV_eq zero_le_one hγpos hL3 (by rw [vert_im]; exact hy₀0) hμ₂γ
  -- the anchor derivative
  have hγD : CκD ≤ γ ^ (-(1 : ℝ) / 2) := by rw [hγ, rpow_inv_sq hg0]; linarith
  have hb'D : CκD ≤ b' ^ (-(1 : ℝ) / 2) := by rw [hb'g', rpow_inv_sq (by linarith)]; linarith
  have hLDγ : RD / γ ≤ L := by
    rw [hγ, div_inv_eq_mul]; exact le_trans (by gcongr) hL
  have hLDb' : RD / b' ≤ L := by
    rw [hb'g', div_inv_eq_mul]
    calc RD * g' ^ 2 ≤ R * g ^ 2 := by gcongr
      _ ≤ (L : ℝ) := hL
  have hm₁ := (HD γ hγpos hγD L hLDγ E₁ hE₁b).1
  have hmv1 : ‖μ - μ₂‖ ≤ 1 / (2 * b') * |E' - E| := by
    have := horiz_move HD hb'pos hb'D hLDb' (by linarith : |E| ≤ 2 - κ / 2) hE'b
    rw [hμeq] at this; exact this
  have hmv3 : ‖mRootV 1 γ L E₁ - m‖ ≤ 1 / (2 * γ) * (δ * CA) := by
    have := horiz_move HD hγpos hγD hLDγ (by linarith : |E| ≤ 2 - κ / 2) hE₁b
    rw [hmeq] at this
    exact this.trans (mul_le_mul_of_nonneg_left hE₁E (by positivity))
  -- the vertical move
  have i₀ : Fin L := ⟨0, by omega⟩
  have hL6 : R6 * g ^ 2 ≤ L := le_trans (by gcongr) hL
  have hmv2 : ‖μ₂ - mRootV 1 γ L E₁‖ ≤ C6 / γ * (δ * CA) := by
    have hD : ∀ y : ℝ, 0 < y → y ≤ y₀ →
        DifferentiableAt ℝ (fun r : ℝ => segMat g L E₁ 1 r i₀ i₀) (y / gammaG g) ∧
        ‖deriv (fun r : ℝ => segMat g L E₁ 1 r i₀ i₀) (y / gammaG g)‖ ≤ C6 := by
      intro y hy hyy
      obtain ⟨-, -, -, -, -, -, hd, hdb, -⟩ :=
        H6 g hg6 L hL6 E₁ y 1 hE₁b hy (hyy.trans hy₀C) (by norm_num) le_rfl
      exact ⟨hd i₀ i₀, hdb i₀ i₀⟩
    have h1 := vert_move hg1 hL3 i₀ hy₀0 hC6.le hD hm₁
    rw [← hγdef, hμ₂eq] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact mul_le_mul_of_nonneg_left ((Complex.im_le_norm μ₂).trans hμ₂C) hδ0
  have hEn := large_energy (u := u) hγpos hγb' (hs.trans hsu) hu1.le hCA.le hC6.le hEE hμC hmv1
    hmv2 hmv3
  have hm'eq : m' = μ := hmroot
  have hC''CA : CA ≤ C'' := by
    have : CA ≤ CA * (2 + C6) := le_mul_of_one_le_right hCA.le (by linarith)
    exact this.trans (le_max_right _ _)
  refine ⟨hξ1, ?_, ?_, ?_, ?_, hE'b, ?_, ?_, ?_, ?_, ?_⟩
  · change s * gammaG (gCmp g s u) = u * γ
    rw [hγ', hb'def]; field_simp
  · rw [hm'eq, hb', hγ']; exact hroot'
  · rw [hm'eq]; refine le_trans ?_ hμc
    exact inv_anti₀ hCA hC''CA
  · rw [← hb'g', ← hγ]
    refine hEn.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ0)
  · rw [show w = (x : ℂ) + (η : ℂ) * I from hw, vert_re]
  · rw [show w = (x : ℂ) + (η : ℂ) * I from hw, vert_im]; exact hηge
  · rw [show w = (x : ℂ) + (η : ℂ) * I from hw, vert_im]
    have h1u : 0 < 1 - u := by linarith
    have hc0' : b' - u * γ ≤ 2 * γ * (1 - s) := by
      have : b' - u * γ = u * γ * (1 - s) / s := by rw [hb'def]; field_simp
      rw [this, div_le_iff₀ hs0]
      have h1s : 0 ≤ γ * (1 - s) := mul_nonneg hγpos.le (by linarith)
      calc u * γ * (1 - s) = u * (γ * (1 - s)) := by ring
        _ ≤ (2 * s) * (γ * (1 - s)) := mul_le_mul_of_nonneg_right (by linarith) h1s
        _ = 2 * γ * (1 - s) * s := by ring
    have hη0' : etaChar g m u = (1 - u) * γ * m.im := rfl
    rw [hη0', hηe]
    have e1 : C'' * ((1 - s) / (1 - u)) * ((1 - u) * γ * m.im) = C'' * (1 - s) * γ * m.im := by
      field_simp
    rw [e1]
    have hμim : μ.im ≤ CA := (Complex.im_le_norm μ).trans hμC
    have h1s : 0 ≤ 1 - s := by linarith
    have hC2 : 2 * CA ^ 2 ≤ C'' := (le_max_right _ _).trans (le_max_left _ _)
    have hmCA : 1 ≤ CA * m.im := by
      have := mul_le_mul_of_nonneg_left hmc hCA.le
      rwa [mul_inv_cancel₀ hCA.ne'] at this
    have hμ0 : 0 < μ.im := hμr.1
    have hm0 : 0 ≤ m.im := hm.1.le
    have hγs : 0 ≤ γ * (1 - s) := mul_nonneg hγpos.le h1s
    calc (b' - u * γ) * μ.im ≤ 2 * γ * (1 - s) * CA :=
          mul_le_mul hc0' hμim hμ0.le (by positivity)
      _ = γ * (1 - s) * (2 * CA) := by ring
      _ ≤ γ * (1 - s) * (2 * CA * (CA * m.im)) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hmCA) hγs
      _ = γ * (1 - s) * (2 * CA ^ 2) * m.im := by ring
      _ ≤ γ * (1 - s) * C'' * m.im :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC2 hγs) hm0
      _ = C'' * (1 - s) * γ * m.im := by ring
  · rw [hm'eq]; exact hwz
  · rw [hm'eq, hb', hγ']; rw [hb', hγ'] at hdys; exact hdys

private lemma regBdd_mono {C B B' c c'' : ℝ} {L : ℕ} {g E : ℝ} (h : RegBdd C B c L g E)
    (hB : B ≤ B') (hc : c'' ≤ c) : RegBdd C B' c'' L g E :=
  ⟨h.1, h.2.1, h.2.2.1.trans hB, h.2.2.2.1, hc.trans h.2.2.2.2⟩

private lemma gCmp_ge_half {g s u : ℝ} (hg : 0 ≤ g) (hs : 1 / 2 ≤ s) (hsu : s ≤ u) (hu1 : u < 1) :
    g / 2 ≤ gCmp g s u := by
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := by linarith
  obtain ⟨hg'0, -, hg'2⟩ := gCmp_facts hg hs0 hsu
  have hsu2 : 1 / 4 ≤ s / u := by rw [le_div_iff₀ hu0]; nlinarith
  have h1 : (g / 2) ^ 2 ≤ gCmp g s u ^ 2 := by
    rw [hg'2]
    have : (g / 2) ^ 2 = g ^ 2 * (1 / 4) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hsu2 (by positivity)
  exact (pow_le_pow_iff_left₀ (by linarith) hg'0 two_ne_zero).mp h1

private lemma cmpChain_cons (L : ℕ) (p su : ℝ × ℝ) (l : List (ℝ × ℝ)) :
    cmpChain L p (su :: l) = cmpChain L (cmpStep L p su) l := rfl

/-- Lemma 6.3(b) [da:lem:comparison-parameters], bounded coupling: chains of at most `J`
comparisons stay in a regular domain. -/
theorem cmpChain_bdd (C B₀ c' : ℝ) (J : ℕ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') :
    ∃ BJ cJ : ℝ, ∃ L₀ : ℕ, 0 < cJ ∧ ∀ g₀ : ℝ, ∀ L : ℕ, 3 ≤ L → L₀ ≤ L → ∀ E₀ : ℝ,
      RegBdd C B₀ c' L g₀ E₀ → ∀ steps : List (ℝ × ℝ), steps.length ≤ J →
      (∀ p ∈ steps, 1 / 2 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 < 1) →
      cJ * g₀ ≤ (cmpChain L (g₀, E₀) steps).1 ∧
        RegBdd C BJ cJ L (cmpChain L (g₀, E₀) steps).1 (cmpChain L (g₀, E₀) steps).2 := by
  induction J generalizing B₀ c' with
  | zero =>
    refine ⟨B₀, min c' 1, 0, lt_min hc' one_pos, ?_⟩
    intro g₀ L _ _ E₀ hreg steps hlen _
    have hnil : steps = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    exact ⟨mul_le_of_le_one_left hreg.1 (min_le_right _ _),
      regBdd_mono hreg le_rfl (min_le_left _ _)⟩
  | succ J ih =>
    obtain ⟨C'', L₁, hC''1, H1⟩ := cmpParams_bdd C B₀ c' hC hB₀ hc'
    obtain ⟨BJ, cJ, L₂, hcJ, H2⟩ := ih C'' C''⁻¹ (by linarith) (inv_pos.mpr (by linarith))
    refine ⟨max B₀ BJ, min (min c' 1) (cJ / 2), max L₁ L₂,
      lt_min (lt_min hc' one_pos) (by positivity), ?_⟩
    intro g₀ L hL3 hL E₀ hreg steps hlen hadm
    cases steps with
    | nil =>
      exact ⟨mul_le_of_le_one_left hreg.1 ((min_le_left _ _).trans (min_le_right _ _)),
        regBdd_mono hreg (le_max_left _ _) ((min_le_left _ _).trans (min_le_left _ _))⟩
    | cons p rest =>
      obtain ⟨hs, hsu, hu1⟩ := hadm p List.mem_cons_self
      obtain ⟨hg0, hgC, hE, hroot, hcm⟩ := hreg
      have h1 := H1 g₀ hg0 hgC L hL3 (le_trans (le_max_left _ _) hL) E₀ hE (mRoot g₀ L E₀) hroot
        hcm p.1 p.2 hs hsu hu1
      obtain ⟨hreg1, -⟩ := h1
      have hreg1' : RegBdd C C'' C''⁻¹ L (cmpStep L (g₀, E₀) p).1 (cmpStep L (g₀, E₀) p).2 :=
        hreg1
      obtain ⟨h2a, h2b⟩ := H2 (cmpStep L (g₀, E₀) p).1 L hL3 (le_trans (le_max_right _ _) hL)
        (cmpStep L (g₀, E₀) p).2 hreg1' rest (by simp at hlen; omega)
        (fun q hq => hadm q (List.mem_cons_of_mem _ hq))
      rw [cmpChain_cons]
      have hhalf : g₀ / 2 ≤ (cmpStep L (g₀, E₀) p).1 := gCmp_ge_half hg0 hs hsu hu1
      refine ⟨?_, regBdd_mono h2b (le_max_right _ _) (min_le_right _ _ |>.trans (by linarith))⟩
      calc min (min c' 1) (cJ / 2) * g₀ ≤ cJ / 2 * g₀ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hg0
        _ = cJ * (g₀ / 2) := by ring
        _ ≤ cJ * (cmpStep L (g₀, E₀) p).1 := mul_le_mul_of_nonneg_left hhalf hcJ.le
        _ ≤ _ := h2a

/-- The two conclusions of `cmpParams_large` used along a chain. -/
private def StepProp (κ Cκ R C₂ : ℝ) : Prop :=
  ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, R * g ^ 2 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ,
    IsDysonRootV (hopB g) (gammaG g) L E m → ∀ s u : ℝ, 1 / 2 ≤ s → s ≤ u → u < 1 →
    s * gammaG (gCmp g s u) = u * gammaG g ∧
      |ECmp g L E m s u - E| ≤ C₂ * ((gCmp g s u ^ 2)⁻¹ - (g ^ 2)⁻¹)

private lemma stepProp_of (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ R C₂ : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ 1 ≤ C₂ ∧ StepProp κ Cκ R C₂ := by
  obtain ⟨Cκ, R, C₂, hCκ, hR, hC₂, H⟩ := cmpParams_large κ hκ hκ2
  refine ⟨Cκ, R, C₂, hCκ, hR, hC₂, fun g hg L hL E hE m hm s u hs hsu hu1 => ?_⟩
  obtain ⟨-, h2, -, -, h5, -⟩ := H g hg L hL E hE m hm s u hs hsu hu1
  exact ⟨h2, h5⟩

/-- The invariant along a nested chain at large coupling. -/
private def ChainInv (g₀ E₀ C₂ g E σ : ℝ) : Prop :=
  1 / 2 ≤ σ ∧ σ ≤ 1 ∧ 0 < g ∧ g ≤ g₀ ∧ σ * (g ^ 2)⁻¹ ≤ (g₀ ^ 2)⁻¹ ∧
    |E - E₀| ≤ C₂ * ((g ^ 2)⁻¹ - (g₀ ^ 2)⁻¹)

private lemma chainInv_facts {κ g₀ E₀ C₂ g E σ : ℝ} (h : ChainInv g₀ E₀ C₂ g E σ)
    (hg₀ : 4 ≤ g₀) (hgκ : 8 * C₂ / κ ≤ g₀) (hκ : 0 < κ) (hC₂ : 0 ≤ C₂)
    (hE₀ : |E₀| ≤ 2 - 3 * κ / 4) :
    g₀ ^ 2 ≤ 2 * g ^ 2 ∧ g₀ / 2 ≤ g ∧ 2 ≤ g ∧ (g ^ 2)⁻¹ ≤ 2 * (g₀ ^ 2)⁻¹ ∧ |E| ≤ 2 - κ / 2 := by
  obtain ⟨hσ, hσ1, hg0, hgg, hσg, hE⟩ := h
  have hg₀0 : 0 < g₀ := by linarith
  have h1 : g₀ ^ 2 ≤ 2 * g ^ 2 := by
    have h2 : σ * (g ^ 2)⁻¹ * (g ^ 2 * g₀ ^ 2) ≤ (g₀ ^ 2)⁻¹ * (g ^ 2 * g₀ ^ 2) :=
      mul_le_mul_of_nonneg_right hσg (by positivity)
    have e1 : σ * (g ^ 2)⁻¹ * (g ^ 2 * g₀ ^ 2) = σ * g₀ ^ 2 := by field_simp
    have e2 : (g₀ ^ 2)⁻¹ * (g ^ 2 * g₀ ^ 2) = g ^ 2 := by field_simp
    rw [e1, e2] at h2
    have h3 : (1 / 2) * g₀ ^ 2 ≤ σ * g₀ ^ 2 := mul_le_mul_of_nonneg_right hσ (by positivity)
    linarith
  have h4 : g₀ / 2 ≤ g := by
    have h5 : (g₀ / 2) ^ 2 ≤ g ^ 2 := by
      have : (g₀ / 2) ^ 2 = g₀ ^ 2 / 4 := by ring
      rw [this]; nlinarith
    exact (pow_le_pow_iff_left₀ (by linarith) hg0.le two_ne_zero).mp h5
  have h6 : (g ^ 2)⁻¹ ≤ 2 * (g₀ ^ 2)⁻¹ := by
    rw [inv_le_comm₀ (by positivity) (by positivity), mul_inv, inv_inv]
    have : 2⁻¹ * g₀ ^ 2 = g₀ ^ 2 / 2 := by ring
    rw [this]; linarith
  refine ⟨h1, h4, by linarith, h6, ?_⟩
  have h7 : C₂ * (g ^ 2)⁻¹ ≤ κ / 4 := by
    have h8 : C₂ * (g ^ 2)⁻¹ ≤ C₂ * (2 * (g₀ ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h6 hC₂
    have h9 : C₂ * (2 * (g₀ ^ 2)⁻¹) ≤ κ / 4 := by
      rw [← mul_assoc, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      have h10 : 8 * C₂ ≤ κ * g₀ := by rw [div_le_iff₀ hκ] at hgκ; linarith
      have h11 : g₀ ≤ g₀ ^ 2 := le_self_pow₀ (by linarith) two_ne_zero
      nlinarith
    linarith
  have h12 : C₂ * ((g ^ 2)⁻¹ - (g₀ ^ 2)⁻¹) ≤ C₂ * (g ^ 2)⁻¹ := by
    have : 0 ≤ (g₀ ^ 2)⁻¹ := by positivity
    nlinarith
  have := abs_sub_abs_le_abs_sub E E₀
  linarith


/-- The induction along a nested chain at large coupling. -/
private lemma chain_large_aux {κ Cκ₂ R₂ C₂ CκA RA cA CA g₀ E₀ : ℝ}
    (H2 : StepProp (κ / 2) Cκ₂ R₂ C₂) (HA : LpcProp (κ / 2) CκA RA cA CA) (hκ : 0 < κ)
    (hC₂ : 0 ≤ C₂) (hR₂ : 0 ≤ R₂) (hRA : 0 ≤ RA) (hCκA : 1 ≤ CκA) (hg₀ : 4 ≤ g₀)
    (hgκ : 8 * C₂ / κ ≤ g₀) (hg₂ : 2 * Cκ₂ ≤ g₀) (hgA : 2 * CκA ≤ g₀)
    (hE₀ : |E₀| ≤ 2 - 3 * κ / 4) {L : ℕ} (hL₂ : R₂ * g₀ ^ 2 ≤ L) (hLA : RA * g₀ ^ 2 ≤ L) :
    ∀ l : List (ℝ × ℝ), ∀ g E σ : ℝ, ChainInv g₀ E₀ C₂ g E σ →
      (∀ p ∈ l, 1 / 2 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 < 1) → (∀ p ∈ l.head?, p.2 ≤ σ) →
      l.IsChain (fun p q => q.2 ≤ p.1) →
      (∀ k (hk : k < l.length),
        (l[k]'hk).2 * gammaG (cmpChain L (g, E) (l.take k)).1 ≤ (g₀ ^ 2)⁻¹ ∧
        (l[k]'hk).1 * gammaG (cmpChain L (g, E) (l.take (k + 1))).1 =
          (l[k]'hk).2 * gammaG (cmpChain L (g, E) (l.take k)).1) ∧
      (∀ p ∈ l.getLast?, p.1 * gammaG (cmpChain L (g, E) l).1 ≤ (g₀ ^ 2)⁻¹) ∧
      ∃ σ', ChainInv g₀ E₀ C₂ (cmpChain L (g, E) l).1 (cmpChain L (g, E) l).2 σ' := by
  intro l
  induction l with
  | nil =>
    intro g E σ hinv _ _ _
    exact ⟨fun k hk => absurd hk (by simp), fun p hp => by simp at hp, σ, hinv⟩
  | cons p rest ih =>
    intro g E σ hinv hadm hhead hchain
    obtain ⟨hs, hsu, hu1⟩ := hadm p List.mem_cons_self
    have hup : p.2 ≤ σ := hhead p (by simp)
    obtain ⟨-, hg2', hg2, -, hEb⟩ := chainInv_facts hinv hg₀ hgκ hκ hC₂ hE₀
    obtain ⟨hσ, hσ1, hg0, hgg, hσg, hEE⟩ := hinv
    have hg1 : 1 ≤ g := by linarith
    have hγ : gammaG g = (g ^ 2)⁻¹ := gG_of_one_le hg1
    have hb : hopB g = 1 := hB_of_one_le hg1
    have hβ : 0 < (g ^ 2)⁻¹ := by positivity
    have hβA : (g ^ 2)⁻¹ ≤ (CκA ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
    have hgsq : g ^ 2 ≤ g₀ ^ 2 := pow_le_pow_left₀ hg0.le hgg 2
    have hLA' : RA / (g ^ 2)⁻¹ ≤ L := by
      rw [div_inv_eq_mul]; exact le_trans (mul_le_mul_of_nonneg_left hgsq hRA) hLA
    obtain ⟨-, hroot, -⟩ := HA (g ^ 2)⁻¹ hβ hβA L hLA' E hEb
    have hmroot : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E) := by
      unfold mRoot; rw [hb, hγ]; exact hroot
    obtain ⟨hγeq, hEn⟩ := H2 g (by linarith) L (le_trans (mul_le_mul_of_nonneg_left hgsq hR₂) hL₂)
      E hEb (mRoot g L E) hmroot p.1 p.2 hs hsu hu1
    set q := cmpStep L (g, E) p with hq
    have hq1 : q.1 = gCmp g p.1 p.2 := rfl
    have hq2 : q.2 = ECmp g L E (mRoot g L E) p.1 p.2 := rfl
    have hgq : g / 2 ≤ q.1 := gCmp_ge_half hg0.le hs hsu hu1
    have hq1g : q.1 ≤ g := (gCmp_facts hg0.le (by linarith) hsu).2.1
    have hq11 : 1 ≤ q.1 := by linarith
    have hγq : gammaG q.1 = (q.1 ^ 2)⁻¹ := gG_of_one_le hq11
    rw [← hq1, ← hq2] at hEn
    rw [← hq1] at hγeq
    have hstep : p.1 * gammaG q.1 = p.2 * gammaG g := hγeq
    have hlead : p.2 * gammaG g ≤ (g₀ ^ 2)⁻¹ := by
      rw [hγ]; exact le_trans (mul_le_mul_of_nonneg_right hup hβ.le) hσg
    have hinv' : ChainInv g₀ E₀ C₂ q.1 q.2 p.1 := by
      refine ⟨hs, by linarith, by linarith, hq1g.trans hgg, ?_, ?_⟩
      · rw [← hγq, hstep]; exact hlead
      · have := abs_sub_le q.2 E E₀
        linarith
    obtain ⟨hhd, hch⟩ := List.isChain_cons.mp hchain
    obtain ⟨hk', hlast', σ', hinv''⟩ := ih q.1 q.2 p.1 hinv'
      (fun r hr => hadm r (List.mem_cons_of_mem _ hr)) hhd hch
    refine ⟨fun k hk => ?_, fun p' hp' => ?_, σ', hinv''⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, List.take_zero, List.take_succ_cons]
        exact ⟨hlead, hstep⟩
      | succ k =>
        simp only [List.getElem_cons_succ, List.take_succ_cons, cmpChain_cons]
        exact hk' k (by simpa using hk)
    · cases rest with
      | nil =>
        simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hp'
        subst hp'
        rw [cmpChain_cons]
        change p.1 * gammaG q.1 ≤ (g₀ ^ 2)⁻¹
        rw [hstep]; exact hlead
      | cons r rest' =>
        rw [List.getLast?_cons_cons] at hp'
        rw [cmpChain_cons]
        exact hlast' p' hp'

/-- Lemma 6.3(b) [da:lem:comparison-parameters], large coupling: (6.10)
[fo:eq:large-time-domain] at every comparison of a nested chain of at most `J` comparisons
(the `k`-th comparison `(s_k, u_k)` acts at coupling `g_k`: `u_kγ_{g_k} ≤ g₀⁻²` and
`s_kγ_{g_{k+1}} = u_kγ_{g_k}`), the bound `sγ_g ≤ g₀⁻²` at the last comparison time `s`, and
(6.11) [fo:eq:large-input-domain]. -/
theorem cmpChain_large (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (J : ℕ) :
    ∃ Cκ R C'' : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ 1 ≤ C'' ∧ ∀ g₀ : ℝ, Cκ ≤ g₀ → ∀ L : ℕ, R * g₀ ^ 2 ≤ L →
      ∀ E₀ : ℝ, |E₀| ≤ 2 - 3 * κ / 4 → ∀ steps : List (ℝ × ℝ), steps.length ≤ J →
      (∀ p ∈ steps, 1 / 2 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 < 1) →
      steps.IsChain (fun p q => q.2 ≤ p.1) →
      let q := cmpChain L (g₀, E₀) steps
      (∀ k (hk : k < steps.length),
        (steps[k]'hk).2 * gammaG (cmpChain L (g₀, E₀) (steps.take k)).1 ≤ (g₀ ^ 2)⁻¹ ∧
        (steps[k]'hk).1 * gammaG (cmpChain L (g₀, E₀) (steps.take (k + 1))).1 =
          (steps[k]'hk).2 * gammaG (cmpChain L (g₀, E₀) (steps.take k)).1) ∧
      (∀ p ∈ steps.getLast?, p.1 * gammaG q.1 ≤ (g₀ ^ 2)⁻¹) ∧
      g₀ / Real.sqrt 2 ≤ q.1 ∧ q.1 ≤ g₀ ∧ |q.2| ≤ 2 - κ / 2 ∧
      IsDysonRootV (hopB q.1) (gammaG q.1) L q.2 (mRoot q.1 L q.2) ∧
      C''⁻¹ ≤ (mRoot q.1 L q.2).im := by
  obtain ⟨Cκ₂, R₂, C₂, hCκ₂, hR₂, hC₂, H2⟩ := stepProp_of (κ / 2) (by linarith) (by linarith)
  obtain ⟨CκA, RA, cA, CA, hCκA, hRA, hcA, hCA, HA⟩ := lpc_var (κ / 2) (by linarith) (by linarith)
  refine ⟨max (max (2 * Cκ₂) (2 * CκA)) (max (8 * C₂ / κ) 4), max R₂ RA, max C₂ CA,
    le_trans (by norm_num) (le_max_right _ _ |>.trans (le_max_right _ _)),
    lt_of_lt_of_le hR₂ (le_max_left _ _), le_trans hC₂ (le_max_left _ _), ?_⟩
  intro g₀ hg₀ L hL E₀ hE₀ steps _ hadm hchain q
  have hg₂ : 2 * Cκ₂ ≤ g₀ := ((le_max_left _ _).trans (le_max_left _ _)).trans hg₀
  have hgA : 2 * CκA ≤ g₀ := ((le_max_right _ _).trans (le_max_left _ _)).trans hg₀
  have hgκ : 8 * C₂ / κ ≤ g₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hg₀
  have hg4 : 4 ≤ g₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans hg₀
  have hg₀0 : 0 < g₀ := by linarith
  have hL₂ : R₂ * g₀ ^ 2 ≤ L :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hL
  have hLA : RA * g₀ ^ 2 ≤ L :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) hL
  have hinv0 : ChainInv g₀ E₀ C₂ g₀ E₀ 1 :=
    ⟨by norm_num, le_rfl, hg₀0, le_rfl, by rw [one_mul], by simp⟩
  obtain ⟨hk, hlast, σ', hinv⟩ := chain_large_aux H2 HA hκ (by linarith) hR₂.le hRA.le hCκA hg4
    hgκ hg₂ hgA hE₀ hL₂ hLA steps g₀ E₀ 1 hinv0 hadm
    (fun p hp => (hadm p (List.mem_of_mem_head? hp)).2.2.le) hchain
  obtain ⟨hgg₀2, hg2', hg2, -, hEb⟩ := chainInv_facts hinv hg4 hgκ hκ (by linarith) hE₀
  have hq0 : 0 < q.1 := hinv.2.2.1
  have hq1 : 1 ≤ q.1 := by linarith
  have hγ : gammaG q.1 = (q.1 ^ 2)⁻¹ := gG_of_one_le hq1
  have hb : hopB q.1 = 1 := hB_of_one_le hq1
  have hβ : 0 < (q.1 ^ 2)⁻¹ := by positivity
  have hβA : (q.1 ^ 2)⁻¹ ≤ (CκA ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  have hgsq : q.1 ^ 2 ≤ g₀ ^ 2 := pow_le_pow_left₀ hq0.le hinv.2.2.2.1 2
  have hLA' : RA / (q.1 ^ 2)⁻¹ ≤ L := by
    rw [div_inv_eq_mul]; exact le_trans (mul_le_mul_of_nonneg_left hgsq hRA.le) hLA
  obtain ⟨-, hroot, hc, -⟩ := HA (q.1 ^ 2)⁻¹ hβ hβA L hLA' q.2 hEb
  have hmeq : mRoot q.1 L q.2 = mRootV 1 (q.1 ^ 2)⁻¹ L q.2 := by unfold mRoot; rw [hb, hγ]
  refine ⟨hk, hlast, ?_, hinv.2.2.2.1, hEb, ?_, ?_⟩
  · have hs2 : 0 < Real.sqrt 2 := by positivity
    rw [div_le_iff₀ hs2]
    have h1 : (g₀) ^ 2 ≤ (q.1 * Real.sqrt 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; linarith
    exact (pow_le_pow_iff_left₀ hg₀0.le (by positivity) two_ne_zero).mp h1
  · rw [hmeq, hb, hγ]; exact hroot
  · rw [hmeq]; exact le_trans (inv_anti₀ hCA (le_max_right _ _)) hc

/-- The three bounds of Lemma 6.1 [da:lem:scales-propagators] used on the segments. -/
private def SBProp (C B₀ c' C' : ℝ) (L₀ : ℕ) : Prop :=
  ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L → ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ,
    IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
    (∀ a b, ‖dysonMat (hopB g) (gammaG g) L E m a b‖ ≤ C') ∧
    (∀ a, gammaG g * ∑ b, (‖dysonMat (hopB g) (gammaG g) L E m a b‖ +
      ‖dysonMat (hopB g) (gammaG g) L E m a b‖ ^ 2) ≤ C') ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ a, ∑ b,
      ‖(1 - (t : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ a b‖ ≤ C'

private lemma sbProp_of (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') :
    ∃ C' : ℝ, ∃ L₀ : ℕ, 0 < C' ∧ SBProp C B₀ c' C' L₀ := by
  obtain ⟨c, C', L₀, hc, hC', H⟩ := scalesProp_bdd C B₀ c' hC hB₀ hc'
  refine ⟨C', L₀, hC', fun g hg hgC L hL hL₀ E hE m hm hcm => ?_⟩
  obtain ⟨-, h1, h2, h3, -⟩ := H g hg hgC L hL hL₀ E hE m hm hcm
  exact ⟨h1, h2, h3⟩

private lemma le_one_add_sq (t : ℝ) : t ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (t - 1 / 2)]

/-- Lemma 6.4 [da:lem:positive-height] at bounded coupling at one point `x + iy` with
`Im m(x + iy; uγ_g) ≥ ρ_m`. -/
private lemma bdd_point {a₀ X ρm C₀' : ℝ} {L₀ : ℕ}
    (HS : SBProp (1 + 1 / a₀) ((1 + 1 / a₀) * (X + 1 / (a₀ * ρm) / ρm)) (ρm / (1 + 1 / a₀))
      C₀' L₀)
    (ha₀ : 0 < a₀) (hρm : 0 < ρm) {g : ℝ} (hg : 0 ≤ g) {L : ℕ} (hL3 : 3 ≤ L)
    (hL₀ : L₀ ≤ L) {x u y : ℝ} (ha₀a : a₀ ≤ u * gammaG g)
    (hX : |x| ≤ X) (hy : 0 < y) (hy1 : y ≤ 1)
    (hρ : ρm ≤ (mRootV (hopB g) (u * gammaG g) L ((x : ℂ) + (y : ℂ) * I)).im) :
    let Λ₁ := 1 + 1 / a₀
    let KR := (Λ₁ + Λ₁ ^ 2) * C₀' * Λ₁ ^ 2
    let z : ℂ := (x : ℂ) + (y : ℂ) * I
    let mu := mRootV (hopB g) (u * gammaG g) L z
    let M := segMat g L x u (y / gammaG g)
    IsDysonRootV (hopB g) (u * gammaG g) L z mu ∧ mu.im ≤ 1 / (a₀ * ρm) ∧
      (∀ a b, ‖M a b‖ ≤ Λ₁ * C₀') ∧ (∀ a, gammaG g * ∑ b, (‖M a b‖ + ‖M a b‖ ^ 2) ≤ KR) ∧
      (∀ a, ∑ b, ‖(1 - pairQ (u * gammaG g) M)⁻¹ a b‖ ≤ C₀') ∧
      (∀ a b, DifferentiableAt ℝ (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)) ∧
      (∀ a b, ‖deriv (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)‖ ≤
        C₀' * (Λ₁ * C₀') * KR) ∧
      ∀ a, gammaG g * ∑ b, ‖deriv (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)‖ ≤
        C₀' * KR ^ 2 := by
  intro Λ₁ KR z mu M
  have hΛ : 1 ≤ Λ₁ := by have : 0 < 1 / a₀ := by positivity
                         simp only [Λ₁]; linarith
  set b := hopB g with hbdef
  set γ := gammaG g with hγdef
  set a := u * γ with hadef
  have hb0 : 0 ≤ b := hB_nonneg hg
  have hb1 : b ≤ 1 := hB_le_one g
  have hγ0 : 0 < γ := gG_pos g
  have hγ1 : γ ≤ 1 := gG_le_one g
  have ha : 0 < a := lt_of_lt_of_le ha₀ ha₀a
  obtain ⟨hr, haβ, hrβ, hMeq⟩ := vert_rep hb0 ha hL3 x y hy
  set μ := mRootV b a L ((x : ℂ) + (y : ℂ) * I) with hμ
  set β := a + y / μ.im with hβdef
  set e := x - y / μ.im * μ.re with hedef
  have hμ0 : 0 < μ.im := hr.1
  have hβ0 : 0 < β := by linarith
  -- bounds on the root
  have hn2 := root_norm_sq ha.le (by omega) hr (by rw [vert_im]; exact hy.le)
  have hμρ : μ.im ≤ ‖μ‖ := Complex.im_le_norm μ
  have hμK : ‖μ‖ ≤ 1 / (a₀ * ρm) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : a₀ * ρm * ‖μ‖ ≤ a * ‖μ‖ * ‖μ‖ :=
      mul_le_mul (mul_le_mul ha₀a (hρ.trans hμρ) hρm.le ha.le) le_rfl (norm_nonneg _)
        (by positivity)
    have h2 : a * ‖μ‖ * ‖μ‖ = a * ‖μ‖ ^ 2 := by ring
    linarith
  have hyρ : y / μ.im ≤ 1 / ρm := by
    rw [div_le_div_iff₀ hμ0 hρm]
    calc y * ρm ≤ 1 * ρm := mul_le_mul_of_nonneg_right hy1 hρm.le
      _ ≤ 1 * μ.im := by rw [one_mul, one_mul]; exact hρ
  have he : |e| ≤ X + 1 / (a₀ * ρm) / ρm := by
    have h1 : |e - x| ≤ 1 / ρm * (1 / (a₀ * ρm)) := by
      rw [hedef, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < y / μ.im)]
      exact mul_le_mul hyρ ((Complex.abs_re_le_norm μ).trans hμK) (abs_nonneg _) (by positivity)
    have h2 := abs_sub_abs_le_abs_sub e x
    have h3 : 1 / ρm * (1 / (a₀ * ρm)) = 1 / (a₀ * ρm) / ρm := by ring
    linarith
  -- the model scaling
  obtain ⟨G, lam, hG0, hlam, hlb, hlβ, hGβ, hlM⟩ := model_scale hb0 hβ0
  have hβa₀ : a₀ ≤ β := ha₀a.trans haβ.le
  have hG2 : G ^ 2 ≤ 1 / a₀ := by
    rw [le_div_iff₀ ha₀]
    have h1 : G ^ 2 * a₀ ≤ G ^ 2 * β := mul_le_mul_of_nonneg_left hβa₀ (sq_nonneg G)
    have h2 : b ^ 2 ≤ 1 := pow_le_one₀ hb0 hb1
    linarith
  have hGC : G ≤ 1 + 1 / a₀ := (le_one_add_sq G).trans (by linarith)
  have hlam2 : lam ^ 2 ≤ 1 / a₀ := by
    have hM1 : 1 ≤ max 1 G ^ 2 := one_le_pow₀ (le_max_left _ _)
    rw [le_div_iff₀ ha₀]
    have h0 : a₀ ≤ max 1 G ^ 2 * β := by
      calc a₀ = 1 * a₀ := (one_mul a₀).symm
        _ ≤ max 1 G ^ 2 * β := mul_le_mul hM1 hβa₀ ha₀.le (by positivity)
    have h1 : lam ^ 2 * a₀ ≤ lam ^ 2 * (max 1 G ^ 2 * β) :=
      mul_le_mul_of_nonneg_left h0 (sq_nonneg lam)
    linarith
  have hlamΛ : lam ≤ Λ₁ := (le_one_add_sq lam).trans (by simp only [Λ₁]; linarith)
  set μ' := ((lam : ℝ) : ℂ)⁻¹ * μ with hμ'
  have hroot' : IsDysonRootV (hopB G) (gammaG G) L ((lam * e : ℝ) : ℂ) μ' := by
    have h := root_scale hrβ hlam
    rw [hlb, hlβ] at h
    rw [Complex.ofReal_mul]; exact h
  have hμ'im : ρm / Λ₁ ≤ μ'.im := by
    rw [hμ', ← Complex.ofReal_inv, Complex.im_ofReal_mul, inv_mul_eq_div]
    exact div_le_div₀ hμ0.le hρ hlam hlamΛ
  have hle : |lam * e| ≤ Λ₁ * (X + 1 / (a₀ * ρm) / ρm) := by
    rw [abs_mul, abs_of_pos hlam]
    exact mul_le_mul hlamΛ he (abs_nonneg _) (by positivity)
  obtain ⟨hMB, hRB, hSB⟩ := HS G hG0 hGC L hL3 hL₀ (lam * e) hle μ' hroot' hμ'im
  set MB := dysonMat (hopB G) (gammaG G) L ((lam * e : ℝ) : ℂ) μ' with hMBdef
  -- the matrix along the segment is `λ M_B`
  have hscale : MB = ((lam : ℝ) : ℂ)⁻¹ • dysonMat b β L e μ := by
    rw [hMBdef, ← hlb, ← hlβ, Complex.ofReal_mul]
    exact dysonMat_scale b β L e μ hlam
  have hlamc : ((lam : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  have hM : M = ((lam : ℝ) : ℂ) • MB := by
    rw [hscale, smul_smul, mul_inv_cancel₀ hlamc, one_smul]
    simp only [M]; rw [segMat_eq]; exact hMeq
  have hMij : ∀ i j, ‖M i j‖ = lam * ‖MB i j‖ := by
    intro i j
    rw [hM, Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg
      hlam.le]
  -- `γ_G ≥ Λ₁⁻²`
  have hγG : (Λ₁ ^ 2)⁻¹ ≤ gammaG G := by
    unfold gammaG
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ 2)
    exact max_le hΛ hGC
  have hrowB : ∀ i, ∑ j, (‖MB i j‖ + ‖MB i j‖ ^ 2) ≤ C₀' * Λ₁ ^ 2 := by
    intro i
    have h1 := hRB i
    have h2 : (Λ₁ ^ 2)⁻¹ * ∑ j, (‖MB i j‖ + ‖MB i j‖ ^ 2) ≤ C₀' :=
      le_trans (mul_le_mul_of_nonneg_right hγG (Finset.sum_nonneg fun j _ => by positivity)) h1
    rw [inv_mul_le_iff₀ (by positivity)] at h2
    linarith
  have hrowM : ∀ i, γ * ∑ j, (‖M i j‖ + ‖M i j‖ ^ 2) ≤ KR := by
    intro i
    have h1 : ∑ j, (‖M i j‖ + ‖M i j‖ ^ 2) ≤ (Λ₁ + Λ₁ ^ 2) * ∑ j, (‖MB i j‖ + ‖MB i j‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [hMij]
      have hx0 := norm_nonneg (MB i j)
      have hl2 : lam ^ 2 ≤ Λ₁ ^ 2 := pow_le_pow_left₀ hlam.le hlamΛ 2
      have e1 : (lam * ‖MB i j‖) ^ 2 = lam ^ 2 * ‖MB i j‖ ^ 2 := by ring
      rw [e1]
      have h3 : lam * ‖MB i j‖ ≤ Λ₁ * ‖MB i j‖ := mul_le_mul_of_nonneg_right hlamΛ hx0
      have h4 : lam ^ 2 * ‖MB i j‖ ^ 2 ≤ Λ₁ ^ 2 * ‖MB i j‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hl2 (sq_nonneg _)
      have h5 : Λ₁ * ‖MB i j‖ ≤ (Λ₁ + Λ₁ ^ 2) * ‖MB i j‖ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) hx0
      have h6 : Λ₁ ^ 2 * ‖MB i j‖ ^ 2 ≤ (Λ₁ + Λ₁ ^ 2) * ‖MB i j‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by linarith)) (sq_nonneg _)
      have e2 : (Λ₁ + Λ₁ ^ 2) * (‖MB i j‖ + ‖MB i j‖ ^ 2) =
          (Λ₁ + Λ₁ ^ 2) * ‖MB i j‖ + (Λ₁ + Λ₁ ^ 2) * ‖MB i j‖ ^ 2 := by ring
      rw [e2]
      linarith
    have h2 : γ * ∑ j, (‖M i j‖ + ‖M i j‖ ^ 2) ≤ ∑ j, (‖M i j‖ + ‖M i j‖ ^ 2) :=
      mul_le_of_le_one_left (Finset.sum_nonneg fun j _ => by positivity) hγ1
    calc γ * ∑ j, (‖M i j‖ + ‖M i j‖ ^ 2) ≤ (Λ₁ + Λ₁ ^ 2) * (C₀' * Λ₁ ^ 2) :=
          h2.trans (h1.trans (mul_le_mul_of_nonneg_left (hrowB i) (by positivity)))
      _ = KR := by simp only [KR]; ring
  have hrowM1 : ∀ i, γ * ∑ j, ‖M i j‖ ≤ KR := by
    intro i
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hγ0.le)
      (hrowM i)
    exact le_add_of_nonneg_right (sq_nonneg _)
  -- stable rows
  have hQ : pairQ a M = ((a / β : ℝ) : ℂ) • pairQ (gammaG G) MB := by
    ext i j
    rw [hM]
    simp only [pairQ, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← hlβ]
    have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ0.ne'
    push_cast; field_simp
  have ht0 : 0 ≤ a / β := by positivity
  have ht1 : a / β ≤ 1 := by rw [div_le_one hβ0]; exact haβ.le
  have hstab : ∀ i, ∑ j, ‖(1 - pairQ a M)⁻¹ i j‖ ≤ C₀' := by
    intro i; rw [hQ]; exact hSB (a / β) ht0 ht1 i
  -- invertibility
  have hrowP := pairP_row_sum b β hβ0 L (by omega) e μ hrβ
  simp only [pairP, Matrix.of_apply] at hrowP
  have hinv : IsUnit (1 - pairQ a M).det := by
    refine pairQ_isUnit ha.le fun i => ?_
    have h1 := hrowP i
    rw [← Finset.mul_sum] at h1
    have hM' : M = dysonMat b β L (e : ℂ) μ := by
      simp only [M]; rw [segMat_eq]; exact hMeq
    rw [hM']
    have h2 : a * ∑ j, ‖dysonMat b β L (↑e) μ i j‖ ^ 2 <
        β * ∑ j, ‖dysonMat b β L (↑e) μ i j‖ ^ 2 := by
      refine mul_lt_mul_of_pos_right haβ ?_
      by_contra hc
      push Not at hc
      have : β * ∑ j, ‖dysonMat b β L (↑e) μ i j‖ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hβ0.le hc
      linarith
    linarith
  -- derivatives
  have hyγ : 0 < y / γ := div_pos hy hγ0
  obtain ⟨w', hder, hid⟩ := seg_deriv hb0 ha hγ0 hL3 x hyγ
  have hMbM : ∀ i j, ‖M i j‖ ≤ Λ₁ * C₀' := fun i j => by
    rw [hMij]; exact mul_le_mul hlamΛ (hMB i j) (norm_nonneg _) (by positivity)
  obtain ⟨-, hd1, hd2⟩ := deriv_bounds (by omega) hγ0 (dysonMat_symm _ _ _ _ _) hid hinv hMbM
    hrowM1 hstab
  have hderiv : ∀ i j, deriv (fun r : ℝ => segMat g L x u r i j) (y / γ) = w' * (M * M) i j :=
    fun i j => (hder i j).deriv
  refine ⟨hr, hμρ.trans hμK, hMbM, hrowM, hstab, fun i j => (hder i j).differentiableAt,
    fun i j => ?_, fun i => ?_⟩
  · rw [hderiv]; exact hd1 i j
  · simp only [hderiv]; exact hd2 i

/-- Lemma 6.4 [da:lem:positive-height], bounded coupling: (6.12) [gc:eq:positive-stability] and
(6.14) [da:eq:height-derivative] on the segment from `z_u(g,E)` to the comparison point. -/
theorem positiveHeight_bdd (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') :
    ∃ c C' : ℝ, ∃ L₀ : ℕ, 0 < c ∧ 0 < C' ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      ∀ s u : ℝ, 1 / 2 ≤ s → s ≤ u → u < 1 →
      ∀ y : ℝ, etaChar g m u ≤ y → y ≤ (wCmp g L E m s u).im →
      let x := (zChar g E m u).re
      let z : ℂ := (x : ℂ) + (y : ℂ) * I
      let mu := mRootV (hopB g) (u * gammaG g) L z
      let M := segMat g L x u (y / gammaG g)
      IsDysonRootV (hopB g) (u * gammaG g) L z mu ∧ c ≤ mu.im ∧ mu.im ≤ C' ∧
      (∀ a b, ‖M a b‖ ≤ C') ∧ (∀ a, gammaG g * ∑ b, (‖M a b‖ + ‖M a b‖ ^ 2) ≤ C') ∧
      (∀ a, ∑ b, ‖(1 - pairQ (u * gammaG g) M)⁻¹ a b‖ ≤ C') ∧
      (∀ a b, DifferentiableAt ℝ (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)) ∧
      (∀ a b, ‖deriv (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)‖ ≤ C') ∧
      ∀ a, gammaG g * ∑ b, ‖deriv (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)‖ ≤ C' := by
  set a₀ := 1 / (2 * max 1 C ^ 2) with ha₀def
  set X := B₀ + 1 / c' with hXdef
  set ρm := min (c' / 2) (a₀ ^ 2 * c' ^ 3 / 4 / (X + 4) ^ 2) with hρm
  have ha₀ : 0 < a₀ := by positivity
  have hX0 : 0 < X := by positivity
  have hρm0 : 0 < ρm := lt_min (by positivity) (by positivity)
  obtain ⟨C₀', L₀, hC₀', HS⟩ := sbProp_of (1 + 1 / a₀) ((1 + 1 / a₀) * (X + 1 / (a₀ * ρm) / ρm))
    (ρm / (1 + 1 / a₀)) (by positivity) (by positivity) (by positivity)
  set Λ₁ := 1 + 1 / a₀ with hΛ₁
  set KR := (Λ₁ + Λ₁ ^ 2) * C₀' * Λ₁ ^ 2 with hKR
  set C' := 1 / (a₀ * ρm) + Λ₁ * C₀' + KR + C₀' + C₀' * (Λ₁ * C₀') * KR + C₀' * KR ^ 2 with hC'
  have hΛ0 : 0 < Λ₁ := by positivity
  have hKR0 : 0 ≤ KR := by positivity
  have t1 : 0 ≤ 1 / (a₀ * ρm) := by positivity
  have t2 : 0 ≤ Λ₁ * C₀' := by positivity
  have t3 : 0 ≤ C₀' * (Λ₁ * C₀') * KR := by positivity
  have t4 : 0 ≤ C₀' * KR ^ 2 := by positivity
  refine ⟨ρm, C', L₀, hρm0, by positivity, ?_⟩
  intro g hg hgC L hL3 hL₀ E hE m hm hcm s u hs hsu hu1 y hy hyw x z mu M
  obtain ⟨ha₀a, ha1, hX, -, hη1, hρ⟩ := bdd_setup hc' hg hgC hL3 hE hm hcm hs hsu hu1
  have H := step_core hg hL3 hm (by linarith) hsu hu1
  dsimp only at H
  obtain ⟨-, -, hη0, -, -, -, -, -, -, -, hw, -, -⟩ := H
  have hyη : y ≤ etaTube (hopB g) (u * gammaG g) (u / s * gammaG g) L x := by
    rw [hw, vert_im] at hyw; exact hyw
  have hy0 : 0 < y := lt_of_lt_of_le hη0 hy
  have hy1 : y ≤ 1 := hyη.trans hη1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    bdd_point HS ha₀ hρm0 hg hL3 hL₀ ha₀a hX hy0 hy1 (hρ y hy hy1)
  refine ⟨h1, hρ y hy hy1, h2.trans (by linarith), fun i j => (h3 i j).trans (by linarith),
    fun i => (h4 i).trans (by linarith), fun i => (h5 i).trans (by linarith), h6,
    fun i j => (h7 i j).trans (by linarith), fun i => (h8 i).trans (by linarith)⟩

/-- Lemma 6.4 [da:lem:positive-height], large coupling, on the direct domain `|x| ≤ 2 - κ/2`,
`0 < y ≤ C₀/g²`, `1/2 ≤ u ≤ 1`, which contains the comparison segments. -/
theorem positiveHeight_large (κ C₀ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC₀ : 0 < C₀) :
    ∃ Cκ R c C' : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ 0 < c ∧ 0 < C' ∧ ∀ g : ℝ, Cκ ≤ g →
      ∀ L : ℕ, R * g ^ 2 ≤ L → ∀ x y u : ℝ, |x| ≤ 2 - κ / 2 → 0 < y → y ≤ C₀ / g ^ 2 →
      1 / 2 ≤ u → u ≤ 1 →
      let z : ℂ := (x : ℂ) + (y : ℂ) * I
      let mu := mRootV (hopB g) (u * gammaG g) L z
      let M := segMat g L x u (y / gammaG g)
      IsDysonRootV (hopB g) (u * gammaG g) L z mu ∧ c ≤ mu.im ∧ mu.im ≤ C' ∧
      (∀ a b, ‖M a b‖ ≤ C') ∧ (∀ a, gammaG g * ∑ b, (‖M a b‖ + ‖M a b‖ ^ 2) ≤ C') ∧
      (∀ a, ∑ b, Real.exp (c * cycDist a b / g ^ 2) *
        ‖(1 - pairQ (u * gammaG g) M)⁻¹ a b‖ ≤ C') ∧
      (∀ a b, DifferentiableAt ℝ (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)) ∧
      (∀ a b, ‖deriv (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)‖ ≤ C') ∧
      ∀ a, gammaG g * ∑ b, ‖deriv (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)‖ ≤ C' :=
  ph_large_core κ C₀ hκ hκ2 hC₀

end LSBA
