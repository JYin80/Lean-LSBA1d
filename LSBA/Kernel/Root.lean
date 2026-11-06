import LSBA.Kernel.Defs

/-!
# Finite-cycle roots

Uniqueness and existence of the finite-cycle Dyson root in `ℂ_+` for every hopping and variance, the
diagonal of `M_B`, and the row identities of the pair kernels ((A.6) [da:eq:ward]).
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Finite averages `⟨·⟩ = L⁻¹ Σ_{k < L}` -/

/-- Average of a complex function over `Fin L`. -/
private def avgS (L : ℕ) (f : Fin L → ℂ) : ℂ := (L : ℂ)⁻¹ * ∑ k, f k

/-- Average of a real function over `Fin L`. -/
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

/-- Cauchy–Schwarz for averages: `‖⟨f h⟩‖² ≤ ⟨‖f‖²⟩ ⟨‖h‖²⟩`. -/
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

/-- Jensen for averages: `⟨x⟩² ≤ ⟨x²⟩`. -/
private lemma avg_sq_le {L : ℕ} (hL : 1 ≤ L) (x : Fin L → ℝ) :
    avgSR L x ^ 2 ≤ avgSR L (fun k => x k ^ 2) := by
  have hL' : (0 : ℝ) < L := by positivity
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)
  unfold avgSR
  rw [Finset.card_univ, Fintype.card_fin] at h
  calc ((L : ℝ)⁻¹ * ∑ k, x k) ^ 2 = ((L : ℝ)⁻¹) ^ 2 * (∑ k, x k) ^ 2 := mul_pow _ _ _
    _ ≤ ((L : ℝ)⁻¹) ^ 2 * (L * ∑ k, x k ^ 2) := by gcongr
    _ = (L : ℝ)⁻¹ * ∑ k, x k ^ 2 := by field_simp

/-! ### The resolvent `R_w(k) = (2b cos(2πk/L) - w)⁻¹` -/

/-- Summand of `freeTL b L w`. -/
private def resL (b : ℝ) (L : ℕ) (w : ℂ) (k : Fin L) : ℂ :=
  ((2 * b * Real.cos (2 * π * k / L) : ℝ) - w)⁻¹

private lemma freeTL_eq_avgS (b : ℝ) (L : ℕ) (w : ℂ) : freeTL b L w = avgS L (resL b L w) := rfl

private lemma resL_base_ne {b : ℝ} {L : ℕ} {w : ℂ} (hw : 0 < w.im) (k : Fin L) :
    ((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ) - w ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at this
  linarith

/-- Pointwise Ward identity: `Im R_w = Im w · |R_w|²`. -/
private lemma im_resL (b : ℝ) (L : ℕ) (w : ℂ) (k : Fin L) :
    (resL b L w k).im = w.im * ‖resL b L w k‖ ^ 2 := by
  unfold resL
  rw [Complex.inv_im, Complex.sq_norm, Complex.normSq_inv]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  ring

/-- Resolvent identity `R_w - R_{w'} = (w - w') R_w R_{w'}`. -/
private lemma resL_sub_resL (b : ℝ) (L : ℕ) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im)
    (k : Fin L) :
    resL b L w k - resL b L w' k = (w - w') * (resL b L w k * resL b L w' k) := by
  unfold resL
  have h1 := resL_base_ne (b := b) (L := L) hw k
  have h2 := resL_base_ne (b := b) (L := L) hw' k
  field_simp
  ring

/-- `⟨|R_w|²⟩`. -/
private def nsqL (b : ℝ) (L : ℕ) (w : ℂ) : ℝ := avgSR L (fun k => ‖resL b L w k‖ ^ 2)

private lemma nsqL_nonneg (b : ℝ) (L : ℕ) (w : ℂ) : 0 ≤ nsqL b L w :=
  avgSR_nonneg fun _ => sq_nonneg _

private lemma freeTL_sub_freeTL (b : ℝ) (L : ℕ) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) :
    freeTL b L w - freeTL b L w' = (w - w') * avgS L (fun k => resL b L w k * resL b L w' k) := by
  rw [freeTL_eq_avgS, freeTL_eq_avgS, ← avgS_sub, ← avgS_const_mul]
  congr 1
  funext k
  exact resL_sub_resL b L hw hw' k

/-- Ward identity for `freeTL`: `Im f(w) = Im w · ⟨|R_w|²⟩`. -/
private lemma im_freeTL (b : ℝ) (L : ℕ) (w : ℂ) : (freeTL b L w).im = w.im * nsqL b L w := by
  rw [freeTL_eq_avgS, im_avgS, nsqL, ← avgSR_const_mul]
  congr 1
  funext k
  exact im_resL b L w k

/-- Scaling `freeTL (cb) L (cw) = c⁻¹ freeTL b L w` for real `c ≠ 0`. -/
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

/-! ### Stability of roots: the Ward contraction (A.6) [da:eq:ward] -/

/-- At two roots, with `A = ⟨R_{w₁} R_{w₂}⟩`: `‖A‖ ≤ β⁻¹`, `Re(1 - βA) ≥ β(Im m₁)²/2`, and
`m₁ - m₂ = (w₁ - w₂) A`. -/
private lemma stab_core (b β : ℝ) (hβ : 0 < β) {L : ℕ} (hL : 1 ≤ L) {w₁ w₂ m₁ m₂ : ℂ}
    (hw₁ : 0 < w₁.im) (hw₂ : 0 < w₂.im) (hm₁ : 0 < m₁.im) (hm₂ : 0 < m₂.im)
    (e₁ : m₁ = freeTL b L w₁) (e₂ : m₂ = freeTL b L w₂) (hi₁ : β * m₁.im ≤ w₁.im)
    (hi₂ : β * m₂.im ≤ w₂.im) :
    ‖avgS L (fun k => resL b L w₁ k * resL b L w₂ k)‖ ≤ β⁻¹ ∧
      β * m₁.im ^ 2 / 2 ≤ (1 - (β : ℂ) * avgS L (fun k => resL b L w₁ k * resL b L w₂ k)).re ∧
      m₁ - m₂ = (w₁ - w₂) * avgS L (fun k => resL b L w₁ k * resL b L w₂ k) := by
  set A := avgS L (fun k => resL b L w₁ k * resL b L w₂ k) with hA
  -- Ward: `β ⟨|R_j|²⟩ ≤ 1`
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
  · -- pointwise: `2 Re(R₁R₂) + (Im R₁)² ≤ |R₁|² + |R₂|²`
    have hpt : ∀ k, 2 * (resL b L w₁ k * resL b L w₂ k).re + (resL b L w₁ k).im ^ 2 ≤
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

/-- Stability of roots in `ℂ_+` at `Im z ≥ 0`:
`‖m₁ - m₂‖ · β(Im m₁)²/2 ≤ ‖z₁ - z₂‖ / β`. -/
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

/-- Existence of a root in `ℂ_+` for `Im z > 0`, by scaling `(b, β, z)` to the model parameters
`(√γ_g g, γ_g, λz)` with `g = b/√β`. -/
private lemma root_exists (b β : ℝ) (hb : 0 ≤ b) (hβ : 0 < β) {L : ℕ} (hL : 1 ≤ L) (z : ℂ)
    (hz : 0 < z.im) : ∃ m : ℂ, IsDysonRootV b β L z m := by
  set g := b / Real.sqrt β with hg
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hsq : Real.sqrt β ^ 2 = β := Real.sq_sqrt hβ.le
  have hg0 : 0 ≤ g := div_nonneg hb hsβ.le
  set M := max 1 g with hM
  have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  set c := (M * Real.sqrt β)⁻¹ with hc
  have hcpos : 0 < c := by positivity
  have hcb : c * b = hopB g := by
    rw [hopB, ← hM, hc, hg]; field_simp
  have hcβ : c ^ 2 * β = gammaG g := by
    rw [gammaG, ← hM, hc, inv_pow, mul_pow, hsq]; field_simp
  obtain ⟨hm', e'⟩ := mDysonL_spec g hg0 L hL ((c : ℂ) * z) (by
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]; positivity)
  set m' := mDysonL g L ((c : ℂ) * z)
  refine ⟨(c : ℂ) * m', by
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]; positivity, ?_⟩
  unfold dysonRHSV
  unfold dysonRHSL at e'
  have h1 := freeTL_scale b L (z + (β : ℂ) * ((c : ℂ) * m')) hcpos.ne'
  have h2 : (c : ℂ) * (z + (β : ℂ) * ((c : ℂ) * m')) = (c : ℂ) * z + (gammaG g : ℂ) * m' := by
    rw [← hcβ]; push_cast; ring
  rw [h2, hcb, ← e'] at h1
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
  conv_lhs => rw [h1]
  rw [← mul_assoc, mul_inv_cancel₀ hc', one_mul]

/-- Uniqueness of the solution in `ℂ_+` at `Im z ≥ 0` (Ward identity (A.6) [da:eq:ward]). -/
theorem isDysonRootV_unique (b β : ℝ) (hb : 0 ≤ b) (hβ : 0 < β) (L : ℕ) (hL : 3 ≤ L) (z : ℂ)
    (hz : 0 ≤ z.im) (m₁ m₂ : ℂ) (h₁ : IsDysonRootV b β L z m₁) (h₂ : IsDysonRootV b β L z m₂) :
    m₁ = m₂ := by
  have h := root_stab b β hβ (by omega : 1 ≤ L) hz hz h₁ h₂
  rw [sub_self, norm_zero, zero_div] at h
  have hpos : 0 < β * m₁.im ^ 2 / 2 := by have := h₁.1; positivity
  have h0 : ‖m₁ - m₂‖ = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_left h hpos) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- Existence in `ℂ_+` for `Im z > 0`, and the selected solution. -/
theorem mRootV_spec (b β : ℝ) (hb : 0 ≤ b) (hβ : 0 < β) (L : ℕ) (hL : 3 ≤ L) (z : ℂ)
    (hz : 0 ≤ z.im) :
    (0 < z.im → IsDysonRootV b β L z (mRootV b β L z)) ∧
      ∀ m : ℂ, IsDysonRootV b β L z m → mRootV b β L z = m := by
  have hsel : ∀ h : ∃ m : ℂ, IsDysonRootV b β L z m, mRootV b β L z = h.choose := by
    intro h
    unfold mRootV
    split_ifs
    rfl
  refine ⟨fun hz' => ?_, fun m hm => ?_⟩
  · have h := root_exists b β hb hβ (by omega : 1 ≤ L) z hz'
    rw [hsel h]
    exact h.choose_spec
  · have h : ∃ m : ℂ, IsDysonRootV b β L z m := ⟨m, hm⟩
    rw [hsel h]
    exact isDysonRootV_unique b β hb hβ L hL z hz _ _ h.choose_spec hm

/-! ### The cycle resolvent in Fourier variables (A.1) [bl:eq:physical] -/

/-- `ζ = e^{2πi/L}`. -/
private def zetaL (L : ℕ) : ℂ := Complex.exp (2 * π * I / L)

private lemma zetaL_ne_zero (L : ℕ) : zetaL L ≠ 0 := Complex.exp_ne_zero _

private lemma zetaL_prim {L : ℕ} (hL : 1 ≤ L) : IsPrimitiveRoot (zetaL L) L :=
  Complex.isPrimitiveRoot_exp L (by omega)

/-- `b(ζ^k + ζ^{-k}) = 2b cos(2πk/L)`. -/
private lemma zetaL_cos (b : ℝ) (L k : ℕ) :
    (b : ℂ) * (zetaL L ^ k + (zetaL L)⁻¹ ^ k) = ((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ) := by
  have h1 : zetaL L ^ k = Complex.exp (((2 * π * k / L : ℝ) : ℂ) * I) := by
    rw [zetaL, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h2 : (zetaL L)⁻¹ ^ k = Complex.exp (-((2 * π * k / L : ℝ) : ℂ) * I) := by
    rw [inv_pow, h1, ← Complex.exp_neg]
    congr 1
    ring
  rw [h1, h2, ← Complex.two_cos]
  push_cast
  ring

/-- Orthogonality `Σ_k ζ^{ka} ζ^{-kc} = L δ_{ac}`. -/
private lemma zetaL_orth {L : ℕ} (hL : 1 ≤ L) (a c : Fin L) :
    ∑ k : Fin L, zetaL L ^ (k.val * a.val) * (zetaL L)⁻¹ ^ (k.val * c.val) =
      if a = c then (L : ℂ) else 0 := by
  have hp := zetaL_prim hL
  have hz := zetaL_ne_zero L
  set x := zetaL L ^ a.val * (zetaL L)⁻¹ ^ c.val with hx
  have hk : ∀ k : Fin L,
      zetaL L ^ (k.val * a.val) * (zetaL L)⁻¹ ^ (k.val * c.val) = x ^ k.val := by
    intro k
    rw [hx, mul_pow, ← pow_mul, ← pow_mul, mul_comm a.val, mul_comm c.val]
  simp_rw [hk]
  rw [Fin.sum_univ_eq_sum_range (fun i => x ^ i) L]
  split_ifs with hac
  · subst hac
    have : x = 1 := by rw [hx, ← mul_pow, mul_inv_cancel₀ hz, one_pow]
    simp [this]
  · have hx1 : x ≠ 1 := by
      intro h
      apply hac
      have h' : zetaL L ^ a.val = zetaL L ^ c.val := by
        rw [eq_inv_of_mul_eq_one_left h, inv_pow, inv_inv]
      exact Fin.ext (hp.pow_inj a.isLt c.isLt h')
    have hxL : x ^ L = 1 := by
      rw [hx, mul_pow, ← pow_mul, ← pow_mul, mul_comm a.val L, mul_comm c.val L, pow_mul,
        pow_mul, inv_pow, hp.pow_eq_one, inv_one, one_pow, one_pow, one_mul]
    rw [geom_sum_eq hx1, hxL, sub_self, zero_div]

/-- The successor on `ℤ_L`. -/
private def cycSucc {L : ℕ} (a : Fin L) : Fin L :=
  ⟨if a.val + 1 < L then a.val + 1 else 0, by have := a.isLt; split_ifs <;> omega⟩

/-- The predecessor on `ℤ_L`. -/
private def cycPred {L : ℕ} (a : Fin L) : Fin L :=
  ⟨if 0 < a.val then a.val - 1 else L - 1, by have := a.isLt; split_ifs <;> omega⟩

private lemma succ_mod_eq (L x : ℕ) (hx : x < L) :
    (x + 1) % L = if x + 1 < L then x + 1 else 0 := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : x + 1 = L := by omega
    rw [this, Nat.mod_self]

private lemma cycleAdj_apply {L : ℕ} (a k : Fin L) :
    cycleAdj L a k = (if k = cycSucc a then 1 else 0) + (if k = cycPred a then 1 else 0) := by
  simp only [cycleAdj, Matrix.of_apply]
  have hk := k.isLt
  have ha := a.isLt
  have h1 : (k.val = (a.val + 1) % L) ↔ k = cycSucc a := by
    rw [succ_mod_eq L a.val ha, Fin.ext_iff]
    simp only [cycSucc]
  have h2 : (a.val = (k.val + 1) % L) ↔ k = cycPred a := by
    rw [succ_mod_eq L k.val hk, Fin.ext_iff]
    simp only [cycPred]
    split_ifs <;> omega
  rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl]

private lemma zetaL_succ {L : ℕ} (hL : 1 ≤ L) (a : Fin L) (k : ℕ) :
    zetaL L ^ (k * (cycSucc a).val) = zetaL L ^ (k * a.val) * zetaL L ^ k := by
  have hp := zetaL_prim hL
  by_cases h : a.val + 1 < L
  · have e : (cycSucc a).val = a.val + 1 := by simp [cycSucc, h]
    rw [e, mul_add, mul_one, pow_add]
  · have e : (cycSucc a).val = 0 := by simp [cycSucc, h]
    have hL' : a.val + 1 = L := by have := a.isLt; omega
    have e2 : k * a.val + k = L * k :=
      calc k * a.val + k = k * (a.val + 1) := by ring
        _ = k * L := by rw [hL']
        _ = L * k := mul_comm _ _
    rw [e, mul_zero, pow_zero, ← pow_add, e2, pow_mul, hp.pow_eq_one, one_pow]

private lemma zetaL_pred {L : ℕ} (hL : 1 ≤ L) (a : Fin L) (k : ℕ) :
    zetaL L ^ (k * (cycPred a).val) = zetaL L ^ (k * a.val) * (zetaL L)⁻¹ ^ k := by
  have hp := zetaL_prim hL
  have hz := zetaL_ne_zero L
  have hkk : zetaL L ^ k * (zetaL L)⁻¹ ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  by_cases h : 0 < a.val
  · have e : (cycPred a).val = a.val - 1 := by simp [cycPred, h]
    obtain ⟨j, hj⟩ : ∃ j, a.val = j + 1 := ⟨a.val - 1, by omega⟩
    rw [e, hj, Nat.add_sub_cancel, mul_add, mul_one, pow_add, mul_assoc, hkk, mul_one]
  · have e : (cycPred a).val = L - 1 := by simp [cycPred, h]
    have ha : a.val = 0 := by omega
    rw [e, ha, mul_zero, pow_zero, one_mul]
    have h1 : zetaL L ^ (k * (L - 1)) * zetaL L ^ k = 1 := by
      rw [← pow_add, show k * (L - 1) + k = L * k by
        obtain ⟨j, hj⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
        rw [hj, Nat.add_sub_cancel]; ring, pow_mul, hp.pow_eq_one, one_pow]
    rw [eq_inv_of_mul_eq_one_left h1, inv_pow]

/-- The cycle resolvent `(bA_L - w)⁻¹` in Fourier variables:
`N_{ac} = L⁻¹ Σ_k ζ^{ka} ζ^{-kc} (2b cos(2πk/L) - w)⁻¹`. -/
private def fourN (b : ℝ) (L : ℕ) (w : ℂ) : Matrix (Fin L) (Fin L) ℂ :=
  Matrix.of fun a c => (L : ℂ)⁻¹ *
    ∑ k : Fin L, zetaL L ^ (k.val * a.val) * (zetaL L)⁻¹ ^ (k.val * c.val) * resL b L w k

private lemma cycle_fourN (b : ℝ) {L : ℕ} (hL : 1 ≤ L) {w : ℂ} (hw : 0 < w.im) :
    ((b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ)) * fourN b L w = 1 := by
  ext a c
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin L,
      ((b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ)) a k * fourN b L w k c =
        (if k = cycSucc a then (b : ℂ) * fourN b L w k c else 0) +
        (if k = cycPred a then (b : ℂ) * fourN b L w k c else 0) -
        (if k = a then w * fourN b L w k c else 0) := by
    intro k
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      cycleAdj_apply, eq_comm (a := a) (b := k)]
    split_ifs <;> ring
  simp_rw [key]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hterm : ∀ k : Fin L,
      (b : ℂ) * (zetaL L ^ (k.val * (cycSucc a).val) * (zetaL L)⁻¹ ^ (k.val * c.val) *
          resL b L w k) +
        (b : ℂ) * (zetaL L ^ (k.val * (cycPred a).val) * (zetaL L)⁻¹ ^ (k.val * c.val) *
          resL b L w k) -
        w * (zetaL L ^ (k.val * a.val) * (zetaL L)⁻¹ ^ (k.val * c.val) * resL b L w k) =
      zetaL L ^ (k.val * a.val) * (zetaL L)⁻¹ ^ (k.val * c.val) := by
    intro k
    rw [zetaL_succ hL, zetaL_pred hL]
    have h1 := zetaL_cos b L k.val
    have h2 : (((2 * b * Real.cos (2 * π * (k.val : ℕ) / L) : ℝ) : ℂ) - w) * resL b L w k = 1 :=
      mul_inv_cancel₀ (resL_base_ne hw k)
    linear_combination
      (zetaL L ^ (k.val * a.val) * (zetaL L)⁻¹ ^ (k.val * c.val) * resL b L w k) * h1 +
      (zetaL L ^ (k.val * a.val) * (zetaL L)⁻¹ ^ (k.val * c.val)) * h2
  simp only [fourN, Matrix.of_apply]
  calc (b : ℂ) * ((L : ℂ)⁻¹ * ∑ k : Fin L, zetaL L ^ (k.val * (cycSucc a).val) *
          (zetaL L)⁻¹ ^ (k.val * c.val) * resL b L w k) +
        (b : ℂ) * ((L : ℂ)⁻¹ * ∑ k : Fin L, zetaL L ^ (k.val * (cycPred a).val) *
          (zetaL L)⁻¹ ^ (k.val * c.val) * resL b L w k) -
        w * ((L : ℂ)⁻¹ * ∑ k : Fin L, zetaL L ^ (k.val * a.val) *
          (zetaL L)⁻¹ ^ (k.val * c.val) * resL b L w k)
      = (L : ℂ)⁻¹ * ∑ k : Fin L,
          ((b : ℂ) * (zetaL L ^ (k.val * (cycSucc a).val) * (zetaL L)⁻¹ ^ (k.val * c.val) *
              resL b L w k) +
            (b : ℂ) * (zetaL L ^ (k.val * (cycPred a).val) * (zetaL L)⁻¹ ^ (k.val * c.val) *
              resL b L w k) -
            w * (zetaL L ^ (k.val * a.val) * (zetaL L)⁻¹ ^ (k.val * c.val) * resL b L w k)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum]
        ring
    _ = (L : ℂ)⁻¹ * ∑ k : Fin L, zetaL L ^ (k.val * a.val) * (zetaL L)⁻¹ ^ (k.val * c.val) := by
        simp_rw [hterm]
    _ = (1 : Matrix (Fin L) (Fin L) ℂ) a c := by
        rw [zetaL_orth hL, Matrix.one_apply]
        have : (L : ℂ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
        split_ifs
        · exact inv_mul_cancel₀ this
        · exact mul_zero _

private lemma dysonMat_eq_fourN (b β : ℝ) {L : ℕ} (hL : 1 ≤ L) (z m : ℂ)
    (hw : 0 < (z + β * m).im) : dysonMat b β L z m = fourN b L (z + β * m) :=
  Matrix.inv_eq_right_inv (cycle_fourN b hL hw)

/-- Ward identity for an inverse `N` of `B` with `Bᴴ - B = (w - w̄) I`:
`Im N_aa = Im w · Σ_c |N_ac|²`. -/
private lemma ward_of_inv {n : Type*} [Fintype n] [DecidableEq n] (B N : Matrix n n ℂ) (w : ℂ)
    (hBN : B * N = 1) (hBH : B.conjTranspose - B = (w - starRingEnd ℂ w) • (1 : Matrix n n ℂ))
    (a : n) : (N a a).im = w.im * ∑ c, ‖N a c‖ ^ 2 := by
  have hNB : N * B = 1 := mul_eq_one_comm.mp hBN
  have hBHN : B.conjTranspose * N.conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, hNB, Matrix.conjTranspose_one]
  have key : N - N.conjTranspose = (w - starRingEnd ℂ w) • (N * N.conjTranspose) := by
    calc N - N.conjTranspose =
          N * (B.conjTranspose * N.conjTranspose) - (N * B) * N.conjTranspose := by
          rw [hBHN, hNB, Matrix.mul_one, Matrix.one_mul]
      _ = N * (B.conjTranspose - B) * N.conjTranspose := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = (w - starRingEnd ℂ w) • (N * N.conjTranspose) := by
          rw [hBH, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have he := congrFun (congrFun key a) a
  simp only [Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.mul_apply,
    smul_eq_mul] at he
  have hs : ∑ c, N a c * star (N a c) = ((∑ c, ‖N a c‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hs] at he
  have him := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.mul_im,
    Complex.ofReal_im, Complex.ofReal_re, mul_zero, Complex.sub_re, Complex.conj_re] at him
  linarith

/-- Ward identity for the cycle resolvent: `Im N_aa = Im w · Σ_c |N_ac|²`. -/
private lemma fourN_ward (b : ℝ) {L : ℕ} (hL : 1 ≤ L) {w : ℂ} (hw : 0 < w.im) (a : Fin L) :
    (fourN b L w a a).im = w.im * ∑ c, ‖fourN b L w a c‖ ^ 2 := by
  refine ward_of_inv _ _ w (cycle_fourN b hL hw) ?_ a
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    (cycleAdj_isHermitian L).eq, Matrix.conjTranspose_one, sub_smul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  abel

/-- The diagonal of the cycle resolvent is the Fourier average, (A.1) [bl:eq:physical];
`M_aa = m` at a solution, (5.3) [fo:eq:characteristic]. -/
theorem dysonMat_diag (b β : ℝ) (L : ℕ) (hL : 1 ≤ L) (z m : ℂ) (hw : 0 < (z + β * m).im)
    (a : Fin L) : dysonMat b β L z m a a = dysonRHSV b β L z m := by
  rw [dysonMat_eq_fourN b β hL z m hw]
  have hz := zetaL_ne_zero L
  have h1 : ∀ k : Fin L, zetaL L ^ (k.val * a.val) * (zetaL L)⁻¹ ^ (k.val * a.val) *
      resL b L (z + β * m) k = resL b L (z + β * m) k := by
    intro k
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow, one_mul]
  simp only [fourN, Matrix.of_apply, h1]
  rfl

/-- Ward identity at a real energy: `Σ_b P_ab = 1`, after (5.13) [fo:eq:pairs]. -/
theorem pairP_row_sum (b β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : 1 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV b β L E m) (a : Fin L) :
    ∑ c, pairP β (dysonMat b β L E m) a c = 1 := by
  obtain ⟨hm0, e⟩ := hm
  have hwi : ((E : ℂ) + β * m).im = β * m.im := by simp
  have hw : 0 < ((E : ℂ) + β * m).im := by rw [hwi]; positivity
  have hd := dysonMat_diag b β L hL E m hw a
  rw [← e] at hd
  have hward := fourN_ward b hL hw a
  rw [← dysonMat_eq_fourN b β hL E m hw, hd, hwi] at hward
  simp only [pairP, Matrix.of_apply]
  rw [← Finset.mul_sum]
  have hpos : 0 < m.im := hm0
  have : m.im * (β * ∑ c, ‖dysonMat b β L E m a c‖ ^ 2) = m.im * 1 := by
    rw [mul_one]; linarith
  exact mul_left_cancel₀ hpos.ne' this

/-! ### Same-sign stability (A.31) [ba:eq:gap], (A.32) [ba:eq:stableinverse] -/

/-- Row bound for the inverse of a strictly row-dominant matrix: if
`G + Σ_{c ≠ a} |B_ac| ≤ |B_aa|` for every row, then every absolute row of `B⁻¹` is at most `1/G`. -/
private lemma dominant_inv_row_le {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ)
    {G : ℝ} (hG : 0 < G) (h : ∀ a, G + ∑ c ∈ Finset.univ.erase a, ‖B a c‖ ≤ ‖B a a‖) (a : n) :
    ∑ c, ‖B⁻¹ a c‖ ≤ 1 / G := by
  -- lower bound `G ‖v‖_∞ ≤ ‖Bv‖_∞`
  have hlow : ∀ (v : n → ℂ) (K : ℝ), (∀ i, ‖(B.mulVec v) i‖ ≤ K) → ∀ i, G * ‖v i‖ ≤ K := by
    intro v K hK i
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖)
      ⟨i, Finset.mem_univ _⟩
    have hmax : ∀ j, ‖v j‖ ≤ ‖v i₀‖ := fun j => hi₀ j (Finset.mem_univ _)
    have hsplit : (B.mulVec v) i₀ = B i₀ i₀ * v i₀ + ∑ c ∈ Finset.univ.erase i₀, B i₀ c * v c := by
      rw [Matrix.mulVec, dotProduct]
      exact (Finset.add_sum_erase Finset.univ (fun c => B i₀ c * v c) (Finset.mem_univ i₀)).symm
    have hrest : ‖∑ c ∈ Finset.univ.erase i₀, B i₀ c * v c‖ ≤
        (∑ c ∈ Finset.univ.erase i₀, ‖B i₀ c‖) * ‖v i₀‖ := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun c _ => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hmax c) (norm_nonneg _)
    have h1 : ‖B i₀ i₀‖ * ‖v i₀‖ - (∑ c ∈ Finset.univ.erase i₀, ‖B i₀ c‖) * ‖v i₀‖ ≤
        ‖(B.mulVec v) i₀‖ := by
      rw [hsplit]
      have := norm_sub_norm_le (B i₀ i₀ * v i₀) (-∑ c ∈ Finset.univ.erase i₀, B i₀ c * v c)
      rw [sub_neg_eq_add, norm_neg, norm_mul] at this
      linarith
    have h2 : G * ‖v i₀‖ ≤
        ‖B i₀ i₀‖ * ‖v i₀‖ - (∑ c ∈ Finset.univ.erase i₀, ‖B i₀ c‖) * ‖v i₀‖ := by
      have := mul_le_mul_of_nonneg_right (h i₀) (norm_nonneg (v i₀))
      linarith
    calc G * ‖v i‖ ≤ G * ‖v i₀‖ := mul_le_mul_of_nonneg_left (hmax i) hG.le
      _ ≤ K := h2.trans (h1.trans (hK i₀))
  have hdet : B.det ≠ 0 := det_ne_zero_of_sum_row_lt_diag fun k => by
    have := h k
    linarith
  have hBX : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hdet)
  set X := B⁻¹ with hX
  set y : n → ℂ := fun c => star (X a c) / (‖X a c‖ : ℂ) with hy
  have hyn : ∀ c, ‖y c‖ ≤ 1 := by
    intro c
    simp only [hy, norm_div, Complex.norm_real, norm_norm, norm_star]
    exact div_self_le_one _
  have hBv : B.mulVec (X.mulVec y) = y := by
    rw [Matrix.mulVec_mulVec, hBX, Matrix.one_mulVec]
  have hv : (X.mulVec y) a = ((∑ c, ‖X a c‖ : ℝ) : ℂ) := by
    rw [Matrix.mulVec, dotProduct]
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hy]
    by_cases h0 : X a c = 0
    · simp [h0]
    · have hn : (‖X a c‖ : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr h0
      rw [mul_div_assoc', Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      field_simp
      push_cast
      ring
  have hl := hlow (X.mulVec y) 1 (fun i => by rw [hBv]; exact hyn i) a
  rw [hv, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    at hl
  rw [le_div_iff₀ hG, mul_comm]
  exact hl

/-- The gap inequality behind (A.31) [ba:eq:gap]:
`(t(1 - x) + y/2)² ≤ (1 - tx)² + 4ty` for `0 ≤ t ≤ 1`, `0 ≤ y ≤ x ≤ 1`. -/
private lemma gap_sq_le {t x y : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hy : 0 ≤ y) (hyx : y ≤ x)
    (hx1 : x ≤ 1) : (t * (1 - x) + y / 2) ^ 2 ≤ (1 - t * x) ^ 2 + 4 * t * y := by
  have e : (1 - t * x) ^ 2 + 4 * t * y - (t * (1 - x) + y / 2) ^ 2 =
      2 * (1 - t) * (t * (1 - x)) + y * (t * x) + (1 - t - 3 * y / 2) ^ 2 +
        y * (3 - 5 * y / 2) := by ring
  have h1 : 0 ≤ 2 * (1 - t) * (t * (1 - x)) := by
    have : 0 ≤ 1 - x := by linarith
    have : 0 ≤ 1 - t := by linarith
    positivity
  have h2 : 0 ≤ y * (t * x) := by
    have : 0 ≤ x := hy.trans hyx
    positivity
  have h3 : 0 ≤ y * (3 - 5 * y / 2) := mul_nonneg hy (by linarith)
  nlinarith [sq_nonneg (1 - t - 3 * y / 2)]

/-- Same-sign stability with an explicit constant, (A.31) [ba:eq:gap] and (A.32)
[ba:eq:stableinverse], for every `L`. -/
theorem sameSign_row_le (b β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : 1 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV b β L E m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a : Fin L) :
    ∑ c, ‖(1 - (t : ℂ) • pairQ β (dysonMat b β L E m))⁻¹ a c‖ ≤ 2 / (β * m.im ^ 2) := by
  have hrow := pairP_row_sum b β hβ L hL E m hm
  obtain ⟨hm0, e⟩ := hm
  have hw : 0 < ((E : ℂ) + β * m).im := by
    have : ((E : ℂ) + β * m).im = β * m.im := by simp
    rw [this]; positivity
  set M := dysonMat b β L E m with hM
  have hdiag : ∀ i, M i i = m := fun i => by
    rw [hM, dysonMat_diag b β L hL E m hw i, ← e]
  set B := 1 - (t : ℂ) • pairQ β M with hB
  have hBoff : ∀ i c, c ≠ i → ‖B i c‖ = t * (β * ‖M i c‖ ^ 2) := by
    intro i c hc
    simp only [hB, pairQ, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul, Matrix.one_apply_ne (Ne.symm hc), zero_sub, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg ht0, Real.norm_of_nonneg hβ.le, norm_pow]
  have hBdiag : ∀ i, B i i = 1 - (t : ℂ) * ((β : ℂ) * m ^ 2) := by
    intro i
    simp only [hB, pairQ, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul, hdiag]
  set x := β * ‖m‖ ^ 2 with hx
  set y := β * m.im ^ 2 with hy
  have hypos : 0 < y := by positivity
  have hrow' : ∀ i, ∑ c, β * ‖M i c‖ ^ 2 = 1 := fun i => by
    have := hrow i
    simpa [pairP, Matrix.of_apply] using this
  have hx1 : x ≤ 1 := by
    have h := Finset.single_le_sum (f := fun c => β * ‖M a c‖ ^ 2)
      (fun c _ => by positivity) (Finset.mem_univ a)
    rw [hrow' a] at h
    simpa [hdiag, hx] using h
  have hyx : y ≤ x := by
    rw [hx, hy, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg m.re]
  have hdom : ∀ i, y / 2 + ∑ c ∈ Finset.univ.erase i, ‖B i c‖ ≤ ‖B i i‖ := by
    intro i
    have hsum : ∑ c ∈ Finset.univ.erase i, ‖B i c‖ = t * (1 - x) := by
      rw [Finset.sum_congr rfl fun c hc => hBoff i c (Finset.ne_of_mem_erase hc),
        ← Finset.mul_sum]
      have := Finset.add_sum_erase Finset.univ (fun c => β * ‖M i c‖ ^ 2) (Finset.mem_univ i)
      rw [hrow' i, hdiag] at this
      have hs' : ∑ c ∈ Finset.univ.erase i, β * ‖M i c‖ ^ 2 = 1 - β * ‖m‖ ^ 2 := by linarith
      rw [hs']
    rw [hsum, hBdiag, add_comm]
    have hnsq : Complex.normSq (1 - (t : ℂ) * ((β : ℂ) * m ^ 2)) =
        (1 - t * x) ^ 2 + 4 * t * y := by
      rw [hx, hy, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im, pow_two]
      ring
    rw [Complex.norm_def, hnsq]
    have h0 : 0 ≤ t * (1 - x) + y / 2 := by
      have : 0 ≤ 1 - x := by linarith
      positivity
    exact (Real.le_sqrt h0 (by positivity)).mpr (gap_sq_le ht0 ht1 hypos.le hyx hx1)
  have h := dominant_inv_row_le B (by positivity : 0 < y / 2) hdom a
  calc ∑ c, ‖B⁻¹ a c‖ ≤ 1 / (y / 2) := h
    _ = 2 / (β * m.im ^ 2) := by rw [hy]; field_simp

end LSBA
