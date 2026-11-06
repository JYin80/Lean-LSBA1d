import LSBA.Dyson.Scalar

/-!
# The finite-cycle Dyson equation

The Dyson equation (5.2) [fo:eq:dyson-family] on the cycle of `L` blocks: its unique solution
`m_{g,L}` in `ℂ_+`, holomorphy, and its boundary values at real energies.
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- Right side of (5.2) [fo:eq:dyson-family]. -/
def dysonRHSL (g : ℝ) (L : ℕ) (z u : ℂ) : ℂ := freeTL (hopB g) L (z + gammaG g * u)

/-- `m_{g,L}(z)`: the unique solution of (5.2) [fo:eq:dyson-family] in `ℂ_+` (junk value `0` if
there is none). -/
def mDysonL (g : ℝ) (L : ℕ) (z : ℂ) : ℂ :=
  if h : ∃! u : ℂ, 0 < u.im ∧ u = dysonRHSL g L z u then h.exists.choose else 0

/-- Boundary value `m_{g,L}(E) = lim_{η↓0} m_{g,L}(E + iη)` (`limUnder`; if the limit fails, the
value is the `limUnder` choice, not `0`). -/
def mDysonLBdry (g : ℝ) (L : ℕ) (E : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun η : ℝ => mDysonL g L (E + η * I)

/-! ### Finite averages `⟨·⟩ = L⁻¹ Σ_{k < L}` -/

/-- Average of a complex function over `Fin L`. -/
private def avgS (L : ℕ) (f : Fin L → ℂ) : ℂ := (L : ℂ)⁻¹ * ∑ k, f k

/-- Average of a real function over `Fin L`. -/
private def avgSR (L : ℕ) (f : Fin L → ℝ) : ℝ := (L : ℝ)⁻¹ * ∑ k, f k

private lemma avgSR_const {L : ℕ} (hL : 1 ≤ L) (c : ℝ) : avgSR L (fun _ => c) = c := by
  have : (L : ℝ) ≠ 0 := by positivity
  unfold avgSR
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

private lemma avgSR_mono {L : ℕ} {f h : Fin L → ℝ} (hle : ∀ k, f k ≤ h k) :
    avgSR L f ≤ avgSR L h := by
  unfold avgSR
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hle k) (by positivity)

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

private lemma norm_avgS_le_const {L : ℕ} (hL : 1 ≤ L) {f : Fin L → ℂ} {C : ℝ}
    (h : ∀ k, ‖f k‖ ≤ C) : ‖avgS L f‖ ≤ C := by
  have hL' : (0 : ℝ) < L := by positivity
  unfold avgS
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h1 : ‖∑ k, f k‖ ≤ L * C := by
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul Finset.univ (fun k => ‖f k‖) C (fun k _ => h k)
    simpa using this
  calc (L : ℝ)⁻¹ * ‖∑ k, f k‖ ≤ (L : ℝ)⁻¹ * (L * C) := by gcongr
    _ = C := by field_simp

private lemma norm_avgS_le {L : ℕ} (f : Fin L → ℂ) :
    ‖avgS L f‖ ≤ avgSR L (fun k => ‖f k‖) := by
  unfold avgS avgSR
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  gcongr
  exact norm_sum_le _ _

private lemma im_avgS {L : ℕ} (f : Fin L → ℂ) :
    (avgS L f).im = avgSR L (fun k => (f k).im) := by
  unfold avgS avgSR
  rw [show (L : ℂ)⁻¹ = (((L : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul,
    Complex.im_sum]

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

private lemma norm_resL_le (b : ℝ) (L : ℕ) {w : ℂ} (hw : 0 < w.im) (k : Fin L) :
    ‖resL b L w k‖ ≤ w.im⁻¹ := by
  unfold resL
  rw [norm_inv]
  apply inv_anti₀ hw
  calc w.im = |(((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ) - w).im| := by
        simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hw]
    _ ≤ ‖((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ) - w‖ := Complex.abs_im_le_norm _

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

private lemma norm_resL_ge (b : ℝ) (L : ℕ) {w : ℂ} (hw : 0 < w.im) (k : Fin L) :
    (2 * |b| + ‖w‖)⁻¹ ≤ ‖resL b L w k‖ := by
  unfold resL
  rw [norm_inv]
  apply inv_anti₀ (norm_pos_iff.mpr (resL_base_ne hw k))
  calc ‖((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ) - w‖
      ≤ ‖((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ)‖ + ‖w‖ := norm_sub_le _ _
    _ ≤ 2 * |b| + ‖w‖ := by
        gcongr
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
        have := Real.abs_cos_le_one (2 * π * k / L)
        have := abs_nonneg b
        norm_num
        nlinarith

/-- `⟨|R_w|²⟩`. -/
private def nsqL (b : ℝ) (L : ℕ) (w : ℂ) : ℝ := avgSR L (fun k => ‖resL b L w k‖ ^ 2)

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

private lemma norm_freeTL_le (b : ℝ) {L : ℕ} (hL : 1 ≤ L) {w : ℂ} (hw : 0 < w.im) :
    ‖freeTL b L w‖ ≤ w.im⁻¹ :=
  norm_avgS_le_const hL (norm_resL_le b L hw)

private lemma nsqL_ge (b : ℝ) {L : ℕ} (hL : 1 ≤ L) {w : ℂ} (hw : 0 < w.im) :
    ((2 * |b| + ‖w‖) ^ 2)⁻¹ ≤ nsqL b L w := by
  have hpos : 0 < 2 * |b| + ‖w‖ := by
    have : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw)
    linarith [abs_nonneg b]
  calc ((2 * |b| + ‖w‖) ^ 2)⁻¹ = avgSR L (fun _ => ((2 * |b| + ‖w‖) ^ 2)⁻¹) :=
        (avgSR_const hL _).symm
    _ ≤ nsqL b L w := by
      apply avgSR_mono
      intro k
      rw [← inv_pow]
      exact pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) (norm_resL_ge b L hw k) 2

private lemma nsqL_pos (b : ℝ) {L : ℕ} (hL : 1 ≤ L) {w : ℂ} (hw : 0 < w.im) : 0 < nsqL b L w := by
  have hpos : 0 < 2 * |b| + ‖w‖ := by
    have : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw)
    linarith [abs_nonneg b]
  exact lt_of_lt_of_le (inv_pos.mpr (pow_pos hpos 2)) (nsqL_ge b hL hw)

private lemma norm_avg_resres_le (b : ℝ) {L : ℕ} (hL : 1 ≤ L) {w w' : ℂ} (hw : 0 < w.im)
    (hw' : 0 < w'.im) :
    ‖avgS L (fun k => resL b L w k * resL b L w' k)‖ ≤ w.im⁻¹ * w'.im⁻¹ :=
  norm_avgS_le_const hL (fun k => by
    rw [norm_mul]
    exact mul_le_mul (norm_resL_le b L hw k) (norm_resL_le b L hw' k) (norm_nonneg _)
      (inv_nonneg.mpr hw.le))

private lemma cs_resres (b : ℝ) (L : ℕ) (w w' : ℂ) :
    ‖avgS L (fun k => resL b L w k * resL b L w' k)‖ ^ 2 ≤ nsqL b L w * nsqL b L w' :=
  avg_cs _ _

/-! ### The parameters `γ_g` and `b = g / max{1,g}` -/

private lemma max_one_pos' (g : ℝ) : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)

private lemma gammaG_pos' (g : ℝ) : 0 < gammaG g := by
  have := max_one_pos' g
  unfold gammaG
  positivity

private lemma gammaG_le_one' (g : ℝ) : gammaG g ≤ 1 := by
  unfold gammaG
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_max_left _ _))

private lemma abs_hopB_le_one' {g : ℝ} (hg : 0 ≤ g) : |hopB g| ≤ 1 := by
  unfold hopB
  rw [abs_of_nonneg (div_nonneg hg (max_one_pos' g).le)]
  exact div_le_one_of_le₀ (le_max_right _ _) (max_one_pos' g).le

/-! ### The right side of (5.2) [fo:eq:dyson-family] as a map on `ℂ_+` -/

private lemma im_shift' (g : ℝ) (z u : ℂ) :
    (z + gammaG g * u).im = z.im + gammaG g * u.im := by
  simp

private lemma im_shift_pos' (g : ℝ) {z u : ℂ} (hz : 0 < z.im) (hu : 0 ≤ u.im) :
    0 < (z + gammaG g * u).im := by
  rw [im_shift']
  have := gammaG_pos' g
  positivity

/-- Ward identity for the right side of (5.2) [fo:eq:dyson-family]:
`Im Φ(u) = (Im z + γ Im u) ⟨|R|²⟩`. -/
private lemma dysonL_im_eq (g : ℝ) (L : ℕ) (z u : ℂ) :
    (dysonRHSL g L z u).im = (z.im + gammaG g * u.im) * nsqL (hopB g) L (z + gammaG g * u) := by
  unfold dysonRHSL
  rw [im_freeTL, im_shift']

private lemma dysonL_im_pos (g : ℝ) {L : ℕ} (hL : 1 ≤ L) {z u : ℂ} (hz : 0 < z.im)
    (hu : 0 ≤ u.im) : 0 < (dysonRHSL g L z u).im := by
  rw [dysonL_im_eq]
  exact mul_pos (by rw [← im_shift']; exact im_shift_pos' g hz hu)
    (nsqL_pos _ hL (im_shift_pos' g hz hu))

private lemma dysonL_norm_le (g : ℝ) {L : ℕ} (hL : 1 ≤ L) {z u : ℂ} (hz : 0 < z.im)
    (hu : 0 ≤ u.im) : ‖dysonRHSL g L z u‖ ≤ z.im⁻¹ := by
  refine (norm_freeTL_le _ hL (im_shift_pos' g hz hu)).trans (inv_anti₀ hz ?_)
  rw [im_shift']
  have := gammaG_pos' g
  nlinarith

private lemma dysonL_im_ge (g : ℝ) (hg : 0 ≤ g) {L : ℕ} (hL : 1 ≤ L) {z u : ℂ} (hz : 0 < z.im)
    (hu : 0 ≤ u.im) :
    z.im * ((2 + ‖z‖ + ‖u‖) ^ 2)⁻¹ ≤ (dysonRHSL g L z u).im := by
  have hw := im_shift_pos' g hz hu
  rw [dysonL_im_eq]
  have hγ := gammaG_pos' g
  have hγ1 := gammaG_le_one' g
  have h1 := nsqL_ge (hopB g) hL hw
  have h2 : 2 * |hopB g| + ‖z + gammaG g * u‖ ≤ 2 + ‖z‖ + ‖u‖ := by
    have hb := abs_hopB_le_one' hg
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
  have h4 : 0 ≤ nsqL (hopB g) L (z + gammaG g * u) := (nsqL_pos _ hL hw).le
  have h5 : 0 ≤ gammaG g * u.im := by positivity
  calc z.im * ((2 + ‖z‖ + ‖u‖) ^ 2)⁻¹ ≤ z.im * nsqL (hopB g) L (z + gammaG g * u) :=
        mul_le_mul_of_nonneg_left (h3.trans h1) hz.le
    _ ≤ (z.im + gammaG g * u.im) * nsqL (hopB g) L (z + gammaG g * u) := by
        gcongr; linarith

/-- Contraction estimate for the right side of (5.2) [fo:eq:dyson-family]:
`|Φu - Φv|² (Im z + γ Im u)(Im z + γ Im v) ≤ γ² |u - v|² Im Φu Im Φv`. -/
private lemma dysonL_contr (g : ℝ) (L : ℕ) {z u v : ℂ} (hz : 0 < z.im) (hu : 0 ≤ u.im)
    (hv : 0 ≤ v.im) :
    ‖dysonRHSL g L z u - dysonRHSL g L z v‖ ^ 2 *
        ((z.im + gammaG g * u.im) * (z.im + gammaG g * v.im)) ≤
      gammaG g ^ 2 * ‖u - v‖ ^ 2 * ((dysonRHSL g L z u).im * (dysonRHSL g L z v).im) := by
  have hwu := im_shift_pos' g hz hu
  have hwv := im_shift_pos' g hz hv
  rw [dysonL_im_eq, dysonL_im_eq]
  unfold dysonRHSL
  rw [freeTL_sub_freeTL _ L hwu hwv]
  have hcs := cs_resres (hopB g) L (z + gammaG g * u) (z + gammaG g * v)
  have e : z + gammaG g * u - (z + gammaG g * v) = (gammaG g : ℂ) * (u - v) := by ring
  rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (gammaG_pos' g).le]
  rw [← im_shift', ← im_shift']
  have h1 : 0 ≤ (z + gammaG g * u).im * (z + gammaG g * v).im := by positivity
  have h2 : 0 ≤ gammaG g ^ 2 * ‖u - v‖ ^ 2 := by positivity
  calc (gammaG g * ‖u - v‖ * ‖avgS L fun k => resL (hopB g) L (z + gammaG g * u) k *
          resL (hopB g) L (z + gammaG g * v) k‖) ^ 2 *
        ((z + gammaG g * u).im * (z + gammaG g * v).im)
      = gammaG g ^ 2 * ‖u - v‖ ^ 2 * ‖avgS L fun k => resL (hopB g) L (z + gammaG g * u) k *
          resL (hopB g) L (z + gammaG g * v) k‖ ^ 2 *
        ((z + gammaG g * u).im * (z + gammaG g * v).im) := by ring
    _ ≤ gammaG g ^ 2 * ‖u - v‖ ^ 2 *
          (nsqL (hopB g) L (z + gammaG g * u) * nsqL (hopB g) L (z + gammaG g * v)) *
        ((z + gammaG g * u).im * (z + gammaG g * v).im) := by gcongr
    _ = _ := by ring

/-- Lipschitz bound `|Φu - Φv| ≤ (Im z)⁻² |u - v|` on the closed upper half-plane. -/
private lemma dysonL_lip (g : ℝ) {L : ℕ} (hL : 1 ≤ L) {z u v : ℂ} (hz : 0 < z.im)
    (hu : 0 ≤ u.im) (hv : 0 ≤ v.im) :
    ‖dysonRHSL g L z u - dysonRHSL g L z v‖ ≤ z.im⁻¹ ^ 2 * ‖u - v‖ := by
  have hwu := im_shift_pos' g hz hu
  have hwv := im_shift_pos' g hz hv
  have hγ := gammaG_pos' g
  have hγ1 := gammaG_le_one' g
  unfold dysonRHSL
  rw [freeTL_sub_freeTL _ L hwu hwv]
  have e : z + gammaG g * u - (z + gammaG g * v) = (gammaG g : ℂ) * (u - v) := by ring
  rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le]
  have h1 := norm_avg_resres_le (hopB g) hL hwu hwv
  have h2 : (z + gammaG g * u).im⁻¹ ≤ z.im⁻¹ :=
    inv_anti₀ hz (by rw [im_shift']; nlinarith)
  have h3 : (z + gammaG g * v).im⁻¹ ≤ z.im⁻¹ :=
    inv_anti₀ hz (by rw [im_shift']; nlinarith)
  have h4 : ‖avgS L fun k => resL (hopB g) L (z + gammaG g * u) k *
      resL (hopB g) L (z + gammaG g * v) k‖ ≤ z.im⁻¹ ^ 2 := by
    refine h1.trans ?_
    rw [sq]
    exact mul_le_mul h2 h3 (inv_nonneg.mpr hwv.le) (inv_nonneg.mpr hz.le)
  have h5 : 0 ≤ ‖u - v‖ := norm_nonneg _
  calc gammaG g * ‖u - v‖ * ‖avgS L fun k => resL (hopB g) L (z + gammaG g * u) k *
        resL (hopB g) L (z + gammaG g * v) k‖
      ≤ 1 * ‖u - v‖ * z.im⁻¹ ^ 2 := by gcongr
    _ = z.im⁻¹ ^ 2 * ‖u - v‖ := by ring

/-- Existence of a solution of (5.2) [fo:eq:dyson-family] in `ℂ_+` by fixed-point iteration from
`u₀ = i`. -/
private lemma dysonL_exists (g : ℝ) (hg : 0 ≤ g) {L : ℕ} (hL : 1 ≤ L) (z : ℂ) (hz : 0 < z.im) :
    ∃ u : ℂ, 0 < u.im ∧ u = dysonRHSL g L z u := by
  set Φ : ℂ → ℂ := fun u => dysonRHSL g L z u with hΦ
  set η := z.im with hη
  set γ := gammaG g with hγdef
  have hγ : 0 < γ := gammaG_pos' g
  have hγ1 : γ ≤ 1 := gammaG_le_one' g
  set u : ℕ → ℂ := fun n => Φ^[n] I with hu
  have hsucc : ∀ n, u (n + 1) = Φ (u n) := fun n => Function.iterate_succ_apply' Φ n I
  have him : ∀ n, 0 < (u n).im := by
    intro n
    induction n with
    | zero => simp [u]
    | succ n ih => rw [hsucc]; exact dysonL_im_pos g hL hz ih.le
  set v : ℕ → ℂ := fun n => u (n + 1) with hv
  have hvs : ∀ n, v (n + 1) = Φ (v n) := fun n => hsucc (n + 1)
  have hvim : ∀ n, 0 < (v n).im := fun n => him (n + 1)
  have hvnorm : ∀ n, ‖v n‖ ≤ η⁻¹ := fun n => by
    change ‖u (n + 1)‖ ≤ η⁻¹
    rw [hsucc]; exact dysonL_norm_le g hL hz (him n).le
  have hvimle : ∀ n, (v n).im ≤ η⁻¹ := fun n =>
    (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans (hvnorm n))
  -- lower bound on the imaginary parts
  set c₀ := η * ((2 + ‖z‖ + η⁻¹) ^ 2)⁻¹ with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  have hvlb : ∀ n, c₀ ≤ (v (n + 1)).im := by
    intro n
    rw [hvs]
    refine le_trans ?_ (dysonL_im_ge g hg hL hz (hvim n).le)
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
    have hc := dysonL_contr g L hz (hvim (n + 1)).le (hvim n).le
    have hvs' : ∀ k, v (k + 1) = dysonRHSL g L z (v k) := hvs
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
      (fun n => dysonL_lip g hL hz (hvim n).le hstar0.le) h0
  have hfix : ustar = Φ ustar := by
    refine tendsto_nhds_unique hlim1 ?_
    simpa only [hvs] using hlim2
  exact ⟨ustar, hstar0, hfix⟩

/-- Uniqueness of the solution of (5.2) [fo:eq:dyson-family] in `ℂ_+`, by the contraction estimate.
-/
private lemma dysonL_unique' (g : ℝ) (L : ℕ) {z u v : ℂ} (hz : 0 < z.im) (hu : 0 < u.im)
    (hv : 0 < v.im) (hu' : u = dysonRHSL g L z u) (hv' : v = dysonRHSL g L z v) : u = v := by
  have hc := dysonL_contr g L hz hu.le hv.le
  rw [← hu', ← hv'] at hc
  have hγ := gammaG_pos' g
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

theorem dysonL_existsUnique (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 1 ≤ L) (z : ℂ) (hz : 0 < z.im) :
    ∃! u : ℂ, 0 < u.im ∧ u = dysonRHSL g L z u := by
  obtain ⟨u, hu, hfix⟩ := dysonL_exists g hg hL z hz
  exact ⟨u, ⟨hu, hfix⟩, fun v ⟨hv, hvfix⟩ => dysonL_unique' g L hz hv hu hvfix hfix⟩

theorem mDysonL_spec (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 1 ≤ L) (z : ℂ) (hz : 0 < z.im) :
    0 < (mDysonL g L z).im ∧ mDysonL g L z = dysonRHSL g L z (mDysonL g L z) := by
  have h := dysonL_existsUnique g hg L hL z hz
  have e : mDysonL g L z = h.exists.choose := by
    unfold mDysonL
    split_ifs
    rfl
  rw [e]
  exact h.exists.choose_spec

theorem mDysonL_unique (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 1 ≤ L) (z : ℂ) (hz : 0 < z.im)
    (u : ℂ) (hu : 0 < u.im) (h : u = dysonRHSL g L z u) : u = mDysonL g L z :=
  (dysonL_existsUnique g hg L hL z hz).unique ⟨hu, h⟩ (mDysonL_spec g hg L hL z hz)

/-! ### Holomorphy of `m_{g,L}` on `ℂ_+` -/

private lemma mDysonL_norm_le_inv_im (g : ℝ) (hg : 0 ≤ g) {L : ℕ} (hL : 1 ≤ L) (z : ℂ)
    (hz : 0 < z.im) : ‖mDysonL g L z‖ ≤ z.im⁻¹ := by
  obtain ⟨hm, hfix⟩ := mDysonL_spec g hg L hL z hz
  calc ‖mDysonL g L z‖ = ‖dysonRHSL g L z (mDysonL g L z)‖ := by rw [← hfix]
    _ ≤ z.im⁻¹ := dysonL_norm_le g hL hz hm.le

private lemma continuousAt_of_lip' {f : ℂ → ℂ} {z : ℂ} {K : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ‖f z' - f z‖ ≤ K * ‖z' - z‖) : ContinuousAt f z := by
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun z' => K * ‖z' - z‖) (𝓝 z) (𝓝 0) := by
    have hc : Continuous fun z' : ℂ => K * ‖z' - z‖ := by fun_prop
    simpa using hc.tendsto z
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) h h0

/-- `⟨R²⟩` at the solution of (5.2) [fo:eq:dyson-family], with
`R_k = (2b cos(2πk/L) - z - γ m_{g,L}(z))⁻¹`. -/
private def selfP (g : ℝ) (L : ℕ) (z : ℂ) : ℂ :=
  avgS L (fun k => resL (hopB g) L (z + gammaG g * mDysonL g L z) k *
    resL (hopB g) L (z + gammaG g * mDysonL g L z) k)

/-- `γ ⟨|R|²⟩ (1 + (Im z)²) ≤ 1` at the solution of (5.2) [fo:eq:dyson-family]. -/
private lemma thetaL_le (g : ℝ) (hg : 0 ≤ g) {L : ℕ} (hL : 1 ≤ L) {z : ℂ} (hz : 0 < z.im) :
    gammaG g * nsqL (hopB g) L (z + gammaG g * mDysonL g L z) * (1 + z.im ^ 2) ≤ 1 := by
  obtain ⟨hm, hfix⟩ := mDysonL_spec g hg L hL z hz
  have him := dysonL_im_eq g L z (mDysonL g L z)
  rw [← hfix] at him
  have hn := mDysonL_norm_le_inv_im g hg hL z hz
  have hγ := gammaG_pos' g
  have hγ1 := gammaG_le_one' g
  have hy : (mDysonL g L z).im * z.im ≤ 1 := by
    have h1 := (le_abs_self (mDysonL g L z).im).trans ((Complex.abs_im_le_norm _).trans hn)
    have h2 := mul_le_mul_of_nonneg_right h1 hz.le
    rwa [inv_mul_cancel₀ hz.ne'] at h2
  have hpos : 0 < z.im + gammaG g * (mDysonL g L z).im := by positivity
  have e : (z.im + gammaG g * (mDysonL g L z).im) *
      (gammaG g * nsqL (hopB g) L (z + gammaG g * mDysonL g L z) * (1 + z.im ^ 2)) =
      gammaG g * (mDysonL g L z).im * (1 + z.im ^ 2) := by
    linear_combination (-(gammaG g) * (1 + z.im ^ 2)) * him
  have key : (z.im + gammaG g * (mDysonL g L z).im) *
      (gammaG g * nsqL (hopB g) L (z + gammaG g * mDysonL g L z) * (1 + z.im ^ 2)) ≤
      (z.im + gammaG g * (mDysonL g L z).im) * 1 := by
    rw [e]
    have h1 : gammaG g * ((mDysonL g L z).im * z.im) ≤ 1 := by nlinarith
    nlinarith
  exact le_of_mul_le_mul_left key hpos

private lemma mDysonL_hasDerivAt (g : ℝ) (hg : 0 ≤ g) {L : ℕ} (hL : 1 ≤ L) {z : ℂ}
    (hz : 0 < z.im) :
    HasDerivAt (mDysonL g L) (selfP g L z / (1 - gammaG g * selfP g L z)) z := by
  set η := z.im with hη
  set γ := gammaG g with hγdef
  set b := hopB g with hb
  have hγ : 0 < γ := gammaG_pos' g
  have hγ1 : γ ≤ 1 := gammaG_le_one' g
  set W : ℂ → ℂ := fun z' => z' + (γ : ℂ) * mDysonL g L z' with hW
  have hWim : ∀ z', 0 < z'.im → z'.im ≤ (W z').im ∧ 0 < (W z').im := by
    intro z' hz'
    have hm := (mDysonL_spec g hg L hL z' hz').1
    have e : (W z').im = z'.im + γ * (mDysonL g L z').im := im_shift' g z' _
    have : 0 < γ * (mDysonL g L z').im := by positivity
    constructor <;> linarith
  have hfixW : ∀ z', 0 < z'.im → mDysonL g L z' = freeTL b L (W z') := fun z' hz' =>
    (mDysonL_spec g hg L hL z' hz').2
  set P : ℂ → ℂ := fun z' => avgS L (fun k => resL b L (W z') k * resL b L (W z) k) with hP
  have hWz := hWim z hz
  have hid : ∀ z', 0 < z'.im →
      (mDysonL g L z' - mDysonL g L z) * (1 - γ * P z') = (z' - z) * P z' := by
    intro z' hz'
    have h1 : mDysonL g L z' - mDysonL g L z = (W z' - W z) * P z' := by
      rw [hfixW z' hz', hfixW z hz]
      exact freeTL_sub_freeTL b L (hWim z' hz').2 hWz.2
    have h2 : W z' - W z = (z' - z) + γ * (mDysonL g L z' - mDysonL g L z) := by
      simp only [hW]; ring
    rw [h2] at h1
    linear_combination h1
  set ρ := (1 + η ^ 2 / 4)⁻¹ with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ (by have := sq_pos_of_pos hz; linarith)
  have hθz := thetaL_le g hg hL hz
  have hgP : ∀ z', η / 2 ≤ z'.im → ‖(γ : ℂ) * P z'‖ ≤ ρ := by
    intro z' hz2
    have hz' : 0 < z'.im := by linarith
    have hθ' := thetaL_le g hg hL hz'
    have hcs := cs_resres b L (W z') (W z)
    have hN'0 := (nsqL_pos b hL (hWim z' hz').2).le
    have hN0 := (nsqL_pos b hL hWz.2).le
    have hA : γ * nsqL b L (W z') ≤ ρ := by
      rw [hρ, ← one_div, le_div_iff₀ (by positivity)]
      have : η ^ 2 / 4 ≤ z'.im ^ 2 := by nlinarith
      have h0 : 0 ≤ γ * nsqL b L (W z') := by positivity
      calc γ * nsqL b L (W z') * (1 + η ^ 2 / 4)
          ≤ γ * nsqL b L (W z') * (1 + z'.im ^ 2) := by gcongr
        _ ≤ 1 := hθ'
    have hB : γ * nsqL b L (W z) ≤ ρ := by
      rw [hρ, ← one_div, le_div_iff₀ (by positivity)]
      have : η ^ 2 / 4 ≤ η ^ 2 := by nlinarith
      have h0 : 0 ≤ γ * nsqL b L (W z) := by positivity
      calc γ * nsqL b L (W z) * (1 + η ^ 2 / 4) ≤ γ * nsqL b L (W z) * (1 + η ^ 2) := by gcongr
        _ ≤ 1 := hθz
    have hsq : ‖(γ : ℂ) * P z'‖ ^ 2 ≤ ρ ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le, mul_pow]
      calc γ ^ 2 * ‖P z'‖ ^ 2 ≤ γ ^ 2 * (nsqL b L (W z') * nsqL b L (W z)) := by gcongr
        _ = (γ * nsqL b L (W z')) * (γ * nsqL b L (W z)) := by ring
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
    exact (norm_avg_resres_le b hL (hWim z' hz').2 hWz.2).trans
      (mul_le_mul (hinv' z' hz2) hinv (inv_nonneg.mpr hWz.2.le) (by positivity))
  set K₁ := 2 / η * η⁻¹ / (1 - ρ) with hK₁
  have h1ρ : 0 < 1 - ρ := by linarith
  have hlipm : ∀ z', η / 2 ≤ z'.im → ‖mDysonL g L z' - mDysonL g L z‖ ≤ K₁ * ‖z' - z‖ := by
    intro z' hz2
    have hz' : 0 < z'.im := by linarith
    have h := congrArg norm (hid z' hz')
    rw [norm_mul, norm_mul] at h
    have h2 : ‖mDysonL g L z' - mDysonL g L z‖ * (1 - ρ) ≤ ‖z' - z‖ * (2 / η * η⁻¹) :=
      calc ‖mDysonL g L z' - mDysonL g L z‖ * (1 - ρ)
          ≤ ‖mDysonL g L z' - mDysonL g L z‖ * ‖1 - (γ : ℂ) * P z'‖ := by gcongr; exact hden z' hz2
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
    have e : P z' - P z = avgS L (fun k => (W z' - W z) *
        (resL b L (W z') k * resL b L (W z) k * resL b L (W z) k)) := by
      simp only [hP]
      rw [← avgS_sub]
      congr 1
      funext k
      rw [← sub_mul, resL_sub_resL b L hW'.2 hWz.2 k]
      ring
    have hWd : ‖W z' - W z‖ ≤ (1 + γ * K₁) * ‖z' - z‖ := by
      have e2 : W z' - W z = (z' - z) + γ * (mDysonL g L z' - mDysonL g L z) := by
        simp only [hW]; ring
      rw [e2]
      calc ‖(z' - z) + γ * (mDysonL g L z' - mDysonL g L z)‖
          ≤ ‖z' - z‖ + ‖(γ : ℂ) * (mDysonL g L z' - mDysonL g L z)‖ := norm_add_le _ _
        _ = ‖z' - z‖ + γ * ‖mDysonL g L z' - mDysonL g L z‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le]
        _ ≤ ‖z' - z‖ + γ * (K₁ * ‖z' - z‖) := by gcongr; exact hlipm z' hz2
        _ = (1 + γ * K₁) * ‖z' - z‖ := by ring
    rw [e]
    apply norm_avgS_le_const hL
    intro k
    have hr1 := (norm_resL_le b L hW'.2 k).trans (hinv' z' hz2)
    have hr2 := (norm_resL_le b L hWz.2 k).trans hinv
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖W z' - W z‖ * (‖resL b L (W z') k‖ * ‖resL b L (W z) k‖ * ‖resL b L (W z) k‖)
        ≤ ((1 + γ * K₁) * ‖z' - z‖) * (2 / η * η⁻¹ * η⁻¹) := by gcongr
      _ = K₂ * ‖z' - z‖ := by rw [hK₂]; ring
  have hev : ∀ᶠ z' in 𝓝 z, η / 2 < z'.im :=
    (Complex.continuous_im.tendsto z).eventually (lt_mem_nhds (by linarith))
  have hPc : ContinuousAt P z := continuousAt_of_lip' (hev.mono fun z' h => hlipP z' h.le)
  have hden0 : (1 : ℂ) - γ * P z ≠ 0 := by
    intro h0
    have := hden z (by linarith)
    rw [h0, norm_zero] at this
    linarith
  have hFc : ContinuousAt (fun z' => P z' / (1 - γ * P z')) z :=
    hPc.div (continuousAt_const.sub (continuousAt_const.mul hPc)) hden0
  change HasDerivAt (mDysonL g L) (P z / (1 - γ * P z)) z
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

theorem mDysonL_differentiableOn (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 1 ≤ L) :
    DifferentiableOn ℂ (mDysonL g L) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (mDysonL_hasDerivAt g hg hL (z := z) hz).differentiableAt.differentiableWithinAt

end LSBA
