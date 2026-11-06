import LSBA.Kernel.Comparison

/-!
# The Dyson matrix on vertical lines

The Dyson matrix at the points `x + iy` above the characteristic point, at large coupling and up
to normalized heights `y/γ_g ≤ W^δ`: existence of the root in the upper half-plane, the bounds
`|m| ≤ C` and `Im m ≥ c`, the entry and covariance-weighted row bounds (6.13)
[gc:eq:residual-row-bounds] and the derivative bound in `log y`, as a perturbation of the bulk
free resolvent (Lemma 6.4 [da:lem:positive-height] beyond its height range).
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

private lemma vt_hopB_nonneg {g : ℝ} (hg : 0 ≤ g) : 0 ≤ hopB g :=
  div_nonneg hg (le_trans zero_le_one (le_max_left _ _))

private lemma vt_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold gammaG
  positivity

private lemma vt_hopB_of_one_le {g : ℝ} (hg : 1 ≤ g) : hopB g = 1 := by
  unfold hopB; rw [max_eq_right hg, div_self (by linarith)]

private lemma vt_gammaG_of_one_le {g : ℝ} (hg : 1 ≤ g) : gammaG g = (g ^ 2)⁻¹ := by
  unfold gammaG; rw [max_eq_right hg]

/-- The characteristic point `z_u` is `Re z_u + iη_u`. -/
private lemma vt_zChar_eq (g E : ℝ) (m : ℂ) (u : ℝ) :
    (((zChar g E m u).re : ℝ) : ℂ) +
      ((gammaG g * (etaChar g m u / gammaG g) : ℝ) : ℂ) * I = zChar g E m u := by
  have hγ := vt_gammaG_pos g
  apply Complex.ext
  · simp [zChar]
  · simp only [zChar, etaChar, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero,
      zero_mul, Complex.add_re, Complex.mul_re, sub_zero]
    field_simp

/-- (5.27) [gc:eq:positive-dyson], last line: on the characteristic, `M_{B,u}(z_u) = M_B(g, E)`
for every `0 ≤ u < 1` (the root `m(g, E)` solves the time-`u` equation at `z_u`). -/
theorem segMat_char (g E : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 3 ≤ L) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1) :
    segMat g L (zChar g E m u).re u (etaChar g m u / gammaG g) =
      dysonMat (hopB g) (gammaG g) L E m := by
  have hγ := vt_gammaG_pos g
  unfold segMat
  rw [vt_zChar_eq]
  have hsum : zChar g E m u + ((u * gammaG g : ℝ) : ℂ) * m = (E : ℂ) + (gammaG g : ℂ) * m := by
    unfold zChar
    push_cast
    ring
  rcases hu0.eq_or_lt with rfl | hu0'
  · unfold dysonMat
    simp only [zero_mul, Complex.ofReal_zero, add_zero, zChar, sub_zero, one_mul]
  · have hzim : 0 ≤ (zChar g E m u).im := by
      have : (zChar g E m u).im = (1 - u) * gammaG g * m.im := by
        simp [zChar]
      rw [this]
      have := hm.1
      have : 0 < 1 - u := by linarith
      positivity
    have hroot : IsDysonRootV (hopB g) (u * gammaG g) L (zChar g E m u) m := by
      refine ⟨hm.1, ?_⟩
      unfold dysonRHSV
      rw [hsum]
      exact hm.2
    rw [(mRootV_spec (hopB g) (u * gammaG g) (vt_hopB_nonneg hg) (by positivity) L hL _ hzim).2 m
      hroot]
    unfold dysonMat
    rw [hsum]

/-! ### Circulant invariance of the cycle resolvent -/

private lemma vt_adj_shift {L : ℕ} [NeZero L] (a i j : Fin L) :
    (j.val = (i.val + 1) % L) ↔ ((j + a).val = ((i + a).val + 1) % L) := by
  rw [Fin.val_add, Fin.val_add]
  have h1 : ((i.val + a.val) % L + 1) % L = (i.val + 1 + a.val) % L := by
    have := (Nat.mod_modEq (i.val + a.val) L).add_right 1
    unfold Nat.ModEq at this
    rw [this]
    congr 1
    ring
  rw [h1]
  constructor
  · intro h
    have : j.val ≡ i.val + 1 [MOD L] := by
      unfold Nat.ModEq
      rw [Nat.mod_eq_of_lt j.isLt]
      exact h
    exact this.add_right a.val
  · intro h
    have : j.val ≡ i.val + 1 [MOD L] := Nat.ModEq.add_right_cancel' a.val h
    unfold Nat.ModEq at this
    rw [Nat.mod_eq_of_lt j.isLt] at this
    exact this

private lemma vt_cycleAdj_shift {L : ℕ} [NeZero L] (a i j : Fin L) :
    cycleAdj L (i + a) (j + a) = cycleAdj L i j := by
  simp only [cycleAdj, Matrix.of_apply]
  rw [if_congr (vt_adj_shift a i j).symm rfl rfl, if_congr (vt_adj_shift a j i).symm rfl rfl]

private lemma vt_inv_shift {L : ℕ} [NeZero L] (b : ℝ) (w : ℂ) (a i j : Fin L) :
    (((b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹) (i + a) (j + a) =
      (((b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹) i j := by
  set N := ((b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ)) with hN
  have hsub : N.submatrix (Equiv.addRight a) (Equiv.addRight a) = N := by
    ext i j
    simp only [Matrix.submatrix_apply, Equiv.coe_addRight, hN, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, vt_cycleAdj_shift, add_left_inj, smul_eq_mul]
  have h := Matrix.inv_submatrix_equiv N (Equiv.addRight a) (Equiv.addRight a)
  rw [hsub] at h
  have h2 := congrFun (congrFun h i) j
  simpa using h2.symm

private lemma vt_inv_circ {L : ℕ} (hL : 3 ≤ L) (b : ℝ) (w : ℂ) (a c : Fin L) :
    (((b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹) a c =
      (((b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹) ⟨0, by omega⟩ (c - a) := by
  have : NeZero L := ⟨by omega⟩
  have h0 : (⟨0, by omega⟩ : Fin L) + a = a := by
    apply Fin.ext
    rw [Fin.val_add]
    simp [Nat.mod_eq_of_lt a.isLt]
  have := vt_inv_shift b w a ⟨0, by omega⟩ (c - a)
  rw [h0, sub_add_cancel] at this
  exact this

/-! ### The bulk free resolvent on the cycle -/

/-- At hopping `1`, `w = ρ(w) + ρ(w)⁻¹` with `ρ(w) ≠ 0`, (A.4) [da:eq:free-decay-factor]. -/
private lemma vt_rho_w {w : ℂ} (hw : 0 < w.im) :
    freeRho 1 w ≠ 0 ∧ w = freeRho 1 w + (freeRho 1 w)⁻¹ := by
  set s := freeS 1 w with hs
  have hs2 : s ^ 2 = w ^ 2 - 4 := by
    have := freeS_sq 1 w
    simpa using this
  have hsim : 0 < s.im := freeS_im_pos 1 w hw
  have hne : w + s ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.zero_im] at this
    linarith
  have hρ : freeRho 1 w = 2 / (w + s) := by
    unfold freeRho
    simp [hs]
  have hρ2 : freeRho 1 w = (w - s) / 2 := by
    rw [hρ, div_eq_div_iff hne two_ne_zero]
    linear_combination hs2
  have hρ0 : freeRho 1 w ≠ 0 := by
    rw [hρ]
    exact div_ne_zero two_ne_zero hne
  refine ⟨hρ0, ?_⟩
  have hinv : (freeRho 1 w)⁻¹ = (w + s) / 2 := by
    rw [hρ]
    field_simp
  rw [hinv, hρ2]
  ring

/-- Bounds on the decay factor at hopping `1`: `‖ρ‖ ≥ 1/(Im w + 3)` for `|Re w| ≤ 2` and
`Im w ‖ρ‖ ≤ 2(1 - ‖ρ‖)`. -/
private lemma vt_rho_bounds {w : ℂ} (hw : 0 < w.im) (hre : |w.re| ≤ 2) :
    1 / (w.im + 3) ≤ ‖freeRho 1 w‖ ∧ w.im * ‖freeRho 1 w‖ ≤ 2 * (1 - ‖freeRho 1 w‖) := by
  obtain ⟨hρ0, hρw⟩ := vt_rho_w hw
  set ρ := freeRho 1 w with hρ
  have hr1 : ‖ρ‖ < 1 := norm_freeRho_lt_one 1 w hw
  have hrpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  constructor
  · -- `‖ρ‖ = 2/‖w + s‖` and `‖w + s‖ ≤ 2 ‖w‖ + 2`
    set s := freeS 1 w with hs
    have hs2 : s ^ 2 = w ^ 2 - 4 := by
      have := freeS_sq 1 w
      simpa using this
    have hsim : 0 < s.im := freeS_im_pos 1 w hw
    have hne : w + s ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp only [Complex.add_im, Complex.zero_im] at this
      linarith
    have hρ' : ρ = 2 / (w + s) := by
      rw [hρ]
      unfold freeRho
      simp [hs]
    have hwn : ‖w‖ ≤ 2 + w.im := by
      have h1 := Complex.norm_le_abs_re_add_abs_im w
      rw [abs_of_pos hw] at h1
      linarith
    have hsn : ‖s‖ ≤ ‖w‖ + 2 := by
      have h1 : ‖s‖ ^ 2 ≤ (‖w‖ + 2) ^ 2 := by
        rw [← norm_pow, hs2]
        calc ‖w ^ 2 - 4‖ ≤ ‖w ^ 2‖ + ‖(4 : ℂ)‖ := norm_sub_le _ _
          _ = ‖w‖ ^ 2 + 4 := by simp [norm_pow]
          _ ≤ (‖w‖ + 2) ^ 2 := by nlinarith [norm_nonneg w]
      exact le_of_sq_le_sq h1 (by positivity)
    have hws : ‖w + s‖ ≤ 2 * (w.im + 3) := by
      calc ‖w + s‖ ≤ ‖w‖ + ‖s‖ := norm_add_le _ _
        _ ≤ 2 * (w.im + 3) := by linarith
    have hwsp : 0 < ‖w + s‖ := norm_pos_iff.mpr hne
    have hn : ‖ρ‖ = 2 / ‖w + s‖ := by
      rw [hρ', norm_div]
      simp
    rw [hn, div_le_div_iff₀ (by linarith) hwsp]
    nlinarith
  · -- `Im w = Im ρ - Im ρ/|ρ|²`
    have hN : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr hρ0
    have hNr : Complex.normSq ρ = ‖ρ‖ ^ 2 := by rw [Complex.sq_norm]
    have him : w.im * Complex.normSq ρ = -ρ.im * (1 - Complex.normSq ρ) := by
      have h1 := congrArg Complex.im hρw
      rw [Complex.add_im, Complex.inv_im] at h1
      rw [h1]
      field_simp
      ring
    have hq : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
    have hN1 : Complex.normSq ρ < 1 := by rw [hNr]; nlinarith
    have h2 : w.im * ‖ρ‖ ^ 2 ≤ ‖ρ‖ * (1 - ‖ρ‖ ^ 2) := by
      rw [← hNr, him]
      have : -ρ.im * (1 - Complex.normSq ρ) ≤ |ρ.im| * (1 - Complex.normSq ρ) := by
        apply mul_le_mul_of_nonneg_right (neg_le_abs _) (by linarith)
      rw [hNr] at this ⊢
      nlinarith [hNr]
    have h3 : w.im * ‖ρ‖ ≤ 1 - ‖ρ‖ ^ 2 := by
      have : ‖ρ‖ * (w.im * ‖ρ‖) ≤ ‖ρ‖ * (1 - ‖ρ‖ ^ 2) := by nlinarith
      exact le_of_mul_le_mul_left this hrpos
    nlinarith

private lemma vt_pow_half {r q : ℝ} (hr0 : 0 ≤ r) (hq0 : 0 ≤ q) (hq : q ≤ 1 - r) {L : ℕ}
    (hLq : 1 ≤ L * q) : r ^ L ≤ 1 / 2 := by
  have hq1 : q ≤ 1 := by linarith
  have h1 : r ^ L ≤ (1 - q) ^ L := pow_le_pow_left₀ hr0 (by linarith) L
  have h2 : 1 + (L : ℝ) * q ≤ (1 + q) ^ L := one_add_mul_le_pow (by linarith) L
  have h3 : (1 - q) ^ L * (1 + q) ^ L ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h4 : 0 ≤ (1 - q) ^ L := pow_nonneg (by linarith) L
  nlinarith

private lemma vt_geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (L : ℕ) :
    ∑ x ∈ Finset.range L, r ^ x ≤ 1 / (1 - r) := by
  have h := geom_sum_mul_neg r L
  have hpos : 0 < 1 - r := by linarith
  rw [le_div_iff₀ hpos]
  have : r ^ L ≥ 0 := pow_nonneg hr0 L
  linarith

private lemma vt_geom_rev_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (L : ℕ) :
    ∑ x ∈ Finset.range L, r ^ (L - x) ≤ 1 / (1 - r) := by
  have hA : ∑ x ∈ Finset.range L, r ^ (L - x) = r * ∑ x ∈ Finset.range L, r ^ x := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [← pow_succ']
    congr 1
    omega
  rw [hA]
  have h1 := vt_geom_le hr0 hr1 L
  have hpos : 0 < 1 - r := by linarith
  calc r * ∑ x ∈ Finset.range L, r ^ x ≤ 1 * (1 / (1 - r)) :=
        mul_le_mul hr1.le h1 (Finset.sum_nonneg fun _ _ => pow_nonneg hr0 _) zero_le_one
    _ = 1 / (1 - r) := one_mul _

/-- The free cycle resolvent `(A_L - w)⁻¹` at `|Re w| ≤ 2 - k` and `L min{Im w, 1} ≥ 8`: entries
at most `4/k` and absolute rows at most `32/(k Im w)`, from the row (A.5) [bl:eq:free]. -/
private lemma vt_free_bound {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) {L : ℕ} (hL : 3 ≤ L) {w : ℂ}
    (hre : |w.re| ≤ 2 - k) (him : 0 < w.im) (hLw : 8 ≤ L * min w.im 1) :
    (∀ a b : Fin L,
      ‖(((1 : ℝ) : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ a b‖ ≤ 4 / k) ∧
    ∀ a : Fin L,
      ∑ b, ‖(((1 : ℝ) : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ a b‖ ≤
        32 / (k * w.im) := by
  have : NeZero L := ⟨by omega⟩
  set η := w.im with hη
  set ρ := freeRho 1 w with hρ
  set r := ‖ρ‖ with hr
  have hr1 : r < 1 := norm_freeRho_lt_one 1 w him
  have hr0 : 0 ≤ r := norm_nonneg _
  obtain ⟨hrlow, hrup⟩ := vt_rho_bounds him (by linarith [abs_nonneg w.re])
  set q := min η 1 / 8 with hq
  have hq0 : 0 ≤ q := by
    have : 0 < min η 1 := lt_min him one_pos
    positivity
  have hq1 : q ≤ 1 - r := by
    have h1 : η / (2 * (η + 3)) ≤ η * r / 2 := by
      have : η * (1 / (η + 3)) ≤ η * r := mul_le_mul_of_nonneg_left hrlow him.le
      calc η / (2 * (η + 3)) = η * (1 / (η + 3)) / 2 := by field_simp
        _ ≤ η * r / 2 := by linarith
    have h2 : q ≤ η / (2 * (η + 3)) := by
      rcases le_total η 1 with h | h
      · rw [hq, min_eq_left h, div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith
      · rw [hq, min_eq_right h, div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith
    linarith
  have hLq : 1 ≤ L * q := by
    have : (L : ℝ) * q = L * min η 1 / 8 := by rw [hq]; ring
    rw [this]
    linarith
  have hrL : r ^ L ≤ 1 / 2 := vt_pow_half hr0 hq0 hq1 hLq
  -- the prefactor `f = -1/s`
  have hfeq := freeT_eq 1 w him
  set s := freeS 1 w with hs
  have hs2 : s ^ 2 = (w - 2) * (w + 2) := by
    have := freeS_sq 1 w
    simp only [Complex.ofReal_one] at this
    rw [this]
    ring
  have hsn : ‖s‖ ^ 2 = ‖w - 2‖ * ‖w + 2‖ := by rw [← norm_pow, hs2, norm_mul]
  have hwr1 : k ≤ ‖w - 2‖ := by
    have h1 := Complex.abs_re_le_norm (w - 2)
    have h2 : (w - 2).re = w.re - 2 := by simp
    have h3 := neg_le_abs (w - 2).re
    have h4 := (abs_le.mp hre).2
    rw [h2] at h1 h3
    linarith
  have hwr2 : k ≤ ‖w + 2‖ := by
    have h1 := Complex.abs_re_le_norm (w + 2)
    have h2 : (w + 2).re = w.re + 2 := by simp
    have h3 := le_abs_self (w + 2).re
    have h4 := (abs_le.mp hre).1
    rw [h2] at h1 h3
    linarith
  have hwi1 : η ≤ ‖w - 2‖ := by
    have h1 := Complex.abs_im_le_norm (w - 2)
    have h2 : (w - 2).im = η := by simp [hη]
    rw [h2, abs_of_pos him] at h1
    exact h1
  have hwi2 : η ≤ ‖w + 2‖ := by
    have h1 := Complex.abs_im_le_norm (w + 2)
    have h2 : (w + 2).im = η := by simp [hη]
    rw [h2, abs_of_pos him] at h1
    exact h1
  have hsk : k ≤ ‖s‖ := by
    have : k ^ 2 ≤ ‖s‖ ^ 2 := by
      rw [hsn, sq]
      exact mul_le_mul hwr1 hwr2 hk.le (le_trans hk.le hwr1)
    exact (pow_le_pow_iff_left₀ hk.le (norm_nonneg s) two_ne_zero).mp this
  have hsη : η ≤ ‖s‖ := by
    have : η ^ 2 ≤ ‖s‖ ^ 2 := by
      rw [hsn, sq]
      exact mul_le_mul hwi1 hwi2 him.le (le_trans him.le hwi1)
    exact (pow_le_pow_iff_left₀ him.le (norm_nonneg s) two_ne_zero).mp this
  have hspos : 0 < ‖s‖ := lt_of_lt_of_le hk hsk
  have hfn : ‖freeT 1 w‖ = ‖s‖⁻¹ := by rw [hfeq, norm_neg, norm_inv]
  have hfk : ‖freeT 1 w‖ ≤ 1 / k := by
    rw [hfn, one_div]
    exact inv_anti₀ hk hsk
  have hfη : ‖freeT 1 w‖ ≤ 1 / η := by
    rw [hfn, one_div]
    exact inv_anti₀ him hsη
  have hf0 : 0 ≤ ‖freeT 1 w‖ := norm_nonneg _
  -- the row `0`
  have hden : 1 / 2 ≤ ‖1 - ρ ^ L‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (ρ ^ L)
    rw [norm_one, norm_pow] at h1
    linarith
  have hrow : ∀ x : Fin L,
      ‖(((1 : ℝ) : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ ⟨0, by omega⟩ x‖ ≤
        2 * ‖freeT 1 w‖ * (r ^ x.val + r ^ (L - x.val)) := by
    intro x
    rw [freeRowCycle_eq 1 w him L hL x, norm_div, norm_mul]
    have hnum : ‖ρ ^ x.val + ρ ^ (L - x.val)‖ ≤ r ^ x.val + r ^ (L - x.val) := by
      refine (norm_add_le _ _).trans ?_
      simp only [norm_pow]
      exact le_rfl
    have hpos : 0 ≤ r ^ x.val + r ^ (L - x.val) := by positivity
    calc ‖freeT 1 w‖ * ‖ρ ^ x.val + ρ ^ (L - x.val)‖ / ‖1 - ρ ^ L‖
        ≤ ‖freeT 1 w‖ * (r ^ x.val + r ^ (L - x.val)) / (1 / 2) := by
          apply div_le_div₀ (by positivity) _ (by norm_num) hden
          exact mul_le_mul_of_nonneg_left hnum hf0
      _ = 2 * ‖freeT 1 w‖ * (r ^ x.val + r ^ (L - x.val)) := by ring
  have hr_le : ∀ n : ℕ, r ^ n ≤ 1 := fun n => pow_le_one₀ hr0 hr1.le
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · rw [vt_inv_circ hL 1 w a b]
    refine (hrow (b - a)).trans ?_
    have h1 := hr_le (b - a).val
    have h2 := hr_le (L - (b - a).val)
    calc 2 * ‖freeT 1 w‖ * (r ^ (b - a).val + r ^ (L - (b - a).val))
        ≤ 2 * ‖freeT 1 w‖ * 2 := by gcongr; linarith
      _ = 4 * ‖freeT 1 w‖ := by ring
      _ ≤ 4 * (1 / k) := by gcongr
      _ = 4 / k := by ring
  · have hsum0 : ∑ x : Fin L,
        ‖(((1 : ℝ) : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ ⟨0, by omega⟩ x‖ ≤
          4 * ‖freeT 1 w‖ / (1 - r) := by
      calc _ ≤ ∑ x : Fin L, 2 * ‖freeT 1 w‖ * (r ^ x.val + r ^ (L - x.val)) :=
            Finset.sum_le_sum fun x _ => hrow x
        _ = 2 * ‖freeT 1 w‖ * (∑ x ∈ Finset.range L, r ^ x +
              ∑ x ∈ Finset.range L, r ^ (L - x)) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
            congr 1
            rw [← Fin.sum_univ_eq_sum_range (fun x => r ^ x) L,
              ← Fin.sum_univ_eq_sum_range (fun x => r ^ (L - x)) L]
        _ ≤ 2 * ‖freeT 1 w‖ * (1 / (1 - r) + 1 / (1 - r)) := by
            gcongr
            · exact vt_geom_le hr0 hr1 L
            · exact vt_geom_rev_le hr0 hr1 L
        _ = 4 * ‖freeT 1 w‖ / (1 - r) := by ring
    have hsum : ∑ b,
        ‖(((1 : ℝ) : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ a b‖ =
        ∑ x : Fin L,
        ‖(((1 : ℝ) : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ ⟨0, by omega⟩ x‖ := by
      simp_rw [vt_inv_circ hL 1 w a]
      exact Fintype.sum_equiv (Equiv.subRight a) _ _ fun b => rfl
    rw [hsum]
    refine hsum0.trans ?_
    have hpos : 0 < 1 - r := by linarith
    rw [div_le_div_iff₀ hpos (by positivity)]
    rcases le_total η 1 with h | h
    · have hq' : η / 8 ≤ 1 - r := by rw [hq, min_eq_left h] at hq1; exact hq1
      have h1 : 4 * ‖freeT 1 w‖ * (k * η) ≤ 4 * (1 / k) * (k * η) := by gcongr
      have h2 : 4 * (1 / k) * (k * η) = 4 * η := by field_simp
      nlinarith
    · have hq' : 1 / 8 ≤ 1 - r := by rw [hq, min_eq_right h] at hq1; exact hq1
      have h1 : ‖freeT 1 w‖ * η ≤ 1 := by
        calc ‖freeT 1 w‖ * η ≤ 1 / η * η := by gcongr
          _ = 1 := by field_simp
      have h3 : 0 < k * η := by positivity
      nlinarith [mul_pos hk him]

/-! ### The Dyson matrix: symmetry, Ward identity, root -/

private lemma vt_cycleAdj_transpose (L : ℕ) : (cycleAdj L).transpose = cycleAdj L := by
  ext i j
  simp only [Matrix.transpose_apply, cycleAdj, Matrix.of_apply]
  rw [add_comm]

/-- `bA_L - w` is invertible for `Im w > 0`. -/
private lemma vt_cyc_isUnit (b : ℝ) (L : ℕ) {w : ℂ} (hw : 0 < w.im) :
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
private lemma vt_dysonMat_symm (b β : ℝ) (L : ℕ) (z m : ℂ) (i j : Fin L) :
    dysonMat b β L z m i j = dysonMat b β L z m j i := by
  have h : (dysonMat b β L z m).transpose = dysonMat b β L z m := by
    unfold dysonMat
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_smul, Matrix.transpose_one, vt_cycleAdj_transpose]
  conv_lhs => rw [← h]
  rfl

/-- Ward identity for an inverse `N` of `B` with `Bᴴ - B = (w - w̄) I`:
`Im N_aa = Im w · Σ_c |N_ac|²`. -/
private lemma vt_ward_of_inv {n : Type*} [Fintype n] [DecidableEq n] (B N : Matrix n n ℂ) (w : ℂ)
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

/-- Ward identity for the Dyson matrix: `Im M_aa = Im(z + βm) Σ_c |M_ac|²`. -/
private lemma vt_ward (b β : ℝ) (L : ℕ) (z m : ℂ) (hw : 0 < (z + β * m).im) (a : Fin L) :
    (dysonMat b β L z m a a).im = (z + β * m).im * ∑ c, ‖dysonMat b β L z m a c‖ ^ 2 := by
  refine vt_ward_of_inv ((b : ℂ) • cycleAdj L - (z + β * m) • (1 : Matrix (Fin L) (Fin L) ℂ))
    _ (z + β * m) (Matrix.mul_nonsing_inv _ (vt_cyc_isUnit b L hw)) ?_ a
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    (cycleAdj_isHermitian L).eq, Matrix.conjTranspose_one, sub_smul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  abel

/-- `Im f(w) > 0` for the finite cycle average at `Im w > 0`. -/
private lemma vt_im_freeTL_pos (b : ℝ) {L : ℕ} (hL : 1 ≤ L) {w : ℂ} (hw : 0 < w.im) :
    0 < (freeTL b L w).im := by
  unfold freeTL
  rw [show (L : ℂ)⁻¹ = (((L : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul,
    Complex.im_sum]
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  refine mul_pos (inv_pos.mpr hL') (Finset.sum_pos (fun k _ => ?_)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
  rw [Complex.inv_im]
  have hne : ((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ) - w ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at this
    linarith
  have hN : 0 < Complex.normSq (((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ) - w) :=
    Complex.normSq_pos.mpr hne
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  positivity

/-- The selected root exists and is a root, also at `β = 0`. -/
private lemma vt_root {b β : ℝ} (hb : 0 ≤ b) (hβ : 0 ≤ β) {L : ℕ} (hL : 3 ≤ L) {z : ℂ}
    (hz : 0 < z.im) : IsDysonRootV b β L z (mRootV b β L z) := by
  rcases hβ.eq_or_lt with rfl | hβ'
  · have hex : ∃ m, IsDysonRootV b 0 L z m :=
      ⟨freeTL b L z, vt_im_freeTL_pos b (by omega) hz, by simp [dysonRHSV]⟩
    have hsel : mRootV b 0 L z = hex.choose := by
      unfold mRootV
      split_ifs
      rfl
    rw [hsel]
    exact hex.choose_spec
  · exact (mRootV_spec b β hb hβ' L hL z hz.le).1 hz

/-! ### Holomorphy of the root and the height derivative -/

/-- Scaling `freeTL (cb) L (cw) = c⁻¹ freeTL b L w` for real `c ≠ 0`. -/
private lemma vt_freeTL_scale (b : ℝ) (L : ℕ) (w : ℂ) {c : ℝ} (hc : c ≠ 0) :
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

private lemma vt_root_scale {b β : ℝ} {L : ℕ} {z m : ℂ} (h : IsDysonRootV b β L z m) {c : ℝ}
    (hc : 0 < c) : IsDysonRootV (c * b) (c ^ 2 * β) L ((c : ℂ) * z) ((c : ℂ)⁻¹ * m) := by
  obtain ⟨hm, e⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]; positivity
  · unfold dysonRHSV at e ⊢
    have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have h1 : (c : ℂ) * z + ((c ^ 2 * β : ℝ) : ℂ) * ((c : ℂ)⁻¹ * m) =
        (c : ℂ) * (z + (β : ℂ) * m) := by
      push_cast; field_simp
    rw [h1, vt_freeTL_scale b L _ hc.ne', ← e]

/-- The root is the scaled finite-cycle solution, so it is holomorphic on `ℂ_+`. -/
private lemma vt_mRootV_diffAt {b a : ℝ} (hb : 0 ≤ b) (ha : 0 < a) {L : ℕ} (hL : 3 ≤ L)
    {z₀ : ℂ} (hz₀ : 0 < z₀.im) : DifferentiableAt ℂ (mRootV b a L) z₀ := by
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
    have h3 := vt_root_scale h2 (inv_pos.mpr hcpos)
    have e1 : c⁻¹ * (c * b) = b := by field_simp
    have e2 : c⁻¹ ^ 2 * (c ^ 2 * a) = a := by field_simp
    have e3 : ((c⁻¹ : ℝ) : ℂ) * ((c : ℂ) * z) = z := by
      have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
      push_cast; field_simp
    rw [e1, e2, e3, Complex.ofReal_inv, inv_inv] at h3
    exact (mRootV_spec b a hb ha L hL z hz.le).2 _ h3
  have hd : DifferentiableAt ℂ (fun z => (c : ℂ) * mDysonL G L ((c : ℂ) * z)) z₀ := by
    have hcz : 0 < ((c : ℂ) * z₀).im := by rw [Complex.im_ofReal_mul]; positivity
    have h1 : DifferentiableAt ℂ (mDysonL G L) ((c : ℂ) * z₀) :=
      (mDysonL_differentiableOn G hG0 L (by omega)).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hcz)
    exact (h1.comp z₀ (differentiableAt_id.const_mul _)).const_mul _
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz₀] with z hz
  exact key z hz

/-- Resolvent identity for `(bA_L - w)⁻¹`. -/
private lemma vt_cyc_resolvent (b : ℝ) (L : ℕ) {w₁ w₂ : ℂ} (h₁ : 0 < w₁.im) (h₂ : 0 < w₂.im) :
    ((b : ℂ) • cycleAdj L - w₁ • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ -
      ((b : ℂ) • cycleAdj L - w₂ • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ =
      (w₁ - w₂) • (((b : ℂ) • cycleAdj L - w₁ • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ *
        ((b : ℂ) • cycleAdj L - w₂ • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹) := by
  set B₁ := (b : ℂ) • cycleAdj L - w₁ • (1 : Matrix (Fin L) (Fin L) ℂ)
  set B₂ := (b : ℂ) • cycleAdj L - w₂ • (1 : Matrix (Fin L) (Fin L) ℂ)
  have hu₁ := vt_cyc_isUnit b L h₁
  have hu₂ := vt_cyc_isUnit b L h₂
  have e : B₂ - B₁ = (w₁ - w₂) • (1 : Matrix (Fin L) (Fin L) ℂ) := by
    simp only [B₁, B₂, sub_smul]; abel
  calc B₁⁻¹ - B₂⁻¹ = B₁⁻¹ * (B₂ * B₂⁻¹) - (B₁⁻¹ * B₁) * B₂⁻¹ := by
        rw [Matrix.mul_nonsing_inv _ hu₂, Matrix.nonsing_inv_mul _ hu₁, Matrix.mul_one,
          Matrix.one_mul]
    _ = B₁⁻¹ * (B₂ - B₁) * B₂⁻¹ := by noncomm_ring
    _ = _ := by rw [e, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- Carathéodory form of the derivative. -/
private lemma vt_hasDerivAt_of_factor {f h φ : ℝ → ℂ} {r₀ : ℝ} {h' : ℂ}
    (hh : HasDerivAt h h' r₀) (hφ : ContinuousAt φ r₀)
    (hf : ∀ᶠ r in 𝓝 r₀, f r - f r₀ = (h r - h r₀) * φ r) :
    HasDerivAt f (h' * φ r₀) r₀ := by
  rw [hasDerivAt_iff_tendsto_slope] at hh ⊢
  have hφ' : Tendsto φ (𝓝[≠] r₀) (𝓝 (φ r₀)) := hφ.tendsto.mono_left nhdsWithin_le_nhds
  refine (hh.mul hφ').congr' ?_
  filter_upwards [nhdsWithin_le_nhds hf] with r hr
  rw [slope_def_module, slope_def_module, hr, smul_mul_assoc]

/-- The derivative of the Dyson matrix along `z = x + ihr`: `∂_r M = w'M²` with
`w'(1 - βM²_ii) = ih`, (A.66) [da:eq:height-derivative-identities]. -/
private lemma vt_seg_deriv {b β h : ℝ} (hb : 0 ≤ b) (hβ : 0 ≤ β) (hh : 0 < h) {L : ℕ}
    (hL : 3 ≤ L) (x : ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ w' : ℂ,
      (∀ i j, HasDerivAt (fun r : ℝ => dysonMat b β L ((x : ℂ) + ((h * r : ℝ) : ℂ) * I)
          (mRootV b β L ((x : ℂ) + ((h * r : ℝ) : ℂ) * I)) i j)
        (w' * (dysonMat b β L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I)
          (mRootV b β L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I)) *
          dysonMat b β L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I)
          (mRootV b β L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I))) i j) r₀) ∧
      ∀ i, w' * (1 - (β : ℂ) * (dysonMat b β L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I)
          (mRootV b β L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I)) *
          dysonMat b β L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I)
          (mRootV b β L ((x : ℂ) + ((h * r₀ : ℝ) : ℂ) * I))) i i) = (h : ℂ) * I := by
  set zf : ℝ → ℂ := fun r => (x : ℂ) + ((h * r : ℝ) : ℂ) * I with hzf
  set μf : ℝ → ℂ := fun r => mRootV b β L (zf r) with hμf
  set wf : ℝ → ℂ := fun r => zf r + (β : ℂ) * μf r with hwf
  set Bf : ℝ → Matrix (Fin L) (Fin L) ℂ :=
    fun r => (b : ℂ) • cycleAdj L - wf r • (1 : Matrix (Fin L) (Fin L) ℂ) with hBf
  have hzim : ∀ r, (zf r).im = h * r := fun r => by simp [hzf]
  have hroot : ∀ r, 0 < r → IsDysonRootV b β L (zf r) (μf r) := fun r hr =>
    vt_root hb hβ hL (by rw [hzim]; positivity)
  have hwim : ∀ r, 0 < r → 0 < (wf r).im := by
    intro r hr
    simp only [hwf]
    rw [Complex.add_im, Complex.im_ofReal_mul, hzim]
    have := (hroot r hr).1
    positivity
  have hS : ∀ r, dysonMat b β L (zf r) (μf r) = (Bf r)⁻¹ := fun r => rfl
  have hz' : HasDerivAt zf ((h : ℂ) * I) r₀ := by
    have h1 : HasDerivAt (fun r : ℝ => ((h * r : ℝ) : ℂ)) (h : ℂ) r₀ := by
      have := ((hasDerivAt_id r₀).const_mul h).ofReal_comp
      simpa using this
    simpa [hzf] using (h1.mul_const I).const_add (x : ℂ)
  -- the derivative of `w`, and its relation to the derivative of the root
  obtain ⟨w', hwd, hw0, hwμ⟩ : ∃ w' : ℂ, HasDerivAt wf w' r₀ ∧ (β = 0 → w' = (h : ℂ) * I) ∧
      (0 < β → ∃ μ' : ℂ, HasDerivAt μf μ' r₀ ∧ w' = (h : ℂ) * I + (β : ℂ) * μ') := by
    rcases hβ.eq_or_lt with hβ0 | hβ0
    · refine ⟨(h : ℂ) * I, ?_, fun _ => rfl, fun h' => absurd hβ0 h'.ne⟩
      have : wf = zf := by
        funext r
        simp [hwf, ← hβ0]
      rw [this]
      exact hz'
    · have hdμ : DifferentiableAt ℂ (mRootV b β L) (zf r₀) :=
        vt_mRootV_diffAt hb hβ0 hL (by rw [hzim]; positivity)
      have hμd : HasDerivAt μf (deriv (mRootV b β L) (zf r₀) * ((h : ℂ) * I)) r₀ :=
        hdμ.hasDerivAt.comp r₀ hz'
      refine ⟨(h : ℂ) * I + (β : ℂ) * (deriv (mRootV b β L) (zf r₀) * ((h : ℂ) * I)),
        hz'.add (hμd.const_mul (β : ℂ)), fun h' => absurd h' hβ0.ne', fun _ => ⟨_, hμd, rfl⟩⟩
  have hBcont : ContinuousAt Bf r₀ := by
    have : ContinuousAt wf r₀ := hwd.continuousAt
    exact continuousAt_const.sub (this.smul continuousAt_const)
  have hdet : (Bf r₀).det ≠ 0 := (vt_cyc_isUnit b L (hwim r₀ hr₀)).ne_zero
  have hinvc : ContinuousAt (fun r => (Bf r)⁻¹) r₀ := by
    have h1 : ContinuousAt Inv.inv (Bf r₀) := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hdet
    exact h1.comp hBcont
  have hder : ∀ i j, HasDerivAt (fun r => dysonMat b β L (zf r) (μf r) i j)
      (w' * ((Bf r₀)⁻¹ * (Bf r₀)⁻¹) i j) r₀ := by
    intro i j
    refine vt_hasDerivAt_of_factor (φ := fun r => ((Bf r)⁻¹ * (Bf r₀)⁻¹) i j) hwd ?_ ?_
    · have h1 : ContinuousAt (fun r => (Bf r)⁻¹ * (Bf r₀)⁻¹) r₀ :=
        hinvc.mul continuousAt_const
      exact (continuous_apply_apply i j).continuousAt.comp h1
    · filter_upwards [lt_mem_nhds hr₀] with r hr
      have hres := vt_cyc_resolvent b L (hwim r hr) (hwim r₀ hr₀)
      simp only [hS]
      have := congrFun (congrFun hres i) j
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
      exact this
  refine ⟨w', fun i j => hder i j, fun i => ?_⟩
  change w' * (1 - (β : ℂ) * (((Bf r₀)⁻¹ * (Bf r₀)⁻¹ : Matrix (Fin L) (Fin L) ℂ) i i)) =
    (h : ℂ) * I
  rcases hβ.eq_or_lt with hβ0 | hβ0
  · rw [hw0 hβ0.symm, ← hβ0]
    simp
  · obtain ⟨μ', hμd, hw'⟩ := hwμ hβ0
    have hdiag : ∀ᶠ r in 𝓝 r₀, dysonMat b β L (zf r) (μf r) i i = μf r := by
      filter_upwards [lt_mem_nhds hr₀] with r hr
      rw [dysonMat_diag b β L (by omega) _ _ (by have := hwim r hr; simpa [hwf] using this)]
      exact ((hroot r hr).2).symm
    have h1 : HasDerivAt μf (w' * ((Bf r₀)⁻¹ * (Bf r₀)⁻¹) i i) r₀ :=
      (hder i i).congr_of_eventuallyEq (hdiag.mono fun r hr => hr.symm)
    have h2 : μ' = w' * ((Bf r₀)⁻¹ * (Bf r₀)⁻¹) i i := hμd.unique h1
    linear_combination hw' + (β : ℂ) * h2

/-! ### Bounds at a point of the vertical half-line -/

/-- The entries of `M²` are bounded by the common row norm `Σ_c |M_ac|²` of a symmetric `M`. -/
private lemma vt_sq_entry {L : ℕ} (M : Matrix (Fin L) (Fin L) ℂ) (hsym : ∀ i j, M i j = M j i)
    {T : ℝ} (hT : ∀ a, ∑ c, ‖M a c‖ ^ 2 = T) (a b : Fin L) : ‖(M * M) a b‖ ≤ T := by
  have hT0 : 0 ≤ T := by
    rw [← hT a]
    exact Finset.sum_nonneg fun c _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c => ‖M a c‖) (fun c => ‖M b c‖)
  simp only [hT a, hT b] at hcs
  have h1 : ‖(M * M) a b‖ ≤ ∑ c, ‖M a c‖ * ‖M b c‖ := by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul, hsym c b]
  have h2 : (∑ c, ‖M a c‖ * ‖M b c‖) ^ 2 ≤ T ^ 2 := by nlinarith
  have h3 : ∑ c, ‖M a c‖ * ‖M b c‖ ≤ T := by
    have h0 : 0 ≤ ∑ c, ‖M a c‖ * ‖M b c‖ :=
      Finset.sum_nonneg fun c _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    exact (pow_le_pow_iff_left₀ h0 hT0 two_ne_zero).mp h2
  exact h1.trans h3

/-- The Dyson matrix at a point `z` with `|Re z| + √β ≤ 2 - k` and `L min{Im z, 1} ≥ 8`
(hopping `1`, variance `β ≥ 0`): the root, the diagonal `M_aa = m`, the common row norm
`Σ_c |M_ac|² = Im m / (Im z + β Im m)` (Ward), the entry bound `4/k` and the absolute row
bound `32/(k Im z)`, as a perturbation of the bulk free resolvent at `z + βm`. -/
private lemma vt_point {b k : ℝ} (hb1 : b = 1) (hk : 0 < k) (hk1 : k ≤ 1) {L : ℕ}
    (hL : 3 ≤ L) {β : ℝ} (hβ : 0 ≤ β) {z : ℂ} (hz : 0 < z.im)
    (hloc : |z.re| + Real.sqrt β ≤ 2 - k) (hLz : 8 ≤ L * min z.im 1) :
    IsDysonRootV b β L z (mRootV b β L z) ∧
    (∀ a, dysonMat b β L z (mRootV b β L z) a a = mRootV b β L z) ∧
    (∀ a, ∑ c, ‖dysonMat b β L z (mRootV b β L z) a c‖ ^ 2 =
      (mRootV b β L z).im / (z.im + β * (mRootV b β L z).im)) ∧
    (∀ a c, ‖dysonMat b β L z (mRootV b β L z) a c‖ ≤ 4 / k) ∧
    (∀ a, ∑ c, ‖dysonMat b β L z (mRootV b β L z) a c‖ ≤ 32 / (k * z.im)) := by
  subst hb1
  set μ := mRootV 1 β L z with hμ
  have hroot : IsDysonRootV 1 β L z μ := vt_root zero_le_one hβ hL hz
  have hμim : 0 < μ.im := hroot.1
  have hwim : (z + β * μ).im = z.im + β * μ.im := by simp
  have hw : 0 < (z + β * μ).im := by rw [hwim]; positivity
  have hdiag : ∀ a, dysonMat 1 β L z μ a a = μ := by
    intro a
    rw [dysonMat_diag 1 β L (by omega) z μ hw a]
    exact hroot.2.symm
  have hward : ∀ a, μ.im = (z.im + β * μ.im) * ∑ c, ‖dysonMat 1 β L z μ a c‖ ^ 2 := by
    intro a
    have := vt_ward 1 β L z μ hw a
    rw [hdiag a, hwim] at this
    exact this
  have hrow : ∀ a, ∑ c, ‖dysonMat 1 β L z μ a c‖ ^ 2 = μ.im / (z.im + β * μ.im) := by
    intro a
    have hpos : 0 < z.im + β * μ.im := by rw [← hwim]; exact hw
    rw [eq_div_iff hpos.ne', mul_comm]
    exact (hward a).symm
  -- `β ‖μ‖² ≤ 1`
  have hβμ : β * ‖μ‖ ^ 2 ≤ 1 := by
    have h1 : ‖dysonMat 1 β L z μ ⟨0, by omega⟩ ⟨0, by omega⟩‖ ^ 2 ≤
        ∑ c, ‖dysonMat 1 β L z μ ⟨0, by omega⟩ c‖ ^ 2 :=
      Finset.single_le_sum (f := fun c => ‖dysonMat 1 β L z μ ⟨0, by omega⟩ c‖ ^ 2)
        (fun c _ => sq_nonneg _) (Finset.mem_univ _)
    rw [hdiag] at h1
    have h2 := hward ⟨0, by omega⟩
    have h3 : β * μ.im * ‖μ‖ ^ 2 ≤ μ.im := by
      have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ z.im + β * μ.im)
      have h5 : (z.im + β * μ.im) * ∑ c, ‖dysonMat 1 β L z μ ⟨0, by omega⟩ c‖ ^ 2 = μ.im :=
        h2.symm
      nlinarith [mul_nonneg hz.le (sq_nonneg ‖μ‖)]
    have : (β * ‖μ‖ ^ 2) * μ.im ≤ 1 * μ.im := by linarith
    exact le_of_mul_le_mul_right this hμim
  have hβμ' : β * ‖μ‖ ≤ Real.sqrt β := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg ‖μ‖]
  have hre : |(z + β * μ).re| ≤ 2 - k := by
    have : (z + β * μ).re = z.re + β * μ.re := by simp
    rw [this]
    calc |z.re + β * μ.re| ≤ |z.re| + |β * μ.re| := abs_add_le _ _
      _ ≤ |z.re| + β * ‖μ‖ := by
          gcongr
          rw [abs_mul, abs_of_nonneg hβ]
          gcongr
          exact Complex.abs_re_le_norm μ
      _ ≤ 2 - k := by linarith
  have hLw : 8 ≤ L * min (z + β * μ).im 1 := by
    refine hLz.trans ?_
    gcongr
    rw [hwim]
    linarith [mul_nonneg hβ hμim.le]
  obtain ⟨hent, hrows⟩ := vt_free_bound hk hk1 hL hre hw hLw
  refine ⟨hroot, hdiag, hrow, fun a c => hent a c, fun a => (hrows a).trans ?_⟩
  rw [hwim]
  have : z.im ≤ z.im + β * μ.im := by linarith [mul_nonneg hβ hμim.le]
  gcongr

/-- The point bounds at a vertical point `z = x + iy`, `y ≥ η_u`, `u ≤ 1/2`, in terms of the
bounds `C₀⁻¹ ≤ Im m`, `‖m‖ ≤ C₀` on the root of the real-energy equation. -/
private lemma vt_pointG {κ C₀ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hC₀ : 0 < C₀) {g : ℝ}
    (hgκ : 2 * (C₀ + 1) / κ ≤ g) (hg1 : 1 ≤ g) {L : ℕ} (hL3 : 3 ≤ L)
    (hRC : 16 * C₀ * g ^ 2 ≤ L) (h16 : 16 * g ^ 2 ≤ L) {E : ℝ} (hE : |E| ≤ 2 - κ) {m : ℂ}
    (hmim : C₀⁻¹ ≤ m.im) (hmn : ‖m‖ ≤ C₀) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) {y : ℝ}
    (hy : etaChar g m u ≤ y) :
    0 < y ∧ u * gammaG g ≤ C₀ * y ∧
    let x := (zChar g E m u).re
    let mu := mRootV (hopB g) (u * gammaG g) L ((x : ℂ) + (y : ℂ) * I)
    let M := dysonMat (hopB g) (u * gammaG g) L ((x : ℂ) + (y : ℂ) * I) mu
    0 < mu.im ∧ (∀ a, M a a = mu) ∧
      (∀ a, ∑ c, ‖M a c‖ ^ 2 = mu.im / (y + u * gammaG g * mu.im)) ∧
      (∀ a c, ‖M a c‖ ≤ 64 / κ) ∧ ∀ a, ∑ c, ‖M a c‖ ≤ 64 / κ / y := by
  have hg0 : 0 < g := by linarith
  have hb : hopB g = 1 := vt_hopB_of_one_le hg1
  have hγ : gammaG g = (g ^ 2)⁻¹ := vt_gammaG_of_one_le hg1
  have hγpos : 0 < gammaG g := vt_gammaG_pos g
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg1
  have hγg : gammaG g * g ^ 2 = 1 := by rw [hγ]; field_simp
  have hηy : (gammaG g / (2 * C₀)) ≤ y := by
    refine le_trans ?_ hy
    unfold etaChar
    have h1 : gammaG g * C₀⁻¹ / 2 ≤ (1 - u) * gammaG g * m.im := by
      have : (1 / 2 : ℝ) ≤ 1 - u := by linarith
      calc gammaG g * C₀⁻¹ / 2 = (1 / 2) * gammaG g * C₀⁻¹ := by ring
        _ ≤ (1 - u) * gammaG g * m.im := by gcongr
    calc gammaG g / (2 * C₀) = gammaG g * C₀⁻¹ / 2 := by field_simp
      _ ≤ _ := h1
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hηy
  have hβ0 : 0 ≤ u * gammaG g := by positivity
  have hβγ : u * gammaG g ≤ gammaG g := by nlinarith
  have hβy : u * gammaG g ≤ C₀ * y := by
    have h1 : gammaG g / 2 ≤ C₀ * y := by
      have := mul_le_mul_of_nonneg_left hηy hC₀.le
      calc gammaG g / 2 = C₀ * (gammaG g / (2 * C₀)) := by field_simp
        _ ≤ C₀ * y := this
    nlinarith
  refine ⟨hy0, hβy, ?_⟩
  intro x mu M
  have hk0 : 0 < κ / 2 := by positivity
  have hk1 : κ / 2 ≤ 1 := by linarith
  have hzim : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  have hzre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have hx : x = E + (1 - u) * gammaG g * m.re := by simp [x, zChar]
  have hxabs : |x| ≤ 2 - κ + C₀ / g := by
    rw [hx]
    have h1 : |(1 - u) * gammaG g * m.re| ≤ C₀ / g := by
      rw [abs_mul, abs_of_nonneg (by nlinarith : 0 ≤ (1 - u) * gammaG g)]
      have h2 : |m.re| ≤ C₀ := (Complex.abs_re_le_norm m).trans hmn
      calc (1 - u) * gammaG g * |m.re| ≤ 1 * gammaG g * C₀ := by gcongr; linarith
        _ = C₀ * (g ^ 2)⁻¹ := by rw [hγ]; ring
        _ ≤ C₀ * g⁻¹ := by
            gcongr
            nlinarith
        _ = C₀ / g := by ring
    calc |E + (1 - u) * gammaG g * m.re| ≤ |E| + |(1 - u) * gammaG g * m.re| := abs_add_le _ _
      _ ≤ 2 - κ + C₀ / g := by linarith
  have hsqrt : Real.sqrt (u * gammaG g) ≤ 1 / g := by
    rw [Real.sqrt_le_left (by positivity)]
    calc u * gammaG g ≤ gammaG g := hβγ
      _ = (1 / g) ^ 2 := by rw [hγ]; field_simp
  have hgκ' : (C₀ + 1) / g ≤ κ / 2 := by
    rw [div_le_iff₀ hg0]
    rw [div_le_iff₀ hκ] at hgκ
    linarith
  have hloc : |((x : ℂ) + (y : ℂ) * I).re| + Real.sqrt (u * gammaG g) ≤ 2 - κ / 2 := by
    rw [hzre]
    have : C₀ / g + 1 / g = (C₀ + 1) / g := by ring
    linarith
  have hLz : 8 ≤ L * min ((x : ℂ) + (y : ℂ) * I).im 1 := by
    rw [hzim]
    rcases le_total y 1 with h | h
    · rw [min_eq_left h]
      have h1 : 16 * C₀ * g ^ 2 * (gammaG g / (2 * C₀)) ≤ L * y := by
        gcongr
      have h2 : 16 * C₀ * g ^ 2 * (gammaG g / (2 * C₀)) = 8 := by
        field_simp
        linarith [hγg]
      linarith
    · rw [min_eq_right h]
      have : (16 : ℝ) ≤ L := by nlinarith
      linarith
  obtain ⟨hroot, hdiag, hrow, hent, hrows⟩ := vt_point (b := hopB g) (k := κ / 2) hb hk0 hk1
    hL3 hβ0 (z := (x : ℂ) + (y : ℂ) * I) (by rw [hzim]; exact hy0) hloc hLz
  rw [hzim] at hrow hrows
  have e1 : 4 / (κ / 2) ≤ 64 / κ := by
    rw [div_le_div_iff₀ hk0 hκ]; nlinarith
  have e2 : 32 / (κ / 2 * y) = 64 / κ / y := by field_simp; ring
  refine ⟨hroot.1, hdiag, hrow, fun a c => (hent a c).trans e1, fun a => ?_⟩
  rw [← e2]
  exact hrows a

/-- From the point bounds on the root, the entries and the rows of `M`: the entry, row and
contraction bounds, and the logarithmic height derivative via `∂_r M = w'M²` with
`w'(1 - βM²_aa) = iγ_g`. -/
private lemma vt_conclude {g : ℝ} {L : ℕ} (hL3 : 3 ≤ L) (hg0 : 0 < g) {x u y C₀ CA : ℝ}
    (hC₀ : 0 < C₀) (hCA1 : 1 ≤ CA) (hy0 : 0 < y) (hu0 : 0 ≤ u)
    (hβy : u * gammaG g ≤ C₀ * y)
    (hpt : let mu := mRootV (hopB g) (u * gammaG g) L ((x : ℂ) + (y : ℂ) * I)
      let M := dysonMat (hopB g) (u * gammaG g) L ((x : ℂ) + (y : ℂ) * I) mu
      0 < mu.im ∧ (∀ a, M a a = mu) ∧
        (∀ a, ∑ c, ‖M a c‖ ^ 2 = mu.im / (y + u * gammaG g * mu.im)) ∧
        (∀ a c, ‖M a c‖ ≤ CA) ∧ ∀ a, ∑ c, ‖M a c‖ ≤ CA / y) :
    let mu := mRootV (hopB g) (u * gammaG g) L
      ((x : ℂ) + ((gammaG g * (y / gammaG g) : ℝ) : ℂ) * I)
    let M := segMat g L x u (y / gammaG g)
    0 ≤ mu.im ∧ ‖mu‖ ≤ CA * (1 + CA * C₀) ∧ (∀ a b, ‖M a b‖ ≤ CA * (1 + CA * C₀)) ∧
      (∀ a, u * gammaG g * ∑ b, (‖M a b‖ + ‖M a b‖ ^ 2) ≤ CA * (1 + CA * C₀)) ∧
      (∀ a, u * gammaG g * ∑ b, ‖M a b‖ ^ 2 ≤ 1 - 1 / (1 + CA * C₀)) ∧
      (∀ a b, DifferentiableAt ℝ (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)) ∧
      ∀ a b, ‖((y / gammaG g : ℝ) : ℂ) * deriv (fun r : ℝ => segMat g L x u r a b)
        (y / gammaG g)‖ ≤ CA * (1 + CA * C₀) := by
  intro mu M
  have hγpos := vt_gammaG_pos g
  have hzy : (x : ℂ) + ((gammaG g * (y / gammaG g) : ℝ) : ℂ) * I = (x : ℂ) + (y : ℂ) * I := by
    rw [mul_div_cancel₀ _ hγpos.ne']
  have hmu : mu = mRootV (hopB g) (u * gammaG g) L ((x : ℂ) + (y : ℂ) * I) := by
    change mRootV _ _ _ _ = _
    rw [hzy]
  have hMd : M = dysonMat (hopB g) (u * gammaG g) L ((x : ℂ) + (y : ℂ) * I) mu := by
    change dysonMat _ _ _ _ _ = _
    rw [hzy, hmu]
  obtain ⟨hμim, hdiag, hrow, hent, hrows⟩ := hpt
  rw [← hmu] at hμim hdiag hrow hent hrows
  rw [← hMd] at hdiag hrow hent hrows
  have hsym : ∀ i j, M i j = M j i := by
    intro i j
    rw [hMd]
    exact vt_dysonMat_symm _ _ _ _ _ i j
  set β := u * gammaG g with hβ
  have hβ0 : 0 ≤ β := by positivity
  set a0 : Fin L := ⟨0, by omega⟩ with ha0
  have hμn : ‖mu‖ ≤ CA := by
    have := hent a0 a0
    rwa [hdiag] at this
  have hμle : mu.im ≤ CA := (Complex.im_le_norm mu).trans hμn
  have hCApos : 0 < CA := by linarith
  have hD : 0 < y + β * mu.im := by positivity
  set T := mu.im / (y + β * mu.im) with hT
  have hT0 : 0 ≤ T := by positivity
  have hβμ : β * mu.im ≤ CA * C₀ * y := by
    calc β * mu.im ≤ (C₀ * y) * CA := mul_le_mul hβy hμle hμim.le (by positivity)
      _ = CA * C₀ * y := by ring
  have hcc : 1 - 1 / (1 + CA * C₀) = CA * C₀ / (1 + CA * C₀) := by
    field_simp
    ring
  have hβT : β * T ≤ 1 - 1 / (1 + CA * C₀) := by
    rw [hT, hcc, ← mul_div_assoc, div_le_div_iff₀ hD (by positivity)]
    nlinarith
  have hCC : 0 < 1 + CA * C₀ := by positivity
  have hC'ge : CA ≤ CA * (1 + CA * C₀) := by nlinarith [mul_pos hCApos hC₀]
  -- the derivative
  have hr₀ : 0 < y / gammaG g := div_pos hy0 hγpos
  obtain ⟨w', hder, hid⟩ := vt_seg_deriv (b := hopB g) (β := u * gammaG g) (h := gammaG g)
    (vt_hopB_nonneg hg0.le) hβ0 hγpos hL3 x hr₀
  have hder' : ∀ i j, HasDerivAt (fun r : ℝ => segMat g L x u r i j) (w' * (M * M) i j)
      (y / gammaG g) := hder
  have hid' : ∀ i, w' * (1 - (β : ℂ) * (M * M) i i) = (gammaG g : ℂ) * I := hid
  have hMM : ∀ a b, ‖(M * M) a b‖ ≤ T := vt_sq_entry M hsym hrow
  have hw' : ‖w'‖ ≤ gammaG g * (1 + CA * C₀) := by
    have h1 : 1 / (1 + CA * C₀) ≤ ‖(1 : ℂ) - (β : ℂ) * (M * M) a0 a0‖ := by
      have h2 := norm_sub_norm_le (1 : ℂ) ((β : ℂ) * (M * M) a0 a0)
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0] at h2
      have h3 : β * ‖(M * M) a0 a0‖ ≤ β * T := mul_le_mul_of_nonneg_left (hMM a0 a0) hβ0
      linarith
    have h4 := hid' a0
    have h5 : ‖w'‖ * ‖(1 : ℂ) - (β : ℂ) * (M * M) a0 a0‖ = gammaG g := by
      rw [← norm_mul, h4, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hγpos.le]
    have h6 : ‖w'‖ * (1 / (1 + CA * C₀)) ≤ gammaG g := by
      rw [← h5]
      exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    rw [mul_one_div, div_le_iff₀ hCC] at h6
    linarith
  have hyT : y * T ≤ mu.im := by
    rw [hT, ← mul_div_assoc, div_le_iff₀ hD]
    nlinarith [mul_nonneg hβ0 hμim.le]
  refine ⟨hμim.le, hμn.trans hC'ge, fun a b => (hent a b).trans hC'ge, fun a => ?_, fun a => ?_,
    fun a b => (hder' a b).differentiableAt, fun a b => ?_⟩
  · rw [Finset.sum_add_distrib, mul_add, hrow a]
    have h1 : β * ∑ b, ‖M a b‖ ≤ CA * C₀ := by
      calc β * ∑ b, ‖M a b‖ ≤ β * (CA / y) := mul_le_mul_of_nonneg_left (hrows a) hβ0
        _ = CA * (β / y) := by ring
        _ ≤ CA * C₀ := by
            gcongr
            rw [div_le_iff₀ hy0]
            exact hβy
    have h2 : β * T ≤ 1 := by
      have : 0 < 1 / (1 + CA * C₀) := by positivity
      linarith
    nlinarith [mul_pos hCApos hC₀]
  · rw [hrow a]
    exact hβT
  · rw [(hder' a b).deriv, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr₀.le]
    calc y / gammaG g * (‖w'‖ * ‖(M * M) a b‖) ≤ y / gammaG g * (gammaG g * (1 + CA * C₀) * T) := by
          gcongr
          exact hMM a b
      _ = (1 + CA * C₀) * (y * T) := by field_simp
      _ ≤ (1 + CA * C₀) * CA := by gcongr; exact hyT.trans hμle
      _ = CA * (1 + CA * C₀) := by ring

/-- The Dyson quantities (5.27) [gc:eq:positive-dyson] on the vertical half-line above the
characteristic point at early times `u ∈ [0, 1/2]`, large coupling, uniformly in `y ≥ η_u`:
a bounded root `m_u(z)`, bounded entries and covariance-weighted rows (6.13)
[gc:eq:residual-row-bounds] of `M_{B,u}(z)`, the contraction `uγ_g Σ_c |M_{ac}|² ≤ 1 - c`, and
the logarithmic height derivative `|y ∂_y M_{ac}| ≤ C'` (as in (6.14) [da:eq:height-derivative]). -/
theorem dysonVert_large (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ R c C' : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ 0 < c ∧ 0 < C' ∧ ∀ g : ℝ, Cκ ≤ g →
      ∀ L : ℕ, R * g ^ 2 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ,
      IsDysonRootV (hopB g) (gammaG g) L E m → ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 →
      ∀ y : ℝ, etaChar g m u ≤ y →
      let x := (zChar g E m u).re
      let mu := mRootV (hopB g) (u * gammaG g) L ((x : ℂ) + ((gammaG g * (y / gammaG g) : ℝ) : ℂ) * I)
      let M := segMat g L x u (y / gammaG g)
      0 ≤ mu.im ∧ ‖mu‖ ≤ C' ∧ (∀ a b, ‖M a b‖ ≤ C') ∧
      (∀ a, u * gammaG g * ∑ b, (‖M a b‖ + ‖M a b‖ ^ 2) ≤ C') ∧
      (∀ a, u * gammaG g * ∑ b, ‖M a b‖ ^ 2 ≤ 1 - c) ∧
      (∀ a b, DifferentiableAt ℝ (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)) ∧
      ∀ a b, ‖((y / gammaG g : ℝ) : ℂ) * deriv (fun r : ℝ => segMat g L x u r a b) (y / gammaG g)‖ ≤
        C' := by
  obtain ⟨Cκ₀, R₀, c₀, C₀, hCκ₀, hR₀, hc₀, hC₀, H⟩ := large_periodic_comparison κ hκ hκ2
  have hCA1 : 1 ≤ 64 / κ := by
    rw [le_div_iff₀ hκ]; linarith
  have hCApos : 0 < 64 / κ := by linarith
  refine ⟨max Cκ₀ (2 * (C₀ + 1) / κ), max (max R₀ 16) (16 * C₀),
    1 / (1 + 64 / κ * C₀), 64 / κ * (1 + 64 / κ * C₀), le_trans hCκ₀ (le_max_left _ _), ?_,
    by positivity, by positivity, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_trans (le_max_right R₀ 16) (le_max_left _ _))
  intro g hg L hL E hE m hm u hu0 hu1 y hy x mu M
  have hg1 : 1 ≤ g := le_trans hCκ₀ (le_trans (le_max_left _ _) hg)
  have hg0 : 0 < g := by linarith
  have hgκ : 2 * (C₀ + 1) / κ ≤ g := le_trans (le_max_right _ _) hg
  have hR₀g : R₀ * g ^ 2 ≤ L :=
    le_trans (by gcongr; exact le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have h16 : 16 * g ^ 2 ≤ L :=
    le_trans (by gcongr; exact le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hRC : 16 * C₀ * g ^ 2 ≤ L := le_trans (by gcongr; exact le_max_right _ _) hL
  have hL3 : 3 ≤ L := by
    have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg1
    have : (3 : ℝ) ≤ L := by nlinarith
    exact_mod_cast this
  obtain ⟨m₀, -, hm₀, -, hm₀im, hm₀n, -⟩ := H g (le_trans (le_max_left _ _) hg) L hR₀g E hE
  obtain rfl : m = m₀ :=
    isDysonRootV_unique (hopB g) (gammaG g) (vt_hopB_nonneg hg0.le) (vt_gammaG_pos g) L hL3
      (E : ℂ) (by simp) m m₀ hm hm₀
  obtain ⟨hy0, hβy, hpt⟩ := vt_pointG hκ hκ2 hC₀ hgκ hg1 hL3 hRC h16 hE hm₀im hm₀n hu0 hu1 hy
  exact vt_conclude hL3 hg0 hC₀ hCA1 hy0 hu0 hβy hpt

end LSBA
