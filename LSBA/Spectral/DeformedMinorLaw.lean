import LSBA.Spectral.DeformedLocalLaw

/-!
# Diagonal entries of the minors

`Im G^{(i)}_{jj} ≤ C|M_jj|²` with high probability for diagonal `B` (two-index minors).
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal Matrix.Norms.L2Operator

noncomputable section
open scoped Classical

namespace LSBA

/-! ### Deterministic estimate -/

/-- The diagonal entries of a Hermitian matrix are real. -/
private lemma minorLaw_im_diag {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian)
    (i : Fin n) : (B i i).im = 0 := by
  have := hB.apply i i
  rw [Complex.star_def] at this
  exact Complex.conj_eq_iff_im.mp this

/-- For diagonal Hermitian `B` and `Im (z + q) > 0`, the trial profile has diagonal entries
`(-B_ii - z - q)⁻¹`. -/
private lemma minorLaw_deformedMat_diag {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.IsDiag) (hBh : B.IsHermitian) {z q : ℂ} (hw : 0 < (z + q).im) (i : Fin n) :
    deformedMat B z q i i = (-B i i - (z + q))⁻¹ := by
  unfold deformedMat resolventMat
  have h : -B - (z + q) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal (fun k => -B k k - (z + q)) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab, hB hab]
  have hne : ∀ k, -B k k - (z + q) ≠ 0 := by
    intro k hk
    have := congrArg Complex.im hk
    simp [minorLaw_im_diag hBh k] at this
    rw [Complex.add_im] at hw
    linarith
  rw [h, Matrix.inv_eq_right_inv (B := Matrix.diagonal (fun k => (-B k k - (z + q))⁻¹))]
  · simp
  · rw [Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hne a]
    · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]

/-- Ward's identity summed: the Hilbert–Schmidt norm of a resolvent is `Im Tr G / η`. -/
private lemma minorLaw_hs {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (E : ℝ) {η : ℝ} (hη : 0 < η) :
    ∑ k, ∑ l, ‖resolventMat A (E + η * Complex.I) k l‖ ^ 2 =
      (resolventMat A (E + η * Complex.I)).trace.im / η := by
  simp only [ward hA E hη.ne', Matrix.trace, Matrix.diag_apply, Complex.im_sum, Finset.sum_div]

/-- `(t/n) √H ≤ √(Y+2) · t/√(nη)` when `H ≤ (nY + 2η⁻¹)/η` and `nη ≥ 1`. -/
private lemma minorLaw_real {n t η Y H : ℝ} (hn : 0 < n) (hη : 0 < η)
    (hnη : 1 ≤ n * η) (ht : 0 ≤ t) (hY : 0 ≤ Y) (hH : H ≤ (n * Y + 2 * η⁻¹) / η) :
    t / n * Real.sqrt H ≤ Real.sqrt (Y + 2) * (t / Real.sqrt (n * η)) := by
  have hnη0 : 0 < n * η := mul_pos hn hη
  calc t / n * Real.sqrt H ≤ t / n * Real.sqrt ((n * Y + 2 * η⁻¹) / η) := by
        gcongr
    _ = Real.sqrt ((t / n) ^ 2 * ((n * Y + 2 * η⁻¹) / η)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    _ ≤ Real.sqrt ((Y + 2) * (t / Real.sqrt (n * η)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have e2 : (t / Real.sqrt (n * η)) ^ 2 = t ^ 2 / (n * η) := by
          rw [div_pow, Real.sq_sqrt hnη0.le]
        rw [e2]
        have e : (t / n) ^ 2 * ((n * Y + 2 * η⁻¹) / η) = t ^ 2 / (n * η) * (Y + 2 / (n * η)) := by
          field_simp
        rw [e]
        have h1 : 2 / (n * η) ≤ 2 := by
          rw [div_le_iff₀ hnη0]; nlinarith
        have h2 : 0 ≤ t ^ 2 / (n * η) := by positivity
        calc t ^ 2 / (n * η) * (Y + 2 / (n * η)) ≤ t ^ 2 / (n * η) * (Y + 2) := by gcongr
          _ = (Y + 2) * (t ^ 2 / (n * η)) := by ring
    _ = Real.sqrt (Y + 2) * (t / Real.sqrt (n * η)) := by
        rw [Real.sqrt_mul (by linarith), Real.sqrt_sq (by positivity)]

/-- Deterministic estimate behind the minor bound of Appendix G.1
[app:relative-local-law-proof]: for diagonal Hermitian `B` and `i ≠ j`, if `⟨G⟩` is within
`(2 C_p)⁻¹` of `m` with `C_p⁻¹ ≤ Im m ≤ C_p`, `|V_jj| ≤ t n^{-1/2}`, the centred quadratic form
`h^* G^{(ij)} h - n⁻¹ Tr G^{(ij)}` is at most `t n⁻¹ ‖G^{(ij)}‖_HS`, and
`C₁ t (nη)^{-1/2} ≤ (4 C_p)⁻¹`, then `Im G^{(i)}_jj ≤ 16 (C* + C_p + 2) |(-b_j - z - m)⁻¹|²`. -/
private lemma minorLaw_step {n : ℕ} (hn : 0 < n) {V B : Matrix (Fin n) (Fin n) ℂ}
    (hV : V.IsHermitian) (hB : B.IsHermitian) (hBd : B.IsDiag) {E η t Cp Cstar : ℝ} {m : ℂ}
    {i j : Fin n} (hji : j ≠ i) (hη : 0 < η) (hηC : η ≤ Cstar) (hnη : 1 ≤ (n : ℝ) * η)
    (ht : 1 ≤ t) (hCp : 1 ≤ Cp) (hm1 : Cp⁻¹ ≤ m.im) (hm2 : m.im ≤ Cp)
    (hG : ‖ntr (resolventMat (V - B) (E + η * Complex.I)) - m‖ ≤ (2 * Cp)⁻¹)
    (hsmall : (Real.sqrt Cstar + Real.sqrt (Cp + 3) + 2) * (t / Real.sqrt (n * η)) ≤
      (4 * Cp)⁻¹)
    (hVd : ‖V j j‖ ≤ t / Real.sqrt n)
    (hQ : ‖star (fun k : {k : {k // k ≠ i} // k ≠ ⟨j, hji⟩} => V k.1.1 j) ⬝ᵥ
        (resolventMat (minorMat (minorMat (V - B) i) ⟨j, hji⟩) (E + η * Complex.I) *ᵥ
          fun k : {k : {k // k ≠ i} // k ≠ ⟨j, hji⟩} => V k.1.1 j) -
        (n : ℂ)⁻¹ * (resolventMat (minorMat (minorMat (V - B) i) ⟨j, hji⟩)
          (E + η * Complex.I)).trace‖ ≤
      t / n * Real.sqrt (∑ k, ∑ l, ‖resolventMat (minorMat (minorMat (V - B) i) ⟨j, hji⟩)
        (E + η * Complex.I) k l‖ ^ 2)) :
    (resolventMat (minorMat (V - B) i) (E + η * Complex.I) ⟨j, hji⟩ ⟨j, hji⟩).im ≤
      16 * (Cstar + Cp + 2) * ‖(-B j j - ((E + η * Complex.I) + m))⁻¹‖ ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnn : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hCp0 : 0 < Cp := by linarith
  have hCpi : 0 < Cp⁻¹ := inv_pos.mpr hCp0
  have hCpi2 : 0 < (2 * Cp)⁻¹ := inv_pos.mpr (by linarith)
  have hzim : (E + η * Complex.I).im = η := by simp
  have hz : 0 < (E + η * Complex.I).im := by rw [hzim]; exact hη
  have hnη0 : 0 < (n : ℝ) * η := mul_pos hn' hη
  set z : ℂ := E + η * Complex.I with hzdef
  set H : Matrix (Fin n) (Fin n) ℂ := V - B with hH
  have hHh : H.IsHermitian := hV.sub hB
  set H' : Matrix {k // k ≠ i} {k // k ≠ i} ℂ := minorMat H i with hH'
  have hH'h : H'.IsHermitian := hHh.submatrix _
  set j' : {k // k ≠ i} := ⟨j, hji⟩ with hj'
  set H'' := minorMat H' j' with hH''
  set G := resolventMat H z with hGdef
  set A := resolventMat H'' z with hAdef
  set s : ℝ := t / Real.sqrt (n * η) with hs
  have hs0 : 0 ≤ s := by positivity
  -- trace comparison
  have htr1 := norm_trace_resolventMat_sub_minor_le hHh hz i
  have htr2 := norm_trace_resolventMat_sub_minor_le hH'h hz j'
  rw [hzim] at htr1 htr2
  have htr : ‖G.trace - A.trace‖ ≤ 2 * η⁻¹ := by
    have e : G.trace - A.trace = (G.trace - (resolventMat H' z).trace) +
        ((resolventMat H' z).trace - A.trace) := by ring
    rw [e]
    exact (norm_add_le _ _).trans (by linarith)
  -- bounds on `⟨G⟩`
  have hGim : (ntr G).im ≤ Cp + 1 := by
    have h1 := (Complex.abs_im_le_norm (ntr G - m))
    rw [Complex.sub_im] at h1
    have h2 := (abs_le.mp (h1.trans hG)).2
    have : (2 * Cp)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith
  have hGim' : (2 * Cp)⁻¹ ≤ (ntr G).im := by
    have h1 := (Complex.abs_im_le_norm (ntr G - m))
    rw [Complex.sub_im] at h1
    have h2 := (abs_le.mp (h1.trans hG)).1
    have : Cp⁻¹ = 2 * (2 * Cp)⁻¹ := by field_simp
    linarith
  -- the Schur formula in the minor `H'`
  have hschur := resolventMat_diag_schur hH'h hz j'
  have hcol : minorCol H' j' = fun k : {k : {k // k ≠ i} // k ≠ j'} => V k.1.1 j := by
    funext k
    have hk : k.1.1 ≠ j := fun h => k.2 (Subtype.ext h)
    simp [minorCol, H', minorMat, H, hj', Matrix.sub_apply, hBd hk]
  have hdiag : H' j' j' = V j j - B j j := by
    simp [H', minorMat, H, hj', Matrix.sub_apply]
  rw [hcol, hdiag] at hschur
  set Q : ℂ := star (fun k : {k : {k // k ≠ i} // k ≠ j'} => V k.1.1 j) ⬝ᵥ
    (A *ᵥ fun k : {k : {k // k ≠ i} // k ≠ j'} => V k.1.1 j) with hQdef
  set T : ℂ := (n : ℂ)⁻¹ * A.trace with hT
  set w : ℂ := -B j j - (z + ntr G) with hw
  set d : ℂ := V j j - (Q - T) - (T - ntr G) with hd
  set wm : ℂ := -B j j - (z + m) with hwm
  have hu : V j j - B j j - z - Q = w + d := by rw [hw, hd]; ring
  rw [hu] at hschur
  -- the size of `d`
  have hVj : ‖V j j‖ ≤ Real.sqrt Cstar * s := by
    refine hVd.trans ?_
    have e : t / Real.sqrt n = Real.sqrt η * s := by
      rw [hs, Real.sqrt_mul hn'.le η]
      have : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn').ne'
      have : Real.sqrt η ≠ 0 := (Real.sqrt_pos.mpr hη).ne'
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hηC) hs0
  have hQs : ‖Q - T‖ ≤ Real.sqrt (Cp + 3) * s := by
    refine hQ.trans ?_
    have hH''h : H''.IsHermitian := hH'h.submatrix _
    have hhs := minorLaw_hs hH''h E hη
    have him : A.trace.im ≤ n * (Cp + 1) + 2 * η⁻¹ := by
      have h := Complex.abs_im_le_norm (G.trace - A.trace)
      rw [Complex.sub_im] at h
      have h' := (abs_le.mp (h.trans htr)).1
      have hq : G.trace.im ≤ n * (Cp + 1) := by
        have h := hGim
        rw [ntr, Fintype.card_fin] at h
        have e : ((n : ℂ)⁻¹ * G.trace).im = (n : ℝ)⁻¹ * G.trace.im := by
          have : (n : ℂ)⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) := by simp
          rw [this, Complex.im_ofReal_mul]
        rw [e] at h
        have := mul_le_mul_of_nonneg_left h hn'.le
        rwa [← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul] at this
      linarith
    have := minorLaw_real (t := t) hn' hη hnη (by linarith) (by linarith : (0 : ℝ) ≤ Cp + 1)
      (H := ∑ k, ∑ l, ‖A k l‖ ^ 2) (by rw [hAdef, hhs]; exact div_le_div_of_nonneg_right him hη.le)
    have e : Cp + 1 + 2 = Cp + 3 := by ring
    rwa [e] at this
  have hTG : ‖T - ntr G‖ ≤ 2 * s := by
    have e : T - ntr G = -((n : ℂ)⁻¹ * (G.trace - A.trace)) := by
      simp only [hT, ntr, Fintype.card_fin]; ring
    rw [e, norm_neg, norm_mul, norm_inv, Complex.norm_natCast]
    have h1 : (n : ℝ)⁻¹ * ‖G.trace - A.trace‖ ≤ (n : ℝ)⁻¹ * (2 * η⁻¹) := by gcongr
    have h3 : (n : ℝ)⁻¹ * η⁻¹ ≤ s := by
      rw [← mul_inv]
      set x : ℝ := n * η with hx
      have hx1 : 1 ≤ x := hnη
      have hsx : Real.sqrt x ≤ x := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
      have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
      calc x⁻¹ ≤ (Real.sqrt x)⁻¹ := inv_anti₀ hsx0 hsx
        _ ≤ t * (Real.sqrt x)⁻¹ := le_mul_of_one_le_left (inv_nonneg.mpr hsx0.le) ht
        _ = s := by rw [hs, div_eq_mul_inv]
    linarith
  have hd1 : ‖d‖ ≤ (Real.sqrt Cstar + Real.sqrt (Cp + 3) + 2) * s := by
    have e : d = V j j - (Q - T) - (T - ntr G) := rfl
    calc ‖d‖ ≤ ‖V j j - (Q - T)‖ + ‖T - ntr G‖ := by rw [e]; exact norm_sub_le _ _
      _ ≤ ‖V j j‖ + ‖Q - T‖ + ‖T - ntr G‖ := by
          have := norm_sub_le (V j j) (Q - T)
          linarith
      _ ≤ _ := by linarith
  have hd2 : ‖d‖ ≤ (4 * Cp)⁻¹ := hd1.trans hsmall
  have hd3 : (4 * Cp)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  -- the sizes of `w`, `wm`
  have hwim : w.im = -(η + (ntr G).im) := by
    simp [hw, minorLaw_im_diag hB j, hzim]
  have hwmim : wm.im = -(η + m.im) := by
    simp [hwm, minorLaw_im_diag hB j, hzim]
  have hwn : (2 * Cp)⁻¹ ≤ ‖w‖ := by
    have h := Complex.abs_im_le_norm w
    rw [hwim, abs_neg, abs_of_nonneg (by linarith)] at h
    linarith
  have hwmn : Cp⁻¹ ≤ ‖wm‖ := by
    have h := Complex.abs_im_le_norm wm
    rw [hwmim, abs_neg, abs_of_nonneg (by linarith)] at h
    linarith
  have hwwm : ‖w - wm‖ ≤ (2 * Cp)⁻¹ := by
    have e : w - wm = -(ntr G - m) := by rw [hw, hwm]; ring
    rw [e, norm_neg]; exact hG
  have hCp2 : Cp⁻¹ = 2 * (2 * Cp)⁻¹ := by field_simp
  have hwn2 : ‖wm‖ / 2 ≤ ‖w‖ := by
    have h1 := norm_sub_norm_le wm w
    have h2 : ‖wm - w‖ = ‖w - wm‖ := norm_sub_rev _ _
    linarith
  have hd4 : ‖d‖ ≤ ‖w‖ / 2 := by
    have : (4 * Cp)⁻¹ = (2 * Cp)⁻¹ / 2 := by field_simp; ring
    linarith
  set u : ℂ := w + d with hudef
  have hun : ‖wm‖ / 4 ≤ ‖u‖ := by
    have h1 : ‖w‖ - ‖d‖ ≤ ‖u‖ := by
      have := norm_sub_norm_le w (-d)
      rw [sub_neg_eq_add, norm_neg] at this
      exact this
    linarith
  have hwm0 : 0 < ‖wm‖ := by
    have : 0 < Cp⁻¹ := inv_pos.mpr hCp0
    linarith
  have hu0 : 0 < ‖u‖ := by linarith
  -- the imaginary part of `G^{(i)}_jj = u⁻¹`
  rw [hschur, Complex.inv_im, Complex.normSq_eq_norm_sq]
  have hnum : -u.im ≤ Cstar + Cp + 2 := by
    have h1 : u.im = w.im + d.im := by rw [hudef, Complex.add_im]
    have h2 : -d.im ≤ ‖d‖ := by
      have := (abs_le.mp (Complex.abs_im_le_norm d)).1
      linarith
    rw [h1, hwim]
    linarith
  have hnum0 : 0 ≤ Cstar + Cp + 2 := by
    have : 0 ≤ Cstar := hη.le.trans hηC
    linarith
  have hM : ‖(-B j j - (z + m))⁻¹‖ ^ 2 = (‖wm‖ ^ 2)⁻¹ := by
    rw [← hwm, norm_inv, inv_pow]
  rw [hM]
  have hden : ‖wm‖ ^ 2 / 16 ≤ ‖u‖ ^ 2 := by nlinarith
  have hden0 : 0 < ‖wm‖ ^ 2 / 16 := by positivity
  calc -u.im / ‖u‖ ^ 2 ≤ (Cstar + Cp + 2) / ‖u‖ ^ 2 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (Cstar + Cp + 2) / (‖wm‖ ^ 2 / 16) :=
        div_le_div_of_nonneg_left hnum0 hden0 hden
    _ = 16 * (Cstar + Cp + 2) * (‖wm‖ ^ 2)⁻¹ := by field_simp

/-! ### Measurability and independence -/

/-- The entries of the GUE matrix are measurable in the sample. -/
private lemma minorLaw_measurable_entry (n : ℕ) (a b : Fin n) :
    Measurable fun ω : Ω n 1 => gueMat n ω a b := by
  unfold gueMat gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The matrix inverse is measurable. -/
private lemma minorLaw_measurable_inv {m : Type*} [Fintype m] [DecidableEq m] :
    Measurable fun A : Matrix m m ℂ => A⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hd : Measurable fun A : Matrix m m ℂ => A.det :=
    (continuous_id.matrix_det).measurable
  have ha : Measurable fun A : Matrix m m ℂ => A.adjugate i j :=
    (continuous_id.matrix_adjugate).measurable.eval_matrix
  exact (hd.inv).mul ha

/-- The two-index minor resolvent of the deformed GUE matrix is measurable in the sample. -/
private lemma minorLaw_measurable_resolvent (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (i : Fin n) (j : {k // k ≠ i}) :
    Measurable fun ω : Ω n 1 => resolventMat (minorMat (minorMat (gueMat n ω - B) i) j) z := by
  unfold resolventMat
  refine minorLaw_measurable_inv.comp ?_
  refine Measurable.of_eval_matrix _ fun k l => ?_
  by_cases h : k = l
  · subst h
    simp only [minorMat, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul]
    exact ((minorLaw_measurable_entry n _ _).sub measurable_const).sub measurable_const
  · simp only [minorMat, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Matrix.one_apply_ne h, smul_zero, sub_zero]
    exact (minorLaw_measurable_entry n _ _).sub measurable_const

/-- The two-index minor resolvent does not depend on row and column `j` of the GUE matrix. -/
private lemma minorLaw_offRow (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (i j : Fin n)
    (hji : j ≠ i) :
    OffRow n j fun ω : Ω n 1 =>
      resolventMat (minorMat (minorMat (gueMat n ω - B) i) ⟨j, hji⟩) z := by
  intro ω ω' h
  have hM : minorMat (minorMat (gueMat n ω - B) i) ⟨j, hji⟩ =
      minorMat (minorMat (gueMat n ω' - B) i) ⟨j, hji⟩ := by
    ext k l
    have hk : k.1.1 ≠ j := fun e => k.2 (Subtype.ext e)
    have hl : l.1.1 ≠ j := fun e => l.2 (Subtype.ext e)
    have hkl : gueMat n ω k.1.1 l.1.1 = gueMat n ω' k.1.1 l.1.1 := by
      have h1 := h (0, k.1.1, l.1.1) hk hl
      have h2 := h (0, l.1.1, k.1.1) hl hk
      have h3 := h (0, k.1.1, k.1.1) hk hk
      simp only [gueMat, gueBlock, Matrix.of_apply]
      simp [h1, h2, h3]
    simp [minorMat, hkl]
  simp only [resolventMat, hM]

/-! ### Asymptotics -/

/-- `n^ξ' / √(nη) ≤ n^{ξ' - δ/2}` for `η ≥ n^{-1+δ}`. -/
private lemma minorLaw_rate_le {n : ℕ} (hn : 1 ≤ n) {δ ξ' η : ℝ}
    (hη : (n : ℝ) ^ (-1 + δ) ≤ η) :
    (n : ℝ) ^ ξ' / Real.sqrt (n * η) ≤ (n : ℝ) ^ (ξ' - δ / 2) := by
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have h1 : (n : ℝ) ^ δ ≤ n * η := by
    calc (n : ℝ) ^ δ = (n : ℝ) * (n : ℝ) ^ (-1 + δ) := by
          conv_lhs => rw [show δ = 1 + (-1 + δ) by ring, Real.rpow_add hN0, Real.rpow_one]
      _ ≤ n * η := by gcongr
  have h2 : (n : ℝ) ^ (δ / 2) ≤ Real.sqrt (n * η) := by
    rw [Real.sqrt_eq_rpow]
    calc (n : ℝ) ^ (δ / 2) = ((n : ℝ) ^ δ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hN0.le]; congr 1; ring
      _ ≤ (n * η) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  calc (n : ℝ) ^ ξ' / Real.sqrt (n * η) ≤ (n : ℝ) ^ ξ' / (n : ℝ) ^ (δ / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h2
    _ = (n : ℝ) ^ (ξ' - δ / 2) := (Real.rpow_sub hN0 _ _).symm

/-- `n^{-θ} ≤ c` for large `n`, `θ > 0`, `c > 0`. -/
private lemma minorLaw_rpow_neg_le_eventually {θ : ℝ} (hθ : 0 < θ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-θ) ≤ c :=
  (((tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop).eventually
    (gt_mem_nhds hc)).mono fun _ h => h.le

/-- The three failure probabilities of the proof of the minor bound add up to at most `n^{-D}`
for large `n`, when `D + 3 ≤ 2 p ξ'`. -/
private lemma minorLaw_union_eventually {K ξ' D : ℝ} {p : ℕ} (hK : 0 < K) (hξ' : 0 < ξ')
    (hD : 0 < D) (hp : D + 3 ≤ 2 * p * ξ') :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-(D + 1)) +
      (n : ℝ) * (2 * Real.exp (-((n : ℝ) ^ ξ') ^ 2 / 2)) +
      ((n : ℝ) * n) * (K * ((n : ℝ) ^ ξ') ^ (-(2 * (p : ℝ)))) ≤ (n : ℝ) ^ (-D) := by
  have hT : Filter.Tendsto (fun x : ℝ => x ^ ((1 + D) / (2 * ξ')) * Real.exp (-(1 / 2) * x))
      Filter.atTop (nhds 0) := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (by norm_num)
  have hx : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (2 * ξ')) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  have hG := (hT.comp hx).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 6 by norm_num))
  filter_upwards [hG, Filter.eventually_ge_atTop 3, Filter.eventually_ge_atTop ⌈3 * K⌉₊]
    with n hG hn3 hn3K
  simp only [Function.comp_apply] at hG
  set N : ℝ := (n : ℝ) with hNdef
  have hN3 : 3 ≤ N := by rw [hNdef]; exact_mod_cast hn3
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hNK : 3 * K ≤ N := (Nat.le_ceil _).trans (by rw [hNdef]; exact_mod_cast hn3K)
  set X : ℝ := N ^ (-D) with hX
  have hX0 : 0 < X := Real.rpow_pos_of_pos hN0 _
  have hXD : N ^ D * X = 1 := by
    rw [hX, ← Real.rpow_add hN0]; simp
  -- the first term
  have h1 : N ^ (-(D + 1)) = X / N := by
    rw [hX, show -(D + 1) = -D + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one,
      div_eq_mul_inv]
  have h1' : N ^ (-(D + 1)) ≤ X / 3 := by
    rw [h1]
    exact div_le_div_of_nonneg_left hX0.le (by norm_num) hN3
  -- the Gaussian term
  have hgauss : N * (2 * Real.exp (-(N ^ ξ') ^ 2 / 2)) ≤ X / 3 := by
    have e1 : (N ^ ξ') ^ 2 = N ^ (2 * ξ') := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
    have e2 : (N ^ (2 * ξ')) ^ ((1 + D) / (2 * ξ')) = N ^ (1 + D) := by
      rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
    have e3 : N ^ (1 + D) = N * N ^ D := by
      rw [Real.rpow_add hN0, Real.rpow_one]
    rw [e2, e3] at hG
    have e4 : -(N ^ ξ') ^ 2 / 2 = -(1 / 2) * N ^ (2 * ξ') := by rw [e1]; ring
    rw [e4]
    have h5 : N * N ^ D * Real.exp (-(1 / 2) * N ^ (2 * ξ')) < 1 / 6 := hG
    have := mul_lt_mul_of_pos_right h5 hX0
    calc N * (2 * Real.exp (-(1 / 2) * N ^ (2 * ξ')))
        = 2 * (N * N ^ D * Real.exp (-(1 / 2) * N ^ (2 * ξ')) * X) := by
          have : N * (2 * Real.exp (-(1 / 2) * N ^ (2 * ξ'))) =
              N * (2 * Real.exp (-(1 / 2) * N ^ (2 * ξ'))) * (N ^ D * X) := by
            rw [hXD, mul_one]
          rw [this]; ring
      _ ≤ 2 * (1 / 6 * X) := by gcongr
      _ = X / 3 := by ring
  -- the polynomial term
  have hpoly : (N ^ ξ') ^ (-(2 * (p : ℝ))) ≤ X / N ^ 3 := by
    rw [← Real.rpow_mul hN0.le]
    have h1 : N ^ (ξ' * -(2 * (p : ℝ))) ≤ N ^ (-(D + 3)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
    have h2 : N ^ (-(D + 3)) = X / N ^ 3 := by
      rw [hX, show -(D + 3) = -D + -3 by ring, Real.rpow_add hN0, Real.rpow_neg hN0.le,
        div_eq_mul_inv]
      norm_num
    rw [← h2]; exact h1
  have hKt : (N * N) * (K * (N ^ ξ') ^ (-(2 * (p : ℝ)))) ≤ X / 3 := by
    calc (N * N) * (K * (N ^ ξ') ^ (-(2 * (p : ℝ)))) ≤ (N * N) * (K * (X / N ^ 3)) := by
          gcongr
      _ = K * X / N := by field_simp
      _ ≤ X / 3 := by
          rw [div_le_div_iff₀ hN0 (by norm_num)]
          nlinarith [mul_le_mul_of_nonneg_right hNK hX0.le]
  calc N ^ (-(D + 1)) + N * (2 * Real.exp (-(N ^ ξ') ^ 2 / 2)) +
        (N * N) * (K * (N ^ ξ') ^ (-(2 * (p : ℝ)))) ≤ X / 3 + X / 3 + X / 3 :=
        add_le_add (add_le_add h1' hgauss) hKt
    _ = X := by ring

/-- A union over a finite index type of sets of measure at most `ofReal c` has measure at most
`ofReal (card ι * c)`. -/
private lemma minorLaw_union_le {n : ℕ} {ι : Type*} [Fintype ι] {S : ι → Set (Ω n 1)} {c : ℝ}
    (h : ∀ x, μ n 1 (S x) ≤ ENNReal.ofReal c) :
    μ n 1 (⋃ x, S x) ≤ ENNReal.ofReal (Fintype.card ι * c) := by
  refine (measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun x _ => h x).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- Minor diagonal bound of Appendix G.1 [app:relative-local-law-proof] for diagonal `B`:
`Im G^{(i)}_jj ≤ C |(M_B)_jj|²` for all `i ≠ j`, with probability `≥ 1 - n^{-D}`. -/
theorem localLaw_minor_diag (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 1 ≤ C ∧ ∀ ε δ D : ℝ, 0 < ε → ε ≤ ε₀ → 0 < δ → 0 < D →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℂ) (E η : ℝ),
        DeformClass ε B → B.IsDiag → |E| ≤ 2 - κ₀ → (n : ℝ) ^ (-1 + δ) ≤ η → η ≤ Cstar →
        μ n 1 {ω | ∃ i j : Fin n, ∃ h : j ≠ i, C * ‖MB B (E + η * Complex.I) j j‖ ^ 2 <
            (resolventMat (minorMat (gueMat n ω - B) i) (E + η * Complex.I) ⟨j, h⟩ ⟨j, h⟩).im} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-D)) := by
  obtain ⟨ε₁, Cp, hε₁, hCp, hprof⟩ := deformed_profile κ₀ Cstar hκ₀ hκ₀' hC
  obtain ⟨ε₂, hε₂, havg⟩ := localLaw_avg κ₀ Cstar hκ₀ hκ₀' hC
  have hCp0 : 0 < Cp := by linarith
  refine ⟨min ε₁ ε₂, max 1 (16 * (Cstar + Cp + 2)), lt_min hε₁ hε₂, le_max_left _ _, ?_⟩
  intro ε δ D hε hεε₀ hδ hD
  have hεε₁ : ε ≤ ε₁ := hεε₀.trans (min_le_left _ _)
  have hεε₂ : ε ≤ ε₂ := hεε₀.trans (min_le_right _ _)
  obtain ⟨n₁, hn₁⟩ := havg ε δ (δ / 4) (D + 1) hε hεε₂ hδ (by positivity) (by linarith)
  set ξ' : ℝ := δ / 16 with hξ'
  have hξ'0 : 0 < ξ' := by positivity
  set p : ℕ := ⌈(D + 3) / (2 * ξ')⌉₊ + 1 with hp
  have hp' : D + 3 ≤ 2 * (p : ℝ) * ξ' := by
    have h1 : (D + 3) / (2 * ξ') ≤ (p : ℝ) := by
      rw [hp]; push_cast; linarith [Nat.le_ceil ((D + 3) / (2 * ξ'))]
    have := (div_le_iff₀ (by positivity : 0 < 2 * ξ')).mp h1
    linarith
  obtain ⟨K, hK, hQL⟩ := gue_quadForm_tail p
  set C₁ : ℝ := Real.sqrt Cstar + Real.sqrt (Cp + 3) + 2 with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  have e2 := minorLaw_rpow_neg_le_eventually (θ := δ / 4) (by positivity)
    (c := (2 * Cp)⁻¹) (by positivity)
  have e3 := minorLaw_rpow_neg_le_eventually (θ := 7 * δ / 16) (by positivity)
    (c := (4 * Cp * C₁)⁻¹) (by positivity)
  have e4 := minorLaw_union_eventually hK hξ'0 hD hp'
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    ((Filter.eventually_ge_atTop 3).and (e2.and (e3.and e4)))
  refine ⟨max n₀ n₁, ?_⟩
  intro n hn B E η hcl hBd hE hηlow hηC
  obtain ⟨hn3, he2, he3, he4⟩ := hn₀ n ((le_max_left _ _).trans hn)
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := hn1
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < n := by linarith
  have hη0 : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hηlow
  have hz : 0 < (E + η * Complex.I).im := by simpa using hη0
  set z : ℂ := E + η * Complex.I with hzdef
  set t : ℝ := (n : ℝ) ^ ξ' with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
  have ht1 : 1 ≤ t := Real.one_le_rpow hN1 hξ'0.le
  have hnη : 1 ≤ (n : ℝ) * η := by
    have : (n : ℝ) ^ δ ≤ n * η := by
      calc (n : ℝ) ^ δ = (n : ℝ) * (n : ℝ) ^ (-1 + δ) := by
            conv_lhs => rw [show δ = 1 + (-1 + δ) by ring, Real.rpow_add hN0, Real.rpow_one]
        _ ≤ n * η := by gcongr
    exact (Real.one_le_rpow hN1 hδ.le).trans this
  have hBh : B.IsHermitian := hcl.1
  have : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  obtain ⟨hlo, hhi, -⟩ := hprof (Fin n) B ε E η hε.le hεε₁ hcl hE hη0 hηC
  -- the three exceptional events
  set SA : Set (Ω n 1) := {ω | (n : ℝ) ^ (δ / 4) / Real.sqrt (n * η) <
    ‖ntr (resolventMat (gueMat n ω - B) z) - mB B z‖} with hSA
  set SD : Fin n → Set (Ω n 1) := fun j => {ω | t / Real.sqrt n < ‖gueMat n ω j j‖} with hSD
  set SQ : Fin n × Fin n → Set (Ω n 1) := fun x => {ω | ∃ h : x.2 ≠ x.1,
    t / n * Real.sqrt (∑ k, ∑ l, ‖resolventMat (minorMat (minorMat (gueMat n ω - B) x.1)
      ⟨x.2, h⟩) z k l‖ ^ 2) <
      ‖star (fun k : {k : {k // k ≠ x.1} // k ≠ ⟨x.2, h⟩} => gueMat n ω k.1.1 x.2) ⬝ᵥ
        (resolventMat (minorMat (minorMat (gueMat n ω - B) x.1) ⟨x.2, h⟩) z *ᵥ
          fun k : {k : {k // k ≠ x.1} // k ≠ ⟨x.2, h⟩} => gueMat n ω k.1.1 x.2) -
        (n : ℂ)⁻¹ * (resolventMat (minorMat (minorMat (gueMat n ω - B) x.1) ⟨x.2, h⟩) z).trace‖}
    with hSQ
  have hSDm : ∀ j, μ n 1 (SD j) ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := fun j =>
    gue_diag_tail n j ht0.le
  have hSQm : ∀ x : Fin n × Fin n, μ n 1 (SQ x) ≤ ENNReal.ofReal (K * t ^ (-(2 * (p : ℝ)))) := by
    intro x
    by_cases h : x.2 ≠ x.1
    · refine le_trans (measure_mono ?_) (hQL n x.2 (κ := {k : {k // k ≠ x.1} // k ≠ ⟨x.2, h⟩})
        (fun k => k.1.1) (fun a b hab => Subtype.ext (Subtype.ext hab))
        (fun k hk => k.2 (Subtype.ext hk))
        (fun ω => resolventMat (minorMat (minorMat (gueMat n ω - B) x.1) ⟨x.2, h⟩) z)
        (minorLaw_measurable_resolvent n B z x.1 ⟨x.2, h⟩)
        (minorLaw_offRow n B z x.1 x.2 h) t ht0)
      rintro ω ⟨h', hω⟩
      exact hω
    · have : SQ x = ∅ := by
        ext ω
        simp only [hSQ, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h', -⟩
        exact h h'
      rw [this]
      simp
  have hbad : {ω : Ω n 1 | ∃ i j : Fin n, ∃ h : j ≠ i,
      (max 1 (16 * (Cstar + Cp + 2))) * ‖MB B z j j‖ ^ 2 <
        (resolventMat (minorMat (gueMat n ω - B) i) z ⟨j, h⟩ ⟨j, h⟩).im} ⊆
      (SA ∪ ⋃ j, SD j) ∪ ⋃ x, SQ x := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hnot
    obtain ⟨⟨hA, hDn⟩, hQn⟩ := hnot
    obtain ⟨i, j, h, hlt⟩ := hω
    apply absurd hlt
    rw [not_lt]
    have hA' : ‖ntr (resolventMat (gueMat n ω - B) z) - mB B z‖ ≤ (2 * Cp)⁻¹ := by
      have h1 : ‖ntr (resolventMat (gueMat n ω - B) z) - mB B z‖ ≤
          (n : ℝ) ^ (δ / 4) / Real.sqrt (n * η) := not_lt.mp hA
      refine h1.trans ((minorLaw_rate_le hn1 hηlow).trans ?_)
      have e : δ / 4 - δ / 2 = -(δ / 4) := by ring
      rw [e]; exact he2
    have hsmall : C₁ * (t / Real.sqrt (n * η)) ≤ (4 * Cp)⁻¹ := by
      have h1 : t / Real.sqrt (n * η) ≤ (n : ℝ) ^ (-(7 * δ / 16)) := by
        refine (minorLaw_rate_le hn1 hηlow).trans (le_of_eq ?_)
        congr 1; rw [hξ']; ring
      calc C₁ * (t / Real.sqrt (n * η)) ≤ C₁ * (4 * Cp * C₁)⁻¹ :=
            mul_le_mul_of_nonneg_left (h1.trans he3) hC₁0.le
        _ = (4 * Cp)⁻¹ := by field_simp
    have hVd : ‖gueMat n ω j j‖ ≤ t / Real.sqrt n := not_lt.mp (hDn j)
    have hm1 : Cp⁻¹ ≤ (mB B z).im := hlo
    have hm2 : (mB B z).im ≤ Cp := hhi
    have hstep := minorLaw_step hn0 (V := gueMat n ω) (B := B) (gueBlock_isHermitian n 1 ω 0) hBh
      hBd (E := E) (η := η) (t := t) (Cp := Cp) (Cstar := Cstar) (m := mB B z) (i := i)
      (j := j) h hη0 hηC hnη ht1 hCp hm1 hm2 hA' hsmall hVd
      (not_lt.mp (fun hlt => hQn (i, j) ⟨h, hlt⟩))
    have hw : 0 < (z + mB B z).im := by
      rw [Complex.add_im]
      have : 0 < Cp⁻¹ := inv_pos.mpr hCp0
      linarith
    have hMB : MB B z j j = (-B j j - (z + mB B z))⁻¹ := minorLaw_deformedMat_diag hBd hBh hw j
    rw [hMB]
    refine hstep.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  calc μ n 1 {ω : Ω n 1 | ∃ i j : Fin n, ∃ h : j ≠ i,
        (max 1 (16 * (Cstar + Cp + 2))) * ‖MB B z j j‖ ^ 2 <
          (resolventMat (minorMat (gueMat n ω - B) i) z ⟨j, h⟩ ⟨j, h⟩).im}
      ≤ μ n 1 ((SA ∪ ⋃ j, SD j) ∪ ⋃ x, SQ x) := measure_mono hbad
    _ ≤ μ n 1 (SA ∪ ⋃ j, SD j) + μ n 1 (⋃ x, SQ x) := measure_union_le _ _
    _ ≤ (μ n 1 SA + μ n 1 (⋃ j, SD j)) + μ n 1 (⋃ x, SQ x) := by
        gcongr; exact measure_union_le _ _
    _ ≤ (ENNReal.ofReal ((n : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal (Fintype.card (Fin n) * (2 * Real.exp (-t ^ 2 / 2)))) +
        ENNReal.ofReal (Fintype.card (Fin n × Fin n) * (K * t ^ (-(2 * (p : ℝ))))) := by
        gcongr
        · exact hn₁ n ((le_max_right _ _).trans hn) B E η hcl hE hηlow hηC
        · exact minorLaw_union_le hSDm
        · exact minorLaw_union_le hSQm
    _ = ENNReal.ofReal ((n : ℝ) ^ (-(D + 1)) + (n : ℝ) * (2 * Real.exp (-t ^ 2 / 2)) +
          ((n : ℝ) * n) * (K * t ^ (-(2 * (p : ℝ))))) := by
        rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_fin]
        push_cast
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal he4

end LSBA
