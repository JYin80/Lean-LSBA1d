import LSBA.Dyson.DeformedRoot

/-!
# Semicircle bounds

`m_sc(z)` as the Herglotz solution with `B = 0` on one coordinate, and the bulk bounds `Im m_sc ≥
c`, `|1 − m_sc²| ≥ c`, `|m_sc − 1/m_sc| ≥ c` on `|E| ≤ 2 − κ₀`, `0 < η ≤ H` (inputs of Lemma A.21
[da:lem:deformed]).
-/

open scoped Matrix

noncomputable section
open scoped Classical

namespace LSBA

/-- The semicircle Stieltjes transform `m_sc(z)`: the Herglotz solution of Lemma A.21
[da:lem:deformed] at `B = 0`, i.e. of `m = -(z + m)⁻¹`. -/
def msc (z : ℂ) : ℂ := mB (0 : Matrix (Fin 1) (Fin 1) ℂ) z

/-- The scalar form of the root equation at `B = 0`. -/
private lemma semicircle_root_eq {z m : ℂ} (hz : 0 < z.im)
    (hm : IsDeformedRoot (0 : Matrix (Fin 1) (Fin 1) ℂ) z m) : m * (z + m) = -1 := by
  have hw : z + m ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith [hm.1]
  have hinv : deformedMat (0 : Matrix (Fin 1) (Fin 1) ℂ) z m =
      Matrix.of fun _ _ => (-(z + m))⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply]
    have h3 : (-m + -z) = -(z + m) := by ring
    rw [h3, inv_neg, mul_neg, mul_inv_cancel₀ hw, neg_neg]
  have h2 := hm.2
  simp only [deformedMap, ntr, hinv, Matrix.trace] at h2
  simp at h2
  have h3 : (-m + -z) = -(z + m) := by ring
  rw [h3] at h2
  calc m * (z + m) = (-(z + m))⁻¹ * (z + m) := by rw [← h2]
    _ = -1 := by rw [inv_neg, neg_mul, inv_mul_cancel₀ hw]

/-- The real and imaginary parts `a = E + 2x`, `b = η + 2y` of `m - m⁻¹ = w + 2m`, with
`m = x + i y` and `w = E + i η`, satisfy `b² = a² + 4 + η² - E²` when `m (w + m) = -1`. -/
private lemma semicircle_real_eq {x y E η : ℝ} (h1 : x * (E + x) - y * (η + y) = -1) :
    (η + 2 * y) ^ 2 = (E + 2 * x) ^ 2 + (4 + η ^ 2 - E ^ 2) := by
  linear_combination (-4) * h1

/-- Bounds in terms of any `m` with `Im m > 0`, `|m| < 1` and `m (w + m) = -1`,
`w = E + i η`. -/
private lemma semicircle_core (κ₀ H : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hH : 0 < H)
    {E η : ℝ} (hE : |E| ≤ 2 - κ₀) (hη : 0 < η) (hηH : η ≤ H) {m : ℂ} (hy : 0 < m.im)
    (hn : ‖m‖ < 1) (hroot : m * (E + η * Complex.I + m) = -1) :
    Real.sqrt (κ₀ * (4 - κ₀)) ^ 2 / (4 * (1 + H)) ≤ m.im ∧
      Real.sqrt (κ₀ * (4 - κ₀)) ^ 2 / (4 * (1 + H)) * Real.sqrt (κ₀ * (4 - κ₀)) ≤
        ‖1 - m ^ 2‖ ∧
      Real.sqrt (κ₀ * (4 - κ₀)) ≤ ‖m - m⁻¹‖ := by
  set s₀ := Real.sqrt (κ₀ * (4 - κ₀)) with hs₀
  have hpos : 0 < κ₀ * (4 - κ₀) := mul_pos hκ₀ (by linarith)
  have hs₀sq : s₀ ^ 2 = κ₀ * (4 - κ₀) := Real.sq_sqrt hpos.le
  have hs₀pos : 0 < s₀ := Real.sqrt_pos.2 hpos
  have hm0 : m ≠ 0 := fun h => by simp [h] at hy
  have hinv : m⁻¹ = -(E + η * Complex.I) - m := by
    field_simp
    linear_combination hroot
  have hs : m - m⁻¹ = (E + η * Complex.I) + 2 * m := by rw [hinv]; ring
  set x := m.re with hx
  set y := m.im with hy'
  have h1 : x * (E + x) - y * (η + y) = -1 := by
    have := congrArg Complex.re hroot
    simp at this
    linarith
  have hb := semicircle_real_eq h1
  have hE2 : E ^ 2 ≤ (2 - κ₀) ^ 2 := by
    have := abs_le.1 hE
    nlinarith
  have hP : s₀ ^ 2 + η ^ 2 ≤ 4 + η ^ 2 - E ^ 2 := by nlinarith
  have hnorms : ‖m - m⁻¹‖ ^ 2 = (E + 2 * x) ^ 2 + (η + 2 * y) ^ 2 := by
    rw [hs, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hsep : s₀ ≤ ‖m - m⁻¹‖ := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [norm_nonneg (m - m⁻¹), sq_nonneg (E + 2 * x), sq_nonneg η]
  have hb2 : s₀ ^ 2 + η ^ 2 ≤ (η + 2 * y) ^ 2 := by nlinarith [sq_nonneg (E + 2 * x)]
  have hyn : y ≤ ‖m‖ := Complex.abs_im_le_norm m |>.trans' (le_abs_self _)
  have him : s₀ ^ 2 / (4 * (1 + H)) ≤ y := by
    rw [div_le_iff₀ (by linarith)]
    have hy1 : y < 1 := lt_of_le_of_lt hyn hn
    nlinarith
  refine ⟨him, ?_, hsep⟩
  have hid : 1 - m ^ 2 = -(m * (m - m⁻¹)) := by
    field_simp
    ring
  rw [hid, norm_neg, norm_mul]
  have hmn : y ≤ ‖m‖ := hyn
  have hcs : 0 ≤ s₀ ^ 2 / (4 * (1 + H)) := by positivity
  calc s₀ ^ 2 / (4 * (1 + H)) * s₀ ≤ y * s₀ := by gcongr
    _ ≤ ‖m‖ * ‖m - m⁻¹‖ := by gcongr

/-- Bulk bounds for the semicircle branch used in the proof of Lemma A.21 [da:lem:deformed]:
`Im m_sc ≥ c`, the stability gap `|1 - m_sc²| ≥ c`, and the root separation
`|m_sc - 1/m_sc| ≥ c`, for `|E| ≤ 2 - κ₀` and `0 < η ≤ H`. -/
theorem semicircle_bounds (κ₀ H : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hH : 0 < H) :
    ∃ c : ℝ, 0 < c ∧ ∀ E η : ℝ, |E| ≤ 2 - κ₀ → 0 < η → η ≤ H →
      c ≤ (msc (E + η * Complex.I)).im ∧ c ≤ ‖1 - msc (E + η * Complex.I) ^ 2‖ ∧
        c ≤ ‖msc (E + η * Complex.I) - (msc (E + η * Complex.I))⁻¹‖ := by
  have hpos : 0 < κ₀ * (4 - κ₀) := mul_pos hκ₀ (by linarith)
  have hs₀pos : 0 < Real.sqrt (κ₀ * (4 - κ₀)) := Real.sqrt_pos.2 hpos
  have hs₀sq : Real.sqrt (κ₀ * (4 - κ₀)) ^ 2 = κ₀ * (4 - κ₀) := Real.sq_sqrt hpos.le
  set s₀ := Real.sqrt (κ₀ * (4 - κ₀))
  have hcpos : 0 < s₀ ^ 2 / (4 * (1 + H)) := by positivity
  have hc1 : s₀ ^ 2 / (4 * (1 + H)) ≤ 1 := by
    rw [div_le_one (by linarith)]
    nlinarith
  refine ⟨min (s₀ ^ 2 / (4 * (1 + H))) (s₀ ^ 2 / (4 * (1 + H)) * s₀), lt_min hcpos
    (mul_pos hcpos hs₀pos), fun E η hE hη hηH => ?_⟩
  have hz : 0 < (E + η * Complex.I).im := by simpa using hη
  have hroot := isDeformedRoot_mB (Matrix.isHermitian_zero (n := Fin 1) (α := ℂ)) hz
  have hr := semicircle_root_eq hz hroot
  have hn := IsDeformedRoot.norm_lt_one (Matrix.isHermitian_zero (n := Fin 1) (α := ℂ)) hz hroot
  obtain ⟨h1, h2, h3⟩ := semicircle_core κ₀ H hκ₀ hκ₀' hH hE hη hηH hroot.1 hn hr
  have hmin1 := min_le_left (s₀ ^ 2 / (4 * (1 + H))) (s₀ ^ 2 / (4 * (1 + H)) * s₀)
  have hmin2 := min_le_right (s₀ ^ 2 / (4 * (1 + H))) (s₀ ^ 2 / (4 * (1 + H)) * s₀)
  have hle : s₀ ^ 2 / (4 * (1 + H)) * s₀ ≤ s₀ := by nlinarith
  exact ⟨hmin1.trans h1, hmin2.trans h2, (hmin2.trans hle).trans h3⟩

end LSBA
