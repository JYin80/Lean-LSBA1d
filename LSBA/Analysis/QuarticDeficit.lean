import Mathlib

/-!
# The quartic deficit

The scalar deficit `¾ + r/4 - r^{1/4}` of the proof of Lemma 8.11 [up:lem:angular]: it is
nonnegative for `r ≥ 0`, and at least `t²/32` when `|log r| > t` with `0 < t ≤ 1`.
-/

open Real

namespace LSBA

/-- `¾ + r/4 - r^{1/4} ≥ 0` for `r ≥ 0` (proof of Lemma 8.11 [up:lem:angular]). -/
theorem quarticDeficit_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ 3 / 4 + r / 4 - r ^ (1 / 4 : ℝ) := by
  have hs : 0 ≤ r ^ (1 / 4 : ℝ) := Real.rpow_nonneg hr _
  have h4 : (r ^ (1 / 4 : ℝ)) ^ 4 = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]; norm_num
  set s := r ^ (1 / 4 : ℝ)
  rw [← h4]
  nlinarith [mul_nonneg (sq_nonneg (s - 1)) (by positivity : 0 ≤ s ^ 2 + 2 * s + 3)]

/-- `¾ + r/4 - r^{1/4} ≥ t²/32` for `r > 0` with `|log r| > t`, `0 < t ≤ 1` (proof of Lemma 8.11
[up:lem:angular]). -/
theorem sq_div_le_quarticDeficit {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (ht1 : t ≤ 1)
    (hrt : t < |Real.log r|) : t ^ 2 / 32 ≤ 3 / 4 + r / 4 - r ^ (1 / 4 : ℝ) := by
  have h4 : (r ^ (1 / 4 : ℝ)) ^ 4 = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; norm_num
  have hsexp : r ^ (1 / 4 : ℝ) = Real.exp (Real.log r / 4) := by
    rw [Real.rpow_def_of_pos hr]; congr 1; ring
  have hspos : 0 < r ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hr _
  have key : 3 / 4 + r / 4 - r ^ (1 / 4 : ℝ)
      = (r ^ (1 / 4 : ℝ) - 1) ^ 2 * ((r ^ (1 / 4 : ℝ)) ^ 2 + 2 * r ^ (1 / 4 : ℝ) + 3) / 4 := by
    linear_combination (-1 / 4 : ℝ) * h4
  rw [key]
  rw [hsexp] at hspos ⊢
  set u := Real.log r with hu
  set s := Real.exp (u / 4) with hs
  rcases lt_abs.mp hrt with h | h
  · -- `u > t`
    have h1 : u / 4 + 1 ≤ s := Real.add_one_le_exp (u / 4)
    have h2 : 1 + t / 4 < s := by linarith
    have h3 : (t / 4) ^ 2 ≤ (s - 1) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    nlinarith [mul_nonneg (sq_nonneg (s - 1)) (by nlinarith : 0 ≤ s ^ 2 + 2 * s - 3),
      sq_nonneg t]
  · -- `u < -t`
    have hx : 0 ≤ t / 4 := by positivity
    have hP : 1 + t / 4 + (t / 4) ^ 2 / 2 ≤ Real.exp (t / 4) :=
      Real.quadratic_le_exp_of_nonneg hx
    have hse : s * Real.exp (t / 4) < 1 := by
      rw [hs, ← Real.exp_add]
      rw [Real.exp_lt_one_iff]; linarith
    have hPpos : 0 < 1 + t / 4 + (t / 4) ^ 2 / 2 := by positivity
    have hsP : s * (1 + t / 4 + (t / 4) ^ 2 / 2) < 1 := by
      calc s * (1 + t / 4 + (t / 4) ^ 2 / 2) ≤ s * Real.exp (t / 4) :=
            mul_le_mul_of_nonneg_left hP hspos.le
        _ < 1 := hse
    have hq : s < 1 - 7 * (t / 4) / 8 := by
      by_contra hcon
      rw [not_lt] at hcon
      have hxle : t / 4 ≤ 1 / 4 := by linarith
      have : (1 - 7 * (t / 4) / 8) * (1 + t / 4 + (t / 4) ^ 2 / 2) ≥ 1 := by
        nlinarith [mul_nonneg hx hx, mul_nonneg (mul_nonneg hx hx) hx,
          mul_nonneg hx (sub_nonneg.mpr hxle), mul_nonneg (mul_nonneg hx hx) (sub_nonneg.mpr hxle)]
      nlinarith [mul_le_mul_of_nonneg_right hcon hPpos.le]
    have h3 : (7 * (t / 4) / 8) ^ 2 ≤ (s - 1) ^ 2 := by
      have h5 : 7 * (t / 4) / 8 ≤ 1 - s := by linarith
      have := pow_le_pow_left₀ (by positivity) h5 2
      nlinarith
    nlinarith [mul_nonneg (sq_nonneg (s - 1)) (by positivity : 0 ≤ s ^ 2 + 2 * s),
      sq_nonneg t]

end LSBA
