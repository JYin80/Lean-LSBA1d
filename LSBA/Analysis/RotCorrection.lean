import LSBA.Upper.CoercivityMap

/-!
# Rank-two skew-Hermitian corrections

For vectors `v, w ∈ ℂ^n`, the matrix
`L = ‖v‖⁻² (w v* - v w*) - ‖v‖⁻⁴ (v* w) v v*` of (9.9) [us:eq:L]. If `Re(v* w) = 0`, then
`L* = -L` and, for `v ≠ 0`, `L v = w` (9.12) [su:eq:correction-identities]: `L` realizes `w` as
an infinitesimal unitary rotation of `v`. In general `‖L‖_HS ≤ 3 ‖v‖⁻¹ ‖w‖` (Section 9.3
[su:sec:generator-bounds], the terminal correction).
-/

open Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `v* v` is the real number `Σ ‖v i‖²`. -/
private lemma RotCorrection_dot_self {n : Type*} [Fintype n] (v : n → ℂ) :
    star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp [dotProduct, Complex.conj_mul', Complex.ofReal_sum]

private lemma RotCorrection_sum_pos {n : Type*} [Fintype n] {v : n → ℂ} (hv : v ≠ 0) :
    0 < ∑ i, ‖v i‖ ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact Finset.sum_pos' (fun _ _ => by positivity)
    ⟨i, Finset.mem_univ _, by have := norm_pos_iff.mpr hi; positivity⟩

private lemma RotCorrection_hsSq_vecMulVec {m n : Type*} [Fintype m] [Fintype n]
    (x : m → ℂ) (y : n → ℂ) :
    hsSq (Matrix.vecMulVec x y) = (∑ i, ‖x i‖ ^ 2) * ∑ j, ‖y j‖ ^ 2 := by
  simp [hsSq, Matrix.vecMulVec, mul_pow, Finset.sum_mul_sum]

private lemma RotCorrection_hsSq_smul {m n : Type*} [Fintype m] [Fintype n] (z : ℂ)
    (A : Matrix m n ℂ) : hsSq (z • A) = ‖z‖ ^ 2 * hsSq A := by
  simp [hsSq, mul_pow, Finset.mul_sum]

private lemma RotCorrection_hsSq_neg {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : hsSq (-A) = hsSq A := by
  simp [hsSq]

private lemma RotCorrection_sqrt_hsSq_add {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) :
    √(hsSq (A + B)) ≤ √(hsSq A) + √(hsSq B) := by
  letI := Matrix.frobeniusNormedAddCommGroup (m := m) (n := n) (α := ℂ)
  have h : ∀ M : Matrix m n ℂ, √(hsSq M) = ‖M‖ := by
    intro M
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
    simp only [hsSq, Real.rpow_two]
  rw [h, h, h]
  exact norm_add_le _ _

private lemma RotCorrection_sqrt_hsSq_sub {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) :
    √(hsSq (A - B)) ≤ √(hsSq A) + √(hsSq B) := by
  rw [sub_eq_add_neg]
  have := RotCorrection_sqrt_hsSq_add A (-B)
  rwa [RotCorrection_hsSq_neg] at this

/-- `L = ‖v‖⁻² (w v* - v w*) - ‖v‖⁻⁴ (v* w) v v*` of (9.9) [us:eq:L], with `‖v‖² = v* v`. -/
def rotCorr {n : Type*} [Fintype n] (v w : n → ℂ) : Matrix n n ℂ :=
  (star v ⬝ᵥ v)⁻¹ • (Matrix.vecMulVec w (star v) - Matrix.vecMulVec v (star w)) -
    ((star v ⬝ᵥ v)⁻¹ ^ 2 * (star v ⬝ᵥ w)) • Matrix.vecMulVec v (star v)

/-- (9.12) [su:eq:correction-identities]: if `Re(v* w) = 0`, then `L* = -L`, and `L v = w` for
`v ≠ 0`. -/
theorem rotCorr_spec {n : Type*} [Fintype n] {v w : n → ℂ} (hvw : (star v ⬝ᵥ w).re = 0) :
    (rotCorr v w)ᴴ = -rotCorr v w ∧ (v ≠ 0 → rotCorr v w *ᵥ v = w) := by
  have ha := RotCorrection_dot_self v
  have hc : star (star v ⬝ᵥ w) = -(star v ⬝ᵥ w) := by
    apply Complex.ext <;> simp [hvw]
  have hs : star (star v ⬝ᵥ v) = star v ⬝ᵥ v := by rw [ha]; exact Complex.conj_ofReal _
  constructor
  · ext i j
    simp only [rotCorr, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Matrix.neg_apply, smul_eq_mul, star_sub, star_mul', star_inv₀, hs,
      star_pow, hc, Pi.star_apply, star_star]
    ring
  · intro hv
    have hne : star v ⬝ᵥ v ≠ 0 := by
      rw [ha]; exact_mod_cast (RotCorrection_sum_pos hv).ne'
    ext i
    simp only [rotCorr, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hwv : star w ⬝ᵥ v = -(star v ⬝ᵥ w) := by
      rw [← hc]; simp [dotProduct, mul_comm]
    simp only [op_smul_eq_mul, hwv]
    field_simp
    ring

/-- `‖L‖_HS ≤ 3 ‖v‖⁻¹ ‖w‖` (Section 9.3 [su:sec:generator-bounds], the terminal correction),
squared. -/
theorem hsSq_rotCorr_le {n : Type*} [Fintype n] {v : n → ℂ} (hv : v ≠ 0) (w : n → ℂ) :
    hsSq (rotCorr v w) ≤ 9 * (∑ i, ‖w i‖ ^ 2) / ∑ i, ‖v i‖ ^ 2 := by
  have hSv := RotCorrection_sum_pos hv
  have hSw : 0 ≤ ∑ i, ‖w i‖ ^ 2 := by positivity
  have ha := RotCorrection_dot_self v
  set Sv := ∑ i, ‖v i‖ ^ 2 with hSvdef
  set Sw := ∑ i, ‖w i‖ ^ 2 with hSwdef
  set s := √Sv with hs
  set t := √Sw with ht
  have hs0 : 0 < s := Real.sqrt_pos.mpr hSv
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hSv' : Sv = s ^ 2 := (Real.sq_sqrt hSv.le).symm
  have hSw' : Sw = t ^ 2 := (Real.sq_sqrt hSw).symm
  -- `√(hsSq (z • A)) = ‖z‖ √(hsSq A)`
  have hsm : ∀ (z : ℂ) (A : Matrix n n ℂ), √(hsSq (z • A)) = ‖z‖ * √(hsSq A) := by
    intro z A
    rw [RotCorrection_hsSq_smul, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  -- `√(hsSq (x y*)) = ‖x‖ ‖y‖`
  have hrk : ∀ x y : n → ℂ, √(hsSq (Matrix.vecMulVec x (star y))) =
      √(∑ i, ‖x i‖ ^ 2) * √(∑ i, ‖y i‖ ^ 2) := by
    intro x y
    rw [RotCorrection_hsSq_vecMulVec, Real.sqrt_mul (by positivity)]
    simp
  -- Cauchy–Schwarz: `|v* w| ≤ ‖v‖ ‖w‖`
  have hcs : ‖star v ⬝ᵥ w‖ ≤ s * t := by
    calc ‖star v ⬝ᵥ w‖ ≤ ∑ i, ‖star (v i) * w i‖ := by
          simpa [dotProduct] using norm_sum_le Finset.univ (fun i => star (v i) * w i)
      _ = ∑ i, ‖v i‖ * ‖w i‖ := by simp
      _ ≤ s * t := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hX := hrk w v
  have hY := hrk v w
  have hZ := hrk v v
  have hZ' : √(hsSq (Matrix.vecMulVec v (star v))) = s ^ 2 := by
    rw [hZ, ← hs, sq]
  rw [← hs, ← ht] at hX hY
  have hinv : ‖(star v ⬝ᵥ v)⁻¹‖ = (s ^ 2)⁻¹ := by
    rw [ha, hSv']; simp [Complex.norm_real]
  have hL : √(hsSq (rotCorr v w)) ≤ 3 * t / s := by
    unfold rotCorr
    refine (RotCorrection_sqrt_hsSq_sub _ _).trans ?_
    rw [hsm, hsm]
    have h1 := RotCorrection_sqrt_hsSq_sub (Matrix.vecMulVec w (star v))
      (Matrix.vecMulVec v (star w))
    rw [hX, hY] at h1
    have hcoef : ‖(star v ⬝ᵥ v)⁻¹ ^ 2 * (star v ⬝ᵥ w)‖ ≤ (s ^ 2)⁻¹ ^ 2 * (s * t) := by
      rw [norm_mul, norm_pow, hinv]
      exact mul_le_mul_of_nonneg_left hcs (by positivity)
    rw [hinv, hZ']
    have h2 : (s ^ 2)⁻¹ * √(hsSq (Matrix.vecMulVec w (star v) - Matrix.vecMulVec v (star w))) ≤
        (s ^ 2)⁻¹ * (t * s + s * t) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : ‖(star v ⬝ᵥ v)⁻¹ ^ 2 * (star v ⬝ᵥ w)‖ * s ^ 2 ≤ (s ^ 2)⁻¹ ^ 2 * (s * t) * s ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    have h4 : (s ^ 2)⁻¹ * (t * s + s * t) + (s ^ 2)⁻¹ ^ 2 * (s * t) * s ^ 2 = 3 * t / s := by
      field_simp; ring
    linarith
  have hL0 : 0 ≤ √(hsSq (rotCorr v w)) := Real.sqrt_nonneg _
  have hsq : hsSq (rotCorr v w) = √(hsSq (rotCorr v w)) ^ 2 := by
    rw [Real.sq_sqrt]; unfold hsSq; positivity
  calc hsSq (rotCorr v w) = √(hsSq (rotCorr v w)) ^ 2 := hsq
    _ ≤ (3 * t / s) ^ 2 := pow_le_pow_left₀ hL0 hL 2
    _ = 9 * Sw / Sv := by rw [hSv', hSw']; field_simp; ring

end LSBA
