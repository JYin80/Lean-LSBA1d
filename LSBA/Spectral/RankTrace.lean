import LSBA.Spectral.SchattenBand
import LSBA.Spectral.Counts
import LSBA.Spectral.BorderInverse
import LSBA.Transfer.FlagAction

/-!
# Rank surrogates and ranges of image projections

The smooth rank surrogate `2 Tr (M (M + t²)⁻¹) = Σ_k 2 m_k/(m_k + t²)` of a positive matrix `M`.
For `M = Y* Y` it dominates the number of singular values of `Y` above `t` and is dominated by
`2 t^{-p} Tr |Y|^p` for `0 < p ≤ 2`; this is the rank estimate (9.53)
[su:eq:retained-rank-moment] in a form that is a rational function of `Y`. The image projection
`flagProj T P` onto `T (ran P)` has the trace of `P` and range inside `T (ran P)`. An orthogonal
projection `Π` with `|v* x|² ≤ K ‖x‖²` on its range has `‖Π v‖² ≤ K`; this restricts the range
estimates (9.42) [us:eq:relative] and (9.52) [nc:eq:compression] to the retained projection.
-/

open MeasureTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rank surrogate `2 Tr (M (M + t²)⁻¹)`. -/
def rankSurr (t : ℝ) (M : Matrix n n ℂ) : ℝ :=
  2 * (M * (M + ((t ^ 2 : ℝ) : ℂ) • 1)⁻¹).trace.re

open scoped ComplexOrder in
/-- The eigenvalues of `Y* Y` are nonnegative. -/
private lemma rankTrace_eigenvalues_nonneg (Y : Matrix n n ℂ) (k : n) :
    0 ≤ (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvalues k :=
  (Matrix.posSemidef_conjTranspose_mul_self Y).eigenvalues_nonneg k

/-- The real part of `Tr (M (M + s)⁻¹)` is `Σ_k λ_k / (λ_k + s)` for a Hermitian `M` with
eigenvalues `λ_k ≥ 0` and `s > 0`. -/
private lemma rankTrace_trace_surr {M : Matrix n n ℂ} (hH : M.IsHermitian) {s : ℝ} (hs : 0 < s)
    (hnn : ∀ k, 0 ≤ hH.eigenvalues k) :
    (M * (M + (s : ℂ) • 1)⁻¹).trace.re = ∑ k, hH.eigenvalues k / (hH.eigenvalues k + s) := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  set D : Matrix n n ℂ := Matrix.diagonal (fun k => ((hH.eigenvalues k : ℝ) : ℂ)) with hD
  set E : Matrix n n ℂ := Matrix.diagonal (fun k => (((hH.eigenvalues k + s)⁻¹ : ℝ) : ℂ)) with hE
  have hMD : M = U * D * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hA : M + (s : ℂ) • 1 = U * (D + (s : ℂ) • 1) * star U := by
    rw [hMD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hUU']
  have hDE : (D + (s : ℂ) • 1) * E = 1 := by
    rw [Matrix.smul_one_eq_diagonal, hD, hE, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    ext k
    have hk : hH.eigenvalues k + s ≠ 0 := by linarith [hnn k]
    rw [← Complex.ofReal_add, ← Complex.ofReal_mul, mul_inv_cancel₀ hk]
    simp
  have hAi : (M + (s : ℂ) • 1)⁻¹ = U * E * star U := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hA]
    calc U * (D + (s : ℂ) • 1) * star U * (U * E * star U)
        = U * ((D + (s : ℂ) • 1) * E) * star U := by
          simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]
      _ = 1 := by rw [hDE, Matrix.mul_one, hUU']
  have htr : (M * (M + (s : ℂ) • 1)⁻¹).trace = (D * E).trace := by
    rw [hAi, hMD]
    calc (U * D * star U * (U * E * star U)).trace = (U * (D * E) * star U).trace := by
          simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]
      _ = (star U * (U * (D * E))).trace := by
          rw [Matrix.trace_mul_comm (U * (D * E)) (star U)]
      _ = (D * E).trace := by rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  rw [htr, hD, hE, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re, div_eq_mul_inv]

/-- `x / (1 + x) ≤ x ^ s` for `x ≥ 0` and `0 < s ≤ 1`, in the form `m / (m + a) ≤ a ^ (-s) m ^ s`
for `m ≥ 0` and `a > 0`. -/
private lemma rankTrace_ratio_le {m a s : ℝ} (hm : 0 ≤ m) (ha : 0 < a) (hs0 : 0 < s)
    (hs1 : s ≤ 1) : m / (m + a) ≤ a ^ (-s) * m ^ s := by
  have hma : m + a ≠ 0 := (by linarith : 0 < m + a).ne'
  have hx : m / (m + a) = (m / a) / (1 + m / a) := by
    field_simp
    ring
  have h2 : a ^ (-s) * m ^ s = (m / a) ^ s := by
    rw [Real.div_rpow hm ha.le, Real.rpow_neg ha.le]; ring
  have hxn : 0 ≤ m / a := div_nonneg hm ha.le
  rw [h2, hx]
  generalize m / a = x at hxn ⊢
  rcases le_total x 1 with h | h
  · calc x / (1 + x) ≤ x := div_le_self hxn (by linarith)
      _ ≤ x ^ s := by
        rcases hxn.eq_or_lt with h0 | hpos
        · rw [← h0, Real.zero_rpow hs0.ne']
        · have := Real.rpow_le_rpow_of_exponent_ge hpos h hs1
          rwa [Real.rpow_one] at this
  · calc x / (1 + x) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      _ ≤ x ^ s := Real.one_le_rpow h hs0.le

/-- (9.53) [su:eq:retained-rank-moment] in surrogate form: for `t > 0` and `0 < p ≤ 2`, the number
of eigenvalues of `Y* Y` above `t²` is at most `rankSurr t (Y* Y)`, which is at most
`2 t^{-p} Tr |Y|^p`. -/
theorem countIn_le_rankSurr (Y : Matrix n n ℂ) {t p : ℝ} (ht : 0 < t) (hp : 0 < p)
    (hp2 : p ≤ 2) :
    (countIn (Yᴴ * Y) (Set.Ioi (t ^ 2)) : ℝ) ≤ rankSurr t (Yᴴ * Y) ∧
      rankSurr t (Yᴴ * Y) ≤ 2 * t ^ (-p) * schattenPow p Y := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self Y
  have hnn : ∀ k, 0 ≤ hH.eigenvalues k := rankTrace_eigenvalues_nonneg Y
  have ht2 : 0 < t ^ 2 := by positivity
  have hrs : rankSurr t (Yᴴ * Y) = 2 * ∑ k, hH.eigenvalues k / (hH.eigenvalues k + t ^ 2) := by
    rw [rankSurr, rankTrace_trace_surr hH ht2 hnn]
  have hcount : (countIn (Yᴴ * Y) (Set.Ioi (t ^ 2)) : ℝ) =
      ((univ.filter fun k => t ^ 2 < hH.eigenvalues k).card : ℝ) := by
    simp only [countIn, hH, ↓reduceDIte, Set.mem_Ioi]
  rw [hrs, hcount]
  refine ⟨?_, ?_⟩
  · calc ((univ.filter fun k => t ^ 2 < hH.eigenvalues k).card : ℝ)
        = ∑ k ∈ univ.filter fun k => t ^ 2 < hH.eigenvalues k, (1 : ℝ) := by simp
      _ ≤ ∑ k ∈ univ.filter fun k => t ^ 2 < hH.eigenvalues k,
          2 * (hH.eigenvalues k / (hH.eigenvalues k + t ^ 2)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : t ^ 2 < hH.eigenvalues k := (Finset.mem_filter.mp hk).2
        have hpos : 0 < hH.eigenvalues k + t ^ 2 := by linarith [hnn k]
        rw [← mul_div_assoc, le_div_iff₀ hpos]
        linarith
      _ ≤ ∑ k, 2 * (hH.eigenvalues k / (hH.eigenvalues k + t ^ 2)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ => by
          have := hnn k
          positivity
      _ = 2 * ∑ k, hH.eigenvalues k / (hH.eigenvalues k + t ^ 2) := by rw [Finset.mul_sum]
  · have ht' : (t ^ 2) ^ (-(p / 2)) = t ^ (-p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      congr 1; push_cast; ring
    calc 2 * ∑ k, hH.eigenvalues k / (hH.eigenvalues k + t ^ 2)
        ≤ 2 * ∑ k, t ^ (-p) * hH.eigenvalues k ^ (p / 2) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by norm_num)
          rw [← ht']
          exact rankTrace_ratio_le (hnn k) ht2 (by linarith) (by linarith)
      _ = 2 * t ^ (-p) * schattenPow p Y := by
          rw [← Finset.mul_sum, schattenPow, mul_assoc]

open scoped ComplexOrder in
/-- `P T* T P + (1 - P)` is invertible for invertible `T` and a Hermitian idempotent `P`. -/
private lemma rankTrace_isUnit_gram {T P : Matrix n n ℂ} (hT : IsUnit T) (hP : Pᴴ = P)
    (hPP : P * P = P) : IsUnit (P * Tᴴ * T * P + (1 - P)) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have hker : ∀ z : n → ℂ, (P * Tᴴ * T * P + (1 - P)) *ᵥ z = 0 → z = 0 := by
    intro z hz
    have h1 : P *ᵥ ((P * Tᴴ * T * P + (1 - P)) *ᵥ z) = 0 := by rw [hz, Matrix.mulVec_zero]
    have h2 : P * (P * Tᴴ * T * P + (1 - P)) = P * Tᴴ * T * P := by
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPP]
      abel
    rw [Matrix.mulVec_mulVec, h2] at h1
    set w : n → ℂ := P *ᵥ z with hw
    have hPw : P *ᵥ w = w := by rw [hw, Matrix.mulVec_mulVec, hPP]
    have h3 : P *ᵥ (Tᴴ *ᵥ (T *ᵥ w)) = 0 := by
      rw [← h1, hw]; simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have hs : star w = star w ᵥ* P := by
      conv_lhs => rw [← hPw]
      rw [Matrix.star_mulVec, hP]
    have h4 : star (T *ᵥ w) ⬝ᵥ (T *ᵥ w) = 0 := by
      calc star (T *ᵥ w) ⬝ᵥ (T *ᵥ w) = star w ⬝ᵥ (Tᴴ *ᵥ (T *ᵥ w)) := by
            rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
        _ = (star w ᵥ* P) ⬝ᵥ (Tᴴ *ᵥ (T *ᵥ w)) := by rw [← hs]
        _ = star w ⬝ᵥ (P *ᵥ (Tᴴ *ᵥ (T *ᵥ w))) := (Matrix.dotProduct_mulVec _ _ _).symm
        _ = 0 := by rw [h3, dotProduct_zero]
    have h5 : T *ᵥ w = 0 := dotProduct_star_self_eq_zero.mp h4
    have h6 : w = 0 := by
      obtain ⟨U, rfl⟩ := hT
      have := congrArg (fun v => (↑U⁻¹ : Matrix n n ℂ) *ᵥ v) h5
      simpa [Matrix.mulVec_mulVec] using this
    have h7 : (1 - P) *ᵥ z = 0 := by
      have : (P * Tᴴ * T * P + (1 - P)) *ᵥ z = (P * Tᴴ * T * P) *ᵥ z + (1 - P) *ᵥ z :=
        Matrix.add_mulVec _ _ _
      rw [hz, h1, zero_add] at this
      exact this.symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hw, h6, sub_zero] at h7
    exact h7
  intro x y hxy
  have := hker (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.mp this

/-- For invertible `T` and an orthogonal projection `P`, `flagProj T P` has the trace of `P`, and
every vector in its range is `T y` for some `y` with `P y = y`. -/
theorem flagProj_trace_range {T P : Matrix n n ℂ} (hT : IsUnit T) (hP : P.IsHermitian)
    (hPP : P * P = P) :
    (flagProj T P).trace = P.trace ∧
      ∀ x : n → ℂ, ∃ y : n → ℂ, P *ᵥ y = y ∧ flagProj T P *ᵥ x = T *ᵥ y := by
  set M : Matrix n n ℂ := P * Tᴴ * T * P + (1 - P) with hM
  have hMd : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).mp (rankTrace_isUnit_gram hT hP.eq hPP)
  have hPM : P * M = P * Tᴴ * T * P := by
    rw [hM]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPP]
    abel
  have hMP : M * P = P * Tᴴ * T * P := by
    rw [hM]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hPP]
    abel
  have hi1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hMd
  have hi2 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMd
  have hcomm : P * M⁻¹ = M⁻¹ * P := by
    calc P * M⁻¹ = (M⁻¹ * M) * P * M⁻¹ := by rw [hi1, Matrix.one_mul]
      _ = M⁻¹ * (M * P) * M⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ * (P * M) * M⁻¹ := by rw [hMP, hPM]
      _ = M⁻¹ * P * (M * M⁻¹) := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ * P := by rw [hi2, Matrix.mul_one]
  have hf : flagProj T P = T * P * M⁻¹ * P * Tᴴ := rfl
  refine ⟨?_, fun x => ⟨P *ᵥ (M⁻¹ *ᵥ (P *ᵥ (Tᴴ *ᵥ x))), ?_, ?_⟩⟩
  · have hK : M⁻¹ * P * Tᴴ * T * P = P := by
      calc M⁻¹ * P * Tᴴ * T * P = M⁻¹ * (P * Tᴴ * T * P) := by simp only [Matrix.mul_assoc]
        _ = M⁻¹ * (M * P) := by rw [hMP]
        _ = (M⁻¹ * M) * P := by simp only [Matrix.mul_assoc]
        _ = P := by rw [hi1, Matrix.one_mul]
    have hN : P * (M⁻¹ * P) = M⁻¹ * P := by rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, hPP]
    have e : P * M⁻¹ * P = M⁻¹ * P := by rw [hcomm, Matrix.mul_assoc, hPP]
    calc (flagProj T P).trace = (T * (M⁻¹ * P * Tᴴ)).trace := by
          rw [hf]
          have : T * P * M⁻¹ * P * Tᴴ = T * (P * M⁻¹ * P) * Tᴴ := by simp only [Matrix.mul_assoc]
          rw [this, e, Matrix.mul_assoc T]
      _ = (M⁻¹ * P * Tᴴ * T).trace := Matrix.trace_mul_comm _ _
      _ = (P * (M⁻¹ * P * Tᴴ * T)).trace := by simp only [← Matrix.mul_assoc, hN]
      _ = (M⁻¹ * P * Tᴴ * T * P).trace := Matrix.trace_mul_comm _ _
      _ = P.trace := by rw [hK]
  · simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPP]
  · rw [hf]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- An orthogonal projection `Π` such that `|v* x|² ≤ K ‖x‖²` for every `x` in its range has
`‖Π v‖² ≤ K`. -/
theorem sq_l2Norm_proj_le {Pr : Matrix n n ℂ} (hPr : Pr.IsHermitian) (hPP : Pr * Pr = Pr)
    (v : n → ℂ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x : n → ℂ, Pr *ᵥ x = x → ‖star v ⬝ᵥ x‖ ^ 2 ≤ K * l2Norm x ^ 2) :
    l2Norm (Pr *ᵥ v) ^ 2 ≤ K := by
  set x : n → ℂ := Pr *ᵥ v with hx
  have hxx : Pr *ᵥ x = x := by rw [hx, Matrix.mulVec_mulVec, hPP]
  have hS : l2Norm x ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  have hdot : star v ⬝ᵥ x = ((l2Norm x ^ 2 : ℝ) : ℂ) := by
    have h1 : star x ⬝ᵥ x = star v ⬝ᵥ x := by
      rw [hx, Matrix.star_mulVec, hPr.eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hPP]
    rw [← h1, hS, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.conj_mul']
  have h2 := hK x hxx
  rw [hdot, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h2
  by_cases h0 : l2Norm x ^ 2 = 0
  · rw [h0]; exact hK0
  · have hpos : 0 < l2Norm x ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm h0)
    nlinarith

end LSBA
