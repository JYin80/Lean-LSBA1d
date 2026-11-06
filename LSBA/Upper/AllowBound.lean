import LSBA.Upper.SmallGenerator
import LSBA.Spectral.RankTrace

/-!
# The allowed compression and the size of the source vector

The common conclusion of the proof of (9.65) [su:eq:construction-overlap-goals] in Section 9.4.1
[su:sec:retained-geometry]: for orthogonal projections `P`, `Q` and `P v ≠ 0`, the allowed
projection `Π = P - ‖P v‖⁻² (P v)(P v)*` satisfies
`x* Π x ≥ (1 - ‖(1 - P) Q‖² - ‖P v‖⁻² ‖Q P v‖²) ‖x‖²` on `ran Q`. If `B_Q = Q Π Q ≥ b` on `ran Q`,
then `Q Π Q + 1 - Q` is invertible and `y = Π Q B_Q⁻¹ Q v` of (9.16) [us:eq:H0] has
`‖y‖ ≤ b⁻¹ ‖Q v‖`. Where `R̃` is invertible, `rank Q` is the number of eigenvalues of `A* A` above
`t²` (9.53) [su:eq:retained-rank-moment].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `w* w = ‖w‖₂²`. -/
private lemma allowBound_dot_self {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    star w ⬝ᵥ w = ((l2Norm w ^ 2 : ℝ) : ℂ) := by
  rw [l2Norm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  push_cast
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']

/-- `‖w‖₂ = 0` forces `w = 0`. -/
private lemma allowBound_eq_zero {ι : Type*} [Fintype ι] {v : ι → ℂ} (h : l2Norm v = 0) :
    v = 0 := by
  rw [l2Norm_eq_norm_toLp, norm_eq_zero] at h
  exact (WithLp.toLp_eq_zero 2).1 h

/-- For Hermitian `H`, `(H y)* z = y* (H z)`. -/
private lemma allowBound_dot_herm {ι : Type*} [Fintype ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (y z : ι → ℂ) : star (H *ᵥ y) ⬝ᵥ z = star y ⬝ᵥ (H *ᵥ z) := by
  rw [Matrix.star_mulVec, hH.eq, Matrix.dotProduct_mulVec]

/-- Cauchy–Schwarz: `|a* x| ≤ ‖a‖₂ ‖x‖₂`. -/
private lemma allowBound_cs {ι : Type*} [Fintype ι] (a x : ι → ℂ) :
    ‖star a ⬝ᵥ x‖ ≤ l2Norm a * l2Norm x := by
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp]
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 a) (WithLp.toLp 2 x)
  rw [EuclideanSpace.inner_toLp_toLp] at h
  rwa [dotProduct_comm] at h

/-- For an orthogonal projection `E`, `‖E u‖₂² + ‖(1 - E) u‖₂² = ‖u‖₂²`. -/
private lemma allowBound_proj_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Matrix ι ι ℂ}
    (hE : E.IsHermitian) (hEE : E * E = E) (u : ι → ℂ) :
    l2Norm (E *ᵥ u) ^ 2 + l2Norm ((1 - E) *ᵥ u) ^ 2 = l2Norm u ^ 2 := by
  have h1 : (1 - E).IsHermitian := Matrix.isHermitian_one.sub hE
  have h11 : (1 - E) * (1 - E) = 1 - E := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.one_mul, Matrix.mul_one, hEE]
    abel
  have key : star (E *ᵥ u) ⬝ᵥ (E *ᵥ u) + star ((1 - E) *ᵥ u) ⬝ᵥ ((1 - E) *ᵥ u) =
      star u ⬝ᵥ u := by
    rw [allowBound_dot_herm hE, allowBound_dot_herm h1, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hEE, h11, ← dotProduct_add, ← Matrix.add_mulVec, add_sub_cancel,
      Matrix.one_mulVec]
  rw [allowBound_dot_self, allowBound_dot_self, allowBound_dot_self] at key
  exact_mod_cast key

/-- The quadratic form of `Π = P - ‖P v‖⁻² (P v)(P v)*`. -/
private lemma allowBound_quad {W : ℕ} (P : Matrix (Fin W) (Fin W) ℂ) (v x : Fin W → ℂ) :
    star x ⬝ᵥ (allowProj P v *ᵥ x) =
      star x ⬝ᵥ (P *ᵥ x) -
        (star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ * ((star x ⬝ᵥ (P *ᵥ v)) * (star (P *ᵥ v) ⬝ᵥ x)) := by
  unfold allowProj
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

/-- The lower bound for `B_Q` (Section 9.4.1 [su:sec:retained-geometry], common conclusion): for
orthogonal projections `P`, `Q`, `P v ≠ 0` and `x ∈ ran Q`,
`(1 - ‖(1 - P) Q‖² - ‖P v‖⁻² ‖Q P v‖²) ‖x‖² ≤ x* Π x`. -/
theorem allowProj_lower {W : ℕ} {P Q : Matrix (Fin W) (Fin W) ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q) {v : Fin W → ℂ} (hv : P *ᵥ v ≠ 0)
    (x : Fin W → ℂ) (hx : Q *ᵥ x = x) :
    (1 - ‖(1 - P) * Q‖ ^ 2 - l2Norm (Q *ᵥ (P *ᵥ v)) ^ 2 / l2Norm (P *ᵥ v) ^ 2) * l2Norm x ^ 2 ≤
      (star x ⬝ᵥ (allowProj P v *ᵥ x)).re := by
  set p : Fin W → ℂ := P *ᵥ v with hp
  have hpn : l2Norm p ≠ 0 := fun h => hv (allowBound_eq_zero h)
  have hn : 0 < l2Norm p ^ 2 := pow_pos (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hpn)) 2
  have hxP : star x ⬝ᵥ (P *ᵥ x) = ((l2Norm (P *ᵥ x) ^ 2 : ℝ) : ℂ) := by
    rw [← allowBound_dot_self, allowBound_dot_herm hP, Matrix.mulVec_mulVec, hPP]
  have hcs : star x ⬝ᵥ p = star (star p ⬝ᵥ x) := Matrix.star_dotProduct x p
  have hzz : star (star p ⬝ᵥ x) * (star p ⬝ᵥ x) = ((‖star p ⬝ᵥ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  have hre : (star x ⬝ᵥ (allowProj P v *ᵥ x)).re =
      l2Norm (P *ᵥ x) ^ 2 - ‖star p ⬝ᵥ x‖ ^ 2 / l2Norm p ^ 2 := by
    rw [allowBound_quad, hxP, hcs, hzz, allowBound_dot_self]
    simp only [Complex.sub_re, Complex.ofReal_re]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re, inv_mul_eq_div]
  have hb : l2Norm ((1 - P) *ᵥ x) ≤ ‖(1 - P) * Q‖ * l2Norm x := by
    have h := l2Norm_mulVec_le ((1 - P) * Q) x
    rwa [← Matrix.mulVec_mulVec, hx] at h
  have hk : ‖star p ⬝ᵥ x‖ ≤ l2Norm (Q *ᵥ p) * l2Norm x := by
    have h := allowBound_cs (Q *ᵥ p) x
    rwa [allowBound_dot_herm hQ, hx] at h
  have hpy := allowBound_proj_sq hP hPP x
  have hb2 : l2Norm ((1 - P) *ᵥ x) ^ 2 ≤ ‖(1 - P) * Q‖ ^ 2 * l2Norm x ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
  have hk2 : ‖star p ⬝ᵥ x‖ ^ 2 ≤ l2Norm (Q *ᵥ p) ^ 2 * l2Norm x ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hk 2
  have hdiv : ‖star p ⬝ᵥ x‖ ^ 2 / l2Norm p ^ 2 ≤
      l2Norm (Q *ᵥ p) ^ 2 * l2Norm x ^ 2 / l2Norm p ^ 2 :=
    div_le_div_of_nonneg_right hk2 hn.le
  rw [hre, sub_mul, sub_mul, div_mul_eq_mul_div]
  linarith

/-- `Π = P - ‖P v‖⁻² (P v)(P v)*` is an orthogonal projection when `P` is. -/
private lemma allowBound_allowProj_proj {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (v : Fin W → ℂ) :
    (allowProj P v).IsHermitian ∧ allowProj P v * allowProj P v = allowProj P v := by
  by_cases h0 : P *ᵥ v = 0
  · have hPi : allowProj P v = P := by
      unfold allowProj
      rw [h0]
      simp
    rw [hPi]
    exact ⟨hP, hPP⟩
  · have hsr : star (P *ᵥ v) ⬝ᵥ (P *ᵥ v) = ((l2Norm (P *ᵥ v) ^ 2 : ℝ) : ℂ) :=
      allowBound_dot_self _
    have hs : star (P *ᵥ v) ⬝ᵥ (P *ᵥ v) ≠ 0 := by
      rw [hsr]
      exact_mod_cast pow_ne_zero 2 fun h => h0 (allowBound_eq_zero h)
    have hPp : P *ᵥ (P *ᵥ v) = P *ᵥ v := by rw [Matrix.mulVec_mulVec, hPP]
    have hPs : star (P *ᵥ v) ᵥ* P = star (P *ᵥ v) := by
      have h := Matrix.star_mulVec P (P *ᵥ v)
      rw [hPp, hP.eq] at h
      exact h.symm
    have hPi : allowProj P v = P - (star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ •
        Matrix.vecMulVec (P *ᵥ v) (star (P *ᵥ v)) := rfl
    have hPV : P * Matrix.vecMulVec (P *ᵥ v) (star (P *ᵥ v)) =
        Matrix.vecMulVec (P *ᵥ v) (star (P *ᵥ v)) := by
      rw [Matrix.mul_vecMulVec, hPp]
    have hVP : Matrix.vecMulVec (P *ᵥ v) (star (P *ᵥ v)) * P =
        Matrix.vecMulVec (P *ᵥ v) (star (P *ᵥ v)) := by
      rw [Matrix.vecMulVec_mul, hPs]
    have hVV : Matrix.vecMulVec (P *ᵥ v) (star (P *ᵥ v)) *
        Matrix.vecMulVec (P *ᵥ v) (star (P *ᵥ v)) =
        (star (P *ᵥ v) ⬝ᵥ (P *ᵥ v)) • Matrix.vecMulVec (P *ᵥ v) (star (P *ᵥ v)) := by
      rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
    have hcc : star (star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ = (star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ := by
      rw [hsr, star_inv₀, Complex.star_def, Complex.conj_ofReal]
    refine ⟨?_, ?_⟩
    · unfold Matrix.IsHermitian
      rw [hPi, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec,
        star_star, hP.eq, hcc]
    · rw [hPi]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hPP, hPV, hVP,
        hVV, smul_smul]
      have hcs : (star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ * (star (P *ᵥ v) ⬝ᵥ (P *ᵥ v)) = 1 :=
        inv_mul_cancel₀ hs
      rw [hcs, one_smul, sub_self, smul_zero, sub_zero]

/-- `Q`, the retained projection, is an orthogonal projection of trace the number of eigenvalues
of `A* A` above `t²`. -/
private lemma allowBound_ret_spec {W q : ℕ} {g E : ℝ} (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ)
    (ω : Ω W q) (hT : IsUnit (cavRes W g E q R ω)) :
    (retProj W g E q R t ω).IsHermitian ∧
      retProj W g E q R t ω * retProj W g E q R t ω = retProj W g E q R t ω ∧
      (retProj W g E q R t ω).trace =
        (countIn ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6))
          (Set.Ioi (t ^ 2)) : ℂ) := by
  have hA : ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self _
  obtain ⟨hSh, hSS, -, hSt⟩ := specProj_spec hA (Set.Ioi (t ^ 2))
  obtain ⟨hQh, hQQ, -⟩ := flagProj_spec hT hSh hSS
  exact ⟨hQh, hQQ, (flagProj_trace_range hT hSh hSS).1.trans hSt⟩

/-- For orthogonal projections `Q`, `Π` with `B_Q ≥ b > 0` on `ran Q`: `Q Π Q + 1 - Q` is
invertible and `‖Π Q (Q Π Q + 1 - Q)⁻¹ Q v‖² ≤ b⁻² ‖Q v‖²`. -/
private lemma allowBound_src {W : ℕ} {Q Pi : Matrix (Fin W) (Fin W) ℂ} (hQh : Q.IsHermitian)
    (hQQ : Q * Q = Q) (hPih : Pi.IsHermitian) (hPiPi : Pi * Pi = Pi) {b : ℝ} (hb : 0 < b)
    (hBQ : ∀ u : Fin W → ℂ, Q *ᵥ u = u → b * l2Norm u ^ 2 ≤ (star u ⬝ᵥ (Pi *ᵥ u)).re)
    (v : Fin W → ℂ) :
    IsUnit (Q * Pi * Q + (1 - Q)) ∧
      l2Norm ((Pi * Q * (Q * Pi * Q + (1 - Q))⁻¹ * Q) *ᵥ v) ^ 2 ≤
        b⁻¹ ^ 2 * l2Norm (Q *ᵥ v) ^ 2 := by
  set M : Matrix (Fin W) (Fin W) ℂ := Q * Pi * Q + (1 - Q) with hM
  have hQ1 : Q * (1 - Q) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hQQ, sub_self]
  have h1Q : (1 - Q) * Q = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hQQ, sub_self]
  have hQM : Q * M = Q * Pi * Q := by
    have h : Q * (Q * Pi * Q) = Q * Pi * Q := by simp only [← Matrix.mul_assoc, hQQ]
    rw [hM, Matrix.mul_add, h, hQ1, add_zero]
  have h1QM : (1 - Q) * M = 1 - Q := by
    have h1 : (1 - Q) * (Q * Pi * Q) = 0 := by
      simp only [← Matrix.mul_assoc, h1Q, Matrix.zero_mul]
    have h2 : (1 - Q) * (1 - Q) = 1 - Q := by
      rw [Matrix.sub_mul, hQ1, Matrix.one_mul, sub_zero]
    rw [hM, Matrix.mul_add, h1, h2, zero_add]
  have hU : IsUnit M := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro z₁ z₂ h12
    have hz : M *ᵥ (z₁ - z₂) = 0 := by rw [Matrix.mulVec_sub, h12, sub_self]
    set z : Fin W → ℂ := z₁ - z₂ with hzdef
    have h1 : (Q * Pi * Q) *ᵥ z = 0 := by
      have h := congrArg (fun y => Q *ᵥ y) hz
      simp only [Matrix.mulVec_mulVec, hQM, Matrix.mulVec_zero] at h
      exact h
    have hw : Q *ᵥ (Q *ᵥ z) = Q *ᵥ z := by rw [Matrix.mulVec_mulVec, hQQ]
    have hq : star (Q *ᵥ z) ⬝ᵥ (Pi *ᵥ (Q *ᵥ z)) = 0 := by
      rw [allowBound_dot_herm hQh]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc] at h1 ⊢
      rw [h1, dotProduct_zero]
    have hb0 := hBQ (Q *ᵥ z) hw
    rw [hq, Complex.zero_re] at hb0
    have hn : l2Norm (Q *ᵥ z) ^ 2 ≤ 0 := by
      by_contra hcon
      nlinarith [not_le.mp hcon]
    have hQz : Q *ᵥ z = 0 :=
      allowBound_eq_zero (pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm hn (sq_nonneg _)))
    have hMz : M *ᵥ z = (Q * Pi * Q) *ᵥ z + (z - Q *ᵥ z) := by
      rw [hM, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hMz, h1, hQz, sub_zero, zero_add] at hz
    exact sub_eq_zero.mp hz
  refine ⟨hU, ?_⟩
  have hMd : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hU
  set u : Fin W → ℂ := M⁻¹ *ᵥ (Q *ᵥ v) with hu
  have hMu : M *ᵥ u = Q *ᵥ v := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hMd, Matrix.one_mulVec]
  have hQu : Q *ᵥ u = u := by
    have h := congrArg (fun y => (1 - Q) *ᵥ y) hMu
    simp only [Matrix.mulVec_mulVec, h1QM, h1Q, Matrix.zero_mulVec] at h
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h.symm
  have hQPi : Q *ᵥ (Pi *ᵥ u) = Q *ᵥ v := by
    have h := congrArg (fun y => Q *ᵥ y) hMu
    simp only [Matrix.mulVec_mulVec, hQM, hQQ] at h
    simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hQu] at h
    exact h
  have hy : (Pi * Q * M⁻¹ * Q) *ᵥ v = Pi *ᵥ u := by
    have : (Pi * Q * M⁻¹ * Q) *ᵥ v = Pi *ᵥ (Q *ᵥ (M⁻¹ *ᵥ (Q *ᵥ v))) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [this, ← hu, hQu]
  have hdot : star u ⬝ᵥ (Pi *ᵥ u) = star u ⬝ᵥ (Q *ᵥ v) := by
    have h := allowBound_dot_herm hQh u (Pi *ᵥ u)
    rw [hQu, hQPi] at h
    exact h
  have hlow := hBQ u hQu
  rw [hdot] at hlow
  have hcs := allowBound_cs u (Q *ᵥ v)
  have hre : b * l2Norm u ^ 2 ≤ l2Norm u * l2Norm (Q *ᵥ v) :=
    hlow.trans ((Complex.re_le_norm _).trans hcs)
  have hnu : 0 ≤ l2Norm u := Real.sqrt_nonneg _
  have hle : l2Norm u ≤ b⁻¹ * l2Norm (Q *ᵥ v) := by
    rw [le_inv_mul_iff₀ hb]
    rcases hnu.eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]; exact Real.sqrt_nonneg _
    · have : l2Norm u * (b * l2Norm u) ≤ l2Norm u * l2Norm (Q *ᵥ v) := by nlinarith
      exact le_of_mul_le_mul_left this hpos
  have hPi := allowBound_proj_sq hPih hPiPi u
  rw [hy, ← mul_pow]
  calc l2Norm (Pi *ᵥ u) ^ 2 ≤ l2Norm u ^ 2 := by nlinarith [sq_nonneg (l2Norm ((1 - Pi) *ᵥ u))]
    _ ≤ (b⁻¹ * l2Norm (Q *ᵥ v)) ^ 2 := pow_le_pow_left₀ hnu hle 2

/-- If `B_Q ≥ b > 0` on `ran Q` and `R̃` is invertible, then `Q Π Q + 1 - Q` is invertible and
`‖y‖² ≤ b⁻² ‖Q v‖²` for `y` of (9.16) [us:eq:H0]. -/
theorem srcVec_sq_le {W q : ℕ} {g E : ℝ} (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ)
    {P : Matrix (Fin W) (Fin W) ℂ} (hP : P.IsHermitian) (hPP : P * P = P) (ω : Ω W q)
    (hT : IsUnit (cavRes W g E q R ω)) {v : Fin W → ℂ} {b : ℝ} (hb : 0 < b)
    (hBQ : ∀ u : Fin W → ℂ, retProj W g E q R t ω *ᵥ u = u →
      b * l2Norm u ^ 2 ≤ (star u ⬝ᵥ (allowProj P v *ᵥ u)).re) :
    IsUnit (retProj W g E q R t ω * allowProj P v * retProj W g E q R t ω +
        (1 - retProj W g E q R t ω)) ∧
      l2Norm (srcVec W g E q R t P ω v) ^ 2 ≤
        b⁻¹ ^ 2 * l2Norm (retProj W g E q R t ω *ᵥ v) ^ 2 := by
  obtain ⟨hQh, hQQ, -⟩ := allowBound_ret_spec (g := g) (E := E) R t ω hT
  obtain ⟨hPih, hPiPi⟩ := allowBound_allowProj_proj hP hPP v
  exact allowBound_src hQh hQQ hPih hPiPi hb hBQ v

/-- (9.53) [su:eq:retained-rank-moment]: where `R̃` is invertible, `Q` is an orthogonal projection
whose trace is the number of eigenvalues of `A* A` above `t²`. -/
theorem trace_retProj {W q : ℕ} {g E : ℝ} (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ) (ω : Ω W q)
    (hT : IsUnit (cavRes W g E q R ω)) :
    (retProj W g E q R t ω).IsHermitian ∧
      retProj W g E q R t ω * retProj W g E q R t ω = retProj W g E q R t ω ∧
      (retProj W g E q R t ω).trace =
        (countIn ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6))
          (Set.Ioi (t ^ 2)) : ℂ) := by
  exact allowBound_ret_spec R t ω hT

end LSBA
