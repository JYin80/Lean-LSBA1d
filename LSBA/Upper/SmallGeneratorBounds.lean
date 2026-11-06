import LSBA.Upper.SmallGenerator

/-!
# Elementary bounds for the construction of `K`

Section 9.2 [su:sec:explicit-generator]: under (9.19) [su:eq:generator-admissibility]
(`P v ≠ 0`, `B_Q ≥ ½` on `ran Q`, `‖y‖ ≤ ‖v‖`, `‖A_< R̃‖ ‖v‖ ≤ ¼ ‖v_{q-1}‖`) and where the
inverses of (3.4) [us:eq:cavity] exist: `‖y‖ ≤ 2 ‖Q v‖` and `‖K_0‖²_HS ≤ 8 ‖P v‖⁻² ‖Q v‖²`
(9.20) [us:eq:sourceenergy]; `½ ≤ ξ ≤ 3/2`, `|ξ - 1| ≤ 2 ‖v_{q-1}‖⁻¹ ‖A_< R̃‖ ‖v‖`,
`‖K‖²_HS ≤ 32 ‖P v‖⁻² ‖Q v‖²`, `‖v_corr‖ ≤ 8 ‖A_< R̃‖ ‖v‖` and
`‖L‖_HS ≤ 24 ‖v_{q-1}‖⁻¹ ‖A_< R̃‖ ‖v‖` (9.21) [su:eq:normalized-generator-costs]. Norms of vectors
are Euclidean, written through `Σ_i |x_i|²`; `‖A_< R̃‖` is the operator norm.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `x* x` is the real number `Σ ‖x i‖²`. -/
private lemma SmallGeneratorBounds_dot_self {n : Type*} [Fintype n] (x : n → ℂ) :
    star x ⬝ᵥ x = ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
  simp [dotProduct, Complex.conj_mul', Complex.ofReal_sum]

private lemma SmallGeneratorBounds_pos {n : Type*} [Fintype n] {x : n → ℂ} (hx : x ≠ 0) :
    0 < ∑ i, ‖x i‖ ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact Finset.sum_pos' (fun _ _ => by positivity)
    ⟨i, Finset.mem_univ _, by have := norm_pos_iff.mpr hi; positivity⟩

private lemma SmallGeneratorBounds_nsq_smul {n : Type*} [Fintype n] (c : ℂ) (x : n → ℂ) :
    ∑ i, ‖(c • x) i‖ ^ 2 = ‖c‖ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
  simp [mul_pow, Finset.mul_sum]

private lemma SmallGeneratorBounds_nsq_sub_le {n : Type*} [Fintype n] (a b : n → ℂ) :
    ∑ i, ‖(a - b) i‖ ^ 2 ≤ 2 * ∑ i, ‖a i‖ ^ 2 + 2 * ∑ i, ‖b i‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.sub_apply]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (a i) (b i)) 2
  nlinarith [sq_nonneg (‖a i‖ - ‖b i‖)]

private lemma SmallGeneratorBounds_cs {n : Type*} [Fintype n] (a b : n → ℂ) :
    ((star a ⬝ᵥ b).re) ^ 2 ≤ (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖b i‖ ^ 2 := by
  have h : ‖star a ⬝ᵥ b‖ ≤ √(∑ i, ‖a i‖ ^ 2) * √(∑ i, ‖b i‖ ^ 2) := by
    calc ‖star a ⬝ᵥ b‖ ≤ ∑ i, ‖star (a i) * b i‖ := by
          simpa [dotProduct] using norm_sum_le Finset.univ (fun i => star (a i) * b i)
      _ = ∑ i, ‖a i‖ * ‖b i‖ := by simp
      _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have h2 : ((star a ⬝ᵥ b).re) ^ 2 ≤ ‖star a ⬝ᵥ b‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  refine h2.trans ?_
  calc ‖star a ⬝ᵥ b‖ ^ 2 ≤ (√(∑ i, ‖a i‖ ^ 2) * √(∑ i, ‖b i‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by
        rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

private lemma SmallGeneratorBounds_opNorm {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (x : Fin W → ℂ) : ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  have h1 : ‖(EuclideanSpace.equiv (Fin W) ℂ).symm (A *ᵥ x)‖ ^ 2 = ∑ i, ‖(A *ᵥ x) i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h2 : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin W))‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  rw [← h1, ← h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

private lemma SmallGeneratorBounds_hsSq_smul {m n : Type*} [Fintype m] [Fintype n] (z : ℂ)
    (A : Matrix m n ℂ) : hsSq (z • A) = ‖z‖ ^ 2 * hsSq A := by
  simp [hsSq, mul_pow, Finset.mul_sum]

private lemma SmallGeneratorBounds_hsSq_sub_le {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) : hsSq (A - B) ≤ 2 * hsSq A + 2 * hsSq B := by
  unfold hsSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  simp only [Matrix.sub_apply]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (A a b) (B a b)) 2
  nlinarith [sq_nonneg (‖A a b‖ - ‖B a b‖)]

private lemma SmallGeneratorBounds_hsSq_vecMulVec {m n : Type*} [Fintype m] [Fintype n]
    (x : m → ℂ) (y : n → ℂ) :
    hsSq (Matrix.vecMulVec x (star y)) = (∑ i, ‖x i‖ ^ 2) * ∑ j, ‖y j‖ ^ 2 := by
  simp [hsSq, Matrix.vecMulVec, mul_pow, Finset.sum_mul_sum]

private lemma SmallGeneratorBounds_hsSq_rank_two {n : Type*} [Fintype n] {u : n → ℂ}
    (hu : u ≠ 0) (y : n → ℂ) :
    hsSq ((star u ⬝ᵥ u)⁻¹ • (Matrix.vecMulVec y (star u) - Matrix.vecMulVec u (star y))) ≤
      4 * (∑ i, ‖y i‖ ^ 2) / ∑ i, ‖u i‖ ^ 2 := by
  have hp := SmallGeneratorBounds_pos hu
  rw [SmallGeneratorBounds_hsSq_smul, SmallGeneratorBounds_dot_self, ← Complex.ofReal_inv,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  refine (mul_le_mul_of_nonneg_left (SmallGeneratorBounds_hsSq_sub_le _ _) (by positivity)).trans ?_
  rw [SmallGeneratorBounds_hsSq_vecMulVec, SmallGeneratorBounds_hsSq_vecMulVec]
  apply le_of_eq
  field_simp
  ring
/-- The allowed projection `Π = P - ‖P v‖⁻² (P v)(P v)*` of Section 9.2
[su:sec:explicit-generator] is an orthogonal projection when `P` is one and `P v ≠ 0`. -/
private lemma SmallGeneratorBounds_allow {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) {v : Fin W → ℂ} (hv : P *ᵥ v ≠ 0) :
    (allowProj P v)ᴴ = allowProj P v ∧ allowProj P v * allowProj P v = allowProj P v := by
  have hpos := SmallGeneratorBounds_pos hv
  set u := P *ᵥ v with hu
  have hPh : Pᴴ = P := hP.eq
  have hPu : P *ᵥ u = u := by rw [hu, Matrix.mulVec_mulVec, hPP]
  have hnr := SmallGeneratorBounds_dot_self u
  set c : ℝ := (∑ i, ‖u i‖ ^ 2)⁻¹ with hc
  have hcn : (star u ⬝ᵥ u)⁻¹ = (c : ℂ) := by rw [hnr, hc, Complex.ofReal_inv]
  have hcnn : (c : ℂ) * (star u ⬝ᵥ u) = 1 := by
    rw [← hcn]; exact inv_mul_cancel₀ (by rw [hnr]; exact_mod_cast hpos.ne')
  have hsu : star u = star v ᵥ* P := by rw [hu, Matrix.star_mulVec, hPh]
  have huv : star u ⬝ᵥ v = star u ⬝ᵥ u := by
    rw [hsu, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, hPu]
  have hPi_h : (allowProj P v)ᴴ = allowProj P v := by
    unfold allowProj
    rw [← hu, hcn, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_vecMulVec, star_star, hPh]
    simp
  have hPPi : P * allowProj P v = allowProj P v := by
    unfold allowProj
    rw [← hu, hcn, Matrix.mul_sub, hPP, Matrix.mul_smul, Matrix.mul_vecMulVec, hPu]
  have hPiv : allowProj P v *ᵥ v = 0 := by
    unfold allowProj
    rw [← hu, hcn, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      op_smul_eq_smul, huv, smul_smul, hcnn, one_smul, ← hu, sub_self]
  have hsPi : star u ᵥ* allowProj P v = 0 := by
    rw [hsu, Matrix.vecMul_vecMul, hPPi]
    have h := Matrix.star_mulVec (allowProj P v) v
    rw [hPiv, hPi_h] at h
    simpa using h.symm
  refine ⟨hPi_h, ?_⟩
  have hdef : allowProj P v = P - (c : ℂ) • Matrix.vecMulVec u (star u) := by
    unfold allowProj; rw [← hu, hcn]
  have h : allowProj P v * allowProj P v =
      P * allowProj P v - (c : ℂ) • (Matrix.vecMulVec u (star u) * allowProj P v) := by
    conv_lhs => arg 1; rw [hdef]
    rw [Matrix.sub_mul, Matrix.smul_mul]
  rw [h, hPPi, Matrix.vecMulVec_mul, hsPi]
  simp

/-- If `Q u = u` for a Hermitian `Q`, then `u* w = u* (Q w)`. -/
private lemma SmallGeneratorBounds_dot_proj {W : ℕ} {Q : Matrix (Fin W) (Fin W) ℂ}
    (hQh : Qᴴ = Q) {u : Fin W → ℂ} (hu : Q *ᵥ u = u) (w : Fin W → ℂ) :
    star u ⬝ᵥ w = star u ⬝ᵥ (Q *ᵥ w) := by
  conv_lhs => rw [← hu]
  rw [Matrix.star_mulVec, hQh, ← Matrix.dotProduct_mulVec]

private lemma SmallGeneratorBounds_gram_unit {W : ℕ} {Q Pi : Matrix (Fin W) (Fin W) ℂ}
    (hQh : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hBQ : ∀ u : Fin W → ℂ, Q *ᵥ u = u →
      (1 / 2 : ℝ) * ∑ i, ‖u i‖ ^ 2 ≤ (star u ⬝ᵥ (Pi *ᵥ u)).re) :
    IsUnit (Q * Pi * Q + (1 - Q)) := by
  have key : ∀ z, (Q * Pi * Q + (1 - Q)) *ᵥ z = 0 → z = 0 := by
    intro z hz
    set a := Q *ᵥ z with ha
    have hQa : Q *ᵥ a = a := by rw [ha, Matrix.mulVec_mulVec, hQQ]
    have hMz : (Q * Pi * Q + (1 - Q)) *ᵥ z = Q *ᵥ (Pi *ᵥ a) + (z - a) := by
      simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
      rfl
    rw [hMz] at hz
    have hQz : Q *ᵥ (z - a) = 0 := by rw [Matrix.mulVec_sub, ← ha, hQa, sub_self]
    have h1 : Q *ᵥ (Pi *ᵥ a) = 0 := by
      have := congrArg (fun w => Q *ᵥ w) hz
      rw [Matrix.mulVec_add, hQz, add_zero, Matrix.mulVec_zero, Matrix.mulVec_mulVec, hQQ] at this
      exact this
    have h2 : z - a = 0 := by rw [h1, zero_add] at hz; exact hz
    have h3 := hBQ a hQa
    rw [SmallGeneratorBounds_dot_proj hQh hQa, h1, dotProduct_zero, Complex.zero_re] at h3
    have ha0 : a = 0 := by
      by_contra hne
      have := SmallGeneratorBounds_pos hne
      linarith
    rw [ha0] at h2
    simpa using h2
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h0 : (Q * Pi * Q + (1 - Q)) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key _ h0)

private lemma SmallGeneratorBounds_Q_alg {W : ℕ} (Q Pi : Matrix (Fin W) (Fin W) ℂ)
    (hQQ : Q * Q = Q) (hB : IsUnit (Q * Pi * Q + (1 - Q))) :
    Q * (Pi * Q * (Q * Pi * Q + (1 - Q))⁻¹ * Q) = Q := by
  have hBd : IsUnit (Q * Pi * Q + (1 - Q)).det := (Matrix.isUnit_iff_isUnit_det _).mp hB
  have hQB : Q * (Q * Pi * Q + (1 - Q)) = Q * Pi * Q := by
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQQ]
    abel
  calc Q * (Pi * Q * (Q * Pi * Q + (1 - Q))⁻¹ * Q)
      = (Q * Pi * Q) * (Q * Pi * Q + (1 - Q))⁻¹ * Q := by simp only [Matrix.mul_assoc]
    _ = (Q * (Q * Pi * Q + (1 - Q))) * (Q * Pi * Q + (1 - Q))⁻¹ * Q := by rw [hQB]
    _ = Q * ((Q * Pi * Q + (1 - Q)) * (Q * Pi * Q + (1 - Q))⁻¹) * Q := by
        simp only [Matrix.mul_assoc]
    _ = Q := by rw [Matrix.mul_nonsing_inv _ hBd, Matrix.mul_one, hQQ]

private lemma SmallGeneratorBounds_src_bound {W : ℕ} {Q Pi : Matrix (Fin W) (Fin W) ℂ}
    (hQh : Qᴴ = Q) (hQQ : Q * Q = Q) (hPh : Piᴴ = Pi) (hPP : Pi * Pi = Pi)
    (hBQ : ∀ u : Fin W → ℂ, Q *ᵥ u = u →
      (1 / 2 : ℝ) * ∑ i, ‖u i‖ ^ 2 ≤ (star u ⬝ᵥ (Pi *ᵥ u)).re) (v : Fin W → ℂ) :
    ∑ i, ‖((Pi * Q * (Q * Pi * Q + (1 - Q))⁻¹ * Q) *ᵥ v) i‖ ^ 2 ≤
      2 * ∑ i, ‖(Q *ᵥ v) i‖ ^ 2 := by
  have hB := SmallGeneratorBounds_gram_unit hQh hQQ hBQ
  have hQM := SmallGeneratorBounds_Q_alg Q Pi hQQ hB
  set u := Q *ᵥ ((Q * Pi * Q + (1 - Q))⁻¹ *ᵥ (Q *ᵥ v)) with hu
  have hQu : Q *ᵥ u = u := by rw [hu, Matrix.mulVec_mulVec, hQQ]
  have hy : (Pi * Q * (Q * Pi * Q + (1 - Q))⁻¹ * Q) *ᵥ v = Pi *ᵥ u := by
    rw [hu]; simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hQy : Q *ᵥ (Pi *ᵥ u) = Q *ᵥ v := by
    rw [← hy, Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ v) hQM
  rw [hy]
  have hyy : star (Pi *ᵥ u) ⬝ᵥ (Pi *ᵥ u) = star u ⬝ᵥ (Pi *ᵥ u) := by
    rw [Matrix.star_mulVec, hPh, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hPP]
  have hN : ∑ i, ‖(Pi *ᵥ u) i‖ ^ 2 = (star u ⬝ᵥ (Pi *ᵥ u)).re := by
    have := congrArg Complex.re (SmallGeneratorBounds_dot_self (Pi *ᵥ u))
    rw [hyy, Complex.ofReal_re] at this
    exact this.symm
  have hc : (star u ⬝ᵥ (Pi *ᵥ u)).re = (star u ⬝ᵥ (Q *ᵥ v)).re := by
    rw [SmallGeneratorBounds_dot_proj hQh hQu, hQy]
  rw [hN]
  set c := (star u ⬝ᵥ (Pi *ᵥ u)).re with hcdef
  have hcs := SmallGeneratorBounds_cs u (Q *ᵥ v)
  rw [← hc] at hcs
  have hh := hBQ u hQu
  rw [← hcdef] at hh
  set a := ∑ i, ‖u i‖ ^ 2 with ha
  set b := ∑ i, ‖(Q *ᵥ v) i‖ ^ 2 with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hab : a ≤ 4 * b := by
    rcases ha0.eq_or_lt with h | h
    · rw [← h]; linarith
    · nlinarith
  nlinarith

private lemma SmallGeneratorBounds_cavProd_unit {W q : ℕ} {g E : ℝ} {ω : Ω W q}
    (hC : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m)) :
    ∀ m, m ≤ q - 6 → IsUnit (cavProd W g E q ω m) := by
  intro m
  induction m with
  | zero => intro _; simp [cavProd]
  | succ m ih =>
    intro hm
    exact (ih (by omega)).mul (hC m (by omega))

/-- The normalization of (9.18) [us:eq:normalize] with the error identity (9.17)
[us:eq:error]: with `ξ = ‖v'‖⁻² Re(v'* C y)`, `v' = C v` and `C (y - v) = M (y - v)`, the bounds
`‖y‖ ≤ ‖v‖` and `‖M‖ ‖v‖ ≤ ¼ ‖v'‖` give `½ ≤ ξ ≤ 3/2`, `(ξ - 1)² ‖v'‖² ≤ 4 ‖M‖² ‖v‖²` and
`‖ξ⁻¹ C y - v'‖² ≤ 64 ‖M‖² ‖v‖²`, in squared form. -/
private lemma SmallGeneratorBounds_core {W : ℕ} (C M : Matrix (Fin W) (Fin W) ℂ)
    (v y : Fin W → ℂ) (hv' : C *ᵥ v ≠ 0) (hCM : C *ᵥ (y - v) = M *ᵥ (y - v))
    (hy : ∑ i, ‖y i‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2)
    (hA : ‖M‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 ≤ (1 / 16 : ℝ) * ∑ i, ‖(C *ᵥ v) i‖ ^ 2) (ξ : ℝ)
    (hξ : ξ = (star (C *ᵥ v) ⬝ᵥ (C *ᵥ y)).re / ∑ i, ‖(C *ᵥ v) i‖ ^ 2) :
    (1 / 2 : ℝ) ≤ ξ ∧ ξ ≤ 3 / 2 ∧
      (ξ - 1) ^ 2 * ∑ i, ‖(C *ᵥ v) i‖ ^ 2 ≤ 4 * (‖M‖ ^ 2 * ∑ i, ‖v i‖ ^ 2) ∧
      ∑ i, ‖((((ξ⁻¹ : ℝ) : ℂ) • (C *ᵥ y) - C *ᵥ v) i)‖ ^ 2 ≤
        64 * (‖M‖ ^ 2 * ∑ i, ‖v i‖ ^ 2) := by
  have hnv := SmallGeneratorBounds_pos hv'
  have hn0 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := by positivity
  have hL0 : 0 ≤ ‖M‖ ^ 2 := by positivity
  set v' := C *ᵥ v with hv'def
  set w := C *ᵥ y with hw
  set nv := ∑ i, ‖v' i‖ ^ 2 with hnvdef
  set n := ∑ i, ‖v i‖ ^ 2 with hndef
  set L := ‖M‖ ^ 2 with hLdef
  have he : C *ᵥ (y - v) = w - v' := by rw [Matrix.mulVec_sub]
  have hNe : ∑ i, ‖(w - v') i‖ ^ 2 ≤ 4 * (L * n) := by
    rw [← he, hCM]
    calc ∑ i, ‖(M *ᵥ (y - v)) i‖ ^ 2 ≤ L * ∑ i, ‖(y - v) i‖ ^ 2 :=
          SmallGeneratorBounds_opNorm M _
      _ ≤ L * (2 * ∑ i, ‖y i‖ ^ 2 + 2 * ∑ i, ‖v i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (SmallGeneratorBounds_nsq_sub_le y v) hL0
      _ ≤ L * (4 * n) := mul_le_mul_of_nonneg_left (by linarith) hL0
      _ = 4 * (L * n) := by ring
  have hdot : (star v' ⬝ᵥ w).re = nv + (star v' ⬝ᵥ (w - v')).re := by
    rw [dotProduct_sub, Complex.sub_re, SmallGeneratorBounds_dot_self, Complex.ofReal_re]
    ring
  have hξ1 : ξ - 1 = (star v' ⬝ᵥ (w - v')).re / nv := by
    rw [hξ, hdot]; field_simp; ring
  have hxi2 : (ξ - 1) ^ 2 * nv ≤ ∑ i, ‖(w - v') i‖ ^ 2 := by
    have hcs := SmallGeneratorBounds_cs v' (w - v')
    rw [hξ1, div_pow]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have h5 : (ξ - 1) ^ 2 * nv ≤ 4 * (L * n) := hxi2.trans hNe
  have hsq : (ξ - 1) ^ 2 ≤ (1 / 2) ^ 2 := by
    refine le_of_mul_le_mul_right ?_ hnv
    nlinarith
  obtain ⟨hlo, hhi⟩ := abs_le_of_sq_le_sq' hsq (by norm_num)
  have hξlo : (1 / 2 : ℝ) ≤ ξ := by linarith
  have hξhi : ξ ≤ 3 / 2 := by linarith
  refine ⟨hξlo, hξhi, h5, ?_⟩
  have hξpos : 0 < ξ := by linarith
  have hinv : ξ⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hξpos (by norm_num)]; linarith
  have hinv0 : 0 ≤ ξ⁻¹ := inv_nonneg.mpr hξpos.le
  have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξpos.ne'
  have hvec : (((ξ⁻¹ : ℝ) : ℂ) • w - v') =
      ((ξ⁻¹ : ℝ) : ℂ) • ((w - v') - ((ξ - 1 : ℝ) : ℂ) • v') := by
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  rw [hvec, SmallGeneratorBounds_nsq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsm := SmallGeneratorBounds_nsq_sub_le (w - v') (((ξ - 1 : ℝ) : ℂ) • v')
  rw [SmallGeneratorBounds_nsq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hsm
  have hinv2 : (ξ⁻¹) ^ 2 ≤ 4 := by nlinarith
  have hS0 : 0 ≤ ∑ i, ‖((w - v') - ((ξ - 1 : ℝ) : ℂ) • v') i‖ ^ 2 := by positivity
  calc (ξ⁻¹) ^ 2 * ∑ i, ‖((w - v') - ((ξ - 1 : ℝ) : ℂ) • v') i‖ ^ 2
      ≤ 4 * ∑ i, ‖((w - v') - ((ξ - 1 : ℝ) : ℂ) • v') i‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hinv2 hS0
    _ ≤ 4 * (2 * ∑ i, ‖(w - v') i‖ ^ 2 + 2 * ((ξ - 1) ^ 2 * nv)) := by linarith
    _ ≤ 64 * (L * n) := by linarith

/-- (9.19) [su:eq:generator-admissibility] ⇒ (9.20) [us:eq:sourceenergy] and (9.21)
[su:eq:normalized-generator-costs], in squared form. -/
theorem smallGen_bounds {W q : ℕ} {g E : ℝ} (hq : 7 ≤ q) {R : Matrix (Fin W) (Fin W) ℂ}
    (hRh : R.IsHermitian) (t : ℝ) {P : Matrix (Fin W) (Fin W) ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (ω : Ω W q) {v : Fin W → ℂ}
    (hR : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j))
    (hC : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m)) (hT : IsUnit (cavRes W g E q R ω))
    (hPv : P *ᵥ v ≠ 0)
    (hBQ : ∀ u : Fin W → ℂ, retProj W g E q R t ω *ᵥ u = u →
      (1 / 2 : ℝ) * ∑ i, ‖u i‖ ^ 2 ≤ (star u ⬝ᵥ (allowProj P v *ᵥ u)).re)
    (hy : ∑ i, ‖srcVec W g E q R t P ω v i‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2)
    (hA : ‖cavProd W g E q ω (q - 6) *
          specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (t ^ 2)) *
          cavRes W g E q R ω‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 ≤
      (1 / 16 : ℝ) * ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2) :
    ∑ i, ‖srcVec W g E q R t P ω v i‖ ^ 2 ≤ 4 * ∑ i, ‖(retProj W g E q R t ω *ᵥ v) i‖ ^ 2 ∧
    hsSq (gen0 W g E q R t P ω v) ≤
      8 * (∑ i, ‖(retProj W g E q R t ω *ᵥ v) i‖ ^ 2) / ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ∧
    (1 / 2 : ℝ) ≤ genScale W g E q R t P ω v ∧ genScale W g E q R t P ω v ≤ 3 / 2 ∧
    (genScale W g E q R t P ω v - 1) ^ 2 * ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 ≤
      4 * (‖cavProd W g E q ω (q - 6) *
          specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (t ^ 2)) *
          cavRes W g E q R ω‖ ^ 2 * ∑ i, ‖v i‖ ^ 2) ∧
    hsSq (smallGen W g E q R t P ω v) ≤
      32 * (∑ i, ‖(retProj W g E q R t ω *ᵥ v) i‖ ^ 2) / ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ∧
    ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ (smallGen W g E q R t P ω v *ᵥ v) -
        chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 ≤
      64 * (‖cavProd W g E q ω (q - 6) *
          specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (t ^ 2)) *
          cavRes W g E q R ω‖ ^ 2 * ∑ i, ‖v i‖ ^ 2) ∧
    hsSq (smallCorr W g E q R v (smallGen W g E q R t P ω v) ω) *
        ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 ≤
      576 * (‖cavProd W g E q ω (q - 6) *
          specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (t ^ 2)) *
          cavRes W g E q R ω‖ ^ 2 * ∑ i, ‖v i‖ ^ 2) := by
  have hAh : ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self _
  obtain ⟨hSh, hSS, -, -⟩ := specProj_spec hAh (Set.Ioi (t ^ 2))
  obtain ⟨hQh, hQQ, -⟩ := flagProj_spec hT hSh hSS
  have hQh' : (retProj W g E q R t ω)ᴴ = retProj W g E q R t ω := hQh
  have hQQ' : retProj W g E q R t ω * retProj W g E q R t ω = retProj W g E q R t ω := hQQ
  obtain ⟨hPih, hPiP⟩ := SmallGeneratorBounds_allow hP hPP hPv
  have hB := SmallGeneratorBounds_gram_unit hQh' hQQ' hBQ
  have hybd : ∑ i, ‖srcVec W g E q R t P ω v i‖ ^ 2 ≤
      2 * ∑ i, ‖(retProj W g E q R t ω *ᵥ v) i‖ ^ 2 :=
    SmallGeneratorBounds_src_bound hQh' hQQ' hPih hPiP hBQ v
  have hp := SmallGeneratorBounds_pos hPv
  have hb0 : 0 ≤ ∑ i, ‖(retProj W g E q R t ω *ᵥ v) i‖ ^ 2 := by positivity
  have hCunit : IsUnit (chartProd W g E q R ω (q - 1)) := by
    rw [chartProd_eq_cavProd_mul hq R ω hR hC hT]
    exact (SmallGeneratorBounds_cavProd_unit hC (q - 6) le_rfl).mul hT
  have hv0 : v ≠ 0 := fun h => hPv (by rw [h, Matrix.mulVec_zero])
  have hv' : chartProd W g E q R ω (q - 1) *ᵥ v ≠ 0 := fun h =>
    hv0 (Matrix.mulVec_injective_iff_isUnit.mpr hCunit (by rw [h, Matrix.mulVec_zero]))
  have hdisc := discErr_eq hq hRh t P ω v hR hC hT hB
  obtain ⟨hξlo, hξhi, hξsq, hcor⟩ := SmallGeneratorBounds_core (chartProd W g E q R ω (q - 1))
    (cavProd W g E q ω (q - 6) *
      specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (t ^ 2)) *
      cavRes W g E q R ω) v (srcVec W g E q R t P ω v) hv' hdisc hy hA
    (genScale W g E q R t P ω v) rfl
  have hξpos : 0 < genScale W g E q R t P ω v := by linarith
  have hgen : hsSq (gen0 W g E q R t P ω v) ≤
      8 * (∑ i, ‖(retProj W g E q R t ω *ᵥ v) i‖ ^ 2) / ∑ i, ‖(P *ᵥ v) i‖ ^ 2 := by
    refine (SmallGeneratorBounds_hsSq_rank_two hPv (srcVec W g E q R t P ω v)).trans ?_
    exact div_le_div_of_nonneg_right (by linarith) hp.le
  have hKv : smallGen W g E q R t P ω v *ᵥ v = (((genScale W g E q R t P ω v)⁻¹ : ℝ) : ℂ) •
      srcVec W g E q R t P ω v := by
    have h := (smallGen_spec (g := g) (E := E) (q := q) R t hP hPP ω hPv).1.2.2
    unfold smallGen
    rw [Matrix.smul_mulVec, h]
  have hCKv : chartProd W g E q R ω (q - 1) *ᵥ (smallGen W g E q R t P ω v *ᵥ v) =
      (((genScale W g E q R t P ω v)⁻¹ : ℝ) : ℂ) •
        (chartProd W g E q R ω (q - 1) *ᵥ srcVec W g E q R t P ω v) := by
    rw [hKv, Matrix.mulVec_smul]
  rw [hCKv]
  have hinv : ((genScale W g E q R t P ω v)⁻¹) ^ 2 ≤ 4 := by
    have h1 : (genScale W g E q R t P ω v)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hξpos (by norm_num)]; linarith
    have h2 : 0 ≤ (genScale W g E q R t P ω v)⁻¹ := inv_nonneg.mpr hξpos.le
    nlinarith
  refine ⟨by linarith, hgen, hξlo, hξhi, hξsq, ?_, hcor, ?_⟩
  · have hs : smallGen W g E q R t P ω v =
        (((genScale W g E q R t P ω v)⁻¹ : ℝ) : ℂ) • gen0 W g E q R t P ω v := rfl
    rw [hs, SmallGeneratorBounds_hsSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    calc ((genScale W g E q R t P ω v)⁻¹) ^ 2 * hsSq (gen0 W g E q R t P ω v)
        ≤ 4 * (8 * (∑ i, ‖(retProj W g E q R t ω *ᵥ v) i‖ ^ 2) /
            ∑ i, ‖(P *ᵥ v) i‖ ^ 2) := by
          refine mul_le_mul hinv hgen (by unfold hsSq; positivity) (by norm_num)
      _ = 32 * (∑ i, ‖(retProj W g E q R t ω *ᵥ v) i‖ ^ 2) / ∑ i, ‖(P *ᵥ v) i‖ ^ 2 := by ring
  · have hnv := SmallGeneratorBounds_pos hv'
    have h := hsSq_rotCorr_le hv'
      (chartProd W g E q R ω (q - 1) *ᵥ (smallGen W g E q R t P ω v *ᵥ v) -
        chartProd W g E q R ω (q - 1) *ᵥ v)
    rw [hCKv] at h
    have h2 := (le_div_iff₀ hnv).mp h
    change hsSq (rotCorr _ _) * _ ≤ _
    rw [hCKv]
    linarith

end LSBA
