import LSBA.Upper.SmallGeneratorReg
import LSBA.Upper.SmallGeneratorBounds

/-!
# Derivatives of the generator in the source

(9.78) [su:eq:construction-derivative-goals], Section 9.4.3 [su:sec:generator-estimates]. Keep the
active blocks fixed; then `P`, `Q` and `‖P v‖` do not move along `𝓗_v = {w ∈ ran P : Re(v* w) = 0}`.
With `u = Q B_Q⁻¹ Q v` and `‖B_Q⁻¹‖ ≤ 4/3`, the derivative of `y` obeys (9.73)
[su:eq:matching-source-derivative], the unnormalized generator obeys (9.74)
[su:eq:unnormalized-source-response] and `y - v` obeys (9.75) [su:eq:matching-error-derivative].
The quotient rule for `ξ = 1 + ‖v_{q-1}‖⁻² Re(v_{q-1}* e_{q-1})` gives (9.76)
[su:eq:normalization-source-response]:
`‖P v‖² ‖∇ξ‖² ≤ C e (1 + ρ)` with `e = ‖v_{q-1}‖⁻² ‖A_< R̃‖² ‖v‖²` and
`ρ = ‖v_{q-1}‖⁻² ‖P v‖² ‖R_{[q-1,5]}‖²`. The exceptional subspace
`𝓔 = {w ∈ 𝓗_v : Q w = 0, ∇_w ξ = 0}^⊥` has real dimension at most `2 rank Q + 1`, and the two
bounds of (9.27) [su:eq:pair-source-regularity] follow, as in (9.78)
[su:eq:construction-derivative-goals].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Squared norms, Cauchy–Schwarz and Hilbert–Schmidt bounds -/

section Basic

variable {n : Type*} [Fintype n]

/-- The squared Euclidean norm `Σ_i ‖x_i‖²`. -/
private abbrev nq (x : n → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

private lemma nq_nonneg (x : n → ℂ) : 0 ≤ nq x := by positivity

private lemma dot_self (x : n → ℂ) : star x ⬝ᵥ x = ((nq x : ℝ) : ℂ) := by
  simp [dotProduct, Complex.conj_mul', Complex.ofReal_sum]

private lemma re_dot_self (x : n → ℂ) : (star x ⬝ᵥ x).re = nq x := by
  rw [dot_self, Complex.ofReal_re]

private lemma nq_pos {x : n → ℂ} (hx : x ≠ 0) : 0 < nq x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact Finset.sum_pos' (fun _ _ => by positivity)
    ⟨i, Finset.mem_univ _, by have := norm_pos_iff.mpr hi; positivity⟩

private lemma eq_zero_of_nq {x : n → ℂ} (h : nq x = 0) : x = 0 := by
  by_contra hx
  exact (nq_pos hx).ne' h

private lemma nq_smul (c : ℂ) (x : n → ℂ) : nq (c • x) = ‖c‖ ^ 2 * nq x := by
  simp [nq, mul_pow, Finset.mul_sum]

private lemma nq_neg (x : n → ℂ) : nq (-x) = nq x := by
  simp [nq]

private lemma nq_add_le (a b : n → ℂ) : nq (a + b) ≤ 2 * nq a + 2 * nq b := by
  simp only [nq]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (a i) (b i)) 2
  nlinarith [sq_nonneg (‖a i‖ - ‖b i‖)]

private lemma nq_sub_le (a b : n → ℂ) : nq (a - b) ≤ 2 * nq a + 2 * nq b := by
  rw [sub_eq_add_neg]
  exact (nq_add_le a (-b)).trans (by rw [nq_neg])

private lemma norm_dot_sq (a b : n → ℂ) : ‖star a ⬝ᵥ b‖ ^ 2 ≤ nq a * nq b := by
  have h : ‖star a ⬝ᵥ b‖ ≤ √(nq a) * √(nq b) := by
    calc ‖star a ⬝ᵥ b‖ ≤ ∑ i, ‖star (a i) * b i‖ := by
          simpa [dotProduct] using norm_sum_le Finset.univ (fun i => star (a i) * b i)
      _ = ∑ i, ‖a i‖ * ‖b i‖ := by simp
      _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  calc ‖star a ⬝ᵥ b‖ ^ 2 ≤ (√(nq a) * √(nq b)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt (nq_nonneg a), Real.sq_sqrt (nq_nonneg b)]

private lemma re_dot_sq (a b : n → ℂ) : (star a ⬝ᵥ b).re ^ 2 ≤ nq a * nq b := by
  refine le_trans ?_ (norm_dot_sq a b)
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

private lemma re_dot_comm (a b : n → ℂ) : (star a ⬝ᵥ b).re = (star b ⬝ᵥ a).re := by
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]
  ring

private lemma hsSq_nonneg {m : Type*} [Fintype m] (A : Matrix m n ℂ) : 0 ≤ hsSq A := by
  unfold hsSq; positivity

private lemma hsSq_smul {m : Type*} [Fintype m] (z : ℂ) (A : Matrix m n ℂ) :
    hsSq (z • A) = ‖z‖ ^ 2 * hsSq A := by
  simp [hsSq, mul_pow, Finset.mul_sum]

private lemma hsSq_add_le {m : Type*} [Fintype m] (A B : Matrix m n ℂ) :
    hsSq (A + B) ≤ 2 * hsSq A + 2 * hsSq B := by
  unfold hsSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  simp only [Matrix.add_apply]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (A a b) (B a b)) 2
  nlinarith [sq_nonneg (‖A a b‖ - ‖B a b‖)]

private lemma hsSq_sub_le {m : Type*} [Fintype m] (A B : Matrix m n ℂ) :
    hsSq (A - B) ≤ 2 * hsSq A + 2 * hsSq B := by
  rw [sub_eq_add_neg]
  refine (hsSq_add_le A (-B)).trans (le_of_eq ?_)
  simp [hsSq]

private lemma hsSq_vecMulVec {m : Type*} [Fintype m] (x : m → ℂ) (y : n → ℂ) :
    hsSq (Matrix.vecMulVec x (star y)) = nq x * nq y := by
  simp [hsSq, Matrix.vecMulVec, mul_pow, Finset.sum_mul_sum]

private lemma nq_mulVec_le_hsSq (A : Matrix n n ℂ) (x : n → ℂ) :
    nq (A *ᵥ x) ≤ hsSq A * nq x := by
  unfold hsSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(A *ᵥ x) i‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ := by
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖) (fun j => ‖x j‖)
  calc ‖(A *ᵥ x) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖x j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

end Basic

section Mat

variable {W : ℕ}

private lemma nq_opNorm (A : Matrix (Fin W) (Fin W) ℂ) (x : Fin W → ℂ) :
    nq (A *ᵥ x) ≤ ‖A‖ ^ 2 * nq x := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  have h1 : ‖(EuclideanSpace.equiv (Fin W) ℂ).symm (A *ᵥ x)‖ ^ 2 = nq (A *ᵥ x) := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h2 : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin W))‖ ^ 2 = nq x := by
    rw [EuclideanSpace.norm_sq_eq]
  rw [← h1, ← h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- For a Hermitian `A`, `a* (A b) = (A a)* b`. -/
private lemma dot_herm {A : Matrix (Fin W) (Fin W) ℂ} (hA : Aᴴ = A) (a b : Fin W → ℂ) :
    star a ⬝ᵥ (A *ᵥ b) = star (A *ᵥ a) ⬝ᵥ b := by
  rw [Matrix.star_mulVec, hA, Matrix.dotProduct_mulVec]

/-- An orthogonal projection `Π` has `‖Π z‖² = Re(z* Π z) ≤ ‖z‖²`. -/
private lemma proj_nq {Pi : Matrix (Fin W) (Fin W) ℂ} (hh : Piᴴ = Pi) (hi : Pi * Pi = Pi)
    (z : Fin W → ℂ) :
    nq (Pi *ᵥ z) = (star z ⬝ᵥ (Pi *ᵥ z)).re ∧ nq (Pi *ᵥ z) ≤ nq z := by
  have h1 : nq (Pi *ᵥ z) = (star z ⬝ᵥ (Pi *ᵥ z)).re := by
    rw [← re_dot_self, ← dot_herm hh, Matrix.mulVec_mulVec, hi]
  refine ⟨h1, ?_⟩
  have h2 := re_dot_sq z (Pi *ᵥ z)
  rw [← h1] at h2
  have h0 := nq_nonneg (Pi *ᵥ z)
  rcases h0.eq_or_lt with h | h
  · rw [← h]; exact nq_nonneg z
  · nlinarith

/-- The allowed projection `Π = P - ‖P v‖⁻² (P v)(P v)*` is an orthogonal projection with
`Π (P v) = 0` when `P` is one and `P v ≠ 0`. -/
private lemma allow_spec {P : Matrix (Fin W) (Fin W) ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    {v : Fin W → ℂ} (hv : P *ᵥ v ≠ 0) :
    (allowProj P v)ᴴ = allowProj P v ∧ allowProj P v * allowProj P v = allowProj P v ∧
      allowProj P v *ᵥ (P *ᵥ v) = 0 := by
  have hpos := nq_pos hv
  set u := P *ᵥ v with hu
  have hPh : Pᴴ = P := hP.eq
  have hPu : P *ᵥ u = u := by rw [hu, Matrix.mulVec_mulVec, hPP]
  have hnr := dot_self u
  set c : ℝ := (nq u)⁻¹ with hc
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
  have hPiP : allowProj P v * P = allowProj P v := by
    have h := congrArg Matrix.conjTranspose hPPi
    rwa [Matrix.conjTranspose_mul, hPi_h, hPh] at h
  have hsPi : star u ᵥ* allowProj P v = 0 := by
    rw [hsu, Matrix.vecMul_vecMul, hPPi]
    have h := Matrix.star_mulVec (allowProj P v) v
    rw [hPiv, hPi_h] at h
    simpa using h.symm
  refine ⟨hPi_h, ?_, ?_⟩
  · have hdef : allowProj P v = P - (c : ℂ) • Matrix.vecMulVec u (star u) := by
      unfold allowProj; rw [← hu, hcn]
    have h : allowProj P v * allowProj P v =
        P * allowProj P v - (c : ℂ) • (Matrix.vecMulVec u (star u) * allowProj P v) := by
      conv_lhs => arg 1; rw [hdef]
      rw [Matrix.sub_mul, Matrix.smul_mul]
    rw [h, hPPi, Matrix.vecMulVec_mul, hsPi]
    simp
  · rw [hu, Matrix.mulVec_mulVec, hPiP, hPiv]

/-- The matrix `X = Q Π Q + 1 - Q`, whose inverse realizes `B_Q⁻¹` on `ran Q`. -/
private def gdX (P Q : Matrix (Fin W) (Fin W) ℂ) (x : Fin W → ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  Q * allowProj P x * Q + (1 - Q)

/-- `G = Q X⁻¹ Q = Q B_Q⁻¹ Q`. -/
private def gdG (P Q : Matrix (Fin W) (Fin W) ℂ) (x : Fin W → ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  Q * (gdX P Q x)⁻¹ * Q

/-- With `Q` idempotent and `X` invertible: `Q G = G`, `G Q = G`, `Q Π G = Q`, and `G` is
`X⁻¹ Q` and `Q X⁻¹`. -/
private lemma qalg {P Q : Matrix (Fin W) (Fin W) ℂ} {x : Fin W → ℂ} (hQQ : Q * Q = Q)
    (hX : IsUnit (gdX P Q x)) :
    Q * gdG P Q x = gdG P Q x ∧ gdG P Q x * Q = gdG P Q x ∧
      Q * allowProj P x * gdG P Q x = Q ∧ Q * (gdX P Q x)⁻¹ = (gdX P Q x)⁻¹ * Q := by
  set X := gdX P Q x with hXdef
  set Pi := allowProj P x with hPi
  have hd : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det _).mp hX
  have h1 : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h2 : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul _ hd
  have hQX : Q * X = Q * Pi * Q := by
    simp only [hXdef, gdX, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      hQQ]
    abel
  have hXQ : X * Q = Q * Pi * Q := by
    simp only [hXdef, gdX, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hQQ]
    abel
  have hc : Q * X⁻¹ = X⁻¹ * Q :=
    calc Q * X⁻¹ = X⁻¹ * X * Q * X⁻¹ := by rw [h2, Matrix.one_mul]
      _ = X⁻¹ * (X * Q) * X⁻¹ := by simp only [Matrix.mul_assoc]
      _ = X⁻¹ * (Q * X) * X⁻¹ := by rw [hXQ, hQX]
      _ = X⁻¹ * Q * (X * X⁻¹) := by simp only [Matrix.mul_assoc]
      _ = X⁻¹ * Q := by rw [h1, Matrix.mul_one]
  have hG : gdG P Q x = Q * X⁻¹ * Q := rfl
  refine ⟨?_, ?_, ?_, hc⟩
  · rw [hG, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ]
  · rw [hG, Matrix.mul_assoc, hQQ]
  · calc Q * Pi * gdG P Q x = (X * Q) * X⁻¹ * Q := by
          rw [hXQ, hG]; simp only [Matrix.mul_assoc]
      _ = X * (Q * X⁻¹) * Q := by simp only [Matrix.mul_assoc]
      _ = Q := by rw [hc, ← Matrix.mul_assoc, h1, Matrix.one_mul, hQQ]

/-- `B_Q ≥ 3/4` on `ran Q` gives `‖G z‖² ≤ (16/9) ‖Q z‖²`, i.e. `‖B_Q⁻¹‖ ≤ 4/3`. -/
private lemma gbound {P Q : Matrix (Fin W) (Fin W) ℂ} {x : Fin W → ℂ} (hQh : Qᴴ = Q)
    (hQQ : Q * Q = Q) (hX : IsUnit (gdX P Q x))
    (hBQ : ∀ u : Fin W → ℂ, Q *ᵥ u = u →
      (3 / 4 : ℝ) * nq u ≤ (star u ⬝ᵥ (allowProj P x *ᵥ u)).re) (z : Fin W → ℂ) :
    nq (gdG P Q x *ᵥ z) ≤ 16 / 9 * nq (Q *ᵥ z) := by
  obtain ⟨hQG, -, hQPG, -⟩ := qalg hQQ hX
  set a := gdG P Q x *ᵥ z with ha
  have hQa : Q *ᵥ a = a := by rw [ha, Matrix.mulVec_mulVec, hQG]
  have hQPa : Q *ᵥ (allowProj P x *ᵥ a) = Q *ᵥ z := by
    rw [ha, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQPG]
  have h3 := hBQ a hQa
  have hd : star a ⬝ᵥ (allowProj P x *ᵥ a) = star a ⬝ᵥ (Q *ᵥ z) := by
    rw [← hQPa, dot_herm hQh, hQa]
  rw [hd] at h3
  have h4 := re_dot_sq a (Q *ᵥ z)
  have h0 := nq_nonneg a
  have h5 := nq_nonneg (Q *ᵥ z)
  rcases h0.eq_or_lt with h | h
  · rw [← h]; positivity
  · nlinarith

end Mat

/-! ### Derivatives along a line

The ℝ-bilinear maps `(M, z) ↦ M z`, `(a, b) ↦ a* b` and `(a, b) ↦ a b*` are continuous, which
gives the product rules; the derivative of `s ↦ X(s)⁻¹` at an invertible point is
`-X⁻¹ X' X⁻¹`. -/

section Deriv

variable {W : ℕ}

/-- An ℝ-bilinear map between finite-dimensional spaces, as a continuous bilinear map. -/
private def clm₂ {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (B : E →ₗ[ℝ] F →ₗ[ℝ] G) : E →L[ℝ] F →L[ℝ] G :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (F →ₗ[ℝ] G) ≃ₗ[ℝ] (F →L[ℝ] G)).toLinearMap ∘ₗ B)

/-- `(M, z) ↦ M z`. -/
private def bMV : Matrix (Fin W) (Fin W) ℂ →L[ℝ] (Fin W → ℂ) →L[ℝ] (Fin W → ℂ) :=
  clm₂ (LinearMap.mk₂ ℝ (fun M z => M *ᵥ z) (fun M N z => Matrix.add_mulVec M N z)
    (fun c M z => Matrix.smul_mulVec c M z) (fun M z z' => Matrix.mulVec_add M z z')
    (fun c M z => Matrix.mulVec_smul M c z))

/-- `(a, b) ↦ a* b`. -/
private def bDot : (Fin W → ℂ) →L[ℝ] (Fin W → ℂ) →L[ℝ] ℂ :=
  clm₂ (LinearMap.mk₂ ℝ (fun a b => star a ⬝ᵥ b)
    (fun a a' b => by rw [star_add, add_dotProduct])
    (fun c a b => by rw [star_smul, star_trivial, smul_dotProduct])
    (fun a b b' => dotProduct_add _ _ _) (fun c a b => dotProduct_smul _ _ _))

/-- `(a, b) ↦ a b*`. -/
private def bOut : (Fin W → ℂ) →L[ℝ] (Fin W → ℂ) →L[ℝ] Matrix (Fin W) (Fin W) ℂ :=
  clm₂ (LinearMap.mk₂ ℝ (fun a b => Matrix.vecMulVec a (star b))
    (fun a a' b => by ext i j; simp [Matrix.vecMulVec_apply, add_mul])
    (fun c a b => by ext i j; simp [Matrix.vecMulVec_apply, mul_assoc])
    (fun a b b' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add])
    (fun c a b => by ext i j; simp [Matrix.vecMulVec_apply]; ring))

private lemma hd_mulVec {f : ℝ → Matrix (Fin W) (Fin W) ℂ} {g : ℝ → Fin W → ℂ}
    {f' : Matrix (Fin W) (Fin W) ℂ} {g' : Fin W → ℂ} {x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun s => f s *ᵥ g s) (f' *ᵥ g x + f x *ᵥ g') x := by
  have h1 : HasDerivAt (fun s => bMV (f s)) (bMV f') x := bMV.hasFDerivAt.comp_hasDerivAt x hf
  exact h1.clm_apply hg

private lemma hd_dot {f g : ℝ → Fin W → ℂ} {f' g' : Fin W → ℂ} {x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun s => star (f s) ⬝ᵥ g s) (star f' ⬝ᵥ g x + star (f x) ⬝ᵥ g') x := by
  have h1 : HasDerivAt (fun s => bDot (f s)) (bDot f') x := bDot.hasFDerivAt.comp_hasDerivAt x hf
  exact h1.clm_apply hg

private lemma hd_out {f g : ℝ → Fin W → ℂ} {f' g' : Fin W → ℂ} {x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun s => Matrix.vecMulVec (f s) (star (g s)))
      (Matrix.vecMulVec f' (star (g x)) + Matrix.vecMulVec (f x) (star g')) x := by
  have h00 : HasFDerivAt (bOut (W := W)) (bOut (W := W)) (f x) := (bOut (W := W)).hasFDerivAt
  have h0 := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := Fin W → ℂ)
    (E := (Fin W → ℂ) →L[ℝ] Matrix (Fin W) (Fin W) ℂ) x h00 hf
  exact HasDerivAt.clm_apply (G := Matrix (Fin W) (Fin W) ℂ) h0 hg

private lemma hd_inv {f : ℝ → Matrix (Fin W) (Fin W) ℂ} {f' : Matrix (Fin W) (Fin W) ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hu : IsUnit (f x)) :
    HasDerivAt (fun s => (f s)⁻¹) (-((f x)⁻¹ * f' * (f x)⁻¹)) x := by
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  rw [hu.unit_spec] at h
  have h2 := h.comp_hasDerivAt x hf
  have hi : ((hu.unit⁻¹ : (Matrix (Fin W) (Fin W) ℂ)ˣ) : Matrix (Fin W) (Fin W) ℂ) =
      (f x)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← Ring.inverse_unit hu.unit, hu.unit_spec]
  simp_rw [Matrix.nonsing_inv_eq_ringInverse] at hi ⊢
  have h3 : (-((ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin W) (Fin W) ℂ)) ↑hu.unit⁻¹)
      ↑hu.unit⁻¹) f' = -(Ring.inverse (f x) * f' * Ring.inverse (f x)) := by
    rw [hi]; simp
  exact h2.congr_deriv h3

/-- The vector `y = Π Q X⁻¹ Q x` of (9.16) [us:eq:H0]. -/
private def gdY (P Q : Matrix (Fin W) (Fin W) ℂ) (x : Fin W → ℂ) : Fin W → ℂ :=
  (allowProj P x * Q * (gdX P Q x)⁻¹ * Q) *ᵥ x

/-- The generator `K_0 = ‖P x‖⁻² (y (P x)* - (P x) y*)` of (9.16) [us:eq:H0]. -/
private def gdK0 (P Q : Matrix (Fin W) (Fin W) ℂ) (x : Fin W → ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (star (P *ᵥ x) ⬝ᵥ (P *ᵥ x))⁻¹ •
    (Matrix.vecMulVec (gdY P Q x) (star (P *ᵥ x)) - Matrix.vecMulVec (P *ᵥ x) (star (gdY P Q x)))

/-- The scale `ξ = ‖M x‖⁻² Re((M x)* M y)` of (9.18) [us:eq:normalize]. -/
private def gdXi (P Q M : Matrix (Fin W) (Fin W) ℂ) (x : Fin W → ℂ) : ℝ :=
  (star (M *ᵥ x) ⬝ᵥ (M *ᵥ gdY P Q x)).re / ∑ i, ‖(M *ᵥ x) i‖ ^ 2

/-- The generator `K = K_0 / ξ` of (9.18) [us:eq:normalize]. -/
private def gdK (P Q M : Matrix (Fin W) (Fin W) ℂ) (x : Fin W → ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (((gdXi P Q M x)⁻¹ : ℝ) : ℂ) • gdK0 P Q x

/-- `∇_w Π = -‖P v‖⁻² (w (P v)* + (P v) w*)` along `w ∈ 𝓗_v`. -/
private def gdP' (P : Matrix (Fin W) (Fin W) ℂ) (v w : Fin W → ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  -((star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ •
    (Matrix.vecMulVec w (star (P *ᵥ v)) + Matrix.vecMulVec (P *ᵥ v) (star w)))

/-- `∇_w y = (∇_w Π) u - Π G (∇_w Π) u + Π G w` with `u = G v`. -/
private def gdY' (P Q : Matrix (Fin W) (Fin W) ℂ) (v w : Fin W → ℂ) : Fin W → ℂ :=
  (gdP' P v w * gdG P Q v - allowProj P v * gdG P Q v * gdP' P v w * gdG P Q v) *ᵥ v +
    (allowProj P v * gdG P Q v) *ᵥ w

/-- `∇_w K_0`. -/
private def gdK0' (P Q : Matrix (Fin W) (Fin W) ℂ) (v w : Fin W → ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  (star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ •
    ((Matrix.vecMulVec (gdY' P Q v w) (star (P *ᵥ v)) + Matrix.vecMulVec (gdY P Q v) (star w)) -
      (Matrix.vecMulVec w (star (gdY P Q v)) + Matrix.vecMulVec (P *ᵥ v) (star (gdY' P Q v w))))

/-- `∇_w ξ` by the quotient rule. -/
private def gdXi' (P Q M : Matrix (Fin W) (Fin W) ℂ) (v w : Fin W → ℂ) : ℝ :=
  ((star (M *ᵥ w) ⬝ᵥ (M *ᵥ gdY P Q v) + star (M *ᵥ v) ⬝ᵥ (M *ᵥ gdY' P Q v w)).re *
      nq (M *ᵥ v) -
    (star (M *ᵥ v) ⬝ᵥ (M *ᵥ gdY P Q v)).re *
      (star (M *ᵥ w) ⬝ᵥ (M *ᵥ v) + star (M *ᵥ v) ⬝ᵥ (M *ᵥ w)).re) / nq (M *ᵥ v) ^ 2

/-- `∇_w K = ξ⁻¹ ∇_w K_0 - ξ⁻² (∇_w ξ) K_0`. -/
private def gdK' (P Q M : Matrix (Fin W) (Fin W) ℂ) (v w : Fin W → ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  (((gdXi P Q M v)⁻¹ : ℝ) : ℂ) • gdK0' P Q v w +
    ((-gdXi' P Q M v w / gdXi P Q M v ^ 2 : ℝ) : ℂ) • gdK0 P Q v

private lemma star_dot_conj (a b : Fin W → ℂ) :
    star b ⬝ᵥ a = (starRingEnd ℂ) (star a ⬝ᵥ b) := by
  simp [dotProduct, mul_comm]

/-- The derivatives of `ξ` and `K` along `s ↦ v + s w` for `w ∈ 𝓗_v`. -/
private lemma gd_hasDeriv {P Q M : Matrix (Fin W) (Fin W) ℂ} {v w : Fin W → ℂ} (hP : Pᴴ = P)
    (hPw : P *ᵥ w = w) (hre : (star v ⬝ᵥ w).re = 0) (hPv : P *ᵥ v ≠ 0)
    (hX : IsUnit (gdX P Q v)) (hD : nq (M *ᵥ v) ≠ 0) (hξ : gdXi P Q M v ≠ 0) :
    HasDerivAt (fun s : ℝ => gdXi P Q M (v + s • w)) (gdXi' P Q M v w) 0 ∧
      HasDerivAt (fun s : ℝ => gdK P Q M (v + s • w)) (gdK' P Q M v w) 0 := by
  have h0 : v + (0 : ℝ) • w = v := by simp
  have hx : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
    simpa using this
  have hp : HasDerivAt (fun s : ℝ => P *ᵥ (v + s • w)) w 0 := by
    have := hd_mulVec (hasDerivAt_const (0 : ℝ) P) hx
    simpa [hPw] using this
  set p := P *ᵥ v with hpdef
  have hpw : star p ⬝ᵥ w = star v ⬝ᵥ w := by rw [hpdef, ← dot_herm hP, hPw]
  have hN' : star w ⬝ᵥ p + star p ⬝ᵥ w = 0 := by
    rw [star_dot_conj, hpw]
    apply Complex.ext <;> simp [hre]
  have hN0 : star p ⬝ᵥ p ≠ 0 := by
    rw [dot_self]; exact_mod_cast (nq_pos hPv).ne' 
  have hN : HasDerivAt (fun s : ℝ => star (P *ᵥ (v + s • w)) ⬝ᵥ (P *ᵥ (v + s • w))) 0 0 := by
    have := hd_dot hp hp
    simp only [h0] at this
    rwa [hN'] at this
  have hNi := (hN.inv (by simp only [h0]; exact hN0)).congr_deriv (show _ = (0 : ℂ) by simp)
  have hPi : HasDerivAt (fun s : ℝ => allowProj P (v + s • w)) (gdP' P v w) 0 := by
    have := (hasDerivAt_const (0 : ℝ) P).sub (hNi.smul (hd_out hp hp))
    refine this.congr_deriv ?_
    simp only [h0, gdP']
    simp
  have hXm : HasDerivAt (fun s : ℝ => gdX P Q (v + s • w)) (Q * gdP' P v w * Q) 0 :=
    ((hPi.const_mul Q).mul_const Q).add_const (1 - Q)
  have hXi := hd_inv hXm (by simp only [h0]; exact hX)
  simp only [h0] at hXi
  have hY : HasDerivAt (fun s : ℝ => gdY P Q (v + s • w)) (gdY' P Q v w) 0 := by
    have := hd_mulVec (((hPi.mul_const Q).mul hXi).mul_const Q) hx
    refine this.congr_deriv ?_
    simp only [h0, gdY', gdG, Pi.mul_apply]
    congr 1
    · congr 1
      noncomm_ring
    · simp only [Matrix.mul_assoc]
  have hK0 : HasDerivAt (fun s : ℝ => gdK0 P Q (v + s • w)) (gdK0' P Q v w) 0 := by
    have := hNi.smul ((hd_out hY hp).sub (hd_out hp hY))
    refine this.congr_deriv ?_
    simp only [h0, gdK0']
    simp
  have hMx : HasDerivAt (fun s : ℝ => M *ᵥ (v + s • w)) (M *ᵥ w) 0 := by
    have := hd_mulVec (hasDerivAt_const (0 : ℝ) M) hx
    simpa using this
  have hMy : HasDerivAt (fun s : ℝ => M *ᵥ gdY P Q (v + s • w)) (M *ᵥ gdY' P Q v w) 0 := by
    have := hd_mulVec (hasDerivAt_const (0 : ℝ) M) hY
    simpa using this
  have hnum := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd_dot hMx hMy)
  have hden := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd_dot hMx hMx)
  have hden' : (fun s : ℝ => ∑ i, ‖(M *ᵥ (v + s • w)) i‖ ^ 2) =
      (Complex.reCLM ∘ fun s : ℝ => star (M *ᵥ (v + s • w)) ⬝ᵥ (M *ᵥ (v + s • w))) := by
    funext s
    simp only [Function.comp, Complex.reCLM_apply, re_dot_self]
  rw [← hden'] at hden
  have hξd := hnum.div hden (by simp only [h0]; exact hD)
  have hξd' : HasDerivAt (fun s : ℝ => gdXi P Q M (v + s • w)) (gdXi' P Q M v w) 0 := by
    refine hξd.congr_deriv ?_
    simp only [h0, gdXi', Function.comp, Complex.reCLM_apply]
  refine ⟨hξd', ?_⟩
  have hK := (hξd'.inv (by simp only [h0]; exact hξ)).ofReal_comp.smul hK0
  refine hK.congr_deriv ?_
  simp only [h0, gdK', Pi.inv_apply]

private lemma da_mulVec {f : (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {g : (Fin W → ℂ) → Fin W → ℂ}
    {x : Fin W → ℂ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => f y *ᵥ g y) x :=
  (bMV.differentiableAt.comp x hf).clm_apply hg

private lemma da_dot {f g : (Fin W → ℂ) → Fin W → ℂ} {x : Fin W → ℂ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => star (f y) ⬝ᵥ g y) x :=
  (bDot.differentiableAt.comp x hf).clm_apply hg

private lemma da_out {f g : (Fin W → ℂ) → Fin W → ℂ} {x : Fin W → ℂ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => Matrix.vecMulVec (f y) (star (g y))) x := by
  have h0 := DifferentiableAt.comp (𝕜 := ℝ) (F := Fin W → ℂ)
    (G := (Fin W → ℂ) →L[ℝ] Matrix (Fin W) (Fin W) ℂ) x (bOut (W := W)).differentiableAt hf
  exact DifferentiableAt.clm_apply (H := Matrix (Fin W) (Fin W) ℂ) h0 hg

private lemma da_inv {f : (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {x : Fin W → ℂ}
    (hf : DifferentiableAt ℝ f x) (hu : IsUnit (f x)) :
    DifferentiableAt ℝ (fun y => (f y)⁻¹) x := by
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  exact (differentiableAt_inverse (𝕜 := ℝ) hu).comp x hf

/-- `x ↦ ξ(x)` is differentiable at a point where `P x ≠ 0`, `X` is invertible and `M x ≠ 0`. -/
private lemma gd_diffXi {P Q M : Matrix (Fin W) (Fin W) ℂ} {v : Fin W → ℂ} (hPv : P *ᵥ v ≠ 0)
    (hX : IsUnit (gdX P Q v)) (hD : nq (M *ᵥ v) ≠ 0) :
    DifferentiableAt ℝ (gdXi P Q M) v := by
  have hid : DifferentiableAt ℝ (fun y : Fin W → ℂ => y) v := differentiableAt_id
  have hp : DifferentiableAt ℝ (fun y : Fin W → ℂ => P *ᵥ y) v :=
    da_mulVec (differentiableAt_const P) hid
  have hN0 : star (P *ᵥ v) ⬝ᵥ (P *ᵥ v) ≠ 0 := by
    rw [dot_self]; exact_mod_cast (nq_pos hPv).ne'
  have hPi : DifferentiableAt ℝ (fun y => allowProj P y) v := by
    unfold allowProj
    exact (differentiableAt_const P).sub (((da_dot hp hp).inv hN0).smul (da_out hp hp))
  have hXd : DifferentiableAt ℝ (fun y => gdX P Q y) v :=
    (((differentiableAt_const Q).mul hPi).mul (differentiableAt_const Q)).add
      (differentiableAt_const _)
  have hY : DifferentiableAt ℝ (fun y => gdY P Q y) v :=
    da_mulVec (((hPi.mul (differentiableAt_const Q)).mul (da_inv hXd hX)).mul
      (differentiableAt_const Q)) hid
  have hMx : DifferentiableAt ℝ (fun y : Fin W → ℂ => M *ᵥ y) v :=
    da_mulVec (differentiableAt_const M) hid
  have hMy : DifferentiableAt ℝ (fun y => M *ᵥ gdY P Q y) v :=
    da_mulVec (differentiableAt_const M) hY
  have hnum := Complex.reCLM.differentiableAt.comp v (da_dot hMx hMy)
  have hden : DifferentiableAt ℝ (fun y : Fin W → ℂ => ∑ i, ‖(M *ᵥ y) i‖ ^ 2) v :=
    DifferentiableAt.fun_sum fun i _ => (differentiableAt_pi.1 hMx i).norm_sq ℝ
  have hi := DifferentiableAt.inv (h := fun y : Fin W → ℂ => ∑ i, ‖(M *ᵥ y) i‖ ^ 2) hden hD
  have h := hnum.mul hi
  have he : gdXi P Q M = (Complex.reCLM ∘ fun y => star (M *ᵥ y) ⬝ᵥ (M *ᵥ gdY P Q y)) *
      (fun y : Fin W → ℂ => ∑ i, ‖(M *ᵥ y) i‖ ^ 2)⁻¹ := by
    funext y
    simp [gdXi, div_eq_mul_inv]
  rw [he]
  exact h

end Deriv

/-! ### The source estimates

(9.73) [su:eq:matching-source-derivative]–(9.76) [su:eq:normalization-source-response]. Here
`p = P v`, `u = G v = Q B_Q⁻¹ Q v` and `y = Π u`. With `‖B_Q⁻¹‖ ≤ 4/3` and `4 ‖Q v‖² ≤ ‖P v‖²`:
`‖u‖² ≤ (4/9) ‖p‖²` and `(3/4) ‖u‖² ≤ ‖y‖² ≤ ‖u‖²`. -/

section Bounds

variable {W : ℕ}

private lemma gd_y {P Q : Matrix (Fin W) (Fin W) ℂ} {v : Fin W → ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (hQh : Qᴴ = Q) (hQQ : Q * Q = Q) (hPv : P *ᵥ v ≠ 0)
    (hX : IsUnit (gdX P Q v))
    (hBQ : ∀ u : Fin W → ℂ, Q *ᵥ u = u →
      (3 / 4 : ℝ) * nq u ≤ (star u ⬝ᵥ (allowProj P v *ᵥ u)).re)
    (hQv : 4 * nq (Q *ᵥ v) ≤ nq (P *ᵥ v)) :
    gdY P Q v = allowProj P v *ᵥ (gdG P Q v *ᵥ v) ∧
      nq (gdG P Q v *ᵥ v) ≤ 4 / 9 * nq (P *ᵥ v) ∧
      nq (gdY P Q v) ≤ nq (gdG P Q v *ᵥ v) ∧
      3 / 4 * nq (gdG P Q v *ᵥ v) ≤ nq (gdY P Q v) ∧
      Q *ᵥ gdY P Q v = Q *ᵥ v ∧ nq (P *ᵥ v) ≤ nq v := by
  obtain ⟨hAh, hAA, -⟩ := allow_spec hP hPP hPv
  obtain ⟨hQG, -, hQAG, -⟩ := qalg hQQ hX
  have hy : gdY P Q v = allowProj P v *ᵥ (gdG P Q v *ᵥ v) := by
    unfold gdY gdG
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc]
  have hu := gbound hQh hQQ hX hBQ v
  have hQu : Q *ᵥ (gdG P Q v *ᵥ v) = gdG P Q v *ᵥ v := by rw [Matrix.mulVec_mulVec, hQG]
  have h1 := proj_nq hAh hAA (gdG P Q v *ᵥ v)
  refine ⟨hy, by linarith, ?_, ?_, ?_, (proj_nq hP.eq hPP v).2⟩
  · rw [hy]; exact h1.2
  · rw [hy, h1.1]; exact hBQ _ hQu
  · rw [hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQAG]

private lemma gd_dy {P Q : Matrix (Fin W) (Fin W) ℂ} {v w : Fin W → ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (hQh : Qᴴ = Q) (hQQ : Q * Q = Q) (hPv : P *ᵥ v ≠ 0)
    (hX : IsUnit (gdX P Q v))
    (hBQ : ∀ u : Fin W → ℂ, Q *ᵥ u = u →
      (3 / 4 : ℝ) * nq u ≤ (star u ⬝ᵥ (allowProj P v *ᵥ u)).re) :
    Q *ᵥ (gdY' P Q v w - w) = 0 ∧
      nq (P *ᵥ v) * nq (gdY' P Q v w) ≤
        400 / 9 * nq (gdG P Q v *ᵥ v) * nq w + 32 / 9 * nq (P *ᵥ v) * nq (Q *ᵥ w) := by
  obtain ⟨hAh, hAA, -⟩ := allow_spec hP hPP hPv
  obtain ⟨-, -, hQAG, -⟩ := qalg hQQ hX
  set G := gdG P Q v with hG
  set A := allowProj P v with hA
  set p := P *ᵥ v with hp
  set u := G *ᵥ v with hu
  set z := gdP' P v w *ᵥ u with hz
  set S := A * G with hS
  have hdy : gdY' P Q v w = z - S *ᵥ z + S *ᵥ w := by
    simp only [gdY', hz, hS, hu, Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.mul_assoc, ← hG,
      ← hA]
  have hQS : Q * S = Q := by rw [hS, ← Matrix.mul_assoc, hQAG]
  have hQSx : ∀ x, Q *ᵥ (S *ᵥ x) = Q *ᵥ x := fun x => by rw [Matrix.mulVec_mulVec, hQS]
  refine ⟨?_, ?_⟩
  · rw [hdy, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_sub, hQSx, hQSx]
    abel
  have hpos := nq_pos hPv
  have hSb : ∀ x, nq (S *ᵥ x) ≤ 16 / 9 * nq (Q *ᵥ x) := fun x => by
    rw [hS, ← Matrix.mulVec_mulVec]
    exact ((proj_nq hAh hAA _).2).trans (gbound hQh hQQ hX hBQ x)
  have hQx : ∀ x, nq (Q *ᵥ x) ≤ nq x := fun x => (proj_nq hQh hQQ x).2
  have hzb : nq p * nq z ≤ 4 * nq u * nq w := by
    have hz' : z = -(((nq p : ℝ) : ℂ)⁻¹ • ((star p ⬝ᵥ u) • w + (star w ⬝ᵥ u) • p)) := by
      rw [hz, gdP', ← hp, dot_self, Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
        Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul]
    have hX1 : nq ((star p ⬝ᵥ u) • w + (star w ⬝ᵥ u) • p) ≤ 4 * nq p * nq u * nq w := by
      refine (nq_add_le _ _).trans ?_
      rw [nq_smul, nq_smul]
      have h1 := norm_dot_sq p u
      have h2 := norm_dot_sq w u
      have := nq_nonneg w
      have := nq_nonneg p
      nlinarith
    have hn : ‖(((nq p : ℝ) : ℂ))⁻¹‖ ^ 2 = (nq p)⁻¹ ^ 2 := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    rw [hz', nq_neg, nq_smul, hn]
    calc nq p * ((nq p)⁻¹ ^ 2 * nq ((star p ⬝ᵥ u) • w + (star w ⬝ᵥ u) • p))
        = (nq p)⁻¹ * nq ((star p ⬝ᵥ u) • w + (star w ⬝ᵥ u) • p) := by
          field_simp
      _ ≤ (nq p)⁻¹ * (4 * nq p * nq u * nq w) :=
          mul_le_mul_of_nonneg_left hX1 (inv_nonneg.mpr hpos.le)
      _ = 4 * nq u * nq w := by field_simp
  have hdyb : nq (gdY' P Q v w) ≤ 100 / 9 * nq z + 32 / 9 * nq (Q *ᵥ w) := by
    rw [hdy]
    have h1 := nq_add_le (z - S *ᵥ z) (S *ᵥ w)
    have h2 := nq_sub_le z (S *ᵥ z)
    have h3 := hSb z
    have h4 := hQx z
    have h5 := hSb w
    nlinarith
  have := nq_nonneg (Q *ᵥ w)
  nlinarith

/-- (9.74) [su:eq:unnormalized-source-response]: `‖p‖⁴ ‖∇_w K_0‖²_HS ≤ 8 ‖p‖² ‖∇_w y‖² +
8 ‖y‖² ‖w‖²`; also `‖p‖² ‖K_0‖²_HS ≤ 4 ‖y‖²` and `‖y‖² ≤ ‖p‖² ‖K_0‖²_HS`, since `K_0 p = y`. -/
private lemma gd_k0 {P Q : Matrix (Fin W) (Fin W) ℂ} {v w : Fin W → ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (hPv : P *ᵥ v ≠ 0) :
    nq (P *ᵥ v) ^ 2 * hsSq (gdK0' P Q v w) ≤
        8 * nq (P *ᵥ v) * nq (gdY' P Q v w) + 8 * nq (gdY P Q v) * nq w ∧
      nq (P *ᵥ v) * hsSq (gdK0 P Q v) ≤ 4 * nq (gdY P Q v) ∧
      nq (gdY P Q v) ≤ nq (P *ᵥ v) * hsSq (gdK0 P Q v) := by
  obtain ⟨hAh, -, hAp⟩ := allow_spec hP hPP hPv
  have hpos := nq_pos hPv
  have hK0'd : gdK0' P Q v w = (star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ •
      ((Matrix.vecMulVec (gdY' P Q v w) (star (P *ᵥ v)) +
        Matrix.vecMulVec (gdY P Q v) (star w)) -
      (Matrix.vecMulVec w (star (gdY P Q v)) +
        Matrix.vecMulVec (P *ᵥ v) (star (gdY' P Q v w)))) := rfl
  have hK0d : gdK0 P Q v = (star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ •
      (Matrix.vecMulVec (gdY P Q v) (star (P *ᵥ v)) -
        Matrix.vecMulVec (P *ᵥ v) (star (gdY P Q v))) := rfl
  set p := P *ᵥ v with hp
  set y := gdY P Q v with hy
  set y' := gdY' P Q v w with hy'
  have hn : ‖(((nq p : ℝ) : ℂ))⁻¹‖ ^ 2 = (nq p)⁻¹ ^ 2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  refine ⟨?_, ?_, ?_⟩
  · rw [hK0'd, dot_self, hsSq_smul, hn]
    have h1 := hsSq_sub_le (Matrix.vecMulVec y' (star p) + Matrix.vecMulVec y (star w))
      (Matrix.vecMulVec w (star y) + Matrix.vecMulVec p (star y'))
    have h2 := hsSq_add_le (Matrix.vecMulVec y' (star p)) (Matrix.vecMulVec y (star w))
    have h3 := hsSq_add_le (Matrix.vecMulVec w (star y)) (Matrix.vecMulVec p (star y'))
    rw [hsSq_vecMulVec, hsSq_vecMulVec] at h2 h3
    have hH : hsSq (Matrix.vecMulVec y' (star p) + Matrix.vecMulVec y (star w) -
        (Matrix.vecMulVec w (star y) + Matrix.vecMulVec p (star y'))) ≤
        8 * nq p * nq y' + 8 * nq y * nq w := by nlinarith
    calc nq p ^ 2 * ((nq p)⁻¹ ^ 2 * hsSq (Matrix.vecMulVec y' (star p) +
          Matrix.vecMulVec y (star w) - (Matrix.vecMulVec w (star y) +
            Matrix.vecMulVec p (star y'))))
        = hsSq (Matrix.vecMulVec y' (star p) + Matrix.vecMulVec y (star w) -
          (Matrix.vecMulVec w (star y) + Matrix.vecMulVec p (star y'))) := by
          field_simp
      _ ≤ _ := hH
  · rw [hK0d, dot_self, hsSq_smul, hn]
    have h1 := hsSq_sub_le (Matrix.vecMulVec y (star p)) (Matrix.vecMulVec p (star y))
    rw [hsSq_vecMulVec, hsSq_vecMulVec] at h1
    calc nq p * ((nq p)⁻¹ ^ 2 *
          hsSq (Matrix.vecMulVec y (star p) - Matrix.vecMulVec p (star y)))
        = (nq p)⁻¹ * hsSq (Matrix.vecMulVec y (star p) - Matrix.vecMulVec p (star y)) := by
          field_simp
      _ ≤ (nq p)⁻¹ * (4 * nq p * nq y) := by
          refine mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hpos.le)
      _ = 4 * nq y := by field_simp
  · have hyA : y = allowProj P v *ᵥ ((Q * (gdX P Q v)⁻¹ * Q) *ᵥ v) := by
      rw [hy, gdY, Matrix.mulVec_mulVec]
      simp only [Matrix.mul_assoc]
    have hyp : star y ⬝ᵥ p = 0 := by
      rw [hyA, ← dot_herm hAh, hAp, dotProduct_zero]
    have hNc : (star p ⬝ᵥ p)⁻¹ * (star p ⬝ᵥ p) = 1 := by
      rw [dot_self]
      exact inv_mul_cancel₀ (by exact_mod_cast hpos.ne')
    have hK : gdK0 P Q v *ᵥ p = y := by
      rw [hK0d, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec,
        Matrix.vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul, hyp, zero_smul, sub_zero,
        smul_smul, hNc, one_smul]
    have := nq_mulVec_le_hsSq (gdK0 P Q v) p
    rw [hK] at this
    linarith

/-- The quotient rule behind (9.76) [su:eq:normalization-source-response]: for
`ξ = Re(a* (a + c)) / ‖a‖²` with derivative `ξ' = (n' ‖a‖² - n D') / ‖a‖⁴`, where
`n = Re(a* (a + c))`, `n' = Re(b* (a + c) + a* (b + d))` and `D' = Re(b* a + a* b)`,
`ξ'² ‖a‖² ≤ 3 (5 ‖b‖² ‖c‖² + ‖a‖² ‖d‖²)`. -/
private lemma gd_quot (A B c d : Fin W → ℂ) (hD : 0 < nq A) :
    (((star B ⬝ᵥ (A + c) + star A ⬝ᵥ (B + d)).re * nq A -
        (star A ⬝ᵥ (A + c)).re * (star B ⬝ᵥ A + star A ⬝ᵥ B).re) / nq A ^ 2) ^ 2 * nq A ^ 2 ≤
      3 * (5 * nq B * nq c + nq A * nq d) := by
  have hBA := re_dot_comm B A
  have hAA := re_dot_self A
  set D := nq A with hDdef
  set r1 := (star A ⬝ᵥ c).re
  set r2 := (star A ⬝ᵥ B).re
  set r3 := (star B ⬝ᵥ c).re
  set r4 := (star A ⬝ᵥ d).re
  have hnum : (star B ⬝ᵥ (A + c) + star A ⬝ᵥ (B + d)).re * D -
      (star A ⬝ᵥ (A + c)).re * (star B ⬝ᵥ A + star A ⬝ᵥ B).re = (r3 + r4) * D - 2 * r1 * r2 := by
    simp only [dotProduct_add, Complex.add_re]
    rw [hBA, hAA]
    ring
  rw [hnum]
  have e1 := re_dot_sq A c
  have e2 := re_dot_sq A B
  have e3 := re_dot_sq B c
  have e4 := re_dot_sq A d
  rw [← hDdef] at e1 e2 e4
  have hB := nq_nonneg B
  have hc := nq_nonneg c
  have hd := nq_nonneg d
  have key : ((r3 + r4) * D - 2 * r1 * r2) ^ 2 ≤ 3 * D ^ 2 * (5 * nq B * nq c + D * nq d) := by
    have s1 : ((r3 + r4) * D - 2 * r1 * r2) ^ 2 ≤
        3 * ((r3 * D) ^ 2 + (r4 * D) ^ 2 + (2 * r1 * r2) ^ 2) := by
      nlinarith [sq_nonneg (r3 * D - r4 * D), sq_nonneg (r3 * D + 2 * r1 * r2),
        sq_nonneg (r4 * D + 2 * r1 * r2)]
    have s2 : (r3 * D) ^ 2 ≤ nq B * nq c * D ^ 2 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right e3 (by positivity)
    have s3 : (r4 * D) ^ 2 ≤ D * nq d * D ^ 2 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right e4 (by positivity)
    have s4 : (2 * r1 * r2) ^ 2 ≤ 4 * (D * nq c) * (D * nq B) := by
      have := mul_le_mul e1 e2 (sq_nonneg _) (by positivity)
      nlinarith
    nlinarith
  calc (((r3 + r4) * D - 2 * r1 * r2) / D ^ 2) ^ 2 * D ^ 2
      = ((r3 + r4) * D - 2 * r1 * r2) ^ 2 / D ^ 2 := by field_simp
    _ ≤ 3 * D ^ 2 * (5 * nq B * nq c + D * nq d) / D ^ 2 :=
        div_le_div_of_nonneg_right key (by positivity)
    _ = _ := by field_simp

end Bounds

/-! ### The exceptional subspace

For a real-linear functional `ℓ` on `ℂ^W` there is `g` with `ℓ w = Re(g* w)`. The real-linear
map `h z = P z - ‖p‖⁻² Re(p* z) p` takes values in `𝓗_v = {w : P w = w, Re(v* w) = 0}` and
`Re((h z)* w) = Re(z* w)` for `w ∈ 𝓗_v`. With `𝓔 = h(ran Q) + ℝ h(g)`, a vector of `𝓗_v`
orthogonal to `𝓔` has `Q w = 0` and `ℓ w = 0`, and `dim_ℝ 𝓔 ≤ 2 rank Q + 1 = 2 Re tr Q + 1`. -/

section Exc

variable {W : ℕ}

private lemma riesz (ℓ : (Fin W → ℂ) →ₗ[ℝ] ℝ) :
    ∃ g : Fin W → ℂ, ∀ w, ℓ w = (star g ⬝ᵥ w).re := by
  refine ⟨fun j => ((ℓ (Pi.single j (1 : ℂ) : Fin W → ℂ) : ℝ) : ℂ) +
    ((ℓ (Pi.single j Complex.I : Fin W → ℂ) : ℝ) : ℂ) * Complex.I, fun w => ?_⟩
  have hw : w = ∑ j, ((w j).re • (Pi.single j (1 : ℂ) : Fin W → ℂ) +
      (w j).im • (Pi.single j Complex.I : Fin W → ℂ)) := by
    ext k
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
    simp only [smul_ite, smul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
    apply Complex.ext <;> simp
  conv_lhs => rw [hw]
  rw [map_sum]
  simp only [map_add, map_smul, smul_eq_mul, dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re]
  ring

/-- The real-linear map `h z = P z - ‖p‖⁻² Re(p* z) p`, `p = P v`. -/
private def hmap (P : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) :
    (Fin W → ℂ) →ₗ[ℝ] (Fin W → ℂ) where
  toFun z := P *ᵥ z - ((star (P *ᵥ v) ⬝ᵥ z).re / nq (P *ᵥ v)) • (P *ᵥ v)
  map_add' a b := by
    simp only [Matrix.mulVec_add, dotProduct_add, Complex.add_re, add_div, add_smul]
    abel
  map_smul' c a := by
    simp only [Matrix.mulVec_smul, dotProduct_smul, Complex.smul_re, smul_eq_mul, mul_div_assoc,
      RingHom.id_apply, smul_sub, smul_smul]

private lemma hmap_spec {P : Matrix (Fin W) (Fin W) ℂ} (hP : Pᴴ = P) (hPP : P * P = P)
    {v : Fin W → ℂ} (hPv : P *ᵥ v ≠ 0) (z : Fin W → ℂ) :
    (P *ᵥ hmap P v z = hmap P v z ∧ (star v ⬝ᵥ hmap P v z).re = 0) ∧
      ∀ w : Fin W → ℂ, P *ᵥ w = w → (star v ⬝ᵥ w).re = 0 →
        (star (hmap P v z) ⬝ᵥ w).re = (star z ⬝ᵥ w).re := by
  have hpos := nq_pos hPv
  have hPp : P *ᵥ (P *ᵥ v) = P *ᵥ v := by rw [Matrix.mulVec_mulVec, hPP]
  have hvp : star v ⬝ᵥ (P *ᵥ v) = star (P *ᵥ v) ⬝ᵥ (P *ᵥ v) := by
    conv_lhs => rw [← hPp]
    exact dot_herm hP _ _
  have hh : hmap P v z = P *ᵥ z - ((star (P *ᵥ v) ⬝ᵥ z).re / nq (P *ᵥ v)) • (P *ᵥ v) := rfl
  refine ⟨⟨?_, ?_⟩, fun w hPw hw => ?_⟩
  · rw [hh, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hPP, hPp]
  · rw [hh, dotProduct_sub, dotProduct_smul, Complex.sub_re, Complex.smul_re, dot_herm hP, hvp,
      re_dot_self, smul_eq_mul, div_mul_cancel₀ _ hpos.ne', sub_self]
  · have hpw : (star (P *ᵥ v) ⬝ᵥ w).re = 0 := by rw [← dot_herm hP, hPw, hw]
    rw [hh, star_sub, star_smul, sub_dotProduct, smul_dotProduct, Complex.sub_re,
      Complex.smul_re, hpw, smul_eq_mul, mul_zero, sub_zero, ← dot_herm hP, hPw]

/-- `rank Q = Re tr Q` for an idempotent `Q`, as the complex dimension of `ran Q`. -/
private lemma finrank_range_eq_trace {Q : Matrix (Fin W) (Fin W) ℂ} (hQQ : Q * Q = Q) :
    (Module.finrank ℂ (LinearMap.range (Matrix.mulVecLin Q)) : ℝ) = Q.trace.re := by
  have hid : IsIdempotentElem (Matrix.mulVecLin Q) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hQQ]
  have htr := ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr hid).trace
  rw [← Matrix.toLin'_apply', Matrix.trace_toLin'_eq] at htr
  rw [htr, Matrix.toLin'_apply']
  simp

private lemma exc_space {P Q : Matrix (Fin W) (Fin W) ℂ} (hP : Pᴴ = P) (hPP : P * P = P)
    (hQh : Qᴴ = Q) (hQQ : Q * Q = Q) {v : Fin W → ℂ} (hPv : P *ᵥ v ≠ 0)
    (ℓ : (Fin W → ℂ) →ₗ[ℝ] ℝ) :
    ∃ Es : Submodule ℝ (Fin W → ℂ), (∀ w ∈ Es, P *ᵥ w = w ∧ (star v ⬝ᵥ w).re = 0) ∧
      (Module.finrank ℝ Es : ℝ) ≤ 2 * Q.trace.re + 1 ∧
      ∀ w : Fin W → ℂ, P *ᵥ w = w → (star v ⬝ᵥ w).re = 0 →
        (∀ u ∈ Es, (star u ⬝ᵥ w).re = 0) → Q *ᵥ w = 0 ∧ ℓ w = 0 := by
  obtain ⟨g, hg⟩ := riesz ℓ
  set RQ := (LinearMap.range (Matrix.mulVecLin Q)).restrictScalars ℝ with hRQ
  set Es := Submodule.map (hmap P v) RQ ⊔ Submodule.span ℝ {hmap P v g} with hEs
  let H : Submodule ℝ (Fin W → ℂ) :=
    { carrier := {w | P *ᵥ w = w ∧ (star v ⬝ᵥ w).re = 0}
      add_mem' := fun {a b} ha hb => by
        refine ⟨by rw [Matrix.mulVec_add, ha.1, hb.1], ?_⟩
        rw [dotProduct_add, Complex.add_re, ha.2, hb.2, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        refine ⟨by rw [Matrix.mulVec_smul, ha.1], ?_⟩
        rw [dotProduct_smul, Complex.smul_re, ha.2, smul_zero] }
  have hEH : Es ≤ H := by
    refine sup_le ?_ ?_
    · rintro _ ⟨z, -, rfl⟩
      exact (hmap_spec hP hPP hPv z).1
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact (hmap_spec hP hPP hPv g).1
  refine ⟨Es, fun w hw => hEH hw, ?_, fun w hPw hw hperp => ?_⟩
  · have h1 := Submodule.finrank_add_le_finrank_add_finrank (Submodule.map (hmap P v) RQ)
      (Submodule.span ℝ {hmap P v g})
    have h2 := Submodule.finrank_map_le (hmap P v) RQ
    have h3 : Module.finrank ℝ (Submodule.span ℝ ({hmap P v g} : Set (Fin W → ℂ))) ≤ 1 := by
      have := finrank_span_le_card (R := ℝ) ({hmap P v g} : Set (Fin W → ℂ))
      simpa using this
    have h4 : Module.finrank ℝ RQ = 2 * Module.finrank ℂ (LinearMap.range (Matrix.mulVecLin Q)) :=
      finrank_real_of_complex _
    have h5 := finrank_range_eq_trace hQQ
    have h6 : (Module.finrank ℝ Es : ℝ) ≤ Module.finrank ℝ RQ + 1 := by
      exact_mod_cast (h1.trans (Nat.add_le_add h2 h3))
    rw [h4] at h6
    push_cast at h6
    linarith
  · have hQ : Q *ᵥ w = 0 := by
      have hm : hmap P v (Q *ᵥ w) ∈ Es :=
        Submodule.mem_sup_left (Submodule.mem_map_of_mem (by
          rw [hRQ, Submodule.restrictScalars_mem]; exact ⟨w, rfl⟩))
      have h1 := hperp _ hm
      rw [(hmap_spec hP hPP hPv _).2 w hPw hw] at h1
      have h2 : star (Q *ᵥ w) ⬝ᵥ w = star (Q *ᵥ w) ⬝ᵥ (Q *ᵥ w) := by
        rw [dot_herm hQh, Matrix.mulVec_mulVec, hQQ]
      rw [h2, re_dot_self] at h1
      exact eq_zero_of_nq h1
    refine ⟨hQ, ?_⟩
    have hm : hmap P v g ∈ Es := Submodule.mem_sup_right (Submodule.subset_span rfl)
    have h1 := hperp _ hm
    rw [(hmap_spec hP hPP hPv _).2 w hPw hw] at h1
    rw [hg, h1]

end Exc

/-! ### The construction with fixed `P`, `Q`, `M`, `L`

(9.78) [su:eq:construction-derivative-goals]. Here `M` plays `R_{[q-1,5]}` and `L` plays `A_< R̃`,
with `M z = L z` whenever `Q z = 0` ((9.17) [us:eq:error]). -/

section Main

variable {W : ℕ}

private lemma ar_dy {a nu nw ny' nQw : ℝ} (ha : 0 < a) (hnw : 0 ≤ nw)
    (h : a * ny' ≤ 400 / 9 * nu * nw + 32 / 9 * a * nQw) (hu : nu ≤ 4 / 9 * a)
    (hQ : nQw ≤ nw) : ny' ≤ 24 * nw := by
  have h1 : nu * nw ≤ 4 / 9 * a * nw := mul_le_mul_of_nonneg_right hu hnw
  have h2 : a * nQw ≤ a * nw := mul_le_mul_of_nonneg_left hQ ha.le
  have h3 : a * ny' ≤ a * (24 * nw) := by nlinarith
  exact le_of_mul_le_mul_left h3 ha

private lemma ar_k0 {a H ny' ny nw : ℝ} (ha : 0 < a) (hnw : 0 ≤ nw)
    (h : a ^ 2 * H ≤ 8 * a * ny' + 8 * ny * nw) (hy' : ny' ≤ 24 * nw) (hy : ny ≤ 4 / 9 * a) :
    a * H ≤ 196 * nw := by
  have h1 : ny * nw ≤ 4 / 9 * a * nw := mul_le_mul_of_nonneg_right hy hnw
  have h2 : a * ny' ≤ a * (24 * nw) := mul_le_mul_of_nonneg_left hy' ha.le
  have h3 : a * (a * H) ≤ a * (196 * nw) := by nlinarith
  exact le_of_mul_le_mul_left h3 ha

private lemma ar_xi {a X D nb nc nd mM lL nv nw e ρ : ℝ} (ha : 0 < a) (hD : 0 < D)
    (hnc : 0 ≤ nc) (hmM : 0 ≤ mM) (hlL : 0 ≤ lL) (hnw : 0 ≤ nw)
    (he0 : 0 ≤ e) (hρ0 : 0 ≤ ρ) (hq : X * D ^ 2 ≤ 3 * (5 * nb * nc + D * nd))
    (hb : nb ≤ mM * nw) (hc : nc ≤ lL * (4 * nv)) (hd : nd ≤ lL * (50 * nw))
    (hρ : a * mM ≤ ρ * D) (he : lL * nv ≤ e * D) (hav : a ≤ nv) :
    a * X ≤ 150 * e * (1 + ρ) * nw := by
  have hnv : 0 ≤ nv := ha.le.trans hav
  have s1 : a * (X * D ^ 2) ≤ a * (3 * (5 * nb * nc + D * nd)) :=
    mul_le_mul_of_nonneg_left hq ha.le
  have s2 : nb * nc ≤ (mM * nw) * (lL * (4 * nv)) := mul_le_mul hb hc hnc (by positivity)
  have s3 : (a * mM) * (lL * nv) ≤ (ρ * D) * (e * D) :=
    mul_le_mul hρ he (by positivity) (by positivity)
  have s4 : a * lL ≤ nv * lL := mul_le_mul_of_nonneg_right hav hlL
  have s5 : a * nd ≤ a * (lL * (50 * nw)) := mul_le_mul_of_nonneg_left hd ha.le
  have s6 : a * (nb * nc) ≤ 4 * nw * ((ρ * D) * (e * D)) := by
    have := mul_le_mul_of_nonneg_left s2 ha.le
    have h7 : a * ((mM * nw) * (lL * (4 * nv))) = 4 * nw * ((a * mM) * (lL * nv)) := by ring
    have h8 := mul_le_mul_of_nonneg_left s3 (by positivity : (0 : ℝ) ≤ 4 * nw)
    linarith
  have s7 : a * nd ≤ 50 * nw * (e * D) := by
    have h7 : a * (lL * (50 * nw)) = 50 * nw * (a * lL) := by ring
    have h8 : 50 * nw * (a * lL) ≤ 50 * nw * (lL * nv) := by
      have := mul_le_mul_of_nonneg_left s4 (by positivity : (0 : ℝ) ≤ 50 * nw)
      linarith
    have h9 := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 50 * nw)
    linarith
  have s8 : a * X * D ^ 2 ≤ (60 * ρ * e + 150 * e) * nw * D ^ 2 := by
    have h1 : a * (3 * (5 * nb * nc + D * nd)) = 15 * (a * (nb * nc)) + 3 * D * (a * nd) := by
      ring
    have h2 : 3 * D * (a * nd) ≤ 3 * D * (50 * nw * (e * D)) :=
      mul_le_mul_of_nonneg_left s7 (by positivity)
    have h3 : a * X * D ^ 2 = a * (X * D ^ 2) := by ring
    nlinarith
  have s9 : a * X ≤ (60 * ρ * e + 150 * e) * nw := le_of_mul_le_mul_right s8 (by positivity)
  have s10 : 0 ≤ ρ * e * nw := by positivity
  nlinarith

private lemma ar_first {a ξi xp H0 H1 Hk nw e ρ : ℝ} (ha : 0 < a) (hξi0 : 0 ≤ ξi)
    (hξi : ξi ≤ 2) (hH0 : a * H0 ≤ 196 * nw) (hH1 : a * H1 ≤ 16 / 9 * a) (hH00 : 0 ≤ H0)
    (hH10 : 0 ≤ H1) (hxi : a * xp ^ 2 ≤ 150 * e * (1 + ρ) * nw)
    (hHk : Hk ≤ 2 * (ξi ^ 2 * H0) + 2 * ((xp * ξi ^ 2) ^ 2 * H1)) :
    a * Hk ≤ 10000 * (1 + e * (1 + ρ)) * nw := by
  have hnw : 0 ≤ nw := by
    have : 0 ≤ a * H0 := mul_nonneg ha.le hH00
    linarith
  have hE : 0 ≤ e * (1 + ρ) * nw := by
    have : 0 ≤ a * xp ^ 2 := by positivity
    linarith
  have hξ2 : ξi ^ 2 ≤ 4 := by nlinarith
  have hξ4 : (ξi ^ 2) ^ 2 ≤ 16 := by nlinarith
  have t1 : a * (ξi ^ 2 * H0) ≤ 4 * (196 * nw) := by
    have h := mul_le_mul hξ2 hH0 (by positivity) (by norm_num)
    nlinarith
  have t2 : a * ((xp * ξi ^ 2) ^ 2 * H1) ≤ 16 * (16 / 9) * (150 * e * (1 + ρ) * nw) := by
    have h1 : a * ((xp * ξi ^ 2) ^ 2 * H1) = (ξi ^ 2) ^ 2 * xp ^ 2 * (a * H1) := by ring
    have h2 : xp ^ 2 * (a * H1) ≤ xp ^ 2 * (16 / 9 * a) :=
      mul_le_mul_of_nonneg_left hH1 (sq_nonneg _)
    have h3 : (ξi ^ 2) ^ 2 * (xp ^ 2 * (a * H1)) ≤ 16 * (16 / 9 * (a * xp ^ 2)) := by
      have h4 : 0 ≤ xp ^ 2 * (a * H1) := by positivity
      have h5 : xp ^ 2 * (16 / 9 * a) = 16 / 9 * (a * xp ^ 2) := by ring
      have h2' : xp ^ 2 * (a * H1) ≤ 16 / 9 * (a * xp ^ 2) := by linarith
      have := mul_le_mul hξ4 h2' h4 (by norm_num)
      linarith
    nlinarith
  have t3 : a * Hk ≤ a * (2 * (ξi ^ 2 * H0) + 2 * ((xp * ξi ^ 2) ^ 2 * H1)) :=
    mul_le_mul_of_nonneg_left hHk ha.le
  nlinarith

private lemma ar_k0' {a H Hk ny' ny nu nw : ℝ} (ha : 0 < a) (hnw : 0 ≤ nw) (hnu : 0 ≤ nu)
    (h : a ^ 2 * H ≤ 8 * a * ny' + 8 * ny * nw) (hy' : a * ny' ≤ 400 / 9 * nu * nw)
    (huy : 3 / 4 * nu ≤ ny) (hyk : ny ≤ a * Hk) : a * H ≤ 483 * Hk * nw := by
  have h1 : nu * nw ≤ 4 / 3 * ny * nw := by
    have := mul_le_mul_of_nonneg_right huy hnw
    nlinarith
  have h2 : ny * nw ≤ a * Hk * nw := mul_le_mul_of_nonneg_right hyk hnw
  have h3 : a * (a * H) ≤ a * (483 * Hk * nw) := by nlinarith
  exact le_of_mul_le_mul_left h3 ha

private theorem gd_main {P Q M L : Matrix (Fin W) (Fin W) ℂ} {v : Fin W → ℂ} {e ρ : ℝ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hQh : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hPv : P *ᵥ v ≠ 0) (hX : IsUnit (gdX P Q v))
    (hBQ : ∀ u : Fin W → ℂ, Q *ᵥ u = u →
      (3 / 4 : ℝ) * nq u ≤ (star u ⬝ᵥ (allowProj P v *ᵥ u)).re)
    (hQv : 4 * nq (Q *ᵥ v) ≤ nq (P *ᵥ v)) (hML : ∀ z, Q *ᵥ z = 0 → M *ᵥ z = L *ᵥ z)
    (hξ : 1 / 2 ≤ gdXi P Q M v) (he : ‖L‖ ^ 2 * nq v ≤ e * nq (M *ᵥ v))
    (hρ : nq (P *ᵥ v) * ‖M‖ ^ 2 ≤ ρ * nq (M *ᵥ v)) (hρ0 : 0 ≤ ρ) :
    ∃ Es : Submodule ℝ (Fin W → ℂ), (∀ w ∈ Es, P *ᵥ w = w ∧ (star v ⬝ᵥ w).re = 0) ∧
      (Module.finrank ℝ Es : ℝ) ≤ 2 * Q.trace.re + 1 ∧
      (∀ w : Fin W → ℂ, P *ᵥ w = w → (star v ⬝ᵥ w).re = 0 →
        nq (P *ᵥ v) * hsSq (lineDeriv ℝ (gdK P Q M) v w) ≤
          10000 * (1 + e * (1 + ρ)) * nq w) ∧
      ∀ w : Fin W → ℂ, P *ᵥ w = w → (star v ⬝ᵥ w).re = 0 →
        (∀ u ∈ Es, (star u ⬝ᵥ w).re = 0) →
        nq (P *ᵥ v) * hsSq (lineDeriv ℝ (gdK P Q M) v w) ≤
          10000 * hsSq (gdK P Q M v) * nq w := by
  have hD : 0 < nq (M *ᵥ v) := by
    rcases (nq_nonneg (M *ᵥ v)).eq_or_lt with h | h
    · exfalso
      have h0 : gdXi P Q M v = 0 := by
        unfold gdXi
        rw [show (∑ i, ‖(M *ᵥ v) i‖ ^ 2) = nq (M *ᵥ v) from rfl, ← h, div_zero]
      linarith
    · exact h
  have hξ0 : gdXi P Q M v ≠ 0 := by intro h; linarith
  have hpos := nq_pos hPv
  obtain ⟨-, hu, hyu, huy, hQy, hpv⟩ := gd_y hP hPP hQh hQQ hPv hX hBQ hQv
  have hyv : nq (gdY P Q v) ≤ nq v := by linarith [nq_nonneg v]
  have hMy : M *ᵥ gdY P Q v = M *ᵥ v + L *ᵥ (gdY P Q v - v) := by
    rw [← hML (gdY P Q v - v) (by rw [Matrix.mulVec_sub, hQy, sub_self]), ← Matrix.mulVec_add,
      add_sub_cancel]
  have he0 : 0 ≤ e := by
    by_contra h
    have h1 : e * nq (M *ᵥ v) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) hD
    have h2 : 0 ≤ ‖L‖ ^ 2 * nq v := by positivity
    linarith
  obtain ⟨-, hk0b, hk0low⟩ := gd_k0 (Q := Q) (w := 0) hP hPP hPv
  have hξi : (gdXi P Q M v)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hξi0 : 0 < (gdXi P Q M v)⁻¹ := inv_pos.mpr (by linarith)
  have hnr : ∀ r : ℝ, ‖(r : ℂ)‖ ^ 2 = r ^ 2 := fun r => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hK' : ∀ w, gdK' P Q M v w = (((gdXi P Q M v)⁻¹ : ℝ) : ℂ) • gdK0' P Q v w +
      ((-gdXi' P Q M v w / gdXi P Q M v ^ 2 : ℝ) : ℂ) • gdK0 P Q v := fun w => rfl
  have hcoef : ∀ x : ℝ, (-x / gdXi P Q M v ^ 2) ^ 2 = (x * (gdXi P Q M v)⁻¹ ^ 2) ^ 2 :=
    fun x => by field_simp
  -- the exceptional subspace
  have hdiff := gd_diffXi hPv hX hD.ne'
  obtain ⟨Es, hEs1, hEs2, hEs3⟩ :=
    exc_space hP.eq hPP hQh hQQ hPv (fderiv ℝ (gdXi P Q M) v : (Fin W → ℂ) →L[ℝ] ℝ).toLinearMap
  refine ⟨Es, hEs1, hEs2, fun w hPw hre => ?_, fun w hPw hre hperp => ?_⟩
  · obtain ⟨hξd, hKd⟩ := gd_hasDeriv hP.eq hPw hre hPv hX hD.ne' hξ0
    rw [HasLineDerivAt.lineDeriv hKd]
    obtain ⟨hQdy, hdyb⟩ := gd_dy (w := w) hP hPP hQh hQQ hPv hX hBQ
    have hk0' := (gd_k0 (Q := Q) (w := w) hP hPP hPv).1
    have hw0 := nq_nonneg w
    have hdy := ar_dy hpos hw0 hdyb hu (proj_nq hQh hQQ w).2
    have hMdy : M *ᵥ gdY' P Q v w = M *ᵥ w + L *ᵥ (gdY' P Q v w - w) := by
      rw [← hML _ hQdy, ← Matrix.mulVec_add, add_sub_cancel]
    have hq := gd_quot (M *ᵥ v) (M *ᵥ w) (L *ᵥ (gdY P Q v - v)) (L *ᵥ (gdY' P Q v w - w)) hD
    rw [← hMy, ← hMdy] at hq
    have hc : nq (L *ᵥ (gdY P Q v - v)) ≤ ‖L‖ ^ 2 * (4 * nq v) := by
      refine (nq_opNorm L _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have := nq_sub_le (gdY P Q v) v
      linarith
    have hd : nq (L *ᵥ (gdY' P Q v w - w)) ≤ ‖L‖ ^ 2 * (50 * nq w) := by
      refine (nq_opNorm L _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have := nq_sub_le (gdY' P Q v w) w
      linarith
    have hxi := ar_xi hpos hD (nq_nonneg _) (by positivity)
      (by positivity) hw0 he0 hρ0 hq (nq_opNorm M w) hc hd hρ (by linarith) hpv
    have hK0' := ar_k0 hpos hw0 hk0' hdy (hyu.trans hu)
    have hsplit := hsSq_add_le ((((gdXi P Q M v)⁻¹ : ℝ) : ℂ) • gdK0' P Q v w)
      (((-gdXi' P Q M v w / gdXi P Q M v ^ 2 : ℝ) : ℂ) • gdK0 P Q v)
    rw [hsSq_smul, hsSq_smul, hnr, hnr, hcoef] at hsplit
    rw [hK']
    exact ar_first hpos hξi0.le hξi hK0' (by linarith) (hsSq_nonneg _) (hsSq_nonneg _) hxi hsplit
  · obtain ⟨hξd, hKd⟩ := gd_hasDeriv hP.eq hPw hre hPv hX hD.ne' hξ0
    rw [HasLineDerivAt.lineDeriv hKd]
    obtain ⟨hQw, hℓ⟩ := hEs3 w hPw hre hperp
    have hx : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
      simpa using this
    have hf : HasFDerivAt (gdXi P Q M) (fderiv ℝ (gdXi P Q M) v) (v + (0 : ℝ) • w) := by
      rw [zero_smul, add_zero]; exact hdiff.hasFDerivAt
    have h3 := hf.comp_hasDerivAt (0 : ℝ) hx
    have h2 : HasDerivAt (fun s : ℝ => gdXi P Q M (v + s • w)) (fderiv ℝ (gdXi P Q M) v w) 0 :=
      h3
    have h1 := hξd.unique h2
    have hxi0 : gdXi' P Q M v w = 0 := by rw [h1]; exact hℓ
    obtain ⟨-, hdyb⟩ := gd_dy (w := w) hP hPP hQh hQQ hPv hX hBQ
    rw [hQw] at hdyb
    have hk0' := (gd_k0 (Q := Q) (w := w) hP hPP hPv).1
    have hdy0 : nq (P *ᵥ v) * nq (gdY' P Q v w) ≤ 400 / 9 * nq (gdG P Q v *ᵥ v) * nq w := by
      have h0 : nq (0 : Fin W → ℂ) = 0 := by simp [nq]
      rw [h0, mul_zero, add_zero] at hdyb
      exact hdyb
    have hH := ar_k0' hpos (nq_nonneg w) (nq_nonneg _) hk0' hdy0 huy hk0low
    have hK : gdK P Q M v = (((gdXi P Q M v)⁻¹ : ℝ) : ℂ) • gdK0 P Q v := rfl
    rw [hK', hxi0, hK, hsSq_smul, hnr]
    simp only [neg_zero, zero_div, Complex.ofReal_zero, zero_smul, add_zero]
    rw [hsSq_smul, hnr]
    have h2 := mul_le_mul_of_nonneg_left hH (sq_nonneg (gdXi P Q M v)⁻¹)
    have h3 : 0 ≤ (gdXi P Q M v)⁻¹ ^ 2 * hsSq (gdK0 P Q v) * nq w := by
      have := hsSq_nonneg (gdK0 P Q v)
      have := nq_nonneg w
      positivity
    nlinarith

end Main

/-! ### The cavity identity on `ker Q`

`R̃` is Hermitian, `Q R̃ 1_{(t², ∞)}(A* A) = R̃ 1_{(t², ∞)}(A* A)` and `R_{[q-1,5]} = A R̃`
((3.4) [us:eq:cavity]); hence `R_{[q-1,5]} z = A_< R̃ z` whenever `Q z = 0`, as in (9.17)
[us:eq:error]. -/

section Cavity

variable {W q : ℕ}

private lemma blockSeq_herm (ω : Ω W q) (k : ℕ) : (blockSeq W q ω k).IsHermitian := by
  unfold blockSeq
  split_ifs
  · exact gueBlock_isHermitian W q ω _
  · exact Matrix.isHermitian_zero

private lemma rsmul_herm (r : ℝ) {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) :
    ((r : ℂ) • A).IsHermitian := by
  unfold Matrix.IsHermitian at hA ⊢
  rw [Matrix.conjTranspose_smul, hA]
  simp

private lemma gsq_herm (g : ℝ) {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) :
    (((g : ℂ) ^ 2) • A).IsHermitian := by
  have := rsmul_herm (g ^ 2) hA
  simpa using this

private lemma cavR_herm (g E : ℝ) (ω : Ω W q) : ∀ m, (cavR W g E q ω m).IsHermitian
  | 0 => by
    simp only [cavR]
    exact ((blockSeq_herm ω _).sub (rsmul_herm E Matrix.isHermitian_one)).inv
  | m + 1 => by
    simp only [cavR]
    exact (((blockSeq_herm ω _).sub (rsmul_herm E Matrix.isHermitian_one)).sub
      (gsq_herm g (cavR_herm g E ω m))).inv

private lemma cavRes_herm (g E : ℝ) {R : Matrix (Fin W) (Fin W) ℂ} (hRh : R.IsHermitian)
    (ω : Ω W q) : (cavRes W g E q R ω).IsHermitian := by
  unfold cavRes
  exact ((((blockSeq_herm ω _).sub (rsmul_herm E Matrix.isHermitian_one)).sub
    (gsq_herm g hRh)).sub (gsq_herm g (cavR_herm g E ω _))).inv

private lemma cav_ker {g E t : ℝ} {R : Matrix (Fin W) (Fin W) ℂ} {ω : Ω W q} (hq : 7 ≤ q)
    (hRh : R.IsHermitian) (hR : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j))
    (hC : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m)) (hT : IsUnit (cavRes W g E q R ω))
    (z : Fin W → ℂ) (hz : retProj W g E q R t ω *ᵥ z = 0) :
    chartProd W g E q R ω (q - 1) *ᵥ z =
      (cavProd W g E q ω (q - 6) *
        specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (t ^ 2)) *
        cavRes W g E q R ω) *ᵥ z := by
  have hRt := cavRes_herm g E hRh ω
  have hAh : ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self _
  obtain ⟨hSh, hSS, -, -⟩ := specProj_spec hAh (Set.Ioi (t ^ 2))
  obtain ⟨hQh, -, hQR⟩ := flagProj_spec hT hSh hSS
  have hsum := (specProj_add_compl hAh (Set.Ioi (t ^ 2))).1
  rw [Set.compl_Ioi] at hsum
  have hQR' : retProj W g E q R t ω * (cavRes W g E q R ω *
      specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Ioi (t ^ 2))) =
      cavRes W g E q R ω *
        specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Ioi (t ^ 2)) :=
    hQR
  have hQh' : (retProj W g E q R t ω)ᴴ = retProj W g E q R t ω := hQh
  have hSRQ : specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6))
      (Set.Ioi (t ^ 2)) * cavRes W g E q R ω * retProj W g E q R t ω =
      specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Ioi (t ^ 2)) *
        cavRes W g E q R ω := by
    have := congrArg Matrix.conjTranspose hQR'
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh.eq, hRt.eq, hQh'] at this
    exact this
  rw [chartProd_eq_cavProd_mul hq R ω hR hC hT]
  set A := cavProd W g E q ω (q - 6)
  set S := specProj (Aᴴ * A) (Set.Ioi (t ^ 2))
  set S' := specProj (Aᴴ * A) (Set.Iic (t ^ 2))
  set Rt := cavRes W g E q R ω
  have hAS : A * Rt = A * S * Rt + A * S' * Rt := by
    rw [← Matrix.add_mul, ← Matrix.mul_add, hsum, Matrix.mul_one]
  have hzero : (A * S * Rt) *ᵥ z = 0 := by
    have : A * S * Rt = A * (S * Rt * retProj W g E q R t ω) := by
      rw [hSRQ, Matrix.mul_assoc]
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz]
    simp
  rw [hAS, Matrix.add_mulVec, hzero, zero_add]

end Cavity

/-- (9.78) [su:eq:construction-derivative-goals]: on the open set where the construction is
smooth, if `B_Q ≥ 3/4` on `ran Q`, `4 ‖Q v‖² ≤ ‖P v‖²`, `‖A_< R̃‖² ‖v‖² ≤ e ‖v_{q-1}‖²` with
`e ≤ 1/16` and `‖P v‖² ‖R_{[q-1,5]}‖² ≤ ρ ‖v_{q-1}‖²`, then there is a real subspace `𝓔 ⊆ 𝓗_v` of
dimension at most `2 rank Q + 1` with `‖P v‖² ‖∇_w K‖²_HS ≤ C₁ (1 + e (1 + ρ)) ‖w‖²` for
`w ∈ 𝓗_v` and `‖P v‖² ‖∇_w K‖²_HS ≤ C₁ ‖K‖²_HS ‖w‖²` for `w ∈ 𝓗_v ∩ 𝓔^⊥`. -/
theorem smallGen_srcDeriv : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ {W q : ℕ} {g E t e ρ : ℝ}
    {R P : Matrix (Fin W) (Fin W) ℂ} {ω : Ω W q} {v : Fin W → ℂ}, 7 ≤ q → R.IsHermitian →
    P.IsHermitian → P * P = P → (ω, v) ∈ genGood W g E q R t P →
    (∀ u : Fin W → ℂ, retProj W g E q R t ω *ᵥ u = u →
      (3 / 4 : ℝ) * ∑ i, ‖u i‖ ^ 2 ≤ (star u ⬝ᵥ (allowProj P v *ᵥ u)).re) →
    4 * ∑ i, ‖(retProj W g E q R t ω *ᵥ v) i‖ ^ 2 ≤ ∑ i, ‖(P *ᵥ v) i‖ ^ 2 →
    ‖cavProd W g E q ω (q - 6) *
        specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (t ^ 2)) *
        cavRes W g E q R ω‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 ≤
      e * ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 → e ≤ 1 / 16 →
    (∑ i, ‖(P *ᵥ v) i‖ ^ 2) * ‖chartProd W g E q R ω (q - 1)‖ ^ 2 ≤
      ρ * ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 → 0 ≤ ρ →
    ∃ Es : Submodule ℝ (Fin W → ℂ), (∀ w ∈ Es, P *ᵥ w = w ∧ (star v ⬝ᵥ w).re = 0) ∧
      (Module.finrank ℝ Es : ℝ) ≤ 2 * (retProj W g E q R t ω).trace.re + 1 ∧
      (∀ w : Fin W → ℂ, P *ᵥ w = w → (star v ⬝ᵥ w).re = 0 →
        (∑ i, ‖(P *ᵥ v) i‖ ^ 2) *
            hsSq (lineDeriv ℝ (fun x => smallGen W g E q R t P ω x) v w) ≤
          C₁ * (1 + e * (1 + ρ)) * ∑ i, ‖w i‖ ^ 2) ∧
      ∀ w : Fin W → ℂ, P *ᵥ w = w → (star v ⬝ᵥ w).re = 0 →
        (∀ u ∈ Es, (star u ⬝ᵥ w).re = 0) →
        (∑ i, ‖(P *ᵥ v) i‖ ^ 2) *
            hsSq (lineDeriv ℝ (fun x => smallGen W g E q R t P ω x) v w) ≤
          C₁ * hsSq (smallGen W g E q R t P ω v) * ∑ i, ‖w i‖ ^ 2 := by
  refine ⟨10000, by norm_num, ?_⟩
  intro W q g E t e ρ R P ω v hq hRh hP hPP hgood hBQ hQv hA he16 hρ hρ0
  obtain ⟨h1, h2, h3, -, h5, h6, -⟩ := hgood
  have hAh : ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self _
  obtain ⟨hSh, hSS, -, -⟩ := specProj_spec hAh (Set.Ioi (t ^ 2))
  obtain ⟨hQh, hQQ, -⟩ := flagProj_spec h3 hSh hSS
  have hQh' : (retProj W g E q R t ω)ᴴ = retProj W g E q R t ω := hQh
  have hQQ' : retProj W g E q R t ω * retProj W g E q R t ω = retProj W g E q R t ω := hQQ
  have hX : IsUnit (gdX P (retProj W g E q R t ω) v) := h6
  obtain ⟨-, hu, hyu, -, -, hpv⟩ := gd_y hP hPP hQh' hQQ' h5 hX hBQ hQv
  have hy : ∑ i, ‖srcVec W g E q R t P ω v i‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by
    have h : nq (gdY P (retProj W g E q R t ω) v) ≤ nq v := by linarith [nq_nonneg v]
    exact h
  have hBQ2 : ∀ u : Fin W → ℂ, retProj W g E q R t ω *ᵥ u = u →
      (1 / 2 : ℝ) * ∑ i, ‖u i‖ ^ 2 ≤ (star u ⬝ᵥ (allowProj P v *ᵥ u)).re := fun u hu => by
    have h := hBQ u hu
    have h0 : 0 ≤ ∑ i, ‖u i‖ ^ 2 := by positivity
    linarith
  have hA16 : ‖cavProd W g E q ω (q - 6) *
        specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (t ^ 2)) *
        cavRes W g E q R ω‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 ≤
      (1 / 16 : ℝ) * ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 := by
    have h0 : 0 ≤ ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_right he16 h0
    linarith
  have hb := smallGen_bounds hq hRh t hP hPP ω h1 h2 h3 h5 hBQ2 hy hA16
  have hξ : 1 / 2 ≤ gdXi P (retProj W g E q R t ω) (chartProd W g E q R ω (q - 1)) v :=
    hb.2.2.1
  exact gd_main hP hPP hQh' hQQ' h5 hX hBQ hQv (cav_ker hq hRh h1 h2 h3) hξ hA hρ hρ0

end LSBA
