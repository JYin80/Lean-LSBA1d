import Mathlib

/-!
# Least-squares left inverses

For a real matrix `A` with `‖A x‖ ≥ τ ‖x‖` for every `x` (`τ > 0`, Euclidean norms), the left
inverse `𝒥 = (AᵀA)⁻¹ Aᵀ` (as `𝒥 = (𝓛*𝓛)⁻¹ 𝓛*` in Section 10 [sec:compact-proof]):
`𝒥 A = I`, `‖𝒥‖ ≤ τ⁻¹` and `‖(AᵀA)⁻¹‖ ≤ τ⁻²`; the derivative of `𝒥ᵀ = A (AᵀA)⁻¹` along a
differentiable family, (10.22) [eq:c-lift-derivative]; and the resulting bound (10.23)
[eq:c-J-bound] over a finite family of directions.
-/

open Real Finset
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace LSBA

/-- The least-squares left inverse `(AᵀA)⁻¹ Aᵀ`. -/
def lsqInv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) :
    Matrix n m ℝ :=
  (Aᵀ * A)⁻¹ * Aᵀ

section LeastSquaresAux

private lemma LeastSquares_sum_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ∑ i, v i ^ 2 = v ⬝ᵥ v := by
  simp [dotProduct, sq]

private lemma LeastSquares_dot_self_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

private lemma LeastSquares_cs {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
  simpa [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v

private lemma LeastSquares_le_of_sq_le {s b : ℝ} (hs : 0 ≤ s) (hb : 0 ≤ b)
    (h : s ^ 2 ≤ s * b) : s ≤ b := by
  rcases hs.eq_or_lt with h0 | h0
  · rw [← h0]; exact hb
  · nlinarith

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private lemma LeastSquares_dot_gram (A : Matrix m n ℝ) (x : n → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ ((Aᵀ * A) *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]

omit [DecidableEq n] in
private lemma LeastSquares_hA_dot {A : Matrix m n ℝ} {τ : ℝ}
    (hA : ∀ x : n → ℝ, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A *ᵥ x) j ^ 2) (x : n → ℝ) :
    τ ^ 2 * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((Aᵀ * A) *ᵥ x) := by
  have := hA x
  rwa [LeastSquares_sum_sq, LeastSquares_sum_sq, LeastSquares_dot_gram] at this

private lemma LeastSquares_isUnit_det {A : Matrix m n ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hA : ∀ x : n → ℝ, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A *ᵥ x) j ^ 2) : IsUnit (Aᵀ * A).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h0 : (Aᵀ * A) *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  have h1 := LeastSquares_hA_dot hA (x - y)
  rw [h0, dotProduct_zero] at h1
  have h2 : (x - y) ⬝ᵥ (x - y) ≤ 0 := by
    by_contra h
    have : 0 < τ ^ 2 * ((x - y) ⬝ᵥ (x - y)) := mul_pos (by positivity) (not_le.1 h)
    linarith
  have h3 : (x - y) ⬝ᵥ (x - y) = 0 := le_antisymm h2 (LeastSquares_dot_self_nonneg _)
  exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 h3)

private lemma LeastSquares_gram_mulVec_inv {A : Matrix m n ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hA : ∀ x : n → ℝ, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A *ᵥ x) j ^ 2) (x : n → ℝ) :
    (Aᵀ * A) *ᵥ ((Aᵀ * A)⁻¹ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (LeastSquares_isUnit_det hτ hA),
    Matrix.one_mulVec]

private lemma LeastSquares_inv_dot_le {A : Matrix m n ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hA : ∀ x : n → ℝ, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A *ᵥ x) j ^ 2) (x : n → ℝ) :
    ((Aᵀ * A)⁻¹ *ᵥ x) ⬝ᵥ ((Aᵀ * A)⁻¹ *ᵥ x) ≤ (τ ^ 4)⁻¹ * (x ⬝ᵥ x) := by
  set z := (Aᵀ * A)⁻¹ *ᵥ x with hz
  have hGz : (Aᵀ * A) *ᵥ z = x := LeastSquares_gram_mulVec_inv hτ hA x
  have h1 := LeastSquares_hA_dot hA z
  rw [hGz] at h1
  have hz0 : 0 ≤ z ⬝ᵥ z := LeastSquares_dot_self_nonneg z
  have h2 := LeastSquares_cs z x
  have h3 : (τ ^ 2 * (z ⬝ᵥ z)) ^ 2 ≤ (z ⬝ᵥ x) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have hx0 : 0 ≤ x ⬝ᵥ x := LeastSquares_dot_self_nonneg x
  rw [le_inv_mul_iff₀ (by positivity)]
  rcases hz0.eq_or_lt with h0 | h0
  · rw [← h0]; simpa using hx0
  · have : τ ^ 4 * (z ⬝ᵥ z) * (z ⬝ᵥ z) ≤ (x ⬝ᵥ x) * (z ⬝ᵥ z) := by nlinarith
    exact le_of_mul_le_mul_right this h0

private lemma LeastSquares_lsqInv_mulVec (A : Matrix m n ℝ) (y : m → ℝ) :
    lsqInv A *ᵥ y = (Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ y) := by
  rw [lsqInv, ← Matrix.mulVec_mulVec]

private lemma LeastSquares_AJ {A : Matrix m n ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hA : ∀ x : n → ℝ, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A *ᵥ x) j ^ 2) (w : m → ℝ) :
    (A *ᵥ (lsqInv A *ᵥ w)) ⬝ᵥ (A *ᵥ (lsqInv A *ᵥ w)) = (A *ᵥ (lsqInv A *ᵥ w)) ⬝ᵥ w ∧
      (A *ᵥ (lsqInv A *ᵥ w)) ⬝ᵥ (A *ᵥ (lsqInv A *ᵥ w)) ≤ w ⬝ᵥ w := by
  set z := lsqInv A *ᵥ w with hz
  have hGz : (Aᵀ * A) *ᵥ z = Aᵀ *ᵥ w := by
    rw [hz, LeastSquares_lsqInv_mulVec, LeastSquares_gram_mulVec_inv hτ hA]
  have h1 : (A *ᵥ z) ⬝ᵥ (A *ᵥ z) = (A *ᵥ z) ⬝ᵥ w := by
    rw [LeastSquares_dot_gram, hGz, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  refine ⟨h1, ?_⟩
  have hs : 0 ≤ (A *ᵥ z) ⬝ᵥ (A *ᵥ z) := LeastSquares_dot_self_nonneg _
  have hw : 0 ≤ w ⬝ᵥ w := LeastSquares_dot_self_nonneg w
  have h2 := LeastSquares_cs (A *ᵥ z) w
  rw [← h1] at h2
  exact LeastSquares_le_of_sq_le hs hw h2

private lemma LeastSquares_transpose_lsqInv (A : Matrix m n ℝ) :
    (lsqInv A)ᵀ = A * (Aᵀ * A)⁻¹ := by
  rw [lsqInv, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_mul,
    Matrix.transpose_transpose]

private lemma LeastSquares_P_dot_le [DecidableEq m] {A : Matrix m n ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hA : ∀ x : n → ℝ, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A *ᵥ x) j ^ 2) (w : m → ℝ) :
    ((1 - A * lsqInv A) *ᵥ w) ⬝ᵥ ((1 - A * lsqInv A) *ᵥ w) ≤ w ⬝ᵥ w := by
  have h := LeastSquares_AJ hτ hA w
  have e : (1 - A * lsqInv A) *ᵥ w = w - A *ᵥ (lsqInv A *ᵥ w) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  have hc := dotProduct_comm w (A *ᵥ (lsqInv A *ᵥ w))
  have hs := LeastSquares_dot_self_nonneg (A *ᵥ (lsqInv A *ᵥ w))
  rw [e]
  simp only [sub_dotProduct, dotProduct_sub]
  linarith [h.1, h.2]

private lemma LeastSquares_Jt_dot_le {A : Matrix m n ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hA : ∀ x : n → ℝ, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A *ᵥ x) j ^ 2) (w : n → ℝ) :
    ((lsqInv A)ᵀ *ᵥ w) ⬝ᵥ ((lsqInv A)ᵀ *ᵥ w) ≤ (τ ^ 2)⁻¹ * (w ⬝ᵥ w) := by
  rw [LeastSquares_transpose_lsqInv, ← Matrix.mulVec_mulVec]
  have hGz := LeastSquares_gram_mulVec_inv hτ hA w
  have hz := LeastSquares_inv_dot_le hτ hA w
  set z := (Aᵀ * A)⁻¹ *ᵥ w with hzdef
  have h1 : (A *ᵥ z) ⬝ᵥ (A *ᵥ z) = z ⬝ᵥ w := by rw [LeastSquares_dot_gram, hGz]
  have hs : 0 ≤ (A *ᵥ z) ⬝ᵥ (A *ᵥ z) := LeastSquares_dot_self_nonneg _
  have hw : 0 ≤ w ⬝ᵥ w := LeastSquares_dot_self_nonneg w
  have h2 := LeastSquares_cs z w
  have h3 : (z ⬝ᵥ z) * (w ⬝ᵥ w) ≤ (τ ^ 4)⁻¹ * (w ⬝ᵥ w) * (w ⬝ᵥ w) :=
    mul_le_mul_of_nonneg_right hz hw
  have h4 : (z ⬝ᵥ w) ^ 2 ≤ ((τ ^ 2)⁻¹ * (w ⬝ᵥ w)) ^ 2 := by
    have : (τ ^ 4)⁻¹ * (w ⬝ᵥ w) * (w ⬝ᵥ w) = ((τ ^ 2)⁻¹ * (w ⬝ᵥ w)) ^ 2 := by
      ring
    linarith
  rw [h1]
  exact (sq_le_sq₀ (h1 ▸ hs) (by positivity)).1 h4

omit [DecidableEq n] in
private lemma LeastSquares_K_nonneg {ι : Type*} [Fintype ι] {A : Matrix m n ℝ} {τ : ℝ}
    (hτ : 0 < τ) (hA : ∀ x : n → ℝ, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A *ᵥ x) j ^ 2)
    {A' : ι → Matrix m n ℝ} {K : ℝ}
    (hK : ∀ x : n → ℝ, ∑ α, ∑ j, (A' α *ᵥ x) j ^ 2 ≤ K * ∑ i, x i ^ 2) {y : n → ℝ}
    (hy : y ≠ 0) : 0 ≤ K := by
  classical
  have hGx := LeastSquares_gram_mulVec_inv hτ hA y
  set x := (Aᵀ * A)⁻¹ *ᵥ y with hxdef
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, Matrix.mulVec_zero] at hGx
    exact hy hGx.symm
  have hpos : 0 < ∑ i, x i ^ 2 := by
    rw [LeastSquares_sum_sq]
    exact lt_of_le_of_ne (LeastSquares_dot_self_nonneg x)
      (Ne.symm (mt dotProduct_self_eq_zero.1 hx0))
  by_contra hneg
  have hKneg : K < 0 := not_le.1 hneg
  have h1 := hK x
  have h2 : 0 ≤ ∑ α, ∑ j, (A' α *ᵥ x) j ^ 2 :=
    Finset.sum_nonneg fun α _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  nlinarith

private lemma LeastSquares_hasDerivAt_mul {l p q : Type*} [Finite l] [Fintype p] [Finite q]
    {u : ℝ → Matrix l p ℝ} {v : ℝ → Matrix p q ℝ} {u' : Matrix l p ℝ} {v' : Matrix p q ℝ}
    {t : ℝ} (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => u s * v s) (u t * v' + u' * v t) t := by
  classical
  have := Fintype.ofFinite l
  have := Fintype.ofFinite q
  let B : Matrix l p ℝ →L[ℝ] Matrix p q ℝ →L[ℝ] Matrix l q ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap (E := Matrix p q ℝ) (F' := Matrix l q ℝ)).toLinearMap
        ∘ₗ mulLinearMap ℝ)
  exact ContinuousLinearMap.hasDerivAt_of_bilinear (B := B) (fun _ => hu) (fun _ => hv)

private lemma LeastSquares_hasDerivAt_transpose {l p : Type*} [Finite l] [Finite p]
    {u : ℝ → Matrix l p ℝ} {u' : Matrix l p ℝ} {t : ℝ} (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => (u s)ᵀ) u'ᵀ t := by
  classical
  have := Fintype.ofFinite l
  have := Fintype.ofFinite p
  let T : Matrix l p ℝ →L[ℝ] Matrix p l ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv l p ℝ ℝ).toLinearMap
  exact HasFDerivAt.comp_hasDerivAt (f := u) (l := T) t T.hasFDerivAt hu

private lemma LeastSquares_hasDerivAt_inv {G : ℝ → Matrix n n ℝ} {G' : Matrix n n ℝ} {t : ℝ}
    (hG : HasDerivAt G G' t) (hu : IsUnit (G t)) :
    HasDerivAt (fun s => (G s)⁻¹) (-((G t)⁻¹ * G' * (G t)⁻¹)) t := by
  obtain ⟨u, hu⟩ := hu
  have h1 : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℝ) ↑u⁻¹ ↑u⁻¹) (G t) :=
    hu ▸ hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have h2 := h1.comp_hasDerivAt t hG
  have e1 : ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) = (G t)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  simp only [e1, neg_apply, ContinuousLinearMap.mulLeftRight_apply] at h2
  simpa only [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using h2

end LeastSquaresAux

/-- For `‖A x‖ ≥ τ ‖x‖`: `𝒥 A = I`, `‖𝒥 y‖ ≤ τ⁻¹ ‖y‖` and `‖(AᵀA)⁻¹ x‖ ≤ τ⁻² ‖x‖`
(Section 10 [sec:compact-proof]). -/
theorem lsqInv_spec {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℝ}
    {τ : ℝ} (hτ : 0 < τ) (hA : ∀ x : n → ℝ, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A *ᵥ x) j ^ 2) :
    lsqInv A * A = 1 ∧
      (∀ y : m → ℝ, ∑ i, (lsqInv A *ᵥ y) i ^ 2 ≤ (τ ^ 2)⁻¹ * ∑ j, y j ^ 2) ∧
      ∀ x : n → ℝ, ∑ i, ((Aᵀ * A)⁻¹ *ᵥ x) i ^ 2 ≤ (τ ^ 4)⁻¹ * ∑ i, x i ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lsqInv, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (LeastSquares_isUnit_det hτ hA)]
  · intro y
    rw [LeastSquares_sum_sq, LeastSquares_sum_sq]
    have h1 := hA (lsqInv A *ᵥ y)
    rw [LeastSquares_sum_sq, LeastSquares_sum_sq] at h1
    have h2 := (LeastSquares_AJ hτ hA y).2
    rw [le_inv_mul_iff₀ (by positivity)]
    exact h1.trans h2
  · intro x
    rw [LeastSquares_sum_sq, LeastSquares_sum_sq]
    exact LeastSquares_inv_dot_le hτ hA x

/-- (10.22) [eq:c-lift-derivative]: along a differentiable family `A(s)` with `‖A(t) x‖ ≥ τ ‖x‖`,
`d𝒥ᵀ = (I - A 𝒥) A' (AᵀA)⁻¹ - 𝒥ᵀ A'ᵀ 𝒥ᵀ` at `t`. -/
theorem hasDerivAt_lsqInv_transpose {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {A : ℝ → Matrix m n ℝ} {A' : Matrix m n ℝ} {t τ : ℝ} (hτ : 0 < τ)
    (hA : HasDerivAt A A' t)
    (hc : ∀ x : n → ℝ, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A t *ᵥ x) j ^ 2) :
    HasDerivAt (fun s => (lsqInv (A s))ᵀ)
      ((1 - A t * lsqInv (A t)) * A' * ((A t)ᵀ * A t)⁻¹ -
        (lsqInv (A t))ᵀ * A'ᵀ * (lsqInv (A t))ᵀ) t := by
  have hT := LeastSquares_hasDerivAt_transpose hA
  have hG := LeastSquares_hasDerivAt_mul hT hA
  have hI := LeastSquares_hasDerivAt_inv hG
    (Matrix.isUnit_iff_isUnit_det _ |>.2 (LeastSquares_isUnit_det hτ hc))
  have hP := LeastSquares_hasDerivAt_mul hA hI
  have hfun : (fun s => (lsqInv (A s))ᵀ) = fun s => A s * ((A s)ᵀ * A s)⁻¹ :=
    funext fun s => LeastSquares_transpose_lsqInv _
  rw [hfun]
  convert hP using 1
  simp only [LeastSquares_transpose_lsqInv]
  simp only [lsqInv, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_neg, Matrix.mul_assoc]
  abel

/-- (10.23) [eq:c-J-bound]: if the directional derivatives `A'_α` satisfy
`Σ_α ‖A'_α x‖² ≤ K ‖x‖²` and `Σ_α ‖A'_αᵀ y‖² ≤ K ‖y‖²`, then the derivatives of `𝒥ᵀ` in
(10.22) [eq:c-lift-derivative] satisfy `Σ_α ‖(D_α 𝒥ᵀ) y‖² ≤ 4 K τ⁻⁴ ‖y‖²`. -/
theorem sum_sq_lsqInv_deriv_le {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι]
    [DecidableEq m] [DecidableEq n] {A : Matrix m n ℝ} {A' : ι → Matrix m n ℝ} {τ K : ℝ}
    (hτ : 0 < τ) (hA : ∀ x : n → ℝ, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A *ᵥ x) j ^ 2)
    (hK : ∀ x : n → ℝ, ∑ α, ∑ j, (A' α *ᵥ x) j ^ 2 ≤ K * ∑ i, x i ^ 2)
    (hK' : ∀ y : m → ℝ, ∑ α, ∑ i, ((A' α)ᵀ *ᵥ y) i ^ 2 ≤ K * ∑ j, y j ^ 2) (y : n → ℝ) :
    ∑ α, ∑ j, (((1 - A * lsqInv A) * A' α * (Aᵀ * A)⁻¹ -
        (lsqInv A)ᵀ * (A' α)ᵀ * (lsqInv A)ᵀ) *ᵥ y) j ^ 2 ≤ 4 * K * (τ ^ 4)⁻¹ * ∑ i, y i ^ 2 := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hK0 : 0 ≤ K := LeastSquares_K_nonneg hτ hA hK hy
  have hxx := (lsqInv_spec hτ hA).2.2 y
  have hcc := LeastSquares_Jt_dot_le hτ hA y
  rw [← LeastSquares_sum_sq, ← LeastSquares_sum_sq] at hcc
  set x := (Aᵀ * A)⁻¹ *ᵥ y with hxdef
  set c := (lsqInv A)ᵀ *ᵥ y with hcdef
  have key : ∀ α, ∑ j, (((1 - A * lsqInv A) * A' α * (Aᵀ * A)⁻¹ -
        (lsqInv A)ᵀ * (A' α)ᵀ * (lsqInv A)ᵀ) *ᵥ y) j ^ 2 ≤
      2 * ∑ j, (A' α *ᵥ x) j ^ 2 + 2 * ((τ ^ 2)⁻¹ * ∑ i, ((A' α)ᵀ *ᵥ c) i ^ 2) := by
    intro α
    have e : ((1 - A * lsqInv A) * A' α * (Aᵀ * A)⁻¹ -
        (lsqInv A)ᵀ * (A' α)ᵀ * (lsqInv A)ᵀ) *ᵥ y =
        (1 - A * lsqInv A) *ᵥ (A' α *ᵥ x) - (lsqInv A)ᵀ *ᵥ ((A' α)ᵀ *ᵥ c) := by
      rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec]
    rw [e]
    set a := (1 - A * lsqInv A) *ᵥ (A' α *ᵥ x) with hadef
    set b := (lsqInv A)ᵀ *ᵥ ((A' α)ᵀ *ᵥ c) with hbdef
    have h1 : ∑ j, (a - b) j ^ 2 ≤ 2 * ∑ j, a j ^ 2 + 2 * ∑ j, b j ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => by
        simp only [Pi.sub_apply]
        nlinarith [sq_nonneg (a j + b j)]
    have ha : ∑ j, a j ^ 2 ≤ ∑ j, (A' α *ᵥ x) j ^ 2 := by
      rw [LeastSquares_sum_sq, LeastSquares_sum_sq]
      exact LeastSquares_P_dot_le hτ hA _
    have hb : ∑ j, b j ^ 2 ≤ (τ ^ 2)⁻¹ * ∑ i, ((A' α)ᵀ *ᵥ c) i ^ 2 := by
      rw [LeastSquares_sum_sq, LeastSquares_sum_sq]
      exact LeastSquares_Jt_dot_le hτ hA _
    linarith
  have hX : K * ∑ i, x i ^ 2 ≤ K * ((τ ^ 4)⁻¹ * ∑ i, y i ^ 2) :=
    mul_le_mul_of_nonneg_left hxx hK0
  have hC : (τ ^ 2)⁻¹ * (K * ∑ j, c j ^ 2) ≤ (τ ^ 2)⁻¹ * (K * ((τ ^ 2)⁻¹ * ∑ i, y i ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcc hK0) (by positivity)
  have hsum : ∑ α, (2 * ∑ j, (A' α *ᵥ x) j ^ 2 + 2 * ((τ ^ 2)⁻¹ * ∑ i, ((A' α)ᵀ *ᵥ c) i ^ 2)) =
      2 * ∑ α, ∑ j, (A' α *ᵥ x) j ^ 2 + 2 * ((τ ^ 2)⁻¹ * ∑ α, ∑ i, ((A' α)ᵀ *ᵥ c) i ^ 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have e2 : (τ ^ 2)⁻¹ * (K * ((τ ^ 2)⁻¹ * ∑ i, y i ^ 2)) = K * (τ ^ 4)⁻¹ * ∑ i, y i ^ 2 := by
    rw [← inv_pow, ← inv_pow]; ring
  have e3 : K * ((τ ^ 4)⁻¹ * ∑ i, y i ^ 2) = K * (τ ^ 4)⁻¹ * ∑ i, y i ^ 2 := by ring
  have hx := hK x
  have hc' := hK' c
  have hc'' : (τ ^ 2)⁻¹ * ∑ α, ∑ i, ((A' α)ᵀ *ᵥ c) i ^ 2 ≤ (τ ^ 2)⁻¹ * (K * ∑ j, c j ^ 2) :=
    mul_le_mul_of_nonneg_left hc' (by positivity)
  calc _ ≤ ∑ α, (2 * ∑ j, (A' α *ᵥ x) j ^ 2 + 2 * ((τ ^ 2)⁻¹ * ∑ i, ((A' α)ᵀ *ᵥ c) i ^ 2)) :=
        Finset.sum_le_sum fun α _ => key α
    _ ≤ _ := by rw [hsum]; linarith

end LSBA
