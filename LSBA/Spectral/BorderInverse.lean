import Mathlib

/-!
# Euclidean norm and bordered matrices

The Euclidean norm `‖v‖₂` of a complex vector; the bordered matrix `[[d, u*], [u, M]]` and the
first column of its inverse through the Schur complement `d - u* M⁻¹ u`; a unitary sending a unit
vector to a coordinate vector. These are the deterministic steps of [APSSS, (2.8)–(2.9)].
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Euclidean norm `‖v‖₂ = (∑ᵢ |vᵢ|²)^{1/2}` of a complex vector. -/
def l2Norm {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := Real.sqrt (∑ i, ‖v i‖ ^ 2)

/-- `‖v‖₂` is the norm of `v` in `EuclideanSpace ℂ ι`. -/
theorem l2Norm_eq_norm_toLp {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    l2Norm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  rfl

/-- `‖M v‖₂ ≤ ‖M‖ ‖v‖₂`, with `‖M‖` the operator norm on `ℓ²`. -/
theorem l2Norm_mulVec_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℂ) (v : ι → ℂ) : l2Norm (M *ᵥ v) ≤ ‖M‖ * l2Norm v := by
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp]
  exact Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 v)

/-- The bordered matrix `[[d, u*], [u, M]]` on `Fin (m + 1)`: corner `d`, column `u` below it,
row `u*` beside it, lower block `M`. -/
def borderMat (m : ℕ) (d : ℂ) (u : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of (Matrix.vecCons (Matrix.vecCons d (star u)) fun k => Matrix.vecCons (u k) (M k))

/-- Action of the bordered matrix on `(x₀, x')`. -/
private lemma borderInverse_borderMat_mulVec {m : ℕ} (d : ℂ) (u : Fin m → ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) (x : Fin (m + 1) → ℂ) :
    borderMat m d u M *ᵥ x =
      Matrix.vecCons (d * x 0 + star u ⬝ᵥ (fun k => x k.succ))
        (fun k => u k * x 0 + (M *ᵥ fun j => x j.succ) k) := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [borderMat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · simp [borderMat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- First column of the inverse of a bordered matrix, with the Schur complement
`s = d - u* M⁻¹ u`: `[[d, u*], [u, M]]⁻¹ e₀ = s⁻¹ (1, -M⁻¹ u)` [APSSS, (2.9)]. -/
theorem borderMat_inv_mulVec_single {m : ℕ} {d : ℂ} {u : Fin m → ℂ}
    {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.det ≠ 0) (hs : d - star u ⬝ᵥ (M⁻¹ *ᵥ u) ≠ 0) :
    (borderMat m d u M)⁻¹ *ᵥ Pi.single 0 1 =
      (d - star u ⬝ᵥ (M⁻¹ *ᵥ u))⁻¹ • Matrix.vecCons 1 (-(M⁻¹ *ᵥ u)) := by
  have hMu : M *ᵥ (M⁻¹ *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]
  have hMi : ∀ y : Fin m → ℂ, M⁻¹ *ᵥ (M *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]
  -- the bordered matrix is invertible
  have hdet : (borderMat m d u M).det ≠ 0 := by
    intro h
    obtain ⟨x, hx, hBx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    rw [borderInverse_borderMat_mulVec] at hBx
    have h0 : d * x 0 + star u ⬝ᵥ (fun k => x k.succ) = 0 := by
      simpa using congrFun hBx 0
    have h1 : (fun k => u k * x 0 + (M *ᵥ fun j => x j.succ) k) = 0 := by
      ext k
      simpa using congrFun hBx k.succ
    have hx' : (fun j => x j.succ) = -(x 0) • (M⁻¹ *ᵥ u) := by
      have : (M *ᵥ fun j => x j.succ) = -(x 0) • u := by
        ext k
        have := congrFun h1 k
        simp only [Pi.zero_apply] at this
        simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination this
      rw [← hMi (fun j => x j.succ), this, Matrix.mulVec_smul]
    have hs0 : (d - star u ⬝ᵥ (M⁻¹ *ᵥ u)) * x 0 = 0 := by
      rw [hx', dotProduct_smul, smul_eq_mul] at h0
      linear_combination h0
    have hx0 : x 0 = 0 := (mul_eq_zero.mp hs0).resolve_left hs
    apply hx
    ext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa using hx0
    · have := congrFun hx' k
      simpa [hx0] using this
  have hB : borderMat m d u M *ᵥ ((d - star u ⬝ᵥ (M⁻¹ *ᵥ u))⁻¹ •
      (Matrix.vecCons 1 (-(M⁻¹ *ᵥ u)) : Fin (m + 1) → ℂ)) = Pi.single 0 1 := by
    have ht : (fun j : Fin m => ((d - star u ⬝ᵥ (M⁻¹ *ᵥ u))⁻¹ •
        (Matrix.vecCons 1 (-(M⁻¹ *ᵥ u)) : Fin (m + 1) → ℂ)) j.succ) =
        (d - star u ⬝ᵥ (M⁻¹ *ᵥ u))⁻¹ • (-(M⁻¹ *ᵥ u)) := by
      ext j; simp
    have h0 : ((d - star u ⬝ᵥ (M⁻¹ *ᵥ u))⁻¹ •
        (Matrix.vecCons 1 (-(M⁻¹ *ᵥ u)) : Fin (m + 1) → ℂ)) 0 =
        (d - star u ⬝ᵥ (M⁻¹ *ᵥ u))⁻¹ := by simp
    rw [borderInverse_borderMat_mulVec, ht, h0]
    ext i
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [Matrix.cons_val_zero, Pi.single_eq_same, dotProduct_smul, dotProduct_neg]
      simp only [smul_eq_mul]
      field_simp
      ring
    · rw [Matrix.mulVec_smul, Matrix.mulVec_neg, hMu]
      simp
      ring
  calc (borderMat m d u M)⁻¹ *ᵥ Pi.single 0 1
      = (borderMat m d u M)⁻¹ *ᵥ (borderMat m d u M *ᵥ ((d - star u ⬝ᵥ (M⁻¹ *ᵥ u))⁻¹ •
        (Matrix.vecCons 1 (-(M⁻¹ *ᵥ u)) : Fin (m + 1) → ℂ))) := by rw [hB]
    _ = _ := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
          Matrix.one_mulVec]

/-- `‖[[d, u*], [u, M]]⁻¹ e₀‖₂ = (1 + ‖M⁻¹ u‖₂²)^{1/2} / |d - u* M⁻¹ u|` [APSSS, (2.9)]. -/
theorem l2Norm_borderMat_inv_single {m : ℕ} {d : ℂ} {u : Fin m → ℂ}
    {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.det ≠ 0) (hs : d - star u ⬝ᵥ (M⁻¹ *ᵥ u) ≠ 0) :
    l2Norm ((borderMat m d u M)⁻¹ *ᵥ Pi.single 0 1) =
      Real.sqrt (1 + l2Norm (M⁻¹ *ᵥ u) ^ 2) / ‖d - star u ⬝ᵥ (M⁻¹ *ᵥ u)‖ := by
  rw [borderMat_inv_mulVec_single hM hs]
  have hsum : ∑ i, ‖(Matrix.vecCons 1 (-(M⁻¹ *ᵥ u)) : Fin (m + 1) → ℂ) i‖ ^ 2 =
      1 + l2Norm (M⁻¹ *ᵥ u) ^ 2 := by
    rw [Fin.sum_univ_succ, l2Norm, Real.sq_sqrt (Finset.sum_nonneg fun k _ => by positivity)]
    simp
  have hs' : 0 < ‖d - star u ⬝ᵥ (M⁻¹ *ᵥ u)‖ := norm_pos_iff.mpr hs
  unfold l2Norm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum, hsum, norm_inv]
  rw [Real.sqrt_mul (by positivity), inv_pow, Real.sqrt_inv, Real.sqrt_sq hs'.le]
  rw [← l2Norm, div_eq_inv_mul]

/-- A unit vector is sent to the coordinate vector `e_{i₀}` by some unitary. -/
theorem exists_unitary_mulVec_eq_single {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι)
    {v : ι → ℂ} (hv : l2Norm v = 1) :
    ∃ U : Matrix.unitaryGroup ι ℂ, (U : Matrix ι ι ℂ) *ᵥ v = Pi.single i₀ 1 := by
  have hn : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ = 1 := by
    rw [← l2Norm_eq_norm_toLp, hv]
  have hon : Orthonormal ℂ (({i₀} : Set ι).domRestrict
      (fun _ : ι => (WithLp.toLp 2 v : EuclideanSpace ℂ ι))) := by
    refine ⟨fun i => by simpa [Set.domRestrict] using hn, fun i j hij => ?_⟩
    exact absurd (Subsingleton.elim i j) hij
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let P : Matrix.unitaryGroup ι ℂ :=
    ⟨(EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b,
      (EuclideanSpace.basisFun ι ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hP : (P : Matrix ι ι ℂ) *ᵥ Pi.single i₀ 1 = v := by
    ext i
    rw [Matrix.mulVec_single_one]
    simp [P, Module.Basis.toMatrix_apply, hb i₀ rfl]
  refine ⟨star P, ?_⟩
  rw [← hP, Matrix.mulVec_mulVec]
  have : ((star P : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) * (P : Matrix ι ι ℂ) = 1 := by
    simp
  rw [this, Matrix.one_mulVec]

end LSBA
