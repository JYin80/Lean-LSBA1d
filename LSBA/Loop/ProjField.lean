import LSBA.Loop.ErrorHierarchy
import LSBA.Loop.Projection
import LSBA.Averaging.LoopField

/-!
# The propagated projected loop error

The Ward profile of (C.33) [fo:eq:ward-projection], the coefficients of the propagated projected
loop error, its generator and bracket in the form of (C.35) [fo:eq:projected-error-equation], and
the heat class of the projected and of the propagated fields, for every loop length.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The Ward profile `θ_r(d) = (1 - r)(P(I - rP)⁻¹)_{x, x + d}`, averaged over `x`; for a
circulant `P` it is the probability profile `θ_u` before (C.33) [fo:eq:ward-projection]. -/
def wardProfile {L : ℕ} (P : Matrix (Fin L) (Fin L) ℝ) (r : ℝ) (d : Fin L) : ℝ :=
  (1 - r) / L * ∑ x : Fin L, mixedKer P r x (x + d)

/-- The coefficients of the propagated projected loop error before (C.35)
[fo:eq:projected-error-equation]: for words `a`, `b` of length `n + 1`,
`Σ_{b'} Π_j (I + (v - r)P(I - vP)⁻¹)_{a_j b'_j} (δ_{b'b} - δ_{b'_0 b_0} Π_{j ≥ 1} θ_r(b'_0 -
b'_j))`, so that `Σ_b coef(a, b) F(b) = Σ_{b'} Π_j U_{a_j b'_j} (𝒬_r F)(b')`. -/
def projCoef {L n : ℕ} (P : Matrix (Fin L) (Fin L) ℝ) (v r : ℝ) (a b : Fin (n + 1) → Fin L) : ℂ :=
  ∑ b' : Fin (n + 1) → Fin L, (∏ j, (((1 + (v - r) • mixedKer P v) (a j) (b' j) : ℝ) : ℂ)) *
    ((if b' = b then 1 else 0) -
      if b' 0 = b 0 then ∏ j : Fin n, ((wardProfile P r (b' 0 - b' j.succ) : ℝ) : ℂ) else 0)

/-! ### Kernels at a root -/

/-- Strict diagonal dominance: `1 - tX` is invertible when every absolute row of `X` is at most
`1` and `‖t‖ < 1`. -/
private lemma projField_det_ne {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n 𝕜) (hX : ∀ a, ∑ b, ‖X a b‖ ≤ 1) (t : 𝕜) (ht : ‖t‖ < 1) :
    (1 - t • X).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro k
  have hoff : ∀ j ∈ Finset.univ.erase k, ‖(1 - t • X) k j‖ = ‖t‖ * ‖X k j‖ := by
    intro j hj
    rw [Matrix.sub_apply, Matrix.one_apply_ne (Finset.ne_of_mem_erase hj).symm, zero_sub,
      norm_neg, Matrix.smul_apply, smul_eq_mul, norm_mul]
  rw [Finset.sum_congr rfl hoff, ← Finset.mul_sum]
  have hs : ∑ j ∈ Finset.univ.erase k, ‖X k j‖ = ∑ j, ‖X k j‖ - ‖X k k‖ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]; ring
  have hdiag : 1 - ‖t‖ * ‖X k k‖ ≤ ‖(1 - t • X) k k‖ := by
    rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul]
    calc 1 - ‖t‖ * ‖X k k‖ = ‖(1 : 𝕜)‖ - ‖t * X k k‖ := by rw [norm_one, norm_mul]
      _ ≤ ‖1 - t * X k k‖ := norm_sub_norm_le _ _
  have h2 : ‖t‖ * ∑ j, ‖X k j‖ ≤ ‖t‖ * 1 := mul_le_mul_of_nonneg_left (hX k) (norm_nonneg t)
  rw [hs]
  nlinarith [norm_nonneg t, norm_nonneg (X k k)]

/-- `1 - rP` is invertible for a probability kernel `P` and `|r| < 1`. -/
private lemma projField_isUnit {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1) {r : ℝ}
    (hr : r ∈ Set.Ioo (-1 : ℝ) 1) : IsUnit (1 - r • P).det := by
  refine isUnit_iff_ne_zero.mpr (projField_det_ne P (fun a => ?_) r ?_)
  · rw [show ∑ b, ‖P a b‖ = ∑ b, P a b from Finset.sum_congr rfl fun b _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hP a b)], hrow a]
  · rw [Real.norm_eq_abs, abs_lt]; exact hr

/-- `X` commutes with `(1 - cX)⁻¹` (Lean inverse). -/
private lemma projField_comm {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n R) (c : R) : X * (1 - c • X)⁻¹ = (1 - c • X)⁻¹ * X := by
  by_cases h : IsUnit (1 - c • X).det
  · have hc : (1 - c • X) * X = X * (1 - c • X) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul]
    calc X * (1 - c • X)⁻¹ = (1 - c • X)⁻¹ * ((1 - c • X) * X) * (1 - c • X)⁻¹ := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]
      _ = (1 - c • X)⁻¹ * (X * (1 - c • X)) * (1 - c • X)⁻¹ := by rw [hc]
      _ = (1 - c • X)⁻¹ * X := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, Matrix.mul_one]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.mul_zero, Matrix.zero_mul]

/-- `(1 - uX)(1 - vX)⁻¹ · X(1 - uX)⁻¹ = X(1 - vX)⁻¹` when `1 - uX` is invertible. -/
private lemma projField_prop_ker {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (X : Matrix n n R) (u v : R) (hA : (1 - u • X) * (1 - u • X)⁻¹ = 1) :
    (1 - u • X) * (1 - v • X)⁻¹ * (X * (1 - u • X)⁻¹) = X * (1 - v • X)⁻¹ := by
  have hBA : (1 - v • X)⁻¹ * (1 - u • X) = (1 - u • X) * (1 - v • X)⁻¹ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul, projField_comm X v]
  have hAP : (1 - u • X) * X = X * (1 - u • X) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
  calc (1 - u • X) * (1 - v • X)⁻¹ * (X * (1 - u • X)⁻¹)
      = (1 - v • X)⁻¹ * ((1 - u • X) * X) * (1 - u • X)⁻¹ := by
        rw [← hBA]; simp only [Matrix.mul_assoc]
    _ = (1 - v • X)⁻¹ * X * ((1 - u • X) * (1 - u • X)⁻¹) := by
        rw [hAP]; simp only [Matrix.mul_assoc]
    _ = X * (1 - v • X)⁻¹ := by rw [hA, Matrix.mul_one, projField_comm]

/-- `(1 - uX)(1 - vX)⁻¹ = 1 + (v - u) X(1 - vX)⁻¹` when `1 - vX` is invertible. -/
private lemma projField_prop_eq {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (X : Matrix n n R) (u v : R) (hB : (1 - v • X) * (1 - v • X)⁻¹ = 1) :
    (1 - u • X) * (1 - v • X)⁻¹ = 1 + (v - u) • (X * (1 - v • X)⁻¹) := by
  have e : (1 - u • X) = (1 - v • X) + (v - u) • X := by rw [sub_smul]; abel
  rw [e, Matrix.add_mul, hB, Matrix.smul_mul]

/-- Derivative in `t` of an entry of `A(1 - tP)⁻¹` at an invertible point. -/
private lemma projField_inv_hasDeriv {n : Type*} [Fintype n] [DecidableEq n]
    (A P : Matrix n n ℝ) (t : ℝ) (hU : IsUnit (1 - t • P)) (a b : n) :
    HasDerivAt (fun t' : ℝ => (A * (1 - t' • P)⁻¹) a b)
      ((A * ((1 - t • P)⁻¹ * P * (1 - t • P)⁻¹)) a b) t := by
  let _ := Matrix.linftyOpNormedRing (n := n) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := n) (R := ℝ) (α := ℝ)
  let ℓ : Matrix n n ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous (Matrix.entryLinearMap ℝ ℝ a b) 1 (by
      intro B
      simp only [Matrix.entryLinearMap_apply, one_mul]
      have h : ‖B a b‖₊ ≤ ‖B‖₊ := by
        rw [Matrix.linfty_opNNNorm_def]
        exact le_trans (Finset.single_le_sum (f := fun j => ‖B a j‖₊) (fun _ _ => zero_le)
          (Finset.mem_univ b)) (Finset.le_sup (f := fun i => ∑ j, ‖B i j‖₊) (Finset.mem_univ a))
      exact_mod_cast h)
  have hg := ((hasDerivAt_id t).smul_const P).const_sub (1 : Matrix n n ℝ)
  obtain ⟨x, hx⟩ := hU
  have h1 := hasFDerivAt_ringInverse (𝕜 := ℝ) x
  rw [hx] at h1
  have h2 := (h1.comp_hasDerivAt t (by simpa using hg)).const_mul A
  have h3 := ℓ.hasFDerivAt.comp_hasDerivAt t h2
  convert h3 using 1
  · funext t'
    simp [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  · simp [ℓ, hx, Matrix.nonsing_inv_eq_ringInverse]

/-- The derivative of the mixed kernel: `∂_r K_r = K_r²` at an invertible point. -/
private lemma projField_ker_hasDeriv {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (r : ℝ) (hU : IsUnit (1 - r • P).det) (a b : n) :
    HasDerivAt (fun r' : ℝ => mixedKer P r' a b) ((mixedKer P r * mixedKer P r) a b) r := by
  have h := projField_inv_hasDeriv P P r ((Matrix.isUnit_iff_isUnit_det _).mpr hU) a b
  have e : (P * ((1 - r • P)⁻¹ * P * (1 - r • P)⁻¹)) a b = (mixedKer P r * mixedKer P r) a b := by
    unfold mixedKer; simp only [Matrix.mul_assoc]
  rw [e] at h
  exact h

/-- Row sums of the mixed kernel: `Σ_b K_r(a, b) = (1 - r)⁻¹` for a kernel with unit rows. -/
private lemma projField_ker_row {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hrow : ∀ a, ∑ b, P a b = 1) {r : ℝ} (hr1 : r < 1) (hU : IsUnit (1 - r • P).det) (a : n) :
    ∑ b, mixedKer P r a b = (1 - r)⁻¹ := by
  have hmul : (1 - r • P)⁻¹ * (1 - r • P) = 1 := Matrix.nonsing_inv_mul _ hU
  have h1 : (1 - r • P) *ᵥ (1 : n → ℝ) = (1 - r) • (1 : n → ℝ) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    funext i
    have := hrow i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply,
      mul_one, this]
  have h2 : (1 - r) • ((1 - r • P)⁻¹ *ᵥ (1 : n → ℝ)) = 1 := by
    have := congrArg (fun M => M *ᵥ (1 : n → ℝ)) hmul
    simp only [← Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_smul] at this
    exact this
  have hne : (1 - r) ≠ 0 := by linarith
  have hN : (1 - r • P)⁻¹ *ᵥ (1 : n → ℝ) = (1 - r)⁻¹ • (1 : n → ℝ) := by
    calc (1 - r • P)⁻¹ *ᵥ (1 : n → ℝ)
        = (1 - r)⁻¹ • ((1 - r) • ((1 - r • P)⁻¹ *ᵥ (1 : n → ℝ))) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (1 - r)⁻¹ • (1 : n → ℝ) := by rw [h2]
  have h3 : (mixedKer P r *ᵥ (1 : n → ℝ)) a = (1 - r)⁻¹ := by
    unfold mixedKer
    rw [← Matrix.mulVec_mulVec, hN, Matrix.mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.one_apply, mul_one,
      hrow a]
  simpa [Matrix.mulVec, dotProduct] using h3

/-- The pair matrix `P = γ_g|M_B|²` at a root: nonnegative, rows summing to one, symmetric. -/
private lemma projField_P_facts (g : ℝ) (L : ℕ) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) :
    (∀ a b, 0 ≤ pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) a b) ∧
    (∀ a, ∑ b, pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) a b = 1) ∧
    (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))ᵀ =
      pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) := by
  have hD := primData_of_root g L hL E m hm
  refine ⟨fun a b => ?_, hD.row_sum, ?_⟩
  · simp only [pairP, Matrix.of_apply]
    exact mul_nonneg hD.pos.le (sq_nonneg _)
  · ext a b
    have h := congrFun (congrFun hD.symm a) b
    simp only [Matrix.transpose_apply] at h
    simp only [Matrix.transpose_apply, pairP, Matrix.of_apply, h]

/-- `(a + 1).val = (a.val + 1) % (n + 1)`. -/
private lemma projField_val_add_one {n : ℕ} (a : Fin (n + 1)) :
    ((a + 1 : Fin (n + 1)) : ℕ) = (a.val + 1) % (n + 1) := by
  rw [Fin.val_add]; simp [Nat.add_mod]

/-- The cycle adjacency matrix is invariant under the rotations of `ℤ_{n+1}`. -/
private lemma projField_cycleAdj_add {n : ℕ} (τ a b : Fin (n + 1)) :
    cycleAdj (n + 1) (a + τ) (b + τ) = cycleAdj (n + 1) a b := by
  have hf : ∀ x y : Fin (n + 1),
      cycleAdj (n + 1) x y = (if y = x + 1 then 1 else 0) + (if x = y + 1 then 1 else 0) := by
    intro x y
    unfold cycleAdj
    simp only [Matrix.of_apply]
    have h1 : (y.val = (x.val + 1) % (n + 1)) ↔ y = x + 1 := by
      rw [Fin.ext_iff, projField_val_add_one]
    have h2 : (x.val = (y.val + 1) % (n + 1)) ↔ x = y + 1 := by
      rw [Fin.ext_iff, projField_val_add_one]
    rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl]
  rw [hf, hf]
  have e1 : (b + τ = a + τ + 1) ↔ b = a + 1 := by
    rw [add_right_comm a τ 1]; exact add_left_inj τ
  have e2 : (a + τ = b + τ + 1) ↔ a = b + 1 := by
    rw [add_right_comm b τ 1]; exact add_left_inj τ
  simp only [e1, e2]

/-- `P = β|M_B|²` is invariant under the rotations of `ℤ_{n+1}`. -/
private lemma projField_P_shift {n : ℕ} (b β : ℝ) (z m : ℂ) (τ : Fin (n + 1)) :
    (pairP β (dysonMat b β (n + 1) z m)).submatrix (Equiv.addRight τ) (Equiv.addRight τ) =
      pairP β (dysonMat b β (n + 1) z m) := by
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    (b : ℂ) • cycleAdj (n + 1) - (z + β * m) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    with hB
  have hBs : B.submatrix (Equiv.addRight τ) (Equiv.addRight τ) = B := by
    ext x y
    simp [hB, Matrix.one_apply, projField_cycleAdj_add]
  have hM : (dysonMat b β (n + 1) z m).submatrix (Equiv.addRight τ) (Equiv.addRight τ) =
      dysonMat b β (n + 1) z m := by
    have := Matrix.inv_submatrix_equiv B (Equiv.addRight τ) (Equiv.addRight τ)
    rw [hBs] at this
    exact this.symm
  ext x y
  have := congrFun (congrFun hM x) y
  simp only [Matrix.submatrix_apply, Equiv.coe_addRight] at this
  simp only [Matrix.submatrix_apply, Equiv.coe_addRight, pairP, Matrix.of_apply, this]

/-- The mixed kernel of a rotation-invariant `P` is rotation invariant. -/
private lemma projField_ker_shift {n : ℕ} (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hP : ∀ τ, P.submatrix (Equiv.addRight τ) (Equiv.addRight τ) = P) (r : ℝ) (τ : Fin (n + 1)) :
    (mixedKer P r).submatrix (Equiv.addRight τ) (Equiv.addRight τ) = mixedKer P r := by
  have h1 : (1 - r • P).submatrix (Equiv.addRight τ) (Equiv.addRight τ) = 1 - r • P := by
    ext x y
    have := congrFun (congrFun (hP τ) x) y
    simp only [Matrix.submatrix_apply, Equiv.coe_addRight] at this
    simp [Matrix.one_apply, this]
  have h2 : ((1 - r • P)⁻¹).submatrix (Equiv.addRight τ) (Equiv.addRight τ) = (1 - r • P)⁻¹ := by
    have := Matrix.inv_submatrix_equiv (1 - r • P) (Equiv.addRight τ) (Equiv.addRight τ)
    rw [h1] at this
    exact this.symm
  unfold mixedKer
  rw [← Matrix.submatrix_mul_equiv _ _ _ (Equiv.addRight τ), hP, h2]

/-- The product of two rotation-invariant matrices is rotation invariant. -/
private lemma projField_mul_shift {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : ∀ τ, A.submatrix (Equiv.addRight τ) (Equiv.addRight τ) = A)
    (hB : ∀ τ, B.submatrix (Equiv.addRight τ) (Equiv.addRight τ) = B) (τ : Fin (n + 1)) :
    (A * B).submatrix (Equiv.addRight τ) (Equiv.addRight τ) = A * B := by
  rw [← Matrix.submatrix_mul_equiv _ _ _ (Equiv.addRight τ), hA, hB]

/-- A rotation-invariant matrix depends only on the difference: `A(z, z + (x - y)) = A(y, x)`. -/
private lemma projField_shift_apply {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : ∀ τ, A.submatrix (Equiv.addRight τ) (Equiv.addRight τ) = A) (z x y : Fin (n + 1)) :
    A z (z + (x - y)) = A y x := by
  have := congrFun (congrFun (hA (y - z)) z) (z + (x - y))
  simp only [Matrix.submatrix_apply, Equiv.coe_addRight] at this
  rw [← this]
  congr 1 <;> abel

/-- The mixed kernel of a symmetric `P` is symmetric. -/
private lemma projField_ker_symm {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hsym : Pᵀ = P) (r : ℝ) (x y : n) : mixedKer P r x y = mixedKer P r y x := by
  have hA : (1 - r • P)ᵀ = 1 - r • P := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hsym]
  have hT : (mixedKer P r)ᵀ = mixedKer P r := by
    unfold mixedKer
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hA, hsym, projField_comm]
  exact (congrFun (congrFun hT y) x)

/-- The Ward profile of a rotation-invariant symmetric probability kernel on `ℤ_{n+1}`. -/
private lemma projField_ward {n : ℕ} (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hP : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1) (hsym : Pᵀ = P)
    (hshift : ∀ τ, P.submatrix (Equiv.addRight τ) (Equiv.addRight τ) = P) :
    (∀ r : ℝ, r ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x y : Fin (n + 1),
      mixedKer P r x y = mixedKer P r y x ∧
      wardProfile P r (x - y) = (1 - r) * mixedKer P r y x ∧
      HasDerivAt (fun r' => wardProfile P r' (x - y))
        (∑ c, mixedKer P r y c * wardProfile P r (x - c) -
          (1 - r)⁻¹ * wardProfile P r (x - y)) r) ∧
    ∀ r : ℝ, 0 ≤ r → r < 1 →
      (∀ d, 0 ≤ wardProfile P r d) ∧ ∑ d, wardProfile P r d = 1 := by
  have hLne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hθ : ∀ (r : ℝ) (x y : Fin (n + 1)),
      wardProfile P r (x - y) = (1 - r) * mixedKer P r y x := by
    intro r x y
    unfold wardProfile
    simp only [projField_shift_apply _ (projField_ker_shift P hshift r), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨fun r hr x y => ⟨projField_ker_symm P hsym r x y, hθ r x y, ?_⟩, fun r hr0 hr1 => ?_⟩
  · have hU := projField_isUnit P hP hrow hr
    have hne : (1 - r) ≠ 0 := by linarith [hr.2]
    have hd : HasDerivAt (fun r' => wardProfile P r' (x - y))
        ((-1) / ((n + 1 : ℕ) : ℝ) * ∑ z, mixedKer P r z (z + (x - y)) +
          (1 - r) / ((n + 1 : ℕ) : ℝ) * ∑ z, (mixedKer P r * mixedKer P r) z (z + (x - y))) r := by
      have h1 : HasDerivAt (fun r' : ℝ => (1 - r') / ((n + 1 : ℕ) : ℝ))
          ((-1) / ((n + 1 : ℕ) : ℝ)) r := by
        simpa using ((hasDerivAt_id r).const_sub 1).div_const ((n + 1 : ℕ) : ℝ)
      have h2 := HasDerivAt.fun_sum (u := Finset.univ) (fun z _ =>
        projField_ker_hasDeriv P r hU z (z + (x - y)))
      exact h1.mul h2
    refine hd.congr_deriv ?_
    have hKK : ∀ τ, (mixedKer P r * mixedKer P r).submatrix (Equiv.addRight τ)
        (Equiv.addRight τ) = mixedKer P r * mixedKer P r :=
      projField_mul_shift _ _ (projField_ker_shift P hshift r) (projField_ker_shift P hshift r)
    simp only [projField_shift_apply _ (projField_ker_shift P hshift r),
      projField_shift_apply _ hKK, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hθ, Matrix.mul_apply]
    have e1 : ∑ c, mixedKer P r y c * ((1 - r) * mixedKer P r c x) =
        (1 - r) * ∑ c, mixedKer P r y c * mixedKer P r c x := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
    rw [e1]
    field_simp
    ring
  · obtain ⟨hK0, hKr⟩ := mixedKer_nonneg_row P hP hrow r hr0 hr1
    have hne : (1 - r) ≠ 0 := by linarith
    refine ⟨fun d => ?_, ?_⟩
    · unfold wardProfile
      exact mul_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun x _ => hK0 _ _)
    · unfold wardProfile
      rw [← Finset.mul_sum, Finset.sum_comm]
      have hs : ∀ x : Fin (n + 1), ∑ d, mixedKer P r x (x + d) = (1 - r)⁻¹ := by
        intro x
        rw [← hKr x]
        exact Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun d => rfl)
      simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-- `γ_g > 0`. -/
private lemma projField_gamma_pos (g : ℝ) : 0 < gammaG g := by
  have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold gammaG; positivity

/-- The two-loops of (5.13) [fo:eq:pairs]: `γ_g W 𝒦_2(c, y; s, s') = 𝒦^{ss'}(c, y)`. -/
private lemma projField_primLoop_two (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (E : ℝ) (m : ℂ) (t : ℝ)
    (c y : Fin L) (s s' : Bool) :
    ((gammaG g * W : ℝ) : ℂ) * primLoop g W L E m t ![c, y] ![s, s'] =
      pairK (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t s s' c y := by
  have hγ : (gammaG g : ℂ) ≠ 0 := by exact_mod_cast (projField_gamma_pos g).ne'
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
  have e : primLoop g W L E m t ![c, y] ![s, s'] = (W : ℂ) ^ (1 - ((2 : ℕ) : ℤ)) *
      ((gammaG g : ℂ)⁻¹ * pairK (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t s s' c y) :=
    rfl
  rw [e, show (1 : ℤ) - ((2 : ℕ) : ℤ) = -1 by norm_num, zpow_neg_one]
  push_cast
  field_simp

/-- `∂_r U^{+-}_{r,v} = -P(I - vP)⁻¹`, entrywise and cast to `ℂ`. -/
private lemma projField_propPM_deriv {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (v r : ℝ) (x y : n) :
    HasDerivAt (fun r : ℝ => ((propPM P r v x y : ℝ) : ℂ))
      (((-(P * (1 - v • P)⁻¹) x y : ℝ) : ℂ)) r := by
  have e : (fun r : ℝ => propPM P r v x y) =
      fun r => (1 - v • P)⁻¹ x y - r * (P * (1 - v • P)⁻¹) x y := by
    funext r
    simp [propPM, Matrix.sub_mul]
  have h := (((hasDerivAt_id' r).mul_const ((P * (1 - v • P)⁻¹) x y)).const_sub
    ((1 - v • P)⁻¹ x y))
  rw [← e] at h
  convert h.ofReal_comp using 1
  simp

/-- `∂_r U^{++}_{r,v} = -Q(I - vQ)⁻¹`, entrywise. -/
private lemma projField_propPP_deriv {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (v r : ℝ) (x y : n) :
    HasDerivAt (fun r' : ℝ => propPP Q r' v x y) (-(Q * (1 - (v : ℂ) • Q)⁻¹) x y) r := by
  have e : (fun r' : ℝ => propPP Q r' v x y) =
      fun r' : ℝ => (1 - (v : ℂ) • Q)⁻¹ x y - (r' : ℂ) * (Q * (1 - (v : ℂ) • Q)⁻¹) x y := by
    funext r'
    simp [propPP, Matrix.sub_mul]
  rw [e]
  have h := ((hasDerivAt_id r).ofReal_comp.mul_const ((Q * (1 - (v : ℂ) • Q)⁻¹) x y)).const_sub
    ((1 - (v : ℂ) • Q)⁻¹ x y)
  convert h using 1 <;> simp

/-! ### Smoothness of the coefficients in time -/

/-- The entries of the mixed kernel of a probability kernel are `C¹` in `r ∈ (-1, 1)`. -/
private lemma projField_ker_contDiffOn {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1) (a b : n) :
    ContDiffOn ℝ 1 (fun r => mixedKer P r a b) (Set.Ioo (-1) 1) := by
  have hd : ∀ r ∈ Set.Ioo (-1 : ℝ) 1, ∀ a b, HasDerivAt (fun r' => mixedKer P r' a b)
      ((mixedKer P r * mixedKer P r) a b) r :=
    fun r hr a b => projField_ker_hasDeriv P r (projField_isUnit P hP hrow hr) a b
  have hc : ∀ a b, ContinuousOn (fun r => mixedKer P r a b) (Set.Ioo (-1) 1) :=
    fun a b r hr => (hd r hr a b).continuousAt.continuousWithinAt
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun r hr => (hd r hr a b).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  refine ContinuousOn.congr (f := fun r => (mixedKer P r * mixedKer P r) a b) ?_
    (fun r hr => (hd r hr a b).deriv)
  simp only [Matrix.mul_apply]
  exact continuousOn_finsetSum _ fun c _ => (hc a c).mul (hc c b)

/-- The real-to-complex cast of a `C¹` function is `C¹`. -/
private lemma projField_ofReal {f : ℝ → ℝ} {s : Set ℝ} (hf : ContDiffOn ℝ 1 f s) :
    ContDiffOn ℝ 1 (fun r => ((f r : ℝ) : ℂ)) s :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn hf

/-- The Ward profile of a probability kernel is `C¹` in `r ∈ (-1, 1)`. -/
private lemma projField_ward_contDiffOn {L : ℕ} (P : Matrix (Fin L) (Fin L) ℝ)
    (hP : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1) (d : Fin L) :
    ContDiffOn ℝ 1 (fun r => wardProfile P r d) (Set.Ioo (-1) 1) := by
  unfold wardProfile
  exact (contDiffOn_const.sub contDiffOn_id).div_const _ |>.mul
    (ContDiffOn.sum fun x _ => projField_ker_contDiffOn P hP hrow x (x + d))

/-- The coefficients `coef_r(a, b)` are `C¹` in `r ∈ (-1, 1)`. -/
private lemma projField_projCoef_contDiffOn {L n : ℕ} (P : Matrix (Fin L) (Fin L) ℝ)
    (hP : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1) (v : ℝ) (a b : Fin (n + 1) → Fin L) :
    ContDiffOn ℝ 1 (fun r => projCoef P v r a b) (Set.Ioo (-1) 1) := by
  unfold projCoef
  refine ContDiffOn.sum fun b' _ => ContDiffOn.mul ?_ ?_
  · refine contDiffOn_prod fun j _ => projField_ofReal ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact contDiffOn_const.add ((contDiffOn_const.sub contDiffOn_id).mul contDiffOn_const)
  · refine contDiffOn_const.sub ?_
    by_cases h : b' 0 = b 0
    · simp only [h, ite_true]
      exact contDiffOn_prod fun j _ => projField_ofReal (projField_ward_contDiffOn P hP hrow _)
    · simp only [h, ite_false]
      exact contDiffOn_const

/-- The propagators `U^{σσ'}_{r,v}` are `C¹` (affine) in `r`. -/
private lemma projField_pairU_contDiff {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (v : ℝ)
    (s s' : Bool) (x y : Fin L) : ContDiff ℝ 1 (fun r => pairU β M r v s s' x y) := by
  have hof : ContDiff ℝ 1 (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contDiff
  have hPP : ContDiff ℝ 1 (fun r : ℝ => propPP (pairQ β M) r v x y) := by
    simp only [propPP, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact ContDiff.sum fun c _ => (contDiff_const.sub (hof.mul contDiff_const)).mul contDiff_const
  have hPMr : ContDiff ℝ 1 (fun r : ℝ => propPM (pairP β M) r v x y) := by
    simp only [propPM, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact ContDiff.sum fun c _ =>
      (contDiff_const.sub (contDiff_id.mul contDiff_const)).mul contDiff_const
  have hPM : ContDiff ℝ 1 (fun r : ℝ => ((propPM (pairP β M) r v x y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hPMr
  cases s <;> cases s'
  · simp only [pairU, ite_true, Bool.false_eq_true, ite_false, Matrix.map_apply]
    exact Complex.conjCLE.contDiff.comp hPP
  · simpa [pairU] using hPM
  · simpa [pairU] using hPM
  · simpa [pairU] using hPP

/-! ### The heat class of time coefficients -/

/-- The zero field is in the heat class. -/
private lemma projField_heat_zero {ι : Type*} [Fintype ι] (a b : ℝ) :
    HeatClass (fun (_ : ℝ) (_ : ι → ℝ) => (0 : ℂ)) a b :=
  ⟨continuousOn_const, ⟨0, fun _ _ _ => le_of_eq norm_zero⟩,
    ⟨fun _ _ => 0, fun r _ _ => hasDerivAt_const r 0, continuousOn_const, 0,
      fun _ _ _ => le_of_eq norm_zero⟩,
    ⟨fun _ _ => (0 : (ι → ℝ) →L[ℝ] ℂ), fun _ _ => (0 : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ),
      fun _ _ x => hasFDerivAt_const 0 x,
      fun _ _ x => hasFDerivAt_const 0 x, continuousOn_const, continuousOn_const, 0,
      fun _ _ _ => ⟨by simp, ContinuousLinearMap.opNorm_le_bound _ le_rfl fun _ => by simp⟩⟩⟩

/-- A function of time that is `C¹` on `(-1, 1)` is in the heat class on every window inside
`(-1, 1)`. -/
private lemma projField_heat_time {ι : Type*} [Fintype ι] (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ 1 f (Set.Ioo (-1) 1)) {a' b' : ℝ} (ha' : -1 < a') (hb' : b' < 1) :
    HeatClass (fun r (_ : ι → ℝ) => f r) a' b' := by
  have hsub : Set.Ioo a' b' ⊆ Set.Ioo (-1) 1 := fun r hr => ⟨ha'.trans hr.1, hr.2.trans hb'⟩
  have hIcc : Set.Icc a' b' ⊆ Set.Ioo (-1) 1 := fun r hr =>
    ⟨ha'.trans_le hr.1, hr.2.trans_lt hb'⟩
  have hd : ∀ r ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt f (deriv f r) r := fun r hr =>
    ((hf.differentiableOn one_ne_zero r hr).differentiableAt (isOpen_Ioo.mem_nhds hr)).hasDerivAt
  have hc' : ContinuousOn (deriv f) (Set.Ioo (-1) 1) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn.mono hIcc)
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc'.mono hIcc)
  have h := (projField_heat_zero (ι := ι) a' b').sub_time (fun r => -f r) (fun r => -deriv f r)
    (fun r hr => (hd r (hsub hr)).neg) (hc'.mono hsub).neg
    ⟨max C₁ C₂, fun r hr => ⟨by
      rw [norm_neg]; exact (hC₁ r (Set.Ioo_subset_Icc_self hr)).trans (le_max_left _ _), by
      rw [norm_neg]; exact (hC₂ r (Set.Ioo_subset_Icc_self hr)).trans (le_max_right _ _)⟩⟩
  simpa using h

/-- A finite sum of fields in the heat class is in the heat class. -/
private lemma projField_heat_sum {ι β : Type*} [Fintype ι] (s : Finset β)
    (F : β → ℝ → (ι → ℝ) → ℂ) {a b : ℝ} (h : ∀ i ∈ s, HeatClass (F i) a b) :
    HeatClass (fun r x => ∑ i ∈ s, F i r x) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using projField_heat_zero (ι := ι) a b
  | insert i s hi ih =>
    have := (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert hi] using this

/-! ### The coefficients and the projection -/

/-- `Σ_b coef_r(a, b) G(b) = Σ_{b'} Π_j U_{a_j b'_j} (𝒬_r G)(b')` with `U = I + (v - r)K_v`. -/
private lemma projField_coef_sum {L n : ℕ} (P : Matrix (Fin L) (Fin L) ℝ) (v r : ℝ)
    (a : Fin (n + 1) → Fin L) (G : (Fin (n + 1) → Fin L) → ℂ) :
    ∑ b, projCoef P v r a b * G b =
      ∑ b', (∏ j, (((1 + (v - r) • mixedKer P v) (a j) (b' j) : ℝ) : ℂ)) *
        projQ (wardProfile P r) G b' := by
  unfold projCoef
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  simp_rw [mul_assoc, ← Finset.mul_sum]
  congr 1
  unfold projQ rowSum
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b' 0 = b 0
  · simp [h, mul_comm]
  · simp [h, Ne.symm h]

/-- `𝒬` is linear: `𝒬(Σ_i w_i F_i) = Σ_i w_i 𝒬 F_i`. -/
private lemma projField_projQ_sum {L n : ℕ} {ι : Type*} [Fintype ι] (θ : Fin L → ℝ) (w : ι → ℂ)
    (F : ι → (Fin (n + 1) → Fin L) → ℂ) (b : Fin (n + 1) → Fin L) :
    projQ θ (fun c => ∑ i, w i * F i c) b = ∑ i, w i * projQ θ (F i) b := by
  unfold projQ rowSum
  have e : ∀ c : Fin (n + 1) → Fin L, (if c 0 = b 0 then ∑ i, w i * F i c else 0) =
      ∑ i, w i * (if c 0 = b 0 then F i c else 0) := fun c => by split_ifs <;> simp
  simp only [e]
  rw [Finset.sum_comm]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]

/-- `𝒬` is additive. -/
private lemma projField_projQ_add {L n : ℕ} (θ : Fin L → ℝ) (F G : (Fin (n + 1) → Fin L) → ℂ)
    (b : Fin (n + 1) → Fin L) :
    projQ θ (fun c => F c + G c) b = projQ θ F b + projQ θ G b := by
  unfold projQ rowSum
  have h : ∑ c : Fin (n + 1) → Fin L, (if c 0 = b 0 then F c + G c else 0) =
      (∑ c : Fin (n + 1) → Fin L, if c 0 = b 0 then F c else 0) +
        ∑ c : Fin (n + 1) → Fin L, if c 0 = b 0 then G c else 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by split_ifs <;> simp
  rw [h]
  ring

/-- The coefficients are real. -/
private lemma projField_star_coef {L n : ℕ} (P : Matrix (Fin L) (Fin L) ℝ) (v r : ℝ)
    (a b : Fin (n + 1) → Fin L) : star (projCoef P v r a b) = projCoef P v r a b := by
  unfold projCoef
  simp only [star_sum, star_mul', star_prod, star_sub, Complex.star_def, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun b' _ => ?_
  congr 1
  congr 1
  · split_ifs <;> simp
  · split_ifs
    · simp only [map_prod, Complex.conj_ofReal]
    · simp

/-- Moving along a block direction from `M`: the slice at `e • δ_{(c,κ)}` is `M + e T_{c,κ}`. -/
private theorem projField_slice_line {W L : ℕ}
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c : Fin L) (κ : Fin W × Fin W) (e : ℝ) :
    blockSlice W L M (e • Pi.single (c, κ.1, κ.2) 1) = M + (e : ℂ) • blockBasis W L c κ := by
  unfold blockSlice
  congr 1
  rw [Finset.sum_eq_single c, Finset.sum_eq_single κ]
  · simp
  · intro κ' _ hκ'
    have : (c, κ'.1, κ'.2) ≠ (c, κ.1, κ.2) := by
      intro h; apply hκ'; simp only [Prod.mk.injEq, true_and] at h; exact Prod.ext h.1 h.2
    simp [this]
  · simp
  · intro c' _ hc'
    refine Finset.sum_eq_zero fun κ' _ => ?_
    have : (c', κ'.1, κ'.2) ≠ (c, κ.1, κ.2) := by
      intro h; apply hc'; simp only [Prod.mk.injEq] at h; exact h.1
    simp [this]
  · simp

/-- A resolvent loop at the characteristic is differentiable in time at `u < 1`, and twice
differentiable along every block direction. -/
private theorem projField_smooth (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L k : ℕ} {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    DifferentiableAt ℝ (fun r => resLoop g E m a σ r M) u ∧
    ∀ (c : Fin L) (κ : Fin W × Fin W),
      (∀ e : ℝ, DifferentiableAt ℝ
        (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ)) e) ∧
      DifferentiableAt ℝ
        (deriv (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ))) 0 := by
  have hC := heatClass_loopTr W L k M hM g E m hm a σ (a' := u - 1) (b' := (u + 1) / 2)
    (by linarith)
  have hu' : u ∈ Set.Ioo (u - 1) ((u + 1) / 2) := ⟨by linarith, by linarith⟩
  have h0 : blockSlice W L M 0 = M := by simp [blockSlice]
  obtain ⟨Fu, hFu, -⟩ := hC.du
  obtain ⟨DF, D2F, hD, hD2, -⟩ := hC.dx
  refine ⟨?_, fun c κ => ?_⟩
  · have := (hFu u hu' 0).differentiableAt
    simpa [resLoop, h0] using this
  · set w : Ω W L := Pi.single (c, κ.1, κ.2) 1 with hw
    have hφ : ∀ e : ℝ, HasDerivAt (fun e : ℝ => e • w) w e := fun e => by
      simpa using (hasDerivAt_id e).smul_const w
    have hf : (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ)) =
        (fun x => loopTr (resolventMat (blockSlice W L M x) (zChar g E m u)) a σ) ∘
          (fun e : ℝ => e • w) := by
      funext e
      simp only [Function.comp, hw, projField_slice_line, resLoop]
    have hder : ∀ e : ℝ, HasDerivAt
        (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ))
        (DF u (e • w) w) e := fun e => by
      rw [hf]; exact (hD u hu' (e • w)).comp_hasDerivAt e (hφ e)
    refine ⟨fun e => (hder e).differentiableAt, ?_⟩
    have hdf : deriv (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ)) =
        fun e => DF u (e • w) w := funext fun e => (hder e).deriv
    rw [hdf]
    have h1 : DifferentiableAt ℝ (fun e : ℝ => DF u (e • w)) 0 :=
      (hD2 u hu' ((0 : ℝ) • w)).differentiableAt.comp (0 : ℝ) (hφ 0).differentiableAt
    exact h1.clm_apply (differentiableAt_const w)

/-! ### Generator identities -/

/-- Linearity of the block generator over a finite family with time-dependent scalar coefficients
`w_b`: `𝒢(Σ_b w_b G_b) = Σ_b (∂_u w_b · G_b + w_b 𝒢 G_b)`. -/
private theorem projField_blockGen_sum {W L : ℕ} (γ : ℝ) {ι : Type*} [Fintype ι]
    (w : ι → ℝ → ℂ) (w' : ι → ℂ)
    (G : ι → ℝ → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ → ℂ) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (hw : ∀ b, HasDerivAt (w b) (w' b) u)
    (hGt : ∀ b, DifferentiableAt ℝ (fun r => G b r M) u)
    (hGl : ∀ b (c : Fin L) (κ : Fin W × Fin W),
      (∀ e : ℝ, DifferentiableAt ℝ (fun e : ℝ => G b u (M + (e : ℂ) • blockBasis W L c κ)) e) ∧
      DifferentiableAt ℝ (deriv (fun e : ℝ => G b u (M + (e : ℂ) • blockBasis W L c κ))) 0) :
    blockGen W L γ (fun r N => ∑ b, w b r * G b r N) u M =
      ∑ b, (w' b * G b u M + w b u * blockGen W L γ (G b) u M) := by
  unfold blockGen
  have ht : deriv (fun r => ∑ b, w b r * G b r M) u =
      ∑ b, (w' b * G b u M + w b u * deriv (fun r => G b r M) u) :=
    (HasDerivAt.fun_sum (u := Finset.univ)
      fun b _ => ((hw b).mul (hGt b).hasDerivAt)).deriv
  have hl : ∀ (c : Fin L) (κ : Fin W × Fin W),
      iteratedDeriv 2 (fun e : ℝ => ∑ b, w b u * G b u (M + (e : ℂ) • blockBasis W L c κ)) 0 =
      ∑ b, w b u * iteratedDeriv 2 (fun e : ℝ => G b u (M + (e : ℂ) • blockBasis W L c κ)) 0 := by
    intro c κ
    have h1 : deriv (fun e : ℝ => ∑ b, w b u * G b u (M + (e : ℂ) • blockBasis W L c κ)) =
        fun e => ∑ b, w b u * deriv (fun e : ℝ => G b u (M + (e : ℂ) • blockBasis W L c κ)) e :=
      funext fun e => (HasDerivAt.fun_sum (u := Finset.univ)
        fun b _ => (((hGl b c κ).1 e).hasDerivAt.const_mul (w b u))).deriv
    rw [iteratedDeriv_succ, iteratedDeriv_one, h1, (HasDerivAt.fun_sum (u := Finset.univ)
      fun b _ => ((hGl b c κ).2.hasDerivAt.const_mul (w b u))).deriv]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [ht]
  simp only [hl]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  have hswap : ∑ c : Fin L, ∑ κ : Fin W × Fin W, ∑ b, ((γ / (2 * W) : ℝ) : ℂ) *
      (w b u * iteratedDeriv 2 (fun e : ℝ => G b u (M + (e : ℂ) • blockBasis W L c κ)) 0) =
      ∑ b, ∑ c : Fin L, ∑ κ : Fin W × Fin W, w b u * (((γ / (2 * W) : ℝ) : ℂ) *
        iteratedDeriv 2 (fun e : ℝ => G b u (M + (e : ℂ) • blockBasis W L c κ)) 0) := by
    calc _ = ∑ c : Fin L, ∑ b, ∑ κ : Fin W × Fin W, ((γ / (2 * W) : ℝ) : ℂ) *
          (w b u * iteratedDeriv 2 (fun e : ℝ => G b u (M + (e : ℂ) • blockBasis W L c κ)) 0) :=
          Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
            Finset.sum_congr rfl fun κ _ => ?_
          ring
  rw [hswap, ← Finset.sum_add_distrib]

/-- Exchange of the labels `b_j ↔ c` in a double sum over words `b` and labels `c`. -/
private theorem projField_swap_sum {L k : ℕ} (j : Fin k)
    (F : (Fin k → Fin L) → Fin L → ℂ) :
    ∑ b : Fin k → Fin L, ∑ c : Fin L, F b c =
      ∑ b : Fin k → Fin L, ∑ c : Fin L, F (Function.update b j c) (b j) := by
  have hinv : Function.Involutive
      (fun p : (Fin k → Fin L) × Fin L => (Function.update p.1 j p.2, p.1 j)) := by
    intro p
    simp
  rw [← Fintype.sum_prod_type' F,
    ← Fintype.sum_prod_type' (fun b c => F (Function.update b j c) (b j))]
  exact (Equiv.sum_comp (Function.Involutive.toPerm _ hinv)
    (fun p : (Fin k → Fin L) × Fin L => F p.1 p.2)).symm

/-- The cancellation of `Θ` against the time derivative of the deterministic legs: for
`∂_u V_j = -V_j · κ K_j`, `Σ_b (∂_u Π_j V_j) D_b + Σ_b (Π_j V_j) Θ D (b) = 0`. -/
private theorem projField_theta_cancel {L k : ℕ} (κ₀ : ℂ) (a : Fin k → Fin L)
    (V : Fin k → Fin L → Fin L → ℂ) (K2 : Fin k → Fin L → Fin L → ℂ)
    (D : (Fin k → Fin L) → ℂ) :
    ∑ b : Fin k → Fin L,
      ((∑ j, (∏ l ∈ Finset.univ.erase j, V l (a l) (b l)) •
          (-(∑ c, V j (a j) c * (κ₀ * K2 j c (b j))))) * D b +
        (∏ j, V j (a j) (b j)) * (κ₀ * ∑ j, ∑ c, K2 j (b j) c * D (Function.update b j c))) =
      0 := by
  set S : ℂ := ∑ j, ∑ b : Fin k → Fin L, ∑ c,
    (∏ l ∈ Finset.univ.erase j, V l (a l) (b l)) * V j (a j) c * K2 j c (b j) * D b with hS
  have hA : ∑ b : Fin k → Fin L, (∑ j, (∏ l ∈ Finset.univ.erase j, V l (a l) (b l)) •
      (-(∑ c, V j (a j) c * (κ₀ * K2 j c (b j))))) * D b = -κ₀ * S := by
    rw [hS, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, ← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hB : ∑ b : Fin k → Fin L, (∏ j, V j (a j) (b j)) *
      (κ₀ * ∑ j, ∑ c, K2 j (b j) c * D (Function.update b j c)) = κ₀ * S := by
    have h1 : ∀ b : Fin k → Fin L, (∏ j, V j (a j) (b j)) *
        (κ₀ * ∑ j, ∑ c, K2 j (b j) c * D (Function.update b j c)) =
        κ₀ * ∑ j, ∑ c, (∏ l, V l (a l) (b l)) * K2 j (b j) c * D (Function.update b j c) := by
      intro b
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
      ring
    simp only [h1]
    rw [← Finset.mul_sum, Finset.sum_comm, hS]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [projField_swap_sum j]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    have hp : ∏ l, V l (a l) (Function.update b j c l) =
        V j (a j) c * ∏ l ∈ Finset.univ.erase j, V l (a l) (b l) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
    rw [hp, Function.update_self, Function.update_idem, Function.update_eq_self]
    ring
  rw [Finset.sum_add_distrib, hA, hB]
  ring

/-- The primitive loops satisfy (5.10) [fo:eq:primitive] at every `u ∈ (-1, 1)`, all lengths. -/
private theorem projField_primDeriv (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (u : ℝ) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    IsPrimDeriv (gammaG g) W L (fun r n b τ => primLoop g W L E m r (k := n) b τ) u := by
  intro n a σ
  rcases n with _ | _ | n
  · have h0 : cutSumFam (fun n b τ => primLoop g W L E m u (k := n) b τ) a σ = 0 := by
      simp [cutSumFam]
    rw [h0, mul_zero]
    exact hasDerivAt_const u (primLoop g W L E m 0 a σ)
  · have h1 : cutSumFam (fun n b τ => primLoop g W L E m u (k := n) b τ) a σ = 0 := by
      simp [cutSumFam]
    rw [h1, mul_zero]
    exact hasDerivAt_const u (primLoop g W L E m 0 a σ)
  · exact primLoop_hasDerivAt g W L hW hL E m hm u hu (by omega) a σ

/-- The Ward profile at a root of (5.2) [fo:eq:dyson-family]: for `|r| < 1` the kernel
`K_r = P(I - rP)⁻¹` of `P = γ_g|M_B|²` is symmetric, `θ_r(x - y) = (1 - r)K_r(y, x)`, and
`∂_r θ_r(x - y) = Σ_c K_r(y, c) θ_r(x - c) - (1 - r)⁻¹ θ_r(x - y)`, the profile identity behind
(C.35) [fo:eq:projected-error-equation]; for `0 ≤ r < 1`, `θ_r` is a probability profile. -/
theorem wardProfile_facts (g : ℝ) (L : ℕ) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) :
    (∀ r : ℝ, r ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x y : Fin L,
      mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r x y =
        mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r y x ∧
      wardProfile (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r (x - y) =
        (1 - r) * mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r y x ∧
      HasDerivAt
        (fun r' => wardProfile (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r' (x - y))
        (∑ c, mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r y c *
            wardProfile (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r (x - c) -
          (1 - r)⁻¹ *
            wardProfile (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r (x - y)) r) ∧
    ∀ r : ℝ, 0 ≤ r → r < 1 →
      (∀ d, 0 ≤ wardProfile (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r d) ∧
      ∑ d, wardProfile (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r d = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  obtain ⟨hP, hrow, hsym⟩ := projField_P_facts g (n + 1) hL E m hm
  exact projField_ward _ hP hrow hsym (fun τ => projField_P_shift _ _ _ _ τ)

/-- The propagators `U^{σσ'}_{r,v}` of (5.15) [fo:eq:propagators] at a root, for every pair of
signs: `∂_r U_{r,v} = -U_{r,v} γ_g W 𝒦_2^{σσ'}(r)` for `|r|, |v| < 1`, with `𝒦_2` the pair formula
(5.13) [fo:eq:pairs]. -/
theorem pairU_hasDerivAt (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (σ σ' : Bool) {r v : ℝ}
    (hr : r ∈ Set.Ioo (-1 : ℝ) 1) (hv : v ∈ Set.Ioo (-1 : ℝ) 1) (x y : Fin L) :
    HasDerivAt (fun r' => pairU (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) r' v σ σ' x y)
      (-(∑ c, pairU (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) r v σ σ' x c *
        (((gammaG g * W : ℝ) : ℂ) * primLoop g W L E m r ![c, y] ![σ, σ']))) r := by
  have _ := hv
  obtain ⟨hP, hrow, -⟩ := projField_P_facts g L hL E m hm
  simp_rw [projField_primLoop_two g W L hW E m r]
  set M := dysonMat (hopB g) (gammaG g) L E m with hMdef
  set P := pairP (gammaG g) M with hPdef
  set Q := pairQ (gammaG g) M with hQdef
  have hQrow : ∀ a, ∑ b, ‖Q a b‖ ≤ 1 := by
    intro a
    rw [← hrow a]
    refine le_of_eq (Finset.sum_congr rfl fun b _ => ?_)
    simp only [hQdef, hPdef, pairQ, pairP, Matrix.of_apply, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (projField_gamma_pos g)]
  have hPu : IsUnit (1 - r • P).det := projField_isUnit P hP hrow hr
  have hQu : (1 - (r : ℂ) • Q).det ≠ 0 := projField_det_ne Q hQrow (r : ℂ)
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; exact hr)
  have hPA : (1 - r • P) * (1 - r • P)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPu
  have hQA : (1 - (r : ℂ) • Q) * (1 - (r : ℂ) • Q)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hQu)
  have hPP : ∀ x y, ∑ c, propPP Q r v x c * (Q * (1 - (r : ℂ) • Q)⁻¹) c y =
      (Q * (1 - (v : ℂ) • Q)⁻¹) x y := by
    intro x y
    rw [← Matrix.mul_apply]
    unfold propPP
    rw [projField_prop_ker Q (r : ℂ) (v : ℂ) hQA]
  have hPM : ∀ x y, ∑ c, ((propPM P r v x c : ℝ) : ℂ) * ((mixedKer P r c y : ℝ) : ℂ) =
      (((P * (1 - v • P)⁻¹) x y : ℝ) : ℂ) := by
    intro x y
    rw [← projField_prop_ker P r v hPA, Matrix.mul_apply, Complex.ofReal_sum]
    simp only [Complex.ofReal_mul]
    rfl
  have hmix : HasDerivAt (fun r' => ((propPM P r' v x y : ℝ) : ℂ))
      (-∑ c, ((propPM P r v x c : ℝ) : ℂ) * ((mixedKer P r c y : ℝ) : ℂ)) r := by
    rw [hPM]
    convert projField_propPM_deriv P v r x y using 1
    push_cast
    simp
  have hpp : HasDerivAt (fun r' => propPP Q r' v x y)
      (-∑ c, propPP Q r v x c * (Q * (1 - (r : ℂ) • Q)⁻¹) c y) r := by
    rw [hPP]
    exact projField_propPP_deriv Q v r x y
  cases σ <;> cases σ'
  · have hmm := hpp.star
    simp only [pairU, pairK, ite_true, Bool.false_eq_true, ite_false, Matrix.map_apply]
    convert hmm using 1
    rw [star_neg, star_sum]
    simp only [star_mul']
    rfl
  · simpa [pairU, pairK] using hmix
  · simpa [pairU, pairK] using hmix
  · simpa [pairU, pairK] using hpp

/-- The projected error equation (C.35) [fo:eq:projected-error-equation] after exact propagation:
for a cyclically alternating word of length `n + 1`, the propagated projected loop error
`Σ_b coef_r(a, b) D_{n+1}(r; b)` with terminal time `v` has generator
`Σ_{b'} Π_j U_{a_j b'_j} [(𝒬_u F)(b') + C_u(h_u)(b')]` at time `u`, where `U = I + (v - u)K_v`,
`F` is the light insertion (5.7) [fo:eq:light] plus the cut sources of (5.17)
[fo:eq:error-hierarchy], `h_u` is the signed row of `D_{n+1}` and `C_u` is the commutator (6.4)
[gc:eq:commutator]. -/
theorem blockGen_projField (g E : ℝ) (m : ℂ) {W L n : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L) (hn : 1 ≤ n)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {u v : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1)
    (hv : v ∈ Set.Ioo (-1 : ℝ) 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hM : M.IsHermitian) (σ : Fin (n + 1) → Bool) (hσ : ∀ j, σ (finRotate (n + 1) j) = !σ j)
    (a : Fin (n + 1) → Fin L) :
    blockGen W L (gammaG g) (fun r N => ∑ b,
        projCoef (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v r a b *
          (resLoop g E m b σ r N - primLoop g W L E m r b σ)) u M =
      ∑ b, (∏ j, (((1 + (v - u) •
          mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v) (a j) (b j) : ℝ) : ℂ)) *
        (projQ (wardProfile (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) u)
            (fun b' => lightW g E m b' σ u M + ((gammaG g * W : ℝ) : ℂ) *
              (cutSrcLin (fun _ c τ => primLoop g W L E m u c τ)
                  (errFam g E m (fun _ c τ => primLoop g W L E m u c τ) u M) b' σ +
                cutSrcQuad (errFam g E m (fun _ c τ => primLoop g W L E m u c τ) u M) b' σ)) b +
          ∑ c, ((mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) u (b 0) c : ℝ) : ℂ) *
            rowSum (fun b' => resLoop g E m b' σ u M - primLoop g W L E m u b' σ) c *
            (∏ j : Fin n, ((wardProfile (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) u
                (c - b j.succ) : ℝ) : ℂ) -
              ∏ j : Fin n, ((wardProfile (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) u
                (b 0 - b j.succ) : ℝ) : ℂ))) := by
  have hT1 := (wardProfile_facts g L hL E m hm).1 u hu
  obtain ⟨hP, hrow, -⟩ := projField_P_facts g L hL E m hm
  set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) with hPdef
  have hUu : IsUnit (1 - u • P).det := projField_isUnit P hP hrow hu
  have hUv : IsUnit (1 - v • P).det := projField_isUnit P hP hrow hv
  have hA : (1 - u • P) * (1 - u • P)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hUu
  have hB : (1 - v • P) * (1 - v • P)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hUv
  have hUK : (1 + (v - u) • mixedKer P v) * mixedKer P u = mixedKer P v := by
    unfold mixedKer
    rw [← projField_prop_eq P u v hB, projField_prop_ker P u v hA]
  -- the leg derivative `∂_r U_r = -U_u K_u` at `r = u`
  have hleg : ∀ x y : Fin L, HasDerivAt
      (fun r => (((1 + (v - r) • mixedKer P v) x y : ℝ) : ℂ))
      (-(∑ c, (((1 + (v - u) • mixedKer P v) x c : ℝ) : ℂ) *
        ((1 : ℂ) * ((mixedKer P u c y : ℝ) : ℂ)))) u := by
    intro x y
    have h1 : HasDerivAt (fun r => (1 + (v - r) • mixedKer P v) x y) (-(mixedKer P v x y)) u := by
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact (((hasDerivAt_id u).const_sub v).mul_const (mixedKer P v x y)).const_add _
        |>.congr_deriv (by simp)
    have h2 : ∑ c, (((1 + (v - u) • mixedKer P v) x c : ℝ) : ℂ) *
        ((1 : ℂ) * ((mixedKer P u c y : ℝ) : ℂ)) = ((mixedKer P v x y : ℝ) : ℂ) := by
      calc _ = ((((1 + (v - u) • mixedKer P v) * mixedKer P u) x y : ℝ) : ℂ) := by
            rw [Matrix.mul_apply, Complex.ofReal_sum]
            simp only [one_mul, Complex.ofReal_mul]
        _ = _ := by rw [hUK]
    rw [h2]
    convert h1.ofReal_comp using 1
    simp
  -- the derivative of the propagator product
  have hprod : ∀ b' : Fin (n + 1) → Fin L, HasDerivAt
      (fun r => ∏ j, (((1 + (v - r) • mixedKer P v) (a j) (b' j) : ℝ) : ℂ))
      (∑ j, (∏ l ∈ Finset.univ.erase j,
          (((1 + (v - u) • mixedKer P v) (a l) (b' l) : ℝ) : ℂ)) •
        (-(∑ c, (((1 + (v - u) • mixedKer P v) (a j) c : ℝ) : ℂ) *
          ((1 : ℂ) * ((mixedKer P u c (b' j) : ℝ) : ℂ))))) u :=
    fun b' => HasDerivAt.fun_finsetProd fun j _ => hleg (a j) (b' j)
  -- the commutator identity at `u`
  have hKsym : ∀ x y, mixedKer P u x y = mixedKer P u y x := fun x y => (hT1 x y).1
  have hKrow : ∀ x, ∑ y, mixedKer P u x y = (1 - u)⁻¹ := projField_ker_row P hrow hu.2 hUu
  set Dfun : (Fin (n + 1) → Fin L) → ℂ :=
    fun b => resLoop g E m b σ u M - primLoop g W L E m u b σ with hDfun
  have hpc := fun b' => projection_commutator (n := n) (wardProfile P) (mixedKer P u) hu.2 hKsym
    hKrow (fun x y => (hT1 x y).2.2) Dfun b'
  choose Qd hQd hQeq using hpc
  -- the coefficients are differentiable at `u`
  have hcd := fun b => projField_projCoef_contDiffOn P hP hrow v a b
  have hw : ∀ b, HasDerivAt (fun r => projCoef P v r a b)
      (deriv (fun r => projCoef P v r a b) u) u := fun b =>
    (((hcd b).differentiableOn one_ne_zero u hu).differentiableAt
      (isOpen_Ioo.mem_nhds hu)).hasDerivAt
  have hD1 : HasDerivAt (fun r => ∑ b, projCoef P v r a b * Dfun b)
      (∑ b, deriv (fun r => projCoef P v r a b) u * Dfun b) u :=
    HasDerivAt.fun_sum fun b _ => (hw b).mul_const (Dfun b)
  have hfun : (fun r => ∑ b, projCoef P v r a b * Dfun b) = fun r =>
      ∑ b', (∏ j, (((1 + (v - r) • mixedKer P v) (a j) (b' j) : ℝ) : ℂ)) *
        projQ (wardProfile P r) Dfun b' := funext fun r => projField_coef_sum P v r a Dfun
  rw [hfun] at hD1
  have hD2 := HasDerivAt.fun_sum (u := Finset.univ) fun b' _ => (hprod b').mul (hQd b')
  have hderiv := hD1.unique hD2
  -- the generator of each loop error
  have hprim := projField_primDeriv g W L hW hL E m hm u hu
  have hsm := fun b : Fin (n + 1) → Fin L => projField_smooth g E m hm.1 hu.2 hM (W := W) b σ
  have hE : ∀ b : Fin (n + 1) → Fin L,
      blockGen W L (gammaG g) (fun r N => resLoop g E m b σ r N - primLoop g W L E m r b σ) u M =
        (lightW g E m b σ u M + ((gammaG g * W : ℝ) : ℂ) *
          (cutSrcLin (fun _ c τ => primLoop g W L E m u c τ)
              (errFam g E m (fun _ c τ => primLoop g W L E m u c τ) u M) b σ +
            cutSrcQuad (errFam g E m (fun _ c τ => primLoop g W L E m u c τ) u M) b σ)) +
          thetaK (mixedKer P u) Dfun b := by
    intro b
    have h1 := blockGen_errorLoop g E m hm.1 hu.2 hM _ hprim b σ
    have h2 := cutErr_split (gammaG g) W (by omega : 2 ≤ n + 1)
      (fun n c τ => primLoop g W L E m u (k := n) c τ)
      (errFam g E m (fun n c τ => primLoop g W L E m u (k := n) c τ) u M)
      (fun x y s t => primLoop_two_swap g W L E m u x y s t) b σ
    have h3 : thetaOp (gammaG g) W (fun n c τ => primLoop g W L E m u (k := n) c τ)
        (errFam g E m (fun n c τ => primLoop g W L E m u (k := n) c τ) u M) b σ =
        thetaK (mixedKer P u) Dfun b := by
      unfold thetaOp thetaK
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← mul_assoc, hσ j, projField_primLoop_two g W L hW E m u]
      cases σ j <;> simp [pairK, hPdef, errFam, hDfun, resLoop]
    rw [h1, h2, h3]
    ring
  refine (projField_blockGen_sum (gammaG g) (fun b r => projCoef P v r a b)
    (fun b => deriv (fun r => projCoef P v r a b) u)
    (fun b r N => resLoop g E m b σ r N - primLoop g W L E m r b σ) u M hw
    (fun b => (hsm b).1.sub (hprim (n + 1) b σ).differentiableAt)
    (fun b c κ => ⟨fun e => (((hsm b).2 c κ).1 e).sub_const _, by
      rw [deriv_sub_const_fun]; exact ((hsm b).2 c κ).2⟩)).trans ?_
  simp only [hE]
  rw [Finset.sum_add_distrib]
  have e1 : ∑ x, deriv (fun r => projCoef P v r a x) u *
      (resLoop g E m x σ u M - primLoop g W L E m u x σ) =
      ∑ b, deriv (fun r => projCoef P v r a b) u * Dfun b := rfl
  rw [e1, hderiv, projField_coef_sum P v u a]
  simp only [projField_projQ_add]
  have hC := projField_theta_cancel 1 a
    (fun _ x y => (((1 + (v - u) • mixedKer P v) x y : ℝ) : ℂ))
    (fun _ x y => ((mixedKer P u x y : ℝ) : ℂ)) (projQ (wardProfile P u) Dfun)
  beta_reduce at hC
  rw [← sub_eq_zero, ← hC, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hq := hQeq b
  simp only [thetaK] at hq ⊢
  linear_combination (∏ j, (((1 + (v - u) • mixedKer P v) (a j) (b j) : ℝ) : ℂ)) * hq

/-- The bracket (5.9) [gc:eq:bracket] of the propagated projected loop error:
`Γ = Σ_{b, b'} Π_j U_{a_j b_j} Π_j U_{a_j b'_j} ((𝒬_r ⊗ 𝒬_r) 𝒱)(b, b')` with
`𝒱(c, c') = Γ(ℒ(c), ℒ(c'))` and `U = I + (v - r)K_v`, for any real kernel `P`. -/
theorem blockGamma_projField (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L n : ℕ}
    (P : Matrix (Fin L) (Fin L) ℝ) {r v : ℝ} (hr : r < 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Fin L) :
    blockGamma W L (gammaG g)
        (fun N => ∑ b, projCoef P v r a b * (resLoop g E m b σ r N - primLoop g W L E m r b σ))
        (fun N => ∑ b, projCoef P v r a b * (resLoop g E m b σ r N - primLoop g W L E m r b σ)) M =
      ∑ b, ∑ b', (∏ j, (((1 + (v - r) • mixedKer P v) (a j) (b j) : ℝ) : ℂ)) *
        (∏ j, (((1 + (v - r) • mixedKer P v) (a j) (b' j) : ℝ) : ℂ)) *
        projQ (wardProfile P r) (fun c => projQ (wardProfile P r)
          (fun c' => blockGamma W L (gammaG g) (resLoop g E m c σ r) (resLoop g E m c' σ r) M) b') b := by
  have hsm := fun b : Fin (n + 1) → Fin L => projField_smooth g E m hm hr hM (W := W) b σ
  have hdiff : ∀ (b : Fin (n + 1) → Fin L) (c : Fin L) (κ : Fin W × Fin W), DifferentiableAt ℝ
      (fun e : ℝ => (fun N => resLoop g E m b σ r N - primLoop g W L E m r b σ)
        (M + (e : ℂ) • blockBasis W L c κ)) 0 :=
    fun b c κ => (((hsm b).2 c κ).1 0).sub_const _
  rw [blockGamma_tensor (gammaG g) _ _ _ _ M hdiff hdiff]
  set V : (Fin (n + 1) → Fin L) → (Fin (n + 1) → Fin L) → ℂ :=
    fun c c' => blockGamma W L (gammaG g) (resLoop g E m c σ r) (resLoop g E m c' σ r) M with hV
  have hG : ∀ b b', blockGamma W L (gammaG g)
      (fun N => resLoop g E m b σ r N - primLoop g W L E m r b σ)
      (fun N => resLoop g E m b' σ r N - primLoop g W L E m r b' σ) M = V b b' := by
    intro b b'
    simp only [hV, blockGamma, deriv_sub_const]
  simp only [hG, projField_star_coef]
  set U : (Fin (n + 1) → Fin L) → ℂ :=
    fun b => ∏ j, (((1 + (v - r) • mixedKer P v) (a j) (b j) : ℝ) : ℂ) with hU
  have h1 : ∀ b, ∑ b', projCoef P v r a b * projCoef P v r a b' * V b b' =
      projCoef P v r a b * ∑ b', U b' * projQ (wardProfile P r) (V b) b' := by
    intro b
    rw [← projField_coef_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b' _ => by ring
  simp only [h1]
  rw [projField_coef_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [projField_projQ_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b' _ => by ring

/-- The propagated projected loop error lies in the heat class on every time window `(a', b')`
with `-1 < a'` and `b' < 1`. -/
theorem heatClass_projField (g E : ℝ) (m : ℂ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {n : ℕ} (σ : Fin (n + 1) → Bool)
    (a : Fin (n + 1) → Fin L) {v a' b' : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) (ha' : -1 < a')
    (hb' : b' < 1) :
    HeatClass (fun r x => ∑ b,
      projCoef (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v r a b *
        loopErrField g E m W L b σ r x) a' b' := by
  have _ := hv
  obtain ⟨hP, hrow, -⟩ := projField_P_facts g L hL E m hm
  exact projField_heat_sum Finset.univ _ fun b _ =>
    (projField_heat_time _ (projField_projCoef_contDiffOn _ hP hrow v a b) ha' hb').mul
      (heatClass_loopErrField g E m W L hW hL hm b σ ha' hb')

/-- The loop error propagated by `U^{σ_jσ_{j+1}}_{r,v}` of (5.15) [fo:eq:propagators] lies in the
heat class on every time window `(a', b')` with `-1 < a'` and `b' < 1`. -/
theorem heatClass_propField (g E : ℝ) (m : ℂ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Fin L)
    {v a' b' : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) (ha' : -1 < a') (hb' : b' < 1) :
    HeatClass (fun r x => ∑ b : Fin k → Fin L,
      (∏ j, pairU (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) r v (σ j) (σ (finRotate k j))
        (a j) (b j)) * loopErrField g E m W L b σ r x) a' b' := by
  have _ := hv
  exact projField_heat_sum Finset.univ _ fun b _ =>
    (projField_heat_time _ (contDiffOn_prod fun j _ =>
        (projField_pairU_contDiff _ _ v _ _ (a j) (b j)).contDiffOn) ha' hb').mul
      (heatClass_loopErrField g E m W L hW hL hm b σ ha' hb')

end LSBA
