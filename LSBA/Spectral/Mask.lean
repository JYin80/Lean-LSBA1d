import Mathlib

/-!
# Masked matrices

For a set `S` of indices, `maskMat S X` keeps the entries of `X` on `S × S`, is the identity on
`Sᶜ × Sᶜ` and vanishes on the two cross blocks. Its inverse on `S × S` is the inverse of the
restriction `X_{SS}`, which is how the resolvents (8.1) [up:eq:local-resolvent] of the
restricted operators `H_Λ` of Section 8.1 [sec:fr-concentration] are realized on the full index
type. Deleting
a subset `T ⊆ S` gives the resolvent identity of one deletion step and the Schur complement on `T`.
-/

open Finset
open scoped Matrix

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `maskMat S X`: the entries of `X` on `S × S`, the identity on `Sᶜ × Sᶜ`, and `0` on the cross
blocks. -/
def maskMat (S : Set n) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  Matrix.of fun p q => if p ∈ S ∧ q ∈ S then X p q else if p = q then 1 else 0

/-- No index is masked when `S` is everything. -/
theorem maskMat_univ (X : Matrix n n ℂ) : maskMat Set.univ X = X := by
  ext p q
  simp [maskMat]

/-- Masking preserves the Hermitian property. -/
theorem maskMat_isHermitian {X : Matrix n n ℂ} (hX : X.IsHermitian) (S : Set n) :
    (maskMat S X).IsHermitian := by
  ext p q
  simp only [Matrix.conjTranspose_apply, maskMat, Matrix.of_apply]
  by_cases hp : p ∈ S <;> by_cases hq : q ∈ S
  · simp [hp, hq, hX.apply]
  · simp [hp, hq, eq_comm]
  · simp [hp, hq, eq_comm]
  · simp [hp, hq, eq_comm]

/-- If a matrix `Y` is block diagonal for `S, Sᶜ`, agrees with `X` on `S × S` and is invertible,
then `maskMat S X` is invertible (both determinants contain the factor `det X_{SS}`). -/
theorem det_maskMat_ne_zero_of_blockDiag {S : Set n} {X Y : Matrix n n ℂ}
    (hY₁ : ∀ p q, p ∈ S → q ∉ S → Y p q = 0) (hY₂ : ∀ p q, p ∉ S → q ∈ S → Y p q = 0)
    (hYX : ∀ p q, p ∈ S → q ∈ S → Y p q = X p q) (hY : Y.det ≠ 0) :
    (maskMat S X).det ≠ 0 := by
  have hprod : Y = maskMat S X * maskMat Sᶜ Y := by
    ext p q
    rw [Matrix.mul_apply]
    by_cases hp : p ∈ S
    · rw [Finset.sum_eq_single q]
      · by_cases hq : q ∈ S
        · simp [maskMat, hp, hq, hYX p q hp hq]
        · have hpq : p ≠ q := fun h => hq (h ▸ hp)
          simp [maskMat, hp, hq, hY₁ p q hp hq, hpq]
      · intro k _ hk
        by_cases hkS : k ∈ S
        · simp [maskMat, hkS, hk]
        · have hpk : p ≠ k := fun h => hkS (h ▸ hp)
          simp [maskMat, hp, hkS, hpk]
      · simp
    · rw [Finset.sum_eq_single p]
      · by_cases hq : q ∈ S
        · have hpq : p ≠ q := fun h => hp (h ▸ hq)
          simp [maskMat, hp, hq, hY₂ p q hp hq, hpq]
        · simp [maskMat, hp, hq]
      · intro k _ hk
        simp [maskMat, hp, Ne.symm hk]
      · simp
  intro h0
  apply hY
  rw [hprod, Matrix.det_mul, h0, zero_mul]

omit [Fintype n] in
private theorem maskMat_apply_of_not_mem_left {S : Set n} (X : Matrix n n ℂ) {p : n}
    (hp : p ∉ S) (q : n) : maskMat S X p q = if p = q then 1 else 0 := by
  simp [maskMat, hp]

omit [Fintype n] in
private theorem maskMat_apply_of_not_mem_right {S : Set n} (X : Matrix n n ℂ) (p : n) {q : n}
    (hq : q ∉ S) : maskMat S X p q = if p = q then 1 else 0 := by
  simp [maskMat, hq]

omit [Fintype n] in
private theorem maskMat_apply_of_mem {S : Set n} (X : Matrix n n ℂ) {p q : n} (hp : p ∈ S)
    (hq : q ∈ S) : maskMat S X p q = X p q := by
  simp [maskMat, hp, hq]

/-- An invertible `maskMat S X` has an inverse with identity rows outside `S`. -/
private theorem maskMat_inv_apply_left {S : Set n} {X : Matrix n n ℂ}
    (h : (maskMat S X).det ≠ 0) {p : n} (hp : p ∉ S) (q : n) :
    (maskMat S X)⁻¹ p q = if p = q then 1 else 0 := by
  have h1 : maskMat S X * (maskMat S X)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h)
  have h2 := congrFun (congrFun h1 p) q
  rw [Matrix.mul_apply] at h2
  simp only [maskMat_apply_of_not_mem_left X hp] at h2
  simpa [Matrix.one_apply] using h2

/-- An invertible `maskMat S X` has an inverse with identity columns outside `S`. -/
private theorem maskMat_inv_apply_right {S : Set n} {X : Matrix n n ℂ}
    (h : (maskMat S X).det ≠ 0) (p : n) {q : n} (hq : q ∉ S) :
    (maskMat S X)⁻¹ p q = if p = q then 1 else 0 := by
  have h1 : (maskMat S X)⁻¹ * maskMat S X = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)
  have h2 := congrFun (congrFun h1 p) q
  rw [Matrix.mul_apply] at h2
  simp only [maskMat_apply_of_not_mem_right X _ hq] at h2
  simpa [Matrix.one_apply] using h2

/-- One deletion step (the second resolvent identity): for `T ⊆ S`, `p ∈ T` and `q ∈ S ∖ T`, if
`maskMat S X` and `maskMat (S ∖ T) X` are invertible, then
`(M_S⁻¹)_{pq} = -Σ_{r ∈ T, s ∈ S ∖ T} (M_S⁻¹)_{pr} X_{rs} (M_{S∖T}⁻¹)_{sq}`. -/
theorem maskMat_inv_delete {S T : Set n} (hTS : T ⊆ S) (X : Matrix n n ℂ)
    (hS : (maskMat S X).det ≠ 0) (hST : (maskMat (S \ T) X).det ≠ 0) {p q : n} (hp : p ∈ T)
    (hq : q ∈ S \ T) :
    (maskMat S X)⁻¹ p q = -∑ r, ∑ s, if r ∈ T ∧ s ∈ S \ T then
      (maskMat S X)⁻¹ p r * X r s * (maskMat (S \ T) X)⁻¹ s q else 0 := by
  have hMu : IsUnit (maskMat S X).det := isUnit_iff_ne_zero.mpr hS
  have hNu : IsUnit (maskMat (S \ T) X).det := isUnit_iff_ne_zero.mpr hST
  have hres : (maskMat (S \ T) X)⁻¹ - (maskMat S X)⁻¹ =
      (maskMat S X)⁻¹ * (maskMat S X - maskMat (S \ T) X) * (maskMat (S \ T) X)⁻¹ := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hMu, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hNu, Matrix.mul_one]
  have hpq : p ≠ q := fun h => hq.2 (h ▸ hp)
  have hNpq : (maskMat (S \ T) X)⁻¹ p q = 0 := by
    rw [maskMat_inv_apply_left hST (fun h : p ∈ S \ T => h.2 hp) q]
    simp [hpq]
  have hentry := congrFun (congrFun hres p) q
  rw [Matrix.sub_apply, hNpq] at hentry
  have hterm : ∀ r s, (maskMat S X)⁻¹ p r * (maskMat S X - maskMat (S \ T) X) r s *
      (maskMat (S \ T) X)⁻¹ s q = if r ∈ T ∧ s ∈ S \ T then
        (maskMat S X)⁻¹ p r * X r s * (maskMat (S \ T) X)⁻¹ s q else 0 := by
    intro r s
    by_cases hs : s ∈ S \ T
    · by_cases hr : r ∈ T
      · have hrs : r ≠ s := fun h => hs.2 (h ▸ hr)
        have h1 : maskMat S X r s = X r s := maskMat_apply_of_mem X (hTS hr) hs.1
        have h2 : maskMat (S \ T) X r s = 0 := by
          rw [maskMat_apply_of_not_mem_left X (fun h : r ∈ S \ T => h.2 hr)]
          simp [hrs]
        simp [hr, hs, h1, h2]
      · have hsub : (maskMat S X - maskMat (S \ T) X) r s = 0 := by
          rw [Matrix.sub_apply, sub_eq_zero]
          by_cases hrS : r ∈ S
          · rw [maskMat_apply_of_mem X hrS hs.1,
              maskMat_apply_of_mem (S := S \ T) X ⟨hrS, hr⟩ hs]
          · have hrs : r ≠ s := fun h => hrS (h ▸ hs.1)
            rw [maskMat_apply_of_not_mem_left X hrS,
              maskMat_apply_of_not_mem_left X (fun h : r ∈ S \ T => hrS h.1)]
        simp [hr, hsub]
    · have hsq : s ≠ q := fun h => hs (h ▸ hq)
      have h3 : (maskMat (S \ T) X)⁻¹ s q = 0 := by
        rw [maskMat_inv_apply_left hST hs q]
        simp [hsq]
      simp [hs, h3]
  have hsum : ((maskMat S X)⁻¹ * (maskMat S X - maskMat (S \ T) X) *
      (maskMat (S \ T) X)⁻¹) p q = ∑ r, ∑ s, if r ∈ T ∧ s ∈ S \ T then
        (maskMat S X)⁻¹ p r * X r s * (maskMat (S \ T) X)⁻¹ s q else 0 := by
    rw [Matrix.mul_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => hterm r s
  rw [hsum] at hentry
  linear_combination -hentry

/-- The entries of `Y` on `U × V`, and `0` elsewhere. -/
private def blockMat (U V : Set n) (Y : Matrix n n ℂ) : Matrix n n ℂ :=
  Matrix.of fun r s => if r ∈ U ∧ s ∈ V then Y r s else 0

omit [Fintype n] [DecidableEq n] in
private theorem blockMat_support {U V : Set n} {Y : Matrix n n ℂ} {r s : n}
    (h : blockMat U V Y r s ≠ 0) : r ∈ U ∧ s ∈ V := by
  by_contra hc
  exact h (by simp [blockMat, hc])

omit [Fintype n] in
private theorem maskMat_eq_one_add (S : Set n) (Y : Matrix n n ℂ) :
    maskMat S Y = 1 + blockMat S S (Y - 1) := by
  ext r s
  by_cases h : r ∈ S ∧ s ∈ S
  · simp [maskMat, blockMat, h, Matrix.one_apply]
  · simp [maskMat, blockMat, h, Matrix.one_apply]

omit [DecidableEq n] in
/-- A product of matrices whose supports do not meet vanishes. -/
private theorem mul_eq_zero_of_support {U V : Set n} {Y Y' : Matrix n n ℂ}
    (hY : ∀ r k, Y r k ≠ 0 → k ∈ U) (hY' : ∀ k c, Y' k c ≠ 0 → k ∈ V)
    (hUV : ∀ k, k ∈ U → k ∉ V) : Y * Y' = 0 := by
  ext r c
  rw [Matrix.mul_apply]
  refine (Finset.sum_eq_zero fun k _ => ?_).trans (by simp)
  by_cases h : Y r k = 0
  · simp [h]
  · by_cases h' : Y' k c = 0
    · simp [h']
    · exact absurd (hY' k c h') (hUV k (hY r k h))

/-- Multiplying on the right by a matrix with identity rows on `U` fixes matrices whose columns
lie in `U`. -/
private theorem mul_eq_self_of_rows {U : Set n} {Y J : Matrix n n ℂ}
    (hY : ∀ r k, Y r k ≠ 0 → k ∈ U) (hJ : ∀ k ∈ U, ∀ c, J k c = if k = c then 1 else 0) :
    Y * J = Y := by
  ext r c
  rw [Matrix.mul_apply]
  have h : ∀ k, Y r k * J k c = Y r k * (if k = c then 1 else 0) := by
    intro k
    by_cases h : Y r k = 0
    · simp [h]
    · rw [hJ k (hY r k h) c]
  simp [h]

/-- Multiplying on the left by a matrix with identity columns on `U` fixes matrices whose rows
lie in `U`. -/
private theorem mul_eq_self_of_cols {U : Set n} {Y J : Matrix n n ℂ}
    (hY : ∀ k c, Y k c ≠ 0 → k ∈ U) (hJ : ∀ k ∈ U, ∀ s, J s k = if s = k then 1 else 0) :
    J * Y = Y := by
  ext s c
  rw [Matrix.mul_apply]
  have h : ∀ k, J s k * Y k c = (if s = k then 1 else 0) * Y k c := by
    intro k
    by_cases h : Y k c = 0
    · simp [h]
    · rw [hJ k (hY k c h) s]
  simp [h]

omit [DecidableEq n] in
private theorem blockMat_mul_mul (T A : Set n) (X B : Matrix n n ℂ) (r s : n) :
    (blockMat T A X * B * blockMat A T X) r s = if r ∈ T ∧ s ∈ T then
      ∑ u, ∑ w, if u ∈ A ∧ w ∈ A then X r u * B u w * X w s else 0 else 0 := by
  by_cases hr : r ∈ T
  · by_cases hs : s ∈ T
    · simp only [Matrix.mul_apply, blockMat, Matrix.of_apply, hr, hs, true_and, and_true,
        Finset.sum_mul, ite_true]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
      by_cases hu : u ∈ A <;> by_cases hw : w ∈ A <;> simp [hu, hw]
    · simp [Matrix.mul_apply, blockMat, hs]
  · simp [Matrix.mul_apply, blockMat, hr]

private theorem maskMat_eq_decomp {S T : Set n} (hTS : T ⊆ S) (X B : Matrix n n ℂ) :
    maskMat S X = maskMat (S \ T) X + blockMat T T ((Matrix.of fun r s => X r s - ∑ u, ∑ w,
      if u ∈ S \ T ∧ w ∈ S \ T then X r u * B u w * X w s else 0) - 1) +
      blockMat T (S \ T) X + blockMat (S \ T) T X +
      blockMat T (S \ T) X * B * blockMat (S \ T) T X := by
  have key : ∀ r, (r ∈ T ∧ r ∈ S) ∨ (r ∉ T ∧ r ∈ S) ∨ (r ∉ T ∧ r ∉ S) := fun r => by
    by_cases h : r ∈ T
    · exact Or.inl ⟨h, hTS h⟩
    · by_cases h' : r ∈ S
      · exact Or.inr (Or.inl ⟨h, h'⟩)
      · exact Or.inr (Or.inr ⟨h, h'⟩)
  ext r s
  simp only [Matrix.add_apply]
  rw [blockMat_mul_mul]
  simp only [maskMat, blockMat, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply,
    Set.mem_sdiff]
  have h1 : r ∈ S → s ∉ S → r ≠ s := fun h h' e => h' (e ▸ h)
  have h2 : r ∉ S → s ∈ S → r ≠ s := fun h h' e => h (e ▸ h')
  have h3 : r ∈ T → s ∉ T → r ≠ s := fun h h' e => h' (e ▸ h)
  have h4 : r ∉ T → s ∈ T → r ≠ s := fun h h' e => h (e ▸ h')
  rcases key r with ⟨hrT, hrS⟩ | ⟨hrT, hrS⟩ | ⟨hrT, hrS⟩ <;>
    rcases key s with ⟨hsT, hsS⟩ | ⟨hsT, hsS⟩ | ⟨hsT, hsS⟩ <;>
    simp [hrT, hrS, hsT, hsS, h1, h2, h3, h4]

/-- The factorization of the inverse behind the Schur complement. -/
private theorem inv_apply_eq_of_factor {T A : Set n} (hTA : ∀ k, k ∈ T → k ∉ A)
    {M Ma B Z W E : Matrix n n ℂ} (hMaB : Ma * B = 1)
    (hBr : ∀ k, k ∉ A → ∀ c, B k c = if k = c then 1 else 0)
    (hBc : ∀ k, k ∉ A → ∀ s, B s k = if s = k then 1 else 0)
    (hZ : ∀ r s, Z r s ≠ 0 → r ∈ T ∧ s ∈ A) (hW : ∀ r s, W r s ≠ 0 → r ∈ A ∧ s ∈ T)
    (hE : ∀ r s, E r s ≠ 0 → r ∈ T ∧ s ∈ T) (hM : M = Ma + E + Z + W + Z * B * W)
    {p q : n} (hp : p ∈ T) (hq : q ∈ T) : M⁻¹ p q = (1 + E)⁻¹ p q := by
  have hEB : E * B = E :=
    mul_eq_self_of_rows (U := Aᶜ) (fun r k h => hTA k (hE r k h).2) hBr
  have hBE : B * E = E :=
    mul_eq_self_of_cols (U := Aᶜ) (fun k c h => hTA k (hE k c h).1) hBc
  have hBZ : B * Z = Z :=
    mul_eq_self_of_cols (U := Aᶜ) (fun k c h => hTA k (hZ k c h).1) hBc
  have hWB : W * B = W :=
    mul_eq_self_of_rows (U := Aᶜ) (fun r k h => hTA k (hW r k h).2) hBr
  have hZE : Z * E = 0 :=
    mul_eq_zero_of_support (U := A) (V := T) (fun r k h => (hZ r k h).2)
      (fun k c h => (hE k c h).1) (fun k hk h => hTA k h hk)
  have hEW : E * W = 0 :=
    mul_eq_zero_of_support (U := T) (V := A) (fun r k h => (hE r k h).2)
      (fun k c h => (hW k c h).1) hTA
  have hZZ : Z * Z = 0 :=
    mul_eq_zero_of_support (U := A) (V := T) (fun r k h => (hZ r k h).2)
      (fun k c h => (hZ k c h).1) (fun k hk h => hTA k h hk)
  have hWW : W * W = 0 :=
    mul_eq_zero_of_support (U := T) (V := A) (fun r k h => (hW r k h).2)
      (fun k c h => (hW k c h).1) hTA
  have hPP : (Z * B) * (Z * B) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc B Z B, hBZ, ← Matrix.mul_assoc, hZZ,
      Matrix.zero_mul]
  have hQQ : (B * W) * (B * W) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc W B W, hWB, hWW, Matrix.mul_zero]
  have hMQ : M * (1 - B * W) * B = (1 + Z * B) * (1 + E) := by
    have h1 : M * (B * W) = W + Z * B * W := by
      have a1 : Ma * (B * W) = W := by rw [← Matrix.mul_assoc, hMaB, Matrix.one_mul]
      have a2 : E * (B * W) = 0 := by rw [← Matrix.mul_assoc, hEB, hEW]
      have a3 : Z * (B * W) = Z * B * W := by rw [Matrix.mul_assoc]
      have a4 : W * (B * W) = 0 := by rw [← Matrix.mul_assoc, hWB, hWW]
      have a5 : Z * B * W * (B * W) = 0 := by
        rw [Matrix.mul_assoc (Z * B) W (B * W), a4, Matrix.mul_zero]
      rw [hM]
      simp only [Matrix.add_mul]
      rw [a1, a2, a3, a4, a5]
      abel
    have h2 : M * (1 - B * W) = Ma + E + Z := by
      rw [Matrix.mul_sub, Matrix.mul_one, h1, hM]
      abel
    have h3 : (Ma + E + Z) * B = 1 + E + Z * B := by
      rw [Matrix.add_mul, Matrix.add_mul, hMaB, hEB]
    have h4 : Z * B * E = 0 := by rw [Matrix.mul_assoc, hBE, hZE]
    rw [h2, h3]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h4]
    abel
  have hIB : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hMaB
  have h5 : (1 - B * W) * (1 + B * W) = 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hQQ]
    abel
  have h6 : (1 - Z * B) * (1 + Z * B) = 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  by_cases hN : (1 + E).det = 0
  · have hMu : ¬ IsUnit M.det := by
      intro hMu
      have hN' : 1 + E = (1 - Z * B) * (M * (1 - B * W) * B) := by
        rw [hMQ, ← Matrix.mul_assoc, h6, Matrix.one_mul]
      have hu1 := Matrix.isUnit_det_of_right_inverse h5
      have hu2 := Matrix.isUnit_det_of_right_inverse h6
      have hdet : IsUnit (1 + E).det := by
        rw [hN', Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
        exact hu2.mul ((hMu.mul hu1).mul hIB)
      exact (hN ▸ hdet).ne_zero rfl
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hMu,
      Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hN]; exact not_isUnit_zero)]
  · have hNu : IsUnit (1 + E).det := isUnit_iff_ne_zero.mpr hN
    have h7 : (1 + Z * B) * (1 - Z * B) = 1 := by
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
      abel
    have hK : M * ((1 - B * W) * B * (1 + E)⁻¹ * (1 - Z * B)) = 1 := by
      calc M * ((1 - B * W) * B * (1 + E)⁻¹ * (1 - Z * B))
          = (M * (1 - B * W) * B) * (1 + E)⁻¹ * (1 - Z * B) := by simp only [Matrix.mul_assoc]
        _ = (1 + Z * B) * (1 + E) * (1 + E)⁻¹ * (1 - Z * B) := by rw [hMQ]
        _ = (1 + Z * B) * (1 - Z * B) := by
          rw [Matrix.mul_assoc (1 + Z * B), Matrix.mul_nonsing_inv _ hNu, Matrix.mul_one]
        _ = 1 := h7
    rw [Matrix.inv_eq_right_inv hK]
    have hpA : p ∉ A := hTA p hp
    have hqA : q ∉ A := hTA q hq
    have hWp : ∀ k, W p k = 0 := fun k => by
      by_contra h
      exact hpA (hW p k h).1
    have hZq : ∀ k, Z k q = 0 := fun k => by
      by_contra h
      exact hqA (hZ k q h).2
    have hrow1 : ∀ c, ((1 - B * W) * ((B * ((1 + E)⁻¹ * (1 - Z * B))))) p c =
        (B * ((1 + E)⁻¹ * (1 - Z * B))) p c := by
      intro c
      rw [Matrix.mul_apply]
      have h : ∀ k, (1 - B * W) p k = if p = k then 1 else 0 := fun k => by
        rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply]
        simp [hBr p hpA, hWp]
      simp [h]
    have hrow2 : ∀ c, (B * ((1 + E)⁻¹ * (1 - Z * B))) p c =
        ((1 + E)⁻¹ * (1 - Z * B)) p c := by
      intro c
      rw [Matrix.mul_apply]
      simp [hBr p hpA]
    have hcol : ((1 + E)⁻¹ * (1 - Z * B)) p q = (1 + E)⁻¹ p q := by
      rw [Matrix.mul_apply]
      have h : ∀ k, (1 - Z * B) k q = if k = q then 1 else 0 := fun k => by
        rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply]
        simp [hBc q hqA, hZq]
      simp [h]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hrow1, hrow2, hcol]

/-- The Schur complement on `T ⊆ S`: if `maskMat (S ∖ T) X` is invertible, the `T × T` entries of
`(maskMat S X)⁻¹` are those of the inverse of `maskMat T (X - Σ)`, where
`Σ_{rs} = Σ_{u, w ∈ S ∖ T} X_{ru} (M_{S∖T}⁻¹)_{uw} X_{ws}`. -/
theorem maskMat_inv_schur {S T : Set n} (hTS : T ⊆ S) (X : Matrix n n ℂ)
    (hST : (maskMat (S \ T) X).det ≠ 0) {p q : n} (hp : p ∈ T) (hq : q ∈ T) :
    (maskMat S X)⁻¹ p q = (maskMat T (Matrix.of fun r s => X r s - ∑ u, ∑ w,
      if u ∈ S \ T ∧ w ∈ S \ T then X r u * (maskMat (S \ T) X)⁻¹ u w * X w s else 0))⁻¹ p q := by
  have hMaB : maskMat (S \ T) X * (maskMat (S \ T) X)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hST)
  rw [inv_apply_eq_of_factor (T := T) (A := S \ T) (fun k hk h => h.2 hk) hMaB
    (fun k hk c => maskMat_inv_apply_left hST hk c)
    (fun k hk s => maskMat_inv_apply_right hST s hk)
    (fun r s h => blockMat_support h) (fun r s h => blockMat_support h)
    (fun r s h => blockMat_support h) (maskMat_eq_decomp hTS X _) hp hq,
    ← maskMat_eq_one_add]

end LSBA
