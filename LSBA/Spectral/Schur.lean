import LSBA.Spectral.ResolventBounds

/-!
# One-index Schur formulas

The minor `H^{(i)}`, the column `h_i`, and the Schur formulas for the diagonal and off-diagonal
resolvent entries of any matrix (Appendix G.1 [app:relative-local-law-proof]).
-/

open scoped Matrix

noncomputable section
open scoped Classical

namespace LSBA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The minor `H^{(i)}` (row and column `i` deleted), Appendix G.1
[app:relative-local-law-proof]. -/
def minorMat (H : Matrix ι ι ℂ) (i : ι) : Matrix {k // k ≠ i} {k // k ≠ i} ℂ :=
  H.submatrix Subtype.val Subtype.val

/-- The column `h_i = (H_{ki})_{k ≠ i}`, Appendix G.1 [app:relative-local-law-proof]. -/
def minorCol (H : Matrix ι ι ℂ) (i : ι) : {k // k ≠ i} → ℂ := fun k => H k.1 i

/-- The centred quadratic form `h_i^* G^{(i)} h_i - n⁻¹ Tr G^{(i)}`, `n = #ι`, of Appendix G.1
[app:relative-local-law-proof]. -/
def schurQuadDev (H : Matrix ι ι ℂ) (z : ℂ) (i : ι) : ℂ :=
  star (minorCol H i) ⬝ᵥ (resolventMat (minorMat H i) z *ᵥ minorCol H i) -
    (Fintype.card ι : ℂ)⁻¹ * (resolventMat (minorMat H i) z).trace

/-- Schur's formula `G_ii = (H_ii - z - h_i^* G^{(i)} h_i)⁻¹`, Appendix G.1
[app:relative-local-law-proof]. -/
theorem resolventMat_diag_schur {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (i : ι) :
    resolventMat H z i i =
      (H i i - z - star (minorCol H i) ⬝ᵥ (resolventMat (minorMat H i) z *ᵥ minorCol H i))⁻¹ := by
  have hM : (minorMat H i).IsHermitian := hH.submatrix _
  have hAG := sub_smul_mul_resolventMat hH hz.ne'
  have hDG := sub_smul_mul_resolventMat hM hz.ne'
  have hGD := mul_eq_one_comm.mp hDG
  have hsplit : ∀ f : ι → ℂ, ∑ l, f l = f i + ∑ k : {k // k ≠ i}, f k.1 :=
    fun f => Fintype.sum_eq_add_sum_subtype_ne f i
  have hDe : ∀ k l : {k // k ≠ i},
      (minorMat H i - z • (1 : Matrix {k // k ≠ i} {k // k ≠ i} ℂ)) k l =
        (H - z • (1 : Matrix ι ι ℂ)) k.1 l.1 := by
    intro k l
    by_cases h : k = l
    · subst h; simp [minorMat]
    · have : k.1 ≠ l.1 := fun e => h (Subtype.ext e)
      simp [minorMat, h, this]
  obtain ⟨G, hG⟩ : ∃ G, G = resolventMat H z := ⟨_, rfl⟩
  obtain ⟨Gm, hGm⟩ : ∃ Gm, Gm = resolventMat (minorMat H i) z := ⟨_, rfl⟩
  rw [← hG] at hAG ⊢
  rw [← hGm] at hDG hGD ⊢
  -- the column `v = (G_{ki})_{k ≠ i}` satisfies `D v = -G_ii h`
  have hDv : (minorMat H i - z • (1 : Matrix {k // k ≠ i} {k // k ≠ i} ℂ)) *ᵥ
      (fun p : {k // k ≠ i} => G p.1 i) = -(G i i) • minorCol H i := by
    funext k
    have h1 := congrFun (congrFun hAG k.1) i
    rw [Matrix.mul_apply, hsplit, Matrix.one_apply_ne k.2] at h1
    have h2 : (H - z • (1 : Matrix ι ι ℂ)) k.1 i = H k.1 i := by
      simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne k.2]
    rw [h2] at h1
    simp only [Matrix.mulVec, dotProduct, hDe, Pi.smul_apply, smul_eq_mul, minorCol]
    linear_combination h1
  have hv : (fun p : {k // k ≠ i} => G p.1 i) = -(G i i) • (Gm *ᵥ minorCol H i) := by
    have : (fun p : {k // k ≠ i} => G p.1 i) = (Gm * (minorMat H i -
        z • (1 : Matrix {k // k ≠ i} {k // k ≠ i} ℂ))) *ᵥ (fun p : {k // k ≠ i} => G p.1 i) := by
      rw [hGD, Matrix.one_mulVec]
    rw [this, ← Matrix.mulVec_mulVec, hDv, Matrix.mulVec_smul]
  have h1 := congrFun (congrFun hAG i) i
  rw [Matrix.mul_apply, hsplit, Matrix.one_apply_eq] at h1
  have hAii : (H - z • (1 : Matrix ι ι ℂ)) i i = H i i - z := by simp
  have hAil : ∀ l : {k // k ≠ i}, (H - z • (1 : Matrix ι ι ℂ)) i l.1 = star (minorCol H i l) := by
    intro l
    have : (H - z • (1 : Matrix ι ι ℂ)) i l.1 = H i l.1 := by
      simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne l.2.symm]
    rw [this, minorCol]
    exact (hH.apply i l.1).symm
  have hsum : ∑ l : {k // k ≠ i}, (H - z • (1 : Matrix ι ι ℂ)) i l.1 * G l.1 i =
      -(G i i * (star (minorCol H i) ⬝ᵥ (Gm *ᵥ minorCol H i))) := by
    have : ∑ l : {k // k ≠ i}, (H - z • (1 : Matrix ι ι ℂ)) i l.1 * G l.1 i =
        star (minorCol H i) ⬝ᵥ (fun p : {k // k ≠ i} => G p.1 i) := by
      simp only [dotProduct, hAil, Pi.star_apply]
    rw [this, hv, dotProduct_smul, smul_eq_mul]
    ring
  rw [hAii, hsum] at h1
  have hne : H i i - z - star (minorCol H i) ⬝ᵥ (Gm *ᵥ minorCol H i) ≠ 0 := by
    intro h0
    have : G i i * (H i i - z - star (minorCol H i) ⬝ᵥ (Gm *ᵥ minorCol H i)) = 1 := by
      linear_combination h1
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  exact eq_inv_of_mul_eq_one_left (by linear_combination h1)

/-- The off-diagonal Schur formula `G_ij = -G_ii Σ_{k ≠ i} H_ik G^{(i)}_kj` of
(G.4) [us:eq:weighted-offdiagonal-law]. -/
theorem resolventMat_offdiag_schur {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) {i j : ι} (hji : j ≠ i) :
    resolventMat H z i j =
      -(resolventMat H z i i *
        ∑ k : {k // k ≠ i}, H i k.1 * resolventMat (minorMat H i) z k ⟨j, hji⟩) := by
  have hM : (minorMat H i).IsHermitian := hH.submatrix _
  have hAG := sub_smul_mul_resolventMat hH hz.ne'
  have hGA := mul_eq_one_comm.mp hAG
  have hDG := sub_smul_mul_resolventMat hM hz.ne'
  have hsplit : ∀ f : ι → ℂ, ∑ l, f l = f i + ∑ k : {k // k ≠ i}, f k.1 :=
    fun f => Fintype.sum_eq_add_sum_subtype_ne f i
  have hDe : ∀ k l : {k // k ≠ i},
      (minorMat H i - z • (1 : Matrix {k // k ≠ i} {k // k ≠ i} ℂ)) k l =
        (H - z • (1 : Matrix ι ι ℂ)) k.1 l.1 := by
    intro k l
    by_cases h : k = l
    · subst h; simp [minorMat]
    · have : k.1 ≠ l.1 := fun e => h (Subtype.ext e)
      simp [minorMat, h, this]
  obtain ⟨G, hG⟩ : ∃ G, G = resolventMat H z := ⟨_, rfl⟩
  obtain ⟨Gm, hGm⟩ : ∃ Gm, Gm = resolventMat (minorMat H i) z := ⟨_, rfl⟩
  rw [← hG] at hGA ⊢
  rw [← hGm] at hDG ⊢
  -- row `w = (G_{ik})_{k ≠ i}` satisfies `w D = -G_ii (H_il)_l`
  have hwD : ∀ l : {k // k ≠ i}, ∑ k : {k // k ≠ i}, G i k.1 *
      (minorMat H i - z • (1 : Matrix {k // k ≠ i} {k // k ≠ i} ℂ)) k l = -(G i i * H i l.1) := by
    intro l
    have h1 := congrFun (congrFun hGA i) l.1
    rw [Matrix.mul_apply, hsplit, Matrix.one_apply_ne l.2.symm] at h1
    have h2 : (H - z • (1 : Matrix ι ι ℂ)) i l.1 = H i l.1 := by
      simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne l.2.symm]
    rw [h2] at h1
    simp only [hDe]
    linear_combination h1
  have h3 : G i j = ∑ m : {k // k ≠ i}, G i m.1 *
      ((minorMat H i - z • (1 : Matrix {k // k ≠ i} {k // k ≠ i} ℂ)) * Gm) m ⟨j, hji⟩ := by
    rw [hDG]
    simp [Matrix.one_apply]
  rw [h3]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h4 : ∀ k : {k // k ≠ i}, ∑ m : {k // k ≠ i}, G i m.1 *
      ((minorMat H i - z • (1 : Matrix {k // k ≠ i} {k // k ≠ i} ℂ)) m k * Gm k ⟨j, hji⟩) =
        -(G i i * H i k.1) * Gm k ⟨j, hji⟩ := by
    intro k
    have := hwD k
    calc _ = (∑ m : {k // k ≠ i}, G i m.1 *
          (minorMat H i - z • (1 : Matrix {k // k ≠ i} {k // k ≠ i} ℂ)) m k) * Gm k ⟨j, hji⟩ := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by ring
      _ = _ := by rw [this]
  rw [Finset.sum_congr rfl fun k _ => h4 k]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

end LSBA
