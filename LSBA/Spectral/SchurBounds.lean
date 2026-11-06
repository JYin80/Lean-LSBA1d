import LSBA.Spectral.Schur

/-!
# Bounds from the Schur formulas

`|G_ii| ≤ (η + Im h*G^{(i)}h)⁻¹` and `|Tr G − Tr G^{(i)}| ≤ η⁻¹` without interlacing (Appendix G.1
[app:relative-local-law-proof]).
-/

open scoped Matrix

noncomputable section
open scoped Classical

namespace LSBA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `(G(z))* = G(z̄)` for Hermitian `A`. -/
private lemma schurBounds_conjTranspose {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (z : ℂ) :
    (resolventMat A z)ᴴ = resolventMat A (star z) := by
  unfold resolventMat
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, hA.eq,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one]

/-- `G G* = (G - G*) / (2 i Im z)`, the second half of the matrix Ward identity. -/
private lemma schurBounds_ward_mul_conjTranspose {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    resolventMat A z * (resolventMat A z)ᴴ =
      ((2 * z.im * Complex.I)⁻¹ : ℂ) • (resolventMat A z - (resolventMat A z)ᴴ) := by
  have hz' : (star z).im ≠ 0 := by simpa using hz
  have h := ward_matrix hA hz'
  rw [← schurBounds_conjTranspose hA z, Matrix.conjTranspose_conjTranspose] at h
  rw [h, ← neg_sub, smul_neg, ← neg_smul]
  congr 1
  simp [inv_neg, mul_neg, neg_mul]

omit [DecidableEq ι] in
/-- `Σ_k |(M u)_k|² = u* M* M u`, as a complex number. -/
private lemma schurBounds_sumsq_eq (M : Matrix ι ι ℂ) (u : ι → ℂ) :
    ((∑ k, ‖(M *ᵥ u) k‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ ((Mᴴ * M) *ᵥ u) := by
  have e : ((∑ k, ‖(M *ᵥ u) k‖ ^ 2 : ℝ) : ℂ) = star (M *ᵥ u) ⬝ᵥ (M *ᵥ u) := by
    push_cast
    simp only [dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  rw [e, Matrix.star_mulVec, Matrix.dotProduct_mulVec (star u) (Mᴴ * M) u,
    ← Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec]

/-- `u* (c (G - G*)) u = Im(u* G u) / Im z` for `c = (2 i Im z)⁻¹`. -/
private lemma schurBounds_quad {A : Matrix ι ι ℂ} {z : ℂ} (hz : z.im ≠ 0) (u : ι → ℂ) :
    star u ⬝ᵥ ((((2 * z.im * Complex.I)⁻¹ : ℂ) •
        (resolventMat A z - (resolventMat A z)ᴴ)) *ᵥ u) =
      (((star u ⬝ᵥ (resolventMat A z *ᵥ u)).im / z.im : ℝ) : ℂ) := by
  set G := resolventMat A z with hG
  have hstar : star u ⬝ᵥ (Gᴴ *ᵥ u) = star (star u ⬝ᵥ (G *ᵥ u)) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply, star_sum,
      star_mul', star_star, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul, dotProduct_sub, hstar]
  set q := star u ⬝ᵥ (G *ᵥ u) with hq
  have hc : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz
  have : q - star q = ((2 * q.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [two_mul]
  rw [smul_eq_mul, this]
  push_cast
  field_simp

/-- `Σ_k |(G u)_k|² = Im(u* G u) / Im z`. -/
private lemma schurBounds_sumsq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (u : ι → ℂ) :
    ∑ k, ‖(resolventMat A z *ᵥ u) k‖ ^ 2 =
      (star u ⬝ᵥ (resolventMat A z *ᵥ u)).im / z.im := by
  apply Complex.ofReal_injective
  rw [schurBounds_sumsq_eq, ward_matrix hA hz, schurBounds_quad hz]

/-- `Σ_k |(G* u)_k|² = Im(u* G u) / Im z`. -/
private lemma schurBounds_sumsq' {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (u : ι → ℂ) :
    ∑ k, ‖((resolventMat A z)ᴴ *ᵥ u) k‖ ^ 2 =
      (star u ⬝ᵥ (resolventMat A z *ᵥ u)).im / z.im := by
  apply Complex.ofReal_injective
  rw [schurBounds_sumsq_eq, Matrix.conjTranspose_conjTranspose,
    schurBounds_ward_mul_conjTranspose hA hz, schurBounds_quad hz]

/-- The block of `G` away from `i`: `G_kj = G^{(i)}_kj + G_ii (G^{(i)} h)_k (h* G^{(i)})_j`. -/
private lemma schurBounds_block {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (i : ι) (k j : {k // k ≠ i}) :
    resolventMat H z k.1 j.1 = resolventMat (minorMat H i) z k j +
      resolventMat H z i i * ((resolventMat (minorMat H i) z *ᵥ minorCol H i) k *
        (star (minorCol H i) ᵥ* resolventMat (minorMat H i) z) j) := by
  have hM : (minorMat H i).IsHermitian := hH.submatrix _
  have hAG := sub_smul_mul_resolventMat hH hz.ne'
  have hDG := sub_smul_mul_resolventMat hM hz.ne'
  have hGD := mul_eq_one_comm.mp hDG
  have hoff := resolventMat_offdiag_schur hH hz (i := i) (j := j.1) j.2
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
  have hHs : ∀ x : {k // k ≠ i}, H i x.1 = star (minorCol H i x) := fun x =>
    (hH.apply i x.1).symm
  obtain ⟨G, hG⟩ : ∃ G, G = resolventMat H z := ⟨_, rfl⟩
  obtain ⟨Gm, hGm⟩ : ∃ Gm, Gm = resolventMat (minorMat H i) z := ⟨_, rfl⟩
  rw [← hG] at hAG hoff ⊢
  rw [← hGm] at hDG hGD hoff ⊢
  set D := minorMat H i - z • (1 : Matrix {k // k ≠ i} {k // k ≠ i} ℂ) with hD
  set Gb : Matrix {k // k ≠ i} {k // k ≠ i} ℂ := Matrix.of fun a b => G a.1 b.1 with hGb
  have hrow : ∀ m l : {k // k ≠ i}, (D * Gb) m l =
      (1 : Matrix {k // k ≠ i} {k // k ≠ i} ℂ) m l - H m.1 i * G i l.1 := by
    intro m l
    have h1 := congrFun (congrFun hAG m.1) l.1
    rw [Matrix.mul_apply, hsplit] at h1
    have h2 : (H - z • (1 : Matrix ι ι ℂ)) m.1 i = H m.1 i := by
      simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne m.2]
    have h3 : (1 : Matrix ι ι ℂ) m.1 l.1 = (1 : Matrix {k // k ≠ i} {k // k ≠ i} ℂ) m l := by
      simp [Matrix.one_apply, Subtype.ext_iff]
    rw [h2, h3] at h1
    simp only [Matrix.mul_apply, hGb, Matrix.of_apply, hDe]
    linear_combination h1
  have hGbeq : Gb = Gm * (D * Gb) := by rw [← Matrix.mul_assoc, hGD, Matrix.one_mul]
  have hkj : G k.1 j.1 = Gm k j - (∑ m : {k // k ≠ i}, Gm k m * H m.1 i) * G i j.1 := by
    have h := congrFun (congrFun hGbeq k) j
    have hl : Gb k j = G k.1 j.1 := rfl
    rw [hl] at h
    rw [h, Matrix.mul_apply]
    simp only [hrow]
    simp only [mul_sub, Finset.sum_sub_distrib, Matrix.one_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Finset.sum_mul]
    refine congrArg (Gm k j - ·) (Finset.sum_congr rfl fun m _ => by ring)
  rw [hkj, hoff]
  have e1 : (∑ m : {k // k ≠ i}, Gm k m * H m.1 i) = (Gm *ᵥ minorCol H i) k := by
    simp [Matrix.mulVec, dotProduct, minorCol]
  have e2 : (∑ x : {k // k ≠ i}, H i x.1 * Gm x j) = (star (minorCol H i) ᵥ* Gm) j := by
    simp only [Matrix.vecMul, dotProduct, hHs, Pi.star_apply]
  rw [e1, e2]
  ring

/-- `Im h_i^* G^{(i)} h_i ≥ 0` and `|G_ii| ≤ (η + Im h_i^* G^{(i)} h_i)⁻¹`, `η = Im z`,
from Schur's formula of Appendix G.1 [app:relative-local-law-proof]. -/
theorem norm_resolventMat_diag_le_schur {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (i : ι) :
    0 ≤ (star (minorCol H i) ⬝ᵥ (resolventMat (minorMat H i) z *ᵥ minorCol H i)).im ∧
      ‖resolventMat H z i i‖ ≤
        (z.im + (star (minorCol H i) ⬝ᵥ
          (resolventMat (minorMat H i) z *ᵥ minorCol H i)).im)⁻¹ := by
  have hM : (minorMat H i).IsHermitian := hH.submatrix _
  have hs := schurBounds_sumsq hM hz.ne' (minorCol H i)
  set Q := star (minorCol H i) ⬝ᵥ (resolventMat (minorMat H i) z *ᵥ minorCol H i) with hQ
  have hQim : Q.im = z.im * ∑ k, ‖(resolventMat (minorMat H i) z *ᵥ minorCol H i) k‖ ^ 2 := by
    rw [hs]; field_simp
  have hQ0 : 0 ≤ Q.im := by rw [hQim]; positivity
  refine ⟨hQ0, ?_⟩
  rw [resolventMat_diag_schur hH hz i, norm_inv]
  have hHii : (H i i).im = 0 := by
    have := hH.apply i i
    rw [Complex.star_def] at this
    exact Complex.conj_eq_iff_im.mp this
  have hw : z.im + Q.im ≤ ‖H i i - z - Q‖ := by
    have h1 := Complex.abs_im_le_norm (H i i - z - Q)
    have h2 : (H i i - z - Q).im = -(z.im + Q.im) := by
      simp [hHii]; ring
    rw [h2, abs_neg, abs_of_nonneg (by linarith)] at h1
    exact h1
  exact inv_anti₀ (by linarith) hw

/-- `|Tr G - Tr G^{(i)}| ≤ η⁻¹`, `η = Im z`, without interlacing; the trace comparison of
Appendix G.1 [app:relative-local-law-proof]. -/
theorem norm_trace_resolventMat_sub_minor_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (i : ι) :
    ‖(resolventMat H z).trace - (resolventMat (minorMat H i) z).trace‖ ≤ z.im⁻¹ := by
  have hM : (minorMat H i).IsHermitian := hH.submatrix _
  obtain ⟨hQ0, hdiag⟩ := norm_resolventMat_diag_le_schur hH hz i
  set Gm := resolventMat (minorMat H i) z with hGm
  set h := minorCol H i with hh
  set Q := star h ⬝ᵥ (Gm *ᵥ h) with hQ
  set a : {k // k ≠ i} → ℂ := Gm *ᵥ h with ha
  set r : {k // k ≠ i} → ℂ := star h ᵥ* Gm with hr
  set X : ℝ := Q.im / z.im with hX
  have hηpos : 0 < z.im := hz
  have hsa : ∑ k, ‖a k‖ ^ 2 = X := schurBounds_sumsq hM hz.ne' h
  have hrstar : r = star (Gmᴴ *ᵥ h) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  have hsr : ∑ k, ‖r k‖ ^ 2 = X := by
    have := schurBounds_sumsq' hM hz.ne' h
    rw [hrstar]
    simp only [Pi.star_apply, norm_star]
    exact this
  -- trace identity
  have htr : (resolventMat H z).trace - Gm.trace =
      resolventMat H z i i * (1 + ∑ k, a k * r k) := by
    have hsplit : ∑ l, resolventMat H z l l =
        resolventMat H z i i + ∑ k : {k // k ≠ i}, resolventMat H z k.1 k.1 :=
      Fintype.sum_eq_add_sum_subtype_ne (fun l => resolventMat H z l l) i
    simp only [Matrix.trace, Matrix.diag_apply]
    rw [hsplit]
    have hb : ∀ k : {k // k ≠ i}, resolventMat H z k.1 k.1 =
        Gm k k + resolventMat H z i i * (a k * r k) := fun k =>
      schurBounds_block hH hz i k k
    rw [Finset.sum_congr rfl fun k _ => hb k, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hS : ‖∑ k, a k * r k‖ ≤ X := by
    calc ‖∑ k, a k * r k‖ ≤ ∑ k, ‖a k * r k‖ := norm_sum_le _ _
      _ ≤ ∑ k, (‖a k‖ ^ 2 + ‖r k‖ ^ 2) / 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul]
          nlinarith [sq_nonneg (‖a k‖ - ‖r k‖)]
      _ = X := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, hsa, hsr]; ring
  have hX0 : 0 ≤ X := div_nonneg hQ0 hz.le
  have hpos : 0 < z.im + Q.im := by linarith
  rw [htr, norm_mul]
  calc ‖resolventMat H z i i‖ * ‖1 + ∑ k, a k * r k‖
      ≤ (z.im + Q.im)⁻¹ * (1 + X) := by
        refine mul_le_mul hdiag ?_ (norm_nonneg _) (inv_nonneg.mpr hpos.le)
        calc ‖1 + ∑ k, a k * r k‖ ≤ ‖(1 : ℂ)‖ + ‖∑ k, a k * r k‖ := norm_add_le _ _
          _ ≤ 1 + X := by rw [norm_one]; linarith
    _ = z.im⁻¹ := by
        rw [hX]
        field_simp

end LSBA
