import LSBA.Spectral.ResolventBounds

/-!
# The deformed scalar Dyson map

The normalized trace, the trial profile `M_q = (−B − z − q)⁻¹`, the scalar map `q ↦ ⟨M_q⟩` and its
Herglotz roots for a Hermitian deformation `B` (Appendix A.16 [app:deformed-dyson]); the Ward-type
identity behind (A.84) [da:eq:deformed-vector-weight], `|m| < 1` and uniqueness of the root.
-/

open scoped Matrix

noncomputable section
open scoped Classical

namespace LSBA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The normalized trace `⟨X⟩ = n⁻¹ Tr X`, `n = #ι`, of Lemma A.21 [da:lem:deformed]. -/
def ntr (X : Matrix ι ι ℂ) : ℂ := (Fintype.card ι : ℂ)⁻¹ * X.trace

/-- The trial profile `M_q = (-B - z - q)⁻¹`; at `z = E + iη` it is the matrix
`(-E I - B - iη - q)⁻¹` of (A.83) [da:eq:deformed-residual-stability]. -/
def deformedMat (B : Matrix ι ι ℂ) (z q : ℂ) : Matrix ι ι ℂ := resolventMat (-B) (z + q)

/-- The scalar Dyson map `q ↦ ⟨M_q⟩` of (A.83) [da:eq:deformed-residual-stability]. -/
def deformedMap (B : Matrix ι ι ℂ) (z q : ℂ) : ℂ := ntr (deformedMat B z q)

/-- `m` is a Herglotz solution of `m = ⟨(-B - z - m)⁻¹⟩`, Lemma A.21 [da:lem:deformed]. -/
def IsDeformedRoot (B : Matrix ι ι ℂ) (z m : ℂ) : Prop := 0 < m.im ∧ m = deformedMap B z m

/-- The Hilbert–Schmidt sum `∑ ij |G_ij|²` of a matrix. -/
private def deformedMap_sqsum (G : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖G i j‖ ^ 2

omit [DecidableEq ι] in
private lemma deformedMap_trace_conjTranspose_mul_self (G : Matrix ι ι ℂ) :
    (Gᴴ * G).trace = ((deformedMap_sqsum G : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    deformedMap_sqsum, Complex.ofReal_sum, Complex.ofReal_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact Complex.conj_mul' _

/-- Ward's identity for the trial profile. -/
private lemma deformedMap_ward {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z q : ℂ}
    (hw : 0 < (z + q).im) :
    (deformedMat B z q)ᴴ * deformedMat B z q =
      ((2 * (z + q).im * Complex.I)⁻¹ : ℂ) • (deformedMat B z q - (deformedMat B z q)ᴴ) :=
  ward_matrix hB.neg hw.ne'

private lemma deformedMap_sqsum_mul {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z q : ℂ}
    (hw : 0 < (z + q).im) :
    deformedMap_sqsum (deformedMat B z q) * (z + q).im = (deformedMat B z q).trace.im := by
  have h := congrArg Matrix.trace (deformedMap_ward hB hw)
  rw [deformedMap_trace_conjTranspose_mul_self, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_conjTranspose, smul_eq_mul] at h
  set t := (deformedMat B z q).trace
  have hw' : ((z + q).im : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have h2 : t - star t = 2 * (t.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simp
    · simp; ring
  rw [h2] at h
  have h3 : ((deformedMap_sqsum (deformedMat B z q) * (z + q).im : ℝ) : ℂ) = (t.im : ℂ) := by
    push_cast
    rw [h]
    field_simp
  exact_mod_cast h3

omit [DecidableEq ι] in
private lemma deformedMap_norm_trace_sq_le (G : Matrix ι ι ℂ) :
    ‖G.trace‖ ^ 2 ≤ (Fintype.card ι : ℝ) * deformedMap_sqsum G := by
  have h1 : ‖G.trace‖ ≤ ∑ i, ‖G i i‖ := norm_sum_le _ _
  have h2 : (∑ i, ‖G i i‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖G i i‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => ‖G i i‖)
    simpa using this
  have h3 : ∑ i, ‖G i i‖ ^ 2 ≤ deformedMap_sqsum G :=
    Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun j => ‖G i j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  calc ‖G.trace‖ ^ 2 ≤ (∑ i, ‖G i i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
    _ ≤ _ := by gcongr

omit [DecidableEq ι] in
/-- `|tr (G G')|² ≤ (∑ |G|²)(∑ |G'|²)`. -/
private lemma deformedMap_norm_trace_mul_sq_le (G G' : Matrix ι ι ℂ) :
    ‖(G * G').trace‖ ^ 2 ≤ deformedMap_sqsum G * deformedMap_sqsum G' := by
  have h1 : ‖(G * G').trace‖ ≤ ∑ i, ∑ j, ‖G i j‖ * ‖G' j i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  have h2 : (∑ i, ∑ j, ‖G i j‖ * ‖G' j i‖) ^ 2 ≤
      deformedMap_sqsum G * deformedMap_sqsum G' := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
      (fun p => ‖G p.1 p.2‖) (fun p => ‖G' p.2 p.1‖)
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at this
    have e : ∑ i, ∑ j, ‖G' j i‖ ^ 2 = deformedMap_sqsum G' := Finset.sum_comm
    rw [e] at this
    exact this
  calc ‖(G * G').trace‖ ^ 2 ≤ (∑ i, ∑ j, ‖G i j‖ * ‖G' j i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- For a Herglotz root `m`: `n > 0`, `Tr M_m = n m` and `∑ |M_m,ij|² = n Im m / (Im z + Im m)`. -/
private lemma deformedMap_root_aux {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z m : ℂ}
    (hz : 0 < z.im) (hm : IsDeformedRoot B z m) :
    0 < (Fintype.card ι : ℝ) ∧ (deformedMat B z m).trace = (Fintype.card ι : ℂ) * m ∧
      deformedMap_sqsum (deformedMat B z m) =
        (Fintype.card ι : ℝ) * (m.im / (z.im + m.im)) := by
  obtain ⟨him, hfix⟩ := hm
  have hw : 0 < (z + m).im := by rw [Complex.add_im]; linarith
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := by
    intro h0
    have : m = 0 := by rw [hfix]; simp [deformedMap, ntr, h0]
    rw [this] at him
    simp at him
  have hcardR : 0 < (Fintype.card ι : ℝ) := by
    have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hcard
    exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm this)
  have htr : (deformedMat B z m).trace = (Fintype.card ι : ℂ) * m := by
    have h := hfix
    simp only [deformedMap, ntr] at h
    calc (deformedMat B z m).trace
        = (Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ)⁻¹ * (deformedMat B z m).trace) := by
          field_simp
      _ = (Fintype.card ι : ℂ) * m := by rw [← h]
  refine ⟨hcardR, htr, ?_⟩
  have h1 := deformedMap_sqsum_mul hB hw
  rw [htr] at h1
  have himn : ((Fintype.card ι : ℂ) * m).im = (Fintype.card ι : ℝ) * m.im := by
    rw [show (Fintype.card ι : ℂ) = ((Fintype.card ι : ℝ) : ℂ) by simp, Complex.im_ofReal_mul]
  rw [himn, Complex.add_im] at h1
  have hw' : z.im + m.im ≠ 0 := by linarith
  field_simp
  linarith

/-- `v^* Im M_q v = Im(z + q) ‖M_q v‖²` for Hermitian `B`, the identity behind
(A.84) [da:eq:deformed-vector-weight]. -/
theorem im_dotProduct_deformedMat {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z q : ℂ}
    (hzq : 0 < (z + q).im) (v : ι → ℂ) :
    (star v ⬝ᵥ (deformedMat B z q *ᵥ v)).im =
      (z + q).im * ∑ i, ‖(deformedMat B z q *ᵥ v) i‖ ^ 2 := by
  set G := deformedMat B z q with hG
  have hw' : ((z + q).im : ℂ) ≠ 0 := by exact_mod_cast hzq.ne'
  have hS : ((∑ i, ‖(G *ᵥ v) i‖ ^ 2 : ℝ) : ℂ) = star (G *ᵥ v) ⬝ᵥ (G *ᵥ v) := by
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    exact Finset.sum_congr rfl fun i _ => (Complex.conj_mul' _).symm
  set s := star v ⬝ᵥ (G *ᵥ v) with hs
  have h1 : star (G *ᵥ v) ⬝ᵥ (G *ᵥ v) = star v ⬝ᵥ ((Gᴴ * G) *ᵥ v) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have h2 : star v ⬝ᵥ (Gᴴ *ᵥ v) = star s := by
    rw [hs, ← Matrix.star_dotProduct, Matrix.star_mulVec, Matrix.dotProduct_mulVec]
  have h3 : star (G *ᵥ v) ⬝ᵥ (G *ᵥ v) =
      ((2 * (z + q).im * Complex.I)⁻¹ : ℂ) * (s - star s) := by
    rw [h1, deformedMap_ward hB hzq, Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul,
      dotProduct_sub, h2, smul_eq_mul]
  have h4 : s - star s = 2 * (s.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simp
    · simp; ring
  rw [h3, h4] at hS
  have : (((z + q).im * ∑ i, ‖(G *ᵥ v) i‖ ^ 2 : ℝ) : ℂ) = (s.im : ℂ) := by
    push_cast at hS ⊢
    rw [hS]
    field_simp
  exact_mod_cast this.symm

/-- Every Herglotz solution has `|m| < 1`; the first half of
(A.82) [da:eq:deformed-scalar-stability], for every Hermitian `B`. -/
theorem IsDeformedRoot.norm_lt_one {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z m : ℂ}
    (hz : 0 < z.im) (hm : IsDeformedRoot B z m) : ‖m‖ < 1 := by
  obtain ⟨hn, htr, hsq⟩ := deformedMap_root_aux hB hz hm
  have him := hm.1
  have hle := deformedMap_norm_trace_sq_le (deformedMat B z m)
  rw [htr, hsq, norm_mul, Complex.norm_natCast] at hle
  have hr1 : m.im / (z.im + m.im) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have hm2 : ‖m‖ ^ 2 ≤ m.im / (z.im + m.im) := by
    have : (Fintype.card ι : ℝ) ^ 2 * ‖m‖ ^ 2 ≤
        (Fintype.card ι : ℝ) ^ 2 * (m.im / (z.im + m.im)) := by
      nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [norm_nonneg m]

/-- The Herglotz solution of Lemma A.21 [da:lem:deformed] is unique, for every Hermitian `B`. -/
theorem IsDeformedRoot.unique {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z m m' : ℂ}
    (hz : 0 < z.im) (hm : IsDeformedRoot B z m) (hm' : IsDeformedRoot B z m') : m = m' := by
  obtain ⟨hn, htr, hsq⟩ := deformedMap_root_aux hB hz hm
  obtain ⟨-, htr', hsq'⟩ := deformedMap_root_aux hB hz hm'
  have him := hm.1
  have him' := hm'.1
  set G := deformedMat B z m with hG
  set G' := deformedMat B z m' with hG'
  have hX : (-B - (z + m) • (1 : Matrix ι ι ℂ)) * G = 1 :=
    sub_smul_mul_resolventMat hB.neg (by simp; linarith)
  have hX' : (-B - (z + m') • (1 : Matrix ι ι ℂ)) * G' = 1 :=
    sub_smul_mul_resolventMat hB.neg (by simp; linarith)
  have hGX : G * (-B - (z + m) • (1 : Matrix ι ι ℂ)) = 1 := mul_eq_one_comm.mp hX
  have hdiff : G - G' = (m - m') • (G * G') := by
    have e : (-B - (z + m') • (1 : Matrix ι ι ℂ)) - (-B - (z + m) • (1 : Matrix ι ι ℂ)) =
        (m - m') • (1 : Matrix ι ι ℂ) := by
      rw [sub_smul, add_smul, add_smul]; abel_nf
    have h1 : G * (-B - (z + m') • (1 : Matrix ι ι ℂ)) * G' = G := by
      rw [Matrix.mul_assoc, hX', Matrix.mul_one]
    have h2 : G * (-B - (z + m) • (1 : Matrix ι ι ℂ)) * G' = G' := by
      rw [hGX, Matrix.one_mul]
    calc G - G' = G * (-B - (z + m') • (1 : Matrix ι ι ℂ)) * G'
          - G * (-B - (z + m) • (1 : Matrix ι ι ℂ)) * G' := by rw [h1, h2]
      _ = G * ((-B - (z + m') • (1 : Matrix ι ι ℂ)) -
            (-B - (z + m) • (1 : Matrix ι ι ℂ))) * G' := by
          rw [← sub_mul, ← mul_sub]
      _ = (m - m') • (G * G') := by rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have htrace := congrArg Matrix.trace hdiff
  rw [Matrix.trace_sub, Matrix.trace_smul, htr, htr', smul_eq_mul] at htrace
  by_contra hne
  have hne' : m - m' ≠ 0 := sub_ne_zero.mpr hne
  have hT : (G * G').trace = (Fintype.card ι : ℂ) := by
    apply mul_left_cancel₀ hne'
    rw [← htrace]; ring
  have hle := deformedMap_norm_trace_mul_sq_le G G'
  rw [hT, hsq, hsq', Complex.norm_natCast] at hle
  have hr : m.im / (z.im + m.im) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hr' : m'.im / (z.im + m'.im) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hr0 : 0 < m.im / (z.im + m.im) := div_pos him (by linarith)
  have hr0' : 0 < m'.im / (z.im + m'.im) := div_pos him' (by linarith)
  have hprod : m.im / (z.im + m.im) * (m'.im / (z.im + m'.im)) < 1 := by nlinarith
  have hn2 : 0 < (Fintype.card ι : ℝ) ^ 2 := by positivity
  nlinarith

end LSBA
