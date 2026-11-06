import LSBA.Loop.Basic
import LSBA.Spectral.ResolventBounds

/-!
# The mixed Ward identity for resolvent loops

The ℒ half of Lemma 5.1 [fo:lem:mixed-ward]: summing the label between two opposite signs merges
them, `Σ_c ℒ_k(…, c; …) = (2i)⁻¹W⁻¹η⁻¹[ℒ_{k−1}(merged +) − ℒ_{k−1}(merged −)]`, for both orders of
the two signs (the numerator does not change sign), for every Hermitian matrix and every `z` with
`Im z > 0`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The conjugate transpose of the resolvent at `z` is the resolvent at `z̄`. -/
private lemma ward_conjTranspose_resolventMat {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} :
    (resolventMat A z)ᴴ = resolventMat A (star z) := by
  unfold resolventMat
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hA.eq]

/-- The two products `G* G` and `G G*` of a resolvent factor and its conjugate coincide with
`(G - G*) / (2iη)`; this is the form of Ward's identity that combines two adjacent factors. -/
private lemma ward_sgnMat_mul {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (s : Bool) :
    sgnMat (resolventMat A z) (!s) * sgnMat (resolventMat A z) s =
      ((2 * z.im * Complex.I)⁻¹ : ℂ) • (resolventMat A z - (resolventMat A z)ᴴ) := by
  cases s
  · have h := ward_matrix hA (z := star z) (by simpa using hz)
    rw [← ward_conjTranspose_resolventMat hA, Matrix.conjTranspose_conjTranspose] at h
    have him : (star z).im = -z.im := rfl
    rw [him] at h
    simp only [sgnMat, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    rw [h, ← neg_sub, smul_neg, ← neg_smul]
    congr 1
    rw [Complex.ofReal_neg]
    simp only [mul_neg, neg_mul, inv_neg, neg_neg]
  · simpa [sgnMat] using ward_matrix hA hz

/-- The sum of the normalized block projections over all blocks is `W⁻¹` times the identity. -/
private lemma ward_sum_blockE (W L : ℕ) :
    ∑ c : Fin L, blockE W L c = (W : ℂ)⁻¹ • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) := by
  ext p q
  simp only [blockE, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases h : p = q
  · subst h
    simp
  · simp [h]

/-- Splitting off the first factor of a loop of length `m + 1`. -/
private lemma ward_loopTr_succ {W L m : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin (m + 1) → Fin L) (σ : Fin (m + 1) → Bool) :
    loopTr X a σ =
      ((sgnMat X (σ 0) * blockE W L (a 0)) *
        (List.ofFn fun i : Fin m => sgnMat X (σ i.succ) * blockE W L (a i.succ)).prod).trace := by
  unfold loopTr
  rw [List.ofFn_succ, List.prod_cons]

/-- Splitting off the last factor of a loop of length `k + 1` whose last label and sign are
appended with `Fin.snoc`. -/
private lemma ward_loopTr_snoc {W L k : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin k → Fin L) (c : Fin L) (σ : Fin k → Bool) (t : Bool) :
    loopTr X (Fin.snoc a c : Fin (k + 1) → Fin L) (Fin.snoc σ t : Fin (k + 1) → Bool) =
      ((List.ofFn fun i : Fin k => sgnMat X (σ i) * blockE W L (a i)).prod *
        (sgnMat X t * blockE W L c)).trace := by
  unfold loopTr
  rw [List.ofFn_succ', List.prod_concat]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- Lemma 5.1 [fo:lem:mixed-ward] for `𝒳 = ℒ`, (5.11) [gc:eq:ward], in the order-independent form:
for every Hermitian `H` and `Im z > 0`, the sum over the label between the signs `!s` (last
position) and `s` (first position) is `(2iWη)⁻¹[ℒ(merged +) - ℒ(merged -)]`, `η = Im z`, for both
values of `s`. -/
theorem loopTr_ward {W L : ℕ} (hW : 1 ≤ W) (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) (k : ℕ) (hk : 1 ≤ k) (a : Fin k → Fin L)
    (τ : Fin k → Bool) (s : Bool) :
    ∑ c : Fin L, loopTr (resolventMat H z) (Fin.snoc a c : Fin (k + 1) → Fin L)
        (Fin.snoc (Function.update τ ⟨0, hk⟩ s) (!s) : Fin (k + 1) → Bool) =
      ((2 * Complex.I * (W : ℂ) * (z.im : ℂ)))⁻¹ *
        (loopTr (resolventMat H z) a (Function.update τ ⟨0, hk⟩ true) -
          loopTr (resolventMat H z) a (Function.update τ ⟨0, hk⟩ false)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h0 : (⟨0, hk⟩ : Fin (m + 1)) = 0 := rfl
  rw [h0]
  set X := resolventMat H z with hX
  set R : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    (List.ofFn fun i : Fin m => sgnMat X (τ i.succ) * blockE W L (a i.succ)).prod with hR
  have hupd : ∀ t : Bool, loopTr X a (Function.update τ 0 t) =
      ((sgnMat X t * blockE W L (a 0)) * R).trace := by
    intro t
    rw [ward_loopTr_succ]
    simp only [Function.update_self, hR]
    congr 4
  have hlhs : ∀ c : Fin L, loopTr X (Fin.snoc a c : Fin (m + 1 + 1) → Fin L)
      (Fin.snoc (Function.update τ 0 s) (!s) : Fin (m + 1 + 1) → Bool) =
      (((sgnMat X s * blockE W L (a 0)) * R) * (sgnMat X (!s) * blockE W L c)).trace := by
    intro c
    rw [ward_loopTr_snoc, List.ofFn_succ, List.prod_cons]
    simp only [Function.update_self, hR]
    congr 5
  have hz0 : z.im ≠ 0 := hz.ne'
  have hS := ward_sgnMat_mul hH hz0 s
  rw [← hX] at hS
  rw [hupd true, hupd false, Finset.sum_congr rfl fun c _ => hlhs c, ← Matrix.trace_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ward_sum_blockE, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hS, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, Matrix.sub_mul,
    Matrix.sub_mul, Matrix.trace_sub]
  simp only [sgnMat, ite_true, Bool.false_eq_true, ite_false, hX, smul_eq_mul]
  have hsc : (W : ℂ)⁻¹ * (2 * (z.im : ℂ) * Complex.I)⁻¹ =
      (2 * Complex.I * (W : ℂ) * (z.im : ℂ))⁻¹ := by
    rw [← mul_inv]
    congr 1
    ring
  rw [← mul_assoc, hsc]

end LSBA
