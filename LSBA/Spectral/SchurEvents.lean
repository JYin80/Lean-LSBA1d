import LSBA.Spectral.Schur
import LSBA.Gauss.QuadLDE

/-!
# The Schur good events

The union over `i` of the diagonal and quadratic-form bad events for a GUE matrix with a diagonal
Hermitian deformation.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

noncomputable section
open scoped Classical

namespace LSBA

/-- The entries of the GUE matrix are measurable in the sample. -/
private lemma schurEvents_measurable_entry (n : ℕ) (a b : Fin n) :
    Measurable fun ω : Ω n 1 => gueMat n ω a b := by
  unfold gueMat gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The matrix inverse is measurable. -/
private lemma schurEvents_measurable_inv {m : Type*} [Fintype m] [DecidableEq m] :
    Measurable fun A : Matrix m m ℂ => A⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hd : Measurable fun A : Matrix m m ℂ => A.det :=
    (continuous_id.matrix_det).measurable
  have ha : Measurable fun A : Matrix m m ℂ => A.adjugate i j :=
    (continuous_id.matrix_adjugate).measurable.eval_matrix
  exact (hd.inv).mul ha

/-- The minor resolvent of the deformed GUE matrix is measurable in the sample. -/
private lemma schurEvents_measurable_resolvent (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (i : Fin n) :
    Measurable fun ω : Ω n 1 => resolventMat (minorMat (gueMat n ω - B) i) z := by
  unfold resolventMat
  refine schurEvents_measurable_inv.comp ?_
  refine Measurable.of_eval_matrix _ fun k l => ?_
  by_cases h : k = l
  · subst h
    simp only [minorMat, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul]
    exact ((schurEvents_measurable_entry n _ _).sub measurable_const).sub measurable_const
  · simp only [minorMat, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Matrix.one_apply_ne h, smul_zero, sub_zero]
    exact (schurEvents_measurable_entry n _ _).sub measurable_const

/-- The minor resolvent does not depend on row and column `i` of the GUE matrix. -/
private lemma schurEvents_offRow (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (i : Fin n) :
    OffRow n i fun ω : Ω n 1 => resolventMat (minorMat (gueMat n ω - B) i) z := by
  intro ω ω' h
  have hM : minorMat (gueMat n ω - B) i = minorMat (gueMat n ω' - B) i := by
    ext k l
    have hkl : gueMat n ω k.1 l.1 = gueMat n ω' k.1 l.1 := by
      have h1 := h (0, k.1, l.1) k.2 l.2
      have h2 := h (0, l.1, k.1) l.2 k.2
      have h3 := h (0, k.1, k.1) k.2 k.2
      simp only [gueMat, gueBlock, Matrix.of_apply]
      simp [h1, h2, h3]
    simp [minorMat, hkl]
  simp only [resolventMat, hM]

/-- Failure probability of the diagonal-entry and centred quadratic-form bounds of Appendix G.1
[app:relative-local-law-proof] at one spectral parameter, for diagonal Hermitian `B`:
at most `n (K t^{-2p} + 2 e^{-t²/2})`. -/
theorem schurEvents_fail_le (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), B.IsHermitian → B.IsDiag →
      ∀ (z : ℂ) (t : ℝ), 0 < z.im → 0 < t →
        μ n 1 {ω | ∃ i, t / Real.sqrt n < ‖gueMat n ω i i‖ ∨
            t / n * Real.sqrt (∑ k, ∑ l, ‖resolventMat (minorMat (gueMat n ω - B) i) z k l‖ ^ 2) <
              ‖schurQuadDev (gueMat n ω - B) z i‖} ≤
          ENNReal.ofReal (n * (K * t ^ (-(2 * (p : ℝ))) + 2 * Real.exp (-t ^ 2 / 2))) := by
  obtain ⟨K, hK, h⟩ := gue_quadForm_tail p
  refine ⟨K, hK, fun n B _ hBd z t _ ht => ?_⟩
  have hD : ∀ i : Fin n, μ n 1 {ω | t / Real.sqrt n < ‖gueMat n ω i i‖} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := fun i => gue_diag_tail n i ht.le
  have hQ : ∀ i : Fin n, μ n 1 {ω | t / n *
        Real.sqrt (∑ k, ∑ l, ‖resolventMat (minorMat (gueMat n ω - B) i) z k l‖ ^ 2) <
          ‖schurQuadDev (gueMat n ω - B) z i‖} ≤ ENNReal.ofReal (K * t ^ (-(2 * (p : ℝ)))) := by
    intro i
    have key := h n i (κ := {k // k ≠ i}) Subtype.val Subtype.val_injective (fun k => k.2)
      (fun ω => resolventMat (minorMat (gueMat n ω - B) i) z)
      (schurEvents_measurable_resolvent n B z i) (schurEvents_offRow n B z i) t ht
    have hcol : ∀ ω : Ω n 1, minorCol (gueMat n ω - B) i = fun k => gueMat n ω k.1 i := by
      intro ω
      funext k
      simp [minorCol, Matrix.sub_apply, hBd k.2]
    convert key using 3
    ext ω
    simp only [schurQuadDev, hcol, Fintype.card_fin]
  have hset : {ω : Ω n 1 | ∃ i, t / Real.sqrt n < ‖gueMat n ω i i‖ ∨
        t / n * Real.sqrt (∑ k, ∑ l, ‖resolventMat (minorMat (gueMat n ω - B) i) z k l‖ ^ 2) <
          ‖schurQuadDev (gueMat n ω - B) z i‖} =
      ⋃ i : Fin n, ({ω | t / Real.sqrt n < ‖gueMat n ω i i‖} ∪
        {ω | t / n * Real.sqrt (∑ k, ∑ l,
            ‖resolventMat (minorMat (gueMat n ω - B) i) z k l‖ ^ 2) <
          ‖schurQuadDev (gueMat n ω - B) z i‖}) := by
    ext ω; simp
  rw [hset]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  have hsum : ∀ i : Fin n, μ n 1 ({ω | t / Real.sqrt n < ‖gueMat n ω i i‖} ∪
        {ω | t / n * Real.sqrt (∑ k, ∑ l,
            ‖resolventMat (minorMat (gueMat n ω - B) i) z k l‖ ^ 2) <
          ‖schurQuadDev (gueMat n ω - B) z i‖}) ≤
      ENNReal.ofReal (K * t ^ (-(2 * (p : ℝ))) + 2 * Real.exp (-t ^ 2 / 2)) := by
    intro i
    refine (measure_union_le _ _).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      add_comm (ENNReal.ofReal (K * t ^ (-(2 * (p : ℝ)))))]
    exact add_le_add (hD i) (hQ i)
  refine (Finset.sum_le_sum fun i _ => hsum i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

end LSBA
