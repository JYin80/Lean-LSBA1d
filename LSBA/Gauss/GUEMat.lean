import LSBA.Gauss.GUELaw

/-!
# One GUE matrix

`gueMat n ω` as the single block of `μ n 1` (entry variance `1/n`, (1.2) [eq:covariance]), the
Gaussian tail of its diagonal entries, and the measure-preserving conjugation by a diagonal sign
matrix.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

noncomputable section
open scoped Classical

namespace LSBA

/-- The `n × n` GUE matrix of (1.2) [eq:covariance] (one block), entry variance `1/n`. -/
def gueMat (n : ℕ) (ω : Ω n 1) : Matrix (Fin n) (Fin n) ℂ := gueBlock n 1 ω 0

private theorem gueMat_gaussian_upper {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 1).real {x : ℝ | t ≤ x} ≤ Real.exp (-t ^ 2 / 2) := by
  have h := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) t ht
    (integrable_exp_mul_gaussianReal t)
  rw [mgf_id_gaussianReal] at h
  refine le_trans h (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  simp only [NNReal.coe_one]
  ring

private theorem gueMat_gaussian_lower {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 1).real {x : ℝ | x ≤ -t} ≤ Real.exp (-t ^ 2 / 2) := by
  have h := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) (-t) (t := -t)
    (by linarith) (integrable_exp_mul_gaussianReal (-t))
  rw [mgf_id_gaussianReal] at h
  refine le_trans h (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  simp only [NNReal.coe_one]
  ring

private theorem gueMat_gaussian_abs {t : ℝ} (ht : 0 ≤ t) :
    gaussianReal 0 1 {x : ℝ | t < |x|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := by
  have hsub : {x : ℝ | t < |x|} ⊆ {x : ℝ | t ≤ x} ∪ {x : ℝ | x ≤ -t} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
    rcases le_total 0 x with h | h
    · left; rw [abs_of_nonneg h] at hx; exact hx.le
    · right; rw [abs_of_nonpos h] at hx; linarith
  have h1 : gaussianReal 0 1 {x : ℝ | t < |x|} ≤
      gaussianReal 0 1 {x : ℝ | t ≤ x} + gaussianReal 0 1 {x : ℝ | x ≤ -t} :=
    (measure_mono hsub).trans (measure_union_le _ _)
  refine h1.trans ?_
  rw [← ofReal_measureReal (μ := gaussianReal 0 1), ← ofReal_measureReal (μ := gaussianReal 0 1),
    ← ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  have := gueMat_gaussian_upper ht
  have := gueMat_gaussian_lower ht
  linarith

/-- Gaussian tail of a diagonal entry `V_jj ~ N(0, 1/n)`, (1.2) [eq:covariance]. -/
theorem gue_diag_tail (n : ℕ) (j : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    μ n 1 {ω | t / Real.sqrt n < ‖gueMat n ω j j‖} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := by
  have hn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast Fin.pos j)
  have hset : {ω : Ω n 1 | t / Real.sqrt n < ‖gueMat n ω j j‖} =
      (fun ω : Ω n 1 => ω (0, j, j)) ⁻¹' {x : ℝ | t < |x|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, gueMat, gueBlock, Matrix.of_apply, ite_true]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hn]
    exact div_lt_div_iff_of_pos_right hn
  have hmp := measurePreserving_eval (fun _ : Fin 1 × Fin n × Fin n => gaussianReal (0 : ℝ) 1)
    (0, j, j)
  rw [hset, ← Measure.map_apply hmp.measurable (measurableSet_lt measurable_const
    continuous_abs.measurable)]
  have hmap : (μ n 1).map (fun ω : Ω n 1 => ω (0, j, j)) = gaussianReal 0 1 := hmp.map_eq
  rw [hmap]
  exact gueMat_gaussian_abs ht

/-- Invariance under a diagonal sign conjugation `V ↦ S V S`, `S = diag(s)`, the random-sign
step of Appendix G.1 [app:relative-local-law-proof]. -/
theorem measurePreserving_signConj (n : ℕ) (s : Fin n → ℤˣ) :
    ∃ T : Ω n 1 → Ω n 1, MeasurePreserving T (μ n 1) (μ n 1) ∧
      ∀ ω, gueMat n (T ω) =
        Matrix.diagonal (fun i => ((s i : ℤ) : ℂ)) * gueMat n ω *
          Matrix.diagonal (fun i => ((s i : ℤ) : ℂ)) := by
  have hstar : star (Matrix.diagonal (fun i => ((s i : ℤ) : ℂ))) =
      Matrix.diagonal (fun i => ((s i : ℤ) : ℂ)) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    simp
  have hU : Matrix.diagonal (fun i => ((s i : ℤ) : ℂ)) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, hstar, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    rcases Int.units_eq_one_or (s i) with h | h <;> simp [h]
  refine ⟨conjMap n 1 ⟨_, hU⟩, measurePreserving_conjMap n 1 ⟨_, hU⟩, fun ω => ?_⟩
  simp only [gueMat]
  rw [gueBlock_conjMap]
  simp only [hstar]

end LSBA
