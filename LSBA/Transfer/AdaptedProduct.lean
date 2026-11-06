import LSBA.Transfer.NormalForm

/-!
# The adapted product

The iterated update (11.4) [lg:eq:normal-transfer]: the unitary chain `C_i` and the product `F_n ⋯
F_1`, with `S_E⁻¹ T_n ⋯ T_1 S_E (I; C₀) = μ^n (I; C_n) F_n ⋯ F_1`; the matrix `D_n(C₀)` of (11.5)
[lg:eq:matrix-product] and its invertibility. Blocks are indexed from 0: `V k` is the block
`V_{k+1}` of the paper.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The graph matrices `C_i` of (11.3) [lg:eq:matrix-update] along the blocks `V 0, V 1, …`:
`C_0 = C₀`, `C_{i+1} = C'(C_i, V i)`. -/
def chainC (g E : ℝ) {W : ℕ} (C₀ : Matrix (Fin W) (Fin W) ℂ) (V : ℕ → Matrix (Fin W) (Fin W) ℂ) :
    ℕ → Matrix (Fin W) (Fin W) ℂ
  | 0 => C₀
  | i + 1 => stepC g E (chainC g E C₀ V i) (V i)

/-- The adapted product `F(C_{n-1}, V (n-1)) ⋯ F(C_0, V 0)` of (11.5)
[lg:eq:matrix-product]. -/
def stepProd (g E : ℝ) {W : ℕ} (C₀ : Matrix (Fin W) (Fin W) ℂ)
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) : ℕ → Matrix (Fin W) (Fin W) ℂ
  | 0 => 1
  | i + 1 => stepF g E (chainC g E C₀ V i) (V i) * stepProd g E C₀ V i

/-- Every `C_i` is unitary (Section 11.1 [lg:sec:scalar-growth]). -/
theorem chainC_mem_unitaryGroup (g E : ℝ) {W : ℕ} {C₀ : Matrix (Fin W) (Fin W) ℂ}
    (hC₀ : C₀ ∈ Matrix.unitaryGroup (Fin W) ℂ) {V : ℕ → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ k, (V k).IsHermitian) (i : ℕ) :
    chainC g E C₀ V i ∈ Matrix.unitaryGroup (Fin W) ℂ := by
  induction i with
  | zero => exact hC₀
  | succ i ih => exact stepC_mem_unitaryGroup g E ih (hV i)

/-- Iterated (11.3) [lg:eq:matrix-update]:
`S_E⁻¹ (T_n ⋯ T_1) S_E (I; C₀) = (-i e^{iθ})^n (I; C_n) F(C_{n-1}, V_n) ⋯ F(C_0, V_1)`. -/
theorem inv_freeConj_mul_transferProd_mul_colStack {W : ℕ} {E : ℝ} (hE : |E| < 2) (g : ℝ)
    {C₀ : Matrix (Fin W) (Fin W) ℂ} (hC₀ : C₀ ∈ Matrix.unitaryGroup (Fin W) ℂ)
    {V : ℕ → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ k, (V k).IsHermitian) (n : ℕ) :
    (freeConj W E)⁻¹ * transferProd g (E : ℂ) V n * freeConj W E * colStack 1 C₀ =
      stepPhase E ^ n • (colStack 1 (chainC g E C₀ V n) * stepProd g E C₀ V n) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_freeConj W hE)
  induction n with
  | zero =>
    simp only [transferProd, chainC, stepProd, pow_zero, one_smul, Matrix.mul_one]
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  | succ n ih =>
    have h1 : freeConj W E * (freeConj W E)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have hsplit : (freeConj W E)⁻¹ * transferProd g (E : ℂ) V (n + 1) * freeConj W E =
        ((freeConj W E)⁻¹ * transferMat g (E : ℂ) (V n) * freeConj W E) *
          ((freeConj W E)⁻¹ * transferProd g (E : ℂ) V n * freeConj W E) := by
      have h2 : ((freeConj W E)⁻¹ * transferMat g (E : ℂ) (V n) * freeConj W E) *
          ((freeConj W E)⁻¹ * transferProd g (E : ℂ) V n * freeConj W E) =
          (freeConj W E)⁻¹ * transferMat g (E : ℂ) (V n) * (freeConj W E * (freeConj W E)⁻¹) *
            transferProd g (E : ℂ) V n * freeConj W E := by
        simp only [Matrix.mul_assoc]
      rw [h2, h1]
      simp only [transferProd, Matrix.mul_one, Matrix.mul_assoc]
    have hstep := inv_freeConj_mul_transferMat_mul_colStack hE g
      (chainC_mem_unitaryGroup g E hC₀ hV n) (hV n)
    rw [hsplit, Matrix.mul_assoc, ih, Matrix.mul_smul, ← Matrix.mul_assoc, hstep, Matrix.smul_mul,
      smul_smul, ← pow_succ]
    simp only [stepProd, chainC, Matrix.mul_assoc]

/-- The normal-coordinate matrix `D_n(C₀; E) = (I 0) S_E⁻¹ (T_n ⋯ T_1) S_E (I; C₀)` of (11.4)
[lg:eq:normal-transfer]. -/
def normalD (g E : ℝ) {W : ℕ} (C₀ : Matrix (Fin W) (Fin W) ℂ)
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun α β =>
    ((freeConj W E)⁻¹ * transferProd g (E : ℂ) V n * freeConj W E * colStack 1 C₀) (0, α) β

/-- (11.5) [lg:eq:matrix-product]: `D_n(C₀; E) = (-i)^n e^{inθ} F(C_{n-1}, V_n) ⋯ F(C_0, V_1)`. -/
theorem normalD_eq {W : ℕ} {E : ℝ} (hE : |E| < 2) (g : ℝ) {C₀ : Matrix (Fin W) (Fin W) ℂ}
    (hC₀ : C₀ ∈ Matrix.unitaryGroup (Fin W) ℂ) {V : ℕ → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ k, (V k).IsHermitian) (n : ℕ) :
    normalD g E C₀ V n = stepPhase E ^ n • stepProd g E C₀ V n := by
  ext α β
  unfold normalD
  rw [Matrix.of_apply, inv_freeConj_mul_transferProd_mul_colStack hE g hC₀ hV n]
  simp only [Matrix.smul_apply, Matrix.mul_apply, colStack, Matrix.of_apply, smul_eq_mul]
  simp [Matrix.one_apply]

/-- `D_n(C₀; E)` of (11.4) [lg:eq:normal-transfer] is invertible. -/
theorem isUnit_normalD {W : ℕ} {E : ℝ} (hE : |E| < 2) (g : ℝ) {C₀ : Matrix (Fin W) (Fin W) ℂ}
    (hC₀ : C₀ ∈ Matrix.unitaryGroup (Fin W) ℂ) {V : ℕ → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ k, (V k).IsHermitian) (n : ℕ) : IsUnit (normalD g E C₀ V n) := by
  have hprod : ∀ m, IsUnit (stepProd g E C₀ V m) := by
    intro m
    induction m with
    | zero => exact isUnit_one
    | succ m ih =>
      exact (isUnit_stepF g E (chainC_mem_unitaryGroup g E hC₀ hV m) (hV m)).mul ih
  rw [normalD_eq hE g hC₀ hV n]
  have hμ : IsUnit (stepPhase E ^ n) := by
    refine IsUnit.pow n (isUnit_iff_ne_zero.mpr ?_)
    unfold stepPhase
    exact Complex.exp_ne_zero _
  rw [Algebra.smul_def]
  exact (hμ.map (algebraMap ℂ (Matrix (Fin W) (Fin W) ℂ))).mul (hprod n)

end LSBA
