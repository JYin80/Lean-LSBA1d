import LSBA.Gauss.GUELaw

/-!
# GUE contractions

Second-moment contractions of one GUE block (1.2) [eq:covariance]: `𝔼[V X V]`, `𝔼[(x*Vw)(p*Vq)]`,
and the vanishing of odd functionals. These are the Wick identities behind (11.12) [lg:eq:c2],
(11.20) [uvg:eq:mmean] and (11.21) [uvg:eq:fmean].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Each entry of a GUE block is square integrable. -/
private theorem GUEContract_memLp_entry (W : ℕ) (α β : Fin W) :
    MemLp (fun ω => gueBlock W 1 ω 0 α β) 2 (μ W 1) := by
  have hc : ∀ x : Fin 1 × Fin W × Fin W, MemLp (fun ω : Ω W 1 => (ω x : ℂ)) 2 (μ W 1) := by
    intro x
    have h : MemLp id 2 (gaussianReal (0 : ℝ) 1) := memLp_id_gaussianReal' 2 ENNReal.ofNat_ne_top
    have h2 : MemLp (fun ω : Ω W 1 => ω x) 2 (μ W 1) :=
      h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin 1 × Fin W × Fin W =>
        gaussianReal (0 : ℝ) 1) x)
    exact h2.ofReal
  have key : ∀ ω : Ω W 1, gueBlock W 1 ω 0 α β = ((Real.sqrt W : ℝ) : ℂ)⁻¹ *
      ∑ k : Fin W × Fin W, (ω (0, k.1, k.2) : ℂ) * hermBasis W k α β := by
    intro ω
    rw [gueBlock_eq_sum_hermBasis]
    simp [Matrix.smul_apply, Matrix.sum_apply]
  simp_rw [key]
  refine MemLp.const_mul ?_ _
  exact memLp_finsetSum _ fun (k : Fin W × Fin W) _ => (hc (0, k.1, k.2)).mul_const _

private theorem GUEContract_integrable_mul (W : ℕ) (α β γ δ : Fin W) :
    Integrable (fun ω => gueBlock W 1 ω 0 α β * gueBlock W 1 ω 0 γ δ) (μ W 1) :=
  (GUEContract_memLp_entry W α β).integrable_mul (GUEContract_memLp_entry W γ δ)

private theorem GUEContract_gueBlock_neg (W : ℕ) (ω : Ω W 1) :
    gueBlock W 1 (-ω) 0 = -gueBlock W 1 ω 0 := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Pi.neg_apply, Matrix.neg_apply]
  split_ifs <;> push_cast <;> ring

/-- `𝔼[V X V] = W⁻¹ Tr(X) I` for one GUE block, from (1.2) [eq:covariance]. -/
theorem integral_gueBlock_mul_mul_apply (W : ℕ) (X : Matrix (Fin W) (Fin W) ℂ) (α β : Fin W) :
    ∫ ω, (gueBlock W 1 ω 0 * X * gueBlock W 1 ω 0) α β ∂(μ W 1) =
      if α = β then (W : ℂ)⁻¹ * X.trace else 0 := by
  have hexp : ∀ ω : Ω W 1, (gueBlock W 1 ω 0 * X * gueBlock W 1 ω 0) α β =
      ∑ γ, ∑ δ, X γ δ * (gueBlock W 1 ω 0 α γ * gueBlock W 1 ω 0 δ β) := by
    intro ω
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
    ring
  simp_rw [hexp]
  have hi : ∀ γ δ : Fin W, Integrable (fun ω : Ω W 1 =>
      X γ δ * (gueBlock W 1 ω 0 α γ * gueBlock W 1 ω 0 δ β)) (μ W 1) :=
    fun γ δ => (GUEContract_integrable_mul W α γ δ β).const_mul _
  have hi' : ∀ γ : Fin W, Integrable (fun ω : Ω W 1 =>
      ∑ δ, X γ δ * (gueBlock W 1 ω 0 α γ * gueBlock W 1 ω 0 δ β)) (μ W 1) :=
    fun γ => integrable_finsetSum _ fun δ _ => hi γ δ
  rw [integral_finsetSum _ fun γ _ => hi' γ]
  have h1 : ∀ γ, ∫ ω, ∑ δ, X γ δ * (gueBlock W 1 ω 0 α γ * gueBlock W 1 ω 0 δ β) ∂(μ W 1) =
      ∑ δ, X γ δ * (if γ = δ ∧ α = β then (W : ℂ)⁻¹ else 0) := by
    intro γ
    rw [integral_finsetSum _ fun δ _ => hi γ δ]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [integral_const_mul, gueBlock_covariance]
    have hc : (α = β ∧ γ = δ) ↔ (γ = δ ∧ α = β) := and_comm
    simp only [true_and, hc]
  simp_rw [h1]
  by_cases hab : α = β
  · simp [hab, Matrix.trace, Finset.mul_sum, mul_comm]
  · simp [hab]

/-- `𝔼[(x* V w)(p* V q)] = W⁻¹ (x* q)(p* w)` for one GUE block, from (1.2) [eq:covariance]. -/
theorem integral_dotProduct_gueBlock_mul (W : ℕ) (x w p q : Fin W → ℂ) :
    ∫ ω, (star x ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ w)) * (star p ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ q)) ∂(μ W 1) =
      (W : ℂ)⁻¹ * (star x ⬝ᵥ q) * (star p ⬝ᵥ w) := by
  have hexp : ∀ ω : Ω W 1, (star x ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ w)) *
      (star p ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ q)) = ∑ k, ∑ l, ∑ i, ∑ j,
        star x i * w j * star p k * q l *
          (gueBlock W 1 ω 0 i j * gueBlock W 1 ω 0 k l) := by
    intro ω
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hi : ∀ i j k l : Fin W, Integrable (fun ω : Ω W 1 =>
      star x i * w j * star p k * q l *
        (gueBlock W 1 ω 0 i j * gueBlock W 1 ω 0 k l)) (μ W 1) :=
    fun i j k l => (GUEContract_integrable_mul W i j k l).const_mul _
  simp_rw [hexp]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j k l]
  have h1 : ∀ k l, ∫ ω, ∑ i, ∑ j, star x i * w j * star p k * q l *
        (gueBlock W 1 ω 0 i j * gueBlock W 1 ω 0 k l) ∂(μ W 1) =
      ∑ i, ∑ j, star x i * w j * star p k * q l *
        (if j = k ∧ i = l then (W : ℂ)⁻¹ else 0) := by
    intro k l
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j k l]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hi i j k l]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, gueBlock_covariance]
    have hc : (i = l ∧ j = k) ↔ (j = k ∧ i = l) := and_comm
    simp only [true_and, hc]
  have h2 : ∀ k, ∫ ω, ∑ l, ∑ i, ∑ j, star x i * w j * star p k * q l *
        (gueBlock W 1 ω 0 i j * gueBlock W 1 ω 0 k l) ∂(μ W 1) =
      ∑ l, ∑ i, ∑ j, star x i * w j * star p k * q l *
        (if j = k ∧ i = l then (W : ℂ)⁻¹ else 0) := by
    intro k
    rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hi i j k l]
    exact Finset.sum_congr rfl fun l _ => h1 k l
  simp_rw [h2]
  simp only [mul_ite, mul_zero, ite_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [dotProduct, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Odd functionals of one GUE block have mean zero (the law is invariant under `V ↦ -V`). -/
theorem integral_odd_gueBlock {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (W : ℕ)
    (f : Matrix (Fin W) (Fin W) ℂ → G) (hf : ∀ V, f (-V) = -f V) :
    ∫ ω, f (gueBlock W 1 ω 0) ∂(μ W 1) = 0 := by
  have hmp : MeasurePreserving (fun ω : Ω W 1 => -ω) (μ W 1) (μ W 1) := by
    have h := measurePreserving_stdGauss_linearIsometry
      (ι := Fin 1 × Fin W × Fin W) (LinearIsometryEquiv.neg ℝ)
    exact h
  have hme : MeasurableEmbedding (fun ω : Ω W 1 => -ω) :=
    (MeasurableEquiv.neg (Ω W 1)).measurableEmbedding
  have h1 := hmp.integral_comp hme (fun ω => f (gueBlock W 1 ω 0))
  simp only [GUEContract_gueBlock_neg, hf, integral_neg] at h1
  have : ∫ ω, f (gueBlock W 1 ω 0) ∂(μ W 1) = -∫ ω, f (gueBlock W 1 ω 0) ∂(μ W 1) := h1.symm
  have h2 : (2 : ℝ) • ∫ ω, f (gueBlock W 1 ω 0) ∂(μ W 1) = 0 := by
    rw [two_smul]; nth_rewrite 1 [this]; exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

end LSBA
