import LSBA.Gauss.HermCoord
import LSBA.Gauss.Divergence

/-!
# Gaussian divergence of conjugation fields

For a skew-Hermitian `A`, Hermitian shifts `c_i` and a set `S` of blocks, the field
`V_i ↦ [A, V_i - c_i]` (`i ∈ S`) in standard coordinates has zero Euclidean divergence and
`⟨V_i, [A, V_i]⟩ = 0`, so its Gaussian divergence is `-W Σ_{i ∈ S} Re Tr(V_i [A, c_i])`: only the
shifts contribute to the Gaussian score (proof of Lemma 9.4 [us:lem:score]; (8.33)
[up:eq:gaussian-divergence]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `δ_G` of the conjugation field `V_i ↦ [A, V_i - c_i]` on the blocks in `S` is
`-W Σ_{i ∈ S} Re Tr(V_i [A, c_i])`. -/
theorem gaussDiv_hermCoord_comm {W q : ℕ} (S : Finset (Fin q)) {A : Matrix (Fin W) (Fin W) ℂ}
    (hA : Aᴴ = -A) {c : Fin q → Matrix (Fin W) (Fin W) ℂ} (hc : ∀ i, (c i).IsHermitian)
    (ω : Ω W q) :
    gaussDiv (fun η => hermCoord W q fun i => if i ∈ S then
        A * (gueBlock W q η i - c i) - (gueBlock W q η i - c i) * A else 0) ω =
      -(W : ℝ) * ∑ i ∈ S, (gueBlock W q ω i * (A * c i - c i * A)).trace.re := by
  -- the block `i` after moving the `p = (i, k)` coordinate by `t`
  have hshift : ∀ (η : Ω W q) (t : ℝ) (p : Fin q × Fin W × Fin W),
      gueBlock W q (η + t • Pi.single p (1 : ℝ)) p.1 = gueBlock W q η p.1 +
        ((t * (Real.sqrt W)⁻¹ : ℝ) : ℂ) • hermBasis W (p.2.1, p.2.2) := by
    intro η t p
    rw [gueBlock_eq_sum_hermBasis, gueBlock_eq_sum_hermBasis]
    have h1 : ∀ k : Fin W × Fin W, ((((η + t • Pi.single p (1 : ℝ) : Ω W q)) (p.1, k.1, k.2) : ℝ) : ℂ) • hermBasis W k =
        (η (p.1, k.1, k.2) : ℂ) • hermBasis W k +
          (t : ℂ) • (if k = (p.2.1, p.2.2) then hermBasis W k else 0) := by
      intro k
      by_cases hk : k = (p.2.1, p.2.2)
      · have : (p.1, k.1, k.2) = p := by rw [hk]
        simp only [Pi.add_apply, Pi.smul_apply, this, Pi.single_eq_same, hk, ite_true,
          smul_eq_mul, mul_one]
        push_cast
        rw [add_smul]
      · have : (p.1, k.1, k.2) ≠ p := by
          intro h; apply hk; rw [← h]
        simp [Pi.single_eq_of_ne this, hk]
    have h2 : ∑ k : Fin W × Fin W, (t : ℂ) • (if k = (p.2.1, p.2.2) then hermBasis W k else 0) =
        (t : ℂ) • hermBasis W (p.2.1, p.2.2) := by
      rw [← Finset.smul_sum, Finset.sum_ite_eq' Finset.univ (p.2.1, p.2.2)]
      simp
    simp only [h1, Finset.sum_add_distrib, h2]
    rw [smul_add, smul_smul]
    push_cast
    rw [mul_comm (t : ℂ)]
  -- the conjugation field
  set Xf : Ω W q → Fin q → Matrix (Fin W) (Fin W) ℂ := fun η i => if i ∈ S then
      A * (gueBlock W q η i - c i) - (gueBlock W q η i - c i) * A else 0 with hXf
  -- zero Euclidean divergence
  have hdiv : ∀ p : Fin q × Fin W × Fin W,
      lineDeriv ℝ (fun y => hermCoord W q (Xf y) p) ω (Pi.single p (1 : ℝ)) = 0 := by
    intro p
    have hconst : (fun t : ℝ => hermCoord W q (Xf (ω + t • Pi.single p (1 : ℝ))) p) =
        fun _ => hermCoord W q (Xf ω) p := by
      funext t
      simp only [hermCoord, hXf]
      by_cases hi : p.1 ∈ S
      · simp only [hi, ite_true]
        rw [hshift ω t p]
        congr 2
        set T := hermBasis W (p.2.1, p.2.2)
        set s : ℂ := ((t * (Real.sqrt W)⁻¹ : ℝ) : ℂ)
        set V := gueBlock W q ω p.1
        have h0 : (T * (A * T - T * A)).trace = 0 := by
          rw [mul_sub, Matrix.trace_sub, ← mul_assoc, ← mul_assoc,
            Matrix.trace_mul_comm (T * A) T, ← mul_assoc, sub_self]
        have : A * (V + s • T - c p.1) - (V + s • T - c p.1) * A =
            (A * (V - c p.1) - (V - c p.1) * A) + s • (A * T - T * A) := by
          simp only [add_sub_right_comm, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
            smul_sub]
          abel
        rw [this, mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul, h0]
        simp
      · simp [hi]
    unfold lineDeriv
    simp only [hconst, deriv_const]
  -- the drift term
  have hsum : ∑ p, ω p * hermCoord W q (Xf ω) p =
      -(W : ℝ) * ∑ i ∈ S, (gueBlock W q ω i * (A * c i - c i * A)).trace.re := by
    have hpt : ∀ i : Fin q, ∑ k : Fin W × Fin W,
        ω (i, k.1, k.2) * hermCoord W q (Xf ω) (i, k.1, k.2) =
        (W : ℝ) * (gueBlock W q ω i * Xf ω i).trace.re := by
      intro i
      rcases Nat.eq_zero_or_pos W with rfl | hWpos
      · simp
      · have hW : (0 : ℝ) < W := by exact_mod_cast hWpos
        have hsW : Real.sqrt W ≠ 0 := (Real.sqrt_pos.2 hW).ne'
        have key : (gueBlock W q ω i * Xf ω i).trace.re =
            (Real.sqrt W)⁻¹ * ∑ k : Fin W × Fin W,
              ω (i, k.1, k.2) * (hermBasis W k * Xf ω i).trace.re := by
          rw [gueBlock_eq_sum_hermBasis, Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul,
            Matrix.trace_sum, smul_eq_mul, ← Complex.ofReal_inv, Complex.re_ofReal_mul,
            Complex.re_sum]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
        rw [key, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hermCoord]
        field_simp
        rw [Real.sq_sqrt hW.le]
        ring
    have hzero : ∀ i ∈ (Finset.univ : Finset (Fin q)), i ∉ S →
        (W : ℝ) * (gueBlock W q ω i * Xf ω i).trace.re = 0 := by
      intro i _ hi
      simp [hXf, hi]
    have hS : ∀ i ∈ S, (W : ℝ) * (gueBlock W q ω i * Xf ω i).trace.re =
        -(W : ℝ) * (gueBlock W q ω i * (A * c i - c i * A)).trace.re := by
      intro i hi
      have h0 : (gueBlock W q ω i * (A * gueBlock W q ω i - gueBlock W q ω i * A)).trace = 0 := by
        rw [mul_sub, Matrix.trace_sub, ← mul_assoc, ← mul_assoc,
          Matrix.trace_mul_comm (gueBlock W q ω i * A) (gueBlock W q ω i), ← mul_assoc, sub_self]
      have : Xf ω i = (A * gueBlock W q ω i - gueBlock W q ω i * A) - (A * c i - c i * A) := by
        simp only [hXf, hi, ite_true]
        noncomm_ring
      rw [this, mul_sub, Matrix.trace_sub, h0]
      simp
    rw [Fintype.sum_prod_type]
    simp only [hpt]
    rw [← Finset.sum_subset (Finset.subset_univ S) hzero, Finset.mul_sum]
    exact Finset.sum_congr rfl hS
  change gaussDiv (fun η => hermCoord W q (Xf η)) ω = _
  unfold gaussDiv
  simp only [hdiv, sub_zero]
  exact hsum

end LSBA
