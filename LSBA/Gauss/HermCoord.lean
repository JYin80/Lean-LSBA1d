import LSBA.Gauss.GUE

/-!
# Standard coordinates of Hermitian input arrays

The standard coordinates `(i, a, b) ↦ √W ⟨H_{(a,b)}, X_i⟩` of an array of Hermitian matrices,
in which a field on `Herm(W)^q` becomes a field on `Ω W q` (Section 8.4
[sec:upper-contraction-rates]): moving along them moves each block `V_i` along `X_i`, and their
squared length is `W Σ_i ‖X_i‖²_HS`, the normalization of (10.4)
[up:eq:lift-divergence-reduction].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

namespace LSBA

/-- The standard coordinates `(i, a, b) ↦ √W Re tr(H_{(a,b)} X_i)` of an input array `X`
(Section 8.4 [sec:upper-contraction-rates]). -/
def hermCoord (W q : ℕ) (X : Fin q → Matrix (Fin W) (Fin W) ℂ) : Ω W q :=
  fun p => Real.sqrt W * (Matrix.trace (hermBasis W (p.2.1, p.2.2) * X p.1)).re

/-- `hermCoord W q` is real-linear. -/
theorem hermCoord_isLinearMap (W q : ℕ) : IsLinearMap ℝ (hermCoord W q) := by
  constructor
  · intro X Y
    funext p
    simp [hermCoord, Matrix.trace_add, mul_add]
  · intro c X
    funext p
    simp [hermCoord, Matrix.trace_smul]
    ring

/-- Completeness of `hermBasis` in matrix form: `Σ_k tr(T_k X) T_k = X`. -/
private theorem hermCoord_sum_trace_smul (W : ℕ) (X : Matrix (Fin W) (Fin W) ℂ) :
    ∑ k : Fin W × Fin W, Matrix.trace (hermBasis W k * X) • hermBasis W k = X := by
  ext l m
  have h : ∀ k : Fin W × Fin W, (Matrix.trace (hermBasis W k * X) • hermBasis W k) l m =
      ∑ i, ∑ j, X j i * (hermBasis W k i j * hermBasis W k l m) := by
    intro k
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [Matrix.sum_apply]
  simp only [h]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  simp only [← Finset.mul_sum, sum_hermBasis_apply_mul_apply]
  simp [ite_and]

/-- For Hermitian `X`, `tr(T_k X)` is real. -/
private theorem hermCoord_trace_real (W : ℕ) (k : Fin W × Fin W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) :
    (((Matrix.trace (hermBasis W k * X)).re : ℝ) : ℂ) = Matrix.trace (hermBasis W k * X) := by
  rw [← Complex.conj_eq_iff_re]
  have h1 := hermBasis_isHermitian W k
  have : star (Matrix.trace (hermBasis W k * X)) = Matrix.trace (hermBasis W k * X) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX.eq, h1.eq,
      Matrix.trace_mul_comm]
  exact this

/-- Moving the standard coordinates along `hermCoord X` moves every block `V_i` along `X_i`,
for Hermitian `X_i` (Section 8.4 [sec:upper-contraction-rates]). -/
theorem gueBlock_add_smul_hermCoord {W q : ℕ} {X : Fin q → Matrix (Fin W) (Fin W) ℂ}
    (hX : ∀ i, (X i).IsHermitian) (ω : Ω W q) (t : ℝ) (i : Fin q) :
    gueBlock W q (ω + t • hermCoord W q X) i = gueBlock W q ω i + (t : ℂ) • X i := by
  ext α β
  have hW : (0 : ℝ) < W := by exact_mod_cast Fin.pos α
  have hsW : ((Real.sqrt W : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hW).ne'
  have h1 : ∀ k : Fin W × Fin W, (((ω + t • hermCoord W q X) (i, k.1, k.2) : ℝ) : ℂ) =
      (ω (i, k.1, k.2) : ℂ) + (t : ℂ) * ((Real.sqrt W : ℝ) : ℂ) *
        Matrix.trace (hermBasis W k * X i) := by
    intro k
    rw [← hermCoord_trace_real W k (hX i)]
    simp [hermCoord]
    ring
  have h2 := congrFun (congrFun (hermCoord_sum_trace_smul W (X i)) α) β
  rw [gueBlock_eq_sum_hermBasis, gueBlock_eq_sum_hermBasis]
  simp only [h1, add_smul, Finset.sum_add_distrib, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul] at h2 ⊢
  have h3 : ∑ x : Fin W × Fin W, (t : ℂ) * ((Real.sqrt W : ℝ) : ℂ) *
      (hermBasis W x * X i).trace * hermBasis W x α β = (t : ℂ) * ((Real.sqrt W : ℝ) : ℂ) * X i α β := by
    rw [← h2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [mul_add, h3]
  field_simp

/-- For Hermitian `X`, `Σ_k (Re tr(T_k X))² = Σ_{ab} ‖X_{ab}‖²`. -/
private theorem hermCoord_sum_re_sq (W : ℕ) {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) :
    ∑ k : Fin W × Fin W, ((Matrix.trace (hermBasis W k * X)).re) ^ 2 =
      ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
  apply Complex.ofReal_injective
  have h1 : Matrix.trace (X * X) = ∑ k : Fin W × Fin W, Matrix.trace (hermBasis W k * X) *
      Matrix.trace (hermBasis W k * X) := by
    have e : Matrix.trace (X * X) = Matrix.trace ((∑ k : Fin W × Fin W,
        Matrix.trace (hermBasis W k * X) • hermBasis W k) * X) := by
      rw [hermCoord_sum_trace_smul W X]
    rw [e, Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have h2 : Matrix.trace (X * X) = ∑ a, ∑ b, ((‖X a b‖ : ℝ) : ℂ) ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have e : X b a = (starRingEnd ℂ) (X a b) := (hX.apply b a).symm
    rw [e, Complex.mul_conj']
  push_cast
  rw [← h2, h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hermCoord_trace_real W k hX, sq]

/-- `Σ_p (hermCoord X)_p² = W Σ_i ‖X_i‖²_HS` for Hermitian `X_i` (the factor `W` in (10.4)
[up:eq:lift-divergence-reduction]). -/
theorem sum_sq_hermCoord {W q : ℕ} {X : Fin q → Matrix (Fin W) (Fin W) ℂ}
    (hX : ∀ i, (X i).IsHermitian) :
    ∑ p, hermCoord W q X p ^ 2 = W * ∑ i, ∑ a, ∑ b, ‖X i a b‖ ^ 2 := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type, ← hermCoord_sum_re_sq W (hX i), Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [hermCoord, mul_pow, Real.sq_sqrt (Nat.cast_nonneg W)]

end LSBA
