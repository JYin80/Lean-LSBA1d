import LSBA.Upper.LiftHermitian
import LSBA.Upper.LiftGeneral

/-!
# Lemma 10.1 [lem:c-gaussian-lift] away from zero energy

The Hermitian lift in the standard coordinates is `C^∞` on `{S_W(G) > 0}`; for `g ≥ 1`,
`0 < |E| ≤ E₀` and a Hermitian target, its Jacobian satisfies (10.32)
[lg:eq:A-derivative-bounds] and (10.33) [lg:eq:DV] in the form
`‖∇_V X‖²_HS ≤ C (1 + |E|⁻¹)² W g² ‖M‖²`; with the cutoff (10.5) [eq:c-main-cutoff] this gives
(10.7) [eq:c-gaussian-away] of Lemma 10.1 [lem:c-gaussian-lift],
`𝔼 |δ_G(χ X)|² ≤ C (1 + |E|⁻¹)² W g²`, with the same cutoff as the general bound, in the
paper's order and, by reversal of the inputs, in the batch order of Definition 8.5
[up:def:transfer-operator].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

private lemma LiftAway_hsSq_nonneg {k l : Type*} [Fintype k] [Fintype l] (A : Matrix k l ℂ) :
    0 ≤ hsSq A := by
  unfold hsSq; positivity

private lemma LiftAway_hsSq_zero {k l : Type*} [Fintype k] [Fintype l] :
    hsSq (0 : Matrix k l ℂ) = 0 := by simp [hsSq]

/-- `‖A - B‖² ≤ 2‖A‖² + 2‖B‖²`. -/
private lemma LiftAway_hsSq_sub_le {k l : Type*} [Fintype k] [Fintype l] (A B : Matrix k l ℂ) :
    hsSq (A - B) ≤ 2 * hsSq A + 2 * hsSq B := by
  unfold hsSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have h := norm_sub_le (A a b) (B a b)
  simp only [Matrix.sub_apply]
  nlinarith [sq_nonneg (‖A a b‖ - ‖B a b‖), norm_nonneg (A a b), norm_nonneg (B a b),
    norm_nonneg (A a b - B a b)]

private lemma LiftAway_hsSq_conj {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    hsSq Aᴴ = hsSq A := by
  simp only [hsSq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

private lemma LiftAway_hsSq_smul {k l : Type*} [Fintype k] [Fintype l] (c : ℂ)
    (A : Matrix k l ℂ) : hsSq (c • A) = ‖c‖ ^ 2 * hsSq A := by
  simp [hsSq, mul_pow, Finset.mul_sum]

/-- `‖A B‖² ≤ |A|²_op ‖B‖²`, column by column. -/
private lemma LiftAway_hsSq_mul_le {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    hsSq (A * B) ≤ ‖A‖ ^ 2 * hsSq B := by
  have hcol : ∀ b : n, ∑ a, ‖(A * B) a b‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ a, ‖B a b‖ ^ 2 := by
    intro b
    have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 (fun a => B a b))
    have h1 : ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ (fun a => B a b))‖ ^ 2 =
        ∑ a, ‖(A * B) a b‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]; rfl
    have h2 : ‖(WithLp.toLp 2 (fun a => B a b) : EuclideanSpace ℂ n)‖ ^ 2 =
        ∑ a, ‖B a b‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]
    rw [← h1, ← h2, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  unfold hsSq
  rw [Finset.sum_comm, Finset.sum_comm (f := fun a b => ‖B a b‖ ^ 2), Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => hcol b

private lemma LiftAway_hsSq_mul_le' {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    hsSq (B * A) ≤ ‖A‖ ^ 2 * hsSq B := by
  rw [← LiftAway_hsSq_conj, Matrix.conjTranspose_mul, ← Matrix.l2_opNorm_conjTranspose A,
    ← LiftAway_hsSq_conj B]
  exact LiftAway_hsSq_mul_le _ _

/-- `‖Σ_{i ∈ s} A_i‖² ≤ |s| Σ_{i ∈ s} ‖A_i‖²`. -/
private lemma LiftAway_hsSq_sum_le {ι k l : Type*} [Fintype k] [Fintype l] (s : Finset ι)
    (A : ι → Matrix k l ℂ) : hsSq (∑ i ∈ s, A i) ≤ s.card * ∑ i ∈ s, hsSq (A i) := by
  unfold hsSq
  have e : ∑ i ∈ s, ∑ a, ∑ b, ‖A i a b‖ ^ 2 = ∑ a, ∑ b, ∑ i ∈ s, ‖A i a b‖ ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [e, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [Matrix.sum_apply a b s A]
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans sq_sum_le_card_mul_sum_sq

private lemma LiftAway_hsInner_sub {k l : Type*} [Fintype k] [Fintype l] (Z A B : Matrix k l ℂ) :
    hsInner Z (A - B) = hsInner Z A - hsInner Z B := by
  simp only [hsInner, Matrix.sub_apply, mul_sub, Complex.sub_re, Finset.sum_sub_distrib]

private lemma LiftAway_hsInner_smul {k l : Type*} [Fintype k] [Fintype l] (Z A : Matrix k l ℂ)
    (r : ℝ) : hsInner Z ((r : ℂ) • A) = r * hsInner Z A := by
  simp only [hsInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [Complex.mul_re]; ring

/-- `⟨A, B⟩ = ⟨B, A⟩`. -/
private lemma LiftAway_hsInner_comm {k l : Type*} [Fintype k] [Fintype l] (A B : Matrix k l ℂ) :
    hsInner A B = hsInner B A := by
  unfold hsInner
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [Complex.mul_re]; ring

/-- `⟨Z, P Y S⟩ = ⟨P* Z S*, Y⟩`. -/
private lemma LiftAway_hsInner_mul {n : Type*} [Fintype n] (Z P Y S : Matrix n n ℂ) :
    hsInner Z (P * Y * S) = hsInner (Pᴴ * Z * Sᴴ) Y := by
  rw [(hsInner_reCoord _ _ 0).1, (hsInner_reCoord _ _ 0).1]
  congr 1
  rw [show Zᴴ * (P * Y * S) = (Zᴴ * P * Y) * S by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
section LiftAwayBlock

variable {W : ℕ}

private lemma LiftAway_hsSq_one (W : ℕ) : hsSq (1 : Matrix (Fin W) (Fin W) ℂ) = W := by
  unfold hsSq; simp [Matrix.one_apply, apply_ite]

/-- `‖[[0, 0], [B, 0]]‖² = ‖B‖²`. -/
private lemma LiftAway_hsSq_N (B : Matrix (Fin W) (Fin W) ℂ) :
    hsSq (blockMat 0 0 B 0) = hsSq B := by
  rw [(blockMat_algebra 0 0 B 0 0 0 0 0).2.2.2, LiftAway_hsSq_zero]; ring

private lemma LiftAway_hsSq_blocks (U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    hsSq U = hsSq (blockPart U 0 0) + hsSq (blockPart U 0 1) + hsSq (blockPart U 1 0) +
      hsSq (blockPart U 1 1) := by
  conv_lhs => rw [← (blockMat_blockPart U 0 0 0 0).1]
  exact (blockMat_algebra _ _ _ _ 0 0 0 0).2.2.2

/-- (10.19) [eq:c-completeness] on the second block column and on the first block row:
`Σ_α ‖U N(H_α)‖² ≤ W ‖U‖²` and `Σ_α ‖N(H_α) U‖² ≤ W ‖U‖²` for `N(H) = [[0, 0], [H, 0]]`. -/
private lemma LiftAway_sum_N (U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∑ k, hsSq (U * blockMat 0 0 (hermBasis W k) 0) ≤ W * hsSq U ∧
      ∑ k, hsSq (blockMat 0 0 (hermBasis W k) 0 * U) ≤ W * hsSq U := by
  have hr : ∀ A : Matrix (Fin W) (Fin W) ℂ, ∑ k, hsSq (A * hermBasis W k) = W * hsSq A := by
    intro A
    have h := (hermBasis_completeness W A 1).2
    simp only [Matrix.mul_one, LiftAway_hsSq_one] at h
    rw [h, mul_comm]
  have hl : ∀ A : Matrix (Fin W) (Fin W) ℂ, ∑ k, hsSq (hermBasis W k * A) = W * hsSq A := by
    intro A
    have h := (hermBasis_completeness W 1 A).2
    simp only [Matrix.one_mul, LiftAway_hsSq_one] at h
    exact h
  have e1 : ∀ k, hsSq (U * blockMat 0 0 (hermBasis W k) 0) =
      hsSq (blockPart U 0 1 * hermBasis W k) + hsSq (blockPart U 1 1 * hermBasis W k) := by
    intro k
    conv_lhs => rw [← (blockMat_blockPart U 0 0 0 0).1]
    rw [(blockMat_algebra _ _ _ _ 0 0 _ 0).1]
    simp only [Matrix.mul_zero, zero_add, add_zero]
    rw [(blockMat_algebra _ _ _ _ 0 0 0 0).2.2.2, LiftAway_hsSq_zero]; ring
  have e2 : ∀ k, hsSq (blockMat 0 0 (hermBasis W k) 0 * U) =
      hsSq (hermBasis W k * blockPart U 0 0) + hsSq (hermBasis W k * blockPart U 0 1) := by
    intro k
    conv_lhs => rw [← (blockMat_blockPart U 0 0 0 0).1]
    rw [(blockMat_algebra 0 0 _ 0 _ _ _ _).1]
    simp only [Matrix.zero_mul, add_zero]
    rw [(blockMat_algebra _ _ _ _ 0 0 0 0).2.2.2, LiftAway_hsSq_zero]; ring
  simp only [e1, e2, Finset.sum_add_distrib, hr, hl]
  rw [LiftAway_hsSq_blocks U]
  have := LiftAway_hsSq_nonneg (blockPart U 0 0)
  have := LiftAway_hsSq_nonneg (blockPart U 0 1)
  have := LiftAway_hsSq_nonneg (blockPart U 1 0)
  have := LiftAway_hsSq_nonneg (blockPart U 1 1)
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  constructor <;> nlinarith

/-- Parseval on the block `(1, 0)`: `Σ_β ⟨Z, P N(H_β) S⟩² ≤ ‖P* Z S*‖²`. -/
private lemma LiftAway_sum_inner_N (Z P S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∑ k, hsInner Z (P * blockMat 0 0 (hermBasis W k) 0 * S) ^ 2 ≤ hsSq (Pᴴ * Z * Sᴴ) := by
  have hN : ∀ (U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (H : Matrix (Fin W) (Fin W) ℂ),
      hsInner U (blockMat 0 0 H 0) = hsInner H (blockPart U 1 0) := by
    intro U H
    rw [LiftAway_hsInner_comm]
    simp [hsInner, blockMat, blockPart, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [LiftAway_hsInner_mul, hN]
  refine (hermBasis_parseval W _).1.trans ?_
  rw [LiftAway_hsSq_blocks (Pᴴ * Z * Sᴴ)]
  have := LiftAway_hsSq_nonneg (blockPart (Pᴴ * Z * Sᴴ) 0 0)
  have := LiftAway_hsSq_nonneg (blockPart (Pᴴ * Z * Sᴴ) 0 1)
  have := LiftAway_hsSq_nonneg (blockPart (Pᴴ * Z * Sᴴ) 1 1)
  linarith

/-- `‖Σ_k c_k H_k‖² = Σ_k c_k²` for real `c_k`. -/
private lemma LiftAway_hsSq_basis (W : ℕ) (c : Fin W × Fin W → ℝ) :
    hsSq (∑ k, ((c k : ℝ) : ℂ) • hermBasis W k) = ∑ k, c k ^ 2 := by
  have hl : ∀ (A : Fin W × Fin W → Matrix (Fin W) (Fin W) ℂ) (B : Matrix (Fin W) (Fin W) ℂ),
      hsInner (∑ x, ((c x : ℝ) : ℂ) • A x) B = ∑ x, c x * hsInner (A x) B := by
    intro A B
    simp only [(hsInner_reCoord _ _ 0).1, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      Complex.star_def, Complex.conj_ofReal, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
      Complex.re_sum, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hb : ∀ k l, hsInner (hermBasis W k) (hermBasis W l) = if k = l then 1 else 0 := by
    intro k l
    rw [(hsInner_reCoord _ _ 0).1, (hermBasis_isHermitian W k).eq, trace_hermBasis_mul]
    split_ifs <;> simp
  rw [← (hsInner_reCoord (∑ k, ((c k : ℝ) : ℂ) • hermBasis W k) 0 0).2.1, hl]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LiftAway_hsInner_comm, hl]
  simp [hb, sq]
private lemma LiftAway_norm_one_le {n : Type*} [Fintype n] [DecidableEq n] :
    ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp

/-- The embedding of the block `a` of `Fin 2 × Fin W`. -/
private def LiftAway_sel (W : ℕ) (a : Fin 2) : Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  Matrix.of fun p β => if p.1 = a ∧ p.2 = β then 1 else 0

private lemma LiftAway_norm_sel (a : Fin 2) :
    ‖LiftAway_sel W a‖ ≤ 1 ∧ ‖(LiftAway_sel W a)ᴴ‖ ≤ 1 := by
  have h1 : (LiftAway_sel W a)ᴴ * LiftAway_sel W a = 1 := by
    ext α β
    simp [LiftAway_sel, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, ite_and, eq_comm]
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (LiftAway_sel W a)
  rw [h1] at h
  have h2 := LiftAway_norm_one_le (n := Fin W)
  rw [Matrix.l2_opNorm_conjTranspose, and_self]
  nlinarith [norm_nonneg (LiftAway_sel W a)]

/-- `[[A, B], [C, D]] = Σ_{a,b} S_a X_{ab} S_b*`. -/
private lemma LiftAway_blockMat_sel (A B C D : Matrix (Fin W) (Fin W) ℂ) :
    blockMat A B C D = LiftAway_sel W 0 * A * (LiftAway_sel W 0)ᴴ +
      LiftAway_sel W 0 * B * (LiftAway_sel W 1)ᴴ + LiftAway_sel W 1 * C * (LiftAway_sel W 0)ᴴ +
      LiftAway_sel W 1 * D * (LiftAway_sel W 1)ᴴ := by
  ext ⟨a, α⟩ ⟨b, β⟩
  fin_cases a <;> fin_cases b <;>
    simp [blockMat, LiftAway_sel, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_and]

private lemma LiftAway_norm_sel_mul (a b : Fin 2) (X : Matrix (Fin W) (Fin W) ℂ) :
    ‖LiftAway_sel W a * X * (LiftAway_sel W b)ᴴ‖ ≤ ‖X‖ := by
  have h1 := (LiftAway_norm_sel (W := W) a).1
  have h2 := (LiftAway_norm_sel (W := W) b).2
  refine (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul (Matrix.l2_opNorm_mul _ _) h2
    (norm_nonneg _) (by positivity)).trans ?_)
  nlinarith [norm_nonneg X, norm_nonneg (LiftAway_sel W a)]

/-- `|[[A, B], [C, D]]|_op ≤ |A|_op + |B|_op + |C|_op + |D|_op`. -/
private lemma LiftAway_norm_blockMat (A B C D : Matrix (Fin W) (Fin W) ℂ) :
    ‖blockMat A B C D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
  rw [LiftAway_blockMat_sel]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_) <;> exact LiftAway_norm_sel_mul _ _ _

/-- The transfer matrix is `[[C, -I], [I, 0]]` with `C = z - V/g`. -/
private lemma LiftAway_transferMat_eq (g z : ℝ) (V : Matrix (Fin W) (Fin W) ℂ) :
    transferMat g (z : ℂ) V =
      blockMat ((z : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - ((g : ℂ)⁻¹) • V) (-1) 1 0 := by
  ext ⟨a, α⟩ ⟨b, β⟩
  fin_cases a <;> fin_cases b <;>
    simp [transferMat, transferFree, blockMat, Matrix.one_apply, Matrix.sub_apply, apply_ite]

/-- The inverse transfer matrix is `[[0, I], [-I, C]]`. -/
private lemma LiftAway_transferInv_eq (g z : ℝ) (V : Matrix (Fin W) (Fin W) ℂ) :
    (transferMat g (z : ℂ) V)⁻¹ =
      blockMat 0 1 (-1) ((z : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - ((g : ℂ)⁻¹) • V) := by
  rw [inv_transferMat]
  ext ⟨a, α⟩ ⟨b, β⟩
  fin_cases a <;> fin_cases b <;>
    simp [transferInv, blockMat, Matrix.one_apply, Matrix.sub_apply, apply_ite]

/-- `|T|_op, |T⁻¹|_op ≤ 2 + |z| + g⁻¹ |V|_op`. -/
private lemma LiftAway_norm_transfer {g : ℝ} (hg : 0 < g) (z : ℝ)
    (V : Matrix (Fin W) (Fin W) ℂ) :
    ‖transferMat g (z : ℂ) V‖ ≤ 2 + |z| + g⁻¹ * ‖V‖ ∧
      ‖(transferMat g (z : ℂ) V)⁻¹‖ ≤ 2 + |z| + g⁻¹ * ‖V‖ := by
  have h2 := LiftAway_norm_one_le (n := Fin W)
  have hC : ‖(z : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - ((g : ℂ)⁻¹) • V‖ ≤ |z| + g⁻¹ * ‖V‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ (le_of_eq ?_))
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left h2 (abs_nonneg z)).trans_eq (mul_one _)
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hg.le]
  have h1 : ‖(-1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := by rw [norm_neg]; exact h2
  have h0 : ‖(0 : Matrix (Fin W) (Fin W) ℂ)‖ = 0 := norm_zero
  rw [LiftAway_transferInv_eq, LiftAway_transferMat_eq]
  exact ⟨(LiftAway_norm_blockMat _ _ _ _).trans (by linarith),
    (LiftAway_norm_blockMat _ _ _ _).trans (by linarith)⟩

/-- A product of `n` matrices with `|T|_op, |T⁻¹|_op ≤ B`, `B ≥ 1`, and its inverse have
operator norm at most `B ^ n`. -/
private lemma LiftAway_norm_prod {B : ℝ} (hB : 1 ≤ B) :
    ∀ l : List (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
      (∀ T ∈ l, ‖T‖ ≤ B ∧ ‖T⁻¹‖ ≤ B) → ‖l.prod‖ ≤ B ^ l.length ∧ ‖l.prod⁻¹‖ ≤ B ^ l.length
  | [], _ => by
    simp only [List.prod_nil, inv_one, List.length_nil, pow_zero]
    exact ⟨LiftAway_norm_one_le, LiftAway_norm_one_le⟩
  | T :: l, h => by
    obtain ⟨ih1, ih2⟩ := LiftAway_norm_prod hB l fun S hS => h S (List.mem_cons_of_mem _ hS)
    obtain ⟨hT1, hT2⟩ := h T List.mem_cons_self
    simp only [List.prod_cons, List.length_cons, pow_succ']
    refine ⟨(Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hT1 ih1 (norm_nonneg _) (zero_le_one.trans hB)), ?_⟩
    rw [Matrix.mul_inv_rev]
    exact (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul ih2 hT2 (norm_nonneg _)
      (by positivity)).trans_eq (mul_comm _ _))

/-- For `g ≥ 1`, `|z| ≤ E₀` and `max_i |V_i|_op ≤ K₁`, every tail `Q_i = T_{i+1} ⋯ T_q`
satisfies `|Q_i|_op, |Q_i⁻¹|_op ≤ (2 + E₀ + K₁)^q`. -/
private lemma LiftAway_norm_tail {q : ℕ} {g z E₀ K₁ : ℝ} (hg : 1 ≤ g) (hz : |z| ≤ E₀)
    {V : Fin q → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, ‖V i‖ ≤ K₁) (i : Fin q) :
    ‖liftTail g z V i‖ ≤ (2 + E₀ + K₁) ^ q ∧ ‖(liftTail g z V i)⁻¹‖ ≤ (2 + E₀ + K₁) ^ q := by
  have hg0 : 0 < g := zero_lt_one.trans_le hg
  have hK : 0 ≤ K₁ := (norm_nonneg _).trans (hV i)
  have hE : 0 ≤ E₀ := (abs_nonneg z).trans hz
  have hB : 1 ≤ 2 + E₀ + K₁ := by linarith
  have hT : ∀ T ∈ ((List.ofFn fun j => transferMat g (z : ℂ) (V j)).drop (i.val + 1)),
      ‖T‖ ≤ 2 + E₀ + K₁ ∧ ‖T⁻¹‖ ≤ 2 + E₀ + K₁ := by
    intro T hT
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hT)
    have hv : g⁻¹ * ‖V j‖ ≤ K₁ := by
      nlinarith [norm_nonneg (V j), hV j, inv_nonneg.2 hg0.le, inv_le_one_of_one_le₀ hg]
    obtain ⟨h1, h2⟩ := LiftAway_norm_transfer hg0 z (V j)
    exact ⟨h1.trans (by linarith), h2.trans (by linarith)⟩
  obtain ⟨h1, h2⟩ := LiftAway_norm_prod hB _ hT
  have hlen : ((List.ofFn fun j => transferMat g (z : ℂ) (V j)).drop (i.val + 1)).length ≤ q :=
    by simp
  exact ⟨h1.trans (pow_le_pow_right₀ hB hlen), h2.trans (pow_le_pow_right₀ hB hlen)⟩
/-- `‖P Y S‖² ≤ |P|²_op |S|²_op ‖Y‖²`. -/
private lemma LiftAway_hsSq_mul3_le {n : Type*} [Fintype n] (P Y S : Matrix n n ℂ) :
    hsSq (P * Y * S) ≤ ‖P‖ ^ 2 * ‖S‖ ^ 2 * hsSq Y := by
  calc hsSq (P * Y * S) ≤ ‖S‖ ^ 2 * hsSq (P * Y) := LiftAway_hsSq_mul_le' _ _
    _ ≤ ‖S‖ ^ 2 * (‖P‖ ^ 2 * hsSq Y) :=
        mul_le_mul_of_nonneg_left (LiftAway_hsSq_mul_le _ _) (sq_nonneg _)
    _ = _ := by ring

/-- `|A B|²_op ≤ κ⁴` for `|A|_op, |B|_op ≤ κ`. -/
private lemma LiftAway_norm_mul_sq {n : Type*} [Fintype n] {A B : Matrix n n ℂ} {κ : ℝ}
    (hA : ‖A‖ ≤ κ) (hB : ‖B‖ ≤ κ) : ‖A * B‖ ^ 2 ≤ κ ^ 4 := by
  have h0 : ‖A‖ * ‖B‖ ≤ κ * κ := mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA)
  exact (pow_le_pow_left₀ (norm_nonneg _) ((Matrix.l2_opNorm_mul A B).trans h0) 2).trans_eq
    (by ring)

/-- (10.32) [lg:eq:A-derivative-bounds] for one pair of inputs, in adjoint form: for
`X(B) = A₁ N(B) A₂`, `Y(K) = A₃ N(K) A₄` with `|A_k|_op ≤ κ`,
`Σ_{α,β} ⟨Z, X(H_β) Y(H_α) - Y(H_α) X(H_β)⟩² ≤ 4 κ⁸ W ‖Z‖²`. -/
private lemma LiftAway_pair_adj {A₁ A₂ A₃ A₄ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {κ : ℝ}
    (h₁ : ‖A₁‖ ≤ κ) (h₂ : ‖A₂‖ ≤ κ) (h₃ : ‖A₃‖ ≤ κ) (h₄ : ‖A₄‖ ≤ κ)
    (Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∑ a, ∑ b, hsInner Z (A₁ * blockMat 0 0 (hermBasis W b) 0 * A₂ *
        (A₃ * blockMat 0 0 (hermBasis W a) 0 * A₄) -
      A₃ * blockMat 0 0 (hermBasis W a) 0 * A₄ *
        (A₁ * blockMat 0 0 (hermBasis W b) 0 * A₂)) ^ 2 ≤ 4 * κ ^ 8 * W * hsSq Z := by
  have hκ : 0 ≤ κ := (norm_nonneg _).trans h₁
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  set N := fun k => (blockMat 0 0 (hermBasis W k) 0 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    with hN
  have hc : ∀ {A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}, ‖A‖ ≤ κ → ‖Aᴴ‖ ^ 2 ≤ κ ^ 2 :=
    fun h => pow_le_pow_left₀ (norm_nonneg _) (by rwa [Matrix.l2_opNorm_conjTranspose]) 2
  have hconj : ∀ (U V : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
      hsSq (U * Vᴴ) = hsSq (V * Uᴴ) := fun U V => by
    rw [← LiftAway_hsSq_conj (U * Vᴴ), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hZ : ∀ {P S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}, ‖P‖ ≤ κ → ‖S‖ ≤ κ →
      hsSq (Pᴴ * Z * Sᴴ) ≤ κ ^ 4 * hsSq Z := fun hP hS =>
    (LiftAway_hsSq_mul3_le _ _ _).trans (mul_le_mul_of_nonneg_right
      ((mul_le_mul (hc hP) (hc hS) (sq_nonneg _) (sq_nonneg _)).trans_eq (by ring))
      (LiftAway_hsSq_nonneg Z))
  have t1 : ∀ a, ∑ b, hsInner Z (A₁ * N b * (A₂ * A₃ * N a * A₄)) ^ 2 ≤
      κ ^ 4 * hsSq (N a * (A₁ᴴ * Z * A₄ᴴ)ᴴ) := by
    intro a
    refine (LiftAway_sum_inner_N Z A₁ (A₂ * A₃ * N a * A₄)).trans ?_
    have e : A₁ᴴ * Z * (A₂ * A₃ * N a * A₄)ᴴ = ((A₁ᴴ * Z * A₄ᴴ) * (N a)ᴴ) * (A₂ * A₃)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have h2 : ‖(A₂ * A₃)ᴴ‖ ^ 2 ≤ κ ^ 4 := by
      rw [Matrix.l2_opNorm_conjTranspose]; exact LiftAway_norm_mul_sq h₂ h₃
    rw [e, hconj (N a) (A₁ᴴ * Z * A₄ᴴ)]
    exact (LiftAway_hsSq_mul_le' _ _).trans
      (mul_le_mul_of_nonneg_right h2 (LiftAway_hsSq_nonneg _))
  have t2 : ∀ a, ∑ b, hsInner Z ((A₃ * N a * A₄ * A₁) * N b * A₂) ^ 2 ≤
      κ ^ 4 * hsSq ((A₃ᴴ * Z * A₂ᴴ)ᴴ * N a) := by
    intro a
    refine (LiftAway_sum_inner_N Z (A₃ * N a * A₄ * A₁) A₂).trans ?_
    have e : (A₃ * N a * A₄ * A₁)ᴴ * Z * A₂ᴴ = (A₄ * A₁)ᴴ * ((N a)ᴴ * (A₃ᴴ * Z * A₂ᴴ)) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have h2 : ‖(A₄ * A₁)ᴴ‖ ^ 2 ≤ κ ^ 4 := by
      rw [Matrix.l2_opNorm_conjTranspose]; exact LiftAway_norm_mul_sq h₄ h₁
    have h3 : hsSq ((N a)ᴴ * (A₃ᴴ * Z * A₂ᴴ)) = hsSq ((A₃ᴴ * Z * A₂ᴴ)ᴴ * N a) := by
      rw [← LiftAway_hsSq_conj ((A₃ᴴ * Z * A₂ᴴ)ᴴ * N a), Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    rw [e, ← h3]
    exact (LiftAway_hsSq_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right h2 (LiftAway_hsSq_nonneg _))
  have hsplit : ∀ a b, hsInner Z (A₁ * N b * A₂ * (A₃ * N a * A₄) -
      A₃ * N a * A₄ * (A₁ * N b * A₂)) ^ 2 ≤
      2 * hsInner Z (A₁ * N b * (A₂ * A₃ * N a * A₄)) ^ 2 +
        2 * hsInner Z ((A₃ * N a * A₄ * A₁) * N b * A₂) ^ 2 := by
    intro a b
    rw [show A₁ * N b * A₂ * (A₃ * N a * A₄) = A₁ * N b * (A₂ * A₃ * N a * A₄) by
      simp only [Matrix.mul_assoc], show A₃ * N a * A₄ * (A₁ * N b * A₂) =
      (A₃ * N a * A₄ * A₁) * N b * A₂ by simp only [Matrix.mul_assoc], LiftAway_hsInner_sub]
    nlinarith [sq_nonneg (hsInner Z (A₁ * N b * (A₂ * A₃ * N a * A₄)) +
      hsInner Z ((A₃ * N a * A₄ * A₁) * N b * A₂))]
  have h1 := (LiftAway_sum_N (W := W) (A₁ᴴ * Z * A₄ᴴ)ᴴ).2
  have h2 := (LiftAway_sum_N (W := W) (A₃ᴴ * Z * A₂ᴴ)ᴴ).1
  rw [LiftAway_hsSq_conj] at h1 h2
  have hk : 0 ≤ 2 * κ ^ 4 := by positivity
  calc _ ≤ ∑ a, (2 * (κ ^ 4 * hsSq (N a * (A₁ᴴ * Z * A₄ᴴ)ᴴ)) +
          2 * (κ ^ 4 * hsSq ((A₃ᴴ * Z * A₂ᴴ)ᴴ * N a))) := by
        refine Finset.sum_le_sum fun a _ => (Finset.sum_le_sum fun b _ => hsplit a b).trans ?_
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        linarith [t1 a, t2 a]
    _ = 2 * κ ^ 4 * ∑ a, hsSq (N a * (A₁ᴴ * Z * A₄ᴴ)ᴴ) +
          2 * κ ^ 4 * ∑ a, hsSq ((A₃ᴴ * Z * A₂ᴴ)ᴴ * N a) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    _ ≤ 2 * κ ^ 4 * (W * (κ ^ 4 * hsSq Z)) + 2 * κ ^ 4 * (W * (κ ^ 4 * hsSq Z)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left (hZ h₁ h₄) hW)) hk)
          (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left (hZ h₃ h₂) hW)) hk)
    _ = 4 * κ ^ 8 * W * hsSq Z := by ring

/-- (10.32) [lg:eq:A-derivative-bounds] for one pair of inputs: for `X(B) = A₁ N(B) A₂`,
`Y(K) = A₃ N(K) A₄` with `|A_k|_op ≤ κ`, `Σ_α ‖X(R) Y(H_α) - Y(H_α) X(R)‖² ≤ 4 κ⁸ W ‖R‖²`. -/
private lemma LiftAway_pair_dir {A₁ A₂ A₃ A₄ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {κ : ℝ}
    (h₁ : ‖A₁‖ ≤ κ) (h₂ : ‖A₂‖ ≤ κ) (h₃ : ‖A₃‖ ≤ κ) (h₄ : ‖A₄‖ ≤ κ)
    (R : Matrix (Fin W) (Fin W) ℂ) :
    ∑ a, hsSq (A₁ * blockMat 0 0 R 0 * A₂ * (A₃ * blockMat 0 0 (hermBasis W a) 0 * A₄) -
      A₃ * blockMat 0 0 (hermBasis W a) 0 * A₄ * (A₁ * blockMat 0 0 R 0 * A₂)) ≤
        4 * κ ^ 8 * W * hsSq R := by
  have hκ : 0 ≤ κ := (norm_nonneg _).trans h₁
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  set N := fun k => (blockMat 0 0 (hermBasis W k) 0 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    with hN
  set NR : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := blockMat 0 0 R 0 with hNR
  have hsq : ∀ {A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}, ‖A‖ ≤ κ → ‖A‖ ^ 2 ≤ κ ^ 2 :=
    fun h => pow_le_pow_left₀ (norm_nonneg _) h 2
  have hR : ∀ {P S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}, ‖P‖ ^ 2 * ‖S‖ ^ 2 ≤ κ ^ 6 →
      hsSq (P * NR * S) ≤ κ ^ 6 * hsSq R := fun h => by
    refine (LiftAway_hsSq_mul3_le _ _ _).trans ?_
    rw [hNR, LiftAway_hsSq_N]
    exact mul_le_mul_of_nonneg_right h (LiftAway_hsSq_nonneg R)
  have hsplit : ∀ a, hsSq (A₁ * NR * A₂ * (A₃ * N a * A₄) - A₃ * N a * A₄ * (A₁ * NR * A₂)) ≤
      2 * (κ ^ 2 * hsSq ((A₁ * NR * (A₂ * A₃)) * N a)) +
        2 * (κ ^ 2 * hsSq (N a * ((A₄ * A₁) * NR * A₂))) := by
    intro a
    rw [show A₁ * NR * A₂ * (A₃ * N a * A₄) = (A₁ * NR * (A₂ * A₃)) * N a * A₄ by
      simp only [Matrix.mul_assoc], show A₃ * N a * A₄ * (A₁ * NR * A₂) =
      A₃ * (N a * ((A₄ * A₁) * NR * A₂)) by simp only [Matrix.mul_assoc]]
    refine (LiftAway_hsSq_sub_le _ _).trans ?_
    have t1 := (LiftAway_hsSq_mul_le' A₄ ((A₁ * NR * (A₂ * A₃)) * N a)).trans
      (mul_le_mul_of_nonneg_right (hsq h₄) (LiftAway_hsSq_nonneg _))
    have t2 := (LiftAway_hsSq_mul_le A₃ (N a * ((A₄ * A₁) * NR * A₂))).trans
      (mul_le_mul_of_nonneg_right (hsq h₃) (LiftAway_hsSq_nonneg _))
    linarith
  have hk : 0 ≤ 2 * κ ^ 2 := by positivity
  calc _ ≤ ∑ a, (2 * (κ ^ 2 * hsSq ((A₁ * NR * (A₂ * A₃)) * N a)) +
        2 * (κ ^ 2 * hsSq (N a * ((A₄ * A₁) * NR * A₂)))) := Finset.sum_le_sum fun a _ => hsplit a
    _ = 2 * κ ^ 2 * ∑ a, hsSq ((A₁ * NR * (A₂ * A₃)) * N a) +
          2 * κ ^ 2 * ∑ a, hsSq (N a * ((A₄ * A₁) * NR * A₂)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    _ ≤ 2 * κ ^ 2 * (W * (κ ^ 6 * hsSq R)) + 2 * κ ^ 2 * (W * (κ ^ 6 * hsSq R)) :=
        add_le_add (mul_le_mul_of_nonneg_left ((LiftAway_sum_N _).1.trans
          (mul_le_mul_of_nonneg_left (hR ((mul_le_mul (hsq h₁) (LiftAway_norm_mul_sq h₂ h₃)
            (sq_nonneg _) (sq_nonneg _)).trans_eq (by ring))) hW)) hk)
          (mul_le_mul_of_nonneg_left ((LiftAway_sum_N _).2.trans
          (mul_le_mul_of_nonneg_left (hR ((mul_le_mul (LiftAway_norm_mul_sq h₄ h₁) (hsq h₂)
            (sq_nonneg _) (by positivity)).trans_eq (by ring))) hW)) hk)
    _ = 4 * κ ^ 8 * W * hsSq R := by ring

end LiftAwayBlock
section LiftAwayTail

variable {W q : ℕ}

/-- The tail `T_k ⋯ T_q` (0-indexed, `k ≤ q`), `liftTail g z V i` at `k = i + 1`. -/
private def LiftAway_tl (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) (k : ℕ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ((List.ofFn fun j => transferMat g (z : ℂ) (V j)).drop k).prod

private lemma LiftAway_tl_cons (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) {k : ℕ}
    (hk : k < q) : LiftAway_tl g z V k = transferMat g (z : ℂ) (V ⟨k, hk⟩) *
      LiftAway_tl g z V (k + 1) := by
  unfold LiftAway_tl
  rw [List.drop_eq_getElem_cons (by simpa using hk)]
  simp [List.getElem_ofFn]

private lemma LiftAway_tl_top (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    LiftAway_tl g z V q = 1 := by
  unfold LiftAway_tl
  rw [List.drop_eq_nil_of_le (by simp)]
  rfl

private lemma LiftAway_tl_unit (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) (k : ℕ) :
    IsUnit (LiftAway_tl g z V k).det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  refine List.prod_isUnit fun M hM => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hM)
  exact (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_right_inverse (transferMat_mul_transferInv g _ _))

/-- `T(A + s B) = T(A) + s T(A) g⁻¹ N(B)` with `N(B) = [[0, 0], [B, 0]]`. -/
private lemma LiftAway_transferMat_add (g z s : ℝ) (A B : Matrix (Fin W) (Fin W) ℂ) :
    transferMat g (z : ℂ) (A + s • B) = transferMat g (z : ℂ) A +
      s • (transferMat g (z : ℂ) A * (((g : ℂ)⁻¹) • blockMat 0 0 B 0)) := by
  have hN : transferMat g (z : ℂ) A * (((g : ℂ)⁻¹) • blockMat 0 0 B 0) =
      -(((g : ℂ)⁻¹) • (!![1, 0; 0, 0] ⊗ₖ B)) := by
    rw [Matrix.mul_smul, ← smul_neg]
    congr 1
    ext ⟨a, α⟩ ⟨b, β⟩
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, blockMat, transferMat,
        transferFree, Matrix.one_apply]
  rw [hN]
  ext ⟨a, α⟩ ⟨b, β⟩
  simp [transferMat]
  ring

variable (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) (l : Fin q)
  (K : Matrix (Fin W) (Fin W) ℂ)

/-- The coefficient `a = g⁻¹ Q_l⁻¹ N(K) Q_l`. -/
private def LiftAway_a : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ((g : ℂ)⁻¹) • ((liftTail g z V l)⁻¹ * blockMat 0 0 K 0 * liftTail g z V l)

/-- Tails beyond `l` do not see the perturbation of `V_l`. -/
private lemma LiftAway_tl_above (s : ℝ) : ∀ d k, k + d = q → l.val < k →
    LiftAway_tl g z (V + s • (Pi.single l K : Fin q → Matrix (Fin W) (Fin W) ℂ)) k =
      LiftAway_tl g z V k
  | 0, k, h, _ => by obtain rfl : k = q := (by omega); rw [LiftAway_tl_top, LiftAway_tl_top]
  | d + 1, k, h, hl => by
    have hk : k < q := by omega
    rw [LiftAway_tl_cons _ _ _ hk, LiftAway_tl_cons _ _ _ hk,
      LiftAway_tl_above s d (k + 1) (by omega) (by omega)]
    have hne : (⟨k, hk⟩ : Fin q) ≠ l := fun h' => by rw [← h'] at hl; exact lt_irrefl _ hl
    simp [hne]

/-- Tails up to `l` move as `Q(s) = Q (1 + s a)`. -/
private lemma LiftAway_tl_below (s : ℝ) : ∀ d k, k + d = l.val →
    LiftAway_tl g z (V + s • (Pi.single l K : Fin q → Matrix (Fin W) (Fin W) ℂ)) k =
      LiftAway_tl g z V k * (1 + s • LiftAway_a g z V l K)
  | 0, k, h => by
    have hk : k < q := by omega
    have hkl : (⟨k, hk⟩ : Fin q) = l := Fin.ext (by simpa using h)
    rw [LiftAway_tl_cons _ _ _ hk, LiftAway_tl_cons _ _ _ hk,
      LiftAway_tl_above g z V l K s (q - (k + 1)) (k + 1) (by omega) (by omega)]
    have hV : (V + s • (Pi.single l K : Fin q → Matrix (Fin W) (Fin W) ℂ)) ⟨k, hk⟩ =
        V ⟨k, hk⟩ + s • K := by simp [hkl]
    have hQ : liftTail g z V l = LiftAway_tl g z V (k + 1) := by rw [← hkl]; rfl
    rw [hV, LiftAway_transferMat_add, LiftAway_a, hQ]
    have hinv := Matrix.mul_nonsing_inv _ (LiftAway_tl_unit g z V (k + 1))
    rw [hkl]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (LiftAway_tl g z V (k + 1)) _ _, hinv, Matrix.one_mul]
  | d + 1, k, h => by
    have hk : k < q := by omega
    rw [LiftAway_tl_cons _ _ _ hk, LiftAway_tl_cons _ _ _ hk,
      LiftAway_tl_below s d (k + 1) (by omega)]
    have hne : (⟨k, hk⟩ : Fin q) ≠ l := fun h' => by rw [← h'] at h; simp at h
    simp [hne, Matrix.mul_assoc]

end LiftAwayTail
section LiftAwayDeriv

variable {W q : ℕ}

/-- The derivative of the inverse of a complex matrix family at an invertible point. -/
private lemma LiftAway_hasDerivAt_inv {n : Type*} [Fintype n] [DecidableEq n]
    {G : ℝ → Matrix n n ℂ} {G' : Matrix n n ℂ} {t : ℝ} (hG : HasDerivAt G G' t)
    (hu : IsUnit (G t)) : HasDerivAt (fun s => (G s)⁻¹) (-((G t)⁻¹ * G' * (G t)⁻¹)) t := by
  obtain ⟨u, hu⟩ := hu
  have h1 : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑u⁻¹ ↑u⁻¹) (G t) :=
    hu ▸ hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have h2 := h1.comp_hasDerivAt t hG
  have e1 : ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = (G t)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  simp only [e1, neg_apply, ContinuousLinearMap.mulLeftRight_apply] at h2
  simpa only [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using h2

/-- `d/ds [(Q (1 + s a))⁻¹ N Q (1 + s a)] = X a - a X` at `s = 0`, `X = Q⁻¹ N Q`. -/
private lemma LiftAway_hasDerivAt_conj {n : Type*} [Fintype n] [DecidableEq n]
    {Q : Matrix n n ℂ} (hQ : IsUnit Q.det) (N a : Matrix n n ℂ) :
    HasDerivAt (fun s : ℝ => (Q * (1 + s • a))⁻¹ * N * (Q * (1 + s • a)))
      (Q⁻¹ * N * Q * a - a * (Q⁻¹ * N * Q)) 0 := by
  have hG : HasDerivAt (fun s : ℝ => Q * (1 + s • a)) (Q * a) 0 := by
    simpa [Matrix.mul_add, Matrix.mul_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (Q * a)).const_add Q
  have h0 : Q * (1 + (0 : ℝ) • a) = Q := by simp
  have hu : IsUnit (Q * (1 + (0 : ℝ) • a)) := by
    rw [h0]; exact (Matrix.isUnit_iff_isUnit_det _).2 hQ
  have hI := LiftAway_hasDerivAt_inv hG hu
  rw [h0] at hI
  have hP := (hI.mul_const N).mul hG
  rw [h0] at hP
  convert hP using 1
  have hinv := Matrix.nonsing_inv_mul _ hQ
  simp only [Matrix.neg_mul, Matrix.mul_assoc, neg_add_eq_sub]
  rw [← Matrix.mul_assoc Q⁻¹ Q, hinv, Matrix.one_mul]

/-- The derivative of `𝒜(R)` along `V ↦ V + s ι_l K`:
`g⁻¹ Σ_{i < l} (X_i a - a X_i)`, `X_i = Q_i⁻¹ N(R_i) Q_i`, `a = g⁻¹ Q_l⁻¹ N(K) Q_l`. -/
private def LiftAway_dA (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) (l : Fin q)
    (K : Matrix (Fin W) (Fin W) ℂ) (R : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ((g : ℂ)⁻¹) • ∑ i, if i < l then
    (liftTail g z V i)⁻¹ * blockMat 0 0 (R i) 0 * liftTail g z V i * LiftAway_a g z V l K -
      LiftAway_a g z V l K * ((liftTail g z V i)⁻¹ * blockMat 0 0 (R i) 0 * liftTail g z V i)
    else 0

/-- (10.8) [eq:c-product-map] differentiated in the inputs: `s ↦ 𝒜_{V + s ι_l K}(R)` has
derivative `LiftAway_dA` at `s = 0`. -/
private lemma LiftAway_hasDerivAt_prodDiff (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ)
    (l : Fin q) (K : Matrix (Fin W) (Fin W) ℂ) (R : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    HasDerivAt (fun s : ℝ => prodDiff g z (V + s • (Pi.single l K :
      Fin q → Matrix (Fin W) (Fin W) ℂ)) R) (LiftAway_dA g z V l K R) 0 := by
  unfold prodDiff LiftAway_dA
  refine HasDerivAt.const_smul ((g : ℂ)⁻¹) (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => ?_)
  by_cases hi : i < l
  · simp only [hi, ite_true]
    have e : ∀ s : ℝ, liftTail g z (V + s • (Pi.single l K : Fin q → Matrix (Fin W) (Fin W) ℂ)) i =
        liftTail g z V i * (1 + s • LiftAway_a g z V l K) := fun s =>
      LiftAway_tl_below g z V l K s (l.val - (i.val + 1)) (i.val + 1) (by omega)
    simp only [e]
    exact LiftAway_hasDerivAt_conj (LiftAway_tl_unit g z V (i.val + 1)) _ _
  · simp only [hi, ite_false]
    have e : ∀ s : ℝ, liftTail g z (V + s • (Pi.single l K : Fin q → Matrix (Fin W) (Fin W) ℂ)) i =
        liftTail g z V i := fun s =>
      LiftAway_tl_above g z V l K s (q - (i.val + 1)) (i.val + 1) (by omega)
        (by rw [not_lt, Fin.le_def] at hi; omega)
    simp only [e]
    exact hasDerivAt_const _ _

end LiftAwayDeriv
/-- A real matrix family is differentiable when its entries are. -/
private lemma LiftAway_hasDerivAt_matrix {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {A : ℝ → Matrix m n ℝ} {A' : Matrix m n ℝ} {t : ℝ}
    (h : ∀ a b, HasDerivAt (fun s => A s a b) (A' a b) t) : HasDerivAt A A' t := by
  let e : (m → n → ℝ) ≃L[ℝ] Matrix m n ℝ := (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  have h1 : HasDerivAt (fun s => e.symm (A s)) (e.symm A') t :=
    hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => h a b
  have h2 := e.hasFDerivAt.comp_hasDerivAt t h1
  simpa [Function.comp_def] using h2

/-- The real coordinates of a differentiable complex matrix family are differentiable. -/
private lemma LiftAway_hasDerivAt_reCoord {n : Type*} [Fintype n] [DecidableEq n]
    {F : ℝ → Matrix n n ℂ} {F' : Matrix n n ℂ} {t : ℝ} (hF : HasDerivAt F F' t)
    (p : Fin 2 × n × n) : HasDerivAt (fun s => reCoord (F s) p) (reCoord F' p) t := by
  let L : Matrix n n ℂ →ₗ[ℝ] ℝ :=
    { toFun := fun A => reCoord A p
      map_add' := fun A B => by
        unfold reCoord; split_ifs <;> simp
      map_smul' := fun c A => by
        unfold reCoord; split_ifs <;> simp }
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t hF
section LiftAwayMatDeriv

variable {W q : ℕ}

/-- The derivative of the real matrix `prodDiffMat` along `V ↦ V + s ι_l K`. -/
private def LiftAway_Pd (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) (l : Fin q)
    (K : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W)) (Fin q × Fin W × Fin W) ℝ :=
  Matrix.of fun p r => reCoord (LiftAway_dA g z V l K (Pi.single r.1 (hermBasis W r.2))) p

/-- `s ↦ hermLiftMat(V + s ι_l K)` has derivative `[(D 𝒜)*; 0]` at `s = 0`. -/
private lemma LiftAway_hasDerivAt_hermLiftMat (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ)
    (l : Fin q) (K : Matrix (Fin W) (Fin W) ℂ) :
    HasDerivAt (fun s : ℝ => hermLiftMat g z (V + s • (Pi.single l K :
      Fin q → Matrix (Fin W) (Fin W) ℂ)))
      (Matrix.fromRows (LiftAway_Pd g z V l K)ᵀ 0) 0 := by
  refine LiftAway_hasDerivAt_matrix fun a b => ?_
  cases a with
  | inl r =>
    simp only [hermLiftMat, Matrix.fromRows_apply_inl, Matrix.transpose_apply, prodDiffMat,
      LiftAway_Pd, Matrix.of_apply]
    exact LiftAway_hasDerivAt_reCoord (LiftAway_hasDerivAt_prodDiff g z V l K _) b
  | inr p =>
    simp only [hermLiftMat, Matrix.fromRows_apply_inr, Matrix.zero_apply]
    exact hasDerivAt_const _ _

end LiftAwayMatDeriv
section LiftAwayLsq

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private lemma LiftAway_sum_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) : ∑ i, v i ^ 2 = v ⬝ᵥ v := by
  simp [dotProduct, sq]

omit [DecidableEq m] [DecidableEq n] in
private lemma LiftAway_dot_mulVec (A : Matrix m n ℝ) (w : m → ℝ) (x : n → ℝ) :
    w ⬝ᵥ (A *ᵥ x) = (Aᵀ *ᵥ w) ⬝ᵥ x := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- `1 - A 𝒥` is a contraction: `‖(1 - A 𝒥) v‖² ≤ ‖v‖²`. -/
private lemma LiftAway_proj_le {A : Matrix m n ℝ} (hu : IsUnit (Aᵀ * A).det) (v : m → ℝ) :
    ∑ i, ((1 - A * lsqInv A) *ᵥ v) i ^ 2 ≤ ∑ i, v i ^ 2 := by
  set u := lsqInv A *ᵥ v with hudef
  set w := (1 - A * lsqInv A) *ᵥ v with hw
  have hwv : w = v - A *ᵥ u := by
    rw [hw, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  have hAw : Aᵀ *ᵥ w = 0 := by
    rw [hwv, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hudef, Matrix.mulVec_mulVec, lsqInv,
      ← Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, sub_self]
  have hv : v = w + A *ᵥ u := by rw [hwv, sub_add_cancel]
  rw [LiftAway_sum_sq, LiftAway_sum_sq]
  have h1 : v ⬝ᵥ v = w ⬝ᵥ w + (A *ᵥ u) ⬝ᵥ (A *ᵥ u) := by
    have h0 : w ⬝ᵥ (A *ᵥ u) = 0 := by rw [LiftAway_dot_mulVec, hAw, zero_dotProduct]
    conv_lhs => rw [hv]
    rw [add_dotProduct, dotProduct_add, dotProduct_add, h0, dotProduct_comm (A *ᵥ u) w, h0]
    ring
  have h2 : 0 ≤ (A *ᵥ u) ⬝ᵥ (A *ᵥ u) := by
    rw [← LiftAway_sum_sq]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

omit [DecidableEq m] in
/-- `‖𝒥ᵀ u‖² ≤ τ⁻² ‖u‖²` for `‖A x‖ ≥ τ ‖x‖`. -/
private lemma LiftAway_Jt_le {A : Matrix m n ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hA : ∀ x : n → ℝ, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A *ᵥ x) j ^ 2) (u : n → ℝ) :
    ∑ i, ((lsqInv A)ᵀ *ᵥ u) i ^ 2 ≤ (τ ^ 2)⁻¹ * ∑ i, u i ^ 2 := by
  set w := (lsqInv A)ᵀ *ᵥ u with hw
  have hJ := (lsqInv_spec hτ hA).2.1 w
  have e : w ⬝ᵥ w = (lsqInv A *ᵥ w) ⬝ᵥ u := by
    conv_lhs => rw [hw]
    rw [LiftAway_dot_mulVec, Matrix.transpose_transpose]
  have cs : ((lsqInv A *ᵥ w) ⬝ᵥ u) ^ 2 ≤ ((lsqInv A *ᵥ w) ⬝ᵥ (lsqInv A *ᵥ w)) * (u ⬝ᵥ u) := by
    simpa [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (lsqInv A *ᵥ w) u
  rw [LiftAway_sum_sq, LiftAway_sum_sq] at hJ
  rw [LiftAway_sum_sq, LiftAway_sum_sq]
  have hw0 : 0 ≤ w ⬝ᵥ w := by rw [← LiftAway_sum_sq]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hu0 : 0 ≤ u ⬝ᵥ u := by rw [← LiftAway_sum_sq]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : (w ⬝ᵥ w) ^ 2 ≤ (τ ^ 2)⁻¹ * (w ⬝ᵥ w) * (u ⬝ᵥ u) := by
    rw [e]
    refine cs.trans ?_
    rw [← e]
    exact mul_le_mul_of_nonneg_right hJ hu0
  rcases hw0.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

/-- (10.22) [eq:c-lift-derivative] split into its two terms:
`‖((1 - A 𝒥) A' (AᵀA)⁻¹ - 𝒥ᵀ A'ᵀ 𝒥ᵀ) y‖² ≤ 2 ‖A' (AᵀA)⁻¹ y‖² + 2 τ⁻² ‖A'ᵀ 𝒥ᵀ y‖²`. -/
private lemma LiftAway_deriv_split {A A' : Matrix m n ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hA : ∀ x : n → ℝ, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A *ᵥ x) j ^ 2) (y : n → ℝ) :
    ∑ j, (((1 - A * lsqInv A) * A' * (Aᵀ * A)⁻¹ - (lsqInv A)ᵀ * A'ᵀ * (lsqInv A)ᵀ) *ᵥ y) j ^ 2 ≤
      2 * ∑ j, (A' *ᵥ ((Aᵀ * A)⁻¹ *ᵥ y)) j ^ 2 +
        2 * ((τ ^ 2)⁻¹ * ∑ i, (A'ᵀ *ᵥ ((lsqInv A)ᵀ *ᵥ y)) i ^ 2) := by
  have hu : IsUnit (Aᵀ * A).det := by
    have h1 := (lsqInv_spec hτ hA).1
    rw [lsqInv, Matrix.mul_assoc] at h1
    exact Matrix.isUnit_det_of_left_inverse h1
  have e : ((1 - A * lsqInv A) * A' * (Aᵀ * A)⁻¹ - (lsqInv A)ᵀ * A'ᵀ * (lsqInv A)ᵀ) *ᵥ y =
      (1 - A * lsqInv A) *ᵥ (A' *ᵥ ((Aᵀ * A)⁻¹ *ᵥ y)) -
        (lsqInv A)ᵀ *ᵥ (A'ᵀ *ᵥ ((lsqInv A)ᵀ *ᵥ y)) := by
    simp only [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e]
  set a := (1 - A * lsqInv A) *ᵥ (A' *ᵥ ((Aᵀ * A)⁻¹ *ᵥ y))
  set b := (lsqInv A)ᵀ *ᵥ (A'ᵀ *ᵥ ((lsqInv A)ᵀ *ᵥ y))
  have h1 : ∑ j, (a - b) j ^ 2 ≤ 2 * ∑ j, a j ^ 2 + 2 * ∑ j, b j ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => by
      simp only [Pi.sub_apply]
      nlinarith [sq_nonneg (a j + b j)]
  have ha := LiftAway_proj_le hu (A' *ᵥ ((Aᵀ * A)⁻¹ *ᵥ y))
  have hb := LiftAway_Jt_le hτ hA (A'ᵀ *ᵥ ((lsqInv A)ᵀ *ᵥ y))
  linarith

end LiftAwayLsq
section LiftAwayBound

variable {W q : ℕ}

/-- `X_i(B) = Q_i⁻¹ N(B) Q_i`, `N(B) = [[0, 0], [B, 0]]`. -/
private def LiftAway_X (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) (i : Fin q)
    (B : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (liftTail g z V i)⁻¹ * blockMat 0 0 B 0 * liftTail g z V i

private lemma LiftAway_blockMat_zero :
    (blockMat 0 0 0 0 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) = 0 := by
  ext ⟨a, α⟩ ⟨b, β⟩
  fin_cases a <;> fin_cases b <;> rfl

/-- At the data `ι_i B`, `D_{ι_l K} 𝒜(ι_i B) = g⁻² [i < l] (X_i(B) X_l(K) - X_l(K) X_i(B))`. -/
private lemma LiftAway_dA_single (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) (l i : Fin q)
    (K B : Matrix (Fin W) (Fin W) ℂ) :
    LiftAway_dA g z V l K (Pi.single i B) = ((g⁻¹ ^ 2 : ℝ) : ℂ) • (if i < l then
      LiftAway_X g z V i B * LiftAway_X g z V l K - LiftAway_X g z V l K * LiftAway_X g z V i B
      else 0) := by
  unfold LiftAway_dA
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb, LiftAway_blockMat_zero]) (by simp)]
  simp only [Pi.single_eq_same, LiftAway_a, LiftAway_X]
  split_ifs
  · rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, smul_smul]; push_cast; ring_nf
  · simp

/-- The real coordinates of `D 𝒜` paired with `x`: `(P'ᵀ x)_r = ⟨D 𝒜(ι_r H), ofReCoord x⟩`. -/
private lemma LiftAway_Pd_transpose_mulVec (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ)
    (l : Fin q) (K : Matrix (Fin W) (Fin W) ℂ)
    (x : Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W) → ℝ) (r : Fin q × Fin W × Fin W) :
    ((LiftAway_Pd g z V l K)ᵀ *ᵥ x) r =
      hsInner (ofReCoord x) (LiftAway_dA g z V l K (Pi.single r.1 (hermBasis W r.2))) := by
  have h := (hsInner_reCoord (LiftAway_dA g z V l K (Pi.single r.1 (hermBasis W r.2)))
    (ofReCoord x : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) x).2.2.2.2
  rw [(hsInner_reCoord (ofReCoord x : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) 0 x).2.2.2.1] at h
  rw [LiftAway_hsInner_comm, ← h]
  simp [Matrix.mulVec, dotProduct, LiftAway_Pd, Matrix.transpose_apply]

private lemma LiftAway_sum_sq_ofRe {k l : Type*} [Fintype k] [Fintype l]
    (x : Fin 2 × k × l → ℝ) : ∑ p, x p ^ 2 = hsSq (ofReCoord x : Matrix k l ℂ) := by
  rw [← (hsInner_reCoord (ofReCoord x : Matrix k l ℂ) 0 x).2.1,
    ← (hsInner_reCoord (ofReCoord x : Matrix k l ℂ) _ x).2.2.2.2,
    (hsInner_reCoord (ofReCoord x : Matrix k l ℂ) 0 x).2.2.2.1]
  simp [sq]

/-- (10.32) [lg:eq:A-derivative-bounds] in adjoint form: for `g ≥ 1`, `|z| ≤ E₀`,
`max_i ‖V_i‖ ≤ K₁`, `Σ_{(l,α)} ‖(D_{l,α} 𝒜)* x‖² ≤ 4 q² κ⁸ W g⁻⁴ ‖x‖²`,
`κ = (2 + E₀ + K₁)^q`. -/
private lemma LiftAway_bound_adj {g z E₀ K₁ : ℝ} (hg : 1 ≤ g) (hz : |z| ≤ E₀)
    {V : Fin q → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, ‖V i‖ ≤ K₁)
    (x : Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W) → ℝ) :
    ∑ j : Fin q × Fin W × Fin W, ∑ r, ((LiftAway_Pd g z V j.1 (hermBasis W j.2))ᵀ *ᵥ x) r ^ 2 ≤
      4 * q ^ 2 * ((2 + E₀ + K₁) ^ q) ^ 8 * W * g⁻¹ ^ 4 * ∑ p, x p ^ 2 := by
  set κ := (2 + E₀ + K₁) ^ q with hκ
  set Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := ofReCoord x with hZ
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hZ0 := LiftAway_hsSq_nonneg Z
  rw [LiftAway_sum_sq_ofRe x, ← hZ]
  simp only [LiftAway_Pd_transpose_mulVec, LiftAway_dA_single, ← hZ, LiftAway_hsInner_smul]
  rw [Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
    Fintype.sum_prod_type _).trans_le ?_
  have key : ∀ l i : Fin q, ∑ a : Fin W × Fin W, ∑ b : Fin W × Fin W,
      (g⁻¹ ^ 2 * hsInner Z (if i < l then LiftAway_X g z V i (hermBasis W b) *
        LiftAway_X g z V l (hermBasis W a) - LiftAway_X g z V l (hermBasis W a) *
          LiftAway_X g z V i (hermBasis W b) else 0)) ^ 2 ≤
        g⁻¹ ^ 4 * (4 * κ ^ 8 * W * hsSq Z) := by
    intro l i
    by_cases hi : i < l
    · simp only [hi, ite_true, mul_pow]
      rw [← pow_mul, show 2 * 2 = 4 from rfl]
      simp only [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      obtain ⟨h₁, h₂⟩ := LiftAway_norm_tail hg hz hV i
      obtain ⟨h₃, h₄⟩ := LiftAway_norm_tail hg hz hV l
      exact LiftAway_pair_adj h₂ h₁ h₄ h₃ Z
    · simp only [hi, ite_false]; simp [hsInner]; positivity
  refine (Finset.sum_congr rfl fun l _ => Finset.sum_comm).trans_le ((Finset.sum_le_sum
    fun l _ => Finset.sum_le_sum fun i _ => key l i).trans_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma LiftAway_reCoord_sum {ι k l : Type*} [Fintype ι] (c : ι → ℝ)
    (A : ι → Matrix k l ℂ) (p : Fin 2 × k × l) :
    reCoord (∑ r, ((c r : ℝ) : ℂ) • A r) p = ∑ r, c r * reCoord (A r) p := by
  unfold reCoord
  split_ifs <;> simp [Matrix.sum_apply, Complex.re_sum, Complex.im_sum]

private lemma LiftAway_sum_sq_reCoord {k l : Type*} [Fintype k] [Fintype l] (B : Matrix k l ℂ) :
    ∑ p, reCoord B p ^ 2 = hsSq B := by
  rw [← (hsInner_reCoord B B 0).2.1, ← (hsInner_reCoord B B 0).2.2.2.2]
  simp [sq]

/-- `N` is real-linear: `N(Σ_β c_β H_β) = Σ_β c_β N(H_β)`. -/
private lemma LiftAway_N_sum {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (H : ι → Matrix (Fin W) (Fin W) ℂ) :
    blockMat 0 0 (∑ b, ((c b : ℝ) : ℂ) • H b) 0 = ∑ b, ((c b : ℝ) : ℂ) • blockMat 0 0 (H b) 0 := by
  ext ⟨a, α⟩ ⟨b, β⟩
  fin_cases a <;> fin_cases b <;> simp [blockMat, Matrix.sum_apply]

/-- (10.32) [lg:eq:A-derivative-bounds]: for `g ≥ 1`, `|z| ≤ E₀`, `max_i ‖V_i‖ ≤ K₁`,
`Σ_{(l,α)} ‖(D_{l,α} 𝒜) c‖² ≤ 4 q² κ⁸ W g⁻⁴ ‖c‖²`, `κ = (2 + E₀ + K₁)^q`. -/
private lemma LiftAway_bound_dir {g z E₀ K₁ : ℝ} (hg : 1 ≤ g) (hz : |z| ≤ E₀)
    {V : Fin q → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, ‖V i‖ ≤ K₁)
    (c : Fin q × Fin W × Fin W → ℝ) :
    ∑ j : Fin q × Fin W × Fin W, ∑ p, (LiftAway_Pd g z V j.1 (hermBasis W j.2) *ᵥ c) p ^ 2 ≤
      4 * q ^ 2 * ((2 + E₀ + K₁) ^ q) ^ 8 * W * g⁻¹ ^ 4 * ∑ r, c r ^ 2 := by
  set κ := (2 + E₀ + K₁) ^ q with hκ
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  set R : Fin q → Matrix (Fin W) (Fin W) ℂ := fun i => ∑ b, ((c (i, b) : ℝ) : ℂ) • hermBasis W b
    with hR
  set D : Fin q → Fin W × Fin W → Fin q → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
    fun l a i => if i < l then LiftAway_X g z V i (R i) * LiftAway_X g z V l (hermBasis W a) -
      LiftAway_X g z V l (hermBasis W a) * LiftAway_X g z V i (R i) else 0 with hD
  have hX : ∀ i, LiftAway_X g z V i (R i) =
      ∑ b, ((c (i, b) : ℝ) : ℂ) • LiftAway_X g z V i (hermBasis W b) := by
    intro i
    simp only [LiftAway_X, hR, LiftAway_N_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  have hrow : ∀ (l : Fin q) (a : Fin W × Fin W),
      ∑ p, (LiftAway_Pd g z V l (hermBasis W a) *ᵥ c) p ^ 2 = g⁻¹ ^ 4 * hsSq (∑ i, D l a i) := by
    intro l a
    have e1 : ∀ p, (LiftAway_Pd g z V l (hermBasis W a) *ᵥ c) p =
        reCoord (∑ r, ((c r : ℝ) : ℂ) •
          LiftAway_dA g z V l (hermBasis W a) (Pi.single r.1 (hermBasis W r.2))) p := by
      intro p
      rw [LiftAway_reCoord_sum]
      simp [Matrix.mulVec, dotProduct, LiftAway_Pd, mul_comm]
    have e2 : ∑ r, ((c r : ℝ) : ℂ) •
        LiftAway_dA g z V l (hermBasis W a) (Pi.single r.1 (hermBasis W r.2)) =
        ((g⁻¹ ^ 2 : ℝ) : ℂ) • ∑ i, D l a i := by
      simp only [LiftAway_dA_single, smul_comm ((c _ : ℝ) : ℂ) ((g⁻¹ ^ 2 : ℝ) : ℂ)]
      rw [← Finset.smul_sum, Fintype.sum_prod_type]
      refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
      simp only [hD]
      split_ifs
      · rw [hX]
        simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
        rw [← Finset.sum_sub_distrib]
        simp only [smul_sub]
      · simp
    simp only [e1, e2, LiftAway_sum_sq_reCoord, LiftAway_hsSq_smul, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    ring
  have hpair : ∀ (l i : Fin q), ∑ a, hsSq (D l a i) ≤ 4 * κ ^ 8 * W * ∑ b, c (i, b) ^ 2 := by
    intro l i
    by_cases hi : i < l
    · simp only [hD, hi, ite_true]
      obtain ⟨h₁, h₂⟩ := LiftAway_norm_tail hg hz hV i
      obtain ⟨h₃, h₄⟩ := LiftAway_norm_tail hg hz hV l
      have h := LiftAway_pair_dir h₂ h₁ h₄ h₃ (R i)
      rw [hR, LiftAway_hsSq_basis] at h
      exact h
    · simp only [hD, hi, ite_false, LiftAway_hsSq_zero, Finset.sum_const_zero]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [Fintype.sum_prod_type]
  simp only [hrow]
  calc _ ≤ ∑ l, ∑ a, g⁻¹ ^ 4 * (q * ∑ i, hsSq (D l a i)) :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          (by simpa using LiftAway_hsSq_sum_le Finset.univ (D l a)) (by positivity)
    _ = g⁻¹ ^ 4 * q * ∑ l, ∑ i, ∑ a, hsSq (D l a i) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by rw [Finset.sum_comm]; simp only [mul_assoc]
    _ ≤ g⁻¹ ^ 4 * q * ∑ l : Fin q, ∑ i, 4 * κ ^ 8 * W * ∑ b, c (i, b) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ =>
          Finset.sum_le_sum fun i _ => hpair l i) (by positivity)
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← Finset.mul_sum]
        ring

end LiftAwayBound
section LiftAwaySmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}

/-- Every entry of the matrix family `F` is `C^∞` on `U`. -/
private def LiftAway_Sm {m n 𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] (U : Set E)
    (F : E → Matrix m n 𝕜) : Prop :=
  ∀ a b, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => F x a b) U

variable {m n l 𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]

private lemma LiftAway_Sm_const (A : Matrix m n 𝕜) : LiftAway_Sm U (fun _ => A) :=
  fun _ _ => contDiffOn_const

private lemma LiftAway_Sm_sub {F G : E → Matrix m n 𝕜} (hF : LiftAway_Sm U F)
    (hG : LiftAway_Sm U G) : LiftAway_Sm U (fun x => F x - G x) :=
  fun a b => (hF a b).sub (hG a b)

private lemma LiftAway_Sm_smul {F : E → Matrix m n 𝕜} (c : 𝕜) (hF : LiftAway_Sm U F) :
    LiftAway_Sm U (fun x => c • F x) :=
  fun a b => by simpa only [Matrix.smul_apply, smul_eq_mul] using contDiffOn_const.mul (hF a b)

private lemma LiftAway_Sm_mul [Fintype n] {F : E → Matrix m n 𝕜} {G : E → Matrix n l 𝕜}
    (hF : LiftAway_Sm U F) (hG : LiftAway_Sm U G) : LiftAway_Sm U (fun x => F x * G x) :=
  fun a b => by
    simp only [Matrix.mul_apply]
    exact ContDiffOn.sum fun k _ => (hF a k).mul (hG k b)

private lemma LiftAway_Sm_transpose {F : E → Matrix m n 𝕜} (hF : LiftAway_Sm U F) :
    LiftAway_Sm U (fun x => (F x)ᵀ) :=
  fun a b => hF b a

private lemma LiftAway_Sm_sum {ι : Type*} (s : Finset ι) {F : ι → E → Matrix m n 𝕜}
    (hF : ∀ i, LiftAway_Sm U (F i)) : LiftAway_Sm U (fun x => ∑ i ∈ s, F i x) :=
  fun a b => by
    simp only [Matrix.sum_apply]
    exact ContDiffOn.sum fun i _ => hF i a b

private lemma LiftAway_det [Fintype n] [DecidableEq n] {F : E → Matrix n n 𝕜}
    (hF : LiftAway_Sm U F) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (F x).det) U := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hF _ _)

private lemma LiftAway_Sm_inv [Fintype n] [DecidableEq n] {F : E → Matrix n n 𝕜}
    (hF : LiftAway_Sm U F) (hdet : ∀ x ∈ U, (F x).det ≠ 0) :
    LiftAway_Sm U (fun x => (F x)⁻¹) := by
  intro a b
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  refine ((LiftAway_det hF).inv hdet).mul (LiftAway_det fun c d => ?_)
  simp only [Matrix.updateRow_apply]
  by_cases h : c = b
  · simp only [h, ite_true]; exact contDiffOn_const
  · simp only [h, ite_false]; exact hF c d

private lemma LiftAway_SmV_mulVec [Fintype n] {F : E → Matrix m n ℝ} (hF : LiftAway_Sm U F)
    (v : n → ℝ) (a : m) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (F x *ᵥ v) a) U := by
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiffOn.sum fun k _ => (hF a k).mul contDiffOn_const

private lemma LiftAway_SmV_reCoord {F : E → Matrix m n ℂ} (hF : LiftAway_Sm U F)
    (p : Fin 2 × m × n) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => reCoord (F x) p) U := by
  by_cases h : p.1 = 0
  · simp only [reCoord, h, ite_true]
    exact Complex.reCLM.contDiff.comp_contDiffOn (hF _ _)
  · simp only [reCoord, h, ite_false]
    exact Complex.imCLM.contDiff.comp_contDiffOn (hF _ _)

private lemma LiftAway_Sm_blockMat {W : ℕ} {A : E → Matrix (Fin W) (Fin W) ℂ}
    (hA : LiftAway_Sm U A) (B C : Matrix (Fin W) (Fin W) ℂ) :
    LiftAway_Sm U (fun x => blockMat (A x) B C 0) := by
  rintro ⟨a, α⟩ ⟨b, β⟩
  fin_cases a <;> fin_cases b
  exacts [hA α β, contDiffOn_const, contDiffOn_const, contDiffOn_const]

private lemma LiftAway_Sm_gue {W L : ℕ} (U : Set (Ω W L)) (i : Fin L) :
    LiftAway_Sm U (fun x => gueBlock W L x i) := by
  have hc : ∀ p, ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Ω W L => ((x p : ℝ) : ℂ)) U := fun p =>
    (Complex.ofRealCLM.contDiff.comp
      (contDiff_apply ℝ (fun _ : Fin L × Fin W × Fin W => ℝ) p)).contDiffOn
  intro α β
  simp only [gueBlock, Matrix.of_apply]
  split_ifs
  · exact (hc _).div_const _
  · exact ((hc _).add (contDiffOn_const.mul (hc _))).div_const _
  · exact ((hc _).sub (contDiffOn_const.mul (hc _))).div_const _

/-- The tails are `C^∞` in smooth inputs. -/
private lemma LiftAway_Sm_tl {W q : ℕ} (g z : ℝ) {V : E → Fin q → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, LiftAway_Sm U (fun x => V x i)) :
    ∀ d k, k + d = q → LiftAway_Sm U (fun x => LiftAway_tl g z (V x) k)
  | 0, k, h => by
    obtain rfl : k = q := by omega
    simp only [LiftAway_tl_top]
    exact LiftAway_Sm_const _
  | d + 1, k, h => by
    have hk : k < q := by omega
    simp only [LiftAway_tl_cons _ _ _ hk, LiftAway_transferMat_eq]
    exact LiftAway_Sm_mul (LiftAway_Sm_blockMat (LiftAway_Sm_sub (LiftAway_Sm_const _)
      (LiftAway_Sm_smul _ (hV _))) _ _) (LiftAway_Sm_tl g z hV d (k + 1) (by omega))

/-- `𝒜(R)` is `C^∞` in smooth inputs. -/
private lemma LiftAway_Sm_prodDiff {W q : ℕ} (g z : ℝ) {V : E → Fin q → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, LiftAway_Sm U (fun x => V x i)) (R : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    LiftAway_Sm U (fun x => prodDiff g z (V x) R) := by
  have hQ : ∀ i : Fin q, LiftAway_Sm U (fun x => liftTail g z (V x) i) := fun i =>
    LiftAway_Sm_tl g z hV (q - (i.val + 1)) (i.val + 1) (by omega)
  unfold prodDiff
  refine LiftAway_Sm_smul _ (LiftAway_Sm_sum _ fun i => LiftAway_Sm_mul (LiftAway_Sm_mul
    (LiftAway_Sm_inv (hQ i) fun x _ => (LiftAway_tl_unit g z (V x) (i.val + 1)).ne_zero)
    (LiftAway_Sm_const _)) (hQ i))

/-- `hermLiftMat` is `C^∞` in smooth inputs. -/
private lemma LiftAway_Sm_hermLiftMat {W q : ℕ} (g z : ℝ)
    {V : E → Fin q → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, LiftAway_Sm U (fun x => V x i)) :
    LiftAway_Sm U (fun x => hermLiftMat g z (V x)) := by
  intro a b
  cases a with
  | inl r =>
    simp only [hermLiftMat, Matrix.fromRows_apply_inl, Matrix.transpose_apply, prodDiffMat,
      Matrix.of_apply]
    exact LiftAway_SmV_reCoord (LiftAway_Sm_prodDiff g z hV _) b
  | inr p =>
    simp only [hermLiftMat, Matrix.fromRows_apply_inr]
    exact contDiffOn_const

end LiftAwaySmooth
section LiftAwayCoord

variable {W q : ℕ}

/-- The standard coordinates of the Hermitian lift:
`Y_{(i, α)} = √W · √2 ((lsqInv B)ᵀ reCoord M)_{(i, α)}`, `B = hermLiftMat`. -/
private lemma LiftAway_hermCoord_field (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (p : Fin q × Fin W × Fin W) :
    hermCoord W q (hermLiftField g z V M) p = Real.sqrt W *
      (Real.sqrt 2 * ((lsqInv (hermLiftMat g z V))ᵀ *ᵥ reCoord M) (Sum.inl p)) := by
  unfold hermCoord hermLiftField
  congr 1
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    trace_hermBasis_mul, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Complex.ofReal_re]

private lemma LiftAway_W_pos {G : Fin 128 → Matrix (Fin W) (Fin W) ℂ} (hG : 0 < coerMin G) :
    0 < W := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW
    have : IsEmpty {P : Matrix (Fin 0) (Fin 0) ℂ // P.trace.im = 0 ∧ hsSq P = 1} :=
      ⟨fun ⟨P, _, h⟩ => by simp [hsSq] at h⟩
    have h0 : coerMin G = 0 := Real.iInf_of_isEmpty _
    linarith
  · exact hW

private lemma LiftAway_prodDiff_zero (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    prodDiff g z V 0 = 0 := by
  unfold prodDiff
  simp [LiftAway_blockMat_zero]

/-- Where `S_W(G) > 0` and `g > 0`, the Gram matrix of `hermLiftMat` is invertible: otherwise
the Hermitian lift of `N(I) = [[0, 0], [I, 0]]`, a nonzero element of the algebra (10.3)
[eq:c-Lie], would vanish, against (10.30) [lg:eq:minimal-lift]. -/
private lemma LiftAway_det_ne {g z : ℝ} (hg : 0 < g) {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, (V i).IsHermitian) (hS : 0 < coerMin (layoutBlocks liftLayout V)) :
    ((hermLiftMat g z V)ᵀ * hermLiftMat g z V).det ≠ 0 := by
  intro h0
  have hW := LiftAway_W_pos hS
  set M₀ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := blockMat 0 0 1 0 with hM₀def
  have hM₀ : M₀ ∈ lieOmega W :=
    (mem_lieOmega_iff _ _ _ _).2 ⟨Matrix.isHermitian_zero, Matrix.isHermitian_one, by simp,
      by simp⟩
  have h1 := (prodDiff_hermLiftField (z := z) hg hS hV le_rfl M₀).2 hM₀
  have hinv : ((hermLiftMat g z V)ᵀ * hermLiftMat g z V)⁻¹ = 0 :=
    Matrix.nonsing_inv_apply_not_isUnit _ (by rw [isUnit_iff_ne_zero]; exact not_not.2 h0)
  have hX : hermLiftField g z V M₀ = 0 := by
    funext i
    simp [hermLiftField, lsqInv, hinv]
  rw [hX, LiftAway_prodDiff_zero] at h1
  have h2 := congrFun (congrFun h1 (1, ⟨0, hW⟩)) (0, ⟨0, hW⟩)
  simp [hM₀def, blockMat] at h2
  exact absurd h2.symm (Complex.ofReal_ne_zero.2 (by positivity))

/-- Moving the standard coordinate `j` by `t` moves `V_{j.1}` by `t W^{-1/2} H_{j.2}`. -/
private lemma LiftAway_gueBlock_line (ω : Ω W q) (j : Fin q × Fin W × Fin W) (t : ℝ) :
    gueBlock W q (ω + t • Pi.single j 1) = gueBlock W q ω +
      (t * (Real.sqrt W)⁻¹) • (Pi.single j.1 (hermBasis W j.2) :
        Fin q → Matrix (Fin W) (Fin W) ℂ) := by
  funext a
  rw [Pi.add_apply, gueBlock_eq_sum_hermBasis, gueBlock_eq_sum_hermBasis]
  obtain ⟨i, b⟩ := j
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Prod.mk.injEq, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Complex.ofReal_add, add_smul, Finset.sum_add_distrib, smul_add]
  congr 1
  by_cases ha : a = i
  · subst ha
    simp only [true_and, apply_ite (fun r : ℝ => ((r : ℝ) : ℂ)), ite_smul,
      Complex.ofReal_zero, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_smul]
    rw [← Complex.coe_smul]; push_cast; ring_nf
  · simp [ha]

private lemma LiftAway_hasDerivAt_mulVec {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {F : ℝ → Matrix m n ℝ} {F' : Matrix m n ℝ} {t : ℝ} (hF : HasDerivAt F F' t) (v : n → ℝ)
    (a : m) : HasDerivAt (fun s => (F s *ᵥ v) a) ((F' *ᵥ v) a) t := by
  let L : Matrix m n ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun B => (B *ᵥ v) a
      map_add' := fun A B => by simp [Matrix.add_mulVec]
      map_smul' := fun c A => by simp [Matrix.smul_mulVec] }
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t hF

end LiftAwayCoord
/-- The reversal of the inputs is an involution. -/
private lemma LiftAway_rev_rev (W q : ℕ) (ω : Ω W q) :
    shiftMap W q Fin.revPerm (shiftMap W q Fin.revPerm ω) = ω := by
  funext x
  simp [shiftMap]

/-- The Hermitian lift in the standard coordinates is `C^∞` on the open set `{S_W(G) > 0}`
for `g > 0`;
(10.32) [lg:eq:A-derivative-bounds] and (10.33) [lg:eq:DV]: for `g ≥ 1`, `0 < |E| ≤ E₀`,
`S_W(G) ≥ c₁`, `max_i ‖V_i‖ ≤ K₁` and a Hermitian target `M` of the algebra,
`‖∇_V X‖²_HS ≤ C (1 + |E|⁻¹)² W g² ‖M‖²`. -/
theorem hermLiftField_deriv (E₀ K₁ c₁ : ℝ) (hE₀ : 0 < E₀) (hK₁ : 0 < K₁) (hc₁ : 0 < c₁) :
    (∀ (W : ℕ) (g z : ℝ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), 0 < g →
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun ω : Ω W 1000 => hermCoord W 1000 (hermLiftField g z (gueBlock W 1000 ω) M))
        {ω : Ω W 1000 | 0 < coerMin (layoutBlocks liftLayout (gueBlock W 1000 ω))}) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ) (g E : ℝ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      (ω : Ω W 1000), 1 ≤ g → E ≠ 0 → |E| ≤ E₀ →
      c₁ ≤ coerMin (layoutBlocks liftLayout (gueBlock W 1000 ω)) →
      (∀ i, ‖gueBlock W 1000 ω i‖ ≤ K₁) → M ∈ lieOmega W → M.IsHermitian →
        ∑ p, ∑ j, (fderiv ℝ (fun η : Ω W 1000 =>
            hermCoord W 1000 (hermLiftField g (max 1 g * E / g) (gueBlock W 1000 η) M)) ω
              (Pi.single j 1) p) ^ 2 ≤
          C * (1 + |E|⁻¹) ^ 2 * W * g ^ 2 * hsSq M := by
  have hsmooth : ∀ (W : ℕ) (g z : ℝ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), 0 < g →
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun ω : Ω W 1000 => hermCoord W 1000 (hermLiftField g z (gueBlock W 1000 ω) M))
        {ω : Ω W 1000 | 0 < coerMin (layoutBlocks liftLayout (gueBlock W 1000 ω))} := by
    intro W g z M hg
    set U := {ω : Ω W 1000 | 0 < coerMin (layoutBlocks liftLayout (gueBlock W 1000 ω))}
    have hA := LiftAway_Sm_hermLiftMat (U := U) g z (fun i => LiftAway_Sm_gue U i)
    have hL : LiftAway_Sm U (fun x => (lsqInv (hermLiftMat g z (gueBlock W 1000 x)))ᵀ) :=
      LiftAway_Sm_transpose (LiftAway_Sm_mul (LiftAway_Sm_inv (LiftAway_Sm_mul
        (LiftAway_Sm_transpose hA) hA) fun x hx =>
          LiftAway_det_ne hg (gueBlock_isHermitian W 1000 x) hx) (LiftAway_Sm_transpose hA))
    refine contDiffOn_pi.2 fun p => ?_
    simp only [LiftAway_hermCoord_field]
    exact contDiffOn_const.mul (contDiffOn_const.mul (LiftAway_SmV_mulVec hL _ _))
  refine ⟨hsmooth, ?_⟩
  obtain ⟨Cc, hCc, hcoer⟩ := hermLiftMat_coercive E₀ K₁ c₁ hE₀ hK₁ hc₁
  obtain ⟨Cs, hCs, hsize⟩ := hermLiftField_size E₀ K₁ c₁ hE₀ hK₁ hc₁
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (2 + E₀ + K₁) ^ 1000 := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  refine ⟨4000000 * κ ^ 8 * Cs * (4 + 2 * Cc), by positivity, ?_⟩
  intro W g E M ω hg hE0 hE hc hVn hM hMh
  have hg0 : 0 < g := zero_lt_one.trans_le hg
  have hW : 0 < W := LiftAway_W_pos (hc₁.trans_le hc)
  set V := gueBlock W 1000 ω with hVdef
  have hV : ∀ i, (V i).IsHermitian := gueBlock_isHermitian W 1000 ω
  set z := max 1 g * E / g with hzdef
  have hz : |z| ≤ E₀ := by
    rw [hzdef, max_eq_right hg, mul_div_cancel_left₀ _ hg0.ne']; exact hE
  set A := hermLiftMat g z V with hAdef
  set y := reCoord M with hy
  set τ := Real.sqrt ((Cc * g ^ 4)⁻¹) with hτdef
  have hτ : 0 < τ := Real.sqrt_pos.2 (by positivity)
  have hτ2 : τ ^ 2 = (Cc * g ^ 4)⁻¹ := Real.sq_sqrt (by positivity)
  have hAτ : ∀ x, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A *ᵥ x) j ^ 2 := by
    intro x; rw [hτ2]; exact hcoer W g E V hg hE hV hVn hc x
  obtain ⟨Ad, hAd⟩ : ∃ Ad : Fin 1000 × Fin W × Fin W →
      Matrix ((Fin 1000 × Fin W × Fin W) ⊕ (Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W)))
        (Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W)) ℝ,
      ∀ j, Ad j = Matrix.fromRows (LiftAway_Pd g z V j.1 (hermBasis W j.2))ᵀ 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨Jd, hJd⟩ : ∃ Jd : Fin 1000 × Fin W × Fin W →
      Matrix ((Fin 1000 × Fin W × Fin W) ⊕ (Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W)))
        (Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W)) ℝ,
      ∀ j, Jd j = (1 - A * lsqInv A) * Ad j * (Aᵀ * A)⁻¹ - (lsqInv A)ᵀ * (Ad j)ᵀ * (lsqInv A)ᵀ :=
    ⟨_, fun _ => rfl⟩
  have hd : ∀ j : Fin 1000 × Fin W × Fin W, HasDerivAt (fun s : ℝ => (lsqInv (hermLiftMat g z
      (V + s • (Pi.single j.1 (hermBasis W j.2) : Fin 1000 → Matrix (Fin W) (Fin W) ℂ))))ᵀ)
      (Jd j) 0 := by
    intro j
    have e : V + (0 : ℝ) • (Pi.single j.1 (hermBasis W j.2) :
        Fin 1000 → Matrix (Fin W) (Fin W) ℂ) = V := by simp
    have h := hasDerivAt_lsqInv_transpose hτ
      (LiftAway_hasDerivAt_hermLiftMat g z V j.1 (hermBasis W j.2))
      (fun x => by simp only [e]; exact hAτ x)
    simp only [e] at h
    rw [hJd, hAd]
    exact h
  -- the partial derivatives
  have hO := (contDiffOn_liftField (W := W) g z M).1
  have hU : ω ∈ {ω : Ω W 1000 | 0 < coerMin (layoutBlocks liftLayout (gueBlock W 1000 ω))} :=
    hc₁.trans_le hc
  have hfd : ∀ (j p : Fin 1000 × Fin W × Fin W), fderiv ℝ (fun η : Ω W 1000 =>
      hermCoord W 1000 (hermLiftField g z (gueBlock W 1000 η) M)) ω (Pi.single j 1) p =
        Real.sqrt 2 * (Jd j *ᵥ y) (Sum.inl p) := by
    intro j p
    have hdiff := (((hsmooth W g z M hg0).contDiffAt (hO.mem_nhds hU)).differentiableAt
      (by simp)).hasFDerivAt
    have hline : HasDerivAt (fun t : ℝ => ω + t • (Pi.single j 1 : Ω W 1000))
        (Pi.single j 1 : Ω W 1000) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j 1 : Ω W 1000)).const_add ω
    have h1 := hasDerivAt_pi.1 (hdiff.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)) p
    set c := (Real.sqrt W)⁻¹ with hcdef
    have hc' : HasDerivAt (fun t : ℝ => t * c) c 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
    have hd' : HasDerivAt (fun s : ℝ => (lsqInv (hermLiftMat g z
        (V + s • (Pi.single j.1 (hermBasis W j.2) : Fin 1000 → Matrix (Fin W) (Fin W) ℂ))))ᵀ)
        (Jd j) ((fun t : ℝ => t * c) 0) := by simpa using hd j
    have h2 := (((LiftAway_hasDerivAt_mulVec (hd'.scomp (0 : ℝ) hc') y (Sum.inl p)).const_mul
      (Real.sqrt 2)).const_mul (Real.sqrt W))
    have e : (fun t : ℝ => ((fun η : Ω W 1000 => hermCoord W 1000 (hermLiftField g z
        (gueBlock W 1000 η) M)) ∘ fun t : ℝ => ω + t • (Pi.single j 1 : Ω W 1000)) t p) =
        fun t => Real.sqrt W * (Real.sqrt 2 * (((fun s : ℝ => (lsqInv (hermLiftMat g z
          (V + s • (Pi.single j.1 (hermBasis W j.2) :
            Fin 1000 → Matrix (Fin W) (Fin W) ℂ))))ᵀ) ∘ fun t : ℝ => t * c) t *ᵥ y)
              (Sum.inl p)) := by
      funext t
      simp only [Function.comp]
      rw [LiftAway_gueBlock_line, LiftAway_hermCoord_field]
    rw [e] at h1
    rw [h1.unique h2, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, hcdef]
    have : Real.sqrt W ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hW)).ne'
    field_simp
  -- the two terms of (10.22) [eq:c-lift-derivative]
  set x := (Aᵀ * A)⁻¹ *ᵥ y with hx
  set cv := (lsqInv A)ᵀ *ᵥ y with hcv
  have hrow : ∀ j, ∑ p, (Jd j *ᵥ y) (Sum.inl p) ^ 2 ≤
      2 * ∑ r, ((LiftAway_Pd g z V j.1 (hermBasis W j.2))ᵀ *ᵥ x) r ^ 2 +
        2 * ((τ ^ 2)⁻¹ * ∑ p, (LiftAway_Pd g z V j.1 (hermBasis W j.2) *ᵥ
          (fun r => cv (Sum.inl r))) p ^ 2) := by
    intro j
    have h := LiftAway_deriv_split (A' := Ad j) hτ hAτ y
    have e1 : ∑ i, (Ad j *ᵥ x) i ^ 2 =
        ∑ r, ((LiftAway_Pd g z V j.1 (hermBasis W j.2))ᵀ *ᵥ x) r ^ 2 := by
      rw [hAd, Matrix.fromRows_mulVec, Fintype.sum_sum_type, Matrix.zero_mulVec]
      simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, Finset.sum_const_zero, add_zero]
    have e2 : ∑ i, ((Ad j)ᵀ *ᵥ cv) i ^ 2 = ∑ p, (LiftAway_Pd g z V j.1 (hermBasis W j.2) *ᵥ
        (fun r => cv (Sum.inl r))) p ^ 2 := by
      rw [hAd, Matrix.transpose_fromRows, Matrix.fromCols_mulVec, Matrix.transpose_transpose,
        Matrix.transpose_zero, Matrix.zero_mulVec, add_zero]
      rfl
    rw [e1, e2, ← hJd, Fintype.sum_sum_type] at h
    have h0 : 0 ≤ ∑ p, (Jd j *ᵥ y) (Sum.inr p) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith only [h, h0]
  have hadj := LiftAway_bound_adj hg hz hVn x
  have hdir := LiftAway_bound_dir hg hz hVn (fun r => cv (Sum.inl r))
  rw [← hκ] at hadj hdir
  obtain ⟨hs1, hs2⟩ := hsize W g E V M hg hE0 hE hV hVn hc hM hMh
  -- `‖X‖² = 2 Σ_r cv_r²`
  have hX : ∑ i, hsSq (hermLiftField g z V M i) = 2 * ∑ r, cv (Sum.inl r) ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : hermLiftField g z V M i = ∑ k : Fin W × Fin W,
        (((Real.sqrt 2 * cv (Sum.inl (i, k))) : ℝ) : ℂ) • hermBasis W k := rfl
    rw [e, LiftAway_hsSq_basis, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have hτi : (τ ^ 2)⁻¹ = Cc * g ^ 4 := by rw [hτ2, inv_inv]
  have hS2 : ∑ r, cv (Sum.inl r) ^ 2 ≤ Cs * (1 + |E|⁻¹) ^ 2 * g ^ 2 * hsSq M / 2 := by
    rw [hX] at hs1; linarith only [hs1]
  have hK0 : 0 ≤ 4 * ((1000 : ℕ) : ℝ) ^ 2 * κ ^ 8 * W * g⁻¹ ^ 4 := by positivity
  have hsum : ∑ j : Fin 1000 × Fin W × Fin W, ∑ p, (Jd j *ᵥ y) (Sum.inl p) ^ 2 ≤
      2 * (4 * ((1000 : ℕ) : ℝ) ^ 2 * κ ^ 8 * W * g⁻¹ ^ 4 *
        (Cs * (1 + |E|⁻¹) ^ 2 * g ^ 6 * hsSq M)) + 2 * ((τ ^ 2)⁻¹ *
        (4 * ((1000 : ℕ) : ℝ) ^ 2 * κ ^ 8 * W * g⁻¹ ^ 4 *
          (Cs * (1 + |E|⁻¹) ^ 2 * g ^ 2 * hsSq M / 2))) := by
    refine (Finset.sum_le_sum fun j _ => hrow j).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hadj.trans (mul_le_mul_of_nonneg_left hs2 hK0)) two_pos.le)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hdir.trans
        (mul_le_mul_of_nonneg_left hS2 hK0)) (by positivity)) two_pos.le)
  simp only [hfd, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left hsum two_pos.le).trans_eq ?_
  have hg1 : g ≠ 0 := hg0.ne'
  rw [hτi]
  field_simp
  push_cast
  ring

/-- Lemma 10.1 [lem:c-gaussian-lift], (10.7) [eq:c-gaussian-away], for `F = T_1 ⋯ T_q`,
`q = 1000`: for a given cutoff with the properties (10.5) [eq:c-main-cutoff] and the margins
(10.14) [eq:c-main-coercivity] at `liftLayout`, every `g ≥ 1`, `0 < |E| ≤ E₀` and every
Hermitian target `M` of the algebra (10.3) [eq:c-Lie] with `‖M‖_HS = 1`, a cut lift with
`𝔼 |δ_G(χ Y)|² ≤ C (1 + |E|⁻¹)² W g²`; `C` depends only on `E₀` and the margins. -/
theorem gaussian_lift_away (E₀ c₁ ρ K₁ L : ℝ) (hE₀ : 0 < E₀) (hc₁ : 0 < c₁) (hK₁ : 0 < K₁)
    (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ) (c C' : ℝ) (χ : Ω W 1000 → ℝ),
      IsCoercivityCutoff W 1000 liftLayout c₁ ρ K₁ L c C' χ →
      ∀ g E : ℝ, 1 ≤ g → E ≠ 0 → |E| ≤ E₀ →
      ∀ M ∈ lieOmega W, M.IsHermitian → hsSq M = 1 →
        ∃ Y : Ω W 1000 → Ω W 1000,
          IsCutLift W 1000 (fun ω => liftProd g (max 1 g * E / g) (gueBlock W 1000 ω)) M
            (C * (1 + |E|⁻¹) ^ 2 * (W * g ^ 2)) χ Y := by
  obtain ⟨hsm, CD, hCD, hDf⟩ := hermLiftField_deriv E₀ K₁ c₁ hE₀ hK₁ hc₁
  obtain ⟨CX, hCX, hX⟩ := hermLiftField_size E₀ K₁ c₁ hE₀ hK₁ hc₁
  refine ⟨(1 + 2 * L ^ 2) * CX + 2 * CD, by positivity, ?_⟩
  intro W c C' χ hχ g E hg hE0 hE M hM hMh hMn
  obtain ⟨hχs, hχc, hχ01, -, hgrad, hmarg⟩ := hχ
  have hg0 : 0 < g := zero_lt_one.trans_le hg
  set z := max 1 g * E / g with hz
  set m := (1 + |E|⁻¹) ^ 2 * g ^ 2 with hm
  have hm0 : 0 ≤ m := by positivity
  have hNo := (contDiffOn_liftField (W := W) g z M).1
  have hYs := hsm W g z M hg0
  have hcoer : ∀ ω ∈ tsupport χ, c₁ ≤ coerMin (layoutBlocks liftLayout (gueBlock W 1000 ω)) ∧
      ∀ i, ‖gueBlock W 1000 ω i‖ ≤ K₁ := fun ω hω =>
    hmarg ω hω ω (by simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero]; positivity)
  have hherm : ∀ ω (i : Fin 1000), (gueBlock W 1000 ω i).IsHermitian :=
    fun ω i => gueBlock_isHermitian W 1000 ω i
  refine ⟨fun ω => hermCoord W 1000 (hermLiftField g z (gueBlock W 1000 ω) M), ?_⟩
  obtain ⟨h1, h2, h3⟩ := cutField_divergence_le (l := L ^ 2 / W) (a := W * (CX * m))
    (b := CD * W * m) hχs hχc hχ01 hgrad hNo
    (fun ω hω => lt_of_lt_of_le hc₁ (hcoer ω hω).1) hYs
    (fun ω hω => by
      obtain ⟨hc, hK⟩ := hcoer ω hω
      rw [sum_sq_hermCoord (prodDiff_hermLiftField hg0 hc₁ (hherm ω) hc M).1]
      have := (hX W g E (gueBlock W 1000 ω) M hg hE0 hE (hherm ω) hK hc hM hMh).1
      rw [hMn, mul_one] at this
      refine mul_le_mul_of_nonneg_left (this.trans_eq ?_) (Nat.cast_nonneg W)
      rw [hm]; ring)
    (fun ω hω => by
      obtain ⟨hc, hK⟩ := hcoer ω hω
      have := hDf W g E M ω hg hE0 hE hc hK hM hMh
      rw [hMn, mul_one] at this
      exact this.trans_eq (by rw [hm]; ring))
  refine ⟨fun ω hω => ?_, h1, h2, h3.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · obtain ⟨hc, -⟩ := hcoer ω hω
    obtain ⟨hXh, hXd⟩ := prodDiff_hermLiftField (z := z) hg0 hc₁ (hherm ω) hc M
    have hfun : (fun t : ℝ => liftProd g z (gueBlock W 1000
        (ω + t • hermCoord W 1000 (hermLiftField g z (gueBlock W 1000 ω) M)))) =
        fun t : ℝ => liftProd g z (gueBlock W 1000 ω +
          t • hermLiftField g z (gueBlock W 1000 ω) M) := by
      funext t
      congr 1
      funext i
      rw [gueBlock_add_smul_hermCoord hXh, Pi.add_apply, Pi.smul_apply, Complex.coe_smul]
    have hd := hasDerivAt_liftProd g z (gueBlock W 1000 ω)
      (hermLiftField g z (gueBlock W 1000 ω) M)
    rw [hXd hM, Matrix.mul_smul] at hd
    change HasDerivAt _ _ 0
    simp only at hd ⊢
    rw [hfun]
    exact hd
  · have hW : (L ^ 2 / W) * W ≤ L ^ 2 * W := by
      rcases Nat.eq_zero_or_pos W with h0 | h0
      · simp [h0]
      · rw [div_mul_cancel₀ _ (by positivity)]
        nlinarith [sq_nonneg L, (by exact_mod_cast h0 : (1 : ℝ) ≤ W)]
    rw [show ((1 + 2 * L ^ 2) * CX + 2 * CD) * (1 + |E|⁻¹) ^ 2 * (W * g ^ 2) =
      ((1 + 2 * L ^ 2) * CX + 2 * CD) * W * m by rw [hm]; ring]
    nlinarith [mul_le_mul_of_nonneg_right hW (by positivity : 0 ≤ CX * m)]

/-- (10.7) [eq:c-gaussian-away] in the batch order of Definition 8.5 [up:def:transfer-operator]:
for a cutoff with the margins at `batchLayout`, `g ≥ 1`, `0 < |E| ≤ E₀` and a Hermitian
`M ∈ 𝔤` of (10.1) [up:eq:lie-algebra] with `‖M‖_HS = 1`, a cut lift with `D_Y T = √2 T M` and
`𝔼 |δ_G(χ Y)|² ≤ C (1 + |E|⁻¹)² W g²`. -/
theorem gaussian_lift_away_batch (E₀ c₁ ρ K₁ L : ℝ) (hE₀ : 0 < E₀) (hc₁ : 0 < c₁)
    (hK₁ : 0 < K₁) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ) (c C' : ℝ) (χ : Ω W 1000 → ℝ),
      IsCoercivityCutoff W 1000 batchLayout c₁ ρ K₁ L c C' χ →
      ∀ g E : ℝ, 1 ≤ g → E ≠ 0 → |E| ≤ E₀ →
      ∀ M ∈ lieJ W, M.IsHermitian → hsSq M = 1 →
        ∃ Y : Ω W 1000 → Ω W 1000,
          IsCutLift W 1000 (batchMat W g E 1000) M (C * (1 + |E|⁻¹) ^ 2 * (W * g ^ 2)) χ Y := by
  obtain ⟨C, hC, hlift⟩ := gaussian_lift_away E₀ c₁ ρ K₁ L hE₀ hc₁ hK₁ hL
  refine ⟨C, hC, fun W c C' χ hχ g E hg hE0 hE M hM hMh hMn => ?_⟩
  set S := freeConj W 0 with hSdef
  have hu := freeConj_zero_mem_unitaryGroup W
  have hSS' : Sᴴ * S = 1 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
    exact hu
  have hback : Sᴴ * (S * M * Sᴴ) * S = M := by
    calc Sᴴ * (S * M * Sᴴ) * S = (Sᴴ * S) * M * (Sᴴ * S) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hSS', Matrix.one_mul, Matrix.mul_one]
  obtain ⟨hlie, hhs, hher, -⟩ := conj_freeConj_lie (S * M * Sᴴ)
  rw [hback] at hlie hhs hher
  obtain ⟨Y, hY⟩ := hlift W c C' _ (isCoercivityCutoff_rev hχ) g E hg hE0 hE (S * M * Sᴴ)
    (hlie.1 hM) (hher.1 hMh) (hhs.symm.trans hMn)
  have h := isCutLift_rev hY
  rw [hback] at h
  have hχχ : (fun ω => χ (shiftMap W 1000 Fin.revPerm (shiftMap W 1000 Fin.revPerm ω))) = χ :=
    funext fun ω => by rw [LiftAway_rev_rev]
  rw [hχχ] at h
  exact ⟨_, h⟩

end LSBA
