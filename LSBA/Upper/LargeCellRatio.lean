import LSBA.Upper.LargeCells
import LSBA.Transfer.Path

/-!
# Mass ratios of two cells

The deterministic part of the proof of (E.3) [uva:eq:cell-correlator]: for an eigenpair
`(E, ψ)` of the block operator (1.3) [eq:model] with `g ≥ 1`, a cell `A` of `n_A ≥ 2` blocks and a
cell `B` of `n_B ≥ 2` blocks inside the Dirichlet path `Λ = ℤ_L ∖ A`, with `E ∉ σ(H_Λ)`,
(E.4) [uva:eq:ratio-audit]: `n_A m_B ≤ 16 K_A⁴ K_B⁴ n_B m_A Σ_{b, x} ‖G_Λ(b, x; E)‖²` over the
first two blocks `b` of `B` and the endpoints `x` of `Λ`. Almost surely no eigenvalue of the
model lies in `σ(H_Λ)`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The Euclidean norm of a vector. -/
private def lcrN {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖

private theorem lcrN_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) : 0 ≤ lcrN v := norm_nonneg _

private theorem lcrN_sq {ι : Type*} [Fintype ι] (v : ι → ℂ) : lcrN v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [lcrN, EuclideanSpace.norm_sq_eq]

private theorem lcrN_mulVec {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ)
    (v : m → ℂ) : lcrN (M *ᵥ v) ≤ ‖M‖ * lcrN v := by
  exact Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 v)

private theorem lcrN_add {ι : Type*} [Fintype ι] (v w : ι → ℂ) :
    lcrN (v + w) ≤ lcrN v + lcrN w := by
  unfold lcrN
  exact norm_add_le (WithLp.toLp 2 v : EuclideanSpace ℂ ι) (WithLp.toLp 2 w)

private theorem lcrN_neg {ι : Type*} [Fintype ι] (v : ι → ℂ) : lcrN (-v) = lcrN v := by
  unfold lcrN
  exact norm_neg (WithLp.toLp 2 v : EuclideanSpace ℂ ι)

private theorem lcr_cellBlock_cellBlock {L : ℕ} (a : Fin L) (i j : ℕ) :
    cellBlock (cellBlock a i) j = cellBlock a (i + j) := by
  apply Fin.ext
  simp only [cellBlock]
  rw [Nat.mod_add_mod, Nat.add_assoc]

private theorem lcr_cellBlock_zero {L : ℕ} (a : Fin L) : cellBlock a 0 = a := by
  apply Fin.ext
  simp [cellBlock, Nat.mod_eq_of_lt a.isLt]

private theorem lcr_cellBlock_add_L {L : ℕ} (a : Fin L) (j : ℕ) :
    cellBlock a (j + L) = cellBlock a j := by
  apply Fin.ext
  simp [cellBlock, ← Nat.add_assoc, Nat.add_mod_right]

private theorem lcr_cellBlock_L {L : ℕ} (a : Fin L) : cellBlock a L = a := by
  have := lcr_cellBlock_add_L a 0
  rwa [Nat.zero_add, lcr_cellBlock_zero] at this

private theorem lcr_pred_succ {L : ℕ} (c : Fin L) : cellBlock (cellBlock c 1) (L - 1) = c := by
  have hL : 0 < L := c.pos
  rw [lcr_cellBlock_cellBlock, show 1 + (L - 1) = L by omega, lcr_cellBlock_L]

private theorem lcr_pred_iff {L : ℕ} (b q : Fin L) :
    b.val = (q.val + 1) % L ↔ q = cellBlock b (L - 1) := by
  have hL : 0 < L := b.pos
  constructor
  · intro h
    apply Fin.ext
    simp only [cellBlock]
    rw [h, Nat.mod_add_mod, show q.val + 1 + (L - 1) = q.val + L by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt q.isLt]
  · rintro rfl
    simp only [cellBlock]
    rw [Nat.mod_add_mod, show b.val + (L - 1) + 1 = b.val + L by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt b.isLt]

private theorem lcr_row {g : ℝ} (hg : 1 ≤ g) {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    {E : ℝ} {ψ : Fin L × Fin W → ℂ} (hψ : Hdet g V *ᵥ ψ = (E : ℂ) • ψ) (b : Fin L) (α : Fin W) :
    ψ (cellBlock b 1, α) + ψ (cellBlock b (L - 1), α) =
      (E : ℂ) * ψ (b, α) - ((g : ℂ)⁻¹) * ∑ β, V b α β * ψ (b, β) := by
  have hrow := congrFun hψ (b, α)
  have hmax : max 1 g = g := max_eq_right hg
  have hg0 : (g : ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le one_pos hg).ne'
  have e1 : ∀ q : Fin L, (if q.val = (b.val + 1) % L then (1 : ℂ) else 0) =
      if q = cellBlock b 1 then 1 else 0 := by
    intro q
    simp only [cellBlock, Fin.ext_iff]
  have e2 : ∀ q : Fin L, (if b.val = (q.val + 1) % L then (1 : ℂ) else 0) =
      if q = cellBlock b (L - 1) then 1 else 0 := by
    intro q
    simp only [lcr_pred_iff]
  have key : (Hdet g V *ᵥ ψ) (b, α) =
      ((max 1 g : ℝ)⁻¹ : ℂ) * ((g : ℂ) * (ψ (cellBlock b 1, α) + ψ (cellBlock b (L - 1), α)) +
        ∑ β, V b α β * ψ (b, β)) := by
    simp only [Hdet, Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.add_apply,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply, blockDiagOp,
      cycleAdj, Matrix.of_apply, smul_eq_mul]
    simp only [e1, e2, mul_add, add_mul, ite_mul, mul_ite, one_mul, zero_mul, mul_zero,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [Finset.mul_sum]
    ring_nf
  rw [key, hmax] at hrow
  simp only [Pi.smul_apply, smul_eq_mul] at hrow
  field_simp at hrow
  field_simp
  linear_combination hrow

private theorem lcr_transferMat_mulVec_pairVec {W : ℕ} (g : ℝ) (z : ℂ)
    (V : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ) :
    transferMat g z V *ᵥ pairVec x y = pairVec (z • x - y - ((g : ℂ)⁻¹) • (V *ᵥ x)) x := by
  ext ⟨a, α⟩
  fin_cases a
  · simp [transferMat, transferFree, pairVec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply,
      Fin.sum_univ_two]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, mul_assoc, ← Finset.mul_sum]
    ring
  · simp [transferMat, transferFree, pairVec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply,
      Fin.sum_univ_two]

/-- The pair `(ψ_c, ψ_{c-1})` of consecutive blocks of `ψ`. -/
private def lcrPair {W L : ℕ} (ψ : Fin L × Fin W → ℂ) (c : Fin L) : Fin 2 × Fin W → ℂ :=
  pairVec (fun α => ψ (c, α)) (fun α => ψ (cellBlock c (L - 1), α))

private theorem lcr_pair_step {g : ℝ} (hg : 1 ≤ g) {W L : ℕ}
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) {E : ℝ} {ψ : Fin L × Fin W → ℂ}
    (hψ : Hdet g V *ᵥ ψ = (E : ℂ) • ψ) (c : Fin L) :
    lcrPair ψ (cellBlock c 1) =
      transferMat g ((max 1 g * E / g : ℝ) : ℂ) (V c) *ᵥ lcrPair ψ c := by
  have hmax : max 1 g = g := max_eq_right hg
  have hg0 : g ≠ 0 := (lt_of_lt_of_le one_pos hg).ne'
  have hz : ((max 1 g * E / g : ℝ) : ℂ) = (E : ℂ) := by
    rw [hmax]; congr 1; field_simp
  rw [lcrPair, lcrPair, lcr_transferMat_mulVec_pairVec, lcr_pred_succ, hz]
  congr 1
  funext α
  have h := lcr_row hg V hψ c α
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  linear_combination h

private theorem lcr_pair_prod {g : ℝ} (hg : 1 ≤ g) {W L : ℕ}
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) {E : ℝ} {ψ : Fin L × Fin W → ℂ}
    (hψ : Hdet g V *ᵥ ψ = (E : ℂ) • ψ) (c : Fin L) (j : ℕ) :
    lcrPair ψ (cellBlock c j) =
      transferProd g ((max 1 g * E / g : ℝ) : ℂ) (fun i => V (cellBlock c i)) j *ᵥ
        lcrPair ψ c := by
  induction j with
  | zero => rw [lcr_cellBlock_zero, transferProd, Matrix.one_mulVec]
  | succ j ih =>
    have h1 : cellBlock c (j + 1) = cellBlock (cellBlock c j) 1 := by
      rw [lcr_cellBlock_cellBlock]
    rw [h1, lcr_pair_step hg V hψ, ih, transferProd, Matrix.mulVec_mulVec]

private theorem lcr_isUnit_transferProd {W : ℕ} (g : ℝ) (z : ℂ) (V : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) : IsUnit (transferProd g z V j).det := by
  induction j with
  | zero => simp [transferProd]
  | succ j ih =>
    rw [transferProd, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_right_inverse (transferMat_mul_transferInv g z (V j))).mul ih

/-- The squared mass `‖ψ_c‖²` of block `c`. -/
private def lcrBn {W L : ℕ} (ψ : Fin L × Fin W → ℂ) (c : Fin L) : ℝ := ∑ α, ‖ψ (c, α)‖ ^ 2

private theorem lcrBn_nonneg {W L : ℕ} (ψ : Fin L × Fin W → ℂ) (c : Fin L) : 0 ≤ lcrBn ψ c :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem lcr_pair_sq {W L : ℕ} (ψ : Fin L × Fin W → ℂ) (c : Fin L) :
    lcrN (lcrPair ψ c) ^ 2 = lcrBn ψ c + lcrBn ψ (cellBlock c (L - 1)) := by
  rw [lcrN_sq]
  simp [lcrPair, pairVec, lcrBn, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem lcr_mass_eq {W L : ℕ} (ψ : Fin L × Fin W → ℂ) (a : Fin L) {n : ℕ} (hn : n ≤ L) :
    ∑ p ∈ cellCoords (W := W) a n, ‖ψ p‖ ^ 2 =
      ∑ j ∈ Finset.range n, lcrBn ψ (cellBlock a j) := by
  have hinj : Set.InjOn (cellBlock a) (Finset.range n : Set ℕ) := by
    intro i hi j hj hij
    have hi' := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hj' := Finset.mem_range.mp (Finset.mem_coe.mp hj)
    have := cellWindow_injective a hn (show cellWindow a n ⟨i, hi'⟩ = cellWindow a n ⟨j, hj'⟩ from
      hij)
    exact congrArg Fin.val this
  unfold cellCoords cellSet
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have h1 : ∀ b : Fin L, ∑ α : Fin W,
      (if b ∈ (Finset.range n).image (cellBlock a) then ‖ψ (b, α)‖ ^ 2 else 0) =
        if b ∈ (Finset.range n).image (cellBlock a) then lcrBn ψ b else 0 := by
    intro b
    split_ifs <;> simp [lcrBn]
  simp only [h1]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_image hinj]

/-- Forward and backward growth of the pair `(ψ_{c+j}, ψ_{c+j-1})` along `n` blocks, by the weight
`K`. -/
private theorem lcr_pair_bounds {g : ℝ} (hg : 1 ≤ g) {W L : ℕ}
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) {E : ℝ} {ψ : Fin L × Fin W → ℂ}
    (hψ : Hdet g V *ᵥ ψ = (E : ℂ) • ψ) (c : Fin L) (n : ℕ) :
    ∀ j ≤ n, lcrN (lcrPair ψ (cellBlock c j)) ≤
        transferWeight g E (fun i => V (cellBlock c i)) n * lcrN (lcrPair ψ c) ∧
      lcrN (lcrPair ψ c) ≤
        transferWeight g E (fun i => V (cellBlock c i)) n * lcrN (lcrPair ψ (cellBlock c j)) := by
  intro j hj
  obtain ⟨-, hKb⟩ := transferWeight_bounds g E (fun i => V (cellBlock c i)) n
  obtain ⟨h1, h2⟩ := hKb j hj
  have hpair := lcr_pair_prod hg V hψ c j
  refine ⟨?_, ?_⟩
  · rw [hpair]
    exact (lcrN_mulVec _ _).trans (mul_le_mul_of_nonneg_right h1 (lcrN_nonneg _))
  · have h3 : lcrPair ψ c =
        (transferProd g ((max 1 g * E / g : ℝ) : ℂ) (fun i => V (cellBlock c i)) j)⁻¹ *ᵥ
          lcrPair ψ (cellBlock c j) := by
      rw [hpair, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (lcr_isUnit_transferProd _ _ _ j), Matrix.one_mulVec]
    calc lcrN (lcrPair ψ c)
        = lcrN ((transferProd g ((max 1 g * E / g : ℝ) : ℂ) (fun i => V (cellBlock c i)) j)⁻¹ *ᵥ
            lcrPair ψ (cellBlock c j)) := by rw [← h3]
      _ ≤ _ := (lcrN_mulVec _ _).trans (mul_le_mul_of_nonneg_right h2 (lcrN_nonneg _))

/-- The first and the last block of a cell `A` of `n ≥ 2` blocks carry at most `8 K_A⁴ m_A / n` of
mass: `n (‖ψ_a‖² + ‖ψ_{a+n-1}‖²) ≤ 8 K_A⁴ m_A` (proof of (E.4) [uva:eq:ratio-audit]). -/
private theorem lcr_cellA {g : ℝ} (hg : 1 ≤ g) {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    {E : ℝ} {ψ : Fin L × Fin W → ℂ} (hψ : Hdet g V *ᵥ ψ = (E : ℂ) • ψ) (a : Fin L) {n : ℕ}
    (hn : 2 ≤ n) (hnL : n ≤ L) :
    (n : ℝ) * (lcrBn ψ a + lcrBn ψ (cellBlock a (n - 1))) ≤
      8 * transferWeight g E (fun j => V (cellBlock a j)) n ^ 4 *
        ∑ p ∈ cellCoords (W := W) a n, ‖ψ p‖ ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk1 : 1 ≤ k := by omega
  have hL : 0 < L := by omega
  obtain ⟨hK1, -⟩ := transferWeight_bounds g E (fun j => V (cellBlock a j)) (k + 1)
  set K := transferWeight g E (fun j => V (cellBlock a j)) (k + 1) with hK
  have hbd := lcr_pair_bounds hg V hψ a (k + 1)
  rw [lcr_mass_eq ψ a hnL]
  set m := ∑ j ∈ Finset.range (k + 1), lcrBn ψ (cellBlock a j) with hm
  set P := lcrN (lcrPair ψ a) with hP
  have hP0 : 0 ≤ P := lcrN_nonneg _
  have hK0 : 0 ≤ K := by linarith
  have hx : ∀ j, 0 ≤ lcrBn ψ (cellBlock a j) := fun j => lcrBn_nonneg _ _
  have hsq : ∀ j, 1 ≤ j → lcrN (lcrPair ψ (cellBlock a j)) ^ 2 =
      lcrBn ψ (cellBlock a j) + lcrBn ψ (cellBlock a (j - 1)) := by
    intro j hj
    rw [lcr_pair_sq, lcr_cellBlock_cellBlock, show j + (L - 1) = (j - 1) + L by omega,
      lcr_cellBlock_add_L]
  have hsum1 : ∑ j ∈ Finset.range k, lcrBn ψ (cellBlock a (j + 1)) ≤ m := by
    have := Finset.sum_range_succ' (fun j => lcrBn ψ (cellBlock a j)) k
    rw [hm]
    have h0 := hx 0
    linarith
  have hsum2 : ∑ j ∈ Finset.range k, lcrBn ψ (cellBlock a j) ≤ m := by
    have := Finset.sum_range_succ (fun j => lcrBn ψ (cellBlock a j)) k
    rw [hm]
    have h0 := hx k
    linarith
  have hkP : (k : ℝ) * P ^ 2 ≤ K ^ 2 * (2 * m) := by
    calc (k : ℝ) * P ^ 2 = ∑ j ∈ Finset.range k, P ^ 2 := by simp
      _ ≤ ∑ j ∈ Finset.range k, K ^ 2 * (lcrBn ψ (cellBlock a (j + 1)) +
            lcrBn ψ (cellBlock a j)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := Finset.mem_range.mp hj
          have h1 := (hbd (j + 1) (by omega)).2
          have h2 := hsq (j + 1) (by omega)
          simp only [Nat.add_sub_cancel] at h2
          have h3 : P ^ 2 ≤ (K * lcrN (lcrPair ψ (cellBlock a (j + 1)))) ^ 2 :=
            pow_le_pow_left₀ hP0 h1 2
          rw [mul_pow, h2] at h3
          exact h3
      _ = K ^ 2 * (∑ j ∈ Finset.range k, lcrBn ψ (cellBlock a (j + 1)) +
            ∑ j ∈ Finset.range k, lcrBn ψ (cellBlock a j)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ K ^ 2 * (2 * m) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          linarith
  have hnP : ((k + 1 : ℕ) : ℝ) * P ^ 2 ≤ 4 * K ^ 2 * m := by
    have : ((k + 1 : ℕ) : ℝ) ≤ 2 * k := by
      push_cast
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      linarith
    nlinarith [sq_nonneg P]
  -- endpoint values
  have hend0 : lcrBn ψ a ≤ P ^ 2 := by
    rw [hP, lcr_pair_sq]
    linarith [lcrBn_nonneg ψ (cellBlock a (L - 1))]
  have hendk : lcrBn ψ (cellBlock a k) ≤ K ^ 2 * P ^ 2 := by
    have h1 := (hbd k (by omega)).1
    have h2 : lcrN (lcrPair ψ (cellBlock a k)) ^ 2 ≤ (K * P) ^ 2 :=
      pow_le_pow_left₀ (lcrN_nonneg _) h1 2
    rw [lcr_pair_sq, mul_pow] at h2
    linarith [lcrBn_nonneg ψ (cellBlock (cellBlock a k) (L - 1))]
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  have hsumends : lcrBn ψ a + lcrBn ψ (cellBlock a k) ≤ 2 * K ^ 2 * P ^ 2 := by
    nlinarith [sq_nonneg P]
  simp only [Nat.add_sub_cancel]
  calc ((k + 1 : ℕ) : ℝ) * (lcrBn ψ a + lcrBn ψ (cellBlock a k))
      ≤ ((k + 1 : ℕ) : ℝ) * (2 * K ^ 2 * P ^ 2) :=
        mul_le_mul_of_nonneg_left hsumends (by positivity)
    _ = 2 * K ^ 2 * (((k + 1 : ℕ) : ℝ) * P ^ 2) := by ring
    _ ≤ 2 * K ^ 2 * (4 * K ^ 2 * m) :=
        mul_le_mul_of_nonneg_left hnP (by positivity)
    _ = 8 * K ^ 4 * m := by ring

/-- The mass of a cell `B` of `n ≥ 1` blocks is at most `n K_B⁴` times the mass of its first two
blocks (proof of (E.4) [uva:eq:ratio-audit]). -/
private theorem lcr_cellB {g : ℝ} (hg : 1 ≤ g) {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    {E : ℝ} {ψ : Fin L × Fin W → ℂ} (hψ : Hdet g V *ᵥ ψ = (E : ℂ) • ψ) (c : Fin L) {n : ℕ}
    (hn : 1 ≤ n) (hnL : n ≤ L) :
    ∑ p ∈ cellCoords (W := W) c n, ‖ψ p‖ ^ 2 ≤
      (n : ℝ) * transferWeight g E (fun j => V (cellBlock c j)) n ^ 4 *
        (lcrBn ψ c + lcrBn ψ (cellBlock c 1)) := by
  have hL : 0 < L := by omega
  obtain ⟨hK1, -⟩ := transferWeight_bounds g E (fun j => V (cellBlock c j)) n
  set K := transferWeight g E (fun j => V (cellBlock c j)) n with hK
  have hbd := lcr_pair_bounds hg V hψ c n
  have hK0 : 0 ≤ K := by linarith
  rw [lcr_mass_eq ψ c hnL]
  set S := lcrBn ψ c + lcrBn ψ (cellBlock c 1) with hS
  have hq1 : lcrN (lcrPair ψ (cellBlock c 1)) ^ 2 = S := by
    rw [lcr_pair_sq, lcr_pred_succ, hS]
    ring
  have h0 : lcrN (lcrPair ψ c) ≤ K * lcrN (lcrPair ψ (cellBlock c 1)) := (hbd 1 hn).2
  have hpt : ∀ j ∈ Finset.range n, lcrBn ψ (cellBlock c j) ≤ K ^ 4 * S := by
    intro j hj
    have hj' := (Finset.mem_range.mp hj).le
    have h1 := (hbd j hj').1
    have h2 : lcrN (lcrPair ψ (cellBlock c j)) ≤ K * (K * lcrN (lcrPair ψ (cellBlock c 1))) :=
      h1.trans (mul_le_mul_of_nonneg_left h0 hK0)
    have h3 : lcrN (lcrPair ψ (cellBlock c j)) ^ 2 ≤
        (K * (K * lcrN (lcrPair ψ (cellBlock c 1)))) ^ 2 := pow_le_pow_left₀ (lcrN_nonneg _) h2 2
    have h4 : (K * (K * lcrN (lcrPair ψ (cellBlock c 1)))) ^ 2 = K ^ 4 * S := by
      rw [← hq1]; ring
    rw [lcr_pair_sq, h4] at h3
    linarith [lcrBn_nonneg ψ (cellBlock (cellBlock c j) (L - 1))]
  calc ∑ j ∈ Finset.range n, lcrBn ψ (cellBlock c j) ≤ ∑ j ∈ Finset.range n, K ^ 4 * S :=
        Finset.sum_le_sum hpt
    _ = (n : ℝ) * K ^ 4 * S := by simp [mul_assoc]

private theorem lcr_pathOp_mulVec {g : ℝ} {W n : ℕ} (V : Fin n → Matrix (Fin W) (Fin W) ℂ)
    (F : Fin n × Fin W → ℂ) (i : Fin n) (α : Fin W) :
    (pathOp g V 0 0 *ᵥ F) (i, α) =
      ((max 1 g : ℝ)⁻¹ : ℂ) * ((g : ℂ) * ∑ k : Fin n, (pathAdj n) i k * F (k, α) +
        (V i *ᵥ fun γ => F (i, γ)) α) := by
  have h1 : ((pathAdj n ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *ᵥ F) (i, α) =
      ∑ k : Fin n, (pathAdj n) i k * F (k, α) := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
  have h2 : ∀ B : Fin n → Matrix (Fin W) (Fin W) ℂ,
      (blockDiagOp B *ᵥ F) (i, α) = (B i *ᵥ fun γ => F (i, γ)) α := by
    intro B
    simp [Matrix.mulVec, dotProduct, blockDiagOp, Fintype.sum_prod_type]
  unfold pathOp
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.smul_apply, Pi.add_apply, Pi.smul_apply, h1, h2, h2]
  simp

private theorem lcr_adj_sum {n : ℕ} (i : Fin n) (c : ℕ → ℂ) :
    ∑ k : Fin n, (pathAdj n) i k * c k.val =
      (if 1 ≤ i.val then c (i.val - 1) else 0) + (if i.val + 1 < n then c (i.val + 1) else 0) := by
  have h1 : ∀ k : Fin n, (pathAdj n) i k * c k.val =
      (if k.val + 1 = i.val then c k.val else 0) + (if k.val = i.val + 1 then c k.val else 0) := by
    intro k
    simp only [pathAdj, Matrix.of_apply]
    by_cases h2 : k.val + 1 = i.val
    · have h4 : k.val ≠ i.val + 1 := by omega
      rw [ite_eq_left (Or.inr h2), ite_eq_left h2, ite_eq_right h4]
      simp
    · by_cases h5 : k.val = i.val + 1
      · rw [ite_eq_left (Or.inl h5.symm), ite_eq_right h2, ite_eq_left h5]
        simp
      · have h6 : ¬ (i.val + 1 = k.val ∨ k.val + 1 = i.val) := by omega
        rw [ite_eq_right h6, ite_eq_right h2, ite_eq_right h5]
        simp
  simp only [h1, Finset.sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun k => if k + 1 = i.val then c k else 0) n,
    Fin.sum_univ_eq_sum_range (fun k => if k = i.val + 1 then c k else 0) n]
  rw [Finset.sum_ite_eq' (Finset.range n) (i.val + 1) c]
  have e1 : ∑ k ∈ Finset.range n, (if k + 1 = i.val then c k else 0) =
      if 1 ≤ i.val then c (i.val - 1) else 0 := by
    by_cases hi : 1 ≤ i.val
    · rw [ite_eq_left hi]
      have : ∀ k, (k + 1 = i.val) ↔ (k = i.val - 1) := fun k => by omega
      simp only [this]
      rw [Finset.sum_ite_eq' (Finset.range n) (i.val - 1) c, ite_eq_left]
      exact Finset.mem_range.mpr (by omega)
    · rw [ite_eq_right hi]
      apply Finset.sum_eq_zero
      intro k _
      rw [ite_eq_right (by omega)]
  rw [e1]
  simp only [Finset.mem_range]

/-- The block `ψ_{a+n+j}` of `ψ` on the path `Λ = a+n, …, a−1`. -/
private def lcrLam {W L : ℕ} (ψ : Fin L × Fin W → ℂ) (a : Fin L) (n : ℕ) :
    Fin (L - n) × Fin W → ℂ :=
  fun p => ψ (cellBlock a (n + p.1.val), p.2)

/-- The boundary terms `ψ_{a+n-1}` at the first and `ψ_a` at the last block of `Λ`. -/
private def lcrRhs {W L : ℕ} (ψ : Fin L × Fin W → ℂ) (a : Fin L) (n : ℕ) :
    Fin (L - n) × Fin W → ℂ :=
  fun p => (if p.1.val = 0 then ψ (cellBlock a (n - 1), p.2) else 0) +
    (if p.1.val + 1 = L - n then ψ (a, p.2) else 0)

private theorem lcr_lam_eq {g : ℝ} (hg : 1 ≤ g) {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    {E : ℝ} {ψ : Fin L × Fin W → ℂ} (hψ : Hdet g V *ᵥ ψ = (E : ℂ) • ψ) (a : Fin L) {n : ℕ}
    (hn : 1 ≤ n) (hnL : n < L) :
    (pathOp g (fun j : Fin (L - n) => V (cellBlock a (n + j))) 0 0 -
        (E : ℂ) • (1 : Matrix (Fin (L - n) × Fin W) (Fin (L - n) × Fin W) ℂ)) *ᵥ
      lcrLam ψ a n = -lcrRhs ψ a n := by
  have hmax : max 1 g = g := max_eq_right hg
  have hg0 : (g : ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le one_pos hg).ne'
  funext ⟨i, α⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply,
    lcr_pathOp_mulVec, hmax]
  have hsum := lcr_adj_sum i (fun j => ψ (cellBlock a (n + j), α))
  have hrow := lcr_row hg V hψ (cellBlock a (n + i.val)) α
  have hb1 : ψ (cellBlock (cellBlock a (n + i.val)) 1, α) =
      (if i.val + 1 < L - n then ψ (cellBlock a (n + (i.val + 1)), α) else 0) +
        (if i.val + 1 = L - n then ψ (a, α) else 0) := by
    rw [lcr_cellBlock_cellBlock]
    have hi := i.isLt
    by_cases h : i.val + 1 < L - n
    · rw [ite_eq_left h, ite_eq_right (by omega), add_zero, ← Nat.add_assoc]
    · have h' : i.val + 1 = L - n := by omega
      rw [ite_eq_right h, ite_eq_left h', zero_add, show n + i.val + 1 = L by omega,
        lcr_cellBlock_L]
  have hb2 : ψ (cellBlock (cellBlock a (n + i.val)) (L - 1), α) =
      (if 1 ≤ i.val then ψ (cellBlock a (n + (i.val - 1)), α) else 0) +
        (if i.val = 0 then ψ (cellBlock a (n - 1), α) else 0) := by
    rw [lcr_cellBlock_cellBlock]
    by_cases h : 1 ≤ i.val
    · rw [ite_eq_left h, ite_eq_right (by omega), add_zero,
        show n + i.val + (L - 1) = (n + (i.val - 1)) + L by omega, lcr_cellBlock_add_L]
    · have h' : i.val = 0 := by omega
      rw [ite_eq_right h, ite_eq_left h', zero_add, show n + i.val + (L - 1) = (n - 1) + L by omega,
        lcr_cellBlock_add_L]
  rw [hb1, hb2] at hrow
  simp only [lcrLam, lcrRhs, Pi.neg_apply, Matrix.mulVec, dotProduct]
  rw [show ∑ k : Fin (L - n), (pathAdj (L - n)) i k * ψ (cellBlock a (n + k.val), α) =
      (if 1 ≤ i.val then ψ (cellBlock a (n + (i.val - 1)), α) else 0) +
        (if i.val + 1 < L - n then ψ (cellBlock a (n + (i.val + 1)), α) else 0) from hsum]
  simp only [smul_eq_mul]
  have hgg : (g : ℂ)⁻¹ * g = 1 := inv_mul_cancel₀ hg0
  generalize (if 1 ≤ i.val then ψ (cellBlock a (n + (i.val - 1)), α) else 0) = s1 at hrow ⊢
  generalize (if i.val + 1 < L - n then ψ (cellBlock a (n + (i.val + 1)), α) else 0) = s2
    at hrow ⊢
  linear_combination hrow + (s1 + s2) * hgg

private theorem lcr_sum_ite {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (c : ι)
    (f : ι → κ → ℂ) : ∑ x, ∑ y, (if x = c then f x y else 0) = ∑ y, f c y := by
  rw [Finset.sum_eq_single c]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- Schur identity on `Λ = ℤ_L ∖ A`: the mass of block `i` of `Λ` is at most
`(‖G(i,0)‖² + ‖G(i,last)‖²)` times the mass of the two blocks of `A` adjacent to `Λ`
(proof of (E.4) [uva:eq:ratio-audit]). -/
private theorem lcr_lam_green {g : ℝ} (hg : 1 ≤ g) {W L : ℕ}
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) {E : ℝ} {ψ : Fin L × Fin W → ℂ}
    (hψ : Hdet g V *ᵥ ψ = (E : ℂ) • ψ) (a : Fin L) {n : ℕ} (hn : 1 ≤ n) (hnL : n < L)
    (hΛ : (pathOp g (fun j : Fin (L - n) => V (cellBlock a (n + j))) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin (L - n) × Fin W) (Fin (L - n) × Fin W) ℂ)).det ≠ 0)
    (i : Fin (L - n)) (h0 : 0 < L - n) :
    lcrBn ψ (cellBlock a (n + i.val)) ≤
      (‖blockOf (resolventMat (pathOp g (fun j : Fin (L - n) => V (cellBlock a (n + j))) 0 0) E)
          i ⟨0, h0⟩‖ ^ 2 +
        ‖blockOf (resolventMat (pathOp g (fun j : Fin (L - n) => V (cellBlock a (n + j))) 0 0) E)
          i ⟨L - n - 1, by omega⟩‖ ^ 2) *
        (lcrBn ψ a + lcrBn ψ (cellBlock a (n - 1))) := by
  set H := pathOp g (fun j : Fin (L - n) => V (cellBlock a (n + j))) 0 0 with hH
  set G := resolventMat H (E : ℂ) with hG
  have hM := lcr_lam_eq hg V hψ a hn hnL
  rw [← hH] at hM
  have hlam : lcrLam ψ a n = -(G *ᵥ lcrRhs ψ a n) := by
    have hu : IsUnit (H - (E : ℂ) • (1 : Matrix (Fin (L - n) × Fin W) (Fin (L - n) × Fin W) ℂ)).det
      := isUnit_iff_ne_zero.mpr hΛ
    calc lcrLam ψ a n = (H - (E : ℂ) • (1 : Matrix (Fin (L - n) × Fin W)
            (Fin (L - n) × Fin W) ℂ))⁻¹ *ᵥ ((H - (E : ℂ) • (1 : Matrix (Fin (L - n) × Fin W)
            (Fin (L - n) × Fin W) ℂ)) *ᵥ lcrLam ψ a n) := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      _ = -(G *ᵥ lcrRhs ψ a n) := by
          rw [hM, Matrix.mulVec_neg]
          rfl
  set u : Fin W → ℂ := fun β => ψ (cellBlock a (n - 1), β) with hu
  set w : Fin W → ℂ := fun β => ψ (a, β) with hw
  have hvec : (fun α => ψ (cellBlock a (n + i.val), α)) =
      -(blockOf G i ⟨0, h0⟩ *ᵥ u + blockOf G i ⟨L - n - 1, by omega⟩ *ᵥ w) := by
    funext α
    have h1 := congrFun hlam (i, α)
    have h2 : (G *ᵥ lcrRhs ψ a n) (i, α) =
        (blockOf G i ⟨0, h0⟩ *ᵥ u) α + (blockOf G i ⟨L - n - 1, by omega⟩ *ᵥ w) α := by
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, lcrRhs, mul_add,
        Finset.sum_add_distrib, mul_ite, mul_zero, blockOf, Matrix.of_apply, hu, hw]
      have e1 : ∀ k : Fin (L - n), (k.val = 0) ↔ (k = ⟨0, h0⟩) := fun k => by
        simp [Fin.ext_iff]
      have e2 : ∀ k : Fin (L - n), (k.val + 1 = L - n) ↔ (k = ⟨L - n - 1, by omega⟩) :=
        fun k => by simp only [Fin.ext_iff]; have := k.isLt; omega
      simp only [e1, e2]
      rw [lcr_sum_ite, lcr_sum_ite]
    have h3 : ψ (cellBlock a (n + i.val), α) = -((G *ᵥ lcrRhs ψ a n) (i, α)) := h1
    rw [h3, h2]
    rfl
  have hnorm : lcrBn ψ (cellBlock a (n + i.val)) =
      lcrN (fun α => ψ (cellBlock a (n + i.val), α)) ^ 2 := by
    rw [lcrN_sq]
    rfl
  have hn1 : lcrN (-(blockOf G i ⟨0, h0⟩ *ᵥ u + blockOf G i ⟨L - n - 1, by omega⟩ *ᵥ w)) ≤
      ‖blockOf G i ⟨0, h0⟩‖ * lcrN u + ‖blockOf G i ⟨L - n - 1, by omega⟩‖ * lcrN w := by
    rw [lcrN_neg]
    exact (lcrN_add _ _).trans (add_le_add (lcrN_mulVec _ _) (lcrN_mulVec _ _))
  have hu2 : lcrN u ^ 2 = lcrBn ψ (cellBlock a (n - 1)) := by
    rw [lcrN_sq]
    rfl
  have hw2 : lcrN w ^ 2 = lcrBn ψ a := by
    rw [lcrN_sq]
    rfl
  rw [hnorm, hvec]
  set p := ‖blockOf G i ⟨0, h0⟩‖ with hp
  set q := ‖blockOf G i ⟨L - n - 1, by omega⟩‖ with hq
  calc lcrN (-(blockOf G i ⟨0, h0⟩ *ᵥ u + blockOf G i ⟨L - n - 1, by omega⟩ *ᵥ w)) ^ 2
      ≤ (p * lcrN u + q * lcrN w) ^ 2 := pow_le_pow_left₀ (lcrN_nonneg _) hn1 2
    _ ≤ (p ^ 2 + q ^ 2) * (lcrN u ^ 2 + lcrN w ^ 2) := by
        nlinarith [sq_nonneg (p * lcrN w - q * lcrN u)]
    _ = (p ^ 2 + q ^ 2) * (lcrBn ψ a + lcrBn ψ (cellBlock a (n - 1))) := by
        rw [hu2, hw2]
        ring

private theorem lcr_combine {nA nB mA mB KA KB g0 g1 SA x0 x1 : ℝ} (hKA : 1 ≤ KA) (hKB : 1 ≤ KB)
    (hnA : 0 ≤ nA) (hnB : 0 ≤ nB) (hmA : 0 ≤ mA) (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1)
    (hA : nA * SA ≤ 8 * KA ^ 4 * mA) (hB : mB ≤ nB * KB ^ 4 * (x0 + x1))
    (hx0 : x0 ≤ g0 * SA) (hx1 : x1 ≤ g1 * SA) :
    nA * mB ≤ 16 * KA ^ 4 * KB ^ 4 * nB * mA * (g0 + g1) := by
  have hKA0 : 0 ≤ KA := by linarith
  have hKB0 : 0 ≤ KB := by linarith
  have h1 : mB ≤ nB * KB ^ 4 * ((g0 + g1) * SA) := by
    refine hB.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    linarith
  calc nA * mB ≤ nA * (nB * KB ^ 4 * ((g0 + g1) * SA)) := mul_le_mul_of_nonneg_left h1 hnA
    _ = nB * KB ^ 4 * (g0 + g1) * (nA * SA) := by ring
    _ ≤ nB * KB ^ 4 * (g0 + g1) * (8 * KA ^ 4 * mA) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ ≤ 16 * KA ^ 4 * KB ^ 4 * nB * mA * (g0 + g1) := by
        have : 0 ≤ nB * KB ^ 4 * (g0 + g1) * (KA ^ 4 * mA) := by positivity
        nlinarith

private theorem lcr_roots_finite {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    {E : ℝ | (M - (E : ℂ) • (1 : Matrix ι ι ℂ)).det = 0}.Finite := by
  have hfin : ((M.charpoly.roots.toFinset : Finset ℂ) : Set ℂ).Finite := Finset.finite_toSet _
  refine (hfin.preimage Complex.ofReal_injective.injOn).subset ?_
  intro E hE
  simp only [Set.mem_ofPred_eq] at hE
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots (Matrix.charpoly_monic M).ne_zero, Polynomial.IsRoot,
    Matrix.eval_charpoly]
  have h1 : Matrix.scalar ι (E : ℂ) - M = -(M - (E : ℂ) • (1 : Matrix ι ι ℂ)) := by
    rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [h1, Matrix.det_neg, hE, mul_zero]

/-- A family `H t = H 0 + c t P`, `P` a coordinate projection, of Hermitian matrices has only
finitely many members with an eigenvector for `E` that is not killed by `P`: the images under `P`
of such eigenvectors are pairwise orthogonal (proof of (E.3)
[uva:eq:cell-correlator]). -/
private theorem lcr_orth_finite {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι)
    (H : ℝ → Matrix ι ι ℂ)
    (hherm : ∀ t, (H t).IsHermitian) (c : ℝ) (hc : c ≠ 0)
    (hline : ∀ t, H t = H 0 + ((c * t : ℝ) : ℂ) • coordProj T) (E : ℝ)
    (hpos : ∀ t (ψ : ι → ℂ), ψ ≠ 0 → H t *ᵥ ψ = (E : ℂ) • ψ → ∃ p ∈ T, ψ p ≠ 0) :
    {t : ℝ | ∃ ψ : ι → ℂ, ψ ≠ 0 ∧ H t *ᵥ ψ = (E : ℂ) • ψ}.Finite := by
  set S : Set ℝ := {t : ℝ | ∃ ψ : ι → ℂ, ψ ≠ 0 ∧ H t *ᵥ ψ = (E : ℂ) • ψ} with hS
  choose ψ hψ0 hψE using fun t : S => t.2
  have hPy : ∀ x : ι → ℂ, coordProj T *ᵥ x = fun p => if p ∈ T then x p else 0 := by
    intro x
    funext p
    simp only [coordProj, Matrix.mulVec_diagonal]
    split_ifs <;> simp
  let v : S → EuclideanSpace ℂ ι := fun t => WithLp.toLp 2 (coordProj T *ᵥ ψ t)
  have hv0 : ∀ t, v t ≠ 0 := by
    intro t h0
    obtain ⟨p, hp, hpne⟩ := hpos t (ψ t) (hψ0 t) (hψE t)
    have := congrArg (fun z : EuclideanSpace ℂ ι => z.ofLp p) h0
    simp only [v, hPy, hp, ↓reduceIte, PiLp.zero_apply] at this
    exact hpne this
  have horth : Pairwise fun t s : S => inner ℂ (v t) (v s) = 0 := by
    intro t s hts
    have hne : (t : ℝ) ≠ s := fun h => hts (Subtype.ext h)
    have hk : ((c * ((t : ℝ) - s) : ℝ) : ℂ) ≠ 0 := by
      have : c * ((t : ℝ) - s) ≠ 0 := mul_ne_zero hc (sub_ne_zero.mpr hne)
      exact_mod_cast this
    have hdiff : H t = H s + ((c * ((t : ℝ) - s) : ℝ) : ℂ) • coordProj T := by
      rw [hline t, hline s]
      have : ((c * (t : ℝ) : ℝ) : ℂ) = ((c * (s : ℝ) : ℝ) : ℂ) + ((c * ((t : ℝ) - s) : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, add_smul, add_assoc]
    have e1 : star (ψ t) ⬝ᵥ (H t *ᵥ ψ s) = (E : ℂ) * (star (ψ t) ⬝ᵥ ψ s) := by
      have h1 : star (H t *ᵥ ψ t) = star (ψ t) ᵥ* H t := by
        rw [Matrix.star_mulVec, (hherm t).eq]
      rw [Matrix.dotProduct_mulVec, ← h1, hψE t]
      simp [star_smul, smul_dotProduct]
    have e2 : star (ψ t) ⬝ᵥ (H t *ᵥ ψ s) = (E : ℂ) * (star (ψ t) ⬝ᵥ ψ s) +
        ((c * ((t : ℝ) - s) : ℝ) : ℂ) * (star (ψ t) ⬝ᵥ (coordProj T *ᵥ ψ s)) := by
      rw [hdiff, Matrix.add_mulVec, Matrix.smul_mulVec, hψE s, dotProduct_add, dotProduct_smul,
        dotProduct_smul]
      simp only [smul_eq_mul]
    have hzero : ((c * ((t : ℝ) - s) : ℝ) : ℂ) * (star (ψ t) ⬝ᵥ (coordProj T *ᵥ ψ s)) = 0 := by
      linear_combination e1 - e2
    have hX : star (ψ t) ⬝ᵥ (coordProj T *ᵥ ψ s) = 0 := (mul_eq_zero.mp hzero).resolve_left hk
    change inner ℂ (WithLp.toLp 2 (coordProj T *ᵥ ψ t)) (WithLp.toLp 2 (coordProj T *ᵥ ψ s)) = 0
    rw [EuclideanSpace.inner_toLp_toLp, ← hX]
    simp only [dotProduct, hPy, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp [mul_comm]
  have hli := linearIndependent_of_ne_zero_of_inner_eq_zero hv0 horth
  exact Set.finite_coe_iff.mp hli.finite

private theorem lcr_ext_not_mem {L : ℕ} (a : Fin L) {n : ℕ} (hnL : n < L) (j : ℕ)
    (hj : j < L - n) : cellBlock a (n + j) ∉ cellSet a n := by
  intro h
  simp only [cellSet, Finset.mem_image, Finset.mem_range] at h
  obtain ⟨i, hi, hij⟩ := h
  have h1 := congrArg Fin.val hij
  simp only [cellBlock] at h1
  have h2 : i % L = (n + j) % L :=
    Nat.ModEq.add_left_cancel' a.val (show (a.val + i) ≡ (a.val + (n + j)) [MOD L] from h1)
  rw [Nat.mod_eq_of_lt (by omega : i < L), Nat.mod_eq_of_lt (by omega : n + j < L)] at h2
  omega

/-- Moving the sample along `scalarDir W L (cellSet a n)` by `t` adds a multiple of the
projection onto the cell `A` to the model (1.3) [eq:model], for every `g > 0`. -/
private theorem lcr_Hmat_line {g : ℝ} {W L n : ℕ} (a : Fin L) (ω : Ω W L) (t : ℝ) :
    Hmat g W L (ω + t • scalarDir W L (cellSet a n)) =
      Hmat g W L ω +
        (((max 1 g)⁻¹ * (t / ((W : ℝ) * Real.sqrt (cellSet a n).card)) : ℝ) : ℂ) •
          coordProj (cellCoords (W := W) a n) := by
  have hblock : ∀ b : Fin L,
      gueBlock W L (ω + t • scalarDir W L (cellSet a n)) b =
        gueBlock W L ω b +
          if b ∈ cellSet a n then
            ((t / ((W : ℝ) * Real.sqrt (cellSet a n).card) : ℝ) : ℂ) •
              (1 : Matrix (Fin W) (Fin W) ℂ) else 0 :=
    fun b => gueBlock_add_smul_scalarDir W L _ ω t b
  unfold Hmat Hdet
  have hfun : gueBlock W L (ω + t • scalarDir W L (cellSet a n)) =
      fun b => gueBlock W L ω b +
        if b ∈ cellSet a n then
          ((t / ((W : ℝ) * Real.sqrt (cellSet a n).card) : ℝ) : ℂ) •
            (1 : Matrix (Fin W) (Fin W) ℂ) else 0 := funext hblock
  rw [hfun]
  have hcc : ∀ (b : Fin L) (α : Fin W), (b, α) ∈ cellCoords (W := W) a n ↔ b ∈ cellSet a n := by
    intro b α
    simp [cellCoords]
  ext ⟨b, α⟩ ⟨b', β⟩
  by_cases hbb : b = b'
  · subst hbb
    by_cases hb : b ∈ cellSet a n
    · by_cases hαβ : α = β
      · subst hαβ
        simp [blockDiagOp, coordProj, hb, hcc, Matrix.diagonal]
        ring
      · simp [blockDiagOp, coordProj, hb, hαβ, hcc, Matrix.diagonal]
    · simp [blockDiagOp, coordProj, hb, hcc, Matrix.diagonal]
      ring
  · simp [blockDiagOp, coordProj, hbb, hcc, Matrix.diagonal]

private theorem lcr_pathOp_line {g : ℝ} {W L n : ℕ} (a : Fin L) (hnL : n < L) (ω : Ω W L)
    (t : ℝ) :
    pathOp g (fun j : Fin (L - n) =>
        gueBlock W L (ω + t • scalarDir W L (cellSet a n)) (cellBlock a (n + j))) 0 0 =
      pathOp g (fun j : Fin (L - n) => gueBlock W L ω (cellBlock a (n + j))) 0 0 := by
  have : (fun j : Fin (L - n) =>
        gueBlock W L (ω + t • scalarDir W L (cellSet a n)) (cellBlock a (n + j))) =
      fun j : Fin (L - n) => gueBlock W L ω (cellBlock a (n + j)) := by
    funext j
    rw [gueBlock_add_smul_scalarDir, ite_eq_right (lcr_ext_not_mem a hnL j j.isLt), add_zero]
  rw [this]

private theorem lcr_continuous_gueBlock (W L : ℕ) (b : Fin L) (α β : Fin W) :
    Continuous fun ω : Ω W L => gueBlock W L ω b α β := by
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

private theorem lcr_continuous_Hmat (g : ℝ) (W L : ℕ) :
    Continuous fun ω : Ω W L => Hmat g W L ω := by
  refine continuous_matrix fun p q => ?_
  simp only [Hmat, Hdet, Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply,
    blockDiagOp, Matrix.of_apply, smul_eq_mul]
  by_cases h : p.1 = q.1
  · simp only [h, ↓reduceIte]
    have := lcr_continuous_gueBlock W L q.1 p.2 q.2
    fun_prop
  · simp only [h, ↓reduceIte]
    fun_prop

private theorem lcr_continuous_pathOp (g : ℝ) (W L n : ℕ) (a : Fin L) :
    Continuous fun ω : Ω W L =>
      pathOp g (fun j : Fin (L - n) => gueBlock W L ω (cellBlock a (n + j))) 0 0 := by
  refine continuous_matrix fun p q => ?_
  simp only [pathOp, Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply,
    blockDiagOp, Matrix.of_apply, smul_eq_mul]
  by_cases h : p.1 = q.1
  · simp only [h, ↓reduceIte]
    have := lcr_continuous_gueBlock W L (cellBlock a (n + q.1.val)) p.2 q.2
    fun_prop
  · simp only [h, ↓reduceIte]
    fun_prop

private theorem lcr_measurableSet_shared {X ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ]
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (A : X → Matrix ι ι ℂ)
    (B : X → Matrix κ κ ℂ) (hA : Continuous A) (hB : Continuous B) :
    MeasurableSet {x | ∃ E : ℝ, (A x - (E : ℂ) • (1 : Matrix ι ι ℂ)).det = 0 ∧
      (B x - (E : ℂ) • (1 : Matrix κ κ ℂ)).det = 0} := by
  have hrepr : {x | ∃ E : ℝ, (A x - (E : ℂ) • (1 : Matrix ι ι ℂ)).det = 0 ∧
      (B x - (E : ℂ) • (1 : Matrix κ κ ℂ)).det = 0} =
      ⋃ R : ℕ, Prod.fst '' {p : X × Set.Icc (-(R : ℝ)) R |
        (A p.1 - ((p.2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).det = 0 ∧
        (B p.1 - ((p.2 : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)).det = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, Prod.exists, exists_and_right,
      exists_eq_right]
    constructor
    · rintro ⟨E, h1, h2⟩
      obtain ⟨R, hR⟩ := exists_nat_ge |E|
      exact ⟨R, ⟨E, abs_le.mp hR⟩, h1, h2⟩
    · rintro ⟨R, ⟨E, hE⟩, h1, h2⟩
      exact ⟨E, h1, h2⟩
  rw [hrepr]
  refine MeasurableSet.iUnion fun R => IsClosed.measurableSet ?_
  have h1 : IsClosed {p : X × Set.Icc (-(R : ℝ)) R |
      (A p.1 - ((p.2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).det = 0} :=
    isClosed_eq (((hA.comp continuous_fst).sub ((Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_snd)).smul continuous_const)).matrix_det)
      continuous_const
  have h2 : IsClosed {p : X × Set.Icc (-(R : ℝ)) R |
      (B p.1 - ((p.2 : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)).det = 0} :=
    isClosed_eq (((hB.comp continuous_fst).sub ((Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_snd)).smul continuous_const)).matrix_det)
      continuous_const
  exact isClosedMap_fst_of_compactSpace _ (h1.inter h2)

/-- (E.4) [uva:eq:ratio-audit]: `Λ = a+n_A, …, a−1` is `ℤ_L ∖ A` in cyclic order, `B` starts at
offset `j₀` of `Λ`, and `x₊ = 0`, `x₋ = L − n_A − 1` are the endpoints of `Λ`. -/
theorem cell_mass_ratio {g : ℝ} (hg : 1 ≤ g) {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (a : Fin L) {nA nB j₀ : ℕ} (hnA : 2 ≤ nA) (hnB : 2 ≤ nB) (hL : nA + j₀ + nB ≤ L) {E : ℝ}
    {ψ : Fin L × Fin W → ℂ} (hψ : Hdet g V *ᵥ ψ = (E : ℂ) • ψ)
    (hΛ : (pathOp g (fun j : Fin (L - nA) => V (cellBlock a (nA + j))) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin (L - nA) × Fin W) (Fin (L - nA) × Fin W) ℂ)).det ≠ 0) :
    (nA : ℝ) * ∑ p ∈ cellCoords (cellBlock a (nA + j₀)) nB, ‖ψ p‖ ^ 2 ≤
      16 * transferWeight g E (fun j => V (cellBlock a j)) nA ^ 4 *
        transferWeight g E (fun j => V (cellBlock (cellBlock a (nA + j₀)) j)) nB ^ 4 * nB *
        (∑ p ∈ cellCoords a nA, ‖ψ p‖ ^ 2) *
        ∑ i : Fin 2, ∑ x : Fin 2, ‖blockOf (resolventMat
          (pathOp g (fun j : Fin (L - nA) => V (cellBlock a (nA + j))) 0 0) E)
            ⟨j₀ + i, by have := i.isLt; omega⟩
            (if x = 0 then ⟨0, by omega⟩ else ⟨L - nA - 1, by omega⟩)‖ ^ 2 := by
  have hnAL : nA < L := by omega
  have hA := lcr_cellA hg V hψ a hnA hnAL.le
  have hB := lcr_cellB hg V hψ (cellBlock a (nA + j₀)) (n := nB) (by omega) (by omega)
  have hG0 := lcr_lam_green hg V hψ a (n := nA) (by omega) hnAL hΛ ⟨j₀, by omega⟩ (by omega)
  have hG1 := lcr_lam_green hg V hψ a (n := nA) (by omega) hnAL hΛ ⟨j₀ + 1, by omega⟩ (by omega)
  have hb1 : cellBlock (cellBlock a (nA + j₀)) 1 = cellBlock a (nA + (j₀ + 1)) := by
    rw [lcr_cellBlock_cellBlock, Nat.add_assoc]
  rw [hb1]  at hB
  simp only [Fin.sum_univ_two, Fin.isValue, ite_true, one_ne_zero, ite_false,
    Fin.val_zero, Fin.val_one, add_zero]
  simp only at hG0 hG1
  exact lcr_combine (transferWeight_bounds g E (fun j => V (cellBlock a j)) nA).1
    (transferWeight_bounds g E (fun j => V (cellBlock (cellBlock a (nA + j₀)) j)) nB).1
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (by positivity) (by positivity) hA hB hG0 hG1

/-- No eigenvalue of the model (1.3) [eq:model] lies in the spectrum of `H_{ℤ_L ∖ A}`, almost
surely, for `g > 0` and a cell `A` with `2 ≤ n < L`. -/
theorem ae_cellExterior_det_ne_zero {g : ℝ} (hg : 0 < g) {W L n : ℕ} (hn : 2 ≤ n) (hnL : n < L)
    (a : Fin L) :
    ∀ᵐ ω ∂(μ W L), ∀ k,
      (pathOp g (fun j : Fin (L - n) => gueBlock W L ω (cellBlock a (n + j))) 0 0 -
      ((Hmat_isHermitian g W L ω).eigenvalues k : ℂ) •
        (1 : Matrix (Fin (L - n) × Fin W) (Fin (L - n) × Fin W) ℂ)).det ≠ 0 := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · exact Filter.Eventually.of_forall fun ω k => Fin.elim0 k.2
  set N : Set (Ω W L) := {ω | ∃ E : ℝ,
    (Hmat g W L ω - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)).det = 0 ∧
    (pathOp g (fun j : Fin (L - n) => gueBlock W L ω (cellBlock a (n + j))) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin (L - n) × Fin W) (Fin (L - n) × Fin W) ℂ)).det = 0} with hN
  have hNm : MeasurableSet N :=
    lcr_measurableSet_shared (fun ω : Ω W L => Hmat g W L ω)
      (fun ω : Ω W L => pathOp g (fun j : Fin (L - n) => gueBlock W L ω (cellBlock a (n + j))) 0 0)
      (lcr_continuous_Hmat g W L) (lcr_continuous_pathOp g W L n a)
  have hN0 : μ W L N = 0 := by
    have hS : (cellSet a n).Nonempty :=
      ⟨cellBlock a 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩
    set e : Ω W L := scalarDir W L (cellSet a n) with he
    have hsq : ∑ p, e p ^ 2 = 1 := sum_sq_scalarDir hW hS
    have hline := lintegral_stdGauss_line e hsq (F := N.indicator 1)
      (measurable_one.indicator hNm)
    have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
    have hpos : 0 < (W : ℝ) * Real.sqrt (cellSet a n).card :=
      mul_pos (by exact_mod_cast hW) (Real.sqrt_pos.mpr (by exact_mod_cast hS.card_pos))
    have hmax : 0 < max 1 g := lt_max_of_lt_left one_pos
    have hinner : ∀ ω₁ : Ω W L,
        ∫⁻ t, N.indicator (1 : Ω W L → ℝ≥0∞) (ω₁ + t • e) ∂(gaussianReal 0 1) = 0 := by
      intro ω₁
      set M := pathOp g (fun j : Fin (L - n) => gueBlock W L ω₁ (cellBlock a (n + j))) 0 0
        with hM
      have hR := lcr_roots_finite M
      have hsub : {t : ℝ | ω₁ + t • e ∈ N} ⊆ ⋃ E ∈ {E : ℝ | (M - (E : ℂ) • 1).det = 0},
          {t : ℝ | ∃ ψ : Fin L × Fin W → ℂ, ψ ≠ 0 ∧
            Hmat g W L (ω₁ + t • e) *ᵥ ψ = (E : ℂ) • ψ} := by
        intro t ht
        obtain ⟨E, h1, h2⟩ := ht
        rw [lcr_pathOp_line a hnL ω₁ t] at h2
        simp only [Set.mem_iUnion]
        refine ⟨E, h2, ?_⟩
        obtain ⟨ψ, hψ0, hψ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h1
        refine ⟨ψ, hψ0, ?_⟩
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hψ
        exact hψ
      have hfin : {t : ℝ | ω₁ + t • e ∈ N}.Finite := by
        refine Set.Finite.subset (hR.biUnion fun E _ => ?_) hsub
        refine lcr_orth_finite (cellCoords (W := W) a n) (fun t => Hmat g W L (ω₁ + t • e))
          (fun t => Hmat_isHermitian g W L _)
          ((max 1 g)⁻¹ / ((W : ℝ) * Real.sqrt (cellSet a n).card))
          (div_ne_zero (inv_ne_zero hmax.ne') hpos.ne') ?_ E ?_
        · intro t
          have h0 : Hmat g W L (ω₁ + (0 : ℝ) • e) = Hmat g W L ω₁ := by simp
          change Hmat g W L (ω₁ + t • e) = Hmat g W L (ω₁ + (0 : ℝ) • e) + _
          rw [h0, lcr_Hmat_line a ω₁ t]
          congr 3
          ring
        · intro t ψ hψ0 hψ
          by_contra hcon
          have hmass := cell_mass_pos hg (gueBlock W L (ω₁ + t • e)) hψ hψ0 a hn
          have hz : ∑ p ∈ cellCoords (W := W) a n, ‖ψ p‖ ^ 2 = 0 :=
            Finset.sum_eq_zero fun p hp => by
              have : ψ p = 0 := by_contra fun h => hcon ⟨p, hp, h⟩
              simp [this]
          linarith
      have hnull : gaussianReal 0 1 {t : ℝ | ω₁ + t • e ∈ N} = 0 := hfin.measure_zero _
      have hae : ∀ᵐ t ∂(gaussianReal 0 1), N.indicator (1 : Ω W L → ℝ≥0∞) (ω₁ + t • e) = 0 := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht
        exact Set.indicator_of_notMem ht _
      rw [lintegral_congr_ae hae, lintegral_zero]
    rw [← lintegral_indicator_one hNm]
    change ∫⁻ ω, N.indicator 1 ω ∂(stdGauss (Fin L × Fin W × Fin W)) = 0
    have hzero : ∀ ω : Ω W L, ∫⁻ t, N.indicator (1 : Ω W L → ℝ≥0∞)
        (ω - (∑ i, ω i * e i) • e + t • e) ∂(gaussianReal 0 1) = 0 :=
      fun ω => hinner _
    rw [hline, lintegral_congr hzero, lintegral_zero]
  rw [ae_iff]
  refine measure_mono_null ?_ hN0
  intro ω hω
  simp only [Set.mem_ofPred_eq, not_forall, not_not] at hω
  obtain ⟨k, hk⟩ := hω
  refine ⟨_, ?_, hk⟩
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨((Hmat_isHermitian g W L ω).eigenvectorBasis k).ofLp, ?_, ?_⟩
  · intro h
    exact ((Hmat_isHermitian g W L ω).eigenvectorBasis.orthonormal.ne_zero k) (by simpa using h)
  · rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      (Hmat_isHermitian g W L ω).mulVec_eigenvectorBasis k, sub_eq_zero]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _)

end LSBA
