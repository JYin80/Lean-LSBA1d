import LSBA.Upper.LargeCells
import LSBA.Transfer.Path

/-!
# Crossings of one cell

(E.11) [uva:eq:cross-audit]: for the block operator (1.3) [eq:model] with `g ≥ 1`, a cell
`A = a, …, a+n−1` with `2 ≤ n < L`, and `H(u) = H + c u P_A`, `c > 0`, the number of
`u ∈ [ℓ, ℓ+1]` with `E ∈ σ(H(u))`, counted with kernel dimension, is at most
`2W + 2 c n W sup_{u ∈ [ℓ, ℓ+1]} K_A(E − c u)²`, for every `E` outside the spectrum of the
Dirichlet path `ℤ_L ∖ A`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Euclidean norms and the cell recurrence -/

/-- The Euclidean norm of a coordinate vector. -/
private def lccN {ι : Type*} [Fintype ι] (x : ι → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖

private lemma lccN_nonneg {ι : Type*} [Fintype ι] (x : ι → ℂ) : 0 ≤ lccN x := norm_nonneg _

private lemma lccN_sq {ι : Type*} [Fintype ι] (x : ι → ℂ) : lccN x ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  unfold lccN
  rw [EuclideanSpace.norm_sq_eq]

private lemma lccN_zero {ι : Type*} [Fintype ι] : lccN (0 : ι → ℂ) = 0 := by
  have h := lccN_sq (0 : ι → ℂ)
  simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, pow_eq_zero_iff] at h
  exact h

private lemma lccN_add_le {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    lccN (x + y) ≤ lccN x + lccN y := by
  unfold lccN
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

private lemma lccN_sum_le {ι κ : Type*} [Fintype ι] (s : Finset κ) (x : κ → ι → ℂ) :
    lccN (∑ k ∈ s, x k) ≤ ∑ k ∈ s, lccN (x k) := by
  induction s using Finset.induction_on with
  | empty => simp [lccN_zero]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    exact le_trans (lccN_add_le _ _) (by linarith)

private lemma lccN_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x : ι → ℂ) : lccN (A *ᵥ x) ≤ ‖A‖ * lccN x :=
  Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)

private lemma lccN_pairVec_sq {W : ℕ} (x y : Fin W → ℂ) :
    lccN (pairVec x y) ^ 2 = lccN x ^ 2 + lccN y ^ 2 := by
  rw [lccN_sq, lccN_sq, lccN_sq, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [pairVec]

private lemma lccN_le_pairVec {W : ℕ} (x y : Fin W → ℂ) : lccN x ≤ lccN (pairVec x y) := by
  have h := lccN_pairVec_sq x y
  have h2 : lccN x ^ 2 ≤ lccN (pairVec x y) ^ 2 := by nlinarith [sq_nonneg (lccN y)]
  exact (pow_le_pow_iff_left₀ (lccN_nonneg _) (lccN_nonneg _) two_ne_zero).mp h2

private lemma lccN_pairVec_zero {W : ℕ} (x : Fin W → ℂ) : lccN (pairVec x 0) = lccN x := by
  have h := lccN_pairVec_sq x 0
  rw [lccN_zero] at h
  have h2 : lccN (pairVec x 0) ^ 2 = lccN x ^ 2 := by simpa using h
  exact (pow_left_inj₀ (lccN_nonneg _) (lccN_nonneg _) two_ne_zero).mp h2

private lemma lcc_transferMat_mulVec_pairVec {W : ℕ} (g : ℝ) (z : ℂ)
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

private lemma lcc_isUnit_transferMat {W : ℕ} (g : ℝ) (z : ℂ) (V : Matrix (Fin W) (Fin W) ℂ) :
    IsUnit (transferMat g z V).det :=
  Matrix.isUnit_det_of_right_inverse (transferMat_mul_transferInv g z V)

private lemma lcc_isUnit_transferProd {W : ℕ} (g : ℝ) (z : ℂ) (V : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) : IsUnit (transferProd g z V j).det := by
  induction j with
  | zero => simp [transferProd]
  | succ j ih =>
    rw [transferProd, Matrix.det_mul]
    exact (lcc_isUnit_transferMat g z (V j)).mul ih

private lemma lcc_pairVec_add {W : ℕ} (x y x' y' : Fin W → ℂ) :
    pairVec (x + x') (y + y') = pairVec x y + pairVec x' y' := by
  ext ⟨s, α⟩
  simp only [pairVec, Pi.add_apply]
  split_ifs <;> rfl

private lemma lcc_pairVec_zero_zero {W : ℕ} : pairVec (0 : Fin W → ℂ) 0 = 0 := by
  ext ⟨s, α⟩
  simp only [pairVec, Pi.zero_apply]
  split_ifs <;> rfl

/-- Propagation of the cell recurrence `φ_{j+1} = z φ_j − φ_{j−1} − V_j φ_j / g + r_j` from
`φ_0 = φ_1 = 0`: `‖φ_k‖ ≤ K² Σ_j ‖r_j‖` when `‖F_j‖, ‖F_j⁻¹‖ ≤ K` for `j ≤ n` (proof of (E.11)
[uva:eq:cross-audit]). -/
private lemma lcc_propagate {W : ℕ} (g : ℝ) (z : ℂ) (V : ℕ → Matrix (Fin W) (Fin W) ℂ) {n : ℕ}
    {K : ℝ} (hK : ∀ j ≤ n, ‖transferProd g z V j‖ ≤ K ∧ ‖(transferProd g z V j)⁻¹‖ ≤ K)
    (φ r : ℕ → Fin W → ℂ) (h0 : φ 0 = 0) (h1 : φ 1 = 0)
    (hrec : ∀ j, 1 ≤ j → j + 1 < n →
      φ (j + 1) = z • φ j - φ (j - 1) - ((g : ℂ)⁻¹) • (V j *ᵥ φ j) + r j) :
    ∀ k < n, lccN (φ k) ≤ K ^ 2 * ∑ j ∈ range n, lccN (r j) := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0 (Nat.zero_le _)).1
  have key : ∀ k, 1 ≤ k → k < n →
      (transferProd g z V k)⁻¹ *ᵥ pairVec (φ k) (φ (k - 1)) =
        ∑ j ∈ Finset.Ico 1 k, (transferProd g z V (j + 1))⁻¹ *ᵥ pairVec (r j) 0 := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
      intro _
      simp [h0, h1, lcc_pairVec_zero_zero]
    | succ k hk ih =>
      intro hkn
      have hT := lcc_transferMat_mulVec_pairVec g z (V k) (φ k) (φ (k - 1))
      have hstep : pairVec (φ (k + 1)) (φ k) =
          transferMat g z (V k) *ᵥ pairVec (φ k) (φ (k - 1)) + pairVec (r k) 0 := by
        rw [hT, hrec k hk hkn, ← lcc_pairVec_add, add_zero]
      have hinv : (transferProd g z V (k + 1))⁻¹ * transferMat g z (V k) =
          (transferProd g z V k)⁻¹ := by
        rw [transferProd, Matrix.mul_inv_rev, Matrix.mul_assoc,
          Matrix.nonsing_inv_mul _ (lcc_isUnit_transferMat g z (V k)), Matrix.mul_one]
      rw [Nat.add_sub_cancel, hstep, Matrix.mulVec_add, Matrix.mulVec_mulVec, hinv,
        ih (by omega), Finset.sum_Ico_succ_top hk]
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [h0, lccN_zero]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => lccN_nonneg _)
  · have hΦ : pairVec (φ k) (φ (k - 1)) = transferProd g z V k *ᵥ
        ((transferProd g z V k)⁻¹ *ᵥ pairVec (φ k) (φ (k - 1))) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (lcc_isUnit_transferProd g z V k),
        Matrix.one_mulVec]
    have hsum : lccN (∑ j ∈ Finset.Ico 1 k, (transferProd g z V (j + 1))⁻¹ *ᵥ pairVec (r j) 0) ≤
        K * ∑ j ∈ range n, lccN (r j) := by
      refine le_trans (lccN_sum_le _ _) ?_
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum fun j hj => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (s := Finset.Ico 1 k) (t := range n) ?_ ?_)
      · change lccN ((transferProd g z V (j + 1))⁻¹ *ᵥ pairVec (r j) 0) ≤ K * lccN (r j)
        have hj' := Finset.mem_Ico.mp hj
        refine le_trans (lccN_mulVec _ _) ?_
        rw [lccN_pairVec_zero]
        exact mul_le_mul_of_nonneg_right (hK (j + 1) (by omega)).2 (lccN_nonneg _)
      · intro j hj
        have hj' := Finset.mem_Ico.mp hj
        exact Finset.mem_range.mpr (by omega)
      · intro j _ _
        exact mul_nonneg hK0 (lccN_nonneg _)
    calc lccN (φ k) ≤ lccN (pairVec (φ k) (φ (k - 1))) := lccN_le_pairVec _ _
      _ ≤ ‖transferProd g z V k‖ *
          lccN ((transferProd g z V k)⁻¹ *ᵥ pairVec (φ k) (φ (k - 1))) := by
        conv_lhs => rw [hΦ]
        exact lccN_mulVec _ _
      _ ≤ K * (K * ∑ j ∈ range n, lccN (r j)) := by
        rw [key k hk1 hk]
        exact mul_le_mul (hK k hk.le).1 hsum (lccN_nonneg _) hK0
      _ = K ^ 2 * ∑ j ∈ range n, lccN (r j) := by ring

private lemma lcc_cellBlock_val {L : ℕ} (a : Fin L) (j : ℕ) :
    (cellBlock a j).val = (a.val + j) % L := rfl

private lemma lcc_cellBlock_succ {L : ℕ} (a : Fin L) (k : ℕ) :
    (cellBlock a (k + 1)).val = ((cellBlock a k).val + 1) % L := by
  rw [lcc_cellBlock_val, lcc_cellBlock_val, Nat.mod_add_mod, Nat.add_assoc]

private lemma lcc_cellBlock_injOn {L : ℕ} (a : Fin L) {i j : ℕ} (hi : i < L) (hj : j < L)
    (h : cellBlock a i = cellBlock a j) : i = j := by
  have := cellWindow_injective a (n := L) le_rfl (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) h
  exact congrArg Fin.val this

private lemma lcc_cellBlock_L {L : ℕ} (a : Fin L) : cellBlock a L = cellBlock a 0 := by
  apply Fin.ext
  rw [lcc_cellBlock_val, lcc_cellBlock_val, Nat.add_mod_right, Nat.add_zero]

private lemma lcc_cellBlock_surj {L : ℕ} (a b : Fin L) : ∃ j < L, cellBlock a j = b := by
  by_cases hab : a.val ≤ b.val
  · refine ⟨b.val - a.val, by omega, Fin.ext ?_⟩
    rw [lcc_cellBlock_val, Nat.add_sub_cancel' hab, Nat.mod_eq_of_lt b.isLt]
  · refine ⟨b.val + L - a.val, by omega, Fin.ext ?_⟩
    rw [lcc_cellBlock_val, show a.val + (b.val + L - a.val) = b.val + L by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt]

private lemma lcc_mem_cellCoords {W L : ℕ} (a : Fin L) {n j : ℕ} (hj : j < n) (α : Fin W) :
    (cellBlock a j, α) ∈ cellCoords (W := W) a n := by
  simp only [cellCoords, cellSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_range]
  exact ⟨j, hj, rfl⟩

private lemma lcc_succ_mod_inj {L x y : ℕ} (hx : x < L) (hy : y < L)
    (h : (x + 1) % L = (y + 1) % L) : x = y := by
  have h2 : x ≡ y [MOD L] := Nat.ModEq.add_right_cancel' 1 h
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h2

/-- `(A_L f)(a + k + 1) = f(a + k + 2) + f(a + k)`. -/
private lemma lcc_cycleAdj_sum {L : ℕ} (a : Fin L) (k : ℕ) (f : Fin L → ℂ) :
    ∑ b, cycleAdj L (cellBlock a (k + 1)) b * f b =
      f (cellBlock a (k + 2)) + f (cellBlock a k) := by
  have e1 : ∀ b : Fin L, (if b.val = ((cellBlock a (k + 1)).val + 1) % L then (1 : ℂ) else 0) =
      if b = cellBlock a (k + 2) then 1 else 0 := by
    intro b
    have : ((cellBlock a (k + 1)).val + 1) % L = (cellBlock a (k + 2)).val :=
      (lcc_cellBlock_succ a (k + 1)).symm
    by_cases hb : b = cellBlock a (k + 2)
    · rw [if_pos hb, if_pos (by rw [this, hb])]
    · rw [if_neg hb, if_neg (by rw [this]; exact fun h => hb (Fin.ext h))]
  have e2 : ∀ b : Fin L, (if (cellBlock a (k + 1)).val = (b.val + 1) % L then (1 : ℂ) else 0) =
      if b = cellBlock a k then 1 else 0 := by
    intro b
    by_cases hb : b = cellBlock a k
    · rw [if_pos hb, if_pos (by rw [hb, lcc_cellBlock_succ])]
    · rw [if_neg hb, if_neg]
      intro h
      rw [lcc_cellBlock_succ] at h
      exact hb (Fin.ext (lcc_succ_mod_inj b.isLt (cellBlock a k).isLt h.symm))
  simp only [cycleAdj, Matrix.of_apply, e1, e2, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private lemma lcc_Hdet_mulVec {g : ℝ} {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (x : Fin L × Fin W → ℂ) (b : Fin L) (α : Fin W) :
    (Hdet g V *ᵥ x) (b, α) = ((max 1 g : ℝ)⁻¹ : ℂ) * ((g : ℂ) *
      ∑ k : Fin L, cycleAdj L b k * x (k, α) + (V b *ᵥ fun γ => x (b, γ)) α) := by
  have h1 : ((cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *ᵥ x) (b, α) =
      ∑ k : Fin L, cycleAdj L b k * x (k, α) := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
  have h2 : (blockDiagOp V *ᵥ x) (b, α) = (V b *ᵥ fun γ => x (b, γ)) α := by
    simp [Matrix.mulVec, dotProduct, blockDiagOp, Fintype.sum_prod_type]
  unfold Hdet
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.smul_apply, Pi.add_apply,
    Pi.smul_apply, h1, h2]
  simp

/-- Row `a + k + 1` of the block operator for `g ≥ 1`. -/
private lemma lcc_Hdet_row {g : ℝ} (hg : 1 ≤ g) {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (x : Fin L × Fin W → ℂ) (a : Fin L) (k : ℕ) (α : Fin W) :
    (Hdet g V *ᵥ x) (cellBlock a (k + 1), α) = x (cellBlock a (k + 2), α) +
      x (cellBlock a k, α) +
        (g : ℂ)⁻¹ * (V (cellBlock a (k + 1)) *ᵥ fun β => x (cellBlock a (k + 1), β)) α := by
  rw [lcc_Hdet_mulVec, lcc_cycleAdj_sum a k (fun b => x (b, α)), max_eq_right hg]
  have hg0 : (g : ℂ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by linarith)
  field_simp

private lemma lcc_pathOp_mulVec {g : ℝ} {W m : ℕ} (V : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (x : Fin m × Fin W → ℂ) (i : Fin m) (α : Fin W) :
    (pathOp g V 0 0 *ᵥ x) (i, α) = ((max 1 g : ℝ)⁻¹ : ℂ) * ((g : ℂ) *
      ∑ k : Fin m, pathAdj m i k * x (k, α) + (V i *ᵥ fun γ => x (i, γ)) α) := by
  have h1 : ((pathAdj m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *ᵥ x) (i, α) =
      ∑ k : Fin m, pathAdj m i k * x (k, α) := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
  have h2 : ∀ B : Fin m → Matrix (Fin W) (Fin W) ℂ,
      (blockDiagOp B *ᵥ x) (i, α) = (B i *ᵥ fun γ => x (i, γ)) α := by
    intro B
    simp [Matrix.mulVec, dotProduct, blockDiagOp, Fintype.sum_prod_type]
  unfold pathOp
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.smul_apply, Pi.add_apply, Pi.smul_apply, h1, h2, h2]
  simp

private lemma lcc_pathAdj_sum {m : ℕ} (i : Fin m) (y : ℕ → ℂ) :
    ∑ k : Fin m, pathAdj m i k * y k.val =
      (if 1 ≤ i.val then y (i.val - 1) else 0) + (if i.val + 1 < m then y (i.val + 1) else 0) := by
  have h1 : ∀ k : Fin m, pathAdj m i k * y k.val =
      (if k.val = i.val - 1 ∧ 1 ≤ i.val then y k.val else 0) +
        (if k.val = i.val + 1 then y k.val else 0) := by
    intro k
    simp only [pathAdj, Matrix.of_apply]
    by_cases h2 : k.val = i.val - 1 ∧ 1 ≤ i.val
    · have h3 : k.val ≠ i.val + 1 := by omega
      rw [if_pos (Or.inr (by omega)), if_pos h2, if_neg h3]
      simp
    · by_cases h5 : k.val = i.val + 1
      · rw [if_pos (Or.inl h5.symm), if_neg h2, if_pos h5]
        simp
      · have h6 : ¬ (i.val + 1 = k.val ∨ k.val + 1 = i.val) := by omega
        rw [if_neg h6, if_neg h2, if_neg h5]
        simp
  simp only [h1, Finset.sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun k => if k = i.val - 1 ∧ 1 ≤ i.val then y k else 0) m,
    Fin.sum_univ_eq_sum_range (fun k => if k = i.val + 1 then y k else 0) m,
    Finset.sum_ite_eq' (Finset.range m) (i.val + 1) y]
  congr 1
  · by_cases hi : 1 ≤ i.val
    · simp only [hi, and_true, if_true]
      rw [Finset.sum_ite_eq' (Finset.range m) (i.val - 1) y,
        if_pos (Finset.mem_range.mpr (by omega))]
    · simp [hi]
  · simp only [Finset.mem_range]

/-- With `E ∉ σ(H_{ℤ_L ∖ A})`, a vector vanishing on the cell and solving the exterior rows of
`(H − E)ψ = 0` is zero (proof of (E.11) [uva:eq:cross-audit]). -/
private lemma lcc_ext_zero {g : ℝ} (hg : 1 ≤ g) {W L n : ℕ} (hn : 2 ≤ n) (hnL : n < L)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (a : Fin L) {E : ℝ}
    (hE : (pathOp g (fun j : Fin (L - n) => V (cellBlock a (n + j))) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin (L - n) × Fin W) (Fin (L - n) × Fin W) ℂ)).det ≠ 0)
    (v : Fin L × Fin W → ℂ) (hcell : ∀ j < n, ∀ α, v (cellBlock a j, α) = 0)
    (hrow : ∀ i, n ≤ i → i < L → ∀ α,
      (Hdet g V *ᵥ v) (cellBlock a i, α) = (E : ℂ) * v (cellBlock a i, α)) :
    v = 0 := by
  set x : Fin (L - n) × Fin W → ℂ := fun q => v (cellBlock a (n + q.1.val), q.2) with hx
  have hx0 : (pathOp g (fun j : Fin (L - n) => V (cellBlock a (n + j))) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin (L - n) × Fin W) (Fin (L - n) × Fin W) ℂ)) *ᵥ x = 0 := by
    funext ⟨i, α⟩
    rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
      lcc_pathOp_mulVec, lcc_pathAdj_sum i (fun j => v (cellBlock a (n + j), α))]
    have hr := hrow (n + i.val) (by omega) (by omega) α
    rw [show n + i.val = (n + i.val - 1) + 1 by omega, lcc_Hdet_row hg,
      show n + i.val - 1 + 1 = n + i.val by omega, show n + i.val - 1 + 2 = n + i.val + 1 by omega]
      at hr
    have hlo : (if 1 ≤ i.val then v (cellBlock a (n + (i.val - 1)), α) else 0) =
        v (cellBlock a (n + i.val - 1), α) := by
      by_cases hi : 1 ≤ i.val
      · rw [if_pos hi, show n + (i.val - 1) = n + i.val - 1 by omega]
      · rw [if_neg hi, show n + i.val - 1 = n - 1 by omega, hcell (n - 1) (by omega)]
    have hhi : (if i.val + 1 < L - n then v (cellBlock a (n + (i.val + 1)), α) else 0) =
        v (cellBlock a (n + i.val + 1), α) := by
      by_cases hi : i.val + 1 < L - n
      · rw [if_pos hi, show n + (i.val + 1) = n + i.val + 1 by omega]
      · rw [if_neg hi, show n + i.val + 1 = L by omega, lcc_cellBlock_L, hcell 0 (by omega)]
    rw [hlo, hhi, max_eq_right hg]
    have hg0 : (g : ℂ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by linarith)
    simp only [hx, Pi.zero_apply, smul_eq_mul]
    rw [← hr]
    field_simp
    ring
  have hxz : x = 0 := Matrix.eq_zero_of_mulVec_eq_zero hE hx0
  funext ⟨b, α⟩
  obtain ⟨j, hjL, rfl⟩ := lcc_cellBlock_surj a b
  by_cases hjn : j < n
  · exact hcell j hjn α
  · have := congrFun hxz (⟨j - n, by omega⟩, α)
    simp only [hx, Pi.zero_apply] at this
    rw [show n + (j - n) = j by omega] at this
    exact this

private lemma lcc_coordProj_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι)
    (v : ι → ℂ) (p : ι) : (coordProj T *ᵥ v) p = if p ∈ T then v p else 0 := by
  simp [coordProj, Matrix.mulVec_diagonal]

private lemma lcc_line_mulVec {g : ℝ} {W L n : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (a : Fin L) (s E : ℝ) (v : Fin L × Fin W → ℂ) (p : Fin L × Fin W) :
    ((Hdet g V + (s : ℂ) • coordProj (cellCoords a n) - (E : ℂ) • 1) *ᵥ v) p =
      (Hdet g V *ᵥ v) p + (s : ℂ) * (coordProj (cellCoords a n) *ᵥ v) p - (E : ℂ) * v p := by
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  simp

/-- Kernel vectors of `H + c u P_A − E` and `H + c u' P_A − E`, `u ≠ u'`, have orthogonal
restrictions to the cell (proof of (E.11) [uva:eq:cross-audit]). -/
private lemma lcc_orth {g : ℝ} {W L n : ℕ} {V : Fin L → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ b, (V b).IsHermitian) (a : Fin L) {c E u u' : ℝ} (hc : c ≠ 0) (huu : u ≠ u')
    {v w : Fin L × Fin W → ℂ}
    (hv : (Hdet g V + ((c * u : ℝ) : ℂ) • coordProj (cellCoords a n) - (E : ℂ) • 1) *ᵥ v = 0)
    (hw : (Hdet g V + ((c * u' : ℝ) : ℂ) • coordProj (cellCoords a n) - (E : ℂ) • 1) *ᵥ w = 0) :
    ∑ p, star ((coordProj (cellCoords a n) *ᵥ v) p) * (coordProj (cellCoords a n) *ᵥ w) p = 0 := by
  set P := coordProj (cellCoords (W := W) a n) with hP
  set Q := Hdet g V with hQdef
  have hQ : Q.IsHermitian := Hdet_isHermitian g hV
  have hQv : ∀ p, (Q *ᵥ v) p = (E : ℂ) * v p - ((c * u : ℝ) : ℂ) * (P *ᵥ v) p := by
    intro p
    have := congrFun hv p
    rw [lcc_line_mulVec] at this
    simp only [Pi.zero_apply] at this
    linear_combination this
  have hQw : ∀ p, (Q *ᵥ w) p = (E : ℂ) * w p - ((c * u' : ℝ) : ℂ) * (P *ᵥ w) p := by
    intro p
    have := congrFun hw p
    rw [lcc_line_mulVec] at this
    simp only [Pi.zero_apply] at this
    linear_combination this
  have herm : ∑ p, star (v p) * (Q *ᵥ w) p = ∑ p, star ((Q *ᵥ v) p) * w p := by
    have h := Matrix.dotProduct_mulVec (star v) Q w
    have e : star v ᵥ* Q = star (Q *ᵥ v) := by rw [Matrix.star_mulVec, hQ.eq]
    rw [e] at h
    simpa [dotProduct] using h
  set s := ∑ p, star ((P *ᵥ v) p) * (P *ᵥ w) p with hs
  have h1 : ∀ p, star (v p) * (Q *ᵥ w) p =
      (E : ℂ) * (star (v p) * w p) - ((c * u' : ℝ) : ℂ) * (star ((P *ᵥ v) p) * (P *ᵥ w) p) := by
    intro p
    rw [hQw p, hP, lcc_coordProj_mulVec, lcc_coordProj_mulVec]
    split_ifs <;> simp <;> ring
  have h2 : ∀ p, star ((Q *ᵥ v) p) * w p =
      (E : ℂ) * (star (v p) * w p) - ((c * u : ℝ) : ℂ) * (star ((P *ᵥ v) p) * (P *ᵥ w) p) := by
    intro p
    rw [hQv p, hP, lcc_coordProj_mulVec, lcc_coordProj_mulVec]
    split_ifs <;> simp [Complex.conj_ofReal] <;> ring
  simp only [h1, h2, Finset.sum_sub_distrib, ← Finset.mul_sum] at herm
  have h3 : ((c * (u - u') : ℝ) : ℂ) * s = 0 := by
    push_cast at herm ⊢
    linear_combination herm
  rcases mul_eq_zero.mp h3 with h | h
  · exfalso
    have : c * (u - u') = 0 := by exact_mod_cast h
    rcases mul_eq_zero.mp this with h' | h'
    · exact hc h'
    · exact huu (by linarith)
  · exact h

/-- Pythagoras for a pairwise orthogonal family of coordinate vectors. -/
private lemma lcc_pythag {ι κ : Type*} [Fintype ι] (s : Finset κ) (x : κ → ι → ℂ) (b : κ → ℂ)
    (horth : ∀ u ∈ s, ∀ u' ∈ s, u ≠ u' → ∑ p, star (x u p) * x u' p = 0) :
    ∑ p, ‖∑ u ∈ s, b u * x u p‖ ^ 2 = ∑ u ∈ s, ‖b u‖ ^ 2 * ∑ p, ‖x u p‖ ^ 2 := by
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := fun z => by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow, hn]
  calc ∑ p, star (∑ u ∈ s, b u * x u p) * ∑ u ∈ s, b u * x u p
      = ∑ p, ∑ u ∈ s, ∑ u' ∈ s, (star (b u) * b u') * (star (x u p) * x u' p) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [star_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
        rw [star_mul']
        ring
    _ = ∑ u ∈ s, ∑ u' ∈ s, (star (b u) * b u') * ∑ p, (star (x u p) * x u' p) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ u ∈ s, (star (b u) * b u) * ∑ p, (star (x u p) * x u p) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Finset.sum_eq_single u]
        · intro u' hu' hne
          rw [horth u hu u' hu' (Ne.symm hne), mul_zero]
        · intro h
          exact absurd hu h

private lemma lcc_cellCoords_eq {W L : ℕ} (a : Fin L) {n : ℕ} :
    cellCoords (W := W) a n =
      ((range n) ×ˢ (univ : Finset (Fin W))).image (fun q => (cellBlock a q.1, q.2)) := by
  ext ⟨b, α⟩
  simp only [cellCoords, cellSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_range, Finset.mem_product, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, α, ⟨hj, trivial⟩, rfl, rfl⟩
  · rintro ⟨j, β, ⟨hj, -⟩, rfl, rfl⟩
    exact ⟨j, hj, rfl⟩

/-- `Σ_{p ∈ A} f(p) = Σ_{j < n} Σ_α f(a + j, α)` for a cell of `n ≤ L` blocks. -/
private lemma lcc_cell_sum {W L n : ℕ} (hnL : n ≤ L) (a : Fin L) (f : Fin L × Fin W → ℝ) :
    ∑ p ∈ cellCoords (W := W) a n, f p = ∑ j ∈ range n, ∑ α, f (cellBlock a j, α) := by
  rw [lcc_cellCoords_eq, Finset.sum_image, Finset.sum_product]
  rintro ⟨j, α⟩ hj ⟨j', α'⟩ hj' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hj hj'
  simp only [Prod.mk.injEq] at h
  have := lcc_cellBlock_injOn a (by omega) (by omega) h.1
  simp [this, h.2]

private lemma lcc_coordProj_normSq {W L n : ℕ} (hnL : n ≤ L) (a : Fin L)
    (v : Fin L × Fin W → ℂ) :
    ∑ p, ‖(coordProj (cellCoords a n) *ᵥ v) p‖ ^ 2 =
      ∑ j ∈ range n, ∑ α, ‖v (cellBlock a j, α)‖ ^ 2 := by
  rw [← lcc_cell_sum hnL a (fun p => ‖v p‖ ^ 2)]
  have e : ∀ p, ‖(coordProj (cellCoords (W := W) a n) *ᵥ v) p‖ ^ 2 =
      if p ∈ cellCoords (W := W) a n then ‖v p‖ ^ 2 else 0 := by
    intro p
    rw [lcc_coordProj_mulVec]
    split_ifs <;> simp
  simp only [e]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The window count: for `|u − u₀| ≤ h` on a finite set `F` and `n K_A(E − c u₀)² c h < 1`, the
kernels of `H + c u P_A − E`, `u ∈ F`, have total dimension at most `2W` (proof of (E.11)
[uva:eq:cross-audit]). -/
private lemma lcc_window {g : ℝ} (hg : 1 ≤ g) {W L n : ℕ} (hn : 2 ≤ n) (hnL : n < L)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ b, (V b).IsHermitian) (a : Fin L) {c : ℝ}
    (hc : 0 < c) {E : ℝ}
    (hE : (pathOp g (fun j : Fin (L - n) => V (cellBlock a (n + j))) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin (L - n) × Fin W) (Fin (L - n) × Fin W) ℂ)).det ≠ 0)
    (F : Finset ℝ) {u₀ h : ℝ} (h0 : 0 ≤ h) (hF : ∀ u ∈ F, |u - u₀| ≤ h)
    (hq : n * transferWeight g (E - c * u₀) (fun j => V (cellBlock a j)) n ^ 2 * c * h < 1) :
    ∑ u ∈ F, Module.finrank ℂ (LinearMap.ker (Matrix.toLin'
      (Hdet g V + ((c * u : ℝ) : ℂ) • coordProj (cellCoords a n) - (E : ℂ) • 1))) ≤ 2 * W := by
  set P := coordProj (cellCoords (W := W) a n) with hP
  set S : ℝ → Submodule ℂ (Fin L × Fin W → ℂ) := fun u =>
    LinearMap.ker (Matrix.toLin' (Hdet g V + ((c * u : ℝ) : ℂ) • P - (E : ℂ) • 1)) with hS
  let ev : (Fin L × Fin W → ℂ) →ₗ[ℂ] (Fin 2 × Fin W → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun q : Fin 2 × Fin W => (cellBlock a q.1.val, q.2))
  let Θ : (∀ u : F, S u) →ₗ[ℂ] (Fin 2 × Fin W → ℂ) :=
    ∑ u : F, ev ∘ₗ (S u).subtype ∘ₗ LinearMap.proj u
  have hΘ : ∀ ψ q, Θ ψ q = ∑ u : F, (ψ u : Fin L × Fin W → ℂ) (cellBlock a q.1.val, q.2) := by
    intro ψ q
    simp [Θ, ev, LinearMap.funLeft_apply]
  have hinj : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ψ hψ
    set v : F → Fin L × Fin W → ℂ := fun u => (ψ u : Fin L × Fin W → ℂ) with hvdef
    have hv : ∀ u : F, (Hdet g V + ((c * u : ℝ) : ℂ) • P - (E : ℂ) • 1) *ᵥ v u = 0 := by
      intro u
      have := (ψ u).2
      simp only [hS, LinearMap.mem_ker, Matrix.toLin'_apply] at this
      exact this
    have hrow : ∀ u : F, ∀ p, (Hdet g V *ᵥ v u) p =
        (E : ℂ) * v u p - ((c * u : ℝ) : ℂ) * (P *ᵥ v u) p := by
      intro u p
      have := congrFun (hv u) p
      rw [hP, lcc_line_mulVec] at this
      simp only [Pi.zero_apply] at this
      rw [hP]
      linear_combination this
    -- the cell values of `Ψ = Σ_u v_u` and the residual `R = Σ_u c (u₀ − u) P v_u`
    set x : F → Fin L × Fin W → ℂ := fun u => P *ᵥ v u with hxdef
    set φ : ℕ → Fin W → ℂ := fun j α => ∑ u : F, v u (cellBlock a j, α) with hφ
    set R : Fin L × Fin W → ℂ := fun p => ∑ u : F, ((c * (u₀ - u) : ℝ) : ℂ) * x u p with hR
    set r : ℕ → Fin W → ℂ := fun j α => R (cellBlock a j, α) with hr
    have hxcell : ∀ u : F, ∀ j < n, ∀ α, x u (cellBlock a j, α) = v u (cellBlock a j, α) := by
      intro u j hj α
      simp only [hxdef, hP, lcc_coordProj_mulVec, if_pos (lcc_mem_cellCoords a hj α)]
    have hφ0 : φ 0 = 0 := by
      funext α
      have := hΘ ψ (0, α)
      rw [hψ] at this
      simpa [hφ] using this.symm
    have hφ1 : φ 1 = 0 := by
      funext α
      have := hΘ ψ (1, α)
      rw [hψ] at this
      simpa [hφ] using this.symm
    -- interior rows: the cell recurrence at energy `E − c u₀`
    have hz : ((max 1 g * (E - c * u₀) / g : ℝ) : ℂ) = ((E - c * u₀ : ℝ) : ℂ) := by
      rw [max_eq_right hg]
      congr 1
      field_simp
    have hrec : ∀ j, 1 ≤ j → j + 1 < n →
        φ (j + 1) = ((max 1 g * (E - c * u₀) / g : ℝ) : ℂ) • φ j - φ (j - 1) -
          ((g : ℂ)⁻¹) • ((fun j => V (cellBlock a j)) j *ᵥ φ j) + r j := by
      intro j hj1 hjn
      funext α
      have hH := lcc_Hdet_row hg V (∑ u : F, v u) a (j - 1) α
      rw [show j - 1 + 1 = j by omega, show j - 1 + 2 = j + 1 by omega] at hH
      have hsum : (Hdet g V *ᵥ ∑ u : F, v u) (cellBlock a j, α) =
          ((E - c * u₀ : ℝ) : ℂ) * φ j α + r j α := by
        rw [Matrix.mulVec_sum, Finset.sum_apply]
        simp only [hrow, hφ, hr, hR, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        have hx' : (P *ᵥ v u) (cellBlock a j, α) = v u (cellBlock a j, α) :=
          hxcell u j (by omega) α
        simp only [hx', hxcell u j (by omega) α]
        push_cast
        ring
      have hfun : ∀ k, (fun β => (∑ u : F, v u) (cellBlock a k, β)) = φ k := by
        intro k
        funext β
        simp [hφ, Finset.sum_apply]
      rw [hfun, hsum] at hH
      simp only [Finset.sum_apply] at hH
      rw [hz]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have e1 : (∑ u : F, v u (cellBlock a (j + 1), α)) = φ (j + 1) α := rfl
      have e2 : (∑ u : F, v u (cellBlock a (j - 1), α)) = φ (j - 1) α := rfl
      rw [e1, e2] at hH
      linear_combination -hH
    set K := transferWeight g (E - c * u₀) (fun j => V (cellBlock a j)) n with hK
    have hKb := transferWeight_bounds g (E - c * u₀) (fun j => V (cellBlock a j)) n
    have hprop := lcc_propagate g _ (fun j => V (cellBlock a j)) (n := n) (K := K) hKb.2 φ r
      hφ0 hφ1 hrec
    have hK1 : 1 ≤ K := hKb.1
    -- the norms
    set B := ∑ j ∈ range n, lccN (r j) ^ 2 with hB
    set A := ∑ j ∈ range n, lccN (φ j) ^ 2 with hA
    set M := ∑ u : F, ∑ p, ‖x u p‖ ^ 2 with hM
    have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hM0 : 0 ≤ M := Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun p _ => sq_nonneg _
    have hAB : A ≤ (n : ℝ) ^ 2 * K ^ 4 * B := by
      have hS0 : 0 ≤ ∑ j ∈ range n, lccN (r j) := Finset.sum_nonneg fun j _ => lccN_nonneg _
      have hCS := sq_sum_le_card_mul_sum_sq (s := range n) (f := fun j => lccN (r j))
      rw [Finset.card_range] at hCS
      calc A ≤ ∑ j ∈ range n, (K ^ 2 * ∑ j ∈ range n, lccN (r j)) ^ 2 := by
            refine Finset.sum_le_sum fun j hj => ?_
            exact pow_le_pow_left₀ (lccN_nonneg _) (hprop j (Finset.mem_range.mp hj)) 2
        _ = n * K ^ 4 * (∑ j ∈ range n, lccN (r j)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
        _ ≤ n * K ^ 4 * (n * B) := by
            refine mul_le_mul_of_nonneg_left hCS (by positivity)
        _ = (n : ℝ) ^ 2 * K ^ 4 * B := by ring
    have horth : ∀ u ∈ (univ : Finset F), ∀ u' ∈ (univ : Finset F), u ≠ u' →
        ∑ p, star (x u p) * x u' p = 0 := by
      intro u _ u' _ hne
      exact lcc_orth hV a hc.ne' (fun h => hne (Subtype.ext h)) (hv u) (hv u')
    have hBM : B ≤ (c * h) ^ 2 * M := by
      have h1 : B = ∑ p ∈ cellCoords (W := W) a n, ‖R p‖ ^ 2 := by
        rw [lcc_cell_sum hnL.le a (fun p => ‖R p‖ ^ 2), hB]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lccN_sq]
      have h2 : ∑ p ∈ cellCoords (W := W) a n, ‖R p‖ ^ 2 ≤ ∑ p, ‖R p‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => sq_nonneg _
      have h3 : ∑ p, ‖R p‖ ^ 2 =
          ∑ u : F, ‖((c * (u₀ - u) : ℝ) : ℂ)‖ ^ 2 * ∑ p, ‖x u p‖ ^ 2 :=
        lcc_pythag univ x (fun u => ((c * (u₀ - u) : ℝ) : ℂ)) horth
      have h4 : ∑ u : F, ‖((c * (u₀ - u) : ℝ) : ℂ)‖ ^ 2 * ∑ p, ‖x u p‖ ^ 2 ≤ (c * h) ^ 2 * M := by
        rw [hM, Finset.mul_sum]
        refine Finset.sum_le_sum fun u _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun p _ => sq_nonneg _)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hc, abs_sub_comm]
        exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hF u u.2) hc.le) 2
      linarith
    have hMA : M = A := by
      have h1 := lcc_pythag univ x (fun _ => (1 : ℂ)) horth
      simp only [one_mul, norm_one, one_pow] at h1
      rw [hM, ← h1]
      have h2 : ∀ p, ∑ u : F, x u p = (P *ᵥ ∑ u : F, v u) p := by
        intro p
        rw [Matrix.mulVec_sum, Finset.sum_apply]
      simp only [h2]
      rw [hP, lcc_coordProj_normSq hnL.le a, hA]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [lccN_sq]
      simp [hφ, Finset.sum_apply]
    -- `M ≤ q² M` with `q < 1`
    have hMz : M = 0 := by
      have hq0 : 0 ≤ (n : ℝ) * K ^ 2 * c * h := by positivity
      have hq' : (n : ℝ) * K ^ 2 * c * h < 1 := hq
      have hle : M ≤ ((n : ℝ) * K ^ 2 * c * h) ^ 2 * M := by
        calc M = A := hMA
          _ ≤ (n : ℝ) ^ 2 * K ^ 4 * B := hAB
          _ ≤ (n : ℝ) ^ 2 * K ^ 4 * ((c * h) ^ 2 * M) :=
            mul_le_mul_of_nonneg_left hBM (by positivity)
          _ = ((n : ℝ) * K ^ 2 * c * h) ^ 2 * M := by ring
      have hq2 : ((n : ℝ) * K ^ 2 * c * h) ^ 2 < 1 := by nlinarith
      nlinarith
    have hx0 : ∀ u : F, x u = 0 := by
      intro u
      have h1 : ∑ p, ‖x u p‖ ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => Finset.sum_nonneg fun p _ => sq_nonneg _)).mp
          hMz u (Finset.mem_univ _)
      funext p
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => sq_nonneg ‖x u p‖)).mp h1 p
        (Finset.mem_univ _)
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    have hv0 : ∀ u : F, v u = 0 := by
      intro u
      refine lcc_ext_zero hg hn hnL V a hE (v u) ?_ ?_
      · intro j hj α
        rw [← hxcell u j hj α, hx0 u]
        rfl
      · intro i _ _ α
        rw [hrow u]
        have : (P *ᵥ v u) = 0 := hx0 u
        rw [this]
        simp
    funext u
    exact Subtype.ext (hv0 u)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin] at hle
  rw [← Finset.sum_coe_sort F]
  exact hle

/-- (E.11) [uva:eq:cross-audit]: `N_{[ℓ,ℓ+1]}(E) ≤ 2W + 2 c n W sup_{u ∈ [ℓ,ℓ+1]} K_A(E − c u)²` for
`H(u) = (g A_L ⊗ I + diag V)/g + c u P_A`, `g ≥ 1`, `2 ≤ n < L`, `E ∉ σ(H_{ℤ_L ∖ A})`. -/
theorem cell_crossCount_le {g : ℝ} (hg : 1 ≤ g) {W L n : ℕ} (hn : 2 ≤ n) (hnL : n < L)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ b, (V b).IsHermitian) (a : Fin L) {c : ℝ}
    (hc : 0 < c) {E : ℝ}
    (hE : (pathOp g (fun j : Fin (L - n) => V (cellBlock a (n + j))) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin (L - n) × Fin W) (Fin (L - n) × Fin W) ℂ)).det ≠ 0) (ℓ : ℤ) :
    crossCount (fun u => Hdet g V + ((c * u : ℝ) : ℂ) • coordProj (cellCoords a n)) E
        (Set.Icc (ℓ : ℝ) (ℓ + 1)) ≤
      ENNReal.ofReal (2 * W) + ENNReal.ofReal (2 * c * n * W) *
        (⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1),
          ENNReal.ofReal (transferWeight g (E - c * u) (fun j => V (cellBlock a j)) n ^ 2)) := by
  set Ssup := ⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1),
    ENNReal.ofReal (transferWeight g (E - c * u) (fun j => V (cellBlock a j)) n ^ 2) with hSsup
  set d : ℝ → ℕ := fun u => Module.finrank ℂ (LinearMap.ker (Matrix.toLin'
    (Hdet g V + ((c * u : ℝ) : ℂ) • coordProj (cellCoords a n) - (E : ℂ) • 1))) with hd
  have hcc : crossCount (fun u => Hdet g V + ((c * u : ℝ) : ℂ) • coordProj (cellCoords a n)) E
      (Set.Icc (ℓ : ℝ) (ℓ + 1)) = ∑' u : Set.Icc (ℓ : ℝ) (ℓ + 1), (d u : ℝ≥0∞) := rfl
  rw [hcc]
  rcases Nat.eq_zero_or_pos W with hW | hWpos
  · -- `W = 0`: every kernel is zero
    subst hW
    have hd0 : ∀ u, d u = 0 := by
      intro u
      have h1 := Submodule.finrank_le (LinearMap.ker (Matrix.toLin'
        (Hdet g V + ((c * u : ℝ) : ℂ) • coordProj (cellCoords a n) - (E : ℂ) • 1)))
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin, mul_zero] at h1
      exact Nat.le_zero.mp h1
    simp [hd0]
  by_cases htop : Ssup = ⊤
  · have h2 : ENNReal.ofReal (2 * c * n * W) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have : (0 : ℝ) < W := by exact_mod_cast hWpos
      positivity
    rw [htop, ENNReal.mul_top h2, add_top]
    exact le_top
  set K2 := Ssup.toReal with hK2def
  have hK2 : 0 ≤ K2 := ENNReal.toReal_nonneg
  have hncK : 0 ≤ (n : ℝ) * c * K2 := by positivity
  set m : ℕ := ⌊(n : ℝ) * c * K2⌋₊ + 1 with hmdef
  have hm : (n : ℝ) * c * K2 < m := by
    rw [hmdef]
    push_cast
    exact Nat.lt_floor_add_one _
  have hm' : (m : ℝ) ≤ n * c * K2 + 1 := by
    rw [hmdef]
    push_cast
    linarith [Nat.floor_le hncK]
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  -- the pieces `[ℓ + i/m, ℓ + (i+1)/m]`
  set idx : Set.Icc (ℓ : ℝ) (ℓ + 1) → ℕ := fun u => min ⌊(u.val - ℓ) * m⌋₊ (m - 1) with hidx
  have hpiece : ∀ u : Set.Icc (ℓ : ℝ) (ℓ + 1),
      (idx u : ℝ) ≤ (u.val - ℓ) * m ∧ (u.val - ℓ) * m ≤ idx u + 1 := by
    intro u
    have hu := u.2
    have ht0 : 0 ≤ (u.val - ℓ) * m := mul_nonneg (by linarith [hu.1]) hmR.le
    have htm : (u.val - ℓ) * m ≤ m := by
      have : u.val - ℓ ≤ 1 := by linarith [hu.2]
      nlinarith
    constructor
    · calc (idx u : ℝ) ≤ (⌊(u.val - ℓ) * m⌋₊ : ℝ) := by
            exact_mod_cast min_le_left _ _
        _ ≤ (u.val - ℓ) * m := Nat.floor_le ht0
    · by_cases hfl : ⌊(u.val - ℓ) * m⌋₊ ≤ m - 1
      · have : idx u = ⌊(u.val - ℓ) * m⌋₊ := min_eq_left hfl
        rw [this]
        exact (Nat.lt_floor_add_one _).le
      · have : idx u = m - 1 := min_eq_right (by omega)
        rw [this, Nat.cast_sub (by omega), Nat.cast_one]
        linarith
  have hidx_lt : ∀ u, idx u < m := fun u => lt_of_le_of_lt (min_le_right _ _) (by omega)
  have hpiece_count : ∀ (s : Finset (Set.Icc (ℓ : ℝ) (ℓ + 1))) (i : ℕ), i < m →
      ∑ u ∈ s.filter (fun u => idx u = i), d u ≤ 2 * W := by
    intro s i hi
    set u₀ : ℝ := ℓ + i / m with hu₀
    have hu₀mem : u₀ ∈ Set.Icc (ℓ : ℝ) (ℓ + 1) := by
      have h1 : (0 : ℝ) ≤ i / m := by positivity
      have h2 : (i : ℝ) / m ≤ 1 := by
        rw [div_le_one hmR]
        exact_mod_cast hi.le
      exact ⟨by linarith, by linarith⟩
    have hKu₀ : transferWeight g (E - c * u₀) (fun j => V (cellBlock a j)) n ^ 2 ≤ K2 := by
      have h1 : ENNReal.ofReal (transferWeight g (E - c * u₀) (fun j => V (cellBlock a j)) n ^ 2)
          ≤ Ssup :=
        le_iSup₂_of_le (f := fun u (_ : u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1)) =>
          ENNReal.ofReal (transferWeight g (E - c * u) (fun j => V (cellBlock a j)) n ^ 2))
          u₀ hu₀mem le_rfl
      exact (ENNReal.ofReal_le_iff_le_toReal htop).mp h1
    have hq : n * transferWeight g (E - c * u₀) (fun j => V (cellBlock a j)) n ^ 2 * c *
        (1 / m) < 1 := by
      have h1 : (n : ℝ) * transferWeight g (E - c * u₀) (fun j => V (cellBlock a j)) n ^ 2 * c ≤
          n * c * K2 := by
        have : (0 : ℝ) ≤ n * c := by positivity
        nlinarith
      rw [mul_one_div, div_lt_one hmR]
      linarith
    have hF : ∀ x ∈ (s.filter (fun u => idx u = i)).map (Function.Embedding.subtype _),
        |x - u₀| ≤ 1 / m := by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      have hui : idx u = i := (Finset.mem_filter.mp hu).2
      obtain ⟨h1, h2⟩ := hpiece u
      rw [hui] at h1 h2
      have e : (u : ℝ) - u₀ = ((u.val - ℓ) * m - i) / m := by
        rw [hu₀]
        field_simp
        ring
      simp only [Function.Embedding.coe_subtype]
      rw [e, abs_le]
      constructor
      · rw [le_div_iff₀ hmR]
        have : -(1 / (m : ℝ)) * m = -1 := by field_simp
        linarith
      · rw [div_le_div_iff_of_pos_right hmR]
        linarith
    have hw := lcc_window hg hn hnL V hV a hc hE
      ((s.filter (fun u => idx u = i)).map (Function.Embedding.subtype _))
      (u₀ := u₀) (h := 1 / m) (by positivity) hF hq
    rw [Finset.sum_map] at hw
    exact hw
  have hcount : ∀ s : Finset (Set.Icc (ℓ : ℝ) (ℓ + 1)), ∑ u ∈ s, d u ≤ 2 * W * m := by
    intro s
    rw [← Finset.sum_fiberwise_of_maps_to (g := idx) (t := range m)
      (fun u _ => Finset.mem_range.mpr (hidx_lt u))]
    calc ∑ i ∈ range m, ∑ u ∈ s with idx u = i, d u ≤ ∑ i ∈ range m, 2 * W :=
          Finset.sum_le_sum fun i hi => hpiece_count s i (Finset.mem_range.mp hi)
      _ = 2 * W * m := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
  calc ∑' u : Set.Icc (ℓ : ℝ) (ℓ + 1), (d u : ℝ≥0∞) ≤ ((2 * W * m : ℕ) : ℝ≥0∞) := by
        rw [ENNReal.tsum_eq_iSup_sum]
        refine iSup_le fun s => ?_
        rw [← Nat.cast_sum]
        exact_mod_cast hcount s
    _ = ENNReal.ofReal (2 * W * m) := by
        rw [← ENNReal.ofReal_natCast]
        push_cast
        rfl
    _ ≤ ENNReal.ofReal (2 * W + 2 * c * n * W * K2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
        nlinarith
    _ = ENNReal.ofReal (2 * W) + ENNReal.ofReal (2 * c * n * W) * Ssup := by
        have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
        rw [← ENNReal.ofReal_toReal htop, ← hK2def, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

end LSBA
