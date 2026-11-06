import LSBA.Sampling.Lemma48

/-!
# Centered traces, entries and residuals

The interpolation of the Dyson matrix along a cell (from Lemma 6.5 [da:lem:free-interpolation]),
the residual of (5.28) [gc:eq:residual-input] as an explicit combination of block traces, its
deterministic interpolation through anchor pairs (Proposition 7.10
[uvc:prop:residual-compression]), the sampling of centered block traces, traceless entries and
residuals at anchor pairs, and the sampling input of Lemma 5.10(b) [fo:lem:sampling-continuity]
at large coupling.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The first-coordinate free interpolation of a matrix on the cells, with error `δ`: the form of
Lemma 6.5 [da:lem:free-interpolation]. -/
def RowInterp (n : ℕ) (E : ℝ) {L : ℕ} (M : Matrix (Fin L) (Fin L) ℂ) (δ : ℝ) : Prop :=
  ∀ a b : Fin L, ‖M a b - (∑ α : Fin L, (cellCoef n E a α : ℂ) * M α b + (cellSrc n E a b : ℂ))‖ ≤ δ

/-- The combination `-⟨G - M⟩_{ab} + β Σ_c M_{ac} ⟨G - M⟩_{cc} ⟨G⟩_{cb}`, which is the averaged
residual by the identity of Proposition 7.10 [uvc:prop:residual-compression]. -/
def resComb {W L : ℕ} (β : ℝ) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (M : Matrix (Fin L) (Fin L) ℂ) (a b : Fin L) : ℂ :=
  -(blockTr G a b - M a b) + (β : ℂ) * ∑ c : Fin L, M a c * (blockTr G c c - M c c) * blockTr G c b

private theorem residualT_rot_val {L : ℕ} (r : Fin L) : (finRotate L r).val = (r.val + 1) % L := by
  cases L with
  | zero => exact r.elim0
  | succ L =>
    rw [coe_finRotate]
    split_ifs with h
    · subst h; simp
    · have := Fin.val_lt_last h
      rw [Nat.mod_eq_of_lt (by omega)]

private theorem residualT_rotPow_val {L : ℕ} (r : Fin L) (m : ℕ) :
    ((finRotate L ^ m) r).val = (r.val + m) % L := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt r.isLt]
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, residualT_rot_val, ih, Nat.mod_add_mod, add_assoc]

private theorem residualT_sum_cycleAdj {L W : ℕ} (r : Fin L)
    (f : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    ∑ c, cycleAdj L r c • f c = f (finRotate L r) + f ((finRotate L).symm r) := by
  have h1 : ∀ c : Fin L, (c.val = (r.val + 1) % L) ↔ c = finRotate L r := by
    intro c; rw [Fin.ext_iff, residualT_rot_val]
  have h2 : ∀ c : Fin L, (r.val = (c.val + 1) % L) ↔ c = (finRotate L).symm r := by
    intro c; rw [Equiv.eq_symm_apply, Fin.ext_iff, residualT_rot_val, eq_comm]
  simp only [cycleAdj, Matrix.of_apply, add_smul, Finset.sum_add_distrib, h1, h2, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem residualT_blockOf_mul {W L : ℕ} (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockOf (X * Y) a b = ∑ c, blockOf X a c * blockOf Y c b := by
  ext α β
  simp [blockOf, Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]


private theorem residualT_blockOf_op {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (z : ℂ)
    (r c : Fin L) :
    blockOf (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
        z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) r c =
      cycleAdj L r c • (1 : Matrix (Fin W) (Fin W) ℂ) +
        if r = c then V r - z • (1 : Matrix (Fin W) (Fin W) ℂ) else 0 := by
  ext α β
  by_cases h : r = c
  · subst h
    simp [blockOf, blockDiagOp, Matrix.one_apply, Matrix.kroneckerMap_apply]
    split_ifs <;> ring
  · simp [blockOf, blockDiagOp, Matrix.one_apply, Matrix.kroneckerMap_apply, h]

private theorem residualT_op_isHermitian {W L : ℕ} {V : Fin L → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ r, (V r).IsHermitian) :
    (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V).IsHermitian := by
  refine Matrix.IsHermitian.add ?_ (blockDiagOp_isHermitian hV)
  rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, (cycleAdj_isHermitian L).eq,
    Matrix.conjTranspose_one]

/-- The forced recurrence of the Green column (Section 7.3.1 [sec:green-interpolation-proof]):
`G_{r+1,b} = (z - V_r) G_{r,b} - G_{r-1,b} + δ_{rb}`. -/
private theorem residualT_green_rec {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (z : ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hG : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
        z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * G = 1) (r b : Fin L) :
    blockOf G (finRotate L r) b =
      (z • (1 : Matrix (Fin W) (Fin W) ℂ) - V r) * blockOf G r b -
        blockOf G ((finRotate L).symm r) b + if r = b then 1 else 0 := by
  have h2 := congrArg (fun X => blockOf X r b) hG
  simp only [residualT_blockOf_mul, residualT_blockOf_op] at h2
  simp only [add_mul, Finset.sum_add_distrib, smul_mul_assoc, one_mul, residualT_sum_cycleAdj,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h2
  have h1 : blockOf (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) r b =
      if r = b then 1 else 0 := by
    ext α β
    by_cases hrb : r = b
    · subst hrb; simp [blockOf, Matrix.one_apply]
    · simp [blockOf, hrb]
  rw [h1] at h2
  rw [← h2]
  simp only [sub_mul]
  abel

/-- The stacked Green column `(G_{r,b}; G_{r-1,b})`. -/
private def residualTCol {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (r b : Fin L) :
    Matrix (Fin W ⊕ Fin W) (Fin W) ℂ :=
  Matrix.fromRows (blockOf G r b) (blockOf G ((finRotate L).symm r) b)

private theorem residualT_col_succ {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (z : ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hG : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
        z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * G = 1) (r b : Fin L) :
    residualTCol G (finRotate L r) b = blockT z (V r) * residualTCol G r b +
      if r = b then Matrix.fromRows (1 : Matrix (Fin W) (Fin W) ℂ) 0 else 0 := by
  have h := residualT_green_rec V z G hG r b
  simp only [residualTCol, blockT, Matrix.fromBlocks_mul_fromRows, Equiv.symm_apply_apply]
  rw [h]
  split_ifs <;> ext (i | i) j <;> simp [sub_eq_add_neg]

private theorem residualT_col_iter {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (z : ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hG : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
        z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * G = 1) (s b : Fin L) (m : ℕ)
    (hm : s.val + m < L) :
    residualTCol G ((finRotate L ^ m) s) b = cellProd z V s m * residualTCol G s b +
      if s.val ≤ b.val ∧ b.val < s.val + m then
        cellProd z V (finRotate L b) (s.val + m - b.val - 1) *
          Matrix.fromRows (1 : Matrix (Fin W) (Fin W) ℂ) 0 else 0 := by
  induction m with
  | zero => simp [cellProd]
  | succ m ih =>
    have ih := ih (by omega)
    have hpos : ((finRotate L ^ m) s).val = s.val + m := by
      rw [residualT_rotPow_val, Nat.mod_eq_of_lt (by omega)]
    rw [pow_succ', Equiv.Perm.mul_apply, residualT_col_succ V z G hG, ih]
    by_cases h1 : s.val ≤ b.val ∧ b.val < s.val + m
    · have hne : (finRotate L ^ m) s ≠ b := by
        intro h; rw [← h, hpos] at h1; omega
      have hb : b.val + 1 < L := by omega
      have hrot : (finRotate L ^ (s.val + m - b.val - 1)) (finRotate L b) =
          (finRotate L ^ m) s := by
        apply Fin.ext
        rw [residualT_rotPow_val, residualT_rotPow_val, residualT_rot_val, Nat.mod_eq_of_lt hb]
        congr 1; omega
      have h1' : s.val ≤ b.val ∧ b.val < s.val + (m + 1) := by omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false hne),
        ite_eq_left_of_eq_true _ _ (eq_true h1'),
        show s.val + (m + 1) - b.val - 1 = (s.val + m - b.val - 1) + 1 by omega]
      simp only [cellProd, hrot, Matrix.mul_add, Matrix.mul_assoc, add_zero]
      congr 1
      exact (Matrix.mul_assoc _ _ _).symm
    · by_cases h2 : b.val = s.val + m
      · have heq : (finRotate L ^ m) s = b := Fin.ext (by rw [hpos, h2])
        have h1' : s.val ≤ b.val ∧ b.val < s.val + (m + 1) := by omega
        rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true heq),
          ite_eq_left_of_eq_true _ _ (eq_true h1'), show s.val + (m + 1) - b.val - 1 = 0 by omega]
        simp only [cellProd, Matrix.mul_assoc, add_zero, heq]
        congr 1
        exact (Matrix.one_mul _).symm
      · have hne : (finRotate L ^ m) s ≠ b := by
          intro h; rw [← h, hpos] at h2; exact h2 rfl
        have h1' : ¬ (s.val ≤ b.val ∧ b.val < s.val + (m + 1)) := by omega
        rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false hne),
          ite_eq_right_of_eq_false _ _ (eq_false h1')]
        simp only [cellProd, Matrix.mul_assoc, add_zero]

/-- `U(m) = sin(mϑ)/sin ϑ` with `2 cos ϑ = E`. -/
private def residualTU (E : ℝ) (m : ℕ) : ℝ :=
  Real.sin (m * Real.arccos (E / 2)) / Real.sin (Real.arccos (E / 2))

private theorem residualT_sin_pos {E : ℝ} (hE : |E| < 2) : 0 < Real.sin (Real.arccos (E / 2)) := by
  rw [Real.sin_arccos]
  apply Real.sqrt_pos.mpr
  have : |E / 2| < 1 := by rw [abs_div]; norm_num; linarith
  have h2 : (E / 2) ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (E / 2)]
  linarith

private theorem residualTU_zero (E : ℝ) : residualTU E 0 = 0 := by simp [residualTU]

private theorem residualTU_one {E : ℝ} (hE : |E| < 2) : residualTU E 1 = 1 := by
  simp only [residualTU, Nat.cast_one, one_mul]
  exact div_self (residualT_sin_pos hE).ne'

private theorem residualTU_rec {E : ℝ} (hE : |E| < 2) (m : ℕ) :
    residualTU E (m + 2) = E * residualTU E (m + 1) - residualTU E m := by
  have hc : Real.cos (Real.arccos (E / 2)) = E / 2 := by
    apply Real.cos_arccos <;> [skip; skip] <;> (rw [abs_lt] at hE; linarith)
  set t := Real.arccos (E / 2)
  simp only [residualTU]
  have h1 : Real.sin (((m + 2 : ℕ) : ℝ) * t) = Real.sin (((m + 1 : ℕ) : ℝ) * t + t) := by
    congr 1; push_cast; ring
  have h2 : Real.sin ((m : ℝ) * t) = Real.sin (((m + 1 : ℕ) : ℝ) * t - t) := by
    congr 1; push_cast; ring
  rw [h1, h2, Real.sin_add, Real.sin_sub, hc]
  field_simp
  ring

/-- The free powers `T(E)^m = [[U_{m+1}, -U_m], [U_m, U_{m+1} - E U_m]] ⊗ I`, whose entries are
the coefficients (6.16) [da:eq:cell-interpolation-coefficients]. -/
private theorem residualT_free_pow {W : ℕ} {E : ℝ} (hE : |E| < 2) (m : ℕ) :
    blockT (E : ℂ) (0 : Matrix (Fin W) (Fin W) ℂ) ^ m =
      Matrix.fromBlocks ((residualTU E (m + 1) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ))
        ((-residualTU E m : ℂ) • 1) ((residualTU E m : ℂ) • 1)
        (((residualTU E (m + 1) - E * residualTU E m : ℝ) : ℂ) • 1) := by
  induction m with
  | zero =>
    simp [residualTU_zero, residualTU_one hE, Matrix.fromBlocks_one]
  | succ m ih =>
    rw [pow_succ', ih, blockT, Matrix.fromBlocks_multiply]
    have hr := residualTU_rec hE m
    congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> simp [hr] <;> ring

private theorem residualT_start_add {n L : ℕ} (a : Fin L) :
    (cellStart n a).val + a.val % n = a.val := Nat.div_add_mod' a.val n

private theorem residualT_prev_ne {n L : ℕ} (hL : 2 ≤ L) (a : Fin L) :
    cellPrev n a ≠ cellStart n a := by
  intro h
  have h2 : finRotate L (cellPrev n a) = cellPrev n a := by
    simp only [cellPrev, Equiv.apply_symm_apply]
    exact h.symm
  have h3 := congrArg Fin.val h2
  rw [residualT_rot_val] at h3
  have hlt := (cellPrev n a).isLt
  by_cases hc : (cellPrev n a).val + 1 < L
  · rw [Nat.mod_eq_of_lt hc] at h3; omega
  · rw [show (cellPrev n a).val + 1 = L by omega, Nat.mod_self] at h3; omega

/-- The source condition `b` precedes `a` in the cell of `a`, in positions. -/
private theorem residualT_src_iff {n L : ℕ} (hn : 1 ≤ n) (a b : Fin L) :
    (cellStart n b = cellStart n a ∧ b.val % n < a.val % n) ↔
      ((cellStart n a).val ≤ b.val ∧ b.val < (cellStart n a).val + a.val % n) := by
  have ha := residualT_start_add (n := n) a
  have hb := residualT_start_add (n := n) b
  have hsa : (cellStart n a).val = a.val / n * n := rfl
  have hsb : (cellStart n b).val = b.val / n * n := rfl
  constructor
  · rintro ⟨h1, h2⟩
    have := congrArg Fin.val h1
    omega
  · rintro ⟨h1, h2⟩
    have hq : b.val / n = a.val / n := by
      apply Nat.div_eq_of_lt_le
      · rw [hsa] at h1; linarith
      · have := Nat.mod_lt a.val (by omega : 0 < n)
        rw [hsa] at h2; rw [Nat.succ_mul]; omega
    have hs : cellStart n b = cellStart n a := Fin.ext (by rw [hsa, hsb, hq])
    refine ⟨hs, ?_⟩
    rw [hs] at hb
    omega

private theorem residualT_toRows₁_add {W : ℕ} (X Y : Matrix (Fin W ⊕ Fin W) (Fin W) ℂ) :
    (X + Y).toRows₁ = X.toRows₁ + Y.toRows₁ := by
  ext i k; rfl

private theorem residualT_toRows₁_mul {W : ℕ} (P : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (A B : Matrix (Fin W) (Fin W) ℂ) :
    (P * Matrix.fromRows A B).toRows₁ = P.toBlocks₁₁ * A + P.toBlocks₁₂ * B := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks P]
  rw [Matrix.fromBlocks_mul_fromRows, Matrix.toRows₁_fromRows]

private theorem residualT_coef_start {n L : ℕ} (E : ℝ) (a : Fin L) :
    cellCoef n E a (cellStart n a) = residualTU E (a.val % n + 1) := by
  simp only [cellCoef, ite_true, residualTU]
  push_cast; ring_nf

private theorem residualT_coef_prev {n L : ℕ} (hL : 2 ≤ L) (E : ℝ) (a : Fin L) :
    cellCoef n E a (cellPrev n a) = -residualTU E (a.val % n) := by
  simp only [cellCoef, residualT_prev_ne hL a, ite_false, ite_true, residualTU]

private theorem residualT_coef_other {n L : ℕ} (E : ℝ) (a α : Fin L) (h1 : α ≠ cellStart n a)
    (h2 : α ≠ cellPrev n a) : cellCoef n E a α = 0 := by
  simp only [cellCoef, h1, h2, ite_false]

/-- `Σ_α c_{aα} X_α` has only the two anchor terms. -/
private theorem residualT_sum_coef {n L : ℕ} (hL : 2 ≤ L) (E : ℝ) {M : Type*} [AddCommGroup M]
    [Module ℂ M] (a : Fin L) (X : Fin L → M) :
    ∑ α, ((cellCoef n E a α : ℝ) : ℂ) • X α =
      ((residualTU E (a.val % n + 1) : ℝ) : ℂ) • X (cellStart n a) +
        ((-residualTU E (a.val % n) : ℝ) : ℂ) • X (cellPrev n a) := by
  rw [Finset.sum_eq_add (cellStart n a) (cellPrev n a) (residualT_prev_ne hL a).symm
    (fun c _ hc => by rw [residualT_coef_other E a c hc.1 hc.2]; simp)
    (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h),
    residualT_coef_start, residualT_coef_prev hL]

private theorem residualT_src_eq {n L : ℕ} (E : ℝ) (a b : Fin L) :
    cellSrc n E a b = if cellStart n b = cellStart n a ∧ b.val % n < a.val % n then
      residualTU E (a.val % n - b.val % n - 1 + 1) else 0 := by
  unfold cellSrc
  split_ifs with h
  · simp only [residualTU]
    rw [show a.val % n - b.val % n - 1 + 1 = a.val % n - b.val % n by omega,
      Nat.cast_sub (by omega : b.val % n ≤ a.val % n)]
  · rfl

private theorem residualT_toBlocks₁₁_sub {W : ℕ} (X Y : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    (X - Y).toBlocks₁₁ = X.toBlocks₁₁ - Y.toBlocks₁₁ := by ext; rfl

private theorem residualT_toBlocks₁₂_sub {W : ℕ} (X Y : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    (X - Y).toBlocks₁₂ = X.toBlocks₁₂ - Y.toBlocks₁₂ := by ext; rfl

/-- The exact interpolation identity: the remainder of `G_{ab}` after the anchor and source
terms is driven by the differences of the transfer products to the free ones. -/
private theorem residualT_identity {W L n : ℕ} (hL : 2 ≤ L) (hn : 1 ≤ n) {E : ℝ} (hE : |E| < 2)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (z : ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hG : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
        z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * G = 1) (a b : Fin L) :
    blockOf G a b - (∑ α, ((cellCoef n E a α : ℝ) : ℂ) • blockOf G α b) -
        ((cellSrc n E a b : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) =
      (cellProd z V (cellStart n a) (a.val % n) - blockT (E : ℂ) 0 ^ (a.val % n)).toBlocks₁₁ *
          blockOf G (cellStart n a) b +
        (cellProd z V (cellStart n a) (a.val % n) - blockT (E : ℂ) 0 ^ (a.val % n)).toBlocks₁₂ *
          blockOf G (cellPrev n a) b +
        if cellStart n b = cellStart n a ∧ b.val % n < a.val % n then
          (cellProd z V (finRotate L b) (a.val % n - b.val % n - 1) -
            blockT (E : ℂ) 0 ^ (a.val % n - b.val % n - 1)).toBlocks₁₁ else 0 := by
  set s := cellStart n a with hs_def
  set j := a.val % n with hj_def
  have hsa : s.val + j = a.val := residualT_start_add a
  have hsL : s.val + j < L := by rw [hsa]; exact a.isLt
  have hrot : (finRotate L ^ j) s = a := by
    apply Fin.ext; rw [residualT_rotPow_val, Nat.mod_eq_of_lt hsL, hsa]
  have iter := residualT_col_iter V z G hG s b j hsL
  rw [hrot] at iter
  have top := congrArg Matrix.toRows₁ iter
  have hprev : (finRotate L).symm s = cellPrev n a := rfl
  -- the top block of the iterated column
  have hGab : blockOf G a b = (cellProd z V s j).toBlocks₁₁ * blockOf G s b +
      (cellProd z V s j).toBlocks₁₂ * blockOf G (cellPrev n a) b +
      if cellStart n b = cellStart n a ∧ b.val % n < a.val % n then
        (cellProd z V (finRotate L b) (j - b.val % n - 1)).toBlocks₁₁ else 0 := by
    have e1 : (residualTCol G a b).toRows₁ = blockOf G a b := rfl
    have e2 : residualTCol G s b = Matrix.fromRows (blockOf G s b)
        (blockOf G ((finRotate L).symm s) b) := rfl
    rw [e1, e2, hprev, residualT_toRows₁_add, residualT_toRows₁_mul] at top
    rw [top]
    have hc := residualT_src_iff hn a b
    rw [← hs_def, ← hj_def] at hc
    by_cases hcond : cellStart n b = cellStart n a ∧ b.val % n < a.val % n
    · have hc' := hc.mp hcond
      have hk : s.val + j - b.val - 1 = j - b.val % n - 1 := by
        have hb := residualT_start_add (n := n) b
        rw [hcond.1] at hb
        omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc'), ite_eq_left_of_eq_true _ _ (eq_true hcond), hk]
      congr 1
      ext i k
      change (∑ x : Fin W ⊕ Fin W, cellProd z V (finRotate L b) (j - b.val % n - 1) (Sum.inl i) x *
        Matrix.fromRows (1 : Matrix (Fin W) (Fin W) ℂ) 0 x k) = _
      simp [Fintype.sum_sum_type, Matrix.one_apply, Matrix.toBlocks₁₁]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hcond (hc.mpr h))),
        ite_eq_right_of_eq_false _ _ (eq_false hcond)]
      ext i k; rfl
  rw [hGab, residualT_sum_coef hL, residualT_src_eq, residualT_toBlocks₁₁_sub,
    residualT_toBlocks₁₂_sub,
    residualT_free_pow hE, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂]
  rw [← hs_def, ← hj_def]
  split_ifs with hcond
  · rw [residualT_toBlocks₁₁_sub, residualT_free_pow hE, Matrix.toBlocks_fromBlocks₁₁]
    simp only [sub_mul, Matrix.smul_mul, Matrix.one_mul, Complex.ofReal_neg, neg_smul, neg_mul]
    abel
  · simp only [sub_mul, Matrix.smul_mul, Matrix.one_mul, Complex.ofReal_zero, zero_smul,
      Complex.ofReal_neg, neg_smul, neg_mul]
    abel


private theorem residualT_norm_le_one_of {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    (X : Matrix m k ℂ) (h : Xᴴ * X = 1) (h1 : ‖(1 : Matrix k k ℂ)‖ ≤ 1) : ‖X‖ ≤ 1 := by
  have := Matrix.l2_opNorm_conjTranspose_mul_self X
  rw [h] at this
  nlinarith [norm_nonneg X]

private theorem residualT_norm_one_le (k : Type*) [Fintype k] [DecidableEq k] :
    ‖(1 : Matrix k k ℂ)‖ ≤ 1 := by
  have := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix k k ℂ)
  rw [Matrix.conjTranspose_one, Matrix.one_mul] at this
  nlinarith [norm_nonneg (1 : Matrix k k ℂ)]

private theorem residualT_norm_smul_one_le {W : ℕ} (c : ℂ) :
    ‖c • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ ‖c‖ := by
  rw [norm_smul]
  have := residualT_norm_one_le (Fin W)
  nlinarith [norm_nonneg c]

/-- The block embeddings `ι₁ = (I; 0)` and `ι₂ = (0; I)`. -/
private def residualTι₁ (W : ℕ) : Matrix (Fin W ⊕ Fin W) (Fin W) ℂ := Matrix.fromRows 1 0
private def residualTι₂ (W : ℕ) : Matrix (Fin W ⊕ Fin W) (Fin W) ℂ := Matrix.fromRows 0 1

private theorem residualT_normι₁ (W : ℕ) : ‖residualTι₁ W‖ ≤ 1 := by
  apply residualT_norm_le_one_of _ _ (residualT_norm_one_le _)
  ext i j
  change (∑ x : Fin W ⊕ Fin W, star (residualTι₁ W x i) * residualTι₁ W x j) = _
  simp [residualTι₁, Fintype.sum_sum_type, Matrix.one_apply, eq_comm]

private theorem residualT_normι₂ (W : ℕ) : ‖residualTι₂ W‖ ≤ 1 := by
  apply residualT_norm_le_one_of _ _ (residualT_norm_one_le _)
  ext i j
  change (∑ x : Fin W ⊕ Fin W, star (residualTι₂ W x i) * residualTι₂ W x j) = _
  simp [residualTι₂, Fintype.sum_sum_type, Matrix.one_apply, eq_comm]

private theorem residualT_blocks_eq {W : ℕ} (X : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    X.toBlocks₁₁ = (residualTι₁ W)ᴴ * X * residualTι₁ W ∧
    X.toBlocks₁₂ = (residualTι₁ W)ᴴ * X * residualTι₂ W ∧
    X.toBlocks₂₁ = (residualTι₂ W)ᴴ * X * residualTι₁ W ∧
    X.toBlocks₂₂ = (residualTι₂ W)ᴴ * X * residualTι₂ W := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [residualTι₁, residualTι₂, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

private theorem residualT_norm_block_le {W : ℕ} (X : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    ‖X.toBlocks₁₁‖ ≤ ‖X‖ ∧ ‖X.toBlocks₁₂‖ ≤ ‖X‖ := by
  obtain ⟨h1, h2, -, -⟩ := residualT_blocks_eq X
  have a1 := residualT_normι₁ W
  have a2 := residualT_normι₂ W
  have b1 : ‖(residualTι₁ W)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact a1
  constructor
  · rw [h1]
    calc _ ≤ ‖(residualTι₁ W)ᴴ * X‖ * ‖residualTι₁ W‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖(residualTι₁ W)ᴴ‖ * ‖X‖) * 1 := by
          gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖X‖ * 1 := by gcongr
      _ = ‖X‖ := by ring
  · rw [h2]
    calc _ ≤ ‖(residualTι₁ W)ᴴ * X‖ * ‖residualTι₂ W‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖(residualTι₁ W)ᴴ‖ * ‖X‖) * 1 := by
          gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖X‖ * 1 := by gcongr
      _ = ‖X‖ := by ring


/-- In the bulk `|E| ≤ 2 - κ`: `sin ϑ ≥ κ/2`. -/
private theorem residualT_sin_ge {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) :
    κ / 2 ≤ Real.sin (Real.arccos (E / 2)) := by
  have hS := Real.sin_arccos (E / 2)
  set S := Real.sin (Real.arccos (E / 2))
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hE 2
  have hpos : 0 ≤ 1 - (E / 2) ^ 2 := by nlinarith
  have hS2 : S ^ 2 = 1 - (E / 2) ^ 2 := by rw [hS, Real.sq_sqrt hpos]
  have hS1 : S ≤ 1 := Real.sin_le_one _
  have hS0 : 0 ≤ S := by rw [hS]; exact Real.sqrt_nonneg _
  nlinarith

private theorem residualTU_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (m : ℕ) : |residualTU E m| ≤ 2 / κ := by
  have hs := residualT_sin_ge hκ hκ2 hE
  have hs0 : 0 < Real.sin (Real.arccos (E / 2)) := by linarith
  unfold residualTU
  rw [abs_div, abs_of_pos hs0, div_le_div_iff₀ hs0 hκ]
  have := Real.abs_sin_le_one (m * Real.arccos (E / 2))
  nlinarith

private theorem residualT_coef_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a α : Fin L) : |cellCoef n E a α| ≤ 2 / κ := by
  have h0 : 0 ≤ 2 / κ := by positivity
  unfold cellCoef
  split_ifs
  · have := residualTU_abs_le hκ hκ2 hE (a.val % n + 1)
    simpa [residualTU] using this
  · have := residualTU_abs_le hκ hκ2 hE (a.val % n)
    simpa [residualTU, abs_neg] using this
  · simpa using h0

private theorem residualT_src_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a b : Fin L) : |cellSrc n E a b| ≤ 2 / κ := by
  rw [residualT_src_eq]
  split_ifs
  · exact residualTU_abs_le hκ hκ2 hE _
  · simp only [abs_zero]; positivity

/-- The prefix of the cell of `a` up to `a` is admissible for `CellClose`. -/
private theorem residualT_adm_prefix {n L : ℕ} (hn : 1 ≤ n) (a : Fin L) :
    (cellStart n a).val % n + a.val % n ≤ n ∧ (cellStart n a).val + a.val % n ≤ L := by
  have h1 : (cellStart n a).val % n = 0 := Nat.mul_mod_left _ _
  have h2 := Nat.mod_lt a.val (by omega : 0 < n)
  have h3 := residualT_start_add (n := n) a
  constructor <;> omega

/-- The product from `b + 1` to `a` is admissible for `CellClose` when `b` precedes `a` in its
cell. -/
private theorem residualT_adm_src {n L : ℕ} (hn : 1 ≤ n) (a b : Fin L)
    (h : cellStart n b = cellStart n a ∧ b.val % n < a.val % n) :
    (finRotate L b).val % n + (a.val % n - b.val % n - 1) ≤ n ∧
      (finRotate L b).val + (a.val % n - b.val % n - 1) ≤ L := by
  have hab := (residualT_src_iff hn a b).mp h
  have ha := residualT_start_add (n := n) a
  have hb := residualT_start_add (n := n) b
  rw [h.1] at hb
  have hlt := a.isLt
  have hj := Nat.mod_lt a.val (by omega : 0 < n)
  have hbL : b.val + 1 < L := by omega
  rw [residualT_rot_val, Nat.mod_eq_of_lt hbL]
  have hmod : (b.val + 1) % n = b.val % n + 1 := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt (by omega)]
  constructor <;> omega

/-- The remainder `G_{ab} - Σ_α c_{aα} G_{αb} - q_{ab} I` of the first-coordinate
interpolation. -/
private def residualTRem (n : ℕ) (E : ℝ) {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : Matrix (Fin W) (Fin W) ℂ :=
  blockOf G a b - (∑ α, ((cellCoef n E a α : ℝ) : ℂ) • blockOf G α b) -
    ((cellSrc n E a b : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)

private theorem residualT_rem_op {W L n : ℕ} (hL : 2 ≤ L) (hn : 1 ≤ n) {E ε : ℝ} (hE : |E| < 2)
    (hε : 0 ≤ ε) (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (z : ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hG : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
        z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * G = 1)
    (hcl : CellClose n E z V ε) (a b : Fin L) :
    ‖residualTRem n E G a b‖ ≤
      ε * (1 + ‖blockOf G (cellStart n a) b‖ + ‖blockOf G (cellPrev n a) b‖) := by
  unfold residualTRem
  rw [residualT_identity hL hn hE V z G hG a b]
  obtain ⟨p1, p2⟩ := residualT_adm_prefix (L := L) hn a
  have hP := hcl _ _ p1 p2
  unfold prodErr at hP
  obtain ⟨b1, b2⟩ := residualT_norm_block_le
    (cellProd z V (cellStart n a) (a.val % n) - blockT (E : ℂ) 0 ^ (a.val % n))
  have hsrc : ‖(if cellStart n b = cellStart n a ∧ b.val % n < a.val % n then
      (cellProd z V (finRotate L b) (a.val % n - b.val % n - 1) -
        blockT (E : ℂ) 0 ^ (a.val % n - b.val % n - 1)).toBlocks₁₁ else 0)‖ ≤ ε := by
    split_ifs with h
    · obtain ⟨q1, q2⟩ := residualT_adm_src hn a b h
      have hQ := hcl _ _ q1 q2
      unfold prodErr at hQ
      exact (residualT_norm_block_le _).1.trans hQ
    · simpa using hε
  have g1 := norm_nonneg (blockOf G (cellStart n a) b)
  have g2 := norm_nonneg (blockOf G (cellPrev n a) b)
  calc _ ≤ ‖(cellProd z V (cellStart n a) (a.val % n) -
          blockT (E : ℂ) 0 ^ (a.val % n)).toBlocks₁₁ * blockOf G (cellStart n a) b‖ +
        ‖(cellProd z V (cellStart n a) (a.val % n) -
          blockT (E : ℂ) 0 ^ (a.val % n)).toBlocks₁₂ * blockOf G (cellPrev n a) b‖ + ε := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _)) hsrc)
    _ ≤ ε * ‖blockOf G (cellStart n a) b‖ + ε * ‖blockOf G (cellPrev n a) b‖ + ε := by
        gcongr
        · exact (Matrix.l2_opNorm_mul _ _).trans (by gcongr; exact b1.trans hP)
        · exact (Matrix.l2_opNorm_mul _ _).trans (by gcongr; exact b2.trans hP)
    _ = _ := by ring

private theorem residualT_blockOf_conjTranspose {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    blockOf Gᴴ a b = (blockOf G b a)ᴴ := by
  ext; simp [blockOf]

/-- The second-coordinate remainder is the adjoint of the first-coordinate remainder of `G^*`. -/
private theorem residualT_adj (n : ℕ) (E : ℝ) {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (b α : Fin L) :
    blockOf G α b - (∑ β, ((cellCoef n E b β : ℝ) : ℂ) • blockOf G α β) -
        ((cellSrc n E b α : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) =
      (residualTRem n E Gᴴ b α)ᴴ := by
  unfold residualTRem
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    residualT_blockOf_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one,
    Complex.star_def, Complex.conj_ofReal]

private theorem residualT_resolvent_conj {W L : ℕ} {V : Fin L → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ r, (V r).IsHermitian) (z : ℂ) :
    resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V)
        (starRingEnd ℂ z) =
      (resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V) z)ᴴ := by
  unfold resolventMat
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    (residualT_op_isHermitian hV).eq, Matrix.conjTranspose_one, Complex.star_def]

private theorem residualT_anchor_le (n : ℕ) {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b α β : Fin L)
    (hα : α = cellStart n a ∨ α = cellPrev n a) (hβ : β = cellStart n b ∨ β = cellPrev n b) :
    ‖blockOf G α β‖ ≤ anchorNorm n G a b := by
  unfold anchorNorm
  rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)


/-- An entry is bounded by the operator norm. -/
private lemma residual_entry_le {m : Type*} [Fintype m] [DecidableEq m]
    (X : Matrix m m ℂ) (i j : m) : ‖X i j‖ ≤ ‖X‖ := by
  have h := Matrix.l2_opNorm_mulVec X (EuclideanSpace.single j (1 : ℂ))
  have hn : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [hn, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv m ℂ).symm
    (X.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  convert this using 2
  simp

/-- The normalized trace `W⁻¹ Σ_i X_ii` of a block. -/
private def residualNtr {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) : ℂ := (W : ℂ)⁻¹ * ∑ i, X i i

private lemma residual_ntr_le {W : ℕ} (hW : 1 ≤ W) (X : Matrix (Fin W) (Fin W) ℂ) :
    ‖residualNtr X‖ ≤ ‖X‖ := by
  unfold residualNtr
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hW0]
  calc ‖∑ i, X i i‖ ≤ ∑ i, ‖X i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin W, ‖X‖ := Finset.sum_le_sum fun i _ => residual_entry_le X i i
    _ = W * ‖X‖ := by simp

/-- `|c_{aα}| ≤ 2/κ`, and `c_{aα} = 0` off the two anchors of the cell of `a`. -/
private lemma residual_coef_ne {n L : ℕ} (E : ℝ) (a α : Fin L) (h : cellCoef n E a α ≠ 0) :
    α = cellStart n a ∨ α = cellPrev n a := by
  by_contra hc
  rw [not_or] at hc
  exact h (by simp [cellCoef, hc.1, hc.2])

/-- `Σ_α |c_{aα}| ≤ 4/κ`. -/
private lemma residual_sum_coef_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a : Fin L) : ∑ α, |cellCoef n E a α| ≤ 4 / κ := by
  have h : ∀ α, |cellCoef n E a α| ≤ 2 / κ * ((if α = cellStart n a then 1 else 0) +
      (if α = cellPrev n a then 1 else 0)) := by
    intro α
    have hb := residualT_coef_abs_le hκ hκ2 hE n a α
    by_cases h1 : α = cellStart n a
    · have : (0 : ℝ) ≤ (if α = cellPrev n a then 1 else 0) := by split_ifs <;> norm_num
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      nlinarith [(by positivity : (0 : ℝ) ≤ 2 / κ)]
    · by_cases h2 : α = cellPrev n a
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
        linarith
      · have : cellCoef n E a α = 0 := by simp [cellCoef, h1, h2]
        rw [this, ite_eq_right_of_eq_false _ _ (eq_false h1),
          ite_eq_right_of_eq_false _ _ (eq_false h2)]
        simp
  calc ∑ α, |cellCoef n E a α| ≤ ∑ α, 2 / κ * ((if α = cellStart n a then 1 else 0) +
        (if α = cellPrev n a then 1 else 0)) := Finset.sum_le_sum fun α _ => h α
    _ = 2 / κ * (1 + 1) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        simp
    _ = 4 / κ := by ring

/-- A combination `Σ_α c_{aα} Y_α` is at most `4/κ` times the largest `‖Y_α‖` over the anchors of
the cell of `a`. -/
private lemma residual_single_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F] (a : Fin L)
    (Y : Fin L → F) (A : ℝ) (hA : 0 ≤ A)
    (hY : ∀ α, (α = cellStart n a ∨ α = cellPrev n a) → ‖Y α‖ ≤ A) :
    ‖∑ α, ((cellCoef n E a α : ℝ) : ℂ) • Y α‖ ≤ 4 / κ * A := by
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ α, ‖((cellCoef n E a α : ℝ) : ℂ) • Y α‖ ≤ |cellCoef n E a α| * A := by
    intro α
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    by_cases h0 : cellCoef n E a α = 0
    · rw [h0]; simp
    · exact mul_le_mul_of_nonneg_left (hY α (residual_coef_ne E a α h0)) (abs_nonneg _)
  calc ∑ α, ‖((cellCoef n E a α : ℝ) : ℂ) • Y α‖ ≤ ∑ α, |cellCoef n E a α| * A :=
        Finset.sum_le_sum fun α _ => h α
    _ = (∑ α, |cellCoef n E a α|) * A := by rw [Finset.sum_mul]
    _ ≤ 4 / κ * A := mul_le_mul_of_nonneg_right (residual_sum_coef_le hκ hκ2 hE n a) hA

/-- A combination `Σ_{α,β} c_{aα} c_{bβ} X_{αβ}` is at most `(4/κ)²` times the largest `‖X_{αβ}‖`
over the anchor pairs of the cells of `a` and `b`. -/
private lemma residual_double_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F] (a b : Fin L)
    (X : Fin L → Fin L → F) (A : ℝ) (hA : 0 ≤ A)
    (hX : ∀ α β, (α = cellStart n a ∨ α = cellPrev n a) → (β = cellStart n b ∨ β = cellPrev n b) →
      ‖X α β‖ ≤ A) :
    ‖∑ α, ∑ β, ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) • X α β‖ ≤ (4 / κ) ^ 2 * A := by
  have e : ∑ α, ∑ β, ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) • X α β =
      ∑ α, ((cellCoef n E a α : ℝ) : ℂ) • ∑ β, ((cellCoef n E b β : ℝ) : ℂ) • X α β := by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [smul_smul]; push_cast; rfl
  rw [e]
  have h4 : 0 ≤ 4 / κ * A := by positivity
  refine (residual_single_le hκ hκ2 hE n a _ (4 / κ * A) h4 fun α hα => ?_).trans
    (le_of_eq (by ring))
  exact residual_single_le hκ hκ2 hE n b _ A hA fun β hβ => hX α β hα hβ

/-- `|d_{ab}| ≤ 2/κ + 8/κ²`. -/
private lemma residual_cellD_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a b : Fin L) : |cellD n E a b| ≤ 2 / κ + 8 / κ ^ 2 := by
  unfold cellD
  have h1 := residualT_src_abs_le hκ hκ2 hE n a b
  have h2 : |∑ α, cellCoef n E a α * cellSrc n E b α| ≤ 8 / κ ^ 2 := by
    have := residual_single_le hκ hκ2 hE n (F := ℂ) a (fun α => ((cellSrc n E b α : ℝ) : ℂ))
      (2 / κ) (by positivity) fun α _ => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact residualT_src_abs_le hκ hκ2 hE n b α
    have e : ‖∑ α, ((cellCoef n E a α : ℝ) : ℂ) • ((cellSrc n E b α : ℝ) : ℂ)‖ =
        |∑ α, cellCoef n E a α * cellSrc n E b α| := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real]; push_cast; simp [smul_eq_mul]
    rw [e] at this
    calc _ ≤ 4 / κ * (2 / κ) := this
      _ = 8 / κ ^ 2 := by ring
  calc _ ≤ |cellSrc n E a b| + |∑ α, cellCoef n E a α * cellSrc n E b α| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

/-- `Σ_c |q_{ac}| ≤ 2n/κ`: at most `n` sources precede `a` in its cell. -/
private lemma residual_sum_src_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) (hn : 1 ≤ n) {L : ℕ} (a : Fin L) : ∑ c, |cellSrc n E a c| ≤ n * (2 / κ) := by
  set S := univ.filter fun c : Fin L => cellStart n c = cellStart n a ∧ c.val % n < a.val % n
  have hS : S.card ≤ n := by
    have := Finset.card_le_card_of_injOn (s := S) (t := range n) (fun c => c.val % n)
      (fun c _ => by simp only [coe_range, Set.mem_Iio]; exact Nat.mod_lt _ (by omega))
      (by
        intro c hc d hd hcd
        rw [Finset.mem_coe, Finset.mem_filter] at hc hd
        apply Fin.ext
        have e1 := Nat.div_add_mod' c.val n
        have e2 := Nat.div_add_mod' d.val n
        have h1 := congrArg Fin.val hc.2.1
        have h2 := congrArg Fin.val hd.2.1
        simp only [cellStart] at h1 h2
        simp only at hcd
        omega)
    simpa using this
  have h : ∀ c, |cellSrc n E a c| ≤ 2 / κ * (if c ∈ S then 1 else 0) := by
    intro c
    by_cases hc : c ∈ S
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), mul_one]
      exact residualT_src_abs_le hκ hκ2 hE n a c
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      have : cellSrc n E a c = 0 := by
        unfold cellSrc
        split_ifs with h'
        · exact (hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩)).elim
        · rfl
      simp [this]
  calc ∑ c, |cellSrc n E a c| ≤ ∑ c, 2 / κ * (if c ∈ S then 1 else 0) :=
        Finset.sum_le_sum fun c _ => h c
    _ = 2 / κ * S.card := by rw [← Finset.mul_sum]; simp
    _ ≤ 2 / κ * n := by gcongr
    _ = n * (2 / κ) := by ring

private lemma residual_ntr_sub {W : ℕ} (X Y : Matrix (Fin W) (Fin W) ℂ) :
    residualNtr (X - Y) = residualNtr X - residualNtr Y := by
  unfold residualNtr; simp only [Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]

private lemma residual_ntr_add {W : ℕ} (X Y : Matrix (Fin W) (Fin W) ℂ) :
    residualNtr (X + Y) = residualNtr X + residualNtr Y := by
  unfold residualNtr; simp only [Matrix.add_apply, Finset.sum_add_distrib, mul_add]

private lemma residual_ntr_smul {W : ℕ} (c : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    residualNtr (c • X) = c * residualNtr X := by
  unfold residualNtr; simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]; ring

private lemma residual_ntr_sum {W : ℕ} {ι : Type*} (s : Finset ι)
    (X : ι → Matrix (Fin W) (Fin W) ℂ) :
    residualNtr (∑ i ∈ s, X i) = ∑ i ∈ s, residualNtr (X i) := by
  unfold residualNtr; simp only [Matrix.sum_apply, Finset.mul_sum]; rw [Finset.sum_comm]

private lemma residual_ntr_one {W : ℕ} (hW : 1 ≤ W) :
    residualNtr (1 : Matrix (Fin W) (Fin W) ℂ) = 1 := by
  have hW0 : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold residualNtr
  simp only [Matrix.one_apply_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ hW0

private lemma residual_ntr_blockOf {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : residualNtr (blockOf G a b) = blockTr G a b := rfl

/-- The normalized trace of the Green-block remainder. -/
private lemma residual_ntr_interp {W L : ℕ} (hW : 1 ≤ W) (n : ℕ) (E : ℝ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    residualNtr (blockOf G a b - interpBlock n E G a b) =
      blockTr G a b - ∑ α, ∑ β, ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * blockTr G α β -
        ((cellD n E a b : ℝ) : ℂ) := by
  unfold interpBlock
  simp only [residual_ntr_sub, residual_ntr_add, residual_ntr_sum, residual_ntr_smul,
    residual_ntr_one hW, residual_ntr_blockOf, mul_one]
  ring

/-- The entries of the Green-block remainder. -/
private lemma residual_entry_interp {W L : ℕ} (n : ℕ) (E : ℝ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) (i j : Fin W) :
    (blockOf G a b - interpBlock n E G a b) i j =
      G (a, i) (b, j) - ∑ α, ∑ β, ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) *
        G (α, i) (β, j) - if i = j then ((cellD n E a b : ℝ) : ℂ) else 0 := by
  unfold interpBlock
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, blockOf, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  ring


/-- The source coefficient through the offset of `b` from the first block of the cell of `a`. -/
private lemma residual_src_eq {n L : ℕ} (hn : 1 ≤ n) (E : ℝ) (a b : Fin L) :
    cellSrc n E a b =
      if (b.val + L - (cellStart n a).val) % L < a.val % n then
        Real.sin (((a.val % n : ℕ) - (((b.val + L - (cellStart n a).val) % L : ℕ) : ℝ)) *
          Real.arccos (E / 2)) / Real.sin (Real.arccos (E / 2))
      else 0 := by
  have ha := Nat.div_add_mod' a.val n
  have hb := Nat.div_add_mod' b.val n
  have hsa : (cellStart n a).val = a.val / n * n := rfl
  have hsb : (cellStart n b).val = b.val / n * n := rfl
  have hmodn := Nat.mod_lt a.val (by omega : 0 < n)
  have hbmodn := Nat.mod_lt b.val (by omega : 0 < n)
  have haL := a.isLt
  have hbL := b.isLt
  unfold cellSrc
  by_cases hab : (cellStart n a).val ≤ b.val
  · have hk : (b.val + L - (cellStart n a).val) % L = b.val - (cellStart n a).val := by
      rw [show b.val + L - (cellStart n a).val = (b.val - (cellStart n a).val) + L by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hk]
    have hiff : (cellStart n b = cellStart n a ∧ b.val % n < a.val % n) ↔
        b.val - (cellStart n a).val < a.val % n := by
      constructor
      · rintro ⟨h1, h2⟩
        have h1' := congrArg Fin.val h1
        rw [hsb, hsa] at h1'
        rw [hsa] at hab ⊢
        rw [h1'] at hb
        omega
      · intro hlt
        have hq : b.val / n = a.val / n := by
          apply Nat.div_eq_of_lt_le
          · rw [hsa] at hab; linarith
          · rw [Nat.succ_mul]; rw [hsa] at hlt; omega
        refine ⟨Fin.ext (by rw [hsa, hsb, hq]), ?_⟩
        rw [hsa] at hlt hab
        rw [hq] at hb
        omega
    by_cases hc : cellStart n b = cellStart n a ∧ b.val % n < a.val % n
    · have hlt := hiff.mp hc
      simp only [hc, hlt, and_self, ite_true]
      have h1 := congrArg Fin.val hc.1
      rw [hsb, hsa] at h1
      have : b.val - (cellStart n a).val = b.val % n := by rw [hsa]; rw [h1] at hb; omega
      rw [this]
    · have hlt : ¬ b.val - (cellStart n a).val < a.val % n := fun h => hc (hiff.mpr h)
      simp only [hc, hlt, ite_false]
  · have hk : (b.val + L - (cellStart n a).val) % L = b.val + L - (cellStart n a).val :=
      Nat.mod_eq_of_lt (by omega)
    have hc : ¬ (cellStart n b = cellStart n a ∧ b.val % n < a.val % n) := by
      rintro ⟨h1, -⟩
      have := congrArg Fin.val h1
      rw [hsb, hsa] at this
      rw [hsa] at hab
      omega
    have hlt : ¬ b.val + L - (cellStart n a).val < a.val % n := by omega
    rw [hk]
    simp only [hc, hlt, ite_false]

/-- The form of Lemma 6.5 [da:lem:free-interpolation] at every first block of a cell, offset
`j < n` and source `b`, gives `RowInterp`. -/
private lemma residual_rowInterp_of {n L : ℕ} (hn : 1 ≤ n) (hL : 2 ≤ L) (E : ℝ)
    (M : Matrix (Fin L) (Fin L) ℂ) (δ : ℝ)
    (h : ∀ b₀ : Fin L, ∀ j : ℕ, j < n → ∀ b : Fin L,
      ‖M ((finRotate L ^ j) b₀) b -
        (((Real.sin ((j + 1) * Real.arccos (E / 2)) / Real.sin (Real.arccos (E / 2)) : ℝ) : ℂ) *
            M b₀ b -
          ((Real.sin (j * Real.arccos (E / 2)) / Real.sin (Real.arccos (E / 2)) : ℝ) : ℂ) *
            M ((finRotate L).symm b₀) b +
          ((if (b.val + L - b₀.val) % L < j then
            Real.sin (((j : ℝ) - ((b.val + L - b₀.val) % L : ℕ)) * Real.arccos (E / 2)) /
              Real.sin (Real.arccos (E / 2)) else 0 : ℝ) : ℂ))‖ ≤ δ) :
    RowInterp n E M δ := by
  intro a b
  set b₀ := cellStart n a with hb₀
  set j := a.val % n with hj
  have hjn : j < n := Nat.mod_lt _ (by omega)
  have hsum : b₀.val + j = a.val := Nat.div_add_mod' a.val n
  have hrot : (finRotate L ^ j) b₀ = a := by
    apply Fin.ext
    rw [residualT_rotPow_val, hsum, Nat.mod_eq_of_lt a.isLt]
  have key := h b₀ j hjn b
  rw [hrot] at key
  have hS : ∑ α : Fin L, (cellCoef n E a α : ℂ) * M α b =
      ((Real.sin ((j + 1) * Real.arccos (E / 2)) / Real.sin (Real.arccos (E / 2)) : ℝ) : ℂ) *
          M b₀ b -
        ((Real.sin (j * Real.arccos (E / 2)) / Real.sin (Real.arccos (E / 2)) : ℝ) : ℂ) *
          M ((finRotate L).symm b₀) b := by
    have hne := residualT_prev_ne (n := n) hL a
    rw [Finset.sum_eq_add (cellStart n a) (cellPrev n a) hne.symm
      (fun c _ hc => by simp [cellCoef, hc.1, hc.2])
      (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
    simp only [cellCoef, ite_true, hne, ite_false]
    have hp : cellPrev n a = (finRotate L).symm b₀ := rfl
    rw [hp]
    push_cast
    ring
  have hQ : ((cellSrc n E a b : ℝ) : ℂ) =
      ((if (b.val + L - b₀.val) % L < j then
        Real.sin (((j : ℝ) - ((b.val + L - b₀.val) % L : ℕ)) * Real.arccos (E / 2)) /
          Real.sin (Real.arccos (E / 2)) else 0 : ℝ) : ℂ) := by
    rw [residual_src_eq hn E a b]
  rw [hS, hQ]
  exact key

/-- Lemma 6.5 [da:lem:free-interpolation] on the cells: the Dyson matrix `(A_L - w)⁻¹` with
`Im w ≥ c/g²` and `|w - E| ≤ C/g²` interpolates with error `C' n/g²`, and has entries and
`g^{-2}`-weighted rows bounded by `C'`. -/
theorem rowInterp_dyson (κ C c : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 0 < C) (hc : 0 < c) :
    ∃ Cκ C' c₀ : ℝ, 1 ≤ Cκ ∧ 0 < C' ∧ 0 < c₀ ∧ ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, 4 * g ^ 2 ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ w : ℂ, c / g ^ 2 ≤ w.im → ‖w - E‖ ≤ C / g ^ 2 →
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ c₀ * g ^ 2 →
        RowInterp n E (cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ (C' * n / g ^ 2) ∧
        (∀ a b, ‖(cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ a b‖ ≤ C') ∧
        ∀ a, (g ^ 2)⁻¹ * ∑ b, ‖(cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ a b‖ ≤ C' := by
  obtain ⟨Cκ, C', c₀, hCκ, hC', hc₀, H⟩ := free_interpolation κ C c hκ hκ2 hC hc
  refine ⟨Cκ, C', c₀, hCκ, hC', hc₀, fun g hg L hL E hE w hw hwE n hn hnc => ?_⟩
  obtain ⟨h1, h2, h3⟩ := H g hg L hL E hE w hw hwE
  have hg1 : 1 ≤ g := hCκ.trans hg
  have hL2 : 2 ≤ L := by
    have : (2 : ℝ) ≤ L := by nlinarith
    exact_mod_cast this
  refine ⟨residual_rowInterp_of hn hL2 E _ _ fun b₀ j hj b => ?_, h1, h2⟩
  have := h3 b₀ n hnc j hj b
  simpa only [] using this

/-- `b A_L` is Hermitian for real `b`. -/
private lemma residual_smul_cycleAdj_isHermitian (b : ℝ) (L : ℕ) :
    (((b : ℝ) : ℂ) • cycleAdj L).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (cycleAdj_isHermitian L).eq, Complex.star_def, Complex.conj_ofReal]

/-- `(bA_L - w)` and the Dyson matrix `(bA_L - w)⁻¹` are mutually inverse when `Im w > 0`,
`w = z + βm`. -/
private lemma residual_dysonMat_mul (b β : ℝ) (L : ℕ) (z m : ℂ) (hw : 0 < (z + β * m).im) :
    (((b : ℝ) : ℂ) • cycleAdj L - (z + β * m) • (1 : Matrix (Fin L) (Fin L) ℂ)) *
        dysonMat b β L z m = 1 ∧
      dysonMat b β L z m *
        (((b : ℝ) : ℂ) • cycleAdj L - (z + β * m) • (1 : Matrix (Fin L) (Fin L) ℂ)) = 1 := by
  have h := sub_smul_mul_resolventMat (residual_smul_cycleAdj_isHermitian b L) hw.ne'
  exact ⟨h, mul_eq_one_comm.mp h⟩

/-- Rows of `(M ⊗ I_W) X`: `((M ⊗ I) X)_{(a,α),y} = Σ_c M_{ac} X_{(c,α),y}`. -/
private lemma residual_kron_mul_apply (W L : ℕ) (M : Matrix (Fin L) (Fin L) ℂ)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a : Fin L) (α : Fin W) (y : Fin L × Fin W) :
    ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * X) (a, α) y = ∑ c : Fin L, M a c * X (c, α) y := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp

/-- `⟨(M ⊗ I) diag(d_c I_W) G⟩_{ab} = Σ_c M_{ac} d_c ⟨G⟩_{cb}`. -/
private lemma residual_blockTr_mul_diag (W L : ℕ) (M : Matrix (Fin L) (Fin L) ℂ) (d : Fin L → ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    blockTr ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
        (Matrix.diagonal (fun x : Fin L × Fin W => d x.1) * G)) a b =
      ∑ c : Fin L, M a c * d c * blockTr G c b := by
  unfold blockTr
  simp only [residual_kron_mul_apply, Matrix.diagonal_mul]
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

/-- `⟨M ⊗ I_W⟩_{ab} = M_{ab}` for `W ≥ 1`. -/
private lemma residual_blockTr_kron (W L : ℕ) (hW : 1 ≤ W) (M : Matrix (Fin L) (Fin L) ℂ)
    (a b : Fin L) : blockTr (M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) a b = M a b := by
  have hW0 : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold blockTr
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- If `M (A - w) = 1` then `(M ⊗ I)(A ⊗ I - w) = 1`. -/
private lemma residual_kron_inv (W L : ℕ) (Mb A : Matrix (Fin L) (Fin L) ℂ) (w : ℂ)
    (h : Mb * (A - w • (1 : Matrix (Fin L) (Fin L) ℂ)) = 1) :
    (Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
      (A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) -
        w • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) = 1 := by
  have e : A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) -
      w • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) =
      (A - w • (1 : Matrix (Fin L) (Fin L) ℂ)) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
    ext ⟨a, α⟩ ⟨b, β⟩
    simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply,
      Prod.mk.injEq, smul_eq_mul]
    by_cases hab : a = b <;> by_cases hαβ : α = β <;> simp [hab, hαβ]
  rw [e, ← Matrix.mul_kronecker_mul, h, Matrix.mul_one, Matrix.one_kronecker_one]

/-- The matrix form of the first identity of (5.32) [gc:eq:scalar], for every `G`: if
`M (A - w) = 1` and `z = w - β'm` then
`G - M⊗I = -(M⊗I) Π(G) + β' (M⊗I) diag(⟨G⟩_{cc} - m) G`. -/
private lemma residual_identity (W L : ℕ) (Mb A : Matrix (Fin L) (Fin L) ℂ) (w z m β' : ℂ)
    (h : Mb * (A - w • (1 : Matrix (Fin L) (Fin L) ℂ)) = 1) (hz : z = w - β' * m)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    G - Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) =
      -((Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
        (1 + (z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) -
            A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * G +
          β' • (Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1) * G))) +
      β' • ((Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
        (Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1 - m) * G)) := by
  set K := Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) with hKdef
  have hK := residual_kron_inv W L Mb A w h
  rw [← hKdef] at hK
  have hKz : K * (z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) -
      A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) = -1 - (β' * m) • K := by
    have e : z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) -
        A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) =
        -(A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) -
          w • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) -
          (β' * m) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) := by
      rw [hz, sub_smul]; abel
    rw [e, Matrix.mul_sub, Matrix.mul_neg, hK, Matrix.mul_smul, Matrix.mul_one]
  have hD : Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1 - m) =
      Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1) -
        m • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) := by
    ext x y
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [Matrix.diagonal_apply_ne _ hxy, Matrix.one_apply_ne hxy]
  have e1 : K * ((1 + (z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) -
        A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * G +
          β' • (Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1) * G))) =
      K + (-G - (β' * m) • (K * G)) +
        β' • (K * (Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1) * G)) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hKz, Matrix.mul_smul]
    rw [sub_mul, Matrix.smul_mul, neg_mul, Matrix.one_mul]
  rw [e1, hD, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_smul]
  module

/-- `⟨·⟩_{ab}` is additive and homogeneous. -/
private lemma residual_blockTr_sub {W L : ℕ} (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockTr (X - Y) a b = blockTr X a b - blockTr Y a b := by
  unfold blockTr
  simp only [Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]

private lemma residual_blockTr_neg {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockTr (-X) a b = -blockTr X a b := by
  unfold blockTr
  simp only [Matrix.neg_apply, Finset.sum_neg_distrib, mul_neg]

private lemma residual_blockTr_add {W L : ℕ} (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockTr (X + Y) a b = blockTr X a b + blockTr Y a b := by
  unfold blockTr
  simp only [Matrix.add_apply, Finset.sum_add_distrib, mul_add]

private lemma residual_blockTr_smul {W L : ℕ} (c : ℂ) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockTr (c • X) a b = c * blockTr X a b := by
  unfold blockTr
  simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring


/-- The averaged residual (5.28) [gc:eq:residual-input] at a point `z = Re z_u + iy` of a
comparison segment is `resComb` with `β = uγ_g` and `M = M_{B,u}(z)` (the identity of
Proposition 7.10 [uvc:prop:residual-compression]). -/
theorem segRes_identity (W : ℕ) (hW : 1 ≤ W) (x : FlowPt × ℝ) (hg : 0 ≤ x.1.g) (hL : 3 ≤ x.1.L)
    (hu : 0 < x.1.u) (hy : 0 < x.2) (ω : Ω W x.1.L) (a b : Fin x.1.L) :
    segRes W x ω a b = resComb (x.1.u * gammaG x.1.g) (segG W x ω)
      (segMat x.1.g x.1.L (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.1.u
        (x.2 / gammaG x.1.g)) a b := by
  have hγ : 0 < gammaG x.1.g := by
    unfold gammaG
    have : (1 : ℝ) ≤ max 1 x.1.g := le_max_left _ _
    positivity
  have hb : 0 ≤ hopB x.1.g := by
    unfold hopB; exact div_nonneg hg (le_trans zero_le_one (le_max_left _ _))
  set re : ℝ := (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re with hre
  set β : ℝ := x.1.u * gammaG x.1.g with hβ
  have hβ0 : 0 < β := mul_pos hu hγ
  set z : ℂ := (re : ℂ) + (x.2 : ℂ) * Complex.I with hz
  have hz' : (re : ℂ) + ((gammaG x.1.g * (x.2 / gammaG x.1.g) : ℝ) : ℂ) * Complex.I = z := by
    rw [hz, mul_div_cancel₀ _ hγ.ne']
  have hzim : z.im = x.2 := by simp [hz]
  set m := mRootV (hopB x.1.g) β x.1.L z with hm
  have hroot : IsDysonRootV (hopB x.1.g) β x.1.L z m :=
    (mRootV_spec (hopB x.1.g) β hb hβ0 x.1.L hL z (by rw [hzim]; exact hy.le)).1
      (by rw [hzim]; exact hy)
  have hw : 0 < (z + β * m).im := by
    have : (z + (β : ℂ) * m).im = x.2 + β * m.im := by simp [hzim]
    rw [this]; nlinarith [hroot.1]
  have hseg : segMat x.1.g x.1.L re x.1.u (x.2 / gammaG x.1.g) =
      dysonMat (hopB x.1.g) β x.1.L z m := by
    unfold segMat; rw [hz']
  rw [hseg]
  have hL1 : 1 ≤ x.1.L := by omega
  have hdiag : ∀ c : Fin x.1.L, dysonMat (hopB x.1.g) β x.1.L z m c c = m := fun c => by
    rw [dysonMat_diag _ _ _ hL1 _ _ hw c]
    exact hroot.2.symm
  obtain ⟨-, hMA⟩ := residual_dysonMat_mul (hopB x.1.g) β x.1.L z m hw
  have hAg : Ag x.1.g x.1.L = ((hopB x.1.g : ℝ) : ℂ) • cycleAdj x.1.L := rfl
  have key := residual_identity W x.1.L (dysonMat (hopB x.1.g) β x.1.L z m) (Ag x.1.g x.1.L)
    (z + β * m) z m (β : ℂ) (by rw [hAg]; exact hMA) (by ring) (segG W x ω)
  have hdg := residual_blockTr_mul_diag W x.1.L (dysonMat (hopB x.1.g) β x.1.L z m)
    (fun c => blockTr (segG W x ω) c c - m) (segG W x ω) a b
  have key2 := congrArg (fun X => blockTr X a b) key
  simp only [residual_blockTr_sub, residual_blockTr_neg, residual_blockTr_add,
    residual_blockTr_smul] at key2
  rw [hdg, residual_blockTr_kron W x.1.L hW] at key2
  unfold segRes segM resComb
  rw [hseg]
  simp only [hdiag]
  rw [← hz]
  unfold resPi
  have hβc : ((x.1.u * gammaG x.1.g : ℝ) : ℂ) = (β : ℂ) := rfl
  rw [hβc]
  linear_combination key2

/-- A symmetric matrix with the first-coordinate free interpolation interpolates in both
coordinates, with particular term `d_{ab}` and error `(1 + 4/κ) δ`. -/
private lemma residual_M_interp {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (M : Matrix (Fin L) (Fin L) ℂ) (hMs : Mᵀ = M) (δ : ℝ)
    (hRI : RowInterp n E M δ) (a b : Fin L) :
    ‖M a b - ∑ α : Fin L, ∑ β : Fin L, ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * M α β -
        ((cellD n E a b : ℝ) : ℂ)‖ ≤ (1 + 4 / κ) * δ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hRI a a)
  set e : Fin L → Fin L → ℂ := fun x y =>
    M x y - (∑ α : Fin L, (cellCoef n E x α : ℂ) * M α y + (cellSrc n E x y : ℂ)) with he
  have hsym : ∀ x y, M x y = M y x := fun x y => by
    have := congrFun (congrFun hMs y) x
    rw [Matrix.transpose_apply] at this
    exact this
  have hcol : ∀ α, M α b - ∑ β, (cellCoef n E b β : ℂ) * M α β - (cellSrc n E b α : ℂ) =
      e b α := by
    intro α
    have h1 : ∑ β, (cellCoef n E b β : ℂ) * M α β = ∑ β, (cellCoef n E b β : ℂ) * M β α :=
      Finset.sum_congr rfl fun β _ => by rw [hsym α β]
    simp only [he]
    rw [h1, hsym α b]
    ring
  have hsum : ∑ α, ((cellCoef n E a α : ℝ) : ℂ) • e b α = ∑ α, (cellCoef n E a α : ℂ) *
      (M α b - ∑ β, (cellCoef n E b β : ℂ) * M α β - (cellSrc n E b α : ℂ)) :=
    Finset.sum_congr rfl fun α _ => by rw [hcol α, smul_eq_mul]
  have key : M a b - ∑ α : Fin L, ∑ β : Fin L,
      ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * M α β - ((cellD n E a b : ℝ) : ℂ) =
      ∑ α, ((cellCoef n E a α : ℝ) : ℂ) • e b α + e a b := by
    rw [hsum]
    simp only [he, cellD]
    push_cast
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
    ring
  rw [key]
  have h1 : ‖∑ α, ((cellCoef n E a α : ℝ) : ℂ) • e b α‖ ≤ 4 / κ * δ :=
    residual_single_le hκ hκ2 hE n (F := ℂ) a (fun α => e b α) δ hδ fun α _ => hRI b α
  calc _ ≤ ‖∑ α, ((cellCoef n E a α : ℝ) : ℂ) • e b α‖ + ‖e a b‖ := norm_add_le _ _
    _ ≤ 4 / κ * δ + δ := add_le_add h1 (hRI a b)
    _ = (1 + 4 / κ) * δ := by ring

/-- The anchor norm is at most the anchor envelope. -/
private lemma residual_anchorNorm_le (n : ℕ) {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    anchorNorm n G a b ≤ anchorEnv n G :=
  le_ciSup (f := fun ab : Fin L × Fin L => anchorNorm n G ab.1 ab.2)
    (Set.finite_range _).bddAbove (a, b)

private lemma residual_anchorEnv_nonneg (n : ℕ) {W L : ℕ} (hL : 1 ≤ L)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) : 0 ≤ anchorEnv n G := by
  have a : Fin L := ⟨0, by omega⟩
  exact (le_max_of_le_left (le_max_of_le_left (norm_nonneg _))).trans
    (residual_anchorNorm_le n G a a)

/-- The Remark (trace and entry envelopes) of Section 7.4 [sec:sampling-propagation-extensions],
deterministic form: the centered
block traces and the traceless entries interpolate through the anchor pairs, the particular terms
cancelling against those of a symmetric matrix `M` with the free interpolation. -/
theorem centered_interp (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W L n : ℕ) (E ε δ : ℝ) (z : ℂ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
      (M : Matrix (Fin L) (Fin L) ℂ), 1 ≤ W → 3 ≤ L → 1 ≤ n → |E| ≤ 2 - κ →
      (∀ r, (V r).IsHermitian) → z.im ≠ 0 → 0 ≤ ε → ε ≤ 1 → CellClose n E z V ε →
      CellClose n E (starRingEnd ℂ z) V ε → Mᵀ = M → RowInterp n E M δ →
      let G := resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V) z
      ∀ a b : Fin L,
        ‖blockTr G a b - M a b - ∑ α : Fin L, ∑ β : Fin L,
            ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * (blockTr G α β - M α β)‖ ≤
          C * (ε * (1 + anchorEnv n G) + δ) ∧
        ∀ i j : Fin W,
          ‖G (a, i) (b, j) - (if i = j then blockTr G a b else 0) -
              ∑ α : Fin L, ∑ β : Fin L, ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) *
                (G (α, i) (β, j) - if i = j then blockTr G α β else 0)‖ ≤
            C * ε * (1 + anchorEnv n G) := by
  obtain ⟨Cg, hCg, Hg⟩ := green_interp κ hκ hκ2
  have hκ4 : 0 < 4 / κ := by positivity
  refine ⟨max (2 * Cg) (Cg + (1 + 4 / κ)), lt_max_of_lt_left (by positivity), ?_⟩
  intro W L n E ε δ z V M hW hL hn hE hV hz hε0 hε1 hcl hcl' hMs hRI G a b
  have hgi := Hg W L n E ε z V hL hn hE hV hz hε0 hε1 hcl hcl' a b
  set A := anchorEnv n G with hA
  have hAab : anchorNorm n G a b ≤ A := residual_anchorNorm_le n G a b
  have hA0 : 0 ≤ A := residual_anchorEnv_nonneg n (by omega) G
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hRI a a)
  set X := blockOf G a b - interpBlock n E G a b with hX
  have hXn : ‖X‖ ≤ Cg * ε * (1 + A) :=
    hgi.trans (by gcongr)
  refine ⟨?_, fun i j => ?_⟩
  · have e1 : blockTr G a b - M a b - ∑ α : Fin L, ∑ β : Fin L,
        ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * (blockTr G α β - M α β) =
        residualNtr X - (M a b - ∑ α : Fin L, ∑ β : Fin L,
          ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * M α β - ((cellD n E a b : ℝ) : ℂ)) := by
      rw [hX, residual_ntr_interp hW]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e1]
    have h1 := (residual_ntr_le hW X).trans hXn
    have h2 := residual_M_interp hκ hκ2 hE n M hMs δ hRI a b
    calc _ ≤ ‖residualNtr X‖ + ‖M a b - ∑ α : Fin L, ∑ β : Fin L,
          ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * M α β - ((cellD n E a b : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ Cg * ε * (1 + A) + (1 + 4 / κ) * δ := add_le_add h1 h2
      _ ≤ max (2 * Cg) (Cg + (1 + 4 / κ)) * (ε * (1 + A) + δ) := by
          have hm1 : Cg ≤ max (2 * Cg) (Cg + (1 + 4 / κ)) :=
            le_trans (by linarith) (le_max_right _ _)
          have hm2 : 1 + 4 / κ ≤ max (2 * Cg) (Cg + (1 + 4 / κ)) :=
            le_trans (by linarith) (le_max_right _ _)
          have hεA : 0 ≤ ε * (1 + A) := by positivity
          nlinarith
  · have e2 : G (a, i) (b, j) - (if i = j then blockTr G a b else 0) -
        ∑ α : Fin L, ∑ β : Fin L, ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) *
          (G (α, i) (β, j) - if i = j then blockTr G α β else 0) =
        X i j - if i = j then residualNtr X else 0 := by
      rw [hX, residual_entry_interp, residual_ntr_interp hW]
      split_ifs
      · simp only [mul_sub, Finset.sum_sub_distrib]; ring
      · simp only [sub_zero]
    rw [e2]
    have h1 := residual_entry_le X i j
    have h2 := residual_ntr_le hW X
    have h3 : ‖(if i = j then residualNtr X else 0)‖ ≤ ‖X‖ := by
      split_ifs
      · exact h2
      · simp
    calc _ ≤ ‖X i j‖ + ‖(if i = j then residualNtr X else 0)‖ := norm_sub_le _ _
      _ ≤ ‖X‖ + ‖X‖ := add_le_add h1 h3
      _ ≤ 2 * (Cg * ε * (1 + A)) := by linarith
      _ ≤ max (2 * Cg) (Cg + (1 + 4 / κ)) * ε * (1 + A) := by
          have hm : 2 * Cg ≤ max (2 * Cg) (Cg + (1 + 4 / κ)) := le_max_left _ _
          have : 0 ≤ ε * (1 + A) := by positivity
          nlinarith

/-- Under the hypotheses of Proposition 7.4 [uvc:prop:green], every Green block is at most
`K₁ (1 + 𝒢)`, `K₁ = (4/κ)² + 2/κ + 8/κ² + C`. -/
private lemma residual_block_le {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) {Cg : ℝ} (hCg : 0 < Cg)
    {W L n : ℕ} {E ε : ℝ} (hE : |E| ≤ 2 - κ) (hε1 : ε ≤ 1)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hgi : ∀ a b : Fin L, ‖blockOf G a b - interpBlock n E G a b‖ ≤
      Cg * ε * (1 + anchorNorm n G a b)) (c b : Fin L) :
    ‖blockOf G c b‖ ≤ ((4 / κ) ^ 2 + (2 / κ + 8 / κ ^ 2) + Cg) * (1 + anchorEnv n G) := by
  have hA0 : 0 ≤ anchorEnv n G :=
    (le_max_of_le_left (le_max_of_le_left (norm_nonneg _))).trans
      (residual_anchorNorm_le n G c b)
  have hAcb := residual_anchorNorm_le n G c b
  have h1 : ‖∑ α, ∑ β, ((cellCoef n E c α * cellCoef n E b β : ℝ) : ℂ) • blockOf G α β‖ ≤
      (4 / κ) ^ 2 * anchorEnv n G :=
    residual_double_le hκ hκ2 hE n c b (fun α β => blockOf G α β) _ hA0
      fun α β hα hβ => (residualT_anchor_le n G c b α β hα hβ).trans hAcb
  have h2 : ‖((cellD n E c b : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 2 / κ + 8 / κ ^ 2 :=
    (residualT_norm_smul_one_le _).trans (by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact residual_cellD_le hκ hκ2 hE n c b)
  have hN0 : 0 ≤ anchorNorm n G c b := le_max_of_le_left (le_max_of_le_left (norm_nonneg _))
  have h3 : ‖blockOf G c b - interpBlock n E G c b‖ ≤ Cg * (1 + anchorEnv n G) := by
    refine (hgi c b).trans ?_
    have : Cg * ε ≤ Cg := by nlinarith
    exact mul_le_mul this (by linarith) (by linarith) hCg.le
  have e : blockOf G c b = (blockOf G c b - interpBlock n E G c b) +
      (∑ α, ∑ β, ((cellCoef n E c α * cellCoef n E b β : ℝ) : ℂ) • blockOf G α β +
        ((cellD n E c b : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) := by
    unfold interpBlock; abel
  rw [e]
  have hκ' : 0 < 4 / κ := by positivity
  calc _ ≤ ‖blockOf G c b - interpBlock n E G c b‖ +
        (‖∑ α, ∑ β, ((cellCoef n E c α * cellCoef n E b β : ℝ) : ℂ) • blockOf G α β‖ +
          ‖((cellD n E c b : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ Cg * (1 + anchorEnv n G) + ((4 / κ) ^ 2 * anchorEnv n G + (2 / κ + 8 / κ ^ 2)) :=
        add_le_add h3 (add_le_add h1 h2)
    _ ≤ _ := by
        have : 0 ≤ 2 / κ + 8 / κ ^ 2 := by positivity
        nlinarith [sq_nonneg (4 / κ)]

/-- Second-coordinate interpolation of the block traces, from the first-coordinate identity for
`G^* = (H - z̄)⁻¹`. -/
private lemma residual_trace_col {W L n : ℕ} (hW : 1 ≤ W) (hL : 2 ≤ L) (hn : 1 ≤ n) {E ε : ℝ}
    (hE : |E| < 2) (hε : 0 ≤ ε) (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (z : ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hG' : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
        (starRingEnd ℂ z) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * Gᴴ = 1)
    (hcl' : CellClose n E (starRingEnd ℂ z) V ε) (c b : Fin L) :
    ‖blockTr G c b - ∑ β, ((cellCoef n E b β : ℝ) : ℂ) * blockTr G c β -
        ((cellSrc n E b c : ℝ) : ℂ)‖ ≤
      ε * (1 + ‖blockOf G c (cellStart n b)‖ + ‖blockOf G c (cellPrev n b)‖) := by
  have h1 := residualT_rem_op hL hn hE hε V _ Gᴴ hG' hcl' b c
  rw [residualT_blockOf_conjTranspose, residualT_blockOf_conjTranspose,
    Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h1
  have h2 := residualT_adj n E G b c
  have e : blockTr G c b - ∑ β, ((cellCoef n E b β : ℝ) : ℂ) * blockTr G c β -
      ((cellSrc n E b c : ℝ) : ℂ) = residualNtr (blockOf G c b -
        (∑ β, ((cellCoef n E b β : ℝ) : ℂ) • blockOf G c β) -
        ((cellSrc n E b c : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) := by
    simp only [residual_ntr_sub, residual_ntr_sum, residual_ntr_smul, residual_ntr_one hW,
      residual_ntr_blockOf, mul_one]
  rw [e, h2]
  refine (residual_ntr_le hW _).trans ?_
  rw [Matrix.l2_opNorm_conjTranspose]
  exact h1

/-- The algebra of the residual combination: the first-coordinate interpolation of `M` and the
second-coordinate interpolation of the block traces. -/
private lemma residual_decomp_K {L : ℕ} (w M T t : Fin L → Fin L → ℂ) (a b : Fin L) :
    (∑ c, M a c * T c c * t c b) - ∑ α, ∑ α', (w a α * w b α') * ∑ c, M α c * T c c * t c α' =
      ∑ c, (M a c - ∑ α, w a α * M α c) * T c c * t c b +
        ∑ α, w a α * ∑ c, M α c * T c c * (t c b - ∑ α', w b α' * t c α') := by
  have e1 : ∑ c, (M a c - ∑ α, w a α * M α c) * T c c * t c b =
      ∑ c, M a c * T c c * t c b - ∑ α, w a α * ∑ c, M α c * T c c * t c b := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun c _ => by ring
  have e2 : ∑ α, w a α * ∑ c, M α c * T c c * (t c b - ∑ α', w b α' * t c α') =
      ∑ α, w a α * ∑ c, M α c * T c c * t c b -
        ∑ α, ∑ α', (w a α * w b α') * ∑ c, M α c * T c c * t c α' := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α' _ => Finset.sum_congr rfl fun c _ => by ring
  rw [e1, e2]
  ring

/-- Proposition 7.10 [uvc:prop:residual-compression], deterministic form: `resComb` interpolates
through the anchor pairs with error `C (1 + Γ)² (1 + 𝒢)² (ε + δ(1 + βL) + βn)`. -/
theorem residual_interp (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W L n : ℕ) (E ε δ β Γ : ℝ) (z : ℂ)
      (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (M : Matrix (Fin L) (Fin L) ℂ), 1 ≤ W → 3 ≤ L →
      1 ≤ n → |E| ≤ 2 - κ → (∀ r, (V r).IsHermitian) → z.im ≠ 0 → 0 ≤ ε → ε ≤ 1 → 0 ≤ δ →
      0 ≤ β → CellClose n E z V ε → CellClose n E (starRingEnd ℂ z) V ε → Mᵀ = M →
      RowInterp n E M δ → (∀ a b, ‖M a b‖ ≤ Γ) → (∀ a, β * ∑ b, ‖M a b‖ ≤ Γ) →
      let G := resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V) z
      ∀ a b : Fin L,
        ‖resComb β G M a b - ∑ α : Fin L, ∑ α' : Fin L,
            ((cellCoef n E a α * cellCoef n E b α' : ℝ) : ℂ) * resComb β G M α α'‖ ≤
          C * (1 + Γ) ^ 2 * (1 + anchorEnv n G) ^ 2 * (ε + δ * (1 + β * L) + β * n) := by
  obtain ⟨Cg, hCg, Hg⟩ := green_interp κ hκ hκ2
  obtain ⟨Cc, hCc, Hc⟩ := centered_interp κ hκ hκ2
  set K : ℝ := 2 / κ with hK
  have hK0 : 0 < K := by positivity
  set K₁ : ℝ := (4 / κ) ^ 2 + (2 / κ + 8 / κ ^ 2) + Cg with hK₁
  have hK₁0 : 0 < K₁ := by positivity
  set K₂ : ℝ := K₁ + 1 with hK₂
  set C : ℝ := Cc + K * K₂ * K₁ + K₂ * K₁ + 4 / κ * K * K₂ + 4 / κ * (1 + 2 * K₁) * K₂ with hC
  have hC0 : 0 < C := by positivity
  have hK₂0 : 0 < K₂ := by positivity
  have hκ4 : 0 ≤ 4 / κ := by positivity
  clear_value K K₁ K₂ C
  refine ⟨C, hC0, ?_⟩
  intro W L n E ε δ β Γ z V M hW hL hn hE hV hz hε0 hε1 hδ0 hβ0 hcl hcl' hMs hRI hMe hMr G a b
  have hL2 : 2 ≤ L := by omega
  have hE' : |E| < 2 := by linarith
  have hHerm := residualT_op_isHermitian hV
  have hz' : (starRingEnd ℂ z).im ≠ 0 := by simpa using hz
  have hG' : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
      (starRingEnd ℂ z) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * Gᴴ = 1 := by
    rw [← residualT_resolvent_conj hV]
    exact sub_smul_mul_resolventMat hHerm hz'
  set A := anchorEnv n G with hA
  have hA0 : 0 ≤ A := residual_anchorEnv_nonneg n (by omega) G
  have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans (hMe a a)
  have hgi := Hg W L n E ε z V hL hn hE hV hz hε0 hε1 hcl hcl'
  set BG : ℝ := K₁ * (1 + A) with hBG
  have hBG0 : 0 ≤ BG := by positivity
  have hblk : ∀ c b, ‖blockOf G c b‖ ≤ BG := fun c b => by
    rw [hBG, hK₁]; exact residual_block_le hκ hκ2 hCg hE hε1 G hgi c b
  have ht : ∀ c b, ‖blockTr G c b‖ ≤ BG := fun c b =>
    (residual_ntr_le hW (blockOf G c b)).trans (hblk c b)
  set BT : ℝ := BG + Γ with hBT
  have hBT0 : 0 ≤ BT := by positivity
  have hT : ∀ c b, ‖blockTr G c b - M c b‖ ≤ BT := fun c b =>
    (norm_sub_le _ _).trans (add_le_add (ht c b) (hMe c b))
  have hetr : ∀ c b, ‖blockTr G c b - ∑ β, ((cellCoef n E b β : ℝ) : ℂ) * blockTr G c β‖ ≤
      |cellSrc n E b c| + ε * (1 + 2 * BG) := by
    intro c b
    have h := residual_trace_col hW hL2 hn hE' hε0 V z G hG' hcl' c b
    have h1 := hblk c (cellStart n b)
    have h2 := hblk c (cellPrev n b)
    have h3 : ε * (1 + ‖blockOf G c (cellStart n b)‖ + ‖blockOf G c (cellPrev n b)‖) ≤
        ε * (1 + 2 * BG) := by
      apply mul_le_mul_of_nonneg_left _ hε0; linarith
    calc _ = ‖(blockTr G c b - ∑ β, ((cellCoef n E b β : ℝ) : ℂ) * blockTr G c β -
          ((cellSrc n E b c : ℝ) : ℂ)) + ((cellSrc n E b c : ℝ) : ℂ)‖ := by ring_nf
      _ ≤ _ := by
          refine (norm_add_le _ _).trans ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
          linarith
  have heM : ∀ a c, ‖M a c - ∑ α, ((cellCoef n E a α : ℝ) : ℂ) * M α c‖ ≤
      |cellSrc n E a c| + δ := by
    intro a c
    have h := hRI a c
    calc _ = ‖(M a c - (∑ α, ((cellCoef n E a α : ℝ) : ℂ) * M α c + (cellSrc n E a c : ℂ))) +
          ((cellSrc n E a c : ℝ) : ℂ)‖ := by ring_nf
      _ ≤ _ := by
          refine (norm_add_le _ _).trans ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
          linarith
  have hcen := (Hc W L n E ε δ z V M hW hL hn hE hV hz hε0 hε1 hcl hcl' hMs hRI a b).1
  -- the decomposition of the residual combination
  set w : Fin L → Fin L → ℂ := fun x α => ((cellCoef n E x α : ℝ) : ℂ) with hw
  set P1 : ℂ := ∑ c, (M a c - ∑ α, w a α * M α c) * (blockTr G c c - M c c) * blockTr G c b
    with hP1
  set Y : Fin L → ℂ := fun α => ∑ c, M α c * (blockTr G c c - M c c) *
    (blockTr G c b - ∑ α', w b α' * blockTr G c α') with hY
  have hdec : resComb β G M a b - ∑ α : Fin L, ∑ α' : Fin L,
      ((cellCoef n E a α * cellCoef n E b α' : ℝ) : ℂ) * resComb β G M α α' =
      -(blockTr G a b - M a b - ∑ α : Fin L, ∑ β' : Fin L,
        ((cellCoef n E a α * cellCoef n E b β' : ℝ) : ℂ) * (blockTr G α β' - M α β')) +
      (β : ℂ) * P1 + ∑ α, ((cellCoef n E a α : ℝ) : ℂ) • ((β : ℂ) * Y α) := by
    have hK := residual_decomp_K w M (fun x y => blockTr G x y - M x y)
      (fun x y => blockTr G x y) a b
    have hsm : ∑ α, ((cellCoef n E a α : ℝ) : ℂ) • ((β : ℂ) * Y α) =
        (β : ℂ) * ∑ α, w a α * Y α := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [smul_eq_mul]; ring
    rw [hsm]
    unfold resComb
    have hcast : ∀ α α', ((cellCoef n E a α * cellCoef n E b α' : ℝ) : ℂ) = w a α * w b α' :=
      fun α α' => by push_cast; rfl
    simp only [hcast]
    have hsplit : ∑ α : Fin L, ∑ α' : Fin L, w a α * w b α' *
        (-(blockTr G α α' - M α α') + (β : ℂ) * ∑ c, M α c * (blockTr G c c - M c c) *
          blockTr G c α') =
        -(∑ α : Fin L, ∑ α' : Fin L, w a α * w b α' * (blockTr G α α' - M α α')) +
          (β : ℂ) * ∑ α : Fin L, ∑ α' : Fin L, w a α * w b α' *
            ∑ c, M α c * (blockTr G c c - M c c) * blockTr G c α' := by
      simp only [mul_add, Finset.sum_add_distrib, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun α' _ =>
        Finset.sum_congr rfl fun c _ => by ring
    rw [hsplit]
    have hK' : (∑ c, M a c * (blockTr G c c - M c c) * blockTr G c b) =
        ∑ α : Fin L, ∑ α' : Fin L, w a α * w b α' *
          ∑ c, M α c * (blockTr G c c - M c c) * blockTr G c α' + (P1 + ∑ α, w a α * Y α) := by
      rw [← hK]; ring
    rw [hK']
    ring
  rw [hdec]
  -- the three bounds
  have hP1b : ‖P1‖ ≤ ((n : ℝ) * K + L * δ) * BT * BG := by
    calc ‖P1‖ ≤ ∑ c, ‖(M a c - ∑ α, w a α * M α c) * (blockTr G c c - M c c) *
          blockTr G c b‖ := norm_sum_le _ _
      _ ≤ ∑ c, (|cellSrc n E a c| + δ) * BT * BG := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul (heM a c) (hT c c) (norm_nonneg _)
            (add_nonneg (abs_nonneg _) hδ0)) (ht c b) (norm_nonneg _)
            (mul_nonneg (add_nonneg (abs_nonneg _) hδ0) hBT0)
      _ = ((∑ c, |cellSrc n E a c|) + L * δ) * BT * BG := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_add_distrib]
          simp
      _ ≤ ((n : ℝ) * K + L * δ) * BT * BG := by
          have : ∑ c, |cellSrc n E a c| ≤ n * K := by
            rw [hK]; exact residual_sum_src_le hκ hκ2 hE n hn a
          gcongr
  set Y₀ : ℝ := β * BT * Γ * ((n : ℝ) * K) + BT * (ε * (1 + 2 * BG)) * Γ with hY₀
  have hY₀0 : 0 ≤ Y₀ := by positivity
  have hYb : ∀ α, ‖(β : ℂ) * Y α‖ ≤ Y₀ := by
    intro α
    have h1 : ‖Y α‖ ≤ ∑ c, ‖M α c‖ * BT * (|cellSrc n E b c| + ε * (1 + 2 * BG)) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
      rw [norm_mul, norm_mul]
      gcongr
      · exact hT c c
      · exact hetr c b
    have h2 : ∑ c, ‖M α c‖ * BT * (|cellSrc n E b c| + ε * (1 + 2 * BG)) ≤
        Γ * BT * ((n : ℝ) * K) + (∑ c, ‖M α c‖) * BT * (ε * (1 + 2 * BG)) := by
      have e : ∑ c, ‖M α c‖ * BT * (|cellSrc n E b c| + ε * (1 + 2 * BG)) =
          BT * ∑ c, ‖M α c‖ * |cellSrc n E b c| + (∑ c, ‖M α c‖) * BT * (ε * (1 + 2 * BG)) := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => by ring
      rw [e]
      have h3 : ∑ c, ‖M α c‖ * |cellSrc n E b c| ≤ Γ * ((n : ℝ) * K) := by
        calc ∑ c, ‖M α c‖ * |cellSrc n E b c| ≤ ∑ c, Γ * |cellSrc n E b c| :=
              Finset.sum_le_sum fun c _ =>
                mul_le_mul_of_nonneg_right (hMe α c) (abs_nonneg _)
          _ = Γ * ∑ c, |cellSrc n E b c| := by rw [Finset.mul_sum]
          _ ≤ Γ * ((n : ℝ) * K) :=
              mul_le_mul_of_nonneg_left (by rw [hK]; exact residual_sum_src_le hκ hκ2 hE n hn b)
                hΓ0
      have := mul_le_mul_of_nonneg_left h3 hBT0
      linarith
    have hr := hMr α
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ0]
    calc β * ‖Y α‖ ≤ β * (Γ * BT * ((n : ℝ) * K) + (∑ c, ‖M α c‖) * BT * (ε * (1 + 2 * BG))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hβ0
      _ = β * BT * Γ * ((n : ℝ) * K) + (β * ∑ c, ‖M α c‖) * (BT * (ε * (1 + 2 * BG))) := by
          ring
      _ ≤ Y₀ := by
          rw [hY₀]
          have h0 : 0 ≤ BT * (ε * (1 + 2 * BG)) := by positivity
          have := mul_le_mul_of_nonneg_right hr h0
          linarith
  have hP2b : ‖∑ α, ((cellCoef n E a α : ℝ) : ℂ) • ((β : ℂ) * Y α)‖ ≤ 4 / κ * Y₀ :=
    residual_single_le hκ hκ2 hE n (F := ℂ) a _ Y₀ hY₀0 fun α _ => hYb α
  have hβP1 : ‖(β : ℂ) * P1‖ ≤ β * (((n : ℝ) * K + L * δ) * BT * BG) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left hP1b hβ0
  -- the final count
  set P : ℝ := (1 + Γ) * (1 + A) with hP
  have hA1 : 1 + A ≤ P := by
    rw [hP]
    calc 1 + A = 1 * (1 + A) := (one_mul _).symm
      _ ≤ (1 + Γ) * (1 + A) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hΓ1 : 1 + Γ ≤ P := by
    rw [hP]
    calc 1 + Γ = (1 + Γ) * 1 := (mul_one _).symm
      _ ≤ (1 + Γ) * (1 + A) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hP1' : 1 ≤ P := le_trans (by linarith) hA1
  clear_value P BG BT Y₀
  have hP0 : 0 ≤ P := by linarith
  have hBGP : BG ≤ K₁ * P := by rw [hBG]; exact mul_le_mul_of_nonneg_left hA1 hK₁0.le
  have hBTP : BT ≤ K₂ * P := by
    rw [hBT, hK₂, add_mul, one_mul]
    have : Γ ≤ P := by linarith
    linarith
  have hQ : P ≤ P ^ 2 := by
    calc P = P * 1 := (mul_one _).symm
      _ ≤ P * P := mul_le_mul_of_nonneg_left hP1' (by linarith)
      _ = P ^ 2 := (sq P).symm
  have hcen' : ‖blockTr G a b - M a b - ∑ α : Fin L, ∑ β' : Fin L,
      ((cellCoef n E a α * cellCoef n E b β' : ℝ) : ℂ) * (blockTr G α β' - M α β')‖ ≤
      Cc * P ^ 2 * ε + Cc * P ^ 2 * δ := by
    refine hcen.trans ?_
    have h1 : ε * (1 + A) ≤ ε * P ^ 2 := mul_le_mul_of_nonneg_left (hA1.trans hQ) hε0
    have h2 : δ ≤ δ * P ^ 2 := le_mul_of_one_le_right hδ0 (one_le_pow₀ hP1')
    have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCc.le
    linarith
  have hterm2 : β * (((n : ℝ) * K + L * δ) * BT * BG) ≤
      K₂ * K₁ * K * P ^ 2 * (β * n) + K₂ * K₁ * P ^ 2 * (β * L * δ) := by
    have h1 : BT * BG ≤ K₂ * K₁ * P ^ 2 := by
      calc BT * BG ≤ (K₂ * P) * (K₁ * P) := mul_le_mul hBTP hBGP hBG0 (mul_nonneg hK₂0.le hP0)
        _ = K₂ * K₁ * P ^ 2 := by ring
    have h0 : 0 ≤ β * ((n : ℝ) * K + L * δ) := by positivity
    calc β * (((n : ℝ) * K + L * δ) * BT * BG) = β * ((n : ℝ) * K + L * δ) * (BT * BG) := by ring
      _ ≤ β * ((n : ℝ) * K + L * δ) * (K₂ * K₁ * P ^ 2) := mul_le_mul_of_nonneg_left h1 h0
      _ = _ := by ring
  have hterm3 : 4 / κ * Y₀ ≤ 4 / κ * K * K₂ * P ^ 2 * (β * n) +
      4 / κ * (1 + 2 * K₁) * K₂ * P ^ 2 * ε := by
    have h1 : BT * Γ ≤ K₂ * P ^ 2 := by
      calc BT * Γ ≤ (K₂ * P) * P := mul_le_mul hBTP (by linarith) hΓ0 (mul_nonneg hK₂0.le hP0)
        _ = K₂ * P ^ 2 := by ring
    have h2 : BT * (1 + 2 * BG) * Γ ≤ (1 + 2 * K₁) * K₂ * P ^ 2 := by
      have e1 : 1 + 2 * BG ≤ (1 + 2 * K₁) * (1 + A) := by
        have : (1 + 2 * K₁) * (1 + A) = (1 + A) + 2 * (K₁ * (1 + A)) := by ring
        rw [this, hBG]; linarith
      have e2 : BT * Γ * (1 + A) ≤ K₂ * P ^ 2 := by
        have ex : (1 + Γ) ^ 2 = 1 + 2 * Γ + Γ ^ 2 := by ring
        have f1 : Γ ≤ (1 + Γ) ^ 2 := by rw [ex]; linarith [sq_nonneg Γ]
        have f2 : Γ ^ 2 ≤ (1 + Γ) ^ 2 := by rw [ex]; linarith
        have f3 : 1 + A ≤ (1 + A) ^ 2 := by
          calc 1 + A = (1 + A) * 1 := by ring
            _ ≤ (1 + A) * (1 + A) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
            _ = (1 + A) ^ 2 := by ring
        have g1 : K₁ * Γ * (1 + A) ^ 2 ≤ K₁ * (1 + Γ) ^ 2 * (1 + A) ^ 2 := by
          have := mul_le_mul_of_nonneg_left f1 hK₁0.le
          exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
        have g2 : Γ ^ 2 * (1 + A) ≤ (1 + Γ) ^ 2 * (1 + A) ^ 2 :=
          mul_le_mul f2 f3 (by linarith) (sq_nonneg _)
        have e : BT * Γ * (1 + A) = K₁ * Γ * (1 + A) ^ 2 + Γ ^ 2 * (1 + A) := by
          rw [hBT, hBG]; ring
        have e' : K₂ * P ^ 2 = K₁ * (1 + Γ) ^ 2 * (1 + A) ^ 2 + (1 + Γ) ^ 2 * (1 + A) ^ 2 := by
          rw [hK₂, hP]; ring
        rw [e, e']
        linarith
      calc BT * (1 + 2 * BG) * Γ = BT * Γ * (1 + 2 * BG) := by ring
        _ ≤ BT * Γ * ((1 + 2 * K₁) * (1 + A)) :=
            mul_le_mul_of_nonneg_left e1 (by positivity)
        _ = (1 + 2 * K₁) * (BT * Γ * (1 + A)) := by ring
        _ ≤ (1 + 2 * K₁) * (K₂ * P ^ 2) := mul_le_mul_of_nonneg_left e2 (by positivity)
        _ = _ := by ring
    have hY₀' : Y₀ ≤ K * K₂ * P ^ 2 * (β * n) + (1 + 2 * K₁) * K₂ * P ^ 2 * ε := by
      rw [hY₀]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      calc β * BT * Γ * ((n : ℝ) * K) + BT * (ε * (1 + 2 * BG)) * Γ =
          (β * n * K) * (BT * Γ) + ε * (BT * (1 + 2 * BG) * Γ) := by ring
        _ ≤ (β * n * K) * (K₂ * P ^ 2) + ε * ((1 + 2 * K₁) * K₂ * P ^ 2) := by
            gcongr
        _ = _ := by ring
    have : 0 ≤ 4 / κ := by positivity
    calc 4 / κ * Y₀ ≤ 4 / κ * (K * K₂ * P ^ 2 * (β * n) + (1 + 2 * K₁) * K₂ * P ^ 2 * ε) :=
          mul_le_mul_of_nonneg_left hY₀' this
      _ = _ := by ring
  have hfin : Cc * P ^ 2 * ε + Cc * P ^ 2 * δ +
      (K₂ * K₁ * K * P ^ 2 * (β * n) + K₂ * K₁ * P ^ 2 * (β * L * δ)) +
      (4 / κ * K * K₂ * P ^ 2 * (β * n) + 4 / κ * (1 + 2 * K₁) * K₂ * P ^ 2 * ε) ≤
      C * (1 + Γ) ^ 2 * (1 + A) ^ 2 * (ε + δ * (1 + β * L) + β * n) := by
    have hPP : (1 + Γ) ^ 2 * (1 + A) ^ 2 = P ^ 2 := by rw [hP]; ring
    have hQ0 : 0 ≤ P ^ 2 := sq_nonneg _
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have v1 : 0 ≤ P ^ 2 * ε := mul_nonneg hQ0 hε0
    have v2 : 0 ≤ P ^ 2 * δ := mul_nonneg hQ0 hδ0
    have v3 : 0 ≤ P ^ 2 * (β * n) := mul_nonneg hQ0 (mul_nonneg hβ0 hn0)
    have v4 : 0 ≤ P ^ 2 * (β * L * δ) := mul_nonneg hQ0 (mul_nonneg (mul_nonneg hβ0 hL0) hδ0)
    have c0 : 0 ≤ K * K₂ * K₁ := mul_nonneg (mul_nonneg hK0.le hK₂0.le) hK₁0.le
    have c1 : 0 ≤ K₂ * K₁ := mul_nonneg hK₂0.le hK₁0.le
    have c3 : 0 ≤ 4 / κ * (1 + 2 * K₁) * K₂ :=
      mul_nonneg (mul_nonneg hκ4 (by linarith)) hK₂0.le
    have c2 : 0 ≤ 4 / κ * K * K₂ := mul_nonneg (mul_nonneg hκ4 hK0.le) hK₂0.le
    have hCe : Cc + 4 / κ * (1 + 2 * K₁) * K₂ ≤ C := by rw [hC]; linarith
    have hCd : Cc ≤ C := by rw [hC]; linarith
    have hCl : K₂ * K₁ ≤ C := by rw [hC]; linarith
    have hCn : K₂ * K₁ * K + 4 / κ * K * K₂ ≤ C := by
      have : K₂ * K₁ * K = K * K₂ * K₁ := by ring
      rw [hC, this]; linarith
    have t1 := mul_le_mul_of_nonneg_right hCe v1
    have t2 := mul_le_mul_of_nonneg_right hCd v2
    have t3 := mul_le_mul_of_nonneg_right hCl v4
    have t4 := mul_le_mul_of_nonneg_right hCn v3
    rw [mul_assoc C, hPP]
    have ex : C * P ^ 2 * (ε + δ * (1 + β * L) + β * n) =
        C * (P ^ 2 * ε) + C * (P ^ 2 * δ) + C * (P ^ 2 * (β * L * δ)) + C * (P ^ 2 * (β * n)) := by
      ring
    rw [ex]
    have ex2 : Cc * P ^ 2 * ε + Cc * P ^ 2 * δ +
        (K₂ * K₁ * K * P ^ 2 * (β * n) + K₂ * K₁ * P ^ 2 * (β * L * δ)) +
        (4 / κ * K * K₂ * P ^ 2 * (β * n) + 4 / κ * (1 + 2 * K₁) * K₂ * P ^ 2 * ε) =
        (Cc + 4 / κ * (1 + 2 * K₁) * K₂) * (P ^ 2 * ε) + Cc * (P ^ 2 * δ) +
          K₂ * K₁ * (P ^ 2 * (β * L * δ)) + (K₂ * K₁ * K + 4 / κ * K * K₂) * (P ^ 2 * (β * n)) := by
      ring
    rw [ex2]
    linarith
  calc _ ≤ ‖-(blockTr G a b - M a b - ∑ α : Fin L, ∑ β' : Fin L,
        ((cellCoef n E a α * cellCoef n E b β' : ℝ) : ℂ) * (blockTr G α β' - M α β'))‖ +
        ‖(β : ℂ) * P1‖ + ‖∑ α, ((cellCoef n E a α : ℝ) : ℂ) • ((β : ℂ) * Y α)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (Cc * P ^ 2 * ε + Cc * P ^ 2 * δ) +
        (K₂ * K₁ * K * P ^ 2 * (β * n) + K₂ * K₁ * P ^ 2 * (β * L * δ)) +
        (4 / κ * K * K₂ * P ^ 2 * (β * n) + 4 / κ * (1 + 2 * K₁) * K₂ * P ^ 2 * ε) := by
        rw [norm_neg]
        exact add_le_add (add_le_add hcen' (hβP1.trans hterm2)) (hP2b.trans hterm3)
    _ ≤ _ := hfin

/-- The decay factor is nonzero and `w = b (ρ + ρ⁻¹)`, (A.4) [da:eq:free-decay-factor]. -/
private lemma residualK_freeRho_aux (b : ℝ) (hb : 0 < b) (w : ℂ) (hw : 0 < w.im) :
    freeRho b w ≠ 0 ∧ w = b * (freeRho b w + (freeRho b w)⁻¹) := by
  have hs2 := freeS_sq b w
  have him : 0 < (w + freeS b w).im := by
    rw [Complex.add_im]; linarith [freeS_im_pos b w hw]
  have hne : w + freeS b w ≠ 0 := by
    intro h; rw [h] at him; simp at him
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have h2b : (2 * (b : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hb'
  refine ⟨?_, ?_⟩
  · unfold freeRho
    exact div_ne_zero h2b hne
  · unfold freeRho
    rw [inv_div]
    field_simp
    linear_combination (-1 : ℂ) * hs2


/-- Three-term recurrence of the sine. -/
private lemma residualK_sin_step (x ϑ : ℝ) :
    Real.sin (x + ϑ) = 2 * Real.cos ϑ * Real.sin x - Real.sin (x - ϑ) := by
  rw [Real.sin_add, Real.sin_sub]
  ring

private lemma residualK_fin_val_add_one {n : ℕ} (a : Fin (n + 1)) :
    ((a + 1 : Fin (n + 1)) : ℕ) = (a.val + 1) % (n + 1) := by
  rw [Fin.val_add]; simp [Nat.add_mod]

/-- The cycle adjacency matrix in terms of the group structure of `Fin (n + 1)`. -/
private lemma residualK_cycleAdj_fin {n : ℕ} (a b : Fin (n + 1)) :
    cycleAdj (n + 1) a b = (if b = a + 1 then 1 else 0) + (if a = b + 1 then 1 else 0) := by
  unfold cycleAdj
  simp only [Matrix.of_apply]
  have h1 : (b.val = (a.val + 1) % (n + 1)) ↔ b = a + 1 := by
    rw [Fin.ext_iff, residualK_fin_val_add_one]
  have h2 : (a.val = (b.val + 1) % (n + 1)) ↔ a = b + 1 := by
    rw [Fin.ext_iff, residualK_fin_val_add_one]
  rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl]

private lemma residualK_cycleAdj_add {n : ℕ} (τ a b : Fin (n + 1)) :
    cycleAdj (n + 1) (a + τ) (b + τ) = cycleAdj (n + 1) a b := by
  rw [residualK_cycleAdj_fin, residualK_cycleAdj_fin]
  have e1 : (b + τ = a + τ + 1) ↔ b = a + 1 := by
    rw [add_right_comm a τ 1]; exact add_left_inj τ
  have e2 : (a + τ = b + τ + 1) ↔ a = b + 1 := by
    rw [add_right_comm b τ 1]; exact add_left_inj τ
  simp only [e1, e2]

/-- The inverse of a circulant is translation invariant. -/
private lemma residualK_inv_add_invariant {n : ℕ} (w : ℂ) (τ a b : Fin (n + 1)) :
    ((cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹) (a + τ) (b + τ) =
    ((cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹) a b := by
  set A' := cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) with hA'
  have h : A'.submatrix (Equiv.addRight τ) (Equiv.addRight τ) = A' := by
    ext x y
    simp [hA', Matrix.one_apply, residualK_cycleAdj_add]
  have := Matrix.inv_submatrix_equiv A' (Equiv.addRight τ) (Equiv.addRight τ)
  rw [h] at this
  exact (congrFun (congrFun this a) b).symm

/-- Row relation of a right inverse of `A_L - w`: `M(a+1, b) + M(a-1, b) - w M(a, b) = δ_{ab}`. -/
private lemma residualK_matrix_rec {n : ℕ} (w : ℂ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hM : (cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) * M = 1)
    (a b : Fin (n + 1)) :
    M (a + 1) b + M (a - 1) b - w * M a b = if a = b then 1 else 0 := by
  have h := congrFun (congrFun hM a) b
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, residualK_cycleAdj_fin] at h
  have s1 : ∑ k, (if k = a + 1 then (1 : ℂ) else 0) * M k b = M (a + 1) b := by simp
  have s2 : ∑ k, (if a = k + 1 then (1 : ℂ) else 0) * M k b = M (a - 1) b := by
    rw [Finset.sum_eq_single (a - 1)]
    · simp
    · intro k _ hk
      have : a ≠ k + 1 := by
        intro h'; apply hk; rw [h']; simp
      simp [this]
    · simp
  have s3 : ∑ k, w * (if a = k then (1 : ℂ) else 0) * M k b = w * M a b := by simp
  simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib] at h
  rw [s1, s2, s3] at h
  exact h

/-- Variation of constants for the three-term recurrence `X(i+2) = E X(i+1) - X(i) + f(i)`, with the
fundamental solution `V` (`V 0 = 0`, `V 1 = 1`, `V (t+1) = E V t - V (t-1)`). -/
private lemma residualK_duhamel_formula (V : ℝ → ℝ) (E : ℝ) (hV0 : V 0 = 0) (hV1 : V 1 = 1)
    (hV : ∀ t, V (t + 1) = E * V t - V (t - 1)) (X f : ℕ → ℂ)
    (hX : ∀ i, X (i + 2) = (E : ℂ) * X (i + 1) - X i + f i) (j : ℕ) :
    X (j + 1) = (V ((j : ℝ) + 1) : ℂ) * X 1 - (V (j : ℝ) : ℂ) * X 0 +
      ∑ i ∈ Finset.range j, (V ((j : ℝ) - i) : ℂ) * f i := by
  set S : ℕ → ℂ := fun j => ∑ i ∈ Finset.range j, (V ((j : ℝ) - i) : ℂ) * f i with hSdef
  have hVn : ∀ m : ℕ, V ((m : ℝ) + 2) = E * V ((m : ℝ) + 1) - V (m : ℝ) := by
    intro m
    have := hV ((m : ℝ) + 1)
    rw [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring,
      show (m : ℝ) + 1 - 1 = (m : ℝ) by ring] at this
    exact this
  have hS : ∀ j : ℕ, S (j + 2) = (E : ℂ) * S (j + 1) - S j + f (j + 1) := by
    intro j
    have h1 : S (j + 2) = ∑ i ∈ Finset.range (j + 1), (V (((j + 2 : ℕ) : ℝ) - i) : ℂ) * f i +
        f (j + 1) := by
      simp only [hSdef]
      rw [Finset.sum_range_succ]
      have : V (((j + 2 : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)) = 1 := by
        rw [← hV1]; congr 1; push_cast; ring
      rw [this]; simp
    have h2 : ∑ i ∈ Finset.range (j + 1), (V (((j + 2 : ℕ) : ℝ) - i) : ℂ) * f i =
        (E : ℂ) * S (j + 1) - ∑ i ∈ Finset.range (j + 1), (V ((j : ℝ) - i) : ℂ) * f i := by
      simp only [hSdef]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hV (((j + 1 : ℕ) : ℝ) - i)
      rw [show ((j + 1 : ℕ) : ℝ) - i + 1 = ((j + 2 : ℕ) : ℝ) - i by push_cast; ring,
        show ((j + 1 : ℕ) : ℝ) - i - 1 = (j : ℝ) - i by push_cast; ring] at this
      rw [this]
      push_cast
      ring
    have h3 : ∑ i ∈ Finset.range (j + 1), (V ((j : ℝ) - i) : ℂ) * f i = S j := by
      simp only [hSdef]
      rw [Finset.sum_range_succ]
      simp [hV0]
    rw [h1, h2, h3]
  set U : ℕ → ℂ := fun j => (V ((j : ℝ) + 1) : ℂ) * X 1 - (V (j : ℝ) : ℂ) * X 0 + S j with hU
  have hUrec : ∀ j : ℕ, U (j + 2) = (E : ℂ) * U (j + 1) - U j + f (j + 1) := by
    intro j
    simp only [hU]
    rw [hS j]
    have h1 : V (((j + 2 : ℕ) : ℝ) + 1) = E * V (((j + 1 : ℕ) : ℝ) + 1) - V ((j : ℝ) + 1) := by
      have := hVn (j + 1)
      push_cast at this ⊢
      rw [show (j : ℝ) + 2 + 1 = (j : ℝ) + 1 + 2 by ring] at *
      linarith
    have h2 : V (((j + 2 : ℕ) : ℝ)) = E * V (((j + 1 : ℕ) : ℝ)) - V ((j : ℝ)) := by
      have := hVn j
      push_cast at this ⊢
      exact this
    have h1c : (V (((j + 2 : ℕ) : ℝ) + 1) : ℂ) =
        (E : ℂ) * (V (((j + 1 : ℕ) : ℝ) + 1) : ℂ) - (V ((j : ℝ) + 1) : ℂ) := by
      exact_mod_cast h1
    have h2c : (V (((j + 2 : ℕ) : ℝ)) : ℂ) =
        (E : ℂ) * (V (((j + 1 : ℕ) : ℝ)) : ℂ) - (V ((j : ℝ)) : ℂ) := by
      exact_mod_cast h2
    rw [h1c, h2c]
    ring
  have key : ∀ j : ℕ, X (j + 1) = U j ∧ X (j + 2) = U (j + 1) := by
    intro j
    induction j with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [hU, hSdef, hV0, hV1]
      · have hV2 : V 2 = E := by
          have := hVn 0
          simp only [Nat.cast_zero, zero_add] at this
          rw [hV0, hV1] at this
          linarith
        have h0 := hX 0
        simp only [hU, hSdef, Nat.cast_zero, Nat.cast_one, zero_add, Finset.sum_range_one,
          sub_zero, hV1]
        rw [show (1 : ℝ) + 1 = 2 by norm_num, hV2]
        simp only [zero_add] at h0
        rw [h0]
        push_cast
        ring
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have h3 := hX (j + 1)
      rw [show j + 1 + 2 = j + 3 by ring, show j + 1 + 1 = j + 2 by ring] at h3
      change X (j + 3) = U (j + 2)
      rw [h3, ih.2, ih.1, hUrec j]
  exact (key j).1

private lemma residualK_finRotate_pow_val {n : ℕ} (b₀ : Fin (n + 1)) (j : ℕ) :
    ((((finRotate (n + 1)) ^ j) b₀ : Fin (n + 1)) : ℕ) = (b₀.val + j) % (n + 1) := by
  induction j with
  | zero => simp [Nat.mod_eq_of_lt b₀.isLt]
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, residualK_fin_val_add_one, ih,
      Nat.mod_add_mod, ← add_assoc]

private lemma residualK_mod_cases (L x : ℕ) (hx : x < 2 * L) :
    x % L = if x < L then x else x - L := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (not_lt.mp h), Nat.mod_eq_of_lt (by omega)]

/-- Within one lap, the rotation `finRotate^i b₀` hits `b` exactly for `i` equal to the offset. -/
private lemma residualK_pow_eq_iff {n : ℕ} (b₀ b : Fin (n + 1)) (i : ℕ) (hi : i < n + 1) :
    ((finRotate (n + 1)) ^ i) b₀ = b ↔ i = (b.val + (n + 1) - b₀.val) % (n + 1) := by
  rw [Fin.ext_iff, residualK_finRotate_pow_val]
  have hb0 := b₀.isLt
  have hb := b.isLt
  have e1 := residualK_mod_cases (n + 1) (b₀.val + i) (by omega)
  have e2 := residualK_mod_cases (n + 1) (b.val + (n + 1) - b₀.val) (by omega)
  rw [e1, e2]
  split_ifs <;> omega

private lemma residualK_source_sum {n : ℕ} (V : ℝ → ℝ) (b₀ b : Fin (n + 1)) (j : ℕ)
    (hj : j < n + 1) :
    ∑ i ∈ Finset.range j, (V ((j : ℝ) - i) : ℂ) *
        (if ((finRotate (n + 1)) ^ i) b₀ = b then (1 : ℂ) else 0) =
      if (b.val + (n + 1) - b₀.val) % (n + 1) < j then
        (V ((j : ℝ) - ((b.val + (n + 1) - b₀.val) % (n + 1) : ℕ)) : ℂ) else 0 := by
  set k := (b.val + (n + 1) - b₀.val) % (n + 1) with hk
  have : ∀ i ∈ Finset.range j, (V ((j : ℝ) - i) : ℂ) *
      (if ((finRotate (n + 1)) ^ i) b₀ = b then (1 : ℂ) else 0) =
      if i = k then (V ((j : ℝ) - i) : ℂ) else 0 := by
    intro i hi
    have hi' : i < n + 1 := lt_of_lt_of_le (Finset.mem_range.mp hi) hj.le
    rw [if_congr (residualK_pow_eq_iff b₀ b i hi') rfl rfl]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Finset.range j) k]
  simp only [Finset.mem_range]

/-- The interpolation identity of Lemma 6.5 [da:lem:free-interpolation] as an exact equation
for a right inverse `M` of `A_L - w`: the remainder is `(w - 2cos ϑ)` times a convolution. -/
private lemma residualK_fi_cell {n : ℕ} (w : ℂ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hM : (cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) * M = 1)
    (ϑ : ℝ) (hs : Real.sin ϑ ≠ 0) (b₀ b : Fin (n + 1)) (j : ℕ) (hj : j < n + 1) :
    M ((finRotate (n + 1) ^ j) b₀) b =
      ((Real.sin (((j : ℝ) + 1) * ϑ) / Real.sin ϑ : ℝ) : ℂ) * M b₀ b -
      ((Real.sin ((j : ℝ) * ϑ) / Real.sin ϑ : ℝ) : ℂ) * M ((finRotate (n + 1)).symm b₀) b +
      ((if (b.val + (n + 1) - b₀.val) % (n + 1) < j then
        Real.sin (((j : ℝ) - (((b.val + (n + 1) - b₀.val) % (n + 1) : ℕ) : ℝ)) * ϑ) /
          Real.sin ϑ else 0 : ℝ) : ℂ) +
      (w - ((2 * Real.cos ϑ : ℝ) : ℂ)) *
        ∑ i ∈ Finset.range j, ((Real.sin (((j : ℝ) - i) * ϑ) / Real.sin ϑ : ℝ) : ℂ) *
          M ((finRotate (n + 1) ^ i) b₀) b := by
  set σ := finRotate (n + 1) with hσ
  set V : ℝ → ℝ := fun t => Real.sin (t * ϑ) / Real.sin ϑ with hV
  set E : ℝ := 2 * Real.cos ϑ with hE
  set X : ℕ → ℂ := fun m => M (σ.symm ((σ ^ m) b₀)) b with hXdef
  set δ : ℕ → ℂ := fun i => if (σ ^ i) b₀ = b then 1 else 0 with hδ
  set f : ℕ → ℂ := fun i => δ i + (w - (E : ℂ)) * X (i + 1) with hf
  have hX1 : ∀ m, X (m + 1) = M ((σ ^ m) b₀) b := by
    intro m
    simp only [hXdef]
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
  have hrec : ∀ i, X (i + 2) = (E : ℂ) * X (i + 1) - X i + f i := by
    intro i
    have hr := residualK_matrix_rec w M hM ((σ ^ i) b₀) b
    have e1 : (σ ^ i) b₀ + 1 = (σ ^ (i + 1)) b₀ := by
      rw [pow_succ', Equiv.Perm.mul_apply, hσ, finRotate_apply]
    have e2 : (σ ^ i) b₀ - 1 = σ.symm ((σ ^ i) b₀) := by
      rw [hσ, finRotate_symm_apply]
    rw [e1, e2] at hr
    have h2 : X (i + 2) = M ((σ ^ (i + 1)) b₀) b := hX1 (i + 1)
    have h1 : X (i + 1) = M ((σ ^ i) b₀) b := hX1 i
    have h0 : X i = M (σ.symm ((σ ^ i) b₀)) b := rfl
    simp only [hf, hδ]
    rw [h2, h1, h0]
    linear_combination hr
  have hV0 : V 0 = 0 := by simp [hV]
  have hV1 : V 1 = 1 := by simp [hV, div_self hs]
  have hVrec : ∀ t, V (t + 1) = E * V t - V (t - 1) := by
    intro t
    simp only [hV, hE]
    rw [show (t + 1) * ϑ = t * ϑ + ϑ by ring, show (t - 1) * ϑ = t * ϑ - ϑ by ring,
      residualK_sin_step]
    ring
  have hD := residualK_duhamel_formula V E hV0 hV1 hVrec X f hrec j
  have hXj : X (j + 1) = M ((σ ^ j) b₀) b := hX1 j
  have hX1' : X 1 = M b₀ b := by rw [hX1 0]; simp
  have hX0 : X 0 = M (σ.symm b₀) b := by simp [hXdef]
  have hsum : ∑ i ∈ Finset.range j, (V ((j : ℝ) - i) : ℂ) * f i =
      ∑ i ∈ Finset.range j, (V ((j : ℝ) - i) : ℂ) * δ i +
        (w - (E : ℂ)) * ∑ i ∈ Finset.range j, (V ((j : ℝ) - i) : ℂ) * M ((σ ^ i) b₀) b := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf]
    rw [hX1 i]
    ring
  have hsrc := residualK_source_sum V b₀ b j hj
  rw [hXj, hX1', hX0, hsum] at hD
  rw [hD]
  simp only [hδ] at *
  rw [hsrc]
  have hite : (if (b.val + (n + 1) - b₀.val) % (n + 1) < j then
        (V ((j : ℝ) - (((b.val + (n + 1) - b₀.val) % (n + 1) : ℕ) : ℝ)) : ℂ) else 0) =
      ((if (b.val + (n + 1) - b₀.val) % (n + 1) < j then
        V ((j : ℝ) - (((b.val + (n + 1) - b₀.val) % (n + 1) : ℕ) : ℝ)) else 0 : ℝ) : ℂ) := by
    split_ifs <;> simp
  rw [hite]
  simp only [hV]
  ring


/-- Away from the band edges, `|s(w)| ≥ κ/2`. -/
private lemma residualK_fi_s_lower {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) {w : ℂ}
    (hw : ‖w - E‖ ≤ κ / 2) : κ / 2 ≤ ‖freeS 1 w‖ := by
  have hre : |w.re - E| ≤ κ / 2 := by
    have := Complex.abs_re_le_norm (w - (E : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    exact this.trans hw
  have hE' := abs_le.mp hE
  have hre' := abs_le.mp hre
  have h1 : κ / 2 ≤ ‖w - 2‖ := by
    have h3 : (w - 2).re = w.re - 2 := by simp
    have h4 := Complex.abs_re_le_norm (w - 2)
    have h5 := neg_abs_le (w - 2).re
    rw [h3] at h4 h5
    linarith
  have h2 : κ / 2 ≤ ‖w + 2‖ := by
    have h3 : (w + 2).re = w.re + 2 := by simp
    have h4 := Complex.re_le_norm (w + 2)
    rw [h3] at h4
    linarith
  have hsq : freeS 1 w ^ 2 = (w - 2) * (w + 2) := by
    rw [freeS_sq]; push_cast; ring
  have hn : ‖freeS 1 w‖ ^ 2 = ‖w - 2‖ * ‖w + 2‖ := by
    rw [← norm_pow, hsq, norm_mul]
  have : (κ / 2) ^ 2 ≤ ‖freeS 1 w‖ ^ 2 := by
    rw [hn, sq]
    exact mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp this

/-- `1 - |ρ(w)| ≥ min{c,1}/(4g²)` when `Im w ≥ c/g²`, `g ≥ 1`. -/
private lemma residualK_fi_one_sub_r {c g : ℝ} (hc : 0 < c) (hg : 1 ≤ g) {w : ℂ}
    (hw : c / g ^ 2 ≤ w.im) :
    min c 1 / (4 * g ^ 2) ≤ 1 - ‖freeRho 1 w‖ := by
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg
  have hgp : 0 < g ^ 2 := by linarith
  have hw0 : 0 < w.im := lt_of_lt_of_le (by positivity) hw
  obtain ⟨hρ0, hw_eq⟩ := residualK_freeRho_aux 1 one_pos w hw0
  have hr1 : ‖freeRho 1 w‖ < 1 := norm_freeRho_lt_one 1 w hw0
  set ρ := freeRho 1 w with hρ
  have hr0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  set r := ‖ρ‖ with hr
  set N := r ^ 2 with hN
  have hNpos : 0 < N := by positivity
  have hnormSq : Complex.normSq ρ = N := by rw [hN, hr, Complex.sq_norm]
  have him : w.im = ρ.im - ρ.im / N := by
    rw [hw_eq, Complex.ofReal_one, one_mul, Complex.add_im, Complex.inv_im, hnormSq]; ring
  have hNxy : N = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [hN, hr, Complex.sq_norm, Complex.normSq_apply]; ring
  have hy : |ρ.im| ≤ r := by
    rw [hr]; exact Complex.abs_im_le_norm ρ
  have hN1 : N < 1 := by nlinarith
  -- `N · Im w = ρ.im (N - 1) ≤ r (1 - N)`
  have h1 : N * w.im = ρ.im * (N - 1) := by rw [him]; field_simp
  have h2 : N * w.im ≤ r * (1 - N) := by
    rw [h1]
    have : ρ.im * (N - 1) ≤ |ρ.im| * (1 - N) := by
      rw [show ρ.im * (N - 1) = -ρ.im * (1 - N) by ring]
      exact mul_le_mul_of_nonneg_right (neg_le_abs _) (by linarith)
    exact this.trans (mul_le_mul_of_nonneg_right hy (by linarith))
  have h3 : r * w.im ≤ 1 - N := by
    have : r * (r * w.im) ≤ r * (1 - N) := by rw [hN] at h2; nlinarith
    exact le_of_mul_le_mul_left this hr0
  have hcw : c / g ^ 2 ≤ w.im := hw
  have hc' : min c 1 / g ^ 2 ≤ w.im :=
    le_trans (div_le_div_of_nonneg_right (min_le_left _ _) hgp.le) hcw
  have hmin1 : min c 1 ≤ 1 := min_le_right _ _
  have hmin0 : 0 < min c 1 := lt_min hc one_pos
  by_cases hrh : 1 / 2 ≤ r
  · have h4 : r * (min c 1 / g ^ 2) ≤ 1 - N := le_trans (mul_le_mul_of_nonneg_left hc' hr0.le) h3
    have h5 : 1 - N ≤ 2 * (1 - r) := by rw [hN]; nlinarith
    have h6 : (1 / 2) * (min c 1 / g ^ 2) ≤ r * (min c 1 / g ^ 2) :=
      mul_le_mul_of_nonneg_right hrh (by positivity)
    have : min c 1 / (4 * g ^ 2) = (1 / 4) * (min c 1 / g ^ 2) := by field_simp
    rw [this]
    nlinarith
  · rw [not_le] at hrh
    have : min c 1 / (4 * g ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith


/-- Entry bound for row `0` of `(A_L - w)⁻¹`. -/
private lemma residualK_fi_row0_norm {n : ℕ} (hn : 2 ≤ n) {w : ℂ} (hw : 0 < w.im) (x : Fin (n + 1))
    {κ σ₁ : ℝ} (hκ : 0 < κ) (hs : κ / 2 ≤ ‖freeS 1 w‖) (hσ : 0 < σ₁)
    (hσ' : σ₁ ≤ 1 - ‖freeRho 1 w‖ ^ (n + 1)) :
    ‖((cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹) 0 x‖ ≤
      (2 / κ) * (‖freeRho 1 w‖ ^ (x : ℕ) + ‖freeRho 1 w‖ ^ (n + 1 - (x : ℕ))) / σ₁ := by
  have h := freeRowCycle_eq 1 w hw (n + 1) (by omega) x
  simp only [Complex.ofReal_one, one_smul] at h
  have h0 : ((cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹) 0 x =
      freeT 1 w * (freeRho 1 w ^ (x : ℕ) + freeRho 1 w ^ (n + 1 - (x : ℕ))) /
        (1 - freeRho 1 w ^ (n + 1)) := h
  rw [h0, norm_div, norm_mul]
  have hfT : ‖freeT 1 w‖ ≤ 2 / κ := by
    rw [freeT_eq 1 w hw, norm_neg, norm_inv]
    rw [show 2 / κ = (κ / 2)⁻¹ by field_simp]
    exact inv_anti₀ (by positivity) hs
  have hnum : ‖freeRho 1 w ^ (x : ℕ) + freeRho 1 w ^ (n + 1 - (x : ℕ))‖ ≤
      ‖freeRho 1 w‖ ^ (x : ℕ) + ‖freeRho 1 w‖ ^ (n + 1 - (x : ℕ)) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow, norm_pow]
  have hden : σ₁ ≤ ‖1 - freeRho 1 w ^ (n + 1)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (freeRho 1 w ^ (n + 1))
    rw [norm_one, norm_pow] at this
    linarith
  have hnn : 0 ≤ (2 / κ) * (‖freeRho 1 w‖ ^ (x : ℕ) + ‖freeRho 1 w‖ ^ (n + 1 - (x : ℕ))) := by
    positivity
  refine div_le_div₀ hnn ?_ hσ hden
  exact mul_le_mul hfT hnum (norm_nonneg _) (by positivity)

private lemma residualK_fi_sum_geom {r : ℝ} (h0 : 0 < r) (h1 : r < 1) (L : ℕ) :
    ∑ x : Fin L, (r ^ (x : ℕ) + r ^ (L - (x : ℕ))) ≤ 2 / (1 - r) := by
  rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range (fun i => r ^ i) L,
    Fin.sum_univ_eq_sum_range (fun i => r ^ (L - i)) L]
  have e : ∑ i ∈ Finset.range L, r ^ (L - i) = ∑ i ∈ Finset.range L, r ^ (i + 1) := by
    rw [← Finset.sum_range_reflect (fun j => r ^ (j + 1)) L]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.mp hi
    congr 1; omega
  rw [e]
  have g1 : ∑ i ∈ Finset.range L, r ^ i ≤ (1 - r)⁻¹ := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := L) h0.le h1
    rw [← Finset.range_eq_Ico] at this
    simpa [div_eq_mul_inv] using this
  have e2 : ∑ i ∈ Finset.range L, r ^ (i + 1) = r * ∑ i ∈ Finset.range L, r ^ i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e2]
  have h3 : r * ∑ i ∈ Finset.range L, r ^ i ≤ (1 - r)⁻¹ := by
    calc r * ∑ i ∈ Finset.range L, r ^ i ≤ 1 * (1 - r)⁻¹ :=
          mul_le_mul h1.le g1 (Finset.sum_nonneg fun i _ => by positivity) zero_le_one
      _ = (1 - r)⁻¹ := one_mul _
  rw [div_eq_mul_inv, two_mul]
  linarith

/-- `A_L - w` is invertible for `Im w > 0`. -/
private lemma residualK_fi_mul_inv {n : ℕ} (hn : 2 ≤ n) {w : ℂ} (hw : 0 < w.im) :
    (cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) *
      (cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ = 1 := by
  set A' := cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) with hA'
  refine Matrix.mul_nonsing_inv A' ?_
  by_contra hnu
  have h0 := Matrix.nonsing_inv_apply_not_isUnit A' hnu
  have h := freeRowCycle_eq 1 w hw (n + 1) (by omega) 0
  simp only [Complex.ofReal_one, one_smul] at h
  have h' : (A'⁻¹) 0 0 = freeT 1 w * (freeRho 1 w ^ ((0 : Fin (n + 1)) : ℕ) +
      freeRho 1 w ^ (n + 1 - ((0 : Fin (n + 1)) : ℕ))) / (1 - freeRho 1 w ^ (n + 1)) := h
  rw [h0] at h'
  have hr1 : ‖freeRho 1 w‖ < 1 := norm_freeRho_lt_one 1 w hw
  have hz : ‖freeRho 1 w ^ (n + 1)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hr1 (by omega)
  have hne1 : 1 - freeRho 1 w ^ (n + 1) ≠ 0 := by
    intro h2
    have : freeRho 1 w ^ (n + 1) = 1 := by linear_combination -h2
    rw [this, norm_one] at hz
    exact lt_irrefl _ hz
  have hne2 : 1 + freeRho 1 w ^ (n + 1) ≠ 0 := by
    intro h2
    have : freeRho 1 w ^ (n + 1) = -1 := by linear_combination h2
    rw [this, norm_neg, norm_one] at hz
    exact lt_irrefl _ hz
  have hs0 : freeS 1 w ≠ 0 := by
    intro h2
    have := freeS_im_pos 1 w hw
    rw [h2] at this
    simp at this
  have hf : freeT 1 w ≠ 0 := by
    rw [freeT_eq 1 w hw]; exact neg_ne_zero.mpr (inv_ne_zero hs0)
  simp only [Fin.val_zero, pow_zero, Nat.sub_zero] at h'
  rw [Matrix.zero_apply] at h'
  have := div_eq_zero_iff.mp h'.symm
  rcases this with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hf h4
    · exact hne2 h4
  · exact hne1 h3


/-- The interpolation identity (6.17) [da:eq:dyson-interpolation] with the error bound, for a
right inverse `M` of `A_L - w` with bounded entries. -/
private lemma residualK_fi_interp {κ C g E : ℝ} {n : ℕ} {w : ℂ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 0 < C) (hgp : 0 < g ^ 2) (hE : |E| ≤ 2 - κ)
    (hwE : ‖w - E‖ ≤ C / g ^ 2) (hL : 4 * g ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hmul : (cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) * M = 1)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hent : ∀ a b, ‖M a b‖ ≤ C₀) :
    ∀ (b₀ : Fin (n + 1)) (n' : ℕ), (n' : ℝ) ≤ 1 * g ^ 2 → ∀ j : ℕ, j < n' → ∀ b : Fin (n + 1),
      ‖M ((finRotate (n + 1) ^ j) b₀) b -
        (((Real.sin (((j : ℝ) + 1) * Real.arccos (E / 2)) /
            Real.sin (Real.arccos (E / 2)) : ℝ) : ℂ) * M b₀ b -
          ((Real.sin ((j : ℝ) * Real.arccos (E / 2)) /
            Real.sin (Real.arccos (E / 2)) : ℝ) : ℂ) * M ((finRotate (n + 1)).symm b₀) b +
          ((if (b.val + (n + 1) - b₀.val) % (n + 1) < j then
            Real.sin (((j : ℝ) - (((b.val + (n + 1) - b₀.val) % (n + 1) : ℕ) : ℝ)) *
              Real.arccos (E / 2)) / Real.sin (Real.arccos (E / 2)) else 0 : ℝ) : ℂ))‖ ≤
        (2 * C * C₀ / κ) * n' / g ^ 2 := by
  intro b₀ n' hn' j hj b
  have hjn : (j : ℝ) < n' := by exact_mod_cast hj
  have hn'g : (n' : ℝ) ≤ g ^ 2 := by simpa using hn'
  have hjL : j < n + 1 := by
    have h1 : (j : ℝ) < n + 1 := by
      have : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [this] at hL
      nlinarith
    exact_mod_cast h1
  have hE' := abs_le.mp hE
  have hcos : Real.cos (Real.arccos (E / 2)) = E / 2 :=
    Real.cos_arccos (by linarith) (by linarith)
  have hsin : κ / 2 ≤ Real.sin (Real.arccos (E / 2)) := by
    rw [Real.sin_arccos]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hs0 : Real.sin (Real.arccos (E / 2)) ≠ 0 := (lt_of_lt_of_le (by positivity) hsin).ne'
  have key := residualK_fi_cell w M hmul (Real.arccos (E / 2)) hs0 b₀ b j hjL
  set ϑ := Real.arccos (E / 2) with hϑ
  have hε : ‖w - ((2 * Real.cos ϑ : ℝ) : ℂ)‖ ≤ C / g ^ 2 := by
    rw [hcos, show 2 * (E / 2) = E by ring]
    exact hwE
  have hV : ∀ t : ℝ, ‖((Real.sin (t * ϑ) / Real.sin ϑ : ℝ) : ℂ)‖ ≤ 2 / κ := by
    intro t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (lt_of_lt_of_le (by positivity) hsin)]
    rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hsin) hκ]
    have := Real.abs_sin_le_one (t * ϑ)
    nlinarith
  have hsum : ‖∑ i ∈ Finset.range j, ((Real.sin (((j : ℝ) - i) * ϑ) / Real.sin ϑ : ℝ) : ℂ) *
      M ((finRotate (n + 1) ^ i) b₀) b‖ ≤ j * (2 / κ * C₀) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Finset.range j, ‖((Real.sin (((j : ℝ) - i) * ϑ) / Real.sin ϑ : ℝ) : ℂ) *
          M ((finRotate (n + 1) ^ i) b₀) b‖
        ≤ ∑ i ∈ Finset.range j, (2 / κ * C₀) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul]
          exact mul_le_mul (hV _) (hent _ _) (norm_nonneg _) (by positivity)
      _ = j * (2 / κ * C₀) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have heq : M ((finRotate (n + 1) ^ j) b₀) b -
      (((Real.sin (((j : ℝ) + 1) * ϑ) / Real.sin ϑ : ℝ) : ℂ) * M b₀ b -
        ((Real.sin ((j : ℝ) * ϑ) / Real.sin ϑ : ℝ) : ℂ) * M ((finRotate (n + 1)).symm b₀) b +
        ((if (b.val + (n + 1) - b₀.val) % (n + 1) < j then
          Real.sin (((j : ℝ) - (((b.val + (n + 1) - b₀.val) % (n + 1) : ℕ) : ℝ)) * ϑ) /
            Real.sin ϑ else 0 : ℝ) : ℂ)) =
      (w - ((2 * Real.cos ϑ : ℝ) : ℂ)) *
        ∑ i ∈ Finset.range j, ((Real.sin (((j : ℝ) - i) * ϑ) / Real.sin ϑ : ℝ) : ℂ) *
          M ((finRotate (n + 1) ^ i) b₀) b := by
    rw [key]; ring
  rw [heq, norm_mul]
  calc ‖w - ((2 * Real.cos ϑ : ℝ) : ℂ)‖ *
        ‖∑ i ∈ Finset.range j, ((Real.sin (((j : ℝ) - i) * ϑ) / Real.sin ϑ : ℝ) : ℂ) *
          M ((finRotate (n + 1) ^ i) b₀) b‖
      ≤ (C / g ^ 2) * (n' * (2 / κ * C₀)) := by
        apply mul_le_mul hε _ (norm_nonneg _) (by positivity)
        exact hsum.trans (mul_le_mul_of_nonneg_right hjn.le (by positivity))
    _ = (2 * C * C₀ / κ) * n' / g ^ 2 := by field_simp


/-- The Ward bound for the finite Fourier average: `|f(w)|² Im w ≤ Im f(w)`, (A.6) [da:eq:ward]. -/
private lemma residual_ward (b : ℝ) {L : ℕ} (hL : 1 ≤ L) (w : ℂ) (hw : 0 ≤ w.im) :
    ‖freeTL b L w‖ ^ 2 * w.im ≤ (freeTL b L w).im := by
  set r : Fin L → ℂ := fun k => (((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ) - w)⁻¹ with hr
  have hf : freeTL b L w = (((L : ℝ)⁻¹ : ℝ) : ℂ) * ∑ k, r k := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]; rfl
  have him : ∀ k, (r k).im = w.im * ‖r k‖ ^ 2 := by
    intro k
    simp only [hr]
    rw [Complex.inv_im, Complex.sq_norm, Complex.normSq_inv]
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
    ring
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hS : (∑ k, r k).im = w.im * ∑ k, ‖r k‖ ^ 2 := by
    rw [Complex.im_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => him k
  have hcs : (∑ k, ‖r k‖) ^ 2 ≤ L * ∑ k, ‖r k‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖r k‖)
    simpa using this
  have hn : ‖freeTL b L w‖ ≤ (L : ℝ)⁻¹ * ∑ k, ‖r k‖ := by
    rw [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL0)]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_pos.mpr hL0).le
  have hR : (freeTL b L w).im = (L : ℝ)⁻¹ * (w.im * ∑ k, ‖r k‖ ^ 2) := by
    rw [hf, Complex.im_ofReal_mul, hS]
  rw [hR]
  have h0 : 0 ≤ ∑ k, ‖r k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc ‖freeTL b L w‖ ^ 2 * w.im ≤ ((L : ℝ)⁻¹ * ∑ k, ‖r k‖) ^ 2 * w.im := by
        gcongr
    _ = (L : ℝ)⁻¹ ^ 2 * (∑ k, ‖r k‖) ^ 2 * w.im := by ring
    _ ≤ (L : ℝ)⁻¹ ^ 2 * (L * ∑ k, ‖r k‖ ^ 2) * w.im := by gcongr
    _ = (L : ℝ)⁻¹ * (w.im * ∑ k, ‖r k‖ ^ 2) := by field_simp


/-- `A_L` is symmetric. -/
private lemma residual_cycleAdj_transpose (L : ℕ) : (cycleAdj L)ᵀ = cycleAdj L := by
  ext a b
  simp only [Matrix.transpose_apply, cycleAdj, Matrix.of_apply]
  exact add_comm _ _

/-- `1 - e^{-t} ≥ t/2` for `0 ≤ t ≤ 1`. -/
private lemma residual_one_sub_exp {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t / 2 ≤ 1 - Real.exp (-t) := by
  have h := Real.add_one_le_exp t
  have he : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
  have hpos : 0 < Real.exp t := Real.exp_pos t
  have h2 : Real.exp (-t) ≤ (1 + t)⁻¹ := by
    rw [he]; exact inv_anti₀ (by linarith) (by linarith)
  have h3 : t / 2 ≤ 1 - (1 + t)⁻¹ := by
    rw [show 1 - (1 + t)⁻¹ = t / (1 + t) by field_simp; ring]
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  linarith

/-- The Dyson matrix `M_{B,u}(z)` of (5.27) [gc:eq:positive-dyson] on a comparison segment at
large coupling, with crude polynomial bounds: for `g ≥ C_κ`, `L ≥ 4g²`, `|x - E| ≤ C/g²`,
`0 < y ≤ C/g²`, `0 < u ≤ 1` and `g²y ≥ Q⁻¹`, `Q ≥ 1`, the matrix is symmetric, its entries and
its `uγ_g`-weighted rows are at most `32Q²/κ`, and it has the free interpolation of Lemma 6.5
[da:lem:free-interpolation] on cells of length `n ≤ g²` with error `2(2C + 8Q/κ)(8Q/κ)n/(κg²)`. -/
private lemma residual_seg (κ C : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 1 ≤ C) :
    ∃ Cκ : ℝ, 1 ≤ Cκ ∧ ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, 4 * g ^ 2 ≤ L → ∀ E x y u Q : ℝ,
      |E| ≤ 2 - κ → |x - E| ≤ C / g ^ 2 → 0 < y → y ≤ C / g ^ 2 → 0 < u → u ≤ 1 → 1 ≤ Q →
      Q⁻¹ ≤ g ^ 2 * y →
      (segMat g L x u (y / gammaG g))ᵀ = segMat g L x u (y / gammaG g) ∧
      (∀ a b, ‖segMat g L x u (y / gammaG g) a b‖ ≤ 32 * Q ^ 2 / κ) ∧
      (∀ a, u * gammaG g * ∑ b, ‖segMat g L x u (y / gammaG g) a b‖ ≤ 32 * Q ^ 2 / κ) ∧
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ g ^ 2 →
        RowInterp n E (segMat g L x u (y / gammaG g))
          (2 * (2 * C + 8 * Q / κ) * (8 * Q / κ) / κ * n / g ^ 2) := by
  refine ⟨max 1 (max (4 / κ) (8 * C / κ)), le_max_left _ _, ?_⟩
  intro g hg L hL E x y u Q hE hxE hy0 hyC hu0 hu1 hQ hQy
  have hg1 : 1 ≤ g := (le_max_left _ _).trans hg
  have hg4 : 4 / κ ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hg8 : 8 * C / κ ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have hg0 : 0 < g := by linarith
  have hgg : 0 < g ^ 2 := by positivity
  have hgsq : 1 ≤ g ^ 2 := one_le_pow₀ hg1
  have hggg : g ≤ g ^ 2 := by nlinarith
  have hb : hopB g = 1 := by unfold hopB; rw [max_eq_right hg1, div_self hg0.ne']
  have hγ : gammaG g = (g ^ 2)⁻¹ := by unfold gammaG; rw [max_eq_right hg1]
  have hγ0 : 0 < gammaG g := by rw [hγ]; positivity
  have hQ0 : 0 < Q := by linarith
  set β : ℝ := u * gammaG g with hβ
  have hβ0 : 0 < β := mul_pos hu0 hγ0
  have hβ1 : β ≤ (g ^ 2)⁻¹ := by
    rw [hβ, hγ]
    calc u * (g ^ 2)⁻¹ ≤ 1 * (g ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hu1 (by positivity)
      _ = (g ^ 2)⁻¹ := one_mul _
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hz
  have hzim : z.im = y := by simp [hz]
  have hz' : (x : ℂ) + ((gammaG g * (y / gammaG g) : ℝ) : ℂ) * Complex.I = z := by
    rw [hz, mul_div_cancel₀ _ hγ0.ne']
  have hL4 : (4 : ℝ) ≤ L := le_trans (by nlinarith) hL
  have hL3 : 3 ≤ L := by
    have : (3 : ℝ) ≤ L := by linarith
    exact_mod_cast this
  set m := mRootV (hopB g) β L z with hm
  have hroot : IsDysonRootV (hopB g) β L z m :=
    (mRootV_spec (hopB g) β (by rw [hb]; norm_num) hβ0 L hL3 z (by rw [hzim]; exact hy0.le)).1
      (by rw [hzim]; exact hy0)
  have hmim := hroot.1
  set w : ℂ := z + β * m with hw
  have hwim : w.im = y + β * m.im := by simp [hw, hzim]
  have hwim0 : 0 < w.im := by rw [hwim]; nlinarith
  have hyw : y ≤ w.im := by rw [hwim]; nlinarith
  have hseg : segMat g L x u (y / gammaG g) =
      (cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ := by
    unfold segMat dysonMat
    rw [hz', ← hm, hb, Complex.ofReal_one, one_smul]
  rw [hseg]
  -- the Ward bound `|m|² β ≤ 1`
  have hward : ‖m‖ ^ 2 * β ≤ 1 := by
    have h1 := residual_ward (hopB g) (by omega : 1 ≤ L) w hwim0.le
    have e : freeTL (hopB g) L w = m := hroot.2.symm
    rw [e] at h1
    have h2 : ‖m‖ ^ 2 * (β * m.im) ≤ ‖m‖ ^ 2 * w.im :=
      mul_le_mul_of_nonneg_left (by rw [hwim]; linarith) (sq_nonneg _)
    have h3 : (‖m‖ ^ 2 * β) * m.im ≤ 1 * m.im := by nlinarith
    exact le_of_mul_le_mul_right h3 hmim
  have hβm : ‖(β : ℂ) * m‖ ≤ 1 / g := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
    have h1 : (β * ‖m‖) ^ 2 ≤ (1 / g) ^ 2 := by
      calc (β * ‖m‖) ^ 2 = β * (‖m‖ ^ 2 * β) := by ring
        _ ≤ β * 1 := mul_le_mul_of_nonneg_left hward hβ0.le
        _ ≤ (g ^ 2)⁻¹ := by linarith
        _ = (1 / g) ^ 2 := by rw [one_div, inv_pow]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
  have hzE : ‖z - E‖ ≤ 2 * C / g ^ 2 := by
    have e : z - E = ((x - E : ℝ) : ℂ) + (y : ℂ) * Complex.I := by rw [hz]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hy0]
    calc |x - E| + y ≤ C / g ^ 2 + C / g ^ 2 := add_le_add hxE hyC
      _ = 2 * C / g ^ 2 := by ring
  have hwE : ‖w - E‖ ≤ κ / 2 := by
    have e : w - E = (z - E) + (β : ℂ) * m := by rw [hw]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : 2 * C / g ^ 2 ≤ κ / 4 := by
      rw [div_le_iff₀ hgg]
      have : 8 * C ≤ κ * g := by
        have := (div_le_iff₀ hκ).mp hg8; linarith
      nlinarith
    have h2 : 1 / g ≤ κ / 4 := by
      rw [div_le_iff₀ hg0]
      have := (div_le_iff₀ hκ).mp hg4; linarith
    linarith
  -- the closed form on the cycle
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have hL' : 2 ≤ L' := by omega
  have hs := residualK_fi_s_lower hκ hE hwE
  have hr1 : ‖freeRho 1 w‖ < 1 := norm_freeRho_lt_one 1 w hwim0
  have hρ0 : 0 < ‖freeRho 1 w‖ := norm_pos_iff.mpr (residualK_freeRho_aux 1 one_pos w hwim0).1
  have hr : min w.im 1 / (4 * 1 ^ 2) ≤ 1 - ‖freeRho 1 w‖ :=
    residualK_fi_one_sub_r hwim0 le_rfl (by simp)
  set r := ‖freeRho 1 w‖ with hrdef
  clear_value r
  have hmin : Q⁻¹ ≤ g ^ 2 * min y 1 := by
    rcases le_total y 1 with h | h
    · rw [min_eq_left h]; exact hQy
    · rw [min_eq_right h, mul_one]
      have : Q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hQ
      linarith
  have hminw : min y 1 ≤ min w.im 1 := min_le_min_right 1 hyw
  have hτ : Q⁻¹ ≤ ((L' + 1 : ℕ) : ℝ) * (1 - r) := by
    have h1 : g ^ 2 * min w.im 1 ≤ ((L' + 1 : ℕ) : ℝ) * (1 - r) := by
      have h4 : min w.im 1 / 4 ≤ 1 - r := by simpa using hr
      have hm0 : 0 ≤ min w.im 1 := le_min hwim0.le zero_le_one
      calc g ^ 2 * min w.im 1 = (4 * g ^ 2) * (min w.im 1 / 4) := by ring
        _ ≤ ((L' + 1 : ℕ) : ℝ) * (1 - r) := mul_le_mul hL h4 (by positivity) (by positivity)
    have h2 : g ^ 2 * min y 1 ≤ g ^ 2 * min w.im 1 := mul_le_mul_of_nonneg_left hminw hgg.le
    linarith
  have hrL : r ^ (L' + 1) ≤ Real.exp (-Q⁻¹) := by
    have h1 : r ≤ Real.exp (-(1 - r)) := by
      have := Real.add_one_le_exp (-(1 - r))
      linarith
    have h2 : r ^ (L' + 1) ≤ Real.exp (-(1 - r)) ^ (L' + 1) := pow_le_pow_left₀ hρ0.le h1 _
    rw [← Real.exp_nat_mul] at h2
    refine h2.trans (Real.exp_le_exp.mpr ?_)
    push_cast at hτ ⊢
    linarith
  have hσ : (2 * Q)⁻¹ ≤ 1 - r ^ (L' + 1) := by
    have h1 := residual_one_sub_exp (inv_pos.mpr hQ0).le (inv_le_one_of_one_le₀ hQ)
    have : (2 * Q)⁻¹ = Q⁻¹ / 2 := by rw [mul_inv]; ring
    rw [this]; linarith
  have hσ0 : 0 < (2 * Q)⁻¹ := by positivity
  set M := (cycleAdj (L' + 1) - w • (1 : Matrix (Fin (L' + 1)) (Fin (L' + 1)) ℂ))⁻¹ with hMdef
  have htr : ∀ a b : Fin (L' + 1), M a b = M 0 (b - a) := by
    intro a b
    have := residualK_inv_add_invariant w (-a) a b
    rw [add_neg_cancel, ← sub_eq_add_neg] at this
    exact this.symm
  have hrow0 : ∀ x : Fin (L' + 1), ‖M 0 x‖ ≤
      (2 / κ) * (r ^ (x : ℕ) + r ^ (L' + 1 - (x : ℕ))) / (2 * Q)⁻¹ :=
    fun x => by
      have := residualK_fi_row0_norm hL' hwim0 x hκ hs hσ0 (by rw [← hrdef]; exact hσ)
      rwa [← hrdef] at this
  have hpow1 : ∀ k : ℕ, r ^ k ≤ 1 := fun k => pow_le_one₀ hρ0.le hr1.le
  have hent : ∀ a b : Fin (L' + 1), ‖M a b‖ ≤ 8 * Q / κ := by
    intro a b
    rw [htr a b]
    refine (hrow0 (b - a)).trans ?_
    have h1 := hpow1 (b - a : Fin (L' + 1)).val
    have h2 := hpow1 (L' + 1 - (b - a : Fin (L' + 1)).val)
    calc (2 / κ) * (r ^ (b - a : Fin (L' + 1)).val + r ^ (L' + 1 - (b - a : Fin (L' + 1)).val)) /
          (2 * Q)⁻¹ ≤ (2 / κ) * (1 + 1) / (2 * Q)⁻¹ := by gcongr
      _ = 8 * Q / κ := by field_simp; ring
  have hQ2 : 8 * Q / κ ≤ 32 * Q ^ 2 / κ := by
    apply div_le_div_of_nonneg_right _ hκ.le
    have h1 : Q ≤ Q ^ 2 := by
      calc Q = Q * 1 := (mul_one _).symm
        _ ≤ Q * Q := mul_le_mul_of_nonneg_left hQ hQ0.le
        _ = Q ^ 2 := (sq Q).symm
    linarith
  refine ⟨?_, fun a b => (hent a b).trans hQ2, ?_, ?_⟩
  · rw [hMdef, Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, residual_cycleAdj_transpose]
  · intro a
    have hsum : ∑ b, ‖M a b‖ = ∑ x, ‖M 0 x‖ := by
      simp_rw [htr a]
      exact Equiv.sum_comp (Equiv.subRight a) (fun x => ‖M 0 x‖)
    have h1 : ∑ x : Fin (L' + 1), ‖M 0 x‖ ≤ (4 * Q / κ) * (2 / (1 - r)) := by
      calc ∑ x : Fin (L' + 1), ‖M 0 x‖
          ≤ ∑ x : Fin (L' + 1), (2 / κ) * (r ^ (x : ℕ) + r ^ (L' + 1 - (x : ℕ))) / (2 * Q)⁻¹ :=
            Finset.sum_le_sum fun x _ => hrow0 x
        _ = (4 * Q / κ) * ∑ x : Fin (L' + 1), (r ^ (x : ℕ) + r ^ (L' + 1 - (x : ℕ))) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            field_simp
            ring
        _ ≤ (4 * Q / κ) * (2 / (1 - r)) :=
            mul_le_mul_of_nonneg_left (residualK_fi_sum_geom hρ0 hr1 (L' + 1)) (by positivity)
    have h2 : 2 / (1 - r) ≤ 8 / min y 1 := by
      have hm0 : 0 < min y 1 := lt_min hy0 one_pos
      have : min y 1 / 4 ≤ 1 - r := by
        have := hr; simp at this; linarith
      rw [div_le_div_iff₀ (by linarith) hm0]
      linarith
    have hm0 : 0 < min y 1 := lt_min hy0 one_pos
    rw [hsum]
    calc u * gammaG g * ∑ x : Fin (L' + 1), ‖M 0 x‖ ≤
          (g ^ 2)⁻¹ * ((4 * Q / κ) * (8 / min y 1)) := by
          have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
          exact mul_le_mul hβ1 h3 (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity)
      _ = 32 * Q / κ * (g ^ 2 * min y 1)⁻¹ := by field_simp; ring
      _ ≤ 32 * Q / κ * Q := by
          gcongr
          rw [← inv_inv Q]
          exact inv_anti₀ (by positivity) hmin
      _ = 32 * Q ^ 2 / κ := by ring
  · intro n hn hng
    have hdiag : M 0 0 = m := by
      have hw' : 0 < (z + (β : ℂ) * m).im := hwim0
      have h := dysonMat_diag (hopB g) β (L' + 1) (by omega) z m hw' 0
      rw [← hroot.2] at h
      have e : dysonMat (hopB g) β (L' + 1) z m = M := by
        rw [hMdef]; unfold dysonMat; rw [hb]; simp [hw]
      rw [e] at h
      exact h
    have hm8 : ‖m‖ ≤ 8 * Q / κ := hdiag ▸ hent 0 0
    have hwE' : ‖w - E‖ ≤ (2 * C + 8 * Q / κ) / g ^ 2 := by
      have e : w - E = (z - E) + (β : ℂ) * m := by rw [hw]; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖(β : ℂ) * m‖ ≤ (g ^ 2)⁻¹ * (8 * Q / κ) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
        exact mul_le_mul hβ1 hm8 (norm_nonneg _) (by positivity)
      calc ‖z - E‖ + ‖(β : ℂ) * m‖ ≤ 2 * C / g ^ 2 + (g ^ 2)⁻¹ * (8 * Q / κ) := add_le_add hzE h1
        _ = (2 * C + 8 * Q / κ) / g ^ 2 := by field_simp
    have hmul := residualK_fi_mul_inv hL' hwim0
    have hint := residualK_fi_interp M hκ hκ2 (by positivity) hgg hE hwE' hL hmul
      (by positivity) hent
    refine residual_rowInterp_of hn (by omega) E M _ fun b₀ j hj b => ?_
    exact hint b₀ n (by linarith) j hj b


/-- The bound `C W^{-a} ≤ c` holds for all large `W`. -/
private lemma residualL_ev (K a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ W : ℕ in atTop, K * (W : ℝ) ^ (-a) ≤ c := by
  have h : Tendsto (fun W : ℕ => K * (W : ℝ) ^ (-a)) atTop (𝓝 (K * 0)) :=
    ((tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop).const_mul K
  rw [mul_zero] at h
  exact h.eventually (eventually_le_nhds hc)


/-- The anchor-envelope bound: with `p = 2(B + C) + D' + 1`, at most `36 W^{2(B+C)}` anchor pairs,
`g²η ≥ (C_χ W³)^{-1}` and `72 C_m C_χ^p W^{-1} ≤ 1`, the union of the Markov bounds
`C_m (g²η)^{-p} W^{-4p}` is at most `W^{-D'}/2`. -/
private lemma residualL_env_arith (x B C D' Cm Cχ p N y : ℝ) (hx : 1 ≤ x)
    (hp : p = 2 * (B + C) + D' + 1) (hp0 : 0 < p) (hCm : 0 < Cm) (hCχ : 0 < Cχ)
    (hN : N ≤ 36 * x ^ (2 * (B + C))) (hy : 0 < y)
    (hy' : (Cχ * x ^ (3 : ℝ))⁻¹ ≤ y) (hev : 72 * Cm * Cχ ^ p * x ^ (-1 : ℝ) ≤ 1) :
    N * (Cm * y ^ (-p) / (x ^ (4 : ℝ)) ^ p) ≤ x ^ (-D') / 2 := by
  have hx0 : 0 < x := by linarith
  have ha : 0 < Cχ * x ^ (3 : ℝ) := by positivity
  have hyp : y ^ (-p) ≤ Cχ ^ p * x ^ (3 * p) := by
    calc y ^ (-p) ≤ ((Cχ * x ^ (3 : ℝ))⁻¹) ^ (-p) :=
          Real.rpow_le_rpow_of_nonpos (inv_pos.mpr ha) hy' (by linarith)
      _ = (Cχ * x ^ (3 : ℝ)) ^ p := by
          rw [Real.inv_rpow ha.le, Real.rpow_neg ha.le, inv_inv]
      _ = Cχ ^ p * x ^ (3 * p) := by
          rw [Real.mul_rpow hCχ.le (by positivity), ← Real.rpow_mul hx0.le]
  have h4 : (x ^ (4 : ℝ)) ^ p = x ^ (4 * p) := by rw [← Real.rpow_mul hx0.le]
  have hexp : x ^ (2 * (B + C)) * x ^ (3 * p) / x ^ (4 * p) = x ^ (-D') * x ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_sub hx0, ← Real.rpow_add hx0]
    congr 1
    rw [hp]
    ring
  have h4p : 0 < x ^ (4 * p) := Real.rpow_pos_of_pos hx0 _
  have hD : 0 ≤ x ^ (-D') := (Real.rpow_pos_of_pos hx0 _).le
  rw [h4]
  calc N * (Cm * y ^ (-p) / x ^ (4 * p))
      ≤ (36 * x ^ (2 * (B + C))) * (Cm * (Cχ ^ p * x ^ (3 * p)) / x ^ (4 * p)) := by
        gcongr
    _ = (36 * Cm * Cχ ^ p) * (x ^ (2 * (B + C)) * x ^ (3 * p) / x ^ (4 * p)) := by ring
    _ = (72 * Cm * Cχ ^ p * x ^ (-1 : ℝ)) * (x ^ (-D') / 2) := by rw [hexp]; ring
    _ ≤ 1 * (x ^ (-D') / 2) := by gcongr
    _ = x ^ (-D') / 2 := one_mul _

/-- Markov's inequality for the `p`-th moment: `P(t ≤ f) ≤ K t^{-p}` when `E f^p ≤ K`. -/
private lemma residualL_markov {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsFiniteMeasure P] (f : Ω' → ℝ) (p t K : ℝ) (hp : 0 < p) (ht : 0 < t)
    (hf : Integrable (fun ω => f ω ^ p) P) (hf0 : ∀ ω, 0 ≤ f ω) (hK : ∫ ω, f ω ^ p ∂P ≤ K) :
    P {ω | t ≤ f ω} ≤ ENNReal.ofReal (K / t ^ p) := by
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  have hsub : {ω | t ≤ f ω} ⊆ {ω | t ^ p ≤ f ω ^ p} := fun ω hω =>
    Real.rpow_le_rpow ht.le hω hp.le
  have hM := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hf0 ω) p) hf (t ^ p)
  refine (measure_mono hsub).trans ?_
  have hK0 : 0 ≤ K := (integral_nonneg fun ω => Real.rpow_nonneg (hf0 ω) p).trans hK
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity), le_div_iff₀ htp]
  rw [measureReal_def] at hM
  nlinarith

/-- Hermitian GUE blocks stay Hermitian under real scaling. -/
private lemma residualL_herm (W L : ℕ) (ω : Ω W L) (b : ℝ) (r : Fin L) :
    (((b : ℝ) : ℂ) • gueBlock W L ω r).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (gueBlock_isHermitian W L ω r).eq, Complex.star_def,
    Complex.conj_ofReal]


/-- `ℓ_v(g) ≥ g²` for `g ≥ 1`, `L ≥ g²` and `0 ≤ v < 1`, (5.18) [fo:eq:scale]. -/
private lemma residualL_ellProp (g : ℝ) (hg : 1 ≤ g) (L : ℕ) (hL : g ^ 2 ≤ L) (v : ℝ) (hv0 : 0 ≤ v)
    (hv : v < 1) : g ^ 2 ≤ ellProp g L v := by
  unfold ellProp
  have hγ : gammaG g = (g ^ 2)⁻¹ := by unfold gammaG; rw [max_eq_right hg]
  rw [hγ]
  refine le_min hL ?_
  have hg0 : 0 < g := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hs0 : 0 < Real.sqrt ((g ^ 2)⁻¹ * (1 - v)) := Real.sqrt_pos.mpr (by positivity)
  have hs : Real.sqrt ((g ^ 2)⁻¹ * (1 - v)) ≤ g⁻¹ := by
    rw [show g⁻¹ = Real.sqrt ((g ^ 2)⁻¹) by rw [Real.sqrt_inv, Real.sqrt_sq hg0.le]]
    exact Real.sqrt_le_sqrt (mul_le_of_le_one_right (by positivity) (by linarith))
  have h1 : g / g⁻¹ ≤ g / Real.sqrt ((g ^ 2)⁻¹ * (1 - v)) :=
    div_le_div_of_nonneg_left hg0.le hs0 hs
  have h2 : g / g⁻¹ = g ^ 2 := by field_simp
  linarith

/-- The weight of Lemma 6.2 [da:lem:scale-budgets] is at least `W^{-F}`. -/
private lemma residualL_weight_ge (cw θ F : ℝ) (W : ℕ) (ℓ r : ℝ) :
    (W : ℝ) ^ (-F) ≤ weightFn cw θ F W ℓ r := by
  unfold weightFn
  linarith [Real.exp_pos (-(cw * (r / ℓ) ^ θ))]


/-- With `g² ≥ W^B` and `L ≤ g² W^C`, `L/n + 1 ≤ 3 W^{B+C}`. -/
private lemma residualL_cells (g B C : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hg : (W : ℝ) ^ B ≤ g ^ 2) (hL : (L : ℝ) ≤ g ^ 2 * (W : ℝ) ^ C) :
    (L : ℝ) / cellLen g W B + 1 ≤ 3 * (W : ℝ) ^ (B + C) := by
  have hx0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  obtain ⟨hlo, -⟩ := cellLen_bounds g B W hW hg
  have hWB : 0 < (W : ℝ) ^ B := Real.rpow_pos_of_pos hx0 B
  have hg2 : 0 < g ^ 2 := lt_of_lt_of_le hWB hg
  have hy : 0 < g ^ 2 * (W : ℝ) ^ (-B) / 2 := by
    have := Real.rpow_pos_of_pos hx0 (-B); positivity
  have hn : (0 : ℝ) < cellLen g W B := lt_of_lt_of_le hy hlo
  have h1 : (L : ℝ) / cellLen g W B ≤ 2 * (W : ℝ) ^ (B + C) := by
    rw [div_le_iff₀ hn]
    have e : (W : ℝ) ^ (B + C) * (W : ℝ) ^ (-B) = (W : ℝ) ^ C := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have hWBC : 0 ≤ (W : ℝ) ^ (B + C) := (Real.rpow_pos_of_pos hx0 _).le
    calc (L : ℝ) ≤ g ^ 2 * (W : ℝ) ^ C := hL
      _ = 2 * (W : ℝ) ^ (B + C) * (g ^ 2 * (W : ℝ) ^ (-B) / 2) := by rw [← e]; ring
      _ ≤ 2 * (W : ℝ) ^ (B + C) * cellLen g W B := by gcongr
  have h2 : (1 : ℝ) ≤ (W : ℝ) ^ (B + C) := Real.one_le_rpow (by exact_mod_cast hW) (by linarith)
  linarith



/-- First blocks of cells and their predecessors are anchors. -/
private lemma residual_anchor (n : ℕ) {L : ℕ} (a : Fin L) :
    IsAnchor n (cellStart n a) ∧ IsAnchor n (cellPrev n a) := by
  have h : (cellStart n a).val % n = 0 := by simp [cellStart]
  refine ⟨Or.inl h, Or.inr ?_⟩
  unfold cellPrev
  rw [Equiv.apply_symm_apply]
  exact h

/-- Norming through the anchor pairs: an interpolation with error `e` and a bound `A` at all
pairs of anchors give `|Y_{ab}| ≤ (4/κ)² A + e`. -/
private lemma residual_norming {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) (n : ℕ)
    {L : ℕ} (Y : Fin L → Fin L → ℂ) (A e : ℝ) (hA : 0 ≤ A)
    (hY : ∀ α β, IsAnchor n α → IsAnchor n β → ‖Y α β‖ ≤ A) (a b : Fin L)
    (h : ‖Y a b - ∑ α, ∑ β, ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * Y α β‖ ≤ e) :
    ‖Y a b‖ ≤ (4 / κ) ^ 2 * A + e := by
  have ha := residual_anchor n a
  have hb := residual_anchor n b
  have h1 := residual_double_le hκ hκ2 hE n (F := ℂ) a b Y A hA fun α β hα hβ =>
    hY α β (by rcases hα with rfl | rfl; exacts [ha.1, ha.2])
      (by rcases hβ with rfl | rfl; exacts [hb.1, hb.2])
  simp only [smul_eq_mul] at h1
  calc ‖Y a b‖ = ‖(Y a b - ∑ α, ∑ β, ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * Y α β) +
        ∑ α, ∑ β, ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * Y α β‖ := by ring_nf
    _ ≤ e + (4 / κ) ^ 2 * A := (norm_add_le _ _).trans (add_le_add h h1)
    _ = _ := by ring

/-- `x^{k₁} x^{a₁} ≤ x^{k₂} x^{a₂}` for `x ≥ 1` and `k₁ + a₁ ≤ k₂ + a₂`. -/
private lemma residual_mono (x : ℝ) (hx : 1 ≤ x) (k₁ k₂ : ℕ) (a₁ a₂ : ℝ)
    (h : (k₁ : ℝ) + a₁ ≤ k₂ + a₂) : x ^ k₁ * x ^ a₁ ≤ x ^ k₂ * x ^ a₂ := by
  have hx0 : 0 < x := by linarith
  rw [← Real.rpow_natCast x k₁, ← Real.rpow_natCast x k₂, ← Real.rpow_add hx0,
    ← Real.rpow_add hx0]
  exact Real.rpow_le_rpow_of_exponent_le hx h

/-- `K x^k x^{-b} ≤ x^{-D}` when `k + D + 1 ≤ b` and `K x^{-1} ≤ 1`. -/
private lemma residual_arith (x : ℝ) (k : ℕ) (b D K : ℝ) (hx : 1 ≤ x) (hK0 : 0 ≤ K)
    (h : (k : ℝ) + D + 1 ≤ b) (hK : K * x ^ (-1 : ℝ) ≤ 1) :
    K * (x ^ k * x ^ (-b)) ≤ x ^ (-D) := by
  have hx0 : 0 < x := by linarith
  have h1 : x ^ k * x ^ (-b) ≤ x ^ (0 : ℕ) * x ^ (-D + -1) :=
    residual_mono x hx k 0 (-b) (-D + -1) (by push_cast; linarith)
  rw [pow_zero, one_mul, Real.rpow_add hx0] at h1
  have hD : 0 ≤ x ^ (-D) := (Real.rpow_pos_of_pos hx0 _).le
  calc K * (x ^ k * x ^ (-b)) ≤ K * (x ^ (-D) * x ^ (-1 : ℝ)) := mul_le_mul_of_nonneg_left h1 hK0
    _ = (K * x ^ (-1 : ℝ)) * x ^ (-D) := by ring
    _ ≤ 1 * x ^ (-D) := mul_le_mul_of_nonneg_right hK hD
    _ = x ^ (-D) := one_mul _

/-- A sampled value is at most the supremum over the sample set. -/
private lemma residual_le_iSup {Λ : Type*} (S : Finset Λ) (f : Λ → ℝ) (s : Λ) (hs : s ∈ S) :
    f s ≤ ⨆ t : S, f t / 1 := by
  have := le_ciSup (f := fun t : S => f t / 1) (Set.finite_range _).bddAbove ⟨s, hs⟩
  simpa using this

private lemma residual_iSup_nonneg {Λ : Type*} (S : Finset Λ) (f : Λ → ℝ) (hf : ∀ s, 0 ≤ f s) :
    0 ≤ ⨆ t : S, f t / 1 :=
  Real.iSup_nonneg fun t => by simpa using hf t


/-- The anchor pairs, the sample set `S₁` of Lemma 5.10(b) [fo:lem:sampling-continuity] for
centered traces and residuals. -/
def anchorPairs (n L : ℕ) : Finset (Fin L × Fin L) :=
  univ.filter fun ab => IsAnchor n ab.1 ∧ IsAnchor n ab.2

/-- The anchor entries, the sample set `S₂` for traceless entries. -/
def anchorEntries (n W L : ℕ) : Finset ((Fin L × Fin W) × (Fin L × Fin W)) :=
  univ.filter fun e => IsAnchor n e.1.1 ∧ IsAnchor n e.2.1

set_option maxHeartbeats 1600000 in
-- the explicit estimates of this proof exceed the default heartbeat limit
/-- Lemma 5.10(b) [fo:lem:sampling-continuity], last paragraph, for centered block traces,
traceless entries and residuals at the anchor sample sets. -/
private theorem residual_pair_sampling (κ C : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 1 < C) (D D' : ℝ)
    (hD : 0 < D) (hD' : 0 < D') :
    ∃ B Cκ Cs : ℝ, 2 < B ∧ 1 ≤ Cκ ∧ 1 ≤ Cs ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x : FlowPt × ℝ,
      Cκ ≤ x.1.g → (W : ℝ) ^ B ≤ x.1.g ^ 2 → 4 * x.1.g ^ 2 ≤ x.1.L →
      (x.1.L : ℝ) ≤ x.1.g ^ 2 * (W : ℝ) ^ C → |x.1.E| ≤ 2 - κ →
      IsDysonRootV (hopB x.1.g) (gammaG x.1.g) x.1.L x.1.E (mRoot x.1.g x.1.L x.1.E) →
      ‖mRoot x.1.g x.1.L x.1.E‖ ≤ C → C⁻¹ ≤ (mRoot x.1.g x.1.L x.1.E).im → 1 / 2 ≤ x.1.u →
      (W : ℝ) ^ (-3 : ℝ) ≤ 1 - x.1.u → etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u ≤ x.2 →
      x.2 ≤ C / x.1.g ^ 2 →
        SampleBound (μ W x.1.L) (fun ab ω => blockTr (segG W x ω - segM W x) ab.1 ab.2)
          (fun _ => 1) (anchorPairs (cellLen x.1.g W B) x.1.L) Cs ((W : ℝ) ^ (-D))
          ((W : ℝ) ^ (-D')) ∧
        SampleBound (μ W x.1.L) (fun e ω => segG W x ω e.1 e.2 -
            if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0)
          (fun _ => 1) (anchorEntries (cellLen x.1.g W B) W x.1.L) Cs ((W : ℝ) ^ (-D))
          ((W : ℝ) ^ (-D')) ∧
        SampleBound (μ W x.1.L) (fun ab ω => segRes W x ω ab.1 ab.2)
          (fun _ => 1) (anchorPairs (cellLen x.1.g W B) x.1.L) Cs ((W : ℝ) ^ (-D))
          ((W : ℝ) ^ (-D')) := by
  obtain ⟨Cκχ, Cχ, hCκχ, hCχ, Hχ⟩ := char_large κ C hκ hκ2 hC.le
  set C₁ : ℝ := max C Cχ with hC₁
  have hC₁1 : 1 ≤ C₁ := le_trans hC.le (le_max_left _ _)
  have hCC₁ : C ≤ C₁ := le_max_left _ _
  have hχC₁ : Cχ ≤ C₁ := le_max_right _ _
  obtain ⟨Cκs, hCκs, Hs⟩ := residual_seg κ C₁ hκ hκ2 hC₁1
  obtain ⟨Cδ, hCδ, Hδ⟩ := cellClose_perturb κ hκ hκ2
  obtain ⟨Cc, hCc, Hc⟩ := centered_interp κ hκ hκ2
  obtain ⟨Cr, hCr, Hr⟩ := residual_interp κ hκ hκ2
  set B : ℝ := 4 * (D + C + 40) with hBdef
  have hB2 : 2 < B := by rw [hBdef]; linarith
  have hB0 : 0 ≤ B := by linarith
  have hB4 : B / 4 = D + C + 40 := by rw [hBdef]; ring
  set Cκ : ℝ := max (max Cκχ Cκs) (2 / Real.sqrt (κ / 2)) with hCκdef
  have hCκχ' : Cκχ ≤ Cκ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCκs' : Cκs ≤ Cκ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCκr : 2 / Real.sqrt (κ / 2) ≤ Cκ := le_max_right _ _
  have hCκ1 : 1 ≤ Cκ := hCκχ.trans hCκχ'
  set Cs : ℝ := max 1 ((4 / κ) ^ 2) with hCs
  have hCs4 : (4 / κ) ^ 2 ≤ Cs := le_max_right _ _
  refine ⟨B, Cκ, Cs, hB2, hCκ1, le_max_left _ _, ?_⟩
  set p : ℝ := 2 * (B + C) + D' + 1 with hpdef
  have hp : 0 < p := by rw [hpdef]; linarith
  obtain ⟨Cm, hCm, Hm⟩ := resolvent_moments (κ / 2) p C₁ (by linarith) hp (by linarith)
  obtain ⟨W₁, H₁⟩ := cells_prefix κ B C (D' + 1) hκ hκ2 hB2 (by linarith) (by linarith)
  set Kδ : ℝ := 2 * (2 * C₁ + 8 * Cχ / κ) * (8 * Cχ / κ) / κ with hKδ
  have hKδ0 : 0 ≤ Kδ := by positivity
  set KΓ : ℝ := 1 + 32 * Cχ ^ 2 / κ with hKΓ
  have hKΓ0 : 0 ≤ KΓ := by positivity
  set KR : ℝ := Cr * KΓ ^ 2 * 4 * (3 + 2 * Kδ) with hKR
  set KT : ℝ := Cc * (4 + Kδ) with hKT
  set KE : ℝ := 4 * Cc with hKE
  have hev : ∀ᶠ W : ℕ in atTop, ((2 ≤ W ∧ W₁ ≤ W) ∧ 4 * p ≤ (W : ℝ)) ∧
      (2 * C₁ * (W : ℝ) ^ (-B) ≤ 1 ∧ 2 * C₁ * Cδ * (W : ℝ) ^ (-(3 * B / 4)) ≤ 1 ∧
        2 * (W : ℝ) ^ (-(B / 4)) ≤ 1) ∧
      (72 * Cm * Cχ ^ p * (W : ℝ) ^ (-1 : ℝ) ≤ 1 ∧ KR * (W : ℝ) ^ (-1 : ℝ) ≤ 1 ∧
        KT * (W : ℝ) ^ (-1 : ℝ) ≤ 1 ∧ KE * (W : ℝ) ^ (-1 : ℝ) ≤ 1) :=
    (((eventually_ge_atTop 2).and (eventually_ge_atTop W₁)).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop (4 * p))).and
    (((residualL_ev (2 * C₁) B 1 (by linarith) one_pos).and
      ((residualL_ev (2 * C₁ * Cδ) (3 * B / 4) 1 (by linarith) one_pos).and
      (residualL_ev 2 (B / 4) 1 (by linarith) one_pos))).and
    ((residualL_ev (72 * Cm * Cχ ^ p) 1 1 one_pos one_pos).and
      ((residualL_ev KR 1 1 one_pos one_pos).and
      ((residualL_ev KT 1 1 one_pos one_pos).and
      (residualL_ev KE 1 1 one_pos one_pos)))))
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp hev
  refine ⟨W₀, fun W hW x hgC hWB h4L hLC hE hroot hmC hmim hu12 hu3 hyη hyC => ?_⟩
  obtain ⟨⟨⟨hW2, hW₁⟩, hW4p⟩, ⟨hE1, hE2, hE3⟩, ⟨hE4, hER, hET, hEE⟩⟩ := hW₀ W hW
  -- notation and basic facts at the point
  set g : ℝ := x.1.g with hgdef
  set L : ℕ := x.1.L with hLdef
  set E : ℝ := x.1.E with hEdef
  set u : ℝ := x.1.u with hudef
  set y : ℝ := x.2 with hydef
  set m : ℂ := mRoot g L E with hmdef
  have hW1 : 1 ≤ W := by omega
  have hx0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hx1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hx2 : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  have hg1 : 1 ≤ g := hCκ1.trans hgC
  have hg0 : 0 < g := by linarith
  have hgg : 0 < g ^ 2 := by positivity
  have hγ : gammaG g = (g ^ 2)⁻¹ := by unfold gammaG; rw [max_eq_right hg1]
  have hW3 : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hu1' : u < 1 := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hupos : 0 < u := by linarith
  obtain ⟨hre, hzE, hη0, hηC, hgη⟩ := Hχ g (hCκχ'.trans hgC) E m hE hmC hmim u hu0 hu1'
  have hy0 : 0 < y := hη0.trans_le hyη
  set zu : ℂ := zChar g E m u with hzu
  set z : ℂ := ((zu.re : ℝ) : ℂ) + (y : ℂ) * Complex.I with hz
  have hzim : z.im = y := by simp [hz]
  have hxE : |zu.re - E| ≤ C₁ / g ^ 2 := by
    have h1 : |zu.re - E| ≤ ‖zu - E‖ := by
      have := Complex.abs_re_le_norm (zu - (E : ℂ))
      simpa using this
    exact h1.trans (hzE.trans (div_le_div_of_nonneg_right hχC₁ hgg.le))
  have hyC₁ : y ≤ C₁ / g ^ 2 := hyC.trans (div_le_div_of_nonneg_right hCC₁ hgg.le)
  -- the comparison matrix on the segment
  set Q : ℝ := Cχ * (W : ℝ) ^ 3 with hQ
  have hW3n : (1 : ℝ) ≤ (W : ℝ) ^ 3 := one_le_pow₀ hx1
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact one_le_mul_of_one_le_of_one_le hCχ hW3n
  have hQy : Q⁻¹ ≤ g ^ 2 * y := by
    have h1 : (W : ℝ) ^ (-3 : ℝ) = ((W : ℝ) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hx0.le]; norm_cast
    have h2 : g ^ 2 * etaChar g m u ≤ g ^ 2 * y := mul_le_mul_of_nonneg_left hyη hgg.le
    have h3 : Q⁻¹ ≤ (1 - u) / Cχ := by
      rw [hQ, mul_inv, div_eq_mul_inv, mul_comm]
      rw [← h1]
      exact mul_le_mul_of_nonneg_right hu3 (by positivity)
    linarith
  set M := segMat g L zu.re u (y / gammaG g) with hMdef
  obtain ⟨hMs, hMe, hMr, hMI⟩ := Hs g (hCκs'.trans hgC) L h4L E zu.re y u Q hE hxE hy0 hyC₁
    hupos hu1'.le hQ1 hQy
  set n : ℕ := cellLen g W B with hndef
  obtain ⟨-, hnhi⟩ := cellLen_bounds g B W hW1 hWB
  have hn1 : 1 ≤ n := le_max_left _ _
  have hWB1 : (W : ℝ) ^ (-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hng : (n : ℝ) ≤ g ^ 2 := hnhi.trans (mul_le_of_le_one_right hgg.le hWB1)
  have hng' : (n : ℝ) / g ^ 2 ≤ (W : ℝ) ^ (-B) := by rw [div_le_iff₀ hgg]; linarith
  set δ : ℝ := 2 * (2 * C₁ + 8 * Q / κ) * (8 * Q / κ) / κ * n / g ^ 2 with hδdef
  have hRI : RowInterp n E M δ := hMI n hn1 hng
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  have hδb : δ ≤ Kδ * ((W : ℝ) ^ 6 * (W : ℝ) ^ (-B)) := by
    have e1 : 2 * C₁ + 8 * Q / κ ≤ (2 * C₁ + 8 * Cχ / κ) * (W : ℝ) ^ 3 := by
      rw [hQ]
      have : 2 * C₁ ≤ 2 * C₁ * (W : ℝ) ^ 3 := le_mul_of_one_le_right (by linarith) hW3n
      have e : (2 * C₁ + 8 * Cχ / κ) * (W : ℝ) ^ 3 = 2 * C₁ * (W : ℝ) ^ 3 +
          8 * (Cχ * (W : ℝ) ^ 3) / κ := by ring
      rw [e]; linarith
    have e2 : 8 * Q / κ = 8 * Cχ / κ * (W : ℝ) ^ 3 := by rw [hQ]; ring
    have hn0 : (0 : ℝ) ≤ n / g ^ 2 := by positivity
    calc δ = 2 * (2 * C₁ + 8 * Q / κ) * (8 * Q / κ) / κ * ((n : ℝ) / g ^ 2) := by
          rw [hδdef]; ring
      _ ≤ 2 * ((2 * C₁ + 8 * Cχ / κ) * (W : ℝ) ^ 3) * (8 * Cχ / κ * (W : ℝ) ^ 3) / κ *
          (W : ℝ) ^ (-B) := by
          have hQ0' : 0 ≤ 8 * Q / κ := by rw [hQ]; positivity
          have hc : 2 * (2 * C₁ + 8 * Q / κ) * (8 * Q / κ) / κ ≤
              2 * ((2 * C₁ + 8 * Cχ / κ) * (W : ℝ) ^ 3) * (8 * Cχ / κ * (W : ℝ) ^ 3) / κ := by
            rw [← e2]
            apply div_le_div_of_nonneg_right _ hκ.le
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 (by norm_num)) hQ0'
          exact mul_le_mul hc hng' hn0 (by positivity)
      _ = Kδ * ((W : ℝ) ^ 6 * (W : ℝ) ^ (-B)) := by rw [hKδ]; ring
  set Γ : ℝ := 32 * Q ^ 2 / κ with hΓdef
  have hΓb : 1 + Γ ≤ KΓ * (W : ℝ) ^ 6 := by
    have hW6 : (1 : ℝ) ≤ (W : ℝ) ^ 6 := one_le_pow₀ hx1
    rw [hΓdef, hQ, hKΓ]
    have e : 32 * (Cχ * (W : ℝ) ^ 3) ^ 2 / κ = 32 * Cχ ^ 2 / κ * (W : ℝ) ^ 6 := by ring
    rw [e, add_mul, one_mul]; linarith
  have hL3 : 3 ≤ L := by
    have h1 : (1 : ℝ) ≤ g ^ 2 := one_le_pow₀ hg1
    have : (3 : ℝ) ≤ L := by linarith
    exact_mod_cast this
  -- the random potential and the Green function
  set s : ℝ := u * gammaG g with hsdef
  have hs0 : 0 ≤ s := mul_nonneg hu0 (by rw [hγ]; positivity)
  have hsg : s * g ^ 2 ≤ 1 := by
    rw [hsdef, hγ, mul_assoc, inv_mul_cancel₀ hgg.ne', mul_one]; exact hu1'.le
  let V : Ω W L → Fin L → Matrix (Fin W) (Fin W) ℂ := fun ω r =>
    ((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω r
  have hV : ∀ ω r, (V ω r).IsHermitian := fun ω r => residualL_herm W L ω _ r
  have hG : ∀ ω, segG W x ω =
      resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp (V ω)) z := by
    intro ω
    change resolventMat (flowH g W L u ω) z = _
    rw [flowH_cycle g hg1]
  -- the bad events
  set A₁ : Set (Ω W L) :=
    {ω | ¬ CellClose n E (E : ℂ) (V ω) ((W : ℝ) ^ (-(B / 4)))} with hA₁
  have hμA₁ : μ W L A₁ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D' + 1))) :=
    H₁ W hW₁ g L E s hWB hLC hE hs0 hsg
  set anc : Finset (Fin L) := univ.filter fun α : Fin L => IsAnchor n α with hanc
  set T : ℝ := (W : ℝ) ^ (4 : ℝ) with hT
  have hT0 : 0 < T := Real.rpow_pos_of_pos hx0 _
  set A₂ : Set (Ω W L) := ⋃ ab ∈ anc ×ˢ anc,
    {ω | T ≤ ‖blockOf (segG W x ω) ab.1 ab.2‖} with hA₂
  have hμA₂ : μ W L A₂ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D') / 2) := by
    have hone : ∀ ab : Fin L × Fin L,
        μ W L {ω | T ≤ ‖blockOf (segG W x ω) ab.1 ab.2‖} ≤
          ENNReal.ofReal (Cm * (g ^ 2 * y) ^ (-p) / T ^ p) := by
      intro ab
      obtain ⟨hint, hbd⟩ := Hm W hW4p L g (hCκr.trans hgC) h4L zu.re y u hre hy0 hyC₁ hu0
        hu1'.le ab.1 ab.2
      exact residualL_markov _ (fun ω => ‖blockOf (segG W x ω) ab.1 ab.2‖) p T _ hp hT0 hint
        (fun _ => norm_nonneg _) hbd
    have hcard : (((anc ×ˢ anc).card : ℕ) : ℝ) ≤ 36 * (W : ℝ) ^ (2 * (B + C)) := by
      have h6 := (card_cells_le_pow g B C W L hW1 hB0 (by linarith) hWB hLC).2
      rw [Finset.card_product, Nat.cast_mul]
      have hpow : ((W : ℝ) ^ (B + C)) ^ 2 = (W : ℝ) ^ (2 * (B + C)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; ring_nf
      have hc0 : (0 : ℝ) ≤ anc.card := Nat.cast_nonneg _
      calc (anc.card : ℝ) * anc.card ≤ (6 * (W : ℝ) ^ (B + C)) * (6 * (W : ℝ) ^ (B + C)) :=
            mul_le_mul h6 h6 hc0 (hc0.trans h6)
        _ = 36 * ((W : ℝ) ^ (B + C)) ^ 2 := by ring
        _ = 36 * (W : ℝ) ^ (2 * (B + C)) := by rw [hpow]
    have hy' : (Cχ * (W : ℝ) ^ (3 : ℝ))⁻¹ ≤ g ^ 2 * y := by
      have : (W : ℝ) ^ (3 : ℝ) = (W : ℝ) ^ 3 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [this]; exact hQy
    have harith := residualL_env_arith W B C D' Cm Cχ p (((anc ×ˢ anc).card : ℕ) : ℝ)
      (g ^ 2 * y) hx1 hpdef hp hCm (by linarith) hcard (mul_pos hgg hy0) hy' hE4
    calc μ W L A₂ ≤ ∑ ab ∈ anc ×ˢ anc,
          μ W L {ω | T ≤ ‖blockOf (segG W x ω) ab.1 ab.2‖} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ ab ∈ anc ×ˢ anc, ENNReal.ofReal (Cm * (g ^ 2 * y) ^ (-p) / T ^ p) :=
          Finset.sum_le_sum fun ab _ => hone ab
      _ = ENNReal.ofReal ((((anc ×ˢ anc).card : ℕ) : ℝ) * (Cm * (g ^ 2 * y) ^ (-p) / T ^ p)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D') / 2) := ENNReal.ofReal_le_ofReal harith
  have hμ : μ W L (A₁ ∪ A₂) ≤ ENNReal.ofReal ((W : ℝ) ^ (-D')) := by
    have h1 : (W : ℝ) ^ (-(D' + 1)) ≤ (W : ℝ) ^ (-D') / 2 := by
      rw [show -(D' + 1) = -D' + (-1) by ring, Real.rpow_add hx0, Real.rpow_neg_one]
      have : (W : ℝ)⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx2
      have hD0 : 0 ≤ (W : ℝ) ^ (-D') := (Real.rpow_pos_of_pos hx0 _).le
      calc (W : ℝ) ^ (-D') * (W : ℝ)⁻¹ ≤ (W : ℝ) ^ (-D') * (1 / 2) :=
            mul_le_mul_of_nonneg_left this hD0
        _ = (W : ℝ) ^ (-D') / 2 := by ring
    calc μ W L (A₁ ∪ A₂) ≤ μ W L A₁ + μ W L A₂ := measure_union_le _ _
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-D') / 2) :=
          add_le_add hμA₁ hμA₂
      _ = ENNReal.ofReal ((W : ℝ) ^ (-(D' + 1)) + (W : ℝ) ^ (-D') / 2) :=
          (ENNReal.ofReal_add (Real.rpow_pos_of_pos hx0 _).le
            (by have := Real.rpow_pos_of_pos hx0 (-D'); positivity)).symm
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal (by linarith)
  -- the deterministic errors on the good event
  set ε₀ : ℝ := (W : ℝ) ^ (-(B / 4)) with hε₀
  have hε₀0 : 0 < ε₀ := Real.rpow_pos_of_pos hx0 _
  have hzE' : ‖z - E‖ ≤ 2 * C₁ / g ^ 2 := by
    have e : z - E = ((zu.re - E : ℝ) : ℂ) + (y : ℂ) * Complex.I := by rw [hz]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hy0]
    calc |zu.re - E| + y ≤ C₁ / g ^ 2 + C₁ / g ^ 2 := add_le_add hxE hyC₁
      _ = 2 * C₁ / g ^ 2 := by ring
  have hnz : (n : ℝ) * ‖z - E‖ ≤ 2 * C₁ * (W : ℝ) ^ (-B) := by
    calc (n : ℝ) * ‖z - E‖ ≤ (g ^ 2 * (W : ℝ) ^ (-B)) * (2 * C₁ / g ^ 2) :=
          mul_le_mul hnhi hzE' (norm_nonneg _) (by positivity)
      _ = 2 * C₁ * (W : ℝ) ^ (-B) := by field_simp
  have hnz1 : (n : ℝ) * ‖z - E‖ ≤ 1 := hnz.trans hE1
  have hδB : Cδ * n * ‖z - E‖ ≤ ε₀ := by
    have hsplit : (W : ℝ) ^ (-B) = (W : ℝ) ^ (-(3 * B / 4)) * (W : ℝ) ^ (-(B / 4)) := by
      rw [← Real.rpow_add hx0]; ring_nf
    calc Cδ * n * ‖z - E‖ = Cδ * ((n : ℝ) * ‖z - E‖) := by ring
      _ ≤ Cδ * (2 * C₁ * (W : ℝ) ^ (-B)) := mul_le_mul_of_nonneg_left hnz hCδ.le
      _ = (2 * C₁ * Cδ * (W : ℝ) ^ (-(3 * B / 4))) * ε₀ := by rw [hsplit, hε₀]; ring
      _ ≤ 1 * ε₀ := mul_le_mul_of_nonneg_right hE2 hε₀0.le
      _ = ε₀ := one_mul _
  have hconj : ‖starRingEnd ℂ z - (E : ℂ)‖ = ‖z - (E : ℂ)‖ := by
    have : starRingEnd ℂ z - (E : ℂ) = starRingEnd ℂ (z - (E : ℂ)) := by
      rw [map_sub, Complex.conj_ofReal]
    rw [this, Complex.norm_conj]
  set ε : ℝ := ε₀ + Cδ * n * ‖z - E‖ with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hε2 : ε ≤ 2 * ε₀ := by linarith
  have hε1 : ε ≤ 1 := by linarith
  have hzim0 : z.im ≠ 0 := by rw [hzim]; exact hy0.ne'
  have hT4 : T = (W : ℝ) ^ 4 := by
    rw [hT, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hW4 : (1 : ℝ) ≤ (W : ℝ) ^ 4 := one_le_pow₀ hx1
  have hgood : ∀ ω, ω ∉ A₁ ∪ A₂ →
      CellClose n E z (V ω) ε ∧ CellClose n E (starRingEnd ℂ z) (V ω) ε ∧
        anchorEnv n (segG W x ω) ≤ T := by
    intro ω hω
    have hω1 : ω ∉ A₁ := fun h => hω (Or.inl h)
    have hω2 : ω ∉ A₂ := fun h => hω (Or.inr h)
    have hcl0 : CellClose n E (E : ℂ) (V ω) ε₀ := not_not.mp hω1
    have hε₀1 : ε₀ ≤ 1 := by linarith
    refine ⟨Hδ W L n E ε₀ z (V ω) hE hε₀0.le hε₀1 hnz1 hcl0, ?_, ?_⟩
    · have := Hδ W L n E ε₀ (starRingEnd ℂ z) (V ω) hE hε₀0.le hε₀1 (by rwa [hconj]) hcl0
      rwa [hconj] at this
    · have hlt : ∀ α β : Fin L, IsAnchor n α → IsAnchor n β →
          ‖blockOf (segG W x ω) α β‖ ≤ T := by
        intro α β hα hβ
        by_contra hcon
        exact hω2 (Set.mem_iUnion₂.mpr ⟨(α, β), Finset.mem_product.mpr
          ⟨by simp [hanc, hα], by simp [hanc, hβ]⟩, (not_le.mp hcon).le⟩)
      refine Real.iSup_le (fun ab => ?_) hT0.le
      obtain ⟨h1a, h2a⟩ := residual_anchor n ab.1
      obtain ⟨h1b, h2b⟩ := residual_anchor n ab.2
      unfold anchorNorm
      exact max_le (max_le (hlt _ _ h1a h1b) (hlt _ _ h1a h2b))
        (max_le (hlt _ _ h2a h1b) (hlt _ _ h2a h2b))
  have henv0 : ∀ ω, 0 ≤ anchorEnv n (segG W x ω) := fun ω =>
    residual_anchorEnv_nonneg n (by omega) _
  -- the trace and entry errors
  have hεenv : ∀ ω, ω ∉ A₁ ∪ A₂ → ε * (1 + anchorEnv n (segG W x ω)) ≤
      4 * ((W : ℝ) ^ 4 * ε₀) := by
    intro ω hω
    have h := (hgood ω hω).2.2
    rw [hT4] at h
    calc ε * (1 + anchorEnv n (segG W x ω)) ≤ (2 * ε₀) * (2 * (W : ℝ) ^ 4) :=
          mul_le_mul hε2 (by linarith) (by linarith [henv0 ω]) (by positivity)
      _ = 4 * ((W : ℝ) ^ 4 * ε₀) := by ring
  have hδ4 : δ ≤ Kδ * ((W : ℝ) ^ 4 * ε₀) := by
    refine hδb.trans (mul_le_mul_of_nonneg_left ?_ hKδ0)
    exact residual_mono W hx1 6 4 (-B) (-(B / 4)) (by push_cast; linarith)
  have hB4' : (4 : ℕ) + D + 1 ≤ B / 4 := by rw [hB4]; push_cast; linarith
  have hB20 : (20 : ℕ) + D + 1 ≤ B / 4 := by rw [hB4]; push_cast; linarith
  have hKT0 : 0 ≤ KT := by rw [hKT]; positivity
  have hKE0 : 0 ≤ KE := by rw [hKE]; positivity
  have hKR0 : 0 ≤ KR := by rw [hKR]; positivity
  have herrT : ∀ ω, ω ∉ A₁ ∪ A₂ → Cc * (ε * (1 + anchorEnv n (segG W x ω)) + δ) ≤
      (W : ℝ) ^ (-D) := by
    intro ω hω
    refine le_trans ?_ (residual_arith W 4 (B / 4) D KT hx1 hKT0 hB4' hET)
    have h1 := hεenv ω hω
    rw [hKT, ← hε₀]
    calc Cc * (ε * (1 + anchorEnv n (segG W x ω)) + δ) ≤
          Cc * (4 * ((W : ℝ) ^ 4 * ε₀) + Kδ * ((W : ℝ) ^ 4 * ε₀)) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 hδ4) hCc.le
      _ = Cc * (4 + Kδ) * ((W : ℝ) ^ 4 * ε₀) := by ring
  have herrE : ∀ ω, ω ∉ A₁ ∪ A₂ → Cc * ε * (1 + anchorEnv n (segG W x ω)) ≤ (W : ℝ) ^ (-D) := by
    intro ω hω
    refine le_trans ?_ (residual_arith W 4 (B / 4) D KE hx1 hKE0 hB4' hEE)
    have h1 := hεenv ω hω
    rw [hKE, ← hε₀]
    calc Cc * ε * (1 + anchorEnv n (segG W x ω)) = Cc * (ε * (1 + anchorEnv n (segG W x ω))) := by
          ring
      _ ≤ Cc * (4 * ((W : ℝ) ^ 4 * ε₀)) := mul_le_mul_of_nonneg_left h1 hCc.le
      _ = 4 * Cc * ((W : ℝ) ^ 4 * ε₀) := by ring
  -- the residual error
  have hsg' : s ≤ (g ^ 2)⁻¹ := by
    rw [hsdef, hγ]
    calc u * (g ^ 2)⁻¹ ≤ 1 * (g ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hu1'.le (by positivity)
      _ = (g ^ 2)⁻¹ := one_mul _
  have hWC : (1 : ℝ) ≤ (W : ℝ) ^ C := Real.one_le_rpow hx1 (by linarith)
  have hsL : s * L ≤ (W : ℝ) ^ C := by
    calc s * L ≤ (g ^ 2)⁻¹ * (g ^ 2 * (W : ℝ) ^ C) :=
          mul_le_mul hsg' hLC (Nat.cast_nonneg _) (by positivity)
      _ = (W : ℝ) ^ C := by field_simp
  have hsn : s * n ≤ ε₀ := by
    have h1 : s * n ≤ (W : ℝ) ^ (-B) := by
      calc s * n ≤ (g ^ 2)⁻¹ * (g ^ 2 * (W : ℝ) ^ (-B)) :=
            mul_le_mul hsg' hnhi (Nat.cast_nonneg _) (by positivity)
        _ = (W : ℝ) ^ (-B) := by field_simp
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  have hδL : δ * (1 + s * L) ≤ 2 * Kδ * ε₀ := by
    have h1 : δ * (1 + s * L) ≤ Kδ * ((W : ℝ) ^ 6 * (W : ℝ) ^ (-B)) * (2 * (W : ℝ) ^ C) :=
      mul_le_mul hδb (by linarith) (by positivity) (by positivity)
    have h2 : (W : ℝ) ^ 6 * (W : ℝ) ^ (C + -B) ≤ (W : ℝ) ^ (0 : ℕ) * ε₀ :=
      residual_mono W hx1 6 0 (C + -B) (-(B / 4)) (by push_cast; linarith)
    rw [pow_zero, one_mul, Real.rpow_add hx0] at h2
    calc δ * (1 + s * L) ≤ Kδ * ((W : ℝ) ^ 6 * (W : ℝ) ^ (-B)) * (2 * (W : ℝ) ^ C) := h1
      _ = 2 * Kδ * ((W : ℝ) ^ 6 * ((W : ℝ) ^ C * (W : ℝ) ^ (-B))) := by ring
      _ ≤ 2 * Kδ * ε₀ := mul_le_mul_of_nonneg_left h2 (by positivity)
  have herrR : ∀ ω, ω ∉ A₁ ∪ A₂ →
      Cr * (1 + Γ) ^ 2 * (1 + anchorEnv n (segG W x ω)) ^ 2 * (ε + δ * (1 + s * L) + s * n) ≤
        (W : ℝ) ^ (-D) := by
    intro ω hω
    refine le_trans ?_ (residual_arith W 20 (B / 4) D KR hx1 hKR0 hB20 hER)
    have henv := (hgood ω hω).2.2
    rw [hT4] at henv
    have hS : ε + δ * (1 + s * L) + s * n ≤ (3 + 2 * Kδ) * ε₀ := by linarith
    have hΓ2 : (1 + Γ) ^ 2 ≤ KΓ ^ 2 * (W : ℝ) ^ 12 := by
      have h0 : 0 ≤ 1 + Γ := by rw [hΓdef]; positivity
      calc (1 + Γ) ^ 2 ≤ (KΓ * (W : ℝ) ^ 6) ^ 2 := pow_le_pow_left₀ h0 hΓb 2
        _ = KΓ ^ 2 * (W : ℝ) ^ 12 := by ring
    have hA2 : (1 + anchorEnv n (segG W x ω)) ^ 2 ≤ 4 * (W : ℝ) ^ 8 := by
      have h0 : 0 ≤ 1 + anchorEnv n (segG W x ω) := by linarith [henv0 ω]
      calc (1 + anchorEnv n (segG W x ω)) ^ 2 ≤ (2 * (W : ℝ) ^ 4) ^ 2 :=
            pow_le_pow_left₀ h0 (by linarith) 2
        _ = 4 * (W : ℝ) ^ 8 := by ring
    have hS0 : 0 ≤ ε + δ * (1 + s * L) + s * n := by
      have : 0 ≤ s * L := by positivity
      have : 0 ≤ s * n := by positivity
      have : 0 ≤ δ * (1 + s * L) := by positivity
      linarith
    rw [hKR, ← hε₀]
    calc Cr * (1 + Γ) ^ 2 * (1 + anchorEnv n (segG W x ω)) ^ 2 * (ε + δ * (1 + s * L) + s * n)
        ≤ Cr * (KΓ ^ 2 * (W : ℝ) ^ 12) * (4 * (W : ℝ) ^ 8) * ((3 + 2 * Kδ) * ε₀) := by
          have n1 : 0 ≤ Cr * (KΓ ^ 2 * (W : ℝ) ^ 12) :=
            mul_nonneg hCr.le (mul_nonneg (sq_nonneg _) (pow_nonneg hx0.le _))
          have n2 : 0 ≤ Cr * (KΓ ^ 2 * (W : ℝ) ^ 12) * (4 * (W : ℝ) ^ 8) :=
            mul_nonneg n1 (mul_nonneg (by norm_num) (pow_nonneg hx0.le _))
          have h1 : Cr * (1 + Γ) ^ 2 ≤ Cr * (KΓ ^ 2 * (W : ℝ) ^ 12) :=
            mul_le_mul_of_nonneg_left hΓ2 hCr.le
          have h2 : Cr * (1 + Γ) ^ 2 * (1 + anchorEnv n (segG W x ω)) ^ 2 ≤
              Cr * (KΓ ^ 2 * (W : ℝ) ^ 12) * (4 * (W : ℝ) ^ 8) :=
            mul_le_mul h1 hA2 (sq_nonneg _) n1
          exact mul_le_mul h2 hS hS0 n2
      _ = Cr * KΓ ^ 2 * 4 * (3 + 2 * Kδ) * ((W : ℝ) ^ 20 * ε₀) := by ring
  -- the three sampling bounds
  have hCs' : ∀ A : ℝ, 0 ≤ A → (4 / κ) ^ 2 * A ≤ Cs * A := fun A hA =>
    mul_le_mul_of_nonneg_right hCs4 hA
  refine ⟨?_, ?_, ?_⟩
  · refine sampleBound_of_norming _ _ _ _ _ _ _ _ hμ fun ω hω l => ?_
    obtain ⟨hcl, hcl', -⟩ := hgood ω hω
    have hGω := hG ω
    have hX : ∀ a b, blockTr (segG W x ω - segM W x) a b =
        blockTr (resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) +
          blockDiagOp (V ω)) z) a b - M a b := by
      intro a b
      unfold segM
      rw [residual_blockTr_sub, residual_blockTr_kron W L hW1, hGω]
    have hcen := (Hc W L n E ε δ z (V ω) M hW1 hL3 hn1 hE (hV ω) hzim0 hε0 hε1 hcl hcl' hMs hRI
      l.1 l.2).1
    rw [← hGω] at hcen
    set A := ⨆ t : anchorPairs n L, ‖blockTr (segG W x ω - segM W x) (t : Fin L × Fin L).1
      (t : Fin L × Fin L).2‖ / 1 with hAdef
    have hA0 : 0 ≤ A := residual_iSup_nonneg (anchorPairs n L)
      (fun t => ‖blockTr (segG W x ω - segM W x) t.1 t.2‖) fun _ => norm_nonneg _
    have hnorm := residual_norming hκ hκ2 hE n
      (fun α β => blockTr (segG W x ω) α β - M α β) A ((W : ℝ) ^ (-D)) hA0
      (fun α β hα hβ => by
        have := residual_le_iSup (anchorPairs n L)
          (fun t => ‖blockTr (segG W x ω - segM W x) t.1 t.2‖) (α, β)
          (by simp [anchorPairs, hα, hβ])
        simp only at this
        rw [hX, ← hGω] at this
        exact this) l.1 l.2 (hcen.trans (herrT ω hω))
    rw [div_one, hX, ← hGω]
    have hfin : (4 / κ) ^ 2 * A + (W : ℝ) ^ (-D) ≤ Cs * A + (W : ℝ) ^ (-D) := by
      linarith [hCs' A hA0]
    exact hnorm.trans hfin
  · refine sampleBound_of_norming _ _ _ _ _ _ _ _ hμ fun ω hω l => ?_
    obtain ⟨hcl, hcl', -⟩ := hgood ω hω
    have hGω := hG ω
    obtain ⟨⟨a, i⟩, ⟨b, j⟩⟩ := l
    have hcen := (Hc W L n E ε δ z (V ω) M hW1 hL3 hn1 hE (hV ω) hzim0 hε0 hε1 hcl hcl' hMs hRI
      a b).2 i j
    rw [← hGω] at hcen
    set A := ⨆ t : anchorEntries n W L,
      ‖segG W x ω (t : (Fin L × Fin W) × (Fin L × Fin W)).1
          (t : (Fin L × Fin W) × (Fin L × Fin W)).2 -
        if (t : (Fin L × Fin W) × (Fin L × Fin W)).1.2 = (t : (Fin L × Fin W) × (Fin L × Fin W)).2.2
        then blockTr (segG W x ω) (t : (Fin L × Fin W) × (Fin L × Fin W)).1.1
          (t : (Fin L × Fin W) × (Fin L × Fin W)).2.1 else 0‖ / 1 with hAdef
    have hA0 : 0 ≤ A := residual_iSup_nonneg (anchorEntries n W L)
      (fun t : (Fin L × Fin W) × (Fin L × Fin W) => ‖segG W x ω t.1 t.2 -
        if t.1.2 = t.2.2 then blockTr (segG W x ω) t.1.1 t.2.1 else 0‖) fun _ => norm_nonneg _
    have hnorm := residual_norming hκ hκ2 hE n
      (fun α β => segG W x ω (α, i) (β, j) - if i = j then blockTr (segG W x ω) α β else 0)
      A ((W : ℝ) ^ (-D)) hA0
      (fun α β hα hβ => by
        have := residual_le_iSup (anchorEntries n W L)
          (fun t : (Fin L × Fin W) × (Fin L × Fin W) => ‖segG W x ω t.1 t.2 -
            if t.1.2 = t.2.2 then blockTr (segG W x ω) t.1.1 t.2.1 else 0‖) ((α, i), (β, j))
          (by simp [anchorEntries, hα, hβ])
        simpa only using this) a b (hcen.trans (herrE ω hω))
    rw [div_one]
    have hfin : (4 / κ) ^ 2 * A + (W : ℝ) ^ (-D) ≤ Cs * A + (W : ℝ) ^ (-D) := by
      linarith [hCs' A hA0]
    exact hnorm.trans hfin
  · refine sampleBound_of_norming _ _ _ _ _ _ _ _ hμ fun ω hω l => ?_
    obtain ⟨hcl, hcl', -⟩ := hgood ω hω
    have hGω := hG ω
    have hid : ∀ a b, segRes W x ω a b = resComb s (segG W x ω) M a b := fun a b =>
      segRes_identity W hW1 x hg0.le hL3 hupos hy0 ω a b
    have hres := Hr W L n E ε δ s Γ z (V ω) M hW1 hL3 hn1 hE (hV ω) hzim0 hε0 hε1 hδ0 hs0 hcl
      hcl' hMs hRI hMe hMr l.1 l.2
    rw [← hGω] at hres
    set A := ⨆ t : anchorPairs n L, ‖segRes W x ω (t : Fin L × Fin L).1 (t : Fin L × Fin L).2‖ / 1
      with hAdef
    have hA0 : 0 ≤ A := residual_iSup_nonneg (anchorPairs n L)
      (fun t => ‖segRes W x ω t.1 t.2‖) fun _ => norm_nonneg _
    have hnorm := residual_norming hκ hκ2 hE n (fun α β => resComb s (segG W x ω) M α β) A
      ((W : ℝ) ^ (-D)) hA0
      (fun α β hα hβ => by
        have := residual_le_iSup (anchorPairs n L) (fun t => ‖segRes W x ω t.1 t.2‖) (α, β)
          (by simp [anchorPairs, hα, hβ])
        simp only at this
        rw [hid] at this
        exact this) l.1 l.2 (hres.trans (herrR ω hω))
    rw [div_one, hid]
    have hfin : (4 / κ) ^ 2 * A + (W : ℝ) ^ (-D) ≤ Cs * A + (W : ℝ) ^ (-D) := by
      linarith [hCs' A hA0]
    exact hnorm.trans hfin

/-- Lemma 5.10(b) [fo:lem:sampling-continuity], last paragraph, at a fixed admissible point
`(u, z)`, `z = Re z_u + iy`, `η_u ≤ y ≤ C/g²`, for `g² ≥ W^B`: centered block traces, traceless
entries and residuals satisfy (5.34) [fo:eq:weighted-sampling-input] with `w = 1` and the anchor
sample sets (the Remark of Section 7.4 [sec:sampling-propagation-extensions] and Proposition 7.10
[uvc:prop:residual-compression]). -/
theorem pair_sampling (κ C : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 1 < C) (D D' : ℝ)
    (hD : 0 < D) (hD' : 0 < D') :
    ∃ B Cκ Cs : ℝ, 2 < B ∧ 1 ≤ Cκ ∧ 1 ≤ Cs ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x : FlowPt × ℝ,
      Cκ ≤ x.1.g → (W : ℝ) ^ B ≤ x.1.g ^ 2 → 4 * x.1.g ^ 2 ≤ x.1.L →
      (x.1.L : ℝ) ≤ x.1.g ^ 2 * (W : ℝ) ^ C → |x.1.E| ≤ 2 - κ →
      IsDysonRootV (hopB x.1.g) (gammaG x.1.g) x.1.L x.1.E (mRoot x.1.g x.1.L x.1.E) →
      ‖mRoot x.1.g x.1.L x.1.E‖ ≤ C → C⁻¹ ≤ (mRoot x.1.g x.1.L x.1.E).im → 1 / 2 ≤ x.1.u →
      (W : ℝ) ^ (-3 : ℝ) ≤ 1 - x.1.u → etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u ≤ x.2 →
      x.2 ≤ C / x.1.g ^ 2 →
        SampleBound (μ W x.1.L) (fun ab ω => blockTr (segG W x ω - segM W x) ab.1 ab.2)
          (fun _ => 1) (anchorPairs (cellLen x.1.g W B) x.1.L) Cs ((W : ℝ) ^ (-D))
          ((W : ℝ) ^ (-D')) ∧
        SampleBound (μ W x.1.L) (fun e ω => segG W x ω e.1 e.2 -
            if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0)
          (fun _ => 1) (anchorEntries (cellLen x.1.g W B) W x.1.L) Cs ((W : ℝ) ^ (-D))
          ((W : ℝ) ^ (-D')) ∧
        SampleBound (μ W x.1.L) (fun ab ω => segRes W x ω ab.1 ab.2)
          (fun _ => 1) (anchorPairs (cellLen x.1.g W B) x.1.L) Cs ((W : ℝ) ^ (-D))
          ((W : ℝ) ^ (-D')) := by
  exact residual_pair_sampling κ C hκ hκ2 hC D D' hD hD'

/-- `anchorPairs` is the product of the anchors with themselves. -/
private lemma residual_anchorPairs_eq (n L : ℕ) :
    anchorPairs n L = (univ.filter fun α : Fin L => IsAnchor n α) ×ˢ
      (univ.filter fun α : Fin L => IsAnchor n α) := by
  ext ab; simp [anchorPairs]

/-- `anchorEntries` is the product of the anchor sites with themselves. -/
private lemma residual_anchorEntries_eq (n W L : ℕ) :
    anchorEntries n W L =
      ((univ.filter fun α : Fin L => IsAnchor n α) ×ˢ (univ : Finset (Fin W))) ×ˢ
      ((univ.filter fun α : Fin L => IsAnchor n α) ×ˢ (univ : Finset (Fin W))) := by
  ext e; simp [anchorEntries]

/-- At a reached point with `g² ≥ W^B`: `W ≤ g`, `g ≥ 1`, `4g² ≤ L` and `L ≤ g²W^{C}` for
`C ≥ 3`, `W ≥ max(3, 2C_V)`, `ρ(W) ≥ 4`. -/
private lemma residual_reach_facts (W : ℕ) (hW3 : 3 ≤ W) (B C CV : ℝ) (hB : 2 < B) (hC : 3 ≤ C)
    (hWCV : 2 * CV ≤ (W : ℝ)) (ρW : ℝ) (hρ4 : 4 ≤ ρW) (g : ℝ) (L : ℕ) (hg0 : 0 < g)
    (hbr : (W : ℝ) ^ B ≤ g ^ 2) (hLlog : ρW * g ^ 2 * Real.log W ≤ L)
    (hLV : (L : ℝ) ≤ 2 * CV * g ^ 2 * (W : ℝ) ^ 2) :
    (W : ℝ) ≤ g ∧ 4 * g ^ 2 ≤ L ∧ (L : ℝ) ≤ g ^ 2 * (W : ℝ) ^ C := by
  have hx0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hx1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hx3 : (3 : ℝ) ≤ W := by exact_mod_cast hW3
  have hWg : (W : ℝ) ≤ g := by
    have h2 : (W : ℝ) ^ (2 : ℝ) ≤ (W : ℝ) ^ B := Real.rpow_le_rpow_of_exponent_le hx1 hB.le
    rw [Real.rpow_two] at h2
    nlinarith
  have hlog : 1 ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  refine ⟨hWg, ?_, ?_⟩
  · have hg2 : 0 ≤ g ^ 2 := sq_nonneg _
    have h1 : 4 ≤ ρW * Real.log W := by nlinarith
    calc 4 * g ^ 2 ≤ (ρW * Real.log W) * g ^ 2 := by gcongr
      _ = ρW * g ^ 2 * Real.log W := by ring
      _ ≤ L := hLlog
  · have h3 : (W : ℝ) ^ (3 : ℝ) ≤ (W : ℝ) ^ C := Real.rpow_le_rpow_of_exponent_le hx1 hC
    have h3' : (W : ℝ) ^ (3 : ℝ) = (W : ℝ) ^ 2 * W := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hg2 : 0 ≤ g ^ 2 := sq_nonneg _
    calc (L : ℝ) ≤ 2 * CV * g ^ 2 * (W : ℝ) ^ 2 := hLV
      _ ≤ W * g ^ 2 * (W : ℝ) ^ 2 := by gcongr
      _ = g ^ 2 * (W : ℝ) ^ (3 : ℝ) := by rw [h3']; ring
      _ ≤ g ^ 2 * (W : ℝ) ^ C := by gcongr

/-- In the exact branch `g² < W^B`: `L ≤ 2C_V W^{B+2}`. -/
private lemma residual_exact_L (W : ℕ) (hW1 : 1 ≤ W) (B CV : ℝ) (g : ℝ) (L : ℕ)
    (hbr : g ^ 2 < (W : ℝ) ^ B) (hLV : (L : ℝ) ≤ 2 * CV * g ^ 2 * (W : ℝ) ^ 2) (hCV : 0 < CV) :
    (L : ℝ) ≤ 2 * CV * (W : ℝ) ^ B * (W : ℝ) ^ 2 := by
  calc (L : ℝ) ≤ 2 * CV * g ^ 2 * (W : ℝ) ^ 2 := hLV
    _ ≤ 2 * CV * (W : ℝ) ^ B * (W : ℝ) ^ 2 := by gcongr

/-- `(c W^a)^k ≤ W^{(a + 3)k}` for `c ≤ W³`. -/
private lemma residual_pow_card (W : ℕ) (hW1 : 1 ≤ W) (a c : ℝ)
    (hc : c ≤ (W : ℝ) ^ (3 : ℝ)) (k : ℕ) (X : ℝ) (hX0 : 0 ≤ X) (hX : X ≤ c * (W : ℝ) ^ a) :
    X ^ k ≤ (W : ℝ) ^ (k * (a + 3)) := by
  have hx0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have h1 : X ≤ (W : ℝ) ^ (a + 3) := by
    rw [Real.rpow_add hx0]
    calc X ≤ c * (W : ℝ) ^ a := hX
      _ ≤ (W : ℝ) ^ (3 : ℝ) * (W : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right hc (Real.rpow_pos_of_pos hx0 _).le
      _ = (W : ℝ) ^ a * (W : ℝ) ^ (3 : ℝ) := by ring
  calc X ^ k ≤ ((W : ℝ) ^ (a + 3)) ^ k := pow_le_pow_left₀ hX0 h1 k
    _ = (W : ℝ) ^ (k * (a + 3)) := by
        rw [mul_comm, Real.rpow_mul_natCast hx0.le]

/-- Lemma 5.10(b) [fo:lem:sampling-continuity] part (1) with Lemma 5.8
[uvc:thm:ordinary-sampling] at the points reached from a base family at large coupling. -/
private theorem residual_loops (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) (J : ℕ)
    (C'' : ℝ) (hC'' : 1 ≤ C'') (Cκ : ℝ) (hCκ : 1 ≤ Cκ) (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop atTop)
    (base : ℕ → Set FlowPt) (W₂ : ℕ)
    (HR : ∀ W : ℕ, W₂ ≤ W → ∀ d p, d ≤ J → CmpReach base W d p →
      Cκ / Real.sqrt 2 ≤ p.g ∧ |p.E| ≤ 2 - κ / 2 ∧
      IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ∧
      C''⁻¹ ≤ (mRoot p.g p.L p.E).im ∧ ‖mRoot p.g p.L p.E‖ ≤ C'' ∧
      ρ W * p.g ^ 2 * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ 2 * CV * p.g ^ 2 * (W : ℝ) ^ 2 ∧
      1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u)
    (k : ℕ) (hk : 1 ≤ k) (cw θ F : ℝ) (hcw : 0 < cw) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hF : 0 < F)
    (D D' : ℝ) (hD : 0 < D) (hD' : 0 < D') :
    ∃ CS Cs : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J → CmpReach base W d p →
      ∃ S : Finset (Fin k → Fin p.L), (S.card : ℝ) ≤ (W : ℝ) ^ CS ∧
        ∀ (σ : Fin k → Bool) (u : ℝ), 0 ≤ u → u ≤ p.u →
          SampleBound (μ W p.L) (fun a ω => loopTr (flowG W ⟨p.g, p.E, p.L, u⟩ ω) a σ)
            (fun _ => 1) S Cs ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) ∧
          SampleBound (μ W p.L) (fun a ω => flowErr W ⟨p.g, p.E, p.L, u⟩ a σ ω)
            (fun _ => 1) S Cs ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) ∧
          SampleBound (μ W p.L) (fun a ω => loopTr (flowG W ⟨p.g, p.E, p.L, u⟩ ω) a σ)
            (fun a => weightFn cw θ F W (ellProp p.g p.L u) (wordDiam a)) S Cs
            ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) ∧
          SampleBound (μ W p.L) (fun a ω => flowErr W ⟨p.g, p.E, p.L, u⟩ a σ ω)
            (fun a => weightFn cw θ F W (ellProp p.g p.L u) (wordDiam a)) S Cs
            ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) := by
  set C₃ : ℝ := max 3 (C'' + 1) with hC₃def
  have hC₃3 : 3 ≤ C₃ := le_max_left _ _
  have hC''C₃ : C'' ≤ C₃ := by have := le_max_right 3 (C'' + 1); linarith
  obtain ⟨B, Cκl, hB, -, W₀l, HL⟩ := loop_sampling (κ / 2) C₃ (by linarith) (by linarith)
    (by linarith) k hk cw θ F D D' hcw hθ hθ2 hF hD hD'
  refine ⟨k * (B + C₃ + 3), 2 * 6 ^ k, ?_⟩
  have hev : ∀ᶠ W : ℕ in atTop, ((W₂ ≤ W ∧ W₀l ≤ W) ∧ 3 ≤ W) ∧
      (Cκl ≤ (W : ℝ) ∧ 2 * CV ≤ (W : ℝ)) ∧ 4 ≤ ρ W :=
    (((eventually_ge_atTop W₂).and (eventually_ge_atTop W₀l)).and (eventually_ge_atTop 3)).and
      (((tendsto_natCast_atTop_atTop.eventually_ge_atTop Cκl).and
        (tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * CV))).and
        (hρ.eventually_ge_atTop 4))
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp hev
  refine ⟨W₀, fun W hW d p hd hreach => ?_⟩
  obtain ⟨⟨⟨hW₂, hW₀l⟩, hW3⟩, ⟨hWκ, hWCV⟩, hρ4⟩ := hW₀ W hW
  obtain ⟨hgp, hEp, hroot, hmim, hmC, hLlog, hLV, hu12, hut⟩ := HR W hW₂ d p hd hreach
  have hW1 : 1 ≤ W := by omega
  have hx0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hx1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hx3 : (3 : ℝ) ≤ W := by exact_mod_cast hW3
  have h27 : (27 : ℝ) ≤ (W : ℝ) ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : (3 : ℝ) ^ 3 ≤ (W : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hx3 3
    norm_num at this; linarith
  have hg0 : 0 < p.g :=
    lt_of_lt_of_le (div_pos (by linarith) (Real.sqrt_pos.mpr two_pos)) hgp
  have hpu : p.u < 1 := by have := Real.rpow_pos_of_pos hx0 (-3 : ℝ); linarith
  have hwpos : ∀ (ℓ : ℝ) (r : ℝ), 0 < weightFn cw θ F W ℓ r := fun ℓ r =>
    (Real.rpow_pos_of_pos hx0 _).trans_le (residualL_weight_ge _ _ _ _ _ _)
  have hCs1 : (1 : ℝ) ≤ 2 * 6 ^ k := by
    have : (1 : ℝ) ≤ 6 ^ k := one_le_pow₀ (by norm_num)
    linarith
  by_cases hbr : (W : ℝ) ^ B ≤ p.g ^ 2
  · obtain ⟨hWg, h4L, hLV'⟩ := residual_reach_facts W hW3 B C₃ CV hB hC₃3 hWCV (ρ W) hρ4 p.g p.L
      hg0 hbr hLlog hLV
    have hg1 : 1 ≤ p.g := hx1.trans hWg
    refine ⟨loopSampleSet (cellLen p.g W B) p.E p.L k, ?_, fun σ u hu0 hup => ?_⟩
    · have hc := card_loopSampleSet_le (cellLen p.g W B) (le_max_left _ _) p.E p.L k
      have hcells := residualL_cells p.g B C₃ W p.L hW1 (by linarith) (by linarith) hbr hLV'
      have hn0 : 0 ≤ (p.L : ℝ) / cellLen p.g W B + 1 := by positivity
      have h6 : 6 ^ k * ((p.L : ℝ) / cellLen p.g W B + 1) ^ k =
          (6 * ((p.L : ℝ) / cellLen p.g W B + 1)) ^ k := by rw [mul_pow]
      have hle : 6 * ((p.L : ℝ) / cellLen p.g W B + 1) ≤ 18 * (W : ℝ) ^ (B + C₃) := by linarith
      have := residual_pow_card W hW1 (B + C₃) 18 (by linarith) k _ (by positivity)
        hle
      rw [show k * (B + C₃ + 3) = (k : ℝ) * (B + C₃ + 3) by rfl]
      linarith
    · have hu3 : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - u := by linarith
      have hl := HL W hW₀l p.g p.L p.E (hWκ.trans hWg) hbr h4L hLV' hEp hroot (hmC.trans hC''C₃)
        ((inv_anti₀ (by linarith) hC''C₃).trans hmim) σ u hu0 hu3
      have hℓ := residualL_ellProp p.g hg1 p.L (by linarith) u hu0 (by linarith)
      exact ⟨hl.1, hl.2.1, (hl.2.2 _ hℓ).1, (hl.2.2 _ hℓ).2⟩
  · have hbr' : p.g ^ 2 < (W : ℝ) ^ B := not_le.mp hbr
    refine ⟨Finset.univ, ?_, fun σ u _ _ => ⟨sampleBound_univ _ _ _ (fun _ => zero_le_one) hCs1
      (Real.rpow_pos_of_pos hx0 _).le _, sampleBound_univ _ _ _ (fun _ => zero_le_one) hCs1
      (Real.rpow_pos_of_pos hx0 _).le _, sampleBound_univ _ _ _ (fun _ => (hwpos _ _).le) hCs1
      (Real.rpow_pos_of_pos hx0 _).le _, sampleBound_univ _ _ _ (fun _ => (hwpos _ _).le) hCs1
      (Real.rpow_pos_of_pos hx0 _).le _⟩⟩
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
    have hLb := residual_exact_L W hW1 B CV p.g p.L hbr' hLV hCV
    have hle : (p.L : ℝ) ≤ 1 * (W : ℝ) ^ (B + C₃) := by
      have h2 : (W : ℝ) ^ B * (W : ℝ) ^ 2 * W ≤ (W : ℝ) ^ (B + C₃) := by
        have e : (W : ℝ) ^ B * (W : ℝ) ^ 2 * W = (W : ℝ) ^ (B + 3) := by
          rw [Real.rpow_add hx0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          ring
        rw [e]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have hWB0 : 0 ≤ (W : ℝ) ^ B * (W : ℝ) ^ 2 := by positivity
      calc (p.L : ℝ) ≤ 2 * CV * (W : ℝ) ^ B * (W : ℝ) ^ 2 := hLb
        _ = (2 * CV) * ((W : ℝ) ^ B * (W : ℝ) ^ 2) := by ring
        _ ≤ W * ((W : ℝ) ^ B * (W : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hWCV hWB0
        _ = (W : ℝ) ^ B * (W : ℝ) ^ 2 * W := by ring
        _ ≤ 1 * (W : ℝ) ^ (B + C₃) := by linarith
    have := residual_pow_card W hW1 (B + C₃) 1 (by linarith) k _ (Nat.cast_nonneg _)
      hle
    rw [show k * (B + C₃ + 3) = (k : ℝ) * (B + C₃ + 3) by rfl]
    linarith

/-- Lemma 5.10(b) [fo:lem:sampling-continuity] part (2), last paragraph, at the admissible pairs
of a base family at large coupling. -/
private theorem residual_pairs (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) (J : ℕ)
    (C'' C' : ℝ) (hC'' : 1 ≤ C'') (Cκ : ℝ) (hCκ : 1 ≤ Cκ) (ρ : ℕ → ℝ)
    (hρ : Tendsto ρ atTop atTop) (base : ℕ → Set FlowPt) (W₂ W₃ : ℕ)
    (HR : ∀ W : ℕ, W₂ ≤ W → ∀ d p, d ≤ J → CmpReach base W d p →
      Cκ / Real.sqrt 2 ≤ p.g ∧ |p.E| ≤ 2 - κ / 2 ∧
      IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ∧
      C''⁻¹ ≤ (mRoot p.g p.L p.E).im ∧ ‖mRoot p.g p.L p.E‖ ≤ C'' ∧
      ρ W * p.g ^ 2 * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ 2 * CV * p.g ^ 2 * (W : ℝ) ^ 2 ∧
      1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u)
    (HS : ∀ W : ℕ, W₃ ≤ W → ∀ x : FlowPt × ℝ, SegAdm base J W x →
      etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u ≤ x.2 ∧ x.2 ≤ C' / x.1.g ^ 2)
    (D D' : ℝ) (hD : 0 < D) (hD' : 0 < D') :
    ∃ CS Cs : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x,
      SegAdm base J W x → ∃ (S₁ : Finset (Fin x.1.L × Fin x.1.L))
        (S₂ : Finset ((Fin x.1.L × Fin W) × (Fin x.1.L × Fin W))),
        (S₁.card : ℝ) ≤ (W : ℝ) ^ CS ∧ (S₂.card : ℝ) ≤ (W : ℝ) ^ CS ∧
        SampleBound (μ W x.1.L) (fun ab ω => blockTr (segG W x ω - segM W x) ab.1 ab.2)
          (fun _ => 1) S₁ Cs ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) ∧
        SampleBound (μ W x.1.L) (fun e ω => segG W x ω e.1 e.2 -
            if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0)
          (fun _ => 1) S₂ Cs ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) ∧
        SampleBound (μ W x.1.L) (fun ab ω => segRes W x ω ab.1 ab.2)
          (fun _ => 1) S₁ Cs ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) := by
  set C₄ : ℝ := max 3 (max (C'' + 1) C') with hC₄def
  have hC₄3 : 3 ≤ C₄ := le_max_left _ _
  have hC''C₄ : C'' ≤ C₄ := by
    have := le_trans (le_max_left (C'' + 1) C') (le_max_right 3 (max (C'' + 1) C')); linarith
  have hC'C₄ : C' ≤ C₄ := le_trans (le_max_right (C'' + 1) C') (le_max_right _ _)
  obtain ⟨B, Cκp, Cs, hB, -, hCs, W₀p, HP⟩ := pair_sampling (κ / 2) C₄ (by linarith)
    (by linarith) (by linarith) D D' hD hD'
  refine ⟨2 * B + 2 * C₄ + 8, Cs, ?_⟩
  have hev : ∀ᶠ W : ℕ in atTop, (((W₂ ≤ W ∧ W₃ ≤ W) ∧ W₀p ≤ W) ∧ 3 ≤ W) ∧
      (Cκp ≤ (W : ℝ) ∧ 2 * CV ≤ (W : ℝ)) ∧ 4 ≤ ρ W :=
    ((((eventually_ge_atTop W₂).and (eventually_ge_atTop W₃)).and
      (eventually_ge_atTop W₀p)).and (eventually_ge_atTop 3)).and
      (((tendsto_natCast_atTop_atTop.eventually_ge_atTop Cκp).and
        (tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * CV))).and
        (hρ.eventually_ge_atTop 4))
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp hev
  refine ⟨W₀, fun W hW x hx => ?_⟩
  obtain ⟨⟨⟨⟨hW₂, hW₃⟩, hW₀p⟩, hW3⟩, ⟨hWκ, hWCV⟩, hρ4⟩ := hW₀ W hW
  obtain ⟨hyη, hyC⟩ := HS W hW₃ x hx
  obtain ⟨d, hd, hreach, -⟩ := hx
  obtain ⟨hgp, hEp, hroot, hmim, hmC, hLlog, hLV, hu12, hut⟩ := HR W hW₂ d x.1 hd hreach
  have hW1 : 1 ≤ W := by omega
  have hx0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hx1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hx3 : (3 : ℝ) ≤ W := by exact_mod_cast hW3
  have hg0 : 0 < x.1.g :=
    lt_of_lt_of_le (div_pos (by linarith) (Real.sqrt_pos.mpr two_pos)) hgp
  have hgg : 0 < x.1.g ^ 2 := by positivity
  have hW2r : (W : ℝ) ^ (2 : ℝ) = (W : ℝ) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h81 : (36 : ℝ) ≤ (W : ℝ) ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : (3 : ℝ) ^ 4 ≤ (W : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hx3 4
    norm_num at this; linarith
  by_cases hbr : (W : ℝ) ^ B ≤ x.1.g ^ 2
  · obtain ⟨hWg, h4L, hLV'⟩ := residual_reach_facts W hW3 B C₄ CV hB hC₄3 hWCV (ρ W) hρ4 x.1.g
      x.1.L hg0 hbr hLlog hLV
    refine ⟨anchorPairs (cellLen x.1.g W B) x.1.L, anchorEntries (cellLen x.1.g W B) W x.1.L, ?_,
      ?_, HP W hW₀p x (hWκ.trans hWg) hbr h4L hLV' hEp hroot (hmC.trans hC''C₄)
        ((inv_anti₀ (by linarith) hC''C₄).trans hmim) hu12 hut hyη
        (hyC.trans (div_le_div_of_nonneg_right hC'C₄ hgg.le))⟩
    · have h6 := (card_cells_le_pow x.1.g B C₄ W x.1.L hW1 (by linarith) (by linarith) hbr hLV').2
      rw [residual_anchorPairs_eq, Finset.card_product, Nat.cast_mul]
      have hc0 : (0 : ℝ) ≤ (univ.filter fun α : Fin x.1.L => IsAnchor (cellLen x.1.g W B) α).card :=
        Nat.cast_nonneg _
      have hpow : (W : ℝ) ^ (B + C₄) * (W : ℝ) ^ (B + C₄) * (W : ℝ) ^ (4 : ℝ) ≤
          (W : ℝ) ^ (2 * B + 2 * C₄ + 8) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have hWBC : 0 ≤ (W : ℝ) ^ (B + C₄) := (Real.rpow_pos_of_pos hx0 _).le
      calc _ ≤ (6 * (W : ℝ) ^ (B + C₄)) * (6 * (W : ℝ) ^ (B + C₄)) :=
            mul_le_mul h6 h6 hc0 (hc0.trans h6)
        _ = 36 * ((W : ℝ) ^ (B + C₄) * (W : ℝ) ^ (B + C₄)) := by ring
        _ ≤ (W : ℝ) ^ (4 : ℝ) * ((W : ℝ) ^ (B + C₄) * (W : ℝ) ^ (B + C₄)) :=
            mul_le_mul_of_nonneg_right h81 (by positivity)
        _ ≤ _ := by linarith
    · have h6 := (card_cells_le_pow x.1.g B C₄ W x.1.L hW1 (by linarith) (by linarith) hbr hLV').2
      rw [residual_anchorEntries_eq, Finset.card_product, Finset.card_product, Finset.card_univ,
        Fintype.card_fin]
      push_cast
      set a := ((univ.filter fun α : Fin x.1.L => IsAnchor (cellLen x.1.g W B) α).card : ℝ)
      have ha0 : 0 ≤ a := Nat.cast_nonneg _
      have hpow : (W : ℝ) ^ (B + C₄) * (W : ℝ) ^ (B + C₄) * ((W : ℝ) ^ (2 : ℝ) * (W : ℝ) ^ (4 : ℝ))
          ≤ (W : ℝ) ^ (2 * B + 2 * C₄ + 8) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have hWBC : 0 ≤ (W : ℝ) ^ (B + C₄) := (Real.rpow_pos_of_pos hx0 _).le
      have hW20 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
      calc a * (W : ℝ) * (a * (W : ℝ)) = (a * a) * (W : ℝ) ^ 2 := by ring
        _ ≤ ((6 * (W : ℝ) ^ (B + C₄)) * (6 * (W : ℝ) ^ (B + C₄))) * (W : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul h6 h6 ha0 (ha0.trans h6)) hW20
        _ = 36 * ((W : ℝ) ^ (B + C₄) * (W : ℝ) ^ (B + C₄) * (W : ℝ) ^ 2) := by ring
        _ ≤ (W : ℝ) ^ (4 : ℝ) * ((W : ℝ) ^ (B + C₄) * (W : ℝ) ^ (B + C₄) * (W : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right h81 (by positivity)
        _ ≤ _ := by rw [← hW2r] at *; linarith
  · have hbr' : x.1.g ^ 2 < (W : ℝ) ^ B := not_le.mp hbr
    have hLb := residual_exact_L W hW1 B CV x.1.g x.1.L hbr' hLV hCV
    have hle : (x.1.L : ℝ) ≤ (W : ℝ) ^ (B + 3) := by
      have e : (W : ℝ) ^ B * (W : ℝ) ^ 2 * W = (W : ℝ) ^ (B + 3) := by
        rw [Real.rpow_add hx0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
      have hWB0 : 0 ≤ (W : ℝ) ^ B * (W : ℝ) ^ 2 := by positivity
      calc (x.1.L : ℝ) ≤ 2 * CV * (W : ℝ) ^ B * (W : ℝ) ^ 2 := hLb
        _ = (2 * CV) * ((W : ℝ) ^ B * (W : ℝ) ^ 2) := by ring
        _ ≤ W * ((W : ℝ) ^ B * (W : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hWCV hWB0
        _ = (W : ℝ) ^ (B + 3) := by rw [← e]; ring
    have hL0 : (0 : ℝ) ≤ x.1.L := Nat.cast_nonneg _
    have hδ0 : (0 : ℝ) ≤ (W : ℝ) ^ (-D) := (Real.rpow_pos_of_pos hx0 _).le
    refine ⟨Finset.univ, Finset.univ, ?_, ?_,
      sampleBound_univ _ _ _ (fun _ => zero_le_one) hCs hδ0 _,
      sampleBound_univ _ _ _ (fun _ => zero_le_one) hCs hδ0 _,
      sampleBound_univ _ _ _ (fun _ => zero_le_one) hCs hδ0 _⟩
    · rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      have h1 : (x.1.L : ℝ) * x.1.L ≤ (W : ℝ) ^ (B + 3) * (W : ℝ) ^ (B + 3) :=
        mul_le_mul hle hle hL0 (hL0.trans hle)
      have h2 : (W : ℝ) ^ (B + 3) * (W : ℝ) ^ (B + 3) ≤ (W : ℝ) ^ (2 * B + 2 * C₄ + 8) := by
        rw [← Real.rpow_add hx0]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      linarith
    · rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin]
      push_cast
      have hW0 : (0 : ℝ) ≤ W := hx0.le
      have h1 : (x.1.L : ℝ) * W * (x.1.L * W) ≤
          ((W : ℝ) ^ (B + 3) * W) * ((W : ℝ) ^ (B + 3) * W) := by
        have := mul_le_mul_of_nonneg_right hle hW0
        exact mul_le_mul this this (by positivity) (by positivity)
      have e1 : (W : ℝ) ^ (B + 3) * W = (W : ℝ) ^ (B + 4) := by
        rw [show B + 4 = (B + 3) + 1 by ring, Real.rpow_add hx0 (B + 3) 1, Real.rpow_one]
      have e : ((W : ℝ) ^ (B + 3) * W) * ((W : ℝ) ^ (B + 3) * W) = (W : ℝ) ^ (2 * B + 8) := by
        rw [e1, ← Real.rpow_add hx0]; congr 1; ring
      have h2 : (W : ℝ) ^ (2 * B + 8) ≤ (W : ℝ) ^ (2 * B + 2 * C₄ + 8) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      linarith

/-- Lemma 5.10(b) [fo:lem:sampling-continuity] with Lemma 5.8 [uvc:thm:ordinary-sampling] at large
coupling, for every base family inside the large-coupling range of the hypothesis on `base`. -/
theorem samplingInput_of_large (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) (J : ℕ) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ base : ℕ → Set FlowPt,
        (∀ W p, p ∈ base W → Cκ ≤ p.g ∧ |p.E| ≤ 2 - 3 * κ / 4 ∧
          ρ W * p.g ^ 2 * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ CV * p.g ^ 2 * (W : ℝ) ^ 2 ∧
          1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u) →
        SamplingInput base J := by
  obtain ⟨Cκ₀r, C'', hCκ₀r, hC'', HR⟩ := cmpReach_large κ CV hκ hκ2 hCV J
  obtain ⟨Cκ₀s, C', hCκ₀s, hC', HS⟩ := segAdm_large κ CV hκ hκ2 hCV J
  refine ⟨max Cκ₀r Cκ₀s, hCκ₀r.trans (le_max_left _ _), fun Cκ hCκ ρ hρ base hbase => ?_⟩
  have hCκ1 : 1 ≤ Cκ := (hCκ₀r.trans (le_max_left _ _)).trans hCκ
  obtain ⟨W₂, HR'⟩ := HR Cκ ((le_max_left _ _).trans hCκ) ρ hρ
  obtain ⟨W₃, HS'⟩ := HS Cκ ((le_max_right _ _).trans hCκ) ρ hρ
  refine ⟨?_, ?_⟩
  · intro k hk cw θ F D D' hcw hθ hθ2 hF hD hD'
    exact residual_loops κ CV hκ hκ2 hCV J C'' hC'' Cκ hCκ1 ρ hρ base W₂ (HR' base hbase) k hk cw
      θ F
      D D' hcw hθ hθ2 hF hD hD'
  · intro D D' hD hD'
    exact residual_pairs κ CV hκ hκ2 hCV J C'' C' hC'' Cκ hCκ1 ρ hρ base W₂ W₃ (HR' base hbase)
      (HS' base hbase) D D' hD hD'

end LSBA
