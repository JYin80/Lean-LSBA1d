import LSBA.Sampling.Cells
import LSBA.Flow.Realization
import LSBA.Volume.LocalComparison
import LSBA.Kernel.LineKernel

/-!
# Transfer products and Green-block interpolation

The one-step transfer matrices of Definition 7.1 [def:transfer-matrices] for a block model on the
cycle, their products over a cell and the closeness of these products to the free ones, the
Duhamel perturbation in `z` (cf. (7.15) [uvc:eq:transfer-duhamel]), and the deterministic part of
Proposition 7.4 [uvc:prop:green], (7.10) [uvc:eq:interpolate]: each Green block is the
combination of anchor blocks with the free coefficients, up to an error controlled by the
closeness and the anchor envelope.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The transfer matrix `T(z) = [[z - V, -1], [1, 0]]` of Definition 7.1 [def:transfer-matrices]
for the block equation of `A_L ⊗ I + diag V`. -/
def blockT {W : ℕ} (z : ℂ) (V : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ :=
  Matrix.fromBlocks (z • (1 : Matrix (Fin W) (Fin W) ℂ) - V) (-1) 1 0

/-- The product `T_{b+j-1}(z) ⋯ T_b(z)` of `j` transfer matrices from block `b` (indices
modulo `L`), Section 7.3.1 [sec:green-interpolation-proof]. -/
def cellProd {W L : ℕ} (z : ℂ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (b : Fin L) :
    ℕ → Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ
  | 0 => 1
  | j + 1 => blockT z (V ((finRotate L ^ j) b)) * cellProd z V b j

/-- The distance `N(T_{b+j-1}(z) ⋯ T_b(z) - T(E)^j)` of a transfer product to the free one. -/
def prodErr {W L : ℕ} (N : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ → ℝ) (E : ℝ) (z : ℂ)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (b : Fin L) (j : ℕ) : ℝ :=
  N (cellProd z V b j - blockT (E : ℂ) 0 ^ j)

/-- Every transfer product inside a cell is within `ε` in operator norm of the free product:
the event of Lemma 7.7 [uvc:lem:cells] in the form used by Proposition 7.4 [uvc:prop:green]. -/
def CellClose {W L : ℕ} (n : ℕ) (E : ℝ) (z : ℂ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (ε : ℝ) : Prop :=
  ∀ (b : Fin L) (j : ℕ), b.val % n + j ≤ n → b.val + j ≤ L →
    prodErr (fun X => ‖X‖) E z V b j ≤ ε

/-- The free coefficient `c_{aα}` of (7.10) [uvc:eq:interpolate]: `sin((j+1)ϑ)/sin ϑ` at the
first block of the cell of `a` and `-sin(jϑ)/sin ϑ` at its predecessor, with `j` the position of
`a` in its cell and `2 cos ϑ = E`; zero elsewhere. -/
def cellCoef (n : ℕ) (E : ℝ) {L : ℕ} (a α : Fin L) : ℝ :=
  if α = cellStart n a then
    Real.sin (((a.val % n : ℕ) + 1 : ℝ) * Real.arccos (E / 2)) / Real.sin (Real.arccos (E / 2))
  else if α = cellPrev n a then
    -(Real.sin ((a.val % n : ℕ) * Real.arccos (E / 2)) / Real.sin (Real.arccos (E / 2)))
  else 0

/-- The free source coefficient `q_{ab}`: `sin((j - k)ϑ)/sin ϑ` when `b` precedes `a` in the
cell of `a` (positions `k < j`), zero otherwise. -/
def cellSrc (n : ℕ) (E : ℝ) {L : ℕ} (a b : Fin L) : ℝ :=
  if cellStart n b = cellStart n a ∧ b.val % n < a.val % n then
    Real.sin ((((a.val % n : ℕ) : ℝ) - ((b.val % n : ℕ) : ℝ)) * Real.arccos (E / 2)) /
      Real.sin (Real.arccos (E / 2))
  else 0

/-- `d_{ab} = q_{ab} + Σ_α c_{aα} q_{bα}` of Proposition 7.4 [uvc:prop:green]. -/
def cellD (n : ℕ) (E : ℝ) {L : ℕ} (a b : Fin L) : ℝ :=
  cellSrc n E a b + ∑ α : Fin L, cellCoef n E a α * cellSrc n E b α

/-- The interpolation `Σ_{α,β} c_{aα} c_{bβ} G_{αβ} + d_{ab} I_W` of (7.10) [uvc:eq:interpolate]. -/
def interpBlock (n : ℕ) (E : ℝ) {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : Matrix (Fin W) (Fin W) ℂ :=
  ∑ α : Fin L, ∑ β : Fin L, ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) • blockOf G α β +
    ((cellD n E a b : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)

/-- The largest operator norm of `G_{αβ}` over the anchors `α` of the cell of `a` and `β` of the
cell of `b`. -/
def anchorNorm (n : ℕ) {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    ℝ :=
  max (max ‖blockOf G (cellStart n a) (cellStart n b)‖ ‖blockOf G (cellStart n a) (cellPrev n b)‖)
    (max ‖blockOf G (cellPrev n a) (cellStart n b)‖ ‖blockOf G (cellPrev n a) (cellPrev n b)‖)

/-- The anchor envelope `𝒢(𝒫)` of Proposition 7.4 [uvc:prop:green]. -/
def anchorEnv (n : ℕ) {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) : ℝ :=
  ⨆ ab : Fin L × Fin L, anchorNorm n G ab.1 ab.2

/-- The operator norms entering the interpolation of `G_{ab}`: the anchor pairs and the blocks
`G_{αb}` with `α` an anchor of the cell of `a`. -/
def interpEnv (n : ℕ) {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    ℝ :=
  max (anchorNorm n G a b) (max ‖blockOf G (cellStart n a) b‖ ‖blockOf G (cellPrev n a) b‖)

/-- The normalized Hilbert–Schmidt norm `‖X‖_{2,W} = W^{-1/2} ‖X‖_HS` of Section 7.3.2
[sec:common-interpolation-proof]. -/
def nhs (W : ℕ) {m : Type*} [Fintype m] (X : Matrix m m ℂ) : ℝ :=
  Real.sqrt ((W : ℝ)⁻¹ * ∑ i, ∑ j, ‖X i j‖ ^ 2)

/-- The transfer products used for the target `a` with source `b`: the prefix from the first
block of the cell of `a` to `a`, and the product from `b + 1` to `a` when `b` precedes `a` in
its cell. -/
def interpErr {W L : ℕ} (N : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ → ℝ) (n : ℕ) (E : ℝ)
    (z : ℂ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (a b : Fin L) : ℝ :=
  prodErr N E z V (cellStart n a) (a.val % n) +
    if cellStart n b = cellStart n a ∧ b.val % n < a.val % n then
      prodErr N E z V (finRotate L b) (a.val % n - b.val % n - 1)
    else 0

/-! ## Auxiliary lemmas -/

private theorem transfer_rot_val {L : ℕ} (r : Fin L) : (finRotate L r).val = (r.val + 1) % L := by
  cases L with
  | zero => exact r.elim0
  | succ L =>
    rw [coe_finRotate]
    split_ifs with h
    · subst h; simp
    · have := Fin.val_lt_last h
      rw [Nat.mod_eq_of_lt (by omega)]

private theorem transfer_rotPow_val {L : ℕ} (r : Fin L) (m : ℕ) :
    ((finRotate L ^ m) r).val = (r.val + m) % L := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt r.isLt]
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, transfer_rot_val, ih, Nat.mod_add_mod, add_assoc]

private theorem transfer_sum_cycleAdj {L W : ℕ} (r : Fin L) (f : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    ∑ c, cycleAdj L r c • f c = f (finRotate L r) + f ((finRotate L).symm r) := by
  have h1 : ∀ c : Fin L, (c.val = (r.val + 1) % L) ↔ c = finRotate L r := by
    intro c; rw [Fin.ext_iff, transfer_rot_val]
  have h2 : ∀ c : Fin L, (r.val = (c.val + 1) % L) ↔ c = (finRotate L).symm r := by
    intro c; rw [Equiv.eq_symm_apply, Fin.ext_iff, transfer_rot_val, eq_comm]
  simp only [cycleAdj, Matrix.of_apply, add_smul, Finset.sum_add_distrib, h1, h2, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem transfer_blockOf_mul {W L : ℕ} (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockOf (X * Y) a b = ∑ c, blockOf X a c * blockOf Y c b := by
  ext α β
  simp [blockOf, Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]


private theorem transfer_blockOf_op {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (z : ℂ)
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

private theorem transfer_op_isHermitian {W L : ℕ} {V : Fin L → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ r, (V r).IsHermitian) :
    (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V).IsHermitian := by
  refine Matrix.IsHermitian.add ?_ (blockDiagOp_isHermitian hV)
  rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, (cycleAdj_isHermitian L).eq,
    Matrix.conjTranspose_one]

/-- The forced recurrence of the Green column (Section 7.3.1 [sec:green-interpolation-proof]):
`G_{r+1,b} = (z - V_r) G_{r,b} - G_{r-1,b} + δ_{rb}`. -/
private theorem transfer_green_rec {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (z : ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hG : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
        z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * G = 1) (r b : Fin L) :
    blockOf G (finRotate L r) b =
      (z • (1 : Matrix (Fin W) (Fin W) ℂ) - V r) * blockOf G r b -
        blockOf G ((finRotate L).symm r) b + if r = b then 1 else 0 := by
  have h2 := congrArg (fun X => blockOf X r b) hG
  simp only [transfer_blockOf_mul, transfer_blockOf_op] at h2
  simp only [add_mul, Finset.sum_add_distrib, smul_mul_assoc, one_mul, transfer_sum_cycleAdj,
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
private def transferCol {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (r b : Fin L) :
    Matrix (Fin W ⊕ Fin W) (Fin W) ℂ :=
  Matrix.fromRows (blockOf G r b) (blockOf G ((finRotate L).symm r) b)

private theorem transfer_col_succ {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (z : ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hG : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
        z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * G = 1) (r b : Fin L) :
    transferCol G (finRotate L r) b = blockT z (V r) * transferCol G r b +
      if r = b then Matrix.fromRows (1 : Matrix (Fin W) (Fin W) ℂ) 0 else 0 := by
  have h := transfer_green_rec V z G hG r b
  simp only [transferCol, blockT, Matrix.fromBlocks_mul_fromRows, Equiv.symm_apply_apply]
  rw [h]
  split_ifs <;> ext (i | i) j <;> simp [sub_eq_add_neg]

private theorem transfer_col_iter {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (z : ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hG : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
        z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * G = 1) (s b : Fin L) (m : ℕ)
    (hm : s.val + m < L) :
    transferCol G ((finRotate L ^ m) s) b = cellProd z V s m * transferCol G s b +
      if s.val ≤ b.val ∧ b.val < s.val + m then
        cellProd z V (finRotate L b) (s.val + m - b.val - 1) *
          Matrix.fromRows (1 : Matrix (Fin W) (Fin W) ℂ) 0 else 0 := by
  induction m with
  | zero => simp [cellProd]
  | succ m ih =>
    have ih := ih (by omega)
    have hpos : ((finRotate L ^ m) s).val = s.val + m := by
      rw [transfer_rotPow_val, Nat.mod_eq_of_lt (by omega)]
    rw [pow_succ', Equiv.Perm.mul_apply, transfer_col_succ V z G hG, ih]
    by_cases h1 : s.val ≤ b.val ∧ b.val < s.val + m
    · have hne : (finRotate L ^ m) s ≠ b := by
        intro h; rw [← h, hpos] at h1; omega
      have hb : b.val + 1 < L := by omega
      have hrot : (finRotate L ^ (s.val + m - b.val - 1)) (finRotate L b) =
          (finRotate L ^ m) s := by
        apply Fin.ext
        rw [transfer_rotPow_val, transfer_rotPow_val, transfer_rot_val, Nat.mod_eq_of_lt hb]
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
private def transferU (E : ℝ) (m : ℕ) : ℝ :=
  Real.sin (m * Real.arccos (E / 2)) / Real.sin (Real.arccos (E / 2))

private theorem transfer_sin_pos {E : ℝ} (hE : |E| < 2) : 0 < Real.sin (Real.arccos (E / 2)) := by
  rw [Real.sin_arccos]
  apply Real.sqrt_pos.mpr
  have : |E / 2| < 1 := by rw [abs_div]; norm_num; linarith
  have h2 : (E / 2) ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (E / 2)]
  linarith

private theorem transferU_zero (E : ℝ) : transferU E 0 = 0 := by simp [transferU]

private theorem transferU_one {E : ℝ} (hE : |E| < 2) : transferU E 1 = 1 := by
  simp only [transferU, Nat.cast_one, one_mul]
  exact div_self (transfer_sin_pos hE).ne'

private theorem transferU_rec {E : ℝ} (hE : |E| < 2) (m : ℕ) :
    transferU E (m + 2) = E * transferU E (m + 1) - transferU E m := by
  have hc : Real.cos (Real.arccos (E / 2)) = E / 2 := by
    apply Real.cos_arccos <;> [skip; skip] <;> (rw [abs_lt] at hE; linarith)
  set t := Real.arccos (E / 2)
  simp only [transferU]
  have h1 : Real.sin (((m + 2 : ℕ) : ℝ) * t) = Real.sin (((m + 1 : ℕ) : ℝ) * t + t) := by
    congr 1; push_cast; ring
  have h2 : Real.sin ((m : ℝ) * t) = Real.sin (((m + 1 : ℕ) : ℝ) * t - t) := by
    congr 1; push_cast; ring
  rw [h1, h2, Real.sin_add, Real.sin_sub, hc]
  field_simp
  ring

/-- The free powers `T(E)^m = [[U_{m+1}, -U_m], [U_m, U_{m+1} - E U_m]] ⊗ I`, whose entries are
the coefficients (6.16) [da:eq:cell-interpolation-coefficients]. -/
private theorem transfer_free_pow {W : ℕ} {E : ℝ} (hE : |E| < 2) (m : ℕ) :
    blockT (E : ℂ) (0 : Matrix (Fin W) (Fin W) ℂ) ^ m =
      Matrix.fromBlocks ((transferU E (m + 1) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ))
        ((-transferU E m : ℂ) • 1) ((transferU E m : ℂ) • 1)
        (((transferU E (m + 1) - E * transferU E m : ℝ) : ℂ) • 1) := by
  induction m with
  | zero =>
    simp [transferU_zero, transferU_one hE, Matrix.fromBlocks_one]
  | succ m ih =>
    rw [pow_succ', ih, blockT, Matrix.fromBlocks_multiply]
    have hr := transferU_rec hE m
    congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> simp [hr] <;> ring

private theorem transfer_start_add {n L : ℕ} (a : Fin L) :
    (cellStart n a).val + a.val % n = a.val := Nat.div_add_mod' a.val n

private theorem transfer_prev_ne {n L : ℕ} (hL : 2 ≤ L) (a : Fin L) :
    cellPrev n a ≠ cellStart n a := by
  intro h
  have h2 : finRotate L (cellPrev n a) = cellPrev n a := by
    simp only [cellPrev, Equiv.apply_symm_apply]
    exact h.symm
  have h3 := congrArg Fin.val h2
  rw [transfer_rot_val] at h3
  have hlt := (cellPrev n a).isLt
  by_cases hc : (cellPrev n a).val + 1 < L
  · rw [Nat.mod_eq_of_lt hc] at h3; omega
  · rw [show (cellPrev n a).val + 1 = L by omega, Nat.mod_self] at h3; omega

/-- The source condition `b` precedes `a` in the cell of `a`, in positions. -/
private theorem transfer_src_iff {n L : ℕ} (hn : 1 ≤ n) (a b : Fin L) :
    (cellStart n b = cellStart n a ∧ b.val % n < a.val % n) ↔
      ((cellStart n a).val ≤ b.val ∧ b.val < (cellStart n a).val + a.val % n) := by
  have ha := transfer_start_add (n := n) a
  have hb := transfer_start_add (n := n) b
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

private theorem transfer_toRows₁_add {W : ℕ} (X Y : Matrix (Fin W ⊕ Fin W) (Fin W) ℂ) :
    (X + Y).toRows₁ = X.toRows₁ + Y.toRows₁ := by
  ext i k; rfl

private theorem transfer_toRows₁_mul {W : ℕ} (P : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (A B : Matrix (Fin W) (Fin W) ℂ) :
    (P * Matrix.fromRows A B).toRows₁ = P.toBlocks₁₁ * A + P.toBlocks₁₂ * B := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks P]
  rw [Matrix.fromBlocks_mul_fromRows, Matrix.toRows₁_fromRows]

private theorem transfer_coef_start {n L : ℕ} (E : ℝ) (a : Fin L) :
    cellCoef n E a (cellStart n a) = transferU E (a.val % n + 1) := by
  simp only [cellCoef, ite_true, transferU]
  push_cast; ring_nf

private theorem transfer_coef_prev {n L : ℕ} (hL : 2 ≤ L) (E : ℝ) (a : Fin L) :
    cellCoef n E a (cellPrev n a) = -transferU E (a.val % n) := by
  simp only [cellCoef, transfer_prev_ne hL a, ite_false, ite_true, transferU]

private theorem transfer_coef_other {n L : ℕ} (E : ℝ) (a α : Fin L) (h1 : α ≠ cellStart n a)
    (h2 : α ≠ cellPrev n a) : cellCoef n E a α = 0 := by
  simp only [cellCoef, h1, h2, ite_false]

/-- `Σ_α c_{aα} X_α` has only the two anchor terms. -/
private theorem transfer_sum_coef {n L : ℕ} (hL : 2 ≤ L) (E : ℝ) {M : Type*} [AddCommGroup M]
    [Module ℂ M] (a : Fin L) (X : Fin L → M) :
    ∑ α, ((cellCoef n E a α : ℝ) : ℂ) • X α =
      ((transferU E (a.val % n + 1) : ℝ) : ℂ) • X (cellStart n a) +
        ((-transferU E (a.val % n) : ℝ) : ℂ) • X (cellPrev n a) := by
  rw [Finset.sum_eq_add (cellStart n a) (cellPrev n a) (transfer_prev_ne hL a).symm
    (fun c _ hc => by rw [transfer_coef_other E a c hc.1 hc.2]; simp)
    (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h),
    transfer_coef_start, transfer_coef_prev hL]

private theorem transfer_src_eq {n L : ℕ} (E : ℝ) (a b : Fin L) :
    cellSrc n E a b = if cellStart n b = cellStart n a ∧ b.val % n < a.val % n then
      transferU E (a.val % n - b.val % n - 1 + 1) else 0 := by
  unfold cellSrc
  split_ifs with h
  · simp only [transferU]
    rw [show a.val % n - b.val % n - 1 + 1 = a.val % n - b.val % n by omega,
      Nat.cast_sub (by omega : b.val % n ≤ a.val % n)]
  · rfl

private theorem transfer_toBlocks₁₁_sub {W : ℕ} (X Y : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    (X - Y).toBlocks₁₁ = X.toBlocks₁₁ - Y.toBlocks₁₁ := by ext; rfl

private theorem transfer_toBlocks₁₂_sub {W : ℕ} (X Y : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    (X - Y).toBlocks₁₂ = X.toBlocks₁₂ - Y.toBlocks₁₂ := by ext; rfl

/-- The exact interpolation identity: the remainder of `G_{ab}` after the anchor and source
terms is driven by the differences of the transfer products to the free ones. -/
private theorem transfer_identity {W L n : ℕ} (hL : 2 ≤ L) (hn : 1 ≤ n) {E : ℝ} (hE : |E| < 2)
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
  have hsa : s.val + j = a.val := transfer_start_add a
  have hsL : s.val + j < L := by rw [hsa]; exact a.isLt
  have hrot : (finRotate L ^ j) s = a := by
    apply Fin.ext; rw [transfer_rotPow_val, Nat.mod_eq_of_lt hsL, hsa]
  have iter := transfer_col_iter V z G hG s b j hsL
  rw [hrot] at iter
  have top := congrArg Matrix.toRows₁ iter
  have hprev : (finRotate L).symm s = cellPrev n a := rfl
  -- the top block of the iterated column
  have hGab : blockOf G a b = (cellProd z V s j).toBlocks₁₁ * blockOf G s b +
      (cellProd z V s j).toBlocks₁₂ * blockOf G (cellPrev n a) b +
      if cellStart n b = cellStart n a ∧ b.val % n < a.val % n then
        (cellProd z V (finRotate L b) (j - b.val % n - 1)).toBlocks₁₁ else 0 := by
    have e1 : (transferCol G a b).toRows₁ = blockOf G a b := rfl
    have e2 : transferCol G s b = Matrix.fromRows (blockOf G s b)
        (blockOf G ((finRotate L).symm s) b) := rfl
    rw [e1, e2, hprev, transfer_toRows₁_add, transfer_toRows₁_mul] at top
    rw [top]
    have hc := transfer_src_iff hn a b
    rw [← hs_def, ← hj_def] at hc
    by_cases hcond : cellStart n b = cellStart n a ∧ b.val % n < a.val % n
    · have hc' := hc.mp hcond
      have hk : s.val + j - b.val - 1 = j - b.val % n - 1 := by
        have hb := transfer_start_add (n := n) b
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
  rw [hGab, transfer_sum_coef hL, transfer_src_eq, transfer_toBlocks₁₁_sub, transfer_toBlocks₁₂_sub,
    transfer_free_pow hE, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂]
  rw [← hs_def, ← hj_def]
  split_ifs with hcond
  · rw [transfer_toBlocks₁₁_sub, transfer_free_pow hE, Matrix.toBlocks_fromBlocks₁₁]
    simp only [sub_mul, Matrix.smul_mul, Matrix.one_mul, Complex.ofReal_neg, neg_smul, neg_mul]
    abel
  · simp only [sub_mul, Matrix.smul_mul, Matrix.one_mul, Complex.ofReal_zero, zero_smul,
      Complex.ofReal_neg, neg_smul, neg_mul]
    abel


private theorem transfer_norm_le_one_of {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    (X : Matrix m k ℂ) (h : Xᴴ * X = 1) (h1 : ‖(1 : Matrix k k ℂ)‖ ≤ 1) : ‖X‖ ≤ 1 := by
  have := Matrix.l2_opNorm_conjTranspose_mul_self X
  rw [h] at this
  nlinarith [norm_nonneg X]

private theorem transfer_norm_one_le (k : Type*) [Fintype k] [DecidableEq k] :
    ‖(1 : Matrix k k ℂ)‖ ≤ 1 := by
  have := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix k k ℂ)
  rw [Matrix.conjTranspose_one, Matrix.one_mul] at this
  nlinarith [norm_nonneg (1 : Matrix k k ℂ)]

private theorem transfer_norm_smul_one_le {W : ℕ} (c : ℂ) :
    ‖c • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ ‖c‖ := by
  rw [norm_smul]
  have := transfer_norm_one_le (Fin W)
  nlinarith [norm_nonneg c]

/-- The block embeddings `ι₁ = (I; 0)` and `ι₂ = (0; I)`. -/
private def transferι₁ (W : ℕ) : Matrix (Fin W ⊕ Fin W) (Fin W) ℂ := Matrix.fromRows 1 0
private def transferι₂ (W : ℕ) : Matrix (Fin W ⊕ Fin W) (Fin W) ℂ := Matrix.fromRows 0 1

private theorem transfer_normι₁ (W : ℕ) : ‖transferι₁ W‖ ≤ 1 := by
  apply transfer_norm_le_one_of _ _ (transfer_norm_one_le _)
  ext i j
  change (∑ x : Fin W ⊕ Fin W, star (transferι₁ W x i) * transferι₁ W x j) = _
  simp [transferι₁, Fintype.sum_sum_type, Matrix.one_apply, eq_comm]

private theorem transfer_normι₂ (W : ℕ) : ‖transferι₂ W‖ ≤ 1 := by
  apply transfer_norm_le_one_of _ _ (transfer_norm_one_le _)
  ext i j
  change (∑ x : Fin W ⊕ Fin W, star (transferι₂ W x i) * transferι₂ W x j) = _
  simp [transferι₂, Fintype.sum_sum_type, Matrix.one_apply, eq_comm]

private theorem transfer_blocks_eq {W : ℕ} (X : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    X.toBlocks₁₁ = (transferι₁ W)ᴴ * X * transferι₁ W ∧
    X.toBlocks₁₂ = (transferι₁ W)ᴴ * X * transferι₂ W ∧
    X.toBlocks₂₁ = (transferι₂ W)ᴴ * X * transferι₁ W ∧
    X.toBlocks₂₂ = (transferι₂ W)ᴴ * X * transferι₂ W := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [transferι₁, transferι₂, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

private theorem transfer_norm_block_le {W : ℕ} (X : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    ‖X.toBlocks₁₁‖ ≤ ‖X‖ ∧ ‖X.toBlocks₁₂‖ ≤ ‖X‖ := by
  obtain ⟨h1, h2, -, -⟩ := transfer_blocks_eq X
  have a1 := transfer_normι₁ W
  have a2 := transfer_normι₂ W
  have b1 : ‖(transferι₁ W)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact a1
  constructor
  · rw [h1]
    calc _ ≤ ‖(transferι₁ W)ᴴ * X‖ * ‖transferι₁ W‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖(transferι₁ W)ᴴ‖ * ‖X‖) * 1 := by
          gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖X‖ * 1 := by gcongr
      _ = ‖X‖ := by ring
  · rw [h2]
    calc _ ≤ ‖(transferι₁ W)ᴴ * X‖ * ‖transferι₂ W‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖(transferι₁ W)ᴴ‖ * ‖X‖) * 1 := by
          gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖X‖ * 1 := by gcongr
      _ = ‖X‖ := by ring

private theorem transfer_norm_fromBlocks_le {W : ℕ} (A B C D : Matrix (Fin W) (Fin W) ℂ) :
    ‖Matrix.fromBlocks A B C D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
  have e : Matrix.fromBlocks A B C D = transferι₁ W * A * (transferι₁ W)ᴴ +
      transferι₁ W * B * (transferι₂ W)ᴴ + transferι₂ W * C * (transferι₁ W)ᴴ +
      transferι₂ W * D * (transferι₂ W)ᴴ := by
    ext (i | i) (j | j) <;>
      simp [transferι₁, transferι₂, Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ (P Q : Matrix (Fin W ⊕ Fin W) (Fin W) ℂ) (Y : Matrix (Fin W) (Fin W) ℂ),
      ‖P‖ ≤ 1 → ‖Q‖ ≤ 1 → ‖P * Y * Qᴴ‖ ≤ ‖Y‖ := by
    intro P Q Y hP hQ
    have hQ' : ‖Qᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hQ
    calc _ ≤ ‖P * Y‖ * ‖Qᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖P‖ * ‖Y‖) * 1 := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖Y‖ * 1 := by gcongr
      _ = ‖Y‖ := by ring
  rw [e]
  have a1 := transfer_normι₁ W
  have a2 := transfer_normι₂ W
  calc _ ≤ ‖transferι₁ W * A * (transferι₁ W)ᴴ‖ + ‖transferι₁ W * B * (transferι₂ W)ᴴ‖ +
        ‖transferι₂ W * C * (transferι₁ W)ᴴ‖ + ‖transferι₂ W * D * (transferι₂ W)ᴴ‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := by gcongr <;> exact key _ _ _ (by assumption) (by assumption)

private theorem transfer_nhs_nonneg (W : ℕ) {m : Type*} [Fintype m] (X : Matrix m m ℂ) :
    0 ≤ nhs W X := Real.sqrt_nonneg _

/-- The squared Hilbert–Schmidt sum. -/
private def transferHS {m : Type*} [Fintype m] (X : Matrix m m ℂ) : ℝ := ∑ i, ∑ j, ‖X i j‖ ^ 2

/-- The flattening of a matrix into `EuclideanSpace`. -/
private def transferFlat {m : Type*} [Fintype m] (X : Matrix m m ℂ) : EuclideanSpace ℂ (m × m) :=
  WithLp.toLp 2 fun p => X p.1 p.2

private theorem transfer_norm_flat {m : Type*} [Fintype m] (X : Matrix m m ℂ) :
    ‖transferFlat X‖ = Real.sqrt (transferHS X) := by
  rw [EuclideanSpace.norm_eq, transferHS, ← Fintype.sum_prod_type']
  rfl

private theorem transfer_nhs_eq (W : ℕ) {m : Type*} [Fintype m] (X : Matrix m m ℂ) :
    nhs W X = Real.sqrt (W : ℝ)⁻¹ * ‖transferFlat X‖ := by
  rw [transfer_norm_flat, ← Real.sqrt_mul (by positivity)]
  rfl

private theorem transfer_nhs_add_le (W : ℕ) {m : Type*} [Fintype m] (X Y : Matrix m m ℂ) :
    nhs W (X + Y) ≤ nhs W X + nhs W Y := by
  rw [transfer_nhs_eq, transfer_nhs_eq, transfer_nhs_eq, ← mul_add]
  have : transferFlat (X + Y) = transferFlat X + transferFlat Y := rfl
  rw [this]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)

private theorem transfer_nhs_smul (W : ℕ) {m : Type*} [Fintype m] (c : ℂ) (X : Matrix m m ℂ) :
    nhs W (c • X) = ‖c‖ * nhs W X := by
  rw [transfer_nhs_eq, transfer_nhs_eq]
  have : transferFlat (c • X) = c • transferFlat X := rfl
  rw [this, norm_smul]
  ring

private theorem transfer_nhs_conjTranspose (W : ℕ) {m : Type*} [Fintype m] (X : Matrix m m ℂ) :
    nhs W Xᴴ = nhs W X := by
  unfold nhs
  congr 2
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

private theorem transferHS_mul_le {m : Type*} [Fintype m] (X Y : Matrix m m ℂ) :
    transferHS (X * Y) ≤ ‖X‖ ^ 2 * transferHS Y := by
  unfold transferHS
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  set y : EuclideanSpace ℂ m := WithLp.toLp 2 fun i => Y i j
  have h := Matrix.l2_opNorm_mulVec X y
  have hy : ‖y‖ ^ 2 = ∑ i, ‖Y i j‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have hXy : ‖(EuclideanSpace.equiv m ℂ).symm (X *ᵥ y)‖ ^ 2 = ∑ i, ‖(X * Y) i j‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    rfl
  rw [← hy, ← hXy, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

private theorem transfer_nhs_mul_le_left (W : ℕ) {m : Type*} [Fintype m] (X Y : Matrix m m ℂ) :
    nhs W (X * Y) ≤ ‖X‖ * nhs W Y := by
  unfold nhs
  rw [← Real.sqrt_sq (norm_nonneg X), ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  have h := transferHS_mul_le X Y
  unfold transferHS at h
  have hW : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  nlinarith

private theorem transfer_nhs_mul_le_right (W : ℕ) {m : Type*} [Fintype m] [DecidableEq m]
    (X Y : Matrix m m ℂ) : nhs W (X * Y) ≤ nhs W X * ‖Y‖ := by
  rw [← transfer_nhs_conjTranspose, Matrix.conjTranspose_mul, ← Matrix.l2_opNorm_conjTranspose Y,
    ← transfer_nhs_conjTranspose W X, mul_comm]
  exact transfer_nhs_mul_le_left W _ _

private theorem transfer_nhs_block_le (W : ℕ) {k : ℕ}
    (X : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℂ) :
    nhs W X.toBlocks₁₁ ≤ nhs W X ∧ nhs W X.toBlocks₁₂ ≤ nhs W X := by
  have hW : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  have hsum : ∑ i, ∑ j, ‖X i j‖ ^ 2 = (∑ i, ∑ j, ‖X.toBlocks₁₁ i j‖ ^ 2 +
      ∑ i, ∑ j, ‖X.toBlocks₁₂ i j‖ ^ 2) +
      (∑ i, ∑ j, ‖X.toBlocks₂₁ i j‖ ^ 2 + ∑ i, ∑ j, ‖X.toBlocks₂₂ i j‖ ^ 2) := by
    simp only [Fintype.sum_sum_type, Finset.sum_add_distrib, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply]
    ring
  have p1 : 0 ≤ ∑ i, ∑ j, ‖X.toBlocks₁₁ i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have p2 : 0 ≤ ∑ i, ∑ j, ‖X.toBlocks₁₂ i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have p3 : 0 ≤ ∑ i, ∑ j, ‖X.toBlocks₂₁ i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have p4 : 0 ≤ ∑ i, ∑ j, ‖X.toBlocks₂₂ i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold nhs
  constructor <;> apply Real.sqrt_le_sqrt <;> rw [hsum] <;>
    exact mul_le_mul_of_nonneg_left (by linarith) hW

/-- In the bulk `|E| ≤ 2 - κ`: `sin ϑ ≥ κ/2`. -/
private theorem transfer_sin_ge {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) :
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

private theorem transferU_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (m : ℕ) : |transferU E m| ≤ 2 / κ := by
  have hs := transfer_sin_ge hκ hκ2 hE
  have hs0 : 0 < Real.sin (Real.arccos (E / 2)) := by linarith
  unfold transferU
  rw [abs_div, abs_of_pos hs0, div_le_div_iff₀ hs0 hκ]
  have := Real.abs_sin_le_one (m * Real.arccos (E / 2))
  nlinarith

private theorem transfer_src_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a b : Fin L) : |cellSrc n E a b| ≤ 2 / κ := by
  rw [transfer_src_eq]
  split_ifs
  · exact transferU_abs_le hκ hκ2 hE _
  · simp only [abs_zero]; positivity

private theorem transfer_free_norm_le {W : ℕ} {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2)
    (hE : |E| ≤ 2 - κ) (m : ℕ) :
    ‖blockT (E : ℂ) (0 : Matrix (Fin W) (Fin W) ℂ) ^ m‖ ≤ 12 / κ := by
  have hE' : |E| < 2 := by linarith
  rw [transfer_free_pow hE']
  refine (transfer_norm_fromBlocks_le _ _ _ _).trans ?_
  have h1 := transferU_abs_le hκ hκ2 hE (m + 1)
  have h2 := transferU_abs_le hκ hκ2 hE m
  have hE2 : |E| ≤ 2 := by linarith
  have e : ∀ c : ℝ, ‖((c : ℂ)) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ |c| := fun c =>
    (transfer_norm_smul_one_le _).trans (by rw [Complex.norm_real, Real.norm_eq_abs])
  have e' : ‖(-(transferU E m : ℂ)) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ |transferU E m| := by
    have := e (-transferU E m); push_cast at this; simpa [abs_neg] using this
  have h3 : |transferU E (m + 1) - E * transferU E m| ≤
      |transferU E (m + 1)| + 2 * |transferU E m| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    gcongr
  have := e (transferU E (m + 1))
  have := e (transferU E m)
  have := e (transferU E (m + 1) - E * transferU E m)
  have h12 : 12 / κ = 2 / κ * 6 := by ring
  nlinarith

/-- `J = [[I, 0], [0, 0]]`, the derivative of `T(z)` in `z`. -/
private def transferJ (W : ℕ) : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ :=
  Matrix.fromBlocks 1 0 0 0

private theorem transfer_normJ (W : ℕ) : ‖transferJ W‖ ≤ 1 := by
  refine (transfer_norm_fromBlocks_le _ _ _ _).trans ?_
  simpa using transfer_norm_one_le (Fin W)

private theorem transfer_blockT_sub {W : ℕ} (z w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    blockT z X = blockT w X + (z - w) • transferJ W := by
  ext (i | i) (k | k) <;> simp [blockT, transferJ, Matrix.one_apply]
  split_ifs <;> ring

/-- The discrete variation of constants (7.15) [uvc:eq:transfer-duhamel]:
`P_m(z) = P_m(w) + Σ_{r<m} P^{(r+1)}_{m-r-1}(w) (z - w) J P_r(z)`. -/
private theorem transfer_duhamel {W L : ℕ} (z w : ℂ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (b : Fin L) (m : ℕ) :
    cellProd z V b m = cellProd w V b m + ∑ r ∈ Finset.range m,
      cellProd w V ((finRotate L ^ (r + 1)) b) (m - r - 1) * ((z - w) • transferJ W) *
        cellProd z V b r := by
  induction m with
  | zero => simp [cellProd]
  | succ m ih =>
    have step : cellProd z V b (m + 1) = blockT w (V ((finRotate L ^ m) b)) * cellProd z V b m +
        (z - w) • transferJ W * cellProd z V b m := by
      rw [cellProd, transfer_blockT_sub z w, Matrix.add_mul]
    rw [step]
    nth_rewrite 1 [ih]
    have hsum : ∀ r ∈ Finset.range m,
        blockT w (V ((finRotate L ^ m) b)) * (cellProd w V ((finRotate L ^ (r + 1)) b) (m - r - 1) *
          ((z - w) • transferJ W) * cellProd z V b r) =
        cellProd w V ((finRotate L ^ (r + 1)) b) (m + 1 - r - 1) * ((z - w) • transferJ W) *
          cellProd z V b r := by
      intro r hr
      have hr' := Finset.mem_range.mp hr
      have hrot : (finRotate L ^ (m - r - 1)) ((finRotate L ^ (r + 1)) b) =
          (finRotate L ^ m) b := by
        rw [← Equiv.Perm.mul_apply, ← pow_add]
        congr 2; omega
      rw [show m + 1 - r - 1 = (m - r - 1) + 1 by omega, cellProd, hrot]
      simp only [Matrix.mul_assoc]
    rw [Matrix.mul_add, Finset.mul_sum, Finset.sum_congr rfl hsum, Finset.sum_range_succ,
      show m + 1 - m - 1 = 0 by omega]
    simp only [cellProd, Matrix.one_mul]
    abel

/-- The products started inside the window of a cell product stay admissible for `CellClose`. -/
private theorem transfer_shift_adm {n L : ℕ} (b : Fin L) {i r : ℕ} (hir : i < r)
    (hbn : b.val % n + r ≤ n) (hbL : b.val + r ≤ L) :
    ((finRotate L ^ (i + 1)) b).val % n + (r - i - 1) ≤ n ∧
      ((finRotate L ^ (i + 1)) b).val + (r - i - 1) ≤ L := by
  rw [transfer_rotPow_val]
  by_cases h : b.val + (i + 1) < L
  · rw [Nat.mod_eq_of_lt h]
    have h1 : (b.val + (i + 1)) % n ≤ b.val % n + (i + 1) := by
      rw [Nat.add_mod]
      exact (Nat.mod_le _ _).trans (by have := Nat.mod_le (i + 1) n; omega)
    constructor <;> omega
  · have hL : b.val + (i + 1) = L := by omega
    rw [hL, Nat.mod_self, Nat.zero_mod]
    constructor <;> omega

/-- Discrete Gronwall: `x_r ≤ M + Σ_{i<r} c x_i` for all `r ≤ j` gives `x_r ≤ M (1 + c)^r`. -/
private theorem transfer_gronwall {M c : ℝ} (hc : 0 ≤ c) (x : ℕ → ℝ) (j : ℕ)
    (hx : ∀ r ≤ j, x r ≤ M + ∑ i ∈ Finset.range r, c * x i) :
    ∀ r ≤ j, x r ≤ M * (1 + c) ^ r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    refine (hx r hr).trans ?_
    have hgeom : ∑ i ∈ Finset.range r, c * (M * (1 + c) ^ i) = M * ((1 + c) ^ r - 1) := by
      have := geom_sum_mul (1 + c) r
      rw [add_sub_cancel_left] at this
      rw [← this, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    calc M + ∑ i ∈ Finset.range r, c * x i ≤ M + ∑ i ∈ Finset.range r, c * (M * (1 + c) ^ i) := by
          gcongr with i hi
          exact ih i (Finset.mem_range.mp hi) (by have := Finset.mem_range.mp hi; omega)
      _ = M * (1 + c) ^ r := by rw [hgeom]; ring

/-- The prefix of the cell of `a` up to `a` is admissible for `CellClose`. -/
private theorem transfer_adm_prefix {n L : ℕ} (hn : 1 ≤ n) (a : Fin L) :
    (cellStart n a).val % n + a.val % n ≤ n ∧ (cellStart n a).val + a.val % n ≤ L := by
  have h1 : (cellStart n a).val % n = 0 := Nat.mul_mod_left _ _
  have h2 := Nat.mod_lt a.val (by omega : 0 < n)
  have h3 := transfer_start_add (n := n) a
  constructor <;> omega

/-- The product from `b + 1` to `a` is admissible for `CellClose` when `b` precedes `a` in its
cell. -/
private theorem transfer_adm_src {n L : ℕ} (hn : 1 ≤ n) (a b : Fin L)
    (h : cellStart n b = cellStart n a ∧ b.val % n < a.val % n) :
    (finRotate L b).val % n + (a.val % n - b.val % n - 1) ≤ n ∧
      (finRotate L b).val + (a.val % n - b.val % n - 1) ≤ L := by
  have hab := (transfer_src_iff hn a b).mp h
  have ha := transfer_start_add (n := n) a
  have hb := transfer_start_add (n := n) b
  rw [h.1] at hb
  have hlt := a.isLt
  have hj := Nat.mod_lt a.val (by omega : 0 < n)
  have hbL : b.val + 1 < L := by omega
  rw [transfer_rot_val, Nat.mod_eq_of_lt hbL]
  have hmod : (b.val + 1) % n = b.val % n + 1 := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt (by omega)]
  constructor <;> omega

/-- The remainder `G_{ab} - Σ_α c_{aα} G_{αb} - q_{ab} I` of the first-coordinate
interpolation. -/
private def transferRem (n : ℕ) (E : ℝ) {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : Matrix (Fin W) (Fin W) ℂ :=
  blockOf G a b - (∑ α, ((cellCoef n E a α : ℝ) : ℂ) • blockOf G α b) -
    ((cellSrc n E a b : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)

private theorem transfer_rem_op {W L n : ℕ} (hL : 2 ≤ L) (hn : 1 ≤ n) {E ε : ℝ} (hE : |E| < 2)
    (hε : 0 ≤ ε) (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (z : ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hG : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
        z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * G = 1)
    (hcl : CellClose n E z V ε) (a b : Fin L) :
    ‖transferRem n E G a b‖ ≤
      ε * (1 + ‖blockOf G (cellStart n a) b‖ + ‖blockOf G (cellPrev n a) b‖) := by
  unfold transferRem
  rw [transfer_identity hL hn hE V z G hG a b]
  obtain ⟨p1, p2⟩ := transfer_adm_prefix (L := L) hn a
  have hP := hcl _ _ p1 p2
  unfold prodErr at hP
  obtain ⟨b1, b2⟩ := transfer_norm_block_le
    (cellProd z V (cellStart n a) (a.val % n) - blockT (E : ℂ) 0 ^ (a.val % n))
  have hsrc : ‖(if cellStart n b = cellStart n a ∧ b.val % n < a.val % n then
      (cellProd z V (finRotate L b) (a.val % n - b.val % n - 1) -
        blockT (E : ℂ) 0 ^ (a.val % n - b.val % n - 1)).toBlocks₁₁ else 0)‖ ≤ ε := by
    split_ifs with h
    · obtain ⟨q1, q2⟩ := transfer_adm_src hn a b h
      have hQ := hcl _ _ q1 q2
      unfold prodErr at hQ
      exact (transfer_norm_block_le _).1.trans hQ
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

private theorem transfer_rem_hs {W L n : ℕ} (hL : 2 ≤ L) (hn : 1 ≤ n) {E : ℝ} (hE : |E| < 2)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (z : ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hG : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
        z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * G = 1) (a b : Fin L) :
    nhs W (transferRem n E G a b) ≤ interpErr (nhs W) n E z V a b *
      (1 + ‖blockOf G (cellStart n a) b‖ + ‖blockOf G (cellPrev n a) b‖) := by
  unfold transferRem
  rw [transfer_identity hL hn hE V z G hG a b]
  set e₁ := prodErr (nhs W) E z V (cellStart n a) (a.val % n) with he₁
  have he₁0 : 0 ≤ e₁ := transfer_nhs_nonneg _ _
  obtain ⟨b1, b2⟩ := transfer_nhs_block_le W
    (cellProd z V (cellStart n a) (a.val % n) - blockT (E : ℂ) 0 ^ (a.val % n))
  set e₂ := (if cellStart n b = cellStart n a ∧ b.val % n < a.val % n then
      prodErr (nhs W) E z V (finRotate L b) (a.val % n - b.val % n - 1) else 0) with he₂
  have he₂0 : 0 ≤ e₂ := by
    rw [he₂]; split_ifs
    · exact transfer_nhs_nonneg _ _
    · exact le_rfl
  have hint : interpErr (nhs W) n E z V a b = e₁ + e₂ := rfl
  have hsrc : nhs W (if cellStart n b = cellStart n a ∧ b.val % n < a.val % n then
      (cellProd z V (finRotate L b) (a.val % n - b.val % n - 1) -
        blockT (E : ℂ) 0 ^ (a.val % n - b.val % n - 1)).toBlocks₁₁ else 0) ≤ e₂ := by
    rw [he₂]
    split_ifs with h
    · exact (transfer_nhs_block_le W _).1
    · simp [nhs]
  have g1 := norm_nonneg (blockOf G (cellStart n a) b)
  have g2 := norm_nonneg (blockOf G (cellPrev n a) b)
  rw [hint]
  calc _ ≤ nhs W ((cellProd z V (cellStart n a) (a.val % n) -
          blockT (E : ℂ) 0 ^ (a.val % n)).toBlocks₁₁ * blockOf G (cellStart n a) b) +
        nhs W ((cellProd z V (cellStart n a) (a.val % n) -
          blockT (E : ℂ) 0 ^ (a.val % n)).toBlocks₁₂ * blockOf G (cellPrev n a) b) + e₂ := by
        refine (transfer_nhs_add_le W _ _).trans (add_le_add (transfer_nhs_add_le W _ _) hsrc)
    _ ≤ e₁ * ‖blockOf G (cellStart n a) b‖ + e₁ * ‖blockOf G (cellPrev n a) b‖ + e₂ := by
        gcongr
        · exact (transfer_nhs_mul_le_right W _ _).trans (by gcongr; exact b1)
        · exact (transfer_nhs_mul_le_right W _ _).trans (by gcongr; exact b2)
    _ ≤ _ := by nlinarith

/-- `G_{ab} - Σ c_{aα} c_{bβ} G_{αβ} - d_{ab} I` splits into the first-coordinate remainder and the
`c_{aα}`-combination of the second-coordinate remainders. -/
private theorem transfer_decomp (n : ℕ) (E : ℝ) {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    blockOf G a b - interpBlock n E G a b = transferRem n E G a b +
      ∑ α, ((cellCoef n E a α : ℝ) : ℂ) • (blockOf G α b -
        (∑ β, ((cellCoef n E b β : ℝ) : ℂ) • blockOf G α β) -
          ((cellSrc n E b α : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) := by
  unfold interpBlock transferRem cellD
  simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_sum, add_smul, Finset.sum_smul]
  abel

private theorem transfer_blockOf_conjTranspose {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    blockOf Gᴴ a b = (blockOf G b a)ᴴ := by
  ext; simp [blockOf]

/-- The second-coordinate remainder is the adjoint of the first-coordinate remainder of `G^*`. -/
private theorem transfer_adj (n : ℕ) (E : ℝ) {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (b α : Fin L) :
    blockOf G α b - (∑ β, ((cellCoef n E b β : ℝ) : ℂ) • blockOf G α β) -
        ((cellSrc n E b α : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) =
      (transferRem n E Gᴴ b α)ᴴ := by
  unfold transferRem
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    transfer_blockOf_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one,
    Complex.star_def, Complex.conj_ofReal]

private theorem transfer_resolvent_conj {W L : ℕ} {V : Fin L → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ r, (V r).IsHermitian) (z : ℂ) :
    resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V)
        (starRingEnd ℂ z) =
      (resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V) z)ᴴ := by
  unfold resolventMat
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    (transfer_op_isHermitian hV).eq, Matrix.conjTranspose_one, Complex.star_def]

private theorem transfer_anchor_le (n : ℕ) {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b α β : Fin L)
    (hα : α = cellStart n a ∨ α = cellPrev n a) (hβ : β = cellStart n b ∨ β = cellPrev n b) :
    ‖blockOf G α β‖ ≤ anchorNorm n G a b := by
  unfold anchorNorm
  rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- The anchor blocks `G_{αb}`, `α` an anchor of the cell of `a`, written through the anchor pairs
and the second-coordinate remainder. -/
private theorem transfer_anchor_col (n : ℕ) (E : ℝ) {W L : ℕ} (hL : 2 ≤ L)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (b α : Fin L) :
    blockOf G α b = (transferRem n E Gᴴ b α)ᴴ +
      (((transferU E (b.val % n + 1) : ℝ) : ℂ) • blockOf G α (cellStart n b) +
        ((-transferU E (b.val % n) : ℝ) : ℂ) • blockOf G α (cellPrev n b)) +
      ((cellSrc n E b α : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
  rw [← transfer_adj, ← transfer_sum_coef hL E b (fun β => blockOf G α β)]
  abel

private theorem transfer_interpErr_nonneg {W L : ℕ} (n : ℕ) (E : ℝ) (z : ℂ)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (a b : Fin L) : 0 ≤ interpErr (nhs W) n E z V a b := by
  unfold interpErr
  have h1 : 0 ≤ prodErr (nhs W) E z V (cellStart n a) (a.val % n) := transfer_nhs_nonneg _ _
  split_ifs
  · have h2 : 0 ≤ prodErr (nhs W) E z V (finRotate L b) (a.val % n - b.val % n - 1) :=
      transfer_nhs_nonneg _ _
    linarith
  · linarith

/-! ## Statements -/

/-- At `g ≥ 1` the single-time matrix is `A_L ⊗ I + diag(√(uγ_g) V_r)`, (5.1) [fo:eq:flow]. -/
theorem flowH_cycle (g : ℝ) (hg : 1 ≤ g) (W L : ℕ) (u : ℝ) (ω : Ω W L) :
    flowH g W L u ω = cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) +
      blockDiagOp (fun r => ((Real.sqrt (u * gammaG g) : ℝ) : ℂ) • gueBlock W L ω r) := by
  have hA : Ag g L = cycleAdj L := by
    rw [Ag, max_eq_right hg, div_self (by linarith : g ≠ 0)]
    simp
  unfold flowH blockFlow blockV
  rw [hA]
  congr 1
  ext p q
  simp only [blockDiagOp, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  split_ifs <;> simp

/-- The discrete variation of constants (7.15) [uvc:eq:transfer-duhamel]: closeness at the real
energy `E` extends to every `z` with `n|z - E| ≤ 1`, with the loss `C n |z - E|`. -/
theorem cellClose_perturb (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W L n : ℕ) (E ε : ℝ) (z : ℂ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ),
      |E| ≤ 2 - κ → 0 ≤ ε → ε ≤ 1 → (n : ℝ) * ‖z - E‖ ≤ 1 → CellClose n E (E : ℂ) V ε →
        CellClose n E z V (ε + C * n * ‖z - E‖) := by
  refine ⟨(12 / κ + 1) ^ 2 * Real.exp (12 / κ + 1), by positivity, ?_⟩
  intro W L n E ε z V hE hε0 hε1 hnz hcl b j hbn hbL
  set M : ℝ := 12 / κ + 1 with hMdef
  set δ : ℝ := ‖z - (E : ℂ)‖ with hδ
  have hM0 : 0 ≤ M := by positivity
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hPE : ∀ (b' : Fin L) (r : ℕ), b'.val % n + r ≤ n → b'.val + r ≤ L →
      ‖cellProd (E : ℂ) V b' r‖ ≤ M := by
    intro b' r h1 h2
    have h3 := hcl b' r h1 h2
    unfold prodErr at h3
    have hT := transfer_free_norm_le (W := W) hκ hκ2 hE r
    calc ‖cellProd (E : ℂ) V b' r‖ =
          ‖(cellProd (E : ℂ) V b' r - blockT (E : ℂ) 0 ^ r) + blockT (E : ℂ) 0 ^ r‖ := by
          rw [sub_add_cancel]
      _ ≤ ε + 12 / κ := (norm_add_le _ _).trans (add_le_add h3 hT)
      _ ≤ M := by linarith
  have hJ : ‖(z - (E : ℂ)) • transferJ W‖ ≤ δ := by
    rw [norm_smul]
    have := transfer_normJ W
    nlinarith
  have hterm : ∀ r ≤ j, ∀ i ∈ Finset.range r,
      ‖cellProd (E : ℂ) V ((finRotate L ^ (i + 1)) b) (r - i - 1) * ((z - E) • transferJ W) *
        cellProd z V b i‖ ≤ M * δ * ‖cellProd z V b i‖ := by
    intro r hr i hi
    have hi' := Finset.mem_range.mp hi
    obtain ⟨a1, a2⟩ := transfer_shift_adm b hi' (by omega : b.val % n + r ≤ n) (by omega)
    have hQ := hPE _ _ a1 a2
    calc _ ≤ ‖cellProd (E : ℂ) V ((finRotate L ^ (i + 1)) b) (r - i - 1) *
            ((z - E) • transferJ W)‖ * ‖cellProd z V b i‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖cellProd (E : ℂ) V ((finRotate L ^ (i + 1)) b) (r - i - 1)‖ *
            ‖(z - E) • transferJ W‖) * ‖cellProd z V b i‖ := by
          gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ M * δ * ‖cellProd z V b i‖ := by gcongr
  have hgr := transfer_gronwall (c := M * δ) (by positivity) (fun r => ‖cellProd z V b r‖) j
    (fun r hr => by
      rw [transfer_duhamel z (E : ℂ) V b r]
      refine (norm_add_le _ _).trans (add_le_add (hPE b r (by omega) (by omega)) ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      exact hterm r hr i hi)
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast (by omega : j ≤ n)
  have hexp : ∀ i ∈ Finset.range j, (1 + M * δ) ^ i ≤ Real.exp M := by
    intro i hi
    have hi' : (i : ℝ) ≤ n := by
      have := Finset.mem_range.mp hi
      exact_mod_cast (by omega : i ≤ n)
    calc (1 + M * δ) ^ i ≤ Real.exp (M * δ) ^ i := by
          gcongr
          linarith [Real.add_one_le_exp (M * δ)]
      _ = Real.exp (i * (M * δ)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp M := by
          apply Real.exp_le_exp.mpr
          have : (i : ℝ) * δ ≤ 1 := le_trans (by gcongr) hnz
          nlinarith
  unfold prodErr
  rw [transfer_duhamel z (E : ℂ) V b j]
  have h0 := hcl b j hbn hbL
  unfold prodErr at h0
  calc ‖cellProd (E : ℂ) V b j + ∑ r ∈ Finset.range j,
        cellProd (E : ℂ) V ((finRotate L ^ (r + 1)) b) (j - r - 1) * ((z - E) • transferJ W) *
          cellProd z V b r - blockT (E : ℂ) 0 ^ j‖
      = ‖(cellProd (E : ℂ) V b j - blockT (E : ℂ) 0 ^ j) + ∑ r ∈ Finset.range j,
        cellProd (E : ℂ) V ((finRotate L ^ (r + 1)) b) (j - r - 1) * ((z - E) • transferJ W) *
          cellProd z V b r‖ := by congr 1; abel
    _ ≤ ε + ∑ r ∈ Finset.range j, M * δ * (M * Real.exp M) := by
        refine (norm_add_le _ _).trans (add_le_add h0 ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
        refine (hterm j le_rfl r hr).trans ?_
        have := hgr r (by have := Finset.mem_range.mp hr; omega)
        have := hexp r hr
        have hMd : 0 ≤ M * δ := by positivity
        calc M * δ * ‖cellProd z V b r‖ ≤ M * δ * (M * (1 + M * δ) ^ r) := by gcongr
          _ ≤ M * δ * (M * Real.exp M) := by gcongr
    _ ≤ ε + M ^ 2 * Real.exp M * n * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have : 0 ≤ M * δ * (M * Real.exp M) := by positivity
        nlinarith

/-- Proposition 7.4 [uvc:prop:green], (7.10) [uvc:eq:interpolate], deterministic form: if the
transfer products are `ε`-close to the free ones at `z` and at `z̄`, then
`‖G_{ab} - Σ c_{aα} c_{bβ} G_{αβ} - d_{ab} I‖ ≤ C ε (1 + max_{anchors} ‖G_{αβ}‖)`. -/
theorem green_interp (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W L n : ℕ) (E ε : ℝ) (z : ℂ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ),
      3 ≤ L → 1 ≤ n → |E| ≤ 2 - κ → (∀ r, (V r).IsHermitian) → z.im ≠ 0 → 0 ≤ ε → ε ≤ 1 →
      CellClose n E z V ε → CellClose n E (starRingEnd ℂ z) V ε →
      let G := resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V) z
      ∀ a b : Fin L, ‖blockOf G a b - interpBlock n E G a b‖ ≤ C * ε * (1 + anchorNorm n G a b) := by
  refine ⟨16 / κ + 4, by positivity, ?_⟩
  intro W L n E ε z V hL hn hE hV hz hε0 hε1 hcl hcl' G a b
  have hL2 : 2 ≤ L := by omega
  have hE' : |E| < 2 := by linarith
  set K : ℝ := 2 / κ with hK
  have hK0 : 0 ≤ K := by positivity
  have hHerm := transfer_op_isHermitian hV
  have hG : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
      z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * G = 1 :=
    sub_smul_mul_resolventMat hHerm hz
  have hz' : (starRingEnd ℂ z).im ≠ 0 := by simpa using hz
  have hG' : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
      (starRingEnd ℂ z) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * Gᴴ = 1 := by
    rw [← transfer_resolvent_conj hV]
    exact sub_smul_mul_resolventMat hHerm hz'
  set A := anchorNorm n G a b with hA
  have hA0 : 0 ≤ A := (norm_nonneg _).trans
    (transfer_anchor_le n G a b _ _ (Or.inl rfl) (Or.inl rfl))
  -- the second-coordinate remainders at the anchors of `a`
  have hX : ∀ α, (α = cellStart n a ∨ α = cellPrev n a) →
      ‖(transferRem n E Gᴴ b α)ᴴ‖ ≤ ε * (1 + 2 * A) := by
    intro α hα
    rw [Matrix.l2_opNorm_conjTranspose]
    refine (transfer_rem_op hL2 hn hE' hε0 V _ Gᴴ hG' hcl' b α).trans ?_
    rw [transfer_blockOf_conjTranspose, transfer_blockOf_conjTranspose,
      Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose]
    have h1 := transfer_anchor_le n G a b α (cellStart n b) hα (Or.inl rfl)
    have h2 := transfer_anchor_le n G a b α (cellPrev n b) hα (Or.inr rfl)
    have : 1 + ‖blockOf G α (cellStart n b)‖ + ‖blockOf G α (cellPrev n b)‖ ≤ 1 + 2 * A := by
      linarith
    exact mul_le_mul_of_nonneg_left this hε0
  -- the anchor columns
  have hcol : ∀ α, (α = cellStart n a ∨ α = cellPrev n a) →
      ‖blockOf G α b‖ ≤ 2 * K * A + K + (1 + 2 * A) := by
    intro α hα
    rw [transfer_anchor_col n E hL2 G b α]
    have c1 := transferU_abs_le hκ hκ2 hE (b.val % n + 1)
    have c2 := transferU_abs_le hκ hκ2 hE (b.val % n)
    have c3 := transfer_src_abs_le hκ hκ2 hE n b α
    have h1 := transfer_anchor_le n G a b α (cellStart n b) hα (Or.inl rfl)
    have h2 := transfer_anchor_le n G a b α (cellPrev n b) hα (Or.inr rfl)
    have hXα := hX α hα
    have hs : ∀ (c : ℝ) (Y : Matrix (Fin W) (Fin W) ℂ), ‖((c : ℝ) : ℂ) • Y‖ = |c| * ‖Y‖ := by
      intro c Y; rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hone : ‖((cellSrc n E b α : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ K :=
      (transfer_norm_smul_one_le _).trans (by rw [Complex.norm_real, Real.norm_eq_abs]; exact c3)
    have t1 : ‖((transferU E (b.val % n + 1) : ℝ) : ℂ) • blockOf G α (cellStart n b)‖ ≤ K * A := by
      rw [hs]; exact mul_le_mul c1 h1 (norm_nonneg _) hK0
    have t2 : ‖((-transferU E (b.val % n) : ℝ) : ℂ) • blockOf G α (cellPrev n b)‖ ≤ K * A := by
      rw [hs, abs_neg]; exact mul_le_mul c2 h2 (norm_nonneg _) hK0
    have hε' : ε * (1 + 2 * A) ≤ 1 + 2 * A := by nlinarith
    calc _ ≤ ‖(transferRem n E Gᴴ b α)ᴴ‖ +
          (‖((transferU E (b.val % n + 1) : ℝ) : ℂ) • blockOf G α (cellStart n b)‖ +
            ‖((-transferU E (b.val % n) : ℝ) : ℂ) • blockOf G α (cellPrev n b)‖) +
          ‖((cellSrc n E b α : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ :=
        (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add le_rfl (norm_add_le _ _))) le_rfl)
      _ ≤ (1 + 2 * A) + (K * A + K * A) + K := by gcongr; exact hXα.trans hε'
      _ = _ := by ring
  rw [transfer_decomp, transfer_sum_coef hL2]
  simp only [transfer_adj]
  have hR := transfer_rem_op hL2 hn hE' hε0 V z G hG hcl a b
  have g1 := hcol _ (Or.inl rfl)
  have g2 := hcol _ (Or.inr rfl)
  have x1 := hX _ (Or.inl rfl)
  have x2 := hX _ (Or.inr rfl)
  have c1 := transferU_abs_le hκ hκ2 hE (a.val % n + 1)
  have c2 := transferU_abs_le hκ hκ2 hE (a.val % n)
  have hs : ∀ (c : ℝ) (Y : Matrix (Fin W) (Fin W) ℂ), ‖((c : ℝ) : ℂ) • Y‖ = |c| * ‖Y‖ := by
    intro c Y; rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have t1 : ‖((transferU E (a.val % n + 1) : ℝ) : ℂ) •
      (transferRem n E Gᴴ b (cellStart n a))ᴴ‖ ≤ K * (ε * (1 + 2 * A)) := by
    rw [hs]; exact mul_le_mul c1 x1 (norm_nonneg _) hK0
  have t2 : ‖((-transferU E (a.val % n) : ℝ) : ℂ) •
      (transferRem n E Gᴴ b (cellPrev n a))ᴴ‖ ≤ K * (ε * (1 + 2 * A)) := by
    rw [hs, abs_neg]; exact mul_le_mul c2 x2 (norm_nonneg _) hK0
  have hR' : ‖transferRem n E G a b‖ ≤ ε * (1 + 2 * (2 * K * A + K + (1 + 2 * A))) := by
    refine hR.trans (mul_le_mul_of_nonneg_left ?_ hε0)
    linarith
  calc _ ≤ ‖transferRem n E G a b‖ +
        (‖((transferU E (a.val % n + 1) : ℝ) : ℂ) • (transferRem n E Gᴴ b (cellStart n a))ᴴ‖ +
          ‖((-transferU E (a.val % n) : ℝ) : ℂ) • (transferRem n E Gᴴ b (cellPrev n a))ᴴ‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ ε * (1 + 2 * (2 * K * A + K + (1 + 2 * A))) +
        (K * (ε * (1 + 2 * A)) + K * (ε * (1 + 2 * A))) := by gcongr
    _ = ε * ((3 + 4 * K) + (8 * K + 4) * A) := by ring
    _ ≤ ε * ((8 * K + 4) * (1 + A)) := by
        apply mul_le_mul_of_nonneg_left _ hε0
        nlinarith
    _ = (16 / κ + 4) * ε * (1 + A) := by rw [hK]; ring

/-- Proposition 7.4 [uvc:prop:green] in the normalized Hilbert–Schmidt norm (the algebraic
remainder of Section 7.3.2 [sec:common-interpolation-proof]): the remainder is bounded by the
errors of the transfer products used for `G_{ab}` times `1 + interpEnv`. -/
theorem green_interp_hs (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W L n : ℕ) (E : ℝ) (z : ℂ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ),
      1 ≤ W → 3 ≤ L → 1 ≤ n → |E| ≤ 2 - κ → (∀ r, (V r).IsHermitian) → z.im ≠ 0 →
      let G := resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V) z
      ∀ a b : Fin L,
        nhs W (blockOf G a b - interpBlock n E G a b) ≤
          C * (interpErr (nhs W) n E z V a b +
              interpErr (nhs W) n E (starRingEnd ℂ z) V b (cellStart n a) +
              interpErr (nhs W) n E (starRingEnd ℂ z) V b (cellPrev n a)) *
            (1 + interpEnv n G a b) := by
  refine ⟨2 + 4 / κ, by positivity, ?_⟩
  intro W L n E z V _ hL hn hE hV hz G a b
  have hL2 : 2 ≤ L := by omega
  have hE' : |E| < 2 := by linarith
  set K : ℝ := 2 / κ with hK
  have hK0 : 0 ≤ K := by positivity
  have hHerm := transfer_op_isHermitian hV
  have hG : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
      z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * G = 1 :=
    sub_smul_mul_resolventMat hHerm hz
  have hz' : (starRingEnd ℂ z).im ≠ 0 := by simpa using hz
  have hG' : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
      (starRingEnd ℂ z) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * Gᴴ = 1 := by
    rw [← transfer_resolvent_conj hV]
    exact sub_smul_mul_resolventMat hHerm hz'
  set I := interpEnv n G a b with hI
  have hAI : anchorNorm n G a b ≤ I := le_max_left _ _
  have hsI : ‖blockOf G (cellStart n a) b‖ ≤ I := (le_max_left _ _).trans (le_max_right _ _)
  have hpI : ‖blockOf G (cellPrev n a) b‖ ≤ I := (le_max_right _ _).trans (le_max_right _ _)
  have hI0 : 0 ≤ I := (norm_nonneg _).trans hsI
  set e₁ := interpErr (nhs W) n E z V a b
  set e₂ := interpErr (nhs W) n E (starRingEnd ℂ z) V b (cellStart n a)
  set e₃ := interpErr (nhs W) n E (starRingEnd ℂ z) V b (cellPrev n a)
  have he₁ : 0 ≤ e₁ := transfer_interpErr_nonneg _ _ _ _ _ _
  have he₂ : 0 ≤ e₂ := transfer_interpErr_nonneg _ _ _ _ _ _
  have he₃ : 0 ≤ e₃ := transfer_interpErr_nonneg _ _ _ _ _ _
  have hX : ∀ α, (α = cellStart n a ∨ α = cellPrev n a) →
      nhs W (transferRem n E Gᴴ b α)ᴴ ≤
        interpErr (nhs W) n E (starRingEnd ℂ z) V b α * (1 + 2 * I) := by
    intro α hα
    rw [transfer_nhs_conjTranspose]
    refine (transfer_rem_hs hL2 hn hE' V _ Gᴴ hG' b α).trans ?_
    rw [transfer_blockOf_conjTranspose, transfer_blockOf_conjTranspose,
      Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose]
    have h1 := transfer_anchor_le n G a b α (cellStart n b) hα (Or.inl rfl)
    have h2 := transfer_anchor_le n G a b α (cellPrev n b) hα (Or.inr rfl)
    exact mul_le_mul_of_nonneg_left (by linarith) (transfer_interpErr_nonneg _ _ _ _ _ _)
  have hR : nhs W (transferRem n E G a b) ≤ e₁ * (1 + 2 * I) :=
    (transfer_rem_hs hL2 hn hE' V z G hG a b).trans
      (mul_le_mul_of_nonneg_left (by linarith) he₁)
  rw [transfer_decomp, transfer_sum_coef hL2]
  simp only [transfer_adj]
  have c1 := transferU_abs_le hκ hκ2 hE (a.val % n + 1)
  have c2 := transferU_abs_le hκ hκ2 hE (a.val % n)
  have t1 : nhs W (((transferU E (a.val % n + 1) : ℝ) : ℂ) •
      (transferRem n E Gᴴ b (cellStart n a))ᴴ) ≤ K * (e₂ * (1 + 2 * I)) := by
    rw [transfer_nhs_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul c1 (hX _ (Or.inl rfl)) (transfer_nhs_nonneg _ _) hK0
  have t2 : nhs W (((-transferU E (a.val % n) : ℝ) : ℂ) •
      (transferRem n E Gᴴ b (cellPrev n a))ᴴ) ≤ K * (e₃ * (1 + 2 * I)) := by
    rw [transfer_nhs_smul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    exact mul_le_mul c2 (hX _ (Or.inr rfl)) (transfer_nhs_nonneg _ _) hK0
  calc _ ≤ nhs W (transferRem n E G a b) +
        (nhs W (((transferU E (a.val % n + 1) : ℝ) : ℂ) • (transferRem n E Gᴴ b (cellStart n a))ᴴ) +
          nhs W (((-transferU E (a.val % n) : ℝ) : ℂ) • (transferRem n E Gᴴ b (cellPrev n a))ᴴ)) :=
        (transfer_nhs_add_le W _ _).trans (add_le_add le_rfl (transfer_nhs_add_le W _ _))
    _ ≤ e₁ * (1 + 2 * I) + (K * (e₂ * (1 + 2 * I)) + K * (e₃ * (1 + 2 * I))) := by gcongr
    _ ≤ (2 + 4 / κ) * (e₁ + e₂ + e₃) * (1 + I) := by
        rw [show (2 + 4 / κ) = 2 * (1 + K) by rw [hK]; ring]
        have h1 : 1 + 2 * I ≤ 2 * (1 + I) := by linarith
        have hsum : 0 ≤ e₁ + K * e₂ + K * e₃ := by positivity
        calc e₁ * (1 + 2 * I) + (K * (e₂ * (1 + 2 * I)) + K * (e₃ * (1 + 2 * I)))
            = (e₁ + K * e₂ + K * e₃) * (1 + 2 * I) := by ring
          _ ≤ (e₁ + K * e₂ + K * e₃) * (2 * (1 + I)) := mul_le_mul_of_nonneg_left h1 hsum
          _ ≤ ((1 + K) * (e₁ + e₂ + e₃)) * (2 * (1 + I)) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              nlinarith
          _ = 2 * (1 + K) * (e₁ + e₂ + e₃) * (1 + I) := by ring

end LSBA
