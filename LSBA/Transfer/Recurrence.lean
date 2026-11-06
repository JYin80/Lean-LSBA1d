import LSBA.Transfer.Basic
import LSBA.Gauss.GUE
import LSBA.Volume.LocalComparison
import LSBA.Spectral.Resolvent

/-!
# The transfer recurrence

The flow `H_t(g)` of (5.1) [fo:eq:flow] as `blockFlow`, the transfer recurrence satisfied by a
column of the resolvent away from its source block, the arc products along a deterministic
direction, and the pathwise bound (7.5) [uvs:eq:pathwise-green-block] on `‖G_{ab}‖` by arc products
(Section 7.2
[sec:uniform-resolvent-seed]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

private theorem recurrence_blockDiagOp_smul {W L : ℕ} (c : ℂ)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    blockDiagOp (fun a => c • V a) = c • blockDiagOp V := by
  ext ⟨a, α⟩ ⟨b, β⟩
  by_cases h : a = b <;> simp [blockDiagOp, h]

private theorem recurrence_sqrt_gammaG (g : ℝ) : Real.sqrt (gammaG g) = (max 1 g)⁻¹ := by
  have h1 : (0 : ℝ) ≤ max 1 g := le_trans zero_le_one (le_max_left 1 g)
  rw [gammaG, Real.sqrt_inv, Real.sqrt_sq h1]

/-- `H_t(g) = A_g ⊗ I + √(t γ_g) V` equals `Hdet g (√t V)`, (5.1) [fo:eq:flow] and (1.3)
[eq:model]. -/
theorem blockFlow_Ag_eq_Hdet (g t : ℝ) (W L : ℕ) (ω : Ω W L) :
    blockFlow W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (t * gammaG g) ω =
      Hdet g (fun a => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω a) := by
  have hγ : 0 ≤ gammaG g := by unfold gammaG; positivity
  have h1 : (max 1 g : ℝ) ≠ 0 := (lt_of_lt_of_le one_pos (le_max_left 1 g)).ne'
  have h1c : ((max 1 g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1
  unfold blockFlow Hdet blockV Ag
  rw [recurrence_blockDiagOp_smul, Real.sqrt_mul' t hγ, recurrence_sqrt_gammaG,
    Matrix.smul_kronecker, smul_add, smul_smul, smul_smul]
  congr 2
  · push_cast
    field_simp
  · push_cast
    ring

theorem Hmat_eq_blockFlow (g : ℝ) (W L : ℕ) (ω : Ω W L) :
    Hmat g W L ω = blockFlow W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (gammaG g) ω := by
  have h := blockFlow_Ag_eq_Hdet g 1 W L ω
  rw [one_mul] at h
  rw [h, Hmat]
  simp

/-- The vector `(x, y) ∈ ℂ² ⊗ ℂ^W`. -/
def pairVec {W : ℕ} (x y : Fin W → ℂ) : Fin 2 × Fin W → ℂ :=
  fun p => if p.1 = 0 then x p.2 else y p.2

/-- The block `a + j` (`d = true`) or `a - j` (`d = false`) of the cycle `ℤ_L`. -/
def arcBlock {L : ℕ} (a : Fin L) (d : Bool) (j : ℕ) : Fin L :=
  if d then (finRotate L ^ j) a else ((finRotate L)⁻¹ ^ j) a

/-- The direction of the arc from `a` of length `n` used in Section 7.2
[sec:uniform-resolvent-seed]: forward unless the forward interior meets `b`. -/
def arcDir {L : ℕ} (a b : Fin L) (n : ℕ) : Bool :=
  decide (∀ i ∈ Finset.Ico 1 n, arcBlock a true i ≠ b)

/-- `K_a`: the maximal inverse-transfer norm on the arc `a, a ± 1, …, a ± n`, including the
identity, Section 7.2 [sec:uniform-resolvent-seed]. -/
def arcK {W L : ℕ} (g : ℝ) (z : ℂ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (a : Fin L) (d : Bool)
    (n : ℕ) : ℝ :=
  ⨆ j : Fin n, ‖(transferProd g z (fun i => V (arcBlock a d (i + 1))) j)⁻¹‖

/-! ### Arcs on the cycle -/

private theorem recurrence_arcBlock_true {L : ℕ} (a : Fin L) (j : ℕ) :
    arcBlock a true j = (finRotate L ^ j) a := rfl

private theorem recurrence_arcBlock_false {L : ℕ} (a : Fin L) (j : ℕ) :
    arcBlock a false j = ((finRotate L)⁻¹ ^ j) a := rfl

private theorem recurrence_perm_inv_apply {α : Type*} (σ : Equiv.Perm α) (x : α) :
    σ⁻¹ (σ x) = x := by
  rw [Equiv.Perm.inv_def]
  exact σ.symm_apply_apply x

private theorem recurrence_perm_apply_inv {α : Type*} (σ : Equiv.Perm α) (x : α) :
    σ (σ⁻¹ x) = x := by
  rw [Equiv.Perm.inv_def]
  exact σ.apply_symm_apply x

private theorem recurrence_arcBlock_zero {L : ℕ} (a : Fin L) (d : Bool) : arcBlock a d 0 = a := by
  cases d <;> simp [recurrence_arcBlock_true, recurrence_arcBlock_false]

private theorem recurrence_arcBlock_one_true {L : ℕ} (a : Fin L) :
    arcBlock a true 1 = finRotate L a := by
  rw [recurrence_arcBlock_true, pow_one]

private theorem recurrence_arcBlock_one_false {L : ℕ} (a : Fin L) :
    arcBlock a false 1 = (finRotate L)⁻¹ a := by
  rw [recurrence_arcBlock_false, pow_one]

private theorem recurrence_arcBlock_add {L : ℕ} (a : Fin L) (d : Bool) (i j : ℕ) :
    arcBlock (arcBlock a d i) d j = arcBlock a d (i + j) := by
  cases d
  · rw [recurrence_arcBlock_false, recurrence_arcBlock_false, recurrence_arcBlock_false,
      add_comm i j, pow_add, Equiv.Perm.mul_apply]
  · rw [recurrence_arcBlock_true, recurrence_arcBlock_true, recurrence_arcBlock_true,
      add_comm i j, pow_add, Equiv.Perm.mul_apply]

private theorem recurrence_arcBlock_back {L : ℕ} (a : Fin L) (d : Bool) (j : ℕ) :
    arcBlock (arcBlock a d (j + 1)) (!d) 1 = arcBlock a d j := by
  cases d
  · rw [Bool.not_false, recurrence_arcBlock_one_true, recurrence_arcBlock_false,
      recurrence_arcBlock_false, pow_succ', Equiv.Perm.mul_apply, recurrence_perm_apply_inv]
  · rw [Bool.not_true, recurrence_arcBlock_one_false, recurrence_arcBlock_true,
      recurrence_arcBlock_true, pow_succ', Equiv.Perm.mul_apply, recurrence_perm_inv_apply]

private theorem recurrence_arcBlock_cancel {L : ℕ} (a : Fin L) (k : ℕ) :
    arcBlock (arcBlock a false k) true k = a := by
  rw [recurrence_arcBlock_true, recurrence_arcBlock_false, ← Equiv.Perm.mul_apply, inv_pow,
    mul_inv_cancel]
  rfl

private theorem recurrence_val_finRotate {L : ℕ} (x : Fin L) :
    (finRotate L x).val = (x.val + 1) % L := by
  cases L with
  | zero => exact x.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : x = Fin.last n
    · subst h
      simp
    · simp only [h, ↓reduceIte]
      have : x.val < n := by
        have h1 := x.isLt
        have h2 : x.val ≠ n := fun h' => h (Fin.ext (by simpa using h'))
        omega
      rw [Nat.mod_eq_of_lt (by omega)]

private theorem recurrence_arcBlock_true_val {L : ℕ} (a : Fin L) (j : ℕ) :
    (arcBlock a true j).val = (a.val + j) % L := by
  induction j with
  | zero =>
    rw [recurrence_arcBlock_zero]
    exact (Nat.mod_eq_of_lt a.isLt).symm
  | succ j ih =>
    have h := recurrence_arcBlock_add a true j 1
    rw [← h, recurrence_arcBlock_one_true, recurrence_val_finRotate, ih, Nat.mod_add_mod]
    rfl

/-- Moving `k` steps with `0 < k < L` leaves every block. -/
private theorem recurrence_arcBlock_ne_self {L : ℕ} (a : Fin L) (d : Bool) {k : ℕ} (hk0 : 0 < k)
    (hkL : k < L) : arcBlock a d k ≠ a := by
  have key : arcBlock a true k ≠ a := by
    intro h
    have h1 := congrArg Fin.val h
    rw [recurrence_arcBlock_true_val] at h1
    have h2 := a.isLt
    by_cases h3 : a.val + k < L
    · rw [Nat.mod_eq_of_lt h3] at h1
      omega
    · rw [Nat.mod_eq_sub_mod (not_lt.mp h3), Nat.mod_eq_of_lt (by omega)] at h1
      omega
  cases d
  · intro h
    apply key
    have := recurrence_arcBlock_cancel a k
    rw [h] at this
    exact this
  · exact key

private theorem recurrence_arcBlock_injOn {L : ℕ} (a : Fin L) (d : Bool) {n : ℕ} (hn : n + 1 ≤ L) :
    Set.InjOn (arcBlock a d) ↑(Finset.range (n + 1)) := by
  have key : ∀ j j' : ℕ, j < j' → j' ≤ n → arcBlock a d j ≠ arcBlock a d j' := by
    intro j j' hjj hj'n h
    have h1 : arcBlock (arcBlock a d j) d (j' - j) = arcBlock a d j := by
      rw [recurrence_arcBlock_add, Nat.add_sub_cancel' hjj.le]
      exact h.symm
    exact recurrence_arcBlock_ne_self _ d (by omega) (by omega) h1
  intro j hj j' hj' h
  simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd h (key j j' hlt (by omega))
  · exact heq
  · exact absurd h.symm (key j' j hgt (by omega))

/-- A nonnegative function summed along an arc of `n + 1 ≤ L` distinct blocks is at most its sum
over the cycle. -/
private theorem recurrence_sum_arc_le {L : ℕ} (a : Fin L) (d : Bool) {n : ℕ} (hn : n + 1 ≤ L)
    (s : Fin L → ℝ) (hs : ∀ c, 0 ≤ s c) :
    ∑ j ∈ Finset.range (n + 1), s (arcBlock a d j) ≤ ∑ c, s c := by
  rw [← Finset.sum_image (f := s) (g := arcBlock a d) (fun j hj j' hj' h =>
    recurrence_arcBlock_injOn a d hn hj hj' h)]
  exact Finset.sum_le_univ_sum_of_nonneg hs

/-! ### The row equation of the resolvent -/

private theorem recurrence_cycleAdj_apply {L : ℕ} (x y : Fin L) :
    cycleAdj L x y = (if y = finRotate L x then 1 else 0) +
      (if y = (finRotate L)⁻¹ x then 1 else 0) := by
  unfold cycleAdj
  simp only [Matrix.of_apply]
  have h1 : (y.val = (x.val + 1) % L) ↔ y = finRotate L x := by
    rw [← recurrence_val_finRotate, Fin.ext_iff]
  have h2 : (x.val = (y.val + 1) % L) ↔ y = (finRotate L)⁻¹ x := by
    rw [← recurrence_val_finRotate, ← Fin.ext_iff, eq_comm, Equiv.Perm.eq_inv_iff_eq]
  simp only [h1, h2]

private theorem recurrence_mulVec_cycle {W L : ℕ} (F : Fin L × Fin W → ℂ) (x : Fin L) (α : Fin W) :
    ((cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *ᵥ F) (x, α) =
      F (finRotate L x, α) + F ((finRotate L)⁻¹ x, α) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, recurrence_cycleAdj_apply]
  simp [add_mul, Finset.sum_add_distrib, ite_mul]

private theorem recurrence_mulVec_blockDiagOp {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (F : Fin L × Fin W → ℂ) (x : Fin L) (α : Fin W) :
    (blockDiagOp V *ᵥ F) (x, α) = (V x *ᵥ fun γ => F (x, γ)) α := by
  simp [Matrix.mulVec, dotProduct, blockDiagOp, Fintype.sum_prod_type]

private theorem recurrence_Hdet_eq {W L : ℕ} {g : ℝ} (hg : 1 ≤ g)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    Hdet g V = cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + ((g : ℂ)⁻¹) • blockDiagOp V := by
  have hm : max 1 g = g := max_eq_right hg
  have hg0 : (g : ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le one_pos hg).ne'
  unfold Hdet
  rw [hm, smul_add, smul_smul, inv_mul_cancel₀ hg0, one_smul]

/-- The vector `ι_b u` supported on the block `b`. -/
private def recurrence_embed {W L : ℕ} (b : Fin L) (u : Fin W → ℂ) : Fin L × Fin W → ℂ :=
  fun p => if p.1 = b then u p.2 else 0

private theorem recurrence_blockOf_mulVec {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (b : Fin L) (u : Fin W → ℂ) (y : Fin L) :
    blockOf G y b *ᵥ u = fun γ => (G *ᵥ recurrence_embed b u) (y, γ) := by
  funext α
  simp [Matrix.mulVec, dotProduct, blockOf, recurrence_embed, Fintype.sum_prod_type]

/-- Row `x` of `(H - z) G = 1` applied to `ι_b u`, for `H = Hdet g V` with `1 ≤ g`:
`f_{x+1} + f_{x-1} + (V_x / g) f_x - z f_x = δ_{xb} u` with `f_y = G_{yb} u`. -/
private theorem recurrence_row {W L : ℕ} {g : ℝ} (hg : 1 ≤ g)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ a, (V a).IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (b : Fin L) (u : Fin W → ℂ) (x : Fin L) :
    blockOf (resolventMat (Hdet g V) z) (finRotate L x) b *ᵥ u +
      blockOf (resolventMat (Hdet g V) z) ((finRotate L)⁻¹ x) b *ᵥ u +
      ((g : ℂ)⁻¹) • (V x *ᵥ (blockOf (resolventMat (Hdet g V) z) x b *ᵥ u)) -
      z • (blockOf (resolventMat (Hdet g V) z) x b *ᵥ u) = if x = b then u else 0 := by
  have hH := Hdet_isHermitian g hV
  have h1 := sub_smul_mul_resolventMat hH hz
  set G := resolventMat (Hdet g V) z with hG
  set F := G *ᵥ recurrence_embed b u with hF
  have h2 : (Hdet g V - z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) *ᵥ F =
      recurrence_embed b u := by
    rw [hF, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  funext α
  have h3 := congrFun h2 (x, α)
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply,
    recurrence_Hdet_eq hg, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply,
    recurrence_mulVec_cycle, recurrence_mulVec_blockDiagOp] at h3
  simp only [recurrence_blockOf_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  rw [← hF]
  simp only [recurrence_embed] at h3
  by_cases hxb : x = b
  · simp only [hxb, ↓reduceIte] at h3 ⊢
    simpa [smul_eq_mul] using h3
  · simp only [hxb, ↓reduceIte] at h3 ⊢
    simpa [smul_eq_mul] using h3

/-- `T_x(z) (p, q) = (z p - V p / g - q, p)`. -/
private theorem recurrence_transferMat_mulVec_pairVec {W : ℕ} (g : ℝ) (z : ℂ)
    (V : Matrix (Fin W) (Fin W) ℂ) (p q : Fin W → ℂ) :
    transferMat g z V *ᵥ pairVec p q = pairVec (z • p - ((g : ℂ)⁻¹) • (V *ᵥ p) - q) p := by
  funext ⟨i, α⟩
  fin_cases i
  · simp [transferMat, transferFree, pairVec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply, sub_mul,
      Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    simp only [mul_assoc]
    ring
  · simp [transferMat, transferFree, pairVec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- Transfer recurrence of Section 7.2 [sec:uniform-resolvent-seed]: away from the source block
`b`, `f_x = G_{xb} u` satisfies `(f_{x±1}, f_x) = T_x(z) (f_x, f_{x∓1})`. -/
theorem pairVec_resolvent_step {W L : ℕ} (hL : 3 ≤ L) {g : ℝ} (hg : 1 ≤ g)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ a, (V a).IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (b : Fin L) (u : Fin W → ℂ) (d : Bool) (x : Fin L) (hx : x ≠ b) :
    pairVec (blockOf (resolventMat (Hdet g V) z) (arcBlock x d 1) b *ᵥ u)
        (blockOf (resolventMat (Hdet g V) z) x b *ᵥ u) =
      transferMat g z (V x) *ᵥ pairVec (blockOf (resolventMat (Hdet g V) z) x b *ᵥ u)
        (blockOf (resolventMat (Hdet g V) z) (arcBlock x (!d) 1) b *ᵥ u) := by
  -- The identity holds for every `L`; the hypothesis `hL` is not used.
  have _ := hL
  have hrow := recurrence_row hg V hV hz b u x
  simp only [hx, ↓reduceIte] at hrow
  rw [recurrence_transferMat_mulVec_pairVec]
  cases d
  · simp only [Bool.not_false, recurrence_arcBlock_one_true, recurrence_arcBlock_one_false]
    unfold pairVec
    funext p
    split_ifs
    · have := congrFun hrow p.2
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this ⊢
      linear_combination this
    · rfl
  · simp only [Bool.not_true, recurrence_arcBlock_one_true, recurrence_arcBlock_one_false]
    unfold pairVec
    funext p
    split_ifs
    · have := congrFun hrow p.2
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this ⊢
      linear_combination this
    · rfl

/-- Iterated recurrence along an arc whose blocks `a ± 1, …, a ± j` avoid `b`. -/
theorem pairVec_resolvent_arc {W L : ℕ} (hL : 3 ≤ L) {g : ℝ} (hg : 1 ≤ g)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ a, (V a).IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (b : Fin L) (u : Fin W → ℂ) (a : Fin L) (d : Bool) (j : ℕ)
    (hb : ∀ i, 1 ≤ i → i ≤ j → arcBlock a d i ≠ b) :
    pairVec (blockOf (resolventMat (Hdet g V) z) (arcBlock a d (j + 1)) b *ᵥ u)
        (blockOf (resolventMat (Hdet g V) z) (arcBlock a d j) b *ᵥ u) =
      transferProd g z (fun i => V (arcBlock a d (i + 1))) j *ᵥ
        pairVec (blockOf (resolventMat (Hdet g V) z) (arcBlock a d 1) b *ᵥ u)
          (blockOf (resolventMat (Hdet g V) z) a b *ᵥ u) := by
  induction j with
  | zero =>
    simp [transferProd, recurrence_arcBlock_zero]
  | succ j ih =>
    have ih' := ih fun i h1 h2 => hb i h1 (by omega)
    have hx : arcBlock a d (j + 1) ≠ b := hb (j + 1) (by omega) le_rfl
    have hstep := pairVec_resolvent_step hL hg V hV hz b u d (arcBlock a d (j + 1)) hx
    rw [recurrence_arcBlock_add, recurrence_arcBlock_back, ih'] at hstep
    rw [transferProd, ← Matrix.mulVec_mulVec]
    exact hstep

/-! ### The arc inequality -/

/-- The sum of squared moduli of the entries of a vector. -/
private def recurrence_nsq {n : Type*} [Fintype n] (v : n → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

private theorem recurrence_nsq_nonneg {n : Type*} [Fintype n] (v : n → ℂ) :
    0 ≤ recurrence_nsq v :=
  Finset.sum_nonneg fun _ _ => by positivity

private theorem recurrence_nsq_pairVec {W : ℕ} (x y : Fin W → ℂ) :
    recurrence_nsq (pairVec x y) = recurrence_nsq x + recurrence_nsq y := by
  simp [recurrence_nsq, pairVec, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem recurrence_nsq_mulVec_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (u : n → ℂ) :
    recurrence_nsq (A *ᵥ u) ≤ ‖A‖ ^ 2 * recurrence_nsq u := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 u)
  have h1 : ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ u)‖ ^ 2 = recurrence_nsq (A *ᵥ u) := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ n)‖ ^ 2 = recurrence_nsq u := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  rw [← h1, ← h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

private theorem recurrence_isUnit_transferMat {W : ℕ} (g : ℝ) (z : ℂ)
    (V : Matrix (Fin W) (Fin W) ℂ) : IsUnit (transferMat g z V) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_right_inverse (transferMat_mul_transferInv g z V))

private theorem recurrence_isUnit_transferProd {W : ℕ} (g : ℝ) (z : ℂ)
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (j : ℕ) : IsUnit (transferProd g z V j) := by
  induction j with
  | zero => exact isUnit_one
  | succ j ih => exact (recurrence_isUnit_transferMat g z (V j)).mul ih

/-- The arc inequality of Section 7.2 [sec:uniform-resolvent-seed]:
`‖f_a‖² ≤ (2 K_a²/n) Σ_{j ≤ n} ‖f_{a ± j}‖²` when the interior of the arc avoids `b`. -/
theorem norm_sq_le_arc {W L : ℕ} (hL : 3 ≤ L) {g : ℝ} (hg : 1 ≤ g)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ a, (V a).IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (b : Fin L) (u : Fin W → ℂ) (a : Fin L) (d : Bool) {n : ℕ} (hn : 1 ≤ n)
    (hb : ∀ i, 1 ≤ i → i < n → arcBlock a d i ≠ b) :
    ∑ α, ‖(blockOf (resolventMat (Hdet g V) z) a b *ᵥ u) α‖ ^ 2 ≤
      2 * arcK g z V a d n ^ 2 / n *
        ∑ j ∈ Finset.range (n + 1),
          ∑ α, ‖(blockOf (resolventMat (Hdet g V) z) (arcBlock a d j) b *ᵥ u) α‖ ^ 2 := by
  set f : Fin L → Fin W → ℂ := fun y => blockOf (resolventMat (Hdet g V) z) y b *ᵥ u with hf
  set K := arcK g z V a d n with hK
  set x : ℕ → ℝ := fun j => recurrence_nsq (f (arcBlock a d j)) with hx
  have hx0 : ∀ j, 0 ≤ x j := fun j => recurrence_nsq_nonneg _
  have hpt : ∀ j, j < n → recurrence_nsq (f a) ≤ K ^ 2 * (x (j + 1) + x j) := by
    intro j hj
    have harc := pairVec_resolvent_arc hL hg V hV hz b u a d j fun i h1 h2 => hb i h1 (by omega)
    set P := transferProd g z (fun i => V (arcBlock a d (i + 1))) j with hP
    have hPu : IsUnit P.det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (recurrence_isUnit_transferProd _ _ _ j)
    have hw : pairVec (f (arcBlock a d 1)) (f a) = P⁻¹ *ᵥ pairVec (f (arcBlock a d (j + 1)))
        (f (arcBlock a d j)) := by
      rw [harc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mulVec]
    have hPK : ‖P⁻¹‖ ≤ K := by
      have : ‖P⁻¹‖ = ‖(transferProd g z (fun i => V (arcBlock a d (i + 1)))
          ((⟨j, hj⟩ : Fin n) : ℕ))⁻¹‖ := rfl
      rw [this]
      exact le_ciSup (f := fun j : Fin n => ‖(transferProd g z (fun i => V (arcBlock a d (i + 1)))
        (j : ℕ))⁻¹‖) (Set.finite_range _).bddAbove ⟨j, hj⟩
    calc recurrence_nsq (f a) ≤ recurrence_nsq (f (arcBlock a d 1)) + recurrence_nsq (f a) :=
          le_add_of_nonneg_left (recurrence_nsq_nonneg _)
      _ = recurrence_nsq (pairVec (f (arcBlock a d 1)) (f a)) := (recurrence_nsq_pairVec _ _).symm
      _ ≤ ‖P⁻¹‖ ^ 2 * recurrence_nsq (pairVec (f (arcBlock a d (j + 1))) (f (arcBlock a d j))) := by
          rw [hw]; exact recurrence_nsq_mulVec_le _ _
      _ ≤ K ^ 2 * (x (j + 1) + x j) := by
          rw [recurrence_nsq_pairVec]
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hPK 2) le_rfl
            (add_nonneg (hx0 _) (hx0 _)) (sq_nonneg _)
  have hsum : (n : ℝ) * recurrence_nsq (f a) ≤ K ^ 2 * (2 * ∑ j ∈ Finset.range (n + 1), x j) := by
    have h1 : ∑ j ∈ Finset.range n, recurrence_nsq (f a) ≤
        ∑ j ∈ Finset.range n, K ^ 2 * (x (j + 1) + x j) :=
      Finset.sum_le_sum fun j hj => hpt j (Finset.mem_range.mp hj)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum,
      Finset.sum_add_distrib] at h1
    have h2 : ∑ j ∈ Finset.range n, x (j + 1) ≤ ∑ j ∈ Finset.range (n + 1), x j := by
      rw [Finset.sum_range_succ' x n]
      exact le_add_of_nonneg_right (hx0 0)
    have h3 : ∑ j ∈ Finset.range n, x j ≤ ∑ j ∈ Finset.range (n + 1), x j := by
      rw [Finset.sum_range_succ x n]
      exact le_add_of_nonneg_right (hx0 n)
    refine h1.trans ?_
    nlinarith [sq_nonneg K]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  change recurrence_nsq (f a) ≤ 2 * K ^ 2 / n * ∑ j ∈ Finset.range (n + 1), x j
  rw [div_mul_eq_mul_div, le_div_iff₀ hn']
  linarith

/-- The arc chosen by `arcDir` has no `b` in its interior when `2n < L`. -/
theorem arcBlock_arcDir_ne {L : ℕ} (a b : Fin L) {n : ℕ} (hnL : 2 * n + 1 ≤ L) :
    ∀ i, 1 ≤ i → i < n → arcBlock a (arcDir a b n) i ≠ b := by
  intro i hi1 hin
  by_cases h : ∀ i, 1 ≤ i → i < n → arcBlock a true i ≠ b
  · have hd : arcDir a b n = true := by
      simp only [arcDir, decide_eq_true_eq, Finset.mem_Ico, and_imp]
      exact h
    rw [hd]
    exact h i hi1 hin
  · have h' : ∃ x, 1 ≤ x ∧ x < n ∧ arcBlock a true x = b := by
      by_contra h2
      exact h fun i h1 h3 hh => h2 ⟨i, h1, h3, hh⟩
    have hd : arcDir a b n = false := by
      simp only [arcDir, decide_eq_false_iff_not, Finset.mem_Ico, and_imp]
      exact fun h3 => h fun i h1 h2 => h3 i h1 h2
    rw [hd]
    obtain ⟨i₀, hi₀1, hi₀2, hab⟩ := h'
    intro hcontra
    have h1 : arcBlock a true (i₀ + i) = a := by
      rw [← recurrence_arcBlock_add, hab, ← hcontra, recurrence_arcBlock_cancel]
    exact recurrence_arcBlock_ne_self a true (by omega) (by omega) h1

/-! ### The pathwise bound (7.5) [uvs:eq:pathwise-green-block] -/

private theorem recurrence_dot_conjTranspose {n : Type*} [Fintype n] (M : Matrix n n ℂ)
    (u : n → ℂ) : star u ⬝ᵥ (Mᴴ *ᵥ u) = star (star u ⬝ᵥ (M *ᵥ u)) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star]

/-- Ward's identity `‖G u‖² = Im ⟨u, G u⟩ / Im z` for the resolvent of a Hermitian matrix. -/
private theorem recurrence_ward_vec {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (u : n → ℂ) :
    recurrence_nsq (resolventMat A z *ᵥ u) =
      (star u ⬝ᵥ (resolventMat A z *ᵥ u)).im / z.im := by
  set G := resolventMat A z with hG
  have h : Gᴴ * G = ((2 * z.im * Complex.I)⁻¹ : ℂ) • (G - Gᴴ) := ward_matrix hA hz
  have h1 : star (G *ᵥ u) ⬝ᵥ (G *ᵥ u) = star u ⬝ᵥ ((Gᴴ * G) *ᵥ u) := by
    rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec u Gᴴ G,
      Matrix.dotProduct_mulVec (star u) Gᴴ]
  have h2 : star (G *ᵥ u) ⬝ᵥ (G *ᵥ u) = ((recurrence_nsq (G *ᵥ u) : ℝ) : ℂ) := by
    simp only [recurrence_nsq, dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  have h3 : star u ⬝ᵥ ((Gᴴ * G) *ᵥ u) = ((2 * z.im * Complex.I)⁻¹ : ℂ) *
      (star u ⬝ᵥ (G *ᵥ u) - star (star u ⬝ᵥ (G *ᵥ u))) := by
    rw [h, Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul, dotProduct_sub,
      recurrence_dot_conjTranspose, smul_eq_mul]
  have h4 : ∀ w : ℂ, w - star w = ((2 * w.im : ℝ) : ℂ) * Complex.I := fun w => by
    apply Complex.ext <;> simp [two_mul]
  apply Complex.ofReal_injective
  rw [← h2, h1, h3, h4]
  have hη' : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz
  push_cast
  field_simp

/-- Cauchy–Schwarz for the pairing `⟨x, y⟩ = x* y`. -/
private theorem recurrence_cauchy {n : Type*} [Fintype n] (x y : n → ℂ) :
    ‖star x ⬝ᵥ y‖ ^ 2 ≤ recurrence_nsq x * recurrence_nsq y := by
  have h1 : ‖star x ⬝ᵥ y‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp
  calc ‖star x ⬝ᵥ y‖ ^ 2 ≤ (∑ i, ‖x i‖ * ‖y i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

private theorem recurrence_embed_pair {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (b : Fin L) (u : Fin W → ℂ) :
    star (recurrence_embed b u) ⬝ᵥ (G *ᵥ recurrence_embed b u) =
      star u ⬝ᵥ (blockOf G b b *ᵥ u) := by
  rw [recurrence_blockOf_mulVec]
  simp only [dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · simp [recurrence_embed]
  · intro c _ hc
    simp [recurrence_embed, hc]
  · simp

private theorem recurrence_nsq_prod {W L : ℕ} (F : Fin L × Fin W → ℂ) :
    recurrence_nsq F = ∑ c, recurrence_nsq (fun γ => F (c, γ)) := by
  simp [recurrence_nsq, Fintype.sum_prod_type]

/-- A matrix whose action on vectors is bounded by `c` in the sum-of-squares norm has operator
norm at most `c`. -/
private theorem recurrence_opNorm_le {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ u : n → ℂ, recurrence_nsq (A *ᵥ u) ≤ c ^ 2 * recurrence_nsq u) :
    ‖A‖ ≤ c := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have h1 : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ^ 2 = recurrence_nsq (A *ᵥ x.ofLp) := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h2 : ‖x‖ ^ 2 = recurrence_nsq x.ofLp := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h3 := h x.ofLp
  rw [← h1, ← h2] at h3
  have h4 : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    rw [mul_pow]; exact h3
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h4

private theorem recurrence_arcK_nonneg {W L : ℕ} (g : ℝ) (z : ℂ)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (a : Fin L) (d : Bool) (n : ℕ) :
    0 ≤ arcK g z V a d n :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- (7.5) [uvs:eq:pathwise-green-block]: `‖G_{ab}(E + iη)‖ ≤ 2 K_a K_b / (n η)`. -/
theorem norm_blockOf_resolvent_le {W L : ℕ} (hL : 3 ≤ L) {g : ℝ} (hg : 1 ≤ g)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ a, (V a).IsHermitian) (E : ℝ) {η : ℝ}
    (hη : 0 < η) {n : ℕ} (hn : 1 ≤ n) (hnL : 2 * n + 1 ≤ L) (a b : Fin L) :
    ‖blockOf (resolventMat (Hdet g V) (↑E + ↑η * Complex.I)) a b‖ ≤
      2 * arcK g (↑E + ↑η * Complex.I) V a (arcDir a b n) n *
        arcK g (↑E + ↑η * Complex.I) V b true n / (n * η) := by
  set z : ℂ := ↑E + ↑η * Complex.I with hzdef
  have hzim : z.im = η := by simp [hzdef]
  have hz : z.im ≠ 0 := by rw [hzim]; exact hη.ne'
  set G := resolventMat (Hdet g V) z with hG
  set Ka := arcK g z V a (arcDir a b n) n with hKa
  set Kb := arcK g z V b true n with hKb
  have hKa0 : 0 ≤ Ka := recurrence_arcK_nonneg _ _ _ _ _ _
  have hKb0 : 0 ≤ Kb := recurrence_arcK_nonneg _ _ _ _ _ _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine recurrence_opNorm_le _ (by positivity) fun u => ?_
  set f : Fin L → Fin W → ℂ := fun y => blockOf G y b *ᵥ u with hf
  set S : ℝ := ∑ c, recurrence_nsq (f c) with hS
  set U : ℝ := recurrence_nsq u with hU
  have hf0 : ∀ c, 0 ≤ recurrence_nsq (f c) := fun c => recurrence_nsq_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun c _ => hf0 c
  have hU0 : 0 ≤ U := recurrence_nsq_nonneg _
  -- Ward's identity
  have hward : η * S = (star u ⬝ᵥ f b).im := by
    have h := recurrence_ward_vec (Hdet_isHermitian g hV) hz (recurrence_embed b u)
    rw [recurrence_embed_pair, recurrence_nsq_prod, hzim] at h
    have h' : S = (star u ⬝ᵥ (blockOf G b b *ᵥ u)).im / η := by
      rw [hS]
      convert h using 2 with c
      exact (congrArg recurrence_nsq (recurrence_blockOf_mulVec G b u c))
    rw [h']
    field_simp
    rfl
  -- Cauchy–Schwarz
  have hC : (η * S) ^ 2 ≤ U * recurrence_nsq (f b) := by
    rw [hward]
    calc ((star u ⬝ᵥ f b).im) ^ 2 = |(star u ⬝ᵥ f b).im| ^ 2 := (sq_abs _).symm
      _ ≤ ‖star u ⬝ᵥ f b‖ ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2
      _ ≤ U * recurrence_nsq (f b) := recurrence_cauchy u (f b)
  -- the arc inequality at `b` and at `a`
  have hnL' : n + 1 ≤ L := by omega
  have hA : recurrence_nsq (f b) ≤ 2 * Kb ^ 2 / n * S := by
    have h := norm_sq_le_arc hL hg V hV hz b u b true hn fun i h1 h2 =>
      recurrence_arcBlock_ne_self b true (by omega) (by omega)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact recurrence_sum_arc_le b true hnL' (fun c => recurrence_nsq (f c)) hf0
  have hB : recurrence_nsq (f a) ≤ 2 * Ka ^ 2 / n * S := by
    have h := norm_sq_le_arc hL hg V hV hz b u a (arcDir a b n) hn
      (arcBlock_arcDir_ne a b hnL)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact recurrence_sum_arc_le a (arcDir a b n) hnL' (fun c => recurrence_nsq (f c)) hf0
  -- closing the constant
  have hη2 : 0 < η ^ 2 := by positivity
  have hS1 : η ^ 2 * S ≤ U * (2 * Kb ^ 2 / n) := by
    by_cases hS00 : S = 0
    · rw [hS00, mul_zero]; positivity
    · have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS00)
      refine le_of_mul_le_mul_right ?_ hSpos
      calc η ^ 2 * S * S = (η * S) ^ 2 := by ring
        _ ≤ U * recurrence_nsq (f b) := hC
        _ ≤ U * (2 * Kb ^ 2 / n * S) := mul_le_mul_of_nonneg_left hA hU0
        _ = U * (2 * Kb ^ 2 / n) * S := by ring
  have hS2 : S ≤ U * (2 * Kb ^ 2 / n) / η ^ 2 := by
    rw [le_div_iff₀ hη2]; linarith
  have hfa : blockOf G a b *ᵥ u = f a := rfl
  rw [hfa]
  calc recurrence_nsq (f a) ≤ 2 * Ka ^ 2 / n * S := hB
    _ ≤ 2 * Ka ^ 2 / n * (U * (2 * Kb ^ 2 / n) / η ^ 2) :=
        mul_le_mul_of_nonneg_left hS2 (by positivity)
    _ = (2 * Ka * Kb / (n * η)) ^ 2 * U := by
        field_simp

end LSBA
