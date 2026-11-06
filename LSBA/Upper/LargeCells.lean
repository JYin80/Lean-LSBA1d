import LSBA.Spectral.EigMass
import LSBA.Transfer.Weight
import LSBA.Gauss.BlockWindow
import LSBA.Gauss.LineDecomp

/-!
# Cells of consecutive blocks

A cell `A = {a, a+1, …, a+n−1}` of `ℤ_L` with its coordinates, and the weight `K_A(E)` of
Appendix E.1 [app:fr-concentration-proof] built from the blocks of the cell in their natural order.
The
scalar direction of a cell shifts the model (1.3) [eq:model] by `α t P_A`, `α = (gW√n)^{-1}`; and
every eigenvector of the block operator has positive mass on a cell of at least two blocks (proof of
the Claim (E.6) [uva:eq:average]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Block `a + j` of `ℤ_L`. -/
def cellBlock {L : ℕ} (a : Fin L) (j : ℕ) : Fin L :=
  ⟨(a.val + j) % L, Nat.mod_lt _ a.pos⟩

/-- The cell `a, a+1, …, a+n−1` as a window `Fin n → Fin L`. -/
def cellWindow {L : ℕ} (a : Fin L) (n : ℕ) : Fin n → Fin L := fun j => cellBlock a j

/-- The blocks of the cell `a, a+1, …, a+n−1`. -/
def cellSet {L : ℕ} (a : Fin L) (n : ℕ) : Finset (Fin L) := (Finset.range n).image (cellBlock a)

/-- The coordinates `(b, α)` with `b` in the cell `a, …, a+n−1`. -/
def cellCoords {W L : ℕ} (a : Fin L) (n : ℕ) : Finset (Fin L × Fin W) :=
  univ.filter fun p => p.1 ∈ cellSet a n

/-- The weight `K_A(E)` of Appendix E.1 [app:fr-concentration-proof] for the cell `A = a, …, a+n−1`
of
the sample `ω`. -/
def cellWeight (g E : ℝ) {W L : ℕ} (ω : Ω W L) (a : Fin L) (n : ℕ) : ℝ :=
  transferWeight g E (fun j => gueBlock W L ω (cellBlock a j)) n

/-- A cell of at most `L` blocks is an injective window. -/
theorem cellWindow_injective {L : ℕ} (a : Fin L) {n : ℕ} (hn : n ≤ L) :
    Function.Injective (cellWindow a n) := by
  intro i j hij
  have h : (a.val + i.val) % L = (a.val + j.val) % L := by
    have := congrArg Fin.val hij
    simpa [cellWindow, cellBlock] using this
  have h2 : i.val % L = j.val % L :=
    Nat.ModEq.add_left_cancel' a.val (show (a.val + i.val) ≡ (a.val + j.val) [MOD L] from h)
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt hn), Nat.mod_eq_of_lt (lt_of_lt_of_le j.isLt hn)]
    at h2
  exact Fin.ext h2

/-- Moving the cell blocks of `windowJoin` along the scalar direction by `t` adds
`t/(gW√n) P_A` to the model (1.3) [eq:model], for `g ≥ 1` (proof of the Claim
(E.6) [uva:eq:average]). -/
theorem Hmat_windowJoin_line {g : ℝ} (hg : 1 ≤ g) {W L n : ℕ} (hn : 1 ≤ n) (hnL : n ≤ L)
    (a : Fin L) (v : Ω W n)
    (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range (cellWindow a n)} → ℝ) (t : ℝ) :
    Hmat g W L (windowJoin (cellWindow a n) (v + t • scalarDir W n univ) e) =
      Hmat g W L (windowJoin (cellWindow a n) v e) +
        ((t / (g * W * Real.sqrt n) : ℝ) : ℂ) • coordProj (cellCoords a n) := by
  have hinj := cellWindow_injective a hnL
  have hrange : Set.range (cellWindow a n) = ↑(cellSet a n) := by
    ext b
    simp only [Set.mem_range, cellWindow, cellSet, Finset.coe_image, Finset.coe_range,
      Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j.val, j.isLt, hj⟩
    · rintro ⟨j, hj, hjb⟩
      exact ⟨⟨j, hj⟩, hjb⟩
  have hg0 : 0 < g := lt_of_lt_of_le one_pos hg
  have hmax : max 1 g = g := max_eq_right hg
  have hblock : ∀ b : Fin L,
      gueBlock W L (windowJoin (cellWindow a n) (v + t • scalarDir W n univ) e) b =
        gueBlock W L (windowJoin (cellWindow a n) v e) b +
          if b ∈ cellSet a n then
            ((t / ((W : ℝ) * Real.sqrt n) : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) else 0 := by
    intro b
    by_cases hb : b ∈ Set.range (cellWindow a n)
    · obtain ⟨j, rfl⟩ := hb
      have hmem : cellWindow a n j ∈ cellSet a n := by
        rw [← Finset.mem_coe, ← hrange]; exact ⟨j, rfl⟩
      rw [gueBlock_windowJoin_apply hinj, gueBlock_windowJoin_apply hinj,
        gueBlock_add_smul_scalarDir W n univ v t j]
      simp only [hmem, Finset.mem_univ, ↓reduceIte, Finset.card_univ, Fintype.card_fin]
    · have hmem : b ∉ cellSet a n := by
        intro h; exact hb (by rw [hrange]; exact h)
      simp only [hmem, ↓reduceIte, add_zero]
      exact gueBlock_windowJoin_of_not_mem _ _ _ _ hb
  unfold Hmat Hdet
  have hfun : (gueBlock W L (windowJoin (cellWindow a n) (v + t • scalarDir W n univ) e)) =
      fun b => gueBlock W L (windowJoin (cellWindow a n) v e) b +
        if b ∈ cellSet a n then
          ((t / ((W : ℝ) * Real.sqrt n) : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) else 0 :=
    funext hblock
  rw [hfun, hmax]
  have hcc : ∀ (b : Fin L) (α : Fin W), (b, α) ∈ cellCoords (W := W) a n ↔ b ∈ cellSet a n := by
    intro b α; simp [cellCoords]
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

/-- An eigenvector of `(g A_L ⊗ I + diag V)/max{1,g}`, `g > 0`, has positive mass on every cell of
at least two blocks (proof of the Claim (E.6) [uva:eq:average]). -/
theorem cell_mass_pos {g : ℝ} (hg : 0 < g) {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    {E : ℝ} {ψ : Fin L × Fin W → ℂ} (hψ : Hdet g V *ᵥ ψ = (E : ℂ) • ψ) (hψ0 : ψ ≠ 0) (a : Fin L)
    {n : ℕ} (hn : 2 ≤ n) :
    0 < ∑ p ∈ cellCoords a n, ‖ψ p‖ ^ 2 := by
  by_contra hcon
  have hnn : 0 ≤ ∑ p ∈ cellCoords a n, ‖ψ p‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  have hz : ∑ p ∈ cellCoords a n, ‖ψ p‖ ^ 2 = 0 := le_antisymm (not_lt.mp hcon) hnn
  rw [Finset.sum_eq_zero_iff_of_nonneg fun p _ => sq_nonneg _] at hz
  have hzero : ∀ p ∈ cellCoords (W := W) a n, ψ p = 0 := by
    intro p hp
    have := hz p hp
    exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this)
  -- the vanishing set of blocks propagates along the cycle
  have hL : 0 < L := a.pos
  have hval : ∀ k : ℕ, (cellBlock a k).val = (a.val + k) % L := fun k => rfl
  have hstep : ∀ k : ℕ, (∀ α, ψ (cellBlock a k, α) = 0) → (∀ α, ψ (cellBlock a (k + 1), α) = 0) →
      ∀ α, ψ (cellBlock a (k + 2), α) = 0 := by
    intro k h0 h1 α
    have hrow := congrFun hψ (cellBlock a (k + 1), α)
    have e1 : ∀ q : Fin L, (if q.val = ((cellBlock a (k + 1)).val + 1) % L then (1 : ℂ) else 0) =
        if q = cellBlock a (k + 2) then 1 else 0 := by
      intro q
      have : ((cellBlock a (k + 1)).val + 1) % L = (cellBlock a (k + 2)).val := by
        rw [hval, hval, Nat.mod_add_mod]
        congr 1
      simp only [this, Fin.ext_iff]
    have e2 : ∀ q : Fin L, (if (cellBlock a (k + 1)).val = (q.val + 1) % L then (1 : ℂ) else 0) =
        if q = cellBlock a k then 1 else 0 := by
      intro q
      by_cases hq : q = cellBlock a k
      · subst hq
        have : (cellBlock a (k + 1)).val = ((cellBlock a k).val + 1) % L := by
          rw [hval, hval, Nat.mod_add_mod]
          congr 1
        simp [this]
      · have : ¬ ((cellBlock a (k + 1)).val = (q.val + 1) % L) := by
          intro h
          apply hq
          rw [hval] at h
          have h' : (q.val + 1) ≡ (a.val + k + 1) [MOD L] := by
            unfold Nat.ModEq
            rw [← h, Nat.add_assoc]
          have h'' : q.val ≡ a.val + k [MOD L] := Nat.ModEq.add_right_cancel' 1 h'
          apply Fin.ext
          rw [hval]
          have := h''
          unfold Nat.ModEq at this
          rwa [Nat.mod_eq_of_lt q.isLt] at this
        simp [hq, this]
    have key : (Hdet g V *ᵥ ψ) (cellBlock a (k + 1), α) =
        ((max 1 g : ℝ)⁻¹ : ℂ) * ((g : ℂ) * (ψ (cellBlock a (k + 2), α) + ψ (cellBlock a k, α)) +
          ∑ β, V (cellBlock a (k + 1)) α β * ψ (cellBlock a (k + 1), β)) := by
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
    have hmax0 : ((max 1 g : ℝ)⁻¹ : ℂ) ≠ 0 := by
      have : (0 : ℝ) < (max 1 g)⁻¹ := inv_pos.mpr (lt_max_of_lt_left one_pos)
      exact_mod_cast this.ne'
    have hg0 : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
    rw [key] at hrow
    simp only [Pi.smul_apply, h0, h1, smul_eq_mul, mul_zero, add_zero,
      Finset.sum_const_zero] at hrow
    rcases mul_eq_zero.mp hrow with h | h
    · exact absurd h hmax0
    · exact (mul_eq_zero.mp h).resolve_left hg0
  have hbase : ∀ k, k < n → ∀ α, ψ (cellBlock a k, α) = 0 := by
    intro k hk α
    apply hzero
    simp only [cellCoords, Finset.mem_filter, Finset.mem_univ, true_and, cellSet,
      Finset.mem_image, Finset.mem_range]
    exact ⟨k, hk, rfl⟩
  have hall : ∀ k, (∀ α, ψ (cellBlock a k, α) = 0) ∧ (∀ α, ψ (cellBlock a (k + 1), α) = 0) := by
    intro k
    induction k with
    | zero => exact ⟨hbase 0 (by omega), hbase 1 (by omega)⟩
    | succ k ih => exact ⟨ih.2, hstep k ih.1 ih.2⟩
  apply hψ0
  funext ⟨b, α⟩
  have hex : ∃ j : ℕ, cellBlock a j = b := by
    by_cases hab : a.val ≤ b.val
    · refine ⟨b.val - a.val, Fin.ext ?_⟩
      rw [hval, show a.val + (b.val - a.val) = b.val by omega]
      exact Nat.mod_eq_of_lt b.isLt
    · refine ⟨b.val + L - a.val, Fin.ext ?_⟩
      rw [hval, show a.val + (b.val + L - a.val) = b.val + L by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt b.isLt
  obtain ⟨j, rfl⟩ := hex
  exact (hall j).1 α

end LSBA
