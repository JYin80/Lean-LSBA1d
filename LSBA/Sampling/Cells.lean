import Mathlib

/-!
# Cells and anchors

The cells of Definition 5.7 [def:cells-anchors]: consecutive intervals of length
`n = max{1, ⌊g²W^{-B}⌋}` on the cycle, their first and previous points and the anchors; the cell
length bounds and the count `⌈L/n⌉ ≤ L/n + 1 ≤ 3W^{B+C}` used by Lemma 5.8
[uvc:thm:ordinary-sampling] and Lemma 7.7 [uvc:lem:cells].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The cell length `n = max{1, ⌊g² W^{-B}⌋}` of Definition 5.7 [def:cells-anchors]. -/
def cellLen (g : ℝ) (W : ℕ) (B : ℝ) : ℕ := max 1 ⌊g ^ 2 * (W : ℝ) ^ (-B)⌋₊

/-- The first block of the cell of `a` in the cell partition of Definition 5.7 [def:cells-anchors]
into the consecutive intervals `[jn, (j + 1)n) ∩ [0, L)`. -/
def cellStart (n : ℕ) {L : ℕ} (a : Fin L) : Fin L :=
  ⟨a.val / n * n, lt_of_le_of_lt (Nat.div_mul_le_self a.val n) a.isLt⟩

/-- The predecessor (modulo `L`) of the first block of the cell of `a`. -/
def cellPrev (n : ℕ) {L : ℕ} (a : Fin L) : Fin L := (finRotate L).symm (cellStart n a)

/-- The anchor blocks of Proposition 7.4 [uvc:prop:green]: first blocks of cells and their
predecessors. -/
def IsAnchor (n : ℕ) {L : ℕ} (α : Fin L) : Prop := α.val % n = 0 ∨ (finRotate L α).val % n = 0

/-- `g² W^{-B} ≥ 1` when `W ≥ 1` and `W^B ≤ g²`. -/
private theorem cells_one_le_ratio (g B : ℝ) (W : ℕ) (hW : 1 ≤ W) (hg : (W : ℝ) ^ B ≤ g ^ 2) :
    1 ≤ g ^ 2 * (W : ℝ) ^ (-B) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hp : (0 : ℝ) < (W : ℝ) ^ B := Real.rpow_pos_of_pos hW0 B
  rw [Real.rpow_neg hW0.le]
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  linarith

/-- Definition 5.7 [def:cells-anchors]: if `g² ≥ W^B` then `g² W^{-B}/2 ≤ n ≤ g² W^{-B}`. -/
theorem cellLen_bounds (g B : ℝ) (W : ℕ) (hW : 1 ≤ W) (hg : (W : ℝ) ^ B ≤ g ^ 2) :
    g ^ 2 * (W : ℝ) ^ (-B) / 2 ≤ cellLen g W B ∧ (cellLen g W B : ℝ) ≤ g ^ 2 * (W : ℝ) ^ (-B) := by
  have hx := cells_one_le_ratio g B W hW hg
  set x : ℝ := g ^ 2 * (W : ℝ) ^ (-B) with hxdef
  have h1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hn : cellLen g W B = ⌊x⌋₊ := max_eq_right h1
  rw [hn]
  have h1' : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h1
  refine ⟨?_, Nat.floor_le (by linarith)⟩
  have := Nat.lt_floor_add_one x
  linarith

/-- The number of cells is at most `L/n + 1`. -/
theorem card_cellStarts_le (n L : ℕ) (hn : 1 ≤ n) :
    ((univ.filter fun b : Fin L => b.val % n = 0).card : ℝ) ≤ (L : ℝ) / n + 1 := by
  have hcard : (univ.filter fun b : Fin L => b.val % n = 0).card ≤ L / n + 1 := by
    have := Finset.card_le_card_of_injOn (s := univ.filter fun b : Fin L => b.val % n = 0)
      (t := range (L / n + 1)) (fun b => b.val / n) ?_ ?_
    · simpa using this
    · intro b _
      simp only [coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right b.isLt.le)
    · intro b hb c hc hbc
      rw [Finset.mem_coe, Finset.mem_filter] at hb hc
      replace hb := hb.2
      replace hc := hc.2
      apply Fin.ext
      have e1 := Nat.div_add_mod b.val n
      have e2 := Nat.div_add_mod c.val n
      simp only at hbc
      rw [hb] at e1
      rw [hc] at e2
      rw [hbc] at e1
      omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  calc ((univ.filter fun b : Fin L => b.val % n = 0).card : ℝ) ≤ ((L / n + 1 : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = ((L / n : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (L : ℝ) / n + 1 := by
        gcongr
        exact Nat.cast_div_le

/-- With `g² ≥ W^B` and `L ≤ g² W^C` there are at most `3W^{B+C}` cells (the count of the proof
of Lemma 7.7 [uvc:lem:cells]) and at most `6W^{B+C}` anchors. -/
theorem card_cells_le_pow (g B C : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hg : (W : ℝ) ^ B ≤ g ^ 2) (hL : (L : ℝ) ≤ g ^ 2 * (W : ℝ) ^ C) :
    ((univ.filter fun b : Fin L => b.val % cellLen g W B = 0).card : ℝ) ≤ 3 * (W : ℝ) ^ (B + C) ∧
      ((univ.filter fun α : Fin L => IsAnchor (cellLen g W B) α).card : ℝ) ≤
        6 * (W : ℝ) ^ (B + C) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hWB : (0 : ℝ) < (W : ℝ) ^ B := Real.rpow_pos_of_pos hW0 B
  have hg2 : 0 < g ^ 2 := lt_of_lt_of_le hWB hg
  obtain ⟨hlow, -⟩ := cellLen_bounds g B W hW hg
  have hx := cells_one_le_ratio g B W hW hg
  have hn1 : 1 ≤ cellLen g W B := le_max_left _ _
  have hnpos : (0 : ℝ) < cellLen g W B := by exact_mod_cast hn1
  have hpow : (1 : ℝ) ≤ (W : ℝ) ^ (B + C) :=
    Real.one_le_rpow (by exact_mod_cast hW) (by linarith)
  have hWadd : (W : ℝ) ^ (B + C) = (W : ℝ) ^ B * (W : ℝ) ^ C := Real.rpow_add hW0 B C
  have hxinv : g ^ 2 * (W : ℝ) ^ (-B) = g ^ 2 / (W : ℝ) ^ B := by
    rw [Real.rpow_neg hW0.le, div_eq_mul_inv]
  have hcells : ((univ.filter fun b : Fin L => b.val % cellLen g W B = 0).card : ℝ) ≤
      3 * (W : ℝ) ^ (B + C) := by
    refine (card_cellStarts_le _ L hn1).trans ?_
    have hLn : (L : ℝ) / cellLen g W B ≤ 2 * (W : ℝ) ^ (B + C) := by
      rw [div_le_iff₀ hnpos]
      have h2 : (L : ℝ) ≤ g ^ 2 * (W : ℝ) ^ C := hL
      have h3 : g ^ 2 / (W : ℝ) ^ B / 2 ≤ (cellLen g W B : ℝ) := by rw [← hxinv]; exact hlow
      have h4 : (L : ℝ) ≤ 2 * (W : ℝ) ^ (B + C) * (g ^ 2 / (W : ℝ) ^ B / 2) := by
        rw [hWadd]
        have : 2 * ((W : ℝ) ^ B * (W : ℝ) ^ C) * (g ^ 2 / (W : ℝ) ^ B / 2) =
            g ^ 2 * (W : ℝ) ^ C := by
          field_simp
        rw [this]; exact h2
      calc (L : ℝ) ≤ 2 * (W : ℝ) ^ (B + C) * (g ^ 2 / (W : ℝ) ^ B / 2) := h4
        _ ≤ 2 * (W : ℝ) ^ (B + C) * (cellLen g W B : ℝ) := by gcongr
    linarith
  refine ⟨hcells, ?_⟩
  have hsub : (univ.filter fun α : Fin L => IsAnchor (cellLen g W B) α) ⊆
      (univ.filter fun b : Fin L => b.val % cellLen g W B = 0) ∪
        (univ.filter fun b : Fin L => b.val % cellLen g W B = 0).image (finRotate L).symm := by
    intro α hα
    rw [Finset.mem_filter] at hα
    obtain ⟨-, h⟩ := hα
    rw [Finset.mem_union]
    rcases h with h | h
    · left; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
    · right
      rw [Finset.mem_image]
      exact ⟨finRotate L α, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩,
        Equiv.symm_apply_apply _ _⟩
  have hcard : (univ.filter fun α : Fin L => IsAnchor (cellLen g W B) α).card ≤
      2 * (univ.filter fun b : Fin L => b.val % cellLen g W B = 0).card := by
    calc _ ≤ _ := card_le_card hsub
      _ ≤ (univ.filter fun b : Fin L => b.val % cellLen g W B = 0).card +
          ((univ.filter fun b : Fin L => b.val % cellLen g W B = 0).image
            (finRotate L).symm).card := card_union_le _ _
      _ ≤ _ := by
        have := card_image_le (s := univ.filter fun b : Fin L => b.val % cellLen g W B = 0)
          (f := (finRotate L).symm)
        omega
  have hcardR : ((univ.filter fun α : Fin L => IsAnchor (cellLen g W B) α).card : ℝ) ≤
      2 * ((univ.filter fun b : Fin L => b.val % cellLen g W B = 0).card : ℝ) := by
    exact_mod_cast hcard
  linarith

end LSBA
