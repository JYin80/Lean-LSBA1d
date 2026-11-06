import LSBA.Primitive.Ward
import LSBA.Primitive.Symm
import LSBA.Kernel.Bounded
import LSBA.Kernel.Large

/-!
# Primitive loops: stable molecules

The stable molecules of Appendix B.3 [app:bounded-primitives]: translation and reflection, the
bound (B.2) [ba:eq:moment] at every anchor, the cancellation (B.3) [ba:eq:cancel] with the
normalized full
transform, and at large coupling the core profile and the mass bound of Appendix B.5
[app:uniform-profile].
-/

open MeasureTheory Real Filter Topology Complex Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ## The two polygons cut off by a diagonal

For a diagonal `(i, j)` of the `k`-gon, the vertices `0, …, i, j, …, k-1` form the polygon of
Cut_L and the vertices `i, …, j` the polygon of Cut_R of (5.6) [fo:eq:cuts]. -/

section Polygon

variable {k : ℕ}

/-- The cyclic offset without `mod`. -/
lemma mol_polyOff_eq {n : ℕ} (v w : Fin n) :
    polyOff v w = if v.val ≤ w.val then w.val - v.val else w.val + n - v.val := by
  have := v.isLt
  have := w.isLt
  unfold polyOff
  split_ifs with h
  · rw [show w.val + n - v.val = (w.val - v.val) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma mol_polyOff_cases {n : ℕ} (v w : Fin n) :
    (v.val ≤ w.val ∧ polyOff v w = w.val - v.val) ∨
      (w.val < v.val ∧ polyOff v w = w.val + n - v.val) := by
  rw [mol_polyOff_eq]
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

/-- The value of the cyclic successor. -/
lemma mol_finRotate_val {n : ℕ} (v : Fin n) :
    (finRotate n v).val = if v.val + 1 = n then 0 else v.val + 1 := by
  rcases n with _ | n
  · exact v.elim0
  · rw [coe_finRotate]
    by_cases h : v = Fin.last n
    · subst h; simp
    · have h' : v.val ≠ n := fun e => h (Fin.ext e)
      simp [h, h']

/-- The vertex map of the polygon of `Cut_{L,i,j}`. -/
private def mol_vL (i j : Fin k) (p : Fin (k + i - j + 1)) : Fin k :=
  ⟨if p.val ≤ i.val then p.val else p.val + j.val - i.val - 1, by
    have := p.isLt; have := i.isLt; have := j.isLt; split_ifs <;> omega⟩

/-- The vertex map of the polygon of `Cut_{R,i,j}`. -/
private def mol_vR (i j : Fin k) (q : Fin (j - i + 1)) : Fin k :=
  ⟨i.val + q.val, by have := q.isLt; have := i.isLt; have := j.isLt; omega⟩

private lemma mol_vL_val (i j : Fin k) (p : Fin (k + i - j + 1)) :
    (mol_vL i j p).val = if p.val ≤ i.val then p.val else p.val + j.val - i.val - 1 := rfl

private lemma mol_vR_val (i j : Fin k) (q : Fin (j - i + 1)) :
    (mol_vR i j q).val = i.val + q.val := rfl

private lemma mol_vL_cases (i j : Fin k) (p : Fin (k + i - j + 1)) :
    (p.val ≤ i.val ∧ (mol_vL i j p).val = p.val) ∨
      (i.val < p.val ∧ (mol_vL i j p).val = p.val + j.val - i.val - 1) := by
  rw [mol_vL_val]
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

private lemma mol_vL_strictMono {i j : Fin k} (hij : i.val < j.val) :
    StrictMono (mol_vL i j) := by
  intro p p' h
  rw [Fin.lt_def, mol_vL_val, mol_vL_val]
  rw [Fin.lt_def] at h
  split_ifs <;> omega

private lemma mol_vR_strictMono (i j : Fin k) : StrictMono (mol_vR i j) := by
  intro q q' h
  rw [Fin.lt_def, mol_vR_val, mol_vR_val]
  rw [Fin.lt_def] at h
  omega

/-- The inverse of `mol_vL` on its range. -/
private def mol_uL (i j : Fin k) (v : Fin k) : Fin (k + i - j + 1) :=
  ⟨if v.val ≤ i.val then v.val else v.val + i.val + 1 - j.val, by
    have := v.isLt; have := i.isLt; have := j.isLt; split_ifs <;> omega⟩

/-- The inverse of `mol_vR` on its range. -/
private def mol_uR (i j : Fin k) (v : Fin k) : Fin (j - i + 1) :=
  ⟨if v.val ≤ j.val then v.val - i.val else 0, by split_ifs <;> omega⟩

private lemma mol_uL_val (i j v : Fin k) :
    (mol_uL i j v).val = if v.val ≤ i.val then v.val else v.val + i.val + 1 - j.val := rfl

private lemma mol_uR_val (i j v : Fin k) :
    (mol_uR i j v).val = if v.val ≤ j.val then v.val - i.val else 0 := rfl

private lemma mol_vL_uL {i j : Fin k} {v : Fin k}
    (hv : v.val ≤ i.val ∨ j.val ≤ v.val) : mol_vL i j (mol_uL i j v) = v := by
  apply Fin.ext
  rw [mol_vL_val, mol_uL_val]
  split_ifs <;> omega

private lemma mol_vR_uR {i j : Fin k} {v : Fin k} (hv : i.val ≤ v.val ∧ v.val ≤ j.val) :
    mol_vR i j (mol_uR i j v) = v := by
  apply Fin.ext
  rw [mol_vR_val, mol_uR_val]
  split_ifs <;> omega

private lemma mol_uL_vL {i j : Fin k} (hij : i.val < j.val) (p : Fin (k + i - j + 1)) :
    mol_uL i j (mol_vL i j p) = p := by
  have := p.isLt; have := j.isLt
  apply Fin.ext
  rw [mol_uL_val, mol_vL_val]
  split_ifs <;> omega

private lemma mol_uR_vR (i j : Fin k) (q : Fin (j - i + 1)) :
    mol_uR i j (mol_vR i j q) = q := by
  have := q.isLt; have := j.isLt
  apply Fin.ext
  rw [mol_uR_val, mol_vR_val]
  split_ifs <;> omega

private lemma mol_vL_inj {i j : Fin k} (hij : i.val < j.val) {p p' : Fin (k + i - j + 1)}
    (h : mol_vL i j p = mol_vL i j p') : p = p' :=
  (mol_vL_strictMono hij).injective h

private lemma mol_vR_inj {i j : Fin k} {q q' : Fin (j - i + 1)}
    (h : mol_vR i j q = mol_vR i j q') : q = q' :=
  (mol_vR_strictMono i j).injective h

/-- The cyclic order seen from a vertex is preserved by `mol_vL`. -/
private lemma mol_off_vL {i j : Fin k} (hij : i.val < j.val) (v w w' : Fin (k + i - j + 1)) :
    polyOff v w < polyOff v w' ↔
      polyOff (mol_vL i j v) (mol_vL i j w) < polyOff (mol_vL i j v) (mol_vL i j w') := by
  have := v.isLt; have := w.isLt; have := w'.isLt; have := j.isLt
  simp only [mol_polyOff_eq, mol_vL_val]
  split_ifs <;> omega

/-- The cyclic order seen from a vertex is preserved by `mol_vR`. -/
private lemma mol_off_vR (i j : Fin k) (v w w' : Fin (j - i + 1)) :
    polyOff v w < polyOff v w' ↔
      polyOff (mol_vR i j v) (mol_vR i j w) < polyOff (mol_vR i j v) (mol_vR i j w') := by
  have := v.isLt; have := w.isLt; have := w'.isLt; have := j.isLt
  simp only [mol_polyOff_eq, mol_vR_val, Nat.add_le_add_iff_left]
  split_ifs <;> omega

private lemma mol_cutLSgn_eq (σ : Fin k → Bool) (i j : Fin k) (p : Fin (k + i - j + 1)) :
    cutLSgn σ i j p = σ (mol_vL i j p) := by
  unfold cutLSgn
  split_ifs with h1 <;> (congr 1; apply Fin.ext; simp [mol_vL_val, h1])

private lemma mol_cutRSgn_eq (σ : Fin k → Bool) (i j : Fin k) (q : Fin (j - i + 1)) :
    cutRSgn σ i j q = σ (mol_vR i j q) := rfl

end Polygon

/-! ## Splitting a dissection along a diagonal -/

section Split

variable {k : ℕ}

private lemma mol_mem_polyDiags {n : ℕ} (e : Fin n × Fin n) :
    e ∈ polyDiags n ↔ e.1.val + 2 ≤ e.2.val ∧ ¬(e.1.val = 0 ∧ e.2.val + 1 = n) := by
  simp [polyDiags, IsPolyDiag]

private lemma mol_mem_dissections {n : ℕ} (F : Finset (Fin n × Fin n)) :
    F ∈ dissections n ↔ F ⊆ polyDiags n ∧ ∀ d ∈ F, ∀ e ∈ F, ¬DiagCross d e := by
  simp [dissections]

private lemma mol_diagCross_iff {n : ℕ} (d e : Fin n × Fin n) :
    DiagCross d e ↔ (d.1.val < e.1.val ∧ e.1.val < d.2.val ∧ d.2.val < e.2.val) ∨
      (e.1.val < d.1.val ∧ d.1.val < e.2.val ∧ e.2.val < d.2.val) := by
  unfold DiagCross
  simp only [Fin.lt_def]

private lemma mol_prod_ne {n : ℕ} {e d : Fin n × Fin n} (h : e ≠ d) :
    ¬(e.1.val = d.1.val ∧ e.2.val = d.2.val) :=
  fun h' => h (Prod.ext (Fin.ext h'.1) (Fin.ext h'.2))

/-- The dissection of the polygon of `Cut_{L,i,j}` induced by `F`. -/
private def mol_splitL (i j : Fin k) (F : Finset (Fin k × Fin k)) :
    Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1)) :=
  Finset.univ.filter fun e =>
    (mol_vL i j e.1, mol_vL i j e.2) ∈ F ∧ (mol_vL i j e.1, mol_vL i j e.2) ≠ (i, j)

/-- The dissection of the polygon of `Cut_{R,i,j}` induced by `F`. -/
private def mol_splitR (i j : Fin k) (F : Finset (Fin k × Fin k)) :
    Finset (Fin (j - i + 1) × Fin (j - i + 1)) :=
  Finset.univ.filter fun e =>
    (mol_vR i j e.1, mol_vR i j e.2) ∈ F ∧ (mol_vR i j e.1, mol_vR i j e.2) ≠ (i, j)

/-- The dissection of the `k`-gon glued from dissections of the two polygons and `(i, j)`. -/
private def mol_glue (i j : Fin k) (FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1)))
    (FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))) : Finset (Fin k × Fin k) :=
  insert (i, j) (FL.image (fun e => (mol_vL i j e.1, mol_vL i j e.2)) ∪
    FR.image (fun e => (mol_vR i j e.1, mol_vR i j e.2)))

private lemma mol_mem_splitL {i j : Fin k} {F : Finset (Fin k × Fin k)}
    (e : Fin (k + i - j + 1) × Fin (k + i - j + 1)) :
    e ∈ mol_splitL i j F ↔
      (mol_vL i j e.1, mol_vL i j e.2) ∈ F ∧ (mol_vL i j e.1, mol_vL i j e.2) ≠ (i, j) := by
  simp [mol_splitL]

private lemma mol_mem_splitR {i j : Fin k} {F : Finset (Fin k × Fin k)}
    (e : Fin (j - i + 1) × Fin (j - i + 1)) :
    e ∈ mol_splitR i j F ↔
      (mol_vR i j e.1, mol_vR i j e.2) ∈ F ∧ (mol_vR i j e.1, mol_vR i j e.2) ≠ (i, j) := by
  simp [mol_splitR]

/-- Every other diagonal of a dissection containing `(i, j)` lies on one side of it. -/
private lemma mol_cover {i j : Fin k} {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k)
    (hd : (i, j) ∈ F) {e : Fin k × Fin k} (he : e ∈ F) (hne : e ≠ (i, j)) :
    ((e.1.val ≤ i.val ∨ j.val ≤ e.1.val) ∧ (e.2.val ≤ i.val ∨ j.val ≤ e.2.val)) ∨
      ((i.val ≤ e.1.val ∧ e.1.val ≤ j.val) ∧ (i.val ≤ e.2.val ∧ e.2.val ≤ j.val)) := by
  rw [mol_mem_dissections] at hF
  have h0 := (mol_mem_polyDiags _).mp (hF.1 he)
  have h1 := hF.2 _ hd _ he
  have h2 := hF.2 _ he _ hd
  have h3 := mol_prod_ne hne
  rw [mol_diagCross_iff] at h1 h2
  simp only at h1 h2 h3
  omega

private lemma mol_splitL_mem {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) :
    mol_splitL i j F ∈ dissections (k + i - j + 1) := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  rw [mol_mem_dissections] at hF ⊢
  refine ⟨fun e he => ?_, fun d' hd' e he => ?_⟩
  · rw [mol_mem_splitL] at he
    have h1 := (mol_mem_polyDiags _).mp (hF.1 he.1)
    have h2 := mol_prod_ne he.2
    rw [mol_mem_polyDiags]
    simp only [mol_vL_val] at h1 h2
    have := e.1.isLt; have := e.2.isLt; have := j.isLt
    split_ifs at h1 h2 <;> omega
  · rw [mol_mem_splitL] at hd' he
    have h := hF.2 _ hd'.1 _ he.1
    rw [mol_diagCross_iff] at h ⊢
    simp only [mol_vL_val] at h
    split_ifs at h <;> omega

private lemma mol_splitR_mem {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) :
    mol_splitR i j F ∈ dissections (j - i + 1) := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  rw [mol_mem_dissections] at hF ⊢
  refine ⟨fun e he => ?_, fun d' hd' e he => ?_⟩
  · rw [mol_mem_splitR] at he
    have h1 := (mol_mem_polyDiags _).mp (hF.1 he.1)
    have h2 := mol_prod_ne he.2
    rw [mol_mem_polyDiags]
    simp only [mol_vR_val] at h1 h2
    have := e.1.isLt; have := e.2.isLt; have := j.isLt
    omega
  · rw [mol_mem_splitR] at hd' he
    have h := hF.2 _ hd'.1 _ he.1
    rw [mol_diagCross_iff] at h ⊢
    simp only [mol_vR_val] at h
    omega

private lemma mol_glue_mem {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1))}
    {FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))}
    (hL : FL ∈ dissections (k + i - j + 1)) (hR : FR ∈ dissections (j - i + 1)) :
    mol_glue i j FL FR ∈ dissections k := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  rw [mol_mem_dissections] at hL hR ⊢
  refine ⟨fun e he => ?_, fun e he f hf => ?_⟩
  · simp only [mol_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at he
    rcases he with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · exact hd
    · have h1 := (mol_mem_polyDiags _).mp (hL.1 ha)
      have := a.1.isLt; have := a.2.isLt
      rw [mol_mem_polyDiags]
      simp only [mol_vL_val]
      split_ifs <;> omega
    · have h1 := (mol_mem_polyDiags _).mp (hR.1 hb)
      have := b.1.isLt; have := b.2.isLt
      rw [mol_mem_polyDiags]
      simp only [mol_vR_val]
      omega
  · simp only [mol_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at he hf
    rw [mol_diagCross_iff]
    rcases he with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;>
      rcases hf with rfl | ⟨a', ha', rfl⟩ | ⟨b', hb', rfl⟩
    · omega
    · have h1 := (mol_mem_polyDiags _).mp (hL.1 ha')
      have := a'.1.isLt; have := a'.2.isLt
      simp only [mol_vL_val]
      split_ifs <;> omega
    · have h1 := (mol_mem_polyDiags _).mp (hR.1 hb')
      have := b'.1.isLt; have := b'.2.isLt
      simp only [mol_vR_val]
      omega
    · have h1 := (mol_mem_polyDiags _).mp (hL.1 ha)
      have := a.1.isLt; have := a.2.isLt
      simp only [mol_vL_val]
      split_ifs <;> omega
    · have h1 := (mol_mem_polyDiags _).mp (hL.1 ha)
      have h2 := (mol_mem_polyDiags _).mp (hL.1 ha')
      have h3 := hL.2 _ ha _ ha'
      rw [mol_diagCross_iff] at h3
      have := a.1.isLt; have := a.2.isLt; have := a'.1.isLt; have := a'.2.isLt
      simp only [mol_vL_val]
      split_ifs <;> omega
    · have h1 := (mol_mem_polyDiags _).mp (hL.1 ha)
      have h2 := (mol_mem_polyDiags _).mp (hR.1 hb')
      have := a.1.isLt; have := a.2.isLt; have := b'.1.isLt; have := b'.2.isLt
      simp only [mol_vL_val, mol_vR_val]
      split_ifs <;> omega
    · have h1 := (mol_mem_polyDiags _).mp (hR.1 hb)
      have := b.1.isLt; have := b.2.isLt
      simp only [mol_vR_val]
      omega
    · have h1 := (mol_mem_polyDiags _).mp (hR.1 hb)
      have h2 := (mol_mem_polyDiags _).mp (hL.1 ha')
      have := b.1.isLt; have := b.2.isLt; have := a'.1.isLt; have := a'.2.isLt
      simp only [mol_vL_val, mol_vR_val]
      split_ifs <;> omega
    · have h1 := (mol_mem_polyDiags _).mp (hR.1 hb)
      have h2 := (mol_mem_polyDiags _).mp (hR.1 hb')
      have h3 := hR.2 _ hb _ hb'
      rw [mol_diagCross_iff] at h3
      have := b.1.isLt; have := b.2.isLt; have := b'.1.isLt; have := b'.2.isLt
      simp only [mol_vR_val]
      omega

private lemma mol_glue_split {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) :
    mol_glue i j (mol_splitL i j F) (mol_splitR i j F) = F := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  ext e
  simp only [mol_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image, mol_mem_splitL,
    mol_mem_splitR]
  constructor
  · rintro (rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact hdF
    · exact ha.1
    · exact hb.1
  · intro he
    by_cases hne : e = (i, j)
    · exact Or.inl hne
    right
    rcases mol_cover hF hdF he hne with h | h
    · left
      refine ⟨(mol_uL i j e.1, mol_uL i j e.2), ?_, ?_⟩ <;>
        simp only [mol_vL_uL h.1, mol_vL_uL h.2]
      exact ⟨he, hne⟩
    · right
      refine ⟨(mol_uR i j e.1, mol_uR i j e.2), ?_, ?_⟩ <;>
        simp only [mol_vR_uR h.1, mol_vR_uR h.2]
      exact ⟨he, hne⟩

private lemma mol_splitL_glue {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1))}
    {FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))}
    (hL : FL ∈ dissections (k + i - j + 1)) (hR : FR ∈ dissections (j - i + 1)) :
    mol_splitL i j (mol_glue i j FL FR) = FL := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  rw [mol_mem_dissections] at hL hR
  ext e
  rw [mol_mem_splitL]
  simp only [mol_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨h | ⟨a, ha, he⟩ | ⟨b, hb, he⟩, hne⟩
    · exact absurd h hne
    · have h1 : a = e := by
        have := congrArg Prod.fst he; have := congrArg Prod.snd he
        exact Prod.ext (mol_vL_inj (by omega) (by assumption))
          (mol_vL_inj (by omega) (by assumption))
      exact h1 ▸ ha
    · exfalso
      have h1 := (mol_mem_polyDiags _).mp (hR.1 hb)
      have h2 := mol_prod_ne hne
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      have := b.1.isLt; have := b.2.isLt; have := e.1.isLt; have := e.2.isLt
      simp only [mol_vL_val, mol_vR_val] at e1 e2 h2
      split_ifs at e1 e2 h2 <;> omega
  · intro he
    have h1 := (mol_mem_polyDiags _).mp (hL.1 he)
    refine ⟨Or.inr (Or.inl ⟨e, he, rfl⟩), fun h => ?_⟩
    have e1 := congrArg (fun x => x.1.val) h
    have e2 := congrArg (fun x => x.2.val) h
    have := e.1.isLt; have := e.2.isLt
    simp only [mol_vL_val] at e1 e2
    split_ifs at e1 e2 <;> omega

private lemma mol_splitR_glue {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1))}
    {FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))}
    (hL : FL ∈ dissections (k + i - j + 1)) (hR : FR ∈ dissections (j - i + 1)) :
    mol_splitR i j (mol_glue i j FL FR) = FR := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  rw [mol_mem_dissections] at hL hR
  ext e
  rw [mol_mem_splitR]
  simp only [mol_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨h | ⟨a, ha, he⟩ | ⟨b, hb, he⟩, hne⟩
    · exact absurd h hne
    · exfalso
      have h1 := (mol_mem_polyDiags _).mp (hL.1 ha)
      have h2 := mol_prod_ne hne
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      have := a.1.isLt; have := a.2.isLt; have := e.1.isLt; have := e.2.isLt
      simp only [mol_vL_val, mol_vR_val] at e1 e2 h2
      split_ifs at e1 e2 h2 <;> omega
    · have h1 : b = e := by
        have := congrArg Prod.fst he; have := congrArg Prod.snd he
        exact Prod.ext (mol_vR_inj (by assumption)) (mol_vR_inj (by assumption))
      exact h1 ▸ hb
  · intro he
    have h1 := (mol_mem_polyDiags _).mp (hR.1 he)
    refine ⟨Or.inr (Or.inr ⟨e, he, rfl⟩), fun h => ?_⟩
    have e1 := congrArg (fun x => x.1.val) h
    have e2 := congrArg (fun x => x.2.val) h
    have := e.1.isLt; have := e.2.isLt
    simp only [mol_vR_val] at e1 e2
    omega

/-- Marking the diagonal `(i, j)` in a dissection is a bijection onto the pairs of dissections
of the two polygons of the cut. -/
private lemma mol_sum_split {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {γ : Type*}
    [AddCommMonoid γ]
    (H : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1)) →
      Finset (Fin (j - i + 1) × Fin (j - i + 1)) → γ) :
    ∑ F ∈ (dissections k).filter (fun F => (i, j) ∈ F), H (mol_splitL i j F) (mol_splitR i j F)
      = ∑ FL ∈ dissections (k + i - j + 1), ∑ FR ∈ dissections (j - i + 1), H FL FR := by
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun F => (mol_splitL i j F, mol_splitR i j F))
    (fun p => mol_glue i j p.1 p.2)
  · intro F hF
    rw [Finset.mem_filter] at hF
    rw [Finset.mem_product]
    exact ⟨mol_splitL_mem hd hF.1, mol_splitR_mem hd hF.1⟩
  · intro p hp
    rw [Finset.mem_product] at hp
    rw [Finset.mem_filter]
    exact ⟨mol_glue_mem hd hp.1 hp.2, Finset.mem_insert_self _ _⟩
  · intro F hF
    rw [Finset.mem_filter] at hF
    exact mol_glue_split hd hF.1 hF.2
  · intro p hp
    rw [Finset.mem_product] at hp
    exact Prod.ext (mol_splitL_glue hd hp.1 hp.2) (mol_splitR_glue hd hp.1 hp.2)
  · intro F _
    rfl

end Split

/-! ## Face corners of the two polygons of a cut -/

section Corners

variable {k : ℕ}

private lemma mol_minmax {n : ℕ} {v u : Fin n} (h : u ≠ v) :
    ((min v u).val = v.val ∧ (max v u).val = u.val ∧ v.val < u.val) ∨
      ((min v u).val = u.val ∧ (max v u).val = v.val ∧ u.val < v.val) := by
  rcases lt_or_gt_of_ne h with h' | h'
  · right
    rw [min_eq_right h'.le, max_eq_left h'.le]
    exact ⟨rfl, rfl, h'⟩
  · left
    rw [min_eq_left h'.le, max_eq_right h'.le]
    exact ⟨rfl, rfl, h'⟩

lemma mol_mem_polyCorners {n : ℕ} (F : Finset (Fin n × Fin n)) (v : Fin n)
    (p : Fin n × Fin n) :
    p ∈ polyCorners F v ↔ PolyNbr F v p.1 ∧ PolyNbr F v p.2 ∧ polyOff v p.1 < polyOff v p.2 ∧
      ∀ u, PolyNbr F v u → ¬(polyOff v p.1 < polyOff v u ∧ polyOff v u < polyOff v p.2) := by
  simp [polyCorners]

/-- Neighbours in a dissection containing `(i, j)` lie on a common side of it. -/
private lemma mol_nbr_side {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) {v u : Fin k}
    (h : PolyNbr F v u) :
    ((v.val ≤ i.val ∨ j.val ≤ v.val) ∧ (u.val ≤ i.val ∨ j.val ≤ u.val)) ∨
      ((i.val ≤ v.val ∧ v.val ≤ j.val) ∧ (i.val ≤ u.val ∧ u.val ≤ j.val)) := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have := v.isLt; have := u.isLt
  obtain ⟨hne, h⟩ := h
  have hmm := mol_minmax hne
  rcases h with h | h | h
  · rw [mol_polyOff_eq] at h; split_ifs at h <;> omega
  · rw [mol_polyOff_eq] at h; split_ifs at h <;> omega
  · by_cases he : (min v u, max v u) = (i, j)
    · have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      simp only at e1 e2
      omega
    · have := mol_cover hF hdF h he
      simp only at this
      omega

/-- `mol_vL` preserves and reflects neighbours. -/
private lemma mol_nbr_vL {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (v w : Fin (k + i - j + 1)) :
    PolyNbr F (mol_vL i j v) (mol_vL i j w) ↔ PolyNbr (mol_splitL i j F) v w := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have hmono := (mol_vL_strictMono (i := i) (j := j) (by omega)).monotone
  unfold PolyNbr
  rw [← hmono.map_min, ← hmono.map_max, mol_mem_splitL]
  by_cases hw : w = v
  · subst hw; simp
  have hw' : mol_vL i j w ≠ mol_vL i j v := fun h => hw (mol_vL_inj (by omega) h)
  have hmm := mol_minmax hw
  have := v.isLt; have := w.isLt; have := j.isLt
  have key : ((mol_vL i j (min v w), mol_vL i j (max v w)) = (i, j) →
      (polyOff v w = 1 ∨ polyOff v w + 1 = k + i - j + 1)) ∧
      ((mol_vL i j (min v w), mol_vL i j (max v w)) ≠ (i, j) →
        ((polyOff (mol_vL i j v) (mol_vL i j w) = 1 ∨
          polyOff (mol_vL i j v) (mol_vL i j w) + 1 = k) ↔
        (polyOff v w = 1 ∨ polyOff v w + 1 = k + i - j + 1))) := by
    constructor
    · intro he
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      simp only [mol_vL_val] at e1 e2
      simp only [mol_polyOff_eq]
      split_ifs at e1 e2 ⊢ <;> omega
    · intro he
      have he' := mol_prod_ne he
      simp only [mol_vL_val] at he'
      simp only [mol_polyOff_eq, mol_vL_val]
      split_ifs at he' ⊢ <;> omega
  by_cases hq : (mol_vL i j (min v w), mol_vL i j (max v w)) = (i, j)
  · have hB := key.1 hq
    rw [hq]
    exact ⟨fun _ => ⟨hw, hB.elim Or.inl (fun h => Or.inr (Or.inl h))⟩,
      fun _ => ⟨hw', Or.inr (Or.inr hdF)⟩⟩
  · have hAB := key.2 hq
    constructor
    · rintro ⟨-, h⟩
      refine ⟨hw, ?_⟩
      rcases h with h | h | h
      · exact (hAB.mp (Or.inl h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact (hAB.mp (Or.inr h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr ⟨h, hq⟩)
    · rintro ⟨-, h⟩
      refine ⟨hw', ?_⟩
      rcases h with h | h | h
      · exact (hAB.mpr (Or.inl h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact (hAB.mpr (Or.inr h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr h.1)

/-- `mol_vR` preserves and reflects neighbours. -/
private lemma mol_nbr_vR {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (v w : Fin (j - i + 1)) :
    PolyNbr F (mol_vR i j v) (mol_vR i j w) ↔ PolyNbr (mol_splitR i j F) v w := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have hmono := (mol_vR_strictMono i j).monotone
  unfold PolyNbr
  rw [← hmono.map_min, ← hmono.map_max, mol_mem_splitR]
  by_cases hw : w = v
  · subst hw; simp
  have hw' : mol_vR i j w ≠ mol_vR i j v := fun h => hw (mol_vR_inj h)
  have hmm := mol_minmax hw
  have := v.isLt; have := w.isLt; have := j.isLt
  have key : ((mol_vR i j (min v w), mol_vR i j (max v w)) = (i, j) →
      (polyOff v w = 1 ∨ polyOff v w + 1 = j - i + 1)) ∧
      ((mol_vR i j (min v w), mol_vR i j (max v w)) ≠ (i, j) →
        ((polyOff (mol_vR i j v) (mol_vR i j w) = 1 ∨
          polyOff (mol_vR i j v) (mol_vR i j w) + 1 = k) ↔
        (polyOff v w = 1 ∨ polyOff v w + 1 = j - i + 1))) := by
    constructor
    · intro he
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      simp only [mol_vR_val] at e1 e2
      simp only [mol_polyOff_eq]
      split_ifs <;> omega
    · intro he
      have he' := mol_prod_ne he
      simp only [mol_vR_val] at he'
      simp only [mol_polyOff_eq, mol_vR_val, Nat.add_le_add_iff_left]
      split_ifs <;> omega
  by_cases hq : (mol_vR i j (min v w), mol_vR i j (max v w)) = (i, j)
  · have hB := key.1 hq
    rw [hq]
    exact ⟨fun _ => ⟨hw, hB.elim Or.inl (fun h => Or.inr (Or.inl h))⟩,
      fun _ => ⟨hw', Or.inr (Or.inr hdF)⟩⟩
  · have hAB := key.2 hq
    constructor
    · rintro ⟨-, h⟩
      refine ⟨hw, ?_⟩
      rcases h with h | h | h
      · exact (hAB.mp (Or.inl h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact (hAB.mp (Or.inr h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr ⟨h, hq⟩)
    · rintro ⟨-, h⟩
      refine ⟨hw', ?_⟩
      rcases h with h | h | h
      · exact (hAB.mpr (Or.inl h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact (hAB.mpr (Or.inr h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr h.1)

/-- The face corners of a dissection as a set of triples `(v, w, w')`. -/
private def mol_cornerP {n : ℕ} (F : Finset (Fin n × Fin n)) : Finset (Fin n × (Fin n × Fin n)) :=
  Finset.univ.filter fun x => x.2 ∈ polyCorners F x.1

private lemma mol_prod_corners {n : ℕ} (F : Finset (Fin n × Fin n))
    (f : Fin n → Fin n × Fin n → ℂ) :
    ∏ v, ∏ p ∈ polyCorners F v, f v p = ∏ x ∈ mol_cornerP F, f x.1 x.2 := by
  rw [mol_cornerP, Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun v _ => ?_
  dsimp only
  rw [Finset.prod_ite_mem, Finset.univ_inter]

private lemma mol_nbr_diag {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) : PolyNbr F i j ∧ PolyNbr F j i := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have hle : i ≤ j := by rw [Fin.le_def]; omega
  have hne : j ≠ i := fun h => by rw [h] at hdv; omega
  refine ⟨⟨hne, Or.inr (Or.inr ?_)⟩, ⟨hne.symm, Or.inr (Or.inr ?_)⟩⟩
  · rwa [min_eq_left hle, max_eq_right hle]
  · rwa [min_eq_right hle, max_eq_left hle]

private lemma mol_corner_toL {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) {v w w' : Fin k}
    (hv : v.val ≤ i.val ∨ j.val ≤ v.val) (hw : w.val ≤ i.val ∨ j.val ≤ w.val)
    (hw' : w'.val ≤ i.val ∨ j.val ≤ w'.val) (h : (w, w') ∈ polyCorners F v) :
    (mol_uL i j w, mol_uL i j w') ∈ polyCorners (mol_splitL i j F) (mol_uL i j v) := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  rw [← mol_vL_uL hv, ← mol_vL_uL hw, ← mol_vL_uL hw'] at h
  rw [mol_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(mol_nbr_vL hd hdF _ _).mp n1, (mol_nbr_vL hd hdF _ _).mp n2,
    (mol_off_vL hij _ _ _).mpr o, fun u hu => ?_⟩
  rw [mol_off_vL hij _ _ u, mol_off_vL hij _ u _]
  exact nb _ ((mol_nbr_vL hd hdF _ _).mpr hu)

private lemma mol_corner_toR {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) {v w w' : Fin k}
    (hv : i.val ≤ v.val ∧ v.val ≤ j.val) (hw : i.val ≤ w.val ∧ w.val ≤ j.val)
    (hw' : i.val ≤ w'.val ∧ w'.val ≤ j.val) (h : (w, w') ∈ polyCorners F v) :
    (mol_uR i j w, mol_uR i j w') ∈ polyCorners (mol_splitR i j F) (mol_uR i j v) := by
  rw [← mol_vR_uR hv, ← mol_vR_uR hw, ← mol_vR_uR hw'] at h
  rw [mol_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(mol_nbr_vR hd hdF _ _).mp n1, (mol_nbr_vR hd hdF _ _).mp n2,
    (mol_off_vR i j _ _ _).mpr o, fun u hu => ?_⟩
  rw [mol_off_vR i j _ _ u, mol_off_vR i j _ u _]
  exact nb _ ((mol_nbr_vR hd hdF _ _).mpr hu)

private lemma mol_corner_fromL {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    {v w w' : Fin (k + i - j + 1)} (h : (w, w') ∈ polyCorners (mol_splitL i j F) v) :
    (mol_vL i j w, mol_vL i j w') ∈ polyCorners F (mol_vL i j v) := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  rw [mol_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(mol_nbr_vL hd hdF _ _).mpr n1, (mol_nbr_vL hd hdF _ _).mpr n2,
    (mol_off_vL hij _ _ _).mp o, fun u hu => ?_⟩
  by_cases huL : u.val ≤ i.val ∨ j.val ≤ u.val
  · rw [← mol_vL_uL huL] at hu ⊢
    rw [← mol_off_vL hij, ← mol_off_vL hij]
    exact nb _ ((mol_nbr_vL hd hdF _ _).mp hu)
  · have hs := mol_nbr_side hd hF hdF hu
    have h1 : w ≠ v := n1.1
    have h2 : w' ≠ v := n2.1
    have h1' : w.val ≠ v.val := fun e => h1 (Fin.ext e)
    have h2' : w'.val ≠ v.val := fun e => h2 (Fin.ext e)
    have := v.isLt; have := w.isLt; have := w'.isLt; have := u.isLt
    simp only [mol_vL_val] at hs
    simp only [mol_polyOff_eq, mol_vL_val]
    split_ifs at hs ⊢ <;> omega

private lemma mol_corner_fromR {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    {v w w' : Fin (j - i + 1)} (h : (w, w') ∈ polyCorners (mol_splitR i j F) v) :
    (mol_vR i j w, mol_vR i j w') ∈ polyCorners F (mol_vR i j v) := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  rw [mol_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(mol_nbr_vR hd hdF _ _).mpr n1, (mol_nbr_vR hd hdF _ _).mpr n2,
    (mol_off_vR i j _ _ _).mp o, fun u hu => ?_⟩
  by_cases huR : i.val ≤ u.val ∧ u.val ≤ j.val
  · rw [← mol_vR_uR huR] at hu ⊢
    rw [← mol_off_vR, ← mol_off_vR]
    exact nb _ ((mol_nbr_vR hd hdF _ _).mp hu)
  · have hs := mol_nbr_side hd hF hdF hu
    have h1 : w ≠ v := n1.1
    have h2 : w' ≠ v := n2.1
    have h1' : w.val ≠ v.val := fun e => h1 (Fin.ext e)
    have h2' : w'.val ≠ v.val := fun e => h2 (Fin.ext e)
    have := v.isLt; have := w.isLt; have := w'.isLt; have := u.isLt; have := j.isLt
    simp only [mol_vR_val] at hs
    have c1 := mol_polyOff_cases (mol_vR i j v) (mol_vR i j w)
    have c2 := mol_polyOff_cases (mol_vR i j v) u
    have c3 := mol_polyOff_cases (mol_vR i j v) (mol_vR i j w')
    simp only [mol_vR_val] at c1 c2 c3
    omega

/-- Every face corner lies in one of the two polygons of the cut. -/
private lemma mol_corner_sides {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) {v w w' : Fin k}
    (h : (w, w') ∈ polyCorners F v) :
    ((v.val ≤ i.val ∨ j.val ≤ v.val) ∧ (w.val ≤ i.val ∨ j.val ≤ w.val) ∧
        (w'.val ≤ i.val ∨ j.val ≤ w'.val)) ∨
      ((i.val ≤ v.val ∧ v.val ≤ j.val) ∧ (i.val ≤ w.val ∧ w.val ≤ j.val) ∧
        (i.val ≤ w'.val ∧ w'.val ≤ j.val)) := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  rw [mol_mem_polyCorners] at h
  dsimp only at h
  obtain ⟨n1, n2, o, nb⟩ := h
  have s1 := mol_nbr_side hd hF hdF n1
  have s2 := mol_nbr_side hd hF hdF n2
  have h1' : w.val ≠ v.val := fun e => n1.1 (Fin.ext e)
  have h2' : w'.val ≠ v.val := fun e => n2.1 (Fin.ext e)
  have := v.isLt; have := w.isLt; have := w'.isLt; have := j.isLt
  by_cases hvi : v = i
  · subst hvi
    have hb := nb j (mol_nbr_diag hd hdF).1
    have c1 := mol_polyOff_cases v w
    have c2 := mol_polyOff_cases v w'
    have c3 := mol_polyOff_cases v j
    omega
  by_cases hvj : v = j
  · subst hvj
    have hb := nb i (mol_nbr_diag hd hdF).2
    have c1 := mol_polyOff_cases v w
    have c2 := mol_polyOff_cases v w'
    have c3 := mol_polyOff_cases v i
    omega
  have hvi' : v.val ≠ i.val := fun e => hvi (Fin.ext e)
  have hvj' : v.val ≠ j.val := fun e => hvj (Fin.ext e)
  omega

/-- The face corners of `F` are those of the two polygons of the cut, transported by the vertex
maps. -/
private lemma mol_prod_cornerP_split {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    (g : Fin k × (Fin k × Fin k) → ℂ) :
    ∏ x ∈ mol_cornerP F, g x =
      (∏ x ∈ mol_cornerP (mol_splitL i j F),
        g (mol_vL i j x.1, (mol_vL i j x.2.1, mol_vL i j x.2.2))) *
      ∏ x ∈ mol_cornerP (mol_splitR i j F),
        g (mol_vR i j x.1, (mol_vR i j x.2.1, mol_vR i j x.2.2)) := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  set ψL : Fin (k + i - j + 1) × (Fin (k + i - j + 1) × Fin (k + i - j + 1)) →
      Fin k × (Fin k × Fin k) := fun x => (mol_vL i j x.1, (mol_vL i j x.2.1, mol_vL i j x.2.2))
  set ψR : Fin (j - i + 1) × (Fin (j - i + 1) × Fin (j - i + 1)) →
      Fin k × (Fin k × Fin k) := fun x => (mol_vR i j x.1, (mol_vR i j x.2.1, mol_vR i j x.2.2))
  have hS : mol_cornerP F = (mol_cornerP (mol_splitL i j F)).image ψL ∪
      (mol_cornerP (mol_splitR i j F)).image ψR := by
    ext ⟨v, w, w'⟩
    simp only [mol_cornerP, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases mol_corner_sides hd hF hdF h with ⟨hv, hw, hw'⟩ | ⟨hv, hw, hw'⟩
      · left
        refine ⟨(mol_uL i j v, (mol_uL i j w, mol_uL i j w')),
          mol_corner_toL hd hdF hv hw hw' h, ?_⟩
        simp only [ψL, mol_vL_uL hv, mol_vL_uL hw, mol_vL_uL hw']
      · right
        refine ⟨(mol_uR i j v, (mol_uR i j w, mol_uR i j w')),
          mol_corner_toR hd hdF hv hw hw' h, ?_⟩
        simp only [ψR, mol_vR_uR hv, mol_vR_uR hw, mol_vR_uR hw']
    · rintro (⟨x, hx, hxe⟩ | ⟨x, hx, hxe⟩)
      · simp only [ψL, Prod.mk.injEq] at hxe
        obtain ⟨rfl, rfl, rfl⟩ := hxe
        exact mol_corner_fromL hd hF hdF hx
      · simp only [ψR, Prod.mk.injEq] at hxe
        obtain ⟨rfl, rfl, rfl⟩ := hxe
        exact mol_corner_fromR hd hF hdF hx
  have hinjL : Set.InjOn ψL (mol_cornerP (mol_splitL i j F)) := by
    intro x _ y _ hxy
    simp only [ψL, Prod.mk.injEq] at hxy
    exact Prod.ext (mol_vL_inj hij hxy.1)
      (Prod.ext (mol_vL_inj hij hxy.2.1) (mol_vL_inj hij hxy.2.2))
  have hinjR : Set.InjOn ψR (mol_cornerP (mol_splitR i j F)) := by
    intro x _ y _ hxy
    simp only [ψR, Prod.mk.injEq] at hxy
    exact Prod.ext (mol_vR_inj hxy.1) (Prod.ext (mol_vR_inj hxy.2.1) (mol_vR_inj hxy.2.2))
  have hdisj : Disjoint ((mol_cornerP (mol_splitL i j F)).image ψL)
      ((mol_cornerP (mol_splitR i j F)).image ψR) := by
    rw [Finset.disjoint_left]
    rintro z hzL hzR
    simp only [Finset.mem_image, mol_cornerP, Finset.mem_filter, Finset.mem_univ,
      true_and] at hzL hzR
    obtain ⟨x, hx, rfl⟩ := hzL
    obtain ⟨y, hy, hxy⟩ := hzR
    simp only [ψL, ψR, Prod.mk.injEq] at hxy
    obtain ⟨e1, e2, e3⟩ := hxy
    rw [mol_mem_polyCorners] at hx
    obtain ⟨n1, n2, o, -⟩ := hx
    have h1 : x.2.1.val ≠ x.1.val := fun e => n1.1 (Fin.ext e)
    have h2 : x.2.2.val ≠ x.1.val := fun e => n2.1 (Fin.ext e)
    have h3 : x.2.1.val ≠ x.2.2.val := by
      intro e
      have : x.2.1 = x.2.2 := Fin.ext e
      rw [this] at o
      exact lt_irrefl _ o
    have f1 := congrArg Fin.val e1
    have f2 := congrArg Fin.val e2
    have f3 := congrArg Fin.val e3
    have := y.1.isLt; have := y.2.1.isLt; have := y.2.2.isLt; have := j.isLt
    have := x.1.isLt; have := x.2.1.isLt; have := x.2.2.isLt
    simp only [mol_vL_val, mol_vR_val] at f1 f2 f3
    split_ifs at f1 f2 f3 <;> omega
  rw [hS, Finset.prod_union hdisj, Finset.prod_image hinjL, Finset.prod_image hinjR]


private lemma mol_corner_conds {n : ℕ} {F : Finset (Fin n × Fin n)} {v : Fin n}
    {p : Fin n × Fin n} (h : p ∈ polyCorners F v) :
    PolyNbr F v p.1 ∧ PolyNbr F v p.2 ∧ polyOff v p.1 + 1 ≠ n ∧ polyOff v p.2 ≠ 1 := by
  rw [mol_mem_polyCorners] at h
  obtain ⟨n1, n2, o, -⟩ := h
  have h1 : p.1.val ≠ v.val := fun e => n1.1 (Fin.ext e)
  have h2 : p.2.val ≠ v.val := fun e => n2.1 (Fin.ext e)
  have c1 := mol_polyOff_cases v p.1
  have c2 := mol_polyOff_cases v p.2
  have := v.isLt; have := p.1.isLt; have := p.2.isLt
  exact ⟨n1, n2, by omega, by omega⟩

/-- The diagonals of the polygon of Cut_L as diagonals of `F`. -/
private def mol_ιL (i j : Fin k) (F : Finset (Fin k × Fin k)) (e : ↥(mol_splitL i j F)) : ↥F :=
  ⟨(mol_vL i j e.1.1, mol_vL i j e.1.2), ((mol_mem_splitL _).mp e.2).1⟩

/-- The diagonals of the polygon of Cut_R as diagonals of `F`. -/
private def mol_ιR (i j : Fin k) (F : Finset (Fin k × Fin k)) (e : ↥(mol_splitR i j F)) : ↥F :=
  ⟨(mol_vR i j e.1.1, mol_vR i j e.1.2), ((mol_mem_splitR _).mp e.2).1⟩

/-- The edge labels of the polygon of Cut_L: the side `i` carries the outer copy of the
label of `(i, j)`. -/
private lemma mol_edgeLab_L {L : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L)
    {v w : Fin (k + i - j + 1)} (hn : PolyNbr (mol_splitL i j F) v w) (small : Bool)
    (hs : if small then polyOff v w ≠ 1 else polyOff v w + 1 ≠ k + i - j + 1) :
    edgeLab (mol_splitL i j F)
        (fun p => if p.val = i.val then cOut ⟨(i, j), hdF⟩ else y (mol_vL i j p))
        (fun e => cIn (mol_ιL i j F e)) (fun e => cOut (mol_ιL i j F e)) v w small =
      edgeLab F y cIn cOut (mol_vL i j v) (mol_vL i j w) small := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hsm := mol_vL_strictMono (i := i) (j := j) hij
  have hmono := hsm.monotone
  simp only [edgeLab, ← hmono.map_min, ← hmono.map_max]
  obtain ⟨hne, hside⟩ := hn
  have hmm := mol_minmax hne
  have cv := mol_vL_cases i j v
  have cw := mol_vL_cases i j w
  have co := mol_polyOff_cases v w
  have co' := mol_polyOff_cases (mol_vL i j v) (mol_vL i j w)
  have := v.isLt; have := w.isLt; have := j.isLt
  have hlt : decide (v < w) = decide (mol_vL i j v < mol_vL i j w) := by
    simp only [hsm.lt_iff_lt]
  by_cases h' : (min v w, max v w) ∈ mol_splitL i j F
  · have h1 : (mol_vL i j (min v w), mol_vL i j (max v w)) ∈ F :=
      ((mol_mem_splitL _).mp h').1
    rw [dite_eq_left h', dite_eq_left h1, hlt]
    rfl
  · rw [dite_eq_right h']
    have hside' : polyOff v w = 1 ∨ polyOff v w + 1 = k + i - j + 1 := by
      rcases hside with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h h'
    by_cases hq : (mol_vL i j (min v w), mol_vL i j (max v w)) = (i, j)
    · have h1 : (mol_vL i j (min v w), mol_vL i j (max v w)) ∈ F := hq ▸ hdF
      rw [dite_eq_left h1]
      have e1 := congrArg (fun x => x.1.val) hq
      have e2 := congrArg (fun x => x.2.val) hq
      have cmin := mol_vL_cases i j (min v w)
      have cmax := mol_vL_cases i j (max v w)
      simp only at e1 e2
      have hsub : (⟨(mol_vL i j (min v w), mol_vL i j (max v w)), h1⟩ : ↥F) = ⟨(i, j), hdF⟩ :=
        Subtype.ext hq
      cases small
      · simp only [Bool.false_eq_true, ite_false] at hs
        have hv : v.val = i.val := by omega
        have hw : ¬ mol_vL i j v < mol_vL i j w → False := by
          intro h; rw [Fin.lt_def] at h; omega
        have hpos : polyOff v w = 1 := by omega
        rw [ite_eq_left hpos, ite_eq_left hv, hsub]
        have : decide (mol_vL i j v < mol_vL i j w) = true := by
          by_contra hc; exact hw (by simpa using hc)
        rw [this]
        rfl
      · simp only [ite_true] at hs
        have hw : w.val = i.val := by omega
        have hv : ¬ mol_vL i j v < mol_vL i j w := by
          rw [Fin.lt_def]; omega
        rw [ite_eq_right hs, ite_eq_left hw, hsub]
        simp [hv]
    · have h1 : (mol_vL i j (min v w), mol_vL i j (max v w)) ∉ F :=
        fun h => h' ((mol_mem_splitL _).mpr ⟨h, hq⟩)
      rw [dite_eq_right h1]
      clear hmm
      by_cases h1 : polyOff v w = 1
      · have h2 : polyOff (mol_vL i j v) (mol_vL i j w) = 1 := by
          have hq' := mol_prod_ne hq
          simp only at hq'
          have hw1 : (w.val = v.val + 1) ∨ (v.val + 1 = k + i - j + 1 ∧ w.val = 0) := by omega
          rcases hw1 with hw1 | hw1
          · have hvw : v < w := by rw [Fin.lt_def]; omega
            rw [min_eq_left hvw.le, max_eq_right hvw.le] at hq'
            omega
          · have hvw : w < v := by rw [Fin.lt_def]; omega
            rw [min_eq_right hvw.le, max_eq_left hvw.le] at hq'
            omega
        have h3 : v.val ≠ i.val := by
          clear co'
          have hmm := mol_minmax hne
          have hq' := mol_prod_ne hq
          have cmin := mol_vL_cases i j (min v w)
          have cmax := mol_vL_cases i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_left h1, ite_eq_left h2, ite_eq_right h3]
      · have h2 : polyOff (mol_vL i j v) (mol_vL i j w) ≠ 1 := by omega
        have h3 : w.val ≠ i.val := by
          clear co'
          have hmm := mol_minmax hne
          have hq' := mol_prod_ne hq
          have cmin := mol_vL_cases i j (min v w)
          have cmax := mol_vL_cases i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

/-- The edge labels of the polygon of Cut_R: the last side carries the inner copy of the
label of `(i, j)`. -/
private lemma mol_edgeLab_R {L : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L)
    {v w : Fin (j - i + 1)} (hn : PolyNbr (mol_splitR i j F) v w) (small : Bool)
    (hs : if small then polyOff v w ≠ 1 else polyOff v w + 1 ≠ j - i + 1) :
    edgeLab (mol_splitR i j F)
        (fun q => if q.val = j.val - i.val then cIn ⟨(i, j), hdF⟩ else y (mol_vR i j q))
        (fun e => cIn (mol_ιR i j F e)) (fun e => cOut (mol_ιR i j F e)) v w small =
      edgeLab F y cIn cOut (mol_vR i j v) (mol_vR i j w) small := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have hsm := mol_vR_strictMono i j
  have hmono := hsm.monotone
  simp only [edgeLab, ← hmono.map_min, ← hmono.map_max]
  obtain ⟨hne, hside⟩ := hn
  have hmm := mol_minmax hne
  have cv := mol_vR_val i j v
  have cw := mol_vR_val i j w
  have co := mol_polyOff_cases v w
  have co' := mol_polyOff_cases (mol_vR i j v) (mol_vR i j w)
  have := v.isLt; have := w.isLt; have := j.isLt
  have hlt : decide (v < w) = decide (mol_vR i j v < mol_vR i j w) := by
    simp only [hsm.lt_iff_lt]
  by_cases h' : (min v w, max v w) ∈ mol_splitR i j F
  · have h1 : (mol_vR i j (min v w), mol_vR i j (max v w)) ∈ F :=
      ((mol_mem_splitR _).mp h').1
    rw [dite_eq_left h', dite_eq_left h1, hlt]
    rfl
  · rw [dite_eq_right h']
    have hside' : polyOff v w = 1 ∨ polyOff v w + 1 = j - i + 1 := by
      rcases hside with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h h'
    by_cases hq : (mol_vR i j (min v w), mol_vR i j (max v w)) = (i, j)
    · have h1 : (mol_vR i j (min v w), mol_vR i j (max v w)) ∈ F := hq ▸ hdF
      rw [dite_eq_left h1]
      have e1 := congrArg (fun x => x.1.val) hq
      have e2 := congrArg (fun x => x.2.val) hq
      have cmin := mol_vR_val i j (min v w)
      have cmax := mol_vR_val i j (max v w)
      simp only at e1 e2
      have hsub : (⟨(mol_vR i j (min v w), mol_vR i j (max v w)), h1⟩ : ↥F) = ⟨(i, j), hdF⟩ :=
        Subtype.ext hq
      cases small
      · simp only [Bool.false_eq_true, ite_false] at hs
        have hv : v.val = j.val - i.val := by omega
        have hw : ¬ mol_vR i j v < mol_vR i j w := by
          rw [Fin.lt_def]; omega
        have hpos : polyOff v w = 1 := by omega
        rw [ite_eq_left hpos, ite_eq_left hv, hsub]
        simp [hw]
      · simp only [ite_true] at hs
        have hw : w.val = j.val - i.val := by omega
        have hv : mol_vR i j v < mol_vR i j w := by
          rw [Fin.lt_def]; omega
        rw [ite_eq_right hs, ite_eq_left hw, hsub]
        simp [hv]
    · have h1 : (mol_vR i j (min v w), mol_vR i j (max v w)) ∉ F :=
        fun h => h' ((mol_mem_splitR _).mpr ⟨h, hq⟩)
      rw [dite_eq_right h1]
      clear hmm
      by_cases h1 : polyOff v w = 1
      · have h2 : polyOff (mol_vR i j v) (mol_vR i j w) = 1 := by
          have hq' := mol_prod_ne hq
          simp only at hq'
          have hw1 : (w.val = v.val + 1) ∨ (v.val + 1 = j - i + 1 ∧ w.val = 0) := by omega
          rcases hw1 with hw1 | hw1
          · have hvw : v < w := by rw [Fin.lt_def]; omega
            rw [min_eq_left hvw.le, max_eq_right hvw.le] at hq'
            omega
          · have hvw : w < v := by rw [Fin.lt_def]; omega
            rw [min_eq_right hvw.le, max_eq_left hvw.le] at hq'
            omega
        have h3 : v.val ≠ j.val - i.val := by
          clear co'
          have hmm := mol_minmax hne
          have hq' := mol_prod_ne hq
          have cmin := mol_vR_val i j (min v w)
          have cmax := mol_vR_val i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_left h1, ite_eq_left h2, ite_eq_right h3]
      · have h2 : polyOff (mol_vR i j v) (mol_vR i j w) ≠ 1 := by omega
        have h3 : w.val ≠ j.val - i.val := by
          clear co'
          have hmm := mol_minmax hne
          have hq' := mol_prod_ne hq
          have cmin := mol_vR_val i j (min v w)
          have cmax := mol_vR_val i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]


/-- The corner product of `F` splits into the corner products of the two polygons of the cut,
with the outer copy of the label of `(i, j)` on the side `i` of Cut_L and its inner copy on
the last side of Cut_R. -/
private lemma mol_corners_split {L : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    (M : Matrix (Fin L) (Fin L) ℂ) (σ : Fin k → Bool) (y : Fin k → Fin L)
    (cIn cOut : ↥F → Fin L) :
    (∏ v : Fin k, ∏ p ∈ polyCorners F v,
        sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)) =
      (∏ v : Fin (k + i - j + 1), ∏ p ∈ polyCorners (mol_splitL i j F) v,
        sgnMat M (cutLSgn σ i j v)
          (edgeLab (mol_splitL i j F)
            (fun p => if p.val = i.val then cOut ⟨(i, j), hdF⟩ else y (mol_vL i j p))
            (fun e => cIn (mol_ιL i j F e)) (fun e => cOut (mol_ιL i j F e)) v p.2 true)
          (edgeLab (mol_splitL i j F)
            (fun p => if p.val = i.val then cOut ⟨(i, j), hdF⟩ else y (mol_vL i j p))
            (fun e => cIn (mol_ιL i j F e)) (fun e => cOut (mol_ιL i j F e)) v p.1 false)) *
      (∏ v : Fin (j - i + 1), ∏ p ∈ polyCorners (mol_splitR i j F) v,
        sgnMat M (cutRSgn σ i j v)
          (edgeLab (mol_splitR i j F)
            (fun q => if q.val = j.val - i.val then cIn ⟨(i, j), hdF⟩ else y (mol_vR i j q))
            (fun e => cIn (mol_ιR i j F e)) (fun e => cOut (mol_ιR i j F e)) v p.2 true)
          (edgeLab (mol_splitR i j F)
            (fun q => if q.val = j.val - i.val then cIn ⟨(i, j), hdF⟩ else y (mol_vR i j q))
            (fun e => cIn (mol_ιR i j F e)) (fun e => cOut (mol_ιR i j F e)) v p.1 false)) := by
  rw [mol_prod_corners, mol_prod_corners, mol_prod_corners,
    mol_prod_cornerP_split hd hF hdF]
  congr 1
  · refine Finset.prod_congr rfl fun x hx => ?_
    simp only [mol_cornerP, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨n1, n2, c1, c2⟩ := mol_corner_conds hx
    rw [mol_cutLSgn_eq, mol_edgeLab_L hd hdF y cIn cOut n2 true (by simpa using c2),
      mol_edgeLab_L hd hdF y cIn cOut n1 false (by simpa using c1)]
  · refine Finset.prod_congr rfl fun x hx => ?_
    simp only [mol_cornerP, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨n1, n2, c1, c2⟩ := mol_corner_conds hx
    rw [mol_cutRSgn_eq, mol_edgeLab_R hd hdF y cIn cOut n2 true (by simpa using c2),
      mol_edgeLab_R hd hdF y cIn cOut n1 false (by simpa using c1)]

end Corners

/-! ## The core of a dissection with one link differentiated -/

section Glue

variable {k L : ℕ}

private lemma mol_sum_pair {T Y : Type*} [Fintype T] [DecidableEq T] [Fintype Y]
    (G : (T → Y) → (T → Y) → ℂ) :
    ∑ cIn : T → Y, ∑ cOut : T → Y, G cIn cOut =
      ∑ c : T → Y × Y, G (fun t => (c t).1) (fun t => (c t).2) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow T (fun _ => Y) (fun _ => Y)) _ _
    (fun c => rfl)).symm

private lemma mol_sum_option {A B T X : Type} [Fintype A] [Fintype B] [Fintype T]
    [DecidableEq A] [DecidableEq B] [DecidableEq T] [Fintype X] (e : Option (A ⊕ B) ≃ T)
    (G : (T → X) → ℂ) :
    ∑ c : T → X, G c = ∑ x : X, ∑ f : A → X, ∑ g : B → X,
      G (fun t => Option.elim (e.symm t) x (Sum.elim f g)) := by
  let E : X × ((A → X) × (B → X)) ≃ (T → X) :=
    ((Equiv.prodCongr (Equiv.refl X) (Equiv.sumArrowEquivProdArrow A B X).symm).trans
      (Equiv.piOptionEquivProd (α := A ⊕ B) (β := fun _ => X)).symm).trans
      (Equiv.arrowCongr e (Equiv.refl X))
  rw [← E.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => ?_
  congr 1
  funext t
  simp only [E, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map, id, Function.comp_apply, Equiv.refl_apply]
  cases e.symm t with
  | none => rfl
  | some a => cases a <;> rfl

/-- The diagonals of `F`: `(i, j)` and those of the two polygons of the cut. -/
private def mol_eqvFun (i j : Fin k) (F : Finset (Fin k × Fin k)) (hdF : (i, j) ∈ F) :
    Option (↥(mol_splitL i j F) ⊕ ↥(mol_splitR i j F)) → ↥F
  | none => ⟨(i, j), hdF⟩
  | some (Sum.inl a) => mol_ιL i j F a
  | some (Sum.inr b) => mol_ιR i j F b

private lemma mol_eqvFun_bij {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) :
    Function.Bijective (mol_eqvFun i j F hdF) := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hFL := mol_splitL_mem hd hF
  have hFR := mol_splitR_mem hd hF
  rw [mol_mem_dissections] at hFL hFR
  have hj := j.isLt
  constructor
  · intro o o' h
    rcases o with _ | a | b <;> rcases o' with _ | a' | b'
    · rfl
    · exfalso
      have := ((mol_mem_splitL _).mp a'.2).2
      exact this (congrArg Subtype.val h).symm
    · exfalso
      have := ((mol_mem_splitR _).mp b'.2).2
      exact this (congrArg Subtype.val h).symm
    · exfalso
      have := ((mol_mem_splitL _).mp a.2).2
      exact this (congrArg Subtype.val h)
    · have h1 := congrArg Subtype.val h
      simp only [mol_eqvFun, mol_ιL, Prod.mk.injEq] at h1
      have e1 := mol_vL_inj hij h1.1
      have e2 := mol_vL_inj hij h1.2
      rw [Subtype.ext (Prod.ext e1 e2)]
    · exfalso
      have h1 := congrArg Subtype.val h
      simp only [mol_eqvFun, mol_ιL, mol_ιR, Prod.mk.injEq] at h1
      have ha := (mol_mem_polyDiags _).mp (hFL.1 a.2)
      have f1 := congrArg Fin.val h1.1
      have f2 := congrArg Fin.val h1.2
      have ca1 := mol_vL_cases i j a.1.1
      have ca2 := mol_vL_cases i j a.1.2
      have hne := mol_prod_ne ((mol_mem_splitL _).mp a.2).2
      simp only [mol_vR_val] at f1 f2
      simp only at hne
      have := a.1.1.isLt; have := a.1.2.isLt; have := b'.1.1.isLt; have := b'.1.2.isLt
      omega
    · exfalso
      have := ((mol_mem_splitR _).mp b.2).2
      exact this (congrArg Subtype.val h)
    · exfalso
      have h1 := congrArg Subtype.val h
      simp only [mol_eqvFun, mol_ιL, mol_ιR, Prod.mk.injEq] at h1
      have ha := (mol_mem_polyDiags _).mp (hFL.1 a'.2)
      have f1 := congrArg Fin.val h1.1
      have f2 := congrArg Fin.val h1.2
      have ca1 := mol_vL_cases i j a'.1.1
      have ca2 := mol_vL_cases i j a'.1.2
      have hne := mol_prod_ne ((mol_mem_splitL _).mp a'.2).2
      simp only [mol_vR_val] at f1 f2
      simp only at hne
      have := a'.1.1.isLt; have := a'.1.2.isLt; have := b.1.1.isLt; have := b.1.2.isLt
      omega
    · have h1 := congrArg Subtype.val h
      simp only [mol_eqvFun, mol_ιR, Prod.mk.injEq] at h1
      have e1 := mol_vR_inj h1.1
      have e2 := mol_vR_inj h1.2
      rw [Subtype.ext (Prod.ext e1 e2)]
  · intro e
    by_cases he : e.1 = (i, j)
    · exact ⟨none, Subtype.ext he.symm⟩
    rcases mol_cover hF hdF e.2 he with h | h
    · refine ⟨some (Sum.inl ⟨(mol_uL i j e.1.1, mol_uL i j e.1.2), ?_⟩), ?_⟩
      · rw [mol_mem_splitL]
        simp only [mol_vL_uL h.1, mol_vL_uL h.2]
        exact ⟨e.2, he⟩
      · apply Subtype.ext
        simp only [mol_eqvFun, mol_ιL, mol_vL_uL h.1, mol_vL_uL h.2]
    · refine ⟨some (Sum.inr ⟨(mol_uR i j e.1.1, mol_uR i j e.1.2), ?_⟩), ?_⟩
      · rw [mol_mem_splitR]
        simp only [mol_vR_uR h.1, mol_vR_uR h.2]
        exact ⟨e.2, he⟩
      · apply Subtype.ext
        simp only [mol_eqvFun, mol_ιR, mol_vR_uR h.1, mol_vR_uR h.2]

/-- The core of `F` in which the link of the diagonal `d` is replaced by the matrix `X`. -/
private def mol_coreX (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (σ : Fin k → Bool)
    (F : Finset (Fin k × Fin k)) (d : Fin k × Fin k) (X : Matrix (Fin L) (Fin L) ℂ)
    (y : Fin k → Fin L) : ℂ :=
  ∑ cIn : ↥F → Fin L, ∑ cOut : ↥F → Fin L,
    (∏ e : ↥F, if e.1 = d then X (cOut e) (cIn e)
      else ((β * t : ℝ) : ℂ) * pairV β M t (σ e.1.1) (σ e.1.2) (cOut e) (cIn e)) *
      ∏ v : Fin k, ∏ p ∈ polyCorners F v,
        sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)

/-- The link `X` of `(i, j)` glues the cores of the two polygons of the cut. -/
private lemma mol_coreX_split {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {t : ℝ}
    {σ : Fin k → Bool} {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {F : Finset (Fin k × Fin k)}
    (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) (X : Matrix (Fin L) (Fin L) ℂ)
    (y : Fin k → Fin L) :
    mol_coreX β M t σ F (i, j) X y =
      ∑ xo : Fin L, ∑ xi : Fin L,
        X xo xi *
          dissCore β M t (cutLSgn σ i j) (mol_splitL i j F)
            (fun p => if p.val = i.val then xo else y (mol_vL i j p)) *
          dissCore β M t (cutRSgn σ i j) (mol_splitR i j F)
            (fun q => if q.val = j.val - i.val then xi else y (mol_vR i j q)) := by
  set e := Equiv.ofBijective _ (mol_eqvFun_bij hd hF hdF) with he_def
  have he0 : e none = ⟨(i, j), hdF⟩ := rfl
  have heL : ∀ a, e (some (Sum.inl a)) = mol_ιL i j F a := fun a => rfl
  have heR : ∀ b, e (some (Sum.inr b)) = mol_ιR i j F b := fun b => rfl
  have hs0 : e.symm ⟨(i, j), hdF⟩ = none := by rw [← he0, Equiv.symm_apply_apply]
  have hsL : ∀ a, e.symm (mol_ιL i j F a) = some (Sum.inl a) := fun a => by
    rw [← heL, Equiv.symm_apply_apply]
  have hsR : ∀ b, e.symm (mol_ιR i j F b) = some (Sum.inr b) := fun b => by
    rw [← heR, Equiv.symm_apply_apply]
  have hL : ∀ a : ↥(mol_splitL i j F), ¬(mol_ιL i j F a).1 = (i, j) :=
    fun a => ((mol_mem_splitL _).mp a.2).2
  have hR : ∀ b : ↥(mol_splitR i j F), ¬(mol_ιR i j F b).1 = (i, j) :=
    fun b => ((mol_mem_splitR _).mp b.2).2
  unfold mol_coreX
  rw [mol_sum_pair, mol_sum_option e, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun xo _ => Finset.sum_congr rfl fun xi _ => ?_
  unfold dissCore
  rw [mol_sum_pair, mol_sum_pair, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mol_corners_split hd hF hdF M σ y]
  rw [← e.prod_comp, Fintype.prod_option, Fintype.prod_sum_type]
  simp only [he0, heL, heR, hs0, hsL, hsR, Option.elim, Sum.elim_inl,
    Sum.elim_inr, ite_true, hL, hR, ite_false]
  have hvL : ∀ a : ↥(mol_splitL i j F),
      (mol_ιL i j F a).1 = (mol_vL i j a.1.1, mol_vL i j a.1.2) := fun a => rfl
  have hvR : ∀ b : ↥(mol_splitR i j F),
      (mol_ιR i j F b).1 = (mol_vR i j b.1.1, mol_vR i j b.1.2) := fun b => rfl
  simp only [hvL, hvR, mol_cutLSgn_eq, mol_cutRSgn_eq]
  ring

/-- The core of a dissection containing `(i, j)` is the core with the link `βtV` of `(i, j)`
written as the matrix `X`. -/
private lemma mol_dissCore_eq_coreX {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {t : ℝ}
    {σ : Fin k → Bool} {i j : Fin k} {F : Finset (Fin k × Fin k)} (y : Fin k → Fin L) :
    dissCore β M t σ F y =
      mol_coreX β M t σ F (i, j) (((β * t : ℝ) : ℂ) • pairV β M t (σ i) (σ j)) y := by
  unfold dissCore mol_coreX
  refine Finset.sum_congr rfl fun cIn _ => Finset.sum_congr rfl fun cOut _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun e _ => ?_
  split_ifs with h
  · rw [Matrix.smul_apply, smul_eq_mul, h]
  · rfl

end Glue

/-! ## The external labels of the two polygons of a cut -/

section Sides

variable {k L : ℕ}

/-- The side `i` of the polygon of Cut_L. -/
private def mol_iL (i j : Fin k) : Fin (k + i - j + 1) := ⟨i.val, by have := j.isLt; omega⟩

/-- The last side of the polygon of Cut_R. -/
private def mol_lastR (i j : Fin k) : Fin (j - i + 1) := ⟨j.val - i.val, by omega⟩

private lemma mol_vL_rot {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {p : Fin (k + i - j + 1)}
    (hp : p.val ≠ i.val) : mol_vL i j (finRotate _ p) = finRotate k (mol_vL i j p) := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have := p.isLt; have := j.isLt
  apply Fin.ext
  rw [mol_finRotate_val, mol_vL_val, mol_vL_val, mol_finRotate_val]
  split_ifs <;> omega

private lemma mol_vL_rot_iL {i j : Fin k} (hd : (i, j) ∈ polyDiags k) :
    mol_vL i j (finRotate _ (mol_iL i j)) = j := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have := j.isLt
  have hr : (finRotate _ (mol_iL i j)).val = i.val + 1 := by
    have h1 := mol_finRotate_val (mol_iL i j)
    have h0 : (mol_iL i j).val = i.val := rfl
    split_ifs at h1 <;> omega
  have h2 := mol_vL_cases i j (finRotate _ (mol_iL i j))
  apply Fin.ext
  omega

private lemma mol_vR_rot {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {q : Fin (j - i + 1)}
    (hq : q.val ≠ j.val - i.val) : mol_vR i j (finRotate _ q) = finRotate k (mol_vR i j q) := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have := q.isLt; have := j.isLt
  apply Fin.ext
  rw [mol_finRotate_val, mol_vR_val, mol_vR_val, mol_finRotate_val]
  split_ifs <;> omega

private lemma mol_vR_rot_lastR {i j : Fin k} (hd : (i, j) ∈ polyDiags k) :
    mol_vR i j (finRotate _ (mol_lastR i j)) = i := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  apply Fin.ext
  rw [mol_vR_val, mol_finRotate_val]
  simp only [mol_lastR]
  split_ifs <;> omega



/-- The external pre-labels of `F` and the two copies of the label of `(i, j)` are the external
pre-labels of the two polygons of the cut. -/
private lemma mol_sum_labels {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    (G : (Fin (k + i - j + 1) → Fin L) → (Fin (j - i + 1) → Fin L) → ℂ) :
    ∑ zL : Fin (k + i - j + 1) → Fin L, ∑ zR : Fin (j - i + 1) → Fin L, G zL zR =
      ∑ y : Fin k → Fin L, ∑ xo : Fin L, ∑ xi : Fin L,
        G (fun p => if p.val = i.val then xo else y (mol_vL i j p))
          (fun q => if q.val = j.val - i.val then xi else y (mol_vR i j q)) := by
  have hdv := (mol_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hj := j.isLt
  let E : (Fin k → Fin L) × (Fin L × Fin L) ≃
      (Fin (k + i - j + 1) → Fin L) × (Fin (j - i + 1) → Fin L) :=
    { toFun := fun x => (fun p => if p.val = i.val then x.2.1 else x.1 (mol_vL i j p),
        fun q => if q.val = j.val - i.val then x.2.2 else x.1 (mol_vR i j q))
      invFun := fun z => (fun s => if s.val < i.val ∨ j.val ≤ s.val then z.1 (mol_uL i j s)
          else z.2 (mol_uR i j s), (z.1 (mol_iL i j), z.2 (mol_lastR i j)))
      left_inv := by
        rintro ⟨y, xo, xi⟩
        simp only [mol_iL, mol_lastR, ite_true, Prod.mk.injEq, and_true]
        funext s
        by_cases hs : s.val < i.val ∨ j.val ≤ s.val
        · rw [ite_eq_left hs]
          have : (mol_uL i j s).val ≠ i.val := by
            rw [mol_uL_val]; split_ifs <;> omega
          rw [ite_eq_right this, mol_vL_uL (by omega)]
        · rw [ite_eq_right hs]
          have : (mol_uR i j s).val ≠ j.val - i.val := by
            rw [mol_uR_val]; split_ifs <;> omega
          rw [ite_eq_right this, mol_vR_uR (by omega)]
      right_inv := by
        rintro ⟨zL, zR⟩
        simp only [Prod.mk.injEq]
        constructor
        · funext p
          by_cases hp : p.val = i.val
          · rw [ite_eq_left hp]
            congr 1
            exact Fin.ext hp.symm
          · rw [ite_eq_right hp]
            have cp := mol_vL_cases i j p
            have hs : (mol_vL i j p).val < i.val ∨ j.val ≤ (mol_vL i j p).val := by omega
            rw [ite_eq_left hs, mol_uL_vL hij]
        · funext q
          by_cases hq : q.val = j.val - i.val
          · rw [ite_eq_left hq]
            congr 1
            exact Fin.ext hq.symm
          · rw [ite_eq_right hq]
            have := q.isLt
            have hs : ¬((mol_vR i j q).val < i.val ∨ j.val ≤ (mol_vR i j q).val) := by
              rw [mol_vR_val]; omega
            rw [ite_eq_right hs, mol_uR_vR] }
  rw [← Fintype.sum_prod_type', ← E.sum_comp, Fintype.sum_prod_type, Fintype.sum_congr]
  intro y
  rw [Fintype.sum_prod_type]
  rfl

end Sides

/-! ## Relabelling of the physical labels -/

section Relabel

/-- `(1 - cX)⁻¹` is invariant under a relabelling that leaves `X` invariant. -/
private lemma mol_oneSub_inv_submatrix {R : Type*} [CommRing R] {L : ℕ} (e : Fin L ≃ Fin L)
    {X : Matrix (Fin L) (Fin L) R} (hX : X.submatrix e e = X) (c : R) :
    ((1 - c • X)⁻¹).submatrix e e = (1 - c • X)⁻¹ := by
  have h1 : (1 - c • X).submatrix e e = 1 - c • X := by
    ext x y
    have := congrFun (congrFun hX x) y
    simp only [Matrix.submatrix_apply] at this
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      e.injective.eq_iff, this]
  rw [← Matrix.inv_submatrix_equiv, h1]

/-- `P` is invariant when `M` is. -/
private lemma mol_pairP_submatrix {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (e : Fin L ≃ Fin L) (hM : ∀ x y, M (e x) (e y) = M x y) :
    (pairP β M).submatrix e e = pairP β M := by
  ext x y
  simp only [Matrix.submatrix_apply, pairP, Matrix.of_apply, hM]

/-- `Q` is invariant when `M` is. -/
private lemma mol_pairQ_submatrix {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (e : Fin L ≃ Fin L) (hM : ∀ x y, M (e x) (e y) = M x y) :
    (pairQ β M).submatrix e e = pairQ β M := by
  ext x y
  simp only [Matrix.submatrix_apply, pairQ, Matrix.of_apply, hM]

/-- The one-label inverses are invariant when `M` is. -/
private lemma mol_pairV_submatrix {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (e : Fin L ≃ Fin L) (hM : ∀ x y, M (e x) (e y) = M x y) (t : ℝ) (s s' : Bool) :
    (pairV β M t s s').submatrix e e = pairV β M t s s' := by
  have hQ := mol_oneSub_inv_submatrix e (mol_pairQ_submatrix β e hM) (t : ℂ)
  have hP := mol_oneSub_inv_submatrix e (mol_pairP_submatrix β e hM) t
  unfold pairV
  split_ifs
  · exact hQ
  · rw [Matrix.submatrix_map, hQ]
  · rw [Matrix.submatrix_map, hP]

/-- `M^s` is invariant when `M` is. -/
private lemma mol_sgnMat_equiv {L : ℕ} {M : Matrix (Fin L) (Fin L) ℂ} (e : Fin L ≃ Fin L)
    (hM : ∀ x y, M (e x) (e y) = M x y) (s : Bool) (x y : Fin L) :
    sgnMat M s (e x) (e y) = sgnMat M s x y := by
  cases s <;> simp [sgnMat, Matrix.conjTranspose_apply, hM]

/-- Entries of the one-label inverses are invariant. -/
private lemma mol_pairV_equiv {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (e : Fin L ≃ Fin L) (hM : ∀ x y, M (e x) (e y) = M x y) (t : ℝ) (s s' : Bool) (x y : Fin L) :
    pairV β M t s s' (e x) (e y) = pairV β M t s s' x y :=
  congrFun (congrFun (mol_pairV_submatrix β e hM t s s') x) y

/-- A relabelling commutes with the edge labels. -/
private lemma mol_edgeLab_equiv {L k : ℕ} (e : Fin L ≃ Fin L) (F : Finset (Fin k × Fin k))
    (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L) (v w : Fin k) (small : Bool) :
    edgeLab F (fun i => e (y i)) (fun d => e (cIn d)) (fun d => e (cOut d)) v w small =
      e (edgeLab F y cIn cOut v w small) := by
  unfold edgeLab
  split_ifs <;> rfl

/-- The core of a dissection is invariant under a relabelling of the external labels. -/
private lemma mol_dissCore_equiv {L k : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (e : Fin L ≃ Fin L) (hM : ∀ x y, M (e x) (e y) = M x y) (t : ℝ) (σ : Fin k → Bool)
    (F : Finset (Fin k × Fin k)) (y : Fin k → Fin L) :
    dissCore β M t σ F (fun i => e (y i)) = dissCore β M t σ F y := by
  unfold dissCore
  symm
  refine Fintype.sum_equiv (Equiv.piCongrRight fun _ : ↥F => e) _ _ (fun cIn => ?_)
  refine Fintype.sum_equiv (Equiv.piCongrRight fun _ : ↥F => e) _ _ (fun cOut => ?_)
  have hE : ∀ c : ↥F → Fin L, (Equiv.piCongrRight fun _ : ↥F => e) c = fun d => e (c d) :=
    fun c => rfl
  simp only [hE, mol_edgeLab_equiv, mol_sgnMat_equiv e hM, mol_pairV_equiv β e hM]

/-- `cycleAdj L` is the adjacency of `a ↦ a + 1` on `Fin L`. -/
private lemma mol_cycleAdj_eq {L : ℕ} [NeZero L] (a b : Fin L) :
    cycleAdj L a b = (if b = a + 1 then 1 else 0) + (if a = b + 1 then 1 else 0) := by
  have h1 : ∀ x : Fin L, (x + 1).val = (x.val + 1) % L := by
    intro x
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  simp only [cycleAdj, Matrix.of_apply, Fin.ext_iff, h1]

/-- The cycle adjacency is invariant under translations. -/
private lemma mol_cycleAdj_add {L : ℕ} [NeZero L] (c a b : Fin L) :
    cycleAdj L (a + c) (b + c) = cycleAdj L a b := by
  have h1 : ∀ x y : Fin L, (y + c = x + c + 1) ↔ (y = x + 1) := by
    intro x y
    rw [add_right_comm x c 1, add_left_inj]
  rw [mol_cycleAdj_eq, mol_cycleAdj_eq]
  simp only [h1]

/-- Negation exchanges the two neighbours. -/
private lemma mol_neg_iff {L : ℕ} [NeZero L] (a b : Fin L) : (-b = -a + 1) ↔ (a = b + 1) := by
  constructor
  · intro h
    calc a = a + -b + b := by abel
      _ = a + (-a + 1) + b := by rw [h]
      _ = b + 1 := by abel
  · intro h
    rw [h]
    abel

/-- The cycle adjacency is invariant under the reflection `a ↦ -a`. -/
private lemma mol_cycleAdj_neg {L : ℕ} [NeZero L] (a b : Fin L) :
    cycleAdj L (-a) (-b) = cycleAdj L a b := by
  rw [mol_cycleAdj_eq, mol_cycleAdj_eq, add_comm]
  simp only [mol_neg_iff]

/-- `M_B` is invariant under a relabelling that leaves the cycle adjacency invariant. -/
private lemma mol_dysonMat_equiv {L : ℕ} (e : Fin L ≃ Fin L)
    (hA : ∀ x y, cycleAdj L (e x) (e y) = cycleAdj L x y) (b β : ℝ) (z m : ℂ) (x y : Fin L) :
    dysonMat b β L z m (e x) (e y) = dysonMat b β L z m x y := by
  have h : (dysonMat b β L z m).submatrix e e = dysonMat b β L z m := by
    unfold dysonMat
    rw [← Matrix.inv_submatrix_equiv]
    congr 1
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      e.injective.eq_iff, hA]
  exact congrFun (congrFun h x) y

/-- The core of a dissection of the model is invariant under the translations of the labels. -/
private lemma mol_dissCore_add (g : ℝ) {L : ℕ} [NeZero L] (E : ℝ) (m : ℂ) (t : ℝ) {k : ℕ}
    (σ : Fin k → Bool) (F : Finset (Fin k × Fin k)) (y : Fin k → Fin L) (c : Fin L) :
    dissCore (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ F (fun i => y i + c) =
      dissCore (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ F y :=
  mol_dissCore_equiv _ (Equiv.addRight c)
    (mol_dysonMat_equiv (Equiv.addRight c) (fun x y => mol_cycleAdj_add c x y) _ _ _ _) t σ F y

/-- The core of a dissection of the model is invariant under the reflection of the labels. -/
private lemma mol_dissCore_neg (g : ℝ) {L : ℕ} [NeZero L] (E : ℝ) (m : ℂ) (t : ℝ) {k : ℕ}
    (σ : Fin k → Bool) (F : Finset (Fin k × Fin k)) (y : Fin k → Fin L) :
    dissCore (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ F (fun i => -y i) =
      dissCore (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ F y :=
  mol_dissCore_equiv _ (Equiv.neg (Fin L))
    (mol_dysonMat_equiv (Equiv.neg (Fin L)) (fun x y => mol_cycleAdj_neg x y) _ _ _ _) t σ F y

end Relabel

/-- Translation and reflection invariance of the stable molecules. -/
theorem stableMol_symm (g : ℝ) (L : ℕ) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (t : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (y : Fin k → Fin L) (c : Fin L) :
    stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ (fun i => y i + c) =
        stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y ∧
      stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ (fun i => -y i) =
        stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y := by
  have _ := hm
  have : NeZero L := ⟨by omega⟩
  exact ⟨Finset.sum_congr rfl fun F _ => mol_dissCore_add g E m t σ F y c,
    Finset.sum_congr rfl fun F _ => mol_dissCore_neg g E m t σ F y⟩

/-! ## Cyclic distances and geometric sums -/

section Dist

private lemma mol_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- Cyclic distance is symmetric. -/
lemma mol_cycDist_comm {L : ℕ} (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

/-- Cyclic distance of a point to itself is `0`. -/
lemma mol_cycDist_self {L : ℕ} (a : Fin L) : cycDist a a = 0 := by
  simp [cycDist]

/-- The cyclic distance satisfies the triangle inequality. -/
private lemma mol_cycDist_tri {L : ℕ} (a b c : Fin L) :
    cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [cycDist, mol_mod ha hb, mol_mod hb ha, mol_mod ha hc, mol_mod hc ha,
    mol_mod hb hc, mol_mod hc hb]
  split_ifs <;> omega

/-- Two labels of a word are within its diameter. -/
private lemma mol_le_wordDiam {L k : ℕ} (y : Fin k → Fin L) (i j : Fin k) :
    cycDist (y i) (y j) ≤ wordDiam y :=
  Finset.le_sup (f := fun p : Fin k × Fin k => cycDist (y p.1) (y p.2)) (Finset.mem_univ (i, j))

/-- A word within `R` of a point has diameter at most `2R`. -/
private lemma mol_wordDiam_le {L k : ℕ} (y : Fin k → Fin L) (b : Fin L) (R : ℕ)
    (h : ∀ i, cycDist (y i) b ≤ R) : wordDiam y ≤ 2 * R := by
  refine Finset.sup_le fun p _ => ?_
  have h1 := mol_cycDist_tri (y p.1) b (y p.2)
  rw [mol_cycDist_comm b] at h1
  have := h p.1
  have := h p.2
  omega

/-- `e^{-c min(u, v)} ≤ e^{-cu} + e^{-cv}`. -/
private lemma mol_exp_min (c a : ℝ) (u v : ℕ) :
    Real.exp (-(c * ((min u v : ℕ) : ℝ) / a)) ≤
      Real.exp (-(c * (u : ℝ) / a)) + Real.exp (-(c * (v : ℝ) / a)) := by
  rcases min_choice u v with h | h <;> rw [h]
  · linarith [Real.exp_pos (-(c * (v : ℝ) / a))]
  · linarith [Real.exp_pos (-(c * (u : ℝ) / a))]

/-- `Σ_{n < L} e^{-cn/a} ≤ 1 + a/c`. -/
private lemma mol_geom_range (L : ℕ) {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∑ z : Fin L, Real.exp (-(c * (z.val : ℝ) / a)) ≤ 1 + a / c := by
  set r := Real.exp (-(c / a)) with hr
  have hx : 0 < c / a := div_pos hc ha
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r * (1 + c / a) ≤ 1 := by
    have h := Real.add_one_le_exp (c / a)
    have h2 : r * Real.exp (c / a) = 1 := by rw [hr, ← Real.exp_add]; simp
    nlinarith
  have hr1' : r < 1 := by nlinarith
  have hterm : ∀ z : Fin L, Real.exp (-(c * (z.val : ℝ) / a)) = r ^ z.val := by
    intro z
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun z _ => hterm z,
    Fin.sum_univ_eq_sum_range (fun n => r ^ n) L]
  have hgeom := mul_neg_geom_sum r L
  have hS : 0 ≤ ∑ i ∈ Finset.range L, r ^ i :=
    Finset.sum_nonneg fun i _ => pow_nonneg hr0.le i
  have hpow : 0 ≤ r ^ L := pow_nonneg hr0.le L
  have h1 : (1 - r) * ∑ i ∈ Finset.range L, r ^ i ≤ 1 := by rw [hgeom]; linarith
  have h2 : (c / a) / (1 + c / a) ≤ 1 - r := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h3 : (c / a) / (1 + c / a) * ∑ i ∈ Finset.range L, r ^ i ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right h2 hS) h1
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h3
  have h4 : ∑ i ∈ Finset.range L, r ^ i ≤ (1 + c / a) / (c / a) := by
    rw [le_div_iff₀ hx]; linarith
  calc ∑ i ∈ Finset.range L, r ^ i ≤ (1 + c / a) / (c / a) := h4
    _ = 1 + a / c := by field_simp; ring

/-- The geometric sum `Σ_z e^{-c‖z - b‖_L / a} ≤ 2(1 + 1/c)a` for `a ≥ 1`, uniformly in `L`. -/
lemma mol_geom_sum {L : ℕ} (b : Fin L) {c a : ℝ} (hc : 0 < c) (ha : 1 ≤ a) :
    ∑ z : Fin L, Real.exp (-(c * (cycDist z b : ℝ) / a)) ≤ 2 * (1 + 1 / c) * a := by
  have : NeZero L := ⟨by have := b.isLt; omega⟩
  have ha0 : 0 < a := by linarith
  have hsub : ∀ x y : Fin L, (x + L - y) % L = (x - y).val := by
    intro x y
    rw [Fin.val_sub]
    congr 1
    have := y.isLt
    omega
  have h1 : ∑ z : Fin L, Real.exp (-(c * (((z + L - b) % L : ℕ) : ℝ) / a)) ≤ 1 + a / c := by
    have e : ∑ z : Fin L, Real.exp (-(c * (((z + L - b) % L : ℕ) : ℝ) / a)) =
        ∑ z : Fin L, Real.exp (-(c * (z.val : ℝ) / a)) := by
      refine Fintype.sum_equiv (Equiv.subRight b) _ _ (fun z => ?_)
      rw [hsub]
      rfl
    rw [e]
    exact mol_geom_range L hc ha0
  have h2 : ∑ z : Fin L, Real.exp (-(c * (((b + L - z) % L : ℕ) : ℝ) / a)) ≤ 1 + a / c := by
    have e : ∑ z : Fin L, Real.exp (-(c * (((b + L - z) % L : ℕ) : ℝ) / a)) =
        ∑ z : Fin L, Real.exp (-(c * (z.val : ℝ) / a)) := by
      refine Fintype.sum_equiv (Equiv.subLeft b) _ _ (fun z => ?_)
      rw [hsub]
      rfl
    rw [e]
    exact mol_geom_range L hc ha0
  calc ∑ z : Fin L, Real.exp (-(c * (cycDist z b : ℝ) / a))
      ≤ ∑ z : Fin L, (Real.exp (-(c * (((z + L - b) % L : ℕ) : ℝ) / a)) +
          Real.exp (-(c * (((b + L - z) % L : ℕ) : ℝ) / a))) :=
        Finset.sum_le_sum fun z _ => mol_exp_min c a _ _
    _ ≤ (1 + a / c) + (1 + a / c) := by rw [Finset.sum_add_distrib]; linarith
    _ ≤ 2 * (1 + 1 / c) * a := by
        have : a / c ≤ a * (1 / c) := by rw [mul_one_div]
        nlinarith [div_pos one_pos hc]

/-- Anchored sums of the profile: on `y v = b`, the weight `e^{-c diam(y)/a}` sums to at most
`(2(1 + k/c)a)^{k-1}`. -/
lemma mol_anchor_sum {L k : ℕ} (v : Fin k) (b : Fin L) {c a : ℝ} (hc : 0 < c)
    (ha : 1 ≤ a) :
    ∑ y ∈ Finset.univ.filter (fun y : Fin k → Fin L => y v = b),
        Real.exp (-(c * wordDiam y / a)) ≤ (2 * (1 + k / c) * a) ^ (k - 1) := by
  have hk : 0 < k := Fin.pos v
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have ha0 : 0 < a := by linarith
  set f : Fin L → ℝ := fun z => Real.exp (-(c / k * (cycDist z b : ℝ) / a)) with hf
  have hpt : ∀ y : Fin k → Fin L, y v = b →
      Real.exp (-(c * wordDiam y / a)) ≤ ∏ i, f (y i) := by
    intro y hy
    rw [hf, ← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    have hsum : ∑ i, (cycDist (y i) b : ℝ) ≤ k * wordDiam y := by
      have : ∀ i, (cycDist (y i) b : ℝ) ≤ wordDiam y := fun i => by
        have := mol_le_wordDiam y i v
        rw [hy] at this
        exact_mod_cast this
      calc ∑ i, (cycDist (y i) b : ℝ) ≤ ∑ _i : Fin k, (wordDiam y : ℝ) :=
            Finset.sum_le_sum fun i _ => this i
        _ = k * wordDiam y := by simp
    have e : ∑ i, -(c / k * (cycDist (y i) b : ℝ) / a) =
        -(c / k / a * ∑ i, (cycDist (y i) b : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [e, neg_le_neg_iff]
    calc c / k / a * ∑ i, (cycDist (y i) b : ℝ) ≤ c / k / a * (k * wordDiam y) := by
          gcongr
      _ = c * wordDiam y / a := by field_simp
  set t : Fin k → Finset (Fin L) := fun i => if i = v then {b} else Finset.univ with ht
  have hfil : Finset.univ.filter (fun y : Fin k → Fin L => y v = b) = Fintype.piFinset t := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, ht]
    constructor
    · intro hy i
      split_ifs with h
      · subst h; simp [hy]
      · exact Finset.mem_univ _
    · intro h
      have := h v
      simpa using this
  calc ∑ y ∈ Finset.univ.filter (fun y : Fin k → Fin L => y v = b),
        Real.exp (-(c * wordDiam y / a))
      ≤ ∑ y ∈ Finset.univ.filter (fun y : Fin k → Fin L => y v = b), ∏ i, f (y i) :=
        Finset.sum_le_sum fun y hy => hpt y (Finset.mem_filter.mp hy).2
    _ = ∏ i, ∑ z ∈ t i, f z := by rw [hfil, Finset.prod_univ_sum]
    _ = ∏ i ∈ Finset.univ.erase v, ∑ z : Fin L, f z := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
        have h1 : ∑ z ∈ t v, f z = 1 := by simp [ht, hf, mol_cycDist_self]
        rw [h1, one_mul]
        refine Finset.prod_congr rfl fun i hi => ?_
        have : i ≠ v := (Finset.mem_erase.mp hi).1
        simp [ht, this]
    _ ≤ ∏ _i ∈ Finset.univ.erase v, (2 * (1 + k / c) * a) := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun z _ => (Real.exp_pos _).le)
          fun i _ => ?_
        have := mol_geom_sum (L := L) b (c := c / k) (a := a) (by positivity) ha
        simp only [hf]
        convert this using 2
        field_simp
    _ = (2 * (1 + k / c) * a) ^ (k - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
          Fintype.card_fin]

/-- Full sums of the profile: `Σ_y e^{-c diam(y)/a} ≤ L(2(1 + k/c)a)^{k-1}`. -/
lemma mol_full_sum {L k : ℕ} (hk : 0 < k) {c a : ℝ} (hc : 0 < c) (ha : 1 ≤ a) :
    ∑ y : Fin k → Fin L, Real.exp (-(c * wordDiam y / a)) ≤
      L * (2 * (1 + k / c) * a) ^ (k - 1) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun y : Fin k → Fin L => y ⟨0, hk⟩)]
  calc ∑ b : Fin L, ∑ y ∈ Finset.univ.filter (fun y : Fin k → Fin L => y ⟨0, hk⟩ = b),
        Real.exp (-(c * wordDiam y / a))
      ≤ ∑ _b : Fin L, (2 * (1 + k / c) * a) ^ (k - 1) :=
        Finset.sum_le_sum fun b _ => mol_anchor_sum ⟨0, hk⟩ b hc ha
    _ = L * (2 * (1 + k / c) * a) ^ (k - 1) := by simp

end Dist

/-! ## Connectivity of the dissection graph

The labels of a dissection (the external labels and the two copies of every diagonal label) are
joined by the face corners and the links. Every label lies within `3k²` times the total length
of the corners and links from the label `y_0`. -/

section Connect

variable {k L : ℕ}

/-- The total length of the links and the face corners of a labelled dissection. -/
def mol_tot (F : Finset (Fin k × Fin k)) (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L) :
    ℕ :=
  (∑ d : ↥F, cycDist (cOut d) (cIn d)) +
    ∑ v : Fin k, ∑ p ∈ polyCorners F v,
      cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)

private lemma mol_corner_le {F : Finset (Fin k × Fin k)} (y : Fin k → Fin L)
    (cIn cOut : ↥F → Fin L) {v : Fin k} {p : Fin k × Fin k} (hp : p ∈ polyCorners F v) :
    cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) ≤
      mol_tot F y cIn cOut := by
  set f : Fin k → Fin k × Fin k → ℕ := fun v p =>
    cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) with hf
  have h1 : f v p ≤ ∑ q ∈ polyCorners F v, f v q :=
    Finset.single_le_sum (f := f v) (fun _ _ => Nat.zero_le _) hp
  have h2 : ∑ q ∈ polyCorners F v, f v q ≤ ∑ w, ∑ q ∈ polyCorners F w, f w q :=
    Finset.single_le_sum (f := fun w => ∑ q ∈ polyCorners F w, f w q)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  have h3 : mol_tot F y cIn cOut = (∑ d : ↥F, cycDist (cOut d) (cIn d)) +
      ∑ w, ∑ q ∈ polyCorners F w, f w q := rfl
  change f v p ≤ _
  omega

private lemma mol_link_le {F : Finset (Fin k × Fin k)} (y : Fin k → Fin L)
    (cIn cOut : ↥F → Fin L) (d : ↥F) : cycDist (cOut d) (cIn d) ≤ mol_tot F y cIn cOut := by
  unfold mol_tot
  exact le_add_right (Finset.single_le_sum (f := fun d => cycDist (cOut d) (cIn d))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ d))

/-- The two labels of an edge seen from its two sides are within the total length. -/
private lemma mol_edge_le {F : Finset (Fin k × Fin k)} (y : Fin k → Fin L)
    (cIn cOut : ↥F → Fin L) (v w : Fin k) :
    cycDist (edgeLab F y cIn cOut v w false) (edgeLab F y cIn cOut v w true) ≤
      mol_tot F y cIn cOut := by
  unfold edgeLab
  by_cases h : (min v w, max v w) ∈ F
  · simp only [h, ↓reduceDIte]
    split_ifs <;> first
      | exact mol_link_le y cIn cOut _
      | (rw [mol_cycDist_comm]; exact mol_link_le y cIn cOut _)
      | (rw [mol_cycDist_self]; exact Nat.zero_le _)
  · simp only [h, ↓reduceDIte, mol_cycDist_self]
    exact Nat.zero_le _

/-- A side of the polygon is not a diagonal. -/
lemma mol_side_not_mem {F : Finset (Fin k × Fin k)} (hF : F ⊆ polyDiags k)
    {v w : Fin k} (h : polyOff v w = 1 ∨ polyOff v w + 1 = k) : (min v w, max v w) ∉ F := by
  intro hm
  have h1 := (mol_mem_polyDiags _).mp (hF hm)
  have := v.isLt
  have := w.isLt
  rw [mol_polyOff_eq] at h
  rcases le_total v w with hle | hle
  · rw [min_eq_left hle, max_eq_right hle] at h1
    rw [Fin.le_def] at hle
    simp only at h1
    split_ifs at h
    omega
  · rw [min_eq_right hle, max_eq_left hle] at h1
    rw [Fin.le_def] at hle
    simp only at h1
    split_ifs at h <;> omega

/-- The next vertex has offset `1`. -/
lemma mol_polyOff_rot (hk : 2 ≤ k) (v : Fin k) : polyOff v (finRotate k v) = 1 := by
  rw [mol_polyOff_eq, mol_finRotate_val]
  have := v.isLt
  split_ifs <;> omega

/-- Along the corners at `v`, the label of the edge to the neighbour `w` on the side of the
smaller offsets is within `2 off(v, w)` total lengths of `y_v`. -/
private lemma mol_chain (hk : 3 ≤ k) {F : Finset (Fin k × Fin k)} (hF : F ⊆ polyDiags k)
    (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L) (v : Fin k) :
    ∀ o, ∀ w, PolyNbr F v w → polyOff v w = o →
      cycDist (edgeLab F y cIn cOut v w true) (y v) ≤ 2 * o * mol_tot F y cIn cOut := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
  intro w hw ho
  set T := mol_tot F y cIn cOut
  by_cases h1 : polyOff v w = 1
  · have hs := mol_side_not_mem hF (Or.inl h1)
    unfold edgeLab
    simp only [hs, ↓reduceDIte, h1, ↓reduceIte, mol_cycDist_self]
    exact Nat.zero_le _
  have hwv : w ≠ v := hw.1
  have hpos : 1 ≤ polyOff v w := by
    by_contra h0
    apply hwv
    have := v.isLt
    have := w.isLt
    rw [mol_polyOff_eq] at h0
    apply Fin.ext
    split_ifs at h0 <;> omega
  set S := Finset.univ.filter (fun u => PolyNbr F v u ∧ polyOff v u < polyOff v w) with hS
  have hu0 : finRotate k v ∈ S := by
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ⟨?_, Or.inl (mol_polyOff_rot (by omega) v)⟩, ?_⟩
    · intro h
      have := mol_polyOff_rot (k := k) (by omega) v
      rw [h, mol_polyOff_eq] at this
      simp at this
    · rw [mol_polyOff_rot (by omega) v]; omega
  obtain ⟨u, huS, hmax⟩ := S.exists_max_image (polyOff v) ⟨_, hu0⟩
  rw [hS, Finset.mem_filter] at huS
  have hc : (u, w) ∈ polyCorners F v := by
    rw [mol_mem_polyCorners]
    refine ⟨huS.2.1, hw, huS.2.2, fun u' hu' hb => ?_⟩
    simp only at hb
    have := hmax u' (by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hu', by omega⟩)
    omega
  have hih := ih (polyOff v u) (by omega) u huS.2.1 rfl
  have hA := mol_corner_le y cIn cOut hc
  have hB := mol_edge_le y cIn cOut v u
  have t1 := mol_cycDist_tri (edgeLab F y cIn cOut v w true) (edgeLab F y cIn cOut v u false)
    (y v)
  have t2 := mol_cycDist_tri (edgeLab F y cIn cOut v u false) (edgeLab F y cIn cOut v u true)
    (y v)
  have hlt : polyOff v u + 1 ≤ o := by omega
  simp only at hA
  calc cycDist (edgeLab F y cIn cOut v w true) (y v) ≤ T + T + 2 * polyOff v u * T := by omega
    _ ≤ 2 * o * T := by nlinarith

/-- Consecutive external labels are within `2k` total lengths. -/
private lemma mol_ext_step (hk : 3 ≤ k) {F : Finset (Fin k × Fin k)} (hF : F ⊆ polyDiags k)
    (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L) (i : Fin k) :
    cycDist (y i) (y (finRotate k i)) ≤ 2 * k * mol_tot F y cIn cOut := by
  set u := finRotate k i
  have hoff : polyOff u i + 1 = k := by
    rw [mol_polyOff_eq, mol_finRotate_val]
    have := i.isLt
    split_ifs <;> omega
  have hne : i ≠ u := by
    intro h
    rw [← h, mol_polyOff_eq] at hoff
    simp at hoff
    omega
  have hnbr : PolyNbr F u i := ⟨hne, Or.inr (Or.inl hoff)⟩
  have hs := mol_side_not_mem hF (Or.inr hoff)
  have hlab : edgeLab F y cIn cOut u i true = y i := by
    unfold edgeLab
    simp only [hs, ↓reduceDIte, show polyOff u i ≠ 1 by omega, ↓reduceIte]
  have := mol_chain hk hF y cIn cOut u _ i hnbr rfl
  rw [hlab] at this
  calc cycDist (y i) (y u) ≤ 2 * polyOff u i * mol_tot F y cIn cOut := this
    _ ≤ 2 * k * mol_tot F y cIn cOut := by gcongr; omega

/-- Every external label is within `2k²` total lengths of `y_0`. -/
private lemma mol_ext_le (hk : 3 ≤ k) {F : Finset (Fin k × Fin k)} (hF : F ⊆ polyDiags k)
    (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L) (i : Fin k) :
    cycDist (y i) (y ⟨0, by omega⟩) ≤ 2 * k ^ 2 * mol_tot F y cIn cOut := by
  set T := mol_tot F y cIn cOut
  have key : ∀ n (hn : n < k), cycDist (y ⟨n, hn⟩) (y ⟨0, by omega⟩) ≤ n * (2 * k * T) := by
    intro n
    induction n with
    | zero => intro hn; simp [mol_cycDist_self]
    | succ n ih =>
      intro hn
      have hrot : finRotate k ⟨n, by omega⟩ = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        rw [mol_finRotate_val]
        simp only
        split_ifs <;> omega
      have h1 := mol_ext_step hk hF y cIn cOut ⟨n, by omega⟩
      rw [hrot, mol_cycDist_comm] at h1
      have h2 := ih (by omega)
      have h3 := mol_cycDist_tri (y ⟨n + 1, hn⟩) (y ⟨n, by omega⟩) (y ⟨0, by omega⟩)
      calc cycDist (y ⟨n + 1, hn⟩) (y ⟨0, by omega⟩) ≤ 2 * k * T + n * (2 * k * T) := by
            linarith
        _ = (n + 1) * (2 * k * T) := by ring
  have := key i.val i.isLt
  calc cycDist (y i) (y ⟨0, by omega⟩) ≤ i.val * (2 * k * T) := this
    _ ≤ k * (2 * k * T) := by gcongr; exact i.isLt.le
    _ = 2 * k ^ 2 * T := by ring

/-- Both copies of every diagonal label are within `3k²` total lengths of `y_0`. -/
private lemma mol_int_le (hk : 3 ≤ k) {F : Finset (Fin k × Fin k)} (hF : F ⊆ polyDiags k)
    (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L) (d : ↥F) :
    cycDist (cIn d) (y ⟨0, by omega⟩) ≤ 3 * k ^ 2 * mol_tot F y cIn cOut ∧
      cycDist (cOut d) (y ⟨0, by omega⟩) ≤ 3 * k ^ 2 * mol_tot F y cIn cOut := by
  set T := mol_tot F y cIn cOut
  obtain ⟨⟨i, j⟩, hdF⟩ := d
  have hdv := (mol_mem_polyDiags _).mp (hF hdF)
  simp only at hdv
  have hij : i < j := by rw [Fin.lt_def]; omega
  have hmin : min i j = i := min_eq_left hij.le
  have hmax : max i j = j := max_eq_right hij.le
  have hmem : (min i j, max i j) ∈ F := by rw [hmin, hmax]; exact hdF
  have hnbr : PolyNbr F i j := ⟨fun h => by rw [h] at hij; exact lt_irrefl _ hij,
    Or.inr (Or.inr hmem)⟩
  have hlab : edgeLab F y cIn cOut i j true = cIn ⟨(i, j), hdF⟩ := by
    unfold edgeLab
    simp only [hmem, ↓reduceDIte, hij, decide_true, ↓reduceIte]
    congr 1
    exact Subtype.ext (Prod.ext hmin hmax)
  have h1 := mol_chain hk hF y cIn cOut i _ j hnbr rfl
  rw [hlab] at h1
  have hoff : polyOff i j < k := by
    unfold polyOff; exact Nat.mod_lt _ (by omega)
  have h2 := mol_ext_le hk hF y cIn cOut i
  have h3 := mol_cycDist_tri (cIn ⟨(i, j), hdF⟩) (y i) (y ⟨0, by omega⟩)
  have h4 := mol_link_le y cIn cOut ⟨(i, j), hdF⟩
  have h5 := mol_cycDist_tri (cOut ⟨(i, j), hdF⟩) (cIn ⟨(i, j), hdF⟩) (y ⟨0, by omega⟩)
  have h6 : 2 * polyOff i j * T ≤ 2 * k * T := by gcongr
  have h7 : 2 * k * T + T ≤ k ^ 2 * T := by
    have : 2 * k + 1 ≤ k ^ 2 := by nlinarith
    nlinarith
  constructor
  · calc cycDist (cIn ⟨(i, j), hdF⟩) (y ⟨0, by omega⟩) ≤ 2 * k * T + 2 * k ^ 2 * T := by
          linarith
      _ ≤ 3 * k ^ 2 * T := by linarith
  · calc cycDist (cOut ⟨(i, j), hdF⟩) (y ⟨0, by omega⟩) ≤ T + (2 * k * T + 2 * k ^ 2 * T) := by
          linarith
      _ ≤ 3 * k ^ 2 * T := by linarith

end Connect

/-! ## The exponential profile of a core -/

section Profile

variable {k L : ℕ}

/-- The total length controls the diameter and the diagonal labels: with
`R = 3k²`, `diam(y) ≤ 2R·tot` and `Σ_d ‖cIn_d - y_0‖ ≤ k²R·tot`. -/
lemma mol_tot_bounds (hk : 3 ≤ k) {F : Finset (Fin k × Fin k)} (hF : F ⊆ polyDiags k)
    (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L) :
    (wordDiam y : ℝ) ≤ 6 * k ^ 2 * mol_tot F y cIn cOut ∧
      ∑ d : ↥F, (cycDist (cIn d) (y ⟨0, by omega⟩) : ℝ) ≤
        3 * k ^ 4 * mol_tot F y cIn cOut := by
  constructor
  · have h := mol_wordDiam_le y (y ⟨0, by omega⟩) (3 * k ^ 2 * mol_tot F y cIn cOut) fun i => by
      have h1 := mol_ext_le hk hF y cIn cOut i
      have h2 : 2 * k ^ 2 * mol_tot F y cIn cOut ≤ 3 * k ^ 2 * mol_tot F y cIn cOut := by
        gcongr; omega
      exact h1.trans h2
    have : (wordDiam y : ℝ) ≤ ((2 * (3 * k ^ 2 * mol_tot F y cIn cOut) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at this
    linarith
  · have hcard : (F.card : ℝ) ≤ k ^ 2 := by
      have h := Finset.card_le_univ F
      rw [Fintype.card_prod, Fintype.card_fin] at h
      have : ((F.card : ℕ) : ℝ) ≤ ((k * k : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this
      nlinarith
    calc ∑ d : ↥F, (cycDist (cIn d) (y ⟨0, by omega⟩) : ℝ)
        ≤ ∑ _d : ↥F, (3 * k ^ 2 * mol_tot F y cIn cOut : ℝ) := Finset.sum_le_sum fun d _ => by
          have := (mol_int_le hk hF y cIn cOut d).1
          exact_mod_cast this
      _ = F.card * (3 * k ^ 2 * mol_tot F y cIn cOut) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ ≤ k ^ 2 * (3 * k ^ 2 * mol_tot F y cIn cOut) := by gcongr
      _ = 3 * k ^ 4 * mol_tot F y cIn cOut := by ring

/-- The exponential profile of a core: if every corner is bounded by `Ce^{-c d/a}` and every
link by `e^{-c d/a}K` with column sums of `K` at most `B/a`, then
`‖C_F(y)‖ ≤ C^{N_c}(2(1 + 6k⁴/c)B)^{|F|}e^{-c diam(y)/(12k²a)}`. -/
private lemma mol_core_profile (hk : 3 ≤ k) {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {t : ℝ}
    {σ : Fin k → Bool} {F : Finset (Fin k × Fin k)} (hF : F ⊆ polyDiags k)
    {a c C B : ℝ} (ha : 1 ≤ a) (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hM : ∀ s x z, ‖sgnMat M s x z‖ ≤ C * Real.exp (-(c * cycDist x z / a)))
    (K : ↥F → Fin L → Fin L → ℝ) (hK0 : ∀ d o i, 0 ≤ K d o i)
    (hlink : ∀ (d : ↥F) o i, ‖((β * t : ℝ) : ℂ) * pairV β M t (σ d.1.1) (σ d.1.2) o i‖ ≤
      Real.exp (-(c * cycDist o i / a)) * K d o i)
    (hKrow : ∀ d i, ∑ o, K d o i ≤ B / a) (y : Fin k → Fin L) :
    ‖dissCore β M t σ F y‖ ≤ C ^ (∑ v, (polyCorners F v).card) *
      (2 * (1 + 6 * k ^ 4 / c) * B) ^ F.card *
      Real.exp (-(c / (12 * k ^ 2) * wordDiam y / a)) := by
  have ha0 : 0 < a := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  set y0 := y ⟨0, by omega⟩
  set c₂ := c / (6 * k ^ 4) with hc₂
  have hc₂0 : 0 < c₂ := by positivity
  set E := Real.exp (-(c / (12 * k ^ 2) * wordDiam y / a))
  set Nc := ∑ v, (polyCorners F v).card
  set h : ↥F → Fin L → Fin L → ℝ := fun d i o =>
    Real.exp (-(c₂ * cycDist i y0 / a)) * K d o i with hh
  -- the pointwise bound
  have hpt : ∀ cIn cOut : ↥F → Fin L,
      ‖(∏ d : ↥F, ((β * t : ℝ) : ℂ) * pairV β M t (σ d.1.1) (σ d.1.2) (cOut d) (cIn d)) *
        ∏ v : Fin k, ∏ p ∈ polyCorners F v,
          sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)‖ ≤
        C ^ Nc * E * ∏ d : ↥F, h d (cIn d) (cOut d) := by
    intro cIn cOut
    set T := mol_tot F y cIn cOut
    have hA : ‖∏ d : ↥F, ((β * t : ℝ) : ℂ) * pairV β M t (σ d.1.1) (σ d.1.2) (cOut d) (cIn d)‖ ≤
        Real.exp (-(c * (∑ d : ↥F, (cycDist (cOut d) (cIn d) : ℝ)) / a)) *
          ∏ d : ↥F, K d (cOut d) (cIn d) := by
      rw [norm_prod]
      calc ∏ d : ↥F, ‖((β * t : ℝ) : ℂ) * pairV β M t (σ d.1.1) (σ d.1.2) (cOut d) (cIn d)‖
          ≤ ∏ d : ↥F, (Real.exp (-(c * cycDist (cOut d) (cIn d) / a)) * K d (cOut d) (cIn d)) :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun d _ => hlink d _ _
        _ = _ := by
            rw [Finset.prod_mul_distrib, ← Real.exp_sum]
            congr 2
            rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
    have hB' : ‖∏ v : Fin k, ∏ p ∈ polyCorners F v,
          sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)‖ ≤
        C ^ Nc * Real.exp (-(c * (∑ v : Fin k, ∑ p ∈ polyCorners F v,
          (cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) : ℝ)) /
            a)) := by
      rw [norm_prod]
      calc ∏ v : Fin k, ‖∏ p ∈ polyCorners F v,
            sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)‖
          ≤ ∏ v : Fin k, ∏ p ∈ polyCorners F v, (C * Real.exp (-(c *
              cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) /
                a))) := by
            refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => ?_
            rw [norm_prod]
            exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun p _ => hM _ _ _
        _ = _ := by
            simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
            congr 1
            rw [Finset.prod_congr rfl fun v _ => (Real.exp_sum _ _).symm, ← Real.exp_sum]
            congr 1
            rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
    have htot : (T : ℝ) = (∑ d : ↥F, (cycDist (cOut d) (cIn d) : ℝ)) +
        ∑ v : Fin k, ∑ p ∈ polyCorners F v,
          (cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) : ℝ) := by
      simp only [T, mol_tot]
      push_cast
      rfl
    obtain ⟨hdiam, hint⟩ := mol_tot_bounds hk hF y cIn cOut
    have hexp : Real.exp (-(c * (∑ d : ↥F, (cycDist (cOut d) (cIn d) : ℝ)) / a)) *
        Real.exp (-(c * (∑ v : Fin k, ∑ p ∈ polyCorners F v,
          (cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) : ℝ)) /
            a)) ≤ E * ∏ d : ↥F, Real.exp (-(c₂ * cycDist (cIn d) y0 / a)) := by
      rw [← Real.exp_add, ← Real.exp_sum, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have e1 : ∑ d : ↥F, -(c₂ * (cycDist (cIn d) y0 : ℝ) / a) =
          -(c₂ / a * ∑ d : ↥F, (cycDist (cIn d) y0 : ℝ)) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun d _ => by ring
      rw [e1]
      have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
      have i1 : c / (12 * k ^ 2) * wordDiam y ≤ c / 2 * T := by
        calc c / (12 * k ^ 2) * wordDiam y ≤ c / (12 * k ^ 2) * (6 * k ^ 2 * T) := by gcongr
          _ = c / 2 * T := by field_simp; ring
      have i2 : c₂ * ∑ d : ↥F, (cycDist (cIn d) y0 : ℝ) ≤ c / 2 * T := by
        calc c₂ * ∑ d : ↥F, (cycDist (cIn d) y0 : ℝ) ≤ c₂ * (3 * k ^ 4 * T) := by gcongr
          _ = c / 2 * T := by rw [hc₂]; field_simp; ring
      have e2 : -(c * (∑ d : ↥F, (cycDist (cOut d) (cIn d) : ℝ)) / a) +
          -(c * (∑ v : Fin k, ∑ p ∈ polyCorners F v,
            (cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) : ℝ)) /
              a) = -(c * T / a) := by
        rw [htot]; ring
      rw [e2]
      have : c / (12 * k ^ 2) * wordDiam y / a + c₂ / a * ∑ d : ↥F, (cycDist (cIn d) y0 : ℝ) ≤
          c * T / a := by
        have e3 : c / (12 * k ^ 2) * wordDiam y / a + c₂ / a * ∑ d : ↥F, (cycDist (cIn d) y0 : ℝ) =
            (c / (12 * k ^ 2) * wordDiam y + c₂ * ∑ d : ↥F, (cycDist (cIn d) y0 : ℝ)) / a := by
          ring
        rw [e3]
        apply div_le_div_of_nonneg_right _ ha0.le
        linarith
      linarith
    rw [norm_mul]
    have hK : 0 ≤ ∏ d : ↥F, K d (cOut d) (cIn d) := Finset.prod_nonneg fun d _ => hK0 _ _ _
    calc ‖∏ d : ↥F, ((β * t : ℝ) : ℂ) * pairV β M t (σ d.1.1) (σ d.1.2) (cOut d) (cIn d)‖ *
          ‖∏ v : Fin k, ∏ p ∈ polyCorners F v,
            sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)‖
        ≤ (Real.exp (-(c * (∑ d : ↥F, (cycDist (cOut d) (cIn d) : ℝ)) / a)) *
            ∏ d : ↥F, K d (cOut d) (cIn d)) *
          (C ^ Nc * Real.exp (-(c * (∑ v : Fin k, ∑ p ∈ polyCorners F v,
            (cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) : ℝ)) /
              a))) := mul_le_mul hA hB' (norm_nonneg _) (by positivity)
      _ = C ^ Nc * (Real.exp (-(c * (∑ d : ↥F, (cycDist (cOut d) (cIn d) : ℝ)) / a)) *
          Real.exp (-(c * (∑ v : Fin k, ∑ p ∈ polyCorners F v,
            (cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) : ℝ)) /
              a))) * ∏ d : ↥F, K d (cOut d) (cIn d) := by ring
      _ ≤ C ^ Nc * (E * ∏ d : ↥F, Real.exp (-(c₂ * cycDist (cIn d) y0 / a))) *
          ∏ d : ↥F, K d (cOut d) (cIn d) := by gcongr
      _ = C ^ Nc * E * ∏ d : ↥F, h d (cIn d) (cOut d) := by
          rw [hh]; simp only [Finset.prod_mul_distrib]; ring
  -- summing over the diagonal labels
  have hsum : ∑ cIn : ↥F → Fin L, ∑ cOut : ↥F → Fin L, ∏ d : ↥F, h d (cIn d) (cOut d) =
      ∏ d : ↥F, ∑ i : Fin L, ∑ o : Fin L, h d i o := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun cIn _ => ?_
    rw [← Fintype.prod_sum (fun d o => h d (cIn d) o)]
  have hfac : ∀ d : ↥F, ∑ i : Fin L, ∑ o : Fin L, h d i o ≤ 2 * (1 + 6 * k ^ 4 / c) * B := by
    intro d
    calc ∑ i : Fin L, ∑ o : Fin L, h d i o
        = ∑ i : Fin L, Real.exp (-(c₂ * cycDist i y0 / a)) * ∑ o, K d o i := by
          simp only [hh, Finset.mul_sum]
      _ ≤ ∑ i : Fin L, Real.exp (-(c₂ * cycDist i y0 / a)) * (B / a) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hKrow d i) (Real.exp_pos _).le
      _ = (∑ i : Fin L, Real.exp (-(c₂ * cycDist i y0 / a))) * (B / a) := by
          rw [Finset.sum_mul]
      _ ≤ (2 * (1 + 1 / c₂) * a) * (B / a) := by
          gcongr
          exact mol_geom_sum y0 hc₂0 ha
      _ = 2 * (1 + 6 * k ^ 4 / c) * B := by
          rw [hc₂]; field_simp
  have hh0 : ∀ d i o, 0 ≤ h d i o := fun d i o => mul_nonneg (Real.exp_pos _).le (hK0 _ _ _)
  unfold dissCore
  calc ‖∑ cIn : ↥F → Fin L, ∑ cOut : ↥F → Fin L,
        (∏ d : ↥F, ((β * t : ℝ) : ℂ) * pairV β M t (σ d.1.1) (σ d.1.2) (cOut d) (cIn d)) *
          ∏ v : Fin k, ∏ p ∈ polyCorners F v,
            sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)‖
      ≤ ∑ cIn : ↥F → Fin L, ∑ cOut : ↥F → Fin L, C ^ Nc * E * ∏ d : ↥F, h d (cIn d) (cOut d) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun cIn _ => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun cOut _ => hpt cIn cOut)
    _ = C ^ Nc * E * ∏ d : ↥F, ∑ i : Fin L, ∑ o : Fin L, h d i o := by
        rw [← hsum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun cIn _ => ?_
        rw [Finset.mul_sum]
    _ ≤ C ^ Nc * E * ∏ _d : ↥F, (2 * (1 + 6 * k ^ 4 / c) * B) := by
        have hE : 0 ≤ C ^ Nc * E := by positivity
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun d _ =>
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun o _ => hh0 d i o)
          fun d _ => hfac d) hE
    _ = C ^ Nc * (2 * (1 + 6 * k ^ 4 / c) * B) ^ F.card * E := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]; ring

end Profile

/-! ## The kernel facts at a scale `a` -/

section Hyp

/-- The kernel facts used for the stable molecules of the model at the scale `a ≥ 1`: `M_B` and
the same-sign inverse `(I - tQ)⁻¹` decay at the rate `c/a`, `‖m‖ ≤ C`, `Im m ≥ C⁻¹` and
`γ_g a ≤ 1 ≤ Cγ_g a`. -/
structure MolHyp (g : ℝ) (L : ℕ) (E : ℝ) (m : ℂ) (t a c C : ℝ) : Prop where
  hL : 3 ≤ L
  root : IsDysonRootV (hopB g) (gammaG g) L E m
  ha : 1 ≤ a
  hc : 0 < c
  hC : 1 ≤ C
  ht0 : 0 ≤ t
  ht1 : t ≤ 1
  Mdec : ∀ x z, ‖dysonMat (hopB g) (gammaG g) L E m x z‖ ≤
    C * Real.exp (-(c * cycDist x z / a))
  Vrow : ∀ x, ∑ z, Real.exp (c * cycDist x z / a) *
    ‖(1 - (t : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ x z‖ ≤ C
  m_le : ‖m‖ ≤ C
  im_ge : C⁻¹ ≤ m.im
  beta_le : gammaG g * a ≤ 1
  beta_ge : 1 ≤ C * (gammaG g * a)

/-- The Lean inverse of a symmetric matrix is symmetric. -/
lemma mol_inv_comm {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (X : Matrix n n R) (hX : Xᵀ = X) (x y : n) : X⁻¹ x y = X⁻¹ y x := by
  have h : (X⁻¹)ᵀ = X⁻¹ := by rw [Matrix.transpose_nonsing_inv, hX]
  exact (congrFun (congrFun h x) y).symm

/-- `1 - cX` is symmetric when `X` is. -/
lemma mol_oneSub_transpose {n R : Type*} [DecidableEq n] [CommRing R]
    (X : Matrix n n R) (hX : Xᵀ = X) (c : R) : (1 - c • X)ᵀ = 1 - c • X := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hX]

/-- `Q` is symmetric when `M` is. -/
lemma mol_pairQ_transpose {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (hM : Mᵀ = M) : (pairQ β M)ᵀ = pairQ β M := by
  ext a b
  have h := congrFun (congrFun hM a) b
  simp only [Matrix.transpose_apply] at h
  simp only [Matrix.transpose_apply, pairQ, Matrix.of_apply, h]

/-- `P` is symmetric when `M` is. -/
private lemma mol_pairP_transpose {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (hM : Mᵀ = M) : (pairP β M)ᵀ = pairP β M := by
  ext a b
  have h := congrFun (congrFun hM a) b
  simp only [Matrix.transpose_apply] at h
  simp only [Matrix.transpose_apply, pairP, Matrix.of_apply, h]

variable {g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ} {t a c C : ℝ}

lemma MolHyp.data (h : MolHyp g L E m t a c C) :
    PrimData (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m :=
  primData_of_root g L h.hL E m h.root

/-- The column version of the weighted rows of `(I - tQ)⁻¹`. -/
lemma MolHyp.Vcol (h : MolHyp g L E m t a c C) (z : Fin L) :
    ∑ x, Real.exp (c * cycDist x z / a) *
      ‖(1 - (t : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ x z‖ ≤ C := by
  have hs := mol_inv_comm (1 - (t : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))
    (mol_oneSub_transpose _ (mol_pairQ_transpose _ h.data.symm) _)
  refine le_trans (le_of_eq ?_) (h.Vrow z)
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hs x z, mol_cycDist_comm]

/-- Both signs of `M_B` decay at the rate `c/a`. -/
lemma MolHyp.sgn (h : MolHyp g L E m t a c C) (s : Bool) (x z : Fin L) :
    ‖sgnMat (dysonMat (hopB g) (gammaG g) L E m) s x z‖ ≤
      C * Real.exp (-(c * cycDist x z / a)) := by
  cases s
  · simp only [sgnMat, Bool.false_eq_true, ↓reduceIte, Matrix.conjTranspose_apply, norm_star]
    rw [mol_cycDist_comm]
    exact h.Mdec z x
  · simp only [sgnMat, ↓reduceIte]
    exact h.Mdec x z

private lemma MolHyp.beta_pos (h : MolHyp g L E m t a c C) : 0 < gammaG g := h.data.pos

/-- The constant of the profile of the stable molecules. -/
private def molCS (k : ℕ) (c C : ℝ) : ℝ :=
  ∑ F ∈ dissections k, C ^ (∑ v, (polyCorners F v).card) *
    (2 * (1 + 6 * k ^ 4 / c) * C) ^ F.card

private lemma molCS_nonneg (k : ℕ) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) : 0 ≤ molCS k c C :=
  Finset.sum_nonneg fun F _ => by positivity

/-- The profile of the core of a dissection whose diagonals join equal signs. -/
private lemma MolHyp.core_profile (h : MolHyp g L E m t a c C) {k : ℕ} (hk : 3 ≤ k)
    (σ : Fin k → Bool) {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k)
    (hst : ∀ d ∈ F, σ d.1 = σ d.2) (y : Fin k → Fin L) :
    ‖dissCore (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ F y‖ ≤
      C ^ (∑ v, (polyCorners F v).card) * (2 * (1 + 6 * k ^ 4 / c) * C) ^ F.card *
        Real.exp (-(c / (12 * k ^ 2) * wordDiam y / a)) := by
  set β := gammaG g
  set M := dysonMat (hopB g) (gammaG g) L E m
  set V := (1 - (t : ℂ) • pairQ β M)⁻¹
  have hβ := h.beta_pos
  have ha0 : 0 < a := by linarith [h.ha]
  have hβt : 0 ≤ β * t := mul_nonneg hβ.le h.ht0
  have hβt' : β * t ≤ 1 / a := by
    rw [le_div_iff₀ ha0]
    nlinarith [h.beta_le, h.ht0, h.ht1]
  have hF' : F ⊆ polyDiags k := ((mol_mem_dissections F).mp hF).1
  set K : ↥F → Fin L → Fin L → ℝ := fun _ o i =>
    Real.exp (c * cycDist o i / a) * (β * t) * ‖V o i‖ with hK
  have hnorm : ∀ (d : ↥F) o i, ‖pairV β M t (σ d.1.1) (σ d.1.2) o i‖ = ‖V o i‖ := by
    intro d o i
    have he := hst d.1 d.2
    unfold pairV
    rw [ite_eq_left he]
    cases σ d.1.1
    · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.map_apply, norm_star, V, β, M]
    · simp only [↓reduceIte, V, β, M]
  refine mol_core_profile hk hF' h.ha h.hc (by linarith [h.hC]) (by linarith [h.hC]) h.sgn K
    (fun _ _ _ => by positivity) (fun d o i => ?_) (fun d i => ?_) y
  · rw [norm_mul, hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβt]
    have h1 : Real.exp (-(c * cycDist o i / a)) * Real.exp (c * cycDist o i / a) = 1 := by
      rw [← Real.exp_add]; simp
    have e : Real.exp (-(c * cycDist o i / a)) * K d o i = β * t * ‖V o i‖ := by
      simp only [hK]
      rw [← mul_assoc, ← mul_assoc, h1, one_mul]
    rw [e]
  · calc ∑ o, K d o i = (β * t) * ∑ o, Real.exp (c * cycDist o i / a) * ‖V o i‖ := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun o _ => by rw [hK]; ring
      _ ≤ (1 / a) * C := by
          gcongr
          exact h.Vcol i
      _ = C / a := by ring

/-- The profile of the stable molecules: `‖S(y)‖ ≤ C_S e^{-c diam(y)/(12k²a)}`. -/
private lemma MolHyp.stable_profile (h : MolHyp g L E m t a c C) {k : ℕ} (hk : 3 ≤ k)
    (σ : Fin k → Bool) (y : Fin k → Fin L) :
    ‖stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖ ≤
      molCS k c C * Real.exp (-(c / (12 * k ^ 2) * wordDiam y / a)) := by
  unfold stableMol molCS
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ F ∈ (dissections k).filter (fun F => ∀ d ∈ F, σ d.1 = σ d.2),
        ‖dissCore (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ F y‖
      ≤ ∑ F ∈ (dissections k).filter (fun F => ∀ d ∈ F, σ d.1 = σ d.2),
          C ^ (∑ v, (polyCorners F v).card) * (2 * (1 + 6 * k ^ 4 / c) * C) ^ F.card *
            Real.exp (-(c / (12 * k ^ 2) * wordDiam y / a)) :=
        Finset.sum_le_sum fun F hF => h.core_profile hk σ (Finset.mem_filter.mp hF).1
          (Finset.mem_filter.mp hF).2 y
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun F _ _ => ?_
        have := h.hc
        have := h.hC
        positivity

end Hyp

/-! ## Bounded coupling: the kernel facts on `0 ≤ t ≤ 1` -/

section Bounded

/-- A weighted row bound for `(I - tQ)⁻¹` on `0 ≤ t < 1` passes to `t = 1` (Lean inverse: if
`I - Q` is singular, its inverse is `0`). -/
private lemma mol_inv_limit {L : ℕ} (Q : Matrix (Fin L) (Fin L) ℂ) (w : Fin L → Fin L → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ x, ∑ z, w x z * ‖(1 - (t : ℂ) • Q)⁻¹ x z‖ ≤ B)
    (x : Fin L) : ∑ z, w x z * ‖(1 - ((1 : ℝ) : ℂ) • Q)⁻¹ x z‖ ≤ B := by
  by_cases hU : IsUnit (1 - ((1 : ℝ) : ℂ) • Q).det
  · have hA : Continuous (fun t : ℝ => (1 - (t : ℂ) • Q)) :=
      continuous_const.sub (Complex.continuous_ofReal.smul continuous_const)
    have hinv : ∀ z, ContinuousAt (fun t : ℝ => (1 - (t : ℂ) • Q)⁻¹ x z) 1 := by
      intro z
      have e : (fun t : ℝ => (1 - (t : ℂ) • Q)⁻¹ x z) = fun t : ℝ =>
          (Ring.inverse (1 - (t : ℂ) • Q).det) * (1 - (t : ℂ) • Q).adjugate x z := by
        funext t
        rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
      rw [e]
      refine ContinuousAt.mul ?_ ((hA.matrix_adjugate.matrix_elem x z).continuousAt)
      simp only [Ring.inverse_eq_inv']
      exact hA.matrix_det.continuousAt.inv₀ hU.ne_zero
    have htend : Tendsto (fun t : ℝ => ∑ z, w x z * ‖(1 - (t : ℂ) • Q)⁻¹ x z‖) (𝓝[<] 1)
        (𝓝 (∑ z, w x z * ‖(1 - ((1 : ℝ) : ℂ) • Q)⁻¹ x z‖)) := by
      refine tendsto_finsetSum _ fun z _ => ?_
      exact (tendsto_const_nhds.mul (hinv z).tendsto.norm).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact h t ht.1.le ht.2 x
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hU]
    simp only [Matrix.zero_apply, norm_zero, mul_zero, Finset.sum_const_zero]
    exact hB

private lemma mol_gammaG_le_one (g : ℝ) : gammaG g ≤ 1 := by
  unfold gammaG
  have : (1 : ℝ) ≤ max 1 g ^ 2 := one_le_pow₀ (le_max_left _ _)
  exact inv_le_one_of_one_le₀ this

private lemma mol_gammaG_ge {g C : ℝ} (hg : 0 ≤ g) (hgC : g ≤ C) :
    ((max 1 C) ^ 2)⁻¹ ≤ gammaG g := by
  unfold gammaG
  have h1 : max 1 g ≤ max 1 C := max_le_max le_rfl hgC
  have h0 : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have := hg
  gcongr

/-- The kernel facts at bounded coupling, at the scale `a = 1`, for every `0 ≤ t ≤ 1`. -/
lemma mol_bdd_hyp (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') :
    ∃ c Ck : ℝ, ∃ L₀ : ℕ, 0 < c ∧ 1 ≤ Ck ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L →
      L₀ ≤ L → ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      c' ≤ m.im → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → MolHyp g L E m t 1 c Ck := by
  obtain ⟨c₁, C₁, L₁, hc₁, hC₁, H⟩ := bdd_kernels C B₀ c' hC hB₀ hc'
  set Ck := max (max C₁ 1) (max (1 / c') ((max 1 C) ^ 2)) with hCk
  have hCk1 : C₁ ≤ Ck := (le_max_left _ _).trans (le_max_left _ _)
  have hCk2 : 1 ≤ Ck := (le_max_right _ _).trans (le_max_left _ _)
  have hCk3 : 1 / c' ≤ Ck := (le_max_left _ _).trans (le_max_right _ _)
  have hCk4 : (max 1 C) ^ 2 ≤ Ck := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨c₁, Ck, L₁, hc₁, hCk2, ?_⟩
  intro g hg hgC L hL hL₁ E hE m hm hcm t ht0 ht1
  have HK := fun t (h0 : 0 ≤ t) (h1 : t < 1) => H g hg hgC L hL hL₁ E hE m hm hcm t h0 h1
  obtain ⟨-, -, hMrow, -, -⟩ := HK 0 le_rfl one_pos
  set M := dysonMat (hopB g) (gammaG g) L E m with hMdef
  have hD := primData_of_root g L hL E m hm
  have hMdec : ∀ x z, ‖M x z‖ ≤ C₁ * Real.exp (-(c₁ * cycDist x z)) := by
    intro x z
    have h1 := Finset.single_le_sum (f := fun b => Real.exp (c₁ * cycDist x b) * ‖M x b‖)
      (fun b _ => by positivity) (Finset.mem_univ z)
    have h2 := h1.trans (hMrow x)
    have he : Real.exp (-(c₁ * cycDist x z)) * Real.exp (c₁ * cycDist x z) = 1 := by
      rw [← Real.exp_add]; simp
    calc ‖M x z‖ = Real.exp (-(c₁ * cycDist x z)) * (Real.exp (c₁ * cycDist x z) * ‖M x z‖) := by
          rw [← mul_assoc, he, one_mul]
      _ ≤ Real.exp (-(c₁ * cycDist x z)) * C₁ := by gcongr
      _ = C₁ * Real.exp (-(c₁ * cycDist x z)) := by ring
  have hVrow : ∀ x, ∑ z, Real.exp (c₁ * cycDist x z) *
      ‖(1 - (t : ℂ) • pairQ (gammaG g) M)⁻¹ x z‖ ≤ C₁ := by
    intro x
    rcases ht1.lt_or_eq with h1 | h1
    · exact (HK t ht0 h1).2.2.2.2 x
    · subst h1
      exact mol_inv_limit _ (fun x z => Real.exp (c₁ * cycDist x z)) C₁ hC₁.le
        (fun t h0 h1 x => (HK t h0 h1).2.2.2.2 x) x
  refine ⟨hL, hm, le_rfl, hc₁, hCk2, ht0, ht1, fun x z => ?_, fun x => ?_, ?_, ?_, ?_, ?_⟩
  · rw [div_one]
    exact (hMdec x z).trans (by gcongr)
  · simp only [div_one]
    exact (hVrow x).trans hCk1
  · have := hMdec ⟨0, by omega⟩ ⟨0, by omega⟩
    have hd : M ⟨0, by omega⟩ ⟨0, by omega⟩ = m := hD.diag _
    rw [hd, mol_cycDist_self] at this
    simp only [CharP.cast_eq_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
    exact this.trans hCk1
  · have h1 : Ck⁻¹ ≤ c' := by
      rw [inv_le_comm₀ (by linarith) hc']
      rw [one_div] at hCk3
      exact hCk3
    exact h1.trans hcm
  · rw [mul_one]; exact mol_gammaG_le_one g
  · rw [mul_one]
    have h1 := mol_gammaG_ge hg hgC
    have h2 : 0 < (max 1 C) ^ 2 := by
      have : (0 : ℝ) < max 1 C := lt_of_lt_of_le one_pos (le_max_left _ _)
      positivity
    calc (1 : ℝ) = (max 1 C) ^ 2 * ((max 1 C) ^ 2)⁻¹ := by field_simp
      _ ≤ Ck * gammaG g := by gcongr

end Bounded

/-- (B.2) [ba:eq:moment], Lemma B.1 [ba:lem:moment]: weighted row and spatial moments of the
stable molecules at every anchor, on `0 ≤ g ≤ C` and `0 ≤ t ≤ 1`. -/
theorem stableMol_bdd (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') (k r : ℕ)
    (hk : 3 ≤ k) :
    ∃ c C' : ℝ, ∃ L₀ : ℕ, 0 < c ∧ 0 < C' ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L →
      L₀ ≤ L → ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      c' ≤ m.im → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ (σ : Fin k → Bool) (v : Fin k) (b : Fin L),
        (∑ y ∈ Finset.univ.filter (fun y : Fin k → Fin L => y v = b), Real.exp (c * wordDiam y) *
            ‖stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖ ≤ C') ∧
        ∑ y ∈ Finset.univ.filter (fun y : Fin k → Fin L => y v = b), (wordDiam y : ℝ) ^ r *
            ‖stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖ ≤ C' := by
  obtain ⟨c₁, Ck, L₀, hc₁, hCk, H⟩ := mol_bdd_hyp C B₀ c' hC hB₀ hc'
  set c₃ := c₁ / (12 * k ^ 2) with hc₃
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hc₃0 : 0 < c₃ := by positivity
  set CS := molCS k c₁ Ck
  have hCS : 0 ≤ CS := molCS_nonneg k hc₁ (by linarith)
  set Kr : ℝ := (r.factorial : ℝ) * (2 / c₃) ^ r
  have hKr : 0 ≤ Kr := by positivity
  set G : ℝ := (2 * (1 + k / (c₃ / 2)) * 1) ^ (k - 1)
  have hG : 0 ≤ G := by positivity
  refine ⟨c₃ / 2, CS * max 1 Kr * G + 1, L₀, by positivity, by positivity, ?_⟩
  intro g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1 σ v b
  have h := H g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1
  have hprof := fun y => h.stable_profile hk σ y
  simp only [div_one] at hprof
  have hsum := mol_anchor_sum (L := L) v b (c := c₃ / 2) (a := 1) (by positivity) le_rfl
  simp only [div_one] at hsum
  have hpt : ∀ y : Fin k → Fin L,
      Real.exp (c₃ / 2 * wordDiam y) *
          ‖stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖ ≤
        CS * max 1 Kr * Real.exp (-(c₃ / 2 * wordDiam y)) ∧
      (wordDiam y : ℝ) ^ r *
          ‖stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖ ≤
        CS * max 1 Kr * Real.exp (-(c₃ / 2 * wordDiam y)) := by
    intro y
    set D : ℝ := (wordDiam y : ℝ)
    have hD : 0 ≤ D := Nat.cast_nonneg _
    have hS : ‖stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖ ≤
        CS * Real.exp (-(c₃ * D)) := hprof y
    have e1 : Real.exp (c₃ / 2 * D) * Real.exp (-(c₃ * D)) = Real.exp (-(c₃ / 2 * D)) := by
      rw [← Real.exp_add]; congr 1; ring
    constructor
    · calc Real.exp (c₃ / 2 * D) *
            ‖stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖
          ≤ Real.exp (c₃ / 2 * D) * (CS * Real.exp (-(c₃ * D))) := by gcongr
        _ = CS * Real.exp (-(c₃ / 2 * D)) := by rw [← e1]; ring
        _ ≤ CS * max 1 Kr * Real.exp (-(c₃ / 2 * D)) := by
            have hx : 0 ≤ CS * Real.exp (-(c₃ / 2 * D)) := by positivity
            have := mul_le_mul_of_nonneg_left (le_max_left 1 Kr) hx
            linarith
    · have hpow : D ^ r ≤ Kr * Real.exp (c₃ / 2 * D) := by
        have h1 := Real.pow_div_factorial_le_exp (c₃ / 2 * D) (by positivity) r
        have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
        rw [div_le_iff₀ hf] at h1
        have e : D ^ r = (2 / c₃) ^ r * (c₃ / 2 * D) ^ r := by
          rw [← mul_pow]; congr 1; field_simp
        rw [e]
        calc (2 / c₃) ^ r * (c₃ / 2 * D) ^ r ≤ (2 / c₃) ^ r *
              (Real.exp (c₃ / 2 * D) * r.factorial) := by gcongr
          _ = Kr * Real.exp (c₃ / 2 * D) := by ring
      calc D ^ r * ‖stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖
          ≤ (Kr * Real.exp (c₃ / 2 * D)) * (CS * Real.exp (-(c₃ * D))) := by
            gcongr
        _ = Kr * CS * Real.exp (-(c₃ / 2 * D)) := by rw [← e1]; ring
        _ ≤ CS * max 1 Kr * Real.exp (-(c₃ / 2 * D)) := by
            have hx : 0 ≤ CS * Real.exp (-(c₃ / 2 * D)) := by positivity
            have := mul_le_mul_of_nonneg_left (le_max_right 1 Kr) hx
            linarith
  have hfin : ∑ y ∈ Finset.univ.filter (fun y : Fin k → Fin L => y v = b),
      CS * max 1 Kr * Real.exp (-(c₃ / 2 * wordDiam y)) ≤ CS * max 1 Kr * G + 1 := by
    rw [← Finset.mul_sum]
    have : 0 ≤ CS * max 1 Kr := by positivity
    calc CS * max 1 Kr * ∑ y ∈ Finset.univ.filter (fun y : Fin k → Fin L => y v = b),
          Real.exp (-(c₃ / 2 * wordDiam y)) ≤ CS * max 1 Kr * G := by
          gcongr
      _ ≤ CS * max 1 Kr * G + 1 := by linarith
  exact ⟨(Finset.sum_le_sum fun y _ => (hpt y).1).trans hfin,
    (Finset.sum_le_sum fun y _ => (hpt y).2).trans hfin⟩

/-! ## Full rows of the primitive loops

The full row `Σ_a F_k(a; σ)`: bounded for one-sign words, and of size `(a/(1-t))^{k-1}` for
every word by the primitive Ward identity, Lemma 5.1 [fo:lem:mixed-ward]. -/

section Rows

/-- The full sum `Σ_a F_k(a; σ)` of a primitive loop. -/
private def molRow {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (t : ℝ) {k : ℕ}
    (σ : Fin k → Bool) : ℂ :=
  ∑ a : Fin k → Fin L, primF β M m t a σ

/-- The full sum of a dressed dissection value: the external inverses act on their columns. -/
private lemma mol_sum_dissVal {L k : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    (σ : Fin k → Bool) (F : Finset (Fin k × Fin k)) :
    ∑ a : Fin k → Fin L, dissVal β M t σ F a =
      ∑ y : Fin k → Fin L, (∏ i, ∑ x, pairV β M t (σ i) (σ (finRotate k i)) x (y i)) *
        dissCore β M t σ F y := by
  unfold dissVal
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_mul, Fintype.prod_sum]

/-- `F_k` is the dissection sum for `k ≥ 3`. -/
private lemma mol_primF_ge3 {L k : ℕ} (hk : 3 ≤ k) (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ)
    (m : ℂ) (t : ℝ) (a : Fin k → Fin L) (σ : Fin k → Bool) :
    primF β M m t a σ = ∑ F ∈ dissections k, dissVal β M t σ F a := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  rfl

/-- The full row for `k ≥ 3`, with the external inverses acting on their columns. -/
private lemma mol_row_ge3 {L k : ℕ} (hk : 3 ≤ k) (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ)
    (m : ℂ) (t : ℝ) (σ : Fin k → Bool) :
    molRow β M m t σ = ∑ F ∈ dissections k, ∑ y : Fin k → Fin L,
      (∏ i, ∑ x, pairV β M t (σ i) (σ (finRotate k i)) x (y i)) * dissCore β M t σ F y := by
  unfold molRow
  simp only [mol_primF_ge3 hk]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun F _ => mol_sum_dissVal β M t σ F

/-- The constant of the one-sign rows. -/
private def molR1 (k : ℕ) (c C : ℝ) : ℝ :=
  C ^ k * (C + molCS k c C * (2 * (1 + k / (c / (12 * k ^ 2)))) ^ (k - 1))

variable {g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ} {t a c C : ℝ}

/-- One-sign rows: `‖Σ_a F_k(a; s, …, s)‖ ≤ C_k L a^{k-1}`. -/
private lemma MolHyp.row_const (h : MolHyp g L E m t a c C) {k : ℕ} (hk : 1 ≤ k)
    (σ : Fin k → Bool) (hσ : ∀ i, σ i = σ ⟨0, by omega⟩) :
    ‖molRow (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t σ‖ ≤
      molR1 k c C * L * a ^ (k - 1) := by
  set β := gammaG g
  set M := dysonMat (hopB g) (gammaG g) L E m
  set V := (1 - (t : ℂ) • pairQ β M)⁻¹
  have hC := h.hC
  have hc := h.hc
  have ha := h.ha
  have ha0 : 0 < a := by linarith
  have hβ := h.beta_pos
  have hCS : 0 ≤ molCS k c C := molCS_nonneg k hc (by linarith)
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hVcol : ∀ y, ∑ x, ‖V x y‖ ≤ C := fun y =>
    le_trans (Finset.sum_le_sum fun x _ => le_mul_of_one_le_left (norm_nonneg _)
      (Real.one_le_exp (by positivity))) (h.Vcol y)
  have hVrow : ∀ x, ∑ y, ‖V x y‖ ≤ C := fun x =>
    le_trans (Finset.sum_le_sum fun y _ => le_mul_of_one_le_left (norm_nonneg _)
      (Real.one_le_exp (by positivity))) (h.Vrow x)
  have hVs : ∀ s x y, ‖pairV β M t s s x y‖ = ‖V x y‖ := by
    intro s x y
    unfold pairV
    cases s
    · simp only [↓reduceIte, Bool.false_eq_true, Matrix.map_apply, norm_star, V, β, M]
    · simp only [↓reduceIte, V, β, M]
  have hX : C ^ k * C ≤ molR1 k c C := by
    unfold molR1
    have : 0 ≤ C ^ k * (molCS k c C * (2 * (1 + k / (c / (12 * k ^ 2)))) ^ (k - 1)) := by
      positivity
    nlinarith
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
    · -- length one
      have hrow : molRow β M m t σ = (L : ℂ) * (if σ 0 then m else star m) := by
        unfold molRow
        change ∑ _a : Fin 1 → Fin L, (if σ 0 then m else star m) = _
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, pow_one, nsmul_eq_mul]
      rw [hrow, norm_mul, Complex.norm_natCast]
      have hm : ‖(if σ 0 then m else star m)‖ ≤ C := by
        split_ifs
        · exact h.m_le
        · rw [norm_star]; exact h.m_le
      have h1 : C ≤ molR1 1 c C := by
        have := hX; simp only [pow_one] at this; nlinarith
      calc (L : ℝ) * ‖(if σ 0 then m else star m)‖ ≤ L * C := by gcongr
        _ ≤ L * molR1 1 c C := by gcongr
        _ = molR1 1 c C * L * a ^ (1 - 1) := by simp; ring
    · -- length two
      have h01 : σ 1 = σ 0 := hσ 1
      have hrow : molRow β M m t σ = ∑ x : Fin L, ∑ y : Fin L,
          (β : ℂ)⁻¹ * pairK β M t (σ 0) (σ 0) x y := by
        unfold molRow
        rw [← (piFinTwoEquiv fun _ => Fin L).symm.sum_comp, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        change (β : ℂ)⁻¹ * pairK β M t (σ 0) (σ 1) x y = _
        rw [h01]
      have hK : ∀ s x y, ‖pairK β M t s s x y‖ ≤ ∑ z, ‖pairQ β M x z‖ * ‖V z y‖ := by
        intro s x y
        have e : ‖pairK β M t s s x y‖ = ‖(pairQ β M * V) x y‖ := by
          cases s <;> simp [pairK, V, Matrix.map_apply]
        rw [e, Matrix.mul_apply]
        exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun z _ => norm_mul _ _))
      have hβ' : 0 < β := hβ
      have hQ : ∀ x, ∑ z, ‖pairQ β M x z‖ = 1 := by
        intro x
        have := h.data.row_sum x
        rw [← this]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp only [pairQ, pairP, Matrix.of_apply, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hβ']
        rfl
      have hβinv : β⁻¹ ≤ C * a := by
        have := h.beta_ge
        rw [inv_le_iff_one_le_mul₀ hβ']
        nlinarith
      have h2 : C * C ≤ molR1 2 c C := by
        have := hX
        have : C * C ≤ C ^ 2 * C := by nlinarith
        linarith
      rw [hrow]
      calc ‖∑ x : Fin L, ∑ y : Fin L, (β : ℂ)⁻¹ * pairK β M t (σ 0) (σ 0) x y‖
          ≤ ∑ x : Fin L, ∑ y : Fin L, β⁻¹ * ∑ z, ‖pairQ β M x z‖ * ‖V z y‖ := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
            rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ']
            gcongr
            exact hK _ x y
        _ = ∑ x : Fin L, β⁻¹ * ∑ z, ‖pairQ β M x z‖ * ∑ y, ‖V z y‖ := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [← Finset.mul_sum, Finset.sum_comm]
            congr 1
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Finset.mul_sum]
        _ ≤ ∑ x : Fin L, β⁻¹ * ∑ z, ‖pairQ β M x z‖ * C := by
            gcongr with x _ z _
            exact hVrow z
        _ = L * (β⁻¹ * C) := by
            simp only [← Finset.sum_mul, hQ, one_mul, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
            ring
        _ ≤ L * (C * a * C) := by gcongr
        _ = (C * C) * (L * a) := by ring
        _ ≤ molR1 2 c C * (L * a) := by
            have : 0 ≤ (L : ℝ) * a := by positivity
            gcongr
        _ = molR1 2 c C * L * a ^ (2 - 1) := by simp; ring
  · -- length at least three
    have hst : ∀ F ∈ dissections k, ∀ d ∈ F, σ d.1 = σ d.2 := fun F _ d _ => by
      rw [hσ d.1, hσ d.2]
    have hpair : ∀ (y : Fin k → Fin L) (i : Fin k),
        ‖∑ x, pairV β M t (σ i) (σ (finRotate k i)) x (y i)‖ ≤ C := by
      intro y i
      rw [hσ i, hσ (finRotate k i)]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_congr rfl fun x _ => hVs _ x (y i)]
      exact hVcol (y i)
    set c₃ := c / (12 * k ^ 2) with hc₃
    have hk0 : (0 : ℝ) < k := by have : 0 < k := by omega
                                 exact_mod_cast this
    have hc₃0 : 0 < c₃ := by positivity
    have hcore : ∀ y : Fin k → Fin L, ∑ F ∈ dissections k, ‖dissCore β M t σ F y‖ ≤
        molCS k c C * Real.exp (-(c₃ * wordDiam y / a)) := by
      intro y
      unfold molCS
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun F hF => h.core_profile hk3 σ hF (hst F hF) y
    have hfull := mol_full_sum (L := L) (k := k) (by omega) hc₃0 ha
    rw [mol_row_ge3 hk3]
    calc ‖∑ F ∈ dissections k, ∑ y : Fin k → Fin L,
          (∏ i, ∑ x, pairV β M t (σ i) (σ (finRotate k i)) x (y i)) * dissCore β M t σ F y‖
        ≤ ∑ F ∈ dissections k, ∑ y : Fin k → Fin L, C ^ k * ‖dissCore β M t σ F y‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun F _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
          rw [norm_mul, norm_prod]
          gcongr
          calc ∏ i, ‖∑ x, pairV β M t (σ i) (σ (finRotate k i)) x (y i)‖ ≤ ∏ _i : Fin k, C :=
                Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => hpair y i
            _ = C ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = C ^ k * ∑ y : Fin k → Fin L, ∑ F ∈ dissections k, ‖dissCore β M t σ F y‖ := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
      _ ≤ C ^ k * ∑ y : Fin k → Fin L, molCS k c C * Real.exp (-(c₃ * wordDiam y / a)) := by
          gcongr with y _
          exact hcore y
      _ = C ^ k * molCS k c C * ∑ y : Fin k → Fin L, Real.exp (-(c₃ * wordDiam y / a)) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ C ^ k * molCS k c C * (L * (2 * (1 + k / c₃) * a) ^ (k - 1)) := by gcongr
      _ = C ^ k * (molCS k c C * (2 * (1 + k / c₃)) ^ (k - 1)) * L * a ^ (k - 1) := by
          rw [mul_pow]; ring
      _ ≤ molR1 k c C * L * a ^ (k - 1) := by
          unfold molR1
          rw [← hc₃]
          have : 0 ≤ C ^ k := by positivity
          have : 0 ≤ (L : ℝ) * a ^ (k - 1) := by positivity
          have : C ^ k * (molCS k c C * (2 * (1 + k / c₃)) ^ (k - 1)) ≤
              C ^ k * (C + molCS k c C * (2 * (1 + k / c₃)) ^ (k - 1)) := by gcongr; linarith
          nlinarith

end Rows

/-! ## The primitive Ward identity on full rows -/

section WardRows

/-- The value of an iterated cyclic rotation. -/
lemma mol_iter_val {k : ℕ} (r : ℕ) (x : Fin k) :
    ((finRotate k)^[r] x).val = (x.val + r) % k := by
  have hk : 0 < k := Fin.pos x
  induction r with
  | zero => simp [Nat.mod_eq_of_lt x.isLt]
  | succ r ih =>
    rw [Function.iterate_succ_apply', mol_finRotate_val, ih]
    have hv : (x.val + r) % k < k := Nat.mod_lt _ hk
    rw [show x.val + (r + 1) = (x.val + r) + 1 by ring, ← Nat.mod_add_mod (x.val + r) k 1]
    split_ifs with h
    · rw [h, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (show (x.val + r) % k + 1 < k by omega)]

/-- A word that is not constant changes sign between two cyclically consecutive positions. -/
private lemma mol_exists_change {k : ℕ} (hk : 1 ≤ k) (σ : Fin k → Bool)
    (h : ¬∀ i, σ i = σ ⟨0, by omega⟩) : ∃ i, σ (finRotate k i) ≠ σ i := by
  by_contra hc
  push Not at hc
  apply h
  intro i
  have key : ∀ r, σ ((finRotate k)^[r] ⟨0, by omega⟩) = σ ⟨0, by omega⟩ := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih => rw [Function.iterate_succ_apply', hc, ih]
  have e : (finRotate k)^[i.val] ⟨0, by omega⟩ = i := by
    apply Fin.ext
    rw [mol_iter_val]
    simp [Nat.mod_eq_of_lt i.isLt]
  rw [← e, key]

variable {g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ} {t : ℝ}

/-- `F_k` of the model is invariant under the cyclic rotation, on `0 ≤ t < 1`. -/
private lemma mol_primF_rotate (hL : 3 ≤ L) (hm : IsDysonRootV (hopB g) (gammaG g) L E m)
    (ht0 : 0 ≤ t) (ht1 : t < 1) {k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) :
    primF (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t (a ∘ finRotate k)
        (σ ∘ finRotate k) =
      primF (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t a σ := by
  have := primLoop_rotate g 1 L hL E m hm t ht0 ht1 a σ
  simpa [primLoop, primK] using this

/-- Full rows are invariant under the cyclic rotation of the word. -/
private lemma mol_row_rotate (hL : 3 ≤ L) (hm : IsDysonRootV (hopB g) (gammaG g) L E m)
    (ht0 : 0 ≤ t) (ht1 : t < 1) {k : ℕ} (σ : Fin k → Bool) :
    molRow (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t (σ ∘ finRotate k) =
      molRow (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t σ := by
  unfold molRow
  rw [← Finset.sum_congr rfl fun a _ => mol_primF_rotate hL hm ht0 ht1 a σ]
  refine Fintype.sum_equiv (Equiv.arrowCongr (finRotate k) (Equiv.refl (Fin L))) _ _
    (fun a => ?_)
  congr 1
  funext x
  change a x = a ((finRotate k).symm ((finRotate k) x))
  rw [Equiv.symm_apply_apply]

/-- Full rows are invariant under the iterated cyclic rotations of the word. -/
private lemma mol_row_iter (hL : 3 ≤ L) (hm : IsDysonRootV (hopB g) (gammaG g) L E m)
    (ht0 : 0 ≤ t) (ht1 : t < 1) {k : ℕ} (σ : Fin k → Bool) (r : ℕ) :
    molRow (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t (σ ∘ (finRotate k)^[r]) =
      molRow (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t σ := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ, ← Function.comp_assoc, mol_row_rotate hL hm ht0 ht1, ih]

/-- The primitive Ward identity, Lemma 5.1 [fo:lem:mixed-ward], summed over all labels: the
full row of a word whose last sign differs from the first. -/
private lemma mol_row_ward (hL : 3 ≤ L) (hm : IsDysonRootV (hopB g) (gammaG g) L E m)
    (ht0 : 0 ≤ t) (ht1 : t < 1) {k : ℕ} (hk : 1 ≤ k) (σ : Fin (k + 1) → Bool)
    (hs : σ (Fin.last k) ≠ σ 0) :
    molRow (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t σ =
      ((2 * I * (((1 - t) * gammaG g * m.im : ℝ) : ℂ)))⁻¹ *
        (molRow (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t
            (Function.update (Fin.init σ) ⟨0, hk⟩ true) -
          molRow (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t
            (Function.update (Fin.init σ) ⟨0, hk⟩ false)) := by
  have hD := primData_of_root g L hL E m hm
  have h1 : Function.update (Fin.init σ) ⟨0, hk⟩ (σ 0) = Fin.init σ := by
    apply Function.update_eq_self_iff.mpr
    rfl
  have h2 : σ (Fin.last k) = !(σ 0) := by
    revert hs
    cases σ (Fin.last k) <;> cases σ 0 <;> simp
  have hσ : Fin.snoc (Function.update (Fin.init σ) ⟨0, hk⟩ (σ 0)) (!(σ 0)) = σ := by
    rw [h1, ← h2, Fin.snoc_init_self]
  have hW := fun a => primF_ward hD t ht0 ht1 k hk a (Fin.init σ) (σ 0)
  rw [hσ] at hW
  unfold molRow
  rw [← (Fin.snocEquiv fun _ => Fin L).sum_comp, Fintype.sum_prod_type, Finset.sum_comm,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hW a]
  rfl

end WardRows

/-! ## The size of the full rows -/

private lemma molR1_nonneg (k : ℕ) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) : 0 ≤ molR1 k c C := by
  unfold molR1
  have := molCS_nonneg k hc hC
  positivity

/-- The full rows of every word: `‖Σ_a F_k(a; σ)‖ ≤ A L a^{k-1}(1-t)^{1-k}`, by the primitive
Ward identity and the one-sign rows. -/
private lemma mol_row_bound {c C : ℝ} (hc : 0 < c) (hC : 1 ≤ C) (k : ℕ) (hk : 1 ≤ k) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (g : ℝ) (L : ℕ) (E : ℝ) (m : ℂ) (t a : ℝ), MolHyp g L E m t a c C →
      t < 1 → ∀ σ : Fin k → Bool,
        ‖molRow (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t σ‖ ≤
          A * L * a ^ (k - 1) * ((1 - t) ^ (k - 1))⁻¹ := by
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨molR1 1 c C, molR1_nonneg 1 hc (by linarith), fun g L E m t a h ht1 σ => ?_⟩
    have := h.row_const le_rfl σ (fun i => congrArg σ (Subsingleton.elim _ _))
    simpa using this
  | succ k hk ih =>
    obtain ⟨A, hA, hAb⟩ := ih
    have hR := molR1_nonneg (k + 1) hc (show (0 : ℝ) ≤ C by linarith)
    refine ⟨max (molR1 (k + 1) c C) (C ^ 2 * A), le_max_of_le_left hR,
      fun g L E m t a h ht1 σ => ?_⟩
    have ha := h.ha
    have ha0 : 0 < a := by linarith
    have hδ : 0 < 1 - t := by linarith
    have hδ1 : 1 - t ≤ 1 := by linarith [h.ht0]
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    rw [show k + 1 - 1 = k by omega]
    have hpow1 : 1 ≤ ((1 - t) ^ k)⁻¹ := one_le_inv₀ (by positivity) |>.mpr (pow_le_one₀ hδ.le hδ1)
    by_cases hcst : ∀ i, σ i = σ ⟨0, by omega⟩
    · have h1 := h.row_const (by omega) σ hcst
      rw [show k + 1 - 1 = k by omega] at h1
      have h2 : molR1 (k + 1) c C * L * a ^ k ≤
          max (molR1 (k + 1) c C) (C ^ 2 * A) * L * a ^ k := by
        gcongr; exact le_max_left _ _
      have h3 : 0 ≤ max (molR1 (k + 1) c C) (C ^ 2 * A) * L * a ^ k :=
        by have := le_max_left (molR1 (k + 1) c C) (C ^ 2 * A); positivity
      calc _ ≤ max (molR1 (k + 1) c C) (C ^ 2 * A) * L * a ^ k := h1.trans h2
        _ ≤ max (molR1 (k + 1) c C) (C ^ 2 * A) * L * a ^ k * ((1 - t) ^ k)⁻¹ :=
            le_mul_of_one_le_right h3 hpow1
    · obtain ⟨i, hi⟩ := mol_exists_change (by omega) σ hcst
      set σ' := σ ∘ (finRotate (k + 1))^[i.val + 1] with hσ'
      have hrow := (mol_row_iter h.hL h.root h.ht0 ht1 σ (i.val + 1)).symm
      have hlast : σ' (Fin.last k) = σ i := by
        simp only [hσ', Function.comp_apply]
        congr 1
        apply Fin.ext
        rw [mol_iter_val, Fin.val_last, show k + (i.val + 1) = i.val + (k + 1) by ring,
          Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      have hfirst : σ' 0 = σ (finRotate (k + 1) i) := by
        simp only [hσ', Function.comp_apply]
        congr 1
        apply Fin.ext
        rw [mol_iter_val, mol_finRotate_val, Fin.val_zero, zero_add]
        have := i.isLt
        split_ifs with h0
        · rw [h0, Nat.mod_self]
        · exact Nat.mod_eq_of_lt (by omega)
      have hs : σ' (Fin.last k) ≠ σ' 0 := by
        rw [hlast, hfirst]; exact fun h => hi h.symm
      rw [hrow, mol_row_ward h.hL h.root h.ht0 ht1 hk σ' hs]
      set β := gammaG g
      set r : ℝ := (1 - t) * β * m.im with hr
      have hβ : 0 < β := h.beta_pos
      have him : 0 < m.im := h.data.im_pos
      have hr0 : 0 < r := by positivity
      have hz : ‖(2 * I * ((r : ℝ) : ℂ))‖ = 2 * r := by
        rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr0]
        simp
      set X := A * L * a ^ (k - 1) * ((1 - t) ^ (k - 1))⁻¹ with hX
      have hX0 : 0 ≤ X := by positivity
      have hp := hAb g L E m t a h ht1 (Function.update (Fin.init σ') ⟨0, hk⟩ true)
      have hm' := hAb g L E m t a h ht1 (Function.update (Fin.init σ') ⟨0, hk⟩ false)
      have hβim : (β * m.im)⁻¹ ≤ C ^ 2 * a := by
        have h1 : 1 ≤ C * (β * a) := h.beta_ge
        have h2 : C⁻¹ ≤ m.im := h.im_ge
        have hC0 : 0 < C := by linarith
        rw [inv_le_iff_one_le_mul₀ (by positivity)]
        have h3 : 1 ≤ C * m.im := by
          have := mul_le_mul_of_nonneg_left h2 hC0.le
          rwa [mul_inv_cancel₀ hC0.ne'] at this
        nlinarith [mul_le_mul h1 h3 zero_le_one (by positivity)]
      have hapow : a ^ (k - 1) * a = a ^ k := by
        rw [← pow_succ, Nat.sub_add_cancel hk]
      have hdpow : (1 - t) ^ (k - 1) * (1 - t) = (1 - t) ^ k := by
        rw [← pow_succ, Nat.sub_add_cancel hk]
      calc ‖(2 * I * ((r : ℝ) : ℂ))⁻¹ *
            (molRow β (dysonMat (hopB g) β L E m) m t (Function.update (Fin.init σ') ⟨0, hk⟩ true) -
              molRow β (dysonMat (hopB g) β L E m) m t
                (Function.update (Fin.init σ') ⟨0, hk⟩ false))‖
          ≤ (2 * r)⁻¹ * (X + X) := by
            rw [norm_mul, norm_inv, hz]
            gcongr
            exact (norm_sub_le _ _).trans (add_le_add hp hm')
        _ = (β * m.im)⁻¹ * (A * L * a ^ (k - 1) * ((1 - t) ^ (k - 1))⁻¹ * (1 - t)⁻¹) := by
            rw [hX, hr]; field_simp; ring
        _ ≤ (C ^ 2 * a) * (A * L * a ^ (k - 1) * ((1 - t) ^ (k - 1))⁻¹ * (1 - t)⁻¹) := by
            gcongr
        _ = C ^ 2 * A * L * (a ^ (k - 1) * a) * ((1 - t) ^ (k - 1) * (1 - t))⁻¹ := by
            rw [mul_inv]; ring
        _ = C ^ 2 * A * L * a ^ k * ((1 - t) ^ k)⁻¹ := by rw [hapow, hdpow]
        _ ≤ max (molR1 (k + 1) c C) (C ^ 2 * A) * L * a ^ k * ((1 - t) ^ k)⁻¹ := by
            gcongr; exact le_max_right _ _

/-! ## Masses of cores and the mixed gluing -/

section Glue2

/-- For a translation-invariant tensor, the sum over the labels with one anchored label is
`L⁻¹` times the full sum. -/
private lemma mol_anchor_eq {L k : ℕ} [NeZero L] (f : (Fin k → Fin L) → ℂ)
    (hf : ∀ z c, f (fun q => z q + c) = f z) (p : Fin k) (x : Fin L) :
    (L : ℂ) * ∑ z ∈ Finset.univ.filter (fun z : Fin k → Fin L => z p = x), f z =
      ∑ z, f z := by
  have hA : ∀ x : Fin L, ∑ z ∈ Finset.univ.filter (fun z : Fin k → Fin L => z p = x), f z =
      ∑ z ∈ Finset.univ.filter (fun z : Fin k → Fin L => z p = 0), f z := by
    intro x
    refine Finset.sum_nbij' (fun z q => z q - x) (fun z q => z q + x) ?_ ?_ ?_ ?_ ?_
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [hz, sub_self]
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [hz, zero_add]
    · intro z _
      funext q
      simp
    · intro z _
      funext q
      simp
    · intro z _
      have := hf (fun q => z q - x) x
      simp only [sub_add_cancel] at this
      exact this
  rw [← Finset.sum_fiberwise Finset.univ (fun z : Fin k → Fin L => z p) f]
  rw [Finset.sum_congr rfl fun y _ => hA y, hA x, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

variable {g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ} {t : ℝ}

/-- The rows of the mixed inverse `(I - tP)⁻¹` sum to `(1 - t)⁻¹`. -/
private lemma mol_mixed_row (hL : 3 ≤ L) (hm : IsDysonRootV (hopB g) (gammaG g) L E m)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (x : Fin L) :
    ∑ z, (1 - t • pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ x z = (1 - t)⁻¹ := by
  have hD := primData_of_root g L hL E m hm
  obtain ⟨-, hrow⟩ := propPM_nonneg_row (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))
    (fun a b => mul_nonneg hD.pos.le (sq_nonneg _)) hD.row_sum 0 t le_rfl ht0 ht1
  have := hrow x
  simp only [propPM, zero_smul, sub_zero, Matrix.one_mul] at this
  rw [this]
  ring

/-- The columns of the mixed inverse `(I - tP)⁻¹` sum to `(1 - t)⁻¹`. -/
private lemma mol_mixed_col (hL : 3 ≤ L) (hm : IsDysonRootV (hopB g) (gammaG g) L E m)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (z : Fin L) :
    ∑ x, (1 - t • pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ x z = (1 - t)⁻¹ := by
  have hD := primData_of_root g L hL E m hm
  have hs := mol_inv_comm (1 - t • pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))
    (mol_oneSub_transpose _ (mol_pairP_transpose _ hD.symm) _)
  rw [← mol_mixed_row hL hm ht0 ht1 z]
  exact Finset.sum_congr rfl fun x _ => hs x z

/-- The mixed gluing: a dissection containing the diagonal `(i, j)` joining opposite signs has
mass `βt/(1 - t)` times the product of the masses of the two polygons of the cut, divided by
`L`. -/
private lemma mol_mass_glue (hL : 3 ≤ L) (hm : IsDysonRootV (hopB g) (gammaG g) L E m)
    (ht0 : 0 ≤ t) (ht1 : t < 1) {k : ℕ} (σ : Fin k → Bool) {i j : Fin k}
    (hd : (i, j) ∈ polyDiags k) (hmix : σ i ≠ σ j) {F : Finset (Fin k × Fin k)}
    (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) :
    (L : ℂ) * ∑ y, dissCore (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ F y =
      ((gammaG g * t / (1 - t) : ℝ) : ℂ) *
        (∑ z, dissCore (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t (cutLSgn σ i j)
          (mol_splitL i j F) z) *
        (∑ z, dissCore (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t (cutRSgn σ i j)
          (mol_splitR i j F) z) := by
  have : NeZero L := ⟨by omega⟩
  set β := gammaG g
  set M := dysonMat (hopB g) (gammaG g) L E m
  set X : Matrix (Fin L) (Fin L) ℂ := ((β * t : ℝ) : ℂ) • pairV β M t (σ i) (σ j) with hX
  set cL := fun z => dissCore β M t (cutLSgn σ i j) (mol_splitL i j F) z
  set cR := fun z => dissCore β M t (cutRSgn σ i j) (mol_splitR i j F) z
  have hδ : (1 - t) ≠ 0 := by linarith
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  -- the row sums of the link
  have hXrow : ∀ x, ∑ z, X x z = ((β * t / (1 - t) : ℝ) : ℂ) := by
    intro x
    have hv : pairV β M t (σ i) (σ j) = ((1 - t • pairP β M)⁻¹).map ((↑) : ℝ → ℂ) := by
      unfold pairV; rw [ite_eq_right hmix]
    simp only [hX, Matrix.smul_apply, smul_eq_mul, hv, Matrix.map_apply, ← Finset.mul_sum]
    rw [← Complex.ofReal_sum, mol_mixed_row hL hm ht0 ht1 x]
    push_cast
    ring
  -- the translation invariance of the two cores
  have hTL : ∀ (z : Fin (k + i - j + 1) → Fin L) (c : Fin L),
      cL (fun q => z q + c) = cL z := fun z c => mol_dissCore_add g E m t _ _ z c
  have hTR : ∀ (z : Fin (j - i + 1) → Fin L) (c : Fin L),
      cR (fun q => z q + c) = cR z := fun z c => mol_dissCore_add g E m t _ _ z c
  have hAR : ∀ xi : Fin L, ∑ z ∈ Finset.univ.filter
      (fun z : Fin (j - i + 1) → Fin L => z (mol_lastR i j) = xi), cR z =
        (L : ℂ)⁻¹ * ∑ z, cR z := by
    intro xi
    rw [← mol_anchor_eq cR hTR (mol_lastR i j) xi, ← mul_assoc, inv_mul_cancel₀ hL0, one_mul]
  have hiL : (mol_iL i j).val = i.val := rfl
  have hlR : (mol_lastR i j).val = j.val - i.val := rfl
  -- the split
  have hsplit : ∑ y, dissCore β M t σ F y =
      ∑ zL : Fin (k + i - j + 1) → Fin L, ∑ zR : Fin (j - i + 1) → Fin L,
        X (zL (mol_iL i j)) (zR (mol_lastR i j)) * cL zL * cR zR := by
    rw [mol_sum_labels hd (fun zL zR => X (zL (mol_iL i j)) (zR (mol_lastR i j)) * cL zL * cR zR)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [mol_dissCore_eq_coreX y, mol_coreX_split hd hF hdF]
    refine Finset.sum_congr rfl fun xo _ => Finset.sum_congr rfl fun xi _ => ?_
    simp only [hiL, hlR, ite_true]
    rfl
  have hinner : ∀ x : Fin L, ∑ zR : Fin (j - i + 1) → Fin L,
      X x (zR (mol_lastR i j)) * cR zR =
        ((β * t / (1 - t) : ℝ) : ℂ) * ((L : ℂ)⁻¹ * ∑ z, cR z) := by
    intro x
    rw [← Finset.sum_fiberwise Finset.univ (fun zR : Fin (j - i + 1) → Fin L => zR (mol_lastR i j))]
    calc ∑ xi : Fin L, ∑ zR ∈ Finset.univ.filter
          (fun zR : Fin (j - i + 1) → Fin L => zR (mol_lastR i j) = xi),
          X x (zR (mol_lastR i j)) * cR zR
        = ∑ xi : Fin L, X x xi * ∑ zR ∈ Finset.univ.filter
          (fun zR : Fin (j - i + 1) → Fin L => zR (mol_lastR i j) = xi), cR zR := by
          refine Finset.sum_congr rfl fun xi _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun zR hz => ?_
          rw [(Finset.mem_filter.mp hz).2]
      _ = ∑ xi : Fin L, X x xi * ((L : ℂ)⁻¹ * ∑ z, cR z) := by
          simp only [hAR]
      _ = _ := by rw [← Finset.sum_mul, hXrow]
  rw [hsplit]
  have e2 : ∑ zL : Fin (k + i - j + 1) → Fin L, ∑ zR : Fin (j - i + 1) → Fin L,
      X (zL (mol_iL i j)) (zR (mol_lastR i j)) * cL zL * cR zR =
        ∑ zL : Fin (k + i - j + 1) → Fin L, cL zL *
          (((β * t / (1 - t) : ℝ) : ℂ) * ((L : ℂ)⁻¹ * ∑ z, cR z)) := by
    refine Finset.sum_congr rfl fun zL _ => ?_
    rw [← hinner (zL (mol_iL i j)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun zR _ => by ring
  rw [e2, ← Finset.sum_mul]
  field_simp

end Glue2

/-! ## Alternating words and the mixed reduction -/

section Alt

/-- The diagonals joining opposite signs. -/
private def molMixed {k : ℕ} (σ : Fin k → Bool) : Finset (Fin k × Fin k) :=
  (polyDiags k).filter (fun d => σ d.1 ≠ σ d.2)

/-- An alternating word has even length. -/
private lemma mol_alt_even {k : ℕ} (hk : 1 ≤ k) (σ : Fin k → Bool)
    (halt : ∀ i, σ (finRotate k i) = !σ i) : k % 2 = 0 := by
  have key : ∀ r, σ ((finRotate k)^[r] ⟨0, by omega⟩) =
      if r % 2 = 0 then σ ⟨0, by omega⟩ else !σ ⟨0, by omega⟩ := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Function.iterate_succ_apply', halt, ih]
      rcases Nat.mod_two_eq_zero_or_one r with h | h
      · have : (r + 1) % 2 = 1 := by omega
        simp [h, this]
      · have : (r + 1) % 2 = 0 := by omega
        simp [h, this]
  have h0 : (finRotate k)^[k] ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    apply Fin.ext
    rw [mol_iter_val]
    simp
  have := key k
  rw [h0] at this
  by_contra hodd
  rw [ite_eq_right hodd] at this
  cases h : σ ⟨0, by omega⟩ <;> simp [h] at this

/-- The polygon of Cut_L of an alternating word along a mixed diagonal is alternating. -/
private lemma mol_altL {k : ℕ} (σ : Fin k → Bool) (halt : ∀ i, σ (finRotate k i) = !σ i)
    {i j : Fin k} (hd : (i, j) ∈ polyDiags k) (hmix : σ i ≠ σ j) (p : Fin (k + i - j + 1)) :
    cutLSgn σ i j (finRotate _ p) = !cutLSgn σ i j p := by
  rw [mol_cutLSgn_eq, mol_cutLSgn_eq]
  by_cases hp : p.val = i.val
  · have hpi : p = mol_iL i j := Fin.ext hp
    rw [hpi, mol_vL_rot_iL hd]
    have hvi : mol_vL i j (mol_iL i j) = i := by
      apply Fin.ext; rw [mol_vL_val]; simp [mol_iL]
    rw [hvi]
    revert hmix
    cases σ i <;> cases σ j <;> simp
  · rw [mol_vL_rot hd hp, halt]

/-- The polygon of Cut_R of an alternating word along a mixed diagonal is alternating. -/
private lemma mol_altR {k : ℕ} (σ : Fin k → Bool) (halt : ∀ i, σ (finRotate k i) = !σ i)
    {i j : Fin k} (hd : (i, j) ∈ polyDiags k) (hmix : σ i ≠ σ j) (q : Fin (j - i + 1)) :
    cutRSgn σ i j (finRotate _ q) = !cutRSgn σ i j q := by
  rw [mol_cutRSgn_eq, mol_cutRSgn_eq]
  by_cases hq : q.val = j.val - i.val
  · have hqj : q = mol_lastR i j := Fin.ext hq
    rw [hqj, mol_vR_rot_lastR hd]
    have hvj : mol_vR i j (mol_lastR i j) = j := by
      have hdv := (mol_mem_polyDiags _).mp hd
      simp only at hdv
      apply Fin.ext; rw [mol_vR_val]; simp only [mol_lastR]; omega
    rw [hvj]
    revert hmix
    cases σ i <;> cases σ j <;> simp
  · rw [mol_vR_rot hd hq, halt]

/-- A set of diagonals contained in a dissection containing `(i, j)` is contained in it if and
only if its two parts are contained in the two parts of the dissection. -/
private lemma mol_subset_split {k : ℕ} {i j : Fin k} {D F : Finset (Fin k × Fin k)}
    (hD : D ∈ dissections k) (hdD : (i, j) ∈ D) (hdF : (i, j) ∈ F) :
    D ⊆ F ↔ mol_splitL i j D ⊆ mol_splitL i j F ∧ mol_splitR i j D ⊆ mol_splitR i j F := by
  constructor
  · intro h
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · rw [mol_mem_splitL] at he ⊢
      exact ⟨h he.1, he.2⟩
    · rw [mol_mem_splitR] at he ⊢
      exact ⟨h he.1, he.2⟩
  · rintro ⟨hL, hR⟩ e he
    by_cases hne : e = (i, j)
    · rw [hne]; exact hdF
    rcases mol_cover hD hdD he hne with h | h
    · have hm : (mol_uL i j e.1, mol_uL i j e.2) ∈ mol_splitL i j D := by
        rw [mol_mem_splitL]
        simp only [mol_vL_uL h.1, mol_vL_uL h.2]
        exact ⟨he, hne⟩
      have := ((mol_mem_splitL _).mp (hL hm)).1
      simp only [mol_vL_uL h.1, mol_vL_uL h.2] at this
      exact this
    · have hm : (mol_uR i j e.1, mol_uR i j e.2) ∈ mol_splitR i j D := by
        rw [mol_mem_splitR]
        simp only [mol_vR_uR h.1, mol_vR_uR h.2]
        exact ⟨he, hne⟩
      have := ((mol_mem_splitR _).mp (hR hm)).1
      simp only [mol_vR_uR h.1, mol_vR_uR h.2] at this
      exact this

/-- The mass `Σ_y C_F(y)` of the core of a dissection. -/
private def molMass {L k : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (σ : Fin k → Bool)
    (F : Finset (Fin k × Fin k)) : ℂ :=
  ∑ y, dissCore β M t σ F y

/-- The sum of the masses over the dissections containing a set `D` of diagonals. -/
private def molPhi {L k : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (σ : Fin k → Bool)
    (D : Finset (Fin k × Fin k)) : ℂ :=
  ∑ F ∈ (dissections k).filter (fun F => D ⊆ F), ∑ y, dissCore β M t σ F y

private lemma mol_phi_eq {L k : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    (σ : Fin k → Bool) (D : Finset (Fin k × Fin k)) :
    molPhi β M t σ D = ∑ F ∈ dissections k, if D ⊆ F then molMass β M t σ F else 0 := by
  unfold molPhi
  rw [Finset.sum_filter]
  rfl

variable {g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ} {t : ℝ}

/-- The mixed reduction: `L Φ(σ, D) = βt/(1 - t) Φ_L Φ_R` along a mixed diagonal of `D`. -/
private lemma mol_phi_split (hL : 3 ≤ L) (hm : IsDysonRootV (hopB g) (gammaG g) L E m)
    (ht0 : 0 ≤ t) (ht1 : t < 1) {k : ℕ} (σ : Fin k → Bool) {i j : Fin k}
    (hd : (i, j) ∈ polyDiags k) (hmix : σ i ≠ σ j) {D : Finset (Fin k × Fin k)}
    (hD : D ∈ dissections k) (hdD : (i, j) ∈ D) :
    (L : ℂ) * molPhi (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ D =
      ((gammaG g * t / (1 - t) : ℝ) : ℂ) *
        molPhi (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t (cutLSgn σ i j)
          (mol_splitL i j D) *
        molPhi (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t (cutRSgn σ i j)
          (mol_splitR i j D) := by
  set β := gammaG g
  set M := dysonMat (hopB g) (gammaG g) L E m
  have h1 : molPhi β M t σ D = ∑ F ∈ (dissections k).filter (fun F => (i, j) ∈ F),
      (if D ⊆ F then molMass β M t σ F else 0) := by
    unfold molPhi
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun F _ => ?_
    by_cases hDF : D ⊆ F
    · rw [ite_eq_left hDF, ite_eq_left (hDF hdD), ite_eq_left hDF]
      rfl
    · rw [ite_eq_right hDF]
      split_ifs <;> rfl
  have h2 : ∑ F ∈ (dissections k).filter (fun F => (i, j) ∈ F),
      (if D ⊆ F then molMass β M t σ F else 0) =
      ∑ F ∈ (dissections k).filter (fun F => (i, j) ∈ F),
        (fun FL FR => if mol_splitL i j D ⊆ FL ∧ mol_splitR i j D ⊆ FR then
          (L : ℂ)⁻¹ * (((β * t / (1 - t) : ℝ) : ℂ) * molMass β M t (cutLSgn σ i j) FL *
            molMass β M t (cutRSgn σ i j) FR) else 0) (mol_splitL i j F) (mol_splitR i j F) := by
    refine Finset.sum_congr rfl fun F hF => ?_
    rw [Finset.mem_filter] at hF
    have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
    have hg := mol_mass_glue hL hm ht0 ht1 σ hd hmix hF.1 hF.2
    simp only
    by_cases hDF : D ⊆ F
    · have h' := (mol_subset_split hD hdD hF.2).mp hDF
      rw [ite_eq_left hDF, ite_eq_left h']
      unfold molMass
      rw [← hg, ← mul_assoc, inv_mul_cancel₀ hL0, one_mul]
    · have h' : ¬(mol_splitL i j D ⊆ mol_splitL i j F ∧ mol_splitR i j D ⊆ mol_splitR i j F) :=
        fun h => hDF ((mol_subset_split hD hdD hF.2).mpr h)
      rw [ite_eq_right hDF, ite_eq_right h']
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  rw [h1, h2, mol_sum_split hd (fun FL FR => if mol_splitL i j D ⊆ FL ∧ mol_splitR i j D ⊆ FR then
          (L : ℂ)⁻¹ * (((β * t / (1 - t) : ℝ) : ℂ) * molMass β M t (cutLSgn σ i j) FL *
            molMass β M t (cutRSgn σ i j) FR) else 0)]
  rw [mol_phi_eq, mol_phi_eq]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun FL _ => Finset.sum_congr rfl fun FR _ => ?_
  by_cases hFL : mol_splitL i j D ⊆ FL <;> by_cases hFR : mol_splitR i j D ⊆ FR <;>
    simp only [hFL, hFR, and_self, and_true, and_false, ite_true, ite_false, mul_zero,
      zero_mul]
  field_simp

end Alt

/-! ## The zero mode of the alternating stable molecules -/

section ZeroMode

variable {g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ} {t : ℝ}

/-- The complete core of an alternating word: every external inverse is mixed, with column
sums `(1 - t)⁻¹`, so the masses of all the dissections add up to `(1 - t)^k Σ_a F_k(a; σ)`. -/
private lemma mol_complete_core (hL : 3 ≤ L) (hm : IsDysonRootV (hopB g) (gammaG g) L E m)
    (ht0 : 0 ≤ t) (ht1 : t < 1) {k : ℕ} (hk : 3 ≤ k) (σ : Fin k → Bool)
    (halt : ∀ i, σ (finRotate k i) = !σ i) :
    ∑ F ∈ dissections k, molMass (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ F =
      ((1 - t : ℝ) : ℂ) ^ k * molRow (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t σ := by
  set β := gammaG g
  set M := dysonMat (hopB g) (gammaG g) L E m
  have hδ : ((1 - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show (1 - t) ≠ 0 by linarith)
  have hcol : ∀ (y : Fin k → Fin L) (i : Fin k),
      ∑ x, pairV β M t (σ i) (σ (finRotate k i)) x (y i) = ((1 - t : ℝ) : ℂ)⁻¹ := by
    intro y i
    have hne : σ i ≠ σ (finRotate k i) := by rw [halt]; cases σ i <;> simp
    have hv : pairV β M t (σ i) (σ (finRotate k i)) =
        ((1 - t • pairP β M)⁻¹).map ((↑) : ℝ → ℂ) := by
      unfold pairV; rw [ite_eq_right hne]
    simp only [hv, Matrix.map_apply]
    rw [← Complex.ofReal_sum, mol_mixed_col hL hm ht0 ht1 (y i), Complex.ofReal_inv]
  rw [mol_row_ge3 hk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  unfold molMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_congr rfl fun i _ => hcol y i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hδ, one_pow, one_mul]

/-- The full rows of all the words of length at most `K`, with one constant `A ≥ 1`. -/
private lemma mol_row_bound_upto {c C : ℝ} (hc : 0 < c) (hC : 1 ≤ C) (K : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ k, 1 ≤ k → k ≤ K → ∀ (g : ℝ) (L : ℕ) (E : ℝ) (m : ℂ) (t a : ℝ),
      MolHyp g L E m t a c C → t < 1 → ∀ σ : Fin k → Bool,
        ‖molRow (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t σ‖ ≤
          A * L * a ^ (k - 1) * ((1 - t) ^ (k - 1))⁻¹ := by
  induction K with
  | zero => exact ⟨1, le_rfl, fun k hk hkK => absurd hkK (by omega)⟩
  | succ K ih =>
    obtain ⟨A, hA, hAb⟩ := ih
    obtain ⟨B, hB, hBb⟩ := mol_row_bound hc hC (K + 1) (by omega)
    refine ⟨max A B, le_max_of_le_left hA, fun k hk hkK g L E m t a h ht1 σ => ?_⟩
    have ha := h.ha
    have hδ : 0 < 1 - t := by linarith
    have hX : 0 ≤ (L : ℝ) * a ^ (k - 1) * ((1 - t) ^ (k - 1))⁻¹ := by positivity
    rcases Nat.lt_or_ge k (K + 1) with hlt | hge
    · calc _ ≤ A * L * a ^ (k - 1) * ((1 - t) ^ (k - 1))⁻¹ :=
            hAb k hk (by omega) g L E m t a h ht1 σ
        _ = A * ((L : ℝ) * a ^ (k - 1) * ((1 - t) ^ (k - 1))⁻¹) := by ring
        _ ≤ max A B * ((L : ℝ) * a ^ (k - 1) * ((1 - t) ^ (k - 1))⁻¹) := by
            gcongr; exact le_max_left _ _
        _ = _ := by ring
    · obtain rfl : k = K + 1 := by omega
      calc _ ≤ B * L * a ^ (K + 1 - 1) * ((1 - t) ^ (K + 1 - 1))⁻¹ := hBb g L E m t a h ht1 σ
        _ = B * ((L : ℝ) * a ^ (K + 1 - 1) * ((1 - t) ^ (K + 1 - 1))⁻¹) := by ring
        _ ≤ max A B * ((L : ℝ) * a ^ (K + 1 - 1) * ((1 - t) ^ (K + 1 - 1))⁻¹) := by
            gcongr; exact le_max_right _ _
        _ = _ := by ring

/-- `molPhi` over the empty set is the complete core. -/
private lemma mol_phi_empty {L k : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    (σ : Fin k → Bool) : molPhi β M t σ ∅ = ∑ F ∈ dissections k, molMass β M t σ F := by
  unfold molPhi molMass
  rw [Finset.filter_true_of_mem fun F _ => Finset.empty_subset F]

/-- The masses over the dissections containing a set of mixed diagonals, for alternating words
of length at most `K`: `‖Φ(σ, D)‖ ≤ A^{k-3}L(1 - t)a^{k-1}`. -/
private lemma mol_phi_bound {c C : ℝ} {A : ℝ} (hA : 1 ≤ A) {K : ℕ}
    (hAb : ∀ k, 1 ≤ k → k ≤ K → ∀ (g : ℝ) (L : ℕ) (E : ℝ) (m : ℂ) (t a : ℝ),
      MolHyp g L E m t a c C → t < 1 → ∀ σ : Fin k → Bool,
        ‖molRow (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t σ‖ ≤
          A * L * a ^ (k - 1) * ((1 - t) ^ (k - 1))⁻¹)
    {a : ℝ} (h : MolHyp g L E m t a c C) (ht1 : t < 1) :
    ∀ k, 3 ≤ k → k ≤ K → ∀ σ : Fin k → Bool, (∀ i, σ (finRotate k i) = !σ i) →
      ∀ D ∈ dissections k, D ⊆ molMixed σ →
        ‖molPhi (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ D‖ ≤
          A ^ (k - 3) * L * (1 - t) * a ^ (k - 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk hkK σ halt D hD hDm
  have ha := h.ha
  have ha0 : 0 < a := by linarith
  have hδ : 0 < 1 - t := by linarith
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by have := h.hL; omega)
  have hev := mol_alt_even (by omega) σ halt
  have hk4 : 4 ≤ k := by omega
  rcases D.eq_empty_or_nonempty with rfl | ⟨⟨u, w⟩, hdD⟩
  · rw [mol_phi_empty, mol_complete_core h.hL h.root h.ht0 ht1 (by omega) σ halt, norm_mul,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    have hR := hAb k (by omega) hkK g L E m t a h ht1 σ
    have hpow : (1 - t) ^ k * ((1 - t) ^ (k - 1))⁻¹ = 1 - t := by
      have e : (1 - t) ^ k = (1 - t) ^ (k - 1) * (1 - t) := by
        rw [← pow_succ]; congr 1; omega
      rw [e]
      have : (1 - t) ^ (k - 1) ≠ 0 := by positivity
      field_simp
    have hAk : A ≤ A ^ (k - 3) := by
      calc A = A ^ 1 := (pow_one A).symm
        _ ≤ A ^ (k - 3) := pow_le_pow_right₀ hA (by omega)
    calc (1 - t) ^ k * ‖molRow (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t σ‖
        ≤ (1 - t) ^ k * (A * L * a ^ (k - 1) * ((1 - t) ^ (k - 1))⁻¹) := by gcongr
      _ = A * L * a ^ (k - 1) * ((1 - t) ^ k * ((1 - t) ^ (k - 1))⁻¹) := by ring
      _ = A * L * (1 - t) * a ^ (k - 1) := by rw [hpow]; ring
      _ ≤ A ^ (k - 3) * L * (1 - t) * a ^ (k - 1) := by gcongr
  · have hdP : (u, w) ∈ polyDiags k := ((mol_mem_dissections D).mp hD).1 hdD
    have hmix : σ u ≠ σ w := (Finset.mem_filter.mp (hDm hdD)).2
    have hdv := (mol_mem_polyDiags _).mp hdP
    simp only at hdv
    have hw := w.isLt
    set k1 := k + (u : ℕ) - (w : ℕ) + 1 with hk1
    set k2 := (w : ℕ) - (u : ℕ) + 1 with hk2
    have hk1lt : k1 < k := by omega
    have hk2lt : k2 < k := by omega
    have hk13 : 3 ≤ k1 := by omega
    have hk23 : 3 ≤ k2 := by omega
    have hsum : k1 + k2 = k + 2 := by omega
    have hDL : mol_splitL u w D ∈ dissections k1 := mol_splitL_mem hdP hD
    have hDR : mol_splitR u w D ∈ dissections k2 := mol_splitR_mem hdP hD
    have hDLm : mol_splitL u w D ⊆ molMixed (cutLSgn σ u w) := by
      intro e he
      have he' := (mol_mem_splitL _).mp he
      have h1 := (Finset.mem_filter.mp (hDm he'.1)).2
      refine Finset.mem_filter.mpr ⟨((mol_mem_dissections _).mp hDL).1 he, ?_⟩
      rw [mol_cutLSgn_eq, mol_cutLSgn_eq]
      exact h1
    have hDRm : mol_splitR u w D ⊆ molMixed (cutRSgn σ u w) := by
      intro e he
      have he' := (mol_mem_splitR _).mp he
      have h1 := (Finset.mem_filter.mp (hDm he'.1)).2
      refine Finset.mem_filter.mpr ⟨((mol_mem_dissections _).mp hDR).1 he, ?_⟩
      rw [mol_cutRSgn_eq, mol_cutRSgn_eq]
      exact h1
    have hL1 := ih k1 hk1lt hk13 (by omega) (cutLSgn σ u w) (mol_altL σ halt hdP hmix) _ hDL hDLm
    have hR1 := ih k2 hk2lt hk23 (by omega) (cutRSgn σ u w) (mol_altR σ halt hdP hmix) _ hDR hDRm
    have hsplit := mol_phi_split h.hL h.root h.ht0 ht1 σ hdP hmix hD hdD
    have hβ := h.beta_pos
    have hβt : gammaG g * t / (1 - t) ≤ 1 / (a * (1 - t)) := by
      rw [div_le_div_iff₀ hδ (by positivity)]
      have h1 : gammaG g * a * t ≤ 1 := by nlinarith [h.beta_le, h.ht0, h.ht1]
      nlinarith [mul_le_mul_of_nonneg_right h1 hδ.le]
    have hβt0 : 0 ≤ gammaG g * t / (1 - t) := by
      have := h.ht0; positivity
    have hnorm : (L : ℝ) * ‖molPhi (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ D‖ ≤
        1 / (a * (1 - t)) * (A ^ (k1 - 3) * L * (1 - t) * a ^ (k1 - 1)) *
          (A ^ (k2 - 3) * L * (1 - t) * a ^ (k2 - 1)) := by
      have := congrArg norm hsplit
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hβt0] at this
      rw [this]
      gcongr
    have hexpA : A ^ (k1 - 3) * A ^ (k2 - 3) ≤ A ^ (k - 3) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hA (by omega)
    have hexpa : a ^ (k1 - 1) * a ^ (k2 - 1) = a * a ^ (k - 1) := by
      rw [← pow_add, ← pow_succ']
      congr 1
      omega
    have hgoal : 1 / (a * (1 - t)) * (A ^ (k1 - 3) * L * (1 - t) * a ^ (k1 - 1)) *
        (A ^ (k2 - 3) * L * (1 - t) * a ^ (k2 - 1)) =
          L * (A ^ (k1 - 3) * A ^ (k2 - 3) * L * (1 - t) * a ^ (k - 1)) := by
      have e1 : 1 / (a * (1 - t)) * (A ^ (k1 - 3) * L * (1 - t) * a ^ (k1 - 1)) *
          (A ^ (k2 - 3) * L * (1 - t) * a ^ (k2 - 1)) = A ^ (k1 - 3) * A ^ (k2 - 3) * L * L *
            (1 - t) * (1 - t) * (a ^ (k1 - 1) * a ^ (k2 - 1)) / (a * (1 - t)) := by ring
      rw [e1, hexpa]
      field_simp
    rw [hgoal] at hnorm
    have h2 := le_of_mul_le_mul_left hnorm hL0
    calc _ ≤ A ^ (k1 - 3) * A ^ (k2 - 3) * L * (1 - t) * a ^ (k - 1) := h2
      _ ≤ A ^ (k - 3) * L * (1 - t) * a ^ (k - 1) := by gcongr

end ZeroMode

/-! ## The mass of the alternating stable molecules -/

section StableMass

/-- Inclusion–exclusion over the mixed diagonals: the sum over the stable dissections is the
alternating sum, over the sets `D` of mixed diagonals, of the sums over the dissections
containing `D`. -/
private lemma mol_incl_excl {k : ℕ} (σ : Fin k → Bool) (f : Finset (Fin k × Fin k) → ℂ) :
    ∑ F ∈ (dissections k).filter (fun F => ∀ d ∈ F, σ d.1 = σ d.2), f F =
      ∑ D ∈ (molMixed σ).powerset,
        (-1 : ℂ) ^ D.card * ∑ F ∈ (dissections k).filter (fun F => D ⊆ F), f F := by
  have hF : ∀ F ∈ dissections k,
      (∑ D ∈ (F.filter (fun d => σ d.1 ≠ σ d.2)).powerset, (-1 : ℂ) ^ D.card) * f F =
        if (∀ d ∈ F, σ d.1 = σ d.2) then f F else 0 := by
    intro F _
    have hz : (∑ D ∈ (F.filter (fun d => σ d.1 ≠ σ d.2)).powerset, (-1 : ℂ) ^ D.card) =
        ((∑ D ∈ (F.filter (fun d => σ d.1 ≠ σ d.2)).powerset, (-1 : ℤ) ^ D.card : ℤ) : ℂ) := by
      push_cast; rfl
    rw [hz, Finset.sum_powerset_neg_one_pow_card]
    by_cases h : ∀ d ∈ F, σ d.1 = σ d.2
    · have he : F.filter (fun d => σ d.1 ≠ σ d.2) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun d hd => not_not.mpr (h d hd)
      rw [ite_eq_left he, ite_eq_left h, Int.cast_one, one_mul]
    · have he : F.filter (fun d => σ d.1 ≠ σ d.2) ≠ ∅ := by
        intro he
        apply h
        intro d hd
        by_contra hne
        have : d ∈ F.filter (fun d => σ d.1 ≠ σ d.2) := Finset.mem_filter.mpr ⟨hd, hne⟩
        rw [he] at this
        exact absurd this (Finset.notMem_empty d)
      rw [ite_eq_right he, ite_eq_right h, Int.cast_zero, zero_mul]
  rw [Finset.sum_filter, ← Finset.sum_congr rfl hF]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_comm' fun F D => ?_
  simp only [Finset.mem_powerset, Finset.mem_filter, molMixed]
  constructor
  · rintro ⟨hFd, hD⟩
    refine ⟨⟨hFd, fun d hd => (Finset.mem_filter.mp (hD hd)).1⟩, fun d hd => ?_⟩
    have h1 := Finset.mem_filter.mp (hD hd)
    exact Finset.mem_filter.mpr ⟨((mol_mem_dissections F).mp hFd).1 h1.1, h1.2⟩
  · rintro ⟨⟨hFd, hDF⟩, hD⟩
    exact ⟨hFd, fun d hd => Finset.mem_filter.mpr ⟨hDF hd, (Finset.mem_filter.mp (hD hd)).2⟩⟩

/-- The mass of the alternating stable molecules: `‖Σ_y S(y)‖ ≤ B L (1 - t) a^{k-1}`, the zero
mode of (B.3) [ba:eq:cancel] and (B.9) [uvp:eq:mass]. -/
private lemma mol_stable_mass {c C : ℝ} (hc : 0 < c) (hC : 1 ≤ C) (k : ℕ) (hk : 3 ≤ k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (g : ℝ) (L : ℕ) (E : ℝ) (m : ℂ) (t a : ℝ), MolHyp g L E m t a c C →
      t < 1 → ∀ σ : Fin k → Bool, (∀ i, σ (finRotate k i) = !σ i) →
        ‖∑ y, stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖ ≤
          B * L * (1 - t) * a ^ (k - 1) := by
  obtain ⟨A, hA, hAb⟩ := mol_row_bound_upto hc hC k
  refine ⟨2 ^ (k * k) * A ^ (k - 3), by positivity, fun g L E m t a h ht1 σ halt => ?_⟩
  set β := gammaG g
  set M := dysonMat (hopB g) (gammaG g) L E m
  have ha0 : 0 < a := by linarith [h.ha]
  have hδ : 0 < 1 - t := by linarith
  set X := A ^ (k - 3) * L * (1 - t) * a ^ (k - 1) with hX
  have hX0 : 0 ≤ X := by positivity
  have hsum : ∑ y, stableMol β M t σ y = ∑ D ∈ (molMixed σ).powerset,
      (-1 : ℂ) ^ D.card * molPhi β M t σ D := by
    unfold stableMol
    rw [Finset.sum_comm]
    exact mol_incl_excl σ (fun F => ∑ y, dissCore β M t σ F y)
  have hD : ∀ D ∈ (molMixed σ).powerset, ‖molPhi β M t σ D‖ ≤ X := by
    intro D hDp
    have hDm : D ⊆ molMixed σ := Finset.mem_powerset.mp hDp
    by_cases hDd : D ∈ dissections k
    · exact mol_phi_bound hA hAb h ht1 k hk le_rfl σ halt D hDd hDm
    · have h0 : molPhi β M t σ D = 0 := by
        unfold molPhi
        rw [Finset.sum_eq_zero]
        intro F hF
        exfalso
        obtain ⟨hFd, hDF⟩ := Finset.mem_filter.mp hF
        apply hDd
        rw [mol_mem_dissections] at hFd ⊢
        exact ⟨hDF.trans hFd.1, fun d hd e he => hFd.2 d (hDF hd) e (hDF he)⟩
      rw [h0, norm_zero]
      exact hX0
  have hcard : ((molMixed σ).powerset.card : ℝ) ≤ 2 ^ (k * k) := by
    rw [Finset.card_powerset]
    have h1 : (molMixed σ).card ≤ k * k := by
      have := Finset.card_le_univ (molMixed σ)
      rwa [Fintype.card_prod, Fintype.card_fin] at this
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) h1
  rw [hsum]
  calc ‖∑ D ∈ (molMixed σ).powerset, (-1 : ℂ) ^ D.card * molPhi β M t σ D‖
      ≤ ∑ D ∈ (molMixed σ).powerset, X := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun D hDp => ?_)
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact hD D hDp
    _ = (molMixed σ).powerset.card * X := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (k * k) * X := by gcongr
    _ = 2 ^ (k * k) * A ^ (k - 3) * L * (1 - t) * a ^ (k - 1) := by rw [hX]; ring

end StableMass

/-! ## The second-order Taylor bound of the normalized transform -/

section Taylor

/-- With symmetric representatives of the momenta and of the displacements from `x_0`, the phase
of the grid character at `Σ_j n_j ≡ 0` is small:
`1 - cos(2πΣ_j n_j x_j/L) ≤ (k/2)(Σ_j |n_j|_𝕋²) diam(x)²`. -/
private lemma mol_one_sub_cos {L k : ℕ} [NeZero L] (hk : 1 ≤ k) (n x : Fin k → Fin L)
    (hn : (∑ j, (n j : ℕ)) % L = 0) :
    1 - Real.cos (2 * π * (∑ j, ((n j : ℕ) : ℝ) * ((x j : ℕ) : ℝ)) / L) ≤
      (k / 2 : ℝ) * (∑ j, torusAbs L (n j) ^ 2) * (wordDiam x : ℝ) ^ 2 := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set x0 := x ⟨0, by omega⟩
  set N : Fin k → ℤ := fun j =>
    if (n j : ℕ) ≤ L - (n j : ℕ) then ((n j : ℕ) : ℤ) else ((n j : ℕ) : ℤ) - L with hN
  set u : Fin k → ℕ := fun j => ((x j : ℕ) + L - (x0 : ℕ)) % L with hu
  set w : Fin k → ℕ := fun j => ((x0 : ℕ) + L - (x j : ℕ)) % L with hw
  set Z : Fin k → ℤ := fun j => if u j ≤ w j then (u j : ℤ) else -(w j : ℤ) with hZ
  have hNabs : ∀ j, |(N j : ℝ)| = ((min (n j : ℕ) (L - (n j : ℕ)) : ℕ) : ℝ) := by
    intro j
    have := (n j).isLt
    simp only [hN]
    split_ifs with h
    · rw [min_eq_left h]; push_cast; exact abs_of_nonneg (by positivity)
    · rw [min_eq_right (by omega)]
      have hlt : ((n j : ℕ) : ℝ) < L := by exact_mod_cast (n j).isLt
      push_cast
      rw [abs_of_neg (by linarith), Nat.cast_sub (by omega)]
      ring
  have hZabs : ∀ j, |(Z j : ℝ)| = (cycDist (x j) x0 : ℝ) := by
    intro j
    simp only [hZ, cycDist, hu, hw]
    split_ifs with h
    · rw [min_eq_left h, Int.cast_natCast]; exact abs_of_nonneg (Nat.cast_nonneg _)
    · rw [min_eq_right (by omega), Int.cast_neg, Int.cast_natCast, abs_neg]
      exact abs_of_nonneg (Nat.cast_nonneg _)
  -- the two phases differ by a multiple of `2π`
  have hdvd : (L : ℤ) ∣ (∑ j, ((n j : ℕ) : ℤ) * ((x j : ℕ) : ℤ)) - ∑ j, N j * Z j := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hNz : ∀ j, ((N j : ℤ) : ZMod L) = ((n j : ℕ) : ZMod L) := by
      intro j
      simp only [hN]
      split_ifs
      · push_cast; rfl
      · push_cast; rw [ZMod.natCast_self, sub_zero]
    have hZz : ∀ j, ((Z j : ℤ) : ZMod L) = ((x j : ℕ) : ZMod L) - ((x0 : ℕ) : ZMod L) := by
      intro j
      have h1 := (x j).isLt
      have h2 := x0.isLt
      simp only [hZ, hu, hw]
      split_ifs
      · push_cast
        rw [Nat.cast_sub (by omega)]
        push_cast
        rw [ZMod.natCast_self]
        ring
      · push_cast
        rw [Nat.cast_sub (by omega)]
        push_cast
        rw [ZMod.natCast_self]
        ring
    have hsum0 : (∑ j, ((n j : ℕ) : ZMod L)) = 0 := by
      have : ((∑ j, (n j : ℕ) : ℕ) : ZMod L) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact Nat.dvd_of_mod_eq_zero hn
      push_cast at this
      exact this
    simp only [Int.cast_sub, Int.cast_sum, Int.cast_mul, Int.cast_natCast, hNz, hZz]
    rw [← Finset.sum_sub_distrib]
    simp only [show ∀ a b c : ZMod L, a * b - a * (b - c) = a * c from fun a b c => by ring]
    rw [← Finset.sum_mul, hsum0, zero_mul]
  obtain ⟨q, hq⟩ := hdvd
  set ψ : ℝ := 2 * π * (∑ j, (N j : ℝ) * (Z j : ℝ)) / L with hψ
  have hφ : 2 * π * (∑ j, ((n j : ℕ) : ℝ) * ((x j : ℕ) : ℝ)) / L = ψ + q * (2 * π) := by
    have hq' : (∑ j, ((n j : ℕ) : ℝ) * ((x j : ℕ) : ℝ)) - ∑ j, (N j : ℝ) * (Z j : ℝ) =
        L * q := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hq
      push_cast at this
      exact this
    have : (∑ j, ((n j : ℕ) : ℝ) * ((x j : ℕ) : ℝ)) = (∑ j, (N j : ℝ) * (Z j : ℝ)) + L * q := by
      linarith
    rw [this, hψ]
    field_simp
  rw [hφ, Real.cos_add_int_mul_two_pi]
  have hcos : 1 - Real.cos ψ ≤ ψ ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := ψ)]
  set τ : Fin k → ℝ := fun j => torusAbs L (n j) with hτ
  set D : ℝ := (wordDiam x : ℝ)
  have hτ0 : ∀ j, 0 ≤ τ j := fun j => by simp only [hτ, torusAbs]; positivity
  have hψb : |ψ| ≤ D * ∑ j, τ j := by
    have h1 : |∑ j, (N j : ℝ) * (Z j : ℝ)| ≤ ∑ j, |(N j : ℝ)| * |(Z j : ℝ)| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun j _ => abs_mul _ _
    have h2 : ∀ j, 2 * π / L * (|(N j : ℝ)| * |(Z j : ℝ)|) ≤ τ j * D := by
      intro j
      rw [hNabs, hZabs]
      have hd : (cycDist (x j) x0 : ℝ) ≤ D := by
        have := mol_le_wordDiam x j ⟨0, by omega⟩
        change ((cycDist (x j) x0 : ℕ) : ℝ) ≤ (wordDiam x : ℝ)
        exact_mod_cast this
      simp only [hτ, torusAbs]
      calc 2 * π / L * (((min (n j : ℕ) (L - (n j : ℕ)) : ℕ) : ℝ) * (cycDist (x j) x0 : ℝ))
          = 2 * π * ((min (n j : ℕ) (L - (n j : ℕ)) : ℕ) : ℝ) / L * (cycDist (x j) x0 : ℝ) := by
            ring
        _ ≤ 2 * π * ((min (n j : ℕ) (L - (n j : ℕ)) : ℕ) : ℝ) / L * D := by gcongr
    calc |ψ| = 2 * π / L * |∑ j, (N j : ℝ) * (Z j : ℝ)| := by
          rw [hψ, mul_div_right_comm, abs_mul, abs_of_pos (by positivity)]
      _ ≤ 2 * π / L * ∑ j, |(N j : ℝ)| * |(Z j : ℝ)| := by gcongr
      _ = ∑ j, 2 * π / L * (|(N j : ℝ)| * |(Z j : ℝ)|) := by rw [Finset.mul_sum]
      _ ≤ ∑ j, τ j * D := Finset.sum_le_sum fun j _ => h2 j
      _ = D * ∑ j, τ j := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  have hcs : (∑ j, τ j) ^ 2 ≤ k * ∑ j, τ j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k))) (f := τ)
    simpa using this
  have hsq : ψ ^ 2 ≤ D ^ 2 * (k * ∑ j, τ j ^ 2) := by
    have h1 : ψ ^ 2 ≤ (D * ∑ j, τ j) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hψb 2
    calc ψ ^ 2 ≤ (D * ∑ j, τ j) ^ 2 := h1
      _ = D ^ 2 * (∑ j, τ j) ^ 2 := by ring
      _ ≤ D ^ 2 * (k * ∑ j, τ j ^ 2) := by gcongr
  calc 1 - Real.cos ψ ≤ ψ ^ 2 / 2 := hcos
    _ ≤ D ^ 2 * (k * ∑ j, τ j ^ 2) / 2 := by gcongr
    _ = (k / 2 : ℝ) * (∑ j, τ j ^ 2) * D ^ 2 := by ring

/-- The second-order Taylor bound of the normalized transform of a reflection-invariant
tensor at `Σ_j n_j ≡ 0`: `‖Ŝ(n)‖ ≤ ‖L⁻¹Σ_y S(y)‖ + (k/2)(Σ_j |n_j|_𝕋²) L⁻¹Σ_y diam(y)²‖S(y)‖`. -/
lemma mol_taylor {L k : ℕ} [NeZero L] (hk : 1 ≤ k) (S : (Fin k → Fin L) → ℂ)
    (hS : ∀ y, S (fun i => -y i) = S y) (n : Fin k → Fin L)
    (hn : (∑ j, (n j : ℕ)) % L = 0) :
    ‖tensorFourier S n‖ ≤ ‖(L : ℂ)⁻¹ * ∑ y, S y‖ +
      (k / 2 : ℝ) * (∑ j, torusAbs L (n j) ^ 2) *
        ((L : ℝ)⁻¹ * ∑ y, (wordDiam y : ℝ) ^ 2 * ‖S y‖) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set φ : (Fin k → Fin L) → ℝ :=
    fun y => 2 * π * (∑ j, ((n j : ℕ) : ℝ) * ((y j : ℕ) : ℝ)) / L with hφ
  have hexp : ∀ y : Fin k → Fin L,
      Complex.exp (-(2 * π * I * ∑ j, ((n j : ℕ) : ℂ) * ((y j : ℕ) : ℂ) / L)) =
        Complex.exp ((-(φ y) : ℝ) * I) := by
    intro y
    congr 1
    simp only [hφ]
    rw [← Finset.sum_div]
    push_cast
    ring
  have hT : tensorFourier S n = (L : ℂ)⁻¹ * ∑ y, S y * Complex.exp ((-(φ y) : ℝ) * I) := by
    unfold tensorFourier
    simp only [hexp]
  -- the reflected phase
  have hneg : ∀ y : Fin k → Fin L, ∃ q : ℤ, φ (fun i => -y i) = -φ y + q * (2 * π) := by
    intro y
    refine ⟨∑ j, ((n j : ℕ) : ℤ) * (if (y j : ℕ) = 0 then 0 else 1), ?_⟩
    have hv : ∀ j, (((-y j : Fin L) : ℕ) : ℝ) =
        (L : ℝ) * (if (y j : ℕ) = 0 then 0 else 1) - ((y j : ℕ) : ℝ) := by
      intro j
      rw [Fin.val_neg']
      have := (y j).isLt
      split_ifs with h
      · rw [h]; simp
      · rw [Nat.mod_eq_of_lt (by omega), Nat.cast_sub (by omega)]; ring
    simp only [hφ, hv]
    push_cast
    field_simp
    rw [← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  have hrefl : ∑ y, S y * Complex.exp ((-(φ y) : ℝ) * I) =
      ∑ y, S y * Complex.exp ((φ y : ℝ) * I) := by
    refine Fintype.sum_equiv (Equiv.piCongrRight fun _ => Equiv.neg (Fin L)) _ _ fun y => ?_
    change S y * Complex.exp ((-(φ y) : ℝ) * I) =
      S (fun i => -y i) * Complex.exp ((φ (fun i => -y i) : ℝ) * I)
    obtain ⟨q, hq⟩ := hneg y
    rw [hS, hq]
    congr 1
    have e : (((-φ y + q * (2 * π)) : ℝ) : ℂ) * I =
        ((-(φ y) : ℝ) : ℂ) * I + (q : ℤ) * (2 * π * I) := by
      push_cast; ring
    rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hcos : ∀ y, Complex.exp ((-(φ y) : ℝ) * I) =
      ((Real.cos (φ y) : ℝ) : ℂ) * 2 - Complex.exp ((φ y : ℝ) * I) := by
    intro y
    rw [Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  have hT2 : tensorFourier S n = (L : ℂ)⁻¹ * ∑ y, S y * ((Real.cos (φ y) : ℝ) : ℂ) := by
    rw [hT]
    congr 1
    have h2 : (2 : ℂ) * ∑ y, S y * Complex.exp ((-(φ y) : ℝ) * I) =
        2 * ∑ y, S y * ((Real.cos (φ y) : ℝ) : ℂ) := by
      calc (2 : ℂ) * ∑ y, S y * Complex.exp ((-(φ y) : ℝ) * I)
          = ∑ y, S y * Complex.exp ((-(φ y) : ℝ) * I) +
              ∑ y, S y * Complex.exp ((φ y : ℝ) * I) := by rw [← hrefl]; ring
        _ = ∑ y, (S y * Complex.exp ((-(φ y) : ℝ) * I) + S y * Complex.exp ((φ y : ℝ) * I)) := by
            rw [Finset.sum_add_distrib]
        _ = ∑ y, 2 * (S y * ((Real.cos (φ y) : ℝ) : ℂ)) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [hcos y]; ring
        _ = 2 * ∑ y, S y * ((Real.cos (φ y) : ℝ) : ℂ) := by rw [Finset.mul_sum]
    exact mul_left_cancel₀ two_ne_zero h2
  have hdiff : tensorFourier S n - (L : ℂ)⁻¹ * ∑ y, S y =
      (L : ℂ)⁻¹ * ∑ y, S y * (((Real.cos (φ y) : ℝ) : ℂ) - 1) := by
    rw [hT2, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun y _ => by ring
  set T := ∑ j, torusAbs L (n j) ^ 2 with hTdef
  have hbound : ‖tensorFourier S n - (L : ℂ)⁻¹ * ∑ y, S y‖ ≤
      (k / 2 : ℝ) * (∑ j, torusAbs L (n j) ^ 2) *
        ((L : ℝ)⁻¹ * ∑ y, (wordDiam y : ℝ) ^ 2 * ‖S y‖) := by
    rw [hdiff, norm_mul, norm_inv, Complex.norm_natCast]
    have h1 : ‖∑ y, S y * (((Real.cos (φ y) : ℝ) : ℂ) - 1)‖ ≤
        ∑ y, ‖S y‖ * ((k / 2 : ℝ) * (∑ j, torusAbs L (n j) ^ 2) * (wordDiam y : ℝ) ^ 2) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
      rw [norm_mul]
      gcongr
      have e : ((Real.cos (φ y) : ℝ) : ℂ) - 1 = ((Real.cos (φ y) - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith [Real.cos_le_one (φ y)])]
      have := mol_one_sub_cos hk n y hn
      simp only [hφ]
      linarith
    calc (L : ℝ)⁻¹ * ‖∑ y, S y * (((Real.cos (φ y) : ℝ) : ℂ) - 1)‖
        ≤ (L : ℝ)⁻¹ * ∑ y, ‖S y‖ * ((k / 2 : ℝ) * (∑ j, torusAbs L (n j) ^ 2) *
            (wordDiam y : ℝ) ^ 2) := by gcongr
      _ = _ := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => by ring
  calc ‖tensorFourier S n‖ = ‖(L : ℂ)⁻¹ * ∑ y, S y +
        (tensorFourier S n - (L : ℂ)⁻¹ * ∑ y, S y)‖ := by ring_nf
    _ ≤ ‖(L : ℂ)⁻¹ * ∑ y, S y‖ + ‖tensorFourier S n - (L : ℂ)⁻¹ * ∑ y, S y‖ := norm_add_le _ _
    _ ≤ _ := by gcongr

end Taylor


/-- (B.3) [ba:eq:cancel], Lemma B.1 [ba:lem:moment]: the alternating stable molecule vanishes
to second order at zero momentum, up to `1 - t`. -/
theorem stableMol_bdd_cancel (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') (k : ℕ)
    (hk : 4 ≤ k) :
    ∃ C' : ℝ, ∃ L₀ : ℕ, 0 < C' ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Fin k → Bool, (∀ i, σ (finRotate k i) = !σ i) →
      ∀ n : Fin k → Fin L, (∑ j, (n j : ℕ)) % L = 0 →
        ‖tensorFourier (stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ) n‖ ≤
          C' * ((1 - t) + ∑ j, torusAbs L (n j) ^ 2) := by
  obtain ⟨c₁, Ck, L₀, hc₁, hCk, H⟩ := mol_bdd_hyp C B₀ c' hC hB₀ hc'
  obtain ⟨B, hB, hBb⟩ := mol_stable_mass hc₁ hCk k (by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  set c₃ := c₁ / (12 * k ^ 2) with hc₃
  have hc₃0 : 0 < c₃ := by positivity
  set CS := molCS k c₁ Ck
  have hCS : 0 ≤ CS := molCS_nonneg k hc₁ (by linarith)
  set G : ℝ := (2 * (1 + k / (c₃ / 2)) * 1) ^ (k - 1)
  have hG : 0 ≤ G := by positivity
  set M2 : ℝ := CS * (8 / c₃ ^ 2) * G
  have hM2 : 0 ≤ M2 := by positivity
  refine ⟨max B (k / 2 * M2) + 1, L₀, by positivity, ?_⟩
  intro g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1 σ halt n hn
  have h := H g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1.le
  have : NeZero L := ⟨by omega⟩
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hδ : 0 < 1 - t := by linarith
  set S := stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ with hSdef
  have hS : ∀ y, S (fun i => -y i) = S y := fun y => (stableMol_symm g L hL E m hm t σ y 0).2
  have hT := mol_taylor (by omega) S hS n hn
  -- the zero mode
  have hmass : ‖(L : ℂ)⁻¹ * ∑ y, S y‖ ≤ B * (1 - t) := by
    have := hBb g L E m t 1 h ht1 σ halt
    rw [one_pow, mul_one] at this
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (L : ℝ)⁻¹ * ‖∑ y, S y‖ ≤ (L : ℝ)⁻¹ * (B * L * (1 - t)) := by gcongr
      _ = B * (1 - t) := by field_simp
  -- the second moment
  have hmom : (L : ℝ)⁻¹ * ∑ y, (wordDiam y : ℝ) ^ 2 * ‖S y‖ ≤ M2 := by
    have hpt : ∀ y : Fin k → Fin L, (wordDiam y : ℝ) ^ 2 * ‖S y‖ ≤
        CS * (8 / c₃ ^ 2) * Real.exp (-(c₃ / 2 * wordDiam y / 1)) := by
      intro y
      set D : ℝ := (wordDiam y : ℝ)
      have hD : 0 ≤ D := Nat.cast_nonneg _
      have hS1 : ‖S y‖ ≤ CS * Real.exp (-(c₃ * D)) := by
        have := h.stable_profile (by omega) σ y
        simpa only [div_one] using this
      have hD2 : D ^ 2 ≤ 8 / c₃ ^ 2 * Real.exp (c₃ / 2 * D) := by
        have h1 := Real.pow_div_factorial_le_exp (c₃ / 2 * D) (by positivity) 2
        simp only [Nat.factorial_two, Nat.cast_ofNat] at h1
        rw [div_le_iff₀ (by norm_num)] at h1
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      have e1 : Real.exp (c₃ / 2 * D) * Real.exp (-(c₃ * D)) = Real.exp (-(c₃ / 2 * D / 1)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc D ^ 2 * ‖S y‖ ≤ (8 / c₃ ^ 2 * Real.exp (c₃ / 2 * D)) * (CS * Real.exp (-(c₃ * D))) := by
            gcongr
        _ = CS * (8 / c₃ ^ 2) * (Real.exp (c₃ / 2 * D) * Real.exp (-(c₃ * D))) := by ring
        _ = CS * (8 / c₃ ^ 2) * Real.exp (-(c₃ / 2 * D / 1)) := by rw [e1]
    have hfull := mol_full_sum (L := L) (k := k) (by omega) (c := c₃ / 2) (a := 1)
      (by positivity) le_rfl
    calc (L : ℝ)⁻¹ * ∑ y, (wordDiam y : ℝ) ^ 2 * ‖S y‖
        ≤ (L : ℝ)⁻¹ * ∑ y : Fin k → Fin L, CS * (8 / c₃ ^ 2) *
            Real.exp (-(c₃ / 2 * wordDiam y / 1)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hpt y) (by positivity)
      _ = (L : ℝ)⁻¹ * (CS * (8 / c₃ ^ 2) * ∑ y : Fin k → Fin L,
            Real.exp (-(c₃ / 2 * wordDiam y / 1))) := by rw [← Finset.mul_sum]
      _ ≤ (L : ℝ)⁻¹ * (CS * (8 / c₃ ^ 2) * (L * G)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfull (by positivity))
            (by positivity)
      _ = M2 := by
          have hc₃ne : c₃ ≠ 0 := hc₃0.ne'
          simp only [M2]
          field_simp
  have hτ : 0 ≤ ∑ j, torusAbs L (n j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  calc ‖tensorFourier S n‖ ≤ ‖(L : ℂ)⁻¹ * ∑ y, S y‖ + (k / 2 : ℝ) * (∑ j, torusAbs L (n j) ^ 2) *
        ((L : ℝ)⁻¹ * ∑ y, (wordDiam y : ℝ) ^ 2 * ‖S y‖) := hT
    _ ≤ B * (1 - t) + (k / 2 : ℝ) * (∑ j, torusAbs L (n j) ^ 2) * M2 := by gcongr
    _ ≤ (max B (k / 2 * M2) + 1) * (1 - t) +
          (max B (k / 2 * M2) + 1) * ∑ j, torusAbs L (n j) ^ 2 := by
        have h1 : B ≤ max B (k / 2 * M2) + 1 := by linarith [le_max_left B (k / 2 * M2)]
        have h2 : k / 2 * M2 ≤ max B (k / 2 * M2) + 1 := by
          linarith [le_max_right B (k / 2 * M2)]
        have e : (k / 2 : ℝ) * (∑ j, torusAbs L (n j) ^ 2) * M2 =
            (k / 2 * M2) * ∑ j, torusAbs L (n j) ^ 2 := by ring
        rw [e]
        gcongr
    _ = (max B (k / 2 * M2) + 1) * ((1 - t) + ∑ j, torusAbs L (n j) ^ 2) := by ring

/-! ## Large coupling: the kernel facts at the scale `g²` -/

/-- The kernel facts at large coupling, at the scale `a = g²`, for every `0 ≤ t ≤ 1`, from
Lemma A.4 [uvp:prop:finite]. -/
private lemma mol_large_hyp (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ R c Ck : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ 0 < c ∧ 1 ≤ Ck ∧ ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ,
      R * g ^ 2 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ,
      IsDysonRootV (hopB g) (gammaG g) L E m → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        MolHyp g L E m t (g ^ 2) c Ck := by
  obtain ⟨Cκ, R₀, c, C₀, hCκ, hR₀, hc, hC₀, H⟩ := large_periodic_comparison κ hκ hκ2
  refine ⟨Cκ, max R₀ 3, c, max C₀ 1, hCκ, by positivity, hc, le_max_right _ _, ?_⟩
  intro g hg L hL E hE m hm t ht0 ht1
  have hg1 : 1 ≤ g := hCκ.trans hg
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg1
  have hL' : R₀ * g ^ 2 ≤ L := le_trans (by gcongr; exact le_max_left _ _) hL
  have hL3 : 3 ≤ L := by
    have : (3 : ℝ) ≤ L := by
      calc (3 : ℝ) = 3 * 1 := by ring
        _ ≤ max R₀ 3 * g ^ 2 := by gcongr; exact le_max_right _ _
        _ ≤ L := hL
    exact_mod_cast this
  obtain ⟨m₀, mInf, hm₀, -, him, hmle, -, -, -, hrest⟩ := H g hg L hL' E hE
  obtain ⟨-, -, -, -, hMdec, -, hVrow⟩ := hrest
  have hb : 0 ≤ hopB g := div_nonneg (by linarith) (le_trans zero_le_one (le_max_left _ _))
  have hβ : 0 < gammaG g := by
    have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
    unfold gammaG; positivity
  have heq : m = m₀ := isDysonRootV_unique (hopB g) (gammaG g) hb hβ L hL3 E
    (by simp) m m₀ hm hm₀
  subst heq
  have hγ : gammaG g = (g ^ 2)⁻¹ := by
    unfold gammaG; rw [max_eq_right hg1]
  have hC1 : C₀ ≤ max C₀ 1 := le_max_left _ _
  refine ⟨hL3, hm, hg2, hc, le_max_right _ _, ht0, ht1, fun x z => (hMdec x z).trans ?_,
    fun x => (hVrow t ht0 ht1 x).trans hC1, hmle.trans hC1, ?_, ?_, ?_⟩
  · gcongr
  · exact (inv_anti₀ hC₀ hC1).trans him
  · rw [hγ, inv_mul_cancel₀ (by positivity)]
  · rw [hγ, inv_mul_cancel₀ (by positivity), mul_one]; exact le_max_right _ _

/-! ## Large coupling: the threshold `C_κ` before the length `k` -/

/-- The core hypotheses (B.7) [uvp:eq:coreprofile] and (B.9) [uvp:eq:mass] of Appendix B.5
[app:uniform-profile] for the stable molecules at large coupling, Proposition B.8 [uvp:prop:cores],
with `a = g²` and `δ = 1 - t`: the coupling threshold `C_κ` and the volume constant depend on `κ`
only, uniformly in the length `k`. -/
theorem stableMol_large' (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ R : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ ∀ k : ℕ, 3 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ,
      R * g ^ 2 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Fin k → Bool,
        (∀ y, ‖stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖ ≤
          C * Real.exp (-(c * wordDiam y / g ^ 2))) ∧
        ((∀ i, σ (finRotate k i) = !σ i) → ∀ (v : Fin k) (b : Fin L),
          ‖∑ y ∈ Finset.univ.filter (fun y : Fin k → Fin L => y v = b),
              stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖ ≤
            C * (1 - t) * (g ^ 2) ^ (k - 1)) := by
  obtain ⟨Cκ, R, c, Ck, hCκ, hR, hc, hCk, H⟩ := mol_large_hyp κ hκ hκ2
  refine ⟨Cκ, R, hCκ, hR, fun k hk => ?_⟩
  obtain ⟨B, hB, hBb⟩ := mol_stable_mass hc hCk k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  set CS := molCS k c Ck
  have hCS : 0 ≤ CS := molCS_nonneg k hc (by linarith)
  refine ⟨c / (12 * k ^ 2), max CS B + 1, by positivity, by positivity, ?_⟩
  intro g hg L hL E hE m hm t ht0 ht1 σ
  have h := H g hg L hL E hE m hm t ht0 ht1.le
  have hL3 := h.hL
  have : NeZero L := ⟨by omega⟩
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  refine ⟨fun y => ?_, fun halt v b => ?_⟩
  · have := h.stable_profile hk σ y
    calc _ ≤ CS * Real.exp (-(c / (12 * k ^ 2) * wordDiam y / g ^ 2)) := this
      _ ≤ (max CS B + 1) * Real.exp (-(c / (12 * k ^ 2) * wordDiam y / g ^ 2)) := by
          gcongr; linarith [le_max_left CS B]
  · have hmass := hBb g L E m t (g ^ 2) h ht1 σ halt
    have hanch := mol_anchor_eq (stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ)
      (fun z c => (stableMol_symm g L hL3 E m hm t σ z c).1) v b
    have hδ : 0 < 1 - t := by linarith
    have hn : ‖∑ y ∈ Finset.univ.filter (fun y : Fin k → Fin L => y v = b),
        stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖ =
          (L : ℝ)⁻¹ * ‖∑ y, stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖ := by
      rw [← hanch, norm_mul, Complex.norm_natCast, ← mul_assoc, inv_mul_cancel₀ hLr.ne', one_mul]
    rw [hn]
    calc (L : ℝ)⁻¹ * ‖∑ y, stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖
        ≤ (L : ℝ)⁻¹ * (B * L * (1 - t) * (g ^ 2) ^ (k - 1)) := by gcongr
      _ = B * (1 - t) * (g ^ 2) ^ (k - 1) := by field_simp
      _ ≤ (max CS B + 1) * (1 - t) * (g ^ 2) ^ (k - 1) := by
          gcongr; linarith [le_max_right CS B]

end LSBA
