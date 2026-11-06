import LSBA.Primitive.Defs

/-!
# Primitive loops: symmetries

Cyclic invariance of the primitive loops of (5.10) [fo:eq:primitive], in the form of
`loopTr_rotate`.
-/

open MeasureTheory Real Filter Topology Complex Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Symmetry and conjugation of the pair data -/

/-- `P` is symmetric when `M` is. -/
private lemma symm_pairP_transpose {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (hM : Mᵀ = M) : (pairP β M)ᵀ = pairP β M := by
  ext a b
  have h := congrFun (congrFun hM a) b
  simp only [Matrix.transpose_apply] at h
  simp only [Matrix.transpose_apply, pairP, Matrix.of_apply, h]

/-- `Q` is symmetric when `M` is. -/
private lemma symm_pairQ_transpose {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (hM : Mᵀ = M) : (pairQ β M)ᵀ = pairQ β M := by
  ext a b
  have h := congrFun (congrFun hM a) b
  simp only [Matrix.transpose_apply] at h
  simp only [Matrix.transpose_apply, pairQ, Matrix.of_apply, h]

/-- The Lean inverse of a symmetric matrix is symmetric. -/
private lemma symm_inv_comm {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (X : Matrix n n R) (hX : Xᵀ = X) (x y : n) : X⁻¹ x y = X⁻¹ y x := by
  have h : (X⁻¹)ᵀ = X⁻¹ := by rw [Matrix.transpose_nonsing_inv, hX]
  exact (congrFun (congrFun h x) y).symm

/-- `1 - cX` is symmetric when `X` is. -/
private lemma symm_oneSub_transpose {n R : Type*} [DecidableEq n] [CommRing R]
    (X : Matrix n n R) (hX : Xᵀ = X) (c : R) : (1 - c • X)ᵀ = 1 - c • X := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hX]

/-- The one-label inverses are symmetric in the two labels. -/
private lemma symm_pairV_comm {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ} (hM : Mᵀ = M)
    (t : ℝ) (s s' : Bool) (x y : Fin L) :
    pairV β M t s s' x y = pairV β M t s s' y x := by
  have hQ := symm_inv_comm (1 - (t : ℂ) • pairQ β M)
    (symm_oneSub_transpose _ (symm_pairQ_transpose β hM) _) x y
  have hP := symm_inv_comm (1 - t • pairP β M)
    (symm_oneSub_transpose _ (symm_pairP_transpose β hM) _) x y
  unfold pairV
  split_ifs
  · exact hQ
  · simp only [Matrix.map_apply, hQ]
  · simp only [Matrix.map_apply, hP]

/-- The one-label inverses are symmetric in the two signs. -/
private lemma symm_pairV_swap {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    (s s' : Bool) : pairV β M t s s' = pairV β M t s' s := by
  cases s <;> cases s' <;> simp [pairV]

/-- Conjugation flips both signs of a one-label inverse. -/
private lemma symm_star_pairV {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    (s s' : Bool) (x y : Fin L) :
    star (pairV β M t s s' x y) = pairV β M t (!s) (!s') x y := by
  cases s <;> cases s' <;> simp [pairV, Matrix.map_apply]

/-- A symmetric matrix `M` has `M^s` symmetric. -/
private lemma symm_sgnMat_comm {L : ℕ} {M : Matrix (Fin L) (Fin L) ℂ} (hM : Mᵀ = M) (s : Bool)
    (x y : Fin L) : sgnMat M s x y = sgnMat M s y x := by
  have h := congrFun (congrFun hM x) y
  simp only [Matrix.transpose_apply] at h
  cases s <;> simp [sgnMat, Matrix.conjTranspose_apply, h]

/-- Conjugation flips the sign of `M^s`. -/
private lemma symm_star_sgnMat {L : ℕ} {M : Matrix (Fin L) (Fin L) ℂ} (hM : Mᵀ = M) (s : Bool)
    (x y : Fin L) : star (sgnMat M s x y) = sgnMat M (!s) x y := by
  have h := congrFun (congrFun hM x) y
  simp only [Matrix.transpose_apply] at h
  cases s <;> simp [sgnMat, Matrix.conjTranspose_apply, h]

/-! ### Relabelling of the physical labels -/

/-- The cyclic offset without `mod`. -/
private lemma symm_polyOff_eq {k : ℕ} (v w : Fin k) :
    polyOff v w = if v.val ≤ w.val then w.val - v.val else w.val + k - v.val := by
  have := v.isLt
  have := w.isLt
  unfold polyOff
  split_ifs with h
  · rw [show w.val + k - v.val = (w.val - v.val) + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- Distinct vertices have an offset in `(0, k)`. -/
private lemma symm_polyOff_bounds {k : ℕ} {v w : Fin k} (h : v ≠ w) :
    0 < polyOff v w ∧ polyOff v w < k := by
  have := v.isLt
  have := w.isLt
  have h' : v.val ≠ w.val := fun h' => h (Fin.ext h')
  rw [symm_polyOff_eq]
  split_ifs <;> omega

/-- The value of the rotation `v ↦ v + 1` of the polygon on `n + 3` vertices. -/
private lemma symm_rot_val {n : ℕ} (v : Fin (n + 3)) :
    (finRotate (n + 3) v).val = if v.val = n + 2 then 0 else v.val + 1 := by
  rw [coe_finRotate]
  by_cases h : v = Fin.last (n + 2)
  · subst h; simp
  · have : v.val ≠ n + 2 := fun h' => h (Fin.ext h')
    simp [h, this]

/-- The rotation preserves the cyclic offsets. -/
private lemma symm_rot_off {n : ℕ} (v w : Fin (n + 3)) :
    polyOff (finRotate (n + 3) v) (finRotate (n + 3) w) = polyOff v w := by
  have := v.isLt
  have := w.isLt
  rw [symm_polyOff_eq, symm_polyOff_eq, symm_rot_val, symm_rot_val]
  split_ifs <;> omega

/-- The sorted image of a pair of vertices under a vertex map. -/
private def symmNd {k : ℕ} (ψ : Fin k → Fin k) (d : Fin k × Fin k) : Fin k × Fin k :=
  (min (ψ d.1) (ψ d.2), max (ψ d.1) (ψ d.2))

/-- The rotation maps diagonals to diagonals. -/
private lemma symm_rot_polyDiag {n : ℕ} (d : Fin (n + 3) × Fin (n + 3))
    (hd : IsPolyDiag (n + 3) d) : IsPolyDiag (n + 3) (symmNd (finRotate (n + 3)) d) := by
  unfold IsPolyDiag symmNd at *
  simp only [Fin.val_min, Fin.val_max, symm_rot_val]
  have := d.1.isLt
  have := d.2.isLt
  split_ifs <;> omega

/-- A crossing of the rotated diagonals is a crossing of the diagonals. -/
private lemma symm_rot_cross {n : ℕ} (d e : Fin (n + 3) × Fin (n + 3))
    (hd : IsPolyDiag (n + 3) d) (he : IsPolyDiag (n + 3) e)
    (h : DiagCross (symmNd (finRotate (n + 3)) d) (symmNd (finRotate (n + 3)) e)) :
    DiagCross d e := by
  unfold IsPolyDiag at hd he
  unfold DiagCross symmNd at *
  simp only [Fin.lt_def, Fin.val_min, Fin.val_max, symm_rot_val] at *
  have := d.1.isLt
  have := d.2.isLt
  have := e.1.isLt
  have := e.2.isLt
  split_ifs at h <;> omega

/-- The sorted image of a sorted pair is the sorted pair of the images. -/
private lemma symmNd_comm {k : ℕ} (ψ : Fin k → Fin k) (u u' : Fin k) :
    symmNd ψ (min u u', max u u') = (min (ψ u) (ψ u'), max (ψ u) (ψ u')) := by
  rcases le_total u u' with h | h
  · simp only [symmNd, min_eq_left h, max_eq_right h]
  · simp only [symmNd, min_eq_right h, max_eq_left h]
    exact Prod.ext (min_comm _ _) (max_comm _ _)

/-- The sorted image is injective on sorted pairs. -/
private lemma symmNd_injOn {k : ℕ} {ψ : Fin k → Fin k} (hψ : Function.Injective ψ)
    {d e : Fin k × Fin k} (hd : d.1 < d.2) (he : e.1 < e.2) (h : symmNd ψ d = symmNd ψ e) :
    d = e := by
  have hne1 : ψ d.1 ≠ ψ d.2 := hψ.ne hd.ne
  have hne2 : ψ e.1 ≠ ψ e.2 := hψ.ne he.ne
  simp only [symmNd, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rcases lt_or_gt_of_ne hne1 with h3 | h3 <;> rcases lt_or_gt_of_ne hne2 with h4 | h4
  · rw [min_eq_left h3.le, min_eq_left h4.le] at h1
    rw [max_eq_right h3.le, max_eq_right h4.le] at h2
    exact Prod.ext (hψ h1) (hψ h2)
  · rw [min_eq_left h3.le, min_eq_right h4.le] at h1
    rw [max_eq_right h3.le, max_eq_left h4.le] at h2
    have e1 : d.1 = e.2 := hψ h1
    have e2 : d.2 = e.1 := hψ h2
    rw [e1, e2] at hd
    exact absurd (lt_trans hd he) (lt_irrefl _)
  · rw [min_eq_right h3.le, min_eq_left h4.le] at h1
    rw [max_eq_left h3.le, max_eq_right h4.le] at h2
    have e1 : d.2 = e.1 := hψ h1
    have e2 : d.1 = e.2 := hψ h2
    rw [e1, e2] at hd
    exact absurd (lt_trans hd he) (lt_irrefl _)
  · rw [min_eq_right h3.le, min_eq_right h4.le] at h1
    rw [max_eq_left h3.le, max_eq_left h4.le] at h2
    exact Prod.ext (hψ h2) (hψ h1)

/-- The sorted image is a bijection from the diagonals of `F` onto those of the image. -/
private lemma symm_exists_equiv {k : ℕ} (ψ : Fin k ≃ Fin k) (F : Finset (Fin k × Fin k))
    (hF : ∀ d ∈ F, d.1 < d.2) :
    ∃ e : ↥F ≃ ↥(F.image (symmNd ψ)), ∀ d, (e d).1 = symmNd ψ d.1 := by
  refine ⟨Equiv.ofBijective (fun d => ⟨symmNd ψ d.1, Finset.mem_image_of_mem _ d.2⟩)
    ⟨?_, ?_⟩, fun d => rfl⟩
  · intro d d' h
    exact Subtype.ext (symmNd_injOn ψ.injective (hF _ d.2) (hF _ d'.2) (congrArg Subtype.val h))
  · rintro ⟨x, hx⟩
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨⟨d, hd⟩, rfl⟩

/-- The diagonals of the image are the images of the diagonals. -/
private lemma symm_corr {k : ℕ} (ψ : Fin k ≃ Fin k) (F : Finset (Fin k × Fin k))
    (hF : ∀ d ∈ F, d.1 < d.2) (u u' : Fin k) (huu : u ≠ u') :
    ((min (ψ u) (ψ u'), max (ψ u) (ψ u')) ∈ F.image (symmNd ψ) ↔ (min u u', max u u') ∈ F) := by
  constructor
  · intro h
    obtain ⟨d, hd, hdd⟩ := Finset.mem_image.mp h
    rw [← symmNd_comm] at hdd
    have : d = (min u u', max u u') :=
      symmNd_injOn ψ.injective (hF d hd) (min_lt_max.mpr huu) hdd
    rwa [← this]
  · intro h
    rw [← symmNd_comm]
    exact Finset.mem_image_of_mem _ h

/-- Membership in `dissections k`. -/
private lemma symm_mem_dissections {k : ℕ} (F : Finset (Fin k × Fin k)) :
    F ∈ dissections k ↔ (∀ d ∈ F, IsPolyDiag k d) ∧ ∀ d ∈ F, ∀ e ∈ F, ¬DiagCross d e := by
  simp only [dissections, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, polyDiags,
    Finset.mem_univ, true_and]

/-- The diagonals of a dissection are sorted pairs. -/
private lemma symm_dissections_sorted {k : ℕ} {F : Finset (Fin k × Fin k)}
    (hF : F ∈ dissections k) : ∀ d ∈ F, d.1 < d.2 := by
  intro d hd
  have := ((symm_mem_dissections F).1 hF).1 d hd
  unfold IsPolyDiag at this
  exact Fin.lt_def.2 (by omega)

/-- A polygon map that preserves diagonals and crossings permutes the dissections. -/
private lemma symm_sum_dissections {k : ℕ} (ψ : Fin k ≃ Fin k)
    (hdiag : ∀ d, IsPolyDiag k d → IsPolyDiag k (symmNd ψ d))
    (hcross : ∀ d e, IsPolyDiag k d → IsPolyDiag k e →
      DiagCross (symmNd ψ d) (symmNd ψ e) → DiagCross d e)
    {f g : Finset (Fin k × Fin k) → ℂ}
    (h : ∀ F ∈ dissections k, f F = g (F.image (symmNd ψ))) :
    ∑ F ∈ dissections k, f F = ∑ F ∈ dissections k, g F := by
  have hsorted : ∀ F ∈ dissections k, ∀ d ∈ F, d.1 < d.2 := fun F hF => symm_dissections_sorted hF
  have hmaps : ∀ F ∈ dissections k, F.image (symmNd ψ) ∈ dissections k := by
    intro F hF
    obtain ⟨h1, h2⟩ := (symm_mem_dissections F).1 hF
    refine (symm_mem_dissections _).2 ⟨?_, ?_⟩
    · intro d hd
      obtain ⟨d0, hd0, rfl⟩ := Finset.mem_image.mp hd
      exact hdiag d0 (h1 d0 hd0)
    · intro d hd e he hde
      obtain ⟨d0, hd0, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he
      exact h2 d0 hd0 e0 he0 (hcross d0 e0 (h1 d0 hd0) (h1 e0 he0) hde)
  have hinj :
      Set.InjOn (fun F : Finset (Fin k × Fin k) => F.image (symmNd ψ)) ↑(dissections k) := by
    intro F hF G hG hFG
    have hFs := hsorted F hF
    have hGs := hsorted G hG
    have hFG : F.image (symmNd ψ) = G.image (symmNd ψ) := hFG
    ext d
    constructor
    · intro hd
      have : symmNd ψ d ∈ G.image (symmNd ψ) := by
        rw [← hFG]; exact Finset.mem_image_of_mem _ hd
      obtain ⟨d', hd', hdd'⟩ := Finset.mem_image.mp this
      have := symmNd_injOn ψ.injective (hGs d' hd') (hFs d hd) hdd'
      rwa [← this]
    · intro hd
      have : symmNd ψ d ∈ F.image (symmNd ψ) := by
        rw [hFG]; exact Finset.mem_image_of_mem _ hd
      obtain ⟨d', hd', hdd'⟩ := Finset.mem_image.mp this
      have := symmNd_injOn ψ.injective (hFs d' hd') (hGs d hd) hdd'
      rwa [← this]
  have hsub : (dissections k).image (fun F : Finset (Fin k × Fin k) => F.image (symmNd ψ)) ⊆
      dissections k := by
    intro F hF
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hF
    exact hmaps G hG
  have hcard : (dissections k).card ≤
      ((dissections k).image (fun F : Finset (Fin k × Fin k) => F.image (symmNd ψ))).card :=
    (Finset.card_image_of_injOn hinj).ge
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  refine Finset.sum_nbij _ hmaps hinj ?_ h
  intro F hF
  have : F ∈ (dissections k).image (fun F : Finset (Fin k × Fin k) => F.image (symmNd ψ)) := by
    rw [heq]; exact hF
  obtain ⟨G, hG, hGF⟩ := Finset.mem_image.mp this
  exact ⟨G, hG, hGF⟩

/-- A polygon map transports the neighbours of a vertex. -/
private lemma symm_polyNbr {k : ℕ} (ψ : Fin k ≃ Fin k) (dir : Bool)
    (hoff : ∀ v w, v ≠ w → polyOff (ψ v) (ψ w) = if dir then polyOff v w else k - polyOff v w)
    {F F' : Finset (Fin k × Fin k)}
    (hC : ∀ u u', u ≠ u' →
      ((min (ψ u) (ψ u'), max (ψ u) (ψ u')) ∈ F' ↔ (min u u', max u u') ∈ F))
    (v w : Fin k) : PolyNbr F' (ψ v) (ψ w) ↔ PolyNbr F v w := by
  by_cases hvw : v = w
  · subst hvw
    simp [PolyNbr]
  · have hne : ψ w ≠ ψ v := ψ.injective.ne (Ne.symm hvw)
    have hb := symm_polyOff_bounds hvw
    unfold PolyNbr
    rw [hoff v w hvw, hC v w hvw]
    by_cases hm : (min v w, max v w) ∈ F
    · simp [hm, ne_eq, ψ.injective.eq_iff, Ne.symm hvw]
    · cases dir
      · simp only [Bool.false_eq_true, ite_false, ne_eq, ψ.injective.eq_iff, hm, or_false,
          Ne.symm hvw, not_false_eq_true, true_and]
        omega
      · simp [hm, ne_eq, ψ.injective.eq_iff]

/-- The action of a vertex map on the corners `(w, w')` at a vertex: the corner order is kept
for an orientation-preserving map and reversed otherwise. -/
private def symmKap {k : ℕ} (ψ : Fin k → Fin k) : Bool → Fin k × Fin k → Fin k × Fin k
  | true, p => (ψ p.1, ψ p.2)
  | false, p => (ψ p.2, ψ p.1)

/-- A polygon map transports the corners at a vertex. -/
private lemma symm_mem_polyCorners {k : ℕ} (ψ : Fin k ≃ Fin k) (dir : Bool)
    (hoff : ∀ v w, v ≠ w → polyOff (ψ v) (ψ w) = if dir then polyOff v w else k - polyOff v w)
    {F F' : Finset (Fin k × Fin k)}
    (hC : ∀ u u', u ≠ u' →
      ((min (ψ u) (ψ u'), max (ψ u) (ψ u')) ∈ F' ↔ (min u u', max u u') ∈ F))
    (v : Fin k) (p : Fin k × Fin k) :
    symmKap ψ dir p ∈ polyCorners F' (ψ v) ↔ p ∈ polyCorners F v := by
  have hnbr := symm_polyNbr ψ dir hoff hC v
  simp only [polyCorners, Finset.mem_filter, Finset.mem_univ, true_and]
  cases dir
  · simp only [symmKap]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have n1 := (hnbr _).1 h2
      have n2 := (hnbr _).1 h1
      have b1 := symm_polyOff_bounds n1.1.symm
      have b2 := symm_polyOff_bounds n2.1.symm
      rw [hoff v _ n1.1.symm, hoff v _ n2.1.symm] at h3
      simp only [Bool.false_eq_true, ite_false] at h3
      refine ⟨n1, n2, by omega, ?_⟩
      intro u hu
      have b3 := symm_polyOff_bounds hu.1.symm
      have := h4 (ψ u) ((hnbr u).2 hu)
      rw [hoff v _ n1.1.symm, hoff v _ n2.1.symm, hoff v _ hu.1.symm] at this
      simp only [Bool.false_eq_true, ite_false] at this
      omega
    · rintro ⟨n1, n2, h3, h4⟩
      have b1 := symm_polyOff_bounds n1.1.symm
      have b2 := symm_polyOff_bounds n2.1.symm
      refine ⟨(hnbr _).2 n2, (hnbr _).2 n1, ?_, ?_⟩
      · rw [hoff v _ n1.1.symm, hoff v _ n2.1.symm]
        simp only [Bool.false_eq_true, ite_false]
        omega
      · intro u' hu'
        obtain ⟨u, rfl⟩ := ψ.surjective u'
        have hu := (hnbr u).1 hu'
        have b3 := symm_polyOff_bounds hu.1.symm
        have := h4 u hu
        rw [hoff v _ n1.1.symm, hoff v _ n2.1.symm, hoff v _ hu.1.symm]
        simp only [Bool.false_eq_true, ite_false]
        omega
  · simp only [symmKap]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have n1 := (hnbr _).1 h1
      have n2 := (hnbr _).1 h2
      rw [hoff v _ n1.1.symm, hoff v _ n2.1.symm] at h3
      simp only [ite_true] at h3
      refine ⟨n1, n2, h3, ?_⟩
      intro u hu
      have := h4 (ψ u) ((hnbr u).2 hu)
      rw [hoff v _ n1.1.symm, hoff v _ n2.1.symm, hoff v _ hu.1.symm] at this
      simpa using this
    · rintro ⟨n1, n2, h3, h4⟩
      refine ⟨(hnbr _).2 n1, (hnbr _).2 n2, ?_, ?_⟩
      · rw [hoff v _ n1.1.symm, hoff v _ n2.1.symm]
        simpa using h3
      · intro u' hu'
        obtain ⟨u, rfl⟩ := ψ.surjective u'
        have hu := (hnbr u).1 hu'
        have := h4 u hu
        rw [hoff v _ n1.1.symm, hoff v _ n2.1.symm, hoff v _ hu.1.symm]
        simpa using this

/-- A product over the corners at a vertex, transported along a polygon map. -/
private lemma symm_prod_corners {k : ℕ} (ψ : Fin k ≃ Fin k) (dir : Bool)
    (hoff : ∀ v w, v ≠ w → polyOff (ψ v) (ψ w) = if dir then polyOff v w else k - polyOff v w)
    {F F' : Finset (Fin k × Fin k)}
    (hC : ∀ u u', u ≠ u' →
      ((min (ψ u) (ψ u'), max (ψ u) (ψ u')) ∈ F' ↔ (min u u', max u u') ∈ F))
    (v : Fin k) {f g : Fin k × Fin k → ℂ}
    (h : ∀ p ∈ polyCorners F v, f p = g (symmKap ψ dir p)) :
    ∏ p ∈ polyCorners F v, f p = ∏ p ∈ polyCorners F' (ψ v), g p := by
  have hκ : Function.Injective (symmKap ψ dir) := by
    cases dir
    · intro p q hpq
      simp only [symmKap, Prod.mk.injEq, ψ.injective.eq_iff] at hpq
      exact Prod.ext hpq.2 hpq.1
    · intro p q hpq
      simp only [symmKap, Prod.mk.injEq, ψ.injective.eq_iff] at hpq
      exact Prod.ext hpq.1 hpq.2
  refine Finset.prod_nbij (symmKap ψ dir) ?_ (hκ.injOn) ?_ h
  · intro p hp
    exact (symm_mem_polyCorners ψ dir hoff hC v p).2 hp
  · intro q hq
    have hκs : Function.Surjective (symmKap ψ dir) := by
      cases dir
      · intro q
        exact ⟨(ψ.symm q.2, ψ.symm q.1), by simp [symmKap]⟩
      · intro q
        exact ⟨(ψ.symm q.1, ψ.symm q.2), by simp [symmKap]⟩
    obtain ⟨p, rfl⟩ := hκs q
    exact ⟨p, (symm_mem_polyCorners ψ dir hoff hC v p).1 hq, rfl⟩

/-- The sign twist of a polygon map: the identity for an orientation-preserving map and the
sign flip otherwise. -/
private def symmFl : Bool → Bool → Bool
  | true, s => s
  | false, s => !s

/-- The ring homomorphism of a polygon map: the identity for an orientation-preserving map and
the complex conjugation otherwise. -/
private def symmRH : Bool → ℂ →+* ℂ
  | true => RingHom.id ℂ
  | false => starRingEnd ℂ

/-- The relabelling of the diagonal labels `(cIn, cOut)` along an equivalence of the diagonals
that exchanges the two copies on the diagonals marked by `X`. -/
private def symmSwapEquiv {ι ι' α : Type*} (e : ι ≃ ι') (X : ι → Bool) :
    ((ι → α) × (ι → α)) ≃ ((ι' → α) × (ι' → α)) where
  toFun p := (fun d' => if X (e.symm d') then p.1 (e.symm d') else p.2 (e.symm d'),
    fun d' => if X (e.symm d') then p.2 (e.symm d') else p.1 (e.symm d'))
  invFun p := (fun d => if X d then p.1 (e d) else p.2 (e d),
    fun d => if X d then p.2 (e d) else p.1 (e d))
  left_inv p := by
    obtain ⟨p1, p2⟩ := p
    refine Prod.ext (funext fun d => ?_) (funext fun d => ?_) <;> by_cases h : X d <;> simp [h]
  right_inv p := by
    obtain ⟨p1, p2⟩ := p
    refine Prod.ext (funext fun d => ?_) (funext fun d => ?_) <;>
      by_cases h : X (e.symm d) <;> simp [h]

/-- A polygon map transports the edge labels. -/
private lemma symm_edgeLab_transport {L k : ℕ} (ψ : Fin k ≃ Fin k) (dir : Bool)
    {F : Finset (Fin k × Fin k)} (hF : ∀ d ∈ F, d.1 < d.2)
    (e : ↥F ≃ ↥(F.image (symmNd ψ))) (he : ∀ d, (e d).1 = symmNd ψ d.1)
    (y y' : Fin k → Fin L)
    (hy : ∀ v w, (polyOff v w = 1 ∨ polyOff v w + 1 = k) →
      (if polyOff (ψ v) (ψ w) = 1 then y' (ψ v) else y' (ψ w)) =
        (if polyOff v w = 1 then y v else y w))
    (cIn cOut : ↥F → Fin L) (cIn' cOut' : ↥(F.image (symmNd ψ)) → Fin L)
    (hIn : ∀ d, cIn d =
      if (decide (ψ d.1.2 < ψ d.1.1) != dir) then cIn' (e d) else cOut' (e d))
    (hOut : ∀ d, cOut d =
      if (decide (ψ d.1.2 < ψ d.1.1) != dir) then cOut' (e d) else cIn' (e d))
    (v w : Fin k) (hvw : PolyNbr F v w) (small : Bool) :
    edgeLab (F.image (symmNd ψ)) y' cIn' cOut' (ψ v) (ψ w) (symmFl dir small) =
      edgeLab F y cIn cOut v w small := by
  have hne : v ≠ w := hvw.1.symm
  have hC := symm_corr ψ F hF v w hne
  unfold edgeLab
  by_cases hm : (min v w, max v w) ∈ F
  · have hm' : (min (ψ v) (ψ w), max (ψ v) (ψ w)) ∈ F.image (symmNd ψ) := hC.2 hm
    simp only [hm, hm', ↓reduceDIte]
    have hee : e ⟨(min v w, max v w), hm⟩ = ⟨(min (ψ v) (ψ w), max (ψ v) (ψ w)), hm'⟩ :=
      Subtype.ext (by rw [he]; exact symmNd_comm ψ v w)
    rw [hIn, hOut, hee]
    rcases lt_or_gt_of_ne hne with h | h <;> rcases lt_or_gt_of_ne (ψ.injective.ne hne) with h' | h'
    · cases dir <;> cases small <;>
        simp [symmFl, min_eq_left h.le, max_eq_right h.le, min_eq_left h'.le, max_eq_right h'.le, h,
          h', not_lt_of_gt h']
    · cases dir <;> cases small <;>
        simp [symmFl, min_eq_left h.le, max_eq_right h.le, min_eq_right h'.le, max_eq_left h'.le, h,
          not_lt_of_gt h', not_le_of_gt h']
    · cases dir <;> cases small <;>
        simp [symmFl, min_eq_right h.le, max_eq_left h.le, min_eq_left h'.le, max_eq_right h'.le,
          not_lt_of_gt h, h']
    · cases dir <;> cases small <;>
        simp [symmFl, min_eq_right h.le, max_eq_left h.le, min_eq_right h'.le, max_eq_left h'.le,
          not_lt_of_gt h, not_lt_of_gt h']
  · have hm' : (min (ψ v) (ψ w), max (ψ v) (ψ w)) ∉ F.image (symmNd ψ) := fun h => hm (hC.1 h)
    simp only [hm, hm', ↓reduceDIte]
    exact hy v w (by
      rcases hvw.2 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hm)

/-- The twist of a one-label inverse. -/
private lemma symm_RH_pairV (dir : Bool) {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    (s s' : Bool) (x y : Fin L) :
    symmRH dir (pairV β M t s s' x y) = pairV β M t (symmFl dir s) (symmFl dir s') x y := by
  cases dir
  · simp only [symmRH, symmFl, starRingEnd_apply, symm_star_pairV]
  · rfl

/-- The twist of `M^s`. -/
private lemma symm_RH_sgnMat (dir : Bool) {L : ℕ} {M : Matrix (Fin L) (Fin L) ℂ} (hM : Mᵀ = M)
    (s : Bool) (x y : Fin L) :
    symmRH dir (sgnMat M s x y) = sgnMat M (symmFl dir s) x y := by
  cases dir
  · simp only [symmRH, symmFl, starRingEnd_apply, symm_star_sgnMat hM]
  · rfl

/-- The twist fixes real numbers. -/
private lemma symm_RH_real (dir : Bool) (r : ℝ) : symmRH dir (r : ℂ) = (r : ℂ) := by
  cases dir <;> simp [symmRH]

/-- The twist of a link between two diagonal labels. -/
private lemma symm_link_eq {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ} (t : ℝ)
    (dir : Bool) (s1 s2 s1' s2' : Bool) (x y x' y' : Fin L) (sw : Bool)
    (hM : Mᵀ = M)
    (hs : if sw then (s1' = symmFl dir s2 ∧ s2' = symmFl dir s1)
      else (s1' = symmFl dir s1 ∧ s2' = symmFl dir s2))
    (hxy : if (sw != dir) then (x' = x ∧ y' = y) else (x' = y ∧ y' = x)) :
    symmRH dir (pairV β M t s1 s2 x y) = pairV β M t s1' s2' x' y' := by
  rw [symm_RH_pairV]
  cases sw <;> cases dir <;> simp only [symmFl, Bool.bne_false, Bool.bne_true, Bool.not_true,
    Bool.not_false, ite_true, ite_false, Bool.false_eq_true] at hs hxy ⊢
  all_goals
    obtain ⟨h1, h2⟩ := hs
    obtain ⟨h3, h4⟩ := hxy
    rw [h1, h2, h3, h4]
    all_goals
      first
      | exact symm_pairV_comm β hM t _ _ _ _
      | (rw [symm_pairV_swap β M t]; done)
      | (rw [symm_pairV_swap β M t]; exact symm_pairV_comm β hM t _ _ _ _)

/-- The signs at the endpoints of the sorted image of a diagonal. -/
private lemma symm_sigma_nd {k : ℕ} (ψ : Fin k ≃ Fin k) (dir : Bool) (σ σ' : Fin k → Bool)
    (hσ : ∀ v, σ' (ψ v) = symmFl dir (σ v)) (i j : Fin k) (hij : i ≠ j) :
    if decide (ψ j < ψ i) then
      (σ' (min (ψ i) (ψ j)) = symmFl dir (σ j) ∧ σ' (max (ψ i) (ψ j)) = symmFl dir (σ i))
    else (σ' (min (ψ i) (ψ j)) = symmFl dir (σ i) ∧ σ' (max (ψ i) (ψ j)) = symmFl dir (σ j)) := by
  rcases lt_or_gt_of_ne (ψ.injective.ne hij) with h | h
  · simp [min_eq_left h.le, max_eq_right h.le, not_lt_of_gt h, hσ]
  · simp [min_eq_right h.le, max_eq_left h.le, h, hσ]

/-- The core of a dissection transported along a polygon map `ψ`: the polygon map carries the
dissection `F` to `F.image (symmNd ψ)`, the corners to the corners (reversed if `ψ` reverses the
orientation), and the pre-labels of the sides to the pre-labels of the sides; the core is
unchanged, up to conjugation if `ψ` reverses the orientation. -/
private theorem symm_dissCore_transport {L k : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (hM : Mᵀ = M) (t : ℝ) (ψ : Fin k ≃ Fin k) (dir : Bool)
    (hoff : ∀ v w, v ≠ w → polyOff (ψ v) (ψ w) = if dir then polyOff v w else k - polyOff v w)
    (F : Finset (Fin k × Fin k)) (hF : ∀ d ∈ F, d.1 < d.2)
    (σ σ' : Fin k → Bool) (hσ : ∀ v, σ' (ψ v) = symmFl dir (σ v))
    (y y' : Fin k → Fin L)
    (hy : ∀ v w, (polyOff v w = 1 ∨ polyOff v w + 1 = k) →
      (if polyOff (ψ v) (ψ w) = 1 then y' (ψ v) else y' (ψ w)) =
        (if polyOff v w = 1 then y v else y w)) :
    dissCore β M t σ' (F.image (symmNd ψ)) y' = symmRH dir (dissCore β M t σ F y) := by
  obtain ⟨e, he⟩ := symm_exists_equiv ψ F hF
  have hC := symm_corr ψ F hF
  let X : ↥F → Bool := fun d => decide (ψ d.1.2 < ψ d.1.1) != dir
  unfold dissCore
  simp only [map_sum]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv (symmSwapEquiv e X) _ _ (fun p => ?_)).symm
  obtain ⟨cIn, cOut⟩ := p
  have hT1 : ∀ d, ((symmSwapEquiv e X) (cIn, cOut)).1 (e d) = if X d then cIn d else cOut d := by
    intro d
    simp [symmSwapEquiv]
  have hT2 : ∀ d, ((symmSwapEquiv e X) (cIn, cOut)).2 (e d) = if X d then cOut d else cIn d := by
    intro d
    simp [symmSwapEquiv]
  dsimp only
  set cIn' := ((symmSwapEquiv e X) (cIn, cOut)).1 with hcI
  set cOut' := ((symmSwapEquiv e X) (cIn, cOut)).2 with hcO
  have hIn : ∀ d : ↥F, cIn d = if X d then cIn' (e d) else cOut' (e d) := by
    intro d
    have h1 := hT1 d
    have h2 := hT2 d
    cases hx : X d
    · rw [hx] at h2
      simpa using h2.symm
    · rw [hx] at h1
      simpa using h1.symm
  have hOut : ∀ d : ↥F, cOut d = if X d then cOut' (e d) else cIn' (e d) := by
    intro d
    have h1 := hT1 d
    have h2 := hT2 d
    cases hx : X d
    · rw [hx] at h1
      simpa using h1.symm
    · rw [hx] at h2
      simpa using h2.symm
  have hedge : ∀ v w, PolyNbr F v w → ∀ small,
      edgeLab (F.image (symmNd ψ)) y' cIn' cOut' (ψ v) (ψ w) (symmFl dir small) =
        edgeLab F y cIn cOut v w small := fun v w hvw small =>
    symm_edgeLab_transport ψ dir hF e he y y' hy cIn cOut cIn' cOut' hIn hOut v w hvw small
  rw [map_mul, map_prod, map_prod]
  congr 1
  · refine Fintype.prod_equiv e _ _ (fun d => ?_)
    rw [map_mul, symm_RH_real]
    congr 1
    have hij : d.1.1 ≠ d.1.2 := (hF _ d.2).ne
    refine symm_link_eq β t dir _ _ _ _ _ _ _ _ (decide (ψ d.1.2 < ψ d.1.1)) hM ?_ ?_
    · rw [he]
      exact symm_sigma_nd ψ dir σ σ' hσ d.1.1 d.1.2 hij
    · have h1 := hT1 d
      have h2 := hT2 d
      cases hx : X d
      · rw [hx] at h1 h2
        simp only [Bool.false_eq_true, ite_false] at h1 h2
        have : (decide (ψ d.1.2 < ψ d.1.1) != dir) = false := hx
        simp only [this, Bool.false_eq_true, ite_false]
        exact ⟨h2, h1⟩
      · rw [hx] at h1 h2
        simp only [ite_true] at h1 h2
        have : (decide (ψ d.1.2 < ψ d.1.1) != dir) = true := hx
        simp only [this, ite_true]
        exact ⟨h2, h1⟩
  · refine Fintype.prod_equiv ψ _ _ (fun v => ?_)
    rw [map_prod]
    refine symm_prod_corners ψ dir hoff hC v (fun p hp => ?_)
    have hp' : PolyNbr F v p.1 ∧ PolyNbr F v p.2 := by
      simp only [polyCorners, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨hp.1, hp.2.1⟩
    rw [symm_RH_sgnMat dir hM]
    cases dir
    · simp only [symmKap]
      rw [hσ v]
      have e1 := hedge v p.1 hp'.1 false
      have e2 := hedge v p.2 hp'.2 true
      simp only [symmFl, Bool.not_false, Bool.not_true] at e1 e2 ⊢
      rw [e1, e2]
      exact symm_sgnMat_comm hM _ _ _
    · simp only [symmKap]
      rw [hσ v]
      have e1 := hedge v p.1 hp'.1 false
      have e2 := hedge v p.2 hp'.2 true
      simp only [symmFl] at e1 e2 ⊢
      rw [e1, e2]

/-- The dressed value of a dissection transported along a polygon map `ψ`, where `χ` is the
induced bijection of the sides of the polygon. -/
private theorem symm_dissVal_transport {L k : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (hM : Mᵀ = M) (t : ℝ) (ψ χ : Fin k ≃ Fin k) (dir : Bool)
    (hoff : ∀ v w, v ≠ w → polyOff (ψ v) (ψ w) = if dir then polyOff v w else k - polyOff v w)
    (hyχ : ∀ v w, (polyOff v w = 1 ∨ polyOff v w + 1 = k) →
      (if polyOff (ψ v) (ψ w) = 1 then χ.symm (ψ v) else χ.symm (ψ w)) =
        (if polyOff v w = 1 then v else w))
    (F : Finset (Fin k × Fin k)) (hF : ∀ d ∈ F, d.1 < d.2)
    (σ σ' : Fin k → Bool) (hσ : ∀ v, σ' (ψ v) = symmFl dir (σ v))
    (hext : ∀ i,
      (σ' (χ i) = symmFl dir (σ i) ∧ σ' (finRotate k (χ i)) = symmFl dir (σ (finRotate k i))) ∨
      (σ' (χ i) = symmFl dir (σ (finRotate k i)) ∧ σ' (finRotate k (χ i)) = symmFl dir (σ i)))
    (a a' : Fin k → Fin L) (ha : ∀ i, a' (χ i) = a i) :
    dissVal β M t σ' (F.image (symmNd ψ)) a' = symmRH dir (dissVal β M t σ F a) := by
  unfold dissVal
  rw [map_sum]
  refine (Fintype.sum_equiv (Equiv.arrowCongr χ (Equiv.refl (Fin L))) _ _ (fun y => ?_)).symm
  set y' := Equiv.arrowCongr χ (Equiv.refl (Fin L)) y with hy'
  have hyy : ∀ u, y' u = y (χ.symm u) := fun u => by simp [y', Equiv.arrowCongr_apply]
  have hy'χ : ∀ i, y' (χ i) = y i := fun i => by rw [hyy, Equiv.symm_apply_apply]
  have hy : ∀ v w, (polyOff v w = 1 ∨ polyOff v w + 1 = k) →
      (if polyOff (ψ v) (ψ w) = 1 then y' (ψ v) else y' (ψ w)) =
        (if polyOff v w = 1 then y v else y w) := by
    intro v w hadj
    simp only [hyy]
    rw [← apply_ite y, hyχ v w hadj, apply_ite y]
  rw [map_mul, map_prod, symm_dissCore_transport β hM t ψ dir hoff F hF σ σ' hσ y y' hy]
  congr 1
  refine Fintype.prod_equiv χ _ _ (fun i => ?_)
  rw [ha, hy'χ, symm_RH_pairV]
  rcases hext i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, symm_pairV_swap β M t]

/-- Cyclic invariance of the primitive loops, in the form of `loopTr_rotate`. -/
theorem primLoop_rotate (g : ℝ) (W L : ℕ) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) {k : ℕ}
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    primLoop g W L E m t (a ∘ finRotate k) (σ ∘ finRotate k) = primLoop g W L E m t a σ := by
  have _ := And.intro ht0 ht1
  have hM := (primData_of_root g L hL E m hm).symm
  rcases k with _ | _ | _ | n
  · rfl
  · simp only [primLoop, primK]
    congr 1
  · have ha : ∀ b : Fin 2 → Fin L, b = ![b 0, b 1] := fun b => by
      funext i; fin_cases i <;> rfl
    have hs : ∀ b : Fin 2 → Bool, b = ![b 0, b 1] := fun b => by
      funext i; fin_cases i <;> rfl
    have hr : ∀ {α : Type} (b : Fin 2 → α), b ∘ finRotate 2 = ![b 1, b 0] := fun b => by
      funext i; fin_cases i <;> rfl
    calc primLoop g W L E m t (a ∘ finRotate 2) (σ ∘ finRotate 2)
        = primLoop g W L E m t ![a 1, a 0] ![σ 1, σ 0] := by rw [hr a, hr σ]
      _ = primLoop g W L E m t ![a 0, a 1] ![σ 0, σ 1] :=
          (primLoop_two_swap g W L E m t (a 0) (a 1) (σ 0) (σ 1)).symm
      _ = primLoop g W L E m t a σ := by rw [← ha a, ← hs σ]
  · simp only [primLoop, primK]
    congr 1
    change ∑ G ∈ dissections (n + 3),
        dissVal (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t (σ ∘ finRotate (n + 3)) G
          (a ∘ finRotate (n + 3)) =
      ∑ F ∈ dissections (n + 3),
        dissVal (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ F a
    refine symm_sum_dissections (finRotate (n + 3)) symm_rot_polyDiag symm_rot_cross ?_
    intro G hG
    exact (symm_dissVal_transport (gammaG g) hM t (finRotate (n + 3)) (finRotate (n + 3)) true
      (fun v w _ => by simp only [ite_true, symm_rot_off])
      (fun v w _ => by simp only [Equiv.symm_apply_apply, symm_rot_off])
      G (symm_dissections_sorted hG) (σ ∘ finRotate (n + 3)) σ (fun v => rfl)
      (fun i => Or.inl ⟨rfl, rfl⟩) (a ∘ finRotate (n + 3)) a (fun i => rfl)).symm

end LSBA
