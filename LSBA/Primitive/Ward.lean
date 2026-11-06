import LSBA.Primitive.Solve

/-!
# Primitive loops: the Ward identity

The 𝒦 half of Lemma 5.1 [fo:lem:mixed-ward]: summing the label between two opposite signs
merges the two neighbouring signs, `Σ_c 𝒦_k(…, c; +, …, −) = (2i)⁻¹W⁻¹η_t⁻¹[𝒦_{k−1}(merged +) −
𝒦_{k−1}(merged −)]`, for both orders of the two signs (the numerator does not change sign).
-/

open MeasureTheory Real Filter Topology Complex Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Closes a pointwise identity of cut maps after unfolding: a case split on the conditions,
then linear arithmetic on the indices. -/
local macro "ward_cases" : tactic =>
  `(tactic| (split_ifs <;> first | rfl | contradiction | omega | (congr 1; omega)))

/-! ## The pair kernels and the initial values -/

section Init

variable {L : ℕ}

/-- `X(1 - cX)⁻¹` is symmetric when `X` is, for every `c` (Lean inverse). -/
private lemma ward_ker_transpose {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (X : Matrix n n R) (hX : Xᵀ = X) (c : R) :
    (X * (1 - c • X)⁻¹)ᵀ = X * (1 - c • X)⁻¹ := by
  have hA : (1 - c • X)ᵀ = 1 - c • X := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hX]
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hA, hX]
  by_cases h : IsUnit (1 - c • X).det
  · have hc : (1 - c • X) * X = X * (1 - c • X) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul]
    calc (1 - c • X)⁻¹ * X = (1 - c • X)⁻¹ * X * ((1 - c • X) * (1 - c • X)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ h, Matrix.mul_one]
      _ = (1 - c • X)⁻¹ * ((1 - c • X) * X) * (1 - c • X)⁻¹ := by
          rw [hc]; simp only [Matrix.mul_assoc]
      _ = X * (1 - c • X)⁻¹ := by
          rw [← Matrix.mul_assoc (1 - c • X)⁻¹, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.mul_zero, Matrix.zero_mul]

/-- The transpose of the pair kernel of (5.13) [fo:eq:pairs] swaps the two signs, for symmetric
`M` and every `t`. -/
private lemma ward_pairK_transpose (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ} (hM : Mᵀ = M) (t : ℝ)
    (s s' : Bool) : (pairK β M t s s')ᵀ = pairK β M t s' s := by
  have h : ∀ a b, M b a = M a b := fun a b => congrFun (congrFun hM a) b
  have hPt : (pairP β M)ᵀ = pairP β M := by
    ext a b; simp only [Matrix.transpose_apply, pairP, Matrix.of_apply, h]
  have hQt : (pairQ β M)ᵀ = pairQ β M := by
    ext a b; simp only [Matrix.transpose_apply, pairQ, Matrix.of_apply, h]
  have hQ := ward_ker_transpose (pairQ β M) hQt (t : ℂ)
  have hP := ward_ker_transpose (pairP β M) hPt t
  cases s <;> cases s' <;>
    simp only [pairK, mixedKer, ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false,
      ← Matrix.transpose_map, hQ, hP]

/-- The cyclic offset without `mod`. -/
private lemma ward_polyOff_eq {k : ℕ} (v w : Fin k) :
    polyOff v w = if v.val ≤ w.val then w.val - v.val else w.val + k - v.val := by
  have := v.isLt
  have := w.isLt
  unfold polyOff
  split_ifs with h
  · rw [show w.val + k - v.val = (w.val - v.val) + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The offset seen from `v` determines the vertex. -/
private lemma ward_polyOff_inj {k : ℕ} {v w w' : Fin k} (h : polyOff v w = polyOff v w') :
    w = w' := by
  rw [ward_polyOff_eq, ward_polyOff_eq] at h
  have := v.isLt
  have := w.isLt
  have := w'.isLt
  apply Fin.ext
  split_ifs at h <;> omega

/-- The next vertex has offset `1`. -/
private lemma ward_polyOff_rot {n : ℕ} (v : Fin (n + 3)) :
    polyOff v (finRotate (n + 3) v) = 1 := by
  rw [ward_polyOff_eq, coe_finRotate]
  have := v.isLt
  by_cases hv : v = Fin.last (n + 2)
  · subst hv
    simp
  · have hv' : v.val ≠ n + 2 := fun h => hv (Fin.ext h)
    simp only [hv, ite_false]
    split_ifs <;> omega

/-- The previous vertex has offset `k - 1`. -/
private lemma ward_polyOff_rot_symm {n : ℕ} (v : Fin (n + 3)) :
    polyOff v ((finRotate (n + 3)).symm v) + 1 = n + 3 := by
  obtain ⟨u, rfl⟩ := (finRotate (n + 3)).surjective v
  rw [Equiv.symm_apply_apply, ward_polyOff_eq, coe_finRotate]
  have := u.isLt
  by_cases hu : u = Fin.last (n + 2)
  · subst hu
    simp
  · have hu' : u.val ≠ n + 2 := fun h => hu (Fin.ext h)
    simp only [hu, ite_false]
    split_ifs <;> omega

/-- Without diagonals, the neighbours of `v` are the vertices at offsets `1` and `k - 1`. -/
private lemma ward_polyNbr_empty {k : ℕ} (hk : 3 ≤ k) (v w : Fin k) :
    PolyNbr (∅ : Finset (Fin k × Fin k)) v w ↔ (polyOff v w = 1 ∨ polyOff v w + 1 = k) := by
  unfold PolyNbr
  simp only [Finset.notMem_empty, or_false]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rintro rfl
  rw [ward_polyOff_eq] at h
  simp at h
  omega

/-- Without diagonals, each vertex `v` has the single corner (next vertex, previous vertex). -/
private lemma ward_polyCorners_empty {n : ℕ} (v : Fin (n + 3)) :
    polyCorners (∅ : Finset (Fin (n + 3) × Fin (n + 3))) v =
      {(finRotate (n + 3) v, (finRotate (n + 3)).symm v)} := by
  have h1 := ward_polyOff_rot v
  have h2 := ward_polyOff_rot_symm v
  ext ⟨w₁, w₂⟩
  simp only [polyCorners, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Prod.mk.injEq, ward_polyNbr_empty (by omega : 3 ≤ n + 3)]
  constructor
  · rintro ⟨hw₁, hw₂, hlt, -⟩
    have e1 : polyOff v w₁ = 1 := by omega
    have e2 : polyOff v w₂ = polyOff v ((finRotate (n + 3)).symm v) := by omega
    exact ⟨ward_polyOff_inj (e1.trans h1.symm), ward_polyOff_inj e2⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨Or.inl h1, Or.inr h2, by omega, ?_⟩
    intro u hu
    omega

/-- Without diagonals, an edge carries the external pre-label. -/
private lemma ward_edgeLab_empty {k : ℕ} (y : Fin k → Fin L)
    (cIn cOut : ↥(∅ : Finset (Fin k × Fin k)) → Fin L) (v w : Fin k) (small : Bool) :
    edgeLab ∅ y cIn cOut v w small = if polyOff v w = 1 then y v else y w := by
  simp [edgeLab]

/-- The one-label inverses at `t = 0` are the identity. -/
private lemma ward_pairV_zero (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (s s' : Bool) :
    pairV β M 0 s s' = 1 := by
  unfold pairV
  split_ifs <;> simp

/-- The empty dissection is a dissection. -/
private lemma ward_empty_mem_dissections (k : ℕ) : ∅ ∈ dissections k := by
  simp [dissections]

/-- At `t = 0` a dissection with a diagonal has value `0` (its link carries `βt = 0`). -/
private lemma ward_dissVal_zero {k : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ)
    (σ : Fin k → Bool) (F : Finset (Fin k × Fin k)) (hF : F ≠ ∅) (a : Fin k → Fin L) :
    dissVal β M 0 σ F a = 0 := by
  obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr hF
  unfold dissVal dissCore
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [mul_eq_zero]
  right
  refine Finset.sum_eq_zero fun cIn _ => Finset.sum_eq_zero fun cOut _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ ⟨d, hd⟩) (by simp), zero_mul]

/-- At `t = 0` the empty dissection of the `k`-gon, `k ≥ 3`, has value
`Π_v (M^{σ_v})_{a_{v-1} a_v}`. -/
private lemma ward_dissVal_empty {n : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ)
    (σ : Fin (n + 3) → Bool) (a : Fin (n + 3) → Fin L) :
    dissVal β M 0 σ ∅ a =
      ∏ j, sgnMat M (σ j) (a ((finRotate (n + 3)).symm j)) (a j) := by
  unfold dissVal
  simp only [ward_pairV_zero, Matrix.one_apply]
  rw [Finset.sum_eq_single a]
  · simp only [ite_true, Finset.prod_const_one, one_mul]
    unfold dissCore
    have hc : ∀ (cIn cOut : ↥(∅ : Finset (Fin (n + 3) × Fin (n + 3))) → Fin L),
        (∏ d : ↥(∅ : Finset (Fin (n + 3) × Fin (n + 3))),
            ((β * 0 : ℝ) : ℂ) * pairV β M 0 (σ d.1.1) (σ d.1.2) (cOut d) (cIn d)) *
          ∏ v : Fin (n + 3), ∏ p ∈ polyCorners ∅ v,
            sgnMat M (σ v) (edgeLab ∅ a cIn cOut v p.2 true)
              (edgeLab ∅ a cIn cOut v p.1 false) =
        ∏ j, sgnMat M (σ j) (a ((finRotate (n + 3)).symm j)) (a j) := by
      intro cIn cOut
      rw [Finset.prod_eq_one (fun d _ => absurd d.2 (Finset.notMem_empty _)), one_mul]
      refine Finset.prod_congr rfl fun v _ => ?_
      have h2 := ward_polyOff_rot_symm v
      have h3 : polyOff v ((finRotate (n + 3)).symm v) ≠ 1 := by omega
      rw [ward_polyCorners_empty, Finset.prod_singleton, ward_edgeLab_empty,
        ward_edgeLab_empty, ward_polyOff_rot]
      simp only [h3, ite_false, ite_true]
    simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
      Fintype.card_fin]
    simp
  · intro y _ hy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi]), zero_mul]
  · simp

/-- The initial value in (5.10) [fo:eq:primitive]: `F_k(0) = Π_j (M^{σ_j})_{a_{j-1} a_j}` for
every primitive data. -/
private lemma ward_primF_init {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (k : ℕ) (hk : 1 ≤ k) (a : Fin k → Fin L) (σ : Fin k → Bool) :
    primF β M m 0 a σ = ∏ j, sgnMat M (σ j) (a ((finRotate k).symm j)) (a j) := by
  have hβ : (β : ℂ) ≠ 0 := by exact_mod_cast hD.pos.ne'
  have hsym : ∀ x y, M y x = M x y := fun x y => congrFun (congrFun hD.symm x) y
  rcases k with _ | _ | _ | n
  · omega
  · have h0 : (finRotate 1).symm 0 = 0 := Subsingleton.elim _ _
    change (if σ 0 then m else star m) = _
    rw [Fin.prod_univ_one, h0]
    cases σ 0 <;> simp [sgnMat, hD.diag]
  · have h0 : (finRotate 2).symm 0 = 1 := by decide
    have h1 : (finRotate 2).symm 1 = 0 := by decide
    change (β : ℂ)⁻¹ * pairK β M 0 (σ 0) (σ 1) (a 0) (a 1) = _
    rw [Fin.prod_univ_two, h0, h1]
    cases σ 0 <;> cases σ 1 <;>
      simp [pairK, mixedKer, pairP, pairQ, sgnMat, Matrix.conjTranspose_apply, hsym (a 0) (a 1),
        hβ, Complex.mul_conj', Complex.conj_mul', sq]
  · change ∑ F ∈ dissections (n + 3), dissVal _ _ 0 σ F a = _
    rw [Finset.sum_eq_single ∅ (fun F _ hF => ward_dissVal_zero _ _ σ F hF a)
      (fun h => absurd (ward_empty_mem_dissections _) h), ward_dissVal_empty]

/-- `F_k` is continuous in `t` on `(-1, 1)`, for every length. -/
private lemma ward_primF_continuousAt {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) {n : ℕ} (a : Fin n → Fin L)
    (σ : Fin n → Bool) : ContinuousAt (fun s => primF β M m s a σ) t := by
  rcases n with _ | _ | n
  · exact continuousAt_const
  · exact continuousAt_const
  · exact (primF_hasDerivAt hD t ht (by omega) a σ).continuousAt

end Init

/-! ## Words indexed by `ℕ`

A word of length `n` is given by two functions on `ℕ` of which only the first `n` values are read;
the cut maps of (5.6) [fo:eq:cuts] become functions on `ℕ`, and lengths that agree as natural
numbers can be exchanged freely. -/

section Words

variable {L : ℕ}

/-- `F_n` at the word whose labels and signs are the first `n` values of `l` and `σ`. -/
private def ward_F (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (t : ℝ) (n : ℕ)
    (l : ℕ → Fin L) (σ : ℕ → Bool) : ℂ :=
  primF β M m t (k := n) (fun p => l p.val) (fun p => σ p.val)

/-- `F_n` reads only the first `n` labels and signs. -/
private lemma ward_F_congr {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} {t : ℝ} {n n' : ℕ}
    (hn : n = n') {l l' : ℕ → Fin L} {σ σ' : ℕ → Bool} (hl : ∀ p < n, l p = l' p)
    (hσ : ∀ p < n, σ p = σ' p) : ward_F β M m t n l σ = ward_F β M m t n' l' σ' := by
  subst hn
  unfold ward_F
  have e1 : (fun p : Fin n => l p.val) = fun p => l' p.val := funext fun p => hl p p.2
  have e2 : (fun p : Fin n => σ p.val) = fun p => σ' p.val := funext fun p => hσ p p.2
  rw [e1, e2]

/-- Labels of `Cut_{L,i,j}^c`, (5.6) [fo:eq:cuts], on `ℕ`. -/
private def ward_cL {α : Type*} (l : ℕ → α) (i j : ℕ) (c : α) : ℕ → α :=
  fun p => if p < i then l p else if p = i then c else l (p + j - i - 1)

/-- Signs of `Cut_{L,i,j}^c` on `ℕ`. -/
private def ward_cLS (σ : ℕ → Bool) (i j : ℕ) : ℕ → Bool :=
  fun p => if p ≤ i then σ p else σ (p + j - i - 1)

/-- Labels of `Cut_{R,i,j}^c` on `ℕ`. -/
private def ward_cR {α : Type*} (l : ℕ → α) (i j : ℕ) (c : α) : ℕ → α :=
  fun p => if p < j - i then l (i + p) else c

/-- Signs of `Cut_{R,i,j}^c` on `ℕ`. -/
private def ward_cRS (σ : ℕ → Bool) (i _j : ℕ) : ℕ → Bool := fun p => σ (i + p)

/-- The quadratic cut sum of (5.10) [fo:eq:primitive] for a family `F` of words on `ℕ`. -/
private def ward_cutN (F : ℕ → (ℕ → Fin L) → (ℕ → Bool) → ℂ) (n : ℕ) (l : ℕ → Fin L)
    (σ : ℕ → Bool) : ℂ :=
  ∑ j ∈ range n, ∑ i ∈ range j, ∑ c : Fin L,
    F (n + i - j + 1) (ward_cL l i j c) (ward_cLS σ i j) *
      F (j - i + 1) (ward_cR l i j c) (ward_cRS σ i j)

/-- The pairs `i < j` of `Fin n` as a double sum over `ℕ`. -/
private lemma ward_sum_pairs (n : ℕ) (G : ℕ → ℕ → ℂ) :
    ∑ i : Fin n, ∑ j : Fin n, (if i < j then G i j else 0) =
      ∑ j ∈ range n, ∑ i ∈ range j, G i j := by
  rw [Finset.sum_comm, Finset.sum_range (fun j => ∑ i ∈ range j, G i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ∀ i : Fin n, (if i < j then G i j else 0) =
      (fun x : ℕ => if x < j.val then G x j else 0) i.val := fun i => rfl
  rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.sum_range (fun x : ℕ =>
    if x < j.val then G x j else 0), ← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  have := j.isLt
  omega

/-- The cut sum `cutSumFam` of `F` at a word on `ℕ`. -/
private lemma ward_cutSumFam_eq (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (t : ℝ) (n : ℕ)
    (l : ℕ → Fin L) (σ : ℕ → Bool) :
    cutSumFam (fun n b τ => primF β M m t (k := n) b τ) (fun p : Fin n => l p.val)
        (fun p => σ p.val) = ward_cutN (ward_F β M m t) n l σ := by
  unfold cutSumFam ward_cutN
  rw [← ward_sum_pairs]
  rfl

/-- (5.10) [fo:eq:primitive] for words on `ℕ`. -/
private lemma ward_F_hasDerivAt {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) {n : ℕ} (hn : 2 ≤ n)
    (l : ℕ → Fin L) (σ : ℕ → Bool) :
    HasDerivAt (fun s => ward_F β M m s n l σ)
      ((β : ℂ) * ward_cutN (ward_F β M m t) n l σ) t := by
  have h := primF_hasDerivAt hD t ht hn (fun p : Fin n => l p.val) (fun p => σ p.val)
  rw [ward_cutSumFam_eq] at h
  exact h

/-- Words on `ℕ` are continuous in `t` on `(-1, 1)`. -/
private lemma ward_F_continuousAt {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) (n : ℕ) (l : ℕ → Fin L)
    (σ : ℕ → Bool) : ContinuousAt (fun s => ward_F β M m s n l σ) t :=
  ward_primF_continuousAt hD ht _ _

/-- On `[0, t]`, `t < 1`, the loops of a fixed length are bounded uniformly in the word. -/
private lemma ward_F_bound {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht1 : t < 1) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Set.Icc (0 : ℝ) t, ∀ (l : ℕ → Fin L) (σ : ℕ → Bool),
      ‖ward_F β M m x n l σ‖ ≤ B := by
  have hg : ContinuousOn (fun x (p : (Fin n → Fin L) × (Fin n → Bool)) => primF β M m x p.1 p.2)
      (Set.Icc 0 t) := continuousOn_pi.mpr fun p x hx =>
    (ward_primF_continuousAt hD ⟨by linarith [hx.1], by linarith [hx.2]⟩ p.1 p.2).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  refine ⟨max B 0, le_max_right _ _, fun x hx l σ => ?_⟩
  refine le_trans ?_ ((hB x hx).trans (le_max_left _ _))
  exact norm_le_pi_norm (fun p : (Fin n → Fin L) × (Fin n → Bool) => primF β M m x p.1 p.2)
    (fun p => l p.val, fun p => σ p.val)

end Words

/-! ## Gronwall's inequality and counting -/

/-- A vector of functions vanishing at `0` whose derivative is bounded by a multiple of its sup
norm on `[0, t]` vanishes at `t`. -/
private lemma ward_gronwall {ι : Type*} [Fintype ι] (f f' : ℝ → ι → ℂ) {t C : ℝ} (ht : 0 ≤ t)
    (hC : 0 ≤ C) (hc : ∀ i, ContinuousOn (fun x => f x i) (Set.Icc 0 t))
    (hd : ∀ x ∈ Set.Ico 0 t, ∀ i, HasDerivAt (fun x => f x i) (f' x i) x)
    (hb : ∀ x ∈ Set.Ico 0 t, ∀ i, ‖f' x i‖ ≤ C * ‖f x‖)
    (h0 : ∀ i, f 0 i = 0) : ∀ i, f t i = 0 := by
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := f) (f' := f') (K := C)
    (a := 0) (b := t) (continuousOn_pi.mpr hc)
    (fun x hx => hasDerivWithinAt_pi.mpr fun i => (hd x hx i).hasDerivWithinAt) (funext h0)
    (fun x hx => (pi_norm_le_iff_of_nonneg (by positivity)).mpr (hb x hx))
  intro i
  exact congrFun (hz t ⟨ht, le_rfl⟩) i

/-- A triangular double sum with a label sum, bounded termwise. -/
private lemma ward_norm_sum3_le {L N : ℕ} (f : ℕ → ℕ → Fin L → ℂ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ j < N, ∀ i < j, ∀ c, ‖f i j c‖ ≤ b) :
    ‖∑ j ∈ range N, ∑ i ∈ range j, ∑ c, f i j c‖ ≤ N * N * L * b := by
  have hj : ∀ j ∈ range N, ‖∑ i ∈ range j, ∑ c, f i j c‖ ≤ N * L * b := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hi : ∀ i ∈ range j, ‖∑ c, f i j c‖ ≤ L * b := by
      intro i hi
      rw [Finset.mem_range] at hi
      refine (norm_sum_le_of_le _ fun c _ => h j hj i hi c).trans ?_
      simp
    refine (norm_sum_le_of_le _ hi).trans ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (j : ℝ) ≤ N := by exact_mod_cast hj.le
    nlinarith [mul_nonneg (Nat.cast_nonneg L : (0 : ℝ) ≤ L) hb]
  refine (norm_sum_le_of_le _ hj).trans ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring_nf
  rfl

/-- A single sum with a label sum, bounded termwise. -/
private lemma ward_norm_sum2_le {L N : ℕ} (f : ℕ → Fin L → ℂ) {b : ℝ}
    (h : ∀ j < N, ∀ c, ‖f j c‖ ≤ b) :
    ‖∑ j ∈ range N, ∑ c, f j c‖ ≤ N * L * b := by
  have hj : ∀ j ∈ range N, ‖∑ c, f j c‖ ≤ L * b := by
    intro j hj
    rw [Finset.mem_range] at hj
    refine (norm_sum_le_of_le _ fun c _ => h j hj c).trans ?_
    simp
  refine (norm_sum_le_of_le _ hj).trans ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring_nf
  rfl

/-! ## Cyclic invariance of `F_k`

The rotated word solves (5.10) [fo:eq:primitive] up to cuts of the same length, so a Gronwall step
at each length gives `F_k(rotated word) = F_k(word)` for `0 ≤ t < 1`. -/

section Rotation

variable {L : ℕ}


/-- The rotation of a word of length `n`: position `p` reads position `p + 1`, the last position
reads position `0`. -/
private def ward_rot {α : Type*} (n : ℕ) (l : ℕ → α) : ℕ → α :=
  fun p => if p + 1 < n then l (p + 1) else l 0

/-- A word on `Fin n` as a function on `ℕ`. -/
private def ward_ext {α : Type*} {n : ℕ} (hn : 0 < n) (a : Fin n → α) : ℕ → α :=
  fun p => a ⟨p % n, Nat.mod_lt _ hn⟩

private lemma ward_ext_apply {α : Type*} {n : ℕ} (hn : 0 < n) (a : Fin n → α) {p : ℕ}
    (hp : p < n) : ward_ext hn a p = a ⟨p, hp⟩ := by
  simp [ward_ext, Nat.mod_eq_of_lt hp]

/-- The rotation reads only the first `n` values. -/
private lemma ward_rot_congr {α : Type*} {n : ℕ} {l l' : ℕ → α} (h : ∀ p < n, l p = l' p) :
    ∀ p < n, ward_rot n l p = ward_rot n l' p := by
  intro p hp
  simp only [ward_rot]
  split_ifs with h1
  · exact h _ h1
  · exact h 0 (by omega)

/-- At length one the rotation is trivial. -/
private lemma ward_rot_one {α : Type*} (l : ℕ → α) : ∀ p < 1, ward_rot 1 l p = l p := by
  intro p hp
  obtain rfl : p = 0 := by omega
  simp [ward_rot]

private lemma ward_finRotate_val {n : ℕ} (j : Fin n) :
    (finRotate n j).val = if j.val + 1 < n then j.val + 1 else 0 := by
  rcases n with _ | n
  · exact j.elim0
  · rw [coe_finRotate]
    by_cases h : j = Fin.last n
    · subst h
      simp
    · have h1 : j.val ≠ n := fun e => h (Fin.ext e)
      have := j.isLt
      simp only [h, ite_false]
      split_ifs <;> omega

private lemma ward_rot_fin {α : Type*} {n : ℕ} (l : ℕ → α) (u : Fin n) :
    ward_rot n l u.val = l (finRotate n u).val := by
  rw [ward_finRotate_val]
  simp only [ward_rot]
  split_ifs <;> rfl

/-- Cyclic invariance at `t = 0`, where `F_n` is the `M`-loop. -/
private lemma ward_rot_zero {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {n : ℕ} (hn : 1 ≤ n) (l : ℕ → Fin L) (σ : ℕ → Bool) :
    ward_F β M m 0 n (ward_rot n l) (ward_rot n σ) = ward_F β M m 0 n l σ := by
  unfold ward_F
  rw [ward_primF_init hD n hn, ward_primF_init hD n hn,
    ← Equiv.prod_comp (finRotate n)
      (fun j => sgnMat M (σ j.val) (l ((finRotate n).symm j).val) (l j.val))]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Equiv.symm_apply_apply, ward_rot_fin, Equiv.apply_symm_apply]

/-- Cyclic invariance at length two, for every `t` (the pair kernel is symmetric up to the
order of the signs). -/
private lemma ward_rot_two (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ} (hM : Mᵀ = M) (m : ℂ) (t : ℝ)
    (l : ℕ → Fin L) (σ : ℕ → Bool) :
    ward_F β M m t 2 (ward_rot 2 l) (ward_rot 2 σ) = ward_F β M m t 2 l σ := by
  change (β : ℂ)⁻¹ * pairK β M t (ward_rot 2 σ 0) (ward_rot 2 σ 1) (ward_rot 2 l 0)
      (ward_rot 2 l 1) = (β : ℂ)⁻¹ * pairK β M t (σ 0) (σ 1) (l 0) (l 1)
  simp only [ward_rot, Nat.reduceAdd, Nat.one_lt_ofNat, ite_true, lt_self_iff_false, ite_false]
  rw [← ward_pairK_transpose β hM t (σ 0) (σ 1)]
  rfl

/-- The left cut of the rotated word at `(i, j)`, `j ≤ n - 2`, is the rotation of the left cut
at `(i + 1, j + 1)`. -/
private lemma ward_rot_cL {α : Type*} {n i j : ℕ} (hj : j + 2 ≤ n) (hij : i < j) (l : ℕ → α)
    (c : α) : ∀ p < n + i - j + 1,
      ward_cL (ward_rot n l) i j c p =
        ward_rot (n + i - j + 1) (ward_cL l (i + 1) (j + 1) c) p := by
  intro p hp
  simp only [ward_cL, ward_rot]
  ward_cases

private lemma ward_rot_cLS {n i j : ℕ} (hj : j + 2 ≤ n) (hij : i < j) (σ : ℕ → Bool) :
    ∀ p < n + i - j + 1,
      ward_cLS (ward_rot n σ) i j p = ward_rot (n + i - j + 1) (ward_cLS σ (i + 1) (j + 1)) p := by
  intro p hp
  simp only [ward_cLS, ward_rot]
  ward_cases

private lemma ward_rot_cR {α : Type*} {n i j : ℕ} (hj : j + 2 ≤ n) (hij : i < j) (l : ℕ → α)
    (c : α) :
    ∀ p < j - i + 1, ward_cR (ward_rot n l) i j c p = ward_cR l (i + 1) (j + 1) c p := by
  intro p hp
  simp only [ward_cR, ward_rot]
  ward_cases

private lemma ward_rot_cRS {n i j : ℕ} (hj : j + 2 ≤ n) (hij : i < j) (σ : ℕ → Bool) :
    ∀ p < j - i + 1, ward_cRS (ward_rot n σ) i j p = ward_cRS σ (i + 1) (j + 1) p := by
  intro p hp
  simp only [ward_cRS, ward_rot]
  ward_cases

/-- The left cut of the rotated word at `(j, n - 1)` is the rotation of the right cut at
`(0, j + 1)`. -/
private lemma ward_rot_cL_last {α : Type*} {n j : ℕ} (hj : j < n) (l : ℕ → α) (c : α) :
    ∀ p < j + 2,
      ward_cL (ward_rot (n + 1) l) j n c p = ward_rot (j + 2) (ward_cR l 0 (j + 1) c) p := by
  intro p hp
  simp only [ward_cL, ward_cR, ward_rot]
  ward_cases

private lemma ward_rot_cLS_last {n j : ℕ} (hj : j < n) (σ : ℕ → Bool) :
    ∀ p < j + 2,
      ward_cLS (ward_rot (n + 1) σ) j n p = ward_rot (j + 2) (ward_cRS σ 0 (j + 1)) p := by
  intro p hp
  simp only [ward_cLS, ward_cRS, ward_rot]
  ward_cases

/-- The right cut of the rotated word at `(j, n - 1)` is the rotation of the left cut at
`(0, j + 1)`. -/
private lemma ward_rot_cR_last {α : Type*} {n j : ℕ} (hj : j < n) (l : ℕ → α) (c : α) :
    ∀ p < n - j + 1,
      ward_cR (ward_rot (n + 1) l) j n c p = ward_rot (n - j + 1) (ward_cL l 0 (j + 1) c) p := by
  intro p hp
  simp only [ward_cL, ward_cR, ward_rot]
  ward_cases

private lemma ward_rot_cRS_last {n j : ℕ} (hj : j < n) (σ : ℕ → Bool) :
    ∀ p < n - j + 1,
      ward_cRS (ward_rot (n + 1) σ) j n p = ward_rot (n - j + 1) (ward_cLS σ 0 (j + 1)) p := by
  intro p hp
  simp only [ward_cLS, ward_cRS, ward_rot]
  ward_cases

/-- The cut sums of a word and of its rotation differ by cut terms of the same length, where the
rotation acts on a loop of length `n + 1` next to a loop of length `2`. -/
private lemma ward_rot_cut_le {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} {x : ℝ} {n : ℕ}
    (hn : 2 ≤ n) {B ε : ℝ} (hB0 : 0 ≤ B) (hε0 : 0 ≤ ε)
    (hrot : ∀ n', 2 ≤ n' → n' < n + 1 → ∀ (l : ℕ → Fin L) (σ : ℕ → Bool),
      ward_F β M m x n' (ward_rot n' l) (ward_rot n' σ) = ward_F β M m x n' l σ)
    (hB : ∀ (l : ℕ → Fin L) (σ : ℕ → Bool), ‖ward_F β M m x 2 l σ‖ ≤ B)
    (hε : ∀ (l : ℕ → Fin L) (σ : ℕ → Bool),
      ‖ward_F β M m x (n + 1) (ward_rot (n + 1) l) (ward_rot (n + 1) σ) -
        ward_F β M m x (n + 1) l σ‖ ≤ ε)
    (l : ℕ → Fin L) (σ : ℕ → Bool) :
    ‖ward_cutN (ward_F β M m x) (n + 1) (ward_rot (n + 1) l) (ward_rot (n + 1) σ) -
        ward_cutN (ward_F β M m x) (n + 1) l σ‖ ≤ (n * n * L + n * L) * (B * ε) := by
  set F := ward_F β M m x with hF
  set rl := ward_rot (n + 1) l with hrl
  set rσ := ward_rot (n + 1) σ with hrσ
  have h1 : ∀ j < n, ∀ i < j, ∀ c : Fin L,
      ‖F (n + 1 + i - j + 1) (ward_cL rl i j c) (ward_cLS rσ i j) *
          F (j - i + 1) (ward_cR rl i j c) (ward_cRS rσ i j) -
        F (n + 1 + (i + 1) - (j + 1) + 1) (ward_cL l (i + 1) (j + 1) c)
            (ward_cLS σ (i + 1) (j + 1)) *
          F (j + 1 - (i + 1) + 1) (ward_cR l (i + 1) (j + 1) c) (ward_cRS σ (i + 1) (j + 1))‖ ≤
        B * ε := by
    intro j hj i hij c
    have eL : F (n + 1 + i - j + 1) (ward_cL rl i j c) (ward_cLS rσ i j) =
        F (n + 1 + i - j + 1) (ward_rot (n + 1 + i - j + 1) (ward_cL l (i + 1) (j + 1) c))
          (ward_rot (n + 1 + i - j + 1) (ward_cLS σ (i + 1) (j + 1))) :=
      ward_F_congr rfl (ward_rot_cL (by omega) hij l c) (ward_rot_cLS (by omega) hij σ)
    have eL' : F (n + 1 + (i + 1) - (j + 1) + 1) (ward_cL l (i + 1) (j + 1) c)
        (ward_cLS σ (i + 1) (j + 1)) =
        F (n + 1 + i - j + 1) (ward_cL l (i + 1) (j + 1) c) (ward_cLS σ (i + 1) (j + 1)) :=
      ward_F_congr (by omega) (fun _ _ => rfl) (fun _ _ => rfl)
    have eR : F (j - i + 1) (ward_cR rl i j c) (ward_cRS rσ i j) =
        F (j + 1 - (i + 1) + 1) (ward_cR l (i + 1) (j + 1) c) (ward_cRS σ (i + 1) (j + 1)) :=
      ward_F_congr (by omega) (ward_rot_cR (by omega) hij l c) (ward_rot_cRS (by omega) hij σ)
    rw [eL, eL', eR, ← sub_mul]
    rcases Nat.lt_or_ge (i + 1) j with hlt | hge
    · rw [hrot _ (by omega) (by omega), sub_self, zero_mul, norm_zero]
      positivity
    · obtain rfl : j = i + 1 := by omega
      have e1 : n + 1 + i - (i + 1) + 1 = n + 1 := by omega
      have e2 : i + 1 + 1 - (i + 1) + 1 = 2 := by omega
      rw [e1, e2, norm_mul, mul_comm B ε]
      exact mul_le_mul (hε _ _) (hB _ _) (norm_nonneg _) hε0
  have h2 : ∀ j < n, ∀ c : Fin L,
      ‖F (n + 1 + j - n + 1) (ward_cL rl j n c) (ward_cLS rσ j n) *
          F (n - j + 1) (ward_cR rl j n c) (ward_cRS rσ j n) -
        F (n + 1 + 0 - (j + 1) + 1) (ward_cL l 0 (j + 1) c) (ward_cLS σ 0 (j + 1)) *
          F (j + 1 - 0 + 1) (ward_cR l 0 (j + 1) c) (ward_cRS σ 0 (j + 1))‖ ≤ B * ε := by
    intro j hj c
    have eA : F (n + 1 + j - n + 1) (ward_cL rl j n c) (ward_cLS rσ j n) =
        F (j + 2) (ward_rot (j + 2) (ward_cR l 0 (j + 1) c))
          (ward_rot (j + 2) (ward_cRS σ 0 (j + 1))) :=
      ward_F_congr (by omega) (fun p hp => ward_rot_cL_last hj l c p (by omega))
        (fun p hp => ward_rot_cLS_last hj σ p (by omega))
    have eB : F (n - j + 1) (ward_cR rl j n c) (ward_cRS rσ j n) =
        F (n - j + 1) (ward_rot (n - j + 1) (ward_cL l 0 (j + 1) c))
          (ward_rot (n - j + 1) (ward_cLS σ 0 (j + 1))) :=
      ward_F_congr rfl (ward_rot_cR_last hj l c) (ward_rot_cRS_last hj σ)
    have eC : F (n + 1 + 0 - (j + 1) + 1) (ward_cL l 0 (j + 1) c) (ward_cLS σ 0 (j + 1)) =
        F (n - j + 1) (ward_cL l 0 (j + 1) c) (ward_cLS σ 0 (j + 1)) :=
      ward_F_congr (by omega) (fun _ _ => rfl) (fun _ _ => rfl)
    have eD : F (j + 1 - 0 + 1) (ward_cR l 0 (j + 1) c) (ward_cRS σ 0 (j + 1)) =
        F (j + 2) (ward_cR l 0 (j + 1) c) (ward_cRS σ 0 (j + 1)) :=
      ward_F_congr (by omega) (fun _ _ => rfl) (fun _ _ => rfl)
    rw [eA, eB, eC, eD]
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [hrot (0 + 2) (by omega) (by omega)]
      have e : n - 0 + 1 = n + 1 := by omega
      rw [e, show ∀ a b b' : ℂ, a * b - b' * a = a * (b - b') from fun _ _ _ => by ring,
        norm_mul]
      exact mul_le_mul (hB _ _) (hε _ _) (norm_nonneg _) hB0
    · rcases Nat.lt_or_ge (j + 1) n with hjn | hjn
      · rw [hrot (j + 2) (by omega) (by omega), hrot (n - j + 1) (by omega) (by omega), mul_comm,
          sub_self, norm_zero]
        positivity
      · have e1 : j + 2 = n + 1 := by omega
        have e2 : n - j + 1 = 2 := by omega
        rw [e1, e2, hrot 2 le_rfl (by omega),
          show ∀ a a' b : ℂ, a * b - b * a' = (a - a') * b from fun _ _ _ => by ring, norm_mul,
          mul_comm B ε]
        exact mul_le_mul (hε _ _) (hB _ _) (norm_nonneg _) hε0
  have key : ward_cutN F (n + 1) rl rσ - ward_cutN F (n + 1) l σ =
      ∑ j ∈ range n, ∑ i ∈ range j, ∑ c : Fin L,
        (F (n + 1 + i - j + 1) (ward_cL rl i j c) (ward_cLS rσ i j) *
            F (j - i + 1) (ward_cR rl i j c) (ward_cRS rσ i j) -
          F (n + 1 + (i + 1) - (j + 1) + 1) (ward_cL l (i + 1) (j + 1) c)
              (ward_cLS σ (i + 1) (j + 1)) *
            F (j + 1 - (i + 1) + 1) (ward_cR l (i + 1) (j + 1) c)
              (ward_cRS σ (i + 1) (j + 1))) +
      ∑ j ∈ range n, ∑ c : Fin L,
        (F (n + 1 + j - n + 1) (ward_cL rl j n c) (ward_cLS rσ j n) *
            F (n - j + 1) (ward_cR rl j n c) (ward_cRS rσ j n) -
          F (n + 1 + 0 - (j + 1) + 1) (ward_cL l 0 (j + 1) c) (ward_cLS σ 0 (j + 1)) *
            F (j + 1 - 0 + 1) (ward_cR l 0 (j + 1) c) (ward_cRS σ 0 (j + 1))) := by
    simp only [Finset.sum_sub_distrib]
    unfold ward_cutN
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Finset.sum_range_succ', Finset.range_zero, Finset.sum_empty, add_zero,
      Finset.sum_add_distrib]
    ring
  rw [key]
  refine (norm_add_le _ _).trans ?_
  have b1 := ward_norm_sum3_le _ (mul_nonneg hB0 hε0) h1
  have b2 := ward_norm_sum2_le _ h2
  linarith

/-- Cyclic invariance of `F_n` for `0 ≤ t < 1`: `F_n(rotated word) = F_n(word)`. -/
private lemma ward_rot_holds {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) :
    ∀ n, 1 ≤ n → ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (l : ℕ → Fin L) (σ : ℕ → Bool),
      ward_F β M m t n (ward_rot n l) (ward_rot n σ) = ward_F β M m t n l σ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn t ht l σ
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · interval_cases n
    · exact ward_F_congr rfl (ward_rot_one l) (ward_rot_one σ)
    · exact ward_rot_two β hD.symm m t l σ
  · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hn0 : 0 < n + 1 := by omega
    have hIoo : ∀ x ∈ Set.Icc (0 : ℝ) t, x ∈ Set.Ioo (-1 : ℝ) 1 :=
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, ht.2]⟩
    have hIco : ∀ x ∈ Set.Icc (0 : ℝ) t, x ∈ Set.Ico (0 : ℝ) 1 :=
      fun x hx => ⟨hx.1, by linarith [hx.2, ht.2]⟩
    obtain ⟨B, hB0, hB⟩ := ward_F_bound hD ht.2 2
    have hext : ∀ {α : Type} (l' : ℕ → α), ∀ q < n + 1,
        ward_ext hn0 (fun p : Fin (n + 1) => l' p.val) q = l' q := fun l' q hq => by
      rw [ward_ext_apply hn0 _ hq]
    set f : ℝ → (Fin (n + 1) → Fin L) × (Fin (n + 1) → Bool) → ℂ := fun x w =>
      ward_F β M m x (n + 1) (ward_rot (n + 1) (ward_ext hn0 w.1))
          (ward_rot (n + 1) (ward_ext hn0 w.2)) -
        ward_F β M m x (n + 1) (ward_ext hn0 w.1) (ward_ext hn0 w.2) with hf
    set f' : ℝ → (Fin (n + 1) → Fin L) × (Fin (n + 1) → Bool) → ℂ := fun x w =>
      (β : ℂ) * (ward_cutN (ward_F β M m x) (n + 1) (ward_rot (n + 1) (ward_ext hn0 w.1))
          (ward_rot (n + 1) (ward_ext hn0 w.2)) -
        ward_cutN (ward_F β M m x) (n + 1) (ward_ext hn0 w.1) (ward_ext hn0 w.2)) with hf'
    have hfw : ∀ x (l' : ℕ → Fin L) (σ' : ℕ → Bool),
        f x (fun p => l' p.val, fun p => σ' p.val) =
          ward_F β M m x (n + 1) (ward_rot (n + 1) l') (ward_rot (n + 1) σ') -
            ward_F β M m x (n + 1) l' σ' := by
      intro x l' σ'
      simp only [hf]
      rw [ward_F_congr rfl (ward_rot_congr (hext l')) (ward_rot_congr (hext σ')),
        ward_F_congr rfl (hext l') (hext σ')]
    have hz := ward_gronwall f f' ht.1
      (C := |β| * ((n * n * L + n * L) * B)) (by positivity)
      (fun w => by
        refine ContinuousOn.sub ?_ ?_ <;>
          exact fun x hx => (ward_F_continuousAt hD (hIoo x hx) _ _ _).continuousWithinAt)
      (fun x hx w => by
        have hx' : x ∈ Set.Icc (0 : ℝ) t := ⟨hx.1, hx.2.le⟩
        have h := (ward_F_hasDerivAt hD (hIoo x hx') (by omega : 2 ≤ n + 1)
          (ward_rot (n + 1) (ward_ext hn0 w.1)) (ward_rot (n + 1) (ward_ext hn0 w.2))).sub
          (ward_F_hasDerivAt hD (hIoo x hx') (by omega : 2 ≤ n + 1)
            (ward_ext hn0 w.1) (ward_ext hn0 w.2))
        refine h.congr_deriv ?_
        simp only [hf']
        ring)
      (fun x hx w => by
        have hx' : x ∈ Set.Icc (0 : ℝ) t := ⟨hx.1, hx.2.le⟩
        simp only [hf', norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hcut := ward_rot_cut_le (β := β) (M := M) (m := m) (x := x) (n := n) (by omega)
          hB0 (norm_nonneg (f x))
          (fun n' h2 hlt l' σ' => ih n' hlt (by omega) x (hIco x hx') l' σ')
          (hB x hx')
          (fun l' σ' => by
            rw [← hfw]
            exact norm_le_pi_norm (f x) _)
          (ward_ext hn0 w.1) (ward_ext hn0 w.2)
        calc |β| * ‖ward_cutN (ward_F β M m x) (n + 1) (ward_rot (n + 1) (ward_ext hn0 w.1))
              (ward_rot (n + 1) (ward_ext hn0 w.2)) -
            ward_cutN (ward_F β M m x) (n + 1) (ward_ext hn0 w.1) (ward_ext hn0 w.2)‖ ≤
            |β| * ((n * n * L + n * L) * (B * ‖f x‖)) :=
              mul_le_mul_of_nonneg_left hcut (abs_nonneg β)
          _ = |β| * ((n * n * L + n * L) * B) * ‖f x‖ := by ring)
      (fun w => by
        simp only [hf]
        rw [ward_rot_zero hD hn0, sub_self])
    have h := hz (fun p => l p.val, fun p => σ p.val)
    rw [hfw] at h
    exact sub_eq_zero.mp h

end Rotation

/-! ## The two sides of the Ward identity

For a word `(a_0, …, a_{k-1})` with signs `(s, τ_1, …, τ_{k-1})`, the left side sums `F_{k+1}` over
a last label `c` with last sign `!s`, and the right side is
`(2iβ(1-t) Im m)⁻¹ [F_k(joined +) - F_k(joined -)]`. -/

section Sides

variable {L : ℕ}

/-- The word `(l_0, …, l_{k-1}, c)` on `ℕ`. -/
private def ward_snoc {α : Type*} (k : ℕ) (l : ℕ → α) (c : α) : ℕ → α :=
  fun p => if p < k then l p else c

/-- The signs `(s, τ_1, …, τ_{k-1}, !s)` on `ℕ`. -/
private def ward_ws (k : ℕ) (τ : ℕ → Bool) (s : Bool) : ℕ → Bool :=
  fun p => if p = 0 then s else if p < k then τ p else !s

/-- The joined signs `(b, τ_1, …, τ_{k-1})` on `ℕ`. -/
private def ward_ms (τ : ℕ → Bool) (b : Bool) : ℕ → Bool :=
  fun p => if p = 0 then b else τ p

/-- The constant `(2iβ(1-t) Im m)⁻¹` of (5.11) [gc:eq:ward] in the normalization `F_k`. -/
private def ward_kap (β : ℝ) (m : ℂ) (t : ℝ) : ℂ := (2 * I * (((1 - t) * β * m.im : ℝ) : ℂ))⁻¹

/-- The left side `Σ_c F_{k+1}(l, c; s, τ, !s)`. -/
private def ward_X (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (t : ℝ) (k : ℕ)
    (l : ℕ → Fin L) (τ : ℕ → Bool) (s : Bool) : ℂ :=
  ∑ c : Fin L, ward_F β M m t (k + 1) (ward_snoc k l c) (ward_ws k τ s)

/-- The right side `(2iβ(1-t) Im m)⁻¹ [F_k(l; +, τ) - F_k(l; -, τ)]`. -/
private def ward_Y (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (t : ℝ) (k : ℕ)
    (l : ℕ → Fin L) (τ : ℕ → Bool) : ℂ :=
  ward_kap β m t * (ward_F β M m t k l (ward_ms τ true) - ward_F β M m t k l (ward_ms τ false))

/-- The left side reads only the labels `l_0, …, l_{k-1}` and the signs `τ_1, …, τ_{k-1}`. -/
private lemma ward_X_congr {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} {t : ℝ} {k : ℕ}
    {l l' : ℕ → Fin L} {τ τ' : ℕ → Bool} (s : Bool) (hl : ∀ p < k, l p = l' p)
    (hτ : ∀ p, 1 ≤ p → p < k → τ p = τ' p) :
    ward_X β M m t k l τ s = ward_X β M m t k l' τ' s := by
  unfold ward_X
  refine Finset.sum_congr rfl fun c _ => ward_F_congr rfl (fun p hp => ?_) (fun p hp => ?_)
  · simp only [ward_snoc]
    split_ifs with h
    · exact hl p h
    · rfl
  · simp only [ward_ws]
    split_ifs with h1 h2
    · rfl
    · exact hτ p (by omega) h2
    · rfl

/-- The right side reads only the labels `l_0, …, l_{k-1}` and the signs `τ_1, …, τ_{k-1}`. -/
private lemma ward_Y_congr {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} {t : ℝ} {k : ℕ}
    {l l' : ℕ → Fin L} {τ τ' : ℕ → Bool} (hl : ∀ p < k, l p = l' p)
    (hτ : ∀ p, 1 ≤ p → p < k → τ p = τ' p) :
    ward_Y β M m t k l τ = ward_Y β M m t k l' τ' := by
  have h : ∀ b, ∀ p < k, ward_ms τ b p = ward_ms τ' b p := by
    intro b p hp
    simp only [ward_ms]
    split_ifs with h1
    · rfl
    · exact hτ p (by omega) hp
  unfold ward_Y
  rw [ward_F_congr rfl hl (h true), ward_F_congr rfl hl (h false)]

/-- The left side at `k = 1` is the row sum `β⁻¹(1-t)⁻¹` of the mixed kernel (5.13)
[fo:eq:pairs]. -/
private lemma ward_X_one {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (l : ℕ → Fin L) (τ : ℕ → Bool) (s : Bool) :
    ward_X β M m t 1 l τ s = (β : ℂ)⁻¹ * (((1 - t)⁻¹ : ℝ) : ℂ) := by
  have hrow := (mixedKer_nonneg_row (pairP β M)
    (fun a b => mul_nonneg hD.pos.le (sq_nonneg _)) hD.row_sum t ht0 ht1).2 (l 0)
  have e : ∀ c : Fin L, ward_F β M m t (1 + 1) (ward_snoc 1 l c) (ward_ws 1 τ s) =
      (β : ℂ)⁻¹ * ((mixedKer (pairP β M) t (l 0) c : ℝ) : ℂ) := by
    intro c
    change (β : ℂ)⁻¹ * pairK β M t (ward_ws 1 τ s 0) (ward_ws 1 τ s 1) (ward_snoc 1 l c 0)
      (ward_snoc 1 l c 1) = _
    cases s <;> simp [ward_ws, ward_snoc, pairK]
  unfold ward_X
  rw [Finset.sum_congr rfl fun c _ => e c, ← Finset.mul_sum, ← Complex.ofReal_sum, hrow]

/-- The right side at `k = 1`: `(2iβ(1-t) Im m)⁻¹ (m - m̄) = β⁻¹(1-t)⁻¹`. -/
private lemma ward_Y_one {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {t : ℝ} (ht1 : t < 1) (l : ℕ → Fin L) (τ : ℕ → Bool) :
    ward_Y β M m t 1 l τ = (β : ℂ)⁻¹ * (((1 - t)⁻¹ : ℝ) : ℂ) := by
  have e : ∀ b, ward_F β M m t 1 l (ward_ms τ b) = if b then m else star m := by
    intro b
    change (if ward_ms τ b 0 then m else star m) = _
    simp [ward_ms]
  have hm : m - star m = 2 * I * (m.im : ℂ) := by
    apply Complex.ext <;> simp; ring
  have hβ : (β : ℂ) ≠ 0 := by exact_mod_cast hD.pos.ne'
  have hμ : (m.im : ℂ) ≠ 0 := by exact_mod_cast hD.im_pos.ne'
  have ht : ((1 - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show (1 - t : ℝ) ≠ 0 by linarith)
  unfold ward_Y ward_kap
  rw [e, e]
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [hm]
  push_cast
  push_cast at ht
  field_simp

end Sides

/-! ## The Ward identity at `t = 0`

At `t = 0` the loops are `M`-loops; summing the last label gives `(M^{!s} M^s)_{a_{k-1} a_0}`,
and `M M* = M* M = (2iβ Im m)⁻¹ (M - M*)` (the characteristic identity of Appendix B.1
[sec:gc-objects] and the symmetry of `M`). -/

section Initial

variable {L : ℕ}

private lemma ward_finRotate_symm_val {n : ℕ} (j : Fin n) :
    ((finRotate n).symm j).val = if j.val = 0 then n - 1 else j.val - 1 := by
  have h := ward_finRotate_val ((finRotate n).symm j)
  rw [Equiv.apply_symm_apply] at h
  have := ((finRotate n).symm j).isLt
  split_ifs at h ⊢ <;> omega

/-- `F_n(0)` on `ℕ`: the `M`-loop `Π_j (M^{σ_j})_{l_{j-1} l_j}`. -/
private lemma ward_F_zero {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {n : ℕ} (hn : 1 ≤ n) (l : ℕ → Fin L) (σ : ℕ → Bool) :
    ward_F β M m 0 n l σ =
      ∏ j ∈ range n, sgnMat M (σ j) (l (if j = 0 then n - 1 else j - 1)) (l j) := by
  unfold ward_F
  rw [ward_primF_init hD n hn, Finset.prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [ward_finRotate_symm_val]

/-- `M` is normal under the primitive data: `M* M = M M*`. -/
private lemma ward_normal {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) : Mᴴ * M = M * Mᴴ := by
  have hsym : ∀ a b, M b a = M a b := fun a b => congrFun (congrFun hD.symm a) b
  have hT : (Mᴴ)ᵀ = Mᴴ := by
    ext a b
    simp [Matrix.conjTranspose_apply, hsym a b]
  have h2 := congrArg Matrix.transpose hD.ward
  rw [Matrix.transpose_sub, hD.symm, hT, Matrix.transpose_smul, Matrix.transpose_mul, hT,
    hD.symm, hD.ward] at h2
  have hc : ((2 * β * m.im : ℝ) * I : ℂ) ≠ 0 := by
    have : (2 * β * m.im : ℝ) ≠ 0 := by
      have := hD.pos; have := hD.im_pos; positivity
    exact mul_ne_zero (by exact_mod_cast this) I_ne_zero
  exact (smul_right_injective _ hc h2).symm

/-- `M^{!s} M^s = (2iβ Im m)⁻¹ (M - M*)` for both signs `s`. -/
private lemma ward_merge {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (s : Bool) :
    sgnMat M (!s) * sgnMat M s = ward_kap β m 0 • (M - Mᴴ) := by
  have hc : ((2 * β * m.im : ℝ) * I : ℂ) ≠ 0 := by
    have : (2 * β * m.im : ℝ) ≠ 0 := by
      have := hD.pos; have := hD.im_pos; positivity
    exact mul_ne_zero (by exact_mod_cast this) I_ne_zero
  have hk : ward_kap β m 0 = ((2 * β * m.im : ℝ) * I : ℂ)⁻¹ := by
    unfold ward_kap
    push_cast
    ring_nf
  have hMM : M * Mᴴ = ward_kap β m 0 • (M - Mᴴ) := by
    rw [hk, hD.ward, smul_smul, inv_mul_cancel₀ hc, one_smul]
  cases s
  · simpa [sgnMat] using hMM
  · simpa [sgnMat, ward_normal hD] using hMM

/-- The left side at `t = 0` before the label sum: the `M`-loop of `(l, c; s, τ, !s)`. -/
private lemma ward_X_zero_term {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (k : ℕ) (l : ℕ → Fin L) (τ : ℕ → Bool) (s : Bool) (c : Fin L) :
    ward_F β M m 0 (k + 1 + 1) (ward_snoc (k + 1) l c) (ward_ws (k + 1) τ s) =
      (∏ j ∈ range k, sgnMat M (τ (j + 1)) (l j) (l (j + 1))) *
        (sgnMat M (!s) (l k) c * sgnMat M s c (l 0)) := by
  rw [ward_F_zero hD (by omega), Finset.prod_range_succ, Finset.prod_range_succ']
  have hmid : ∀ j ∈ range k, sgnMat M (ward_ws (k + 1) τ s (j + 1))
      (ward_snoc (k + 1) l c (if j + 1 = 0 then k + 1 + 1 - 1 else j + 1 - 1))
      (ward_snoc (k + 1) l c (j + 1)) = sgnMat M (τ (j + 1)) (l j) (l (j + 1)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [ward_ws, ward_snoc, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel]
    have h1 : j + 1 < k + 1 := by omega
    have h2 : j < k + 1 := by omega
    simp only [h1, h2, ↓reduceIte]
  rw [Finset.prod_congr rfl hmid]
  simp only [ward_ws, ward_snoc, ↓reduceIte, Nat.add_sub_cancel, lt_self_iff_false,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.lt_add_one, Nat.zero_lt_succ]
  ring

/-- The joined loop at `t = 0`: the `M`-loop of `(l; b, τ)`. -/
private lemma ward_Y_zero_term {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (k : ℕ) (l : ℕ → Fin L) (τ : ℕ → Bool) (b : Bool) :
    ward_F β M m 0 (k + 1) l (ward_ms τ b) =
      (∏ j ∈ range k, sgnMat M (τ (j + 1)) (l j) (l (j + 1))) * sgnMat M b (l k) (l 0) := by
  rw [ward_F_zero hD (by omega), Finset.prod_range_succ']
  have hmid : ∀ j ∈ range k, sgnMat M (ward_ms τ b (j + 1))
      (l (if j + 1 = 0 then k + 1 - 1 else j + 1 - 1)) (l (j + 1)) =
        sgnMat M (τ (j + 1)) (l j) (l (j + 1)) := by
    intro j _
    simp [ward_ms]
  rw [Finset.prod_congr rfl hmid]
  simp [ward_ms]

/-- The Ward identity at `t = 0`, `k ≥ 1`. -/
private lemma ward_zero {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    (k : ℕ) (l : ℕ → Fin L) (τ : ℕ → Bool) (s : Bool) :
    ward_X β M m 0 (k + 1) l τ s = ward_Y β M m 0 (k + 1) l τ := by
  unfold ward_X ward_Y
  simp only [ward_X_zero_term hD, ward_Y_zero_term hD]
  rw [← Finset.mul_sum]
  have h := congrFun (congrFun (ward_merge hD s) (l k)) (l 0)
  rw [Matrix.mul_apply] at h
  rw [h]
  simp [sgnMat, Matrix.smul_apply, Matrix.sub_apply]
  ring

end Initial

/-! ## The cut sums of the two sides

Every cut of the summed word keeps the summed label in its left loop, which is again a summed word.
The nonadjacent cuts match the cuts of the joined words by the induction hypothesis, the cuts at
the summed label match the cuts at position `0` of the joined words by cyclic invariance, the cut
`(0, k)` gives the row `β⁻¹(1-t)⁻¹` times the left side, and the adjacent cuts are linear in the
defect of the same length. -/

section Cuts

variable {L : ℕ}

/-- The summand of the cut sum of the summed word `(l, c; s, τ, !s)`, summed over `c`. -/
private def ward_T (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (x : ℝ) (k : ℕ)
    (l : ℕ → Fin L) (τ : ℕ → Bool) (s : Bool) (i j : ℕ) (c' : Fin L) : ℂ :=
  ∑ c : Fin L, ward_F β M m x (k + 1 + i - j + 1) (ward_cL (ward_snoc k l c) i j c')
      (ward_cLS (ward_ws k τ s) i j) *
    ward_F β M m x (j - i + 1) (ward_cR (ward_snoc k l c) i j c') (ward_cRS (ward_ws k τ s) i j)

/-- The summand of the cut sum of the joined word `(l; b, τ)`. -/
private def ward_U (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (x : ℝ) (k : ℕ)
    (l : ℕ → Fin L) (τ : ℕ → Bool) (b : Bool) (i j : ℕ) (c' : Fin L) : ℂ :=
  ward_F β M m x (k + i - j + 1) (ward_cL l i j c') (ward_cLS (ward_ms τ b) i j) *
    ward_F β M m x (j - i + 1) (ward_cR l i j c') (ward_cRS (ward_ms τ b) i j)

/-- The difference of the two cut summands at a pair `(i, j)`, `j < k`. -/
private def ward_G (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (x : ℝ) (k : ℕ)
    (l : ℕ → Fin L) (τ : ℕ → Bool) (s : Bool) (i j : ℕ) (c' : Fin L) : ℂ :=
  ward_T β M m x k l τ s i j c' -
    ward_kap β m x * (ward_U β M m x k l τ true i j c' - ward_U β M m x k l τ false i j c')

/-- A cut `(i, j)`, `j < k`, of the summed word: the left loop is a summed word and the right loop
is the right cut of the joined word with first sign `s`. -/
private lemma ward_P1 (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (x : ℝ) {k i j : ℕ}
    (hij : i < j) (hjk : j < k) (l : ℕ → Fin L) (τ : ℕ → Bool) (s : Bool) (c' : Fin L) :
    ward_T β M m x k l τ s i j c' =
      ward_X β M m x (k + i - j + 1) (ward_cL l i j c') (ward_cLS τ i j) s *
        ward_F β M m x (j - i + 1) (ward_cR l i j c') (ward_cRS (ward_ms τ s) i j) := by
  unfold ward_T ward_X
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  · refine ward_F_congr (by omega) (fun p hp => ?_) (fun p hp => ?_)
    · simp only [ward_cL, ward_snoc]
      ward_cases
    · simp only [ward_cLS, ward_ws]
      ward_cases
  · refine ward_F_congr rfl (fun p hp => ?_) (fun p hp => ?_)
    · simp only [ward_cR, ward_snoc]
      ward_cases
    · simp only [ward_cRS, ward_ws, ward_ms]
      ward_cases

/-- A cut `(i, k)` of the summed word: the left loop is the summed word of length `i + 1`. -/
private lemma ward_P2 (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (x : ℝ) {k i : ℕ}
    (hik : i < k) (l : ℕ → Fin L) (τ : ℕ → Bool) (s : Bool) (c' : Fin L) :
    ward_T β M m x k l τ s i k c' =
      ward_X β M m x (i + 1) (ward_cL l i k c') τ s *
        ward_F β M m x (k - i + 1) (ward_cR l i k c') (ward_cRS (ward_ws k τ s) i k) := by
  unfold ward_T ward_X
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  · refine ward_F_congr (by omega) (fun p hp => ?_) (fun p hp => ?_)
    · simp only [ward_cL, ward_snoc]
      ward_cases
    · simp only [ward_cLS, ward_ws]
      ward_cases
  · refine ward_F_congr rfl (fun p hp => ?_) (fun _ _ => rfl)
    simp only [ward_cR, ward_snoc]
    ward_cases

/-- The joined signs commute with the left cut. -/
private lemma ward_ms_cLS {i j : ℕ} (hij : i < j) (τ : ℕ → Bool) (b : Bool) (p : ℕ) :
    ward_ms (ward_cLS τ i j) b p = ward_cLS (ward_ms τ b) i j p := by
  simp only [ward_ms, ward_cLS]
  ward_cases

/-- A cut `(i, j)`, `1 ≤ i < j < k`: the difference of the cut summands is the defect of the left
loop times the right loop. -/
private lemma ward_W1 (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (x : ℝ) {k i j : ℕ}
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) (l : ℕ → Fin L) (τ : ℕ → Bool) (s : Bool)
    (c' : Fin L) :
    ward_G β M m x k l τ s i j c' =
      (ward_X β M m x (k + i - j + 1) (ward_cL l i j c') (ward_cLS τ i j) s -
          ward_Y β M m x (k + i - j + 1) (ward_cL l i j c') (ward_cLS τ i j)) *
        ward_F β M m x (j - i + 1) (ward_cR l i j c') (ward_cRS (ward_ms τ s) i j) := by
  unfold ward_G ward_U ward_Y
  rw [ward_P1 β M m x hij hjk]
  have e1 : ∀ b, ward_F β M m x (k + i - j + 1) (ward_cL l i j c') (ward_cLS (ward_ms τ b) i j) =
      ward_F β M m x (k + i - j + 1) (ward_cL l i j c') (ward_ms (ward_cLS τ i j) b) :=
    fun b => ward_F_congr rfl (fun _ _ => rfl) (fun p _ => (ward_ms_cLS hij τ b p).symm)
  have e2 : ∀ b, ward_F β M m x (j - i + 1) (ward_cR l i j c') (ward_cRS (ward_ms τ b) i j) =
      ward_F β M m x (j - i + 1) (ward_cR l i j c') (ward_cRS (ward_ms τ s) i j) := by
    intro b
    refine ward_F_congr rfl (fun _ _ => rfl) (fun p _ => ?_)
    simp only [ward_cRS, ward_ms]
    ward_cases
  rw [e1 true, e1 false, e2 true, e2 false]
  ring

/-- The cuts `(0, j)` and `(j, k)`, `1 ≤ j < k`, together: the joined terms cancel by cyclic
invariance of the loop of length `k - j + 1`, and the defects of the two left loops remain. -/
private lemma ward_W2 (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (x : ℝ) {k j : ℕ}
    (hj : 1 ≤ j) (hjk : j < k) (l : ℕ → Fin L) (τ : ℕ → Bool) (s : Bool) (c' : Fin L)
    (hrot : ward_F β M m x (k - j + 1) (ward_rot (k - j + 1) (ward_cL l 0 j c'))
        (ward_rot (k - j + 1) (ward_cLS (ward_ms τ (!s)) 0 j)) =
      ward_F β M m x (k - j + 1) (ward_cL l 0 j c') (ward_cLS (ward_ms τ (!s)) 0 j)) :
    ward_G β M m x k l τ s 0 j c' + ward_T β M m x k l τ s j k c' =
      (ward_X β M m x (k + 0 - j + 1) (ward_cL l 0 j c') (ward_cLS τ 0 j) s -
          ward_Y β M m x (k + 0 - j + 1) (ward_cL l 0 j c') (ward_cLS τ 0 j)) *
        ward_F β M m x (j - 0 + 1) (ward_cR l 0 j c') (ward_cRS (ward_ms τ s) 0 j) +
      (ward_X β M m x (j + 1) (ward_cL l j k c') τ s -
          ward_Y β M m x (j + 1) (ward_cL l j k c') τ) *
        ward_F β M m x (k - j + 1) (ward_cR l j k c') (ward_cRS (ward_ws k τ s) j k) := by
  unfold ward_G ward_U ward_Y
  rw [ward_P1 β M m x (by omega : 0 < j) hjk, ward_P2 β M m x hjk]
  have eA : ∀ b, ward_F β M m x (k + 0 - j + 1) (ward_cL l 0 j c') (ward_ms (ward_cLS τ 0 j) b) =
      ward_F β M m x (k + 0 - j + 1) (ward_cL l 0 j c') (ward_cLS (ward_ms τ b) 0 j) :=
    fun b => ward_F_congr rfl (fun _ _ => rfl) (fun p _ => ward_ms_cLS (by omega) τ b p)
  have eB : ∀ b, ward_F β M m x (j + 1) (ward_cL l j k c') (ward_ms τ b) =
      ward_F β M m x (j - 0 + 1) (ward_cR l 0 j c') (ward_cRS (ward_ms τ b) 0 j) := by
    intro b
    refine ward_F_congr (by omega) (fun p hp => ?_) (fun p hp => ?_)
    · simp only [ward_cL, ward_cR]
      ward_cases
    · simp only [ward_cRS, Nat.zero_add]
  have eC : ward_F β M m x (k - j + 1) (ward_cR l j k c') (ward_cRS (ward_ws k τ s) j k) =
      ward_F β M m x (k + 0 - j + 1) (ward_cL l 0 j c') (ward_cLS (ward_ms τ (!s)) 0 j) := by
    refine (ward_F_congr rfl (fun p hp => ?_) (fun p hp => ?_)).trans
      (hrot.trans (ward_F_congr (by omega) (fun _ _ => rfl) (fun _ _ => rfl)))
    · simp only [ward_cR, ward_cL, ward_rot]
      ward_cases
    · simp only [ward_cRS, ward_cLS, ward_ws, ward_ms, ward_rot]
      ward_cases
  rw [eA true, eA false, eB true, eB false, eC]
  cases s <;> simp only [Bool.not_true, Bool.not_false] <;> ring

/-- The cut `(0, k)`: the row `r` of the mixed pair times the left side. -/
private lemma ward_W3 (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (x : ℝ) {k : ℕ}
    (hk : 1 ≤ k) (l : ℕ → Fin L) (τ : ℕ → Bool) (s : Bool) {r : ℂ}
    (hrow : ∀ (l' : ℕ → Fin L) (τ' : ℕ → Bool), ward_X β M m x 1 l' τ' s = r) :
    ∑ c' : Fin L, ward_T β M m x k l τ s 0 k c' = r * ward_X β M m x k l τ s := by
  unfold ward_X
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [ward_P2 β M m x (by omega : 0 < k), hrow]
  congr 1
  refine ward_F_congr (by omega) (fun p hp => ?_) (fun p hp => ?_)
  · simp only [ward_cR, ward_snoc]
    ward_cases
  · simp only [ward_cRS, Nat.zero_add]

/-- Moving the label sum inside the cut sum. -/
private lemma ward_sum_swap (N : ℕ) (f : Fin L → ℕ → ℕ → Fin L → ℂ) :
    ∑ c, ∑ j ∈ range N, ∑ i ∈ range j, ∑ c', f c i j c' =
      ∑ j ∈ range N, ∑ i ∈ range j, ∑ c', ∑ c, f c i j c' := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/-- The derivative of the left side minus that of the right side, split by cuts. -/
private lemma ward_decomp (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (x : ℝ) (k : ℕ)
    (l : ℕ → Fin L) (τ : ℕ → Bool) (s : Bool) :
    ∑ c : Fin L, ward_cutN (ward_F β M m x) (k + 1 + 1) (ward_snoc (k + 1) l c)
        (ward_ws (k + 1) τ s) -
      ward_kap β m x * (ward_cutN (ward_F β M m x) (k + 1) l (ward_ms τ true) -
        ward_cutN (ward_F β M m x) (k + 1) l (ward_ms τ false)) =
    ∑ j ∈ range k, ∑ i ∈ range j, ∑ c' : Fin L, ward_G β M m x (k + 1) l τ s (i + 1) (j + 1) c' +
      ∑ j ∈ range k, ∑ c' : Fin L,
        (ward_G β M m x (k + 1) l τ s 0 (j + 1) c' +
          ward_T β M m x (k + 1) l τ s (j + 1) (k + 1) c') +
      ∑ c' : Fin L, ward_T β M m x (k + 1) l τ s 0 (k + 1) c' := by
  have hT : ∑ c : Fin L, ward_cutN (ward_F β M m x) (k + 1 + 1) (ward_snoc (k + 1) l c)
      (ward_ws (k + 1) τ s) = ∑ j ∈ range (k + 1 + 1), ∑ i ∈ range j, ∑ c' : Fin L,
        ward_T β M m x (k + 1) l τ s i j c' := by
    unfold ward_cutN ward_T
    exact ward_sum_swap _ _
  have hU : ∀ b, ward_cutN (ward_F β M m x) (k + 1) l (ward_ms τ b) =
      ∑ j ∈ range (k + 1), ∑ i ∈ range j, ∑ c' : Fin L, ward_U β M m x (k + 1) l τ b i j c' :=
    fun b => rfl
  rw [hT, hU, hU, Finset.sum_range_succ]
  unfold ward_G
  simp only [Finset.sum_range_succ', Finset.range_zero, Finset.sum_empty, add_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, mul_sub, mul_add]
  ring

end Cuts

/-! ## The Ward identity for `F_k`

By induction on `k`: the defect `Σ_c F_{k+1} - (2iβ(1-t) Im m)⁻¹[F_k(+) - F_k(-)]` vanishes at
`t = 0` and solves a linear equation whose coefficients are the pair loops and `(1-t)⁻¹`, so a
Gronwall step gives the identity for `0 ≤ t < 1`. -/

section Holds

variable {L : ℕ}

/-- A defect of length `k' ≤ k` times a factor: zero for `k' < k` by the induction hypothesis,
at most `εB` for `k' = k`. -/
private lemma ward_def_mul_le {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} {x : ℝ}
    {k k' : ℕ} {τ τ' : ℕ → Bool} {s : Bool} {l' : ℕ → Fin L} {Z : ℂ} {B ε : ℝ}
    (hB0 : 0 ≤ B) (hε0 : 0 ≤ ε) (hk' : 1 ≤ k') (hk'k : k' ≤ k)
    (hih : ∀ k'', 1 ≤ k'' → k'' < k → ∀ (l : ℕ → Fin L) (τ'' : ℕ → Bool) (s' : Bool),
      ward_X β M m x k'' l τ'' s' = ward_Y β M m x k'' l τ'')
    (hε : ∀ (l : ℕ → Fin L) (τ'' : ℕ → Bool), (∀ p, 1 ≤ p → p < k → τ'' p = τ p) →
      ‖ward_X β M m x k l τ'' s - ward_Y β M m x k l τ''‖ ≤ ε)
    (hτ' : k' = k → ∀ p, 1 ≤ p → p < k → τ' p = τ p) (hZ : k' = k → ‖Z‖ ≤ B) :
    ‖(ward_X β M m x k' l' τ' s - ward_Y β M m x k' l' τ') * Z‖ ≤ ε * B := by
  rcases hk'k.lt_or_eq with hlt | rfl
  · rw [hih k' hk' hlt, sub_self, zero_mul, norm_zero]
    positivity
  · rw [norm_mul]
    exact mul_le_mul (hε l' τ' (hτ' rfl)) (hZ rfl) (norm_nonneg _) hε0

/-- The derivative of the defect, minus `(1-t)⁻¹` times the defect, is bounded by the defects of
the same length. -/
private lemma ward_cut_le {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {k : ℕ} (hk : 1 ≤ k) {τ : ℕ → Bool} {s : Bool}
    {B ε : ℝ} (hB0 : 0 ≤ B) (hε0 : 0 ≤ ε)
    (hB : ∀ (l : ℕ → Fin L) (σ : ℕ → Bool), ‖ward_F β M m x 2 l σ‖ ≤ B)
    (hih : ∀ k', 1 ≤ k' → k' < k + 1 → ∀ (l : ℕ → Fin L) (τ' : ℕ → Bool) (s' : Bool),
      ward_X β M m x k' l τ' s' = ward_Y β M m x k' l τ')
    (hε : ∀ (l : ℕ → Fin L) (τ' : ℕ → Bool), (∀ p, 1 ≤ p → p < k + 1 → τ' p = τ p) →
      ‖ward_X β M m x (k + 1) l τ' s - ward_Y β M m x (k + 1) l τ'‖ ≤ ε)
    (hrot : ∀ n', 2 ≤ n' → n' ≤ k + 1 → ∀ (l : ℕ → Fin L) (σ : ℕ → Bool),
      ward_F β M m x n' (ward_rot n' l) (ward_rot n' σ) = ward_F β M m x n' l σ)
    (l : ℕ → Fin L) :
    ‖∑ c : Fin L, ward_cutN (ward_F β M m x) (k + 1 + 1) (ward_snoc (k + 1) l c)
          (ward_ws (k + 1) τ s) -
        ward_kap β m x * (ward_cutN (ward_F β M m x) (k + 1) l (ward_ms τ true) -
          ward_cutN (ward_F β M m x) (k + 1) l (ward_ms τ false)) -
        (β : ℂ)⁻¹ * (((1 - x)⁻¹ : ℝ) : ℂ) * ward_X β M m x (k + 1) l τ s‖ ≤
      (k * k * L + k * L * 2) * (ε * B) := by
  have hrow : ∀ (l' : ℕ → Fin L) (τ' : ℕ → Bool),
      ward_X β M m x 1 l' τ' s = (β : ℂ)⁻¹ * (((1 - x)⁻¹ : ℝ) : ℂ) :=
    fun l' τ' => ward_X_one hD hx0 hx1 l' τ' s
  rw [ward_decomp, ward_W3 β M m x (by omega) l τ s hrow, add_sub_cancel_right]
  refine (norm_add_le _ _).trans ?_
  have b1 := ward_norm_sum3_le (N := k)
    (fun i j c' => ward_G β M m x (k + 1) l τ s (i + 1) (j + 1) c') (mul_nonneg hε0 hB0)
    (fun j hj i hij c' => by
      rw [ward_W1 β M m x (by omega) (by omega) (by omega)]
      refine ward_def_mul_le hB0 hε0 (by omega) (by omega) hih hε (fun h p hp1 hp2 => ?_)
        (fun h => ?_)
      · simp only [ward_cLS]
        split_ifs <;> first | rfl | (congr 1; omega)
      · have e : j + 1 - (i + 1) + 1 = 2 := by omega
        rw [e]
        exact hB _ _)
  have b2 := ward_norm_sum2_le (N := k)
    (fun j c' => ward_G β M m x (k + 1) l τ s 0 (j + 1) c' +
      ward_T β M m x (k + 1) l τ s (j + 1) (k + 1) c') (b := ε * B + ε * B)
    (fun j hj c' => by
      rw [ward_W2 β M m x (by omega) (by omega) l τ s c' (hrot _ (by omega) (by omega) _ _)]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine ward_def_mul_le hB0 hε0 (by omega) (by omega) hih hε (fun h p hp1 hp2 => ?_)
          (fun h => ?_)
        · simp only [ward_cLS]
          split_ifs <;> first | rfl | (congr 1; omega)
        · have e : j + 1 - 0 + 1 = 2 := by omega
          rw [e]
          exact hB _ _
      · refine ward_def_mul_le hB0 hε0 (by omega) (by omega) hih hε (fun _ _ _ _ => rfl)
          (fun h => ?_)
        have e : k + 1 - (j + 1) + 1 = 2 := by omega
        rw [e]
        exact hB _ _)
  have : (k : ℝ) * k * L * (ε * B) + k * L * (ε * B + ε * B) =
      (k * k * L + k * L * 2) * (ε * B) := by ring
  linarith

/-- `t ↦ (2iβ(1-t) Im m)⁻¹` has derivative `(2iβ(1-t) Im m)⁻¹ (1-t)⁻¹` for `t < 1`. -/
private lemma ward_kap_hasDerivAt (β : ℝ) (m : ℂ) {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y => ward_kap β m y) (ward_kap β m x * (((1 - x)⁻¹ : ℝ) : ℂ)) x := by
  have e : (fun y => ward_kap β m y) =
      fun y => (2 * I * ((β * m.im : ℝ) : ℂ))⁻¹ * (((1 - y)⁻¹ : ℝ) : ℂ) := by
    funext y
    unfold ward_kap
    push_cast
    rw [show (2 * I * ((1 - (y : ℂ)) * β * m.im)) = (2 * I * (β * m.im)) * (1 - y) by ring,
      mul_inv]
  have h1 : HasDerivAt (fun y : ℝ => (1 - y)⁻¹) (-(-1) / (1 - x) ^ 2) x :=
    ((hasDerivAt_id x).const_sub 1).fun_inv (by simp; linarith)
  rw [e]
  refine (h1.ofReal_comp.const_mul ((2 * I * ((β * m.im : ℝ) : ℂ))⁻¹)).congr_deriv ?_
  have hx' : (1 - x : ℝ) ≠ 0 := by linarith
  unfold ward_kap
  push_cast
  have hx'' : (1 - (x : ℂ)) ≠ 0 := by exact_mod_cast hx'
  rw [show (2 * I * ((1 - (x : ℂ)) * β * m.im)) = (2 * I * (β * m.im)) * (1 - x) by ring,
    mul_inv]
  field_simp

/-- The Ward identity (5.11) [gc:eq:ward] for `F_k` on words on `ℕ`, `0 ≤ t < 1`. -/
private lemma ward_holds {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m) :
    ∀ k, 1 ≤ k → ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (l : ℕ → Fin L) (τ : ℕ → Bool) (s : Bool),
      ward_X β M m t k l τ s = ward_Y β M m t k l τ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk t ht l τ s
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · obtain rfl : k = 1 := by omega
    rw [ward_X_one hD ht.1 ht.2, ward_Y_one hD ht.2]
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk0 : 0 < k + 1 := by omega
    have hIoo : ∀ x ∈ Set.Icc (0 : ℝ) t, x ∈ Set.Ioo (-1 : ℝ) 1 :=
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, ht.2]⟩
    have hIco : ∀ x ∈ Set.Icc (0 : ℝ) t, x ∈ Set.Ico (0 : ℝ) 1 :=
      fun x hx => ⟨hx.1, by linarith [hx.2, ht.2]⟩
    have hβ : (β : ℂ) ≠ 0 := by exact_mod_cast hD.pos.ne'
    obtain ⟨B, hB0, hB⟩ := ward_F_bound hD ht.2 2
    have hext : ∀ (l' : ℕ → Fin L), ∀ q < k + 1,
        ward_ext hk0 (fun p : Fin (k + 1) => l' p.val) q = l' q := fun l' q hq => by
      rw [ward_ext_apply hk0 _ hq]
    set f : ℝ → (Fin (k + 1) → Fin L) → ℂ := fun x a =>
      ward_X β M m x (k + 1) (ward_ext hk0 a) τ s - ward_Y β M m x (k + 1) (ward_ext hk0 a) τ
      with hf
    set f' : ℝ → (Fin (k + 1) → Fin L) → ℂ := fun x a =>
      (β : ℂ) * ∑ c : Fin L, ward_cutN (ward_F β M m x) (k + 1 + 1)
          (ward_snoc (k + 1) (ward_ext hk0 a) c) (ward_ws (k + 1) τ s) -
        (ward_kap β m x * (((1 - x)⁻¹ : ℝ) : ℂ) *
            (ward_F β M m x (k + 1) (ward_ext hk0 a) (ward_ms τ true) -
              ward_F β M m x (k + 1) (ward_ext hk0 a) (ward_ms τ false)) +
          ward_kap β m x *
            ((β : ℂ) * ward_cutN (ward_F β M m x) (k + 1) (ward_ext hk0 a) (ward_ms τ true) -
              (β : ℂ) * ward_cutN (ward_F β M m x) (k + 1) (ward_ext hk0 a) (ward_ms τ false)))
      with hf'
    have hfw : ∀ x (l' : ℕ → Fin L), f x (fun p => l' p.val) =
        ward_X β M m x (k + 1) l' τ s - ward_Y β M m x (k + 1) l' τ := by
      intro x l'
      simp only [hf]
      rw [ward_X_congr s (hext l') (fun _ _ _ => rfl), ward_Y_congr (hext l') (fun _ _ _ => rfl)]
    have ht1 : 0 < 1 - t := by linarith [ht.2]
    have hz := ward_gronwall f f' ht.1
      (C := |β| * ((k * k * L + k * L * 2) * B) + (1 - t)⁻¹) (by positivity)
      (fun a => by
        refine ContinuousOn.sub ?_ ?_
        · exact continuousOn_finsetSum _ fun c _ => fun x hx =>
            (ward_F_continuousAt hD (hIoo x hx) _ _ _).continuousWithinAt
        · refine ContinuousOn.mul ?_ (ContinuousOn.sub ?_ ?_)
          · exact fun x hx =>
              (ward_kap_hasDerivAt β m (hIoo x hx).2).continuousAt.continuousWithinAt
          · exact fun x hx => (ward_F_continuousAt hD (hIoo x hx) _ _ _).continuousWithinAt
          · exact fun x hx => (ward_F_continuousAt hD (hIoo x hx) _ _ _).continuousWithinAt)
      (fun x hx a => by
        have hx' : x ∈ Set.Icc (0 : ℝ) t := ⟨hx.1, hx.2.le⟩
        have hX := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin L))) (x := x)
          (A := fun c y => ward_F β M m y (k + 1 + 1) (ward_snoc (k + 1) (ward_ext hk0 a) c)
            (ward_ws (k + 1) τ s))
          (fun c _ => ward_F_hasDerivAt hD (hIoo x hx') (by omega) _ _)
        have hY := (ward_kap_hasDerivAt β m (hIoo x hx').2).mul
          ((ward_F_hasDerivAt hD (hIoo x hx') (by omega : 2 ≤ k + 1) (ward_ext hk0 a)
            (ward_ms τ true)).sub
            (ward_F_hasDerivAt hD (hIoo x hx') (by omega : 2 ≤ k + 1) (ward_ext hk0 a)
              (ward_ms τ false)))
        refine (hX.sub hY).congr_deriv ?_
        simp only [hf', Pi.sub_apply]
        rw [Finset.mul_sum])
      (fun x hx a => by
        have hx' : x ∈ Set.Icc (0 : ℝ) t := ⟨hx.1, hx.2.le⟩
        have hcut := ward_cut_le hD hx.1 (hIoo x hx').2 (k := k) (by omega) (τ := τ) (s := s)
          hB0 (norm_nonneg (f x)) (hB x hx')
          (fun k' hk' hlt l' τ' s' => ih k' hlt hk' x (hIco x hx') l' τ' s')
          (fun l' τ' hτ' => by
            rw [ward_X_congr s (fun _ _ => rfl) hτ', ward_Y_congr (fun _ _ => rfl) hτ', ← hfw]
            exact norm_le_pi_norm (f x) _)
          (fun n' h2' hle l' σ' => ward_rot_holds hD n' (by omega) x (hIco x hx') l' σ')
          (ward_ext hk0 a)
        set u : ℂ := (((1 - x)⁻¹ : ℝ) : ℂ) with hu
        have hinv : (β : ℂ) * (β : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hβ
        have key : f' x a = (β : ℂ) * (∑ c : Fin L, ward_cutN (ward_F β M m x) (k + 1 + 1)
              (ward_snoc (k + 1) (ward_ext hk0 a) c) (ward_ws (k + 1) τ s) -
            ward_kap β m x * (ward_cutN (ward_F β M m x) (k + 1) (ward_ext hk0 a) (ward_ms τ true) -
              ward_cutN (ward_F β M m x) (k + 1) (ward_ext hk0 a) (ward_ms τ false)) -
            (β : ℂ)⁻¹ * u * ward_X β M m x (k + 1) (ward_ext hk0 a) τ s) + u * f x a := by
          simp only [hf, hf', ward_Y]
          linear_combination (u * ward_X β M m x (k + 1) (ward_ext hk0 a) τ s) * hinv
        rw [key]
        have hu1 : ‖u‖ ≤ (1 - t)⁻¹ := by
          rw [hu, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith [hx.2,
            ht.2]))]
          exact inv_anti₀ ht1 (by linarith [hx.2])
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hfa := norm_le_pi_norm (f x) a
        have e1 := mul_le_mul_of_nonneg_left hcut (abs_nonneg β)
        have e2 := mul_le_mul hu1 hfa (norm_nonneg _) (by positivity)
        have e3 : |β| * (((k : ℝ) * k * L + k * L * 2) * (‖f x‖ * B)) =
            |β| * ((k * k * L + k * L * 2) * B) * ‖f x‖ := by ring
        nlinarith [norm_nonneg (f x)])
      (fun a => by
        simp only [hf]
        rw [ward_zero hD k, sub_self])
    have h := hz (fun p => l p.val)
    rw [hfw] at h
    exact sub_eq_zero.mp h

end Holds

/-! ## The pair row -/

section PairRow

open scoped Matrix.Norms.Operator

variable {L : ℕ}

end PairRow

/-- The primitive mixed Ward identity, Lemma 5.1 [fo:lem:mixed-ward] for `𝒳 = 𝒦` in the
normalization `F_k`: the label summed lies between the signs `!s` (last position) and `s`
(first position), and the numerator is `F(+) - F(-)` for both orders. -/
theorem primF_ward {L : ℕ} {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (k : ℕ) (hk : 1 ≤ k)
    (a : Fin k → Fin L) (τ : Fin k → Bool) (s : Bool) :
    ∑ c : Fin L, primF β M m t (Fin.snoc a c : Fin (k + 1) → Fin L)
        (Fin.snoc (Function.update τ ⟨0, hk⟩ s) (!s) : Fin (k + 1) → Bool) =
      ((2 * I * (((1 - t) * β * m.im : ℝ) : ℂ)))⁻¹ *
        (primF β M m t a (Function.update τ ⟨0, hk⟩ true) -
          primF β M m t a (Function.update τ ⟨0, hk⟩ false)) := by
  have hk0 : 0 < k := hk
  have h := ward_holds hD k hk t ⟨ht0, ht1⟩ (ward_ext hk0 a) (ward_ext hk0 τ) s
  have hL : ∀ c : Fin L, primF β M m t (Fin.snoc a c : Fin (k + 1) → Fin L)
      (Fin.snoc (Function.update τ ⟨0, hk⟩ s) (!s) : Fin (k + 1) → Bool) =
        ward_F β M m t (k + 1) (ward_snoc k (ward_ext hk0 a) c)
          (ward_ws k (ward_ext hk0 τ) s) := by
    intro c
    unfold ward_F
    congr 1 <;> funext p
    · by_cases hp : p.val < k
      · have e : p = Fin.castSucc ⟨p.val, hp⟩ := Fin.ext rfl
        rw [e, Fin.snoc_castSucc]
        simp [ward_snoc, hp, ward_ext_apply hk0 a hp]
      · have e : p = Fin.last k := Fin.ext (by have := p.isLt; simp; omega)
        rw [e, Fin.snoc_last]
        simp [ward_snoc]
    · by_cases hp : p.val < k
      · have e : p = Fin.castSucc ⟨p.val, hp⟩ := Fin.ext rfl
        rw [e, Fin.snoc_castSucc, Function.update_apply]
        simp only [ward_ws, Fin.val_castSucc, Fin.mk.injEq, hp, ward_ext_apply hk0 τ hp]
        split_ifs <;> rfl
      · have e : p = Fin.last k := Fin.ext (by have := p.isLt; simp; omega)
        rw [e, Fin.snoc_last]
        simp [ward_ws, show k ≠ 0 by omega]
  have hR : ∀ b : Bool, primF β M m t a (Function.update τ ⟨0, hk⟩ b) =
      ward_F β M m t k (ward_ext hk0 a) (ward_ms (ward_ext hk0 τ) b) := by
    intro b
    unfold ward_F
    congr 1 <;> funext p
    · rw [ward_ext_apply hk0 a p.isLt]
    · rw [Function.update_apply]
      simp only [ward_ms, Fin.ext_iff, ward_ext_apply hk0 τ p.isLt]
  rw [Finset.sum_congr rfl fun c _ => hL c, hR, hR]
  exact h

/-- (5.11) [gc:eq:ward] for the model primitives, with `η_t = (1-t)γ_g Im m`. -/
theorem primLoop_ward (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (k : ℕ)
    (hk : 1 ≤ k) (a : Fin k → Fin L) (τ : Fin k → Bool) (s : Bool) :
    ∑ c : Fin L, primLoop g W L E m t (Fin.snoc a c : Fin (k + 1) → Fin L)
        (Fin.snoc (Function.update τ ⟨0, hk⟩ s) (!s) : Fin (k + 1) → Bool) =
      ((2 * I * (W : ℂ) * (etaChar g m t : ℂ)))⁻¹ *
        (primLoop g W L E m t a (Function.update τ ⟨0, hk⟩ true) -
          primLoop g W L E m t a (Function.update τ ⟨0, hk⟩ false)) := by
  have hD := primData_of_root g L hL E m hm
  have h := primF_ward hD t ht0 ht1 k hk a τ s
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
  simp only [primLoop, primK]
  rw [← Finset.mul_sum, h]
  have hz : (W : ℂ) ^ (1 - ((k + 1 : ℕ) : ℤ)) = (W : ℂ)⁻¹ * (W : ℂ) ^ (1 - (k : ℤ)) := by
    rw [show (1 - ((k + 1 : ℕ) : ℤ)) = -1 + (1 - (k : ℤ)) by push_cast; ring, zpow_add₀ hW0,
      zpow_neg_one]
  rw [hz, show (etaChar g m t : ℂ) = (((1 - t) * gammaG g * m.im : ℝ) : ℂ) from rfl,
    show 2 * I * (W : ℂ) * (((1 - t) * gammaG g * m.im : ℝ) : ℂ) =
      (W : ℂ) * (2 * I * (((1 - t) * gammaG g * m.im : ℝ) : ℂ)) by ring, mul_inv]
  ring

end LSBA
