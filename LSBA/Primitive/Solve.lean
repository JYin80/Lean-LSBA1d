import LSBA.Primitive.Tree
import LSBA.Kernel.Algebra

/-!
# Primitive loops: uniqueness and Duhamel

The generator form (5.14) [fo:eq:generator] with the nonadjacent source; and Duhamel's formula
(5.16) [fo:eq:duhamel] with the propagators of (5.15) [fo:eq:propagators].
-/

open MeasureTheory Real Filter Topology Complex Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ## The sign-pair matrices

For a pair of signs `(s, s')` the one-label inverse, pair kernel and propagator of Appendix B.2
[sec:bl-primitives] and (5.15) [fo:eq:propagators] are the functions `(1 - tX)⁻¹`, `X(1 - tX)⁻¹` and
`(1 - uX)(1 - tX)⁻¹` of one matrix `X`: `P` for opposite signs, `Q` for `++` and its conjugate
for `--`. -/

section Calculus

open scoped Matrix.Norms.Operator

variable {L : ℕ}

/-- The pair matrix of a sign pair: `P` for opposite signs, `Q` for `++`, its conjugate for
`--`. -/
private def solve_pairX (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (s s' : Bool) :
    Matrix (Fin L) (Fin L) ℂ :=
  if s = s' then (if s then pairQ β M else (pairQ β M).map star)
  else (pairP β M).map ((↑) : ℝ → ℂ)

/-- The pair matrix does not depend on the order of the two signs. -/
private lemma solve_pairX_swap (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (s s' : Bool) :
    solve_pairX β M s s' = solve_pairX β M s' s := by
  cases s <;> cases s' <;> rfl

/-- Under the primitive data, the rows of `|X|` sum to one. -/
private lemma solve_pairX_rowsum {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (s s' : Bool) (a : Fin L) :
    ∑ b, ‖solve_pairX β M s s' a b‖ = 1 := by
  have hQ : ∀ b, ‖pairQ β M a b‖ = pairP β M a b := by
    intro b
    simp [pairQ, pairP, norm_pow, Complex.norm_real, abs_of_pos hD.pos]
  have hP : ∀ b, ‖((pairP β M a b : ℝ) : ℂ)‖ = pairP β M a b := by
    intro b
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    simp only [pairP, Matrix.of_apply]
    exact mul_nonneg hD.pos.le (sq_nonneg _)
  rw [← hD.row_sum a]
  unfold solve_pairX
  split_ifs
  · exact Finset.sum_congr rfl fun b _ => hQ b
  · exact Finset.sum_congr rfl fun b _ => by rw [Matrix.map_apply, norm_star, hQ b]
  · exact Finset.sum_congr rfl fun b _ => by rw [Matrix.map_apply, hP b]

/-- The pair matrix is symmetric when `M` is. -/
private lemma solve_pairX_transpose {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} (hM : Mᵀ = M)
    (s s' : Bool) : (solve_pairX β M s s')ᵀ = solve_pairX β M s s' := by
  have h : ∀ a b, M b a = M a b := fun a b => congrFun (congrFun hM a) b
  unfold solve_pairX
  split_ifs <;> ext a b <;> simp [pairQ, pairP, h a b]

/-- Row sums of `|X|` at most `1` give `‖X‖_{∞→∞} ≤ 1`. -/
private lemma solve_norm_le {X : Matrix (Fin L) (Fin L) ℂ} (hX : ∀ a, ∑ b, ‖X a b‖ ≤ 1) :
    ‖X‖ ≤ 1 := by
  have h : ‖X‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun a _ => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_one]
    simpa using hX a
  exact_mod_cast h

/-- `1 - tX` is invertible for `‖X‖ ≤ 1` and `|t| < 1`. -/
private lemma solve_isUnit {X : Matrix (Fin L) (Fin L) ℂ} (hX : ‖X‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    IsUnit (1 - (t : ℂ) • X) := by
  have h : ‖(t : ℂ) • X‖ < 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖X‖ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hX (abs_nonneg t)
      _ < 1 := by rwa [mul_one]
  exact ⟨Units.oneSub _ h, Units.val_oneSub _ _⟩

/-- `1 - tX` is invertible for the pair matrices of the primitive data and `|t| < 1`. -/
private lemma solve_pairX_isUnit {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (s s' : Bool) :
    IsUnit (1 - (t : ℂ) • solve_pairX β M s s') :=
  solve_isUnit (solve_norm_le fun a => (solve_pairX_rowsum hD s s' a).le) ht

/-- The entrywise image of an inverse under a ring hom of fields. -/
private lemma solve_map_inv {R S : Type*} [Field R] [Field S] (f : R →+* S)
    (A : Matrix (Fin L) (Fin L) R) : (A⁻¹).map f = (A.map f)⁻¹ := by
  by_cases h : IsUnit A.det
  · symm
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ (map_zero f) (map_one f)]
  · have h' : ¬IsUnit (A.map f).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero,
        map_ne_zero_iff _ f.injective, ← isUnit_iff_ne_zero]
      exact h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h']
    ext a b
    simp

private lemma solve_map_star_eq (A : Matrix (Fin L) (Fin L) ℂ) :
    A.map star = A.map (starRingEnd ℂ) := rfl

/-- The one-label inverse is `(I - tX)⁻¹`. -/
private lemma solve_pairV_eq (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (s s' : Bool) :
    pairV β M t s s' = (1 - (t : ℂ) • solve_pairX β M s s')⁻¹ := by
  unfold pairV solve_pairX
  split_ifs with h1 h2
  · rfl
  · rw [solve_map_star_eq, solve_map_inv]
    congr 1
    ext a b
    simp [Matrix.one_apply]
  · rw [show ((1 - t • pairP β M)⁻¹).map ((↑) : ℝ → ℂ) =
        ((1 - t • pairP β M)⁻¹).map Complex.ofRealHom from rfl, solve_map_inv]
    congr 1
    ext a b
    simp [Matrix.one_apply]
    split_ifs <;> simp

/-- The pair kernel is `X(I - tX)⁻¹`. -/
private lemma solve_pairK_eq (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (s s' : Bool) :
    pairK β M t s s' = solve_pairX β M s s' * (1 - (t : ℂ) • solve_pairX β M s s')⁻¹ := by
  have hV := solve_pairV_eq β M t s s'
  cases s <;> cases s' <;>
    simp only [pairK, pairV, solve_pairX, Bool.false_eq_true, Bool.true_eq_false, ite_true,
      ite_false, mixedKer] at hV ⊢
  · rw [← hV, solve_map_star_eq, solve_map_star_eq, solve_map_star_eq, Matrix.map_mul]
  · rw [← hV, show ((pairP β M * (1 - t • pairP β M)⁻¹)).map ((↑) : ℝ → ℂ) =
        ((pairP β M * (1 - t • pairP β M)⁻¹)).map Complex.ofRealHom from rfl, Matrix.map_mul]
    rfl
  · rw [← hV, show ((pairP β M * (1 - t • pairP β M)⁻¹)).map ((↑) : ℝ → ℂ) =
        ((pairP β M * (1 - t • pairP β M)⁻¹)).map Complex.ofRealHom from rfl, Matrix.map_mul]
    rfl

/-- The propagator is `(I - uX)(I - tX)⁻¹`. -/
private lemma solve_pairU_eq (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (u t : ℝ) (s s' : Bool) :
    pairU β M u t s s' = (1 - (u : ℂ) • solve_pairX β M s s') *
      (1 - (t : ℂ) • solve_pairX β M s s')⁻¹ := by
  unfold pairU solve_pairX propPP propPM
  split_ifs with h1 h2
  · rfl
  · rw [solve_map_star_eq, Matrix.map_mul, solve_map_inv]
    congr 2
    · ext a b
      simp [Matrix.one_apply]
    · ext a b
      simp [Matrix.one_apply]
  · rw [show ((1 - u • pairP β M) * (1 - t • pairP β M)⁻¹).map ((↑) : ℝ → ℂ) =
        ((1 - u • pairP β M) * (1 - t • pairP β M)⁻¹).map Complex.ofRealHom from rfl,
      Matrix.map_mul, solve_map_inv]
    congr 2
    · ext a b
      simp [Matrix.one_apply]
      split_ifs <;> simp
    · ext a b
      simp [Matrix.one_apply]
      split_ifs <;> simp

section Generic

variable {X : Matrix (Fin L) (Fin L) ℂ}

private lemma solve_inv_mul {t : ℝ} (hU : IsUnit (1 - (t : ℂ) • X)) :
    (1 - (t : ℂ) • X)⁻¹ * (1 - (t : ℂ) • X) = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)

private lemma solve_mul_inv {t : ℝ} (hU : IsUnit (1 - (t : ℂ) • X)) :
    (1 - (t : ℂ) • X) * (1 - (t : ℂ) • X)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)

/-- `X` commutes with `(1 - tX)⁻¹`. -/
private lemma solve_comm {t : ℝ} (hU : IsUnit (1 - (t : ℂ) • X)) :
    X * (1 - (t : ℂ) • X)⁻¹ = (1 - (t : ℂ) • X)⁻¹ * X := by
  have hc : (1 - (t : ℂ) • X) * X = X * (1 - (t : ℂ) • X) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
  set V := (1 - (t : ℂ) • X)⁻¹
  calc X * V = (V * (1 - (t : ℂ) • X)) * X * V := by rw [solve_inv_mul hU, Matrix.one_mul]
    _ = V * ((1 - (t : ℂ) • X) * X) * V := by simp only [Matrix.mul_assoc]
    _ = V * (X * (1 - (t : ℂ) • X)) * V := by rw [hc]
    _ = V * X * ((1 - (t : ℂ) • X) * V) := by simp only [Matrix.mul_assoc]
    _ = V * X := by rw [solve_mul_inv hU, Matrix.mul_one]

/-- `U_{u,t} · X(1 - uX)⁻¹ = X(1 - tX)⁻¹`. -/
private lemma solve_prop_mul_ker {u t : ℝ} (hu : IsUnit (1 - (u : ℂ) • X))
    (ht : IsUnit (1 - (t : ℂ) • X)) :
    ((1 - (u : ℂ) • X) * (1 - (t : ℂ) • X)⁻¹) * (X * (1 - (u : ℂ) • X)⁻¹) =
      X * (1 - (t : ℂ) • X)⁻¹ := by
  set A := (1 - (u : ℂ) • X) with hA
  set V := (1 - (t : ℂ) • X)⁻¹ with hV
  have hAX : A * X = X * A := by
    rw [hA, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
  have hVX : V * X = X * V := (solve_comm ht).symm
  have hAV : A * V = V * A := by
    rw [hA, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul, hVX]
  calc A * V * (X * A⁻¹) = V * A * (X * A⁻¹) := by rw [hAV]
    _ = V * (A * X) * A⁻¹ := by simp only [Matrix.mul_assoc]
    _ = V * (X * A) * A⁻¹ := by rw [hAX]
    _ = V * X * (A * A⁻¹) := by simp only [Matrix.mul_assoc]
    _ = X * V := by rw [solve_mul_inv hu, Matrix.mul_one, hVX]

end Generic

/-- The transpose of the pair kernel swaps the two signs. -/
private lemma solve_pairK_transpose {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (s s' : Bool) :
    (pairK β M t s s')ᵀ = pairK β M t s' s := by
  rw [solve_pairK_eq, solve_pairK_eq, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
    solve_pairX_transpose hD.symm, solve_pairX_swap β M s' s,
    solve_comm (solve_pairX_isUnit hD ht s s')]

/-- `U_{t,t} = I`. -/
private lemma solve_pairU_self {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (s s' : Bool) : pairU β M t t s s' = 1 := by
  rw [solve_pairU_eq, solve_mul_inv (solve_pairX_isUnit hD ht s s')]

/-- `∂_u U_{u,t}` is `-X(1 - tX)⁻¹`, entrywise. -/
private lemma solve_pairU_hasDerivAt (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (u t : ℝ)
    (s s' : Bool) (a b : Fin L) :
    HasDerivAt (fun r => pairU β M r t s s' a b) (-(pairK β M t s s' a b)) u := by
  set X := solve_pairX β M s s'
  set V := (1 - (t : ℂ) • X)⁻¹
  have e : (fun r : ℝ => pairU β M r t s s' a b) =
      fun r : ℝ => V a b - (r : ℂ) * (X * V) a b := by
    funext r
    rw [solve_pairU_eq, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul]
  have hK : pairK β M t s s' = X * V := solve_pairK_eq β M t s s'
  rw [e, hK]
  have h : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
  simpa using ((h.mul_const ((X * V) a b)).const_sub (V a b))

end Calculus

/-! ## The cut maps at adjacent pairs

The pairs `i < j` of positions of the `k`-gon are the `k` adjacent pairs `(s, s + 1)`, `(0, k - 1)`
and the diagonals of `polyDiags`; the cut maps of (5.6) [fo:eq:cuts] at an adjacent pair are a
one-label update and a pair. -/

section Cuts

variable {L k : ℕ}

/-- The value of the cyclic successor. -/
private lemma solve_finRotate_val {n : ℕ} (v : Fin n) :
    (finRotate n v).val = if v.val + 1 = n then 0 else v.val + 1 := by
  rcases n with _ | n
  · exact v.elim0
  · rw [coe_finRotate]
    by_cases h : v = Fin.last n
    · subst h; simp
    · have h' : v.val ≠ n := fun e => h (Fin.ext e)
      simp [h, h']

/-- The vertex map of the polygon of `Cut_{L,i,j}`. -/
private def solve_vL (i j : Fin k) (p : Fin (k + i - j + 1)) : Fin k :=
  ⟨if p.val ≤ i.val then p.val else p.val + j.val - i.val - 1, by
    have := p.isLt; have := i.isLt; have := j.isLt; split_ifs <;> omega⟩

/-- The vertex map of the polygon of `Cut_{R,i,j}`. -/
private def solve_vR (i j : Fin k) (q : Fin (j - i + 1)) : Fin k :=
  ⟨i.val + q.val, by have := q.isLt; have := i.isLt; have := j.isLt; omega⟩

private lemma solve_vL_val (i j : Fin k) (p : Fin (k + i - j + 1)) :
    (solve_vL i j p).val = if p.val ≤ i.val then p.val else p.val + j.val - i.val - 1 := rfl

private lemma solve_vR_val (i j : Fin k) (q : Fin (j - i + 1)) :
    (solve_vR i j q).val = i.val + q.val := rfl

/-- The labels of Cut_L through the vertex map. -/
private lemma solve_cutLLab_eq {α : Type*} (a : Fin k → α) (i j : Fin k) (c : α)
    (p : Fin (k + i - j + 1)) :
    cutLLab a i j c p = if p.val = i.val then c else a (solve_vL i j p) := by
  unfold cutLLab
  split_ifs <;> first | omega | rfl | (congr 1; apply Fin.ext; simp [solve_vL_val]; omega)

private lemma solve_cutLSgn_eq (σ : Fin k → Bool) (i j : Fin k) (p : Fin (k + i - j + 1)) :
    cutLSgn σ i j p = σ (solve_vL i j p) := by
  unfold cutLSgn
  split_ifs with h1 <;> (congr 1; apply Fin.ext; simp [solve_vL_val, h1])

private lemma solve_cutRLab_eq {α : Type*} (a : Fin k → α) (i j : Fin k) (c : α)
    (q : Fin (j - i + 1)) :
    cutRLab a i j c q = if q.val = j.val - i.val then c else a (solve_vR i j q) := by
  have := q.isLt
  unfold cutRLab
  split_ifs with h1 h2 h2 <;> first | omega | rfl

private lemma solve_cutRSgn_eq (σ : Fin k → Bool) (i j : Fin k) (q : Fin (j - i + 1)) :
    cutRSgn σ i j q = σ (solve_vR i j q) := rfl

private lemma solve_mem_polyDiags {n : ℕ} (e : Fin n × Fin n) :
    e ∈ polyDiags n ↔ e.1.val + 2 ≤ e.2.val ∧ ¬(e.1.val = 0 ∧ e.2.val + 1 = n) := by
  simp [polyDiags, IsPolyDiag]

private lemma solve_primF_two (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (t : ℝ) {n : ℕ}
    (h : n = 2) (a : Fin n → Fin L) (σ : Fin n → Bool) :
    primF β M m t a σ = (β : ℂ)⁻¹ * pairK β M t (σ ⟨0, by omega⟩) (σ ⟨1, by omega⟩)
      (a ⟨0, by omega⟩) (a ⟨1, by omega⟩) := by
  subst h
  rfl

private lemma solve_primF_cast (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (t : ℝ) {n n' : ℕ}
    (h : n = n') (a : Fin n → Fin L) (σ : Fin n → Bool) :
    primF β M m t a σ =
      primF β M m t (fun p : Fin n' => a (Fin.cast h.symm p)) (fun p => σ (Fin.cast h.symm p)) := by
  subst h
  rfl

/-- The adjacent pair starting at the position `s`: `(s, s + 1)`, and `(0, k - 1)` for the last
position. -/
private def solve_adj {n : ℕ} (s : Fin (n + 3)) : Fin (n + 3) × Fin (n + 3) :=
  if h : s.val + 1 < n + 3 then (s, ⟨s.val + 1, h⟩) else (0, Fin.last (n + 2))

/-- The pairs `i < j` are the `k` adjacent pairs and the diagonals. -/
private lemma solve_pairs_split {n : ℕ} (T : Fin (n + 3) → Fin (n + 3) → ℂ) :
    ∑ i : Fin (n + 3), ∑ j : Fin (n + 3), (if i < j then T i j else 0) =
      ∑ s, T (solve_adj s).1 (solve_adj s).2 + ∑ d ∈ polyDiags (n + 3), T d.1 d.2 := by
  rw [← Finset.sum_product' (f := fun i j => if i < j then T i j else 0), ← Finset.sum_filter]
  have hadj : ∀ s : Fin (n + 3), ((solve_adj s).1.val = s.val ∧ (solve_adj s).2.val = s.val + 1 ∧
      s.val + 1 < n + 3) ∨ ((solve_adj s).1.val = 0 ∧ (solve_adj s).2.val = n + 2 ∧
      s.val = n + 2) := by
    intro s
    have := s.isLt
    unfold solve_adj
    split_ifs with h
    · exact Or.inl ⟨rfl, rfl, h⟩
    · exact Or.inr ⟨rfl, rfl, by omega⟩
  have hU : (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin (n + 3) × Fin (n + 3) => p.1 < p.2)
      = Finset.univ.image solve_adj ∪ polyDiags (n + 3) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image, solve_mem_polyDiags, Fin.lt_def]
    have := i.isLt; have := j.isLt
    constructor
    · intro h
      by_cases h1 : j.val = i.val + 1
      · left
        refine ⟨i, ?_⟩
        have := hadj i
        apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
      by_cases h2 : i.val = 0 ∧ j.val = n + 2
      · left
        refine ⟨Fin.last (n + 2), ?_⟩
        have := hadj (Fin.last (n + 2))
        simp only [Fin.val_last] at this
        apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
      · right
        omega
    · rintro (⟨s, hs⟩ | h)
      · have := hadj s
        have e1 := congrArg (fun p => p.1.val) hs
        have e2 := congrArg (fun p => p.2.val) hs
        simp only at e1 e2
        omega
      · omega
  have hdisj : Disjoint (Finset.univ.image solve_adj) (polyDiags (n + 3)) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hp
    rw [solve_mem_polyDiags] at hp'
    have := hadj s
    omega
  have hinj : ∀ s ∈ (Finset.univ : Finset (Fin (n + 3))),
      ∀ s' ∈ (Finset.univ : Finset (Fin (n + 3))), solve_adj s = solve_adj s' → s = s' := by
    intro s _ s' _ h
    have h1 := hadj s
    have h2 := hadj s'
    have e1 := congrArg (fun p => p.1.val) h
    have e2 := congrArg (fun p => p.2.val) h
    apply Fin.ext
    omega
  rw [hU, Finset.sum_union hdisj, Finset.sum_image hinj]

/-- The cut term of the adjacent pair `(s, s + 1)` is the pair kernel acting on the label `a_s`. -/
private lemma solve_adj_succ {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {t : ℝ} {n : ℕ} (a : Fin (n + 3) → Fin L) (σ : Fin (n + 3) → Bool)
    (s : Fin (n + 3)) (h : s.val + 1 < n + 3) :
    (β : ℂ) * ∑ c : Fin L, primF β M m t (cutLLab a s ⟨s.val + 1, h⟩ c)
        (cutLSgn σ s ⟨s.val + 1, h⟩) *
      primF β M m t (cutRLab a s ⟨s.val + 1, h⟩ c) (cutRSgn σ s ⟨s.val + 1, h⟩) =
    ∑ c : Fin L, pairK β M t (σ s) (σ (finRotate _ s)) (a s) c *
      primF β M m t (Function.update a s c) σ := by
  have hβ : (β : ℂ) ≠ 0 := by exact_mod_cast hD.pos.ne'
  set j : Fin (n + 3) := ⟨s.val + 1, h⟩ with hj
  have hjv : j.val = s.val + 1 := rfl
  have hrot : finRotate (n + 3) s = j := by
    apply Fin.ext
    rw [solve_finRotate_val, ite_eq_right (by omega)]
  have hlenL : n + 3 + s.val - j.val + 1 = n + 3 := by omega
  have hlenR : j.val - s.val + 1 = 2 := by omega
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [solve_primF_cast β M m t hlenL, solve_primF_two β M m t hlenR]
  have hvL : ∀ p : Fin (n + 3), solve_vL s j (Fin.cast hlenL.symm p) = p := by
    intro p
    apply Fin.ext
    rw [solve_vL_val, Fin.val_cast]
    split_ifs <;> omega
  have hwL : (fun p : Fin (n + 3) => cutLLab a s j c (Fin.cast hlenL.symm p)) =
      Function.update a s c := by
    funext p
    rw [solve_cutLLab_eq, hvL, Function.update_apply, Fin.val_cast]
    by_cases hp : p = s
    · rw [ite_eq_left (congrArg Fin.val hp), ite_eq_left hp]
    · rw [ite_eq_right (fun e => hp (Fin.ext e)), ite_eq_right hp]
  have hsL : (fun p : Fin (n + 3) => cutLSgn σ s j (Fin.cast hlenL.symm p)) = σ := by
    funext p
    rw [solve_cutLSgn_eq, hvL]
  have hv0 : solve_vR s j ⟨0, by omega⟩ = s := Fin.ext (by rw [solve_vR_val]; rfl)
  have hv1 : solve_vR s j ⟨1, by omega⟩ = j := Fin.ext (by rw [solve_vR_val])
  rw [hwL, hsL, solve_cutRSgn_eq, solve_cutRSgn_eq, solve_cutRLab_eq, solve_cutRLab_eq, hv0, hv1,
    ite_eq_right (show (0 : ℕ) ≠ j.val - s.val by omega),
    ite_eq_left (show (1 : ℕ) = j.val - s.val by omega), hrot]
  field_simp

/-- The cut term of the cyclic pair `(0, k - 1)` is the pair kernel acting on the label `a_{k-1}`;
the two signs of the pair kernel are swapped by its symmetry. -/
private lemma solve_adj_last {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {t : ℝ} (ht : |t| < 1) {n : ℕ} (a : Fin (n + 3) → Fin L) (σ : Fin (n + 3) → Bool) :
    (β : ℂ) * ∑ c : Fin L, primF β M m t (cutLLab a 0 (Fin.last (n + 2)) c)
        (cutLSgn σ 0 (Fin.last (n + 2))) *
      primF β M m t (cutRLab a 0 (Fin.last (n + 2)) c) (cutRSgn σ 0 (Fin.last (n + 2))) =
    ∑ c : Fin L, pairK β M t (σ (Fin.last (n + 2))) (σ (finRotate _ (Fin.last (n + 2))))
      (a (Fin.last (n + 2))) c * primF β M m t (Function.update a (Fin.last (n + 2)) c) σ := by
  have hβ : (β : ℂ) ≠ 0 := by exact_mod_cast hD.pos.ne'
  have hlenL : n + 3 + (0 : Fin (n + 3)).val - (Fin.last (n + 2)).val + 1 = 2 := by simp
  have hlenR : (Fin.last (n + 2)).val - (0 : Fin (n + 3)).val + 1 = n + 3 := by simp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [solve_primF_cast β M m t hlenR, solve_primF_two β M m t hlenL]
  have hvR : ∀ q : Fin (n + 3), solve_vR 0 (Fin.last (n + 2)) (Fin.cast hlenR.symm q) = q := by
    intro q
    apply Fin.ext
    rw [solve_vR_val, Fin.val_cast]
    simp
  have hwR : (fun q : Fin (n + 3) => cutRLab a 0 (Fin.last (n + 2)) c (Fin.cast hlenR.symm q)) =
      Function.update a (Fin.last (n + 2)) c := by
    funext q
    rw [solve_cutRLab_eq, hvR, Function.update_apply, Fin.val_cast]
    by_cases hq : q = Fin.last (n + 2)
    · rw [ite_eq_left (by rw [hq]; simp), ite_eq_left hq]
    · have : q.val ≠ n + 2 := fun e => hq (Fin.ext e)
      rw [ite_eq_right (by simpa using this), ite_eq_right hq]
  have hsR : (fun q : Fin (n + 3) => cutRSgn σ 0 (Fin.last (n + 2)) (Fin.cast hlenR.symm q)) =
      σ := by
    funext q
    rw [solve_cutRSgn_eq, hvR]
  have hv0 : solve_vL 0 (Fin.last (n + 2)) ⟨0, by omega⟩ = 0 := Fin.ext (by rw [solve_vL_val]; simp)
  have hv1 : solve_vL 0 (Fin.last (n + 2)) ⟨1, by omega⟩ = Fin.last (n + 2) :=
    Fin.ext (by rw [solve_vL_val]; simp)
  have hrot : finRotate (n + 3) (Fin.last (n + 2)) = 0 := finRotate_last
  rw [hwR, hsR, solve_cutLSgn_eq, solve_cutLSgn_eq, solve_cutLLab_eq, solve_cutLLab_eq, hv0, hv1,
    ite_eq_left (show (0 : ℕ) = (0 : Fin (n + 3)).val by simp),
    ite_eq_right (show (1 : ℕ) ≠ (0 : Fin (n + 3)).val by simp), hrot]
  have hK := congrFun (congrFun (solve_pairK_transpose hD ht (σ (Fin.last (n + 2))) (σ 0)) c)
    (a (Fin.last (n + 2)))
  rw [Matrix.transpose_apply] at hK
  rw [← hK]
  field_simp

/-- The cut term of the adjacent pair at the position `s` is the pair kernel acting on the label
`a_s`. -/
private lemma solve_adj_term {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {t : ℝ} (ht : |t| < 1) {n : ℕ} (a : Fin (n + 3) → Fin L) (σ : Fin (n + 3) → Bool)
    (s : Fin (n + 3)) :
    (β : ℂ) * ∑ c : Fin L, primF β M m t (cutLLab a (solve_adj s).1 (solve_adj s).2 c)
        (cutLSgn σ (solve_adj s).1 (solve_adj s).2) *
      primF β M m t (cutRLab a (solve_adj s).1 (solve_adj s).2 c)
        (cutRSgn σ (solve_adj s).1 (solve_adj s).2) =
    ∑ c : Fin L, pairK β M t (σ s) (σ (finRotate _ s)) (a s) c *
      primF β M m t (Function.update a s c) σ := by
  have key : ∀ p : Fin (n + 3) × Fin (n + 3), p = solve_adj s →
      (β : ℂ) * ∑ c : Fin L, primF β M m t (cutLLab a p.1 p.2 c) (cutLSgn σ p.1 p.2) *
        primF β M m t (cutRLab a p.1 p.2 c) (cutRSgn σ p.1 p.2) =
      ∑ c : Fin L, pairK β M t (σ s) (σ (finRotate _ s)) (a s) c *
        primF β M m t (Function.update a s c) σ := by
    intro p hp
    unfold solve_adj at hp
    split_ifs at hp with h
    · subst hp
      exact solve_adj_succ hD a σ s h
    · subst hp
      have hsl : s = Fin.last (n + 2) := Fin.ext (by have := s.isLt; simp; omega)
      subst hsl
      exact solve_adj_last hD ht a σ
  exact key _ rfl

end Cuts

/-! ## The initial value and continuity of `F_k`

At `t = 0` every dissection with a diagonal vanishes (its link carries the factor `β t`), the empty
dissection gives the `M`-loop of (5.10) [fo:eq:primitive]. -/

section Init

variable {L : ℕ}

/-- `F_k` is continuous in `t` on `(-1, 1)`, for every length. -/
private lemma solve_primF_continuousAt {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) {n : ℕ} (a : Fin n → Fin L)
    (σ : Fin n → Bool) : ContinuousAt (fun s => primF β M m s a σ) t := by
  rcases n with _ | _ | n
  · exact continuousAt_const
  · exact continuousAt_const
  · exact (primF_hasDerivAt hD t ht (by omega) a σ).continuousAt

end Init

/-! ## Uniqueness for the triangular system

For fixed length `k` the difference of two solutions solves a linear system whose coefficients are
the shorter loops, so Gronwall's inequality gives uniqueness by induction on `k`. -/

section Unique

variable {L : ℕ}

end Unique

/-- The generator form after (5.14) [fo:eq:generator]: adjacent cuts give the one-label
operator with the pair kernels, the diagonals give the source. -/
theorem primF_generator {L : ℕ} {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) {k : ℕ} (hk : 3 ≤ k)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    HasDerivAt (fun s => primF β M m s a σ)
      ((β : ℂ) * (∑ j : Fin k, ∑ c : Fin L,
          primF β M m t ![a j, c] ![σ j, σ (finRotate k j)] *
            primF β M m t (Function.update a j c) σ) +
        (β : ℂ) * ∑ d ∈ polyDiags k, ∑ c : Fin L,
          primF β M m t (cutLLab a d.1 d.2 c) (cutLSgn σ d.1 d.2) *
            primF β M m t (cutRLab a d.1 d.2 c) (cutRSgn σ d.1 d.2)) t := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  have ht' : |t| < 1 := abs_lt.mpr ht
  have hβ : (β : ℂ) ≠ 0 := by exact_mod_cast hD.pos.ne'
  refine (primF_hasDerivAt hD t ht (by omega) a σ).congr_deriv ?_
  unfold cutSumFam
  rw [solve_pairs_split, mul_add]
  congr 1
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [solve_adj_term hD ht' a σ s, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    change _ = (β : ℂ) * ((β : ℂ)⁻¹ * pairK β M t (σ s) (σ (finRotate _ s)) (a s) c *
      primF β M m t (Function.update a s c) σ)
    field_simp

/-! ## Duhamel's formula

Variation of constants for the generator form: the propagators of (5.15) [fo:eq:propagators] on
every label cancel the one-label operator, and the diagonal source remains. -/

section Duhamel

variable {L : ℕ}

/-- Moving a one-label matrix across the product of matrices on the labels. -/
private lemma solve_label_act {k : ℕ} (A : Fin k → Matrix (Fin L) (Fin L) ℂ)
    (R : Matrix (Fin L) (Fin L) ℂ) (j : Fin k) (a : Fin k → Fin L)
    (F : (Fin k → Fin L) → ℂ) :
    ∑ b, (∏ l, A l (a l) (b l)) * ∑ c, R (b j) c * F (Function.update b j c) =
      ∑ b, (∏ l ∈ Finset.univ.erase j, A l (a l) (b l)) * (A j * R) (a j) (b j) * F b := by
  set G : (Fin k → Fin L) → ℂ := fun b => ∏ l ∈ Finset.univ.erase j, A l (a l) (b l) with hG
  have hGu : ∀ b e, G (Function.update b j e) = G b := by
    intro b e
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  let eqv : ((Fin k → Fin L) × Fin L) ≃ ((Fin k → Fin L) × Fin L) :=
    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
      left_inv := by intro p; simp
      right_inv := by intro p; simp }
  have lhs : ∑ b, (∏ l, A l (a l) (b l)) * ∑ c, R (b j) c * F (Function.update b j c) =
      ∑ p : (Fin k → Fin L) × Fin L,
        A j (a j) (p.1 j) * G p.1 * (R (p.1 j) p.2 * F (Function.update p.1 j p.2)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Finset.mul_sum]
  have rhs : ∑ b, (∏ l ∈ Finset.univ.erase j, A l (a l) (b l)) * (A j * R) (a j) (b j) * F b =
      ∑ p : (Fin k → Fin L) × Fin L,
        A j (a j) p.2 * G p.1 * (R p.2 (p.1 j) * F p.1) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hG]
    ring
  rw [lhs, rhs]
  refine (Equiv.sum_comp eqv (fun p : (Fin k → Fin L) × Fin L =>
    A j (a j) (p.1 j) * G p.1 * (R (p.1 j) p.2 * F (Function.update p.1 j p.2)))).symm.trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [eqv, hGu]

/-- The propagator `U_{u,t}` times the pair kernel `K_u` on a label is the pair kernel `K_t`; this
cancels the one-label operator of (5.14) [fo:eq:generator] against the derivative of the
propagators. -/
private lemma solve_cancel {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {u t : ℝ} (hu : |u| < 1) (ht : |t| < 1) {k : ℕ} (a : Fin k → Fin L)
    (σ : Fin k → Bool) (F : (Fin k → Fin L) → ℂ) :
    ∑ b, (∏ l, pairU β M u t (σ l) (σ (finRotate k l)) (a l) (b l)) *
        ∑ j, ∑ c, pairK β M u (σ j) (σ (finRotate k j)) (b j) c * F (Function.update b j c) =
      ∑ j, ∑ b, (∏ l ∈ Finset.univ.erase j, pairU β M u t (σ l) (σ (finRotate k l)) (a l) (b l)) *
        pairK β M t (σ j) (σ (finRotate k j)) (a j) (b j) * F b := by
  rw [Finset.sum_congr rfl fun b _ => Finset.mul_sum (Finset.univ : Finset (Fin k)) _ _]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [solve_label_act (fun l => pairU β M u t (σ l) (σ (finRotate k l)))
    (pairK β M u (σ j) (σ (finRotate k j))) j a F]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := solve_prop_mul_ker (solve_pairX_isUnit hD hu (σ j) (σ (finRotate k j)))
    (solve_pairX_isUnit hD ht (σ j) (σ (finRotate k j)))
  rw [← solve_pairU_eq, ← solve_pairK_eq, ← solve_pairK_eq] at h
  rw [h]

end Duhamel

/-- Duhamel's formula (5.16) [fo:eq:duhamel] with the propagators (5.15)
[fo:eq:propagators] acting on every label. -/
theorem primF_duhamel {L : ℕ} {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) {k : ℕ}
    (hk : 3 ≤ k) (a : Fin k → Fin L) (σ : Fin k → Bool) :
    primF β M m t a σ =
      ∑ b : Fin k → Fin L, (∏ j, pairU β M s t (σ j) (σ (finRotate k j)) (a j) (b j)) *
          primF β M m s b σ +
        (β : ℂ) * ∫ u in s..t, ∑ b : Fin k → Fin L,
          (∏ j, pairU β M u t (σ j) (σ (finRotate k j)) (a j) (b j)) *
            ∑ d ∈ polyDiags k, ∑ c : Fin L,
              primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2) *
                primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2) := by
  have hβ : (β : ℂ) ≠ 0 := by exact_mod_cast hD.pos.ne'
  have ht1 : |t| < 1 := abs_lt.mpr ⟨by linarith, ht⟩
  have hIoo : ∀ u ∈ Set.Icc s t, u ∈ Set.Ioo (-1 : ℝ) 1 :=
    fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  set Φ : ℝ → (Fin k → Fin L) → ℂ :=
    fun u b => ∏ j, pairU β M u t (σ j) (σ (finRotate k j)) (a j) (b j) with hΦ
  set Sd : ℝ → (Fin k → Fin L) → ℂ := fun u b => ∑ d ∈ polyDiags k, ∑ c : Fin L,
    primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2) *
      primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2) with hSd
  set H : ℝ → ℂ := fun u => ∑ b, Φ u b * primF β M m u b σ with hH
  set H' : ℝ → ℂ := fun u => (β : ℂ) * ∑ b, Φ u b * Sd u b with hH'
  have hderiv : ∀ u ∈ Set.uIcc s t, HasDerivAt H (H' u) u := by
    intro u hu
    rw [Set.uIcc_of_le hst] at hu
    have hu1 := hIoo u hu
    have hu' : |u| < 1 := abs_lt.mpr hu1
    have hΦd : ∀ b : Fin k → Fin L, HasDerivAt (fun u => Φ u b)
        (∑ j, (∏ l ∈ Finset.univ.erase j,
          pairU β M u t (σ l) (σ (finRotate k l)) (a l) (b l)) *
            (-(pairK β M t (σ j) (σ (finRotate k j)) (a j) (b j)))) u := by
      intro b
      have h := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin k))) (x := u)
        (f := fun j u => pairU β M u t (σ j) (σ (finRotate k j)) (a j) (b j))
        (f' := fun j => -(pairK β M t (σ j) (σ (finRotate k j)) (a j) (b j)))
        (fun j _ => solve_pairU_hasDerivAt β M u t _ _ _ _)
      simpa only [smul_eq_mul] using h
    have hFd := fun b : Fin k → Fin L => primF_generator hD u hu1 hk b σ
    have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin k → Fin L)))
      (fun b _ => (hΦd b).mul (hFd b))
    refine hsum.congr_deriv ?_
    have hF2 : ∀ b : Fin k → Fin L, (β : ℂ) * (∑ j : Fin k, ∑ c : Fin L,
        primF β M m u ![b j, c] ![σ j, σ (finRotate k j)] *
          primF β M m u (Function.update b j c) σ) =
        ∑ j : Fin k, ∑ c : Fin L, pairK β M u (σ j) (σ (finRotate k j)) (b j) c *
          primF β M m u (Function.update b j c) σ := by
      intro b
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      change (β : ℂ) * ((β : ℂ)⁻¹ * pairK β M u (σ j) (σ (finRotate k j)) (b j) c *
        primF β M m u (Function.update b j c) σ) = _
      field_simp
    have hB := solve_cancel hD hu' ht1 a σ (fun b => primF β M m u b σ)
    have hA : ∑ b : Fin k → Fin L, (∑ j, (∏ l ∈ Finset.univ.erase j,
        pairU β M u t (σ l) (σ (finRotate k l)) (a l) (b l)) *
          (-(pairK β M t (σ j) (σ (finRotate k j)) (a j) (b j)))) * primF β M m u b σ =
        -∑ j, ∑ b : Fin k → Fin L, (∏ l ∈ Finset.univ.erase j,
          pairU β M u t (σ l) (σ (finRotate k l)) (a l) (b l)) *
            pairK β M t (σ j) (σ (finRotate k j)) (a j) (b j) * primF β M m u b σ := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    have hC : ∑ b : Fin k → Fin L, Φ u b * ((β : ℂ) * (∑ j : Fin k, ∑ c : Fin L,
        primF β M m u ![b j, c] ![σ j, σ (finRotate k j)] *
          primF β M m u (Function.update b j c) σ)) =
        ∑ j, ∑ b : Fin k → Fin L, (∏ l ∈ Finset.univ.erase j,
          pairU β M u t (σ l) (σ (finRotate k l)) (a l) (b l)) *
            pairK β M t (σ j) (σ (finRotate k j)) (a j) (b j) * primF β M m u b σ := by
      rw [← hB]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hF2 b]
    simp only [hH', Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]
    rw [hA, hC]
    have hS : ∑ x : Fin k → Fin L, Φ u x * ((β : ℂ) * ∑ d ∈ polyDiags k, ∑ c : Fin L,
        primF β M m u (cutLLab x d.1 d.2 c) (cutLSgn σ d.1 d.2) *
          primF β M m u (cutRLab x d.1 d.2 c) (cutRSgn σ d.1 d.2)) =
        (β : ℂ) * ∑ b, Φ u b * Sd u b := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [hSd]
      ring
    rw [hS]
    ring
  have hcont : ContinuousOn H' (Set.Icc s t) := by
    refine continuousOn_const.mul (continuousOn_finsetSum _ fun b _ => ?_)
    refine ContinuousOn.mul ?_ ?_
    · exact (continuous_finsetProd _ fun j _ => continuous_iff_continuousAt.2 fun u =>
        (solve_pairU_hasDerivAt β M u t _ _ _ _).continuousAt).continuousOn
    · refine continuousOn_finsetSum _ fun d _ => continuousOn_finsetSum _ fun c _ =>
        ContinuousOn.mul ?_ ?_ <;>
      exact fun u hu => (solve_primF_continuousAt hD (hIoo u hu) _ _).continuousWithinAt
  have hint : IntervalIntegrable H' volume s t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hst]
    exact hcont
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hHt : H t = primF β M m t a σ := by
    simp only [hH, hΦ, solve_pairU_self hD ht1, Matrix.one_apply]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi]), zero_mul]
    · simp
  have hI : ∫ u in s..t, H' u = (β : ℂ) * ∫ u in s..t, ∑ b, Φ u b * Sd u b :=
    intervalIntegral.integral_const_mul _ _
  rw [hI, hHt] at hftc
  change primF β M m t a σ = H s + (β : ℂ) * ∫ u in s..t, ∑ b, Φ u b * Sd u b
  rw [hftc]
  ring

end LSBA
