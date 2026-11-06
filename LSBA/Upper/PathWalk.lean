import LSBA.Upper.StrongWalk
import LSBA.Transfer.Path

/-!
# The one-path expansion on a Dirichlet path

The linear algebra of the path form of [PSSS, Theorem 1] used in the proof of Theorem 3.1
[thm:strong-upper]. On the Dirichlet path of `m` blocks (the operator (8.5)
[up:eq:shifted-resolvent] at zero endpoint shifts), the walk `γ_j` from `x` to `y` is the only
self-avoiding walk: the neighbour of `x` on the far side from `y` is separated from `y` once `x`
is deleted, and each later `γ_i` has the single neighbour `γ_{i+1}` left. So
`G(x, y) = (-g/m)^k G_{Λ_0}(γ_0, γ_0) ⋯ G_{Λ_k}(γ_k, γ_k)`, `k = |x - y|`, `m = max{1, g}`, with
the masked resolvents of [PSSS, (2.7)].
-/

open Finset
open scoped Matrix Kronecker

noncomputable section

open scoped Classical

namespace LSBA

/-- If `Λ` splits along a set `S` of blocks, with no hopping inside `Λ` between `S` and its
complement, then the masked resolvent `G_Λ(E)` has no block from `S` to the complement of `S`. -/
theorem blockOf_maskRes_eq_zero_of_separated {W L : ℕ}
    (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (Λ S : Finset (Fin L)) (E : ℝ)
    (hdet : (maskMat {p | p.1 ∈ Λ}
      (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))).det ≠ 0)
    (hsep : ∀ a ∈ Λ, ∀ b ∈ Λ, a ∈ S → b ∉ S → blockOf H a b = 0 ∧ blockOf H b a = 0)
    {c y : Fin L} (hc : c ∈ S) (hy : y ∉ S) : blockOf (maskRes H Λ E) c y = 0 := by
  set X := maskMat {p : Fin L × Fin W | p.1 ∈ Λ}
    (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) with hX
  set P : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    Matrix.diagonal fun p => if p.1 ∈ S then 1 else 0 with hP
  have hne : ∀ p q : Fin L × Fin W, p.1 ∈ S → q.1 ∉ S → X p q = 0 ∧ X q p = 0 := by
    intro p q hp hq
    have hpq : p ≠ q := fun h => hq (h ▸ hp)
    have hpq1 : p.1 ≠ q.1 := fun h => hq (h ▸ hp)
    constructor
    · simp only [hX, maskMat, Matrix.of_apply, Set.mem_ofPred_eq]
      by_cases h : p.1 ∈ Λ ∧ q.1 ∈ Λ
      · have h0 := congrFun (congrFun (hsep _ h.1 _ h.2 hp hq).1 p.2) q.2
        simp only [blockOf, Matrix.of_apply, Matrix.zero_apply] at h0
        simp [Matrix.sub_apply, Matrix.smul_apply, hpq, h0, h]
      · simp [h, hpq]
    · simp only [hX, maskMat, Matrix.of_apply, Set.mem_ofPred_eq]
      by_cases h : q.1 ∈ Λ ∧ p.1 ∈ Λ
      · have h0 := congrFun (congrFun (hsep _ h.2 _ h.1 hp hq).2 q.2) p.2
        simp only [blockOf, Matrix.of_apply, Matrix.zero_apply] at h0
        simp [Matrix.sub_apply, Matrix.smul_apply, hpq.symm, h0, h]
      · simp [h, hpq.symm]
  have hcomm : X * P = P * X := by
    ext p q
    rw [hP, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hp : p.1 ∈ S <;> by_cases hq : q.1 ∈ S
    · simp [hp, hq]
    · simp [hp, hq, (hne p q hp hq).1]
    · simp [hp, hq, (hne q p hq hp).2]
    · simp [hp, hq]
  have hu : IsUnit X.det := isUnit_iff_ne_zero.mpr hdet
  have hinv : X⁻¹ * P = P * X⁻¹ := by
    calc X⁻¹ * P = X⁻¹ * P * (X * X⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = X⁻¹ * (P * X) * X⁻¹ := by simp only [Matrix.mul_assoc]
      _ = X⁻¹ * (X * P) * X⁻¹ := by rw [hcomm]
      _ = (X⁻¹ * X) * P * X⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P * X⁻¹ := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  ext α β
  have h := congrFun (congrFun hinv (c, α)) (y, β)
  rw [hP, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  simp only [hc, hy, ↓reduceIte, mul_zero, one_mul] at h
  simpa [blockOf, maskRes, hX] using h.symm

/-- The block `γ_j` of the walk from `x` to `y` on the Dirichlet path: `x + j` up to `y` when
`x ≤ y`, and `x - j` down to `y` when `y < x`. -/
def pathWalk {m : ℕ} (x y : Fin m) (j : ℕ) : Fin m :=
  ⟨if x ≤ y then min (x.val + j) y.val else max (x.val - j) y.val, by
    have := x.isLt; have := y.isLt; split_ifs <;> omega⟩

/-- The walk from `x` to `y` reaches `y` in `|x - y|` steps. -/
theorem pathWalk_dist {m : ℕ} (x y : Fin m) : pathWalk x y (Nat.dist x y) = y := by
  ext
  simp only [pathWalk, Nat.dist, Fin.le_def]
  split_ifs <;> omega

/-- The walk from `x` to `y` starts at `x`. -/
theorem pathWalk_zero {m : ℕ} (x y : Fin m) : pathWalk x y 0 = x := by
  ext
  simp only [pathWalk, Fin.le_def]
  split_ifs <;> omega

/-- The walk from `x` to `y` visits distinct blocks during its `|x - y| + 1` steps. -/
theorem pathWalk_ne {m : ℕ} (x y : Fin m) {i j : ℕ} (hi : i ≤ Nat.dist x y) (hji : j < i) :
    pathWalk x y j ≠ pathWalk x y i := by
  intro h
  have h' := congrArg Fin.val h
  simp only [pathWalk, Nat.dist, Fin.le_def] at h' hi
  split_ifs at h' <;> omega

/-- Blocks of the path are adjacent iff they differ by one. -/
private theorem pathWalk_adj_apply {m : ℕ} (a b : Fin m) :
    pathAdj m a b = if a.val + 1 = b.val ∨ b.val + 1 = a.val then 1 else 0 := rfl

/-- The off-diagonal blocks of the path operator at zero shifts:
`H_{xc} = (g/m) P_n(x, c) I_W` for `x ≠ c`, `m = max{1, g}`. -/
theorem blockOf_pathOp_of_ne (g : ℝ) {W m : ℕ} (V : Fin m → Matrix (Fin W) (Fin W) ℂ)
    {x c : Fin m} (hxc : x ≠ c) :
    blockOf (pathOp g V 0 0) x c =
      (((g / max 1 g : ℝ) : ℂ) * pathAdj m x c) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
  ext α β
  simp only [blockOf, pathOp, blockDiagOp, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.kroneckerMap_apply, hxc, ↓reduceIte, add_zero, smul_eq_mul]
  push_cast
  ring

variable {W m : ℕ} {H : Matrix (Fin m × Fin W) (Fin m × Fin W) ℂ} {t : ℂ}

/-- One deletion step with a single neighbour `n` of `x` left in `Λ ∖ {x}`:
`G_Λ(x, y) = -t G_Λ(x, x) G_{Λ∖{x}}(n, y)`. -/
private theorem pathWalk_delete_single
    (hoff : ∀ a c : Fin m, a ≠ c → blockOf H a c = (t * pathAdj m a c) • 1)
    (E : ℝ) {Λ : Finset (Fin m)} {x y n : Fin m} (hx : x ∈ Λ) (hy : y ∈ Λ) (hxy : x ≠ y)
    (hΛ : (maskMat {p | p.1 ∈ Λ}
      (H - (E : ℂ) • (1 : Matrix (Fin m × Fin W) (Fin m × Fin W) ℂ))).det ≠ 0)
    (hΛx : (maskMat {p | p.1 ∈ Λ.erase x}
      (H - (E : ℂ) • (1 : Matrix (Fin m × Fin W) (Fin m × Fin W) ℂ))).det ≠ 0)
    (hn : n ∈ Λ.erase x) (hxn : pathAdj m x n = 1)
    (hother : ∀ c ∈ Λ.erase x, c ≠ n → t * pathAdj m x c = 0 ∨
      blockOf (maskRes H (Λ.erase x) E) c y = 0) :
    blockOf (maskRes H Λ E) x y =
      (-t) • (blockOf (maskRes H Λ E) x x * blockOf (maskRes H (Λ.erase x) E) n y) := by
  rw [blockOf_maskRes_delete H hx hy hxy E hΛ hΛx, Finset.sum_eq_single n
    (fun c hc hcn => ?_) (fun h => absurd hn h)]
  · rw [hoff x n (Finset.ne_of_mem_erase hn).symm, hxn, mul_one]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, neg_smul]
  · rw [hoff x c (Finset.ne_of_mem_erase hc).symm]
    rcases hother c hc hcn with h | h
    · rw [h, zero_smul, Matrix.mul_zero, Matrix.zero_mul]
    · rw [h, Matrix.mul_zero]

/-- `Λ_{i+1} = Λ_i ∖ {γ_i}`. -/
private theorem pathWalk_rest_succ (γ : ℕ → Fin m) (i : ℕ) :
    walkRest γ (i + 1) = (walkRest γ i).erase (γ i) := by
  ext c
  simp only [walkRest, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · intro h
    exact ⟨h i (Nat.lt_succ_self i), fun j hj => h j (Nat.lt_succ_of_lt hj)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact h2 j hj
    · exact h1

/-- `Λ_0` is everything. -/
private theorem pathWalk_rest_zero (γ : ℕ → Fin m) : walkRest γ 0 = univ := by
  ext c
  simp [walkRest]

/-- A block of the walk visited at a step `l ≥ i` lies in `Λ_i`. -/
private theorem pathWalk_mem_rest {γ : ℕ → Fin m} {k : ℕ}
    (hinj : ∀ i ≤ k, ∀ j < i, γ j ≠ γ i) {i l : ℕ} (hil : i ≤ l) (hl : l ≤ k) :
    γ l ∈ walkRest γ i := by
  simp only [walkRest, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j hj
  exact (hinj l hl j (by omega)).symm

/-- A block visited before step `i` is not in `Λ_i`. -/
private theorem pathWalk_not_mem_rest (γ : ℕ → Fin m) {i j : ℕ} (hji : j < i) :
    γ j ∉ walkRest γ i := by
  simp only [walkRest, Finset.mem_filter, Finset.mem_univ, true_and, not_forall]
  exact ⟨j, hji, fun h => h rfl⟩

/-- Downward induction along the walk, from the second step on. -/
private theorem pathWalk_induction
    (hoff : ∀ a c : Fin m, a ≠ c → blockOf H a c = (t * pathAdj m a c) • 1) (E : ℝ)
    (hdet : ∀ Λ : Finset (Fin m), (maskMat {p | p.1 ∈ Λ}
      (H - (E : ℂ) • (1 : Matrix (Fin m × Fin W) (Fin m × Fin W) ℂ))).det ≠ 0)
    {γ : ℕ → Fin m} {k : ℕ} (hinj : ∀ i ≤ k, ∀ j < i, γ j ≠ γ i)
    (hstep : ∀ i < k, pathAdj m (γ i) (γ (i + 1)) = 1)
    (hprev : ∀ i, 1 ≤ i → i < k → ∀ c, pathAdj m (γ i) c ≠ 0 → c = γ (i + 1) ∨ c = γ (i - 1))
    (u : ℕ) :
    ∀ i, 1 ≤ i → i + u = k →
      blockOf (maskRes H (walkRest γ i) E) (γ i) (γ k) =
        (-t) ^ u • ((List.range (u + 1)).map fun l =>
          blockOf (maskRes H (walkRest γ (i + l)) E) (γ (i + l)) (γ (i + l))).prod := by
  induction u with
  | zero =>
    intro i _ hik
    subst hik
    simp
  | succ u ih =>
    intro i hi hik
    have hstep' := pathWalk_delete_single hoff E (Λ := walkRest γ i) (x := γ i) (y := γ k)
      (n := γ (i + 1)) (pathWalk_mem_rest hinj le_rfl (by omega))
      (pathWalk_mem_rest hinj (by omega) le_rfl) (hinj k le_rfl i (by omega)) (hdet _) (hdet _)
      (by rw [← pathWalk_rest_succ]; exact pathWalk_mem_rest hinj le_rfl (by omega))
      (hstep i (by omega)) (fun c hc hcn => Or.inl (by
        by_contra h0
        have h1 : pathAdj m (γ i) c ≠ 0 := fun h => h0 (by rw [h, mul_zero])
        rcases hprev i hi (by omega) c h1 with h2 | h2
        · exact hcn h2
        · rw [← pathWalk_rest_succ, h2] at hc
          exact pathWalk_not_mem_rest γ (by omega) hc))
    rw [hstep', ← pathWalk_rest_succ, ih (i + 1) (by omega) (by omega), Matrix.mul_smul,
      smul_smul, ← pow_succ', List.range_succ_eq_map (n := u + 1), List.map_cons, List.prod_cons,
      List.map_map]
    congr 2
    refine congrArg List.prod (List.map_congr_left fun l _ => ?_)
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    rw [show i + (l + 1) = i + 1 + l by omega]

/-- The one-path expansion, for a walk `γ` with `γ_0 = a`, `k ≥ 1`, whose only surviving first
step is `γ_1`: `G(γ_0, γ_k) = (-t)^k G_{Λ_0}(γ_0, γ_0) ⋯ G_{Λ_k}(γ_k, γ_k)`. -/
private theorem pathWalk_expansion
    (hoff : ∀ a c : Fin m, a ≠ c → blockOf H a c = (t * pathAdj m a c) • 1) (E : ℝ)
    (hdet : ∀ Λ : Finset (Fin m), (maskMat {p | p.1 ∈ Λ}
      (H - (E : ℂ) • (1 : Matrix (Fin m × Fin W) (Fin m × Fin W) ℂ))).det ≠ 0)
    {γ : ℕ → Fin m} {k : ℕ} (hk : 1 ≤ k) (hinj : ∀ i ≤ k, ∀ j < i, γ j ≠ γ i)
    (hstep : ∀ i < k, pathAdj m (γ i) (γ (i + 1)) = 1)
    (hprev : ∀ i, 1 ≤ i → i < k → ∀ c, pathAdj m (γ i) c ≠ 0 → c = γ (i + 1) ∨ c = γ (i - 1))
    (hfirst : ∀ c ∈ (univ : Finset (Fin m)).erase (γ 0), c ≠ γ 1 → pathAdj m (γ 0) c = 0 ∨
      blockOf (maskRes H (univ.erase (γ 0)) E) c (γ k) = 0) :
    blockOf (resolventMat H E) (γ 0) (γ k) = (-t) ^ k • walkProd H E γ k := by
  have hrest1 : walkRest γ 1 = univ.erase (γ 0) := by
    rw [pathWalk_rest_succ, pathWalk_rest_zero]
  have h1 := pathWalk_delete_single hoff E (Λ := univ) (x := γ 0) (y := γ k) (n := γ 1)
    (Finset.mem_univ _) (Finset.mem_univ _) (hinj k le_rfl 0 (by omega)) (hdet _) (hdet _)
    (Finset.mem_erase.mpr ⟨(hinj 1 hk 0 (by omega)).symm, Finset.mem_univ _⟩)
    (hstep 0 (by omega)) (fun c hc hcn => by
      rcases hfirst c hc hcn with h | h
      · exact Or.inl (by rw [h, mul_zero])
      · exact Or.inr h)
  have h2 := pathWalk_induction hoff E hdet hinj hstep hprev (k - 1) 1 le_rfl (by omega)
  rw [hrest1] at h2
  rw [← maskRes_univ, h1, h2, Matrix.mul_smul, smul_smul, ← pow_succ', Nat.sub_add_cancel hk]
  unfold walkProd
  rw [List.range_succ_eq_map (n := k), List.map_cons, List.prod_cons, List.map_map]
  simp only [pathWalk_rest_zero]
  congr 3
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply, Nat.succ_eq_add_one, add_comm 1 l]

/-- Hopping across a deleted block of the path vanishes: blocks on the two sides of `x` are not
adjacent. -/
private theorem pathWalk_adj_sides {a b x : Fin m} (ha : a.val < x.val) (hb : x.val < b.val) :
    pathAdj m a b = 0 ∧ pathAdj m b a = 0 := by
  have h1 : ¬ (a.val + 1 = b.val ∨ b.val + 1 = a.val) := by omega
  have h2 : ¬ (b.val + 1 = a.val ∨ a.val + 1 = b.val) := by omega
  simp [pathWalk_adj_apply, h1, h2]

/-- The one-path expansion on the Dirichlet path ([PSSS, (2.7)] and the proof of [PSSS,
Theorem 1] with one element in `Π_k(x, y)`): if all masked operators of the path operator at zero
shifts are invertible at the real energy `E`, then for all blocks `x, y`,
`G(x, y) = (-g/m)^k G_{Λ_0}(γ_0, γ_0) ⋯ G_{Λ_k}(γ_k, γ_k)` with `k = |x - y|`, `m = max{1, g}`
and `γ` the walk from `x` to `y`. -/
theorem blockOf_resolventMat_pathOp_eq_walkProd (g : ℝ) {W m : ℕ}
    (V : Fin m → Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (hdet : ∀ Λ : Finset (Fin m), (maskMat {p | p.1 ∈ Λ}
      (pathOp g V 0 0 - (E : ℂ) • (1 : Matrix (Fin m × Fin W) (Fin m × Fin W) ℂ))).det ≠ 0)
    (x y : Fin m) :
    blockOf (resolventMat (pathOp g V 0 0) E) x y =
      (-((g / max 1 g : ℝ) : ℂ)) ^ Nat.dist x y •
        walkProd (pathOp g V 0 0) E (pathWalk x y) (Nat.dist x y) := by
  by_cases hxy : x = y
  · subst hxy
    simp [walkProd, walkRest, pathWalk_zero, maskRes_univ]
  have hk : 1 ≤ Nat.dist x y := by
    have : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    unfold Nat.dist
    omega
  have hoff := fun a c hac => blockOf_pathOp_of_ne g V (x := a) (c := c) hac
  have hz := pathWalk_zero x y
  have hd := pathWalk_dist x y
  have hval : ∀ i, i ≤ Nat.dist x y → ((pathWalk x y i).val =
      if x.val ≤ y.val then x.val + i else x.val - i) := by
    intro i hi
    simp only [pathWalk, Fin.le_def]
    simp only [Nat.dist] at hi
    split_ifs <;> omega
  have hexp := pathWalk_expansion hoff E hdet (γ := pathWalk x y) hk
    (fun i hi j hj => pathWalk_ne x y hi hj)
    (fun i hi => by
      have h1 := hval i (by omega)
      have h2 := hval (i + 1) (by omega)
      simp only [Nat.dist] at hi
      have h4 : (pathWalk x y i).val + 1 = (pathWalk x y (i + 1)).val ∨
          (pathWalk x y (i + 1)).val + 1 = (pathWalk x y i).val := by
        split_ifs at h1 h2 <;> omega
      simp [pathWalk_adj_apply, h4])
    (fun i hi1 hi c hc => by
      have h1 := hval i (by omega)
      have h2 := hval (i + 1) (by omega)
      have h3 := hval (i - 1) (by omega)
      have hc' : (pathWalk x y i).val + 1 = c.val ∨ c.val + 1 = (pathWalk x y i).val := by
        by_contra h
        exact hc (by simp [pathWalk_adj_apply, h])
      simp only [Nat.dist] at hi
      simp only [Fin.ext_iff]
      split_ifs at h1 h2 h3 <;> omega)
    (fun c hc hc1 => by
      rw [hz] at hc ⊢
      rw [hd]
      have hcx : c.val ≠ x.val := fun h => (Finset.mem_erase.mp hc).1 (Fin.ext h)
      have h1 := hval 1 hk
      have hc1' : c.val ≠ (pathWalk x y 1).val := fun h => hc1 (Fin.ext h)
      by_cases hadj : x.val + 1 = c.val ∨ c.val + 1 = x.val
      · right
        have hdet' := hdet ((univ : Finset (Fin m)).erase x)
        have hsep : ∀ S : Finset (Fin m), (∀ a ∈ S, ∀ b ∉ S, b ≠ x → pathAdj m a b = 0 ∧
            pathAdj m b a = 0) → ∀ a ∈ (univ : Finset (Fin m)).erase x,
            ∀ b ∈ (univ : Finset (Fin m)).erase x, a ∈ S → b ∉ S →
            blockOf (pathOp g V 0 0) a b = 0 ∧ blockOf (pathOp g V 0 0) b a = 0 := by
          intro S hS a _ b hb ha hbS
          have hab : a ≠ b := fun h => hbS (h ▸ ha)
          obtain ⟨h0, h0'⟩ := hS a ha b hbS (Finset.mem_erase.mp hb).1
          rw [hoff a b hab, hoff b a hab.symm, h0, h0']
          simp
        have hxyv : x.val ≠ y.val := fun h => hxy (Fin.ext h)
        by_cases hle : x.val < y.val
        · have hcl : c.val < x.val := by
            simp only [hle.le, ↓reduceIte] at h1
            omega
          refine blockOf_maskRes_eq_zero_of_separated _ _ (univ.filter fun a => a.val < x.val) E
            hdet' (hsep _ fun a ha b hb hbx => ?_) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl⟩)
            (fun h => absurd (Finset.mem_filter.mp h).2 (by omega))
          have hb' : ¬ b.val < x.val := fun h => hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have hbx' : b.val ≠ x.val := fun h => hbx (Fin.ext h)
          exact pathWalk_adj_sides (Finset.mem_filter.mp ha).2 (by omega)
        · have hcl : x.val < c.val := by
            simp only [show ¬ x.val ≤ y.val by omega, ↓reduceIte] at h1
            omega
          refine blockOf_maskRes_eq_zero_of_separated _ _ (univ.filter fun a => x.val < a.val) E
            hdet' (hsep _ fun a ha b hb hbx => ?_) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl⟩)
            (fun h => absurd (Finset.mem_filter.mp h).2 (by omega))
          have hb' : ¬ x.val < b.val := fun h => hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have hbx' : b.val ≠ x.val := fun h => hbx (Fin.ext h)
          exact (pathWalk_adj_sides (a := b) (b := a) (x := x) (by omega)
            (Finset.mem_filter.mp ha).2).symm
      · left
        simp [pathWalk_adj_apply, hadj])
  rwa [hz, hd] at hexp

/-- Almost surely, for every set `Λ` of blocks and a deterministic `K`, the masked operator of
`K + diag(V_a)` at the energy `E` is invertible. -/
theorem ae_det_maskMat_add_gueBlock_ne_zero {W L : ℕ}
    (K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (E : ℝ) :
    ∀ᵐ ω ∂(μ W L), ∀ Λ : Finset (Fin L), (maskMat {p | p.1 ∈ Λ}
      (K + blockDiagOp (gueBlock W L ω) -
        (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))).det ≠ 0 := by
  rw [MeasureTheory.ae_all_iff]
  intro Λ
  set K₀ : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    Matrix.of fun p q => if (p.1 ∈ Λ ↔ q.1 ∈ Λ) then K p q else 0 with hK₀
  filter_upwards [ae_det_ne_zero_gueBlock K₀ (c := 1) one_ne_zero (E : ℂ)] with ω hω
  refine det_maskMat_ne_zero_of_blockDiag
    (Y := K₀ + ((1 : ℝ) : ℂ) • blockDiagOp (gueBlock W L ω) -
      (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) ?_ ?_ ?_ hω
  · intro p q hp hq
    have hp' : p.1 ∈ Λ := hp
    have hq' : q.1 ∉ Λ := hq
    have hpq : p ≠ q := fun h => hq' (h ▸ hp')
    have hpq1 : p.1 ≠ q.1 := fun h => hq' (h ▸ hp')
    simp [hK₀, blockDiagOp, hp', hq', hpq, hpq1]
  · intro p q hp hq
    have hp' : p.1 ∉ Λ := hp
    have hq' : q.1 ∈ Λ := hq
    have hpq : p ≠ q := fun h => hp' (h ▸ hq')
    have hpq1 : p.1 ≠ q.1 := fun h => hp' (h ▸ hq')
    simp [hK₀, blockDiagOp, hp', hq', hpq, hpq1]
  · intro p q hp hq
    have hp' : p.1 ∈ Λ := hp
    have hq' : q.1 ∈ Λ := hq
    simp [hK₀, hp', hq']

/-- For `g ≤ 1`, the path operator at zero shifts is `K + diag(V_a)`, with the deterministic
`K = g P_m ⊗ I_W`. -/
theorem pathOp_eq_add_blockDiagOp {g : ℝ} (hg : g ≤ 1) {W m : ℕ}
    (V : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    pathOp g V 0 0 = pathOp g (fun _ => 0) 0 0 + blockDiagOp V := by
  ext p q
  simp only [pathOp, max_eq_left hg, Matrix.add_apply, Matrix.smul_apply, blockDiagOp,
    Matrix.of_apply]
  split_ifs <;> simp

end LSBA
