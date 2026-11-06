import LSBA.Transfer.PathCut

/-!
# Interval splitting and the cycle Schur identity

The Schur identity `G(p, y) = −(g/m) G_Λ^{L₀,R₀}(0, n₀) G_right(0, y′)` on
`Fin (p + (n₀+1) + q)`, and the cycle Schur identity (E.15) [eq:c-cycle-Schur] with one block
deleted.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Blocks of a block path whose potential is precomposed with a length identification. -/
private theorem pathSchur_blockOf_cast {g : ℝ} {W m n : ℕ} (h : m = n)
    (V : Fin n → Matrix (Fin W) (Fin W) ℂ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (a b : Fin m) :
    blockOf (resolventMat (pathOp g (V ∘ Fin.cast h) L₀ R₀) E) a b =
      blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.cast h a) (Fin.cast h b) := by
  subst h
  rfl

/-- The interval split of the proof of Proposition 8.2 [up:prop:fr-concentration]: for the
path `[0, p) ∪ Λ ∪ [p+n₀+1, p+n₀+1+q)` with `Λ = [p, p+n₀]`,
`G(p, y) = -(g/max{1,g}) G_Λ^{L₀,R₀}(p, p+n₀) G_{right}(p+n₀+1, y)`, with the shifts induced by
the two outer paths. -/
theorem pathOp_interval_split (g : ℝ) {W p n₀ q : ℕ} (hq : 0 < q)
    (V : Fin (p + (n₀ + 1) + q) → Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (hL : (pathOp g (V ∘ Fin.castAdd q ∘ Fin.castAdd (n₀ + 1)) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ)).det ≠ 0)
    (hR : (pathOp g (V ∘ Fin.natAdd (p + (n₀ + 1))) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ)).det ≠ 0)
    (j : Fin q) :
    blockOf (resolventMat (pathOp g V 0 0) E) (Fin.castAdd q (Fin.natAdd p 0))
        (Fin.natAdd (p + (n₀ + 1)) j) =
      -((g / max 1 g : ℝ) : ℂ) •
        (blockOf (resolventMat
            (pathOp g (V ∘ Fin.castAdd q ∘ Fin.natAdd p)
              (shiftFromLeft g (V ∘ Fin.castAdd q ∘ Fin.castAdd (n₀ + 1)) 0 E)
              (shiftFromRight g (V ∘ Fin.natAdd (p + (n₀ + 1))) 0 E)) E) 0 (Fin.last n₀) *
          blockOf (resolventMat (pathOp g (V ∘ Fin.natAdd (p + (n₀ + 1))) 0 0) E) ⟨0, hq⟩ j) := by
  have hP : 0 < p + (n₀ + 1) := by omega
  rw [pathOp_cut_offdiag g hP hq V 0 0 E hR (Fin.natAdd p 0) j]
  have hidx : (⟨p + (n₀ + 1) - 1, by omega⟩ : Fin (p + (n₀ + 1))) = Fin.natAdd p (Fin.last n₀) :=
    Fin.ext (by simp)
  congr 2
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have hs : shiftFromLeft g (V ∘ Fin.castAdd q ∘ Fin.castAdd (n₀ + 1)) 0 E = 0 := by
      simp [shiftFromLeft]
    rw [hs, hidx]
    have hn : n₀ + 1 = 0 + (n₀ + 1) := by omega
    have hV : (V ∘ Fin.castAdd q ∘ Fin.natAdd 0) = (V ∘ Fin.castAdd q) ∘ Fin.cast hn := by
      funext i
      simp only [Function.comp]
      congr 2
      exact Fin.ext (by simp)
    rw [hV, pathSchur_blockOf_cast hn]
    congr 1
    exact Fin.ext (by simp)
  · rw [hidx, pathOp_cut_right g hp (V ∘ Fin.castAdd q) 0 _ E hL 0 (Fin.last n₀)]
    rfl

/-- Block `a + 1 + j` of `ℤ_L`: the path `ℤ_L ∖ {a}` of (E.15) [eq:c-cycle-Schur]. -/
def cycPathBlock {L : ℕ} (a : Fin L) (j : Fin (L - 1)) : Fin L :=
  ⟨(a.val + 1 + j.val) % L, Nat.mod_lt _ a.pos⟩

private theorem pathSchur_mod_cases (x L : ℕ) (hx : x < 2 * L) :
    (x % L = x ∧ x < L) ∨ (x % L + L = x ∧ L ≤ x) := by
  rcases lt_or_ge x L with h | h
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · right
    have h2 : x % L = x - L := by
      rw [Nat.mod_eq_sub_mod h]
      exact Nat.mod_eq_of_lt (by omega)
    exact ⟨by omega, h⟩

/-- The value of `cycPathBlock a j`, by cases on the wrap-around. -/
private theorem pathSchur_cyc_val {L : ℕ} (a : Fin L) (j : Fin (L - 1)) :
    ((cycPathBlock a j).val = a.val + 1 + j.val ∧ a.val + 1 + j.val < L) ∨
    ((cycPathBlock a j).val + L = a.val + 1 + j.val ∧ L ≤ a.val + 1 + j.val) := by
  have := a.isLt
  have := j.isLt
  exact pathSchur_mod_cases (a.val + 1 + j.val) L (by omega)

private theorem pathSchur_cyc_ne {L : ℕ} (a : Fin L) (j : Fin (L - 1)) :
    cycPathBlock a j ≠ a := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 := pathSchur_cyc_val a j
  have := a.isLt
  have := j.isLt
  omega

private theorem pathSchur_cyc_inj {L : ℕ} (a : Fin L) {j k : Fin (L - 1)}
    (h : cycPathBlock a j = cycPathBlock a k) : j = k := by
  have h1 := congrArg Fin.val h
  have h2 := pathSchur_cyc_val a j
  have h3 := pathSchur_cyc_val a k
  have := a.isLt
  have := j.isLt
  have := k.isLt
  exact Fin.ext (by omega)

/-- `ℤ_L = {a} ⊔ (ℤ_L ∖ {a})`, with the second part listed by `cycPathBlock a`. -/
private def pathSchurEquiv {L : ℕ} (a : Fin L) : Fin 1 ⊕ Fin (L - 1) ≃ Fin L :=
  Equiv.ofBijective (Sum.elim (fun _ => a) (cycPathBlock a)) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, ?_⟩
    · rintro (x | x) (y | y) h
      · exact congrArg Sum.inl (Subsingleton.elim _ _)
      · exact absurd h.symm (pathSchur_cyc_ne a y)
      · exact absurd h (pathSchur_cyc_ne a x)
      · exact congrArg Sum.inr (pathSchur_cyc_inj a h)
    · have := a.pos
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega)

private theorem pathSchur_sum_cyc {L : ℕ} (a : Fin L) (f : Fin L → ℂ) :
    ∑ x, f x = f a + ∑ k : Fin (L - 1), f (cycPathBlock a k) := by
  rw [← (pathSchurEquiv a).sum_comp, Fintype.sum_sum_type]
  simp [pathSchurEquiv]


/-- The cycle adjacency between `a` and the path block `a + 1 + k`: it is `1` for the two ends
`k = 0` and `k = L - 2` of the path. -/
private theorem pathSchur_cycleAdj_self {L : ℕ} (a : Fin L) (k : Fin (L - 1)) :
    cycleAdj L a (cycPathBlock a k) =
      (if k.val = 0 then 1 else 0) + (if k.val + 2 = L then 1 else 0) := by
  have h0 := pathSchur_cyc_val a k
  have h1 := pathSchur_mod_cases (a.val + 1) L (by have := a.isLt; omega)
  have h2 := pathSchur_mod_cases ((cycPathBlock a k).val + 1) L
    (by have := (cycPathBlock a k).isLt; omega)
  have := a.isLt
  have := k.isLt
  have e1 : ((cycPathBlock a k).val = (a.val + 1) % L) ↔ k.val = 0 := by omega
  have e2 : (a.val = ((cycPathBlock a k).val + 1) % L) ↔ k.val + 2 = L := by omega
  simp only [cycleAdj, Matrix.of_apply, e1, e2]

/-- The cycle adjacency restricted to the path `ℤ_L ∖ {a}` is the path adjacency. -/
private theorem pathSchur_cycleAdj_path {L : ℕ} (a : Fin L) (j k : Fin (L - 1)) :
    cycleAdj L (cycPathBlock a j) (cycPathBlock a k) = pathAdj (L - 1) j k := by
  have hj := pathSchur_cyc_val a j
  have hk := pathSchur_cyc_val a k
  have h1 := pathSchur_mod_cases ((cycPathBlock a j).val + 1) L
    (by have := (cycPathBlock a j).isLt; omega)
  have h2 := pathSchur_mod_cases ((cycPathBlock a k).val + 1) L
    (by have := (cycPathBlock a k).isLt; omega)
  have := a.isLt
  have := j.isLt
  have := k.isLt
  have e1 : ((cycPathBlock a k).val = ((cycPathBlock a j).val + 1) % L) ↔ j.val + 1 = k.val := by
    omega
  have e2 : ((cycPathBlock a j).val = ((cycPathBlock a k).val + 1) % L) ↔ k.val + 1 = j.val := by
    omega
  simp only [cycleAdj, pathAdj, Matrix.of_apply, e1, e2]
  by_cases hjk : j.val + 1 = k.val
  · have : ¬ k.val + 1 = j.val := by omega
    simp [hjk, this]
  · by_cases hkj : k.val + 1 = j.val
    · simp [hjk, hkj]
    · simp [hjk, hkj]

/-- Entries of the cycle operator. -/
private theorem pathSchur_Hdet_apply (g : ℝ) {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (x y : Fin L) (α β : Fin W) :
    Hdet g V (x, α) (y, β) =
      ((max 1 g : ℝ)⁻¹ : ℂ) * ((g : ℂ) * (cycleAdj L x y * (if α = β then 1 else 0)) +
        (if x = y then V x α β else 0)) := by
  by_cases h1 : α = β <;> by_cases h2 : x = y <;>
    simp [Hdet, blockDiagOp, Matrix.kroneckerMap_apply, h1, h2, mul_add]

/-- Entries of the block path operator with zero shifts. -/
private theorem pathSchur_pathOp_apply (g : ℝ) {W n : ℕ} (V : Fin n → Matrix (Fin W) (Fin W) ℂ)
    (x y : Fin n) (α β : Fin W) :
    pathOp g V 0 0 (x, α) (y, β) =
      ((max 1 g : ℝ)⁻¹ : ℂ) * ((g : ℂ) * (pathAdj n x y * (if α = β then 1 else 0)) +
        (if x = y then V x α β else 0)) := by
  by_cases h1 : α = β <;> by_cases h2 : x = y <;>
    simp [pathOp, blockDiagOp, Matrix.kroneckerMap_apply, h1, h2, mul_add]

/-- The coupling of `a` to the path `ℤ_L ∖ {a}` in `H - E`. -/
private theorem pathSchur_coupling (g : ℝ) {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (E : ℝ) (a : Fin L) (k : Fin (L - 1)) (γ β : Fin W) :
    (Hdet g V - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))
        (a, γ) (cycPathBlock a k, β) =
      ((g / max 1 g : ℝ) : ℂ) *
        (((if k.val = 0 then 1 else 0) + (if k.val + 2 = L then 1 else 0)) *
          (if γ = β then 1 else 0)) := by
  have hne : a ≠ cycPathBlock a k := (pathSchur_cyc_ne a k).symm
  have hm : (max 1 g : ℝ) ≠ 0 := (lt_of_lt_of_le one_pos (le_max_left 1 g)).ne'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, hne, false_and,
    ite_false, smul_zero, sub_zero, pathSchur_Hdet_apply, pathSchur_cycleAdj_self, add_zero]
  push_cast
  field_simp

/-- The block of `H - E` on the path `ℤ_L ∖ {a}` is the Dirichlet path operator minus `E`. -/
private theorem pathSchur_path_block (g : ℝ) {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (E : ℝ) (a : Fin L) (j k : Fin (L - 1)) (δ β : Fin W) :
    (Hdet g V - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))
        (cycPathBlock a j, δ) (cycPathBlock a k, β) =
      (pathOp g (V ∘ cycPathBlock a) 0 0 -
        (E : ℂ) • (1 : Matrix (Fin (L - 1) × Fin W) (Fin (L - 1) × Fin W) ℂ)) (j, δ) (k, β) := by
  have hiff : cycPathBlock a j = cycPathBlock a k ↔ j = k :=
    ⟨pathSchur_cyc_inj a, fun h => h ▸ rfl⟩
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, hiff,
    pathSchur_Hdet_apply, pathSchur_pathOp_apply, pathSchur_cycleAdj_path, Function.comp]


/-- (E.15) [eq:c-cycle-Schur]: `G_{ab} = -(g/max{1,g}) G_{aa} (G^{(a)}_{a+1,b} + G^{(a)}_{a-1,b})`
for the cycle of `L ≥ 3` blocks, with `G^{(a)}` the resolvent of the Dirichlet path
`ℤ_L ∖ {a}`, for every real `g`. -/
theorem cycle_schur' (g : ℝ) {W L : ℕ} (hL : 3 ≤ L)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (E : ℝ) (a : Fin L)
    (hdet : (pathOp g (V ∘ cycPathBlock a) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin (L - 1) × Fin W) (Fin (L - 1) × Fin W) ℂ)).det ≠ 0)
    (j : Fin (L - 1)) :
    blockOf (resolventMat (Hdet g V) E) a (cycPathBlock a j) =
      -((g / max 1 g : ℝ) : ℂ) • (blockOf (resolventMat (Hdet g V) E) a a *
        (blockOf (resolventMat (pathOp g (V ∘ cycPathBlock a) 0 0) E) ⟨0, by omega⟩ j +
          blockOf (resolventMat (pathOp g (V ∘ cycPathBlock a) 0 0) E) ⟨L - 2, by omega⟩ j)) := by
  set M := Hdet g V - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) with hM
  set D := pathOp g (V ∘ cycPathBlock a) 0 0 -
    (E : ℂ) • (1 : Matrix (Fin (L - 1) × Fin W) (Fin (L - 1) × Fin W) ℂ) with hD
  have hGdef : resolventMat (Hdet g V) E = M⁻¹ := rfl
  have hDdef : resolventMat (pathOp g (V ∘ cycPathBlock a) 0 0) E = D⁻¹ := rfl
  rw [hGdef, hDdef]
  by_cases hMd : IsUnit M.det
  swap
  · have hz : ∀ x y : Fin L,
        blockOf (0 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) x y = 0 := by
      intro x y
      ext
      simp [blockOf]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hMd]
    simp only [hz, zero_mul, smul_zero]
  have hGM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hMd
  have hDD : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hcoup : ∀ (k : Fin (L - 1)) (γ β : Fin W), M (a, γ) (cycPathBlock a k, β) =
      ((g / max 1 g : ℝ) : ℂ) *
        (((if k.val = 0 then 1 else 0) + (if k.val + 2 = L then 1 else 0)) *
          (if γ = β then 1 else 0)) :=
    fun k γ β => pathSchur_coupling g V E a k γ β
  have hblock : ∀ (j k : Fin (L - 1)) (δ β : Fin W),
      M (cycPathBlock a j, δ) (cycPathBlock a k, β) = D (j, δ) (k, β) :=
    fun j k δ β => pathSchur_path_block g V E a j k δ β
  ext α β
  -- the row `(a, α)` of `G` on the path blocks
  set u : Fin (L - 1) × Fin W → ℂ := fun x => M⁻¹ (a, α) (cycPathBlock a x.1, x.2) with hu
  set c : Fin (L - 1) × Fin W → ℂ := fun x =>
    -(((g / max 1 g : ℝ) : ℂ) *
      (((if x.1.val = 0 then 1 else 0) + (if x.1.val + 2 = L then 1 else 0)) *
        M⁻¹ (a, α) (a, x.2))) with hc
  have hrow : Matrix.vecMul u D = c := by
    ext ⟨k, β'⟩
    have h1 := congrFun (congrFun hGM (a, α)) (cycPathBlock a k, β')
    rw [Matrix.mul_apply, Matrix.one_apply_ne (by simp [(pathSchur_cyc_ne a k).symm])] at h1
    rw [Fintype.sum_prod_type, pathSchur_sum_cyc a] at h1
    simp only [hcoup, hblock] at h1
    simp only [Matrix.vecMul, dotProduct, Fintype.sum_prod_type, hu, hc]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
    linear_combination h1
  have hsol : u = Matrix.vecMul c D⁻¹ := by
    calc u = Matrix.vecMul u (D * D⁻¹) := by rw [hDD, Matrix.vecMul_one]
      _ = Matrix.vecMul (Matrix.vecMul u D) D⁻¹ := by rw [Matrix.vecMul_vecMul]
      _ = Matrix.vecMul c D⁻¹ := by rw [hrow]
  have h2 := congrFun hsol (j, β)
  simp only [hu, Matrix.vecMul, dotProduct, Fintype.sum_prod_type, hc] at h2
  have hk : ∀ x_1 : Fin W, ∑ x : Fin (L - 1),
      -(((g / max 1 g : ℝ) : ℂ) * (((if x.val = 0 then 1 else 0) +
        (if x.val + 2 = L then 1 else 0)) * M⁻¹ (a, α) (a, x_1))) * D⁻¹ (x, x_1) (j, β) =
      -(((g / max 1 g : ℝ) : ℂ) * M⁻¹ (a, α) (a, x_1)) *
        (D⁻¹ (⟨0, by omega⟩, x_1) (j, β) + D⁻¹ (⟨L - 2, by omega⟩, x_1) (j, β)) := by
    intro x_1
    have e : ∀ x : Fin (L - 1),
        -(((g / max 1 g : ℝ) : ℂ) * (((if x.val = 0 then 1 else 0) +
          (if x.val + 2 = L then 1 else 0)) * M⁻¹ (a, α) (a, x_1))) * D⁻¹ (x, x_1) (j, β) =
        -(((g / max 1 g : ℝ) : ℂ) * M⁻¹ (a, α) (a, x_1)) *
            (if x = (⟨0, by omega⟩ : Fin (L - 1)) then D⁻¹ (x, x_1) (j, β) else 0) +
          -(((g / max 1 g : ℝ) : ℂ) * M⁻¹ (a, α) (a, x_1)) *
            (if x = (⟨L - 2, by omega⟩ : Fin (L - 1)) then D⁻¹ (x, x_1) (j, β) else 0) := by
      intro x
      have hx := x.isLt
      have hx0 : x = (⟨0, by omega⟩ : Fin (L - 1)) ↔ x.val = 0 := by rw [Fin.ext_iff]
      have hx2 : x = (⟨L - 2, by omega⟩ : Fin (L - 1)) ↔ x.val + 2 = L := by
        rw [Fin.ext_iff]
        simp only
        omega
      simp only [hx0, hx2]
      by_cases h0 : x.val = 0
      · have h2 : ¬ x.val + 2 = L := by omega
        simp only [eq_true h0, eq_false h2, ↓reduceIte]
        ring
      · by_cases h2 : x.val + 2 = L
        · simp only [eq_false h0, eq_true h2, ↓reduceIte]
          ring
        · simp only [eq_false h0, eq_false h2, ↓reduceIte]
          ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    ring
  rw [Finset.sum_comm] at h2
  simp only [hk] at h2
  simp only [blockOf, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.add_apply,
    smul_eq_mul]
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  ring

end LSBA
