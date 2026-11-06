import LSBA.Transfer.Recurrence

/-!
# Block path operators and the transfer recurrence

The Dirichlet block path operator with Hermitian endpoint shifts (8.5) [up:eq:shifted-resolvent],
the adjunction of its resolvent blocks, and the transfer recurrence for the column `f_j = G(j, 0)u`
for every `g > 0` (proof of Proposition 8.4(i) [up:prop:conversion]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Adjacency matrix of the path `0 - 1 - ⋯ - (n-1)` (no wraparound). -/
def pathAdj (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if a.val + 1 = b.val ∨ b.val + 1 = a.val then 1 else 0

/-- The Dirichlet block path operator with Hermitian endpoint shifts, (8.5)
[up:eq:shifted-resolvent]: `(g P_n ⊗ I_W + diag V) / max{1,g} + ι₀ L₀ ι₀* + ι_{n-1} R₀ ι_{n-1}*`. -/
def pathOp (g : ℝ) {W n : ℕ} (V : Fin n → Matrix (Fin W) (Fin W) ℂ)
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ :=
  ((max 1 g : ℝ)⁻¹ : ℂ) • ((g : ℂ) • (pathAdj n ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) +
      blockDiagOp V) +
    blockDiagOp (fun a : Fin n => (if a.val = 0 then L₀ else 0) + (if a.val + 1 = n then R₀ else 0))

private theorem path_pathAdj_isHermitian (n : ℕ) : (pathAdj n).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, pathAdj, Matrix.of_apply]
  by_cases h : a.val + 1 = b.val ∨ b.val + 1 = a.val
  · simp [h, or_comm]
  · have h' : ¬ (b.val + 1 = a.val ∨ a.val + 1 = b.val) := fun h2 => h (or_comm.mp h2)
    simp [h, h']

theorem pathOp_isHermitian (g : ℝ) {W n : ℕ} {V : Fin n → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ a, (V a).IsHermitian) {L₀ R₀ : Matrix (Fin W) (Fin W) ℂ} (hL₀ : L₀.IsHermitian)
    (hR₀ : R₀.IsHermitian) : (pathOp g V L₀ R₀).IsHermitian := by
  have hK : (pathAdj n ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, (path_pathAdj_isHermitian n).eq,
      Matrix.conjTranspose_one]
  have hs : ∀ a : Fin n, ((if a.val = 0 then L₀ else 0) +
      (if a.val + 1 = n then R₀ else 0)).IsHermitian := by
    intro a
    refine Matrix.IsHermitian.add ?_ ?_
    · split_ifs
      · exact hL₀
      · exact Matrix.isHermitian_zero
    · split_ifs
      · exact hR₀
      · exact Matrix.isHermitian_zero
  refine Matrix.IsHermitian.add ?_ (blockDiagOp_isHermitian hs)
  have h1 : ((g : ℂ) • (pathAdj n ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) + blockDiagOp V).IsHermitian := by
    refine Matrix.IsHermitian.add ?_ (blockDiagOp_isHermitian hV)
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hK.eq, Complex.star_def,
      Complex.conj_ofReal]
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, h1.eq, Complex.star_def, map_inv₀,
    Complex.conj_ofReal]

/-- `G(b, a) = G(a, b)*` for a Hermitian matrix at a real energy. -/
theorem blockOf_resolventMat_swap {W L : ℕ} {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hA : A.IsHermitian) (E : ℝ) (a b : Fin L) :
    blockOf (resolventMat A E) b a = (blockOf (resolventMat A E) a b)ᴴ := by
  have hM : (A - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))ᴴ =
      A - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) := by
    rw [Matrix.conjTranspose_sub, hA.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_ofReal]
  have hG : (resolventMat A E)ᴴ = resolventMat A E := by
    unfold resolventMat
    rw [Matrix.conjTranspose_nonsing_inv, hM]
  ext α β
  have := congrFun (congrFun hG (b, α)) (a, β)
  simp only [Matrix.conjTranspose_apply] at this
  simp only [blockOf, Matrix.of_apply, Matrix.conjTranspose_apply]
  exact this.symm

/-- `f_j = G(j, 0) u` for `j ≤ n` and the right boundary value
`f_{n+1} = (max{1,g}/g) R₀ f_n` (proof of Proposition 8.4(i) [up:prop:conversion]). -/
def pathCol (g : ℝ) {W n : ℕ} (V : Fin (n + 1) → Matrix (Fin W) (Fin W) ℂ)
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ) (u : Fin W → ℂ) (j : ℕ) : Fin W → ℂ :=
  if h : j ≤ n then blockOf (resolventMat (pathOp g V L₀ R₀) E) ⟨j, by omega⟩ 0 *ᵥ u
  else if j = n + 1 then
    (((max 1 g / g : ℝ) : ℂ) • R₀) *ᵥ (blockOf (resolventMat (pathOp g V L₀ R₀) E) (Fin.last n) 0 *ᵥ u)
  else 0

private theorem path_mulVec_apply {g : ℝ} {W n : ℕ} (V : Fin n → Matrix (Fin W) (Fin W) ℂ)
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (F : Fin n × Fin W → ℂ) (i : Fin n) (α : Fin W) :
    (pathOp g V L₀ R₀ *ᵥ F) (i, α) =
      ((max 1 g : ℝ)⁻¹ : ℂ) * ((g : ℂ) * ∑ k : Fin n, (pathAdj n) i k * F (k, α) +
        (V i *ᵥ fun γ => F (i, γ)) α) +
      (((if i.val = 0 then L₀ else 0) + (if i.val + 1 = n then R₀ else 0)) *ᵥ
        fun γ => F (i, γ)) α := by
  have h1 : ((pathAdj n ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *ᵥ F) (i, α) =
      ∑ k : Fin n, (pathAdj n) i k * F (k, α) := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
  have h2 : ∀ B : Fin n → Matrix (Fin W) (Fin W) ℂ,
      (blockDiagOp B *ᵥ F) (i, α) = (B i *ᵥ fun γ => F (i, γ)) α := by
    intro B
    simp [Matrix.mulVec, dotProduct, blockDiagOp, Fintype.sum_prod_type]
  unfold pathOp
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.smul_apply, Pi.add_apply, Pi.smul_apply, h1, h2, h2]
  simp

private theorem path_transferMat_mulVec_pairVec {W : ℕ} (g : ℝ) (z : ℂ)
    (V : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ) :
    transferMat g z V *ᵥ pairVec x y = pairVec (z • x - y - ((g : ℂ)⁻¹) • (V *ᵥ x)) x := by
  ext ⟨a, α⟩
  fin_cases a
  · simp [transferMat, transferFree, pairVec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply,
      Fin.sum_univ_two]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, mul_assoc, ← Finset.mul_sum]
    ring
  · simp [transferMat, transferFree, pairVec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply,
      Fin.sum_univ_two]


private theorem path_adj_sum {n : ℕ} (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (c : ℕ → ℂ) :
    ∑ k : Fin (n + 1), (pathAdj (n + 1)) ⟨i, by omega⟩ k * c k.val =
      c (i - 1) + (if i + 1 ≤ n then c (i + 1) else 0) := by
  have h1 : ∀ k : Fin (n + 1), (pathAdj (n + 1)) ⟨i, by omega⟩ k * c k.val =
      (if k.val = i - 1 then c k.val else 0) + (if k.val = i + 1 then c k.val else 0) := by
    intro k
    simp only [pathAdj, Matrix.of_apply]
    by_cases h2 : k.val = i - 1
    · have h3 : k.val + 1 = i := by omega
      have h4 : k.val ≠ i + 1 := by omega
      rw [if_pos (Or.inr h3), if_pos h2, if_neg h4]
      simp
    · by_cases h5 : k.val = i + 1
      · have h7 : k.val ≠ i - 1 := h2
        rw [if_pos (Or.inl h5.symm), if_neg h7, if_pos h5]
        simp
      · have h6 : ¬ (i + 1 = k.val ∨ k.val + 1 = i) := by omega
        rw [if_neg h6, if_neg h2, if_neg h5]
        simp
  simp only [h1, Finset.sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun k => if k = i - 1 then c k else 0) (n + 1),
    Fin.sum_univ_eq_sum_range (fun k => if k = i + 1 then c k else 0) (n + 1)]
  rw [Finset.sum_ite_eq' (Finset.range (n + 1)) (i - 1) c,
    Finset.sum_ite_eq' (Finset.range (n + 1)) (i + 1) c]
  have : i - 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [if_pos this]
  by_cases h : i + 1 ≤ n
  · rw [if_pos (Finset.mem_range.mpr (by omega)), if_pos h]
  · rw [if_neg (by simpa [Finset.mem_range] using h), if_neg h]

/-- The transfer recurrence for every `g > 0` (proof of Proposition 8.4(i)
[up:prop:conversion]): `(f_{i-1}, f_i) = T_i (f_i, f_{i+1})` for `1 ≤ i ≤ n`, with `T_i` of
(8.9) [eq:c-transfer]. -/
theorem pathCol_step {g : ℝ} (hg : 0 < g) {W n : ℕ} (V : Fin (n + 1) → Matrix (Fin W) (Fin W) ℂ)
    (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ) (u : Fin W → ℂ) (i : ℕ) (hi : 1 ≤ i)
    (hin : i ≤ n) :
    pairVec (pathCol g V L₀ R₀ E u (i - 1)) (pathCol g V L₀ R₀ E u i) =
      transferMat g ((max 1 g * E / g : ℝ) : ℂ) (V ⟨i, by omega⟩) *ᵥ
        pairVec (pathCol g V L₀ R₀ E u i) (pathCol g V L₀ R₀ E u (i + 1)) := by
  have hm : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left 1 g)
  have hmc : ((max 1 g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hgc : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  rw [path_transferMat_mulVec_pairVec]
  by_cases hdet : IsUnit (pathOp g V L₀ R₀ - (E : ℂ) • (1 : Matrix (Fin (n + 1) × Fin W)
      (Fin (n + 1) × Fin W) ℂ)).det
  · -- Row `i` of `(H - E) G ι₀ u = ι₀ u`
    set H := pathOp g V L₀ R₀ with hH
    set G := resolventMat H E with hG
    let e : Fin (n + 1) × Fin W → ℂ := fun p => if p.1 = 0 then u p.2 else 0
    have hF : ∀ j (hj : j ≤ n), pathCol g V L₀ R₀ E u j =
        fun γ => (G *ᵥ e) (⟨j, by omega⟩, γ) := by
      intro j hj
      funext α
      simp [pathCol, hj, e, hG, hH, Matrix.mulVec, dotProduct, blockOf, Fintype.sum_prod_type]
    have hrow : ∀ α, (H *ᵥ (G *ᵥ e)) (⟨i, by omega⟩, α) -
        (E : ℂ) * (G *ᵥ e) (⟨i, by omega⟩, α) = 0 := by
      intro α
      have h1 : (H - (E : ℂ) • (1 : Matrix (Fin (n + 1) × Fin W) (Fin (n + 1) × Fin W) ℂ)) *ᵥ
          (G *ᵥ e) = e := by
        rw [Matrix.mulVec_mulVec, hG, resolventMat, Matrix.mul_nonsing_inv _ hdet,
          Matrix.one_mulVec]
      have h2 := congrFun h1 (⟨i, by omega⟩, α)
      have h3 : e (⟨i, by omega⟩, α) = 0 := by
        simp only [e]
        rw [if_neg]
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      rw [h3, Matrix.sub_mulVec, Pi.sub_apply, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.smul_apply] at h2
      simpa using h2
    have hFk : ∀ (α : Fin W) (k : Fin (n + 1)),
        (G *ᵥ e) (k, α) = pathCol g V L₀ R₀ E u k.val α := by
      intro α k
      rw [hF k.val (by omega)]
    have hlast : pathCol g V L₀ R₀ E u (n + 1) =
        (((max 1 g / g : ℝ) : ℂ) • R₀) *ᵥ pathCol g V L₀ R₀ E u n := by
      simp only [pathCol, le_refl, dite_true, Nat.not_succ_le_self, dite_false, if_true]
      rfl
    have hE : ∀ α, ((max 1 g : ℝ) : ℂ)⁻¹ * ((g : ℂ) * (pathCol g V L₀ R₀ E u (i - 1) α +
        pathCol g V L₀ R₀ E u (i + 1) α) + (V ⟨i, by omega⟩ *ᵥ pathCol g V L₀ R₀ E u i) α) -
        (E : ℂ) * pathCol g V L₀ R₀ E u i α = 0 := by
      intro α
      have h1 := hrow α
      rw [hH, path_mulVec_apply] at h1
      have hsum := path_adj_sum (n := n) i hi hin (fun j => pathCol g V L₀ R₀ E u j α)
      beta_reduce at hsum
      simp only [hFk α] at h1
      rw [hsum] at h1
      have hv : (fun γ => (G *ᵥ e) (⟨i, by omega⟩, γ)) = pathCol g V L₀ R₀ E u i := by
        rw [hF i hin]
      rw [hv] at h1
      rcases Nat.lt_or_ge i n with hlt | hge
      · have hR : ((if i = 0 then L₀ else 0) + (if i + 1 = n + 1 then R₀ else 0)) = 0 := by
          rw [if_neg (by omega), if_neg (by omega), add_zero]
        rw [hR, if_pos (by omega), Matrix.zero_mulVec] at h1
        simpa using h1
      · have hin' : i = n := le_antisymm hin hge
        subst hin'
        have hR : ((if i = 0 then L₀ else 0) + (if i + 1 = i + 1 then R₀ else 0)) = R₀ := by
          rw [if_neg (by omega), if_pos rfl, zero_add]
        rw [hR, if_neg (by omega)] at h1
        have h3 : (R₀ *ᵥ pathCol g V L₀ R₀ E u i) α =
            (g : ℂ) / ((max 1 g : ℝ) : ℂ) * pathCol g V L₀ R₀ E u (i + 1) α := by
          rw [hlast, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
          push_cast
          field_simp
        rw [h3] at h1
        linear_combination h1
    have hfin : pathCol g V L₀ R₀ E u (i - 1) =
        ((max 1 g * E / g : ℝ) : ℂ) • pathCol g V L₀ R₀ E u i - pathCol g V L₀ R₀ E u (i + 1) -
          ((g : ℂ)⁻¹) • (V ⟨i, by omega⟩ *ᵥ pathCol g V L₀ R₀ E u i) := by
      funext α
      have h := hE α
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      field_simp
      field_simp at h
      linear_combination h
    rw [hfin]
  · have hG0 : resolventMat (pathOp g V L₀ R₀) (E : ℂ) = 0 := by
      unfold resolventMat
      exact Matrix.nonsing_inv_apply_not_isUnit _ hdet
    have hf : ∀ j, pathCol g V L₀ R₀ E u j = 0 := by
      intro j
      have hb : ∀ a b : Fin (n + 1), blockOf (0 : Matrix (Fin (n + 1) × Fin W)
          (Fin (n + 1) × Fin W) ℂ) a b = 0 := by
        intro a b
        ext
        simp [blockOf]
      simp [pathCol, hG0, hb]
    simp [hf]

/-- `T_1 ⋯ T_n` maps the right boundary pair `(f_n, f_{n+1})` to `(f_0, f_1)`. -/
theorem pathCol_transferProd {g : ℝ} (hg : 0 < g) {W n : ℕ}
    (V : Fin (n + 1) → Matrix (Fin W) (Fin W) ℂ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (u : Fin W → ℂ) :
    pairVec (pathCol g V L₀ R₀ E u 0) (pathCol g V L₀ R₀ E u 1) =
      transferProd g ((max 1 g * E / g : ℝ) : ℂ) (fun k => V ⟨n - k, by omega⟩) n *ᵥ
        pairVec (pathCol g V L₀ R₀ E u n) (pathCol g V L₀ R₀ E u (n + 1)) := by
  have key : ∀ j, j ≤ n →
      pairVec (pathCol g V L₀ R₀ E u (n - j)) (pathCol g V L₀ R₀ E u (n - j + 1)) =
        transferProd g ((max 1 g * E / g : ℝ) : ℂ) (fun k => V ⟨n - k, by omega⟩) j *ᵥ
          pairVec (pathCol g V L₀ R₀ E u n) (pathCol g V L₀ R₀ E u (n + 1)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp [transferProd]
    | succ j ih =>
      intro hj
      have h1 := pathCol_step hg V L₀ R₀ E u (n - j) (by omega) (by omega)
      have h2 : n - j - 1 = n - (j + 1) := by omega
      have h3 : n - (j + 1) + 1 = n - j := by omega
      rw [h2] at h1
      rw [h3, h1, transferProd, ← Matrix.mulVec_mulVec, ← ih (by omega)]
  simpa using key n le_rfl

end LSBA
