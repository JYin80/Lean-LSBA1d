import LSBA.Spectral.Mask
import LSBA.Volume.LocalComparison

/-!
# Block-masked resolvents

For a set `Λ` of blocks of `ℂ^L ⊗ ℂ^W`, the masked resolvent
`G_Λ(E) = (1_Λ (H - E) 1_Λ + 1_{Λᶜ})⁻¹`. Its `Λ × Λ` blocks are those of the restricted resolvent
(8.1) [up:eq:local-resolvent] of the restricted operator `H_Λ` of Section 8.1
[sec:fr-concentration], and
`G_{ℤ_L} = (H - E)⁻¹`. Deleting one block `x ∈ Λ` gives the one-step expansion and the Schur
complement at `x` ([PSSS, (2.5), (2.7)]) behind [PSSS, Theorem 1], which the proof of Theorem 3.1
[thm:strong-upper] cites.
-/

open Finset
open scoped Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- A double sum over indices of `Fin L × Fin W` restricted to two sets of blocks. -/
private theorem blockMask_sum_pairs {W L : ℕ} (A B : Finset (Fin L))
    (F : Fin L × Fin W → Fin L × Fin W → ℂ) :
    ∑ u, ∑ w, (if u.1 ∈ A ∧ w.1 ∈ B then F u w else 0) =
      ∑ a ∈ A, ∑ b ∈ B, ∑ γ, ∑ δ, F (a, γ) (b, δ) := by
  simp only [Fintype.sum_prod_type]
  have h1 : ∀ a : Fin L, ∑ γ : Fin W, ∑ b : Fin L, ∑ δ : Fin W,
      (if a ∈ A ∧ b ∈ B then F (a, γ) (b, δ) else 0) =
      ∑ b : Fin L, ∑ γ : Fin W, ∑ δ : Fin W,
        (if a ∈ A ∧ b ∈ B then F (a, γ) (b, δ) else 0) :=
    fun a => Finset.sum_comm
  simp only [h1]
  have h2 : ∀ a b : Fin L, ∑ γ : Fin W, ∑ δ : Fin W,
      (if a ∈ A ∧ b ∈ B then F (a, γ) (b, δ) else 0) =
      if a ∈ A ∧ b ∈ B then ∑ γ : Fin W, ∑ δ : Fin W, F (a, γ) (b, δ) else 0 := by
    intro a b
    split_ifs <;> simp
  simp only [h2]
  have h3 : ∀ a : Fin L, (∑ b : Fin L, if a ∈ A ∧ b ∈ B then
      ∑ γ : Fin W, ∑ δ : Fin W, F (a, γ) (b, δ) else 0) =
      if a ∈ A then ∑ b ∈ B, ∑ γ : Fin W, ∑ δ : Fin W, F (a, γ) (b, δ) else 0 := by
    intro a
    by_cases ha : a ∈ A
    · simp [ha, Finset.sum_ite_mem]
    · simp [ha]
  simp only [h3, Finset.sum_ite_mem, Finset.univ_inter]

/-- The conjugate transpose of a block is the transposed block of the conjugate transpose. -/
private theorem blockMask_blockOf_conjTranspose {W L : ℕ}
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    (blockOf X a b)ᴴ = blockOf Xᴴ b a := by
  ext α β
  simp [blockOf, Matrix.conjTranspose_apply]

/-- `H - E` is Hermitian for Hermitian `H` and real `E`. -/
private theorem blockMask_shift_isHermitian {W L : ℕ}
    {H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hH : H.IsHermitian) (E : ℝ) :
    (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)).IsHermitian :=
  hH.sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))

/-- Off the diagonal blocks, `H - E` agrees with `H`. -/
private theorem blockMask_shift_apply_ne {W L : ℕ}
    (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (E : ℝ) {a b : Fin L} (hab : a ≠ b)
    (α β : Fin W) :
    (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) (a, α) (b, β) =
      H (a, α) (b, β) := by
  simp [hab]

/-- The blocks of `Λ` other than `x` are those of `Λ ∖ {x}`. -/
private theorem blockMask_sdiff {W L : ℕ} (Λ : Finset (Fin L)) (x : Fin L) :
    ({p : Fin L × Fin W | p.1 ∈ Λ} \ {p | p.1 ∈ ({x} : Finset (Fin L))}) =
      {p | p.1 ∈ Λ.erase x} := by
  ext p
  simp [Finset.mem_erase, and_comm]

/-- The `(x, x)` block of the matrix inside the Schur complement at `x`. -/
private theorem blockMask_schur_block {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (Λ : Finset (Fin L)) (x : Fin L) (E : ℝ) :
    blockOf (Matrix.of fun r s => (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))
        r s - ∑ u, ∑ w, if u.1 ∈ Λ.erase x ∧ w.1 ∈ Λ.erase x then
          (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) r u *
            (maskMat {p | p.1 ∈ Λ.erase x}
              (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)))⁻¹ u w *
            (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) w s else 0) x x =
      blockOf H x x - (E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - ∑ c ∈ Λ.erase x,
        ∑ c' ∈ Λ.erase x, blockOf H x c * blockOf (maskMat {p | p.1 ∈ Λ.erase x}
          (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)))⁻¹ c c' *
          blockOf H c' x := by
  ext α β
  simp only [blockOf, Matrix.of_apply, Matrix.sub_apply]
  rw [blockMask_sum_pairs]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.of_apply]
  have hd : ((E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) (x, α) (x, β) =
      ((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) α β := by
    simp [Matrix.one_apply]
  rw [hd]
  congr 1
  refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun c' hc' => ?_
  have hcx : c ≠ x := (Finset.mem_erase.mp hc).1
  have hc'x : c' ≠ x := (Finset.mem_erase.mp hc').1
  have h1 : ∀ γ, ((E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) (x, α) (c, γ) = 0 :=
    fun γ => by simp [Ne.symm hcx]
  have h2 : ∀ δ, ((E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) (c', δ) (x, β) = 0 :=
    fun δ => by simp [hc'x]
  simp only [h1, h2, sub_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [Finset.sum_mul]

/-- The inverse of a matrix masked to a single block is the inverse of that block. -/
private theorem blockMask_inv_oneBlock {W L : ℕ} (Z : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x : Fin L) (α β : Fin W) :
    (maskMat {p | p.1 ∈ ({x} : Finset (Fin L))} Z)⁻¹ (x, α) (x, β) =
      (blockOf Z x x)⁻¹ α β := by
  have hrow : ∀ p k : Fin L × Fin W, maskMat {p | p.1 ∈ ({x} : Finset (Fin L))} Z p k =
      if p.1 = x ∧ k.1 = x then Z p k else if p = k then 1 else 0 := by
    intro p k
    simp [maskMat]
  by_cases hB : (blockOf Z x x).det = 0
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hB
    have hdet : (maskMat {p | p.1 ∈ ({x} : Finset (Fin L))} Z).det = 0 := by
      refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun p => if p.1 = x then v p.2 else 0, ?_, ?_⟩
      · intro h
        apply hv0
        ext j
        have := congrFun h (x, j)
        simpa using this
      · ext p
        rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
        by_cases hp : p.1 = x
        · rw [Finset.sum_eq_single x]
          · have := congrFun hv p.2
            simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
            simp only [hrow, hp, true_and, ite_true, Pi.zero_apply]
            refine Eq.trans ?_ this
            refine Finset.sum_congr rfl fun γ _ => ?_
            simp only [blockOf, Matrix.of_apply]
            rw [show p = (x, p.2) from Prod.ext hp rfl]
          · intro c _ hc
            simp [hc]
          · simp
        · simp only [hrow, hp, false_and, ite_false, Pi.zero_apply]
          rw [Finset.sum_eq_single p.1]
          · rw [Finset.sum_eq_single p.2]
            · simp [hp]
            · intro γ _ hγ
              have : p ≠ (p.1, γ) := fun h => hγ (congrArg Prod.snd h).symm
              simp [this]
            · simp
          · intro c _ hc
            refine Finset.sum_eq_zero fun γ _ => ?_
            have : p ≠ (c, γ) := fun h => hc (congrArg Prod.fst h).symm
            simp [this]
          · simp
    have hu : ¬ IsUnit (maskMat {p | p.1 ∈ ({x} : Finset (Fin L))} Z).det := by
      rw [hdet]; exact not_isUnit_zero
    have hBu : ¬ IsUnit (blockOf Z x x).det := by
      rw [hB]; exact not_isUnit_zero
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hu, Matrix.nonsing_inv_apply_not_isUnit _ hBu]
    simp
  · have hBu : IsUnit (blockOf Z x x).det := isUnit_iff_ne_zero.mpr hB
    have hNrow : ∀ k q : Fin L × Fin W,
        maskMat {p | p.1 ∈ ({x} : Finset (Fin L))}
          (Matrix.of fun p q : Fin L × Fin W => (blockOf Z x x)⁻¹ p.2 q.2) k q =
        if k.1 = x ∧ q.1 = x then (blockOf Z x x)⁻¹ k.2 q.2 else if k = q then 1 else 0 := by
      intro k q
      simp [maskMat]
    have hMN : maskMat {p | p.1 ∈ ({x} : Finset (Fin L))} Z *
        maskMat {p | p.1 ∈ ({x} : Finset (Fin L))}
          (Matrix.of fun p q : Fin L × Fin W => (blockOf Z x x)⁻¹ p.2 q.2) = 1 := by
      ext p q
      by_cases hp : p.1 = x
      · rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single x]
        · by_cases hq : q.1 = x
          · have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv _ hBu) p.2) q.2
            rw [Matrix.mul_apply, Matrix.one_apply] at h1
            have hpq : p = q ↔ p.2 = q.2 := by rw [Prod.ext_iff]; simp [hp, hq]
            simp only [hrow, hNrow, hp, hq, and_self, ite_true, Matrix.one_apply, hpq]
            rw [← h1]
            refine Finset.sum_congr rfl fun γ _ => ?_
            simp only [blockOf, Matrix.of_apply]
            rw [show p = (x, p.2) from Prod.ext hp rfl]
          · have hpq : p ≠ q := fun h => hq (h ▸ hp)
            simp only [hrow, hNrow, hp, hq, and_false, ite_false, and_true, ite_true,
              Matrix.one_apply, hpq]
            refine Finset.sum_eq_zero fun γ _ => ?_
            have : ((x, γ) : Fin L × Fin W) ≠ q := fun h => hq (h ▸ rfl)
            simp [this]
        · intro c _ hc
          refine Finset.sum_eq_zero fun γ _ => ?_
          have : p ≠ (c, γ) := fun h => hc ((congrArg Prod.fst h).symm.trans hp)
          rw [hrow p (c, γ)]
          simp [hc, this]
        · simp
      · have hrow' : ∀ k : Fin L × Fin W, maskMat {p | p.1 ∈ ({x} : Finset (Fin L))} Z p k =
            if p = k then 1 else 0 := by
          intro k
          rw [hrow]
          simp [hp]
        simp only [Matrix.mul_apply, hrow', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true]
        rw [hNrow]
        simp [hp, Matrix.one_apply]
    rw [Matrix.inv_eq_right_inv hMN, hNrow]
    simp

/-- The masked resolvent `G_Λ(E) = (1_Λ (H - E) 1_Λ + 1_{Λᶜ})⁻¹` for a set `Λ` of blocks. -/
def maskRes {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (Λ : Finset (Fin L))
    (E : ℝ) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  (maskMat {p | p.1 ∈ Λ} (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)))⁻¹

/-- `G_{ℤ_L}(E) = (H - E)⁻¹`. -/
theorem maskRes_univ {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (E : ℝ) :
    maskRes H univ E = resolventMat H E := by
  have hS : ({p : Fin L × Fin W | p.1 ∈ (univ : Finset (Fin L))} : Set (Fin L × Fin W)) =
      Set.univ := by
    ext p
    simp
  unfold maskRes resolventMat
  rw [hS, maskMat_univ]

/-- `G_Λ(E)` is Hermitian for Hermitian `H` and real `E`. -/
theorem maskRes_isHermitian {W L : ℕ} {H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hH : H.IsHermitian) (Λ : Finset (Fin L)) (E : ℝ) : (maskRes H Λ E).IsHermitian := by
  unfold maskRes
  exact Matrix.IsHermitian.inv (maskMat_isHermitian (blockMask_shift_isHermitian hH E) _)

/-- The self-energy of block `x` in `Λ`:
`Σ_x = Σ_{c, c' ∈ Λ ∖ {x}} H_{xc} G_{Λ∖{x}}(c, c') H_{c'x}`. -/
def selfEnergy {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (Λ : Finset (Fin L))
    (x : Fin L) (E : ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  ∑ c ∈ Λ.erase x, ∑ c' ∈ Λ.erase x,
    blockOf H x c * blockOf (maskRes H (Λ.erase x) E) c c' * blockOf H c' x

/-- The self-energy is Hermitian for Hermitian `H` and real `E`. -/
theorem selfEnergy_isHermitian {W L : ℕ} {H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hH : H.IsHermitian) (Λ : Finset (Fin L)) (x : Fin L) (E : ℝ) :
    (selfEnergy H Λ x E).IsHermitian := by
  have hG : (maskRes H (Λ.erase x) E).IsHermitian := maskRes_isHermitian hH _ E
  unfold Matrix.IsHermitian selfEnergy
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    blockMask_blockOf_conjTranspose, hH.eq, hG.eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  simp only [Matrix.mul_assoc]

/-- One deletion step ([PSSS, (2.7)]): for `x ≠ y` in `Λ`, if `G_Λ` and `G_{Λ∖{x}}` are proper
inverses, `G_Λ(x, y) = -Σ_{c ∈ Λ∖{x}} G_Λ(x, x) H_{xc} G_{Λ∖{x}}(c, y)`. -/
theorem blockOf_maskRes_delete {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    {Λ : Finset (Fin L)} {x y : Fin L} (hx : x ∈ Λ) (hy : y ∈ Λ) (hxy : x ≠ y) (E : ℝ)
    (hΛ : (maskMat {p | p.1 ∈ Λ}
      (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))).det ≠ 0)
    (hΛx : (maskMat {p | p.1 ∈ Λ.erase x}
      (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))).det ≠ 0) :
    blockOf (maskRes H Λ E) x y = -∑ c ∈ Λ.erase x,
      blockOf (maskRes H Λ E) x x * blockOf H x c * blockOf (maskRes H (Λ.erase x) E) c y := by
  have hTS : {p : Fin L × Fin W | p.1 ∈ ({x} : Finset (Fin L))} ⊆ {p | p.1 ∈ Λ} := by
    intro p hp
    simp only [Set.mem_ofPred_eq, Finset.mem_singleton] at hp ⊢
    exact hp ▸ hx
  have hdiff := blockMask_sdiff (W := W) Λ x
  have hST : (maskMat ({p : Fin L × Fin W | p.1 ∈ Λ} \ {p | p.1 ∈ ({x} : Finset (Fin L))})
      (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))).det ≠ 0 := by
    rw [hdiff]
    exact hΛx
  ext α β
  have key := maskMat_inv_delete hTS (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))
    hΛ hST (p := (x, α)) (q := (y, β)) (by simp)
    (by rw [hdiff]; simp [Finset.mem_erase, hy, Ne.symm hxy])
  simp only [hdiff, Set.mem_ofPred_eq] at key
  rw [blockMask_sum_pairs] at key
  simp only [Finset.sum_singleton] at key
  simp only [blockOf, Matrix.of_apply, Matrix.neg_apply, Matrix.sum_apply, Matrix.mul_apply]
  unfold maskRes
  rw [key]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  have hcx : c ≠ x := (Finset.mem_erase.mp hc).1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [blockMask_shift_apply_ne H E (Ne.symm hcx)]

/-- The Schur complement at one block ([PSSS, (2.5)]): for `x ∈ Λ`, if `G_{Λ∖{x}}` is a proper
inverse, `G_Λ(x, x) = (H_{xx} - E - Σ_x)⁻¹`. -/
theorem blockOf_maskRes_self {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    {Λ : Finset (Fin L)} {x : Fin L} (hx : x ∈ Λ) (E : ℝ)
    (hΛx : (maskMat {p | p.1 ∈ Λ.erase x}
      (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))).det ≠ 0) :
    blockOf (maskRes H Λ E) x x =
      (blockOf H x x - (E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - selfEnergy H Λ x E)⁻¹ := by
  have hTS : {p : Fin L × Fin W | p.1 ∈ ({x} : Finset (Fin L))} ⊆ {p | p.1 ∈ Λ} := by
    intro p hp
    simp only [Set.mem_ofPred_eq, Finset.mem_singleton] at hp ⊢
    exact hp ▸ hx
  have hdiff := blockMask_sdiff (W := W) Λ x
  have hST : (maskMat ({p : Fin L × Fin W | p.1 ∈ Λ} \ {p | p.1 ∈ ({x} : Finset (Fin L))})
      (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))).det ≠ 0 := by
    rw [hdiff]
    exact hΛx
  ext α β
  have key := maskMat_inv_schur hTS (H - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))
    hST (p := (x, α)) (q := (x, β)) (by simp) (by simp)
  simp only [hdiff, Set.mem_ofPred_eq] at key
  rw [blockMask_inv_oneBlock] at key
  refine (show blockOf (maskRes H Λ E) x x α β = _ from rfl).trans (key.trans ?_)
  rw [blockMask_schur_block]
  rfl

end LSBA
