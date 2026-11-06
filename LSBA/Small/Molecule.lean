import LSBA.Small.Rows
import LSBA.Primitive.Molecule

/-!
# Stable molecules at small coupling

The cancellation bound (B.3) [ba:eq:cancel] of Lemma B.1 [ba:lem:moment] with the explicit factor
`g²` of small coupling: alternating stable molecules satisfy
`|Ŝ_t(n)| ≤ C'((1 - t) + g² Σ_j |n_j|²_𝕋)`, on `0 ≤ g ≤ C` and `0 ≤ t < 1`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

section Faces

variable {k L : ℕ}

/-- With equal copies of every diagonal label, the two sides of an edge carry the same label. -/
private lemma edgeLab_sides (F : Finset (Fin k × Fin k)) (y : Fin k → Fin L) (c : ↥F → Fin L)
    (v w : Fin k) : edgeLab F y c c v w false = edgeLab F y c c v w true := by
  unfold edgeLab
  split_ifs <;> rfl

/-- With equal copies of every diagonal label, if every corner at `u` joins equal labels, then
every edge at `u` carries the label `y_u`. -/
private lemma chain_eq (hk : 3 ≤ k) {F : Finset (Fin k × Fin k)} (hF : F ⊆ polyDiags k)
    (y : Fin k → Fin L) (c : ↥F → Fin L) (u : Fin k)
    (hu : ∀ p ∈ polyCorners F u, edgeLab F y c c u p.2 true = edgeLab F y c c u p.1 false) :
    ∀ o, ∀ w, PolyNbr F u w → polyOff u w = o → edgeLab F y c c u w true = y u := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
  intro w hw ho
  by_cases h1 : polyOff u w = 1
  · have hs := mol_side_not_mem hF (Or.inl h1)
    unfold edgeLab
    simp only [hs, ↓reduceDIte, h1, ↓reduceIte]
  have hwv : w ≠ u := hw.1
  have hpos : 1 ≤ polyOff u w := by
    by_contra h0
    apply hwv
    have := u.isLt
    have := w.isLt
    rw [mol_polyOff_eq] at h0
    apply Fin.ext
    split_ifs at h0 <;> omega
  set S := Finset.univ.filter (fun x => PolyNbr F u x ∧ polyOff u x < polyOff u w) with hS
  have hu0 : finRotate k u ∈ S := by
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ⟨?_, Or.inl (mol_polyOff_rot (by omega) u)⟩, ?_⟩
    · intro h
      have := mol_polyOff_rot (k := k) (by omega) u
      rw [h, mol_polyOff_eq] at this
      simp at this
    · rw [mol_polyOff_rot (by omega) u]; omega
  obtain ⟨x, hxS, hmax⟩ := S.exists_max_image (polyOff u) ⟨_, hu0⟩
  rw [hS, Finset.mem_filter] at hxS
  have hc : (x, w) ∈ polyCorners F u := by
    rw [mol_mem_polyCorners]
    refine ⟨hxS.2.1, hw, hxS.2.2, fun u' hu' hb => ?_⟩
    simp only at hb
    have := hmax u' (by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hu', by omega⟩)
    omega
  have hih := ih (polyOff u x) (by omega) x hxS.2.1 rfl
  have hA := hu _ hc
  simp only at hA
  rw [hA, edgeLab_sides, hih]

/-- With equal copies of every diagonal label, if every corner at the vertex `i + 1` joins
equal labels, then `y_i = y_{i+1}`. -/
private lemma step_eq (hk : 3 ≤ k) {F : Finset (Fin k × Fin k)} (hF : F ⊆ polyDiags k)
    (y : Fin k → Fin L) (c : ↥F → Fin L) (i : Fin k)
    (hu : ∀ p ∈ polyCorners F (finRotate k i),
      edgeLab F y c c (finRotate k i) p.2 true = edgeLab F y c c (finRotate k i) p.1 false) :
    y i = y (finRotate k i) := by
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
  have hlab : edgeLab F y c c u i true = y i := by
    unfold edgeLab
    simp only [hs, ↓reduceDIte, show polyOff u i ≠ 1 by omega, ↓reduceIte]
  rw [← hlab]
  exact chain_eq hk hF y c u hu _ i hnbr rfl

/-- `(a + r) mod k ≠ a` for `0 < r < k`. -/
private lemma mod_ne_self {a r k : ℕ} (ha : a < k) (hr0 : 0 < r) (hrk : r < k) :
    (a + r) % k ≠ a := by
  by_cases h : a + r < k
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [show a + r = (a + r - k) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- A cyclic word that is not constant changes its value at two different positions. -/
private lemma two_changes {α : Type*} (hk : 1 ≤ k) (y : Fin k → α) (hy : ∃ i j, y i ≠ y j) :
    ∃ i₁ i₂ : Fin k, i₁ ≠ i₂ ∧ y (finRotate k i₁) ≠ y i₁ ∧ y (finRotate k i₂) ≠ y i₂ := by
  by_contra H
  push Not at H
  have h₀ : ∃ i₀ : Fin k, ∀ i, i ≠ i₀ → y (finRotate k i) = y i := by
    by_cases hc : ∃ i₀, y (finRotate k i₀) ≠ y i₀
    · obtain ⟨i₀, hi₀⟩ := hc
      exact ⟨i₀, fun i hi => H i₀ i (Ne.symm hi) hi₀⟩
    · push Not at hc
      exact ⟨⟨0, by omega⟩, fun i _ => hc i⟩
  obtain ⟨i₀, hi₀⟩ := h₀
  have key : ∀ r, 1 ≤ r → r ≤ k → y ((finRotate k)^[r] i₀) = y (finRotate k i₀) := by
    intro r
    induction r with
    | zero => intro h; omega
    | succ r ih =>
      intro _ hr
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0; rfl
      rw [Function.iterate_succ_apply', hi₀, ih h0 (by omega)]
      intro he
      have := congrArg Fin.val he
      rw [mol_iter_val] at this
      exact mod_ne_self i₀.isLt h0 (by omega) this
  obtain ⟨i, j, hij⟩ := hy
  have hall : ∀ x : Fin k, y x = y (finRotate k i₀) := by
    intro x
    by_cases hx : i₀.val < x.val
    · have e : (finRotate k)^[x.val - i₀.val] i₀ = x := by
        apply Fin.ext
        rw [mol_iter_val, Nat.mod_eq_of_lt (by omega)]
        omega
      rw [← e, key _ (by omega) (by omega)]
    · have e : (finRotate k)^[x.val + k - i₀.val] i₀ = x := by
        apply Fin.ext
        rw [mol_iter_val, show i₀.val + (x.val + k - i₀.val) = x.val + k by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
      have := i₀.isLt
      rw [← e, key _ (by omega) (by omega)]
  exact hij ((hall i).trans (hall j).symm)

/-- With equal copies of every diagonal label and a nonconstant external word, two different
vertices carry a corner that joins different labels. -/
private lemma two_bad (hk : 3 ≤ k) {F : Finset (Fin k × Fin k)} (hF : F ⊆ polyDiags k)
    (y : Fin k → Fin L) (c : ↥F → Fin L) (hy : ∃ i j, y i ≠ y j) :
    ∃ v₁ v₂ : Fin k, v₁ ≠ v₂ ∧
      (∃ p ∈ polyCorners F v₁, edgeLab F y c c v₁ p.2 true ≠ edgeLab F y c c v₁ p.1 false) ∧
      ∃ p ∈ polyCorners F v₂, edgeLab F y c c v₂ p.2 true ≠ edgeLab F y c c v₂ p.1 false := by
  obtain ⟨i₁, i₂, h12, h1, h2⟩ := two_changes (by omega) y hy
  have bad : ∀ i, y (finRotate k i) ≠ y i → ∃ p ∈ polyCorners F (finRotate k i),
      edgeLab F y c c (finRotate k i) p.2 true ≠ edgeLab F y c c (finRotate k i) p.1 false := by
    intro i hi
    by_contra hc
    push Not at hc
    exact hi (step_eq hk hF y c i hc).symm
  exact ⟨finRotate k i₁, finRotate k i₂, fun h => h12 ((finRotate k).injective h), bad i₁ h1,
    bad i₂ h2⟩

/-- The coupling weight of the corners of a labelled dissection: one factor `g` per corner
joining two different labels. -/
private def cornerW (F : Finset (Fin k × Fin k)) (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L)
    (g : ℝ) : ℝ :=
  ∏ v, ∏ p ∈ polyCorners F v,
    if edgeLab F y cIn cOut v p.2 true = edgeLab F y cIn cOut v p.1 false then 1 else g

private lemma cornerW_nonneg (F : Finset (Fin k × Fin k)) (y : Fin k → Fin L)
    (cIn cOut : ↥F → Fin L) {g : ℝ} (hg : 0 ≤ g) : 0 ≤ cornerW F y cIn cOut g :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by split_ifs <;> linarith

/-- The coupling weight is at most `G^{N_c}`, and at most `g²G^{N_c}` when all diagonal labels
have equal copies and the external word is not constant. -/
private lemma cornerW_le (hk : 3 ≤ k) {F : Finset (Fin k × Fin k)} (hF : F ⊆ polyDiags k)
    (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L) {g G : ℝ} (hg : 0 ≤ g) (hgG : g ≤ G)
    (hG : 1 ≤ G) (hy : ∃ i j, y i ≠ y j) :
    cornerW F y cIn cOut g ≤
      G ^ (∑ v, (polyCorners F v).card) * (g ^ 2 + ∑ d : ↥F, if cOut d = cIn d then 0 else 1) := by
  set ρ : Fin k → Fin k × Fin k → ℝ := fun v p =>
    if edgeLab F y cIn cOut v p.2 true = edgeLab F y cIn cOut v p.1 false then 1 else g with hρ
  have hρ0 : ∀ v p, 0 ≤ ρ v p := fun v p => by simp only [hρ]; split_ifs <;> linarith
  have hρG : ∀ v p, ρ v p ≤ G := fun v p => by simp only [hρ]; split_ifs <;> linarith
  have hv : ∀ v, ∏ p ∈ polyCorners F v, ρ v p ≤ G ^ (polyCorners F v).card := fun v => by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun p _ => hρ0 v p) fun p _ => hρG v p
  have hW : cornerW F y cIn cOut g = ∏ v, ∏ p ∈ polyCorners F v, ρ v p := rfl
  have hGN : 0 ≤ G ^ (∑ v, (polyCorners F v).card) := by positivity
  have hS0 : 0 ≤ ∑ d : ↥F, (if cOut d = cIn d then (0 : ℝ) else 1) :=
    Finset.sum_nonneg fun d _ => by split_ifs <;> norm_num
  by_cases hP : ∀ d, cOut d = cIn d
  · have hc : cOut = cIn := funext hP
    subst hc
    have hsum : ∑ d : ↥F, (if cOut d = cOut d then (0 : ℝ) else 1) = 0 := by simp
    rw [hsum, add_zero]
    obtain ⟨v₁, v₂, h12, ⟨p₁, hp₁, hb₁⟩, ⟨p₂, hp₂, hb₂⟩⟩ := two_bad hk hF y cOut hy
    have hbad : ∀ v, ∀ p ∈ polyCorners F v, ρ v p = g → ∏ q ∈ polyCorners F v, ρ v q ≤
        g * G ^ (polyCorners F v).card := by
      intro v p hp hρp
      rw [← Finset.mul_prod_erase _ _ hp, hρp]
      have h1 : ∏ q ∈ (polyCorners F v).erase p, ρ v q ≤ G ^ ((polyCorners F v).erase p).card := by
        rw [← Finset.prod_const]
        exact Finset.prod_le_prod₀ (fun q _ => hρ0 v q) fun q _ => hρG v q
      have h2 : G ^ ((polyCorners F v).erase p).card ≤ G ^ (polyCorners F v).card :=
        pow_le_pow_right₀ hG (Finset.card_erase_le)
      exact mul_le_mul_of_nonneg_left (h1.trans h2) hg
    have hb : ∀ v, ∏ p ∈ polyCorners F v, ρ v p ≤
        (if v ∈ ({v₁, v₂} : Finset (Fin k)) then g else 1) * G ^ (polyCorners F v).card := by
      intro v
      split_ifs with hm
      · rcases Finset.mem_insert.mp hm with h | h
        · subst h; exact hbad _ p₁ hp₁ (by simp only [hρ]; exact ite_eq_right hb₁)
        · rw [Finset.mem_singleton] at h
          subst h; exact hbad _ p₂ hp₂ (by simp only [hρ]; exact ite_eq_right hb₂)
      · rw [one_mul]; exact hv v
    rw [hW]
    calc ∏ v, ∏ p ∈ polyCorners F v, ρ v p
        ≤ ∏ v, (if v ∈ ({v₁, v₂} : Finset (Fin k)) then g else 1) * G ^ (polyCorners F v).card :=
          Finset.prod_le_prod₀ (fun v _ => Finset.prod_nonneg fun p _ => hρ0 v p) fun v _ => hb v
      _ = G ^ (∑ v, (polyCorners F v).card) * g ^ 2 := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_ite_mem,
            Finset.univ_inter, Finset.prod_const, Finset.card_pair h12]
          ring
  · push Not at hP
    obtain ⟨d₀, hd₀⟩ := hP
    have h1 : (1 : ℝ) ≤ ∑ d : ↥F, if cOut d = cIn d then (0 : ℝ) else 1 := by
      have := Finset.single_le_sum (f := fun d : ↥F => if cOut d = cIn d then (0 : ℝ) else 1)
        (fun d _ => by split_ifs <;> norm_num) (Finset.mem_univ d₀)
      simpa [hd₀] using this
    rw [hW]
    calc ∏ v, ∏ p ∈ polyCorners F v, ρ v p ≤ ∏ v, G ^ (polyCorners F v).card :=
          Finset.prod_le_prod₀ (fun v _ => Finset.prod_nonneg fun p _ => hρ0 v p) fun v _ => hv v
      _ = G ^ (∑ v, (polyCorners F v).card) * 1 := by rw [Finset.prod_pow_eq_pow_sum, mul_one]
      _ ≤ _ := by gcongr; nlinarith [sq_nonneg g]

/-- Sums over the two copies of the diagonal labels factor over the diagonals. -/
private lemma sum_prod_links (F : Finset (Fin k × Fin k)) (h : ↥F → Fin L → Fin L → ℝ) :
    ∑ cIn : ↥F → Fin L, ∑ cOut : ↥F → Fin L, ∏ d : ↥F, h d (cIn d) (cOut d) =
      ∏ d : ↥F, ∑ i : Fin L, ∑ o : Fin L, h d i o := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun cIn _ => ?_
  rw [← Fintype.prod_sum (fun d o => h d (cIn d) o)]

/-- The core of a dissection at a nonconstant external word is `O(g²)`: if every corner is
bounded by `Ce^{-c d}`, by `Cge^{-c d}` off the diagonal, and every link by `e^{-c d}K` with
column sums of `K` at most `B` and off-diagonal column sums at most `Bg²`, then
`‖C_F(y)‖ ≤ g²(CG)^{N_c}(1 + |F|)(2(1 + 6k⁴/c)B)^{|F|}e^{-c diam(y)/(12k²)}`. -/
private lemma core_small (hk : 3 ≤ k) {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {t : ℝ}
    {σ : Fin k → Bool} {F : Finset (Fin k × Fin k)} (hF : F ⊆ polyDiags k)
    {c C B g G : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hg : 0 ≤ g) (hgG : g ≤ G)
    (hG : 1 ≤ G)
    (hM : ∀ s x z, ‖sgnMat M s x z‖ ≤
      C * Real.exp (-(c * cycDist x z)) * (if x = z then 1 else g))
    (K : Fin L → Fin L → ℝ) (hK0 : ∀ o i, 0 ≤ K o i)
    (hlink : ∀ (d : ↥F) o i, ‖((β * t : ℝ) : ℂ) * pairV β M t (σ d.1.1) (σ d.1.2) o i‖ ≤
      Real.exp (-(c * cycDist o i)) * K o i)
    (hKrow : ∀ i, ∑ o, K o i ≤ B) (hKoff : ∀ i, ∑ o ∈ Finset.univ.erase i, K o i ≤ B * g ^ 2)
    (y : Fin k → Fin L) (hy : ∃ i j, y i ≠ y j) :
    ‖dissCore β M t σ F y‖ ≤ g ^ 2 * ((C * G) ^ (∑ v, (polyCorners F v).card) *
      (1 + F.card) * (2 * (1 + 6 * k ^ 4 / c) * B) ^ F.card) *
      Real.exp (-(c / (12 * k ^ 2) * wordDiam y)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  set y0 := y ⟨0, by omega⟩
  set c₂ := c / (6 * k ^ 4) with hc₂
  have hc₂0 : 0 < c₂ := by positivity
  set E := Real.exp (-(c / (12 * k ^ 2) * wordDiam y))
  set Nc := ∑ v, (polyCorners F v).card
  set A := 2 * (1 + 6 * k ^ 4 / c) * B with hA
  have hA0 : 0 ≤ A := by positivity
  set h : Fin L → Fin L → ℝ := fun i o => Real.exp (-(c₂ * cycDist i y0)) * K o i with hh
  have hh0 : ∀ i o, 0 ≤ h i o := fun i o => mul_nonneg (Real.exp_pos _).le (hK0 _ _)
  -- the pointwise bound
  have hpt : ∀ cIn cOut : ↥F → Fin L,
      ‖(∏ d : ↥F, ((β * t : ℝ) : ℂ) * pairV β M t (σ d.1.1) (σ d.1.2) (cOut d) (cIn d)) *
        ∏ v : Fin k, ∏ p ∈ polyCorners F v,
          sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)‖ ≤
        C ^ Nc * cornerW F y cIn cOut g * E * ∏ d : ↥F, h (cIn d) (cOut d) := by
    intro cIn cOut
    set T := mol_tot F y cIn cOut
    have hA' : ‖∏ d : ↥F, ((β * t : ℝ) : ℂ) * pairV β M t (σ d.1.1) (σ d.1.2) (cOut d) (cIn d)‖ ≤
        Real.exp (-(c * (∑ d : ↥F, (cycDist (cOut d) (cIn d) : ℝ)))) *
          ∏ d : ↥F, K (cOut d) (cIn d) := by
      rw [norm_prod]
      calc ∏ d : ↥F, ‖((β * t : ℝ) : ℂ) * pairV β M t (σ d.1.1) (σ d.1.2) (cOut d) (cIn d)‖
          ≤ ∏ d : ↥F, (Real.exp (-(c * cycDist (cOut d) (cIn d))) * K (cOut d) (cIn d)) :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun d _ => hlink d _ _
        _ = _ := by
            rw [Finset.prod_mul_distrib, ← Real.exp_sum]
            congr 2
            rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    have hexpc : ∏ v : Fin k, ∏ p ∈ polyCorners F v, Real.exp (-(c *
          cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false))) =
        Real.exp (-(c * (∑ v : Fin k, ∑ p ∈ polyCorners F v,
          (cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) :
            ℝ)))) := by
      rw [Finset.prod_congr rfl fun v _ => (Real.exp_sum _ _).symm, ← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    have hB' : ‖∏ v : Fin k, ∏ p ∈ polyCorners F v,
          sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)‖ ≤
        C ^ Nc * cornerW F y cIn cOut g * Real.exp (-(c * (∑ v : Fin k, ∑ p ∈ polyCorners F v,
          (cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) :
            ℝ)))) := by
      rw [norm_prod]
      calc ∏ v : Fin k, ‖∏ p ∈ polyCorners F v,
            sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)‖
          ≤ ∏ v : Fin k, ∏ p ∈ polyCorners F v, (C * Real.exp (-(c *
              cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false))) *
              (if edgeLab F y cIn cOut v p.2 true = edgeLab F y cIn cOut v p.1 false then 1
                else g)) := by
            refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => ?_
            rw [norm_prod]
            exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun p _ => hM _ _ _
        _ = _ := by
            unfold cornerW
            simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
            rw [hexpc]
            ring
    have htot : (T : ℝ) = (∑ d : ↥F, (cycDist (cOut d) (cIn d) : ℝ)) +
        ∑ v : Fin k, ∑ p ∈ polyCorners F v,
          (cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) : ℝ) := by
      simp only [T, mol_tot]
      push_cast
      rfl
    obtain ⟨hdiam, hint⟩ := mol_tot_bounds hk hF y cIn cOut
    have hexp : Real.exp (-(c * (∑ d : ↥F, (cycDist (cOut d) (cIn d) : ℝ)))) *
        Real.exp (-(c * (∑ v : Fin k, ∑ p ∈ polyCorners F v,
          (cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) : ℝ)))) ≤
          E * ∏ d : ↥F, Real.exp (-(c₂ * cycDist (cIn d) y0)) := by
      rw [← Real.exp_add, ← Real.exp_sum, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have e1 : ∑ d : ↥F, -(c₂ * (cycDist (cIn d) y0 : ℝ)) =
          -(c₂ * ∑ d : ↥F, (cycDist (cIn d) y0 : ℝ)) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      rw [e1]
      have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
      have i1 : c / (12 * k ^ 2) * wordDiam y ≤ c / 2 * T := by
        calc c / (12 * k ^ 2) * wordDiam y ≤ c / (12 * k ^ 2) * (6 * k ^ 2 * T) := by gcongr
          _ = c / 2 * T := by field_simp; ring
      have i2 : c₂ * ∑ d : ↥F, (cycDist (cIn d) y0 : ℝ) ≤ c / 2 * T := by
        calc c₂ * ∑ d : ↥F, (cycDist (cIn d) y0 : ℝ) ≤ c₂ * (3 * k ^ 4 * T) := by gcongr
          _ = c / 2 * T := by rw [hc₂]; field_simp; ring
      have e2 : -(c * (∑ d : ↥F, (cycDist (cOut d) (cIn d) : ℝ))) +
          -(c * (∑ v : Fin k, ∑ p ∈ polyCorners F v,
            (cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) : ℝ))) =
            -(c * T) := by
        rw [htot]; ring
      rw [e2]
      linarith
    rw [norm_mul]
    have hK : 0 ≤ ∏ d : ↥F, K (cOut d) (cIn d) := Finset.prod_nonneg fun d _ => hK0 _ _
    have hW0 := cornerW_nonneg F y cIn cOut hg
    calc ‖∏ d : ↥F, ((β * t : ℝ) : ℂ) * pairV β M t (σ d.1.1) (σ d.1.2) (cOut d) (cIn d)‖ *
          ‖∏ v : Fin k, ∏ p ∈ polyCorners F v,
            sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)‖
        ≤ (Real.exp (-(c * (∑ d : ↥F, (cycDist (cOut d) (cIn d) : ℝ)))) *
            ∏ d : ↥F, K (cOut d) (cIn d)) *
          (C ^ Nc * cornerW F y cIn cOut g * Real.exp (-(c * (∑ v : Fin k, ∑ p ∈ polyCorners F v,
            (cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) :
              ℝ))))) := mul_le_mul hA' hB' (norm_nonneg _) (by positivity)
      _ = C ^ Nc * cornerW F y cIn cOut g *
          (Real.exp (-(c * (∑ d : ↥F, (cycDist (cOut d) (cIn d) : ℝ)))) *
          Real.exp (-(c * (∑ v : Fin k, ∑ p ∈ polyCorners F v,
            (cycDist (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false) :
              ℝ))))) * ∏ d : ↥F, K (cOut d) (cIn d) := by ring
      _ ≤ C ^ Nc * cornerW F y cIn cOut g *
          (E * ∏ d : ↥F, Real.exp (-(c₂ * cycDist (cIn d) y0))) *
          ∏ d : ↥F, K (cOut d) (cIn d) := by gcongr
      _ = C ^ Nc * cornerW F y cIn cOut g * E * ∏ d : ↥F, h (cIn d) (cOut d) := by
          rw [hh]; simp only [Finset.prod_mul_distrib]; ring
  -- the factors of the summed links
  have hfac : ∀ i : Fin L, ∑ o : Fin L, h i o ≤ Real.exp (-(c₂ * cycDist i y0)) * B := by
    intro i
    simp only [hh, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hKrow i) (Real.exp_pos _).le
  have hfacoff : ∀ i : Fin L, ∑ o : Fin L, (if o = i then 0 else h i o) ≤
      Real.exp (-(c₂ * cycDist i y0)) * (B * g ^ 2) := by
    intro i
    have e : ∑ o : Fin L, (if o = i then 0 else h i o) = ∑ o ∈ Finset.univ.erase i, h i o := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ite_eq_left rfl, zero_add]
      exact Finset.sum_congr rfl fun o ho => ite_eq_right (Finset.ne_of_mem_erase ho)
    rw [e]
    simp only [hh, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hKoff i) (Real.exp_pos _).le
  have hgeom : ∑ i : Fin L, Real.exp (-(c₂ * cycDist i y0)) ≤ 2 * (1 + 6 * k ^ 4 / c) := by
    have := mol_geom_sum y0 hc₂0 (a := 1) le_rfl
    simp only [div_one, mul_one] at this
    calc _ ≤ 2 * (1 + 1 / c₂) := this
      _ = 2 * (1 + 6 * k ^ 4 / c) := by rw [hc₂]; field_simp
  have hS1 : ∑ i : Fin L, ∑ o : Fin L, h i o ≤ A := by
    calc ∑ i : Fin L, ∑ o : Fin L, h i o ≤ ∑ i : Fin L, Real.exp (-(c₂ * cycDist i y0)) * B :=
          Finset.sum_le_sum fun i _ => hfac i
      _ = (∑ i : Fin L, Real.exp (-(c₂ * cycDist i y0))) * B := by rw [Finset.sum_mul]
      _ ≤ 2 * (1 + 6 * k ^ 4 / c) * B := by gcongr
  have hS2 : ∑ i : Fin L, ∑ o : Fin L, (if o = i then 0 else h i o) ≤ A * g ^ 2 := by
    calc ∑ i : Fin L, ∑ o : Fin L, (if o = i then 0 else h i o)
        ≤ ∑ i : Fin L, Real.exp (-(c₂ * cycDist i y0)) * (B * g ^ 2) :=
          Finset.sum_le_sum fun i _ => hfacoff i
      _ = (∑ i : Fin L, Real.exp (-(c₂ * cycDist i y0))) * (B * g ^ 2) := by rw [Finset.sum_mul]
      _ ≤ 2 * (1 + 6 * k ^ 4 / c) * (B * g ^ 2) := by gcongr
      _ = A * g ^ 2 := by rw [hA]; ring
  -- the links with one off-diagonal link
  set h' : ↥F → ↥F → Fin L → Fin L → ℝ := fun d₀ d i o =>
    if d = d₀ then (if o = i then 0 else h i o) else h i o with hh'
  have hsplit : ∀ (d₀ : ↥F) (cIn cOut : ↥F → Fin L),
      (if cOut d₀ = cIn d₀ then (0 : ℝ) else 1) * ∏ d : ↥F, h (cIn d) (cOut d) =
        ∏ d : ↥F, h' d₀ d (cIn d) (cOut d) := by
    intro d₀ cIn cOut
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ d₀),
      ← Finset.mul_prod_erase _ (fun d => h' d₀ d (cIn d) (cOut d)) (Finset.mem_univ d₀)]
    have e : ∏ d ∈ Finset.univ.erase d₀, h' d₀ d (cIn d) (cOut d) =
        ∏ d ∈ Finset.univ.erase d₀, h (cIn d) (cOut d) :=
      Finset.prod_congr rfl fun d hd => by
        simp only [hh', ite_eq_right (Finset.ne_of_mem_erase hd)]
    rw [e]
    simp only [hh', ite_eq_left rfl]
    split_ifs <;> ring
  have hP1 : ∏ _d : ↥F, ∑ i : Fin L, ∑ o : Fin L, h i o ≤ A ^ F.card := by
    calc ∏ _d : ↥F, ∑ i : Fin L, ∑ o : Fin L, h i o ≤ ∏ _d : ↥F, A :=
          Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun i _ =>
            Finset.sum_nonneg fun o _ => hh0 i o) fun _ _ => hS1
      _ = A ^ F.card := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  have hh'0 : ∀ d₀ d i o, 0 ≤ h' d₀ d i o := fun d₀ d i o => by
    simp only [hh']
    split_ifs
    · exact le_rfl
    · exact hh0 i o
    · exact hh0 i o
  have hP2 : ∀ d₀ : ↥F, ∏ d : ↥F, ∑ i : Fin L, ∑ o : Fin L, h' d₀ d i o ≤ A ^ F.card * g ^ 2 := by
    intro d₀
    calc ∏ d : ↥F, ∑ i : Fin L, ∑ o : Fin L, h' d₀ d i o
        ≤ ∏ d : ↥F, (A * if d = d₀ then g ^ 2 else 1) := by
          refine Finset.prod_le_prod₀ (fun d _ => Finset.sum_nonneg fun i _ =>
            Finset.sum_nonneg fun o _ => hh'0 d₀ d i o) fun d _ => ?_
          by_cases hd : d = d₀
          · simp only [hh', hd, ↓reduceIte]
            exact hS2
          · simp only [hh', hd, ↓reduceIte, mul_one]
            exact hS1
      _ = A ^ F.card * g ^ 2 := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
            Fintype.prod_ite_eq']
  have hs0 := sum_prod_links F (fun _ => h)
  set X := C ^ Nc * G ^ Nc * E with hX
  have hX0 : 0 ≤ X := by positivity
  have hpt2 : ∀ cIn cOut : ↥F → Fin L,
      C ^ Nc * cornerW F y cIn cOut g * E * ∏ d : ↥F, h (cIn d) (cOut d) ≤
        X * (g ^ 2 * ∏ d : ↥F, h (cIn d) (cOut d) +
          ∑ d₀ : ↥F, ∏ d : ↥F, h' d₀ d (cIn d) (cOut d)) := by
    intro cIn cOut
    have hP : 0 ≤ ∏ d : ↥F, h (cIn d) (cOut d) := Finset.prod_nonneg fun d _ => hh0 _ _
    have hW := cornerW_le hk hF y cIn cOut hg hgG hG hy
    calc C ^ Nc * cornerW F y cIn cOut g * E * ∏ d : ↥F, h (cIn d) (cOut d)
        ≤ C ^ Nc * (G ^ Nc * (g ^ 2 + ∑ d : ↥F, if cOut d = cIn d then 0 else 1)) * E *
            ∏ d : ↥F, h (cIn d) (cOut d) := by gcongr
      _ = X * (g ^ 2 * ∏ d : ↥F, h (cIn d) (cOut d) +
            (∑ d : ↥F, if cOut d = cIn d then (0 : ℝ) else 1) * ∏ d : ↥F, h (cIn d) (cOut d)) := by
          rw [hX]; ring
      _ = _ := by
          rw [Finset.sum_mul]
          simp only [hsplit]
  unfold dissCore
  calc ‖∑ cIn : ↥F → Fin L, ∑ cOut : ↥F → Fin L,
        (∏ d : ↥F, ((β * t : ℝ) : ℂ) * pairV β M t (σ d.1.1) (σ d.1.2) (cOut d) (cIn d)) *
          ∏ v : Fin k, ∏ p ∈ polyCorners F v,
            sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)‖
      ≤ ∑ cIn : ↥F → Fin L, ∑ cOut : ↥F → Fin L,
          X * (g ^ 2 * ∏ d : ↥F, h (cIn d) (cOut d) +
            ∑ d₀ : ↥F, ∏ d : ↥F, h' d₀ d (cIn d) (cOut d)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun cIn _ => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun cOut _ =>
          (hpt cIn cOut).trans (hpt2 cIn cOut))
    _ = X * (g ^ 2 * ∑ cIn : ↥F → Fin L, ∑ cOut : ↥F → Fin L, ∏ d : ↥F, h (cIn d) (cOut d) +
          ∑ d₀ : ↥F, ∑ cIn : ↥F → Fin L, ∑ cOut : ↥F → Fin L,
            ∏ d : ↥F, h' d₀ d (cIn d) (cOut d)) := by
        simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
        congr 1
        exact (Finset.sum_congr rfl fun cIn _ => Finset.sum_comm).trans Finset.sum_comm
    _ = X * (g ^ 2 * ∏ _d : ↥F, ∑ i : Fin L, ∑ o : Fin L, h i o +
          ∑ d₀ : ↥F, ∏ d : ↥F, ∑ i : Fin L, ∑ o : Fin L, h' d₀ d i o) := by
        rw [hs0]
        simp only [sum_prod_links]
    _ ≤ X * (g ^ 2 * A ^ F.card + ∑ _d₀ : ↥F, A ^ F.card * g ^ 2) := by
        gcongr with d₀
        exact hP2 d₀
    _ = g ^ 2 * ((C * G) ^ Nc * (1 + F.card) * A ^ F.card) * E := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, hX, mul_pow]
        ring

end Faces

/-- The profile of the stable molecules at small coupling: at every nonconstant word,
`‖S_t(y)‖ ≤ g²C_S e^{-c diam(y)}`, on `0 ≤ g ≤ C` and `0 ≤ t < 1`. -/
private lemma stable_small (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') (k : ℕ)
    (hk : 3 ≤ k) :
    ∃ c CS : ℝ, ∃ L₀ : ℕ, 0 < c ∧ 0 ≤ CS ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L →
      L₀ ≤ L → ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      c' ≤ m.im → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin k → Bool) (y : Fin k → Fin L),
        (∃ i j, y i ≠ y j) →
        ‖stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y‖ ≤
          g ^ 2 * CS * Real.exp (-(c * wordDiam y)) := by
  obtain ⟨c₁, Ck, L₁, hc₁, hCk, H⟩ := mol_bdd_hyp C B₀ c' hC hB₀ hc'
  obtain ⟨c₂, C₂, L₂, hc₂, hC₂, H2⟩ := kernel_small_rows C B₀ c' hC hB₀ hc'
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  set c := min c₁ c₂ with hcdef
  have hc : 0 < c := lt_min hc₁ hc₂
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  have hcc₂ : c ≤ c₂ := min_le_right _ _
  set Cm := max Ck C₂ with hCm
  have hCm1 : 1 ≤ Cm := hCk.trans (le_max_left _ _)
  set G := max 1 C with hGdef
  have hG : 1 ≤ G := le_max_left _ _
  set CS := ∑ F ∈ dissections k, (Cm * G) ^ (∑ v, (polyCorners F v).card) * (1 + F.card) *
    (2 * (1 + 6 * k ^ 4 / c) * Cm) ^ F.card with hCS
  have hCS0 : 0 ≤ CS := Finset.sum_nonneg fun F _ => by positivity
  refine ⟨c / (12 * k ^ 2), CS, max L₁ L₂, by positivity, hCS0, ?_⟩
  intro g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1 σ y hy
  have h := H g hg hgC L hL (le_of_max_le_left hL₀) E hE m hm hcm t ht0 ht1.le
  have h2 := H2 g hg hgC L hL (le_of_max_le_right hL₀) E hE m hm hcm t ht0 ht1
  have hgG : g ≤ G := hgC.trans (le_max_right _ _)
  set β := gammaG g with hβdef
  set M := dysonMat (hopB g) (gammaG g) L E m with hMdef
  set V := (1 - (t : ℂ) • pairQ β M)⁻¹ with hV
  have hβ : 0 < β := h.data.pos
  have hβ1 : β ≤ 1 := by have := h.beta_le; rwa [mul_one] at this
  have hβt : 0 ≤ β * t := mul_nonneg hβ.le ht0
  have hβt1 : β * t ≤ 1 := by nlinarith
  have hVs : ∀ o i, V o i = V i o :=
    mol_inv_comm _ (mol_oneSub_transpose _ (mol_pairQ_transpose _ h.data.symm) _)
  -- the corners
  have hMoff : ∀ a b, a ≠ b → ‖M a b‖ ≤ C₂ * g * Real.exp (-(c * cycDist a b)) := by
    intro a b hab
    have h1 := Finset.single_le_sum (f := fun b => Real.exp (c₂ * cycDist a b) * ‖M a b‖)
      (fun b _ => by positivity) (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩)
    have h3 := h1.trans (h2 a).1
    have he : Real.exp (-(c₂ * cycDist a b)) * Real.exp (c₂ * cycDist a b) = 1 := by
      rw [← Real.exp_add]; simp
    calc ‖M a b‖ = Real.exp (-(c₂ * cycDist a b)) * (Real.exp (c₂ * cycDist a b) * ‖M a b‖) := by
          rw [← mul_assoc, he, one_mul]
      _ ≤ Real.exp (-(c₂ * cycDist a b)) * (C₂ * g) := by gcongr
      _ ≤ Real.exp (-(c * cycDist a b)) * (C₂ * g) := by gcongr
      _ = _ := by ring
  have hM : ∀ s x z, ‖sgnMat M s x z‖ ≤
      Cm * Real.exp (-(c * cycDist x z)) * (if x = z then 1 else g) := by
    intro s x z
    by_cases hxz : x = z
    · subst hxz
      have := h.sgn s x x
      simp only [mol_cycDist_self, CharP.cast_eq_zero, mul_zero, zero_div, neg_zero,
        Real.exp_zero, mul_one, ↓reduceIte] at this ⊢
      exact this.trans (le_max_left _ _)
    · simp only [hxz, ↓reduceIte]
      have hsym : ‖sgnMat M s x z‖ ≤ C₂ * g * Real.exp (-(c * cycDist x z)) := by
        cases s
        · simp only [sgnMat, Bool.false_eq_true, ↓reduceIte, Matrix.conjTranspose_apply,
            norm_star]
          rw [mol_cycDist_comm]
          exact hMoff z x (Ne.symm hxz)
        · simp only [sgnMat, ↓reduceIte]
          exact hMoff x z hxz
      calc _ ≤ C₂ * g * Real.exp (-(c * cycDist x z)) := hsym
        _ ≤ Cm * g * Real.exp (-(c * cycDist x z)) := by gcongr; exact le_max_right _ _
        _ = _ := by ring
  -- the links
  set K : Fin L → Fin L → ℝ := fun o i => Real.exp (c * cycDist o i) * (β * t) * ‖V o i‖
    with hK
  have hK0 : ∀ o i, 0 ≤ K o i := fun o i => by simp only [hK]; positivity
  have hKrow : ∀ i, ∑ o, K o i ≤ Cm := by
    intro i
    calc ∑ o, K o i = (β * t) * ∑ o, Real.exp (c * cycDist o i) * ‖V o i‖ := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun o _ => by simp only [hK]; ring
      _ ≤ 1 * ∑ o, Real.exp (c₁ * cycDist o i) * ‖V o i‖ := by gcongr
      _ ≤ 1 * Ck := by gcongr; simpa only [div_one] using h.Vcol i
      _ ≤ Cm := by rw [one_mul]; exact le_max_left _ _
  have hKoff : ∀ i, ∑ o ∈ Finset.univ.erase i, K o i ≤ Cm * g ^ 2 := by
    intro i
    calc ∑ o ∈ Finset.univ.erase i, K o i
        = (β * t) * ∑ o ∈ Finset.univ.erase i, Real.exp (c * cycDist i o) * ‖V i o‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun o _ => by
            simp only [hK]; rw [hVs o i, mol_cycDist_comm o i]; ring
      _ ≤ 1 * ∑ o ∈ Finset.univ.erase i, Real.exp (c₂ * cycDist i o) * ‖V i o‖ := by
          gcongr
      _ ≤ 1 * (C₂ * g ^ 2) := by gcongr; exact (h2 i).2
      _ ≤ Cm * g ^ 2 := by rw [one_mul]; gcongr; exact le_max_right _ _
  -- every stable dissection
  have hcore : ∀ F ∈ (dissections k).filter (fun F => ∀ d ∈ F, σ d.1 = σ d.2),
      ‖dissCore β M t σ F y‖ ≤ g ^ 2 * ((Cm * G) ^ (∑ v, (polyCorners F v).card) *
        (1 + F.card) * (2 * (1 + 6 * k ^ 4 / c) * Cm) ^ F.card) *
        Real.exp (-(c / (12 * k ^ 2) * wordDiam y)) := by
    intro F hF
    obtain ⟨hFd, hst⟩ := Finset.mem_filter.mp hF
    have hF' : F ⊆ polyDiags k := Finset.mem_powerset.mp (Finset.mem_filter.mp hFd).1
    have hlink : ∀ (d : ↥F) o i, ‖((β * t : ℝ) : ℂ) * pairV β M t (σ d.1.1) (σ d.1.2) o i‖ ≤
        Real.exp (-(c * cycDist o i)) * K o i := by
      intro d o i
      have hnorm : ‖pairV β M t (σ d.1.1) (σ d.1.2) o i‖ = ‖V o i‖ := by
        have he := hst d.1 d.2
        unfold pairV
        rw [ite_eq_left he]
        cases σ d.1.1
        · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.map_apply, norm_star, V]
        · simp only [↓reduceIte, V]
      rw [norm_mul, hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβt]
      have h1 : Real.exp (-(c * cycDist o i)) * Real.exp (c * cycDist o i) = 1 := by
        rw [← Real.exp_add]; simp
      have e : Real.exp (-(c * cycDist o i)) * K o i = β * t * ‖V o i‖ := by
        simp only [hK]
        rw [← mul_assoc, ← mul_assoc, h1, one_mul]
      rw [e]
    exact core_small hk hF' hc (by linarith) (by linarith) hg hgG hG hM K hK0 hlink hKrow hKoff
      y hy
  unfold stableMol
  rw [hCS, Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ F ∈ (dissections k).filter (fun F => ∀ d ∈ F, σ d.1 = σ d.2), ‖dissCore β M t σ F y‖
      ≤ ∑ F ∈ (dissections k).filter (fun F => ∀ d ∈ F, σ d.1 = σ d.2),
          g ^ 2 * ((Cm * G) ^ (∑ v, (polyCorners F v).card) *
            (1 + F.card) * (2 * (1 + 6 * k ^ 4 / c) * Cm) ^ F.card) *
            Real.exp (-(c / (12 * k ^ 2) * wordDiam y)) := Finset.sum_le_sum hcore
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun F _ _ => ?_
        positivity

/-- A pointwise moment bound: if `‖S(y)‖ ≤ g²C_S e^{-c diam(y)}` at every nonconstant word, then
`diam(y)^r ‖S(y)‖ ≤ g²C_S r!(2/c)^r e^{-c diam(y)/2}` at every word, for `r ≥ 1`. -/
private lemma moment_pt {k L r : ℕ} (hr : 1 ≤ r) {c CS g : ℝ} (hc : 0 < c) (hCS : 0 ≤ CS)
    (S : (Fin k → Fin L) → ℂ)
    (hS : ∀ y, (∃ i j, y i ≠ y j) → ‖S y‖ ≤ g ^ 2 * CS * Real.exp (-(c * wordDiam y)))
    (y : Fin k → Fin L) :
    (wordDiam y : ℝ) ^ r * ‖S y‖ ≤
      g ^ 2 * (CS * ((r.factorial : ℝ) * (2 / c) ^ r)) * Real.exp (-(c / 2 * wordDiam y)) := by
  set D : ℝ := (wordDiam y : ℝ)
  have hD : 0 ≤ D := Nat.cast_nonneg _
  by_cases hy : ∃ i j, y i ≠ y j
  · have hSy := hS y hy
    have e1 : Real.exp (c / 2 * D) * Real.exp (-(c * D)) = Real.exp (-(c / 2 * D)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hpow : D ^ r ≤ (r.factorial : ℝ) * (2 / c) ^ r * Real.exp (c / 2 * D) := by
      have h1 := Real.pow_div_factorial_le_exp (c / 2 * D) (by positivity) r
      have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
      rw [div_le_iff₀ hf] at h1
      have e : D ^ r = (2 / c) ^ r * (c / 2 * D) ^ r := by
        rw [← mul_pow]; congr 1; field_simp
      rw [e]
      calc (2 / c) ^ r * (c / 2 * D) ^ r ≤ (2 / c) ^ r * (Real.exp (c / 2 * D) * r.factorial) := by
            gcongr
        _ = (r.factorial : ℝ) * (2 / c) ^ r * Real.exp (c / 2 * D) := by ring
    calc D ^ r * ‖S y‖ ≤ ((r.factorial : ℝ) * (2 / c) ^ r * Real.exp (c / 2 * D)) *
          (g ^ 2 * CS * Real.exp (-(c * D))) := by gcongr
      _ = g ^ 2 * (CS * ((r.factorial : ℝ) * (2 / c) ^ r)) *
          (Real.exp (c / 2 * D) * Real.exp (-(c * D))) := by ring
      _ = _ := by rw [e1]
  · push Not at hy
    have h0 : wordDiam y = 0 := by
      unfold wordDiam
      refine Nat.eq_zero_of_le_zero (Finset.sup_le fun p _ => ?_)
      rw [hy p.2 p.1, mol_cycDist_self]
    have hD0 : D = 0 := by simp only [D, h0, Nat.cast_zero]
    rw [hD0, zero_pow (by omega), zero_mul]
    positivity

/-- (B.3) [ba:eq:cancel] with the small-coupling factor, Lemma B.1 [ba:lem:moment]: for an
alternating stable molecule, `|Ŝ_t(n)| ≤ C'((1 - t) + g² Σ_j |n_j|²_𝕋)` on `0 ≤ g ≤ C`. -/
theorem stableMol_small_cancel (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') (k : ℕ)
    (hk : 4 ≤ k) :
    ∃ C' : ℝ, ∃ L₀ : ℕ, 0 < C' ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Fin k → Bool, (∀ i, σ (finRotate k i) = !σ i) →
      ∀ n : Fin k → Fin L, (∑ j, (n j : ℕ)) % L = 0 →
        ‖tensorFourier (stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ) n‖ ≤
          C' * ((1 - t) + g ^ 2 * ∑ j, torusAbs L (n j) ^ 2) := by
  obtain ⟨c, CS, L₁, hc, hCS, H⟩ := stable_small C B₀ c' hC hB₀ hc' k (by omega)
  obtain ⟨C₀, L₂, hC₀, H0⟩ := stableMol_bdd_cancel C B₀ c' hC hB₀ hc' k hk
  set K2 : ℝ := ((2 : ℕ).factorial : ℝ) * (2 / c) ^ 2 with hK2
  have hK20 : 0 ≤ K2 := by positivity
  set G : ℝ := (2 * (1 + k / (c / 2)) * 1) ^ (k - 1) with hG
  have hG0 : 0 ≤ G := by positivity
  set M2 : ℝ := CS * K2 * G with hM2
  have hM20 : 0 ≤ M2 := by positivity
  refine ⟨max C₀ (k / 2 * M2) + 1, max L₁ L₂, by positivity, ?_⟩
  intro g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1 σ halt n hn
  have : NeZero L := ⟨by omega⟩
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  set S := stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ with hSdef
  have hS : ∀ y, S (fun i => -y i) = S y := fun y => (stableMol_symm g L hL E m hm t σ y 0).2
  have hT := mol_taylor (by omega) S hS n hn
  -- the zero mode, uniformly in `g`
  have hmass : ‖(L : ℂ)⁻¹ * ∑ y, S y‖ ≤ C₀ * (1 - t) := by
    have h0 := H0 g hg hgC L hL (le_of_max_le_right hL₀) E hE m hm hcm t ht0 ht1 σ halt 0
      (by simp)
    have e : tensorFourier S 0 = (L : ℂ)⁻¹ * ∑ y, S y := by
      unfold tensorFourier
      simp
    have e2 : ∑ j, torusAbs L ((0 : Fin k → Fin L) j) ^ 2 = 0 := by simp [torusAbs]
    rw [e, e2, add_zero] at h0
    exact h0
  -- the second moment carries `g²`
  have hmom : (L : ℝ)⁻¹ * ∑ y, (wordDiam y : ℝ) ^ 2 * ‖S y‖ ≤ g ^ 2 * M2 := by
    have hpt := moment_pt (le_of_eq_of_le rfl one_le_two) hc hCS S
      (H g hg hgC L hL (le_of_max_le_left hL₀) E hE m hm hcm t ht0 ht1 σ)
    have hfull := mol_full_sum (L := L) (k := k) (by omega) (c := c / 2) (a := 1)
      (by positivity) le_rfl
    simp only [div_one] at hfull
    calc (L : ℝ)⁻¹ * ∑ y, (wordDiam y : ℝ) ^ 2 * ‖S y‖
        ≤ (L : ℝ)⁻¹ * ∑ y : Fin k → Fin L, g ^ 2 * (CS * K2) *
            Real.exp (-(c / 2 * wordDiam y)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hpt y) (by positivity)
      _ = (L : ℝ)⁻¹ * (g ^ 2 * (CS * K2) * ∑ y : Fin k → Fin L,
            Real.exp (-(c / 2 * wordDiam y))) := by rw [← Finset.mul_sum]
      _ ≤ (L : ℝ)⁻¹ * (g ^ 2 * (CS * K2) * (L * G)) := by gcongr
      _ = g ^ 2 * M2 := by
          rw [hM2]
          field_simp
  have hτ : 0 ≤ ∑ j, torusAbs L (n j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hδ : 0 ≤ 1 - t := by linarith
  calc ‖tensorFourier S n‖ ≤ ‖(L : ℂ)⁻¹ * ∑ y, S y‖ + (k / 2 : ℝ) * (∑ j, torusAbs L (n j) ^ 2) *
        ((L : ℝ)⁻¹ * ∑ y, (wordDiam y : ℝ) ^ 2 * ‖S y‖) := hT
    _ ≤ C₀ * (1 - t) + (k / 2 : ℝ) * (∑ j, torusAbs L (n j) ^ 2) * (g ^ 2 * M2) := by gcongr
    _ ≤ (max C₀ (k / 2 * M2) + 1) * (1 - t) +
          (max C₀ (k / 2 * M2) + 1) * (g ^ 2 * ∑ j, torusAbs L (n j) ^ 2) := by
        have h1 : C₀ ≤ max C₀ (k / 2 * M2) + 1 := by linarith [le_max_left C₀ (k / 2 * M2)]
        have h2 : k / 2 * M2 ≤ max C₀ (k / 2 * M2) + 1 := by
          linarith [le_max_right C₀ (k / 2 * M2)]
        have e : (k / 2 : ℝ) * (∑ j, torusAbs L (n j) ^ 2) * (g ^ 2 * M2) =
            (k / 2 * M2) * (g ^ 2 * ∑ j, torusAbs L (n j) ^ 2) := by ring
        rw [e]
        gcongr
    _ = (max C₀ (k / 2 * M2) + 1) * ((1 - t) + g ^ 2 * ∑ j, torusAbs L (n j) ^ 2) := by ring

end LSBA
