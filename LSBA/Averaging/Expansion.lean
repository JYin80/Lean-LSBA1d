import LSBA.Prop.Inputs

/-!
# The Gaussian expansion of the residual

The divergence form (C.1) [gc:eq:divergence] of the residual and the moment implications (7.26)
[gc:eq:residual-fixed-moment] and (5.31) [fo:eq:residual-moments] by Gaussian integration by parts
and the orbital count (C.2) [gc:eq:residual-pairing]–(C.4) [gc:eq:facecount], at a general spectral
parameter in the upper half-plane with a deterministic matrix of Dyson form and the
covariance-weighted rows as hypotheses.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Insertions of a label into a word -/

section Words

variable {α : Type*}

/-- All insertions of `y` into the word `w`, at the positions `0, …, |w|`. -/
private def insAll (y : α) : List α → List (List α)
  | [] => [[y]]
  | x :: w => (y :: x :: w) :: (insAll y w).map (x :: ·)

/-- The insertions of `y` into `w` after its first letter. -/
private def insTail (y : α) : List α → List (List α)
  | [] => []
  | x :: w => (insAll y w).map (x :: ·)

private lemma insAll_eq (y : α) (w : List α) : insAll y w = (y :: w) :: insTail y w := by
  cases w <;> rfl

private lemma insAll_map {β : Type*} (f : α → β) (y : α) (w : List α) :
    (insAll y w).map (List.map f) = insAll (f y) (w.map f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [insAll, List.map_cons, List.map_map, ← ih]
    rfl

private lemma insTail_map {β : Type*} (f : α → β) (y : α) (w : List α) :
    (insTail y w).map (List.map f) = insTail (f y) (w.map f) := by
  cases w with
  | nil => rfl
  | cons x w =>
    simp only [insTail, List.map_cons, List.map_map, ← insAll_map]
    rfl

private lemma perm_of_mem_insAll {y : α} {w v : List α} (h : v ∈ insAll y w) :
    v.Perm (y :: w) := by
  induction w generalizing v with
  | nil =>
    simp only [insAll, List.mem_singleton] at h
    subst h; rfl
  | cons x w ih =>
    simp only [insAll, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨u, hu, rfl⟩
    · rfl
    · exact ((ih hu).cons x).trans (List.Perm.swap y x w)

private lemma perm_of_mem_insTail {y : α} {w v : List α} (h : v ∈ insTail y w) :
    v.Perm (y :: w) := by
  cases w with
  | nil => simp [insTail] at h
  | cons x w =>
    simp only [insTail, List.mem_map] at h
    obtain ⟨u, hu, rfl⟩ := h
    exact ((perm_of_mem_insAll hu).cons x).trans (List.Perm.swap y x w)

private lemma head_of_mem_insTail {y x : α} {w v : List α} (h : v ∈ insTail y (x :: w)) :
    v.head? = some x := by
  simp only [insTail, List.mem_map] at h
  obtain ⟨u, -, rfl⟩ := h
  rfl

private lemma length_insAll (y : α) (w : List α) : (insAll y w).length = w.length + 1 := by
  induction w with
  | nil => rfl
  | cons x w ih => simp [insAll, ih]

private lemma length_insTail (y : α) (w : List α) : (insTail y w).length = w.length := by
  cases w with
  | nil => rfl
  | cons x w => simp [insTail, length_insAll]

/-- Inserting `a` and then `b` gives the same words, with multiplicity, as inserting `b` and then
`a`: the combinatorial form of the symmetry of second derivatives. -/
private lemma sum_insAll_comm {M : Type*} [AddCommMonoid M] (a b : α) (w : List α)
    (f : List α → M) :
    ((insAll a w).map fun v => ((insAll b v).map f).sum).sum =
      ((insAll b w).map fun v => ((insAll a v).map f).sum).sum := by
  induction w generalizing f with
  | nil =>
    simp only [insAll, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact add_comm _ _
  | cons x w ih =>
    have h := ih (fun u => f (x :: u))
    simp only [insAll, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
      List.sum_map_add] at h ⊢
    rw [h]
    abel

end Words

/-! ### Hilbert–Schmidt sums over the Hermitian basis -/

section HS

variable {W : ℕ}

/-- The squared Hilbert–Schmidt norm `Σ_{ij} |X_ij|²`. -/
private def hs (X : Matrix (Fin W) (Fin W) ℂ) : ℝ := ∑ i, ∑ j, ‖X i j‖ ^ 2

private lemma hs_nonneg (X : Matrix (Fin W) (Fin W) ℂ) : 0 ≤ hs X := by
  unfold hs; positivity

private lemma trace_mul_conjTranspose_eq_hs (X : Matrix (Fin W) (Fin W) ℂ) :
    (X * Xᴴ).trace = (hs X : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, hs]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.mul_conj']
  rfl

/-- `Σ_t ‖A T_t B‖²_HS = ‖A‖²_HS ‖B‖²_HS`, from `Σ_t T_t X T_t = (Tr X) I`. -/
private lemma sum_hs_mul_hermBasis_mul (A B : Matrix (Fin W) (Fin W) ℂ) :
    ∑ t, hs (A * hermBasis W t * B) = hs A * hs B := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← trace_mul_conjTranspose_eq_hs, Matrix.conjTranspose_mul,
    (hermBasis_isHermitian W _).eq]
  have h : ∀ t, A * hermBasis W t * B * (Bᴴ * (hermBasis W t * Aᴴ)) =
      A * (hermBasis W t * (B * Bᴴ) * hermBasis W t) * Aᴴ := by
    intro t; simp only [Matrix.mul_assoc]
  simp only [h, ← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, sum_hermBasis_mul_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  ring

/-- Expansion in the Hermitian basis: `Σ_t Tr(T_t X) T_t = X`. -/
private lemma sum_trace_smul_hermBasis (X : Matrix (Fin W) (Fin W) ℂ) :
    ∑ t, (hermBasis W t * X).trace • hermBasis W t = X := by
  ext l m
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h : ∀ i, ∑ t, ∑ j, hermBasis W t i j * X j i * hermBasis W t l m =
      ∑ j, X j i * (if i = m ∧ j = l then 1 else 0) := by
    intro i
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sum_hermBasis_apply_mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  simp only [h, mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq']

/-- Completeness in trace form: `Σ_t Tr(T_t X) Tr(T_t Y) = Tr(X Y)`. -/
private lemma sum_trace_hermBasis_mul_mul (X Y : Matrix (Fin W) (Fin W) ℂ) :
    ∑ t, (hermBasis W t * X).trace * (hermBasis W t * Y).trace = (X * Y).trace := by
  conv_rhs => rw [← sum_trace_smul_hermBasis X]
  rw [Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- Parseval for the Hermitian basis: `Σ_t |Tr(T_t R)|² = ‖R‖²_HS`. -/
private lemma sum_norm_trace_hermBasis_mul_sq (R : Matrix (Fin W) (Fin W) ℂ) :
    ∑ t, ‖(hermBasis W t * R).trace‖ ^ 2 = hs R := by
  apply Complex.ofReal_injective
  push_cast
  have h : ∀ t, ((‖(hermBasis W t * R).trace‖ : ℂ)) ^ 2 =
      (hermBasis W t * R).trace * (hermBasis W t * Rᴴ).trace := by
    intro t
    rw [← Complex.mul_conj']
    congr 1
    rw [Matrix.trace_mul_comm (hermBasis W t) Rᴴ, ← (hermBasis_isHermitian W t).eq,
      ← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose, (hermBasis_isHermitian W t).eq]
    rfl
  simp only [h, sum_trace_hermBasis_mul_mul, trace_mul_conjTranspose_eq_hs]

end HS

/-! ### Averaging out one label -/

section Finner

variable {Λ K : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype K]

private lemma sum_sum_update (l : Λ) (ψ : (Λ → K) → ℝ) :
    ∑ k : Λ → K, ∑ t : K, ψ (Function.update k l t) = Fintype.card K * ∑ k, ψ k := by
  let E := Equiv.piSplitAt l (fun _ : Λ => K)
  have hupd : ∀ k t, Function.update k l t = E.symm (t, (E k).2) := by
    intro k t
    funext j
    by_cases hj : j = l
    · subst hj; simp [E, Equiv.piSplitAt]
    · simp [E, Equiv.piSplitAt, hj]
  simp only [hupd]
  rw [← E.symm.sum_comp, ← E.symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_comm

/-- Generalized Hölder inequality over labels (Finner's inequality for a double cover): if every
label enters exactly two of the factors or none, the average of the product is at most the product
of the root mean squares. -/
private theorem finner {ι' : Type*} [Fintype ι'] [Nonempty K] :
    ∀ (m : ℕ) (D : ι' → Finset Λ) (F : ι' → (Λ → K) → ℝ),
      ∑ i, (D i).card = m →
      (∀ i k, 0 ≤ F i k) →
      (∀ i k k', (∀ l ∈ D i, k l = k' l) → F i k = F i k') →
      (∀ l, (univ.filter fun i => l ∈ D i).card = 0 ∨ (univ.filter fun i => l ∈ D i).card = 2) →
      (∑ k, ∏ i, F i k) / (Fintype.card K : ℝ) ^ Fintype.card Λ ≤
        ∏ i, Real.sqrt ((∑ k, F i k ^ 2) / (Fintype.card K : ℝ) ^ Fintype.card Λ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro D F hm hF hdep hcount
  set N : ℝ := (Fintype.card K : ℝ) ^ Fintype.card Λ with hN
  have hK : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hNpos : 0 < N := by positivity
  by_cases hD : ∀ i, D i = ∅
  · -- every factor is constant
    obtain ⟨k₀⟩ : Nonempty (Λ → K) := inferInstance
    have hc : ∀ i k, F i k = F i k₀ := fun i k =>
      hdep i k k₀ (by simp [hD i])
    simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcardf : (Fintype.card (Λ → K) : ℝ) = N := by
      rw [hN, Fintype.card_fun]; push_cast; ring
    rw [hcardf]
    have : ∀ i, Real.sqrt (N * F i k₀ ^ 2 / N) = F i k₀ := fun i => by
      rw [mul_div_cancel_left₀ _ hNpos.ne', Real.sqrt_sq (hF i k₀)]
    simp only [this]
    rw [mul_div_cancel_left₀ _ hNpos.ne']
  · simp only [not_forall] at hD
    obtain ⟨i₀, hi₀⟩ := hD
    obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.mpr hi₀
    have hl2 : (univ.filter fun i => l ∈ D i).card = 2 := by
      rcases hcount l with h | h
      · exfalso
        have : i₀ ∈ univ.filter fun i => l ∈ D i := by simp [hl]
        rw [Finset.card_eq_zero] at h
        rw [h] at this
        simp at this
      · exact h
    obtain ⟨A, B, hAB, hfil⟩ := Finset.card_eq_two.mp hl2
    have hmemAB : ∀ i, l ∈ D i ↔ i = A ∨ i = B := by
      intro i
      have : i ∈ univ.filter (fun i => l ∈ D i) ↔ i ∈ ({A, B} : Finset ι') := by rw [hfil]
      simpa using this
    let D' : ι' → Finset Λ := fun i => if i = A ∨ i = B then (D i).erase l else D i
    let F' : ι' → (Λ → K) → ℝ := fun i k =>
      if i = A ∨ i = B then
        Real.sqrt ((∑ t, F i (Function.update k l t) ^ 2) / Fintype.card K)
      else F i k
    -- the new data satisfy the hypotheses
    have hm' : ∑ i, (D' i).card + 2 = m := by
      rw [← hm]
      have hsplit : ∀ G : ι' → ℕ, ∑ i, G i = G A + G B + ∑ i ∈ (univ.erase A).erase B, G i := by
        intro G
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ A),
          ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hAB, Finset.mem_univ B⟩)]
        ring
      rw [hsplit (fun i => (D' i).card), hsplit (fun i => (D i).card)]
      have hA : (D' A).card + 1 = (D A).card := by
        simp only [D', true_or, ite_true]
        exact Finset.card_erase_add_one ((hmemAB A).mpr (Or.inl rfl))
      have hB : (D' B).card + 1 = (D B).card := by
        simp only [D', or_true, ite_true]
        exact Finset.card_erase_add_one ((hmemAB B).mpr (Or.inr rfl))
      have hrest : ∑ i ∈ (univ.erase A).erase B, (D' i).card =
          ∑ i ∈ (univ.erase A).erase B, (D i).card := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hiA : i ≠ A := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
        have hiB : i ≠ B := Finset.ne_of_mem_erase hi
        simp [D', hiA, hiB]
      rw [hrest]
      omega
    have hF' : ∀ i k, 0 ≤ F' i k := by
      intro i k
      simp only [F']
      split_ifs
      · exact Real.sqrt_nonneg _
      · exact hF i k
    have hdep' : ∀ i k k', (∀ l' ∈ D' i, k l' = k' l') → F' i k = F' i k' := by
      intro i k k' hkk
      simp only [F']
      split_ifs with hi
      · congr 1
        congr 1
        refine Finset.sum_congr rfl fun t _ => ?_
        congr 1
        refine hdep i _ _ fun l' hl' => ?_
        by_cases hll : l' = l
        · subst hll; simp
        · rw [Function.update_of_ne hll, Function.update_of_ne hll]
          refine hkk l' ?_
          simp only [D', hi, ite_true]
          exact Finset.mem_erase.mpr ⟨hll, hl'⟩
      · exact hdep i k k' fun l' hl' => hkk l' (by simpa [D', hi] using hl')
    have hcount' : ∀ l', (univ.filter fun i => l' ∈ D' i).card = 0 ∨
        (univ.filter fun i => l' ∈ D' i).card = 2 := by
      intro l'
      by_cases hll : l' = l
      · subst hll
        left
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _
        simp only [D']
        split_ifs with hi
        · simp
        · exact fun h => hi ((hmemAB i).mp h)
      · have : (univ.filter fun i => l' ∈ D' i) = univ.filter fun i => l' ∈ D i := by
          refine Finset.filter_congr fun i _ => ?_
          simp only [D']
          split_ifs <;> simp [Finset.mem_erase, hll]
        rw [this]
        exact hcount l'
    have hsq : ∀ i, ∑ k, F' i k ^ 2 = ∑ k, F i k ^ 2 := by
      intro i
      simp only [F']
      split_ifs
      · have hnn : ∀ k, 0 ≤ (∑ t, F i (Function.update k l t) ^ 2) / Fintype.card K :=
          fun k => div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hK.le
        simp only [Real.sq_sqrt (hnn _), ← Finset.sum_div]
        rw [sum_sum_update l (fun k => F i k ^ 2), mul_div_cancel_left₀ _ hK.ne']
      · rfl
    have IH := ih (∑ i, (D' i).card) (by omega) D' F' rfl hF' hdep' hcount'
    simp only [hsq] at IH
    refine le_trans ?_ IH
    -- the step: averaging out the label `l`
    refine div_le_div_of_nonneg_right ?_ hNpos.le
    have hstep : ∑ k, ∏ i, F i k =
        (Fintype.card K : ℝ)⁻¹ * ∑ k, ∑ t, ∏ i, F i (Function.update k l t) := by
      rw [sum_sum_update l (fun k => ∏ i, F i k), ← mul_assoc, inv_mul_cancel₀ hK.ne', one_mul]
    rw [hstep, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hsplitP : ∀ G : ι' → ℝ, ∏ i, G i = G A * G B * ∏ i ∈ (univ.erase A).erase B, G i := by
      intro G
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ A),
        ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hAB, Finset.mem_univ B⟩)]
      ring
    have hrestF : ∀ t, ∏ i ∈ (univ.erase A).erase B, F i (Function.update k l t) =
        ∏ i ∈ (univ.erase A).erase B, F' i k := by
      intro t
      refine Finset.prod_congr rfl fun i hi => ?_
      have hiA : i ≠ A := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      have hiB : i ≠ B := Finset.ne_of_mem_erase hi
      have hnot : l ∉ D i := fun h => by
        rcases (hmemAB i).mp h with h | h
        · exact hiA h
        · exact hiB h
      simp only [F', hiA, hiB, or_self, ite_false]
      refine hdep i _ _ fun l' hl' => ?_
      have : l' ≠ l := fun h => hnot (h ▸ hl')
      rw [Function.update_of_ne this]
    simp only [hsplitP, hrestF]
    rw [← Finset.sum_mul, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => hF' i k)
    have hFA : F' A k = Real.sqrt ((∑ t, F A (Function.update k l t) ^ 2) / Fintype.card K) := by
      simp [F']
    have hFB : F' B k = Real.sqrt ((∑ t, F B (Function.update k l t) ^ 2) / Fintype.card K) := by
      simp [F']
    rw [hFA, hFB, Real.sqrt_div' _ hK.le, Real.sqrt_div' _ hK.le, div_mul_div_comm,
      Real.mul_self_sqrt hK.le, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (by positivity)

end Finner

/-! ### Words of resolvent blocks and their orbital sums -/

section Chains

variable {W L : ℕ}

/-- The block `G_{cd}` of a matrix on `ℂ^L ⊗ ℂ^W`. -/
private def blk (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c d : Fin L) :
    Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun α β => G (c, α) (d, β)

/-- The block of the first letter of a word, and `d` for the empty word. -/
private def nbX (xs : List (Fin L × Fin W × Fin W)) (d : Fin L) : Fin L :=
  match xs with
  | [] => d
  | x :: _ => x.1

/-- The word `T_{k_0} G_{c_0 c_1} T_{k_1} ⋯ T_{k_r} G_{c_r d}` of the letters `(c_j, k_j)`. -/
private def QX (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    List (Fin L × Fin W × Fin W) → Fin L → Matrix (Fin W) (Fin W) ℂ
  | [], _ => 1
  | x :: xs, d => hermBasis W x.2 * blk G x.1 (nbX xs d) * QX G xs d

/-- The block of the first label of a word under `c`, and `d` for the empty word. -/
private def nbL {Λ : Type*} (c : Λ → Fin L) (w : List Λ) (d : Fin L) : Fin L :=
  match w with
  | [] => d
  | l :: _ => c l

/-- The product of the squared Hilbert–Schmidt norms of the blocks of a word. -/
private def PY2 (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {Λ : Type*} (c : Λ → Fin L) :
    List Λ → Fin L → ℝ
  | [], _ => 1
  | l :: w, d => hs (blk G (c l) (nbL c w d)) * PY2 G c w d

private lemma nbX_map {Λ : Type*} (c : Λ → Fin L) (k : Λ → Fin W × Fin W) (w : List Λ)
    (d : Fin L) : nbX (w.map fun l => (c l, k l)) d = nbL c w d := by
  cases w <;> rfl

private lemma QX_congr (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {Λ : Type*}
    (c : Λ → Fin L) {k k' : Λ → Fin W × Fin W} (w : List Λ) (h : ∀ l ∈ w, k l = k' l)
    (d : Fin L) :
    QX G (w.map fun l => (c l, k l)) d = QX G (w.map fun l => (c l, k' l)) d := by
  rw [List.map_congr_left fun l hl => by rw [h l hl]]

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Orbital sum of an open word: `Σ_k ‖A Q(k)‖²_HS = |K|^{|Λ| - |w|} ‖A‖²_HS Π ‖Y_j‖²_HS`. -/
private lemma sum_hs_mul_QX (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c : Λ → Fin L)
    (d : Fin L) : ∀ (w : List Λ), w.Nodup → ∀ A : Matrix (Fin W) (Fin W) ℂ,
      (∑ k : Λ → Fin W × Fin W, hs (A * QX G (w.map fun l => (c l, k l)) d)) *
          (Fintype.card (Fin W × Fin W) : ℝ) ^ w.length =
        (Fintype.card (Fin W × Fin W) : ℝ) ^ Fintype.card Λ * hs A * PY2 G c w d := by
  intro w
  induction w with
  | nil =>
    intro _ A
    simp [QX, PY2, Finset.sum_const, Finset.card_univ]
  | cons l w ih =>
    intro hw A
    rw [List.nodup_cons] at hw
    have IH := ih hw.2 (blk G (c l) (nbL c w d))
    set Y := blk G (c l) (nbL c w d)
    set κ : ℝ := (Fintype.card (Fin W × Fin W) : ℝ)
    have hrew : ∀ k : Λ → Fin W × Fin W,
        hs (A * QX G ((l :: w).map fun l => (c l, k l)) d) =
          hs (A * hermBasis W (k l) * (Y * QX G (w.map fun l => (c l, k l)) d)) := by
      intro k
      simp only [List.map_cons, QX, nbX_map, Y, Matrix.mul_assoc]
    have hupd : ∀ (k : Λ → Fin W × Fin W) (t : Fin W × Fin W),
        hs (A * hermBasis W (Function.update k l t l) *
            (Y * QX G (w.map fun l' => (c l', Function.update k l t l')) d)) =
          hs (A * hermBasis W t * (Y * QX G (w.map fun l' => (c l', k l')) d)) := by
      intro k t
      rw [Function.update_self, QX_congr G c (k := fun l' => Function.update k l t l') (k' := k) w
        (fun l' hl' => Function.update_of_ne (fun h => hw.1 (by rw [← h]; exact hl')) _ _)]
    have hsum : (∑ k : Λ → Fin W × Fin W, hs (A * QX G ((l :: w).map fun l => (c l, k l)) d)) * κ
        = hs A * ∑ k : Λ → Fin W × Fin W, hs (Y * QX G (w.map fun l => (c l, k l)) d) := by
      simp only [hrew]
      rw [mul_comm, ← sum_sum_update l]
      simp only [hupd, sum_hs_mul_hermBasis_mul, Finset.mul_sum]
    calc (∑ k : Λ → Fin W × Fin W, hs (A * QX G ((l :: w).map fun l => (c l, k l)) d)) *
          κ ^ (l :: w).length
        = ((∑ k : Λ → Fin W × Fin W, hs (A * QX G ((l :: w).map fun l => (c l, k l)) d)) * κ) *
            κ ^ w.length := by rw [List.length_cons, pow_succ]; ring
      _ = hs A * ((∑ k : Λ → Fin W × Fin W, hs (Y * QX G (w.map fun l => (c l, k l)) d)) *
            κ ^ w.length) := by rw [hsum]; ring
      _ = κ ^ Fintype.card Λ * hs A * PY2 G c (l :: w) d := by
          rw [IH]; simp only [PY2, Y]; ring

/-- Orbital sum of a closed word: `Σ_k |Tr Q(k)|² = |K|^{|Λ| - |w|} Π ‖Y_j‖²_HS`. -/
private lemma sum_norm_trace_QX_sq (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (c : Λ → Fin L) (d : Fin L) (w : List Λ) (hw : w.Nodup) (hne : w ≠ []) :
    (∑ k : Λ → Fin W × Fin W, ‖(QX G (w.map fun l => (c l, k l)) d).trace‖ ^ 2) *
        (Fintype.card (Fin W × Fin W) : ℝ) ^ w.length =
      (Fintype.card (Fin W × Fin W) : ℝ) ^ Fintype.card Λ * PY2 G c w d := by
  obtain ⟨l, w, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [List.nodup_cons] at hw
  have IH := sum_hs_mul_QX G c d w hw.2 (blk G (c l) (nbL c w d))
  set Y := blk G (c l) (nbL c w d)
  set κ : ℝ := (Fintype.card (Fin W × Fin W) : ℝ)
  have hrew : ∀ k : Λ → Fin W × Fin W,
      ‖(QX G ((l :: w).map fun l => (c l, k l)) d).trace‖ ^ 2 =
        ‖(hermBasis W (k l) * (Y * QX G (w.map fun l => (c l, k l)) d)).trace‖ ^ 2 := by
    intro k
    simp only [List.map_cons, QX, nbX_map, Y, Matrix.mul_assoc]
  have hupd : ∀ (k : Λ → Fin W × Fin W) (t : Fin W × Fin W),
      ‖(hermBasis W (Function.update k l t l) *
          (Y * QX G (w.map fun l' => (c l', Function.update k l t l')) d)).trace‖ ^ 2 =
        ‖(hermBasis W t * (Y * QX G (w.map fun l' => (c l', k l')) d)).trace‖ ^ 2 := by
    intro k t
    rw [Function.update_self, QX_congr G c (k := fun l' => Function.update k l t l') (k' := k) w
      (fun l' hl' => Function.update_of_ne (fun h => hw.1 (by rw [← h]; exact hl')) _ _)]
  have hsum : (∑ k : Λ → Fin W × Fin W,
      ‖(QX G ((l :: w).map fun l => (c l, k l)) d).trace‖ ^ 2) * κ =
        ∑ k : Λ → Fin W × Fin W, hs (Y * QX G (w.map fun l => (c l, k l)) d) := by
    simp only [hrew]
    rw [mul_comm, ← sum_sum_update l]
    simp only [hupd, sum_norm_trace_hermBasis_mul_sq]
  have hY : ∀ k : Λ → Fin W × Fin W, hs (Y * QX G (w.map fun l => (c l, k l)) d) =
      hs (1 * (Y * QX G (w.map fun l => (c l, k l)) d)) := fun k => by rw [Matrix.one_mul]
  calc (∑ k : Λ → Fin W × Fin W, ‖(QX G ((l :: w).map fun l => (c l, k l)) d).trace‖ ^ 2) *
        κ ^ (l :: w).length
      = ((∑ k : Λ → Fin W × Fin W, ‖(QX G ((l :: w).map fun l => (c l, k l)) d).trace‖ ^ 2) *
          κ) * κ ^ w.length := by rw [List.length_cons, pow_succ]; ring
    _ = (∑ k : Λ → Fin W × Fin W, hs (Y * QX G (w.map fun l => (c l, k l)) d)) *
          κ ^ w.length := by rw [hsum]
    _ = κ ^ Fintype.card Λ * PY2 G c (l :: w) d := by
        rw [IH]; simp only [PY2, Y]; ring

private lemma sum_count_eq_length (w : List Λ) : ∑ l, w.count l = w.length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.count_cons, Finset.sum_add_distrib, ih, List.length_cons, beq_iff_eq]
    simp

/-- The orbital sum of a product of closed words in which every label occurs in exactly two of
the words (the contraction (C.3) [gc:eq:orbital-contraction] without cycles of length one):
`Σ_k Π_i |Tr Q_i(k)| ≤ Π_i (Π_j ‖Y_{ij}‖²_HS)^{1/2}`. -/
private lemma orbital_bound (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c : Λ → Fin L)
    (d : Fin L) (hW : 0 < W) {p : ℕ} (w : Fin p → List Λ) (hnd : ∀ i, (w i).Nodup)
    (hne : ∀ i, w i ≠ []) (hcnt : ∀ l, ∑ i, (w i).count l = 2) :
    ∑ k : Λ → Fin W × Fin W, ∏ i, ‖(QX G ((w i).map fun l => (c l, k l)) d).trace‖ ≤
      ∏ i, Real.sqrt (PY2 G c (w i) d) := by
  have : Nonempty (Fin W × Fin W) := ⟨(⟨0, hW⟩, ⟨0, hW⟩)⟩
  set F : Fin p → (Λ → Fin W × Fin W) → ℝ := fun i k =>
    ‖(QX G ((w i).map fun l => (c l, k l)) d).trace‖ with hF
  have hκ : (Fintype.card (Fin W × Fin W) : ℝ) = (W : ℝ) ^ 2 := by
    simp [Fintype.card_prod, Fintype.card_fin, sq]
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hfin := finner (K := Fin W × Fin W) (∑ i, ((w i).toFinset).card) (fun i => (w i).toFinset)
    F rfl (fun i k => norm_nonneg _)
    (fun i k k' h => by
      simp only [hF]
      rw [QX_congr G c (w i) (fun l hl => h l (List.mem_toFinset.mpr hl))])
    (fun l => by
      right
      rw [Finset.card_filter, ← hcnt l]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hl : l ∈ w i
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (List.mem_toFinset.mpr hl)),
          List.count_eq_one_of_mem (hnd i) hl]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hl (List.mem_toFinset.mp h)),
          List.count_eq_zero_of_not_mem hl])
  have hlen : ∑ i, (w i).length = 2 * Fintype.card Λ := by
    simp only [← sum_count_eq_length]
    rw [Finset.sum_comm]
    simp [hcnt, Finset.sum_const, Finset.card_univ, mul_comm]
  have hsq : ∀ i, Real.sqrt ((∑ k, F i k ^ 2) / (Fintype.card (Fin W × Fin W) : ℝ) ^
      Fintype.card Λ) = Real.sqrt (PY2 G c (w i) d) / (W : ℝ) ^ (w i).length := by
    intro i
    have h := sum_norm_trace_QX_sq G c d (w i) (hnd i) (hne i)
    rw [hκ] at h ⊢
    have hp : (0 : ℝ) < ((W : ℝ) ^ 2) ^ Fintype.card Λ := by positivity
    have hq : (0 : ℝ) < ((W : ℝ) ^ 2) ^ (w i).length := by positivity
    have : (∑ k, F i k ^ 2) / ((W : ℝ) ^ 2) ^ Fintype.card Λ =
        PY2 G c (w i) d / ((W : ℝ) ^ (w i).length) ^ 2 := by
      have e1 : ((W : ℝ) ^ (w i).length) ^ 2 = ((W : ℝ) ^ 2) ^ (w i).length := by ring
      rw [div_eq_div_iff hp.ne' (by positivity), e1]
      simp only [hF]
      linarith [h]
    rw [this, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  simp only [hsq, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hlen] at hfin
  rw [hκ, div_le_div_iff₀ (by positivity) (by positivity)] at hfin
  have hpow : ((W : ℝ) ^ 2) ^ Fintype.card Λ = (W : ℝ) ^ (2 * Fintype.card Λ) := by
    rw [← pow_mul]
  rw [hpow] at hfin
  exact le_of_mul_le_mul_right (by simpa [hF] using hfin) (by positivity)

end Chains

/-! ### Functions of the Gaussian coordinates with polynomial growth -/

section Good

variable {ι : Type*} [Fintype ι]

/-- Polynomial growth `‖φ ω‖ ≤ C (1 + ‖ω‖)^k`. -/
private def PB (φ : (ι → ℝ) → ℂ) : Prop := ∃ C : ℝ, ∃ k : ℕ, ∀ ω, ‖φ ω‖ ≤ C * (1 + ‖ω‖) ^ k

private lemma one_add_norm_pow_mono (ω : ι → ℝ) {k k' : ℕ} (h : k ≤ k') :
    (1 + ‖ω‖) ^ k ≤ (1 + ‖ω‖) ^ k' :=
  pow_le_pow_right₀ (by linarith [norm_nonneg ω]) h

private lemma PB_const_nonneg {φ : (ι → ℝ) → ℂ} {C : ℝ} {k : ℕ}
    (h : ∀ ω, ‖φ ω‖ ≤ C * (1 + ‖ω‖) ^ k) : 0 ≤ C := by
  have h0 := h 0
  simp only [norm_zero, add_zero, one_pow, mul_one] at h0
  exact (norm_nonneg _).trans h0

private lemma PB_add {φ ψ : (ι → ℝ) → ℂ} (hφ : PB φ) (hψ : PB ψ) : PB (fun ω => φ ω + ψ ω) := by
  obtain ⟨C₁, k₁, h₁⟩ := hφ
  obtain ⟨C₂, k₂, h₂⟩ := hψ
  have hC₁ := PB_const_nonneg h₁
  have hC₂ := PB_const_nonneg h₂
  refine ⟨C₁ + C₂, k₁ + k₂, fun ω => ?_⟩
  calc ‖φ ω + ψ ω‖ ≤ ‖φ ω‖ + ‖ψ ω‖ := norm_add_le _ _
    _ ≤ C₁ * (1 + ‖ω‖) ^ k₁ + C₂ * (1 + ‖ω‖) ^ k₂ := add_le_add (h₁ ω) (h₂ ω)
    _ ≤ C₁ * (1 + ‖ω‖) ^ (k₁ + k₂) + C₂ * (1 + ‖ω‖) ^ (k₁ + k₂) :=
        add_le_add (mul_le_mul_of_nonneg_left (one_add_norm_pow_mono ω (Nat.le_add_right _ _)) hC₁)
          (mul_le_mul_of_nonneg_left (one_add_norm_pow_mono ω (Nat.le_add_left _ _)) hC₂)
    _ = (C₁ + C₂) * (1 + ‖ω‖) ^ (k₁ + k₂) := by ring

private lemma PB_mul {φ ψ : (ι → ℝ) → ℂ} (hφ : PB φ) (hψ : PB ψ) : PB (fun ω => φ ω * ψ ω) := by
  obtain ⟨C₁, k₁, h₁⟩ := hφ
  obtain ⟨C₂, k₂, h₂⟩ := hψ
  have hC₁ := PB_const_nonneg h₁
  refine ⟨C₁ * C₂, k₁ + k₂, fun ω => ?_⟩
  rw [norm_mul, pow_add]
  calc ‖φ ω‖ * ‖ψ ω‖ ≤ (C₁ * (1 + ‖ω‖) ^ k₁) * (C₂ * (1 + ‖ω‖) ^ k₂) :=
        mul_le_mul (h₁ ω) (h₂ ω) (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * ((1 + ‖ω‖) ^ k₁ * (1 + ‖ω‖) ^ k₂) := by ring

private lemma PB_const (c : ℂ) : PB (fun _ : ι → ℝ => c) :=
  ⟨‖c‖, 0, fun ω => by simp⟩

private lemma PB_coord (y : ι) : PB (fun ω : ι → ℝ => ((ω y : ℝ) : ℂ)) := by
  refine ⟨1, 1, fun ω => ?_⟩
  rw [Complex.norm_real, pow_one, one_mul]
  have := norm_le_pi_norm ω y
  linarith

private lemma PB_conj {φ : (ι → ℝ) → ℂ} (hφ : PB φ) : PB (fun ω => (starRingEnd ℂ) (φ ω)) := by
  obtain ⟨C, k, h⟩ := hφ
  exact ⟨C, k, fun ω => by rw [Complex.norm_conj]; exact h ω⟩

private lemma PB_list_sum {κ : Type*} (l : List κ) {φ : κ → (ι → ℝ) → ℂ}
    (h : ∀ j ∈ l, PB (φ j)) : PB (fun ω => (l.map fun j => φ j ω).sum) := by
  induction l with
  | nil => simpa using PB_const (ι := ι) 0
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact PB_add (h a (List.mem_cons_self ..)) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

private lemma PB_congr {φ ψ : (ι → ℝ) → ℂ} (hφ : PB φ) (h : ∀ ω, ψ ω = φ ω) : PB ψ := by
  obtain ⟨C, k, hb⟩ := hφ
  exact ⟨C, k, fun ω => by rw [h ω]; exact hb ω⟩

private lemma PB_const_mul (c : ℂ) {φ : (ι → ℝ) → ℂ} (hφ : PB φ) : PB (fun ω => c * φ ω) :=
  PB_mul (PB_const c) hφ

variable [DecidableEq ι]

/-- The partial derivative `∂_y φ`. -/
private def dd (y : ι) (φ : (ι → ℝ) → ℂ) (ω : ι → ℝ) : ℂ := fderiv ℝ φ ω (Pi.single y 1)

/-- `C¹`, with polynomial growth of the function and of its partial derivatives. -/
private def Good (φ : (ι → ℝ) → ℂ) : Prop := ContDiff ℝ 1 φ ∧ PB φ ∧ ∀ y, PB (dd y φ)

private lemma Good.differentiable' {φ : (ι → ℝ) → ℂ} (h : Good φ) : Differentiable ℝ φ :=
  h.1.differentiable one_ne_zero

private lemma dd_add {φ ψ : (ι → ℝ) → ℂ} (hφ : Good φ) (hψ : Good ψ) (y : ι) (ω : ι → ℝ) :
    dd y (fun ω => φ ω + ψ ω) ω = dd y φ ω + dd y ψ ω := by
  simp only [dd]
  rw [((hφ.differentiable' ω).hasFDerivAt.fun_add (hψ.differentiable' ω).hasFDerivAt).fderiv]
  rfl

private lemma dd_mul {φ ψ : (ι → ℝ) → ℂ} (hφ : Good φ) (hψ : Good ψ) (y : ι) (ω : ι → ℝ) :
    dd y (fun ω => φ ω * ψ ω) ω = φ ω * dd y ψ ω + ψ ω * dd y φ ω := by
  simp only [dd]
  rw [fderiv_fun_mul (hφ.differentiable' ω) (hψ.differentiable' ω)]
  rfl

omit [Fintype ι] in
private lemma dd_const (c : ℂ) (y : ι) (ω : ι → ℝ) : dd y (fun _ => c) ω = 0 := by
  simp [dd]

omit [Fintype ι] in
private lemma dd_coord (y' y : ι) (ω : ι → ℝ) :
    dd y (fun ω : ι → ℝ => ((ω y' : ℝ) : ℂ)) ω = (((Pi.single y (1 : ℝ) : ι → ℝ) y' : ℝ) : ℂ) := by
  simp only [dd]
  have h : HasFDerivAt (fun ω : ι → ℝ => ((ω y' : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) y')) ω :=
    (Complex.ofRealCLM.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) y')).hasFDerivAt
  rw [h.fderiv]
  rfl

private lemma dd_conj {φ : (ι → ℝ) → ℂ} (hφ : Good φ) (y : ι) (ω : ι → ℝ) :
    dd y (fun ω => (starRingEnd ℂ) (φ ω)) ω = (starRingEnd ℂ) (dd y φ ω) := by
  simp only [dd]
  have h : HasFDerivAt (fun ω => (starRingEnd ℂ) (φ ω))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ φ ω)) ω :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp ω (hφ.differentiable' ω).hasFDerivAt
  rw [h.fderiv]
  rfl

private lemma Good_add {φ ψ : (ι → ℝ) → ℂ} (hφ : Good φ) (hψ : Good ψ) :
    Good (fun ω => φ ω + ψ ω) :=
  ⟨hφ.1.add hψ.1, PB_add hφ.2.1 hψ.2.1, fun y =>
    PB_congr (PB_add (hφ.2.2 y) (hψ.2.2 y)) (dd_add hφ hψ y)⟩

private lemma Good_mul {φ ψ : (ι → ℝ) → ℂ} (hφ : Good φ) (hψ : Good ψ) :
    Good (fun ω => φ ω * ψ ω) :=
  ⟨hφ.1.mul hψ.1, PB_mul hφ.2.1 hψ.2.1, fun y =>
    PB_congr (PB_add (PB_mul hφ.2.1 (hψ.2.2 y)) (PB_mul hψ.2.1 (hφ.2.2 y))) (dd_mul hφ hψ y)⟩

private lemma Good_const (c : ℂ) : Good (fun _ : ι → ℝ => c) :=
  ⟨contDiff_const, PB_const c, fun y => PB_congr (PB_const 0) (dd_const c y)⟩

private lemma Good_coord (y' : ι) : Good (fun ω : ι → ℝ => ((ω y' : ℝ) : ℂ)) :=
  ⟨Complex.ofRealCLM.contDiff.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) y').contDiff,
    PB_coord y', fun y => PB_congr (PB_const _) (dd_coord y' y)⟩

private lemma Good_conj {φ : (ι → ℝ) → ℂ} (hφ : Good φ) :
    Good (fun ω => (starRingEnd ℂ) (φ ω)) :=
  ⟨(Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp hφ.1, PB_conj hφ.2.1, fun y =>
    PB_congr (PB_conj (hφ.2.2 y)) (dd_conj hφ y)⟩

private lemma Good_const_mul (c : ℂ) {φ : (ι → ℝ) → ℂ} (hφ : Good φ) :
    Good (fun ω => c * φ ω) :=
  Good_mul (Good_const c) hφ

private lemma dd_const_mul (c : ℂ) {φ : (ι → ℝ) → ℂ} (hφ : Good φ) (y : ι) (ω : ι → ℝ) :
    dd y (fun ω => c * φ ω) ω = c * dd y φ ω := by
  rw [dd_mul (Good_const c) hφ, dd_const]; ring

private lemma Good_sum {κ : Type*} (s : Finset κ) {φ : κ → (ι → ℝ) → ℂ}
    (h : ∀ j ∈ s, Good (φ j)) : Good (fun ω => ∑ j ∈ s, φ j ω) := by
  induction s using Finset.induction_on with
  | empty => simpa using Good_const (ι := ι) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact Good_add (h a (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma dd_sum {κ : Type*} (s : Finset κ) {φ : κ → (ι → ℝ) → ℂ}
    (h : ∀ j ∈ s, Good (φ j)) (y : ι) (ω : ι → ℝ) :
    dd y (fun ω => ∑ j ∈ s, φ j ω) ω = ∑ j ∈ s, dd y (φ j) ω := by
  induction s using Finset.induction_on with
  | empty => simpa using dd_const (ι := ι) 0 y ω
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [dd_add (h a (Finset.mem_insert_self _ _))
      (Good_sum s fun j hj => h j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)]

private lemma Good_list_sum {κ : Type*} (l : List κ) {φ : κ → (ι → ℝ) → ℂ}
    (h : ∀ j ∈ l, Good (φ j)) : Good (fun ω => (l.map fun j => φ j ω).sum) := by
  induction l with
  | nil => simpa using Good_const (ι := ι) 0
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Good_add (h a (List.mem_cons_self ..)) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

private lemma dd_list_sum {κ : Type*} (l : List κ) {φ : κ → (ι → ℝ) → ℂ}
    (h : ∀ j ∈ l, Good (φ j)) (y : ι) (ω : ι → ℝ) :
    dd y (fun ω => (l.map fun j => φ j ω).sum) ω = (l.map fun j => dd y (φ j) ω).sum := by
  induction l with
  | nil => simpa using dd_const (ι := ι) 0 y ω
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [dd_add (h a (List.mem_cons_self ..))
      (Good_list_sum l fun j hj => h j (List.mem_cons_of_mem _ hj)),
      ih fun j hj => h j (List.mem_cons_of_mem _ hj)]

private lemma Good_prod {κ : Type*} (s : Finset κ) {φ : κ → (ι → ℝ) → ℂ}
    (h : ∀ j ∈ s, Good (φ j)) : Good (fun ω => ∏ j ∈ s, φ j ω) := by
  induction s using Finset.induction_on with
  | empty => simpa using Good_const (ι := ι) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact Good_mul (h a (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Leibniz's rule for a finite product. -/
private lemma dd_prod {κ : Type*} [DecidableEq κ] (s : Finset κ) {φ : κ → (ι → ℝ) → ℂ}
    (h : ∀ j ∈ s, Good (φ j)) (y : ι) (ω : ι → ℝ) :
    dd y (fun ω => ∏ j ∈ s, φ j ω) ω = ∑ j ∈ s, dd y (φ j) ω * ∏ i ∈ s.erase j, φ i ω := by
  induction s using Finset.induction_on with
  | empty => simpa using dd_const (ι := ι) 1 y ω
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [dd_mul (h a (Finset.mem_insert_self _ _))
      (Good_prod s fun j hj => h j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj), Finset.sum_insert ha,
      Finset.erase_insert ha, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hja : j ≠ a := fun hja => ha (hja ▸ hj)
      rw [Finset.erase_insert_of_ne (Ne.symm hja), Finset.prod_insert
        (fun h' => ha (Finset.mem_of_mem_erase h'))]
      ring

/-! ### Integration by parts against the standard Gaussian -/

private lemma integrable_one_add_abs_pow (m : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 1) := by
  have hm : MemLp id (m : ENNReal) (gaussianReal (0 : ℝ) 1) :=
    memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) m (ENNReal.natCast_ne_top m)
  have hm' : MemLp id (m : ℕ) (gaussianReal (0 : ℝ) 1) := by simpa using hm
  have h1 : Integrable (fun x : ℝ => ‖id x‖ ^ m) (gaussianReal 0 1) := hm'.integrable_norm_pow'
  have h2 : Integrable (fun x : ℝ => (2 : ℝ) ^ m * (1 + |x| ^ m)) (gaussianReal 0 1) :=
    ((integrable_const (1 : ℝ)).add (by simpa using h1)).const_mul _
  refine h2.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ℝ => (1 + |x|) ^ m).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    have h2' : (0 : ℝ) ≤ 2 ^ m := by positivity
    have hx : (0 : ℝ) ≤ |x| ^ m := by positivity
    rcases le_total |x| 1 with h | h
    · calc (1 + |x|) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
        _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
    · calc (1 + |x|) ^ m ≤ (2 * |x|) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
        _ = 2 ^ m * |x| ^ m := by rw [mul_pow]
        _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith

omit [DecidableEq ι] in
private lemma integrable_one_add_norm_pow (m : ℕ) :
    Integrable (fun x : ι → ℝ => (1 + ‖x‖) ^ m) (stdGauss ι) := by
  have hprod : Integrable (fun x : ι → ℝ => ∏ j, (1 + |x j|) ^ m) (stdGauss ι) :=
    Integrable.fintype_prod (f := fun _ (t : ℝ) => (1 + |t|) ^ m)
      (fun _ => integrable_one_add_abs_pow m)
  refine hprod.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ι → ℝ => (1 + ‖x‖) ^ m).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity), Finset.prod_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ m
    have hone : ∀ s : Finset ι, (1 : ℝ) ≤ ∏ l ∈ s, (1 + |x l|) := fun s =>
      Finset.one_le_prod₀ fun l _ => by linarith [abs_nonneg (x l)]
    have : ‖x‖ ≤ (∏ j, (1 + |x j|)) - 1 := by
      refine (pi_norm_le_iff_of_nonneg (by linarith [hone Finset.univ])).mpr fun j => ?_
      have hj : 1 + |x j| ≤ ∏ l, (1 + |x l|) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        exact le_mul_of_one_le_right (by positivity) (hone _)
      rw [Real.norm_eq_abs]
      linarith
    linarith

omit [DecidableEq ι] in
private lemma integrable_of_PB {φ : (ι → ℝ) → ℂ} (hc : Continuous φ) (hφ : PB φ) :
    Integrable φ (stdGauss ι) := by
  obtain ⟨C, k, h⟩ := hφ
  exact ((integrable_one_add_norm_pow k).const_mul C).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall h)

private lemma Good.integrable {φ : (ι → ℝ) → ℂ} (h : Good φ) : Integrable φ (stdGauss ι) :=
  integrable_of_PB h.1.continuous h.2.1

private lemma Good.integrable_dd {φ : (ι → ℝ) → ℂ} (h : Good φ) (y : ι) :
    Integrable (dd y φ) (stdGauss ι) :=
  integrable_of_PB ((h.1.continuous_fderiv one_ne_zero).clm_apply continuous_const) (h.2.2 y)

/-- A continuous linear functional on `ℝ^ι` is bounded by the sum of its values on the basis. -/
private lemma opNorm_le_sum_single (T : (ι → ℝ) →L[ℝ] ℂ) :
    ‖T‖ ≤ ∑ y, ‖T (Pi.single y 1)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    fun v => ?_
  have hdec : T v = ∑ y, (v y : ℂ) * T (Pi.single y 1) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : (Pi.single y (v y) : ι → ℝ) = v y • Pi.single y 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this, ContinuousLinearMap.map_smul, Complex.real_smul]
  rw [hdec, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [norm_mul, Complex.norm_real, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v y) (norm_nonneg _)

/-- Gaussian integration by parts in one coordinate: `E[ω_y F] = E[∂_y F]`. -/
private lemma integral_coord_mul_eq {φ : (ι → ℝ) → ℂ} (h : Good φ) (y : ι) :
    ∫ ω, ((ω y : ℝ) : ℂ) * φ ω ∂(stdGauss ι) = ∫ ω, dd y φ ω ∂(stdGauss ι) := by
  obtain ⟨hc, ⟨C₀, k₀, h₀⟩, hd⟩ := h
  choose C k hb using hd
  have hC : ∀ y, 0 ≤ C y := fun y => PB_const_nonneg (hb y)
  set C' : ℝ := C₀ + ∑ y, C y
  set k' : ℕ := k₀ + ∑ y, k y
  have hpow : ∀ (ω : ι → ℝ) (j : ℕ), j ≤ k' → (1 + ‖ω‖) ^ j ≤ (1 + ‖ω‖) ^ k' :=
    fun ω j hj => one_add_norm_pow_mono ω hj
  refine integral_coord_mul_stdGauss φ hc (C := C') (k := k') (fun ω => ?_) (fun ω => ?_) y
  · have hC₀ := PB_const_nonneg h₀
    calc ‖φ ω‖ ≤ C₀ * (1 + ‖ω‖) ^ k₀ := h₀ ω
      _ ≤ C₀ * (1 + ‖ω‖) ^ k' :=
          mul_le_mul_of_nonneg_left (hpow ω _ (Nat.le_add_right _ _)) hC₀
      _ ≤ C' * (1 + ‖ω‖) ^ k' := by
          gcongr
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun y _ => hC y)
  · have hC₀ := PB_const_nonneg h₀
    refine (opNorm_le_sum_single _).trans ?_
    calc ∑ y, ‖fderiv ℝ φ ω (Pi.single y 1)‖ ≤ ∑ y, C y * (1 + ‖ω‖) ^ k' := by
          refine Finset.sum_le_sum fun y _ => (hb y ω).trans ?_
          exact mul_le_mul_of_nonneg_left (hpow ω _ ((Finset.single_le_sum
            (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ y)).trans (Nat.le_add_left _ _))) (hC y)
      _ = (∑ y, C y) * (1 + ‖ω‖) ^ k' := by rw [Finset.sum_mul]
      _ ≤ C' * (1 + ‖ω‖) ^ k' := by gcongr; exact le_add_of_nonneg_left hC₀

end Good

/-! ### The resolvent as a function of the Gaussian coordinates -/

section Model

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ}

/-- The basis matrix `T_{c,k}` of the Gaussian coordinate `y = (c, k)`, embedded in block `c`. -/
private def bB (y : Fin L × Fin W × Fin W) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  blockBasis W L y.1 y.2

/-- `σ = (uγ_g/W)^{1/2}`: each coordinate `ξ_λ` of (C.1) [gc:eq:divergence] is `σ` times a
standard Gaussian. -/
private def sg (W : ℕ) (g u : ℝ) : ℝ := Real.sqrt (u * gammaG g) / Real.sqrt W

/-- `B_{x_0} G B_{x_1} G ⋯ B_{x_r} G`. -/
private def pX (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (xs : List (Fin L × Fin W × Fin W)) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  (xs.map fun y => bB y * G).prod

private lemma bB_isHermitian (y : Fin L × Fin W × Fin W) : (bB y).IsHermitian :=
  blockBasis_isHermitian W L y.1 y.2

private lemma blockV_single (y : Fin L × Fin W × Fin W) :
    blockV W L (Pi.single y 1) = ((Real.sqrt W : ℝ) : ℂ)⁻¹ • bB y := by
  rw [blockV_eq_sum_blockBasis]
  congr 1
  rw [Finset.sum_eq_single y.1, Finset.sum_eq_single y.2]
  · simp [bB]
  · intro k _ hk
    have : ((y.1, k.1, k.2) : Fin L × Fin W × Fin W) ≠ y := fun h => hk (by rw [← h])
    simp [this]
  · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun k _ => ?_
    have : ((c, k.1, k.2) : Fin L × Fin W × Fin W) ≠ y := fun h => hc (by rw [← h])
    simp [this]
  · simp

private lemma blockV_add_smul (ω v : Ω W L) (t : ℝ) :
    blockV W L (ω + t • v) = blockV W L ω + (t : ℂ) • blockV W L v := by
  ext ⟨a, α⟩ ⟨b, β⟩
  simp only [blockV, blockDiagOp, gueBlock, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

private lemma flowH_line (g u : ℝ) (ω : Ω W L) (y : Fin L × Fin W × Fin W) (t : ℝ) :
    flowH g W L u (ω + t • Pi.single y 1) =
      flowH g W L u ω + (t : ℂ) • ((sg W g u : ℂ) • bB y) := by
  simp only [flowH, blockFlow, blockV_add_smul, blockV_single]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, sg]
  push_cast
  ring

private lemma sg_bB_isHermitian (g u : ℝ) (y : Fin L × Fin W × Fin W) :
    ((sg W g u : ℂ) • bB y).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (bB_isHermitian y).eq, Complex.star_def, Complex.conj_ofReal]

/-- The resolvent `G = (H_u - z)⁻¹` as a function of the coordinates. -/
private def Gr (g u : ℝ) (z : ℂ) (ω : Ω W L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  resolventMat (flowH g W L u ω) z

/-- `∂_y G = -σ G B_y G` along the line `t ↦ ω + t e_y`. -/
private lemma hasDerivAt_Gr_line (g u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (ω : Ω W L)
    (y : Fin L × Fin W × Fin W) :
    HasDerivAt (fun t : ℝ => Gr g u z (ω + t • Pi.single y 1))
      (-(sg W g u : ℂ) • (Gr g u z ω * bB y * Gr g u z ω)) 0 := by
  have h := hasDerivAt_resolventMat_line (flowH_isHermitian g W L u ω) (sg_bB_isHermitian g u y)
    hz 0
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at h
  have e : (fun t : ℝ => Gr g u z (ω + t • Pi.single y 1)) =
      fun s : ℝ => resolventMat (flowH g W L u ω + (s : ℂ) • ((sg W g u : ℂ) • bB y)) z := by
    funext t; simp only [Gr, flowH_line]
  rw [e]
  convert h using 1
  simp only [Gr, Matrix.mul_smul, Matrix.smul_mul, neg_smul]

private lemma contDiff_Gr (g u : ℝ) {z : ℂ} (hz : z.im ≠ 0) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun ω : Ω W L => Gr g u z ω) := by
  have hshift : ContDiff ℝ n (fun ω : Ω W L => flowH g W L u ω - z • (1 : Matrix _ _ ℂ)) := by
    have h : (fun ω : Ω W L => flowH g W L u ω - z • (1 : Matrix _ _ ℂ)) = fun ω =>
        (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) - z • (1 : Matrix _ _ ℂ)) +
          ((Real.sqrt (u * gammaG g) : ℝ) : ℂ) • (((Real.sqrt W : ℝ) : ℂ)⁻¹ •
          ∑ c : Fin L, ∑ k : Fin W × Fin W, (ω (c, k.1, k.2) : ℂ) • blockBasis W L c k) := by
      funext ω
      rw [flowH, blockFlow, blockV_eq_sum_blockBasis]
      abel
    rw [h]
    refine contDiff_const.add (ContDiff.const_smul _ (ContDiff.const_smul _ ?_))
    refine ContDiff.sum fun c _ => ContDiff.sum fun k _ => ?_
    exact (Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin L × Fin W × Fin W => ℝ) (c, k.1, k.2)).contDiff).smul contDiff_const
  have h : (fun ω : Ω W L => Gr g u z ω) =
      Ring.inverse ∘ (fun ω : Ω W L => flowH g W L u ω - z • (1 : Matrix _ _ ℂ)) := by
    funext ω
    exact Matrix.nonsing_inv_eq_ringInverse _
  rw [h, contDiff_iff_contDiffAt]
  intro ω
  have hu := isUnit_sub_smul_one (flowH_isHermitian g W L u ω) hz
  have h1 := contDiffAt_ringInverse ℝ (n := n) hu.unit
  rw [hu.unit_spec] at h1
  exact h1.comp ω hshift.contDiffAt

/-- An entry is bounded by the operator norm. -/
private lemma norm_entry_le_opNorm {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
  have hn : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [hn, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  convert this using 2
  simp

private lemma norm_Gr_le (g u : ℝ) {z : ℂ} (hz : 0 < z.im) (ω : Ω W L) :
    ‖Gr g u z ω‖ ≤ z.im⁻¹ :=
  norm_resolventMat_le (flowH_isHermitian g W L u ω) hz (abs_of_pos hz).ge

/-- Leibniz's rule for `B_{x_0} G ⋯ B_{x_r} G` along a line: the derivative inserts `B_y G` after
each letter. -/
private lemma hasDerivAt_pX {Gt : ℝ → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {σ : ℂ}
    {y : Fin L × Fin W × Fin W} (hG : HasDerivAt Gt (-σ • (Gt 0 * bB y * Gt 0)) 0) :
    ∀ xs : List (Fin L × Fin W × Fin W), HasDerivAt (fun t => pX (Gt t) xs)
      (-σ • ((insTail y xs).map (pX (Gt 0))).sum) 0 := by
  intro xs
  induction xs with
  | nil =>
    simp only [pX, List.map_nil, List.prod_nil, insTail, List.sum_nil, smul_zero]
    exact hasDerivAt_const _ _
  | cons x xs ih =>
    have h := (hG.const_mul (bB x)).mul ih
    have e : (fun t => pX (Gt t) (x :: xs)) = (fun t => bB x * Gt t) * fun t => pX (Gt t) xs := by
      funext t; simp [pX]
    rw [e]
    convert h using 1
    have hl : insTail y (x :: xs) = (x :: y :: xs) :: (insTail y xs).map (x :: ·) := by
      rw [insTail, insAll_eq]; rfl
    rw [hl]
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def, pX, List.prod_cons]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, ← List.sum_map_mul_left,
      Matrix.mul_assoc]
    rfl

end Model

/-! ### Words of resolvents as functions of the coordinates -/

section ModelChains

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ} (g u : ℝ) (z : ℂ) (M : Matrix (Fin L) (Fin L) ℂ) (a b : Fin L)

/-- The functional `X ↦ ⟨(M ⊗ I) X⟩_{ab}`. -/
private def trF : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => blockTr ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * X) a b
      map_add' := fun X Y => by
        simp only [blockTr, Matrix.add_apply, Finset.sum_add_distrib, mul_add]
      map_smul' := fun r X => by
        simp only [blockTr, Matrix.mul_smul, Matrix.smul_apply, RingHom.id_apply,
          Complex.real_smul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }

private lemma trF_apply (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    trF M a b X = blockTr ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * X) a b := rfl

private lemma trF_smul (c : ℂ) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    trF M a b (c • X) = c * trF M a b X := by
  simp only [trF_apply, blockTr, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

private lemma trF_list_sum (l : List (Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) :
    trF M a b l.sum = (l.map (trF M a b)).sum := by
  induction l with
  | nil => simp
  | cons X l ih => simp [map_add, ih]

/-- The word `⟨(M ⊗ I) B_{x_0} G ⋯ B_{x_r} G⟩_{ab}` as a function of the coordinates. -/
private def ch (xs : List (Fin L × Fin W × Fin W)) (ω : Ω W L) : ℂ :=
  trF M a b (pX (Gr g u z ω) xs)

private lemma contDiff_pX (hz : z.im ≠ 0) (xs : List (Fin L × Fin W × Fin W))
    {n : WithTop ℕ∞} : ContDiff ℝ n (fun ω : Ω W L => pX (Gr g u z ω) xs) := by
  induction xs with
  | nil => simpa [pX] using contDiff_const
  | cons x xs ih =>
    simp only [pX, List.map_cons, List.prod_cons]
    exact (contDiff_const.mul (contDiff_Gr g u hz)).mul ih

private lemma norm_pX_le (hz : 0 < z.im) (xs : List (Fin L × Fin W × Fin W)) :
    ∃ C : ℝ, ∀ ω : Ω W L, ‖pX (Gr g u z ω) xs‖ ≤ C := by
  induction xs with
  | nil => exact ⟨‖(1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)‖, fun ω => by simp [pX]⟩
  | cons x xs ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨‖bB x‖ * z.im⁻¹ * C, fun ω => ?_⟩
    simp only [pX, List.map_cons, List.prod_cons]
    refine (norm_mul_le _ _).trans ?_
    refine mul_le_mul ((norm_mul_le _ _).trans ?_) (hC ω) (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left (norm_Gr_le g u hz ω) (norm_nonneg _)

private lemma norm_blockTr_le (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    ‖blockTr X a b‖ ≤ ‖X‖ := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp [blockTr]
  · simp only [blockTr, norm_mul, norm_inv, Complex.norm_natCast]
    have hWr : (0 : ℝ) < W := by exact_mod_cast hW
    rw [inv_mul_le_iff₀ hWr]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ α, ‖X (a, α) (b, α)‖ ≤ ∑ _α : Fin W, ‖X‖ :=
          Finset.sum_le_sum fun α _ => norm_entry_le_opNorm X _ _
      _ = W * ‖X‖ := by simp

private lemma hasDerivAt_ch_line (hz : z.im ≠ 0) (xs : List (Fin L × Fin W × Fin W))
    (ω : Ω W L) (y : Fin L × Fin W × Fin W) :
    HasDerivAt (fun t : ℝ => ch g u z M a b xs (ω + t • Pi.single y 1))
      (-(sg W g u : ℂ) * ((insTail y xs).map fun v => ch g u z M a b v ω).sum) 0 := by
  have hG := hasDerivAt_Gr_line g u hz ω y
  have hG' : HasDerivAt (fun t : ℝ => Gr g u z (ω + t • Pi.single y 1))
      (-(sg W g u : ℂ) • (Gr g u z (ω + (0 : ℝ) • Pi.single y 1) * bB y *
        Gr g u z (ω + (0 : ℝ) • Pi.single y 1))) 0 := by
    simpa only [zero_smul, add_zero] using hG
  have h := (trF M a b).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_pX hG' xs)
  simp only [zero_smul, add_zero] at h
  have e : (trF M a b) (-(sg W g u : ℂ) • ((insTail y xs).map (pX (Gr g u z ω))).sum) =
      -(sg W g u : ℂ) * ((insTail y xs).map fun v => ch g u z M a b v ω).sum := by
    rw [trF_smul, trF_list_sum, List.map_map]
    rfl
  rw [e] at h
  exact h

private lemma contDiff_ch (hz : z.im ≠ 0) (xs : List (Fin L × Fin W × Fin W))
    {n : WithTop ℕ∞} : ContDiff ℝ n (ch g u z M a b xs) :=
  (trF M a b).contDiff.comp (contDiff_pX g u z hz xs)

private lemma dd_ch (hz : z.im ≠ 0) (xs : List (Fin L × Fin W × Fin W)) (y : Fin L × Fin W × Fin W)
    (ω : Ω W L) :
    dd y (ch g u z M a b xs) ω =
      -(sg W g u : ℂ) * ((insTail y xs).map fun v => ch g u z M a b v ω).sum := by
  have hd : DifferentiableAt ℝ (ch g u z M a b xs) ω :=
    ((contDiff_ch g u z M a b hz xs (n := 1)).differentiable one_ne_zero) ω
  have hline : HasDerivAt (fun t : ℝ => ω + t • (Pi.single y 1 : Ω W L)) (Pi.single y 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single y 1 : Ω W L)).const_add ω
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  exact h1.unique (hasDerivAt_ch_line g u z M a b hz xs ω y)

private lemma Good_ch (hz : 0 < z.im) (xs : List (Fin L × Fin W × Fin W)) :
    Good (ch g u z M a b xs) := by
  have hb : ∀ v : List (Fin L × Fin W × Fin W), PB (ch g u z M a b v) := by
    intro v
    obtain ⟨C, hC⟩ := norm_pX_le g u z hz v
    refine ⟨‖M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)‖ * C, 0, fun ω => ?_⟩
    simp only [pow_zero, mul_one, ch, trF_apply]
    refine (norm_blockTr_le _ a b).trans ((norm_mul_le _ _).trans ?_)
    exact mul_le_mul_of_nonneg_left (hC ω) (norm_nonneg _)
  refine ⟨contDiff_ch g u z M a b hz.ne' xs, hb xs, fun y => ?_⟩
  exact PB_congr (PB_const_mul (-(sg W g u : ℂ)) (PB_list_sum (insTail y xs) fun v _ => hb v))
    fun ω => dd_ch g u z M a b hz.ne' xs y ω

/-- The word or its complex conjugate. -/
private def Cb (cj : Bool) (xs : List (Fin L × Fin W × Fin W)) (ω : Ω W L) : ℂ :=
  if cj then (starRingEnd ℂ) (ch g u z M a b xs ω) else ch g u z M a b xs ω

private lemma Good_Cb (hz : 0 < z.im) (cj : Bool) (xs : List (Fin L × Fin W × Fin W)) :
    Good (Cb g u z M a b cj xs) := by
  cases cj
  · exact Good_ch g u z M a b hz xs
  · exact Good_conj (Good_ch g u z M a b hz xs)

private lemma dd_Cb (hz : 0 < z.im) (cj : Bool) (xs : List (Fin L × Fin W × Fin W))
    (y : Fin L × Fin W × Fin W) (ω : Ω W L) :
    dd y (Cb g u z M a b cj xs) ω =
      -(sg W g u : ℂ) * ((insTail y xs).map fun v => Cb g u z M a b cj v ω).sum := by
  cases cj
  · exact dd_ch g u z M a b hz.ne' xs y ω
  · have e : Cb g u z M a b true xs = fun ω => (starRingEnd ℂ) (ch g u z M a b xs ω) := rfl
    simp only [Cb, ite_true]
    rw [e, dd_conj (Good_ch g u z M a b hz xs), dd_ch g u z M a b hz.ne' xs y ω, map_mul, map_neg,
      Complex.conj_ofReal, map_list_sum, List.map_map]
    rfl

end ModelChains

/-! ### The divergence form (C.1) [gc:eq:divergence] and the cancellation of the self-derivatives -/

section Divergence

variable {W L : ℕ} (g u : ℝ) (z : ℂ) (M : Matrix (Fin L) (Fin L) ℂ) (a b : Fin L)

/-- The divergence `σ⁻¹ Σ_y (ξ_y h_y - σ² ∂_y h_y)` of (C.1) [gc:eq:divergence] for the family
`h_y` = the word `y :: xs`, written out: `Σ_y (ω_y C(y :: xs) + σ Σ_v C(y :: v))`, with `v` running
over the insertions of `y` into `xs`. -/
private def divXb (cj : Bool) (xs : List (Fin L × Fin W × Fin W)) (ω : Ω W L) : ℂ :=
  ∑ y, (((ω y : ℝ) : ℂ) * Cb g u z M a b cj (y :: xs) ω +
    (sg W g u : ℂ) * ((insAll y xs).map fun v => Cb g u z M a b cj (y :: v) ω).sum)

private lemma Good_divXb (hz : 0 < z.im) (cj : Bool) (xs : List (Fin L × Fin W × Fin W)) :
    Good (divXb g u z M a b cj xs) :=
  Good_sum _ fun y _ => Good_add (Good_mul (Good_coord y) (Good_Cb g u z M a b hz cj _))
    (Good_const_mul _ (Good_list_sum _ fun _ _ => Good_Cb g u z M a b hz cj _))

private lemma list_sum_finset_sum {κ ι' : Type*} (l : List κ) (s : Finset ι') (f : κ → ι' → ℂ) :
    (l.map fun x => ∑ j ∈ s, f x j).sum = ∑ j ∈ s, (l.map fun x => f x j).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, Finset.sum_add_distrib]

/-- `∂_y` of the divergence: `∂_y div(h) = h_y + div(∂_y h)` with `∂_y h` written as insertions. -/
private lemma dd_divXb (hz : 0 < z.im) (cj : Bool) (xs : List (Fin L × Fin W × Fin W))
    (y : Fin L × Fin W × Fin W) (ω : Ω W L) :
    dd y (divXb g u z M a b cj xs) ω = Cb g u z M a b cj (y :: xs) ω -
      (sg W g u : ℂ) * ((insAll y xs).map fun xs' => divXb g u z M a b cj xs' ω).sum := by
  set σ : ℂ := (sg W g u : ℂ)
  set C : List (Fin L × Fin W × Fin W) → Ω W L → ℂ := Cb g u z M a b cj
  have hC : ∀ w, Good (C w) := fun w => Good_Cb g u z M a b hz cj w
  have hdC : ∀ w ω, dd y (C w) ω = -σ * ((insTail y w).map fun v => C v ω).sum :=
    fun w ω => dd_Cb g u z M a b hz cj w y ω
  have hterm : ∀ y' : Fin L × Fin W × Fin W,
      dd y (fun ω => ((ω y' : ℝ) : ℂ) * C (y' :: xs) ω +
        σ * ((insAll y' xs).map fun v => C (y' :: v) ω).sum) ω =
      C (y' :: xs) ω * (((Pi.single y (1 : ℝ) : Ω W L) y' : ℝ) : ℂ) -
        σ * (((ω y' : ℝ) : ℂ) * ((insAll y xs).map fun xs' => C (y' :: xs') ω).sum +
          σ * ((insAll y' xs).map fun v => ((insAll y v).map fun w => C (y' :: w) ω).sum).sum) := by
    intro y'
    rw [dd_add (Good_mul (Good_coord y') (hC _))
        (Good_const_mul _ (Good_list_sum _ fun v _ => hC _)),
      dd_mul (Good_coord y') (hC _), dd_const_mul _ (Good_list_sum _ fun v _ => hC _),
      dd_list_sum _ (fun v _ => hC _), dd_coord, hdC]
    simp only [hdC]
    have e1 : insTail y (y' :: xs) = (insAll y xs).map (y' :: ·) := rfl
    have e2 : ∀ v, insTail y (y' :: v) = (insAll y v).map (y' :: ·) := fun v => rfl
    simp only [e1, e2, List.map_map, Function.comp_def, List.sum_map_mul_left]
    ring
  have hsingle : ∑ y' : Fin L × Fin W × Fin W,
      C (y' :: xs) ω * (((Pi.single y (1 : ℝ) : Ω W L) y' : ℝ) : ℂ) = C (y :: xs) ω := by
    rw [Finset.sum_eq_single y]
    · simp
    · intro y' _ hy'; simp [hy']
    · simp
  have hdiv : ∀ xs', divXb g u z M a b cj xs' ω = ∑ y', (((ω y' : ℝ) : ℂ) * C (y' :: xs') ω +
      σ * ((insAll y' xs').map fun v => C (y' :: v) ω).sum) := fun xs' => rfl
  have hfun : divXb g u z M a b cj xs = fun ω => ∑ y', (((ω y' : ℝ) : ℂ) * C (y' :: xs) ω +
      σ * ((insAll y' xs).map fun v => C (y' :: v) ω).sum) := rfl
  rw [hfun, dd_sum _ (fun y' _ => Good_add (Good_mul (Good_coord y') (hC _))
    (Good_const_mul _ (Good_list_sum _ fun v _ => hC _)))]
  simp only [hterm, Finset.sum_sub_distrib, hsingle, hdiv, list_sum_finset_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [sum_insAll_comm y' y xs (fun w => C (y' :: w) ω)]
  simp only [List.sum_map_add, List.sum_map_mul_left]

/-- Gaussian integration by parts against a divergence (the exact cancellation after (C.1)
[gc:eq:divergence]): `E[div(h) F] = Σ_y E[h_y ∂_y F]`. -/
private lemma integral_divXb_mul (hz : 0 < z.im) (cj : Bool) (xs : List (Fin L × Fin W × Fin W))
    {Φ : Ω W L → ℂ} (hΦ : Good Φ) :
    ∫ ω, divXb g u z M a b cj xs ω * Φ ω ∂(stdGauss (Fin L × Fin W × Fin W)) =
      ∑ y, ∫ ω, Cb g u z M a b cj (y :: xs) ω * dd y Φ ω
        ∂(stdGauss (Fin L × Fin W × Fin W)) := by
  set σ : ℂ := (sg W g u : ℂ)
  set C : List (Fin L × Fin W × Fin W) → Ω W L → ℂ := Cb g u z M a b cj
  have hC : ∀ w, Good (C w) := fun w => Good_Cb g u z M a b hz cj w
  have hS : ∀ y : Fin L × Fin W × Fin W,
      Good (fun ω => ((insAll y xs).map fun v => C (y :: v) ω).sum) :=
    fun y => Good_list_sum _ fun v _ => hC _
  have hCΦ : ∀ y : Fin L × Fin W × Fin W, Good (fun ω => C (y :: xs) ω * Φ ω) :=
    fun y => Good_mul (hC _) hΦ
  have hpt : ∀ ω, divXb g u z M a b cj xs ω * Φ ω = ∑ y,
      (((ω y : ℝ) : ℂ) * (C (y :: xs) ω * Φ ω) +
        σ * (((insAll y xs).map fun v => C (y :: v) ω).sum * Φ ω)) := by
    intro ω
    simp only [divXb, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => by ring
  have hder : ∀ (y : Fin L × Fin W × Fin W) ω, dd y (fun ω => C (y :: xs) ω * Φ ω) ω +
      σ * (((insAll y xs).map fun v => C (y :: v) ω).sum * Φ ω) = C (y :: xs) ω * dd y Φ ω := by
    intro y ω
    rw [dd_mul (hC _) hΦ, dd_Cb g u z M a b hz cj]
    have e1 : insTail y (y :: xs) = (insAll y xs).map (y :: ·) := rfl
    simp only [e1, List.map_map, Function.comp_def]
    ring
  simp only [hpt]
  rw [integral_finsetSum _ fun y _ => (Good_add (Good_mul (Good_coord y) (hCΦ y))
    (Good_const_mul σ (Good_mul (hS y) hΦ))).integrable]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_add (Good_mul (Good_coord y) (hCΦ y)).integrable
      (Good_const_mul σ (Good_mul (hS y) hΦ)).integrable,
    integral_coord_mul_eq (hCΦ y) y,
    ← integral_add ((hCΦ y).integrable_dd y) (Good_const_mul σ (Good_mul (hS y) hΦ)).integrable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => hder y ω)

end Divergence

/-! ### Terms of the expansion -/

/-- A factor of a term of the expansion of `E|R_ab|^p`: a divergence (`dv`) or a word, possibly
conjugated (`cj`), with its word `w` of labels (the leading label of a divergence is summed and is
not listed). -/
private structure Fac (e : ℕ) where
  dv : Bool
  cj : Bool
  w : List (Fin e)

/-- Relabelling `l ↦ l + 1`, freeing the label `0`. -/
private def Fac.lift {e : ℕ} (f : Fac e) : Fac (e + 1) := ⟨f.dv, f.cj, f.w.map Fin.succ⟩

/-- The derivative of a factor in the direction of the new label `0`, as a list of signed
factors: for a word, the insertions of `0` after its first letter; for a divergence, the pairing
term (a word headed by `0`) and the insertions of `0` into its word. -/
private def Fac.dfac {e : ℕ} (f : Fac e) : List (ℂ × Fac (e + 1)) :=
  if f.dv then
    ((1 : ℂ), (⟨false, f.cj, 0 :: f.w.map Fin.succ⟩ : Fac (e + 1))) ::
      (insAll 0 (f.w.map Fin.succ)).map fun v => ((-1 : ℂ), (⟨true, f.cj, v⟩ : Fac (e + 1)))
  else (insTail 0 (f.w.map Fin.succ)).map fun v => ((-1 : ℂ), (⟨false, f.cj, v⟩ : Fac (e + 1)))

/-- The term obtained from `fs` by integrating the divergence `j₀` by parts, when the derivative
in its new label `0` falls on the factor `j` and gives `f'`. -/
private def child {p e : ℕ} (fs : Fin p → Fac e) (j₀ j : Fin p) (f' : Fac (e + 1)) :
    Fin p → Fac (e + 1) :=
  fun i => if i = j₀ then ⟨false, (fs j₀).cj, 0 :: (fs j₀).w.map Fin.succ⟩
    else if i = j then f' else (fs i).lift

private lemma sum_fin_cons {e : ℕ} {β : Type*} [Fintype β] (F : (Fin (e + 1) → β) → ℂ) :
    ∑ x', F x' = ∑ y, ∑ x : Fin e → β, F (Fin.cons y x) := by
  rw [← (Fin.consEquiv fun _ => β).sum_comp, Fintype.sum_prod_type]
  rfl

private lemma sum_comm3 {X Y J : Type*} [Fintype X] [Fintype Y] (s : Finset J)
    (f : X → Y → J → ℂ) :
    ∑ x, ∑ y, ∑ j ∈ s, f x y j = ∑ j ∈ s, ∑ y, ∑ x, f x y j := by
  calc ∑ x, ∑ y, ∑ j ∈ s, f x y j = ∑ x, ∑ j ∈ s, ∑ y, f x y j :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ j ∈ s, ∑ x, ∑ y, f x y j := Finset.sum_comm
    _ = ∑ j ∈ s, ∑ y, ∑ x, f x y j := Finset.sum_congr rfl fun j _ => Finset.sum_comm

private lemma integrable_list_sum' {κ X : Type*} [MeasurableSpace X] {μ : Measure X}
    (l : List κ) (f : κ → X → ℂ) (hf : ∀ k ∈ l, Integrable (f k) μ) :
    Integrable (fun ω => (l.map fun k => f k ω).sum) μ := by
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf k (List.mem_cons_self ..)).add (ih fun k' hk' => hf k' (List.mem_cons_of_mem _ hk'))

private lemma integral_list_sum {κ X : Type*} [MeasurableSpace X] {μ : Measure X} (l : List κ)
    (f : κ → X → ℂ) (hf : ∀ k ∈ l, Integrable (f k) μ) :
    ∫ ω, (l.map fun k => f k ω).sum ∂μ = (l.map fun k => ∫ ω, f k ω ∂μ).sum := by
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (hf k (List.mem_cons_self ..))
      (integrable_list_sum' l f fun k' hk' => hf k' (List.mem_cons_of_mem _ hk')),
      ih fun k' hk' => hf k' (List.mem_cons_of_mem _ hk')]

section Config

variable {W L : ℕ} (g u : ℝ) (z : ℂ) (M : Matrix (Fin L) (Fin L) ℂ) (a b : Fin L)

/-- The value of a factor at the label values `x`: `σ^{|w|+1} div(w)` or `σ^{|w|} C(w)`. -/
private def fval {e : ℕ} (f : Fac e) (x : Fin e → Fin L × Fin W × Fin W) (ω : Ω W L) : ℂ :=
  if f.dv then (sg W g u : ℂ) ^ (f.w.length + 1) * divXb g u z M a b f.cj (f.w.map x) ω
  else (sg W g u : ℂ) ^ f.w.length * Cb g u z M a b f.cj (f.w.map x) ω

private lemma fval_lift {e : ℕ} (f : Fac e) (x : Fin e → Fin L × Fin W × Fin W)
    (y : Fin L × Fin W × Fin W) (ω : Ω W L) :
    fval g u z M a b f.lift (Fin.cons y x) ω = fval g u z M a b f x ω := by
  have h : (f.w.map Fin.succ).map (Fin.cons y x : Fin (e + 1) → Fin L × Fin W × Fin W) =
      f.w.map x := by
    rw [List.map_map]; rfl
  simp only [fval, Fac.lift, h, List.length_map]

private lemma Good_fval (hz : 0 < z.im) {e : ℕ} (f : Fac e)
    (x : Fin e → Fin L × Fin W × Fin W) : Good (fval g u z M a b f x) := by
  unfold fval
  split_ifs
  · exact Good_const_mul _ (Good_divXb g u z M a b hz _ _)
  · exact Good_const_mul _ (Good_Cb g u z M a b hz _ _)

private lemma dd_fval (hz : 0 < z.im) {e : ℕ} (f : Fac e) (x : Fin e → Fin L × Fin W × Fin W)
    (y : Fin L × Fin W × Fin W) (ω : Ω W L) :
    dd y (fval g u z M a b f x) ω =
      (f.dfac.map fun cf => cf.1 * fval g u z M a b cf.2 (Fin.cons y x) ω).sum := by
  set σ : ℂ := (sg W g u : ℂ)
  have hmap : ∀ v : List (Fin e), (v.map Fin.succ).map
      (Fin.cons y x : Fin (e + 1) → Fin L × Fin W × Fin W) = v.map x := by
    intro v; rw [List.map_map]; rfl
  rcases f with ⟨dv, cj, w⟩
  cases dv
  · -- a word
    have hfun : fval g u z M a b (⟨false, cj, w⟩ : Fac e) x =
        fun ω => σ ^ w.length * Cb g u z M a b cj (w.map x) ω := rfl
    have hlen : ∀ v ∈ insTail (0 : Fin (e + 1)) (w.map Fin.succ), v.length = w.length + 1 := by
      intro v hv
      rw [(perm_of_mem_insTail hv).length_eq]; simp
    have hR : ((Fac.dfac (⟨false, cj, w⟩ : Fac e)).map
        fun cf => cf.1 * fval g u z M a b cf.2 (Fin.cons y x) ω).sum =
        ((insTail (0 : Fin (e + 1)) (w.map Fin.succ)).map fun v =>
          (-(σ ^ (w.length + 1))) * Cb g u z M a b cj
            (v.map (Fin.cons y x : Fin (e + 1) → Fin L × Fin W × Fin W)) ω).sum := by
      simp only [Fac.dfac, Bool.false_eq_true, ite_false, List.map_map]
      refine congrArg List.sum (List.map_congr_left fun v hv => ?_)
      simp only [Function.comp_apply, fval, Bool.false_eq_true, ite_false, hlen v hv]
      ring
    have hins : insTail y (w.map x) = (insTail (0 : Fin (e + 1)) (w.map Fin.succ)).map
        (List.map (Fin.cons y x : Fin (e + 1) → Fin L × Fin W × Fin W)) := by
      rw [insTail_map, hmap]; rfl
    rw [hfun, dd_const_mul _ (Good_Cb g u z M a b hz _ _), dd_Cb g u z M a b hz, hR, hins,
      List.map_map, List.sum_map_mul_left]
    simp only [Function.comp_def]
    ring
  · -- a divergence
    have hfun : fval g u z M a b (⟨true, cj, w⟩ : Fac e) x =
        fun ω => σ ^ (w.length + 1) * divXb g u z M a b cj (w.map x) ω := rfl
    have hlen : ∀ v ∈ insAll (0 : Fin (e + 1)) (w.map Fin.succ), v.length = w.length + 1 := by
      intro v hv
      rw [(perm_of_mem_insAll hv).length_eq]; simp
    have hhead : (List.map (Fin.cons y x : Fin (e + 1) → Fin L × Fin W × Fin W)
        (0 :: w.map Fin.succ)) = y :: w.map x := by
      rw [List.map_cons, Fin.cons_zero, hmap]
    have hR : ((Fac.dfac (⟨true, cj, w⟩ : Fac e)).map
        fun cf => cf.1 * fval g u z M a b cf.2 (Fin.cons y x) ω).sum =
        σ ^ (w.length + 1) * Cb g u z M a b cj (y :: w.map x) ω +
        ((insAll (0 : Fin (e + 1)) (w.map Fin.succ)).map fun v =>
          (-(σ ^ (w.length + 2))) * divXb g u z M a b cj
            (v.map (Fin.cons y x : Fin (e + 1) → Fin L × Fin W × Fin W)) ω).sum := by
      simp only [Fac.dfac, ite_true, List.map_cons, List.sum_cons, List.map_map]
      congr 1
      · simp only [fval, Bool.false_eq_true, ite_false, hhead, List.length_cons, List.length_map]
        ring
      · refine congrArg List.sum (List.map_congr_left fun v hv => ?_)
        simp only [Function.comp_apply, fval, ite_true, hlen v hv]
        ring
    have hins : insAll y (w.map x) = (insAll (0 : Fin (e + 1)) (w.map Fin.succ)).map
        (List.map (Fin.cons y x : Fin (e + 1) → Fin L × Fin W × Fin W)) := by
      rw [insAll_map, hmap]; rfl
    rw [hfun, dd_const_mul _ (Good_divXb g u z M a b hz _ _), dd_divXb g u z M a b hz, hR, hins,
      List.map_map, List.sum_map_mul_left]
    simp only [Function.comp_def]
    ring

/-- The value `Σ_x E Π_i (factor i)(x)` of a term, summed over all values `x` of its labels. -/
private def V {p e : ℕ} (fs : Fin p → Fac e) : ℂ :=
  ∑ x : Fin e → Fin L × Fin W × Fin W,
    ∫ ω, ∏ i, fval g u z M a b (fs i) x ω ∂(stdGauss (Fin L × Fin W × Fin W))

/-- One step of the expansion (C.2) [gc:eq:residual-pairing]: integrating the divergence `j₀` by
parts, `V(fs) = Σ_{j ≠ j₀} Σ_{(s, f') ∈ ∂f_j} s V(child)`. -/
private lemma V_expand (hz : 0 < z.im) {p e : ℕ} (fs : Fin p → Fac e) (j₀ : Fin p)
    (hdv : (fs j₀).dv = true) :
    V (W := W) g u z M a b fs = ∑ j ∈ univ.erase j₀,
      ((fs j).dfac.map fun cf => cf.1 * V (W := W) g u z M a b (child fs j₀ j cf.2)).sum := by
  set σ : ℂ := (sg W g u : ℂ)
  set n₀ := (fs j₀).w.length
  set cj₀ := (fs j₀).cj
  have hG : ∀ (f : Fac e) (x : Fin e → Fin L × Fin W × Fin W), Good (fval g u z M a b f x) :=
    fun f x => Good_fval g u z M a b hz f x
  have hG' : ∀ (f : Fac (e + 1)) (x : Fin (e + 1) → Fin L × Fin W × Fin W),
      Good (fval g u z M a b f x) :=
    fun f x => Good_fval g u z M a b hz f x
  -- the value of each child
  have hchild : ∀ j ∈ univ.erase j₀, ∀ (f' : Fac (e + 1)) (x : Fin e → Fin L × Fin W × Fin W)
      (y : Fin L × Fin W × Fin W) (ω : Ω W L),
      ∏ i, fval g u z M a b (child fs j₀ j f' i) (Fin.cons y x) ω =
        σ ^ (n₀ + 1) * (Cb g u z M a b cj₀ (y :: (fs j₀).w.map x) ω *
          (fval g u z M a b f' (Fin.cons y x) ω *
            ∏ i ∈ (univ.erase j₀).erase j, fval g u z M a b (fs i) x ω)) := by
    intro j hj f' x y ω
    have hjj : j ≠ j₀ := Finset.ne_of_mem_erase hj
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j₀),
      ← Finset.mul_prod_erase _ _ hj]
    have h1 : child fs j₀ j f' j₀ = ⟨false, cj₀, 0 :: (fs j₀).w.map Fin.succ⟩ := by
      simp only [child, ↓reduceIte]
      try rfl
    have h2 : child fs j₀ j f' j = f' := by simp [child, hjj]
    have h3 : ∀ i ∈ (univ.erase j₀).erase j, fval g u z M a b (child fs j₀ j f' i) (Fin.cons y x) ω
        = fval g u z M a b (fs i) x ω := by
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      have hij₀ : i ≠ j₀ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      simp only [child, hij, hij₀, ite_false]
      exact fval_lift g u z M a b (fs i) x y ω
    rw [h1, h2, Finset.prod_congr rfl h3]
    have hmap : ((0 : Fin (e + 1)) :: (fs j₀).w.map Fin.succ).map
        (Fin.cons y x : Fin (e + 1) → Fin L × Fin W × Fin W) = y :: (fs j₀).w.map x := by
      simp only [List.map_cons, Fin.cons_zero, List.map_map]; rfl
    simp only [fval, Bool.false_eq_true, ite_false, hmap, List.length_cons, List.length_map]
    ring
  -- one integration by parts at fixed label values
  have hstep : ∀ x : Fin e → Fin L × Fin W × Fin W,
      ∫ ω, ∏ i, fval g u z M a b (fs i) x ω ∂(stdGauss (Fin L × Fin W × Fin W)) =
        ∑ y, ∑ j ∈ univ.erase j₀, ((fs j).dfac.map fun cf => cf.1 *
          ∫ ω, ∏ i, fval g u z M a b (child fs j₀ j cf.2 i) (Fin.cons y x) ω
            ∂(stdGauss (Fin L × Fin W × Fin W))).sum := by
    intro x
    set Φ : Ω W L → ℂ := fun ω => ∏ i ∈ univ.erase j₀, fval g u z M a b (fs i) x ω
    have hΦ : Good Φ := Good_prod _ fun i _ => hG _ x
    have hsplit : ∀ ω, ∏ i, fval g u z M a b (fs i) x ω =
        σ ^ (n₀ + 1) * (divXb g u z M a b cj₀ ((fs j₀).w.map x) ω * Φ ω) := by
      intro ω
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j₀)]
      simp only [fval, hdv, ite_true, Φ]
      ring
    simp only [hsplit]
    rw [integral_const_mul, integral_divXb_mul g u z M a b hz cj₀ _ hΦ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hdΦ : ∀ ω, Cb g u z M a b cj₀ (y :: (fs j₀).w.map x) ω * dd y Φ ω =
        ∑ j ∈ univ.erase j₀, ((fs j).dfac.map fun cf => cf.1 *
          (Cb g u z M a b cj₀ (y :: (fs j₀).w.map x) ω * (fval g u z M a b cf.2 (Fin.cons y x) ω *
            ∏ i ∈ (univ.erase j₀).erase j, fval g u z M a b (fs i) x ω))).sum := by
      intro ω
      rw [dd_prod _ (fun i _ => hG _ x), Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dd_fval g u z M a b hz, ← List.sum_map_mul_right, ← List.sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun cf _ => ?_)
      ring
    have hint : ∀ j ∈ univ.erase j₀, ∀ cf ∈ (fs j).dfac, Integrable (fun ω =>
        Cb g u z M a b cj₀ (y :: (fs j₀).w.map x) ω * (fval g u z M a b cf.2 (Fin.cons y x) ω *
          ∏ i ∈ (univ.erase j₀).erase j, fval g u z M a b (fs i) x ω))
          (stdGauss (Fin L × Fin W × Fin W)) := by
      intro j _ cf _
      exact (Good_mul (Good_Cb g u z M a b hz _ _) (Good_mul (hG' _ _)
        (Good_prod _ fun i _ => hG _ x))).integrable
    simp only [hdΦ]
    rw [integral_finsetSum _ (fun j hj => integrable_list_sum' _ _ fun cf hcf =>
      (hint j hj cf hcf).const_mul cf.1), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [integral_list_sum _ _ (fun cf hcf => (hint j hj cf hcf).const_mul cf.1),
      ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun cf _ => ?_)
    rw [integral_const_mul, integral_congr_ae (Filter.Eventually.of_forall
      (hchild j hj cf.2 x y)), integral_const_mul]
    ring
  simp only [V, hstep, sum_fin_cons, Finset.mul_sum, list_sum_finset_sum]
  exact sum_comm3 _ _

end Config

/-! ### Invariants of the terms and the count of the expansion -/

/-- The number of divergences of a term. -/
private def ndiv {p e : ℕ} (fs : Fin p → Fac e) : ℕ := (univ.filter fun i => (fs i).dv = true).card

/-- The structural invariants of the terms of the expansion: words without repeated labels; every
label in exactly two factors; every label the first letter of a word; words nonempty; and
`e + #divergences ≤ p`. -/
private def Inv {p e : ℕ} (fs : Fin p → Fac e) : Prop :=
  (∀ i, (fs i).w.Nodup) ∧ (∀ l, ∑ i, (fs i).w.count l = 2) ∧
    (∀ l, ∃ i, (fs i).dv = false ∧ (fs i).w.head? = some l) ∧
    (∀ i, (fs i).dv = false → (fs i).w ≠ []) ∧ e + ndiv fs ≤ p

private lemma dfac_spec {e : ℕ} (f : Fac e) (cf : ℂ × Fac (e + 1)) (hcf : cf ∈ f.dfac) :
    cf.2.w.Perm (0 :: f.w.map Fin.succ) ∧ ‖cf.1‖ = 1 ∧ cf.2.cj = f.cj ∧
      (f.dv = false → cf.2.dv = false ∧ cf.2.w.head? = (f.w.map Fin.succ).head?) ∧
      (f.dv = true → cf.2.dv = false → cf.2.w.head? = some 0) ∧
      (cf.2.dv = true → f.dv = true) := by
  rcases f with ⟨dv, cj, w⟩
  cases dv
  · simp only [Fac.dfac, Bool.false_eq_true, ite_false, List.mem_map] at hcf
    obtain ⟨v, hv, rfl⟩ := hcf
    refine ⟨perm_of_mem_insTail hv, by simp, rfl, fun _ => ⟨rfl, ?_⟩, by simp, by simp⟩
    cases w with
    | nil => simp [insTail] at hv
    | cons l w => exact head_of_mem_insTail hv
  · simp only [Fac.dfac, ite_true, List.mem_cons, List.mem_map] at hcf
    rcases hcf with rfl | ⟨v, hv, rfl⟩
    · exact ⟨List.Perm.refl _, by simp, rfl, by simp, fun _ _ => rfl, by simp⟩
    · exact ⟨perm_of_mem_insAll hv, by simp, rfl, by simp, by simp, fun _ => rfl⟩

private lemma length_dfac_le {e : ℕ} (f : Fac e) : f.dfac.length ≤ f.w.length + 2 := by
  rcases f with ⟨dv, cj, w⟩
  cases dv
  · simp [Fac.dfac, length_insTail]
  · simp [Fac.dfac, length_insAll]

private lemma count_succ_cons_zero {e : ℕ} (w : List (Fin e)) (l : Fin e) :
    (0 :: w.map Fin.succ).count l.succ = w.count l := by
  rw [List.count_cons, List.count_map_of_injective _ _ (Fin.succ_injective e)]
  simp [Ne.symm (Fin.succ_ne_zero l)]

private lemma count_zero_cons_zero {e : ℕ} (w : List (Fin e)) :
    (0 :: w.map Fin.succ).count 0 = 1 := by
  rw [List.count_cons, List.count_eq_zero_of_not_mem]
  · simp
  · simp [Fin.succ_ne_zero]

private lemma nodup_cons_zero {e : ℕ} {w : List (Fin e)} (hw : w.Nodup) :
    (0 :: w.map Fin.succ).Nodup := by
  rw [List.nodup_cons]
  exact ⟨by simp [Fin.succ_ne_zero], hw.map (Fin.succ_injective e)⟩

private lemma Inv_child {p e : ℕ} {fs : Fin p → Fac e} (hI : Inv fs) {j₀ : Fin p}
    (hdv : (fs j₀).dv = true) {j : Fin p} (hj : j ≠ j₀) {cf : ℂ × Fac (e + 1)}
    (hcf : cf ∈ (fs j).dfac) :
    Inv (child fs j₀ j cf.2) ∧ ndiv (child fs j₀ j cf.2) < ndiv fs := by
  obtain ⟨hnd, hcnt, hhead, hne, hle⟩ := hI
  obtain ⟨hperm, -, -, hplain, hdivp, hdivd⟩ := dfac_spec (fs j) cf hcf
  have hc₀ : child fs j₀ j cf.2 j₀ = ⟨false, (fs j₀).cj, 0 :: (fs j₀).w.map Fin.succ⟩ := by
    simp [child]
  have hcj : child fs j₀ j cf.2 j = cf.2 := by simp [child, hj]
  have hco : ∀ i, i ≠ j₀ → i ≠ j → child fs j₀ j cf.2 i = (fs i).lift := by
    intro i h1 h2; simp [child, h1, h2]
  -- counts of the relabelled labels
  have hsucc : ∀ (i : Fin p) (l : Fin e),
      (child fs j₀ j cf.2 i).w.count l.succ = (fs i).w.count l := by
    intro i l
    by_cases h1 : i = j₀
    · subst h1; rw [hc₀]; exact count_succ_cons_zero _ l
    · by_cases h2 : i = j
      · subst h2; rw [hcj, hperm.count_eq]; exact count_succ_cons_zero _ l
      · rw [hco i h1 h2]
        exact List.count_map_of_injective _ _ (Fin.succ_injective e) l
  have hzero : ∀ i : Fin p, (child fs j₀ j cf.2 i).w.count 0 = if i = j₀ ∨ i = j then 1 else 0 := by
    intro i
    by_cases h1 : i = j₀
    · subst h1; rw [hc₀, count_zero_cons_zero]; simp
    · by_cases h2 : i = j
      · subst h2; rw [hcj, hperm.count_eq, count_zero_cons_zero]; simp
      · rw [hco i h1 h2]
        simp only [h1, h2, or_self, ite_false, Fac.lift]
        exact List.count_eq_zero_of_not_mem (by simp [Fin.succ_ne_zero])
  -- the number of divergences drops
  have hsub : (univ.filter fun i => (child fs j₀ j cf.2 i).dv = true) ⊆
      (univ.filter fun i => (fs i).dv = true).erase j₀ := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have h1 : i ≠ j₀ := by
      rintro rfl; rw [hc₀] at hi; simp at hi
    refine Finset.mem_erase.mpr ⟨h1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    by_cases h2 : i = j
    · subst h2; rw [hcj] at hi; exact hdivd hi
    · rw [hco i h1 h2] at hi; exact hi
  have hlt : ndiv (child fs j₀ j cf.2) < ndiv fs := by
    have hmem : j₀ ∈ univ.filter fun i => (fs i).dv = true := by simp [hdv]
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hmem] at this
    have hpos : 0 < ndiv fs := Finset.card_pos.mpr ⟨j₀, hmem⟩
    unfold ndiv at hpos ⊢; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hlt⟩
  · intro i
    by_cases h1 : i = j₀
    · subst h1; rw [hc₀]; exact nodup_cons_zero (hnd _)
    · by_cases h2 : i = j
      · subst h2; rw [hcj, hperm.nodup_iff]; exact nodup_cons_zero (hnd _)
      · rw [hco i h1 h2]; exact (hnd i).map (Fin.succ_injective e)
  · intro l
    refine Fin.cases ?_ (fun l => ?_) l
    · simp only [hzero]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
      have : (univ.filter fun i : Fin p => i = j₀ ∨ i = j) = {j₀, j} := by
        ext i; simp
      rw [this, Finset.card_pair (Ne.symm hj)]
    · simp only [hsucc]; exact hcnt l
  · intro l
    refine Fin.cases ⟨j₀, by rw [hc₀], by rw [hc₀]; rfl⟩ (fun l => ?_) l
    obtain ⟨i, hi, hil⟩ := hhead l
    have h1 : i ≠ j₀ := by rintro rfl; rw [hdv] at hi; exact absurd hi (by decide)
    refine ⟨i, ?_, ?_⟩
    · by_cases h2 : i = j
      · subst h2; rw [hcj]; exact (hplain hi).1
      · rw [hco i h1 h2]; exact hi
    · by_cases h2 : i = j
      · subst h2; rw [hcj, (hplain hi).2]
        cases hw : (fs i).w with
        | nil => rw [hw] at hil; simp at hil
        | cons l' w' => rw [hw] at hil; simp at hil; simp [hil]
      · rw [hco i h1 h2]
        cases hw : (fs i).w with
        | nil => rw [hw] at hil; simp at hil
        | cons l' w' => rw [hw] at hil; simp at hil; simp [Fac.lift, hw, hil]
  · intro i hi
    by_cases h1 : i = j₀
    · subst h1; rw [hc₀]; simp
    · by_cases h2 : i = j
      · subst h2; rw [hcj] at hi ⊢
        intro h; rw [h] at hperm; exact absurd hperm.length_eq (by simp)
      · rw [hco i h1 h2] at hi ⊢
        simp only [Fac.lift, ne_eq, List.map_eq_nil_iff]
        exact hne i hi
  · calc e + 1 + ndiv (child fs j₀ j cf.2) = e + (ndiv (child fs j₀ j cf.2) + 1) := by ring
      _ ≤ e + ndiv fs := Nat.add_le_add_left hlt _
      _ ≤ p := hle

private lemma sum_length_eq {p e : ℕ} {fs : Fin p → Fac e} (hI : Inv fs) :
    ∑ i, (fs i).w.length = 2 * e := by
  simp only [← sum_count_eq_length]
  rw [Finset.sum_comm]
  simp [hI.2.1, Finset.sum_const, Finset.card_univ, mul_comm]

private lemma norm_list_sum_le' {κ : Type*} (l : List κ) (f : κ → ℂ) (c : ℝ)
    (h : ∀ k ∈ l, ‖f k‖ ≤ c) : ‖(l.map f).sum‖ ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    refine (norm_add_le _ _).trans ?_
    have := ih fun k' hk' => h k' (List.mem_cons_of_mem _ hk')
    have := h k (List.mem_cons_self ..)
    linarith

section Bound

variable {W L : ℕ} (g u : ℝ) (z : ℂ) (M : Matrix (Fin L) (Fin L) ℂ) (a b : Fin L)

/-- A term with at most `n` divergences is bounded by `(4p + 1)^n` times a bound for the terms
without divergences. -/
private theorem V_bound (hz : 0 < z.im) {p : ℕ} (Bf : ℝ) (hBf : 0 ≤ Bf)
    (hfin : ∀ e (fs : Fin p → Fac e), Inv fs → ndiv fs = 0 → ‖V (W := W) g u z M a b fs‖ ≤ Bf) :
    ∀ n e (fs : Fin p → Fac e), Inv fs → ndiv fs ≤ n →
      ‖V (W := W) g u z M a b fs‖ ≤ (4 * p + 1 : ℝ) ^ n * Bf := by
  intro n
  induction n with
  | zero =>
    intro e fs hI hn
    simpa using hfin e fs hI (by omega)
  | succ n ih =>
    intro e fs hI hn
    have hq : (1 : ℝ) ≤ 4 * p + 1 := by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    by_cases h0 : ndiv fs = 0
    · refine (hfin e fs hI h0).trans ?_
      calc Bf = 1 * Bf := (one_mul _).symm
        _ ≤ (4 * p + 1 : ℝ) ^ (n + 1) * Bf :=
            mul_le_mul_of_nonneg_right (one_le_pow₀ hq) hBf
    · obtain ⟨j₀, hj₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀
      rw [V_expand g u z M a b hz fs j₀ hj₀]
      have hterm : ∀ j ∈ univ.erase j₀, ∀ cf ∈ (fs j).dfac,
          ‖cf.1 * V (W := W) g u z M a b (child fs j₀ j cf.2)‖ ≤ (4 * p + 1 : ℝ) ^ n * Bf := by
        intro j hj cf hcf
        obtain ⟨hI', hlt⟩ := Inv_child hI hj₀ (Finset.ne_of_mem_erase hj) hcf
        rw [norm_mul, (dfac_spec (fs j) cf hcf).2.1, one_mul]
        exact ih (e + 1) _ hI' (by omega)
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j ∈ univ.erase j₀, ‖((fs j).dfac.map fun cf =>
            cf.1 * V (W := W) g u z M a b (child fs j₀ j cf.2)).sum‖
          ≤ ∑ j ∈ univ.erase j₀, ((fs j).w.length + 2 : ℝ) * ((4 * p + 1 : ℝ) ^ n * Bf) := by
            refine Finset.sum_le_sum fun j hj => (norm_list_sum_le' _ _ _ (hterm j hj)).trans ?_
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast length_dfac_le (fs j)
        _ ≤ ∑ j, ((fs j).w.length + 2 : ℝ) * ((4 * p + 1 : ℝ) ^ n * Bf) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              fun _ _ _ => by positivity
        _ = ((∑ j, (fs j).w.length : ℕ) + 2 * p : ℝ) * ((4 * p + 1 : ℝ) ^ n * Bf) := by
            rw [← Finset.sum_mul, Finset.sum_add_distrib]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ (4 * p + 1 : ℝ) * ((4 * p + 1 : ℝ) ^ n * Bf) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [sum_length_eq hI]
            have : e ≤ p := by have := hI.2.2.2.2; omega
            have : (e : ℝ) ≤ p := by exact_mod_cast this
            push_cast; linarith
        _ = (4 * p + 1 : ℝ) ^ (n + 1) * Bf := by ring

end Bound

/-! ### Block form of the words -/

section BlockForm

variable {W L : ℕ}

private lemma bB_mul_apply (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x : Fin L × Fin W × Fin W) (c : Fin L) (α : Fin W) (c' : Fin L) (γ : Fin W) :
    (bB x * G) (c, α) (c', γ) = if c = x.1 then (hermBasis W x.2 * blk G x.1 c') α γ else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hc : c = x.1
  · subst hc
    rw [ite_eq_left_of_eq_true _ _ (eq_self x.1), Finset.sum_eq_single x.1]
    · simp [bB, blockBasis, blk, Matrix.mul_apply]
    · intro c'' _ hc''; simp [bB, blockBasis, hc'']
    · simp
  · simp only [hc, ite_false]
    refine Finset.sum_eq_zero fun c'' _ => Finset.sum_eq_zero fun δ _ => ?_
    simp [bB, blockBasis, hc]

private lemma pX_apply (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (xs : List (Fin L × Fin W × Fin W)) (c : Fin L) (α : Fin W) (d : Fin L) (β : Fin W) :
    pX G xs (c, α) (d, β) = if c = nbX xs d then QX G xs d α β else 0 := by
  induction xs generalizing c α with
  | nil =>
    simp only [pX, List.map_nil, List.prod_nil, nbX, QX, Matrix.one_apply, Prod.mk.injEq]
    by_cases h : c = d <;> simp [h]
  | cons x xs ih =>
    have hp : pX G (x :: xs) = (bB x * G) * pX G xs := by simp [pX]
    rw [hp, Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [ih, bB_mul_apply, mul_ite, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_eq_single (nbX xs d)]
    · by_cases hc : c = x.1
      · simp only [hc, ite_true, nbX, QX]
        rw [Matrix.mul_apply]
      · simp [hc, nbX]
    · intro c' _ hc'; simp [hc']
    · simp

private lemma trF_pX (M : Matrix (Fin L) (Fin L) ℂ) (a b : Fin L)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (xs : List (Fin L × Fin W × Fin W)) :
    trF M a b (pX G xs) = (W : ℂ)⁻¹ * M a (nbX xs b) * (QX G xs b).trace := by
  rw [trF_apply, blockTr, mul_assoc]
  congr 1
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, pX_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, Matrix.trace, Matrix.diag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_eq_single (nbX xs b)]
  · simp
  · intro c _ hc; simp [hc]
  · simp

end BlockForm

/-! ### Moments of the blocks -/

private lemma sqrt_prod' {κ : Type*} (s : Finset κ) (f : κ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    Real.sqrt (∏ j ∈ s, f j) = ∏ j ∈ s, Real.sqrt (f j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Real.sqrt_mul (hf a), ih]

/-- A product of `m ≥ 1` nonnegative numbers is at most the sum of their `m`-th powers. -/
private lemma prod_le_sum_pow {κ : Type*} [Fintype κ] [Nonempty κ] (f : κ → ℝ)
    (hf : ∀ j, 0 ≤ f j) : ∏ j, f j ≤ ∑ j, f j ^ Fintype.card κ := by
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  calc ∏ j, f j ≤ ∏ _j : κ, f j₀ :=
        Finset.prod_le_prod₀ (fun j _ => hf j) fun j _ => hj₀ j (Finset.mem_univ j)
    _ = f j₀ ^ Fintype.card κ := by rw [Finset.prod_const, Finset.card_univ]
    _ ≤ ∑ j, f j ^ Fintype.card κ :=
        Finset.single_le_sum (f := fun j => f j ^ Fintype.card κ) (fun j _ => pow_nonneg (hf j) _)
          (Finset.mem_univ j₀)

/-- Lower moments from a higher one: `E X^m ≤ 2 B^m` if `E X^n ≤ B^n`, `m ≤ n`. -/
private lemma integral_pow_le_of_pow {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) {m n : ℕ} (hmn : m ≤ n)
    (hm : Integrable (fun x => f x ^ m) μ) (hn : Integrable (fun x => f x ^ n) μ) {B : ℝ}
    (hB : 0 < B) (h : ∫ x, f x ^ n ∂μ ≤ B ^ n) : ∫ x, f x ^ m ∂μ ≤ 2 * B ^ m := by
  have hBn : 0 < B ^ (n - m) := pow_pos hB _
  have hpt : ∀ x, f x ^ m ≤ B ^ m + f x ^ n / B ^ (n - m) := by
    intro x
    rcases le_total (f x) B with hx | hx
    · have : f x ^ m ≤ B ^ m := pow_le_pow_left₀ (hf x) hx m
      have : 0 ≤ f x ^ n / B ^ (n - m) := div_nonneg (pow_nonneg (hf x) _) hBn.le
      linarith
    · have hfx : f x ^ m * B ^ (n - m) ≤ f x ^ n := by
        calc f x ^ m * B ^ (n - m) ≤ f x ^ m * f x ^ (n - m) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB.le hx _) (pow_nonneg (hf x) _)
          _ = f x ^ n := by rw [← pow_add, Nat.add_sub_cancel' hmn]
      have : f x ^ m ≤ f x ^ n / B ^ (n - m) := by rw [le_div_iff₀ hBn]; exact hfx
      linarith [pow_nonneg hB.le m]
  calc ∫ x, f x ^ m ∂μ ≤ ∫ x, (B ^ m + f x ^ n / B ^ (n - m)) ∂μ :=
        integral_mono hm ((integrable_const _).add (hn.div_const _)) hpt
    _ = B ^ m + (∫ x, f x ^ n ∂μ) / B ^ (n - m) := by
        rw [integral_add (integrable_const _) (hn.div_const _), integral_const, integral_div]
        simp
    _ ≤ B ^ m + B ^ n / B ^ (n - m) := by gcongr
    _ = 2 * B ^ m := by
        rw [show B ^ n = B ^ m * B ^ (n - m) by rw [← pow_add, Nat.add_sub_cancel' hmn],
          mul_div_cancel_right₀ _ hBn.ne']
        ring

section Final

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ}

private lemma PY2_eq_prod (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {Λ : Type*}
    (c : Λ → Fin L) (w : List Λ) (d : Fin L) :
    PY2 G c w d = ∏ j : Fin w.length, hs (blk G (c (w.get j)) (nbL c (w.drop (j.1 + 1)) d)) := by
  induction w with
  | nil => simp [PY2]
  | cons l w ih =>
    rw [PY2, ih]
    change _ = ∏ j : Fin (w.length + 1), _
    rw [Fin.prod_univ_succ]
    simp

/-- The entry `(p, q)` as a continuous real-linear functional. -/
private def entryCLM {n : Type*} [Fintype n] [DecidableEq n] (i j : n) : Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => X i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private lemma continuous_Gr_apply (g u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (i j : Fin L × Fin W) :
    Continuous fun ω : Ω W L => Gr g u z ω i j :=
  (entryCLM i j).continuous.comp (contDiff_Gr g u hz (n := 0)).continuous

private lemma norm_Gr_apply_le (g u : ℝ) {z : ℂ} (hz : 0 < z.im) (ω : Ω W L)
    (i j : Fin L × Fin W) : ‖Gr g u z ω i j‖ ≤ z.im⁻¹ :=
  (norm_entry_le_opNorm _ i j).trans (norm_Gr_le g u hz ω)

private lemma continuous_hs_blk (g u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (c d : Fin L) :
    Continuous fun ω : Ω W L => hs (blk (Gr g u z ω) c d) := by
  unfold hs blk
  simp only [Matrix.of_apply]
  exact continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ =>
    ((continuous_Gr_apply g u hz _ _).norm).pow 2

private lemma hs_blk_le (g u : ℝ) {z : ℂ} (hz : 0 < z.im) (ω : Ω W L) (c d : Fin L) :
    hs (blk (Gr g u z ω) c d) ≤ W * W * z.im⁻¹ ^ 2 := by
  unfold hs blk
  simp only [Matrix.of_apply]
  calc ∑ α, ∑ β, ‖Gr g u z ω (c, α) (d, β)‖ ^ 2 ≤ ∑ _α : Fin W, ∑ _β : Fin W, z.im⁻¹ ^ 2 :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_Gr_apply_le g u hz ω _ _) 2
    _ = W * W * z.im⁻¹ ^ 2 := by simp; ring

/-- Moment bound for one block, `E ‖G_{cd}‖_HS^{2e} ≤ 2 (2 C K W χ)^{2e}`, from the entrywise
`L^{2p}` hypotheses of (7.26) [gc:eq:residual-fixed-moment], `e ≤ p`, and `χ ≥ W^{-1/2}`. -/
private lemma integral_hs_blk_pow_le (g u : ℝ) {z : ℂ} (hz : 0 < z.im) (hW : 1 ≤ W)
    {p e : ℕ} (he : 1 ≤ e) (hep : e ≤ p) {C K χ : ℝ} (hC : 0 < C) (hK : 1 ≤ K) (hχ : 0 < χ)
    (hWχ : 1 ≤ (W : ℝ) * χ ^ 2)
    (hG1 : ∀ c d : Fin L, ∫ ω, ‖blockTr (Gr g u z ω) c d‖ ^ (2 * p)
      ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ (C * K) ^ (2 * p))
    (hG2 : ∀ e₁ e₂ : Fin L × Fin W, ∫ ω, ‖Gr g u z ω e₁ e₂ -
      (if e₁.2 = e₂.2 then blockTr (Gr g u z ω) e₁.1 e₂.1 else 0)‖ ^ (2 * p)
      ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ (C * K * χ) ^ (2 * p))
    (c d : Fin L) :
    ∫ ω, hs (blk (Gr g u z ω) c d) ^ e ∂(stdGauss (Fin L × Fin W × Fin W)) ≤
      2 * (2 * C * K * W * χ) ^ (2 * e) := by
  set μ' := stdGauss (Fin L × Fin W × Fin W)
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  set T : Ω W L → ℝ := fun ω => ‖blockTr (Gr g u z ω) c d‖ with hT
  set Z : Fin W × Fin W → Ω W L → ℝ := fun αβ ω => ‖Gr g u z ω (c, αβ.1) (d, αβ.2) -
    (if αβ.1 = αβ.2 then blockTr (Gr g u z ω) c d else 0)‖ with hZ
  have hcT : Continuous T := by
    simp only [hT, blockTr]
    exact (continuous_const.mul (continuous_finsetSum _ fun α _ =>
      continuous_Gr_apply g u hz.ne' _ _)).norm
  have hcZ : ∀ αβ, Continuous (Z αβ) := by
    intro αβ
    simp only [hZ, blockTr]
    refine ((continuous_Gr_apply g u hz.ne' _ _).sub ?_).norm
    split_ifs
    · exact continuous_const.mul (continuous_finsetSum _ fun α _ =>
        continuous_Gr_apply g u hz.ne' _ _)
    · exact continuous_const
  have hbT : ∀ ω, T ω ≤ z.im⁻¹ := by
    intro ω
    simp only [hT]
    refine (norm_blockTr_le _ c d).trans (norm_Gr_le g u hz ω)
  have hbZ : ∀ αβ ω, Z αβ ω ≤ 2 * z.im⁻¹ := by
    intro αβ ω
    simp only [hZ]
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_Gr_apply_le g u hz ω (c, αβ.1) (d, αβ.2)
    have h2 : ‖(if αβ.1 = αβ.2 then blockTr (Gr g u z ω) c d else 0)‖ ≤ z.im⁻¹ := by
      split_ifs
      · exact hbT ω
      · rw [norm_zero]; positivity
    linarith
  have hint : ∀ {f : Ω W L → ℝ} (n : ℕ), Continuous f → (∀ ω, 0 ≤ f ω) →
      (∀ ω, f ω ≤ 2 * z.im⁻¹) → Integrable (fun ω => f ω ^ n) μ' := by
    intro f n hf h0 hb
    refine Integrable.of_bound (hf.pow n).aestronglyMeasurable ((2 * z.im⁻¹) ^ n)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (h0 ω) _)]
    exact pow_le_pow_left₀ (h0 ω) (hb ω) n
  have hbT' : ∀ ω, T ω ≤ 2 * z.im⁻¹ := fun ω =>
    (hbT ω).trans (by linarith [inv_pos.mpr hz])
  -- lower moments
  have hCK : 0 < C * K := by positivity
  have hmT : ∫ ω, T ω ^ (2 * e) ∂μ' ≤ 2 * (C * K) ^ (2 * e) :=
    integral_pow_le_of_pow (fun ω => norm_nonneg _) (by omega)
      (hint _ hcT (fun ω => norm_nonneg _) hbT') (hint _ hcT (fun ω => norm_nonneg _) hbT') hCK
      (hG1 c d)
  have hmZ : ∀ αβ, ∫ ω, Z αβ ω ^ (2 * e) ∂μ' ≤ 2 * (C * K * χ) ^ (2 * e) := fun αβ =>
    integral_pow_le_of_pow (fun ω => norm_nonneg _) (by omega)
      (hint _ (hcZ αβ) (fun ω => norm_nonneg _) (hbZ αβ))
      (hint _ (hcZ αβ) (fun ω => norm_nonneg _) (hbZ αβ)) (by positivity)
      (hG2 (c, αβ.1) (d, αβ.2))
  -- the pointwise bound
  have hpt : ∀ ω, hs (blk (Gr g u z ω) c d) ^ e ≤
      2 ^ (2 * e - 1) * ((W : ℝ) ^ e * T ω ^ (2 * e) +
        (W : ℝ) ^ (2 * e - 2) * ∑ αβ : Fin W × Fin W, Z αβ ω ^ (2 * e)) := by
    intro ω
    have h1 : hs (blk (Gr g u z ω) c d) ≤
        2 * W * T ω ^ 2 + 2 * ∑ αβ : Fin W × Fin W, Z αβ ω ^ 2 := by
      have hpair : ∀ α β : Fin W, ‖Gr g u z ω (c, α) (d, β)‖ ^ 2 ≤
          2 * ‖(if α = β then blockTr (Gr g u z ω) c d else 0)‖ ^ 2 + 2 * Z (α, β) ω ^ 2 := by
        intro α β
        have hsplit : Gr g u z ω (c, α) (d, β) =
            (if α = β then blockTr (Gr g u z ω) c d else 0) +
              (Gr g u z ω (c, α) (d, β) - (if α = β then blockTr (Gr g u z ω) c d else 0)) := by
          ring
        rw [hsplit]
        refine (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans ?_
        have := add_sq_le (a := ‖(if α = β then blockTr (Gr g u z ω) c d else 0)‖)
          (b := ‖Gr g u z ω (c, α) (d, β) - (if α = β then blockTr (Gr g u z ω) c d else 0)‖)
        simp only [hZ]
        linarith
      have hdiag : ∑ α : Fin W, ∑ β : Fin W,
          ‖(if α = β then blockTr (Gr g u z ω) c d else 0)‖ ^ 2 = W * T ω ^ 2 := by
        simp only [hT, apply_ite (fun x : ℂ => ‖x‖ ^ 2), norm_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hZsum : ∑ αβ : Fin W × Fin W, Z αβ ω ^ 2 = ∑ α : Fin W, ∑ β : Fin W, Z (α, β) ω ^ 2 :=
        Fintype.sum_prod_type _
      unfold hs blk
      simp only [Matrix.of_apply]
      calc ∑ α, ∑ β, ‖Gr g u z ω (c, α) (d, β)‖ ^ 2 ≤ ∑ α : Fin W, ∑ β : Fin W,
            (2 * ‖(if α = β then blockTr (Gr g u z ω) c d else 0)‖ ^ 2 + 2 * Z (α, β) ω ^ 2) :=
          Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hpair α β
        _ = 2 * W * T ω ^ 2 + 2 * ∑ αβ : Fin W × Fin W, Z αβ ω ^ 2 := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hdiag, hZsum]
          ring
    have hS0 : 0 ≤ ∑ αβ : Fin W × Fin W, Z αβ ω ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h2 : (∑ αβ : Fin W × Fin W, Z αβ ω ^ 2) ^ e ≤
        (W : ℝ) ^ (2 * e - 2) * ∑ αβ : Fin W × Fin W, Z αβ ω ^ (2 * e) := by
      obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
      have hj := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Fin W × Fin W)))
        (f := fun αβ => Z αβ ω ^ 2) (fun _ _ => sq_nonneg _) k
      have hcard : ((Finset.univ : Finset (Fin W × Fin W)).card : ℝ) ^ k =
          (W : ℝ) ^ (2 * (k + 1) - 2) := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
        push_cast
        rw [show 2 * (k + 1) - 2 = 2 * k by omega, pow_mul]
        ring
      rw [hcard, div_le_iff₀ (by positivity)] at hj
      calc (∑ αβ : Fin W × Fin W, Z αβ ω ^ 2) ^ (k + 1) ≤
            (∑ αβ : Fin W × Fin W, (Z αβ ω ^ 2) ^ (k + 1)) * (W : ℝ) ^ (2 * (k + 1) - 2) := hj
        _ = (W : ℝ) ^ (2 * (k + 1) - 2) * ∑ αβ : Fin W × Fin W, Z αβ ω ^ (2 * (k + 1)) := by
            rw [mul_comm]; congr 1
            refine Finset.sum_congr rfl fun αβ _ => by rw [← pow_mul]
    have hT0 : 0 ≤ T ω := norm_nonneg _
    calc hs (blk (Gr g u z ω) c d) ^ e ≤
          (2 * W * T ω ^ 2 + 2 * ∑ αβ : Fin W × Fin W, Z αβ ω ^ 2) ^ e :=
          pow_le_pow_left₀ (hs_nonneg _) h1 e
      _ ≤ 2 ^ (e - 1) * ((2 * W * T ω ^ 2) ^ e + (2 * ∑ αβ : Fin W × Fin W, Z αβ ω ^ 2) ^ e) :=
          add_pow_le (by positivity) (by positivity) e
      _ = 2 ^ (e - 1) * 2 ^ e * ((W : ℝ) ^ e * T ω ^ (2 * e) +
            (∑ αβ : Fin W × Fin W, Z αβ ω ^ 2) ^ e) := by
          rw [mul_pow, mul_pow, mul_pow, ← pow_mul]; ring
      _ ≤ 2 ^ (e - 1) * 2 ^ e * ((W : ℝ) ^ e * T ω ^ (2 * e) +
            (W : ℝ) ^ (2 * e - 2) * ∑ αβ : Fin W × Fin W, Z αβ ω ^ (2 * e)) := by gcongr
      _ = 2 ^ (2 * e - 1) * ((W : ℝ) ^ e * T ω ^ (2 * e) +
            (W : ℝ) ^ (2 * e - 2) * ∑ αβ : Fin W × Fin W, Z αβ ω ^ (2 * e)) := by
          rw [← pow_add]; congr 2; omega
  -- integrate
  have hintT := hint (2 * e) hcT (fun ω => norm_nonneg _) hbT'
  have hintZ : ∀ αβ, Integrable (fun ω => Z αβ ω ^ (2 * e)) μ' :=
    fun αβ => hint (2 * e) (hcZ αβ) (fun ω => norm_nonneg _) (hbZ αβ)
  have hintS : Integrable (fun ω => ∑ αβ : Fin W × Fin W, Z αβ ω ^ (2 * e)) μ' :=
    integrable_finsetSum _ fun αβ _ => hintZ αβ
  have hintR : Integrable (fun ω => 2 ^ (2 * e - 1) * ((W : ℝ) ^ e * T ω ^ (2 * e) +
      (W : ℝ) ^ (2 * e - 2) * ∑ αβ : Fin W × Fin W, Z αβ ω ^ (2 * e))) μ' :=
    ((hintT.const_mul _).add (hintS.const_mul _)).const_mul _
  have hintL : Integrable (fun ω => hs (blk (Gr g u z ω) c d) ^ e) μ' := by
    refine Integrable.of_bound ((continuous_hs_blk g u hz.ne' c d).pow e).aestronglyMeasurable
      ((W * W * z.im⁻¹ ^ 2) ^ e) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (hs_nonneg _) _)]
    exact pow_le_pow_left₀ (hs_nonneg _) (hs_blk_le g u hz ω c d) e
  refine (integral_mono hintL hintR hpt).trans ?_
  rw [integral_const_mul, integral_add (hintT.const_mul _) (hintS.const_mul _),
    integral_const_mul, integral_const_mul, integral_finsetSum _ fun αβ _ => hintZ αβ]
  have hsumZ : ∑ αβ : Fin W × Fin W, ∫ ω, Z αβ ω ^ (2 * e) ∂μ' ≤
      (W : ℝ) ^ 2 * (2 * (C * K * χ) ^ (2 * e)) := by
    calc ∑ αβ : Fin W × Fin W, ∫ ω, Z αβ ω ^ (2 * e) ∂μ' ≤
          ∑ _αβ : Fin W × Fin W, 2 * (C * K * χ) ^ (2 * e) := Finset.sum_le_sum fun αβ _ => hmZ αβ
      _ = (W : ℝ) ^ 2 * (2 * (C * K * χ) ^ (2 * e)) := by
          simp [Finset.card_univ, Fintype.card_prod, sq]
  have hWe : (W : ℝ) ^ e ≤ (W : ℝ) ^ (2 * e) * χ ^ (2 * e) := by
    have : (1 : ℝ) ≤ ((W : ℝ) * χ ^ 2) ^ e := one_le_pow₀ hWχ
    calc (W : ℝ) ^ e = (W : ℝ) ^ e * 1 := (mul_one _).symm
      _ ≤ (W : ℝ) ^ e * ((W : ℝ) * χ ^ 2) ^ e := mul_le_mul_of_nonneg_left this (by positivity)
      _ = (W : ℝ) ^ (2 * e) * χ ^ (2 * e) := by
          rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]; ring_nf
  have hW22 : (W : ℝ) ^ (2 * e - 2) * (W : ℝ) ^ 2 = (W : ℝ) ^ (2 * e) := by
    rw [← pow_add]; congr 1; omega
  calc 2 ^ (2 * e - 1) * ((W : ℝ) ^ e * ∫ ω, T ω ^ (2 * e) ∂μ' +
        (W : ℝ) ^ (2 * e - 2) * ∑ αβ : Fin W × Fin W, ∫ ω, Z αβ ω ^ (2 * e) ∂μ')
      ≤ 2 ^ (2 * e - 1) * ((W : ℝ) ^ e * (2 * (C * K) ^ (2 * e)) +
        (W : ℝ) ^ (2 * e - 2) * ((W : ℝ) ^ 2 * (2 * (C * K * χ) ^ (2 * e)))) := by gcongr
    _ = 2 ^ (2 * e - 1) * 2 * (C * K) ^ (2 * e) * ((W : ℝ) ^ e +
        (W : ℝ) ^ (2 * e - 2) * (W : ℝ) ^ 2 * χ ^ (2 * e)) := by rw [mul_pow (C * K)]; ring
    _ ≤ 2 ^ (2 * e - 1) * 2 * (C * K) ^ (2 * e) * ((W : ℝ) ^ (2 * e) * χ ^ (2 * e) +
        (W : ℝ) ^ (2 * e) * χ ^ (2 * e)) := by rw [hW22]; gcongr
    _ = 2 * (2 * C * K * W * χ) ^ (2 * e) := by
        have h2 : (2 : ℝ) ^ (2 * e - 1) * 2 = 2 ^ (2 * e) := by
          rw [← pow_succ]; congr 1; omega
        rw [show (2 * C * K * W * χ) ^ (2 * e) = 2 ^ (2 * e) * (C * K) ^ (2 * e) *
          ((W : ℝ) ^ (2 * e) * χ ^ (2 * e)) by ring, ← h2]
        ring

/-- `E Π_i (Π_j ‖Y_{ij}‖²_HS)^{1/2} ≤ 4e (2 C K W χ)^{2e}` for words with `2e` blocks in total. -/
private lemma integral_prod_sqrt_PY2_le (g u : ℝ) {z : ℂ} (hz : 0 < z.im) (hW : 1 ≤ W)
    {p e : ℕ} (he : 1 ≤ e) (hep : e ≤ p) {C K χ : ℝ} (hC : 0 < C) (hK : 1 ≤ K) (hχ : 0 < χ)
    (hWχ : 1 ≤ (W : ℝ) * χ ^ 2)
    (hG1 : ∀ c d : Fin L, ∫ ω, ‖blockTr (Gr g u z ω) c d‖ ^ (2 * p)
      ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ (C * K) ^ (2 * p))
    (hG2 : ∀ e₁ e₂ : Fin L × Fin W, ∫ ω, ‖Gr g u z ω e₁ e₂ -
      (if e₁.2 = e₂.2 then blockTr (Gr g u z ω) e₁.1 e₂.1 else 0)‖ ^ (2 * p)
      ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ (C * K * χ) ^ (2 * p))
    (c : Fin e → Fin L) (d : Fin L) (w : Fin p → List (Fin e))
    (hlen : ∑ i, (w i).length = 2 * e) :
    ∫ ω, ∏ i, Real.sqrt (PY2 (Gr g u z ω) c (w i) d) ∂(stdGauss (Fin L × Fin W × Fin W)) ≤
      4 * e * (2 * C * K * W * χ) ^ (2 * e) := by
  set μ' := stdGauss (Fin L × Fin W × Fin W)
  let S := Σ i : Fin p, Fin (w i).length
  let Y : S → Fin L × Fin L := fun s =>
    (c ((w s.1).get s.2), nbL c ((w s.1).drop (s.2.1 + 1)) d)
  have hcard : Fintype.card S = 2 * e := by
    simp only [S, Fintype.card_sigma, Fintype.card_fin, hlen]
  have hS : Nonempty S := Fintype.card_pos_iff.mp (by rw [hcard]; omega)
  have hprod : ∀ ω : Ω W L, ∏ i, Real.sqrt (PY2 (Gr g u z ω) c (w i) d) =
      ∏ s : S, Real.sqrt (hs (blk (Gr g u z ω) (Y s).1 (Y s).2)) := by
    intro ω
    simp only [PY2_eq_prod]
    rw [show (∏ i, Real.sqrt (∏ j : Fin (w i).length, hs (blk (Gr g u z ω) (c ((w i).get j))
        (nbL c ((w i).drop (j.1 + 1)) d)))) = ∏ i, ∏ j : Fin (w i).length,
          Real.sqrt (hs (blk (Gr g u z ω) (c ((w i).get j)) (nbL c ((w i).drop (j.1 + 1)) d)))
      from Finset.prod_congr rfl fun i _ => sqrt_prod' _ _ fun j => hs_nonneg _]
    exact (Fintype.prod_sigma' (fun i j => Real.sqrt (hs (blk (Gr g u z ω) (c ((w i).get j))
      (nbL c ((w i).drop (j.1 + 1)) d))))).symm
  simp only [hprod]
  have hcont : ∀ s : S, Continuous fun ω : Ω W L => hs (blk (Gr g u z ω) (Y s).1 (Y s).2) :=
    fun s => continuous_hs_blk g u hz.ne' _ _
  have hB : ∀ (s : S) (ω : Ω W L), hs (blk (Gr g u z ω) (Y s).1 (Y s).2) ≤ W * W * z.im⁻¹ ^ 2 :=
    fun s ω => hs_blk_le g u hz ω _ _
  have hintL : Integrable (fun ω => ∏ s : S, Real.sqrt (hs (blk (Gr g u z ω) (Y s).1 (Y s).2)))
      μ' := by
    refine Integrable.of_bound (continuous_finsetProd _ fun s _ =>
      Real.continuous_sqrt.comp (hcont s)).aestronglyMeasurable
      (Real.sqrt (W * W * z.im⁻¹ ^ 2) ^ Fintype.card S) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Finset.prod_nonneg fun s _ => Real.sqrt_nonneg _)]
    calc ∏ s : S, Real.sqrt (hs (blk (Gr g u z ω) (Y s).1 (Y s).2)) ≤
          ∏ _s : S, Real.sqrt (W * W * z.im⁻¹ ^ 2) :=
        Finset.prod_le_prod₀ (fun s _ => Real.sqrt_nonneg _)
          fun s _ => Real.sqrt_le_sqrt (hB s ω)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ]
  have hintP : ∀ s : S, Integrable (fun ω => hs (blk (Gr g u z ω) (Y s).1 (Y s).2) ^ e) μ' := by
    intro s
    refine Integrable.of_bound ((hcont s).pow e).aestronglyMeasurable ((W * W * z.im⁻¹ ^ 2) ^ e)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (hs_nonneg _) _)]
    exact pow_le_pow_left₀ (hs_nonneg _) (hB s ω) e
  have hpt : ∀ ω : Ω W L, ∏ s : S, Real.sqrt (hs (blk (Gr g u z ω) (Y s).1 (Y s).2)) ≤
      ∑ s : S, hs (blk (Gr g u z ω) (Y s).1 (Y s).2) ^ e := by
    intro ω
    refine (prod_le_sum_pow _ fun s => Real.sqrt_nonneg _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hcard, pow_mul, Real.sq_sqrt (hs_nonneg _)]
  refine (integral_mono hintL (integrable_finsetSum _ fun s _ => hintP s) hpt).trans ?_
  rw [integral_finsetSum _ fun s _ => hintP s]
  calc ∑ s : S, ∫ ω, hs (blk (Gr g u z ω) (Y s).1 (Y s).2) ^ e ∂μ' ≤
        ∑ _s : S, 2 * (2 * C * K * W * χ) ^ (2 * e) :=
      Finset.sum_le_sum fun s _ => integral_hs_blk_pow_le g u hz hW he hep hC hK hχ hWχ hG1 hG2 _ _
    _ = 4 * e * (2 * C * K * W * χ) ^ (2 * e) := by
        rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]; push_cast; ring

private lemma sum_arrow_prod {e : ℕ} {β γ : Type*} [Fintype β] [Fintype γ]
    (F : (Fin e → β × γ) → ℝ) :
    ∑ x, F x = ∑ c : Fin e → β, ∑ k : Fin e → γ, F fun l => (c l, k l) := by
  rw [← (Equiv.arrowProdEquivProdArrow (Fin e) (fun _ => β) (fun _ => γ)).symm.sum_comp,
    Fintype.sum_prod_type]
  rfl

private lemma norm_Cb (g u : ℝ) (z : ℂ) (M : Matrix (Fin L) (Fin L) ℂ) (a b : Fin L) (cj : Bool)
    (xs : List (Fin L × Fin W × Fin W)) (ω : Ω W L) :
    ‖Cb g u z M a b cj xs ω‖ = ‖ch g u z M a b xs ω‖ := by
  cases cj <;> simp [Cb]

/-- The terms of (C.2) [gc:eq:residual-pairing] without divergences, bounded as in (C.4)
[gc:eq:facecount]: the block labels are summed with the rows (6.13) [gc:eq:residual-row-bounds],
the orbital labels by Hilbert–Schmidt norms, and each such term is at most
`4p Γ^p max(1, 2C)^{2p} (K²χ²)^p`. -/
private theorem V_final (g u : ℝ) (z : ℂ) (M : Matrix (Fin L) (Fin L) ℂ) (a b : Fin L)
    (hz : 0 < z.im) (hu : 0 ≤ u) (hW : 1 ≤ W) {p : ℕ} (hp : 1 ≤ p) {C Γ K χ : ℝ} (hC : 0 < C)
    (hΓ : 0 ≤ Γ) (hK : 1 ≤ K) (hχ : 0 < χ) (hWχ : 1 ≤ (W : ℝ) * χ ^ 2)
    (hM : ∀ c, ‖M a c‖ ≤ Γ) (hrow : u * gammaG g * ∑ c, ‖M a c‖ ≤ Γ)
    (hG1 : ∀ c d : Fin L, ∫ ω, ‖blockTr (Gr g u z ω) c d‖ ^ (2 * p)
      ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ (C * K) ^ (2 * p))
    (hG2 : ∀ e₁ e₂ : Fin L × Fin W, ∫ ω, ‖Gr g u z ω e₁ e₂ -
      (if e₁.2 = e₂.2 then blockTr (Gr g u z ω) e₁.1 e₂.1 else 0)‖ ^ (2 * p)
      ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ (C * K * χ) ^ (2 * p))
    {e : ℕ} (fs : Fin p → Fac e) (hI : Inv fs) (h0 : ndiv fs = 0) :
    ‖V (W := W) g u z M a b fs‖ ≤
      4 * p * Γ ^ p * (max 1 (2 * C)) ^ (2 * p) * (K ^ 2 * χ ^ 2) ^ p := by
  set μ' := stdGauss (Fin L × Fin W × Fin W)
  obtain ⟨hnd, hcnt, hhead, hne, hle⟩ := hI
  have hplain : ∀ i, (fs i).dv = false := by
    intro i
    have : (univ.filter fun i => (fs i).dv = true) = ∅ := Finset.card_eq_zero.mp h0
    have hi : i ∉ univ.filter fun i => (fs i).dv = true := by rw [this]; simp
    simpa using hi
  have hne' : ∀ i, (fs i).w ≠ [] := fun i => hne i (hplain i)
  have hlen : ∑ i, (fs i).w.length = 2 * e := sum_length_eq ⟨hnd, hcnt, hhead, hne, hle⟩
  have hep : e ≤ p := by omega
  have he : 1 ≤ e := by
    obtain ⟨l, -⟩ := List.exists_mem_of_ne_nil _ (hne' ⟨0, hp⟩)
    exact Nat.one_le_iff_ne_zero.mpr fun h => by subst h; exact Fin.elim0 l
  set σ : ℝ := sg W g u
  set β : ℝ := u * gammaG g
  have hγ : 0 < gammaG g := by
    unfold gammaG
    have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  have hβ : 0 ≤ β := mul_nonneg hu hγ.le
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hσ0 : 0 ≤ σ := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hσ2 : σ ^ 2 = β / W := by
    rw [show σ = Real.sqrt β / Real.sqrt W from rfl, div_pow, Real.sq_sqrt hβ,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ W)]
  -- heads of the words
  let h : Fin p → Fin e := fun i => (fs i).w.head (hne' i)
  have hhead' : ∀ (c : Fin e → Fin L) (k : Fin e → Fin W × Fin W) (i : Fin p),
      nbX ((fs i).w.map fun l => (c l, k l)) b = c (h i) := by
    intro c k i
    rw [nbX_map]
    obtain ⟨l, w', hw⟩ := List.exists_cons_of_ne_nil (hne' i)
    simp only [h, hw, nbL, List.head_cons]
  -- the integrand, pointwise
  set A : (Fin e → Fin L) → ℝ := fun c => ∏ i, ‖M a (c (h i))‖ with hA
  set P : (Fin e → Fin L) → Ω W L → ℝ :=
    fun c ω => ∏ i, Real.sqrt (PY2 (Gr g u z ω) c (fs i).w b) with hP
  have hpt : ∀ ω : Ω W L, ∑ x, ‖∏ i, fval g u z M a b (fs i) x ω‖ ≤
      σ ^ (2 * e) * ((W : ℝ)⁻¹) ^ p * ∑ c, A c * P c ω := by
    intro ω
    rw [sum_arrow_prod, Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have heq : ∀ k : Fin e → Fin W × Fin W,
        ‖∏ i, fval g u z M a b (fs i) (fun l => (c l, k l)) ω‖ = σ ^ (2 * e) * ((W : ℝ)⁻¹) ^ p *
          (A c * ∏ i, ‖(QX (Gr g u z ω) ((fs i).w.map fun l => (c l, k l)) b).trace‖) := by
      intro k
      rw [norm_prod]
      have hf : ∀ i, ‖fval g u z M a b (fs i) (fun l => (c l, k l)) ω‖ = σ ^ (fs i).w.length *
          ((W : ℝ)⁻¹ * (‖M a (c (h i))‖ *
            ‖(QX (Gr g u z ω) ((fs i).w.map fun l => (c l, k l)) b).trace‖)) := by
        intro i
        simp only [fval, hplain i, Bool.false_eq_true, ite_false, norm_mul, norm_pow,
          Complex.norm_real, Real.norm_eq_abs, norm_Cb, ch, trF_pX, hhead', norm_inv,
          Complex.norm_natCast]
        rw [show sg W g u = σ from rfl, abs_of_nonneg hσ0]
        ring
      simp only [hf, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hlen, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, hA]
      ring
    have hσW : 0 ≤ σ ^ (2 * e) * ((W : ℝ)⁻¹) ^ p := by positivity
    calc ∑ k : Fin e → Fin W × Fin W, ‖∏ i, fval g u z M a b (fs i) (fun l => (c l, k l)) ω‖
        = ∑ k : Fin e → Fin W × Fin W, σ ^ (2 * e) * ((W : ℝ)⁻¹) ^ p *
          (A c * ∏ i, ‖(QX (Gr g u z ω) ((fs i).w.map fun l => (c l, k l)) b).trace‖) :=
          Finset.sum_congr rfl fun k _ => heq k
      _ = σ ^ (2 * e) * ((W : ℝ)⁻¹) ^ p * (A c * ∑ k : Fin e → Fin W × Fin W,
          ∏ i, ‖(QX (Gr g u z ω) ((fs i).w.map fun l => (c l, k l)) b).trace‖) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ σ ^ (2 * e) * ((W : ℝ)⁻¹) ^ p * (A c * P c ω) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (orbital_bound (Gr g u z ω) c b (by omega) (fun i => (fs i).w) hnd hne' hcnt)
            (Finset.prod_nonneg fun i _ => norm_nonneg _)) hσW
  -- integrability
  have hGood : ∀ x : Fin e → Fin L × Fin W × Fin W,
      Good (fun ω => ∏ i, fval g u z M a b (fs i) x ω) :=
    fun x => Good_prod _ fun i _ => Good_fval g u z M a b hz _ x
  have hcontP : ∀ c, Continuous (P c) := by
    intro c
    simp only [hP, PY2_eq_prod]
    exact continuous_finsetProd _ fun i _ => Real.continuous_sqrt.comp
      (continuous_finsetProd _ fun j _ => continuous_hs_blk g u hz.ne' _ _)
  have hboundP : ∀ c ω, ‖P c ω‖ ≤
      ∏ i : Fin p, Real.sqrt ((W * W * z.im⁻¹ ^ 2) ^ (fs i).w.length) := by
    intro c ω
    rw [Real.norm_of_nonneg (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _)]
    refine Finset.prod_le_prod₀ (fun i _ => Real.sqrt_nonneg _) fun i _ => Real.sqrt_le_sqrt ?_
    rw [PY2_eq_prod]
    calc ∏ j : Fin (fs i).w.length, hs (blk (Gr g u z ω) (c ((fs i).w.get j))
          (nbL c ((fs i).w.drop (j.1 + 1)) b)) ≤ ∏ _j : Fin (fs i).w.length, W * W * z.im⁻¹ ^ 2 :=
        Finset.prod_le_prod₀ (fun j _ => hs_nonneg _) fun j _ => hs_blk_le g u hz ω _ _
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hintP : ∀ c, Integrable (P c) μ' := fun c =>
    Integrable.of_bound (hcontP c).aestronglyMeasurable _ (Filter.Eventually.of_forall (hboundP c))
  have hintR : Integrable (fun ω => σ ^ (2 * e) * ((W : ℝ)⁻¹) ^ p * ∑ c, A c * P c ω) μ' :=
    (integrable_finsetSum _ fun c _ => (hintP c).const_mul _).const_mul _
  -- the integrated bound
  have hD : ∀ c, ∫ ω, P c ω ∂μ' ≤ 4 * e * (2 * C * K * W * χ) ^ (2 * e) := fun c =>
    integral_prod_sqrt_PY2_le g u hz hW he hep hC hK hχ hWχ hG1 hG2 c b _ hlen
  have hA0 : ∀ c, 0 ≤ A c := fun c => Finset.prod_nonneg fun i _ => norm_nonneg _
  have step1 : ‖V (W := W) g u z M a b fs‖ ≤
      σ ^ (2 * e) * ((W : ℝ)⁻¹) ^ p * ∑ c, A c * (4 * e * (2 * C * K * W * χ) ^ (2 * e)) := by
    calc ‖V (W := W) g u z M a b fs‖ ≤ ∑ x, ‖∫ ω, ∏ i, fval g u z M a b (fs i) x ω ∂μ'‖ :=
          norm_sum_le _ _
      _ ≤ ∑ x, ∫ ω, ‖∏ i, fval g u z M a b (fs i) x ω‖ ∂μ' :=
          Finset.sum_le_sum fun x _ => norm_integral_le_integral_norm _
      _ = ∫ ω, ∑ x, ‖∏ i, fval g u z M a b (fs i) x ω‖ ∂μ' :=
          (integral_finsetSum _ fun x _ => (hGood x).integrable.norm).symm
      _ ≤ ∫ ω, σ ^ (2 * e) * ((W : ℝ)⁻¹) ^ p * ∑ c, A c * P c ω ∂μ' :=
          integral_mono (integrable_finsetSum _ fun x _ => (hGood x).integrable.norm) hintR hpt
      _ = σ ^ (2 * e) * ((W : ℝ)⁻¹) ^ p * ∑ c, A c * ∫ ω, P c ω ∂μ' := by
          rw [integral_const_mul, integral_finsetSum _ fun c _ => (hintP c).const_mul _]
          simp only [integral_const_mul]
      _ ≤ σ ^ (2 * e) * ((W : ℝ)⁻¹) ^ p * ∑ c, A c * (4 * e * (2 * C * K * W * χ) ^ (2 * e)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ =>
            mul_le_mul_of_nonneg_left (hD c) (hA0 c)) (by positivity)
  -- the block sums
  set N : Fin e → ℕ := fun l => Fintype.card {i // h i = l} with hN
  have hNpos : ∀ l, 1 ≤ N l := by
    intro l
    obtain ⟨i, hi, hil⟩ := hhead l
    have : h i = l := by
      obtain ⟨l', w', hw⟩ := List.exists_cons_of_ne_nil (hne' i)
      simp only [hw, List.head?_cons, Option.some.injEq] at hil
      simp only [h, hw, List.head_cons, hil]
    exact Fintype.card_pos_iff.mpr ⟨⟨i, this⟩⟩
  have hNsum : ∑ l, N l = p := by
    simp only [hN, Fintype.card_eq_sum_ones]
    rw [Fintype.sum_fiberwise h (fun _ => (1 : ℕ))]
    simp
  have hAc : ∀ c : Fin e → Fin L, A c = ∏ l, ‖M a (c l)‖ ^ N l := by
    intro c
    simp only [hA, hN]
    rw [← Fintype.prod_fiberwise' h (fun l => ‖M a (c l)‖)]
    simp [Finset.prod_const, Finset.card_univ]
  have hrow' : ∀ n : ℕ, 1 ≤ n → β * ∑ c', ‖M a c'‖ ^ n ≤ Γ ^ n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    calc β * ∑ c', ‖M a c'‖ ^ (m + 1) ≤ β * ∑ c', Γ ^ m * ‖M a c'‖ := by
          gcongr with c'
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM c') m)
            (norm_nonneg _)
      _ = Γ ^ m * (β * ∑ c', ‖M a c'‖) := by rw [← Finset.mul_sum]; ring
      _ ≤ Γ ^ m * Γ := mul_le_mul_of_nonneg_left hrow (pow_nonneg hΓ _)
      _ = Γ ^ (m + 1) := (pow_succ _ _).symm
  have hsumA : β ^ e * ∑ c, A c ≤ Γ ^ p := by
    simp only [hAc]
    rw [← Fintype.prod_sum (fun l c' => ‖M a c'‖ ^ N l)]
    calc β ^ e * ∏ l : Fin e, ∑ c', ‖M a c'‖ ^ N l = ∏ l : Fin e, (β * ∑ c', ‖M a c'‖ ^ N l) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ l : Fin e, Γ ^ N l :=
          Finset.prod_le_prod₀ (fun l _ => mul_nonneg hβ (Finset.sum_nonneg fun _ _ =>
            pow_nonneg (norm_nonneg _) _)) fun l _ => hrow' (N l) (hNpos l)
      _ = Γ ^ p := by rw [Finset.prod_pow_eq_pow_sum, hNsum]
  -- final arithmetic
  refine step1.trans ?_
  have hWpos : (0 : ℝ) < W := by linarith
  have hσe : σ ^ (2 * e) = β ^ e * ((W : ℝ)⁻¹) ^ e := by
    rw [pow_mul, hσ2, div_eq_mul_inv, mul_pow]
  have hmax : 1 ≤ max 1 (2 * C) := le_max_left _ _
  have hKm : 1 ≤ max 1 (2 * C) * K := one_le_mul_of_one_le_of_one_le hmax hK
  have h2CK : (2 * C * K) ^ (2 * e) ≤ (max 1 (2 * C) * K) ^ (2 * p) :=
    (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by linarith)) _).trans (pow_le_pow_right₀ hKm (by omega))
  have hWe : (W : ℝ) ^ e * χ ^ (2 * e) ≤ (W : ℝ) ^ p * χ ^ (2 * p) := by
    have := pow_le_pow_right₀ hWχ hep
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul] at this
    exact this
  have hpow : (2 * C * K * W * χ) ^ (2 * e) =
      (2 * C * K) ^ (2 * e) * ((W : ℝ) ^ e) ^ 2 * χ ^ (2 * e) := by
    rw [← pow_mul, mul_comm e 2, ← mul_pow, ← mul_pow]
  have hWe0 : (0 : ℝ) < (W : ℝ) ^ e := by positivity
  have hWp0 : (0 : ℝ) < (W : ℝ) ^ p := by positivity
  have hsA0 : 0 ≤ β ^ e * ∑ c, A c := mul_nonneg (pow_nonneg hβ _)
    (Finset.sum_nonneg fun c _ => hA0 c)
  rw [← Finset.sum_mul, hσe, hpow, inv_pow, inv_pow]
  calc β ^ e * ((W : ℝ) ^ e)⁻¹ * ((W : ℝ) ^ p)⁻¹ *
        ((∑ c, A c) * (4 * e * ((2 * C * K) ^ (2 * e) * ((W : ℝ) ^ e) ^ 2 * χ ^ (2 * e))))
      = (β ^ e * ∑ c, A c) * (4 * e) * (2 * C * K) ^ (2 * e) *
          (((W : ℝ) ^ e * χ ^ (2 * e)) / (W : ℝ) ^ p) := by
        field_simp
    _ ≤ Γ ^ p * (4 * p) * (max 1 (2 * C) * K) ^ (2 * p) *
          (((W : ℝ) ^ p * χ ^ (2 * p)) / (W : ℝ) ^ p) := by
        have h4e : (4 * e : ℝ) ≤ 4 * p := by
          have : (e : ℝ) ≤ p := by exact_mod_cast hep
          linarith
        refine mul_le_mul (mul_le_mul (mul_le_mul hsumA h4e (by positivity) (by positivity))
          h2CK (by positivity) (by positivity)) (div_le_div_of_nonneg_right hWe hWp0.le)
          (by positivity) (by positivity)
    _ = 4 * p * Γ ^ p * (max 1 (2 * C)) ^ (2 * p) * (K ^ 2 * χ ^ 2) ^ p := by
        rw [show ((W : ℝ) ^ p * χ ^ (2 * p)) / (W : ℝ) ^ p = χ ^ (2 * p) from by field_simp,
          mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 p]
        ring

end Final

/-! ### The residual in divergence form -/

section Residual

variable {W L : ℕ} (g u : ℝ) (z : ℂ) (M : Matrix (Fin L) (Fin L) ℂ) (a b : Fin L)

/-- `Σ_y T_y X T_y = W diag(⟨X⟩_{cc} I_W)`, the identity `Σ_α T_α A T_α = (Tr A) I` blockwise. -/
private lemma sum_bB_mul_bB (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    ∑ y : Fin L × Fin W × Fin W, bB y * X * bB y =
      (W : ℂ) • Matrix.diagonal (fun x : Fin L × Fin W => blockTr X x.1 x.1) := by
  ext ⟨c₁, α⟩ ⟨c₂, β⟩
  rw [Matrix.sum_apply, Fintype.sum_prod_type]
  have hent : ∀ (c : Fin L) (k : Fin W × Fin W), (bB (c, k) * X * bB (c, k)) (c₁, α) (c₂, β) =
      if c₁ = c ∧ c₂ = c then (hermBasis W k * blk X c c * hermBasis W k) α β else 0 := by
    intro c k
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [bB_mul_apply]
    by_cases h1 : c₁ = c
    · subst h1
      rw [Finset.sum_eq_single c₁]
      · by_cases h2 : c₂ = c₁
        · subst h2
          simp only [and_self, ite_true, Matrix.mul_apply]
          refine Finset.sum_congr rfl fun γ _ => ?_
          simp [bB, blockBasis]
        · simp only [h2, and_false, ite_false]
          refine Finset.sum_eq_zero fun γ _ => ?_
          simp [bB, blockBasis, h2]
      · intro d _ hd
        refine Finset.sum_eq_zero fun γ _ => ?_
        simp [bB, blockBasis, hd]
      · simp
    · simp only [h1, false_and, ite_false]
      refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun γ _ => ?_
      simp
  simp only [hent]
  rw [Finset.sum_eq_single c₁]
  · simp only [true_and]
    by_cases h2 : c₂ = c₁
    · subst h2
      simp only [ite_true]
      rw [← Matrix.sum_apply, sum_hermBasis_mul_mul]
      simp only [Matrix.smul_apply, Matrix.diagonal_apply, Prod.mk.injEq, true_and, smul_eq_mul,
        Matrix.one_apply]
      by_cases hαβ : α = β
      · subst hαβ
        simp only [ite_true, mul_one, blockTr, Matrix.trace, Matrix.diag, blk, Matrix.of_apply]
        have hW : (W : ℂ) ≠ 0 ∨ W = 0 := by
          by_cases h : W = 0
          · exact Or.inr h
          · exact Or.inl (by exact_mod_cast h)
        rcases hW with hW | hW
        · field_simp
        · subst hW; exact Fin.elim0 α
      · simp [hαβ]
    · simp only [h2, ite_false, Matrix.smul_apply, Matrix.diagonal_apply]
      simp [Ne.symm h2, Finset.sum_const_zero]
  · intro c _ hc
    simp [Ne.symm hc]
  · simp

private lemma sum_coord_smul_bB (ω : Ω W L) (hW : 1 ≤ W) :
    ∑ y : Fin L × Fin W × Fin W, ((ω y : ℝ) : ℂ) • bB y =
      ((Real.sqrt W : ℝ) : ℂ) • blockV W L ω := by
  have hsW : ((Real.sqrt W : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt W := Real.sqrt_pos.mpr (by exact_mod_cast hW)
    exact_mod_cast this.ne'
  rw [blockV_eq_sum_blockBasis, smul_smul, mul_inv_cancel₀ hsW, one_smul, Fintype.sum_prod_type]
  rfl

/-- The divergence form (C.1) [gc:eq:divergence] of the residual:
`⟨(M ⊗ I) Π(G)⟩_{ab} = σ div(f)`, `f_y = ⟨(M ⊗ I) T_y G⟩_{ab}`. -/
private lemma residual_eq_divXb (hu : 0 ≤ u) (hW : 1 ≤ W) (hz : z.im ≠ 0) (ω : Ω W L) :
    blockTr ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * resPi g u z (Gr g u z ω)) a b =
      (sg W g u : ℂ) * divXb g u z M a b false [] ω := by
  set G := Gr g u z ω
  set A₀ : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)
  have hγ : 0 < gammaG g := by
    unfold gammaG
    have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  have hβ : 0 ≤ u * gammaG g := mul_nonneg hu hγ.le
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hres : (flowH g W L u ω - z • (1 : Matrix _ _ ℂ)) * G = 1 :=
    sub_smul_mul_resolventMat (flowH_isHermitian g W L u ω) hz
  have hH : flowH g W L u ω - A₀ = (sg W g u : ℂ) • ∑ y, ((ω y : ℝ) : ℂ) • bB y := by
    have hsW : ((Real.sqrt W : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < Real.sqrt W := Real.sqrt_pos.mpr hWr
      exact_mod_cast this.ne'
    rw [sum_coord_smul_bB ω hW, smul_smul]
    have : (sg W g u : ℂ) * ((Real.sqrt W : ℝ) : ℂ) = ((Real.sqrt (u * gammaG g) : ℝ) : ℂ) := by
      simp only [sg]; push_cast; field_simp
    rw [this]
    simp only [flowH, blockFlow, A₀]
    abel
  have hσW : (sg W g u : ℂ) ^ 2 * W = ((u * gammaG g : ℝ) : ℂ) := by
    have hreal : (sg W g u) ^ 2 * (W : ℝ) = u * gammaG g := by
      simp only [sg, div_pow, Real.sq_sqrt hβ, Real.sq_sqrt hWr.le]
      field_simp
    have := congrArg (fun r : ℝ => (r : ℂ)) hreal
    push_cast at this ⊢
    exact this
  have hPi : resPi g u z G = ((sg W g u : ℂ) • ∑ y, ((ω y : ℝ) : ℂ) • bB y) * G +
      ((sg W g u : ℂ) ^ 2) • ((∑ y, bB y * G * bB y) * G) := by
    rw [sum_bB_mul_bB, ← hH, resPi]
    have h1 : (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) + (z • 1 - A₀) * G =
        (flowH g W L u ω - A₀) * G := by
      calc (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) + (z • 1 - A₀) * G =
            (flowH g W L u ω - z • (1 : Matrix _ _ ℂ)) * G + (z • 1 - A₀) * G := by rw [hres]
        _ = (flowH g W L u ω - A₀) * G := by
            rw [← Matrix.add_mul]
            congr 1
            abel
    rw [h1, Matrix.smul_mul, smul_smul, hσW]
  simp only [divXb, Cb, Bool.false_eq_true, ite_false, ch, insAll, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  rw [← trF_apply, hPi, map_add, Matrix.smul_mul, trF_smul, trF_smul, Matrix.sum_mul, map_sum,
    Matrix.sum_mul, map_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.smul_mul, trF_smul]
  simp only [pX, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one,
    Matrix.mul_assoc]
  ring

private lemma divXb_true (xs : List (Fin L × Fin W × Fin W)) (ω : Ω W L) :
    divXb g u z M a b true xs ω = (starRingEnd ℂ) (divXb g u z M a b false xs ω) := by
  simp only [divXb, Cb, ite_true, Bool.false_eq_true, ite_false, map_sum, map_add, map_mul,
    Complex.conj_ofReal, map_list_sum, List.map_map, Function.comp_def]

end Residual

/-! ### Assembly -/

private lemma Good_pow {ι : Type*} [Fintype ι] [DecidableEq ι] {φ : (ι → ℝ) → ℂ} (hφ : Good φ) :
    ∀ n : ℕ, Good (fun ω => φ ω ^ n)
  | 0 => by simpa using Good_const (ι := ι) 1
  | n + 1 => by simpa [pow_succ] using Good_mul (Good_pow hφ n) hφ

private lemma μ_eq (W L : ℕ) : μ W L = stdGauss (Fin L × Fin W × Fin W) := rfl

/-- `I^{1/(2p)} ≤ B` gives `I ≤ B^{2p}` for `I ≥ 0`. -/
private lemma le_pow_of_rpow_le {I B : ℝ} {p : ℕ} (hp : 0 < p) (hI : 0 ≤ I)
    (h : I ^ (1 / (2 * (p : ℝ))) ≤ B) : I ≤ B ^ (2 * p) := by
  have h0 : 0 ≤ I ^ (1 / (2 * (p : ℝ))) := Real.rpow_nonneg hI _
  have hpow := pow_le_pow_left₀ h0 h (2 * p)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hI] at hpow
  have : 1 / (2 * (p : ℝ)) * ((2 * p : ℕ) : ℝ) = 1 := by
    push_cast; field_simp
  rwa [this, Real.rpow_one] at hpow

/-- (7.26) [gc:eq:residual-fixed-moment] in integral form, for any deterministic `M` with
`|M_{ac}| ≤ Γ` and `uγ_g Σ_c |M_{ac}| ≤ Γ`. -/
private theorem residual_core {p : ℕ} (hp : 2 ≤ p) (hpe : Even p) {C Γ : ℝ} (hC : 0 < C)
    (hΓ : 0 < Γ) {W L : ℕ} (hW : 1 ≤ W) (g u : ℝ) (hu : 0 ≤ u) (z : ℂ) (hz : 0 < z.im)
    (M : Matrix (Fin L) (Fin L) ℂ) (a b : Fin L) (hM : ∀ c, ‖M a c‖ ≤ Γ)
    (hrow : u * gammaG g * ∑ c, ‖M a c‖ ≤ Γ) {K χ : ℝ} (hK : 1 ≤ K) (hχ : 0 < χ)
    (hWχ : 1 ≤ (W : ℝ) * χ ^ 2)
    (hG1 : ∀ c d : Fin L, ∫ ω, ‖blockTr (Gr g u z ω) c d‖ ^ (2 * p)
      ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ (C * K) ^ (2 * p))
    (hG2 : ∀ e₁ e₂ : Fin L × Fin W, ∫ ω, ‖Gr g u z ω e₁ e₂ -
      (if e₁.2 = e₂.2 then blockTr (Gr g u z ω) e₁.1 e₂.1 else 0)‖ ^ (2 * p)
      ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ (C * K * χ) ^ (2 * p)) :
    Integrable (fun ω => ‖blockTr ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
        resPi g u z (Gr g u z ω)) a b‖ ^ p) (stdGauss (Fin L × Fin W × Fin W)) ∧
      ∫ ω, ‖blockTr ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
        resPi g u z (Gr g u z ω)) a b‖ ^ p ∂(stdGauss (Fin L × Fin W × Fin W)) ≤
      ((4 * p + 1 : ℝ) ^ p * (4 * p * Γ ^ p * (max 1 (2 * C)) ^ (2 * p))) *
        (K ^ 2 * χ ^ 2) ^ p := by
  set R : Ω W L → ℂ := fun ω =>
    blockTr ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * resPi g u z (Gr g u z ω)) a b with hRdef
  have hR : ∀ ω, R ω = (sg W g u : ℂ) * divXb g u z M a b false [] ω :=
    fun ω => residual_eq_divXb g u z M a b hu hW hz.ne' ω
  have hGR : Good R := by
    have : R = fun ω => (sg W g u : ℂ) * divXb g u z M a b false [] ω := funext hR
    rw [this]
    exact Good_const_mul _ (Good_divXb g u z M a b hz false [])
  have hint : Integrable (fun ω => ‖R ω‖ ^ p) (stdGauss (Fin L × Fin W × Fin W)) := by
    have := ((Good_pow hGR p).integrable).norm
    simpa [norm_pow] using this
  refine ⟨hint, ?_⟩
  obtain ⟨q, rfl⟩ := hpe
  -- the initial term: q divergences `R` and q divergences `R̄`
  let fs₀ : Fin (q + q) → Fac 0 := fun i => ⟨true, decide (q ≤ i.1), []⟩
  have hI : Inv fs₀ := by
    refine ⟨fun i => List.nodup_nil, fun l => Fin.elim0 l, fun l => Fin.elim0 l,
      fun i hi => by simp [fs₀] at hi, ?_⟩
    simp only [ndiv, fs₀, Finset.filter_true, Finset.card_univ, Fintype.card_fin, zero_add,
      le_refl]
  have hval : ∀ (i : Fin (q + q)) (x : Fin 0 → Fin L × Fin W × Fin W) (ω : Ω W L),
      fval g u z M a b (fs₀ i) x ω = if q ≤ i.1 then (starRingEnd ℂ) (R ω) else R ω := by
    intro i x ω
    simp only [fval, fs₀, ite_true, List.length_nil, zero_add, pow_one, List.map_nil]
    by_cases hi : q ≤ i.1
    · simp only [hi, decide_true, ite_true, divXb_true, hR, map_mul, Complex.conj_ofReal]
    · simp only [hi, decide_false, ite_false, hR]
  have hV : V (W := W) g u z M a b fs₀ =
      ((∫ ω, ‖R ω‖ ^ (q + q) ∂(stdGauss (Fin L × Fin W × Fin W)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp only [V]
    rw [Fintype.sum_unique]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hval]
    rw [Fin.prod_univ_add]
    simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.is_lt, not_le.mpr, ite_false,
      le_add_iff_nonneg_right, zero_le, ite_true, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [← mul_pow, Complex.mul_conj', ← pow_mul]
    push_cast
    ring_nf
  have hbound := V_bound g u z M a b hz (p := q + q)
    (4 * (q + q : ℕ) * Γ ^ (q + q) * (max 1 (2 * C)) ^ (2 * (q + q)) * (K ^ 2 * χ ^ 2) ^ (q + q))
    (by positivity)
    (fun e fs hI' h0 => V_final g u z M a b hz hu hW (by omega) hC hΓ.le hK hχ hWχ hM hrow
      hG1 hG2 fs hI' h0) (q + q) 0 fs₀ hI (by simp [ndiv, fs₀])
  rw [hV, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun ω => by positivity)]
    at hbound
  refine hbound.trans (le_of_eq ?_)
  push_cast
  ring










/-! ### Main results -/

/-- From the entrywise bounds `‖(G - M ⊗ I)_{e₁e₂}‖_{2p} ≤ Cχ` of (5.31)
[fo:eq:residual-moments] to the two moment bounds of (7.26) [gc:eq:residual-fixed-moment]:
`⟨G⟩_{cd} = M_{cd} + ⟨G̃⟩_{cd}` and `Z = G̃ - ⟨G̃⟩ I`. -/
private lemma moments_of_entries {W L : ℕ} (hW : 1 ≤ W) (g u : ℝ) {z : ℂ} (hz : 0 < z.im)
    {p : ℕ} (hp : 1 ≤ p) (M : Matrix (Fin L) (Fin L) ℂ) {Γ C χ : ℝ} (hΓ : 0 ≤ Γ)
    (hMe : ∀ c d, ‖M c d‖ ≤ Γ)
    (hE : ∀ e₁ e₂ : Fin L × Fin W, ∫ ω, ‖(Gr g u z ω -
      M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) e₁ e₂‖ ^ (2 * p)
      ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ (C * χ) ^ (2 * p)) :
    (∀ c d : Fin L, ∫ ω, ‖blockTr (Gr g u z ω) c d‖ ^ (2 * p)
      ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ 2 ^ (2 * p - 1) * (Γ ^ (2 * p) + (C * χ) ^ (2 * p))) ∧
    (∀ e₁ e₂ : Fin L × Fin W, ∫ ω, ‖Gr g u z ω e₁ e₂ -
      (if e₁.2 = e₂.2 then blockTr (Gr g u z ω) e₁.1 e₂.1 else 0)‖ ^ (2 * p)
      ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ (2 * C * χ) ^ (2 * p)) := by
  set μ' := stdGauss (Fin L × Fin W × Fin W)
  set Gt : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    fun ω => Gr g u z ω - M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) with hGt
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hW)
  have hcG : ∀ i j, Continuous fun ω : Ω W L => Gt ω i j := fun i j =>
    (continuous_Gr_apply g u hz.ne' i j).sub continuous_const
  have hbG : ∀ i j (ω : Ω W L), ‖Gt ω i j‖ ≤ z.im⁻¹ + Γ := by
    intro i j ω
    simp only [hGt, Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
    refine (norm_sub_le _ _).trans (add_le_add (norm_Gr_apply_le g u hz ω i j) ?_)
    split_ifs <;> simp [hMe, hΓ]
  -- `⟨G⟩ = M + ⟨G̃⟩` and the form of `Z`
  have hbt : ∀ ω (c d : Fin L), blockTr (Gr g u z ω) c d = M c d + blockTr (Gt ω) c d := by
    intro ω c d
    simp only [hGt, blockTr, Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.one_apply_eq,
      mul_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    ring
  have hZ : ∀ ω (e₁ e₂ : Fin L × Fin W), Gr g u z ω e₁ e₂ -
      (if e₁.2 = e₂.2 then blockTr (Gr g u z ω) e₁.1 e₂.1 else 0) =
      Gt ω e₁ e₂ - (if e₁.2 = e₂.2 then blockTr (Gt ω) e₁.1 e₂.1 else 0) := by
    intro ω e₁ e₂
    simp only [hGt, Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
    split_ifs with h
    · rw [hbt]; ring
    · ring
  -- the average over the diagonal
  have hcbt : ∀ c d, Continuous fun ω : Ω W L => blockTr (Gt ω) c d := fun c d =>
    continuous_const.mul (continuous_finsetSum _ fun α _ => hcG _ _)
  have hint : ∀ {f : Ω W L → ℂ}, Continuous f → (∀ ω, ‖f ω‖ ≤ z.im⁻¹ + Γ) →
      Integrable (fun ω => ‖f ω‖ ^ (2 * p)) μ' := by
    intro f hf hb
    refine Integrable.of_bound (hf.norm.pow _).aestronglyMeasurable ((z.im⁻¹ + Γ) ^ (2 * p))
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb ω) _
  have hbbt : ∀ c d (ω : Ω W L), ‖blockTr (Gt ω) c d‖ ≤ z.im⁻¹ + Γ := by
    intro c d ω
    simp only [blockTr, norm_mul, norm_inv, Complex.norm_natCast]
    rw [inv_mul_le_iff₀ hWr]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ α, ‖Gt ω (c, α) (d, α)‖ ≤ ∑ _α : Fin W, (z.im⁻¹ + Γ) :=
          Finset.sum_le_sum fun α _ => hbG _ _ ω
      _ = W * (z.im⁻¹ + Γ) := by simp; ring
  have havg : ∀ c d (ω : Ω W L), ‖blockTr (Gt ω) c d‖ ^ (2 * p) ≤
      (W : ℝ)⁻¹ * ∑ α, ‖Gt ω (c, α) (d, α)‖ ^ (2 * p) := by
    intro c d ω
    have h1 : ‖blockTr (Gt ω) c d‖ ≤ (∑ α, ‖Gt ω (c, α) (d, α)‖) / W := by
      simp only [blockTr, norm_mul, norm_inv, Complex.norm_natCast]
      rw [inv_mul_eq_div]
      exact div_le_div_of_nonneg_right (norm_sum_le _ _) hWr.le
    obtain ⟨n, hn⟩ : ∃ n, 2 * p = n + 1 := ⟨2 * p - 1, by omega⟩
    have hj := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Fin W)))
      (f := fun α => ‖Gt ω (c, α) (d, α)‖) (fun _ _ => norm_nonneg _) n
    rw [Finset.card_univ, Fintype.card_fin] at hj
    rw [hn]
    calc ‖blockTr (Gt ω) c d‖ ^ (n + 1) ≤ ((∑ α, ‖Gt ω (c, α) (d, α)‖) / W) ^ (n + 1) :=
          pow_le_pow_left₀ (norm_nonneg _) h1 _
      _ = (∑ α, ‖Gt ω (c, α) (d, α)‖) ^ (n + 1) / (W : ℝ) ^ n * (W : ℝ)⁻¹ := by
          rw [div_pow, pow_succ (W : ℝ) n]; field_simp
      _ ≤ (∑ α, ‖Gt ω (c, α) (d, α)‖ ^ (n + 1)) * (W : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hj (by positivity)
      _ = (W : ℝ)⁻¹ * ∑ α, ‖Gt ω (c, α) (d, α)‖ ^ (n + 1) := mul_comm _ _
  have hmbt : ∀ c d, ∫ ω, ‖blockTr (Gt ω) c d‖ ^ (2 * p) ∂μ' ≤ (C * χ) ^ (2 * p) := by
    intro c d
    calc ∫ ω, ‖blockTr (Gt ω) c d‖ ^ (2 * p) ∂μ' ≤
          ∫ ω, (W : ℝ)⁻¹ * ∑ α, ‖Gt ω (c, α) (d, α)‖ ^ (2 * p) ∂μ' :=
        integral_mono (hint (hcbt c d) (hbbt c d))
          ((integrable_finsetSum _ fun α _ => hint (hcG _ _) (hbG _ _)).const_mul _) (havg c d)
      _ = (W : ℝ)⁻¹ * ∑ α, ∫ ω, ‖Gt ω (c, α) (d, α)‖ ^ (2 * p) ∂μ' := by
          rw [integral_const_mul, integral_finsetSum _ fun α _ => hint (hcG _ _) (hbG _ _)]
      _ ≤ (W : ℝ)⁻¹ * ∑ _α : Fin W, (C * χ) ^ (2 * p) := by
          gcongr with α
          exact hE _ _
      _ = (C * χ) ^ (2 * p) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hpow2 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      (x + y) ^ (2 * p) ≤ 2 ^ (2 * p - 1) * (x ^ (2 * p) + y ^ (2 * p)) :=
    fun x y hx hy => add_pow_le hx hy _
  refine ⟨fun c d => ?_, fun e₁ e₂ => ?_⟩
  · have hpt : ∀ ω : Ω W L, ‖blockTr (Gr g u z ω) c d‖ ^ (2 * p) ≤
        2 ^ (2 * p - 1) * (Γ ^ (2 * p) + ‖blockTr (Gt ω) c d‖ ^ (2 * p)) := by
      intro ω
      rw [hbt]
      calc ‖M c d + blockTr (Gt ω) c d‖ ^ (2 * p) ≤ (Γ + ‖blockTr (Gt ω) c d‖) ^ (2 * p) :=
            pow_le_pow_left₀ (norm_nonneg _) ((norm_add_le _ _).trans
              (add_le_add_left (hMe c d) _)) _
        _ ≤ _ := hpow2 _ _ hΓ (norm_nonneg _)
    have hcB : Continuous fun ω : Ω W L => blockTr (Gr g u z ω) c d := by
      simp only [blockTr]
      exact continuous_const.mul (continuous_finsetSum _ fun α _ =>
        continuous_Gr_apply g u hz.ne' _ _)
    have hintL : Integrable (fun ω => ‖blockTr (Gr g u z ω) c d‖ ^ (2 * p)) μ' :=
      hint hcB fun ω => ((norm_blockTr_le _ c d).trans (norm_Gr_le g u hz ω)).trans
        (le_add_of_nonneg_right hΓ)
    have hintR : Integrable (fun ω => 2 ^ (2 * p - 1) *
        (Γ ^ (2 * p) + ‖blockTr (Gt ω) c d‖ ^ (2 * p))) μ' :=
      ((integrable_const _).add (hint (hcbt c d) (hbbt c d))).const_mul _
    refine (integral_mono hintL hintR hpt).trans ?_
    rw [integral_const_mul, integral_add (integrable_const _) (hint (hcbt c d) (hbbt c d)),
      integral_const, smul_eq_mul, probReal_univ, one_mul]
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (hmbt c d)) (by positivity)
  · have hpt : ∀ ω : Ω W L, ‖Gr g u z ω e₁ e₂ -
        (if e₁.2 = e₂.2 then blockTr (Gr g u z ω) e₁.1 e₂.1 else 0)‖ ^ (2 * p) ≤
        2 ^ (2 * p - 1) * (‖Gt ω e₁ e₂‖ ^ (2 * p) + ‖blockTr (Gt ω) e₁.1 e₂.1‖ ^ (2 * p)) := by
      intro ω
      rw [hZ]
      have hb : ‖(if e₁.2 = e₂.2 then blockTr (Gt ω) e₁.1 e₂.1 else 0)‖ ≤
          ‖blockTr (Gt ω) e₁.1 e₂.1‖ := by
        split_ifs <;> simp
      calc ‖Gt ω e₁ e₂ - (if e₁.2 = e₂.2 then blockTr (Gt ω) e₁.1 e₂.1 else 0)‖ ^ (2 * p) ≤
            (‖Gt ω e₁ e₂‖ + ‖blockTr (Gt ω) e₁.1 e₂.1‖) ^ (2 * p) :=
          pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add_right hb _)) _
        _ ≤ _ := hpow2 _ _ (norm_nonneg _) (norm_nonneg _)
    have hcZ : Continuous fun ω : Ω W L => Gr g u z ω e₁ e₂ -
        (if e₁.2 = e₂.2 then blockTr (Gr g u z ω) e₁.1 e₂.1 else 0) := by
      refine (continuous_Gr_apply g u hz.ne' _ _).sub ?_
      split_ifs
      · simp only [blockTr]
        exact continuous_const.mul (continuous_finsetSum _ fun α _ =>
          continuous_Gr_apply g u hz.ne' _ _)
      · exact continuous_const
    have hbZ : ∀ ω : Ω W L, ‖Gr g u z ω e₁ e₂ -
        (if e₁.2 = e₂.2 then blockTr (Gr g u z ω) e₁.1 e₂.1 else 0)‖ ≤ 2 * (z.im⁻¹ + Γ) := by
      intro ω
      rw [hZ]
      refine (norm_sub_le _ _).trans ?_
      have h1 := hbG e₁ e₂ ω
      have h2 : ‖(if e₁.2 = e₂.2 then blockTr (Gt ω) e₁.1 e₂.1 else 0)‖ ≤ z.im⁻¹ + Γ := by
        split_ifs
        · exact hbbt _ _ ω
        · rw [norm_zero]; positivity
      linarith
    have hintL : Integrable (fun ω => ‖Gr g u z ω e₁ e₂ -
        (if e₁.2 = e₂.2 then blockTr (Gr g u z ω) e₁.1 e₂.1 else 0)‖ ^ (2 * p)) μ' := by
      refine Integrable.of_bound (hcZ.norm.pow _).aestronglyMeasurable
        ((2 * (z.im⁻¹ + Γ)) ^ (2 * p))
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbZ ω) _
    have hintR : Integrable (fun ω => 2 ^ (2 * p - 1) * (‖Gt ω e₁ e₂‖ ^ (2 * p) +
        ‖blockTr (Gt ω) e₁.1 e₂.1‖ ^ (2 * p))) μ' :=
      ((hint (hcG _ _) (hbG _ _)).add (hint (hcbt _ _) (hbbt _ _))).const_mul _
    refine (integral_mono hintL hintR hpt).trans ?_
    rw [integral_const_mul, integral_add (hint (hcG _ _) (hbG _ _)) (hint (hcbt _ _) (hbbt _ _))]
    have h1 : ∫ ω, ‖Gt ω e₁ e₂‖ ^ (2 * p) ∂μ' ≤ (C * χ) ^ (2 * p) := hE e₁ e₂
    have h2 : (2 : ℝ) ^ (2 * p) = 2 ^ (2 * p - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    have h3 : 2 ^ (2 * p - 1) * (∫ ω, ‖Gt ω e₁ e₂‖ ^ (2 * p) ∂μ' +
        ∫ ω, ‖blockTr (Gt ω) e₁.1 e₂.1‖ ^ (2 * p) ∂μ') ≤
        2 ^ (2 * p - 1) * ((C * χ) ^ (2 * p) + (C * χ) ^ (2 * p)) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 (hmbt _ _)) (by positivity)
    refine h3.trans (le_of_eq ?_)
    rw [show (2 * C * χ) ^ (2 * p) = 2 ^ (2 * p) * (C * χ) ^ (2 * p) by ring, h2]
    ring

/-- `χ ≥ W^{-1/2}` gives `W χ² ≥ 1`. -/
private lemma one_le_mul_sq_of_rpow_le {W χ : ℝ} (hW : 0 < W) (h : W ^ (-(1 / 2 : ℝ)) ≤ χ) :
    1 ≤ W * χ ^ 2 := by
  have h0 : 0 ≤ W ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hW.le _
  have hsq : (W ^ (-(1 / 2 : ℝ))) ^ 2 = W⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    norm_num
    exact Real.rpow_neg_one W
  calc (1 : ℝ) = W * W⁻¹ := (mul_inv_cancel₀ hW.ne').symm
    _ = W * (W ^ (-(1 / 2 : ℝ))) ^ 2 := by rw [hsq]
    _ ≤ W * χ ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h 2) hW.le

/-- `2^{2p-1}(x^{2p} + y^{2p}) ≤ (2B)^{2p}` for `0 ≤ x, y ≤ B`. -/
private lemma two_pow_add_le {p : ℕ} (hp : 1 ≤ p) {x y B : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxB : x ≤ B) (hyB : y ≤ B) :
    2 ^ (2 * p - 1) * (x ^ (2 * p) + y ^ (2 * p)) ≤ (2 * B) ^ (2 * p) := by
  have h2 : (2 : ℝ) ^ (2 * p) = 2 ^ (2 * p - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  calc 2 ^ (2 * p - 1) * (x ^ (2 * p) + y ^ (2 * p)) ≤
        2 ^ (2 * p - 1) * (B ^ (2 * p) + B ^ (2 * p)) := by gcongr
    _ = (2 * B) ^ (2 * p) := by rw [mul_pow, h2]; ring

/-- (7.26) [gc:eq:residual-fixed-moment] at a general spectral point `z ∈ ℂ_+`, a general time
`u ≥ 0` and a deterministic `M = (A_g - z - uγ_g m')⁻¹` with `Im m' ≥ 0`, under the
covariance-weighted rows (6.13) [gc:eq:residual-row-bounds] as hypotheses: if
`‖⟨G⟩_{ab}‖_{2p} ≤ CK` and `‖G_{ai,bj} - δ_{ij}⟨G⟩_{ab}‖_{2p} ≤ CKχ`, then
`E|⟨(M ⊗ I)Π(G)⟩_{ab}|^p ≤ C_p (K²χ²)^p`. -/
theorem residual_moment (p : ℕ) (hp : 2 ≤ p) (hpe : Even p) (C Γ : ℝ) (hC : 0 < C)
    (hΓ : 0 < Γ) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ W L : ℕ, 1 ≤ W → ∀ g u : ℝ, 0 ≤ u → ∀ z m' : ℂ, 0 < z.im →
      0 ≤ m'.im → ‖m'‖ ≤ Γ →
      (∀ a c, ‖dysonMat (hopB g) (u * gammaG g) L z m' a c‖ ≤ Γ) →
      (∀ a, u * gammaG g * ∑ c, (‖dysonMat (hopB g) (u * gammaG g) L z m' a c‖ +
        ‖dysonMat (hopB g) (u * gammaG g) L z m' a c‖ ^ 2) ≤ Γ) →
      ∀ K χ : ℝ, 1 ≤ K → (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ χ →
      (∀ a b : Fin L, (∫ ω, ‖blockTr (resolventMat (flowH g W L u ω) z) a b‖ ^ (2 * p)
        ∂(μ W L)) ^ (1 / (2 * (p : ℝ))) ≤ C * K) →
      (∀ e₁ e₂ : Fin L × Fin W, (∫ ω, ‖resolventMat (flowH g W L u ω) z e₁ e₂ -
          if e₁.2 = e₂.2 then blockTr (resolventMat (flowH g W L u ω) z) e₁.1 e₂.1 else 0‖ ^ (2 * p)
        ∂(μ W L)) ^ (1 / (2 * (p : ℝ))) ≤ C * K * χ) →
      ∀ a b : Fin L,
        Integrable (fun ω => ‖blockTr ((dysonMat (hopB g) (u * gammaG g) L z m' ⊗ₖ
          (1 : Matrix (Fin W) (Fin W) ℂ)) * resPi g u z (resolventMat (flowH g W L u ω) z)) a b‖ ^ p)
          (μ W L) ∧
        ∫ ω, ‖blockTr ((dysonMat (hopB g) (u * gammaG g) L z m' ⊗ₖ
          (1 : Matrix (Fin W) (Fin W) ℂ)) * resPi g u z (resolventMat (flowH g W L u ω) z)) a b‖ ^ p
          ∂(μ W L) ≤ Cp * (K ^ 2 * χ ^ 2) ^ p := by
  refine ⟨(4 * p + 1 : ℝ) ^ p * (4 * p * Γ ^ p * (max 1 (2 * C)) ^ (2 * p)), by positivity, ?_⟩
  intro W L hW g u hu z m' hz hm' hm'Γ hMe hrow K χ hK hχ h1 h2 a b
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hχ0 : 0 < χ := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hχ
  have hWχ : 1 ≤ (W : ℝ) * χ ^ 2 := one_le_mul_sq_of_rpow_le hW0 hχ
  have hγ : 0 ≤ u * gammaG g := mul_nonneg hu (by unfold gammaG; positivity)
  have hrow' : u * gammaG g * ∑ c, ‖dysonMat (hopB g) (u * gammaG g) L z m' a c‖ ≤ Γ := by
    refine le_trans ?_ (hrow a)
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ =>
      le_add_of_nonneg_right (sq_nonneg _)) hγ
  rw [μ_eq]
  exact residual_core hp hpe hC hΓ hW g u hu z hz _ a b (fun c => hMe a c) hrow' hK hχ0 hWχ
    (fun c d => le_pow_of_rpow_le (by omega) (integral_nonneg fun ω => by positivity) (h1 c d))
    (fun e₁ e₂ => le_pow_of_rpow_le (by omega) (integral_nonneg fun ω => by positivity)
      (h2 e₁ e₂))

/-- (5.31) [fo:eq:residual-moments] at a general spectral point and a general Dyson-form `M`
with the rows (6.13) [gc:eq:residual-row-bounds]: `‖(G - M ⊗ I)_{ai,bj}‖_{2p} ≤ Cχ` for all
entries gives `E|⟨(M ⊗ I)Π(G)⟩_{ab}|^p ≤ C_p χ^{2p}`. -/
theorem residual_moment_entries (p : ℕ) (hp : 2 ≤ p) (hpe : Even p) (C Γ : ℝ) (hC : 0 < C)
    (hΓ : 0 < Γ) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ W L : ℕ, 1 ≤ W → ∀ g u : ℝ, 0 ≤ u → ∀ z m' : ℂ, 0 < z.im →
      0 ≤ m'.im → ‖m'‖ ≤ Γ →
      (∀ a c, ‖dysonMat (hopB g) (u * gammaG g) L z m' a c‖ ≤ Γ) →
      (∀ a, u * gammaG g * ∑ c, (‖dysonMat (hopB g) (u * gammaG g) L z m' a c‖ +
        ‖dysonMat (hopB g) (u * gammaG g) L z m' a c‖ ^ 2) ≤ Γ) →
      ∀ χ : ℝ, (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ χ →
      (∀ e₁ e₂ : Fin L × Fin W, (∫ ω, ‖(resolventMat (flowH g W L u ω) z -
          dysonMat (hopB g) (u * gammaG g) L z m' ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) e₁ e₂‖ ^ (2 * p)
        ∂(μ W L)) ^ (1 / (2 * (p : ℝ))) ≤ C * χ) →
      ∀ a b : Fin L,
        Integrable (fun ω => ‖blockTr ((dysonMat (hopB g) (u * gammaG g) L z m' ⊗ₖ
          (1 : Matrix (Fin W) (Fin W) ℂ)) * resPi g u z (resolventMat (flowH g W L u ω) z)) a b‖ ^ p)
          (μ W L) ∧
        ∫ ω, ‖blockTr ((dysonMat (hopB g) (u * gammaG g) L z m' ⊗ₖ
          (1 : Matrix (Fin W) (Fin W) ℂ)) * resPi g u z (resolventMat (flowH g W L u ω) z)) a b‖ ^ p
          ∂(μ W L) ≤ Cp * χ ^ (2 * p) := by
  have hC₀ : 0 < 2 * (Γ + C) := by positivity
  refine ⟨(4 * p + 1 : ℝ) ^ p * (4 * p * Γ ^ p * (max 1 (2 * (2 * (Γ + C)))) ^ (2 * p)),
    by positivity, ?_⟩
  intro W L hW g u hu z m' hz hm' hm'Γ hMe hrow χ hχ hE a b
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hχ0 : 0 < χ := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hχ
  have hWχ : 1 ≤ (W : ℝ) * χ ^ 2 := one_le_mul_sq_of_rpow_le hW0 hχ
  have hγ : 0 ≤ u * gammaG g := mul_nonneg hu (by unfold gammaG; positivity)
  have hrow' : u * gammaG g * ∑ c, ‖dysonMat (hopB g) (u * gammaG g) L z m' a c‖ ≤ Γ := by
    refine le_trans ?_ (hrow a)
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ =>
      le_add_of_nonneg_right (sq_nonneg _)) hγ
  have hE' := fun e₁ e₂ => le_pow_of_rpow_le (by omega)
    (integral_nonneg fun ω => by positivity) (hE e₁ e₂)
  obtain ⟨hB1, hB2⟩ := moments_of_entries hW g u hz (by omega) _ hΓ.le hMe hE'
  rw [μ_eq]
  by_cases hχ1 : χ ≤ 1
  · have key := residual_core hp hpe hC₀ hΓ hW g u hu z hz _ a b (fun c => hMe a c) hrow'
      (K := 1) (χ := χ) le_rfl hχ0 hWχ
      (fun c d => (hB1 c d).trans (by
        rw [mul_one]
        exact two_pow_add_le (by omega) hΓ.le (by positivity) (by linarith)
          (by nlinarith)))
      (fun e₁ e₂ => (hB2 e₁ e₂).trans (by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        nlinarith))
    refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
    rw [one_pow, one_mul, ← pow_mul]
  · have hχ1' : 1 < χ := lt_of_not_ge hχ1
    have key := residual_core hp hpe hC₀ hΓ hW g u hu z hz _ a b (fun c => hMe a c) hrow'
      (K := χ) (χ := 1) hχ1'.le one_pos (by simpa using (by exact_mod_cast hW : (1 : ℝ) ≤ W))
      (fun c d => (hB1 c d).trans (by
        rw [show 2 * (Γ + C) * χ = 2 * ((Γ + C) * χ) by ring]
        exact two_pow_add_le (by omega) hΓ.le (by positivity) (by nlinarith) (by nlinarith)))
      (fun e₁ e₂ => (hB2 e₁ e₂).trans (by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        nlinarith))
    refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
    rw [one_pow, mul_one, ← pow_mul]

section Instances

open scoped Matrix.Norms.L2Operator

end Instances

end LSBA
