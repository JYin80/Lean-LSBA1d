import Mathlib

/-!
# Operator norms of pairing sums

The pairings of `Fin n` (fixed-point-free involutions), and the per-pairing bound
`‖Σ_{j∘σ = j} D_{j_0} ⋯ D_{j_{2p-1}}‖ ≤ ‖Σ_a D_a²‖^p` for Hermitian `D_a` and every pairing `σ`
of `Fin (2p)`, crossing or not. This is the deterministic half of the tensor bound in Appendix
G.4 [app:compact-gaussian].
-/

open Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The pairings of `Fin n`: fixed-point-free involutions. -/
def pairings (n : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ => ∀ i, σ (σ i) = i ∧ σ i ≠ i

section PairingNormAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For symmetric `T_a`: `Σ_a ‖T_a y‖² ≤ ‖Σ_a T_a T_a‖ ‖y‖²`. -/
private lemma PairingNorm_sum_norm_sq_le {m : ℕ} (T : Fin m → E →L[ℂ] E)
    (hT : ∀ a x y, inner ℂ (T a x) y = inner ℂ x (T a y)) (y : E) :
    ∑ a, ‖T a y‖ ^ 2 ≤ ‖∑ a, T a * T a‖ * ‖y‖ ^ 2 := by
  have h1 : ∀ a, ‖T a y‖ ^ 2 = RCLike.re (inner ℂ y ((T a * T a) y)) := by
    intro a
    rw [mul_apply_eq_comp, ← hT, inner_self_eq_norm_sq]
  calc ∑ a, ‖T a y‖ ^ 2 = RCLike.re (inner ℂ y ((∑ a, T a * T a) y)) := by
        simp_rw [h1, _root_.sum_apply, inner_sum, map_sum]
    _ ≤ ‖y‖ * ‖(∑ a, T a * T a) y‖ := re_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖∑ a, T a * T a‖ * ‖y‖) := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = _ := by ring

/-- For symmetric `T_a`: `‖Σ_a T_a u_a‖² ≤ ‖Σ_a T_a T_a‖ Σ_a ‖u_a‖²`. -/
private lemma PairingNorm_norm_sum_sq_le {m : ℕ} (T : Fin m → E →L[ℂ] E)
    (hT : ∀ a x y, inner ℂ (T a x) y = inner ℂ x (T a y)) (u : Fin m → E) :
    ‖∑ a, T a (u a)‖ ^ 2 ≤ ‖∑ a, T a * T a‖ * ∑ a, ‖u a‖ ^ 2 := by
  set z := ∑ a, T a (u a) with hz
  set A := ‖∑ a, T a * T a‖
  have h1 : ‖z‖ ^ 2 ≤ ∑ a, ‖T a z‖ * ‖u a‖ := by
    have hzz : inner ℂ z z = ∑ a, inner ℂ (T a z) (u a) := by
      simp_rw [hT]
      rw [← inner_sum]
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hzz, map_sum]
    exact Finset.sum_le_sum fun a _ => re_inner_le_norm _ _
  have h4 : (‖z‖ ^ 2) ^ 2 ≤ (A * ∑ a, ‖u a‖ ^ 2) * ‖z‖ ^ 2 := by
    calc (‖z‖ ^ 2) ^ 2 ≤ (∑ a, ‖T a z‖ * ‖u a‖) ^ 2 := by gcongr
      _ ≤ (∑ a, ‖T a z‖ ^ 2) * ∑ a, ‖u a‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (A * ‖z‖ ^ 2) * ∑ a, ‖u a‖ ^ 2 := by
          gcongr; exact PairingNorm_sum_norm_sq_le T hT z
      _ = _ := by ring
  rcases (sq_nonneg ‖z‖).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · exact le_of_mul_le_mul_right (by rw [← pow_two]; exact h4) h0

/-- Summing over a free coordinate: `Σ_c Σ_a h(c[s ↦ a]) = m Σ_c h(c)`. -/
private lemma PairingNorm_sum_update {n m : ℕ} (h : (Fin n → Fin m) → ℝ) (s : Fin n) :
    ∑ c : Fin n → Fin m, ∑ a : Fin m, h (Function.update c s a) = m * ∑ c, h c := by
  let e : (Fin n → Fin m) × Fin m ≃ (Fin n → Fin m) × Fin m :=
    { toFun := fun q => (Function.update q.1 s q.2, q.1 s)
      invFun := fun q => (Function.update q.1 s q.2, q.1 s)
      left_inv := fun q => Prod.ext (by simp) (by simp)
      right_inv := fun q => Prod.ext (by simp) (by simp) }
  calc ∑ c : Fin n → Fin m, ∑ a : Fin m, h (Function.update c s a)
      = ∑ q : (Fin n → Fin m) × Fin m, h (e q).1 := by rw [Fintype.sum_prod_type]; rfl
    _ = ∑ q : (Fin n → Fin m) × Fin m, h q.1 := Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = m * ∑ c, h c := by rw [Fintype.sum_prod_type]; simp [Finset.mul_sum]

/-- The tail product `T_{j_t} ⋯ T_{j_{n-1}}`. -/
private def PairingNorm_tail {m n : ℕ} (T : Fin m → E →L[ℂ] E) (j : Fin n → Fin m) (t : ℕ) :
    E →L[ℂ] E :=
  ((List.ofFn fun i => T (j i)).drop t).prod

private lemma PairingNorm_tail_succ {m n : ℕ} (T : Fin m → E →L[ℂ] E) (j : Fin n → Fin m)
    (i : Fin n) : PairingNorm_tail T j i.val = T (j i) * PairingNorm_tail T j (i.val + 1) := by
  unfold PairingNorm_tail
  rw [List.drop_eq_getElem_cons (by simp), List.prod_cons, List.getElem_ofFn]

private lemma PairingNorm_tail_self {m n : ℕ} (T : Fin m → E →L[ℂ] E) (j : Fin n → Fin m) :
    PairingNorm_tail T j n = 1 := by
  unfold PairingNorm_tail
  rw [List.drop_of_length_le (by simp)]
  rfl

private lemma PairingNorm_tail_zero {m n : ℕ} (T : Fin m → E →L[ℂ] E) (j : Fin n → Fin m) :
    PairingNorm_tail T j 0 = (List.ofFn fun i => T (j i)).prod := by
  simp [PairingNorm_tail]

private lemma PairingNorm_tail_congr {m n : ℕ} (T : Fin m → E →L[ℂ] E) {j j' : Fin n → Fin m}
    {t : ℕ} (h : ∀ i : Fin n, t ≤ i.val → j i = j' i) :
    PairingNorm_tail T j t = PairingNorm_tail T j' t := by
  unfold PairingNorm_tail
  congr 1
  apply List.ext_getElem (by simp)
  intro r h1 h2
  simp only [List.getElem_drop, List.getElem_ofFn]
  congr 1
  exact h _ (by simp)

/-- Admissible labellings at level `t`: equal to `c` below `t`, constant on pairs from `t` on. -/
private def PairingNorm_adm {m n : ℕ} (σ : Equiv.Perm (Fin n)) (t : ℕ) (c j : Fin n → Fin m) :
    Prop :=
  (∀ i : Fin n, i.val < t → j i = c i) ∧ ∀ i : Fin n, t ≤ i.val → j (σ i) = j i

/-- The state at level `t` and boundary labelling `c`. -/
private def PairingNorm_state {m n : ℕ} (T : Fin m → E →L[ℂ] E) (σ : Equiv.Perm (Fin n))
    (x : E) (t : ℕ) (c : Fin n → Fin m) : E :=
  ∑ j ∈ univ.filter (PairingNorm_adm σ t c), PairingNorm_tail T j t x

private lemma PairingNorm_state_self {m n : ℕ} (T : Fin m → E →L[ℂ] E)
    (σ : Equiv.Perm (Fin n)) (x : E) (c : Fin n → Fin m) :
    PairingNorm_state T σ x n c = x := by
  unfold PairingNorm_state
  have hfil : univ.filter (PairingNorm_adm σ n c) = {c} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton, PairingNorm_adm]
    constructor
    · rintro ⟨h, -⟩
      funext i
      exact h i i.isLt
    · rintro rfl
      exact ⟨fun _ _ => rfl, fun i hi => absurd i.isLt (not_lt.mpr hi)⟩
  rw [hfil, sum_singleton, PairingNorm_tail_self, one_apply_eq_self]

private lemma PairingNorm_state_zero {m n : ℕ} (T : Fin m → E →L[ℂ] E)
    (σ : Equiv.Perm (Fin n)) (x : E) (c : Fin n → Fin m) :
    PairingNorm_state T σ x 0 c =
      (∑ j ∈ (Finset.univ : Finset (Fin n → Fin m)).filter (fun j => ∀ i, j (σ i) = j i),
        (List.ofFn fun i => T (j i)).prod) x := by
  unfold PairingNorm_state
  rw [_root_.sum_apply]
  refine Finset.sum_congr (Finset.filter_congr fun j _ => ?_) fun j _ => ?_
  · simp [PairingNorm_adm]
  · rw [PairingNorm_tail_zero]

private lemma PairingNorm_state_update {m n : ℕ} (T : Fin m → E →L[ℂ] E)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, σ (σ i) = i) (x : E) {t : ℕ} (c : Fin n → Fin m)
    {l : Fin n} (hl : l.val < t) (hσl : (σ l).val < t) (a : Fin m) :
    PairingNorm_state T σ x t (Function.update c l a) = PairingNorm_state T σ x t c := by
  unfold PairingNorm_state
  have key : ∀ (c' j : Fin n → Fin m) (b : Fin m), PairingNorm_adm σ t c' j →
      PairingNorm_adm σ t (Function.update c' l b) (Function.update j l b) := by
    rintro c' j b ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rcases eq_or_ne i l with rfl | hil
      · simp
      · rw [Function.update_of_ne hil, Function.update_of_ne hil, h1 i hi]
    · have hil : i ≠ l := by rintro rfl; omega
      have hsil : σ i ≠ l := by
        intro h
        have h' := hσ i
        rw [h] at h'
        rw [← h'] at hi
        omega
      rw [Function.update_of_ne hil, Function.update_of_ne hsil, h2 i hi]
  refine Finset.sum_nbij' (fun j => Function.update j l (c l)) (fun j => Function.update j l a)
    ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_univ, true_and, mem_filter] at hj ⊢
    have := key _ j (c l) hj
    rwa [Function.update_idem, Function.update_eq_self] at this
  · intro j hj
    simp only [mem_univ, true_and, mem_filter] at hj ⊢
    exact key _ j a hj
  · intro j hj
    simp only [mem_univ, true_and, mem_filter] at hj
    have hja : j l = a := by simpa using hj.1 l hl
    rw [Function.update_idem, ← hja, Function.update_eq_self]
  · intro j hj
    simp only [mem_univ, true_and, mem_filter] at hj
    have hja : j l = c l := hj.1 l hl
    rw [Function.update_idem, ← hja, Function.update_eq_self]
  · intro j _
    rw [PairingNorm_tail_congr T (j' := Function.update j l (c l)) fun i hi => ?_]
    have hil : i ≠ l := by rintro rfl; omega
    rw [Function.update_of_ne hil]

/-- Opening step: position `i₀` is the right end of its pair. -/
private lemma PairingNorm_state_open {m n : ℕ} (T : Fin m → E →L[ℂ] E)
    (σ : Equiv.Perm (Fin n)) (x : E) (i0 : Fin n) (ho : σ i0 < i0) (c : Fin n → Fin m) :
    PairingNorm_state T σ x i0.val c =
      T (c (σ i0)) (PairingNorm_state T σ x (i0.val + 1) (Function.update c i0 (c (σ i0)))) := by
  have ho' : (σ i0).val < i0.val := ho
  have hne : σ i0 ≠ i0 := fun h => by rw [h] at ho'; omega
  unfold PairingNorm_state
  have hfil : univ.filter (PairingNorm_adm σ i0.val c) =
      univ.filter (PairingNorm_adm σ (i0.val + 1) (Function.update c i0 (c (σ i0)))) := by
    refine Finset.filter_congr fun j _ => ?_
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi => ?_, fun i hi => h2 i (by omega)⟩
      rcases eq_or_ne i i0 with rfl | hii
      · rw [Function.update_self, ← h2 i le_rfl, h1 _ ho']
      · have : i.val ≠ i0.val := fun h => hii (Fin.ext h)
        rw [Function.update_of_ne hii]
        exact h1 i (by omega)
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have hii : i ≠ i0 := fun h => by rw [h] at hi; omega
        rw [h1 i (by omega), Function.update_of_ne hii]
      · rcases eq_or_ne i i0 with rfl | hii
        · rw [h1 (σ i) (by omega), Function.update_of_ne hne, h1 i (by omega),
            Function.update_self]
        · have : i.val ≠ i0.val := fun h => hii (Fin.ext h)
          exact h2 i (by omega)
  rw [hfil, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [PairingNorm_tail_succ, mul_apply_eq_comp]
  have hj0 : j i0 = c (σ i0) := by
    have := (mem_filter.mp hj).2.1 i0 (by omega)
    rwa [Function.update_self] at this
  rw [hj0]

/-- Closing step: position `i₀` is the left end of its pair. -/
private lemma PairingNorm_state_close {m n : ℕ} (T : Fin m → E →L[ℂ] E)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, σ (σ i) = i) (x : E) (i0 : Fin n) (hc : i0 < σ i0)
    (c : Fin n → Fin m) :
    PairingNorm_state T σ x i0.val c =
      ∑ a, T a (PairingNorm_state T σ x (i0.val + 1) (Function.update c i0 a)) := by
  have hc' : i0.val < (σ i0).val := hc
  unfold PairingNorm_state
  rw [← Finset.sum_fiberwise (univ.filter (PairingNorm_adm σ i0.val c)) (fun j => j i0)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.filter_filter, map_sum]
  have hfil : univ.filter (fun j => PairingNorm_adm σ i0.val c j ∧ j i0 = a) =
      univ.filter (PairingNorm_adm σ (i0.val + 1) (Function.update c i0 a)) := by
    refine Finset.filter_congr fun j _ => ?_
    constructor
    · rintro ⟨⟨h1, h2⟩, rfl⟩
      refine ⟨fun i hi => ?_, fun i hi => h2 i (by omega)⟩
      rcases eq_or_ne i i0 with rfl | hii
      · simp
      · have : i.val ≠ i0.val := fun h => hii (Fin.ext h)
        rw [Function.update_of_ne hii]
        exact h1 i (by omega)
    · rintro ⟨h1, h2⟩
      have hja : j i0 = a := by simpa using h1 i0 (by omega)
      refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, hja⟩
      · have hii : i ≠ i0 := fun h => by rw [h] at hi; omega
        rw [h1 i (by omega), Function.update_of_ne hii]
      · rcases eq_or_ne i i0 with rfl | hii
        · have := h2 (σ i) (by omega)
          rw [hσ] at this
          exact this.symm
        · have : i.val ≠ i0.val := fun h => hii (Fin.ext h)
          exact h2 i (by omega)
  rw [hfil]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [PairingNorm_tail_succ, mul_apply_eq_comp]
  have hja : j i0 = a := by simpa using (mem_filter.mp hj).2.1 i0 (by omega)
  rw [hja]

/-- The squared norm of the state at level `t`, summed over all boundary labellings. -/
private def PairingNorm_S {m n : ℕ} (T : Fin m → E →L[ℂ] E) (σ : Equiv.Perm (Fin n)) (x : E)
    (t : ℕ) : ℝ :=
  ∑ c : Fin n → Fin m, ‖PairingNorm_state T σ x t c‖ ^ 2

private lemma PairingNorm_S_nonneg {m n : ℕ} (T : Fin m → E →L[ℂ] E) (σ : Equiv.Perm (Fin n))
    (x : E) (t : ℕ) : 0 ≤ PairingNorm_S T σ x t := by
  unfold PairingNorm_S; positivity

private lemma PairingNorm_S_open {m n : ℕ} (T : Fin m → E →L[ℂ] E)
    (hT : ∀ a x y, inner ℂ (T a x) y = inner ℂ x (T a y)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, σ (σ i) = i) (x : E) (i0 : Fin n) (ho : σ i0 < i0) :
    (m : ℝ) * PairingNorm_S T σ x i0.val ≤
      ‖∑ a, T a * T a‖ * PairingNorm_S T σ x (i0.val + 1) := by
  have ho' : (σ i0).val < i0.val := ho
  set s := σ i0 with hs
  have hss : σ s = i0 := hσ i0
  let h : (Fin n → Fin m) → ℝ := fun c => ‖T (c s) (PairingNorm_state T σ x (i0.val + 1) c)‖ ^ 2
  have e1 : ∀ c, ‖PairingNorm_state T σ x i0.val c‖ ^ 2 = h c := by
    intro c
    rw [PairingNorm_state_open T σ x i0 ho c,
      PairingNorm_state_update T σ hσ x c (by omega) (by rw [← hs]; omega)]
  have e2 : ∀ c a, h (Function.update c s a) =
      ‖T a (PairingNorm_state T σ x (i0.val + 1) c)‖ ^ 2 := by
    intro c a
    simp only [h, Function.update_self]
    rw [PairingNorm_state_update T σ hσ x c (by omega) (by rw [hss]; omega)]
  unfold PairingNorm_S
  calc (m : ℝ) * ∑ c, ‖PairingNorm_state T σ x i0.val c‖ ^ 2 = (m : ℝ) * ∑ c, h c := by
        simp_rw [e1]
    _ = ∑ c, ∑ a, h (Function.update c s a) := (PairingNorm_sum_update h s).symm
    _ = ∑ c, ∑ a, ‖T a (PairingNorm_state T σ x (i0.val + 1) c)‖ ^ 2 := by simp_rw [e2]
    _ ≤ ∑ c, ‖∑ a, T a * T a‖ * ‖PairingNorm_state T σ x (i0.val + 1) c‖ ^ 2 :=
        Finset.sum_le_sum fun c _ => PairingNorm_sum_norm_sq_le T hT _
    _ = _ := (Finset.mul_sum _ _ _).symm

private lemma PairingNorm_S_close {m n : ℕ} (T : Fin m → E →L[ℂ] E)
    (hT : ∀ a x y, inner ℂ (T a x) y = inner ℂ x (T a y)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, σ (σ i) = i) (x : E) (i0 : Fin n) (hc : i0 < σ i0) :
    PairingNorm_S T σ x i0.val ≤
      ‖∑ a, T a * T a‖ * ((m : ℝ) * PairingNorm_S T σ x (i0.val + 1)) := by
  unfold PairingNorm_S
  rw [← PairingNorm_sum_update _ i0, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [PairingNorm_state_close T σ hσ x i0 hc c]
  exact PairingNorm_norm_sum_sq_le T hT _

/-- Number of positions `i ≥ t` satisfying `P`. -/
private def PairingNorm_cnt {n : ℕ} (P : Fin n → Prop) (t : ℕ) : ℕ :=
  ∑ i : Fin n, if t ≤ i.val ∧ P i then 1 else 0

private lemma PairingNorm_cnt_succ {n : ℕ} (P : Fin n → Prop) (i0 : Fin n) :
    PairingNorm_cnt P i0.val = PairingNorm_cnt P (i0.val + 1) + if P i0 then 1 else 0 := by
  unfold PairingNorm_cnt
  have : ∀ i : Fin n, (if i0.val ≤ i.val ∧ P i then 1 else 0 : ℕ) =
      (if i0.val + 1 ≤ i.val ∧ P i then 1 else 0) +
        if i0 = i then (if P i then 1 else 0) else 0 := by
    intro i
    rcases eq_or_ne i0 i with rfl | h
    · simp
    · have : i.val ≠ i0.val := fun h' => h (Fin.ext h'.symm)
      simp only [h, ite_false, add_zero]
      by_cases hP : P i
      · simp only [hP, and_true]
        split_ifs <;> omega
      · simp [hP]
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

private lemma PairingNorm_cnt_self {n : ℕ} (P : Fin n → Prop) : PairingNorm_cnt P n = 0 :=
  Finset.sum_eq_zero fun i _ => ite_eq_right_iff.mpr fun h => absurd h.1 (not_le.mpr i.isLt)

private lemma PairingNorm_invariant {m n : ℕ} (T : Fin m → E →L[ℂ] E)
    (hT : ∀ a x y, inner ℂ (T a x) y = inner ℂ x (T a y)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, σ (σ i) = i ∧ σ i ≠ i) (x : E) (d : ℕ) :
    ∀ t, t + d = n →
      (m : ℝ) ^ PairingNorm_cnt (fun i => σ i < i) t * PairingNorm_S T σ x t ≤
        ‖∑ a, T a * T a‖ ^ (n - t) * (m : ℝ) ^ PairingNorm_cnt (fun i => i < σ i) t *
          PairingNorm_S T σ x n := by
  set A := ‖∑ a, T a * T a‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  have hσ1 : ∀ i, σ (σ i) = i := fun i => (hσ i).1
  induction d with
  | zero =>
    intro t ht
    have ht' : t = n := by omega
    subst ht'
    simp [PairingNorm_cnt_self]
  | succ d ih =>
    intro t ht
    obtain ⟨i0, rfl⟩ : ∃ i0 : Fin n, i0.val = t := ⟨⟨t, by omega⟩, rfl⟩
    have hrec := ih (i0.val + 1) (by omega)
    have hn : n - i0.val = n - (i0.val + 1) + 1 := by omega
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hSn := PairingNorm_S_nonneg T σ x n
    rw [PairingNorm_cnt_succ _ i0, PairingNorm_cnt_succ (fun i => i < σ i) i0, hn, pow_succ]
    rcases lt_or_gt_of_ne (hσ i0).2 with ho | hc
    · have hstep := PairingNorm_S_open T hT σ hσ1 x i0 ho
      have hnc : ¬ i0 < σ i0 := not_lt.mpr ho.le
      simp only [ho, hnc, ite_true, ite_false, add_zero, pow_succ]
      calc (m : ℝ) ^ PairingNorm_cnt (fun i => σ i < i) (i0.val + 1) * m *
            PairingNorm_S T σ x i0.val
          = (m : ℝ) ^ PairingNorm_cnt (fun i => σ i < i) (i0.val + 1) *
              (m * PairingNorm_S T σ x i0.val) := by ring
        _ ≤ (m : ℝ) ^ PairingNorm_cnt (fun i => σ i < i) (i0.val + 1) *
              (A * PairingNorm_S T σ x (i0.val + 1)) := by gcongr
        _ = A * ((m : ℝ) ^ PairingNorm_cnt (fun i => σ i < i) (i0.val + 1) *
              PairingNorm_S T σ x (i0.val + 1)) := by ring
        _ ≤ A * (A ^ (n - (i0.val + 1)) *
              (m : ℝ) ^ PairingNorm_cnt (fun i => i < σ i) (i0.val + 1) *
              PairingNorm_S T σ x n) := by gcongr
        _ = _ := by ring
    · have hstep := PairingNorm_S_close T hT σ hσ1 x i0 hc
      have hno : ¬ σ i0 < i0 := not_lt.mpr hc.le
      simp only [hc, hno, ite_true, ite_false, add_zero, pow_succ]
      calc (m : ℝ) ^ PairingNorm_cnt (fun i => σ i < i) (i0.val + 1) *
            PairingNorm_S T σ x i0.val
          ≤ (m : ℝ) ^ PairingNorm_cnt (fun i => σ i < i) (i0.val + 1) *
              (A * (m * PairingNorm_S T σ x (i0.val + 1))) := by gcongr
        _ = A * m * ((m : ℝ) ^ PairingNorm_cnt (fun i => σ i < i) (i0.val + 1) *
              PairingNorm_S T σ x (i0.val + 1)) := by ring
        _ ≤ A * m * (A ^ (n - (i0.val + 1)) *
              (m : ℝ) ^ PairingNorm_cnt (fun i => i < σ i) (i0.val + 1) *
              PairingNorm_S T σ x n) := by gcongr
        _ = _ := by ring

/-- The pairing bound for symmetric operators on a complex inner product space, in squared
vector form: `‖M_σ x‖² ≤ ‖Σ_a T_a T_a‖^n ‖x‖²`. -/
private lemma PairingNorm_core {m n : ℕ} (T : Fin m → E →L[ℂ] E)
    (hT : ∀ a x y, inner ℂ (T a x) y = inner ℂ x (T a y)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, σ (σ i) = i ∧ σ i ≠ i) (x : E) :
    ‖(∑ j ∈ (Finset.univ : Finset (Fin n → Fin m)).filter (fun j => ∀ i, j (σ i) = j i),
        (List.ofFn fun i => T (j i)).prod) x‖ ^ 2 ≤ ‖∑ a, T a * T a‖ ^ n * ‖x‖ ^ 2 := by
  set M := ∑ j ∈ (Finset.univ : Finset (Fin n → Fin m)).filter (fun j => ∀ i, j (σ i) = j i),
    (List.ofFn fun i => T (j i)).prod with hM
  set A := ‖∑ a, T a * T a‖ with hA
  have hinv := PairingNorm_invariant T hT σ hσ x n 0 (by simp)
  have hS0 : PairingNorm_S T σ x 0 = (m : ℝ) ^ n * ‖M x‖ ^ 2 := by
    unfold PairingNorm_S
    simp_rw [PairingNorm_state_zero]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
  have hSn : PairingNorm_S T σ x n = (m : ℝ) ^ n * ‖x‖ ^ 2 := by
    unfold PairingNorm_S
    simp_rw [PairingNorm_state_self]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
  have hoc : PairingNorm_cnt (fun i => σ i < i) 0 = PairingNorm_cnt (fun i => i < σ i) 0 := by
    unfold PairingNorm_cnt
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [(hσ i).1]
  rw [hS0, hSn, hoc, Nat.sub_zero] at hinv
  set c := PairingNorm_cnt (fun i => i < σ i) 0
  by_cases hmn : 0 < m ∨ n = 0
  · have hpos : 0 < (m : ℝ) ^ c * (m : ℝ) ^ n := by
      rcases hmn with hm | hn
      · positivity
      · subst hn
        simp [c, PairingNorm_cnt]
    refine le_of_mul_le_mul_left ?_ hpos
    calc (m : ℝ) ^ c * (m : ℝ) ^ n * ‖M x‖ ^ 2 = (m : ℝ) ^ c * ((m : ℝ) ^ n * ‖M x‖ ^ 2) := by
          ring
      _ ≤ A ^ n * (m : ℝ) ^ c * ((m : ℝ) ^ n * ‖x‖ ^ 2) := hinv
      _ = _ := by ring
  · push Not at hmn
    obtain ⟨hm, hn⟩ := hmn
    have hm0 : m = 0 := by omega
    subst hm0
    have : IsEmpty (Fin n → Fin 0) := isEmpty_fun.mpr ⟨⟨⟨0, by omega⟩⟩, inferInstance⟩
    have hM0 : M = 0 := by
      rw [hM, Finset.univ_eq_empty]
      simp
    rw [hM0, zero_apply, norm_zero, zero_pow two_ne_zero]
    positivity

end PairingNormAux

/-- Per-pairing bound: for Hermitian `D_a` and a pairing `σ` of `Fin (2p)`,
`‖Σ_{j : j∘σ = j} D_{j_0} ⋯ D_{j_{2p-1}}‖ ≤ ‖Σ_a D_a²‖^p` (operator norms). -/
theorem norm_sum_pairing_prod_le {k : Type*} [Fintype k] [DecidableEq k] {m p : ℕ}
    (D : Fin m → Matrix k k ℂ) (hD : ∀ a, (D a).IsHermitian) {σ : Equiv.Perm (Fin (2 * p))}
    (hσ : σ ∈ pairings (2 * p)) :
    ‖∑ j ∈ (Finset.univ : Finset (Fin (2 * p) → Fin m)).filter (fun j => ∀ i, j (σ i) = j i),
        (List.ofFn fun i => D (j i)).prod‖ ≤ ‖∑ a, D a * D a‖ ^ p := by
  have hσ' : ∀ i, σ (σ i) = i ∧ σ i ≠ i := by
    simpa only [pairings, Finset.mem_filter, Finset.mem_univ, true_and] using hσ
  let T : Fin m → EuclideanSpace ℂ k →L[ℂ] EuclideanSpace ℂ k :=
    fun a => Matrix.toEuclideanCLM (n := k) (𝕜 := ℂ) (D a)
  have hT : ∀ a x y, inner ℂ (T a x) y = inner ℂ x (T a y) := by
    intro a x y
    have hstar : star (T a) = T a := by
      simp only [T, ← map_star, Matrix.star_eq_conjTranspose, (hD a).eq]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hstar]
  have hL : Matrix.toEuclideanCLM (n := k) (𝕜 := ℂ)
      (∑ j ∈ (Finset.univ : Finset (Fin (2 * p) → Fin m)).filter
        (fun j => ∀ i, j (σ i) = j i), (List.ofFn fun i => D (j i)).prod) =
      ∑ j ∈ (Finset.univ : Finset (Fin (2 * p) → Fin m)).filter
        (fun j => ∀ i, j (σ i) = j i), (List.ofFn fun i => T (j i)).prod := by
    simp only [map_sum, map_list_prod, List.map_ofFn, Function.comp_def, T]
  have hR : Matrix.toEuclideanCLM (n := k) (𝕜 := ℂ) (∑ a, D a * D a) = ∑ a, T a * T a := by
    simp only [map_sum, map_mul, T]
  rw [← Matrix.l2_opNorm_toEuclideanCLM, hL, ← Matrix.l2_opNorm_toEuclideanCLM, hR]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have hcore := PairingNorm_core T hT σ hσ' x
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, ← pow_mul, mul_comm p 2]
  exact hcore

end LSBA
