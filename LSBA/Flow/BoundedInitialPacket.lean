import LSBA.Flow.BoundedInitial
import LSBA.Prop.Objects
import LSBA.Primitive.Early
import LSBA.Averaging.Expansion

/-!
# Lemma 5.3 [fo:lem:bounded-initial]: the initial input at bounded coupling

The components of the input (5.22) [gc:eq:one-step-input] at each deterministic `u ∈ [0, 1/2]` on
`0 < g ≤ C`, `RegBdd`, `3 ≤ L ≤ W²`: loop errors, block averages, pairs and tails, and their
packet `boundedInitial_packet` (Lemma 5.3 [fo:lem:bounded-initial], fixed-time form). The
operator-norm clause of (5.23) [gc:eq:iteration-input] is not part of the packet.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The range of Lemma 5.3 [fo:lem:bounded-initial] in fixed-time form:
`0 < g`, `RegBdd C B c'`, `3 ≤ L ≤ W²`, `u ∈ [0, 1/2]`. -/
def initBdd (C B c' : ℝ) (W : ℕ) : Set FlowPt :=
  {p | 0 < p.g ∧ RegBdd C B c' p.L p.g p.E ∧ 3 ≤ p.L ∧ (p.L : ℝ) ≤ (W : ℝ) ^ 2 ∧ 0 ≤ p.u ∧
    p.u ≤ 1 / 2}

/-! ### Operator-norm tools for block matrices -/

section PacketNorms

open scoped Matrix.Norms.L2Operator

/-- An entry is bounded by the operator norm. -/
private theorem packet_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  have h1 := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j 1)
  rw [← Matrix.cstar_norm_def] at h1
  have h2 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [h2, mul_one] at h1
  refine le_trans ?_ h1
  have h3 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)).ofLp i =
      A i j := by
    rw [Matrix.ofLp_toEuclideanCLM]
    simp [Matrix.mulVec, dotProduct]
  rw [← h3]
  exact PiLp.norm_apply_le _ i

/-- The block projection `P_a = W E_a`. -/
private def pkP (W L : ℕ) (a : Fin L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.diagonal fun p => if p.1 = a then 1 else 0

private theorem pkP_mul_self (W L : ℕ) (a : Fin L) : pkP W L a * pkP W L a = pkP W L a := by
  unfold pkP
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> simp

private theorem blockE_eq_pkP (W L : ℕ) (a : Fin L) :
    blockE W L a = ((W : ℂ)⁻¹) • pkP W L a := by
  unfold blockE pkP
  rw [← Matrix.diagonal_smul]
  congr 1
  funext p
  by_cases h : p.1 = a <;> simp [h]

private theorem norm_pkP_le (W L : ℕ) (a : Fin L) : ‖pkP W L a‖ ≤ 1 := by
  unfold pkP
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

/-- The inclusion of block `a`. -/
private def pkR (W L : ℕ) (a : Fin L) : Matrix (Fin W) (Fin L × Fin W) ℂ :=
  Matrix.of fun α p => if p = (a, α) then 1 else 0

private theorem norm_pkR_le (W L : ℕ) (a : Fin L) : ‖pkR W L a‖ ≤ 1 := by
  set R := pkR W L a
  have hRR : R * Rᴴ = 1 := by
    ext i j
    simp only [R, pkR, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.one_apply]
    rw [Finset.sum_eq_single (a, i)]
    · by_cases hij : i = j
      · subst hij; simp
      · have : ((a, i) : Fin L × Fin W) ≠ (a, j) := fun e => hij (Prod.mk.inj e).2
        simp [this, hij]
    · intro p _ hp; simp [hp]
    · simp
  have h1 : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp
  have h2 : ‖Rᴴ‖ * ‖Rᴴ‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, Matrix.conjTranspose_conjTranspose, hRR]
    exact h1
  rw [← Matrix.l2_opNorm_conjTranspose]
  nlinarith [norm_nonneg Rᴴ]

/-- `‖P_a X P_b‖ ≤ ‖X_{ab}‖`. -/
private theorem norm_pkP_sandwich_le (W L : ℕ) (a b : Fin L)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    ‖pkP W L a * X * pkP W L b‖ ≤ ‖X.submatrix (fun α => (a, α)) (fun β => (b, β))‖ := by
  have he : pkP W L a * X * pkP W L b =
      (pkR W L a)ᴴ * X.submatrix (fun α => (a, α)) (fun β => (b, β)) * pkR W L b := by
    ext ⟨p1, p2⟩ ⟨q1, q2⟩
    simp only [pkP, Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [pkR, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.submatrix_apply, Prod.mk.injEq]
    by_cases hp : p1 = a <;> by_cases hq : q1 = b
    · subst hp hq
      simp [Finset.sum_ite_eq]
    · simp [hq]
    · simp [hp]
    · simp [hp]
  rw [he]
  calc ‖(pkR W L a)ᴴ * X.submatrix (fun α => (a, α)) (fun β => (b, β)) * pkR W L b‖
      ≤ ‖(pkR W L a)ᴴ * X.submatrix (fun α => (a, α)) (fun β => (b, β))‖ * ‖pkR W L b‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(pkR W L a)ᴴ‖ * ‖X.submatrix (fun α => (a, α)) (fun β => (b, β))‖) * ‖pkR W L b‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * ‖X.submatrix (fun α => (a, α)) (fun β => (b, β))‖) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
        · exact norm_pkR_le W L a
        · exact norm_pkR_le W L b
    _ = _ := by ring

end PacketNorms

/-! ### Cyclic distance and word lengths -/

private theorem packet_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private theorem packet_cycDist_comm {L : ℕ} (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

private theorem packet_cycDist_self {L : ℕ} (a : Fin L) : cycDist a a = 0 := by
  simp [cycDist]

private theorem packet_cycDist_tri {L : ℕ} (a b c : Fin L) :
    cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [cycDist, packet_mod ha hb, packet_mod hb ha, packet_mod ha hc,
    packet_mod hc ha, packet_mod hb hc, packet_mod hc hb]
  split_ifs <;> omega

private theorem packet_cycDist_le {L : ℕ} (a b : Fin L) : cycDist a b ≤ L := by
  have ha := a.isLt
  unfold cycDist
  exact (min_le_left _ _).trans (Nat.mod_lt _ (by omega)).le

/-- `Σ_b f(‖a-b‖_L) ≤ 2 Σ_{j<L} f(j)` for nonnegative `f`. -/
private theorem packet_sum_dist {L : ℕ} (a : Fin L) (h : ℕ → ℝ) (h0 : ∀ j, 0 ≤ h j) :
    ∑ b, h (cycDist a b) ≤ 2 * ∑ j ∈ Finset.range L, h j := by
  have ha := a.isLt
  have hinj : ∀ (g : Fin L → ℕ), Function.Injective g → (∀ b, g b < L) →
      ∑ b, h (g b) ≤ ∑ j ∈ Finset.range L, h j := by
    intro g hg hlt
    rw [← Finset.sum_image (f := h) (s := Finset.univ) (g := g) (fun x _ y _ hxy => hg hxy)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj
      obtain ⟨b, hb⟩ := hj
      rw [Finset.mem_range, ← hb]
      exact hlt b
    · intro i _ _
      exact h0 i
  have h1 : ∑ b : Fin L, h ((a.val + L - b.val) % L) ≤ ∑ j ∈ Finset.range L, h j := by
    apply hinj (fun b : Fin L => (a.val + L - b.val) % L)
    · intro b b' hbb
      have hb := b.isLt
      have hb' := b'.isLt
      simp only [packet_mod ha hb, packet_mod ha hb'] at hbb
      apply Fin.ext
      split_ifs at hbb <;> omega
    · intro b
      exact Nat.mod_lt _ (by omega)
  have h2 : ∑ b : Fin L, h ((b.val + L - a.val) % L) ≤ ∑ j ∈ Finset.range L, h j := by
    apply hinj (fun b : Fin L => (b.val + L - a.val) % L)
    · intro b b' hbb
      have hb := b.isLt
      have hb' := b'.isLt
      simp only [packet_mod hb ha, packet_mod hb' ha] at hbb
      apply Fin.ext
      split_ifs at hbb <;> omega
    · intro b
      exact Nat.mod_lt _ (by omega)
  have h3 : ∀ b : Fin L, h (cycDist a b) ≤
      h ((a.val + L - b.val) % L) + h ((b.val + L - a.val) % L) := by
    intro b
    unfold cycDist
    rcases min_choice ((a.val + L - b.val) % L) ((b.val + L - a.val) % L) with e | e
    · rw [e]; linarith [h0 ((b.val + L - a.val) % L)]
    · rw [e]; linarith [h0 ((a.val + L - b.val) % L)]
  calc ∑ b, h (cycDist a b) ≤ ∑ b : Fin L, (h ((a.val + L - b.val) % L) +
        h ((b.val + L - a.val) % L)) := Finset.sum_le_sum fun b _ => h3 b
    _ ≤ 2 * ∑ j ∈ Finset.range L, h j := by
        rw [Finset.sum_add_distrib]; linarith

/-- The geometric sum over the cycle: `Σ_b e^{-λ‖a-b‖_L} ≤ 2/(1 - e^{-λ})` for `λ > 0`. -/
private theorem packet_sum_exp {L : ℕ} (a : Fin L) {l : ℝ} (hl : 0 < l) :
    ∑ b, Real.exp (-(l * cycDist a b)) ≤ 2 / (1 - Real.exp (-l)) := by
  have hq0 : 0 ≤ Real.exp (-l) := (Real.exp_pos _).le
  have hq1 : Real.exp (-l) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := packet_sum_dist a (fun j => Real.exp (-(l * j))) fun j => (Real.exp_pos _).le
  refine h.trans ?_
  have e : ∀ j : ℕ, Real.exp (-(l * j)) = Real.exp (-l) ^ j := by
    intro j; rw [← Real.exp_nat_mul]; ring_nf
  simp only [e]
  have h1 : 0 < 1 - Real.exp (-l) := by linarith
  have hg : (∑ j ∈ Finset.range L, Real.exp (-l) ^ j) * (1 - Real.exp (-l)) ≤ 1 := by
    have := geom_sum_mul (Real.exp (-l)) L
    have hp : 0 ≤ Real.exp (-l) ^ L := pow_nonneg hq0 L
    nlinarith
  have hg' : ∑ j ∈ Finset.range L, Real.exp (-l) ^ j ≤ 1 / (1 - Real.exp (-l)) := by
    rw [le_div_iff₀ h1]; exact hg
  calc 2 * ∑ j ∈ Finset.range L, Real.exp (-l) ^ j ≤ 2 * (1 / (1 - Real.exp (-l))) := by linarith
    _ = 2 / (1 - Real.exp (-l)) := by ring

/-- The cyclic length of a word of length `n` is at most `n` times its periodic diameter. -/
private theorem packet_loopLen_le_diam {L n : ℕ} (a : Fin n → Fin L) :
    loopLen a ≤ n * wordDiam a := by
  unfold loopLen
  calc ∑ i : Fin n, cycDist (a i) (a (finRotate n i)) ≤ ∑ _i : Fin n, wordDiam a :=
        Finset.sum_le_sum fun i _ =>
          Finset.le_sup (f := fun p : Fin n × Fin n => cycDist (a p.1) (a p.2))
            (Finset.mem_univ (i, finRotate n i))
    _ = n * wordDiam a := by simp

/-- Two labels of a word are at cyclic distance at most the diameter. -/
private theorem packet_cycDist_le_diam {L n : ℕ} (a : Fin n → Fin L) (i j : Fin n) :
    cycDist (a i) (a j) ≤ wordDiam a :=
  Finset.le_sup (f := fun p : Fin n × Fin n => cycDist (a p.1) (a p.2)) (Finset.mem_univ (i, j))

private theorem packet_diam_le {L n : ℕ} (a : Fin n → Fin L) : wordDiam a ≤ L :=
  Finset.sup_le fun _ _ => packet_cycDist_le _ _

/-- Two labels of a word are at cyclic distance at most the cyclic length of the word. -/
private theorem packet_cycDist_le_loopLen {L n : ℕ} (w : Fin n → Fin L) (i j : Fin n) :
    cycDist (w i) (w j) ≤ loopLen w := by
  wlog hij : i ≤ j generalizing i j
  · rw [packet_cycDist_comm]; exact this j i (le_of_not_ge hij)
  set leg : ℕ → ℕ := fun q => if h : q + 1 < n then
    cycDist (w ⟨q, by omega⟩) (w ⟨q + 1, h⟩) else 0 with hleg
  have key : ∀ s : ℕ, ∀ h : i.val + s < n,
      cycDist (w i) (w ⟨i.val + s, h⟩) ≤ ∑ t ∈ Finset.range s, leg (i.val + t) := by
    intro s
    induction s with
    | zero => intro h; simp [packet_cycDist_self]
    | succ s ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := packet_cycDist_tri (w i) (w ⟨i.val + s, by omega⟩) (w ⟨i.val + (s + 1), h⟩)
      have h3 : leg (i.val + s) = cycDist (w ⟨i.val + s, by omega⟩) (w ⟨i.val + (s + 1), h⟩) := by
        have hlt : i.val + s + 1 < n := by omega
        simp only [hleg, hlt, ↓reduceDIte]
        rfl
      rw [Finset.sum_range_succ, h3]
      omega
  have hs := key (j.val - i.val) (by omega)
  have hj : (⟨i.val + (j.val - i.val), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
  rw [hj] at hs
  refine hs.trans ?_
  set F : ℕ → ℕ := fun q => if h : q < n then cycDist (w ⟨q, h⟩) (w (finRotate n ⟨q, h⟩)) else 0
    with hF
  have hlen : loopLen w = ∑ q ∈ Finset.range n, F q := by
    unfold loopLen
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hF, p.isLt, ↓reduceDIte]
  have hlegF : ∀ q, leg q ≤ F q := by
    intro q
    simp only [hleg, hF]
    by_cases h : q + 1 < n
    · have hq : q < n := by omega
      simp only [h, hq, ↓reduceDIte]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have : finRotate (n' + 1) ⟨q, by omega⟩ = ⟨q + 1, h⟩ := by
        apply Fin.ext
        rw [coe_finRotate_of_ne_last]
        intro e
        have := congrArg Fin.val e
        simp at this
        omega
      rw [this]
    · simp only [h, ↓reduceDIte]; exact Nat.zero_le _
  rw [hlen]
  calc ∑ t ∈ Finset.range (j.val - i.val), leg (i.val + t)
      ≤ ∑ t ∈ Finset.range (j.val - i.val), F (i.val + t) :=
        Finset.sum_le_sum fun t _ => hlegF _
    _ = ∑ q ∈ Finset.Ico i.val j.val, F q := by
        rw [Finset.sum_Ico_eq_sum_range]
    _ ≤ ∑ q ∈ Finset.range n, F q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          simp only [Finset.mem_Ico] at hq
          simp only [Finset.mem_range]
          have := j.isLt
          omega
        · intro _ _ _; exact Nat.zero_le _

/-- The periodic diameter is at most the cyclic length. -/
private theorem packet_diam_le_loopLen {L n : ℕ} (w : Fin n → Fin L) : wordDiam w ≤ loopLen w :=
  Finset.sup_le fun p _ => packet_cycDist_le_loopLen w p.1 p.2

/-! ### Loop bounds from block bounds -/

section PacketLoops

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ}

/-- The chain bound `‖Q_0 X_0 Q_1 X_1 ⋯ X_{q-1} Q_q‖ ≤ Π_p ‖Q_p X_p Q_{p+1}‖` for idempotent
contractions `Q_j`. -/
private theorem packet_chain {n : Type*} [Fintype n] [DecidableEq n] :
    ∀ (q : ℕ) (Q : Fin (q + 1) → Matrix n n ℂ) (X : Fin q → Matrix n n ℂ),
      (∀ j, Q j * Q j = Q j) → (∀ j, ‖Q j‖ ≤ 1) →
      ‖Q 0 * (List.ofFn fun p => X p * Q p.succ).prod‖ ≤ ∏ p, ‖Q p.castSucc * X p * Q p.succ‖
  | 0, Q, X, _, hn => by simpa using hn 0
  | q + 1, Q, X, hQ, hn => by
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    have IH := packet_chain q (fun j => Q j.succ) (fun i => X i.succ) (fun j => hQ _)
      (fun j => hn _)
    set R := (List.ofFn fun i : Fin q => X i.succ * Q i.succ.succ).prod with hR
    have e : Q 0 * (X 0 * Q (0 : Fin (q + 1)).succ * R) =
        (Q (0 : Fin (q + 1)).castSucc * X 0 * Q (0 : Fin (q + 1)).succ) *
          (Q (0 : Fin (q + 1)).succ * R) := by
      have h1 := hQ (0 : Fin (q + 1)).succ
      calc Q 0 * (X 0 * Q (0 : Fin (q + 1)).succ * R) =
          Q 0 * X 0 * (Q (0 : Fin (q + 1)).succ * Q (0 : Fin (q + 1)).succ) * R := by
            rw [h1]; noncomm_ring
        _ = _ := by simp only [Fin.castSucc_zero]; noncomm_ring
    rw [e]
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine IH.trans (le_of_eq ?_)
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Fin.succ_castSucc]

/-- `(Π_p Y_p (c P_p)) = c^q Π_p Y_p P_p`. -/
private theorem packet_prod_smul {n : Type*} [Fintype n] [DecidableEq n] (c : ℂ) :
    ∀ (q : ℕ) (Y P : Fin q → Matrix n n ℂ),
      (List.ofFn fun p => Y p * (c • P p)).prod = c ^ q • (List.ofFn fun p => Y p * P p).prod
  | 0, Y, P => by simp
  | q + 1, Y, P => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons,
      packet_prod_smul c q (fun i => Y i.succ) (fun i => P i.succ), pow_succ]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]

/-- `|Tr(P_c Z)| ≤ W ‖P_c Z‖`. -/
private theorem packet_trace_le (c : Fin L) (Z : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    ‖(pkP W L c * Z).trace‖ ≤ W * ‖pkP W L c * Z‖ := by
  have e : (pkP W L c * Z).trace = ∑ p : Fin L × Fin W,
      if p.1 = c then (pkP W L c * Z) p p else 0 := by
    unfold Matrix.trace
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Matrix.diag, pkP, Matrix.diagonal_mul]
    split_ifs <;> simp
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p : Fin L × Fin W, ‖(if p.1 = c then (pkP W L c * Z) p p else 0)‖ ≤
      ∑ p : Fin L × Fin W, (if p.1 = c then ‖pkP W L c * Z‖ else 0) := by
        refine Finset.sum_le_sum fun p _ => ?_
        split_ifs
        · exact packet_entry_le _ p p
        · simp
    _ = W * ‖pkP W L c * Z‖ := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
        · simp
        · intro b _ hb; simp [hb]
        · simp

/-- The cyclic predecessor in `Fin (q+1)`. -/
private def packet_prev {q : ℕ} (p : Fin (q + 1)) : Fin (q + 1) :=
  if h : p.val = 0 then Fin.last q else ⟨p.val - 1, by omega⟩

private theorem packet_rot_prev {q : ℕ} (p : Fin (q + 1)) :
    finRotate (q + 1) (packet_prev p) = p := by
  unfold packet_prev
  split_ifs with h
  · rw [finRotate_last]; exact Fin.ext h.symm
  · apply Fin.ext
    rw [coe_finRotate_of_ne_last]
    · simp; omega
    · intro e
      have := congrArg Fin.val e
      simp at this
      omega

/-- `loopLen` as the sum over legs `(prev p, p)`. -/
private theorem packet_loopLen_prev {q : ℕ} (w : Fin (q + 1) → Fin L) :
    ∑ p, (cycDist (w (packet_prev p)) (w p) : ℝ) = loopLen w := by
  have hinj : Function.Injective (packet_prev (q := q)) := by
    intro p p' h
    have := congrArg (finRotate (q + 1)) h
    rwa [packet_rot_prev, packet_rot_prev] at this
  have hbij : Function.Bijective (packet_prev (q := q)) :=
    (Finite.injective_iff_bijective).mp hinj
  unfold loopLen
  push_cast
  refine Fintype.sum_bijective _ hbij _ _ fun p => ?_
  rw [packet_rot_prev]

/-- The loop bound `|ℒ_q(w)| ≤ W^{1-q} g^q e^{-μ loopLen(w)}` from leg bounds
`‖P_x X^s P_y‖ ≤ g e^{-μ‖x-y‖_L}`. -/
private theorem packet_loop_le (hW : 1 ≤ W) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    {g₀ μ : ℝ}
    (hleg : ∀ x y s, ‖pkP W L x * sgnMat X s * pkP W L y‖ ≤ g₀ * Real.exp (-(μ * cycDist x y)))
    {q : ℕ} (hq : 1 ≤ q) (w : Fin q → Fin L) (τ : Fin q → Bool) :
    ‖loopTr X w τ‖ ≤ (W : ℝ) ^ (1 - (q : ℝ)) * (g₀ ^ q * Real.exp (-(μ * loopLen w))) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set Y := (List.ofFn fun p : Fin (q' + 1) => sgnMat X (τ p) * pkP W L (w p)).prod with hY
  have hl : loopTr X w τ = ((W : ℂ)⁻¹) ^ (q' + 1) * Y.trace := by
    unfold loopTr
    simp only [blockE_eq_pkP]
    rw [packet_prod_smul, Matrix.trace_smul, smul_eq_mul]
  have hYP : Y * pkP W L (w (Fin.last q')) = Y := by
    rw [hY, List.ofFn_succ', List.prod_concat, Matrix.mul_assoc, Matrix.mul_assoc,
      pkP_mul_self]
  have htr : Y.trace = (pkP W L (w (Fin.last q')) * Y).trace := by
    rw [← Matrix.trace_mul_comm, hYP]
  set Q : Fin (q' + 2) → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := fun j =>
    pkP W L (w (if h : j.val = 0 then Fin.last q' else ⟨j.val - 1, by omega⟩)) with hQ
  have hQ0 : Q 0 = pkP W L (w (Fin.last q')) := by simp [hQ]
  have hQs : ∀ p : Fin (q' + 1), Q p.succ = pkP W L (w p) := by
    intro p; simp only [hQ, Fin.val_succ]; simp
  have hQc : ∀ p : Fin (q' + 1), Q p.castSucc = pkP W L (w (packet_prev p)) := by
    intro p; simp only [hQ, packet_prev, Fin.val_castSucc]
  have hch := packet_chain (q' + 1) Q (fun p => sgnMat X (τ p))
    (fun j => pkP_mul_self W L _) (fun j => norm_pkP_le W L _)
  simp only [hQ0, hQs, hQc] at hch
  have hprod : ∏ p : Fin (q' + 1), ‖pkP W L (w (packet_prev p)) * sgnMat X (τ p) *
      pkP W L (w p)‖ ≤ g₀ ^ (q' + 1) * Real.exp (-(μ * loopLen w)) := by
    calc ∏ p : Fin (q' + 1), ‖pkP W L (w (packet_prev p)) * sgnMat X (τ p) *
        pkP W L (w p)‖ ≤ ∏ p : Fin (q' + 1),
          g₀ * Real.exp (-(μ * cycDist (w (packet_prev p)) (w p))) :=
          Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) fun p _ => hleg _ _ _
      _ = g₀ ^ (q' + 1) * Real.exp (-(μ * loopLen w)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← Real.exp_sum, ← packet_loopLen_prev w, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [hl, htr, norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
  have hT := (packet_trace_le (w (Fin.last q')) Y).trans
    (mul_le_mul_of_nonneg_left (hch.trans hprod) (Nat.cast_nonneg W))
  have hWp : (W : ℝ) ^ (1 - ((q' + 1 : ℕ) : ℝ)) = ((W : ℝ)⁻¹) ^ (q' + 1) * W := by
    rw [Real.rpow_sub hW0, Real.rpow_one, Real.rpow_natCast, inv_pow]; ring
  rw [hWp, mul_assoc]
  exact mul_le_mul_of_nonneg_left hT (by positivity)

end PacketLoops

/-! ### The bounded-coupling constants -/

/-- `η₀ = c'/(2 max{1,C}²)`, a lower bound for `η_u` at `u ≤ 1/2` on the regular domain. -/
private def pkEta (C c' : ℝ) : ℝ := c' / (2 * (max 1 C) ^ 2)

/-- The Combes–Thomas rate `μ₀ = log(1 + η₀/4)`. -/
private def pkMu (C c' : ℝ) : ℝ := Real.log (1 + pkEta C c' / 4)

/-- The Combes–Thomas constant `g₀ = 2/η₀`. -/
private def pkG (C c' : ℝ) : ℝ := 2 / pkEta C c'

/-- The cycle sum `Σ_b e^{-μ₀‖a-b‖_L} ≤ 2/(1 - e^{-μ₀})`. -/
private def pkS (C c' : ℝ) : ℝ := 2 / (1 - Real.exp (-pkMu C c'))

/-- `c_ζ = (1 + 2C max{1,C})⁻¹`, so that `ζ_u ≥ c_ζ W⁻¹`. -/
private def pkCz (C : ℝ) : ℝ := (1 + 2 * C * max 1 C)⁻¹

private theorem pkEta_pos {C c' : ℝ} (hc' : 0 < c') : 0 < pkEta C c' := by
  unfold pkEta; positivity

private theorem pkMu_pos {C c' : ℝ} (hc' : 0 < c') : 0 < pkMu C c' := by
  unfold pkMu
  have := pkEta_pos (C := C) hc'
  exact Real.log_pos (by linarith)

private theorem pkMu_exp {C c' : ℝ} (hc' : 0 < c') : Real.exp (pkMu C c') - 1 = pkEta C c' / 4 := by
  unfold pkMu
  have := pkEta_pos (C := C) hc'
  rw [Real.exp_log (by linarith)]; ring

private theorem pkG_pos {C c' : ℝ} (hc' : 0 < c') : 0 < pkG C c' := by
  unfold pkG; have := pkEta_pos (C := C) hc'; positivity

private theorem pkS_pos {C c' : ℝ} (hc' : 0 < c') : 0 < pkS C c' := by
  unfold pkS
  have : Real.exp (-pkMu C c') < 1 := Real.exp_lt_one_iff.mpr (by linarith [pkMu_pos (C := C) hc'])
  have : 0 < 1 - Real.exp (-pkMu C c') := by linarith
  positivity

private theorem pkCz_pos {C : ℝ} (hC : 0 ≤ C) : 0 < pkCz C := by
  unfold pkCz
  have : 0 ≤ 2 * C * max 1 C := by have := le_max_left 1 C; positivity
  positivity

private theorem pk_sum_exp {C c' : ℝ} (hc' : 0 < c') {L : ℕ} (a : Fin L) :
    ∑ b, Real.exp (-(pkMu C c' * cycDist a b)) ≤ pkS C c' :=
  packet_sum_exp a (pkMu_pos hc')

private theorem pk_gamma_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

private theorem pk_gamma_le_one (g : ℝ) : gammaG g ≤ 1 := by
  unfold gammaG
  have h : (1 : ℝ) ≤ max 1 g := le_max_left _ _
  have : (1 : ℝ) ≤ (max 1 g) ^ 2 := one_le_pow₀ h
  exact inv_le_one_of_one_le₀ this

/-- `γ_g ≥ max{1,C}^{-2}` on `g ≤ C`. -/
private theorem pk_gamma_ge {C g : ℝ} (hgC : g ≤ C) : ((max 1 C) ^ 2)⁻¹ ≤ gammaG g := by
  unfold gammaG
  have h1 : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h2 : max 1 g ≤ max 1 C := max_le_max le_rfl hgC
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h1.le h2 2)

/-- `η_u ≥ η₀` on the regular domain for `u ≤ 1/2`. -/
private theorem pkEta_le_im {C B c' : ℝ} (hc' : 0 < c') {L : ℕ} {g E : ℝ}
    (hreg : RegBdd C B c' L g E) {u : ℝ} (hu : u ≤ 1 / 2) :
    pkEta C c' ≤ (zChar g E (mRoot g L E) u).im := by
  obtain ⟨hg0, hgC, -, hroot, hcm⟩ := hreg
  rw [im_zChar, etaChar]
  have hγ := pk_gamma_ge hgC
  unfold pkEta
  have hC2 : (0 : ℝ) < (max 1 C) ^ 2 := by
    have : (0 : ℝ) < max 1 C := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  have hm : c' ≤ (mRoot g L E).im := hcm
  have hγ0 : 0 < gammaG g := pk_gamma_pos g
  calc c' / (2 * (max 1 C) ^ 2) = (1 / 2) * ((max 1 C) ^ 2)⁻¹ * c' := by field_simp
    _ ≤ (1 - u) * gammaG g * (mRoot g L E).im := by
        have h1 : (1 / 2 : ℝ) ≤ 1 - u := by linarith
        have hc0 : 0 ≤ c' := hc'.le
        gcongr

/-- `1 ≤ ℓ_u ≤ 1 + 2C max{1,C}` on `[0, 1/2]` at bounded coupling. -/
private theorem pk_ell_bounds {C g : ℝ} (hg : 0 ≤ g) (hgC : g ≤ C) {L : ℕ} (hL : 1 ≤ L) {u : ℝ}
    (hu : u ≤ 1 / 2) :
    1 ≤ ellProp g L u ∧ ellProp g L u ≤ 1 + 2 * C * max 1 C := by
  have hγ0 := pk_gamma_pos g
  have hC0 : 0 ≤ C := hg.trans hgC
  have h1u : 0 < 1 - u := by linarith
  have hs : Real.sqrt (gammaG g * (1 - u)) = (max 1 g)⁻¹ * Real.sqrt (1 - u) := by
    rw [Real.sqrt_mul hγ0.le, gammaG, Real.sqrt_inv, Real.sqrt_sq (by
      linarith [le_max_left 1 g])]
  have hsu : (1 / 2 : ℝ) ≤ Real.sqrt (1 - u) := by
    rw [Real.le_sqrt (by norm_num) h1u.le]; nlinarith
  have hspos : 0 < Real.sqrt (1 - u) := by linarith
  have key : g / Real.sqrt (gammaG g * (1 - u)) ≤ 2 * C * max 1 C := by
    rw [hs, div_eq_mul_inv, mul_inv, inv_inv]
    have hinv : (Real.sqrt (1 - u))⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hspos (by norm_num)]; linarith
    have hmC : max 1 g ≤ max 1 C := max_le_max le_rfl hgC
    have hm0 : 0 ≤ max 1 g := le_trans zero_le_one (le_max_left _ _)
    calc g * (max 1 g * (Real.sqrt (1 - u))⁻¹) ≤ C * (max 1 C * 2) := by
          gcongr
      _ = 2 * C * max 1 C := by ring
  constructor
  · rw [ellProp]
    refine le_min (by exact_mod_cast hL) ?_
    have : 0 ≤ g / Real.sqrt (gammaG g * (1 - u)) := by positivity
    linarith
  · rw [ellProp]
    exact (min_le_right _ _).trans (by linarith)

/-- `ζ_u ≥ c_ζ W⁻¹` on `[0, 1/2]` at bounded coupling. -/
private theorem pk_zeta_ge {C : ℝ} {g : ℝ} (hg : 0 ≤ g) (hgC : g ≤ C)
    {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    pkCz C * (W : ℝ)⁻¹ ≤ zetaProp g W L u := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγ0 := pk_gamma_pos g
  have hγ1 := pk_gamma_le_one g
  obtain ⟨hℓ1, hℓb⟩ := pk_ell_bounds hg hgC hL hu
  set ℓ := ellProp g L u with hℓ
  unfold pkCz
  rw [zetaProp, ← hℓ, ← mul_inv]
  have hC0 : 0 ≤ C := hg.trans hgC
  have : 0 ≤ 2 * C * max 1 C := by have := le_max_left 1 C; positivity
  refine inv_anti₀ (mul_pos (mul_pos (mul_pos hW0 (by linarith)) (by linarith)) hγ0) ?_
  have h1 : ℓ * (1 - u) * gammaG g ≤ ℓ := by
    have : (1 - u) * gammaG g ≤ 1 := by nlinarith
    nlinarith
  calc (W : ℝ) * ℓ * (1 - u) * gammaG g = W * (ℓ * (1 - u) * gammaG g) := by ring
    _ ≤ W * (1 + 2 * C * max 1 C) := by
        refine mul_le_mul_of_nonneg_left (h1.trans hℓb) hW0.le
    _ = (1 + 2 * C * max 1 C) * W := by ring

/-- `ζ_u ≤ 2 max{1,C}² W⁻¹` on `[0, 1/2]` at bounded coupling. -/
private theorem pk_zeta_le {C : ℝ} {g : ℝ} (hg : 0 ≤ g) (hgC : g ≤ C)
    {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L) {u : ℝ} (hu : u ≤ 1 / 2) :
    zetaProp g W L u ≤ 2 * (max 1 C) ^ 2 * (W : ℝ)⁻¹ := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγ := pk_gamma_ge hgC
  obtain ⟨hℓ1, -⟩ := pk_ell_bounds hg hgC hL hu
  have hC2 : (0 : ℝ) < (max 1 C) ^ 2 := by
    have : (0 : ℝ) < max 1 C := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  rw [zetaProp]
  have h2 : (2 * (max 1 C) ^ 2 * (W : ℝ)⁻¹) = ((W : ℝ) * 1 * (1 / 2) * ((max 1 C) ^ 2)⁻¹)⁻¹ := by
    field_simp
  rw [h2]
  refine inv_anti₀ (by positivity) ?_
  have h1u : (1 / 2 : ℝ) ≤ 1 - u := by linarith
  gcongr

/-! ### Combes–Thomas bounds on the domain -/

section PacketCT

open scoped Matrix.Norms.L2Operator

/-- `H_u = A_g ⊗ I + V` with `V = √(uγ_g) V(ω)` Hermitian and block diagonal. -/
private theorem packet_ct {C B c' : ℝ} (hc' : 0 < c') {L : ℕ} {g E : ℝ}
    (hreg : RegBdd C B c' L g E) {u : ℝ} (hu : u ≤ 1 / 2) (W : ℕ) (ω : Ω W L) (a b : Fin L) :
    ‖(resolventMat (flowH g W L u ω) (zChar g E (mRoot g L E) u)).submatrix
        (fun α => (a, α)) (fun β => (b, β))‖ ≤
      pkG C c' * Real.exp (-(pkMu C c' * cycDist a b)) := by
  set V : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    ((Real.sqrt (u * gammaG g) : ℝ) : ℂ) • blockV W L ω with hVdef
  have hV : V.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hVdef, Matrix.conjTranspose_smul, (blockV_isHermitian W L ω).eq, Complex.star_def,
      Complex.conj_ofReal]
  have hVb : ∀ p q : Fin L × Fin W, p.1 ≠ q.1 → V p q = 0 := by
    intro p q h; simp [hVdef, blockV, blockDiagOp, h]
  have e : flowH g W L u ω = Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + V := rfl
  rw [e]
  exact combesThomas_block W L g hreg.1 V hV hVb _ (pkEta_pos hc') (pkEta_le_im hc' hreg hu)
    (pkMu_pos hc').le (pkMu_exp hc').le a b

private theorem pkP_conjTranspose (W L : ℕ) (a : Fin L) : (pkP W L a)ᴴ = pkP W L a := by
  unfold pkP
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases h : p.1 = a <;> simp [h]

/-- Leg bounds `‖P_x G^s P_y‖ ≤ g₀ e^{-μ₀‖x-y‖_L}` on the domain. -/
private theorem packet_leg {C B c' : ℝ} (hc' : 0 < c') {L : ℕ} {g E : ℝ}
    (hreg : RegBdd C B c' L g E) {u : ℝ} (hu : u ≤ 1 / 2) (W : ℕ) (ω : Ω W L) (x y : Fin L)
    (s : Bool) :
    ‖pkP W L x * sgnMat (resolventMat (flowH g W L u ω) (zChar g E (mRoot g L E) u)) s *
        pkP W L y‖ ≤ pkG C c' * Real.exp (-(pkMu C c' * cycDist x y)) := by
  set G := resolventMat (flowH g W L u ω) (zChar g E (mRoot g L E) u)
  cases s
  · have e : pkP W L x * sgnMat G false * pkP W L y = (pkP W L y * G * pkP W L x)ᴴ := by
      simp only [sgnMat, Bool.false_eq_true, ite_false, Matrix.conjTranspose_mul,
        pkP_conjTranspose, Matrix.mul_assoc]
    rw [e, Matrix.l2_opNorm_conjTranspose, packet_cycDist_comm]
    exact (norm_pkP_sandwich_le W L y x G).trans (packet_ct hc' hreg hu W ω y x)
  · simp only [sgnMat, ite_true]
    exact (norm_pkP_sandwich_le W L x y G).trans (packet_ct hc' hreg hu W ω x y)

/-- Entries of `G_u` on the domain: `|G_{(a,α),(b,β)}| ≤ g₀`. -/
private theorem packet_G_entry {C B c' : ℝ} (hc' : 0 < c') {L : ℕ} {g E : ℝ}
    (hreg : RegBdd C B c' L g E) {u : ℝ} (hu : u ≤ 1 / 2) (W : ℕ) (ω : Ω W L)
    (e₁ e₂ : Fin L × Fin W) :
    ‖resolventMat (flowH g W L u ω) (zChar g E (mRoot g L E) u) e₁ e₂‖ ≤ pkG C c' := by
  have h := packet_entry_le ((resolventMat (flowH g W L u ω) (zChar g E (mRoot g L E) u)).submatrix
    (fun α => (e₁.1, α)) (fun β => (e₂.1, β))) e₁.2 e₂.2
  simp only [Matrix.submatrix_apply] at h
  refine h.trans ((packet_ct hc' hreg hu W ω e₁.1 e₂.1).trans ?_)
  have := pkG_pos (C := C) hc'
  have : Real.exp (-(pkMu C c' * cycDist e₁.1 e₂.1)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := pkMu_pos (C := C) hc'
    have : (0 : ℝ) ≤ cycDist e₁.1 e₂.1 := Nat.cast_nonneg _
    nlinarith
  nlinarith

/-- Entries of `M_B` on the domain: `|(M_B)_{ab}| ≤ g₀ e^{-μ₀‖a-b‖_L}`. -/
private theorem packet_M_entry {C B c' : ℝ} (hc' : 0 < c') {L : ℕ} {g E : ℝ}
    (hreg : RegBdd C B c' L g E) (a b : Fin L) :
    ‖dysonMat (hopB g) (gammaG g) L E (mRoot g L E) a b‖ ≤
      pkG C c' * Real.exp (-(pkMu C c' * cycDist a b)) := by
  have h0 := resolvent_flow_zero g E 1 L (mRoot g L E) (fun _ => 0)
  have h := packet_entry_le ((resolventMat (flowH g 1 L 0 (fun _ => 0))
    (zChar g E (mRoot g L E) 0)).submatrix (fun α => (a, α)) (fun β => (b, β))) 0 0
  rw [h0] at h
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply_eq,
    mul_one] at h
  refine h.trans ?_
  have := packet_ct hc' hreg (u := 0) (by norm_num) 1 (fun _ => 0) a b
  rwa [h0] at this

end PacketCT

/-- Row sums of `M_B`: `Σ_c |(M_B)_{ac}| ≤ g₀ S`. -/
private theorem packet_M_row {C B c' : ℝ} (hc' : 0 < c') {L : ℕ} {g E : ℝ}
    (hreg : RegBdd C B c' L g E) (a : Fin L) :
    ∑ c, ‖dysonMat (hopB g) (gammaG g) L E (mRoot g L E) a c‖ ≤ pkG C c' * pkS C c' := by
  calc ∑ c, ‖dysonMat (hopB g) (gammaG g) L E (mRoot g L E) a c‖ ≤
      ∑ c, pkG C c' * Real.exp (-(pkMu C c' * cycDist a c)) :=
        Finset.sum_le_sum fun c _ => packet_M_entry hc' hreg a c
    _ = pkG C c' * ∑ c, Real.exp (-(pkMu C c' * cycDist a c)) := by rw [Finset.mul_sum]
    _ ≤ pkG C c' * pkS C c' := mul_le_mul_of_nonneg_left (pk_sum_exp hc' a) (pkG_pos hc').le

/-- `Σ_c |(M_B)_{ac}|² ≤ g₀² S`. -/
private theorem packet_M_row2 {C B c' : ℝ} (hc' : 0 < c') {L : ℕ} {g E : ℝ}
    (hreg : RegBdd C B c' L g E) (a : Fin L) :
    ∑ c, ‖dysonMat (hopB g) (gammaG g) L E (mRoot g L E) a c‖ ^ 2 ≤ pkG C c' ^ 2 * pkS C c' := by
  have hG := pkG_pos (C := C) hc'
  calc ∑ c, ‖dysonMat (hopB g) (gammaG g) L E (mRoot g L E) a c‖ ^ 2 ≤
      ∑ c, pkG C c' ^ 2 * Real.exp (-(pkMu C c' * cycDist a c)) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 := packet_M_entry hc' hreg a c
        have h2 : Real.exp (-(pkMu C c' * cycDist a c)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have := pkMu_pos (C := C) hc'
          have : (0 : ℝ) ≤ cycDist a c := Nat.cast_nonneg _
          nlinarith
        have h3 : 0 < Real.exp (-(pkMu C c' * cycDist a c)) := Real.exp_pos _
        calc ‖dysonMat (hopB g) (gammaG g) L E (mRoot g L E) a c‖ ^ 2 ≤
            (pkG C c' * Real.exp (-(pkMu C c' * cycDist a c))) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ = pkG C c' ^ 2 * (Real.exp (-(pkMu C c' * cycDist a c)) *
              Real.exp (-(pkMu C c' * cycDist a c))) := by ring
          _ ≤ pkG C c' ^ 2 * (Real.exp (-(pkMu C c' * cycDist a c)) * 1) := by gcongr
          _ = _ := by ring
    _ = pkG C c' ^ 2 * ∑ c, Real.exp (-(pkMu C c' * cycDist a c)) := by rw [Finset.mul_sum]
    _ ≤ pkG C c' ^ 2 * pkS C c' := mul_le_mul_of_nonneg_left (pk_sum_exp hc' a) (by positivity)

/-- The diagonal of `M_B` is the anchor: `(M_B)_{aa} = m`. -/
private theorem packet_M_diag {C B c' : ℝ} {L : ℕ} {g E : ℝ} (hreg : RegBdd C B c' L g E)
    (a : Fin L) : dysonMat (hopB g) (gammaG g) L E (mRoot g L E) a a = mRoot g L E := by
  have hγpos := pk_gamma_pos g
  have hm := hreg.2.2.2.1
  have hw : 0 < ((E : ℂ) + (gammaG g : ℝ) * mRoot g L E).im := by
    simpa using mul_pos hγpos hm.1
  rw [dysonMat_diag (hopB g) (gammaG g) L (Fin.pos a) (E : ℂ) (mRoot g L E) hw a]
  exact hm.2.symm

/-- `|m| ≤ g₀` on the domain. -/
private theorem packet_m_le {C B c' : ℝ} (hc' : 0 < c') {L : ℕ} (hL : 1 ≤ L) {g E : ℝ}
    (hreg : RegBdd C B c' L g E) : ‖mRoot g L E‖ ≤ pkG C c' := by
  have a : Fin L := ⟨0, hL⟩
  rw [← packet_M_diag hreg a]
  refine (packet_M_entry hc' hreg a a).trans ?_
  simp [packet_cycDist_self]

/-! ### Tools for `PrecMax` -/

section PacketPrec

variable {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι}

/-- A change of labels: if the bound `‖X_l‖ ≤ t Y_l` for all `l` forces `‖X'_{l'}‖ ≤ t Y'_{l'}`
for all `l'`, then `X ≺ Y` gives `X' ≺ Y'`. -/
private theorem packet_pm_relabel {Λ Λ' : ℕ → ι → Type*}
    {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ} {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ}
    {X' : (W : ℕ) → (p : ι) → Λ' W p → Ω W (vol p) → ℂ} {Y' : (W : ℕ) → (p : ι) → Λ' W p → ℝ}
    (h : PrecMax vol Dom X Y)
    (hX : ∀ W : ℕ, 1 ≤ W → ∀ p ∈ Dom W, ∀ ω (t : ℝ), 0 ≤ t →
      (∀ l, ‖X W p l ω‖ ≤ t * Y W p l) → ∀ l', ‖X' W p l' ω‖ ≤ t * Y' W p l') :
    PrecMax vol Dom X' Y' := by
  intro ε D hε hD
  obtain ⟨W₀, hW₀⟩ := h ε D hε hD
  refine ⟨max W₀ 1, fun W hW p hp => (measure_mono ?_).trans
    (hW₀ W ((le_max_left _ _).trans hW) p hp)⟩
  rintro ω ⟨l', hl'⟩
  by_contra hne
  simp only [Set.mem_ofPred_eq, not_exists, not_lt] at hne
  have := hX W ((le_max_right _ _).trans hW) p hp ω ((W : ℝ) ^ ε)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) hne l'
  linarith

/-- A fixed constant in the bound can be dropped. -/
private theorem packet_pm_const {Λ : ℕ → ι → Type*}
    {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ} {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ}
    {K : ℝ} (h : PrecMax vol Dom X (fun W p l => K * Y W p l))
    (hY : ∀ W p, p ∈ Dom W → ∀ l, 0 ≤ Y W p l) :
    PrecMax vol Dom X Y := by
  intro ε D hε hD
  obtain ⟨W₀, hW₀⟩ := h (ε / 2) D (by positivity) hD
  have ht : Tendsto (fun W : ℕ => (W : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  obtain ⟨W₁, hW₁⟩ := eventually_atTop.mp (ht.eventually_ge_atTop K)
  refine ⟨max (max W₀ W₁) 1, fun W hW p hp => (measure_mono ?_).trans
    (hW₀ W ((le_max_left _ _).trans ((le_max_left _ _).trans hW)) p hp)⟩
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hK := hW₁ W ((le_max_right _ _).trans ((le_max_left _ _).trans hW))
  rintro ω ⟨l, hl⟩
  refine ⟨l, lt_of_le_of_lt ?_ hl⟩
  have hsq : (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) = (W : ℝ) ^ ε := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  have h0 : 0 ≤ (W : ℝ) ^ (ε / 2) := Real.rpow_nonneg hW0.le _
  calc (W : ℝ) ^ (ε / 2) * (K * Y W p l) ≤ (W : ℝ) ^ (ε / 2) * ((W : ℝ) ^ (ε / 2) * Y W p l) := by
        gcongr
        exact hY W p hp l
    _ = (W : ℝ) ^ ε * Y W p l := by rw [← mul_assoc, hsq]

/-- A deterministic bound `‖X‖ ≤ Y` for all large `W` gives `X ≺ Y`. -/
private theorem packet_pm_eventually {Λ : ℕ → ι → Type*}
    {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ} {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ}
    (hY : ∀ W p, p ∈ Dom W → ∀ l, 0 ≤ Y W p l)
    (h : ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ p ∈ Dom W, ∀ l ω, ‖X W p l ω‖ ≤ Y W p l) :
    PrecMax vol Dom X Y := by
  intro ε D hε hD
  obtain ⟨W₁, hW₁⟩ := h
  refine ⟨max W₁ 1, fun W hW p hp => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (le_max_right _ _).trans hW
  have hempty : {ω | ∃ l : Λ W p, (W : ℝ) ^ ε * Y W p l < ‖X W p l ω‖} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    intro l
    refine (hW₁ W ((le_max_left _ _).trans hW) p hp l ω).trans ?_
    exact le_mul_of_one_le_left (hY W p hp l) (Real.one_le_rpow hW1 hε.le)
  rw [hempty, measure_empty]
  exact bot_le

/-- A deterministic bound `‖X‖ ≤ K Y` at `W ≥ 1` with a fixed constant gives `X ≺ Y`. -/
private theorem packet_pm_of_le {Λ : ℕ → ι → Type*}
    {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ} {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ}
    (K : ℝ) (hY : ∀ W p, p ∈ Dom W → ∀ l, 0 ≤ Y W p l)
    (h : ∀ W : ℕ, 1 ≤ W → ∀ p ∈ Dom W, ∀ l ω, ‖X W p l ω‖ ≤ K * Y W p l) :
    PrecMax vol Dom X Y := by
  refine packet_pm_const (K := max K 0) (packet_pm_eventually (fun W p hp l =>
    mul_nonneg (le_max_right _ _) (hY W p hp l)) ⟨1, fun W hW p hp l ω => ?_⟩) hY
  exact (h W hW p hp l ω).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hY W p hp l))

private lemma packet_two_le (W : ℕ) (hW : 2 ≤ W) (D : ℝ) :
    ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) ≤
      ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  have hWpos : (0 : ℝ) < W := by linarith
  have hnn : 0 ≤ (W : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hWpos.le _
  rw [← ENNReal.ofReal_add hnn hnn]
  apply ENNReal.ofReal_le_ofReal
  have e : (W : ℝ) ^ (-(D + 1)) = (W : ℝ) ^ (-D) * (W : ℝ)⁻¹ := by
    rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
  have hpos : 0 < (W : ℝ) ^ (-D) := Real.rpow_pos_of_pos hWpos _
  have hinv : (W : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW2
  rw [e]
  nlinarith

/-- Sums, with nonnegative bounds on the family only: `‖X‖ ≤ ‖X₁‖ + ‖X₂‖`, `X₁ ≺ Y₁` and
`X₂ ≺ Y₂` give `X ≺ Y₁ + Y₂`. -/
private theorem packet_pm_add {Λ : ℕ → ι → Type*}
    {X X₁ X₂ : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ}
    {Y₁ Y₂ : (W : ℕ) → (p : ι) → Λ W p → ℝ} (h₁ : PrecMax vol Dom X₁ Y₁)
    (h₂ : PrecMax vol Dom X₂ Y₂) (hY₁ : ∀ W p, p ∈ Dom W → ∀ l, 0 ≤ Y₁ W p l)
    (hY₂ : ∀ W p, p ∈ Dom W → ∀ l, 0 ≤ Y₂ W p l)
    (hX : ∀ W : ℕ, 1 ≤ W → ∀ p ∈ Dom W, ∀ l ω, ‖X W p l ω‖ ≤ ‖X₁ W p l ω‖ + ‖X₂ W p l ω‖) :
    PrecMax vol Dom X (fun W p l => Y₁ W p l + Y₂ W p l) := by
  intro ε D hε hD
  obtain ⟨W₁, hW₁⟩ := h₁ (ε / 2) (D + 1) (by positivity) (by linarith)
  obtain ⟨W₂, hW₂⟩ := h₂ (ε / 2) (D + 1) (by positivity) (by linarith)
  refine ⟨max (max W₁ W₂) 2, fun W hW p hp => ?_⟩
  have h1 : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have h2 : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have h3 : 2 ≤ W := (le_max_right _ _).trans hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hle : (W : ℝ) ^ (ε / 2) ≤ (W : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  calc μ W (vol p) {ω | ∃ l : Λ W p, (W : ℝ) ^ ε * (Y₁ W p l + Y₂ W p l) < ‖X W p l ω‖}
      ≤ μ W (vol p) ({ω | ∃ l : Λ W p, (W : ℝ) ^ (ε / 2) * Y₁ W p l < ‖X₁ W p l ω‖} ∪
          {ω | ∃ l : Λ W p, (W : ℝ) ^ (ε / 2) * Y₂ W p l < ‖X₂ W p l ω‖}) := by
        apply measure_mono
        rintro ω ⟨l, hl⟩
        by_contra hcon
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hcon
        have c1 := hcon.1 l
        have c2 := hcon.2 l
        have hs : 0 ≤ Y₁ W p l + Y₂ W p l := add_nonneg (hY₁ W p hp l) (hY₂ W p hp l)
        have := hX W (by omega) p hp l ω
        have : ‖X W p l ω‖ ≤ (W : ℝ) ^ ε * (Y₁ W p l + Y₂ W p l) :=
          calc ‖X W p l ω‖ ≤ (W : ℝ) ^ (ε / 2) * (Y₁ W p l + Y₂ W p l) := by linarith
            _ ≤ _ := mul_le_mul_of_nonneg_right hle hs
        linarith
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) :=
        add_le_add (hW₁ W h1 p hp) (hW₂ W h2 p hp)
    _ ≤ _ := packet_two_le W h3 D

end PacketPrec

/-! ### Moments and tails -/

section PacketMoments

variable {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} [IsProbabilityMeasure P]

/-- `E f^n ≤ s^n + K^n δ` for `0 ≤ f ≤ K` with `P(f > s) ≤ δ`. -/
private theorem packet_moment_of_tail {f : Ω' → ℝ} (hf0 : ∀ x, 0 ≤ f x) {K s δ : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ x, f x ≤ K) (hs : 0 ≤ s) (n : ℕ)
    (hP : P {x | s < f x} ≤ ENNReal.ofReal δ)
    (hδ : 0 ≤ δ) : ∫ x, f x ^ n ∂P ≤ s ^ n + K ^ n * δ := by
  set S := {x | s < f x}
  set T := toMeasurable P S
  have hT : MeasurableSet T := measurableSet_toMeasurable P S
  have hpt : ∀ x, f x ^ n ≤ s ^ n + T.indicator (fun _ => K ^ n) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem (subset_toMeasurable P S hx)]
      have : f x ^ n ≤ K ^ n := pow_le_pow_left₀ (hf0 x) (hK x) n
      have : 0 ≤ s ^ n := pow_nonneg hs n
      linarith
    · have hle : f x ≤ s := not_lt.mp hx
      have h1 : f x ^ n ≤ s ^ n := pow_le_pow_left₀ (hf0 x) hle n
      have h2 : 0 ≤ T.indicator (fun _ => K ^ n) x := by
        by_cases hxT : x ∈ T
        · rw [Set.indicator_of_mem hxT]
          exact (pow_nonneg (hf0 x) n).trans (pow_le_pow_left₀ (hf0 x) (hK x) n)
        · rw [Set.indicator_of_notMem hxT]
      linarith
  have hint : Integrable (fun x => s ^ n + T.indicator (fun _ => K ^ n) x) P :=
    (integrable_const _).add ((integrable_const _).indicator hT)
  have hle := integral_mono_of_nonneg (ae_of_all _ fun x => pow_nonneg (hf0 x) n) hint
    (ae_of_all _ hpt)
  have heq : ∫ x, (s ^ n + T.indicator (fun _ => K ^ n) x) ∂P = s ^ n + K ^ n * P.real T := by
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hT), integral_const,
      integral_indicator_const _ hT]
    simp [mul_comm]
  have hPT : P.real T ≤ δ := by
    rw [measureReal_def, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hδ hP
  rw [heq] at hle
  have hKn : 0 ≤ K ^ n := pow_nonneg hK0 n
  nlinarith

/-- Markov's inequality for `f^n`. -/
private theorem packet_markov {f : Ω' → ℝ} (hf0 : ∀ x, 0 ≤ f x) {n : ℕ}
    (hint : Integrable (fun x => f x ^ n) P) {t : ℝ} (ht : 0 < t) :
    P {x | t < f x} ≤ ENNReal.ofReal ((∫ x, f x ^ n ∂P) / t ^ n) := by
  have hsub : {x | t < f x} ⊆ {x | t ^ n ≤ f x ^ n} := fun x hx =>
    pow_le_pow_left₀ ht.le (le_of_lt hx) n
  have hM := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => pow_nonneg (hf0 x) n) hint
    (t ^ n)
  have htn : 0 < t ^ n := pow_pos ht n
  have h1 : P.real {x | t ^ n ≤ f x ^ n} ≤ (∫ x, f x ^ n ∂P) / t ^ n := by
    rw [le_div_iff₀ htn, mul_comm]; exact hM
  calc P {x | t < f x} ≤ P {x | t ^ n ≤ f x ^ n} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {x | t ^ n ≤ f x ^ n}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h1

end PacketMoments

/-! ### The primitive family and the loop-error component -/

/-- The model primitive loops of (5.10) [fo:eq:primitive], with the value `0` at length zero. -/
private def pkK (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) : ℝ → LoopFam L :=
  fun t n b τ => if n = 0 then 0 else primLoop g W L E m t (k := n) b τ

/-- The family `pkK` satisfies (5.10) [fo:eq:primitive] at every length: for `n ≥ 2` by the tree
expansion, and for `n ≤ 1` both sides vanish; the cuts only evaluate lengths `≥ 1`. -/
private theorem pkK_deriv {g E : ℝ} {W L : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L) {m : ℂ}
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (u : ℝ) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    IsPrimDeriv (gammaG g) W L (pkK g W L E m) u := by
  intro n a σ
  have hcut : cutSumFam (pkK g W L E m u) a σ =
      cutSumFam (fun n b τ => primLoop g W L E m u (k := n) b τ) a σ := by
    unfold cutSumFam pkK
    simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pkK, ↓reduceIte]
    have h0 : cutSumFam (pkK g W L E m u) a σ = 0 := by simp [cutSumFam]
    rw [h0, mul_zero]
    exact hasDerivAt_const _ _
  · have e : (fun r => pkK g W L E m r n a σ) = fun r => primLoop g W L E m r a σ := by
      funext r; simp [pkK, hn.ne']
    rw [e, hcut]
    by_cases hn2 : 2 ≤ n
    · exact primLoop_hasDerivAt g W L hW hL E m hm u hu hn2 a σ
    · obtain rfl : n = 1 := by omega
      have h0 : cutSumFam (fun n b τ => primLoop g W L E m u (k := n) b τ) a σ = 0 := by
        simp [cutSumFam]
      rw [h0, mul_zero]
      have e2 : (fun r => primLoop g W L E m r a σ) = fun _ => primLoop g W L E m u a σ :=
        funext fun _ => rfl
      rw [e2]
      exact hasDerivAt_const _ _

/-- `|𝒦_n| = W^{1-n} |F_n|`. -/
private theorem packet_primLoop_norm (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) {n : ℕ}
    (a : Fin n → Fin L) (σ : Fin n → Bool) :
    ‖primLoop g W L E m t a σ‖ = (W : ℝ) ^ (1 - (n : ℝ)) * ‖primLoopF g L E m t a σ‖ := by
  have : primLoop g W L E m t a σ = (W : ℂ) ^ (1 - (n : ℤ)) * primLoopF g L E m t a σ := rfl
  rw [this, norm_mul, norm_zpow, Complex.norm_natCast]
  congr 1
  rw [← Real.rpow_intCast]
  push_cast
  rfl

/-- The bounds `|𝒦_n| ≤ C_n W^{1-n} e^{-c_n loopLen}` of (B.13) [b:eq:early-primitive] for the
family `pkK`, uniformly in `L ≥ 3` on the regular domain and `u ∈ [0, 1/2]`. -/
private theorem packet_K_bound (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') (n : ℕ) :
    ∃ CK cK : ℝ, 0 < CK ∧ 0 < cK ∧ ∀ W : ℕ, 1 ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g E : ℝ,
      RegBdd C B c' L g E → ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ (a : Fin n → Fin L)
        (σ : Fin n → Bool), ‖pkK g W L E (mRoot g L E) u n a σ‖ ≤
          CK * (W : ℝ) ^ (1 - (n : ℝ)) * Real.exp (-(cK * loopLen a)) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rcases Nat.lt_or_ge n 1 with hn1 | hn1
    · obtain rfl : n = 0 := by omega
      refine ⟨1, 1, one_pos, one_pos, fun W hW L hL g E hreg u hu a σ => ?_⟩
      simp only [pkK, ↓reduceIte, norm_zero]
      have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
      positivity
    · obtain rfl : n = 1 := by omega
      refine ⟨pkG C c', 1, pkG_pos hc', one_pos, fun W hW L hL g E hreg u hu a σ => ?_⟩
      have hl : loopLen a = 0 := by
        unfold loopLen; simp [packet_cycDist_self]
      have e : ‖pkK g W L E (mRoot g L E) u 1 a σ‖ = ‖mRoot g L E‖ := by
        simp only [pkK, one_ne_zero, ↓reduceIte, primLoop, primK, primF]
        split_ifs <;> simp
      rw [e, hl]
      simp only [Nat.cast_one, sub_self, Real.rpow_zero, mul_one, Nat.cast_zero, mul_zero,
        neg_zero, Real.exp_zero]
      exact packet_m_le hc' (by omega) hreg
  · obtain ⟨Ck, ck, L₀, hCk, hck, H⟩ := primLoop_early C B c' hC hB hc' n hn
    obtain ⟨Ck', hCk', H'⟩ := primLoopF_coarse (pkG C c') (pkG_pos hc') n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    refine ⟨Ck + Ck' * 2 ^ (2 * n - 3) * Real.exp (ck * L₀), ck / n, by positivity,
      by positivity, fun W hW L hL g E hreg u hu a σ => ?_⟩
    have hn0' : n ≠ 0 := by omega
    have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
    have hWn : 0 < (W : ℝ) ^ (1 - (n : ℝ)) := Real.rpow_pos_of_pos hW0 _
    have e : pkK g W L E (mRoot g L E) u n a σ = primLoop g W L E (mRoot g L E) u a σ := by
      simp [pkK, hn0']
    rw [e]
    have hdiam : ck / n * (loopLen a : ℝ) ≤ ck * wordDiam a := by
      have h1 : (loopLen a : ℝ) ≤ n * wordDiam a := by exact_mod_cast packet_loopLen_le_diam a
      rw [div_mul_eq_mul_div, div_le_iff₀ hn0]
      nlinarith
    have hE0 : 0 < Real.exp (-(ck / n * loopLen a)) := Real.exp_pos _
    by_cases hL₀ : L₀ ≤ L
    · have h := H g hreg.1 hreg.2.1 L hL hL₀ E hreg.2.2.1 (mRoot g L E) hreg.2.2.2.1
        hreg.2.2.2.2 W hW u hu.1 hu.2 a σ
      have hpos : 0 < Real.exp (ck * wordDiam a) := Real.exp_pos _
      have h2 : ‖primLoop g W L E (mRoot g L E) u a σ‖ ≤
          Ck * (W : ℝ) ^ (1 - (n : ℝ)) * Real.exp (-(ck * wordDiam a)) := by
        rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
        exact h
      refine h2.trans ?_
      have h3 : Real.exp (-(ck * wordDiam a)) ≤ Real.exp (-(ck / n * loopLen a)) :=
        Real.exp_le_exp.mpr (by linarith)
      have h4 : Ck ≤ Ck + Ck' * 2 ^ (2 * n - 3) * Real.exp (ck * L₀) := by
        have : 0 ≤ Ck' * 2 ^ (2 * n - 3) * Real.exp (ck * L₀) := by positivity
        linarith
      gcongr
    · have hMb : ∀ x y, ‖dysonMat (hopB g) (gammaG g) L E (mRoot g L E) x y‖ ≤ pkG C c' := by
        intro x y
        refine (packet_M_entry hc' hreg x y).trans ?_
        have := pkG_pos (C := C) hc'
        have : Real.exp (-(pkMu C c' * cycDist x y)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have := pkMu_pos (C := C) hc'
          have : (0 : ℝ) ≤ cycDist x y := Nat.cast_nonneg _
          nlinarith
        nlinarith
      have h := (H' g hreg.1 L hL E (mRoot g L E) hreg.2.2.2.1 hMb u hu.1 (by linarith [hu.2])).1
        a σ
      have h1u : (1 / 2 : ℝ) ≤ 1 - u := by linarith [hu.2]
      have hinv : ((1 - u) ^ (2 * n - 3))⁻¹ ≤ 2 ^ (2 * n - 3) := by
        rw [inv_le_comm₀ (by positivity) (by positivity), ← inv_pow]
        exact pow_le_pow_left₀ (by norm_num) (by linarith) _
      have hF : ‖primLoopF g L E (mRoot g L E) u a σ‖ ≤ Ck' * 2 ^ (2 * n - 3) :=
        h.trans (mul_le_mul_of_nonneg_left hinv hCk'.le)
      have hlen : ck / n * (loopLen a : ℝ) ≤ ck * L₀ := by
        have h1 : (wordDiam a : ℝ) ≤ L₀ := by
          have := packet_diam_le a
          exact_mod_cast (show wordDiam a ≤ L₀ by omega)
        nlinarith
      have hone : 1 ≤ Real.exp (ck * L₀) * Real.exp (-(ck / n * loopLen a)) := by
        rw [← Real.exp_add]; exact Real.one_le_exp_iff.mpr (by linarith)
      rw [packet_primLoop_norm]
      calc (W : ℝ) ^ (1 - (n : ℝ)) * ‖primLoopF g L E (mRoot g L E) u a σ‖ ≤
          (W : ℝ) ^ (1 - (n : ℝ)) * (Ck' * 2 ^ (2 * n - 3)) :=
            mul_le_mul_of_nonneg_left hF hWn.le
        _ ≤ (W : ℝ) ^ (1 - (n : ℝ)) * (Ck' * 2 ^ (2 * n - 3)) *
            (Real.exp (ck * L₀) * Real.exp (-(ck / n * loopLen a))) :=
            le_mul_of_one_le_right (by positivity) hone
        _ = Ck' * 2 ^ (2 * n - 3) * Real.exp (ck * L₀) * (W : ℝ) ^ (1 - (n : ℝ)) *
            Real.exp (-(ck / n * loopLen a)) := by ring
        _ ≤ (Ck + Ck' * 2 ^ (2 * n - 3) * Real.exp (ck * L₀)) * (W : ℝ) ^ (1 - (n : ℝ)) *
            Real.exp (-(ck / n * loopLen a)) := by
            gcongr
            linarith

/-- The loop-error component of (5.22) [gc:eq:one-step-input] on `initBdd` with the model
primitive loops, from `boundedInitial_loopError` and `packet_K_bound`. -/
private theorem packet_err (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') (k : ℕ)
    (hk : 1 ≤ k) :
    PrecMax FlowPt.L (initBdd C B c') (Λ := fun _ p => Word k p.L)
      (fun W p w ω => flowErr W p w.1 w.2 ω) (fun W p _ => flowZeta W p ^ k) := by
  choose CK cK hCK hcK hKb using packet_K_bound C B c' hC hB hc'
  intro ε D hε hD
  obtain ⟨W₀, hW₀⟩ := boundedInitial_loopError C B c' hC hB hc' k hk CK cK hCK hcK ε D hε hD
  refine ⟨max W₀ 1, fun W hW p hp => ?_⟩
  obtain ⟨hg, hreg, hL, hLW, hu0, hu1⟩ := hp
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hLW' : p.L ≤ W ^ 2 := by exact_mod_cast hLW
  have hroot := hreg.2.2.2.1
  have key := hW₀ W p.L ((le_max_left _ _).trans hW) hL hLW' p.g p.E hg hreg
    (pkK p.g W p.L p.E (mRoot p.g p.L p.E))
    (fun n a σ hn => by
      have hn0 : n ≠ 0 := by omega
      simp only [pkK, hn0, ↓reduceIte]
      exact primLoop_init p.g W p.L hW1 hL p.E _ hroot a σ)
    (fun u hu => pkK_deriv hW1 hL hroot u hu)
    (fun u x y s t => by
      simp only [pkK, OfNat.ofNat_ne_zero, ↓reduceIte]
      exact primLoop_two_swap p.g W p.L p.E _ u x y s t)
    (fun n _ u hu a σ => hKb n W hW1 p.L hL p.g p.E hreg u hu a σ) p.u ⟨hu0, hu1⟩
  refine (measure_mono ?_).trans key
  rintro ω ⟨w, hw⟩
  refine ⟨w.1, w.2, ?_⟩
  have e : pkK p.g W p.L p.E (mRoot p.g p.L p.E) p.u k w.1 w.2 =
      primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u w.1 w.2 := by
    have hk0 : k ≠ 0 := by omega
    simp only [pkK, hk0, ↓reduceIte]
  rw [e]
  exact hw

/-! ### Facts on the domain -/

private theorem pk_zeta_nonneg {C B c' : ℝ} {W : ℕ} {p : FlowPt} (hp : p ∈ initBdd C B c' W) :
    0 ≤ flowZeta W p := by
  obtain ⟨hg, -, -, -, -, hu1⟩ := hp
  unfold flowZeta zetaProp
  have hℓ : 0 ≤ ellProp p.g p.L p.u := by
    unfold ellProp
    refine le_min (Nat.cast_nonneg _) ?_
    have : 0 ≤ p.g / Real.sqrt (gammaG p.g * (1 - p.u)) := div_nonneg hg.le (Real.sqrt_nonneg _)
    linarith
  have h1 : 0 ≤ 1 - p.u := by linarith
  have := (pk_gamma_pos p.g).le
  positivity

private theorem pk_rpow_one_sub {W : ℕ} (hW : 1 ≤ W) {k : ℕ} (hk : 1 ≤ k) :
    (W : ℝ) ^ (1 - (k : ℝ)) = ((W : ℝ)⁻¹) ^ (k - 1) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, show (1 : ℝ) - ((j + 1 : ℕ) : ℝ) = -(j : ℝ) by push_cast; ring,
    Real.rpow_neg hW0.le, Real.rpow_natCast, inv_pow]

/-- `|ℒ_k| ≤ W^{1-k} g₀^k e^{-μ₀ loopLen}` on the domain. -/
private theorem packet_loop_bound {C B c' : ℝ} (hc' : 0 < c') {W : ℕ} (hW : 1 ≤ W) {p : FlowPt}
    (hp : p ∈ initBdd C B c' W) (ω : Ω W p.L) {k : ℕ} (hk : 1 ≤ k) (a : Fin k → Fin p.L)
    (σ : Fin k → Bool) :
    ‖loopTr (flowG W p ω) a σ‖ ≤
      (W : ℝ) ^ (1 - (k : ℝ)) * (pkG C c' ^ k * Real.exp (-(pkMu C c' * loopLen a))) :=
  packet_loop_le hW (flowG W p ω) (packet_leg hc' hp.2.1 hp.2.2.2.2.2 W ω) hk a σ

/-! ### Tails -/

/-- Superpolynomial decay: `C₁ W^{3C₁} e^{-c₁ W^ε} ≤ W^{-Q}` for large `W`. -/
private lemma packet_tail_analytic {C₁ c₁ ε Q : ℝ} (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hε : 0 < ε) :
    ∃ W₀ : ℕ, 1 ≤ W₀ ∧ ∀ W : ℕ, W₀ ≤ W →
      C₁ * (W : ℝ) ^ (3 * C₁) * Real.exp (-(c₁ * (W : ℝ) ^ ε)) ≤ (W : ℝ) ^ (-Q) := by
  set s : ℝ := (3 * C₁ + Q) / ε with hs
  have h1 := isLittleO_rpow_exp_pos_mul_atTop s hc₁
  have hy : Filter.Tendsto (fun x : ℝ => x ^ ε) Filter.atTop Filter.atTop := tendsto_rpow_atTop hε
  have h2 := h1.comp_tendsto hy
  have h3 := h2.def (by positivity : 0 < 1 / C₁)
  have h4 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x ∧ ‖((fun y : ℝ => y ^ s) ∘ fun x : ℝ => x ^ ε) x‖ ≤
      1 / C₁ * ‖(fun y : ℝ => Real.exp (c₁ * y)) (x ^ ε)‖ :=
    (Filter.eventually_ge_atTop 1).and h3
  have h5 := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually h4
  obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.mp h5
  refine ⟨max W₀ 1, le_max_right _ _, fun W hW => ?_⟩
  obtain ⟨hW1, hW2⟩ := hW₀ W (le_trans (le_max_left _ _) hW)
  have hW0 : (0 : ℝ) < W := by linarith
  simp only [Function.comp_apply, Real.norm_eq_abs] at hW2
  rw [abs_of_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hW0.le _) _),
    abs_of_nonneg (Real.exp_pos _).le] at hW2
  have e1 : ((W : ℝ) ^ ε) ^ s = (W : ℝ) ^ (3 * C₁ + Q) := by
    rw [← Real.rpow_mul hW0.le, hs]
    congr 1
    field_simp
  rw [e1, Real.rpow_add hW0] at hW2
  have hQ0 : 0 < (W : ℝ) ^ Q := Real.rpow_pos_of_pos hW0 _
  have hE : C₁ * ((W : ℝ) ^ (3 * C₁) * (W : ℝ) ^ Q) ≤ Real.exp (c₁ * (W : ℝ) ^ ε) := by
    have := mul_le_mul_of_nonneg_left hW2 hC₁.le
    rwa [← mul_assoc C₁ (1 / C₁), mul_one_div_cancel hC₁.ne', one_mul] at this
  rw [Real.rpow_neg hW0.le, Real.exp_neg, ← div_eq_mul_inv, ← one_div,
    div_le_div_iff₀ (Real.exp_pos _) hQ0]
  linarith [hE, mul_assoc C₁ ((W : ℝ) ^ (3 * C₁)) ((W : ℝ) ^ Q)]

/-- `W^ε → ∞`: `W^ε ≥ R` for large `W`. -/
private lemma packet_rpow_ge {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → R ≤ (W : ℝ) ^ ε := by
  have ht : Tendsto (fun W : ℕ => (W : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_ge_atTop R)

/-- `W^{-3} ≤ 1/2` for `W ≥ 2`. -/
private lemma packet_rpow_neg_three {W : ℕ} (hW : 2 ≤ W) : (W : ℝ) ^ (-3 : ℝ) ≤ 1 / 2 := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have h1 : (W : ℝ) ^ (-3 : ℝ) ≤ (W : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
  rw [Real.rpow_neg_one] at h1
  have h2 : (W : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hW)
  linarith

/-! ### Block averages -/

/-- `M_{B,u}(z_u) = M_B`: `z_u + uγ_g m = E + γ_g m`, (5.27) [gc:eq:positive-dyson] at the
characteristic. -/
private theorem packet_dysonMat_u (g E : ℝ) (L : ℕ) (m : ℂ) (u : ℝ) :
    dysonMat (hopB g) (u * gammaG g) L (zChar g E m u) m =
      dysonMat (hopB g) (gammaG g) L (E : ℂ) m := by
  unfold dysonMat zChar
  congr 3
  push_cast
  ring

/-- Entries of `M_B ⊗ I`: `|(M_B ⊗ I)_{e₁e₂}| ≤ g₀`. -/
private theorem packet_Mkron_entry {C B c' : ℝ} (hc' : 0 < c') {L W : ℕ} {g E : ℝ}
    (hreg : RegBdd C B c' L g E) (e₁ e₂ : Fin L × Fin W) :
    ‖(dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) e₁ e₂‖ ≤
      pkG C c' := by
  rw [Matrix.kroneckerMap_apply, norm_mul]
  have h1 : ‖(1 : Matrix (Fin W) (Fin W) ℂ) e₁.2 e₂.2‖ ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  have h2 := (packet_M_entry hc' hreg e₁.1 e₂.1).trans (by
    have := pkG_pos (C := C) hc'
    have : Real.exp (-(pkMu C c' * cycDist e₁.1 e₂.1)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := pkMu_pos (C := C) hc'
      have : (0 : ℝ) ≤ cycDist e₁.1 e₂.1 := Nat.cast_nonneg _
      nlinarith
    nlinarith : pkG C c' * Real.exp (-(pkMu C c' * cycDist e₁.1 e₂.1)) ≤ pkG C c')
  calc _ ≤ pkG C c' * 1 := mul_le_mul h2 h1 (norm_nonneg _) (pkG_pos hc').le
    _ = _ := mul_one _

/-- The entry moments `‖G̃_{e₁e₂}‖_{2n} ≤ C_m χ`, `χ = W^{ε/4} W^{-1/2}`, from the entrywise tail
bound `P(max |G̃| > W^{ε/4} √ζ) ≤ W^{-n}` and the crude bound `|G̃| ≤ 2g₀`. -/
private theorem packet_res_moment {C B c' : ℝ} (hc' : 0 < c') {W : ℕ} (hW1 : 1 ≤ W)
    {p : FlowPt} (hp : p ∈ initBdd C B c' W) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n)
    (hE : μ W p.L {ω | ∃ e₁ e₂ : Fin p.L × Fin W, (W : ℝ) ^ (ε / 4) *
        Real.sqrt (zetaProp p.g W p.L p.u) <
          ‖(resolventMat (flowH p.g W p.L p.u ω) (zChar p.g p.E (mRoot p.g p.L p.E) p.u) -
            dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ⊗ₖ
              (1 : Matrix (Fin W) (Fin W) ℂ)) e₁ e₂‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-(n : ℝ))))
    (e₁ e₂ : Fin p.L × Fin W) :
    (∫ ω, ‖(resolventMat (flowH p.g W p.L p.u ω) (zChar p.g p.E (mRoot p.g p.L p.E) p.u) -
        dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ⊗ₖ
          (1 : Matrix (Fin W) (Fin W) ℂ)) e₁ e₂‖ ^ (2 * n) ∂(μ W p.L)) ^ (1 / (2 * (n : ℝ))) ≤
      ((2 * (max 1 C) ^ 2) ^ n + (2 * pkG C c') ^ (2 * n)) ^ (1 / (2 * (n : ℝ))) *
        ((W : ℝ) ^ (ε / 4) * (W : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨hg, hreg, hL, hLW, hu0, hu1⟩ := hp
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hG := pkG_pos (C := C) hc'
  set G := fun ω => resolventMat (flowH p.g W p.L p.u ω) (zChar p.g p.E (mRoot p.g p.L p.E) p.u)
  set M := dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ⊗ₖ
    (1 : Matrix (Fin W) (Fin W) ℂ)
  set f : Ω W p.L → ℝ := fun ω => ‖(G ω - M) e₁ e₂‖ with hf
  set ζ := zetaProp p.g W p.L p.u with hζdef
  set y := (W : ℝ) ^ (ε / 4) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hW0 _
  have hζ0 : 0 ≤ ζ := pk_zeta_nonneg (W := W) ⟨hg, hreg, hL, hLW, hu0, hu1⟩
  have hζle : ζ ≤ 2 * (max 1 C) ^ 2 * (W : ℝ)⁻¹ :=
    pk_zeta_le hreg.1 hreg.2.1 hW1 (by omega) hu1
  have hK : ∀ ω, f ω ≤ 2 * pkG C c' := by
    intro ω
    simp only [hf, Matrix.sub_apply]
    refine (norm_sub_le _ _).trans ?_
    have := packet_G_entry hc' hreg hu1 W ω e₁ e₂
    have := packet_Mkron_entry (W := W) hc' hreg e₁ e₂
    linarith
  have hT : μ W p.L {ω | y * Real.sqrt ζ < f ω} ≤ ENNReal.ofReal ((W : ℝ) ^ (-(n : ℝ))) := by
    refine (measure_mono ?_).trans hE
    intro ω hω
    exact ⟨e₁, e₂, hω⟩
  have hmom := packet_moment_of_tail (P := μ W p.L) (f := f) (fun _ => norm_nonneg _)
    (by positivity) hK (by positivity) (2 * n) hT (Real.rpow_nonneg hW0.le _)
  -- `s^{2n} ≤ Cζ^n χ^{2n}` and `W^{-n} ≤ χ^{2n}`
  set χ := y * (W : ℝ) ^ (-(1 / 2 : ℝ)) with hχ
  have hy2 : y ^ 2 = (W : ℝ) ^ (ε / 2) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
  have hh2 : ((W : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (W : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_neg_one]; congr 1; push_cast; ring
  have hχ2 : χ ^ 2 = (W : ℝ) ^ (ε / 2) * (W : ℝ)⁻¹ := by
    rw [hχ, mul_pow, hy2, hh2]
  have hs : (y * Real.sqrt ζ) ^ (2 * n) ≤ (2 * (max 1 C) ^ 2) ^ n * χ ^ (2 * n) := by
    rw [pow_mul, pow_mul, mul_pow, Real.sq_sqrt hζ0, hχ2, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    rw [hy2]
    calc (W : ℝ) ^ (ε / 2) * ζ ≤ (W : ℝ) ^ (ε / 2) * (2 * (max 1 C) ^ 2 * (W : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hζle (by positivity)
      _ = _ := by ring
  have hWn : (W : ℝ) ^ (-(n : ℝ)) ≤ χ ^ (2 * n) := by
    rw [pow_mul, hχ2, Real.rpow_neg hW0.le, Real.rpow_natCast, ← inv_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    have : (1 : ℝ) ≤ (W : ℝ) ^ (ε / 2) :=
      Real.one_le_rpow (by exact_mod_cast hW1) (by positivity)
    have : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
    nlinarith
  set X := (2 * (max 1 C) ^ 2) ^ n + (2 * pkG C c') ^ (2 * n) with hX
  have hX0 : 0 ≤ X := by positivity
  have hint : ∫ ω, f ω ^ (2 * n) ∂(μ W p.L) ≤ X * χ ^ (2 * n) := by
    refine hmom.trans ?_
    have : 0 ≤ (2 * pkG C c') ^ (2 * n) := by positivity
    have := mul_le_mul_of_nonneg_left hWn this
    rw [hX]; nlinarith
  have hχ0 : 0 ≤ χ := by positivity
  have h2n : (1 / (2 * (n : ℝ))) = (((2 * n : ℕ) : ℝ))⁻¹ := by push_cast; ring
  have hfin : (X * χ ^ (2 * n)) ^ (1 / (2 * (n : ℝ))) = X ^ (1 / (2 * (n : ℝ))) * χ := by
    rw [Real.mul_rpow hX0 (by positivity), h2n, Real.pow_rpow_inv_natCast hχ0 (by omega)]
  calc (∫ ω, f ω ^ (2 * n) ∂(μ W p.L)) ^ (1 / (2 * (n : ℝ))) ≤
      (X * χ ^ (2 * n)) ^ (1 / (2 * (n : ℝ))) :=
        Real.rpow_le_rpow (integral_nonneg fun ω => by positivity) hint (by positivity)
    _ = _ := hfin

/-- The residual `R_{ab}` of (5.28) [gc:eq:residual-input] on the domain: `|R_{ab}| ≺ ζ_u`, by
the residual moments (5.31) [fo:eq:residual-moments] with the entrywise component of (5.22)
[gc:eq:one-step-input] and
Markov's inequality. -/
private theorem packet_res (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') :
    PrecMax FlowPt.L (initBdd C B c') (Λ := fun _ p => Fin p.L × Fin p.L)
      (fun W p ab ω => -flowRes W p ω ab.1 ab.2) (fun W p _ => flowZeta W p) := by
  refine PrecMax.of_card (Λ := fun _ p => Fin p.L × Fin p.L) 4 (fun W (p : FlowPt) hp => ?_) ?_
  · simp only [Fintype.card_prod, Fintype.card_fin]
    have hLW := hp.2.2.2.1
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast
    have : (0 : ℝ) ≤ p.L := Nat.cast_nonneg _
    calc (p.L : ℝ) * p.L ≤ (W : ℝ) ^ 2 * (W : ℝ) ^ 2 := mul_le_mul hLW hLW this (by positivity)
      _ = (W : ℝ) ^ 4 := by ring
  intro ε D hε hD
  set q : ℕ := ⌈(D + 1) / ε⌉₊ + 1 with hq
  set n : ℕ := 2 * q with hn
  have hn2 : 2 ≤ n := by omega
  have hne : Even n := ⟨q, by omega⟩
  have hqε : D + 1 ≤ q * ε := by
    have h1 := Nat.le_ceil ((D + 1) / ε)
    have h2 : (D + 1) / ε ≤ q := by rw [hq]; push_cast; linarith
    rwa [div_le_iff₀ hε] at h2
  have hG := pkG_pos (C := C) hc'
  have hS := pkS_pos (C := C) hc'
  set Cm : ℝ := ((2 * (max 1 C) ^ 2) ^ n + (2 * pkG C c') ^ (2 * n)) ^ (1 / (2 * (n : ℝ)))
    with hCm
  have hCm0 : 0 < Cm := by positivity
  set Γ : ℝ := pkG C c' + pkG C c' * pkS C c' + pkG C c' ^ 2 * pkS C c' with hΓ
  have hΓ0 : 0 < Γ := by positivity
  obtain ⟨Cp, hCp, HR⟩ := residual_moment_entries n hn2 hne Cm Γ hCm0 hΓ0
  obtain ⟨We, HE⟩ := boundedInitial_entry C B c' hC hB hc' (ε / 4) n (by positivity)
    (by positivity)
  have hcz := pkCz_pos hC.le
  refine ⟨max (max We ⌈Cp * (pkCz C ^ n)⁻¹⌉₊) 1, fun W hW p hp ab => ?_⟩
  have hWe : We ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hWc : Cp * (pkCz C ^ n)⁻¹ ≤ W := by
    have := Nat.le_ceil (Cp * (pkCz C ^ n)⁻¹)
    have : (⌈Cp * (pkCz C ^ n)⁻¹⌉₊ : ℝ) ≤ W := by
      exact_mod_cast (le_max_right _ _).trans ((le_max_left _ _).trans hW)
    linarith
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hp' := hp
  obtain ⟨hg, hreg, hL, hLW, hu0, hu1⟩ := hp'
  have hLW' : p.L ≤ W ^ 2 := by exact_mod_cast hLW
  set z := zChar p.g p.E (mRoot p.g p.L p.E) p.u with hz
  have hzim : 0 < z.im := lt_of_lt_of_le (pkEta_pos hc') (pkEta_le_im hc' hreg hu1)
  have hm0 : 0 ≤ (mRoot p.g p.L p.E).im := hreg.2.2.2.1.1.le
  have hmΓ : ‖mRoot p.g p.L p.E‖ ≤ Γ := by
    have := packet_m_le hc' (by omega) hreg
    have : 0 ≤ pkG C c' * pkS C c' + pkG C c' ^ 2 * pkS C c' := by positivity
    linarith
  have hMu := packet_dysonMat_u p.g p.E p.L (mRoot p.g p.L p.E) p.u
  have hMe : ∀ a c, ‖dysonMat (hopB p.g) (p.u * gammaG p.g) p.L z (mRoot p.g p.L p.E) a c‖ ≤ Γ := by
    intro a c
    rw [hz, hMu]
    have h1 := packet_M_entry hc' hreg a c
    have : Real.exp (-(pkMu C c' * cycDist a c)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := pkMu_pos (C := C) hc'
      have : (0 : ℝ) ≤ cycDist a c := Nat.cast_nonneg _
      nlinarith
    have : 0 ≤ pkG C c' * pkS C c' + pkG C c' ^ 2 * pkS C c' := by positivity
    nlinarith
  have hrow : ∀ a, p.u * gammaG p.g * ∑ c, (‖dysonMat (hopB p.g) (p.u * gammaG p.g) p.L z
      (mRoot p.g p.L p.E) a c‖ + ‖dysonMat (hopB p.g) (p.u * gammaG p.g) p.L z
        (mRoot p.g p.L p.E) a c‖ ^ 2) ≤ Γ := by
    intro a
    rw [hz, hMu, Finset.sum_add_distrib]
    have h1 := packet_M_row hc' hreg a
    have h2 := packet_M_row2 hc' hreg a
    have hγ1 := pk_gamma_le_one p.g
    have hγ0 := (pk_gamma_pos p.g).le
    have huγ : p.u * gammaG p.g ≤ 1 := by nlinarith
    have huγ0 : 0 ≤ p.u * gammaG p.g := mul_nonneg hu0 hγ0
    have hs0 : 0 ≤ ∑ c, ‖dysonMat (hopB p.g) (gammaG p.g) p.L (p.E : ℂ) (mRoot p.g p.L p.E) a c‖ +
        ∑ c, ‖dysonMat (hopB p.g) (gammaG p.g) p.L (p.E : ℂ) (mRoot p.g p.L p.E) a c‖ ^ 2 :=
      add_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => by positivity)
    calc p.u * gammaG p.g * (∑ c, ‖dysonMat (hopB p.g) (gammaG p.g) p.L (p.E : ℂ)
          (mRoot p.g p.L p.E) a c‖ + ∑ c, ‖dysonMat (hopB p.g) (gammaG p.g) p.L (p.E : ℂ)
            (mRoot p.g p.L p.E) a c‖ ^ 2) ≤ 1 * (pkG C c' * pkS C c' + pkG C c' ^ 2 * pkS C c') :=
          mul_le_mul huγ (add_le_add h1 h2) hs0 zero_le_one
      _ ≤ Γ := by rw [hΓ]; linarith
  set χ := (W : ℝ) ^ (ε / 4) * (W : ℝ) ^ (-(1 / 2 : ℝ)) with hχ
  have hχ1 : (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ χ := by
    have : (1 : ℝ) ≤ (W : ℝ) ^ (ε / 4) := Real.one_le_rpow (by exact_mod_cast hW1) (by positivity)
    have : 0 < (W : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hW0 _
    nlinarith
  have hE := HE W p.L hWe hL hLW' p.g p.E hg hreg p.u ⟨hu0, hu1⟩
  have hmom : ∀ e₁ e₂ : Fin p.L × Fin W, (∫ ω, ‖(resolventMat (flowH p.g W p.L p.u ω) z -
      dysonMat (hopB p.g) (p.u * gammaG p.g) p.L z (mRoot p.g p.L p.E) ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ)) e₁ e₂‖ ^ (2 * n) ∂(μ W p.L)) ^ (1 / (2 * (n : ℝ))) ≤
      Cm * χ := by
    intro e₁ e₂
    rw [hz, hMu]
    exact packet_res_moment hc' hW1 hp hε (by omega) hE e₁ e₂
  obtain ⟨hint, hbd⟩ := HR W p.L hW1 p.g p.u hu0 z (mRoot p.g p.L p.E) hzim hm0 hmΓ hMe hrow χ
    hχ1 hmom ab.1 ab.2
  rw [hz, hMu] at hint hbd
  -- Markov
  set t := (W : ℝ) ^ ε * flowZeta W p with ht
  have hζ : pkCz C * (W : ℝ)⁻¹ ≤ flowZeta W p :=
    pk_zeta_ge hreg.1 hreg.2.1 hW1 (by omega) hu0 hu1
  have ht0 : 0 < t := mul_pos (Real.rpow_pos_of_pos hW0 _) (lt_of_lt_of_le (by positivity) hζ)
  have hset : {ω : Ω W (FlowPt.L p) | (W : ℝ) ^ ε * flowZeta W p < ‖-flowRes W p ω ab.1 ab.2‖} =
      {ω | t < ‖flowRes W p ω ab.1 ab.2‖} := by
    ext ω; simp only [norm_neg, ht]
  rw [hset]
  refine (packet_markov (P := μ W p.L) (f := fun ω => ‖flowRes W p ω ab.1 ab.2‖)
    (fun _ => norm_nonneg _) (n := n) hint ht0).trans (ENNReal.ofReal_le_ofReal ?_)
  -- the final count
  have htn : (pkCz C * (W : ℝ)⁻¹ * (W : ℝ) ^ ε) ^ n ≤ t ^ n := by
    refine pow_le_pow_left₀ (by positivity) ?_ n
    rw [ht, mul_comm ((W : ℝ) ^ ε)]
    exact mul_le_mul_of_nonneg_right hζ (by positivity)
  set y := (W : ℝ) ^ (ε / 2) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hW0 _
  have hyε : y ^ 2 = (W : ℝ) ^ ε := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
  have hχ2 : χ ^ 2 = y * (W : ℝ)⁻¹ := by
    have h1 : ((W : ℝ) ^ (ε / 4)) ^ 2 = y := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
    have h2 : ((W : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (W : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_neg_one]; congr 1; push_cast
      ring
    rw [hχ, mul_pow, h1, h2]
  have hyn : (W : ℝ) ^ (D + 1) ≤ y ^ n := by
    rw [hn, pow_mul, hyε, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hW1) (by rw [mul_comm]; exact hqε)
  have hfrac : Cp * χ ^ (2 * n) / t ^ n ≤ Cp * (pkCz C ^ n)⁻¹ * (y ^ n)⁻¹ := by
    rw [div_le_iff₀ (pow_pos ht0 n)]
    calc Cp * χ ^ (2 * n) = Cp * (pkCz C ^ n)⁻¹ * (y ^ n)⁻¹ *
          (pkCz C * (W : ℝ)⁻¹ * (W : ℝ) ^ ε) ^ n := by
          rw [pow_mul, hχ2, ← hyε]
          field_simp
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htn (by positivity)
  have hfin : Cp * (pkCz C ^ n)⁻¹ * (y ^ n)⁻¹ ≤ (W : ℝ) ^ (-D) := by
    have h1 : (y ^ n)⁻¹ ≤ ((W : ℝ) ^ (D + 1))⁻¹ :=
      inv_anti₀ (Real.rpow_pos_of_pos hW0 _) hyn
    have h2 : (W : ℝ) * ((W : ℝ) ^ (D + 1))⁻¹ = (W : ℝ) ^ (-D) := by
      rw [← Real.rpow_neg hW0.le, ← Real.rpow_one_add' hW0.le (by
        intro h; linarith)]
      congr 1; ring
    calc Cp * (pkCz C ^ n)⁻¹ * (y ^ n)⁻¹ ≤ (W : ℝ) * ((W : ℝ) ^ (D + 1))⁻¹ :=
          mul_le_mul hWc h1 (by positivity) hW0.le
      _ = _ := h2
  calc (∫ ω, ‖flowRes W p ω ab.1 ab.2‖ ^ n ∂(μ W p.L)) / t ^ n ≤ Cp * χ ^ (2 * n) / t ^ n :=
        div_le_div_of_nonneg_right hbd (by positivity)
    _ ≤ _ := hfrac.trans hfin

/-- `⟨G̃_u⟩_{cc} = D_1(c, +)`, since `⟨M_B ⊗ I⟩_{cc} = m = 𝒦_1(c, +)`. -/
private theorem packet_avg_diag {C B c' : ℝ} {W : ℕ} (hW1 : 1 ≤ W) {p : FlowPt}
    (hp : p ∈ initBdd C B c' W) (ω : Ω W p.L) (c : Fin p.L) :
    blockTr (flowG W p ω - flowM W p) c c = flowErr W p ![c] ![true] ω := by
  have hroot := hp.2.1.2.2.2.1
  have h1 : blockTr (flowG W p ω - flowM W p) c c =
      loopTr (flowG W p ω) ![c] ![true] - loopTr (flowM W p) ![c] ![true] := by
    rw [loopTr_one, loopTr_one]
    unfold blockTr
    simp only [Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]
  have h2 : loopTr (flowM W p) ![c] ![true] = mRoot p.g p.L p.E := by
    have := loopTr_one_dysonMat p.g p.E W p.L hW1 (Fin.pos c) _ hroot c true
    simpa [flowM] using this
  have h3 : primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u ![c] ![true] = mRoot p.g p.L p.E := by
    simp [primLoop, primK, primF]
  rw [h1, h2, flowErr, h3]

/-- `|⟨G_u⟩_{cb}| ≤ g₀` on the domain. -/
private theorem packet_blockTr_G {C B c' : ℝ} (hc' : 0 < c') {W : ℕ} (hW1 : 1 ≤ W) {p : FlowPt}
    (hp : p ∈ initBdd C B c' W) (ω : Ω W p.L) (c b : Fin p.L) :
    ‖blockTr (flowG W p ω) c b‖ ≤ pkG C c' := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  unfold blockTr
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h : ‖∑ α : Fin W, flowG W p ω (c, α) (b, α)‖ ≤ W * pkG C c' := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ α : Fin W, ‖flowG W p ω (c, α) (b, α)‖ ≤ ∑ _α : Fin W, pkG C c' :=
          Finset.sum_le_sum fun α _ => packet_G_entry hc' hp.2.1 hp.2.2.2.2.2 W ω _ _
      _ = W * pkG C c' := by simp
  calc (W : ℝ)⁻¹ * ‖∑ α : Fin W, flowG W p ω (c, α) (b, α)‖ ≤ (W : ℝ)⁻¹ * (W * pkG C c') :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = pkG C c' := by field_simp

/-- The linear term `uγ_g Σ_c (M_B)_{ac} ⟨G̃_u⟩_{cc} ⟨G_u⟩_{cb}` of (5.32) [gc:eq:scalar]: it is
`≺ ζ_u` by the loop-error component at length one. -/
private theorem packet_lin (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') :
    PrecMax FlowPt.L (initBdd C B c') (Λ := fun _ p => Fin p.L × Fin p.L)
      (fun W p ab ω => ((p.u * gammaG p.g : ℝ) : ℂ) * ∑ c : Fin p.L,
        dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ab.1 c *
          blockTr (flowG W p ω - flowM W p) c c * blockTr (flowG W p ω) c ab.2)
      (fun W p _ => flowZeta W p) := by
  have hG := pkG_pos (C := C) hc'
  have hS := pkS_pos (C := C) hc'
  refine packet_pm_const (K := pkG C c' ^ 2 * pkS C c') ?_ (fun W p hp _ => pk_zeta_nonneg hp)
  refine packet_pm_relabel (packet_err C B c' hC hB hc' 1 le_rfl) ?_
  intro W hW1 p hp ω t ht hD ab
  have hζ0 := pk_zeta_nonneg hp
  have hd : ∀ c, ‖blockTr (flowG W p ω - flowM W p) c c‖ ≤ t * flowZeta W p := by
    intro c
    rw [packet_avg_diag hW1 hp ω c]
    have := hD (![c], ![true])
    simpa using this
  have hγ1 := pk_gamma_le_one p.g
  have hγ0 := (pk_gamma_pos p.g).le
  have hu0 := hp.2.2.2.2.1
  have hu1 := hp.2.2.2.2.2
  have huγ : p.u * gammaG p.g ≤ 1 := by nlinarith
  have huγ0 : 0 ≤ p.u * gammaG p.g := mul_nonneg hu0 hγ0
  have hrow := packet_M_row hc' hp.2.1 ab.1
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg huγ0]
  have hsum : ‖∑ c : Fin p.L, dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ab.1 c *
      blockTr (flowG W p ω - flowM W p) c c * blockTr (flowG W p ω) c ab.2‖ ≤
      (pkG C c' * pkS C c') * (t * flowZeta W p) * pkG C c' := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c : Fin p.L, ‖dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ab.1 c *
        blockTr (flowG W p ω - flowM W p) c c * blockTr (flowG W p ω) c ab.2‖ ≤
        ∑ c : Fin p.L, ‖dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ab.1 c‖ *
          (t * flowZeta W p) * pkG C c' := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hd c) (norm_nonneg _))
            (packet_blockTr_G hc' hW1 hp ω c ab.2) (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (by positivity))
      _ = (∑ c : Fin p.L, ‖dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ab.1 c‖) *
          (t * flowZeta W p) * pkG C c' := by rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ _ := by gcongr
  have h0 : 0 ≤ (pkG C c' * pkS C c') * (t * flowZeta W p) * pkG C c' := by positivity
  calc p.u * gammaG p.g * ‖∑ c : Fin p.L, dysonMat (hopB p.g) (gammaG p.g) p.L p.E
        (mRoot p.g p.L p.E) ab.1 c * blockTr (flowG W p ω - flowM W p) c c *
          blockTr (flowG W p ω) c ab.2‖ ≤ 1 * ((pkG C c' * pkS C c') * (t * flowZeta W p) *
            pkG C c') := mul_le_mul huγ hsum (norm_nonneg _) zero_le_one
    _ = t * (pkG C c' ^ 2 * pkS C c' * flowZeta W p) := by ring

/-- Lemma 5.3 [fo:lem:bounded-initial], component `max |ℒ_k|/ζ_u^{k-1} ≺ 1` of (5.22)
[gc:eq:one-step-input]. -/
theorem boundedInitial_loop (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') (k : ℕ)
    (hk : 1 ≤ k) :
    PrecMax FlowPt.L (initBdd C B c') (Λ := fun _ p => Word k p.L)
      (fun W p w ω => loopTr (flowG W p ω) w.1 w.2) (fun W p _ => flowZeta W p ^ (k - 1)) := by
  have _hC := hC
  have _hB := hB
  refine packet_pm_of_le (pkG C c' ^ k * (pkCz C ^ (k - 1))⁻¹)
    (fun W p hp _ => pow_nonneg (pk_zeta_nonneg hp) _) (fun W hW p hp l ω => ?_)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hreg := hp.2.1
  have hz := pk_zeta_ge hreg.1 hreg.2.1 hW (by have := hp.2.2.1; omega) hp.2.2.2.2.1
    hp.2.2.2.2.2 (W := W) (L := p.L)
  have hcz := pkCz_pos (hreg.1.trans hreg.2.1)
  have hG := pkG_pos (C := C) hc'
  have h := packet_loop_bound hc' hW hp ω hk l.1 l.2
  have he : Real.exp (-(pkMu C c' * loopLen l.1)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := pkMu_pos (C := C) hc'
    have : (0 : ℝ) ≤ loopLen l.1 := Nat.cast_nonneg _
    nlinarith
  rw [pk_rpow_one_sub hW hk] at h
  have hWi : 0 ≤ ((W : ℝ)⁻¹) ^ (k - 1) := by positivity
  calc ‖loopTr (flowG W p ω) l.1 l.2‖ ≤ ((W : ℝ)⁻¹) ^ (k - 1) * (pkG C c' ^ k * 1) :=
        h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by positivity)) hWi)
    _ = pkG C c' ^ k * (pkCz C ^ (k - 1))⁻¹ * (pkCz C * (W : ℝ)⁻¹) ^ (k - 1) := by
        rw [mul_pow]
        field_simp
    _ ≤ pkG C c' ^ k * (pkCz C ^ (k - 1))⁻¹ * flowZeta W p ^ (k - 1) := by
        gcongr
        exact hz

/-- Lemma 5.3 [fo:lem:bounded-initial], component `max |⟨G̃_u⟩_{ab}|/ζ_u ≺ 1` of (5.22)
[gc:eq:one-step-input]. -/
theorem boundedInitial_avg (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') :
    PrecMax FlowPt.L (initBdd C B c') (Λ := fun _ p => Fin p.L × Fin p.L)
      (fun W p ab ω => blockTr (flowG W p ω - flowM W p) ab.1 ab.2)
      (fun W p _ => flowZeta W p) := by
  have hsum := packet_pm_add (X := fun W p ab ω => blockTr (flowG W p ω - flowM W p) ab.1 ab.2)
    (packet_res C B c' hC hB hc') (packet_lin C B c' hC hB hc')
    (fun W p hp _ => pk_zeta_nonneg hp) (fun W p hp _ => pk_zeta_nonneg hp)
    (fun W hW p hp ab ω => by
      rw [scalar_identity W hW p hp.2.1.2.2.2.1.1 (by linarith [hp.2.2.2.2.2]) ω ab.1 ab.2]
      exact norm_add_le _ _)
  refine packet_pm_const (K := 2) ?_ (fun W p hp _ => pk_zeta_nonneg hp)
  exact PrecMax.mono hsum (fun W p _ l => le_of_eq (by ring))

/-- `e^{-c x²} ≤ e^{b²/(4c)} e^{-b x}` for `c > 0`. -/
private lemma packet_gauss_exp {c b x : ℝ} (hc : 0 < c) :
    Real.exp (-(c * x ^ 2)) ≤ Real.exp (b ^ 2 / (4 * c)) * Real.exp (-(b * x)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h : b ^ 2 / (4 * c) + -(b * x) - -(c * x ^ 2) = (2 * c * x - b) ^ 2 / (4 * c) := by
    field_simp; ring
  have : 0 ≤ (2 * c * x - b) ^ 2 / (4 * c) := by positivity
  linarith

/-- The pair error at distance `d`: `|D_2^{+-}(a,b)| ≤ (g₀² + C_k) W⁻¹ e^{-c d}` with
`c = min{μ₀, c_k}`, from the leg bounds and (B.13) [b:eq:early-primitive]. -/
private theorem packet_pair_far {C B c' : ℝ} (hc' : 0 < c') {Ck ck : ℝ} (hck : 0 < ck) {W : ℕ}
    (hW1 : 1 ≤ W) {p : FlowPt} (hp : p ∈ initBdd C B c' W) (ω : Ω W p.L) (a b : Fin p.L)
    (hK : Real.exp (ck * wordDiam ![a, b]) *
      ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u ![a, b] ![true, false]‖ ≤
        Ck * (W : ℝ) ^ (1 - ((2 : ℕ) : ℝ))) :
    ‖flowErr W p ![a, b] ![true, false] ω‖ ≤
      (pkG C c' ^ 2 + Ck) * (W : ℝ)⁻¹ * Real.exp (-(min (pkMu C c') ck * cycDist a b)) := by
  have hμ := pkMu_pos (C := C) hc'
  have hc : 0 < min (pkMu C c') ck := lt_min hμ hck
  have hd0 : (0 : ℝ) ≤ cycDist a b := Nat.cast_nonneg _
  have hl := packet_loop_bound hc' hW1 hp ω (k := 2) (by norm_num) ![a, b] ![true, false]
  rw [pk_rpow_one_sub hW1 (by norm_num : 1 ≤ 2), pow_one] at hl
  rw [pk_rpow_one_sub hW1 (by norm_num : 1 ≤ 2), pow_one] at hK
  have hlen : (cycDist a b : ℝ) ≤ loopLen ![a, b] := by
    have := packet_cycDist_le_loopLen ![a, b] 0 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    exact_mod_cast this
  have hdiam : (cycDist a b : ℝ) ≤ wordDiam ![a, b] := by
    have := packet_cycDist_le_diam ![a, b] 0 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    exact_mod_cast this
  set c := min (pkMu C c') ck with hcdef
  set E1 := Real.exp (-(c * cycDist a b)) with hE1
  have hWi : 0 ≤ (W : ℝ)⁻¹ := by positivity
  have hK' : ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u ![a, b] ![true, false]‖ ≤
      Ck * (W : ℝ)⁻¹ * E1 := by
    have hpos : 0 < Real.exp (ck * wordDiam ![a, b]) := Real.exp_pos _
    have h1 : ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u ![a, b] ![true, false]‖ ≤
        Ck * (W : ℝ)⁻¹ * Real.exp (-(ck * wordDiam ![a, b])) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
      exact hK
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ?_)
    · have : c * cycDist a b ≤ ck * wordDiam ![a, b] :=
        mul_le_mul (min_le_right _ _) hdiam hd0 hck.le
      linarith
    · have h0 : 0 ≤ ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u ![a, b] ![true, false]‖ :=
        norm_nonneg _
      have h2 : 0 ≤ Ck * (W : ℝ)⁻¹ * Real.exp (-(ck * wordDiam ![a, b])) := h0.trans h1
      by_contra hneg
      have : Ck * (W : ℝ)⁻¹ < 0 := lt_of_not_ge hneg
      have : Ck * (W : ℝ)⁻¹ * Real.exp (-(ck * wordDiam ![a, b])) < 0 :=
        mul_neg_of_neg_of_pos this (Real.exp_pos _)
      linarith
  have hL' : ‖loopTr (flowG W p ω) ![a, b] ![true, false]‖ ≤ pkG C c' ^ 2 * (W : ℝ)⁻¹ * E1 := by
    refine hl.trans ?_
    have h1 : c * cycDist a b ≤ pkMu C c' * loopLen ![a, b] :=
      mul_le_mul (min_le_left _ _) hlen hd0 hμ.le
    have h2 : Real.exp (-(pkMu C c' * loopLen ![a, b])) ≤ E1 := Real.exp_le_exp.mpr (by linarith)
    calc (W : ℝ)⁻¹ * (pkG C c' ^ 2 * Real.exp (-(pkMu C c' * loopLen ![a, b]))) ≤
        (W : ℝ)⁻¹ * (pkG C c' ^ 2 * E1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) hWi
      _ = _ := by ring
  have e : pkG C c' ^ 2 * (W : ℝ)⁻¹ * E1 + Ck * (W : ℝ)⁻¹ * E1 =
      (pkG C c' ^ 2 + Ck) * (W : ℝ)⁻¹ * E1 := by ring
  calc ‖flowErr W p ![a, b] ![true, false] ω‖ ≤ ‖loopTr (flowG W p ω) ![a, b] ![true, false]‖ +
      ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u ![a, b] ![true, false]‖ := norm_sub_le _ _
    _ ≤ _ := by rw [← e]; exact add_le_add hL' hK'

/-- `e^{-√d} < W^{-ε/2}` gives `e^{-c d} ≤ e^{b²/(4c)} W^{-F} W⁻¹` with `b = 2(F+1)/ε`. -/
private theorem packet_exp_far {c d ε F : ℝ} {W : ℕ} (hW1 : 1 ≤ W) (hc : 0 < c) (hd0 : 0 ≤ d)
    (hε : 0 < ε) (hF : 0 < F) (hx : Real.exp (-Real.sqrt d) < (W : ℝ) ^ (-(ε / 2))) :
    Real.exp (-(c * d)) ≤
      Real.exp ((2 * (F + 1) / ε) ^ 2 / (4 * c)) * ((W : ℝ) ^ (-F) * (W : ℝ)⁻¹) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  set b := 2 * (F + 1) / ε with hb
  have hb0 : 0 ≤ b := by positivity
  have h1 : Real.exp (-(c * d)) ≤ Real.exp (b ^ 2 / (4 * c)) * Real.exp (-(b * Real.sqrt d)) := by
    have := packet_gauss_exp (b := b) (x := Real.sqrt d) hc
    rwa [Real.sq_sqrt hd0] at this
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  have h2 : Real.exp (-(b * Real.sqrt d)) = Real.exp (-Real.sqrt d) ^ b := by
    rw [← Real.exp_mul]; ring_nf
  have h3 : Real.exp (-Real.sqrt d) ^ b ≤ ((W : ℝ) ^ (-(ε / 2))) ^ b :=
    Real.rpow_le_rpow (Real.exp_pos _).le hx.le hb0
  have h4 : ((W : ℝ) ^ (-(ε / 2))) ^ b = (W : ℝ) ^ (-F) * (W : ℝ)⁻¹ := by
    rw [← Real.rpow_mul hW0.le, ← Real.rpow_neg_one, ← Real.rpow_add hW0]
    congr 1
    rw [hb]; field_simp; ring
  rw [h2]; linarith

/-- Lemma 5.3 [fo:lem:bounded-initial], weighted mixed-pair component of (5.22)
[gc:eq:one-step-input] with `θ = 1/2`. -/
theorem boundedInitial_pair (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') :
    ∃ cp : ℝ, 0 < cp ∧ ∀ F : ℝ, 0 < F → PrecMax FlowPt.L (initBdd C B c')
      (Λ := fun _ p => Fin p.L × Fin p.L)
      (fun W p ab ω => flowErr W p ![ab.1, ab.2] ![true, false] ω)
      (fun W p ab => flowZeta W p ^ 2 *
        weightFn cp (1 / 2) F W (flowEll p) (cycDist ab.1 ab.2)) := by
  refine ⟨1, one_pos, fun F hF => ?_⟩
  have herr := packet_err C B c' hC hB hc' 2 (by norm_num)
  obtain ⟨Ck, ck, L₀, hCk, hck, H⟩ := primLoop_early C B c' hC hB hc' 2 le_rfl
  have hG := pkG_pos (C := C) hc'
  have hc : 0 < min (pkMu C c') ck := lt_min (pkMu_pos hc') hck
  have hcz := pkCz_pos hC.le
  intro ε D hε hD
  obtain ⟨W₁, hW₁⟩ := herr (ε / 2) D (by positivity) hD
  obtain ⟨W₂, hW₂⟩ := packet_rpow_ge (ε := ε / 2) (by positivity) (Real.exp (Real.sqrt L₀))
  obtain ⟨W₃, hW₃⟩ := packet_rpow_ge hε ((pkG C c' ^ 2 + Ck) *
    Real.exp ((2 * (F + 1) / ε) ^ 2 / (4 * min (pkMu C c') ck)) / pkCz C ^ 2)
  refine ⟨max (max W₁ W₂) (max W₃ 1), fun W hW p hp => (measure_mono ?_).trans
    (hW₁ W ((le_max_left _ _).trans ((le_max_left _ _).trans hW)) p hp)⟩
  have hW2' := hW₂ W ((le_max_right _ _).trans ((le_max_left _ _).trans hW))
  have hW3' := hW₃ W ((le_max_left _ _).trans ((le_max_right _ _).trans hW))
  have hW1 : 1 ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hp' := hp
  obtain ⟨hg, hreg, hL, hLW, hu0, hu1⟩ := hp'
  rintro ω ⟨ab, hab⟩
  refine ⟨(![ab.1, ab.2], ![true, false]), ?_⟩
  change (W : ℝ) ^ (ε / 2) * flowZeta W p ^ 2 < ‖flowErr W p ![ab.1, ab.2] ![true, false] ω‖
  have hd0 : (0 : ℝ) ≤ cycDist ab.1 ab.2 := Nat.cast_nonneg _
  have hℓ := (pk_ell_bounds hreg.1 hreg.2.1 (by omega : 1 ≤ p.L) hu1).1
  have hζ0 := pk_zeta_nonneg hp
  have hζ : pkCz C * (W : ℝ)⁻¹ ≤ flowZeta W p :=
    pk_zeta_ge hreg.1 hreg.2.1 hW1 (by omega) hu0 hu1
  have hWF : 0 < (W : ℝ) ^ (-F) := Real.rpow_pos_of_pos hW0 _
  have hWe : 0 < (W : ℝ) ^ ε := Real.rpow_pos_of_pos hW0 _
  simp only [weightFn] at hab
  set ex := Real.exp (-(1 * ((cycDist ab.1 ab.2 : ℝ) / flowEll p) ^ (1 / 2 : ℝ))) with hex
  have hex0 : 0 ≤ ex := (Real.exp_pos _).le
  by_cases hA : (W : ℝ) ^ (-(ε / 2)) ≤ ex
  · refine lt_of_le_of_lt ?_ hab
    have e : (W : ℝ) ^ (ε / 2) = (W : ℝ) ^ ε * (W : ℝ) ^ (-(ε / 2)) := by
      rw [← Real.rpow_add hW0]; congr 1; ring
    rw [e]
    have : (W : ℝ) ^ (-(ε / 2)) ≤ ex + (W : ℝ) ^ (-F) := by linarith
    calc (W : ℝ) ^ ε * (W : ℝ) ^ (-(ε / 2)) * flowZeta W p ^ 2 =
        (W : ℝ) ^ ε * (flowZeta W p ^ 2 * (W : ℝ) ^ (-(ε / 2))) := by ring
      _ ≤ (W : ℝ) ^ ε * (flowZeta W p ^ 2 * (ex + (W : ℝ) ^ (-F))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this (by positivity)) hWe.le
  · exfalso
    have hB' : ex < (W : ℝ) ^ (-(ε / 2)) := lt_of_not_ge hA
    have hsq : ((cycDist ab.1 ab.2 : ℝ) / flowEll p) ^ (1 / 2 : ℝ) ≤
        Real.sqrt (cycDist ab.1 ab.2) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt (div_le_self hd0 hℓ)
    have hx : Real.exp (-Real.sqrt (cycDist ab.1 ab.2)) < (W : ℝ) ^ (-(ε / 2)) :=
      lt_of_le_of_lt (Real.exp_le_exp.mpr (by linarith)) hB'
    by_cases hL₀ : L₀ ≤ p.L
    · have hD2 := packet_pair_far hc' hck hW1 hp ω ab.1 ab.2
        (H p.g hreg.1 hreg.2.1 p.L hL hL₀ p.E hreg.2.2.1 _ hreg.2.2.2.1 hreg.2.2.2.2 W
          hW1 p.u hu0 hu1 ![ab.1, ab.2] ![true, false])
      have hed := packet_exp_far hW1 hc hd0 hε hF hx
      set Eb := Real.exp ((2 * (F + 1) / ε) ^ 2 / (4 * min (pkMu C c') ck))
      set Kd := pkG C c' ^ 2 + Ck
      have hKd0 : 0 < Kd := by positivity
      have h1 : (pkCz C * (W : ℝ)⁻¹) ^ 2 ≤ flowZeta W p ^ 2 :=
        pow_le_pow_left₀ (by positivity) hζ 2
      have h2 : (W : ℝ) ^ (-F) ≤ ex + (W : ℝ) ^ (-F) := by linarith
      have h3 : Kd * Eb ≤ (W : ℝ) ^ ε * pkCz C ^ 2 := by
        rw [div_le_iff₀ (by positivity)] at hW3'
        linarith
      have hWi : 0 ≤ (W : ℝ)⁻¹ := by positivity
      have : ‖flowErr W p ![ab.1, ab.2] ![true, false] ω‖ ≤
          (W : ℝ) ^ ε * (flowZeta W p ^ 2 * (ex + (W : ℝ) ^ (-F))) :=
        calc ‖flowErr W p ![ab.1, ab.2] ![true, false] ω‖ ≤
            Kd * (W : ℝ)⁻¹ * Real.exp (-(min (pkMu C c') ck * cycDist ab.1 ab.2)) := hD2
          _ ≤ Kd * (W : ℝ)⁻¹ * (Eb * ((W : ℝ) ^ (-F) * (W : ℝ)⁻¹)) :=
            mul_le_mul_of_nonneg_left hed (by positivity)
          _ = (Kd * Eb) * ((W : ℝ)⁻¹ ^ 2 * (W : ℝ) ^ (-F)) := by ring
          _ ≤ ((W : ℝ) ^ ε * pkCz C ^ 2) * ((W : ℝ)⁻¹ ^ 2 * (W : ℝ) ^ (-F)) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = (W : ℝ) ^ ε * ((pkCz C * (W : ℝ)⁻¹) ^ 2 * (W : ℝ) ^ (-F)) := by ring
          _ ≤ (W : ℝ) ^ ε * (flowZeta W p ^ 2 * (ex + (W : ℝ) ^ (-F))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 hWF.le (by positivity)) hWe.le
      linarith
    · have hdL : (cycDist ab.1 ab.2 : ℝ) ≤ L₀ := by
        have := packet_cycDist_le ab.1 ab.2
        have : (cycDist ab.1 ab.2 : ℝ) ≤ p.L := by exact_mod_cast this
        have : (p.L : ℝ) ≤ L₀ := by exact_mod_cast (not_le.mp hL₀).le
        linarith
      have h1 : Real.exp (-Real.sqrt L₀) ≤ Real.exp (-Real.sqrt (cycDist ab.1 ab.2)) :=
        Real.exp_le_exp.mpr (by linarith [Real.sqrt_le_sqrt hdL])
      have h2 : (W : ℝ) ^ (-(ε / 2)) ≤ Real.exp (-Real.sqrt L₀) := by
        rw [Real.rpow_neg hW0.le, Real.exp_neg]
        exact inv_anti₀ (Real.exp_pos _) hW2'
      linarith

/-- Lemma 5.3 [fo:lem:bounded-initial], joint-tail component of (5.22) [gc:eq:one-step-input]. -/
theorem boundedInitial_tail (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') (k : ℕ)
    (hk : 2 ≤ k) (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    PrecMax FlowPt.L (initBdd C B c')
      (Λ := fun W p => {w : Word k p.L // (W : ℝ) ^ ε * flowEll p < wordDiam w.1})
      (fun W p w ω => ((‖loopTr (flowG W p ω) w.1.1 w.1.2‖ + ‖flowErr W p w.1.1 w.1.2 ω‖ : ℝ) : ℂ))
      (fun W _ _ => (W : ℝ) ^ (-A)) := by
  obtain ⟨Wt, Lt, Ht⟩ := primLoop_bdd_tail C B c' ε (A + 1) hC hB hc' hε (by linarith) k hk
  have hG := pkG_pos (C := C) hc'
  have hμ := pkMu_pos (C := C) hc'
  obtain ⟨Wa, -, Ha⟩ := packet_tail_analytic (C₁ := 4 * pkG C c' ^ k) (Q := A) (by positivity) hμ
    hε
  obtain ⟨Wl, Hl⟩ := packet_rpow_ge hε (Lt : ℝ)
  refine packet_pm_eventually (fun W _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    ⟨max (max Wt Wa) (max Wl 2), fun W hW p hp l ω => ?_⟩
  have hWt : Wt ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hWa : Wa ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hWl : Wl ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW2 : 2 ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  obtain ⟨hg, hreg, hL, hLW, hu0, hu1⟩ := hp
  obtain ⟨⟨a, σ⟩, hdiam⟩ := l
  simp only at hdiam ⊢
  have hℓ := (pk_ell_bounds hreg.1 hreg.2.1 (by omega : 1 ≤ p.L) hu1).1
  have hWe1 : (1 : ℝ) ≤ (W : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast hW1) hε.le
  have hdW : (W : ℝ) ^ ε < wordDiam a := by
    have : (W : ℝ) ^ ε ≤ (W : ℝ) ^ ε * flowEll p := le_mul_of_one_le_right (by linarith) hℓ
    linarith
  -- the label set is empty for `L < L_t`
  have hLt : Lt ≤ p.L := by
    by_contra hcon
    have h1 : (wordDiam a : ℝ) ≤ p.L := by exact_mod_cast packet_diam_le a
    have h2 : (p.L : ℝ) < Lt := by exact_mod_cast (not_le.mp hcon)
    linarith [Hl W hWl]
  -- the primitive loop
  have hK : ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u a σ‖ ≤ (W : ℝ) ^ (-(A + 1)) :=
    Ht W hWt p.g hreg.1 hreg.2.1 p.L hL hLt p.E hreg.2.2.1 _ hreg.2.2.2.1 hreg.2.2.2.2 p.u hu0
      ((packet_rpow_neg_three hW2).trans (by linarith)) a σ hdiam
  -- the loop
  have hl := packet_loop_bound hc' hW1 ⟨hg, hreg, hL, hLW, hu0, hu1⟩ ω (by omega : 1 ≤ k) a σ
  have hWk : (W : ℝ) ^ (1 - (k : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hW1)
      (by have : (2 : ℝ) ≤ k := by exact_mod_cast hk
          linarith)
  have hlen : (W : ℝ) ^ ε ≤ loopLen a := by
    have : (wordDiam a : ℝ) ≤ loopLen a := by exact_mod_cast packet_diam_le_loopLen a
    linarith
  have hexp : Real.exp (-(pkMu C c' * loopLen a)) ≤ Real.exp (-(pkMu C c' * (W : ℝ) ^ ε)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hL' : ‖loopTr (flowG W p ω) a σ‖ ≤ pkG C c' ^ k * Real.exp (-(pkMu C c' * (W : ℝ) ^ ε)) := by
    refine hl.trans ?_
    calc (W : ℝ) ^ (1 - (k : ℝ)) * (pkG C c' ^ k * Real.exp (-(pkMu C c' * loopLen a))) ≤
        1 * (pkG C c' ^ k * Real.exp (-(pkMu C c' * (W : ℝ) ^ ε))) := by
          gcongr
      _ = _ := one_mul _
  have hsup := Ha W hWa
  have h3 : 1 ≤ (W : ℝ) ^ (3 * (4 * pkG C c' ^ k)) :=
    Real.one_le_rpow (by exact_mod_cast hW1) (by positivity)
  have hsup' : 4 * pkG C c' ^ k * Real.exp (-(pkMu C c' * (W : ℝ) ^ ε)) ≤ (W : ℝ) ^ (-A) := by
    refine le_trans ?_ hsup
    have : 0 ≤ 4 * pkG C c' ^ k * Real.exp (-(pkMu C c' * (W : ℝ) ^ ε)) := by positivity
    calc 4 * pkG C c' ^ k * Real.exp (-(pkMu C c' * (W : ℝ) ^ ε)) =
        4 * pkG C c' ^ k * 1 * Real.exp (-(pkMu C c' * (W : ℝ) ^ ε)) := by ring
      _ ≤ _ := by gcongr
  have hA1 : (W : ℝ) ^ (-(A + 1)) ≤ (W : ℝ) ^ (-A) / 2 := by
    rw [show -(A + 1) = -A + (-1) by ring, Real.rpow_add hW0, Real.rpow_neg_one]
    have h2 : (W : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hW2)
    have := Real.rpow_pos_of_pos hW0 (-A)
    nlinarith
  have herr : ‖flowErr W p a σ ω‖ ≤ ‖loopTr (flowG W p ω) a σ‖ +
      ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u a σ‖ := norm_sub_le _ _
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  linarith

/-- The entrywise component of (5.22) [gc:eq:one-step-input] on `initBdd`, from
`boundedInitial_entry`. -/
private theorem packet_entry (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') :
    PrecMax FlowPt.L (initBdd C B c')
      (Λ := fun W p => (Fin p.L × Fin W) × (Fin p.L × Fin W))
      (fun W p e ω => (flowG W p ω - flowM W p) e.1 e.2)
      (fun W p _ => Real.sqrt (flowZeta W p)) := by
  intro ε D hε hD
  obtain ⟨W₀, H⟩ := boundedInitial_entry C B c' hC hB hc' ε D hε hD
  refine ⟨W₀, fun W hW p hp => ?_⟩
  obtain ⟨hg, hreg, hL, hLW, hu0, hu1⟩ := hp
  have hLW' : p.L ≤ W ^ 2 := by exact_mod_cast hLW
  refine (measure_mono ?_).trans (H W p.L hW hL hLW' p.g p.E hg hreg p.u ⟨hu0, hu1⟩)
  rintro ω ⟨e, he⟩
  exact ⟨e.1, e.2, he⟩

/-- Lemma 5.3 [fo:lem:bounded-initial], (5.23) [gc:eq:iteration-input] in fixed-time form with the
primitive loops of (5.10) [fo:eq:primitive]: every component of (5.22) [gc:eq:one-step-input] at
each `u ∈ [0, 1/2]`. -/
theorem boundedInitial_packet (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') :
    ∃ cp : ℝ, 0 < cp ∧ OneStepInput cp (1 / 2) id (initBdd C B c') := by
  obtain ⟨cp, hcp, hpair⟩ := boundedInitial_pair C B c' hC hB hc'
  exact ⟨cp, hcp, ⟨fun k hk => boundedInitial_loop C B c' hC hB hc' k hk,
    fun k hk => packet_err C B c' hC hB hc' k hk, boundedInitial_avg C B c' hC hB hc',
    packet_entry C B c' hC hB hc', hpair,
    fun k hk ε A hε hA => boundedInitial_tail C B c' hC hB hc' k hk ε A hε hA⟩⟩

end LSBA
