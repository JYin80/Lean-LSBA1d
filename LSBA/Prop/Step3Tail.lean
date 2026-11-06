import LSBA.Prop.Step2
import LSBA.Primitive.Early
import LSBA.Primitive.Large

/-!
# Step 3 of the one-step propagation: tails

The tail estimates of Step 3 of Appendix C.3 [sec:gc-one-step] at each deterministic time, from the
primitive tails (5.22)(a)(b) [gc:eq:one-step-input] and the outputs of Step 2.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The squared Hilbert–Schmidt norm of a matrix. -/
private def step3Tail_hsq {ι : Type*} [Fintype ι] (T : Matrix ι ι ℂ) : ℝ :=
  ∑ p, ∑ q, ‖T p q‖ ^ 2

private lemma step3Tail_hsq_nonneg {ι : Type*} [Fintype ι] (T : Matrix ι ι ℂ) :
    0 ≤ step3Tail_hsq T :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Submultiplicativity of the squared Hilbert–Schmidt norm. -/
private lemma step3Tail_hsq_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) :
    step3Tail_hsq (A * B) ≤ step3Tail_hsq A * step3Tail_hsq B := by
  have h1 : ∀ p q, ‖(A * B) p q‖ ^ 2 ≤ (∑ r, ‖A p r‖ ^ 2) * ∑ r, ‖B r q‖ ^ 2 := by
    intro p q
    calc ‖(A * B) p q‖ ^ 2 ≤ (∑ r, ‖A p r‖ * ‖B r q‖) ^ 2 := by
          rw [Matrix.mul_apply]
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => (norm_mul _ _).le)
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc step3Tail_hsq (A * B) ≤ ∑ p, ∑ q, (∑ r, ‖A p r‖ ^ 2) * ∑ r, ‖B r q‖ ^ 2 :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => h1 p q
    _ = (∑ p, ∑ r, ‖A p r‖ ^ 2) * ∑ q, ∑ r, ‖B r q‖ ^ 2 := (Finset.sum_mul_sum _ _ _ _).symm
    _ = step3Tail_hsq A * step3Tail_hsq B := by
        rw [step3Tail_hsq, step3Tail_hsq, Finset.sum_comm (f := fun q r => ‖B r q‖ ^ 2)]

/-- Cauchy–Schwarz for the trace of a product. -/
private lemma step3Tail_trace_sq {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) :
    ‖(A * B).trace‖ ^ 2 ≤ step3Tail_hsq A * step3Tail_hsq B := by
  have h : ‖(A * B).trace‖ ≤ ∑ x : ι × ι, ‖A x.1 x.2‖ * ‖B x.2 x.1‖ := by
    rw [Matrix.trace, Fintype.sum_prod_type]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    simp only [Matrix.diag_apply, Matrix.mul_apply]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => (norm_mul _ _).le)
  calc ‖(A * B).trace‖ ^ 2 ≤ (∑ x : ι × ι, ‖A x.1 x.2‖ * ‖B x.2 x.1‖) ^ 2 := by gcongr
    _ ≤ (∑ x : ι × ι, ‖A x.1 x.2‖ ^ 2) * ∑ x : ι × ι, ‖B x.2 x.1‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = step3Tail_hsq A * step3Tail_hsq B := by
        rw [step3Tail_hsq, step3Tail_hsq, Fintype.sum_prod_type, Fintype.sum_prod_type]
        congr 1
        exact Finset.sum_comm (f := fun p q => ‖B q p‖ ^ 2)


/-- The squared Hilbert–Schmidt norm of a product of `m + 1` matrices. -/
private lemma step3Tail_hsq_prod {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (m : ℕ) (T : Fin (m + 1) → Matrix ι ι ℂ),
      step3Tail_hsq (List.ofFn T).prod ≤ ∏ i, step3Tail_hsq (T i)
  | 0, T => by simp [List.ofFn_succ]
  | m + 1, T => by
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    refine (step3Tail_hsq_mul _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (step3Tail_hsq_prod m (fun i => T i.succ))
      (step3Tail_hsq_nonneg _)

/-- The trace of a product of at least two matrices, squared, is at most the product of the
squared Hilbert–Schmidt norms. -/
private lemma step3Tail_trace_prod_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (T : Fin (m + 2) → Matrix ι ι ℂ) :
    ‖(List.ofFn T).prod.trace‖ ^ 2 ≤ ∏ i, step3Tail_hsq (T i) := by
  rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
  refine (step3Tail_trace_sq _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (step3Tail_hsq_prod m (fun i => T i.succ))
    (step3Tail_hsq_nonneg _)

/-- The projection onto the block `a`. -/
private def step3Tail_P (W L : ℕ) (a : Fin L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.diagonal fun p => if p.1 = a then 1 else 0

private lemma step3Tail_P_idem (W L : ℕ) (a : Fin L) :
    step3Tail_P W L a * step3Tail_P W L a = step3Tail_P W L a := by
  unfold step3Tail_P
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> simp

private lemma step3Tail_blockE (W L : ℕ) (a : Fin L) :
    blockE W L a = (W : ℂ)⁻¹ • step3Tail_P W L a := by
  unfold blockE step3Tail_P
  ext p q
  by_cases hpq : p = q
  · subst hpq
    by_cases h : p.1 = a <;> simp [h]
  · simp [hpq]

/-- The squared Hilbert–Schmidt norm of `P_x S P_y` is the block norm `‖S_{xy}‖²_HS`. -/
private lemma step3Tail_hsq_PSP (W L : ℕ) (S : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x y : Fin L) :
    step3Tail_hsq (step3Tail_P W L x * S * step3Tail_P W L y) = blockHS2 S x y := by
  unfold step3Tail_hsq blockHS2 step3Tail_P
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_eq_single y]
    · refine Finset.sum_congr rfl fun β _ => ?_
      simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun β _ => ?_
      simp [hj]
    · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun j _ =>
      Finset.sum_eq_zero fun β _ => ?_
    simp [hi]
  · simp

/-- The block norm of the adjoint swaps the blocks. -/
private lemma step3Tail_blockHS2_conjTranspose (W L : ℕ)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (x y : Fin L) :
    blockHS2 Xᴴ x y = blockHS2 X y x := by
  unfold blockHS2
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

/-- Inserting idempotents between the factors of a product. -/
private lemma step3Tail_chain {M ι : Type*} [Monoid M] (P : ι → M) (hP : ∀ x, P x * P x = P x) :
    ∀ (n : ℕ) (S : Fin (n + 1) → M) (b : Fin (n + 2) → ι),
      P (b 0) * (List.ofFn fun i : Fin (n + 1) => S i * P (b i.succ)).prod =
        (List.ofFn fun i : Fin (n + 1) => P (b i.castSucc) * S i * P (b i.succ)).prod
  | 0, S, b => by simp [List.ofFn_succ, mul_assoc]
  | n + 1, S, b => by
    have ih := step3Tail_chain P hP n (fun i => S i.succ) (fun i => b i.succ)
    rw [List.ofFn_succ,
      List.ofFn_succ (f := fun i : Fin (n + 2) => P (b i.castSucc) * S i * P (b i.succ)),
      List.prod_cons, List.prod_cons]
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.succ_castSucc] at ih ⊢
    rw [← ih]
    calc P (b 0) * (S 0 * P (b 1) *
          (List.ofFn fun i : Fin (n + 1) => S i.succ * P (b i.succ.succ)).prod)
        = P (b 0) * S 0 * (P (b 1) * P (b 1)) *
            (List.ofFn fun i : Fin (n + 1) => S i.succ * P (b i.succ.succ)).prod := by
          rw [hP]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]

/-- A scalar on every second factor of a product. -/
private lemma step3Tail_prod_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℂ) :
    ∀ (n : ℕ) (S P : Fin n → Matrix ι ι ℂ),
      (List.ofFn fun i => S i * (r • P i)).prod = r ^ n • (List.ofFn fun i => S i * P i).prod
  | 0, S, P => by simp
  | n + 1, S, P => by
    rw [List.ofFn_succ, List.ofFn_succ (f := fun i => S i * P i), List.prod_cons, List.prod_cons,
      step3Tail_prod_smul r n (fun i => S i.succ) (fun i => P i.succ)]
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
    rw [pow_succ]

/-- A loop of `n + 1` factors is `W^{-(n+1)}` times the trace of a product of blocks
`P_{a_{i-1}} S_i P_{a_i}`, cyclically. -/
private lemma step3Tail_loopTr_eq {W L n : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin (n + 1) → Fin L) (σ : Fin (n + 1) → Bool) :
    loopTr X a σ = (W : ℂ)⁻¹ ^ (n + 1) *
      (List.ofFn fun i : Fin (n + 1) =>
        step3Tail_P W L ((Fin.cons (a (Fin.last n)) a : Fin (n + 2) → Fin L) i.castSucc) *
          sgnMat X (σ i) * step3Tail_P W L (a i)).prod.trace := by
  unfold loopTr
  simp only [step3Tail_blockE]
  rw [step3Tail_prod_smul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  have hch := step3Tail_chain (step3Tail_P W L) (step3Tail_P_idem W L) n
    (fun i => sgnMat X (σ i)) (Fin.cons (a (Fin.last n)) a)
  simp only [Fin.cons_zero, Fin.cons_succ] at hch
  rw [← hch]
  set Mx := (List.ofFn fun i : Fin (n + 1) => sgnMat X (σ i) * step3Tail_P W L (a i)).prod
    with hMx
  have hlast : Mx * step3Tail_P W L (a (Fin.last n)) = Mx := by
    rw [hMx, List.ofFn_succ', List.prod_concat]
    simp only [mul_assoc, step3Tail_P_idem]
  calc Mx.trace = (Mx * step3Tail_P W L (a (Fin.last n))).trace := by rw [hlast]
    _ = (step3Tail_P W L (a (Fin.last n)) * Mx).trace := Matrix.trace_mul_comm _ _

private lemma step3Tail_hsq_sgn (W L : ℕ) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (s : Bool)
    (x y : Fin L) :
    step3Tail_hsq (step3Tail_P W L x * sgnMat X s * step3Tail_P W L y) =
      if s then blockHS2 X x y else blockHS2 X y x := by
  rw [step3Tail_hsq_PSP]
  cases s
  · simp [sgnMat, step3Tail_blockHS2_conjTranspose]
  · simp [sgnMat]

/-- The loop of a word with at least two letters is at most `δ` when every block has
Hilbert–Schmidt norm at most `W` and one pair of consecutive letters has both blocks of
Hilbert–Schmidt norm at most `Wδ`. -/
private lemma step3Tail_loop_le {W L n : ℕ} (hn : 1 ≤ n) (hW : 1 ≤ W)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a : Fin (n + 1) → Fin L)
    (σ : Fin (n + 1) → Bool) (δ : ℝ) (hδ : 0 ≤ δ)
    (hall : ∀ x y, blockHS2 X x y ≤ (W : ℝ) ^ 2)
    (hlong : ∃ l l' : Fin (n + 1), l.val + 1 = l'.val ∧
      blockHS2 X (a l) (a l') ≤ (W : ℝ) ^ 2 * δ ^ 2 ∧
      blockHS2 X (a l') (a l) ≤ (W : ℝ) ^ 2 * δ ^ 2) :
    ‖loopTr X a σ‖ ≤ δ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨l, l', hll', h1, h2⟩ := hlong
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set b : Fin (m + 1 + 2) → Fin L := Fin.cons (a (Fin.last (m + 1))) a with hb
  set T : Fin (m + 1 + 1) → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := fun i =>
    step3Tail_P W L (b i.castSucc) * sgnMat X (σ i) * step3Tail_P W L (a i) with hT
  have hloop : loopTr X a σ = (W : ℂ)⁻¹ ^ (m + 1 + 1) * (List.ofFn T).prod.trace :=
    step3Tail_loopTr_eq X a σ
  set f : Fin (m + 1 + 1) → ℝ := fun i => ((W : ℝ) ^ 2)⁻¹ * step3Tail_hsq (T i) with hf
  have hfnn : ∀ i, 0 ≤ f i := fun i =>
    mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (step3Tail_hsq_nonneg _)
  have hf1 : ∀ i, f i ≤ 1 := by
    intro i
    have : step3Tail_hsq (T i) ≤ (W : ℝ) ^ 2 := by
      rw [hT]
      simp only
      rw [step3Tail_hsq_sgn]
      split_ifs <;> exact hall _ _
    rw [hf]
    simp only
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    exact this
  have hfl : f l' ≤ δ ^ 2 := by
    have hcs : b l'.castSucc = a l := by
      have : l'.castSucc = l.succ := Fin.ext (by simp [← hll'])
      rw [this, hb, Fin.cons_succ]
    have : step3Tail_hsq (T l') ≤ (W : ℝ) ^ 2 * δ ^ 2 := by
      rw [hT]
      simp only
      rw [step3Tail_hsq_sgn, hcs]
      split_ifs
      · exact h1
      · exact h2
    rw [hf]
    simp only
    rw [inv_mul_le_iff₀ (by positivity)]
    exact this
  have hprod : ∏ i, f i ≤ δ ^ 2 := by
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ l')]
    calc f l' * ∏ i ∈ Finset.univ.erase l', f i ≤ f l' * 1 :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_one₀ (fun i _ => hfnn i) fun i _ => hf1 i)
            (hfnn l')
      _ ≤ δ ^ 2 := by rw [mul_one]; exact hfl
  have hsq : ‖loopTr X a σ‖ ^ 2 ≤ ∏ i, f i := by
    have h3 := step3Tail_trace_prod_sq m T
    rw [hloop, norm_mul, norm_pow, mul_pow, ← pow_mul]
    have hnorm : ‖(W : ℂ)⁻¹‖ ^ 2 = ((W : ℝ) ^ 2)⁻¹ := by
      rw [norm_inv, Complex.norm_natCast, inv_pow]
    rw [mul_comm (m + 1 + 1) 2, pow_mul, hnorm, hf]
    simp only
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have : ‖loopTr X a σ‖ ^ 2 ≤ δ ^ 2 := hsq.trans hprod
  exact (sq_le_sq₀ (norm_nonneg _) hδ).mp this

/-- A word whose diameter exceeds `k m` has a pair of consecutive letters at cyclic distance
more than `m`. -/
private lemma step3Tail_long_edge {L k : ℕ} [NeZero L] (hk : 2 ≤ k) (a : Fin k → Fin L) (m : ℝ)
    (hm : 0 ≤ m) (hd : (k : ℝ) * m < wordDiam a) :
    ∃ l l' : Fin k, l.val + 1 = l'.val ∧ m < (cycDist (a l) (a l') : ℝ) := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hclaim : ∀ d : ℕ, ∀ i j : Fin k, j.val = i.val + d →
      (cycDist (a i) (a j) : ℝ) ≤ d * m := by
    intro d
    induction d with
    | zero =>
      intro i j hij
      have : j = i := Fin.ext (by simpa using hij)
      subst this
      simp [mol_cycDist_self]
    | succ d ih =>
      intro i j hij
      have hj : 0 < j.val := by omega
      have h1 := ih i ⟨j.val - 1, by omega⟩ (by simp; omega)
      have h2 := hcon ⟨j.val - 1, by omega⟩ j (by simp; omega)
      have h3 : (cycDist (a i) (a j) : ℝ) ≤
          cycDist (a i) (a ⟨j.val - 1, by omega⟩) + cycDist (a ⟨j.val - 1, by omega⟩) (a j) := by
        exact_mod_cast bd_cycDist_tri (a i) (a ⟨j.val - 1, by omega⟩) (a j)
      push_cast
      nlinarith
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin k × Fin k))
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), Finset.mem_univ _⟩
    (fun p : Fin k × Fin k => cycDist (a p.1) (a p.2))
  unfold wordDiam at hd
  rw [hp] at hd
  rcases le_total p.1 p.2 with h | h
  · have h1 := hclaim (p.2.val - p.1.val) p.1 p.2 (by have := Fin.le_def.mp h; omega)
    have h2 : ((p.2.val - p.1.val : ℕ) : ℝ) ≤ k := by
      exact_mod_cast (by have := p.2.isLt; omega : p.2.val - p.1.val ≤ k)
    nlinarith
  · have h1 := hclaim (p.1.val - p.2.val) p.2 p.1 (by have := Fin.le_def.mp h; omega)
    have h2 : ((p.1.val - p.2.val : ℕ) : ℝ) ≤ k := by
      exact_mod_cast (by have := p.1.isLt; omega : p.1.val - p.2.val ≤ k)
    rw [mol_cycDist_comm] at h1
    nlinarith

/-- A stretched exponential is eventually below any fixed negative power of `W`. -/
private lemma step3Tail_exp_le (cp b F : ℝ) (hcp : 0 < cp) (hb : 0 < b) (hF : 0 < F) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → Real.exp (-(cp * (W : ℝ) ^ b)) ≤ (W : ℝ) ^ (-F) := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (F / b) cp hcp
  have hc : Tendsto (fun W : ℕ => (W : ℝ) ^ b) atTop atTop :=
    (tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp ((ht.comp hc).eventually (ge_mem_nhds one_pos))
  refine ⟨max W₀ 1, fun W hW => ?_⟩
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have h := hW₀ W ((le_max_left _ _).trans hW)
  simp only [Function.comp] at h
  have hbF : b * (F / b) = F := by field_simp
  rw [← Real.rpow_mul hWpos.le, hbF, neg_mul] at h
  rw [Real.rpow_neg hWpos.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hWpos _)]
  linarith

/-- `W^{-(D+1)} + W^{-(D+1)} ≤ W^{-D}` for `W ≥ 2`. -/
private lemma step3Tail_two_le (W : ℕ) (hW : 2 ≤ W) (D : ℝ) :
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

private lemma step3Tail_blockHS2_nonneg {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x y : Fin L) : 0 ≤ blockHS2 X x y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The two-letter loop is the block norm. -/
private lemma step3Tail_loopTr_two_hs {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) :
    loopTr X ![a, b] ![true, false] = ((((W : ℝ) ^ 2)⁻¹ * blockHS2 X b a : ℝ) : ℂ) := by
  rw [loopTr_two]
  rfl

/-- A far pair: the block norm `‖G_{xy}‖²_HS` is at most `W² (W^{-(A+1)})²` when
`ℒ_2(y, x; +, -) = 𝒦_2 + D_2` with `‖𝒦_2‖ ≤ W^{-(2A+4)}` and `‖D_2‖ ≤ 2 W · W^{-(2A+4)}`. -/
private lemma step3Tail_far {W L : ℕ} (hW3 : 3 ≤ W) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x y : Fin L) (A : ℝ) (Err K2 : ℂ) (hdec : loopTr G ![y, x] ![true, false] = Err + K2)
    (hK : ‖K2‖ ≤ (W : ℝ) ^ (-(2 * A + 4))) (hE : ‖Err‖ ≤ 2 * (W : ℝ) * (W : ℝ) ^ (-(2 * A + 4))) :
    blockHS2 G x y ≤ (W : ℝ) ^ 2 * ((W : ℝ) ^ (-(A + 1))) ^ 2 := by
  have hW3' : (3 : ℝ) ≤ W := by exact_mod_cast hW3
  have hWpos : (0 : ℝ) < W := by linarith
  set w : ℝ := (W : ℝ) ^ (-(2 * A + 4)) with hw
  have hwpos : 0 < w := Real.rpow_pos_of_pos hWpos _
  have hsq : ((W : ℝ) ^ (-(A + 1))) ^ 2 = (W : ℝ) ^ 2 * w := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_natCast ((W : ℝ)), ← Real.rpow_mul hWpos.le,
      ← Real.rpow_add hWpos]
    congr 1
    push_cast
    ring
  have hnorm : ‖loopTr G ![y, x] ![true, false]‖ = ((W : ℝ) ^ 2)⁻¹ * blockHS2 G x y := by
    rw [step3Tail_loopTr_two_hs, Complex.norm_real, Real.norm_of_nonneg]
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (step3Tail_blockHS2_nonneg _ _ _)
  have h1 : ((W : ℝ) ^ 2)⁻¹ * blockHS2 G x y ≤ (1 + 2 * W) * w := by
    rw [← hnorm, hdec]
    calc ‖Err + K2‖ ≤ ‖Err‖ + ‖K2‖ := norm_add_le _ _
      _ ≤ (1 + 2 * W) * w := by nlinarith
  have hW2 : (0 : ℝ) < (W : ℝ) ^ 2 := by positivity
  rw [inv_mul_le_iff₀ hW2] at h1
  rw [hsq]
  calc blockHS2 G x y ≤ (W : ℝ) ^ 2 * ((1 + 2 * W) * w) := h1
    _ ≤ (W : ℝ) ^ 2 * ((W : ℝ) ^ 2 * w) := by
        apply mul_le_mul_of_nonneg_left _ hW2.le
        nlinarith

/-- The deterministic core of the tail bound: if the word has `k = n + 1 ≤ W^{ε/2}` letters and
diameter above `W^ε ℓ`, every block has Hilbert–Schmidt norm at most `W`, far pairs have norm at
most `W · W^{-(A+1)}` and `‖𝒦_k‖ ≤ W^{-(A+1)}`, then `|ℒ_k| + |D_k| ≤ W^{-A}`. -/
private lemma step3Tail_det {W L n : ℕ} [NeZero L] (hn : 1 ≤ n) (hW3 : 3 ≤ W)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (K : ∀ {k : ℕ}, (Fin k → Fin L) → (Fin k → Bool) → ℂ) (A ε ℓ : ℝ) (hℓ : 0 < ℓ)
    (hkW : ((n + 1 : ℕ) : ℝ) ≤ (W : ℝ) ^ (ε / 2))
    (hall : ∀ x y, blockHS2 G x y ≤ (W : ℝ) ^ 2)
    (hfar : ∀ x y, (W : ℝ) ^ (ε / 2) * ℓ < (cycDist x y : ℝ) →
      blockHS2 G x y ≤ (W : ℝ) ^ 2 * ((W : ℝ) ^ (-(A + 1))) ^ 2)
    (a : Fin (n + 1) → Fin L) (σ : Fin (n + 1) → Bool) (hdiam : (W : ℝ) ^ ε * ℓ < wordDiam a)
    (hK : ‖K a σ‖ ≤ (W : ℝ) ^ (-(A + 1))) :
    ‖loopTr G a σ‖ + ‖loopTr G a σ - K a σ‖ ≤ (W : ℝ) ^ (-A) := by
  have hW3' : (3 : ℝ) ≤ W := by exact_mod_cast hW3
  have hWpos : (0 : ℝ) < W := by linarith
  have hδ : 0 < (W : ℝ) ^ (-(A + 1)) := Real.rpow_pos_of_pos hWpos _
  have hsplit : (W : ℝ) ^ ε = (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hWpos]; congr 1; ring
  have hm : 0 ≤ (W : ℝ) ^ (ε / 2) * ℓ := mul_nonneg (Real.rpow_nonneg hWpos.le _) hℓ.le
  have hd : ((n + 1 : ℕ) : ℝ) * ((W : ℝ) ^ (ε / 2) * ℓ) < wordDiam a := by
    refine lt_of_le_of_lt ?_ hdiam
    rw [hsplit, mul_assoc]
    exact mul_le_mul_of_nonneg_right hkW hm
  obtain ⟨l, l', hl, hlt⟩ := step3Tail_long_edge (by omega) a _ hm hd
  have hloop : ‖loopTr G a σ‖ ≤ (W : ℝ) ^ (-(A + 1)) :=
    step3Tail_loop_le hn (by omega) G a σ _ hδ.le hall
      ⟨l, l', hl, hfar _ _ hlt, hfar _ _ (by rw [mol_cycDist_comm]; exact hlt)⟩
  have hexp : (W : ℝ) ^ (-A) = (W : ℝ) * (W : ℝ) ^ (-(A + 1)) := by
    rw [show -A = (1 : ℝ) + -(A + 1) by ring, Real.rpow_add hWpos, Real.rpow_one]
  calc ‖loopTr G a σ‖ + ‖loopTr G a σ - K a σ‖
      ≤ ‖loopTr G a σ‖ + (‖loopTr G a σ‖ + ‖K a σ‖) := by
        gcongr; exact norm_sub_le _ _
    _ ≤ 3 * (W : ℝ) ^ (-(A + 1)) := by linarith
    _ ≤ (W : ℝ) * (W : ℝ) ^ (-(A + 1)) := mul_le_mul_of_nonneg_right hW3' hδ.le
    _ = (W : ℝ) ^ (-A) := hexp.symm

/-- Step 3 of Appendix C.3 [sec:gc-one-step], joint tails (C.29) [fo:eq:step5-tails] at fixed
times: the long-edge argument with the primitive tails (5.21) [fo:eq:primitive-tail], the Step 2
pair bound with a floor `W^{-F}` chosen by (C.30) [gc:eq:floor], and crude bounds on the other
factors. -/
theorem step3_tail (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N cp₂ : ℝ) (hc : 0 < c)
    (hcp₂ : 0 < cp₂) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hN : lemmaNN0 I.Cw ≤ N)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) (h1 : Step1Out S)
    (h2 : Step2Out cp₂ θ S) :
    ∀ k : ℕ, 2 ≤ k → ∀ ε A : ℝ, 0 < ε → 0 < A → PrecMax StepPt.L S
      (Λ := fun W q => {w : Word k q.L // (W : ℝ) ^ ε * ellProp q.g q.L q.u < wordDiam w.1})
      (fun W q w ω => ((‖loopTr (flowG W (q.at q.u) ω) w.1.1 w.1.2‖ +
        ‖flowErr W (q.at q.u) w.1.1 w.1.2 ω‖ : ℝ) : ℂ))
      (fun W _ _ => (W : ℝ) ^ (-A)) := by
  intro k hk ε A hε hA
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  intro ε' D hε' hD
  have hN20 : (20 : ℝ) ≤ N := le_trans (le_max_left _ _) hN
  obtain ⟨Wd, hWd⟩ := R.dyson
  obtain ⟨W1, hW1⟩ := h2.pair (2 * A + 4) (by linarith) 1 (D + 1) one_pos (by linarith)
  obtain ⟨W2, hW2⟩ := h2.hs c (D + 1) hc (by linarith)
  obtain ⟨W3, hW3⟩ := R.primTail 2 le_rfl (ε / 2) (2 * A + 4) (half_pos hε) (by linarith)
  obtain ⟨W4, hW4⟩ := R.primTail (n + 1) hk ε (A + 1) hε (by linarith)
  obtain ⟨W5, hW5⟩ := step3Tail_exp_le cp₂ (ε / 2 * θ) (2 * A + 4) hcp₂ (by positivity)
    (by linarith)
  obtain ⟨W6, hW6⟩ : ∃ W6 : ℕ, ∀ W : ℕ, W6 ≤ W → ((n + 1 : ℕ) : ℝ) ≤ (W : ℝ) ^ (ε / 2) := by
    have ht : Tendsto (fun W : ℕ => (W : ℝ) ^ (ε / 2)) atTop atTop :=
      (tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop
    exact eventually_atTop.mp (ht.eventually_ge_atTop ((n + 1 : ℕ) : ℝ))
  refine ⟨max (max (max Wd W1) (max W2 W3)) (max (max W4 W5) (max W6 3)), fun W hW q hq => ?_⟩
  have hWd' : Wd ≤ W := by omega
  have hW1' : W1 ≤ W := by omega
  have hW2' : W2 ≤ W := by omega
  have hW3' : W3 ≤ W := by omega
  have hW4' : W4 ≤ W := by omega
  have hW5' : W5 ≤ W := by omega
  have hW6' : W6 ≤ W := by omega
  have hW3n : 3 ≤ W := by omega
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hW3r : (3 : ℝ) ≤ W := by exact_mod_cast hW3n
  obtain ⟨⟨d, hdJ, hreach⟩, hs12, hsu, hut, hst, hWt, hratio⟩ : StepAdm R c N W q := hS W hq
  have hreachu : CmpReach R.base W d (q.at q.u) :=
    CmpReach.earlier (base := R.base) (W := W) (p := q.at q.t) q.u hreach (by linarith) hut
  obtain ⟨hL3, hg0, -⟩ := hWd W hWd' d (q.at q.u) hdJ.le hreachu
  have hL3' : 3 ≤ q.L := hL3
  have hg0' : 0 ≤ q.g := hg0
  have : NeZero q.L := ⟨by omega⟩
  have : NeZero (q.at q.u).L := ⟨by omega⟩
  have ht1 : q.t < 1 := by
    have : (0 : ℝ) < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hWpos _
    linarith
  obtain ⟨hell1, -, -, hzpos, hzut, -⟩ :=
    scale_facts q.g hg0' W q.L (by omega) (by omega) q.u q.t (by linarith) hut ht1
  have hzpos' : 0 < zetaProp q.g W q.L q.u :=
    lt_of_lt_of_le (inv_pos.mpr (by positivity)) hzpos
  have hzt0 : 0 ≤ zetaProp q.g W q.L q.t := by linarith
  have hrat : 1 ≤ q.ratio := by
    unfold StepPt.ratio
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hrN : 1 ≤ q.ratio ^ N := Real.one_le_rpow hrat (by linarith)
  have hWc : (W : ℝ) ^ (-c) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hzt : zetaProp q.g W q.L q.t ≤ (W : ℝ) ^ (-c) :=
    (le_mul_of_one_le_left hzt0 hrN).trans hratio
  have hzu1 : zetaProp q.g W q.L q.u ≤ 1 := hzut.trans (hzt.trans hWc)
  have hprof : q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2 ≤ 1 := by
    have h6 : q.ratio ^ 6 ≤ q.ratio ^ N := by
      rw [show q.ratio ^ 6 = q.ratio ^ ((6 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
      exact Real.rpow_le_rpow_of_exponent_le hrat (by norm_num; linarith)
    calc q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2
        ≤ q.ratio ^ 6 * zetaProp q.g W q.L q.t := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
      _ ≤ q.ratio ^ N * zetaProp q.g W q.L q.t := mul_le_mul_of_nonneg_right h6 hzt0
      _ ≤ 1 := hratio.trans hWc
  have hzc : (W : ℝ) ^ c * zetaProp q.g W q.L q.u ≤ 1 := by
    calc (W : ℝ) ^ c * zetaProp q.g W q.L q.u ≤ (W : ℝ) ^ c * (W : ℝ) ^ (-c) :=
          mul_le_mul_of_nonneg_left (hzut.trans hzt) (Real.rpow_nonneg hWpos.le _)
      _ = 1 := by rw [← Real.rpow_add hWpos]; simp
  have hℓ : 0 < ellProp q.g q.L q.u := by linarith
  have e1 := hW1 W hW1' q hq
  have e2 := hW2 W hW2' q hq
  refine le_trans ?_ (step3Tail_two_le W (by omega) D)
  refine le_trans ?_ (add_le_add e1 e2)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  obtain ⟨w, hw⟩ := hω
  by_contra hnot
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hnot
  obtain ⟨hω1, hω2⟩ := hnot
  have hall : ∀ x y, blockHS2 (flowG W (q.at q.u) ω) x y ≤ (W : ℝ) ^ 2 := by
    intro x y
    have h := hω2 (x, y)
    rw [Complex.norm_real, Real.norm_of_nonneg (step3Tail_blockHS2_nonneg _ _ _)] at h
    calc blockHS2 (flowG W (q.at q.u) ω) x y
        ≤ (W : ℝ) ^ c * ((W : ℝ) ^ 2 * zetaProp q.g W q.L q.u) := h
      _ = ((W : ℝ) ^ c * zetaProp q.g W q.L q.u) * (W : ℝ) ^ 2 := by ring
      _ ≤ 1 * (W : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hzc (by positivity)
      _ = (W : ℝ) ^ 2 := one_mul _
  have hfar : ∀ x y : Fin q.L, (W : ℝ) ^ (ε / 2) * ellProp q.g q.L q.u < (cycDist x y : ℝ) →
      blockHS2 (flowG W (q.at q.u) ω) x y ≤ (W : ℝ) ^ 2 * ((W : ℝ) ^ (-(A + 1))) ^ 2 := by
    intro x y hxy
    have hdiam2 : (W : ℝ) ^ (ε / 2) * ellProp (q.at q.u).g (q.at q.u).L (q.at q.u).u <
        (wordDiam (![y, x] : Fin 2 → Fin (q.at q.u).L) : ℝ) := by
      refine lt_of_lt_of_le hxy ?_
      have : cycDist x y ≤ wordDiam (![y, x] : Fin 2 → Fin (q.at q.u).L) :=
        Finset.le_sup (f := fun p : Fin 2 × Fin 2 =>
          cycDist ((![y, x] : Fin 2 → Fin (q.at q.u).L) p.1)
            ((![y, x] : Fin 2 → Fin (q.at q.u).L) p.2)) (Finset.mem_univ (1, 0))
      exact_mod_cast this
    have hK := hW3 W hW3' d (q.at q.u) hdJ.le hreachu ![y, x] ![true, false] hdiam2
    have hE := hω1 (y, x)
    have hr : (W : ℝ) ^ (ε / 2) < (cycDist y x : ℝ) / ellProp q.g q.L q.u := by
      rw [lt_div_iff₀ hℓ, mol_cycDist_comm]; exact hxy
    have hθr : (W : ℝ) ^ (ε / 2 * θ) ≤ ((cycDist y x : ℝ) / ellProp q.g q.L q.u) ^ θ := by
      rw [Real.rpow_mul hWpos.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hWpos.le _) hr.le hθ.le
    have hexp : Real.exp (-(cp₂ * ((cycDist y x : ℝ) / ellProp q.g q.L q.u) ^ θ)) ≤
        (W : ℝ) ^ (-(2 * A + 4)) :=
      (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hθr hcp₂.le))).trans
        (hW5 W hW5')
    refine step3Tail_far hW3n _ x y A
      (flowErr W (q.at q.u) ![y, x] ![true, false] ω)
      (primLoop (q.at q.u).g W (q.at q.u).L (q.at q.u).E
        (mRoot (q.at q.u).g (q.at q.u).L (q.at q.u).E) (q.at q.u).u ![y, x] ![true, false])
      (by unfold flowErr; exact (sub_add_cancel _ _).symm) hK ?_
    have hwf : weightFn cp₂ θ (2 * A + 4) W (ellProp q.g q.L q.u) (cycDist y x) ≤
        2 * (W : ℝ) ^ (-(2 * A + 4)) := by
      unfold weightFn
      linarith
    have hwf0 : 0 ≤ weightFn cp₂ θ (2 * A + 4) W (ellProp q.g q.L q.u) (cycDist y x) := by
      unfold weightFn
      positivity
    calc ‖flowErr W (q.at q.u) ![y, x] ![true, false] ω‖
        ≤ (W : ℝ) ^ (1 : ℝ) * (q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2 *
          weightFn cp₂ θ (2 * A + 4) W (ellProp q.g q.L q.u) (cycDist y x)) := hE
      _ ≤ (W : ℝ) * (1 * (2 * (W : ℝ) ^ (-(2 * A + 4)))) := by
          rw [Real.rpow_one]
          apply mul_le_mul_of_nonneg_left _ hWpos.le
          exact mul_le_mul hprof hwf hwf0 zero_le_one
      _ = 2 * (W : ℝ) * (W : ℝ) ^ (-(2 * A + 4)) := by ring
  have hdiam := w.2
  have hK := hW4 W hW4' d (q.at q.u) hdJ.le hreachu w.1.1 w.1.2 hdiam
  have hdet := step3Tail_det hn hW3n (flowG W (q.at q.u) ω)
    (fun {k} a σ => primLoop (q.at q.u).g W (q.at q.u).L (q.at q.u).E
      (mRoot (q.at q.u).g (q.at q.u).L (q.at q.u).E) (q.at q.u).u a σ)
    A ε (ellProp q.g q.L q.u) hℓ (hW6 W hW6') hall hfar w.1.1 w.1.2 hdiam hK
  have hflow : flowErr W (q.at q.u) w.1.1 w.1.2 ω = loopTr (flowG W (q.at q.u) ω) w.1.1 w.1.2 -
      primLoop (q.at q.u).g W (q.at q.u).L (q.at q.u).E
        (mRoot (q.at q.u).g (q.at q.u).L (q.at q.u).E) (q.at q.u).u w.1.1 w.1.2 := rfl
  rw [← hflow] at hdet
  rw [Complex.norm_real, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] at hw
  have h1W : (1 : ℝ) ≤ (W : ℝ) ^ ε' := Real.one_le_rpow (by linarith) hε'.le
  have hpos : 0 < (W : ℝ) ^ (-A) := Real.rpow_pos_of_pos hWpos _
  nlinarith

end LSBA
