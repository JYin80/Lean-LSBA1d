import LSBA.Loop.Generator
import LSBA.Prop.Ward
import LSBA.Gauss.RoughDensity
import LSBA.Volume.LocalComparison

/-!
# Rows of resolvent loops

The sharp row of a loop of length two and the general row of a loop with one freely summed label
(Cauchy–Schwarz and the Ward identity (5.11) [gc:eq:ward]), and the bracket and light-term rows of
the loop generator, used in the proof of Lemma 5.6 [fo:prop:inputs].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Block projections, sandwiches and Hilbert–Schmidt sums -/

/-- The unnormalized projection onto block `x`. -/
private def lrP (W L : ℕ) (x : Fin L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.diagonal fun p => if p.1 = x then 1 else 0

/-- The inclusion of `ℂ^W` as block `x` of `ℂ^L ⊗ ℂ^W`. -/
private def lrJ (W L : ℕ) (x : Fin L) : Matrix (Fin L × Fin W) (Fin W) ℂ :=
  Matrix.of fun p α => if p = (x, α) then 1 else 0

private lemma lr_blockE_eq (W L : ℕ) (a : Fin L) :
    blockE W L a = (W : ℂ)⁻¹ • lrP W L a := by
  ext p q
  by_cases h : p = q
  · subst h
    by_cases h1 : p.1 = a <;> simp [blockE, lrP, h1]
  · simp [blockE, lrP, h]

private lemma lrP_mul_self (W L : ℕ) (x : Fin L) : lrP W L x * lrP W L x = lrP W L x := by
  unfold lrP
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  by_cases h : p.1 = x <;> simp [h]

private lemma lrP_conjTranspose (W L : ℕ) (x : Fin L) : (lrP W L x)ᴴ = lrP W L x := by
  unfold lrP
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases h : p.1 = x <;> simp [h]

private lemma lrJ_conjTranspose_mul (W L : ℕ) (x : Fin L) :
    (lrJ W L x)ᴴ * lrJ W L x = 1 := by
  ext α β
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, lrJ, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (x, α)]
  · by_cases h : α = β <;> simp [h]
  · intro p _ hp
    simp [hp]
  · simp

private lemma lrP_sandwich {W L : ℕ} (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (x y : Fin L) :
    lrP W L x * A * lrP W L y = lrJ W L x * blockOf A x y * (lrJ W L y)ᴴ := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  simp only [lrP, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, lrJ, blockOf, Matrix.of_apply, Matrix.conjTranspose_apply,
    Prod.mk.injEq]
  by_cases h1 : p1 = x <;> by_cases h2 : q1 = y <;> simp [h1, h2]

private lemma lrJ_norm_le (W L : ℕ) (x : Fin L) : ‖lrJ W L x‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (lrJ W L x)
  rw [lrJ_conjTranspose_mul] at h
  have h1 : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp
  nlinarith [norm_nonneg (lrJ W L x)]

/-- The operator norm of a block sandwich is at most the operator norm of the block. -/
private lemma norm_lrP_sandwich_le {W L : ℕ} (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x y : Fin L) : ‖lrP W L x * A * lrP W L y‖ ≤ ‖blockOf A x y‖ := by
  rw [lrP_sandwich]
  have h1 := Matrix.l2_opNorm_mul (lrJ W L x * blockOf A x y) (lrJ W L y)ᴴ
  have h2 := Matrix.l2_opNorm_mul (lrJ W L x) (blockOf A x y)
  rw [Matrix.l2_opNorm_conjTranspose] at h1
  have hJx := lrJ_norm_le W L x
  have hJy := lrJ_norm_le W L y
  have hB := norm_nonneg (blockOf A x y)
  calc _ ≤ ‖lrJ W L x * blockOf A x y‖ * ‖lrJ W L y‖ := h1
    _ ≤ (‖lrJ W L x‖ * ‖blockOf A x y‖) * ‖lrJ W L y‖ := by gcongr
    _ ≤ 1 * ‖blockOf A x y‖ * 1 := by gcongr
    _ = ‖blockOf A x y‖ := by ring

private lemma norm_lrP_le (W L : ℕ) (x : Fin L) : ‖lrP W L x‖ ≤ 1 := by
  unfold lrP
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
  by_cases h : p.1 = x <;> simp [h]

/-- The sum of squared moduli of the entries. -/
private def lrHS {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

private lemma lrHS_nonneg {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    0 ≤ lrHS A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

private lemma lrHS_mul_left_aux {n : Type*} [Fintype n] [DecidableEq n] (Y X : Matrix n n ℂ) :
    ∑ j, ∑ i, ‖(Y * X) i j‖ ^ 2 ≤ ‖Y‖ ^ 2 * ∑ j, ∑ i, ‖X i j‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  set x : EuclideanSpace ℂ n := (EuclideanSpace.equiv n ℂ).symm (fun i => X i j) with hx
  have h := Matrix.l2_opNorm_mulVec Y x
  have hxx : (EuclideanSpace.equiv n ℂ).symm (Y *ᵥ (fun i => X i j))
      = (EuclideanSpace.equiv n ℂ).symm (fun i => (Y * X) i j) := by
    congr 1
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa [hx, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h2

/-- `‖Y X‖_HS ≤ ‖Y‖ ‖X‖_HS`. -/
private lemma lrHS_mul_left {n : Type*} [Fintype n] [DecidableEq n] (Y X : Matrix n n ℂ) :
    lrHS (Y * X) ≤ ‖Y‖ ^ 2 * lrHS X := by
  unfold lrHS
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖X i j‖ ^ 2)]
  exact lrHS_mul_left_aux Y X

/-- `‖X Y‖_HS ≤ ‖X‖_HS ‖Y‖`. -/
private lemma lrHS_mul_right {n : Type*} [Fintype n] [DecidableEq n] (X Y : Matrix n n ℂ) :
    lrHS (X * Y) ≤ ‖Y‖ ^ 2 * lrHS X := by
  have h := lrHS_mul_left Yᴴ Xᴴ
  rw [← Matrix.conjTranspose_mul, Matrix.l2_opNorm_conjTranspose] at h
  have e1 : lrHS (X * Y)ᴴ = lrHS (X * Y) := by
    unfold lrHS
    rw [Finset.sum_comm]; simp [Matrix.conjTranspose_apply]
  have e2 : lrHS Xᴴ = lrHS X := by
    unfold lrHS
    rw [Finset.sum_comm]; simp [Matrix.conjTranspose_apply]
  rw [e1, e2] at h
  exact h

/-- Cauchy–Schwarz for the trace of a product in Hilbert–Schmidt form. -/
private lemma norm_trace_mul_le {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    ‖(A * B).trace‖ ≤ Real.sqrt (lrHS A) * Real.sqrt (lrHS B) := by
  have e1 : (A * B).trace = ∑ x : n × n, A x.1 x.2 * B x.2 x.1 := by
    rw [Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply]
    exact (Fintype.sum_prod_type (fun x : n × n => A x.1 x.2 * B x.2 x.1)).symm
  rw [e1]
  have e2 : lrHS A = ∑ x : n × n, ‖A x.1 x.2‖ ^ 2 := by
    unfold lrHS; rw [Fintype.sum_prod_type]
  have e3 : lrHS B = ∑ x : n × n, ‖B x.2 x.1‖ ^ 2 := by
    unfold lrHS; rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [e2, e3]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

private lemma lrHS_sandwich {W L : ℕ} (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c x : Fin L) :
    lrHS (lrP W L c * A * lrP W L x) = ∑ β : Fin W, ∑ α : Fin W, ‖A (c, β) (x, α)‖ ^ 2 := by
  have hent : ∀ p q : Fin L × Fin W, (lrP W L c * A * lrP W L x) p q =
      if p.1 = c ∧ q.1 = x then A p q else 0 := by
    rintro ⟨p1, p2⟩ ⟨q1, q2⟩
    simp only [lrP, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h1 : p1 = c <;> by_cases h2 : q1 = x <;> simp [h1, h2]
  unfold lrHS
  simp only [hent, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single c]
  · refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_eq_single x]
    · refine Finset.sum_congr rfl fun α _ => ?_
      simp
    · intro d _ hd
      simp [hd]
    · simp
  · intro d _ hd
    refine Finset.sum_eq_zero fun β _ => Finset.sum_eq_zero fun d' _ =>
      Finset.sum_eq_zero fun α _ => ?_
    simp [hd]
  · simp

private lemma lr_loopTr_one_false {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin L) : loopTr X ![a] ![false] = star (loopTr X ![a] ![true]) := by
  have h := star_loopTr X ![a] ![true]
  have e1 : (![a] : Fin 1 → Fin L) ∘ Fin.rev = ![a] := by
    ext j; fin_cases j; rfl
  have e2 : (fun j : Fin 1 => !(![true] (finRotate 1 (Fin.rev j)))) = ![false] := by
    ext j; fin_cases j; rfl
  rw [e1, e2] at h
  exact h.symm

/-- Ward's identity (5.11) [gc:eq:ward] in Hilbert–Schmidt form: both block sums of the squared
Hilbert–Schmidt norms at a fixed block `x` equal `W Im⟨G⟩_{xx} / Im z`. -/
private lemma lr_ward_hs {W L : ℕ} (hW : 1 ≤ W) (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) (x : Fin L) :
    (∑ c : Fin L, ∑ β : Fin W, ∑ α : Fin W, ‖resolventMat H z (c, β) (x, α)‖ ^ 2 =
      (W : ℝ) * (blockTr (resolventMat H z) x x).im / z.im) ∧
    (∑ c : Fin L, ∑ β : Fin W, ∑ α : Fin W, ‖resolventMat H z (x, β) (c, α)‖ ^ 2 =
      (W : ℝ) * (blockTr (resolventMat H z) x x).im / z.im) := by
  set G := resolventMat H z with hG
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hWc : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have key : ∀ s : Bool, ∑ c : Fin L, loopTr G (Fin.snoc ![x] c : Fin 2 → Fin L)
      (Fin.snoc (Function.update ![true] ⟨0, one_pos⟩ s) (!s) : Fin 2 → Bool) =
      (((blockTr G x x).im / ((W : ℝ) * z.im) : ℝ) : ℂ) := by
    intro s
    rw [loopTr_ward hW H hH z hz 1 le_rfl ![x] ![true] s]
    have h1 : Function.update ![true] (⟨0, one_pos⟩ : Fin 1) true = ![true] := by
      ext i; fin_cases i; simp
    have h2 : Function.update ![true] (⟨0, one_pos⟩ : Fin 1) false = ![false] := by
      ext i; fin_cases i; simp
    rw [h1, h2, lr_loopTr_one_false]
    have ht : loopTr G ![x] ![true] = blockTr G x x := loopTr_one G x
    rw [ht, Complex.star_def, Complex.sub_conj]
    have hzc : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    push_cast
    field_simp
  have hnorm : ∀ a b : Fin L, loopTr G ![a, b] ![true, false] =
      ((((W : ℝ) ^ 2)⁻¹ * ∑ β : Fin W, ∑ α : Fin W, ‖G (b, β) (a, α)‖ ^ 2 : ℝ) : ℂ) :=
    fun a b => loopTr_two G a b
  have conv : ∀ f : Fin L → ℝ, ∑ c, ((f c : ℝ) : ℂ) = ((∑ c, f c : ℝ) : ℂ) := fun f => by
    push_cast; rfl
  constructor
  · have k1 := key true
    have ha : ∀ c : Fin L, (Fin.snoc ![x] c : Fin 2 → Fin L) = ![x, c] := fun c => by
      ext i; fin_cases i <;> rfl
    have hs : (Fin.snoc (Function.update ![true] ⟨0, one_pos⟩ true) (!true) : Fin 2 → Bool) =
        ![true, false] := by
      ext i; fin_cases i <;> rfl
    simp only [ha, hs, hnorm, conv] at k1
    have k2 := Complex.ofReal_injective k1
    rw [← Finset.mul_sum] at k2
    have hz0 : z.im ≠ 0 := hz.ne'
    field_simp at k2 ⊢
    linarith
  · have k1 := key false
    have ha : ∀ c : Fin L, (Fin.snoc ![x] c : Fin 2 → Fin L) = ![c, x] ∘ finRotate 2 := fun c => by
      ext i; fin_cases i <;> rfl
    have hs : (Fin.snoc (Function.update ![true] ⟨0, one_pos⟩ false) (!false) : Fin 2 → Bool) =
        ![true, false] ∘ finRotate 2 := by
      ext i; fin_cases i <;> rfl
    simp only [ha, hs, loopTr_rotate, hnorm, conv] at k1
    have k2 := Complex.ofReal_injective k1
    rw [← Finset.mul_sum] at k2
    have hz0 : z.im ≠ 0 := hz.ne'
    field_simp at k2 ⊢
    linarith

private lemma lr_im_le {W L : ℕ} (hW : 1 ≤ W) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x : Fin L) (X : ℝ) (hX : ‖blockOf G x x‖ ≤ X) : (blockTr G x x).im ≤ X := by
  have hentry : ∀ i j : Fin W, ‖blockOf G x x i j‖ ≤ ‖blockOf G x x‖ := by
    intro i j
    have h := Matrix.l2_opNorm_mulVec (blockOf G x x) (EuclideanSpace.single j (1 : ℂ))
    have h1 : ‖(EuclideanSpace.single j (1 : ℂ))‖ = 1 := by simp
    rw [h1, mul_one] at h
    refine le_trans ?_ h
    have := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin W) ℂ).symm
      (blockOf G x x *ᵥ ⇑(EuclideanSpace.single j (1 : ℂ)))) i
    simpa [Matrix.mulVec, dotProduct] using this
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : ‖blockTr G x x‖ ≤ ‖blockOf G x x‖ := by
    unfold blockTr
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have h2 : ‖∑ α : Fin W, G (x, α) (x, α)‖ ≤ W * ‖blockOf G x x‖ := by
      refine (norm_sum_le _ _).trans ?_
      have : ∑ α : Fin W, ‖G (x, α) (x, α)‖ ≤ ∑ _α : Fin W, ‖blockOf G x x‖ :=
        Finset.sum_le_sum fun α _ => hentry α α
      simpa using this
    calc (W : ℝ)⁻¹ * ‖∑ α : Fin W, G (x, α) (x, α)‖ ≤ (W : ℝ)⁻¹ * (W * ‖blockOf G x x‖) := by
          gcongr
      _ = ‖blockOf G x x‖ := by field_simp
  exact (Complex.im_le_norm _).trans (h1.trans hX)

private lemma lr_hXs {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (X : ℝ)
    (hX : ∀ c d, ‖blockOf G c d‖ ≤ X) (s : Bool) (c d : Fin L) :
    ‖lrP W L c * sgnMat G s * lrP W L d‖ ≤ X := by
  cases s
  · have h := norm_lrP_sandwich_le G d c
    have e : lrP W L c * sgnMat G false * lrP W L d = (lrP W L d * G * lrP W L c)ᴴ := by
      simp only [sgnMat, Bool.false_eq_true, ite_false, Matrix.conjTranspose_mul,
        lrP_conjTranspose, Matrix.mul_assoc]
    rw [e, Matrix.l2_opNorm_conjTranspose]
    exact h.trans (hX d c)
  · exact (norm_lrP_sandwich_le G c d).trans (hX c d)

private lemma lr_prod_E {W L : ℕ} : ∀ (n : ℕ) (S : Fin n → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x : Fin n → Fin L), (List.ofFn fun p => S p * blockE W L (x p)).prod =
      ((W : ℂ)⁻¹) ^ n • (List.ofFn fun p => S p * lrP W L (x p)).prod
  | 0, S, x => by simp
  | n + 1, S, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      lr_prod_E n (fun p => S p.succ) (fun p => x p.succ), lr_blockE_eq]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1

private lemma lr_idem_split {n : Type*} [Fintype n] (P0 S0 P1 R : Matrix n n ℂ)
    (h : P1 * P1 = P1) : P0 * (S0 * P1 * R) = (P0 * S0 * P1) * (P1 * R) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P1 P1 R, h]

private lemma lr_chain_norm {W L : ℕ} (X : ℝ) (hX0 : 0 ≤ X) : ∀ (n : ℕ)
    (S : Fin n → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (x : Fin (n + 1) → Fin L),
    (∀ p : Fin n, ‖lrP W L (x p.castSucc) * S p * lrP W L (x p.succ)‖ ≤ X) →
    ‖lrP W L (x 0) * (List.ofFn fun p : Fin n => S p * lrP W L (x p.succ)).prod‖ ≤ X ^ n
  | 0, S, x, _ => by
    simpa using norm_lrP_le W L (x 0)
  | n + 1, S, x, h => by
    rw [List.ofFn_succ, List.prod_cons]
    have ih := lr_chain_norm X hX0 n (fun p => S p.succ) (fun p => x p.succ) (fun p => by
      have := h p.succ
      show ‖lrP W L (x p.castSucc.succ) * S p.succ * lrP W L (x p.succ.succ)‖ ≤ X
      rw [Fin.succ_castSucc]
      exact this)
    rw [lr_idem_split _ _ _ _ (lrP_mul_self W L _)]
    have h0 := h 0
    rw [Fin.castSucc_zero] at h0
    calc _ ≤ ‖lrP W L (x 0) * S 0 * lrP W L (x (Fin.succ 0))‖ *
          ‖lrP W L (x (Fin.succ 0)) *
            (List.ofFn fun i : Fin n => S i.succ * lrP W L (x i.succ.succ)).prod‖ :=
          Matrix.l2_opNorm_mul _ _
      _ ≤ X * X ^ n := by gcongr
      _ = X ^ (n + 1) := by ring

private lemma lr_chain_absorb {W L : ℕ} : ∀ (n : ℕ)
    (S : Fin n → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (x : Fin (n + 1) → Fin L),
    lrP W L (x 0) * (List.ofFn fun p : Fin n => S p * lrP W L (x p.succ)).prod *
      lrP W L (x (Fin.last n)) =
      lrP W L (x 0) * (List.ofFn fun p : Fin n => S p * lrP W L (x p.succ)).prod
  | 0, S, x => by
    simp [lrP_mul_self]
  | n + 1, S, x => by
    rw [List.ofFn_succ, List.prod_cons]
    have ih := lr_chain_absorb n (fun p => S p.succ) (fun p => x p.succ)
    rw [← Fin.succ_last]
    calc _ = lrP W L (x 0) * S 0 * (lrP W L (x (Fin.succ 0)) *
          (List.ofFn fun p : Fin n => S p.succ * lrP W L (x p.succ.succ)).prod *
          lrP W L (x (Fin.succ (Fin.last n)))) := by simp only [Matrix.mul_assoc]
      _ = lrP W L (x 0) * S 0 * (lrP W L (x (Fin.succ 0)) *
          (List.ofFn fun p : Fin n => S p.succ * lrP W L (x p.succ.succ)).prod) := by rw [ih]
      _ = _ := by simp only [Matrix.mul_assoc]

private lemma lr_loopTr_eq {W L k : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    loopTr X a σ = ((W : ℂ)⁻¹) ^ k *
      (List.ofFn fun p => sgnMat X (σ p) * lrP W L (a p)).prod.trace := by
  unfold loopTr
  rw [lr_prod_E k (fun p => sgnMat X (σ p)) a, Matrix.trace_smul, smul_eq_mul]

/-- One term of the row of a loop with the free label `c` in the first position. -/
private lemma lr_row_term {W L m : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (X : ℝ)
    (hX0 : 0 ≤ X) (hXs : ∀ (_ : Fin m) (s : Bool) (c d : Fin L),
      ‖lrP W L c * sgnMat G s * lrP W L d‖ ≤ X)
    (c : Fin L) (a₁ : Fin (m + 1) → Fin L) (s₀ : Bool) (σ₁ : Fin (m + 1) → Bool) :
    ‖loopTr G (Fin.cons c a₁ : Fin (m + 2) → Fin L) (Fin.cons s₀ σ₁ : Fin (m + 2) → Bool)‖ ≤
      ((W : ℝ)⁻¹) ^ (m + 2) *
        (Real.sqrt (lrHS (lrP W L c * sgnMat G (σ₁ 0) * lrP W L (a₁ 0))) * X ^ m *
          Real.sqrt (lrHS (lrP W L (a₁ (Fin.last m)) * sgnMat G s₀ * lrP W L c))) := by
  rw [lr_loopTr_eq]
  set S0 := sgnMat G s₀ with hS0
  set S1 := sgnMat G (σ₁ 0) with hS1
  set R2 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    (List.ofFn fun p : Fin m => sgnMat G (σ₁ p.succ) * lrP W L (a₁ p.succ)).prod with hR2
  set N := lrP W L (a₁ 0) * R2 with hNdef
  have hprod : (List.ofFn fun p : Fin (m + 2) =>
      sgnMat G ((Fin.cons s₀ σ₁ : Fin (m + 2) → Bool) p) *
      lrP W L ((Fin.cons c a₁ : Fin (m + 2) → Fin L) p)).prod =
      (S0 * lrP W L c) * (S1 * N) := by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    simp only [Fin.cons_zero, Fin.cons_succ, hNdef, hR2, hS0, hS1, Matrix.mul_assoc]
  rw [hprod]
  have hN : ‖N‖ ≤ X ^ m :=
    lr_chain_norm X hX0 m (fun p => sgnMat G (σ₁ p.succ)) a₁ (fun p => hXs p _ _ _)
  have hNP : N * lrP W L (a₁ (Fin.last m)) = N := lr_chain_absorb m _ a₁
  have hPN : lrP W L (a₁ 0) * N = N := by
    rw [hNdef, ← Matrix.mul_assoc, lrP_mul_self]
  set A := (lrP W L c * S1 * lrP W L (a₁ 0)) * N with hA
  set B := lrP W L (a₁ (Fin.last m)) * S0 * lrP W L c with hB
  have hAB : A * B = lrP W L c * (S1 * N * S0 * lrP W L c) := by
    calc A * B = lrP W L c * S1 * (lrP W L (a₁ 0) * N * lrP W L (a₁ (Fin.last m))) * S0 *
          lrP W L c := by simp only [hA, hB, Matrix.mul_assoc]
      _ = lrP W L c * S1 * N * S0 * lrP W L c := by rw [hPN, hNP]
      _ = _ := by simp only [Matrix.mul_assoc]
  have htr : ((S0 * lrP W L c) * (S1 * N)).trace = (A * B).trace := by
    rw [hAB, Matrix.trace_mul_comm (lrP W L c), Matrix.trace_mul_comm (S0 * lrP W L c)]
    congr 1
    calc S1 * N * (S0 * lrP W L c) = S1 * N * S0 * lrP W L c := by simp only [Matrix.mul_assoc]
      _ = S1 * N * S0 * (lrP W L c * lrP W L c) := by rw [lrP_mul_self]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [htr, norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hA' : lrHS A ≤ (X ^ m) ^ 2 * lrHS (lrP W L c * S1 * lrP W L (a₁ 0)) := by
    refine (lrHS_mul_right _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hN 2) (lrHS_nonneg _)
  refine (norm_trace_mul_le A B).trans ?_
  have hsA : Real.sqrt (lrHS A) ≤ X ^ m * Real.sqrt (lrHS (lrP W L c * S1 * lrP W L (a₁ 0))) := by
    refine (Real.sqrt_le_sqrt hA').trans ?_
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  calc Real.sqrt (lrHS A) * Real.sqrt (lrHS B)
      ≤ (X ^ m * Real.sqrt (lrHS (lrP W L c * S1 * lrP W L (a₁ 0)))) * Real.sqrt (lrHS B) := by
        gcongr
    _ = _ := by ring

private lemma lr_sgn_ward {W L : ℕ} (hW : 1 ≤ W) (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) (s : Bool) (x : Fin L) :
    (∑ c : Fin L, lrHS (lrP W L c * sgnMat (resolventMat H z) s * lrP W L x) =
      (W : ℝ) * (blockTr (resolventMat H z) x x).im / z.im) ∧
    (∑ c : Fin L, lrHS (lrP W L x * sgnMat (resolventMat H z) s * lrP W L c) =
      (W : ℝ) * (blockTr (resolventMat H z) x x).im / z.im) := by
  obtain ⟨w1, w2⟩ := lr_ward_hs hW H hH z hz x
  set G := resolventMat H z
  cases s
  · simp only [sgnMat, Bool.false_eq_true, ite_false, lrHS_sandwich, Matrix.conjTranspose_apply,
      Complex.star_def, Complex.norm_conj]
    constructor
    · rw [← w2]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_comm
    · rw [← w1]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_comm
  · simp only [sgnMat, ite_true, lrHS_sandwich]
    exact ⟨w1, w2⟩

/-- The row with the free label in the first position, in terms of the diagonal imaginary parts
at the two neighbouring labels. -/
private lemma lr_row_sum {W L m : ℕ} (hW : 1 ≤ W) (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) (X : ℝ) (hX0 : 0 ≤ X)
    (hXs : ∀ (_ : Fin m) (s : Bool) (c d : Fin L),
      ‖lrP W L c * sgnMat (resolventMat H z) s * lrP W L d‖ ≤ X)
    (a : Fin (m + 2) → Fin L) (σ : Fin (m + 2) → Bool) :
    ∑ c : Fin L, ‖loopTr (resolventMat H z) (Function.update a 0 c) σ‖ ≤
      ((W : ℝ)⁻¹) ^ (m + 2) *
        (Real.sqrt ((W : ℝ) * (blockTr (resolventMat H z) (a 1) (a 1)).im / z.im) * X ^ m *
          Real.sqrt ((W : ℝ) * (blockTr (resolventMat H z) (a (Fin.last (m + 1)))
            (a (Fin.last (m + 1)))).im / z.im)) := by
  set G := resolventMat H z with hG
  have ha : ∀ c, Function.update a 0 c =
      (Fin.cons c (Fin.tail a) : Fin (m + 2) → Fin L) := fun c => by
    conv_lhs => rw [← Fin.cons_self_tail a]
    exact Fin.update_cons_zero _ _ _
  have hσ : σ = (Fin.cons (σ 0) (Fin.tail σ) : Fin (m + 2) → Bool) := (Fin.cons_self_tail σ).symm
  have hx : Fin.tail a 0 = a 1 := rfl
  have hy : Fin.tail a (Fin.last m) = a (Fin.last (m + 1)) := by
    simp [Fin.tail, Fin.succ_last]
  have hs1 : Fin.tail σ 0 = σ 1 := rfl
  have hterm : ∀ c, ‖loopTr G (Function.update a 0 c) σ‖ ≤ ((W : ℝ)⁻¹) ^ (m + 2) *
      (Real.sqrt (lrHS (lrP W L c * sgnMat G (σ 1) * lrP W L (a 1))) * X ^ m *
        Real.sqrt (lrHS (lrP W L (a (Fin.last (m + 1))) * sgnMat G (σ 0) * lrP W L c))) := by
    intro c
    rw [ha c]
    conv_lhs => rw [hσ]
    have := lr_row_term G X hX0 hXs c (Fin.tail a) (σ 0) (Fin.tail σ)
    rwa [hx, hy, hs1] at this
  refine (Finset.sum_le_sum fun c _ => hterm c).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin L))
    (fun c => Real.sqrt (lrHS (lrP W L c * sgnMat G (σ 1) * lrP W L (a 1))))
    (fun c => Real.sqrt (lrHS (lrP W L (a (Fin.last (m + 1))) * sgnMat G (σ 0) * lrP W L c)))
  simp only [Real.sq_sqrt (lrHS_nonneg _)] at hcs
  rw [(lr_sgn_ward hW H hH z hz (σ 1) (a 1)).1,
    (lr_sgn_ward hW H hH z hz (σ 0) (a (Fin.last (m + 1)))).2] at hcs
  have e : ∑ c : Fin L, Real.sqrt (lrHS (lrP W L c * sgnMat G (σ 1) * lrP W L (a 1))) * X ^ m *
      Real.sqrt (lrHS (lrP W L (a (Fin.last (m + 1))) * sgnMat G (σ 0) * lrP W L c)) =
      X ^ m * ∑ c : Fin L, Real.sqrt (lrHS (lrP W L c * sgnMat G (σ 1) * lrP W L (a 1))) *
        Real.sqrt (lrHS (lrP W L (a (Fin.last (m + 1))) * sgnMat G (σ 0) * lrP W L c)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [e]
  calc _ ≤ X ^ m * (Real.sqrt ((W : ℝ) * (blockTr (resolventMat H z) (a 1) (a 1)).im / z.im) *
        Real.sqrt ((W : ℝ) * (blockTr (resolventMat H z) (a (Fin.last (m + 1)))
          (a (Fin.last (m + 1)))).im / z.im)) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by ring

private lemma lr_loopTr_shift {W L m : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin (m + 1) → Fin L) (σ : Fin (m + 1) → Bool) (i : Fin (m + 1)) :
    loopTr X (fun p => a (p + i)) (fun p => σ (p + i)) = loopTr X a σ := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    have h := loopTr_rotate X (fun p => a (p + i.castSucc)) (fun p => σ (p + i.castSucc))
    have e1 : (fun p : Fin (m + 1) => a (p + i.succ)) =
        (fun p => a (p + i.castSucc)) ∘ finRotate (m + 1) := by
      funext p
      simp only [Function.comp, finRotate_apply, ← Fin.coeSucc_eq_succ]
      congr 1
      abel
    have e2 : (fun p : Fin (m + 1) => σ (p + i.succ)) =
        (fun p => σ (p + i.castSucc)) ∘ finRotate (m + 1) := by
      funext p
      simp only [Function.comp, finRotate_apply, ← Fin.coeSucc_eq_succ]
      congr 1
      abel
    rw [e1, e2, h, ih]

/-- A loop with the free label at position `i` is the loop with the free label at position `0`
of the words shifted by `i`. -/
private lemma lr_loopTr_update_shift {W L m : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin (m + 1) → Fin L) (σ : Fin (m + 1) → Bool) (i : Fin (m + 1)) (c : Fin L) :
    loopTr X (Function.update a i c) σ =
      loopTr X (Function.update (fun p => a (p + i)) 0 c) (fun p => σ (p + i)) := by
  have h := lr_loopTr_shift X (Function.update a i c) σ i
  rw [← h]
  congr 1
  funext p
  by_cases hp : p = 0
  · subst hp
    simp
  · have : p + i ≠ i := fun h' => hp (by simpa using h')
    simp [hp, this]

private lemma lr_V_nonneg {W L : ℕ} (hW : 1 ≤ W) (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) (x : Fin L) :
    0 ≤ (W : ℝ) * (blockTr (resolventMat H z) x x).im / z.im := by
  rw [← (lr_sgn_ward hW H hH z hz true x).1]
  exact Finset.sum_nonneg fun _ _ => lrHS_nonneg _

private lemma lr_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

private lemma lr_insLab_update {L k : ℕ} (a : Fin k → Fin L) (i : Fin k) (c c' : Fin L) :
    Function.update (insLab a i c') i.castSucc c = insLab a i c := by
  unfold insLab
  exact Fin.update_insertNth _ _ _ _

private lemma lr_norm_loopTr_one_sub {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (m : ℂ) (τ : ℝ) (c : Fin L) (s : Bool) (h : ‖blockTr G c c - m‖ ≤ τ) :
    ‖loopTr G ![c] ![s] - sgnScalar m s‖ ≤ τ := by
  cases s
  · rw [lr_loopTr_one_false, sgnScalar]
    simp only [Bool.false_eq_true, ite_false]
    have e : loopTr G ![c] ![true] = blockTr G c c := loopTr_one G c
    rw [e, ← star_sub, norm_star]
    exact h
  · have e : loopTr G ![c] ![true] = blockTr G c c := loopTr_one G c
    simpa [sgnScalar, e] using h

private lemma lrHS_smul {n : Type*} [Fintype n] (c : ℂ) (A : Matrix n n ℂ) :
    lrHS (c • A) = ‖c‖ ^ 2 * lrHS A := by
  unfold lrHS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [mul_pow]

private lemma lrHS_sum_le {n : Type*} [Fintype n] {k : ℕ} (A : Fin k → Matrix n n ℂ) :
    lrHS (∑ i, A i) ≤ k * ∑ i, lrHS (A i) := by
  calc lrHS (∑ i, A i) = ∑ p : n, ∑ q : n, ‖∑ i : Fin k, A i p q‖ ^ 2 := by
        simp [lrHS, Matrix.sum_apply]
    _ ≤ ∑ p : n, ∑ q : n, (k : ℝ) * ∑ i : Fin k, ‖A i p q‖ ^ 2 := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
        refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
        simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k)))
          (f := fun i => ‖A i p q‖)
    _ = k * ∑ i, lrHS (A i) := by
        simp only [lrHS, ← Finset.mul_sum]
        congr 1
        calc _ = ∑ p : n, ∑ i : Fin k, ∑ q : n, ‖A i p q‖ ^ 2 :=
              Finset.sum_congr rfl fun p _ => Finset.sum_comm
          _ = _ := Finset.sum_comm

private lemma lr_trace_mul_conjTranspose {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) : (A * Aᴴ).trace = ((lrHS A : ℝ) : ℂ) := by
  unfold lrHS
  push_cast
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.mul_conj']

private lemma lr_loopB_shift {W L m : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin (m + 1) → Fin L) (σ : Fin (m + 1) → Bool) (i : Fin (m + 1)) :
    loopB X a σ i = loopB X (fun p => a (i + p)) (fun p => σ (i + p)) 0 := by
  simp only [loopB, zero_add, add_zero]

/-- One block row of the bracket of a loop: the `(c, c)` block of `loopB` at position `0` has
Hilbert–Schmidt norm at most `W^{-k} X^k` times that of the block `(c, a_0)` of the first
factor. -/
private lemma lr_loopB_term {W L m : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (X : ℝ)
    (hX0 : 0 ≤ X) (hXs : ∀ (s : Bool) (c d : Fin L), ‖lrP W L c * sgnMat G s * lrP W L d‖ ≤ X)
    (a : Fin (m + 1) → Fin L) (σ : Fin (m + 1) → Bool) (c : Fin L) :
    lrHS (lrP W L c * loopB G a σ 0 * lrP W L c) ≤
      ((W : ℝ)⁻¹) ^ (2 * (m + 1)) * (X ^ (m + 1)) ^ 2 *
        lrHS (lrP W L c * sgnMat G (σ 0) * lrP W L (a 0)) := by
  set S0 := sgnMat G (σ 0) with hS0
  set R2 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    (List.ofFn fun p : Fin m => sgnMat G (σ p.succ) * lrP W L (a p.succ)).prod with hR2
  set N := lrP W L (a 0) * R2 with hNdef
  have hB : loopB G a σ 0 = ((W : ℂ)⁻¹) ^ (m + 1) • ((S0 * lrP W L (a 0) * R2) * S0) := by
    simp only [loopB, zero_add]
    rw [lr_prod_E (m + 1) (fun p => sgnMat G (σ p)) a, List.ofFn_succ, List.prod_cons,
      Matrix.smul_mul]
  have hN : ‖N‖ ≤ X ^ m :=
    lr_chain_norm X hX0 m (fun p => sgnMat G (σ p.succ)) a (fun p => hXs _ _ _)
  have hNP : N * lrP W L (a (Fin.last m)) = N := lr_chain_absorb m _ a
  have hPN : lrP W L (a 0) * N = N := by
    rw [hNdef, ← Matrix.mul_assoc, lrP_mul_self]
  have hmid : lrP W L c * (S0 * lrP W L (a 0) * R2 * S0) * lrP W L c =
      (lrP W L c * S0 * lrP W L (a 0)) *
        (N * (lrP W L (a (Fin.last m)) * S0 * lrP W L c)) := by
    calc _ = lrP W L c * S0 * (lrP W L (a 0) * R2) * S0 * lrP W L c := by
          simp only [Matrix.mul_assoc]
      _ = lrP W L c * S0 * lrP W L (a 0) * (N * lrP W L (a (Fin.last m))) * S0 * lrP W L c := by
          rw [hNP, hNdef]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (lrP W L (a 0)) (lrP W L (a 0)), lrP_mul_self]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hB, Matrix.mul_smul, Matrix.smul_mul, lrHS_smul, hmid]
  have hnorm : ‖N * (lrP W L (a (Fin.last m)) * S0 * lrP W L c)‖ ≤ X ^ (m + 1) := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [pow_succ]
    exact mul_le_mul hN (hXs _ _ _) (norm_nonneg _) (by positivity)
  have h1 := lrHS_mul_right (lrP W L c * S0 * lrP W L (a 0))
    (N * (lrP W L (a (Fin.last m)) * S0 * lrP W L c))
  have h2 : ‖N * (lrP W L (a (Fin.last m)) * S0 * lrP W L c)‖ ^ 2 ≤ (X ^ (m + 1)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hc : ‖((W : ℂ)⁻¹) ^ (m + 1)‖ ^ 2 = ((W : ℝ)⁻¹) ^ (2 * (m + 1)) := by
    rw [norm_pow, norm_inv, Complex.norm_natCast, ← pow_mul, mul_comm, pow_mul]
  rw [hc]
  calc _ ≤ ((W : ℝ)⁻¹) ^ (2 * (m + 1)) * (‖N * (lrP W L (a (Fin.last m)) * S0 * lrP W L c)‖ ^ 2 *
        lrHS (lrP W L c * S0 * lrP W L (a 0))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ ((W : ℝ)⁻¹) ^ (2 * (m + 1)) * ((X ^ (m + 1)) ^ 2 *
        lrHS (lrP W L c * S0 * lrP W L (a 0))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (lrHS_nonneg _)) (by positivity)
    _ = _ := by ring

private lemma lr_smul_blockE {W : ℕ} (hW : 1 ≤ W) (L : ℕ) (c : Fin L) :
    (W : ℂ) • blockE W L c = lrP W L c := by
  rw [lr_blockE_eq, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 (by omega)), one_smul]

private lemma lr_gamma_sum {W L k : ℕ} (B : Fin k → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (c : Fin L) :
    ∑ i : Fin k, ∑ j : Fin k, (lrP W L c * B i * lrP W L c * (B j)ᴴ).trace =
      ((lrHS (∑ i : Fin k, lrP W L c * B i * lrP W L c) : ℝ) : ℂ) := by
  have hP := lrP_mul_self W L c
  have e1 : ∀ i j, (lrP W L c * B i * lrP W L c * (B j)ᴴ).trace =
      ((lrP W L c * B i * lrP W L c) * (lrP W L c * B j * lrP W L c)ᴴ).trace := by
    intro i j
    have h1 : (lrP W L c * B j * lrP W L c)ᴴ = lrP W L c * (B j)ᴴ * lrP W L c := by
      simp only [Matrix.conjTranspose_mul, lrP_conjTranspose, Matrix.mul_assoc]
    rw [h1]
    have h2 : (lrP W L c * B i * lrP W L c) * (lrP W L c * (B j)ᴴ * lrP W L c) =
        (lrP W L c * B i * lrP W L c * (B j)ᴴ) * lrP W L c := by
      calc _ = lrP W L c * B i * (lrP W L c * lrP W L c) * (B j)ᴴ * lrP W L c := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hP]
    have h3 : lrP W L c * (lrP W L c * B i * lrP W L c * (B j)ᴴ) =
        lrP W L c * B i * lrP W L c * (B j)ᴴ := by
      calc _ = (lrP W L c * lrP W L c) * B i * lrP W L c * (B j)ᴴ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hP]
    rw [h2, Matrix.trace_mul_comm (lrP W L c * B i * lrP W L c * (B j)ᴴ) (lrP W L c), h3]
  simp only [e1]
  rw [← lr_trace_mul_conjTranspose, Matrix.conjTranspose_sum, Finset.sum_mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_sum]

/-- Sharp row of a loop of length two with one freely summed label (Cauchy–Schwarz on the two
incident blocks and the Ward identity (5.11) [gc:eq:ward]): for `G = (H - z)⁻¹`, `H` Hermitian,
any signs and the label at position `i` summed, `Σ_c |ℒ_2(…, c, …)| ≤ Im⟨G⟩_{bb}/(W Im z)`,
where `b` is the other label. -/
theorem loopTr_two_row_ward {W L : ℕ} (hW : 1 ≤ W) (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) (a : Fin 2 → Fin L) (σ : Fin 2 → Bool)
    (i : Fin 2) :
    ∑ c : Fin L, ‖loopTr (resolventMat H z) (Function.update a i c) σ‖ ≤
      (blockTr (resolventMat H z) (a (i + 1)) (a (i + 1))).im / ((W : ℝ) * z.im) := by
  set G := resolventMat H z with hG
  have hsh : ∀ c, loopTr G (Function.update a i c) σ =
      loopTr G (Function.update (fun p => a (p + i)) 0 c) (fun p => σ (p + i)) :=
    fun c => lr_loopTr_update_shift (m := 1) G a σ i c
  simp only [hsh]
  have h := lr_row_sum (m := 0) hW H hH z hz 0 le_rfl (fun p => p.elim0) (fun p => a (p + i))
    (fun p => σ (p + i))
  have e : ∀ j : Fin 2, (1 : Fin 2) + j = j + 1 := by decide
  have e' : ∀ j : Fin 2, Fin.last (0 + 1) + j = j + 1 := by decide
  rw [e, e'] at h
  have hV := lr_V_nonneg hW H hH z hz (a (i + 1))
  rw [← hG] at h hV
  have hz0 : z.im ≠ 0 := hz.ne'
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  refine h.trans (le_of_eq ?_)
  rw [pow_zero, mul_one, Real.mul_self_sqrt hV, zero_add]
  field_simp

/-- Absolute row of a loop with one freely summed label (Cauchy–Schwarz on the two incident
blocks and the Ward identity (5.11) [gc:eq:ward]): for `G = (H - z)⁻¹`, `H` Hermitian, `k ≥ 2`
and `‖G_{cd}‖ ≤ X` for all blocks, `Σ_c |ℒ_k(…, c, …)| ≤ X^{k-1}/(W^{k-1} Im z)`. -/
theorem loopRows_row_ward {W L k : ℕ} (hk : 2 ≤ k) (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) (X : ℝ)
    (hX : ∀ c d, ‖blockOf (resolventMat H z) c d‖ ≤ X) (a : Fin k → Fin L) (σ : Fin k → Bool)
    (i : Fin k) :
    ∑ c : Fin L, ‖loopTr (resolventMat H z) (Function.update a i c) σ‖ ≤
      X ^ (k - 1) / ((W : ℝ) ^ (k - 1) * z.im) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  by_cases hW0 : W = 0
  · subst hW0
    have h0 : ∀ c, loopTr (resolventMat H z) (Function.update a i c) σ = 0 := fun c => by
      simp [loopTr, Matrix.trace]
    simp [h0]
  have hW1 : 1 ≤ W := Nat.pos_of_ne_zero hW0
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  set G := resolventMat H z with hG
  have hX0 : 0 ≤ X := le_trans (norm_nonneg _) (hX (a 0) (a 0))
  have hsh : ∀ c, loopTr G (Function.update a i c) σ =
      loopTr G (Function.update (fun p => a (p + i)) 0 c) (fun p => σ (p + i)) :=
    fun c => lr_loopTr_update_shift (m := m + 1) G a σ i c
  simp only [hsh]
  have h := lr_row_sum hW1 H hH z hz X hX0 (fun _ => lr_hXs G X hX) (fun p => a (p + i))
    (fun p => σ (p + i))
  rw [← hG] at h
  have hz0 : z.im ≠ 0 := hz.ne'
  have hV : 0 ≤ (W : ℝ) * X / z.im := by positivity
  have hs : ∀ x : Fin L, Real.sqrt ((W : ℝ) * (blockTr G x x).im / z.im) ≤
      Real.sqrt ((W : ℝ) * X / z.im) := fun x => by
    refine Real.sqrt_le_sqrt ?_
    gcongr
    exact lr_im_le hW1 G x X (hX x x)
  refine h.trans ?_
  calc _ ≤ ((W : ℝ)⁻¹) ^ (m + 2) * (Real.sqrt ((W : ℝ) * X / z.im) * X ^ m *
        Real.sqrt ((W : ℝ) * X / z.im)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul
          (mul_le_mul_of_nonneg_right (hs _) (pow_nonneg hX0 m)) (hs _) (Real.sqrt_nonneg _)
          (by positivity)) (by positivity)
    _ = X ^ (m + 2 - 1) / ((W : ℝ) ^ (m + 2 - 1) * z.im) := by
        have e : Real.sqrt ((W : ℝ) * X / z.im) * X ^ m * Real.sqrt ((W : ℝ) * X / z.im) =
            (W : ℝ) * X / z.im * X ^ m := by
          rw [mul_right_comm, Real.mul_self_sqrt hV]
        rw [e, show m + 2 - 1 = m + 1 by omega, inv_pow]
        field_simp
        ring

/-- The bracket (5.9) [gc:eq:bracket] of a resolvent loop at the characteristic `z_u` of (5.3)
[fo:eq:characteristic]: if `‖G_{cd}‖ ≤ X` for all blocks, then
`Re Γ(ℒ_k, ℒ_k) ≤ k² γ X^{2k+1}/(W^{2k} η_u)`. -/
theorem blockGamma_loopTr_le (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L k : ℕ} (hW : 1 ≤ W)
    (hk : 1 ≤ k) {u : ℝ} (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hM : M.IsHermitian) (X : ℝ) (hX : ∀ c d, ‖blockOf (resolventMat M (zChar g E m u)) c d‖ ≤ X)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    (blockGamma W L (gammaG g) (resLoop g E m a σ u) (resLoop g E m a σ u) M).re ≤
      (k : ℝ) ^ 2 * gammaG g * X ^ (2 * k + 1) / ((W : ℝ) ^ (2 * k) * etaChar g m u) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set G := resolventMat M (zChar g E m u) with hG
  have hγ := lr_gammaG_pos g
  have hη := etaChar_pos g m hm hu
  have hzim : 0 < (zChar g E m u).im := by rw [im_zChar]; exact hη
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hX0 : 0 ≤ X := le_trans (norm_nonneg _) (hX (a 0) (a 0))
  have hXs := lr_hXs G X hX
  rw [blockGamma_loopTr g E m hm hu hM a σ a σ]
  simp only [lr_smul_blockE hW, lr_gamma_sum]
  rw [Complex.re_ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  -- the row bound for each position
  have hrow : ∀ i : Fin (k' + 1), ∑ c : Fin L,
      lrHS (lrP W L c * loopB G a σ i * lrP W L c) ≤
        ((W : ℝ)⁻¹) ^ (2 * (k' + 1)) * (X ^ (k' + 1)) ^ 2 * ((W : ℝ) * X / (zChar g E m u).im) := by
    intro i
    rw [lr_loopB_shift]
    calc _ ≤ ∑ c : Fin L, ((W : ℝ)⁻¹) ^ (2 * (k' + 1)) * (X ^ (k' + 1)) ^ 2 *
          lrHS (lrP W L c * sgnMat G (σ (i + 0)) * lrP W L (a (i + 0))) :=
          Finset.sum_le_sum fun c _ => lr_loopB_term G X hX0 hXs (fun p => a (i + p))
            (fun p => σ (i + p)) c
      _ = ((W : ℝ)⁻¹) ^ (2 * (k' + 1)) * (X ^ (k' + 1)) ^ 2 *
          ∑ c : Fin L, lrHS (lrP W L c * sgnMat G (σ (i + 0)) * lrP W L (a (i + 0))) := by
          rw [Finset.mul_sum]
      _ ≤ _ := by
          rw [(lr_sgn_ward hW M hM (zChar g E m u) hzim (σ (i + 0)) (a (i + 0))).1]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := lr_im_le hW G (a (i + 0)) X (hX _ _)
          gcongr
  have hγW : 0 ≤ gammaG g / (W : ℝ) := by positivity
  calc gammaG g / (W : ℝ) * ∑ c : Fin L, lrHS (∑ i : Fin (k' + 1),
        lrP W L c * loopB G a σ i * lrP W L c)
      ≤ gammaG g / (W : ℝ) * ∑ c : Fin L, ((k' + 1 : ℕ) : ℝ) * ∑ i : Fin (k' + 1),
        lrHS (lrP W L c * loopB G a σ i * lrP W L c) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => lrHS_sum_le _) hγW
    _ = gammaG g / (W : ℝ) * (((k' + 1 : ℕ) : ℝ) * ∑ i : Fin (k' + 1), ∑ c : Fin L,
        lrHS (lrP W L c * loopB G a σ i * lrP W L c)) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ gammaG g / (W : ℝ) * (((k' + 1 : ℕ) : ℝ) * ∑ _i : Fin (k' + 1),
        (((W : ℝ)⁻¹) ^ (2 * (k' + 1)) * (X ^ (k' + 1)) ^ 2 * ((W : ℝ) * X / (zChar g E m u).im))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ => hrow i) (by positivity)) hγW
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, im_zChar,
          inv_pow]
        field_simp
        ring

/-- The light insertion `𝒲_k` of (5.7) [fo:eq:light] at the characteristic `z_u`: if
`‖G_{cd}‖ ≤ X` for all blocks and `|⟨G⟩_{cc} - m| ≤ τ` for all `c`, then
`‖𝒲_k‖ ≤ γ W k τ X^k/(W^k η_u)`. -/
theorem lightW_norm_le (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L k : ℕ} {u : ℝ} (hu : u < 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian) (X τ : ℝ)
    (hX : ∀ c d, ‖blockOf (resolventMat M (zChar g E m u)) c d‖ ≤ X)
    (hτ : ∀ c, ‖blockTr (resolventMat M (zChar g E m u)) c c - m‖ ≤ τ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ‖lightW g E m a σ u M‖ ≤
      gammaG g * W * k * τ * X ^ k / ((W : ℝ) ^ k * etaChar g m u) := by
  have hγ := lr_gammaG_pos g
  have hη := etaChar_pos g m hm hu
  rcases Nat.eq_zero_or_pos W with hW0 | hW1
  · subst hW0
    simp [lightW]
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    simp [lightW]
  set G := resolventMat M (zChar g E m u) with hG
  have hτ0 : 0 ≤ τ := le_trans (norm_nonneg _) (hτ (a ⟨0, hk1⟩))
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hzim : 0 < (zChar g E m u).im := by rw [im_zChar]; exact hη
  have hrow : ∀ i : Fin k, ∑ c : Fin L, ‖loopTr G (insLab a i c) (insSgn σ i)‖ ≤
      X ^ k / ((W : ℝ) ^ k * etaChar g m u) := by
    intro i
    have := loopRows_row_ward (W := W) (k := k + 1) (by omega) M hM (zChar g E m u) hzim X hX
      (insLab a i (a i)) (insSgn σ i) i.castSucc
    simp only [lr_insLab_update, Nat.add_sub_cancel, im_zChar] at this
    exact this
  unfold lightW
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hsum : ‖∑ i : Fin k, ∑ c : Fin L, (loopTr G ![c] ![σ i] - sgnScalar m (σ i)) *
      loopTr G (insLab a i c) (insSgn σ i)‖ ≤
      ∑ _i : Fin k, τ * (X ^ k / ((W : ℝ) ^ k * etaChar g m u)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c : Fin L,
          ‖(loopTr G ![c] ![σ i] - sgnScalar m (σ i)) * loopTr G (insLab a i c) (insSgn σ i)‖
        ≤ ∑ c : Fin L, τ * ‖loopTr G (insLab a i c) (insSgn σ i)‖ := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (lr_norm_loopTr_one_sub G m τ c (σ i) (hτ c))
            (norm_nonneg _)
      _ = τ * ∑ c : Fin L, ‖loopTr G (insLab a i c) (insSgn σ i)‖ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrow i) hτ0
  calc gammaG g * W * ‖∑ i : Fin k, ∑ c : Fin L, (loopTr G ![c] ![σ i] - sgnScalar m (σ i)) *
        loopTr G (insLab a i c) (insSgn σ i)‖
      ≤ gammaG g * W * ∑ _i : Fin k, τ * (X ^ k / ((W : ℝ) ^ k * etaChar g m u)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

end LSBA
