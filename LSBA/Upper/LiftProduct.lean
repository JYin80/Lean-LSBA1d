import LSBA.Upper.LieAlgebra
import LSBA.Upper.Operator

/-!
# The product `F = T_1 ⋯ T_q` and its differential

The product `F = T_1 ⋯ T_q` of Section 10 [sec:compact-proof] of the transfer matrices
`T_i = [[C_i, -I], [I, 0]]` with `C_i = z - V_i/g` (Definition 7.1 [def:transfer-matrices]),
where input `i` of `Fin q` stands for the paper's `V_{i+1}`; the tails `Q_i = T_{i+1} ⋯ T_q`;
the differential `𝒜(H) = F⁻¹ (H · ∇_V) F = g⁻¹ Σ_i Q_i⁻¹ [[0, 0], [H_i, 0]] Q_i` of (10.8)
[eq:c-product-map] and (G.17) [eq:c-differential], which maps Hermitian arrays into the algebra
(10.3) [eq:c-Lie]; and the reversal of the inputs, which turns `S* F S` into the batch
`S* T_q ⋯ T_1 S` of Definition 8.5 [up:def:transfer-operator] (proof of Lemma 8.13
[up:lem:density-contraction]).
-/

open MeasureTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The block `C_i = z - V_i/g` of the transfer matrix `T_i` (Definition 7.1
[def:transfer-matrices], (8.9) [eq:c-transfer]). -/
def liftC {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) (i : Fin q) :
    Matrix (Fin W) (Fin W) ℂ :=
  (z : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - ((g : ℂ)⁻¹) • V i

/-- `F = T_1 ⋯ T_q` of Section 10 [sec:compact-proof], input `i` in the place of `V_{i+1}`. -/
def liftProd {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (List.ofFn fun i => transferMat g (z : ℂ) (V i)).prod

/-- The tail `Q_i = T_{i+1} ⋯ T_q` of (10.8) [eq:c-product-map] at input `i` (the paper's index
`i + 1`); `Q_q = I`. -/
def liftTail {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) (i : Fin q) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ((List.ofFn fun j => transferMat g (z : ℂ) (V j)).drop (i.val + 1)).prod

/-- `𝒜(H) = g⁻¹ Σ_i Q_i⁻¹ [[0, 0], [H_i, 0]] Q_i` of (10.8) [eq:c-product-map] and (G.17)
[eq:c-differential]. -/
def prodDiff {W q : ℕ} (g z : ℝ) (V H : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ((g : ℂ)⁻¹) • ∑ i, (liftTail g z V i)⁻¹ * blockMat 0 0 (H i) 0 * liftTail g z V i

/-- (10.8) [eq:c-product-map], (G.17) [eq:c-differential]: `t ↦ F(V + t H)` has derivative
`F(V) 𝒜(H)` at `t = 0`. -/
theorem hasDerivAt_liftProd {W q : ℕ} (g z : ℝ) (V H : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    HasDerivAt (fun t : ℝ => liftProd g z (V + t • H)) (liftProd g z V * prodDiff g z V H) 0 := by
  have hunit : ∀ (n : ℕ) (U : Fin n → Matrix (Fin W) (Fin W) ℂ),
      IsUnit (liftProd g z U).det := by
    intro n U
    rw [← Matrix.isUnit_iff_isUnit_det]
    refine List.prod_isUnit fun M hM => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hM
    exact (Matrix.isUnit_iff_isUnit_det _).mpr
      (Matrix.isUnit_det_of_right_inverse (transferMat_mul_transferInv g _ _))
  have hT : ∀ (A B : Matrix (Fin W) (Fin W) ℂ) (t : ℝ),
      transferMat g (z : ℂ) (A + t • B) =
        transferMat g (z : ℂ) A + t • (-(((g : ℂ)⁻¹) • (!![1, 0; 0, 0] ⊗ₖ B))) := by
    intro A B t
    ext ⟨a, α⟩ ⟨b, β⟩
    simp [transferMat]
    ring
  have hN : ∀ A B : Matrix (Fin W) (Fin W) ℂ,
      transferMat g (z : ℂ) A * (((g : ℂ)⁻¹) • blockMat 0 0 B 0) =
        -(((g : ℂ)⁻¹) • (!![1, 0; 0, 0] ⊗ₖ B)) := by
    intro A B
    rw [Matrix.mul_smul, ← smul_neg]
    congr 1
    ext ⟨a, α⟩ ⟨b, β⟩
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, blockMat, transferMat,
        transferFree, Matrix.one_apply]
  have key : ∀ (n : ℕ) (U K : Fin n → Matrix (Fin W) (Fin W) ℂ),
      HasDerivAt (fun t : ℝ => liftProd g z (U + t • K)) (liftProd g z U * prodDiff g z U K) 0 := by
    intro n
    induction n with
    | zero =>
      intro U K
      simp only [liftProd, prodDiff, List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty,
        Finset.sum_empty, smul_zero, mul_zero]
      exact hasDerivAt_const _ _
    | succ n ih =>
      intro U K
      have hP : ∀ U' : Fin (n + 1) → Matrix (Fin W) (Fin W) ℂ,
          liftProd g z U' = transferMat g (z : ℂ) (U' 0) * liftProd g z (Fin.tail U') := by
        intro U'
        simp [liftProd, List.ofFn_succ, Fin.tail]
      have hQ0 : ∀ U' : Fin (n + 1) → Matrix (Fin W) (Fin W) ℂ,
          liftTail g z U' 0 = liftProd g z (Fin.tail U') := by
        intro U'
        simp [liftTail, liftProd, List.ofFn_succ, Fin.tail]
      have hQs : ∀ (U' : Fin (n + 1) → Matrix (Fin W) (Fin W) ℂ) (j : Fin n),
          liftTail g z U' j.succ = liftTail g z (Fin.tail U') j := by
        intro U' j
        simp [liftTail, List.ofFn_succ, Fin.tail]
      have hD : prodDiff g z U K = ((g : ℂ)⁻¹) • ((liftProd g z (Fin.tail U))⁻¹ *
          blockMat 0 0 (K 0) 0 * liftProd g z (Fin.tail U)) +
            prodDiff g z (Fin.tail U) (Fin.tail K) := by
        simp only [prodDiff]
        rw [Fin.sum_univ_succ, hQ0, smul_add]
        simp only [hQs]
        rfl
      have h1 : HasDerivAt (fun t : ℝ => transferMat g (z : ℂ) (U 0 + t • K 0))
          (-(((g : ℂ)⁻¹) • (!![1, 0; 0, 0] ⊗ₖ K 0))) 0 := by
        simp only [hT]
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
          (-(((g : ℂ)⁻¹) • (!![1, 0; 0, 0] ⊗ₖ K 0)))).const_add (transferMat g (z : ℂ) (U 0))
      have h3 := h1.mul (ih (Fin.tail U) (Fin.tail K))
      have hfun : (fun t : ℝ => liftProd g z (U + t • K)) =
          (fun t : ℝ => transferMat g (z : ℂ) (U 0 + t • K 0)) *
            (fun t : ℝ => liftProd g z (Fin.tail U + t • Fin.tail K)) := by
        funext t
        rw [hP]
        rfl
      rw [hfun]
      convert h3 using 1
      simp only [zero_smul, add_zero]
      have hinv := Matrix.mul_nonsing_inv _ (hunit n (Fin.tail U))
      rw [hP U, hD, ← hN (U 0) (K 0)]
      simp only [mul_add, Matrix.mul_smul, Matrix.smul_mul, mul_assoc]
      rw [← mul_assoc (liftProd g z (Fin.tail U)) _ _, hinv, one_mul]
  exact key q V H

/-- `𝒜(H)` lies in the algebra (10.3) [eq:c-Lie] for real `z` and Hermitian `V_i`, `H_i`. -/
theorem prodDiff_mem_lieOmega {W q : ℕ} {g z : ℝ} {V H : Fin q → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, (V i).IsHermitian) (hH : ∀ i, (H i).IsHermitian) :
    prodDiff g z V H ∈ lieOmega W := by
  have hJ : ∀ l : List (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
      (∀ M ∈ l, Mᴴ * phJ W * M = phJ W) → l.prodᴴ * phJ W * l.prod = phJ W := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons M l ih =>
      intro h
      have hM := h M List.mem_cons_self
      have hl := ih fun N hN => h N (List.mem_cons_of_mem _ hN)
      rw [List.prod_cons, Matrix.conjTranspose_mul]
      calc l.prodᴴ * Mᴴ * phJ W * (M * l.prod) = l.prodᴴ * (Mᴴ * phJ W * M) * l.prod := by
            simp only [mul_assoc]
        _ = phJ W := by rw [hM, hl]
  have hTi : ∀ i, (transferMat g (z : ℂ) (V i))ᴴ * phJ W * transferMat g (z : ℂ) (V i) =
      phJ W := by
    intro i
    simpa [transferProd] using
      transferProd_conjTranspose_mul_phJ g z (fun _ => V i) (fun _ => hV i) 1
  have hQ : ∀ i, (liftTail g z V i)ᴴ * phJ W * liftTail g z V i = phJ W := fun i =>
    hJ _ fun M hM => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hM)
      exact hTi j
  have hN : ∀ i, blockMat 0 0 (H i) 0 ∈ lieOmega W := fun i =>
    (mem_lieOmega_iff _ _ _ _).mpr ⟨Matrix.isHermitian_zero, hH i, by simp, by simp⟩
  have hadd : ∀ A B, A ∈ lieOmega W → B ∈ lieOmega W → A + B ∈ lieOmega W := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_add, add_mul, mul_add]
      calc Aᴴ * phJ W + Bᴴ * phJ W + (phJ W * A + phJ W * B)
          = (Aᴴ * phJ W + phJ W * A) + (Bᴴ * phJ W + phJ W * B) := by abel
        _ = 0 := by rw [hA1, hB1, add_zero]
    · rw [Matrix.trace_add, hA2, hB2, add_zero]
  have hzero : (0 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) ∈ lieOmega W :=
    ⟨by simp, by simp⟩
  have hsmul : ∀ (c : ℝ) A, A ∈ lieOmega W → (c : ℂ) • A ∈ lieOmega W := by
    rintro c A ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
        Matrix.mul_smul, ← smul_add, h1, smul_zero]
    · rw [Matrix.trace_smul, h2, smul_zero]
  unfold prodDiff
  rw [← Complex.ofReal_inv]
  exact hsmul _ _ (Finset.sum_induction _ (· ∈ lieOmega W) hadd hzero
    fun i _ => (conj_mem_lieOmega (hQ i) (hN i)).2)

/-- Reversal of the inputs (proof of Lemma 8.13 [up:lem:density-contraction]): the batch
`S* T_q ⋯ T_1 S` of Definition 8.5 [up:def:transfer-operator] is `S* F S` for the reversed
inputs, with `z = max{1, g} E / g`. -/
theorem batchMat_eq_liftProd (W : ℕ) (g E : ℝ) (q : ℕ) (ω : Ω W q) :
    batchMat W g E q ω = (freeConj W 0)ᴴ *
      liftProd g (max 1 g * E / g) (gueBlock W q (shiftMap W q Fin.revPerm ω)) * freeConj W 0 := by
  have hcongr : ∀ (U U' : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ), (∀ k < n, U k = U' k) →
      transferProd g ((max 1 g * E / g : ℝ) : ℂ) U n =
        transferProd g ((max 1 g * E / g : ℝ) : ℂ) U' n := by
    intro U U' n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro h
      simp only [transferProd]
      rw [h n (Nat.lt_succ_self n), ih fun k hk => h k (Nat.lt_succ_of_lt hk)]
  have key : ∀ (n : ℕ) (U : Fin n → Matrix (Fin W) (Fin W) ℂ),
      transferProd g ((max 1 g * E / g : ℝ) : ℂ) (fun k => if h : k < n then U ⟨k, h⟩ else 0) n =
        liftProd g (max 1 g * E / g) (fun i => U i.rev) := by
    intro n
    induction n with
    | zero => intro U; simp [transferProd, liftProd]
    | succ n ih =>
      intro U
      simp only [transferProd]
      rw [hcongr _ (fun k => if h : k < n then U (Fin.castSucc ⟨k, h⟩) else 0) n
        (fun k hk => by simp [hk, Nat.lt_succ_of_lt hk])]
      rw [ih fun i => U i.castSucc]
      simp only [liftProd, List.ofFn_succ, List.prod_cons, Fin.rev_succ, Fin.rev_zero]
      simp [Fin.last]
  unfold batchMat
  rw [key]
  rfl

end LSBA
