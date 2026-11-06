import LSBA.Upper.LiftProduct

/-!
# The adjoint of the differential and the observation recursions

For a target `Z` in the algebra (10.3) [eq:c-Lie], the conjugates `Z_i = Q_i^{-*} Z Q_i^*` lie
in the algebra, so their lower-left blocks `R_i` are Hermitian and
`⟨𝒜(H), Z⟩ = g⁻¹ Σ_i ⟨H_i, R_i⟩`, that is `𝒜* Z = g⁻¹ (R_i)_i` with no projection; the blocks
`(P_i, U_i, R_i)` of `Z_i` satisfy the recursions of (G.18) [eq:c-observe], with `Z_q = Z`.
-/

open Real Finset
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `Z_i = Q_i^{-*} Z Q_i^*` of (G.18) [eq:c-observe] at input `i` (the paper's `i + 1`). Its
blocks `(0,0)`, `(0,1)`, `(1,0)` are `P_i, U_i, R_i`. -/
def liftConj {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ)
    (Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin q) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ((liftTail g z V i)⁻¹)ᴴ * Z * (liftTail g z V i)ᴴ

/-- (G.18) [eq:c-observe], first part: for `Z` in the algebra (10.3) [eq:c-Lie], every `Z_i`
lies in the algebra (so `R_i` is Hermitian), and `⟨𝒜(H), Z⟩ = g⁻¹ Σ_i ⟨H_i, R_i⟩`. -/
theorem hsInner_prodDiff {W q : ℕ} {g z : ℝ} {V : Fin q → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, (V i).IsHermitian) (H : Fin q → Matrix (Fin W) (Fin W) ℂ)
    {Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hZ : Z ∈ lieOmega W) :
    (∀ i, liftConj g z V Z i ∈ lieOmega W) ∧
      hsInner (prodDiff g z V H) Z =
        g⁻¹ * ∑ i, hsInner (H i) (blockPart (liftConj g z V Z i) 1 0) := by
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
  have hmem : ∀ i, liftConj g z V Z i ∈ lieOmega W := fun i => (conj_mem_lieOmega (hQ i) hZ).1
  refine ⟨hmem, ?_⟩
  have hpair : ∀ (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (K : Matrix (Fin W) (Fin W) ℂ),
      ((blockMat 0 0 K 0)ᴴ * Y).trace = (Kᴴ * blockPart Y 1 0).trace := by
    intro Y K
    rw [(blockMat_algebra 0 0 K 0 0 0 0 0).2.1]
    conv_lhs => rw [← (blockMat_blockPart Y (0 : Matrix (Fin W) (Fin W) ℂ) 0 0 0).1]
    rw [(blockMat_algebra _ _ _ _ _ _ _ _).1, (blockMat_algebra _ _ _ _ 0 0 0 0).2.2.1]
    simp
  have hterm : ∀ i, (((liftTail g z V i)⁻¹ * blockMat 0 0 (H i) 0 * liftTail g z V i)ᴴ *
      Z).trace = ((H i)ᴴ * blockPart (liftConj g z V Z i) 1 0).trace := by
    intro i
    rw [← hpair]
    have e : ((liftTail g z V i)⁻¹ * blockMat 0 0 (H i) 0 * liftTail g z V i)ᴴ * Z =
        (liftTail g z V i)ᴴ * ((blockMat 0 0 (H i) 0)ᴴ * ((liftTail g z V i)⁻¹)ᴴ * Z) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, liftConj]
    congr 1
    simp only [Matrix.mul_assoc]
  unfold prodDiff
  rw [(hsInner_reCoord _ _ 0).1, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    Matrix.smul_mul, Finset.sum_mul, Matrix.trace_smul, Matrix.trace_sum]
  simp only [hterm, hsInner_reCoord _ _ (0 : Fin 2 × Fin W × Fin W → ℝ) |>.1, smul_eq_mul,
    Complex.star_def, map_inv₀, Complex.conj_ofReal]
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]

/-- (G.18) [eq:c-observe], the recursions: `Z_q = Z`, and for consecutive inputs `j + 1 = i`
(the paper's `2 ≤ i ≤ q`), with `C = C_i`:
`P_{i-1} = -R_i C - P_i*`, `U_{i-1} = -R_i`, `R_{i-1} = P_i C + C P_i* + C R_i C - U_i`. -/
theorem liftConj_recursion {W q : ℕ} {g z : ℝ} {V : Fin q → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, (V i).IsHermitian) {Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hZ : Z ∈ lieOmega W) :
    (∀ i : Fin q, i.val + 1 = q → liftConj g z V Z i = Z) ∧
      ∀ i j : Fin q, j.val + 1 = i.val →
        blockPart (liftConj g z V Z j) 0 0 =
            -(blockPart (liftConj g z V Z i) 1 0 * liftC g z V i) -
              (blockPart (liftConj g z V Z i) 0 0)ᴴ ∧
          blockPart (liftConj g z V Z j) 0 1 = -blockPart (liftConj g z V Z i) 1 0 ∧
          blockPart (liftConj g z V Z j) 1 0 =
            blockPart (liftConj g z V Z i) 0 0 * liftC g z V i +
              liftC g z V i * (blockPart (liftConj g z V Z i) 0 0)ᴴ +
              liftC g z V i * blockPart (liftConj g z V Z i) 1 0 * liftC g z V i -
              blockPart (liftConj g z V Z i) 0 1 := by
  have hmem : ∀ i, liftConj g z V Z i ∈ lieOmega W :=
    (hsInner_prodDiff (g := g) (z := z) hV (fun _ => 0) hZ).1
  have hmul : ∀ A B C D A' B' C' D' : Matrix (Fin W) (Fin W) ℂ,
      blockMat A B C D * blockMat A' B' C' D' =
        blockMat (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') :=
    fun A B C D A' B' C' D' => (blockMat_algebra A B C D A' B' C' D').1
  have hadj : ∀ A B C D : Matrix (Fin W) (Fin W) ℂ,
      (blockMat A B C D)ᴴ = blockMat Aᴴ Cᴴ Bᴴ Dᴴ :=
    fun A B C D => (blockMat_algebra A B C D 0 0 0 0).2.1
  have hb00 : ∀ A B C D : Matrix (Fin W) (Fin W) ℂ, blockPart (blockMat A B C D) 0 0 = A :=
    fun A B C D => (blockMat_blockPart 0 A B C D).2.1
  have hb01 : ∀ A B C D : Matrix (Fin W) (Fin W) ℂ, blockPart (blockMat A B C D) 0 1 = B :=
    fun A B C D => (blockMat_blockPart 0 A B C D).2.2.1
  have hb10 : ∀ A B C D : Matrix (Fin W) (Fin W) ℂ, blockPart (blockMat A B C D) 1 0 = C :=
    fun A B C D => (blockMat_blockPart 0 A B C D).2.2.2.1
  have hC : ∀ i, (liftC g z V i)ᴴ = liftC g z V i := by
    intro i
    unfold liftC
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, (hV i).eq]
    simp [Complex.conj_ofReal]
  have hT : ∀ i, transferMat g (z : ℂ) (V i) = blockMat (liftC g z V i) (-1) 1 0 := by
    intro i
    ext ⟨a, α⟩ ⟨b, β⟩
    fin_cases a <;> fin_cases b <;>
      simp [transferMat, transferFree, liftC, blockMat, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Matrix.sub_apply]
    all_goals (split_ifs <;> simp)
  have hTi : ∀ i, transferInv g (z : ℂ) (V i) = blockMat 0 1 (-1) (liftC g z V i) := by
    intro i
    ext ⟨a, α⟩ ⟨b, β⟩
    fin_cases a <;> fin_cases b <;>
      simp [transferInv, liftC, blockMat, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Matrix.sub_apply]
    all_goals (split_ifs <;> simp)
  have hstep : ∀ i j : Fin q, j.val + 1 = i.val →
      liftTail g z V j = transferMat g (z : ℂ) (V i) * liftTail g z V i := by
    intro i j hji
    unfold liftTail
    rw [hji, List.drop_eq_getElem_cons (by simp), List.prod_cons]
    simp
  refine ⟨?_, ?_⟩
  · intro i hi
    have h1 : liftTail g z V i = 1 := by
      unfold liftTail
      rw [hi, List.drop_of_length_le (by simp)]
      simp
    simp [liftConj, h1]
  · intro i j hji
    obtain ⟨P, U, R, hY⟩ : ∃ P U R : Matrix (Fin W) (Fin W) ℂ,
        liftConj g z V Z i = blockMat P U R (-Pᴴ) := by
      have hZ' : blockMat (blockPart (liftConj g z V Z i) 0 0) (blockPart (liftConj g z V Z i) 0 1)
          (blockPart (liftConj g z V Z i) 1 0) (blockPart (liftConj g z V Z i) 1 1) ∈
            lieOmega W := by
        rw [(blockMat_blockPart (liftConj g z V Z i) 0 0 0 0).1]
        exact hmem i
      obtain ⟨-, -, hD, -⟩ := (mem_lieOmega_iff _ _ _ _).1 hZ'
      refine ⟨blockPart (liftConj g z V Z i) 0 0, blockPart (liftConj g z V Z i) 0 1,
        blockPart (liftConj g z V Z i) 1 0, ?_⟩
      rw [← hD]
      exact ((blockMat_blockPart (liftConj g z V Z i) 0 0 0 0).1).symm
    have hconj : liftConj g z V Z j =
        (transferInv g (z : ℂ) (V i))ᴴ * liftConj g z V Z i * (transferMat g (z : ℂ) (V i))ᴴ := by
      unfold liftConj
      rw [hstep i j hji, Matrix.mul_inv_rev, inv_transferMat, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [hconj, hY, hT i, hTi i]
    simp only [hmul, hadj, hb00, hb01, hb10, hC i, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one, Matrix.conjTranspose_neg]
    refine ⟨?_, ?_, ?_⟩ <;> noncomm_ring

end LSBA
