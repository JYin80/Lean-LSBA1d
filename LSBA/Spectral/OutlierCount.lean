import LSBA.Spectral.Measurability
import LSBA.Gauss.NormTail

/-!
# Outlier count by a dimension argument

`#{λ(T + diag V) ∉ [-K, K]} ≤ W · #{a : K − τ < ‖V_a‖}` for Hermitian `T` with `‖T‖ ≤ τ`, by a
norm argument on the span of the good blocks; the instance for the model (1.3) [eq:model] with
`0 ≤ g ≤ 1/4`, and the mean bound used in the proof of Theorem 3.1 [thm:strong-upper].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The `ℓ²` operator norm of `A` bounds the Euclidean norm of `A x`. -/
private lemma outlierCount_norm_mulVec_le {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (x : m → ℂ) :
    ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ m)‖ ≤
      ‖A‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ m)‖ := by
  have := A.l2_opNorm_mulVec (WithLp.toLp 2 x : EuclideanSpace ℂ m)
  simpa using this

/-- Parseval for the eigenbasis `v_k` of a Hermitian matrix: `‖Σ_k d_k v_k‖² = Σ_k |d_k|²`. -/
private lemma outlierCount_sum_sq_eigen {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (d : m → ℂ) :
    ∑ p, ‖(∑ k, d k • (hA.eigenvectorBasis k).ofLp) p‖ ^ 2 = ∑ k, ‖d k‖ ^ 2 := by
  have h1 := (hA.eigenvectorBasis).sum_repr_symm (WithLp.toLp 2 d)
  have h2 : ‖(hA.eigenvectorBasis).repr.symm (WithLp.toLp 2 d)‖ ^ 2 = ∑ k, ‖d k‖ ^ 2 := by
    rw [LinearIsometryEquiv.norm_map, EuclideanSpace.norm_sq_eq]
  rw [← h2, EuclideanSpace.norm_sq_eq, ← h1]
  simp

/-- Block `a` of `diag(V_a) x` is `V_a x_a`. -/
private lemma outlierCount_blockDiag_mulVec {W n : ℕ} (V : Fin n → Matrix (Fin W) (Fin W) ℂ)
    (x : Fin n × Fin W → ℂ) (a : Fin n) (α : Fin W) :
    (blockDiagOp V *ᵥ x) (a, α) = (V a *ᵥ fun β => x (a, β)) α := by
  simp [Matrix.mulVec, dotProduct, blockDiagOp, Fintype.sum_prod_type]

/-- If `x` vanishes on every block `a` with `‖V_a‖ > c ≥ 0`, then `‖diag(V_a) x‖ ≤ c ‖x‖`. -/
private lemma outlierCount_blockDiag_norm_le {W n : ℕ} (V : Fin n → Matrix (Fin W) (Fin W) ℂ)
    {c : ℝ} (hc : 0 ≤ c) (x : Fin n × Fin W → ℂ)
    (hx : ∀ a, c < ‖V a‖ → ∀ α, x (a, α) = 0) :
    ‖(WithLp.toLp 2 (blockDiagOp V *ᵥ x) : EuclideanSpace ℂ (Fin n × Fin W))‖ ≤
      c * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n × Fin W))‖ := by
  have key : ∀ a : Fin n, ∑ α, ‖(blockDiagOp V *ᵥ x) (a, α)‖ ^ 2 ≤
      c ^ 2 * ∑ α, ‖x (a, α)‖ ^ 2 := by
    intro a
    have h1 := outlierCount_norm_mulVec_le (V a) (fun β => x (a, β))
    have h2 : ∑ α, ‖(blockDiagOp V *ᵥ x) (a, α)‖ ^ 2 =
        ‖(WithLp.toLp 2 (V a *ᵥ fun β => x (a, β)) : EuclideanSpace ℂ (Fin W))‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [outlierCount_blockDiag_mulVec]
    have h3 : ∑ α, ‖x (a, α)‖ ^ 2 =
        ‖(WithLp.toLp 2 (fun β => x (a, β)) : EuclideanSpace ℂ (Fin W))‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    rw [h2, h3]
    by_cases hb : c < ‖V a‖
    · have h0 : (fun β => x (a, β)) = 0 := funext fun β => hx a hb β
      simp [h0]
    · have h4 : ‖V a‖ ≤ c := not_lt.mp hb
      calc ‖(WithLp.toLp 2 (V a *ᵥ fun β => x (a, β)) : EuclideanSpace ℂ (Fin W))‖ ^ 2
          ≤ (‖V a‖ * ‖(WithLp.toLp 2 (fun β => x (a, β)) : EuclideanSpace ℂ (Fin W))‖) ^ 2 := by
            gcongr
        _ ≤ (c * ‖(WithLp.toLp 2 (fun β => x (a, β)) : EuclideanSpace ℂ (Fin W))‖) ^ 2 := by
            gcongr
        _ = c ^ 2 * ‖(WithLp.toLp 2 (fun β => x (a, β)) : EuclideanSpace ℂ (Fin W))‖ ^ 2 := by
            ring
  have hsq : ‖(WithLp.toLp 2 (blockDiagOp V *ᵥ x) : EuclideanSpace ℂ (Fin n × Fin W))‖ ^ 2 ≤
      (c * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n × Fin W))‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
    simp only [Fintype.sum_prod_type]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => key a
  exact abs_le_of_sq_le_sq' hsq (by positivity) |>.2

/-- Schur test: if all row sums and all column sums of the moduli of `B` are at most `r`, then
`‖B‖ ≤ r` in the `ℓ²` operator norm. -/
private lemma outlierCount_schur {m : Type*} [Fintype m] [DecidableEq m] (B : Matrix m m ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : ∀ p, ∑ q, ‖B p q‖ ≤ r) (hc : ∀ q, ∑ p, ‖B p q‖ ≤ r) :
    ‖B‖ ≤ r := by
  have key : ∀ x : m → ℂ, ∑ p, ‖(B *ᵥ x) p‖ ^ 2 ≤ r ^ 2 * ∑ q, ‖x q‖ ^ 2 := by
    intro x
    have h1 : ∀ p, ‖(B *ᵥ x) p‖ ^ 2 ≤ r * ∑ q, ‖B p q‖ * ‖x q‖ ^ 2 := by
      intro p
      have h2 : ‖(B *ᵥ x) p‖ ≤ ∑ q, ‖B p q‖ * ‖x q‖ := by
        simp only [Matrix.mulVec, dotProduct]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
        rw [norm_mul]
      have h3 : (∑ q, ‖B p q‖ * ‖x q‖) ^ 2 ≤
          (∑ q, ‖B p q‖) * ∑ q, ‖B p q‖ * ‖x q‖ ^ 2 :=
        Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun q _ => norm_nonneg _)
          (fun q _ => by positivity) (fun q _ => le_of_eq (by ring))
      calc ‖(B *ᵥ x) p‖ ^ 2 ≤ (∑ q, ‖B p q‖ * ‖x q‖) ^ 2 := by gcongr
        _ ≤ (∑ q, ‖B p q‖) * ∑ q, ‖B p q‖ * ‖x q‖ ^ 2 := h3
        _ ≤ r * ∑ q, ‖B p q‖ * ‖x q‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right (hr p)
              (Finset.sum_nonneg fun q _ => by positivity)
    calc ∑ p, ‖(B *ᵥ x) p‖ ^ 2 ≤ ∑ p, r * ∑ q, ‖B p q‖ * ‖x q‖ ^ 2 :=
          Finset.sum_le_sum fun p _ => h1 p
      _ = r * ∑ q, (∑ p, ‖B p q‖) * ‖x q‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ ≤ r * ∑ q, r * ‖x q‖ ^ 2 := by
          gcongr with q
          exact hc q
      _ = r ^ 2 * ∑ q, ‖x q‖ ^ 2 := by
          rw [← Finset.mul_sum]; ring
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hr0 fun x => ?_
  have hsq : ‖(WithLp.toLp 2 (B *ᵥ x.ofLp) : EuclideanSpace ℂ m)‖ ^ 2 ≤ (r * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
    exact key x.ofLp
  have h4 := (abs_le_of_sq_le_sq' hsq (by positivity)).2
  have h5 : (Matrix.toEuclideanLin B) x = WithLp.toLp 2 (B *ᵥ x.ofLp) := rfl
  change ‖(Matrix.toEuclideanLin B) x‖ ≤ r * ‖x‖
  rw [h5]
  exact h4

/-- The cyclic successor on `Fin L`. -/
private def outlierCountSucc {L : ℕ} (a : Fin L) : Fin L :=
  ⟨(a.val + 1) % L, Nat.mod_lt _ (Fin.pos a)⟩

/-- The cyclic successor of `Fin L` is injective. -/
private lemma outlierCountSucc_injective {L : ℕ} :
    Function.Injective (outlierCountSucc : Fin L → Fin L) := by
  intro a a' h
  have h1 : ∀ c : Fin L, (c.val + 1) % L = if c.val + 1 < L then c.val + 1 else 0 := by
    intro c
    split_ifs with hc
    · exact Nat.mod_eq_of_lt hc
    · have : c.val + 1 = L := by have := c.2; omega
      rw [this, Nat.mod_self]
  have h2 : (a.val + 1) % L = (a'.val + 1) % L := congrArg Fin.val h
  rw [h1 a, h1 a'] at h2
  apply Fin.ext
  have := a.2
  have := a'.2
  split_ifs at h2 <;> omega

/-- `|(A_L)_{ab}|` is at most the number of the two shifts `a ↦ a ± 1` that connect `a` and `b`,
(1.3) [eq:model]. -/
private lemma outlierCount_cycleAdj_norm_le {L : ℕ} (a b : Fin L) :
    ‖cycleAdj L a b‖ ≤
      (if b = outlierCountSucc a then (1 : ℝ) else 0) +
        (if a = outlierCountSucc b then (1 : ℝ) else 0) := by
  have e1 : ∀ c d : Fin L, (d.val = (c.val + 1) % L) ↔ d = outlierCountSucc c := fun c d => by
    rw [Fin.ext_iff]; rfl
  simp only [cycleAdj, Matrix.of_apply, e1]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> split_ifs <;> simp

/-- At most one `x` has cyclic successor `c`. -/
private lemma outlierCount_succ_card_le {L : ℕ} (c : Fin L) :
    ∑ x : Fin L, (if c = outlierCountSucc x then (1 : ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  have : (univ.filter fun x : Fin L => c = outlierCountSucc x).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun x hx y hy => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact outlierCountSucc_injective (hx.symm.trans hy)
  exact_mod_cast this

/-- Exactly one `x` equals the cyclic successor of `c`. -/
private lemma outlierCount_succ_sum {L : ℕ} (c : Fin L) :
    ∑ x : Fin L, (if x = outlierCountSucc c then (1 : ℝ) else 0) = 1 := by
  simp

/-- `‖A_L ⊗ I_W‖ ≤ 2` for every `L` and `W`, by the Schur test on the row and column sums of the
adjacency matrix `A_L` of (1.3) [eq:model]. -/
private lemma outlierCount_cycleAdj_kron_norm_le (L W : ℕ) :
    ‖cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 2 := by
  have hrow : ∀ a : Fin L, ∑ b, ‖cycleAdj L a b‖ ≤ 2 := by
    intro a
    calc ∑ b, ‖cycleAdj L a b‖ ≤ ∑ b : Fin L, ((if b = outlierCountSucc a then (1 : ℝ) else 0) +
          (if a = outlierCountSucc b then (1 : ℝ) else 0)) :=
          Finset.sum_le_sum fun b _ => outlierCount_cycleAdj_norm_le a b
      _ ≤ 2 := by
          rw [Finset.sum_add_distrib, outlierCount_succ_sum]
          linarith [outlierCount_succ_card_le a]
  have hcol : ∀ b : Fin L, ∑ a, ‖cycleAdj L a b‖ ≤ 2 := by
    intro b
    calc ∑ a, ‖cycleAdj L a b‖ ≤ ∑ a : Fin L, ((if b = outlierCountSucc a then (1 : ℝ) else 0) +
          (if a = outlierCountSucc b then (1 : ℝ) else 0)) :=
          Finset.sum_le_sum fun a _ => outlierCount_cycleAdj_norm_le a b
      _ ≤ 2 := by
          rw [Finset.sum_add_distrib, outlierCount_succ_sum]
          linarith [outlierCount_succ_card_le b]
  refine outlierCount_schur _ (by norm_num) ?_ ?_
  · rintro ⟨a, α⟩
    simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply, norm_mul]
    simpa [apply_ite] using hrow a
  · rintro ⟨b, β⟩
    simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply, norm_mul]
    rw [Finset.sum_comm]
    simpa [apply_ite] using hcol b

/-- Outlier count: for Hermitian `T` with `‖T‖ ≤ τ` and Hermitian blocks `V_a`, the number of
eigenvalues of `T + diag(V_a)` outside `[-K, K]` is at most `W · #{a : ‖V_a‖ > K - τ}`. -/
theorem countIn_compl_Icc_le {W n : ℕ} (T : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)
    (hT : T.IsHermitian) (V : Fin n → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ a, (V a).IsHermitian)
    {τ : ℝ} (hτ : ‖T‖ ≤ τ) (K : ℝ) :
    countIn (T + blockDiagOp V) (Set.Icc (-K) K)ᶜ ≤ W * #(univ.filter fun a => K - τ < ‖V a‖) := by
  have hH : (T + blockDiagOp V).IsHermitian := hT.add (blockDiagOp_isHermitian hV)
  set bad : Finset (Fin n) := univ.filter fun a => K - τ < ‖V a‖ with hbad
  set S : Finset (Fin n × Fin W) :=
    univ.filter fun k => hH.eigenvalues k ∈ (Set.Icc (-K) K)ᶜ with hS
  have hcount : countIn (T + blockDiagOp V) (Set.Icc (-K) K)ᶜ = #S := by
    simp [countIn, hH, hS]
  rw [hcount, mul_comm]
  let v : Fin n × Fin W → (↥bad × Fin W → ℂ) :=
    fun k q => (hH.eigenvectorBasis k).ofLp (q.1.1, q.2)
  have hli : LinearIndepOn ℂ v (S : Set (Fin n × Fin W)) := by
    rw [linearIndepOn_finset_iff]
    intro f hf
    by_contra hcon
    push Not at hcon
    obtain ⟨k₀, hk₀S, hk₀⟩ := hcon
    set d : Fin n × Fin W → ℂ := fun k => if k ∈ S then f k else 0 with hd
    set y : Fin n × Fin W → ℂ := ∑ k, d k • (hH.eigenvectorBasis k).ofLp with hy
    have hynorm : ∑ p, ‖y p‖ ^ 2 = ∑ k, ‖d k‖ ^ 2 := outlierCount_sum_sq_eigen hH d
    have hdk₀ : 0 < ‖d k₀‖ ^ 2 := by
      simp only [hd, hk₀S, ite_true]
      positivity
    have hpos : 0 < ∑ k, ‖d k‖ ^ 2 :=
      lt_of_lt_of_le hdk₀ (Finset.single_le_sum (f := fun k => ‖d k‖ ^ 2)
        (fun k _ => by positivity) (Finset.mem_univ k₀))
    have hybad : ∀ a, K - τ < ‖V a‖ → ∀ α, y (a, α) = 0 := by
      intro a ha α
      have h1 := congrFun hf (⟨a, by simp [hbad, ha]⟩, α)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v, Pi.zero_apply] at h1
      simp only [hy, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hd]
      simpa [Finset.sum_ite_mem] using h1
    have hHy : (T + blockDiagOp V) *ᵥ y =
        ∑ k, (((hH.eigenvalues k : ℝ) : ℂ) * d k) • (hH.eigenvectorBasis k).ofLp := by
      simp only [hy, Matrix.mulVec_sum, Matrix.mulVec_smul, hH.mulVec_eigenvectorBasis]
      refine Finset.sum_congr rfl fun k _ => ?_
      ext p
      simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
      ring
    have hHnorm : ∑ p, ‖(((T + blockDiagOp V) *ᵥ y) p)‖ ^ 2 =
        ∑ k, (hH.eigenvalues k) ^ 2 * ‖d k‖ ^ 2 := by
      rw [hHy, outlierCount_sum_sq_eigen hH (fun k => ((hH.eigenvalues k : ℝ) : ℂ) * d k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hKτ : 0 ≤ K - τ := by
      by_contra hneg
      have hz : ∀ p, y p = 0 := fun p =>
        hybad p.1 (lt_of_lt_of_le (not_le.mp hneg) (norm_nonneg _)) p.2
      simp [hz] at hynorm
      linarith
    have hτ0 : 0 ≤ τ := (norm_nonneg T).trans hτ
    have hK0 : 0 ≤ K := by linarith
    have hlam : ∀ k ∈ S, K ^ 2 < (hH.eigenvalues k) ^ 2 := by
      intro k hk
      by_contra hcon
      have hk' : hH.eigenvalues k ∈ (Set.Icc (-K) K)ᶜ := (Finset.mem_filter.mp hk).2
      exact hk' (abs_le_of_sq_le_sq' (not_lt.mp hcon) hK0)
    have hYsq : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n × Fin W))‖ ^ 2 =
        ∑ k, ‖d k‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact hynorm
    have hTy := outlierCount_norm_mulVec_le T y
    have hDy := outlierCount_blockDiag_norm_le V hKτ y hybad
    have hbound : ‖(WithLp.toLp 2 ((T + blockDiagOp V) *ᵥ y) :
        EuclideanSpace ℂ (Fin n × Fin W))‖ ≤
        K * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n × Fin W))‖ := by
      rw [Matrix.add_mulVec, WithLp.toLp_add]
      calc _ ≤ ‖(WithLp.toLp 2 (T *ᵥ y) : EuclideanSpace ℂ (Fin n × Fin W))‖ +
            ‖(WithLp.toLp 2 (blockDiagOp V *ᵥ y) : EuclideanSpace ℂ (Fin n × Fin W))‖ :=
            norm_add_le _ _
        _ ≤ ‖T‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n × Fin W))‖ +
            (K - τ) * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n × Fin W))‖ :=
            add_le_add hTy hDy
        _ ≤ τ * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n × Fin W))‖ +
            (K - τ) * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n × Fin W))‖ := by gcongr
        _ = K * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n × Fin W))‖ := by ring
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    rw [mul_pow, hYsq, EuclideanSpace.norm_sq_eq] at hsq
    have hsq' : ∑ p, ‖(((T + blockDiagOp V) *ᵥ y) p)‖ ^ 2 ≤ K ^ 2 * ∑ k, ‖d k‖ ^ 2 := hsq
    rw [hHnorm, Finset.mul_sum] at hsq'
    have hlt : ∑ k, K ^ 2 * ‖d k‖ ^ 2 < ∑ k, (hH.eigenvalues k) ^ 2 * ‖d k‖ ^ 2 := by
      refine Finset.sum_lt_sum (fun k _ => ?_) ⟨k₀, Finset.mem_univ _, ?_⟩
      · by_cases hk : k ∈ S
        · exact mul_le_mul_of_nonneg_right (hlam k hk).le (by positivity)
        · simp [hd, hk]
      · exact mul_lt_mul_of_pos_right (hlam k₀ hk₀S) hdk₀
    linarith
  have hcard := hli.fintype_card_le_finrank
  simpa [Module.finrank_fintype_fun_eq_card] using hcard

/-- The outlier count for the model (1.3) [eq:model] with `0 ≤ g ≤ 1/4`. -/
theorem countIn_Hmat_compl_Icc_le {g : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1 / 4) (W L : ℕ) (ω : Ω W L)
    (K : ℝ) :
    countIn (Hmat g W L ω) (Set.Icc (-K) K)ᶜ ≤
      W * #(univ.filter fun a => K - 1 / 2 < ‖gueBlock W L ω a‖) := by
  have hmax : max 1 g = 1 := max_eq_left (by linarith)
  have hHm : Hmat g W L ω =
      (g : ℂ) • (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) +
        blockDiagOp (gueBlock W L ω) := by
    simp [Hmat, Hdet, hmax]
  have hK : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, (cycleAdj_isHermitian L).eq,
      Matrix.conjTranspose_one]
  have hT : ((g : ℂ) • (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hK.eq, Complex.star_def,
      Complex.conj_ofReal]
  have hnorm : ‖(g : ℂ) • (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))‖ ≤ 1 / 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg0]
    calc g * ‖cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ (1 / 4) * 2 := by
          gcongr
          exact outlierCount_cycleAdj_kron_norm_le L W
      _ = 1 / 2 := by norm_num
  rw [hHm]
  exact countIn_compl_Icc_le _ hT (gueBlock W L ω) (gueBlock_isHermitian W L ω) hnorm K

/-- The event `{‖V_a‖ > c}` for the block `V_a` of (1.2) [eq:covariance] is measurable. -/
private lemma outlierCount_measurableSet_norm_gt {W L : ℕ} (a : Fin L) (c : ℝ) :
    MeasurableSet {ω : Ω W L | c < ‖gueBlock W L ω a‖} := by
  have hm : Measurable fun ω : Ω W L => ‖gueBlock W L ω a‖ := by
    refine Measurable.norm ?_
    refine measurable_pi_iff.2 fun α => measurable_pi_iff.2 fun β => ?_
    simp only [gueBlock, Matrix.of_apply]
    split_ifs <;> fun_prop
  exact measurableSet_lt measurable_const hm

/-- The mean fraction of eigenvalues of (1.3) [eq:model] outside `[-33/2, 33/2]` is at most
`e^{-W/2}` for `W ≥ 32` and `0 ≤ g ≤ 1/4`. -/
theorem outlier_mean_le {g : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1 / 4) {W : ℕ} (hW : 32 ≤ W) (L : ℕ) :
    ((W : ℝ) * L)⁻¹ * ∫ ω, (countIn (Hmat g W L ω) (Set.Icc (-(33 / 2)) (33 / 2))ᶜ : ℝ) ∂(μ W L) ≤
      Real.exp (-(W : ℝ) / 2) := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp [Real.exp_nonneg]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  set E : Fin L → Set (Ω W L) := fun a => {ω | 16 < ‖gueBlock W L ω a‖} with hE
  have hEm : ∀ a, MeasurableSet (E a) := fun a => outlierCount_measurableSet_norm_gt a 16
  set G : Ω W L → ℝ := fun ω => (W : ℝ) * ∑ a, (E a).indicator (fun _ => (1 : ℝ)) ω with hG
  have hGint : Integrable G (μ W L) := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ fun a _ => (integrable_const (1 : ℝ)).indicator (hEm a)
  have hpt : ∀ ω, (countIn (Hmat g W L ω) (Set.Icc (-(33 / 2)) (33 / 2))ᶜ : ℝ) ≤ G ω := by
    intro ω
    have h1 := countIn_Hmat_compl_Icc_le hg0 hg W L ω (33 / 2)
    have h2 : (33 / 2 : ℝ) - 1 / 2 = 16 := by norm_num
    rw [h2] at h1
    have h3 : (#(univ.filter fun a => 16 < ‖gueBlock W L ω a‖) : ℝ) =
        ∑ a, (E a).indicator (fun _ => (1 : ℝ)) ω := by
      rw [Finset.natCast_card_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [hE, Set.indicator]
    calc (countIn (Hmat g W L ω) (Set.Icc (-(33 / 2)) (33 / 2))ᶜ : ℝ)
        ≤ ((W * #(univ.filter fun a => 16 < ‖gueBlock W L ω a‖) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = G ω := by rw [Nat.cast_mul, h3]
  have hint : ∫ ω, (countIn (Hmat g W L ω) (Set.Icc (-(33 / 2)) (33 / 2))ᶜ : ℝ) ∂(μ W L) ≤
      ∫ ω, G ω ∂(μ W L) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity) hGint
      (Filter.Eventually.of_forall hpt)
  have hGval : ∫ ω, G ω ∂(μ W L) = (W : ℝ) * ∑ a, (μ W L).real (E a) := by
    simp only [hG]
    rw [integral_const_mul, integral_finsetSum _ fun a _ =>
      (integrable_const (1 : ℝ)).indicator (hEm a)]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_indicator_const _ (hEm a), smul_eq_mul, mul_one]
  have hμ : ∀ a, (μ W L).real (E a) ≤ Real.exp (-(W : ℝ) / 2) := fun a =>
    ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _) (gueBlock_norm_tail hW a)
  have hsum : ∑ a, (μ W L).real (E a) ≤ L * Real.exp (-(W : ℝ) / 2) := by
    calc ∑ a, (μ W L).real (E a) ≤ ∑ _a : Fin L, Real.exp (-(W : ℝ) / 2) :=
          Finset.sum_le_sum fun a _ => hμ a
      _ = L * Real.exp (-(W : ℝ) / 2) := by simp
  calc ((W : ℝ) * L)⁻¹ * ∫ ω, (countIn (Hmat g W L ω) (Set.Icc (-(33 / 2)) (33 / 2))ᶜ : ℝ) ∂(μ W L)
      ≤ ((W : ℝ) * L)⁻¹ * ((W : ℝ) * (L * Real.exp (-(W : ℝ) / 2))) := by
        gcongr
        exact hint.trans (hGval ▸ mul_le_mul_of_nonneg_left hsum hWpos.le)
    _ = Real.exp (-(W : ℝ) / 2) := by field_simp

end LSBA
