import LSBA.Transfer.Norms
import LSBA.Gauss.GUE
import LSBA.Gauss.ExpQuadratic

/-!
# One-step moments

The transfer matrix conjugated by `S_E`, `M_j = R_E + iηB_E + g⁻¹X_j`, and the one-step moment bound
(7.2) [uvs:eq:one-step-moment] for it and for its inverse, in the proof of Lemma 7.2
[uvs:lem:transfer-moments].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The conjugated transfer matrix `M = S_E⁻¹ T(E + iη) S_E`, proof of Lemma 7.2
[uvs:lem:transfer-moments]. -/
def transferConj {W : ℕ} (g E η : ℝ) (V : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (freeConj W E)⁻¹ * transferMat g (↑E + ↑η * Complex.I) V * freeConj W E

/-- `‖A x‖² ≤ ‖A‖² ‖x‖²` for the operator norm, in coordinates. -/
private lemma oneStep_sum_sq_mulVec_le {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
    (A : Matrix m n 𝕜) (x : n → 𝕜) :
    ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
  have h := A.l2_opNorm_mulVec (WithLp.toLp 2 x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa using h2

/-- A coordinatewise bound `‖A x‖² ≤ C ‖x‖²` bounds the operator norm: `‖A‖² ≤ C`. -/
private lemma oneStep_sq_opNorm_le {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : n → ℝ, ∑ i, (A *ᵥ x) i ^ 2 ≤ C * ∑ j, x j ^ 2) : ‖A‖ ^ 2 ≤ C := by
  have hA : ‖A‖ ≤ Real.sqrt C := by
    rw [Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    rw [mul_pow, Real.sq_sqrt hC, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simpa using h x.ofLp
  calc ‖A‖ ^ 2 ≤ Real.sqrt C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
    _ = C := Real.sq_sqrt hC

/-- A unitary matrix has operator norm at most `1`. -/
private lemma oneStep_norm_le_one {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : ‖U‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hU] at h
  have h1 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp
  nlinarith [norm_nonneg U]

/-- Real and imaginary parts of a complex vector. -/
private def oneStep_re {n : Type*} (z : n → ℂ) : n × Fin 2 → ℝ :=
  fun i => if i.2 = 0 then (z i.1).re else (z i.1).im

/-- `Σ (Re z_p)² + (Im z_p)² = Σ |z_p|²`. -/
private lemma oneStep_sum_sq_re {n : Type*} [Fintype n] (z : n → ℂ) :
    ∑ i, oneStep_re z i ^ 2 = ∑ p, ‖z p‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [oneStep_re, Fin.sum_univ_two, sq]

private lemma oneStep_re_add {n : Type*} (z z' : n → ℂ) :
    oneStep_re (z + z') = oneStep_re z + oneStep_re z' := by
  funext i
  simp only [oneStep_re, Pi.add_apply]
  split_ifs <;> simp

private lemma oneStep_re_smul {n : Type*} (c : ℝ) (z : n → ℂ) :
    oneStep_re ((c : ℂ) • z) = c • oneStep_re z := by
  funext i
  simp only [oneStep_re, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- `V_a(ω + ω') = V_a(ω) + V_a(ω')`. -/
private lemma oneStep_gueBlock_add (W L : ℕ) (x y : Ω W L) (a : Fin L) :
    gueBlock W L (x + y) a = gueBlock W L x a + gueBlock W L y a := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> push_cast <;> ring

/-- `V_a(c ω) = c V_a(ω)` for real `c`. -/
private lemma oneStep_gueBlock_smul (W L : ℕ) (c : ℝ) (x : Ω W L) (a : Fin L) :
    gueBlock W L (c • x) a = (c : ℂ) • gueBlock W L x a := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

/-- `((1 ⊗ A) v)(i, α) = Σ_β A_{αβ} v(i, β)`. -/
private lemma oneStep_kron_mulVec {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v : Fin 2 × Fin W → ℂ) (i : Fin 2) (α : Fin W) :
    (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A) *ᵥ v) (i, α) = ∑ β, A α β * v (i, β) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]


/-- `‖(1 ⊗ A) v‖² ≤ ‖A‖²_HS ‖v‖²`. -/
private lemma oneStep_kron_sum_sq_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v : Fin 2 × Fin W → ℂ) :
    ∑ p, ‖(((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A) *ᵥ v) p‖ ^ 2 ≤
      (∑ α, ∑ β, ‖A α β‖ ^ 2) * ∑ p, ‖v p‖ ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type (f := fun p => ‖v p‖ ^ 2), Finset.mul_sum]
  simp only [oneStep_kron_mulVec]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun α _ => ?_
  calc ‖∑ β, A α β * v (i, β)‖ ^ 2 ≤ (∑ β, ‖A α β‖ * ‖v (i, β)‖) ^ 2 := by
        gcongr
        exact (norm_sum_le _ _).trans (by simp)
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- `‖V_a‖²_HS ≤ W⁻¹ Σ ω²`. -/
private lemma oneStep_hs_gueBlock_le (W L : ℕ) (x : Ω W L) (a : Fin L) :
    ∑ α, ∑ β, ‖gueBlock W L x a α β‖ ^ 2 ≤ (W : ℝ)⁻¹ * ∑ k, x k ^ 2 := by
  rw [← sum_norm_sq_blockV]
  have h : ∀ α β, gueBlock W L x a α β = blockV W L x (a, α) (a, β) := by
    intro α β
    simp [blockV, blockDiagOp]
  simp_rw [h]
  calc ∑ α, ∑ β, ‖blockV W L x (a, α) (a, β)‖ ^ 2 ≤ ∑ α, ∑ q, ‖blockV W L x (a, α) q‖ ^ 2 := by
        gcongr with α
        rw [Fintype.sum_prod_type]
        exact Finset.single_le_sum (f := fun b => ∑ β, ‖blockV W L x (a, α) (b, β)‖ ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ a)
    _ ≤ ∑ p, ∑ q, ‖blockV W L x p q‖ ^ 2 := by
        rw [Fintype.sum_prod_type (f := fun p => ∑ q, ‖blockV W L x p q‖ ^ 2)]
        exact Finset.single_le_sum (f := fun b => ∑ α, ∑ q, ‖blockV W L x (b, α) q‖ ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ a)

/-- Completeness of `hermBasis` against a vector: `Σ_k ‖T_k z‖² = W ‖z‖²`. -/
private lemma oneStep_sum_hermBasis_sq (W : ℕ) (z : Fin W → ℂ) :
    ∑ k : Fin W × Fin W, ∑ α, ‖∑ β, hermBasis W k α β * z β‖ ^ 2 = W * ∑ β, ‖z β‖ ^ 2 := by
  have hc : ∀ c : ℂ, ((‖c‖ ^ 2 : ℝ) : ℂ) = c * star c := by
    intro c
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hH : ∀ k α m, star (hermBasis W k α m) = hermBasis W k m α := by
    intro k α m
    have := congrFun (congrFun (hermBasis_isHermitian W k) m) α
    simpa [Matrix.conjTranspose_apply] using this
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum]
  simp_rw [Complex.ofReal_sum, hc, star_sum, star_mul', hH, Finset.sum_mul_sum]
  calc ∑ k : Fin W × Fin W, ∑ α, ∑ β, ∑ m,
        hermBasis W k α β * z β * (hermBasis W k m α * star (z m))
      = ∑ α, ∑ β, ∑ m, z β * star (z m) *
          ∑ k : Fin W × Fin W, hermBasis W k α β * hermBasis W k m α := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = ∑ α : Fin W, ∑ β, z β * star (z β) := by
        simp [sum_hermBasis_apply_mul_apply]
    _ = _ := by
        simp [Finset.sum_const]

/-- The block `a` of the coordinate vector `e_{(a', k)}`. -/
private lemma oneStep_gueBlock_single (W L : ℕ) (a a' : Fin L) (k : Fin W × Fin W) :
    gueBlock W L (Pi.single (a', k) 1) a =
      if a' = a then ((Real.sqrt W : ℝ) : ℂ)⁻¹ • hermBasis W k else 0 := by
  rw [gueBlock_eq_sum_hermBasis]
  split_ifs with h
  · subst h
    congr 1
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'
      have : ((a', k'.1, k'.2) : Fin L × Fin W × Fin W) ≠ (a', k) := by
        intro h'
        simp only [Prod.mk.injEq] at h'
        exact hk' (by simpa using h'.2)
      simp [this]
    · simp
  · have : ∀ k' : Fin W × Fin W, ((a, k'.1, k'.2) : Fin L × Fin W × Fin W) ≠ (a', k) := by
      intro k' h'
      simp only [Prod.mk.injEq] at h'
      exact h h'.1.symm
    simp [this]


/-- `Σ_k ‖(1 ⊗ √t V_a(e_k)) v‖² = t ‖v‖²` over the coordinate vectors `e_k` of `Ω W L`. -/
private lemma oneStep_sum_kron_single (W L : ℕ) (hW : 0 < W) (a : Fin L) {t : ℝ} (ht : 0 ≤ t)
    (v : Fin 2 × Fin W → ℂ) :
    ∑ k : Fin L × Fin W × Fin W, ∑ p, ‖(((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
        (((Real.sqrt t : ℝ) : ℂ) • gueBlock W L (Pi.single k 1) a)) *ᵥ v) p‖ ^ 2 =
      t * ∑ p, ‖v p‖ ^ 2 := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · have hent : ∀ (k : Fin W × Fin W) (i : Fin 2) (α : Fin W),
        (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (((Real.sqrt t : ℝ) : ℂ) •
          gueBlock W L (Pi.single (a, k) 1) a)) *ᵥ v) (i, α) =
        ((Real.sqrt t / Real.sqrt W : ℝ) : ℂ) * ∑ β, hermBasis W k α β * v (i, β) := by
      intro k i α
      rw [oneStep_kron_mulVec, oneStep_gueBlock_single]
      simp only [ite_true, Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      simp only [Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    have hc : ‖((Real.sqrt t / Real.sqrt W : ℝ) : ℂ)‖ ^ 2 = t / W := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt ht,
        Real.sq_sqrt hW'.le]
    calc _ = ∑ k : Fin W × Fin W, ∑ i : Fin 2, ∑ α, (t / W) *
          ‖∑ β, hermBasis W k α β * v (i, β)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Fintype.sum_prod_type]
          simp only [hent, norm_mul, mul_pow, hc]
      _ = (t / W) * ∑ i : Fin 2, ∑ k : Fin W × Fin W, ∑ α,
          ‖∑ β, hermBasis W k α β * v (i, β)‖ ^ 2 := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
      _ = (t / W) * ∑ i : Fin 2, (W * ∑ β, ‖v (i, β)‖ ^ 2) := by
          simp only [oneStep_sum_hermBasis_sq]
      _ = t * ∑ p, ‖v p‖ ^ 2 := by
          rw [Fintype.sum_prod_type (f := fun p => ‖v p‖ ^ 2), ← Finset.mul_sum, ← mul_assoc,
            div_mul_cancel₀ _ hW'.ne']
  · intro a' _ ha'
    simp [oneStep_gueBlock_single, ha']
  · simp

/-- The real-linear map `ω ↦ (Re, Im)(-B (1 ⊗ √t V_a(ω)) v)`. -/
private def oneStep_xi (W L : ℕ) (a : Fin L) (t : ℝ)
    (B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (v : Fin 2 × Fin W → ℂ) :
    Ω W L →ₗ[ℝ] ((Fin 2 × Fin W) × Fin 2 → ℝ) where
  toFun x := oneStep_re (-(B *ᵥ (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
    (((Real.sqrt t : ℝ) : ℂ) • gueBlock W L x a)) *ᵥ v)))
  map_add' x y := by
    simp only [oneStep_gueBlock_add, smul_add, Matrix.kronecker_add, Matrix.add_mulVec,
      Matrix.mulVec_add, neg_add, oneStep_re_add]
  map_smul' c x := by
    simp only [oneStep_gueBlock_smul, RingHom.id_apply]
    rw [smul_comm, Matrix.kronecker_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, ← smul_neg,
      oneStep_re_smul]


/-- `‖Λ ω‖² = ‖B (1 ⊗ √t V_a(ω)) v‖²` for the matrix `Λ` of `oneStep_xi`. -/
private lemma oneStep_xi_sum_sq (W L : ℕ) (a : Fin L) (t : ℝ)
    (B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (v : Fin 2 × Fin W → ℂ) (x : Ω W L) :
    ∑ i, oneStep_xi W L a t B v x i ^ 2 = ∑ p, ‖(B *ᵥ (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
        (((Real.sqrt t : ℝ) : ℂ) • gueBlock W L x a)) *ᵥ v)) p‖ ^ 2 := by
  simp only [oneStep_xi, LinearMap.coe_mk, AddHom.coe_mk, oneStep_sum_sq_re, Pi.neg_apply,
    norm_neg]

/-- `‖√t A‖²_HS = t ‖A‖²_HS`. -/
private lemma oneStep_hs_smul {W : ℕ} {t : ℝ} (ht : 0 ≤ t) (A : Matrix (Fin W) (Fin W) ℂ) :
    ∑ α, ∑ β, ‖((((Real.sqrt t : ℝ) : ℂ) • A) α β)‖ ^ 2 = t * ∑ α, ∑ β, ‖A α β‖ ^ 2 := by
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg t), mul_pow, Real.sq_sqrt ht, Finset.mul_sum]

/-- Operator-norm bound for the matrix of `oneStep_xi`: `‖Λ‖² ≤ K² t W⁻¹ ‖v‖²`. -/
private lemma oneStep_xi_opNorm (W L : ℕ) (a : Fin L) {t K : ℝ} (ht : 0 ≤ t)
    {B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hB : ‖B‖ ≤ K) (v : Fin 2 × Fin W → ℂ) :
    ‖LinearMap.toMatrix' (oneStep_xi W L a t B v)‖ ^ 2 ≤
      K ^ 2 * t * (W : ℝ)⁻¹ * ∑ p, ‖v p‖ ^ 2 := by
  have hK : ‖B‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hB 2
  refine oneStep_sq_opNorm_le _ (by positivity) fun x => ?_
  rw [LinearMap.toMatrix'_mulVec, oneStep_xi_sum_sq]
  refine (oneStep_sum_sq_mulVec_le _ _).trans ?_
  have h1 := oneStep_kron_sum_sq_le (((Real.sqrt t : ℝ) : ℂ) • gueBlock W L x a) v
  rw [oneStep_hs_smul ht] at h1
  have h2 := oneStep_hs_gueBlock_le W L x a
  have hv : 0 ≤ ∑ p, ‖v p‖ ^ 2 := by positivity
  have hx : 0 ≤ ∑ k, x k ^ 2 := by positivity
  calc ‖B‖ ^ 2 * ∑ p, ‖(((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
        (((Real.sqrt t : ℝ) : ℂ) • gueBlock W L x a)) *ᵥ v) p‖ ^ 2
      ≤ K ^ 2 * (t * ((W : ℝ)⁻¹ * ∑ k, x k ^ 2) * ∑ p, ‖v p‖ ^ 2) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = K ^ 2 * t * (W : ℝ)⁻¹ * (∑ p, ‖v p‖ ^ 2) * ∑ k, x k ^ 2 := by ring

/-- Hilbert–Schmidt bound for the matrix of `oneStep_xi`: `‖Λ‖²_HS ≤ K² t ‖v‖²`. -/
private lemma oneStep_xi_hs (W L : ℕ) (hW : 0 < W) (a : Fin L) {t K : ℝ} (ht : 0 ≤ t)
    {B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hB : ‖B‖ ≤ K) (v : Fin 2 × Fin W → ℂ) :
    ∑ i, ∑ k, LinearMap.toMatrix' (oneStep_xi W L a t B v) i k ^ 2 ≤
      K ^ 2 * t * ∑ p, ‖v p‖ ^ 2 := by
  have hK : ‖B‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hB 2
  simp only [LinearMap.toMatrix'_apply]
  rw [Finset.sum_comm]
  simp only [oneStep_xi_sum_sq]
  calc _ ≤ ∑ k : Fin L × Fin W × Fin W, K ^ 2 * ∑ p, ‖(((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
        (((Real.sqrt t : ℝ) : ℂ) • gueBlock W L (Pi.single k 1) a)) *ᵥ v) p‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => (oneStep_sum_sq_mulVec_le _ _).trans ?_
        exact mul_le_mul_of_nonneg_right hK (by positivity)
    _ = K ^ 2 * t * ∑ p, ‖v p‖ ^ 2 := by
        rw [← Finset.mul_sum, oneStep_sum_kron_single W L hW a ht, mul_assoc]

/-- The Gaussian step: for `x` standard Gaussian, a real matrix `Λ`, a vector `r` and `n > 0`,
`E (Σ (r + cΛx)²)^q ≤ e^D n^q` as soon as `(2qc²/n)‖Λ‖² ≤ 1/2` and `D` dominates the exponent
`q(‖r‖²/n - 1) + (2qc²/n)‖Λ‖²_HS + ‖Λ‖² ‖(2qc/n) r‖²`. -/
private lemma oneStep_core {ι m : Type*} [Fintype ι] [Fintype m] [DecidableEq ι]
    (Λ : Matrix m ι ℝ) (r : m → ℝ) {c n q D : ℝ} (hn : 0 < n) (hq : 0 ≤ q)
    (hs : 2 * q * c ^ 2 / n * ‖Λ‖ ^ 2 ≤ 1 / 2)
    (hD : q * ((∑ i, r i ^ 2) / n - 1) + (2 * q * c ^ 2 / n * ∑ i, ∑ j, Λ i j ^ 2 +
      ‖Λ‖ ^ 2 * ∑ i, (2 * q * c / n * r i) ^ 2) ≤ D) :
    Integrable (fun x => (∑ i, (r i + c * (Λ *ᵥ x) i) ^ 2) ^ q) (stdGauss ι) ∧
      ∫ x, (∑ i, (r i + c * (Λ *ᵥ x) i) ^ 2) ^ q ∂(stdGauss ι) ≤ Real.exp D * n ^ q := by
  set s := 2 * q * c ^ 2 / n with hs_def
  set b : m → ℝ := fun i => 2 * q * c / n * r i with hb_def
  obtain ⟨hI, hle⟩ := integral_exp_linear_add_quadratic_le Λ b (s := s) (by positivity) hs
  set C0 := q * ((∑ i, r i ^ 2) / n - 1) with hC0
  have hpt : ∀ x : ι → ℝ, (∑ i, (r i + c * (Λ *ᵥ x) i) ^ 2) ^ q ≤
      n ^ q * Real.exp C0 * Real.exp (b ⬝ᵥ (Λ *ᵥ x) + s / 2 * ∑ i, (Λ *ᵥ x) i ^ 2) := by
    intro x
    set u := Λ *ᵥ x
    set y := ∑ i, (r i + c * u i) ^ 2 with hy
    have hy0 : 0 ≤ y := by positivity
    have hsplit : y = ∑ i, r i ^ 2 + ∑ i, (2 * c * r i * u i + c ^ 2 * u i ^ 2) := by
      rw [hy, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hexp : (y / n - 1) * q = C0 + (b ⬝ᵥ u + s / 2 * ∑ i, u i ^ 2) := by
      have h2 : b ⬝ᵥ u + s / 2 * ∑ i, u i ^ 2 =
          q / n * ∑ i, (2 * c * r i * u i + c ^ 2 * u i ^ 2) := by
        simp only [hb_def, hs_def, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
      rw [h2, hC0, hsplit]
      field_simp
      ring
    have h1 : y / n ≤ Real.exp (y / n - 1) := by linarith [Real.add_one_le_exp (y / n - 1)]
    calc y ^ q = (n * (y / n)) ^ q := by rw [mul_div_cancel₀ _ hn.ne']
      _ = n ^ q * (y / n) ^ q := Real.mul_rpow hn.le (by positivity)
      _ ≤ n ^ q * Real.exp (y / n - 1) ^ q := by gcongr
      _ = n ^ q * Real.exp C0 * Real.exp (b ⬝ᵥ u + s / 2 * ∑ i, u i ^ 2) := by
        rw [← Real.exp_mul, hexp, Real.exp_add, mul_assoc]
  have hcont : Continuous fun x : ι → ℝ => (∑ i, (r i + c * (Λ *ᵥ x) i) ^ 2) ^ q := by
    have hmv : Continuous fun x : ι → ℝ => Λ *ᵥ x :=
      Continuous.matrix_mulVec continuous_const continuous_id
    refine (Real.continuous_rpow_const hq).comp ?_
    fun_prop
  have hInt : Integrable (fun x => (∑ i, (r i + c * (Λ *ᵥ x) i) ^ 2) ^ q) (stdGauss ι) := by
    refine (hI.const_mul (n ^ q * Real.exp C0)).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt x
  refine ⟨hInt, ?_⟩
  calc ∫ x, (∑ i, (r i + c * (Λ *ᵥ x) i) ^ 2) ^ q ∂(stdGauss ι)
      ≤ ∫ x, n ^ q * Real.exp C0 *
          Real.exp (b ⬝ᵥ (Λ *ᵥ x) + s / 2 * ∑ i, (Λ *ᵥ x) i ^ 2) ∂(stdGauss ι) :=
        integral_mono hInt (hI.const_mul _) hpt
    _ = n ^ q * Real.exp C0 *
          ∫ x, Real.exp (b ⬝ᵥ (Λ *ᵥ x) + s / 2 * ∑ i, (Λ *ᵥ x) i ^ 2) ∂(stdGauss ι) :=
        integral_const_mul _ _
    _ ≤ n ^ q * Real.exp C0 *
          Real.exp (s * ∑ i, ∑ j, Λ i j ^ 2 + ‖Λ‖ ^ 2 * ∑ i, b i ^ 2) := by
        gcongr
    _ = n ^ q * Real.exp (C0 + (s * ∑ i, ∑ j, Λ i j ^ 2 + ‖Λ‖ ^ 2 * ∑ i, b i ^ 2)) := by
        rw [Real.exp_add C0, mul_assoc]
    _ ≤ n ^ q * Real.exp D := by gcongr
    _ = Real.exp D * n ^ q := mul_comm _ _

/-! ### The decomposition `M = R_E + iηB_E - g⁻¹ B_E (1 ⊗ V)` -/

/-- `1 ⊗ V` commutes with `S_E`. -/
private lemma oneStep_kron_comm_freeConj (W : ℕ) (E : ℝ) (V : Matrix (Fin W) (Fin W) ℂ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) * freeConj W E =
      freeConj W E * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) := by
  unfold freeConj
  rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]

/-- `M = R_E + iη B_E - g⁻¹ B_E (1 ⊗ V)` for `|E| < 2`, proof of Lemma 7.2
[uvs:lem:transfer-moments]. -/
private lemma oneStep_transferConj_eq {W : ℕ} {E : ℝ} (hE : |E| < 2) (g η : ℝ)
    (V : Matrix (Fin W) (Fin W) ℂ) :
    transferConj g E η V = freeRot W E + ((η : ℂ) * Complex.I) • freeShear W E -
      ((g : ℂ)⁻¹) • (freeShear W E * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)) := by
  rw [transferConj, inv_freeConj_mul_transferMat_mul hE]
  have hP : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V =
      (!![1, 0; 0, 0] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hX : (freeConj W E)⁻¹ * ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) *
      freeConj W E = freeShear W E * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) := by
    rw [hP, freeShear, Matrix.mul_assoc, Matrix.mul_assoc, oneStep_kron_comm_freeConj,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [hX]

/-- `M v = w + g⁻¹ ξ` with `w = R_E v + iη B_E v` and `ξ = -B_E (1 ⊗ V) v`. -/
private lemma oneStep_transferConj_mulVec {W : ℕ} {E : ℝ} (hE : |E| < 2) (g η : ℝ)
    (V : Matrix (Fin W) (Fin W) ℂ) (v : Fin 2 × Fin W → ℂ) :
    transferConj g E η V *ᵥ v =
      (freeRot W E *ᵥ v + ((η : ℂ) * Complex.I) • (freeShear W E *ᵥ v)) +
        ((g⁻¹ : ℝ) : ℂ) • (-(freeShear W E *ᵥ (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) *ᵥ v))) := by
  rw [oneStep_transferConj_eq hE, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, smul_neg, Complex.ofReal_inv, sub_eq_add_neg]

/-- `Σ_p |z_p|² = ‖z‖²` in `EuclideanSpace`. -/
private lemma oneStep_sum_sq_eq {n : Type*} [Fintype n] (z : n → ℂ) :
    ∑ p, ‖z p‖ ^ 2 = ‖(WithLp.toLp 2 z : EuclideanSpace ℂ n)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]

/-- `‖A z‖ ≤ ‖A‖ ‖z‖` in `EuclideanSpace`. -/
private lemma oneStep_norm_toLp_mulVec_le {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (z : n → ℂ) :
    ‖(WithLp.toLp 2 (A *ᵥ z) : EuclideanSpace ℂ m)‖ ≤
      ‖A‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℂ n)‖ :=
  A.l2_opNorm_mulVec (WithLp.toLp 2 z)

/-- `‖R_E v + iη B_E v‖² ≤ (1 + K|η|)² ‖v‖²` for `‖B_E‖ ≤ K`. -/
private lemma oneStep_det_le {W : ℕ} (E η : ℝ) {K : ℝ} (hB : ‖freeShear W E‖ ≤ K)
    (v : Fin 2 × Fin W → ℂ) :
    ∑ p, ‖(freeRot W E *ᵥ v + ((η : ℂ) * Complex.I) • (freeShear W E *ᵥ v)) p‖ ^ 2 ≤
      (1 + K * |η|) ^ 2 * ∑ p, ‖v p‖ ^ 2 := by
  have hR := oneStep_norm_le_one (freeRot_mem_unitaryGroup W E)
  rw [oneStep_sum_sq_eq, oneStep_sum_sq_eq, ← mul_pow]
  set e : EuclideanSpace ℂ (Fin 2 × Fin W) := WithLp.toLp 2 v
  have h1 := oneStep_norm_toLp_mulVec_le (freeRot W E) v
  have h2 := oneStep_norm_toLp_mulVec_le (freeShear W E) v
  have hη : ‖(η : ℂ) * Complex.I‖ = |η| := by simp
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [WithLp.toLp_add, WithLp.toLp_smul]
  calc _ ≤ ‖(WithLp.toLp 2 (freeRot W E *ᵥ v) : EuclideanSpace ℂ (Fin 2 × Fin W))‖ +
        ‖((η : ℂ) * Complex.I) • (WithLp.toLp 2 (freeShear W E *ᵥ v) :
          EuclideanSpace ℂ (Fin 2 × Fin W))‖ := norm_add_le _ _
    _ ≤ 1 * ‖e‖ + |η| * (K * ‖e‖) := by
        rw [norm_smul, hη]
        gcongr
        · exact h1.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
        · exact h2.trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
    _ = (1 + K * |η|) * ‖e‖ := by ring

/-! ### The one-step moment bound -/

/-- (7.2) [uvs:eq:one-step-moment] with `q = W`, for a block of onsite variance `t ∈ [0, 1]`
and a deterministic vector: `E‖M v‖^W ≤ e^{A W (|η| + g⁻²)} ‖v‖^W`. -/
theorem one_step_moment (κ : ℝ) (hκ : 0 < κ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (W L : ℕ) (a : Fin L) (g : ℝ), 2 / Real.sqrt κ ≤ g → ∀ E η t : ℝ,
      |E| ≤ 2 - κ → |η| ≤ 1 → 0 ≤ t → t ≤ 1 → ∀ v : Fin 2 × Fin W → ℂ,
      Integrable (fun ω => (∑ p, ‖(transferConj g E η (((Real.sqrt t : ℝ) : ℂ) •
          gueBlock W L ω a) *ᵥ v) p‖ ^ 2) ^ ((W : ℝ) / 2)) (μ W L) ∧
      ∫ ω, (∑ p, ‖(transferConj g E η (((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω a) *ᵥ v) p‖ ^ 2)
          ^ ((W : ℝ) / 2) ∂(μ W L) ≤
        Real.exp (A * W * (|η| + g⁻¹ ^ 2)) * (∑ p, ‖v p‖ ^ 2) ^ ((W : ℝ) / 2) := by
  set K := Real.sqrt (2 / κ) with hK_def
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hK2 : K ^ 2 = 2 / κ := Real.sq_sqrt (by positivity)
  refine ⟨K + K ^ 2 / 2 + K ^ 2 * (1 + (1 + K) ^ 2), by positivity, ?_⟩
  intro W L a g hg E η t hE hη ht0 ht1 v
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hg0 : 0 < g := lt_of_lt_of_le (by positivity) hg
  have hgc : g⁻¹ ^ 2 * K ^ 2 ≤ 1 / 2 := by
    have h1 : (2 / Real.sqrt κ) ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ (by positivity) hg 2
    rw [div_pow, Real.sq_sqrt hκ.le] at h1
    rw [hK2, inv_pow, ← div_eq_inv_mul, div_div, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hκ] at h1
    linarith
  have hE2 : |E| < 2 := by linarith [abs_nonneg E]
  have hB : ‖freeShear W E‖ ≤ K := norm_freeShear_le W hκ hE
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp
  set n := ∑ p, ‖v p‖ ^ 2 with hn_def
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rcases (show 0 ≤ n by positivity).eq_or_lt with hn0 | hn
  · have hv : v = 0 := by
      funext p
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by positivity)).mp hn0.symm p
        (Finset.mem_univ p)
      simpa using this
    subst hv
    have hW2 : (W : ℝ) / 2 ≠ 0 := by positivity
    have h0 : ∀ M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
        (∑ p, ‖(M *ᵥ (0 : Fin 2 × Fin W → ℂ)) p‖ ^ 2) ^ ((W : ℝ) / 2) = 0 := by
      intro M
      simp [Real.zero_rpow hW2]
    simp_rw [h0]
    refine ⟨integrable_zero _ _ _, ?_⟩
    rw [integral_zero]
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hn0.le _)
  set w := freeRot W E *ᵥ v + ((η : ℂ) * Complex.I) • (freeShear W E *ᵥ v) with hw_def
  set Λ := LinearMap.toMatrix' (oneStep_xi W L a t (freeShear W E) v) with hΛ_def
  set r := oneStep_re w with hr_def
  have hpt : ∀ ω : Ω W L, ∑ p, ‖(transferConj g E η (((Real.sqrt t : ℝ) : ℂ) •
      gueBlock W L ω a) *ᵥ v) p‖ ^ 2 = ∑ i, (r i + g⁻¹ * (Λ *ᵥ ω) i) ^ 2 := by
    intro ω
    rw [oneStep_transferConj_mulVec hE2, ← oneStep_sum_sq_re, oneStep_re_add, oneStep_re_smul,
      hΛ_def, LinearMap.toMatrix'_mulVec]
    rfl
  have hfun : (fun ω : Ω W L => (∑ p, ‖(transferConj g E η (((Real.sqrt t : ℝ) : ℂ) •
      gueBlock W L ω a) *ᵥ v) p‖ ^ 2) ^ ((W : ℝ) / 2)) =
      fun ω => (∑ i, (r i + g⁻¹ * (Λ *ᵥ ω) i) ^ 2) ^ ((W : ℝ) / 2) := by
    funext ω
    rw [hpt ω]
  rw [hfun]
  have hΛop := oneStep_xi_opNorm W L a ht0 hB v
  have hΛhs := oneStep_xi_hs W L hW a ht0 hB v
  have hR : ∑ i, r i ^ 2 ≤ (1 + K * |η|) ^ 2 * n := by
    rw [hr_def, oneStep_sum_sq_re]
    exact oneStep_det_le E η hB v
  rw [← hΛ_def] at hΛop hΛhs
  -- normalized quantities
  set ρ := (∑ i, r i ^ 2) / n with hρ_def
  set ℓ := ‖Λ‖ ^ 2 * W / n with hℓ_def
  set h := (∑ i, ∑ j, Λ i j ^ 2) / n with hh_def
  have hρ : ρ ≤ (1 + K * |η|) ^ 2 := (div_le_iff₀ hn).mpr hR
  have hρ0 : 0 ≤ ρ := by positivity
  have hℓ0 : 0 ≤ ℓ := by positivity
  have hℓ : ℓ ≤ K ^ 2 * t := by
    rw [hℓ_def, div_le_iff₀ hn]
    calc ‖Λ‖ ^ 2 * W ≤ K ^ 2 * t * (W : ℝ)⁻¹ * n * W := by gcongr
      _ = K ^ 2 * t * n := by field_simp
  have hh : h ≤ K ^ 2 * t := by
    rw [hh_def, div_le_iff₀ hn]
    exact hΛhs
  have hs_eq : 2 * ((W : ℝ) / 2) * g⁻¹ ^ 2 / n * ‖Λ‖ ^ 2 = g⁻¹ ^ 2 * ℓ := by
    rw [hℓ_def]; field_simp
  have heq : (W : ℝ) / 2 * ((∑ i, r i ^ 2) / n - 1) + (2 * ((W : ℝ) / 2) * g⁻¹ ^ 2 / n *
      ∑ i, ∑ j, Λ i j ^ 2 + ‖Λ‖ ^ 2 * ∑ i, (2 * ((W : ℝ) / 2) * g⁻¹ / n * r i) ^ 2) =
      (W : ℝ) / 2 * (ρ - 1) + W * g⁻¹ ^ 2 * h + ℓ * (W * g⁻¹ ^ 2) * ρ := by
    simp only [mul_pow, ← Finset.mul_sum]
    rw [hρ_def, hℓ_def, hh_def]
    field_simp
    ring
  clear_value ρ ℓ h
  have hη2 : η ^ 2 ≤ |η| := by
    rw [← sq_abs, sq]
    exact mul_le_of_le_one_left (abs_nonneg η) hη
  have hKη : (1 + K * |η|) ^ 2 ≤ (1 + K) ^ 2 := by
    have : K * |η| ≤ K := mul_le_of_le_one_right hK0 hη
    gcongr
  have hc0 : 0 ≤ g⁻¹ ^ 2 := by positivity
  have hKt : K ^ 2 * t ≤ K ^ 2 := mul_le_of_le_one_right (sq_nonneg K) ht1
  refine oneStep_core Λ r (c := g⁻¹) (n := n) (q := (W : ℝ) / 2) hn (by positivity) ?_ ?_
  · rw [hs_eq]
    calc g⁻¹ ^ 2 * ℓ ≤ g⁻¹ ^ 2 * K ^ 2 := mul_le_mul_of_nonneg_left (hℓ.trans hKt) hc0
      _ ≤ 1 / 2 := hgc
  · rw [heq]
    set A := K + K ^ 2 / 2 + K ^ 2 * (1 + (1 + K) ^ 2) with hA_def
    have t1 : (W : ℝ) / 2 * (ρ - 1) ≤ W * ((K + K ^ 2 / 2) * |η|) := by
      have e1 : (1 + K * |η|) ^ 2 = 1 + 2 * K * |η| + K ^ 2 * η ^ 2 := by
        rw [add_sq, mul_pow, sq_abs]; ring
      have e2 : K ^ 2 * η ^ 2 ≤ K ^ 2 * |η| := mul_le_mul_of_nonneg_left hη2 (sq_nonneg K)
      have e3 : ρ - 1 ≤ 2 * ((K + K ^ 2 / 2) * |η|) := by linarith
      calc (W : ℝ) / 2 * (ρ - 1) ≤ (W : ℝ) / 2 * (2 * ((K + K ^ 2 / 2) * |η|)) :=
            mul_le_mul_of_nonneg_left e3 (by positivity)
        _ = W * ((K + K ^ 2 / 2) * |η|) := by ring
    have t2 : W * g⁻¹ ^ 2 * h ≤ W * g⁻¹ ^ 2 * K ^ 2 :=
      mul_le_mul_of_nonneg_left (hh.trans hKt) (mul_nonneg hW'.le hc0)
    have t3 : ℓ * (W * g⁻¹ ^ 2) * ρ ≤ W * g⁻¹ ^ 2 * (K ^ 2 * (1 + K) ^ 2) := by
      have hρ' : ρ ≤ (1 + K) ^ 2 := hρ.trans hKη
      have e1 := mul_le_mul (hℓ.trans hKt) hρ' hρ0 (sq_nonneg K)
      have e2 := mul_le_mul_of_nonneg_left e1 (mul_nonneg hW'.le hc0)
      calc ℓ * (W * g⁻¹ ^ 2) * ρ = W * g⁻¹ ^ 2 * (ℓ * ρ) := by ring
        _ ≤ _ := e2
    have hA1 : K + K ^ 2 / 2 ≤ A := by
      rw [hA_def]
      have : 0 ≤ K ^ 2 * (1 + (1 + K) ^ 2) := by positivity
      linarith
    have hA2 : K ^ 2 + K ^ 2 * (1 + K) ^ 2 ≤ A := by
      rw [hA_def]
      have : 0 ≤ K := hK0
      have : 0 ≤ K ^ 2 / 2 := by positivity
      linarith
    have f1 : W * ((K + K ^ 2 / 2) * |η|) ≤ W * (A * |η|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA1 (abs_nonneg η)) hW'.le
    have f2 : W * g⁻¹ ^ 2 * (K ^ 2 + K ^ 2 * (1 + K) ^ 2) ≤ W * g⁻¹ ^ 2 * A :=
      mul_le_mul_of_nonneg_left hA2 (mul_nonneg hW'.le hc0)
    have f3 : A * W * (|η| + g⁻¹ ^ 2) = W * (A * |η|) + W * g⁻¹ ^ 2 * A := by ring
    have f4 : W * g⁻¹ ^ 2 * (K ^ 2 + K ^ 2 * (1 + K) ^ 2) =
        W * g⁻¹ ^ 2 * K ^ 2 + W * g⁻¹ ^ 2 * (K ^ 2 * (1 + K) ^ 2) := by ring
    rw [f3]
    linarith

/-! ### The inverse adjoint `M^{-*}` -/

/-- The sign matrix `diag(-1, 1) ⊗ I_W`. -/
def signKron (W : ℕ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  !![-1, 0; 0, 1] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)

/-- `[[1, 1], [a, b]] diag(-1, 1) [[1, 1], [a, b]]^* = [[0, a - b], [b - a, 0]]` for `b = ā`. -/
private lemma oneStep_block_sign (a b : ℂ) (hab : star a = b) (hba : star b = a) :
    (!![1, 1; a, b] : Matrix (Fin 2) (Fin 2) ℂ) * !![-1, 0; 0, 1] * !![1, 1; a, b]ᴴ =
      !![0, a - b; b - a, 0] := by
  have hH : (!![1, 1; a, b] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = !![1, b; 1, a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, hab, hba]
  have hab' : a * b = b * a := mul_comm a b
  rw [hH, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- `S_E diag(-1, 1) S_E^* = [[0, i], [-i, 0]] ⊗ I_W` for `|E| < 2`. -/
lemma freeConj_mul_sign_mul_conjTranspose {W : ℕ} {E : ℝ} (hE : |E| < 2) :
    freeConj W E * signKron W * (freeConj W E)ᴴ =
      !![0, Complex.I; -Complex.I, 0] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
  have h := abs_lt.mp hE
  have hs : 0 < Real.sin (freeAngle E) :=
    Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr (by linarith))
      (Real.arccos_lt_pi.mpr (by linarith))
  have hcc : (((Real.sqrt (2 * Real.sin (freeAngle E)))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (2 * Real.sin (freeAngle E)))⁻¹ : ℝ) : ℂ) =
      (2 * (Real.sin (freeAngle E) : ℂ))⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  have hsne : (Real.sin (freeAngle E) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hsub : Complex.exp (freeAngle E * Complex.I) - Complex.exp (-(freeAngle E * Complex.I)) =
      2 * (Real.sin (freeAngle E) : ℂ) * Complex.I := by
    rw [← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_sin]
    ring
  have hstar : star (Complex.exp (freeAngle E * Complex.I)) =
      Complex.exp (-(freeAngle E * Complex.I)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    simp
  have hstar' : star (Complex.exp (-(freeAngle E * Complex.I))) =
      Complex.exp (freeAngle E * Complex.I) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    simp
  unfold freeConj signKron
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Complex.star_def, Complex.conj_ofReal]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hcc, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one,
    ← Matrix.smul_kronecker, oneStep_block_sign _ _ hstar hstar']
  congr 1
  have hneg : Complex.exp (-(freeAngle E * Complex.I)) - Complex.exp (freeAngle E * Complex.I) =
      -(2 * (Real.sin (freeAngle E) : ℂ) * Complex.I) := by
    rw [← hsub]; ring
  rw [hsub, hneg]
  have hsne' : Complex.sin (freeAngle E) ≠ 0 := by rw [← Complex.ofReal_sin]; exact hsne
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp


/-- `T(z) J T(z')^* = J` for `J = [[0, i], [-i, 0]] ⊗ I_W`, `z̄' = z` and Hermitian `V`. -/
lemma transferMat_mul_symp_mul_conjTranspose {W : ℕ} (g : ℝ) {z z' : ℂ} (hz : star z' = z)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    transferMat g z V * (!![0, Complex.I; -Complex.I, 0] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
        (transferMat g z' V)ᴴ =
      !![0, Complex.I; -Complex.I, 0] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
  have hA : (!![z', -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = !![z, 1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, hz]
  have hP : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  have hg : star ((g : ℂ)⁻¹) = (g : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hT' : (transferMat g z' V)ᴴ = !![z, 1; -1, 0] ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) -
      ((g : ℂ)⁻¹) • (!![1, 0; 0, 0] ⊗ₖ V) := by
    unfold transferMat transferFree
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_kronecker, hA, hP, hV.eq, Matrix.conjTranspose_one, hg]
  have h1 : (!![z, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, Complex.I; -Complex.I, 0] *
      !![z, 1; -1, 0] = !![0, Complex.I; -Complex.I, 0] := by
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]
  have h2 : (!![z, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, Complex.I; -Complex.I, 0] *
      !![1, 0; 0, 0] = !![Complex.I, 0; 0, 0] := by
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h3 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, Complex.I; -Complex.I, 0] *
      !![z, 1; -1, 0] = (-1 : ℂ) • !![Complex.I, 0; 0, 0] := by
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h4 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, Complex.I; -Complex.I, 0] *
      !![1, 0; 0, 0] = 0 := by
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hT']
  unfold transferMat transferFree
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, h1, h2, h3, h4,
    Matrix.smul_kronecker, Matrix.zero_kronecker, smul_zero, smul_smul]
  module

/-- `(M^{-1})^* = D M(-η) D` with `D = diag(-1, 1) ⊗ I_W`, for `|E| < 2` and Hermitian `V`;
here `M(η) = S_E⁻¹ T(E + iη) S_E`. The factors `M_j^{-*}` of the proof of Lemma 7.2
[uvs:lem:transfer-moments] thus have the structure of `M_j` at `-η`. -/
private lemma oneStep_inv_conjTranspose {W : ℕ} {E : ℝ} (hE : |E| < 2) (g η : ℝ)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    ((transferConj g E η V)⁻¹)ᴴ = signKron W * transferConj g E (-η) V * signKron W := by
  have hU := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_freeConj W hE)
  have hD : signKron W * signKron W = 1 := by
    unfold signKron
    have h22 : (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) * !![-1, 0; 0, 1] = 1 := by
      rw [Matrix.mul_fin_two, Matrix.one_fin_two]
      norm_num
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, h22, Matrix.one_kronecker_one]
  have hDH : (signKron W)ᴴ = signKron W := by
    unfold signKron
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  have hz : star ((↑E : ℂ) + ↑(-η) * Complex.I) = ↑E + ↑η * Complex.I := by
    simp [Complex.conj_ofReal]
  have hsymp := transferMat_mul_symp_mul_conjTranspose g hz hV (W := W)
  have hSDS := freeConj_mul_sign_mul_conjTranspose (W := W) hE
  have hmul : transferConj g E η V *
      (signKron W * (transferConj g E (-η) V)ᴴ * signKron W) = 1 := by
    set S := freeConj W E
    set D := signKron W
    set T := transferMat g (↑E + ↑η * Complex.I) V
    set T' := transferMat g (↑E + ↑(-η) * Complex.I) V
    have e1 : transferConj g E η V = S⁻¹ * T * S := rfl
    have e2 : transferConj g E (-η) V = S⁻¹ * T' * S := rfl
    rw [e1, e2, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc S⁻¹ * T * S * (D * (Sᴴ * (T'ᴴ * S⁻¹ᴴ)) * D)
        = S⁻¹ * (T * (S * D * Sᴴ) * T'ᴴ) * S⁻¹ᴴ * D := by
          simp only [Matrix.mul_assoc]
      _ = S⁻¹ * (S * D * Sᴴ) * S⁻¹ᴴ * D := by rw [hSDS, hsymp]
      _ = (S⁻¹ * S) * D * (S⁻¹ * S)ᴴ * D := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [Matrix.nonsing_inv_mul _ hU, Matrix.conjTranspose_one, Matrix.one_mul,
            Matrix.mul_one, hD]
  rw [Matrix.inv_eq_right_inv hmul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hDH, Matrix.mul_assoc]

/-- `‖D u‖ = ‖u‖` for the sign matrix `D`. -/
private lemma oneStep_sum_sq_sign {W : ℕ} (u : Fin 2 × Fin W → ℂ) :
    ∑ p, ‖(signKron W *ᵥ u) p‖ ^ 2 = ∑ p, ‖u p‖ ^ 2 := by
  have h : ∀ (i : Fin 2) (α : Fin W), ‖(signKron W *ᵥ u) (i, α)‖ = ‖u (i, α)‖ := by
    intro i α
    fin_cases i <;>
      simp [signKron, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply,
        Fin.sum_univ_two]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type (f := fun p => ‖u p‖ ^ 2)]
  simp only [h]


/-- (7.2) [uvs:eq:one-step-moment] for the inverse adjoints `M^{-*}`, proof of Lemma 7.2
[uvs:lem:transfer-moments]. -/
theorem one_step_moment_inv (κ : ℝ) (hκ : 0 < κ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (W L : ℕ) (a : Fin L) (g : ℝ), 2 / Real.sqrt κ ≤ g → ∀ E η t : ℝ,
      |E| ≤ 2 - κ → |η| ≤ 1 → 0 ≤ t → t ≤ 1 → ∀ v : Fin 2 × Fin W → ℂ,
      Integrable (fun ω => (∑ p, ‖(((transferConj g E η (((Real.sqrt t : ℝ) : ℂ) •
          gueBlock W L ω a))⁻¹)ᴴ *ᵥ v) p‖ ^ 2) ^ ((W : ℝ) / 2)) (μ W L) ∧
      ∫ ω, (∑ p, ‖(((transferConj g E η (((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω a))⁻¹)ᴴ *ᵥ v)
          p‖ ^ 2) ^ ((W : ℝ) / 2) ∂(μ W L) ≤
        Real.exp (A * W * (|η| + g⁻¹ ^ 2)) * (∑ p, ‖v p‖ ^ 2) ^ ((W : ℝ) / 2) := by
  obtain ⟨A, hA, h⟩ := one_step_moment κ hκ
  refine ⟨A, hA, ?_⟩
  intro W L a g hg E η t hE hη ht0 ht1 v
  have hE2 : |E| < 2 := by linarith [abs_nonneg E]
  have hV : ∀ ω : Ω W L, (((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω a).IsHermitian := by
    intro ω
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, (gueBlock_isHermitian W L ω a).eq, Complex.star_def,
      Complex.conj_ofReal]
  have key : ∀ ω : Ω W L, ∑ p, ‖(((transferConj g E η (((Real.sqrt t : ℝ) : ℂ) •
      gueBlock W L ω a))⁻¹)ᴴ *ᵥ v) p‖ ^ 2 = ∑ p, ‖(transferConj g E (-η)
        (((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω a) *ᵥ (signKron W *ᵥ v)) p‖ ^ 2 := by
    intro ω
    rw [oneStep_inv_conjTranspose hE2 g η (hV ω), ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      oneStep_sum_sq_sign]
  simp_rw [key]
  have := h W L a g hg E (-η) t hE (by rwa [abs_neg]) ht0 ht1 (signKron W *ᵥ v)
  rwa [oneStep_sum_sq_sign, abs_neg] at this

end LSBA
