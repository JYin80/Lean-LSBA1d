import LSBA.Upper.LiftSize

/-!
# The Hermitian lift away from zero energy

The minimum-norm lift `X = √2 𝒜* Γ⁻¹ M`, `Γ = 𝒜 𝒜*`, of (10.30) [lg:eq:minimal-lift], in
real coordinates: `𝒜*` is the transpose of the real matrix of `𝒜` in the basis `ι_i H_α` of
Hermitian arrays, and `Γ` is inverted on the algebra (10.3) [eq:c-Lie] through the least-squares
inverse of `𝒜*` stacked with the orthogonal projection onto the complement of the algebra.
Where `S_W(G) ≥ c₁ > 0`, `𝒜(X) = √2 M` for every target `M` of the algebra; for `g ≥ 1`,
`|E| ≤ E₀`, `max_i ‖V_i‖ ≤ K₁`, the coercivity (10.29) [lg:eq:coercivity] `Γ ≥ c g⁻⁴` holds, and
for Hermitian `M` and `E ≠ 0` the bounds (10.27) [lg:eq:hermitian-blocks], (10.28)
[lg:eq:hermitian-dual] and (10.31) [lg:eq:hermlift] hold with the explicit dependence
`C (1 + |E|⁻¹)` in place of `C_{κ₁}` (Section 10 [sec:compact-proof]).
-/

open Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The real matrix of `𝒜` from the coefficients in the basis `ι_i H_α` of Hermitian arrays to
the coordinates `reCoord` (Section 10 [sec:compact-proof]). -/
def prodDiffMat {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W)) (Fin q × Fin W × Fin W) ℝ :=
  Matrix.of fun p r => reCoord (prodDiff g z V (Pi.single r.1 (hermBasis W (r.2.1, r.2.2)))) p

/-- The orthogonal projection onto the complement of the algebra (10.3) [eq:c-Lie]:
`M ↦ J_ph N_h + (Im Tr(J_ph N_s) / (2W)) i I` with `N = J_ph M = N_h + N_s` (Hermitian and
skew-Hermitian parts). -/
def lieOmegaPerp {W : ℕ} (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  phJ W * ((1 / 2 : ℂ) • (phJ W * M + (phJ W * M)ᴴ)) +
    (((phJ W * ((1 / 2 : ℂ) • (phJ W * M - (phJ W * M)ᴴ))).trace.im / (2 * W) : ℝ) : ℂ) •
      (Complex.I • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))

/-- `𝒜*` stacked with the projection onto the complement of the algebra, in real coordinates;
its Gram matrix is `𝒜 𝒜* + Π_⊥`, equal to `Γ` on the algebra. -/
def hermLiftMat {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    Matrix ((Fin q × Fin W × Fin W) ⊕ (Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W)))
      (Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W)) ℝ :=
  Matrix.fromRows (prodDiffMat g z V)ᵀ
    (Matrix.of fun p r => reCoord (lieOmegaPerp (ofReCoord (Pi.single r 1) :
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) p)

/-- The Hermitian lift `X = √2 𝒜* Γ⁻¹ M` of (10.30) [lg:eq:minimal-lift], as a Hermitian array. -/
def hermLiftField {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Fin q → Matrix (Fin W) (Fin W) ℂ :=
  fun i => ∑ k : Fin W × Fin W,
    ((Real.sqrt 2 * ((lsqInv (hermLiftMat g z V))ᵀ *ᵥ reCoord M) (Sum.inl (i, k.1, k.2)) : ℝ) :
      ℂ) • hermBasis W k

section LiftHermitianAux

/-- `‖A‖² ≥ 0`. -/
private lemma LiftHermitian_hsSq_nonneg {k l : Type*} [Fintype k] [Fintype l]
    (A : Matrix k l ℂ) : 0 ≤ hsSq A := by
  unfold hsSq; positivity

/-- `‖A + B‖² ≤ 2‖A‖² + 2‖B‖²`. -/
private lemma LiftHermitian_hsSq_add_le {k l : Type*} [Fintype k] [Fintype l]
    (A B : Matrix k l ℂ) : hsSq (A + B) ≤ 2 * hsSq A + 2 * hsSq B := by
  unfold hsSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have h := norm_add_le (A a b) (B a b)
  have h0 : 0 ≤ ‖A a b + B a b‖ := norm_nonneg _
  simp only [Matrix.add_apply]
  nlinarith [sq_nonneg (‖A a b‖ - ‖B a b‖), norm_nonneg (A a b), norm_nonneg (B a b)]

/-- `‖A - B‖² ≤ 2‖A‖² + 2‖B‖²`. -/
private lemma LiftHermitian_hsSq_sub_le {k l : Type*} [Fintype k] [Fintype l]
    (A B : Matrix k l ℂ) : hsSq (A - B) ≤ 2 * hsSq A + 2 * hsSq B := by
  have h : hsSq (-B) = hsSq B := by simp [hsSq]
  rw [sub_eq_add_neg, ← h]
  exact LiftHermitian_hsSq_add_le A (-B)

/-- `‖A*‖ = ‖A‖`. -/
private lemma LiftHermitian_hsSq_conjTranspose {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    hsSq Aᴴ = hsSq A := by
  simp only [hsSq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

/-- `‖c A‖² = |c|² ‖A‖²`. -/
private lemma LiftHermitian_hsSq_smul {k l : Type*} [Fintype k] [Fintype l] (c : ℂ)
    (A : Matrix k l ℂ) : hsSq (c • A) = ‖c‖ ^ 2 * hsSq A := by
  simp [hsSq, mul_pow, Finset.mul_sum]

/-- `‖A B‖² ≤ |A|²_op ‖B‖²`, column by column. -/
private lemma LiftHermitian_hsSq_mul_le {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    hsSq (A * B) ≤ ‖A‖ ^ 2 * hsSq B := by
  have hcol : ∀ b : n, ∑ a, ‖(A * B) a b‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ a, ‖B a b‖ ^ 2 := by
    intro b
    have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 (fun a => B a b))
    have h1 : ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ (fun a => B a b))‖ ^ 2 =
        ∑ a, ‖(A * B) a b‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      rfl
    have h2 : ‖(WithLp.toLp 2 (fun a => B a b) : EuclideanSpace ℂ n)‖ ^ 2 =
        ∑ a, ‖B a b‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    have h0 : 0 ≤ ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ (fun a => B a b))‖ := norm_nonneg _
    rw [← h1, ← h2, ← mul_pow]
    exact pow_le_pow_left₀ h0 h 2
  unfold hsSq
  rw [Finset.sum_comm, Finset.sum_comm (f := fun a b => ‖B a b‖ ^ 2), Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => hcol b

/-- `‖B A‖² ≤ |A|²_op ‖B‖²`. -/
private lemma LiftHermitian_hsSq_mul_le' {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    hsSq (B * A) ≤ ‖A‖ ^ 2 * hsSq B := by
  rw [← LiftHermitian_hsSq_conjTranspose, Matrix.conjTranspose_mul,
    ← Matrix.l2_opNorm_conjTranspose A, ← LiftHermitian_hsSq_conjTranspose B]
  exact LiftHermitian_hsSq_mul_le _ _

/-- `‖V P + P* V‖² ≤ 4 |V|²_op ‖P‖²`. -/
private lemma LiftHermitian_hsSq_sym_le {n : Type*} [Fintype n] (V P : Matrix n n ℂ) :
    hsSq (V * P + Pᴴ * V) ≤ 4 * ‖V‖ ^ 2 * hsSq P := by
  have h1 := LiftHermitian_hsSq_mul_le V P
  have h2 := LiftHermitian_hsSq_mul_le' V Pᴴ
  rw [LiftHermitian_hsSq_conjTranspose] at h2
  have h3 := LiftHermitian_hsSq_add_le (V * P) (Pᴴ * V)
  linarith

/-- `‖A‖ = 0` implies `A = 0`. -/
private lemma LiftHermitian_eq_zero_of_hsSq {k l : Type*} [Fintype k] [Fintype l]
    {A : Matrix k l ℂ} (h : hsSq A = 0) : A = 0 := by
  unfold hsSq at h
  ext a b
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).1 h a
    (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by positivity)).1 h1 b
    (Finset.mem_univ _)
  simpa using h2

/-- `⟨A, B⟩ = ⟨B, A⟩`. -/
private lemma LiftHermitian_hsInner_comm {k l : Type*} [Fintype k] [Fintype l]
    (A B : Matrix k l ℂ) : hsInner A B = hsInner B A := by
  rw [← (hsInner_reCoord A B 0).2.2.2.2, ← (hsInner_reCoord B A 0).2.2.2.2]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

/-- `⟨r A, B⟩ = r ⟨A, B⟩` for real `r`. -/
private lemma LiftHermitian_hsInner_smul_left {k l : Type*} [Fintype k] [Fintype l] (r : ℝ)
    (A B : Matrix k l ℂ) : hsInner ((r : ℂ) • A) B = r * hsInner A B := by
  simp only [(hsInner_reCoord _ _ 0).1, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- `‖A + B‖² = ‖A‖² + 2⟨A, B⟩ + ‖B‖²`. -/
private lemma LiftHermitian_hsSq_add {k l : Type*} [Fintype k] [Fintype l] (A B : Matrix k l ℂ) :
    hsSq (A + B) = hsSq A + 2 * hsInner A B + hsSq B := by
  have h := LiftHermitian_hsInner_comm B A
  rw [← (hsInner_reCoord (A + B) (A + B) 0).2.1, ← (hsInner_reCoord A A 0).2.1,
    ← (hsInner_reCoord B B 0).2.1]
  simp only [(hsInner_reCoord _ _ 0).1] at h ⊢
  simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add,
    Complex.add_re]
  linarith

/-- Cauchy–Schwarz: `⟨A, B⟩² ≤ ‖A‖² ‖B‖²`. -/
private lemma LiftHermitian_hsInner_sq_le {k l : Type*} [Fintype k] [Fintype l]
    (A B : Matrix k l ℂ) : hsInner A B ^ 2 ≤ hsSq A * hsSq B := by
  rw [← (hsInner_reCoord A B 0).2.2.2.2, ← (hsInner_reCoord A A 0).2.1,
    ← (hsInner_reCoord B B 0).2.1, ← (hsInner_reCoord A A 0).2.2.2.2,
    ← (hsInner_reCoord B B 0).2.2.2.2]
  simpa [sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (reCoord A) (reCoord B)

/-- `‖Σ_k c_k H_k‖² = Σ_k c_k²` for real `c_k`. -/
private lemma LiftHermitian_hsSq_basis (W : ℕ) (c : Fin W × Fin W → ℝ) :
    hsSq (∑ k, ((c k : ℝ) : ℂ) • hermBasis W k) = ∑ k, c k ^ 2 := by
  have hl : ∀ (A : Fin W × Fin W → Matrix (Fin W) (Fin W) ℂ) (B : Matrix (Fin W) (Fin W) ℂ),
      hsInner (∑ x, ((c x : ℝ) : ℂ) • A x) B = ∑ x, c x * hsInner (A x) B := by
    intro A B
    simp only [(hsInner_reCoord _ _ 0).1, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      Complex.star_def, Complex.conj_ofReal, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
      Complex.re_sum, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hr : ∀ (A : Matrix (Fin W) (Fin W) ℂ) (B : Fin W × Fin W → Matrix (Fin W) (Fin W) ℂ),
      hsInner A (∑ x, ((c x : ℝ) : ℂ) • B x) = ∑ x, c x * hsInner A (B x) := by
    intro A B
    simp only [(hsInner_reCoord _ _ 0).1, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum,
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hb : ∀ k l, hsInner (hermBasis W k) (hermBasis W l) = if k = l then 1 else 0 := by
    intro k l
    rw [(hsInner_reCoord _ _ 0).1, (hermBasis_isHermitian W k).eq, trace_hermBasis_mul]
    split_ifs <;> simp
  rw [← (hsInner_reCoord (∑ k, ((c k : ℝ) : ℂ) • hermBasis W k) 0 0).2.1, hl]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hr]
  simp [hb, sq]

/-- Parseval for a Hermitian matrix: `Σ_k ⟨H_k, A⟩² = ‖A‖²`. -/
private lemma LiftHermitian_parseval {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) :
    ∑ k, hsInner (hermBasis W k) A ^ 2 = hsSq A := by
  conv_rhs => rw [(hermBasis_parseval W A).2 hA]
  rw [LiftHermitian_hsSq_basis]

/-- `|C_i|_op ≤ |z| + g⁻¹ |V_i|_op`. -/
private lemma LiftHermitian_norm_liftC_le {W q : ℕ} {g : ℝ} (hg : 0 < g) (z : ℝ)
    (V : Fin q → Matrix (Fin W) (Fin W) ℂ) (i : Fin q) :
    ‖liftC g z V i‖ ≤ |z| + g⁻¹ * ‖V i‖ := by
  unfold liftC
  have h1 : ‖(z : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ |z| := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg z)).2 fun j => ?_
    simp
  have h2 : ‖((g : ℂ)⁻¹) • V i‖ = g⁻¹ * ‖V i‖ := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hg.le]
  calc _ ≤ ‖(z : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ + ‖((g : ℂ)⁻¹) • V i‖ := norm_sub_le _ _
    _ ≤ _ := by rw [h2]; linarith

/-- `reCoord` as a real-linear map. -/
private def LiftHermitian_reL (k l : Type*) : Matrix k l ℂ →ₗ[ℝ] (Fin 2 × k × l → ℝ) where
  toFun := reCoord
  map_add' A B := by
    funext p
    simp only [reCoord, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c A := by
    funext p
    simp only [reCoord, Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp

/-- `ofReCoord` as a real-linear map. -/
private def LiftHermitian_ofReL (k l : Type*) : (Fin 2 × k × l → ℝ) →ₗ[ℝ] Matrix k l ℂ where
  toFun := ofReCoord
  map_add' x y := by
    ext a b
    apply Complex.ext <;> simp [ofReCoord]
  map_smul' c x := by
    ext a b
    apply Complex.ext <;> simp [ofReCoord]

/-- `H ↦ 𝒜(H)` as a real-linear map. -/
private def LiftHermitian_pdL {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    (Fin q → Matrix (Fin W) (Fin W) ℂ) →ₗ[ℝ] Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ where
  toFun := prodDiff g z V
  map_add' H H' := by
    have hb : ∀ i, blockMat (0 : Matrix (Fin W) (Fin W) ℂ) 0 ((H + H') i) 0 =
        blockMat 0 0 (H i) 0 + blockMat 0 0 (H' i) 0 := by
      intro i; ext ⟨a, α⟩ ⟨b, β⟩; fin_cases a <;> fin_cases b <;> simp [blockMat]
    simp only [prodDiff, hb, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib, smul_add]
  map_smul' c H := by
    have hb : ∀ i, blockMat (0 : Matrix (Fin W) (Fin W) ℂ) 0 ((c • H) i) 0 =
        c • blockMat 0 0 (H i) 0 := by
      intro i; ext ⟨a, α⟩ ⟨b, β⟩; fin_cases a <;> fin_cases b <;> simp [blockMat]
    simp only [prodDiff, hb, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum,
      RingHom.id_apply]
    rw [smul_comm]

/-- The Hermitian array `c ↦ (Σ_k c_{ik} H_k)_i` as a real-linear map. -/
private def LiftHermitian_hermL (q W : ℕ) :
    (Fin q × Fin W × Fin W → ℝ) →ₗ[ℝ] (Fin q → Matrix (Fin W) (Fin W) ℂ) where
  toFun c := fun i => ∑ k : Fin W × Fin W, ((c (i, k) : ℝ) : ℂ) • hermBasis W k
  map_add' c d := by
    funext i
    simp only [Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
      Finset.smul_sum, mul_smul, Complex.coe_smul]

/-- `M ↦ Π_⊥ M` as a real-linear map. -/
private def LiftHermitian_perpL (W : ℕ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ →ₗ[ℝ] Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ where
  toFun := lieOmegaPerp
  map_add' A B := by
    unfold lieOmegaPerp
    simp only [Matrix.mul_add, Matrix.conjTranspose_add, add_sub_add_comm, smul_add,
      Matrix.trace_add, Complex.add_im, add_div, Complex.ofReal_add, add_smul]
    abel
  map_smul' c A := by
    unfold lieOmegaPerp
    simp only [Matrix.mul_smul, Matrix.conjTranspose_smul, star_trivial, ← smul_add, ← smul_sub,
      smul_comm (1 / 2 : ℂ) c, Matrix.trace_smul, Complex.smul_im, smul_eq_mul, mul_div_assoc,
      Complex.ofReal_mul, mul_smul, Complex.coe_smul, RingHom.id_apply]

/-- `ofReCoord` is injective on the range of `reCoord`. -/
private lemma LiftHermitian_of_re {k l : Type*} (A : Matrix k l ℂ) : ofReCoord (reCoord A) = A := by
  ext a b
  simp [ofReCoord, reCoord]

/-- `reCoord ∘ ofReCoord = id`. -/
private lemma LiftHermitian_re_of {k l : Type*} (x : Fin 2 × k × l → ℝ) :
    reCoord (ofReCoord x : Matrix k l ℂ) = x := by
  funext ⟨i, a, b⟩
  fin_cases i <;> simp [reCoord, ofReCoord]

/-- `Σ_p (reCoord A)_p (reCoord B)_p = ⟨A, B⟩` as a dot product. -/
private lemma LiftHermitian_dot_re {k l : Type*} [Fintype k] [Fintype l] (A B : Matrix k l ℂ) :
    reCoord A ⬝ᵥ reCoord B = hsInner A B :=
  (hsInner_reCoord A B 0).2.2.2.2

/-- `‖x‖² = ‖ofReCoord x‖²`. -/
private lemma LiftHermitian_sum_sq {k l : Type*} [Fintype k] [Fintype l]
    (x : Fin 2 × k × l → ℝ) : ∑ p, x p ^ 2 = hsSq (ofReCoord x : Matrix k l ℂ) := by
  rw [← (hsInner_reCoord (ofReCoord x : Matrix k l ℂ) (ofReCoord x) 0).2.1,
    ← LiftHermitian_dot_re, LiftHermitian_re_of]
  simp [dotProduct, sq]

/-- `ι_i H_k` is a Hermitian array. -/
private lemma LiftHermitian_single_herm {W q : ℕ} (r : Fin q × Fin W × Fin W) (j : Fin q) :
    ((Pi.single r.1 (hermBasis W r.2) : Fin q → Matrix (Fin W) (Fin W) ℂ) j).IsHermitian := by
  by_cases h : j = r.1
  · subst h; simpa using hermBasis_isHermitian W r.2
  · simp [h]

/-- Every `Σ_k c_{ik} H_k` is Hermitian. -/
private lemma LiftHermitian_hermL_herm {W q : ℕ} (c : Fin q × Fin W × Fin W → ℝ) (i : Fin q) :
    (LiftHermitian_hermL q W c i).IsHermitian := by
  simp only [LiftHermitian_hermL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.IsHermitian]
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    (hermBasis_isHermitian W k).eq]

/-- `‖(Σ_k c_{ik} H_k)_i‖² = Σ c²`. -/
private lemma LiftHermitian_hermL_sq {W q : ℕ} (c : Fin q × Fin W × Fin W → ℝ) :
    ∑ i, hsSq (LiftHermitian_hermL q W c i) = ∑ r, c r ^ 2 := by
  simp only [LiftHermitian_hermL, LinearMap.coe_mk, AddHom.coe_mk, LiftHermitian_hsSq_basis]
  rw [Fintype.sum_prod_type]

/-- The matrix of `𝒜` acts as `c ↦ reCoord 𝒜(Σ c_{ik} ι_i H_k)`. -/
private lemma LiftHermitian_A_mulVec {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ)
    (c : Fin q × Fin W × Fin W → ℝ) :
    prodDiffMat g z V *ᵥ c = reCoord (prodDiff g z V (LiftHermitian_hermL q W c)) := by
  have hs : ∀ r : Fin q × Fin W × Fin W,
      LiftHermitian_hermL q W (Pi.single r 1) = Pi.single r.1 (hermBasis W r.2) := by
    rintro ⟨i, k⟩
    funext j
    simp only [LiftHermitian_hermL, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hj : j = i
    · subst hj
      simp [Pi.single_apply]
    · simp [hj]
  have hA : prodDiffMat g z V = LinearMap.toMatrix' ((LiftHermitian_reL _ _).comp
      ((LiftHermitian_pdL g z V).comp (LiftHermitian_hermL q W))) := by
    ext p r
    rw [LinearMap.toMatrix'_apply]
    simp only [LinearMap.comp_apply, hs]
    rfl
  rw [hA, LinearMap.toMatrix'_mulVec]
  rfl

/-- The second block of `hermLiftMat` acts as `x ↦ reCoord Π_⊥(ofReCoord x)`. -/
private lemma LiftHermitian_Pi_mulVec {W : ℕ} (x : Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W) → ℝ) :
    (Matrix.of fun p r => reCoord (lieOmegaPerp (ofReCoord (Pi.single r 1) :
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) p) *ᵥ x =
      reCoord (lieOmegaPerp (ofReCoord x : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) := by
  have hA : (Matrix.of fun p r => reCoord (lieOmegaPerp (ofReCoord (Pi.single r 1) :
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) p) = LinearMap.toMatrix'
      ((LiftHermitian_reL _ _).comp ((LiftHermitian_perpL W).comp (LiftHermitian_ofReL _ _))) := by
    ext p r
    rw [LinearMap.toMatrix'_apply]
    rfl
  rw [hA, LinearMap.toMatrix'_mulVec]
  rfl

/-- `hermLiftMat` acts as `x ↦ (𝒜* x, Π_⊥ x)`. -/
private lemma LiftHermitian_B_mulVec {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ)
    (x : Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W) → ℝ) :
    hermLiftMat g z V *ᵥ x = Sum.elim ((prodDiffMat g z V)ᵀ *ᵥ x)
      (reCoord (lieOmegaPerp (ofReCoord x : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))) := by
  rw [hermLiftMat, Matrix.fromRows_mulVec, LiftHermitian_Pi_mulVec]

/-- `‖B x‖² = ‖𝒜* x‖² + ‖Π_⊥ x‖²`. -/
private lemma LiftHermitian_B_sq {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ)
    (x : Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W) → ℝ) :
    ∑ p, (hermLiftMat g z V *ᵥ x) p ^ 2 = ∑ r, ((prodDiffMat g z V)ᵀ *ᵥ x) r ^ 2 +
      hsSq (lieOmegaPerp (ofReCoord x : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) := by
  rw [LiftHermitian_B_mulVec, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [LiftHermitian_sum_sq (reCoord _), LiftHermitian_of_re]

/-- The entries of `𝒜* y`: `(𝒜* y)_{ik} = ⟨𝒜(ι_i H_k), ofReCoord y⟩`. -/
private lemma LiftHermitian_At_apply {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ)
    (y : Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W) → ℝ) (r : Fin q × Fin W × Fin W) :
    ((prodDiffMat g z V)ᵀ *ᵥ y) r =
      hsInner (prodDiff g z V (Pi.single r.1 (hermBasis W r.2))) (ofReCoord y) := by
  rw [← LiftHermitian_dot_re, LiftHermitian_re_of]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, prodDiffMat, Matrix.of_apply]

/-- `⟨𝒜(Σ c_{ik} ι_i H_k), Y⟩ = c · 𝒜* Y`. -/
private lemma LiftHermitian_hsInner_pd {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ)
    (c : Fin q × Fin W × Fin W → ℝ) (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    hsInner (prodDiff g z V (LiftHermitian_hermL q W c)) Y =
      c ⬝ᵥ ((prodDiffMat g z V)ᵀ *ᵥ reCoord Y) := by
  rw [← LiftHermitian_dot_re, ← LiftHermitian_A_mulVec, Matrix.mulVec_transpose, dotProduct_comm,
    Matrix.dotProduct_mulVec, dotProduct_comm]

/-- `u · (BᵀB) y = (B u) · (B y)`. -/
private lemma LiftHermitian_gram {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℝ)
    (u y : n → ℝ) : u ⬝ᵥ ((Bᵀ * B) *ᵥ y) = (B *ᵥ u) ⬝ᵥ (B *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- `u · Γ y = (𝒜* u) · (𝒜* y) + (Π_⊥ u) · (Π_⊥ y)` for the Gram matrix of `hermLiftMat`. -/
private lemma LiftHermitian_gram_split {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ)
    (u y : Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W) → ℝ) :
    u ⬝ᵥ (((hermLiftMat g z V)ᵀ * hermLiftMat g z V) *ᵥ y) =
      ((prodDiffMat g z V)ᵀ *ᵥ u) ⬝ᵥ ((prodDiffMat g z V)ᵀ *ᵥ y) +
        reCoord (lieOmegaPerp (ofReCoord u : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) ⬝ᵥ
          reCoord (lieOmegaPerp (ofReCoord y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) := by
  rw [LiftHermitian_gram, LiftHermitian_B_mulVec, LiftHermitian_B_mulVec]
  simp [dotProduct, Fintype.sum_sum_type]

/-- The Hermitian lift is `√2 𝒜* Γ⁻¹ M` in the basis `ι_i H_k`. -/
private lemma LiftHermitian_field_eq {W q : ℕ} (g z : ℝ) (V : Fin q → Matrix (Fin W) (Fin W) ℂ)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    hermLiftField g z V M = LiftHermitian_hermL q W (Real.sqrt 2 • ((prodDiffMat g z V)ᵀ *ᵥ
      (((hermLiftMat g z V)ᵀ * hermLiftMat g z V)⁻¹ *ᵥ reCoord M))) := by
  have h : (lsqInv (hermLiftMat g z V))ᵀ *ᵥ reCoord M = hermLiftMat g z V *ᵥ
      (((hermLiftMat g z V)ᵀ * hermLiftMat g z V)⁻¹ *ᵥ reCoord M) := by
    rw [lsqInv, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mulVec_mulVec]
  funext i
  simp only [hermLiftField, LiftHermitian_hermL, LinearMap.coe_mk, AddHom.coe_mk, h,
    LiftHermitian_B_mulVec, Sum.elim_inl, Pi.smul_apply, smul_eq_mul]

/-- `J_ph² = 1`. -/
private lemma LiftHermitian_phJ_sq (W : ℕ) : phJ W * phJ W = 1 := by
  unfold phJ
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have : (!![0, -Complex.I; Complex.I, 0] * !![0, -Complex.I; Complex.I, 0] :
      Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, Matrix.one_kronecker_one]

/-- `J_ph* = J_ph`. -/
private lemma LiftHermitian_phJ_herm (W : ℕ) : (phJ W)ᴴ = phJ W := by
  unfold phJ
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `Π_⊥ M = 0` on the algebra (10.3) [eq:c-Lie]. -/
private lemma LiftHermitian_perp_of_mem {W : ℕ} {M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hM : M ∈ lieOmega W) : lieOmegaPerp M = 0 := by
  obtain ⟨h1, h2⟩ := hM
  have hN : (phJ W * M)ᴴ = -(phJ W * M) := by
    rw [Matrix.conjTranspose_mul, LiftHermitian_phJ_herm]
    exact eq_neg_of_add_eq_zero_left h1
  have hJJ : phJ W * (phJ W * M) = M := by
    rw [← Matrix.mul_assoc, LiftHermitian_phJ_sq, Matrix.one_mul]
  have hh : (1 / 2 : ℂ) • (phJ W * M - -(phJ W * M)) = phJ W * M := by
    rw [sub_neg_eq_add, ← two_smul ℂ (phJ W * M), smul_smul]
    norm_num
  unfold lieOmegaPerp
  rw [hN, add_neg_cancel, smul_zero, Matrix.mul_zero, zero_add, hh, hJJ, h2]
  simp

/-- `M - Π_⊥ M` lies in the algebra (10.3) [eq:c-Lie]. -/
private lemma LiftHermitian_sub_perp_mem {W : ℕ} (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    M - lieOmegaPerp M ∈ lieOmega W := by
  have hJh := LiftHermitian_phJ_herm W
  have hJJ := LiftHermitian_phJ_sq W
  set J := phJ W with hJ
  set N := J * M with hNdef
  set S := (1 / 2 : ℂ) • (N - Nᴴ) with hSdef
  set c : ℝ := (J * S).trace.im / (2 * W) with hc
  have hdec : M - lieOmegaPerp M = J * S - ((c : ℂ) * Complex.I) • (1 : Matrix _ _ ℂ) := by
    have hM : M = J * ((1 / 2 : ℂ) • (N + Nᴴ)) + J * S := by
      rw [← Matrix.mul_add, hSdef, ← smul_add, add_add_sub_cancel, ← two_smul ℂ N, smul_smul]
      norm_num
      rw [hNdef, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    unfold lieOmegaPerp
    rw [← hJ, ← hNdef, ← hSdef, ← hc, smul_smul]
    conv_lhs => rw [hM]
    abel
  have hS : Sᴴ = -S := by
    rw [hSdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, ← neg_sub, smul_neg]
    congr 2
    simp
  have hk : star ((c : ℂ) * Complex.I) = -((c : ℂ) * Complex.I) := by
    simp
  rw [hdec]
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hS, hJh, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hk]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, neg_smul]
    rw [← Matrix.mul_assoc J J S, hJJ, Matrix.one_mul]
    simp only [Matrix.mul_one]
    abel
  · have hre : (J * S).trace.re = 0 := by
      have h1 : star (J * S).trace = -(J * S).trace := by
        rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hS, hJh, Matrix.neg_mul,
          Matrix.trace_neg, Matrix.trace_mul_comm]
      have h2 := congrArg Complex.re h1
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h2
      linarith
    rcases Nat.eq_zero_or_pos W with hW | hW
    · subst hW
      simp [Matrix.trace]
    · have hW' : (0 : ℝ) < W := Nat.cast_pos.2 hW
      rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
      simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
      apply Complex.ext
      · simp [hre]
      · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im, Complex.mul_re,
          Complex.zero_im]
        rw [hc]
        push_cast
        field_simp
        ring

/-- `⟨Y, Π_⊥ M⟩ = 0` for `Y` in the algebra (10.3) [eq:c-Lie]. -/
private lemma LiftHermitian_hsInner_perp {W : ℕ} {Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : Y ∈ lieOmega W) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    hsInner Y (lieOmegaPerp M) = 0 := by
  obtain ⟨h1, h2⟩ := hY
  have hJh := LiftHermitian_phJ_herm W
  set J := phJ W with hJ
  set N := J * M with hNdef
  set H := (1 / 2 : ℂ) • (N + Nᴴ) with hHdef
  have hH : Hᴴ = H := by
    rw [hHdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
    congr 1
    simp
  have hYJ : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left h1
  have hK : (J * Y)ᴴ = -(J * Y) := by rw [Matrix.conjTranspose_mul, hJh, hYJ]
  have ht : ((J * Y) * H).trace.re = 0 := by
    have e : star ((J * Y) * H).trace = -((J * Y) * H).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hH, hK, Matrix.mul_neg,
        Matrix.trace_neg, Matrix.trace_mul_comm]
    have e2 := congrArg Complex.re e
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at e2
    linarith
  rw [(hsInner_reCoord _ _ 0).1]
  unfold lieOmegaPerp
  rw [← hJ, ← hNdef, ← hHdef, Matrix.mul_add, Matrix.trace_add, Complex.add_re,
    ← Matrix.mul_assoc, hYJ, Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re, ht]
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_conjTranspose, h2,
    star_zero, smul_zero, Complex.zero_re, neg_zero, add_zero]

/-- `Π_⊥` is idempotent. -/
private lemma LiftHermitian_perp_perp {W : ℕ} (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    lieOmegaPerp (lieOmegaPerp M) = lieOmegaPerp M := by
  have h := LiftHermitian_perp_of_mem (LiftHermitian_sub_perp_mem M)
  have h2 := (LiftHermitian_perpL W).map_sub M (lieOmegaPerp M)
  simp only [LiftHermitian_perpL, LinearMap.coe_mk, AddHom.coe_mk] at h2
  rw [h] at h2
  exact (sub_eq_zero.mp h2.symm).symm

/-- The general lift in the basis `ι_i H_k`. -/
private lemma LiftHermitian_liftField_eq {W : ℕ} (g z : ℝ)
    (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    liftField g z V Y = LiftHermitian_hermL 1000 W (fun r =>
      Real.sqrt 2 * g * hsInner Y (liftK0 g z V (Pi.single r.1 (hermBasis W r.2)))) := rfl

/-- `𝒜*` vanishes on the range of `Π_⊥`. -/
private lemma LiftHermitian_At_perp {W q : ℕ} {g z : ℝ} {V : Fin q → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, (V i).IsHermitian) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (prodDiffMat g z V)ᵀ *ᵥ reCoord (lieOmegaPerp M) = 0 := by
  funext r
  rw [LiftHermitian_At_apply, LiftHermitian_of_re]
  exact LiftHermitian_hsInner_perp (prodDiff_mem_lieOmega hV (LiftHermitian_single_herm r)) M

/-- `ofReCoord 0 = 0`. -/
private lemma LiftHermitian_ofRe_zero {k l : Type*} :
    (ofReCoord (0 : Fin 2 × k × l → ℝ) : Matrix k l ℂ) = 0 := by
  ext a b
  apply Complex.ext <;> simp [ofReCoord]

/-- Where `S_W(G) ≥ c₁ > 0`, the Gram matrix of `hermLiftMat` is invertible. -/
private lemma LiftHermitian_isUnit {W : ℕ} {g z c₁ : ℝ} (hg : 0 < g) (hc₁ : 0 < c₁)
    {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, (V i).IsHermitian)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V)) :
    IsUnit ((hermLiftMat g z V)ᵀ * hermLiftMat g z V).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨y, hy, hGy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hy
  have hBy : hermLiftMat g z V *ᵥ y = 0 := by
    have h1 := LiftHermitian_gram (hermLiftMat g z V) y y
    rw [hGy, dotProduct_zero] at h1
    exact dotProduct_self_eq_zero.1 h1.symm
  rw [LiftHermitian_B_mulVec] at hBy
  have hAy : (prodDiffMat g z V)ᵀ *ᵥ y = 0 := by
    funext r
    exact congrFun hBy (Sum.inl r)
  have hPy : lieOmegaPerp (ofReCoord y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) = 0 := by
    have h1 : reCoord (lieOmegaPerp (ofReCoord y :
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) = 0 := by
      funext p
      exact congrFun hBy (Sum.inr p)
    rw [← LiftHermitian_of_re (lieOmegaPerp _), h1, LiftHermitian_ofRe_zero]
  have hY : (ofReCoord y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) ∈ lieOmega W := by
    have h1 := LiftHermitian_sub_perp_mem (ofReCoord y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    rwa [hPy, sub_zero] at h1
  have hX := (prodDiff_liftField (z := z) hg hc₁ hV hc (ofReCoord y)).2 hY
  have h2 := LiftHermitian_hsInner_pd g z V (fun r => Real.sqrt 2 * g *
    hsInner (ofReCoord y) (liftK0 g z V (Pi.single r.1 (hermBasis W r.2)))) (ofReCoord y)
  rw [← LiftHermitian_liftField_eq, hX, LiftHermitian_hsInner_smul_left,
    (hsInner_reCoord (ofReCoord y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) 0 0).2.1,
    LiftHermitian_re_of, hAy, dotProduct_zero] at h2
  have h4 := LiftHermitian_eq_zero_of_hsSq ((mul_eq_zero.1 h2).resolve_left (by positivity))
  rw [← LiftHermitian_re_of y, h4]
  funext p
  simp [reCoord]

/-- Where `S_W(G) ≥ c₁ > 0`, for `M` in the algebra (10.3) [eq:c-Lie], `y = Γ⁻¹ M` lies in the
algebra and `𝒜 𝒜* y = M`. -/
private lemma LiftHermitian_solve {W : ℕ} {g z c₁ : ℝ} (hg : 0 < g) (hc₁ : 0 < c₁)
    {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, (V i).IsHermitian)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V))
    {M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hM : M ∈ lieOmega W) :
    (ofReCoord (((hermLiftMat g z V)ᵀ * hermLiftMat g z V)⁻¹ *ᵥ reCoord M) :
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) ∈ lieOmega W ∧
      prodDiffMat g z V *ᵥ ((prodDiffMat g z V)ᵀ *ᵥ
        (((hermLiftMat g z V)ᵀ * hermLiftMat g z V)⁻¹ *ᵥ reCoord M)) = reCoord M := by
  have hsplit := LiftHermitian_gram_split g z V
  have hunit := LiftHermitian_isUnit (z := z) hg hc₁ hV hc
  set G := (hermLiftMat g z V)ᵀ * hermLiftMat g z V with hG
  set A := prodDiffMat g z V with hA
  set m := reCoord M with hm
  set y := G⁻¹ *ᵥ m with hy
  have hGy : G *ᵥ y = m := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  set Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := ofReCoord y with hYdef
  set y₂ := reCoord (lieOmegaPerp Y) with hy₂
  have hA2 : Aᵀ *ᵥ y₂ = 0 := LiftHermitian_At_perp hV _
  have hP2 : reCoord (lieOmegaPerp (ofReCoord y₂ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) =
      y₂ := by
    rw [hy₂, LiftHermitian_of_re, LiftHermitian_perp_perp]
  have hm2 : y₂ ⬝ᵥ m = 0 := by
    rw [hy₂, hm, LiftHermitian_dot_re, LiftHermitian_hsInner_comm, LiftHermitian_hsInner_perp hM]
  have hy20 : y₂ = 0 := by
    have h := hsplit y₂ y
    rw [hGy, hm2, hA2, zero_dotProduct, zero_add, hP2] at h
    exact dotProduct_self_eq_zero.1 h.symm
  have hPY : lieOmegaPerp Y = 0 := by
    rw [← LiftHermitian_of_re (lieOmegaPerp Y), ← hy₂, hy20, LiftHermitian_ofRe_zero]
  refine ⟨?_, ?_⟩
  · have h := LiftHermitian_sub_perp_mem Y
    rwa [hPY, sub_zero] at h
  · set u := m - A *ᵥ (Aᵀ *ᵥ y) with hu
    have h := hsplit u y
    rw [hGy, ← hy₂, hy20, dotProduct_zero, add_zero, Matrix.mulVec_transpose,
      ← Matrix.dotProduct_mulVec] at h
    have huu : u ⬝ᵥ u = 0 := by
      calc u ⬝ᵥ u = u ⬝ᵥ (m - A *ᵥ (Aᵀ *ᵥ y)) := rfl
        _ = 0 := by rw [dotProduct_sub, h, sub_self]
    have hu0 := dotProduct_self_eq_zero.1 huu
    rw [hu] at hu0
    exact (sub_eq_zero.1 hu0).symm

/-- (10.29) [lg:eq:coercivity] on the algebra (10.3) [eq:c-Lie]: `‖Z‖² ≤ C g⁴ ‖𝒜* Z‖²`. -/
private lemma LiftHermitian_core (E₀ K₁ c₁ : ℝ) (hE₀ : 0 < E₀) (hK₁ : 0 < K₁) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ) (g E : ℝ) (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ),
      1 ≤ g → |E| ≤ E₀ → (∀ i, (V i).IsHermitian) → (∀ i, ‖V i‖ ≤ K₁) →
      c₁ ≤ coerMin (layoutBlocks liftLayout V) →
        ∀ Y ∈ lieOmega W, hsSq Y ≤ C * g ^ 4 *
          ∑ r, ((prodDiffMat g (max 1 g * E / g) V)ᵀ *ᵥ reCoord Y) r ^ 2 := by
  obtain ⟨C, hC, hL⟩ := sum_hsSq_liftField_le E₀ K₁ c₁ hE₀ hK₁ hc₁
  refine ⟨C, hC, fun W g E V hg hE hVh hVn hc Y hY => ?_⟩
  have hg0 : 0 < g := by linarith
  have hmax : max (g⁻¹ ^ 2) (g ^ 4) = g ^ 4 := by
    apply max_eq_right
    have h1 : g⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hg)
    have h2 : 1 ≤ g ^ 4 := one_le_pow₀ hg
    linarith
  have hsz := hL W g E V Y hg0 hE hVh hVn hc
  have hX := (prodDiff_liftField (z := max 1 g * E / g) hg0 hc₁ hVh hc Y).2 hY
  have hin := LiftHermitian_hsInner_pd g (max 1 g * E / g) V (fun r => Real.sqrt 2 * g *
    hsInner Y (liftK0 g (max 1 g * E / g) V (Pi.single r.1 (hermBasis W r.2)))) Y
  rw [hmax, LiftHermitian_liftField_eq, LiftHermitian_hermL_sq] at hsz
  rw [← LiftHermitian_liftField_eq, hX, LiftHermitian_hsInner_smul_left,
    (hsInner_reCoord Y Y 0).2.1] at hin
  set c : Fin 1000 × Fin W × Fin W → ℝ := fun r => Real.sqrt 2 * g *
    hsInner Y (liftK0 g (max 1 g * E / g) V (Pi.single r.1 (hermBasis W r.2))) with hcdef
  set w := (prodDiffMat g (max 1 g * E / g) V)ᵀ *ᵥ reCoord Y with hw
  have hcs : (c ⬝ᵥ w) ^ 2 ≤ (∑ r, c r ^ 2) * ∑ r, w r ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  rw [← hin] at hcs
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hY0 := LiftHermitian_hsSq_nonneg Y
  have hw0 : 0 ≤ ∑ r, w r ^ 2 := Finset.sum_nonneg fun r _ => sq_nonneg _
  have key : 2 * hsSq Y ^ 2 ≤ (C * g ^ 4 * hsSq Y) * ∑ r, w r ^ 2 := by
    calc 2 * hsSq Y ^ 2 = (Real.sqrt 2 * hsSq Y) ^ 2 := by rw [mul_pow, hs2]
      _ ≤ _ := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_right hsz hw0
  rcases hY0.lt_or_eq with hpos | hzero
  · have h2 : 2 * hsSq Y ≤ C * g ^ 4 * ∑ r, w r ^ 2 := by
      have h' : hsSq Y * (2 * hsSq Y) ≤ hsSq Y * (C * g ^ 4 * ∑ r, w r ^ 2) := by nlinarith
      exact le_of_mul_le_mul_left h' hpos
    nlinarith
  · rw [← hzero]
    positivity

/-- Equal block matrices have equal blocks. -/
private lemma LiftHermitian_blockMat_inj {n : Type*} {A B C D A' B' C' D' : Matrix n n ℂ}
    (h : blockMat A B C D = blockMat A' B' C' D') : A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  obtain ⟨-, e1, e2, e3, e4⟩ := blockMat_blockPart (0 : Matrix (Fin 2 × n) (Fin 2 × n) ℂ) A B C D
  obtain ⟨-, f1, f2, f3, f4⟩ :=
    blockMat_blockPart (0 : Matrix (Fin 2 × n) (Fin 2 × n) ℂ) A' B' C' D'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e1, ← f1, h]
  · rw [← e2, ← f2, h]
  · rw [← e3, ← f3, h]
  · rw [← e4, ← f4, h]

/-- A Hermitian target of the algebra (10.3) [eq:c-Lie] is `[[A, B], [B, -A]]` with `A, B`
Hermitian. -/
private lemma LiftHermitian_herm_target {W : ℕ} {M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hM : M ∈ lieOmega W) (hMh : M.IsHermitian) :
    (blockPart M 0 0)ᴴ = blockPart M 0 0 ∧ (blockPart M 0 1)ᴴ = blockPart M 0 1 ∧
      M = blockMat (blockPart M 0 0) (blockPart M 0 1) (blockPart M 0 1) (-blockPart M 0 0) := by
  obtain ⟨hMb, -⟩ := blockMat_blockPart M 0 0 0 0
  have hl := hM
  rw [← hMb, mem_lieOmega_iff] at hl
  obtain ⟨hB, hB', hD, -⟩ := hl
  have hh : (blockMat (blockPart M 0 0) (blockPart M 0 1) (blockPart M 1 0) (blockPart M 1 1))ᴴ =
      blockMat (blockPart M 0 0) (blockPart M 0 1) (blockPart M 1 0) (blockPart M 1 1) := by
    rw [hMb]; exact hMh
  rw [(blockMat_algebra _ _ _ _ 0 0 0 0).2.1] at hh
  obtain ⟨hA, h10, -, -⟩ := LiftHermitian_blockMat_inj hh
  have hBB : blockPart M 1 0 = blockPart M 0 1 := by rw [← h10, hB'.eq]
  refine ⟨hA, hB.eq, ?_⟩
  conv_lhs => rw [← hMb]
  rw [hBB, hD, hA]

/-- `⟨[[A, B], [B, -A]], [[P, U], [R, -P*]]⟩ = ⟨A, P + P*⟩ + ⟨B, U + R⟩` for Hermitian `A, B`. -/
private lemma LiftHermitian_hsInner_block {n : Type*} [Fintype n] {A B : Matrix n n ℂ}
    (hA : Aᴴ = A) (hB : Bᴴ = B) (P U R : Matrix n n ℂ) :
    hsInner (blockMat A B B (-A)) (blockMat P U R (-Pᴴ)) =
      hsInner A (P + Pᴴ) + hsInner B (U + R) := by
  rw [(hsInner_reCoord _ _ 0).1, (blockMat_algebra A B B (-A) 0 0 0 0).2.1,
    Matrix.conjTranspose_neg, hA, hB, (blockMat_algebra A B B (-A) P U R (-Pᴴ)).1,
    (blockMat_algebra _ _ _ _ 0 0 0 0).2.2.1, (hsInner_reCoord _ _ 0).1,
    (hsInner_reCoord _ _ 0).1, hA, hB]
  simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re, Matrix.neg_mul, Matrix.mul_neg,
    neg_neg]
  ring

/-- (10.27) [lg:eq:hermitian-blocks], (10.28) [lg:eq:hermitian-dual]: for a Hermitian target `M`
and `Y` of the algebra (10.3) [eq:c-Lie], `⟨M, Y⟩² ≤ C (1 + |E|⁻¹)² g² ‖𝒜* Y‖² ‖M‖²`. -/
private lemma LiftHermitian_dual (E₀ K₁ c₁ : ℝ) (hE₀ : 0 < E₀) (hK₁ : 0 < K₁) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ) (g E : ℝ) (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
      (M Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
      1 ≤ g → E ≠ 0 → |E| ≤ E₀ → (∀ i, (V i).IsHermitian) → (∀ i, ‖V i‖ ≤ K₁) →
      c₁ ≤ coerMin (layoutBlocks liftLayout V) → M ∈ lieOmega W → M.IsHermitian →
      Y ∈ lieOmega W →
        hsInner M Y ^ 2 ≤ C * (1 + |E|⁻¹) ^ 2 * g ^ 2 *
          (∑ r, ((prodDiffMat g (max 1 g * E / g) V)ᵀ *ᵥ reCoord Y) r ^ 2) * hsSq M := by
  obtain ⟨C₀, hC₀, hcore⟩ := LiftHermitian_core E₀ K₁ c₁ hE₀ hK₁ hc₁
  obtain ⟨CF, hCF, hF⟩ := hsSq_liftF_le E₀ K₁ hE₀ hK₁
  set Q₁ := 2 * CF + 8 * K₁ ^ 2 * C₀ with hQ₁
  set Q₂ := 8 * (Q₁ + 4 * K₁ ^ 2 * C₀ + (E₀ + K₁) ^ 4 + 1) with hQ₂
  refine ⟨Q₁ + 2 * Q₂ + 2, by positivity,
    fun W g E V M Y hg hE0 hE hVh hVn hc hM hMh hY => ?_⟩
  clear_value Q₁ Q₂
  have hg0 : 0 < g := by linarith
  have hcY := hcore W g E V hg hE hVh hVn hc Y hY
  have hFR := fun R => (hF W g E V R hg0 hE hVn).1 2
  have hK := liftK0_liftConj (g := g) (z := max 1 g * E / g) hg0 hc₁ hVh hc hY
  have hobs := fun H => hsInner_prodDiff (g := g) (z := max 1 g * E / g) hVh H hY
  have hpair := liftF_eq (g := g) (z := max 1 g * E / g) hVh hY (by decide : Even 1000)
    (by decide : Even 2) le_rfl (by norm_num)
  set z := max 1 g * E / g with hzdef
  have hz : z = E := by rw [hzdef, max_eq_right hg]; field_simp
  set S := ∑ r, ((prodDiffMat g z V)ᵀ *ᵥ reCoord Y) r ^ 2 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ := fun i => blockPart (liftConj g z V Y i) 1 0
    with hRdef
  have hRh : ∀ i, (R i).IsHermitian := by
    intro i
    have h := (hobs 0).1 i
    rw [← (blockMat_blockPart (liftConj g z V Y i) 0 0 0 0).1, mem_lieOmega_iff] at h
    exact h.2.1
  set a := g ^ 2 * S with ha
  have ha0 : 0 ≤ a := by positivity
  have hρ : ∑ i, hsSq (R i) = a := by
    have hSρ : S = (g ^ 2)⁻¹ * ∑ i, hsSq (R i) := by
      rw [hSdef, Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← LiftHermitian_parseval (hRh i), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LiftHermitian_At_apply, LiftHermitian_of_re, (hobs _).2]
      dsimp only
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same]
        ring
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj, hsInner]
      · simp
    rw [ha, hSρ, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have hR1 : ∀ i, hsSq (R i) ≤ a := fun i => hρ ▸
    Finset.single_le_sum (f := fun i => hsSq (R i)) (fun i _ => LiftHermitian_hsSq_nonneg _)
      (Finset.mem_univ i)
  clear_value a
  set P := liftKP g z V R with hPdef
  set Cq := liftC g z V 999 with hCq
  set U := P * Cq + Cq * Pᴴ + Cq * R 999 * Cq - R 998 with hUdef
  have hYb : Y = blockMat P U (R 999) (-Pᴴ) := by rw [← hK]; rfl
  have hPC : P * Cq + Cq * Pᴴ = (z : ℂ) • (P + Pᴴ) - ((g : ℂ)⁻¹) • (P * V 999 + V 999 * Pᴴ) := by
    rw [hCq]
    unfold liftC
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_add]
    abel
  clear_value U P Cq
  have hP0 : blockPart Y 0 0 = P := by
    rw [hYb]; exact (blockMat_blockPart Y P U (R 999) (-Pᴴ)).2.1
  have hs2 : liftSeq (liftC g z V) 2 = liftC g z V 2 := by
    simp only [liftSeq, show (2 : ℕ) < 1000 by norm_num, ↓reduceDIte]
    rfl
  rw [hs2, hP0] at hpair
  have hYs : hsSq Y = hsSq P + hsSq U + hsSq (R 999) + hsSq (-Pᴴ) := by
    rw [hYb]; exact (blockMat_algebra P U (R 999) (-Pᴴ) 0 0 0 0).2.2.2
  have hPY : hsSq P ≤ hsSq Y := by
    linarith [LiftHermitian_hsSq_nonneg U, LiftHermitian_hsSq_nonneg (R 999),
      LiftHermitian_hsSq_nonneg (-Pᴴ)]
  have hPg : (g ^ 2)⁻¹ * hsSq P ≤ C₀ * a := by
    rw [inv_mul_le_iff₀ (by positivity)]
    calc hsSq P ≤ C₀ * g ^ 4 * S := hPY.trans hcY
      _ = g ^ 2 * (C₀ * a) := by rw [ha]; ring
  have hnorm : ∀ i, ‖V i‖ ^ 2 ≤ K₁ ^ 2 := fun i => pow_le_pow_left₀ (norm_nonneg _) (hVn i) 2
  have hVP : ∀ i, hsSq (V i * P + Pᴴ * V i) ≤ 4 * K₁ ^ 2 * hsSq P ∧
      hsSq (P * V i + V i * Pᴴ) ≤ 4 * K₁ ^ 2 * hsSq P := by
    intro i
    have h4 := mul_le_mul_of_nonneg_right (hnorm i) (LiftHermitian_hsSq_nonneg P)
    have h5 := LiftHermitian_hsSq_sym_le (V i) Pᴴ
    rw [Matrix.conjTranspose_conjTranspose, LiftHermitian_hsSq_conjTranspose, add_comm] at h5
    have h6 : 4 * ‖V i‖ ^ 2 * hsSq P ≤ 4 * K₁ ^ 2 * hsSq P := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left h4 (by norm_num)
    exact ⟨(LiftHermitian_hsSq_sym_le (V i) P).trans h6, h5.trans h6⟩
  have hgV : ∀ X : Matrix (Fin W) (Fin W) ℂ, hsSq X ≤ 4 * K₁ ^ 2 * hsSq P →
      (g ^ 2)⁻¹ * hsSq X ≤ 4 * K₁ ^ 2 * (C₀ * a) := by
    intro X hX
    calc (g ^ 2)⁻¹ * hsSq X ≤ (g ^ 2)⁻¹ * (4 * K₁ ^ 2 * hsSq P) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = 4 * K₁ ^ 2 * ((g ^ 2)⁻¹ * hsSq P) := by ring
      _ ≤ 4 * K₁ ^ 2 * (C₀ * a) := mul_le_mul_of_nonneg_left hPg (by positivity)
  have hginv : ‖((g : ℂ)⁻¹)‖ ^ 2 = (g ^ 2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hg0.le, inv_pow]
  have hzP : (z : ℂ) • (P + Pᴴ) = liftF g z V R 2 + ((g : ℂ)⁻¹) • (V 2 * P + Pᴴ * V 2) := by
    rw [← hpair]
    unfold liftC
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_add]
    abel
  have hmax4 : max 1 (g⁻¹ ^ 4) = 1 :=
    max_eq_left (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hg))
  have hEP : hsSq ((z : ℂ) • (P + Pᴴ)) ≤ Q₁ * a := by
    rw [hzP]
    have h1 := LiftHermitian_hsSq_add_le (liftF g z V R 2) (((g : ℂ)⁻¹) • (V 2 * P + Pᴴ * V 2))
    have h2 := hFR R
    rw [hmax4, mul_one, hρ] at h2
    rw [LiftHermitian_hsSq_smul, hginv] at h1
    have h3 := hgV _ (hVP 2).1
    rw [hQ₁]
    linarith
  have hPP : hsSq (P + Pᴴ) ≤ |E|⁻¹ ^ 2 * (Q₁ * a) := by
    rw [LiftHermitian_hsSq_smul, Complex.norm_real, Real.norm_eq_abs, hz] at hEP
    have hE2 : 0 < |E| ^ 2 := by positivity
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ hE2]
    linarith
  have hCn : ‖Cq‖ ≤ E₀ + K₁ := by
    have h := LiftHermitian_norm_liftC_le hg0 z V 999
    have h1 : g⁻¹ * ‖V 999‖ ≤ 1 * K₁ :=
      mul_le_mul (inv_le_one_of_one_le₀ hg) (hVn 999) (norm_nonneg _) zero_le_one
    have hzE : |z| ≤ E₀ := by rw [hz]; exact hE
    rw [hCq]
    linarith
  have hCn2 : ‖Cq‖ ^ 2 ≤ (E₀ + K₁) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hCn 2
  have hCRC : hsSq (Cq * R 999 * Cq) ≤ (E₀ + K₁) ^ 4 * a := by
    calc hsSq (Cq * R 999 * Cq) ≤ ‖Cq‖ ^ 2 * hsSq (Cq * R 999) :=
          LiftHermitian_hsSq_mul_le' Cq (Cq * R 999)
      _ ≤ (E₀ + K₁) ^ 2 * ((E₀ + K₁) ^ 2 * a) :=
          mul_le_mul hCn2 ((LiftHermitian_hsSq_mul_le Cq (R 999)).trans (mul_le_mul hCn2 (hR1 999)
            (LiftHermitian_hsSq_nonneg _) (by positivity))) (LiftHermitian_hsSq_nonneg _)
            (by positivity)
      _ = (E₀ + K₁) ^ 4 * a := by ring
  have hU : hsSq U ≤ Q₂ * a := by
    have h1 := LiftHermitian_hsSq_sub_le (P * Cq + Cq * Pᴴ + Cq * R 999 * Cq) (R 998)
    have h2 := LiftHermitian_hsSq_add_le (P * Cq + Cq * Pᴴ) (Cq * R 999 * Cq)
    have h3 := LiftHermitian_hsSq_sub_le ((z : ℂ) • (P + Pᴴ))
      (((g : ℂ)⁻¹) • (P * V 999 + V 999 * Pᴴ))
    rw [← hPC, LiftHermitian_hsSq_smul ((g : ℂ)⁻¹), hginv] at h3
    have h4 := hgV _ (hVP 999).2
    have h5 := hR1 998
    have h6 : 0 ≤ (E₀ + K₁) ^ 4 * a := by positivity
    rw [hUdef, hQ₂]
    linarith
  obtain ⟨hAh, hBh, hMe⟩ := LiftHermitian_herm_target hM hMh
  set A := blockPart M 0 0 with hAdef
  set B := blockPart M 0 1 with hBdef
  have hin : hsInner M Y = hsInner A (P + Pᴴ) + hsInner B (U + R 999) := by
    rw [hMe, hYb]
    exact LiftHermitian_hsInner_block hAh hBh P U (R 999)
  have hMs : hsSq M = 2 * hsSq A + 2 * hsSq B := by
    rw [hMe, (blockMat_algebra A B B (-A) 0 0 0 0).2.2.2, show hsSq (-A) = hsSq A by simp [hsSq]]
    ring
  have hi1 := LiftHermitian_hsInner_sq_le A (P + Pᴴ)
  have hi2 := LiftHermitian_hsInner_sq_le B (U + R 999)
  have hUR := LiftHermitian_hsSq_add_le U (R 999)
  have hA0 := LiftHermitian_hsSq_nonneg A
  have hB0 := LiftHermitian_hsSq_nonneg B
  have step1 : hsInner M Y ^ 2 ≤
      hsSq M * (hsSq (P + Pᴴ) + 2 * hsSq U + 2 * hsSq (R 999)) := by
    rw [hin, hMs]
    have hxy := two_mul_le_add_sq (hsInner A (P + Pᴴ)) (hsInner B (U + R 999))
    have k1 := mul_le_mul_of_nonneg_left hUR hB0
    have k2 := mul_nonneg hA0 (LiftHermitian_hsSq_nonneg U)
    have k3 := mul_nonneg hA0 (LiftHermitian_hsSq_nonneg (R 999))
    have k4 := mul_nonneg hB0 (LiftHermitian_hsSq_nonneg (P + Pᴴ))
    linarith
  set e := |E|⁻¹ with he
  have he0 : 0 ≤ e := by positivity
  have step2 : hsSq (P + Pᴴ) + 2 * hsSq U + 2 * hsSq (R 999) ≤
      (Q₁ + 2 * Q₂ + 2) * (1 + e) ^ 2 * a := by
    have hQ₁0 : 0 ≤ Q₁ := by rw [hQ₁]; positivity
    have hQ₂0 : 0 ≤ Q₂ := by rw [hQ₂, hQ₁]; positivity
    have hR := hR1 999
    have h1 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ he0 (by linarith : e ≤ 1 + e) 2)
      (mul_nonneg hQ₁0 ha0)
    have h2 := mul_le_mul_of_nonneg_right (one_le_pow₀ (by linarith : 1 ≤ 1 + e) : 1 ≤ (1 + e) ^ 2)
      (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Q₂ + 2) ha0)
    linarith
  calc hsInner M Y ^ 2 ≤ hsSq M * (hsSq (P + Pᴴ) + 2 * hsSq U + 2 * hsSq (R 999)) := step1
    _ ≤ hsSq M * ((Q₁ + 2 * Q₂ + 2) * (1 + e) ^ 2 * a) :=
        mul_le_mul_of_nonneg_left step2 (LiftHermitian_hsSq_nonneg M)
    _ = (Q₁ + 2 * Q₂ + 2) * (1 + e) ^ 2 * g ^ 2 * S * hsSq M := by rw [ha]; ring

end LiftHermitianAux

/-- (10.30) [lg:eq:minimal-lift]: where `S_W(G) ≥ c₁ > 0`, the Hermitian lift solves
`𝒜(X) = √2 M` for every target `M` of the algebra (10.3) [eq:c-Lie]. -/
theorem prodDiff_hermLiftField {W : ℕ} {g z c₁ : ℝ} (hg : 0 < g) (hc₁ : 0 < c₁)
    {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, (V i).IsHermitian)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V)) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (∀ i, (hermLiftField g z V M i).IsHermitian) ∧
      (M ∈ lieOmega W → prodDiff g z V (hermLiftField g z V M) = ((Real.sqrt 2 : ℝ) : ℂ) • M) := by
  refine ⟨fun i => ?_, fun hM => ?_⟩
  · rw [LiftHermitian_field_eq]
    exact LiftHermitian_hermL_herm _ i
  · obtain ⟨-, hAA⟩ := LiftHermitian_solve (z := z) hg hc₁ hV hc hM
    have h1 := LiftHermitian_A_mulVec g z V (Real.sqrt 2 • ((prodDiffMat g z V)ᵀ *ᵥ
      (((hermLiftMat g z V)ᵀ * hermLiftMat g z V)⁻¹ *ᵥ reCoord M)))
    rw [Matrix.mulVec_smul, hAA] at h1
    have h2 := (LiftHermitian_ofReL (Fin 2 × Fin W) (Fin 2 × Fin W)).map_smul (Real.sqrt 2)
      (reCoord M)
    simp only [LiftHermitian_ofReL, LinearMap.coe_mk, AddHom.coe_mk] at h2
    rw [LiftHermitian_field_eq, ← LiftHermitian_of_re (prodDiff g z V _), ← h1, h2,
      LiftHermitian_of_re, Complex.coe_smul]

/-- (10.29) [lg:eq:coercivity]: for `g ≥ 1`, `|E| ≤ E₀`, `max_i ‖V_i‖ ≤ K₁` and
`S_W(G) ≥ c₁`, `‖𝒜* Z‖² + ‖Π_⊥ Z‖² ≥ (C g⁴)⁻¹ ‖Z‖²`, that is `Γ ≥ c g⁻⁴` on the algebra. -/
theorem hermLiftMat_coercive (E₀ K₁ c₁ : ℝ) (hE₀ : 0 < E₀) (hK₁ : 0 < K₁) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ) (g E : ℝ) (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ),
      1 ≤ g → |E| ≤ E₀ → (∀ i, (V i).IsHermitian) → (∀ i, ‖V i‖ ≤ K₁) →
      c₁ ≤ coerMin (layoutBlocks liftLayout V) →
        ∀ x : Fin 2 × (Fin 2 × Fin W) × (Fin 2 × Fin W) → ℝ,
          (C * g ^ 4)⁻¹ * ∑ r, x r ^ 2 ≤ ∑ p, (hermLiftMat g (max 1 g * E / g) V *ᵥ x) p ^ 2 := by
  obtain ⟨C₀, hC₀, hcore⟩ := LiftHermitian_core E₀ K₁ c₁ hE₀ hK₁ hc₁
  refine ⟨max C₀ 1, by positivity, fun W g E V hg hE hVh hVn hc x => ?_⟩
  have hY₁ := LiftHermitian_sub_perp_mem (ofReCoord x : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
  have hc0 := hcore W g E V hg hE hVh hVn hc _ hY₁
  have hAt : (prodDiffMat g (max 1 g * E / g) V)ᵀ *ᵥ x =
      (prodDiffMat g (max 1 g * E / g) V)ᵀ *ᵥ reCoord ((ofReCoord x : Matrix (Fin 2 × Fin W)
        (Fin 2 × Fin W) ℂ) - lieOmegaPerp (ofReCoord x)) := by
    have h1 := (LiftHermitian_reL (Fin 2 × Fin W) (Fin 2 × Fin W)).map_sub
      (ofReCoord x : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (lieOmegaPerp (ofReCoord x))
    simp only [LiftHermitian_reL, LinearMap.coe_mk, AddHom.coe_mk] at h1
    rw [h1, Matrix.mulVec_sub, LiftHermitian_At_perp hVh, sub_zero, LiftHermitian_re_of]
  have hsq : ∑ r, x r ^ 2 = hsSq ((ofReCoord x : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      lieOmegaPerp (ofReCoord x)) + hsSq (lieOmegaPerp (ofReCoord x :
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) := by
    rw [LiftHermitian_sum_sq]
    conv_lhs => rw [← sub_add_cancel (ofReCoord x : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      (lieOmegaPerp (ofReCoord x))]
    rw [LiftHermitian_hsSq_add, LiftHermitian_hsInner_perp hY₁, mul_zero, add_zero]
  rw [LiftHermitian_B_sq, hAt, hsq, inv_mul_le_iff₀ (by positivity)]
  have hs0 : 0 ≤ ∑ r, ((prodDiffMat g (max 1 g * E / g) V)ᵀ *ᵥ reCoord ((ofReCoord x :
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - lieOmegaPerp (ofReCoord x))) r ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hy₂0 := LiftHermitian_hsSq_nonneg (lieOmegaPerp (ofReCoord x :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))
  have h1 : 1 ≤ max C₀ 1 * g ^ 4 :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ hg)
  have h2 : C₀ * g ^ 4 ≤ max C₀ 1 * g ^ 4 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  nlinarith

/-- (10.27) [lg:eq:hermitian-blocks], (10.28) [lg:eq:hermitian-dual], (10.31) [lg:eq:hermlift]:
for `g ≥ 1`, `0 < |E| ≤ E₀`, `max_i ‖V_i‖ ≤ K₁`, `S_W(G) ≥ c₁` and a Hermitian target `M` of the
algebra, `‖X‖² ≤ C (1 + |E|⁻¹)² g² ‖M‖²` and `‖Γ⁻¹ M‖² ≤ C (1 + |E|⁻¹)² g⁶ ‖M‖²`. -/
theorem hermLiftField_size (E₀ K₁ c₁ : ℝ) (hE₀ : 0 < E₀) (hK₁ : 0 < K₁) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ) (g E : ℝ) (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
      (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
      1 ≤ g → E ≠ 0 → |E| ≤ E₀ → (∀ i, (V i).IsHermitian) → (∀ i, ‖V i‖ ≤ K₁) →
      c₁ ≤ coerMin (layoutBlocks liftLayout V) → M ∈ lieOmega W → M.IsHermitian →
        ∑ i, hsSq (hermLiftField g (max 1 g * E / g) V M i) ≤
            C * (1 + |E|⁻¹) ^ 2 * g ^ 2 * hsSq M ∧
          ∑ r, (((hermLiftMat g (max 1 g * E / g) V)ᵀ * hermLiftMat g (max 1 g * E / g) V)⁻¹ *ᵥ
            reCoord M) r ^ 2 ≤ C * (1 + |E|⁻¹) ^ 2 * g ^ 6 * hsSq M := by
  obtain ⟨C₀, hC₀, hcore⟩ := LiftHermitian_core E₀ K₁ c₁ hE₀ hK₁ hc₁
  obtain ⟨D, hD, hdual⟩ := LiftHermitian_dual E₀ K₁ c₁ hE₀ hK₁ hc₁
  refine ⟨2 * D + C₀ * D, by positivity,
    fun W g E V M hg hE0 hE hVh hVn hc hM hMh => ?_⟩
  have hg0 : 0 < g := by linarith
  obtain ⟨hYm, hAA⟩ := LiftHermitian_solve (z := max 1 g * E / g) hg0 hc₁ hVh hc hM
  have hcY := hcore W g E V hg hE hVh hVn hc _ hYm
  have hdY := hdual W g E V M _ hg hE0 hE hVh hVn hc hM hMh hYm
  rw [LiftHermitian_field_eq, LiftHermitian_hermL_sq]
  rw [LiftHermitian_re_of] at hcY hdY
  rw [← LiftHermitian_sum_sq] at hcY
  set A := prodDiffMat g (max 1 g * E / g) V with hA
  set y := ((hermLiftMat g (max 1 g * E / g) V)ᵀ * hermLiftMat g (max 1 g * E / g) V)⁻¹ *ᵥ
    reCoord M with hy
  set S := ∑ r, (Aᵀ *ᵥ y) r ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSM : S = hsInner M (ofReCoord y) := by
    have e : y ⬝ᵥ (A *ᵥ (Aᵀ *ᵥ y)) = (Aᵀ *ᵥ y) ⬝ᵥ (Aᵀ *ᵥ y) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have e2 : y ⬝ᵥ reCoord M = hsInner M (ofReCoord y) := by
      rw [LiftHermitian_hsInner_comm, ← LiftHermitian_dot_re, LiftHermitian_re_of]
    rw [hAA, e2] at e
    rw [e, hS]
    simp [dotProduct, sq]
  rw [← hSM] at hdY
  set e := |E|⁻¹ with he
  have hM0 := LiftHermitian_hsSq_nonneg M
  have hS1 : S ≤ D * (1 + e) ^ 2 * g ^ 2 * hsSq M := by
    rcases hS0.lt_or_eq with hpos | hzero
    · have h' : S * S ≤ S * (D * (1 + e) ^ 2 * g ^ 2 * hsSq M) := by
        calc S * S = S ^ 2 := (sq S).symm
          _ ≤ D * (1 + e) ^ 2 * g ^ 2 * S * hsSq M := hdY
          _ = S * (D * (1 + e) ^ 2 * g ^ 2 * hsSq M) := by ring
      exact le_of_mul_le_mul_left h' hpos
    · rw [← hzero]; positivity
  have hsm : ∑ r, (Real.sqrt 2 • (Aᵀ *ᵥ y)) r ^ 2 = 2 * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt (by norm_num)]
  rw [hsm]
  have hK : 0 ≤ D * (1 + e) ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · have h1 : 2 * S ≤ 2 * D * (1 + e) ^ 2 * g ^ 2 * hsSq M := by linarith
    have h2 : 2 * D * (1 + e) ^ 2 * g ^ 2 * hsSq M ≤
        (2 * D + C₀ * D) * (1 + e) ^ 2 * g ^ 2 * hsSq M := by
      have : 0 ≤ C₀ * D * (1 + e) ^ 2 * g ^ 2 * hsSq M := by positivity
      linarith
    linarith
  · have h1 : ∑ p, y p ^ 2 ≤ C₀ * g ^ 4 * (D * (1 + e) ^ 2 * g ^ 2 * hsSq M) :=
      hcY.trans (mul_le_mul_of_nonneg_left hS1 (by positivity))
    have h2 : C₀ * g ^ 4 * (D * (1 + e) ^ 2 * g ^ 2 * hsSq M) =
        C₀ * D * (1 + e) ^ 2 * g ^ 6 * hsSq M := by ring
    have h3 : 0 ≤ 2 * D * (1 + e) ^ 2 * g ^ 6 * hsSq M := by positivity
    have h4 : (2 * D + C₀ * D) * (1 + e) ^ 2 * g ^ 6 * hsSq M =
        2 * D * (1 + e) ^ 2 * g ^ 6 * hsSq M + C₀ * D * (1 + e) ^ 2 * g ^ 6 * hsSq M := by ring
    linarith

end LSBA
