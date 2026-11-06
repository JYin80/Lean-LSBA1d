import LSBA.Prop.Inputs
import LSBA.Prop.Comparison
import LSBA.Prop.Domination
import LSBA.Flow.Comparison

/-!
# Step 1 of the one-step propagation

Step 1 of Appendix C.3 [sec:gc-one-step] at each deterministic time: rough bounds, residual
moments and the Dyson closure ((5.38)′ [gc:eq:one-step] admissible steps, at fixed times).
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Vectors, Hilbert–Schmidt and operator norms -/

section LinAlg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Squared Euclidean norm of a vector. -/
private def step1_nsq (x : n → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

/-- Squared Hilbert–Schmidt norm of a square matrix. -/
private def step1_hs (A : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

omit [DecidableEq n] in
private lemma step1_nsq_nonneg (x : n → ℂ) : 0 ≤ step1_nsq x :=
  Finset.sum_nonneg fun _ _ => by positivity

omit [DecidableEq n] in
private lemma step1_hs_nonneg (A : Matrix n n ℂ) : 0 ≤ step1_hs A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

omit [DecidableEq n] in
private lemma step1_star_dot_self (x : n → ℂ) :
    star x ⬝ᵥ x = ((step1_nsq x : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', step1_nsq]
  push_cast
  rfl

omit [DecidableEq n] in
/-- Cauchy–Schwarz for the pairing `x* y`. -/
private lemma step1_cauchy (x y : n → ℂ) :
    ‖star x ⬝ᵥ y‖ ^ 2 ≤ step1_nsq x * step1_nsq y := by
  have h1 : ‖star x ⬝ᵥ y‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp
  calc ‖star x ⬝ᵥ y‖ ^ 2 ≤ (∑ i, ‖x i‖ * ‖y i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

omit [DecidableEq n] in
private lemma step1_dot_conjTranspose (M : Matrix n n ℂ) (u : n → ℂ) :
    star u ⬝ᵥ (Mᴴ *ᵥ u) = star (star u ⬝ᵥ (M *ᵥ u)) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star]

omit [DecidableEq n] in
/-- `‖M u‖² = u* (M* M) u`. -/
private lemma step1_nsq_mulVec (M : Matrix n n ℂ) (u : n → ℂ) :
    ((step1_nsq (M *ᵥ u) : ℝ) : ℂ) = star u ⬝ᵥ ((Mᴴ * M) *ᵥ u) := by
  rw [← step1_star_dot_self, Matrix.star_mulVec, ← Matrix.mulVec_mulVec u Mᴴ M,
    Matrix.dotProduct_mulVec (star u) Mᴴ]

omit [DecidableEq n] in
private lemma step1_ward_aux (G : Matrix n n ℂ) {η : ℝ} (hη : η ≠ 0)
    (h : Gᴴ * G = ((2 * η * Complex.I)⁻¹ : ℂ) • (G - Gᴴ)) (u : n → ℂ) :
    step1_nsq (G *ᵥ u) = (star u ⬝ᵥ (G *ᵥ u)).im / η := by
  have h3 : star u ⬝ᵥ ((Gᴴ * G) *ᵥ u) = ((2 * η * Complex.I)⁻¹ : ℂ) *
      (star u ⬝ᵥ (G *ᵥ u) - star (star u ⬝ᵥ (G *ᵥ u))) := by
    rw [h, Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul, dotProduct_sub,
      step1_dot_conjTranspose, smul_eq_mul]
  have h4 : ∀ w : ℂ, w - star w = ((2 * w.im : ℝ) : ℂ) * Complex.I := fun w => by
    apply Complex.ext <;> simp [two_mul]
  apply Complex.ofReal_injective
  rw [step1_nsq_mulVec, h3, h4]
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  push_cast
  field_simp

/-- Ward's identity for a resolvent: `‖G u‖² = Im ⟨u, G u⟩ / Im z`. -/
private lemma step1_ward_vec {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (u : n → ℂ) :
    step1_nsq (resolventMat A z *ᵥ u) = (star u ⬝ᵥ (resolventMat A z *ᵥ u)).im / z.im :=
  step1_ward_aux _ hz (ward_matrix hA hz) u

/-- Resolvent identity at two spectral points: `G(z) - G(w) = (z - w) G(z) G(w)`. -/
private lemma step1_resolvent_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    resolventMat A z - resolventMat A w = (z - w) • (resolventMat A z * resolventMat A w) := by
  have hAr := sub_smul_mul_resolventMat hA hz
  have hBr := sub_smul_mul_resolventMat hA hw
  have hAl := mul_eq_one_comm.mp hAr
  have hdiff : (A - w • (1 : Matrix n n ℂ)) - (A - z • (1 : Matrix n n ℂ)) =
      (z - w) • (1 : Matrix n n ℂ) := by
    rw [sub_smul]; abel
  have h1 : (z - w) • (resolventMat A z * resolventMat A w) =
      resolventMat A z * ((A - w • (1 : Matrix n n ℂ)) - (A - z • (1 : Matrix n n ℂ))) *
        resolventMat A w := by
    rw [hdiff, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [h1, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc (resolventMat A z) (A - w • (1 : Matrix n n ℂ)) (resolventMat A w), hBr,
    Matrix.mul_one, hAl, Matrix.one_mul]

/-- Row form of Ward's identity: `Σ_y |G_xy|² = Im G_xx / Im z`. -/
private lemma step1_ward_row {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (x : n) : ∑ y, ‖resolventMat A z x y‖ ^ 2 = (resolventMat A z x x).im / z.im := by
  have h := ward hA z.re hz x
  rw [Complex.re_add_im] at h
  exact h

/-- Column form of Ward's identity: `Σ_y |G_yx|² = Im G_xx / Im z`. -/
private lemma step1_ward_col {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (x : n) : ∑ y, ‖resolventMat A z y x‖ ^ 2 = (resolventMat A z x x).im / z.im := by
  have h := step1_ward_vec hA hz (Pi.single x 1)
  have e1 : resolventMat A z *ᵥ Pi.single x 1 = fun y => resolventMat A z y x := by
    funext y; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e1] at h
  have e2 : star (Pi.single x (1 : ℂ)) ⬝ᵥ (fun y => resolventMat A z y x) =
      resolventMat A z x x := by
    simp [dotProduct, Pi.single_apply]
  rw [e2] at h
  exact h

open scoped Matrix.Norms.L2Operator

/-- `‖A u‖² ≤ ‖A‖² ‖u‖²` for the operator norm. -/
private lemma step1_nsq_le_opNorm (A : Matrix n n ℂ) (u : n → ℂ) :
    step1_nsq (A *ᵥ u) ≤ ‖A‖ ^ 2 * step1_nsq u := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 u)
  have h1 : ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ u)‖ ^ 2 = step1_nsq (A *ᵥ u) := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ n)‖ ^ 2 = step1_nsq u := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  rw [← h1, ← h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- `|u'* (A u)| ≤ ‖A‖ ‖u'‖ ‖u‖`. -/
private lemma step1_bilin_le_opNorm (A : Matrix n n ℂ) (u' u : n → ℂ) :
    ‖star u' ⬝ᵥ (A *ᵥ u)‖ ≤ ‖A‖ * (Real.sqrt (step1_nsq u') * Real.sqrt (step1_nsq u)) := by
  have h1 := step1_cauchy u' (A *ᵥ u)
  have h2 := step1_nsq_le_opNorm A u
  have h3 : ‖star u' ⬝ᵥ (A *ᵥ u)‖ ^ 2 ≤
      (‖A‖ * (Real.sqrt (step1_nsq u') * Real.sqrt (step1_nsq u))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (step1_nsq_nonneg _), Real.sq_sqrt (step1_nsq_nonneg _)]
    calc _ ≤ step1_nsq u' * step1_nsq (A *ᵥ u) := h1
      _ ≤ step1_nsq u' * (‖A‖ ^ 2 * step1_nsq u) :=
        mul_le_mul_of_nonneg_left h2 (step1_nsq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

omit [DecidableEq n] in
/-- `‖A u‖² ≤ ‖A‖²_HS ‖u‖²`. -/
private lemma step1_nsq_le_hs (A : Matrix n n ℂ) (u : n → ℂ) :
    step1_nsq (A *ᵥ u) ≤ step1_hs A * step1_nsq u := by
  unfold step1_nsq step1_hs
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : ‖(A *ᵥ u) i‖ ≤ ∑ j, ‖A i j‖ * ‖u j‖ := by
    simp only [Matrix.mulVec, dotProduct]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  calc ‖(A *ᵥ u) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖u j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- The operator norm is at most the Hilbert–Schmidt norm. -/
private lemma step1_opNorm_sq_le_hs (A : Matrix n n ℂ) : ‖A‖ ^ 2 ≤ step1_hs A := by
  have hK : 0 ≤ Real.sqrt (step1_hs A) := Real.sqrt_nonneg _
  have hop : ‖A‖ ≤ Real.sqrt (step1_hs A) := by
    rw [Matrix.cstar_norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
    have h1 : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ^ 2 = step1_nsq (A *ᵥ x.ofLp) := by
      rw [EuclideanSpace.norm_sq_eq]; rfl
    have h2 : ‖x‖ ^ 2 = step1_nsq x.ofLp := by
      rw [EuclideanSpace.norm_sq_eq]; rfl
    have h3 := step1_nsq_le_hs A x.ofLp
    rw [← h1, ← h2] at h3
    have h4 : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ^ 2 ≤
        (Real.sqrt (step1_hs A) * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (step1_hs_nonneg _)]; exact h3
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h4
  calc ‖A‖ ^ 2 ≤ Real.sqrt (step1_hs A) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hop 2
    _ = _ := Real.sq_sqrt (step1_hs_nonneg _)

/-- Columnwise: `‖Y X‖²_HS ≤ ‖Y‖² ‖X‖²_HS`. -/
private lemma step1_hs_mul_left (Y X : Matrix n n ℂ) :
    step1_hs (Y * X) ≤ ‖Y‖ ^ 2 * step1_hs X := by
  unfold step1_hs
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖X i j‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := step1_nsq_le_opNorm Y (fun i => X i j)
  have e : (Y *ᵥ fun i => X i j) = fun i => (Y * X) i j := by
    funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [e] at h
  exact h

omit [DecidableEq n] in
private lemma step1_hs_conjTranspose (X : Matrix n n ℂ) : step1_hs Xᴴ = step1_hs X := by
  unfold step1_hs
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

/-- Rowwise: `‖X Y‖²_HS ≤ ‖Y‖² ‖X‖²_HS`. -/
private lemma step1_hs_mul_right (X Y : Matrix n n ℂ) :
    step1_hs (X * Y) ≤ ‖Y‖ ^ 2 * step1_hs X := by
  have h := step1_hs_mul_left Yᴴ Xᴴ
  rwa [← Matrix.conjTranspose_mul, step1_hs_conjTranspose, Matrix.l2_opNorm_conjTranspose,
    step1_hs_conjTranspose] at h

omit [DecidableEq n] in
/-- `|Tr(A B)| ≤ ‖A‖_HS ‖B‖_HS`. -/
private lemma step1_trace_mul_le (A B : Matrix n n ℂ) :
    ‖(A * B).trace‖ ≤ Real.sqrt (step1_hs A) * Real.sqrt (step1_hs B) := by
  have h1 : (A * B).trace = ∑ x : n × n, A x.1 x.2 * B x.2 x.1 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact (Fintype.sum_prod_type' _).symm
  have hA : step1_hs A = ∑ x : n × n, ‖A x.1 x.2‖ ^ 2 := (Fintype.sum_prod_type' _).symm
  have hB : step1_hs B = ∑ x : n × n, ‖B x.2 x.1‖ ^ 2 := by
    unfold step1_hs
    rw [Finset.sum_comm]
    exact (Fintype.sum_prod_type' (fun i j => ‖B j i‖ ^ 2)).symm
  rw [h1, hA, hB]
  calc ‖∑ x : n × n, A x.1 x.2 * B x.2 x.1‖ ≤ ∑ x : n × n, ‖A x.1 x.2‖ * ‖B x.2 x.1‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => norm_mul _ _))
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- For a Hermitian matrix, `‖A^(2^j)‖ = ‖A‖^(2^j)`. -/
private lemma step1_norm_pow_two_pow {A : Matrix n n ℂ} (hA : A.IsHermitian) (j : ℕ) :
    ‖A ^ (2 ^ j)‖ = ‖A‖ ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hH : (A ^ (2 ^ j))ᴴ = A ^ (2 ^ j) := by
      rw [Matrix.conjTranspose_pow, hA.eq]
    have e : A ^ (2 ^ (j + 1)) = (A ^ (2 ^ j))ᴴ * A ^ (2 ^ j) := by
      rw [hH, ← pow_add, pow_succ, mul_two]
    rw [e, Matrix.l2_opNorm_conjTranspose_mul_self, ih, ← pow_add, pow_succ 2 j, mul_two]

omit [DecidableEq n] in
/-- `Tr(Z* Z) = ‖Z‖²_HS`. -/
private lemma step1_trace_conjTranspose_mul_self (Z : Matrix n n ℂ) :
    (Zᴴ * Z).trace = ((step1_hs Z : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, step1_hs]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj']

/-- Positive loops bound the operator norm: `‖B‖^(2·2^j) ≤ Tr((B B*)^(2^j))`, and the trace is
real. -/
private lemma step1_opNorm_pow_le_trace (B : Matrix n n ℂ) (j : ℕ) :
    ((B * Bᴴ) ^ (2 ^ j)).trace = ((((B * Bᴴ) ^ (2 ^ j)).trace.re : ℝ) : ℂ) ∧
      ‖B‖ ^ (2 * 2 ^ j) ≤ ((B * Bᴴ) ^ (2 ^ j)).trace.re := by
  have hA : (B * Bᴴ).IsHermitian := by
    unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hnA : ‖B * Bᴴ‖ = ‖B‖ ^ 2 := by
    have := Matrix.l2_opNorm_conjTranspose_mul_self Bᴴ
    rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at this
    rw [this, sq]
  obtain ⟨Z, hZ, hnZ⟩ : ∃ Z : Matrix n n ℂ, (B * Bᴴ) ^ (2 ^ j) = Zᴴ * Z ∧
      ‖Z‖ ^ 2 = ‖B‖ ^ (2 * 2 ^ j) := by
    cases j with
    | zero =>
      refine ⟨Bᴴ, by simp, ?_⟩
      rw [Matrix.l2_opNorm_conjTranspose]; norm_num
    | succ j =>
      refine ⟨(B * Bᴴ) ^ (2 ^ j), ?_, ?_⟩
      · rw [Matrix.conjTranspose_pow, hA.eq, ← pow_add, pow_succ 2 j, mul_two]
      · rw [step1_norm_pow_two_pow hA, hnA, ← pow_mul, ← pow_mul, pow_succ 2 j]
  rw [hZ, step1_trace_conjTranspose_mul_self, Complex.ofReal_re]
  exact ⟨rfl, hnZ ▸ step1_opNorm_sq_le_hs Z⟩

end LinAlg

/-! ### Loops as traces of block products -/

section Loops

variable {W L : ℕ}

/-- The matrix whose block `(a, b)` is `B` and whose other blocks vanish. -/
private def step1_emb (a b : Fin L) (B : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.of fun x y => if x.1 = a ∧ y.1 = b then B x.2 y.2 else 0

/-- The projection `P_a` onto block `a`. -/
private def step1_proj (a : Fin L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.diagonal fun p => if p.1 = a then 1 else 0

private lemma step1_blockE_eq (a : Fin L) :
    blockE W L a = ((W : ℂ)⁻¹) • (step1_proj a : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy; by_cases h : x.1 = a <;> simp [blockE, step1_proj, h]
  · simp [blockE, step1_proj, Matrix.diagonal_apply_ne _ hxy]

private lemma step1_proj_eq_emb (a : Fin L) :
    (step1_proj a : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) = step1_emb a a 1 := by
  ext x y
  by_cases hxy : x = y
  · subst hxy; by_cases h : x.1 = a <;> simp [step1_emb, step1_proj, h]
  · simp only [step1_proj, Matrix.diagonal_apply_ne _ hxy, step1_emb, Matrix.of_apply]
    by_cases h1 : x.1 = a
    · by_cases h2 : y.1 = a
      · have h3 : x.2 ≠ y.2 := fun h => hxy (Prod.ext (h1.trans h2.symm) h)
        simp [h1, h2, Matrix.one_apply_ne h3]
      · simp [h2]
    · simp [h1]

private lemma step1_emb_mul (a b c : Fin L) (A B : Matrix (Fin W) (Fin W) ℂ) :
    step1_emb a b A * step1_emb b c B = step1_emb a c (A * B) := by
  ext x y
  simp only [step1_emb, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · by_cases hx : x.1 = a <;> by_cases hy : y.1 = c <;> simp [hx, hy]
  · intro e _ he; simp [he]
  · simp

private lemma step1_proj_mul_proj (a : Fin L) :
    (step1_proj a : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) * step1_proj a = step1_proj a := by
  rw [step1_proj_eq_emb, step1_emb_mul, Matrix.one_mul]

private lemma step1_proj_mul_mul_proj (a b : Fin L) (Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    step1_proj a * Y * step1_proj b = step1_emb a b (blockOf Y a b) := by
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  simp only [step1_proj, Matrix.diagonal_mul, Matrix.mul_diagonal, step1_emb, Matrix.of_apply,
    blockOf]
  by_cases hx : x1 = a <;> by_cases hy : y1 = b
  · subst hx; subst hy; simp
  all_goals simp [hx, hy]

private lemma step1_trace_emb (a : Fin L) (B : Matrix (Fin W) (Fin W) ℂ) :
    (step1_emb a a B).trace = B.trace := by
  simp only [Matrix.trace, Matrix.diag, step1_emb, Matrix.of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp
  · intro e _ he; simp [he]
  · simp

/-- The product of the blocks `Y_{c, a_1}, Y_{a_1, a_2}, …` along a list of pairs `(Y, a)`. -/
private def step1_chain : Fin L → List (Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ × Fin L) →
    Matrix (Fin W) (Fin W) ℂ
  | _, [] => 1
  | c, p :: l => blockOf p.1 c p.2 * step1_chain p.2 l

/-- The last label of a list of pairs (the start `c` if the list is empty). -/
private def step1_endLabel : Fin L → List (Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ × Fin L) →
    Fin L
  | c, [] => c
  | _, p :: l => step1_endLabel p.2 l

private lemma step1_endLabel_append (c : Fin L)
    (l : List (Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ × Fin L))
    (p : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ × Fin L) :
    step1_endLabel c (l ++ [p]) = p.2 := by
  induction l generalizing c with
  | nil => rfl
  | cons q l ih => exact ih q.2

private lemma step1_proj_mul_prod (c : Fin L)
    (l : List (Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ × Fin L)) :
    step1_proj c * (l.map fun p => p.1 * blockE W L p.2).prod =
      ((W : ℂ)⁻¹) ^ l.length • step1_emb c (step1_endLabel c l) (step1_chain c l) := by
  induction l generalizing c with
  | nil => simp [step1_endLabel, step1_chain, step1_proj_eq_emb]
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, step1_endLabel, step1_chain]
    set R := (List.map (fun p => p.1 * blockE W L p.2) l).prod with hR
    have e1 : step1_proj c * (p.1 * step1_proj p.2 * R) =
        (step1_proj c * p.1 * step1_proj p.2) * (step1_proj p.2 * R) := by
      rw [← Matrix.mul_assoc (step1_proj c * p.1 * step1_proj p.2),
        Matrix.mul_assoc (step1_proj c * p.1) (step1_proj p.2), step1_proj_mul_proj]
      simp only [Matrix.mul_assoc]
    rw [step1_blockE_eq]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, ih p.2, step1_proj_mul_mul_proj, Matrix.mul_smul, step1_emb_mul, smul_smul, pow_succ']

/-- A loop of length `k + 1` is `W^{-(k+1)}` times the trace of the product of its blocks
`(X^{σ_i})_{a_{i-1} a_i}`, with `a_{-1} = a_k`. -/
private lemma step1_loopTr_eq_chain (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {k : ℕ}
    (a : Fin (k + 1) → Fin L) (σ : Fin (k + 1) → Bool) :
    loopTr X a σ = ((W : ℂ)⁻¹) ^ (k + 1) *
      (step1_chain (a (Fin.last k)) (List.ofFn fun i => (sgnMat X (σ i), a i))).trace := by
  set c := a (Fin.last k) with hc
  set M := (List.ofFn fun i => sgnMat X (σ i) * blockE W L (a i)).prod with hM
  have hMl : M = ((List.ofFn fun i => (sgnMat X (σ i), a i)).map
      fun p => p.1 * blockE W L p.2).prod := by
    rw [hM, List.map_ofFn]; rfl
  have hMP : M * step1_proj c = M := by
    rw [hM, List.ofFn_succ', List.prod_concat, Matrix.mul_assoc, Matrix.mul_assoc,
      step1_blockE_eq, Matrix.smul_mul, step1_proj_mul_proj]
  have htr : loopTr X a σ = (step1_proj c * M).trace := by
    unfold loopTr
    rw [← hM, Matrix.trace_mul_comm, hMP]
  have hend : step1_endLabel c (List.ofFn fun i => (sgnMat X (σ i), a i)) = c := by
    rw [List.ofFn_succ', List.concat_eq_append, step1_endLabel_append]
  rw [htr, hMl, step1_proj_mul_prod, hend, Matrix.trace_smul, step1_trace_emb, List.length_ofFn,
    smul_eq_mul]

open scoped Matrix.Norms.L2Operator

private lemma step1_norm_one_le : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp

private lemma step1_chain_norm_le {O : ℝ} (hO0 : 0 ≤ O) (c : Fin L)
    (l : List (Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ × Fin L))
    (hO : ∀ p ∈ l, ∀ e, ‖blockOf p.1 e p.2‖ ≤ O) : ‖step1_chain c l‖ ≤ O ^ l.length := by
  induction l generalizing c with
  | nil => simpa [step1_chain] using step1_norm_one_le
  | cons p l ih =>
    simp only [step1_chain, List.length_cons, pow_succ']
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    exact mul_le_mul (hO p (by simp) c) (ih p.2 fun q hq => hO q (by simp [hq]))
      (norm_nonneg _) hO0

private lemma step1_chain_trace_le {O H : ℝ} (hO0 : 0 ≤ O) (hH0 : 0 ≤ H) (c : Fin L)
    (l : List (Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ × Fin L)) (hl : 2 ≤ l.length)
    (hO : ∀ p ∈ l, ∀ e, ‖blockOf p.1 e p.2‖ ≤ O)
    (hH : ∀ p ∈ l, ∀ e, step1_hs (blockOf p.1 e p.2) ≤ H) :
    ‖(step1_chain c l).trace‖ ≤ H * O ^ (l.length - 2) := by
  match l, hl with
  | p₀ :: p₁ :: l', _ =>
    simp only [step1_chain, List.length_cons]
    have h0 := hH p₀ (by simp) c
    have h1 := hH p₁ (by simp) p₀.2
    have hr := step1_chain_norm_le hO0 p₁.2 l' fun q hq => hO q (by simp [hq])
    have hr0 : 0 ≤ O ^ l'.length := pow_nonneg hO0 _
    have e : l'.length + 1 + 1 - 2 = l'.length := by omega
    rw [e]
    refine (step1_trace_mul_le _ _).trans ?_
    have h2 := step1_hs_mul_right (blockOf p₁.1 p₀.2 p₁.2) (step1_chain p₁.2 l')
    have h3 : step1_hs (blockOf p₁.1 p₀.2 p₁.2 * step1_chain p₁.2 l') ≤ (O ^ l'.length) ^ 2 * H :=
      h2.trans (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hr 2) h1 (step1_hs_nonneg _)
        (by positivity))
    calc Real.sqrt (step1_hs (blockOf p₀.1 c p₀.2)) *
          Real.sqrt (step1_hs (blockOf p₁.1 p₀.2 p₁.2 * step1_chain p₁.2 l'))
        ≤ Real.sqrt H * Real.sqrt ((O ^ l'.length) ^ 2 * H) :=
          mul_le_mul (Real.sqrt_le_sqrt h0) (Real.sqrt_le_sqrt h3) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = H * O ^ l'.length := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hr0, ← mul_assoc, mul_comm _ (O ^ _),
            mul_assoc, Real.mul_self_sqrt hH0, mul_comm]

private lemma step1_blockOf_conjTranspose (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (e f : Fin L) : blockOf Xᴴ e f = (blockOf X f e)ᴴ := by
  ext α β; simp [blockOf, Matrix.conjTranspose_apply]

private lemma step1_hs_blockOf (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (e f : Fin L) :
    step1_hs (blockOf X e f) = blockHS2 X e f := by
  simp [step1_hs, blockHS2, blockOf]

/-- `|ℒ_k| ≤ W^{-k} · H · O^{k-2}` for `k ≥ 2` when every block of `X` has operator norm at
most `O` and squared Hilbert–Schmidt norm at most `H`. -/
private lemma step1_loopTr_norm_le (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {k : ℕ}
    (hk : 2 ≤ k) (a : Fin k → Fin L) (σ : Fin k → Bool) {O H : ℝ} (hO0 : 0 ≤ O) (hH0 : 0 ≤ H)
    (hO : ∀ e f, ‖blockOf X e f‖ ≤ O) (hH : ∀ e f, blockHS2 X e f ≤ H) :
    ‖loopTr X a σ‖ ≤ ((W : ℝ)⁻¹) ^ k * (H * O ^ (k - 2)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hO' : ∀ s e f, ‖blockOf (sgnMat X s) e f‖ ≤ O := by
    intro s e f; cases s
    · simp only [sgnMat, Bool.false_eq_true, ↓reduceIte]
      rw [step1_blockOf_conjTranspose, Matrix.l2_opNorm_conjTranspose]; exact hO f e
    · exact hO e f
  have hH' : ∀ s e f, step1_hs (blockOf (sgnMat X s) e f) ≤ H := by
    intro s e f; cases s
    · simp only [sgnMat, Bool.false_eq_true, ↓reduceIte]
      rw [step1_blockOf_conjTranspose, step1_hs_conjTranspose, step1_hs_blockOf]; exact hH f e
    · rw [step1_hs_blockOf]; exact hH e f
  rw [step1_loopTr_eq_chain, norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h := step1_chain_trace_le hO0 hH0 (a (Fin.last k'))
    (List.ofFn fun i => (sgnMat X (σ i), a i)) (by simpa using hk)
    (fun p hp e => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      exact hO' _ _ _)
    (fun p hp e => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      exact hH' _ _ _)
  simpa using h

/-- The alternating chain `X_{cd}, X*_{dc}, …` of length `2p` is `(B B*)^p`, `B = X_{cd}`. -/
private lemma step1_chain_alt (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c d : Fin L) :
    ∀ p : ℕ, step1_chain c (List.ofFn fun i : Fin (2 * p) =>
      if i.val % 2 = 0 then (X, d) else (Xᴴ, c)) =
        (blockOf X c d * (blockOf X c d)ᴴ) ^ p
  | 0 => by simp [step1_chain]
  | p + 1 => by
    have ih := step1_chain_alt X c d p
    have e : (List.ofFn fun i : Fin (2 * (p + 1)) => if i.val % 2 = 0 then (X, d) else (Xᴴ, c)) =
        (X, d) :: (Xᴴ, c) :: List.ofFn fun i : Fin (2 * p) =>
          if i.val % 2 = 0 then (X, d) else (Xᴴ, c) := by
      rw [List.ofFn_succ (n := 2 * p + 1), List.ofFn_succ]
      simp only [Fin.val_zero, Nat.zero_mod, ↓reduceIte, Fin.val_succ]
      congr 2
      congr 1
      funext i
      have h2 : (i.val + 1 + 1) % 2 = 0 ↔ i.val % 2 = 0 := by omega
      simp only [h2]
    rw [e]
    simp only [step1_chain]
    rw [ih, step1_blockOf_conjTranspose, pow_succ', Matrix.mul_assoc]

end Loops

/-! ### Positive loops and the operator norm -/

section PosLoop

variable {W L : ℕ}

/-- The alternating loop
`ℒ_{2m}(d, c, d, c, …; +, -, +, -, …) = W^{-2m} Tr((X_{cd} X_{cd}^*)^m)`. -/
private lemma step1_loopTr_alt (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c d : Fin L)
    (m : ℕ) (hm : 1 ≤ m) :
    loopTr X (fun i : Fin (2 * m) => if i.val % 2 = 0 then d else c)
        (fun i => decide (i.val % 2 = 0)) =
      ((W : ℂ)⁻¹) ^ (2 * m) * ((blockOf X c d * (blockOf X c d)ᴴ) ^ m).trace := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  rw [step1_loopTr_eq_chain (k := 2 * p + 1)]
  have hlast : (if (Fin.last (2 * p + 1)).val % 2 = 0 then d else c) = c := by
    have h1 : (2 * p + 1) % 2 ≠ 0 := by omega
    simp only [Fin.val_last, h1, ↓reduceIte]
  have hl : (List.ofFn fun i : Fin (2 * p + 1 + 1) =>
      (sgnMat X (decide (i.val % 2 = 0)), if i.val % 2 = 0 then d else c)) =
      List.ofFn fun i : Fin (2 * (p + 1)) => if i.val % 2 = 0 then (X, d) else (Xᴴ, c) := by
    congr 1
    funext i
    by_cases h : i.val % 2 = 0 <;> simp [h, sgnMat]
  rw [hlast, hl, step1_chain_alt, show 2 * p + 1 + 1 = 2 * (p + 1) by ring]

open scoped Matrix.Norms.L2Operator

/-- A bound `T` on the positive `2·2^j`-loops at `(d, c)` gives
`‖X_{cd}‖^{2·2^j} ≤ W^{2·2^j} T`, as in (C.7) [fo:eq:starting-positive-loop]. -/
private lemma step1_opNorm_le_of_loop (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (c d : Fin L) (j : ℕ) (hW : 1 ≤ W) {T : ℝ}
    (h : ‖loopTr X (fun i : Fin (2 * 2 ^ j) => if i.val % 2 = 0 then d else c)
        (fun i => decide (i.val % 2 = 0))‖ ≤ T) :
    ‖blockOf X c d‖ ^ (2 * 2 ^ j) ≤ (W : ℝ) ^ (2 * 2 ^ j) * T := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [step1_loopTr_alt X c d (2 ^ j) Nat.one_le_two_pow] at h
  obtain ⟨hre, hle⟩ := step1_opNorm_pow_le_trace (blockOf X c d) j
  rw [hre, norm_mul, norm_pow, norm_inv, Complex.norm_natCast, Complex.norm_real,
    Real.norm_of_nonneg ((pow_nonneg (norm_nonneg _) _).trans hle)] at h
  have hWp : (0 : ℝ) < (W : ℝ) ^ (2 * 2 ^ j) := pow_pos hW0 _
  calc ‖blockOf X c d‖ ^ (2 * 2 ^ j) ≤ ((blockOf X c d * (blockOf X c d)ᴴ) ^ 2 ^ j).trace.re := hle
    _ = (W : ℝ) ^ (2 * 2 ^ j) * ((W : ℝ)⁻¹ ^ (2 * 2 ^ j) *
          ((blockOf X c d * (blockOf X c d)ᴴ) ^ 2 ^ j).trace.re) := by
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hW0.ne', one_pow, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h hWp.le

end PosLoop

/-! ### Resolvents on a vertical segment -/

section Segment

variable {W L : ℕ}

private lemma step1_blockTr_im (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a : Fin L)
    (hW : 1 ≤ W) : ∑ α : Fin W, (X (a, α) (a, α)).im = W * (blockTr X a a).im := by
  have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
  simp only [blockTr]
  rw [show ((W : ℂ)⁻¹) = (((W : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul,
    Complex.im_sum, ← mul_assoc, mul_inv_cancel₀ hW0, one_mul]

/-- Lipschitz bound in the height for the diagonal block traces of a resolvent:
`|⟨G(x+iy₁)⟩_aa - ⟨G(x+iy₂)⟩_aa| ≤ |y₁ - y₂| (Im⟨G₁⟩_aa/y₁)^{1/2} (Im⟨G₂⟩_aa/y₂)^{1/2}`. -/
private lemma step1_blockTr_lip {H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hH : H.IsHermitian) (hW : 1 ≤ W) (x y₁ y₂ : ℝ) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (a : Fin L) :
    ‖blockTr (resolventMat H ((x : ℂ) + (y₁ : ℂ) * Complex.I)) a a -
        blockTr (resolventMat H ((x : ℂ) + (y₂ : ℂ) * Complex.I)) a a‖ ≤
      |y₁ - y₂| * (Real.sqrt ((blockTr (resolventMat H ((x : ℂ) + (y₁ : ℂ) * Complex.I)) a a).im /
        y₁) * Real.sqrt ((blockTr (resolventMat H ((x : ℂ) + (y₂ : ℂ) * Complex.I)) a a).im /
        y₂)) := by
  set z₁ : ℂ := (x : ℂ) + (y₁ : ℂ) * Complex.I with hz₁
  set z₂ : ℂ := (x : ℂ) + (y₂ : ℂ) * Complex.I with hz₂
  have hi₁ : z₁.im = y₁ := by simp [hz₁]
  have hi₂ : z₂.im = y₂ := by simp [hz₂]
  set G₁ := resolventMat H z₁ with hG₁
  set G₂ := resolventMat H z₂ with hG₂
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hdiff := step1_resolvent_sub hH (z := z₁) (w := z₂) (by rw [hi₁]; exact hy₁.ne')
    (by rw [hi₂]; exact hy₂.ne')
  have hz : z₁ - z₂ = ((y₁ - y₂ : ℝ) : ℂ) * Complex.I := by
    rw [hz₁, hz₂]; push_cast; ring
  have e1 : blockTr G₁ a a - blockTr G₂ a a =
      (z₁ - z₂) * ((W : ℂ)⁻¹ * ∑ α : Fin W, (G₁ * G₂) (a, α) (a, α)) := by
    have : blockTr G₁ a a - blockTr G₂ a a = blockTr (G₁ - G₂) a a := by
      simp only [blockTr, Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]
    rw [this, hdiff]
    simp only [blockTr, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    ring
  -- rows and columns
  set r : Fin W → ℝ := fun α => ∑ v, ‖G₁ (a, α) v‖ ^ 2 with hr
  set k : Fin W → ℝ := fun α => ∑ v, ‖G₂ v (a, α)‖ ^ 2 with hk
  have hr' : ∀ α, r α = (G₁ (a, α) (a, α)).im / y₁ := fun α => by
    rw [hr, ← hi₁]; exact step1_ward_row hH (by rw [hi₁]; exact hy₁.ne') _
  have hk' : ∀ α, k α = (G₂ (a, α) (a, α)).im / y₂ := fun α => by
    rw [hk, ← hi₂]; exact step1_ward_col hH (by rw [hi₂]; exact hy₂.ne') _
  have hr0 : ∀ α, 0 ≤ r α := fun α => Finset.sum_nonneg fun _ _ => by positivity
  have hk0 : ∀ α, 0 ≤ k α := fun α => Finset.sum_nonneg fun _ _ => by positivity
  have hentry : ∀ α, ‖(G₁ * G₂) (a, α) (a, α)‖ ≤ Real.sqrt (r α) * Real.sqrt (k α) := by
    intro α
    rw [Matrix.mul_apply]
    calc ‖∑ v, G₁ (a, α) v * G₂ v (a, α)‖ ≤ ∑ v, ‖G₁ (a, α) v‖ * ‖G₂ v (a, α)‖ :=
          (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun v _ => norm_mul _ _))
      _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hsum : ‖∑ α : Fin W, (G₁ * G₂) (a, α) (a, α)‖ ≤
      Real.sqrt (∑ α, r α) * Real.sqrt (∑ α, k α) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun α _ => hentry α).trans ?_)
    have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun α => Real.sqrt (r α))
      (fun α => Real.sqrt (k α))
    simp only [Real.sq_sqrt (hr0 _), Real.sq_sqrt (hk0 _)] at this
    exact this
  have hR : ∑ α, r α = W * ((blockTr G₁ a a).im / y₁) := by
    simp only [hr']; rw [← Finset.sum_div, step1_blockTr_im G₁ a hW, mul_div_assoc]
  have hK : ∑ α, k α = W * ((blockTr G₂ a a).im / y₂) := by
    simp only [hk']; rw [← Finset.sum_div, step1_blockTr_im G₂ a hW, mul_div_assoc]
  have hI₁ : 0 ≤ (blockTr G₁ a a).im / y₁ := by
    have : 0 ≤ ∑ α, r α := Finset.sum_nonneg fun α _ => hr0 α
    rw [hR] at this; exact (mul_nonneg_iff_of_pos_left hW0).mp this
  have hI₂ : 0 ≤ (blockTr G₂ a a).im / y₂ := by
    have : 0 ≤ ∑ α, k α := Finset.sum_nonneg fun α _ => hk0 α
    rw [hK] at this; exact (mul_nonneg_iff_of_pos_left hW0).mp this
  rw [e1, norm_mul, hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [hR, hK, Real.sqrt_mul hW0.le, Real.sqrt_mul hW0.le] at hsum
  have hsW : Real.sqrt (W : ℝ) * Real.sqrt W = W := Real.mul_self_sqrt hW0.le
  calc (W : ℝ)⁻¹ * ‖∑ α : Fin W, (G₁ * G₂) (a, α) (a, α)‖
      ≤ (W : ℝ)⁻¹ * (Real.sqrt W * Real.sqrt ((blockTr G₁ a a).im / y₁) *
          (Real.sqrt W * Real.sqrt ((blockTr G₂ a a).im / y₂))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
        rw [show Real.sqrt W * Real.sqrt ((blockTr G₁ a a).im / y₁) *
            (Real.sqrt W * Real.sqrt ((blockTr G₂ a a).im / y₂)) =
            (Real.sqrt W * Real.sqrt W) * (Real.sqrt ((blockTr G₁ a a).im / y₁) *
              Real.sqrt ((blockTr G₂ a a).im / y₂)) by ring, hsW, ← mul_assoc,
          inv_mul_cancel₀ hW0.ne', one_mul]

end Segment

/-! ### Hilbert–Schmidt comparison on a vertical segment -/

section HSCmp

variable {W L : ℕ}

open scoped Matrix.Norms.L2Operator

/-- One row of `G F`: `Σ_β |(G F)_{(a,α),(b,β)}|² ≤ (Σ_v |G_{(a,α),v}|²) ‖F_{bb}‖ / Im w` for the
resolvent `F` at `w`. -/
private lemma step1_row_GF {H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hH : H.IsHermitian)
    {w : ℂ} (hw : 0 < w.im) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L)
    (α : Fin W) :
    ∑ β : Fin W, ‖(G * resolventMat H w) (a, α) (b, β)‖ ^ 2 ≤
      (∑ v, ‖G (a, α) v‖ ^ 2) * ‖blockOf (resolventMat H w) b b‖ / w.im := by
  set F := resolventMat H w with hF
  set c : Fin W → ℂ := fun β => (G * F) (a, α) (b, β) with hc
  set N : ℝ := ∑ β, ‖c β‖ ^ 2 with hN
  set e : Fin L × Fin W → ℂ := fun v => if v.1 = b then star (c v.2) else 0 with he
  set u : Fin L × Fin W → ℂ := fun v => star (G (a, α) v) with hu
  set eW : Fin W → ℂ := fun β => star (c β) with heW
  have hFe : ∀ v, (F *ᵥ e) v = ∑ β, F v (b, β) * star (c β) := by
    intro v
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, he]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'; simp [hb']
    · simp
  have hN1 : star u ⬝ᵥ (F *ᵥ e) = ((N : ℝ) : ℂ) := by
    simp only [dotProduct, hu, Pi.star_apply, star_star, hFe, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [hN]; push_cast
    refine Finset.sum_congr rfl fun β _ => ?_
    have : ∑ v, G (a, α) v * (F v (b, β) * star (c β)) = c β * star (c β) := by
      simp only [hc, Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [this, Complex.star_def, Complex.mul_conj']
  have hN2 : star e ⬝ᵥ (F *ᵥ e) = star eW ⬝ᵥ (blockOf F b b *ᵥ eW) := by
    have h1 : ∀ v : Fin L × Fin W, star (e v) * (F *ᵥ e) v =
        if v.1 = b then c v.2 * ∑ β, F v (b, β) * star (c β) else 0 := by
      intro v; rw [hFe]; by_cases h : v.1 = b <;> simp [he, h]
    simp only [dotProduct, Pi.star_apply, h1, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single b (by intro b' _ hb'; simp [hb']) (by simp)]
    simp [heW, Matrix.mulVec, dotProduct, blockOf]
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => by positivity
  have hnu : step1_nsq u = ∑ v, ‖G (a, α) v‖ ^ 2 := by simp [step1_nsq, hu]
  have hneW : step1_nsq eW = N := by simp [step1_nsq, heW, hN]
  have hC := step1_cauchy u (F *ᵥ e)
  rw [hN1, Complex.norm_real, Real.norm_of_nonneg hN0] at hC
  have hWd := step1_ward_vec hH hw.ne' e
  have hbil := step1_bilin_le_opNorm (blockOf F b b) eW eW
  rw [← hN2, hneW, ← Real.sqrt_mul hN0, Real.sqrt_mul_self hN0] at hbil
  have hFe2 : step1_nsq (F *ᵥ e) ≤ ‖blockOf F b b‖ * N / w.im := by
    rw [hWd]
    exact div_le_div_of_nonneg_right
      ((le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hbil)) hw.le
  rw [← hnu]
  rcases hN0.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact div_nonneg (mul_nonneg (step1_nsq_nonneg _) (norm_nonneg _)) hw.le
  · have h3 : N ^ 2 ≤ step1_nsq u * (‖blockOf F b b‖ * N / w.im) :=
      hC.trans (mul_le_mul_of_nonneg_left hFe2 (step1_nsq_nonneg _))
    have h4 : N * N ≤ (step1_nsq u * ‖blockOf F b b‖ / w.im) * N := by
      rw [← sq]; convert h3 using 1; ring
    exact le_of_mul_le_mul_right h4 hpos

/-- The Hilbert–Schmidt comparison (C.9) [fo:eq:step1-hs-comparison] for one Hermitian matrix:
for `z = x + iy`, `w = x + iy'`, `0 < y ≤ y'`,
`‖G(z)_{ab}‖²_HS ≤ 2‖G(w)_{ab}‖²_HS + 2 (y'/y) W Im⟨G(z)⟩_aa ‖G(w)_{bb}‖`. -/
private lemma step1_hs_cmp {H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hH : H.IsHermitian)
    (hW : 1 ≤ W) (x y y' : ℝ) (hy : 0 < y) (hyy : y ≤ y') (a b : Fin L) :
    blockHS2 (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a b ≤
      2 * blockHS2 (resolventMat H ((x : ℂ) + (y' : ℂ) * Complex.I)) a b +
        2 * (y' / y) * (W * (blockTr (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a a).im) *
          ‖blockOf (resolventMat H ((x : ℂ) + (y' : ℂ) * Complex.I)) b b‖ := by
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hz
  set w : ℂ := (x : ℂ) + (y' : ℂ) * Complex.I with hw
  have hzi : z.im = y := by simp [hz]
  have hwi : w.im = y' := by simp [hw]
  have hy' : 0 < y' := lt_of_lt_of_le hy hyy
  set G := resolventMat H z with hG
  set F := resolventMat H w with hF
  have hdiff := step1_resolvent_sub hH (z := z) (w := w) (by rw [hzi]; exact hy.ne')
    (by rw [hwi]; exact hy'.ne')
  have hGe : ∀ p q, G p q = F p q + (z - w) * (G * F) p q := by
    intro p q
    have := congrFun (congrFun hdiff p) q
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
    rw [← this]; ring
  have hzw : ‖z - w‖ ≤ y' := by
    have : z - w = ((y - y' : ℝ) : ℂ) * Complex.I := by rw [hz, hw]; push_cast; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have hrow : ∀ α, ∑ v, ‖G (a, α) v‖ ^ 2 = (G (a, α) (a, α)).im / y := fun α => by
    rw [← hzi]; exact step1_ward_row hH (by rw [hzi]; exact hy.ne') _
  have hrow0 : ∀ α, 0 ≤ (G (a, α) (a, α)).im / y := fun α => by
    rw [← hrow α]; exact Finset.sum_nonneg fun _ _ => by positivity
  have hB0 : 0 ≤ ‖blockOf F b b‖ := norm_nonneg _
  have hGF : ∑ α : Fin W, ∑ β : Fin W, ‖(G * F) (a, α) (b, β)‖ ^ 2 ≤
      (W * (blockTr G a a).im) / y * ‖blockOf F b b‖ / y' := by
    calc ∑ α : Fin W, ∑ β : Fin W, ‖(G * F) (a, α) (b, β)‖ ^ 2
        ≤ ∑ α : Fin W, (∑ v, ‖G (a, α) v‖ ^ 2) * ‖blockOf F b b‖ / y' := by
          refine Finset.sum_le_sum fun α _ => ?_
          rw [← hwi]; exact step1_row_GF hH (by rw [hwi]; exact hy') G a b α
      _ = (∑ α : Fin W, (G (a, α) (a, α)).im) / y * ‖blockOf F b b‖ / y' := by
          simp only [hrow]
          rw [← Finset.sum_div, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_div]
      _ = _ := by rw [step1_blockTr_im G a hW]
  have hpt : ∀ α β, ‖G (a, α) (b, β)‖ ^ 2 ≤
      2 * ‖F (a, α) (b, β)‖ ^ 2 + 2 * y' ^ 2 * ‖(G * F) (a, α) (b, β)‖ ^ 2 := by
    intro α β
    rw [hGe]
    have h1 := norm_add_le (F (a, α) (b, β)) ((z - w) * (G * F) (a, α) (b, β))
    rw [norm_mul] at h1
    have h2 : ‖z - w‖ * ‖(G * F) (a, α) (b, β)‖ ≤ y' * ‖(G * F) (a, α) (b, β)‖ :=
      mul_le_mul_of_nonneg_right hzw (norm_nonneg _)
    nlinarith [norm_nonneg (F (a, α) (b, β)), norm_nonneg ((G * F) (a, α) (b, β)),
      norm_nonneg (F (a, α) (b, β) + (z - w) * (G * F) (a, α) (b, β)),
      sq_nonneg (‖F (a, α) (b, β)‖ - y' * ‖(G * F) (a, α) (b, β)‖)]
  have hsum : blockHS2 G a b ≤ 2 * blockHS2 F a b +
      2 * y' ^ 2 * ∑ α : Fin W, ∑ β : Fin W, ‖(G * F) (a, α) (b, β)‖ ^ 2 := by
    unfold blockHS2
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun α _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun β _ => hpt α β
  have hIm : 0 ≤ (W : ℝ) * (blockTr G a a).im / y := by
    rw [← step1_blockTr_im G a hW, Finset.sum_div]
    exact Finset.sum_nonneg fun α _ => hrow0 α
  calc blockHS2 G a b ≤ 2 * blockHS2 F a b +
        2 * y' ^ 2 * ((W * (blockTr G a a).im) / y * ‖blockOf F b b‖ / y') :=
        hsum.trans (by gcongr)
    _ = _ := by field_simp

/-- `Im⟨G(x + iy)⟩_aa ≥ 0` for `y > 0`. -/
private lemma step1_im_blockTr_nonneg {H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hH : H.IsHermitian) (hW : 1 ≤ W) (x y : ℝ) (hy : 0 < y) (a : Fin L) :
    0 ≤ (blockTr (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a a).im := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hzi : ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
  have h := step1_blockTr_im (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a hW
  have hpos : 0 ≤
      ∑ α : Fin W, (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I) (a, α) (a, α)).im := by
    refine Finset.sum_nonneg fun α _ => ?_
    have hr := step1_ward_row hH (z := (x : ℂ) + (y : ℂ) * Complex.I) (by rw [hzi]; exact hy.ne')
      (a, α)
    rw [hzi] at hr
    have : 0 ≤ (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I) (a, α) (a, α)).im / y := by
      rw [← hr]; exact Finset.sum_nonneg fun _ _ => by positivity
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hy))
  rw [h] at hpos
  exact (mul_nonneg_iff_of_pos_left hW0).mp hpos

end HSCmp

/-! ### The Dyson matrix on a vertical segment -/

section DysonSeg

private lemma step1_cycleAdj_transpose (L : ℕ) : (cycleAdj L)ᵀ = cycleAdj L := by
  ext a b
  simp only [Matrix.transpose_apply, cycleAdj, Matrix.of_apply]
  exact add_comm _ _

/-- `(bA_L - z - βm)⁻¹` is symmetric. -/
private lemma step1_dysonMat_symm (b β : ℝ) (L : ℕ) (z m : ℂ) (a c : Fin L) :
    dysonMat b β L z m a c = dysonMat b β L z m c a := by
  have h : (dysonMat b β L z m)ᵀ = dysonMat b β L z m := by
    rw [dysonMat, Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_smul, step1_cycleAdj_transpose, Matrix.transpose_one]
  have := congrFun (congrFun h c) a
  rwa [Matrix.transpose_apply] at this

private lemma step1_smul_cycleAdj_isHermitian (b : ℝ) (L : ℕ) :
    (((b : ℝ) : ℂ) • cycleAdj L).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (cycleAdj_isHermitian L).eq, Complex.star_def, Complex.conj_ofReal]

/-- `M (bA_L - w) = 1` for the Dyson matrix at `w = z + βm`, `Im w > 0`. -/
private lemma step1_dysonMat_mul (b β : ℝ) (L : ℕ) (z m : ℂ) (hw : 0 < (z + β * m).im) :
    dysonMat b β L z m *
        (((b : ℝ) : ℂ) • cycleAdj L - (z + β * m) • (1 : Matrix (Fin L) (Fin L) ℂ)) = 1 :=
  mul_eq_one_comm.mp (sub_smul_mul_resolventMat (step1_smul_cycleAdj_isHermitian b L) hw.ne')

/-- Ward's identity for the Dyson matrix: `Σ_c |M_ac|² = Im M_aa / Im(z + βm)`. -/
private lemma step1_dysonMat_ward (b β : ℝ) (L : ℕ) (z m : ℂ) (hw : 0 < (z + β * m).im)
    (a : Fin L) :
    ∑ c, ‖dysonMat b β L z m a c‖ ^ 2 = (dysonMat b β L z m a a).im / (z + β * m).im := by
  have h := ward (step1_smul_cycleAdj_isHermitian b L) (z + β * m).re hw.ne' a
  rw [Complex.re_add_im] at h
  exact h

private lemma step1_blockTr_sub {W L : ℕ} (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockTr (X - Y) a b = blockTr X a b - blockTr Y a b := by
  unfold blockTr
  simp only [Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]

private lemma step1_blockTr_neg {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockTr (-X) a b = -blockTr X a b := by
  unfold blockTr
  simp only [Matrix.neg_apply, Finset.sum_neg_distrib, mul_neg]

private lemma step1_blockTr_add {W L : ℕ} (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockTr (X + Y) a b = blockTr X a b + blockTr Y a b := by
  unfold blockTr
  simp only [Matrix.add_apply, Finset.sum_add_distrib, mul_add]

private lemma step1_blockTr_smul {W L : ℕ} (c : ℂ) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockTr (c • X) a b = c * blockTr X a b := by
  unfold blockTr
  simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- `⟨M ⊗ I_W⟩_{ab} = M_{ab}` for `W ≥ 1`. -/
private lemma step1_blockTr_kron (W L : ℕ) (hW : 1 ≤ W) (M : Matrix (Fin L) (Fin L) ℂ)
    (a b : Fin L) : blockTr (M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) a b = M a b := by
  have hW0 : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold blockTr
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

private lemma step1_kron_mul_apply (W L : ℕ) (M : Matrix (Fin L) (Fin L) ℂ)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a : Fin L) (α : Fin W) (y : Fin L × Fin W) :
    ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * X) (a, α) y = ∑ c : Fin L, M a c * X (c, α) y := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp

private lemma step1_blockTr_mul_diag (W L : ℕ) (M : Matrix (Fin L) (Fin L) ℂ) (d : Fin L → ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    blockTr ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
        (Matrix.diagonal (fun x : Fin L × Fin W => d x.1) * G)) a b =
      ∑ c : Fin L, M a c * d c * blockTr G c b := by
  unfold blockTr
  simp only [step1_kron_mul_apply, Matrix.diagonal_mul]
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

private lemma step1_kron_inv (W L : ℕ) (Mb A : Matrix (Fin L) (Fin L) ℂ) (w : ℂ)
    (h : Mb * (A - w • (1 : Matrix (Fin L) (Fin L) ℂ)) = 1) :
    (Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
      (A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) -
        w • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) = 1 := by
  have e : A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) -
      w • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) =
      (A - w • (1 : Matrix (Fin L) (Fin L) ℂ)) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
    ext ⟨a, α⟩ ⟨b, β⟩
    simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply,
      Prod.mk.injEq, smul_eq_mul]
    by_cases hab : a = b <;> by_cases hαβ : α = β <;> simp [hab, hαβ]
  rw [e, ← Matrix.mul_kronecker_mul, h, Matrix.mul_one, Matrix.one_kronecker_one]

private lemma step1_identity (W L : ℕ) (Mb A : Matrix (Fin L) (Fin L) ℂ) (w z m β' : ℂ)
    (h : Mb * (A - w • (1 : Matrix (Fin L) (Fin L) ℂ)) = 1) (hz : z = w - β' * m)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    G - Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) =
      -((Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
        (1 + (z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) -
            A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * G +
          β' • (Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1) * G))) +
      β' • ((Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
        (Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1 - m) * G)) := by
  set K := Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) with hKdef
  have hK := step1_kron_inv W L Mb A w h
  rw [← hKdef] at hK
  have hKz : K * (z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) -
      A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) = -1 - (β' * m) • K := by
    have e : z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) -
        A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) =
        -(A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) -
          w • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) -
          (β' * m) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) := by
      rw [hz, sub_smul]; abel
    rw [e, Matrix.mul_sub, Matrix.mul_neg, hK, Matrix.mul_smul, Matrix.mul_one]
  have hD : Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1 - m) =
      Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1) -
        m • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) := by
    ext x y
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [Matrix.diagonal_apply_ne _ hxy, Matrix.one_apply_ne hxy]
  have e1 : K * ((1 + (z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) -
        A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * G +
          β' • (Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1) * G))) =
      K + (-G - (β' * m) • (K * G)) +
        β' • (K * (Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1) * G)) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hKz, Matrix.mul_smul]
    rw [sub_mul, Matrix.smul_mul, neg_mul, Matrix.one_mul]
  rw [e1, hD, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_smul]
  module

/-- The first identity of (5.32) [gc:eq:scalar] at a spectral point `z` of a vertical segment,
for a matrix `M` with `M (A_g - z - uγ_g m) = 1` and `M_cc = m`, and every matrix `G`:
`⟨G - M⊗I⟩_{ab} = -⟨(M⊗I) Π(G)⟩_{ab} + uγ_g Σ_c M_{ac} ⟨G - M⊗I⟩_{cc} ⟨G⟩_{cb}`. -/
private lemma step1_seg_identity (W L : ℕ) (hW : 1 ≤ W) (g u : ℝ) (z m : ℂ)
    (M : Matrix (Fin L) (Fin L) ℂ)
    (hMA : M * (Ag g L - (z + ((u * gammaG g : ℝ) : ℂ) * m) • (1 : Matrix (Fin L) (Fin L) ℂ)) = 1)
    (hdiag : ∀ c, M c c = m) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    blockTr (G - M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) a b =
      -blockTr ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * resPi g u z G) a b +
      ((u * gammaG g : ℝ) : ℂ) * ∑ c : Fin L, M a c *
        blockTr (G - M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c * blockTr G c b := by
  have key := step1_identity W L M (Ag g L) (z + ((u * gammaG g : ℝ) : ℂ) * m) z m
    ((u * gammaG g : ℝ) : ℂ) hMA (by ring) G
  have key' : G - M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) =
      -((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * resPi g u z G) +
        ((u * gammaG g : ℝ) : ℂ) • ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
          (Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1 - m) * G)) := by
    unfold resPi; exact key
  have hdg := step1_blockTr_mul_diag W L M (fun c => blockTr G c c - m) G a b
  have hcc : ∀ c, blockTr (G - M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c = blockTr G c c - m := by
    intro c; rw [step1_blockTr_sub, step1_blockTr_kron W L hW, hdiag]
  conv_lhs => rw [key']
  rw [step1_blockTr_add, step1_blockTr_neg, step1_blockTr_smul, hdg]
  simp only [hcc]

/-- `1 - Q` is invertible when every row sum of `|Q|` is at most `θ < 1`. -/
private lemma step1_isUnit_one_sub {L : ℕ} (Q : Matrix (Fin L) (Fin L) ℂ) {θ : ℝ} (hθ : θ < 1)
    (h : ∀ a, ∑ c, ‖Q a c‖ ≤ θ) : IsUnit (1 - Q) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hfix : ∀ a, v a = ∑ c, Q a c * v c := by
    intro a
    have := congrFun hv a
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply,
      sub_eq_zero] at this
    rw [this]; rfl
  set V := ⨆ a, ‖v a‖ with hV
  have hle : ∀ a, ‖v a‖ ≤ V := fun a =>
    le_ciSup (f := fun a => ‖v a‖) (Set.finite_range _).bddAbove a
  have hV0 : 0 ≤ V := Real.iSup_nonneg fun a => norm_nonneg _
  have hθ0 : 0 ≤ θ := by
    rcases isEmpty_or_nonempty (Fin L) with hL | ⟨⟨a⟩⟩
    · exact absurd (funext fun a => (hL.false a).elim) hv0
    · exact (Finset.sum_nonneg fun c _ => norm_nonneg _).trans (h a)
  have hVθ : V ≤ θ * V := by
    refine Real.iSup_le (fun a => ?_) (mul_nonneg hθ0 hV0)
    rw [hfix a]
    calc ‖∑ c, Q a c * v c‖ ≤ ∑ c, ‖Q a c‖ * V :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hle c) (norm_nonneg _))
      _ = (∑ c, ‖Q a c‖) * V := (Finset.sum_mul _ _ _).symm
      _ ≤ θ * V := mul_le_mul_of_nonneg_right (h a) hV0
  have hV00 : V = 0 := by nlinarith
  apply hv0
  funext a
  have := hle a
  rw [hV00] at this
  exact norm_le_zero_iff.mp this

/-- The rows of `Q = pairQ β M` above the real axis: `Σ_c |Q_ac| = β Im m / (Im z + β Im m)`. -/
private lemma step1_pairQ_row (b β : ℝ) (hβ : 0 ≤ β) (L : ℕ) (z m : ℂ) (hz : 0 < z.im)
    (hm : 0 < m.im) (hdiag : ∀ c, dysonMat b β L z m c c = m) (a : Fin L) :
    ∑ c, ‖pairQ β (dysonMat b β L z m) a c‖ = β * m.im / (z.im + β * m.im) := by
  have hw : 0 < (z + β * m).im := by
    have : (z + (β : ℂ) * m).im = z.im + β * m.im := by simp
    rw [this]; positivity
  have hward := step1_dysonMat_ward b β L z m hw a
  rw [hdiag a] at hward
  have : (z + (β : ℂ) * m).im = z.im + β * m.im := by simp
  rw [this] at hward
  simp only [pairQ, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ,
    norm_pow, ← Finset.mul_sum, hward]
  ring

/-- The closure inequality at one height: with `v_ab = ⟨G - M⟩_ab`, `|R| ≤ ρ`, `|⟨G⟩| ≤ Γ`,
`βΣ_c|M_ac| ≤ C`, rows of `(1 - Q)⁻¹` at most `C` and `|v_cc| ≤ U`,
`|v_aa| ≤ C(ρ + C U (ρ + C Γ U))`. -/
private lemma step1_closure_ineq {L : ℕ} (M : Matrix (Fin L) (Fin L) ℂ)
    (hMs : ∀ a c, M a c = M c a) (β : ℝ) (hβ : 0 ≤ β) (v g R : Fin L → Fin L → ℂ)
    (hid : ∀ a b, v a b = -R a b + (β : ℂ) * ∑ c, M a c * v c c * g c b)
    (hg : ∀ c b, g c b = M c b + v c b) {ρ Γ C U : ℝ} (hρ : ∀ a b, ‖R a b‖ ≤ ρ)
    (hΓ : ∀ a b, ‖g a b‖ ≤ Γ) (hrow : ∀ a, β * ∑ c, ‖M a c‖ ≤ C)
    (hinv : IsUnit (1 - pairQ β M)) (hrowinv : ∀ a, ∑ c, ‖(1 - pairQ β M)⁻¹ a c‖ ≤ C)
    (hU : ∀ c, ‖v c c‖ ≤ U) (hU0 : 0 ≤ U) (hΓ0 : 0 ≤ Γ) :
    ∀ a, ‖v a a‖ ≤ C * (ρ + C * U * (ρ + C * Γ * U)) := by
  have hρ0 : 0 ≤ ρ ∨ IsEmpty (Fin L) := by
    rcases isEmpty_or_nonempty (Fin L) with hL | ⟨⟨a⟩⟩
    · exact Or.inr hL
    · exact Or.inl ((norm_nonneg _).trans (hρ a a))
  have hoff : ∀ a b, ‖v a b‖ ≤ ρ + C * U * Γ := by
    intro a b
    rw [hid]
    have h1 : ‖(β : ℂ) * ∑ c, M a c * v c c * g c b‖ ≤ C * U * Γ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ]
      calc β * ‖∑ c, M a c * v c c * g c b‖ ≤ β * ∑ c, ‖M a c‖ * (U * Γ) := by
            refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
              (Finset.sum_le_sum fun c _ => ?_)) hβ
            rw [norm_mul, norm_mul, mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul (hU c) (hΓ c b) (norm_nonneg _) hU0)
              (norm_nonneg _)
        _ = (β * ∑ c, ‖M a c‖) * (U * Γ) := by rw [← Finset.sum_mul]; ring
        _ ≤ C * (U * Γ) := mul_le_mul_of_nonneg_right (hrow a) (mul_nonneg hU0 hΓ0)
        _ = C * U * Γ := by ring
    calc ‖-R a b + (β : ℂ) * ∑ c, M a c * v c c * g c b‖
        ≤ ‖R a b‖ + ‖(β : ℂ) * ∑ c, M a c * v c c * g c b‖ := by
          rw [← norm_neg (R a b)]; exact norm_add_le _ _
      _ ≤ ρ + C * U * Γ := add_le_add (hρ a b) h1
  set Q := pairQ β M with hQ
  set d : Fin L → ℂ := fun a => v a a with hd
  set e : Fin L → ℂ := fun a => (β : ℂ) * ∑ c, M a c * v c c * v c a with he
  have hlin : (1 - Q) *ᵥ d = fun a => -R a a + e a := by
    funext a
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, hd, he]
    have h := hid a a
    simp only [hg] at h
    have hQd : (Q *ᵥ fun a => v a a) a = (β : ℂ) * ∑ c, M a c * v c c * M c a := by
      simp only [Matrix.mulVec, dotProduct, hQ, pairQ, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hMs c a]; ring
    rw [hQd]
    conv_lhs => rw [h]
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  have hdinv : d = (1 - Q)⁻¹ *ᵥ ((1 - Q) *ᵥ d) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hinv),
      Matrix.one_mulVec]
  have hf : ∀ c, ‖-R c c + e c‖ ≤ ρ + C * U * (ρ + C * Γ * U) := by
    intro c
    have he1 : ‖e c‖ ≤ C * U * (ρ + C * Γ * U) := by
      simp only [he]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ]
      have hb : ∀ c', ‖v c' c‖ ≤ ρ + C * Γ * U := fun c' => by
        have := hoff c' c; linarith [mul_comm (C * U) Γ, show C * U * Γ = C * Γ * U by ring]
      have hpos : 0 ≤ ρ + C * Γ * U := (norm_nonneg _).trans (hb c)
      calc β * ‖∑ c', M c c' * v c' c' * v c' c‖ ≤ β * ∑ c', ‖M c c'‖ * (U * (ρ + C * Γ * U)) := by
            refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
              (Finset.sum_le_sum fun c' _ => ?_)) hβ
            rw [norm_mul, norm_mul, mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul (hU c') (hb c') (norm_nonneg _) hU0)
              (norm_nonneg _)
        _ = (β * ∑ c', ‖M c c'‖) * (U * (ρ + C * Γ * U)) := by rw [← Finset.sum_mul]; ring
        _ ≤ C * (U * (ρ + C * Γ * U)) :=
            mul_le_mul_of_nonneg_right (hrow c) (mul_nonneg hU0 hpos)
        _ = _ := by ring
    calc ‖-R c c + e c‖ ≤ ‖R c c‖ + ‖e c‖ := by rw [← norm_neg (R c c)]; exact norm_add_le _ _
      _ ≤ _ := add_le_add (hρ c c) he1
  intro a
  have hda : v a a = ((1 - Q)⁻¹ *ᵥ fun c => -R c c + e c) a := by
    have := congrFun hdinv a
    rw [hlin] at this
    exact this
  have hpos : 0 ≤ ρ + C * U * (ρ + C * Γ * U) := (norm_nonneg _).trans (hf a)
  rw [hda]
  simp only [Matrix.mulVec, dotProduct]
  calc ‖∑ c, (1 - Q)⁻¹ a c * (-R c c + e c)‖
      ≤ ∑ c, ‖(1 - Q)⁻¹ a c‖ * (ρ + C * U * (ρ + C * Γ * U)) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hf c) (norm_nonneg _))
    _ = (∑ c, ‖(1 - Q)⁻¹ a c‖) * (ρ + C * U * (ρ + C * Γ * U)) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrowinv a) hpos

/-- The dichotomy of the quadratic inequality `U ≤ a + bU²`: below `1/(2b)` it forces `U ≤ 2a`. -/
private lemma step1_dichotomy {U a b : ℝ} (hU : 0 ≤ U) (ha : 0 ≤ a)
    (h : U ≤ a + b * U ^ 2) (hsmall : 2 * b * U < 1) : U ≤ 2 * a := by
  by_contra hcon
  replace hcon := not_le.mp hcon
  have h1 : b * U ^ 2 < U / 2 := by
    have : b * U * U < U / 2 := by
      have hU' : 0 < U := by linarith
      nlinarith
    nlinarith
  linarith

end DysonSeg

/-! ### The two ends of a comparison segment -/

section Ends

private lemma step1_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

private lemma step1_hopB_nonneg {g : ℝ} (hg : 0 ≤ g) : 0 ≤ hopB g :=
  div_nonneg hg (le_trans zero_le_one (le_max_left _ _))

private lemma step1_xi_eq {g s u : ℝ} (hs : 0 < s) (hsu : s ≤ u) :
    xiCmp g s u = Real.sqrt (s / u) * max 1 g / max 1 (gCmp g s u) := by
  have hu : 0 < u := lt_of_lt_of_le hs hsu
  have hM : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hM' : 0 < max 1 (gCmp g s u) := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold xiCmp
  have e : s * gammaG (gCmp g s u) / (u * gammaG g) =
      (s / u) * (max 1 g / max 1 (gCmp g s u)) ^ 2 := by
    unfold gammaG; field_simp
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

/-- `0 < ξ ≤ 1`, `hopB g' = ξ hopB g`, `γ_{g'} = ξ² (u/s) γ_g` for `g' = g√(s/u)`,
Lemma 6.3(a) [da:lem:comparison-parameters]. -/
private lemma step1_xi_facts {g s u : ℝ} (hs : 0 < s) (hsu : s ≤ u) :
    0 < xiCmp g s u ∧ xiCmp g s u ≤ 1 ∧
      hopB (gCmp g s u) = xiCmp g s u * hopB g ∧
      gammaG (gCmp g s u) = xiCmp g s u ^ 2 * (u / s * gammaG g) := by
  have hu : 0 < u := lt_of_lt_of_le hs hsu
  set r := Real.sqrt (s / u) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr (by rw [div_le_one hu]; exact hsu)
  have hr2 : r ^ 2 = s / u := Real.sq_sqrt (by positivity)
  have hM : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hg' : gCmp g s u = g * r := rfl
  have hM' : 0 < max 1 (gCmp g s u) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hxi := step1_xi_eq (g := g) hs hsu
  rw [← hr] at hxi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hxi]; positivity
  · rw [hxi, div_le_one hM', mul_max_of_nonneg _ _ hr0.le, mul_one, hg']
    exact max_le_max hr1 (le_of_eq (mul_comm r g))
  · rw [hxi]; unfold hopB; rw [hg']; field_simp
  · rw [hxi]; unfold gammaG
    field_simp
    rw [hr2]; field_simp

private lemma step1_inv_smul {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ)
    {c : ℂ} (hc : c ≠ 0) : (c • B)⁻¹ = c⁻¹ • B⁻¹ := by
  by_cases h : IsUnit B.det
  · have := Matrix.inv_smul' B (Units.mk0 c hc) h
    rw [Units.smul_def, Units.val_mk0] at this
    rw [this, Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0]
  · have h' : ¬ IsUnit (c • B).det := by
      rw [isUnit_iff_ne_zero] at h ⊢
      rw [Matrix.det_smul]
      exact fun h0 => h (by simpa [hc] using h0)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h',
      smul_zero]

/-- At the lower end `y = η_u` of a segment the segment objects are those of the point:
`G = G_u(g, E)`, `M_u(z_u) = M_B ⊗ I` (the root at `(uγ_g, z_u)` is `m`). -/
private lemma step1_seg_lower (W : ℕ) (p : FlowPt) (hL : 3 ≤ p.L) (hg : 0 ≤ p.g)
    (hroot : IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E)) (hu0 : 0 < p.u)
    (hu : p.u < 1) :
    (∀ ω, segG W (p, etaChar p.g (mRoot p.g p.L p.E) p.u) ω = flowG W p ω) ∧
      segM W (p, etaChar p.g (mRoot p.g p.L p.E) p.u) = flowM W p := by
  set m := mRoot p.g p.L p.E with hm
  set zu := zChar p.g p.E m p.u with hzu
  have hγ := step1_gammaG_pos p.g
  have hz1 : ((zu.re : ℝ) : ℂ) + ((etaChar p.g m p.u : ℝ) : ℂ) * Complex.I = zu := by
    rw [← im_zChar p.g p.E m p.u, ← hzu, Complex.re_add_im]
  have hz2 : ((zu.re : ℝ) : ℂ) +
      ((gammaG p.g * (etaChar p.g m p.u / gammaG p.g) : ℝ) : ℂ) * Complex.I = zu := by
    rw [mul_div_cancel₀ _ hγ.ne', hz1]
  have hsum : zu + ((p.u * gammaG p.g : ℝ) : ℂ) * m = (p.E : ℂ) + ((gammaG p.g : ℝ) : ℂ) * m := by
    rw [hzu]; unfold zChar; push_cast; ring
  have hroot' : IsDysonRootV (hopB p.g) (p.u * gammaG p.g) p.L zu m := by
    refine ⟨hroot.1, ?_⟩
    unfold dysonRHSV
    rw [hsum]
    exact hroot.2
  have hzim : 0 ≤ zu.im := by
    rw [hzu, im_zChar]; exact (etaChar_pos p.g m hroot.1 hu).le
  have hsel : mRootV (hopB p.g) (p.u * gammaG p.g) p.L zu = m :=
    (mRootV_spec (hopB p.g) (p.u * gammaG p.g) (step1_hopB_nonneg hg) (by positivity) p.L hL zu
      hzim).2 m hroot'
  refine ⟨fun ω => ?_, ?_⟩
  · unfold segG flowG
    simp only
    rw [hz1]
  · unfold segM flowM segMat
    simp only
    rw [hz2, hsel]
    congr 1
    unfold dysonMat
    rw [hsum]

/-- At the upper end `y = Im w` of a comparison segment, with the endpoint identity
`w = ξ⁻¹ z_s(g', E')` and the root `m'` at the comparison point: `G = ξ G_s(g', E')` and
`M_u(w) = ξ M_B(g', E') ⊗ I` (the root at `(uγ_g, w)` is `ξ m'`). -/
private lemma step1_seg_upper (W : ℕ) (p : FlowPt) (s : ℝ) (hL : 3 ≤ p.L) (hg : 0 ≤ p.g)
    (hs : 0 < s) (hsu : s ≤ p.u)
    (hroot' : IsDysonRootV (hopB (cmpPt p s).g) (gammaG (cmpPt p s).g) p.L (cmpPt p s).E
      (mRoot (cmpPt p s).g p.L (cmpPt p s).E))
    (hre : (wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u).re =
      (zChar p.g p.E (mRoot p.g p.L p.E) p.u).re)
    (hwpos : 0 < (wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u).im)
    (hwid : wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u = ((xiCmp p.g s p.u : ℝ) : ℂ)⁻¹ *
      zChar (cmpPt p s).g (cmpPt p s).E (mRoot (cmpPt p s).g p.L (cmpPt p s).E) s) :
    (∀ ω, segG W (p, (wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u).im) ω =
        ((xiCmp p.g s p.u : ℝ) : ℂ) • flowG W (cmpPt p s) ω) ∧
      segM W (p, (wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u).im) =
        ((xiCmp p.g s p.u : ℝ) : ℂ) • flowM W (cmpPt p s) := by
  set w := wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u with hw
  set ξ := xiCmp p.g s p.u with hξ
  set g' := (cmpPt p s).g with hg'
  set E' := (cmpPt p s).E with hE'
  set m' := mRoot g' p.L E' with hm'
  have hγ := step1_gammaG_pos p.g
  have hu0 : 0 < p.u := lt_of_lt_of_le hs hsu
  obtain ⟨hξ0, -, hb, hγ'⟩ := step1_xi_facts (g := p.g) hs hsu
  have hb' : hopB g' = ξ * hopB p.g := hb
  have hγ'' : gammaG g' = ξ ^ 2 * (p.u / s * gammaG p.g) := hγ'
  have hξc : ((ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hξ0.ne'
  have hw1 : (((zChar p.g p.E (mRoot p.g p.L p.E) p.u).re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I
      = w := by rw [← hre, Complex.re_add_im]
  have hw2 : (((zChar p.g p.E (mRoot p.g p.L p.E) p.u).re : ℝ) : ℂ) +
      ((gammaG p.g * (w.im / gammaG p.g) : ℝ) : ℂ) * Complex.I = w := by
    rw [mul_div_cancel₀ _ hγ.ne', hw1]
  -- the matrix identity
  have hmat : ((hopB p.g : ℝ) : ℂ) • cycleAdj p.L -
        (w + ((p.u * gammaG p.g : ℝ) : ℂ) * (((ξ : ℝ) : ℂ) * m')) •
          (1 : Matrix (Fin p.L) (Fin p.L) ℂ) =
      (((ξ : ℝ) : ℂ))⁻¹ • (((hopB g' : ℝ) : ℂ) • cycleAdj p.L -
        ((E' : ℂ) + ((gammaG g' : ℝ) : ℂ) * m') • (1 : Matrix (Fin p.L) (Fin p.L) ℂ)) := by
    have e1 : (((ξ : ℝ) : ℂ))⁻¹ * ((hopB g' : ℝ) : ℂ) = ((hopB p.g : ℝ) : ℂ) := by
      rw [hb']; push_cast; field_simp
    have e2 : (((ξ : ℝ) : ℂ))⁻¹ * ((E' : ℂ) + ((gammaG g' : ℝ) : ℂ) * m') =
        w + ((p.u * gammaG p.g : ℝ) : ℂ) * (((ξ : ℝ) : ℂ) * m') := by
      rw [hwid]; unfold zChar; rw [hγ'']; push_cast
      have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      field_simp
      ring
    rw [smul_sub, smul_smul, smul_smul, e1, e2]
  have hM : dysonMat (hopB p.g) (p.u * gammaG p.g) p.L w (((ξ : ℝ) : ℂ) * m') =
      ((ξ : ℝ) : ℂ) • dysonMat (hopB g') (gammaG g') p.L E' m' := by
    unfold dysonMat
    rw [show ((p.u * gammaG p.g : ℝ) : ℂ) = ((p.u * gammaG p.g : ℝ) : ℂ) from rfl]
    rw [hmat, step1_inv_smul _ (inv_ne_zero hξc), inv_inv]
  have hL1 : 1 ≤ p.L := by omega
  have hm'pos := hroot'.1
  have hw' : 0 < (w + ((p.u * gammaG p.g : ℝ) : ℂ) * (((ξ : ℝ) : ℂ) * m')).im := by
    have : (w + ((p.u * gammaG p.g : ℝ) : ℂ) * (((ξ : ℝ) : ℂ) * m')).im =
        w.im + p.u * gammaG p.g * (ξ * m'.im) := by simp
    rw [this]; positivity
  have hw'' : 0 < ((E' : ℂ) + ((gammaG g' : ℝ) : ℂ) * m').im := by
    have : ((E' : ℂ) + ((gammaG g' : ℝ) : ℂ) * m').im = gammaG g' * m'.im := by simp
    rw [this]; exact mul_pos (step1_gammaG_pos _) hm'pos
  have hroot2 : IsDysonRootV (hopB p.g) (p.u * gammaG p.g) p.L w (((ξ : ℝ) : ℂ) * m') := by
    refine ⟨by simpa using mul_pos hξ0 hm'pos, ?_⟩
    have a0 : Fin p.L := ⟨0, by omega⟩
    have h1 := dysonMat_diag (hopB p.g) (p.u * gammaG p.g) p.L hL1 w (((ξ : ℝ) : ℂ) * m')
      (by exact_mod_cast hw') a0
    have h2 := dysonMat_diag (hopB g') (gammaG g') p.L hL1 E' m' (by exact_mod_cast hw'') a0
    rw [← h1, hM, Matrix.smul_apply, h2, ← hroot'.2, smul_eq_mul]
  have hsel : mRootV (hopB p.g) (p.u * gammaG p.g) p.L w = ((ξ : ℝ) : ℂ) * m' :=
    (mRootV_spec (hopB p.g) (p.u * gammaG p.g) (step1_hopB_nonneg hg) (by positivity) p.L hL w
      hwpos.le).2 _ hroot2
  refine ⟨fun ω => ?_, ?_⟩
  · unfold segG
    simp only
    rw [hw1]
    exact (flow_cmp_samplewise W p s hg hs hsu hwid ω).2
  · unfold segM flowM segMat
    simp only
    rw [hw2, hsel, hM, Matrix.smul_kronecker]
    rfl

end Ends

/-! ### The data of an admissible step point -/

section Facts

/-- `x = Re z_u` at a step point. -/
private def step1X (q : StepPt) : ℝ := (zChar q.g q.E (mRoot q.g q.L q.E) q.u).re

/-- `η_u` at a step point. -/
private def step1Eta (q : StepPt) : ℝ := etaChar q.g (mRoot q.g q.L q.E) q.u

/-- `Im w` of the comparison point of a step point. -/
private def step1Top (q : StepPt) : ℝ := (wCmp q.g q.L q.E (mRoot q.g q.L q.E) q.s q.u).im

/-- The comparison point `(g', E', L, s)` of a step point. -/
private def step1Cmp (q : StepPt) : FlowPt := cmpPt (q.at q.u) q.s

open scoped Matrix.Norms.L2Operator in
/-- The deterministic facts at an admissible step point for `W ≥ W₀`. -/
private structure Step1Facts (R : PropRegime) (c N : ℝ) (W : ℕ) (q : StepPt) : Prop where
  two_le : 2 ≤ W
  reach : ∃ d : ℕ, d < R.J ∧ CmpReach R.base W d (q.at q.u)
  L3 : 3 ≤ q.L
  g0 : 0 ≤ q.g
  root : IsDysonRootV (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E)
  mlo : R.C⁻¹ ≤ (mRoot q.g q.L q.E).im
  mhi : (mRoot q.g q.L q.E).im ≤ R.C
  Mbd : ∀ a b, ‖dysonMat (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E) a b‖ ≤ R.C
  root' : IsDysonRootV (hopB (step1Cmp q).g) (gammaG (step1Cmp q).g) q.L (step1Cmp q).E
    (mRoot (step1Cmp q).g q.L (step1Cmp q).E)
  Mbd' : ∀ a b, ‖dysonMat (hopB (step1Cmp q).g) (gammaG (step1Cmp q).g) q.L (step1Cmp q).E
    (mRoot (step1Cmp q).g q.L (step1Cmp q).E) a b‖ ≤ R.C
  re : (wCmp q.g q.L q.E (mRoot q.g q.L q.E) q.s q.u).re = step1X q
  etaw : step1Eta q ≤ step1Top q
  wle : step1Top q ≤ R.C * ((1 - q.s) / (1 - q.u)) * step1Eta q
  wid : wCmp q.g q.L q.E (mRoot q.g q.L q.E) q.s q.u = ((xiCmp q.g q.s q.u : ℝ) : ℂ)⁻¹ *
    zChar (step1Cmp q).g (step1Cmp q).E (mRoot (step1Cmp q).g q.L (step1Cmp q).E) q.s
  height : ∀ y : ℝ, step1Eta q ≤ y → y ≤ step1Top q →
    IsDysonRootV (hopB q.g) (q.u * gammaG q.g) q.L ((step1X q : ℂ) + (y : ℂ) * Complex.I)
        (mRootV (hopB q.g) (q.u * gammaG q.g) q.L ((step1X q : ℂ) + (y : ℂ) * Complex.I)) ∧
      (∀ a b, ‖segMat q.g q.L (step1X q) q.u (y / gammaG q.g) a b‖ ≤ R.C) ∧
      (∀ a, gammaG q.g * ∑ b,
        (‖segMat q.g q.L (step1X q) q.u (y / gammaG q.g) a b‖ +
         ‖segMat q.g q.L (step1X q) q.u (y / gammaG q.g) a b‖ ^ 2) ≤ R.C) ∧
      (∀ a, ∑ b, ‖(1 - pairQ (q.u * gammaG q.g)
        (segMat q.g q.L (step1X q) q.u (y / gammaG q.g)))⁻¹ a b‖ ≤ R.C) ∧
      (∀ a b, DifferentiableAt ℝ (fun r : ℝ => segMat q.g q.L (step1X q) q.u r a b)
        (y / gammaG q.g)) ∧
      ∀ a b, ‖deriv (fun r : ℝ => segMat q.g q.L (step1X q) q.u r a b) (y / gammaG q.g)‖ ≤ R.C
  s12 : 1 / 2 ≤ q.s
  su : q.s ≤ q.u
  ut : q.u ≤ q.t
  st : q.s < q.t
  t1 : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - q.t
  adm : q.ratio ^ N * zetaProp q.g W q.L q.t ≤ (W : ℝ) ^ (-c)
  cmp411 : ∀ ω : Ω W q.L,
    (∀ a b : Fin q.L, ‖blockOf (flowG W (q.at q.u) ω) a b‖ ≤ R.C * ((1 - q.s) / (1 - q.u)) *
      ⨆ c : Fin q.L, ⨆ e : Fin q.L, ‖blockOf (flowG W (step1Cmp q) ω) c e‖)
  zcmp : zetaProp (step1Cmp q).g W q.L q.s ≤ zetaProp q.g W q.L q.u

private lemma step1_facts (R : PropRegime) : ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ (c N : ℝ) (q : StepPt),
    StepAdm R c N W q → Step1Facts R c N W q := by
  obtain ⟨W₁, h₁⟩ := R.dyson
  obtain ⟨W₂, h₂⟩ := R.cmp
  obtain ⟨W₃, h₃⟩ := R.height
  obtain ⟨W₄, h₄⟩ := lemma411 R
  refine ⟨max 2 (max (max W₁ W₂) (max W₃ W₄)), fun W hW c N q hq => ?_⟩
  have hW2 : 2 ≤ W := (le_max_left _ _).trans hW
  have hW1 : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans
    ((le_max_right _ _).trans hW))
  have hW2' : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans
    ((le_max_right _ _).trans hW))
  have hW3 : W₃ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hW))
  have hW4 : W₄ ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hW))
  obtain ⟨⟨d, hd, hreach⟩, hs12, hsu, hut, hst, ht1, hadm⟩ := hq
  have hreach' : CmpReach R.base W d (q.at q.u) := CmpReach.earlier q.u hreach (hs12.trans hsu) hut
  obtain ⟨hL3, hg0, hroot, hmlo, hmhi, hMbd, -, -⟩ := h₁ W hW1 d (q.at q.u) hd.le hreach'
  have hreach2 : CmpReach R.base W (d + 1) (step1Cmp q) := CmpReach.cmp q.s hreach' hs12 hsu
  obtain ⟨-, -, hroot', -, -, hMbd', -, -⟩ := h₁ W hW1 (d + 1) (step1Cmp q) (by omega) hreach2
  obtain ⟨hre, hη1, hη2, hwid⟩ := h₂ W hW2' d (q.at q.u) q.s hd hreach' hs12 hsu
  have h411 := h₄ W hW4 d (q.at q.u) q.s hd hreach' hs12 hsu
  refine ⟨hW2, ⟨d, hd, hreach'⟩, hL3, hg0, hroot, hmlo, hmhi, hMbd, hroot', hMbd', hre, hη1, hη2,
    hwid, fun y hy1 hy2 => ?_, hs12, hsu, hut, hst, ht1, hadm, fun ω => (h411 ω).2.2.1,
    (h411 (fun _ => 0)).2.2.2.2.1⟩
  obtain ⟨hr, -, hb, hrow, hinv, hdiff, hder⟩ := h₃ W hW3 d (q.at q.u) q.s y hd hreach' hs12 hsu
    hy1 hy2
  exact ⟨hr, hb, hrow, hinv, hdiff, hder⟩

end Facts

/-! ### Numerical consequences of admissibility -/

section Num

/-- Times, the ratio `R = (1-s)/(1-t)`, and the scales at an admissible step point:
`1 ≤ R ≤ W³`, `(1-s)/(1-u) ≤ R`, `Im w ≤ C² γ_g`, `(2W)⁻¹ ≤ ζ_s(g') ≤ ζ_u(g)`, `(2W)⁻¹ ≤ ζ_u`,
`R³ ζ_u ≤ W^{-c}`, `0 < η_u ≤ Im w`. -/
private lemma step1_num {R : PropRegime} {c N : ℝ} {W : ℕ} {q : StepPt} (F : Step1Facts R c N W q)
    (hN : 20 ≤ N) :
    0 < 1 - q.t ∧ 0 < q.s ∧ q.u < 1 ∧ 1 ≤ q.ratio ∧ q.ratio ≤ (W : ℝ) ^ 3 ∧
      (1 - q.s) / (1 - q.u) ≤ q.ratio ∧ step1Top q ≤ R.C ^ 2 * gammaG q.g ∧
      (2 * (W : ℝ))⁻¹ ≤ zetaProp (step1Cmp q).g W q.L q.s ∧
      zetaProp (step1Cmp q).g W q.L q.s ≤ zetaProp q.g W q.L q.u ∧
      (2 * (W : ℝ))⁻¹ ≤ zetaProp q.g W q.L q.u ∧
      q.ratio ^ 3 * zetaProp q.g W q.L q.u ≤ (W : ℝ) ^ (-c) ∧
      0 < step1Eta q ∧ 0 < step1Top q ∧ q.ratio / (1 - q.u) ≤ (W : ℝ) ^ 6 := by
  have hW2 := F.two_le
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hW3 : (W : ℝ) ^ (-3 : ℝ) = ((W : ℝ) ^ 3)⁻¹ := by
    rw [Real.rpow_neg hW0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have ht := F.t1
  rw [hW3] at ht
  have hWp : 0 < (W : ℝ) ^ 3 := by positivity
  have ht0 : 0 < 1 - q.t := lt_of_lt_of_le (inv_pos.mpr hWp) ht
  have hs0 : 0 < q.s := by linarith [F.s12]
  have hu1 : q.u < 1 := by linarith [F.ut]
  have hs1 : 0 < 1 - q.s := by linarith [F.st]
  have hsh : 1 - q.s ≤ 1 / 2 := by linarith [F.s12]
  have hu1' : 0 < 1 - q.u := by linarith
  have hR1 : 1 ≤ q.ratio := by
    unfold StepPt.ratio; rw [le_div_iff₀ ht0]; linarith [F.st]
  have hR3 : q.ratio ≤ (W : ℝ) ^ 3 := by
    unfold StepPt.ratio
    rw [div_le_iff₀ ht0]
    have : (W : ℝ) ^ 3 * ((W : ℝ) ^ 3)⁻¹ = 1 := mul_inv_cancel₀ hWp.ne'
    nlinarith
  have hRu : (1 - q.s) / (1 - q.u) ≤ q.ratio := by
    unfold StepPt.ratio
    exact div_le_div_of_nonneg_left hs1.le ht0 (by linarith [F.ut])
  have hL1 : 1 ≤ q.L := by have := F.L3; omega
  have hg' : 0 ≤ (step1Cmp q).g := by
    change 0 ≤ gCmp q.g q.s q.u
    unfold gCmp; exact mul_nonneg F.g0 (Real.sqrt_nonneg _)
  have hsf' := scale_facts (step1Cmp q).g hg' W q.L (by omega) hL1 q.s q.s hs0.le le_rfl
    (by linarith [F.st, F.ut])
  have hsf := scale_facts q.g F.g0 W q.L (by omega) hL1 q.u q.t (by linarith [F.s12, F.su])
    F.ut (by linarith)
  have hR3' : q.ratio ^ 3 ≤ q.ratio ^ N := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by push_cast; linarith)
  have hzt : q.ratio ^ 3 * zetaProp q.g W q.L q.u ≤ (W : ℝ) ^ (-c) := by
    have hz0 : 0 ≤ zetaProp q.g W q.L q.u := (inv_nonneg.mpr (by positivity)).trans hsf.2.2.2.1
    calc q.ratio ^ 3 * zetaProp q.g W q.L q.u ≤ q.ratio ^ N * zetaProp q.g W q.L q.t :=
          mul_le_mul hR3' hsf.2.2.2.2.1 hz0 (Real.rpow_nonneg (by linarith) _)
      _ ≤ _ := F.adm
  have hmpos : 0 < (mRoot q.g q.L q.E).im :=
    lt_of_lt_of_le (inv_pos.mpr (lt_of_lt_of_le one_pos R.one_le_C)) F.mlo
  have heta : 0 < step1Eta q := etaChar_pos _ _ hmpos hu1
  have hTop : step1Top q ≤ R.C ^ 2 * gammaG q.g := by
    have h1 := F.wle
    have hC0 : 0 ≤ R.C := le_trans zero_le_one R.one_le_C
    have hγ0 : 0 < gammaG q.g := step1_gammaG_pos q.g
    have e : R.C * ((1 - q.s) / (1 - q.u)) * step1Eta q =
        R.C * (1 - q.s) * gammaG q.g * (mRoot q.g q.L q.E).im := by
      unfold step1Eta etaChar; field_simp
    rw [e] at h1
    calc step1Top q ≤ R.C * (1 - q.s) * gammaG q.g * (mRoot q.g q.L q.E).im := h1
      _ ≤ R.C * 1 * gammaG q.g * R.C := by
          gcongr
          · linarith
          · exact F.mhi
      _ = _ := by ring
  have hR6 : q.ratio / (1 - q.u) ≤ (W : ℝ) ^ 6 := by
    rw [div_le_iff₀ hu1']
    have h1 : 1 ≤ (W : ℝ) ^ 3 * (1 - q.u) := by
      have : ((W : ℝ) ^ 3)⁻¹ ≤ 1 - q.u := ht.trans (by linarith [F.ut])
      rw [inv_le_iff_one_le_mul₀ hWp] at this; linarith
    calc q.ratio ≤ (W : ℝ) ^ 3 := hR3
      _ ≤ (W : ℝ) ^ 3 * ((W : ℝ) ^ 3 * (1 - q.u)) := le_mul_of_one_le_right hWp.le h1
      _ = _ := by ring
  exact ⟨ht0, hs0, hu1, hR1, hR3, hRu, hTop, hsf'.2.2.2.1, F.zcmp, hsf.2.2.2.1, hzt, heta,
    lt_of_lt_of_le heta F.etaw, hR6⟩

end Num

/-! ### Rough bounds on the comparison segment -/

section Rough

/-- `ζ_s(g')` at the comparison point of a step point. -/
private def step1ZC (W : ℕ) (q : StepPt) : ℝ := zetaProp (step1Cmp q).g W q.L q.s

/-- `G_s(g', E')` at the comparison point, on the index set of the step point. -/
private def step1G' (W : ℕ) (q : StepPt) (ω : Ω W q.L) :
    Matrix (Fin q.L × Fin W) (Fin q.L × Fin W) ℂ :=
  flowG W (step1Cmp q) ω

/-- `M_B(g', E') ⊗ I` at the comparison point. -/
private def step1M' (W : ℕ) (q : StepPt) : Matrix (Fin q.L × Fin W) (Fin q.L × Fin W) ℂ :=
  flowM W (step1Cmp q)

/-- `M_B(g', E')` at the comparison point. -/
private def step1MB' (q : StepPt) : Matrix (Fin q.L) (Fin q.L) ℂ :=
  dysonMat (hopB (step1Cmp q).g) (gammaG (step1Cmp q).g) q.L (step1Cmp q).E
    (mRoot (step1Cmp q).g q.L (step1Cmp q).E)

open scoped Matrix.Norms.L2Operator in
/-- The bounds on `G_s(g', E')` that come from the input (5.22) [gc:eq:one-step-input] at the
comparison point, at accuracy `W^ε`: operator norms `≤ Wζ'`, Hilbert–Schmidt norms `≤ W²ζ'` and
centered block traces `≤ ζ'`. -/
private def step1GoodC (W : ℕ) (q : StepPt) (ε : ℝ) (ω : Ω W q.L) : Prop :=
  (∀ c e : Fin q.L, ‖blockOf (step1G' W q ω) c e‖ ≤ (W : ℝ) ^ ε * (W * step1ZC W q)) ∧
  (∀ c e : Fin q.L, blockHS2 (step1G' W q ω) c e ≤
    (W : ℝ) ^ ε * ((W : ℝ) ^ 2 * step1ZC W q)) ∧
  (∀ c e : Fin q.L, ‖blockTr (step1G' W q ω - step1M' W q) c e‖ ≤
    (W : ℝ) ^ ε * step1ZC W q)

/-- `G = (H_u - z)⁻¹` at `z = x + iy` on the segment of a step point. -/
private def step1Gy (W : ℕ) (q : StepPt) (y : ℝ) (ω : Ω W q.L) :
    Matrix (Fin q.L × Fin W) (Fin q.L × Fin W) ℂ :=
  segG W (q.at q.u, y) ω

/-- `M_u(z) ⊗ I` at `z = x + iy` on the segment of a step point. -/
private def step1My (W : ℕ) (q : StepPt) (y : ℝ) : Matrix (Fin q.L × Fin W) (Fin q.L × Fin W) ℂ :=
  segM W (q.at q.u, y)

/-- The residual `R_ab` at `z = x + iy` on the segment of a step point. -/
private def step1Res (W : ℕ) (q : StepPt) (y : ℝ) (ω : Ω W q.L) (a b : Fin q.L) : ℂ :=
  segRes W (q.at q.u, y) ω a b

private lemma step1_blockOf_smul {W L : ℕ} (ξ : ℂ) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (c d : Fin L) : blockOf (ξ • X) c d = ξ • blockOf X c d := by
  ext α β
  simp [blockOf]

private lemma step1_blockHS2_smul {W L : ℕ} (ξ : ℝ) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (c d : Fin L) : blockHS2 (((ξ : ℝ) : ℂ) • X) c d = ξ ^ 2 * blockHS2 X c d := by
  simp only [blockHS2, Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]

/-- `W^ε ζ_s(g') ≤ 1` and `W^ε ζ_u ≤ 1` for `ε ≤ c`. -/
private lemma step1_small {R : PropRegime} {c N : ℝ} {W : ℕ} {q : StepPt}
    (F : Step1Facts R c N W q) (hN : 20 ≤ N) {ε : ℝ} (hεc : ε ≤ c) :
    (W : ℝ) ^ ε * (q.ratio ^ 3 * zetaProp q.g W q.L q.u) ≤ 1 ∧
      (W : ℝ) ^ ε * zetaProp q.g W q.L q.u ≤ 1 ∧ (W : ℝ) ^ ε * step1ZC W q ≤ 1 := by
  obtain ⟨-, -, -, hR1, -, -, -, -, hzc, hz0, hzt, -, -, -⟩ := step1_num F hN
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by have := F.two_le; omega : 1 ≤ W)
  have hW0 : (0 : ℝ) < W := by linarith
  have hz : 0 ≤ zetaProp q.g W q.L q.u := (inv_nonneg.mpr (by positivity)).trans hz0
  have h1 : (W : ℝ) ^ ε * (q.ratio ^ 3 * zetaProp q.g W q.L q.u) ≤ 1 := by
    calc (W : ℝ) ^ ε * (q.ratio ^ 3 * zetaProp q.g W q.L q.u) ≤ (W : ℝ) ^ ε * (W : ℝ) ^ (-c) :=
          mul_le_mul_of_nonneg_left hzt (Real.rpow_nonneg hW0.le _)
      _ = (W : ℝ) ^ (ε - c) := by rw [← Real.rpow_add hW0]; ring_nf
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hR3 : 1 ≤ q.ratio ^ 3 := one_le_pow₀ hR1
  have h2 : (W : ℝ) ^ ε * zetaProp q.g W q.L q.u ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hz hR3)
      (Real.rpow_nonneg hW0.le _)) h1
  exact ⟨h1, h2, le_trans (mul_le_mul_of_nonneg_left hzc (Real.rpow_nonneg hW0.le _)) h2⟩

open scoped Matrix.Norms.L2Operator in
/-- The rough bounds (C.8) [fo:eq:rough-comparison] and (C.9) [fo:eq:step1-hs-comparison] on the
comparison segment `y ∈ [η_u, Im w]`, on the event of
`step1GoodC`: `|⟨G⟩_ab| ≤ 2C²R`, and `‖G_ab‖²_HS ≤ W^ε W² ζ' (2 + 2CR T)` whenever
`Im⟨G⟩_aa ≤ T` for all `a`. -/
private lemma step1_seg_bounds {R : PropRegime} {c N : ℝ} {W : ℕ} {q : StepPt}
    (F : Step1Facts R c N W q) (hN : 20 ≤ N) {ε : ℝ} (hεc : ε ≤ c) {ω : Ω W q.L}
    (hG : step1GoodC W q ε ω) {y : ℝ} (hy1 : step1Eta q ≤ y) (hy2 : y ≤ step1Top q) :
    (∀ a b : Fin q.L, ‖blockTr (step1Gy W q y ω) a b‖ ≤ 2 * R.C ^ 2 * q.ratio) ∧
    ∀ T : ℝ, 0 ≤ T → (∀ a, (blockTr (step1Gy W q y ω) a a).im ≤ T) →
      ∀ a b, blockHS2 (step1Gy W q y ω) a b ≤
        (W : ℝ) ^ ε * ((W : ℝ) ^ 2 * step1ZC W q) * (2 + 2 * R.C * q.ratio * T) := by
  obtain ⟨-, hs0, hu1, hR1, -, hRu, -, hzc0, -, -, -, heta, htop, -⟩ := step1_num F hN
  obtain ⟨-, -, hsm⟩ := step1_small F hN hεc
  have hW1 : 1 ≤ W := by have := F.two_le; omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hC1 := R.one_le_C
  have hC0 : 0 < R.C := lt_of_lt_of_le one_pos hC1
  set H := flowH q.g W q.L q.u ω with hH
  have hHh : H.IsHermitian := flowH_isHermitian _ _ _ _ _
  set x := step1X q with hx
  have hy0 : 0 < y := lt_of_lt_of_le heta hy1
  obtain ⟨hξ0, hξ1, -, -⟩ := step1_xi_facts (g := q.g) hs0 F.su
  obtain ⟨hup, -⟩ := step1_seg_upper W (q.at q.u) q.s F.L3 F.g0 hs0 F.su F.root' F.re htop F.wid
  have hF : resolventMat H ((x : ℂ) + ((step1Top q : ℝ) : ℂ) * Complex.I) =
      ((xiCmp q.g q.s q.u : ℝ) : ℂ) • step1G' W q ω := hup ω
  have hGy : step1Gy W q y ω = resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I) := rfl
  set ξ := xiCmp q.g q.s q.u with hξ
  have hzc : 0 ≤ step1ZC W q := (inv_nonneg.mpr (by positivity)).trans hzc0
  have hratio : step1Top q / y ≤ R.C * q.ratio := by
    rw [div_le_iff₀ hy0]
    calc step1Top q ≤ R.C * ((1 - q.s) / (1 - q.u)) * step1Eta q := F.wle
      _ ≤ R.C * q.ratio * y := by gcongr
  have hTy : 0 ≤ step1Top q / y := div_nonneg htop.le hy0.le
  -- the block traces of `G'`
  have hGC := hG.2.2
  have htrC : ∀ c e : Fin q.L, ‖blockTr (step1G' W q ω) c e‖ ≤ 2 * R.C := by
    intro c e
    have h1 := hGC c e
    have hk : blockTr (step1M' W q) c e = step1MB' q c e := step1_blockTr_kron W q.L hW1 _ c e
    rw [step1_blockTr_sub, hk] at h1
    have h2 : ‖step1MB' q c e‖ ≤ R.C := F.Mbd' c e
    calc ‖blockTr (step1G' W q ω) c e‖
        ≤ ‖blockTr (step1G' W q ω) c e - step1MB' q c e‖ + ‖step1MB' q c e‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ 1 + R.C := add_le_add (h1.trans hsm) h2
      _ ≤ 2 * R.C := by linarith
  have hB1 : ∀ a b : Fin q.L, ‖blockTr (step1Gy W q y ω) a b‖ ≤ 2 * R.C ^ 2 * q.ratio := by
    intro a b
    have hcmp := (resolvent_vertical_cmp H hHh ((x : ℂ) + (y : ℂ) * Complex.I)
      ((x : ℂ) + ((step1Top q : ℝ) : ℂ) * Complex.I) (by simp) (by simpa using hy0)
      (by simpa using hy2)).2.2 a b
    rw [hF] at hcmp
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at hcmp
    have hsup : ⨆ c : Fin q.L, ⨆ e : Fin q.L, ‖blockTr ((ξ : ℂ) • step1G' W q ω) c e‖ ≤
        2 * R.C := by
      refine Real.iSup_le (fun c => Real.iSup_le (fun e => ?_) (by positivity)) (by positivity)
      rw [step1_blockTr_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hξ0.le]
      exact (mul_le_of_le_one_left (norm_nonneg _) hξ1).trans (htrC c e)
    rw [hGy]
    calc _ ≤ _ := hcmp
      _ ≤ (R.C * q.ratio) * (2 * R.C) := mul_le_mul hratio hsup
          (Real.iSup_nonneg fun c => Real.iSup_nonneg fun e => norm_nonneg _) (by positivity)
      _ = 2 * R.C ^ 2 * q.ratio := by ring
  refine ⟨hB1, fun T hT0 hT a b => ?_⟩
  have hcmp := step1_hs_cmp hHh hW1 x y (step1Top q) hy0 hy2 a b
  rw [hF] at hcmp
  have e1 : blockHS2 (((ξ : ℝ) : ℂ) • step1G' W q ω) a b = ξ ^ 2 * blockHS2 (step1G' W q ω) a b :=
    step1_blockHS2_smul ξ _ a b
  have e2 : ‖blockOf (((ξ : ℝ) : ℂ) • step1G' W q ω) b b‖ = ξ * ‖blockOf (step1G' W q ω) b b‖ := by
    have h := step1_blockOf_smul (((ξ : ℝ) : ℂ)) (step1G' W q ω) b b
    rw [h, norm_smul, Complex.norm_real, Real.norm_of_nonneg hξ0.le]
  rw [e1, e2] at hcmp
  rw [hGy]
  have hξ2 : ξ ^ 2 ≤ 1 := by nlinarith
  have h1 : ξ ^ 2 * blockHS2 (step1G' W q ω) a b ≤ (W : ℝ) ^ ε * ((W : ℝ) ^ 2 * step1ZC W q) :=
    (mul_le_of_le_one_left (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
      hξ2).trans (hG.2.1 a b)
  have h2 : ξ * ‖blockOf (step1G' W q ω) b b‖ ≤ (W : ℝ) ^ ε * (W * step1ZC W q) :=
    (mul_le_of_le_one_left (norm_nonneg _) hξ1).trans (hG.1 b b)
  have h3 : (W : ℝ) * (blockTr (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a a).im ≤ W * T :=
    mul_le_mul_of_nonneg_left (hGy ▸ hT a) hW0.le
  have hWε : 0 ≤ (W : ℝ) ^ ε := Real.rpow_nonneg hW0.le _
  have hIm0 := step1_im_blockTr_nonneg hHh hW1 x y hy0 a
  have hprod : 2 * (step1Top q / y) *
      ((W : ℝ) * (blockTr (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a a).im) *
      (ξ * ‖blockOf (step1G' W q ω) b b‖) ≤
      2 * (R.C * q.ratio) * (W * T) * ((W : ℝ) ^ ε * (W * step1ZC W q)) := by
    apply mul_le_mul _ h2 (mul_nonneg hξ0.le (norm_nonneg _)) (by positivity)
    exact mul_le_mul (by linarith) h3 (mul_nonneg hW0.le hIm0) (by positivity)
  calc _ ≤ 2 * (ξ ^ 2 * blockHS2 (step1G' W q ω) a b) + 2 * (step1Top q / y) *
        ((W : ℝ) * (blockTr (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a a).im) *
        (ξ * ‖blockOf (step1G' W q ω) b b‖) := hcmp
    _ ≤ 2 * ((W : ℝ) ^ ε * ((W : ℝ) ^ 2 * step1ZC W q)) + 2 * (R.C * q.ratio) * (W * T) *
        ((W : ℝ) ^ ε * (W * step1ZC W q)) := add_le_add (by linarith) hprod
    _ = _ := by ring

end Rough

/-! ### The Dyson closure along the comparison segment -/

section Closure

/-- `M_u(z) = M_{B,u}(z)` at `z = x + iy`. -/
private lemma step1_segMat_eq (g : ℝ) (L : ℕ) (x u y : ℝ) :
    segMat g L x u (y / gammaG g) = dysonMat (hopB g) (u * gammaG g) L
      ((x : ℂ) + (y : ℂ) * Complex.I)
      (mRootV (hopB g) (u * gammaG g) L ((x : ℂ) + (y : ℂ) * Complex.I)) := by
  unfold segMat
  rw [mul_div_cancel₀ _ (step1_gammaG_pos g).ne']

/-- `⟨G - M_u(z)⟩_aa` on the segment at height `y`. -/
private def step1V (W : ℕ) (q : StepPt) (y : ℝ) (ω : Ω W q.L) (a : Fin q.L) : ℂ :=
  blockTr (step1Gy W q y ω - step1My W q y) a a

/-- `max_a |⟨G - M_u(z)⟩_aa|` on the segment at height `y`. -/
private def step1U (W : ℕ) (q : StepPt) (y : ℝ) (ω : Ω W q.L) : ℝ :=
  ⨆ a : Fin q.L, ‖step1V W q y ω a‖

private lemma step1_le_U (W : ℕ) (q : StepPt) (y : ℝ) (ω : Ω W q.L) (a : Fin q.L) :
    ‖step1V W q y ω a‖ ≤ step1U W q y ω :=
  le_ciSup (f := fun a => ‖step1V W q y ω a‖) (Set.finite_range _).bddAbove a

private lemma step1_U_nonneg (W : ℕ) (q : StepPt) (y : ℝ) (ω : Ω W q.L) : 0 ≤ step1U W q y ω :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- The quadratic inequality at one height of the segment (the two identities of (5.32)
[gc:eq:scalar] with the stability of (6.12) [gc:eq:positive-stability]–(6.14)
[da:eq:height-derivative]):
`U ≤ C(ρ + C U (ρ + C Γ U))` with `Γ = 2C²R` whenever the residual is at most `ρ`. -/
private lemma step1_quad {R : PropRegime} {c N : ℝ} {W : ℕ} {q : StepPt}
    (F : Step1Facts R c N W q) (hN : 20 ≤ N) {ε : ℝ} (hεc : ε ≤ c) {ω : Ω W q.L}
    (hG : step1GoodC W q ε ω) {y : ℝ} (hy1 : step1Eta q ≤ y) (hy2 : y ≤ step1Top q) {ρ : ℝ}
    (hres : ∀ a b, ‖step1Res W q y ω a b‖ ≤ ρ) :
    step1U W q y ω ≤ R.C * (ρ + R.C * step1U W q y ω *
      (ρ + R.C * (2 * R.C ^ 2 * q.ratio) * step1U W q y ω)) := by
  obtain ⟨-, -, hu1, hR1, -, -, -, -, -, -, -, heta, -, -⟩ := step1_num F hN
  have hB1 := (step1_seg_bounds F hN hεc hG hy1 hy2).1
  have hW1 : 1 ≤ W := by have := F.two_le; omega
  have hL1 : 1 ≤ q.L := by have := F.L3; omega
  have hy0 : 0 < y := lt_of_lt_of_le heta hy1
  have hγ := step1_gammaG_pos q.g
  have hu0 : 0 ≤ q.u := by linarith [F.s12, F.su]
  have hC1 := R.one_le_C
  obtain ⟨hroot, -, hrow, hinvrow, -, -⟩ := F.height y hy1 hy2
  set z : ℂ := (step1X q : ℂ) + (y : ℂ) * Complex.I with hz
  set my := mRootV (hopB q.g) (q.u * gammaG q.g) q.L z with hmy
  set M := dysonMat (hopB q.g) (q.u * gammaG q.g) q.L z my with hM
  have hseg : segMat q.g q.L (step1X q) q.u (y / gammaG q.g) = M := step1_segMat_eq _ _ _ _ _
  rw [hseg] at hrow hinvrow
  have hzi : z.im = y := by simp [hz]
  have hmy0 : 0 < my.im := hroot.1
  have hβ : 0 ≤ q.u * gammaG q.g := mul_nonneg hu0 hγ.le
  have hw : 0 < (z + ((q.u * gammaG q.g : ℝ) : ℂ) * my).im := by
    have : (z + ((q.u * gammaG q.g : ℝ) : ℂ) * my).im = y + q.u * gammaG q.g * my.im := by
      simp [hz]
    rw [this]; positivity
  have hdiag : ∀ c, M c c = my := fun c => by
    rw [hM, dysonMat_diag _ _ _ hL1 _ _ hw c]; exact hroot.2.symm
  have hMA := step1_dysonMat_mul (hopB q.g) (q.u * gammaG q.g) q.L z my hw
  have hsegM : step1My W q y = M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
    change segMat q.g q.L (step1X q) q.u (y / gammaG q.g) ⊗ₖ _ = _
    rw [hseg]
  set G := step1Gy W q y ω with hG'
  -- the abstract closure inequality
  have hid : ∀ a b, blockTr (G - M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) a b =
      -step1Res W q y ω a b + ((q.u * gammaG q.g : ℝ) : ℂ) * ∑ c, M a c *
        blockTr (G - M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c * blockTr G c b := by
    intro a b
    have h := step1_seg_identity W q.L hW1 q.g q.u z my M hMA hdiag G a b
    have hres' : step1Res W q y ω a b =
        blockTr ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * resPi q.g q.u z G) a b := by
      change blockTr (step1My W q y * resPi q.g q.u z G) a b = _
      rw [hsegM]
    rw [hres']; exact h
  have hg : ∀ c b, blockTr G c b = M c b + blockTr (G - M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c b :=
    fun c b => by rw [step1_blockTr_sub, step1_blockTr_kron W _ hW1]; ring
  have hrowM : ∀ a, q.u * gammaG q.g * ∑ c, ‖M a c‖ ≤ R.C := by
    intro a
    have h := hrow a
    have h1 : gammaG q.g * ∑ c, ‖M a c‖ ≤ gammaG q.g * ∑ c, (‖M a c‖ + ‖M a c‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => by nlinarith [norm_nonneg (M a c)])
        hγ.le
    have h2 : q.u * (gammaG q.g * ∑ c, ‖M a c‖) ≤ gammaG q.g * ∑ c, ‖M a c‖ :=
      mul_le_of_le_one_left (mul_nonneg hγ.le (Finset.sum_nonneg fun _ _ => norm_nonneg _))
        (by linarith)
    calc q.u * gammaG q.g * ∑ c, ‖M a c‖ = q.u * (gammaG q.g * ∑ c, ‖M a c‖) := by ring
      _ ≤ _ := h2.trans (h1.trans h)
  have hθ : q.u * gammaG q.g * my.im / (z.im + q.u * gammaG q.g * my.im) < 1 := by
    rw [div_lt_one (by rw [hzi]; positivity)]; rw [hzi]; linarith
  have hinv : IsUnit (1 - pairQ (q.u * gammaG q.g) M) :=
    step1_isUnit_one_sub _ hθ fun a => le_of_eq (step1_pairQ_row _ _ hβ _ z my
      (by rw [hzi]; exact hy0) hmy0 hdiag a)
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hres ⟨0, by omega⟩ ⟨0, by omega⟩)
  have hU : ∀ c, ‖blockTr (G - M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c‖ ≤ step1U W q y ω := by
    intro c
    have := step1_le_U W q y ω c
    unfold step1V at this
    rwa [hsegM] at this
  have hcl := step1_closure_ineq M (step1_dysonMat_symm _ _ _ _ _) (q.u * gammaG q.g) hβ
    (fun a b => blockTr (G - M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) a b)
    (fun a b => blockTr G a b) (fun a b => step1Res W q y ω a b) hid hg hres
    (fun a b => hB1 a b) hrowM hinv hinvrow hU (step1_U_nonneg W q y ω) (by positivity)
  refine Real.iSup_le (fun a => ?_) (by
    have := step1_U_nonneg W q y ω
    positivity)
  have := hcl a
  unfold step1V
  rw [hsegM]
  exact this

open scoped Matrix.Norms.L2Operator in
/-- Lipschitz continuity in the height: for `|y - y'| ≤ γ_g W^{-12}`,
`|⟨G - M⟩_aa(y')| ≤ |⟨G - M⟩_aa(y)| + 3C³W^{-6}`. -/
private lemma step1_lip {R : PropRegime} {c N : ℝ} {W : ℕ} {q : StepPt}
    (F : Step1Facts R c N W q) (hN : 20 ≤ N) {ε : ℝ} (hεc : ε ≤ c) {ω : Ω W q.L}
    (hG : step1GoodC W q ε ω) {y y' : ℝ} (hy1 : step1Eta q ≤ y) (hy2 : y ≤ step1Top q)
    (hy1' : step1Eta q ≤ y') (hy2' : y' ≤ step1Top q)
    (hδ : |y' - y| ≤ gammaG q.g / (W : ℝ) ^ 12) (a : Fin q.L) :
    ‖step1V W q y' ω a‖ ≤ ‖step1V W q y ω a‖ + 3 * R.C ^ 3 / (W : ℝ) ^ 6 := by
  obtain ⟨-, -, hu1, hR1, -, -, -, -, -, -, -, heta, -, hR6⟩ := step1_num F hN
  have hB1 := fun y hy1 hy2 => (step1_seg_bounds F hN hεc hG (y := y) hy1 hy2).1
  have hW1 : 1 ≤ W := by have := F.two_le; omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hγ := step1_gammaG_pos q.g
  have hC1 := R.one_le_C
  have hC0 : 0 < R.C := lt_of_lt_of_le one_pos hC1
  have hy0 : 0 < y := lt_of_lt_of_le heta hy1
  have hy0' : 0 < y' := lt_of_lt_of_le heta hy1'
  have hu1' : 0 < 1 - q.u := by linarith
  have hmlo := F.mlo
  have hm0 : 0 < (mRoot q.g q.L q.E).im := lt_of_lt_of_le (inv_pos.mpr hC0) hmlo
  set H := flowH q.g W q.L q.u ω with hH
  have hHh : H.IsHermitian := flowH_isHermitian _ _ _ _ _
  set x := step1X q with hx
  -- decomposition `v = ⟨G⟩ - M_aa`
  have hv : ∀ y, step1V W q y ω a = blockTr (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a a -
      segMat q.g q.L x q.u (y / gammaG q.g) a a := by
    intro y
    unfold step1V
    rw [step1_blockTr_sub]
    congr 1
    exact step1_blockTr_kron W q.L hW1 (segMat q.g q.L x q.u (y / gammaG q.g)) a a
  -- the resolvent part
  have hA : ∀ y, step1Eta q ≤ y → y ≤ step1Top q →
      (blockTr (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a a).im / y ≤
        2 * R.C ^ 2 * q.ratio / step1Eta q := by
    intro y h1 h2
    have hy0 : 0 < y := lt_of_lt_of_le heta h1
    have him := step1_im_blockTr_nonneg hHh hW1 x y hy0 a
    have hb : (blockTr (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a a).im ≤
        2 * R.C ^ 2 * q.ratio :=
      ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (hB1 y h1 h2 a a)
    calc _ ≤ (2 * R.C ^ 2 * q.ratio) / y := div_le_div_of_nonneg_right hb hy0.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) heta h1
  have hlipG := step1_blockTr_lip hHh hW1 x y' y hy0' hy0 a
  have hK0 : 0 ≤ 2 * R.C ^ 2 * q.ratio / step1Eta q := by positivity
  have hsq : Real.sqrt ((blockTr (resolventMat H ((x : ℂ) + (y' : ℂ) * Complex.I)) a a).im / y') *
      Real.sqrt ((blockTr (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a a).im / y) ≤
      2 * R.C ^ 2 * q.ratio / step1Eta q := by
    calc _ ≤ Real.sqrt (2 * R.C ^ 2 * q.ratio / step1Eta q) *
          Real.sqrt (2 * R.C ^ 2 * q.ratio / step1Eta q) :=
          mul_le_mul (Real.sqrt_le_sqrt (hA y' hy1' hy2')) (Real.sqrt_le_sqrt (hA y hy1 hy2))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hK0
  have hG1 : ‖blockTr (resolventMat H ((x : ℂ) + (y' : ℂ) * Complex.I)) a a -
      blockTr (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a a‖ ≤
        2 * R.C ^ 3 / (W : ℝ) ^ 6 := by
    have heta' : step1Eta q = (1 - q.u) * gammaG q.g * (mRoot q.g q.L q.E).im := rfl
    calc _ ≤ |y' - y| * (2 * R.C ^ 2 * q.ratio / step1Eta q) :=
          hlipG.trans (mul_le_mul_of_nonneg_left hsq (abs_nonneg _))
      _ ≤ gammaG q.g / (W : ℝ) ^ 12 * (2 * R.C ^ 2 * q.ratio / step1Eta q) :=
          mul_le_mul_of_nonneg_right hδ hK0
      _ = 2 * R.C ^ 2 * (q.ratio / (1 - q.u)) / ((mRoot q.g q.L q.E).im * (W : ℝ) ^ 12) := by
          rw [heta']; field_simp
      _ ≤ 2 * R.C ^ 2 * (W : ℝ) ^ 6 / (R.C⁻¹ * (W : ℝ) ^ 12) := by
          gcongr
      _ = 2 * R.C ^ 3 / (W : ℝ) ^ 6 := by field_simp
  -- the Dyson part, by the mean value theorem in `r = y/γ`
  have hM1 : ‖segMat q.g q.L x q.u (y' / gammaG q.g) a a -
      segMat q.g q.L x q.u (y / gammaG q.g) a a‖
      ≤ R.C / (W : ℝ) ^ 12 := by
    set s := Set.Icc (step1Eta q / gammaG q.g) (step1Top q / gammaG q.g) with hs
    have hmem : ∀ r ∈ s, step1Eta q ≤ gammaG q.g * r ∧ gammaG q.g * r ≤ step1Top q := by
      intro r hr
      obtain ⟨h1, h2⟩ := hr
      constructor
      · rw [div_le_iff₀ hγ] at h1; linarith
      · rw [le_div_iff₀ hγ] at h2; linarith
    have hdiff : ∀ r ∈ s, DifferentiableAt ℝ (fun r : ℝ => segMat q.g q.L x q.u r a a) r := by
      intro r hr
      obtain ⟨h1, h2⟩ := hmem r hr
      have := (F.height (gammaG q.g * r) h1 h2).2.2.2.2.1 a a
      rwa [mul_div_cancel_left₀ _ hγ.ne'] at this
    have hder : ∀ r ∈ s, ‖deriv (fun r : ℝ => segMat q.g q.L x q.u r a a) r‖ ≤ R.C := by
      intro r hr
      obtain ⟨h1, h2⟩ := hmem r hr
      have := (F.height (gammaG q.g * r) h1 h2).2.2.2.2.2 a a
      rwa [mul_div_cancel_left₀ _ hγ.ne'] at this
    have hys : y / gammaG q.g ∈ s := ⟨div_le_div_of_nonneg_right hy1 hγ.le,
      div_le_div_of_nonneg_right hy2 hγ.le⟩
    have hys' : y' / gammaG q.g ∈ s := ⟨div_le_div_of_nonneg_right hy1' hγ.le,
      div_le_div_of_nonneg_right hy2' hγ.le⟩
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hder (convex_Icc _ _) hys hys'
    calc _ ≤ R.C * ‖y' / gammaG q.g - y / gammaG q.g‖ := h
      _ = R.C * (|y' - y| / gammaG q.g) := by
          rw [← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos hγ]
      _ ≤ R.C * (gammaG q.g / (W : ℝ) ^ 12 / gammaG q.g) := by gcongr
      _ = R.C / (W : ℝ) ^ 12 := by field_simp
  rw [hv y', hv y]
  have hW6 : R.C / (W : ℝ) ^ 12 ≤ R.C ^ 3 / (W : ℝ) ^ 6 := by
    have hW12 : (W : ℝ) ^ 6 ≤ (W : ℝ) ^ 12 :=
      pow_le_pow_right₀ (by exact_mod_cast hW1) (by norm_num)
    have hC3 : R.C ≤ R.C ^ 3 := by nlinarith
    calc R.C / (W : ℝ) ^ 12 ≤ R.C / (W : ℝ) ^ 6 :=
          div_le_div_of_nonneg_left hC0.le (by positivity) hW12
      _ ≤ R.C ^ 3 / (W : ℝ) ^ 6 := div_le_div_of_nonneg_right hC3 (by positivity)
  calc _ = ‖(blockTr (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a a -
        segMat q.g q.L x q.u (y / gammaG q.g) a a) +
        ((blockTr (resolventMat H ((x : ℂ) + (y' : ℂ) * Complex.I)) a a -
          blockTr (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a a) -
        (segMat q.g q.L x q.u (y' / gammaG q.g) a a -
          segMat q.g q.L x q.u (y / gammaG q.g) a a))‖ := by congr 1; ring
    _ ≤ _ + (2 * R.C ^ 3 / (W : ℝ) ^ 6 + R.C / (W : ℝ) ^ 12) :=
        (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sub_le _ _).trans (add_le_add hG1 hM1)))
    _ ≤ _ := by
        have e1 : 2 * R.C ^ 3 / (W : ℝ) ^ 6 = 2 * (R.C ^ 3 / (W : ℝ) ^ 6) := by ring
        have e2 : 3 * R.C ^ 3 / (W : ℝ) ^ 6 = 3 * (R.C ^ 3 / (W : ℝ) ^ 6) := by ring
        rw [e1, e2]; linarith

end Closure

/-! ### The height mesh and the closure on it -/

section Mesh

/-- The mesh spacing `γ_g W^{-12}` in the height. -/
private def step1Del (W : ℕ) (q : StepPt) : ℝ := gammaG q.g / (W : ℝ) ^ 12

/-- The number of mesh steps from `Im w` down to `η_u`. -/
private def step1Nm (W : ℕ) (q : StepPt) : ℕ := ⌈(step1Top q - step1Eta q) / step1Del W q⌉₊

/-- The `k`-th mesh height `max(η_u, Im w - kδ)`. -/
private def step1Ym (W : ℕ) (q : StepPt) (k : ℕ) : ℝ :=
  max (step1Eta q) (step1Top q - k * step1Del W q)

/-- The residual bound at all mesh heights, at accuracy `W^ε`. -/
private def step1ResGood (R : PropRegime) (W : ℕ) (q : StepPt) (ε : ℝ) (ω : Ω W q.L) : Prop :=
  ∀ k, k ≤ step1Nm W q → ∀ a b, ‖step1Res W q (step1Ym W q k) ω a b‖ ≤
    (W : ℝ) ^ ε * (64 * R.C ^ 4 * q.ratio ^ 2 * zetaProp q.g W q.L q.u)

/-- `G_u(g, E)` at a step point, on its index set. -/
private def step1Gu (W : ℕ) (q : StepPt) (ω : Ω W q.L) :
    Matrix (Fin q.L × Fin W) (Fin q.L × Fin W) ℂ :=
  flowG W (q.at q.u) ω

/-- `M_B(g, E) ⊗ I` at a step point. -/
private def step1Mu (W : ℕ) (q : StepPt) : Matrix (Fin q.L × Fin W) (Fin q.L × Fin W) ℂ :=
  flowM W (q.at q.u)

private lemma step1_mesh {W : ℕ} {q : StepPt} (hδ : 0 < step1Del W q)
    (hηT : step1Eta q ≤ step1Top q) :
    (∀ k, step1Eta q ≤ step1Ym W q k ∧ step1Ym W q k ≤ step1Top q) ∧
      step1Ym W q 0 = step1Top q ∧ step1Ym W q (step1Nm W q) = step1Eta q ∧
      ∀ k, |step1Ym W q (k + 1) - step1Ym W q k| ≤ step1Del W q := by
  refine ⟨fun k => ⟨le_max_left _ _, max_le hηT ?_⟩, ?_, ?_, fun k => ?_⟩
  · have : 0 ≤ (k : ℝ) * step1Del W q := mul_nonneg (Nat.cast_nonneg k) hδ.le
    linarith
  · simp [step1Ym, hηT]
  · unfold step1Ym
    apply max_eq_left
    have h := Nat.le_ceil ((step1Top q - step1Eta q) / step1Del W q)
    rw [div_le_iff₀ hδ] at h
    unfold step1Nm
    linarith
  · unfold step1Ym
    have h := abs_max_sub_max_le_max (step1Eta q) (step1Top q - ((k + 1 : ℕ) : ℝ) * step1Del W q)
      (step1Eta q) (step1Top q - (k : ℝ) * step1Del W q)
    have h2 : max (0 : ℝ) |step1Top q - ((k + 1 : ℕ) : ℝ) * step1Del W q -
        (step1Top q - (k : ℝ) * step1Del W q)| = |step1Top q - ((k + 1 : ℕ) : ℝ) * step1Del W q -
        (step1Top q - (k : ℝ) * step1Del W q)| := max_eq_right (abs_nonneg _)
    rw [sub_self, abs_zero, h2] at h
    refine h.trans (le_of_eq ?_)
    push_cast
    rw [show step1Top q - (↑k + 1) * step1Del W q - (step1Top q - ↑k * step1Del W q) =
      -step1Del W q by ring, abs_neg, abs_of_pos hδ]

/-- The number of mesh heights is at most `C² W^{12} + 2`. -/
private lemma step1_Nm_le {R : PropRegime} {c N : ℝ} {W : ℕ} {q : StepPt}
    (F : Step1Facts R c N W q) (hN : 20 ≤ N) :
    ((step1Nm W q : ℕ) : ℝ) + 1 ≤ R.C ^ 2 * (W : ℝ) ^ 12 + 2 := by
  obtain ⟨-, -, -, -, -, -, hTop, -, -, -, -, heta, -, -⟩ := step1_num F hN
  have hγ := step1_gammaG_pos q.g
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by have := F.two_le; omega : 0 < W)
  have hδ : 0 < step1Del W q := by unfold step1Del; positivity
  have h1 := Nat.ceil_lt_add_one (show 0 ≤ (step1Top q - step1Eta q) / step1Del W q from
    div_nonneg (by linarith [F.etaw]) hδ.le)
  have h2 : (step1Top q - step1Eta q) / step1Del W q ≤ R.C ^ 2 * (W : ℝ) ^ 12 := by
    rw [div_le_iff₀ hδ]
    unfold step1Del
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith [pow_pos hW0 12]
  unfold step1Nm
  linarith

/-- The Dyson closure (C.14) [fo:eq:step1-dyson-closure] at the time `u`: on the events of
`step1GoodC` and `step1ResGood`, starting from the small branch at `Im w` (the input at the
comparison point) and descending along the mesh to `η_u`,
`|⟨G_u - M⟩_aa| ≤ 256 C⁵ W^ε R² ζ_u`. -/
private lemma step1_closure {R : PropRegime} {c N : ℝ} {W : ℕ} {q : StepPt}
    (F : Step1Facts R c N W q) (hN : 20 ≤ N) (hc : 0 < c) {ε : ℝ} (hεc : ε ≤ c / 4)
    (hbig1 : 4096 * R.C ^ 10 * (W : ℝ) ^ (-(3 * c / 4)) ≤ 1 / 2)
    (hbig2 : 48 * R.C ^ 8 ≤ (W : ℝ) ^ 3) {ω : Ω W q.L}
    (hG : step1GoodC W q ε ω) (hRes : step1ResGood R W q ε ω) (a : Fin q.L) :
    ‖blockTr (step1Gu W q ω - step1Mu W q) a a‖ ≤
      256 * R.C ^ 5 * ((W : ℝ) ^ ε * (q.ratio ^ 2 * zetaProp q.g W q.L q.u)) := by
  obtain ⟨-, hs0, hu1, hR1, hR3, -, -, -, hzc, hz0, hzt, heta, htop, -⟩ := step1_num F hN
  have hεc' : ε ≤ c := by linarith
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by have := F.two_le; omega : 1 ≤ W)
  have hW0 : (0 : ℝ) < W := by linarith
  have hC1 := R.one_le_C
  have hC0 : 0 < R.C := lt_of_lt_of_le one_pos hC1
  have hγ := step1_gammaG_pos q.g
  have hδ : 0 < step1Del W q := by unfold step1Del; positivity
  obtain ⟨hmem, hY0, hYN, hYstep⟩ := step1_mesh hδ F.etaw
  set ζ := zetaProp q.g W q.L q.u with hζ
  set Rt := q.ratio with hRt
  have hζ0 : 0 ≤ ζ := (inv_nonneg.mpr (by positivity)).trans hz0
  set B := (W : ℝ) ^ ε * (Rt ^ 3 * ζ) with hB
  have hWε : 0 < (W : ℝ) ^ ε := Real.rpow_pos_of_pos hW0 _
  have hB0 : 0 ≤ B := by positivity
  have hBc : B ≤ (W : ℝ) ^ (-(3 * c / 4)) := by
    calc B ≤ (W : ℝ) ^ ε * (W : ℝ) ^ (-c) := mul_le_mul_of_nonneg_left hzt hWε.le
      _ = (W : ℝ) ^ (ε - c) := by rw [← Real.rpow_add hW0]; ring_nf
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hR2 : Rt ^ 2 ≤ Rt ^ 3 := pow_le_pow_right₀ hR1 (by norm_num)
  have hR1' : Rt ≤ Rt ^ 3 := by
    calc Rt = Rt ^ 1 := (pow_one _).symm
      _ ≤ Rt ^ 3 := pow_le_pow_right₀ hR1 (by norm_num)
  -- the constants of the dichotomy
  set ρ := (W : ℝ) ^ ε * (64 * R.C ^ 4 * Rt ^ 2 * ζ) with hρ
  set Γ := 2 * R.C ^ 2 * Rt with hΓ
  set a₀ := 2 * R.C * ρ with ha₀
  set b₀ := 2 * R.C ^ 3 * Γ with hb₀
  set Lp := 3 * R.C ^ 3 / (W : ℝ) ^ 6 with hLp
  have hρB : ρ ≤ 64 * R.C ^ 4 * B := by
    have : (W : ℝ) ^ ε * (Rt ^ 2 * ζ) ≤ (W : ℝ) ^ ε * (Rt ^ 3 * ζ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR2 hζ0) hWε.le
    calc ρ = 64 * R.C ^ 4 * ((W : ℝ) ^ ε * (Rt ^ 2 * ζ)) := by rw [hρ]; ring
      _ ≤ 64 * R.C ^ 4 * B := mul_le_mul_of_nonneg_left this (by positivity)
  have hρ0 : 0 ≤ ρ := by positivity
  have hC10 : 0 < R.C ^ 10 := by positivity
  have hBsmall : 4096 * R.C ^ 10 * B ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_left hBc (by positivity)) hbig1
  have hC2ρ : R.C ^ 2 * ρ ≤ 1 / 2 := by
    have h6 : R.C ^ 6 ≤ R.C ^ 10 := pow_le_pow_right₀ hC1 (by norm_num)
    calc R.C ^ 2 * ρ ≤ R.C ^ 2 * (64 * R.C ^ 4 * B) := mul_le_mul_of_nonneg_left hρB (by positivity)
      _ = 64 * R.C ^ 6 * B := by ring
      _ ≤ 4096 * R.C ^ 10 * B := by gcongr; norm_num
      _ ≤ 1 / 2 := hBsmall
  -- one step: `U ≤ a₀ + b₀ U²`, hence the dichotomy
  have hstep : ∀ k, k ≤ step1Nm W q → 2 * b₀ * step1U W q (step1Ym W q k) ω < 1 →
      step1U W q (step1Ym W q k) ω ≤ 2 * a₀ := by
    intro k hk hsmall
    obtain ⟨h1, h2⟩ := hmem k
    have hq := step1_quad F hN hεc' hG h1 h2 (hRes k hk)
    set U := step1U W q (step1Ym W q k) ω with hU
    have hU0 : 0 ≤ U := step1_U_nonneg _ _ _ _
    have hquad : U ≤ a₀ + b₀ * U ^ 2 := by
      have e : R.C * (ρ + R.C * U * (ρ + R.C * Γ * U)) =
          R.C * ρ + (R.C ^ 2 * ρ) * U + R.C ^ 3 * Γ * U ^ 2 := by ring
      rw [e] at hq
      have : (R.C ^ 2 * ρ) * U ≤ 1 / 2 * U := mul_le_mul_of_nonneg_right hC2ρ hU0
      rw [ha₀, hb₀]; linarith
    exact step1_dichotomy hU0 (by positivity) hquad hsmall
  -- the start at `Im w`
  obtain ⟨hξ0, hξ1, -, -⟩ := step1_xi_facts (g := q.g) hs0 F.su
  have hup := step1_seg_upper W (q.at q.u) q.s F.L3 F.g0 hs0 F.su F.root' F.re htop F.wid
  have hGT : step1Gy W q (step1Top q) ω = ((xiCmp q.g q.s q.u : ℝ) : ℂ) • step1G' W q ω :=
    hup.1 ω
  have hMT : step1My W q (step1Top q) = ((xiCmp q.g q.s q.u : ℝ) : ℂ) • step1M' W q := hup.2
  have hU0 : step1U W q (step1Top q) ω ≤ (W : ℝ) ^ ε * ζ := by
    refine Real.iSup_le (fun a => ?_) (by positivity)
    unfold step1V
    rw [hGT, hMT, ← smul_sub, step1_blockTr_smul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hξ0.le]
    calc xiCmp q.g q.s q.u * ‖blockTr (step1G' W q ω - step1M' W q) a a‖
        ≤ 1 * ((W : ℝ) ^ ε * step1ZC W q) :=
          mul_le_mul hξ1 (hG.2.2 a a) (norm_nonneg _) zero_le_one
      _ ≤ _ := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hzc hWε.le
  have hb0 : 0 ≤ b₀ := by positivity
  have hstart : 2 * b₀ * step1U W q (step1Ym W q 0) ω < 1 := by
    rw [hY0]
    calc 2 * b₀ * step1U W q (step1Top q) ω ≤ 2 * b₀ * ((W : ℝ) ^ ε * ζ) :=
          mul_le_mul_of_nonneg_left hU0 (by positivity)
      _ = 8 * R.C ^ 5 * ((W : ℝ) ^ ε * (Rt * ζ)) := by rw [hb₀, hΓ]; ring
      _ ≤ 8 * R.C ^ 5 * B := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hB]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR1' hζ0) hWε.le
      _ ≤ 4096 * R.C ^ 10 * B := by
          have h5 : R.C ^ 5 ≤ R.C ^ 10 := pow_le_pow_right₀ hC1 (by norm_num)
          gcongr; norm_num
      _ < 1 := by linarith
  -- propagation down the mesh
  have hprop : 2 * b₀ * (2 * a₀ + Lp) < 1 := by
    have h1 : 2 * b₀ * (2 * a₀) ≤ 2048 * R.C ^ 10 * B := by
      refine le_of_eq ?_
      rw [ha₀, hb₀, hΓ, hρ, hB]; ring
    have h2 : 2 * b₀ * Lp ≤ 24 * R.C ^ 8 / (W : ℝ) ^ 3 := by
      have e : 2 * b₀ * Lp = 24 * R.C ^ 8 * Rt / (W : ℝ) ^ 6 := by rw [hb₀, hΓ, hLp]; ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      calc 24 * R.C ^ 8 * Rt * (W : ℝ) ^ 3 ≤ 24 * R.C ^ 8 * (W : ℝ) ^ 3 * (W : ℝ) ^ 3 := by gcongr
        _ = 24 * R.C ^ 8 * (W : ℝ) ^ 6 := by ring
    have h3 : 24 * R.C ^ 8 / (W : ℝ) ^ 3 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hind : ∀ k, k ≤ step1Nm W q → step1U W q (step1Ym W q k) ω ≤ 2 * a₀ := by
    intro k
    induction k with
    | zero => exact fun hk => hstep 0 hk hstart
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      obtain ⟨h1, h2⟩ := hmem k
      obtain ⟨h1', h2'⟩ := hmem (k + 1)
      have hlip : step1U W q (step1Ym W q (k + 1)) ω ≤ step1U W q (step1Ym W q k) ω + Lp := by
        refine Real.iSup_le (fun a => ?_) (by
          have := step1_U_nonneg W q (step1Ym W q k) ω; positivity)
        have := step1_lip F hN hεc' hG h1 h2 h1' h2' (hYstep k) a
        exact this.trans (add_le_add (step1_le_U _ _ _ _ a) le_rfl)
      refine hstep (k + 1) hk ?_
      calc 2 * b₀ * step1U W q (step1Ym W q (k + 1)) ω ≤ 2 * b₀ * (2 * a₀ + Lp) :=
            mul_le_mul_of_nonneg_left (hlip.trans (by linarith)) (by positivity)
        _ < 1 := hprop
  have hfin := hind (step1Nm W q) le_rfl
  rw [hYN] at hfin
  have hlow := step1_seg_lower W (q.at q.u) F.L3 F.g0 F.root
    (show 0 < q.u by linarith [F.s12, F.su]) hu1
  have hGη : step1Gy W q (step1Eta q) ω = step1Gu W q ω := hlow.1 ω
  have hMη : step1My W q (step1Eta q) = step1Mu W q := hlow.2
  have hv := step1_le_U W q (step1Eta q) ω a
  unfold step1V at hv
  rw [hGη, hMη] at hv
  calc _ ≤ _ := hv.trans hfin
    _ = 256 * R.C ^ 5 * ((W : ℝ) ^ ε * (Rt ^ 2 * ζ)) := by rw [ha₀, hρ]; ring

end Mesh

/-! ### Probability bounds -/

section Prob

/-- Domination at all small accuracies `ε ≤ ε₀` gives domination. -/
private lemma step1_prec_of_small {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι} {Λ : ℕ → ι → Type*}
    {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ} {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ}
    (hY : ∃ Wy : ℕ, ∀ W : ℕ, Wy ≤ W → ∀ p ∈ Dom W, ∀ l, 0 ≤ Y W p l) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (h : ∀ ε D : ℝ, 0 < ε → ε ≤ ε₀ → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ p ∈ Dom W,
      μ W (vol p) {ω | ∃ l : Λ W p, (W : ℝ) ^ ε * Y W p l < ‖X W p l ω‖} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-D))) :
    PrecMax vol Dom X Y := by
  intro ε D hε hD
  obtain ⟨Wy, hWy⟩ := hY
  obtain ⟨W₀, hW⟩ := h (min ε ε₀) D (lt_min hε hε₀) (min_le_right _ _) hD
  refine ⟨max (max W₀ Wy) 1, fun W hW' p hp => (measure_mono ?_).trans
    (hW W ((le_max_left _ _).trans (le_of_max_le_left hW')) p hp)⟩
  rintro ω ⟨l, hl⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW'
  refine ⟨l, lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_
    (hWy W ((le_max_right _ _).trans (le_of_max_le_left hW')) p hp l)) hl⟩
  exact Real.rpow_le_rpow_of_exponent_le hW1 (min_le_left _ _)

/-- A fixed constant is eventually below `W^ε`. -/
private lemma step1_eventually_ge (A ε : ℝ) (hε : 0 < ε) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → A ≤ (W : ℝ) ^ ε := by
  have ht : Tendsto (fun W : ℕ => (W : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_ge_atTop A)

/-- `n` events of probability at most `W^{-(D+C)}`, `n ≤ W^C`, `W ≥ 1`. -/
private lemma step1_card_bound (W : ℕ) (hW : 1 ≤ W) (C D : ℝ) (n : ℝ) (hn : n ≤ (W : ℝ) ^ C) :
    n * (W : ℝ) ^ (-(D + C)) ≤ (W : ℝ) ^ (-D) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  calc n * (W : ℝ) ^ (-(D + C)) ≤ (W : ℝ) ^ C * (W : ℝ) ^ (-(D + C)) :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hW0.le _)
    _ = (W : ℝ) ^ (-D) := by rw [← Real.rpow_add hW0]; ring_nf

/-- `2 W^{-(D+1)} ≤ W^{-D}` for `W ≥ 2`. -/
private lemma step1_two (W : ℕ) (hW : 2 ≤ W) (D : ℝ) :
    ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) ≤
      ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  rw [← ENNReal.ofReal_add (Real.rpow_nonneg hW0.le _) (Real.rpow_nonneg hW0.le _)]
  apply ENNReal.ofReal_le_ofReal
  have e : (W : ℝ) ^ (-(D + 1)) = (W : ℝ) ^ (-D) * (W : ℝ)⁻¹ := by
    rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hW0, Real.rpow_neg_one]
  have hpos : 0 < (W : ℝ) ^ (-D) := Real.rpow_pos_of_pos hW0 _
  have hinv : (W : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW2
  rw [e]; nlinarith

/-- `3 W^{-(D+2)} ≤ W^{-D}` for `W ≥ 2`. -/
private lemma step1_three (W : ℕ) (hW : 2 ≤ W) (D : ℝ) :
    ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) +
      ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  have hn := Real.rpow_nonneg hW0.le (-(D + 2))
  rw [← ENNReal.ofReal_add hn hn, ← ENNReal.ofReal_add (by positivity) hn]
  apply ENNReal.ofReal_le_ofReal
  have e : (W : ℝ) ^ (-(D + 2)) = (W : ℝ) ^ (-D) * ((W : ℝ) ^ 2)⁻¹ := by
    rw [show -(D + 2) = -D + (-2) by ring, Real.rpow_add hW0]
    congr 1
    rw [Real.rpow_neg hW0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpos : 0 < (W : ℝ) ^ (-D) := Real.rpow_pos_of_pos hW0 _
  have hinv : ((W : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  rw [e]; nlinarith

/-- The positive `2·2^j`-loop word `(d, c, d, c, …; +, -, +, -, …)`. -/
private def step1AltWord (L j : ℕ) (c d : Fin L) : Word (2 * 2 ^ j) L :=
  (fun i => if i.val % 2 = 0 then d else c, fun i => decide (i.val % 2 = 0))

open scoped Matrix.Norms.L2Operator in
/-- The bounds of `step1GoodC` hold with probability `1 - O(W^{-D})`, from the input (5.22)
[gc:eq:one-step-input] at the comparison points: positive `2·2^j`-loops at accuracy `W`, loops of
length two and centered block traces. -/
private lemma step1_goodC_prob (R : PropRegime) (c N : ℝ) (hN : 20 ≤ N) (S : ℕ → Set StepPt)
    (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) (cp θ : ℝ)
    (hcmp : OneStepInput cp θ (fun q : StepPt => cmpPt (q.at q.u) q.s) S) :
    ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ q ∈ S W,
      μ W q.L {ω | ¬ step1GoodC W q ε ω} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  intro ε D hε hD
  obtain ⟨Wf, hf⟩ := step1_facts R
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (3 / ε) (by norm_num : (1 : ℝ) < 2)
  have hjε : 3 ≤ ((2 * 2 ^ j : ℕ) : ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hj; push_cast; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]
  have hk1' : 1 ≤ 2 * 2 ^ j := by have := Nat.one_le_two_pow (n := j); omega
  obtain ⟨W₁, hW₁⟩ := hcmp.loop (2 * 2 ^ j) hk1' 1 (D + 2) one_pos (by linarith)
  obtain ⟨W₂, hW₂⟩ := hcmp.loop 2 (by norm_num) ε (D + 2) hε (by linarith)
  obtain ⟨W₃, hW₃⟩ := hcmp.avg ε (D + 2) hε (by linarith)
  refine ⟨max (max Wf 2) (max W₁ (max W₂ W₃)), fun W hW q hq => ?_⟩
  have hWf : Wf ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW2 : 2 ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW1' : W₁ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW2' : W₂ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hW))
  have hW3' : W₃ ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hW))
  have F := hf W hWf c N q (hS W hq)
  obtain ⟨-, -, -, -, -, -, -, hzc0, -, -, -, -, -, -⟩ := step1_num F hN
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  set ζ' := step1ZC W q with hζ'
  have hζ'0 : 0 < ζ' := lt_of_lt_of_le (by positivity) hzc0
  set k := 2 * 2 ^ j with hk
  have hk1 : 1 ≤ k := hk1'
  -- the three events
  set E₁ := {ω : Ω W q.L | ∃ w : Word k q.L,
    (W : ℝ) ^ (1 : ℝ) * ζ' ^ (k - 1) < ‖loopTr (step1G' W q ω) w.1 w.2‖} with hE₁
  set E₂ := {ω : Ω W q.L | ∃ w : Word 2 q.L,
    (W : ℝ) ^ ε * ζ' ^ (2 - 1) < ‖loopTr (step1G' W q ω) w.1 w.2‖} with hE₂
  set E₃ := {ω : Ω W q.L | ∃ ab : Fin q.L × Fin q.L,
    (W : ℝ) ^ ε * ζ' < ‖blockTr (step1G' W q ω - step1M' W q) ab.1 ab.2‖} with hE₃
  have h₁ : μ W q.L E₁ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) := hW₁ W hW1' q hq
  have h₂ : μ W q.L E₂ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) := hW₂ W hW2' q hq
  have h₃ : μ W q.L E₃ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) := hW₃ W hW3' q hq
  have hsub : {ω | ¬ step1GoodC W q ε ω} ⊆ E₁ ∪ E₂ ∪ E₃ := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨n1, n2⟩, n3⟩ := hcon
    simp only [hE₁, hE₂, hE₃, Set.mem_ofPred_eq, not_exists, not_lt] at n1 n2 n3
    apply hω
    refine ⟨fun c e => ?_, fun c e => ?_, fun c e => n3 (c, e)⟩
    · -- operator norms from the positive loops
      have hloop := n1 (step1AltWord q.L j c e)
      have hb := step1_opNorm_le_of_loop (step1G' W q ω) c e j (by omega) hloop
      rw [Real.rpow_one] at hb
      have hB0 : 0 ≤ (W : ℝ) ^ ε * (W * ζ') := by positivity
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) hB0 (by omega : k ≠ 0)).mp ?_
      calc ‖blockOf (step1G' W q ω) c e‖ ^ k ≤ (W : ℝ) ^ k * (W * ζ' ^ (k - 1)) := hb
        _ ≤ (W : ℝ) ^ k * ((W : ℝ) ^ ((k : ℝ) * ε) * ζ' * ζ' ^ (k - 1)) := by
            gcongr
            have h3 : (W : ℝ) ^ (3 : ℝ) ≤ (W : ℝ) ^ ((k : ℝ) * ε) :=
              Real.rpow_le_rpow_of_exponent_le hW1 hjε
            have h3' : (W : ℝ) ^ (3 : ℝ) = W * W * W := by
              rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
            have hz : (2 * (W : ℝ))⁻¹ ≤ ζ' := hzc0
            have hWW : (W : ℝ) ≤ W * W * W * (2 * (W : ℝ))⁻¹ := by
              rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
              have hW2r : (2 : ℝ) ≤ W := by exact_mod_cast hW2
              nlinarith [mul_le_mul_of_nonneg_left hW2r (mul_nonneg hW0.le hW0.le)]
            calc (W : ℝ) ≤ W * W * W * (2 * (W : ℝ))⁻¹ := hWW
              _ ≤ (W : ℝ) ^ ((k : ℝ) * ε) * ζ' := by
                  rw [← h3']; exact mul_le_mul h3 hz (by positivity) (by positivity)
        _ = ((W : ℝ) ^ ε * (W * ζ')) ^ k := by
            rw [mul_pow, mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ ε), ← Real.rpow_mul hW0.le,
              mul_comm ε]
            have : ζ' * ζ' ^ (k - 1) = ζ' ^ k := by
              rw [← pow_succ']; congr 1; omega
            rw [mul_assoc ((W : ℝ) ^ ((k : ℝ) * ε)), this]
            ring
    · -- Hilbert–Schmidt norms from the loops of length two
      have hloop := n2 (![e, c], ![true, false])
      rw [loopTr_two, Complex.norm_real, Real.norm_of_nonneg (by positivity), pow_one] at hloop
      have e1 : ∑ β : Fin W, ∑ α : Fin W, ‖step1G' W q ω (c, β) (e, α)‖ ^ 2 =
          blockHS2 (step1G' W q ω) c e := rfl
      rw [e1] at hloop
      have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by positivity
      rw [inv_mul_le_iff₀ hW2'] at hloop
      calc _ ≤ (W : ℝ) ^ 2 * ((W : ℝ) ^ ε * ζ') := hloop
        _ = _ := by ring
  calc μ W q.L {ω | ¬ step1GoodC W q ε ω} ≤ μ W q.L (E₁ ∪ E₂ ∪ E₃) := measure_mono hsub
    _ ≤ μ W q.L E₁ + μ W q.L E₂ + μ W q.L E₃ :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) +
          ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) := add_le_add (add_le_add h₁ h₂) h₃
    _ ≤ _ := step1_three W hW2 D

end Prob

/-! ### The averaging inputs on the comparison segments -/

section Avg

/-- `R ≥ 1` at an admissible step point for `W ≥ 1`. -/
private lemma step1_ratio_ge {R : PropRegime} {c N : ℝ} {W : ℕ} (hW : 1 ≤ W) {q : StepPt}
    (hq : StepAdm R c N W q) : 1 ≤ q.ratio := by
  obtain ⟨-, -, -, -, hst, ht, -⟩ := hq
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ht0 : 0 < 1 - q.t := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) ht
  unfold StepPt.ratio; rw [le_div_iff₀ ht0]; linarith

/-- `x = (p, y)` lies on the comparison segment of the step point `q ∈ S W` at its time `u`. -/
private def step1Gen (S : ℕ → Set StepPt) (W : ℕ) (x : FlowPt × ℝ) (q : StepPt) : Prop :=
  q ∈ S W ∧ x.1 = q.at q.u ∧ step1Eta q ≤ x.2 ∧ x.2 ≤ step1Top q

/-- The pairs on the comparison segments of the step points of `S W`, for `W ≥ W₀`. -/
private def step1Dom (S : ℕ → Set StepPt) (W₀ W : ℕ) : Set (FlowPt × ℝ) :=
  {x | W₀ ≤ W ∧ ∃ q, step1Gen S W x q}

/-- The smallest ratio `R` of a step point whose segment contains `x` (at least `1`). -/
private def step1Rinf (S : ℕ → Set StepPt) (W : ℕ) (x : FlowPt × ℝ) : ℝ :=
  max 1 (sInf {r | ∃ q, step1Gen S W x q ∧ r = q.ratio})

private lemma step1_rinf {R : PropRegime} {c N : ℝ} {S : ℕ → Set StepPt}
    (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) {W : ℕ} (hW : 1 ≤ W) {x : FlowPt × ℝ} {q : StepPt}
    (hq : step1Gen S W x q) :
    1 ≤ step1Rinf S W x ∧ step1Rinf S W x ≤ q.ratio ∧
      ∃ q', step1Gen S W x q' ∧ q'.ratio ≤ 2 * step1Rinf S W x := by
  set T := {r | ∃ q, step1Gen S W x q ∧ r = q.ratio} with hT
  have hge : ∀ r ∈ T, 1 ≤ r := by
    rintro r ⟨q', hq', rfl⟩; exact step1_ratio_ge hW (hS W hq'.1)
  have hne : T.Nonempty := ⟨q.ratio, q, hq, rfl⟩
  have hbdd : BddBelow T := ⟨1, hge⟩
  have hinf1 : 1 ≤ sInf T := le_csInf hne hge
  have hR : step1Rinf S W x = sInf T := max_eq_right hinf1
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · rw [hR]; exact csInf_le hbdd ⟨q, hq, rfl⟩
  · obtain ⟨r, ⟨q', hq', rfl⟩, hr⟩ := exists_lt_of_csInf_lt hne (show sInf T < 2 * sInf T by
      linarith)
    exact ⟨q', hq', by rw [hR]; exact hr.le⟩

/-- Traceless entries from (5.30) [gc:eq:haar] per pair of blocks and the sampling of
Lemma 5.10(b) [fo:lem:sampling-continuity]: the maximum over all entries inside the probability. -/
private lemma step1_traceless (base : ℕ → Set FlowPt) (J : ℕ) (hsamp : SamplingInput base J)
    (Dom : ℕ → Set (FlowPt × ℝ)) (hDom : ∀ W x, x ∈ Dom W → SegAdm base J W x)
    (Ψ K χ : ℕ → FlowPt × ℝ → ℝ) (hΨK : ∀ W x, x ∈ Dom W → Ψ W x ≤ K W x * χ W x)
    (hKχ : ∀ W x, x ∈ Dom W → (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ K W x * χ W x)
    (hii : ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ Dom W,
      ∀ a b : Fin x.1.L, μ W x.1.L {ω | ∃ i j : Fin W, (W : ℝ) ^ ε * Ψ W x <
        ‖segG W x ω (a, i) (b, j) - if i = j then blockTr (segG W x ω) a b else 0‖} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-D))) :
    PrecMax (fun x : FlowPt × ℝ => x.1.L) Dom
      (Λ := fun W x => (Fin x.1.L × Fin W) × (Fin x.1.L × Fin W))
      (fun W x e ω => segG W x ω e.1 e.2 -
        if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0)
      (fun W x _ => K W x * χ W x) := by
  intro ε D hε hD
  obtain ⟨CS, Cs, W₂, hW₂⟩ := hsamp.2 1 (D + 1) one_pos (by linarith)
  set C' := max CS 0 with hC'
  set Cs' := max Cs 0 with hCs'
  obtain ⟨W₁, hW₁⟩ := hii (ε / 2) (D + 1 + C') (by positivity)
    (by have := le_max_right CS 0; linarith)
  have ht : Tendsto (fun W : ℕ => (W : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  obtain ⟨W₃, hW₃⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (Cs' + 1))
  refine ⟨max (max W₁ W₂) (max W₃ 2), fun W hW x hx => ?_⟩
  have hW1 : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW2 : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW3 : W₃ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW4 : 2 ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hWr1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  obtain ⟨S₁, S₂, -, hS₂, -, hsb, -⟩ := hW₂ W hW2 x (hDom W x hx)
  set X : (Fin x.1.L × Fin W) × (Fin x.1.L × Fin W) → Ω W x.1.L → ℂ := fun e ω =>
    segG W x ω e.1 e.2 - if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0 with hX
  set Bad := {ω : Ω W x.1.L | ∃ l, Cs * (⨆ s : S₂, ‖X s ω‖ / 1) + (W : ℝ) ^ (-(1 : ℝ)) <
    ‖X l ω‖ / 1} with hBad
  set B : (Fin x.1.L × Fin W) × (Fin x.1.L × Fin W) → Set (Ω W x.1.L) := fun s =>
    {ω | ∃ i j : Fin W, (W : ℝ) ^ (ε / 2) * Ψ W x <
      ‖segG W x ω (s.1.1, i) (s.2.1, j) - if i = j then blockTr (segG W x ω) s.1.1 s.2.1 else 0‖}
    with hB
  have hKχ0 : 0 < K W x * χ W x := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) (hKχ W x hx)
  have hWε2 := hW₃ W hW3
  have hWε : (W : ℝ) ^ ε = (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hdel : (W : ℝ) ^ (-(1 : ℝ)) ≤ K W x * χ W x := by
    refine le_trans ?_ (hKχ W x hx)
    exact Real.rpow_le_rpow_of_exponent_le hWr1 (by norm_num)
  have hsub : {ω | ∃ l, (W : ℝ) ^ ε * (K W x * χ W x) < ‖X l ω‖} ⊆
      Bad ∪ ⋃ s ∈ S₂, B s := by
    rintro ω ⟨l, hl⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨hnb, hns⟩ := hcon
    have hs : ∀ s ∈ S₂, ‖X s ω‖ ≤ (W : ℝ) ^ (ε / 2) * Ψ W x := by
      intro s hs
      have := hns s hs
      simp only [hB, Set.mem_ofPred_eq, not_exists, not_lt] at this
      exact this s.1.2 s.2.2
    have hsup0 : 0 ≤ ⨆ s : S₂, ‖X s ω‖ / 1 := Real.iSup_nonneg fun _ => by positivity
    have hsup : (⨆ s : S₂, ‖X s ω‖ / 1) ≤ (W : ℝ) ^ (ε / 2) * (K W x * χ W x) := by
      refine Real.iSup_le (fun s => ?_) (by positivity)
      rw [div_one]
      exact (hs s s.2).trans (mul_le_mul_of_nonneg_left (hΨK W x hx) (by positivity))
    have hnb' : ‖X l ω‖ / 1 ≤ Cs * (⨆ s : S₂, ‖X s ω‖ / 1) + (W : ℝ) ^ (-(1 : ℝ)) := by
      simp only [hBad, Set.mem_ofPred_eq, not_exists, not_lt] at hnb
      exact hnb l
    rw [div_one] at hnb'
    have h1 : Cs * (⨆ s : S₂, ‖X s ω‖ / 1) ≤ Cs' * ((W : ℝ) ^ (ε / 2) * (K W x * χ W x)) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hsup0).trans
        (mul_le_mul_of_nonneg_left hsup (le_max_right _ _))
    have h2 : Cs' * ((W : ℝ) ^ (ε / 2) * (K W x * χ W x)) + K W x * χ W x ≤
        (W : ℝ) ^ ε * (K W x * χ W x) := by
      rw [hWε]
      have : Cs' * (W : ℝ) ^ (ε / 2) + 1 ≤ (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) := by
        have h1' : (1 : ℝ) ≤ (W : ℝ) ^ (ε / 2) := Real.one_le_rpow hWr1 (by positivity)
        nlinarith [le_max_right Cs 0]
      nlinarith
    linarith
  calc μ W x.1.L {ω | ∃ l, (W : ℝ) ^ ε * (K W x * χ W x) < ‖X l ω‖}
      ≤ μ W x.1.L (Bad ∪ ⋃ s ∈ S₂, B s) := measure_mono hsub
    _ ≤ μ W x.1.L Bad + ∑ s ∈ S₂, μ W x.1.L (B s) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) +
          ∑ _s ∈ S₂, ENNReal.ofReal ((W : ℝ) ^ (-(D + 1 + C'))) := by
        gcongr with s hs
        · exact hsb
        · exact hW₁ W hW1 x hx s.1.1 s.2.1
    _ = ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal ((S₂.card : ℝ) * (W : ℝ) ^ (-(D + 1 + C'))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) := by
        gcongr
        exact step1_card_bound W (by omega) C' (D + 1) _ (hS₂.trans
          (Real.rpow_le_rpow_of_exponent_le hWr1 (le_max_left _ _)))
    _ ≤ _ := step1_two W hW4 D

end Avg

/-! ### The residual on the mesh -/

section Residual

/-- `ζ_u(g)` at the point of a pair. -/
private def step1ZetaX (W : ℕ) (x : FlowPt × ℝ) : ℝ := zetaProp x.1.g W x.1.L x.1.u

private lemma step1_dom_segAdm {R : PropRegime} {c N : ℝ} {S : ℕ → Set StepPt}
    (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) (Wt W : ℕ) (x : FlowPt × ℝ)
    (hx : x ∈ step1Dom S Wt W) : SegAdm R.base R.J W x := by
  obtain ⟨-, q, hqS, hpq, hy1, hy2⟩ := hx
  obtain ⟨⟨d, hd, hreach⟩, hs12, hsu, hut, -, -, -⟩ := hS W hqS
  obtain ⟨p, y⟩ := x
  simp only at hpq hy1 hy2
  subst hpq
  exact ⟨d, hd.le, CmpReach.earlier q.u hreach (hs12.trans hsu) hut,
    Or.inr ⟨hd, q.s, hs12, hsu, hy1, hy2⟩⟩

/-- The residual (5.28) [gc:eq:residual-input] at the mesh heights, from Lemma 5.9(i)
[gc:lem:residual] with `K = 4C² R`, `χ = 2ζ_u^{1/2}`, its premises from (5.30) [gc:eq:haar],
the sampling of Lemma 5.10(b) [fo:lem:sampling-continuity] and the rough bounds on the segment:
the bounds of `step1ResGood` hold with probability `1 - O(W^{-D})`. -/
private lemma step1_resGood_prob (R : PropRegime) (I : PropInputs R.base R.J) (c N : ℝ)
    (hc : 0 < c) (hN : 20 ≤ N) (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (cp θ : ℝ) (hcmp : OneStepInput cp θ (fun q : StepPt => cmpPt (q.at q.u) q.s) S) :
    ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ q ∈ S W,
      μ W q.L {ω | ¬ step1ResGood R W q ε ω} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  obtain ⟨Wf, hf⟩ := step1_facts R
  have hC1 := R.one_le_C
  have hC0 : 0 < R.C := lt_of_lt_of_le one_pos hC1
  set Wt : ℕ := max Wf (⌈4 * R.C ^ 2⌉₊ + ⌈R.C ^ 2⌉₊ + 2) with hWt
  set Dom := step1Dom S Wt with hDom
  set K : ℕ → FlowPt × ℝ → ℝ := fun W x => 4 * R.C ^ 2 * step1Rinf S W x with hK
  set χ : ℕ → FlowPt × ℝ → ℝ := fun W x => 2 * Real.sqrt (step1ZetaX W x) with hχ
  set Ψ : ℕ → FlowPt × ℝ → ℝ := fun W x =>
    5 * R.C ^ 2 * step1Rinf S W x * Real.sqrt (step1ZetaX W x) with hΨ
  have hDomA : ∀ W x, x ∈ Dom W → SegAdm R.base R.J W x := fun W x hx =>
    step1_dom_segAdm hS Wt W x hx
  -- facts at a point of the domain, through a step point with almost the smallest ratio
  have hpt : ∀ W x, x ∈ Dom W → ∃ q, step1Gen S W x q ∧ q.ratio ≤ 2 * step1Rinf S W x ∧
      Step1Facts R c N W q ∧ 1 ≤ step1Rinf S W x := by
    intro W x hx
    obtain ⟨hWt', q0, hq0⟩ := hx
    have hW1 : 1 ≤ W := le_trans (by omega) hWt'
    obtain ⟨hr1, -, q, hq, hqR⟩ := step1_rinf hS hW1 hq0
    exact ⟨q, hq, hqR, hf W ((le_max_left _ _).trans hWt') c N q (hS W hq.1), hr1⟩
  have hWbig : ∀ W x, x ∈ Dom W → 4 * R.C ^ 2 ≤ W ∧ R.C ^ 2 + 2 ≤ W := by
    intro W x hx
    have h1 : (⌈4 * R.C ^ 2⌉₊ + ⌈R.C ^ 2⌉₊ + 2 : ℕ) ≤ W := (le_max_right _ _).trans hx.1
    have h2 : ((⌈4 * R.C ^ 2⌉₊ + ⌈R.C ^ 2⌉₊ + 2 : ℕ) : ℝ) ≤ W := by exact_mod_cast h1
    push_cast at h2
    have h3 := Nat.le_ceil (4 * R.C ^ 2)
    have h4 := Nat.le_ceil (R.C ^ 2)
    have h5 : (0 : ℝ) ≤ ⌈4 * R.C ^ 2⌉₊ := Nat.cast_nonneg _
    have h6 : (0 : ℝ) ≤ ⌈R.C ^ 2⌉₊ := Nat.cast_nonneg _
    constructor <;> linarith
  -- (i): the block traces on the segment
  have hKprec : PrecMax (fun x : FlowPt × ℝ => x.1.L) Dom
      (Λ := fun _ x => Fin x.1.L × Fin x.1.L)
      (fun W x ab ω => blockTr (segG W x ω) ab.1 ab.2) (fun W x _ => K W x) := by
    refine step1_prec_of_small ⟨0, fun W _ x _ _ => mul_nonneg (by positivity)
      (le_trans zero_le_one (le_max_left _ _))⟩ (ε₀ := c / 4) (by positivity) ?_
    intro ε D hε hεc hD
    obtain ⟨Wg, hWg⟩ := step1_goodC_prob R c N hN S hS cp θ hcmp ε D hε hD
    refine ⟨Wg, fun W hW x hx => ?_⟩
    obtain ⟨q, ⟨hqS, hpq, hy1, hy2⟩, hqR, F, hr1⟩ := hpt W x hx
    obtain ⟨p, y⟩ := x
    simp only at hpq hy1 hy2
    subst hpq
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by have := F.two_le; omega : 1 ≤ W)
    refine le_trans (measure_mono ?_) (hWg W hW q hqS)
    intro ω hω
    obtain ⟨ab, hab⟩ := hω
    intro hG
    have hb := (step1_seg_bounds F hN (by linarith) hG hy1 hy2).1 ab.1 ab.2
    have hK1 : 2 * R.C ^ 2 * q.ratio ≤ K W (q.at q.u, y) := by
      simp only [hK]; nlinarith [pow_pos hC0 2]
    have hKp : 0 ≤ K W (q.at q.u, y) := by simp only [hK]; positivity
    have : K W (q.at q.u, y) ≤ (W : ℝ) ^ ε * K W (q.at q.u, y) :=
      le_mul_of_one_le_left hKp (Real.one_le_rpow hW1 hε.le)
    exact absurd hab (not_lt.mpr ((hb.trans hK1).trans this))
  -- (ii): the Hilbert–Schmidt premise on the segment
  have hΨpos : ∀ W x, x ∈ Dom W → 0 < Ψ W x := by
    intro W x hx
    obtain ⟨q, ⟨hqS, hpq, -, -⟩, -, F, hr1⟩ := hpt W x hx
    obtain ⟨-, -, -, -, -, -, -, -, -, hz0, -, -, -, -⟩ := step1_num F hN
    obtain ⟨p, y⟩ := x
    simp only at hpq
    subst hpq
    have hW0 : (0 : ℝ) < W := by exact_mod_cast (by have := F.two_le; omega : 0 < W)
    have hz : 0 < step1ZetaX W (q.at q.u, y) := lt_of_lt_of_le (by positivity) hz0
    simp only [hΨ]
    have := Real.sqrt_pos.mpr hz
    positivity
  have hHS : ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ Dom W,
      ∀ a b : Fin x.1.L, μ W x.1.L {ω | (W : ℝ) ^ ε * Ψ W x ^ 2 <
        ((W : ℝ) ^ 2)⁻¹ * blockHS2 (segG W x ω) a b} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
    intro ε D hε hD
    set ε' := min ε (c / 4) with hε'
    have hε'0 : 0 < ε' := lt_min hε (by positivity)
    obtain ⟨Wg, hWg⟩ := step1_goodC_prob R c N hN S hS cp θ hcmp ε' D hε'0 hD
    refine ⟨Wg, fun W hW x hx a b => ?_⟩
    obtain ⟨q, ⟨hqS, hpq, hy1, hy2⟩, hqR, F, hr1⟩ := hpt W x hx
    obtain ⟨-, -, -, hR1, -, -, -, hzc0, hzc, hz0, -, -, -, -⟩ := step1_num F hN
    obtain ⟨p, y⟩ := x
    simp only at hpq hy1 hy2
    subst hpq
    have hW0 : (0 : ℝ) < W := by exact_mod_cast (by have := F.two_le; omega : 0 < W)
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by have := F.two_le; omega : 1 ≤ W)
    have hzc00 : 0 ≤ step1ZC W q := (inv_nonneg.mpr (by positivity)).trans hzc0
    refine le_trans (measure_mono ?_) (hWg W hW q hqS)
    intro ω hω hG
    simp only [Set.mem_ofPred_eq] at hω
    obtain ⟨hB1, hB2⟩ := step1_seg_bounds F hN (by linarith [min_le_right ε (c / 4)]) hG hy1 hy2
    have hT : ∀ a, (blockTr (step1Gy W q y ω) a a).im ≤ 2 * R.C ^ 2 * q.ratio := fun a =>
      ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (hB1 a a)
    have hb := hB2 _ (by positivity) hT a b
    set ζ := zetaProp q.g W q.L q.u with hζ
    have hζ0 : 0 ≤ ζ := (inv_nonneg.mpr (by positivity)).trans hz0
    have hzc' : step1ZC W q ≤ ζ := hzc
    set r := step1Rinf S W (q.at q.u, y) with hr
    have hΨ2 : Ψ W (q.at q.u, y) ^ 2 = 25 * R.C ^ 4 * r ^ 2 * ζ := by
      have hzx : step1ZetaX W (q.at q.u, y) = ζ := rfl
      simp only [hΨ]
      rw [hzx, mul_pow, Real.sq_sqrt hζ0]
      ring
    have hWε : (W : ℝ) ^ ε' ≤ (W : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hW1 (min_le_left _ _)
    have hkey : ((W : ℝ) ^ 2)⁻¹ * blockHS2 (step1Gy W q y ω) a b ≤
        (W : ℝ) ^ ε * (25 * R.C ^ 4 * r ^ 2 * ζ) := by
      rw [inv_mul_le_iff₀ (by positivity)]
      have hR2 : q.ratio ^ 2 ≤ 4 * r ^ 2 := by nlinarith
      have hC34 : R.C ^ 3 ≤ R.C ^ 4 := pow_le_pow_right₀ hC1 (by norm_num)
      calc blockHS2 (step1Gy W q y ω) a b
          ≤ (W : ℝ) ^ ε' * ((W : ℝ) ^ 2 * step1ZC W q) *
            (2 + 2 * R.C * q.ratio * (2 * R.C ^ 2 * q.ratio)) := hb
        _ ≤ (W : ℝ) ^ ε * ((W : ℝ) ^ 2 * ζ) * (25 * R.C ^ 4 * r ^ 2) := by
            have hA : 2 + 2 * R.C * q.ratio * (2 * R.C ^ 2 * q.ratio) ≤ 25 * R.C ^ 4 * r ^ 2 := by
              have h1 : 2 ≤ 2 * R.C ^ 4 * r ^ 2 := by
                have : 1 ≤ R.C ^ 4 * r ^ 2 := one_le_mul_of_one_le_of_one_le
                  (one_le_pow₀ hC1) (one_le_pow₀ hr1)
                linarith
              have h2 : 2 * R.C * q.ratio * (2 * R.C ^ 2 * q.ratio) ≤ 16 * R.C ^ 4 * r ^ 2 := by
                have : 2 * R.C * q.ratio * (2 * R.C ^ 2 * q.ratio) = 4 * R.C ^ 3 * q.ratio ^ 2 := by
                  ring
                rw [this]
                calc 4 * R.C ^ 3 * q.ratio ^ 2 ≤ 4 * R.C ^ 4 * (4 * r ^ 2) := by gcongr
                  _ = 16 * R.C ^ 4 * r ^ 2 := by ring
              linarith
            have hB0 : 0 ≤ (W : ℝ) ^ ε' * ((W : ℝ) ^ 2 * step1ZC W q) := by positivity
            calc _ ≤ (W : ℝ) ^ ε' * ((W : ℝ) ^ 2 * step1ZC W q) * (25 * R.C ^ 4 * r ^ 2) :=
                  mul_le_mul_of_nonneg_left hA hB0
              _ ≤ _ := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact mul_le_mul hWε (mul_le_mul_of_nonneg_left hzc' (by positivity))
                    (mul_nonneg (by positivity) hzc00) (by positivity)
        _ = (W : ℝ) ^ 2 * ((W : ℝ) ^ ε * (25 * R.C ^ 4 * r ^ 2 * ζ)) := by ring
    rw [hΨ2] at hω
    exact absurd hω (not_lt.mpr hkey)
  have hΨK : ∀ W x, x ∈ Dom W → Ψ W x ≤ K W x * χ W x := by
    intro W x hx
    simp only [hΨ, hK, hχ]
    have h0 : 0 ≤ R.C ^ 2 * step1Rinf S W x * Real.sqrt (step1ZetaX W x) := by
      obtain ⟨-, -, -, -, hr1⟩ := hpt W x hx
      positivity
    nlinarith
  have hχ0 : ∀ W x, x ∈ Dom W → (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ χ W x := by
    intro W x hx
    obtain ⟨q, ⟨hqS, hpq, -, -⟩, -, F, hr1⟩ := hpt W x hx
    obtain ⟨-, -, -, -, -, -, -, -, -, hz0, -, -, -, -⟩ := step1_num F hN
    obtain ⟨p, y⟩ := x
    simp only at hpq
    subst hpq
    have hW0 : (0 : ℝ) < W := by exact_mod_cast (by have := F.two_le; omega : 0 < W)
    simp only [hχ]
    have hz : (2 * (W : ℝ))⁻¹ ≤ step1ZetaX W (q.at q.u, y) := hz0
    rw [Real.rpow_neg hW0.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
    have h1 : Real.sqrt ((W : ℝ)⁻¹) ≤ Real.sqrt (4 * step1ZetaX W (q.at q.u, y)) := by
      apply Real.sqrt_le_sqrt
      have : (W : ℝ)⁻¹ = 2 * (2 * (W : ℝ))⁻¹ := by field_simp
      have h0 : 0 ≤ (2 * (W : ℝ))⁻¹ := by positivity
      rw [this]; linarith
    calc Real.sqrt ((W : ℝ)⁻¹) ≤ Real.sqrt (4 * step1ZetaX W (q.at q.u, y)) := h1
      _ = 2 * Real.sqrt (step1ZetaX W (q.at q.u, y)) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have hKχ : ∀ W x, x ∈ Dom W → (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ K W x * χ W x := by
    intro W x hx
    obtain ⟨-, -, -, -, hr1⟩ := hpt W x hx
    have hK1 : 1 ≤ K W x := by
      simp only [hK]
      have : 1 ≤ R.C ^ 2 := one_le_pow₀ hC1
      nlinarith
    have hχ' := hχ0 W x hx
    have hχp : 0 ≤ χ W x := le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) hχ'
    nlinarith
  have hTL := step1_traceless R.base R.J I.sampling Dom hDomA Ψ K χ hΨK hKχ
    (I.averaging.2.1 Dom hDomA Ψ hΨpos hHS)
  have hKb : ∀ W x, x ∈ Dom W →
      1 ≤ K W x ∧ K W x ≤ (W : ℝ) ^ (4 : ℝ) ∧ (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ χ W x := by
    intro W x hx
    obtain ⟨q, hq, -, F, hr1⟩ := hpt W x hx
    obtain ⟨-, -, -, -, hR3, -, -, -, -, -, -, -, -, -⟩ := step1_num F hN
    obtain ⟨-, hrq, -⟩ := step1_rinf hS (by have := F.two_le; omega) hq
    have hW0 : (0 : ℝ) < W := by exact_mod_cast (by have := F.two_le; omega : 0 < W)
    obtain ⟨hW4, -⟩ := hWbig W x hx
    refine ⟨?_, ?_, hχ0 W x hx⟩
    · simp only [hK]
      have : 1 ≤ R.C ^ 2 := one_le_pow₀ hC1
      nlinarith
    · simp only [hK]
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc 4 * R.C ^ 2 * step1Rinf S W x ≤ (W : ℝ) * (W : ℝ) ^ 3 :=
            mul_le_mul hW4 (hrq.trans hR3) (by linarith) hW0.le
        _ = (W : ℝ) ^ 4 := by ring
  have hRes := I.averaging.1 Dom hDomA K χ 4 hKb hKprec hTL
  -- the mesh heights
  intro ε D hε hD
  obtain ⟨W₁, hW₁⟩ := hRes ε (D + 13) hε (by linarith)
  refine ⟨max W₁ Wt, fun W hW q hq => ?_⟩
  have hWt' : Wt ≤ W := le_of_max_le_right hW
  have F := hf W ((le_max_left _ _).trans hWt') c N q (hS W hq)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by have := F.two_le; omega : 0 < W)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by have := F.two_le; omega : 1 ≤ W)
  have hγ := step1_gammaG_pos q.g
  have hδ : 0 < step1Del W q := by unfold step1Del; positivity
  obtain ⟨hmem, -, -, -⟩ := step1_mesh hδ F.etaw
  have hxk : ∀ k, ((q.at q.u, step1Ym W q k) : FlowPt × ℝ) ∈ Dom W := fun k =>
    ⟨hWt', q, hq, rfl, (hmem k).1, (hmem k).2⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hz0, -, -, -, -⟩ := step1_num F hN
  set ζ := zetaProp q.g W q.L q.u with hζ
  have hζ0 : 0 ≤ ζ := (inv_nonneg.mpr (by positivity)).trans hz0
  set E : ℕ → Set (Ω W q.L) := fun k => {ω | ∃ ab : Fin q.L × Fin q.L,
    (W : ℝ) ^ ε * (K W (q.at q.u, step1Ym W q k) * χ W (q.at q.u, step1Ym W q k)) ^ 2 <
      ‖step1Res W q (step1Ym W q k) ω ab.1 ab.2‖} with hE
  have hsub : {ω | ¬ step1ResGood R W q ε ω} ⊆ ⋃ k ∈ Finset.range (step1Nm W q + 1), E k := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, step1ResGood, not_forall, not_le] at hω
    obtain ⟨k, hk, a, b, hab⟩ := hω
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨k, by omega, ⟨a, b⟩, lt_of_le_of_lt ?_ hab⟩
    obtain ⟨-, hrq, -⟩ := step1_rinf hS (by have := F.two_le; omega)
      (x := (q.at q.u, step1Ym W q k))
      ⟨hq, rfl, (hmem k).1, (hmem k).2⟩
    have hr1 : 1 ≤ step1Rinf S W (q.at q.u, step1Ym W q k) := le_max_left _ _
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hW0.le _)
    simp only [hK, hχ]
    have hzx : step1ZetaX W (q.at q.u, step1Ym W q k) = ζ := rfl
    rw [hzx, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hζ0]
    have : step1Rinf S W (q.at q.u, step1Ym W q k) ^ 2 ≤ q.ratio ^ 2 :=
      pow_le_pow_left₀ (by linarith) hrq 2
    have hC4 : 0 ≤ R.C ^ 4 := by positivity
    calc (4 : ℝ) ^ 2 * (R.C ^ 2) ^ 2 * step1Rinf S W (q.at q.u, step1Ym W q k) ^ 2 * (2 ^ 2 * ζ)
        = 64 * R.C ^ 4 * step1Rinf S W (q.at q.u, step1Ym W q k) ^ 2 * ζ := by ring
      _ ≤ 64 * R.C ^ 4 * q.ratio ^ 2 * ζ := by gcongr
  have hk : ∀ k, μ W q.L (E k) ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 13))) := fun k =>
    hW₁ W (le_of_max_le_left hW) _ (hxk k)
  have hNm := step1_Nm_le F hN
  obtain ⟨-, hW2C⟩ := hWbig W _ (hxk 0)
  calc μ W q.L {ω | ¬ step1ResGood R W q ε ω}
      ≤ μ W q.L (⋃ k ∈ Finset.range (step1Nm W q + 1), E k) := measure_mono hsub
    _ ≤ ∑ k ∈ Finset.range (step1Nm W q + 1), μ W q.L (E k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range (step1Nm W q + 1), ENNReal.ofReal ((W : ℝ) ^ (-(D + 13))) :=
        Finset.sum_le_sum fun k _ => hk k
    _ = ENNReal.ofReal (((step1Nm W q + 1 : ℕ) : ℝ) * (W : ℝ) ^ (-(D + 13))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        apply step1_card_bound W (by exact_mod_cast hW1) 13 D
        push_cast
        rw [show (13 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        calc ((step1Nm W q : ℕ) : ℝ) + 1 ≤ R.C ^ 2 * (W : ℝ) ^ 12 + 2 := hNm
          _ ≤ (R.C ^ 2 + 2) * (W : ℝ) ^ 12 := by
              have : (1 : ℝ) ≤ (W : ℝ) ^ 12 := one_le_pow₀ hW1
              nlinarith
          _ ≤ (W : ℝ) * (W : ℝ) ^ 12 := by gcongr
          _ = (W : ℝ) ^ 13 := by ring

end Residual

/-! ### The bounds at the time `u` -/

section Point

private lemma step1_loopTr_one_norm {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin 1 → Fin L) (σ : Fin 1 → Bool) : ‖loopTr X a σ‖ = ‖blockTr X (a 0) (a 0)‖ := by
  rw [step1_loopTr_eq_chain (k := 0)]
  have hc : step1_chain (a (Fin.last 0)) (List.ofFn fun i => (sgnMat X (σ i), a i)) =
      blockOf (sgnMat X (σ 0)) (a 0) (a 0) := by
    simp [List.ofFn_succ, step1_chain, Fin.last]
  have ht : blockTr X (a 0) (a 0) = (W : ℂ)⁻¹ * (blockOf X (a 0) (a 0)).trace := by
    simp [blockTr, Matrix.trace, blockOf]
  rw [hc, ht, norm_mul, norm_mul, pow_one]
  congr 1
  cases σ 0 with
  | true => simp [sgnMat]
  | false =>
    simp only [sgnMat, Bool.false_eq_true, ↓reduceIte]
    rw [step1_blockOf_conjTranspose, Matrix.trace_conjTranspose, norm_star]

/-- `W^ε R³ ζ_u ≤ W^{-3c/4}` for `ε ≤ c/4`. -/
private lemma step1_B {R : PropRegime} {c N : ℝ} {W : ℕ} {q : StepPt} (F : Step1Facts R c N W q)
    (hN : 20 ≤ N) {ε : ℝ} (hεc : ε ≤ c / 4) :
    (W : ℝ) ^ ε * (q.ratio ^ 3 * zetaProp q.g W q.L q.u) ≤ (W : ℝ) ^ (-(3 * c / 4)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hzt, -, -, -⟩ := step1_num F hN
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by have := F.two_le; omega : 1 ≤ W)
  have hW0 : (0 : ℝ) < W := by linarith
  calc (W : ℝ) ^ ε * (q.ratio ^ 3 * zetaProp q.g W q.L q.u) ≤ (W : ℝ) ^ ε * (W : ℝ) ^ (-c) :=
        mul_le_mul_of_nonneg_left hzt (Real.rpow_nonneg hW0.le _)
    _ = (W : ℝ) ^ (ε - c) := by rw [← Real.rpow_add hW0]; ring_nf
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)

open scoped Matrix.Norms.L2Operator in
/-- On the events of `step1GoodC` and `step1ResGood`, the bounds (C.5) [fo:eq:step1] and
(C.6) [fo:eq:step1-density] at the time `u` with the constant `256C⁵`. -/
private lemma step1_point {R : PropRegime} {c N : ℝ} {W : ℕ} {q : StepPt}
    (F : Step1Facts R c N W q) (hN : 20 ≤ N) (hc : 0 < c) {ε : ℝ} (hεc : ε ≤ c / 4)
    (hbig1 : 4096 * R.C ^ 10 * (W : ℝ) ^ (-(3 * c / 4)) ≤ 1 / 2)
    (hbig2 : 48 * R.C ^ 8 ≤ (W : ℝ) ^ 3) {ω : Ω W q.L}
    (hG : step1GoodC W q ε ω) (hRes : step1ResGood R W q ε ω) :
    (∀ a b : Fin q.L, ‖blockOf (step1Gu W q ω) a b‖ ≤
      256 * R.C ^ 5 * ((W : ℝ) ^ ε * (W * q.ratio * zetaProp q.g W q.L q.u))) ∧
    (∀ a b : Fin q.L, blockHS2 (step1Gu W q ω) a b ≤
      256 * R.C ^ 5 * ((W : ℝ) ^ ε * ((W : ℝ) ^ 2 * q.ratio * zetaProp q.g W q.L q.u))) ∧
    (∀ a : Fin q.L, ‖blockTr (step1Gu W q ω - step1Mu W q) a a‖ ≤
      256 * R.C ^ 5 * ((W : ℝ) ^ ε * (q.ratio ^ 2 * zetaProp q.g W q.L q.u))) ∧
    ∀ a : Fin q.L, ‖blockTr (step1Gu W q ω) a a‖ ≤ R.C + 1 := by
  obtain ⟨-, hs0, hu1, hR1, -, hRu, -, hzc0, hzc, hz0, -, heta, -, -⟩ := step1_num F hN
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by have := F.two_le; omega : 1 ≤ W)
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by have := F.two_le; omega
  have hC1 := R.one_le_C
  have hC0 : 0 < R.C := lt_of_lt_of_le one_pos hC1
  set ζ := zetaProp q.g W q.L q.u with hζ
  have hζ0 : 0 ≤ ζ := (inv_nonneg.mpr (by positivity)).trans hz0
  have hzc00 : 0 ≤ step1ZC W q := (inv_nonneg.mpr (by positivity)).trans hzc0
  have hWε : 0 < (W : ℝ) ^ ε := Real.rpow_pos_of_pos hW0 _
  have hεc' : ε ≤ c := by linarith
  have havg := fun a => step1_closure F hN hc hεc hbig1 hbig2 hG hRes a
  -- `256 C⁵ W^ε R² ζ ≤ 1`
  have hsmall : 256 * R.C ^ 5 * ((W : ℝ) ^ ε * (q.ratio ^ 2 * ζ)) ≤ 1 := by
    have hB := step1_B F hN hεc
    have h2 : (W : ℝ) ^ ε * (q.ratio ^ 2 * ζ) ≤ (W : ℝ) ^ ε * (q.ratio ^ 3 * ζ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hR1 (by norm_num)) hζ0) hWε.le
    have h5 : R.C ^ 5 ≤ R.C ^ 10 := pow_le_pow_right₀ hC1 (by norm_num)
    calc 256 * R.C ^ 5 * ((W : ℝ) ^ ε * (q.ratio ^ 2 * ζ))
        ≤ 4096 * R.C ^ 10 * (W : ℝ) ^ (-(3 * c / 4)) := by
          apply mul_le_mul (by nlinarith) (h2.trans hB) (by positivity) (by positivity)
      _ ≤ 1 := by linarith
  have htr : ∀ a : Fin q.L, ‖blockTr (step1Gu W q ω) a a‖ ≤ R.C + 1 := by
    intro a
    have hk : blockTr (step1Mu W q) a a =
        dysonMat (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E) a a :=
      step1_blockTr_kron W q.L hWn _ a a
    have h1 := havg a
    rw [step1_blockTr_sub, hk] at h1
    calc ‖blockTr (step1Gu W q ω) a a‖
        ≤ ‖blockTr (step1Gu W q ω) a a -
            dysonMat (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E) a a‖ +
          ‖dysonMat (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E) a a‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ 1 + R.C := add_le_add (h1.trans hsmall) (F.Mbd a a)
      _ = R.C + 1 := by ring
  refine ⟨fun a b => ?_, fun a b => ?_, havg, htr⟩
  · -- operator norms by Lemma 5.11 [fo:lem:families]
    have h := F.cmp411 ω a b
    have hsup : ⨆ c : Fin q.L, ⨆ e : Fin q.L, ‖blockOf (flowG W (step1Cmp q) ω) c e‖ ≤
        (W : ℝ) ^ ε * (W * step1ZC W q) :=
      Real.iSup_le (fun c => Real.iSup_le (fun e => hG.1 c e) (by positivity)) (by positivity)
    have hsup0 : 0 ≤ ⨆ c : Fin q.L, ⨆ e : Fin q.L, ‖blockOf (flowG W (step1Cmp q) ω) c e‖ :=
      Real.iSup_nonneg fun c => Real.iSup_nonneg fun e => norm_nonneg _
    have hC5 : R.C ≤ 256 * R.C ^ 5 := by
      have : R.C ≤ R.C ^ 5 := by
        calc R.C = R.C ^ 1 := (pow_one _).symm
          _ ≤ R.C ^ 5 := pow_le_pow_right₀ hC1 (by norm_num)
      linarith
    calc ‖blockOf (step1Gu W q ω) a b‖ ≤ R.C * ((1 - q.s) / (1 - q.u)) *
          ⨆ c : Fin q.L, ⨆ e : Fin q.L, ‖blockOf (flowG W (step1Cmp q) ω) c e‖ := h
      _ ≤ R.C * q.ratio * ((W : ℝ) ^ ε * (W * ζ)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hRu hC0.le) (hsup.trans ?_) hsup0
            (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzc hW0.le) hWε.le
      _ = R.C * ((W : ℝ) ^ ε * (W * q.ratio * ζ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC5 (by positivity)
  · -- Hilbert–Schmidt norms by (C.9) [fo:eq:step1-hs-comparison] at `y = η_u`
    have hlow := step1_seg_lower W (q.at q.u) F.L3 F.g0 F.root
      (show 0 < q.u by linarith [F.s12, F.su]) hu1
    have hGη : step1Gy W q (step1Eta q) ω = step1Gu W q ω := hlow.1 ω
    have hT : ∀ a, (blockTr (step1Gy W q (step1Eta q) ω) a a).im ≤ R.C + 1 := by
      intro a; rw [hGη]
      exact ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (htr a)
    have h := (step1_seg_bounds F hN hεc' hG le_rfl F.etaw).2 (R.C + 1) (by positivity) hT a b
    rw [hGη] at h
    have hA : 2 + 2 * R.C * q.ratio * (R.C + 1) ≤ 6 * R.C ^ 2 * q.ratio := by
      have h1 : 1 ≤ R.C * q.ratio := one_le_mul_of_one_le_of_one_le hC1 hR1
      have h2 : R.C * q.ratio ≤ R.C ^ 2 * q.ratio := by
        have : R.C * q.ratio * 1 ≤ R.C * q.ratio * R.C :=
          mul_le_mul_of_nonneg_left hC1 (by linarith)
        nlinarith
      have e : 2 + 2 * R.C * q.ratio * (R.C + 1) = 2 + 2 * (R.C ^ 2 * q.ratio) +
          2 * (R.C * q.ratio) := by ring
      rw [e]; linarith
    have hC6 : 6 * R.C ^ 2 ≤ 256 * R.C ^ 5 := by
      have : R.C ^ 2 ≤ R.C ^ 5 := pow_le_pow_right₀ hC1 (by norm_num)
      have h0 : 0 ≤ R.C ^ 5 := by positivity
      linarith
    calc blockHS2 (step1Gu W q ω) a b ≤ (W : ℝ) ^ ε * ((W : ℝ) ^ 2 * step1ZC W q) *
          (2 + 2 * R.C * q.ratio * (R.C + 1)) := h
      _ ≤ (W : ℝ) ^ ε * ((W : ℝ) ^ 2 * ζ) * (6 * R.C ^ 2 * q.ratio) := by
          apply mul_le_mul _ hA (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzc (by positivity)) hWε.le
      _ = 6 * R.C ^ 2 * ((W : ℝ) ^ ε * ((W : ℝ) ^ 2 * q.ratio * ζ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC6 (by positivity)

end Point

/-- Step 1 of Appendix C.3 [sec:gc-one-step] at fixed times: the inputs (5.22)
[gc:eq:one-step-input] at the start and at the comparison points give (C.5) [fo:eq:step1] and
(C.6) [fo:eq:step1-density] at every time `u` of the step. -/
theorem step1 (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N : ℝ) (hc : 0 < c)
    (hN : 20 ≤ N) (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (hin : OneStepInput cp θ (fun q : StepPt => q.at q.s) S)
    (hcmp : OneStepInput cp θ (fun q : StepPt => cmpPt (q.at q.u) q.s) S) : Step1Out S := by
  have _hin := hin
  obtain ⟨Wf, hf⟩ := step1_facts R
  have hC1 := R.one_le_C
  have hC0 : 0 < R.C := lt_of_lt_of_le one_pos hC1
  obtain ⟨Wb1, hWb1⟩ := step1_eventually_ge (8192 * R.C ^ 10) (3 * c / 4) (by positivity)
  obtain ⟨Wb2, hWb2⟩ := step1_eventually_ge (48 * R.C ^ 8) 3 (by norm_num)
  set W0 := max Wf (max (max Wb1 Wb2) 2) with hW0def
  have hbig : ∀ W : ℕ, W0 ≤ W → 4096 * R.C ^ 10 * (W : ℝ) ^ (-(3 * c / 4)) ≤ 1 / 2 ∧
      48 * R.C ^ 8 ≤ (W : ℝ) ^ 3 := by
    intro W hW
    have hW2 : 2 ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
    have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
    have h1 := hWb1 W ((le_max_left _ _).trans ((le_max_left _ _).trans
      ((le_max_right _ _).trans hW)))
    have h2 := hWb2 W ((le_max_right _ _).trans ((le_max_left _ _).trans
      ((le_max_right _ _).trans hW)))
    refine ⟨?_, ?_⟩
    · rw [Real.rpow_neg hW0.le]
      have hp : 0 < (W : ℝ) ^ (3 * c / 4) := Real.rpow_pos_of_pos hW0 _
      rw [← div_eq_mul_inv, div_le_iff₀ hp]
      linarith
    · rwa [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h2
  have hgood : ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ q ∈ S W,
      μ W q.L {ω | ¬ (step1GoodC W q ε ω ∧ step1ResGood R W q ε ω)} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
    intro ε D hε hD
    obtain ⟨W₁, h₁⟩ := step1_goodC_prob R c N hN S hS cp θ hcmp ε (D + 1) hε (by linarith)
    obtain ⟨W₂, h₂⟩ := step1_resGood_prob R I c N hc hN S hS cp θ hcmp ε (D + 1) hε (by linarith)
    refine ⟨max (max W₁ W₂) 2, fun W hW q hq => ?_⟩
    have hsub : {ω | ¬ (step1GoodC W q ε ω ∧ step1ResGood R W q ε ω)} ⊆
        {ω | ¬ step1GoodC W q ε ω} ∪ {ω | ¬ step1ResGood R W q ε ω} := by
      intro ω hω
      by_cases hA : step1GoodC W q ε ω
      · exact Or.inr fun hB => hω ⟨hA, hB⟩
      · exact Or.inl hA
    calc _ ≤ μ W q.L ({ω | ¬ step1GoodC W q ε ω} ∪ {ω | ¬ step1ResGood R W q ε ω}) :=
          measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) :=
          add_le_add (h₁ W ((le_max_left _ _).trans ((le_max_left _ _).trans hW)) q hq)
            (h₂ W ((le_max_right _ _).trans ((le_max_left _ _).trans hW)) q hq)
      _ ≤ _ := step1_two W ((le_max_right _ _).trans hW) D
  -- the deterministic bounds on the good event
  have hdet : ∀ W : ℕ, W0 ≤ W → ∀ q ∈ S W, ∀ ε : ℝ, ε ≤ c / 4 → ∀ ω : Ω W q.L,
      step1GoodC W q ε ω → step1ResGood R W q ε ω → _ := fun W hW q hq ε hεc ω hG hR =>
    step1_point (hf W (le_of_max_le_left hW) c N q (hS W hq)) hN hc hεc (hbig W hW).1
      (hbig W hW).2 hG hR
  have hposW : ∀ W : ℕ, W0 ≤ W → ∀ q ∈ S W, 1 ≤ q.ratio ∧ 0 < zetaProp q.g W q.L q.u ∧
      (1 : ℝ) ≤ W := by
    intro W hW q hq
    have F := hf W (le_of_max_le_left hW) c N q (hS W hq)
    obtain ⟨-, -, -, hR1, -, -, -, -, -, hz0, -, -, -, -⟩ := step1_num F hN
    have hW0 : (0 : ℝ) < W := by exact_mod_cast (by have := F.two_le; omega : 0 < W)
    exact ⟨hR1, lt_of_lt_of_le (by positivity) hz0,
      by exact_mod_cast (by have := F.two_le; omega : 1 ≤ W)⟩
  have hK₀ : ∀ ε : ℝ, 0 < ε → ∃ W₂ : ℕ, ∀ W : ℕ, W₂ ≤ W → 256 * R.C ^ 5 ≤ (W : ℝ) ^ ε :=
    fun ε hε => step1_eventually_ge _ ε hε
  have hsplit : ∀ W : ℕ, 1 ≤ W → ∀ ε : ℝ, (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) = (W : ℝ) ^ ε := by
    intro W hW ε
    rw [← Real.rpow_add (by exact_mod_cast hW)]; ring_nf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- operator norms
    refine step1_prec_of_small ⟨W0, fun W hW q hq _ => by
      obtain ⟨h1, h2, h3⟩ := hposW W hW q hq; positivity⟩ (ε₀ := c / 4) (by positivity) ?_
    intro ε D hε hεc hD
    obtain ⟨W₁, h₁⟩ := hgood (ε / 2) D (by positivity) hD
    obtain ⟨W₂, h₂⟩ := hK₀ (ε / 2) (by positivity)
    refine ⟨max (max W₁ W₂) W0, fun W hW q hq => ?_⟩
    have hW0 : W0 ≤ W := le_of_max_le_right hW
    refine le_trans (measure_mono ?_) (h₁ W ((le_max_left _ _).trans (le_of_max_le_left hW)) q hq)
    rintro ω ⟨ab, hab⟩ ⟨hG, hR⟩
    obtain ⟨hR1, hz, hW1⟩ := hposW W hW0 q hq
    have hb := (hdet W hW0 q hq (ε / 2) (by linarith) ω hG hR).1 ab.1 ab.2
    have hK := h₂ W ((le_max_right _ _).trans (le_of_max_le_left hW))
    open scoped Matrix.Norms.L2Operator in
    rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at hab
    have hY : 0 ≤ (W : ℝ) ^ (ε / 2) * (W * q.ratio * zetaProp q.g W q.L q.u) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hz.le)
    refine absurd hab (not_lt.mpr (hb.trans (le_trans (mul_le_mul_of_nonneg_right hK hY)
      (le_of_eq ?_))))
    rw [← mul_assoc, hsplit W (by exact_mod_cast hW1) ε]
  · -- Hilbert–Schmidt norms
    refine step1_prec_of_small ⟨W0, fun W hW q hq _ => by
      obtain ⟨h1, h2, h3⟩ := hposW W hW q hq; positivity⟩ (ε₀ := c / 4) (by positivity) ?_
    intro ε D hε hεc hD
    obtain ⟨W₁, h₁⟩ := hgood (ε / 2) D (by positivity) hD
    obtain ⟨W₂, h₂⟩ := hK₀ (ε / 2) (by positivity)
    refine ⟨max (max W₁ W₂) W0, fun W hW q hq => ?_⟩
    have hW0 : W0 ≤ W := le_of_max_le_right hW
    refine le_trans (measure_mono ?_) (h₁ W ((le_max_left _ _).trans (le_of_max_le_left hW)) q hq)
    rintro ω ⟨ab, hab⟩ ⟨hG, hR⟩
    obtain ⟨hR1, hz, hW1⟩ := hposW W hW0 q hq
    have hb := (hdet W hW0 q hq (ε / 2) (by linarith) ω hG hR).2.1 ab.1 ab.2
    have hK := h₂ W ((le_max_right _ _).trans (le_of_max_le_left hW))
    have hnn : 0 ≤ blockHS2 (flowG W (q.at q.u) ω) ab.1 ab.2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    rw [Complex.norm_real, Real.norm_of_nonneg hnn] at hab
    have hY : 0 ≤ (W : ℝ) ^ (ε / 2) * ((W : ℝ) ^ 2 * q.ratio * zetaProp q.g W q.L q.u) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (mul_nonneg (mul_nonneg (by positivity) (by linarith)) hz.le)
    refine absurd hab (not_lt.mpr (hb.trans (le_trans (mul_le_mul_of_nonneg_right hK hY)
      (le_of_eq ?_))))
    rw [← mul_assoc, hsplit W (by exact_mod_cast hW1) ε]
  · -- centered block traces
    refine step1_prec_of_small ⟨W0, fun W hW q hq _ => by
      obtain ⟨h1, h2, h3⟩ := hposW W hW q hq; positivity⟩ (ε₀ := c / 4) (by positivity) ?_
    intro ε D hε hεc hD
    obtain ⟨W₁, h₁⟩ := hgood (ε / 2) D (by positivity) hD
    obtain ⟨W₂, h₂⟩ := hK₀ (ε / 2) (by positivity)
    refine ⟨max (max W₁ W₂) W0, fun W hW q hq => ?_⟩
    have hW0 : W0 ≤ W := le_of_max_le_right hW
    refine le_trans (measure_mono ?_) (h₁ W ((le_max_left _ _).trans (le_of_max_le_left hW)) q hq)
    rintro ω ⟨a, hab⟩ ⟨hG, hR⟩
    obtain ⟨hR1, hz, hW1⟩ := hposW W hW0 q hq
    have hb := (hdet W hW0 q hq (ε / 2) (by linarith) ω hG hR).2.2.1 a
    have hK := h₂ W ((le_max_right _ _).trans (le_of_max_le_left hW))
    have hY : 0 ≤ (W : ℝ) ^ (ε / 2) * (q.ratio ^ 2 * zetaProp q.g W q.L q.u) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (mul_nonneg (by positivity) hz.le)
    refine absurd hab (not_lt.mpr (hb.trans (le_trans (mul_le_mul_of_nonneg_right hK hY)
      (le_of_eq ?_))))
    rw [← mul_assoc, hsplit W (by exact_mod_cast hW1) ε]
  · -- loops
    intro k hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      refine step1_prec_of_small ⟨0, fun W _ q _ _ => by simp⟩ (ε₀ := c / 4)
        (by positivity) ?_
      intro ε D hε hεc hD
      obtain ⟨W₁, h₁⟩ := hgood ε D hε hD
      obtain ⟨W₂, h₂⟩ := step1_eventually_ge (R.C + 1) ε hε
      refine ⟨max (max W₁ W₂) W0, fun W hW q hq => ?_⟩
      have hW0 : W0 ≤ W := le_of_max_le_right hW
      refine le_trans (measure_mono ?_)
        (h₁ W ((le_max_left _ _).trans (le_of_max_le_left hW)) q hq)
      rintro ω ⟨w, hw⟩ ⟨hG, hR⟩
      have hb := (hdet W hW0 q hq ε hεc ω hG hR).2.2.2 (w.1 0)
      have hK := h₂ W ((le_max_right _ _).trans (le_of_max_le_left hW))
      have hb' : ‖loopTr (flowG W (q.at q.u) ω) w.1 w.2‖ ≤ R.C + 1 :=
        (step1_loopTr_one_norm (flowG W (q.at q.u) ω) w.1 w.2).le.trans hb
      have e : (q.ratio * zetaProp q.g W q.L q.u) ^ (1 - 1) = 1 := by simp
      rw [e, mul_one] at hw
      exact absurd hw (not_lt.mpr (hb'.trans hK))
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      refine step1_prec_of_small ⟨W0, fun W hW q hq _ => by
        obtain ⟨h1, h2, h3⟩ := hposW W hW q hq; positivity⟩ (ε₀ := c / 4) (by positivity) ?_
      intro ε D hε hεc hD
      set ε' := ε / (2 * (m + 2)) with hε'
      have hε'0 : 0 < ε' := by positivity
      have hε'c : ε' ≤ c / 4 := by
        have : ε' ≤ ε := by
          rw [hε', div_le_iff₀ (by positivity)]; nlinarith
        linarith
      obtain ⟨W₁, h₁⟩ := hgood ε' D hε'0 hD
      obtain ⟨W₂, h₂⟩ := step1_eventually_ge ((256 * R.C ^ 5) ^ (m + 1)) (ε / 2) (by positivity)
      refine ⟨max (max W₁ W₂) W0, fun W hW q hq => ?_⟩
      have hW0 : W0 ≤ W := le_of_max_le_right hW
      refine le_trans (measure_mono ?_)
        (h₁ W ((le_max_left _ _).trans (le_of_max_le_left hW)) q hq)
      rintro ω ⟨w, hw⟩ ⟨hG, hR⟩
      obtain ⟨hR1, hz, hW1⟩ := hposW W hW0 q hq
      have hWp : (0 : ℝ) < W := by linarith
      obtain ⟨hop, hhs, -, -⟩ := hdet W hW0 q hq ε' hε'c ω hG hR
      have hK := h₂ W ((le_max_right _ _).trans (le_of_max_le_left hW))
      set ζ := zetaProp q.g W q.L q.u with hζ
      set K₀ := 256 * R.C ^ 5 with hK₀def
      set A := (W : ℝ) ^ ε' with hA
      have hA0 : 0 < A := Real.rpow_pos_of_pos hWp _
      have hb := step1_loopTr_norm_le (flowG W (q.at q.u) ω) (by omega : 2 ≤ m + 2) w.1 w.2
        (O := K₀ * (A * (W * q.ratio * ζ))) (H := K₀ * (A * ((W : ℝ) ^ 2 * q.ratio * ζ)))
        (by positivity) (by positivity) hop hhs
      have he : ((W : ℝ)⁻¹) ^ (m + 2) * (K₀ * (A * ((W : ℝ) ^ 2 * q.ratio * ζ)) *
          (K₀ * (A * (W * q.ratio * ζ))) ^ (m + 2 - 2)) =
          K₀ ^ (m + 1) * A ^ (m + 1) * (q.ratio * ζ) ^ (m + 2 - 1) := by
        rw [show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega, inv_pow]
        have hWm : ((W : ℝ) ^ (m + 2)) ≠ 0 := pow_ne_zero _ hWp.ne'
        field_simp
        ring
      have hAp : A ^ (m + 1) ≤ (W : ℝ) ^ (ε / 2) := by
        rw [hA, ← Real.rpow_natCast, ← Real.rpow_mul hWp.le]
        apply Real.rpow_le_rpow_of_exponent_le hW1
        rw [hε']
        push_cast
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      rw [he] at hb
      refine absurd hw (not_lt.mpr (hb.trans ?_))
      rw [← hsplit W (by exact_mod_cast hW1) ε]
      have hX : 0 ≤ (q.ratio * ζ) ^ (m + 2 - 1) := by positivity
      calc K₀ ^ (m + 1) * A ^ (m + 1) * (q.ratio * ζ) ^ (m + 2 - 1)
          ≤ (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) * (q.ratio * ζ) ^ (m + 2 - 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hK hAp (by positivity)
              (Real.rpow_nonneg hWp.le _)) hX
        _ = _ := rfl
  · -- density
    refine step1_prec_of_small ⟨0, fun W _ q _ _ => zero_le_one⟩ (ε₀ := c / 4)
      (by positivity) ?_
    intro ε D hε hεc hD
    obtain ⟨W₁, h₁⟩ := hgood ε D hε hD
    obtain ⟨W₂, h₂⟩ := step1_eventually_ge (R.C + 1) ε hε
    refine ⟨max (max W₁ W₂) W0, fun W hW q hq => ?_⟩
    have hW0 : W0 ≤ W := le_of_max_le_right hW
    refine le_trans (measure_mono ?_)
      (h₁ W ((le_max_left _ _).trans (le_of_max_le_left hW)) q hq)
    rintro ω ⟨a, ha⟩ ⟨hG, hR⟩
    have hb := (hdet W hW0 q hq ε hεc ω hG hR).2.2.2 a
    have hK := h₂ W ((le_max_right _ _).trans (le_of_max_le_left hW))
    rw [Complex.norm_real, Real.norm_eq_abs, mul_one] at ha
    exact absurd ha (not_lt.mpr (((Complex.abs_im_le_norm _).trans hb).trans hK))

end LSBA
