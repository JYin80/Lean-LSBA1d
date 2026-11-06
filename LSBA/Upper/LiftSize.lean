import LSBA.Upper.LiftReconstruct

/-!
# The general lift and its size

The general lift `X = √2 g 𝒦₀* M` of Section 10 [sec:compact-proof], as the Hermitian array
`X_i = Σ_α √2 g ⟨M, 𝒦₀(ι_i H_α)⟩ H_α` (the Riesz representative of `R ↦ √2 g ⟨M, 𝒦₀ R⟩` in the
trace-orthonormal Hermitian basis); where `S_W(G) ≥ c₁ > 0` it solves `𝒜(X) = √2 M`, that is
`D_X F = √2 F M`, for every target `M` of the algebra (10.3) [eq:c-Lie]. On the cutoff
neighbourhood `max_i ‖V_i‖ ≤ K₁`, `|E| ≤ E₀`, the sizes (10.16) [eq:c-Fi-size], (10.17)
[eq:c-F-size] and (10.18) [eq:c-lift-size] hold with constants depending only on `E₀, K₁, c₁`,
for `z = max{1, g} E / g` and every `g > 0`.
-/

open Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The general lift `X = √2 g 𝒦₀* M` of Section 10 [sec:compact-proof]:
`X_i = Σ_α √2 g ⟨M, 𝒦₀(ι_i H_α)⟩ H_α`. -/
def liftField {W : ℕ} (g z : ℝ) (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Fin 1000 → Matrix (Fin W) (Fin W) ℂ :=
  fun i => ∑ k, ((Real.sqrt 2 * g * hsInner M (liftK0 g z V (Pi.single i (hermBasis W k))) : ℝ) :
    ℂ) • hermBasis W k

section LiftSizeAux

/-- `‖A‖² ≥ 0`. -/
private lemma LiftSize_hsSq_nonneg {k l : Type*} [Fintype k] [Fintype l] (A : Matrix k l ℂ) :
    0 ≤ hsSq A := by
  unfold hsSq; positivity

/-- `‖A + B‖² ≤ 2‖A‖² + 2‖B‖²`. -/
private lemma LiftSize_hsSq_add_le {k l : Type*} [Fintype k] [Fintype l] (A B : Matrix k l ℂ) :
    hsSq (A + B) ≤ 2 * hsSq A + 2 * hsSq B := by
  unfold hsSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have h := norm_add_le (A a b) (B a b)
  have h0 : 0 ≤ ‖A a b + B a b‖ := norm_nonneg _
  simp only [Matrix.add_apply]
  nlinarith [sq_nonneg (‖A a b‖ - ‖B a b‖), norm_nonneg (A a b), norm_nonneg (B a b)]

/-- `‖-A‖ = ‖A‖`. -/
private lemma LiftSize_hsSq_neg {k l : Type*} [Fintype k] [Fintype l] (A : Matrix k l ℂ) :
    hsSq (-A) = hsSq A := by
  simp [hsSq]

/-- `‖A - B‖² ≤ 2‖A‖² + 2‖B‖²`. -/
private lemma LiftSize_hsSq_sub_le {k l : Type*} [Fintype k] [Fintype l] (A B : Matrix k l ℂ) :
    hsSq (A - B) ≤ 2 * hsSq A + 2 * hsSq B := by
  rw [sub_eq_add_neg, ← LiftSize_hsSq_neg B]
  exact LiftSize_hsSq_add_le A (-B)

/-- `‖A*‖ = ‖A‖`. -/
private lemma LiftSize_hsSq_conjTranspose {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    hsSq Aᴴ = hsSq A := by
  simp only [hsSq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

/-- `‖c A‖² = |c|² ‖A‖²`. -/
private lemma LiftSize_hsSq_smul {k l : Type*} [Fintype k] [Fintype l] (c : ℂ) (A : Matrix k l ℂ) :
    hsSq (c • A) = ‖c‖ ^ 2 * hsSq A := by
  simp [hsSq, mul_pow, Finset.mul_sum]

/-- `‖A B‖² ≤ |A|²_op ‖B‖²`, column by column. -/
private lemma LiftSize_hsSq_mul_le {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    hsSq (A * B) ≤ ‖A‖ ^ 2 * hsSq B := by
  have hcol : ∀ b : n, ∑ a, ‖(A * B) a b‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ a, ‖B a b‖ ^ 2 := by
    intro b
    have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 (fun a => B a b))
    have h1 : ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ (fun a => B a b))‖ ^ 2 =
        ∑ a, ‖(A * B) a b‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      rfl
    have h2 : ‖(WithLp.toLp 2 (fun a => B a b) : EuclideanSpace ℂ n)‖ ^ 2 = ∑ a, ‖B a b‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    have h0 : 0 ≤ ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ (fun a => B a b))‖ := norm_nonneg _
    rw [← h1, ← h2, ← mul_pow]
    exact pow_le_pow_left₀ h0 h 2
  unfold hsSq
  rw [Finset.sum_comm, Finset.sum_comm (f := fun a b => ‖B a b‖ ^ 2), Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => hcol b

/-- `‖B A‖² ≤ |A|²_op ‖B‖²`. -/
private lemma LiftSize_hsSq_mul_le' {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    hsSq (B * A) ≤ ‖A‖ ^ 2 * hsSq B := by
  rw [← LiftSize_hsSq_conjTranspose, Matrix.conjTranspose_mul, ← Matrix.l2_opNorm_conjTranspose A,
    ← LiftSize_hsSq_conjTranspose B]
  exact LiftSize_hsSq_mul_le _ _

/-- `|C_i|_op ≤ |z| + g⁻¹ |V_i|_op`. -/
private lemma LiftSize_norm_liftC_le {W q : ℕ} {g : ℝ} (hg : 0 < g) (z : ℝ)
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

/-- `⟨A, Σ c_x B_x⟩ = Σ c_x ⟨A, B_x⟩` for real `c_x`. -/
private lemma LiftSize_hsInner_sum_right {k l ι : Type*} [Fintype k] [Fintype l]
    (A : Matrix k l ℂ) (s : Finset ι) (c : ι → ℝ) (B : ι → Matrix k l ℂ) :
    hsInner A (∑ x ∈ s, ((c x : ℝ) : ℂ) • B x) = ∑ x ∈ s, c x * hsInner A (B x) := by
  simp only [(hsInner_reCoord _ _ 0).1, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- `⟨Σ c_x A_x, B⟩ = Σ c_x ⟨A_x, B⟩` for real `c_x`. -/
private lemma LiftSize_hsInner_sum_left {k l ι : Type*} [Fintype k] [Fintype l]
    (s : Finset ι) (c : ι → ℝ) (A : ι → Matrix k l ℂ) (B : Matrix k l ℂ) :
    hsInner (∑ x ∈ s, ((c x : ℝ) : ℂ) • A x) B = ∑ x ∈ s, c x * hsInner (A x) B := by
  simp only [(hsInner_reCoord _ _ 0).1, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
    Complex.re_sum, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- Cauchy–Schwarz: `⟨A, B⟩² ≤ ‖A‖² ‖B‖²`. -/
private lemma LiftSize_hsInner_sq_le {k l : Type*} [Fintype k] [Fintype l] (A B : Matrix k l ℂ) :
    hsInner A B ^ 2 ≤ hsSq A * hsSq B := by
  rw [← (hsInner_reCoord A B 0).2.2.2.2, ← (hsInner_reCoord A A 0).2.1,
    ← (hsInner_reCoord B B 0).2.1, ← (hsInner_reCoord A A 0).2.2.2.2,
    ← (hsInner_reCoord B B 0).2.2.2.2]
  simpa [sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (reCoord A) (reCoord B)

/-- Orthonormality of the Hermitian basis: `⟨H_k, H_l⟩ = δ_{kl}`. -/
private lemma LiftSize_hsInner_hermBasis (W : ℕ) (k l : Fin W × Fin W) :
    hsInner (hermBasis W k) (hermBasis W l) = if k = l then 1 else 0 := by
  rw [(hsInner_reCoord _ _ 0).1, (hermBasis_isHermitian W k).eq, trace_hermBasis_mul]
  split_ifs <;> simp

/-- `‖Σ_k c_k H_k‖² = Σ_k c_k²` for real `c_k`. -/
private lemma LiftSize_hsSq_basis (W : ℕ) (c : Fin W × Fin W → ℝ) :
    hsSq (∑ k, ((c k : ℝ) : ℂ) • hermBasis W k) = ∑ k, c k ^ 2 := by
  rw [← (hsInner_reCoord (∑ k, ((c k : ℝ) : ℂ) • hermBasis W k) 0 0).2.1,
    LiftSize_hsInner_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LiftSize_hsInner_sum_right]
  simp [LiftSize_hsInner_hermBasis, sq]

/-- `‖A‖ = 0` implies `A = 0`. -/
private lemma LiftSize_eq_zero_of_hsSq {k l : Type*} [Fintype k] [Fintype l] {A : Matrix k l ℂ}
    (h : hsSq A = 0) : A = 0 := by
  unfold hsSq at h
  ext a b
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).1 h a
    (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by positivity)).1 h1 b
    (Finset.mem_univ _)
  simpa using h2

/-- Every entry of the extended array has `‖R_k‖² ≤ ‖R‖²`. -/
private lemma LiftSize_liftSeq_hsSq {W q : ℕ} (R : Fin q → Matrix (Fin W) (Fin W) ℂ) (k : ℕ) :
    hsSq (liftSeq R k) ≤ ∑ i, hsSq (R i) := by
  unfold liftSeq
  split_ifs with h
  · exact Finset.single_le_sum (f := fun i => hsSq (R i)) (fun i _ => LiftSize_hsSq_nonneg _)
      (Finset.mem_univ _)
  · rw [show hsSq (0 : Matrix (Fin W) (Fin W) ℂ) = 0 by simp [hsSq]]
    exact Finset.sum_nonneg fun i _ => LiftSize_hsSq_nonneg _

/-- Every entry of the extended blocks has operator norm at most `κ`. -/
private lemma LiftSize_liftSeq_norm {W q : ℕ} (C : Fin q → Matrix (Fin W) (Fin W) ℂ) {κ : ℝ}
    (hκ : 0 ≤ κ) (hC : ∀ i, ‖C i‖ ≤ κ) (k : ℕ) : ‖liftSeq C k‖ ≤ κ := by
  unfold liftSeq
  split_ifs with h
  · exact hC _
  · simpa using hκ

/-- `‖E‖² ≤ 4ⁿ κ² S` after `n` steps of the recursion of (10.12) [eq:c-data-map]. -/
private lemma LiftSize_liftEAux_le {W : ℕ} (C R : ℕ → Matrix (Fin W) (Fin W) ℂ) (top : ℕ)
    {κ S : ℝ} (hκ : 0 ≤ κ) (hS : 0 ≤ S) (hC : ∀ j, ‖C j‖ ≤ κ) (hR : ∀ j, hsSq (R j) ≤ S) :
    ∀ n, hsSq (liftEAux C R top n) ≤ 4 ^ n * (κ ^ 2 * S)
  | 0 => by
    rw [liftEAux, pow_zero, one_mul, show hsSq (0 : Matrix (Fin W) (Fin W) ℂ) = 0 by simp [hsSq]]
    positivity
  | n + 1 => by
    have ih := LiftSize_liftEAux_le C R top hκ hS hC hR n
    have h1 : hsSq (R (top - n) * C (top - n)) ≤ κ ^ 2 * S := by
      have hk : ‖C (top - n)‖ ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hC _) 2
      calc _ ≤ ‖C (top - n)‖ ^ 2 * hsSq (R (top - n)) := LiftSize_hsSq_mul_le' _ _
        _ ≤ κ ^ 2 * S := mul_le_mul hk (hR _) (LiftSize_hsSq_nonneg _) (by positivity)
    have h2 := LiftSize_hsSq_sub_le (-(R (top - n) * C (top - n))) (liftEAux C R top n)ᴴ
    rw [LiftSize_hsSq_neg, LiftSize_hsSq_conjTranspose] at h2
    have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    have h5 : 0 ≤ κ ^ 2 * S := by positivity
    simp only [liftEAux]
    rw [pow_succ]
    nlinarith

/-- `‖F_k(R)‖² ≤ 64 · 4⁹⁹⁹ (κ⁴ + 1) ‖R‖²` when every `|C_i|_op ≤ κ`. -/
private lemma LiftSize_liftF_le {W : ℕ} {g z κ : ℝ} {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ}
    (hκ : 0 ≤ κ) (hC : ∀ i, ‖liftC g z V i‖ ≤ κ) (R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
    (k : ℕ) : hsSq (liftF g z V R k) ≤ 64 * 4 ^ 999 * (κ ^ 4 + 1) * ∑ i, hsSq (R i) := by
  set S := ∑ i, hsSq (R i) with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => LiftSize_hsSq_nonneg _
  have hCs := LiftSize_liftSeq_norm (liftC g z V) hκ hC
  have hRs := LiftSize_liftSeq_hsSq R
  have hk2 : ∀ j, ‖liftSeq (liftC g z V) j‖ ^ 2 ≤ κ ^ 2 := fun j =>
    pow_le_pow_left₀ (norm_nonneg _) (hCs j) 2
  have hE : hsSq (liftE g z V R k) ≤ (4 : ℝ) ^ 999 * (κ ^ 2 * S) := by
    unfold liftE
    refine (LiftSize_liftEAux_le _ _ _ hκ hS hCs hRs _).trans ?_
    have : (4 : ℝ) ^ (1000 - 1 - k) ≤ 4 ^ 999 :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hc1 : (1 : ℝ) ≤ 4 ^ 999 := one_le_pow₀ (by norm_num)
  generalize (4 : ℝ) ^ 999 = c at hE hc1 ⊢
  set E := liftE g z V R k
  set Ck := liftSeq (liftC g z V) k
  have hE0 : 0 ≤ hsSq E := LiftSize_hsSq_nonneg _
  have t1 : hsSq (E * Ck) ≤ κ ^ 2 * hsSq E :=
    (LiftSize_hsSq_mul_le' _ _).trans (mul_le_mul_of_nonneg_right (hk2 k) hE0)
  have t2 : hsSq (Ck * Eᴴ) ≤ κ ^ 2 * hsSq E := by
    refine (LiftSize_hsSq_mul_le _ _).trans ?_
    rw [LiftSize_hsSq_conjTranspose]
    exact mul_le_mul_of_nonneg_right (hk2 k) hE0
  have t3 : hsSq (Ck * liftSeq R k * Ck) ≤ κ ^ 4 * S := by
    have a1 : hsSq (Ck * liftSeq R k) ≤ κ ^ 2 * S :=
      (LiftSize_hsSq_mul_le _ _).trans (mul_le_mul (hk2 k) (hRs k) (LiftSize_hsSq_nonneg _)
        (by positivity))
    calc _ ≤ ‖Ck‖ ^ 2 * hsSq (Ck * liftSeq R k) := LiftSize_hsSq_mul_le' _ _
      _ ≤ κ ^ 2 * (κ ^ 2 * S) := mul_le_mul (hk2 k) a1 (LiftSize_hsSq_nonneg _) (by positivity)
      _ = κ ^ 4 * S := by ring
  have t4 : hsSq (liftSeq R (k + 1)) ≤ S := hRs (k + 1)
  have t5 : hsSq (liftSeq R (k - 1)) ≤ S := hRs (k - 1)
  have s1 := LiftSize_hsSq_add_le (E * Ck) (Ck * Eᴴ)
  have s2 := LiftSize_hsSq_add_le (E * Ck + Ck * Eᴴ) (Ck * liftSeq R k * Ck)
  have s3 := LiftSize_hsSq_add_le (E * Ck + Ck * Eᴴ + Ck * liftSeq R k * Ck) (liftSeq R (k + 1))
  have s4 := LiftSize_hsSq_sub_le
    (E * Ck + Ck * Eᴴ + Ck * liftSeq R k * Ck + liftSeq R (k + 1)) (liftSeq R (k - 1))
  have hκ2 : 0 ≤ κ ^ 2 := by positivity
  have hEb : κ ^ 2 * hsSq E ≤ κ ^ 2 * (c * (κ ^ 2 * S)) := mul_le_mul_of_nonneg_left hE hκ2
  have hκ4 : κ ^ 2 * (c * (κ ^ 2 * S)) = c * (κ ^ 4 * S) := by ring
  have hκ4S : 0 ≤ κ ^ 4 * S := by positivity
  have f : 32 * (c * (κ ^ 4 * S)) + 8 * (κ ^ 4 * S) + 6 * S ≤ 64 * c * (κ ^ 4 + 1) * S := by
    have e : 64 * c * (κ ^ 4 + 1) * S = 64 * (c * (κ ^ 4 * S)) + 64 * (c * S) := by ring
    have a1 := mul_le_mul_of_nonneg_right hc1 hκ4S
    have a2 := mul_le_mul_of_nonneg_right hc1 hS
    rw [e]
    linarith
  change hsSq (E * Ck + Ck * Eᴴ + Ck * liftSeq R k * Ck + liftSeq R (k + 1) - liftSeq R (k - 1))
    ≤ _
  linarith

/-- `|C_i|_op ≤ (E₀ + K₁) max{1, g⁻¹}` for `z = max{1, g} E / g`. -/
private lemma LiftSize_norm_liftC_cut {W : ℕ} {g E E₀ K₁ : ℝ} (hg : 0 < g) (hE : |E| ≤ E₀)
    {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, ‖V i‖ ≤ K₁) (i : Fin 1000) :
    ‖liftC g (max 1 g * E / g) V i‖ ≤ (E₀ + K₁) * max 1 g⁻¹ := by
  have hE₀ : 0 ≤ E₀ := (abs_nonneg E).trans hE
  have hm : max 1 g / g ≤ max 1 g⁻¹ := by
    rcases le_total g 1 with h | h
    · rw [max_eq_left h, one_div]; exact le_max_right _ _
    · rw [max_eq_right h, div_self hg.ne']; exact le_max_left _ _
  have hz : |max 1 g * E / g| ≤ E₀ * max 1 g⁻¹ := by
    have hpos : 0 < max 1 g := lt_max_of_lt_left one_pos
    rw [abs_div, abs_mul, abs_of_pos hpos, abs_of_pos hg]
    calc max 1 g * |E| / g = (max 1 g / g) * |E| := by ring
      _ ≤ max 1 g⁻¹ * E₀ := mul_le_mul hm hE (abs_nonneg E) (by positivity)
      _ = E₀ * max 1 g⁻¹ := mul_comm _ _
  have hv : g⁻¹ * ‖V i‖ ≤ K₁ * max 1 g⁻¹ := by
    have hK : 0 ≤ K₁ := (norm_nonneg _).trans (hV i)
    calc g⁻¹ * ‖V i‖ ≤ max 1 g⁻¹ * K₁ :=
          mul_le_mul (le_max_right _ _) (hV i) (norm_nonneg _) (by positivity)
      _ = K₁ * max 1 g⁻¹ := mul_comm _ _
  calc _ ≤ |max 1 g * E / g| + g⁻¹ * ‖V i‖ := LiftSize_norm_liftC_le hg _ V i
    _ ≤ E₀ * max 1 g⁻¹ + K₁ * max 1 g⁻¹ := add_le_add hz hv
    _ = _ := by ring

/-- `max{1, g⁻¹}⁴ ≤ max{1, g⁻⁴}`. -/
private lemma LiftSize_pow_max_le (g : ℝ) :
    max 1 g⁻¹ ^ 4 ≤ max 1 (g⁻¹ ^ 4) := by
  rcases le_total 1 g⁻¹ with h | h
  · rw [max_eq_right h]; exact le_max_right _ _
  · rw [max_eq_left h, one_pow]; exact le_max_left _ _

/-- The algebra (10.3) [eq:c-Lie] is closed under `A - r B`, `r` real. -/
private lemma LiftSize_lieOmega_sub {W : ℕ} {A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hA : A ∈ lieOmega W) (hB : B ∈ lieOmega W) (r : ℝ) : A - (r : ℂ) • B ∈ lieOmega W := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
    calc Aᴴ * phJ W - (r : ℂ) • (Bᴴ * phJ W) + (phJ W * A - (r : ℂ) • (phJ W * B))
        = (Aᴴ * phJ W + phJ W * A) - (r : ℂ) • (Bᴴ * phJ W + phJ W * B) := by
          rw [smul_add]; abel
      _ = 0 := by rw [hA1, hB1, smul_zero, sub_zero]
  · rw [Matrix.trace_sub, Matrix.trace_smul, hA2, hB2, smul_zero, sub_zero]

/-- `⟨A - r B, C⟩ = ⟨A, C⟩ - r ⟨B, C⟩` for real `r`. -/
private lemma LiftSize_hsInner_sub_left {k l : Type*} [Fintype k] [Fintype l]
    (A B C : Matrix k l ℂ) (r : ℝ) :
    hsInner (A - (r : ℂ) • B) C = hsInner A C - r * hsInner B C := by
  simp only [(hsInner_reCoord _ _ 0).1, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul]

section LiftSizeK0

variable {W : ℕ} {g z c₁ : ℝ} {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ}

/-- `𝒦₀` commutes with finite real linear combinations. -/
private lemma LiftSize_liftK0_sum (hc₁ : 0 < c₁) (hV : ∀ i, (V i).IsHermitian)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V)) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (R : ι → Fin 1000 → Matrix (Fin W) (Fin W) ℂ) :
    liftK0 g z V (∑ x ∈ s, c x • R x) = ∑ x ∈ s, (c x : ℂ) • liftK0 g z V (R x) := by
  have hlin := (liftK0_spec (g := g) (z := z) hc₁ hV hc).1
  have h0 : liftK0 g z V 0 = 0 := by
    have h := hlin 1 0 0
    simp only [one_smul, add_zero, Complex.ofReal_one] at h
    exact left_eq_add.mp h
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hlin, ih]

/-- `⟨M, 𝒦₀ R⟩ = Σ_{i,k} d_{ik} ⟨M, 𝒦₀(ι_i H_k)⟩` for `R_i = Σ_k d_{ik} H_k`. -/
private lemma LiftSize_hsInner_liftK0 (hc₁ : 0 < c₁) (hV : ∀ i, (V i).IsHermitian)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V)) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (d : Fin 1000 → Fin W × Fin W → ℝ) :
    hsInner M (liftK0 g z V (fun i => ∑ k, ((d i k : ℝ) : ℂ) • hermBasis W k)) =
      ∑ i, ∑ k, d i k * hsInner M (liftK0 g z V (Pi.single i (hermBasis W k))) := by
  have e : (fun i => ∑ k, ((d i k : ℝ) : ℂ) • hermBasis W k) =
      ∑ p : Fin 1000 × (Fin W × Fin W), d p.1 p.2 • Pi.single p.1 (hermBasis W p.2) := by
    funext j
    symm
    rw [Finset.sum_apply, Fintype.sum_prod_type]
    simp only [Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
    simp [Complex.coe_smul]
  rw [e, LiftSize_liftK0_sum hc₁ hV hc, LiftSize_hsInner_sum_right, Fintype.sum_prod_type]

end LiftSizeK0

/-- The size of `𝒦₀ R` from the size of `𝓕 R` and `|C_q|_op ≤ κ`. -/
private lemma LiftSize_hsSq_liftK0_le {W : ℕ} {g z c₁ κ T : ℝ} (hc₁ : 0 < c₁)
    {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, (V i).IsHermitian)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V)) (hC : ∀ i, ‖liftC g z V i‖ ≤ κ)
    (R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
    (hT : ∑ j, hsSq (pairData g z V R j) ≤ T * ∑ i, hsSq (R i)) :
    hsSq (liftK0 g z V R) ≤
      ((2 + 16 * κ ^ 2) * (g ^ 2 / 2 * ((min c₁ 1 ^ 2)⁻¹ * T)) + 4 * κ ^ 4 + 3) *
        ∑ i, hsSq (R i) := by
  have hG : ∀ j, (layoutBlocks liftLayout V j).IsHermitian := by
    intro j
    unfold layoutBlocks Matrix.IsHermitian
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_smul, (hV i).eq, Complex.star_def, Complex.conj_ofReal]
  have hJ := ((cohLeftInv_spec hG hc₁ hc).2.1 (pairData g z V R)).2
  set S := ∑ i, hsSq (R i) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => LiftSize_hsSq_nonneg _
  have hRi : ∀ i, hsSq (R i) ≤ S := fun i =>
    Finset.single_le_sum (f := fun i => hsSq (R i)) (fun i _ => LiftSize_hsSq_nonneg _)
      (Finset.mem_univ _)
  set P := liftKP g z V R with hPdef
  set C := liftC g z V 999
  have hm : 0 ≤ (min c₁ 1 ^ 2)⁻¹ := by positivity
  have hP : hsSq P ≤ g ^ 2 / 2 * ((min c₁ 1 ^ 2)⁻¹ * T) * S := by
    rw [hPdef, liftKP, LiftSize_hsSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
      inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have h1 := mul_le_mul_of_nonneg_left hT hm
    have h2 := hJ.trans h1
    calc 2⁻¹ * g ^ 2 * hsSq (cohLeftInv (layoutBlocks liftLayout V) (pairData g z V R))
        ≤ 2⁻¹ * g ^ 2 * ((min c₁ 1 ^ 2)⁻¹ * (T * S)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have hk2 : ‖C‖ ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hC _) 2
  have hP0 : 0 ≤ hsSq P := LiftSize_hsSq_nonneg _
  have t1 : hsSq (P * C) ≤ κ ^ 2 * hsSq P :=
    (LiftSize_hsSq_mul_le' _ _).trans (mul_le_mul_of_nonneg_right hk2 hP0)
  have t2 : hsSq (C * Pᴴ) ≤ κ ^ 2 * hsSq P := by
    refine (LiftSize_hsSq_mul_le _ _).trans ?_
    rw [LiftSize_hsSq_conjTranspose]
    exact mul_le_mul_of_nonneg_right hk2 hP0
  have t3 : hsSq (C * R 999 * C) ≤ κ ^ 4 * S := by
    have a1 : hsSq (C * R 999) ≤ κ ^ 2 * S :=
      (LiftSize_hsSq_mul_le _ _).trans (mul_le_mul hk2 (hRi 999) (LiftSize_hsSq_nonneg _)
        (by positivity))
    calc _ ≤ ‖C‖ ^ 2 * hsSq (C * R 999) := LiftSize_hsSq_mul_le' _ _
      _ ≤ κ ^ 2 * (κ ^ 2 * S) := mul_le_mul hk2 a1 (LiftSize_hsSq_nonneg _) (by positivity)
      _ = κ ^ 4 * S := by ring
  have t4 := hRi 998
  have t5 := hRi 999
  have s1 := LiftSize_hsSq_add_le (P * C) (C * Pᴴ)
  have s2 := LiftSize_hsSq_add_le (P * C + C * Pᴴ) (C * R 999 * C)
  have s3 := LiftSize_hsSq_sub_le (P * C + C * Pᴴ + C * R 999 * C) (R 998)
  have hblk := (blockMat_algebra P (P * C + C * Pᴴ + C * R 999 * C - R 998) (R 999) (-Pᴴ)
    0 0 0 0).2.2.2
  rw [LiftSize_hsSq_neg, LiftSize_hsSq_conjTranspose] at hblk
  have hκP : κ ^ 2 * hsSq P ≤ κ ^ 2 * (g ^ 2 / 2 * ((min c₁ 1 ^ 2)⁻¹ * T) * S) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  change hsSq (blockMat P (P * C + C * Pᴴ + C * R 999 * C - R 998) (R 999) (-Pᴴ)) ≤ _
  rw [hblk]
  nlinarith

/-- `g⁴ max{1, g⁻¹}⁶` and `g² max{1, g⁻¹}⁴` are at most `max{g⁻², g⁴}`. -/
private lemma LiftSize_max_bounds {g : ℝ} (hg : 0 < g) :
    g ^ 4 * max 1 g⁻¹ ^ 6 ≤ max (g⁻¹ ^ 2) (g ^ 4) ∧
      g ^ 2 * max 1 g⁻¹ ^ 4 ≤ max (g⁻¹ ^ 2) (g ^ 4) := by
  rcases le_total g 1 with h | h
  · rw [max_eq_right ((one_le_inv₀ hg).2 h)]
    have e1 : g ^ 4 * g⁻¹ ^ 6 = g⁻¹ ^ 2 := by field_simp
    have e2 : g ^ 2 * g⁻¹ ^ 4 = g⁻¹ ^ 2 := by field_simp
    rw [e1, e2]
    exact ⟨le_max_left _ _, le_max_left _ _⟩
  · rw [max_eq_left (inv_le_one_of_one_le₀ h), one_pow, one_pow, mul_one, mul_one]
    exact ⟨le_max_right _ _, (pow_le_pow_right₀ h (by norm_num)).trans (le_max_right _ _)⟩

end LiftSizeAux

/-- (10.16) [eq:c-Fi-size], (10.17) [eq:c-F-size]: on `max_i ‖V_i‖ ≤ K₁`, `|E| ≤ E₀`,
`‖F_k(R)‖ ≤ C max{1, g⁻²} ‖R‖` at every input and `‖𝓕 R‖ ≤ C max{1, g⁻²} ‖R‖`, squared. -/
theorem hsSq_liftF_le (E₀ K₁ : ℝ) (hE₀ : 0 < E₀) (hK₁ : 0 < K₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ) (g E : ℝ) (V R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ),
      0 < g → |E| ≤ E₀ → (∀ i, ‖V i‖ ≤ K₁) →
        (∀ k : ℕ, hsSq (liftF g (max 1 g * E / g) V R k) ≤
          C * max 1 (g⁻¹ ^ 4) * ∑ i, hsSq (R i)) ∧
        ∑ j, hsSq (pairData g (max 1 g * E / g) V R j) ≤ C * max 1 (g⁻¹ ^ 4) * ∑ i, hsSq (R i) := by
  have hL := @LiftSize_liftF_le
  have hc1 : (1 : ℝ) ≤ 4 ^ 999 := one_le_pow₀ (by norm_num)
  generalize (4 : ℝ) ^ 999 = c at hL hc1
  have hc0 : 0 < c := by linarith
  set A : ℝ := 64 * c * ((E₀ + K₁) ^ 4 + 1) with hA
  have hA0 : 0 < A := by positivity
  refine ⟨512 * A, by positivity, fun W g E V R hg hE hV => ?_⟩
  set κ := (E₀ + K₁) * max 1 g⁻¹ with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hC := LiftSize_norm_liftC_cut hg hE hV
  set S := ∑ i, hsSq (R i) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => LiftSize_hsSq_nonneg _
  set P := max 1 (g⁻¹ ^ 4) with hP
  have hP1 : 1 ≤ P := le_max_left _ _
  have hκ4 : κ ^ 4 + 1 ≤ ((E₀ + K₁) ^ 4 + 1) * P := by
    have h1 := LiftSize_pow_max_le g
    have h2 : κ ^ 4 = (E₀ + K₁) ^ 4 * max 1 g⁻¹ ^ 4 := by rw [hκ, mul_pow]
    rw [h2]
    have h3 : (E₀ + K₁) ^ 4 * max 1 g⁻¹ ^ 4 ≤ (E₀ + K₁) ^ 4 * P :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  have hF : ∀ k : ℕ, hsSq (liftF g (max 1 g * E / g) V R k) ≤ A * P * S := by
    intro k
    refine (hL hκ0 hC R k).trans ?_
    rw [hA]
    have h4 : (0 : ℝ) ≤ 64 * c := by positivity
    have := mul_le_mul_of_nonneg_left hκ4 h4
    calc 64 * c * (κ ^ 4 + 1) * S ≤ 64 * c * (((E₀ + K₁) ^ 4 + 1) * P) * S :=
          mul_le_mul_of_nonneg_right this hS0
      _ = _ := by ring
  have hAPS : 0 ≤ A * P * S := by positivity
  refine ⟨fun k => (hF k).trans ?_, ?_⟩
  · nlinarith
  · calc ∑ j, hsSq (pairData g (max 1 g * E / g) V R j) ≤ ∑ _j : Fin 128, 4 * (A * P * S) := by
          refine Finset.sum_le_sum fun j _ => ?_
          unfold pairData
          have := LiftSize_hsSq_sub_le (liftF g (max 1 g * E / g) V R (liftPairI j))
            (liftF g (max 1 g * E / g) V R (liftPairK j))
          linarith [hF (liftPairI j), hF (liftPairK j)]
      _ = 512 * A * P * S := by simp; ring

/-- The general lift solves `𝒜(X) = √2 M` (Section 10 [sec:compact-proof], (G.21)
[eq:c-right-inverse]): where `S_W(G) ≥ c₁ > 0` for `G = liftLayout V`, for every target `M` of
the algebra (10.3) [eq:c-Lie]; every `X_i` is Hermitian. -/
theorem prodDiff_liftField {W : ℕ} {g z c₁ : ℝ} (hg : 0 < g) (hc₁ : 0 < c₁)
    {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, (V i).IsHermitian)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V)) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (∀ i, (liftField g z V M i).IsHermitian) ∧
      (M ∈ lieOmega W → prodDiff g z V (liftField g z V M) = ((Real.sqrt 2 : ℝ) : ℂ) • M) := by
  have hX : ∀ i, (liftField g z V M i).IsHermitian := by
    intro i
    unfold liftField Matrix.IsHermitian
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      (hermBasis_isHermitian W k).eq]
  refine ⟨hX, fun hM => ?_⟩
  have key : ∀ Z ∈ lieOmega W,
      hsInner (prodDiff g z V (liftField g z V M)) Z = Real.sqrt 2 * hsInner M Z := by
    intro Z hZ
    have hP := hsInner_prodDiff (g := g) (z := z) hV (liftField g z V M) hZ
    rw [hP.2]
    have hRh : ∀ i, (blockPart (liftConj g z V Z i) 1 0).IsHermitian := by
      intro i
      have h := hP.1 i
      rw [← (blockMat_blockPart (liftConj g z V Z i) 0 0 0 0).1, mem_lieOmega_iff] at h
      exact h.2.1
    have hRe : (fun i => blockPart (liftConj g z V Z i) 1 0) = fun i =>
        ∑ k, ((hsInner (hermBasis W k) (blockPart (liftConj g z V Z i) 1 0) : ℝ) : ℂ) •
          hermBasis W k :=
      funext fun i => (hermBasis_parseval W _).2 (hRh i)
    have hK := liftK0_liftConj (g := g) (z := z) hg hc₁ hV hc hZ
    rw [hRe] at hK
    have h1 : hsInner M Z = ∑ i, ∑ k, hsInner (hermBasis W k) (blockPart (liftConj g z V Z i) 1 0) *
        hsInner M (liftK0 g z V (Pi.single i (hermBasis W k))) := by
      conv_lhs => rw [← hK]
      rw [LiftSize_hsInner_liftK0 hc₁ hV hc]
    rw [h1]
    unfold liftField
    simp only [LiftSize_hsInner_sum_left]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  have hD := LiftSize_lieOmega_sub (prodDiff_mem_lieOmega (g := g) (z := z) hV hX) hM
    (Real.sqrt 2)
  set D := prodDiff g z V (liftField g z V M) - ((Real.sqrt 2 : ℝ) : ℂ) • M with hDdef
  have hDD : hsSq D = 0 := by
    rw [← (hsInner_reCoord D D 0).2.1]
    conv_lhs => rw [hDdef]
    rw [LiftSize_hsInner_sub_left, key D hD, sub_self]
  exact sub_eq_zero.mp (LiftSize_eq_zero_of_hsSq hDD)

/-- (10.18) [eq:c-lift-size]: on `max_i ‖V_i‖ ≤ K₁`, `S_W(G) ≥ c₁`, `|E| ≤ E₀`,
`‖X‖ ≤ C max{g⁻¹, g²} ‖M‖`, squared. -/
theorem sum_hsSq_liftField_le (E₀ K₁ c₁ : ℝ) (hE₀ : 0 < E₀) (hK₁ : 0 < K₁) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ) (g E : ℝ) (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
      (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), 0 < g → |E| ≤ E₀ →
      (∀ i, (V i).IsHermitian) → (∀ i, ‖V i‖ ≤ K₁) → c₁ ≤ coerMin (layoutBlocks liftLayout V) →
        ∑ i, hsSq (liftField g (max 1 g * E / g) V M i) ≤
          C * max (g⁻¹ ^ 2) (g ^ 4) * hsSq M := by
  obtain ⟨C₁, hC₁, hF⟩ := hsSq_liftF_le E₀ K₁ hE₀ hK₁
  set K := E₀ + K₁ with hK
  set a := (min c₁ 1 ^ 2)⁻¹ * C₁ with ha
  have ha0 : 0 ≤ a := by positivity
  refine ⟨(2 + 16 * K ^ 2) * a + 8 * K ^ 4 + 6, by positivity,
    fun W g E V M hg hE hVh hVn hc => ?_⟩
  set z := max 1 g * E / g with hz
  set h := max 1 g⁻¹ with hh
  have h1 : 1 ≤ h := le_max_left _ _
  have hCz := LiftSize_norm_liftC_cut hg hE hVn
  set P' := max 1 (g⁻¹ ^ 4) with hP'
  have hP'0 : 0 ≤ P' := zero_le_one.trans (le_max_left _ _)
  have hP'h : P' ≤ h ^ 4 :=
    max_le (one_le_pow₀ h1) (pow_le_pow_left₀ (by positivity) (le_max_right _ _) 4)
  set B := (2 + 16 * (K * h) ^ 2) * (g ^ 2 / 2 * ((min c₁ 1 ^ 2)⁻¹ * (C₁ * P'))) +
    4 * (K * h) ^ 4 + 3 with hB
  have hB0 : 0 ≤ B := by positivity
  have hK0 : ∀ R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ,
      hsSq (liftK0 g z V R) ≤ B * ∑ i, hsSq (R i) := by
    intro R
    exact LiftSize_hsSq_liftK0_le hc₁ hVh hc hCz R (hF W g E V R hg hE hVn).2
  set v : Fin 1000 → Fin W × Fin W → ℝ :=
    fun i k => hsInner M (liftK0 g z V (Pi.single i (hermBasis W k))) with hv
  set X := liftField g z V M with hX
  have hXe : X = fun i => ∑ k, ((Real.sqrt 2 * g * v i k : ℝ) : ℂ) • hermBasis W k := rfl
  set Q := ∑ i, hsSq (X i) with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => LiftSize_hsSq_nonneg _
  have hQe : Q = Real.sqrt 2 * g * hsInner M (liftK0 g z V X) := by
    rw [hQ, hXe, LiftSize_hsInner_liftK0 hc₁ hVh hc]
    simp only [LiftSize_hsSq_basis]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hQsq : Q * Q ≤ (2 * g ^ 2 * B * hsSq M) * Q := by
    have hcs := LiftSize_hsInner_sq_le M (liftK0 g z V X)
    have hk := hK0 X
    have hM0 := LiftSize_hsSq_nonneg M
    calc Q * Q = 2 * g ^ 2 * hsInner M (liftK0 g z V X) ^ 2 := by rw [hQe]; ring_nf; rw [hs2]; ring
      _ ≤ 2 * g ^ 2 * (hsSq M * hsSq (liftK0 g z V X)) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ ≤ 2 * g ^ 2 * (hsSq M * (B * Q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk hM0) (by positivity)
      _ = _ := by ring
  have hQB : Q ≤ 2 * g ^ 2 * B * hsSq M := by
    rcases hQ0.lt_or_eq with hpos | hzero
    · exact le_of_mul_le_mul_right hQsq hpos
    · rw [← hzero]; have := LiftSize_hsSq_nonneg M; positivity
  set Mx := max (g⁻¹ ^ 2) (g ^ 4) with hMx
  have hu : g ^ 4 * h ^ 6 ≤ Mx := (LiftSize_max_bounds hg).1
  have hw : g ^ 2 * h ^ 4 ≤ Mx := (LiftSize_max_bounds hg).2
  have e : 2 * g ^ 2 * B =
      (2 + 16 * K ^ 2 * h ^ 2) * (g ^ 4 * (a * P')) + 8 * K ^ 4 * (g ^ 2 * h ^ 4) + 6 * g ^ 2 := by
    rw [hB, ha]; ring
  have p1 : (2 + 16 * K ^ 2 * h ^ 2) * (g ^ 4 * (a * P')) ≤
      (2 + 16 * K ^ 2 * h ^ 2) * (g ^ 4 * (a * h ^ 4)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP'h ha0)
      (by positivity)) (by positivity)
  have p2 : (2 + 16 * K ^ 2 * h ^ 2) * (g ^ 4 * (a * h ^ 4)) =
      2 * (a * (g ^ 4 * h ^ 4)) + 16 * (K ^ 2 * a * (g ^ 4 * h ^ 6)) := by ring
  have p3 : g ^ 4 * h ^ 4 ≤ g ^ 4 * h ^ 6 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by norm_num)) (by positivity)
  have p4 : g ^ 2 ≤ g ^ 2 * h ^ 4 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ h1)
  have q1 : a * (g ^ 4 * h ^ 6) ≤ a * Mx := mul_le_mul_of_nonneg_left hu ha0
  have q2 : a * (g ^ 4 * h ^ 4) ≤ a * (g ^ 4 * h ^ 6) := mul_le_mul_of_nonneg_left p3 ha0
  have q3 : K ^ 2 * a * (g ^ 4 * h ^ 6) ≤ K ^ 2 * a * Mx :=
    mul_le_mul_of_nonneg_left hu (by positivity)
  have q4 : K ^ 4 * (g ^ 2 * h ^ 4) ≤ K ^ 4 * Mx := mul_le_mul_of_nonneg_left hw (by positivity)
  have hfin : 2 * g ^ 2 * B ≤ ((2 + 16 * K ^ 2) * a + 8 * K ^ 4 + 6) * Mx := by
    rw [e]
    have r : ((2 + 16 * K ^ 2) * a + 8 * K ^ 4 + 6) * Mx =
        2 * (a * Mx) + 16 * (K ^ 2 * a * Mx) + 8 * (K ^ 4 * Mx) + 6 * Mx := by ring
    rw [r]
    linarith
  exact hQB.trans (mul_le_mul_of_nonneg_right hfin (LiftSize_hsSq_nonneg M))

end LSBA
