import LSBA.Upper.LiftReconstruct

/-!
# Input derivatives of the data map and of `𝓛`

The bounds (10.20) [eq:c-F-bounds] and (10.21) [eq:c-L-bounds] over the derivatives
`D_{i,α} = H_α · ∇_{V_i}` in every input `i` and every direction `H_α` of the
trace-orthonormal Hermitian basis: the adjoint derivatives of the data map `𝓕`, written through
their coordinates `⟨Z, (D_{i,α} 𝓕)(ι_k H_β)⟩` in the basis of Hermitian arrays, satisfy
`Σ ‖(D_{i,α} 𝓕)* Z‖² ≤ C W max{g⁻², g⁻⁴} ‖Z‖²` on `max_i ‖V_i‖ ≤ K₁`, `|E| ≤ E₀`; and, since
`𝓛` is linear in the inputs with `D_{i,α} 𝓛 = 𝓛_{G(ι_i H_α)}` and `𝓛* D = Σ_j G_j (D_j + D_j*)`,
`Σ ‖(D_{i,α} 𝓛) P‖² ≤ 512 W ‖P‖²` and `Σ ‖(D_{i,α} 𝓛)* Z‖² ≤ 4 W ‖Z‖²` (Section 10
[sec:compact-proof]).
-/

open Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

section LiftDataDerivAux

private lemma LiftDataDeriv_hsSq_nonneg {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) : 0 ≤ hsSq A := by
  unfold hsSq; positivity

private lemma LiftDataDeriv_hsSq_conj {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    hsSq Aᴴ = hsSq A := by
  unfold hsSq; rw [Finset.sum_comm]; simp [Matrix.conjTranspose_apply]

private lemma LiftDataDeriv_hsSq_smul {W : ℕ} (w : ℂ) (A : Matrix (Fin W) (Fin W) ℂ) :
    hsSq (w • A) = ‖w‖ ^ 2 * hsSq A := by
  unfold hsSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [mul_pow]

private lemma LiftDataDeriv_hsSq_add_le {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) :
    hsSq (A + B) ≤ 2 * hsSq A + 2 * hsSq B := by
  unfold hsSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have h := norm_add_le (A a b) (B a b)
  have h0 := norm_nonneg (A a b + B a b)
  simp only [Matrix.add_apply]
  nlinarith [sq_nonneg (‖A a b‖ - ‖B a b‖), norm_nonneg (A a b), norm_nonneg (B a b)]

private lemma LiftDataDeriv_hsSq_one (W : ℕ) : hsSq (1 : Matrix (Fin W) (Fin W) ℂ) = W := by
  unfold hsSq
  simp [Matrix.one_apply, apply_ite]

/-- `‖A u‖² ≤ ‖A‖² ‖u‖²` for the operator norm. -/
private lemma LiftDataDeriv_nsq_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) (u : Fin W → ℂ) :
    ∑ i, ‖(A *ᵥ u) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ i, ‖u i‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 u)
  have h1 : ‖(EuclideanSpace.equiv (Fin W) ℂ).symm (A *ᵥ u)‖ ^ 2 = ∑ i, ‖(A *ᵥ u) i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin W))‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  rw [← h1, ← h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- `‖A Z‖²_HS ≤ ‖A‖² ‖Z‖²_HS`. -/
private lemma LiftDataDeriv_hsSq_mul_left {W : ℕ} (A Z : Matrix (Fin W) (Fin W) ℂ) :
    hsSq (A * Z) ≤ ‖A‖ ^ 2 * hsSq Z := by
  unfold hsSq
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖Z i j‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := LiftDataDeriv_nsq_le A (fun i => Z i j)
  have e : (A *ᵥ fun i => Z i j) = fun i => (A * Z) i j := by
    funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [e] at h
  exact h

/-- `‖Z A‖²_HS ≤ ‖A‖² ‖Z‖²_HS`. -/
private lemma LiftDataDeriv_hsSq_mul_right {W : ℕ} (Z A : Matrix (Fin W) (Fin W) ℂ) :
    hsSq (Z * A) ≤ ‖A‖ ^ 2 * hsSq Z := by
  have h := LiftDataDeriv_hsSq_mul_left Aᴴ Zᴴ
  rwa [← Matrix.conjTranspose_mul, LiftDataDeriv_hsSq_conj, Matrix.l2_opNorm_conjTranspose,
    LiftDataDeriv_hsSq_conj] at h

private lemma LiftDataDeriv_inner_tr {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) :
    hsInner A B = (Aᴴ * B).trace.re := (hsInner_reCoord A B 0).1

private lemma LiftDataDeriv_inner_comm {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) :
    hsInner A B = hsInner B A := by
  unfold hsInner
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [Complex.mul_re]
  ring

private lemma LiftDataDeriv_inner_add {W : ℕ} (Z A B : Matrix (Fin W) (Fin W) ℂ) :
    hsInner Z (A + B) = hsInner Z A + hsInner Z B := by
  simp only [hsInner, Matrix.add_apply, mul_add, Complex.add_re, Finset.sum_add_distrib]

private lemma LiftDataDeriv_inner_smul {W : ℕ} (Z A : Matrix (Fin W) (Fin W) ℂ) (r : ℝ) :
    hsInner Z (r • A) = r * hsInner Z A := by
  unfold hsInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Complex.mul_re]
  ring

private lemma LiftDataDeriv_inner_neg {W : ℕ} (Z A : Matrix (Fin W) (Fin W) ℂ) :
    hsInner Z (-A) = -hsInner Z A := by
  simp only [hsInner, Matrix.neg_apply, mul_neg, Complex.neg_re, Finset.sum_neg_distrib]

private lemma LiftDataDeriv_inner_mul_left {W : ℕ} (Z P A : Matrix (Fin W) (Fin W) ℂ) :
    hsInner Z (P * A) = hsInner (Pᴴ * Z) A := by
  rw [LiftDataDeriv_inner_tr, LiftDataDeriv_inner_tr, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

private lemma LiftDataDeriv_inner_mul_right {W : ℕ} (Z A S : Matrix (Fin W) (Fin W) ℂ) :
    hsInner Z (A * S) = hsInner (Z * Sᴴ) A := by
  rw [LiftDataDeriv_inner_tr, LiftDataDeriv_inner_tr, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc S, Matrix.trace_mul_comm S,
    Matrix.mul_assoc]

private lemma LiftDataDeriv_inner_conj {W : ℕ} (Z A : Matrix (Fin W) (Fin W) ℂ) :
    hsInner Z Aᴴ = hsInner Zᴴ A := by
  rw [LiftDataDeriv_inner_tr, LiftDataDeriv_inner_tr, Matrix.conjTranspose_conjTranspose,
    ← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose, Matrix.trace_mul_comm Z]
  simp

/-- `Σ_x ⟨Z, f x⟩² ≤ K ‖Z‖²` for every `Z`: the squared norm of the adjoint of
`c ↦ Σ_x c_x f x` is at most `K`. -/
private def LiftDataDeriv_Good {ι : Type*} [Fintype ι] {W : ℕ}
    (f : ι → Matrix (Fin W) (Fin W) ℂ) (K : ℝ) : Prop :=
  ∀ Z : Matrix (Fin W) (Fin W) ℂ, ∑ x, hsInner Z (f x) ^ 2 ≤ K * hsSq Z

variable {ι : Type*} [Fintype ι] {W : ℕ}

private lemma LiftDataDeriv_Good_mono {f : ι → Matrix (Fin W) (Fin W) ℂ} {K K' : ℝ}
    (h : LiftDataDeriv_Good f K) (hK : K ≤ K') : LiftDataDeriv_Good f K' := fun Z =>
  (h Z).trans (mul_le_mul_of_nonneg_right hK (LiftDataDeriv_hsSq_nonneg Z))

private lemma LiftDataDeriv_Good_congr {f f' : ι → Matrix (Fin W) (Fin W) ℂ} {K : ℝ}
    (h : LiftDataDeriv_Good f K) (e : ∀ x, f' x = f x) : LiftDataDeriv_Good f' K := by
  intro Z; simpa only [e] using h Z

private lemma LiftDataDeriv_Good_zero :
    LiftDataDeriv_Good (fun _ : ι => (0 : Matrix (Fin W) (Fin W) ℂ)) 0 := fun Z => by
  simp [hsInner]

private lemma LiftDataDeriv_Good_add {f f' : ι → Matrix (Fin W) (Fin W) ℂ} {K K' : ℝ}
    (h : LiftDataDeriv_Good f K) (h' : LiftDataDeriv_Good f' K') :
    LiftDataDeriv_Good (fun x => f x + f' x) (2 * K + 2 * K') := by
  intro Z
  have h1 := h Z
  have h2 := h' Z
  simp only [LiftDataDeriv_inner_add]
  calc ∑ x, (hsInner Z (f x) + hsInner Z (f' x)) ^ 2
      ≤ ∑ x, (2 * hsInner Z (f x) ^ 2 + 2 * hsInner Z (f' x) ^ 2) :=
        Finset.sum_le_sum fun x _ => by
          nlinarith [sq_nonneg (hsInner Z (f x) - hsInner Z (f' x))]
    _ = 2 * ∑ x, hsInner Z (f x) ^ 2 + 2 * ∑ x, hsInner Z (f' x) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (2 * K + 2 * K') * hsSq Z := by nlinarith

private lemma LiftDataDeriv_Good_smul {f : ι → Matrix (Fin W) (Fin W) ℂ} {K : ℝ} (r : ℝ)
    (h : LiftDataDeriv_Good f K) : LiftDataDeriv_Good (fun x => r • f x) (r ^ 2 * K) := by
  intro Z
  simp only [LiftDataDeriv_inner_smul, mul_pow]
  rw [← Finset.mul_sum, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h Z) (sq_nonneg r)

private lemma LiftDataDeriv_Good_neg {f : ι → Matrix (Fin W) (Fin W) ℂ} {K : ℝ}
    (h : LiftDataDeriv_Good f K) : LiftDataDeriv_Good (fun x => -f x) K := by
  intro Z
  simpa only [LiftDataDeriv_inner_neg, neg_sq] using h Z

private lemma LiftDataDeriv_Good_conj {f : ι → Matrix (Fin W) (Fin W) ℂ} {K : ℝ}
    (h : LiftDataDeriv_Good f K) : LiftDataDeriv_Good (fun x => (f x)ᴴ) K := by
  intro Z
  simpa only [LiftDataDeriv_inner_conj, LiftDataDeriv_hsSq_conj] using h Zᴴ

private lemma LiftDataDeriv_Good_mul_left {f : ι → Matrix (Fin W) (Fin W) ℂ} {K κ : ℝ}
    (P : Matrix (Fin W) (Fin W) ℂ) (hK : 0 ≤ K) (hP : ∀ Z, hsSq (Pᴴ * Z) ≤ κ * hsSq Z)
    (h : LiftDataDeriv_Good f K) : LiftDataDeriv_Good (fun x => P * f x) (K * κ) := by
  intro Z
  simp only [LiftDataDeriv_inner_mul_left]
  calc _ ≤ K * hsSq (Pᴴ * Z) := h _
    _ ≤ K * (κ * hsSq Z) := mul_le_mul_of_nonneg_left (hP Z) hK
    _ = K * κ * hsSq Z := by ring

private lemma LiftDataDeriv_Good_mul_right {f : ι → Matrix (Fin W) (Fin W) ℂ} {K κ : ℝ}
    (S : Matrix (Fin W) (Fin W) ℂ) (hK : 0 ≤ K) (hS : ∀ Z, hsSq (Z * Sᴴ) ≤ κ * hsSq Z)
    (h : LiftDataDeriv_Good f K) : LiftDataDeriv_Good (fun x => f x * S) (K * κ) := by
  intro Z
  simp only [LiftDataDeriv_inner_mul_right]
  calc _ ≤ K * hsSq (Z * Sᴴ) := h _
    _ ≤ K * (κ * hsSq Z) := mul_le_mul_of_nonneg_left (hS Z) hK
    _ = K * κ * hsSq Z := by ring

private lemma LiftDataDeriv_Good_basis (W : ℕ) : LiftDataDeriv_Good (hermBasis W) 1 := by
  intro Z
  simp only [LiftDataDeriv_inner_comm Z, one_mul]
  exact (hermBasis_parseval W Z).1

private lemma LiftDataDeriv_Good_herm_left {f : ι → Matrix (Fin W) (Fin W) ℂ} {K : ℝ}
    (h : LiftDataDeriv_Good f K) :
    LiftDataDeriv_Good (fun p : (Fin W × Fin W) × ι => hermBasis W p.1 * f p.2) (W * K) := by
  intro Z
  rw [Fintype.sum_prod_type]
  simp only [LiftDataDeriv_inner_mul_left, (hermBasis_isHermitian W _).eq]
  have hc := (hermBasis_completeness W 1 Z).2
  simp only [Matrix.one_mul, LiftDataDeriv_hsSq_one] at hc
  calc _ ≤ ∑ a, K * hsSq (hermBasis W a * Z) := Finset.sum_le_sum fun a _ => h _
    _ = W * K * hsSq Z := by rw [← Finset.mul_sum, hc]; ring

private lemma LiftDataDeriv_Good_herm_right {f : ι → Matrix (Fin W) (Fin W) ℂ} {K : ℝ}
    (h : LiftDataDeriv_Good f K) :
    LiftDataDeriv_Good (fun p : (Fin W × Fin W) × ι => f p.2 * hermBasis W p.1) (W * K) := by
  intro Z
  rw [Fintype.sum_prod_type]
  simp only [LiftDataDeriv_inner_mul_right, (hermBasis_isHermitian W _).eq]
  have hc := (hermBasis_completeness W Z 1).2
  simp only [Matrix.mul_one, LiftDataDeriv_hsSq_one] at hc
  calc _ ≤ ∑ a, K * hsSq (Z * hermBasis W a) := Finset.sum_le_sum fun a _ => h _
    _ = W * K * hsSq Z := by rw [← Finset.mul_sum, hc]; ring

/-- `M ↦ ±M` or `M ↦ ±M*` with the sign and the adjoint alternating in `d`:
`alt 0 M = M*`, `alt (d + 1) M = -(alt d M)*`. -/
private def LiftDataDeriv_alt {W : ℕ} :
    ℕ → Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ
  | 0, M => Mᴴ
  | d + 1, M => -(LiftDataDeriv_alt d M)ᴴ

private lemma LiftDataDeriv_alt_zero (d : ℕ) :
    LiftDataDeriv_alt d (0 : Matrix (Fin W) (Fin W) ℂ) = 0 := by
  induction d with
  | zero => simp [LiftDataDeriv_alt]
  | succ d ih => simp [LiftDataDeriv_alt, ih]

private lemma LiftDataDeriv_Good_alt {f : ι → Matrix (Fin W) (Fin W) ℂ} {K : ℝ} (d : ℕ)
    (h : LiftDataDeriv_Good f K) : LiftDataDeriv_Good (fun x => LiftDataDeriv_alt d (f x)) K := by
  induction d with
  | zero => exact LiftDataDeriv_Good_conj h
  | succ d ih => exact LiftDataDeriv_Good_neg (LiftDataDeriv_Good_conj ih)

/-- `E` for data supported at one index: `R_l = δ_{lk} H` gives
`E_e = alt (k - e) (H X_k)` for `e < k ≤ top`, and `E_e = 0` otherwise. -/
private lemma LiftDataDeriv_liftEAux_single {W : ℕ} (X R : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (top k : ℕ) (H : Matrix (Fin W) (Fin W) ℂ) (hR : ∀ l, R l = if l = k then H else 0) :
    ∀ n, n ≤ top → liftEAux X R top n =
      if top - n < k ∧ k ≤ top then LiftDataDeriv_alt (k - (top - n)) (H * X k) else 0
  | 0, _ => by
    rw [ite_eq_right (by omega)]
    rfl
  | n + 1, hn => by
    rw [liftEAux, LiftDataDeriv_liftEAux_single X R top k H hR n (by omega), hR]
    by_cases h1 : top - n = k
    · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left (by omega),
        show k - (top - (n + 1)) = 0 + 1 by omega]
      subst h1
      simp [LiftDataDeriv_alt]
    · rw [ite_eq_right h1]
      by_cases h2 : top - n < k ∧ k ≤ top
      · rw [ite_eq_left h2, ite_eq_left (by omega),
          show k - (top - (n + 1)) = (k - (top - n)) + 1 by omega]
        simp [LiftDataDeriv_alt]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]
        simp

/-- `E` is real-linear in the sequence `C`. -/
private lemma LiftDataDeriv_liftEAux_lin {W : ℕ} (C D R : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (t : ℝ) (top : ℕ) : ∀ n,
    liftEAux (C + t • D) R top n = liftEAux C R top n + t • liftEAux D R top n
  | 0 => by simp [liftEAux]
  | n + 1 => by
    simp only [liftEAux, LiftDataDeriv_liftEAux_lin C D R t top n, Pi.add_apply,
      Pi.smul_apply, Matrix.mul_add, Matrix.mul_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, star_trivial]
    module

/-- The first-order part of `F_m` along `C ↦ C + t D`. -/
private def LiftDataDeriv_dF {W : ℕ} (C D R : ℕ → Matrix (Fin W) (Fin W) ℂ) (m : ℕ) :
    Matrix (Fin W) (Fin W) ℂ :=
  liftEAux D R (1000 - 1) (1000 - 1 - m) * C m + liftEAux C R (1000 - 1) (1000 - 1 - m) * D m +
    D m * (liftEAux C R (1000 - 1) (1000 - 1 - m))ᴴ +
    C m * (liftEAux D R (1000 - 1) (1000 - 1 - m))ᴴ + D m * R m * C m + C m * R m * D m

/-- The second-order part of `F_m` along `C ↦ C + t D`. -/
private def LiftDataDeriv_qF {W : ℕ} (D R : ℕ → Matrix (Fin W) (Fin W) ℂ) (m : ℕ) :
    Matrix (Fin W) (Fin W) ℂ :=
  liftEAux D R (1000 - 1) (1000 - 1 - m) * D m +
    D m * (liftEAux D R (1000 - 1) (1000 - 1 - m))ᴴ + D m * R m * D m

/-- `C_l(V + t ι_i H) = C_l(V) - t g⁻¹ δ_{il} H`. -/
private lemma LiftDataDeriv_liftC_pert {W : ℕ} (g z t : ℝ)
    (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) (i : Fin 1000) (H : Matrix (Fin W) (Fin W) ℂ) :
    liftSeq (liftC g z (V + Pi.single i ((t : ℂ) • H))) =
      liftSeq (liftC g z V) + t • liftSeq (Pi.single i ((-g⁻¹) • H)) := by
  funext l
  simp only [Pi.add_apply, Pi.smul_apply]
  unfold liftSeq
  by_cases hl : l < 1000
  · simp only [hl, dite_true]
    ext a b
    by_cases hi : (⟨l, hl⟩ : Fin 1000) = i
    · subst hi
      simp [liftC]
      ring
    · simp [liftC, hi]
  · simp [hl]

/-- `F_m(V + t ι_i H) = F_m(V) + t dF_m + t² qF_m`. -/
private lemma LiftDataDeriv_liftF_pert {W : ℕ} (g z t : ℝ)
    (V R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) (i : Fin 1000) (H : Matrix (Fin W) (Fin W) ℂ)
    (m : ℕ) :
    liftF g z (V + Pi.single i ((t : ℂ) • H)) R m = liftF g z V R m +
      t • LiftDataDeriv_dF (liftSeq (liftC g z V)) (liftSeq (Pi.single i ((-g⁻¹) • H)))
        (liftSeq R) m +
      (t * t) • LiftDataDeriv_qF (liftSeq (Pi.single i ((-g⁻¹) • H))) (liftSeq R) m := by
  unfold liftF liftE LiftDataDeriv_dF LiftDataDeriv_qF
  rw [LiftDataDeriv_liftC_pert, LiftDataDeriv_liftEAux_lin]
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial]
  module

private lemma LiftDataDeriv_deriv {W : ℕ} (A B Q : Matrix (Fin W) (Fin W) ℂ) :
    deriv (fun t : ℝ => A + t • B + (t * t) • Q) 0 = B := by
  have h := ((hasDerivAt_const (0 : ℝ) A).add ((hasDerivAt_id (0 : ℝ)).smul_const B)).add
    (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).smul_const Q)
  have h' : HasDerivAt (fun t : ℝ => A + t • B + (t * t) • Q) B 0 := by
    convert h using 1
    · funext t; simp
    · simp
  exact h'.deriv

private lemma LiftDataDeriv_liftSeq_single {W : ℕ} (i : Fin 1000) (X : Matrix (Fin W) (Fin W) ℂ)
    (l : ℕ) : liftSeq (Pi.single i X) l = if l = (i : ℕ) then X else 0 := by
  unfold liftSeq
  split_ifs with h1 h2 h2
  · subst h2; simp
  · rw [Pi.single_apply, ite_eq_right]
    intro h; exact h2 (by rw [← h])
  · omega
  · rfl

/-- The count `[i = k] + [i = m]` of the index pairs that carry a derivative of `F_m`. -/
private def LiftDataDeriv_ind (i k m : ℕ) : ℝ := (if i = k then 1 else 0) + (if i = m then 1 else 0)

private lemma LiftDataDeriv_ind_nonneg (i k m : ℕ) : 0 ≤ LiftDataDeriv_ind i k m := by
  unfold LiftDataDeriv_ind; split_ifs <;> norm_num

private lemma LiftDataDeriv_le_ind {i k m : ℕ} (h : i = k ∨ i = m) {K₀ K : ℝ} (hK₀ : 0 ≤ K₀)
    (hK : K = K₀) : K ≤ LiftDataDeriv_ind i k m * K₀ := by
  have : 1 ≤ LiftDataDeriv_ind i k m := by
    unfold LiftDataDeriv_ind; rcases h with h | h <;> split_ifs <;> simp_all
  rw [hK]; nlinarith

private lemma LiftDataDeriv_sum_ind (m : Fin 1000) :
    ∑ i : Fin 1000, ∑ k : Fin 1000, LiftDataDeriv_ind i k m = 2000 := by
  simp [LiftDataDeriv_ind, Finset.sum_add_distrib, Fin.val_inj, Finset.sum_ite_eq,
    Finset.sum_ite_eq']
  norm_num

/-- The derivative bound for one `F_m`: over the directions `(H_α, H_β)` of the data
`D = ι_i (r H_α)` and `R = ι_k H_β`, `Σ ⟨Z, dF_m⟩² ≤ 94 ([i = k] + [i = m]) r² W κ ‖Z‖²`. -/
private lemma LiftDataDeriv_Good_dF {W : ℕ} (c : ℕ → Matrix (Fin W) (Fin W) ℂ) (κ r : ℝ)
    (hκ : 0 ≤ κ)
    (hc : ∀ l Z, hsSq ((c l)ᴴ * Z) ≤ κ * hsSq Z ∧ hsSq (Z * (c l)ᴴ) ≤ κ * hsSq Z)
    (i k : Fin 1000) (m : ℕ) (hm : m < 1000) :
    LiftDataDeriv_Good (fun p : (Fin W × Fin W) × (Fin W × Fin W) =>
      LiftDataDeriv_dF c (liftSeq (Pi.single i (r • hermBasis W p.1)))
        (liftSeq (Pi.single k (hermBasis W p.2))) m)
      (94 * (LiftDataDeriv_ind i k m * (r ^ 2 * W * κ))) := by
  have hK₀ : 0 ≤ r ^ 2 * W * κ := by positivity
  have hE : ∀ (X : ℕ → Matrix (Fin W) (Fin W) ℂ) (b : Fin W × Fin W),
      liftEAux X (liftSeq (Pi.single k (hermBasis W b))) (1000 - 1) (1000 - 1 - m) =
        if m < (k : ℕ) then LiftDataDeriv_alt ((k : ℕ) - m) (hermBasis W b * X k) else 0 := by
    intro X b
    rw [LiftDataDeriv_liftEAux_single X _ (1000 - 1) k (hermBasis W b)
      (LiftDataDeriv_liftSeq_single k _) _ (by omega),
      show 1000 - 1 - (1000 - 1 - m) = m by omega]
    have hk := k.isLt
    by_cases h : m < (k : ℕ)
    · rw [ite_eq_left ⟨h, by omega⟩, ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h]
  have hcr : ∀ l Z, hsSq (Z * (c l)ᴴ) ≤ κ * hsSq Z := fun l Z => (hc l Z).2
  have hcl : ∀ l Z, hsSq ((c l)ᴴ * Z) ≤ κ * hsSq Z := fun l Z => (hc l Z).1
  have hB := LiftDataDeriv_Good_basis W
  have hI : 0 ≤ LiftDataDeriv_ind i k m * (r ^ 2 * W * κ) :=
    mul_nonneg (LiftDataDeriv_ind_nonneg _ _ _) hK₀
  -- `E_m(D, R) C_m`
  have T1 : LiftDataDeriv_Good (fun p : (Fin W × Fin W) × (Fin W × Fin W) =>
      (if m < (k : ℕ) then LiftDataDeriv_alt ((k : ℕ) - m)
        (hermBasis W p.2 * (if (k : ℕ) = (i : ℕ) then r • hermBasis W p.1 else 0)) else 0) * c m)
      (LiftDataDeriv_ind i k m * (r ^ 2 * W * κ)) := by
    by_cases h : m < (k : ℕ) ∧ (k : ℕ) = (i : ℕ)
    · refine LiftDataDeriv_Good_mono (LiftDataDeriv_Good_congr
        (LiftDataDeriv_Good_mul_right (c m) (by positivity) (hcr m)
          (LiftDataDeriv_Good_alt ((k : ℕ) - m)
            (LiftDataDeriv_Good_smul r (LiftDataDeriv_Good_herm_right hB)))) fun p => ?_) ?_
      · rw [ite_eq_left h.2, ite_eq_left h.1, Matrix.mul_smul]
      · exact LiftDataDeriv_le_ind (Or.inl h.2.symm) hK₀ (by ring)
    · refine LiftDataDeriv_Good_mono (LiftDataDeriv_Good_congr LiftDataDeriv_Good_zero
        fun p => ?_) hI
      by_cases h1 : m < (k : ℕ)
      · have h2 : ¬ (k : ℕ) = i := fun h2 => h ⟨h1, h2⟩
        rw [ite_eq_left h1, ite_eq_right h2, Matrix.mul_zero, LiftDataDeriv_alt_zero,
          Matrix.zero_mul]
      · rw [ite_eq_right h1, Matrix.zero_mul]
  -- `E_m(C, R) D_m`
  have T2 : LiftDataDeriv_Good (fun p : (Fin W × Fin W) × (Fin W × Fin W) =>
      (if m < (k : ℕ) then LiftDataDeriv_alt ((k : ℕ) - m) (hermBasis W p.2 * c k) else 0) *
        (if m = (i : ℕ) then r • hermBasis W p.1 else 0))
      (LiftDataDeriv_ind i k m * (r ^ 2 * W * κ)) := by
    by_cases h : m < (k : ℕ) ∧ m = (i : ℕ)
    · refine LiftDataDeriv_Good_mono (LiftDataDeriv_Good_congr
        (LiftDataDeriv_Good_smul r (LiftDataDeriv_Good_herm_right
          (LiftDataDeriv_Good_alt ((k : ℕ) - m)
            (LiftDataDeriv_Good_mul_right (c k) zero_le_one (hcr k) hB)))) fun p => ?_) ?_
      · rw [ite_eq_left h.1, ite_eq_left h.2, Matrix.mul_smul]
      · exact LiftDataDeriv_le_ind (Or.inr h.2.symm) hK₀ (by ring)
    · refine LiftDataDeriv_Good_mono (LiftDataDeriv_Good_congr LiftDataDeriv_Good_zero
        fun p => ?_) hI
      by_cases h1 : m < (k : ℕ)
      · have h2 : ¬ m = i := fun h2 => h ⟨h1, h2⟩
        rw [ite_eq_right h2, Matrix.mul_zero]
      · rw [ite_eq_right h1, Matrix.zero_mul]
  -- `D_m E_m(C, R)*`
  have T3 : LiftDataDeriv_Good (fun p : (Fin W × Fin W) × (Fin W × Fin W) =>
      (if m = (i : ℕ) then r • hermBasis W p.1 else 0) *
        (if m < (k : ℕ) then LiftDataDeriv_alt ((k : ℕ) - m) (hermBasis W p.2 * c k) else 0)ᴴ)
      (LiftDataDeriv_ind i k m * (r ^ 2 * W * κ)) := by
    by_cases h : m < (k : ℕ) ∧ m = (i : ℕ)
    · refine LiftDataDeriv_Good_mono (LiftDataDeriv_Good_congr
        (LiftDataDeriv_Good_smul r (LiftDataDeriv_Good_herm_left (LiftDataDeriv_Good_conj
          (LiftDataDeriv_Good_alt ((k : ℕ) - m)
            (LiftDataDeriv_Good_mul_right (c k) zero_le_one (hcr k) hB))))) fun p => ?_) ?_
      · rw [ite_eq_left h.1, ite_eq_left h.2, Matrix.smul_mul]
      · exact LiftDataDeriv_le_ind (Or.inr h.2.symm) hK₀ (by ring)
    · refine LiftDataDeriv_Good_mono (LiftDataDeriv_Good_congr LiftDataDeriv_Good_zero
        fun p => ?_) hI
      by_cases h1 : m < (k : ℕ)
      · have h2 : ¬ m = i := fun h2 => h ⟨h1, h2⟩
        rw [ite_eq_right h2, Matrix.zero_mul]
      · rw [ite_eq_right h1, Matrix.conjTranspose_zero, Matrix.mul_zero]
  -- `C_m E_m(D, R)*`
  have T4 : LiftDataDeriv_Good (fun p : (Fin W × Fin W) × (Fin W × Fin W) =>
      c m * (if m < (k : ℕ) then LiftDataDeriv_alt ((k : ℕ) - m)
        (hermBasis W p.2 * (if (k : ℕ) = (i : ℕ) then r • hermBasis W p.1 else 0)) else 0)ᴴ)
      (LiftDataDeriv_ind i k m * (r ^ 2 * W * κ)) := by
    by_cases h : m < (k : ℕ) ∧ (k : ℕ) = (i : ℕ)
    · refine LiftDataDeriv_Good_mono (LiftDataDeriv_Good_congr
        (LiftDataDeriv_Good_mul_left (c m) (by positivity) (hcl m)
          (LiftDataDeriv_Good_conj (LiftDataDeriv_Good_alt ((k : ℕ) - m)
            (LiftDataDeriv_Good_smul r (LiftDataDeriv_Good_herm_right hB))))) fun p => ?_) ?_
      · rw [ite_eq_left h.2, ite_eq_left h.1, Matrix.mul_smul]
      · exact LiftDataDeriv_le_ind (Or.inl h.2.symm) hK₀ (by ring)
    · refine LiftDataDeriv_Good_mono (LiftDataDeriv_Good_congr LiftDataDeriv_Good_zero
        fun p => ?_) hI
      by_cases h1 : m < (k : ℕ)
      · have h2 : ¬ (k : ℕ) = i := fun h2 => h ⟨h1, h2⟩
        rw [ite_eq_left h1, ite_eq_right h2, Matrix.mul_zero, LiftDataDeriv_alt_zero,
          Matrix.conjTranspose_zero, Matrix.mul_zero]
      · rw [ite_eq_right h1, Matrix.conjTranspose_zero, Matrix.mul_zero]
  -- `D_m R_m C_m`
  have T5 : LiftDataDeriv_Good (fun p : (Fin W × Fin W) × (Fin W × Fin W) =>
      (if m = (i : ℕ) then r • hermBasis W p.1 else 0) *
        (if m = (k : ℕ) then hermBasis W p.2 else 0) * c m)
      (LiftDataDeriv_ind i k m * (r ^ 2 * W * κ)) := by
    by_cases h : m = (i : ℕ) ∧ m = (k : ℕ)
    · refine LiftDataDeriv_Good_mono (LiftDataDeriv_Good_congr
        (LiftDataDeriv_Good_smul r (LiftDataDeriv_Good_herm_left
          (LiftDataDeriv_Good_mul_right (c m) zero_le_one (hcr m) hB))) fun p => ?_) ?_
      · rw [ite_eq_left h.1, ite_eq_left h.2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc]
      · exact LiftDataDeriv_le_ind (Or.inr h.1.symm) hK₀ (by ring)
    · refine LiftDataDeriv_Good_mono (LiftDataDeriv_Good_congr LiftDataDeriv_Good_zero
        fun p => ?_) hI
      by_cases h1 : m = (i : ℕ)
      · have h2 : ¬ m = k := fun h2 => h ⟨h1, h2⟩
        rw [ite_eq_right h2, Matrix.mul_zero, Matrix.zero_mul]
      · rw [ite_eq_right h1, Matrix.zero_mul, Matrix.zero_mul]
  -- `C_m R_m D_m`
  have T6 : LiftDataDeriv_Good (fun p : (Fin W × Fin W) × (Fin W × Fin W) =>
      c m * (if m = (k : ℕ) then hermBasis W p.2 else 0) *
        (if m = (i : ℕ) then r • hermBasis W p.1 else 0))
      (LiftDataDeriv_ind i k m * (r ^ 2 * W * κ)) := by
    by_cases h : m = (i : ℕ) ∧ m = (k : ℕ)
    · refine LiftDataDeriv_Good_mono (LiftDataDeriv_Good_congr
        (LiftDataDeriv_Good_smul r (LiftDataDeriv_Good_herm_right
          (LiftDataDeriv_Good_mul_left (c m) zero_le_one (hcl m) hB))) fun p => ?_) ?_
      · rw [ite_eq_left h.1, ite_eq_left h.2, Matrix.mul_smul]
      · exact LiftDataDeriv_le_ind (Or.inr h.1.symm) hK₀ (by ring)
    · refine LiftDataDeriv_Good_mono (LiftDataDeriv_Good_congr LiftDataDeriv_Good_zero
        fun p => ?_) hI
      by_cases h1 : m = (i : ℕ)
      · have h2 : ¬ m = k := fun h2 => h ⟨h1, h2⟩
        rw [ite_eq_right h2, Matrix.mul_zero, Matrix.zero_mul]
      · rw [ite_eq_right h1, Matrix.mul_zero]
  have hsum := LiftDataDeriv_Good_add (LiftDataDeriv_Good_add (LiftDataDeriv_Good_add
    (LiftDataDeriv_Good_add (LiftDataDeriv_Good_add T1 T2) T3) T4) T5) T6
  refine LiftDataDeriv_Good_mono (LiftDataDeriv_Good_congr hsum fun p => ?_) (le_of_eq (by ring))
  simp only [LiftDataDeriv_dF, hE, LiftDataDeriv_liftSeq_single]

/-- The derivative of the data map along `V ↦ V + t ι_i H` at the data `R = ι_k H'`:
`dF_{i_j} - dF_{k_j}`. -/
private lemma LiftDataDeriv_deriv_pairData {W : ℕ} (g z : ℝ)
    (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) (i k : Fin 1000) (H H' : Matrix (Fin W) (Fin W) ℂ)
    (j : Fin 128) :
    deriv (fun t : ℝ => pairData g z (V + Pi.single i ((t : ℂ) • H)) (Pi.single k H') j) 0 =
      LiftDataDeriv_dF (liftSeq (liftC g z V)) (liftSeq (Pi.single i ((-g⁻¹) • H)))
          (liftSeq (Pi.single k H')) (liftPairI j) +
        -LiftDataDeriv_dF (liftSeq (liftC g z V)) (liftSeq (Pi.single i ((-g⁻¹) • H)))
          (liftSeq (Pi.single k H')) (liftPairK j) := by
  have e : (fun t : ℝ => pairData g z (V + Pi.single i ((t : ℂ) • H)) (Pi.single k H') j) =
      fun t : ℝ => (liftF g z V (Pi.single k H') (liftPairI j) -
          liftF g z V (Pi.single k H') (liftPairK j)) +
        t • (LiftDataDeriv_dF (liftSeq (liftC g z V)) (liftSeq (Pi.single i ((-g⁻¹) • H)))
            (liftSeq (Pi.single k H')) (liftPairI j) +
          -LiftDataDeriv_dF (liftSeq (liftC g z V)) (liftSeq (Pi.single i ((-g⁻¹) • H)))
            (liftSeq (Pi.single k H')) (liftPairK j)) +
        (t * t) • (LiftDataDeriv_qF (liftSeq (Pi.single i ((-g⁻¹) • H)))
            (liftSeq (Pi.single k H')) (liftPairI j) -
          LiftDataDeriv_qF (liftSeq (Pi.single i ((-g⁻¹) • H)))
            (liftSeq (Pi.single k H')) (liftPairK j)) := by
    funext t
    simp only [pairData, LiftDataDeriv_liftF_pert]
    module
  rw [e, LiftDataDeriv_deriv]

/-- `‖C_l* Z‖² ≤ κ ‖Z‖²` and `‖Z C_l*‖² ≤ κ ‖Z‖²` with `κ = 2 z² + 2 g⁻² K₁²` on
`max_i ‖V_i‖ ≤ K₁`. -/
private lemma LiftDataDeriv_hc {W : ℕ} {g z K₁ : ℝ} {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, ‖V i‖ ≤ K₁) (l : ℕ) (Z : Matrix (Fin W) (Fin W) ℂ) :
    hsSq ((liftSeq (liftC g z V) l)ᴴ * Z) ≤ (2 * z ^ 2 + 2 * g⁻¹ ^ 2 * K₁ ^ 2) * hsSq Z ∧
      hsSq (Z * (liftSeq (liftC g z V) l)ᴴ) ≤ (2 * z ^ 2 + 2 * g⁻¹ ^ 2 * K₁ ^ 2) * hsSq Z := by
  have hZ := LiftDataDeriv_hsSq_nonneg Z
  have hκ : 0 ≤ 2 * z ^ 2 + 2 * g⁻¹ ^ 2 * K₁ ^ 2 := by positivity
  unfold liftSeq
  split_ifs with hl
  · have hA : ‖(V ⟨l, hl⟩)ᴴ‖ ^ 2 ≤ K₁ ^ 2 := by
      rw [Matrix.l2_opNorm_conjTranspose]
      exact pow_le_pow_left₀ (norm_nonneg _) (hV _) 2
    have hc : (liftC g z V ⟨l, hl⟩)ᴴ = ((z : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) +
        ((-g⁻¹ : ℝ) : ℂ) • (V ⟨l, hl⟩)ᴴ := by
      simp [liftC, Matrix.conjTranspose_smul, sub_eq_add_neg]
    have hz : ‖((z : ℝ) : ℂ)‖ ^ 2 = z ^ 2 := by simp [sq_abs]
    have hg : ‖((-g⁻¹ : ℝ) : ℂ)‖ ^ 2 = g⁻¹ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, neg_sq]
    constructor
    · rw [hc, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
      calc _ ≤ 2 * hsSq (((z : ℝ) : ℂ) • Z) + 2 * hsSq (((-g⁻¹ : ℝ) : ℂ) • ((V ⟨l, hl⟩)ᴴ * Z)) :=
            LiftDataDeriv_hsSq_add_le _ _
        _ = 2 * z ^ 2 * hsSq Z + 2 * g⁻¹ ^ 2 * hsSq ((V ⟨l, hl⟩)ᴴ * Z) := by
            rw [LiftDataDeriv_hsSq_smul, LiftDataDeriv_hsSq_smul, hz, hg]; ring
        _ ≤ 2 * z ^ 2 * hsSq Z + 2 * g⁻¹ ^ 2 * (K₁ ^ 2 * hsSq Z) := by
            gcongr
            exact (LiftDataDeriv_hsSq_mul_left _ _).trans (mul_le_mul_of_nonneg_right hA hZ)
        _ = _ := by ring
    · rw [hc, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
      calc _ ≤ 2 * hsSq (((z : ℝ) : ℂ) • Z) + 2 * hsSq (((-g⁻¹ : ℝ) : ℂ) • (Z * (V ⟨l, hl⟩)ᴴ)) :=
            LiftDataDeriv_hsSq_add_le _ _
        _ = 2 * z ^ 2 * hsSq Z + 2 * g⁻¹ ^ 2 * hsSq (Z * (V ⟨l, hl⟩)ᴴ) := by
            rw [LiftDataDeriv_hsSq_smul, LiftDataDeriv_hsSq_smul, hz, hg]; ring
        _ ≤ 2 * z ^ 2 * hsSq Z + 2 * g⁻¹ ^ 2 * (K₁ ^ 2 * hsSq Z) := by
            gcongr
            exact (LiftDataDeriv_hsSq_mul_right _ _).trans (mul_le_mul_of_nonneg_right hA hZ)
        _ = _ := by ring
  · have h0 : hsSq (0 : Matrix (Fin W) (Fin W) ℂ) = 0 := by simp [hsSq]
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, h0]
    exact ⟨mul_nonneg hκ hZ, mul_nonneg hκ hZ⟩

/-- `Σ_a Σ_b Σ_j f = Σ_j Σ_{(a, b)} f`. -/
private lemma LiftDataDeriv_sum_reorder {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    ∑ a, ∑ b, ∑ j, f a b j = ∑ j, ∑ p : α × β, f p.1 p.2 j := by
  calc ∑ a, ∑ b, ∑ j, f a b j = ∑ a, ∑ j, ∑ b, f a b j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ b, f a b j := Finset.sum_comm
    _ = ∑ j, ∑ p : α × β, f p.1 p.2 j := by simp only [Fintype.sum_prod_type]

end LiftDataDerivAux

/-- (10.20) [eq:c-F-bounds]: on `max_i ‖V_i‖ ≤ K₁`, `|E| ≤ E₀`,
`Σ_{i,α} ‖(D_{i,α} 𝓕)* Z‖² ≤ C W max{g⁻², g⁻⁴} ‖Z‖²`, with `‖A* Z‖² = Σ_{k,β} ⟨Z, A(ι_k H_β)⟩²`
in the basis of Hermitian arrays. -/
theorem sum_deriv_pairData_le (E₀ K₁ : ℝ) (hE₀ : 0 < E₀) (hK₁ : 0 < K₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ) (g E : ℝ) (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
      (Z : Fin 128 → Matrix (Fin W) (Fin W) ℂ), 0 < g → |E| ≤ E₀ → (∀ i, ‖V i‖ ≤ K₁) →
        ∑ i : Fin 1000, ∑ a : Fin W × Fin W, ∑ k : Fin 1000, ∑ b : Fin W × Fin W,
          (∑ j, hsInner (Z j) (deriv (fun t : ℝ => pairData g (max 1 g * E / g)
            (V + Pi.single i ((t : ℂ) • hermBasis W a)) (Pi.single k (hermBasis W b)) j) 0)) ^ 2 ≤
          C * W * max (g⁻¹ ^ 2) (g⁻¹ ^ 4) * ∑ j, hsSq (Z j) := by
  refine ⟨128 * (2 * 94) * 4000 * (2 * (E₀ ^ 2 + K₁ ^ 2)), by positivity, ?_⟩
  intro W g E V Z hg hE hV
  set z := max 1 g * E / g with hz
  set κ := 2 * z ^ 2 + 2 * g⁻¹ ^ 2 * K₁ ^ 2 with hκdef
  have hκ : 0 ≤ κ := by positivity
  set K₀ := (-g⁻¹) ^ 2 * (W : ℝ) * κ with hK₀def
  have hc := fun l Z => LiftDataDeriv_hc (g := g) (z := z) hV l Z
  set D := fun (i : Fin 1000) (a : Fin W × Fin W) (k : Fin 1000) (b : Fin W × Fin W)
      (j : Fin 128) =>
    deriv (fun t : ℝ => pairData g z (V + Pi.single i ((t : ℂ) • hermBasis W a))
      (Pi.single k (hermBasis W b)) j) 0 with hDdef
  have hD : ∀ (i k : Fin 1000) (j : Fin 128),
      LiftDataDeriv_Good (fun p : (Fin W × Fin W) × (Fin W × Fin W) => D i p.1 k p.2 j)
        (2 * (94 * (LiftDataDeriv_ind i k (liftPairI j) * K₀)) +
          2 * (94 * (LiftDataDeriv_ind i k (liftPairK j) * K₀))) := by
    intro i k j
    refine LiftDataDeriv_Good_congr (LiftDataDeriv_Good_add
      (LiftDataDeriv_Good_dF _ κ (-g⁻¹) hκ hc i k (liftPairI j) (liftPairI j).isLt)
      (LiftDataDeriv_Good_neg
        (LiftDataDeriv_Good_dF _ κ (-g⁻¹) hκ hc i k (liftPairK j) (liftPairK j).isLt)))
      fun p => ?_
    exact LiftDataDeriv_deriv_pairData g z V i k _ _ j
  have hmax : g⁻¹ ^ 2 * κ ≤ 2 * (E₀ ^ 2 + K₁ ^ 2) * max (g⁻¹ ^ 2) (g⁻¹ ^ 4) := by
    have hE2 : E ^ 2 ≤ E₀ ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg E) hE 2
      rwa [sq_abs] at this
    have hm2 := le_max_left (g⁻¹ ^ 2) (g⁻¹ ^ 4)
    have hm4 := le_max_right (g⁻¹ ^ 2) (g⁻¹ ^ 4)
    have hzb : g⁻¹ ^ 2 * z ^ 2 ≤ E₀ ^ 2 * max (g⁻¹ ^ 2) (g⁻¹ ^ 4) := by
      rcases le_total g 1 with h1 | h1
      · have ez : z = E * g⁻¹ := by rw [hz, max_eq_left h1, one_mul, div_eq_mul_inv]
        rw [ez]
        have : g⁻¹ ^ 2 * (E * g⁻¹) ^ 2 = E ^ 2 * g⁻¹ ^ 4 := by ring
        rw [this]
        exact mul_le_mul hE2 hm4 (by positivity) (by positivity)
      · have ez : z = E := by rw [hz, max_eq_right h1]; field_simp
        rw [ez, mul_comm]
        exact mul_le_mul hE2 hm2 (by positivity) (by positivity)
    have hkb : g⁻¹ ^ 2 * (g⁻¹ ^ 2 * K₁ ^ 2) ≤ K₁ ^ 2 * max (g⁻¹ ^ 2) (g⁻¹ ^ 4) := by
      have : g⁻¹ ^ 2 * (g⁻¹ ^ 2 * K₁ ^ 2) = K₁ ^ 2 * g⁻¹ ^ 4 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hm4 (by positivity)
    rw [hκdef]
    nlinarith
  have hS := fun j => LiftDataDeriv_hsSq_nonneg (Z j)
  calc ∑ i, ∑ a, ∑ k, ∑ b, (∑ j, hsInner (Z j) (D i a k b j)) ^ 2
      = ∑ i, ∑ k, ∑ a, ∑ b, (∑ j, hsInner (Z j) (D i a k b j)) ^ 2 :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ ≤ ∑ i, ∑ k, ∑ a, ∑ b, 128 * ∑ j, hsInner (Z j) (D i a k b j) ^ 2 := by
        gcongr with i _ k _ a _ b _
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun j => hsInner (Z j) (D i a k b j))
    _ = 128 * ∑ i, ∑ k, ∑ j, ∑ p : (Fin W × Fin W) × (Fin W × Fin W),
          hsInner (Z j) (D i p.1 k p.2 j) ^ 2 := by
        simp only [← Finset.mul_sum]
        refine congrArg (fun x => 128 * x) ?_
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        exact LiftDataDeriv_sum_reorder (fun a b j => hsInner (Z j) (D i a k b j) ^ 2)
    _ ≤ 128 * ∑ i : Fin 1000, ∑ k : Fin 1000, ∑ j : Fin 128,
          (2 * (94 * (LiftDataDeriv_ind i k (liftPairI j) * K₀)) +
          2 * (94 * (LiftDataDeriv_ind i k (liftPairK j) * K₀))) * hsSq (Z j) := by
        gcongr with i _ k _ j _
        exact hD i k j (Z j)
    _ = 128 * ∑ j : Fin 128, (188 * K₀ * 4000) * hsSq (Z j) := by
        refine congrArg (fun x => 128 * x) ?_
        rw [LiftDataDeriv_sum_reorder]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_mul, Fintype.sum_prod_type]
        refine congrArg (fun x => x * hsSq (Z j)) ?_
        have e : ∀ i k : Fin 1000, 2 * (94 * (LiftDataDeriv_ind i k (liftPairI j) * K₀)) +
            2 * (94 * (LiftDataDeriv_ind i k (liftPairK j) * K₀)) =
            188 * K₀ * (LiftDataDeriv_ind i k (liftPairI j) +
              LiftDataDeriv_ind i k (liftPairK j)) := fun i k => by ring
        simp only [e, ← Finset.mul_sum, Finset.sum_add_distrib, LiftDataDeriv_sum_ind]
        norm_num
    _ ≤ 128 * (2 * 94) * 4000 * (2 * (E₀ ^ 2 + K₁ ^ 2)) * W * max (g⁻¹ ^ 2) (g⁻¹ ^ 4) *
          ∑ j, hsSq (Z j) := by
        rw [← Finset.mul_sum, ← mul_assoc]
        have hK : K₀ ≤ W * (2 * (E₀ ^ 2 + K₁ ^ 2) * max (g⁻¹ ^ 2) (g⁻¹ ^ 4)) := by
          rw [hK₀def, neg_sq, mul_comm _ (W : ℝ), mul_assoc]
          exact mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg W)
        have hZs : 0 ≤ ∑ j, hsSq (Z j) := Finset.sum_nonneg fun j _ => hS j
        nlinarith [mul_le_mul_of_nonneg_right hK hZs]

section LiftDataDerivAux2

/-- `d dᵀ = I` for the layout of the disjoint pairs. -/
private lemma LiftDataDeriv_layout_orth : liftLayout * liftLayoutᵀ = 1 :=
  pairLayout_mul_transpose (fun a b h => by simp [liftPairI, Fin.ext_iff] at h; omega)
    (fun a b h => by simp [liftPairK, Fin.ext_iff] at h; omega)
    (fun a b h => by simp [liftPairI, liftPairK, Fin.ext_iff] at h; omega)

/-- `G(ι_i H)_j = d_{ji} H`. -/
private lemma LiftDataDeriv_layout_single {W : ℕ} (i : Fin 1000) (H : Matrix (Fin W) (Fin W) ℂ)
    (j : Fin 128) : layoutBlocks liftLayout (Pi.single i H) j = ((liftLayout j i : ℝ) : ℂ) • H := by
  simp only [layoutBlocks]
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hl; simp [hl]
  · simp

/-- `Σ_i d_{ji}² = 1`. -/
private lemma LiftDataDeriv_row_sq (j : Fin 128) : ∑ i, liftLayout j i ^ 2 = 1 := by
  have h := congrFun (congrFun LiftDataDeriv_layout_orth j) j
  simpa [Matrix.mul_apply, sq] using h

/-- `Σ_i (Σ_j d_{ji} u_j)² = Σ_j u_j²` for `d dᵀ = I`. -/
private lemma LiftDataDeriv_orth_real (u : Fin 128 → ℝ) :
    ∑ i, (∑ j, liftLayout j i * u j) ^ 2 = ∑ j, u j ^ 2 := by
  have h1 : ∀ i, (∑ j, liftLayout j i * u j) ^ 2 =
      ∑ j, ∑ j', liftLayout j i * u j * (liftLayout j' i * u j') := fun i => by
    rw [sq, Finset.sum_mul_sum]
  have h2 : ∀ j j', ∑ i, liftLayout j i * u j * (liftLayout j' i * u j') =
      u j * u j' * (if j = j' then 1 else 0) := fun j j' => by
    have h := congrFun (congrFun LiftDataDeriv_layout_orth j) j'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    rw [← h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [fun j => (Finset.sum_comm : ∑ i : Fin 1000, ∑ j' : Fin 128,
    liftLayout j i * u j * (liftLayout j' i * u j') = _), h2]
  simp [sq]

/-- `Σ_i ‖Σ_j d_{ji} Y_j‖² = Σ_j ‖Y_j‖²` for `d dᵀ = I`. -/
private lemma LiftDataDeriv_orth {W : ℕ} (Y : Fin 128 → Matrix (Fin W) (Fin W) ℂ) :
    ∑ i : Fin 1000, hsSq (∑ j, ((liftLayout j i : ℝ) : ℂ) • Y j) = ∑ j, hsSq (Y j) := by
  have e : ∀ (M : Matrix (Fin W) (Fin W) ℂ), hsSq M =
      ∑ a, ∑ b, ((M a b).re ^ 2 + (M a b).im ^ 2) := fun M => by
    unfold hsSq
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [e, Matrix.sum_apply, Matrix.smul_apply, Complex.re_sum, Complex.im_sum,
    smul_eq_mul, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  have L : ∀ a b, ∑ i : Fin 1000, ((∑ j, liftLayout j i * (Y j a b).re) ^ 2 +
      (∑ j, liftLayout j i * (Y j a b).im) ^ 2) = ∑ j, ((Y j a b).re ^ 2 + (Y j a b).im ^ 2) := by
    intro a b
    rw [Finset.sum_add_distrib, LiftDataDeriv_orth_real, LiftDataDeriv_orth_real,
      ← Finset.sum_add_distrib]
  calc _ = ∑ a, ∑ b, ∑ i : Fin 1000, ((∑ j, liftLayout j i * (Y j a b).re) ^ 2 +
        (∑ j, liftLayout j i * (Y j a b).im) ^ 2) := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ j, ((Y j a b).re ^ 2 + (Y j a b).im ^ 2) := by simp only [L]
    _ = ∑ j, ∑ a, ∑ b, ((Y j a b).re ^ 2 + (Y j a b).im ^ 2) := by
        rw [Finset.sum_comm (s := Finset.univ (α := Fin 128))]
        exact (Finset.sum_congr rfl fun a _ => Finset.sum_comm).symm

end LiftDataDerivAux2

/-- (10.21) [eq:c-L-bounds]: `Σ_{i,α} ‖𝓛_{G(ι_i H_α)} P‖² ≤ 512 W ‖P‖²` and
`Σ_{i,α} ‖Σ_j G(ι_i H_α)_j (Z_j + Z_j*)‖² ≤ 4 W ‖Z‖²` for `G = liftLayout`. -/
theorem sum_hsSq_cohMap_deriv_le {W : ℕ} (P : Matrix (Fin W) (Fin W) ℂ)
    (Z : Fin 128 → Matrix (Fin W) (Fin W) ℂ) :
    ∑ i : Fin 1000, ∑ a : Fin W × Fin W, ∑ j,
        hsSq (cohMap (layoutBlocks liftLayout (Pi.single i (hermBasis W a))) P j) ≤
      512 * W * hsSq P ∧
    ∑ i : Fin 1000, ∑ a : Fin W × Fin W,
        hsSq (∑ j, layoutBlocks liftLayout (Pi.single i (hermBasis W a)) j * (Z j + (Z j)ᴴ)) ≤
      4 * W * ∑ j, hsSq (Z j) := by
  have hL : ∀ X : Matrix (Fin W) (Fin W) ℂ, ∑ a, hsSq (hermBasis W a * X) = W * hsSq X := by
    intro X
    have h := (hermBasis_completeness W 1 X).2
    simpa only [Matrix.one_mul, LiftDataDeriv_hsSq_one] using h
  have hR : ∀ X : Matrix (Fin W) (Fin W) ℂ, ∑ a, hsSq (X * hermBasis W a) = W * hsSq X := by
    intro X
    have h := (hermBasis_completeness W X 1).2
    rw [LiftDataDeriv_hsSq_one, mul_comm] at h
    simpa only [Matrix.mul_one] using h
  have hd : ∀ x : ℝ, ‖((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  refine ⟨?_, ?_⟩
  · have e1 : ∀ (i : Fin 1000) (a : Fin W × Fin W) (j : Fin 128),
        hsSq (cohMap (layoutBlocks liftLayout (Pi.single i (hermBasis W a))) P j) =
          liftLayout j i ^ 2 * hsSq (hermBasis W a * P + Pᴴ * hermBasis W a) := by
      intro i a j
      rw [cohMap, LiftDataDeriv_layout_single, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
        LiftDataDeriv_hsSq_smul, hd]
    calc ∑ i : Fin 1000, ∑ a : Fin W × Fin W, ∑ j,
          hsSq (cohMap (layoutBlocks liftLayout (Pi.single i (hermBasis W a))) P j)
        = ∑ a : Fin W × Fin W, ∑ j : Fin 128, (∑ i : Fin 1000, liftLayout j i ^ 2) *
            hsSq (hermBasis W a * P + Pᴴ * hermBasis W a) := by
          simp only [e1]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
      _ = ∑ a : Fin W × Fin W, 128 * hsSq (hermBasis W a * P + Pᴴ * hermBasis W a) := by
          simp [LiftDataDeriv_row_sq]
      _ ≤ ∑ a : Fin W × Fin W,
            128 * (2 * hsSq (hermBasis W a * P) + 2 * hsSq (Pᴴ * hermBasis W a)) := by
          gcongr with a _
          exact LiftDataDeriv_hsSq_add_le _ _
      _ = 512 * W * hsSq P := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, hL, hR,
            LiftDataDeriv_hsSq_conj]
          ring
  · have e2 : ∀ (i : Fin 1000) (a : Fin W × Fin W),
        ∑ j, layoutBlocks liftLayout (Pi.single i (hermBasis W a)) j * (Z j + (Z j)ᴴ) =
          hermBasis W a * ∑ j, ((liftLayout j i : ℝ) : ℂ) • (Z j + (Z j)ᴴ) := by
      intro i a
      simp only [LiftDataDeriv_layout_single, Matrix.smul_mul, Finset.mul_sum, Matrix.mul_smul]
    have hZ : ∀ j, hsSq (Z j + (Z j)ᴴ) ≤ 4 * hsSq (Z j) := fun j => by
      have h := LiftDataDeriv_hsSq_add_le (Z j) (Z j)ᴴ
      rw [LiftDataDeriv_hsSq_conj] at h
      linarith
    calc ∑ i : Fin 1000, ∑ a : Fin W × Fin W,
          hsSq (∑ j, layoutBlocks liftLayout (Pi.single i (hermBasis W a)) j * (Z j + (Z j)ᴴ))
        = W * ∑ j, hsSq (Z j + (Z j)ᴴ) := by
          simp only [e2, hL, ← Finset.mul_sum, LiftDataDeriv_orth]
      _ ≤ W * ∑ j, 4 * hsSq (Z j) := by
          gcongr with j _
          exact hZ j
      _ = 4 * W * ∑ j, hsSq (Z j) := by
          rw [← Finset.mul_sum]; ring

end LSBA
