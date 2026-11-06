import LSBA.Gauss.GUE
import LSBA.Upper.CoercivityMap

/-!
# Skew-Hermitian frames of a projection

For an orthogonal projection `P`, the matrices `K_k = P (i H_k) P` over the Hermitian basis
`(H_k)` form a tight frame of `𝔨_P = {A : A* = -A, A = P A P}`: sums `Σ_k ‖Λ(K_k)‖²` equal the
sums over a real orthonormal basis of `𝔨_P`. The identity
`Σ_k ‖[K_k, A]‖²_HS = 2 Tr(P) ‖A‖²_HS - 2 |Tr A|²` for `A = P A P`, which gives (9.33)
[su:eq:commutator-basis-bound]; and the covariance bound `Σ_k Re(w* K_k v)² ≤ ‖P v‖² ‖Π_v w‖²`,
where `Π_v` is the real orthogonal projection onto `𝓗_v = {w ∈ ran P : Re(v* w) = 0}` (proof
of Lemma 9.4 [us:lem:score]).
-/

open Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `Tr(M* M) = ‖M‖²_HS`. -/
private lemma SkewBasis_trace_conjTranspose_mul {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) :
    (Mᴴ * M).trace = (hsSq M : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hsSq]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.conj_mul']

/-- Completeness of the Hermitian basis: `Σ_k Tr(X (H_k Y H_k)) = Tr X Tr Y`. -/
private lemma SkewBasis_sum_trace_mul {W : ℕ} (X Y : Matrix (Fin W) (Fin W) ℂ) :
    ∑ k, (X * (hermBasis W k * Y * hermBasis W k)).trace = X.trace * Y.trace := by
  rw [← Matrix.trace_sum, ← Finset.mul_sum, sum_hermBasis_mul_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, smul_eq_mul, mul_comm]

/-- Completeness of the Hermitian basis in bilinear form:
`Σ_k (p ⬝ H_k q)(r ⬝ H_k s) = (p ⬝ s)(r ⬝ q)`. -/
private lemma SkewBasis_sum_bilin {W : ℕ} (p q r s : Fin W → ℂ) :
    ∑ k, (p ⬝ᵥ (hermBasis W k *ᵥ q)) * (r ⬝ᵥ (hermBasis W k *ᵥ s)) = (p ⬝ᵥ s) * (r ⬝ᵥ q) := by
  have e : ∀ (H : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ),
      x ⬝ᵥ (H *ᵥ y) = ∑ i, ∑ j, x i * y j * H i j := by
    intro H x y
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∀ k : Fin W × Fin W, (p ⬝ᵥ (hermBasis W k *ᵥ q)) * (r ⬝ᵥ (hermBasis W k *ᵥ s)) =
      ∑ i, ∑ l, ∑ j, ∑ m, (p i * q j * (r l * s m)) * (hermBasis W k i j * hermBasis W k l m) := by
    intro k
    rw [e, e]
    simp only [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by ring
  simp only [e2]
  have hsw : ∀ (F : Fin W × Fin W → Fin W → Fin W → Fin W → Fin W → ℂ),
      ∑ k, ∑ i, ∑ l, ∑ j, ∑ m, F k i l j m = ∑ i, ∑ l, ∑ j, ∑ m, ∑ k, F k i l j m := by
    intro F
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
  rw [hsw (fun k i l j m => (p i * q j * (r l * s m)) * (hermBasis W k i j * hermBasis W k l m))]
  simp only [← Finset.mul_sum, sum_hermBasis_apply_mul_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_and]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [dotProduct, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `Tr(B* B)` for `B = P H A - A H P`, where `P* = P`, `P² = P`, `H* = H`, `P A = A`, `A P = A`,
as a sum of four terms of the form `Tr(X (H Y H))`. -/
private lemma SkewBasis_trace_comm_sq {W : ℕ} {P A H : Matrix (Fin W) (Fin W) ℂ}
    (hP : Pᴴ = P) (hH : Hᴴ = H) (hPP : P * P = P) (hPA : P * A = A) (hAP : A * P = A) :
    ((P * H * A - A * H * P)ᴴ * (P * H * A - A * H * P)).trace =
      (A * Aᴴ * (H * P * H)).trace - (Aᴴ * (H * A * H)).trace - (A * (H * Aᴴ * H)).trace +
        (P * (H * (Aᴴ * A) * H)).trace := by
  have hPAh : P * Aᴴ = Aᴴ := by
    have := congrArg Matrix.conjTranspose hAP
    rwa [Matrix.conjTranspose_mul, hP] at this
  have hAhP : Aᴴ * P = Aᴴ := by
    have := congrArg Matrix.conjTranspose hPA
    rwa [Matrix.conjTranspose_mul, hP] at this
  have h1 : ∀ X : Matrix (Fin W) (Fin W) ℂ, P * (P * X) = P * X := fun X => by
    rw [← Matrix.mul_assoc, hPP]
  have h2 : ∀ X : Matrix (Fin W) (Fin W) ℂ, P * (A * X) = A * X := fun X => by
    rw [← Matrix.mul_assoc, hPA]
  have h4 : ∀ X : Matrix (Fin W) (Fin W) ℂ, Aᴴ * (P * X) = Aᴴ * X := fun X => by
    rw [← Matrix.mul_assoc, hAhP]
  have h5 : ∀ X : Matrix (Fin W) (Fin W) ℂ, P * (Aᴴ * X) = Aᴴ * X := fun X => by
    rw [← Matrix.mul_assoc, hPAh]
  have hB : (P * H * A - A * H * P)ᴴ = Aᴴ * H * P - P * H * Aᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP, hH]
    simp only [Matrix.mul_assoc]
  rw [hB]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  have t1 : (Aᴴ * H * P * (P * H * A)).trace = (A * Aᴴ * (H * P * H)).trace := by
    rw [show Aᴴ * H * P * (P * H * A) = (Aᴴ * H * P * H) * A by
      simp only [Matrix.mul_assoc, h1], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have t2 : (Aᴴ * H * P * (A * H * P)).trace = (Aᴴ * (H * A * H)).trace := by
    rw [show Aᴴ * H * P * (A * H * P) = (Aᴴ * H * A * H) * P by
      simp only [Matrix.mul_assoc, h2], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc, h5]
  have t3 : (P * H * Aᴴ * (P * H * A)).trace = (A * (H * Aᴴ * H)).trace := by
    rw [show P * H * Aᴴ * (P * H * A) = P * (H * Aᴴ * H * A) by
      simp only [Matrix.mul_assoc, h4], Matrix.trace_mul_comm]
    rw [Matrix.trace_mul_comm A]
    simp only [Matrix.mul_assoc, hAP]
  have t4 : (P * H * Aᴴ * (A * H * P)).trace = (P * (H * (Aᴴ * A) * H)).trace := by
    rw [show P * H * Aᴴ * (A * H * P) = P * (H * (Aᴴ * A) * H * P) by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    rw [Matrix.trace_mul_comm P]
    simp only [Matrix.mul_assoc, hPP]
  rw [t1, t2, t3, t4]
  ring

/-- `v* v = Σ_i ‖v_i‖²`. -/
private lemma SkewBasis_dot_self {W : ℕ} (v : Fin W → ℂ) :
    star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp [dotProduct, Complex.conj_mul', Complex.ofReal_sum]

/-- Cauchy–Schwarz: `|u* a|² ≤ ‖u‖² ‖a‖²`. -/
private lemma SkewBasis_norm_dot_sq_le {W : ℕ} (u a : Fin W → ℂ) :
    ‖star u ⬝ᵥ a‖ ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖a i‖ ^ 2 := by
  have h1 : ‖star u ⬝ᵥ a‖ ≤ ∑ i, ‖u i‖ * ‖a i‖ := by
    calc ‖star u ⬝ᵥ a‖ ≤ ∑ i, ‖star (u i) * a i‖ := by
          simpa [dotProduct] using norm_sum_le Finset.univ (fun i => star (u i) * a i)
      _ = ∑ i, ‖u i‖ * ‖a i‖ := by simp
  calc ‖star u ⬝ᵥ a‖ ^ 2 ≤ (∑ i, ‖u i‖ * ‖a i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- `w* (P (i H_k) P) v = i (P w)* H_k (P v)` for Hermitian `P`. -/
private lemma SkewBasis_coef {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ} (hP : P.IsHermitian)
    (v w : Fin W → ℂ) (k : Fin W × Fin W) :
    star w ⬝ᵥ ((P * (Complex.I • hermBasis W k) * P) *ᵥ v) =
      Complex.I * (star (P *ᵥ w) ⬝ᵥ (hermBasis W k *ᵥ (P *ᵥ v))) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.smul_mulVec, Matrix.star_mulVec, hP.eq, dotProduct_smul, smul_eq_mul]

/-- `conj (a* H_k u) = u* H_k a`, since `H_k` is Hermitian. -/
private lemma SkewBasis_star_coef {W : ℕ} (k : Fin W × Fin W) (a u : Fin W → ℂ) :
    star (star a ⬝ᵥ (hermBasis W k *ᵥ u)) = star u ⬝ᵥ (hermBasis W k *ᵥ a) := by
  rw [← Matrix.star_dotProduct, Matrix.star_mulVec, (hermBasis_isHermitian W k).eq,
    Matrix.dotProduct_mulVec]

/-- `Σ_k (Im a* H_k u)² = ½ (‖u‖² ‖a‖² - Re(u* a)² + Im(u* a)²)`. -/
private lemma SkewBasis_sum_im_sq {W : ℕ} (u a : Fin W → ℂ) :
    ∑ k, ((star a ⬝ᵥ (hermBasis W k *ᵥ u)).im) ^ 2 =
      (1 / 2) * ((∑ i, ‖u i‖ ^ 2) * (∑ i, ‖a i‖ ^ 2) - (star u ⬝ᵥ a).re ^ 2 +
        (star u ⬝ᵥ a).im ^ 2) := by
  have hpt : ∀ s : ℂ, ((s.im ^ 2 : ℝ) : ℂ) =
      -(1 / 4) * (s * s - 2 * (s * star s) + star s * star s) := by
    intro s
    apply Complex.ext <;> simp [sq] <;> ring
  have hsum : ((∑ k, ((star a ⬝ᵥ (hermBasis W k *ᵥ u)).im) ^ 2 : ℝ) : ℂ) =
      -(1 / 4) * ((star a ⬝ᵥ u) * (star a ⬝ᵥ u) - 2 * ((star a ⬝ᵥ a) * (star u ⬝ᵥ u)) +
        (star u ⬝ᵥ a) * (star u ⬝ᵥ a)) := by
    rw [Complex.ofReal_sum]
    simp only [hpt, SkewBasis_star_coef]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      SkewBasis_sum_bilin, SkewBasis_sum_bilin, SkewBasis_sum_bilin]
  have h := congrArg Complex.re hsum
  rw [Complex.ofReal_re] at h
  rw [h, Matrix.star_dotProduct a u, SkewBasis_dot_self a, SkewBasis_dot_self u]
  generalize (∑ i, ‖a i‖ ^ 2) = Sa
  generalize (∑ i, ‖u i‖ ^ 2) = Su
  generalize star u ⬝ᵥ a = c
  simp
  ring

/-- `Σ_i ‖(a - t u)_i‖² = ‖a‖² - 2 t Re(u* a) + t² ‖u‖²` for real `t`. -/
private lemma SkewBasis_sum_sub_smul {W : ℕ} (u a : Fin W → ℂ) (t : ℝ) :
    ∑ i, ‖(a - (t : ℂ) • u) i‖ ^ 2 =
      (∑ i, ‖a i‖ ^ 2) - 2 * t * (star u ⬝ᵥ a).re + t ^ 2 * ∑ i, ‖u i‖ ^ 2 := by
  have hpt : ∀ z y : ℂ, ‖z - (t : ℂ) * y‖ ^ 2 =
      ‖z‖ ^ 2 - 2 * t * (star y * z).re + t ^ 2 * ‖y‖ ^ 2 := by
    intro z y
    simp only [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hpt, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [dotProduct, Complex.re_sum, Finset.mul_sum]

/-- The frame `K_k = P (i H_k) P` of `𝔨_P`. -/
def skewProjBasis {W : ℕ} (P : Matrix (Fin W) (Fin W) ℂ) (k : Fin W × Fin W) :
    Matrix (Fin W) (Fin W) ℂ :=
  P * (Complex.I • hermBasis W k) * P

/-- The real orthogonal projection of `w` onto `𝓗_v = {w ∈ ran P : Re(v* w) = 0}`
(Lemma 9.3 [su:lem:chosen-generator](iv)): `P w - (Re((P v)* w) / ‖P v‖²) P v`. -/
def tangProj {W : ℕ} (P : Matrix (Fin W) (Fin W) ℂ) (v w : Fin W → ℂ) : Fin W → ℂ :=
  P *ᵥ w - (((star (P *ᵥ v) ⬝ᵥ w).re / ∑ i, ‖(P *ᵥ v) i‖ ^ 2 : ℝ) : ℂ) • (P *ᵥ v)

/-- `Σ_k ‖[K_k, A]‖²_HS = 2 Tr(P) ‖A‖²_HS - 2 |Tr A|²` for `A = P A P`; hence (9.33)
[su:eq:commutator-basis-bound] `Σ_k ‖[K_k, A]‖²_HS ≤ 2 W ‖A‖²_HS`. -/
theorem sum_hsSq_comm_skewProjBasis {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) {A : Matrix (Fin W) (Fin W) ℂ} (hA : P * A * P = A) :
    ∑ k, hsSq (skewProjBasis P k * A - A * skewProjBasis P k) =
      2 * P.trace.re * hsSq A - 2 * ‖A.trace‖ ^ 2 := by
  unfold skewProjBasis
  have hPA : P * A = A := by
    calc P * A = P * (P * A * P) := by rw [hA]
      _ = P * A * P := by simp only [← Matrix.mul_assoc, hPP]
      _ = A := hA
  have hAP : A * P = A := by
    calc A * P = P * A * P * P := by rw [hA]
      _ = P * A * P := by simp only [Matrix.mul_assoc, hPP]
      _ = A := hA
  have hP' : Pᴴ = P := hP.eq
  have h3 : ∀ X : Matrix (Fin W) (Fin W) ℂ, A * (P * X) = A * X := fun X => by
    rw [← Matrix.mul_assoc, hAP]
  have hcomm : ∀ k, P * (Complex.I • hermBasis W k) * P * A -
      A * (P * (Complex.I • hermBasis W k) * P) =
      Complex.I • (P * hermBasis W k * A - A * hermBasis W k * P) := by
    intro k
    simp only [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
    congr 1
    simp only [Matrix.mul_assoc, hPA, h3]
  have hk : ∀ k, ((hsSq (P * (Complex.I • hermBasis W k) * P * A -
      A * (P * (Complex.I • hermBasis W k) * P)) : ℝ) : ℂ) =
      (A * Aᴴ * (hermBasis W k * P * hermBasis W k)).trace -
        (Aᴴ * (hermBasis W k * A * hermBasis W k)).trace -
        (A * (hermBasis W k * Aᴴ * hermBasis W k)).trace +
          (P * (hermBasis W k * (Aᴴ * A) * hermBasis W k)).trace := by
    intro k
    rw [← SkewBasis_trace_conjTranspose_mul, hcomm k]
    have h : (Complex.I • (P * hermBasis W k * A - A * hermBasis W k * P))ᴴ *
        (Complex.I • (P * hermBasis W k * A - A * hermBasis W k * P)) =
        (P * hermBasis W k * A - A * hermBasis W k * P)ᴴ *
          (P * hermBasis W k * A - A * hermBasis W k * P) := by
      simp [Matrix.conjTranspose_smul, smul_smul]
    rw [h]
    exact SkewBasis_trace_comm_sq hP' (hermBasis_isHermitian W k) hPP hPA hAP
  have hTP : P.trace = (P.trace.re : ℂ) := by
    have h := Matrix.trace_conjTranspose P
    rw [hP'] at h
    apply Complex.ext
    · simp
    · have := congrArg Complex.im h
      simp at this ⊢
      linarith
  have key : ((∑ k, hsSq (P * (Complex.I • hermBasis W k) * P * A -
      A * (P * (Complex.I • hermBasis W k) * P)) : ℝ) : ℂ) =
      ((2 * P.trace.re * hsSq A - 2 * ‖A.trace‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp only [hk, Finset.sum_add_distrib, Finset.sum_sub_distrib, SkewBasis_sum_trace_mul]
    have hAA : (A * Aᴴ).trace = (hsSq A : ℂ) := by
      rw [Matrix.trace_mul_comm]
      exact SkewBasis_trace_conjTranspose_mul A
    have hAA' : (Aᴴ * A).trace = (hsSq A : ℂ) := SkewBasis_trace_conjTranspose_mul A
    have hc : star A.trace * A.trace = ((‖A.trace‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def]; exact Complex.conj_mul' _
    rw [hAA, hAA', Matrix.trace_conjTranspose]
    push_cast
    rw [← hTP, hc, mul_comm A.trace, hc]
    ring
  exact_mod_cast key

/-- The covariance of `(K_k v)_k` (proof of Lemma 9.4 [us:lem:score]):
`Σ_k Re(w* K_k v)² ≤ ‖P v‖² ‖Π_v w‖²`. -/
theorem sum_sq_re_skewProjBasis_le {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (v w : Fin W → ℂ) :
    ∑ k, (star w ⬝ᵥ (skewProjBasis P k *ᵥ v)).re ^ 2 ≤
      (∑ i, ‖(P *ᵥ v) i‖ ^ 2) * ∑ i, ‖tangProj P v w i‖ ^ 2 := by
  unfold tangProj
  simp only [skewProjBasis]
  have hk : ∀ k, (star w ⬝ᵥ ((P * (Complex.I • hermBasis W k) * P) *ᵥ v)).re ^ 2 =
      ((star (P *ᵥ w) ⬝ᵥ (hermBasis W k *ᵥ (P *ᵥ v))).im) ^ 2 := by
    intro k
    rw [SkewBasis_coef hP]
    simp
  have hx : star (P *ᵥ v) ⬝ᵥ w = star (P *ᵥ v) ⬝ᵥ (P *ᵥ w) := by
    rw [Matrix.star_mulVec, hP.eq, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, hPP]
  simp only [hk]
  rw [SkewBasis_sum_im_sq, hx, SkewBasis_sum_sub_smul]
  have hcs := SkewBasis_norm_dot_sq_le (P *ᵥ v) (P *ᵥ w)
  have hSu : 0 ≤ ∑ i, ‖(P *ᵥ v) i‖ ^ 2 := by positivity
  generalize star (P *ᵥ v) ⬝ᵥ (P *ᵥ w) = c at hcs ⊢
  generalize (∑ i, ‖(P *ᵥ w) i‖ ^ 2) = Sa at hcs ⊢
  generalize (∑ i, ‖(P *ᵥ v) i‖ ^ 2) = Su at hcs hSu ⊢
  have hn : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hn] at hcs
  rcases hSu.eq_or_lt with h0 | hpos
  · subst h0
    simp only [zero_mul, mul_zero, div_zero]
    nlinarith [sq_nonneg c.re, sq_nonneg c.im]
  · have : Su * (Sa - 2 * (c.re / Su) * c.re + (c.re / Su) ^ 2 * Su) = Su * Sa - c.re ^ 2 := by
      field_simp
      ring
    rw [this]
    nlinarith [sq_nonneg c.re, sq_nonneg c.im]

end LSBA
