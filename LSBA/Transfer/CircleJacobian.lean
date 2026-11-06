import LSBA.Transfer.CircleMeasure
import LSBA.Transfer.VolCocycle

/-!
# The angular Jacobian

The exact angular Jacobian (8.36) [cc:eq:jac], stated as the change-of-variables identity
`∫ φ(T·y) e^{−2c(T; y)} dm_U(y) = ∫ φ dm_{TU}` for `J`-unitary `T`, from `e^{−2c} = ‖A_T v_θ‖^{−2}`
and the Möbius action on the circle (Lemma F.1 [cc:lem:quotient]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Helpers for Lemma F.1 [cc:lem:quotient] -/

/-- A `J`-unitary matrix is invertible. -/
private theorem circleJacobian_isUnit {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : Tᴴ * isoJ W * T = isoJ W) : IsUnit T := by
  rw [Matrix.isUnit_iff_isUnit_det]
  refine Matrix.isUnit_det_of_left_inverse (B := isoJ W * Tᴴ * isoJ W) ?_
  calc isoJ W * Tᴴ * isoJ W * T = isoJ W * (Tᴴ * isoJ W * T) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hT, isoJ_mul_isoJ]

/-- `Π_{TU} J T v = 0` for `P_U J v = 0` and `T* J T = J`. -/
private theorem circleJacobian_flagProj_J {W : ℕ} {T P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : Tᴴ * isoJ W * T = isoJ W) {v : Fin 2 × Fin W → ℂ} (hv : P *ᵥ (isoJ W *ᵥ v) = 0) :
    flagProj T P *ᵥ (isoJ W *ᵥ (T *ᵥ v)) = 0 := by
  have h : flagProj T P * isoJ W * T =
      T * P * (P * Tᴴ * T * P + (1 - P))⁻¹ * (P * isoJ W) := by
    unfold flagProj
    calc _ = T * P * (P * Tᴴ * T * P + (1 - P))⁻¹ * P * (Tᴴ * isoJ W * T) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hT]; simp only [Matrix.mul_assoc]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec (N := P * isoJ W),
    ← Matrix.mulVec_mulVec (M := P), hv, Matrix.mulVec_zero]

/-- `A_T v = (1 - Π_{TU}) T v` for `P_U J v = 0`: the height of `T v` over `TU` lies in
`H_{TU}`. -/
private theorem circleJacobian_quotProj_T {W : ℕ}
    {T P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hT : Tᴴ * isoJ W * T = isoJ W)
    {v : Fin 2 × Fin W → ℂ} (hv : P *ᵥ (isoJ W *ᵥ v) = 0) :
    quotProj (flagProj T P) *ᵥ (T *ᵥ v) = (1 - flagProj T P) *ᵥ (T *ᵥ v) := by
  unfold quotProj
  rw [Matrix.sub_mulVec _ (isoJ W * flagProj T P * isoJ W), ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, circleJacobian_flagProj_J hT hv, Matrix.mulVec_zero, sub_zero]

/-- `J` is Hermitian: `v* (J u) = (J v)* u`. -/
private theorem circleJacobian_star_J {W : ℕ} (v u : Fin 2 × Fin W → ℂ) :
    star v ⬝ᵥ (isoJ W *ᵥ u) = star (isoJ W *ᵥ v) ⬝ᵥ u := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, isoJ_conjTranspose]

/-- `e* f = 0` for a circle basis. -/
private theorem circleJacobian_star_ef {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) : star e ⬝ᵥ f = 0 := by
  obtain ⟨-, -, heJ, hfJ, -, -⟩ := hef
  have h := circleJacobian_star_J e f
  rw [hfJ, heJ, dotProduct_neg] at h
  have h2 : (2 : ℂ) * (star e ⬝ᵥ f) = 0 := by linear_combination -h
  simpa using h2

/-- For orthonormal `e, f`: `(p e + q f)* (p' e + q' f) = p̄ p' + q̄ q'`. -/
private theorem circleJacobian_dot_pair {ι : Type*} [Fintype ι] {e f : ι → ℂ}
    (he : star e ⬝ᵥ e = 1) (hf : star f ⬝ᵥ f = 1) (hef : star e ⬝ᵥ f = 0) (p q p' q' : ℂ) :
    star (p • e + q • f) ⬝ᵥ (p' • e + q' • f) = star p * p' + star q * q' := by
  have hfe : star f ⬝ᵥ e = 0 := by rw [Matrix.star_dotProduct, hef, star_zero]
  simp only [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, he, hf, hef, hfe, smul_eq_mul]
  ring

/-- `|1/√2|² = 1/2`. -/
private theorem circleJacobian_s_sq :
    star (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- `|e^{iθ}|² = 1`. -/
private theorem circleJacobian_z_sq (θ : ℝ) :
    star (Complex.exp ((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]
  norm_num

/-- `v_θ = (1/√2) e + (e^{iθ}/√2) f`. -/
private theorem circleJacobian_vec_eq {W : ℕ} (e f : Fin 2 × Fin W → ℂ) (θ : ℝ) :
    circleVec e f θ = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • e +
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) • f := by
  unfold circleVec
  rw [smul_add, smul_smul]

/-- `v_θ` is a unit vector with `P v_θ = 0` and `P J v_θ = 0`. -/
private theorem circleJacobian_vec_spec {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) (θ : ℝ) :
    star (circleVec e f θ) ⬝ᵥ circleVec e f θ = 1 ∧ P *ᵥ circleVec e f θ = 0 ∧
      P *ᵥ (isoJ W *ᵥ circleVec e f θ) = 0 := by
  have h0 := circleJacobian_star_ef hef
  obtain ⟨he, hf, heJ, hfJ, heP, hfP⟩ := hef
  refine ⟨?_, ?_, ?_⟩
  · rw [circleJacobian_vec_eq, circleJacobian_dot_pair he hf h0, star_mul']
    linear_combination (1 + star (Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp ((θ : ℂ) * Complex.I)) * circleJacobian_s_sq + (1 / 2 : ℂ) * circleJacobian_z_sq θ
  · rw [circleJacobian_vec_eq]
    simp [Matrix.mulVec_smul, Matrix.mulVec_add, heP, hfP]
  · rw [circleJacobian_vec_eq]
    simp [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_neg, heJ, hfJ, heP, hfP]

/-- Lemma F.1 [cc:lem:quotient]: `e^{2c(T; U, Y_θ)} = ‖A_T v_θ‖²` with
`A_T v = proj_{H_{TU}} T v`, for `T* J T = J`. -/
theorem exp_two_mul_volCocycle_circlePair {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : Tᴴ * isoJ W * T = isoJ W) (x : IsoFlag W) {e f : Fin 2 × Fin W → ℂ}
    (hef : IsCircleBasis x.1.1 e f) (θ : ℝ) :
    Real.exp (2 * volCocycle T ⟨circlePair x.1.1 e f θ, circlePair_mem_isoFlags x.2.1 hef θ⟩) =
      ∑ i, ‖(quotProj (flagProj T x.1.1) *ᵥ (T *ᵥ circleVec e f θ)) i‖ ^ 2 := by
  obtain ⟨hv1, hPv, hPJv⟩ := circleJacobian_vec_spec hef θ
  have hYv : (circlePair x.1.1 e f θ).2 *ᵥ circleVec e f θ = circleVec e f θ := by
    simp only [circlePair, Matrix.add_mulVec, hPv, Matrix.vecMulVec_mulVec, hv1, zero_add]
    simp
  have h := exp_volCocycle_eq (circleJacobian_isUnit hT)
    ⟨circlePair x.1.1 e f θ, circlePair_mem_isoFlags x.2.1 hef θ⟩ hYv hPv hv1
  rw [two_mul, Real.exp_add, h, Real.mul_self_sqrt (Finset.sum_nonneg fun i _ => by positivity),
    circleJacobian_quotProj_T hT hPJv]
  rfl

/-! ### Helpers for (8.36) [cc:eq:jac] -/

open scoped ComplexOrder in
/-- Two Hermitian idempotents `B`, `B'` with `B B' = B'` and equal traces coincide. -/
private theorem circleJacobian_eq_of_trace {ι : Type*} [Fintype ι] {B B' : Matrix ι ι ℂ}
    (hB : Bᴴ = B) (hBB : B * B = B) (hB' : B'ᴴ = B') (hB'B' : B' * B' = B')
    (hmul : B * B' = B') (htr : B.trace = B'.trace) : B = B' := by
  have hmul' : B' * B = B' := by
    have := congrArg Matrix.conjTranspose hmul
    rwa [Matrix.conjTranspose_mul, hB, hB'] at this
  have hD : (B - B')ᴴ = B - B' := by rw [Matrix.conjTranspose_sub, hB, hB']
  have hDD : (B - B') * (B - B') = B - B' := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, hBB, hmul, hmul', hB'B']
    abel
  have htr0 : ((B - B')ᴴ * (B - B')).trace = 0 := by
    rw [hD, hDD, Matrix.trace_sub, htr, sub_self]
  exact sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr0)

/-- `quotProj P` fixes `u` when `P u = 0` and `P J u = 0`. -/
private theorem circleJacobian_Q_mulVec {W : ℕ}
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {u : Fin 2 × Fin W → ℂ}
    (h1 : P *ᵥ u = 0) (h2 : P *ᵥ (isoJ W *ᵥ u) = 0) : quotProj P *ᵥ u = u := by
  unfold quotProj
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, h2, h1]
  simp

/-- `quotProj P = e e* + f f*` for a circle basis `(e, f)` (Lemma F.1 [cc:lem:quotient]). -/
private theorem circleJacobian_quotProj_eq {W : ℕ}
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hP : P ∈ isoBases W)
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) :
    quotProj P = Matrix.vecMulVec e (star e) + Matrix.vecMulVec f (star f) := by
  have hW : 1 ≤ W := by
    by_contra h
    have hW : W = 0 := by omega
    subst hW
    have := hef.1
    simp [dotProduct] at this
  obtain ⟨hQh, hQQ, -, hQtr, -⟩ := quotProj_spec hW hP
  have h0 := circleJacobian_star_ef hef
  obtain ⟨he, hf, heJ, hfJ, heP, hfP⟩ := hef
  have hQe : quotProj P *ᵥ e = e :=
    circleJacobian_Q_mulVec heP (by rw [heJ, heP])
  have hQf : quotProj P *ᵥ f = f :=
    circleJacobian_Q_mulVec hfP (by rw [hfJ, Matrix.mulVec_neg, hfP, neg_zero])
  have h0' : star f ⬝ᵥ e = 0 := by rw [Matrix.star_dotProduct, h0, star_zero]
  have hEE : Matrix.vecMulVec e (star e) * Matrix.vecMulVec e (star e) =
      Matrix.vecMulVec e (star e) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, he, one_smul]
  have hEF : Matrix.vecMulVec e (star e) * Matrix.vecMulVec f (star f) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, h0, zero_smul, Matrix.vecMulVec_zero]
  have hFE : Matrix.vecMulVec f (star f) * Matrix.vecMulVec e (star e) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, h0', zero_smul, Matrix.vecMulVec_zero]
  have hFF : Matrix.vecMulVec f (star f) * Matrix.vecMulVec f (star f) =
      Matrix.vecMulVec f (star f) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hf, one_smul]
  refine circleJacobian_eq_of_trace hQh hQQ ?_ ?_ ?_ ?_
  · rw [Matrix.conjTranspose_add, Matrix.conjTranspose_vecMulVec, Matrix.conjTranspose_vecMulVec,
      star_star, star_star]
  · simp only [Matrix.add_mul, Matrix.mul_add, hEE, hEF, hFE, hFF, zero_add, add_zero]
  · rw [Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hQe, hQf]
  · rw [Matrix.trace_add, Matrix.trace_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm e,
      dotProduct_comm f, he, hf, hQtr]
    norm_num

/-- For a circle basis `(e', f')` of `P'`, `quotProj P' u = (e'* u) e' + (f'* u) f'`. -/
private theorem circleJacobian_expand {W : ℕ}
    {P' : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hP' : P' ∈ isoBases W)
    {e' f' : Fin 2 × Fin W → ℂ} (hef' : IsCircleBasis P' e' f') (u : Fin 2 × Fin W → ℂ) :
    quotProj P' *ᵥ u = (star e' ⬝ᵥ u) • e' + (star f' ⬝ᵥ u) • f' := by
  rw [circleJacobian_quotProj_eq hP' hef', Matrix.add_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.vecMulVec_mulVec]
  simp

/-- `A_T : H_U → H_{TU}` preserves the `J`-form (proof of Lemma F.1 [cc:lem:quotient]): for
`P_U J u = P_U J u' = 0` and a circle basis `(e', f')` of `Π_{TU}`,
`(e'* T u)‾ (e'* T u') − (f'* T u)‾ (f'* T u') = u* J u'`. -/
private theorem circleJacobian_form {W : ℕ} (hW : 1 ≤ W)
    {T P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hT : Tᴴ * isoJ W * T = isoJ W)
    (hPi : flagProj T P ∈ isoBases W) {e' f' : Fin 2 × Fin W → ℂ}
    (hef' : IsCircleBasis (flagProj T P) e' f') {u u' : Fin 2 × Fin W → ℂ}
    (hu : P *ᵥ (isoJ W *ᵥ u) = 0) (hu' : P *ᵥ (isoJ W *ᵥ u') = 0) :
    star (star e' ⬝ᵥ (T *ᵥ u)) * (star e' ⬝ᵥ (T *ᵥ u')) -
      star (star f' ⬝ᵥ (T *ᵥ u)) * (star f' ⬝ᵥ (T *ᵥ u')) = star u ⬝ᵥ (isoJ W *ᵥ u') := by
  obtain ⟨hQh, hQQ, hJQ, -, hQPi⟩ := quotProj_spec hW hPi
  have hPi' := hPi
  obtain ⟨hPih, -, -, hPiJ⟩ := hPi'
  have hPiQ : flagProj T P * quotProj (flagProj T P) = 0 := by
    have := congrArg Matrix.conjTranspose hQPi
    rwa [Matrix.conjTranspose_mul, hQh.eq, hPih.eq, Matrix.conjTranspose_zero] at this
  have hsplit : ∀ {t : Fin 2 × Fin W → ℂ}, P *ᵥ (isoJ W *ᵥ t) = 0 →
      (quotProj (flagProj T P) + flagProj T P) *ᵥ (T *ᵥ t) = T *ᵥ t := by
    intro t ht
    rw [Matrix.add_mulVec, circleJacobian_quotProj_T hT ht, Matrix.sub_mulVec, Matrix.one_mulVec,
      sub_add_cancel]
  have hM : (quotProj (flagProj T P) + flagProj T P)ᴴ * isoJ W *
      (quotProj (flagProj T P) + flagProj T P) = quotProj (flagProj T P) * isoJ W := by
    rw [Matrix.conjTranspose_add, hQh.eq, hPih.eq]
    have h1 : quotProj (flagProj T P) * isoJ W * quotProj (flagProj T P) =
        quotProj (flagProj T P) * isoJ W := by
      calc _ = quotProj (flagProj T P) * (isoJ W * quotProj (flagProj T P)) := by
            rw [Matrix.mul_assoc]
        _ = quotProj (flagProj T P) * quotProj (flagProj T P) * isoJ W := by
            rw [hJQ, Matrix.mul_assoc]
        _ = _ := by rw [hQQ]
    have h2 : quotProj (flagProj T P) * isoJ W * flagProj T P = 0 := by
      rw [← hJQ, Matrix.mul_assoc, hQPi, Matrix.mul_zero]
    have h3 : flagProj T P * isoJ W * quotProj (flagProj T P) = 0 := by
      rw [Matrix.mul_assoc, hJQ, ← Matrix.mul_assoc, hPiQ, Matrix.zero_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, h1, h2, h3, hPiJ, add_zero]
  have key : star (T *ᵥ u) ⬝ᵥ (isoJ W *ᵥ (T *ᵥ u')) = star u ⬝ᵥ (isoJ W *ᵥ u') := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hT]
  have key2 : star (T *ᵥ u) ⬝ᵥ (isoJ W *ᵥ (T *ᵥ u')) =
      star (T *ᵥ u) ⬝ᵥ ((quotProj (flagProj T P) * isoJ W) *ᵥ (T *ᵥ u')) := by
    calc _ = star ((quotProj (flagProj T P) + flagProj T P) *ᵥ (T *ᵥ u)) ⬝ᵥ
          (isoJ W *ᵥ ((quotProj (flagProj T P) + flagProj T P) *ᵥ (T *ᵥ u'))) := by
          rw [hsplit hu, hsplit hu']
      _ = _ := by
          rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
            Matrix.mulVec_mulVec, hM]
  have hQJ : (quotProj (flagProj T P) * isoJ W) *ᵥ (T *ᵥ u') =
      (star e' ⬝ᵥ (T *ᵥ u')) • e' - (star f' ⬝ᵥ (T *ᵥ u')) • f' := by
    rw [← Matrix.mulVec_mulVec, circleJacobian_expand hPi hef', circleJacobian_star_J,
      circleJacobian_star_J, hef'.2.2.1, hef'.2.2.2.1, star_neg, neg_dotProduct, neg_smul,
      sub_eq_add_neg]
  rw [← key, key2, hQJ, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    Matrix.star_dotProduct (T *ᵥ u) e', Matrix.star_dotProduct (T *ᵥ u) f']
  ring

/-- `|v|² = v* v` for `v : ι → ℂ`. -/
private theorem circleJacobian_sum_sq {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ w := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow, Complex.star_def,
    Complex.conj_mul']

/-- `θ ↦ (P, P + v_θ v_θ*)` is continuous. -/
private theorem circleJacobian_continuous {W : ℕ} (P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (e f : Fin 2 × Fin W → ℂ) : Continuous (circlePair P e f) := by
  unfold circlePair circleVec
  refine continuous_const.prodMk (continuous_const.add ?_)
  refine Continuous.matrix_vecMulVec ?_ ?_
  · fun_prop
  · fun_prop

/-- `e^{it} = 1` forces `t ∈ 2πℤ`. -/
private theorem circleJacobian_exp_eq_one {t : ℝ} (h : Complex.exp ((t : ℂ) * Complex.I) = 1) :
    ∃ n : ℤ, t = n * (2 * π) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have h2 : ((t : ℂ) - (n * (2 * π) : ℝ)) * Complex.I = 0 := by
    rw [sub_mul, hn]
    push_cast
    ring
  have h3 := (mul_eq_zero.mp h2).resolve_right Complex.I_ne_zero
  exact_mod_cast sub_eq_zero.mp h3

/-- The flags over a base in `ℂ^0` form a single point. -/
private theorem circleJacobian_subsingleton : Subsingleton (IsoFlag 0) := by
  have h : ∀ M N : Matrix (Fin 2 × Fin 0) (Fin 2 × Fin 0) ℂ, M = N := fun M N => by
    ext i
    exact i.2.elim0
  exact ⟨fun y y' => Subtype.ext (Prod.ext (h _ _) (h _ _))⟩

/-- (8.36) [cc:eq:jac] as a change of variables: for `T* J T = J` and measurable `φ ≥ 0`,
`∫ φ(TY) e^{-2c(T; U, Y)} dm_U(Y) = ∫ φ dm_{TU}`. -/
theorem lintegral_circleMeasure_flagAct {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : Tᴴ * isoJ W * T = isoJ W) (x : IsoFlag W) {φ : IsoFlag W → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ y, φ (flagAct T y) * ENNReal.ofReal (Real.exp (-2 * volCocycle T y)) ∂(circleMeasure x) =
      ∫⁻ y, φ y ∂(circleMeasure (flagAct T x)) := by
  by_cases hW0 : W = 0
  · subst hW0
    have hS := circleJacobian_subsingleton
    have h1 : ∀ y : IsoFlag 0, flagAct T y = y := fun y => Subsingleton.elim _ _
    have h2 : ∀ y : IsoFlag 0, volCocycle T y = 0 := fun y => by
      have : y.1.2 = y.1.1 := by
        ext i
        exact i.2.elim0
      unfold volCocycle
      rw [this, sub_self]
    simp only [h1, h2, mul_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  have hW : 1 ≤ W := Nat.one_le_iff_ne_zero.mpr hW0
  have hTu := circleJacobian_isUnit hT
  have hP : x.1.1 ∈ isoBases W := x.2.1
  obtain ⟨e, f, hef⟩ := exists_isCircleBasis hW hP
  have hPieq : (flagAct T x).1.1 = flagProj T x.1.1 := by rw [flagAct_coe hT x]
  have hPi : flagProj T x.1.1 ∈ isoBases W := hPieq ▸ (flagAct T x).2.1
  obtain ⟨e', f', hef'⟩ := exists_isCircleBasis hW hPi
  -- the matrix of `A_T` in the bases `(e, f)` and `(e', f')`
  obtain ⟨a, ha⟩ : ∃ a, star e' ⬝ᵥ (T *ᵥ e) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, star e' ⬝ᵥ (T *ᵥ f) = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, star f' ⬝ᵥ (T *ᵥ e) = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, star f' ⬝ᵥ (T *ᵥ f) = d := ⟨_, rfl⟩
  have hJe : x.1.1 *ᵥ (isoJ W *ᵥ e) = 0 := by rw [hef.2.2.1, hef.2.2.2.2.1]
  have hJf : x.1.1 *ᵥ (isoJ W *ᵥ f) = 0 := by
    rw [hef.2.2.2.1, Matrix.mulVec_neg, hef.2.2.2.2.2, neg_zero]
  have R1 : star a * a - star c * c = 1 := by
    have h := circleJacobian_form hW hT hPi hef' hJe hJe
    rwa [ha, hc, hef.2.2.1, hef.1] at h
  have R2 : star b * b - star d * d = -1 := by
    have h := circleJacobian_form hW hT hPi hef' hJf hJf
    rwa [hb, hd, hef.2.2.2.1, dotProduct_neg, hef.2.1] at h
  have R3 : star a * b - star c * d = 0 := by
    have h := circleJacobian_form hW hT hPi hef' hJe hJf
    rwa [ha, hb, hc, hd, hef.2.2.2.1, dotProduct_neg, circleJacobian_star_ef hef, neg_zero] at h
  have R3' : star b * a - star d * c = 0 := by
    have h := congrArg star R3
    rw [star_sub, star_mul', star_mul', star_star, star_star, star_zero] at h
    linear_combination h
  -- `A_T v_θ = ((a + b z) e' + (c + d z) f') / √2` with `z = e^{iθ}`
  set s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hs
  set A : ℝ → ℂ := fun θ => a + b * Complex.exp ((θ : ℂ) * Complex.I) with hA
  set B : ℝ → ℂ := fun θ => c + d * Complex.exp ((θ : ℂ) * Complex.I) with hB
  have hw : ∀ θ, quotProj (flagProj T x.1.1) *ᵥ (T *ᵥ circleVec e f θ) =
      (s * A θ) • e' + (s * B θ) • f' := by
    intro θ
    rw [circleJacobian_expand hPi hef', circleJacobian_vec_eq, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add, dotProduct_add, dotProduct_smul,
      dotProduct_smul, dotProduct_smul, dotProduct_smul, ha, hb, hc, hd]
    simp only [smul_eq_mul, hA, hB]
    congr 1 <;> congr 1 <;> ring
  have E1 : ∀ θ, star (A θ) * A θ = star (B θ) * B θ := by
    intro θ
    have hz := circleJacobian_z_sq θ
    simp only [hA, hB, star_add, star_mul']
    linear_combination R1 + Complex.exp ((θ : ℂ) * Complex.I) * R3 +
      star (Complex.exp ((θ : ℂ) * Complex.I)) * R3' +
      star (Complex.exp ((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) * R2 - hz
  have E2 : ∀ θ : ℝ,
      Complex.exp ((θ : ℂ) * Complex.I) * (star (A θ) * b - star (B θ) * d) = -1 := by
    intro θ
    have hz := circleJacobian_z_sq θ
    simp only [hA, hB, star_add, star_mul']
    linear_combination Complex.exp ((θ : ℂ) * Complex.I) * R3 +
      star (Complex.exp ((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) * R2 - hz
  have E3 : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) * (a * d - b * c) * star (A θ) = B θ := by
    intro θ
    have hAB : d * A θ - b * B θ = a * d - b * c := by simp only [hA, hB]; ring
    rw [← hAB]
    linear_combination (Complex.exp ((θ : ℂ) * Complex.I) * d) * E1 θ - B θ * E2 θ
  -- `e^{2c(T; U, Y_θ)} = |a + b z|²`
  have hs2 : star s * s = 1 / 2 := circleJacobian_s_sq
  have hexp2 : ∀ θ : ℝ, Real.exp (2 * volCocycle T
      ⟨circlePair x.1.1 e f θ, circlePair_mem_isoFlags x.2.1 hef θ⟩) = ‖A θ‖ ^ 2 := by
    intro θ
    rw [exp_two_mul_volCocycle_circlePair hT x hef θ, hw θ]
    have h := circleJacobian_sum_sq ((s * A θ) • e' + (s * B θ) • f')
    rw [circleJacobian_dot_pair hef'.1 hef'.2.1 (circleJacobian_star_ef hef'), star_mul',
      star_mul'] at h
    have hA2 : star (A θ) * A θ = (‖A θ‖ : ℂ) ^ 2 := by rw [Complex.star_def, Complex.conj_mul']
    have h2 : ((∑ i, ‖((s * A θ) • e' + (s * B θ) • f') i‖ ^ 2 : ℝ) : ℂ) =
        ((‖A θ‖ ^ 2 : ℝ) : ℂ) := by
      rw [h]
      push_cast
      linear_combination (star (A θ) * A θ + star (B θ) * B θ) * hs2 - (1 / 2 : ℂ) * E1 θ + hA2
    exact_mod_cast h2
  have hApos : ∀ θ : ℝ, 0 < ‖A θ‖ ^ 2 := fun θ => hexp2 θ ▸ Real.exp_pos _
  have hAne : ∀ θ : ℝ, A θ ≠ 0 := fun θ h => by
    have := hApos θ
    rw [h, norm_zero] at this
    norm_num at this
  have hBne : ∀ θ : ℝ, B θ ≠ 0 := fun θ h => by
    have h1 := E1 θ
    rw [h, mul_zero] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hAne θ (star_eq_zero.mp h2)
    · exact hAne θ h2
  -- the lift `g(θ) = ∫₀^θ |a + b e^{it}|⁻² dt` of the angle map
  set ρ : ℝ → ℝ := fun θ => (‖A θ‖ ^ 2)⁻¹ with hρ
  have hρpos : ∀ θ, 0 < ρ θ := fun θ => inv_pos.mpr (hApos θ)
  have hAc : Continuous A := by
    simp only [hA]
    fun_prop
  have hρc : Continuous ρ := ((continuous_norm.comp hAc).pow 2).inv₀ fun θ => (hApos θ).ne'
  set g : ℝ → ℝ := fun θ => ∫ t in (0 : ℝ)..θ, ρ t with hgdef
  have hg : ∀ θ, HasDerivAt g (ρ θ) θ := fun θ => (hρc.integral_hasStrictDerivAt 0 θ).hasDerivAt
  have hgmono : StrictMono g := strictMono_of_deriv_pos fun θ => by
    rw [(hg θ).deriv]
    exact hρpos θ
  have hg0 : g 0 = 0 := intervalIntegral.integral_same
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun θ => (hg θ).continuousAt
  -- the Möbius action `z' = (c + d z) / (a + b z) = ζ e^{i g(θ)}`
  have hlin : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := fun θ => by
    simpa using ((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I
  have hA' : ∀ θ : ℝ, HasDerivAt A
      (b * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I)) θ := fun θ =>
    ((hlin θ).cexp.const_mul b).const_add a
  have hB' : ∀ θ : ℝ, HasDerivAt B
      (d * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I)) θ := fun θ =>
    ((hlin θ).cexp.const_mul d).const_add c
  have hE' : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(g t : ℂ) * Complex.I))
      (Complex.exp (-(g θ : ℂ) * Complex.I) * (-(ρ θ : ℂ) * Complex.I)) θ := fun θ =>
    (((hg θ).ofReal_comp).neg.mul_const Complex.I).cexp
  have hh : ∀ θ : ℝ,
      HasDerivAt (fun t => B t / A t * Complex.exp (-(g t : ℂ) * Complex.I)) 0 θ := by
    intro θ
    have h1 := ((hB' θ).div (hA' θ) (hAne θ)).mul (hE' θ)
    convert h1 using 1
    have hρC : (ρ θ : ℂ) = (star (A θ) * A θ)⁻¹ := by
      simp only [hρ]
      push_cast
      rw [Complex.star_def, Complex.conj_mul']
    have hsA : star (A θ) ≠ 0 := star_ne_zero.mpr (hAne θ)
    have hE3 : Complex.exp ((θ : ℂ) * Complex.I) * (d * A θ - B θ * b) * star (A θ) = B θ := by
      have hAB : d * A θ - B θ * b = a * d - b * c := by simp only [hA, hB]; ring
      rw [hAB]
      exact E3 θ
    rw [Pi.div_apply, hρC]
    field_simp
    rw [hE3]
    simp
  have hconst : ∀ θ : ℝ, B θ / A θ * Complex.exp (-(g θ : ℂ) * Complex.I) = B 0 / A 0 :=
    fun θ => by
      have := is_const_of_deriv_eq_zero (fun t => (hh t).differentiableAt) (fun t => (hh t).deriv)
        θ 0
      simpa [hg0] using this
  set ζ : ℂ := B 0 / A 0 with hζdef
  have hζ : ∀ θ : ℝ, B θ / A θ = ζ * Complex.exp ((g θ : ℂ) * Complex.I) := by
    intro θ
    rw [← hconst θ, mul_assoc, ← Complex.exp_add]
    simp
  have hζ1 : ‖ζ‖ = 1 := by
    have h1 := E1 0
    rw [Complex.star_def, Complex.conj_mul', Complex.conj_mul'] at h1
    have h2 : ‖A 0‖ ^ 2 = ‖B 0‖ ^ 2 := by exact_mod_cast h1
    have h3 : ‖A 0‖ = ‖B 0‖ := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
    rw [hζdef, norm_div, h3, div_self (norm_ne_zero_iff.mpr (hBne 0))]
  have hζ0 : ζ ≠ 0 := fun h => by
    rw [h, norm_zero] at hζ1
    norm_num at hζ1
  -- one turn of `θ` is one turn of `g(θ)`
  have hz2π : Complex.exp (((2 * π : ℝ) : ℂ) * Complex.I) = 1 := by
    push_cast
    exact Complex.exp_two_pi_mul_I
  have hz0 : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have hgper : g (2 * π) = 2 * π := by
    have h1 : Complex.exp ((g (2 * π) : ℂ) * Complex.I) = 1 := by
      have h2 := hζ (2 * π)
      have hA2 : A (2 * π) = A 0 := by simp only [hA, hz2π, hz0]
      have hB2 : B (2 * π) = B 0 := by simp only [hB, hz2π, hz0]
      rw [hA2, hB2] at h2
      exact (mul_eq_left₀ hζ0).mp h2.symm
    obtain ⟨n, hn⟩ := circleJacobian_exp_eq_one h1
    have hpos : 0 < g (2 * π) := hg0 ▸ hgmono (by positivity)
    have hn1 : 1 ≤ n := by
      have h2 : (0 : ℝ) < n := by
        rw [hn] at hpos
        exact pos_of_mul_pos_left hpos (by positivity)
      have h3 : (0 : ℤ) < n := by exact_mod_cast h2
      omega
    have hn2 : n ≤ 1 := by
      by_contra hcon
      have h2le : (2 : ℝ) ≤ n := by exact_mod_cast (show (2 : ℤ) ≤ n by omega)
      have hlt : 2 * π < g (2 * π) := by
        rw [hn]
        nlinarith [pi_pos]
      obtain ⟨θ₁, ⟨h0θ, hθ2⟩, hgθ⟩ := intermediate_value_Icc (by positivity : (0 : ℝ) ≤ 2 * π)
        hgc.continuousOn (⟨by rw [hg0]; positivity, hlt.le⟩ :
          2 * π ∈ Set.Icc (g 0) (g (2 * π)))
      have hθpos : 0 < θ₁ := lt_of_le_of_ne h0θ fun h => by
        rw [← h, hg0] at hgθ
        linarith [pi_pos]
      have hθlt : θ₁ < 2 * π := lt_of_le_of_ne hθ2 fun h => by
        rw [h] at hgθ
        linarith
      have h3 : B θ₁ / A θ₁ = B 0 / A 0 := by rw [hζ θ₁, hgθ, hz2π, mul_one]
      rw [div_eq_div_iff (hAne θ₁) (hAne 0)] at h3
      have h4 : (a * d - b * c) * (Complex.exp ((θ₁ : ℂ) * Complex.I) - 1) = 0 := by
        simp only [hA, hB, hz0] at h3
        linear_combination h3
      have hdet : a * d - b * c ≠ 0 := fun h => hBne θ₁ (by rw [← E3 θ₁, h]; ring)
      have h5 := sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left hdet)
      obtain ⟨m, hm⟩ := circleJacobian_exp_eq_one h5
      have hm0 : (0 : ℝ) < m := by
        rw [hm] at hθpos
        exact pos_of_mul_pos_left hθpos (by positivity)
      have hm1 : (m : ℝ) < 1 := by
        rw [hm] at hθlt
        nlinarith [pi_pos]
      have hm0' : (0 : ℤ) < m := by exact_mod_cast hm0
      have hm1' : m < (1 : ℤ) := by exact_mod_cast hm1
      omega
    rw [hn, show n = 1 by omega]
    simp
  have himage : g '' Set.Ioc 0 (2 * π) = Set.Ioc 0 (2 * π) := by
    ext t
    constructor
    · rintro ⟨θ, ⟨h1, h2⟩, rfl⟩
      exact ⟨hg0 ▸ hgmono h1, hgper ▸ hgmono.monotone h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨θ, ⟨h3, h4⟩, h5⟩ := intermediate_value_Icc (by positivity : (0 : ℝ) ≤ 2 * π)
        hgc.continuousOn (⟨by rw [hg0]; exact h1.le, by rw [hgper]; exact h2⟩ :
          t ∈ Set.Icc (g 0) (g (2 * π)))
      refine ⟨θ, ⟨lt_of_le_of_ne h3 ?_, h4⟩, h5⟩
      rintro rfl
      rw [hg0] at h5
      linarith
  -- the circle basis `(e', ζ f')` of `TU`, in which `T·Y_θ = Y'_{g(θ)}`
  have hefζ : IsCircleBasis (flagAct T x).1.1 e' (ζ • f') := by
    rw [hPieq]
    obtain ⟨he1, hf1, heJ, hfJ, heP, hfP⟩ := hef'
    refine ⟨he1, ?_, heJ, ?_, heP, ?_⟩
    · rw [star_smul, smul_dotProduct, dotProduct_smul, hf1, smul_eq_mul, smul_eq_mul, mul_one,
        Complex.star_def, Complex.conj_mul', hζ1]
      norm_num
    · rw [Matrix.mulVec_smul, hfJ, smul_neg]
    · rw [Matrix.mulVec_smul, hfP, smul_zero]
  have hflag : ∀ θ : ℝ,
      flagAct T ⟨circlePair x.1.1 e f θ, circlePair_mem_isoFlags x.2.1 hef θ⟩ =
        ⟨circlePair (flagAct T x).1.1 e' (ζ • f') (g θ),
          circlePair_mem_isoFlags (flagAct T x).2.1 hefζ (g θ)⟩ := by
    intro θ
    obtain ⟨hv1, hPv, hPJv⟩ := circleJacobian_vec_spec hef θ
    have hYv : (circlePair x.1.1 e f θ).2 *ᵥ circleVec e f θ = circleVec e f θ := by
      simp only [circlePair, Matrix.add_mulVec, hPv, Matrix.vecMulVec_mulVec, hv1, zero_add]
      simp
    have hmemF := (flagAct T ⟨circlePair x.1.1 e f θ, circlePair_mem_isoFlags x.2.1 hef θ⟩).2
    rw [flagAct_coe hT] at hmemF
    obtain ⟨-, hFh, hFF, hFtr, hFPi', -⟩ := hmemF
    have hFPi : flagProj T (circlePair x.1.1 e f θ).2 * flagProj T x.1.1 = flagProj T x.1.1 :=
      hFPi'
    obtain ⟨-, hYh, hYY, -⟩ := circlePair_mem_isoFlags x.2.1 hef θ
    obtain ⟨-, hRh, hRR, hRtr, -, -⟩ := circlePair_mem_isoFlags (flagAct T x).2.1 hefζ (g θ)
    have hFT := (flagProj_spec hTu hYh hYY).2.2
    have hFTv : flagProj T (circlePair x.1.1 e f θ).2 *ᵥ (T *ᵥ circleVec e f θ) =
        T *ᵥ circleVec e f θ := by
      calc _ = flagProj T (circlePair x.1.1 e f θ).2 *ᵥ
            (T *ᵥ ((circlePair x.1.1 e f θ).2 *ᵥ circleVec e f θ)) := by rw [hYv]
        _ = (flagProj T (circlePair x.1.1 e f θ).2 * (T * (circlePair x.1.1 e f θ).2)) *ᵥ
            circleVec e f θ := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = _ := by rw [hFT, ← Matrix.mulVec_mulVec, hYv]
    have hFw : flagProj T (circlePair x.1.1 e f θ).2 *ᵥ
        (quotProj (flagProj T x.1.1) *ᵥ (T *ᵥ circleVec e f θ)) =
          quotProj (flagProj T x.1.1) *ᵥ (T *ᵥ circleVec e f θ) := by
      rw [circleJacobian_quotProj_T hT hPJv, Matrix.sub_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_sub, hFTv, Matrix.mulVec_mulVec, hFPi]
    have hv' : circleVec e' (ζ • f') (g θ) =
        (A θ)⁻¹ • (quotProj (flagProj T x.1.1) *ᵥ (T *ᵥ circleVec e f θ)) := by
      rw [hw θ, circleJacobian_vec_eq, ← hs, smul_add, smul_smul, smul_smul, smul_smul]
      have h1 := hζ θ
      congr 1
      · congr 1
        field_simp [hAne θ]
      · congr 1
        rw [show (A θ)⁻¹ * (s * B θ) = s * (B θ / A θ) by rw [div_eq_mul_inv]; ring, h1]
        ring
    have hFv' : flagProj T (circlePair x.1.1 e f θ).2 *ᵥ circleVec e' (ζ • f') (g θ) =
        circleVec e' (ζ • f') (g θ) := by
      rw [hv', Matrix.mulVec_smul, hFw]
    apply Subtype.ext
    rw [flagAct_coe hT]
    refine Prod.ext hPieq.symm ?_
    refine circleJacobian_eq_of_trace hFh.eq hFF hRh.eq hRR ?_ (hFtr.trans hRtr.symm)
    change flagProj T (circlePair x.1.1 e f θ).2 * ((flagAct T x).1.1 + Matrix.vecMulVec
        (circleVec e' (ζ • f') (g θ)) (star (circleVec e' (ζ • f') (g θ)))) = _
    have hFPi2 : flagProj T (circlePair x.1.1 e f θ).2 * (flagAct T x).1.1 = (flagAct T x).1.1 := by
      rw [hPieq]
      exact hFPi
    rw [Matrix.mul_add, Matrix.mul_vecMulVec, hFv', hFPi2]
    rfl
  -- the change of variables `θ' = g(θ)` on one turn
  have hGm : Measurable fun θ : ℝ =>
      (⟨circlePair x.1.1 e f θ, circlePair_mem_isoFlags x.2.1 hef θ⟩ : IsoFlag W) :=
    Measurable.subtype_mk (circleJacobian_continuous _ e f).measurable
  have hG'm : Measurable fun t : ℝ =>
      (⟨circlePair (flagAct T x).1.1 e' (ζ • f') t,
        circlePair_mem_isoFlags (flagAct T x).2.1 hefζ t⟩ : IsoFlag W) :=
    Measurable.subtype_mk (circleJacobian_continuous _ e' _).measurable
  have hΦm : Measurable fun y : IsoFlag W =>
      φ (flagAct T y) * ENNReal.ofReal (Real.exp (-2 * volCocycle T y)) := by
    have h1 : Measurable fun y : IsoFlag W => (T, y) := measurable_const.prodMk measurable_id
    have h2 := (measurable_flagAct W).comp h1
    have h3 := (measurable_volCocycle W).comp h1
    exact (hφ.comp h2).mul
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (h3.const_mul (-2))))
  rw [circleMeasure_eq_map x hef, circleMeasure_eq_map (flagAct T x) hefζ, lintegral_map hΦm hGm,
    lintegral_map hφ hG'm]
  unfold angleMeas
  rw [lintegral_smul_measure, lintegral_smul_measure]
  congr 1
  conv_rhs => rw [← himage]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc
    (fun θ _ => (hg θ).hasDerivWithinAt) hgmono.injective.injOn]
  refine lintegral_congr fun θ => ?_
  have hneg : Real.exp (-2 * volCocycle T
      ⟨circlePair x.1.1 e f θ, circlePair_mem_isoFlags x.2.1 hef θ⟩) = ρ θ := by
    rw [neg_mul, Real.exp_neg, hexp2 θ]
  rw [hflag θ, hneg, abs_of_pos (hρpos θ), mul_comm]

end LSBA
