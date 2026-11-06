import LSBA.Transfer.CircleMeasure
import LSBA.Upper.LieAlgebra

/-!
# The rotation of a circle of isotropic extensions

For an isotropic `U` with projection `P`, the generator `K_U = -(i/2) Q J` with
`Q = 1 - P - J P J` the projection onto `H_U = (U + JU)^⊥` (Lemma F.1 [cc:lem:quotient]): it is
`½ diag(-i, i)` in every `J`-eigenbasis of `H_U` and zero on `U + JU`, as in the proof of Lemma
F.3 [lem:c-operators], and `√2 K_U` lies in the algebra (10.1) [up:eq:lie-algebra] with
Hilbert–Schmidt norm one. The one-parameter group
`R_t = (1 - Q) + e^{-it/2} Q (1 + J)/2 + e^{it/2} Q (1 - J)/2 = e^{t K_U}` is unitary and
`J`-unitary, fixes `U`, and moves `Y_θ` of (F.1) [cc:eq:circle] to `Y_{θ+t}`; so the angular
measure `m_U` of Section 8.3 [sec:upper-inputs] is the law of `R_t Y` for uniform `t`, for every
`Y ⊃ U`, with no choice of frame. The derivative along the circle of a function of the projection
pair.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The generator `K_U = -(i/2) Q J` of the rotation of the circle `𝒞_U` (proof of Lemma F.3
[lem:c-operators]); `Q = 1 - P - J P J` is the projection onto `H_U` (Lemma F.1
[cc:lem:quotient]). -/
def circleGen {W : ℕ} (P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (-(Complex.I / 2)) • (quotProj P * isoJ W)

/-- `R_t = (1 - Q) + e^{-it/2} Q (1 + J)/2 + e^{it/2} Q (1 - J)/2`, the rotation of the circle
`𝒞_U` at unit angular speed (proof of Lemma F.3 [lem:c-operators]). -/
def circleRot {W : ℕ} (P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (t : ℝ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  1 - quotProj P +
    Complex.exp (-(((t / 2 : ℝ) : ℂ) * Complex.I)) • ((1 / 2 : ℂ) • (quotProj P * (1 + isoJ W))) +
    Complex.exp (((t / 2 : ℝ) : ℂ) * Complex.I) • ((1 / 2 : ℂ) • (quotProj P * (1 - isoJ W)))

/-- The derivative of `ψ` along the circle through the flag `y`: the derivative of
`ψ(R_s P_U R_s*, R_s P_Y R_s*)` at `s = 0`, that is `Dψ(P_U, P_Y) (0, [K_U, P_Y])` (proof of
Lemma F.3 [lem:c-operators]). -/
def circleDeriv {W : ℕ}
    (ψ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ)
    (y : IsoFlag W) : ℝ :=
  fderiv ℝ ψ y.1 (0, circleGen y.1.1 * y.1.2 - y.1.2 * circleGen y.1.1)

/-! ### Helpers -/

/-- `(1 - Q) + a Q (1 + J)/2 + b Q (1 - J)/2`. -/
private def circleRotation_E {ι : Type*} [Fintype ι] [DecidableEq ι] (Q J : Matrix ι ι ℂ)
    (a b : ℂ) : Matrix ι ι ℂ :=
  1 - Q + a • ((1 / 2 : ℂ) • (Q * (1 + J))) + b • ((1 / 2 : ℂ) • (Q * (1 - J)))

section circleRotationAlg

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q J : Matrix ι ι ℂ}

/-- The multiplication rule `E(a, b) E(c, d) = E(ac, bd)`. -/
private theorem circleRotation_E_mul (hQQ : Q * Q = Q) (hJJ : J * J = 1) (hJQ : J * Q = Q * J)
    (a b c d : ℂ) :
    circleRotation_E Q J a b * circleRotation_E Q J c d =
      circleRotation_E Q J (a * c) (b * d) := by
  have h2 : ∀ X : Matrix ι ι ℂ, X * J * J = X := fun X => by
    rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have h3 : ∀ X : Matrix ι ι ℂ, X * J * Q = X * Q * J := fun X => by
    rw [Matrix.mul_assoc, hJQ, ← Matrix.mul_assoc]
  unfold circleRotation_E
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hQQ, h2, h3]
  module

/-- `E(1, 1) = 1`. -/
private theorem circleRotation_E_one : circleRotation_E Q J 1 1 = 1 := by
  unfold circleRotation_E
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, one_smul]
  module

/-- `E(a, b)* = E(ā, b̄)`. -/
private theorem circleRotation_E_conjTranspose (hQh : Qᴴ = Q) (hJh : Jᴴ = J)
    (hJQ : J * Q = Q * J) (a b : ℂ) :
    (circleRotation_E Q J a b)ᴴ = circleRotation_E Q J (star a) (star b) := by
  unfold circleRotation_E
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hQh, hJh, Matrix.mul_add,
    Matrix.mul_sub, Matrix.mul_one, hJQ]
  simp

/-- `J` commutes with `E(a, b)`. -/
private theorem circleRotation_E_comm (hJQ : J * Q = Q * J) (a b : ℂ) :
    J * circleRotation_E Q J a b = circleRotation_E Q J a b * J := by
  unfold circleRotation_E
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hJQ]

/-- `E(a, b)` fixes the range of `P` when `Q P = Q J P = 0`. -/
private theorem circleRotation_E_mul_fix {P : Matrix ι ι ℂ} (hQP : Q * P = 0)
    (hQJP : Q * J * P = 0) (a b : ℂ) : circleRotation_E Q J a b * P = P := by
  unfold circleRotation_E
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one,
    Matrix.one_mul, Matrix.smul_mul, hQP, hQJP]
  simp

/-- `E(a, b) v = a v` for `Q v = v`, `J v = v`. -/
private theorem circleRotation_E_mulVec_plus {v : ι → ℂ} (hQ : Q *ᵥ v = v) (hJ : J *ᵥ v = v)
    (a b : ℂ) : circleRotation_E Q J a b *ᵥ v = a • v := by
  unfold circleRotation_E
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hQ, hJ, Matrix.mulVec_add, Matrix.mulVec_sub]
  module

/-- `E(a, b) v = b v` for `Q v = v`, `J v = -v`. -/
private theorem circleRotation_E_mulVec_minus {v : ι → ℂ} (hQ : Q *ᵥ v = v) (hJ : J *ᵥ v = -v)
    (a b : ℂ) : circleRotation_E Q J a b *ᵥ v = b • v := by
  unfold circleRotation_E
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hQ, hJ, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_neg]
  module

end circleRotationAlg

/-- `|e^z|² = 1` for `Re z = 0`. -/
private theorem circleRotation_star_exp (z : ℂ) (hz : z.re = 0) :
    star (Complex.exp z) * Complex.exp z = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have h : (starRingEnd ℂ) z + z = 0 := by
    apply Complex.ext <;> simp [hz]
  rw [h, Complex.exp_zero]

/-- `R_t = E(e^{-it/2}, e^{it/2})` for `Q = Q_U`. -/
private theorem circleRotation_eq {W : ℕ} (P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (t : ℝ) :
    circleRot P t = circleRotation_E (quotProj P) (isoJ W)
      (Complex.exp (-(((t / 2 : ℝ) : ℂ) * Complex.I)))
      (Complex.exp (((t / 2 : ℝ) : ℂ) * Complex.I)) :=
  rfl

/-- `d/dt e^{c i t/2} = (c i/2) e^{c i t/2}`. -/
private theorem circleRotation_hasDerivAt_exp (c : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (c * ((t / 2 : ℝ) : ℂ) * Complex.I))
      (Complex.exp (c * ((t / 2 : ℝ) : ℂ) * Complex.I) * (c * Complex.I / 2)) t := by
  have h0 : HasDerivAt (fun t : ℝ => c * ((t / 2 : ℝ) : ℂ) * Complex.I) (c * Complex.I / 2) t := by
    have h1 : HasDerivAt (fun t : ℝ => ((t / 2 : ℝ) : ℂ)) ((1 / 2 : ℝ) : ℂ) t :=
      ((hasDerivAt_id t).div_const 2).ofReal_comp
    convert (h1.const_mul c).mul_const Complex.I using 1
    push_cast; ring
  exact h0.cexp

/-- `tr J = 0`. -/
private theorem circleRotation_trace_isoJ (W : ℕ) : (isoJ W).trace = 0 := by
  unfold isoJ
  rw [Matrix.trace_kronecker]
  simp [Matrix.trace, Fin.sum_univ_two]

/-- `tr (Q J) = 0` for `Q = 1 - P - J P J`, `P` an isotropic projection. -/
private theorem circleRotation_trace_QJ {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hPP : P * P = P) (hPJ : P * isoJ W * P = 0) : (quotProj P * isoJ W).trace = 0 := by
  have h : quotProj P * isoJ W = isoJ W - P * isoJ W - isoJ W * P := by
    unfold quotProj
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, isoJ_mul_isoJ, Matrix.mul_one]
  have hPJt : (P * isoJ W).trace = 0 := by
    calc (P * isoJ W).trace = (P * (P * isoJ W)).trace := by rw [← Matrix.mul_assoc, hPP]
      _ = (P * isoJ W * P).trace := Matrix.trace_mul_comm _ _
      _ = 0 := by rw [hPJ, Matrix.trace_zero]
  rw [h, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm (isoJ W) P,
    circleRotation_trace_isoJ, hPJt]
  simp

/-- `‖A‖²_HS = Re tr (A* A)`. -/
private theorem circleRotation_hsSq {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    hsSq A = (Aᴴ * A).trace.re := by
  unfold hsSq
  rw [Finset.sum_comm, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']
  norm_cast

/-- `R_t v_θ = e^{-it/2} v_{θ+t}` for a circle basis `(e, f)` of `U`. -/
private theorem circleRotation_mulVec_circleVec {W : ℕ}
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {e f : Fin 2 × Fin W → ℂ}
    (hef : IsCircleBasis P e f) (θ t : ℝ) :
    circleRot P t *ᵥ circleVec e f θ =
      Complex.exp (-(((t / 2 : ℝ) : ℂ) * Complex.I)) • circleVec e f (θ + t) := by
  obtain ⟨-, -, hJe, hJf, hPe, hPf⟩ := hef
  have hQe : quotProj P *ᵥ e = e := by
    unfold quotProj
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hJe, hPe,
      Matrix.mulVec_zero, sub_zero]
  have hQf : quotProj P *ᵥ f = f := by
    unfold quotProj
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hJf,
      Matrix.mulVec_neg, hPf, Matrix.mulVec_zero, neg_zero, sub_zero]
  have hk : Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (((t / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-(((t / 2 : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [circleRotation_eq]
  unfold circleVec
  rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
    circleRotation_E_mulVec_plus hQe hJe, circleRotation_E_mulVec_minus hQf hJf, smul_smul, hk,
    ← smul_smul]
  module

/-- `R_t P_U R_t* = P_U` and `R_t P_{Y_θ} R_t* = P_{Y_{θ+t}}`. -/
private theorem circleRotation_conj_circlePair {W : ℕ} (hW : 1 ≤ W)
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hP : P ∈ isoBases W)
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) (θ t : ℝ) :
    circleRot P t * P * (circleRot P t)ᴴ = P ∧
      circleRot P t * (P + Matrix.vecMulVec (circleVec e f θ) (star (circleVec e f θ))) *
          (circleRot P t)ᴴ =
        P + Matrix.vecMulVec (circleVec e f (θ + t)) (star (circleVec e f (θ + t))) := by
  have hRP : circleRot P t * P = P := by
    obtain ⟨-, -, hJQ, -, hQP⟩ := quotProj_spec hW hP
    refine circleRotation_E_mul_fix hQP ?_ _ _
    rw [← hJQ, Matrix.mul_assoc, hQP, Matrix.mul_zero]
  have hPR : P * (circleRot P t)ᴴ = P := by
    have h := congrArg Matrix.conjTranspose hRP
    rwa [Matrix.conjTranspose_mul, hP.1.eq] at h
  have h1 : circleRot P t * P * (circleRot P t)ᴴ = P := by
    rw [Matrix.mul_assoc, hPR, hRP]
  refine ⟨h1, ?_⟩
  have hk : Complex.exp (-(((t / 2 : ℝ) : ℂ) * Complex.I)) *
      star (Complex.exp (-(((t / 2 : ℝ) : ℂ) * Complex.I))) = 1 := by
    rw [mul_comm]
    exact circleRotation_star_exp _ (by simp)
  rw [Matrix.mul_add, Matrix.add_mul, h1, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    ← Matrix.star_mulVec, circleRotation_mulVec_circleVec hef, star_smul, Matrix.smul_vecMulVec,
    Matrix.vecMulVec_smul, smul_smul, hk, one_smul]

/-- `R_t` is unitary and `J`-unitary, a one-parameter group with generator `K_U`, and fixes `U`
(proof of Lemma F.3 [lem:c-operators]). -/
theorem circleRot_spec {W : ℕ} (hW : 1 ≤ W) {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hP : P ∈ isoBases W) (s t : ℝ) :
    circleRot P t ∈ Matrix.unitaryGroup (Fin 2 × Fin W) ℂ ∧
      (circleRot P t)ᴴ * isoJ W * circleRot P t = isoJ W ∧
      circleRot P (s + t) = circleRot P s * circleRot P t ∧ circleRot P 0 = 1 ∧
      circleRot P t * P = P ∧ HasDerivAt (circleRot P) (circleGen P * circleRot P t) t := by
  obtain ⟨hQh, hQQ, hJQ, -, hQP⟩ := quotProj_spec hW hP
  have hJJ := isoJ_mul_isoJ W
  have hJh := isoJ_conjTranspose W
  have hQJP : quotProj P * isoJ W * P = 0 := by
    rw [← hJQ, Matrix.mul_assoc, hQP, Matrix.mul_zero]
  have hre : ∀ x : ℝ, ((x : ℂ) * Complex.I).re = 0 := fun x => by simp
  have hre' : ∀ x : ℝ, (-((x : ℂ) * Complex.I)).re = 0 := fun x => by simp
  have hu : (circleRot P t)ᴴ * circleRot P t = 1 := by
    rw [circleRotation_eq, circleRotation_E_conjTranspose hQh.eq hJh hJQ,
      circleRotation_E_mul hQQ hJJ hJQ, circleRotation_star_exp _ (hre' _),
      circleRotation_star_exp _ (hre _), circleRotation_E_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    exact hu
  · have hc : isoJ W * circleRot P t = circleRot P t * isoJ W := circleRotation_E_comm hJQ _ _
    rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · rw [circleRotation_eq, circleRotation_eq, circleRotation_eq,
      circleRotation_E_mul hQQ hJJ hJQ, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring
  · rw [circleRotation_eq]
    simp only [zero_div, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero]
    exact circleRotation_E_one
  · exact circleRotation_E_mul_fix hQP hQJP _ _
  · have ha := circleRotation_hasDerivAt_exp (-1) t
    have hb := circleRotation_hasDerivAt_exp 1 t
    simp only [one_mul, neg_mul] at ha hb
    have h := ((hasDerivAt_const t (1 - quotProj P)).add
      (ha.smul_const ((1 / 2 : ℂ) • (quotProj P * (1 + isoJ W))))).add
      (hb.smul_const ((1 / 2 : ℂ) • (quotProj P * (1 - isoJ W))))
    refine (show HasDerivAt (circleRot P) _ t from h).congr_deriv ?_
    have h2 : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X * isoJ W * isoJ W = X :=
      fun X => by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
    have h3 : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
        X * isoJ W * quotProj P = X * quotProj P * isoJ W := fun X => by
      rw [Matrix.mul_assoc, hJQ, ← Matrix.mul_assoc]
    rw [circleRotation_eq]
    unfold circleGen circleRotation_E
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
      ← Matrix.mul_assoc, hQQ, h2, h3]
    module

/-- `√2 K_U` lies in the algebra `𝔤` of (10.1) [up:eq:lie-algebra] and has Hilbert–Schmidt norm
one; `K_U` vanishes on `U` (proof of Lemma F.3 [lem:c-operators]). -/
theorem circleGen_mem_lieJ {W : ℕ} (hW : 1 ≤ W) {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hP : P ∈ isoBases W) :
    ((Real.sqrt 2 : ℝ) : ℂ) • circleGen P ∈ lieJ W ∧
      hsSq (((Real.sqrt 2 : ℝ) : ℂ) • circleGen P) = 1 ∧ circleGen P * P = 0 ∧
      P * circleGen P = 0 := by
  obtain ⟨hQh, hQQ, hJQ, hQtr, hQP⟩ := quotProj_spec hW hP
  obtain ⟨hPh, hPP, -, hPJ⟩ := hP
  have hJJ := isoJ_mul_isoJ W
  have hJh := isoJ_conjTranspose W
  have hPQ : P * quotProj P = 0 := by
    have h := congrArg Matrix.conjTranspose hQP
    rwa [Matrix.conjTranspose_mul, hQh.eq, hPh.eq, Matrix.conjTranspose_zero] at h
  have hQJP : quotProj P * isoJ W * P = 0 := by
    rw [← hJQ, Matrix.mul_assoc, hQP, Matrix.mul_zero]
  have hJQJ : isoJ W * quotProj P * isoJ W = quotProj P := by
    rw [hJQ, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hs : star ((Real.sqrt 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := Complex.conj_ofReal _
  have hI : star (-(Complex.I / 2)) = Complex.I / 2 := by simp; ring
  have h22 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hct : (((Real.sqrt 2 : ℝ) : ℂ) • circleGen P)ᴴ =
      ((Real.sqrt 2 : ℝ) : ℂ) • ((Complex.I / 2) • (isoJ W * quotProj P)) := by
    unfold circleGen
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hQh.eq,
      hJh, hs, hI]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hct]
    unfold circleGen
    simp only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hJQJ]
    module
  · unfold circleGen
    rw [Matrix.trace_smul, Matrix.trace_smul, circleRotation_trace_QJ hPP hPJ, smul_zero,
      smul_zero]
  · rw [circleRotation_hsSq, hct]
    unfold circleGen
    have h4 : isoJ W * quotProj P * (quotProj P * isoJ W) = quotProj P := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (isoJ W), hQQ, hJQJ]
    simp only [Matrix.smul_mul, Matrix.mul_smul, h4, Matrix.trace_smul, hQtr, smul_eq_mul]
    have : ((Real.sqrt 2 : ℝ) : ℂ) * (-(Complex.I / 2) * (((Real.sqrt 2 : ℝ) : ℂ) *
        (Complex.I / 2 * 2))) = 1 := by
      linear_combination (-(Complex.I ^ 2) / 2) * h22 - Complex.I_sq
    rw [this, Complex.one_re]
  · unfold circleGen
    rw [Matrix.smul_mul, hQJP, smul_zero]
  · unfold circleGen
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, hPQ, Matrix.zero_mul, smul_zero]

/-- `R_t` moves `Y_θ` of (F.1) [cc:eq:circle] to `Y_{θ+t}`, for every circle basis. -/
theorem flagAct_circleRot_circlePair {W : ℕ} (hW : 1 ≤ W) (x : IsoFlag W)
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis x.1.1 e f) (θ t : ℝ) :
    ((flagAct (circleRot x.1.1 t)
        ⟨circlePair x.1.1 e f θ, circlePair_mem_isoFlags x.2.1 hef θ⟩ : IsoFlag W) :
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) =
      circlePair x.1.1 e f (θ + t) := by
  have hP := x.2.1
  have spec := circleRot_spec hW hP 0 t
  have hmem := circlePair_mem_isoFlags hP hef θ
  have hYY : (x.1.1 + Matrix.vecMulVec (circleVec e f θ) (star (circleVec e f θ))) *
      (x.1.1 + Matrix.vecMulVec (circleVec e f θ) (star (circleVec e f θ))) =
      x.1.1 + Matrix.vecMulVec (circleVec e f θ) (star (circleVec e f θ)) := hmem.2.2.1
  obtain ⟨h1, h2⟩ := circleRotation_conj_circlePair hW hP hef θ t
  rw [flagAct_coe spec.2.1]
  change (flagProj (circleRot x.1.1 t) x.1.1, flagProj (circleRot x.1.1 t)
    (x.1.1 + Matrix.vecMulVec (circleVec e f θ) (star (circleVec e f θ)))) = _
  rw [flagProj_of_mem_unitaryGroup spec.1 hP.2.1, flagProj_of_mem_unitaryGroup spec.1 hYY, h1,
    h2]
  rfl

/-- The angular measure `m_U` (Section 8.3 [sec:upper-inputs]) is the law of `R_t Y` for `t`
uniform on `(0, 2π]`, for every flag `(U, Y)`. -/
theorem circleMeasure_eq_map_circleRot {W : ℕ} (hW : 1 ≤ W) (x : IsoFlag W) :
    circleMeasure x = Measure.map (fun t => flagAct (circleRot x.1.1 t) x) angleMeas := by
  obtain ⟨e, f, hef⟩ := exists_isCircleBasis hW x.2.1
  obtain ⟨θ₀, hθ₀⟩ := exists_circlePair_eq x hef
  set c : ℂ := Complex.exp ((θ₀ : ℂ) * Complex.I) with hc
  have hcc : star c * c = 1 := circleRotation_star_exp _ (by simp)
  have hef' : IsCircleBasis x.1.1 e (c • f) := by
    obtain ⟨he1, hf1, hJe, hJf, hPe, hPf⟩ := hef
    refine ⟨he1, ?_, hJe, ?_, hPe, ?_⟩
    · rw [star_smul, smul_dotProduct, dotProduct_smul, hf1, smul_eq_mul, smul_eq_mul, mul_one,
        hcc]
    · rw [Matrix.mulVec_smul, hJf, smul_neg]
    · rw [Matrix.mulVec_smul, hPf, smul_zero]
  have hpair : ∀ t : ℝ, circlePair x.1.1 e (c • f) t = circlePair x.1.1 e f (θ₀ + t) := by
    intro t
    have hk : Complex.exp ((t : ℂ) * Complex.I) * c =
        Complex.exp (((θ₀ + t : ℝ) : ℂ) * Complex.I) := by
      rw [hc, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    unfold circlePair circleVec
    rw [smul_smul, hk]
  have hx : x = ⟨circlePair x.1.1 e f θ₀, circlePair_mem_isoFlags x.2.1 hef θ₀⟩ :=
    Subtype.ext hθ₀
  rw [circleMeasure_eq_map x hef']
  congr 1
  funext t
  apply Subtype.ext
  calc circlePair x.1.1 e (c • f) t = circlePair x.1.1 e f (θ₀ + t) := hpair t
    _ = ((flagAct (circleRot x.1.1 t)
          ⟨circlePair x.1.1 e f θ₀, circlePair_mem_isoFlags x.2.1 hef θ₀⟩ : IsoFlag W) :
          Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
            Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :=
      (flagAct_circleRot_circlePair hW x hef θ₀ t).symm
    _ = ((flagAct (circleRot x.1.1 t) x : IsoFlag W) :
          Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
            Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :=
      congrArg (fun y => ((flagAct (circleRot x.1.1 t) y : IsoFlag W) :
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))
        hx.symm

end LSBA
