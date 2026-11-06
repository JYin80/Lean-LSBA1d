import LSBA.Transfer.FlagAction

/-!
# The circle of isotropic extensions

For a `(W−1)`-dimensional isotropic `U`, the space `H_U = (U + JU)^⊥` of signature (1,1), a circle
basis `e, f` (`Je = e`, `Jf = −f`), and the circle of maximal isotropic extensions `Y_θ = U ⊕ ℂ(e +
e^{iθ}f)/√2` (Lemma F.1 [cc:lem:quotient], (F.1) [cc:eq:circle]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `1 - P_U - J P_U J`, the orthogonal projection onto `H_U = (U + JU)^⊥` of Lemma F.1
[cc:lem:quotient]. -/
def quotProj {W : ℕ} (P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  1 - P - isoJ W * P * isoJ W

/-- Unit vectors `e, f ∈ H_U` with `J e = e` and `J f = -f` (Lemma F.1 [cc:lem:quotient]). -/
def IsCircleBasis {W : ℕ} (P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (e f : Fin 2 × Fin W → ℂ) : Prop :=
  star e ⬝ᵥ e = 1 ∧ star f ⬝ᵥ f = 1 ∧ isoJ W *ᵥ e = e ∧ isoJ W *ᵥ f = -f ∧ P *ᵥ e = 0 ∧
    P *ᵥ f = 0

/-- A fixed choice of `(e, f)` (zero if there is none). -/
def circleBasis {W : ℕ} (P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (Fin 2 × Fin W → ℂ) × (Fin 2 × Fin W → ℂ) :=
  if h : ∃ ef : (Fin 2 × Fin W → ℂ) × (Fin 2 × Fin W → ℂ), IsCircleBasis P ef.1 ef.2 then
    h.choose else 0

/-- `v_θ = (e + e^{iθ} f)/√2` of (F.1) [cc:eq:circle]. -/
def circleVec {W : ℕ} (e f : Fin 2 × Fin W → ℂ) (θ : ℝ) : Fin 2 × Fin W → ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (e + Complex.exp ((θ : ℂ) * Complex.I) • f)

/-- The pair `(P_U, P_U + v_θ v_θ*)`, i.e. the extension `Y_θ = U ⊕ ℂ v_θ` of (F.1)
[cc:eq:circle]. -/
def circlePair {W : ℕ} (P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (e f : Fin 2 × Fin W → ℂ)
    (θ : ℝ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (P, P + Matrix.vecMulVec (circleVec e f θ) (star (circleVec e f θ)))

/-- `1 - P - R` is idempotent for idempotents `P`, `R` with `P R = 0 = R P` (Lemma F.1
[cc:lem:quotient]). -/
private theorem circle_sub_idem {ι : Type*} [Fintype ι] [DecidableEq ι] {P R : Matrix ι ι ℂ}
    (hPP : P * P = P) (hRR : R * R = R) (hPR : P * R = 0) (hRP : R * P = 0) :
    (1 - P - R) * (1 - P - R) = 1 - P - R := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP, hRR, hPR, hRP]
  abel

/-- `P (J P J) = 0` for `P J P = 0`. -/
private theorem circle_PJPJ {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hPJ : P * isoJ W * P = 0) : P * (isoJ W * P * isoJ W) = 0 := by
  calc P * (isoJ W * P * isoJ W) = (P * isoJ W * P) * isoJ W := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hPJ, Matrix.zero_mul]

/-- `(J P J) P = 0` for `P J P = 0`. -/
private theorem circle_JPJP {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hPJ : P * isoJ W * P = 0) : isoJ W * P * isoJ W * P = 0 := by
  calc isoJ W * P * isoJ W * P = isoJ W * (P * isoJ W * P) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hPJ, Matrix.mul_zero]

/-- `J P J` is idempotent for an idempotent `P`. -/
private theorem circle_JPJ_idem {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hPP : P * P = P) : isoJ W * P * isoJ W * (isoJ W * P * isoJ W) = isoJ W * P * isoJ W := by
  calc isoJ W * P * isoJ W * (isoJ W * P * isoJ W)
      = isoJ W * P * (isoJ W * isoJ W) * P * isoJ W := by simp only [Matrix.mul_assoc]
    _ = isoJ W * P * isoJ W := by rw [isoJ_mul_isoJ, Matrix.mul_one, Matrix.mul_assoc (isoJ W) P P, hPP]

/-- `tr (J P J) = tr P`. -/
private theorem circle_trace_JPJ {W : ℕ} (P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (isoJ W * P * isoJ W).trace = P.trace := by
  calc (isoJ W * P * isoJ W).trace = (isoJ W * (isoJ W * P)).trace := Matrix.trace_mul_comm _ _
    _ = P.trace := by rw [← Matrix.mul_assoc, isoJ_mul_isoJ, Matrix.one_mul]

/-- `#(Fin 2 × Fin W) = 2 W` in `ℂ`. -/
private theorem circle_card (W : ℕ) : (Fintype.card (Fin 2 × Fin W) : ℂ) = 2 * W := by
  simp [Fintype.card_prod]

/-- Lemma F.1 [cc:lem:quotient]: `H_U` is `J`-invariant, two-dimensional and orthogonal to `U`. -/
theorem quotProj_spec {W : ℕ} (hW : 1 ≤ W) {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hP : P ∈ isoBases W) :
    (quotProj P).IsHermitian ∧ quotProj P * quotProj P = quotProj P ∧
      isoJ W * quotProj P = quotProj P * isoJ W ∧ (quotProj P).trace = 2 ∧ quotProj P * P = 0 := by
  obtain ⟨hPh, hPP, hPtr, hPJ⟩ := hP
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Matrix.IsHermitian quotProj
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, isoJ_conjTranspose, hPh.eq]
    simp only [Matrix.mul_assoc]
  · exact circle_sub_idem hPP (circle_JPJ_idem hPP) (circle_PJPJ hPJ) (circle_JPJP hPJ)
  · unfold quotProj
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc,
      isoJ_mul_isoJ]
    simp only [Matrix.mul_assoc, isoJ_mul_isoJ, Matrix.mul_one]
    abel
  · unfold quotProj
    rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_one, circle_trace_JPJ, hPtr,
      circle_card, Nat.cast_sub hW]
    push_cast
    ring
  · unfold quotProj
    simp only [Matrix.sub_mul, Matrix.one_mul, hPP, circle_JPJP hPJ]
    abel

/-- A nonzero idempotent matrix fixes a unit vector. -/
private theorem circle_exists_unit_fixed {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hAA : A * A = A) (hA0 : A ≠ 0) :
    ∃ e : ι → ℂ, star e ⬝ᵥ e = 1 ∧ A *ᵥ e = e := by
  obtain ⟨j, hj⟩ : ∃ j, A *ᵥ Pi.single j 1 ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hA0
    ext i j
    have := congrFun (h j) i
    simpa [Matrix.mulVec_single_one] using this
  set c := A *ᵥ Pi.single j 1 with hc
  have hAc : A *ᵥ c = c := by rw [hc, Matrix.mulVec_mulVec, hAA]
  set s : ℝ := ∑ i, Complex.normSq (c i) with hs
  have hspos : 0 < s := by
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hj (funext h)
    exact Finset.sum_pos' (fun k _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  have hcc : star c ⬝ᵥ c = (s : ℂ) := by
    simp only [dotProduct, hs, Complex.ofReal_sum, Pi.star_apply, Complex.star_def]
    exact Finset.sum_congr rfl fun i _ => (Complex.normSq_eq_conj_mul_self).symm
  refine ⟨(((Real.sqrt s)⁻¹ : ℝ) : ℂ) • c, ?_, ?_⟩
  · simp only [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal]
    rw [hcc]
    have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hspos.le
    have hne : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hspos).ne'
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    field_simp
    rw [sq]
    exact hsq.symm
  · rw [Matrix.mulVec_smul, hAc]

/-- If `Q² = Q`, `Q K = K = K Q` and `K² = Q`, then `(Q + ε K) / 2` is idempotent for
`ε² = 1`. -/
private theorem circle_half_idem {ι : Type*} [Fintype ι] {Q K : Matrix ι ι ℂ}
    {ε : ℂ} (hε : ε * ε = 1) (hQQ : Q * Q = Q) (hQK : Q * K = K) (hKQ : K * Q = K)
    (hKK : K * K = Q) :
    ((1 / 2 : ℂ) • (Q + ε • K)) * ((1 / 2 : ℂ) • (Q + ε • K)) = (1 / 2 : ℂ) • (Q + ε • K) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, hQQ, hQK, hKQ,
    hKK, smul_smul]
  match_scalars <;> first | ring1 | linear_combination (1 / 4 : ℂ) * hε

/-- `P (1 - P - J P J) = 0` for an isotropic projection `P`. -/
private theorem circle_PQ {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hPP : P * P = P) (hPJ : P * isoJ W * P = 0) : P * quotProj P = 0 := by
  unfold quotProj
  simp only [Matrix.mul_sub, Matrix.mul_one, hPP, circle_PJPJ hPJ]
  abel

/-- `tr J = 0`. -/
private theorem circle_trace_isoJ (W : ℕ) : (isoJ W).trace = 0 := by
  unfold isoJ
  rw [Matrix.trace_kronecker]
  simp [Matrix.trace, Fin.sum_univ_two]

/-- `tr (P J) = 0` for an isotropic projection `P`. -/
private theorem circle_trace_PJ {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hPP : P * P = P) (hPJ : P * isoJ W * P = 0) : (P * isoJ W).trace = 0 := by
  calc (P * isoJ W).trace = (P * (P * isoJ W)).trace := by rw [← Matrix.mul_assoc, hPP]
    _ = (P * isoJ W * P).trace := Matrix.trace_mul_comm _ _
    _ = 0 := by rw [hPJ, Matrix.trace_zero]

/-- `tr (Q J) = 0` for `Q = 1 - P - J P J`, `P` an isotropic projection. -/
private theorem circle_trace_QJ {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hPP : P * P = P) (hPJ : P * isoJ W * P = 0) : (quotProj P * isoJ W).trace = 0 := by
  have h : quotProj P * isoJ W = isoJ W - P * isoJ W - isoJ W * P := by
    unfold quotProj
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, isoJ_mul_isoJ, Matrix.mul_one]
  rw [h, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm (isoJ W) P,
    circle_trace_isoJ, circle_trace_PJ hPP hPJ]
  simp

/-- For `ε = ±1` there is a unit vector `e` in `H_U` with `J e = ε e` (Lemma F.1
[cc:lem:quotient]). -/
private theorem circle_exists_eigvec {W : ℕ} (hW : 1 ≤ W)
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hP : P ∈ isoBases W) {ε : ℂ}
    (hε : ε * ε = 1) :
    ∃ e : Fin 2 × Fin W → ℂ, star e ⬝ᵥ e = 1 ∧ isoJ W *ᵥ e = ε • e ∧ P *ᵥ e = 0 := by
  obtain ⟨-, hQQ, hJQ, hQtr, -⟩ := quotProj_spec hW hP
  obtain ⟨-, hPP, -, hPJ⟩ := hP
  have hPQ := circle_PQ hPP hPJ
  have hQJtr := circle_trace_QJ hPP hPJ
  set Q := quotProj P with hQ
  set J := isoJ W with hJ
  have hJJ : J * J = 1 := isoJ_mul_isoJ W
  have hQK : Q * (Q * J) = Q * J := by rw [← Matrix.mul_assoc, hQQ]
  have hKQ : Q * J * Q = Q * J := by rw [Matrix.mul_assoc, hJQ, hQK]
  have hKK : Q * J * (Q * J) = Q := by
    rw [← Matrix.mul_assoc, hKQ, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hJQJ : J * (Q * J) = Q := by
    rw [← Matrix.mul_assoc, hJQ, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  set A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := (1 / 2 : ℂ) • (Q + ε • (Q * J)) with hA
  have hAA : A * A = A := circle_half_idem hε hQQ hQK hKQ hKK
  have hAtr : A.trace = 1 := by
    rw [hA, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, hQtr, hQJtr]
    simp
  have hA0 : A ≠ 0 := fun h => by rw [h, Matrix.trace_zero] at hAtr; exact zero_ne_one hAtr
  have hJA : J * A = ε • A := by
    rw [hA, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_smul, hJQ, hJQJ]
    simp only [smul_add, smul_smul]
    match_scalars <;> first | ring1 | linear_combination (-1 / 2 : ℂ) * hε
  have hPA : P * A = 0 := by
    rw [hA, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_smul, hPQ, ← Matrix.mul_assoc, hPQ]
    simp
  obtain ⟨e, he1, hAe⟩ := circle_exists_unit_fixed hAA hA0
  refine ⟨e, he1, ?_, ?_⟩
  · calc J *ᵥ e = J *ᵥ (A *ᵥ e) := by rw [hAe]
      _ = (J * A) *ᵥ e := by rw [Matrix.mulVec_mulVec]
      _ = ε • e := by rw [hJA, Matrix.smul_mulVec, hAe]
  · calc P *ᵥ e = P *ᵥ (A *ᵥ e) := by rw [hAe]
      _ = (P * A) *ᵥ e := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hPA, Matrix.zero_mulVec]

/-- Lemma F.1 [cc:lem:quotient]: `H_U` has signature `(1, 1)`. -/
theorem exists_isCircleBasis {W : ℕ} (hW : 1 ≤ W) {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hP : P ∈ isoBases W) : ∃ e f : Fin 2 × Fin W → ℂ, IsCircleBasis P e f := by
  obtain ⟨e, he1, heJ, heP⟩ := circle_exists_eigvec hW hP (ε := 1) (by norm_num)
  obtain ⟨f, hf1, hfJ, hfP⟩ := circle_exists_eigvec hW hP (ε := -1) (by norm_num)
  exact ⟨e, f, he1, hf1, by simpa using heJ, by simpa using hfJ, heP, hfP⟩

/-- A circle basis exists only for `1 ≤ W`. -/
private theorem circle_one_le {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) : 1 ≤ W := by
  by_contra h
  have hW : W = 0 := by omega
  subst hW
  have := hef.1
  simp [dotProduct] at this

/-- `e* f = 0` for a circle basis. -/
private theorem circle_star_dot {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) : star e ⬝ᵥ f = 0 := by
  obtain ⟨-, -, heJ, hfJ, -, -⟩ := hef
  have h1 : star e ⬝ᵥ (isoJ W *ᵥ f) = star e ⬝ᵥ f := by
    rw [Matrix.dotProduct_mulVec]
    have : star e ᵥ* isoJ W = star e := by
      conv_rhs => rw [← heJ]
      rw [Matrix.star_mulVec, isoJ_conjTranspose]
    rw [this]
  rw [hfJ, dotProduct_neg] at h1
  have h2 : (2 : ℂ) * (star e ⬝ᵥ f) = 0 := by linear_combination -h1
  simpa using h2

/-- `f* e = 0` for a circle basis. -/
private theorem circle_star_dot' {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) : star f ⬝ᵥ e = 0 := by
  have h := circle_star_dot hef
  have : star f ⬝ᵥ e = star (star e ⬝ᵥ f) := by
    rw [← Matrix.star_dotProduct_star, star_star]
  rw [this, h, star_zero]

/-- For `2 |c|² = 1` and `|w| = 1`, the vector `c (e + w f)` is a unit vector `v` with
`v* J v = 0`. -/
private theorem circle_dot_gen {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) {c w : ℂ} (hc : star c * c * 2 = 1)
    (hw : star w * w = 1) :
    star (c • (e + w • f)) ⬝ᵥ (c • (e + w • f)) = 1 ∧
      star (c • (e + w • f)) ⬝ᵥ (isoJ W *ᵥ (c • (e + w • f))) = 0 := by
  have h0 := circle_star_dot hef
  have h0' := circle_star_dot' hef
  obtain ⟨he, hf, heJ, hfJ, -, -⟩ := hef
  constructor
  · simp only [star_smul, star_add, smul_dotProduct, dotProduct_smul, add_dotProduct,
      dotProduct_add, smul_eq_mul, he, hf, h0, h0']
    linear_combination hc + (star c * c) * hw
  · simp only [Matrix.mulVec_smul, Matrix.mulVec_add, heJ, hfJ, star_smul, star_add,
      smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add, smul_eq_mul, he, hf, h0,
      h0', dotProduct_neg]
    linear_combination (-(star c * c)) * hw

/-- `|e^{iθ}| = 1`. -/
private theorem circle_w_norm (θ : ℝ) :
    star (Complex.exp ((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]
  simp

/-- `2 |1/√2|² = 1`. -/
private theorem circle_c_norm :
    star (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * 2 = 1 := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_ofNat,
    ← Complex.ofReal_mul, ← Complex.ofReal_one]
  congr 1
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  rw [sq]
  exact h.symm

/-- `v_θ` is a unit vector with `P v_θ = 0`, `v_θ* J v_θ = 0` and `P J v_θ = 0`. -/
private theorem circle_vec_spec {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) (θ : ℝ) :
    star (circleVec e f θ) ⬝ᵥ circleVec e f θ = 1 ∧
      star (circleVec e f θ) ⬝ᵥ (isoJ W *ᵥ circleVec e f θ) = 0 ∧ P *ᵥ circleVec e f θ = 0 ∧
      P *ᵥ (isoJ W *ᵥ circleVec e f θ) = 0 := by
  have hd := circle_dot_gen hef circle_c_norm (circle_w_norm θ)
  obtain ⟨-, -, heJ, hfJ, heP, hfP⟩ := hef
  refine ⟨hd.1, hd.2, ?_, ?_⟩
  · unfold circleVec
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, heP, hfP]
    simp
  · unfold circleVec
    simp [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_neg, heJ, hfJ, heP, hfP]

/-- `(P, P + v v*)` is a flag for a unit vector `v` with `P v = 0`, `v* J v = 0` and
`P J v = 0`. -/
private theorem circle_mem_of_vec {W : ℕ} (hW : 1 ≤ W)
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hP : P ∈ isoBases W)
    {v : Fin 2 × Fin W → ℂ} (h1 : star v ⬝ᵥ v = 1) (hPv : P *ᵥ v = 0)
    (hJv : star v ⬝ᵥ (isoJ W *ᵥ v) = 0) (hPJv : P *ᵥ (isoJ W *ᵥ v) = 0) :
    (P, P + Matrix.vecMulVec v (star v)) ∈ isoFlags W := by
  refine ⟨hP, ?_⟩
  obtain ⟨hPh, hPP, hPtr, hPJ⟩ := hP
  set V := Matrix.vecMulVec v (star v) with hV
  have hVh : Vᴴ = V := by rw [hV, Matrix.conjTranspose_vecMulVec, star_star]
  have hVV : V * V = V := by rw [hV, Matrix.vecMulVec_mul_vecMulVec, h1, one_smul]
  have hVtr : V.trace = 1 := by rw [hV, Matrix.trace_vecMulVec, dotProduct_comm, h1]
  have hPV : P * V = 0 := by rw [hV, Matrix.mul_vecMulVec, hPv, Matrix.zero_vecMulVec]
  have hvP : star v ᵥ* P = 0 := by
    have := Matrix.star_mulVec P v
    rw [hPh.eq, hPv, star_zero] at this
    exact this.symm
  have hVP : V * P = 0 := by rw [hV, Matrix.vecMulVec_mul, hvP, Matrix.vecMulVec_zero]
  have hPJV : P * isoJ W * V = 0 := by
    rw [hV, Matrix.mul_vecMulVec, ← Matrix.mulVec_mulVec, hPJv, Matrix.zero_vecMulVec]
  have hvJP : (star v ᵥ* isoJ W) ᵥ* P = 0 := by
    have h : star v ᵥ* (isoJ W * P) = star ((P * isoJ W) *ᵥ v) := by
      rw [Matrix.star_mulVec, Matrix.conjTranspose_mul, hPh.eq, isoJ_conjTranspose]
    rw [Matrix.vecMul_vecMul, h, ← Matrix.mulVec_mulVec, hPJv, star_zero]
  have hVJP : V * isoJ W * P = 0 := by
    rw [hV, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hvJP, Matrix.vecMulVec_zero]
  have hVJV : V * isoJ W * V = 0 := by
    rw [hV, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec, ← Matrix.dotProduct_mulVec, hJv,
      zero_smul, Matrix.vecMulVec_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_add, hPh.eq, hVh]
  · simp only [Matrix.add_mul, Matrix.mul_add, hPP, hPV, hVP, hVV, zero_add, add_zero]
  · rw [Matrix.trace_add, hVtr, hPtr, Nat.cast_sub hW]
    push_cast
    ring
  · simp only [Matrix.add_mul, hPP, hVP, add_zero]
  · simp only [Matrix.add_mul, Matrix.mul_add, hPJ, hPJV, hVJP, hVJV, add_zero]

/-- Each `Y_θ = U ⊕ ℂ v_θ` of (F.1) [cc:eq:circle] is a flag. -/
theorem circlePair_mem_isoFlags {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hP : P ∈ isoBases W) {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) (θ : ℝ) :
    circlePair P e f θ ∈ isoFlags W := by
  obtain ⟨h1, hJv, hPv, hPJv⟩ := circle_vec_spec hef θ
  exact circle_mem_of_vec (circle_one_le hef) hP h1 hPv hJv hPJv

open scoped ComplexOrder in
/-- Two Hermitian idempotents `B`, `B'` with `B B' = B'` and equal traces coincide. -/
private theorem circle_eq_of_trace {ι : Type*} [Fintype ι] {B B' : Matrix ι ι ℂ}
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

/-- `quotProj P` fixes `e` and `f`. -/
private theorem circle_Q_mulVec {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) :
    quotProj P *ᵥ e = e ∧ quotProj P *ᵥ f = f := by
  obtain ⟨-, -, heJ, hfJ, heP, hfP⟩ := hef
  unfold quotProj
  constructor
  · rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, heJ, heP]
    simp
  · rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hfJ, Matrix.mulVec_neg, hfP]
    simp

/-- `quotProj P = e e* + f f*` for a circle basis (Lemma F.1 [cc:lem:quotient]). -/
private theorem circle_quotProj_eq {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hP : P ∈ isoBases W) {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) :
    quotProj P = Matrix.vecMulVec e (star e) + Matrix.vecMulVec f (star f) := by
  have hW := circle_one_le hef
  obtain ⟨hQh, hQQ, -, hQtr, -⟩ := quotProj_spec hW hP
  obtain ⟨hQe, hQf⟩ := circle_Q_mulVec hef
  have h0 := circle_star_dot hef
  have h0' := circle_star_dot' hef
  obtain ⟨he, hf, -⟩ := hef
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
  refine circle_eq_of_trace hQh hQQ ?_ ?_ ?_ ?_
  · rw [Matrix.conjTranspose_add, Matrix.conjTranspose_vecMulVec, Matrix.conjTranspose_vecMulVec,
      star_star, star_star]
  · simp only [Matrix.add_mul, Matrix.mul_add, hEE, hEF, hFE, hFF, zero_add, add_zero]
  · rw [Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hQe, hQf]
  · rw [Matrix.trace_add, Matrix.trace_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm e,
      dotProduct_comm f, he, hf, hQtr]
    norm_num

/-- Lemma F.1 [cc:lem:quotient]: every extension `Y ⊃ U` is some `Y_θ`, for every choice of
`(e, f)`. -/
theorem exists_circlePair_eq {W : ℕ} (x : IsoFlag W) {e f : Fin 2 × Fin W → ℂ}
    (hef : IsCircleBasis x.1.1 e f) : ∃ θ : ℝ, x.1 = circlePair x.1.1 e f θ := by
  obtain ⟨⟨P, Y⟩, hx⟩ := x
  obtain ⟨⟨hPh, hPP, hPtr, hPJ⟩, hYh, hYY, hYtr, hYP, hYJ⟩ := hx
  have hP : P ∈ isoBases W := ⟨hPh, hPP, hPtr, hPJ⟩
  dsimp only at hef ⊢
  have hW := circle_one_le hef
  set J := isoJ W with hJ
  have hPY : P * Y = P := by
    have := congrArg Matrix.conjTranspose hYP
    rwa [Matrix.conjTranspose_mul, hPh.eq, hYh.eq] at this
  have hPJY : P * J * Y = 0 := by
    calc P * J * Y = P * Y * J * Y := by rw [hPY]
      _ = P * (Y * J * Y) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hYJ, Matrix.mul_zero]
  have hYJP : Y * J * P = 0 := by
    calc Y * J * P = Y * J * (Y * P) := by rw [hYP]
      _ = (Y * J * Y) * P := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hYJ, Matrix.zero_mul]
  set N := Y - P with hN
  have hNh : Nᴴ = N := by rw [hN, Matrix.conjTranspose_sub, hYh.eq, hPh.eq]
  have hNN : N * N = N := by
    rw [hN]
    simp only [Matrix.sub_mul, Matrix.mul_sub, hYY, hYP, hPY, hPP]
    abel
  have hNtr : N.trace = 1 := by
    rw [hN, Matrix.trace_sub, hYtr, hPtr, Nat.cast_sub hW]
    push_cast
    ring
  have hPN : P * N = 0 := by
    rw [hN, Matrix.mul_sub, hPY, hPP, sub_self]
  have hPJN : P * J * N = 0 := by
    rw [hN, Matrix.mul_sub, hPJY, hPJ, sub_zero]
  have hNJN : N * J * N = 0 := by
    rw [hN]
    simp only [Matrix.sub_mul, Matrix.mul_sub, hYJ, hYJP, hPJY, hPJ]
    simp
  have hN0 : N ≠ 0 := fun h => by rw [h, Matrix.trace_zero] at hNtr; exact zero_ne_one hNtr
  obtain ⟨w, hw1, hNw⟩ := circle_exists_unit_fixed hNN hN0
  have hNV : N = Matrix.vecMulVec w (star w) := by
    refine circle_eq_of_trace hNh hNN ?_ ?_ ?_ ?_
    · rw [Matrix.conjTranspose_vecMulVec, star_star]
    · rw [Matrix.vecMulVec_mul_vecMulVec, hw1, one_smul]
    · rw [Matrix.mul_vecMulVec, hNw]
    · rw [Matrix.trace_vecMulVec, dotProduct_comm, hw1, hNtr]
  have hPw : P *ᵥ w = 0 := by
    calc P *ᵥ w = P *ᵥ (N *ᵥ w) := by rw [hNw]
      _ = (P * N) *ᵥ w := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hPN, Matrix.zero_mulVec]
  have hPJw : P *ᵥ (J *ᵥ w) = 0 := by
    calc P *ᵥ (J *ᵥ w) = P *ᵥ (J *ᵥ (N *ᵥ w)) := by rw [hNw]
      _ = (P * J * N) *ᵥ w := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = 0 := by rw [hPJN, Matrix.zero_mulVec]
  have hQw : quotProj P *ᵥ w = w := by
    unfold quotProj
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hPJw, hPw]
    simp
  have hwexp : w = (star e ⬝ᵥ w) • e + (star f ⬝ᵥ w) • f := by
    have h := congrArg (fun M => M *ᵥ w) (circle_quotProj_eq hP hef)
    simp only [hQw, Matrix.add_mulVec, Matrix.vecMulVec_mulVec] at h
    simpa using h
  obtain ⟨α, hα⟩ : ∃ α : ℂ, α = star e ⬝ᵥ w := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, β = star f ⬝ᵥ w := ⟨_, rfl⟩
  rw [← hα, ← hβ] at hwexp
  have hα' : star w ⬝ᵥ e = star α := by
    rw [hα, ← Matrix.star_dotProduct_star, star_star]
  have hβ' : star w ⬝ᵥ f = star β := by
    rw [hβ, ← Matrix.star_dotProduct_star, star_star]
  obtain ⟨-, -, heJ, hfJ, -, -⟩ := hef
  have hsum : α * star α + β * star β = 1 := by
    have h : star w ⬝ᵥ w = star w ⬝ᵥ (α • e + β • f) := by rw [← hwexp]
    rw [hw1, dotProduct_add, dotProduct_smul, dotProduct_smul, hα', hβ', smul_eq_mul,
      smul_eq_mul] at h
    exact h.symm
  have hJw0 : star w ⬝ᵥ (J *ᵥ w) = 0 := by
    calc star w ⬝ᵥ (J *ᵥ w) = star (N *ᵥ w) ⬝ᵥ (J *ᵥ (N *ᵥ w)) := by rw [hNw]
      _ = (star w ᵥ* Nᴴ) ⬝ᵥ (J *ᵥ (N *ᵥ w)) := by rw [Matrix.star_mulVec]
      _ = star w ⬝ᵥ (N *ᵥ (J *ᵥ (N *ᵥ w))) := by rw [hNh, ← Matrix.dotProduct_mulVec]
      _ = star w ⬝ᵥ ((N * J * N) *ᵥ w) := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = 0 := by rw [hNJN, Matrix.zero_mulVec, dotProduct_zero]
  have hJw : J *ᵥ w = α • e + β • (-f) := by
    conv_lhs => rw [hwexp]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, heJ, hfJ]
  rw [hJw, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_neg, hα', hβ',
    smul_eq_mul, smul_eq_mul] at hJw0
  have hα2 : α * star α = 1 / 2 := by linear_combination (1 / 2 : ℂ) * hsum + (1 / 2 : ℂ) * hJw0
  have hβ2 : β * star β = 1 / 2 := by linear_combination (1 / 2 : ℂ) * hsum - (1 / 2 : ℂ) * hJw0
  have hα0 : α ≠ 0 := fun h => by rw [h, zero_mul] at hα2; norm_num at hα2
  have hnα : ‖α‖ ^ 2 = 1 / 2 := by
    rw [Complex.sq_norm]
    have h : ((Complex.normSq α : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, mul_comm, hα2]; push_cast; ring
    exact_mod_cast h
  have hnβ : ‖β‖ ^ 2 = 1 / 2 := by
    rw [Complex.sq_norm]
    have h : ((Complex.normSq β : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, mul_comm, hβ2]; push_cast; ring
    exact_mod_cast h
  have hnorm : ‖β‖ = ‖α‖ :=
    (sq_eq_sq₀ (norm_nonneg β) (norm_nonneg α)).mp (by rw [hnα, hnβ])
  have hu1 : ‖β / α‖ = 1 := by
    rw [norm_div, hnorm, div_self (norm_ne_zero_iff.mpr hα0)]
  have hexp : Complex.exp ((Complex.arg (β / α) : ℂ) * Complex.I) = β / α := by
    have := Complex.norm_mul_exp_arg_mul_I (β / α)
    rwa [hu1, Complex.ofReal_one, one_mul] at this
  refine ⟨Complex.arg (β / α), ?_⟩
  have hsc : ((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    exact mul_inv_cancel₀ (by positivity)
  have hwv : w = (α * ((Real.sqrt 2 : ℝ) : ℂ)) • circleVec e f (Complex.arg (β / α)) := by
    have hβu : β = α * (β / α) := by field_simp
    unfold circleVec
    rw [hexp]
    generalize (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = c at hsc ⊢
    generalize ((Real.sqrt 2 : ℝ) : ℂ) = s at hsc ⊢
    conv_lhs => rw [hwexp, hβu]
    simp only [smul_add, smul_smul]
    match_scalars
    · linear_combination (-α) * hsc
    · linear_combination (-(α * (β / α))) * hsc
  have hk : (α * ((Real.sqrt 2 : ℝ) : ℂ)) * star (α * ((Real.sqrt 2 : ℝ) : ℂ)) = 1 := by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
      norm_num
    calc α * ((Real.sqrt 2 : ℝ) : ℂ) * (star α * ((Real.sqrt 2 : ℝ) : ℂ))
        = (α * star α) * (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)) := by ring
      _ = 1 := by rw [hα2, h2]; norm_num
  have hNV' : N = Matrix.vecMulVec (circleVec e f (Complex.arg (β / α)))
      (star (circleVec e f (Complex.arg (β / α)))) := by
    rw [hNV, hwv, Matrix.smul_vecMulVec, star_smul, Matrix.vecMulVec_smul, smul_smul, hk,
      one_smul]
  change (P, Y) = (P, P + Matrix.vecMulVec (circleVec e f (Complex.arg (β / α)))
      (star (circleVec e f (Complex.arg (β / α)))))
  refine Prod.ext rfl ?_
  rw [← hNV', hN, add_sub_cancel]

end LSBA
