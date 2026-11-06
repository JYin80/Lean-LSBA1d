import LSBA.Upper.CircleRotation
import LSBA.Transfer.VolCocycle

/-!
# The angular speed of the transfer action

The infinitesimal form of the exact angular Jacobian (8.36) [cc:eq:jac]: for `J`-unitary `T`,
moving the source flag along its circle at unit speed (`T ↦ T + s T K_U`) moves the image
projection `P_{TY}` along the circle `𝒞_{TU}` at speed `e^{-2c(T; U, Y)}`, with `c` the cocycle
(8.17) [eq:c-volume-cocycle]; along the same motion `c` has derivative at most `½ e^{-c} ‖T‖` in
absolute value, so that `|X_{K_U} e^{2c}| ≤ e^{c} ‖T‖ ≤ ‖T‖²` (proof of Lemma F.3
[lem:c-operators], from `e^{2c} = ‖A_T v_θ‖²` of Lemma F.1 [cc:lem:quotient]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Helpers -/

/-- `T* J T = J` makes `T` invertible. -/
private theorem circleSpeed_isUnit {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : Tᴴ * isoJ W * T = isoJ W) : IsUnit T := by
  have h : isoJ W * Tᴴ * isoJ W * T = 1 := by
    calc isoJ W * Tᴴ * isoJ W * T = isoJ W * (Tᴴ * isoJ W * T) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hT, isoJ_mul_isoJ]
  exact (Matrix.isUnit_iff_isUnit_det T).mpr (Matrix.isUnit_det_of_left_inverse h)

open scoped ComplexOrder in
/-- An orthogonal projection of trace zero vanishes. -/
private theorem circleSpeed_proj_eq_zero {ι : Type*} [Fintype ι] {S : Matrix ι ι ℂ}
    (hSh : Sᴴ = S) (hSS : S * S = S) (htr : S.trace = 0) : S = 0 := by
  rw [← Matrix.trace_conjTranspose_mul_self_eq_zero_iff, hSh, hSS, htr]

/-- `w* F = (F w)*` for Hermitian `F`. -/
private theorem circleSpeed_star_vecMul {ι : Type*} [Fintype ι] {F : Matrix ι ι ℂ} (hFh : Fᴴ = F)
    (w : ι → ℂ) : star w ᵥ* F = star (F *ᵥ w) := by
  rw [Matrix.star_mulVec, hFh]

/-- `‖w‖² = w* w`. -/
private theorem circleSpeed_dot_self {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_sum,
    Complex.ofReal_pow]

/-- `‖A w‖ ≤ ‖A‖ ‖w‖` for the operator norm. -/
private theorem circleSpeed_norm_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (w : ι → ℂ) :
    Real.sqrt (∑ i, ‖(A *ᵥ w) i‖ ^ 2) ≤ ‖A‖ * Real.sqrt (∑ i, ‖w i‖ ^ 2) := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 w)
  simpa [EuclideanSpace.norm_eq] using h

/-- The Cauchy–Schwarz inequality `|a* b| ≤ ‖a‖ ‖b‖`. -/
private theorem circleSpeed_norm_dot_le {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖b ⬝ᵥ star a‖ ≤ Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 a : EuclideanSpace ℂ ι) (WithLp.toLp 2 b)
  simpa [EuclideanSpace.norm_eq, EuclideanSpace.inner_eq_star_dotProduct] using h

/-- For a `J`-Lagrangian orthogonal projection `F` (`F J F = 0`, `tr F = W`): `J F J = 1 - F`,
hence `(1 - F) J = J F`. -/
private theorem circleSpeed_lagrangian {W : ℕ} {F : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hFh : Fᴴ = F) (hFF : F * F = F) (hFJ : F * isoJ W * F = 0) (htr : F.trace = (W : ℂ)) :
    (1 - F) * isoJ W = isoJ W * F := by
  have hJJ := isoJ_mul_isoJ W
  have hJh := isoJ_conjTranspose W
  have h1 : F * (isoJ W * F * isoJ W) = 0 := by
    calc F * (isoJ W * F * isoJ W) = (F * isoJ W * F) * isoJ W := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hFJ, Matrix.zero_mul]
  have h2 : isoJ W * F * isoJ W * F = 0 := by
    calc isoJ W * F * isoJ W * F = isoJ W * (F * isoJ W * F) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hFJ, Matrix.mul_zero]
  have h3 : isoJ W * F * isoJ W * (isoJ W * F * isoJ W) = isoJ W * F * isoJ W := by
    calc isoJ W * F * isoJ W * (isoJ W * F * isoJ W)
        = isoJ W * (F * (isoJ W * isoJ W) * F) * isoJ W := by simp only [Matrix.mul_assoc]
      _ = isoJ W * F * isoJ W := by rw [hJJ, Matrix.mul_one, hFF, Matrix.mul_assoc]
  have hS : 1 - F - isoJ W * F * isoJ W = 0 := by
    apply circleSpeed_proj_eq_zero
    · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh, hFh]
      simp only [Matrix.mul_assoc]
    · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hFF, h1, h2, h3]
      abel
    · have hc : (isoJ W * F * isoJ W).trace = F.trace := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
      rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_one, hc, htr]
      simp [Fintype.card_prod]
      ring
  have hS' : 1 - F = isoJ W * F * isoJ W := sub_eq_zero.mp hS
  rw [hS', Matrix.mul_assoc, hJJ, Matrix.mul_one]

/-- `T⁻¹ P' = P T⁻¹ P'` for the projection `P'` onto `T (ran P)`: `T⁻¹` maps `T (ran P)` into
`ran P`. -/
private theorem circleSpeed_inv_mul_flagProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T P : Matrix ι ι ℂ} (hT : IsUnit T) (hPP : P * P = P) :
    T⁻¹ * flagProj T P = P * (T⁻¹ * flagProj T P) := by
  have hTT : T⁻¹ * T = 1 :=
    Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp hT)
  have h : T⁻¹ * flagProj T P = P * (P * Tᴴ * T * P + (1 - P))⁻¹ * P * Tᴴ := by
    unfold flagProj
    calc T⁻¹ * (T * P * (P * Tᴴ * T * P + (1 - P))⁻¹ * P * Tᴴ)
        = (T⁻¹ * T) * P * (P * Tᴴ * T * P + (1 - P))⁻¹ * P * Tᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hTT, Matrix.one_mul]
  rw [h]
  simp only [← Matrix.mul_assoc, hPP]

/-- An orthogonal projection `F ≥ P` of rank one more than `P`, fixing `a ⊥ ran P`, is
`P + a a* / ‖a‖²`. -/
private theorem circleSpeed_rank_one {ι : Type*} [Fintype ι] {P F : Matrix ι ι ℂ}
    {a : ι → ℂ} {s : ℝ} (hPh : Pᴴ = P) (hPP : P * P = P) (hFh : Fᴴ = F) (hFF : F * F = F)
    (hFP : F * P = P) (htr : F.trace = P.trace + 1) (hFa : F *ᵥ a = a) (hPa : P *ᵥ a = 0)
    (hs : star a ⬝ᵥ a = (s : ℂ)) (hs0 : s ≠ 0) :
    F = P + ((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec a (star a) := by
  have hPF : P * F = P := by
    have := congrArg Matrix.conjTranspose hFP
    rwa [Matrix.conjTranspose_mul, hFh, hPh] at this
  have hsc : ((s⁻¹ : ℝ) : ℂ) * (s : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hs0, Complex.ofReal_one]
  have hFN : F * (((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec a (star a)) =
      ((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec a (star a) := by
    rw [Matrix.mul_smul, Matrix.mul_vecMulVec, hFa]
  have hNF : (((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec a (star a)) * F =
      ((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec a (star a) := by
    rw [Matrix.smul_mul, Matrix.vecMulVec_mul]
    rw [circleSpeed_star_vecMul hFh, hFa]
  have hPN : P * (((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec a (star a)) = 0 := by
    rw [Matrix.mul_smul, Matrix.mul_vecMulVec, hPa, Matrix.zero_vecMulVec, smul_zero]
  have hNP : (((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec a (star a)) * P = 0 := by
    rw [Matrix.smul_mul, Matrix.vecMulVec_mul, circleSpeed_star_vecMul hPh, hPa, star_zero,
      Matrix.vecMulVec_zero, smul_zero]
  have hNN : (((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec a (star a)) *
      (((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec a (star a)) =
      ((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec a (star a) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul, Matrix.vecMul_vecMulVec, hs,
      Matrix.vecMulVec_smul, smul_smul, smul_smul, mul_assoc, hsc, mul_one]
  have hS :=
    circleSpeed_proj_eq_zero (S := F - P - ((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec a (star a)) ?_ ?_ ?_
  · rw [sub_sub, sub_eq_zero] at hS
    exact hS
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_vecMulVec, star_star, hFh, hPh]
    simp
  · simp only [Matrix.sub_mul, Matrix.mul_sub, hFF, hFP, hFN, hPF, hPP, hPN, hNF, hNP, hNN]
    abel
  · rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_vecMulVec,
      dotProduct_comm, hs, htr, smul_eq_mul, hsc]
    ring

/-- A frame for the flag `x = (U, Y)` and its image: a unit `v ∈ Y ⊖ U` in `H_U`, the vector
`a = (1 - P_{TU}) T v` with `‖a‖ = e^{c}`, `P_{TY} = P_{TU} + a a* / ‖a‖²`, and
`P_{TY} T^{-*} v = a / ‖a‖²` (Lemma F.1 [cc:lem:quotient]). -/
private theorem circleSpeed_frame {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : Tᴴ * isoJ W * T = isoJ W) (x : IsoFlag W) (hW : 1 ≤ W) :
    ∃ (v a : Fin 2 × Fin W → ℂ) (s : ℝ),
      x.1.2 = x.1.1 + Matrix.vecMulVec v (star v) ∧ x.1.1 *ᵥ v = 0 ∧ star v ⬝ᵥ v = 1 ∧
      quotProj x.1.1 *ᵥ v = v ∧
      flagProj T x.1.2 = flagProj T x.1.1 + ((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec a (star a) ∧
      flagProj T x.1.1 *ᵥ a = 0 ∧ flagProj T x.1.2 *ᵥ a = a ∧
      flagProj T x.1.2 *ᵥ ((T⁻¹)ᴴ *ᵥ v) = ((s⁻¹ : ℝ) : ℂ) • a ∧
      Real.exp (volCocycle T x) = Real.sqrt (∑ i, ‖a i‖ ^ 2) ∧
      s = Real.exp (volCocycle T x) ^ 2 := by
  have hP : x.1.1 ∈ isoBases W := x.2.1
  obtain ⟨⟨hUh, hUU, hUtr, hUJ⟩, hYh, hYY, hYtr, hYU, hYJ⟩ := x.2
  obtain ⟨e, f, hef⟩ := exists_isCircleBasis hW hP
  obtain ⟨θ, hθ⟩ := exists_circlePair_eq x hef
  obtain ⟨-, -, heJ, hfJ, heP, hfP⟩ := hef
  have h1 : x.1.2 = x.1.1 + Matrix.vecMulVec (circleVec e f θ) (star (circleVec e f θ)) :=
    congrArg Prod.snd hθ
  have h2 : x.1.1 *ᵥ circleVec e f θ = 0 := by
    simp [circleVec, Matrix.mulVec_smul, Matrix.mulVec_add, heP, hfP]
  have h3 : star (circleVec e f θ) ⬝ᵥ circleVec e f θ = 1 := by
    have h := congrArg Matrix.trace h1
    rw [Matrix.trace_add, Matrix.trace_vecMulVec, hYtr, hUtr, Nat.cast_sub hW] at h
    rw [dotProduct_comm]
    push_cast at h
    linear_combination -h
  have hJv : x.1.1 *ᵥ (isoJ W *ᵥ circleVec e f θ) = 0 := by
    simp [circleVec, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_neg, heJ, hfJ, heP, hfP]
  have h4 : quotProj x.1.1 *ᵥ circleVec e f θ = circleVec e f θ := by
    unfold quotProj
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, h2, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hJv, Matrix.mulVec_zero, sub_zero, sub_zero]
  set v := circleVec e f θ with hv
  have hTu := circleSpeed_isUnit hT
  have hYv : x.1.2 *ᵥ v = v := by
    rw [h1, Matrix.add_mulVec, h2, Matrix.vecMulVec_mulVec, h3]
    simp
  have hexp := exp_volCocycle_eq hTu x hYv h2 h3
  have hmem : (flagProj T x.1.1, flagProj T x.1.2) ∈ isoFlags W :=
    flagAct_coe hT x ▸ (flagAct T x).2
  obtain ⟨⟨hP'h, hP'P', hP'tr, -⟩, hFh, hFF, hFtr, hFP', -⟩ := hmem
  dsimp only at hP'h hP'P' hP'tr hFh hFF hFtr hFP'
  set P' := flagProj T x.1.1 with hP'
  set F := flagProj T x.1.2 with hF
  set a := (1 - P') *ᵥ (T *ᵥ v) with ha
  set s : ℝ := ∑ i, ‖a i‖ ^ 2 with hs
  have hs2 : s = Real.exp (volCocycle T x) ^ 2 := by
    rw [hexp, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  have hs0 : s ≠ 0 := by
    rw [hs2]
    positivity
  have hFTv : F *ᵥ (T *ᵥ v) = T *ᵥ v := by
    have hY := (flagProj_spec hTu hYh hYY).2.2
    calc F *ᵥ (T *ᵥ v) = (F * (T * x.1.2)) *ᵥ v := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hYv]
      _ = T *ᵥ v := by rw [hY, ← Matrix.mulVec_mulVec, hYv]
  have hFa : F *ᵥ a = a := by
    rw [ha, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, hFTv, Matrix.mulVec_mulVec,
      hFP']
  have hP'a : P' *ᵥ a = 0 := by
    rw [ha, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hP'P', sub_self,
      Matrix.zero_mulVec]
  have htr : F.trace = P'.trace + 1 := by
    rw [hFtr, hP'tr, Nat.cast_sub hW]
    push_cast
    ring
  have hdot : star a ⬝ᵥ a = (s : ℂ) := circleSpeed_dot_self a
  have h5 := circleSpeed_rank_one hP'h.eq hP'P' hFh.eq hFF hFP' htr hFa hP'a hdot hs0
  have hL4 := circleSpeed_inv_mul_flagProj hTu hUU
  rw [← hP'] at hL4
  have hP'inv : P' * (T⁻¹)ᴴ * x.1.1 = P' * (T⁻¹)ᴴ := by
    have := congrArg Matrix.conjTranspose hL4
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP'h.eq,
      hUh.eq] at this
    exact this.symm
  have hP'v : P' *ᵥ ((T⁻¹)ᴴ *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, ← hP'inv, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]
  have hTTv : T⁻¹ *ᵥ (T *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp hTu), Matrix.one_mulVec]
  have hav : star a ⬝ᵥ ((T⁻¹)ᴴ *ᵥ v) = 1 := by
    have hTa : T⁻¹ *ᵥ a = v - x.1.1 *ᵥ ((T⁻¹ * P') *ᵥ (T *ᵥ v)) := by
      rw [ha, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, hTTv,
        Matrix.mulVec_mulVec (T *ᵥ v) x.1.1, ← hL4, Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hTa, star_sub, sub_dotProduct, h3,
      Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hUh.eq, h2, dotProduct_zero, sub_zero]
  refine ⟨v, a, s, h1, h2, h3, h4, h5, hP'a, hFa, ?_, hexp, hs2⟩
  rw [h5, Matrix.add_mulVec, hP'v, zero_add, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hav]
  simp

/-- `T K_U T⁻¹ P_{TY} = -(i/2) (T J v) a* / ‖a‖²` in the frame of `circleSpeed_frame`. -/
private theorem circleSpeed_main {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : Tᴴ * isoJ W * T = isoJ W) (x : IsoFlag W) (hW : 1 ≤ W)
    {v a : Fin 2 × Fin W → ℂ} {s : ℝ}
    (h1 : x.1.2 = x.1.1 + Matrix.vecMulVec v (star v)) (h4 : quotProj x.1.1 *ᵥ v = v)
    (h7 : flagProj T x.1.2 *ᵥ ((T⁻¹)ᴴ *ᵥ v) = ((s⁻¹ : ℝ) : ℂ) • a) :
    T * circleGen x.1.1 * T⁻¹ * flagProj T x.1.2 =
      Matrix.vecMulVec (T *ᵥ ((-(Complex.I / 2)) • (isoJ W *ᵥ v))) (((s⁻¹ : ℝ) : ℂ) • star a) := by
  have hP : x.1.1 ∈ isoBases W := x.2.1
  obtain ⟨⟨hUh, hUU, -, -⟩, hYh, hYY, -⟩ := x.2
  have hTu := circleSpeed_isUnit hT
  obtain ⟨-, -, hJQ, -, -⟩ := quotProj_spec hW hP
  have hKP := (circleGen_mem_lieJ hW hP).2.2.1
  have hL4 := circleSpeed_inv_mul_flagProj hTu hYY
  have hKv : circleGen x.1.1 *ᵥ v = (-(Complex.I / 2)) • (isoJ W *ᵥ v) := by
    unfold circleGen
    rw [Matrix.smul_mulVec, ← hJQ, ← Matrix.mulVec_mulVec, h4]
  have hKY : circleGen x.1.1 * x.1.2 =
      Matrix.vecMulVec ((-(Complex.I / 2)) • (isoJ W *ᵥ v)) (star v) := by
    rw [h1, Matrix.mul_add, hKP, zero_add, Matrix.mul_vecMulVec, hKv]
  have hrow : star v ᵥ* (T⁻¹ * flagProj T x.1.2) = ((s⁻¹ : ℝ) : ℂ) • star a := by
    have h := Matrix.star_mulVec (T⁻¹ * flagProj T x.1.2)ᴴ v
    rw [Matrix.conjTranspose_conjTranspose] at h
    rw [← h, Matrix.conjTranspose_mul, (flagProj_spec hTu hYh hYY).1.eq, ← Matrix.mulVec_mulVec,
      h7, star_smul]
    simp
  calc T * circleGen x.1.1 * T⁻¹ * flagProj T x.1.2
      = T * (circleGen x.1.1 * (T⁻¹ * flagProj T x.1.2)) := by simp only [Matrix.mul_assoc]
    _ = T * ((circleGen x.1.1 * x.1.2) * (T⁻¹ * flagProj T x.1.2)) := by
        conv_lhs => rw [hL4]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hKY, Matrix.vecMulVec_mul, hrow, Matrix.mul_vecMulVec]

/-! ### The angular speed -/


/-- The infinitesimal (8.36) [cc:eq:jac]: for `T* J T = J`, the line derivative
`(1 - Π) D T⁻¹ Π + Π T^{-*} D* (1 - Π)` of the image projection `Π = P_{TY}` along
`D = T K_U` equals `e^{-2c(T; U, Y)} [K_{TU}, Π]`: the image flag moves along its circle at
speed `e^{-2c}`. -/
theorem flagProj_circleGen_motion {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : Tᴴ * isoJ W * T = isoJ W) (x : IsoFlag W) :
    (1 - flagProj T x.1.2) * (T * circleGen x.1.1) * T⁻¹ * flagProj T x.1.2 +
        flagProj T x.1.2 * (T⁻¹)ᴴ * (T * circleGen x.1.1)ᴴ * (1 - flagProj T x.1.2) =
      ((Real.exp (-2 * volCocycle T x) : ℝ) : ℂ) •
        (circleGen (flagProj T x.1.1) * flagProj T x.1.2 -
          flagProj T x.1.2 * circleGen (flagProj T x.1.1)) := by
  rcases Nat.eq_zero_or_pos W with h0 | hW
  · subst h0
    exact Matrix.ext fun i _ => Fin.elim0 i.2
  obtain ⟨v, a, s, h1, -, -, h4, h5, hP'a, hFa, h7, -, hs2⟩ := circleSpeed_frame hT x hW
  have hmem : (flagProj T x.1.1, flagProj T x.1.2) ∈ isoFlags W :=
    flagAct_coe hT x ▸ (flagAct T x).2
  obtain ⟨hP', hFh, hFF, hFtr, hFP', hFJ⟩ := hmem
  dsimp only at hP' hFh hFF hFtr hFP' hFJ
  have hlag := circleSpeed_lagrangian hFh.eq hFF hFJ hFtr
  have hmain := circleSpeed_main hT x hW h1 h4 h7
  obtain ⟨hQh', -, hJQ', -, -⟩ := quotProj_spec hW hP'
  have hK'P' := (circleGen_mem_lieJ hW hP').2.2.1
  have hP'F : flagProj T x.1.1 * flagProj T x.1.2 = flagProj T x.1.1 := by
    have := congrArg Matrix.conjTranspose hFP'
    rwa [Matrix.conjTranspose_mul, hFh.eq, hP'.1.eq] at this
  have hrs : star ((s⁻¹ : ℝ) : ℂ) = ((s⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  have hTJ : T * isoJ W = isoJ W * (T⁻¹)ᴴ := by
    rw [inv_eq_isoJ_mul_conjTranspose_mul hT, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      isoJ_conjTranspose, Matrix.conjTranspose_conjTranspose]
    simp only [← Matrix.mul_assoc, isoJ_mul_isoJ, Matrix.one_mul]
  have hvec : (1 - flagProj T x.1.2) *ᵥ (T *ᵥ ((-(Complex.I / 2)) • (isoJ W *ᵥ v))) =
      ((-(Complex.I / 2)) * ((s⁻¹ : ℝ) : ℂ)) • (isoJ W *ᵥ a) := by
    have hM : (1 - flagProj T x.1.2) * T * isoJ W = isoJ W * flagProj T x.1.2 * (T⁻¹)ᴴ := by
      rw [Matrix.mul_assoc, hTJ, ← Matrix.mul_assoc, hlag]
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h7, Matrix.mulVec_smul, smul_smul]
  have hX : (1 - flagProj T x.1.2) * (T * circleGen x.1.1) * T⁻¹ * flagProj T x.1.2 =
      (((s⁻¹ : ℝ) : ℂ) * ((s⁻¹ : ℝ) : ℂ)) •
        ((-(Complex.I / 2)) • Matrix.vecMulVec (isoJ W *ᵥ a) (star a)) := by
    calc (1 - flagProj T x.1.2) * (T * circleGen x.1.1) * T⁻¹ * flagProj T x.1.2
        = (1 - flagProj T x.1.2) * (T * circleGen x.1.1 * T⁻¹ * flagProj T x.1.2) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hmain, Matrix.mul_vecMulVec, hvec]
          ext i j
          simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
          ring
  have hQ'a : quotProj (flagProj T x.1.1) *ᵥ a = a := by
    have hP'Ja : flagProj T x.1.1 *ᵥ (isoJ W *ᵥ a) = 0 := by
      have h0 : flagProj T x.1.1 * isoJ W * flagProj T x.1.2 = 0 := by
        calc flagProj T x.1.1 * isoJ W * flagProj T x.1.2
            = flagProj T x.1.1 * (flagProj T x.1.2 * isoJ W * flagProj T x.1.2) := by
              conv_lhs => rw [← hP'F]
              simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hFJ, Matrix.mul_zero]
      rw [← hFa, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]
    unfold quotProj
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hP'a, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hP'Ja, Matrix.mulVec_zero, sub_zero, sub_zero]
  have hK'a : circleGen (flagProj T x.1.1) *ᵥ a = (-(Complex.I / 2)) • (isoJ W *ᵥ a) := by
    unfold circleGen
    rw [Matrix.smul_mulVec, ← hJQ', ← Matrix.mulVec_mulVec, hQ'a]
  have hX' : (1 - flagProj T x.1.2) * circleGen (flagProj T x.1.1) * flagProj T x.1.2 =
      ((s⁻¹ : ℝ) : ℂ) • ((-(Complex.I / 2)) • Matrix.vecMulVec (isoJ W *ᵥ a) (star a)) := by
    have hJa : (1 - flagProj T x.1.2) *ᵥ (isoJ W *ᵥ a) = isoJ W *ᵥ a := by
      rw [Matrix.mulVec_mulVec, hlag, ← Matrix.mulVec_mulVec, hFa]
    have hK'F : circleGen (flagProj T x.1.1) * flagProj T x.1.2 =
        ((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec ((-(Complex.I / 2)) • (isoJ W *ᵥ a)) (star a) := by
      rw [h5, Matrix.mul_add, hK'P', zero_add, Matrix.mul_smul, Matrix.mul_vecMulVec, hK'a]
    rw [Matrix.mul_assoc, hK'F, Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.mulVec_smul, hJa,
      Matrix.smul_vecMulVec]
  have hK'h : (circleGen (flagProj T x.1.1))ᴴ = -circleGen (flagProj T x.1.1) := by
    unfold circleGen
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, isoJ_conjTranspose, hQh'.eq, hJQ',
      ← neg_smul]
    congr 1
    simp [neg_div]
  have hXh : flagProj T x.1.2 * (T⁻¹)ᴴ * (T * circleGen x.1.1)ᴴ * (1 - flagProj T x.1.2) =
      ((1 - flagProj T x.1.2) * (T * circleGen x.1.1) * T⁻¹ * flagProj T x.1.2)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      hFh.eq, Matrix.mul_assoc]
  have hcomm : circleGen (flagProj T x.1.1) * flagProj T x.1.2 -
      flagProj T x.1.2 * circleGen (flagProj T x.1.1) =
      (1 - flagProj T x.1.2) * circleGen (flagProj T x.1.1) * flagProj T x.1.2 +
        ((1 - flagProj T x.1.2) * circleGen (flagProj T x.1.1) * flagProj T x.1.2)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hK'h, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hFh.eq]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul,
      Matrix.mul_neg, Matrix.mul_assoc]
    abel
  have hexp : ((Real.exp (-2 * volCocycle T x) : ℝ) : ℂ) = ((s⁻¹ : ℝ) : ℂ) := by
    congr 1
    rw [hs2, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  rw [hXh, hcomm, hX, hX', hexp, smul_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, star_mul', hrs]
  module

/-- Along `D = T K_U` the cocycle (8.17) [eq:c-volume-cocycle] has line derivative
`Re Tr(P_{TY} D T⁻¹) - Re Tr(P_{TU} D T⁻¹)`, of absolute value at most `½ e^{-c} ‖T‖` (proof of
Lemma F.3 [lem:c-operators]). -/
theorem abs_cocycle_circleGen_le {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : Tᴴ * isoJ W * T = isoJ W) (x : IsoFlag W) :
    |(flagProj T x.1.2 * (T * circleGen x.1.1) * T⁻¹).trace.re -
        (flagProj T x.1.1 * (T * circleGen x.1.1) * T⁻¹).trace.re| ≤
      Real.exp (-volCocycle T x) * ‖T‖ / 2 := by
  rcases Nat.eq_zero_or_pos W with h0 | hW
  · subst h0
    have h : ∀ M : Matrix (Fin 2 × Fin 0) (Fin 2 × Fin 0) ℂ, M.trace = 0 := fun M => by
      simp [Matrix.trace]
    rw [h, h, Complex.zero_re, sub_self, abs_zero]
    positivity
  obtain ⟨v, a, s, h1, -, h3, h4, -, -, -, h7, hexp, hs2⟩ := circleSpeed_frame hT x hW
  have hP : x.1.1 ∈ isoBases W := x.2.1
  obtain ⟨⟨-, hUU, -, -⟩, -⟩ := x.2
  have hTu := circleSpeed_isUnit hT
  have hmain := circleSpeed_main hT x hW h1 h4 h7
  have hKP := (circleGen_mem_lieJ hW hP).2.2.1
  have hL4 := circleSpeed_inv_mul_flagProj hTu hUU
  have htrY : (flagProj T x.1.2 * (T * circleGen x.1.1) * T⁻¹).trace =
      ((-(Complex.I / 2)) * ((s⁻¹ : ℝ) : ℂ)) * ((T *ᵥ (isoJ W *ᵥ v)) ⬝ᵥ star a) := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, hmain, Matrix.trace_vecMulVec,
      Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have htrU : (flagProj T x.1.1 * (T * circleGen x.1.1) * T⁻¹).trace = 0 := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    have h0 : T * circleGen x.1.1 * T⁻¹ * flagProj T x.1.1 = 0 := by
      calc T * circleGen x.1.1 * T⁻¹ * flagProj T x.1.1
          = T * (circleGen x.1.1 * (T⁻¹ * flagProj T x.1.1)) := by simp only [Matrix.mul_assoc]
        _ = T * ((circleGen x.1.1 * x.1.1) * (T⁻¹ * flagProj T x.1.1)) := by
            conv_lhs => rw [hL4]
            simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hKP, Matrix.zero_mul, Matrix.mul_zero]
    rw [h0, Matrix.trace_zero]
  have hJv : Real.sqrt (∑ i, ‖(isoJ W *ᵥ v) i‖ ^ 2) = 1 := by
    have h : star (isoJ W *ᵥ v) ⬝ᵥ (isoJ W *ᵥ v) = 1 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        isoJ_conjTranspose, isoJ_mul_isoJ, Matrix.one_mulVec, h3]
    rw [circleSpeed_dot_self] at h
    have h' : ∑ i, ‖(isoJ W *ᵥ v) i‖ ^ 2 = 1 := by exact_mod_cast h
    rw [h', Real.sqrt_one]
  have hd : ‖(T *ᵥ (isoJ W *ᵥ v)) ⬝ᵥ star a‖ ≤ Real.exp (volCocycle T x) * ‖T‖ := by
    calc ‖(T *ᵥ (isoJ W *ᵥ v)) ⬝ᵥ star a‖
        ≤ Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖(T *ᵥ (isoJ W *ᵥ v)) i‖ ^ 2) :=
          circleSpeed_norm_dot_le a _
      _ ≤ Real.sqrt (∑ i, ‖a i‖ ^ 2) * (‖T‖ * Real.sqrt (∑ i, ‖(isoJ W *ᵥ v) i‖ ^ 2)) := by
          gcongr
          exact circleSpeed_norm_mulVec T _
      _ = Real.exp (volCocycle T x) * ‖T‖ := by rw [hJv, ← hexp, mul_one]
  have hspos : 0 < s := by
    rw [hs2]
    positivity
  rw [htrY, htrU, Complex.zero_re, sub_zero]
  calc |((-(Complex.I / 2)) * ((s⁻¹ : ℝ) : ℂ) * ((T *ᵥ (isoJ W *ᵥ v)) ⬝ᵥ star a)).re|
      ≤ ‖(-(Complex.I / 2)) * ((s⁻¹ : ℝ) : ℂ) * ((T *ᵥ (isoJ W *ᵥ v)) ⬝ᵥ star a)‖ :=
        Complex.abs_re_le_norm _
    _ = 1 / 2 * s⁻¹ * ‖(T *ᵥ (isoJ W *ᵥ v)) ⬝ᵥ star a‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hspos.le)]
        simp
    _ ≤ 1 / 2 * s⁻¹ * (Real.exp (volCocycle T x) * ‖T‖) := by gcongr
    _ = Real.exp (-volCocycle T x) * ‖T‖ / 2 := by
        rw [hs2, Real.exp_neg]
        field_simp

end LSBA
