import LSBA.Upper.LargeContract
import LSBA.Transfer.Transition
import LSBA.Gauss.GUENormMoment

/-!
# The mean of the first vector observable

(11.21) [uvg:eq:fmean]: `P_g f₁ = −e^{−2iθ} f₁ + e^{−2iθ} h²g⁻² (B_o + B_e) + O(g⁻⁴ + g⁻²/W)` with
the explicit `B_o`, `B_e`, for every `W ≥ 1`, `g ≥ 1` and state, with the constant depending only on
`E₀`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `B_o = (3 + m_2) f_1 + 2 m_1 f_2 - f_1 (m_1 f_1 + m_{-1} f_{-1})` of (11.21)
[uvg:eq:fmean]. -/
def bOdd {W : ℕ} (X : State W) : ℂ :=
  (3 + obsM 2 X) * obsF 1 X + 2 * obsM 1 X * obsF 2 X -
    obsF 1 X * (obsM 1 X * obsF 1 X + obsM (-1) X * obsF (-1) X)

/-- `B_e = 4 m_1 f_1 + 2 f_2 - f_1² - f_1 f_{-1}` of (11.21) [uvg:eq:fmean]. -/
def bEven {W : ℕ} (X : State W) : ℂ :=
  4 * obsM 1 X * obsF 1 X + 2 * obsF 2 X - obsF 1 X ^ 2 - obsF 1 X * obsF (-1) X

/-! ### Scalar and norm bounds -/

private lemma mf_normalH_nonneg (E : ℝ) : 0 ≤ normalH E := by
  unfold normalH freeAngle
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg (E / 2))
    (Real.arccos_le_pi (E / 2))
  positivity

/-- `h_θ ≤ (2 √(1 − E₀²/4))⁻¹` for `|E| ≤ E₀ < 2`. -/
private lemma mf_normalH_le {E₀ E : ℝ} (hE₀ : E₀ < 2) (hE : |E| ≤ E₀) :
    normalH E ≤ (2 * √(1 - E₀ ^ 2 / 4))⁻¹ := by
  unfold normalH freeAngle
  rw [Real.sin_arccos]
  have ha := abs_nonneg E
  have h1 : E ^ 2 ≤ E₀ ^ 2 := by
    rw [← sq_abs E]
    exact pow_le_pow_left₀ ha hE 2
  have h2 : 0 < 1 - E₀ ^ 2 / 4 := by nlinarith
  have h3 : √(1 - E₀ ^ 2 / 4) ≤ √(1 - (E / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have h4 : 0 < √(1 - E₀ ^ 2 / 4) := Real.sqrt_pos.mpr h2
  exact inv_anti₀ (by positivity) (by linarith)

private lemma mf_norm_normalPhase (E : ℝ) : ‖normalPhase E‖ = 1 := by
  unfold normalPhase
  rw [norm_neg, show 2 * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma mf_norm_stepPhase (E : ℝ) : ‖stepPhase E‖ = 1 := by
  unfold stepPhase
  rw [show -((freeAngle E : ℂ) * Complex.I) = ((-freeAngle E : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma mf_norm_lin_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : ‖Matrix.toEuclideanLin A v‖ ≤ ‖A‖ * ‖v‖ :=
  (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) A).le_opNorm v

private lemma mf_lin_mul {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) :
    Matrix.toEuclideanLin (A * B) v = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

private lemma mf_inner_lin_conjTranspose {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v w : EuclideanSpace ℂ (Fin W)) :
    inner ℂ v (Matrix.toEuclideanLin Aᴴ w) = inner ℂ (Matrix.toEuclideanLin A v) w := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

/-! ### The quadratic form `v* A v` -/

private lemma mf_vecForm_add {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : vecForm (A + B) v = vecForm A v + vecForm B v := by
  unfold vecForm
  rw [map_add, LinearMap.add_apply, inner_add_right]

private lemma mf_vecForm_smul {W : ℕ} (c : ℂ) (A : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : vecForm (c • A) v = c * vecForm A v := by
  unfold vecForm
  rw [map_smul, LinearMap.smul_apply, inner_smul_right]

private lemma mf_vecForm_neg {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : vecForm (-A) v = -vecForm A v := by
  rw [← neg_one_smul ℂ A, mf_vecForm_smul]
  ring

private lemma mf_vecForm_sub {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : vecForm (A - B) v = vecForm A v - vecForm B v := by
  rw [sub_eq_add_neg, mf_vecForm_add, mf_vecForm_neg, ← sub_eq_add_neg]

private lemma mf_vecForm_one {W : ℕ} {v : EuclideanSpace ℂ (Fin W)} (hv : ‖v‖ = 1) :
    vecForm (1 : Matrix (Fin W) (Fin W) ℂ) v = 1 := by
  unfold vecForm
  have h1 : Matrix.toEuclideanLin (1 : Matrix (Fin W) (Fin W) ℂ) v = v := by simp
  rw [h1, inner_self_eq_norm_sq_to_K, hv]
  simp

private lemma mf_norm_vecForm_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    {v : EuclideanSpace ℂ (Fin W)} (hv : ‖v‖ = 1) : ‖vecForm A v‖ ≤ ‖A‖ := by
  unfold vecForm
  refine (norm_inner_le_norm _ _).trans ?_
  rw [hv, one_mul]
  exact (mf_norm_lin_le A v).trans (by rw [hv, mul_one])

private lemma mf_continuous_vecForm {W : ℕ}
    {φ : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} (hφ : Continuous φ)
    (v : EuclideanSpace ℂ (Fin W)) :
    Continuous fun V => vecForm (φ V) v := by
  have hc : Continuous (fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) =>
      Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) q.1 q.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM
  have h := hc.comp (hφ.prodMk (continuous_const (y := v)))
  exact continuous_const.inner h

/-! ### The jet of the inverse-adjoint direction

With `X = V (I + C)`, `X' = (I + C*) V` and `s = i h_θ g⁻¹`, the matrices `F⁻*`, `F⁻¹ F⁻*` and
`F⁻¹ (I + C) F⁻¹ F⁻*` of (11.3) [lg:eq:matrix-update] and (11.7) [lg:eq:update] satisfy one linear
recursion `x = a + s L x`. -/

/-- The linear map `L (A, B, R) = (−X' A, −X' A + X B, (I + C)(−X' A + X B) + X R)`. -/
private def mfL {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) :
    Module.End ℂ (Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ ×
      Matrix (Fin W) (Fin W) ℂ) where
  toFun z := (-((1 + Cᴴ) * V * z.1), -((1 + Cᴴ) * V * z.1) + V * (1 + C) * z.2.1,
    (1 + C) * (-((1 + Cᴴ) * V * z.1) + V * (1 + C) * z.2.1) + V * (1 + C) * z.2.2)
  map_add' z z' := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [Prod.fst_add, Prod.snd_add] <;> noncomm_ring
  map_smul' c z := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [Prod.smul_fst, Prod.smul_snd, Matrix.mul_smul, RingHom.id_apply, smul_add,
        smul_neg, Matrix.mul_add, Matrix.mul_neg]

/-- The initial point `a = (I, I, I + C)` of the recursion. -/
private def mfA {W : ℕ} (C : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ :=
  (1, 1, 1 + C)

/-- Iterating `x = a + s L x` four times. -/
private lemma mf_jet {M : Type*} [AddCommGroup M] [Module ℂ M] (L : Module.End ℂ M) (s : ℂ)
    {a x : M} (hx : x = a + s • L x) :
    x = a + s • (L ^ 1) a + s ^ 2 • (L ^ 2) a + s ^ 3 • (L ^ 3) a + s ^ 4 • (L ^ 4) x := by
  have step : ∀ k : ℕ, (L ^ k) x = (L ^ k) a + s • (L ^ (k + 1)) x := by
    intro k
    conv_lhs => rw [hx]
    rw [map_add, map_smul, pow_succ, Module.End.mul_apply]
  have h0 := step 0
  have h1 := step 1
  have h2 := step 2
  have h3 := step 3
  rw [pow_zero, Module.End.one_apply, Module.End.one_apply] at h0
  rw [h1, h2, h3] at h0
  have e : x = a + s • ((L ^ 1) a + s • ((L ^ 2) a + s • ((L ^ 3) a + s • (L ^ 4) x))) := h0
  conv_lhs => rw [e]
  module

private lemma mf_L_apply {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ)
    (z : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ) :
    mfL C V z = (-((1 + Cᴴ) * V * z.1), -((1 + Cᴴ) * V * z.1) + V * (1 + C) * z.2.1,
      (1 + C) * (-((1 + Cᴴ) * V * z.1) + V * (1 + C) * z.2.1) + V * (1 + C) * z.2.2) := rfl

private lemma mf_L_neg {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ)
    (z : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ) :
    mfL C (-V) z = -mfL C V z := by
  rw [mf_L_apply, mf_L_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> noncomm_ring

/-- `L` is odd in `V`. -/
private lemma mf_Lpow_neg {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (k : ℕ)
    (z : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ) :
    (mfL C (-V) ^ k) z = (-1 : ℂ) ^ k • (mfL C V ^ k) z := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc (mfL C (-V) ^ (k + 1)) z = mfL C (-V) ((mfL C (-V) ^ k) z) := by
          rw [pow_succ', Module.End.mul_apply]
      _ = (-1 : ℂ) ^ k • -mfL C V ((mfL C V ^ k) z) := by rw [ih, map_smul, mf_L_neg]
      _ = (-1 : ℂ) ^ (k + 1) • (mfL C V ^ (k + 1)) z := by
          rw [pow_succ' (mfL C V), Module.End.mul_apply, pow_succ (-1 : ℂ), mul_smul,
            neg_one_smul]

private lemma mf_norm_PVZ {W : ℕ} (P V Z : Matrix (Fin W) (Fin W) ℂ) :
    ‖P * V * Z‖ ≤ ‖P‖ * ‖V‖ * ‖Z‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

private lemma mf_norm_one_add {W : ℕ} (hW : 1 ≤ W) {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) : ‖C‖ = 1 ∧ ‖1 + C‖ ≤ 2 ∧ ‖1 + Cᴴ‖ ≤ 2 := by
  have : Nonempty (Fin W) := ⟨⟨0, hW⟩⟩
  have hnC : ‖C‖ = 1 := CStarRing.norm_of_mem_unitary hC
  refine ⟨hnC, ?_, ?_⟩
  · calc ‖1 + C‖ ≤ ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ + ‖C‖ := norm_add_le _ _
      _ = 2 := by rw [norm_one, hnC]; norm_num
  · calc ‖1 + Cᴴ‖ ≤ ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ + ‖Cᴴ‖ := norm_add_le _ _
      _ = 2 := by rw [norm_one, Matrix.l2_opNorm_conjTranspose, hnC]; norm_num

/-- `‖L z‖ ≤ 10 ‖V‖ ‖z‖`. -/
private lemma mf_norm_L {W : ℕ} (hW : 1 ≤ W) {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (V : Matrix (Fin W) (Fin W) ℂ)
    (z : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ) :
    ‖mfL C V z‖ ≤ 10 * ‖V‖ * ‖z‖ := by
  obtain ⟨-, h1, h1'⟩ := mf_norm_one_add hW hC
  have hz1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have hz2 : ‖z.2.1‖ ≤ ‖z‖ := (norm_fst_le z.2).trans (norm_snd_le z)
  have hz3 : ‖z.2.2‖ ≤ ‖z‖ := (norm_snd_le z.2).trans (norm_snd_le z)
  have hV := norm_nonneg V
  have hz := norm_nonneg z
  have hA : ‖(1 + Cᴴ) * V * z.1‖ ≤ 2 * ‖V‖ * ‖z‖ :=
    (mf_norm_PVZ _ _ _).trans (by nlinarith [mul_le_mul h1' hz1 (norm_nonneg _) (by norm_num)])
  have hB : ‖V * (1 + C) * z.2.1‖ ≤ 2 * ‖V‖ * ‖z‖ :=
    (mf_norm_PVZ _ _ _).trans (by nlinarith [mul_le_mul h1 hz2 (norm_nonneg _) (by norm_num)])
  have hB' : ‖V * (1 + C) * z.2.2‖ ≤ 2 * ‖V‖ * ‖z‖ :=
    (mf_norm_PVZ _ _ _).trans (by nlinarith [mul_le_mul h1 hz3 (norm_nonneg _) (by norm_num)])
  have hAB : ‖-((1 + Cᴴ) * V * z.1) + V * (1 + C) * z.2.1‖ ≤ 4 * ‖V‖ * ‖z‖ :=
    (norm_add_le _ _).trans (by rw [norm_neg]; linarith)
  rw [mf_L_apply]
  refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩
  · rw [norm_neg]
    nlinarith [mul_nonneg hV hz]
  · nlinarith [mul_nonneg hV hz]
  · refine (norm_add_le _ _).trans ?_
    have := (norm_mul_le (1 + C) (-((1 + Cᴴ) * V * z.1) + V * (1 + C) * z.2.1)).trans
      (mul_le_mul h1 hAB (norm_nonneg _) (by norm_num))
    nlinarith [mul_nonneg hV hz]

private lemma mf_norm_Lpow {W : ℕ} (hW : 1 ≤ W) {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (V : Matrix (Fin W) (Fin W) ℂ) (k : ℕ)
    (z : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ) :
    ‖(mfL C V ^ k) z‖ ≤ (10 * ‖V‖) ^ k * ‖z‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    refine (mf_norm_L hW hC V _).trans ?_
    calc 10 * ‖V‖ * ‖(mfL C V ^ k) z‖ ≤ 10 * ‖V‖ * ((10 * ‖V‖) ^ k * ‖z‖) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (10 * ‖V‖) ^ (k + 1) * ‖z‖ := by ring

/-- The triple `x = (F⁻*, F⁻¹ F⁻*, F⁻¹ (I + C) F⁻¹ F⁻*)`. -/
private def mfx (g E : ℝ) {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ :=
  ((stepF g E C V)⁻¹ᴴ, (stepF g E C V)⁻¹ * (stepF g E C V)⁻¹ᴴ,
    (stepF g E C V)⁻¹ * (1 + C) * ((stepF g E C V)⁻¹ * (stepF g E C V)⁻¹ᴴ))

/-- The recursion `x = a + s L x` with `s = i h_θ g⁻¹`, from `F⁻¹ F = F F⁻¹ = I`. -/
private lemma mf_rec (g E : ℝ) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) :
    mfx g E C V = mfA C + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • mfL C V (mfx g E C V) := by
  set s : ℂ := Complex.I * ((normalH E / g : ℝ) : ℂ) with hs_def
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_stepF g E hC hV)
  have hGF : (stepF g E C V)⁻¹ * stepF g E C V = 1 := Matrix.nonsing_inv_mul _ hdet
  have hFG : stepF g E C V * (stepF g E C V)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hF : stepF g E C V = 1 - s • (V * (1 + C)) := rfl
  set G := (stepF g E C V)⁻¹ with hG_def
  have hG1 : G = 1 + s • (G * (V * (1 + C))) := by
    calc G = G * stepF g E C V + s • (G * (V * (1 + C))) := by
          rw [hF, Matrix.mul_sub, mul_one, Matrix.mul_smul]; abel
      _ = 1 + s • (G * (V * (1 + C))) := by rw [hGF]
  have hG2 : G = 1 + s • (V * (1 + C) * G) := by
    calc G = stepF g E C V * G + s • (V * (1 + C) * G) := by
          rw [hF, Matrix.sub_mul, one_mul, Matrix.smul_mul]; abel
      _ = 1 + s • (V * (1 + C) * G) := by rw [hFG]
  have hs : star s = -s := by
    rw [hs_def, star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hX : (V * (1 + C))ᴴ = (1 + Cᴴ) * V := by
    rw [Matrix.conjTranspose_mul, hV.eq, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
  have hGh : Gᴴ = 1 + s • -((1 + Cᴴ) * V * Gᴴ) := by
    conv_lhs => rw [hG1]
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul, hX, hs, neg_smul, smul_neg]
  have hQ : G * Gᴴ = 1 + s • (-((1 + Cᴴ) * V * Gᴴ) + V * (1 + C) * (G * Gᴴ)) := by
    have e1 : G * Gᴴ = Gᴴ + s • (V * (1 + C) * (G * Gᴴ)) := by
      nth_rewrite 1 [hG2]
      rw [add_mul, one_mul, Matrix.smul_mul, mul_assoc (V * (1 + C))]
    conv_lhs => rw [e1]
    conv_lhs => arg 1; rw [hGh]
    rw [smul_add]
    abel
  have hR : G * (1 + C) * (G * Gᴴ) = (1 + C) + s • ((1 + C) * (-((1 + Cᴴ) * V * Gᴴ) +
      V * (1 + C) * (G * Gᴴ)) + V * (1 + C) * (G * (1 + C) * (G * Gᴴ))) := by
    have e1 : G * (1 + C) * (G * Gᴴ) = (1 + C) * (G * Gᴴ) +
        s • (V * (1 + C) * (G * (1 + C) * (G * Gᴴ))) := by
      nth_rewrite 1 [hG2]
      rw [add_mul, add_mul, one_mul, Matrix.smul_mul, Matrix.smul_mul]
      simp only [mul_assoc]
    have e2 : (1 + C) * (G * Gᴴ) = (1 + C) + s • ((1 + C) * (-((1 + Cᴴ) * V * Gᴴ) +
        V * (1 + C) * (G * Gᴴ))) := by
      conv_lhs => rw [hQ]
      rw [Matrix.mul_add, mul_one, Matrix.mul_smul]
    conv_lhs => rw [e1]
    conv_lhs => arg 1; rw [e2]
    rw [smul_add]
    abel
  unfold mfx mfA
  rw [mf_L_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact hGh
  · exact hQ
  · exact hR

/-- `Y = v* F⁻¹ F⁻* v = ‖F⁻* v‖²`. -/
private lemma mf_Y_eq (g E : ℝ) {W : ℕ} (X : State W) (V : Matrix (Fin W) (Fin W) ℂ) :
    vecForm (mfx g E X.1 V).2.1 X.2 = ((‖stepVec g E X V‖ ^ 2 : ℝ) : ℂ) := by
  unfold mfx vecForm stepVec
  simp only
  rw [mf_lin_mul]
  nth_rewrite 1 [← Matrix.conjTranspose_conjTranspose (stepF g E X.1 V)⁻¹]
  rw [mf_inner_lin_conjTranspose, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- `f_1' = -e^{-2iθ} (P - Y) / Y` with `P = v* F⁻¹ (I + C) F⁻¹ F⁻* v`. -/
private lemma mf_obsF_eq (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    obsF 1 (stepState g E X V) = -normalPhase E *
      ((vecForm (mfx g E X.1 V).2.2 X.2 - vecForm (mfx g E X.1 V).2.1 X.2) /
        vecForm (mfx g E X.1 V).2.1 X.2) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_stepF g E hX.1 hV)
  have hGF : (stepF g E X.1 V)⁻¹ * stepF g E X.1 V = 1 := Matrix.nonsing_inv_mul _ hdet
  set w := stepVec g E X V with hw
  have hw0 : 0 < ‖w‖ := by
    refine norm_pos_iff.mpr fun h0 => ?_
    have h1 : Matrix.toEuclideanLin (stepF g E X.1 V)ᴴ w = X.2 := by
      rw [hw]
      unfold stepVec
      rw [← mf_lin_mul, ← Matrix.conjTranspose_mul, hGF, Matrix.conjTranspose_one]
      simp
    rw [h0, map_zero] at h1
    have h2 : ‖X.2‖ = 0 := by rw [← h1, norm_zero]
    rw [hX.2] at h2
    exact one_ne_zero h2
  rw [mf_Y_eq]
  set G := (stepF g E X.1 V)⁻¹ with hG
  set c : ℂ := stepPhase E * ((‖w‖⁻¹ : ℝ) : ℂ) with hc
  have hC' : G * stepC g E X.1 V * Gᴴ = -normalPhase E • ((mfx g E X.1 V).2.2 - G * Gᴴ) := by
    have e : G * (X.1 + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + X.1))) =
        G * (1 + X.1) - 1 := by
      have hF1 : G * (1 - (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + X.1))) = 1 := hGF
      calc G * (X.1 + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + X.1))) =
          G * (1 + X.1) - G * (1 - (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + X.1))) := by
            simp only [Matrix.mul_add, Matrix.mul_sub, mul_one]
            abel
        _ = G * (1 + X.1) - 1 := by rw [hF1]
    unfold stepC mfx
    rw [← hG, Matrix.mul_smul, Matrix.smul_mul, ← mul_assoc, e]
    simp only [mul_assoc, Matrix.sub_mul, one_mul]
  have hin : vecForm (G * stepC g E X.1 V * Gᴴ) X.2 =
      inner ℂ w (Matrix.toEuclideanLin (stepC g E X.1 V) w) := by
    unfold vecForm
    rw [mf_lin_mul, mf_lin_mul]
    rw [show Matrix.toEuclideanLin Gᴴ X.2 = w from rfl]
    rw [← Matrix.conjTranspose_conjTranspose G, mf_inner_lin_conjTranspose]
    rfl
  have hstate : obsF 1 (stepState g E X V) =
      (star c * c) * vecForm (G * stepC g E X.1 V * Gᴴ) X.2 := by
    rw [hin]
    unfold obsF vecForm stepState
    simp only [zpow_one]
    rw [← hw, ← hc, map_smul, inner_smul_left, inner_smul_right]
    simp only [Complex.star_def]
    ring
  have hcc : star c * c = (((‖w‖ ^ 2 : ℝ) : ℂ))⁻¹ := by
    rw [Complex.star_def, Complex.conj_mul', hc, norm_mul, mf_norm_stepPhase, one_mul,
      Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hw0.le)]
    push_cast
    rw [inv_pow]
  rw [hstate, hC', mf_vecForm_smul, mf_vecForm_sub, hcc]
  have hY : vecForm (G * Gᴴ) X.2 = ((‖w‖ ^ 2 : ℝ) : ℂ) := mf_Y_eq g E X V
  rw [hY]
  simp only [← hw]
  ring

/-! ### The ratio `P / Y` to third order with remainder -/

/-- The first-order coefficient of `P / Y`. -/
private def mfq1 (p y : ℕ → ℂ) : ℂ := p 1 - p 0 * y 1

/-- The second-order coefficient of `P / Y`. -/
private def mfq2 (p y : ℕ → ℂ) : ℂ := p 2 - p 1 * y 1 - p 0 * y 2 + p 0 * y 1 ^ 2

/-- The third-order coefficient of `P / Y`. -/
private def mfq3 (p y : ℕ → ℂ) : ℂ :=
  p 3 - p 2 * y 1 - p 1 * y 2 + p 1 * y 1 ^ 2 - p 0 * y 3 + 2 * p 0 * y 1 * y 2 - p 0 * y 1 ^ 3

/-- The third-order truncation of `P / Y`. -/
private def mfT (s : ℂ) (p y : ℕ → ℂ) : ℂ :=
  p 0 + s * mfq1 p y + s ^ 2 * mfq2 p y + s ^ 3 * mfq3 p y

/-- The numerator of the fourth-order remainder of `P / Y`. -/
private def mfrho (s : ℂ) (p y : ℕ → ℂ) (rP rY : ℂ) : ℂ :=
  rP - mfT s p y * rY - (mfq1 p y * y 3 + mfq2 p y * y 2 + mfq3 p y * y 1) -
    s * (mfq2 p y * y 3 + mfq3 p y * y 2) - s ^ 2 * (mfq3 p y * y 3)

/-- `P / Y = T₃ + s⁴ ρ / Y` for `P = Σ s^k p_k + s⁴ r_P` and `Y = 1 + Σ s^k y_k + s⁴ r_Y`. -/
private lemma mf_div {s P Y rP rY : ℂ} (p y : ℕ → ℂ)
    (hP : P = p 0 + s * p 1 + s ^ 2 * p 2 + s ^ 3 * p 3 + s ^ 4 * rP)
    (hY : Y = 1 + s * y 1 + s ^ 2 * y 2 + s ^ 3 * y 3 + s ^ 4 * rY) (hY0 : Y ≠ 0) :
    P / Y = mfT s p y + s ^ 4 * (mfrho s p y rP rY / Y) := by
  have e : P = mfT s p y * Y + s ^ 4 * mfrho s p y rP rY := by
    rw [hP, hY]
    unfold mfrho mfT mfq1 mfq2 mfq3
    ring
  rw [e]
  field_simp

private lemma mf_norm_pow_le {y : ℂ} {A : ℝ} (h : ‖y‖ ≤ A) (n : ℕ) : ‖y ^ n‖ ≤ A ^ n := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h n

private lemma mf_mono {H A : ℝ} (hH : 0 ≤ H) (hA : 1 ≤ A) {i j : ℕ} (hi : i ≤ 3) (hj : j ≤ 5) :
    H ^ i * A ^ j ≤ (1 + H) ^ 3 * A ^ 5 := by
  have h1 : H ^ i ≤ (1 + H) ^ 3 :=
    (pow_le_pow_left₀ hH (by linarith) i).trans (pow_le_pow_right₀ (by linarith) hi)
  have h2 : A ^ j ≤ A ^ 5 := pow_le_pow_right₀ hA hj
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- `‖ρ‖ ≤ 50 (1 + H)³ A⁵` when all coefficients and remainders are bounded by `A ≥ 1`. -/
private lemma mf_norm_rho_le {s : ℂ} {H A : ℝ} (hs : ‖s‖ ≤ H) (hA : 1 ≤ A) (p y : ℕ → ℂ)
    {rP rY : ℂ} (hp : ∀ k, k ≤ 3 → ‖p k‖ ≤ A) (hy : ∀ k, k ≤ 3 → ‖y k‖ ≤ A) (hrP : ‖rP‖ ≤ A)
    (hrY : ‖rY‖ ≤ A) : ‖mfrho s p y rP rY‖ ≤ 50 * (1 + H) ^ 3 * A ^ 5 := by
  have hH : 0 ≤ H := (norm_nonneg _).trans hs
  have a0 := hp 0 (by norm_num)
  have a1 := hp 1 (by norm_num)
  have a2 := hp 2 (by norm_num)
  have a3 := hp 3 (by norm_num)
  have b1 := hy 1 (by norm_num)
  have b2 := hy 2 (by norm_num)
  have b3 := hy 3 (by norm_num)
  have h2 : ‖(2 : ℂ)‖ ≤ 2 := by norm_num
  have hq1 : ‖mfq1 p y‖ ≤ A + A * A := norm_sub_le_of_le a1 (norm_mul_le_of_le a0 b1)
  have hq2 : ‖mfq2 p y‖ ≤ A + A * A + A * A + A * A ^ 2 :=
    norm_add_le_of_le (norm_sub_le_of_le (norm_sub_le_of_le a2 (norm_mul_le_of_le a1 b1))
      (norm_mul_le_of_le a0 b2)) (norm_mul_le_of_le a0 (mf_norm_pow_le b1 2))
  have hq3 : ‖mfq3 p y‖ ≤ A + A * A + A * A + A * A ^ 2 + A * A + 2 * A * A * A +
      A * A ^ 3 :=
    norm_sub_le_of_le (norm_add_le_of_le (norm_sub_le_of_le (norm_add_le_of_le
      (norm_sub_le_of_le (norm_sub_le_of_le a3 (norm_mul_le_of_le a2 b1))
        (norm_mul_le_of_le a1 b2)) (norm_mul_le_of_le a1 (mf_norm_pow_le b1 2)))
      (norm_mul_le_of_le a0 b3))
      (norm_mul_le_of_le (norm_mul_le_of_le (norm_mul_le_of_le h2 a0) b1) b2))
      (norm_mul_le_of_le a0 (mf_norm_pow_le b1 3))
  have hA2 : A ≤ A ^ 2 := by nlinarith
  have hA3 : A ^ 2 ≤ A ^ 3 := by nlinarith
  have hA4 : A ^ 3 ≤ A ^ 4 := by nlinarith
  have hq1' : ‖mfq1 p y‖ ≤ 2 * A ^ 2 := by nlinarith
  have hq2' : ‖mfq2 p y‖ ≤ 4 * A ^ 3 := by nlinarith
  have hq3' : ‖mfq3 p y‖ ≤ 8 * A ^ 4 := by nlinarith
  have hT : ‖mfT s p y‖ ≤ A + H * (2 * A ^ 2) + H ^ 2 * (4 * A ^ 3) + H ^ 3 * (8 * A ^ 4) :=
    norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le a0 (norm_mul_le_of_le hs hq1'))
      (norm_mul_le_of_le (mf_norm_pow_le hs 2) hq2'))
      (norm_mul_le_of_le (mf_norm_pow_le hs 3) hq3')
  have hρ : ‖mfrho s p y rP rY‖ ≤ A + (A + H * (2 * A ^ 2) + H ^ 2 * (4 * A ^ 3) +
      H ^ 3 * (8 * A ^ 4)) * A + (2 * A ^ 2 * A + 4 * A ^ 3 * A + 8 * A ^ 4 * A) +
      H * (4 * A ^ 3 * A + 8 * A ^ 4 * A) + H ^ 2 * (8 * A ^ 4 * A) :=
    norm_sub_le_of_le (norm_sub_le_of_le (norm_sub_le_of_le (norm_sub_le_of_le hrP
      (norm_mul_le_of_le hT hrY)) (norm_add_le_of_le (norm_add_le_of_le
        (norm_mul_le_of_le hq1' b3) (norm_mul_le_of_le hq2' b2)) (norm_mul_le_of_le hq3' b1)))
      (norm_mul_le_of_le hs (norm_add_le_of_le (norm_mul_le_of_le hq2' b3)
        (norm_mul_le_of_le hq3' b2))))
      (norm_mul_le_of_le (mf_norm_pow_le hs 2) (norm_mul_le_of_le hq3' b3))
  refine hρ.trans ?_
  have m01 := mf_mono hH hA (i := 0) (j := 1) (by norm_num) (by norm_num)
  have m02 := mf_mono hH hA (i := 0) (j := 2) (by norm_num) (by norm_num)
  have m03 := mf_mono hH hA (i := 0) (j := 3) (by norm_num) (by norm_num)
  have m04 := mf_mono hH hA (i := 0) (j := 4) (by norm_num) (by norm_num)
  have m05 := mf_mono hH hA (i := 0) (j := 5) (by norm_num) (by norm_num)
  have m13 := mf_mono hH hA (i := 1) (j := 3) (by norm_num) (by norm_num)
  have m14 := mf_mono hH hA (i := 1) (j := 4) (by norm_num) (by norm_num)
  have m15 := mf_mono hH hA (i := 1) (j := 5) (by norm_num) (by norm_num)
  have m24 := mf_mono hH hA (i := 2) (j := 4) (by norm_num) (by norm_num)
  have m25 := mf_mono hH hA (i := 2) (j := 5) (by norm_num) (by norm_num)
  have m35 := mf_mono hH hA (i := 3) (j := 5) (by norm_num) (by norm_num)
  simp only [pow_zero, pow_one, one_mul] at m01 m02 m03 m04 m05 m13 m14 m15
  nlinarith

/-! ### The coefficients of `Y` and `P` -/

/-- The coefficient `y_k` of `s^k` in `Y = v* F⁻¹ F⁻* v`. -/
private def mfy {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W))
    (k : ℕ) : ℂ :=
  vecForm ((mfL C V ^ k) (mfA C)).2.1 v

/-- The coefficient `p_k` of `s^k` in `P = v* F⁻¹ (I + C) F⁻¹ F⁻* v`. -/
private def mfp {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W))
    (k : ℕ) : ℂ :=
  vecForm ((mfL C V ^ k) (mfA C)).2.2 v

private lemma mf_y_neg {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W))
    (k : ℕ) : mfy C (-V) v k = (-1) ^ k * mfy C V v k := by
  unfold mfy
  rw [mf_Lpow_neg, Prod.smul_snd, Prod.smul_fst, mf_vecForm_smul]

private lemma mf_p_neg {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W))
    (k : ℕ) : mfp C (-V) v k = (-1) ^ k * mfp C V v k := by
  unfold mfp
  rw [mf_Lpow_neg, Prod.smul_snd, Prod.smul_snd, mf_vecForm_smul]

/-- The first- and third-order coefficients of `P / Y` are odd in `V`, the second is even. -/
private lemma mf_q_neg {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) :
    mfq1 (mfp C (-V) v) (mfy C (-V) v) = -mfq1 (mfp C V v) (mfy C V v) ∧
      mfq2 (mfp C (-V) v) (mfy C (-V) v) = mfq2 (mfp C V v) (mfy C V v) ∧
      mfq3 (mfp C (-V) v) (mfy C (-V) v) = -mfq3 (mfp C V v) (mfy C V v) := by
  unfold mfq1 mfq2 mfq3
  simp only [mf_y_neg, mf_p_neg]
  refine ⟨by ring, by ring, by ring⟩

private lemma mf_p_zero {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) {v : EuclideanSpace ℂ (Fin W)}
    (hv : ‖v‖ = 1) : mfp C V v 0 = 1 + vecForm C v := by
  unfold mfp
  rw [pow_zero, Module.End.one_apply]
  change vecForm (1 + C) v = _
  rw [mf_vecForm_add, mf_vecForm_one hv]

private lemma mf_norm_A {W : ℕ} (hW : 1 ≤ W) {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) : ‖mfA C‖ ≤ 2 := by
  have : Nonempty (Fin W) := ⟨⟨0, hW⟩⟩
  obtain ⟨-, h1, -⟩ := mf_norm_one_add hW hC
  refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, h1⟩⟩ <;>
    · change ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 2
      rw [norm_one]
      norm_num

private lemma mf_norm_y {W : ℕ} (hW : 1 ≤ W) {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (V : Matrix (Fin W) (Fin W) ℂ)
    {v : EuclideanSpace ℂ (Fin W)} (hv : ‖v‖ = 1) (k : ℕ) :
    ‖mfy C V v k‖ ≤ (10 * ‖V‖) ^ k * 2 ∧ ‖mfp C V v k‖ ≤ (10 * ‖V‖) ^ k * 2 := by
  have h := (mf_norm_Lpow hW hC V k (mfA C)).trans
    (mul_le_mul_of_nonneg_left (mf_norm_A hW hC) (by positivity))
  refine ⟨(mf_norm_vecForm_le _ hv).trans (((norm_fst_le _).trans (norm_snd_le _)).trans h),
    (mf_norm_vecForm_le _ hv).trans (((norm_snd_le _).trans (norm_snd_le _)).trans h)⟩

/-- The direction term `y₁` of the proof of (11.21) [uvg:eq:fmean] is `i` times the coefficient of
`s` in `Y`. -/
private lemma mf_dirY1 {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) :
    vecForm (dirY1 C V) v = Complex.I * mfy C V v 1 := by
  unfold mfy
  rw [← mf_vecForm_smul]
  congr 1
  rw [pow_one, mf_L_apply]
  simp only [mfA, mul_one, dirY1]
  congr 1
  abel

/-- `y₂` is minus the coefficient of `s²` in `Y`. -/
private lemma mf_dirY2 {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) :
    vecForm (dirY2 C V) v = -mfy C V v 2 := by
  unfold mfy
  rw [← mf_vecForm_neg]
  congr 1
  rw [sq, Module.End.mul_apply, mf_L_apply, mf_L_apply]
  simp only [mfA, dirY2]
  noncomm_ring

/-- `n₁` is `i` times the coefficient of `s` in `P − Y`. -/
private lemma mf_dirN1 {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) :
    vecForm (dirN1 C V) v = Complex.I * (mfp C V v 1 - mfy C V v 1) := by
  unfold mfy mfp
  rw [← mf_vecForm_sub, ← mf_vecForm_smul]
  congr 1
  rw [pow_one, mf_L_apply]
  simp only [mfA, dirN1]
  congr 1
  noncomm_ring

/-- `n₂` is minus the coefficient of `s²` in `P − Y`. -/
private lemma mf_dirN2 {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) :
    vecForm (dirN2 C V) v = -(mfp C V v 2 - mfy C V v 2) := by
  unfold mfy mfp
  rw [← mf_vecForm_sub, ← mf_vecForm_neg]
  congr 1
  rw [sq, Module.End.mul_apply, mf_L_apply, mf_L_apply]
  simp only [mfA, dirN2]
  noncomm_ring

/-- The integrand `n₂ − n₁ y₁ − f₁ y₂ + f₁ y₁²` of the second-order term of (11.21)
[uvg:eq:fmean]. -/
private def mfQ {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) : ℂ :=
  vecForm (dirN2 C V) v - vecForm (dirN1 C V) v * vecForm (dirY1 C V) v -
    vecForm C v * vecForm (dirY2 C V) v + vecForm C v * vecForm (dirY1 C V) v ^ 2

/-- The second-order coefficient of `P / Y` in `s = i h_θ g⁻¹` is `−Q`. -/
private lemma mf_q2_eq {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) {v : EuclideanSpace ℂ (Fin W)}
    (hv : ‖v‖ = 1) : mfq2 (mfp C V v) (mfy C V v) = -mfQ C V v := by
  unfold mfQ mfq2
  rw [mf_dirY1, mf_dirY2, mf_dirN1, mf_dirN2, mf_p_zero C V hv]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-(mfp C V v 1) * mfy C V v 1 + mfy C V v 1 ^ 2 +
    vecForm C v * mfy C V v 1 ^ 2) * hI

/-! ### The update of `f₁` to third order with remainder -/

/-- The jets `Y = 1 + Σ_{k ≤ 3} s^k y_k + s⁴ r_Y` and `P = Σ_{k ≤ 3} s^k p_k + s⁴ r_P`. -/
private lemma mf_jets (g E : ℝ) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) {v : EuclideanSpace ℂ (Fin W)}
    (hv : ‖v‖ = 1) :
    vecForm (mfx g E C V).2.1 v = 1 + (Complex.I * ((normalH E / g : ℝ) : ℂ)) * mfy C V v 1 +
        (Complex.I * ((normalH E / g : ℝ) : ℂ)) ^ 2 * mfy C V v 2 +
        (Complex.I * ((normalH E / g : ℝ) : ℂ)) ^ 3 * mfy C V v 3 +
        (Complex.I * ((normalH E / g : ℝ) : ℂ)) ^ 4 *
          vecForm ((mfL C V ^ 4) (mfx g E C V)).2.1 v ∧
      vecForm (mfx g E C V).2.2 v = mfp C V v 0 +
        (Complex.I * ((normalH E / g : ℝ) : ℂ)) * mfp C V v 1 +
        (Complex.I * ((normalH E / g : ℝ) : ℂ)) ^ 2 * mfp C V v 2 +
        (Complex.I * ((normalH E / g : ℝ) : ℂ)) ^ 3 * mfp C V v 3 +
        (Complex.I * ((normalH E / g : ℝ) : ℂ)) ^ 4 *
          vecForm ((mfL C V ^ 4) (mfx g E C V)).2.2 v := by
  have hj := mf_jet (mfL C V) _ (mf_rec g E hC hV)
  have h1 := congrArg (fun z => vecForm z.2.1 v) hj
  have h2 := congrArg (fun z => vecForm z.2.2 v) hj
  simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, mf_vecForm_add,
    mf_vecForm_smul] at h1 h2
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · rw [show (mfA C).2.1 = 1 from rfl, mf_vecForm_one hv]
    rfl
  · rw [show vecForm (mfA C).2.2 v = mfp C V v 0 by
      unfold mfp; rw [pow_zero, Module.End.one_apply]]
    rfl

/-- `‖x‖ ≤ 2 γ³` with `γ = 1 + 2 h_θ ‖V‖ / g`. -/
private lemma mf_norm_x {W : ℕ} (hW : 1 ≤ W) {g E : ℝ} (hg : 0 < g)
    {C V : Matrix (Fin W) (Fin W) ℂ} (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ)
    (hV : V.IsHermitian) : ‖mfx g E C V‖ ≤ 2 * (1 + 2 * normalH E * ‖V‖ / g) ^ 3 := by
  obtain ⟨-, h1, -⟩ := mf_norm_one_add hW hC
  have hG := (norm_stepF_le hg E hC hV).2
  set γ := 1 + 2 * normalH E * ‖V‖ / g with hγ
  have hγ1 : 1 ≤ γ := by
    have : 0 ≤ 2 * normalH E * ‖V‖ / g := by
      have := mf_normalH_nonneg E
      positivity
    linarith
  have hGh : ‖(stepF g E C V)⁻¹ᴴ‖ ≤ γ := by rw [Matrix.l2_opNorm_conjTranspose]; exact hG
  have hQ : ‖(stepF g E C V)⁻¹ * (stepF g E C V)⁻¹ᴴ‖ ≤ γ ^ 2 :=
    (norm_mul_le _ _).trans (by rw [sq]; exact mul_le_mul hG hGh (norm_nonneg _) (by linarith))
  have hR : ‖(stepF g E C V)⁻¹ * (1 + C) * ((stepF g E C V)⁻¹ * (stepF g E C V)⁻¹ᴴ)‖ ≤
      γ * 2 * γ ^ 2 :=
    (mf_norm_PVZ _ _ _).trans (mul_le_mul (mul_le_mul hG h1 (norm_nonneg _) (by linarith)) hQ
      (norm_nonneg _) (by positivity))
  have hγ2 : γ ≤ γ ^ 2 := by nlinarith
  have hγ3 : γ ^ 2 ≤ γ ^ 3 := by nlinarith
  unfold mfx
  refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- The pointwise expansion: `f₁' = −e^{−2iθ}(f₁ + s q₁ + s² q₂ + s³ q₃) + O(t⁴ (1 + ‖V‖)^42)` with
`t = h_θ / g`, `s = i t`, on all Hermitian blocks. -/
private lemma mf_point {W : ℕ} (hW : 1 ≤ W) {g E H : ℝ} (hg : 1 ≤ g) (hH : normalH E ≤ H)
    {X : State W} (hX : IsState X) {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    ‖obsF 1 (stepState g E X V) - -normalPhase E * (obsF 1 X +
        (Complex.I * ((normalH E / g : ℝ) : ℂ)) * mfq1 (mfp X.1 V X.2) (mfy X.1 V X.2) +
        (Complex.I * ((normalH E / g : ℝ) : ℂ)) ^ 2 * mfq2 (mfp X.1 V X.2) (mfy X.1 V X.2) +
        (Complex.I * ((normalH E / g : ℝ) : ℂ)) ^ 3 * mfq3 (mfp X.1 V X.2) (mfy X.1 V X.2))‖ ≤
      (normalH E / g) ^ 4 *
        (50 * (1 + H) ^ 3 * (2 * (1 + 2 * H) ^ 3 * (10 * (1 + ‖V‖)) ^ 7) ^ 6) := by
  have hg0 : 0 < g := by linarith
  have hh0 := mf_normalH_nonneg E
  have hH0 : 0 ≤ H := hh0.trans hH
  set t : ℝ := normalH E / g with ht
  have ht0 : 0 ≤ t := div_nonneg hh0 hg0.le
  have htH : t ≤ H := (div_le_self hh0 hg).trans hH
  set s : ℂ := Complex.I * (t : ℂ) with hs
  have hsn : ‖s‖ = t := by
    rw [hs, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
  set S : ℝ := 1 + ‖V‖ with hS
  have hS1 : 1 ≤ S := by have := norm_nonneg V; linarith
  set A : ℝ := 2 * (1 + 2 * H) ^ 3 * (10 * S) ^ 7 with hA
  have h10 : 1 ≤ 10 * S := by linarith
  have hH1 : 1 ≤ (1 + 2 * H) ^ 3 := one_le_pow₀ (by linarith)
  have hA1 : 1 ≤ A := by
    have : 1 ≤ (10 * S) ^ 7 := one_le_pow₀ h10
    nlinarith
  -- the coefficient bounds
  have hcoef : ∀ k, k ≤ 3 → (10 * ‖V‖) ^ k * 2 ≤ A := by
    intro k hk
    have e1 : (10 * ‖V‖) ^ k ≤ (10 * S) ^ 7 :=
      (pow_le_pow_left₀ (by positivity) (by linarith) k).trans (pow_le_pow_right₀ h10 (by omega))
    have : 0 ≤ (10 * S) ^ 7 := by positivity
    nlinarith
  have hp : ∀ k, k ≤ 3 → ‖mfp X.1 V X.2 k‖ ≤ A := fun k hk =>
    (mf_norm_y hW hX.1 V hX.2 k).2.trans (hcoef k hk)
  have hy : ∀ k, k ≤ 3 → ‖mfy X.1 V X.2 k‖ ≤ A := fun k hk =>
    (mf_norm_y hW hX.1 V hX.2 k).1.trans (hcoef k hk)
  -- the remainder bounds
  set γ := 1 + 2 * normalH E * ‖V‖ / g with hγ
  have hγS : γ ≤ (1 + 2 * H) * S := by
    have e : 2 * normalH E * ‖V‖ / g = 2 * t * ‖V‖ := by rw [ht]; ring
    rw [hγ, e]
    nlinarith [norm_nonneg V, mul_le_mul_of_nonneg_right htH (norm_nonneg V)]
  have hγ1 : 1 ≤ γ := by
    have : 0 ≤ 2 * normalH E * ‖V‖ / g := by positivity
    linarith
  have hx := mf_norm_x hW hg0 (E := E) hX.1 hV
  have hrem : (10 * ‖V‖) ^ 4 * ‖mfx g E X.1 V‖ ≤ A := by
    have e1 : (10 * ‖V‖) ^ 4 ≤ (10 * S) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    have e2 : γ ^ 3 ≤ ((1 + 2 * H) * S) ^ 3 := pow_le_pow_left₀ (by linarith) hγS 3
    have e3 : S ^ 3 ≤ (10 * S) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    calc (10 * ‖V‖) ^ 4 * ‖mfx g E X.1 V‖ ≤ (10 * S) ^ 4 * (2 * ((1 + 2 * H) * S) ^ 3) :=
          mul_le_mul e1 (hx.trans (by linarith)) (norm_nonneg _) (by positivity)
      _ = 2 * (1 + 2 * H) ^ 3 * ((10 * S) ^ 4 * S ^ 3) := by ring
      _ ≤ 2 * (1 + 2 * H) ^ 3 * ((10 * S) ^ 4 * (10 * S) ^ 3) := by gcongr
      _ = A := by rw [hA]; ring
  have hrY : ‖vecForm ((mfL X.1 V ^ 4) (mfx g E X.1 V)).2.1 X.2‖ ≤ A :=
    (mf_norm_vecForm_le _ hX.2).trans ((((norm_fst_le _).trans (norm_snd_le _)).trans
      (mf_norm_Lpow hW hX.1 V 4 _)).trans hrem)
  have hrP : ‖vecForm ((mfL X.1 V ^ 4) (mfx g E X.1 V)).2.2 X.2‖ ≤ A :=
    (mf_norm_vecForm_le _ hX.2).trans ((((norm_snd_le _).trans (norm_snd_le _)).trans
      (mf_norm_Lpow hW hX.1 V 4 _)).trans hrem)
  -- the lower bound on `Y`
  set w := stepVec g E X V with hw
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_stepF g E hX.1 hV)
  have hwv : Matrix.toEuclideanLin (stepF g E X.1 V)ᴴ w = X.2 := by
    rw [hw]
    unfold stepVec
    rw [← mf_lin_mul, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hdet,
      Matrix.conjTranspose_one]
    simp
  have hw1 : 1 ≤ γ * ‖w‖ := by
    have h1 := mf_norm_lin_le (stepF g E X.1 V)ᴴ w
    rw [hwv, hX.2, Matrix.l2_opNorm_conjTranspose] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (norm_stepF_le hg0 E hX.1 hV).1 (norm_nonneg _))
  have hY := mf_Y_eq g E X V
  have hYn : ‖vecForm (mfx g E X.1 V).2.1 X.2‖ = ‖w‖ ^ 2 := by
    rw [hY, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hw0 : 0 < ‖w‖ := by
    by_contra h0
    have : ‖w‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
    rw [this, mul_zero] at hw1
    linarith
  have hY0 : vecForm (mfx g E X.1 V).2.1 X.2 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hYn
    have : 0 < ‖w‖ ^ 2 := by positivity
    linarith
  have hYinv : ‖vecForm (mfx g E X.1 V).2.1 X.2‖⁻¹ ≤ A := by
    rw [hYn]
    have e1 : (‖w‖ ^ 2)⁻¹ ≤ γ ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      nlinarith
    have e2 : γ ^ 2 ≤ ((1 + 2 * H) * S) ^ 2 := pow_le_pow_left₀ (by linarith) hγS 2
    have e3 : ((1 + 2 * H) * S) ^ 2 ≤ A := by
      have f1 : (1 + 2 * H) ^ 2 ≤ (1 + 2 * H) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have f2 : S ^ 2 ≤ (10 * S) ^ 7 :=
        (pow_le_pow_left₀ (by linarith) (by linarith) 2).trans (pow_le_pow_right₀ h10 (by norm_num))
      rw [mul_pow, hA]
      have : 0 ≤ S ^ 2 := by positivity
      nlinarith [mul_le_mul f1 f2 this (by positivity)]
    linarith
  -- assembly
  obtain ⟨hJY, hJP⟩ := mf_jets g E hX.1 hV hX.2
  have hdiv := mf_div (mfp X.1 V X.2) (mfy X.1 V X.2) hJP hJY hY0
  have hf := mf_obsF_eq g E hX hV
  have hf1 : obsF 1 X = vecForm X.1 X.2 := by unfold obsF; rw [zpow_one]
  have hp0 := mf_p_zero X.1 V hX.2
  have e : obsF 1 (stepState g E X V) - -normalPhase E * (obsF 1 X +
      s * mfq1 (mfp X.1 V X.2) (mfy X.1 V X.2) + s ^ 2 * mfq2 (mfp X.1 V X.2) (mfy X.1 V X.2) +
      s ^ 3 * mfq3 (mfp X.1 V X.2) (mfy X.1 V X.2)) =
      -normalPhase E * s ^ 4 * (mfrho s (mfp X.1 V X.2) (mfy X.1 V X.2)
        (vecForm ((mfL X.1 V ^ 4) (mfx g E X.1 V)).2.2 X.2)
        (vecForm ((mfL X.1 V ^ 4) (mfx g E X.1 V)).2.1 X.2) /
          vecForm (mfx g E X.1 V).2.1 X.2) := by
    rw [hf, sub_div, div_self hY0, hdiv, hf1]
    unfold mfT
    rw [hp0]
    ring
  rw [e, norm_mul, norm_mul, norm_neg, mf_norm_normalPhase, one_mul, norm_pow, hsn, norm_div]
  have hρ := mf_norm_rho_le (le_of_eq hsn |>.trans htH) hA1 (mfp X.1 V X.2) (mfy X.1 V X.2) hp hy
    hrP hrY
  have ht4 : 0 ≤ t ^ 4 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ ht4
  rw [div_eq_mul_inv]
  calc ‖mfrho s (mfp X.1 V X.2) (mfy X.1 V X.2)
        (vecForm ((mfL X.1 V ^ 4) (mfx g E X.1 V)).2.2 X.2)
        (vecForm ((mfL X.1 V ^ 4) (mfx g E X.1 V)).2.1 X.2)‖ *
        ‖vecForm (mfx g E X.1 V).2.1 X.2‖⁻¹ ≤ (50 * (1 + H) ^ 3 * A ^ 5) * A :=
        mul_le_mul hρ hYinv (by positivity) (by positivity)
    _ = 50 * (1 + H) ^ 3 * A ^ 6 := by rw [mul_assoc, ← pow_succ]

/-! ### Integration over one block -/

private lemma mf_measurable_gb (W : ℕ) : Measurable fun ω : Ω W 1 => gueBlock W 1 ω 0 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma mf_pow_le {x : ℝ} (hx : 0 ≤ x) (r : ℕ) : (1 + x) ^ r ≤ 2 ^ r * (1 + x ^ r) := by
  have h := add_pow_le zero_le_one hx r
  rw [one_pow] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le r 1)

/-- `𝔼 (1 + ‖V‖)^r ≤ M` uniformly in `W`, from the moment bound (11.14) [uvg:eq:tail]. -/
private lemma mf_moment (r : ℕ) : ∃ M : ℝ, 0 < M ∧ ∀ W : ℕ,
    Integrable (fun ω : Ω W 1 => (1 + ‖gueBlock W 1 ω 0‖) ^ r) (μ W 1) ∧
      ∫ ω, (1 + ‖gueBlock W 1 ω 0‖) ^ r ∂(μ W 1) ≤ M := by
  obtain ⟨C, hC, h⟩ := lintegral_norm_gueBlock_pow_le r
  refine ⟨2 ^ r * (1 + C), by positivity, fun W => ?_⟩
  have hdom : Integrable (fun ω : Ω W 1 => 2 ^ r * (1 + ‖gueBlock W 1 ω 0‖ ^ r)) (μ W 1) :=
    ((integrable_const (1 : ℝ)).add (integrable_norm_gueBlock_pow W r)).const_mul _
  have hmeas : Measurable fun ω : Ω W 1 => (1 + ‖gueBlock W 1 ω 0‖) ^ r :=
    (measurable_const.add (measurable_norm.comp (mf_measurable_gb W))).pow_const r
  have hint : Integrable (fun ω : Ω W 1 => (1 + ‖gueBlock W 1 ω 0‖) ^ r) (μ W 1) :=
    hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact mf_pow_le (norm_nonneg _) r)
  refine ⟨hint, ?_⟩
  have hn : ∫ ω, ‖gueBlock W 1 ω 0‖ ^ r ∂(μ W 1) ≤ C := by
    have h1 := ofReal_integral_eq_lintegral_ofReal (integrable_norm_gueBlock_pow W r)
      (Filter.Eventually.of_forall fun ω => by positivity)
    have h2 : ∫⁻ ω, ENNReal.ofReal (‖gueBlock W 1 ω 0‖ ^ r) ∂(μ W 1) =
        ∫⁻ ω, ‖gueBlock W 1 ω 0‖ₑ ^ r ∂(μ W 1) := by
      refine lintegral_congr fun ω => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [h2] at h1
    exact (ENNReal.ofReal_le_ofReal_iff hC.le).mp (h1.trans_le (h W))
  calc ∫ ω, (1 + ‖gueBlock W 1 ω 0‖) ^ r ∂(μ W 1)
      ≤ ∫ ω, 2 ^ r * (1 + ‖gueBlock W 1 ω 0‖ ^ r) ∂(μ W 1) :=
        integral_mono hint hdom fun ω => mf_pow_le (norm_nonneg _) r
    _ = 2 ^ r * (1 + ∫ ω, ‖gueBlock W 1 ω 0‖ ^ r ∂(μ W 1)) := by
        rw [integral_const_mul, integral_add (integrable_const _)
          (integrable_norm_gueBlock_pow W r)]
        simp
    _ ≤ 2 ^ r * (1 + C) := by gcongr

/-- A continuous function of the block with polynomial growth on Hermitian matrices is
integrable. -/
private lemma mf_integrable {W : ℕ} {φ : Matrix (Fin W) (Fin W) ℂ → ℂ} (hφ : Continuous φ)
    {c : ℝ} (r : ℕ) (hb : ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian →
      ‖φ V‖ ≤ c * (1 + ‖V‖) ^ r) :
    Integrable (fun ω : Ω W 1 => φ (gueBlock W 1 ω 0)) (μ W 1) := by
  obtain ⟨M, -, hM⟩ := mf_moment r
  exact ((hM W).1.const_mul c).mono' (hφ.measurable.comp (mf_measurable_gb W)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => hb _ (gueBlock_isHermitian W 1 ω 0))

private lemma mf_measurable_obsF_one (W : ℕ) : Measurable fun Y : State W => obsF 1 Y := by
  have hc : Continuous (fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) =>
      Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) q.1 q.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM
  have h : (fun Y : State W => obsF 1 Y) = fun Y : State W =>
      inner ℂ Y.2 (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) Y.1 Y.2) := by
    funext Y
    unfold obsF vecForm
    rw [zpow_one]
    rfl
  rw [h]
  exact (continuous_snd.inner hc).measurable

/-- Growth of the direction terms: `|y₁| ≤ 20 S`, `|n₁| ≤ 40 S`, `|y₂| ≤ 200 S²`,
`|n₂| ≤ 400 S²` with `S = 1 + ‖V‖`. -/
private lemma mf_norm_dir {W : ℕ} (hW : 1 ≤ W) {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (V : Matrix (Fin W) (Fin W) ℂ)
    {v : EuclideanSpace ℂ (Fin W)} (hv : ‖v‖ = 1) :
    ‖vecForm (dirY1 C V) v‖ ≤ 20 * (1 + ‖V‖) ∧ ‖vecForm (dirN1 C V) v‖ ≤ 40 * (1 + ‖V‖) ∧
      ‖vecForm (dirY2 C V) v‖ ≤ 200 * (1 + ‖V‖) ^ 2 ∧
      ‖vecForm (dirN2 C V) v‖ ≤ 400 * (1 + ‖V‖) ^ 2 := by
  obtain ⟨y1, p1⟩ := mf_norm_y hW hC V hv 1
  obtain ⟨y2, p2⟩ := mf_norm_y hW hC V hv 2
  have hV := norm_nonneg V
  have hVS : ‖V‖ ^ 2 ≤ (1 + ‖V‖) ^ 2 := pow_le_pow_left₀ hV (by linarith) 2
  rw [mf_dirY1, mf_dirN1, mf_dirY2, mf_dirN2, norm_mul, norm_mul, Complex.norm_I, one_mul,
    one_mul, norm_neg, norm_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · exact (norm_sub_le _ _).trans (by nlinarith)
  · nlinarith
  · exact (norm_sub_le _ _).trans (by nlinarith)

/-- The symmetrization `𝔼 f(V) = 𝔼 (f(V) + f(−V))/2` for the update of `f₁`. -/
private lemma mf_sym {W : ℕ} (g E : ℝ) {X : State W} (hX : IsState X) :
    transOp g E (obsF 1) X = ∫ ω, (obsF 1 (stepState g E X (gueBlock W 1 ω 0)) +
      obsF 1 (stepState g E X (-gueBlock W 1 ω 0))) / 2 ∂(μ W 1) ∧
    Integrable (fun ω => (obsF 1 (stepState g E X (gueBlock W 1 ω 0)) +
      obsF 1 (stepState g E X (-gueBlock W 1 ω 0))) / 2) (μ W 1) := by
  have hgb := mf_measurable_gb W
  have hfm : ∀ φ : Ω W 1 → Matrix (Fin W) (Fin W) ℂ, Measurable φ →
      Measurable fun ω => obsF 1 (stepState g E X (φ ω)) := by
    intro φ hφ
    have hS : Measurable fun ω => (X, φ ω) := Measurable.prodMk measurable_const hφ
    have h1 := (measurable_stepState g E W).comp hS
    have h2 := (mf_measurable_obsF_one W).comp h1
    exact h2
  have hfi : Integrable (fun ω : Ω W 1 => obsF 1 (stepState g E X (gueBlock W 1 ω 0)))
      (μ W 1) :=
    Integrable.of_bound (hfm _ hgb).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω =>
        norm_obsF_le_one 1 (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)))
  have hfni : Integrable (fun ω : Ω W 1 => obsF 1 (stepState g E X (-gueBlock W 1 ω 0)))
      (μ W 1) :=
    Integrable.of_bound (hfm _ hgb.neg).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω =>
        norm_obsF_le_one 1 (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0).neg))
  refine ⟨?_, (hfi.add hfni).div_const 2⟩
  have hodd := integral_odd_gueBlock (G := ℂ) W
    (fun V => obsF 1 (stepState g E X V) - obsF 1 (stepState g E X (-V)))
    (fun V => by simp only [neg_neg, neg_sub])
  beta_reduce at hodd
  rw [integral_sub hfi hfni] at hodd
  have h2 := sub_eq_zero.mp hodd
  rw [integral_div, integral_add hfi hfni, ← h2, ← two_mul,
    mul_div_cancel_left₀ _ (two_ne_zero' ℂ)]
  rfl

/-- `𝔼 (n₂ − n₁ y₁ − f₁ y₂ + f₁ y₁²) = −(B_o + B_e) − (𝔼 n₁ y₁ − f₁ 𝔼 y₁²)`, with integrability. -/
private lemma mf_Q_int {W : ℕ} (hW : 1 ≤ W) {X : State W} (hX : IsState X) :
    Integrable (fun ω => mfQ X.1 (gueBlock W 1 ω 0) X.2) (μ W 1) ∧
    ∫ ω, mfQ X.1 (gueBlock W 1 ω 0) X.2 ∂(μ W 1) = -(bOdd X + bEven X) -
      ((∫ ω, vecForm (dirN1 X.1 (gueBlock W 1 ω 0)) X.2 *
          vecForm (dirY1 X.1 (gueBlock W 1 ω 0)) X.2 ∂(μ W 1)) -
        obsF 1 X * ∫ ω, vecForm (dirY1 X.1 (gueBlock W 1 ω 0)) X.2 ^ 2 ∂(μ W 1)) := by
  have hdir := fun V => mf_norm_dir hW hX.1 V hX.2
  have cN2 : Continuous fun V => vecForm (dirN2 X.1 V) X.2 :=
    mf_continuous_vecForm (by
      have hX : Continuous fun V : Matrix (Fin W) (Fin W) ℂ => V * (1 + X.1) :=
        continuous_id.mul continuous_const
      have hX' : Continuous fun V : Matrix (Fin W) (Fin W) ℂ => (1 + X.1ᴴ) * V :=
        continuous_const.mul continuous_id
      unfold dirN2
      exact (((((hX.pow 2).neg.mul continuous_const).sub (continuous_const.mul (hX.pow 2))).sub
        (continuous_const.mul (hX'.pow 2))).sub ((hX.mul continuous_const).mul hX)).add
        ((hX.mul continuous_const).mul hX') |>.add ((continuous_const.mul hX).mul hX')) X.2
  have cN1 : Continuous fun V => vecForm (dirN1 X.1 V) X.2 :=
    mf_continuous_vecForm (by unfold dirN1; fun_prop) X.2
  have cY1 : Continuous fun V => vecForm (dirY1 X.1 V) X.2 :=
    mf_continuous_vecForm (by unfold dirY1; fun_prop) X.2
  have cY2 : Continuous fun V => vecForm (dirY2 X.1 V) X.2 :=
    mf_continuous_vecForm (by unfold dirY2; fun_prop) X.2
  have iN2 : Integrable (fun ω => vecForm (dirN2 X.1 (gueBlock W 1 ω 0)) X.2) (μ W 1) :=
    mf_integrable cN2 2 fun V _ => (hdir V).2.2.2
  have iY2 : Integrable (fun ω => vecForm (dirY2 X.1 (gueBlock W 1 ω 0)) X.2) (μ W 1) :=
    mf_integrable cY2 2 fun V _ => (hdir V).2.2.1
  have iN1Y1 : Integrable (fun ω => vecForm (dirN1 X.1 (gueBlock W 1 ω 0)) X.2 *
      vecForm (dirY1 X.1 (gueBlock W 1 ω 0)) X.2) (μ W 1) :=
    mf_integrable (cN1.mul cY1) 2 (c := 800) fun V _ => by
      simp only [Pi.mul_apply]
      rw [norm_mul]
      calc _ ≤ (40 * (1 + ‖V‖)) * (20 * (1 + ‖V‖)) :=
            mul_le_mul (hdir V).2.1 (hdir V).1 (norm_nonneg _) (by positivity)
        _ = 800 * (1 + ‖V‖) ^ 2 := by ring
  have iY1sq : Integrable (fun ω => vecForm (dirY1 X.1 (gueBlock W 1 ω 0)) X.2 ^ 2) (μ W 1) :=
    mf_integrable (cY1.pow 2) 2 (c := 400) fun V _ => by
      simp only [Pi.pow_apply]
      rw [norm_pow]
      calc _ ≤ (20 * (1 + ‖V‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hdir V).1 2
        _ = 400 * (1 + ‖V‖) ^ 2 := by ring
  have hf1 : vecForm X.1 X.2 = obsF 1 X := by unfold obsF; rw [zpow_one]
  have iA : Integrable (fun ω => vecForm (dirN2 X.1 (gueBlock W 1 ω 0)) X.2 -
      vecForm (dirN1 X.1 (gueBlock W 1 ω 0)) X.2 * vecForm (dirY1 X.1 (gueBlock W 1 ω 0)) X.2)
      (μ W 1) := iN2.sub iN1Y1
  have iD : Integrable (fun ω => vecForm X.1 X.2 * vecForm (dirY2 X.1 (gueBlock W 1 ω 0)) X.2)
      (μ W 1) := iY2.const_mul _
  have iB : Integrable (fun ω => vecForm (dirN2 X.1 (gueBlock W 1 ω 0)) X.2 -
      vecForm (dirN1 X.1 (gueBlock W 1 ω 0)) X.2 * vecForm (dirY1 X.1 (gueBlock W 1 ω 0)) X.2 -
      vecForm X.1 X.2 * vecForm (dirY2 X.1 (gueBlock W 1 ω 0)) X.2) (μ W 1) := iA.sub iD
  have iC : Integrable (fun ω => vecForm X.1 X.2 * vecForm (dirY1 X.1 (gueBlock W 1 ω 0)) X.2 ^ 2)
      (μ W 1) := iY1sq.const_mul _
  refine ⟨by unfold mfQ; exact iB.add iC, ?_⟩
  unfold mfQ
  rw [integral_add iB iC, integral_sub iA iD, integral_sub iN2 iN1Y1,
    integral_const_mul, integral_const_mul, integral_vecForm_dirN2 hW hX,
    integral_vecForm_dirY2 hW hX, hf1]
  unfold bOdd bEven
  ring

/-- The symmetrized pointwise bound
`|(f₁'(V) + f₁'(−V))/2 + e^{−2iθ}(f₁ + t² Q)| ≤ K₁ t⁴ (1 + ‖V‖)^42`. -/
private lemma mf_pt_sym {W : ℕ} (hW : 1 ≤ W) {g E H : ℝ} (hg : 1 ≤ g) (hH : normalH E ≤ H)
    {X : State W} (hX : IsState X) {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    ‖(obsF 1 (stepState g E X V) + obsF 1 (stepState g E X (-V))) / 2 - -normalPhase E *
        (obsF 1 X + ((normalH E / g : ℝ) : ℂ) ^ 2 * mfQ X.1 V X.2)‖ ≤
      (normalH E / g) ^ 4 * (50 * (1 + H) ^ 3 * (2 * (1 + 2 * H) ^ 3 * 10 ^ 7) ^ 6) *
        (1 + ‖V‖) ^ 42 := by
  have h1 := mf_point hW hg hH hX hV
  have h2 := mf_point hW hg hH hX hV.neg
  obtain ⟨n1, n2, n3⟩ := mf_q_neg X.1 V X.2
  rw [n1, n2, n3, norm_neg] at h2
  have hq2 := mf_q2_eq X.1 V hX.2
  set t : ℝ := normalH E / g with ht
  have hs2 : (Complex.I * (t : ℂ)) ^ 2 = -(t : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq]
    ring
  set K₁ : ℝ := 50 * (1 + H) ^ 3 * (2 * (1 + 2 * H) ^ 3 * 10 ^ 7) ^ 6 with hK₁
  have eA : 50 * (1 + H) ^ 3 * (2 * (1 + 2 * H) ^ 3 * (10 * (1 + ‖V‖)) ^ 7) ^ 6 =
      K₁ * (1 + ‖V‖) ^ 42 := by
    rw [hK₁, mul_pow (10 : ℝ) (1 + ‖V‖), ← mul_assoc, mul_pow _ ((1 + ‖V‖) ^ 7), ← pow_mul]
    ring
  rw [eA] at h1 h2
  set q1 := mfq1 (mfp X.1 V X.2) (mfy X.1 V X.2)
  set q2 := mfq2 (mfp X.1 V X.2) (mfy X.1 V X.2)
  set q3 := mfq3 (mfp X.1 V X.2) (mfy X.1 V X.2)
  set s : ℂ := Complex.I * (t : ℂ) with hs
  set a := obsF 1 (stepState g E X V)
  set b := obsF 1 (stepState g E X (-V))
  have e : (a + b) / 2 - -normalPhase E * (obsF 1 X + (t : ℂ) ^ 2 * mfQ X.1 V X.2) =
      ((a - -normalPhase E * (obsF 1 X + s * q1 + s ^ 2 * q2 + s ^ 3 * q3)) +
        (b - -normalPhase E * (obsF 1 X + s * -q1 + s ^ 2 * q2 + s ^ 3 * -q3))) / 2 := by
    linear_combination (-normalPhase E) * q2 * hs2 + normalPhase E * (t : ℂ) ^ 2 * hq2
  rw [e, norm_div, Complex.norm_ofNat]
  calc _ ≤ (t ^ 4 * (K₁ * (1 + ‖V‖) ^ 42) + t ^ 4 * (K₁ * (1 + ‖V‖) ^ 42)) / 2 := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = t ^ 4 * K₁ * (1 + ‖V‖) ^ 42 := by ring

/-- (11.21) [uvg:eq:fmean]:
`P_g f_1 = -e^{-2iθ} f_1 + e^{-2iθ} h² g⁻² (B_o + B_e) + O(g⁻⁴ + g⁻²/W)`. -/
theorem transOp_obsF_one {E₀ : ℝ} (hE₀ : E₀ < 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X →
        ‖transOp g E (obsF 1) X - (-normalPhase E * obsF 1 X + normalPhase E *
            ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (bOdd X + bEven X))‖ ≤
          K * (1 / g ^ 4 + 1 / (g ^ 2 * W)) := by
  obtain ⟨K₀, hK₀, hΔ⟩ := norm_integral_dirN1_dirY1_sub_le
  obtain ⟨M, hM0, hM⟩ := mf_moment 42
  set H : ℝ := (2 * √(1 - E₀ ^ 2 / 4))⁻¹ with hH
  have hH0 : 0 ≤ H := by positivity
  set K₁ : ℝ := 50 * (1 + H) ^ 3 * (2 * (1 + 2 * H) ^ 3 * 10 ^ 7) ^ 6 with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  refine ⟨K₁ * M * H ^ 4 + K₀ * H ^ 2 + 1, by positivity, ?_⟩
  intro W hW g hg E hE X hX
  have hg0 : 0 < g := by linarith
  have hh0 := mf_normalH_nonneg E
  have hhH : normalH E ≤ H := mf_normalH_le hE₀ hE
  obtain ⟨hsym, hsi⟩ := mf_sym g E hX
  obtain ⟨hQi, hQint⟩ := mf_Q_int hW hX
  set t : ℝ := normalH E / g with ht
  have ht0 : 0 ≤ t := div_nonneg hh0 hg0.le
  -- the integrated remainder
  have hmain : ‖transOp g E (obsF 1) X - -normalPhase E * (obsF 1 X +
      (t : ℂ) ^ 2 * ∫ ω, mfQ X.1 (gueBlock W 1 ω 0) X.2 ∂(μ W 1))‖ ≤ t ^ 4 * K₁ * M := by
    have hc : -normalPhase E * (obsF 1 X + (t : ℂ) ^ 2 *
        ∫ ω, mfQ X.1 (gueBlock W 1 ω 0) X.2 ∂(μ W 1)) =
        ∫ ω, -normalPhase E * (obsF 1 X + (t : ℂ) ^ 2 * mfQ X.1 (gueBlock W 1 ω 0) X.2)
          ∂(μ W 1) := by
      rw [integral_const_mul, integral_add (integrable_const _) (hQi.const_mul _),
        integral_const_mul]
      simp
    have hI : Integrable (fun ω => -normalPhase E * (obsF 1 X + (t : ℂ) ^ 2 *
        mfQ X.1 (gueBlock W 1 ω 0) X.2)) (μ W 1) :=
      ((integrable_const _).add (hQi.const_mul _)).const_mul _
    rw [hsym, hc, ← integral_sub hsi hI]
    refine (norm_integral_le_of_norm_le ((hM W).1.const_mul (t ^ 4 * K₁))
      (Filter.Eventually.of_forall fun ω =>
        mf_pt_sym hW hg hhH hX (gueBlock_isHermitian W 1 ω 0))).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hM W).2 (by positivity)
  -- assembly
  have hΔW := hΔ W hW X hX
  have ht2 : ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) = (t : ℂ) ^ 2 := by
    rw [ht]
    push_cast
    ring
  rw [ht2]
  rw [hQint] at hmain
  set Δ := (∫ ω, vecForm (dirN1 X.1 (gueBlock W 1 ω 0)) X.2 *
      vecForm (dirY1 X.1 (gueBlock W 1 ω 0)) X.2 ∂(μ W 1)) -
    obsF 1 X * ∫ ω, vecForm (dirY1 X.1 (gueBlock W 1 ω 0)) X.2 ^ 2 ∂(μ W 1) with hΔdef
  have e : transOp g E (obsF 1) X - (-normalPhase E * obsF 1 X + normalPhase E * (t : ℂ) ^ 2 *
      (bOdd X + bEven X)) = (transOp g E (obsF 1) X - -normalPhase E * (obsF 1 X +
        (t : ℂ) ^ 2 * (-(bOdd X + bEven X) - Δ))) + normalPhase E * (t : ℂ) ^ 2 * Δ := by
    ring
  rw [e]
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ht4 : t ^ 4 ≤ H ^ 4 / g ^ 4 := by
    rw [ht, div_pow]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hh0 hhH 4) (by positivity)
  have ht2' : t ^ 2 ≤ H ^ 2 / g ^ 2 := by
    rw [ht, div_pow]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hh0 hhH 2) (by positivity)
  have hb2 : ‖normalPhase E * (t : ℂ) ^ 2 * Δ‖ ≤ H ^ 2 / g ^ 2 * (K₀ / W) := by
    rw [norm_mul, norm_mul, mf_norm_normalPhase, one_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg ht0]
    exact mul_le_mul ht2' hΔW (norm_nonneg _) (by positivity)
  have hb1 : t ^ 4 * K₁ * M ≤ H ^ 4 / g ^ 4 * K₁ * M := by gcongr
  refine (norm_add_le _ _).trans ((add_le_add (hmain.trans hb1) hb2).trans ?_)
  have e1 : H ^ 4 / g ^ 4 * K₁ * M = (K₁ * M * H ^ 4) * (1 / g ^ 4) := by ring
  have e2 : H ^ 2 / g ^ 2 * (K₀ / W) = (K₀ * H ^ 2) * (1 / (g ^ 2 * W)) := by
    field_simp
  rw [e1, e2]
  have p1 : 0 ≤ 1 / g ^ 4 := by positivity
  have p2 : 0 ≤ 1 / (g ^ 2 * W) := by positivity
  have p3 : 0 ≤ K₁ * M * H ^ 4 := by positivity
  have p4 : 0 ≤ K₀ * H ^ 2 := by positivity
  nlinarith [mul_nonneg p3 p2, mul_nonneg p4 p1]

end LSBA
