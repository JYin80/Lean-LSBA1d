import LSBA.Upper.LargeMeanM
import LSBA.Upper.LargeMeanF
import LSBA.Upper.LargeZeroNoise

/-!
# The corrected observables

The corrected observables `M` of (11.16) [uvg:eq:M] and `F` of (11.17) [uvg:eq:F], the factor `α` of
(11.22) [uvg:eq:means], the two identities `P_g M = αM + O(g⁻⁴)` and `P_g F = αF + O(g⁻²(|M| + g⁻² +
W⁻¹))`, and `|α|² ≤ 1 − 1/(2g²)` for `g ≥ √8 h_θ`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `M = m_1 - h² g⁻² (e^{-2iθ} + m_2 + 2 m_1²)/(1 + e^{-2iθ})` of (11.16) [uvg:eq:M]. -/
def corrM (g E : ℝ) {W : ℕ} (X : State W) : ℂ :=
  obsM 1 X - ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) *
    ((normalPhase E + obsM 2 X + 2 * obsM 1 X ^ 2) / (1 + normalPhase E))

/-- `F = f_1 - h² g⁻² (4 m_1 f_1 + 2 f_2 - f_1² - e^{-2iθ} f_1 f_{-1})/(1 + e^{-2iθ})` of (11.17)
[uvg:eq:F]. -/
def corrF (g E : ℝ) {W : ℕ} (X : State W) : ℂ :=
  obsF 1 X - ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) *
    ((4 * obsM 1 X * obsF 1 X + 2 * obsF 2 X - obsF 1 X ^ 2 -
      normalPhase E * obsF 1 X * obsF (-1) X) / (1 + normalPhase E))

/-- `α = -e^{-2iθ} [1 - h² g⁻² (3 + m_2)]` of (11.22) [uvg:eq:means]. -/
def driftAlpha (g E : ℝ) {W : ℕ} (X : State W) : ℂ :=
  -normalPhase E * (1 - ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (3 + obsM 2 X))

/-! ### Scalar facts: `h_θ`, `e^{-2iθ}` and `1 + e^{-2iθ}` -/

/-- `sin ϑ > 0` for `|E| < 2`. -/
private lemma lc_sin_pos {E : ℝ} (hE : |E| < 2) : 0 < Real.sin (freeAngle E) := by
  unfold freeAngle
  rw [Real.sin_arccos]
  apply Real.sqrt_pos.mpr
  have h : E ^ 2 < 4 := by
    have := sq_abs E
    nlinarith [abs_nonneg E]
  nlinarith

/-- `h_θ > 0` for `|E| < 2`. -/
private lemma lc_normalH_pos {E : ℝ} (hE : |E| < 2) : 0 < normalH E := by
  unfold normalH
  have := lc_sin_pos hE
  positivity

/-- `h_θ ≥ 1/2` for `|E| < 2`. -/
private lemma lc_half_le_normalH {E : ℝ} (hE : |E| < 2) : 1 / 2 ≤ normalH E := by
  unfold normalH
  have h1 := lc_sin_pos hE
  have h2 := Real.sin_le_one (freeAngle E)
  rw [one_div]
  exact inv_anti₀ (by positivity) (by linarith)

/-- `|1 + e^{-2iθ}| = 2 sin ϑ = h_θ⁻¹` for `|E| < 2`. -/
private lemma lc_norm_one_add {E : ℝ} (hE : |E| < 2) : ‖1 + normalPhase E‖ = (normalH E)⁻¹ := by
  have hs := lc_sin_pos hE
  have h1 : 1 + normalPhase E = -(Complex.exp (freeAngle E * Complex.I) *
      (2 * Complex.I * (Real.sin (freeAngle E) : ℂ))) := by
    unfold normalPhase
    rw [Complex.ofReal_sin, Complex.sin]
    set z : ℂ := Complex.exp ((freeAngle E : ℂ) * Complex.I) with hz
    set w : ℂ := Complex.exp (-(freeAngle E : ℂ) * Complex.I) with hw
    have h2 : Complex.exp (2 * ((freeAngle E : ℂ) * Complex.I)) = z * z := by
      rw [hz, ← Complex.exp_add]; ring_nf
    have h3 : w * z = 1 := by
      rw [hw, hz, ← Complex.exp_add]; simp
    rw [h2]
    linear_combination (-1 : ℂ) * h3 + (z * w - z ^ 2) * Complex.I_sq
  rw [h1, norm_neg, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  simp only [Complex.norm_I, Complex.norm_ofNat]
  unfold normalH
  rw [inv_inv, mul_one]

/-! ### Bounded measurable functions of states and the one-step mean -/

private lemma lc_measurable_gb (W : ℕ) : Measurable fun ω : Ω W 1 => gueBlock W 1 ω 0 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma lc_measurable_inv {W : ℕ} :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => X⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have h : (fun X : Matrix (Fin W) (Fin W) ℂ => X⁻¹ i j) =
      fun X => (X.det)⁻¹ * X.adjugate i j := by
    funext X
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [h]
  have hd : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => X.det := continuous_id.matrix_det
  have ha : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => X.adjugate i j :=
    (continuous_id.matrix_adjugate).matrix_elem i j
  exact hd.measurable.inv.mul ha.measurable

private lemma lc_measurable_zpow {W : ℕ} (k : ℤ) :
    Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A ^ k := by
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact (continuous_id.pow n).measurable
  | negSucc n =>
    simp only [zpow_negSucc]
    exact lc_measurable_inv.comp (continuous_id.pow _).measurable

private lemma lc_measurable_obsM (W : ℕ) (k : ℤ) : Measurable fun X : State W => obsM k X :=
  measurable_const.mul ((continuous_id.matrix_trace).measurable.comp
    ((lc_measurable_zpow k).comp measurable_fst))

private lemma lc_cont_vecForm {W : ℕ} :
    Continuous fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) => vecForm q.1 q.2 := by
  have hc : Continuous (fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) =>
      Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) q.1 q.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM
  exact continuous_snd.inner hc

private lemma lc_measurable_obsF (W : ℕ) (k : ℤ) : Measurable fun X : State W => obsF k X := by
  unfold obsF
  have h1 : Measurable fun X : State W => (X.1 ^ k, X.2) :=
    ((lc_measurable_zpow k).comp measurable_fst).prodMk measurable_snd
  have h2 := (lc_cont_vecForm (W := W)).measurable.comp h1
  exact h2

/-- A bounded measurable function of the states. -/
private def LcTame {W : ℕ} (φ : State W → ℂ) : Prop :=
  Measurable φ ∧ ∃ B : ℝ, ∀ Y : State W, IsState Y → ‖φ Y‖ ≤ B

private lemma lc_tame_const {W : ℕ} (c : ℂ) : LcTame (fun _ : State W => c) :=
  ⟨measurable_const, ‖c‖, fun _ _ => le_rfl⟩

private lemma lc_tame_add {W : ℕ} {φ ψ : State W → ℂ} (hφ : LcTame φ) (hψ : LcTame ψ) :
    LcTame (fun Y => φ Y + ψ Y) := by
  obtain ⟨m1, B1, b1⟩ := hφ
  obtain ⟨m2, B2, b2⟩ := hψ
  exact ⟨m1.add m2, B1 + B2, fun Y hY => (norm_add_le _ _).trans (add_le_add (b1 Y hY) (b2 Y hY))⟩

private lemma lc_tame_sub {W : ℕ} {φ ψ : State W → ℂ} (hφ : LcTame φ) (hψ : LcTame ψ) :
    LcTame (fun Y => φ Y - ψ Y) := by
  obtain ⟨m1, B1, b1⟩ := hφ
  obtain ⟨m2, B2, b2⟩ := hψ
  exact ⟨m1.sub m2, B1 + B2, fun Y hY => (norm_sub_le _ _).trans (add_le_add (b1 Y hY) (b2 Y hY))⟩

private lemma lc_tame_mul {W : ℕ} {φ ψ : State W → ℂ} (hφ : LcTame φ) (hψ : LcTame ψ) :
    LcTame (fun Y => φ Y * ψ Y) := by
  obtain ⟨m1, B1, b1⟩ := hφ
  obtain ⟨m2, B2, b2⟩ := hψ
  refine ⟨m1.mul m2, |B1| * |B2|, fun Y hY => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((b1 Y hY).trans (le_abs_self _)) ((b2 Y hY).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

private lemma lc_tame_obsM {W : ℕ} (k : ℤ) : LcTame (fun X : State W => obsM k X) :=
  ⟨lc_measurable_obsM W k, 1, fun _ hY => norm_obsM_le_one k hY⟩

private lemma lc_tame_obsF {W : ℕ} (k : ℤ) : LcTame (fun X : State W => obsF k X) :=
  ⟨lc_measurable_obsF W k, 1, fun _ hY => norm_obsF_le_one k hY⟩

private lemma lc_integrable (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {φ : State W → ℂ} (hφ : LcTame φ) :
    Integrable (fun ω : Ω W 1 => φ (stepState g E X (gueBlock W 1 ω 0))) (μ W 1) := by
  obtain ⟨hm, B, hb⟩ := hφ
  have hS : Measurable fun ω : Ω W 1 => (X, gueBlock W 1 ω 0) :=
    Measurable.prodMk measurable_const (lc_measurable_gb W)
  have h1 := hm.comp ((measurable_stepState g E W).comp hS)
  exact Integrable.of_bound h1.aestronglyMeasurable B (Filter.Eventually.of_forall fun ω =>
    hb _ (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)))

private lemma lc_transOp_add (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {φ ψ : State W → ℂ} (hφ : LcTame φ) (hψ : LcTame ψ) :
    transOp g E (fun Y => φ Y + ψ Y) X = transOp g E φ X + transOp g E ψ X :=
  integral_add (lc_integrable g E hX hφ) (lc_integrable g E hX hψ)

private lemma lc_transOp_sub (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {φ ψ : State W → ℂ} (hφ : LcTame φ) (hψ : LcTame ψ) :
    transOp g E (fun Y => φ Y - ψ Y) X = transOp g E φ X - transOp g E ψ X :=
  integral_sub (lc_integrable g E hX hφ) (lc_integrable g E hX hψ)

private lemma lc_transOp_const_mul (g E : ℝ) {W : ℕ} (X : State W) (c : ℂ) (φ : State W → ℂ) :
    transOp g E (fun Y => c * φ Y) X = c * transOp g E φ X :=
  integral_const_mul c _

private lemma lc_transOp_const (g E : ℝ) {W : ℕ} (X : State W) (c : ℂ) :
    transOp g E (fun _ : State W => c) X = c := by
  unfold transOp
  simp

private lemma lc_transOp_congr (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {φ ψ : State W → ℂ} (h : ∀ Y : State W, IsState Y → φ Y = ψ Y) :
    transOp g E φ X = transOp g E ψ X :=
  integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    h _ (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)))


/-- `P_g` of the expression defining `M` in (11.16) [uvg:eq:M], in terms of `P_g m_1`,
`P_g m_2` and `P_g (m_1²)`; `r` stands for `h² g⁻² (1 + e^{-2iθ})⁻¹`. -/
private lemma lc_transOp_M (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) (r e : ℂ) :
    transOp g E (fun Y => obsM 1 Y - r * (e + obsM 2 Y + 2 * (obsM 1 Y * obsM 1 Y))) X =
      transOp g E (obsM 1) X - r * (e + transOp g E (obsM 2) X +
        2 * transOp g E (fun Y => obsM 1 Y * obsM 1 Y) X) := by
  have t1 : LcTame (fun Y : State W => obsM 1 Y) := lc_tame_obsM 1
  have t2 : LcTame (fun Y : State W => obsM 2 Y) := lc_tame_obsM 2
  have t3 : LcTame (fun Y : State W => obsM 1 Y * obsM 1 Y) := lc_tame_mul t1 t1
  have t4 : LcTame (fun Y : State W => e + obsM 2 Y) := lc_tame_add (lc_tame_const e) t2
  have t5 : LcTame (fun Y : State W => 2 * (obsM 1 Y * obsM 1 Y)) :=
    lc_tame_mul (lc_tame_const 2) t3
  have t6 : LcTame (fun Y : State W => e + obsM 2 Y + 2 * (obsM 1 Y * obsM 1 Y)) :=
    lc_tame_add t4 t5
  have t7 : LcTame (fun Y : State W => r * (e + obsM 2 Y + 2 * (obsM 1 Y * obsM 1 Y))) :=
    lc_tame_mul (lc_tame_const r) t6
  rw [lc_transOp_sub g E hX t1 t7, lc_transOp_const_mul, lc_transOp_add g E hX t4 t5,
    lc_transOp_add g E hX (lc_tame_const e) t2, lc_transOp_const_mul, lc_transOp_const]

/-- The algebraic identity behind (11.22) [uvg:eq:means], first line: the terms of order
`h² g⁻²` cancel exactly, using `r (1 + e^{-2iθ}) = h² g⁻²`. -/
private lemma lc_alg_M (e q r m n a b c : ℂ) (hr : r * (1 + e) = q) :
    (a - r * (e + c + 2 * b)) - (-e * (1 - q * (3 + n))) * (m - r * (e + n + 2 * m ^ 2)) =
      (a - (-e * m + e * q * (1 + m) * (1 + 2 * m + n))) -
        r * ((c - e ^ 2 * n) + 2 * (b - e ^ 2 * (m * m))) +
        e * q * (3 + n) * r * (e + n + 2 * m ^ 2) := by
  linear_combination (-e * (1 + n + 2 * m ^ 2)) * hr


private lemma lc_normalH_le {E₀ E : ℝ} (hE₀ : E₀ < 2) (hE : |E| ≤ E₀) :
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

private lemma lc_norm_normalPhase (E : ℝ) : ‖normalPhase E‖ = 1 := by
  unfold normalPhase
  rw [norm_neg, show 2 * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma lc_norm_q {E : ℝ} {g : ℝ} (hE : |E| < 2) :
    ‖((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ)‖ = normalH E ^ 2 / g ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  have := lc_normalH_pos hE
  positivity

private lemma lc_norm_r {E : ℝ} {g : ℝ} (hE : |E| < 2) :
    ‖((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (1 + normalPhase E)⁻¹‖ = normalH E ^ 3 / g ^ 2 := by
  rw [norm_mul, lc_norm_q hE, norm_inv, lc_norm_one_add hE, inv_inv]
  ring

private lemma lc_one_add_ne {E : ℝ} (hE : |E| < 2) : 1 + normalPhase E ≠ 0 := by
  intro h0
  have h1 := lc_norm_one_add hE
  rw [h0, norm_zero] at h1
  exact (inv_pos.mpr (lc_normalH_pos hE)).ne h1

private lemma lc_zpow_two (E : ℝ) (k l : ℤ) (h : k + l = 2) :
    (-normalPhase E) ^ (k + l) = normalPhase E ^ 2 := by
  rw [h, zpow_ofNat, neg_sq]

private lemma lc_norm_comb (A r B C D : ℂ) :
    ‖A - r * (B + 2 * C) + D‖ ≤ ‖A‖ + ‖r‖ * (‖B‖ + 2 * ‖C‖) + ‖D‖ := by
  have h1 : ‖A - r * (B + 2 * C) + D‖ ≤ ‖A - r * (B + 2 * C)‖ + ‖D‖ := norm_add_le _ _
  have h2 : ‖A - r * (B + 2 * C)‖ ≤ ‖A‖ + ‖r * (B + 2 * C)‖ := norm_sub_le _ _
  have h3 : ‖r * (B + 2 * C)‖ ≤ ‖r‖ * (‖B‖ + 2 * ‖C‖) := by
    rw [norm_mul]
    gcongr
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_ofNat]
  linarith

private lemma lc_norm_T {W : ℕ} {E : ℝ} {X : State W} (hX : IsState X) :
    ‖normalPhase E + obsM 2 X + 2 * obsM 1 X ^ 2‖ ≤ 4 := by
  have h1 := norm_obsM_le_one 1 hX
  have h2 := norm_obsM_le_one 2 hX
  have h3 := lc_norm_normalPhase E
  calc ‖normalPhase E + obsM 2 X + 2 * obsM 1 X ^ 2‖
      ≤ ‖normalPhase E + obsM 2 X‖ + ‖2 * obsM 1 X ^ 2‖ := norm_add_le _ _
    _ ≤ (‖normalPhase E‖ + ‖obsM 2 X‖) + ‖2 * obsM 1 X ^ 2‖ := by gcongr; exact norm_add_le _ _
    _ ≤ 4 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat]
      have : ‖obsM 1 X‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
      linarith

private lemma lc_norm_s {W : ℕ} {X : State W} (hX : IsState X) : ‖(3 : ℂ) + obsM 2 X‖ ≤ 4 := by
  have h2 := norm_obsM_le_one 2 hX
  calc ‖(3 : ℂ) + obsM 2 X‖ ≤ ‖(3 : ℂ)‖ + ‖obsM 2 X‖ := norm_add_le _ _
    _ ≤ 4 := by rw [Complex.norm_ofNat]; linarith

/-- `P_g` of the expression defining `F` in (11.17) [uvg:eq:F], in terms of `P_g` of `f_1`,
`m_1 f_1`, `f_2`, `f_1²` and `f_1 f_{-1}`; `r` stands for `h² g⁻² (1 + e^{-2iθ})⁻¹`. -/
private lemma lc_transOp_F (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) (r e : ℂ) :
    transOp g E (fun Y => obsF 1 Y - r * (4 * (obsM 1 Y * obsF 1 Y) + 2 * obsF 2 Y -
      obsF 1 Y * obsF 1 Y - e * (obsF 1 Y * obsF (-1) Y))) X =
      transOp g E (obsF 1) X - r * (4 * transOp g E (fun Y => obsM 1 Y * obsF 1 Y) X +
        2 * transOp g E (obsF 2) X - transOp g E (fun Y => obsF 1 Y * obsF 1 Y) X -
        e * transOp g E (fun Y => obsF 1 Y * obsF (-1) Y) X) := by
  have t1 : LcTame (fun Y : State W => obsF 1 Y) := lc_tame_obsF 1
  have t2 : LcTame (fun Y : State W => obsF 2 Y) := lc_tame_obsF 2
  have t3 : LcTame (fun Y : State W => obsM 1 Y * obsF 1 Y) := lc_tame_mul (lc_tame_obsM 1) t1
  have t4 : LcTame (fun Y : State W => obsF 1 Y * obsF 1 Y) := lc_tame_mul t1 t1
  have t5 : LcTame (fun Y : State W => obsF 1 Y * obsF (-1) Y) := lc_tame_mul t1 (lc_tame_obsF (-1))
  have u1 : LcTame (fun Y : State W => 4 * (obsM 1 Y * obsF 1 Y)) :=
    lc_tame_mul (lc_tame_const 4) t3
  have u2 : LcTame (fun Y : State W => 2 * obsF 2 Y) := lc_tame_mul (lc_tame_const 2) t2
  have u3 : LcTame (fun Y : State W => e * (obsF 1 Y * obsF (-1) Y)) :=
    lc_tame_mul (lc_tame_const e) t5
  have v1 : LcTame (fun Y : State W => 4 * (obsM 1 Y * obsF 1 Y) + 2 * obsF 2 Y) :=
    lc_tame_add u1 u2
  have v2 : LcTame (fun Y : State W => 4 * (obsM 1 Y * obsF 1 Y) + 2 * obsF 2 Y -
      obsF 1 Y * obsF 1 Y) := lc_tame_sub v1 t4
  have v3 : LcTame (fun Y : State W => 4 * (obsM 1 Y * obsF 1 Y) + 2 * obsF 2 Y -
      obsF 1 Y * obsF 1 Y - e * (obsF 1 Y * obsF (-1) Y)) := lc_tame_sub v2 u3
  have v4 : LcTame (fun Y : State W => r * (4 * (obsM 1 Y * obsF 1 Y) + 2 * obsF 2 Y -
      obsF 1 Y * obsF 1 Y - e * (obsF 1 Y * obsF (-1) Y))) := lc_tame_mul (lc_tame_const r) v3
  rw [lc_transOp_sub g E hX t1 v4, lc_transOp_const_mul, lc_transOp_sub g E hX v2 u3,
    lc_transOp_sub g E hX v1 t4, lc_transOp_add g E hX u1 u2, lc_transOp_const_mul,
    lc_transOp_const_mul, lc_transOp_const_mul]

/-- The algebraic identity behind (11.22) [uvg:eq:means], second line: the terms of order
`h² g⁻²` cancel except `e^{-2iθ} h² g⁻² (2 m_1 f_2 - m_1 f_1² - m_{-1} f_1 f_{-1})`, using
`r (1 + e^{-2iθ}) = h² g⁻²`. -/
private lemma lc_alg_F (e q r m mm n f f2 fm a0 pa pb pc pd : ℂ) (hr : r * (1 + e) = q) :
    (a0 - r * (4 * pa + 2 * pb - pc - e * pd)) -
        (-e * (1 - q * (3 + n))) *
          (f - r * (4 * (m * f) + 2 * f2 - f * f - e * (f * fm))) =
      (a0 - (-e * f + e * q * (((3 + n) * f + 2 * m * f2 - f * (m * f + mm * fm)) +
          (4 * m * f + 2 * f2 - f ^ 2 - f * fm)))) -
        r * (4 * (pa - e ^ 2 * (m * f)) + 2 * (pb - e ^ 2 * f2) - (pc - e ^ 2 * (f * f)) -
          e * (pd - f * fm)) +
        e * q * (2 * m * f2 - m * f * f - mm * f * fm) +
        e * q * (3 + n) * r * (4 * (m * f) + 2 * f2 - f * f - e * (f * fm)) := by
  linear_combination (-e * (4 * m * f + 2 * f2 - f ^ 2 - f * fm)) * hr

private lemma lc_norm_comb_F (A r B C D E' F₁ F₂ e : ℂ) :
    ‖A - r * (4 * B + 2 * C - D - e * E') + F₁ + F₂‖ ≤
      ‖A‖ + ‖r‖ * (4 * ‖B‖ + 2 * ‖C‖ + ‖D‖ + ‖e‖ * ‖E'‖) + ‖F₁‖ + ‖F₂‖ := by
  have h1 : ‖A - r * (4 * B + 2 * C - D - e * E') + F₁ + F₂‖ ≤
      ‖A - r * (4 * B + 2 * C - D - e * E')‖ + ‖F₁‖ + ‖F₂‖ := by
    have := norm_add_le (A - r * (4 * B + 2 * C - D - e * E') + F₁) F₂
    have := norm_add_le (A - r * (4 * B + 2 * C - D - e * E')) F₁
    linarith
  have h2 : ‖A - r * (4 * B + 2 * C - D - e * E')‖ ≤ ‖A‖ + ‖r * (4 * B + 2 * C - D - e * E')‖ :=
    norm_sub_le _ _
  have h3 : ‖r * (4 * B + 2 * C - D - e * E')‖ ≤
      ‖r‖ * (4 * ‖B‖ + 2 * ‖C‖ + ‖D‖ + ‖e‖ * ‖E'‖) := by
    rw [norm_mul]
    gcongr
    calc ‖4 * B + 2 * C - D - e * E'‖
        ≤ ‖4 * B + 2 * C - D‖ + ‖e * E'‖ := norm_sub_le _ _
      _ ≤ (‖4 * B + 2 * C‖ + ‖D‖) + ‖e * E'‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ((‖4 * B‖ + ‖2 * C‖) + ‖D‖) + ‖e * E'‖ := by gcongr; exact norm_add_le _ _
      _ = 4 * ‖B‖ + 2 * ‖C‖ + ‖D‖ + ‖e‖ * ‖E'‖ := by
        rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat, norm_mul]
  linarith

private lemma lc_norm_Bx {m mm f f2 fm : ℂ} (hmm : ‖mm‖ = ‖m‖) (hf : ‖f‖ ≤ 1) (hf2 : ‖f2‖ ≤ 1)
    (hfm : ‖fm‖ ≤ 1) : ‖2 * m * f2 - m * f * f - mm * f * fm‖ ≤ 4 * ‖m‖ := by
  have hm := norm_nonneg m
  have h1 : ‖2 * m * f2‖ ≤ 2 * ‖m‖ := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    nlinarith [norm_nonneg f2]
  have h2 : ‖m * f * f‖ ≤ ‖m‖ := by
    rw [norm_mul, norm_mul]
    have := norm_nonneg f
    calc ‖m‖ * ‖f‖ * ‖f‖ ≤ ‖m‖ * 1 * 1 := by gcongr
      _ = ‖m‖ := by ring
  have h3 : ‖mm * f * fm‖ ≤ ‖m‖ := by
    rw [norm_mul, norm_mul, hmm]
    have := norm_nonneg f
    have := norm_nonneg fm
    calc ‖m‖ * ‖f‖ * ‖fm‖ ≤ ‖m‖ * 1 * 1 := by gcongr
      _ = ‖m‖ := by ring
  calc ‖2 * m * f2 - m * f * f - mm * f * fm‖
      ≤ ‖2 * m * f2 - m * f * f‖ + ‖mm * f * fm‖ := norm_sub_le _ _
    _ ≤ (‖2 * m * f2‖ + ‖m * f * f‖) + ‖mm * f * fm‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ 4 * ‖m‖ := by linarith

private lemma lc_mul_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a‖ * ‖b‖ ≤ 1 :=
  (mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

private lemma lc_norm_NF {W : ℕ} {E : ℝ} {X : State W} (hX : IsState X) :
    ‖4 * (obsM 1 X * obsF 1 X) + 2 * obsF 2 X - obsF 1 X * obsF 1 X -
      normalPhase E * (obsF 1 X * obsF (-1) X)‖ ≤ 8 := by
  have h1 := norm_obsM_le_one 1 hX
  have h2 := norm_obsF_le_one 1 hX
  have h3 := norm_obsF_le_one 2 hX
  have h4 := norm_obsF_le_one (-1) hX
  have h5 := lc_norm_normalPhase E
  have hp : ‖obsM 1 X * obsF 1 X‖ ≤ 1 := by
    rw [norm_mul]; exact lc_mul_le_one h1 h2
  have hq : ‖obsF 1 X * obsF 1 X‖ ≤ 1 := by
    rw [norm_mul]; exact lc_mul_le_one h2 h2
  have hs : ‖normalPhase E * (obsF 1 X * obsF (-1) X)‖ ≤ 1 := by
    rw [norm_mul, h5, one_mul, norm_mul]; exact lc_mul_le_one h2 h4
  calc ‖4 * (obsM 1 X * obsF 1 X) + 2 * obsF 2 X - obsF 1 X * obsF 1 X -
        normalPhase E * (obsF 1 X * obsF (-1) X)‖
      ≤ ‖4 * (obsM 1 X * obsF 1 X) + 2 * obsF 2 X - obsF 1 X * obsF 1 X‖ +
        ‖normalPhase E * (obsF 1 X * obsF (-1) X)‖ := norm_sub_le _ _
    _ ≤ (‖4 * (obsM 1 X * obsF 1 X) + 2 * obsF 2 X‖ + ‖obsF 1 X * obsF 1 X‖) +
        ‖normalPhase E * (obsF 1 X * obsF (-1) X)‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((‖4 * (obsM 1 X * obsF 1 X)‖ + ‖2 * obsF 2 X‖) + ‖obsF 1 X * obsF 1 X‖) +
        ‖normalPhase E * (obsF 1 X * obsF (-1) X)‖ := by gcongr; exact norm_add_le _ _
    _ ≤ 8 := by
      have e1 : ‖(4 : ℂ) * (obsM 1 X * obsF 1 X)‖ ≤ 4 := by
        rw [norm_mul, Complex.norm_ofNat]; linarith
      have e2 : ‖(2 : ℂ) * obsF 2 X‖ ≤ 2 := by
        rw [norm_mul, Complex.norm_ofNat]; linarith
      linarith

private lemma lc_final_F {K₅ S H h a w x : ℝ} (hK₅ : 0 ≤ K₅) (hS : 0 ≤ S) (h0 : 0 ≤ h)
    (hH : h ≤ H) (ha : 0 ≤ a) (hw : 0 ≤ w) (hx : 0 ≤ x) :
    K₅ * (a ^ 2 + a * w) + (h ^ 3 * a) * (S * a) + h ^ 2 * a * (4 * (x + 4 * (h ^ 3 * a))) +
        h ^ 2 * a * 4 * (h ^ 3 * a) * 8 ≤
      (K₅ + H ^ 3 * S + 4 * H ^ 2 + 48 * H ^ 5 + 1) * a * (x + a + w) := by
  have hh3 : h ^ 3 ≤ H ^ 3 := pow_le_pow_left₀ h0 hH 3
  have hh2 : h ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ h0 hH 2
  have hh5 : h ^ 5 ≤ H ^ 5 := pow_le_pow_left₀ h0 hH 5
  have hH0 : 0 ≤ H := h0.trans hH
  calc K₅ * (a ^ 2 + a * w) + (h ^ 3 * a) * (S * a) + h ^ 2 * a * (4 * (x + 4 * (h ^ 3 * a))) +
        h ^ 2 * a * 4 * (h ^ 3 * a) * 8
      = K₅ * a ^ 2 + K₅ * (a * w) + h ^ 3 * S * a ^ 2 + 4 * h ^ 2 * (a * x) +
        48 * h ^ 5 * a ^ 2 := by ring
    _ ≤ K₅ * a ^ 2 + K₅ * (a * w) + H ^ 3 * S * a ^ 2 + 4 * H ^ 2 * (a * x) +
        48 * H ^ 5 * a ^ 2 := by gcongr
    _ ≤ (K₅ + H ^ 3 * S + 4 * H ^ 2 + 48 * H ^ 5 + 1) * a * (x + a + w) := by
      have e : (K₅ + H ^ 3 * S + 4 * H ^ 2 + 48 * H ^ 5 + 1) * a * (x + a + w) -
          (K₅ * a ^ 2 + K₅ * (a * w) + H ^ 3 * S * a ^ 2 + 4 * H ^ 2 * (a * x) +
            48 * H ^ 5 * a ^ 2) =
          (K₅ + H ^ 3 * S + 48 * H ^ 5 + 1) * (a * x) + (4 * H ^ 2 + 1) * a ^ 2 +
            (H ^ 3 * S + 4 * H ^ 2 + 48 * H ^ 5 + 1) * (a * w) := by ring
      have : 0 ≤ (K₅ + H ^ 3 * S + 48 * H ^ 5 + 1) * (a * x) + (4 * H ^ 2 + 1) * a ^ 2 +
            (H ^ 3 * S + 4 * H ^ 2 + 48 * H ^ 5 + 1) * (a * w) := by positivity
      linarith

/-- (11.22) [uvg:eq:means], first identity: `P_g M = α M + O(g⁻⁴)`. -/
theorem transOp_corrM {E₀ : ℝ} (hE₀ : E₀ < 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X →
        ‖transOp g E (corrM g E) X - driftAlpha g E X * corrM g E X‖ ≤ K / g ^ 4 := by
  obtain ⟨K₁, hK₁, h1⟩ := transOp_obsM_one hE₀
  obtain ⟨K₂, hK₂, h2⟩ := transOp_obsM_mul_obsM hE₀ 1 1
  obtain ⟨K₃, hK₃, h3⟩ := transOp_obsM_mul_obsM hE₀ 2 0
  set H : ℝ := (2 * √(1 - E₀ ^ 2 / 4))⁻¹ with hH
  have hH0 : 0 ≤ H := by positivity
  refine ⟨K₁ + H ^ 3 * (K₃ + 2 * K₂) + 16 * H ^ 5 + 1, by positivity, ?_⟩
  intro W hW g hg E hE X hX
  have hg0 : 0 < g := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have hE2 : |E| < 2 := lt_of_le_of_lt hE hE₀
  have hh0 := lc_normalH_pos hE2
  have hhH : normalH E ≤ H := lc_normalH_le hE₀ hE
  obtain ⟨r, hrdef⟩ : ∃ r : ℂ, r = ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (1 + normalPhase E)⁻¹ :=
    ⟨_, rfl⟩
  have hr : r * (1 + normalPhase E) = ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) := by
    rw [hrdef]
    exact inv_mul_cancel_right₀ (lc_one_add_ne hE2) _
  have hrn : ‖r‖ = normalH E ^ 3 / g ^ 2 := by rw [hrdef]; exact lc_norm_r hE2
  have hfun : (corrM g E : State W → ℂ) = fun Y => obsM 1 Y -
      r * (normalPhase E + obsM 2 Y + 2 * (obsM 1 Y * obsM 1 Y)) := by
    funext Y
    unfold corrM
    rw [hrdef, div_eq_mul_inv]
    ring
  have hcorr : corrM g E X = obsM 1 X - r * (normalPhase E + obsM 2 X + 2 * obsM 1 X ^ 2) := by
    rw [hfun]
    ring
  have hP : transOp g E (corrM g E) X = transOp g E (obsM 1) X -
      r * (normalPhase E + transOp g E (obsM 2) X +
        2 * transOp g E (fun Y => obsM 1 Y * obsM 1 Y) X) := by
    rw [hfun]
    exact lc_transOp_M g E hX r _
  have hm0 : ∀ Y : State W, IsState Y → obsM 0 Y = 1 := fun Y hY => (obsM_zero_neg hW hY 0).1
  have hc : transOp g E (fun Y => obsM 2 Y * obsM 0 Y) X = transOp g E (obsM 2) X :=
    lc_transOp_congr g E hX fun Y hY => by rw [hm0 Y hY, mul_one]
  have e1 := h1 W hW g hg E hE X hX
  have e2 := h2 W hW g hg E hE X hX
  have e3 := h3 W hW g hg E hE X hX
  rw [hc, hm0 X hX, mul_one, lc_zpow_two E 2 0 (by norm_num)] at e3
  rw [lc_zpow_two E 1 1 (by norm_num)] at e2
  have hkey := lc_alg_M (normalPhase E) ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) r (obsM 1 X) (obsM 2 X)
    (transOp g E (obsM 1) X) (transOp g E (fun Y => obsM 1 Y * obsM 1 Y) X)
    (transOp g E (obsM 2) X) hr
  unfold driftAlpha
  rw [hP, hcorr, hkey]
  refine (lc_norm_comb _ _ _ _ _).trans ?_
  have hD : ‖normalPhase E * ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (3 + obsM 2 X) * r *
      (normalPhase E + obsM 2 X + 2 * obsM 1 X ^ 2)‖ ≤
      1 * (normalH E ^ 2 / g ^ 2) * 4 * (normalH E ^ 3 / g ^ 2) * 4 := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, lc_norm_normalPhase, lc_norm_q hE2, hrn]
    gcongr
    · exact lc_norm_s hX
    · exact lc_norm_T hX
  have hnum : ‖transOp g E (obsM 1) X -
        (-normalPhase E * obsM 1 X +
          normalPhase E * ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (1 + obsM 1 X) *
            (1 + 2 * obsM 1 X + obsM 2 X))‖ +
      ‖r‖ * (‖transOp g E (obsM 2) X - normalPhase E ^ 2 * obsM 2 X‖ +
        2 * ‖transOp g E (fun Y => obsM 1 Y * obsM 1 Y) X -
          normalPhase E ^ 2 * (obsM 1 X * obsM 1 X)‖) +
      1 * (normalH E ^ 2 / g ^ 2) * 4 * (normalH E ^ 3 / g ^ 2) * 4 ≤
      K₁ / g ^ 4 + (normalH E ^ 3 / g ^ 2) * (K₃ / g ^ 2 + 2 * (K₂ / g ^ 2)) +
        1 * (normalH E ^ 2 / g ^ 2) * 4 * (normalH E ^ 3 / g ^ 2) * 4 := by
    rw [hrn]
    gcongr
  have hfin : K₁ / g ^ 4 + (normalH E ^ 3 / g ^ 2) * (K₃ / g ^ 2 + 2 * (K₂ / g ^ 2)) +
        1 * (normalH E ^ 2 / g ^ 2) * 4 * (normalH E ^ 3 / g ^ 2) * 4 ≤
      (K₁ + H ^ 3 * (K₃ + 2 * K₂) + 16 * H ^ 5 + 1) / g ^ 4 := by
    have hrw : K₁ / g ^ 4 + (normalH E ^ 3 / g ^ 2) * (K₃ / g ^ 2 + 2 * (K₂ / g ^ 2)) +
        1 * (normalH E ^ 2 / g ^ 2) * 4 * (normalH E ^ 3 / g ^ 2) * 4 =
        (K₁ + normalH E ^ 3 * (K₃ + 2 * K₂) + 16 * normalH E ^ 5) / g ^ 4 := by
      field_simp
      ring
    rw [hrw]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h3 : normalH E ^ 3 ≤ H ^ 3 := pow_le_pow_left₀ hh0.le hhH 3
    have h5 : normalH E ^ 5 ≤ H ^ 5 := pow_le_pow_left₀ hh0.le hhH 5
    nlinarith [mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ K₃ + 2 * K₂)]
  exact (add_le_add le_rfl hD).trans (hnum.trans hfin)

/-- (11.22) [uvg:eq:means], second identity: `P_g F = α F + O(g⁻² (|M| + g⁻² + W⁻¹))`. -/
theorem transOp_corrF {E₀ : ℝ} (hE₀ : E₀ < 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X →
        ‖transOp g E (corrF g E) X - driftAlpha g E X * corrF g E X‖ ≤
          K / g ^ 2 * (‖corrM g E X‖ + 1 / g ^ 2 + 1 / W) := by
  obtain ⟨K₅, hK₅, h5⟩ := transOp_obsF_one hE₀
  obtain ⟨Ka, hKa, ha⟩ := transOp_obsM_mul_obsF hE₀ 1 1
  obtain ⟨Kb, hKb, hb⟩ := transOp_obsM_mul_obsF hE₀ 0 2
  obtain ⟨Kc, hKc, hc⟩ := transOp_obsF_mul_obsF hE₀ 1 1
  obtain ⟨Kd, hKd, hd⟩ := transOp_obsF_mul_obsF hE₀ 1 (-1)
  set H : ℝ := (2 * √(1 - E₀ ^ 2 / 4))⁻¹ with hH
  have hH0 : 0 ≤ H := by positivity
  refine ⟨K₅ + H ^ 3 * (4 * Ka + 2 * Kb + Kc + Kd) + 4 * H ^ 2 + 48 * H ^ 5 + 1,
    by positivity, ?_⟩
  intro W hW g hg E hE X hX
  have hg0 : 0 < g := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have hE2 : |E| < 2 := lt_of_le_of_lt hE hE₀
  have hh0 := lc_normalH_pos hE2
  have hhH : normalH E ≤ H := lc_normalH_le hE₀ hE
  obtain ⟨r, hrdef⟩ : ∃ r : ℂ, r = ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (1 + normalPhase E)⁻¹ :=
    ⟨_, rfl⟩
  have hr : r * (1 + normalPhase E) = ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) := by
    rw [hrdef]
    exact inv_mul_cancel_right₀ (lc_one_add_ne hE2) _
  have hrn : ‖r‖ = normalH E ^ 3 * (1 / g ^ 2) := by
    rw [hrdef, lc_norm_r hE2]; ring
  have hfun : (corrF g E : State W → ℂ) = fun Y => obsF 1 Y - r * (4 * (obsM 1 Y * obsF 1 Y) +
      2 * obsF 2 Y - obsF 1 Y * obsF 1 Y - normalPhase E * (obsF 1 Y * obsF (-1) Y)) := by
    funext Y
    unfold corrF
    rw [hrdef, div_eq_mul_inv]
    ring
  have hcorrF : corrF g E X = obsF 1 X - r * (4 * (obsM 1 X * obsF 1 X) + 2 * obsF 2 X -
      obsF 1 X * obsF 1 X - normalPhase E * (obsF 1 X * obsF (-1) X)) := by
    rw [hfun]
  have hcorrM : corrM g E X = obsM 1 X - r * (normalPhase E + obsM 2 X + 2 * obsM 1 X ^ 2) := by
    unfold corrM
    rw [hrdef, div_eq_mul_inv]
    ring
  have hP : transOp g E (corrF g E) X = transOp g E (obsF 1) X -
      r * (4 * transOp g E (fun Y => obsM 1 Y * obsF 1 Y) X + 2 * transOp g E (obsF 2) X -
        transOp g E (fun Y => obsF 1 Y * obsF 1 Y) X -
        normalPhase E * transOp g E (fun Y => obsF 1 Y * obsF (-1) Y) X) := by
    rw [hfun]
    exact lc_transOp_F g E hX r _
  have hm0 : ∀ Y : State W, IsState Y → obsM 0 Y = 1 := fun Y hY => (obsM_zero_neg hW hY 0).1
  have hcb : transOp g E (fun Y => obsM 0 Y * obsF 2 Y) X = transOp g E (obsF 2) X :=
    lc_transOp_congr g E hX fun Y hY => by rw [hm0 Y hY, one_mul]
  have e1 := h5 W hW g hg E hE X hX
  have ea := ha W hW g hg E hE X hX
  have eb := hb W hW g hg E hE X hX
  have ec := hc W hW g hg E hE X hX
  have ed := hd W hW g hg E hE X hX
  rw [hcb, hm0 X hX, one_mul, lc_zpow_two E 0 2 (by norm_num)] at eb
  rw [lc_zpow_two E 1 1 (by norm_num)] at ea ec
  rw [show (1 : ℤ) + -1 = 0 by norm_num, zpow_zero, one_mul] at ed
  simp only [bOdd, bEven] at e1
  have hkey := lc_alg_F (normalPhase E) ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) r (obsM 1 X)
    (obsM (-1) X) (obsM 2 X) (obsF 1 X) (obsF 2 X) (obsF (-1) X) (transOp g E (obsF 1) X)
    (transOp g E (fun Y => obsM 1 Y * obsF 1 Y) X) (transOp g E (obsF 2) X)
    (transOp g E (fun Y => obsF 1 Y * obsF 1 Y) X)
    (transOp g E (fun Y => obsF 1 Y * obsF (-1) Y) X) hr
  unfold driftAlpha
  rw [hP, hcorrF, hkey]
  refine (lc_norm_comb_F _ _ _ _ _ _ _ _ _).trans ?_
  have hmm : ‖obsM (-1) X‖ = ‖obsM 1 X‖ := by
    rw [(obsM_zero_neg hW hX 1).2, norm_star]
  have hT := lc_norm_T (E := E) hX
  have hha : 0 ≤ normalH E ^ 2 * (1 / g ^ 2) := by positivity
  have hm_le : ‖obsM 1 X‖ ≤ ‖corrM g E X‖ + 4 * (normalH E ^ 3 * (1 / g ^ 2)) := by
    have h1 : obsM 1 X = corrM g E X +
        r * (normalPhase E + obsM 2 X + 2 * obsM 1 X ^ 2) := by
      rw [hcorrM]; ring
    have h2 := mul_le_mul_of_nonneg_left hT (norm_nonneg r)
    rw [hrn] at h2
    calc ‖obsM 1 X‖ = ‖corrM g E X + r * (normalPhase E + obsM 2 X + 2 * obsM 1 X ^ 2)‖ := by
          rw [← h1]
      _ ≤ ‖corrM g E X‖ + ‖r * (normalPhase E + obsM 2 X + 2 * obsM 1 X ^ 2)‖ := norm_add_le _ _
      _ ≤ ‖corrM g E X‖ + 4 * (normalH E ^ 3 * (1 / g ^ 2)) := by
          rw [norm_mul, hrn]; linarith
  have hF1 : ‖normalPhase E * ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) *
      (2 * obsM 1 X * obsF 2 X - obsM 1 X * obsF 1 X * obsF 1 X -
        obsM (-1) X * obsF 1 X * obsF (-1) X)‖ ≤
      1 * (normalH E ^ 2 * (1 / g ^ 2)) * (4 * ‖obsM 1 X‖) := by
    rw [norm_mul, norm_mul, lc_norm_normalPhase, lc_norm_q hE2,
      show normalH E ^ 2 / g ^ 2 = normalH E ^ 2 * (1 / g ^ 2) by ring]
    gcongr
    exact lc_norm_Bx hmm (norm_obsF_le_one 1 hX) (norm_obsF_le_one 2 hX)
      (norm_obsF_le_one (-1) hX)
  have hF2 : ‖normalPhase E * ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (3 + obsM 2 X) * r *
      (4 * (obsM 1 X * obsF 1 X) + 2 * obsF 2 X - obsF 1 X * obsF 1 X -
        normalPhase E * (obsF 1 X * obsF (-1) X))‖ ≤
      1 * (normalH E ^ 2 * (1 / g ^ 2)) * 4 * (normalH E ^ 3 * (1 / g ^ 2)) * 8 := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, lc_norm_normalPhase, lc_norm_q hE2, hrn,
      show normalH E ^ 2 / g ^ 2 = normalH E ^ 2 * (1 / g ^ 2) by ring]
    gcongr
    · exact lc_norm_s hX
    · exact lc_norm_NF hX
  have ea' : ‖transOp g E (fun Y => obsM 1 Y * obsF 1 Y) X -
      normalPhase E ^ 2 * (obsM 1 X * obsF 1 X)‖ ≤ Ka * (1 / g ^ 2) := ea.trans_eq (by ring)
  have eb' : ‖transOp g E (obsF 2) X - normalPhase E ^ 2 * obsF 2 X‖ ≤ Kb * (1 / g ^ 2) :=
    eb.trans_eq (by ring)
  have ec' : ‖transOp g E (fun Y => obsF 1 Y * obsF 1 Y) X -
      normalPhase E ^ 2 * (obsF 1 X * obsF 1 X)‖ ≤ Kc * (1 / g ^ 2) := ec.trans_eq (by ring)
  have ed' : ‖transOp g E (fun Y => obsF 1 Y * obsF (-1) Y) X - obsF 1 X * obsF (-1) X‖ ≤
      Kd * (1 / g ^ 2) := ed.trans_eq (by ring)
  have e1' := e1.trans_eq (show K₅ * (1 / g ^ 4 + 1 / (g ^ 2 * W)) =
    K₅ * ((1 / g ^ 2) ^ 2 + (1 / g ^ 2) * (1 / (W : ℝ))) by ring)
  have hmain := lc_final_F (K₅ := K₅) (S := 4 * Ka + 2 * Kb + Kc + Kd) (H := H)
    (h := normalH E) (a := 1 / g ^ 2) (w := 1 / (W : ℝ)) (x := ‖corrM g E X‖) hK₅.le
    (by positivity) hh0.le hhH (by positivity) (by positivity) (norm_nonneg _)
  refine le_trans ?_ (hmain.trans_eq (by ring))
  have t2 : ‖r‖ * (4 * ‖transOp g E (fun Y => obsM 1 Y * obsF 1 Y) X -
        normalPhase E ^ 2 * (obsM 1 X * obsF 1 X)‖ +
      2 * ‖transOp g E (obsF 2) X - normalPhase E ^ 2 * obsF 2 X‖ +
      ‖transOp g E (fun Y => obsF 1 Y * obsF 1 Y) X - normalPhase E ^ 2 * (obsF 1 X * obsF 1 X)‖ +
      ‖normalPhase E‖ * ‖transOp g E (fun Y => obsF 1 Y * obsF (-1) Y) X -
        obsF 1 X * obsF (-1) X‖) ≤
      (normalH E ^ 3 * (1 / g ^ 2)) * ((4 * Ka + 2 * Kb + Kc + Kd) * (1 / g ^ 2)) := by
    rw [hrn, lc_norm_normalPhase, one_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have t3 : ‖normalPhase E * ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) *
      (2 * obsM 1 X * obsF 2 X - obsM 1 X * obsF 1 X * obsF 1 X -
        obsM (-1) X * obsF 1 X * obsF (-1) X)‖ ≤
      normalH E ^ 2 * (1 / g ^ 2) * (4 * (‖corrM g E X‖ + 4 * (normalH E ^ 3 * (1 / g ^ 2)))) := by
    refine hF1.trans ?_
    rw [one_mul]
    exact mul_le_mul_of_nonneg_left (by linarith) hha
  exact add_le_add (add_le_add (add_le_add e1' t2) t3) (hF2.trans_eq (by ring))

/-- `|α|² ≤ 1 - a_1 g⁻²` after (11.22) [uvg:eq:means], with `a_1 = 1/2` for `g ≥ √8 h_θ`. -/
theorem normSq_driftAlpha_le {W : ℕ} (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) {g : ℝ}
    (hg : Real.sqrt 8 * normalH E ≤ g) {X : State W} (hX : IsState X) :
    ‖driftAlpha g E X‖ ^ 2 ≤ 1 - 1 / (2 * g ^ 2) := by
  have hh0 := lc_normalH_pos hE
  have hhalf := lc_half_le_normalH hE
  have hg0 : 0 < g := lt_of_lt_of_le (by positivity) hg
  have hg2 : 0 < g ^ 2 := by positivity
  have hg8 : 8 * normalH E ^ 2 ≤ g ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hg 2
    rwa [mul_pow, Real.sq_sqrt (by norm_num)] at this
  have hq0 : 0 ≤ normalH E ^ 2 / g ^ 2 := by positivity
  have hq8 : normalH E ^ 2 / g ^ 2 ≤ 1 / 8 := by
    rw [div_le_iff₀ hg2]; linarith
  have hq4 : 1 / (4 * g ^ 2) ≤ normalH E ^ 2 / g ^ 2 := by
    have hh4 : 1 / 4 ≤ normalH E ^ 2 := by nlinarith
    rw [div_le_div_iff₀ (by positivity) hg2]
    nlinarith [mul_le_mul_of_nonneg_right hh4 hg2.le]
  have hα : ‖driftAlpha g E X‖ = ‖1 - ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (3 + obsM 2 X)‖ := by
    unfold driftAlpha
    rw [norm_mul, norm_neg, lc_norm_normalPhase, one_mul]
  have hm2 := norm_obsM_le_one 2 hX
  have hs := lc_norm_s hX
  have hre : 2 ≤ (3 + obsM 2 X).re := by
    have := Complex.abs_re_le_norm (obsM 2 X)
    rw [abs_le] at this
    simp only [Complex.add_re]
    norm_num
    linarith [this.1, hm2]
  have hsq : (3 + obsM 2 X).re ^ 2 + (3 + obsM 2 X).im ^ 2 ≤ 16 := by
    have h1 := Complex.sq_norm (3 + obsM 2 X)
    rw [Complex.normSq_apply] at h1
    have h2 : ‖(3 : ℂ) + obsM 2 X‖ ^ 2 ≤ 16 := by nlinarith [norm_nonneg ((3 : ℂ) + obsM 2 X)]
    nlinarith
  rw [hα, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  generalize normalH E ^ 2 / g ^ 2 = q at hq0 hq8 hq4 ⊢
  generalize (3 + obsM 2 X).re = x at hre hsq ⊢
  generalize (3 + obsM 2 X).im = y at hsq ⊢
  have h1 : 1 / (2 * g ^ 2) ≤ 2 * q := by
    have : 1 / (2 * g ^ 2) = 2 * (1 / (4 * g ^ 2)) := by field_simp; ring
    rw [this]
    linarith
  nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hre),
    mul_nonneg (mul_nonneg hq0 hq0) (sub_nonneg.mpr hsq),
    mul_nonneg hq0 (sub_nonneg.mpr hq8)]

end LSBA
