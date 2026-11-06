import LSBA.Prop.StepDefs
import LSBA.Kernel.Scales

/-!
# Resolvent comparison at two times (Lemma 5.11 [fo:lem:families])

The vertical comparison of resolvents (5.35) [fo:eq:backward-matching] for every Hermitian matrix,
the samplewise identity `H_s(g′) = ξ H_u(g)` and `(H_u − w)⁻¹ = ξ G_s(g′, E′)`, and Lemma 5.11
[fo:lem:families] on the comparison reach.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA


section VerticalToolkit

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Squared Euclidean norm of a vector. -/
private def comparison_nsq (x : n → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

omit [DecidableEq n] in
private lemma comparison_nsq_nonneg (x : n → ℂ) : 0 ≤ comparison_nsq x :=
  Finset.sum_nonneg fun _ _ => by positivity

omit [DecidableEq n] in
private lemma comparison_star_dot_self (x : n → ℂ) :
    star x ⬝ᵥ x = ((comparison_nsq x : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', comparison_nsq]
  push_cast
  rfl

omit [DecidableEq n] in
/-- Cauchy–Schwarz for the pairing `x* y`. -/
private lemma comparison_cauchy (x y : n → ℂ) :
    ‖star x ⬝ᵥ y‖ ^ 2 ≤ comparison_nsq x * comparison_nsq y := by
  have h1 : ‖star x ⬝ᵥ y‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp
  calc ‖star x ⬝ᵥ y‖ ^ 2 ≤ (∑ i, ‖x i‖ * ‖y i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

omit [DecidableEq n] in
private lemma comparison_dot_conjTranspose (M : Matrix n n ℂ) (u : n → ℂ) :
    star u ⬝ᵥ (Mᴴ *ᵥ u) = star (star u ⬝ᵥ (M *ᵥ u)) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star]

omit [DecidableEq n] in
/-- `‖M u‖² = u* (M* M) u`. -/
private lemma comparison_nsq_mulVec (M : Matrix n n ℂ) (u : n → ℂ) :
    ((comparison_nsq (M *ᵥ u) : ℝ) : ℂ) = star u ⬝ᵥ ((Mᴴ * M) *ᵥ u) := by
  rw [← comparison_star_dot_self, Matrix.star_mulVec, ← Matrix.mulVec_mulVec u Mᴴ M,
    Matrix.dotProduct_mulVec (star u) Mᴴ]

omit [DecidableEq n] in
private lemma comparison_ward_aux (G : Matrix n n ℂ) {η : ℝ} (hη : η ≠ 0)
    (h : Gᴴ * G = ((2 * η * Complex.I)⁻¹ : ℂ) • (G - Gᴴ)) (u : n → ℂ) :
    comparison_nsq (G *ᵥ u) = (star u ⬝ᵥ (G *ᵥ u)).im / η := by
  have h3 : star u ⬝ᵥ ((Gᴴ * G) *ᵥ u) = ((2 * η * Complex.I)⁻¹ : ℂ) *
      (star u ⬝ᵥ (G *ᵥ u) - star (star u ⬝ᵥ (G *ᵥ u))) := by
    rw [h, Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul, dotProduct_sub,
      comparison_dot_conjTranspose, smul_eq_mul]
  have h4 : ∀ w : ℂ, w - star w = ((2 * w.im : ℝ) : ℂ) * Complex.I := fun w => by
    apply Complex.ext <;> simp [two_mul]
  apply Complex.ofReal_injective
  rw [comparison_nsq_mulVec, h3, h4]
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  push_cast
  field_simp

private lemma comparison_resolvent_conjTranspose {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : ℂ) :
    (resolventMat A z)ᴴ = resolventMat A (star z) := by
  unfold resolventMat
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, hA.eq,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one]

/-- Ward's identity for `G` and `G*`: `‖G u‖² = ‖G* u‖² = Im ⟨u, G u⟩ / Im z`. -/
private lemma comparison_ward_vec {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (u : n → ℂ) :
    comparison_nsq (resolventMat A z *ᵥ u) = (star u ⬝ᵥ (resolventMat A z *ᵥ u)).im / z.im ∧
    comparison_nsq ((resolventMat A z)ᴴ *ᵥ u) =
      (star u ⬝ᵥ (resolventMat A z *ᵥ u)).im / z.im := by
  refine ⟨comparison_ward_aux _ hz (ward_matrix hA hz) u, ?_⟩
  have hz' : (star z).im ≠ 0 := by simpa using hz
  have h := comparison_ward_aux (resolventMat A (star z)) hz' (ward_matrix hA hz') u
  rw [← comparison_resolvent_conjTranspose hA z] at h
  rw [h, comparison_dot_conjTranspose]
  simp


/-- Resolvent identity at two spectral points: `G(z) - G(w) = (z - w) G(z) G(w)`. -/
private lemma comparison_resolvent_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) {z w : ℂ}
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

/-- `G(z) - G(w) = (z - w) G(w) G(z)`. -/
private lemma comparison_resolvent_sub' {A : Matrix n n ℂ} (hA : A.IsHermitian) {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    resolventMat A z - resolventMat A w = (z - w) • (resolventMat A w * resolventMat A z) := by
  have h := comparison_resolvent_sub hA hw hz
  rw [← neg_sub, h, ← neg_smul, neg_sub]

/-- For `Re z = Re w`, `0 < Im z ≤ Im w` and `T = 1 + (z - w) G(z)`:
`T* T = 1 + (Im w² - Im z²) G(z)* G(z)`. -/
private lemma comparison_T_gram {A : Matrix n n ℂ} (hA : A.IsHermitian) {z w : ℂ}
    (hre : z.re = w.re) (hz : z.im ≠ 0) :
    ((1 : Matrix n n ℂ) + (z - w) • resolventMat A z)ᴴ *
        ((1 : Matrix n n ℂ) + (z - w) • resolventMat A z) =
      1 + ((w.im ^ 2 - z.im ^ 2 : ℝ) : ℂ) • ((resolventMat A z)ᴴ * resolventMat A z) := by
  set G := resolventMat A z with hG
  have hward : Gᴴ * G = ((2 * z.im * Complex.I)⁻¹ : ℂ) • (G - Gᴴ) := ward_matrix hA hz
  have hc : (2 * (z.im : ℂ) * Complex.I) ≠ 0 := by simp [hz]
  have hward' : (G - Gᴴ) = (2 * (z.im : ℂ) * Complex.I) • (Gᴴ * G) := by
    rw [hward, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hzw : z - w = ((z.im - w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  have hzw' : star (z - w) = -(((z.im - w.im : ℝ) : ℂ) * Complex.I) := by
    rw [hzw]; apply Complex.ext <;> simp
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]
  have hcc : star (z - w) = -(z - w) := by rw [hzw']; rw [hzw]
  have hr : ((w.im ^ 2 - z.im ^ 2 : ℝ) : ℂ) =
      (z - w) * (2 * (z.im : ℂ) * Complex.I) - (z - w) * (z - w) := by
    rw [hzw]; push_cast
    ring_nf
    rw [Complex.I_sq]; ring
  rw [hcc, hr]
  set M := Gᴴ * G with hM
  linear_combination (norm := module) (z - w) • hward'


/-- `Im z ^ 2 ‖G(z) u‖² ≤ ‖u‖²`. -/
private lemma comparison_sq_nsq_le {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (u : n → ℂ) :
    z.im ^ 2 * comparison_nsq (resolventMat A z *ᵥ u) ≤ comparison_nsq u := by
  have hw := (comparison_ward_vec hA hz.ne' u).1
  set v := resolventMat A z *ᵥ u with hv
  set X := star u ⬝ᵥ v with hX
  have h1 : z.im * comparison_nsq v = X.im := by rw [hw]; field_simp
  have h2 : (z.im * comparison_nsq v) ^ 2 ≤ comparison_nsq u * comparison_nsq v := by
    rw [h1]
    calc X.im ^ 2 = |X.im| ^ 2 := (sq_abs _).symm
      _ ≤ ‖X‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm X) 2
      _ ≤ _ := comparison_cauchy u v
  rcases (comparison_nsq_nonneg v).eq_or_lt with h0 | hpos
  · rw [← h0]; simpa using comparison_nsq_nonneg u
  · have : z.im ^ 2 * comparison_nsq v * comparison_nsq v ≤
        comparison_nsq u * comparison_nsq v := by
      nlinarith
    exact le_of_mul_le_mul_right this hpos

/-- Vertical comparison of resolvent vectors: for `Re z = Re w`, `0 < Im z ≤ Im w`,
`‖G(z) x‖ ≤ (Im w/Im z) ‖G(w) x‖`. -/
private lemma comparison_nsq_vertical {A : Matrix n n ℂ} (hA : A.IsHermitian) {z w : ℂ}
    (hre : z.re = w.re) (hz : 0 < z.im) (hzw : z.im ≤ w.im) (x : n → ℂ) :
    comparison_nsq (resolventMat A z *ᵥ x) ≤
      (w.im / z.im) ^ 2 * comparison_nsq (resolventMat A w *ᵥ x) := by
  have hw : 0 < w.im := lt_of_lt_of_le hz hzw
  set G := resolventMat A z with hG
  set F := resolventMat A w with hF
  set u := F *ᵥ x with hu
  set T : Matrix n n ℂ := 1 + (z - w) • G with hT
  have hGT : G *ᵥ x = T *ᵥ u := by
    have h := comparison_resolvent_sub hA hz.ne' hw.ne'
    have h2 : G = T * F := by
      rw [hT, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
      have : G = F + (z - w) • (G * F) := by rw [← h]; abel
      exact this
    rw [h2, hu, Matrix.mulVec_mulVec]
  have hgram := comparison_T_gram hA hre hz.ne'
  have hnsqT : comparison_nsq (T *ᵥ u) =
      comparison_nsq u + (w.im ^ 2 - z.im ^ 2) * comparison_nsq (G *ᵥ u) := by
    apply Complex.ofReal_injective
    rw [comparison_nsq_mulVec, hT, hgram, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, comparison_star_dot_self,
      ← comparison_nsq_mulVec]
    push_cast
    rfl
  have hb := comparison_sq_nsq_le hA hz u
  rw [hGT, hnsqT]
  have hz2 : 0 < z.im ^ 2 := by positivity
  have hr : 0 ≤ w.im ^ 2 - z.im ^ 2 := by nlinarith
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ hz2]
  nlinarith [mul_le_mul_of_nonneg_left hb hr, comparison_nsq_nonneg u]


/-- `Im ⟨x, G(z) x⟩ ≤ (Im w/Im z) Im ⟨x, G(w) x⟩` for `Re z = Re w`, `0 < Im z ≤ Im w`. -/
private lemma comparison_im_vertical {A : Matrix n n ℂ} (hA : A.IsHermitian) {z w : ℂ}
    (hre : z.re = w.re) (hz : 0 < z.im) (hzw : z.im ≤ w.im) (x : n → ℂ) :
    (star x ⬝ᵥ (resolventMat A z *ᵥ x)).im ≤
      w.im / z.im * (star x ⬝ᵥ (resolventMat A w *ᵥ x)).im := by
  have hw : 0 < w.im := lt_of_lt_of_le hz hzw
  have e1 := (comparison_ward_vec hA hz.ne' x).1
  have e2 := (comparison_ward_vec hA hw.ne' x).1
  have key := comparison_nsq_vertical hA hre hz hzw x
  have hXz : (star x ⬝ᵥ (resolventMat A z *ᵥ x)).im =
      z.im * comparison_nsq (resolventMat A z *ᵥ x) := by
    rw [e1]; field_simp
  have hXw : (star x ⬝ᵥ (resolventMat A w *ᵥ x)).im =
      w.im * comparison_nsq (resolventMat A w *ᵥ x) := by
    rw [e2]; field_simp
  rw [hXz, hXw]
  calc z.im * comparison_nsq (resolventMat A z *ᵥ x)
      ≤ z.im * ((w.im / z.im) ^ 2 * comparison_nsq (resolventMat A w *ᵥ x)) :=
        mul_le_mul_of_nonneg_left key hz.le
    _ = w.im / z.im * (w.im * comparison_nsq (resolventMat A w *ᵥ x)) := by field_simp

private lemma comparison_qform_eq {m : Type*} [Fintype m] (M : Matrix m m ℂ) (u : m → ℂ) :
    qform M u = (star u ⬝ᵥ (M *ᵥ u)).re := by
  unfold qform
  congr 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]

/-- The quadratic form of `Im B` is the imaginary part of `u* B u`. -/
private lemma comparison_qform_matIm {m : Type*} [Fintype m] (B : Matrix m m ℂ) (u : m → ℂ) :
    qform (matIm B) u = (star u ⬝ᵥ (B *ᵥ u)).im := by
  rw [comparison_qform_eq, matIm, Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul,
    dotProduct_sub, comparison_dot_conjTranspose, smul_eq_mul]
  set s := star u ⬝ᵥ (B *ᵥ u) with hs
  have h4 : s - star s = ((2 * s.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [two_mul]
  rw [h4]
  have : ((2 : ℂ) * Complex.I)⁻¹ * (((2 * s.im : ℝ) : ℂ) * Complex.I) = (s.im : ℂ) := by
    push_cast
    field_simp
  rw [this, Complex.ofReal_re]

/-- The first comparison of (5.35) [fo:eq:backward-matching]: `Im G(z) ⪯ (Im w/Im z) Im G(w)` as
quadratic forms. -/
private lemma comparison_vertical_qform {A : Matrix n n ℂ} (hA : A.IsHermitian) {z w : ℂ}
    (hre : z.re = w.re) (hz : 0 < z.im) (hzw : z.im ≤ w.im) (v : n → ℂ) :
    qform (matIm (resolventMat A z)) v ≤ w.im / z.im * qform (matIm (resolventMat A w)) v := by
  rw [comparison_qform_matIm, comparison_qform_matIm]
  exact comparison_im_vertical hA hre hz hzw v

/-- The quadratic form of `Im G(z)` is nonnegative for `Im z > 0`. -/
private lemma comparison_qform_resolvent_nonneg {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (v : n → ℂ) : 0 ≤ qform (matIm (resolventMat A z)) v := by
  rw [comparison_qform_matIm]
  have e := (comparison_ward_vec hA hz.ne' v).1
  have : (star v ⬝ᵥ (resolventMat A z *ᵥ v)).im =
      z.im * comparison_nsq (resolventMat A z *ᵥ v) := by
    rw [e]; field_simp
  rw [this]
  exact mul_nonneg hz.le (comparison_nsq_nonneg _)


omit [DecidableEq n] in
/-- Cauchy–Schwarz through a matrix: `|x* (F y)| ≤ ‖F* x‖ ‖y‖`. -/
private lemma comparison_cauchy_mul (F : Matrix n n ℂ) (x y : n → ℂ) :
    ‖star x ⬝ᵥ (F *ᵥ y)‖ ≤ Real.sqrt (comparison_nsq (Fᴴ *ᵥ x)) * Real.sqrt (comparison_nsq y) := by
  have h : star x ⬝ᵥ (F *ᵥ y) = star (Fᴴ *ᵥ x) ⬝ᵥ y := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]
  rw [h, ← Real.sqrt_mul (comparison_nsq_nonneg _)]
  exact Real.le_sqrt_of_sq_le (comparison_cauchy _ _)

end VerticalToolkit

section BlockToolkit

variable {W L : ℕ}

open scoped Matrix.Norms.L2Operator in
/-- `‖A u‖² ≤ ‖A‖² ‖u‖²` for the operator norm. -/
private lemma comparison_nsq_le_opNorm (A : Matrix (Fin W) (Fin W) ℂ) (u : Fin W → ℂ) :
    comparison_nsq (A *ᵥ u) ≤ ‖A‖ ^ 2 * comparison_nsq u := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 u)
  have h1 : ‖(EuclideanSpace.equiv (Fin W) ℂ).symm (A *ᵥ u)‖ ^ 2 = comparison_nsq (A *ᵥ u) := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin W))‖ ^ 2 = comparison_nsq u := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  rw [← h1, ← h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

open scoped Matrix.Norms.L2Operator in
/-- `|u'* (A u)| ≤ ‖A‖ ‖u'‖ ‖u‖`. -/
private lemma comparison_bilin_le_opNorm (A : Matrix (Fin W) (Fin W) ℂ) (u' u : Fin W → ℂ) :
    ‖star u' ⬝ᵥ (A *ᵥ u)‖ ≤
      ‖A‖ * (Real.sqrt (comparison_nsq u') * Real.sqrt (comparison_nsq u)) := by
  have h1 := comparison_cauchy u' (A *ᵥ u)
  have h2 := comparison_nsq_le_opNorm A u
  have h3 : ‖star u' ⬝ᵥ (A *ᵥ u)‖ ^ 2 ≤
      (‖A‖ * (Real.sqrt (comparison_nsq u') * Real.sqrt (comparison_nsq u))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (comparison_nsq_nonneg _),
      Real.sq_sqrt (comparison_nsq_nonneg _)]
    calc _ ≤ comparison_nsq u' * comparison_nsq (A *ᵥ u) := h1
      _ ≤ comparison_nsq u' * (‖A‖ ^ 2 * comparison_nsq u) :=
        mul_le_mul_of_nonneg_left h2 (comparison_nsq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

open scoped Matrix.Norms.L2Operator in
/-- The operator norm is bounded by the best bilinear constant. -/
private lemma comparison_opNorm_le_of_bilin (A : Matrix (Fin W) (Fin W) ℂ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ u' u : Fin W → ℂ, ‖star u' ⬝ᵥ (A *ᵥ u)‖ ≤
      K * (Real.sqrt (comparison_nsq u') * Real.sqrt (comparison_nsq u))) : ‖A‖ ≤ K := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  have h1 : ‖Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) A x‖ ^ 2 =
      comparison_nsq (A *ᵥ x.ofLp) := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h2 : ‖x‖ ^ 2 = comparison_nsq x.ofLp := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have hu := h (A *ᵥ x.ofLp) x.ofLp
  rw [comparison_star_dot_self, Complex.norm_real,
    Real.norm_of_nonneg (comparison_nsq_nonneg _)] at hu
  have h3 : ‖Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) A x‖ ≤ K * ‖x‖ := by
    set a := Real.sqrt (comparison_nsq (A *ᵥ x.ofLp)) with ha
    have ha1 : a ^ 2 = comparison_nsq (A *ᵥ x.ofLp) := Real.sq_sqrt (comparison_nsq_nonneg _)
    have hnx : ‖x‖ = Real.sqrt (comparison_nsq x.ofLp) := by
      rw [← h2, Real.sqrt_sq (norm_nonneg _)]
    have hnA : ‖Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) A x‖ = a := by
      rw [ha, ← h1, Real.sqrt_sq (norm_nonneg _)]
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    rw [hnA, hnx]
    rcases ha0.eq_or_lt with h0 | hpos
    · rw [← h0]; exact mul_nonneg hK (Real.sqrt_nonneg _)
    · rw [← ha1] at hu
      refine le_of_mul_le_mul_left ?_ hpos
      nlinarith
  exact h3


open scoped Matrix.Norms.L2Operator in
private lemma comparison_im_dot_le (A : Matrix (Fin W) (Fin W) ℂ) (u : Fin W → ℂ) :
    (star u ⬝ᵥ (A *ᵥ u)).im ≤ ‖A‖ * comparison_nsq u := by
  have h := comparison_bilin_le_opNorm A u u
  rw [← Real.sqrt_mul (comparison_nsq_nonneg _), Real.sqrt_mul_self (comparison_nsq_nonneg u)] at h
  exact ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans h

/-- Embedding of `u ∈ ℂ^W` at block `b` of `ℂ^L ⊗ ℂ^W`. -/
private def comparison_emb (b : Fin L) (u : Fin W → ℂ) : Fin L × Fin W → ℂ :=
  fun p => if p.1 = b then u p.2 else 0

private lemma comparison_emb_dot (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L)
    (u' u : Fin W → ℂ) :
    star (comparison_emb a u') ⬝ᵥ (M *ᵥ comparison_emb b u) =
      star u' ⬝ᵥ (blockOf M a b *ᵥ u) := by
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, comparison_emb,
    blockOf, Matrix.mulVec, Matrix.of_apply]
  simp [apply_ite (starRingEnd ℂ)]

/-- `‖z - w‖ = Im w - Im z` for `Re z = Re w`, `Im z ≤ Im w`. -/
private lemma comparison_norm_sub {z w : ℂ} (hre : z.re = w.re) (hzw : z.im ≤ w.im) :
    ‖z - w‖ = w.im - z.im := by
  have : z - w = (((z.im - w.im : ℝ)) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_nonpos (by linarith)]
  ring

open scoped Matrix.Norms.L2Operator in
/-- The block-operator-norm comparison of (5.35) [fo:eq:backward-matching]:
`‖G(z)_{ab}‖ ≤ (Im w/Im z) M`
whenever `‖G(w)_{cd}‖ ≤ M` for all blocks. -/
private lemma comparison_block_op {H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hH : H.IsHermitian) {z w : ℂ} (hre : z.re = w.re) (hz : 0 < z.im) (hzw : z.im ≤ w.im)
    (a b : Fin L) {M : ℝ} (hM : ∀ c d : Fin L, ‖blockOf (resolventMat H w) c d‖ ≤ M) :
    ‖blockOf (resolventMat H z) a b‖ ≤ w.im / z.im * M := by
  have hw : 0 < w.im := lt_of_lt_of_le hz hzw
  set G := resolventMat H z with hG
  set F := resolventMat H w with hF
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a b)
  have hy : 0 ≤ w.im / z.im := by positivity
  refine comparison_opNorm_le_of_bilin _ (by positivity) fun u' u => ?_
  set x' := comparison_emb a u' with hx'
  set x := comparison_emb b u with hx
  rw [← comparison_emb_dot]
  have hGx : G *ᵥ x = F *ᵥ x + (z - w) • (F *ᵥ (G *ᵥ x)) := by
    have h := comparison_resolvent_sub' hH hz.ne' hw.ne'
    have h2 : G = F + (z - w) • (F * G) := by rw [← h]; abel
    conv_lhs => rw [h2]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  rw [hGx, dotProduct_add, dotProduct_smul, smul_eq_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, comparison_norm_sub hre hzw]
  set nu' := Real.sqrt (comparison_nsq u') with hnu'
  set nu := Real.sqrt (comparison_nsq u) with hnu
  have hnu'0 : 0 ≤ nu' := Real.sqrt_nonneg _
  have hnu0 : 0 ≤ nu := Real.sqrt_nonneg _
  have t1 : ‖star x' ⬝ᵥ (F *ᵥ x)‖ ≤ M * (nu' * nu) := by
    rw [hx', hx, comparison_emb_dot]
    exact (comparison_bilin_le_opNorm _ _ _).trans
      (mul_le_mul_of_nonneg_right (hM a b) (by positivity))
  have n1 : comparison_nsq (Fᴴ *ᵥ x') ≤ M / w.im * comparison_nsq u' := by
    rw [(comparison_ward_vec hH hw.ne' x').2, hx', comparison_emb_dot, div_le_iff₀ hw,
      mul_comm (M / w.im), mul_assoc, div_mul_cancel₀ _ hw.ne']
    refine (comparison_im_dot_le _ _).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hM a a) (comparison_nsq_nonneg _)
  have n2 : comparison_nsq (G *ᵥ x) ≤ w.im / z.im * M / z.im * comparison_nsq u := by
    rw [(comparison_ward_vec hH hz.ne' x).1, div_le_iff₀ hz]
    have h1 := comparison_im_vertical hH hre hz hzw x
    have h2 : (star x ⬝ᵥ (F *ᵥ x)).im ≤ M * comparison_nsq u := by
      rw [hx, comparison_emb_dot]
      refine (comparison_im_dot_le _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hM b b) (comparison_nsq_nonneg _)
    calc _ ≤ w.im / z.im * (star x ⬝ᵥ (F *ᵥ x)).im := h1
      _ ≤ w.im / z.im * (M * comparison_nsq u) := mul_le_mul_of_nonneg_left h2 hy
      _ = _ := by field_simp
  have t2 : ‖star x' ⬝ᵥ (F *ᵥ (G *ᵥ x))‖ ≤ M / z.im * (nu' * nu) := by
    refine (comparison_cauchy_mul F x' (G *ᵥ x)).trans ?_
    rw [← Real.sqrt_mul (comparison_nsq_nonneg _), hnu', hnu,
      ← Real.sqrt_mul (comparison_nsq_nonneg _)]
    have hsq : (M / z.im * Real.sqrt (comparison_nsq u' * comparison_nsq u)) ^ 2 =
        M ^ 2 / z.im ^ 2 * (comparison_nsq u' * comparison_nsq u) := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (comparison_nsq_nonneg _) (comparison_nsq_nonneg _)),
        div_pow]
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (div_nonneg hM0 hz.le) (Real.sqrt_nonneg _), ?_⟩
    rw [hsq]
    calc comparison_nsq (Fᴴ *ᵥ x') * comparison_nsq (G *ᵥ x)
        ≤ (M / w.im * comparison_nsq u') * (w.im / z.im * M / z.im * comparison_nsq u) :=
          mul_le_mul n1 n2 (comparison_nsq_nonneg _)
            (mul_nonneg (div_nonneg hM0 hw.le) (comparison_nsq_nonneg _))
      _ = _ := by field_simp
  have hz' : (w.im - z.im) * (M / z.im * (nu' * nu)) = (w.im - z.im) / z.im * M * (nu' * nu) := by
    ring
  calc ‖star x' ⬝ᵥ (F *ᵥ x)‖ + (w.im - z.im) * ‖star x' ⬝ᵥ (F *ᵥ (G *ᵥ x))‖
      ≤ M * (nu' * nu) + (w.im - z.im) * (M / z.im * (nu' * nu)) := by
        gcongr
    _ = w.im / z.im * M * (nu' * nu) := by field_simp; ring

end BlockToolkit

section DiagToolkit

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma comparison_single_dot (M : Matrix n n ℂ) (p : n) :
    star (Pi.single p (1 : ℂ) : n → ℂ) ⬝ᵥ (M *ᵥ Pi.single p (1 : ℂ)) = M p p := by
  simp [dotProduct, Pi.single_apply]

private lemma comparison_entry_mul (F G : Matrix n n ℂ) (p q : n) :
    star (Pi.single p (1 : ℂ) : n → ℂ) ⬝ᵥ (F *ᵥ (G *ᵥ Pi.single q (1 : ℂ))) = (F * G) p q := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  simp [dotProduct, Pi.single_apply]

private lemma comparison_entry_mul_le (F G : Matrix n n ℂ) (p q : n) :
    ‖(F * G) p q‖ ≤ Real.sqrt (comparison_nsq (Fᴴ *ᵥ Pi.single p (1 : ℂ))) *
      Real.sqrt (comparison_nsq (G *ᵥ Pi.single q (1 : ℂ))) := by
  rw [← comparison_entry_mul]
  exact comparison_cauchy_mul F _ _

private lemma comparison_ward_diag {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (p : n) :
    comparison_nsq ((resolventMat A z)ᴴ *ᵥ Pi.single p (1 : ℂ)) = (resolventMat A z p p).im / z.im ∧
    comparison_nsq (resolventMat A z *ᵥ Pi.single p (1 : ℂ)) =
      (resolventMat A z p p).im / z.im := by
  have h := comparison_ward_vec hA hz (Pi.single p (1 : ℂ))
  rw [comparison_single_dot] at h
  exact ⟨h.2, h.1⟩

private lemma comparison_im_diag_vertical {A : Matrix n n ℂ} (hA : A.IsHermitian) {z w : ℂ}
    (hre : z.re = w.re) (hz : 0 < z.im) (hzw : z.im ≤ w.im) (p : n) :
    (resolventMat A z p p).im ≤ w.im / z.im * (resolventMat A w p p).im := by
  have h := comparison_im_vertical hA hre hz hzw (Pi.single p (1 : ℂ))
  rwa [comparison_single_dot, comparison_single_dot] at h

end DiagToolkit

section BlockTrace

variable {W L : ℕ}

/-- The block-trace comparison of (5.35) [fo:eq:backward-matching]: `|⟨G(z)⟩_{ab}| ≤ (Im w/Im z) M`
whenever
`|⟨G(w)⟩_{cd}| ≤ M` for all blocks. -/
private lemma comparison_block_tr {H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hH : H.IsHermitian) {z w : ℂ} (hre : z.re = w.re) (hz : 0 < z.im) (hzw : z.im ≤ w.im)
    (a b : Fin L) {M : ℝ} (hM : ∀ c d : Fin L, ‖blockTr (resolventMat H w) c d‖ ≤ M) :
    ‖blockTr (resolventMat H z) a b‖ ≤ w.im / z.im * M := by
  have hw : 0 < w.im := lt_of_lt_of_le hz hzw
  set G := resolventMat H z with hG
  set F := resolventMat H w with hF
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a b)
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW
    simp only [blockTr, Nat.cast_zero, inv_zero, zero_mul, norm_zero]
    positivity
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  -- decomposition of the trace
  have hdecomp : blockTr G a b = blockTr F a b + (z - w) * blockTr (F * G) a b := by
    have h := comparison_resolvent_sub' hH hz.ne' hw.ne'
    have h2 : G = F + (z - w) • (F * G) := by rw [← h]; abel
    conv_lhs => rw [h2]
    simp only [blockTr, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    ring
  -- the sum of the products of the row and column norms
  set sA : Fin W → ℝ :=
    fun α => Real.sqrt (comparison_nsq (Fᴴ *ᵥ Pi.single (a, α) (1 : ℂ))) with hsA
  set sB : Fin W → ℝ :=
    fun α => Real.sqrt (comparison_nsq (G *ᵥ Pi.single (b, α) (1 : ℂ))) with hsB
  have hS : ‖∑ α, (F * G) (a, α) (b, α)‖ ≤ ∑ α, sA α * sB α := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    exact comparison_entry_mul_le F G (a, α) (b, α)
  have hPa : ∑ α, (F (a, α) (a, α)).im ≤ W * M := by
    have e : ∑ α, F (a, α) (a, α) = (W : ℂ) * blockTr F a a := by
      simp only [blockTr]; field_simp
    have h1 : ∑ α, (F (a, α) (a, α)).im = (∑ α, F (a, α) (a, α)).im := by
      rw [Complex.im_sum]
    rw [h1, e]
    refine ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans ?_
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hM a a) hWr.le
  have hPb : ∑ α, (F (b, α) (b, α)).im ≤ W * M := by
    have e : ∑ α, F (b, α) (b, α) = (W : ℂ) * blockTr F b b := by
      simp only [blockTr]; field_simp
    have h1 : ∑ α, (F (b, α) (b, α)).im = (∑ α, F (b, α) (b, α)).im := by
      rw [Complex.im_sum]
    rw [h1, e]
    refine ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans ?_
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hM b b) hWr.le
  have hA2 : ∑ α, sA α ^ 2 ≤ W * M / w.im := by
    have : ∑ α, sA α ^ 2 = (∑ α, (F (a, α) (a, α)).im) / w.im := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [hsA, Real.sq_sqrt (comparison_nsq_nonneg _)]
      exact (comparison_ward_diag hH hw.ne' (a, α)).1
    rw [this]
    exact div_le_div_of_nonneg_right hPa hw.le
  have hB2 : ∑ α, sB α ^ 2 ≤ w.im / z.im * (W * M) / z.im := by
    have : ∑ α, sB α ^ 2 = (∑ α, (G (b, α) (b, α)).im) / z.im := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [hsB, Real.sq_sqrt (comparison_nsq_nonneg _)]
      exact (comparison_ward_diag hH hz.ne' (b, α)).2
    rw [this]
    refine div_le_div_of_nonneg_right ?_ hz.le
    calc ∑ α, (G (b, α) (b, α)).im ≤ ∑ α, w.im / z.im * (F (b, α) (b, α)).im :=
          Finset.sum_le_sum fun α _ => comparison_im_diag_vertical hH hre hz hzw (b, α)
      _ = w.im / z.im * ∑ α, (F (b, α) (b, α)).im := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hPb (by positivity)
  have hCS : (∑ α, sA α * sB α) ^ 2 ≤ (∑ α, sA α ^ 2) * ∑ α, sB α ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hCS' : ∑ α, sA α * sB α ≤ W * M / z.im := by
    have hnn : 0 ≤ ∑ α, sA α * sB α :=
      Finset.sum_nonneg fun α _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq : (∑ α, sA α * sB α) ^ 2 ≤ (W * M / z.im) ^ 2 := by
      refine hCS.trans ?_
      calc (∑ α, sA α ^ 2) * ∑ α, sB α ^ 2 ≤ (W * M / w.im) * (w.im / z.im * (W * M) / z.im) :=
            mul_le_mul hA2 hB2 (Finset.sum_nonneg fun α _ => by positivity)
              (by positivity)
        _ = _ := by field_simp
    exact (pow_le_pow_iff_left₀ hnn (by positivity) two_ne_zero).mp hsq
  have hT : ‖blockTr (F * G) a b‖ ≤ M / z.im := by
    have : ‖blockTr (F * G) a b‖ = ((W : ℝ)⁻¹) * ‖∑ α, (F * G) (a, α) (b, α)‖ := by
      simp only [blockTr, norm_mul, norm_inv, Complex.norm_natCast]
    rw [this]
    calc (W : ℝ)⁻¹ * ‖∑ α, (F * G) (a, α) (b, α)‖ ≤ (W : ℝ)⁻¹ * (W * M / z.im) :=
          mul_le_mul_of_nonneg_left (hS.trans hCS') (by positivity)
      _ = M / z.im := by field_simp
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, comparison_norm_sub hre hzw]
  calc ‖blockTr F a b‖ + (w.im - z.im) * ‖blockTr (F * G) a b‖
      ≤ M + (w.im - z.im) * (M / z.im) := by
        gcongr
        exact hM a b
    _ = w.im / z.im * M := by field_simp; ring

end BlockTrace

private lemma comparison_le_iSup2 {L : ℕ} (f : Fin L → Fin L → ℝ) (c d : Fin L) :
    f c d ≤ ⨆ c, ⨆ d, f c d :=
  (le_ciSup (Set.finite_range _).bddAbove d).trans
    (le_ciSup (f := fun c => ⨆ d, f c d) (Set.finite_range _).bddAbove c)

open scoped Matrix.Norms.L2Operator in
/-- The three comparisons of (5.35) [fo:eq:backward-matching] for one Hermitian matrix on a
vertical segment: with `G = (H - z)⁻¹`, `F = (H - w)⁻¹`, `Re z = Re w`, `0 < Im z ≤ Im w`:
`Im G ⪯ (Im w/Im z) Im F`, and every block operator norm and normalized block trace of `G` is at
most `Im w/Im z` times the largest one of `F`. -/
theorem resolvent_vertical_cmp {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hH : H.IsHermitian) (z w : ℂ) (hre : z.re = w.re) (hz : 0 < z.im) (hzw : z.im ≤ w.im) :
    (∀ v : Fin L × Fin W → ℂ,
      qform (matIm (resolventMat H z)) v ≤ w.im / z.im * qform (matIm (resolventMat H w)) v) ∧
    (∀ a b : Fin L, ‖blockOf (resolventMat H z) a b‖ ≤
      w.im / z.im * ⨆ c : Fin L, ⨆ d : Fin L, ‖blockOf (resolventMat H w) c d‖) ∧
    ∀ a b : Fin L, ‖blockTr (resolventMat H z) a b‖ ≤
      w.im / z.im * ⨆ c : Fin L, ⨆ d : Fin L, ‖blockTr (resolventMat H w) c d‖ :=
  ⟨comparison_vertical_qform hH hre hz hzw,
    fun a b => comparison_block_op hH hre hz hzw a b
      (comparison_le_iSup2 fun c d => ‖blockOf (resolventMat H w) c d‖),
    fun a b => comparison_block_tr hH hre hz hzw a b
      (comparison_le_iSup2 fun c d => ‖blockTr (resolventMat H w) c d‖)⟩


section Samplewise

private lemma comparison_xi_eq {g s u : ℝ} (hs : 0 < s) (hsu : s ≤ u) :
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
private lemma comparison_xi_facts {g s u : ℝ} (hs : 0 < s) (hsu : s ≤ u) :
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
  have hxi := comparison_xi_eq (g := g) hs hsu
  rw [← hr] at hxi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hxi]; positivity
  · rw [hxi, div_le_one hM', mul_max_of_nonneg _ _ hr0.le, mul_one, hg']
    exact max_le_max hr1 (le_of_eq (mul_comm r g))
  · rw [hxi]; unfold hopB; rw [hg']; field_simp
  · rw [hxi]; unfold gammaG
    field_simp
    rw [hr2]; field_simp

private lemma comparison_inv_smul {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ)
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

private lemma comparison_resolvent_smul {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    {ξ : ℂ} (z' : ℂ) (hξ : ξ ≠ 0) : resolventMat H (ξ⁻¹ * z') = ξ • resolventMat (ξ • H) z' := by
  unfold resolventMat
  have : ξ • H - z' • (1 : Matrix n n ℂ) = ξ • (H - (ξ⁻¹ * z') • (1 : Matrix n n ℂ)) := by
    rw [smul_sub, smul_smul, mul_inv_cancel_left₀ hξ]
  rw [this, comparison_inv_smul _ hξ, smul_smul, mul_inv_cancel₀ hξ, one_smul]

/-- Lemma 5.11 [fo:lem:families] for the single-time realization, samplewise: for a comparison
`p ↦ cmpPt p s` whose point `w` satisfies the endpoint identity `w = ξ⁻¹ z_s(g', E')`,
`H_s(g') = ξ H_u(g)` for every sample, hence `(H_u(g) - w)⁻¹ = ξ G_s(g', E')`; no coupling of
laws is needed. -/
theorem flow_cmp_samplewise (W : ℕ) (p : FlowPt) (s : ℝ) (hg : 0 ≤ p.g) (hs : 0 < s)
    (hsu : s ≤ p.u)
    (hw : wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u = ((xiCmp p.g s p.u : ℝ) : ℂ)⁻¹ *
      zChar (cmpPt p s).g (cmpPt p s).E (mRoot (cmpPt p s).g p.L (cmpPt p s).E) s)
    (ω : Ω W p.L) :
    flowH (cmpPt p s).g W p.L s ω = ((xiCmp p.g s p.u : ℝ) : ℂ) • flowH p.g W p.L p.u ω ∧
      resolventMat (flowH p.g W p.L p.u ω) (wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u) =
        ((xiCmp p.g s p.u : ℝ) : ℂ) • flowG W (cmpPt p s) ω := by
  have _hg : 0 ≤ p.g := hg
  obtain ⟨hξ0, hξ1, hb, hγ⟩ := comparison_xi_facts (g := p.g) hs hsu
  have hu : 0 < p.u := lt_of_lt_of_le hs hsu
  have hscale : flowH (cmpPt p s).g W p.L s ω =
      ((xiCmp p.g s p.u : ℝ) : ℂ) • flowH p.g W p.L p.u ω := by
    refine flowH_scaling p.g (cmpPt p s).g W p.L (u := p.u) (u' := s) (c := xiCmp p.g s p.u)
      hξ0.le hu.le ?_ ?_ ω
    · change Ag (gCmp p.g s p.u) p.L = _
      unfold Ag
      have hb' : (gCmp p.g s p.u / max 1 (gCmp p.g s p.u) : ℝ) =
          xiCmp p.g s p.u * (p.g / max 1 p.g) := hb
      rw [hb', smul_smul]
      push_cast
      rfl
    · change s * gammaG (gCmp p.g s p.u) = _
      rw [hγ]
      field_simp
  refine ⟨hscale, ?_⟩
  have hξne : ((xiCmp p.g s p.u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hξ0.ne'
  rw [hw, comparison_resolvent_smul _ _ hξne, ← hscale]
  rfl

end Samplewise

section Regime

/-- On the reach of a regime, for `W ≥ 1` the time is `< 1`. -/
private lemma comparison_reach_lt_one (R : PropRegime) {W : ℕ} (hW : 1 ≤ W) {d : ℕ} {p : FlowPt}
    (h : CmpReach R.base W d p) : p.u < 1 := by
  induction h with
  | base hp =>
    have h1 := (R.time W _ hp).2
    have h2 : (0 : ℝ) < (W : ℝ) ^ (-3 : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hW) _
    linarith
  | earlier _ _ _ hvu ih => exact lt_of_le_of_lt hvu ih
  | cmp _ _ _ hsu ih => exact lt_of_le_of_lt hsu ih
  | lift _ ih => exact ih

private lemma comparison_blockOf_smul {W L : ℕ} (ξ : ℂ)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c d : Fin L) :
    blockOf (ξ • X) c d = ξ • blockOf X c d := by
  ext α β
  simp [blockOf]

private lemma comparison_blockTr_smul {W L : ℕ} (ξ : ℂ)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c d : Fin L) :
    blockTr (ξ • X) c d = ξ * blockTr X c d := by
  simp only [blockTr, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

private lemma comparison_iSup2_mul {L : ℕ} {ξ : ℝ} (hξ : 0 ≤ ξ) (f : Fin L → Fin L → ℝ) :
    ⨆ c, ⨆ d, ξ * f c d = ξ * ⨆ c, ⨆ d, f c d := by
  simp_rw [← Real.mul_iSup_of_nonneg hξ]

private lemma comparison_iSup2_nonneg {L : ℕ} (f : Fin L → Fin L → ℝ) (hf : ∀ c d, 0 ≤ f c d) :
    0 ≤ ⨆ c, ⨆ d, f c d :=
  Real.iSup_nonneg fun c => Real.iSup_nonneg fun d => hf c d

private lemma comparison_qform_matIm_smul {m : Type*} [Fintype m] (ξ : ℝ) (X : Matrix m m ℂ)
    (v : m → ℂ) : qform (matIm ((ξ : ℂ) • X)) v = ξ * qform (matIm X) v := by
  rw [comparison_qform_matIm, comparison_qform_matIm, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, Complex.im_ofReal_mul]

open scoped Matrix.Norms.L2Operator in
/-- The three comparisons of (5.35) [fo:eq:backward-matching] for `G(z)` against `G'`, when
`G(w) = ξ G'` with `0 < ξ ≤ 1`
and `Im w/Im z ≤ K`. -/
private lemma comparison_scaled {W L : ℕ} {H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hH : H.IsHermitian) {z w : ℂ} (hre : z.re = w.re) (hz : 0 < z.im) (hzw : z.im ≤ w.im)
    (G' : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hF : resolventMat H w = (ξ : ℂ) • G') {K : ℝ} (hK : w.im / z.im ≤ K) :
    (∀ v : Fin L × Fin W → ℂ,
      qform (matIm (resolventMat H z)) v ≤ K * qform (matIm G') v) ∧
    (∀ a b : Fin L, ‖blockOf (resolventMat H z) a b‖ ≤
      K * ⨆ c : Fin L, ⨆ e : Fin L, ‖blockOf G' c e‖) ∧
    ∀ a b : Fin L, ‖blockTr (resolventMat H z) a b‖ ≤
      K * ⨆ c : Fin L, ⨆ e : Fin L, ‖blockTr G' c e‖ := by
  have hwpos : 0 < w.im := lt_of_lt_of_le hz hzw
  have hK0 : 0 ≤ w.im / z.im := div_nonneg hwpos.le hz.le
  obtain ⟨c1, c2, c3⟩ := resolvent_vertical_cmp H hH z w hre hz hzw
  rw [hF] at c1 c2 c3
  refine ⟨fun v => ?_, fun a b => ?_, fun a b => ?_⟩
  · have h := c1 v
    have hq : 0 ≤ qform (matIm ((ξ : ℂ) • G')) v := by
      rw [← hF]; exact comparison_qform_resolvent_nonneg hH hwpos v
    rw [comparison_qform_matIm_smul] at h hq
    have hq' : 0 ≤ qform (matIm G') v := nonneg_of_mul_nonneg_right hq hξ0
    have h1 : ξ * qform (matIm G') v ≤ qform (matIm G') v := by nlinarith
    calc _ ≤ w.im / z.im * (ξ * qform (matIm G') v) := h
      _ ≤ w.im / z.im * qform (matIm G') v := mul_le_mul_of_nonneg_left h1 hK0
      _ ≤ _ := mul_le_mul_of_nonneg_right hK hq'
  · have h := c2 a b
    simp_rw [comparison_blockOf_smul, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hξ0.le] at h
    rw [comparison_iSup2_mul hξ0.le] at h
    have hS := comparison_iSup2_nonneg (fun c e => ‖blockOf G' c e‖) fun _ _ => norm_nonneg _
    calc _ ≤ _ := h
      _ ≤ w.im / z.im * ⨆ c : Fin L, ⨆ e : Fin L, ‖blockOf G' c e‖ :=
        mul_le_mul_of_nonneg_left (by nlinarith) hK0
      _ ≤ _ := mul_le_mul_of_nonneg_right hK hS
  · have h := c3 a b
    simp_rw [comparison_blockTr_smul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hξ0.le] at h
    rw [comparison_iSup2_mul hξ0.le] at h
    have hS := comparison_iSup2_nonneg (fun c e => ‖blockTr G' c e‖) fun _ _ => norm_nonneg _
    calc _ ≤ _ := h
      _ ≤ w.im / z.im * ⨆ c : Fin L, ⨆ e : Fin L, ‖blockTr G' c e‖ :=
        mul_le_mul_of_nonneg_left (by nlinarith) hK0
      _ ≤ _ := mul_le_mul_of_nonneg_right hK hS

end Regime

open scoped Matrix.Norms.L2Operator in
/-- Lemma 5.11 [fo:lem:families] in a propagation regime: for `W ≥ W₀`, a point `p` of depth
`d < J` and `1/2 ≤ s ≤ u`, the comparison point has depth `d + 1`, the three comparisons of
(5.35) [fo:eq:backward-matching] hold for every sample with loss `C R`, `R = (1 - s)/(1 - u)`,
and `ζ_s(g') ≤ ζ_u(g)`, `ζ_s(g') ≍ ζ_s(g)`. -/
theorem lemma411 (R : PropRegime) : ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ (d : ℕ) (p : FlowPt) (s : ℝ),
    d < R.J → CmpReach R.base W d p → 1 / 2 ≤ s → s ≤ p.u → ∀ ω : Ω W p.L,
    CmpReach R.base W (d + 1) (cmpPt p s) ∧
    (∀ v : Fin p.L × Fin W → ℂ, qform (matIm (flowG W p ω)) v ≤
      R.C * ((1 - s) / (1 - p.u)) * qform (matIm (flowG W (cmpPt p s) ω)) v) ∧
    (∀ a b : Fin p.L, ‖blockOf (flowG W p ω) a b‖ ≤ R.C * ((1 - s) / (1 - p.u)) *
      ⨆ c : Fin p.L, ⨆ e : Fin p.L, ‖blockOf (flowG W (cmpPt p s) ω) c e‖) ∧
    (∀ a b : Fin p.L, ‖blockTr (flowG W p ω) a b‖ ≤ R.C * ((1 - s) / (1 - p.u)) *
      ⨆ c : Fin p.L, ⨆ e : Fin p.L, ‖blockTr (flowG W (cmpPt p s) ω) c e‖) ∧
    zetaProp (cmpPt p s).g W p.L s ≤ zetaProp p.g W p.L p.u ∧
    zetaProp (cmpPt p s).g W p.L s ≤ 2 * zetaProp p.g W p.L s ∧
    zetaProp p.g W p.L s ≤ 2 * zetaProp (cmpPt p s).g W p.L s := by
  obtain ⟨W₁, h₁⟩ := R.dyson
  obtain ⟨W₂, h₂⟩ := R.cmp
  refine ⟨max 1 (max W₁ W₂), fun W hW d p s hd hreach hs hsu ω => ?_⟩
  have hW1 : 1 ≤ W := (le_max_left _ _).trans hW
  have hWW₁ : W₁ ≤ W := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hWW₂ : W₂ ≤ W := ((le_max_right _ _).trans (le_max_right _ _)).trans hW
  have hlt := comparison_reach_lt_one R hW1 hreach
  obtain ⟨hL3, hg0, -, hmlo, -, -⟩ := h₁ W hWW₁ d p hd.le hreach
  obtain ⟨hre, hη1, hη2, hwid⟩ := h₂ W hWW₂ d p s hd hreach hs hsu
  have hs0 : 0 < s := by linarith
  have hC0 : 0 < R.C := lt_of_lt_of_le one_pos R.one_le_C
  have hmim : 0 < (mRoot p.g p.L p.E).im := lt_of_lt_of_le (inv_pos.mpr hC0) hmlo
  have hη : 0 < etaChar p.g (mRoot p.g p.L p.E) p.u := etaChar_pos _ _ hmim hlt
  obtain ⟨hξ0, hξ1, -, -⟩ := comparison_xi_facts (g := p.g) hs0 hsu
  obtain ⟨hF1, hF2⟩ := flow_cmp_samplewise W p s hg0 hs0 hsu hwid ω
  set z := zChar p.g p.E (mRoot p.g p.L p.E) p.u with hz
  set w := wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u with hw
  set ξ := xiCmp p.g s p.u with hξ
  have hzim : z.im = etaChar p.g (mRoot p.g p.L p.E) p.u := im_zChar _ _ _ _
  have hzpos : 0 < z.im := by rw [hzim]; exact hη
  have hzw : z.im ≤ w.im := by rw [hzim]; exact hη1
  have hK : w.im / z.im ≤ R.C * ((1 - s) / (1 - p.u)) := by
    rw [div_le_iff₀ hzpos, hzim]; exact hη2
  have hK0 : 0 ≤ w.im / z.im := div_nonneg (hzpos.le.trans hzw) hzpos.le
  obtain ⟨c1, c2, c3⟩ := comparison_scaled (flowH_isHermitian p.g W p.L p.u ω) hre.symm hzpos hzw
    (flowG W (cmpPt p s) ω) hξ0 hξ1 hF2 hK
  exact ⟨CmpReach.cmp s hreach hs hsu, c1, c2, c3, zeta_cmp_le p.g hg0 W p.L hW1 (by omega) s p.u
    hs hsu hlt⟩

end LSBA
