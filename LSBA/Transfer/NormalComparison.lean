import LSBA.Transfer.AdaptedProduct
import LSBA.Transfer.OneStep

/-!
# Comparison with the boundary frame

Every boundary frame `Φ` of (8.8) [up:eq:boundary-frame] has normal coordinates `S_E⁻¹ S Φ = (B;
C₀B)` with `C₀` unitary and `B` invertible; the coordinate comparison (11.6)
[lg:eq:coordinate-comparison] between `D_n(Φ; E)` of (8.10) [up:eq:D-definition] and the
normal-coordinate product, in both directions with the explicit constant `K_E =
((2+|E|)/(2−|E|))^{1/2}`; and `‖D⁻¹‖^s ≤ Σ_j ‖D^{−*}e_j‖^s` for `0 < s ≤ 2`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `K_E = ‖S_E‖ ‖S_E⁻¹‖ = ((2 + |E|)/(2 - |E|))^{1/2}`, the constant of (11.6)
[lg:eq:coordinate-comparison]. -/
def coordConst (E : ℝ) : ℝ := Real.sqrt ((2 + |E|) / (2 - |E|))

/-- `coordConst 0 = 1`. -/
private lemma coordConst_zero : coordConst 0 = 1 := by
  simp [coordConst]

/-- `K_E > 0` for `|E| < 2`. -/
private lemma coordConst_pos {E : ℝ} (hE : |E| < 2) : 0 < coordConst E := by
  have h := abs_lt.mp hE
  refine Real.sqrt_pos.mpr (div_pos ?_ ?_) <;> linarith [abs_nonneg E]

/-- The squared Euclidean norm `∑ i, ‖y i‖²` of a coordinate vector. -/
private def ncSq {ι : Type*} [Fintype ι] (y : ι → ℂ) : ℝ := ∑ i, ‖y i‖ ^ 2

private lemma ncSq_nonneg {ι : Type*} [Fintype ι] (y : ι → ℂ) : 0 ≤ ncSq y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma ncSq_eq_zero {ι : Type*} [Fintype ι] {y : ι → ℂ} (h : ncSq y = 0) : y = 0 := by
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖y i‖)).mp h
  funext i
  have := h0 i (Finset.mem_univ i)
  simpa using this

private lemma ncSq_eq_re {ι : Type*} [Fintype ι] (y : ι → ℂ) :
    ncSq y = (star y ⬝ᵥ y).re := by
  simp only [ncSq, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.conj_mul', sq]

private lemma ncSq_mulVec_eq_re {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℂ)
    (x : n → ℂ) : ncSq (B *ᵥ x) = (star x ⬝ᵥ (Bᴴ * B) *ᵥ x).re := by
  rw [ncSq_eq_re, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

/-- Matrices with the same Gram matrix have the same squared norms on every vector. -/
private lemma ncSq_mulVec_gram {m m' n : Type*} [Fintype m] [Fintype m'] [Fintype n]
    {A : Matrix m n ℂ} {A' : Matrix m' n ℂ} (h : Aᴴ * A = A'ᴴ * A') (x : n → ℂ) :
    ncSq (A *ᵥ x) = ncSq (A' *ᵥ x) := by
  rw [ncSq_mulVec_eq_re, ncSq_mulVec_eq_re, h]

private lemma ncSq_mulVec_of_gram_one {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m n ℂ} (h : Aᴴ * A = 1) (x : n → ℂ) : ncSq (A *ᵥ x) = ncSq x := by
  rw [ncSq_mulVec_gram (A' := (1 : Matrix n n ℂ)) (by simpa using h) x, Matrix.one_mulVec]

/-- `‖A x‖² ≤ ‖A‖² ‖x‖²` for the operator norm. -/
private lemma ncSq_mulVec_le {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ)
    (x : n → ℂ) : ncSq (A *ᵥ x) ≤ ‖A‖ ^ 2 * ncSq x := by
  have h := A.l2_opNorm_mulVec (WithLp.toLp 2 x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa [ncSq] using h2

/-- A bound `‖A x‖² ≤ c² ‖x‖²` bounds the operator norm by `c`. -/
private lemma norm_le_of_ncSq_le {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ x : n → ℂ, ncSq (A *ᵥ x) ≤ c ^ 2 * ncSq x) : ‖A‖ ≤ c := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simpa [ncSq] using h x.ofLp

/-- A lower bound `‖x‖² ≤ c² ‖U x‖²` makes a square matrix invertible with `‖U⁻¹‖ ≤ c`. -/
private lemma isUnit_norm_inv_le_of_ncSq {W : ℕ} (U : Matrix (Fin W) (Fin W) ℂ) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ x : Fin W → ℂ, ncSq x ≤ c ^ 2 * ncSq (U *ᵥ x)) :
    IsUnit U ∧ ‖U⁻¹‖ ≤ c := by
  have hU : IsUnit U := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have h0 : ncSq (x - y) ≤ c ^ 2 * ncSq (U *ᵥ (x - y)) := h _
    rw [Matrix.mulVec_sub, hxy, sub_self] at h0
    have : ncSq (0 : Fin W → ℂ) = 0 := by simp [ncSq]
    rw [this, mul_zero] at h0
    exact sub_eq_zero.mp (ncSq_eq_zero (le_antisymm h0 (ncSq_nonneg _)))
  refine ⟨hU, norm_le_of_ncSq_le _ hc fun x => ?_⟩
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have := h (U⁻¹ *ᵥ x)
  rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at this

/-- For an invertible `U`, `‖x‖² ≤ ‖U⁻¹‖² ‖U x‖²`. -/
private lemma ncSq_le_norm_inv_sq {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : IsUnit U)
    (x : Fin W → ℂ) : ncSq x ≤ ‖U⁻¹‖ ^ 2 * ncSq (U *ᵥ x) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have := ncSq_mulVec_le U⁻¹ (U *ᵥ x)
  rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec] at this

private lemma ncSq_colStack {W : ℕ} (X Y : Matrix (Fin W) (Fin W) ℂ) (x : Fin W → ℂ) :
    ncSq (colStack X Y *ᵥ x) = ncSq (X *ᵥ x) + ncSq (Y *ᵥ x) := by
  simp only [ncSq, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.mulVec, dotProduct, colStack,
    Matrix.of_apply]
  simp

private lemma nc_colStack_top_bot {W : ℕ} (Q : Matrix (Fin 2 × Fin W) (Fin W) ℂ) :
    Q = colStack (Matrix.of fun α β => Q (0, α) β) (Matrix.of fun α β => Q (1, α) β) := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack]

private lemma nc_colStack_mul {W : ℕ} (X Y B : Matrix (Fin W) (Fin W) ℂ) :
    colStack X Y * B = colStack (X * B) (Y * B) := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack, Matrix.mul_apply]

private lemma nc_colStack_gram_isoJ {W : ℕ} (X Y : Matrix (Fin W) (Fin W) ℂ) :
    (colStack X Y)ᴴ * isoJ W * colStack X Y = Xᴴ * X - Yᴴ * Y := by
  ext α β
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, colStack, isoJ,
    Matrix.conjTranspose_apply, Matrix.one_apply, sub_eq_add_neg]

private lemma nc_mem_unitary_iff {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} :
    U ∈ Matrix.unitaryGroup (Fin W) ℂ ↔ Uᴴ * U = 1 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]

/-! ### The two-sided bound for `S_E` -/

private lemma nc_pair {E : ℝ} {a : ℂ} (ha : a.re = E / 2) (hn : a.re ^ 2 + a.im ^ 2 = 1)
    (u v : ℂ) :
    (2 - |E|) * (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤ ‖u + v‖ ^ 2 + ‖a * u + (starRingEnd ℂ) a * v‖ ^ 2 ∧
      ‖u + v‖ ^ 2 + ‖a * u + (starRingEnd ℂ) a * v‖ ^ 2 ≤ (2 + |E|) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have key : ‖u + v‖ ^ 2 + ‖a * u + (starRingEnd ℂ) a * v‖ ^ 2 =
      2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) + 2 * E * (a * u * (starRingEnd ℂ) v).re := by
    have hE : E = 2 * a.re := by linarith
    rw [hE]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    linear_combination ((u.re - v.re) ^ 2 + (u.im - v.im) ^ 2) * hn
  have hw : |(a * u * (starRingEnd ℂ) v).re| ≤ ‖u‖ * ‖v‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    have ha1 : ‖a‖ = 1 := by
      have : ‖a‖ ^ 2 = 1 := by rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
      nlinarith [norm_nonneg a]
    simp [ha1]
  have huv : ‖u‖ * ‖v‖ ≤ (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  have hb : |E * (a * u * (starRingEnd ℂ) v).re| ≤ |E| * ((‖u‖ ^ 2 + ‖v‖ ^ 2) / 2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hw.trans huv) (abs_nonneg _)
  have hb' := abs_le.mp hb
  constructor <;> nlinarith [hb'.1, hb'.2]

/-- Coordinates of `S_E z`. -/
private lemma nc_freeConj_mulVec {W : ℕ} (E : ℝ) (z : Fin 2 × Fin W → ℂ) (α : Fin W) :
    (freeConj W E *ᵥ z) (0, α) = (((Real.sqrt (2 * Real.sin (freeAngle E)))⁻¹ : ℝ) : ℂ) *
        (z (0, α) + z (1, α)) ∧
    (freeConj W E *ᵥ z) (1, α) = (((Real.sqrt (2 * Real.sin (freeAngle E)))⁻¹ : ℝ) : ℂ) *
        (Complex.exp (freeAngle E * Complex.I) * z (0, α) +
          Complex.exp (-(freeAngle E * Complex.I)) * z (1, α)) := by
  constructor <;>
  · simp [freeConj, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.one_apply]
    ring

/-- `K_E⁻¹ ‖z‖² ≤ ‖S_E z‖² ≤ K_E ‖z‖²`, the singular values of `S_E`. -/
private lemma nc_freeConj_sq {W : ℕ} {E : ℝ} (hE : |E| < 2) (z : Fin 2 × Fin W → ℂ) :
    ncSq (freeConj W E *ᵥ z) ≤ coordConst E * ncSq z ∧
      ncSq z ≤ coordConst E * ncSq (freeConj W E *ᵥ z) := by
  have h2 := abs_lt.mp hE
  have hab : 0 ≤ |E| := abs_nonneg E
  set θ := freeAngle E with hθ
  have hcos : Real.cos θ = E / 2 := Real.cos_arccos (by linarith) (by linarith)
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr (by linarith))
      (Real.arccos_lt_pi.mpr (by linarith))
  have hsin2 : Real.sin θ ^ 2 = 1 - (E / 2) ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ
    rw [hcos] at this
    linarith
  set a : ℂ := Complex.exp (θ * Complex.I) with ha
  have hare : a.re = E / 2 := by rw [ha, Complex.exp_ofReal_mul_I_re, hcos]
  have haim : a.im = Real.sin θ := by rw [ha, Complex.exp_ofReal_mul_I_im]
  have hn : a.re ^ 2 + a.im ^ 2 = 1 := by
    rw [ha, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    exact Real.cos_sq_add_sin_sq θ
  have hb : Complex.exp (-(θ * Complex.I)) = (starRingEnd ℂ) a := by
    rw [ha, ← Complex.exp_conj]
    simp
  set c : ℝ := (Real.sqrt (2 * Real.sin θ))⁻¹ with hc
  set κ : ℝ := c ^ 2 with hκ
  have hs2 : 0 < 2 * Real.sin θ := by linarith
  have hκs : κ * (2 * Real.sin θ) = 1 := by
    rw [hκ, hc, inv_pow, Real.sq_sqrt hs2.le]
    exact inv_mul_cancel₀ hs2.ne'
  have hκ0 : 0 ≤ κ := sq_nonneg c
  have hprod : (2 * Real.sin θ) ^ 2 = (2 - |E|) * (2 + |E|) := by
    have : E ^ 2 = |E| ^ 2 := (sq_abs E).symm
    nlinarith [hsin2]
  have hKe : κ * (2 + |E|) = coordConst E := by
    have hx : 0 ≤ (2 + |E|) / (2 - |E|) := div_nonneg (by linarith) (by linarith)
    unfold coordConst
    symm
    rw [Real.sqrt_eq_iff_mul_self_eq hx (mul_nonneg hκ0 (by linarith))]
    have h2e : (2 - |E|) ≠ 0 := by linarith
    have : (κ * (2 + |E|)) * (κ * (2 + |E|)) =
        (κ * (2 * Real.sin θ)) ^ 2 * ((2 + |E|) / (2 - |E|)) := by
      field_simp
      nlinarith [hprod]
    rw [this, hκs]
    ring
  have hKe' : coordConst E * (κ * (2 - |E|)) = 1 := by
    rw [← hKe]
    have : κ * (2 + |E|) * (κ * (2 - |E|)) = (κ * (2 * Real.sin θ)) ^ 2 := by
      rw [mul_pow, hprod]; ring
    rw [this, hκs]
    norm_num
  have hsum : ncSq (freeConj W E *ᵥ z) = κ * ∑ α : Fin W,
      (‖z (0, α) + z (1, α)‖ ^ 2 + ‖a * z (0, α) + (starRingEnd ℂ) a * z (1, α)‖ ^ 2) := by
    simp only [ncSq, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    obtain ⟨h0, h1⟩ := nc_freeConj_mulVec E z α
    rw [h0, h1, hb, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_pow, mul_pow]
    ring
  have hz : ncSq z = ∑ α : Fin W, (‖z (0, α)‖ ^ 2 + ‖z (1, α)‖ ^ 2) := by
    simp only [ncSq, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [← Finset.sum_add_distrib]
  have hup : ∑ α : Fin W,
      (‖z (0, α) + z (1, α)‖ ^ 2 + ‖a * z (0, α) + (starRingEnd ℂ) a * z (1, α)‖ ^ 2) ≤
        (2 + |E|) * ncSq z := by
    rw [hz, Finset.mul_sum]
    exact Finset.sum_le_sum fun α _ => (nc_pair hare hn _ _).2
  have hlo : (2 - |E|) * ncSq z ≤ ∑ α : Fin W,
      (‖z (0, α) + z (1, α)‖ ^ 2 + ‖a * z (0, α) + (starRingEnd ℂ) a * z (1, α)‖ ^ 2) := by
    rw [hz, Finset.mul_sum]
    exact Finset.sum_le_sum fun α _ => (nc_pair hare hn _ _).1
  constructor
  · rw [hsum, ← hKe]
    calc κ * _ ≤ κ * ((2 + |E|) * ncSq z) := mul_le_mul_of_nonneg_left hup hκ0
      _ = κ * (2 + |E|) * ncSq z := by ring
  · rw [hsum]
    calc ncSq z = coordConst E * (κ * (2 - |E|)) * ncSq z := by rw [hKe', one_mul]
      _ = coordConst E * (κ * ((2 - |E|) * ncSq z)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlo hκ0)
        (coordConst_pos hE).le

/-! ### Isotropy of `S_E` -/

private lemma nc_isoJ_mul_self (W : ℕ) : isoJ W * isoJ W = 1 := by
  unfold isoJ
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  have : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, -1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, Matrix.one_kronecker_one]

private lemma nc_phJ_mul_self (W : ℕ) : phJ W * phJ W = 1 := by
  unfold phJ
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  have : (!![0, -Complex.I; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
      !![0, -Complex.I; Complex.I, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, Matrix.one_kronecker_one]

private lemma nc_neg_kronecker {W : ℕ} (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (-A) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) = -(A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) := by
  ext i j
  simp

private lemma nc_freeConj_isoJ {W : ℕ} {E : ℝ} (hE : |E| < 2) :
    freeConj W E * isoJ W * (freeConj W E)ᴴ = phJ W := by
  have h := freeConj_mul_sign_mul_conjTranspose (W := W) hE
  have hs : signKron W = -isoJ W := by
    unfold signKron isoJ
    rw [← nc_neg_kronecker]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hp : (!![0, Complex.I; -Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ) = -phJ W := by
    unfold phJ
    rw [← nc_neg_kronecker]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hs, hp, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
  exact h

private lemma nc_inv_conj_isoJ {W : ℕ} {E : ℝ} (hE : |E| < 2) :
    ((freeConj W E)⁻¹)ᴴ * isoJ W * (freeConj W E)⁻¹ = phJ W := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_freeConj W hE)
  have h1 := nc_freeConj_isoJ (W := W) hE
  have hN : (freeConj W E)⁻¹ * freeConj W E = 1 := Matrix.nonsing_inv_mul _ hdet
  have hN' : freeConj W E * (freeConj W E)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : (((freeConj W E)⁻¹)ᴴ * isoJ W * (freeConj W E)⁻¹) * phJ W = 1 := by
    calc (((freeConj W E)⁻¹)ᴴ * isoJ W * (freeConj W E)⁻¹) * phJ W
        = ((freeConj W E)⁻¹)ᴴ * isoJ W * ((freeConj W E)⁻¹ * freeConj W E) * isoJ W *
            (freeConj W E)ᴴ := by
          rw [← h1]; simp only [Matrix.mul_assoc]
      _ = ((freeConj W E)⁻¹)ᴴ * (isoJ W * isoJ W) * (freeConj W E)ᴴ := by
          rw [hN, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [nc_isoJ_mul_self, Matrix.mul_one, ← Matrix.conjTranspose_mul, hN',
            Matrix.conjTranspose_one]
  calc ((freeConj W E)⁻¹)ᴴ * isoJ W * (freeConj W E)⁻¹
      = (((freeConj W E)⁻¹)ᴴ * isoJ W * (freeConj W E)⁻¹ * phJ W) * phJ W := by
        rw [Matrix.mul_assoc _ (phJ W) (phJ W), nc_phJ_mul_self, Matrix.mul_one]
    _ = phJ W := by rw [h2, Matrix.one_mul]

private lemma nc_conjTranspose_phJ {W : ℕ} {E : ℝ} (hE : |E| < 2) :
    (freeConj W E)ᴴ * phJ W * freeConj W E = isoJ W := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_freeConj W hE)
  have hN : (freeConj W E)⁻¹ * freeConj W E = 1 := Matrix.nonsing_inv_mul _ hdet
  calc (freeConj W E)ᴴ * phJ W * freeConj W E
      = (freeConj W E)ᴴ * (((freeConj W E)⁻¹)ᴴ * isoJ W * (freeConj W E)⁻¹) * freeConj W E := by
        rw [nc_inv_conj_isoJ hE]
    _ = ((freeConj W E)⁻¹ * freeConj W E)ᴴ * isoJ W * ((freeConj W E)⁻¹ * freeConj W E) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = isoJ W := by rw [hN, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/-- `S_E⁻¹ S Φ` for a frame with `Φ* Φ = 1`: `K_E⁻¹ ‖x‖² ≤ ‖S_E⁻¹ S Φ x‖² ≤ K_E ‖x‖²`. -/
private lemma nc_normal_bounds {W : ℕ} {E : ℝ} (hE : |E| < 2)
    {Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ} (hΦ : Φᴴ * Φ = 1) (x : Fin W → ℂ) :
    ncSq x ≤ coordConst E * ncSq (((freeConj W E)⁻¹ * freeConj W 0 * Φ) *ᵥ x) ∧
      ncSq (((freeConj W E)⁻¹ * freeConj W 0 * Φ) *ᵥ x) ≤ coordConst E * ncSq x := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_freeConj W hE)
  have hΦx : ncSq (Φ *ᵥ x) = ncSq x := ncSq_mulVec_of_gram_one hΦ x
  have hz : ncSq (freeConj W 0 *ᵥ (Φ *ᵥ x)) = ncSq x := by
    have h0 := nc_freeConj_sq (W := W) (E := 0) (by norm_num) (Φ *ᵥ x)
    rw [coordConst_zero, one_mul, one_mul, hΦx] at h0
    exact le_antisymm h0.1 h0.2
  have hNz : ((freeConj W E)⁻¹ * freeConj W 0 * Φ) *ᵥ x =
      (freeConj W E)⁻¹ *ᵥ (freeConj W 0 *ᵥ (Φ *ᵥ x)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hs := nc_freeConj_sq hE ((freeConj W E)⁻¹ *ᵥ (freeConj W 0 *ᵥ (Φ *ᵥ x)))
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec, hz] at hs
  rw [hNz]
  exact ⟨hs.1, hs.2⟩

/-- The transformed initial frame (Section 11.1 [lg:sec:scalar-growth]): for a frame `Φ` with
(8.8) [up:eq:boundary-frame], `S_E⁻¹ S Φ = (I; C₀) B` with `C₀` unitary and `B` invertible. -/
theorem exists_normalFrame {W : ℕ} {E : ℝ} (hE : |E| < 2)
    {Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ} (hΦ : IsBoundaryFrame Φ) :
    ∃ C₀ ∈ Matrix.unitaryGroup (Fin W) ℂ, ∃ B : Matrix (Fin W) (Fin W) ℂ, IsUnit B ∧
      (freeConj W E)⁻¹ * freeConj W 0 * Φ = colStack B (C₀ * B) := by
  set Ψ := (freeConj W E)⁻¹ * freeConj W 0 * Φ with hΨ
  obtain ⟨X, Y, hXY⟩ : ∃ X Y : Matrix (Fin W) (Fin W) ℂ, Ψ = colStack X Y :=
    ⟨_, _, nc_colStack_top_bot Ψ⟩
  have hiso : Ψᴴ * isoJ W * Ψ = 0 := by
    calc Ψᴴ * isoJ W * Ψ
        = Φᴴ * ((freeConj W 0)ᴴ * (((freeConj W E)⁻¹)ᴴ * isoJ W * (freeConj W E)⁻¹) *
            freeConj W 0) * Φ := by
          simp only [hΨ, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Φᴴ * ((freeConj W 0)ᴴ * phJ W * freeConj W 0) * Φ := by
          rw [nc_inv_conj_isoJ hE]
      _ = 0 := by rw [nc_conjTranspose_phJ (by norm_num)]; exact hΦ.2
  have hXYg : Xᴴ * X = Yᴴ * Y := by
    rw [hXY, nc_colStack_gram_isoJ] at hiso
    exact sub_eq_zero.mp hiso
  have hK := coordConst_pos hE
  have hXu : IsUnit X := by
    refine (isUnit_norm_inv_le_of_ncSq X (c := Real.sqrt (2 * coordConst E))
      (Real.sqrt_nonneg _) fun x => ?_).1
    have h1 := (nc_normal_bounds hE hΦ.1 x).1
    rw [← hΨ, hXY, ncSq_colStack, ncSq_mulVec_gram hXYg.symm x] at h1
    rw [Real.sq_sqrt (by positivity)]
    linarith
  have hdetX := (Matrix.isUnit_iff_isUnit_det _).mp hXu
  have hUu : (Y * X⁻¹)ᴴ * (Y * X⁻¹) = 1 := by
    calc (Y * X⁻¹)ᴴ * (Y * X⁻¹) = (X⁻¹)ᴴ * (Yᴴ * Y) * X⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (X * X⁻¹)ᴴ * (X * X⁻¹) := by
          rw [← hXYg]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hdetX, Matrix.conjTranspose_one, Matrix.mul_one]
  refine ⟨Y * X⁻¹, nc_mem_unitary_iff.mpr hUu, X, hXu, ?_⟩
  rw [hXY, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetX, Matrix.mul_one]

/-- (11.6) [lg:eq:coordinate-comparison] with the explicit constant `K_E`:
`K_E⁻¹ ‖D_n(C₀; E)⁻¹‖ ≤ ‖D_n(Φ; E)⁻¹‖ ≤ K_E ‖D_n(C₀; E)⁻¹‖`, where `D_n(Φ; E)` is (8.10)
[up:eq:D-definition]. -/
theorem norm_inv_frameD_le {W : ℕ} {E : ℝ} (hE : |E| < 2) (g : ℝ)
    {Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ} (hΦ : IsBoundaryFrame Φ)
    {C₀ B : Matrix (Fin W) (Fin W) ℂ} (hC₀ : C₀ ∈ Matrix.unitaryGroup (Fin W) ℂ)
    (hB : (freeConj W E)⁻¹ * freeConj W 0 * Φ = colStack B (C₀ * B))
    {V : ℕ → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ k, (V k).IsHermitian) (n : ℕ) :
    ‖(frameD (transferProd g (E : ℂ) V n) Φ)⁻¹‖ ≤ coordConst E * ‖(normalD g E C₀ V n)⁻¹‖ ∧
      ‖(normalD g E C₀ V n)⁻¹‖ ≤ coordConst E * ‖(frameD (transferProd g (E : ℂ) V n) Φ)⁻¹‖ := by
  have hK := coordConst_pos hE
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_freeConj W hE)
  have hSN : freeConj W E * (freeConj W E)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  set K := coordConst E with hKdef
  set M := transferProd g (E : ℂ) V n with hM
  set D₀ := normalD g E C₀ V n with hD₀
  set Dφ := frameD M Φ with hDφ
  set Q : Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
    colStack 1 (chainC g E C₀ V n) with hQ
  have hCn := nc_mem_unitary_iff.mp (chainC_mem_unitaryGroup g E hC₀ hV n)
  have hC₀' := nc_mem_unitary_iff.mp hC₀
  -- the iterated (11.3) [lg:eq:matrix-update] in the notation of the frame
  have hnormal : (freeConj W E)⁻¹ * M * freeConj W E * colStack 1 C₀ = Q * D₀ := by
    rw [hM, hQ, hD₀, inv_freeConj_mul_transferProd_mul_colStack hE g hC₀ hV n,
      normalD_eq hE g hC₀ hV n, Matrix.mul_smul]
  have hSΦ : freeConj W 0 * Φ = freeConj W E * (colStack 1 C₀ * B) := by
    have h1 : colStack 1 C₀ * B = colStack B (C₀ * B) := by
      rw [nc_colStack_mul, Matrix.one_mul]
    rw [h1, ← hB]
    simp only [← Matrix.mul_assoc, hSN, Matrix.one_mul]
  have hMSΦ : M * freeConj W 0 * Φ = freeConj W E * Q * D₀ * B := by
    have h1 : M * freeConj W 0 * Φ = M * freeConj W E * colStack 1 C₀ * B := by
      rw [Matrix.mul_assoc M, hSΦ]; simp only [Matrix.mul_assoc]
    have h2 : M * freeConj W E * colStack 1 C₀ = freeConj W E * (Q * D₀) := by
      rw [← hnormal]; simp only [← Matrix.mul_assoc, hSN, Matrix.one_mul]
    rw [h1, h2]; simp only [Matrix.mul_assoc]
  have hDgram := frameD_gram (transferProd_conjTranspose_mul_phJ g E V hV n) hΦ
  have hDx : ∀ x, ncSq (Dφ *ᵥ x) =
      ncSq (freeConj W E *ᵥ (Q *ᵥ (D₀ *ᵥ (B *ᵥ x)))) := by
    intro x
    rw [← ncSq_mulVec_gram hDgram x, hMSΦ]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hQw : ∀ w, ncSq (Q *ᵥ w) = 2 * ncSq w := by
    intro w
    rw [hQ, ncSq_colStack, Matrix.one_mulVec, ncSq_mulVec_of_gram_one hCn w]
    ring
  have hDb : ∀ x, ncSq (Dφ *ᵥ x) ≤ 2 * K * ncSq (D₀ *ᵥ (B *ᵥ x)) ∧
      2 * ncSq (D₀ *ᵥ (B *ᵥ x)) ≤ K * ncSq (Dφ *ᵥ x) := by
    intro x
    have h := nc_freeConj_sq hE (Q *ᵥ (D₀ *ᵥ (B *ᵥ x)))
    rw [hQw, ← hDx] at h
    constructor <;> linarith [h.1, h.2]
  have hBb : ∀ x, ncSq x ≤ 2 * K * ncSq (B *ᵥ x) ∧ 2 * ncSq (B *ᵥ x) ≤ K * ncSq x := by
    intro x
    have h := nc_normal_bounds hE hΦ.1 x
    rw [hB, ncSq_colStack, ← Matrix.mulVec_mulVec, ncSq_mulVec_of_gram_one hC₀'] at h
    constructor <;> linarith [h.1, h.2]
  have hD₀u : IsUnit D₀ := isUnit_normalD hE g hC₀ hV n
  have hL₀ := fun y => ncSq_le_norm_inv_sq hD₀u y
  have hP1 : IsUnit Dφ ∧ ‖Dφ⁻¹‖ ≤ K * ‖D₀⁻¹‖ := by
    refine isUnit_norm_inv_le_of_ncSq Dφ (mul_nonneg hK.le (norm_nonneg _)) fun x => ?_
    have h1 := (hBb x).1
    have h2 := hL₀ (B *ᵥ x)
    have h3 := (hDb x).2
    calc ncSq x ≤ 2 * K * ncSq (B *ᵥ x) := h1
      _ ≤ 2 * K * (‖D₀⁻¹‖ ^ 2 * ncSq (D₀ *ᵥ (B *ᵥ x))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = K * ‖D₀⁻¹‖ ^ 2 * (2 * ncSq (D₀ *ᵥ (B *ᵥ x))) := by ring
      _ ≤ K * ‖D₀⁻¹‖ ^ 2 * (K * ncSq (Dφ *ᵥ x)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (K * ‖D₀⁻¹‖) ^ 2 * ncSq (Dφ *ᵥ x) := by ring
  obtain ⟨hDφu, hP1⟩ := hP1
  have hBu : IsUnit B := by
    refine (isUnit_norm_inv_le_of_ncSq B (c := Real.sqrt (2 * K)) (Real.sqrt_nonneg _)
      fun x => ?_).1
    rw [Real.sq_sqrt (by positivity)]
    exact (hBb x).1
  have hBdet := (Matrix.isUnit_iff_isUnit_det _).mp hBu
  refine ⟨hP1, ?_⟩
  refine (isUnit_norm_inv_le_of_ncSq D₀ (mul_nonneg hK.le (norm_nonneg _)) fun y => ?_).2
  have hBx : B *ᵥ (B⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hBdet, Matrix.one_mulVec]
  have h1 := (hBb (B⁻¹ *ᵥ y)).2
  have h2 := ncSq_le_norm_inv_sq hDφu (B⁻¹ *ᵥ y)
  have h3 := (hDb (B⁻¹ *ᵥ y)).1
  rw [hBx] at h1 h3
  have h4 : 2 * ncSq y ≤ K * (‖Dφ⁻¹‖ ^ 2 * (2 * K * ncSq (D₀ *ᵥ y))) :=
    h1.trans (by
      calc K * ncSq (B⁻¹ *ᵥ y) ≤ K * (‖Dφ⁻¹‖ ^ 2 * ncSq (Dφ *ᵥ (B⁻¹ *ᵥ y))) :=
            mul_le_mul_of_nonneg_left h2 hK.le
        _ ≤ K * (‖Dφ⁻¹‖ ^ 2 * (2 * K * ncSq (D₀ *ᵥ y))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (sq_nonneg _)) hK.le)
  nlinarith [h4]

/-- Subadditivity of `t ↦ t ^ p` for `0 < p ≤ 1` over finite sums of nonnegative reals. -/
private lemma nc_rpow_sum_le {ι : Type*} (t : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) : (∑ i ∈ t, f i) ^ p ≤ ∑ i ∈ t, f i ^ p := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Real.zero_rpow hp0.ne']
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc (f a + ∑ i ∈ t, f i) ^ p ≤ f a ^ p + (∑ i ∈ t, f i) ^ p :=
          Real.rpow_add_le_add_rpow (hf a) (Finset.sum_nonneg fun i _ => hf i) hp0.le hp1
      _ ≤ _ := by gcongr

/-- The squared norm of the `j`-th column of `A`, as a sum over entries. -/
private lemma nc_col_norm_sq {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) (j : Fin W) :
    ‖Matrix.toEuclideanLin A (EuclideanSpace.single j 1)‖ ^ 2 = ∑ i, ‖A i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.toLpLin_apply]

/-- The operator norm is at most the Hilbert-Schmidt norm: `‖A‖² ≤ ∑ i j, ‖A i j‖²`. -/
private lemma nc_opNorm_sq_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    ‖A‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have hc : 0 ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := Real.sqrt_nonneg _
  have hnn : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h := norm_le_of_ncSq_le A hc (fun x => by
    rw [Real.sq_sqrt hnn]
    unfold ncSq
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hcs : ‖(A *ᵥ x) i‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ := by
      simp only [Matrix.mulVec, dotProduct]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)
    calc ‖(A *ᵥ x) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖x j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hcs 2
      _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  calc ‖A‖ ^ 2 ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hnn

/-- `‖D⁻¹‖^s ≤ Σ_j ‖D^{-*} e_j‖^s` for `0 < s ≤ 2` (proof of Theorem 11.1
[uvg:thm:transfer]). -/
theorem norm_inv_rpow_le_sum {W : ℕ} (D : Matrix (Fin W) (Fin W) ℂ) {s : ℝ} (hs0 : 0 < s)
    (hs2 : s ≤ 2) :
    ‖D⁻¹‖ ^ s ≤ ∑ j, ‖Matrix.toEuclideanLin (D⁻¹ᴴ) (EuclideanSpace.single j 1)‖ ^ s := by
  set A := D⁻¹ᴴ with hA
  have hnorm : ‖D⁻¹‖ = ‖A‖ := (Matrix.l2_opNorm_conjTranspose _).symm
  have hHS : ‖A‖ ^ 2 ≤ ∑ j, ‖Matrix.toEuclideanLin A (EuclideanSpace.single j 1)‖ ^ 2 := by
    refine (nc_opNorm_sq_le A).trans ?_
    rw [Finset.sum_comm]
    exact (Finset.sum_congr rfl fun j _ => (nc_col_norm_sq A j).symm).le
  have hrp : ∀ t : ℝ, 0 ≤ t → t ^ s = (t ^ 2) ^ (s / 2) := by
    intro t ht
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    congr 1
    push_cast
    ring
  calc ‖D⁻¹‖ ^ s = (‖A‖ ^ 2) ^ (s / 2) := by rw [hnorm]; exact hrp _ (norm_nonneg _)
    _ ≤ (∑ j, ‖Matrix.toEuclideanLin A (EuclideanSpace.single j 1)‖ ^ 2) ^ (s / 2) :=
        Real.rpow_le_rpow (sq_nonneg _) hHS (by positivity)
    _ ≤ ∑ j, (‖Matrix.toEuclideanLin A (EuclideanSpace.single j 1)‖ ^ 2) ^ (s / 2) :=
        nc_rpow_sum_le _ _ (fun j => sq_nonneg _) (by positivity) (by linarith)
    _ = _ := Finset.sum_congr rfl fun j _ => (hrp _ (norm_nonneg _)).symm

end LSBA
