import LSBA.Gauss.GUEFirstRow
import LSBA.Gauss.QuadRatio

/-!
# Fixed-vector bounds for a deformed GUE matrix

For `H = A + V`, `A` Hermitian and `V` the `n × n` GUE matrix of (1.2) [eq:covariance]: the
fixed-vector tail `P(‖H⁻¹ v‖₂ ≥ t √n ‖v‖₂) ≤ C/t` of [APSSS, Theorem 1 (1.6)] (GUE case), and
the half moment `E‖H⁻¹ v‖₂^{1/2} ≤ C n^{1/4} ‖v‖₂^{1/2}`, the one-block input [PSSS, (2.4)] of
[PSSS, Theorem 1], which the proof of Theorem 3.1 [thm:strong-upper] cites. Constants are absolute.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `‖c w‖₂ = |c| ‖w‖₂`. -/
private lemma fixedVector_l2Norm_smul {ι : Type*} [Fintype ι] (c : ℂ) (w : ι → ℂ) :
    l2Norm (c • w) = ‖c‖ * l2Norm w := by
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, WithLp.toLp_smul, norm_smul]

/-- `w* w = ‖w‖₂²`. -/
private lemma fixedVector_dot_self {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']

/-- A unitary matrix preserves `‖·‖₂`. -/
private lemma fixedVector_l2Norm_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (w : ι → ℂ) : l2Norm ((U : Matrix ι ι ℂ) *ᵥ w) = l2Norm w := by
  have hU : star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  have h : star ((U : Matrix ι ι ℂ) *ᵥ w) ⬝ᵥ ((U : Matrix ι ι ℂ) *ᵥ w) = star w ⬝ᵥ w := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, hU, Matrix.one_mulVec]
  rw [fixedVector_dot_self, fixedVector_dot_self] at h
  unfold l2Norm
  rw [Complex.ofReal_injective h]

/-- `(k X)⁻¹ = k⁻¹ X⁻¹` for `k ≠ 0`, with the convention `X⁻¹ = 0` for singular `X`. -/
private lemma fixedVector_inv_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℂ} (hk : k ≠ 0)
    (X : Matrix ι ι ℂ) : (k • X)⁻¹ = k⁻¹ • X⁻¹ := by
  by_cases h : IsUnit X.det
  · exact Matrix.inv_smul' (A := X) (Units.mk0 k hk) h
  · have h' : ¬ IsUnit (k • X).det := by
      rw [Matrix.det_smul, IsUnit.mul_iff]
      exact fun h'' => h h''.2
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h',
      smul_zero]

/-- `(U X U*)⁻¹ = U X⁻¹ U*` for unitary `U` and every `X`. -/
private lemma fixedVector_inv_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * X * star (U : Matrix ι ι ℂ))⁻¹ =
      (U : Matrix ι ι ℂ) * X⁻¹ * star (U : Matrix ι ι ℂ) := by
  have h1 : star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  have h2 : (U : Matrix ι ι ℂ) * star (U : Matrix ι ι ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv h1,
    Matrix.inv_eq_left_inv h2, Matrix.mul_assoc]

/-- The matrix inverse `X ↦ X⁻¹ = det(X)⁻¹ adj(X)` is Borel. -/
private lemma fixedVector_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable fun X : Matrix ι ι ℂ => X⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have h : (fun X : Matrix ι ι ℂ => X⁻¹ i j) = fun X => (X.det)⁻¹ * X.adjugate i j := by
    funext X
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [h]
  have hd : Continuous fun X : Matrix ι ι ℂ => X.det := continuous_id.matrix_det
  have ha : Continuous fun X : Matrix ι ι ℂ => X.adjugate i j :=
    (continuous_id.matrix_adjugate).matrix_elem i j
  exact hd.measurable.inv.mul ha.measurable

/-- The GUE matrix of (1.2) [eq:covariance] is continuous in its coordinates. -/
private lemma fixedVector_continuous_gueMat (n : ℕ) : Continuous (gueMat n) := by
  refine continuous_pi fun α => continuous_pi fun β => ?_
  simp only [gueMat, gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

/-- `‖·‖₂` is continuous. -/
private lemma fixedVector_continuous_l2Norm {ι : Type*} [Fintype ι] :
    Continuous (l2Norm : (ι → ℂ) → ℝ) := by
  unfold l2Norm
  fun_prop

/-- For `g ~ N(0, 1)`: `P(|g + w| ≤ h) ≤ h`, since the density is at most `1/2`. -/
private lemma fixedVector_gaussian_le (w : ℂ) (h : ℝ) :
    gaussianReal 0 1 {g : ℝ | ‖(g : ℂ) + w‖ ≤ h} ≤ ENNReal.ofReal h := by
  have hsub : {g : ℝ | ‖(g : ℂ) + w‖ ≤ h} ⊆ Set.Icc (-w.re - h) (-w.re + h) := by
    intro g hg
    have h1 : |g + w.re| ≤ h := by
      have := Complex.abs_re_le_norm ((g : ℂ) + w)
      simp only [Complex.add_re, Complex.ofReal_re] at this
      exact this.trans hg
    rw [abs_le] at h1
    constructor <;> linarith
  have hpdf : ∀ x, gaussianPDF 0 1 x ≤ ENNReal.ofReal (1 / 2) := by
    intro x
    rw [gaussianPDF_def]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    have hpi : (2 : ℝ) ≤ Real.sqrt (2 * π) := by
      rw [Real.le_sqrt' (by norm_num)]
      linarith [Real.pi_gt_three]
    have he : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := sq_nonneg x
      linarith)
    calc (Real.sqrt (2 * π))⁻¹ * Real.exp (-x ^ 2 / 2) ≤ (Real.sqrt (2 * π))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ 1 / 2 := by
          rw [mul_one, one_div]
          exact inv_anti₀ (by norm_num) hpi
  calc gaussianReal 0 1 {g : ℝ | ‖(g : ℂ) + w‖ ≤ h}
      ≤ gaussianReal 0 1 (Set.Icc (-w.re - h) (-w.re + h)) := measure_mono hsub
    _ = ∫⁻ x in Set.Icc (-w.re - h) (-w.re + h), gaussianPDF 0 1 x :=
        gaussianReal_apply 0 one_ne_zero _
    _ ≤ ∫⁻ _ in Set.Icc (-w.re - h) (-w.re + h), ENNReal.ofReal (1 / 2) :=
        lintegral_mono fun x => hpdf x
    _ = ENNReal.ofReal (1 / 2) * ENNReal.ofReal (-w.re + h - (-w.re - h)) := by
        rw [setLIntegral_const, Real.volume_Icc]
    _ = ENNReal.ofReal h := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- The `e₀` case of [APSSS, Theorem 1 (1.6)] at size `m + 1`, given the quadratic-form ratio
bound of [APSSS, Lemma 2.1 (2.7)] on `ℂ^m` with constant `C₈`. -/
private theorem fixedVector_tail_single {C₈ : ℝ} (hC₈ : 0 < C₈) (m : ℕ)
    (h₈ : ∀ Q : Matrix (Fin m) (Fin m) ℂ, Q.IsHermitian → Q ≠ 0 →
      ∀ (b : Fin m → ℂ) (a t : ℝ), 0 < t →
        stdCGauss (Fin m) {x | t * ‖star (x + b) ⬝ᵥ (Q *ᵥ (x + b)) - a‖ ≤
          l2Norm (Q *ᵥ (x + b))} ≤ ENNReal.ofReal (C₈ / t))
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hA : A.IsHermitian) {t : ℝ} (ht : 0 < t) :
    μ (m + 1) 1 {ω | t * Real.sqrt ((m : ℝ) + 1) ≤
      l2Norm ((A + gueMat (m + 1) ω)⁻¹ *ᵥ Pi.single 0 1)} ≤
        ENNReal.ofReal ((2 + 2 * C₈) / t) := by
  set r : ℝ := Real.sqrt ((m : ℝ) + 1) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  set D : Matrix (Fin m) (Fin m) ℂ := A.submatrix Fin.succ Fin.succ with hD
  set bv : Fin m → ℂ := (r : ℂ) • fun k => A k.succ 0 with hbv
  set Mf : Ω m 1 → Matrix (Fin m) (Fin m) ℂ :=
    fun ω' => ((Real.sqrt (m : ℝ) : ℝ) : ℂ) • gueMat m ω' + (r : ℂ) • D with hMf
  set Qf : Ω m 1 → Matrix (Fin m) (Fin m) ℂ := fun ω' => (Mf ω')⁻¹ with hQf
  set sf : ℝ × (Fin m → ℂ) × Ω m 1 → ℂ := fun p =>
    (p.1 : ℂ) + (r : ℂ) * A 0 0 - star (p.2.1 + bv) ⬝ᵥ (Qf p.2.2 *ᵥ (p.2.1 + bv)) with hsf
  set Z : Set (ℝ × (Fin m → ℂ) × Ω m 1) := {p | (Mf p.2.2).det = 0} with hZ
  set T₁ : Set (ℝ × (Fin m → ℂ) × Ω m 1) := {p | ‖sf p‖ ≤ 2 / t} with hT₁
  set T₂ : Set (ℝ × (Fin m → ℂ) × Ω m 1) :=
    {p | Qf p.2.2 ≠ 0 ∧ t / 2 * ‖sf p‖ ≤ l2Norm (Qf p.2.2 *ᵥ (p.2.1 + bv))} with hT₂
  set ν : Measure (ℝ × (Fin m → ℂ) × Ω m 1) :=
    (gaussianReal 0 1).prod ((stdCGauss (Fin m)).prod (μ m 1)) with hν
  have hMm : Measurable Mf := by
    have := fixedVector_continuous_gueMat m
    have hc : Continuous Mf := by simp only [hMf]; fun_prop
    exact hc.measurable
  have hQm : Measurable Qf := fixedVector_measurable_inv.comp hMm
  have hΦ : Measurable fun p : ℝ × (Fin m → ℂ) × Ω m 1 => (p.1, p.2.1, Qf p.2.2) :=
    measurable_fst.prodMk (measurable_snd.fst.prodMk (hQm.comp measurable_snd.snd))
  have hsm : Measurable sf := by
    have hG : Continuous fun q : ℝ × (Fin m → ℂ) × Matrix (Fin m) (Fin m) ℂ =>
        (q.1 : ℂ) + (r : ℂ) * A 0 0 - star (q.2.1 + bv) ⬝ᵥ (q.2.2 *ᵥ (q.2.1 + bv)) := by
      fun_prop
    exact hG.measurable.comp hΦ
  have hqm : Measurable fun p : ℝ × (Fin m → ℂ) × Ω m 1 =>
      l2Norm (Qf p.2.2 *ᵥ (p.2.1 + bv)) := by
    have hG : Continuous fun q : ℝ × (Fin m → ℂ) × Matrix (Fin m) (Fin m) ℂ =>
        l2Norm (q.2.2 *ᵥ (q.2.1 + bv)) := by
      have := fixedVector_continuous_l2Norm (ι := Fin m)
      fun_prop
    have h := hG.measurable.comp hΦ
    exact h
  have hT₁m : MeasurableSet T₁ := measurableSet_le hsm.norm measurable_const
  have hT₂m : MeasurableSet T₂ :=
    ((measurableSet_singleton 0).compl.preimage (hQm.comp measurable_snd.snd)).inter
      (measurableSet_le (measurable_const.mul hsm.norm) hqm)
  have hZ0 : ν Z = 0 := by
    have hZ' : μ m 1 {ω' | (Mf ω').det = 0} = 0 := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        have : {ω' : Ω 0 1 | (Mf ω').det = 0} = ∅ := by
          ext ω'
          simp [Matrix.det_isEmpty]
        rw [this, measure_empty]
      · have hDh : ((r : ℂ) • D).IsHermitian := by
          have h1 : D.IsHermitian := hA.submatrix Fin.succ
          ext i j
          simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul',
            Complex.star_def, Complex.conj_ofReal]
          rw [← Complex.star_def, h1.apply]
        have hc : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hm)).ne'
        have h := ae_det_ne_zero_gueMat m hDh hc
        rw [ae_iff] at h
        simpa [Mf, add_comm] using h
    have : Z = Set.univ ×ˢ (Set.univ ×ˢ {ω' | (Mf ω').det = 0}) := by
      ext p
      simp [Z]
    rw [this, hν, Measure.prod_prod, Measure.prod_prod, hZ']
    simp
  have hT₁b : ν T₁ ≤ ENNReal.ofReal (2 / t) := by
    rw [hν, Measure.prod_apply_symm hT₁m]
    calc ∫⁻ y, gaussianReal 0 1 ((fun x => (x, y)) ⁻¹' T₁) ∂((stdCGauss (Fin m)).prod (μ m 1))
        ≤ ∫⁻ _, ENNReal.ofReal (2 / t) ∂((stdCGauss (Fin m)).prod (μ m 1)) := by
          refine lintegral_mono fun y => ?_
          have := fixedVector_gaussian_le
            ((r : ℂ) * A 0 0 - star (y.1 + bv) ⬝ᵥ (Qf y.2 *ᵥ (y.1 + bv))) (2 / t)
          refine le_trans (le_of_eq ?_) this
          congr 1
          ext g
          simp only [Set.mem_preimage, hT₁, Set.mem_ofPred_eq, hsf]
          ring_nf
      _ = ENNReal.ofReal (2 / t) := by simp
  have hT₂b : ν T₂ ≤ ENNReal.ofReal (C₈ / (t / 2)) := by
    rw [hν, Measure.prod_apply hT₂m]
    calc ∫⁻ g, ((stdCGauss (Fin m)).prod (μ m 1)) (Prod.mk g ⁻¹' T₂) ∂(gaussianReal 0 1)
        ≤ ∫⁻ _, ENNReal.ofReal (C₈ / (t / 2)) ∂(gaussianReal 0 1) := by
          refine lintegral_mono fun g => ?_
          rw [Measure.prod_apply_symm (measurable_prodMk_left hT₂m)]
          calc ∫⁻ ω', stdCGauss (Fin m) ((fun x => (x, ω')) ⁻¹' (Prod.mk g ⁻¹' T₂)) ∂(μ m 1)
              ≤ ∫⁻ _, ENNReal.ofReal (C₈ / (t / 2)) ∂(μ m 1) := by
                refine lintegral_mono fun ω' => ?_
                by_cases hQ0 : Qf ω' = 0
                · have : (fun x => (x, ω')) ⁻¹' (Prod.mk g ⁻¹' T₂) = ∅ := by
                    ext x
                    simp [hT₂, hQ0]
                  rw [this, measure_empty]
                  exact bot_le
                have hQh : (Qf ω').IsHermitian := by
                  refine Matrix.IsHermitian.inv ?_
                  have h1 : D.IsHermitian := hA.submatrix Fin.succ
                  have h2 := gueBlock_isHermitian m 1 ω' 0
                  ext i j
                  have e1 : star (D j i) = D i j := congrFun (congrFun h1 i) j
                  have e2 : star (gueMat m ω' j i) = gueMat m ω' i j :=
                    congrFun (congrFun h2 i) j
                  simp only [Mf, Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply,
                    smul_eq_mul, star_add, star_mul', e1, e2]
                  simp
                have hre : A 0 0 = ((A 0 0).re : ℂ) := by
                  have := hA.apply 0 0
                  rw [Complex.star_def] at this
                  exact (Complex.conj_eq_iff_re.mp this).symm
                refine le_trans (measure_mono ?_) (h₈ (Qf ω') hQh hQ0 bv
                  (g + r * (A 0 0).re) (t / 2) (by positivity))
                intro x hx
                simp only [Set.mem_preimage, hT₂, Set.mem_ofPred_eq] at hx
                simp only [Set.mem_ofPred_eq]
                refine le_trans (le_of_eq ?_) hx.2
                congr 1
                rw [hsf, ← norm_neg]
                congr 1
                simp only
                push_cast
                rw [← hre]
                ring
            _ = ENNReal.ofReal (C₈ / (t / 2)) := by simp
      _ = ENNReal.ofReal (C₈ / (t / 2)) := by simp
  have hsub : {ω | t * r ≤ l2Norm ((A + gueMat (m + 1) ω)⁻¹ *ᵥ Pi.single 0 1)} ⊆
      firstRowSplit m ⁻¹' (Z ∪ T₁ ∪ T₂) := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    set p := firstRowSplit m ω with hp
    change p ∈ Z ∪ T₁ ∪ T₂
    by_cases hZp : (Mf p.2.2).det = 0
    · exact Or.inl (Or.inl hZp)
    have hT₁' : ‖sf p‖ ≤ 2 / t → p ∈ Z ∪ T₁ ∪ T₂ := fun h => Or.inl (Or.inr h)
    by_cases hs : sf p = 0
    · exact hT₁' (by rw [hs, norm_zero]; positivity)
    have hB' : (r : ℂ) • (A + gueMat (m + 1) ω) =
        borderMat m ((p.1 : ℂ) + (r : ℂ) * A 0 0) (p.2.1 + bv) (Mf p.2.2) :=
      smul_add_gueMat_eq_borderMat m hA ω
    have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have hnorm : l2Norm ((A + gueMat (m + 1) ω)⁻¹ *ᵥ Pi.single 0 1) =
        r * l2Norm ((borderMat m ((p.1 : ℂ) + (r : ℂ) * A 0 0) (p.2.1 + bv) (Mf p.2.2))⁻¹ *ᵥ
          Pi.single 0 1) := by
      rw [← hB', fixedVector_inv_smul hr0', Matrix.smul_mulVec, fixedVector_l2Norm_smul,
        norm_inv, Complex.norm_real, Real.norm_of_nonneg hr0.le, ← mul_assoc,
        mul_inv_cancel₀ hr0.ne', one_mul]
    have hform := l2Norm_borderMat_inv_single (d := (p.1 : ℂ) + (r : ℂ) * A 0 0)
      (u := p.2.1 + bv) (M := Mf p.2.2) hZp hs
    rw [hnorm, hform] at hω
    have hω' : t ≤ Real.sqrt (1 + l2Norm (Qf p.2.2 *ᵥ (p.2.1 + bv)) ^ 2) / ‖sf p‖ :=
      le_of_mul_le_mul_right (by rw [mul_comm r] at hω; exact hω) hr0
    have hspos : 0 < ‖sf p‖ := norm_pos_iff.mpr hs
    set q := l2Norm (Qf p.2.2 *ᵥ (p.2.1 + bv)) with hq
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hsq : Real.sqrt (1 + q ^ 2) ≤ 1 + q := by
      rw [show 1 + q = Real.sqrt ((1 + q) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hts : t * ‖sf p‖ ≤ 1 + q := by
      rw [le_div_iff₀ hspos] at hω'
      linarith
    by_cases hq1 : q ≤ 1
    · exact hT₁' (by rw [le_div_iff₀ ht]; linarith)
    by_cases hQ0 : Qf p.2.2 = 0
    · exfalso
      apply hq1
      rw [hq, hQ0, Matrix.zero_mulVec]
      simp [l2Norm]
    exact Or.inr ⟨hQ0, by linarith⟩
  calc μ (m + 1) 1 {ω | t * r ≤ l2Norm ((A + gueMat (m + 1) ω)⁻¹ *ᵥ Pi.single 0 1)}
      ≤ μ (m + 1) 1 (firstRowSplit m ⁻¹' (Z ∪ T₁ ∪ T₂)) := measure_mono hsub
    _ ≤ ν (Z ∪ T₁ ∪ T₂) := (measurePreserving_firstRowSplit m).measure_preimage_le _
    _ ≤ ν Z + ν T₁ + ν T₂ := (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ 0 + ENNReal.ofReal (2 / t) + ENNReal.ofReal (C₈ / (t / 2)) := by
        rw [hZ0]
        exact add_le_add (add_le_add le_rfl hT₁b) hT₂b
    _ = ENNReal.ofReal ((2 + 2 * C₈) / t) := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp

/-- [APSSS, Theorem 1 (1.6)], GUE case: `P(‖(A + V)⁻¹ v‖₂ ≥ t √n ‖v‖₂) ≤ C / t` for every
Hermitian `A`, `v ≠ 0` and `t > 0`. -/
theorem gueMat_inv_mulVec_tail : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.IsHermitian → ∀ v : Fin n → ℂ, v ≠ 0 →
      ∀ t : ℝ, 0 < t →
        μ n 1 {ω | t * Real.sqrt n * l2Norm v ≤ l2Norm ((A + gueMat n ω)⁻¹ *ᵥ v)} ≤
          ENNReal.ofReal (C / t) := by
  obtain ⟨C₈, hC₈, h₈⟩ := stdCGauss_quadForm_ratio_le.{0}
  refine ⟨2 + 2 * C₈, by positivity, ?_⟩
  intro n A hA v hv t ht
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exact absurd (Subsingleton.elim v 0) hv
    · exact ⟨m, rfl⟩
  have hv0 : 0 < l2Norm v := by
    rw [l2Norm_eq_norm_toLp, norm_pos_iff]
    intro h
    apply hv
    simpa using congrArg WithLp.ofLp h
  set u : Fin (m + 1) → ℂ := ((l2Norm v)⁻¹ : ℂ) • v with hu
  have hu1 : l2Norm u = 1 := by
    rw [hu, fixedVector_l2Norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hv0.le,
      inv_mul_cancel₀ hv0.ne']
  obtain ⟨U, hU⟩ := exists_unitary_mulVec_eq_single 0 hu1
  set A' := (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) * A *
    star (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) with hA'
  have hA'h : A'.IsHermitian := by
    rw [hA', Matrix.star_eq_conjTranspose]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hA
  have hcore := fixedVector_tail_single hC₈ m (fun Q hQ hQ0 b a t ht => h₈ Q hQ hQ0 b a t ht)
    hA'h ht
  have hsub : {ω | t * Real.sqrt ((m + 1 : ℕ) : ℝ) * l2Norm v ≤
      l2Norm ((A + gueMat (m + 1) ω)⁻¹ *ᵥ v)} ⊆
      conjMap (m + 1) 1 U ⁻¹' {ω | t * Real.sqrt ((m : ℝ) + 1) ≤
        l2Norm ((A' + gueMat (m + 1) ω)⁻¹ *ᵥ Pi.single 0 1)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hω ⊢
    have hconj : A' + gueMat (m + 1) (conjMap (m + 1) 1 U ω) =
        (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) * (A + gueMat (m + 1) ω) *
          star (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
      rw [show gueMat (m + 1) (conjMap (m + 1) 1 U ω) =
          (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) * gueMat (m + 1) ω *
            star (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) from gueBlock_conjMap _ _ U ω 0,
        hA', Matrix.mul_add, Matrix.add_mul]
    have h1 : star (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) *
        (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp U.2
    have hval : l2Norm ((A' + gueMat (m + 1) (conjMap (m + 1) 1 U ω))⁻¹ *ᵥ Pi.single 0 1) =
        (l2Norm v)⁻¹ * l2Norm ((A + gueMat (m + 1) ω)⁻¹ *ᵥ v) := by
      rw [hconj, fixedVector_inv_conj, ← hU, Matrix.mulVec_mulVec, Matrix.mul_assoc,
        Matrix.mul_assoc, h1, Matrix.mul_one, ← Matrix.mulVec_mulVec, fixedVector_l2Norm_unitary,
        hu, Matrix.mulVec_smul, fixedVector_l2Norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hv0.le]
    rw [hval, le_inv_mul_iff₀ hv0]
    push_cast at hω
    linarith
  calc μ (m + 1) 1 {ω | t * Real.sqrt ((m + 1 : ℕ) : ℝ) * l2Norm v ≤
        l2Norm ((A + gueMat (m + 1) ω)⁻¹ *ᵥ v)}
      ≤ μ (m + 1) 1 (conjMap (m + 1) 1 U ⁻¹' {ω | t * Real.sqrt ((m : ℝ) + 1) ≤
        l2Norm ((A' + gueMat (m + 1) ω)⁻¹ *ᵥ Pi.single 0 1)}) := measure_mono hsub
    _ ≤ μ (m + 1) 1 {ω | t * Real.sqrt ((m : ℝ) + 1) ≤
        l2Norm ((A' + gueMat (m + 1) ω)⁻¹ *ᵥ Pi.single 0 1)} :=
        (measurePreserving_conjMap (m + 1) 1 U).measure_preimage_le _
    _ ≤ ENNReal.ofReal ((2 + 2 * C₈) / t) := hcore

/-- Half moment ([PSSS, (2.4)] at `s = 1/2`): `E‖(A + V)⁻¹ v‖₂^{1/2} ≤ C n^{1/4} ‖v‖₂^{1/2}` for
every Hermitian `A` and every `v`. -/
theorem gueMat_inv_mulVec_halfMoment : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.IsHermitian → ∀ v : Fin n → ℂ,
      ∫⁻ ω, ENNReal.ofReal (Real.sqrt (l2Norm ((A + gueMat n ω)⁻¹ *ᵥ v))) ∂(μ n 1) ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (l2Norm v)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := gueMat_inv_mulVec_tail
  refine ⟨1 + C₁, by positivity, ?_⟩
  intro n A hA v
  by_cases hv : v = 0
  · subst hv
    simp [l2Norm]
  have hn : 0 < n := by
    rcases n with _ | m
    · exact absurd (Subsingleton.elim v 0) hv
    · exact Nat.succ_pos m
  have hv0 : 0 < l2Norm v := by
    rw [l2Norm_eq_norm_toLp, norm_pos_iff]
    intro h
    apply hv
    simpa using congrArg WithLp.ofLp h
  set κ : ℝ := (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (l2Norm v) with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ2 : κ ^ 2 = Real.sqrt n * l2Norm v := by
    rw [hκ, mul_pow, Real.sq_sqrt hv0.le, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.sqrt_eq_rpow]
    norm_num
  set f : Ω n 1 → ℝ := fun ω => Real.sqrt (l2Norm ((A + gueMat n ω)⁻¹ *ᵥ v)) with hf
  have hfm : Measurable f := by
    have hc : Continuous fun ω : Ω n 1 => A + gueMat n ω :=
      continuous_const.add (fixedVector_continuous_gueMat n)
    have hinv : Measurable fun ω : Ω n 1 => (A + gueMat n ω)⁻¹ :=
      fixedVector_measurable_inv.comp hc.measurable
    have hmv : Continuous fun X : Matrix (Fin n) (Fin n) ℂ => Real.sqrt (l2Norm (X *ᵥ v)) := by
      have := fixedVector_continuous_l2Norm (ι := Fin n)
      fun_prop
    exact hmv.measurable.comp hinv
  have htail : ∀ s ∈ Set.Ioi κ, μ n 1 {ω | s ≤ f ω} ≤
      ENNReal.ofReal (C₁ * κ ^ 2 * s ^ (-2 : ℝ)) := by
    intro s hs
    have hs0 : 0 < s := hκ0.trans hs
    have ht : 0 < s ^ 2 / κ ^ 2 := by positivity
    refine le_trans (measure_mono ?_) ((h₁ n A hA v hv _ ht).trans (le_of_eq ?_))
    · intro ω hω
      simp only [Set.mem_ofPred_eq, hf] at hω ⊢
      rw [Real.le_sqrt' hs0] at hω
      rw [mul_assoc, ← hκ2, div_mul_cancel₀ _ (by positivity)]
      exact hω
    · congr 1
      rw [Real.rpow_neg hs0.le, Real.rpow_two]
      field_simp
  rw [lintegral_eq_lintegral_meas_le _ (ae_of_all _ fun ω => Real.sqrt_nonneg _)
    hfm.aemeasurable, ← Set.Ioc_union_Ioi_eq_Ioi hκ0.le]
  have hint : IntegrableOn (fun s : ℝ => C₁ * κ ^ 2 * s ^ (-2 : ℝ)) (Set.Ioi κ) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hκ0).const_mul _
  calc ∫⁻ s in Set.Ioc 0 κ ∪ Set.Ioi κ, μ n 1 {ω | s ≤ f ω}
      ≤ (∫⁻ s in Set.Ioc 0 κ, μ n 1 {ω | s ≤ f ω}) + ∫⁻ s in Set.Ioi κ, μ n 1 {ω | s ≤ f ω} :=
        lintegral_union_le _ _ _
    _ ≤ (∫⁻ _ in Set.Ioc 0 κ, 1) +
        ∫⁻ s in Set.Ioi κ, ENNReal.ofReal (C₁ * κ ^ 2 * s ^ (-2 : ℝ)) :=
        add_le_add (lintegral_mono fun _ => prob_le_one)
          (setLIntegral_mono' measurableSet_Ioi htail)
    _ = ENNReal.ofReal κ + ENNReal.ofReal (C₁ * κ ^ 2 * κ⁻¹) := by
        rw [setLIntegral_const, Real.volume_Ioc, one_mul, sub_zero,
          ← ofReal_integral_eq_lintegral_ofReal hint
            (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs =>
              by have : 0 < s := hκ0.trans hs; positivity),
          integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hκ0]
        norm_num [Real.rpow_neg_one]
    _ = ENNReal.ofReal ((1 + C₁) * (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (l2Norm v)) := by
        rw [← ENNReal.ofReal_add hκ0.le (by positivity), mul_assoc (1 + C₁), ← hκ]
        congr 1
        field_simp

end LSBA
