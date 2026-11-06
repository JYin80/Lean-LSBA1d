import LSBA.Spectral.SpecProj

/-!
# Smoothness of a spectral projection across a gap

For a Hermitian matrix `M` that does not have `s` as an eigenvalue, the spectral projection
`1_{(s, ∞)}(M)` is a smooth function of `M` along the Hermitian matrices: near such an `M` it is
the Riesz projection `(2 π i)⁻¹ ∮ (z - M)⁻¹ dz` over a contour that encloses the eigenvalues above
`s` and separates them from the others. This is the smoothness of the retained projection on the
invariant open set of Section 9.4.4 [su:sec:cutoff-estimates], where the singular values of the
right product avoid the threshold.
-/

open Real

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

section

open Complex MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix `U diag(d) U*`, for the eigenvector unitary `U` of a Hermitian `M`. -/
private def SpecProjSmooth_eigDiag {M : Matrix n n ℂ} (hM : M.IsHermitian) (d : n → ℂ) :
    Matrix n n ℂ :=
  (hM.eigenvectorUnitary : Matrix n n ℂ) * Matrix.diagonal d *
    (hM.eigenvectorUnitary : Matrix n n ℂ)ᴴ

private lemma SpecProjSmooth_mul_star {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (hM.eigenvectorUnitary : Matrix n n ℂ) * (hM.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp hM.eigenvectorUnitary.2

private lemma SpecProjSmooth_star_mul {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (hM.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hM.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp hM.eigenvectorUnitary.2

private lemma SpecProjSmooth_eigDiag_mul {M : Matrix n n ℂ} (hM : M.IsHermitian) (d e : n → ℂ) :
    SpecProjSmooth_eigDiag hM d * SpecProjSmooth_eigDiag hM e =
      SpecProjSmooth_eigDiag hM (fun k => d k * e k) := by
  unfold SpecProjSmooth_eigDiag
  set U := (hM.eigenvectorUnitary : Matrix n n ℂ)
  calc U * Matrix.diagonal d * Uᴴ * (U * Matrix.diagonal e * Uᴴ)
      = U * Matrix.diagonal d * (Uᴴ * U) * Matrix.diagonal e * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun k => d k * e k) * Uᴴ := by
        rw [SpecProjSmooth_star_mul, Matrix.mul_one, Matrix.mul_assoc U (Matrix.diagonal d),
          Matrix.diagonal_mul_diagonal]

private lemma SpecProjSmooth_eigDiag_const {M : Matrix n n ℂ} (hM : M.IsHermitian) (z : ℂ) :
    SpecProjSmooth_eigDiag hM (fun _ => z) = z • (1 : Matrix n n ℂ) := by
  unfold SpecProjSmooth_eigDiag
  rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    SpecProjSmooth_mul_star]

private lemma SpecProjSmooth_eigDiag_self {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    M = SpecProjSmooth_eigDiag hM (fun k => (hM.eigenvalues k : ℂ)) := by
  have h := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

/-- `w - M = U diag(w - λ) U*`. -/
private lemma SpecProjSmooth_shift {M : Matrix n n ℂ} (hM : M.IsHermitian) (w : ℂ) :
    w • (1 : Matrix n n ℂ) - M =
      SpecProjSmooth_eigDiag hM (fun k => w - (hM.eigenvalues k : ℂ)) := by
  conv_lhs => rw [SpecProjSmooth_eigDiag_self hM, ← SpecProjSmooth_eigDiag_const hM w]
  unfold SpecProjSmooth_eigDiag
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]

/-- `U diag(d) U* = Σ_k d_k u_k u_k*`. -/
private lemma SpecProjSmooth_eigDiag_eq_sum {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (d : n → ℂ) :
    SpecProjSmooth_eigDiag hM d = ∑ k, d k •
      Matrix.vecMulVec ⇑(hM.eigenvectorBasis k) (star ⇑(hM.eigenvectorBasis k)) := by
  unfold SpecProjSmooth_eigDiag
  ext i j
  rw [Matrix.sum_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The resolvent `(z - M)⁻¹ = U diag((z - λ)⁻¹) U*` off the spectrum. -/
private lemma SpecProjSmooth_inverse_eq {M : Matrix n n ℂ} (hM : M.IsHermitian) {z : ℂ}
    (hz : ∀ k, z ≠ (hM.eigenvalues k : ℂ)) :
    Ring.inverse (z • (1 : Matrix n n ℂ) - M) =
      SpecProjSmooth_eigDiag hM (fun k => (z - (hM.eigenvalues k : ℂ))⁻¹) := by
  rw [← Matrix.nonsing_inv_eq_ringInverse, SpecProjSmooth_shift hM z]
  apply Matrix.inv_eq_right_inv
  rw [SpecProjSmooth_eigDiag_mul]
  have h : (fun k => (z - (hM.eigenvalues k : ℂ)) * (z - (hM.eigenvalues k : ℂ))⁻¹) =
      fun _ => (1 : ℂ) := by
    funext k
    exact mul_inv_cancel₀ (sub_ne_zero.2 (hz k))
  rw [h, SpecProjSmooth_eigDiag_const, one_smul]

/-- An eigenvalue `λ_k` of `M` makes `λ_k - M` singular. -/
private lemma SpecProjSmooth_not_isUnit {M : Matrix n n ℂ} (hM : M.IsHermitian) (k : n) :
    ¬ IsUnit ((hM.eigenvalues k : ℂ) • (1 : Matrix n n ℂ) - M) := by
  intro h
  rw [SpecProjSmooth_shift hM] at h
  set U := (hM.eigenvectorUnitary : Matrix n n ℂ)
  have hU : IsUnit U :=
    ⟨⟨U, Uᴴ, SpecProjSmooth_mul_star hM, SpecProjSmooth_star_mul hM⟩, rfl⟩
  have hUs : IsUnit Uᴴ :=
    ⟨⟨Uᴴ, U, SpecProjSmooth_star_mul hM, SpecProjSmooth_mul_star hM⟩, rfl⟩
  set d : n → ℂ := fun j => (hM.eigenvalues k : ℂ) - (hM.eigenvalues j : ℂ)
  have h2 := (hUs.mul h).mul hU
  have h3 : Uᴴ * SpecProjSmooth_eigDiag hM d * U = Matrix.diagonal d := by
    unfold SpecProjSmooth_eigDiag
    calc Uᴴ * (U * Matrix.diagonal d * Uᴴ) * U
        = (Uᴴ * U) * Matrix.diagonal d * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [SpecProjSmooth_star_mul, Matrix.one_mul, Matrix.mul_one]
  rw [h3, Matrix.isUnit_diagonal, Pi.isUnit_iff] at h2
  have := h2 k
  simp only [isUnit_iff_ne_zero] at this
  exact this (by simp [d])

/-- `‖U diag(d) U*‖ ≤ r` when every `|d_k| ≤ r`. -/
private lemma SpecProjSmooth_norm_eigDiag_le {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {d : n → ℂ} {r : ℝ} (hr : 0 ≤ r) (hd : ∀ k, ‖d k‖ ≤ r) :
    ‖SpecProjSmooth_eigDiag hM d‖ ≤ r := by
  have := Matrix.instCStarRing (n := n) (𝕜 := ℂ)
  have hU' : (hM.eigenvectorUnitary : Matrix n n ℂ) ∈ unitary (Matrix n n ℂ) :=
    hM.eigenvectorUnitary.2
  have hUs : (hM.eigenvectorUnitary : Matrix n n ℂ)ᴴ ∈ unitary (Matrix n n ℂ) :=
    Unitary.star_mem hU'
  unfold SpecProjSmooth_eigDiag
  rw [Matrix.mul_assoc, CStarRing.norm_mem_unitary_mul _ hU',
    CStarRing.norm_mul_mem_unitary _ hUs, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hr).mpr hd

/-- If `z` is at distance at least `r` from the spectrum of a Hermitian `M₀` and
`‖M - M₀‖ < r`, then `z - M` is invertible. -/
private lemma SpecProjSmooth_isUnit_of_near {M₀ M : Matrix n n ℂ} (hM₀ : M₀.IsHermitian)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ∀ k, r ≤ ‖z - (hM₀.eigenvalues k : ℂ)‖)
    (hM : ‖M - M₀‖ < r) : IsUnit (z • (1 : Matrix n n ℂ) - M) := by
  have hz0 : ∀ k, z - (hM₀.eigenvalues k : ℂ) ≠ 0 := by
    intro k h
    have := hz k
    rw [h, norm_zero] at this
    linarith
  set A := z • (1 : Matrix n n ℂ) - M₀ with hAdef
  set B := SpecProjSmooth_eigDiag hM₀ (fun k => (z - (hM₀.eigenvalues k : ℂ))⁻¹)
  have hA : A = SpecProjSmooth_eigDiag hM₀ (fun k => z - (hM₀.eigenvalues k : ℂ)) :=
    SpecProjSmooth_shift hM₀ z
  have hAB : A * B = 1 := by
    rw [hA, SpecProjSmooth_eigDiag_mul]
    have h : (fun k => (z - (hM₀.eigenvalues k : ℂ)) * (z - (hM₀.eigenvalues k : ℂ))⁻¹) =
        fun _ => (1 : ℂ) := funext fun k => mul_inv_cancel₀ (hz0 k)
    rw [h, SpecProjSmooth_eigDiag_const, one_smul]
  have hBA : B * A = 1 := by
    rw [hA, SpecProjSmooth_eigDiag_mul]
    have h : (fun k => (z - (hM₀.eigenvalues k : ℂ))⁻¹ * (z - (hM₀.eigenvalues k : ℂ))) =
        fun _ => (1 : ℂ) := funext fun k => inv_mul_cancel₀ (hz0 k)
    rw [h, SpecProjSmooth_eigDiag_const, one_smul]
  have hBn : ‖B‖ ≤ r⁻¹ :=
    SpecProjSmooth_norm_eigDiag_le hM₀ (inv_nonneg.2 hr.le) fun k => by
      rw [norm_inv]
      exact inv_anti₀ hr (hz k)
  have hsmall : ‖B * (M - M₀)‖ < 1 := by
    calc ‖B * (M - M₀)‖ ≤ ‖B‖ * ‖M - M₀‖ := norm_mul_le _ _
      _ ≤ r⁻¹ * ‖M - M₀‖ := by gcongr
      _ < r⁻¹ * r := by gcongr
      _ = 1 := inv_mul_cancel₀ hr.ne'
  have hfac : z • (1 : Matrix n n ℂ) - M = A * (1 - B * (M - M₀)) := by
    rw [mul_sub, mul_one, ← mul_assoc, hAB, one_mul, hAdef]
    abel
  have hAu : IsUnit A := ⟨⟨A, B, hAB, hBA⟩, rfl⟩
  rw [hfac]
  exact hAu.mul (isUnit_one_sub_of_norm_lt_one hsmall)

private lemma SpecProjSmooth_norm_ofReal_sub (x y : ℝ) : ‖(x : ℂ) - (y : ℂ)‖ = |x - y| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- Finite sums commute with circle integrals of circle-integrable matrix functions. -/
private lemma SpecProjSmooth_circleIntegral_sum {ι : Type*} (S : Finset ι) {c : ℂ} {R : ℝ}
    {f : ι → ℂ → Matrix n n ℂ} (h : ∀ i, CircleIntegrable (f i) c R) :
    (∮ z in C(c, R), ∑ i ∈ S, f i z) = ∑ i ∈ S, ∮ z in C(c, R), f i z := by
  induction S using Finset.induction_on with
  | empty => simp [circleIntegral]
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    have hS : CircleIntegrable (fun z => ∑ i ∈ S, f i z) c R := by
      have := CircleIntegrable.sum S (fun i _ => h i)
      convert this using 1
      funext z
      simp
    rw [circleIntegral.integral_add (h a) hS, ih]

/-- The Riesz formula: if the eigenvalues of a Hermitian `M` in `S` lie inside the circle
`C(c, ρ)` and the others outside the closed disc, then `∮ (z - M)⁻¹ dz = 2 π i 1_S(M)`. -/
private lemma SpecProjSmooth_riesz {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (S : Set ℝ)
    (hin : ∀ k, hM.eigenvalues k ∈ S → ((hM.eigenvalues k : ℝ) : ℂ) ∈ Metric.ball c ρ)
    (hout : ∀ k, hM.eigenvalues k ∉ S →
      ((hM.eigenvalues k : ℝ) : ℂ) ∉ Metric.closedBall c ρ) :
    (∮ z in C(c, ρ), Ring.inverse (z • (1 : Matrix n n ℂ) - M)) =
      (2 * π * I) • specProj M S := by
  set P : n → Matrix n n ℂ := fun k =>
    Matrix.vecMulVec ⇑(hM.eigenvectorBasis k) (star ⇑(hM.eigenvectorBasis k)) with hP
  have hne : ∀ z ∈ Metric.sphere c ρ, ∀ k, z ≠ (hM.eigenvalues k : ℂ) := by
    intro z hz k hzk
    rw [Metric.mem_sphere] at hz
    by_cases hk : hM.eigenvalues k ∈ S
    · have := hin k hk
      rw [Metric.mem_ball, ← hzk, hz] at this
      exact lt_irrefl _ this
    · have := hout k hk
      rw [Metric.mem_closedBall, ← hzk, hz] at this
      exact this le_rfl
  have hcongr : (∮ z in C(c, ρ), Ring.inverse (z • (1 : Matrix n n ℂ) - M)) =
      ∮ z in C(c, ρ), ∑ k, (z - (hM.eigenvalues k : ℂ))⁻¹ • P k := by
    apply circleIntegral.integral_congr hρ.le
    intro z hz
    simp only
    rw [SpecProjSmooth_inverse_eq hM (hne z hz), SpecProjSmooth_eigDiag_eq_sum]
  have hint : ∀ k, CircleIntegrable (fun z => (z - (hM.eigenvalues k : ℂ))⁻¹ • P k) c ρ := by
    intro k
    apply ContinuousOn.circleIntegrable hρ.le
    exact ((continuousOn_id.sub continuousOn_const).inv₀ fun z hz =>
      sub_ne_zero.2 (hne z hz k)).smul continuousOn_const
  have hval : ∀ k, (∮ z in C(c, ρ), (z - (hM.eigenvalues k : ℂ))⁻¹) =
      if hM.eigenvalues k ∈ S then 2 * π * I else 0 := by
    intro k
    split_ifs with hk
    · exact circleIntegral.integral_sub_inv_of_mem_ball (hin k hk)
    · have hne' : ∀ z ∈ Metric.closedBall c ρ, z - (hM.eigenvalues k : ℂ) ≠ 0 := by
        intro z hz h
        rw [sub_eq_zero] at h
        exact hout k hk (h ▸ hz)
      exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le
        Set.countable_empty ((continuousOn_id.sub continuousOn_const).inv₀ hne')
        fun z hz => (differentiableAt_id.sub_const _).inv
          (hne' z (Metric.ball_subset_closedBall hz.1))
  rw [hcongr, SpecProjSmooth_circleIntegral_sum _ hint]
  simp only [circleIntegral.integral_smul_const, hval]
  simp only [specProj, hM, ↓reduceDIte]
  rw [Finset.smul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [hP]

/-- `M ↦ ∮_{C(c, ρ)} (z - M)⁻¹ dz` is smooth on an open set of matrices `M` for which `z - M` is
invertible on the whole circle. -/
private lemma SpecProjSmooth_contDiffOn_circleIntegral {U : Set (Matrix n n ℂ)} (hU : IsOpen U)
    (c : ℂ) {ρ : ℝ}
    (hunit : ∀ M ∈ U, ∀ θ : ℝ, IsUnit (circleMap c ρ θ • (1 : Matrix n n ℂ) - M)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun M => ∮ z in C(c, ρ), Ring.inverse (z • (1 : Matrix n n ℂ) - M)) U := by
  let ψ : ContDiffBump (0 : ℝ) := ⟨8, 9, by norm_num, by norm_num⟩
  let F : Matrix n n ℂ → ℝ → Matrix n n ℂ := fun M t =>
    ψ t • ((circleMap 0 ρ (-t) * I) •
      Ring.inverse (circleMap c ρ (-t) • (1 : Matrix n n ℂ) - M))
  let f : ℝ → ℝ := Set.indicator (Set.Ioc 0 (2 * π)) (fun _ => 1)
  have hf : LocallyIntegrable f volume :=
    (locallyIntegrable_const 1).indicator measurableSet_Ioc
  have hgs : ∀ M t, M ∈ U → t ∉ Metric.closedBall (0 : ℝ) 9 → F M t = 0 := by
    intro M t _ ht
    have h0 : ψ t = 0 := by
      apply Function.notMem_support.mp
      rw [ψ.support_eq]
      exact fun h => ht (Metric.ball_subset_closedBall h)
    simp [F, h0]
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F) (U ×ˢ Set.univ) := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : Matrix n n ℂ × ℝ => circleMap c ρ (-p.2) • (1 : Matrix n n ℂ) - p.1) :=
      (((contDiff_circleMap c ρ).comp contDiff_snd.neg).smul contDiff_const).sub contDiff_fst
    obtain ⟨u, hu⟩ := hunit p.1 hp.1 (-p.2)
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ring.inverse
        (circleMap c ρ (-p.2) • (1 : Matrix n n ℂ) - p.1) := by
      rw [← hu]
      exact (contDiffAt_ringInverse ℂ u).restrict_scalars ℝ
    have h3 := h2.comp p h1.contDiffAt
    exact (ψ.contDiff.comp contDiff_snd).contDiffAt.smul
      ((((contDiff_circleMap 0 ρ).comp contDiff_snd.neg).mul contDiff_const).contDiffAt.smul h3)
  have key := contDiffOn_convolution_right_with_param_comp (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ) (contDiffOn_const (c := (0 : ℝ))) hU
    (isCompact_closedBall (0 : ℝ) 9) hgs hf hg
  refine key.congr fun M _ => ?_
  rw [convolution_def]
  have hind : (fun t => (ContinuousLinearMap.lsmul ℝ ℝ (f t)) (F M (0 - t))) =
      Set.indicator (Set.Ioc 0 (2 * π)) (fun t => F M (-t)) := by
    funext t
    by_cases ht : t ∈ Set.Ioc 0 (2 * π) <;> simp [f, ht]
  rw [hind, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  simp only [circleIntegral]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)] at ht
  have hψ : ψ (-t) = 1 := by
    apply ψ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    have := Real.pi_lt_four
    change t ≤ 8
    linarith [ht.2]
  simp only [F, neg_neg, hψ, one_smul, deriv_circleMap]

end

/-- `M ↦ 1_{(s, ∞)}(M)` is smooth on the Hermitian matrices `M` for which `M - s` is
invertible. -/
theorem contDiffOn_specProj_Ioi {n : Type*} [Fintype n] [DecidableEq n] (s : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun M : Matrix n n ℂ => specProj M (Set.Ioi s))
      {M | M.IsHermitian ∧ IsUnit (M - ((s : ℝ) : ℂ) • 1)} := by
  intro M₀ hM₀
  obtain ⟨hH, hunit₀⟩ := hM₀
  set lam := hH.eigenvalues with hlam
  have hne : ∀ j, lam j ≠ s := by
    intro j hj
    apply SpecProjSmooth_not_isUnit hH j
    have : ((hH.eigenvalues j : ℝ) : ℂ) • (1 : Matrix n n ℂ) - M₀ =
        -(M₀ - ((s : ℝ) : ℂ) • 1) := by
      rw [← hlam, hj, neg_sub]
    rw [this]
    exact hunit₀.neg
  set D : ℝ := ∑ j, |lam j - s| with hDdef
  set δ : ℝ := 1 / (1 + ∑ j, |lam j - s|⁻¹) with hδdef
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hD : ∀ j, |lam j - s| ≤ D := fun j =>
    Finset.single_le_sum (f := fun j => |lam j - s|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ j)
  have hδpos : 0 < δ := by
    rw [hδdef]
    have : 0 ≤ ∑ j, |lam j - s|⁻¹ := Finset.sum_nonneg fun j _ => inv_nonneg.2 (abs_nonneg _)
    positivity
  have hδle : ∀ j, δ ≤ |lam j - s| := by
    intro j
    have hpos : 0 < |lam j - s| := abs_pos.2 (sub_ne_zero.2 (hne j))
    have hsum : |lam j - s|⁻¹ ≤ ∑ j, |lam j - s|⁻¹ :=
      Finset.single_le_sum (f := fun j => |lam j - s|⁻¹) (fun i _ => inv_nonneg.2 (abs_nonneg _))
        (Finset.mem_univ j)
    rw [hδdef, div_le_iff₀ (by positivity)]
    calc (1 : ℝ) = |lam j - s| * |lam j - s|⁻¹ := (mul_inv_cancel₀ hpos.ne').symm
      _ ≤ |lam j - s| * (1 + ∑ j, |lam j - s|⁻¹) := by gcongr; linarith
  -- each eigenvalue of `M₀` lies in `[s + δ, s + D]` or in `(-∞, s - δ]`
  have hcase : ∀ j, (s + δ ≤ lam j ∧ lam j ≤ s + D) ∨ lam j ≤ s - δ := by
    intro j
    have h1 := hδle j
    have h2 := hD j
    rcases le_abs'.1 h1 with h | h
    · right; linarith
    · left; constructor
      · linarith
      · linarith [le_abs_self (lam j - s)]
  set cR : ℝ := s + D / 2 + 5 * δ / 4 with hcR
  set ρ : ℝ := D / 2 + 3 * δ / 4 with hρdef
  have hρ : 0 < ρ := by positivity
  set c : ℂ := (cR : ℂ) with hc
  -- the circle stays at distance `δ / 2` from the spectrum of `M₀`
  have hcirc : ∀ θ : ℝ, ∀ j, δ / 2 ≤ ‖circleMap c ρ θ - (lam j : ℂ)‖ := by
    intro θ j
    have hz : ‖circleMap c ρ θ - c‖ = ρ := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ]
    have hcl : ‖c - (lam j : ℂ)‖ = |cR - lam j| := SpecProjSmooth_norm_ofReal_sub _ _
    have t1 := norm_sub_le_norm_sub_add_norm_sub (circleMap c ρ θ) (lam j : ℂ) c
    have t2 := norm_sub_le_norm_sub_add_norm_sub c (circleMap c ρ θ) (lam j : ℂ)
    rw [norm_sub_rev (lam j : ℂ) c] at t1
    rw [norm_sub_rev c (circleMap c ρ θ)] at t2
    rcases hcase j with ⟨h1, h2⟩ | h1
    · have : |cR - lam j| ≤ ρ - δ / 2 := by
        rw [abs_le]; constructor <;> linarith
      linarith
    · have : ρ + δ / 2 ≤ |cR - lam j| := by
        rw [abs_of_nonneg (by linarith)]; linarith
      linarith
  set V : Set (Matrix n n ℂ) := Metric.ball M₀ (δ / 4) with hV
  have hunit : ∀ M ∈ V, ∀ θ : ℝ, IsUnit (circleMap c ρ θ • (1 : Matrix n n ℂ) - M) := by
    intro M hM θ
    rw [hV, Metric.mem_ball, dist_eq_norm] at hM
    exact SpecProjSmooth_isUnit_of_near hH (by positivity) (hcirc θ) (by linarith)
  -- the eigenvalues of a Hermitian `M ∈ V` above `s` lie inside the circle, the others outside
  have hloc : ∀ M ∈ V, ∀ hM : M.IsHermitian, ∀ k,
      (s < hM.eigenvalues k ∧ ((hM.eigenvalues k : ℝ) : ℂ) ∈ Metric.ball c ρ) ∨
      (hM.eigenvalues k ≤ s ∧ ((hM.eigenvalues k : ℝ) : ℂ) ∉ Metric.closedBall c ρ) := by
    intro M hMV hM k
    rw [hV, Metric.mem_ball, dist_eq_norm] at hMV
    obtain ⟨j, hj⟩ : ∃ j, |hM.eigenvalues k - lam j| < δ / 4 := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      apply SpecProjSmooth_not_isUnit hM k
      exact SpecProjSmooth_isUnit_of_near hH (by positivity)
        (fun j => by rw [SpecProjSmooth_norm_ofReal_sub]; exact hcon j) hMV
    have hdist : dist ((hM.eigenvalues k : ℝ) : ℂ) c = |hM.eigenvalues k - cR| := by
      rw [dist_eq_norm, hc, SpecProjSmooth_norm_ofReal_sub]
    rw [abs_lt] at hj
    rcases hcase j with ⟨h1, h2⟩ | h1
    · left
      refine ⟨by linarith, ?_⟩
      rw [Metric.mem_ball, hdist, abs_lt]
      constructor <;> linarith
    · right
      refine ⟨by linarith, ?_⟩
      rw [Metric.mem_closedBall, hdist, not_le, abs_of_neg (by linarith)]
      linarith
  set g : Matrix n n ℂ → Matrix n n ℂ := fun M =>
    (2 * π * Complex.I)⁻¹ • ∮ z in C(c, ρ), Ring.inverse (z • (1 : Matrix n n ℂ) - M) with hgdef
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g V :=
    (SpecProjSmooth_contDiffOn_circleIntegral Metric.isOpen_ball c hunit).const_smul _
  have heq : ∀ M ∈ V, M.IsHermitian → g M = specProj M (Set.Ioi s) := by
    intro M hMV hM
    rw [hgdef]
    simp only
    rw [SpecProjSmooth_riesz hM c hρ (Set.Ioi s), smul_smul, inv_mul_cancel₀, one_smul]
    · simp [Real.pi_ne_zero, Complex.I_ne_zero]
    · intro k hk
      rcases hloc M hMV hM k with h | h
      · exact h.2
      · exact absurd hk (not_lt.2 h.1)
    · intro k hk
      rcases hloc M hMV hM k with h | h
      · exact absurd h.1 hk
      · exact h.2
  have hVn : V ∈ nhds M₀ := Metric.ball_mem_nhds _ (by positivity)
  refine (hg.contDiffAt hVn).contDiffWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [inter_mem_nhdsWithin _ hVn] with M hM
    exact (heq M hM.2 hM.1.1).symm
  · exact (heq M₀ (Metric.mem_ball_self (by positivity)) hH).symm

end LSBA
