import LSBA.Spectral.Measurability

/-!
# Spectral masses on a set of coordinates

For a Hermitian matrix with its orthonormal eigenbasis `ψ_k` and eigenvalues `λ_k`: the coordinate
projection `P_T`, the weighted mass sum `Σ_k ‖P_T ψ_k‖² G(λ_k)`, the mass correlator
`Σ_{λ_k ∈ J} (‖P_{T₁} ψ_k‖² ‖P_{T₂} ψ_k‖²)^{1/2}`, and the number of parameters `u ∈ I` at which
`E` is an eigenvalue of a one-parameter family, counted with the dimension of the kernel. These
are `m_A(k)`, `Q(A, B)` and the root sum of (E.7) [uva:eq:coarea-audit] in Appendix E.1
[app:fr-concentration-proof]; the weighted mass sum is a measurable function of the matrix.
-/

open MeasureTheory Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The coordinate projection `P_T = diag(1_T)`. -/
def coordProj {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => if i ∈ T then 1 else 0

/-- `Σ_k ‖P_T ψ_k‖² G(λ_k)` over the eigenpairs of a Hermitian matrix; `0` otherwise. -/
def eigMassSum {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (T : Finset ι)
    (G : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  if hA : A.IsHermitian then
    ∑ k, ENNReal.ofReal (∑ i ∈ T, ‖hA.eigenvectorBasis k i‖ ^ 2) * G (hA.eigenvalues k)
  else 0

/-- `Σ_{λ_k ∈ J} (‖P_{T₁} ψ_k‖² ‖P_{T₂} ψ_k‖²)^{1/2}` over the eigenpairs of a Hermitian matrix;
`0` otherwise. -/
def eigMassCorr {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (T₁ T₂ : Finset ι)
    (J : Set ℝ) : ℝ :=
  if hA : A.IsHermitian then
    ∑ k ∈ univ.filter (fun k => hA.eigenvalues k ∈ J),
      Real.sqrt ((∑ i ∈ T₁, ‖hA.eigenvectorBasis k i‖ ^ 2) *
        ∑ i ∈ T₂, ‖hA.eigenvectorBasis k i‖ ^ 2)
  else 0

/-- The parameters `u ∈ I` with `E ∈ σ(H(u))`, each counted with `dim ker(H(u) − E)`. -/
def crossCount {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ℝ → Matrix ι ι ℂ) (E : ℝ)
    (I : Set ℝ) : ℝ≥0∞ :=
  ∑' u : I, (Module.finrank ℂ (LinearMap.ker (Matrix.toLin' (H u - (E : ℂ) • 1))) : ℝ≥0∞)

section EigMassCorrAux

/-- For an orthonormal eigenbasis, `Σ_k |ψ_k(i)|² = 1` for every coordinate `i`. -/
private lemma eigMass_sum_sq_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (i : ι) :
    ∑ k, ‖hA.eigenvectorBasis k i‖ ^ 2 = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have h2 := congrFun (congrFun h i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def] at h2
  have h3 : ∀ k, hA.eigenvectorUnitary.1 i k * (starRingEnd ℂ) (hA.eigenvectorUnitary.1 i k) =
      ((‖hA.eigenvectorBasis k i‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  simp only [h3] at h2
  exact_mod_cast h2

/-- For an orthonormal eigenbasis, `Σ_k ‖P_T ψ_k‖² = |T|`. -/
private lemma eigMass_sum_card {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (T : Finset ι) :
    ∑ k, ∑ i ∈ T, ‖hA.eigenvectorBasis k i‖ ^ 2 = T.card := by
  rw [Finset.sum_comm]
  simp [eigMass_sum_sq_eq_one hA]

end EigMassCorrAux

/-- `Q ≤ (|T₁| |T₂|)^{1/2}`: for an orthonormal eigenbasis, `Σ_k ‖P_T ψ_k‖² = |T|`. -/
theorem eigMassCorr_le_sqrt_card {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (T₁ T₂ : Finset ι) (J : Set ℝ) :
    eigMassCorr A T₁ T₂ J ≤ Real.sqrt (T₁.card * T₂.card) := by
  unfold eigMassCorr
  split_ifs with hA
  · have h1 : ∀ k ∈ (univ : Finset ι), 0 ≤ ∑ i ∈ T₁, ‖hA.eigenvectorBasis k i‖ ^ 2 :=
      fun k _ => Finset.sum_nonneg fun i _ => by positivity
    have h2 : ∀ k ∈ (univ : Finset ι), 0 ≤ ∑ i ∈ T₂, ‖hA.eigenvectorBasis k i‖ ^ 2 :=
      fun k _ => Finset.sum_nonneg fun i _ => by positivity
    calc _ ≤ ∑ k, Real.sqrt ((∑ i ∈ T₁, ‖hA.eigenvectorBasis k i‖ ^ 2) *
          ∑ i ∈ T₂, ‖hA.eigenvectorBasis k i‖ ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Real.sqrt_nonneg _)
      _ = ∑ k, Real.sqrt (∑ i ∈ T₁, ‖hA.eigenvectorBasis k i‖ ^ 2) *
          Real.sqrt (∑ i ∈ T₂, ‖hA.eigenvectorBasis k i‖ ^ 2) :=
          Finset.sum_congr rfl fun k hk => Real.sqrt_mul (h1 k hk) _
      _ ≤ Real.sqrt (∑ k, ∑ i ∈ T₁, ‖hA.eigenvectorBasis k i‖ ^ 2) *
          Real.sqrt (∑ k, ∑ i ∈ T₂, ‖hA.eigenvectorBasis k i‖ ^ 2) :=
          Real.sum_sqrt_mul_sqrt_le _ (fun k => h1 k (mem_univ k)) (fun k => h2 k (mem_univ k))
      _ = Real.sqrt (T₁.card * T₂.card) := by
          rw [eigMass_sum_card hA, eigMass_sum_card hA, Real.sqrt_mul (Nat.cast_nonneg _)]
  · positivity

section EigMassSumAux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `(i, i)` entry of `U diag(d) U*` is `Σ_k U_{ik} d_k conj(U_{ik})`. -/
private lemma eigMass_conj_apply (U : Matrix ι ι ℂ) (d : ι → ℂ) (i : ι) :
    (U * Matrix.diagonal d * star U) i i = ∑ k, U i k * d k * star (U i k) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply]

/-- The matrix `1 + c (M - μ)²`, whose inverse tends to the spectral projection of `M` at `μ`
as `c → ∞`. -/
private def eigMassMat (c : ℂ) (M : Matrix ι ι ℂ) (μ : ℝ) : Matrix ι ι ℂ :=
  (1 : Matrix ι ι ℂ) + c • ((M - (μ : ℂ) • 1) * (M - (μ : ℂ) • 1))

/-- For a Hermitian matrix `A = U diag(λ) U*` and `c ≥ 0`,
`(1 + c (A - μ)²)⁻¹ = U diag((1 + c (λ_k - μ)²)⁻¹) U*`. -/
private lemma eigMassMat_inv {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ) (hc : 0 ≤ c)
    (μ : ℝ) :
    (eigMassMat (c : ℂ) A μ)⁻¹ = hA.eigenvectorUnitary.1 *
      Matrix.diagonal (fun k => (((1 + c * (hA.eigenvalues k - μ) ^ 2)⁻¹ : ℝ) : ℂ)) *
      star hA.eigenvectorUnitary.1 := by
  set U : Matrix ι ι ℂ := hA.eigenvectorUnitary.1 with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hUU' : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hM : A = U * Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ)) * star U := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have hY : A - (μ : ℂ) • 1 =
      U * Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ) - μ) * star U := by
    have : Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ) - μ) =
        Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ)) - (μ : ℂ) • (1 : Matrix ι ι ℂ) := by
      ext a b
      by_cases hab : a = b <;> simp [hab]
    rw [this, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, hUU, ← hM]
  have hZ : eigMassMat (c : ℂ) A μ = U * Matrix.diagonal (fun k => 1 + (c : ℂ) *
      ((hA.eigenvalues k : ℂ) - μ) ^ 2) * star U := by
    unfold eigMassMat
    rw [hY]
    have h1 : U * Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ) - μ) * star U *
        (U * Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ) - μ) * star U) =
        U * Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ) - μ) ^ 2) * star U := by
      calc _ = U * Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ) - μ) * (star U * U) *
            Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ) - μ) * star U := by
            simp only [mul_assoc]
        _ = _ := by
            rw [hUU', mul_one, mul_assoc U, Matrix.diagonal_mul_diagonal]
            simp only [sq]
    rw [h1]
    have h3 : Matrix.diagonal (fun k => 1 + (c : ℂ) * ((hA.eigenvalues k : ℂ) - μ) ^ 2) =
        (1 : Matrix ι ι ℂ) + (c : ℂ) • Matrix.diagonal
          (fun k => ((hA.eigenvalues k : ℂ) - μ) ^ 2) := by
      ext a b
      by_cases hab : a = b <;> simp [hab]
    rw [h3, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, hUU]
  apply Matrix.inv_eq_right_inv
  rw [hZ]
  calc _ = U * (Matrix.diagonal (fun k => 1 + (c : ℂ) * ((hA.eigenvalues k : ℂ) - μ) ^ 2) *
        Matrix.diagonal (fun k => (((1 + c * (hA.eigenvalues k - μ) ^ 2)⁻¹ : ℝ) : ℂ))) *
        star U := by
        simp only [mul_assoc]
        rw [← mul_assoc (star U) U, hUU', one_mul]
    _ = 1 := by
        rw [Matrix.diagonal_mul_diagonal]
        have : (fun k => (1 + (c : ℂ) * ((hA.eigenvalues k : ℂ) - μ) ^ 2) *
            (((1 + c * (hA.eigenvalues k - μ) ^ 2)⁻¹ : ℝ) : ℂ)) = fun _ => 1 := by
          funext k
          have hpos : (0 : ℝ) < 1 + c * (hA.eigenvalues k - μ) ^ 2 := by
            nlinarith [mul_nonneg hc (sq_nonneg (hA.eigenvalues k - μ))]
          have : (1 + (c : ℂ) * ((hA.eigenvalues k : ℂ) - μ) ^ 2) =
              ((1 + c * (hA.eigenvalues k - μ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
          rw [this, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne']
          simp
        rw [this, Matrix.diagonal_one, mul_one, hUU]

/-- The real part of `Σ_{i ∈ T} ((1 + c (M - μ)²)⁻¹)_{ii}`. -/
private def eigMassApprox (T : Finset ι) (c : ℝ) (M : Matrix ι ι ℂ) (μ : ℝ) : ℝ :=
  ∑ i ∈ T, ((eigMassMat (c : ℂ) M μ)⁻¹ i i).re

/-- For Hermitian `A` and `c ≥ 0`, `eigMassApprox T c A μ = Σ_k (1 + c (λ_k - μ)²)⁻¹ ‖P_T ψ_k‖²`. -/
private lemma eigMassApprox_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (T : Finset ι) (c : ℝ)
    (hc : 0 ≤ c) (μ : ℝ) :
    eigMassApprox T c A μ = ∑ k, (1 + c * (hA.eigenvalues k - μ) ^ 2)⁻¹ *
      ∑ i ∈ T, ‖hA.eigenvectorBasis k i‖ ^ 2 := by
  unfold eigMassApprox
  rw [eigMassMat_inv hA c hc μ]
  have h3 : ∀ (i k : ι), hA.eigenvectorUnitary.1 i k *
      (((1 + c * (hA.eigenvalues k - μ) ^ 2)⁻¹ : ℝ) : ℂ) * star (hA.eigenvectorUnitary.1 i k) =
      (((1 + c * (hA.eigenvalues k - μ) ^ 2)⁻¹ * ‖hA.eigenvectorBasis k i‖ ^ 2 : ℝ) : ℂ) := by
    intro i k
    have : hA.eigenvectorUnitary.1 i k * (starRingEnd ℂ) (hA.eigenvectorUnitary.1 i k) =
        ((‖hA.eigenvectorBasis k i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rfl
    rw [Complex.star_def]
    calc _ = (((1 + c * (hA.eigenvalues k - μ) ^ 2)⁻¹ : ℝ) : ℂ) *
          (hA.eigenvectorUnitary.1 i k * (starRingEnd ℂ) (hA.eigenvectorUnitary.1 i k)) := by ring
      _ = _ := by rw [this, ← Complex.ofReal_mul]
  simp only [eigMass_conj_apply, h3, Complex.re_sum, Complex.ofReal_re]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum]

/-- `Σ_{k : λ_k = μ} ‖P_T ψ_k‖²`, the mass on `T` of the eigenspace at `μ` (`0` off Hermitian
matrices). -/
private def eigMassAt (T : Finset ι) (M : Matrix ι ι ℂ) (μ : ℝ) : ℝ :=
  if hM : M.IsHermitian then
    ∑ k ∈ univ.filter (fun k => hM.eigenvalues k = μ), ∑ i ∈ T, ‖hM.eigenvectorBasis k i‖ ^ 2
  else 0

/-- `eigMassApprox T n² A μ` tends to `eigMassAt T A μ` as `n → ∞` for Hermitian `A`. -/
private lemma tendsto_eigMassApprox {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (T : Finset ι)
    (μ : ℝ) :
    Filter.Tendsto (fun n : ℕ => eigMassApprox T ((n : ℝ) ^ 2) A μ) Filter.atTop
      (nhds (eigMassAt T A μ)) := by
  have hc : ∀ n : ℕ, 0 ≤ ((n : ℝ) ^ 2) := fun n => by positivity
  have h1 : (fun n : ℕ => eigMassApprox T ((n : ℝ) ^ 2) A μ) = fun n : ℕ => ∑ k,
      (1 + ((n : ℝ) ^ 2) * (hA.eigenvalues k - μ) ^ 2)⁻¹ *
        ∑ i ∈ T, ‖hA.eigenvectorBasis k i‖ ^ 2 := by
    funext n
    exact eigMassApprox_eq hA T _ (hc n) μ
  rw [h1]
  simp only [eigMassAt, hA, ↓reduceDIte]
  rw [Finset.sum_filter]
  refine tendsto_finsetSum _ fun k _ => ?_
  by_cases hk : hA.eigenvalues k = μ
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    have h2 : Filter.Tendsto (fun n : ℕ => (1 + (n : ℝ) ^ 2 * (hA.eigenvalues k - μ) ^ 2)⁻¹)
        Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.inv_tendsto_atTop
      apply Filter.tendsto_atTop_add_const_left
      apply Filter.Tendsto.atTop_mul_const (by have := sub_ne_zero.mpr hk; positivity)
      exact (Filter.tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop
    simpa using h2.mul_const (∑ i ∈ T, ‖hA.eigenvectorBasis k i‖ ^ 2)

/-- `eigMassApprox T c` is measurable in the matrix and `μ` jointly. -/
private lemma measurable_eigMassApprox (T : Finset ι) (c : ℝ) :
    Measurable fun p : Matrix ι ι ℂ × ℝ => eigMassApprox T c p.1 p.2 := by
  unfold eigMassApprox
  refine Finset.measurable_sum _ fun i _ => ?_
  have hZ : Continuous fun p : Matrix ι ι ℂ × ℝ => eigMassMat (c : ℂ) p.1 p.2 := by
    unfold eigMassMat
    fun_prop
  have hdet : Measurable fun p : Matrix ι ι ℂ × ℝ => (eigMassMat (c : ℂ) p.1 p.2).det :=
    (hZ.matrix_det).measurable
  have hadj : Measurable fun p : Matrix ι ι ℂ × ℝ => (eigMassMat (c : ℂ) p.1 p.2).adjugate i i :=
    ((continuous_apply i).comp ((continuous_apply i).comp hZ.matrix_adjugate)).measurable
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  exact Complex.measurable_re.comp (hdet.inv.mul hadj)


omit [Fintype ι] [DecidableEq ι] in
/-- The Hermitian matrices form a measurable set. -/
private lemma measurableSet_isHermitian [Finite ι] :
    MeasurableSet {M : Matrix ι ι ℂ | M.IsHermitian} := by
  have : IsClosed {M : Matrix ι ι ℂ | M.IsHermitian} :=
    isClosed_eq (by unfold Matrix.conjTranspose; fun_prop) continuous_id
  exact this.measurableSet

/-- `(A, μ) ↦ eigMassAt T A μ` is measurable. -/
private lemma measurable_eigMassAt (T : Finset ι) :
    Measurable fun p : Matrix ι ι ℂ × ℝ => eigMassAt T p.1 p.2 := by
  have hS : MeasurableSet {p : Matrix ι ι ℂ × ℝ | p.1.IsHermitian} :=
    measurableSet_isHermitian.preimage measurable_fst
  refine measurable_of_tendsto_metrizable
    (f := fun (n : ℕ) (p : Matrix ι ι ℂ × ℝ) =>
      if p.1.IsHermitian then eigMassApprox T ((n : ℝ) ^ 2) p.1 p.2 else 0) ?_ ?_
  · intro n
    exact Measurable.ite hS (measurable_eigMassApprox T _) measurable_const
  · refine tendsto_pi_nhds.mpr fun p => ?_
    by_cases hp : p.1.IsHermitian
    · simpa [hp] using tendsto_eigMassApprox hp T p.2
    · simp [hp, eigMassAt]

/-- The `j`-th eigenvalue in decreasing order is a measurable function of a measurable family of
matrices. -/
private lemma measurable_sortedEig_comp {X : Type*} [MeasurableSpace X] {A : X → Matrix ι ι ℂ}
    (hA : Measurable A) (j : Fin (Fintype.card ι)) :
    Measurable fun x => sortedEig (A x) j := by
  have h : (fun M : Matrix ι ι ℂ => sortedEig M j) =
      {M : Matrix ι ι ℂ | M.IsHermitian}.piecewise (fun M => sortedEig M j) (fun _ => 0) := by
    funext M
    by_cases hM : M.IsHermitian
    · simp [Set.piecewise, hM]
    · simp [Set.piecewise, hM, sortedEig]
  have h2 : Measurable fun M : Matrix ι ι ℂ => sortedEig M j := by
    rw [h]
    exact ContinuousOn.measurable_piecewise
      ((continuous_apply j).comp_continuousOn continuousOn_sortedEig)
      continuousOn_const measurableSet_isHermitian
  exact h2.comp hA

/-- Grouping the eigenpairs by eigenvalue: each eigenvalue `μ` of multiplicity `m` contributes
`m` copies of `(eigMassAt T A μ / m) G(μ)`. -/
private lemma eigMassSum_eq_fiber {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (T : Finset ι)
    (G : ℝ → ℝ≥0∞) :
    eigMassSum A T G = ∑ k, ENNReal.ofReal (eigMassAt T A (hA.eigenvalues k) /
        ∑ k', if hA.eigenvalues k' = hA.eigenvalues k then (1 : ℝ) else 0) *
      G (hA.eigenvalues k) := by
  have hm : ∀ k, 0 ≤ ∑ i ∈ T, ‖hA.eigenvectorBasis k i‖ ^ 2 :=
    fun k => Finset.sum_nonneg fun i _ => by positivity
  have ha : ∀ μ, eigMassAt T A μ = ∑ k ∈ univ.filter (fun k => hA.eigenvalues k = μ),
      ∑ i ∈ T, ‖hA.eigenvectorBasis k i‖ ^ 2 := by
    intro μ
    simp only [eigMassAt, hA, ↓reduceDIte]
  have hmem : ∀ k ∈ (univ : Finset ι), hA.eigenvalues k ∈ univ.image hA.eigenvalues :=
    fun k _ => Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have hL : eigMassSum A T G = ∑ μ ∈ univ.image hA.eigenvalues,
      ENNReal.ofReal (eigMassAt T A μ) * G μ := by
    simp only [eigMassSum, hA, ↓reduceDIte]
    rw [← Finset.sum_fiberwise_of_maps_to hmem]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [ha, ENNReal.ofReal_sum_of_nonneg (fun k _ => hm k), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [(Finset.mem_filter.mp hk).2]
  rw [hL, ← Finset.sum_fiberwise_of_maps_to hmem]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  obtain ⟨k₀, -, hk₀⟩ := Finset.mem_image.mp hμ
  have hne : (univ.filter (fun k => hA.eigenvalues k = μ)).Nonempty := ⟨k₀, by simp [hk₀]⟩
  have hpos : (0 : ℝ) < ((univ.filter (fun k => hA.eigenvalues k = μ)).card : ℝ) := by
    exact_mod_cast hne.card_pos
  calc ENNReal.ofReal (eigMassAt T A μ) * G μ
      = ∑ k ∈ univ.filter (fun k => hA.eigenvalues k = μ), ENNReal.ofReal (eigMassAt T A μ /
        ((univ.filter (fun k => hA.eigenvalues k = μ)).card : ℝ)) * G μ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_div_cancel₀ _ hpos.ne']
    _ = _ := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := (Finset.mem_filter.mp hk).2
        rw [hk', Finset.sum_boole]

/-- The sum `eigMassSum A T G` of a Hermitian matrix, written over its eigenvalues in decreasing
order. -/
private lemma eigMassSum_eq_sorted {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (T : Finset ι)
    (G : ℝ → ℝ≥0∞) :
    eigMassSum A T G = ∑ j : Fin (Fintype.card ι),
      ENNReal.ofReal (eigMassAt T A (sortedEig A j) /
        ∑ j', if sortedEig A j' = sortedEig A j then (1 : ℝ) else 0) * G (sortedEig A j) := by
  rw [eigMassSum_eq_fiber hA]
  have hev : ∀ k, hA.eigenvalues k =
      sortedEig A ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm k) :=
    eigenvalues_eq_sortedEig hA
  refine Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm _ _ fun k => ?_
  have hc : (∑ k', if hA.eigenvalues k' = hA.eigenvalues k then (1 : ℝ) else 0) =
      ∑ j', if sortedEig A j' = sortedEig A ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm k)
        then (1 : ℝ) else 0 :=
    Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm _ _ fun k' => by
      simp only [hev]
  rw [hc, hev k]

end EigMassSumAux

/-- `x ↦ Σ_k ‖P_T ψ_k(x)‖² G(x, λ_k(x))` is measurable for a measurable matrix family `A` and a
jointly measurable weight `G`; the sum does not depend on the choice of the eigenbasis. -/
theorem measurable_eigMassSum {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*}
    [MeasurableSpace X] {A : X → Matrix ι ι ℂ} (hA : Measurable A) (T : Finset ι)
    {G : X → ℝ → ℝ≥0∞} (hG : Measurable (Function.uncurry G)) :
    Measurable fun x => eigMassSum (A x) T (G x) := by
  have hS : MeasurableSet {x | (A x).IsHermitian} := measurableSet_isHermitian.preimage hA
  have hs := fun j => measurable_sortedEig_comp hA j
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : X → ℝ≥0∞, Ψ = fun x => ∑ j : Fin (Fintype.card ι),
      ENNReal.ofReal (eigMassAt T (A x) (sortedEig (A x) j) /
        ∑ j', if sortedEig (A x) j' = sortedEig (A x) j then (1 : ℝ) else 0) *
        G x (sortedEig (A x) j) := ⟨_, rfl⟩
  have hΨ : Measurable Ψ := by
    rw [hΨdef]
    refine Finset.measurable_sum _ fun j _ => ?_
    refine Measurable.mul (ENNReal.measurable_ofReal.comp (Measurable.div ?_ ?_)) ?_
    · exact (measurable_eigMassAt T).comp (hA.prodMk (hs j))
    · refine Finset.measurable_sum _ fun j' _ => ?_
      exact Measurable.ite (measurableSet_eq_fun (hs j') (hs j)) measurable_const measurable_const
    · exact hG.comp (measurable_id.prodMk (hs j))
  have heq : (fun x => eigMassSum (A x) T (G x)) =
      fun x => if (A x).IsHermitian then Ψ x else 0 := by
    funext x
    by_cases hx : (A x).IsHermitian
    · simp only [hx, ↓reduceIte, hΨdef]
      exact eigMassSum_eq_sorted hx T (G x)
    · simp [eigMassSum, hx]
  rw [heq]
  exact Measurable.ite hS hΨ measurable_const

end LSBA
