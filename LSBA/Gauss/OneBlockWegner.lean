import LSBA.Gauss.InverseNorm
import LSBA.Spectral.Measurability

/-!
# Wegner bound for a deformed GUE matrix

For `H = A + V`, `A` Hermitian and `V` the `n × n` GUE matrix of (1.2) [eq:covariance]: the
spectrum of `H` is almost surely simple, the eigenvalue count in a measurable set is measurable,
and `E #{eigenvalues of H in [α, β]} ≤ C n (β - α)` with an absolute constant
([APSSS, Theorem 1 (1.8)], GUE case; the one-block intensity bound of (9.58) [us:eq:wegner]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The Hankel determinant `det [Tr A^{i+j}]_{0 ≤ i,j < N}` over a commutative ring. -/
private def oneBlockWegner_hankelR {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n R) : R :=
  (Matrix.of fun i j : Fin (Fintype.card n) => (A ^ (i.val + j.val)).trace).det

/-- The Hankel determinant commutes with ring homomorphisms applied entrywise. -/
private lemma oneBlockWegner_map_hankelR {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    f (oneBlockWegner_hankelR A) = oneBlockWegner_hankelR (A.map f) := by
  unfold oneBlockWegner_hankelR
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, ← Matrix.map_pow]
  exact AddMonoidHom.map_trace f.toAddMonoidHom _

/-- The Hankel discriminant of `diag(0, 1, …, n - 1)` is nonzero. -/
private lemma oneBlockWegner_hankelDisc_diagonal_ne_zero (n : ℕ) :
    hankelDisc (Matrix.diagonal fun i : Fin n => ((i : ℕ) : ℂ)) ≠ 0 := by
  set v : Fin n → ℂ := fun i => ((i : ℕ) : ℂ) with hv
  have hvinj : Function.Injective v := fun i j h => Fin.ext (by simpa [hv] using h)
  have h : (Matrix.of fun i j : Fin (Fintype.card (Fin n)) =>
      ((Matrix.diagonal v) ^ (i.val + j.val)).trace) =
      (Matrix.vandermonde (v ∘ (Fintype.equivFin (Fin n)).symm))ᵀ *
        Matrix.vandermonde (v ∘ (Fintype.equivFin (Fin n)).symm) := by
    ext i j
    rw [Matrix.vandermonde_transpose_mul_vandermonde, Matrix.of_apply, Matrix.diagonal_pow,
      Matrix.trace_diagonal]
    exact (Equiv.sum_comp (Fintype.equivFin (Fin n)).symm
      (fun m => v m ^ (i.val + j.val))).symm
  rw [hankelDisc, h, Matrix.det_mul, Matrix.det_transpose, ← sq, pow_ne_zero_iff two_ne_zero,
    Matrix.det_vandermonde_ne_zero_iff]
  exact Equiv.injective_comp _ _ |>.mpr hvinj

/-- The entries of `A + V` as polynomials in the Gaussian coordinates of the GUE matrix of (1.2)
[eq:covariance]. -/
private def oneBlockWegner_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (α β : Fin n) :
    MvPolynomial (Fin 1 × Fin n × Fin n) ℂ :=
  MvPolynomial.C (A α β) +
    (if α = β then MvPolynomial.X (0, α, α) * MvPolynomial.C (((Real.sqrt n : ℝ) : ℂ)⁻¹)
    else if α < β then
      (MvPolynomial.X (0, α, β) + MvPolynomial.C Complex.I * MvPolynomial.X (0, β, α)) *
        MvPolynomial.C (((Real.sqrt (2 * n) : ℝ) : ℂ)⁻¹)
    else
      (MvPolynomial.X (0, β, α) - MvPolynomial.C Complex.I * MvPolynomial.X (0, α, β)) *
        MvPolynomial.C (((Real.sqrt (2 * n) : ℝ) : ℂ)⁻¹))

private lemma oneBlockWegner_eval_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (ω : Ω n 1)
    (α β : Fin n) :
    MvPolynomial.eval (fun i => (ω i : ℂ)) (oneBlockWegner_entry A α β) =
      (A + gueMat n ω) α β := by
  simp only [oneBlockWegner_entry, gueMat, gueBlock, Matrix.add_apply, Matrix.of_apply, map_add,
    MvPolynomial.eval_C]
  congr 1
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

/-- The Hankel discriminant of `A + V` is the real evaluation of one complex polynomial in the
coordinates. -/
private lemma oneBlockWegner_exists_poly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ P : MvPolynomial (Fin 1 × Fin n × Fin n) ℂ, ∀ ω : Ω n 1,
      hankelDisc (A + gueMat n ω) = MvPolynomial.eval (fun i => (ω i : ℂ)) P := by
  refine ⟨oneBlockWegner_hankelR (Matrix.of fun α β => oneBlockWegner_entry A α β),
    fun ω => ?_⟩
  rw [oneBlockWegner_map_hankelR]
  have : (Matrix.of fun α β => oneBlockWegner_entry A α β).map
      (MvPolynomial.eval fun i => (ω i : ℂ)) = A + gueMat n ω := by
    ext α β
    exact oneBlockWegner_eval_entry A ω α β
  rw [this]
  rfl

/-- `A + V` is Hermitian for Hermitian `A`. -/
private lemma oneBlockWegner_isHermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (ω : Ω n 1) : (A + gueMat n ω).IsHermitian :=
  hA.add (gueBlock_isHermitian n 1 ω 0)

/-- `countIn` is a sum of indicators of the decreasing eigenvalues. -/
private lemma oneBlockWegner_countIn_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) (J : Set ℝ) :
    countIn M J = ∑ j, if sortedEig M j ∈ J then 1 else 0 := by
  simp only [countIn, hM, ↓reduceDIte, Finset.card_filter, eigenvalues_eq_sortedEig hM]
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun j => if sortedEig M j ∈ J then 1 else 0)

/-- For Hermitian `A`, the spectrum of `A + V` is almost surely simple. -/
theorem ae_injective_eigenvalues_add_gueMat (n : ℕ) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) :
    ∀ᵐ ω ∂(μ n 1), Function.Injective (hA.add (gueBlock_isHermitian n 1 ω 0)).eigenvalues := by
  obtain ⟨P, hP⟩ := oneBlockWegner_exists_poly A
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i : Fin n => ((i : ℕ) : ℂ) with hD
  have hDh : (D - A).IsHermitian := by
    refine (Matrix.isHermitian_diagonal_of_self_adjoint _ ?_).sub hA
    ext i
    simp
  set ω₀ : Ω n 1 := gueCoord n 1 (fun _ => D - A) with hω₀
  have hω₀B : gueMat n ω₀ = D - A :=
    congrFun (gueBlock_gueCoord n 1 (fun _ => D - A) (fun _ => hDh)) 0
  have h₀ : MvPolynomial.eval (fun i => (ω₀ i : ℂ)) P ≠ 0 := by
    rw [← hP, hω₀B, add_sub_cancel]
    exact oneBlockWegner_hankelDisc_diagonal_ne_zero n
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hnull :=
    measure_zero_mvPolynomial (fun _ : Fin 1 × Fin n × Fin n => gaussianReal 0 1) P ω₀ h₀
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull
  rw [Set.mem_ofPred_eq] at hω ⊢
  rw [← hP]
  by_contra h
  exact hω ((hankelDisc_ne_zero_iff (oneBlockWegner_isHermitian hA ω)).mp h)

/-- For Hermitian `A` and measurable `J`, `ω ↦ #{eigenvalues of A + V in J}` is measurable. -/
theorem measurable_countIn_add_gueMat (n : ℕ) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable fun ω : Ω n 1 => countIn (A + gueMat n ω) J := by
  have hcont : Continuous fun ω : Ω n 1 => A + gueMat n ω := by
    refine continuous_matrix fun p q => ?_
    simp only [gueMat, gueBlock, Matrix.add_apply, Matrix.of_apply]
    split_ifs <;> fun_prop
  have heq : (fun ω : Ω n 1 => countIn (A + gueMat n ω) J) =
      fun ω => ∑ j, if sortedEig (A + gueMat n ω) j ∈ J then 1 else 0 :=
    funext fun ω => oneBlockWegner_countIn_eq (oneBlockWegner_isHermitian hA ω) J
  rw [heq]
  exact Finset.measurable_sum _ fun j _ => Measurable.ite
    (hJ.preimage ((continuous_apply j).comp (continuousOn_sortedEig.comp_continuous hcont
      fun ω => oneBlockWegner_isHermitian hA ω)).measurable)
    measurable_const measurable_const

/-- `countIn` is the number of eigenvalue indices with eigenvalue in `J`. -/
private lemma oneBlockWegner_countIn_eq_card {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) (J : Set ℝ) :
    countIn M J = #(univ.filter fun k => hM.eigenvalues k ∈ J) := by
  simp only [countIn, hM, ↓reduceDIte]

/-- `A + V` has a positive count of eigenvalues in `J` exactly when some eigenvalue is in `J`. -/
private lemma oneBlockWegner_one_le_countIn {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) (J : Set ℝ) : 1 ≤ countIn M J ↔ ∃ k, hM.eigenvalues k ∈ J := by
  rw [oneBlockWegner_countIn_eq_card hM, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero,
    ← Ne, ← Finset.nonempty_iff_ne_empty]
  simp [Finset.Nonempty]

/-- If `H - c` is invertible, an eigenvalue `λ` of the Hermitian `H` differs from `c` and
`‖(H - c)⁻¹‖ ≥ 1 / |λ - c|`. -/
private lemma oneBlockWegner_eig_inv {n : ℕ} {H M : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) {c : ℝ} (hM : M = H - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
    (hdet : M.det ≠ 0) (k : Fin n) :
    hH.eigenvalues k ≠ c ∧ 1 / |hH.eigenvalues k - c| ≤ ‖M⁻¹‖ := by
  set v : EuclideanSpace ℂ (Fin n) := hH.eigenvectorBasis k with hv
  set e : ℝ := hH.eigenvalues k with he
  have hv1 : ‖v‖ = 1 := (hH.eigenvectorBasis).norm_eq_one k
  have hv0 : (v : Fin n → ℂ) ≠ 0 := by
    intro h
    have : v = 0 := by ext i; simpa using congrFun h i
    rw [this, norm_zero] at hv1
    exact zero_ne_one hv1
  have hMv : M *ᵥ (v : Fin n → ℂ) = ((e - c : ℝ) : ℂ) • (v : Fin n → ℂ) := by
    have h1 := hH.mulVec_eigenvectorBasis k
    rw [hM, Matrix.sub_mulVec, h1, Matrix.smul_mulVec, Matrix.one_mulVec,
      Complex.ofReal_sub, sub_smul]
    congr 1
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hdet)
  have hne : e ≠ c := by
    intro h
    have h1 : M *ᵥ (v : Fin n → ℂ) = 0 := by rw [hMv, h, sub_self]; simp
    apply hv0
    have := congrArg (fun w => M⁻¹ *ᵥ w) h1
    simpa [Matrix.mulVec_mulVec, hinv] using this
  have hec : ((e - c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hMiv : M⁻¹ *ᵥ (v : Fin n → ℂ) = ((e - c : ℝ) : ℂ)⁻¹ • (v : Fin n → ℂ) := by
    have h1 : M⁻¹ *ᵥ (M *ᵥ (v : Fin n → ℂ)) = (v : Fin n → ℂ) := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [hMv, Matrix.mulVec_smul] at h1
    calc M⁻¹ *ᵥ (v : Fin n → ℂ)
        = ((e - c : ℝ) : ℂ)⁻¹ • (((e - c : ℝ) : ℂ) • (M⁻¹ *ᵥ (v : Fin n → ℂ))) := by
          rw [smul_smul, inv_mul_cancel₀ hec, one_smul]
      _ = _ := by rw [h1]
  refine ⟨hne, ?_⟩
  have h2 := Matrix.l2_opNorm_mulVec M⁻¹ v
  have h3 : (EuclideanSpace.equiv (Fin n) ℂ).symm (M⁻¹ *ᵥ (v : Fin n → ℂ)) =
      (((e - c : ℝ) : ℂ)⁻¹) • v := by
    rw [hMiv]
    rfl
  rw [h3, norm_smul, hv1, mul_one, mul_one, norm_inv, Complex.norm_real,
    Real.norm_eq_abs] at h2
  rwa [one_div]

/-- For Hermitian `A` and real `c`, almost surely `A + V - c` is invertible, and then every
eigenvalue `λ` of `A + V` differs from `c` and `‖(A - c + V)⁻¹‖ ≥ 1 / |λ - c|`. -/
private lemma oneBlockWegner_ae_eig_inv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (c : ℝ) :
    ∀ᵐ ω ∂(μ n 1), ∀ k, (oneBlockWegner_isHermitian hA ω).eigenvalues k ≠ c ∧
      1 / |(oneBlockWegner_isHermitian hA ω).eigenvalues k - c| ≤
        ‖(A - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + gueMat n ω)⁻¹‖ := by
  have hA' : (A - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian :=
    hA.sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal]))
  filter_upwards [ae_det_ne_zero_gueMat n hA' (c := 1) one_ne_zero] with ω hω k
  have hM : A - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + gueMat n ω =
      (A + gueMat n ω) - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by abel
  have hdet : (A - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + gueMat n ω).det ≠ 0 := by
    simpa using hω
  exact oneBlockWegner_eig_inv (oneBlockWegner_isHermitian hA ω) hM hdet k

/-- For Hermitian `A`, the probability that `A + V` has an eigenvalue in `[a, a + ℓ]` is at most
`C₀ n ℓ / 2`, given the operator-norm tail bound of constant `C₀`. -/
private lemma oneBlockWegner_piece {C₀ : ℝ}
    (hC₀ : ∀ (n : ℕ), 1 ≤ n → ∀ (A : Matrix (Fin n) (Fin n) ℂ), A.IsHermitian → ∀ t : ℝ, 0 < t →
      μ n 1 {ω | t * n ≤ ‖(A + gueMat n ω)⁻¹‖} ≤ ENNReal.ofReal (C₀ / t))
    {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (a ℓ : ℝ)
    (hℓ : 0 < ℓ) :
    μ n 1 {ω | 1 ≤ countIn (A + gueMat n ω) (Set.Icc a (a + ℓ))} ≤
      ENNReal.ofReal (C₀ * n * (ℓ / 2)) := by
  set c : ℝ := a + ℓ / 2 with hc
  set A' : Matrix (Fin n) (Fin n) ℂ := A - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) with hA'
  have hA'h : A'.IsHermitian :=
    hA.sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal]))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set t : ℝ := 2 / (n * ℓ) with ht
  have ht0 : 0 < t := by positivity
  have htn : t * n = 2 / ℓ := by rw [ht]; field_simp
  refine (measure_mono_ae ?_).trans ((hC₀ n hn A' hA'h t ht0).trans (le_of_eq ?_))
  · filter_upwards [oneBlockWegner_ae_eig_inv hA c] with ω hω hmem
    obtain ⟨k, hk⟩ := (oneBlockWegner_one_le_countIn (oneBlockWegner_isHermitian hA ω) _).mp hmem
    obtain ⟨hne, hineq⟩ := hω k
    have habs : |(oneBlockWegner_isHermitian hA ω).eigenvalues k - c| ≤ ℓ / 2 :=
      abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩
    have hpos : 0 < |(oneBlockWegner_isHermitian hA ω).eigenvalues k - c| :=
      abs_pos.mpr (sub_ne_zero.mpr hne)
    change t * n ≤ ‖(A' + gueMat n ω)⁻¹‖
    refine le_trans ?_ hineq
    rw [htn]
    have : 1 / (ℓ / 2) ≤ 1 / |(oneBlockWegner_isHermitian hA ω).eigenvalues k - c| :=
      one_div_le_one_div_of_le hpos habs
    calc 2 / ℓ = 1 / (ℓ / 2) := by field_simp
      _ ≤ _ := this
  · congr 1
    rw [ht]
    field_simp

/-- Every `q ∈ [0, m + 1]` lies in some `[j, j + 1]`, `j ≤ m`. -/
private lemma oneBlockWegner_cover (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ m + 1) :
    ∃ j ∈ Finset.range (m + 1), (j : ℝ) ≤ q ∧ q ≤ j + 1 := by
  by_cases h : ⌊q⌋₊ ≤ m
  · exact ⟨⌊q⌋₊, Finset.mem_range.mpr (Nat.lt_succ_of_le h), Nat.floor_le hq0,
      (Nat.lt_floor_add_one q).le⟩
  · have h1 : m + 1 ≤ ⌊q⌋₊ := by omega
    have h2 : ((m + 1 : ℕ) : ℝ) ≤ q := (Nat.cast_le.mpr h1).trans (Nat.floor_le hq0)
    push_cast at h2
    exact ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self m), by linarith, hq1⟩

/-- A simple spectrum has a positive gap. -/
private lemma oneBlockWegner_gap {n : ℕ} {ev : Fin n → ℝ} (hinj : Function.Injective ev) :
    ∃ g : ℝ, 0 < g ∧ ∀ k k', k ≠ k' → g ≤ |ev k - ev k'| := by
  set D : Finset ℝ := insert 1
    ((univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2).image fun p => |ev p.1 - ev p.2|) with hD
  have hDne : D.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨D.min' hDne, ?_, fun k k' hkk' => Finset.min'_le _ _ ?_⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rw [hD, Finset.mem_insert, Finset.mem_image] at hy
    rcases hy with rfl | ⟨p, hp, rfl⟩
    · exact one_pos
    · exact abs_pos.mpr (sub_ne_zero.mpr fun h => (Finset.mem_filter.mp hp).2 (hinj h))
  · rw [hD, Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨(k, k'), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkk'⟩, rfl⟩

/-- For a simple spectrum and fine enough partitions of `[α, β]` into `m + 1` closed pieces, the
number of eigenvalues in `[α, β]` is at most the number of pieces containing an eigenvalue. -/
private lemma oneBlockWegner_count_le {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) (hinj : Function.Injective hH.eigenvalues) {α β : ℝ} (hαβ : α < β) :
    ∀ᶠ m : ℕ in Filter.atTop, countIn H (Set.Icc α β) ≤
      ∑ j ∈ Finset.range (m + 1),
        if 1 ≤ countIn H (Set.Icc (α + j * ((β - α) / (m + 1)))
          (α + j * ((β - α) / (m + 1)) + (β - α) / (m + 1))) then 1 else 0 := by
  obtain ⟨g, hg0, hg⟩ := oneBlockWegner_gap hinj
  refine Filter.eventually_atTop.mpr ⟨⌈(β - α) / g⌉₊, fun m hm => ?_⟩
  set ℓ : ℝ := (β - α) / (m + 1) with hℓ
  have hm1 : (0 : ℝ) < m + 1 := by positivity
  have hℓ0 : 0 < ℓ := div_pos (sub_pos.mpr hαβ) hm1
  have hℓm : ℓ * (m + 1) = β - α := by rw [hℓ]; field_simp
  have hℓg : ℓ < g := by
    have h1 : (β - α) / g ≤ m := (Nat.le_ceil _).trans (Nat.cast_le.mpr hm)
    rw [hℓ, div_lt_iff₀ hm1]
    rw [div_le_iff₀ hg0] at h1
    nlinarith
  have hcov : ∀ k, ∃ j : ℕ, hH.eigenvalues k ∈ Set.Icc α β →
      j ∈ Finset.range (m + 1) ∧
        hH.eigenvalues k ∈ Set.Icc (α + j * ℓ) (α + j * ℓ + ℓ) := by
    intro k
    by_cases hk : hH.eigenvalues k ∈ Set.Icc α β
    · obtain ⟨j, hj, hj1, hj2⟩ := oneBlockWegner_cover m
        (q := (hH.eigenvalues k - α) / ℓ) (div_nonneg (sub_nonneg.mpr hk.1) hℓ0.le)
        (by rw [div_le_iff₀ hℓ0]; nlinarith [hk.2])
      refine ⟨j, fun _ => ⟨hj, ?_, ?_⟩⟩
      · rw [le_div_iff₀ hℓ0] at hj1
        linarith
      · rw [div_le_iff₀ hℓ0] at hj2
        linarith
    · exact ⟨0, fun h => absurd h hk⟩
  choose jf hjf using hcov
  have hcard : countIn H (Set.Icc α β) ≤
      #((Finset.range (m + 1)).filter fun j : ℕ => 1 ≤ countIn H
        (Set.Icc (α + (j : ℝ) * ℓ) (α + (j : ℝ) * ℓ + ℓ))) := by
    rw [oneBlockWegner_countIn_eq_card hH]
    refine Finset.card_le_card_of_injOn jf (fun k hk => ?_) (fun k hk k' hk' hkk' => ?_)
    · have hk' : hH.eigenvalues k ∈ Set.Icc α β := by
        simpa only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] using hk
      obtain ⟨h1, h2⟩ := hjf k hk'
      exact Finset.mem_filter.mpr ⟨h1, (oneBlockWegner_one_le_countIn hH _).mpr ⟨k, h2⟩⟩
    · have hk1 : hH.eigenvalues k ∈ Set.Icc α β := by
        simpa only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] using hk
      have hk2 : hH.eigenvalues k' ∈ Set.Icc α β := by
        simpa only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] using hk'
      obtain ⟨_, h1⟩ := hjf k hk1
      obtain ⟨_, h2⟩ := hjf k' hk2
      rw [hkk'] at h1
      by_contra hne
      have := hg k k' hne
      have h3 : |hH.eigenvalues k - hH.eigenvalues k'| ≤ ℓ := by
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      linarith
  rw [← Finset.card_filter]
  exact hcard

/-- [APSSS, Theorem 1 (1.8)], GUE case: `E #{eigenvalues of A + V in [α, β]} ≤ C n (β - α)`
for every Hermitian `A` and `α, β ∈ ℝ`. -/
theorem lintegral_countIn_add_gueMat_le : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.IsHermitian → ∀ α β : ℝ,
      ∫⁻ ω, (countIn (A + gueMat n ω) (Set.Icc α β) : ℝ≥0∞) ∂(μ n 1) ≤
        ENNReal.ofReal (C * n * (β - α)) := by
  obtain ⟨C₀, hC₀, hT⟩ := gueMat_inv_norm_tail
  refine ⟨C₀, hC₀, fun n A hA α β => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ∀ ω : Ω 0 1, countIn (A + gueMat 0 ω) (Set.Icc α β) = 0 := fun ω => by
      simp [countIn]
    simp [h0]
  have hn' : 1 ≤ n := hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rcases lt_trichotomy α β with hlt | rfl | hgt
  · -- `α < β`: partition `[α, β]` into `m + 1` closed pieces and apply Fatou's lemma
    set ℓ : ℕ → ℝ := fun m => (β - α) / (m + 1) with hℓ
    have hℓ0 : ∀ m, 0 < ℓ m := fun m => div_pos (sub_pos.mpr hlt) (by positivity)
    set S : ℕ → ℕ → Set (Ω n 1) := fun m j =>
      {ω | 1 ≤ countIn (A + gueMat n ω) (Set.Icc (α + j * ℓ m) (α + j * ℓ m + ℓ m))} with hS
    have hSm : ∀ m j, MeasurableSet (S m j) := fun m j =>
      (measurable_countIn_add_gueMat n hA measurableSet_Icc) (measurableSet_Ici (a := 1))
    set f : ℕ → Ω n 1 → ℝ≥0∞ := fun m ω =>
      ∑ j ∈ Finset.range (m + 1), (S m j).indicator 1 ω with hf
    have hfm : ∀ m, Measurable (f m) := fun m =>
      Finset.measurable_sum _ fun j _ => measurable_one.indicator (hSm m j)
    have hfint : ∀ m, ∫⁻ ω, f m ω ∂(μ n 1) ≤ ENNReal.ofReal (C₀ * n * (β - α) / 2) := by
      intro m
      rw [hf]
      simp only
      rw [lintegral_finsetSum _ fun j _ => measurable_one.indicator (hSm m j)]
      simp_rw [lintegral_indicator_one (hSm m _)]
      calc ∑ j ∈ Finset.range (m + 1), μ n 1 (S m j)
          ≤ ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal (C₀ * n * (ℓ m / 2)) :=
            Finset.sum_le_sum fun j _ => oneBlockWegner_piece hT hn' hA _ _ (hℓ0 m)
        _ = ENNReal.ofReal (((m : ℝ) + 1) * (C₀ * n * (ℓ m / 2))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ENNReal.ofReal_mul (p := (m : ℝ) + 1) (by positivity)]
            congr 1
            rw [← ENNReal.ofReal_natCast]
            simp
        _ = ENNReal.ofReal (C₀ * n * (β - α) / 2) := by
            congr 1
            rw [hℓ]
            field_simp
    have hae : ∀ᵐ ω ∂(μ n 1), (countIn (A + gueMat n ω) (Set.Icc α β) : ℝ≥0∞) ≤
        Filter.liminf (fun m => f m ω) Filter.atTop := by
      filter_upwards [ae_injective_eigenvalues_add_gueMat n hA] with ω hω
      refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [oneBlockWegner_count_le (oneBlockWegner_isHermitian hA ω) hω hlt]
        with m hm
      have hcast : f m ω = ((∑ j ∈ Finset.range (m + 1),
          if 1 ≤ countIn (A + gueMat n ω) (Set.Icc (α + j * ℓ m) (α + j * ℓ m + ℓ m))
            then 1 else 0 : ℕ) : ℝ≥0∞) := by
        simp only [hf, hS, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
          Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
      rw [hcast]
      exact Nat.cast_le.mpr hm
    calc ∫⁻ ω, (countIn (A + gueMat n ω) (Set.Icc α β) : ℝ≥0∞) ∂(μ n 1)
        ≤ ∫⁻ ω, Filter.liminf (fun m => f m ω) Filter.atTop ∂(μ n 1) := lintegral_mono_ae hae
      _ ≤ Filter.liminf (fun m => ∫⁻ ω, f m ω ∂(μ n 1)) Filter.atTop :=
          lintegral_liminf_le hfm
      _ ≤ ENNReal.ofReal (C₀ * n * (β - α) / 2) :=
          Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hfint)
      _ ≤ ENNReal.ofReal (C₀ * n * (β - α)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have : 0 ≤ C₀ * n * (β - α) := by
            have := sub_pos.mpr hlt
            positivity
          linarith
  · -- `α = β`: almost surely `α` is not an eigenvalue
    have h0 : ∀ᵐ ω ∂(μ n 1), (countIn (A + gueMat n ω) (Set.Icc α α) : ℝ≥0∞) = 0 := by
      filter_upwards [oneBlockWegner_ae_eig_inv hA α] with ω hω
      have : ¬ 1 ≤ countIn (A + gueMat n ω) (Set.Icc α α) := by
        intro h
        obtain ⟨k, hk⟩ := (oneBlockWegner_one_le_countIn (oneBlockWegner_isHermitian hA ω) _).mp h
        exact (hω k).1 (le_antisymm hk.2 hk.1)
      have h1 : countIn (A + gueMat n ω) (Set.Icc α α) = 0 := by omega
      rw [h1, Nat.cast_zero]
    refine le_trans (le_of_eq ((lintegral_congr_ae h0).trans lintegral_zero)) zero_le
  · -- `β < α`: the interval is empty
    have h0 : ∀ ω : Ω n 1, countIn (A + gueMat n ω) (Set.Icc α β) = 0 := fun ω => by
      rw [Set.Icc_eq_empty (not_le.mpr hgt), oneBlockWegner_countIn_eq_card
        (oneBlockWegner_isHermitian hA ω)]
      simp
    simp [h0]

end LSBA
