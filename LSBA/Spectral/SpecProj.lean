import LSBA.Spectral.Counts

/-!
# Spectral projections of Hermitian matrices

The spectral projection `1_S(A)` of a Hermitian matrix onto the eigenvalues in a set `S`, as a
sum of rank-one projections over an eigenbasis (`0` off Hermitian matrices): it is an orthogonal
projection commuting with `A`, of trace `#{k : λ_k ∈ S}`, equal to `1` for `S = ℝ`, complementary
to `1_{Sᶜ}(A)`, equivariant under unitary conjugation and measurable in `A` for closed `S`; and
`‖A 1_S(A)‖ ≤ s` for `S ⊆ [-s, s]`, `‖B 1_{[0,t²]}(B* B)‖ ≤ t`. These are the projections
`P` of (9.4) [su:eq:source-projection] and `1_{(t², ∞)}(A* A)` of Section 9.2
[su:sec:explicit-generator].
-/

open MeasureTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral projection `1_S(A) = Σ_{λ_k ∈ S} u_k u_k*` of a Hermitian `A` (`0` otherwise). -/
def specProj (A : Matrix n n ℂ) (S : Set ℝ) : Matrix n n ℂ :=
  if hA : A.IsHermitian then
    ∑ k ∈ univ.filter (fun k => hA.eigenvalues k ∈ S),
      Matrix.vecMulVec ⇑(hA.eigenvectorBasis k) (star ⇑(hA.eigenvectorBasis k))
  else 0

/-- The diagonal matrix of the indicator `1_S` of `S` along `μ`. -/
private def indDiag (S : Set ℝ) (μ : n → ℝ) : Matrix n n ℂ :=
  Matrix.diagonal fun k => if μ k ∈ S then (1 : ℂ) else 0

/-- The diagonal matrix of a real vector `μ`. -/
private def realDiag (μ : n → ℝ) : Matrix n n ℂ :=
  Matrix.diagonal fun k => (μ k : ℂ)

omit [Fintype n] in
private lemma indDiag_conjTranspose (S : Set ℝ) (μ : n → ℝ) : (indDiag S μ)ᴴ = indDiag S μ := by
  unfold indDiag
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  by_cases h : μ k ∈ S <;> simp [h]

private lemma indDiag_mul_self (S : Set ℝ) (μ : n → ℝ) :
    indDiag S μ * indDiag S μ = indDiag S μ := by
  unfold indDiag
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : μ k ∈ S <;> simp [h]

omit [Fintype n] in
private lemma indDiag_add_compl (S : Set ℝ) (μ : n → ℝ) :
    indDiag S μ + indDiag Sᶜ μ = 1 := by
  unfold indDiag
  rw [Matrix.diagonal_add, ← Matrix.diagonal_one]
  congr 1
  funext k
  by_cases h : μ k ∈ S <;> simp [h]

omit [Fintype n] in
private lemma indDiag_univ (μ : n → ℝ) : indDiag Set.univ μ = 1 := by
  unfold indDiag
  rw [← Matrix.diagonal_one]
  simp

private lemma realDiag_mul_indDiag (S : Set ℝ) (μ : n → ℝ) :
    realDiag μ * indDiag S μ = indDiag S μ * realDiag μ := by
  unfold realDiag indDiag
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  ring

private lemma trace_indDiag (S : Set ℝ) (μ : n → ℝ) :
    (indDiag S μ).trace = ((univ.filter fun k => μ k ∈ S).card : ℂ) := by
  unfold indDiag
  rw [Matrix.trace_diagonal, Finset.sum_boole]

/-- Explicit form of `1_S(A)` in the eigenbasis of `A`. -/
private lemma specProj_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) (S : Set ℝ) :
    specProj A S = (hA.eigenvectorUnitary : Matrix n n ℂ) * indDiag S hA.eigenvalues *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  simp only [specProj, hA, ↓reduceDIte]
  ext i j
  rw [Finset.sum_filter, Matrix.sum_apply]
  simp only [indDiag, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : hA.eigenvalues c ∈ S <;> simp [h, Matrix.vecMulVec_apply, mul_comm]

private lemma unitary_conjTranspose_mul {V : Matrix n n ℂ} (hV : V ∈ Matrix.unitaryGroup n ℂ) :
    Vᴴ * V = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp hV

private lemma unitary_mul_conjTranspose {V : Matrix n n ℂ} (hV : V ∈ Matrix.unitaryGroup n ℂ) :
    V * Vᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp hV

/-- Unitary diagonalization of a Hermitian matrix in the eigenbasis. -/
private lemma eq_eigenvectorUnitary_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) * realDiag hA.eigenvalues *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

/-- `1_S(A)` computed from any unitary diagonalization `A = V diag(μ) V*`. -/
private lemma specProj_eq_of_diag {A V : Matrix n n ℂ} (hA : A.IsHermitian)
    (hV : V ∈ Matrix.unitaryGroup n ℂ) (μ : n → ℝ) (hAV : A = V * realDiag μ * Vᴴ)
    (S : Set ℝ) : specProj A S = V * indDiag S μ * Vᴴ := by
  have hU : (hA.eigenvectorUnitary : Matrix n n ℂ) ∈ Matrix.unitaryGroup n ℂ :=
    hA.eigenvectorUnitary.2
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix n n ℂ, U = (hA.eigenvectorUnitary : Matrix n n ℂ) :=
    ⟨_, rfl⟩
  rw [← hUdef] at hU
  have hspec : A = U * realDiag hA.eigenvalues * Uᴴ := by
    rw [hUdef]; exact eq_eigenvectorUnitary_mul hA
  have hproj : specProj A S = U * indDiag S hA.eigenvalues * Uᴴ := by
    rw [specProj_eq hA S, hUdef]
  have hV1 := unitary_conjTranspose_mul hV
  have hV2 := unitary_mul_conjTranspose hV
  have hU1 := unitary_conjTranspose_mul hU
  have hU2 := unitary_mul_conjTranspose hU
  obtain ⟨W, hW⟩ : ∃ W : Matrix n n ℂ, W = Vᴴ * U := ⟨_, rfl⟩
  have hWW : W * Wᴴ = 1 := by
    rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Vᴴ * U * (Uᴴ * V) = Vᴴ * (U * Uᴴ) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU2, Matrix.mul_one, hV1]
  have hVW : V * W = U := by rw [hW, ← Matrix.mul_assoc, hV2, Matrix.one_mul]
  have hcomm : realDiag μ * W = W * realDiag hA.eigenvalues := by
    have h : V * realDiag μ * Vᴴ = U * realDiag hA.eigenvalues * Uᴴ := hAV.symm.trans hspec
    have e1 : Vᴴ * (V * realDiag μ * Vᴴ) * U = realDiag μ * W := by
      calc _ = (Vᴴ * V) * realDiag μ * (Vᴴ * U) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hV1, Matrix.one_mul, hW]
    have e2 : Vᴴ * (U * realDiag hA.eigenvalues * Uᴴ) * U = W * realDiag hA.eigenvalues := by
      calc _ = Vᴴ * U * realDiag hA.eigenvalues * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU1, Matrix.mul_one, hW]
    rw [← e1, h, e2]
  have hent : ∀ i j, W i j ≠ 0 → μ i = hA.eigenvalues j := by
    intro i j hij
    have := congrFun (congrFun hcomm i) j
    simp only [realDiag, Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    have h2 : (μ i : ℂ) = (hA.eigenvalues j : ℂ) := mul_right_cancel₀ hij (by rw [this, mul_comm])
    exact_mod_cast h2
  have hind : indDiag S μ * W = W * indDiag S hA.eigenvalues := by
    ext i j
    simp only [indDiag, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : W i j = 0
    · simp [hij]
    · rw [hent i j hij]; ring
  rw [hproj]
  calc U * indDiag S hA.eigenvalues * Uᴴ
      = (V * W) * indDiag S hA.eigenvalues * (V * W)ᴴ := by rw [hVW]
    _ = V * (W * indDiag S hA.eigenvalues) * (Wᴴ * Vᴴ) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = V * (indDiag S μ * W) * (Wᴴ * Vᴴ) := by rw [hind]
    _ = V * indDiag S μ * (W * Wᴴ) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = V * indDiag S μ * Vᴴ := by rw [hWW, Matrix.mul_one]

private lemma sandwich_mul {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (X Y : Matrix n n ℂ) :
    U * X * Uᴴ * (U * Y * Uᴴ) = U * (X * Y) * Uᴴ := by
  calc U * X * Uᴴ * (U * Y * Uᴴ) = U * X * (Uᴴ * U) * Y * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = U * (X * Y) * Uᴴ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]

private lemma mul_specProj_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) (S : Set ℝ) :
    A * specProj A S = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (realDiag hA.eigenvalues * indDiag S hA.eigenvalues) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  have hU1 := unitary_conjTranspose_mul hA.eigenvectorUnitary.2
  calc A * specProj A S
      = (hA.eigenvectorUnitary : Matrix n n ℂ) * realDiag hA.eigenvalues *
          (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
        ((hA.eigenvectorUnitary : Matrix n n ℂ) * indDiag S hA.eigenvalues *
          (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ) := by
        rw [← eq_eigenvectorUnitary_mul hA, ← specProj_eq hA S]
    _ = _ := sandwich_mul hU1 _ _

private lemma specProj_mul_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) (S : Set ℝ) :
    specProj A S * A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (indDiag S hA.eigenvalues * realDiag hA.eigenvalues) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  have hU1 := unitary_conjTranspose_mul hA.eigenvectorUnitary.2
  calc specProj A S * A
      = (hA.eigenvectorUnitary : Matrix n n ℂ) * indDiag S hA.eigenvalues *
          (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
        ((hA.eigenvectorUnitary : Matrix n n ℂ) * realDiag hA.eigenvalues *
          (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ) := by
        rw [← eq_eigenvectorUnitary_mul hA, ← specProj_eq hA S]
    _ = _ := sandwich_mul hU1 _ _

private lemma norm_sandwich_le {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (X : Matrix n n ℂ) : ‖U * X * Uᴴ‖ ≤ ‖X‖ := by
  have := Matrix.instCStarRing (n := n) (𝕜 := ℂ)
  have hU' : U ∈ unitary (Matrix n n ℂ) := hU
  have hUs : Uᴴ ∈ unitary (Matrix n n ℂ) := Unitary.star_mem hU'
  rw [Matrix.mul_assoc, CStarRing.norm_mem_unitary_mul _ hU', CStarRing.norm_mul_mem_unitary _ hUs]

private lemma norm_diagonal_le {d : n → ℂ} {r : ℝ} (hr : 0 ≤ r) (hd : ∀ k, ‖d k‖ ≤ r) :
    ‖(Matrix.diagonal d : Matrix n n ℂ)‖ ≤ r := by
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hr).mpr hd

private lemma realDiag_mul_indDiag_eq (S : Set ℝ) (μ : n → ℝ) :
    realDiag μ * indDiag S μ = Matrix.diagonal fun k => if μ k ∈ S then (μ k : ℂ) else 0 := by
  unfold realDiag indDiag
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : μ k ∈ S <;> simp [h]

open scoped ComplexOrder in
private lemma eigenvalues_conjTranspose_mul_self_nonneg (B : Matrix n n ℂ)
    (hC : (Bᴴ * B).IsHermitian) (k : n) : 0 ≤ hC.eigenvalues k :=
  (Matrix.posSemidef_conjTranspose_mul_self B).eigenvalues_nonneg k

private lemma specProj_empty (A : Matrix n n ℂ) : specProj A ∅ = 0 := by
  by_cases hA : A.IsHermitian <;> simp [specProj, hA]

/-- Continuous cutoffs decreasing to `1_S` for a nonempty closed `S`. -/
private def cutoff (S : Set ℝ) (m : ℕ) (x : ℝ) : ℝ := max 0 (1 - (m : ℝ) * Metric.infDist x S)

private lemma continuous_cutoff (S : Set ℝ) (m : ℕ) : Continuous (cutoff S m) :=
  continuous_const.max
    (continuous_const.sub (continuous_const.mul (Metric.continuous_infDist_pt S)))

private lemma tendsto_cutoff {S : Set ℝ} (hS : IsClosed S) (hne : S.Nonempty) (x : ℝ) :
    Filter.Tendsto (fun m => cutoff S m x) Filter.atTop (nhds (if x ∈ S then 1 else 0)) := by
  by_cases hx : x ∈ S
  · simp [cutoff, hx, Metric.infDist_zero_of_mem hx]
  · have hpos := (hS.notMem_iff_infDist_pos hne).mp hx
    simp only [hx, ↓reduceIte]
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / Metric.infDist x S)
    filter_upwards [Filter.eventually_ge_atTop M] with m hm
    have h1 : 1 < (m : ℝ) * Metric.infDist x S := by
      have : (M : ℝ) ≤ m := by exact_mod_cast hm
      rw [div_lt_iff₀ hpos] at hM
      nlinarith
    simp [cutoff, max_eq_left (by linarith : 1 - (m : ℝ) * Metric.infDist x S ≤ 0)]

omit [Fintype n] [DecidableEq n] in
private lemma isClosed_isHermitian : IsClosed {A : Matrix n n ℂ | A.IsHermitian} := by
  have : {A : Matrix n n ℂ | A.IsHermitian} = {A | Aᴴ = A} := rfl
  rw [this]
  exact isClosed_eq (Continuous.matrix_conjTranspose continuous_id) continuous_id

private lemma continuousOn_cfc_cutoff (S : Set ℝ) (m : ℕ) :
    ContinuousOn (fun A : Matrix n n ℂ => cfc (cutoff S m) A) {A | A.IsHermitian} := by
  exact ContinuousOn.cfc_of_mem_nhdsSet (s := Set.univ) (cutoff S m) (a := fun A => A)
    Filter.univ_mem continuousOn_id (fun A hA => hA.isSelfAdjoint)
    (continuous_cutoff S m).continuousOn

private lemma tendsto_cfc_cutoff {S : Set ℝ} (hS : IsClosed S) (hne : S.Nonempty)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Filter.Tendsto (fun m => cfc (cutoff S m) A) Filter.atTop (nhds (specProj A S)) := by
  have hcfc : ∀ m, cfc (cutoff S m) A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun k => ((cutoff S m (hA.eigenvalues k) : ℝ) : ℂ)) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    intro m
    rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rfl
  have hD : Filter.Tendsto (fun m => fun k => ((cutoff S m (hA.eigenvalues k) : ℝ) : ℂ))
      Filter.atTop (nhds fun k => if hA.eigenvalues k ∈ S then (1 : ℂ) else 0) := by
    rw [tendsto_pi_nhds]
    intro k
    have h := (Complex.continuous_ofReal.tendsto _).comp (tendsto_cutoff hS hne (hA.eigenvalues k))
    have hlim : (if hA.eigenvalues k ∈ S then (1 : ℂ) else 0) =
        ((if hA.eigenvalues k ∈ S then (1 : ℝ) else 0 : ℝ) : ℂ) := by
      by_cases hk : hA.eigenvalues k ∈ S <;> simp [hk]
    rw [hlim]
    exact h
  have hcont : Continuous fun D : n → ℂ => (hA.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal D * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ :=
    (continuous_const.matrix_mul (Continuous.matrix_diagonal continuous_id)).matrix_mul
      continuous_const
  rw [specProj_eq hA S]
  simp only [hcfc]
  exact (hcont.tendsto _).comp hD

/-- `1_S(A)` is an orthogonal projection commuting with `A`, of trace `#{k : λ_k ∈ S}`. -/
theorem specProj_spec {A : Matrix n n ℂ} (hA : A.IsHermitian) (S : Set ℝ) :
    (specProj A S).IsHermitian ∧ specProj A S * specProj A S = specProj A S ∧
      A * specProj A S = specProj A S * A ∧ (specProj A S).trace = (countIn A S : ℂ) := by
  have hU1 := unitary_conjTranspose_mul hA.eigenvectorUnitary.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [specProj_eq hA S]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      indDiag_conjTranspose, Matrix.mul_assoc]
  · rw [specProj_eq hA S, sandwich_mul hU1, indDiag_mul_self]
  · rw [mul_specProj_eq hA S, specProj_mul_eq hA S, realDiag_mul_indDiag]
  · rw [specProj_eq hA S, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1,
      Matrix.one_mul, trace_indDiag]
    simp only [countIn, hA, ↓reduceDIte]

/-- `1_S(A) + 1_{Sᶜ}(A) = 1`; in particular `1_ℝ(A) = 1`. -/
theorem specProj_add_compl {A : Matrix n n ℂ} (hA : A.IsHermitian) (S : Set ℝ) :
    specProj A S + specProj A Sᶜ = 1 ∧ specProj A Set.univ = 1 := by
  have hU2 := unitary_mul_conjTranspose hA.eigenvectorUnitary.2
  refine ⟨?_, ?_⟩
  · rw [specProj_eq hA S, specProj_eq hA Sᶜ, ← Matrix.add_mul, ← Matrix.mul_add,
      indDiag_add_compl, Matrix.mul_one, hU2]
  · rw [specProj_eq hA Set.univ, indDiag_univ, Matrix.mul_one, hU2]

/-- Unitary equivariance: `1_S(U A U*) = U 1_S(A) U*`. -/
theorem specProj_conj {A U : Matrix n n ℂ} (hA : A.IsHermitian)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (S : Set ℝ) :
    specProj (U * A * Uᴴ) S = U * specProj A S * Uᴴ := by
  have hA' : (U * A * Uᴴ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hA.eq, Matrix.mul_assoc]
  have hV : U * (hA.eigenvectorUnitary : Matrix n n ℂ) ∈ Matrix.unitaryGroup n ℂ :=
    (Matrix.unitaryGroup n ℂ).mul_mem hU hA.eigenvectorUnitary.2
  have hAV : U * A * Uᴴ = (U * (hA.eigenvectorUnitary : Matrix n n ℂ)) * realDiag hA.eigenvalues *
      (U * (hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ := by
    calc U * A * Uᴴ
        = U * ((hA.eigenvectorUnitary : Matrix n n ℂ) * realDiag hA.eigenvalues *
            (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ) * Uᴴ := by
          rw [← eq_eigenvectorUnitary_mul hA]
      _ = _ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [specProj_eq_of_diag hA' hV hA.eigenvalues hAV S, specProj_eq hA S,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- `‖A 1_S(A)‖ ≤ s` for `S ⊆ [-s, s]`, and `‖B 1_{(-∞, t²]}(B* B)‖ ≤ t` for `t ≥ 0`. -/
theorem norm_mul_specProj_le {A : Matrix n n ℂ} (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s)
    {S : Set ℝ} (hS : S ⊆ Set.Icc (-s) s) (B : Matrix n n ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖A * specProj A S‖ ≤ s ∧ ‖B * specProj (Bᴴ * B) (Set.Iic (t ^ 2))‖ ≤ t := by
  refine ⟨?_, ?_⟩
  · rw [mul_specProj_eq hA S, realDiag_mul_indDiag_eq]
    refine (norm_sandwich_le hA.eigenvectorUnitary.2 _).trans (norm_diagonal_le hs fun k => ?_)
    by_cases h : hA.eigenvalues k ∈ S
    · have := hS h
      simp only [h, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [this.1], this.2⟩
    · simp [h, hs]
  · have hC : (Bᴴ * B).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self B
    obtain ⟨hPH, hPP, hPC, -⟩ := specProj_spec hC (Set.Iic (t ^ 2))
    have hBP : (B * specProj (Bᴴ * B) (Set.Iic (t ^ 2)))ᴴ *
        (B * specProj (Bᴴ * B) (Set.Iic (t ^ 2))) =
        Bᴴ * B * specProj (Bᴴ * B) (Set.Iic (t ^ 2)) := by
      calc _ = specProj (Bᴴ * B) (Set.Iic (t ^ 2)) *
            (Bᴴ * B * specProj (Bᴴ * B) (Set.Iic (t ^ 2))) := by
            rw [Matrix.conjTranspose_mul, hPH.eq]; simp only [Matrix.mul_assoc]
        _ = specProj (Bᴴ * B) (Set.Iic (t ^ 2)) *
            (specProj (Bᴴ * B) (Set.Iic (t ^ 2)) * (Bᴴ * B)) := by rw [hPC]
        _ = specProj (Bᴴ * B) (Set.Iic (t ^ 2)) *
            specProj (Bᴴ * B) (Set.Iic (t ^ 2)) * (Bᴴ * B) := (Matrix.mul_assoc _ _ _).symm
        _ = specProj (Bᴴ * B) (Set.Iic (t ^ 2)) * (Bᴴ * B) := by rw [hPP]
        _ = _ := hPC.symm
    have hCP : ‖Bᴴ * B * specProj (Bᴴ * B) (Set.Iic (t ^ 2))‖ ≤ t ^ 2 := by
      rw [mul_specProj_eq hC, realDiag_mul_indDiag_eq]
      refine (norm_sandwich_le hC.eigenvectorUnitary.2 _).trans
        (norm_diagonal_le (sq_nonneg t) fun k => ?_)
      by_cases h : hC.eigenvalues k ∈ Set.Iic (t ^ 2)
      · have h0 := eigenvalues_conjTranspose_mul_self_nonneg B hC k
        simp only [h, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
        exact h
      · simp only [h, ↓reduceIte, norm_zero]
        exact sq_nonneg t
    have hsq : ‖B * specProj (Bᴴ * B) (Set.Iic (t ^ 2))‖ *
        ‖B * specProj (Bᴴ * B) (Set.Iic (t ^ 2))‖ ≤ t ^ 2 := by
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hBP]
      exact hCP
    by_contra h
    have h' := not_le.mp h
    nlinarith [norm_nonneg (B * specProj (Bᴴ * B) (Set.Iic (t ^ 2)))]

/-- For closed `S`, `A ↦ 1_S(A)` is measurable. -/
theorem measurable_specProj {S : Set ℝ} (hS : IsClosed S) :
    Measurable fun A : Matrix n n ℂ => specProj A S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [specProj_empty]
    exact measurable_const
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have hF : ∀ m, Measurable fun A : Matrix n n ℂ =>
      (if A.IsHermitian then cfc (cutoff S m) A else 0) i j := by
    intro m
    have hpw : (fun A : Matrix n n ℂ => (if A.IsHermitian then cfc (cutoff S m) A else 0) i j) =
        Set.piecewise {A : Matrix n n ℂ | A.IsHermitian} (fun A => cfc (cutoff S m) A i j)
          (fun _ => 0) := by
      ext A
      by_cases h : A.IsHermitian <;> simp [Set.piecewise, h]
    rw [hpw]
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const
      isClosed_isHermitian.measurableSet
    exact ((continuous_apply j).comp (continuous_apply i)).comp_continuousOn
      (continuousOn_cfc_cutoff S m)
  refine measurable_of_tendsto_metrizable hF ?_
  rw [tendsto_pi_nhds]
  intro A
  by_cases hA : A.IsHermitian
  · simp only [hA, ↓reduceIte]
    exact (((continuous_apply j).comp (continuous_apply i)).tendsto _).comp
      (tendsto_cfc_cutoff hS hne hA)
  · simp [hA, specProj]

end LSBA
