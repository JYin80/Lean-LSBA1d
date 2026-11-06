import LSBA.Gauss.RectGaussQuad
import LSBA.Spectral.InvSpectrum

/-!
# Dependent Gaussian projections

Lemma 9.6 [us:lem:self]. Let `R` be a Hermitian matrix on `ℂ^n` (`n ≤ W`) whose spectrum
satisfies (9.43) [us:eq:spectrum] at the scale `η = A d / W`: `C₀ d ≤ #{|r| ≥ η⁻¹} ≤ C₁ W η`,
`Tr |R_<| ≤ C W log W` and `Tr R_<² ≤ C W / η` with `R_< = R 1_{|R| < η⁻¹}`. Let `F` be a
deterministic subspace of dimension at most `d`, and `Y` an `n × k` matrix (`k ≤ d`) with
independent centered complex Gaussian entries of variance `1/W`. Then, with failure `C e^{-c d}`,
`‖Y* x‖ ≤ C √η log W ‖x‖` for every `x ∈ F + ran (R Y)` (9.44) [us:eq:self]. The proof combines
(9.45) [us:eq:lowerK]–(9.47) [us:eq:quadratic] of Appendix G.2.1
[app:gaussian-projection-inputs].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The spectral hypotheses (9.43) [us:eq:spectrum] of Lemma 9.6 [us:lem:self] on a Hermitian
inverse `R` at the scale `η`: `C₀ d ≤ #{|r| ≥ η⁻¹} ≤ C₁ W η`, `Tr |R_<| ≤ C W log W` and
`Tr R_<² ≤ C W / η`, with `R_< = R 1_{|R| < η⁻¹}`; `‖R_<‖ ≤ η⁻¹` holds by definition. -/
def InvSpecInput {n : Type*} [Fintype n] [DecidableEq n] (C₀ C C₁ : ℝ) (W d : ℕ) (η : ℝ)
    (R : Matrix n n ℂ) : Prop :=
  C₀ * d ≤ countIn R {x | η⁻¹ ≤ |x|} ∧ (countIn R {x | η⁻¹ ≤ |x|} : ℝ) ≤ C₁ * W * η ∧
    truncPowSum R η⁻¹ 1 ≤ C * W * Real.log W ∧ truncPowSum R η⁻¹ 2 ≤ C * W / η

/-! ### Euclidean norms and isometries -/

private lemma gaussProj_l2Norm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) : 0 ≤ l2Norm v :=
  Real.sqrt_nonneg _

private lemma gaussProj_l2Norm_sq {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    l2Norm v ^ 2 = ∑ i, ‖v i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private lemma gaussProj_l2Norm_smul {ι : Type*} [Fintype ι] (c : ℂ) (v : ι → ℂ) :
    l2Norm (c • v) = ‖c‖ * l2Norm v := by
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, WithLp.toLp_smul, norm_smul]

private lemma gaussProj_l2Norm_add_le {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    l2Norm (u + v) ≤ l2Norm u + l2Norm v := by
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, WithLp.toLp_add]
  exact norm_add_le _ _

/-- An entry is bounded by the Euclidean norm. -/
private lemma gaussProj_norm_apply_le {ι : Type*} [Fintype ι] (v : ι → ℂ) (i : ι) :
    ‖v i‖ ≤ l2Norm v := by
  rw [l2Norm]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => ‖v j‖ ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

/-- Entrywise domination gives domination of Euclidean norms. -/
private lemma gaussProj_l2Norm_le_of_le {ι : Type*} [Fintype ι] (u v : ι → ℂ) {s : ℝ}
    (hs : 0 ≤ s) (h : ∀ i, s * ‖u i‖ ≤ ‖v i‖) : s * l2Norm u ≤ l2Norm v := by
  rw [l2Norm, l2Norm, ← Real.sqrt_sq hs, ← Real.sqrt_mul (sq_nonneg s)]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have := h i
  have h0 : 0 ≤ s * ‖u i‖ := mul_nonneg hs (norm_nonneg _)
  nlinarith

/-- An upper bound on all vectors is an operator-norm bound. -/
private lemma gaussProj_opNorm_le {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ]
    [DecidableEq ι] (A : Matrix κ ι ℂ) {β : ℝ}
    (hβ : 0 ≤ β) (h : ∀ y : ι → ℂ, l2Norm (A *ᵥ y) ≤ β * l2Norm y) : ‖A‖ ≤ β := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hβ fun v => ?_
  have := h v.ofLp
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp] at this
  exact this

private lemma gaussProj_norm_one_le (m : ℕ) : ‖(1 : Matrix (Fin m) (Fin m) ℂ)‖ ≤ 1 :=
  gaussProj_opNorm_le _ zero_le_one fun y => by simp

/-- `star z ⬝ᵥ z = ‖z‖²`. -/
private lemma gaussProj_star_dot_self {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    star z ⬝ᵥ z = ((l2Norm z ^ 2 : ℝ) : ℂ) := by
  rw [gaussProj_l2Norm_sq]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
  push_cast
  rfl

/-- `‖J c‖ = ‖c‖` for `Jᴴ J = 1`. -/
private lemma gaussProj_l2Norm_isometry {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (J : Matrix ι κ ℂ) (hJ : Jᴴ * J = 1) (c : κ → ℂ) : l2Norm (J *ᵥ c) = l2Norm c := by
  have h : star (J *ᵥ c) ⬝ᵥ (J *ᵥ c) = star c ⬝ᵥ c := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hJ,
      Matrix.one_mulVec]
  rw [gaussProj_star_dot_self, gaussProj_star_dot_self] at h
  have h2 : l2Norm (J *ᵥ c) ^ 2 = l2Norm c ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (gaussProj_l2Norm_nonneg _) (gaussProj_l2Norm_nonneg _)).1 h2

/-- `‖J‖ ≤ 1` and `‖Jᴴ‖ ≤ 1` for `Jᴴ J = 1`. -/
private lemma gaussProj_norm_isometry_le {m n : ℕ} (J : Matrix (Fin n) (Fin m) ℂ)
    (hJ : Jᴴ * J = 1) : ‖J‖ ≤ 1 ∧ ‖Jᴴ‖ ≤ 1 := by
  have h1 : ‖J‖ ≤ 1 := gaussProj_opNorm_le J zero_le_one fun c => by
    rw [gaussProj_l2Norm_isometry J hJ, one_mul]
  exact ⟨h1, by rwa [Matrix.l2_opNorm_conjTranspose]⟩

/-- `‖1 - J Jᴴ‖ ≤ 1` for `Jᴴ J = 1`. -/
private lemma gaussProj_norm_compl_le {m n : ℕ} (J : Matrix (Fin n) (Fin m) ℂ)
    (hJ : Jᴴ * J = 1) : ‖1 - J * Jᴴ‖ ≤ 1 := by
  set P : Matrix (Fin n) (Fin n) ℂ := 1 - J * Jᴴ with hP
  have hPH : Pᴴ = P := by
    rw [hP, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hPP : P * P = P := by
    rw [hP, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ, hJ, Matrix.one_mul]
    abel
  have h := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [hPH, hPP] at h
  by_contra hc
  push Not at hc
  have : ‖P‖ * ‖P‖ > ‖P‖ * 1 := mul_lt_mul_of_pos_left hc (by linarith)
  linarith

/-- `‖Jᴴ‖_HS² = m` for `Jᴴ J = 1` with `m` columns. -/
private lemma gaussProj_hs_isometry {m n : ℕ} (J : Matrix (Fin n) (Fin m) ℂ) (hJ : Jᴴ * J = 1) :
    ∑ i, ∑ j, ‖Jᴴ i j‖ ^ 2 = m := by
  have hi : ∀ i, ∑ j, ‖Jᴴ i j‖ ^ 2 = 1 := by
    intro i
    have h1 := congrFun (congrFun hJ i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      RCLike.star_def, Complex.conj_mul'] at h1
    simp only [Matrix.conjTranspose_apply, RCLike.star_def, Complex.norm_conj]
    exact_mod_cast h1
  rw [Finset.sum_congr rfl fun i _ => hi i]
  simp

/-- `‖Q X‖_HS ≤ ‖X‖_HS` for `‖Q‖ ≤ 1`. -/
private lemma gaussProj_hs_mul_le {n : ℕ} (Q X : Matrix (Fin n) (Fin n) ℂ) (hQ : ‖Q‖ ≤ 1) :
    ∑ i, ∑ j, ‖(Q * X) i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖X i j‖ ^ 2)]
  refine Finset.sum_le_sum fun j _ => ?_
  have hcol : (fun i => (Q * X) i j) = Q *ᵥ (fun i => X i j) := by
    funext i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have h1 := l2Norm_mulVec_le Q (fun i => X i j)
  rw [← hcol] at h1
  have h2 : l2Norm (fun i => (Q * X) i j) ≤ l2Norm (fun i => X i j) :=
    h1.trans (by
      have := gaussProj_l2Norm_nonneg (fun i => X i j)
      nlinarith)
  have h3 := pow_le_pow_left₀ (gaussProj_l2Norm_nonneg _) h2 2
  rwa [gaussProj_l2Norm_sq, gaussProj_l2Norm_sq] at h3

/-- `|Tr X| ≤ m ‖X‖` on `ℂ^m`. -/
private lemma gaussProj_norm_trace_le {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    ‖X.trace‖ ≤ m * ‖X‖ := by
  rw [Matrix.trace]
  refine (norm_sum_le _ _).trans ?_
  have hi : ∀ i, ‖X.diag i‖ ≤ ‖X‖ := by
    intro i
    have h1 : X.diag i = (X *ᵥ Pi.single i 1) i := by
      simp
    have h2 : l2Norm (Pi.single i (1 : ℂ) : Fin m → ℂ) = 1 := by
      rw [l2Norm]
      have : ∑ j, ‖(Pi.single i (1 : ℂ) : Fin m → ℂ) j‖ ^ 2 = 1 := by
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj])
          (fun h => absurd (Finset.mem_univ i) h)]
        simp
      rw [this, Real.sqrt_one]
    rw [h1]
    calc ‖(X *ᵥ Pi.single i 1) i‖ ≤ l2Norm (X *ᵥ Pi.single i 1) := gaussProj_norm_apply_le _ _
      _ ≤ ‖X‖ * l2Norm (Pi.single i (1 : ℂ) : Fin m → ℂ) := l2Norm_mulVec_le _ _
      _ = ‖X‖ := by rw [h2, mul_one]
  calc ∑ i, ‖X.diag i‖ ≤ ∑ _i : Fin m, ‖X‖ := Finset.sum_le_sum fun i _ => hi i
    _ = m * ‖X‖ := by simp

/-- `‖X‖_HS² = Re Tr (Xᴴ X)`. -/
private lemma gaussProj_hs_eq_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, ‖X i j‖ ^ 2 = ((Xᴴ * X).trace).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Complex.conj_mul', Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  norm_cast

/-- An isometry onto a subspace: `J : ℂ^m → ℂ^n` with `Jᴴ J = 1`, `m = dim K`, range in `K`,
and `J Jᴴ v = v` on `K`. -/
private lemma gaussProj_exists_isometry {n : ℕ} (K : Submodule ℂ (Fin n → ℂ)) :
    ∃ (m : ℕ) (J : Matrix (Fin n) (Fin m) ℂ), m = Module.finrank ℂ K ∧ Jᴴ * J = 1 ∧
      (∀ c, J *ᵥ c ∈ K) ∧ ∀ v ∈ K, J *ᵥ (Jᴴ *ᵥ v) = v := by
  set e : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] (Fin n → ℂ) := WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
    with he
  set K' : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := K.comap e.toLinearMap with hK'
  have hdim : Module.finrank ℂ K' = Module.finrank ℂ K := by
    rw [hK', Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  set b := stdOrthonormalBasis ℂ K' with hb
  set J : Matrix (Fin n) (Fin (Module.finrank ℂ K')) ℂ :=
    Matrix.of fun i j => ((b j : EuclideanSpace ℂ (Fin n))).ofLp i with hJ
  have hinner : ∀ (j : Fin (Module.finrank ℂ K')) (w : EuclideanSpace ℂ (Fin n)),
      inner ℂ (b j : EuclideanSpace ℂ (Fin n)) w = (Jᴴ *ᵥ w.ofLp) j := by
    intro j w
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [hJ, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply,
      Pi.star_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hJmul : ∀ c, J *ᵥ c = e ((∑ j, c j • b j : K') : EuclideanSpace ℂ (Fin n)) := by
    intro c
    funext i
    simp only [he, hJ, Matrix.mulVec, dotProduct, Matrix.of_apply, Submodule.coe_sum,
      Submodule.coe_smul, WithLp.linearEquiv_apply]
    change _ = (WithLp.ofLp (∑ x, c x • (b x : EuclideanSpace ℂ (Fin n)))) i
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨Module.finrank ℂ K', J, hdim, ?_, fun c => ?_, fun v hv => ?_⟩
  · ext i j
    have h := (orthonormal_iff_ite.mp b.orthonormal) i j
    rw [Submodule.coe_inner, hinner] at h
    rw [Matrix.one_apply, ← h]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, hJ,
      Matrix.of_apply]
  · rw [hJmul]
    exact (∑ j, c j • b j).2
  · have hv' : e.symm v ∈ K' := by
      rw [hK', Submodule.mem_comap]
      simpa using hv
    have hsum := b.sum_repr' ⟨e.symm v, hv'⟩
    rw [hJmul]
    have hco : (fun j => (Jᴴ *ᵥ v) j) = fun j => inner ℂ (b j) (⟨e.symm v, hv'⟩ : K') := by
      funext j
      rw [Submodule.coe_inner, hinner]
      simp [he]
    simp only [hco, hsum]
    simp

/-! ### Spectral decomposition -/

private lemma gaussProj_unitary {n : ℕ} {R : Matrix (Fin n) (Fin n) ℂ} (hR : R.IsHermitian) :
    (hR.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ * hR.eigenvectorUnitary = 1 ∧
      (hR.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * (hR.eigenvectorUnitary)ᴴ = 1 :=
  ⟨Matrix.mem_unitaryGroup_iff'.mp hR.eigenvectorUnitary.2,
    Matrix.mem_unitaryGroup_iff.mp hR.eigenvectorUnitary.2⟩

/-- `R 1_T(R) = U diag(r 1_T(r)) U*` and `1_T(R) = U diag(1_T(r)) U*`. -/
private lemma gaussProj_mul_specProj {n : ℕ} {R : Matrix (Fin n) (Fin n) ℂ} (hR : R.IsHermitian)
    (T : Set ℝ) :
    R * specProj R T = (hR.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      Matrix.diagonal (fun k => if hR.eigenvalues k ∈ T then (hR.eigenvalues k : ℂ) else 0) *
        (hR.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ ∧
    specProj R T = (hR.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      Matrix.diagonal (fun k => if hR.eigenvalues k ∈ T then (1 : ℂ) else 0) *
        (hR.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hR.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hUdef
  have hU1 : Uᴴ * U = 1 := (gaussProj_unitary hR).1
  have key : specProj R T =
      U * Matrix.diagonal (fun k => if hR.eigenvalues k ∈ T then (1 : ℂ) else 0) * Uᴴ := by
    simp only [specProj, hR, ↓reduceDIte]
    ext i j
    rw [Finset.sum_filter, Matrix.sum_apply]
    simp only [hUdef, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : hR.eigenvalues c ∈ T <;> simp [h, Matrix.vecMulVec_apply, mul_comm]
  have hRU : R = U * Matrix.diagonal (fun k => (hR.eigenvalues k : ℂ)) * Uᴴ := by
    conv_lhs => rw [hR.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  refine ⟨?_, key⟩
  have e0 : R * specProj R T = U * Matrix.diagonal (fun k => (hR.eigenvalues k : ℂ)) * Uᴴ *
      (U * Matrix.diagonal (fun k => if hR.eigenvalues k ∈ T then (1 : ℂ) else 0) * Uᴴ) := by
    rw [key]
    exact congrArg (· * _) hRU
  rw [e0]
  calc U * Matrix.diagonal (fun k => (hR.eigenvalues k : ℂ)) * Uᴴ *
        (U * Matrix.diagonal (fun k => if hR.eigenvalues k ∈ T then (1 : ℂ) else 0) * Uᴴ)
      = U * (Matrix.diagonal (fun k => (hR.eigenvalues k : ℂ)) * (Uᴴ * U) *
        Matrix.diagonal (fun k => if hR.eigenvalues k ∈ T then (1 : ℂ) else 0)) * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hU1, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
        congr 3
        funext k
        split_ifs <;> simp

/-- On the range of `1_{|R| ≥ s}(R)`, `‖R z‖ ≥ s ‖z‖`. -/
private lemma gaussProj_lower_specProj {n : ℕ} {R : Matrix (Fin n) (Fin n) ℂ}
    (hR : R.IsHermitian) {s : ℝ} (hs : 0 ≤ s) (w : Fin n → ℂ) :
    s * l2Norm (specProj R {x | s ≤ |x|} *ᵥ w) ≤
      l2Norm (R *ᵥ (specProj R {x | s ≤ |x|} *ᵥ w)) := by
  obtain ⟨h1, h2⟩ := gaussProj_mul_specProj hR {x | s ≤ |x|}
  have hU1 := (gaussProj_unitary hR).1
  rw [Matrix.mulVec_mulVec, h1, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gaussProj_l2Norm_isometry _ hU1,
    gaussProj_l2Norm_isometry _ hU1]
  refine gaussProj_l2Norm_le_of_le _ _ hs fun k => ?_
  simp only [Matrix.mulVec_diagonal]
  by_cases hk : hR.eigenvalues k ∈ {x : ℝ | s ≤ |x|}
  · simp only [hk, ↓reduceIte, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hk (norm_nonneg _)
  · simp [hk]

/-- `|Tr (R 1_{|R| < s}(R))| ≤ Tr |R_<|`. -/
private lemma gaussProj_trace_low {n : ℕ} {R : Matrix (Fin n) (Fin n) ℂ}
    (hR : R.IsHermitian) (s : ℝ) :
    ‖(R * specProj R {x | s ≤ |x|}ᶜ).trace‖ ≤ truncPowSum R s 1 := by
  obtain ⟨h1, -⟩ := gaussProj_mul_specProj hR {x | s ≤ |x|}ᶜ
  have hU1 := (gaussProj_unitary hR).1
  rw [h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul, Matrix.trace_diagonal]
  simp only [truncPowSum, hR, ↓reduceDIte, pow_one]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : |hR.eigenvalues k| < s
  · have : hR.eigenvalues k ∈ {x : ℝ | s ≤ |x|}ᶜ := by simpa using hk
    simp [this, hk]
  · have : hR.eigenvalues k ∉ {x : ℝ | s ≤ |x|}ᶜ := by simpa using hk
    simp [this, hk]

/-- `‖R 1_{|R| < s}(R)‖_HS² = Tr R_<²`. -/
private lemma gaussProj_hs_low {n : ℕ} {R : Matrix (Fin n) (Fin n) ℂ}
    (hR : R.IsHermitian) (s : ℝ) :
    ∑ i, ∑ j, ‖(R * specProj R {x | s ≤ |x|}ᶜ) i j‖ ^ 2 = truncPowSum R s 2 := by
  obtain ⟨h1, -⟩ := gaussProj_mul_specProj hR {x | s ≤ |x|}ᶜ
  obtain ⟨hU1, hU2⟩ := gaussProj_unitary hR
  set U : Matrix (Fin n) (Fin n) ℂ := (hR.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  have e1 : ∀ D : Matrix (Fin n) (Fin n) ℂ,
      (U * D * Uᴴ)ᴴ * (U * D * Uᴴ) = U * (Dᴴ * D) * Uᴴ := by
    intro D
    calc (U * D * Uᴴ)ᴴ * (U * D * Uᴴ) = U * Dᴴ * (Uᴴ * U) * D * Uᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
      _ = _ := by rw [hU1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [gaussProj_hs_eq_trace, h1, e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1,
    Matrix.one_mul, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  simp only [truncPowSum, hR, ↓reduceDIte, Complex.re_sum]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : |hR.eigenvalues k| < s
  · have : hR.eigenvalues k ∈ {x : ℝ | s ≤ |x|}ᶜ := by simpa using hk
    simp only [this, hk, ↓reduceIte, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
    rw [sq_abs, ← Complex.ofReal_mul, Complex.ofReal_re, sq]
  · have : hR.eigenvalues k ∉ {x : ℝ | s ≤ |x|}ᶜ := by simpa using hk
    simp [this, hk]

/-! ### Arithmetic of the constants -/

/-- The closing arithmetic of (9.44) [us:eq:self]: with `η = A d / W`, `s = η⁻¹`,
`L = log W ≥ 1` and `t = W^{-1/2}`, the bounds (9.45) [us:eq:lowerK], (9.46) [us:eq:Gaussnorm]
and (9.47) [us:eq:quadratic] in the form `X₁ ≤ Cn (√v + √(k + d))`,
`X₂ ≤ |Tr M| + Cq (√(k + d) ‖M‖_HS + (k + d) ‖M‖)` and `cr s √h ‖b‖ ≤ √W ‖y‖` give
`t X₁ ‖y‖ + t² X₂ ‖b‖ ≤ C' √η L ‖y‖`. -/
private lemma gaussProj_arith {A C C₁ Cn Cq cr C₀r Wr Dr kr vr hr X1 X2 TrM HS NM yN bN : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hC₁ : 0 < C₁) (hCn : 0 < Cn) (hCq : 0 < Cq) (hcr : 0 < cr)
    (hC₀r : 0 < C₀r) (hW : 0 < Wr) (hD : 0 < Dr) (hL : 1 ≤ Real.log Wr)
    (hk0 : 0 ≤ kr) (hk : kr ≤ Dr) (hv : vr ≤ Dr + C₁ * A * Dr) (hh : C₀r * Dr ≤ hr)
    (hX1 : X1 ≤ Cn * (Real.sqrt vr + Real.sqrt (kr + Dr)))
    (hX2 : X2 ≤ TrM + Cq * (Real.sqrt (kr + Dr) * HS + (kr + Dr) * NM))
    (hTr : TrM ≤ C * Wr * Real.log Wr + vr * (A * Dr / Wr)⁻¹)
    (hHS0 : 0 ≤ HS) (hHS : HS ≤ Real.sqrt (C * Wr / (A * Dr / Wr)))
    (hNM : NM ≤ (A * Dr / Wr)⁻¹)
    (hy0 : 0 ≤ yN) (hb0 : 0 ≤ bN)
    (hb : cr * (A * Dr / Wr)⁻¹ * Real.sqrt hr * bN ≤ Real.sqrt Wr * yN) :
    (Real.sqrt Wr)⁻¹ * X1 * yN + (Real.sqrt Wr)⁻¹ ^ 2 * X2 * bN ≤
      ((Cn * (Real.sqrt (1 + C₁ * A) + Real.sqrt 2) +
          (C + (1 + C₁ * A) / A + Cq * (Real.sqrt (2 * C / A) + 2 / A)) * A /
            (cr * Real.sqrt C₀r)) / Real.sqrt A + 3) *
        Real.sqrt (A * Dr / Wr) * Real.log Wr * yN := by
  obtain ⟨w, hw, rfl⟩ : ∃ w : ℝ, 0 < w ∧ w ^ 2 = Wr :=
    ⟨Real.sqrt Wr, Real.sqrt_pos.2 hW, Real.sq_sqrt hW.le⟩
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℝ, 0 < a ∧ a ^ 2 = Dr :=
    ⟨Real.sqrt Dr, Real.sqrt_pos.2 hD, Real.sq_sqrt hD.le⟩
  set L := Real.log (w ^ 2) with hLdef
  set Q₃ := C + (1 + C₁ * A) / A + Cq * (Real.sqrt (2 * C / A) + 2 / A) with hQ₃
  set ψ := Real.sqrt (1 + C₁ * A) with hψ
  set β := Real.sqrt C₀r with hβ
  set α := Real.sqrt A with hα
  set r2 := Real.sqrt 2 with hr2
  set ρ := Real.sqrt (2 * C / A) with hρ
  have hα0 : 0 < α := Real.sqrt_pos.2 hA
  have hβ0 : 0 < β := Real.sqrt_pos.2 hC₀r
  have hψ0 : 0 ≤ ψ := Real.sqrt_nonneg _
  have hr20 : 0 ≤ r2 := Real.sqrt_nonneg _
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hα2 : α ^ 2 = A := Real.sq_sqrt hA.le
  have hsw : Real.sqrt (w ^ 2) = w := Real.sqrt_sq hw.le
  have hsa : ∀ c : ℝ, 0 ≤ c → Real.sqrt (c * a ^ 2) = Real.sqrt c * a := fun c hc => by
    rw [Real.sqrt_mul hc, Real.sqrt_sq ha.le]
  have hs : (A * a ^ 2 / w ^ 2)⁻¹ = w ^ 2 / (A * a ^ 2) := by rw [inv_div]
  rw [hsw] at hb ⊢
  rw [hs] at hb hTr hNM
  have hη : Real.sqrt (A * a ^ 2 / w ^ 2) = α * a / w := by
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul hA.le, Real.sqrt_sq ha.le,
      Real.sqrt_sq hw.le]
  rw [hη]
  -- (9.46) [us:eq:Gaussnorm]: `t X₁ ≤ Cn (ψ + √2) a / w`
  have hv' : Real.sqrt vr ≤ ψ * a := by
    rw [← hsa _ (by positivity)]
    exact Real.sqrt_le_sqrt (le_of_le_of_eq hv (by ring))
  have hk' : Real.sqrt (kr + a ^ 2) ≤ r2 * a := by
    rw [← hsa _ (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hT1 : w⁻¹ * X1 ≤ Cn * (ψ + r2) * a / w := by
    rw [inv_mul_le_iff₀ hw, mul_div_cancel₀ _ hw.ne']
    calc X1 ≤ _ := hX1
      _ ≤ Cn * (ψ * a + r2 * a) := mul_le_mul_of_nonneg_left (add_le_add hv' hk') hCn.le
      _ = _ := by ring
  -- (9.45) [us:eq:lowerK]: `cr β w ‖b‖ ≤ A a ‖y‖`
  have hh' : β * a ≤ Real.sqrt hr := by
    rw [← hsa _ hC₀r.le]
    exact Real.sqrt_le_sqrt hh
  have hB : cr * β * w * bN ≤ A * a * yN := by
    have h1 : cr * (w ^ 2 / (A * a ^ 2)) * (β * a) * bN ≤ w * yN := by
      refine le_trans ?_ hb
      have : 0 ≤ cr * (w ^ 2 / (A * a ^ 2)) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh' this) hb0
    have e : cr * (w ^ 2 / (A * a ^ 2)) * (β * a) * bN =
        (cr * β * w * bN) * (w / (A * a)) := by
      field_simp
    rw [e] at h1
    have h2 : 0 < w / (A * a) := by positivity
    have h3 : (cr * β * w * bN) * (w / (A * a)) ≤ (A * a * yN) * (w / (A * a)) := by
      calc _ ≤ w * yN := h1
        _ = (A * a * yN) * (w / (A * a)) := by field_simp
    exact le_of_mul_le_mul_right h3 h2
  -- (9.47) [us:eq:quadratic]: `X₂ ≤ w² Q₃ L`
  have hP : Real.sqrt (kr + a ^ 2) * HS ≤ ρ * w ^ 2 := by
    have hP0 : 0 ≤ Real.sqrt (kr + a ^ 2) * HS := mul_nonneg (Real.sqrt_nonneg _) hHS0
    have hHS2 : HS ^ 2 ≤ C * w ^ 2 / (A * a ^ 2 / w ^ 2) := by
      have := pow_le_pow_left₀ hHS0 hHS 2
      rwa [Real.sq_sqrt (by positivity)] at this
    have hk2 : Real.sqrt (kr + a ^ 2) ^ 2 ≤ 2 * a ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
      linarith
    have e : ρ * w ^ 2 = Real.sqrt (2 * C / A * (w ^ 2) ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [e, Real.le_sqrt hP0 (by positivity), mul_pow]
    have e2 : C * w ^ 2 / (A * a ^ 2 / w ^ 2) = C * (w ^ 2) ^ 2 / (A * a ^ 2) := by
      field_simp
    rw [e2] at hHS2
    calc Real.sqrt (kr + a ^ 2) ^ 2 * HS ^ 2 ≤ (2 * a ^ 2) * (C * (w ^ 2) ^ 2 / (A * a ^ 2)) :=
          mul_le_mul hk2 hHS2 (sq_nonneg _) (by positivity)
      _ = 2 * C / A * (w ^ 2) ^ 2 := by field_simp
  have hvs : vr * (w ^ 2 / (A * a ^ 2)) ≤ (1 + C₁ * A) / A * w ^ 2 := by
    have : vr * (w ^ 2 / (A * a ^ 2)) ≤ (a ^ 2 + C₁ * A * a ^ 2) * (w ^ 2 / (A * a ^ 2)) :=
      mul_le_mul_of_nonneg_right hv (by positivity)
    refine this.trans (le_of_eq ?_)
    field_simp
  have hkN : (kr + a ^ 2) * NM ≤ 2 / A * w ^ 2 := by
    have hNM0' : NM ≤ w ^ 2 / (A * a ^ 2) := hNM
    by_cases hN : NM ≤ 0
    · have : (kr + a ^ 2) * NM ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hN
      have : 0 ≤ 2 / A * w ^ 2 := by positivity
      linarith
    · push Not at hN
      calc (kr + a ^ 2) * NM ≤ (2 * a ^ 2) * (w ^ 2 / (A * a ^ 2)) :=
            mul_le_mul (by linarith) hNM0' hN.le (by positivity)
        _ = 2 / A * w ^ 2 := by field_simp
  have hX2' : X2 ≤ w ^ 2 * (Q₃ * L) := by
    have h1 : X2 ≤ C * w ^ 2 * L + (1 + C₁ * A) / A * w ^ 2 +
        Cq * (ρ * w ^ 2 + 2 / A * w ^ 2) := by
      have h2 := mul_le_mul_of_nonneg_left (add_le_add hP hkN) hCq.le
      linarith
    have hQL : C * L + (1 + C₁ * A) / A + Cq * (ρ + 2 / A) ≤ Q₃ * L := by
      have h0 : 0 ≤ (1 + C₁ * A) / A + Cq * (ρ + 2 / A) := by positivity
      have h1 : (1 + C₁ * A) / A + Cq * (ρ + 2 / A) ≤
          ((1 + C₁ * A) / A + Cq * (ρ + 2 / A)) * L := le_mul_of_one_le_right h0 hL
      calc C * L + (1 + C₁ * A) / A + Cq * (ρ + 2 / A)
          ≤ C * L + ((1 + C₁ * A) / A + Cq * (ρ + 2 / A)) * L := by linarith
        _ = Q₃ * L := by rw [hQ₃]; ring
    have hw2 : 0 ≤ w ^ 2 := by positivity
    calc X2 ≤ w ^ 2 * (C * L + (1 + C₁ * A) / A + Cq * (ρ + 2 / A)) := by linarith
      _ ≤ w ^ 2 * (Q₃ * L) := mul_le_mul_of_nonneg_left hQL hw2
  have hQ0 : 0 ≤ Q₃ := by positivity
  have hT2 : w⁻¹ ^ 2 * X2 * bN ≤ Q₃ * L * (A * a * yN / (cr * β * w)) := by
    have h1 : w⁻¹ ^ 2 * X2 ≤ Q₃ * L := by
      rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
      exact hX2'
    have h2 : bN ≤ A * a * yN / (cr * β * w) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hX2n : 0 ≤ Q₃ * L := by positivity
    calc w⁻¹ ^ 2 * X2 * bN ≤ Q₃ * L * bN := mul_le_mul_of_nonneg_right h1 hb0
      _ ≤ Q₃ * L * (A * a * yN / (cr * β * w)) := mul_le_mul_of_nonneg_left h2 hX2n
  -- assembly
  set K := Cn * (ψ + r2) + Q₃ * A / (cr * β) with hK
  have hK0 : 0 ≤ K := by positivity
  have hL0 : 0 ≤ L := by linarith
  have hT1' : w⁻¹ * X1 * yN ≤ Cn * (ψ + r2) * a / w * L * yN := by
    have h1 := mul_le_mul_of_nonneg_right hT1 hy0
    have h2 : Cn * (ψ + r2) * a / w * yN ≤ Cn * (ψ + r2) * a / w * L * yN := by
      have : 0 ≤ Cn * (ψ + r2) * a / w * yN := by positivity
      calc Cn * (ψ + r2) * a / w * yN ≤ Cn * (ψ + r2) * a / w * yN * L :=
            le_mul_of_one_le_right this hL
        _ = _ := by ring
    linarith
  have e1 : Q₃ * L * (A * a * yN / (cr * β * w)) = Q₃ * A / (cr * β) * a / w * L * yN := by
    field_simp
  have e2 : (K / α + 3) * (α * a / w) * L * yN =
      K * a / w * L * yN + 3 * (α * a / w) * L * yN := by
    field_simp
  rw [e2]
  have h3 : 0 ≤ 3 * (α * a / w) * L * yN := by positivity
  have h4 : K * a / w * L * yN =
      Cn * (ψ + r2) * a / w * L * yN + Q₃ * A / (cr * β) * a / w * L * yN := by
    rw [hK]
    ring
  linarith [hT1', hT2, e1, h4]

/-! ### The splitting of `Y* y` -/

/-- If `y - J J* y = t M G b` with `J* J = 1`, then
`‖(t G)* y‖ ≤ t ‖J* G‖ ‖y‖ + t² ‖G* M G‖ ‖b‖`. -/
private lemma gaussProj_split {n k v : ℕ} (G : Matrix (Fin n) (Fin k) ℂ)
    (J : Matrix (Fin n) (Fin v) ℂ) (M : Matrix (Fin n) (Fin n) ℂ) {t : ℝ} (ht : 0 ≤ t)
    (hJ : Jᴴ * J = 1) (y : Fin n → ℂ) (b : Fin k → ℂ)
    (hy : y - J *ᵥ (Jᴴ *ᵥ y) = (t : ℂ) • (M *ᵥ (G *ᵥ b))) :
    l2Norm (((t : ℂ) • G)ᴴ *ᵥ y) ≤ t * ‖Jᴴ * G‖ * l2Norm y + t ^ 2 * ‖Gᴴ * M * G‖ * l2Norm b := by
  have hy' : y = J *ᵥ (Jᴴ *ᵥ y) + (t : ℂ) • (M *ᵥ (G *ᵥ b)) := by
    rw [← hy]
    abel
  have hst : ((t : ℂ) • G)ᴴ = (t : ℂ) • Gᴴ := by
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  have e : ((t : ℂ) • G)ᴴ *ᵥ y =
      (t : ℂ) • ((Gᴴ * J) *ᵥ (Jᴴ *ᵥ y)) + ((t ^ 2 : ℝ) : ℂ) • ((Gᴴ * M * G) *ᵥ b) := by
    conv_lhs => rw [hy']
    rw [hst, Matrix.mulVec_add, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul,
      smul_smul]
    congr 1
    · rw [← Matrix.mulVec_mulVec]
    · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      push_cast
      ring_nf
  have htn : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have ht2 : ‖((t ^ 2 : ℝ) : ℂ)‖ = t ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [e]
  refine (gaussProj_l2Norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [gaussProj_l2Norm_smul, htn, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ ht
    calc l2Norm ((Gᴴ * J) *ᵥ (Jᴴ *ᵥ y)) ≤ ‖Gᴴ * J‖ * l2Norm (Jᴴ *ᵥ y) := l2Norm_mulVec_le _ _
      _ ≤ ‖Gᴴ * J‖ * (‖Jᴴ‖ * l2Norm y) :=
          mul_le_mul_of_nonneg_left (l2Norm_mulVec_le _ _) (norm_nonneg _)
      _ ≤ ‖Gᴴ * J‖ * (1 * l2Norm y) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right (gaussProj_norm_isometry_le J hJ).2
            (gaussProj_l2Norm_nonneg _)
      _ = ‖Jᴴ * G‖ * l2Norm y := by
          rw [one_mul, ← Matrix.l2_opNorm_conjTranspose, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]
  · rw [gaussProj_l2Norm_smul, ht2, mul_assoc]
    exact mul_le_mul_of_nonneg_left (l2Norm_mulVec_le _ _) (by positivity)

/-! ### Proof of (9.44) [us:eq:self] -/

/-- Lemma 9.6 [us:lem:self], (9.44) [us:eq:self]: there is an absolute `C₀` such that for all
`A, C, C₁ > 0`, under (9.43) [us:eq:spectrum] at `η = A d / W`, for a deterministic subspace
`F` of dimension at most `d` and `Y = W^{-1/2} G` (`G` an `n × k` standard complex Gaussian
matrix, `k ≤ d`), `‖Y* x‖ ≤ C' √η log W ‖x‖` for all `x ∈ F + ran (R Y)`, with failure
`C' e^{-c d}`. -/
theorem gaussProj_overlap_le : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ A C C₁ : ℝ, 0 < A → 0 < C → 0 < C₁ →
    ∃ C' c : ℝ, 0 < C' ∧ 0 < c ∧ ∀ (W n k d : ℕ), 3 ≤ W → n ≤ W → k ≤ d →
      ∀ R : Matrix (Fin n) (Fin n) ℂ, R.IsHermitian →
      InvSpecInput C₀ C C₁ W d (A * d / W) R →
      ∀ F : Submodule ℂ (Fin n → ℂ), Module.finrank ℂ F ≤ d →
      stdCGauss (Fin n × Fin k)
          {x | ∃ y ∈ F ⊔ LinearMap.range (R * ((((Real.sqrt W)⁻¹ : ℝ) : ℂ) • cgMat x)).mulVecLin,
            C' * Real.sqrt (A * d / W) * Real.log W * l2Norm y <
              l2Norm (((((Real.sqrt W)⁻¹ : ℝ) : ℂ) • cgMat x)ᴴ *ᵥ y)} ≤
        ENNReal.ofReal (C' * Real.exp (-(c * d))) := by
  obtain ⟨C₀r, cr, hC₀r, hcr, hsm⟩ := cgMat_sminor
  obtain ⟨Cn, hCn, hnorm⟩ := cgMat_mul_norm_le
  obtain ⟨Cq, hCq, hquad⟩ := cgMat_quadForm_le
  refine ⟨C₀r + 1, by linarith, fun A C C₁ hA hC hC₁ => ?_⟩
  set K : ℝ := Cn * (Real.sqrt (1 + C₁ * A) + Real.sqrt 2) +
    (C + (1 + C₁ * A) / A + Cq * (Real.sqrt (2 * C / A) + 2 / A)) * A /
      (cr * Real.sqrt C₀r) with hK
  have hK0 : 0 ≤ K := by positivity
  have hc0 : 0 < min 1 (cr * C₀r) := lt_min one_pos (mul_pos hcr hC₀r)
  refine ⟨K / Real.sqrt A + 3, min 1 (cr * C₀r), by positivity, hc0, ?_⟩
  intro W n k d hW hn hkd R hR hspec F hF
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hLW : 1 ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le hW0]
    have h3 : (3 : ℝ) ≤ W := by exact_mod_cast hW
    linarith [Real.exp_one_lt_d9]
  have hC'0 : 0 < K / Real.sqrt A + 3 := by positivity
  set t : ℝ := (Real.sqrt W)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 (Real.sqrt_pos.2 hW0)
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- no columns: `Y* y ∈ ℂ⁰`
    subst hk0
    refine le_trans (measure_mono (t := ∅) fun x hx => ?_) (by simp)
    obtain ⟨y, -, hlt⟩ := hx
    have h0 : l2Norm (((t : ℂ) • cgMat x)ᴴ *ᵥ y) = 0 := by simp [l2Norm]
    rw [h0] at hlt
    have : 0 ≤ (K / Real.sqrt A + 3) * Real.sqrt (A * d / W) * Real.log W * l2Norm y :=
      mul_nonneg (mul_nonneg (mul_nonneg hC'0.le (Real.sqrt_nonneg _)) (by linarith))
        (gaussProj_l2Norm_nonneg y)
    exact absurd hlt (not_lt.2 this)
  have hd1 : 1 ≤ d := le_trans hkpos hkd
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hkd' : (k : ℝ) ≤ d := by exact_mod_cast hkd
  set η : ℝ := A * d / W with hη
  have hη0 : 0 < η := by positivity
  set s : ℝ := η⁻¹ with hs
  have hs0 : 0 < s := inv_pos.2 hη0
  obtain ⟨hc1, hc2, ht1, ht2⟩ := hspec
  set S : Set ℝ := {x | s ≤ |x|} with hS
  set P1 : Matrix (Fin n) (Fin n) ℂ := specProj R S with hP1
  set P2 : Matrix (Fin n) (Fin n) ℂ := specProj R Sᶜ with hP2
  obtain ⟨-, -, hRP1, -⟩ := specProj_spec hR S
  have hP12 : P1 + P2 = 1 := (specProj_add_compl hR S).1
  set E : Submodule ℂ (Fin n → ℂ) := LinearMap.range P1.mulVecLin with hE
  have hEdim : Module.finrank ℂ E = countIn R S := rank_specProj hR S
  obtain ⟨f, JF, hfdim, hJF1, -, hJF3⟩ := gaussProj_exists_isometry F
  obtain ⟨v, JV, hvdim, hJV1, -, hJV3⟩ := gaussProj_exists_isometry (F ⊔ E)
  set Fp : Submodule ℂ (Fin n → ℂ) := LinearMap.ker JFᴴ.mulVecLin with hFp
  obtain ⟨h, JH, hhdim, hJH1, hJH2, -⟩ := gaussProj_exists_isometry (E ⊓ Fp)
  have hfd : (f : ℝ) ≤ d := by rw [hfdim]; exact_mod_cast hF
  -- dimensions
  have hv : (v : ℝ) ≤ d + C₁ * A * d := by
    have h1 : v ≤ f + countIn R S := by
      rw [hvdim, hfdim, ← hEdim]
      exact Submodule.finrank_add_le_finrank_add_finrank F E
    have h2 : (countIn R S : ℝ) ≤ C₁ * A * d := by
      calc _ ≤ C₁ * W * η := hc2
        _ = C₁ * A * d := by rw [hη]; field_simp
    have h1' : (v : ℝ) ≤ f + countIn R S := by exact_mod_cast h1
    linarith
  have hFpdim : Module.finrank ℂ Fp + f = n := by
    have hsurj : LinearMap.range JFᴴ.mulVecLin = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      exact ⟨JF *ᵥ c, by
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hJF1, Matrix.one_mulVec]⟩
    have := LinearMap.finrank_range_add_finrank_ker JFᴴ.mulVecLin
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun, ← hFp] at this
    omega
  have hh : C₀r * d ≤ h := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq E Fp
    have h2 : Module.finrank ℂ (E ⊔ Fp : Submodule ℂ (Fin n → ℂ)) ≤ n := by
      have := Submodule.finrank_le (E ⊔ Fp)
      rwa [Module.finrank_fin_fun] at this
    have h3 : countIn R S ≤ h + f := by
      rw [hhdim, ← hEdim]
      omega
    have h4 : (countIn R S : ℝ) ≤ h + f := by exact_mod_cast h3
    have h5 : (C₀r + 1) * d ≤ (countIn R S : ℝ) := hc1
    rw [add_mul, one_mul] at h5
    linarith
  have hkh : C₀r * k ≤ h := le_trans (mul_le_mul_of_nonneg_left hkd' hC₀r.le) hh
  -- orthogonality of `ran J_H` and `F`
  have hFH : JFᴴ * JH = 0 := by
    ext i j
    have h1 : JH *ᵥ Pi.single j 1 ∈ Fp := (Submodule.mem_inf.1 (hJH2 _)).2
    rw [hFp, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_single_one] at h1
    simpa using congrFun h1 i
  have hHF : ∀ g ∈ F, JHᴴ *ᵥ g = 0 := by
    intro g hg
    have hHF' : JHᴴ * JF = 0 := by
      have := congrArg Matrix.conjTranspose hFH
      simpa [Matrix.conjTranspose_mul] using this
    rw [← hJF3 g hg, Matrix.mulVec_mulVec, hHF', Matrix.zero_mulVec]
  -- (9.45) [us:eq:lowerK]: the co-isometry `N = J_H* R`, `H = E_> ∩ F^⊥`
  set N : Matrix (Fin h) (Fin n) ℂ := JHᴴ * R with hN
  have hNlow : ∀ u, s * l2Norm u ≤ l2Norm (Nᴴ *ᵥ u) := by
    intro u
    have hmem : JH *ᵥ u ∈ E := (Submodule.mem_inf.1 (hJH2 u)).1
    obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hmem
    rw [Matrix.mulVecLin_apply] at hw
    have h1 := gaussProj_lower_specProj hR hs0.le w
    rw [hw] at h1
    rw [hN, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hR.eq,
      ← Matrix.mulVec_mulVec, ← gaussProj_l2Norm_isometry JH hJH1 u]
    exact h1
  -- (9.47) [us:eq:quadratic]: the matrix `M = (1 - P_V) R_<`, `V = F + E_>`
  set M : Matrix (Fin n) (Fin n) ℂ := (1 - JV * JVᴴ) * (R * P2) with hM
  have hRP2 : ‖R * P2‖ ≤ s := by
    refine (norm_mul_specProj_le hR hs0.le (S := Sᶜ) (fun x hx => ?_) 0 le_rfl).1
    have hx' : |x| < s := by simpa [hS] using hx
    exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hMnorm : ‖M‖ ≤ s := by
    calc ‖M‖ ≤ ‖1 - JV * JVᴴ‖ * ‖R * P2‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * s := mul_le_mul (gaussProj_norm_compl_le JV hJV1) hRP2 (norm_nonneg _) zero_le_one
      _ = s := one_mul s
  have hMhs : ∑ i, ∑ j, ‖M i j‖ ^ 2 ≤ truncPowSum R s 2 := by
    rw [← gaussProj_hs_low hR s]
    exact gaussProj_hs_mul_le _ _ (gaussProj_norm_compl_le JV hJV1)
  have hMtr : ‖M.trace‖ ≤ truncPowSum R s 1 + v * s := by
    have e : M.trace = (R * P2).trace - (JVᴴ * (R * P2) * JV).trace := by
      rw [hM, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.mul_assoc,
        Matrix.trace_mul_comm JV]
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add (gaussProj_trace_low hR s) ?_)
    refine (gaussProj_norm_trace_le _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg v)
    obtain ⟨hJn, hJhn⟩ := gaussProj_norm_isometry_le JV hJV1
    calc ‖JVᴴ * (R * P2) * JV‖ ≤ ‖JVᴴ * (R * P2)‖ * ‖JV‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖JVᴴ‖ * ‖R * P2‖) * 1 :=
          mul_le_mul (Matrix.l2_opNorm_mul _ _) hJn (norm_nonneg _) (by positivity)
      _ ≤ (1 * s) * 1 := by
          gcongr
      _ = s := by ring
  -- the decomposition `(1 - P_V) (g + R z) = M z`
  have hVkill : ∀ u ∈ F ⊔ E, u - JV *ᵥ (JVᴴ *ᵥ u) = 0 := fun u hu => by
    rw [hJV3 u hu, sub_self]
  have hdec : ∀ g ∈ F, ∀ z : Fin n → ℂ,
      (g + R *ᵥ z) - JV *ᵥ (JVᴴ *ᵥ (g + R *ᵥ z)) = M *ᵥ z := by
    intro g hg z
    have hg' : g - JV *ᵥ (JVᴴ *ᵥ g) = 0 := hVkill g (Submodule.mem_sup_left hg)
    have hz1 : R *ᵥ (P1 *ᵥ z) ∈ F ⊔ E := by
      refine Submodule.mem_sup_right ?_
      refine ⟨R *ᵥ z, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hRP1]
    have hz1' := hVkill _ hz1
    have hRz : R *ᵥ z = R *ᵥ (P1 *ᵥ z) + R *ᵥ (P2 *ᵥ z) := by
      rw [← Matrix.mulVec_add, ← Matrix.add_mulVec, hP12, Matrix.one_mulVec]
    have hMz : M *ᵥ z = R *ᵥ (P2 *ᵥ z) - JV *ᵥ (JVᴴ *ᵥ (R *ᵥ (P2 *ᵥ z))) := by
      rw [hM, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hMz, hRz]
    simp only [Matrix.mulVec_add]
    calc g + (R *ᵥ (P1 *ᵥ z) + R *ᵥ (P2 *ᵥ z)) -
          (JV *ᵥ (JVᴴ *ᵥ g) + (JV *ᵥ (JVᴴ *ᵥ (R *ᵥ (P1 *ᵥ z))) +
            JV *ᵥ (JVᴴ *ᵥ (R *ᵥ (P2 *ᵥ z)))))
        = (g - JV *ᵥ (JVᴴ *ᵥ g)) + (R *ᵥ (P1 *ᵥ z) - JV *ᵥ (JVᴴ *ᵥ (R *ᵥ (P1 *ᵥ z)))) +
          (R *ᵥ (P2 *ᵥ z) - JV *ᵥ (JVᴴ *ᵥ (R *ᵥ (P2 *ᵥ z)))) := by abel
      _ = _ := by rw [hg', hz1', zero_add, zero_add]
  -- the three failure events
  have hB1 := hsm h n k N s hs0.le hNlow hkh
  have hB2 := hnorm v n k JVᴴ d (Nat.cast_nonneg d)
  have hB3 := hquad n k M d (Nat.cast_nonneg d)
  refine le_trans (measure_mono ?_) (le_trans (measure_union_le _ _)
    (le_trans (add_le_add (le_trans (measure_union_le _ _) (add_le_add hB1 hB2)) hB3) ?_))
  · intro x hx
    by_contra hc
    simp only [Set.mem_union, not_or, Set.mem_ofPred_eq, not_exists, not_lt] at hc
    obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hc
    obtain ⟨y, hy, hlt⟩ := hx
    obtain ⟨g, hg, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨b, rfl⟩ := LinearMap.mem_range.1 hz
    set G := cgMat x with hG
    have hRY : (R * ((t : ℂ) • G)).mulVecLin b = R *ᵥ ((t : ℂ) • (G *ᵥ b)) := by
      rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
    rw [hRY] at hlt
    set y := g + R *ᵥ ((t : ℂ) • (G *ᵥ b)) with hy
    -- (9.45) [us:eq:lowerK] on the good event
    have hJHy : JHᴴ *ᵥ y = (t : ℂ) • (N *ᵥ (G *ᵥ b)) := by
      rw [hy, Matrix.mulVec_add, hHF g hg, zero_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hN,
        ← Matrix.mulVec_mulVec]
    have hb : cr * s * Real.sqrt h * l2Norm b ≤ Real.sqrt W * l2Norm y := by
      refine (hn1 b).trans ?_
      have h1 : l2Norm (JHᴴ *ᵥ y) ≤ l2Norm y := by
        refine (l2Norm_mulVec_le _ _).trans ?_
        calc ‖JHᴴ‖ * l2Norm y ≤ 1 * l2Norm y := mul_le_mul_of_nonneg_right
              (gaussProj_norm_isometry_le JH hJH1).2 (gaussProj_l2Norm_nonneg y)
          _ = l2Norm y := one_mul _
      rw [hJHy, gaussProj_l2Norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0] at h1
      rw [ht] at h1
      have hsW : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
      rw [inv_mul_le_iff₀ hsW] at h1
      exact h1
    -- (9.46) [us:eq:Gaussnorm] and (9.47) [us:eq:quadratic] on the good event
    have hX1 : ‖JVᴴ * G‖ ≤ Cn * (Real.sqrt v + Real.sqrt (k + d)) := by
      refine hn2.trans ?_
      rw [gaussProj_hs_isometry JV hJV1]
      have := (gaussProj_norm_isometry_le JV hJV1).2
      gcongr
      calc ‖JVᴴ‖ * Real.sqrt (k + d) ≤ 1 * Real.sqrt (k + d) :=
            mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
        _ = _ := one_mul _
    have hX2 : ‖Gᴴ * M * G‖ ≤ ‖M.trace‖ +
        Cq * (Real.sqrt (k + d) * Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) + (k + d) * ‖M‖) := by
      have h1 : ‖M.trace • (1 : Matrix (Fin k) (Fin k) ℂ)‖ ≤ ‖M.trace‖ := by
        rw [norm_smul]
        calc ‖M.trace‖ * ‖(1 : Matrix (Fin k) (Fin k) ℂ)‖ ≤ ‖M.trace‖ * 1 :=
              mul_le_mul_of_nonneg_left (gaussProj_norm_one_le k) (norm_nonneg _)
          _ = _ := mul_one _
      calc ‖Gᴴ * M * G‖ = ‖(Gᴴ * M * G - M.trace • 1) + M.trace • 1‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖Gᴴ * M * G - M.trace • 1‖ + ‖M.trace • (1 : Matrix (Fin k) (Fin k) ℂ)‖ :=
            norm_add_le _ _
        _ ≤ _ := by linarith [hn3]
    have hsplit := gaussProj_split G JV M ht0.le hJV1 y b (by
      rw [hy, hdec g hg, Matrix.mulVec_smul])
    have hfin := gaussProj_arith (Wr := W) (Dr := d) (kr := k) (vr := v) (hr := h)
      (X1 := ‖JVᴴ * G‖) (X2 := ‖Gᴴ * M * G‖) (TrM := ‖M.trace‖)
      (HS := Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2)) (NM := ‖M‖) (yN := l2Norm y) (bN := l2Norm b)
      hA hC hC₁ hCn hCq hcr hC₀r hW0 (by linarith) hLW (Nat.cast_nonneg k) hkd' hv hh hX1 hX2
      (by
        refine hMtr.trans ?_
        have := ht1
        linarith)
      (Real.sqrt_nonneg _)
      (Real.sqrt_le_sqrt (hMhs.trans ht2))
      hMnorm (gaussProj_l2Norm_nonneg y) (gaussProj_l2Norm_nonneg b) hb
    have := hsplit.trans hfin
    linarith
  · have e1 : Real.exp (-(cr * h)) ≤ Real.exp (-(min 1 (cr * C₀r) * d)) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      calc min 1 (cr * C₀r) * d ≤ cr * C₀r * d :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg d)
        _ = cr * (C₀r * d) := by ring
        _ ≤ cr * h := mul_le_mul_of_nonneg_left hh hcr.le
    have e2 : Real.exp (-(d : ℝ)) ≤ Real.exp (-(min 1 (cr * C₀r) * d)) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      calc min 1 (cr * C₀r) * d ≤ 1 * d :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg d)
        _ = d := one_mul _
    rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
      ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have e3 : 3 * Real.exp (-(min 1 (cr * C₀r) * d)) ≤
        (K / Real.sqrt A + 3) * Real.exp (-(min 1 (cr * C₀r) * d)) := by
      have : 0 ≤ K / Real.sqrt A := by positivity
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    linarith

end LSBA
