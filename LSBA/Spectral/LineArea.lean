import LSBA.Spectral.EigMass

/-!
# The area inequality along a line of Hermitian matrices

(E.7) [uva:eq:coarea-audit], in the form used with (E.11) [uva:eq:cross-audit]: for
`H(u) = H₀ + c u P_T` with `c > 0`, the integral over `u` of `Σ_k ‖P_T ψ_k(u)‖² G(λ_k(u), u)` is at
most `c⁻¹ ∫ dE Σ_ℓ N_ℓ(E) sup_{u ∈ [ℓ, ℓ+1]} G(E, u)`, where `N_ℓ(E)` is the number of
`u ∈ [ℓ, ℓ+1]` with `E ∈ σ(H(u))`, counted with the dimension of the kernel.
-/

open MeasureTheory Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

section LineAreaAux

open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic form `x ↦ Re ⟨x, M x⟩`. -/
private def lineArea_q (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) : ℝ :=
  RCLike.re ⟪x, Matrix.toEuclideanLin M x⟫_ℂ

/-- `A ψ_k = λ_k ψ_k` for the eigenbasis of a Hermitian `A`, as linear maps of Euclidean space. -/
private lemma lineArea_toEuclideanLin_eigenvectorBasis {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (k : ι) : Matrix.toEuclideanLin A (hA.eigenvectorBasis k) =
      ((hA.eigenvalues k : ℝ) : ℂ) • hA.eigenvectorBasis k := by
  ext i
  have := congrFun (hA.mulVec_eigenvectorBasis k) i
  simp only [Matrix.toLpLin_apply, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul] at this ⊢
  rw [this]
  simp [Complex.real_smul]

/-- The quadratic form is additive in the matrix. -/
private lemma lineArea_q_add (M N : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    lineArea_q (M + N) x = lineArea_q M x + lineArea_q N x := by
  simp [lineArea_q, map_add]

/-- The quadratic form is homogeneous under real scalars. -/
private lemma lineArea_q_smul (r : ℝ) (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    lineArea_q ((r : ℂ) • M) x = r * lineArea_q M x := by
  rw [lineArea_q, LinearEquiv.map_smul, LinearMap.smul_apply, inner_smul_right]
  simp [lineArea_q]

/-- `⟨x, P_T x⟩ = Σ_{i ∈ T} |x_i|²`. -/
private lemma lineArea_q_coordProj (T : Finset ι) (x : EuclideanSpace ℂ ι) :
    lineArea_q (coordProj T) x = ∑ i ∈ T, ‖x i‖ ^ 2 := by
  simp only [lineArea_q, coordProj, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Matrix.mulVec_diagonal]
  rw [map_sum, ← Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by simp [hi])]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [ite_eq_left hi, one_mul, Pi.star_apply, RCLike.star_def, RCLike.mul_conj]
  norm_cast

/-- `⟨x, A x⟩ = Σ_k λ_k |⟨ψ_k, x⟩|²` for a Hermitian `A` with eigenbasis `ψ_k`. -/
private lemma lineArea_q_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : EuclideanSpace ℂ ι) :
    lineArea_q A x = ∑ k, hA.eigenvalues k * ‖⟪hA.eigenvectorBasis k, x⟫_ℂ‖ ^ 2 := by
  set b := hA.eigenvectorBasis
  have hx : Matrix.toEuclideanLin A x = ∑ k, (⟪b k, x⟫_ℂ * (hA.eigenvalues k : ℂ)) • b k := by
    conv_lhs => rw [← b.sum_repr' x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, lineArea_toEuclideanLin_eigenvectorBasis, smul_smul]
  rw [lineArea_q, hx, inner_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, ← inner_conj_symm, mul_comm, ← mul_assoc, RCLike.mul_conj,
    RCLike.norm_conj, ← RCLike.ofReal_pow]
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul, mul_comm]
  congr 1


/-- `⟨ψ_k, A ψ_k⟩ = λ_k`. -/
private lemma lineArea_q_eigenvectorBasis {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (k : ι) :
    lineArea_q A (hA.eigenvectorBasis k) = hA.eigenvalues k := by
  rw [lineArea_q, lineArea_toEuclideanLin_eigenvectorBasis, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hA.eigenvectorBasis.orthonormal.1 k]
  simp

/-- The `i`-th eigenvalue in decreasing order is the eigenvalue of `ψ_{e(i)}`, where `e` is the
fixed reindexing of Mathlib. -/
private lemma lineArea_sortedEig_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (i : Fin (Fintype.card ι)) :
    sortedEig A i = hA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin _) i) := by
  rw [eigenvalues_eq_sortedEig hA, Equiv.symm_apply_apply]

/-- The eigenvalues in decreasing order are antitone in the index. -/
private lemma lineArea_sortedEig_antitone {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    Antitone (sortedEig A) := by
  have h : sortedEig A = hA.eigenvalues₀ := by simp [sortedEig, hA]
  rw [h]
  exact hA.eigenvalues₀_antitone

/-- Weyl monotonicity: if `⟨x, A x⟩ ≤ ⟨x, B x⟩` for every `x`, the eigenvalues of `A` and `B` in
decreasing order satisfy `λ_j(A) ≤ λ_j(B)`. -/
private lemma lineArea_sortedEig_mono {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : ∀ x, lineArea_q A x ≤ lineArea_q B x)
    (j : Fin (Fintype.card ι)) : sortedEig A j ≤ sortedEig B j := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) (α := Fin _) (β := ι)
  set v : {i : Fin (Fintype.card ι) // i ≠ j} → EuclideanSpace ℂ ι := fun i =>
    if j < i.1 then hA.eigenvectorBasis (e i.1) else hB.eigenvectorBasis (e i.1)
  set L : EuclideanSpace ℂ ι →ₗ[ℂ] ({i : Fin (Fintype.card ι) // i ≠ j} → ℂ) :=
    LinearMap.pi fun i => innerₛₗ ℂ (v i)
  have hrank : Module.finrank ℂ ({i : Fin (Fintype.card ι) // i ≠ j} → ℂ) <
      Module.finrank ℂ (EuclideanSpace ℂ ι) := by
    rw [Module.finrank_fintype_fun_eq_card, finrank_euclideanSpace]
    have := Fintype.card_subtype_lt (p := fun i : Fin (Fintype.card ι) => i ≠ j) (x := j)
      (by simp)
    simpa using this
  obtain ⟨x, hxk, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hrank)
  have hx : ∀ i : {i : Fin (Fintype.card ι) // i ≠ j}, ⟪v i, x⟫_ℂ = 0 := fun i =>
    congrFun (LinearMap.mem_ker.mp hxk) i
  have hxpos : 0 < ‖x‖ ^ 2 := by positivity
  have hnA : ∑ i, ‖⟪hA.eigenvectorBasis (e i), x⟫_ℂ‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [Equiv.sum_comp e (fun k => ‖⟪hA.eigenvectorBasis k, x⟫_ℂ‖ ^ 2),
      OrthonormalBasis.sum_sq_norm_inner_right]
  have hnB : ∑ i, ‖⟪hB.eigenvectorBasis (e i), x⟫_ℂ‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [Equiv.sum_comp e (fun k => ‖⟪hB.eigenvectorBasis k, x⟫_ℂ‖ ^ 2),
      OrthonormalBasis.sum_sq_norm_inner_right]
  have hqA : lineArea_q A x =
      ∑ i, sortedEig A i * ‖⟪hA.eigenvectorBasis (e i), x⟫_ℂ‖ ^ 2 := by
    rw [lineArea_q_eq_sum hA, ← Equiv.sum_comp e]
    simp only [lineArea_sortedEig_eq hA, e]
  have hqB : lineArea_q B x =
      ∑ i, sortedEig B i * ‖⟪hB.eigenvectorBasis (e i), x⟫_ℂ‖ ^ 2 := by
    rw [lineArea_q_eq_sum hB, ← Equiv.sum_comp e]
    simp only [lineArea_sortedEig_eq hB, e]
  have h1 : sortedEig A j * ‖x‖ ^ 2 ≤ lineArea_q A x := by
    rw [hqA, ← hnA, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hij : j < i
    · have := hx ⟨i, ne_of_gt hij⟩
      simp only [v, hij, ↓reduceIte] at this
      simp [this]
    · exact mul_le_mul_of_nonneg_right (lineArea_sortedEig_antitone hA (not_lt.mp hij))
        (by positivity)
  have h2 : lineArea_q B x ≤ sortedEig B j * ‖x‖ ^ 2 := by
    rw [hqB, ← hnB, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hij : i < j
    · have := hx ⟨i, ne_of_lt hij⟩
      simp only [v, not_lt.mpr hij.le, ↓reduceIte] at this
      simp [this]
    · exact mul_le_mul_of_nonneg_right (lineArea_sortedEig_antitone hB (not_lt.mp hij))
        (by positivity)
  exact le_of_mul_le_mul_right ((h1.trans (hAB x)).trans h2) hxpos

/-- `Σ_i λ_i w_i ≤ Σ_{i < b} λ_i` for `λ` decreasing and weights `0 ≤ w_i ≤ 1` of total `b`. -/
private lemma lineArea_sum_mul_le {n : ℕ} (lam w : Fin n → ℝ) (hlam : Antitone lam)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (b : ℕ) (hb0 : 0 < b) (hbn : b ≤ n)
    (hsum : ∑ i, w i = ∑ i : Fin n, if i.1 < b then (1 : ℝ) else 0) :
    ∑ i, lam i * w i ≤ ∑ i : Fin n, if i.1 < b then lam i else 0 := by
  set t := lam ⟨b - 1, by omega⟩
  have key : ∀ i, lam i * w i - (if i.1 < b then lam i else 0) ≤
      t * (w i - if i.1 < b then (1 : ℝ) else 0) := by
    intro i
    split_ifs with h
    · have : t ≤ lam i := hlam (Fin.mk_le_mk.mpr (by omega) : i ≤ ⟨b - 1, by omega⟩)
      nlinarith [hw1 i]
    · have : lam i ≤ t := hlam (Fin.mk_le_mk.mpr (by omega) : (⟨b - 1, by omega⟩ : Fin n) ≤ i)
      nlinarith [hw0 i]
  have := Finset.sum_le_sum fun i (_ : i ∈ univ) => key i
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hsum, sub_self,
    mul_zero] at this
  linarith

/-- Ky Fan: for an orthonormal family `ψ`, `Σ_{i < b} ⟨ψ_i, A ψ_i⟩ ≤ Σ_{i < b} λ_i(A)`. -/
private lemma lineArea_kyFan {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    {ψ : Fin (Fintype.card ι) → EuclideanSpace ℂ ι} (hψ : Orthonormal ℂ ψ) (b : ℕ) (hb0 : 0 < b)
    (hbn : b ≤ Fintype.card ι) :
    ∑ i : Fin (Fintype.card ι), (if i.1 < b then lineArea_q A (ψ i) else 0) ≤
      ∑ i : Fin (Fintype.card ι), if i.1 < b then sortedEig A i else 0 := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) (α := Fin _) (β := ι)
  set a : Fin (Fintype.card ι) → Fin (Fintype.card ι) → ℝ := fun m i =>
    ‖⟪hA.eigenvectorBasis (e m), ψ i⟫_ℂ‖ ^ 2
  set w : Fin (Fintype.card ι) → ℝ := fun m =>
    ∑ i : Fin (Fintype.card ι), if i.1 < b then a m i else 0
  have hq : ∀ i, lineArea_q A (ψ i) = ∑ m, sortedEig A m * a m i := by
    intro i
    rw [lineArea_q_eq_sum hA, ← Equiv.sum_comp e]
    simp only [lineArea_sortedEig_eq hA, e, a]
  have hL : ∑ i : Fin (Fintype.card ι), (if i.1 < b then lineArea_q A (ψ i) else 0) =
      ∑ m, sortedEig A m * w m := by
    simp only [hq, w, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hw0 : ∀ m, 0 ≤ w m := fun m =>
    Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
  have hw1 : ∀ m, w m ≤ 1 := by
    intro m
    have h := hψ.sum_inner_products_le (hA.eigenvectorBasis (e m))
      (s := univ.filter fun i : Fin (Fintype.card ι) => i.1 < b)
    rw [OrthonormalBasis.norm_eq_one, one_pow, Finset.sum_filter] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [a, norm_inner_symm]
  have hsum : ∑ m, w m = ∑ i : Fin (Fintype.card ι), if i.1 < b then (1 : ℝ) else 0 := by
    simp only [w]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs
    · simp only [a]
      rw [Equiv.sum_comp e (fun k => ‖⟪hA.eigenvectorBasis k, ψ i⟫_ℂ‖ ^ 2),
        OrthonormalBasis.sum_sq_norm_inner_right, hψ.1 i, one_pow]
    · simp
  rw [hL]
  exact lineArea_sum_mul_le _ w (lineArea_sortedEig_antitone hA) hw0 hw1 b hb0 hbn hsum

/-- The real-scalar line `H₀ + (c u) P_T` through a Hermitian `H₀` consists of Hermitian
matrices. -/
private lemma lineArea_isHermitian {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian) (T : Finset ι)
    (r : ℝ) : (H₀ + (r : ℂ) • coordProj T).IsHermitian := by
  refine hH₀.add (Matrix.IsHermitian.smul ?_ (by simp [IsSelfAdjoint]))
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  ext i
  by_cases hi : i ∈ T <;> simp [hi]

/-- `⟨x, H(u) x⟩ = ⟨x, H(u₀) x⟩ + c (u − u₀) ⟨x, P_T x⟩` along `H(u) = H₀ + c u P_T`. -/
private lemma lineArea_q_line (H₀ : Matrix ι ι ℂ) (T : Finset ι) (c u u₀ : ℝ)
    (x : EuclideanSpace ℂ ι) :
    lineArea_q (H₀ + ((c * u : ℝ) : ℂ) • coordProj T) x =
      lineArea_q (H₀ + ((c * u₀ : ℝ) : ℂ) • coordProj T) x +
        c * (u - u₀) * lineArea_q (coordProj T) x := by
  have h : H₀ + ((c * u : ℝ) : ℂ) • coordProj T = (H₀ + ((c * u₀ : ℝ) : ℂ) • coordProj T) +
      ((c * (u - u₀) : ℝ) : ℂ) • coordProj T := by
    rw [add_assoc, ← add_smul]
    congr 2
    push_cast
    ring
  rw [h, lineArea_q_add, lineArea_q_smul]

/-- `0 ≤ ⟨x, P_T x⟩`. -/
private lemma lineArea_q_coordProj_nonneg (T : Finset ι) (x : EuclideanSpace ℂ ι) :
    0 ≤ lineArea_q (coordProj T) x := by
  rw [lineArea_q_coordProj]
  positivity

/-- Each eigenvalue in decreasing order of `H₀ + c u P_T`, `c > 0`, is nondecreasing in `u`. -/
private lemma lineArea_monotone {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian) (T : Finset ι)
    {c : ℝ} (hc : 0 < c) (j : Fin (Fintype.card ι)) :
    Monotone fun u : ℝ => sortedEig (H₀ + ((c * u : ℝ) : ℂ) • coordProj T) j := by
  intro u u' huu'
  refine lineArea_sortedEig_mono (lineArea_isHermitian hH₀ T _) (lineArea_isHermitian hH₀ T _)
    (fun x => ?_) j
  rw [lineArea_q_line H₀ T c u' u x]
  have := lineArea_q_coordProj_nonneg T x
  have : 0 ≤ c * (u' - u) := mul_nonneg hc.le (by linarith)
  nlinarith

/-- Each eigenvalue in decreasing order of `H₀ + c u P_T` is continuous in `u`. -/
private lemma lineArea_continuous {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian) (T : Finset ι)
    (c : ℝ) (j : Fin (Fintype.card ι)) :
    Continuous fun u : ℝ => sortedEig (H₀ + ((c * u : ℝ) : ℂ) • coordProj T) j := by
  have hH : Continuous fun u : ℝ => H₀ + ((c * u : ℝ) : ℂ) • coordProj T := by fun_prop
  exact (continuous_apply j).comp
    (continuousOn_sortedEig.comp_continuous hH fun u => lineArea_isHermitian hH₀ T _)

/-- `Σ_{i < j+1} f_i = Σ_{i < j} f_i + f_j`. -/
private lemma lineArea_sum_lt_succ {n : ℕ} (f : Fin n → ℝ) (j : Fin n) :
    (∑ i : Fin n, if i.1 < j.1 + 1 then f i else 0) =
      (∑ i : Fin n, if i.1 < j.1 then f i else 0) + f j := by
  have h : f j = ∑ i : Fin n, if i = j then f i else 0 := by simp
  rw [h, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hij : i = j
  · subst hij
    simp
  · have : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
    by_cases hlt : i.1 < j.1
    · simp [hij, hlt, show i.1 < j.1 + 1 by omega]
    · simp [hij, hlt, show ¬ i.1 < j.1 + 1 by omega]

/-- At a point where every eigenvalue `λ_i(u)` of `H(u) = H₀ + c u P_T` is differentiable,
`Σ_{i < b} λ_i′(u₀) = c Σ_{i < b} ‖P_T ψ_i(u₀)‖²` for the eigenbasis `ψ_i(u₀)` in decreasing order:
the minimum at `u₀` of `Σ_{i < b} λ_i(u) − Σ_{i < b} ⟨ψ_i(u₀), H(u) ψ_i(u₀)⟩ ≥ 0` (Ky Fan). -/
private lemma lineArea_deriv_sum {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian) (T : Finset ι)
    (c u₀ : ℝ) (hd : ∀ j : Fin (Fintype.card ι), DifferentiableAt ℝ
      (fun u : ℝ => sortedEig (H₀ + ((c * u : ℝ) : ℂ) • coordProj T) j) u₀)
    (b : ℕ) (hbn : b ≤ Fintype.card ι) :
    (∑ i : Fin (Fintype.card ι), if i.1 < b then
      deriv (fun u : ℝ => sortedEig (H₀ + ((c * u : ℝ) : ℂ) • coordProj T) i) u₀ else 0) =
      c * ∑ i : Fin (Fintype.card ι), if i.1 < b then lineArea_q (coordProj T)
        ((lineArea_isHermitian hH₀ T (c * u₀)).eigenvectorBasis
          (Fintype.equivOfCardEq (Fintype.card_fin _) i)) else 0 := by
  rcases Nat.eq_zero_or_pos b with hb | hb0
  · subst hb
    simp
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) (α := Fin _) (β := ι)
  set h₀ := lineArea_isHermitian hH₀ T (c * u₀)
  set lam : Fin (Fintype.card ι) → ℝ → ℝ := fun j u =>
    sortedEig (H₀ + ((c * u : ℝ) : ℂ) • coordProj T) j
  set ψ : Fin (Fintype.card ι) → EuclideanSpace ℂ ι := fun i => h₀.eigenvectorBasis (e i)
  set m : Fin (Fintype.card ι) → ℝ := fun i => lineArea_q (coordProj T) (ψ i)
  have hψ : Orthonormal ℂ ψ := h₀.eigenvectorBasis.orthonormal.comp _ e.injective
  set F : ℝ → ℝ := fun u => (∑ i : Fin (Fintype.card ι), if i.1 < b then lam i u else 0) -
    ∑ i : Fin (Fintype.card ι), if i.1 < b then lam i u₀ + c * m i * (u - u₀) else 0
  have hF0 : F u₀ = 0 := by simp [F]
  have hFnn : ∀ u, 0 ≤ F u := by
    intro u
    have hk := lineArea_kyFan (lineArea_isHermitian hH₀ T (c * u)) hψ b hb0 hbn
    have heq : ∀ i, lineArea_q (H₀ + ((c * u : ℝ) : ℂ) • coordProj T) (ψ i) =
        lam i u₀ + c * m i * (u - u₀) := by
      intro i
      rw [lineArea_q_line H₀ T c u u₀, lineArea_q_eigenvectorBasis,
        ← lineArea_sortedEig_eq h₀]
      simp only [lam, m]
      ring
    simp only [heq] at hk
    simp only [F, lam]
    linarith
  have hmin : IsLocalMin F u₀ :=
    Filter.Eventually.of_forall fun u => by rw [hF0]; exact hFnn u
  have hderiv : HasDerivAt F ((∑ i : Fin (Fintype.card ι), if i.1 < b then
      deriv (lam i) u₀ else 0) - ∑ i : Fin (Fintype.card ι), if i.1 < b then c * m i * 1
        else 0) u₀ := by
    refine HasDerivAt.sub (HasDerivAt.fun_sum fun i _ => ?_) (HasDerivAt.fun_sum fun i _ => ?_)
    · split_ifs
      · exact (hd i).hasDerivAt
      · exact hasDerivAt_const _ _
    · split_ifs
      · exact (((hasDerivAt_id u₀).sub_const u₀).const_mul (c * m i)).const_add _
      · exact hasDerivAt_const _ _
  have h0 := hmin.hasDerivAt_eq_zero hderiv
  rw [Finset.mul_sum]
  simp only [mul_one, mul_ite, mul_zero] at h0 ⊢
  linarith

/-- At a point where every eigenvalue of `H(u) = H₀ + c u P_T` is differentiable,
`Σ_k ‖P_T ψ_k(u)‖² G(λ_k(u)) = Σ_j c⁻¹ λ_j′(u) G(λ_j(u))` over the eigenvalues in decreasing
order. -/
private lemma lineArea_eigMassSum_eq {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian) (T : Finset ι)
    {c : ℝ} (hc : 0 < c) (u₀ : ℝ) (hd : ∀ j : Fin (Fintype.card ι), DifferentiableAt ℝ
      (fun u : ℝ => sortedEig (H₀ + ((c * u : ℝ) : ℂ) • coordProj T) j) u₀)
    (G : ℝ → ℝ≥0∞) :
    eigMassSum (H₀ + ((c * u₀ : ℝ) : ℂ) • coordProj T) T G =
      ∑ j : Fin (Fintype.card ι), ENNReal.ofReal c⁻¹ * (ENNReal.ofReal
        (deriv (fun u : ℝ => sortedEig (H₀ + ((c * u : ℝ) : ℂ) • coordProj T) j) u₀) *
          G (sortedEig (H₀ + ((c * u₀ : ℝ) : ℂ) • coordProj T) j)) := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) (α := Fin _) (β := ι)
  set h₀ := lineArea_isHermitian hH₀ T (c * u₀)
  have hj : ∀ j : Fin (Fintype.card ι),
      deriv (fun u : ℝ => sortedEig (H₀ + ((c * u : ℝ) : ℂ) • coordProj T) j) u₀ =
        c * lineArea_q (coordProj T) (h₀.eigenvectorBasis (e j)) := by
    intro j
    have h1 := lineArea_deriv_sum hH₀ T c u₀ hd (j.1 + 1) j.2
    have h2 := lineArea_deriv_sum hH₀ T c u₀ hd j.1 j.2.le
    rw [lineArea_sum_lt_succ, lineArea_sum_lt_succ, h2, mul_add] at h1
    exact add_left_cancel h1
  simp only [eigMassSum, h₀, ↓reduceDIte]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hj, ← lineArea_sortedEig_eq h₀, lineArea_q_coordProj, ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

/-- The number of eigenvalues of a Hermitian `A` equal to `E`, counted in decreasing order, is at
most `dim ker(A − E)`. -/
private lemma lineArea_card_le_finrank {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (E : ℝ) :
    (univ.filter fun j : Fin (Fintype.card ι) => sortedEig A j = E).card ≤
      Module.finrank ℂ (LinearMap.ker (Matrix.toLin' (A - (E : ℂ) • 1))) := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) (α := Fin _) (β := ι)
  set K := {j : Fin (Fintype.card ι) // sortedEig A j = E}
  set v : K → (ι → ℂ) := fun j => WithLp.linearEquiv 2 ℂ (ι → ℂ) (hA.eigenvectorBasis (e j.1))
  have hli : LinearIndependent ℂ v := by
    have h := (hA.eigenvectorBasis.orthonormal.comp _ (e.injective.comp
      (Subtype.val_injective (p := fun j : Fin (Fintype.card ι) => sortedEig A j = E))))
      |>.linearIndependent
    exact h.map' _ (WithLp.linearEquiv 2 ℂ (ι → ℂ)).ker
  have hspan : Submodule.span ℂ (Set.range v) ≤
      LinearMap.ker (Matrix.toLin' (A - (E : ℂ) • 1)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hE : hA.eigenvalues (e j.1) = E := by rw [← lineArea_sortedEig_eq hA]; exact j.2
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, v]
    change A *ᵥ (hA.eigenvectorBasis (e j.1)).ofLp -
      (E : ℂ) • (hA.eigenvectorBasis (e j.1)).ofLp = 0
    rw [hA.mulVec_eigenvectorBasis, hE, sub_eq_zero]
    ext i
    simp [Complex.real_smul]
  rw [← Fintype.card_subtype, ← finrank_span_eq_card hli]
  exact Submodule.finrank_mono hspan

/-- `Σ_j 1{E ∈ λ_j(s_j)} ≤ N_I(E)` for sets `s_j ⊆ I`: each such `j` has a parameter `u ∈ I` with
`λ_j(u) = E`, and at most `dim ker(H(u) − E)` indices share a parameter. -/
private lemma lineArea_card_le_crossCount (H : ℝ → Matrix ι ι ℂ) (hH : ∀ u, (H u).IsHermitian)
    (E : ℝ) (I : Set ℝ) (s : Fin (Fintype.card ι) → Set ℝ) (hsI : ∀ j, s j ⊆ I) :
    (((univ.filter fun j => E ∈ (fun u => sortedEig (H u) j) '' s j).card : ℕ) : ℝ≥0∞) ≤
      crossCount H E I := by
  set J := univ.filter fun j => E ∈ (fun u => sortedEig (H u) j) '' s j
  set φ : Fin (Fintype.card ι) → ℝ := fun j =>
    if h : E ∈ (fun u => sortedEig (H u) j) '' s j then h.choose else 0
  have hφ : ∀ j ∈ J, φ j ∈ s j ∧ sortedEig (H (φ j)) j = E := by
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    simp only [φ, h, ↓reduceDIte]
    exact h.choose_spec
  set d : ℝ → ℝ≥0∞ := fun u =>
    (Module.finrank ℂ (LinearMap.ker (Matrix.toLin' (H u - (E : ℂ) • 1))) : ℝ≥0∞)
  have hfib : ∀ v ∈ J.image φ, ((J.filter fun j => φ j = v).card : ℝ≥0∞) ≤ d v := by
    intro v _
    refine le_trans ?_ (Nat.cast_le.mpr (lineArea_card_le_finrank (hH v) E))
    refine Nat.cast_le.mpr (Finset.card_le_card fun j hj => ?_)
    obtain ⟨hjJ, hjv⟩ := Finset.mem_filter.mp hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hjv]
    exact (hφ j hjJ).2
  have hI : ∀ v ∈ J.image φ, v ∈ I := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    exact hsI j (hφ j hj).1
  calc ((J.card : ℕ) : ℝ≥0∞) = ∑ v ∈ J.image φ, ((J.filter fun j => φ j = v).card : ℝ≥0∞) := by
        rw [Finset.card_eq_sum_card_image φ J]
        push_cast
        rfl
    _ ≤ ∑ v ∈ J.image φ, d v := Finset.sum_le_sum hfib
    _ = ∑ w ∈ (J.image φ).subtype (· ∈ I), d w.1 := (Finset.sum_subtype_of_mem d hI).symm
    _ ≤ ∑' w : I, d w.1 := ENNReal.sum_le_tsum _
    _ = crossCount H E I := rfl

/-- The one-dimensional area step: for `f` continuous and nondecreasing, `s = {f′ > 0} ∩ I` and
`F ≤ g ∘ f` on `I`, `∫_I f′ F ≤ ∫ 1_{f(s)} g`; `f` is injective on `s`. -/
private lemma lineArea_setLIntegral_le {f : ℝ → ℝ} (hmono : Monotone f) (hcont : Continuous f)
    {I : Set ℝ} (hI : MeasurableSet I) (F g : ℝ → ℝ≥0∞) (hFg : ∀ u ∈ I, F u ≤ g (f u)) :
    ∫⁻ u in I, ENNReal.ofReal (deriv f u) * F u ≤
      ∫⁻ E, (f '' ({u | 0 < deriv f u} ∩ I)).indicator g E := by
  set s := {u | 0 < deriv f u} ∩ I
  have hs : MeasurableSet s := (measurableSet_lt measurable_const (measurable_deriv f)).inter hI
  have hder : ∀ x ∈ s, HasDerivWithinAt f (deriv f x) s x := fun x hx =>
    (differentiableAt_of_deriv_ne_zero (ne_of_gt hx.1)).hasDerivAt.hasDerivWithinAt
  have hinj : Set.InjOn f s := by
    have key : ∀ x ∈ s, ∀ y, x < y → f x ≠ f y := by
      intro x hx y hxy hfxy
      have hconst : ∀ z ∈ Set.Icc x y, f z = f x := fun z hz =>
        le_antisymm (hfxy ▸ hmono hz.2) (hmono hz.1)
      have h1 : HasDerivWithinAt f 0 (Set.Icc x y) x :=
        (hasDerivWithinAt_const x (Set.Icc x y) (f x)).congr (fun z hz => hconst z hz) rfl
      have h2 : HasDerivWithinAt f (deriv f x) (Set.Icc x y) x :=
        (differentiableAt_of_deriv_ne_zero (ne_of_gt hx.1)).hasDerivAt.hasDerivWithinAt
      have := (uniqueDiffOn_Icc hxy x ⟨le_rfl, hxy.le⟩).eq_deriv _ h2 h1
      exact (ne_of_gt hx.1) this
    intro x hx y hy hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key x hx y h hxy
    · exact key y hy x h hxy.symm
  have himg : MeasurableSet (f '' s) := hs.image_of_continuousOn_injOn hcont.continuousOn hinj
  calc ∫⁻ u in I, ENNReal.ofReal (deriv f u) * F u
      = ∫⁻ u in I, {u | 0 < deriv f u}.indicator
          (fun u => ENNReal.ofReal (deriv f u) * F u) u := by
        refine lintegral_congr fun u => ?_
        by_cases hu : 0 < deriv f u
        · simp [Set.indicator, hu]
        · simp [Set.indicator, hu, ENNReal.ofReal_of_nonpos (not_lt.mp hu)]
    _ = ∫⁻ u in s, ENNReal.ofReal (deriv f u) * F u :=
        setLIntegral_indicator (measurableSet_lt measurable_const (measurable_deriv f)) _
    _ ≤ ∫⁻ u in s, ENNReal.ofReal |deriv f u| * g (f u) := by
        refine setLIntegral_mono' hs fun u hu => ?_
        rw [abs_of_pos hu.1]
        gcongr
        exact hFg u hu.2
    _ = ∫⁻ E in f '' s, g E := (lintegral_image_eq_lintegral_abs_deriv_mul hs hder hinj g).symm
    _ = ∫⁻ E, (f '' s).indicator g E := (lintegral_indicator himg g).symm

section Superadditive

variable {α κ : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `Σ_{i ∈ S} ∫ F_i ≤ ∫ Σ_{i ∈ S} F_i` for arbitrary functions. -/
private lemma lineArea_sum_lintegral_le (S : Finset κ) (F : κ → α → ℝ≥0∞) :
    ∑ i ∈ S, ∫⁻ a, F i a ∂μ ≤ ∫⁻ a, ∑ i ∈ S, F i a ∂μ := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-- `Σ'_ℓ ∫ F_ℓ ≤ ∫ Σ'_ℓ F_ℓ` for arbitrary functions. -/
private lemma lineArea_tsum_lintegral_le (F : κ → α → ℝ≥0∞) :
    ∑' i, ∫⁻ a, F i a ∂μ ≤ ∫⁻ a, ∑' i, F i a ∂μ := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun S => (lineArea_sum_lintegral_le S F).trans
    (lintegral_mono fun a => ENNReal.sum_le_tsum S)

end Superadditive

end LineAreaAux

/-- (E.7) [uva:eq:coarea-audit] for `H(u) = H₀ + c u P_T`, `c > 0`, with the root sum grouped
over the unit intervals `[ℓ, ℓ+1]`. -/
theorem lintegral_eigMassSum_line_le {ι : Type*} [Fintype ι] [DecidableEq ι] {H₀ : Matrix ι ι ℂ}
    (hH₀ : H₀.IsHermitian) (T : Finset ι) {c : ℝ} (hc : 0 < c) {G : ℝ → ℝ → ℝ≥0∞}
    (hG : Measurable (Function.uncurry G)) :
    ∫⁻ u, eigMassSum (H₀ + ((c * u : ℝ) : ℂ) • coordProj T) T (fun E => G E u) ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ E, ∑' ℓ : ℤ,
        crossCount (fun u => H₀ + ((c * u : ℝ) : ℂ) • coordProj T) E (Set.Icc (ℓ : ℝ) (ℓ + 1)) *
          (⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), G E u) := by
  set H : ℝ → Matrix ι ι ℂ := fun u => H₀ + ((c * u : ℝ) : ℂ) • coordProj T with hHdef
  set lam : Fin (Fintype.card ι) → ℝ → ℝ := fun j u => sortedEig (H u) j with hlam
  set g : ℤ → ℝ → ℝ≥0∞ := fun ℓ E => ⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), G E u with hg
  set s : Fin (Fintype.card ι) → ℤ → Set ℝ := fun j ℓ =>
    {u | 0 < deriv (lam j) u} ∩ Set.Ico (ℓ : ℝ) (ℓ + 1) with hs
  set F : Fin (Fintype.card ι) → ℝ → ℝ≥0∞ := fun j u =>
    ENNReal.ofReal (deriv (lam j) u) * G (lam j u) u with hF
  have hmono : ∀ j, Monotone (lam j) := lineArea_monotone hH₀ T hc
  have hcont : ∀ j, Continuous (lam j) := lineArea_continuous hH₀ T c
  have hD : ∀ᵐ u, ∀ j, DifferentiableAt ℝ (lam j) u :=
    ae_all_iff.mpr fun j => (hmono j).ae_differentiableAt
  have hFmeas : ∀ j, Measurable (F j) := fun j =>
    (ENNReal.measurable_ofReal.comp (measurable_deriv _)).mul
      (hG.comp ((hcont j).measurable.prodMk measurable_id))
  -- the area step on each unit interval
  have harea : ∀ j (ℓ : ℤ), ∫⁻ u in Set.Ico (ℓ : ℝ) (ℓ + 1), F j u ≤
      ∫⁻ E, (lam j '' s j ℓ).indicator (g ℓ) E := fun j ℓ =>
    lineArea_setLIntegral_le (hmono j) (hcont j) measurableSet_Ico _ _ fun u hu =>
      le_iSup₂_of_le (f := fun u' (_ : u' ∈ Set.Icc (ℓ : ℝ) (ℓ + 1)) => G (lam j u) u') u
        (Set.Ico_subset_Icc_self hu) le_rfl
  -- the root count on each unit interval
  have hcount : ∀ (ℓ : ℤ) E, ∑ j, (lam j '' s j ℓ).indicator (g ℓ) E ≤
      crossCount H E (Set.Icc (ℓ : ℝ) (ℓ + 1)) * g ℓ E := by
    intro ℓ E
    have h : ∑ j, (lam j '' s j ℓ).indicator (g ℓ) E =
        (((univ.filter fun j => E ∈ (fun u => sortedEig (H u) j) '' s j ℓ).card : ℕ) :
          ℝ≥0∞) * g ℓ E := by
      simp only [Set.indicator_apply]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [h]
    exact mul_le_mul_of_nonneg_right (lineArea_card_le_crossCount H
      (fun u => lineArea_isHermitian hH₀ T _) E _ (fun j => s j ℓ)
      (fun j => Set.inter_subset_right.trans Set.Ico_subset_Icc_self)) (by positivity)
  have hsplit : ∀ j, ∫⁻ u, F j u = ∑' ℓ : ℤ, ∫⁻ u in Set.Ico (ℓ : ℝ) (ℓ + 1), F j u := by
    intro j
    rw [← setLIntegral_univ, ← iUnion_Ico_intCast (α := ℝ),
      lintegral_iUnion (fun ℓ => measurableSet_Ico) (Set.pairwise_disjoint_Ico_intCast ℝ)]
  have hkey : ∑ j, ∫⁻ u, F j u ≤ ∫⁻ E, ∑' ℓ : ℤ,
      crossCount H E (Set.Icc (ℓ : ℝ) (ℓ + 1)) * g ℓ E := by
    calc ∑ j, ∫⁻ u, F j u
        ≤ ∑ j, ∑' ℓ : ℤ, ∫⁻ E, (lam j '' s j ℓ).indicator (g ℓ) E := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [hsplit j]
          exact ENNReal.tsum_le_tsum fun ℓ => harea j ℓ
      _ = ∑' ℓ : ℤ, ∑ j, ∫⁻ E, (lam j '' s j ℓ).indicator (g ℓ) E :=
          (Summable.tsum_finsetSum fun _ _ => ENNReal.summable).symm
      _ ≤ ∑' ℓ : ℤ, ∫⁻ E, ∑ j, (lam j '' s j ℓ).indicator (g ℓ) E :=
          ENNReal.tsum_le_tsum fun ℓ => lineArea_sum_lintegral_le _ _
      _ ≤ ∫⁻ E, ∑' ℓ : ℤ, ∑ j, (lam j '' s j ℓ).indicator (g ℓ) E :=
          lineArea_tsum_lintegral_le _
      _ ≤ ∫⁻ E, ∑' ℓ : ℤ, crossCount H E (Set.Icc (ℓ : ℝ) (ℓ + 1)) * g ℓ E :=
          lintegral_mono fun E => ENNReal.tsum_le_tsum fun ℓ => hcount ℓ E
  calc ∫⁻ u, eigMassSum (H u) T (fun E => G E u)
      = ∫⁻ u, ∑ j, ENNReal.ofReal c⁻¹ * F j u := by
        refine lintegral_congr_ae (hD.mono fun u hu => ?_)
        exact lineArea_eigMassSum_eq hH₀ T hc u hu _
    _ = ∑ j, ∫⁻ u, ENNReal.ofReal c⁻¹ * F j u :=
        lintegral_finsetSum _ fun j _ => (hFmeas j).const_mul _
    _ = ENNReal.ofReal c⁻¹ * ∑ j, ∫⁻ u, F j u := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_of_nonneg_left hkey (by positivity)

end LSBA
