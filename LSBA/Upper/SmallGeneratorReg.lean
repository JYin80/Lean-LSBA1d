import LSBA.Upper.SmallGenerator
import LSBA.Upper.ChosenGenerator

/-!
# Symmetry, smoothness and measurability of the construction of `K`

Section 9.2 [su:sec:explicit-generator] and Lemma 9.3 [su:lem:chosen-generator](ii): for fixed
`R_4 = R`, `P` and threshold `t`, the generator `K` of (9.18) [us:eq:normalize] is equivariant
under the change (9.24) [su:eq:cut-generator-equivariance] by every unitary `U` with
`U (1 - P) = 1 - P`, and unchanged under `v ↦ a v`, `a ≠ 0`. It is smooth on the open set where
`R_5, …, R_{q-1}`, the right-cavity inverses and `R̃` exist, `t²` is not an eigenvalue of `A* A`,
`P v ≠ 0`, `B_Q` is invertible and `ξ ≠ 0` (the invariant open set of Section 9.4.4
[su:sec:cutoff-estimates]), and it is jointly measurable in `(R, ω, v)` when `P` is a
measurable function of `R`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The open set of Section 9.2 [su:sec:explicit-generator] on which the construction is
smooth: the inverses of (3.4) [us:eq:cavity] exist, `t²` is not an eigenvalue of `A* A`,
`P v ≠ 0`, `Q Π Q + 1 - Q` is invertible and `ξ ≠ 0`. -/
def genGood (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ)
    (P : Matrix (Fin W) (Fin W) ℂ) : Set (Ω W q × (Fin W → ℂ)) :=
  {p | (∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R p.1 j)) ∧
    (∀ m, m ≤ q - 7 → IsUnit (cavR W g E q p.1 m)) ∧ IsUnit (cavRes W g E q R p.1) ∧
    IsUnit ((cavProd W g E q p.1 (q - 6))ᴴ * cavProd W g E q p.1 (q - 6) -
      ((t ^ 2 : ℝ) : ℂ) • 1) ∧
    P *ᵥ p.2 ≠ 0 ∧
    IsUnit (retProj W g E q R t p.1 * allowProj P p.2 * retProj W g E q R t p.1 +
      (1 - retProj W g E q R t p.1)) ∧
    genScale W g E q R t P p.1 p.2 ≠ 0}

/-! ### Spectral calculus in an eigenbasis; the spectral projection at a gap

For a Hermitian `H` with orthonormal eigenvectors `u_k` and eigenvalues `λ_k`, the sums
`Σ_k f(λ_k) u_k u_k*` multiply as functions of `λ`; `1`, `H` and `1_T(H)` are of this form. If `c`
is not an eigenvalue of `H(x)`, then `1_{(c, ∞)}(H) = (1 + X⁻¹ |X|) / 2` with `X = H - c` and
`|X| = √(X²)`. Near `x`, `|X|` is the local inverse of `R ↦ R²` at `|X(x)|`, whose derivative
`D ↦ |X| D + D |X|` is invertible; so the projection is smooth on the set where `c` is not an
eigenvalue, as used for the open set of Section 9.2 [su:sec:explicit-generator]. -/

section Gap

variable {W : ℕ} {H : Matrix (Fin W) (Fin W) ℂ}

/-- The rank-one projection `u_k u_k*` onto the `k`-th eigenvector of `H`. -/
private def evProj (hH : H.IsHermitian) (k : Fin W) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.vecMulVec ⇑(hH.eigenvectorBasis k) (star ⇑(hH.eigenvectorBasis k))

/-- `Σ_k f(λ_k) u_k u_k*` over the eigenpairs of `H`. -/
private def eigSum (hH : H.IsHermitian) (f : ℝ → ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  ∑ k, ((f (hH.eigenvalues k) : ℝ) : ℂ) • evProj hH k

private lemma evDot (hH : H.IsHermitian) (i j : Fin W) :
    star ⇑(hH.eigenvectorBasis i) ⬝ᵥ ⇑(hH.eigenvectorBasis j) = if i = j then 1 else 0 := by
  have h := orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [dotProduct_comm]
  exact h

private lemma evProj_mul (hH : H.IsHermitian) (i j : Fin W) :
    evProj hH i * evProj hH j = if i = j then evProj hH i else 0 := by
  unfold evProj
  rw [Matrix.vecMulVec_mul_vecMulVec, evDot]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

private lemma eigSum_mul (hH : H.IsHermitian) (f g : ℝ → ℝ) :
    eigSum hH f * eigSum hH g = eigSum hH (fun x => f x * g x) := by
  unfold eigSum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  simp_rw [Matrix.smul_mul, Matrix.mul_smul, evProj_mul, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  rw [smul_smul, ← Complex.ofReal_mul]

private lemma specProj_eigSum (hH : H.IsHermitian) (T : Set ℝ) :
    specProj H T = eigSum hH (fun x => if x ∈ T then 1 else 0) := by
  unfold specProj eigSum evProj
  simp only [hH, ↓reduceDIte]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : hH.eigenvalues k ∈ T <;> simp [h]

private lemma eigSum_one (hH : H.IsHermitian) : eigSum hH (fun _ => 1) = 1 := by
  have h := (specProj_add_compl hH Set.univ).2
  rw [specProj_eigSum hH] at h
  simpa using h

private lemma eigSum_smul (hH : H.IsHermitian) (c : ℝ) (f : ℝ → ℝ) :
    (c : ℂ) • eigSum hH f = eigSum hH (fun x => c * f x) := by
  unfold eigSum
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  push_cast
  rfl

private lemma eigSum_id (hH : H.IsHermitian) : H = eigSum hH (fun x => x) := by
  have h1 : H = H * eigSum hH (fun _ => 1) := by rw [eigSum_one, Matrix.mul_one]
  refine h1.trans ?_
  unfold eigSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, evProj, Matrix.mul_vecMulVec, hH.mulVec_eigenvectorBasis,
    Matrix.smul_vecMulVec]
  beta_reduce
  rw [Complex.ofReal_one, one_smul]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

private lemma eigSum_mulVec (hH : H.IsHermitian) (f : ℝ → ℝ) (j : Fin W) :
    eigSum hH f *ᵥ ⇑(hH.eigenvectorBasis j) =
      ((f (hH.eigenvalues j) : ℝ) : ℂ) • ⇑(hH.eigenvectorBasis j) := by
  unfold eigSum evProj
  rw [Matrix.sum_mulVec]
  simp_rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, evDot, op_smul_eq_smul, ite_smul,
    one_smul, zero_smul, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq']
  simp

open scoped ComplexOrder in
private lemma eigSum_posSemidef (hH : H.IsHermitian) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) :
    (eigSum hH f).PosSemidef := by
  unfold eigSum
  refine Matrix.posSemidef_sum _ fun k _ => ?_
  have h : ((f (hH.eigenvalues k) : ℝ) : ℂ) • evProj hH k =
      Matrix.vecMulVec (((Real.sqrt (f (hH.eigenvalues k)) : ℝ) : ℂ) • ⇑(hH.eigenvectorBasis k))
        (star (((Real.sqrt (f (hH.eigenvalues k)) : ℝ) : ℂ) • ⇑(hH.eigenvectorBasis k))) := by
    rw [star_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, evProj]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hf _)]
  rw [h]
  exact Matrix.posSemidef_vecMulVec_self_star _


private lemma eigSum_sub (hH : H.IsHermitian) (f g : ℝ → ℝ) :
    eigSum hH f - eigSum hH g = eigSum hH (fun x => f x - g x) := by
  unfold eigSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← sub_smul]
  push_cast
  rfl

private lemma eigSum_sub_const (hH : H.IsHermitian) (c : ℝ) :
    H - ((c : ℝ) : ℂ) • 1 = eigSum hH (fun x => x - c) := by
  have h := eigSum_smul hH c (fun _ => 1)
  rw [eigSum_one] at h
  have h1 : H - ((c : ℝ) : ℂ) • 1 = eigSum hH (fun x => x) - ((c : ℝ) : ℂ) • 1 :=
    congrArg (fun M => M - ((c : ℝ) : ℂ) • 1) (eigSum_id hH)
  rw [h1, h, eigSum_sub]
  simp

private lemma evProj_mul_eigSum (hH : H.IsHermitian) (a : ℝ → ℝ) (i : Fin W) :
    evProj hH i * eigSum hH a = ((a (hH.eigenvalues i) : ℝ) : ℂ) • evProj hH i := by
  unfold eigSum
  rw [Finset.mul_sum]
  simp_rw [Matrix.mul_smul, evProj_mul, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq]
  simp

private lemma eigSum_mul_evProj (hH : H.IsHermitian) (a : ℝ → ℝ) (j : Fin W) :
    eigSum hH a * evProj hH j = ((a (hH.eigenvalues j) : ℝ) : ℂ) • evProj hH j := by
  unfold eigSum
  rw [Finset.sum_mul]
  simp_rw [Matrix.smul_mul, evProj_mul, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq']
  simp

private lemma sum_evProj (hH : H.IsHermitian) : ∑ k, evProj hH k = 1 := by
  have h := eigSum_one hH
  unfold eigSum at h
  simpa using h

private lemma eigSum_sq_injective (hH : H.IsHermitian) {a : ℝ → ℝ}
    (ha : ∀ k, 0 < a (hH.eigenvalues k)) :
    Function.Injective (fun D : Matrix (Fin W) (Fin W) ℂ => eigSum hH a * D + D * eigSum hH a) := by
  intro D₁ D₂ h
  simp only at h
  have h0 : eigSum hH a * (D₁ - D₂) + (D₁ - D₂) * eigSum hH a = 0 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← sub_eq_zero.mpr h]
    abel
  have key : ∀ i j, evProj hH i * (D₁ - D₂) * evProj hH j = 0 := by
    intro i j
    have h1 : evProj hH i * (eigSum hH a * (D₁ - D₂) + (D₁ - D₂) * eigSum hH a) *
        evProj hH j = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]
    have e1 : evProj hH i * (eigSum hH a * (D₁ - D₂)) * evProj hH j =
        ((a (hH.eigenvalues i) : ℝ) : ℂ) • (evProj hH i * (D₁ - D₂) * evProj hH j) := by
      rw [← Matrix.mul_assoc, evProj_mul_eigSum, Matrix.smul_mul, Matrix.smul_mul]
    have e2 : evProj hH i * ((D₁ - D₂) * eigSum hH a) * evProj hH j =
        ((a (hH.eigenvalues j) : ℝ) : ℂ) • (evProj hH i * (D₁ - D₂) * evProj hH j) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, eigSum_mul_evProj, Matrix.mul_smul,
        Matrix.mul_smul, ← Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.add_mul, e1, e2, ← add_smul] at h1
    have hne : ((a (hH.eigenvalues i) : ℝ) : ℂ) + ((a (hH.eigenvalues j) : ℝ) : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_add]
      exact_mod_cast (add_pos (ha i) (ha j)).ne'
    exact (smul_eq_zero.mp h1).resolve_left hne
  have hD : D₁ - D₂ = 0 := by
    calc D₁ - D₂ = (∑ i, evProj hH i) * (D₁ - D₂) * (∑ j, evProj hH j) := by
          rw [sum_evProj, Matrix.one_mul, Matrix.mul_one]
      _ = ∑ i, ∑ j, evProj hH i * (D₁ - D₂) * evProj hH j := by
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ = 0 := by simp [key]
  exact sub_eq_zero.mp hD

private lemma eigenvalues_ne_of_isUnit (hH : H.IsHermitian) {c : ℝ}
    (hu : IsUnit (H - ((c : ℝ) : ℂ) • 1)) (k : Fin W) : hH.eigenvalues k ≠ c := by
  intro hk
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hu
  have h1 : (H - ((c : ℝ) : ℂ) • 1) *ᵥ ⇑(hH.eigenvectorBasis k) =
      (H - ((c : ℝ) : ℂ) • 1) *ᵥ 0 := by
    rw [eigSum_sub_const hH c, eigSum_mulVec, hk, Matrix.mulVec_zero]
    simp
  have h2 := evDot hH k k
  rw [hinj h1] at h2
  simp at h2

private lemma reg_contDiffAt_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {f : E → Matrix (Fin W) (Fin W) ℂ} {x : E} (hf : ContDiffAt ℝ n f x)
    (hu : IsUnit (f x)) : ContDiffAt ℝ n (fun y => (f y)⁻¹) x := by
  have h1 := contDiffAt_ringInverse ℝ (n := n) hu.unit
  rw [hu.unit_spec] at h1
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  exact h1.comp x hf

open scoped MatrixOrder ComplexOrder in
/-- If `H` is smooth with Hermitian values and `c` is not an eigenvalue of `H(x)`, then
`1_{(c, ∞)}(H)` is smooth at `x`. -/
private lemma contDiffAt_specProj_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} (hn : n ≠ 0) {Hf : E → Matrix (Fin W) (Fin W) ℂ} {x : E} (c : ℝ)
    (hd : ContDiffAt ℝ n Hf x) (hh : ∀ y, (Hf y).IsHermitian)
    (hu : IsUnit (Hf x - ((c : ℝ) : ℂ) • 1)) :
    ContDiffAt ℝ n (fun y => specProj (Hf y) (Set.Ioi c)) x := by
  set X : E → Matrix (Fin W) (Fin W) ℂ := fun y => Hf y - ((c : ℝ) : ℂ) • 1 with hXdef
  set Rf : E → Matrix (Fin W) (Fin W) ℂ :=
    fun y => X y * ((2 : ℂ) • specProj (Hf y) (Set.Ioi c) - 1) with hRdef
  have hXe : ∀ y, X y = eigSum (hh y) (fun z => z - c) := fun y => eigSum_sub_const (hh y) c
  have hRe : ∀ y, Rf y = eigSum (hh y) (fun z => |z - c|) := fun y => by
    simp only [hRdef, hXe y, specProj_eigSum (hh y)]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, eigSum_smul, ← eigSum_one (hh y), eigSum_sub,
      eigSum_mul]
    congr 1
    funext z
    by_cases hz : z ∈ Set.Ioi c
    · simp only [hz, ↓reduceIte]
      rw [abs_of_pos (sub_pos.mpr hz)]
      ring
    · simp only [hz, ↓reduceIte]
      rw [abs_of_nonpos (by simpa using hz)]
      ring
  have hRpsd : ∀ y, 0 ≤ Rf y := fun y => by
    rw [hRe y]
    exact Matrix.nonneg_iff_posSemidef.mpr (eigSum_posSemidef _ fun z => abs_nonneg _)
  have hRsq : ∀ y, Rf y * Rf y = X y * X y := fun y => by
    rw [hRe y, hXe y, eigSum_mul, eigSum_mul]
    congr 1
    funext z
    exact abs_mul_abs_self _
  have hsqrt : ∀ y, CFC.sqrt (X y * X y) = Rf y := fun y => by
    rw [← hRsq y, ← sq]
    exact CFC.sqrt_sq _ (hRpsd y)
  have hYnn : ∀ y, 0 ≤ X y * X y := fun y => by
    rw [← hRsq y]
    have hs : star (Rf y) = Rf y := by
      rw [Matrix.star_eq_conjTranspose]
      exact (Matrix.nonneg_iff_posSemidef.mp (hRpsd y)).1.eq
    have := star_mul_self_nonneg (Rf y)
    rwa [hs] at this
  have hXd : ContDiffAt ℝ n X x := hd.sub contDiffAt_const
  have hYd : ContDiffAt ℝ n (fun y => X y * X y) x := hXd.mul hXd
  have hRc : ContinuousAt Rf x := by
    have h1 : Rf = fun y => CFC.sqrt (X y * X y) := funext fun y => (hsqrt y).symm
    rw [h1]
    have h2 := CFC.continuousOn_sqrt (A := Matrix (Fin W) (Fin W) ℂ) _ (hYnn x)
    exact h2.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hYd.continuousAt.tendsto, Filter.Eventually.of_forall hYnn⟩)
  have hpos : ∀ k, 0 < |(hh x).eigenvalues k - c| := fun k =>
    abs_pos.mpr (sub_ne_zero.mpr (eigenvalues_ne_of_isUnit (hh x) hu k))
  have hinj : Function.Injective (fun D : Matrix (Fin W) (Fin W) ℂ => Rf x * D + D * Rf x) := by
    rw [hRe x]
    exact eigSum_sq_injective (hh x) hpos
  let Lc : Matrix (Fin W) (Fin W) ℂ →L[ℝ] Matrix (Fin W) (Fin W) ℂ :=
    id (Rf x) • ContinuousLinearMap.id ℝ (Matrix (Fin W) (Fin W) ℂ) +
      MulOpposite.op (id (Rf x)) • ContinuousLinearMap.id ℝ (Matrix (Fin W) (Fin W) ℂ)
  have hLc : ∀ D, Lc D = Rf x * D + D * Rf x := fun D => by
    simp [Lc, MulOpposite.smul_eq_mul_unop]
  have hinj' :
      Function.Injective (Lc : Matrix (Fin W) (Fin W) ℂ →ₗ[ℝ] Matrix (Fin W) (Fin W) ℂ) := by
    intro D₁ D₂ h
    apply hinj
    simp only
    rw [← hLc, ← hLc]
    exact h
  let e := (LinearEquiv.ofInjectiveEndo _ hinj').toContinuousLinearEquiv
  have hΦ : ContDiffAt ℝ n (fun R : Matrix (Fin W) (Fin W) ℂ => R * R) (Rf x) :=
    contDiffAt_id.mul contDiffAt_id
  have hder : HasFDerivAt (fun R : Matrix (Fin W) (Fin W) ℂ => R * R)
      (e : Matrix (Fin W) (Fin W) ℂ →L[ℝ] Matrix (Fin W) (Fin W) ℂ) (Rf x) := by
    have h := (hasFDerivAt_id (𝕜 := ℝ) (Rf x)).mul' (hasFDerivAt_id (𝕜 := ℝ) (Rf x))
    have he : (e : Matrix (Fin W) (Fin W) ℂ →L[ℝ] Matrix (Fin W) (Fin W) ℂ) = Lc := by
      ext D : 1
      rfl
    rw [he]
    exact h
  have hg := hΦ.to_localInverse hder hn
  have hleft := (hΦ.hasStrictFDerivAt' hder hn).eventually_left_inverse
  have hev : (fun y => hΦ.localInverse hder hn (X y * X y)) =ᶠ[nhds x] Rf := by
    filter_upwards [hRc.eventually hleft] with y hy
    rw [← hRsq y]
    exact hy
  have hRd : ContDiffAt ℝ n Rf x := by
    have h1 : ContDiffAt ℝ n (fun y => hΦ.localInverse hder hn (X y * X y)) x := by
      have h3 : X x * X x = Rf x * Rf x := (hRsq x).symm
      refine ContDiffAt.comp (g := hΦ.localInverse hder hn) x ?_ hYd
      rw [h3]
      exact hg
    exact h1.congr_of_eventuallyEq hev.symm
  have hXinv := reg_contDiffAt_inv hXd hu
  have hev2 : (fun y => specProj (Hf y) (Set.Ioi c)) =ᶠ[nhds x]
      fun y => (1 / 2 : ℂ) • (1 + (X y)⁻¹ * Rf y) := by
    filter_upwards [hXd.continuousAt.eventually_mem (Units.isOpen.mem_nhds hu)] with y hy
    have hdet : IsUnit (X y).det := (Matrix.isUnit_iff_isUnit_det _).mp hy
    simp only [hRdef]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul, add_sub_cancel,
      smul_smul]
    norm_num
  exact ((contDiffAt_const.add (hXinv.mul hRd)).const_smul _).congr_of_eventuallyEq hev2

end Gap

/-! ### Conjugation by a unitary matrix

`M ↦ U M U*` for a unitary `U` respects products, sums, scalars, `1`, inverses, adjoints and the
projection `flagProj`; `U` preserves inner products of vectors. -/

section Conj

variable {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ}

private lemma conj_mul (hU : Uᴴ * U = 1) (M N : Matrix (Fin W) (Fin W) ℂ) :
    U * (M * N) * Uᴴ = U * M * Uᴴ * (U * N * Uᴴ) := by
  calc U * (M * N) * Uᴴ = U * M * (Uᴴ * U) * N * Uᴴ := by
        rw [hU, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = U * M * Uᴴ * (U * N * Uᴴ) := by simp only [Matrix.mul_assoc]

private lemma conj_add (M N : Matrix (Fin W) (Fin W) ℂ) :
    U * (M + N) * Uᴴ = U * M * Uᴴ + U * N * Uᴴ := by
  rw [Matrix.mul_add, Matrix.add_mul]

private lemma conj_sub (M N : Matrix (Fin W) (Fin W) ℂ) :
    U * (M - N) * Uᴴ = U * M * Uᴴ - U * N * Uᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul]

private lemma conj_smul (c : ℂ) (M : Matrix (Fin W) (Fin W) ℂ) :
    U * (c • M) * Uᴴ = c • (U * M * Uᴴ) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

private lemma conj_one (hU' : U * Uᴴ = 1) : U * (1 : Matrix (Fin W) (Fin W) ℂ) * Uᴴ = 1 := by
  rw [Matrix.mul_one, hU']

private lemma conj_inv (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (M : Matrix (Fin W) (Fin W) ℂ) :
    (U * M * Uᴴ)⁻¹ = U * M⁻¹ * Uᴴ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hU,
    Matrix.inv_eq_left_inv hU', Matrix.mul_assoc]

private lemma conj_conjTranspose (M : Matrix (Fin W) (Fin W) ℂ) :
    (U * M * Uᴴ)ᴴ = U * Mᴴ * Uᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

private lemma conj_herm {M : Matrix (Fin W) (Fin W) ℂ} (hM : M.IsHermitian) :
    (U * M * Uᴴ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conj_conjTranspose, hM.eq]

private lemma conj_affine (hU' : U * Uᴴ = 1) (B X : Matrix (Fin W) (Fin W) ℂ) (c d : ℂ) :
    U * B * Uᴴ - c • 1 - d • (U * X * Uᴴ) = U * (B - c • 1 - d • X) * Uᴴ := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU']

private lemma conj_mulVec (hU : Uᴴ * U = 1) (M : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) :
    (U * M * Uᴴ) *ᵥ (U *ᵥ v) = U *ᵥ (M *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (U * M), hU, Matrix.mul_one, Matrix.mulVec_mulVec]

private lemma dot_unitary (hU : Uᴴ * U = 1) (a b : Fin W → ℂ) :
    star (U *ᵥ a) ⬝ᵥ (U *ᵥ b) = star a ⬝ᵥ b := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU,
    Matrix.one_mulVec]

private lemma vecMulVec_unitary (a b : Fin W → ℂ) :
    Matrix.vecMulVec (U *ᵥ a) (star (U *ᵥ b)) = U * Matrix.vecMulVec a (star b) * Uᴴ := by
  rw [Matrix.star_mulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

private lemma dot_self_eq (a : Fin W → ℂ) : star a ⬝ᵥ a = ((∑ i, ‖a i‖ ^ 2 : ℝ) : ℂ) := by
  simp [dotProduct, Complex.conj_mul', Complex.ofReal_sum]

private lemma sum_norm_sq_unitary (hU : Uᴴ * U = 1) (a : Fin W → ℂ) :
    ∑ i, ‖(U *ᵥ a) i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
  have h := dot_unitary hU a a
  rw [dot_self_eq, dot_self_eq] at h
  exact_mod_cast h

private lemma flagProj_conj (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (T S : Matrix (Fin W) (Fin W) ℂ) :
    flagProj (U * T * Uᴴ) (U * S * Uᴴ) = U * flagProj T S * Uᴴ := by
  unfold flagProj
  simp only [conj_mul hU, conj_add, conj_sub, conj_one hU', ← conj_inv hU hU',
    ← conj_conjTranspose]

private lemma comm_of_fix {P : Matrix (Fin W) (Fin W) ℂ} (hP : P.IsHermitian) (hU : Uᴴ * U = 1)
    (hUP : U * (1 - P) = 1 - P) : P * U = U * P := by
  have h1 : Uᴴ * (1 - P) = 1 - P := by
    calc Uᴴ * (1 - P) = Uᴴ * (U * (1 - P)) := by rw [hUP]
      _ = 1 - P := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have h2 : (1 - P) * U = 1 - P := by
    have h := congrArg Matrix.conjTranspose h1
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hP.eq] at h
  have h3 : U * (1 - P) = (1 - P) * U := by rw [hUP, h2]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul] at h3
  exact (sub_right_injective h3).symm

private lemma allowProj_unitary (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    {P : Matrix (Fin W) (Fin W) ℂ} (hPU : P * U = U * P) (v : Fin W → ℂ) :
    allowProj P (U *ᵥ v) = U * allowProj P v * Uᴴ := by
  have hPv : P *ᵥ (U *ᵥ v) = U *ᵥ (P *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hPU, ← Matrix.mulVec_mulVec]
  have hcP : U * P * Uᴴ = P := by rw [← hPU, Matrix.mul_assoc, hU', Matrix.mul_one]
  unfold allowProj
  rw [hPv, dot_unitary hU, vecMulVec_unitary, conj_sub, conj_smul, hcP]

end Conj

/-! ### The construction under the change (9.24) [su:eq:cut-generator-equivariance]

For `q ≥ 7` and `U (1 - P) = 1 - P`, the change `srcAct` conjugates the blocks `5, …, q - 2` by
`U` and shifts block `4` so that `V_5 - g² R_4` is conjugated. Then `R_j`, `R←_j`, `A`, `R̃`, the
retained projection `Q`, `Π`, `K_0` and `K` are conjugated, `y ↦ U y` and `ξ` is unchanged. -/

section Equiv

variable {W q : ℕ} {g E : ℝ} {R U : Matrix (Fin W) (Fin W) ℂ}

private lemma gsq_smul_herm (g : ℝ) {M : Matrix (Fin W) (Fin W) ℂ} (hM : M.IsHermitian) :
    (((g : ℂ) ^ 2) • M).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hM.eq]
  simp

private lemma gueBlock_srcAct (hRh : R.IsHermitian) (ω : Ω W q) :
    gueBlock W q (srcAct W q g R U ω) = fun i : Fin q =>
      if (i : ℕ) = 4 then U * (gueBlock W q ω i - ((g : ℂ) ^ 2) • R) * Uᴴ + ((g : ℂ) ^ 2) • R
      else if 5 ≤ (i : ℕ) ∧ (i : ℕ) + 2 ≤ q then U * gueBlock W q ω i * Uᴴ
      else gueBlock W q ω i := by
  unfold srcAct
  refine gueBlock_gueCoord W q _ fun i => ?_
  split_ifs
  · exact (conj_herm ((gueBlock_isHermitian W q ω i).sub (gsq_smul_herm g hRh))).add
      (gsq_smul_herm g hRh)
  · exact conj_herm (gueBlock_isHermitian W q ω i)
  · exact gueBlock_isHermitian W q ω i

private lemma blockSeq_srcAct_four (hRh : R.IsHermitian) (ω : Ω W q) (hq : 4 < q) :
    blockSeq W q (srcAct W q g R U ω) 4 =
      U * (blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R) * Uᴴ + ((g : ℂ) ^ 2) • R := by
  simp only [blockSeq, hq, ↓reduceDIte, gueBlock_srcAct hRh]
  simp

private lemma blockSeq_srcAct_mid (hRh : R.IsHermitian) (ω : Ω W q) {k : ℕ} (h5 : 5 ≤ k)
    (hk : k + 2 ≤ q) : blockSeq W q (srcAct W q g R U ω) k = U * blockSeq W q ω k * Uᴴ := by
  have hkq : k < q := by omega
  have h4 : k ≠ 4 := by omega
  simp only [blockSeq, hkq, ↓reduceDIte, gueBlock_srcAct hRh]
  simp [h4, h5, hk]

private lemma chartR_succ' (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) {j : ℕ}
    (hj : 4 ≤ j) : chartR W g E q R ω (j + 1) =
      (blockSeq W q ω j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω j)⁻¹ := by
  simp [chartR, not_lt.mpr hj]

private lemma chartR_four' (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) :
    chartR W g E q R ω 4 = R := by
  simp [chartR]

private lemma chartR_srcAct (hRh : R.IsHermitian) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (ω : Ω W q) : ∀ i, 5 + i ≤ q - 1 →
      chartR W g E q R (srcAct W q g R U ω) (5 + i) = U * chartR W g E q R ω (5 + i) * Uᴴ := by
  intro i
  induction i with
  | zero =>
    intro hi
    rw [show 5 + 0 = 4 + 1 from rfl, chartR_succ' g E R _ le_rfl, chartR_succ' g E R _ le_rfl,
      chartR_four', chartR_four', blockSeq_srcAct_four hRh ω (by omega), ← conj_inv hU hU']
    congr 1
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hU']
    abel
  | succ i ih =>
    intro hi
    rw [show 5 + (i + 1) = (5 + i) + 1 by omega, chartR_succ' g E R _ (by omega),
      chartR_succ' g E R _ (by omega), blockSeq_srcAct_mid hRh ω (by omega) (by omega),
      ih (by omega), conj_affine hU', conj_inv hU hU']

private lemma chartProd_srcAct (hRh : R.IsHermitian) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (ω : Ω W q) : ∀ j, j ≤ q - 1 →
      chartProd W g E q R (srcAct W q g R U ω) j = U * chartProd W g E q R ω j * Uᴴ := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [chartProd]
    exact (conj_one hU').symm
  | succ j ih =>
    intro hj
    by_cases hj4 : j < 4
    · simp only [chartProd, hj4, ↓reduceIte]
      exact (conj_one hU').symm
    · simp only [chartProd, hj4, ↓reduceIte]
      have h5 := chartR_srcAct (g := g) (E := E) hRh hU hU' ω (j + 1 - 5) (by omega)
      rw [show 5 + (j + 1 - 5) = j + 1 by omega] at h5
      rw [h5, ih (by omega), ← conj_mul hU]

private lemma cavR_srcAct (hq : 7 ≤ q) (hRh : R.IsHermitian) (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (ω : Ω W q) : ∀ m, m ≤ q - 7 →
      cavR W g E q (srcAct W q g R U ω) m = U * cavR W g E q ω m * Uᴴ := by
  intro m
  induction m with
  | zero =>
    intro _
    simp only [cavR]
    rw [blockSeq_srcAct_mid hRh ω (by omega) (by omega), ← conj_inv hU hU']
    congr 1
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hU']
  | succ m ih =>
    intro hm
    simp only [cavR]
    rw [blockSeq_srcAct_mid hRh ω (by omega) (by omega), ih (by omega), conj_affine hU',
      conj_inv hU hU']

private lemma cavProd_srcAct (hq : 7 ≤ q) (hRh : R.IsHermitian) (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (ω : Ω W q) : ∀ m, m ≤ q - 6 →
      cavProd W g E q (srcAct W q g R U ω) m = U * cavProd W g E q ω m * Uᴴ := by
  intro m
  induction m with
  | zero =>
    intro _
    simp only [cavProd]
    exact (conj_one hU').symm
  | succ m ih =>
    intro hm
    simp only [cavProd]
    rw [ih (by omega), cavR_srcAct hq hRh hU hU' ω m (by omega), ← conj_mul hU]

private lemma cavRes_srcAct (hq : 7 ≤ q) (hRh : R.IsHermitian) (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (ω : Ω W q) :
    cavRes W g E q R (srcAct W q g R U ω) = U * cavRes W g E q R ω * Uᴴ := by
  unfold cavRes
  rw [blockSeq_srcAct_four hRh ω (by omega), cavR_srcAct hq hRh hU hU' ω (q - 7) le_rfl,
    ← conj_inv hU hU']
  congr 1
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hU']
  abel

private lemma retProj_srcAct (hq : 7 ≤ q) (hRh : R.IsHermitian) (t : ℝ)
    (hUm : U ∈ Matrix.unitaryGroup (Fin W) ℂ) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (ω : Ω W q) :
    retProj W g E q R t (srcAct W q g R U ω) = U * retProj W g E q R t ω * Uᴴ := by
  have hS : retSpec W g E q t (srcAct W q g R U ω) = U * retSpec W g E q t ω * Uᴴ := by
    unfold retSpec
    rw [cavProd_srcAct hq hRh hU hU' ω (q - 6) le_rfl, conj_conjTranspose, ← conj_mul hU,
      specProj_conj (Matrix.isHermitian_conjTranspose_mul_self _) hUm]
  unfold retProj
  rw [cavRes_srcAct hq hRh hU hU' ω, hS, flagProj_conj hU hU']

private lemma smallGen_srcAct (hq : 7 ≤ q) (hRh : R.IsHermitian) (t : ℝ)
    {P : Matrix (Fin W) (Fin W) ℂ} (hUm : U ∈ Matrix.unitaryGroup (Fin W) ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (hPU : P * U = U * P) (ω : Ω W q) (v : Fin W → ℂ) :
    smallGen W g E q R t P (srcAct W q g R U ω) (U *ᵥ v) = U * smallGen W g E q R t P ω v * Uᴴ := by
  have hQ := retProj_srcAct (g := g) (E := E) hq hRh t hUm hU hU' ω
  have hPi := allowProj_unitary hU hU' hPU v
  have hPv : P *ᵥ (U *ᵥ v) = U *ᵥ (P *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hPU, ← Matrix.mulVec_mulVec]
  have hy : srcVec W g E q R t P (srcAct W q g R U ω) (U *ᵥ v) =
      U *ᵥ srcVec W g E q R t P ω v := by
    unfold srcVec
    rw [hQ, hPi]
    have hM : U * allowProj P v * Uᴴ * (U * retProj W g E q R t ω * Uᴴ) *
        (U * retProj W g E q R t ω * Uᴴ * (U * allowProj P v * Uᴴ) *
          (U * retProj W g E q R t ω * Uᴴ) + (1 - U * retProj W g E q R t ω * Uᴴ))⁻¹ *
        (U * retProj W g E q R t ω * Uᴴ) =
        U * (allowProj P v * retProj W g E q R t ω *
          (retProj W g E q R t ω * allowProj P v * retProj W g E q R t ω +
            (1 - retProj W g E q R t ω))⁻¹ * retProj W g E q R t ω) * Uᴴ := by
      simp only [conj_mul hU, conj_add, conj_sub, conj_one hU', ← conj_inv hU hU']
    rw [hM, conj_mulVec hU]
  have hg0 : gen0 W g E q R t P (srcAct W q g R U ω) (U *ᵥ v) =
      U * gen0 W g E q R t P ω v * Uᴴ := by
    unfold gen0
    rw [hy, hPv, dot_unitary hU, vecMulVec_unitary, vecMulVec_unitary, ← conj_sub, ← conj_smul]
  have hξ : genScale W g E q R t P (srcAct W q g R U ω) (U *ᵥ v) =
      genScale W g E q R t P ω v := by
    unfold genScale
    rw [chartProd_srcAct hRh hU hU' ω (q - 1) le_rfl, hy, conj_mulVec hU, conj_mulVec hU,
      dot_unitary hU, sum_norm_sq_unitary hU]
  unfold smallGen
  rw [hξ, hg0, conj_smul]

end Equiv

/-! ### `K = 0` for `q ≤ 6`

For `q ≤ 6` the product `A` is empty, so `1_{(t², ∞)}(A* A) ∈ {0, 1}` and `Q ∈ {0, 1}`; then
`y = 0` (for `Q = 1`, `Π` kills `P v`), and `K = 0`. -/

section Small

open scoped ComplexOrder

variable {W q : ℕ} {g E : ℝ}

private lemma specProj_one_cases (T : Set ℝ) :
    specProj (1 : Matrix (Fin W) (Fin W) ℂ) T = 0 ∨
      specProj (1 : Matrix (Fin W) (Fin W) ℂ) T = 1 := by
  have h1 : (1 : Matrix (Fin W) (Fin W) ℂ).IsHermitian := Matrix.isHermitian_one
  have hev : ∀ k, h1.eigenvalues k = 1 := by
    intro k
    have h := eigSum_mulVec h1 (fun x => x) k
    rw [← eigSum_id h1, Matrix.one_mulVec] at h
    have h2 := congrArg (fun w => star ⇑(h1.eigenvectorBasis k) ⬝ᵥ w) h
    simp only [dotProduct_smul, evDot, smul_eq_mul, ↓reduceIte, mul_one] at h2
    exact_mod_cast h2.symm
  rw [specProj_eigSum h1]
  by_cases hT : (1 : ℝ) ∈ T
  · right
    unfold eigSum
    simp only [hev, hT, ↓reduceIte, Complex.ofReal_one, one_smul]
    exact sum_evProj h1
  · left
    unfold eigSum
    simp [hev, hT]

private lemma flagProj_inv_one (M : Matrix (Fin W) (Fin W) ℂ) :
    flagProj M⁻¹ 1 = 0 ∨ flagProj M⁻¹ 1 = 1 := by
  by_cases hM : IsUnit M.det
  · right
    have hT : IsUnit M⁻¹.det := Matrix.isUnit_nonsing_inv_det M hM
    have hTh : IsUnit (M⁻¹)ᴴ.det := by
      rw [Matrix.det_conjTranspose]
      exact hT.star
    unfold flagProj
    simp only [Matrix.mul_one, Matrix.one_mul, sub_self, add_zero]
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hTh]
  · left
    rw [Matrix.nonsing_inv_apply_not_isUnit M hM]
    simp [flagProj]

private lemma retProj_cases (hq : q ≤ 6) (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ) (ω : Ω W q) :
    retProj W g E q R t ω = 0 ∨ retProj W g E q R t ω = 1 := by
  have hA : cavProd W g E q ω (q - 6) = 1 := by
    rw [show q - 6 = 0 by omega]
    rfl
  have hS : retSpec W g E q t ω = 0 ∨ retSpec W g E q t ω = 1 := by
    unfold retSpec
    rw [hA, Matrix.conjTranspose_one, Matrix.mul_one]
    exact specProj_one_cases _
  unfold retProj
  rcases hS with h | h <;> rw [h]
  · left
    simp [flagProj]
  · unfold cavRes
    exact flagProj_inv_one _

private lemma allowProj_mulVec {P : Matrix (Fin W) (Fin W) ℂ} (hPP : P * P = P) (v : Fin W → ℂ)
    (hu : P *ᵥ v ≠ 0) : allowProj P v *ᵥ (P *ᵥ v) = 0 := by
  have hs : star (P *ᵥ v) ⬝ᵥ (P *ᵥ v) ≠ 0 := fun h => hu (dotProduct_star_self_eq_zero.mp h)
  unfold allowProj
  rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, hPP, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul, inv_mul_cancel₀ hs, one_smul, sub_self]

private lemma smallGen_eq_zero_of_le (hq : q ≤ 6) (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ)
    {P : Matrix (Fin W) (Fin W) ℂ} (hPP : P * P = P) (ω : Ω W q) (v : Fin W → ℂ) :
    smallGen W g E q R t P ω v = 0 := by
  have hg : gen0 W g E q R t P ω v = 0 := by
    by_cases hu : P *ᵥ v = 0
    · unfold gen0
      rw [hu]
      simp
    · have hPi : ¬ IsUnit (allowProj P v).det := by
        intro hd
        apply hu
        have h1 : (allowProj P v)⁻¹ *ᵥ (allowProj P v *ᵥ (P *ᵥ v)) = P *ᵥ v := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]
        rw [allowProj_mulVec hPP v hu, Matrix.mulVec_zero] at h1
        exact h1.symm
      have hy : srcVec W g E q R t P ω v = 0 := by
        unfold srcVec
        rcases retProj_cases (g := g) (E := E) hq R t ω with h | h <;> rw [h]
        · simp
        · simp only [Matrix.mul_one, Matrix.one_mul, sub_self, add_zero]
          rw [Matrix.nonsing_inv_apply_not_isUnit _ hPi]
          simp
      unfold gen0
      rw [hy]
      simp
  unfold smallGen
  rw [hg, smul_zero]

/-- Degree-zero homogeneity of `K` in the source `v`, for every `q`. -/
private lemma smallGen_smul_src (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ)
    (P : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) (v : Fin W → ℂ) {a : ℂ} (ha : a ≠ 0) :
    smallGen W g E q R t P ω (a • v) = smallGen W g E q R t P ω v := by
  have hk : star a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  have hr : (0 : ℝ) < ‖a‖ ^ 2 := by
    have := norm_pos_iff.mpr ha
    positivity
  have hk0 : star a * a ≠ 0 := by
    rw [hk]
    exact_mod_cast hr.ne'
  have hu : P *ᵥ (a • v) = a • (P *ᵥ v) := Matrix.mulVec_smul _ _ _
  have hs : ∀ x y : Fin W → ℂ, star (a • x) ⬝ᵥ (a • y) = (star a * a) * (star x ⬝ᵥ y) := by
    intro x y
    rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, mul_assoc]
  have hvv : ∀ x y : Fin W → ℂ, Matrix.vecMulVec (a • x) (star (a • y)) =
      (star a * a) • Matrix.vecMulVec x (star y) := by
    intro x y
    rw [star_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, mul_comm]
  have hinv : ∀ s : ℂ, (star a * a * s)⁻¹ * (star a * a) = s⁻¹ := fun s => by
    rw [mul_inv, mul_comm (star a * a)⁻¹, mul_assoc, inv_mul_cancel₀ hk0, mul_one]
  have hPi : allowProj P (a • v) = allowProj P v := by
    unfold allowProj
    rw [hu, hs, hvv, smul_smul, hinv]
  have hy : srcVec W g E q R t P ω (a • v) = a • srcVec W g E q R t P ω v := by
    unfold srcVec
    rw [hPi, Matrix.mulVec_smul]
  have hg : gen0 W g E q R t P ω (a • v) = gen0 W g E q R t P ω v := by
    unfold gen0
    rw [hy, hu, hs, hvv, hvv, ← smul_sub, smul_smul, hinv]
  have hξ : genScale W g E q R t P ω (a • v) = genScale W g E q R t P ω v := by
    unfold genScale
    rw [hy, Matrix.mulVec_smul, Matrix.mulVec_smul, hs, hk, Complex.re_ofReal_mul]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
    exact mul_div_mul_left _ _ hr.ne'
  unfold smallGen
  rw [hξ, hg]

end Small

/-- Lemma 9.3 [su:lem:chosen-generator](ii) for the construction: equivariance under the change
(9.24) [su:eq:cut-generator-equivariance] by a unitary `U` with `U (1 - P) = 1 - P`, and
homogeneity of degree zero in the source. -/
theorem smallGen_equivariant {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hRh : R.IsHermitian) (t : ℝ) {P : Matrix (Fin W) (Fin W) ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (ω : Ω W q) (v : Fin W → ℂ) :
    (∀ U ∈ Matrix.unitaryGroup (Fin W) ℂ, U * (1 - P) = 1 - P →
      smallGen W g E q R t P (srcAct W q g R U ω) (U *ᵥ v) =
        U * smallGen W g E q R t P ω v * Uᴴ) ∧
    ∀ a : ℂ, a ≠ 0 → smallGen W g E q R t P ω (a • v) = smallGen W g E q R t P ω v := by
  refine ⟨fun U hU hUP => ?_, fun a ha => smallGen_smul_src R t P ω v ha⟩
  have hU1 : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have hU2 : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hU
  by_cases hq : q ≤ 6
  · rw [smallGen_eq_zero_of_le hq R t hPP, smallGen_eq_zero_of_le hq R t hPP]
    simp
  · exact smallGen_srcAct (by omega) hRh t hU hU1 hU2 (comm_of_fix hP hU1 hUP) ω v

/-! ### Smoothness of the construction

A matrix-valued map is smooth when its entries are; matrix–vector products, adjoints, inverses at
units and the spectral projection at a gap (`contDiffAt_specProj_Ioi`) keep smoothness. Every
ingredient of `K` is smooth at each point of `genGood`. -/

section Smooth

open scoped ComplexOrder

variable {W : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞}

private lemma cd_matrix {f : F → Matrix (Fin W) (Fin W) ℂ} {x : F}
    (h : ∀ i j, ContDiffAt ℝ n (fun y => f y i j) x) : ContDiffAt ℝ n f x := by
  let L : (Fin W → Fin W → ℂ) →ₗ[ℝ] Matrix (Fin W) (Fin W) ℂ :=
    { toFun := Matrix.of, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hp : ContDiffAt ℝ n (fun y => fun i j => f y i j) x :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => h i j
  exact (LinearMap.toContinuousLinearMap L).contDiff.contDiffAt.comp x hp

private lemma cd_entry {f : F → Matrix (Fin W) (Fin W) ℂ} {x : F} (hf : ContDiffAt ℝ n f x)
    (i j : Fin W) : ContDiffAt ℝ n (fun y => f y i j) x := by
  let L : Matrix (Fin W) (Fin W) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).contDiff.contDiffAt.comp x hf

private lemma cd_conjTranspose {f : F → Matrix (Fin W) (Fin W) ℂ} {x : F}
    (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun y => (f y)ᴴ) x := by
  let L : Matrix (Fin W) (Fin W) ℂ →ₗ[ℝ] Matrix (Fin W) (Fin W) ℂ :=
    { toFun := fun M => Mᴴ, map_add' := Matrix.conjTranspose_add,
      map_smul' := fun r M => by simp [Matrix.conjTranspose_smul] }
  exact (LinearMap.toContinuousLinearMap L).contDiff.contDiffAt.comp x hf

private lemma cd_star {g : F → Fin W → ℂ} {x : F} (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun y => star (g y)) x := by
  refine contDiffAt_pi.2 fun i => ?_
  have h : (fun y => star (g y) i) = fun y => Complex.conjCLE (g y i) := funext fun y => by simp
  rw [h]
  exact Complex.conjCLE.contDiff.contDiffAt.comp x (contDiffAt_pi.1 hg i)

private lemma cd_mulVec {f : F → Matrix (Fin W) (Fin W) ℂ} {g : F → Fin W → ℂ} {x : F}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun y => f y *ᵥ g y) x := by
  refine contDiffAt_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiffAt.sum fun j _ => (cd_entry hf i j).mul (contDiffAt_pi.1 hg j)

private lemma cd_dot {a b : F → Fin W → ℂ} {x : F} (ha : ContDiffAt ℝ n a x)
    (hb : ContDiffAt ℝ n b x) : ContDiffAt ℝ n (fun y => a y ⬝ᵥ b y) x := by
  simp only [dotProduct]
  exact ContDiffAt.sum fun j _ => (contDiffAt_pi.1 ha j).mul (contDiffAt_pi.1 hb j)

private lemma cd_vecMulVec {a b : F → Fin W → ℂ} {x : F} (ha : ContDiffAt ℝ n a x)
    (hb : ContDiffAt ℝ n b x) : ContDiffAt ℝ n (fun y => Matrix.vecMulVec (a y) (b y)) x :=
  cd_matrix fun i j => by
    simp only [Matrix.vecMulVec_apply]
    exact (contDiffAt_pi.1 ha i).mul (contDiffAt_pi.1 hb j)

private lemma cd_allowProj {P : Matrix (Fin W) (Fin W) ℂ} {v : F → Fin W → ℂ} {x : F}
    (hv : ContDiffAt ℝ n v x) (h0 : P *ᵥ v x ≠ 0) :
    ContDiffAt ℝ n (fun y => allowProj P (v y)) x := by
  have hu : ContDiffAt ℝ n (fun y => P *ᵥ v y) x := cd_mulVec contDiffAt_const hv
  have hs : ContDiffAt ℝ n (fun y => star (P *ᵥ v y) ⬝ᵥ (P *ᵥ v y)) x := cd_dot (cd_star hu) hu
  have hs0 : star (P *ᵥ v x) ⬝ᵥ (P *ᵥ v x) ≠ 0 := fun h => h0 (dotProduct_star_self_eq_zero.mp h)
  unfold allowProj
  exact contDiffAt_const.sub ((hs.inv hs0).smul (cd_vecMulVec hu (cd_star hu)))

private lemma isUnit_gram {T S : Matrix (Fin W) (Fin W) ℂ} (hT : IsUnit T) (hS : S.IsHermitian)
    (hSS : S * S = S) : IsUnit (S * Tᴴ * T * S + (1 - S)) := by
  refine Matrix.mulVec_injective_iff_isUnit.mp fun a b hab => ?_
  have hw : (S * Tᴴ * T * S + (1 - S)) *ᵥ (a - b) = 0 := by
    rw [Matrix.mulVec_sub, hab, sub_self]
  have hSM : S * (S * Tᴴ * T * S + (1 - S)) = S * Tᴴ * T * S := by
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, hSS, sub_self, add_zero]
    simp only [← Matrix.mul_assoc, hSS]
  have h1 : (S * Tᴴ * T * S) *ᵥ (a - b) = 0 := by
    rw [← hSM, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  have hTS : S * Tᴴ * T * S = (T * S)ᴴ * (T * S) := by
    rw [Matrix.conjTranspose_mul, hS.eq]
    simp only [Matrix.mul_assoc]
  have h3 : star ((T * S) *ᵥ (a - b)) ⬝ᵥ ((T * S) *ᵥ (a - b)) = 0 := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← hTS, h1,
      dotProduct_zero]
  have h4 := dotProduct_star_self_eq_zero.mp h3
  rw [← Matrix.mulVec_mulVec] at h4
  have hSw : S *ᵥ (a - b) = 0 :=
    (Matrix.mulVec_injective_iff_isUnit.mpr hT) (by rw [h4, Matrix.mulVec_zero])
  have hMw : (S * Tᴴ * T * S + (1 - S)) *ᵥ (a - b) = a - b := by
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hSw, sub_zero,
      ← Matrix.mulVec_mulVec, hSw, Matrix.mulVec_zero, zero_add]
  rw [hMw] at hw
  exact sub_eq_zero.mp hw

variable {q : ℕ}

private lemma cd_blockSeq (k : ℕ) : ContDiff ℝ n (fun ω : Ω W q => blockSeq W q ω k) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  unfold blockSeq
  by_cases hk : k < q
  · simp only [hk, ↓reduceDIte]
    refine cd_matrix fun α β => ?_
    have hc : ∀ p : Fin q × Fin W × Fin W, ContDiff ℝ n (fun ω : Ω W q => ((ω p : ℝ) : ℂ)) :=
      fun p => Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin q × Fin W × Fin W => ℝ) p).contDiff
    simp only [gueBlock, Matrix.of_apply]
    split_ifs
    · exact ((hc _).div_const _).contDiffAt
    · exact (((hc _).add (contDiff_const.mul (hc _))).div_const _).contDiffAt
    · exact (((hc _).sub (contDiff_const.mul (hc _))).div_const _).contDiffAt
  · simp only [hk, ↓reduceDIte]
    exact contDiffAt_const

private lemma cd_chartR (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (x : Ω W q) :
    ∀ j, (∀ i, 5 ≤ i → i ≤ j → IsUnit (chartR W g E q R x i)) →
      ContDiffAt ℝ n (fun ω => chartR W g E q R ω j) x
  | 0, _ => by
    simp only [chartR]
    exact contDiffAt_const
  | j + 1, h => by
    by_cases hj : j < 4
    · simp only [chartR, hj, ↓reduceIte]
      exact contDiffAt_const
    · have hj' : 4 ≤ j := not_lt.mp hj
      have he : (fun ω => chartR W g E q R ω (j + 1)) = fun ω =>
          (blockSeq W q ω j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω j)⁻¹ :=
        funext fun ω => chartR_succ' g E R ω hj'
      have hu : IsUnit (blockSeq W q x j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R x j) := by
        have h1 := h (j + 1) (by omega) le_rfl
        rw [chartR_succ' g E R x hj'] at h1
        exact Matrix.isUnit_nonsing_inv_iff.mp h1
      rw [he]
      exact reg_contDiffAt_inv (((cd_blockSeq j).contDiffAt.sub contDiffAt_const).sub
        ((cd_chartR g E R x j fun i h5 hi => h i h5 (by omega)).const_smul _)) hu

private lemma cd_chartProd (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (x : Ω W q)
    (h : ∀ i, 5 ≤ i → i ≤ q - 1 → IsUnit (chartR W g E q R x i)) :
    ∀ j, j ≤ q - 1 → ContDiffAt ℝ n (fun ω => chartProd W g E q R ω j) x
  | 0, _ => by
    simp only [chartProd]
    exact contDiffAt_const
  | j + 1, hj => by
    by_cases hj4 : j < 4
    · simp only [chartProd, hj4, ↓reduceIte]
      exact contDiffAt_const
    · simp only [chartProd, hj4, ↓reduceIte]
      exact (cd_chartR g E R x (j + 1) fun i h5 hi => h i h5 (by omega)).mul
        (cd_chartProd g E R x h j (by omega))

private lemma cd_cavR (g E : ℝ) (x : Ω W q) (h : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q x m)) :
    ∀ m, m ≤ q - 7 → ContDiffAt ℝ n (fun ω => cavR W g E q ω m) x
  | 0, _ => by
    have hu : IsUnit (blockSeq W q x (q - 2) - (E : ℂ) • 1) :=
      Matrix.isUnit_nonsing_inv_iff.mp (h 0 (Nat.zero_le _))
    simp only [cavR]
    exact reg_contDiffAt_inv ((cd_blockSeq _).contDiffAt.sub contDiffAt_const) hu
  | m + 1, hm => by
    have hu : IsUnit (blockSeq W q x (q - 3 - m) - (E : ℂ) • 1 -
        ((g : ℂ) ^ 2) • cavR W g E q x m) :=
      Matrix.isUnit_nonsing_inv_iff.mp (h (m + 1) hm)
    simp only [cavR]
    exact reg_contDiffAt_inv (((cd_blockSeq _).contDiffAt.sub contDiffAt_const).sub
      ((cd_cavR g E x h m (by omega)).const_smul _)) hu

private lemma cd_cavProd (g E : ℝ) (x : Ω W q) (h : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q x m)) :
    ∀ m, m ≤ q - 6 → ContDiffAt ℝ n (fun ω => cavProd W g E q ω m) x
  | 0, _ => by
    simp only [cavProd]
    exact contDiffAt_const
  | m + 1, hm => by
    simp only [cavProd]
    exact (cd_cavProd g E x h m (by omega)).mul (cd_cavR g E x h m (by omega))

private lemma cd_cavRes (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (x : Ω W q)
    (h : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q x m)) (hT : IsUnit (cavRes W g E q R x)) :
    ContDiffAt ℝ n (fun ω => cavRes W g E q R ω) x := by
  unfold cavRes at hT ⊢
  exact reg_contDiffAt_inv ((((cd_blockSeq 4).contDiffAt.sub contDiffAt_const).sub
    contDiffAt_const).sub ((cd_cavR g E x h (q - 7) le_rfl).const_smul _))
    (Matrix.isUnit_nonsing_inv_iff.mp hT)

private lemma cd_retProj {g E t : ℝ} {R : Matrix (Fin W) (Fin W) ℂ} {x : Ω W q} (hn : n ≠ 0)
    (h2 : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q x m)) (h3 : IsUnit (cavRes W g E q R x))
    (h4 : IsUnit ((cavProd W g E q x (q - 6))ᴴ * cavProd W g E q x (q - 6) -
      ((t ^ 2 : ℝ) : ℂ) • 1)) :
    ContDiffAt ℝ n (fun ω => retProj W g E q R t ω) x := by
  have hA := cd_cavProd (n := n) g E x h2 (q - 6) le_rfl
  have hS : ContDiffAt ℝ n (fun ω => retSpec W g E q t ω) x :=
    contDiffAt_specProj_Ioi hn (t ^ 2) ((cd_conjTranspose hA).mul hA)
      (fun y => Matrix.isHermitian_conjTranspose_mul_self _) h4
  have hT := cd_cavRes (n := n) g E R x h2 h3
  obtain ⟨hSh, hSS, -, -⟩ := specProj_spec
    (Matrix.isHermitian_conjTranspose_mul_self (cavProd W g E q x (q - 6))) (Set.Ioi (t ^ 2))
  have hG := isUnit_gram h3 hSh hSS
  unfold retProj flagProj
  exact (((hT.mul hS).mul (reg_contDiffAt_inv ((((hS.mul (cd_conjTranspose hT)).mul hT).mul
    hS).add (contDiffAt_const.sub hS)) hG)).mul hS).mul (cd_conjTranspose hT)

private lemma cd_parts {g E t : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {p : Ω W q × (Fin W → ℂ)} (hp : p ∈ genGood W g E q R t P) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Ω W q × (Fin W → ℂ) =>
      retProj W g E q R t y.1 * allowProj P y.2 * retProj W g E q R t y.1 +
        (1 - retProj W g E q R t y.1)) p ∧
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Ω W q × (Fin W → ℂ) => genScale W g E q R t P y.1 y.2) p ∧
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Ω W q × (Fin W → ℂ) => smallGen W g E q R t P y.1 y.2) p := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hp
  have hQ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Ω W q × (Fin W → ℂ) => retProj W g E q R t y.1) p :=
    (cd_retProj (by simp) h2 h3 h4).comp p contDiffAt_fst
  have hv : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Ω W q × (Fin W → ℂ) => y.2) p :=
    contDiffAt_snd
  have hPi := cd_allowProj (P := P) hv h5
  have hG := ((hQ.mul hPi).mul hQ).add
    ((contDiffAt_const (c := (1 : Matrix (Fin W) (Fin W) ℂ))).sub hQ)
  have hy : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Ω W q × (Fin W → ℂ) => srcVec W g E q R t P y.1 y.2) p := by
    unfold srcVec
    exact cd_mulVec (((hPi.mul hQ).mul (reg_contDiffAt_inv hG h6)).mul hQ) hv
  have hu := cd_mulVec (contDiffAt_const (c := P)) hv
  have hs := cd_dot (cd_star hu) hu
  have hs0 : star (P *ᵥ p.2) ⬝ᵥ (P *ᵥ p.2) ≠ 0 := fun h => h5 (dotProduct_star_self_eq_zero.mp h)
  have hg0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Ω W q × (Fin W → ℂ) => gen0 W g E q R t P y.1 y.2) p := by
    unfold gen0
    exact (hs.inv hs0).smul ((cd_vecMulVec hy (cd_star hu)).sub (cd_vecMulVec hu (cd_star hy)))
  have hC : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Ω W q × (Fin W → ℂ) => chartProd W g E q R y.1 (q - 1)) p :=
    (cd_chartProd g E R p.1 h1 (q - 1) le_rfl).comp p contDiffAt_fst
  have hCv := cd_mulVec hC hv
  have hCy := cd_mulVec hC hy
  have hnum := Complex.reCLM.contDiff.contDiffAt.comp p (cd_dot (cd_star hCv) hCy)
  have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Ω W q × (Fin W → ℂ) =>
      ∑ i, ‖(chartProd W g E q R y.1 (q - 1) *ᵥ y.2) i‖ ^ 2) p :=
    ContDiffAt.sum fun i _ => (contDiff_norm_sq ℝ).contDiffAt.comp p (contDiffAt_pi.1 hCv i)
  have hden0 : (∑ i, ‖(chartProd W g E q R p.1 (q - 1) *ᵥ p.2) i‖ ^ 2) ≠ 0 := by
    intro h
    apply h7
    unfold genScale
    rw [h, div_zero]
  have hξ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Ω W q × (Fin W → ℂ) => genScale W g E q R t P y.1 y.2) p := by
    unfold genScale
    exact hnum.div hden hden0
  refine ⟨hG, hξ, ?_⟩
  unfold smallGen
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p (hξ.inv h7)).smul hg0

end Smooth

/-- The set `genGood` is open, and `(ω, v) ↦ K` is smooth on it. -/
theorem contDiffOn_smallGen (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ)
    (P : Matrix (Fin W) (Fin W) ℂ) :
    IsOpen (genGood W g E q R t P) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : Ω W q × (Fin W → ℂ) => smallGen W g E q R t P p.1 p.2)
        (genGood W g E q R t P) := by
  refine ⟨?_, fun p hp => (cd_parts hp).2.2.contDiffWithinAt⟩
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨hG, hξ, -⟩ := cd_parts hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hp
  have e1 : ∀ᶠ y in nhds p, ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R y.1 j) := by
    have h : ∀ᶠ y in nhds p, ∀ j ∈ Finset.range q, 5 ≤ j → j ≤ q - 1 →
        IsUnit (chartR W g E q R y.1 j) := by
      rw [Filter.eventually_all_finset]
      intro j _
      by_cases hj : 5 ≤ j ∧ j ≤ q - 1
      · have hc := ((cd_chartR (n := 0) g E R p.1 j fun i h5 hi => h1 i h5 (by omega)).comp p
          contDiffAt_fst).continuousAt
        filter_upwards [hc.eventually_mem (Units.isOpen.mem_nhds (h1 j hj.1 hj.2))] with y hy
        exact fun _ _ => hy
      · exact Filter.Eventually.of_forall fun y h5 hq => absurd ⟨h5, hq⟩ hj
    filter_upwards [h] with y hy j h5 hq
    exact hy j (Finset.mem_range.mpr (by omega)) h5 hq
  have e2 : ∀ᶠ y in nhds p, ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q y.1 m) := by
    have h : ∀ᶠ y in nhds p, ∀ m ∈ Finset.range (q - 7 + 1), IsUnit (cavR W g E q y.1 m) := by
      rw [Filter.eventually_all_finset]
      intro m hm
      have hm' : m ≤ q - 7 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hc := ((cd_cavR (n := 0) g E p.1 h2 m hm').comp p contDiffAt_fst).continuousAt
      filter_upwards [hc.eventually_mem (Units.isOpen.mem_nhds (h2 m hm'))] with y hy
      exact hy
    filter_upwards [h] with y hy m hm
    exact hy m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  have e3 : ∀ᶠ y in nhds p, IsUnit (cavRes W g E q R y.1) := by
    have hc := ((cd_cavRes (n := 0) g E R p.1 h2 h3).comp p contDiffAt_fst).continuousAt
    exact hc.eventually_mem (Units.isOpen.mem_nhds h3)
  have e4 : ∀ᶠ y in nhds p, IsUnit ((cavProd W g E q y.1 (q - 6))ᴴ * cavProd W g E q y.1 (q - 6) -
      ((t ^ 2 : ℝ) : ℂ) • 1) := by
    have hA := cd_cavProd (n := 0) g E p.1 h2 (q - 6) le_rfl
    have hc := ((((cd_conjTranspose hA).mul hA).sub
      (contDiffAt_const (c := ((t ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)))).comp p
      contDiffAt_fst).continuousAt
    exact hc.eventually_mem (Units.isOpen.mem_nhds h4)
  have e5 : ∀ᶠ y in nhds p, P *ᵥ y.2 ≠ 0 :=
    (cd_mulVec (n := 0) (contDiffAt_const (c := P)) contDiffAt_snd).continuousAt.eventually_ne h5
  have e6 := hG.continuousAt.eventually_mem (Units.isOpen.mem_nhds h6)
  have e7 := hξ.continuousAt.eventually_ne h7
  filter_upwards [e1, e2, e3, e4, e5, e6, e7] with y y1 y2 y3 y4 y5 y6 y7
  exact ⟨y1, y2, y3, y4, y5, y6, y7⟩

/-! ### Measurability of the construction

The total inverse `M⁻¹ = det(M)⁻¹ adj(M)` is measurable, and so are products, adjoints and
matrix–vector products of measurable maps; `1_{(t², ∞)}(A* A) = 1 - 1_{(-∞, t²]}(A* A)` is
measurable since `(-∞, t²]` is closed. -/

section Meas

variable {W q : ℕ} {α : Type*} [MeasurableSpace α]

private lemma meas_inv : Measurable (fun M : Matrix (Fin W) (Fin W) ℂ => M⁻¹) := by
  have h : (fun M : Matrix (Fin W) (Fin W) ℂ => M⁻¹) = fun M => Ring.inverse M.det • M.adjugate :=
    funext Matrix.inv_def
  rw [h, Ring.inverse_eq_inv']
  exact ((Continuous.matrix_det continuous_id).measurable.inv).smul
    (Continuous.matrix_adjugate continuous_id).measurable

private lemma meas_conjTranspose {f : α → Matrix (Fin W) (Fin W) ℂ} (hf : Measurable f) :
    Measurable (fun y => (f y)ᴴ) :=
  continuous_star.measurable.comp hf

private lemma meas_mulVec {f : α → Matrix (Fin W) (Fin W) ℂ} {v : α → Fin W → ℂ}
    (hf : Measurable f) (hv : Measurable v) : Measurable (fun y => f y *ᵥ v y) :=
  (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp (hf.prodMk hv)

private lemma meas_vecMulVec {a b : α → Fin W → ℂ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun y => Matrix.vecMulVec (a y) (b y)) :=
  (Continuous.matrix_vecMulVec continuous_fst continuous_snd).measurable.comp (ha.prodMk hb)

private lemma meas_dot {a b : α → Fin W → ℂ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun y => a y ⬝ᵥ b y) :=
  (Continuous.dotProduct continuous_fst continuous_snd).measurable.comp (ha.prodMk hb)

private lemma meas_star {a : α → Fin W → ℂ} (ha : Measurable a) :
    Measurable (fun y => star (a y)) :=
  continuous_star.measurable.comp ha

private lemma meas_const_smul (c : ℂ) {f : α → Matrix (Fin W) (Fin W) ℂ} (hf : Measurable f) :
    Measurable (fun y => c • f y) :=
  hf.const_smul c

private lemma meas_flagProj {T S : α → Matrix (Fin W) (Fin W) ℂ} (hT : Measurable T)
    (hS : Measurable S) : Measurable (fun y => flagProj (T y) (S y)) := by
  unfold flagProj
  exact (((hT.mul hS).mul (meas_inv.comp ((((hS.mul (meas_conjTranspose hT)).mul hT).mul
    hS).add (measurable_const.sub hS)))).mul hS).mul (meas_conjTranspose hT)

private lemma meas_blockSeq {ω : α → Ω W q} (hω : Measurable ω) (k : ℕ) :
    Measurable (fun y => blockSeq W q (ω y) k) :=
  (cd_blockSeq (n := 0) k).continuous.measurable.comp hω

private lemma meas_chartR (g E : ℝ) {R : α → Matrix (Fin W) (Fin W) ℂ} {ω : α → Ω W q}
    (hR : Measurable R) (hω : Measurable ω) :
    ∀ j, Measurable (fun y => chartR W g E q (R y) (ω y) j)
  | 0 => by
    simp only [chartR]
    exact hR
  | j + 1 => by
    by_cases hj : j < 4
    · simp only [chartR, hj, ↓reduceIte]
      exact hR
    · simp only [chartR, hj, ↓reduceIte]
      exact meas_inv.comp (((meas_blockSeq hω j).sub measurable_const).sub
        (meas_const_smul _ (meas_chartR g E hR hω j)))

private lemma meas_chartProd (g E : ℝ) {R : α → Matrix (Fin W) (Fin W) ℂ} {ω : α → Ω W q}
    (hR : Measurable R) (hω : Measurable ω) :
    ∀ j, Measurable (fun y => chartProd W g E q (R y) (ω y) j)
  | 0 => by
    simp only [chartProd]
    exact measurable_const
  | j + 1 => by
    by_cases hj : j < 4
    · simp only [chartProd, hj, ↓reduceIte]
      exact measurable_const
    · simp only [chartProd, hj, ↓reduceIte]
      exact (meas_chartR g E hR hω (j + 1)).mul (meas_chartProd g E hR hω j)

private lemma meas_cavR (g E : ℝ) {ω : α → Ω W q} (hω : Measurable ω) :
    ∀ m, Measurable (fun y => cavR W g E q (ω y) m)
  | 0 => by
    simp only [cavR]
    exact meas_inv.comp ((meas_blockSeq hω _).sub measurable_const)
  | m + 1 => by
    simp only [cavR]
    exact meas_inv.comp (((meas_blockSeq hω _).sub measurable_const).sub
      (meas_const_smul _ (meas_cavR g E hω m)))

private lemma meas_cavProd (g E : ℝ) {ω : α → Ω W q} (hω : Measurable ω) :
    ∀ m, Measurable (fun y => cavProd W g E q (ω y) m)
  | 0 => by
    simp only [cavProd]
    exact measurable_const
  | m + 1 => by
    simp only [cavProd]
    exact (meas_cavProd g E hω m).mul (meas_cavR g E hω m)

private lemma meas_retProj (g E t : ℝ) {R : α → Matrix (Fin W) (Fin W) ℂ} {ω : α → Ω W q}
    (hR : Measurable R) (hω : Measurable ω) :
    Measurable (fun y => retProj W g E q (R y) t (ω y)) := by
  have hA := meas_cavProd g E hω (q - 6)
  have hS : Measurable (fun y => retSpec W g E q t (ω y)) := by
    have h : (fun y => retSpec W g E q t (ω y)) = fun y =>
        1 - specProj ((cavProd W g E q (ω y) (q - 6))ᴴ * cavProd W g E q (ω y) (q - 6))
          (Set.Iic (t ^ 2)) := by
      funext y
      have hs := (specProj_add_compl (Matrix.isHermitian_conjTranspose_mul_self
        (cavProd W g E q (ω y) (q - 6))) (Set.Ioi (t ^ 2))).1
      rw [Set.compl_Ioi] at hs
      unfold retSpec
      rw [← hs, add_sub_cancel_right]
    rw [h]
    exact measurable_const.sub ((measurable_specProj isClosed_Iic).comp
      ((meas_conjTranspose hA).mul hA))
  have hT : Measurable (fun y => cavRes W g E q (R y) (ω y)) := by
    unfold cavRes
    exact meas_inv.comp ((((meas_blockSeq hω 4).sub measurable_const).sub
      (meas_const_smul _ hR)).sub (meas_const_smul _ (meas_cavR g E hω (q - 7))))
  exact meas_flagProj hT hS

end Meas

/-- Joint measurability of `(R, ω, v) ↦ K` for a measurable choice `R ↦ P(R)`. -/
theorem measurable_smallGen (W : ℕ) (g E : ℝ) (q : ℕ) (t : ℝ)
    {Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} (hPf : Measurable Pf) :
    Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) =>
      smallGen W g E q p.1 t (Pf p.1) p.2.1 p.2.2 := by
  have hR : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) => p.1 :=
    measurable_fst
  have hω : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) => p.2.1 :=
    measurable_fst.comp measurable_snd
  have hv : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) => p.2.2 :=
    measurable_snd.comp measurable_snd
  have hP : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) => Pf p.1 :=
    hPf.comp measurable_fst
  have hQ := meas_retProj g E t hR hω
  have hu := meas_mulVec hP hv
  have hs := meas_dot (meas_star hu) hu
  have hPi : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) =>
      allowProj (Pf p.1) p.2.2 := by
    unfold allowProj
    exact hP.sub (hs.inv.smul (meas_vecMulVec hu (meas_star hu)))
  have hy : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) =>
      srcVec W g E q p.1 t (Pf p.1) p.2.1 p.2.2 := by
    unfold srcVec
    exact meas_mulVec (((hPi.mul hQ).mul (meas_inv.comp (((hQ.mul hPi).mul hQ).add
      (measurable_const.sub hQ)))).mul hQ) hv
  have hg0 : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) =>
      gen0 W g E q p.1 t (Pf p.1) p.2.1 p.2.2 := by
    unfold gen0
    exact hs.inv.smul ((meas_vecMulVec hy (meas_star hu)).sub (meas_vecMulVec hu (meas_star hy)))
  have hC := meas_chartProd g E hR hω (q - 1)
  have hCv := meas_mulVec hC hv
  have hCy := meas_mulVec hC hy
  have hξ : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) =>
      genScale W g E q p.1 t (Pf p.1) p.2.1 p.2.2 := by
    unfold genScale
    exact (Complex.measurable_re.comp (meas_dot (meas_star hCv) hCy)).div
      (Finset.measurable_sum _ fun i _ =>
        (measurable_norm.comp ((measurable_pi_apply i).comp hCv)).pow_const 2)
  unfold smallGen
  exact (Complex.measurable_ofReal.comp hξ.inv).smul hg0

end LSBA
