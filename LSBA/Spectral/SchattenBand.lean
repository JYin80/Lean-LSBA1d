import Mathlib

/-!
# Schatten sums of square matrices

`Tr |Y|^p = Σ_k σ_k^p` over the singular values `σ_k` of `Y`, computed from the eigenvalues
`σ_k²` of `Y* Y`. Three facts used for (G.6) [us:eq:product] in Appendix G.3
[app:product-moment-proof]: for `p > 0` and `M` matrices,
`Tr |Σ_i Y_i|^p ≤ M^p Σ_i Tr |Y_i|^p` (from the counting inequality
`N_{Σ Y_i}(t) ≤ Σ_i N_{Y_i}(t/M)` for the numbers `N_Y(t)` of singular values above `t`, which
follows from a kernel-dimension argument); the power-mean inequality
`Tr |Y|^p ≤ (rank Y)^{1 - p/2} ‖Y‖_HS^p` for `0 < p ≤ 2`; and invariance under unitary factors
and adjoints.
-/

open MeasureTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Tr |Y|^p = Σ_k (σ_k²)^{p/2}` over the eigenvalues `σ_k²` of `Y* Y`. -/
def schattenPow (p : ℝ) (Y : Matrix n n ℂ) : ℝ :=
  ∑ k, ((Matrix.isHermitian_conjTranspose_mul_self Y).eigenvalues k) ^ (p / 2)

/-- For a Hermitian `C`, `Σ_k f(λ_k)` is the sum of `f ∘ Re` over the roots of the
characteristic polynomial of `C`. -/
private lemma sum_eigenvalues_eq_roots {C : Matrix n n ℂ} (hC : C.IsHermitian) (f : ℝ → ℝ) :
    ∑ k, f (hC.eigenvalues k) = (C.charpoly.roots.map (fun z : ℂ => f z.re)).sum := by
  rw [hC.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  simp

/-- Hermitian matrices with the same characteristic polynomial have the same sums `Σ_k f(λ_k)`
over their eigenvalues. -/
private lemma sum_eigenvalues_eq_of_charpoly {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) (f : ℝ → ℝ) :
    ∑ k, f (hA.eigenvalues k) = ∑ k, f (hB.eigenvalues k) := by
  rw [sum_eigenvalues_eq_roots hA, sum_eigenvalues_eq_roots hB, h]

omit [DecidableEq n] in
/-- Concavity of `x ↦ x^q` for `0 < q ≤ 1`: `Σ_i l_i^q ≤ r^{1-q} (Σ_i l_i)^q` for nonnegative `l`
vanishing off a set of `r` indices. -/
private lemma sum_rpow_le_card_mul {s : Finset n} (l : n → ℝ) (hl : ∀ i, 0 ≤ l i) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hs : ∀ i, i ∉ s → l i = 0) :
    ∑ i, l i ^ q ≤ (s.card : ℝ) ^ (1 - q) * (∑ i, l i) ^ q := by
  have h1 : ∑ i, l i ^ q = ∑ i ∈ s, l i ^ q :=
    (Finset.sum_subset (Finset.subset_univ s) fun i _ hi => by
      rw [hs i hi, Real.zero_rpow hq0.ne']).symm
  have h2 : ∑ i, l i = ∑ i ∈ s, l i :=
    (Finset.sum_subset (Finset.subset_univ s) fun i _ hi => hs i hi).symm
  rw [h1, h2]
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  · have hr : (0 : ℝ) < s.card := by exact_mod_cast hpos
    have hj := (Real.concaveOn_rpow hq0.le hq1).le_map_sum (t := s) (w := fun _ => 1 / (s.card : ℝ))
      (p := l) (fun i _ => by positivity) (by simp [Finset.sum_const, hr.ne'])
      (fun i _ => Set.mem_Ici.mpr (hl i))
    simp only [smul_eq_mul, ← Finset.mul_sum] at hj
    rw [Real.mul_rpow (by positivity) (Finset.sum_nonneg fun i _ => hl i), one_div,
      Real.inv_rpow hr.le] at hj
    have h3 : (s.card : ℝ) ^ (1 - q) = (s.card : ℝ) * ((s.card : ℝ) ^ q)⁻¹ := by
      rw [Real.rpow_sub hr, Real.rpow_one, div_eq_mul_inv]
    rw [h3]
    have := mul_le_mul_of_nonneg_left hj hr.le
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at this
    calc ∑ i ∈ s, l i ^ q ≤ (s.card : ℝ) * ((s.card : ℝ) ^ q)⁻¹ * (∑ i ∈ s, l i) ^ q := this

/-- `Tr Y* Y = Σ_k λ_k = Σ_{i,j} |Y_{ij}|²` for the eigenvalues `λ_k` of `Y* Y`. -/
private lemma sum_eigenvalues_eq_sum_sq (Y : Matrix n n ℂ) :
    ∑ k, (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvalues k = ∑ i, ∑ j, ‖Y i j‖ ^ 2 := by
  have h := (Matrix.isHermitian_conjTranspose_mul_self Y).trace_eq_sum_eigenvalues
  have h2 := congrArg Complex.re h
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum] at h2
  have h3 : ∀ x : ℝ, (RCLike.ofReal x : ℂ).re = x := fun x => rfl
  simp only [h3] at h2
  rw [← h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

open scoped ComplexOrder in
/-- The eigenvalues of `Y* Y` are nonnegative. -/
private lemma eigenvalues_conjTranspose_mul_self_nonneg (Y : Matrix n n ℂ) (k : n) :
    0 ≤ (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvalues k :=
  (Matrix.posSemidef_conjTranspose_mul_self Y).eigenvalues_nonneg k

open scoped ComplexOrder in
/-- `rank Y` is the number of nonzero eigenvalues of `Y* Y`. -/
private lemma rank_eq_card_ne_zero_eigenvalues (Y : Matrix n n ℂ) :
    Y.rank = Fintype.card {k // (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvalues k ≠ 0} := by
  rw [← Matrix.rank_conjTranspose_mul_self,
    (Matrix.isHermitian_conjTranspose_mul_self Y).rank_eq_card_non_zero_eigs]

/-- `‖Y x‖² = Σ_k λ_k |⟨u_k, x⟩|²` for the eigenpairs `(λ_k, u_k)` of `Y* Y`. -/
private lemma norm_sq_toEuclideanLin (Y : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin Y x‖ ^ 2 =
      ∑ k, (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvalues k *
        ‖inner ℂ ((Matrix.isHermitian_conjTranspose_mul_self Y).eigenvectorBasis k) x‖ ^ 2 := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self Y
  have hsym : (Matrix.toEuclideanLin (Yᴴ * Y)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have h1 : inner ℂ x (Matrix.toEuclideanLin (Yᴴ * Y) x) = ((‖Matrix.toEuclideanLin Y x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    simp
  have h2 : inner ℂ x (Matrix.toEuclideanLin (Yᴴ * Y) x) =
      ∑ k, (((hH.eigenvalues k * ‖inner ℂ (hH.eigenvectorBasis k) x‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← (hH.eigenvectorBasis).sum_inner_mul_inner x (Matrix.toEuclideanLin (Yᴴ * Y) x)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hb : Matrix.toEuclideanLin (Yᴴ * Y) (hH.eigenvectorBasis k) =
        ((hH.eigenvalues k : ℝ) : ℂ) • hH.eigenvectorBasis k := by
      ext i
      simpa [Matrix.toLpLin_apply] using congrFun (hH.mulVec_eigenvectorBasis k) i
    rw [← hsym (hH.eigenvectorBasis k) x, hb, inner_smul_left, ← inner_conj_symm x (hH.eigenvectorBasis k), Complex.conj_ofReal]
    push_cast
    rw [mul_left_comm, Complex.conj_mul']
  have := h1.symm.trans h2
  rw [← Complex.ofReal_sum] at this
  exact_mod_cast this


/-- The indices of the eigenvalues of `Y* Y` that exceed `s`. -/
private def hiIdx (Y : Matrix n n ℂ) (s : ℝ) : Finset n :=
  univ.filter fun k => s < (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvalues k

/-- The span of the eigenvectors of `Y* Y` with eigenvalue above `s`. -/
private def hiSpace (Y : Matrix n n ℂ) (s : ℝ) : Submodule ℂ (EuclideanSpace ℂ n) :=
  Submodule.span ℂ (Set.range fun k : hiIdx Y s =>
    (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvectorBasis k)

/-- The dimension of `hiSpace Y s` is the number of eigenvalues of `Y* Y` above `s`. -/
private lemma finrank_hiSpace (Y : Matrix n n ℂ) (s : ℝ) :
    Module.finrank ℂ (hiSpace Y s) = (hiIdx Y s).card := by
  have hli : LinearIndependent ℂ (fun k : hiIdx Y s =>
      (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvectorBasis k) :=
    (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvectorBasis.toBasis.linearIndependent.comp
      _ Subtype.val_injective
  rw [hiSpace, finrank_span_eq_card hli, Fintype.card_coe]

/-- A vector of `hiSpace Y s` is orthogonal to the eigenvectors of `Y* Y` whose eigenvalue is at
most `s`. -/
private lemma inner_eq_zero_of_mem_hiSpace (Y : Matrix n n ℂ) (s : ℝ)
    {x : EuclideanSpace ℂ n} (hx : x ∈ hiSpace Y s) {k : n} (hk : k ∉ hiIdx Y s) :
    inner ℂ ((Matrix.isHermitian_conjTranspose_mul_self Y).eigenvectorBasis k) x = 0 := by
  have hon := (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvectorBasis.orthonormal
  refine Submodule.span_induction (p := fun x _ =>
    inner ℂ ((Matrix.isHermitian_conjTranspose_mul_self Y).eigenvectorBasis k) x = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨j, rfl⟩
    exact hon.2 (fun h => hk (h ▸ j.2))
  · simp
  · intro x y _ _ hx hy
    rw [inner_add_right, hx, hy, add_zero]
  · intro a x _ hx
    rw [inner_smul_right, hx, mul_zero]


/-- On `hiSpace Y s`, nonzero `x` satisfy `s ‖x‖² < ‖Y x‖²`. -/
private lemma hiSpace_lt (Y : Matrix n n ℂ) (s : ℝ) {x : EuclideanSpace ℂ n}
    (hx : x ∈ hiSpace Y s) (hx0 : x ≠ 0) :
    s * ‖x‖ ^ 2 < ‖Matrix.toEuclideanLin Y x‖ ^ 2 := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self Y
  rw [norm_sq_toEuclideanLin, ← hH.eigenvectorBasis.sum_sq_norm_inner_right x, Finset.mul_sum,
    ← sub_pos, ← Finset.sum_sub_distrib]
  have key : ∀ k, k ∉ hiIdx Y s → inner ℂ (hH.eigenvectorBasis k) x = 0 :=
    fun k hk => inner_eq_zero_of_mem_hiSpace Y s hx hk
  apply Finset.sum_pos'
  · intro k _
    by_cases hk : k ∈ hiIdx Y s
    · have : s < hH.eigenvalues k := (Finset.mem_filter.mp hk).2
      nlinarith [sq_nonneg ‖inner ℂ (hH.eigenvectorBasis k) x‖]
    · rw [key k hk]; simp
  · obtain ⟨k, hk, hpos⟩ : ∃ k ∈ (univ : Finset n), 0 < ‖inner ℂ (hH.eigenvectorBasis k) x‖ ^ 2 := by
      by_contra h
      push Not at h
      have h1 : ∑ k, ‖inner ℂ (hH.eigenvectorBasis k) x‖ ^ 2 ≤ 0 :=
        Finset.sum_nonpos (fun k hk => h k hk)
      rw [hH.eigenvectorBasis.sum_sq_norm_inner_right] at h1
      have h2 : 0 < ‖x‖ ^ 2 := by positivity
      linarith
    have hk' : k ∈ hiIdx Y s := by
      by_contra hk'
      rw [key k hk'] at hpos
      simp at hpos
    have : s < hH.eigenvalues k := (Finset.mem_filter.mp hk').2
    exact ⟨k, hk, by nlinarith⟩

/-- On the orthogonal complement of `hiSpace Y s`, `‖Y x‖² ≤ s ‖x‖²`. -/
private lemma hiSpace_orth_le (Y : Matrix n n ℂ) (s : ℝ) {x : EuclideanSpace ℂ n}
    (hx : x ∈ (hiSpace Y s)ᗮ) :
    ‖Matrix.toEuclideanLin Y x‖ ^ 2 ≤ s * ‖x‖ ^ 2 := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self Y
  rw [norm_sq_toEuclideanLin, ← hH.eigenvectorBasis.sum_sq_norm_inner_right x, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k ∈ hiIdx Y s
  · have h0 : inner ℂ (hH.eigenvectorBasis k) x = 0 :=
      (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩)
    rw [h0]; simp
  · have : hH.eigenvalues k ≤ s := not_lt.mp fun h => hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)


omit [Fintype n] [DecidableEq n] in
/-- The dimension of a finite sum of subspaces is at most the sum of the dimensions. -/
private lemma finrank_iSup_le_sum {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {ι : Type*} [Fintype ι] (F : ι → Submodule ℂ V) (s : Finset ι) :
    Module.finrank ℂ (⨆ i ∈ s, F i : Submodule ℂ V) ≤ ∑ i ∈ s, Module.finrank ℂ (F i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (by omega)

omit [Fintype n] [DecidableEq n] in
/-- Dimension count behind the band counting inequality: if `‖(Σ_i T_i) x‖ > t ‖x‖` on the nonzero
vectors of `E` and `‖T_i x‖ ≤ (t/M) ‖x‖` on `(F_i)ᗮ`, with `M` the number of summands, then
`dim E ≤ Σ_i dim F_i`. -/
private lemma finrank_le_sum_finrank {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {ι : Type*} [Fintype ι] (T : ι → V →ₗ[ℂ] V) {t : ℝ} (ht : 0 ≤ t)
    (E : Submodule ℂ V) (hE : ∀ x ∈ E, x ≠ 0 → t * ‖x‖ < ‖(∑ i, T i) x‖)
    (F : ι → Submodule ℂ V)
    (hF : ∀ i, ∀ x ∈ (F i)ᗮ, ‖T i x‖ ≤ (t / (Fintype.card ι : ℝ)) * ‖x‖) :
    Module.finrank ℂ E ≤ ∑ i, Module.finrank ℂ (F i) := by
  set G : Submodule ℂ V := ⨆ i ∈ (Finset.univ : Finset ι), F i with hG
  have hGle : ∀ i, F i ≤ G := fun i => le_iSup₂_of_le i (Finset.mem_univ i) le_rfl
  have hK : ∀ x ∈ Gᗮ, ‖(∑ i, T i) x‖ ≤ t * ‖x‖ := by
    intro x hx
    calc ‖(∑ i, T i) x‖ = ‖∑ i, T i x‖ := by rw [LinearMap.sum_apply]
      _ ≤ ∑ i, ‖T i x‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, (t / (Fintype.card ι : ℝ)) * ‖x‖ :=
          Finset.sum_le_sum fun i _ => hF i x (Submodule.orthogonal_le (hGle i) hx)
      _ ≤ t * ‖x‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
          · rw [h0]; simp; positivity
          · have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
            rw [← mul_assoc, mul_div_cancel₀ _ this]
  have hdisj : E ⊓ Gᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    have := hE x hx.1 hx0
    have := hK x hx.2
    linarith
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq E Gᗮ
  rw [hdisj, finrank_bot] at h1
  have h2 := Submodule.finrank_le (E ⊔ Gᗮ)
  have h3 := Submodule.finrank_add_finrank_orthogonal G
  have h4 : Module.finrank ℂ G ≤ ∑ i, Module.finrank ℂ (F i) := finrank_iSup_le_sum F Finset.univ
  omega


/-- The counting inequality `N_{Σ Y_i}(t) ≤ Σ_i N_{Y_i}(t/M)`. -/
private lemma card_hiIdx_sum_le {ι : Type*} [Fintype ι] (Y : ι → Matrix n n ℂ) {t : ℝ}
    (ht : 0 < t) :
    (hiIdx (∑ i, Y i) (t ^ 2)).card ≤
      ∑ i, (hiIdx (Y i) ((t / (Fintype.card ι : ℝ)) ^ 2)).card := by
  have hS : (∑ i, (Matrix.toEuclideanLin (Y i) : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n)) =
      Matrix.toEuclideanLin (∑ i, Y i) := (map_sum Matrix.toEuclideanLin Y Finset.univ).symm
  have h := finrank_le_sum_finrank (fun i => (Matrix.toEuclideanLin (Y i) :
    EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n)) ht.le (hiSpace (∑ i, Y i) (t ^ 2))
    (by
      intro x hx hx0
      rw [hS]
      refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
      rw [mul_pow]
      exact hiSpace_lt (∑ i, Y i) _ hx hx0)
    (fun i => hiSpace (Y i) ((t / (Fintype.card ι : ℝ)) ^ 2))
    (by
      intro i x hx
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
      rw [mul_pow]
      exact hiSpace_orth_le (Y i) _ hx)
  simpa only [finrank_hiSpace] using h

/-- The counting measure of `{x | t < c x}` is the number of such `x`. -/
private lemma count_lt_eq_card {C : Type*} [Fintype C] [MeasurableSpace C]
    [MeasurableSingletonClass C] (c : C → ℝ) (t : ℝ) :
    (Measure.count : Measure C) {x | t < c x} = ((univ.filter fun x => t < c x).card : ℝ≥0∞) := by
  rw [← Measure.count_apply_finset]
  simp

/-- If the counting functions of `a` and `b` compare, so do the sums of `p`-th powers. -/
private lemma sum_rpow_le_of_count_le {A B : Type*} [Fintype A] [Fintype B] (a : A → ℝ)
    (b : B → ℝ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) {p : ℝ} (hp : 0 < p)
    (hcount : ∀ t : ℝ, 0 < t →
      (univ.filter fun x => t < a x).card ≤ (univ.filter fun y => t < b y).card) :
    ∑ x, a x ^ p ≤ ∑ y, b y ^ p := by
  let : MeasurableSpace A := ⊤
  have : MeasurableSingletonClass A := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let : MeasurableSpace B := ⊤
  have : MeasurableSingletonClass B := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hA := lintegral_rpow_eq_lintegral_meas_lt_mul (Measure.count : Measure A)
    (Filter.Eventually.of_forall ha) (measurable_of_finite a).aemeasurable hp
  have hB := lintegral_rpow_eq_lintegral_meas_lt_mul (Measure.count : Measure B)
    (Filter.Eventually.of_forall hb) (measurable_of_finite b).aemeasurable hp
  have hle : ∫⁻ ω, ENNReal.ofReal (a ω ^ p) ∂(Measure.count : Measure A) ≤
      ∫⁻ ω, ENNReal.ofReal (b ω ^ p) ∂(Measure.count : Measure B) := by
    rw [hA, hB]
    refine mul_le_mul_right ?_ _
    refine setLIntegral_mono' (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ))) fun t ht => ?_
    rw [count_lt_eq_card, count_lt_eq_card]
    gcongr
    exact hcount t ht
  rw [lintegral_fintype, lintegral_fintype] at hle
  simp only [Measure.count_singleton, mul_one] at hle
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => Real.rpow_nonneg (ha x) p),
    ← ENNReal.ofReal_sum_of_nonneg (fun y _ => Real.rpow_nonneg (hb y) p),
    ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (hb y) p)] at hle
  exact hle

/-- Band summation (Appendix G.3 [app:product-moment-proof]): for `p > 0`,
`Tr |Σ_i Y_i|^p ≤ M^p Σ_i Tr |Y_i|^p` with `M` the number of summands. -/
theorem schattenPow_sum_le {ι : Type*} [Fintype ι] (Y : ι → Matrix n n ℂ) {p : ℝ} (hp : 0 < p) :
    schattenPow p (∑ i, Y i) ≤ (Fintype.card ι : ℝ) ^ p * ∑ i, schattenPow p (Y i) := by
  have hpow : ∀ Z : Matrix n n ℂ, schattenPow p Z =
      ∑ k, (√((Matrix.isHermitian_conjTranspose_mul_self Z).eigenvalues k)) ^ p := by
    intro Z
    unfold schattenPow
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (eigenvalues_conjTranspose_mul_self_nonneg Z k)]
    congr 1
    ring
  set M : ℝ := (Fintype.card ι : ℝ) with hM
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have key := sum_rpow_le_of_count_le (A := n) (B := ι × n)
    (fun k => √((Matrix.isHermitian_conjTranspose_mul_self (∑ i, Y i)).eigenvalues k))
    (fun q => M * √((Matrix.isHermitian_conjTranspose_mul_self (Y q.1)).eigenvalues q.2))
    (fun k => Real.sqrt_nonneg _) (fun q => mul_nonneg hM0 (Real.sqrt_nonneg _)) hp ?_
  · calc schattenPow p (∑ i, Y i) = ∑ k, (√((Matrix.isHermitian_conjTranspose_mul_self
            (∑ i, Y i)).eigenvalues k)) ^ p := hpow _
      _ ≤ ∑ q : ι × n, (M * √((Matrix.isHermitian_conjTranspose_mul_self (Y q.1)).eigenvalues
            q.2)) ^ p := key
      _ = M ^ p * ∑ i, schattenPow p (Y i) := by
          rw [Fintype.sum_prod_type, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hpow, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => Real.mul_rpow hM0 (Real.sqrt_nonneg _)
  · intro t ht
    have h1 : (univ.filter fun k => t < √((Matrix.isHermitian_conjTranspose_mul_self
        (∑ i, Y i)).eigenvalues k)).card = (hiIdx (∑ i, Y i) (t ^ 2)).card := by
      unfold hiIdx
      congr 1
      ext k
      simp [Real.lt_sqrt ht.le]
    rw [h1]
    refine (card_hiIdx_sum_le Y ht).trans ?_
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp
    · have hMpos : 0 < M := Nat.cast_pos.mpr Fintype.card_pos
      have h2 : ∀ i, (hiIdx (Y i) ((t / M) ^ 2)).card = (univ.filter fun k => t <
          M * √((Matrix.isHermitian_conjTranspose_mul_self (Y i)).eigenvalues k)).card := by
        intro i
        unfold hiIdx
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← div_lt_iff₀' hMpos, Real.lt_sqrt (by positivity)]
      rw [← hM]
      simp only [h2, Finset.card_filter, Fintype.sum_prod_type]
      exact le_rfl

/-- The power-mean inequality for singular values (Appendix G.3 [app:product-moment-proof]):
`Tr |Y|^p ≤ (rank Y)^{1 - p/2} ‖Y‖_HS^p` for `0 < p ≤ 2`. -/
theorem schattenPow_le_rank_mul (Y : Matrix n n ℂ) {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    schattenPow p Y ≤ (Y.rank : ℝ) ^ (1 - p / 2) * (∑ i, ∑ j, ‖Y i j‖ ^ 2) ^ (p / 2) := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self Y
  have hq0 : 0 < p / 2 := by positivity
  have hq1 : p / 2 ≤ 1 := by linarith
  have hrank : (Y.rank : ℝ) = ((Finset.univ.filter fun k => hH.eigenvalues k ≠ 0).card : ℝ) := by
    rw [rank_eq_card_ne_zero_eigenvalues, Fintype.card_subtype]
  unfold schattenPow
  rw [hrank, ← sum_eigenvalues_eq_sum_sq]
  exact sum_rpow_le_card_mul (fun k => hH.eigenvalues k)
    (fun k => eigenvalues_conjTranspose_mul_self_nonneg Y k) hq0 hq1
    (fun k hk => by simpa using hk)

/-- Unitary factors and adjoints do not change `Tr |Y|^p`. -/
theorem schattenPow_unitary_mul (Y : Matrix n n ℂ) {U V : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ) (p : ℝ) :
    schattenPow p (U * Y * V) = schattenPow p Y ∧ schattenPow p Yᴴ = schattenPow p Y := by
  constructor
  · unfold schattenPow
    refine sum_eigenvalues_eq_of_charpoly _ _ ?_ (fun x => x ^ (p / 2))
    have hU' : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    have hV' : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
    have : (U * Y * V)ᴴ * (U * Y * V) = Vᴴ * ((Yᴴ * Y) * V) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul]
    rw [this, Matrix.charpoly_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hV', Matrix.mul_one]
  · unfold schattenPow
    refine sum_eigenvalues_eq_of_charpoly _ _ ?_ (fun x => x ^ (p / 2))
    rw [Matrix.conjTranspose_conjTranspose, Matrix.charpoly_mul_comm]

end LSBA
