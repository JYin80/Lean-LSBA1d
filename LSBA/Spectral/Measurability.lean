import LSBA.Spectral.Counts
import LSBA.Spectral.SimpleSpectrum

/-!
# Measurability of the spectral counts

Eigenvalues in decreasing order depend continuously on a Hermitian matrix; the counts of
(1.15) [eq:rough-counting], (1.17) [eq:main] and (2.12) [uv:eq:lower-regions-output] are
measurable functions of the sample.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Eigenvalues in decreasing order (`0` off Hermitian matrices). -/
def sortedEig (A : Matrix n n ℂ) : Fin (Fintype.card n) → ℝ :=
  if hA : A.IsHermitian then hA.eigenvalues₀ else 0

/-- A closed relation between `x` and `f x` that holds eventually along `F ≤ 𝓝 x₀` holds between
`x₀` and every cluster point of `f` along `F`. -/
private lemma measurability_mem_of_mapClusterPt {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {F : Filter X} {x₀ : X} (hF : F ≤ nhds x₀) {f : X → Y} {y : Y}
    (hy : MapClusterPt y F f) {R : Set (X × Y)} (hR : IsClosed R)
    (h : ∀ᶠ x in F, (x, f x) ∈ R) : (x₀, y) ∈ R := by
  by_contra hn
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp (hR.isOpen_compl.mem_nhds hn)
  obtain ⟨x, hxV, hxU, hxR⟩ :=
    ((hy.frequently (p := fun b => b ∈ V) hV).and_eventually
      ((show ∀ᶠ x in F, x ∈ U from hF hU).and h)).exists
  exact hUV ⟨hxU, hxV⟩ hxR

/-- `eigenvalues` is `eigenvalues₀` composed with the fixed reindexing of Mathlib. -/
lemma eigenvalues_eq_sortedEig {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : n) :
    hA.eigenvalues k = sortedEig A ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm k) := by
  simp [sortedEig, hA, Matrix.IsHermitian.eigenvalues]

/-- Each eigenvalue of a Hermitian matrix is bounded by the sum of the moduli of its entries. -/
private lemma measurability_abs_sortedEig_le {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (j : Fin (Fintype.card n)) : |sortedEig A j| ≤ ∑ a, ∑ b, ‖A a b‖ := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) (α := Fin _) (β := n)
  have hj : sortedEig A j = hA.eigenvalues (e j) := by
    rw [eigenvalues_eq_sortedEig hA, Equiv.symm_apply_apply]
  set v := hA.eigenvectorBasis (e j)
  have hv : ∀ a, ‖v a‖ ≤ 1 := by
    intro a
    have h1 : ∑ x, ‖v x‖ ^ 2 = 1 := by
      rw [← EuclideanSpace.norm_sq_eq, OrthonormalBasis.norm_eq_one, one_pow]
    have h2 : ‖v a‖ ^ 2 ≤ 1 := by
      rw [← h1]
      exact Finset.single_le_sum (f := fun x => ‖v x‖ ^ 2) (fun x _ => by positivity)
        (Finset.mem_univ a)
    nlinarith [norm_nonneg (v a)]
  rw [hj, hA.eigenvalues_eq]
  refine (RCLike.abs_re_le_norm _).trans ?_
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul, norm_mul, Pi.star_apply, norm_star]
  calc ‖v a‖ * (‖A a b‖ * ‖v b‖) ≤ 1 * (‖A a b‖ * 1) := by
        gcongr
        · exact hv a
        · exact hv b
    _ = ‖A a b‖ := by ring

/-- An antitone `ν` whose linear factors give the characteristic polynomial of a Hermitian `A`
is the decreasing list of eigenvalues of `A`. -/
private lemma measurability_eq_eigenvalues₀ {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {ν : Fin (Fintype.card n) → ℝ} (hν : Antitone ν)
    (h : ∀ z : ℂ, (Matrix.scalar n z - A).det = ∏ j, (z - (ν j : ℂ))) :
    ν = hA.eigenvalues₀ := by
  have hc : A.charpoly = ((Finset.univ.val.map fun j => (ν j : ℂ)).map
      fun a => Polynomial.X - Polynomial.C a).prod := by
    refine Polynomial.funext fun z => ?_
    rw [Matrix.eval_charpoly, h, Multiset.map_map, Polynomial.eval_multiset_prod,
      Multiset.map_map]
    simp [Finset.prod_eq_multiset_prod]
  have hs := hA.sort_roots_charpoly_eq_eigenvalues₀
  rw [hc, Polynomial.roots_multiset_prod_X_sub_C] at hs
  simp_rw [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Function.comp_def,
    RCLike.re_to_complex, Complex.ofReal_re, Multiset.coe_sort] at hs
  rw [List.mergeSort_of_pairwise] at hs
  · exact List.ofFn_injective hs
  · simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hν.sortedGE_ofFn

/-- The characteristic polynomial of a Hermitian matrix at `z` is the product of `z - λ_j` over
the decreasing eigenvalues. -/
private lemma measurability_det_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : ℂ) :
    (Matrix.scalar n z - A).det = ∏ j, (z - (sortedEig A j : ℂ)) := by
  rw [← Matrix.eval_charpoly, hA.charpoly_eq, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    eigenvalues_eq_sortedEig hA]
  exact Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun j => z - (sortedEig A j : ℂ))

theorem continuousOn_sortedEig :
    ContinuousOn (sortedEig (n := n)) {A : Matrix n n ℂ | A.IsHermitian} := by
  intro A₀ hA₀
  set S := {A : Matrix n n ℂ | A.IsHermitian}
  set B : Matrix n n ℂ → ℝ := fun A => ∑ a, ∑ b, ‖A a b‖
  have hB : Continuous B := by fun_prop
  set K : Set (Fin (Fintype.card n) → ℝ) :=
    Set.pi Set.univ fun _ => Set.Icc (-(B A₀ + 1)) (B A₀ + 1)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hF : nhdsWithin A₀ S ≤ nhds A₀ := nhdsWithin_le_nhds
  refine hK.tendsto_nhds_of_unique_mapClusterPt ?_ ?_
  · have h1 : ∀ᶠ A in nhdsWithin A₀ S, B A < B A₀ + 1 :=
      hF (hB.continuousAt.eventually (gt_mem_nhds (lt_add_one _)))
    filter_upwards [h1, self_mem_nhdsWithin] with A hA hS j _
    have := abs_le.mp (measurability_abs_sortedEig_le (A := A) hS j)
    constructor <;> linarith [this.1, this.2]
  · intro ν _ hν
    have hanti : Antitone ν := by
      intro i j hij
      refine measurability_mem_of_mapClusterPt hF hν (R := {p | p.2 j ≤ p.2 i})
        (isClosed_le ((continuous_apply j).comp continuous_snd)
          ((continuous_apply i).comp continuous_snd)) ?_
      filter_upwards [self_mem_nhdsWithin] with A hS
      have hS' : A.IsHermitian := hS
      simp only [sortedEig, hS', ↓reduceDIte]
      exact hS'.eigenvalues₀_antitone hij
    have hpoly : ∀ z : ℂ, (Matrix.scalar n z - A₀).det = ∏ j, (z - (ν j : ℂ)) := by
      intro z
      refine measurability_mem_of_mapClusterPt hF hν
        (R := {p | (Matrix.scalar n z - p.1).det = ∏ j, (z - (p.2 j : ℂ))}) ?_ ?_
      · refine isClosed_eq ?_ ?_
        · exact (continuous_const.sub continuous_fst).matrix_det
        · exact continuous_finsetProd _ fun j _ => continuous_const.sub
            (Complex.continuous_ofReal.comp ((continuous_apply j).comp continuous_snd))
      · filter_upwards [self_mem_nhdsWithin] with A hS
        exact measurability_det_eq hS z
    have hA₀' : A₀.IsHermitian := hA₀
    rw [measurability_eq_eigenvalues₀ hA₀' hanti hpoly]
    simp [sortedEig, hA₀']

/-- The model (1.3) [eq:model] depends continuously on the sample. -/
lemma continuous_Hmat (g : ℝ) (W L : ℕ) : Continuous (Hmat g W L) := by
  refine continuous_matrix fun p q => ?_
  simp only [Hmat, Hdet, gueBlock, blockDiagOp, Matrix.smul_apply, Matrix.add_apply,
    Matrix.of_apply, smul_eq_mul]
  split_ifs <;> fun_prop

/-- The decreasing eigenvalues of the model (1.3) [eq:model] depend continuously on the sample. -/
lemma continuous_sortedEig_Hmat (g : ℝ) (W L : ℕ)
    (j : Fin (Fintype.card (Fin L × Fin W))) :
    Continuous fun ω : Ω W L => sortedEig (Hmat g W L ω) j :=
  (continuous_apply j).comp (continuousOn_sortedEig.comp_continuous
    (continuous_Hmat g W L) fun ω => Hmat_isHermitian g W L ω)

/-- `countIn` is a sum of indicators of the decreasing eigenvalues. -/
private lemma measurability_countIn_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) (J : Set ℝ) :
    countIn A J = ∑ j, if sortedEig A j ∈ J then 1 else 0 := by
  simp only [countIn, hA, ↓reduceDIte, Finset.card_filter, eigenvalues_eq_sortedEig hA]
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun j => if sortedEig A j ∈ J then 1 else 0)

theorem measurable_countIn_Hmat (g : ℝ) (W L : ℕ) {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable fun ω : Ω W L => countIn (Hmat g W L ω) J := by
  have heq : (fun ω : Ω W L => countIn (Hmat g W L ω) J) =
      fun ω => ∑ j, if sortedEig (Hmat g W L ω) j ∈ J then 1 else 0 :=
    funext fun ω => measurability_countIn_eq (Hmat_isHermitian g W L ω) J
  rw [heq]
  exact Finset.measurable_sum _ fun j _ => Measurable.ite
    (hJ.preimage (continuous_sortedEig_Hmat g W L j).measurable)
    measurable_const measurable_const

/-- The unitary conjugate of a matrix has the unitary conjugate of its adjugate as adjugate. -/
private lemma measurability_adjugate_conj (U : Matrix.unitaryGroup n ℂ) (M : Matrix n n ℂ) :
    ((U : Matrix n n ℂ) * M * star (U : Matrix n n ℂ)).adjugate =
      (U : Matrix n n ℂ) * M.adjugate * star (U : Matrix n n ℂ) := by
  set V : Matrix n n ℂ := U.1
  have h1 : V * star V = 1 := Unitary.coe_mul_star_self U
  have h2 : star V * V = 1 := Unitary.coe_star_mul_self U
  have hU : V.adjugate = V.det • star V := by
    calc V.adjugate = V.adjugate * (V * star V) := by rw [h1, mul_one]
      _ = (V.adjugate * V) * star V := by rw [mul_assoc]
      _ = _ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, one_mul]
  have hU' : (star V).adjugate = (star V).det • V := by
    calc (star V).adjugate = (star V).adjugate * (star V * V) := by rw [h2, mul_one]
      _ = ((star V).adjugate * star V) * V := by rw [mul_assoc]
      _ = _ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, one_mul]
  have hd : (star V).det * V.det = 1 := by rw [← Matrix.det_mul, h2, Matrix.det_one]
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hU, hU']
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_assoc]
  rw [mul_comm, hd, one_smul]

/-- On simple spectrum, the squared moduli of the entries of an eigenvector are given by the
adjugate of `λ_k - A` divided by `∏_{j ≠ k} (λ_k - λ_j)`. -/
lemma norm_sq_eigenvectorBasis_eq_adjugate {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hinj : Function.Injective hA.eigenvalues) (k i : n) :
    ‖hA.eigenvectorBasis k i‖ ^ 2 =
      ((Matrix.scalar n (hA.eigenvalues k : ℂ) - A).adjugate i i).re /
        ∏ j ∈ univ.erase k, (hA.eigenvalues k - hA.eigenvalues j) := by
  set U : Matrix n n ℂ := hA.eigenvectorUnitary.1
  set ev := hA.eigenvalues
  set z : ℂ := (ev k : ℂ)
  set c : ℝ := ∏ j ∈ univ.erase k, (ev k - ev j)
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj =>
    sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hj).1 (hinj h).symm
  have h1 : Matrix.scalar n z - A = U * Matrix.diagonal (fun m => z - (ev m : ℂ)) * star U := by
    have hd : Matrix.diagonal (fun m => z - (ev m : ℂ)) =
        Matrix.scalar n z - Matrix.diagonal (RCLike.ofReal ∘ ev) := by
      ext a b
      by_cases hab : a = b <;> simp [hab]
    have hs : U * Matrix.scalar n z * star U = Matrix.scalar n z := by
      have hUU : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
      rw [(Matrix.scalar_commute z (fun r => Commute.all z r) U).eq.symm, mul_assoc, hUU,
        mul_one]
    rw [hd, mul_sub, sub_mul, hs]
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [h1, measurability_adjugate_conj, Matrix.adjugate_diagonal]
  have h2 : (U * Matrix.diagonal (fun m => ∏ j ∈ univ.erase m, (z - (ev j : ℂ))) * star U) i i =
      (c : ℂ) * (U i k * star (U i k)) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · simp only [Matrix.mul_diagonal, Matrix.star_apply, c, Complex.ofReal_prod,
        Complex.ofReal_sub, z]
      ring
    · intro m _ hmk
      have h0 : ∏ j ∈ univ.erase m, (z - (ev j : ℂ)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hmk, Finset.mem_univ k⟩) (sub_self z)
      simp [Matrix.mul_diagonal, h0]
    · simp
  rw [h2, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  have hU : U i k = hA.eigenvectorBasis k i := rfl
  rw [hU]
  field_simp

/-- Real eigenvalue `λ_k`, defined on all matrices through `sortedEig`. -/
def eigAt (A : Matrix n n ℂ) (k : n) : ℝ :=
  sortedEig A ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm k)

/-- The profile `i ↦ adj(λ_k - A)_{ii} / ∏_{j ≠ k} (λ_k - λ_j)`; on simple spectrum it is
`|ψ_k(i)|²`. -/
def eigProfile (A : Matrix n n ℂ) (k i : n) : ℝ :=
  ((Matrix.scalar n (eigAt A k : ℂ) - A).adjugate i i).re /
    ∏ j ∈ univ.erase k, (eigAt A k - eigAt A j)

/-- `ellProf` is a measurable function of the profile. -/
lemma measurable_ellProf (W L : ℕ) : Measurable (ellProf W L) := by
  have hc : ∀ m : ℕ, MeasurableSet {p : Fin L × Fin W → ℝ | ellProf W L p ≤ m} := fun m =>
    (((isClosed_setOf_ellMass_le (L * W) m).preimage
      (continuous_pi fun i => continuous_apply (finProdFinEquiv.symm i))) :
      IsClosed ((fun (p : Fin L × Fin W → ℝ) i => p (finProdFinEquiv.symm i)) ⁻¹'
        {q | ellMass (L * W) q ≤ m})).measurableSet
  refine measurable_to_countable' fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : ellProf W L ⁻¹' {0} = {p | ellProf W L p ≤ 0} := by
      ext p
      simp
    rw [this]
    exact hc 0
  · have : ellProf W L ⁻¹' {m} = {p | ellProf W L p ≤ m} \ {p | ellProf W L p ≤ m - 1} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
      omega
    rw [this]
    exact (hc m).diff (hc (m - 1))

/-- The profile `eigProfile` of the model is a measurable function of the sample. -/
lemma measurable_eigProfile_Hmat (g : ℝ) (W L : ℕ) (k : Fin L × Fin W) :
    Measurable fun ω : Ω W L => eigProfile (Hmat g W L ω) k := by
  have hev : ∀ j, Continuous fun ω : Ω W L => eigAt (Hmat g W L ω) j := fun j =>
    continuous_sortedEig_Hmat g W L _
  have hH := continuous_Hmat g W L
  refine measurable_pi_iff.mpr fun i => ?_
  refine Measurable.div ?_ ?_
  · refine Continuous.measurable ?_
    refine Complex.continuous_re.comp ?_
    refine (continuous_apply i).comp ((continuous_apply i).comp ?_)
    refine Continuous.matrix_adjugate ?_
    refine Continuous.sub ?_ hH
    simp only [Matrix.scalar_apply]
    exact Continuous.matrix_diagonal (continuous_pi fun _ =>
      Complex.continuous_ofReal.comp (hev k))
  · exact (continuous_finsetProd _ fun j _ => (hev k).sub (hev j)).measurable

/-- On simple spectrum, `badCount` is the sum over `k` of the indicator of `λ_k ∈ J` and
`ℓ < r` for the profile `eigProfile`. -/
lemma badCount_eq_sum_eigProfile {W L : ℕ}
    {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hA : A.IsHermitian)
    (hinj : Function.Injective hA.eigenvalues) (J : Set ℝ) (r : ℝ) :
    (badCount W L A J r : ℝ) = ∑ k, if eigAt A k ∈ J ∧
      ((ellProf W L (eigProfile A k) : ℕ) : ℝ) < r then 1 else 0 := by
  have hev : ∀ k, hA.eigenvalues k = eigAt A k := fun k =>
    eigenvalues_eq_sortedEig hA k
  have hmult : ∀ k, mult hA.eigenvalues k = 1 := by
    intro k
    unfold mult
    rw [Finset.card_eq_one]
    exact ⟨k, by ext j; simp [hinj.eq_iff]⟩
  have hp : ∀ k, projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k =
      eigProfile A k := by
    intro k
    funext i
    rw [projDiag_of_mult_eq_one _ _ (hmult k), norm_sq_eigenvectorBasis_eq_adjugate hA hinj, hev]
    simp only [eigProfile, hev]
  simp only [badCount, hA, ↓reduceDIte, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 : ¬ 2 ≤ mult hA.eigenvalues k := by rw [hmult k]; omega
  simp only [h2, false_or, hp, hev]

theorem aemeasurable_badCount_Hmat (g : ℝ) (W L : ℕ) {J : Set ℝ} (hJ : MeasurableSet J)
    (r : ℝ) : AEMeasurable (fun ω => (badCount W L (Hmat g W L ω) J r : ℝ)) (μ W L) := by
  have hF : Measurable fun ω : Ω W L => ∑ k, if eigAt (Hmat g W L ω) k ∈ J ∧
      ((ellProf W L (eigProfile (Hmat g W L ω) k) : ℕ) : ℝ) < r then (1 : ℝ) else 0 := by
    refine Finset.measurable_sum _ fun k _ => Measurable.ite ?_ measurable_const measurable_const
    have h1 : MeasurableSet {ω : Ω W L | eigAt (Hmat g W L ω) k ∈ J} :=
      hJ.preimage (continuous_sortedEig_Hmat g W L _).measurable
    have h2 : MeasurableSet {ω : Ω W L |
        ((ellProf W L (eigProfile (Hmat g W L ω) k) : ℕ) : ℝ) < r} :=
      measurableSet_lt (measurable_from_nat.comp ((measurable_ellProf W L).comp
        (measurable_eigProfile_Hmat g W L k))) measurable_const
    exact h1.inter h2
  refine hF.aemeasurable.congr ?_
  filter_upwards [ae_injective_eigenvalues g W L] with ω hω
  exact (badCount_eq_sum_eigProfile (Hmat_isHermitian g W L ω) hω J r).symm

theorem aemeasurable_goodCount_Hmat (g : ℝ) (W L : ℕ) {J : Set ℝ} (hJ : MeasurableSet J)
    (r : ℝ) : AEMeasurable (fun ω => (goodCount W L (Hmat g W L ω) J r : ℝ)) (μ W L) := by
  have heq : (fun ω => (goodCount W L (Hmat g W L ω) J r : ℝ)) =
      fun ω => (countIn (Hmat g W L ω) J : ℝ) - (badCount W L (Hmat g W L ω) J r : ℝ) := by
    funext ω
    rw [← goodCount_add_badCount W L (Hmat g W L ω) J r, Nat.cast_add, add_sub_cancel_right]
  rw [heq]
  exact (measurable_from_nat.comp (measurable_countIn_Hmat g W L hJ)).aemeasurable.sub
    (aemeasurable_badCount_Hmat g W L hJ r)

end LSBA
