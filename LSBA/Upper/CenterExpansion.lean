import LSBA.Transfer.StepSeries
import LSBA.Transfer.Transition

/-!
# Uniform polynomial expansions: the expansion

The expansion of Lemma 11.7 [lg:lem:ideal]: for a fixed polynomial `p` in finitely many `m_k`,
`f_k`, `W⁻¹` (and `g⁻²`) and every `s`,
`P_g p = Σ_{r≤s} t^{2r} q_r(ρ_θ p) + O(g^{−2s−2})`, `t = h_θ/g`, with `θ`-free coefficient
polynomials `q_r` (the Wick expectations of the order-`2r` configurations of one step) and
remainder uniform in `W ≥ 1`, `g ≥ 1`, `|E| ≤ E₀` and the state; `q_0 = id`. The paper's
coefficient of `g^{−2r} W^{−ℓ}` is `p_{r,ℓ} = h_θ^{2r} [w^ℓ] q_r(ρ_θ p)`. The same expansion of
the mean increment `P_g c`, continued from (11.12) [lg:eq:c2] (Section 11.3.4
[lg:sec:cocycle-correction]).
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The coefficient polynomial `q_r(p)` of `t^{2r}` in the expected one-step image of `p`
(Lemma 11.7 [lg:lem:ideal]); it does not depend on `θ`, `g`, `W`. -/
def wickMap (r : ℕ) (p : ObsPoly) : ObsPoly :=
  cfgWick (PowerSeries.coeff (2 * r) (stepSeries p))

/-- The coefficient polynomial `c_r` of `t^{2r}` in the mean increment `P_g c`. -/
def incWick (r : ℕ) : ObsPoly := cfgWick (PowerSeries.coeff (2 * r) incSeries)

/-! ### The `V`-degree grading of the step series -/

/-- The span of the words with exactly `n` letters `V`. -/
private def ceWd (n : ℕ) : Submodule ℂ WordAlg :=
  Submodule.span ℂ {a | ∃ u : List WLetter, u.count .v = n ∧ wordOf u = a}

private lemma ce_wordOf_append (u u' : List WLetter) :
    wordOf (u ++ u') = wordOf u * wordOf u' := by
  simp [wordOf]

private lemma ce_wd_mul {n m : ℕ} {x y : WordAlg} (hx : x ∈ ceWd n) (hy : y ∈ ceWd m) :
    x * y ∈ ceWd (n + m) := by
  unfold ceWd at hx hy ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨u', hu', rfl⟩ := hb
      exact Submodule.subset_span ⟨u ++ u', by simp [hu, hu'], ce_wordOf_append u u'⟩
    | zero => simp
    | add b b' _ _ hb hb' => rw [mul_add]; exact add_mem hb hb'
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hb
  | zero => simp
  | add a a' _ _ ha ha' => rw [add_mul]; exact add_mem ha ha'
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

private lemma ce_one_mem : (1 : WordAlg) ∈ ceWd 0 :=
  Submodule.subset_span ⟨[], rfl, by simp [wordOf]⟩

private lemma ce_wC_mem : wC ∈ ceWd 0 :=
  Submodule.subset_span ⟨[.c], by simp, by simp [wordOf, wC]⟩

private lemma ce_wCi_mem : wCi ∈ ceWd 0 :=
  Submodule.subset_span ⟨[.cInv], by simp, by simp [wordOf, wCi]⟩

private lemma ce_wV_mem : wV ∈ ceWd 1 :=
  Submodule.subset_span ⟨[.v], by simp, by simp [wordOf, wV]⟩

private lemma ce_wd_pow {x : WordAlg} (hx : x ∈ ceWd 1) (j : ℕ) : x ^ j ∈ ceWd j := by
  induction j with
  | zero => simpa using ce_one_mem
  | succ j ih => rw [pow_succ]; exact ce_wd_mul ih hx

/-- Series over words whose `n`-th coefficient is a combination of words with `n` letters `V`. -/
private def ceWSer : Subsemiring (PowerSeries WordAlg) where
  carrier := {S | ∀ n, PowerSeries.coeff n S ∈ ceWd n}
  mul_mem' := by
    intro S T hS hT n
    rw [PowerSeries.coeff_mul]
    refine Submodule.sum_mem _ fun p hp => ?_
    have h := ce_wd_mul (hS p.1) (hT p.2)
    rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hp] at h
  one_mem' := by
    intro n
    rw [PowerSeries.coeff_one]
    split_ifs with h
    · subst h; exact ce_one_mem
    · exact zero_mem _
  add_mem' := fun hS hT n => by rw [map_add]; exact add_mem (hS n) (hT n)
  zero_mem' := fun n => by rw [map_zero]; exact zero_mem _

private lemma ce_U_mem : (1 + wC) ∈ ceWd 0 := add_mem ce_one_mem ce_wC_mem

private lemma ce_Ui_mem : (1 + wCi) ∈ ceWd 0 := add_mem ce_one_mem ce_wCi_mem

private lemma ce_VU_mem : wV * (1 + wC) ∈ ceWd 1 := by
  simpa using ce_wd_mul ce_wV_mem ce_U_mem

private lemma ce_UiV_mem : (1 + wCi) * wV ∈ ceWd 1 := by
  simpa using ce_wd_mul ce_Ui_mem ce_wV_mem

private lemma ce_kSeries_mem : kSeries ∈ ceWSer := by
  intro n
  rw [kSeries, PowerSeries.coeff_mk]
  split_ifs with h
  · subst h; exact ce_wC_mem
  · refine Submodule.smul_mem _ _ ?_
    simpa using ce_wd_mul ce_U_mem (ce_wd_pow ce_VU_mem n)

private lemma ce_kAdjSeries_mem : kAdjSeries ∈ ceWSer := by
  intro n
  rw [kAdjSeries, PowerSeries.coeff_mk]
  split_ifs with h
  · subst h; exact ce_wCi_mem
  · refine Submodule.smul_mem _ _ ?_
    simpa using ce_wd_mul (ce_wd_pow ce_UiV_mem n) ce_Ui_mem

private lemma ce_fInvSeries_mem : fInvSeries ∈ ceWSer := by
  intro n
  rw [fInvSeries, PowerSeries.coeff_mk]
  exact Submodule.smul_mem _ _ (ce_wd_pow ce_VU_mem n)

private lemma ce_fInvAdjSeries_mem : fInvAdjSeries ∈ ceWSer := by
  intro n
  rw [fInvAdjSeries, PowerSeries.coeff_mk]
  exact Submodule.smul_mem _ _ (ce_wd_pow ce_UiV_mem n)

private lemma ce_kPowSeries_mem (k : ℤ) : kPowSeries k ∈ ceWSer := by
  unfold kPowSeries
  split_ifs
  · exact pow_mem ce_kSeries_mem _
  · exact pow_mem ce_kAdjSeries_mem _

private lemma ce_eq_wordOf (u : List WLetter) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := WLetter) (wordOf u) =
      MonoidAlgebra.of ℂ (FreeMonoid WLetter) (FreeMonoid.ofList u) := by
  induction u with
  | nil => simp [wordOf]; rfl
  | cons l u ih =>
    simp only [wordOf, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]

private lemma ce_wordFun_wordOf (φ : List WLetter → CfgPoly) (u : List WLetter) :
    wordFun φ (wordOf u) = φ u := by
  simp only [wordFun, LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
    ce_eq_wordOf]
  simp [MonoidAlgebra.of_apply]

/-- Series over configurations whose `n`-th coefficient has `V`-weight `n`. -/
private def ceCSer : Subalgebra ℂ (PowerSeries CfgPoly) where
  carrier := {S | ∀ n, IsWeightedHomogeneous CfgVar.vc (PowerSeries.coeff n S) n}
  mul_mem' := by
    intro S T hS hT n
    rw [PowerSeries.coeff_mul]
    refine IsWeightedHomogeneous.sum _ _ _ fun p hp => ?_
    have h := (hS p.1).mul (hT p.2)
    rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hp] at h
  add_mem' := fun hS hT n => by rw [map_add]; exact (hS n).add (hT n)
  algebraMap_mem' := by
    intro r n
    rw [PowerSeries.algebraMap_apply, PowerSeries.coeff_C]
    split_ifs with h
    · subst h; exact isWeightedHomogeneous_C _ _
    · exact isWeightedHomogeneous_zero _ _ _

private lemma ce_C_mem {a : CfgPoly} (ha : IsWeightedHomogeneous CfgVar.vc a 0) :
    PowerSeries.C a ∈ ceCSer := by
  intro n
  rw [PowerSeries.coeff_C]
  split_ifs with h
  · subst h; exact ha
  · exact isWeightedHomogeneous_zero _ _ _

private lemma ce_seriesMap_mem (L : WordAlg →ₗ[ℂ] CfgPoly)
    (hL : ∀ n u, u.count .v = n → IsWeightedHomogeneous CfgVar.vc (L (wordOf u)) n)
    {S : PowerSeries WordAlg} (hS : S ∈ ceWSer) : seriesMap L S ∈ ceCSer := by
  intro n
  rw [seriesMap, PowerSeries.coeff_mk]
  have : ceWd n ≤ (weightedHomogeneousSubmodule ℂ CfgVar.vc n).comap L := by
    refine Submodule.span_le.mpr ?_
    rintro a ⟨u, hu, rfl⟩
    exact (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hL n u hu)
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp (this (hS n))

private lemma ce_trcFun_hom (n : ℕ) (u : List WLetter) (hu : u.count .v = n) :
    IsWeightedHomogeneous CfgVar.vc (trcFun (wordOf u)) n := by
  rw [trcFun, ce_wordFun_wordOf]
  split_ifs with h
  · subst h
    have : n = 0 := by simpa using hu.symm
    subst this
    exact isWeightedHomogeneous_one _ _
  · have h1 := isWeightedHomogeneous_X ℂ CfgVar.vc (CfgVar.trc u)
    have h2 : CfgVar.vc (CfgVar.trc u) = n := hu
    rwa [h2] at h1

private lemma ce_mrkFun_hom (n : ℕ) (u : List WLetter) (hu : u.count .v = n) :
    IsWeightedHomogeneous CfgVar.vc (mrkFun (wordOf u)) n := by
  rw [mrkFun, ce_wordFun_wordOf]
  split_ifs with h
  · subst h
    have : n = 0 := by simpa using hu.symm
    subst this
    exact isWeightedHomogeneous_one _ _
  · have h1 := isWeightedHomogeneous_X ℂ CfgVar.vc (CfgVar.mrk u)
    have h2 : CfgVar.vc (CfgVar.mrk u) = n := hu
    rwa [h2] at h1

private lemma ce_ySeries_mem : ySeries ∈ ceCSer :=
  ce_seriesMap_mem mrkFun ce_mrkFun_hom
    (mul_mem ce_fInvSeries_mem ce_fInvAdjSeries_mem)

private lemma ce_yInvSeries_mem : yInvSeries ∈ ceCSer := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [yInvSeries, PowerSeries.coeff_invOfUnit]
    split_ifs with h0
    · subst h0
      simpa using isWeightedHomogeneous_one ℂ CfgVar.vc
    · simp only [inv_one, Units.val_one, neg_mul, one_mul]
      refine (weightedHomogeneousSubmodule ℂ CfgVar.vc n).neg_mem ?_
      refine (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_
      refine IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_
      split_ifs with hlt
      · have h := (ce_ySeries_mem x.1).mul (ih x.2 hlt)
        rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hx] at h
      · exact isWeightedHomogeneous_zero _ _ _

/-- The coefficient of `t^n` in the one-step image of any polynomial is a combination of
configurations with exactly `n` letters `V` (proof of Lemma 11.7 [lg:lem:ideal]). -/
private lemma ce_stepSeries_mem (q : ObsPoly) : stepSeries q ∈ ceCSer := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    exact ceCSer.algebraMap_mem a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    simp only [stepSeries, aeval_X]
    cases v with
    | m k => exact ce_seriesMap_mem trcFun ce_trcFun_hom (ce_kPowSeries_mem _)
    | f k =>
      exact mul_mem (ce_seriesMap_mem mrkFun ce_mrkFun_hom
        (mul_mem (mul_mem ce_fInvSeries_mem (ce_kPowSeries_mem _)) ce_fInvAdjSeries_mem))
        ce_yInvSeries_mem
    | w =>
      have h := isWeightedHomogeneous_X ℂ CfgVar.vc CfgVar.w
      exact ce_C_mem (by simpa [CfgVar.vc, CfgVar.word] using h)
    | γ =>
      have h := isWeightedHomogeneous_X ℂ CfgVar.vc CfgVar.γ
      exact ce_C_mem (by simpa [CfgVar.vc, CfgVar.word] using h)

private lemma ce_logSeries_mem {x : PowerSeries CfgPoly} (hx : x ∈ ceCSer) :
    logSeries x ∈ ceCSer := by
  intro n
  rw [logSeries, PowerSeries.coeff_mk]
  refine IsWeightedHomogeneous.sum _ _ _ fun j _ => ?_
  have h := (mem_weightedHomogeneousSubmodule ℂ CfgVar.vc n _).mpr ((pow_mem hx j) n)
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.smul_mem _ _ h)

/-- The same for the increment `c = −½ log Y` of (11.7) [lg:eq:update]. -/
private lemma ce_incSeries_mem : incSeries ∈ ceCSer := by
  rw [incSeries]
  exact Subalgebra.smul_mem _ (ce_logSeries_mem (sub_mem ce_ySeries_mem (one_mem _))) _

/-! ### Linearity and the `V`-free part of the formal expectation -/

private lemma ce_cfgWick_eq_sum (c : CfgPoly) {s : Finset (CfgVar →₀ ℕ)} (hs : c.support ⊆ s) :
    cfgWick c = ∑ d ∈ s, c.coeff d • cfgWickAux (Finsupp.weight CfgVar.vc d) d :=
  Finset.sum_subset hs fun d _ hd => by rw [notMem_support_iff.mp hd, zero_smul]

private lemma ce_cfgWick_add (p q : CfgPoly) : cfgWick (p + q) = cfgWick p + cfgWick q := by
  rw [ce_cfgWick_eq_sum (p + q) support_add, ce_cfgWick_eq_sum p Finset.subset_union_left,
    ce_cfgWick_eq_sum q Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by simp [add_smul]

private lemma ce_cfgWick_smul (a : ℂ) (c : CfgPoly) : cfgWick (a • c) = a • cfgWick c := by
  rw [ce_cfgWick_eq_sum (a • c) (MvPolynomial.support_smul), cfgWick, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul]

private lemma ce_cfgWick_sum {ι : Type*} (S : Finset ι) (a : ι → ℂ) (c : ι → CfgPoly) :
    cfgWick (∑ i ∈ S, a i • c i) = ∑ i ∈ S, a i • cfgWick (c i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [cfgWick]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ce_cfgWick_add,
      ce_cfgWick_smul, ih]

/-- On a configuration without `V` the formal expectation is the substitution `CfgVar.base`. -/
private lemma ce_cfgWick_weight_zero {c : CfgPoly} (hc : IsWeightedHomogeneous CfgVar.vc c 0) :
    cfgWick c = aeval CfgVar.base c := by
  conv_rhs => rw [c.as_sum]
  rw [map_sum, cfgWick]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight CfgVar.vc d = 0 := hc (mem_support_iff.mp hd)
  rw [hw, cfgWickAux, aeval_monomial, Algebra.smul_def]

/-! ### Measurability of the evaluations -/

private lemma ce_measurable_gb (W : ℕ) : Measurable fun ω : Ω W 1 => gueBlock W 1 ω 0 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma ce_cont_vecForm {W : ℕ} :
    Continuous fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) => vecForm q.1 q.2 := by
  have hc : Continuous (fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) =>
      Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) q.1 q.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM
  exact continuous_snd.inner hc

private lemma ce_cont_wordMat {W : ℕ} (C : Matrix (Fin W) (Fin W) ℂ) (a : WordAlg) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => wordMat C V a := by
  induction a using FreeAlgebra.induction with
  | grade0 r => simp only [AlgHom.commutes]; exact continuous_const
  | grade1 x =>
    cases x
    · simp only [wordMat, FreeAlgebra.lift_ι_apply]; exact continuous_const
    · simp only [wordMat, FreeAlgebra.lift_ι_apply]; exact continuous_const
    · simp only [wordMat, FreeAlgebra.lift_ι_apply]; exact continuous_id
  | mul a b ha hb => simp only [map_mul]; exact ha.matrix_mul hb
  | add a b ha hb => simp only [map_add]; exact ha.add hb

private lemma ce_cont_cfgEval (g : ℝ) {W : ℕ} (X : State W) (c : CfgPoly) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => cfgEval g X V c := by
  induction c using MvPolynomial.induction_on with
  | C a => simp only [cfgEval, aeval_C]; exact continuous_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p x hp =>
    simp only [map_mul]
    refine hp.mul ?_
    cases x with
    | trc u =>
      simp only [cfgEval, aeval_X]
      exact continuous_const.mul (ce_cont_wordMat X.1 _).matrix_trace
    | mrk u =>
      simp only [cfgEval, aeval_X]
      have h1 : Continuous fun V : Matrix (Fin W) (Fin W) ℂ =>
          (wordMat X.1 V (wordOf u), X.2) :=
        Continuous.prodMk (ce_cont_wordMat X.1 (wordOf u))
          (continuous_const : Continuous fun _ : Matrix (Fin W) (Fin W) ℂ => X.2)
      have h2 := (ce_cont_vecForm (W := W)).comp h1
      exact h2
    | w => simp only [cfgEval, aeval_X]; exact continuous_const
    | γ => simp only [cfgEval, aeval_X]; exact continuous_const

private lemma ce_measurable_inv {W : ℕ} :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => X⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have h : (fun X : Matrix (Fin W) (Fin W) ℂ => X⁻¹ i j) =
      fun X => (X.det)⁻¹ * X.adjugate i j := by
    funext X
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [h]
  have hd : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => X.det := continuous_id.matrix_det
  have ha : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => X.adjugate i j :=
    (continuous_id.matrix_adjugate).matrix_elem i j
  exact hd.measurable.inv.mul ha.measurable

private lemma ce_measurable_zpow {W : ℕ} (k : ℤ) :
    Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A ^ k := by
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact (continuous_id.pow n).measurable
  | negSucc n =>
    simp only [zpow_negSucc]
    exact ce_measurable_inv.comp (continuous_id.pow _).measurable

private lemma ce_measurable_obsEval (g : ℝ) (W : ℕ) (p : ObsPoly) :
    Measurable fun X : State W => obsEval g X p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [obsEval, aeval_C]; exact measurable_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p v hp =>
    simp only [map_mul]
    refine hp.mul ?_
    cases v with
    | m k =>
      simp only [obsEval, aeval_X, obsM]
      exact measurable_const.mul ((continuous_id.matrix_trace).measurable.comp
        ((ce_measurable_zpow k.1).comp measurable_fst))
    | f k =>
      simp only [obsEval, aeval_X, obsF]
      have h1 : Measurable fun X : State W => (X.1 ^ k.1, X.2) :=
        ((ce_measurable_zpow k.1).comp measurable_fst).prodMk measurable_snd
      have h2 := (ce_cont_vecForm (W := W)).measurable.comp h1
      exact h2
    | w => simp only [obsEval, aeval_X]; exact measurable_const
    | γ => simp only [obsEval, aeval_X]; exact measurable_const

/-! ### Moments and the transfer of a pointwise expansion through the Gaussian expectation -/

private lemma ce_pow_le {x : ℝ} (hx : 0 ≤ x) (r : ℕ) : (1 + x) ^ r ≤ 2 ^ r * (1 + x ^ r) := by
  have h := add_pow_le zero_le_one hx r
  rw [one_pow] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le r 1)

/-- `𝔼 (1 + ‖V‖)^r ≤ M` uniformly in `W`. -/
private lemma ce_moment (r : ℕ) : ∃ M : ℝ, 0 < M ∧ ∀ W : ℕ,
    Integrable (fun ω : Ω W 1 => (1 + ‖gueBlock W 1 ω 0‖) ^ r) (μ W 1) ∧
      ∫ ω, (1 + ‖gueBlock W 1 ω 0‖) ^ r ∂(μ W 1) ≤ M := by
  obtain ⟨C, hC, h⟩ := lintegral_norm_gueBlock_pow_le r
  refine ⟨2 ^ r * (1 + C), by positivity, fun W => ?_⟩
  have hdom : Integrable (fun ω : Ω W 1 => 2 ^ r * (1 + ‖gueBlock W 1 ω 0‖ ^ r)) (μ W 1) :=
    ((integrable_const (1 : ℝ)).add (integrable_norm_gueBlock_pow W r)).const_mul _
  have hmeas : Measurable fun ω : Ω W 1 => (1 + ‖gueBlock W 1 ω 0‖) ^ r :=
    (measurable_const.add (measurable_norm.comp (ce_measurable_gb W))).pow_const r
  have hint : Integrable (fun ω : Ω W 1 => (1 + ‖gueBlock W 1 ω 0‖) ^ r) (μ W 1) :=
    hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact ce_pow_le (norm_nonneg _) r)
  refine ⟨hint, ?_⟩
  have hn : ∫ ω, ‖gueBlock W 1 ω 0‖ ^ r ∂(μ W 1) ≤ C := by
    have h1 := ofReal_integral_eq_lintegral_ofReal (integrable_norm_gueBlock_pow W r)
      (Filter.Eventually.of_forall fun ω => by positivity)
    have h2 : ∫⁻ ω, ENNReal.ofReal (‖gueBlock W 1 ω 0‖ ^ r) ∂(μ W 1) =
        ∫⁻ ω, ‖gueBlock W 1 ω 0‖ₑ ^ r ∂(μ W 1) := by
      refine lintegral_congr fun ω => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [h2] at h1
    exact (ENNReal.ofReal_le_ofReal_iff hC.le).mp (h1.trans_le (h W))
  calc ∫ ω, (1 + ‖gueBlock W 1 ω 0‖) ^ r ∂(μ W 1)
      ≤ ∫ ω, 2 ^ r * (1 + ‖gueBlock W 1 ω 0‖ ^ r) ∂(μ W 1) :=
        integral_mono hint hdom fun ω => ce_pow_le (norm_nonneg _) r
    _ = 2 ^ r * (1 + ∫ ω, ‖gueBlock W 1 ω 0‖ ^ r ∂(μ W 1)) := by
        rw [integral_const_mul, integral_add (integrable_const _)
          (integrable_norm_gueBlock_pow W r)]
        simp
    _ ≤ 2 ^ r * (1 + C) := by gcongr

/-- A pointwise expansion in configurations, valid for every Hermitian block, passes through the
GUE expectation: the odd configurations are not yet discarded. -/
private lemma ce_core {W : ℕ} (hW : 1 ≤ W) (g : ℝ) {X : State W} (hX : IsState X)
    (N r : ℕ) {K t M : ℝ} (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hM : Integrable (fun ω : Ω W 1 => (1 + ‖gueBlock W 1 ω 0‖) ^ r) (μ W 1))
    (hMb : ∫ ω, (1 + ‖gueBlock W 1 ω 0‖) ^ r ∂(μ W 1) ≤ M)
    (F : Matrix (Fin W) (Fin W) ℂ → ℂ) (hF : Measurable F)
    (hFi : Integrable (fun ω : Ω W 1 => F (gueBlock W 1 ω 0)) (μ W 1))
    (cs : ℕ → CfgPoly)
    (hb : ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian →
      ‖F V - ∑ n ∈ Finset.range (N + 1),
          (((t ^ n : ℝ) : ℂ)) * cfgEval g X V (cs n)‖ ≤ K * t ^ (N + 1) * (1 + ‖V‖) ^ r) :
    ‖∫ ω, F (gueBlock W 1 ω 0) ∂(μ W 1) - ∑ n ∈ Finset.range (N + 1),
        (((t ^ n : ℝ) : ℂ)) * obsEval g X (cfgWick (cs n))‖ ≤ K * t ^ (N + 1) * M := by
  set c : CfgPoly := ∑ n ∈ Finset.range (N + 1), (((t ^ n : ℝ) : ℂ)) • cs n with hc
  have hev : ∀ V : Matrix (Fin W) (Fin W) ℂ, cfgEval g X V c =
      ∑ n ∈ Finset.range (N + 1), (((t ^ n : ℝ) : ℂ)) * cfgEval g X V (cs n) := by
    intro V
    simp [hc, map_sum]
  have hwick : obsEval g X (cfgWick c) = ∑ n ∈ Finset.range (N + 1),
      (((t ^ n : ℝ) : ℂ)) * obsEval g X (cfgWick (cs n)) := by
    rw [hc, ce_cfgWick_sum, map_sum]
    simp
  set R : Ω W 1 → ℂ := fun ω => F (gueBlock W 1 ω 0) - cfgEval g X (gueBlock W 1 ω 0) c with hR
  have hRb : ∀ ω, ‖R ω‖ ≤ K * t ^ (N + 1) * (1 + ‖gueBlock W 1 ω 0‖) ^ r := fun ω => by
    simp only [hR]
    rw [hev]
    exact hb _ (gueBlock_isHermitian W 1 ω 0)
  have hGm : Measurable fun ω : Ω W 1 => cfgEval g X (gueBlock W 1 ω 0) c :=
    (ce_cont_cfgEval g X c).measurable.comp (ce_measurable_gb W)
  have hRm : Measurable R := (hF.comp (ce_measurable_gb W)).sub hGm
  have hRi : Integrable R (μ W 1) :=
    (hM.const_mul (K * t ^ (N + 1))).mono' hRm.aestronglyMeasurable
      (Filter.Eventually.of_forall hRb)
  have hGi : Integrable (fun ω : Ω W 1 => cfgEval g X (gueBlock W 1 ω 0) c) (μ W 1) := by
    have h := hFi.sub hRi
    have e : ((fun ω : Ω W 1 => F (gueBlock W 1 ω 0)) - R) =
        fun ω : Ω W 1 => cfgEval g X (gueBlock W 1 ω 0) c := by
      funext ω
      simp [hR]
    rwa [e] at h
  have hint := integral_cfgEval hW g hX c
  have hdiff : ∫ ω, F (gueBlock W 1 ω 0) ∂(μ W 1) - obsEval g X (cfgWick c) =
      ∫ ω, R ω ∂(μ W 1) := by
    rw [← hint, ← integral_sub hFi hGi]
  rw [← hwick, hdiff]
  calc ‖∫ ω, R ω ∂(μ W 1)‖
      ≤ ∫ ω, K * t ^ (N + 1) * (1 + ‖gueBlock W 1 ω 0‖) ^ r ∂(μ W 1) :=
        norm_integral_le_of_norm_le (hM.const_mul _) (Filter.Eventually.of_forall hRb)
    _ = K * t ^ (N + 1) * ∫ ω, (1 + ‖gueBlock W 1 ω 0‖) ^ r ∂(μ W 1) := integral_const_mul _ _
    _ ≤ K * t ^ (N + 1) * M := by
        exact mul_le_mul_of_nonneg_left hMb (mul_nonneg hK (pow_nonneg ht _))

private lemma ce_measurable_stepObs (g E : ℝ) {W : ℕ} (X : State W) (p : ObsPoly) :
    Measurable fun V : Matrix (Fin W) (Fin W) ℂ => obsEval g (stepState g E X V) p := by
  have hS : Measurable fun V : Matrix (Fin W) (Fin W) ℂ => (X, V) :=
    Measurable.prodMk measurable_const measurable_id
  have h := (ce_measurable_obsEval g W p).comp ((measurable_stepState g E W).comp hS)
  exact h

private lemma ce_measurable_stepInc (g E : ℝ) {W : ℕ} (X : State W) :
    Measurable fun V : Matrix (Fin W) (Fin W) ℂ => ((stepInc g E X V : ℝ) : ℂ) := by
  have hS : Measurable fun V : Matrix (Fin W) (Fin W) ℂ => (X, V) :=
    Measurable.prodMk measurable_const measurable_id
  have h := Complex.measurable_ofReal.comp ((measurable_stepInc g E W).comp hS)
  exact h

/-! ### Bounds on `h_θ` and bookkeeping of the orders -/

private lemma ce_normalH_nonneg (E : ℝ) : 0 ≤ normalH E := by
  unfold normalH freeAngle
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg (E / 2))
    (Real.arccos_le_pi (E / 2))
  positivity

/-- `h_θ ≤ (2 √(1 − E₀²/4))⁻¹` for `|E| ≤ E₀ < 2`. -/
private lemma ce_normalH_le {E₀ E : ℝ} (hE₀ : E₀ < 2) (hE : |E| ≤ E₀) :
    normalH E ≤ (2 * √(1 - E₀ ^ 2 / 4))⁻¹ := by
  unfold normalH freeAngle
  rw [Real.sin_arccos]
  have ha := abs_nonneg E
  have h1 : E ^ 2 ≤ E₀ ^ 2 := by
    rw [← sq_abs E]
    exact pow_le_pow_left₀ ha hE 2
  have h2 : 0 < 1 - E₀ ^ 2 / 4 := by nlinarith
  have h3 : √(1 - E₀ ^ 2 / 4) ≤ √(1 - (E / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have h4 : 0 < √(1 - E₀ ^ 2 / 4) := Real.sqrt_pos.mpr h2
  exact inv_anti₀ (by positivity) (by linarith)

/-- The terms of odd order drop out of a sum over `n ≤ 2s + 1`. -/
private lemma ce_sum_even (s : ℕ) (a : ℕ → ℂ) (h : ∀ r, a (2 * r + 1) = 0) :
    ∑ n ∈ Finset.range (2 * s + 1 + 1), a n = ∑ r ∈ Finset.range (s + 1), a (2 * r) := by
  induction s with
  | zero => simp [Finset.sum_range_succ, h 0]
  | succ s ih =>
    have h1 : a (2 * s + 1 + 1 + 1) = 0 := by
      have := h (s + 1)
      rwa [show 2 * (s + 1) + 1 = 2 * s + 1 + 1 + 1 by ring] at this
    have h2 : 2 * s + 1 + 1 = 2 * (s + 1) := by ring
    rw [show 2 * (s + 1) + 1 + 1 = 2 * s + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, h1, add_zero, Finset.sum_range_succ _ (s + 1), h2]

/-- The final constant: `K t^n M ≤ (K M h_max^n + 1) / g^n` for `t = h/g`, `0 ≤ h ≤ h_max`. -/
private lemma ce_final {K M h hmax g : ℝ} (n : ℕ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hh : 0 ≤ h)
    (hle : h ≤ hmax) (hg : 0 < g) : K * (h / g) ^ n * M ≤ (K * M * hmax ^ n + 1) / g ^ n := by
  have hgn : 0 < g ^ n := pow_pos hg n
  have h1 : h ^ n ≤ hmax ^ n := pow_le_pow_left₀ hh hle n
  have h2 : K * (h / g) ^ n * M = K * M * h ^ n / g ^ n := by
    rw [div_pow]; ring
  rw [h2]
  exact div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hK hM)])
    hgn.le

private lemma ce_incSeries_coeff_zero : PowerSeries.coeff 0 incSeries = 0 := by
  simp [incSeries, logSeries]

/-! ### The zero-noise coefficient -/

private lemma ce_wordOf_replicate (l : WLetter) (n : ℕ) :
    wordOf (List.replicate n l) = (FreeAlgebra.ι ℂ l) ^ n := by
  induction n with
  | zero => simp [wordOf]
  | succ n ih =>
    rw [List.replicate_succ, pow_succ', ← ih]
    simp [wordOf]

private lemma ce_trcFun_pow (l : WLetter) {n : ℕ} (hn : n ≠ 0) :
    trcFun ((FreeAlgebra.ι ℂ l) ^ n) = X (.trc (List.replicate n l)) := by
  rw [← ce_wordOf_replicate, trcFun, ce_wordFun_wordOf]
  simp [hn]

private lemma ce_mrkFun_pow (l : WLetter) {n : ℕ} (hn : n ≠ 0) :
    mrkFun ((FreeAlgebra.ι ℂ l) ^ n) = X (.mrk (List.replicate n l)) := by
  rw [← ce_wordOf_replicate, mrkFun, ce_wordFun_wordOf]
  simp [hn]

private lemma ce_cc_seriesMap (L : WordAlg →ₗ[ℂ] CfgPoly) (S : PowerSeries WordAlg) :
    PowerSeries.constantCoeff (seriesMap L S) = L (PowerSeries.constantCoeff S) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, seriesMap, PowerSeries.coeff_mk,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

private lemma ce_cc_kPow (k : ℤ) :
    PowerSeries.constantCoeff (kPowSeries k) =
      if 0 ≤ k then wC ^ k.toNat else wCi ^ (-k).toNat := by
  have h1 : PowerSeries.constantCoeff kSeries = wC := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [kSeries]
  have h2 : PowerSeries.constantCoeff kAdjSeries = wCi := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [kAdjSeries]
  unfold kPowSeries
  split_ifs <;> simp [map_pow, h1, h2]

private lemma ce_cc_fInv : PowerSeries.constantCoeff fInvSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [fInvSeries]

private lemma ce_cc_fInvAdj : PowerSeries.constantCoeff fInvAdjSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [fInvAdjSeries]

private lemma ce_wordExp_replicate_c (n : ℕ) : wordExp (List.replicate n .c) = n := by
  simp [wordExp, List.count_replicate]

private lemma ce_wordExp_replicate_cInv (n : ℕ) : wordExp (List.replicate n .cInv) = -n := by
  simp [wordExp, List.count_replicate]

/-- The `V`-free part of the one-step image of a generator is the generator. -/
private lemma ce_gen_zero (v : ObsVar) :
    aeval CfgVar.base (PowerSeries.constantCoeff (stepSeries (X v))) = X v := by
  simp only [stepSeries, aeval_X]
  cases v with
  | m k =>
    obtain ⟨k, hk⟩ := k
    rw [ce_cc_seriesMap, ce_cc_kPow]
    by_cases h : 0 ≤ k
    · have hn : k.toNat ≠ 0 := by omega
      simp only [h, ↓reduceIte]
      change aeval CfgVar.base (trcFun ((FreeAlgebra.ι ℂ WLetter.c) ^ k.toNat)) = _
      rw [ce_trcFun_pow _ hn, aeval_X, CfgVar.base, ce_wordExp_replicate_c, Int.toNat_of_nonneg h]
      simp [mVar, hk]
    · have hn : (-k).toNat ≠ 0 := by omega
      simp only [h, ↓reduceIte]
      change aeval CfgVar.base (trcFun ((FreeAlgebra.ι ℂ WLetter.cInv) ^ (-k).toNat)) = _
      rw [ce_trcFun_pow _ hn, aeval_X, CfgVar.base, ce_wordExp_replicate_cInv,
        Int.toNat_of_nonneg (by omega), neg_neg]
      simp [mVar, hk]
  | f k =>
    obtain ⟨k, hk⟩ := k
    have hcc : PowerSeries.constantCoeff (fInvSeries * kPowSeries k * fInvAdjSeries) =
        if 0 ≤ k then wC ^ k.toNat else wCi ^ (-k).toNat := by
      rw [map_mul, map_mul, ce_cc_fInv, ce_cc_fInvAdj, ce_cc_kPow, one_mul, mul_one]
    have hy : PowerSeries.constantCoeff yInvSeries = 1 := by
      rw [yInvSeries, PowerSeries.constantCoeff_invOfUnit]; simp
    rw [map_mul, ce_cc_seriesMap, hcc, hy, mul_one]
    by_cases h : 0 ≤ k
    · have hn : k.toNat ≠ 0 := by omega
      simp only [h, ↓reduceIte]
      change aeval CfgVar.base (mrkFun ((FreeAlgebra.ι ℂ WLetter.c) ^ k.toNat)) = _
      rw [ce_mrkFun_pow _ hn, aeval_X, CfgVar.base, ce_wordExp_replicate_c, Int.toNat_of_nonneg h]
      simp [fVar, hk]
    · have hn : (-k).toNat ≠ 0 := by omega
      simp only [h, ↓reduceIte]
      change aeval CfgVar.base (mrkFun ((FreeAlgebra.ι ℂ WLetter.cInv) ^ (-k).toNat)) = _
      rw [ce_mrkFun_pow _ hn, aeval_X, CfgVar.base, ce_wordExp_replicate_cInv,
        Int.toNat_of_nonneg (by omega), neg_neg]
      simp [fVar, hk]
  | w => simp [CfgVar.base]
  | γ => simp [CfgVar.base]

private lemma ce_base_cc (p : ObsPoly) :
    aeval CfgVar.base (PowerSeries.constantCoeff (stepSeries p)) = p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, PowerSeries.algebraMap_apply,
      PowerSeries.constantCoeff_C, AlgHom.commutes]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, ce_gen_zero]

/-- Lemma 11.7 [lg:lem:ideal], the expansion:
`|P_g p − Σ_{r≤s} t^{2r} q_r(ρ_θ p)| ≤ K g^{−2s−2}`, uniformly in `W ≥ 1`, `g ≥ 1`, `|E| ≤ E₀`
and the state. -/
theorem transOp_obsEval_sub_le {E₀ : ℝ} (hE₀ : E₀ < 2) (p : ObsPoly) (s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X →
        ‖transOp g E (fun Y => obsEval g Y p) X - ∑ r ∈ Finset.range (s + 1),
            (((normalH E / g) ^ (2 * r) : ℝ) : ℂ) * obsEval g X (wickMap r (rotPoly E p))‖ ≤
          K / g ^ (2 * s + 2) := by
  obtain ⟨K₁, r₁, hK₁, h₁⟩ := norm_obsEval_stepState_sub_le hE₀ p (2 * s + 1)
  obtain ⟨M, hM0, hM⟩ := ce_moment r₁
  refine ⟨K₁ * M * ((2 * √(1 - E₀ ^ 2 / 4))⁻¹) ^ (2 * s + 2) + 1, by positivity,
    fun W hW g hg E hE X hX => ?_⟩
  have hg0 : 0 < g := by linarith
  have ht : 0 ≤ normalH E / g := div_nonneg (ce_normalH_nonneg E) hg0.le
  set cs : ℕ → CfgPoly := fun n => PowerSeries.coeff n (stepSeries (rotPoly E p)) with hcs
  set F : Matrix (Fin W) (Fin W) ℂ → ℂ := fun V => obsEval g (stepState g E X V) p with hF
  have hFm : Measurable F := ce_measurable_stepObs g E X p
  have hFi : Integrable (fun ω : Ω W 1 => F (gueBlock W 1 ω 0)) (μ W 1) :=
    Integrable.of_bound (hFm.comp (ce_measurable_gb W)).aestronglyMeasurable
      (∑ d ∈ p.support, ‖p.coeff d‖) (Filter.Eventually.of_forall fun ω =>
        norm_obsEval_le hW hg (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)) p)
  have hcore := ce_core hW g hX (2 * s + 1) r₁ hK₁.le ht (hM W).1 (hM W).2 F hFm hFi cs
    (fun V hV => h₁ W hW g hg E hE X hX V hV)
  have hodd : ∀ r : ℕ, (((normalH E / g) ^ (2 * r + 1) : ℝ) : ℂ) *
      obsEval g X (cfgWick (cs (2 * r + 1))) = 0 := fun r => by
    rw [cfgWick_eq_zero_of_odd, map_zero, mul_zero]
    intro d hd
    have hw := ce_stepSeries_mem (rotPoly E p) (2 * r + 1) (mem_support_iff.mp hd)
    rw [hw]
    exact ⟨r, rfl⟩
  have hsum := ce_sum_even s (fun n => (((normalH E / g) ^ n : ℝ) : ℂ) *
    obsEval g X (cfgWick (cs n))) hodd
  have hw : ∀ r, wickMap r (rotPoly E p) = cfgWick (cs (2 * r)) := fun r => rfl
  simp only [hw]
  change ‖∫ ω, F (gueBlock W 1 ω 0) ∂(μ W 1) - _‖ ≤ _
  rw [hsum] at hcore
  refine hcore.trans ?_
  exact ce_final (2 * s + 1 + 1) hK₁.le hM0.le (ce_normalH_nonneg E) (ce_normalH_le hE₀ hE) hg0

/-- The expansion of the mean increment `P_g c` to every order (continuing (11.12)
[lg:eq:c2]; Section 11.3.4 [lg:sec:cocycle-correction]). -/
theorem incMean_sub_le {E₀ : ℝ} (hE₀ : E₀ < 2) (s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X →
        ‖((incMean g E X : ℝ) : ℂ) - ∑ r ∈ Finset.range (s + 1),
            (((normalH E / g) ^ (2 * r) : ℝ) : ℂ) * obsEval g X (incWick r)‖ ≤
          K / g ^ (2 * s + 2) := by
  obtain ⟨K₁, r₁, hK₁, h₁⟩ := norm_stepInc_sub_le hE₀ (2 * s + 1)
  obtain ⟨K₀, r₀, hK₀, h₀⟩ := norm_stepInc_sub_le hE₀ 0
  obtain ⟨M₁, hM₁0, hM₁⟩ := ce_moment r₁
  obtain ⟨M₀, hM₀0, hM₀⟩ := ce_moment r₀
  refine ⟨K₁ * M₁ * ((2 * √(1 - E₀ ^ 2 / 4))⁻¹) ^ (2 * s + 2) + 1, by positivity,
    fun W hW g hg E hE X hX => ?_⟩
  have hg0 : 0 < g := by linarith
  have ht : 0 ≤ normalH E / g := div_nonneg (ce_normalH_nonneg E) hg0.le
  set cs : ℕ → CfgPoly := fun n => PowerSeries.coeff n incSeries with hcs
  set F : Matrix (Fin W) (Fin W) ℂ → ℂ := fun V => ((stepInc g E X V : ℝ) : ℂ) with hF
  have hFm : Measurable F := ce_measurable_stepInc g E X
  have hFi : Integrable (fun ω : Ω W 1 => F (gueBlock W 1 ω 0)) (μ W 1) := by
    refine ((hM₀ W).1.const_mul (K₀ * (normalH E / g) ^ (0 + 1))).mono'
      (hFm.comp (ce_measurable_gb W)).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    have h := h₀ W hW g hg E hE X hX _ (gueBlock_isHermitian W 1 ω 0)
    simpa [ce_incSeries_coeff_zero, hF] using h
  have hcore := ce_core hW g hX (2 * s + 1) r₁ hK₁.le ht (hM₁ W).1 (hM₁ W).2 F hFm hFi cs
    (fun V hV => h₁ W hW g hg E hE X hX V hV)
  have hodd : ∀ r : ℕ, (((normalH E / g) ^ (2 * r + 1) : ℝ) : ℂ) *
      obsEval g X (cfgWick (cs (2 * r + 1))) = 0 := fun r => by
    rw [cfgWick_eq_zero_of_odd, map_zero, mul_zero]
    intro d hd
    have hw := ce_incSeries_mem (2 * r + 1) (mem_support_iff.mp hd)
    rw [hw]
    exact ⟨r, rfl⟩
  have hsum := ce_sum_even s (fun n => (((normalH E / g) ^ n : ℝ) : ℂ) *
    obsEval g X (cfgWick (cs n))) hodd
  have hw : ∀ r, incWick r = cfgWick (cs (2 * r)) := fun r => rfl
  simp only [hw]
  have hint : ((incMean g E X : ℝ) : ℂ) = ∫ ω, F (gueBlock W 1 ω 0) ∂(μ W 1) :=
    (integral_ofReal (𝕜 := ℂ) (f := fun ω : Ω W 1 => stepInc g E X (gueBlock W 1 ω 0))).symm
  rw [hint]
  rw [hsum] at hcore
  refine hcore.trans ?_
  exact ce_final (2 * s + 1 + 1) hK₁.le hM₁0.le (ce_normalH_nonneg E) (ce_normalH_le hE₀ hE) hg0

/-- The zero-noise coefficient is the identity: `q_0 = id`, `c_0 = 0`. -/
theorem wickMap_zero_incWick_zero (p : ObsPoly) : wickMap 0 p = p ∧ incWick 0 = 0 := by
  refine ⟨?_, ?_⟩
  · unfold wickMap
    rw [Nat.mul_zero, ce_cfgWick_weight_zero (ce_stepSeries_mem p 0),
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ce_base_cc p
  · unfold incWick
    rw [Nat.mul_zero, ce_incSeries_coeff_zero]
    simp [cfgWick]

end LSBA
