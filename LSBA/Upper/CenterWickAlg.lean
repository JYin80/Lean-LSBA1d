import LSBA.Upper.CenterExpansion
import LSBA.Gauss.WickConfigAlg
import LSBA.Gauss.WickConfigConj

/-!
# Uniform polynomial expansions: algebraic properties

Properties of the coefficient polynomials `q_r` of Lemma 11.7 [lg:lem:ideal]: linearity and
`g⁻²`-linearity; commutation with conjugation; property (ii), the `W⁰` part is multiplicative:
`π₀ q_r(p p̃) = Σ_{a+b=r} π₀ q_a(p) π₀ q_b(p̃)`; property (iii), a polynomial in the `m_k` (and
`g⁻²`) has coefficients in the traces with even powers of `W⁻¹` only, so no `W⁻¹` term.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Linearity of the formal expectation -/

private lemma cwa_cfgWick_eq_sum (c : CfgPoly) {s : Finset (CfgVar →₀ ℕ)} (hs : c.support ⊆ s) :
    cfgWick c = ∑ d ∈ s, c.coeff d • cfgWickAux (Finsupp.weight CfgVar.vc d) d :=
  Finset.sum_subset hs fun d _ hd => by rw [notMem_support_iff.mp hd, zero_smul]

private lemma cwa_cfgWick_add (p q : CfgPoly) : cfgWick (p + q) = cfgWick p + cfgWick q := by
  rw [cwa_cfgWick_eq_sum (p + q) support_add, cwa_cfgWick_eq_sum p Finset.subset_union_left,
    cwa_cfgWick_eq_sum q Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by simp [add_smul]

private lemma cwa_cfgWick_smul (a : ℂ) (c : CfgPoly) : cfgWick (a • c) = a • cfgWick c := by
  rw [cwa_cfgWick_eq_sum (a • c) (MvPolynomial.support_smul), cfgWick, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul]

/-- The formal expectation as a `ℂ`-linear map. -/
private def cwaLin : CfgPoly →ₗ[ℂ] ObsPoly where
  toFun := cfgWick
  map_add' := cwa_cfgWick_add
  map_smul' := cwa_cfgWick_smul

private lemma cwaLin_apply (c : CfgPoly) : cwaLin c = cfgWick c := rfl

private lemma cwa_cfgWick_monomial (d : CfgVar →₀ ℕ) (a : ℂ) :
    cfgWick (monomial d a) = a • cfgWickAux (Finsupp.weight CfgVar.vc d) d := by
  rw [cwa_cfgWick_eq_sum _ support_monomial_subset, Finset.sum_singleton, coeff_monomial,
    ite_eq_left rfl]

/-! ### The factor `γ` -/

private lemma cwa_vc_γ : CfgVar.γ.vc = 0 := rfl

private lemma cwa_filter_add_γ (d : CfgVar →₀ ℕ) :
    ((d + Finsupp.single CfgVar.γ 1).support.filter fun x => 0 < x.vc) =
      d.support.filter fun x => 0 < x.vc := by
  ext x
  simp only [Finset.mem_filter, Finsupp.mem_support_iff, Finsupp.add_apply]
  by_cases hx : x = .γ
  · subst hx
    simp [cwa_vc_γ]
  · rw [Finsupp.single_eq_of_ne hx, add_zero]

private lemma cwa_cfgPick_add_γ (d : CfgVar →₀ ℕ) :
    cfgPick (d + Finsupp.single CfgVar.γ 1) = cfgPick d := by
  simp only [cfgPick, cwa_filter_add_γ]

private lemma cwa_cfgPick_mem {d : CfgVar →₀ ℕ}
    (h : (d.support.filter fun x => 0 < x.vc).Nonempty) :
    cfgPick d ∈ d.support ∧ 0 < (cfgPick d).vc := by
  have := (Classical.choose_spec
    ((d.support.filter fun x => 0 < x.vc).exists_min_image CfgVar.key h)).1
  simp only [cfgPick, h, ↓reduceDIte]
  exact Finset.mem_filter.mp this

private lemma cwa_prod_add_γ (d : CfgVar →₀ ℕ) :
    (d + Finsupp.single CfgVar.γ 1).prod (fun x k => x.base ^ k) =
      X ObsVar.γ * d.prod fun x k => x.base ^ k := by
  rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
    Finsupp.prod_single_index (by simp)]
  simp [CfgVar.base, mul_comm]

private lemma cwa_sub_add_γ {d : CfgVar →₀ ℕ} {x : CfgVar} (hx : x ≠ .γ) :
    d + Finsupp.single CfgVar.γ 1 - Finsupp.single x 1 =
      (d - Finsupp.single x 1) + Finsupp.single CfgVar.γ 1 := by
  ext y
  simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply]
  by_cases hy : y = .γ
  · subst hy
    simp [Ne.symm hx]
  · simp [Finsupp.single_apply, Ne.symm hy]

/-- The cross sum of one expansion step commutes with the factor `γ`. -/
private lemma cwa_cross_γ (n : ℕ)
    (ih : ∀ d : CfgVar →₀ ℕ,
      cfgWickAux n (d + Finsupp.single CfgVar.γ 1) = X ObsVar.γ * cfgWickAux n d)
    (φ : CfgVar) (e : CfgVar →₀ ℕ) :
    ∑ ψ ∈ (e + Finsupp.single CfgVar.γ 1).support,
        ((vPos ψ.word).map fun j =>
          (((e + Finsupp.single CfgVar.γ 1 : CfgVar →₀ ℕ) ψ : ℕ) : ℂ) •
            (X ObsVar.w ^ (crossPair φ ψ j).1 *
              cfgWickAux n (e + Finsupp.single CfgVar.γ 1 - Finsupp.single ψ 1 +
                (crossPair φ ψ j).2))).sum =
      X ObsVar.γ * ∑ ψ ∈ e.support,
        ((vPos ψ.word).map fun j =>
          ((e ψ : ℕ) : ℂ) • (X ObsVar.w ^ (crossPair φ ψ j).1 *
            cfgWickAux n (e - Finsupp.single ψ 1 + (crossPair φ ψ j).2))).sum := by
  rw [Finset.mul_sum]
  have hterm : ∀ ψ : CfgVar,
      ((vPos ψ.word).map fun j =>
          (((e + Finsupp.single CfgVar.γ 1 : CfgVar →₀ ℕ) ψ : ℕ) : ℂ) •
            (X ObsVar.w ^ (crossPair φ ψ j).1 *
              cfgWickAux n (e + Finsupp.single CfgVar.γ 1 - Finsupp.single ψ 1 +
                (crossPair φ ψ j).2))).sum =
        X ObsVar.γ * ((vPos ψ.word).map fun j =>
          ((e ψ : ℕ) : ℂ) • (X ObsVar.w ^ (crossPair φ ψ j).1 *
            cfgWickAux n (e - Finsupp.single ψ 1 + (crossPair φ ψ j).2))).sum := by
    intro ψ
    by_cases hψ : ψ = .γ
    · subst hψ
      simp [CfgVar.word, vPos]
    · rw [cwa_sub_add_γ hψ, Finsupp.add_apply, Finsupp.single_eq_of_ne hψ, add_zero,
        ← List.sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
      rw [add_right_comm, ih, mul_left_comm, mul_smul_comm]
  have hsub : e.support ⊆ (e + Finsupp.single CfgVar.γ 1).support := by
    intro ψ hψ
    rw [Finsupp.mem_support_iff] at hψ ⊢
    simp only [Finsupp.add_apply]
    omega
  rw [Finset.sum_congr rfl fun ψ _ => hterm ψ]
  refine (Finset.sum_subset hsub fun ψ _ hψ => ?_).symm
  rw [Finsupp.notMem_support_iff.mp hψ]
  simp

private lemma cwa_wickAux_γ (n : ℕ) : ∀ d : CfgVar →₀ ℕ,
    cfgWickAux n (d + Finsupp.single CfgVar.γ 1) = X ObsVar.γ * cfgWickAux n d := by
  induction n with
  | zero => intro d; simp only [cfgWickAux]; exact cwa_prod_add_γ d
  | succ n ih =>
    intro d
    rw [cfgWickAux.eq_2, cfgWickAux.eq_2, cwa_filter_add_γ, cwa_cfgPick_add_γ]
    by_cases hne : (d.support.filter fun x => 0 < x.vc).Nonempty
    · simp only [ite_eq_left hne]
      obtain ⟨hφd, hφ⟩ := cwa_cfgPick_mem hne
      have hφγ : cfgPick d ≠ .γ := fun h => by rw [h, cwa_vc_γ] at hφ; exact lt_irrefl _ hφ
      rw [cwa_sub_add_γ hφγ, mul_add]
      refine congrArg₂ (· + ·) ?_ (cwa_cross_γ n ih _ _)
      rw [← List.sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
      rw [add_right_comm, ih]
    · simp only [ite_eq_right hne]
      exact cwa_prod_add_γ d

private lemma cwa_cfgWick_γ (c : CfgPoly) : cfgWick (X CfgVar.γ * c) = X ObsVar.γ * cfgWick c := by
  induction c using MvPolynomial.induction_on' with
  | monomial d a =>
    have hw : Finsupp.weight CfgVar.vc (d + Finsupp.single CfgVar.γ 1) =
        Finsupp.weight CfgVar.vc d := by
      rw [map_add, Finsupp.weight_single, cwa_vc_γ, smul_zero, add_zero]
    rw [X, monomial_mul_monomial, one_mul, cwa_cfgWick_monomial, cwa_cfgWick_monomial,
      add_comm (Finsupp.single CfgVar.γ 1) d, hw, cwa_wickAux_γ, mul_smul_comm]
  | add p q hp hq => rw [mul_add, cwa_cfgWick_add, cwa_cfgWick_add, hp, hq, mul_add]

/-! ### Words -/

private lemma cwa_wordOf_append (u u' : List WLetter) :
    wordOf (u ++ u') = wordOf u * wordOf u' := by
  simp [wordOf]

private lemma cwa_eq_wordOf (u : List WLetter) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := WLetter) (wordOf u) =
      MonoidAlgebra.of ℂ (FreeMonoid WLetter) (FreeMonoid.ofList u) := by
  induction u with
  | nil => simp [wordOf]; rfl
  | cons l u ih =>
    simp only [wordOf, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]

private lemma cwa_wordFun_wordOf (φ : List WLetter → CfgPoly) (u : List WLetter) :
    wordFun φ (wordOf u) = φ u := by
  simp only [wordFun, LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
    cwa_eq_wordOf]
  simp [MonoidAlgebra.of_apply]

private lemma cwa_trcFun_wordOf (u : List WLetter) :
    trcFun (wordOf u) = if u = [] then 1 else X (.trc u) := by
  rw [trcFun, cwa_wordFun_wordOf]

private lemma cwa_mrkFun_wordOf (u : List WLetter) :
    mrkFun (wordOf u) = if u = [] then 1 else X (.mrk u) := by
  rw [mrkFun, cwa_wordFun_wordOf]

/-- The words span the algebra of words. -/
private lemma cwa_mem_span (a : WordAlg) : a ∈ Submodule.span ℂ (Set.range wordOf) := by
  have hmul : ∀ x y : WordAlg, x ∈ Submodule.span ℂ (Set.range wordOf) →
      y ∈ Submodule.span ℂ (Set.range wordOf) →
      x * y ∈ Submodule.span ℂ (Set.range wordOf) := by
    intro x y hx hy
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨u, rfl⟩ := ha
      induction hy using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨u', rfl⟩ := hb
        exact Submodule.subset_span ⟨u ++ u', cwa_wordOf_append u u'⟩
      | zero => simp
      | add b b' _ _ hb hb' => rw [mul_add]; exact add_mem hb hb'
      | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hb
    | zero => simp
    | add a a' _ _ ha ha' => rw [add_mul]; exact add_mem ha ha'
    | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], by simp [wordOf]⟩)
  | grade1 x => exact Submodule.subset_span ⟨[x], by simp [wordOf]⟩
  | mul a b ha hb => exact hmul a b ha hb
  | add a b ha hb => exact add_mem ha hb

/-! ### Conjugation of words -/

/-- `WordAlg` with the scalar action twisted by complex conjugation. -/
private def WTw : Type := WordAlg

private instance : Ring WTw := inferInstanceAs (Ring WordAlg)

private instance : Algebra ℂ WTw := Algebra.compHom WordAlg (starRingEnd ℂ)

/-- The algebra map to the opposite of the conjugate algebra: `C ↔ C⁻¹`, `V ↦ V`. -/
private def wStarHom : WordAlg →ₐ[ℂ] WTwᵐᵒᵖ :=
  FreeAlgebra.lift ℂ fun l => MulOpposite.op ((FreeAlgebra.ι ℂ l.adj : WordAlg) : WTw)

/-- The conjugate-linear anti-involution of words: reverse, `C ↔ C⁻¹`, conjugate scalars. -/
private def wStar (a : WordAlg) : WordAlg := MulOpposite.unop (wStarHom a)

private lemma wStar_mul (a b : WordAlg) : wStar (a * b) = wStar b * wStar a := by
  simp [wStar, map_mul]
  rfl

private lemma wStar_add (a b : WordAlg) : wStar (a + b) = wStar a + wStar b := by
  simp [wStar, map_add]
  rfl

private lemma wStar_zero : wStar 0 = 0 := by
  simp [wStar, map_zero]
  rfl

private lemma wStar_smul (c : ℂ) (a : WordAlg) : wStar (c • a) = (starRingEnd ℂ c) • wStar a := by
  simp only [wStar, map_smul]
  rfl

private lemma wStar_ι (l : WLetter) : wStar (FreeAlgebra.ι ℂ l) = FreeAlgebra.ι ℂ l.adj := by
  simp [wStar, wStarHom]
  rfl

private lemma wStar_one : wStar 1 = 1 := by
  simp [wStar, map_one]
  rfl

private lemma wStar_sum {ι : Type*} (s : Finset ι) (f : ι → WordAlg) :
    wStar (∑ i ∈ s, f i) = ∑ i ∈ s, wStar (f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using wStar_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, wStar_add, ih]

private lemma wStar_pow (a : WordAlg) (n : ℕ) : wStar (a ^ n) = wStar a ^ n := by
  induction n with
  | zero => simpa using wStar_one
  | succ n ih => rw [pow_succ, wStar_mul, ih, pow_succ']

private lemma wStar_wordOf (u : List WLetter) :
    wStar (wordOf u) = wordOf (u.reverse.map WLetter.adj) := by
  induction u with
  | nil => simpa [wordOf] using wStar_one
  | cons l u ih =>
    rw [show wordOf (l :: u) = wordOf [l] * wordOf u by simp [wordOf], wStar_mul, ih,
      List.reverse_cons, List.map_append, cwa_wordOf_append]
    simp [wordOf, wStar_ι]

private lemma cwa_cfgConj_smul (c : ℂ) (x : CfgPoly) :
    cfgConj (c • x) = (starRingEnd ℂ c) • cfgConj x := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.smul_eq_C_mul]
  simp [cfgConj]

private lemma cwa_cfgConj_trcFun (a : WordAlg) : cfgConj (trcFun a) = trcFun (wStar a) := by
  induction cwa_mem_span a using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, rfl⟩ := ha
    rw [wStar_wordOf, cwa_trcFun_wordOf, cwa_trcFun_wordOf]
    by_cases hu : u = []
    · simp [hu]
    · have hu' : u.reverse.map WLetter.adj ≠ [] := by simpa using hu
      rw [ite_eq_right hu, ite_eq_right hu']
      simp [cfgConj, CfgVar.adj]
  | zero => rw [map_zero, map_zero, wStar_zero, map_zero]
  | add a b _ _ ha hb => rw [map_add, map_add, wStar_add, map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, cwa_cfgConj_smul, wStar_smul, map_smul, ha]

private lemma cwa_cfgConj_mrkFun (a : WordAlg) : cfgConj (mrkFun a) = mrkFun (wStar a) := by
  induction cwa_mem_span a using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, rfl⟩ := ha
    rw [wStar_wordOf, cwa_mrkFun_wordOf, cwa_mrkFun_wordOf]
    by_cases hu : u = []
    · simp [hu]
    · have hu' : u.reverse.map WLetter.adj ≠ [] := by simpa using hu
      rw [ite_eq_right hu, ite_eq_right hu']
      simp [cfgConj, CfgVar.adj]
  | zero => rw [map_zero, map_zero, wStar_zero, map_zero]
  | add a b _ _ ha hb => rw [map_add, map_add, wStar_add, map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, cwa_cfgConj_smul, wStar_smul, map_smul, ha]

/-! ### Conjugation of series -/

/-- `wStar` on each coefficient of a series. -/
private def cwaStarS (S : PowerSeries WordAlg) : PowerSeries WordAlg :=
  PowerSeries.mk fun n => wStar (PowerSeries.coeff n S)

private lemma coeff_cwaStarS (S : PowerSeries WordAlg) (n : ℕ) :
    PowerSeries.coeff n (cwaStarS S) = wStar (PowerSeries.coeff n S) := by
  rw [cwaStarS, PowerSeries.coeff_mk]

private lemma cwaStarS_mul (S T : PowerSeries WordAlg) :
    cwaStarS (S * T) = cwaStarS T * cwaStarS S := by
  ext n
  rw [coeff_cwaStarS, PowerSeries.coeff_mul, PowerSeries.coeff_mul, wStar_sum,
    ← Finset.Nat.sum_antidiagonal_swap]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [wStar_mul, coeff_cwaStarS, coeff_cwaStarS]
  rfl

private lemma cwaStarS_one : cwaStarS 1 = 1 := by
  ext n
  rw [coeff_cwaStarS, PowerSeries.coeff_one]
  split_ifs
  · exact wStar_one
  · exact wStar_zero

private lemma cwaStarS_pow (S : PowerSeries WordAlg) (n : ℕ) :
    cwaStarS (S ^ n) = cwaStarS S ^ n := by
  induction n with
  | zero => simpa using cwaStarS_one
  | succ n ih => rw [pow_succ, cwaStarS_mul, ih, pow_succ']

private lemma wStar_wC : wStar wC = wCi := by
  rw [wC, wStar_ι]
  rfl

private lemma wStar_wCi : wStar wCi = wC := by
  rw [wCi, wStar_ι]
  rfl

private lemma wStar_wV : wStar wV = wV := by
  rw [wV, wStar_ι]
  rfl

private lemma wStar_VU : wStar (wV * (1 + wC)) = (1 + wCi) * wV := by
  rw [wStar_mul, wStar_add, wStar_one, wStar_wC, wStar_wV]

private lemma wStar_UiV : wStar ((1 + wCi) * wV) = wV * (1 + wC) := by
  rw [wStar_mul, wStar_add, wStar_one, wStar_wCi, wStar_wV]

private lemma cwaStarS_kSeries : cwaStarS kSeries = kAdjSeries := by
  ext j
  rw [coeff_cwaStarS, kSeries, kAdjSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  split_ifs with h
  · exact wStar_wC
  · rw [wStar_smul, wStar_mul, wStar_pow, wStar_VU, wStar_add, wStar_one, wStar_wC, map_pow,
      Complex.conj_I, neg_pow Complex.I, ]

/-! ### The `V`-degree grading of the step series -/

/-- The span of the words with exactly `n` letters `V`. -/
private def cwaWd (n : ℕ) : Submodule ℂ WordAlg :=
  Submodule.span ℂ {a | ∃ u : List WLetter, u.count .v = n ∧ wordOf u = a}

private lemma cwa_wd_mul {n m : ℕ} {x y : WordAlg} (hx : x ∈ cwaWd n) (hy : y ∈ cwaWd m) :
    x * y ∈ cwaWd (n + m) := by
  unfold cwaWd at hx hy ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨u', hu', rfl⟩ := hb
      exact Submodule.subset_span ⟨u ++ u', by simp [hu, hu'], cwa_wordOf_append u u'⟩
    | zero => simp
    | add b b' _ _ hb hb' => rw [mul_add]; exact add_mem hb hb'
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hb
  | zero => simp
  | add a a' _ _ ha ha' => rw [add_mul]; exact add_mem ha ha'
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

private lemma cwa_one_mem : (1 : WordAlg) ∈ cwaWd 0 :=
  Submodule.subset_span ⟨[], rfl, by simp [wordOf]⟩

private lemma cwa_wC_mem : wC ∈ cwaWd 0 :=
  Submodule.subset_span ⟨[.c], by simp, by simp [wordOf, wC]⟩

private lemma cwa_wCi_mem : wCi ∈ cwaWd 0 :=
  Submodule.subset_span ⟨[.cInv], by simp, by simp [wordOf, wCi]⟩

private lemma cwa_wV_mem : wV ∈ cwaWd 1 :=
  Submodule.subset_span ⟨[.v], by simp, by simp [wordOf, wV]⟩

private lemma cwa_wd_pow {x : WordAlg} (hx : x ∈ cwaWd 1) (j : ℕ) : x ^ j ∈ cwaWd j := by
  induction j with
  | zero => simpa using cwa_one_mem
  | succ j ih => rw [pow_succ]; exact cwa_wd_mul ih hx

/-- Series over words whose `n`-th coefficient is a combination of words with `n` letters `V`. -/
private def cwaWSer : Subsemiring (PowerSeries WordAlg) where
  carrier := {S | ∀ n, PowerSeries.coeff n S ∈ cwaWd n}
  mul_mem' := by
    intro S T hS hT n
    rw [PowerSeries.coeff_mul]
    refine Submodule.sum_mem _ fun p hp => ?_
    have h := cwa_wd_mul (hS p.1) (hT p.2)
    rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hp] at h
  one_mem' := by
    intro n
    rw [PowerSeries.coeff_one]
    split_ifs with h
    · subst h; exact cwa_one_mem
    · exact zero_mem _
  add_mem' := fun hS hT n => by rw [map_add]; exact add_mem (hS n) (hT n)
  zero_mem' := fun n => by rw [map_zero]; exact zero_mem _

private lemma cwa_U_mem : (1 + wC) ∈ cwaWd 0 := add_mem cwa_one_mem cwa_wC_mem

private lemma cwa_Ui_mem : (1 + wCi) ∈ cwaWd 0 := add_mem cwa_one_mem cwa_wCi_mem

private lemma cwa_VU_mem : wV * (1 + wC) ∈ cwaWd 1 := by
  simpa using cwa_wd_mul cwa_wV_mem cwa_U_mem

private lemma cwa_UiV_mem : (1 + wCi) * wV ∈ cwaWd 1 := by
  simpa using cwa_wd_mul cwa_Ui_mem cwa_wV_mem

private lemma cwa_kSeries_mem : kSeries ∈ cwaWSer := by
  intro n
  rw [kSeries, PowerSeries.coeff_mk]
  split_ifs with h
  · subst h; exact cwa_wC_mem
  · refine Submodule.smul_mem _ _ ?_
    simpa using cwa_wd_mul cwa_U_mem (cwa_wd_pow cwa_VU_mem n)

private lemma cwa_kAdjSeries_mem : kAdjSeries ∈ cwaWSer := by
  intro n
  rw [kAdjSeries, PowerSeries.coeff_mk]
  split_ifs with h
  · subst h; exact cwa_wCi_mem
  · refine Submodule.smul_mem _ _ ?_
    simpa using cwa_wd_mul (cwa_wd_pow cwa_UiV_mem n) cwa_Ui_mem

private lemma cwa_fInvSeries_mem : fInvSeries ∈ cwaWSer := by
  intro n
  rw [fInvSeries, PowerSeries.coeff_mk]
  exact Submodule.smul_mem _ _ (cwa_wd_pow cwa_VU_mem n)

private lemma cwa_fInvAdjSeries_mem : fInvAdjSeries ∈ cwaWSer := by
  intro n
  rw [fInvAdjSeries, PowerSeries.coeff_mk]
  exact Submodule.smul_mem _ _ (cwa_wd_pow cwa_UiV_mem n)

private lemma cwa_kPowSeries_mem (k : ℤ) : kPowSeries k ∈ cwaWSer := by
  unfold kPowSeries
  split_ifs
  · exact pow_mem cwa_kSeries_mem _
  · exact pow_mem cwa_kAdjSeries_mem _

/-- Series over configurations whose `n`-th coefficient has `V`-weight `n`. -/
private def cwaCSer : Subalgebra ℂ (PowerSeries CfgPoly) where
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

private lemma cwa_C_mem {a : CfgPoly} (ha : IsWeightedHomogeneous CfgVar.vc a 0) :
    PowerSeries.C a ∈ cwaCSer := by
  intro n
  rw [PowerSeries.coeff_C]
  split_ifs with h
  · subst h; exact ha
  · exact isWeightedHomogeneous_zero _ _ _

private lemma cwa_seriesMap_mem (L : WordAlg →ₗ[ℂ] CfgPoly)
    (hL : ∀ n u, u.count .v = n → IsWeightedHomogeneous CfgVar.vc (L (wordOf u)) n)
    {S : PowerSeries WordAlg} (hS : S ∈ cwaWSer) : seriesMap L S ∈ cwaCSer := by
  intro n
  rw [seriesMap, PowerSeries.coeff_mk]
  have : cwaWd n ≤ (weightedHomogeneousSubmodule ℂ CfgVar.vc n).comap L := by
    refine Submodule.span_le.mpr ?_
    rintro a ⟨u, hu, rfl⟩
    exact (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hL n u hu)
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp (this (hS n))

private lemma cwa_trcFun_hom (n : ℕ) (u : List WLetter) (hu : u.count .v = n) :
    IsWeightedHomogeneous CfgVar.vc (trcFun (wordOf u)) n := by
  rw [trcFun, cwa_wordFun_wordOf]
  split_ifs with h
  · subst h
    have : n = 0 := by simpa using hu.symm
    subst this
    exact isWeightedHomogeneous_one _ _
  · have h1 := isWeightedHomogeneous_X ℂ CfgVar.vc (CfgVar.trc u)
    have h2 : CfgVar.vc (CfgVar.trc u) = n := hu
    rwa [h2] at h1

private lemma cwa_mrkFun_hom (n : ℕ) (u : List WLetter) (hu : u.count .v = n) :
    IsWeightedHomogeneous CfgVar.vc (mrkFun (wordOf u)) n := by
  rw [mrkFun, cwa_wordFun_wordOf]
  split_ifs with h
  · subst h
    have : n = 0 := by simpa using hu.symm
    subst this
    exact isWeightedHomogeneous_one _ _
  · have h1 := isWeightedHomogeneous_X ℂ CfgVar.vc (CfgVar.mrk u)
    have h2 : CfgVar.vc (CfgVar.mrk u) = n := hu
    rwa [h2] at h1

private lemma cwa_ySeries_mem : ySeries ∈ cwaCSer :=
  cwa_seriesMap_mem mrkFun cwa_mrkFun_hom
    (mul_mem cwa_fInvSeries_mem cwa_fInvAdjSeries_mem)

private lemma cwa_constantCoeff_y : PowerSeries.constantCoeff ySeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ySeries, seriesMap, PowerSeries.coeff_mk,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
  have h1 : PowerSeries.constantCoeff fInvSeries = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [fInvSeries]
  have h2 : PowerSeries.constantCoeff fInvAdjSeries = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [fInvAdjSeries]
  rw [h1, h2, mul_one, show (1 : WordAlg) = wordOf [] by simp [wordOf], mrkFun,
    cwa_wordFun_wordOf]
  simp

private lemma cwa_yInvSeries_mem : yInvSeries ∈ cwaCSer := by
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
      · have h := (cwa_ySeries_mem x.1).mul (ih x.2 hlt)
        rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hx] at h
      · exact isWeightedHomogeneous_zero _ _ _

/-- The coefficient of `t^n` in the one-step image of any polynomial is a combination of
configurations with exactly `n` letters `V` (proof of Lemma 11.7 [lg:lem:ideal]). -/
private lemma cwa_stepSeries_mem (q : ObsPoly) : stepSeries q ∈ cwaCSer := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    exact cwaCSer.algebraMap_mem a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    simp only [stepSeries, aeval_X]
    cases v with
    | m k => exact cwa_seriesMap_mem trcFun cwa_trcFun_hom (cwa_kPowSeries_mem _)
    | f k =>
      exact mul_mem (cwa_seriesMap_mem mrkFun cwa_mrkFun_hom
        (mul_mem (mul_mem cwa_fInvSeries_mem (cwa_kPowSeries_mem _)) cwa_fInvAdjSeries_mem))
        cwa_yInvSeries_mem
    | w =>
      have h := isWeightedHomogeneous_X ℂ CfgVar.vc CfgVar.w
      exact cwa_C_mem (by simpa [CfgVar.vc, CfgVar.word] using h)
    | γ =>
      have h := isWeightedHomogeneous_X ℂ CfgVar.vc CfgVar.γ
      exact cwa_C_mem (by simpa [CfgVar.vc, CfgVar.word] using h)

private lemma cwaStarS_kAdjSeries : cwaStarS kAdjSeries = kSeries := by
  ext j
  rw [coeff_cwaStarS, kSeries, kAdjSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  split_ifs with h
  · exact wStar_wCi
  · rw [wStar_smul, wStar_mul, wStar_pow, wStar_UiV, wStar_add, wStar_one, wStar_wCi, map_pow,
      map_neg, Complex.conj_I, neg_neg]

private lemma cwaStarS_fInvSeries : cwaStarS fInvSeries = fInvAdjSeries := by
  ext j
  rw [coeff_cwaStarS, fInvSeries, fInvAdjSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    wStar_smul, wStar_pow, wStar_VU, map_pow, Complex.conj_I]

private lemma cwaStarS_fInvAdjSeries : cwaStarS fInvAdjSeries = fInvSeries := by
  ext j
  rw [coeff_cwaStarS, fInvSeries, fInvAdjSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    wStar_smul, wStar_pow, wStar_UiV, map_pow, map_neg, Complex.conj_I, neg_neg]

private lemma cwaStarS_kPowSeries {k : ℤ} (hk : k ≠ 0) :
    cwaStarS (kPowSeries k) = kPowSeries (-k) := by
  unfold kPowSeries
  by_cases h : 0 ≤ k
  · have h' : ¬ 0 ≤ -k := by omega
    rw [ite_eq_left h, ite_eq_right h', cwaStarS_pow, cwaStarS_kSeries, neg_neg]
  · have h' : 0 ≤ -k := by omega
    rw [ite_eq_right h, ite_eq_left h', cwaStarS_pow, cwaStarS_kAdjSeries]

/-- `cfgConj` on each coefficient of a series of traces. -/
private lemma cwa_map_seriesMap_trc (S : PowerSeries WordAlg) :
    PowerSeries.map cfgConj (seriesMap trcFun S) = seriesMap trcFun (cwaStarS S) := by
  ext n
  rw [PowerSeries.coeff_map, seriesMap, seriesMap, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    cwa_cfgConj_trcFun, coeff_cwaStarS]

private lemma cwa_map_seriesMap_mrk (S : PowerSeries WordAlg) :
    PowerSeries.map cfgConj (seriesMap mrkFun S) = seriesMap mrkFun (cwaStarS S) := by
  ext n
  rw [PowerSeries.coeff_map, seriesMap, seriesMap, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    cwa_cfgConj_mrkFun, coeff_cwaStarS]

private lemma cwa_map_ySeries : PowerSeries.map cfgConj ySeries = ySeries := by
  rw [ySeries, cwa_map_seriesMap_mrk, cwaStarS_mul, cwaStarS_fInvSeries, cwaStarS_fInvAdjSeries]

private lemma cwa_map_yInvSeries : PowerSeries.map cfgConj yInvSeries = yInvSeries := by
  have h1 : ySeries * yInvSeries = 1 :=
    PowerSeries.mul_invOfUnit _ 1 (by rw [cwa_constantCoeff_y]; rfl)
  have h2 : ySeries * PowerSeries.map cfgConj yInvSeries = 1 := by
    have := congrArg (PowerSeries.map cfgConj) h1
    rwa [map_mul, cwa_map_ySeries, map_one] at this
  have h3 : yInvSeries * ySeries = 1 := by rw [mul_comm]; exact h1
  exact (left_inv_eq_right_inv h3 h2).symm

private lemma cwa_stepSeries_C (b : ℂ) :
    stepSeries (C b) = PowerSeries.C (C b : CfgPoly) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, PowerSeries.algebraMap_apply]
  rfl

/-- The one-step image commutes with conjugation. -/
private lemma cwa_stepSeries_conj (p : ObsPoly) :
    stepSeries (conjPoly p) = PowerSeries.map cfgConj (stepSeries p) := by
  let f₁ : ObsPoly →+* PowerSeries CfgPoly := (stepSeries : ObsPoly →ₐ[ℂ] PowerSeries CfgPoly)
  let f₂ : ObsPoly →+* PowerSeries CfgPoly :=
    (PowerSeries.map cfgConj).comp (stepSeries : ObsPoly →ₐ[ℂ] PowerSeries CfgPoly)
  have h : f₁.comp conjPoly = f₂ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun v => ?_)
    · have e1 : conjPoly (C a) = C (starRingEnd ℂ a) := by simp [conjPoly]
      change stepSeries (conjPoly (C a)) = PowerSeries.map cfgConj (stepSeries (C a))
      rw [e1, cwa_stepSeries_C, cwa_stepSeries_C, PowerSeries.map_C]
      simp [cfgConj]
    · cases v with
      | m k =>
        simp only [f₁, f₂, RingHom.comp_apply, conjPoly, eval₂Hom_X', ObsVar.neg,
          AlgHom.coe_toRingHom, stepSeries, aeval_X]
        rw [cwa_map_seriesMap_trc, cwaStarS_kPowSeries k.2]
      | f k =>
        simp only [f₁, f₂, RingHom.comp_apply, conjPoly, eval₂Hom_X', ObsVar.neg,
          AlgHom.coe_toRingHom, stepSeries, aeval_X]
        rw [map_mul, cwa_map_seriesMap_mrk, cwa_map_yInvSeries, cwaStarS_mul, cwaStarS_mul,
          cwaStarS_fInvAdjSeries, cwaStarS_kPowSeries k.2, cwaStarS_fInvSeries]
        simp only [mul_assoc]
      | w =>
        simp only [f₁, f₂, RingHom.comp_apply, conjPoly, eval₂Hom_X', ObsVar.neg,
          AlgHom.coe_toRingHom, stepSeries, aeval_X]
        rw [PowerSeries.map_C]
        simp [cfgConj, CfgVar.adj]
      | γ =>
        simp only [f₁, f₂, RingHom.comp_apply, conjPoly, eval₂Hom_X', ObsVar.neg,
          AlgHom.coe_toRingHom, stepSeries, aeval_X]
        rw [PowerSeries.map_C]
        simp [cfgConj, CfgVar.adj]
  exact RingHom.congr_fun h p

/-! ### Series of traces -/

/-- Configurations of traces only: no marked form, no `W⁻¹`. -/
private def cwaTr : Set CfgVar := {x : CfgVar | x.isMrk = false ∧ x ≠ .w}

/-- Series over configurations of traces only. -/
private def cwaTSer : Subalgebra ℂ (PowerSeries CfgPoly) where
  carrier := {S | ∀ n, PowerSeries.coeff n S ∈ supported ℂ cwaTr}
  mul_mem' := by
    intro S T hS hT n
    rw [PowerSeries.coeff_mul]
    exact Subalgebra.sum_mem _ fun p _ => Subalgebra.mul_mem _ (hS _) (hT _)
  add_mem' := fun hS hT n => by rw [map_add]; exact add_mem (hS n) (hT n)
  algebraMap_mem' := by
    intro r n
    rw [PowerSeries.algebraMap_apply, PowerSeries.coeff_C]
    split_ifs with h
    · exact Subalgebra.algebraMap_mem _ _
    · exact zero_mem _

private lemma cwa_trcFun_mem (a : WordAlg) : trcFun a ∈ supported ℂ cwaTr := by
  induction cwa_mem_span a using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, rfl⟩ := ha
    rw [cwa_trcFun_wordOf]
    split_ifs
    · exact one_mem _
    · exact X_mem_supported.mpr (by simp [cwaTr, CfgVar.isMrk])
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Subalgebra.smul_mem _ ha _

private lemma cwa_stepSeries_trace {p : ObsPoly} (hp : p ∈ supported ℂ traceVars) :
    stepSeries p ∈ cwaTSer := by
  have h : supported ℂ traceVars ≤ cwaTSer.comap stepSeries := by
    rw [supported_eq_adjoin_X]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, hv, rfl⟩
    change stepSeries (X v) ∈ cwaTSer
    cases v with
    | m k =>
      intro n
      simp only [stepSeries, aeval_X]
      rw [seriesMap, PowerSeries.coeff_mk]
      exact cwa_trcFun_mem _
    | f k => simp [traceVars, ObsVar.idx, k.2] at hv
    | w => simp [traceVars] at hv
    | γ =>
      intro n
      simp only [stepSeries, aeval_X]
      rw [PowerSeries.coeff_C]
      split_ifs
      · exact X_mem_supported.mpr (by simp [cwaTr, CfgVar.isMrk])
      · exact zero_mem _
  exact h hp

/-! ### Odd orders -/

private lemma cwa_cfgWick_stepSeries_odd (q : ObsPoly) {n : ℕ} (hn : Odd n) :
    cfgWick (PowerSeries.coeff n (stepSeries q)) = 0 := by
  refine cfgWick_eq_zero_of_odd _ fun d hd => ?_
  rw [cwa_stepSeries_mem q n (mem_support_iff.mp hd)]
  exact hn

private lemma cwa_sum_even (g : ℕ → ObsPoly) (h : ∀ a, g (2 * a + 1) = 0) (r : ℕ) :
    ∑ k ∈ Finset.range (2 * r + 1), g k = ∑ a ∈ Finset.range (r + 1), g (2 * a) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 2 * (r + 1) + 1 = 2 * r + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, h r, add_zero, Finset.sum_range_succ _ (r + 1)]
    rfl

/-- `q_r` is `ℂ`-linear and commutes with multiplication by `g⁻²`. -/
theorem wickMap_linear (r : ℕ) (a : ℂ) (p p' : ObsPoly) :
    wickMap r (a • p + p') = a • wickMap r p + wickMap r p' ∧
      wickMap r (X .γ * p) = X .γ * wickMap r p := by
  unfold wickMap
  refine ⟨?_, ?_⟩
  · simp only [map_add, map_smul, PowerSeries.coeff_smul, ← cwaLin_apply]
  · have h : stepSeries (X .γ) = PowerSeries.C (X CfgVar.γ) := by simp [stepSeries]
    rw [map_mul, h, PowerSeries.coeff_C_mul, cwa_cfgWick_γ]

/-- `q_r` commutes with conjugation `x_k ↦ x_{−k}`. -/
theorem wickMap_conjPoly (r : ℕ) (p : ObsPoly) :
    wickMap r (conjPoly p) = conjPoly (wickMap r p) := by
  unfold wickMap
  rw [cwa_stepSeries_conj, PowerSeries.coeff_map, cfgWick_cfgConj]

/-- Lemma 11.7 (ii) [lg:lem:ideal]: the `W⁰` part of the expansion preserves multiplication. -/
theorem zeroW_wickMap_mul (r : ℕ) (p p' : ObsPoly) :
    zeroW (wickMap r (p * p')) =
      ∑ a ∈ Finset.range (r + 1), zeroW (wickMap a p) * zeroW (wickMap (r - a) p') := by
  unfold wickMap
  rw [map_mul, PowerSeries.coeff_mul, ← cwaLin_apply, map_sum, map_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [cwaLin_apply, zeroW_cfgWick_mul]
  rw [cwa_sum_even _ (fun a => by
    rw [cwa_cfgWick_stepSeries_odd p ⟨a, rfl⟩, map_zero, zero_mul])]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [show 2 * r - 2 * a = 2 * (r - a) by have := Finset.mem_range.mp ha; omega]

/-- Lemma 11.7 (iii) [lg:lem:ideal]: for `p` in the `m_k` (and `g⁻²`), `q_r(p)` is a polynomial
in the `m_k`, `W⁻¹`, `g⁻²` without odd powers of `W⁻¹`; in particular the `W⁻¹` coefficient
vanishes. -/
theorem wickMap_traceVars (r : ℕ) (p : ObsPoly) (hp : p ∈ supported ℂ traceVars) :
    wickMap r p ∈ supported ℂ (traceVars ∪ {.w}) ∧
      ∀ j : ℕ, Odd j → weightedHomogeneousComponent ObsVar.wWt j (wickMap r p) = 0 := by
  exact cfgWick_trace _ (cwa_stepSeries_trace hp _)

end LSBA
