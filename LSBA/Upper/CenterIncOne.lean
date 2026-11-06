import LSBA.Upper.CenterExpansion

/-!
# The first coefficient of the mean increment

The coefficient of `t² = h_θ² g⁻²` in the expansion of the mean increment `P_g c` as a formal
polynomial in the observables: `½ W⁻¹ + Re f_1 + Re(m_1 f_1) − ½ W⁻¹ Re f_1²`, the bracket of
(11.12) [lg:eq:c2], with `Re z` written as `(z + z̄)/2` through the independent variables of
indices `±1`.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Words -/

private lemma cio_eq_wordOf (u : List WLetter) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := WLetter) (wordOf u) =
      MonoidAlgebra.of ℂ (FreeMonoid WLetter) (FreeMonoid.ofList u) := by
  induction u with
  | nil => simp [wordOf]; rfl
  | cons l u ih =>
    simp only [wordOf, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]

private lemma cio_mrkFun_wordOf (u : List WLetter) :
    mrkFun (wordOf u) = if u = [] then 1 else X (.mrk u) := by
  simp only [mrkFun, wordFun, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, cio_eq_wordOf]
  simp [MonoidAlgebra.of_apply]
  congr

private lemma cio_wordOf_mul (u u' : List WLetter) :
    wordOf u * wordOf u' = wordOf (u ++ u') := by
  simp [wordOf]

private lemma cio_wC : wC = wordOf [.c] := by simp [wC, wordOf]
private lemma cio_wCi : wCi = wordOf [.cInv] := by simp [wCi, wordOf]
private lemma cio_wV : wV = wordOf [.v] := by simp [wV, wordOf]
private lemma cio_one : (1 : WordAlg) = wordOf [] := by simp [wordOf]

/-- The `t¹` coefficient of `Y`. -/
private lemma cio_y1 : PowerSeries.coeff 1 ySeries =
    Complex.I • X (.mrk [.v, .c]) + (-Complex.I) • X (.mrk [.cInv, .v]) := by
  simp only [ySeries, seriesMap, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_succ, fInvSeries, fInvAdjSeries]
  simp [mul_add, add_mul, cio_wC, cio_wCi, cio_wV, cio_wordOf_mul, cio_mrkFun_wordOf]
  abel

/-- The `t²` coefficient of `Y`. -/
private lemma cio_y2 : PowerSeries.coeff 2 ySeries =
    (-1 : ℂ) • X (.mrk [.v, .v]) + X (.mrk [.v, .c, .cInv, .v]) + (-1 : ℂ) • X (.mrk [.v, .v, .c]) +
      (-1 : ℂ) • X (.mrk [.v, .c, .v, .c]) + (-1 : ℂ) • X (.mrk [.cInv, .v, .v]) +
      (-1 : ℂ) • X (.mrk [.cInv, .v, .cInv, .v]) := by
  simp only [ySeries, seriesMap, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_succ, fInvSeries, fInvAdjSeries]
  simp [pow_two, mul_add, add_mul, cio_wC, cio_wCi, cio_wV, cio_wordOf_mul, cio_mrkFun_wordOf,
    smul_smul]
  abel

private lemma cio_y0 : PowerSeries.coeff 0 ySeries = 1 := by
  simp [ySeries, seriesMap, fInvSeries, fInvAdjSeries, cio_one, cio_wordOf_mul, cio_mrkFun_wordOf]

/-- The `t²` coefficient of `c = −½ log Y`: `−½ y₂ + ¼ y₁²`. -/
private lemma cio_inc2 : PowerSeries.coeff 2 incSeries =
    (-(1 / 2) : ℂ) • PowerSeries.coeff 2 ySeries +
      (1 / 4 : ℂ) • PowerSeries.coeff 1 ySeries ^ 2 := by
  rw [incSeries, PowerSeries.coeff_smul, logSeries, PowerSeries.coeff_mk, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp [pow_two, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, cio_y0]
  rw [smul_smul, ← neg_smul]
  norm_num

/-! ### The formal expectation on monomials with two letters `V` -/

private lemma cio_cfgWick_eq_sum (c : CfgPoly) {s : Finset (CfgVar →₀ ℕ)} (hs : c.support ⊆ s) :
    cfgWick c = ∑ d ∈ s, c.coeff d • cfgWickAux (Finsupp.weight CfgVar.vc d) d :=
  Finset.sum_subset hs fun d _ hd => by rw [notMem_support_iff.mp hd, zero_smul]

private lemma cio_cfgWick_add (p q : CfgPoly) : cfgWick (p + q) = cfgWick p + cfgWick q := by
  rw [cio_cfgWick_eq_sum (p + q) support_add, cio_cfgWick_eq_sum p Finset.subset_union_left,
    cio_cfgWick_eq_sum q Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by simp [add_smul]

private lemma cio_cfgWick_smul (a : ℂ) (c : CfgPoly) : cfgWick (a • c) = a • cfgWick c := by
  rw [cio_cfgWick_eq_sum (a • c) (MvPolynomial.support_smul), cfgWick, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul]

private lemma cio_cfgWick_monomial (d : CfgVar →₀ ℕ) :
    cfgWick (monomial d 1) = cfgWickAux (Finsupp.weight CfgVar.vc d) d := by
  rw [cio_cfgWick_eq_sum _ support_monomial_subset, Finset.sum_singleton, coeff_monomial,
    ite_eq_left rfl, one_smul]

private lemma cio_cfgPick_mem {d : CfgVar →₀ ℕ}
    (h : (d.support.filter fun x => 0 < x.vc).Nonempty) :
    cfgPick d ∈ d.support ∧ 0 < (cfgPick d).vc := by
  have := (Classical.choose_spec
    ((d.support.filter fun x => 0 < x.vc).exists_min_image CfgVar.key h)).1
  simp only [cfgPick, h, ↓reduceDIte]
  exact Finset.mem_filter.mp this

/-- A monomial without `V` is the product of its factors. -/
private lemma cio_aux_base (n : ℕ) {d : CfgVar →₀ ℕ} (hd : ∀ x ∈ d.support, x.vc = 0) :
    cfgWickAux n d = d.prod fun x k => x.base ^ k := by
  have h : ¬ (d.support.filter fun x => 0 < x.vc).Nonempty := by
    rintro ⟨x, hx⟩
    rw [Finset.mem_filter] at hx
    exact absurd (hd x hx.1) (Nat.pos_iff_ne_zero.mp hx.2)
  cases n with
  | zero => rfl
  | succ n => rw [cfgWickAux, ite_eq_right h]

/-- Two factors without `V`. -/
private lemma cio_aux_two (n : ℕ) {a b : CfgVar} (ha : a.vc = 0) (hb : b.vc = 0) :
    cfgWickAux n (Finsupp.single a 1 + Finsupp.single b 1) = a.base * b.base := by
  rw [cio_aux_base n]
  · rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp
  · intro x hx
    rcases Finset.mem_union.mp (Finsupp.support_add hx) with h | h <;>
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)] <;> assumption

private lemma cio_support_single (x : CfgVar) {k : ℕ} (hk : k ≠ 0) :
    (Finsupp.single x k).support = {x} := Finsupp.support_single x hk

/-- One factor with `V`: only self-pairs. -/
private lemma cio_aux_single (n : ℕ) {φ : CfgVar} (hφ : 0 < φ.vc) :
    cfgWickAux (n + 1) (Finsupp.single φ 1) =
      ((vPos (φ.word.drop (φ.word.idxOf .v + 1))).map fun j =>
        cfgWickAux n (selfPair φ j)).sum := by
  have hne : ((Finsupp.single φ 1).support.filter fun x => 0 < x.vc).Nonempty :=
    ⟨φ, Finset.mem_filter.mpr ⟨by rw [cio_support_single φ one_ne_zero]; simp, hφ⟩⟩
  have hp : cfgPick (Finsupp.single φ 1) = φ := by
    have := (cio_cfgPick_mem hne).1
    rwa [cio_support_single φ one_ne_zero, Finset.mem_singleton] at this
  rw [cfgWickAux, ite_eq_left hne, hp, tsub_self]
  simp

/-- The square of a factor with `V`. -/
private lemma cio_aux_sq (n : ℕ) {φ : CfgVar} (hφ : 0 < φ.vc) :
    cfgWickAux (n + 1) (Finsupp.single φ 2) =
      ((vPos (φ.word.drop (φ.word.idxOf .v + 1))).map fun j =>
        cfgWickAux n (Finsupp.single φ 1 + selfPair φ j)).sum +
      ((vPos φ.word).map fun j =>
        X ObsVar.w ^ (crossPair φ φ j).1 * cfgWickAux n (crossPair φ φ j).2).sum := by
  have hne : ((Finsupp.single φ 2).support.filter fun x => 0 < x.vc).Nonempty :=
    ⟨φ, Finset.mem_filter.mpr ⟨by rw [cio_support_single φ two_ne_zero]; simp, hφ⟩⟩
  have hp : cfgPick (Finsupp.single φ 2) = φ := by
    have := (cio_cfgPick_mem hne).1
    rwa [cio_support_single φ two_ne_zero, Finset.mem_singleton] at this
  have h21 : Finsupp.single φ 2 - Finsupp.single φ 1 = Finsupp.single φ 1 := by
    rw [← Finsupp.single_tsub]
  rw [cfgWickAux, ite_eq_left hne, hp, h21, cio_support_single φ one_ne_zero, Finset.sum_singleton,
    tsub_self]
  simp

/-- Two different factors with `V`, for either choice of the pivot. -/
private lemma cio_aux_pair (n : ℕ) {φ ψ : CfgVar} (hne' : φ ≠ ψ) (hφ : 0 < φ.vc) :
    ∃ p q : CfgVar, ((p = φ ∧ q = ψ) ∨ (p = ψ ∧ q = φ)) ∧
      cfgWickAux (n + 1) (Finsupp.single φ 1 + Finsupp.single ψ 1) =
        ((vPos (p.word.drop (p.word.idxOf .v + 1))).map fun j =>
          cfgWickAux n (Finsupp.single q 1 + selfPair p j)).sum +
        ((vPos q.word).map fun j =>
          X ObsVar.w ^ (crossPair p q j).1 * cfgWickAux n (crossPair p q j).2).sum := by
  have hsupp : (Finsupp.single φ 1 + Finsupp.single ψ 1).support = {φ, ψ} := by
    rw [Finsupp.support_add_eq, cio_support_single φ one_ne_zero,
      cio_support_single ψ one_ne_zero]
    · rfl
    · rw [cio_support_single φ one_ne_zero, cio_support_single ψ one_ne_zero]
      simpa using hne'
  have hne : ((Finsupp.single φ 1 + Finsupp.single ψ 1).support.filter
      fun x : CfgVar => 0 < x.vc).Nonempty :=
    ⟨φ, Finset.mem_filter.mpr ⟨by rw [hsupp]; simp, hφ⟩⟩
  have hmem := (cio_cfgPick_mem hne).1
  rw [hsupp, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hp | hp
  · refine ⟨φ, ψ, Or.inl ⟨rfl, rfl⟩, ?_⟩
    rw [cfgWickAux, ite_eq_left hne, hp, add_tsub_cancel_left, cio_support_single ψ one_ne_zero,
      Finset.sum_singleton, tsub_self]
    simp [add_comm]
  · refine ⟨ψ, φ, Or.inr ⟨rfl, rfl⟩, ?_⟩
    rw [cfgWickAux, ite_eq_left hne, hp, add_tsub_cancel_right, cio_support_single φ one_ne_zero,
      Finset.sum_singleton, tsub_self]
    simp [add_comm]

private lemma cio_wick_X (x : CfgVar) :
    cfgWick (X x) = cfgWickAux x.vc (Finsupp.single x 1) := by
  rw [X, cio_cfgWick_monomial, Finsupp.weight_single, one_smul]

private lemma cio_wick_sq (x : CfgVar) :
    cfgWick (X x ^ 2) = cfgWickAux (x.vc + x.vc) (Finsupp.single x 2) := by
  rw [X_pow_eq_monomial, cio_cfgWick_monomial, Finsupp.weight_single, two_smul]

private lemma cio_wick_mul (x y : CfgVar) :
    cfgWick (X x * X y) = cfgWickAux (x.vc + y.vc) (Finsupp.single x 1 + Finsupp.single y 1) := by
  rw [X, X, monomial_mul_monomial, one_mul, cio_cfgWick_monomial, map_add, Finsupp.weight_single,
    Finsupp.weight_single, one_smul, one_smul]

/-! ### The marked forms of `y₂` and the products of `y₁²` -/

private lemma cio_mVar_zero : mVar 0 = 1 := by simp [mVar]

private lemma cio_fVar_zero : fVar 0 = 1 := by simp [fVar]

/-- The expectation of a marked form with two letters `V`, through its unique self-pair. -/
private lemma cio_wick_two (u : List WLetter) (hu : (CfgVar.mrk u).vc = 1 + 1) :
    cfgWick (X (.mrk u)) =
      ((vPos (u.drop (u.idxOf .v + 1))).map fun j =>
        cfgWickAux 1 (selfPair (.mrk u) j)).sum := by
  rw [cio_wick_X, hu, cio_aux_single _ (by rw [hu]; norm_num)]
  rfl

private lemma cio_w_vv : cfgWick (X (.mrk [.v, .v])) = 1 := by
  rw [cio_wick_two _ rfl]
  simp [vPos, List.range_succ, selfPair, CfgVar.word, CfgVar.isMrk]
  rw [cio_aux_two _ rfl rfl]
  simp [CfgVar.base, wordExp, cio_mVar_zero, cio_fVar_zero]

private lemma cio_w_vcciv : cfgWick (X (.mrk [.v, .c, .cInv, .v])) = 1 := by
  rw [cio_wick_two _ rfl]
  simp [vPos, List.range_succ, selfPair, CfgVar.word, CfgVar.isMrk]
  rw [cio_aux_two _ rfl rfl]
  simp [CfgVar.base, wordExp, cio_mVar_zero, cio_fVar_zero]

private lemma cio_w_vvc : cfgWick (X (.mrk [.v, .v, .c])) = fVar 1 := by
  rw [cio_wick_two _ rfl]
  simp [vPos, List.range_succ, selfPair, CfgVar.word, CfgVar.isMrk]
  rw [cio_aux_two _ rfl rfl]
  simp [CfgVar.base, wordExp, cio_mVar_zero]

private lemma cio_w_vcvc : cfgWick (X (.mrk [.v, .c, .v, .c])) = mVar 1 * fVar 1 := by
  rw [cio_wick_two _ rfl]
  simp [vPos, List.range_succ, selfPair, CfgVar.word, CfgVar.isMrk]
  rw [cio_aux_two _ rfl rfl]
  simp [CfgVar.base, wordExp]

private lemma cio_w_civv : cfgWick (X (.mrk [.cInv, .v, .v])) = fVar (-1) := by
  rw [cio_wick_two _ rfl]
  simp [vPos, List.range_succ, selfPair, CfgVar.word, CfgVar.isMrk]
  rw [cio_aux_two _ rfl rfl]
  simp [CfgVar.base, wordExp, cio_mVar_zero]

private lemma cio_w_civciv : cfgWick (X (.mrk [.cInv, .v, .cInv, .v])) = mVar (-1) * fVar (-1) := by
  rw [cio_wick_two _ rfl]
  simp [vPos, List.range_succ, selfPair, CfgVar.word, CfgVar.isMrk]
  rw [cio_aux_two _ rfl rfl]
  simp [CfgVar.base, wordExp]

private lemma cio_w_sq_vc : cfgWick (X (.mrk [.v, .c]) ^ 2) = X .w * fVar 1 ^ 2 := by
  rw [cio_wick_sq, show (CfgVar.mrk [.v, .c]).vc + (CfgVar.mrk [.v, .c]).vc = 1 + 1 from rfl,
    cio_aux_sq _ (by decide)]
  simp [vPos, List.range_succ, crossPair, CfgVar.word, CfgVar.isMrk]
  rw [cio_aux_two _ rfl rfl]
  simp [CfgVar.base, wordExp, pow_two]

private lemma cio_w_sq_civ : cfgWick (X (.mrk [.cInv, .v]) ^ 2) = X .w * fVar (-1) ^ 2 := by
  rw [cio_wick_sq, show (CfgVar.mrk [.cInv, .v]).vc + (CfgVar.mrk [.cInv, .v]).vc = 1 + 1 from rfl,
    cio_aux_sq _ (by decide)]
  simp [vPos, List.range_succ, crossPair, CfgVar.word, CfgVar.isMrk]
  rw [cio_aux_two _ rfl rfl]
  simp [CfgVar.base, wordExp, pow_two]

private lemma cio_w_mul : cfgWick (X (.mrk [.v, .c]) * X (.mrk [.cInv, .v])) = X .w := by
  rw [cio_wick_mul, show (CfgVar.mrk [.v, .c]).vc + (CfgVar.mrk [.cInv, .v]).vc = 1 + 1 from rfl]
  obtain ⟨p, q, hpq, h⟩ := cio_aux_pair 1 (φ := .mrk [.v, .c]) (ψ := .mrk [.cInv, .v])
    (by simp) (by decide)
  rw [h]
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [vPos, List.range_succ, crossPair, CfgVar.word, CfgVar.isMrk]
    rw [cio_aux_two _ rfl rfl]
    simp [CfgVar.base, wordExp, cio_fVar_zero]
  · simp [vPos, List.range_succ, crossPair, CfgVar.word, CfgVar.isMrk]
    rw [cio_aux_two _ rfl rfl]
    simp [CfgVar.base, wordExp, cio_fVar_zero]

private lemma cio_sq_expand (A B : CfgPoly) :
    (Complex.I • A + (-Complex.I) • B) ^ 2 =
      (-1 : ℂ) • A ^ 2 + (2 : ℂ) • (A * B) + (-1 : ℂ) • B ^ 2 := by
  simp only [add_sq, two_mul, add_mul, smul_pow, mul_smul_comm, smul_mul_assoc]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq]

/-- The order-`t²` coefficient of `P_g c` as a formal polynomial ((11.12) [lg:eq:c2]):
`c_1 = ½ w + ½ (f_1 + f_{−1}) + ½ (m_1 f_1 + m_{−1} f_{−1}) − ¼ w (f_1² + f_{−1}²)`. -/
theorem incWick_one :
    incWick 1 = C (1 / 2) * X .w + C (1 / 2) * (fVar 1 + fVar (-1)) +
      C (1 / 2) * (mVar 1 * fVar 1 + mVar (-1) * fVar (-1)) -
      C (1 / 4) * X .w * (fVar 1 ^ 2 + fVar (-1) ^ 2) := by
  rw [incWick, show 2 * 1 = 2 from rfl, cio_inc2, cio_y1, cio_y2, cio_sq_expand]
  simp only [cio_cfgWick_add, cio_cfgWick_smul, cio_w_vv, cio_w_vcciv, cio_w_vvc, cio_w_vcvc,
    cio_w_civv, cio_w_civciv, cio_w_sq_vc, cio_w_sq_civ, cio_w_mul]
  simp only [← smul_eq_C_mul, smul_mul_assoc, mul_add, smul_add]
  module

end LSBA
