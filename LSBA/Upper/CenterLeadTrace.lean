import LSBA.Upper.CenterExpansion

/-!
# Uniform polynomial expansions: the leading trace coefficients

The order-`g⁻²` `W⁰` coefficient of the unrotated transition of `m_k`, `k ≥ 1` (Section 11.3.3
[lg:sec:general-state]): `𝒟_1 m_k = −k(1 + m_1)τ_k − (k/2) Σ_{d=1}^{k−1} τ_d τ_{k−d}` with
`τ_d = m_{d−1} + 2m_d + m_{d+1}` (`k = 1` is (11.20) [uvg:eq:mmean]), and its part of parity `k`,
which is (11.52) [lg:eq:center-trace].
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `τ_d = m_{d−1} + 2 m_d + m_{d+1}`. -/
def traceTau (d : ℤ) : ObsPoly := mVar (d - 1) + 2 * mVar d + mVar (d + 1)

/-- `𝒟_1 m_k = −k(1 + m_1)τ_k − (k/2) Σ_{d=1}^{k−1} τ_d τ_{k−d}` (Section 11.3.3
[lg:sec:general-state]). -/
def diffTrace (k : ℕ) : ObsPoly :=
  -(k : ObsPoly) * (1 + mVar 1) * traceTau k -
    C ((k : ℂ) / 2) * ∑ d ∈ Finset.Icc 1 (k - 1), traceTau d * traceTau ((k : ℤ) - d)

/-- (11.52) [lg:eq:center-trace]: `𝓛 m_k = −3k m_k − 3k Σ_{a=1}^{k−1} m_a m_{k−a}
− (k/2) Σ_{a=0}^{k−2} m_a m_{k−2−a} − (k/2) Σ_{a=1}^{k+1} m_a m_{k+2−a}`. -/
def centerTrace (k : ℕ) : ObsPoly :=
  -C (3 * (k : ℂ)) * mVar k -
    C (3 * (k : ℂ)) * ∑ a ∈ Finset.Icc 1 (k - 1), mVar a * mVar ((k : ℤ) - a) -
    C ((k : ℂ) / 2) * ∑ a ∈ Finset.range (k - 1), mVar a * mVar ((k : ℤ) - 2 - a) -
    C ((k : ℂ) / 2) * ∑ a ∈ Finset.Icc 1 (k + 1), mVar a * mVar ((k : ℤ) + 2 - a)

/-! ### Words -/

private lemma clt_eq_wordOf (u : List WLetter) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := WLetter) (wordOf u) =
      MonoidAlgebra.of ℂ (FreeMonoid WLetter) (FreeMonoid.ofList u) := by
  induction u with
  | nil => simp [wordOf]; rfl
  | cons l u ih =>
    simp only [wordOf, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]

private lemma clt_trcFun_wordOf (u : List WLetter) :
    trcFun (wordOf u) = if u = [] then 1 else X (.trc u) := by
  simp only [trcFun, wordFun, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, clt_eq_wordOf]
  simp [MonoidAlgebra.of_apply]
  congr

private lemma clt_wordOf_append (u u' : List WLetter) :
    wordOf (u ++ u') = wordOf u * wordOf u' := by
  simp [wordOf]

private lemma clt_wordOf_replicate (l : WLetter) (n : ℕ) :
    wordOf (List.replicate n l) = FreeAlgebra.ι ℂ l ^ n := by
  simp [wordOf, List.map_replicate, List.prod_replicate]

private lemma clt_wordOf_cons (l : WLetter) (u : List WLetter) :
    wordOf (l :: u) = FreeAlgebra.ι ℂ l * wordOf u := by
  simp [wordOf]

/-! ### The formal expectation on monomials with two letters `V` -/

private lemma clt_cfgWick_eq_sum (c : CfgPoly) {s : Finset (CfgVar →₀ ℕ)} (hs : c.support ⊆ s) :
    cfgWick c = ∑ d ∈ s, c.coeff d • cfgWickAux (Finsupp.weight CfgVar.vc d) d :=
  Finset.sum_subset hs fun d _ hd => by rw [notMem_support_iff.mp hd, zero_smul]

private lemma clt_cfgWick_add (p q : CfgPoly) : cfgWick (p + q) = cfgWick p + cfgWick q := by
  rw [clt_cfgWick_eq_sum (p + q) support_add, clt_cfgWick_eq_sum p Finset.subset_union_left,
    clt_cfgWick_eq_sum q Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by simp [add_smul]

private lemma clt_cfgWick_smul (a : ℂ) (c : CfgPoly) : cfgWick (a • c) = a • cfgWick c := by
  rw [clt_cfgWick_eq_sum (a • c) (MvPolynomial.support_smul), cfgWick, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul]

private lemma clt_cfgWick_monomial (d : CfgVar →₀ ℕ) :
    cfgWick (monomial d 1) = cfgWickAux (Finsupp.weight CfgVar.vc d) d := by
  rw [clt_cfgWick_eq_sum _ support_monomial_subset, Finset.sum_singleton, coeff_monomial,
    ite_eq_left rfl, one_smul]

/-- `cfgWick` as a linear map. -/
private def clt_wickL : CfgPoly →ₗ[ℂ] ObsPoly where
  toFun := cfgWick
  map_add' := clt_cfgWick_add
  map_smul' := fun a c => clt_cfgWick_smul a c

/-- The formal expectation of the normalized trace of a word, linear in the word. -/
private def clt_tw : WordAlg →ₗ[ℂ] ObsPoly := clt_wickL ∘ₗ trcFun

private lemma clt_cfgPick_mem {d : CfgVar →₀ ℕ}
    (h : (d.support.filter fun x => 0 < x.vc).Nonempty) :
    cfgPick d ∈ d.support ∧ 0 < (cfgPick d).vc := by
  have := (Classical.choose_spec
    ((d.support.filter fun x => 0 < x.vc).exists_min_image CfgVar.key h)).1
  simp only [cfgPick, h, ↓reduceDIte]
  exact Finset.mem_filter.mp this

private lemma clt_aux_base (n : ℕ) {d : CfgVar →₀ ℕ} (hd : ∀ x ∈ d.support, x.vc = 0) :
    cfgWickAux n d = d.prod fun x k => x.base ^ k := by
  have h : ¬ (d.support.filter fun x => 0 < x.vc).Nonempty := by
    rintro ⟨x, hx⟩
    rw [Finset.mem_filter] at hx
    exact absurd (hd x hx.1) (Nat.pos_iff_ne_zero.mp hx.2)
  cases n with
  | zero => rfl
  | succ n => rw [cfgWickAux, ite_eq_right h]

private lemma clt_aux_two (n : ℕ) {a b : CfgVar} (ha : a.vc = 0) (hb : b.vc = 0) :
    cfgWickAux n (Finsupp.single a 1 + Finsupp.single b 1) = a.base * b.base := by
  rw [clt_aux_base n]
  · rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp
  · intro x hx
    rcases Finset.mem_union.mp (Finsupp.support_add hx) with h | h <;>
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)] <;> assumption

private lemma clt_aux_single (n : ℕ) {φ : CfgVar} (hφ : 0 < φ.vc) :
    cfgWickAux (n + 1) (Finsupp.single φ 1) =
      ((vPos (φ.word.drop (φ.word.idxOf .v + 1))).map fun j =>
        cfgWickAux n (selfPair φ j)).sum := by
  have hs : (Finsupp.single φ 1).support = {φ} := Finsupp.support_single φ one_ne_zero
  have hne : ((Finsupp.single φ 1).support.filter fun x => 0 < x.vc).Nonempty :=
    ⟨φ, Finset.mem_filter.mpr ⟨by rw [hs]; simp, hφ⟩⟩
  have hp : cfgPick (Finsupp.single φ 1) = φ := by
    have := (clt_cfgPick_mem hne).1
    rwa [hs, Finset.mem_singleton] at this
  rw [cfgWickAux, ite_eq_left hne, hp, tsub_self]
  simp

private lemma clt_wick_X (x : CfgVar) :
    cfgWick (X x) = cfgWickAux x.vc (Finsupp.single x 1) := by
  rw [X, clt_cfgWick_monomial, Finsupp.weight_single, one_smul]

/-- The expectation of a trace with two letters `V`, through its unique self-pair. -/
private lemma clt_wick_two (u : List WLetter) (hu : (CfgVar.trc u).vc = 1 + 1) :
    cfgWick (X (.trc u)) =
      ((vPos (u.drop (u.idxOf .v + 1))).map fun j =>
        cfgWickAux 1 (selfPair (.trc u) j)).sum := by
  rw [clt_wick_X, hu, clt_aux_single _ (by rw [hu]; norm_num)]
  rfl

private lemma clt_vPos_two {B₁ B₂ : List WLetter} (h₁ : WLetter.v ∉ B₁) (h₂ : WLetter.v ∉ B₂) :
    vPos (B₁ ++ .v :: B₂) = [B₁.length] := by
  have hnd : (vPos (B₁ ++ .v :: B₂)).Nodup := (List.nodup_range).filter _
  have hmem : ∀ j, j ∈ vPos (B₁ ++ .v :: B₂) ↔ j = B₁.length := by
    intro j
    simp only [vPos, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨-, hj⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [List.getElem?_append_left hlt] at hj
        exact h₁ (List.mem_of_getElem? hj)
      · rw [List.getElem?_append_right hgt.le] at hj
        obtain ⟨m, hm⟩ : ∃ m, j - B₁.length = m + 1 := ⟨j - B₁.length - 1, by omega⟩
        rw [hm, List.getElem?_cons_succ] at hj
        exact h₂ (List.mem_of_getElem? hj)
    · rintro rfl
      refine ⟨by simp, ?_⟩
      simp
  exact List.perm_singleton.mp
    ((List.perm_ext_iff_of_nodup hnd (List.nodup_singleton _)).mpr fun j => by
      rw [hmem, List.mem_singleton])

/-- The word `C^i V C^j V C^l`. -/
private def clt_w3 (i j l : ℕ) : List WLetter :=
  List.replicate i WLetter.c ++ WLetter.v :: (List.replicate j WLetter.c ++ WLetter.v ::
    List.replicate l WLetter.c)

/-- The expectation of the trace of `C^i V C^j V C^l`: `m_j m_{i+l}`. -/
private lemma clt_wick_word (i j l : ℕ) :
    cfgWick (X (.trc (clt_w3 i j l))) = mVar j * mVar ((i + l : ℕ) : ℤ) := by
  have hA : WLetter.v ∉ List.replicate i WLetter.c := by simp [List.mem_replicate]
  have hB : WLetter.v ∉ List.replicate j WLetter.c := by simp [List.mem_replicate]
  have hC : WLetter.v ∉ List.replicate l WLetter.c := by simp [List.mem_replicate]
  have hvc : (CfgVar.trc (clt_w3 i j l)).vc = 1 + 1 := by
    simp [clt_w3, CfgVar.vc, CfgVar.word, List.count_replicate]
  have hidx : (clt_w3 i j l).idxOf .v = i := by
    rw [clt_w3, List.idxOf_append_of_notMem hA]
    simp
  rw [clt_wick_two _ hvc, hidx]
  have hdrop : (clt_w3 i j l).drop (i + 1) =
      List.replicate j WLetter.c ++ WLetter.v :: List.replicate l WLetter.c := by
    rw [clt_w3, List.drop_append]
    simp
  rw [hdrop, clt_vPos_two hB hC]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [selfPair, CfgVar.word, CfgVar.isMrk, hidx, hdrop, Bool.false_eq_true, ↓reduceIte,
    List.length_replicate]
  have e1 : List.take j (List.replicate j WLetter.c ++ WLetter.v :: List.replicate l WLetter.c) =
      List.replicate j WLetter.c := List.take_left' (by simp)
  have e2 : List.take i (clt_w3 i j l) = List.replicate i WLetter.c := by
    rw [clt_w3]; exact List.take_left' (by simp)
  have e3 : List.drop (j + 1)
      (List.replicate j WLetter.c ++ WLetter.v :: List.replicate l WLetter.c) =
        List.replicate l WLetter.c := by
    rw [List.drop_append]; simp
  rw [e1, e2, e3, clt_aux_two 1 (by simp [CfgVar.vc, CfgVar.word, List.count_replicate])
    (by simp [CfgVar.vc, CfgVar.word, List.count_replicate])]
  simp [CfgVar.base, wordExp, List.count_replicate]

/-! ### Words with two letters `V` between polynomials in `C` -/

/-- The linear functional `C^n ↦ m_n` on polynomials in `C`. -/
private def clt_mu : Polynomial ℂ →ₗ[ℂ] ObsPoly :=
  Polynomial.lsum fun n => LinearMap.toSpanSingleton ℂ ObsPoly (mVar n)

private lemma clt_mu_monomial (n : ℕ) (a : ℂ) :
    clt_mu (Polynomial.monomial n a) = a • mVar n := by
  simp [clt_mu, Polynomial.lsum_apply]

private lemma clt_mu_X_pow (n : ℕ) : clt_mu (Polynomial.X ^ n) = mVar n := by
  rw [← Polynomial.monomial_one_right_eq_X_pow, clt_mu_monomial, one_smul]

private lemma clt_tw_wordOf (u : List WLetter) (hu : u ≠ []) :
    clt_tw (wordOf u) = cfgWick (X (.trc u)) := by
  simp [clt_tw, clt_wickL, clt_trcFun_wordOf, hu]

private lemma clt_wordOf_w3 (i j l : ℕ) :
    wordOf (clt_w3 i j l) = wC ^ i * wV * wC ^ j * wV * wC ^ l := by
  simp [clt_w3, clt_wordOf_append, clt_wordOf_cons, clt_wordOf_replicate, wC, wV, mul_assoc]

private lemma clt_tw_w3 (i j l : ℕ) :
    clt_tw (wC ^ i * wV * wC ^ j * wV * wC ^ l) = mVar (j : ℤ) * mVar ((i + l : ℕ) : ℤ) := by
  rw [← clt_wordOf_w3, clt_tw_wordOf _ (by simp [clt_w3]), clt_wick_word]

/-- The expectation of a word `p(C) V q(C) V r(C)`: `μ(q) μ(p r)`. -/
private lemma clt_T3 (p q r : Polynomial ℂ) :
    clt_tw (Polynomial.aeval wC p * wV * Polynomial.aeval wC q * wV * Polynomial.aeval wC r) =
      clt_mu q * clt_mu (p * r) := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ => simp only [map_add, add_mul, mul_add, h₁, h₂]
  | monomial i a =>
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ h₁ h₂ => simp only [map_add, add_mul, mul_add, h₁, h₂]
    | monomial j b =>
      induction r using Polynomial.induction_on' with
      | add r₁ r₂ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂]
      | monomial l c =>
        simp only [Polynomial.aeval_monomial, ← Algebra.smul_def, smul_mul_assoc, mul_smul_comm,
          smul_smul, map_smul, clt_tw_w3, Polynomial.monomial_mul_monomial, clt_mu_monomial,
          smul_mul_assoc, mul_smul_comm, Nat.cast_add]
        rw [show c * (b * a) = a * c * b from by ring]

/-- The word `U V U`, `U = 1 + C`. -/
private def clt_a1 : WordAlg := (1 + wC) * wV * (1 + wC)

/-- The word `U V U V U`, `U = 1 + C`. -/
private def clt_a2 : WordAlg := (1 + wC) * wV * (1 + wC) * wV * (1 + wC)

/-- `m_n + 2 m_{n+1} + m_{n+2} = τ_{n+1}`. -/
private def clt_t (n : ℕ) : ObsPoly :=
  mVar (n : ℤ) + 2 * mVar ((n : ℤ) + 1) + mVar ((n : ℤ) + 2)

private lemma clt_mVar_zero : mVar 0 = 1 := by simp [mVar]

private lemma clt_mu_U : clt_mu (1 + Polynomial.X) = 1 + mVar 1 := by
  have h : (1 + Polynomial.X : Polynomial ℂ) = Polynomial.X ^ 0 + Polynomial.X ^ 1 := by simp
  rw [h, map_add, clt_mu_X_pow, clt_mu_X_pow]
  simp [clt_mVar_zero]

private lemma clt_mu_tau (n : ℕ) :
    clt_mu (Polynomial.X ^ n * (1 + Polynomial.X) ^ 2) = clt_t n := by
  have h : (Polynomial.X ^ n * (1 + Polynomial.X) ^ 2 : Polynomial ℂ) =
      Polynomial.X ^ n + (2 : ℂ) • Polynomial.X ^ (n + 1) + Polynomial.X ^ (n + 2) := by
    rw [Polynomial.smul_eq_C_mul]
    simp only [pow_succ, map_ofNat]
    ring
  rw [h, map_add, map_add, map_smul, clt_mu_X_pow, clt_mu_X_pow, clt_mu_X_pow, clt_t]
  push_cast
  simp [two_mul, two_smul]

private lemma clt_tw_a2 (r s : ℕ) :
    clt_tw (wC ^ r * clt_a2 * wC ^ s) = (1 + mVar 1) * clt_t (r + s) := by
  have h : wC ^ r * clt_a2 * wC ^ s =
      Polynomial.aeval (R := ℂ) wC (Polynomial.X ^ r * (1 + Polynomial.X)) * wV *
        Polynomial.aeval (R := ℂ) wC (1 + Polynomial.X) * wV *
        Polynomial.aeval (R := ℂ) wC ((1 + Polynomial.X) * Polynomial.X ^ s) := by
    simp [clt_a2, mul_assoc]
  rw [h, clt_T3, clt_mu_U, show (Polynomial.X ^ r * (1 + Polynomial.X) *
    ((1 + Polynomial.X) * Polynomial.X ^ s) : Polynomial ℂ) =
      Polynomial.X ^ (r + s) * (1 + Polynomial.X) ^ 2 by ring, clt_mu_tau]

private lemma clt_tw_a1a1 (i j l : ℕ) :
    clt_tw (wC ^ i * clt_a1 * wC ^ j * clt_a1 * wC ^ l) = clt_t j * clt_t (i + l) := by
  have h : wC ^ i * clt_a1 * wC ^ j * clt_a1 * wC ^ l =
      Polynomial.aeval (R := ℂ) wC (Polynomial.X ^ i * (1 + Polynomial.X)) * wV *
        Polynomial.aeval (R := ℂ) wC ((1 + Polynomial.X) * Polynomial.X ^ j * (1 + Polynomial.X)) *
        wV * Polynomial.aeval (R := ℂ) wC ((1 + Polynomial.X) * Polynomial.X ^ l) := by
    simp [clt_a1, mul_assoc]
  rw [h, clt_T3, show ((1 + Polynomial.X) * Polynomial.X ^ j * (1 + Polynomial.X) :
    Polynomial ℂ) = Polynomial.X ^ j * (1 + Polynomial.X) ^ 2 by ring,
    show (Polynomial.X ^ i * (1 + Polynomial.X) * ((1 + Polynomial.X) * Polynomial.X ^ l) :
    Polynomial ℂ) = Polynomial.X ^ (i + l) * (1 + Polynomial.X) ^ 2 by ring,
    clt_mu_tau, clt_mu_tau]

/-! ### Coefficients of the powers of `K̃` -/

private lemma clt_K0 : PowerSeries.coeff 0 kSeries = wC := by simp [kSeries]

private lemma clt_K1 : PowerSeries.coeff 1 kSeries = Complex.I • clt_a1 := by
  simp [kSeries, clt_a1, mul_assoc]

private lemma clt_K2 : PowerSeries.coeff 2 kSeries = (-1 : ℂ) • clt_a2 := by
  simp [kSeries, clt_a2, mul_assoc, pow_two]

private lemma clt_Kpow0 (n : ℕ) : PowerSeries.coeff 0 (kSeries ^ n) = wC ^ n := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, clt_K0]

private lemma clt_coeff1_mul (A B : PowerSeries WordAlg) :
    PowerSeries.coeff 1 (A * B) = PowerSeries.coeff 0 A * PowerSeries.coeff 1 B +
      PowerSeries.coeff 1 A * PowerSeries.coeff 0 B := by
  rw [PowerSeries.coeff_mul]
  simp [Finset.Nat.sum_antidiagonal_succ]

private lemma clt_coeff2_mul (A B : PowerSeries WordAlg) :
    PowerSeries.coeff 2 (A * B) = PowerSeries.coeff 0 A * PowerSeries.coeff 2 B +
      PowerSeries.coeff 1 A * PowerSeries.coeff 1 B +
        PowerSeries.coeff 2 A * PowerSeries.coeff 0 B := by
  rw [PowerSeries.coeff_mul]
  simp [Finset.Nat.sum_antidiagonal_succ, add_assoc]

private lemma clt_Kpow1 (n : ℕ) : PowerSeries.coeff 1 (kSeries ^ (n + 1)) =
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, wC ^ p.1 * (Complex.I • clt_a1) * wC ^ p.2 := by
  induction n with
  | zero => simp [clt_K1]
  | succ n ih =>
    rw [pow_succ, clt_coeff1_mul, Finset.Nat.sum_antidiagonal_succ', ih, clt_Kpow0, clt_K0,
      clt_K1]
    simp [Finset.sum_mul, pow_succ, mul_assoc]

private lemma clt_pair_step (n r s : ℕ) :
    ∑ b ∈ range (n + 1), ((b : ObsPoly) + 1) * (clt_t (n - b) * clt_t (b + r + s)) =
      ∑ b ∈ range n, ((b : ObsPoly) + 1) * (clt_t (n - 1 - b) * clt_t (b + r + (s + 1))) +
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, clt_t p.2 * clt_t (r + p.1 + s) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => clt_t j * clt_t (r + i + s)) n]
  have h1 : ∑ b ∈ range (n + 1), ((b : ObsPoly) + 1) * (clt_t (n - b) * clt_t (b + r + s)) =
      ∑ b ∈ range (n + 1), (b : ObsPoly) * (clt_t (n - b) * clt_t (b + r + s)) +
        ∑ b ∈ range (n + 1), (clt_t (n - b) * clt_t (b + r + s)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h1, Finset.sum_range_succ' (fun b => (b : ObsPoly) * (clt_t (n - b) * clt_t (b + r + s)))]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have h2 : ∑ b ∈ range n, ((b + 1 : ℕ) : ObsPoly) *
        (clt_t (n - (b + 1)) * clt_t (b + 1 + r + s)) =
      ∑ b ∈ range n, ((b : ObsPoly) + 1) * (clt_t (n - 1 - b) * clt_t (b + r + (s + 1))) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Nat.cast_add, Nat.cast_one, show n - (b + 1) = n - 1 - b by omega,
      show b + 1 + r + s = b + r + (s + 1) by omega]
  rw [h2, add_right_inj]
  refine Finset.sum_congr rfl fun b _ => ?_
  show clt_t (n - b) * clt_t (b + r + s) = clt_t (n - b) * clt_t (r + b + s)
  rw [Nat.add_comm b r]

/-- The expectation of the `t²` coefficient of `K̃^{n+1}`, between the powers `C^r`, `C^s`. -/
private lemma clt_E2 (n : ℕ) : ∀ r s : ℕ,
    clt_tw (wC ^ r * PowerSeries.coeff 2 (kSeries ^ (n + 1)) * wC ^ s) =
      -(((n : ObsPoly) + 1) * (1 + mVar 1) * clt_t (n + r + s)) -
        ∑ b ∈ range n, ((b : ObsPoly) + 1) * (clt_t (n - 1 - b) * clt_t (b + r + s)) := by
  induction n with
  | zero =>
    intro r s
    simp [clt_K2, clt_tw_a2, add_assoc]
  | succ n ih =>
    intro r s
    rw [pow_succ, clt_coeff2_mul, clt_Kpow0, clt_Kpow1, clt_K0, clt_K1, clt_K2]
    have h3 : wC ^ r * (wC ^ (n + 1) * ((-1 : ℂ) • clt_a2)) * wC ^ s =
        (-1 : ℂ) • (wC ^ (r + (n + 1)) * clt_a2 * wC ^ s) := by
      simp [pow_add, mul_assoc]
    have h2 : wC ^ r * ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          wC ^ p.1 * (Complex.I • clt_a1) * wC ^ p.2) * (Complex.I • clt_a1)) * wC ^ s =
        (-1 : ℂ) • ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          wC ^ (r + p.1) * clt_a1 * wC ^ p.2 * clt_a1 * wC ^ s := by
      rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, pow_add, mul_assoc]
    have h1 : wC ^ r * (PowerSeries.coeff 2 (kSeries ^ (n + 1)) * wC) * wC ^ s =
        wC ^ r * PowerSeries.coeff 2 (kSeries ^ (n + 1)) * wC ^ (s + 1) := by
      rw [pow_succ' wC s]
      simp only [mul_assoc]
    rw [mul_add, mul_add, add_mul, add_mul, h3, h2, h1, map_add, map_add, map_smul, map_smul,
      clt_tw_a2, ih r (s + 1), map_sum]
    simp only [clt_tw_a1a1, neg_smul, one_smul, Nat.add_sub_cancel]
    rw [clt_pair_step n r s, show r + (n + 1) + s = n + 1 + r + s by omega,
      show n + r + (s + 1) = n + 1 + r + s by omega]
    push_cast
    ring

/-! ### The coefficient of `t²` of `m_k(K̃)` -/

private lemma clt_wickMap (n : ℕ) :
    wickMap 1 (mVar ((n + 1 : ℕ) : ℤ)) = clt_tw (PowerSeries.coeff 2 (kSeries ^ (n + 1))) := by
  have hne : ((n + 1 : ℕ) : ℤ) ≠ 0 := by omega
  have h0 : (0 : ℤ) ≤ (n : ℤ) + 1 := by omega
  unfold wickMap
  simp only [mVar, hne, ↓reduceDIte]
  simp [stepSeries, seriesMap, kPowSeries, clt_tw, clt_wickL, h0]

private lemma clt_wickMap_eq (n : ℕ) :
    wickMap 1 (mVar ((n + 1 : ℕ) : ℤ)) =
      -(((n : ObsPoly) + 1) * (1 + mVar 1) * clt_t n) -
        ∑ b ∈ range n, ((b : ObsPoly) + 1) * (clt_t (n - 1 - b) * clt_t b) := by
  have h := clt_E2 n 0 0
  simp only [pow_zero, one_mul, mul_one, add_zero] at h
  rw [clt_wickMap, h]

private lemma clt_traceTau (b : ℕ) : traceTau ((b + 1 : ℕ) : ℤ) = clt_t b := by
  unfold traceTau clt_t
  rw [Nat.cast_add, Nat.cast_one, show (b : ℤ) + 1 - 1 = b by ring,
    show (b : ℤ) + 1 + 1 = (b : ℤ) + 2 by ring]

private lemma clt_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ d ∈ Finset.Icc 1 n, f d = ∑ b ∈ range n, f (b + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

private lemma clt_diffTrace (n : ℕ) : diffTrace (n + 1) =
    -(((n : ObsPoly) + 1) * (1 + mVar 1) * clt_t n) -
      C (((n : ℂ) + 1) / 2) * ∑ b ∈ range n, clt_t b * clt_t (n - 1 - b) := by
  unfold diffTrace
  rw [Nat.add_sub_cancel, clt_sum_Icc, clt_traceTau]
  have h : ∑ b ∈ range n, traceTau ((b + 1 : ℕ) : ℤ) * traceTau (((n + 1 : ℕ) : ℤ) -
      ((b + 1 : ℕ) : ℤ)) = ∑ b ∈ range n, clt_t b * clt_t (n - 1 - b) := by
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb' := Finset.mem_range.mp hb
    rw [clt_traceTau, show ((n + 1 : ℕ) : ℤ) - ((b + 1 : ℕ) : ℤ) = ((n - 1 - b + 1 : ℕ) : ℤ) by
      omega, clt_traceTau]
  rw [h]
  push_cast
  simp
  ring

private lemma clt_sym (n : ℕ) (f : ℕ → ObsPoly) (hf : ∀ b < n, f (n - 1 - b) = f b) :
    2 * ∑ b ∈ range n, ((b : ObsPoly) + 1) * f b = ((n : ObsPoly) + 1) * ∑ b ∈ range n, f b := by
  have hr := Finset.sum_range_reflect (fun b => ((b : ObsPoly) + 1) * f b) n
  have h2 : ∑ j ∈ range n, (((n - 1 - j : ℕ) : ObsPoly) + 1) * f (n - 1 - j) =
      ∑ j ∈ range n, ((n : ObsPoly) - j) * f j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [hf j hj', Nat.cast_sub (by omega : j ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n),
      Nat.cast_one]
    ring
  rw [h2] at hr
  rw [two_mul]
  nth_rewrite 1 [← hr]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

private lemma clt_wickMap_diffTrace (n : ℕ) :
    wickMap 1 (mVar ((n + 1 : ℕ) : ℤ)) = diffTrace (n + 1) := by
  rw [clt_wickMap_eq, clt_diffTrace]
  congr 1
  have hs := clt_sym n (fun b => clt_t (n - 1 - b) * clt_t b) (fun b hb => by
    show clt_t (n - 1 - (n - 1 - b)) * clt_t (n - 1 - b) = clt_t (n - 1 - b) * clt_t b
    rw [show n - 1 - (n - 1 - b) = b by omega, mul_comm])
  have h2 : (2 : ObsPoly) * (C (((n : ℂ) + 1) / 2) * ∑ b ∈ range n, clt_t b * clt_t (n - 1 - b)) =
      2 * ∑ b ∈ range n, ((b : ObsPoly) + 1) * (clt_t (n - 1 - b) * clt_t b) := by
    rw [hs, ← mul_assoc]
    have hc : (2 : ObsPoly) * C (((n : ℂ) + 1) / 2) = (n : ObsPoly) + 1 := by
      have : (2 : ObsPoly) * C (((n : ℂ) + 1) / 2) = C ((n : ℂ) + 1) := by
        rw [← map_ofNat C 2, ← map_mul]
        congr 1
        ring
      rw [this]
      simp
    rw [hc]
    congr 1
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  exact (mul_left_cancel₀ two_ne_zero h2).symm

private lemma clt_zeroW_mVar (a : ℤ) : zeroW (mVar a) = mVar a := by
  unfold mVar
  split_ifs with h
  · simp
  · simp [zeroW]

private lemma clt_zeroW_diffTrace (k : ℕ) : zeroW (diffTrace k) = diffTrace k := by
  simp [diffTrace, traceTau, clt_zeroW_mVar, map_sum, map_ofNat]

/-! ### The parity part -/

private lemma clt_coeff_parity (k : ℤ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (parityPart k p).coeff d = if Even (obsDeg d - k) then p.coeff d else 0 := by
  unfold parityPart
  rw [coeff_sum]
  have key : ∀ x, ((if Even (obsDeg x - k) then monomial x (p.coeff x) else 0 : ObsPoly)).coeff d =
      if x = d ∧ Even (obsDeg x - k) then p.coeff x else 0 := by
    intro x
    by_cases hx : x = d
    · subst hx
      by_cases h : Even (obsDeg x - k) <;> simp [h, coeff_monomial]
    · by_cases h : Even (obsDeg x - k) <;> simp [h, hx, coeff_monomial]
  simp only [key]
  rw [Finset.sum_eq_single d (fun x _ hx => by simp [hx])
    (fun hd => by simp [notMem_support_iff.mp hd])]
  by_cases h : Even (obsDeg d - k) <;> simp [h]

/-- The parity part as a linear map. -/
private def clt_par (k : ℤ) : ObsPoly →ₗ[ℂ] ObsPoly where
  toFun := parityPart k
  map_add' p q := by
    change parityPart k (p + q) = parityPart k p + parityPart k q
    ext d
    have h := clt_coeff_parity k (p + q) d
    have h1 := clt_coeff_parity k p d
    have h2 := clt_coeff_parity k q d
    have e : (p + q).coeff d = p.coeff d + q.coeff d := rfl
    have e' : (parityPart k p + parityPart k q).coeff d =
        (parityPart k p).coeff d + (parityPart k q).coeff d := rfl
    rw [e', h, h1, h2, e]
    split_ifs <;> simp
  map_smul' c p := by
    change parityPart k (c • p) = c • parityPart k p
    ext d
    simp only [clt_coeff_parity, coeff_smul]
    split_ifs <;> simp

private lemma clt_par_apply (k : ℤ) (p : ObsPoly) : clt_par k p = parityPart k p := rfl

private lemma clt_par_homog {p : ObsPoly} {w : ℤ}
    (hp : IsWeightedHomogeneous ObsVar.idx p w) (k : ℤ) :
    parityPart k p = if Even (w - k) then p else 0 := by
  ext d
  rw [clt_coeff_parity]
  by_cases h : p.coeff d = 0
  · split_ifs <;> simp [h]
  · have hd : obsDeg d = w := hp h
    rw [hd]
    split_ifs <;> simp

private lemma clt_mVar_homog (a : ℤ) : IsWeightedHomogeneous ObsVar.idx (mVar a) a := by
  unfold mVar
  split_ifs with h
  · subst h
    exact isWeightedHomogeneous_one _ _
  · exact isWeightedHomogeneous_X ℂ ObsVar.idx (.m ⟨a, h⟩)

private lemma clt_par_even {k a b : ℤ} (h : Even (a + b - k)) :
    parityPart k (mVar a * mVar b) = mVar a * mVar b := by
  rw [clt_par_homog ((clt_mVar_homog a).mul (clt_mVar_homog b)) k]
  simp [h]

private lemma clt_par_odd {k a b : ℤ} (h : ¬ Even (a + b - k)) :
    parityPart k (mVar a * mVar b) = 0 := by
  rw [clt_par_homog ((clt_mVar_homog a).mul (clt_mVar_homog b)) k]
  simp [h]

private lemma clt_par_C_mul (k : ℤ) (c : ℂ) (x : ObsPoly) :
    parityPart k (C c * x) = C c * parityPart k x := by
  rw [C_mul', C_mul', ← clt_par_apply, map_smul, clt_par_apply]

/-- `m_a + 2 m_{a+1} + m_{a+2}`, with an integer index. -/
private def clt_tz (a : ℤ) : ObsPoly := mVar a + 2 * mVar (a + 1) + mVar (a + 2)

private lemma clt_t_eq (n : ℕ) : clt_t n = clt_tz n := rfl

private lemma clt_par_tz {k a e : ℤ} (h : Even (a + e - k)) :
    parityPart k (clt_tz a * clt_tz e) =
      mVar a * mVar e + mVar a * mVar (e + 2) + 4 * (mVar (a + 1) * mVar (e + 1)) +
        mVar (a + 2) * mVar e + mVar (a + 2) * mVar (e + 2) := by
  obtain ⟨r, hr⟩ := h
  have hexp : clt_tz a * clt_tz e =
      (mVar a * mVar e + mVar a * mVar (e + 2) + 4 • (mVar (a + 1) * mVar (e + 1)) +
        mVar (a + 2) * mVar e + mVar (a + 2) * mVar (e + 2)) +
      2 • (mVar a * mVar (e + 1) + mVar (a + 1) * mVar e + mVar (a + 1) * mVar (e + 2) +
        mVar (a + 2) * mVar (e + 1)) := by
    unfold clt_tz
    ring
  rw [hexp, ← clt_par_apply]
  simp only [map_add, map_nsmul, clt_par_apply]
  have e1 : Even (a + e - k) := ⟨r, hr⟩
  have e2 : Even (a + (e + 2) - k) := ⟨r + 1, by omega⟩
  have e3 : Even (a + 1 + (e + 1) - k) := ⟨r + 1, by omega⟩
  have e4 : Even (a + 2 + e - k) := ⟨r + 1, by omega⟩
  have e5 : Even (a + 2 + (e + 2) - k) := ⟨r + 2, by omega⟩
  have o1 : ¬ Even (a + (e + 1) - k) := by rintro ⟨s, hs⟩; omega
  have o2 : ¬ Even (a + 1 + e - k) := by rintro ⟨s, hs⟩; omega
  have o3 : ¬ Even (a + 1 + (e + 2) - k) := by rintro ⟨s, hs⟩; omega
  have o4 : ¬ Even (a + 2 + (e + 1) - k) := by rintro ⟨s, hs⟩; omega
  rw [clt_par_even e1, clt_par_even e2, clt_par_even e3, clt_par_even e4, clt_par_even e5,
    clt_par_odd o1, clt_par_odd o2, clt_par_odd o3, clt_par_odd o4]
  simp [nsmul_eq_mul]

private lemma clt_par_first (n : ℕ) :
    parityPart ((n : ℤ) + 1) ((1 + mVar 1) * clt_tz n) =
      2 * mVar ((n : ℤ) + 1) + mVar 1 * mVar (n : ℤ) + mVar 1 * mVar ((n : ℤ) + 2) := by
  have h0 := clt_mVar_zero
  have hexp : (1 + mVar 1) * clt_tz n =
      (2 • (mVar 0 * mVar ((n : ℤ) + 1)) + mVar 1 * mVar (n : ℤ) +
        mVar 1 * mVar ((n : ℤ) + 2)) +
      (mVar 0 * mVar (n : ℤ) + mVar 0 * mVar ((n : ℤ) + 2) +
        2 • (mVar 1 * mVar ((n : ℤ) + 1))) := by
    unfold clt_tz
    rw [h0]
    ring
  have e1 : Even (0 + ((n : ℤ) + 1) - ((n : ℤ) + 1)) := ⟨0, by ring⟩
  have e2 : Even (1 + (n : ℤ) - ((n : ℤ) + 1)) := ⟨0, by ring⟩
  have e3 : Even (1 + ((n : ℤ) + 2) - ((n : ℤ) + 1)) := ⟨1, by ring⟩
  have o1 : ¬ Even (0 + (n : ℤ) - ((n : ℤ) + 1)) := by rintro ⟨s, hs⟩; omega
  have o2 : ¬ Even (0 + ((n : ℤ) + 2) - ((n : ℤ) + 1)) := by rintro ⟨s, hs⟩; omega
  have o3 : ¬ Even (1 + ((n : ℤ) + 1) - ((n : ℤ) + 1)) := by rintro ⟨s, hs⟩; omega
  rw [hexp, ← clt_par_apply]
  simp only [map_add, map_nsmul, clt_par_apply]
  rw [clt_par_even e1, clt_par_even e2, clt_par_even e3, clt_par_odd o1, clt_par_odd o2,
    clt_par_odd o3, h0]
  simp [nsmul_eq_mul]

private lemma clt_par_diffTrace (n : ℕ) :
    parityPart ((n : ℤ) + 1) (diffTrace (n + 1)) =
      -(C ((n : ℂ) + 1) * (2 * mVar ((n : ℤ) + 1) + mVar 1 * mVar (n : ℤ) +
          mVar 1 * mVar ((n : ℤ) + 2))) -
        C (((n : ℂ) + 1) / 2) * ∑ b ∈ range n,
          (mVar (b : ℤ) * mVar ((n : ℤ) - 1 - b) +
            mVar (b : ℤ) * mVar ((n : ℤ) - 1 - b + 2) +
            4 * (mVar ((b : ℤ) + 1) * mVar ((n : ℤ) - 1 - b + 1)) +
            mVar ((b : ℤ) + 2) * mVar ((n : ℤ) - 1 - b) +
            mVar ((b : ℤ) + 2) * mVar ((n : ℤ) - 1 - b + 2)) := by
  have h1 : diffTrace (n + 1) =
      -(C ((n : ℂ) + 1) * ((1 + mVar 1) * clt_tz n)) -
        C (((n : ℂ) + 1) / 2) * ∑ b ∈ range n, clt_tz (b : ℤ) * clt_tz ((n : ℤ) - 1 - b) := by
    rw [clt_diffTrace]
    have hc : (C ((n : ℂ) + 1) : ObsPoly) = (n : ObsPoly) + 1 := by simp
    have hs : ∑ b ∈ range n, clt_t b * clt_t (n - 1 - b) =
        ∑ b ∈ range n, clt_tz (b : ℤ) * clt_tz ((n : ℤ) - 1 - b) := by
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb' := Finset.mem_range.mp hb
      rw [clt_t_eq, clt_t_eq, show (((n - 1 - b : ℕ)) : ℤ) = (n : ℤ) - 1 - b by omega]
    rw [hc, hs, clt_t_eq]
    ring
  rw [h1, ← clt_par_apply]
  simp only [map_sub, map_neg, clt_par_apply, clt_par_C_mul, clt_par_first]
  have hG : parityPart ((n : ℤ) + 1) (∑ b ∈ range n, clt_tz (b : ℤ) * clt_tz ((n : ℤ) - 1 - b)) =
      ∑ b ∈ range n,
          (mVar (b : ℤ) * mVar ((n : ℤ) - 1 - b) +
            mVar (b : ℤ) * mVar ((n : ℤ) - 1 - b + 2) +
            4 * (mVar ((b : ℤ) + 1) * mVar ((n : ℤ) - 1 - b + 1)) +
            mVar ((b : ℤ) + 2) * mVar ((n : ℤ) - 1 - b) +
            mVar ((b : ℤ) + 2) * mVar ((n : ℤ) - 1 - b + 2)) := by
    rw [← clt_par_apply, map_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [clt_par_apply, clt_par_tz]
    exact ⟨-1, by ring⟩
  rw [hG]

private lemma clt_mVar_congr {a b : ℤ} (h : a = b) : mVar a = mVar b := by rw [h]

private lemma clt_R1 (n : ℕ) :
    ∑ b ∈ range n, mVar (b : ℤ) * mVar ((n : ℤ) - 1 - b + 2) =
      mVar ((n : ℤ) + 1) + ∑ b ∈ range n, mVar ((b : ℤ) + 1) * mVar ((n : ℤ) - 1 - b + 1) -
        mVar 1 * mVar (n : ℤ) := by
  cases n with
  | zero => simp [clt_mVar_zero]
  | succ n =>
    have hA : ∑ b ∈ range (n + 1), mVar (b : ℤ) * mVar (((n + 1 : ℕ) : ℤ) - 1 - b + 2) =
        ∑ b ∈ range n, mVar ((b : ℤ) + 1) * mVar (((n + 1 : ℕ) : ℤ) - 1 - b + 1) +
          mVar (((n + 1 : ℕ) : ℤ) + 1) := by
      rw [Finset.sum_range_succ']
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun b _ => ?_) ?_
      · rw [clt_mVar_congr (a := ((b + 1 : ℕ) : ℤ)) (b := (b : ℤ) + 1) (by push_cast; ring),
          clt_mVar_congr (a := ((n + 1 : ℕ) : ℤ) - 1 - ((b + 1 : ℕ) : ℤ) + 2)
            (b := ((n + 1 : ℕ) : ℤ) - 1 - b + 1) (by push_cast; ring)]
      · rw [Nat.cast_zero, clt_mVar_zero, one_mul]
        exact clt_mVar_congr (by push_cast; ring)
    have hB : ∑ b ∈ range (n + 1), mVar ((b : ℤ) + 1) * mVar (((n + 1 : ℕ) : ℤ) - 1 - b + 1) =
        ∑ b ∈ range n, mVar ((b : ℤ) + 1) * mVar (((n + 1 : ℕ) : ℤ) - 1 - b + 1) +
          mVar 1 * mVar ((n : ℤ) + 1) := by
      rw [Finset.sum_range_succ, mul_comm]
      refine congrArg₂ (· + ·) rfl ?_
      rw [clt_mVar_congr (a := (n : ℤ) + 1) (b := ((n + 1 : ℕ) : ℤ)) (by push_cast; ring),
        clt_mVar_congr (a := ((n + 1 : ℕ) : ℤ) - 1 - n + 1) (b := 1) (by push_cast; ring)]
    rw [hA, hB]
    push_cast
    ring

private lemma clt_R2 (n : ℕ) :
    ∑ b ∈ range n, mVar ((b : ℤ) + 2) * mVar ((n : ℤ) - 1 - b) =
      ∑ b ∈ range n, mVar (b : ℤ) * mVar ((n : ℤ) - 1 - b + 2) := by
  have hr := Finset.sum_range_reflect (fun b : ℕ => mVar ((b : ℤ) + 2) * mVar ((n : ℤ) - 1 - b)) n
  rw [← hr]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  change mVar (((n - 1 - j : ℕ) : ℤ) + 2) * mVar ((n : ℤ) - 1 - ((n - 1 - j : ℕ) : ℤ)) = _
  rw [mul_comm, clt_mVar_congr (a := (n : ℤ) - 1 - ((n - 1 - j : ℕ) : ℤ)) (b := j) (by omega),
    clt_mVar_congr (a := ((n - 1 - j : ℕ) : ℤ) + 2) (b := (n : ℤ) - 1 - j + 2) (by omega)]

private lemma clt_R3 (n : ℕ) :
    ∑ a ∈ Finset.Icc 1 (n + 1 + 1), mVar (a : ℤ) * mVar (((n + 1 : ℕ) : ℤ) + 2 - a) =
      ∑ b ∈ range n, mVar ((b : ℤ) + 2) * mVar ((n : ℤ) - 1 - b + 2) +
        2 * (mVar 1 * mVar ((n : ℤ) + 2)) := by
  rw [clt_sum_Icc, Finset.sum_range_succ, Finset.sum_range_succ']
  have h1 : ∑ b ∈ range n, mVar (((b + 1 + 1 : ℕ)) : ℤ) *
        mVar (((n + 1 : ℕ) : ℤ) + 2 - ((b + 1 + 1 : ℕ) : ℤ)) =
      ∑ b ∈ range n, mVar ((b : ℤ) + 2) * mVar ((n : ℤ) - 1 - b + 2) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [clt_mVar_congr (a := ((b + 1 + 1 : ℕ) : ℤ)) (b := (b : ℤ) + 2) (by push_cast; ring),
      clt_mVar_congr (a := ((n + 1 : ℕ) : ℤ) + 2 - ((b + 1 + 1 : ℕ) : ℤ))
        (b := (n : ℤ) - 1 - b + 2) (by push_cast; ring)]
  have h2 : mVar (((0 + 1 : ℕ)) : ℤ) * mVar (((n + 1 : ℕ) : ℤ) + 2 - ((0 + 1 : ℕ) : ℤ)) =
      mVar 1 * mVar ((n : ℤ) + 2) := by
    rw [clt_mVar_congr (a := ((0 + 1 : ℕ) : ℤ)) (b := 1) (by simp),
      clt_mVar_congr (a := ((n + 1 : ℕ) : ℤ) + 2 - ((0 + 1 : ℕ) : ℤ)) (b := (n : ℤ) + 2)
        (by push_cast; ring)]
  have h3 : mVar (((n + 1 + 1 : ℕ)) : ℤ) * mVar (((n + 1 : ℕ) : ℤ) + 2 - ((n + 1 + 1 : ℕ) : ℤ)) =
      mVar 1 * mVar ((n : ℤ) + 2) := by
    rw [mul_comm, clt_mVar_congr (a := ((n + 1 : ℕ) : ℤ) + 2 - ((n + 1 + 1 : ℕ) : ℤ)) (b := 1)
        (by push_cast; ring),
      clt_mVar_congr (a := ((n + 1 + 1 : ℕ) : ℤ)) (b := (n : ℤ) + 2) (by push_cast; ring)]
  simp only [h1, h2, h3]
  ring

private lemma clt_parity_succ (n : ℕ) :
    parityPart ((n + 1 : ℕ) : ℤ) (diffTrace (n + 1)) = centerTrace (n + 1) := by
  rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, clt_par_diffTrace]
  unfold centerTrace
  have hT : ∑ a ∈ Finset.Icc 1 (n + 1 - 1), mVar (a : ℤ) * mVar (((n + 1 : ℕ) : ℤ) - a) =
      ∑ b ∈ range n, mVar ((b : ℤ) + 1) * mVar ((n : ℤ) - 1 - b + 1) := by
    rw [Nat.add_sub_cancel, clt_sum_Icc]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [clt_mVar_congr (a := ((b + 1 : ℕ) : ℤ)) (b := (b : ℤ) + 1) (by push_cast; ring),
      clt_mVar_congr (a := ((n + 1 : ℕ) : ℤ) - ((b + 1 : ℕ) : ℤ)) (b := (n : ℤ) - 1 - b + 1)
        (by push_cast; ring)]
  have hS : ∑ a ∈ range (n + 1 - 1), mVar (a : ℤ) * mVar (((n + 1 : ℕ) : ℤ) - 2 - a) =
      ∑ b ∈ range n, mVar (b : ℤ) * mVar ((n : ℤ) - 1 - b) := by
    rw [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [clt_mVar_congr (a := ((n + 1 : ℕ) : ℤ) - 2 - b) (b := (n : ℤ) - 1 - b)
      (by push_cast; ring)]
  rw [hT, hS, clt_R3]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [clt_R2, clt_R1]
  have hC1 : (C ((n : ℂ) + 1) : ObsPoly) = 2 * C (((n : ℂ) + 1) / 2) := by
    rw [← map_ofNat C 2, ← map_mul]
    congr 1
    ring
  have hC3 : (C (3 * ((n + 1 : ℕ) : ℂ)) : ObsPoly) = 6 * C (((n : ℂ) + 1) / 2) := by
    rw [← map_ofNat C 6, ← map_mul]
    congr 1
    push_cast
    ring
  have hC2 : (C (((n + 1 : ℕ) : ℂ) / 2) : ObsPoly) = C (((n : ℂ) + 1) / 2) := by
    push_cast
    rfl
  have hm : mVar (((n + 1 : ℕ) : ℤ)) = mVar ((n : ℤ) + 1) :=
    clt_mVar_congr (by push_cast; ring)
  rw [hC3, hC2, hC1, hm]
  ring

/-- The order-`g⁻²` `W⁰` coefficient of `P_g m_k`, `k ≥ 1` (Section 11.3.3
[lg:sec:general-state]; `k = 1` is (11.20) [uvg:eq:mmean]). -/
theorem zeroW_wickMap_one_mVar {k : ℕ} (hk : 1 ≤ k) :
    zeroW (wickMap 1 (mVar k)) = diffTrace k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [clt_wickMap_diffTrace, clt_zeroW_diffTrace]

/-- The parity-`k` part of `𝒟_1 m_k` is (11.52) [lg:eq:center-trace]. -/
theorem parityPart_diffTrace {k : ℕ} (hk : 1 ≤ k) :
    parityPart k (diffTrace k) = centerTrace k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact clt_parity_succ n

end LSBA
