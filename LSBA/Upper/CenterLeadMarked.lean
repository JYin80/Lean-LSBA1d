import LSBA.Upper.CenterExpansion

/-!
# Uniform polynomial expansions: the leading marked coefficients

The order-`g⁻²` `W⁰` coefficient of the unrotated transition of `f_k`, `k ≥ 1` (display before
(11.51) [lg:eq:center-corner]):
`𝒟_1 f_k = −[w^k](1+w)^3[1 + (1+w)𝒯(w)]𝓕′(w) + [(1+m_1)f_1 + (1+m_{−1})f_{−1}] f_k` with
`𝒯(w) = Σ_{j≥0} m_{j+1} w^j`, `𝓕(w) = Σ_{j≥0} f_j w^j`, and its part of parity `k`, which is
(11.51) [lg:eq:center-corner].
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `𝒟_1 f_k = −[w^k](1+w)^3[1+(1+w)𝒯(w)]𝓕′(w) + [(1+m_1)f_1 + (1+m_{−1})f_{−1}] f_k` (display
before (11.51) [lg:eq:center-corner], `k ≥ 1`). -/
def diffMarked (k : ℕ) : ObsPoly :=
  -(∑ i ∈ Finset.range 4, ∑ l ∈ Finset.range (k + 1),
      if i + l = k then C ((Nat.choose 3 i : ℂ) * (l + 1)) * fVar (l + 1) else 0) -
    (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1),
      if i + j + l = k then C ((Nat.choose 4 i : ℂ) * (l + 1)) * mVar (j + 1) * fVar (l + 1)
      else 0) +
    ((1 + mVar 1) * fVar 1 + (1 + mVar (-1)) * fVar (-1)) * fVar k

/-- (11.51) [lg:eq:center-corner]: `𝓛 f_k = −3k f_k − 1_{k≥3}(k−2) f_{k−2}
− Σ_{n=1}^{k+1} n f_n m_{k+2−n} − 6 Σ_{n=1}^{k−1} n f_n m_{k−n} − Σ_{n=1}^{k−3} n f_n m_{k−2−n}
+ f_k(m_1 f_1 + m_{−1} f_{−1})`, `k > 0`. -/
def centerCorner (k : ℕ) : ObsPoly :=
  -C (3 * (k : ℂ)) * fVar k - (if 3 ≤ k then C ((k : ℂ) - 2) * fVar ((k : ℤ) - 2) else 0) -
    ∑ n ∈ Finset.Icc 1 (k + 1), C (n : ℂ) * fVar n * mVar ((k : ℤ) + 2 - n) -
    C 6 * ∑ n ∈ Finset.Icc 1 (k - 1), C (n : ℂ) * fVar n * mVar ((k : ℤ) - n) -
    ∑ n ∈ Finset.Icc 1 (k - 3), C (n : ℂ) * fVar n * mVar ((k : ℤ) - 2 - n) +
    fVar k * (mVar 1 * fVar 1 + mVar (-1) * fVar (-1))

/-! ### Linearity of the `W⁰` part of the formal expectation -/

private lemma clm_cfgWick_eq_sum (c : CfgPoly) {s : Finset (CfgVar →₀ ℕ)} (hs : c.support ⊆ s) :
    cfgWick c = ∑ d ∈ s, c.coeff d • cfgWickAux (Finsupp.weight CfgVar.vc d) d :=
  Finset.sum_subset hs fun d _ hd => by rw [notMem_support_iff.mp hd, zero_smul]

private lemma clm_cfgWick_add (p q : CfgPoly) : cfgWick (p + q) = cfgWick p + cfgWick q := by
  rw [clm_cfgWick_eq_sum (p + q) support_add, clm_cfgWick_eq_sum p Finset.subset_union_left,
    clm_cfgWick_eq_sum q Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by simp [add_smul]

private lemma clm_cfgWick_smul (a : ℂ) (c : CfgPoly) : cfgWick (a • c) = a • cfgWick c := by
  rw [clm_cfgWick_eq_sum (a • c) (MvPolynomial.support_smul), cfgWick, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul]

/-- The `W⁰` part of the formal expectation, as a linear map. -/
private def clmE : CfgPoly →ₗ[ℂ] ObsPoly where
  toFun c := zeroW (cfgWick c)
  map_add' p q := by rw [clm_cfgWick_add, map_add]
  map_smul' a c := by rw [clm_cfgWick_smul, map_smul]; rfl

private lemma clmE_apply (c : CfgPoly) : clmE c = zeroW (cfgWick c) := rfl

private lemma clm_cfgWick_monomial (d : CfgVar →₀ ℕ) :
    cfgWick (monomial d 1) = cfgWickAux (Finsupp.weight CfgVar.vc d) d := by
  simp [cfgWick, support_monomial, coeff_monomial]

private lemma clm_zeroW_mVar (j : ℤ) : zeroW (mVar j) = mVar j := by
  unfold mVar; split_ifs <;> simp [zeroW]

private lemma clm_zeroW_fVar (j : ℤ) : zeroW (fVar j) = fVar j := by
  unfold fVar; split_ifs <;> simp [zeroW]

/-! ### The `V`-degree of words -/

/-- The span of the words with exactly `n` letters `V`. -/
private def clmWd (n : ℕ) : Submodule ℂ WordAlg :=
  Submodule.span ℂ {a | ∃ u : List WLetter, u.count .v = n ∧ wordOf u = a}

private lemma clm_wordOf_append (u u' : List WLetter) :
    wordOf (u ++ u') = wordOf u * wordOf u' := by
  simp [wordOf]

private lemma clm_wd_mul {n m : ℕ} {x y : WordAlg} (hx : x ∈ clmWd n) (hy : y ∈ clmWd m) :
    x * y ∈ clmWd (n + m) := by
  unfold clmWd at hx hy ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨u', hu', rfl⟩ := hb
      exact Submodule.subset_span ⟨u ++ u', by simp [hu, hu'], clm_wordOf_append u u'⟩
    | zero => simp
    | add b b' _ _ hb hb' => rw [mul_add]; exact add_mem hb hb'
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hb
  | zero => simp
  | add a a' _ _ ha ha' => rw [add_mul]; exact add_mem ha ha'
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

private lemma clm_one_mem : (1 : WordAlg) ∈ clmWd 0 :=
  Submodule.subset_span ⟨[], rfl, by simp [wordOf]⟩

private lemma clm_wC_mem : wC ∈ clmWd 0 :=
  Submodule.subset_span ⟨[.c], by simp, by simp [wordOf, wC]⟩

private lemma clm_wCi_mem : wCi ∈ clmWd 0 :=
  Submodule.subset_span ⟨[.cInv], by simp, by simp [wordOf, wCi]⟩

private lemma clm_wV_mem : wV ∈ clmWd 1 :=
  Submodule.subset_span ⟨[.v], by simp, by simp [wordOf, wV]⟩

private lemma clm_wd_pow {x : WordAlg} (hx : x ∈ clmWd 1) (j : ℕ) : x ^ j ∈ clmWd j := by
  induction j with
  | zero => simpa using clm_one_mem
  | succ j ih => rw [pow_succ]; exact clm_wd_mul ih hx

/-- Series over words whose `n`-th coefficient is a combination of words with `n` letters `V`. -/
private def clmWSer : Subsemiring (PowerSeries WordAlg) where
  carrier := {S | ∀ n, PowerSeries.coeff n S ∈ clmWd n}
  mul_mem' := by
    intro S T hS hT n
    rw [PowerSeries.coeff_mul]
    refine Submodule.sum_mem _ fun p hp => ?_
    have h := clm_wd_mul (hS p.1) (hT p.2)
    rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hp] at h
  one_mem' := by
    intro n
    rw [PowerSeries.coeff_one]
    split_ifs with h
    · subst h; exact clm_one_mem
    · exact zero_mem _
  add_mem' := fun hS hT n => by rw [map_add]; exact add_mem (hS n) (hT n)
  zero_mem' := fun n => by rw [map_zero]; exact zero_mem _

private lemma clm_U_mem : (1 + wC) ∈ clmWd 0 := add_mem clm_one_mem clm_wC_mem

private lemma clm_Ui_mem : (1 + wCi) ∈ clmWd 0 := add_mem clm_one_mem clm_wCi_mem

private lemma clm_VU_mem : wV * (1 + wC) ∈ clmWd 1 := by
  simpa using clm_wd_mul clm_wV_mem clm_U_mem

private lemma clm_UiV_mem : (1 + wCi) * wV ∈ clmWd 1 := by
  simpa using clm_wd_mul clm_Ui_mem clm_wV_mem

private lemma clm_kSeries_mem : kSeries ∈ clmWSer := by
  intro n
  rw [kSeries, PowerSeries.coeff_mk]
  split_ifs with h
  · subst h; exact clm_wC_mem
  · refine Submodule.smul_mem _ _ ?_
    simpa using clm_wd_mul clm_U_mem (clm_wd_pow clm_VU_mem n)

private lemma clm_fInvSeries_mem : fInvSeries ∈ clmWSer := by
  intro n
  rw [fInvSeries, PowerSeries.coeff_mk]
  exact Submodule.smul_mem _ _ (clm_wd_pow clm_VU_mem n)

private lemma clm_fInvAdjSeries_mem : fInvAdjSeries ∈ clmWSer := by
  intro n
  rw [fInvAdjSeries, PowerSeries.coeff_mk]
  exact Submodule.smul_mem _ _ (clm_wd_pow clm_UiV_mem n)

private lemma clm_eq_wordOf (u : List WLetter) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := WLetter) (wordOf u) =
      MonoidAlgebra.of ℂ (FreeMonoid WLetter) (FreeMonoid.ofList u) := by
  induction u with
  | nil => simp [wordOf]; rfl
  | cons l u ih =>
    simp only [wordOf, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]

private lemma clm_mrkFun_wordOf (u : List WLetter) :
    mrkFun (wordOf u) = if u = [] then 1 else X (.mrk u) := by
  simp only [mrkFun, wordFun, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, clm_eq_wordOf]
  by_cases h : u = [] <;> simp [MonoidAlgebra.of_apply, h]

/-! ### Words: positions of `V` and splittings -/

private lemma clm_vPos_cons (l : WLetter) (u : List WLetter) :
    vPos (l :: u) = (if l = .v then [0] else []) ++ (vPos u).map Nat.succ := by
  unfold vPos
  rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
  by_cases h : l = .v <;> simp [h, Function.comp_def]

private lemma clm_vPos_nil {u : List WLetter} (hu : u.count .v = 0) : vPos u = [] := by
  induction u with
  | nil => rfl
  | cons l u ih =>
    rw [clm_vPos_cons]
    by_cases h : l = .v
    · subst h; simp at hu
    · rw [List.count_cons] at hu
      simp [h, ih (by simpa [h] using hu)]

private lemma clm_vPos_two {B D : List WLetter} (hB : B.count .v = 0) (hD : D.count .v = 0) :
    vPos (B ++ .v :: D) = [B.length] := by
  induction B with
  | nil => simp [clm_vPos_cons, clm_vPos_nil hD]
  | cons l B ih =>
    by_cases h : l = .v
    · subst h; simp at hB
    · rw [List.count_cons] at hB
      rw [List.cons_append, clm_vPos_cons, ih (by simpa [h] using hB)]
      simp [h]

private lemma clm_count_drop_idxOf (u : List WLetter) :
    (u.drop (u.idxOf .v + 1)).count .v = u.count .v - 1 := by
  induction u with
  | nil => simp
  | cons l u ih =>
    by_cases h : l = .v
    · subst h; simp
    · rw [List.idxOf_cons_ne _ (by simpa using h), List.count_cons]
      simpa [h] using ih

private lemma clm_split (u : List WLetter) (h : 0 < u.count .v) :
    ∃ A t, A.count .v = 0 ∧ u = A ++ .v :: t := by
  induction u with
  | nil => simp at h
  | cons l u ih =>
    by_cases hl : l = .v
    · exact ⟨[], u, rfl, by simp [hl]⟩
    · rw [List.count_cons] at h
      obtain ⟨A, t, hA, rfl⟩ := ih (by simpa [hl] using h)
      exact ⟨l :: A, t, by simp [hl, hA], rfl⟩

private lemma clm_split_two (u : List WLetter) (h : u.count .v = 2) :
    ∃ A B D, A.count .v = 0 ∧ B.count .v = 0 ∧ D.count .v = 0 ∧
      u = A ++ .v :: (B ++ .v :: D) := by
  obtain ⟨A, t, hA, rfl⟩ := clm_split u (by omega)
  have ht : t.count .v = 1 := by
    simp [List.count_append, hA] at h; omega
  obtain ⟨B, D, hB, rfl⟩ := clm_split t (by omega)
  refine ⟨A, B, D, hA, hB, ?_, rfl⟩
  simp [List.count_append, hB] at ht; omega

private lemma clm_idxOf_split {A t : List WLetter} (hA : A.count .v = 0) :
    (A ++ .v :: t).idxOf .v = A.length := by
  induction A with
  | nil => simp
  | cons l A ih =>
    have hl : l ≠ .v := by rintro rfl; simp at hA
    rw [List.count_cons] at hA
    rw [List.cons_append, List.idxOf_cons_ne _ (by simpa using hl), ih (by simpa [hl] using hA)]
    rfl

/-- The pivot is a factor containing `V`. -/
private lemma clm_cfgPick_mem {d : CfgVar →₀ ℕ}
    (h : (d.support.filter fun x => 0 < x.vc).Nonempty) :
    cfgPick d ∈ d.support.filter fun x => 0 < x.vc := by
  rw [cfgPick, dite_eq_left_of_eq_true (eq_true h)]
  exact (Classical.choose_spec
    ((d.support.filter fun x => 0 < x.vc).exists_min_image CfgVar.key h)).1

private lemma clm_prod_add (d e : CfgVar →₀ ℕ) :
    (d + e).prod (fun x k => x.base ^ k) =
      d.prod (fun x k => x.base ^ k) * e.prod (fun x k => x.base ^ k) :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

private lemma clm_prod_single (x : CfgVar) :
    (Finsupp.single x 1).prod (fun x k => x.base ^ k) = x.base := by
  simp [Finsupp.prod_single_index]

private lemma clm_mem_support_add {d e : CfgVar →₀ ℕ} {x : CfgVar} (h : x ∈ (d + e).support) :
    x ∈ d.support ∨ x ∈ e.support :=
  Finset.mem_union.mp (Finsupp.support_add h)

private lemma clm_mem_support_single {x y : CfgVar} (h : x ∈ (Finsupp.single y 1).support) :
    x = y :=
  Finset.mem_singleton.mp (Finsupp.support_single_subset h)

/-- With no `V` left, the expansion is the substitution `CfgVar.base`. -/
private lemma clm_aux_novc (n : ℕ) {d : CfgVar →₀ ℕ} (hd : ∀ x ∈ d.support, x.vc = 0) :
    cfgWickAux n d = d.prod fun x k => x.base ^ k := by
  cases n with
  | zero => rfl
  | succ n =>
    have hne : ¬ (d.support.filter fun x => 0 < x.vc).Nonempty := by
      rintro ⟨x, hx⟩
      rw [Finset.mem_filter] at hx
      exact absurd (hd x hx.1) hx.2.ne'
    rw [cfgWickAux]
    simp only [hne, ↓reduceIte]

/-- A marked form with two letters `V`, `v* A V B V D v`, next to factors without `V`: the pair
gives `W⁻¹ Tr(B) · v* A D v`, i.e. `m_{exp B} f_{exp(AD)}`. -/
private lemma clm_aux_two (d0 : CfgVar →₀ ℕ) (hd0 : ∀ x ∈ d0.support, x.vc = 0)
    {A B D : List WLetter} (hA : A.count .v = 0) (hB : B.count .v = 0) (hD : D.count .v = 0) :
    cfgWickAux 2 (d0 + Finsupp.single (.mrk (A ++ .v :: (B ++ .v :: D))) 1) =
      d0.prod (fun x k => x.base ^ k) * (mVar (wordExp B) * fVar (wordExp (A ++ D))) := by
  set u := A ++ .v :: (B ++ .v :: D) with hu
  set d := d0 + Finsupp.single (CfgVar.mrk u) 1 with hd
  have hvc : (CfgVar.mrk u).vc = 2 := by
    simp [CfgVar.vc, CfgVar.word, hu, List.count_append, hA, hB, hD]
  have hmem : CfgVar.mrk u ∈ d.support := by
    rw [Finsupp.mem_support_iff]; simp [hd]
  have hne : (d.support.filter fun x => 0 < x.vc).Nonempty :=
    ⟨_, Finset.mem_filter.mpr ⟨hmem, by omega⟩⟩
  have hpick : cfgPick d = .mrk u := by
    have h := clm_cfgPick_mem hne
    rw [Finset.mem_filter] at h
    rcases clm_mem_support_add h.1 with h1 | h1
    · exact absurd (hd0 _ h1) h.2.ne'
    · exact clm_mem_support_single h1
  have hsub : d - Finsupp.single (CfgVar.mrk u) 1 = d0 := by
    rw [hd]; exact add_tsub_cancel_right _ _
  have hdrop : u.drop (u.idxOf .v + 1) = B ++ .v :: D := by
    rw [hu, clm_idxOf_split hA]; simp
  have htake : u.take (u.idxOf .v) = A := by
    rw [hu, clm_idxOf_split hA]; simp
  have hsp : selfPair (.mrk u) B.length =
      Finsupp.single (.trc B) 1 + Finsupp.single (.mrk (A ++ D)) 1 := by
    simp only [selfPair, CfgVar.word, CfgVar.isMrk, hdrop, htake, ite_true]
    simp
  rw [cfgWickAux]
  simp only [hne, ↓reduceIte]
  rw [hpick, hsub]
  have hw : (CfgVar.mrk u).word = u := rfl
  rw [hw, hdrop, clm_vPos_two hB hD, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, hsp]
  have hcross : ∑ ψ ∈ d0.support, ((vPos ψ.word).map fun j =>
      ((d0 ψ : ℕ) : ℂ) • (X ObsVar.w ^ (crossPair (.mrk u) ψ j).1 *
        cfgWickAux 1 (d0 - Finsupp.single ψ 1 + (crossPair (.mrk u) ψ j).2))).sum = 0 :=
    Finset.sum_eq_zero fun ψ hψ => by rw [clm_vPos_nil (hd0 ψ hψ)]; rfl
  rw [hcross, add_zero, clm_aux_novc]
  · rw [← add_assoc, clm_prod_add, clm_prod_add, clm_prod_single, clm_prod_single, mul_assoc]
    rfl
  · intro x hx
    rcases clm_mem_support_add hx with h1 | h1
    · exact hd0 x h1
    · rcases clm_mem_support_add h1 with h2 | h2
      · rw [clm_mem_support_single h2]; exact hB
      · rw [clm_mem_support_single h2]
        simp [CfgVar.vc, CfgVar.word, List.count_append, hA, hD]

/-- Marked factors with at most one `V` each: every pair joins two marked forms and carries `w`,
so the `W⁰` part vanishes. -/
private lemma clm_aux_zero (n : ℕ) {d : CfgVar →₀ ℕ}
    (hd : ∀ x ∈ d.support, x.isMrk = true ∧ x.vc ≤ 1)
    (hne : (d.support.filter fun x => 0 < x.vc).Nonempty) :
    zeroW (cfgWickAux (n + 1) d) = 0 := by
  rw [cfgWickAux]
  simp only [hne, ↓reduceIte]
  have hp := clm_cfgPick_mem hne
  rw [Finset.mem_filter] at hp
  have hpd := hd _ hp.1
  have hnil : vPos ((cfgPick d).word.drop ((cfgPick d).word.idxOf .v + 1)) = [] := by
    refine clm_vPos_nil ?_
    rw [clm_count_drop_idxOf]
    have := hpd.2
    unfold CfgVar.vc at this
    omega
  rw [hnil, List.map_nil, List.sum_nil, zero_add, map_sum]
  refine Finset.sum_eq_zero fun ψ hψ => ?_
  have hψd : ψ ∈ d.support := by
    rw [Finsupp.mem_support_iff] at hψ ⊢
    intro h0
    apply hψ
    simp [h0]
  rw [map_list_sum, List.map_map]
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
  have h1 : (crossPair (cfgPick d) ψ j).1 = 1 := by
    simp only [crossPair, hpd.1, (hd ψ hψd).1]
  simp [h1, zeroW]

/-! ### Words as triangular matrices over Laurent polynomials -/

/-- Laurent polynomials in `z` (exponent of the outer word) and `y` (exponent of the word between
the two letters `V`). -/
private abbrev ClmR : Type := AddMonoidAlgebra ℂ (ℤ × ℤ)

/-- The monomial `z^a y^b`. -/
private def clmMon (a b : ℤ) : ClmR := AddMonoidAlgebra.single (a, b) 1

private lemma clmMon_mul (a b c e : ℤ) : clmMon a b * clmMon c e = clmMon (a + c) (b + e) := by
  simp [clmMon, AddMonoidAlgebra.single_mul_single]

private lemma clmMon_zero : clmMon 0 0 = 1 := by
  rw [clmMon, AddMonoidAlgebra.one_def]; rfl

/-- Words as upper triangular `3 × 3` matrices: `C ↦ diag(z, y, z)`, `V ↦` the shift; the entry
`(0, 2)` of `A V B V D` is `z^{exp A + exp D} y^{exp B}`. -/
private def clmΘ : WordAlg →ₐ[ℂ] Matrix (Fin 3) (Fin 3) ClmR :=
  FreeAlgebra.lift ℂ fun l => match l with
    | .c => !![clmMon 1 0, 0, 0; 0, clmMon 0 1, 0; 0, 0, clmMon 1 0]
    | .cInv => !![clmMon (-1) 0, 0, 0; 0, clmMon 0 (-1), 0; 0, 0, clmMon (-1) 0]
    | .v => !![0, 1, 0; 0, 0, 1; 0, 0, 0]

/-- `z^a y^b ↦ f_a m_b`. -/
private def clmΛ : ClmR →ₗ[ℂ] ObsPoly :=
  Finsupp.linearCombination ℂ (fun p : ℤ × ℤ => fVar p.1 * mVar p.2) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

private lemma clmΛ_mon (a b : ℤ) : clmΛ (clmMon a b) = fVar a * mVar b := by
  simp [clmΛ, clmMon, AddMonoidAlgebra.coeff_single]

private lemma clm_wordOf_cons (l : WLetter) (A : List WLetter) :
    wordOf (l :: A) = FreeAlgebra.ι ℂ l * wordOf A := by
  simp [wordOf]

private lemma clm_Θ_free (A : List WLetter) (hA : A.count .v = 0) :
    clmΘ (wordOf A) = !![clmMon (wordExp A) 0, 0, 0; 0, clmMon 0 (wordExp A), 0;
      0, 0, clmMon (wordExp A) 0] := by
  induction A with
  | nil =>
    simp only [wordOf, List.map_nil, List.prod_nil, map_one, wordExp, List.count_nil,
      Nat.cast_zero, sub_zero, clmMon_zero]
    exact Matrix.one_fin_three
  | cons l A ih =>
    have hl : l ≠ .v := by rintro rfl; simp at hA
    rw [List.count_cons] at hA
    rw [clm_wordOf_cons, map_mul, ih (by simpa [hl] using hA), clmΘ, FreeAlgebra.lift_ι_apply]
    cases l with
    | c =>
      simp only [Matrix.mul_fin_three, mul_zero, zero_mul, add_zero, zero_add, clmMon_mul]
      simp [wordExp]
      ring_nf
      simp only [and_self]
    | cInv =>
      simp only [Matrix.mul_fin_three, mul_zero, zero_mul, add_zero, zero_add, clmMon_mul]
      simp [wordExp]
      ring_nf
      simp only [and_self]
    | v => exact absurd rfl hl

private lemma clm_wordExp_append (A D : List WLetter) :
    wordExp (A ++ D) = wordExp A + wordExp D := by
  simp [wordExp, List.count_append]; ring

private lemma clm_Θ_two {A B D : List WLetter} (hA : A.count .v = 0) (hB : B.count .v = 0)
    (hD : D.count .v = 0) :
    clmΘ (wordOf (A ++ .v :: (B ++ .v :: D))) 0 2 = clmMon (wordExp (A ++ D)) (wordExp B) := by
  rw [clm_wordOf_append, clm_wordOf_cons, clm_wordOf_append, clm_wordOf_cons, map_mul, map_mul,
    map_mul, map_mul, clm_Θ_free A hA, clm_Θ_free B hB, clm_Θ_free D hD, clmΘ,
    FreeAlgebra.lift_ι_apply]
  simp only [Matrix.mul_fin_three, mul_zero, zero_mul, add_zero, zero_add, one_mul]
  simp [clmMon_mul, clm_wordExp_append]

/-- `clmΛ` of the entry `(0, 2)` of a word with two letters `V` is the `W⁰` part of its marked
form. -/
private lemma clm_weight (d0 : CfgVar →₀ ℕ) (hd0 : ∀ x ∈ d0.support, x.vc = 0) (x : CfgVar) :
    Finsupp.weight CfgVar.vc (d0 + Finsupp.single x 1) = x.vc := by
  rw [map_add, Finsupp.weight_single, one_smul, Finsupp.weight_apply]
  rw [Finsupp.sum, Finset.sum_eq_zero fun y hy => by rw [hd0 y hy, smul_zero], zero_add]

private lemma clm_E_word_two (d0 : CfgVar →₀ ℕ) (hd0 : ∀ x ∈ d0.support, x.vc = 0)
    {u : List WLetter} (hu : u.count .v = 2) :
    clmE (monomial (d0 + Finsupp.single (.mrk u) 1) 1) =
      zeroW (d0.prod fun x k => x.base ^ k) * clmΛ (clmΘ (wordOf u) 0 2) := by
  obtain ⟨A, B, D, hA, hB, hD, rfl⟩ := clm_split_two u hu
  rw [clmE_apply, clm_cfgWick_monomial, clm_weight d0 hd0]
  have h2 : (CfgVar.mrk (A ++ .v :: (B ++ .v :: D))).vc = 2 := hu
  rw [h2, clm_aux_two d0 hd0 hA hB hD, map_mul, map_mul, clm_zeroW_mVar, clm_zeroW_fVar,
    clm_Θ_two hA hB hD, clmΛ_mon, mul_comm (mVar _)]

private lemma clm_E_word_zero {d : CfgVar →₀ ℕ} (hd : ∀ x ∈ d.support, x.isMrk = true ∧ x.vc ≤ 1)
    (hne : (d.support.filter fun x => 0 < x.vc).Nonempty) (hw : 1 ≤ Finsupp.weight CfgVar.vc d) :
    clmE (monomial d 1) = 0 := by
  rw [clmE_apply, clm_cfgWick_monomial]
  obtain ⟨n, hn⟩ : ∃ n, Finsupp.weight CfgVar.vc d = n + 1 := ⟨_, (Nat.sub_add_cancel hw).symm⟩
  rw [hn]
  exact clm_aux_zero n hd hne

private lemma clm_mrkFun_ne {u : List WLetter} (hu : 0 < u.count .v) :
    mrkFun (wordOf u) = monomial (Finsupp.single (.mrk u) 1) 1 := by
  have hne : u ≠ [] := by rintro rfl; simp at hu
  simp only [clm_mrkFun_wordOf, hne, ↓reduceIte]
  rfl

/-! ### The `W⁰` expectation of products of marked forms -/

private lemma clm_X_eq (x : CfgVar) : (X x : CfgPoly) = monomial (Finsupp.single x 1) 1 := rfl

/-- A marked form of `V`-degree two. -/
private lemma clm_E_two {x : WordAlg} (hx : x ∈ clmWd 2) :
    clmE (mrkFun x) = clmΛ (clmΘ x 0 2) := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    rw [clm_mrkFun_ne (by omega), ← zero_add (Finsupp.single _ 1),
      clm_E_word_two 0 (by simp) hu]
    simp
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, Matrix.add_apply, ha, hb]
  | smul c a _ ha => simp only [map_smul, Matrix.smul_apply, ha]

/-- A marked form without `V` times one of `V`-degree two. -/
private lemma clm_E_mrk_two {u0 : List WLetter} (hu0 : u0.count .v = 0) {x : WordAlg}
    (hx : x ∈ clmWd 2) :
    clmE (X (.mrk u0) * mrkFun x) = fVar (wordExp u0) * clmΛ (clmΘ x 0 2) := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    rw [clm_mrkFun_ne (by omega), clm_X_eq, monomial_mul_monomial, one_mul,
      clm_E_word_two _ (fun y hy => by rw [clm_mem_support_single hy]; exact hu0) hu,
      clm_prod_single]
    simp [CfgVar.base, clm_zeroW_fVar]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, mul_add, Matrix.add_apply, ha, hb]
  | smul c a _ ha => simp only [map_smul, mul_smul_comm, Matrix.smul_apply, ha]

/-- Two marked forms of `V`-degree one. -/
private lemma clm_E_one_one {x y : WordAlg} (hx : x ∈ clmWd 1) (hy : y ∈ clmWd 1) :
    clmE (mrkFun x * mrkFun y) = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨u', hu', rfl⟩ := hb
      rw [clm_mrkFun_ne (by omega), clm_mrkFun_ne (by omega), monomial_mul_monomial, one_mul]
      refine clm_E_word_zero ?_ ?_ ?_
      · intro z hz
        rcases clm_mem_support_add hz with h | h <;> rw [clm_mem_support_single h] <;>
          simp [CfgVar.isMrk, CfgVar.vc, CfgVar.word, hu, hu']
      · refine ⟨.mrk u, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
        · rw [Finsupp.mem_support_iff]; simp
        · simp [CfgVar.vc, CfgVar.word, hu]
      · rw [map_add, Finsupp.weight_single, Finsupp.weight_single]
        simp [CfgVar.vc, CfgVar.word, hu, hu']
    | zero => simp
    | add b b' _ _ hb hb' => simp only [map_add, mul_add, hb, hb', add_zero]
    | smul c b _ hb => simp only [map_smul, mul_smul_comm, hb, smul_zero]
  | zero => simp
  | add a a' _ _ ha ha' => simp only [map_add, add_mul, ha, ha', add_zero]
  | smul c a _ ha => simp only [map_smul, smul_mul_assoc, ha, smul_zero]

/-- A marked form without `V` times two marked forms of `V`-degree one. -/
private lemma clm_E_mrk_one_one {u0 : List WLetter} (hu0 : u0.count .v = 0) {x y : WordAlg}
    (hx : x ∈ clmWd 1) (hy : y ∈ clmWd 1) :
    clmE (X (.mrk u0) * mrkFun x * mrkFun y) = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨u', hu', rfl⟩ := hb
      rw [clm_mrkFun_ne (by omega), clm_mrkFun_ne (by omega), clm_X_eq, monomial_mul_monomial,
        monomial_mul_monomial, one_mul, one_mul]
      refine clm_E_word_zero ?_ ?_ ?_
      · intro z hz
        rcases clm_mem_support_add hz with h | h
        · rcases clm_mem_support_add h with h' | h' <;> rw [clm_mem_support_single h'] <;>
            simp [CfgVar.isMrk, CfgVar.vc, CfgVar.word, hu, hu0]
        · rw [clm_mem_support_single h]
          simp [CfgVar.isMrk, CfgVar.vc, CfgVar.word, hu']
      · refine ⟨.mrk u, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
        · rw [Finsupp.mem_support_iff]; simp
        · simp [CfgVar.vc, CfgVar.word, hu]
      · rw [map_add, map_add, Finsupp.weight_single, Finsupp.weight_single,
          Finsupp.weight_single]
        simp [CfgVar.vc, CfgVar.word, hu, hu']
    | zero => simp
    | add b b' _ _ hb hb' => simp only [map_add, mul_add, hb, hb', add_zero]
    | smul c b _ hb => simp only [map_smul, mul_smul_comm, hb, smul_zero]
  | zero => simp
  | add a a' _ _ ha ha' => simp only [map_add, mul_add, add_mul, ha, ha', add_zero]
  | smul c a _ ha => simp only [map_smul, mul_smul_comm, smul_mul_assoc, ha, smul_zero]

/-! ### Upper triangular matrices -/

/-- The upper triangular matrix with rows `(a, b, c)`, `(0, d, e)`, `(0, 0, f)`. -/
private def clmUT (a b c d e f : ClmR) : Matrix (Fin 3) (Fin 3) ClmR :=
  !![a, b, c; 0, d, e; 0, 0, f]

private lemma clmUT_mul (a b c d e f a' b' c' d' e' f' : ClmR) :
    clmUT a b c d e f * clmUT a' b' c' d' e' f' =
      clmUT (a * a') (a * b' + b * d') (a * c' + b * e' + c * f') (d * d') (d * e' + e * f')
        (f * f') := by
  simp only [clmUT, Matrix.mul_fin_three]
  congr 1; simp

private lemma clmUT_add (a b c d e f a' b' c' d' e' f' : ClmR) :
    clmUT a b c d e f + clmUT a' b' c' d' e' f' =
      clmUT (a + a') (b + b') (c + c') (d + d') (e + e') (f + f') := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [clmUT]

private lemma clmUT_smul (r : ℂ) (a b c d e f : ClmR) :
    r • clmUT a b c d e f = clmUT (r • a) (r • b) (r • c) (r • d) (r • e) (r • f) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [clmUT]

private lemma clmUT_one : (1 : Matrix (Fin 3) (Fin 3) ClmR) = clmUT 1 0 0 1 0 1 :=
  Matrix.one_fin_three

private lemma clmUT_zero : (0 : Matrix (Fin 3) (Fin 3) ClmR) = clmUT 0 0 0 0 0 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [clmUT]

private lemma clmUT_eq {a b c d e f a' b' c' d' e' f' : ClmR} (ha : a = a') (hb : b = b')
    (hc : c = c') (hd : d = d') (he : e = e') (hf : f = f') :
    clmUT a b c d e f = clmUT a' b' c' d' e' f' := by
  subst ha hb hc hd he hf; rfl

private lemma clmUT_02 (a b c d e f : ClmR) : clmUT a b c d e f 0 2 = c := rfl

/-- `z`, `y`, `z⁻¹`, `y⁻¹` and the image of `i`. -/
private abbrev clmZ : ClmR := clmMon 1 0
private abbrev clmY : ClmR := clmMon 0 1
private abbrev clmZi : ClmR := clmMon (-1) 0
private abbrev clmYi : ClmR := clmMon 0 (-1)
private abbrev clmI : ClmR := algebraMap ℂ ClmR Complex.I

private lemma clmI_mul_self :
    algebraMap ℂ ClmR Complex.I * algebraMap ℂ ClmR Complex.I = -1 := by
  rw [← map_mul, Complex.I_mul_I, map_neg, map_one]

private lemma clm_smul_eq (r : ℂ) (x : ClmR) : r • x = algebraMap ℂ ClmR r * x :=
  Algebra.smul_def r x

private lemma clmΘ_wC : clmΘ wC = clmUT clmZ 0 0 clmY 0 clmZ := by
  rw [wC, clmΘ, FreeAlgebra.lift_ι_apply]; rfl

private lemma clmΘ_wCi : clmΘ wCi = clmUT clmZi 0 0 clmYi 0 clmZi := by
  rw [wCi, clmΘ, FreeAlgebra.lift_ι_apply]; rfl

private lemma clmΘ_wV : clmΘ wV = clmUT 0 1 0 0 1 0 := by
  rw [wV, clmΘ, FreeAlgebra.lift_ι_apply]; rfl

private lemma clmΘ_U : clmΘ (1 + wC) = clmUT (1 + clmZ) 0 0 (1 + clmY) 0 (1 + clmZ) := by
  rw [map_add, map_one, clmΘ_wC, clmUT_one, clmUT_add]; simp

private lemma clmΘ_Ui : clmΘ (1 + wCi) = clmUT (1 + clmZi) 0 0 (1 + clmYi) 0 (1 + clmZi) := by
  rw [map_add, map_one, clmΘ_wCi, clmUT_one, clmUT_add]; simp

/-- `u = (1 + z)(1 + y)`. -/
private abbrev clmu : ClmR := (1 + clmZ) * (1 + clmY)

private lemma clmΘ_k0 : clmΘ (PowerSeries.coeff 0 kSeries) = clmUT clmZ 0 0 clmY 0 clmZ := by
  simp [kSeries, clmΘ_wC]

private lemma clmΘ_k1 : clmΘ (PowerSeries.coeff 1 kSeries) =
    clmUT 0 (clmI * clmu) 0 0 (clmI * clmu) 0 := by
  simp only [kSeries, PowerSeries.coeff_mk, one_ne_zero, ↓reduceIte, pow_one, map_smul, map_mul,
    clmΘ_U, clmΘ_wV, clmUT_mul, clmUT_smul]
  refine clmUT_eq ?_ ?_ ?_ ?_ ?_ ?_ <;> simp only [clm_smul_eq] <;> ring

private lemma clmΘ_k2 : clmΘ (PowerSeries.coeff 2 kSeries) =
    clmUT 0 0 (-(clmu * (1 + clmZ))) 0 0 0 := by
  simp only [kSeries, PowerSeries.coeff_mk, OfNat.ofNat_ne_zero, ↓reduceIte, map_smul, map_mul,
    clmΘ_U, clmΘ_wV, pow_two, clmUT_mul, clmUT_smul]
  refine clmUT_eq ?_ ?_ ?_ ?_ ?_ ?_ <;> simp only [clm_smul_eq, map_mul] <;>
    first | ring1 | linear_combination (clmu * (1 + clmZ)) * clmI_mul_self

private lemma clmΘ_f0 : clmΘ (PowerSeries.coeff 0 fInvSeries) = clmUT 1 0 0 1 0 1 := by
  simp [fInvSeries, clmUT_one]

private lemma clmΘ_f1 : clmΘ (PowerSeries.coeff 1 fInvSeries) =
    clmUT 0 (clmI * (1 + clmY)) 0 0 (clmI * (1 + clmZ)) 0 := by
  simp only [fInvSeries, PowerSeries.coeff_mk, pow_one, map_smul, map_mul, clmΘ_U, clmΘ_wV,
    clmUT_mul, clmUT_smul]
  refine clmUT_eq ?_ ?_ ?_ ?_ ?_ ?_ <;> simp only [clm_smul_eq] <;> ring

private lemma clmΘ_f2 : clmΘ (PowerSeries.coeff 2 fInvSeries) =
    clmUT 0 0 (-((1 + clmY) * (1 + clmZ))) 0 0 0 := by
  simp only [fInvSeries, PowerSeries.coeff_mk, map_smul, map_mul, clmΘ_U, clmΘ_wV,
    pow_two, clmUT_mul, clmUT_smul]
  refine clmUT_eq ?_ ?_ ?_ ?_ ?_ ?_ <;> simp only [clm_smul_eq, map_mul] <;>
    first | ring1 | linear_combination ((1 + clmY) * (1 + clmZ)) * clmI_mul_self

private lemma clmΘ_g0 : clmΘ (PowerSeries.coeff 0 fInvAdjSeries) = clmUT 1 0 0 1 0 1 := by
  simp [fInvAdjSeries, clmUT_one]

private lemma clmΘ_g1 : clmΘ (PowerSeries.coeff 1 fInvAdjSeries) =
    clmUT 0 (-(clmI * (1 + clmZi))) 0 0 (-(clmI * (1 + clmYi))) 0 := by
  simp only [fInvAdjSeries, PowerSeries.coeff_mk, pow_one, map_smul, map_mul, clmΘ_Ui, clmΘ_wV,
    clmUT_mul, clmUT_smul]
  refine clmUT_eq ?_ ?_ ?_ ?_ ?_ ?_ <;> simp only [clm_smul_eq, map_neg] <;> ring

private lemma clmΘ_g2 : clmΘ (PowerSeries.coeff 2 fInvAdjSeries) =
    clmUT 0 0 (-((1 + clmZi) * (1 + clmYi))) 0 0 0 := by
  simp only [fInvAdjSeries, PowerSeries.coeff_mk, map_smul, map_mul, clmΘ_Ui, clmΘ_wV, pow_two,
    clmUT_mul, clmUT_smul]
  refine clmUT_eq ?_ ?_ ?_ ?_ ?_ ?_ <;> simp only [clm_smul_eq, map_mul, map_neg] <;>
    first | ring1 | linear_combination ((1 + clmZi) * (1 + clmYi)) * clmI_mul_self

private lemma clm_coeff_mul_zero {R : Type*} [Semiring R] (A B : PowerSeries R) :
    PowerSeries.coeff 0 (A * B) = PowerSeries.coeff 0 A * PowerSeries.coeff 0 B := by
  simp [PowerSeries.coeff_mul]

private lemma clm_coeff_mul_one {R : Type*} [Semiring R] (A B : PowerSeries R) :
    PowerSeries.coeff 1 (A * B) = PowerSeries.coeff 0 A * PowerSeries.coeff 1 B +
      PowerSeries.coeff 1 A * PowerSeries.coeff 0 B := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

private lemma clm_coeff_mul_two {R : Type*} [Semiring R] (A B : PowerSeries R) :
    PowerSeries.coeff 2 (A * B) = PowerSeries.coeff 0 A * PowerSeries.coeff 2 B +
      PowerSeries.coeff 1 A * PowerSeries.coeff 1 B +
        PowerSeries.coeff 2 A * PowerSeries.coeff 0 B := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, add_assoc]

/-- The orders `t⁰, t¹, t²` of `K̃^k` as triangular matrices: `diag(z^k, y^k, z^k)`; the
entries `i a`, `i b` with `(y − z) a = (y − z) b = u (y^k − z^k)`, `u = (1 + z)(1 + y)`; and
the corner `γ`. -/
private lemma clmΘ_kPow (k : ℕ) : ∃ a b γ : ClmR,
    clmΘ (PowerSeries.coeff 0 (kSeries ^ k)) = clmUT (clmZ ^ k) 0 0 (clmY ^ k) 0 (clmZ ^ k) ∧
    clmΘ (PowerSeries.coeff 1 (kSeries ^ k)) = clmUT 0 (clmI * a) 0 0 (clmI * b) 0 ∧
    clmΘ (PowerSeries.coeff 2 (kSeries ^ k)) = clmUT 0 0 γ 0 0 0 ∧
    (clmY - clmZ) * a = clmu * (clmY ^ k - clmZ ^ k) ∧
    (clmY - clmZ) * b = clmu * (clmY ^ k - clmZ ^ k) ∧
    (clmY - clmZ) ^ 2 * clmZ * γ =
      -((k : ClmR) * clmZ ^ k * (clmY - clmZ) ^ 2 * (clmu * (1 + clmZ))) -
        clmu ^ 2 * (clmZ * clmY ^ k - clmZ ^ (k + 1) - k * clmZ ^ k * (clmY - clmZ)) := by
  induction k with
  | zero =>
    refine ⟨0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [clmUT_one]
    · simp [clmUT_zero]
    · simp [clmUT_zero]
    · simp
    · simp
    · simp
  | succ k ih =>
    obtain ⟨a, b, γ, h0, h1, h2, ha, hb, hγ⟩ := ih
    refine ⟨clmZ ^ k * clmu + a * clmY, clmY ^ k * clmu + b * clmZ,
      -(clmZ ^ k * (clmu * (1 + clmZ))) - a * clmu + γ * clmZ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pow_succ, clm_coeff_mul_zero, map_mul, h0, clmΘ_k0, clmUT_mul]
      refine clmUT_eq ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    · rw [pow_succ, clm_coeff_mul_one, map_add, map_mul, map_mul, h0, h1, clmΘ_k0, clmΘ_k1,
        clmUT_mul, clmUT_mul, clmUT_add]
      refine clmUT_eq ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    · rw [pow_succ, clm_coeff_mul_two, map_add, map_add, map_mul, map_mul, map_mul, h0, h1, h2,
        clmΘ_k0, clmΘ_k1, clmΘ_k2, clmUT_mul, clmUT_mul, clmUT_mul, clmUT_add, clmUT_add]
      refine clmUT_eq ?_ ?_ ?_ ?_ ?_ ?_ <;>
        first | ring1 | linear_combination (a * clmu) * clmI_mul_self
    · linear_combination clmY * ha
    · linear_combination clmZ * hb
    · push_cast
      linear_combination (-((clmY - clmZ) * clmZ * clmu)) * ha + clmZ * hγ

private lemma clmY_mul_Yi : clmY * clmYi = 1 := by
  rw [clmMon_mul]; simpa using clmMon_zero

private lemma clmZ_mul_Zi : clmZ * clmZi = 1 := by
  rw [clmMon_mul]; simpa using clmMon_zero

/-- The corner of the order-`t²` part of `Y = v*F⁻¹F^{−*}v`. -/
private lemma clmΘ_Y2 : clmΘ (PowerSeries.coeff 2 (fInvSeries * fInvAdjSeries)) 0 2 =
    -(clmZ + clmZ * clmY + clmZi + clmZi * clmYi) := by
  simp only [clm_coeff_mul_two, map_add, map_mul, clmΘ_f0, clmΘ_f1, clmΘ_f2, clmΘ_g0, clmΘ_g1,
    clmΘ_g2, clmUT_mul, clmUT_add, clmUT_02]
  linear_combination (-(1 + clmYi + clmY + clmY * clmYi)) * clmI_mul_self + clmY_mul_Yi

/-- The corner of the order-`t²` part of `F⁻¹K̃^kF^{−*}`. -/
private lemma clmΘ_N2 (k : ℕ) : ∃ a b γ : ClmR,
    (clmY - clmZ) * a = clmu * (clmY ^ k - clmZ ^ k) ∧
    (clmY - clmZ) * b = clmu * (clmY ^ k - clmZ ^ k) ∧
    (clmY - clmZ) ^ 2 * clmZ * γ =
      -((k : ClmR) * clmZ ^ k * (clmY - clmZ) ^ 2 * (clmu * (1 + clmZ))) -
        clmu ^ 2 * (clmZ * clmY ^ k - clmZ ^ (k + 1) - k * clmZ ^ k * (clmY - clmZ)) ∧
    clmΘ (PowerSeries.coeff 2 (fInvSeries * kSeries ^ k * fInvAdjSeries)) 0 2 =
      -(clmZ ^ k * (1 + clmZi) * (1 + clmYi)) + a * (1 + clmYi) + γ +
        (1 + clmY) * (1 + clmYi) * clmY ^ k - (1 + clmY) * b -
          (1 + clmY) * (1 + clmZ) * clmZ ^ k := by
  obtain ⟨a, b, γ, h0, h1, h2, ha, hb, hγ⟩ := clmΘ_kPow k
  refine ⟨a, b, γ, ha, hb, hγ, ?_⟩
  simp only [clm_coeff_mul_two, clm_coeff_mul_one, clm_coeff_mul_zero, map_add, map_mul, h0, h1,
    h2, clmΘ_f0, clmΘ_f1, clmΘ_f2, clmΘ_g0, clmΘ_g1, clmΘ_g2, clmUT_mul, clmUT_add, clmUT_02]
  linear_combination (-(a * (1 + clmYi)) + (1 + clmY) * b -
    (1 + clmY) * clmY ^ k * (1 + clmYi)) * clmI_mul_self

/-! ### The generating identity -/

/-- The first sum of `diffMarked k` in `z, y`: `Σ_{i+l=k} C(3,i)(l+1) z^{l+1}`. -/
private def clmG1 (k : ℕ) : ClmR :=
  ∑ i ∈ Finset.range 4, ∑ l ∈ Finset.range (k + 1),
    if i + l = k then ((Nat.choose 3 i : ℂ) * (l + 1)) • clmMon ((l : ℤ) + 1) 0 else 0

/-- The second sum of `diffMarked k` in `z, y`: `Σ_{i+j+l=k} C(4,i)(l+1) z^{l+1} y^{j+1}`. -/
private def clmG2 (k : ℕ) : ClmR :=
  ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1),
    if i + j + l = k then ((Nat.choose 4 i : ℂ) * (l + 1)) • clmMon ((l : ℤ) + 1) ((j : ℤ) + 1)
    else 0

private lemma clm_sum_if_one {M : Type*} [AddCommMonoid M] (i k : ℕ) (F : ℕ → M) :
    ∑ l ∈ Finset.range (k + 1), (if i + l = k then F l else 0) =
      if i ≤ k then F (k - i) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (k - i)]
    · simp only [show i + (k - i) = k by omega, ↓reduceIte]
    · intro l _ hl; simp only [show ¬ (i + l = k) by omega, ↓reduceIte]
    · intro hl; simp at hl
  · exact Finset.sum_eq_zero fun l _ => by simp only [show ¬ (i + l = k) by omega, ↓reduceIte]

private lemma clm_sum_if_two {M : Type*} [AddCommMonoid M] (i k : ℕ) (F : ℕ → ℕ → M) :
    ∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1),
      (if i + j + l = k then F j l else 0) =
      ∑ l ∈ Finset.range (k + 1 - i), F (k - i - l) l := by
  rw [Finset.sum_comm]
  have h1 : ∀ l ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if i + j + l = k then F j l else 0) = if l < k + 1 - i then F (k - i - l) l else 0 := by
    intro l _
    split_ifs with h
    · rw [Finset.sum_eq_single (k - i - l)]
      · simp only [show i + (k - i - l) + l = k by omega, ↓reduceIte]
      · intro j _ hj; simp only [show ¬ (i + j + l = k) by omega, ↓reduceIte]
      · intro hj; simp at hj; omega
    · exact Finset.sum_eq_zero fun j _ => by simp only [show ¬ (i + j + l = k) by omega, ↓reduceIte]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  congr 1
  ext l; simp only [Finset.mem_filter, Finset.mem_range]; omega

private lemma clmMon_nat (a b : ℕ) : clmMon a b = clmZ ^ a * clmY ^ b := by
  simp only [clmZ, clmY, clmMon, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single,
    one_pow, mul_one]
  congr 1
  ext <;> simp

private lemma clm_smul_nat (n : ℕ) (x : ClmR) : (n : ℂ) • x = (n : ClmR) * x := by
  rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

private lemma clmG1_eq (k : ℕ) : clmG1 k = ∑ i ∈ Finset.range 4,
    if i ≤ k then ((Nat.choose 3 i * (k - i + 1) : ℕ) : ClmR) * clmZ ^ (k - i + 1) else 0 := by
  unfold clmG1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [clm_sum_if_one]
  split_ifs
  · rw [show ((↑(k - i) : ℤ) + 1) = ((k - i + 1 : ℕ) : ℤ) by push_cast; ring,
      show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, clmMon_nat, pow_zero, mul_one,
      show ((Nat.choose 3 i : ℂ) * ((↑(k - i) : ℂ) + 1)) = ((Nat.choose 3 i * (k - i + 1) : ℕ) : ℂ)
        by push_cast; ring, clm_smul_nat]
  · rfl

/-- `(y − z)² Σ_{l≤n} (l+1) z^l y^{n−l} = y^{n+2} − z^{n+2} − (n+2)(y − z) z^{n+1}`. -/
private lemma clm_S {R : Type*} [CommRing R] (Z Y : R) (n : ℕ) :
    (Y - Z) ^ 2 * ∑ l ∈ Finset.range (n + 1), ((l : R) + 1) * Z ^ l * Y ^ (n - l) =
      Y ^ (n + 2) - Z ^ (n + 2) - ((n : R) + 2) * (Y - Z) * Z ^ (n + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h : ∑ l ∈ Finset.range (n + 1), ((l : R) + 1) * Z ^ l * Y ^ (n + 1 - l) =
        Y * ∑ l ∈ Finset.range (n + 1), ((l : R) + 1) * Z ^ l * Y ^ (n - l) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [Finset.mem_range] at hl
      rw [show n + 1 - l = n - l + 1 by omega, pow_succ]
      ring
    rw [h, Nat.sub_self, pow_zero, mul_one]
    push_cast
    linear_combination Y * ih

private lemma clmG2_closed (k : ℕ) : (clmY - clmZ) ^ 2 * clmG2 k = ∑ i ∈ Finset.range 5,
    if i ≤ k then ((Nat.choose 4 i : ℕ) : ClmR) * (clmZ * clmY * (clmY ^ (k - i + 2) -
      clmZ ^ (k - i + 2) - (((k - i : ℕ) : ClmR) + 2) * (clmY - clmZ) * clmZ ^ (k - i + 1)))
    else 0 := by
  unfold clmG2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [clm_sum_if_two]
  split_ifs with h
  · rw [show k + 1 - i = k - i + 1 by omega, ← clm_S clmZ clmY (k - i), Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [show ((↑(k - i - l) : ℤ) + 1) = ((k - i - l + 1 : ℕ) : ℤ) by push_cast; ring,
      show ((l : ℤ) + 1) = ((l + 1 : ℕ) : ℤ) by push_cast; ring, clmMon_nat,
      show ((Nat.choose 4 i : ℂ) * ((l : ℂ) + 1)) = ((Nat.choose 4 i * (l + 1) : ℕ) : ℂ)
        by push_cast; ring, clm_smul_nat, show k - i - l + 1 = (k - i - l) + 1 from rfl]
    push_cast
    ring
  · rw [show k + 1 - i = 0 by omega, Finset.sum_range_zero, mul_zero]

private lemma clmY_sub_Z_ne : clmY - clmZ ≠ 0 := by
  intro h
  have h1 := congrArg (fun p : ClmR => p.coeff ((0 : ℤ), (1 : ℤ))) h
  simp [clmMon, AddMonoidAlgebra.coeff_single] at h1

/-- The corner of `F⁻¹K̃^kF^{−*}` at order `t²` is the generating form of the two sums of
`diffMarked k`. -/
private lemma clm_identity {k : ℕ} (hk : 1 ≤ k) {a b γ : ClmR}
    (ha : (clmY - clmZ) * a = clmu * (clmY ^ k - clmZ ^ k))
    (hb : (clmY - clmZ) * b = clmu * (clmY ^ k - clmZ ^ k))
    (hγ : (clmY - clmZ) ^ 2 * clmZ * γ =
      -((k : ClmR) * clmZ ^ k * (clmY - clmZ) ^ 2 * (clmu * (1 + clmZ))) -
        clmu ^ 2 * (clmZ * clmY ^ k - clmZ ^ (k + 1) - k * clmZ ^ k * (clmY - clmZ))) :
    -(clmZ ^ k * (1 + clmZi) * (1 + clmYi)) + a * (1 + clmYi) + γ +
        (1 + clmY) * (1 + clmYi) * clmY ^ k - (1 + clmY) * b -
          (1 + clmY) * (1 + clmZ) * clmZ ^ k = -clmG1 k - clmG2 k := by
  have hinj := IsFractionRing.injective ClmR (FractionRing ClmR)
  apply hinj
  set ι := algebraMap ClmR (FractionRing ClmR) with hι
  have hZm : ι clmZ * ι clmZi = 1 := by rw [← map_mul, clmZ_mul_Zi, map_one]
  have hYm : ι clmY * ι clmYi = 1 := by rw [← map_mul, clmY_mul_Yi, map_one]
  have hZi : ι clmZi = (ι clmZ)⁻¹ := eq_inv_of_mul_eq_one_right hZm
  have hYi : ι clmYi = (ι clmY)⁻¹ := eq_inv_of_mul_eq_one_right hYm
  have hZ0 : ι clmZ ≠ 0 := left_ne_zero_of_mul_eq_one hZm
  have hY0 : ι clmY ≠ 0 := left_ne_zero_of_mul_eq_one hYm
  have hYZ : ι clmY - ι clmZ ≠ 0 := by
    rw [← map_sub]; exact (map_ne_zero_iff ι hinj).mpr clmY_sub_Z_ne
  set Z := ι clmZ
  set Y := ι clmY
  have ha' : ι a = (1 + Z) * (1 + Y) * (Y ^ k - Z ^ k) / (Y - Z) := by
    rw [eq_div_iff hYZ]
    have := congrArg ι ha
    simp only [clmu, map_mul, map_sub, map_pow, map_add, map_one] at this
    linear_combination this
  have hb' : ι b = (1 + Z) * (1 + Y) * (Y ^ k - Z ^ k) / (Y - Z) := by
    rw [eq_div_iff hYZ]
    have := congrArg ι hb
    simp only [clmu, map_mul, map_sub, map_pow, map_add, map_one] at this
    linear_combination this
  have hγ' : ι γ = (-((k : FractionRing ClmR) * Z ^ k * (Y - Z) ^ 2 *
      ((1 + Z) * (1 + Y) * (1 + Z))) - ((1 + Z) * (1 + Y)) ^ 2 *
        (Z * Y ^ k - Z ^ (k + 1) - k * Z ^ k * (Y - Z))) / ((Y - Z) ^ 2 * Z) := by
    rw [eq_div_iff (mul_ne_zero (pow_ne_zero 2 hYZ) hZ0)]
    have := congrArg ι hγ
    simp only [clmu, map_mul, map_sub, map_pow, map_neg, map_add, map_natCast, map_one] at this
    linear_combination this
  have hG1 : ι (clmG1 k) = ∑ i ∈ Finset.range 4, if i ≤ k then
      ((Nat.choose 3 i * (k - i + 1) : ℕ) : FractionRing ClmR) * Z ^ (k - i + 1) else 0 := by
    rw [clmG1_eq, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [Z]
  have hG2 : ι (clmG2 k) = (∑ i ∈ Finset.range 5, if i ≤ k then
      ((Nat.choose 4 i : ℕ) : FractionRing ClmR) * (Z * Y * (Y ^ (k - i + 2) -
        Z ^ (k - i + 2) - (((k - i : ℕ) : FractionRing ClmR) + 2) * (Y - Z) * Z ^ (k - i + 1)))
      else 0) / (Y - Z) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hYZ), mul_comm]
    have := congrArg ι (clmG2_closed k)
    rw [map_mul, map_pow, map_sub, map_sum] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs
    · simp only [map_mul, map_sub, map_add, map_pow, map_natCast, map_ofNat]; rfl
    · exact map_zero ι
  simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_one, hZi, hYi, ha', hb', hγ', hG1,
    hG2]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rcases n with _ | _ | _ | n
  · simp [Finset.sum_range_succ, Nat.choose]
    field_simp
    ring
  · simp [Finset.sum_range_succ, Nat.choose]
    field_simp
    ring
  · simp [Finset.sum_range_succ, Nat.choose]
    field_simp
    ring
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      show 0 ≤ n + 3 + 1 by omega, show 1 ≤ n + 3 + 1 by omega, show 2 ≤ n + 3 + 1 by omega,
      show 3 ≤ n + 3 + 1 by omega, show 4 ≤ n + 3 + 1 by omega, ↓reduceIte,
      show n + 3 + 1 - 0 = n + 4 by omega, show n + 3 + 1 - 1 = n + 3 by omega,
      show n + 3 + 1 - 2 = n + 2 by omega, show n + 3 + 1 - 3 = n + 1 by omega,
      show n + 3 + 1 - 4 = n by omega]
    simp [Nat.choose]
    field_simp
    ring

/-! ### The coefficient of `t²` of one step of `f_k` -/

private lemma clm_yInv_zero : PowerSeries.coeff 0 yInvSeries = 1 := by
  simp [yInvSeries, PowerSeries.coeff_invOfUnit]

private lemma clm_yInv_one :
    PowerSeries.coeff 1 yInvSeries = -PowerSeries.coeff 1 ySeries := by
  have h0 : PowerSeries.coeff 0 (ySeries.invOfUnit 1) = 1 := clm_yInv_zero
  rw [yInvSeries, PowerSeries.coeff_invOfUnit, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, h0]

private lemma clm_yInv_two : PowerSeries.coeff 2 yInvSeries =
    PowerSeries.coeff 1 ySeries * PowerSeries.coeff 1 ySeries - PowerSeries.coeff 2 ySeries := by
  have h0 : PowerSeries.coeff 0 (ySeries.invOfUnit 1) = 1 := clm_yInv_zero
  have h1 : PowerSeries.coeff 1 (ySeries.invOfUnit 1) = -PowerSeries.coeff 1 ySeries := clm_yInv_one
  rw [yInvSeries, PowerSeries.coeff_invOfUnit, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, h0, h1]
  ring

private lemma clm_wordOf_replicate (k : ℕ) : wC ^ k = wordOf (List.replicate k .c) := by
  induction k with
  | zero => simp [wordOf]
  | succ k ih => rw [pow_succ', ih, List.replicate_succ, clm_wordOf_cons]; rfl

private lemma clm_stepSeries_fVar {k : ℕ} (hk : 1 ≤ k) :
    stepSeries (fVar k) =
      seriesMap mrkFun (fInvSeries * kSeries ^ k * fInvAdjSeries) * yInvSeries := by
  have hk0 : k ≠ 0 := by omega
  simp [fVar, hk0, stepSeries, kPowSeries]

private lemma clm_S_mem (k : ℕ) : fInvSeries * kSeries ^ k * fInvAdjSeries ∈ clmWSer :=
  mul_mem (mul_mem clm_fInvSeries_mem (pow_mem clm_kSeries_mem k)) clm_fInvAdjSeries_mem

private lemma clm_P_mem : fInvSeries * fInvAdjSeries ∈ clmWSer :=
  mul_mem clm_fInvSeries_mem clm_fInvAdjSeries_mem

/-- `π₀q₁(f_k)` through the entries `(0, 2)` of the order-`t²` words of `F⁻¹K̃^kF^{−*}` and of
`Y = v*F⁻¹F^{−*}v`. -/
private lemma clm_E_coeff_two {k : ℕ} (hk : 1 ≤ k) :
    zeroW (wickMap 1 (fVar k)) =
      clmΛ (clmΘ (PowerSeries.coeff 2 (fInvSeries * kSeries ^ k * fInvAdjSeries)) 0 2) -
        fVar k * clmΛ (clmΘ (PowerSeries.coeff 2 (fInvSeries * fInvAdjSeries)) 0 2) := by
  rw [wickMap, ← clmE_apply, clm_stepSeries_fVar hk, Nat.mul_one, clm_coeff_mul_two,
    clm_yInv_zero, clm_yInv_one, clm_yInv_two]
  simp only [seriesMap, ySeries, PowerSeries.coeff_mk]
  have h0 : PowerSeries.coeff 0 (fInvSeries * kSeries ^ k * fInvAdjSeries) =
      wordOf (List.replicate k .c) := by
    rw [← clm_wordOf_replicate, clm_coeff_mul_zero, clm_coeff_mul_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply (kSeries ^ k), map_pow,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [fInvSeries, fInvAdjSeries, kSeries]
  have hrep : (List.replicate k WLetter.c).count .v = 0 := by simp [List.count_replicate]
  have hm0 : mrkFun (wordOf (List.replicate k .c)) = X (.mrk (List.replicate k .c)) := by
    have hne : List.replicate k WLetter.c ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
    simp only [clm_mrkFun_wordOf, hne, ↓reduceIte]
  have he : wordExp (List.replicate k .c) = k := by simp [wordExp, List.count_replicate]
  rw [h0, hm0, mul_one, mul_neg, mul_sub, map_add, map_add, map_neg, map_sub, ← mul_assoc,
    clm_E_mrk_one_one hrep (clm_P_mem 1) (clm_P_mem 1), clm_E_mrk_two hrep (clm_P_mem 2),
    clm_E_one_one (clm_S_mem k 1) (clm_P_mem 1), clm_E_two (clm_S_mem k 2), he]
  ring

/-! ### Back to the observables -/

private lemma clmΛ_G1 (k : ℕ) : clmΛ (clmG1 k) = ∑ i ∈ Finset.range 4, ∑ l ∈ Finset.range (k + 1),
    if i + l = k then C ((Nat.choose 3 i : ℂ) * (l + 1)) * fVar (l + 1) else 0 := by
  unfold clmG1
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · rw [map_smul, clmΛ_mon, smul_eq_C_mul]; simp [mVar]
  · exact map_zero _

private lemma clmΛ_G2 (k : ℕ) : clmΛ (clmG2 k) = ∑ i ∈ Finset.range 5,
    ∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1),
      if i + j + l = k then C ((Nat.choose 4 i : ℂ) * (l + 1)) * mVar (j + 1) * fVar (l + 1)
      else 0 := by
  unfold clmG2
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · rw [map_smul, clmΛ_mon, smul_eq_C_mul]; ring
  · exact map_zero _

private lemma clmΛ_Y2 : clmΛ (-(clmZ + clmZ * clmY + clmZi + clmZi * clmYi)) =
    -(fVar 1 + fVar 1 * mVar 1 + fVar (-1) + fVar (-1) * mVar (-1)) := by
  rw [clmMon_mul, clmMon_mul]
  simp only [map_neg, map_add, clmΛ_mon]
  simp [mVar]

/-- The order-`g⁻²` `W⁰` coefficient of `P_g f_k`, `k ≥ 1` (display before (11.51)
[lg:eq:center-corner]; `k = 1` is the bracket of (11.21) [uvg:eq:fmean] at `W⁰`). -/
theorem zeroW_wickMap_one_fVar {k : ℕ} (hk : 1 ≤ k) :
    zeroW (wickMap 1 (fVar k)) = diffMarked k := by
  obtain ⟨a, b, γ, ha, hb, hγ, hN⟩ := clmΘ_N2 k
  rw [clm_E_coeff_two hk, hN, clm_identity hk ha hb hγ, clmΘ_Y2, clmΛ_Y2, map_sub, map_neg,
    clmΛ_G1, clmΛ_G2, diffMarked]
  ring

/-! ### Parity parts -/

private lemma clm_par_eq_sum (k : ℤ) (p : ObsPoly) {s : Finset (ObsVar →₀ ℕ)}
    (hs : p.support ⊆ s) :
    parityPart k p = ∑ d ∈ s, if Even (obsDeg d - k) then monomial d (p.coeff d) else 0 :=
  Finset.sum_subset hs fun d _ hd => by rw [notMem_support_iff.mp hd]; simp

/-- `parityPart k` as a linear map. -/
private def clmPar (k : ℤ) : ObsPoly →ₗ[ℂ] ObsPoly where
  toFun := parityPart k
  map_add' p q := by
    rw [clm_par_eq_sum k (p + q) support_add, clm_par_eq_sum k p Finset.subset_union_left,
      clm_par_eq_sum k q Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  map_smul' a p := by
    rw [clm_par_eq_sum k (a • p) (MvPolynomial.support_smul), parityPart, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp [smul_monomial]

private lemma clmPar_apply (k : ℤ) (p : ObsPoly) : clmPar k p = parityPart k p := rfl

private lemma clmPar_hom (k n : ℤ) {p : ObsPoly} (hp : IsWeightedHomogeneous ObsVar.idx p n) :
    clmPar k p = if Even (n - k) then p else 0 := by
  rw [clmPar_apply, parityPart]
  have h : ∀ d ∈ p.support, obsDeg d = n := fun d hd => hp (mem_support_iff.mp hd)
  rw [Finset.sum_congr rfl fun d hd => by rw [h d hd]]
  split_ifs
  · exact p.support_sum_monomial_coeff
  · simp

private lemma clm_hom_f (a : ℤ) : IsWeightedHomogeneous ObsVar.idx (fVar a) a := by
  unfold fVar
  split_ifs with h
  · subst h; exact isWeightedHomogeneous_one (R := ℂ) ObsVar.idx
  · exact isWeightedHomogeneous_X ℂ ObsVar.idx (.f ⟨a, h⟩)

private lemma clm_hom_m (a : ℤ) : IsWeightedHomogeneous ObsVar.idx (mVar a) a := by
  unfold mVar
  split_ifs with h
  · subst h; exact isWeightedHomogeneous_one (R := ℂ) ObsVar.idx
  · exact isWeightedHomogeneous_X ℂ ObsVar.idx (.m ⟨a, h⟩)

private lemma clmPar_Cf (k : ℤ) (c : ℂ) (a : ℤ) :
    clmPar k (C c * fVar a) = if Even (a - k) then C c * fVar a else 0 := by
  rw [clmPar_hom k a (by simpa using (isWeightedHomogeneous_C ObsVar.idx c).mul (clm_hom_f a))]

private lemma clmPar_Cmf (k : ℤ) (c : ℂ) (a b : ℤ) :
    clmPar k (C c * mVar a * fVar b) = if Even (a + b - k) then C c * mVar a * fVar b else 0 := by
  rw [clmPar_hom k (a + b) (by
    simpa using ((isWeightedHomogeneous_C ObsVar.idx c).mul (clm_hom_m a)).mul (clm_hom_f b))]

private lemma clm_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ l ∈ Finset.range N, f (l + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

private lemma clm_even_iff (a : ℤ) : Even a ↔ a % 2 = 0 := Int.even_iff

/-- The first sum keeps `i = 1` and `i = 3`. -/
private lemma clmPar_S1 {k : ℕ} (hk : 1 ≤ k) :
    clmPar k (∑ i ∈ Finset.range 4, ∑ l ∈ Finset.range (k + 1),
      if i + l = k then C ((Nat.choose 3 i : ℂ) * (l + 1)) * fVar (l + 1) else 0) =
      C (3 * (k : ℂ)) * fVar k +
        (if 3 ≤ k then C ((k : ℂ) - 2) * fVar ((k : ℤ) - 2) else 0) := by
  rw [map_sum]
  have hi : ∀ i ∈ Finset.range 4, clmPar k (∑ l ∈ Finset.range (k + 1),
      if i + l = k then C ((Nat.choose 3 i : ℂ) * (l + 1)) * fVar (l + 1) else 0) =
      if i ≤ k then (if Even (((k - i : ℕ) : ℤ) + 1 - k) then
        C ((Nat.choose 3 i : ℂ) * ((k - i : ℕ) + 1)) * fVar (((k - i : ℕ) : ℤ) + 1) else 0)
      else 0 := by
    intro i _
    rw [clm_sum_if_one i k (fun l => C ((Nat.choose 3 i : ℂ) * (l + 1)) * fVar (l + 1))]
    by_cases h : i ≤ k
    · simp only [h, ↓reduceIte, clmPar_Cf]
    · simp only [h, ↓reduceIte, map_zero]
  rw [Finset.sum_congr rfl hi]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have e0 : ¬ Even (((k - 0 : ℕ) : ℤ) + 1 - k) := by
    rw [clm_even_iff]; omega
  have e1 : Even (((k - 1 : ℕ) : ℤ) + 1 - k) := by
    rw [clm_even_iff]; push_cast [Nat.cast_sub hk]; omega
  have e2 : ∀ h : 2 ≤ k, ¬ Even (((k - 2 : ℕ) : ℤ) + 1 - k) := by
    intro h; rw [clm_even_iff]; push_cast [Nat.cast_sub h]; omega
  have e3 : ∀ h : 3 ≤ k, Even (((k - 3 : ℕ) : ℤ) + 1 - k) := by
    intro h; rw [clm_even_iff]; push_cast [Nat.cast_sub h]; omega
  simp only [Nat.zero_le, ↓reduceIte, e0, hk, e1]
  have hc1 : ((Nat.choose 3 1 : ℂ) * (((k - 1 : ℕ) : ℂ) + 1)) = 3 * (k : ℂ) := by
    rw [Nat.cast_sub hk]; norm_num
  have hf1 : (((k - 1 : ℕ) : ℤ) + 1) = (k : ℤ) := by push_cast [Nat.cast_sub hk]; ring
  rw [hc1, hf1]
  by_cases h3 : 3 ≤ k
  · have h2 : 2 ≤ k := by omega
    simp only [h2, h3, ↓reduceIte, e2 h2, e3 h3]
    have hc3 : ((Nat.choose 3 3 : ℂ) * (((k - 3 : ℕ) : ℂ) + 1)) = (k : ℂ) - 2 := by
      rw [Nat.cast_sub h3]; norm_num; ring
    have hf3 : (((k - 3 : ℕ) : ℤ) + 1) = (k : ℤ) - 2 := by push_cast [Nat.cast_sub h3]; ring
    rw [hc3, hf3]
    ring
  · simp only [h3, ↓reduceIte]
    by_cases h2 : 2 ≤ k
    · simp only [h2, ↓reduceIte, e2 h2]; ring
    · simp only [h2, ↓reduceIte]; ring

/-- The second sum keeps `i = 0, 2, 4`. -/
private lemma clmPar_S2 {k : ℕ} (hk : 1 ≤ k) :
    clmPar k (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1),
      if i + j + l = k then C ((Nat.choose 4 i : ℂ) * (l + 1)) * mVar (j + 1) * fVar (l + 1)
      else 0) =
      ∑ n ∈ Finset.Icc 1 (k + 1), C (n : ℂ) * fVar n * mVar ((k : ℤ) + 2 - n) +
      C 6 * ∑ n ∈ Finset.Icc 1 (k - 1), C (n : ℂ) * fVar n * mVar ((k : ℤ) - n) +
      ∑ n ∈ Finset.Icc 1 (k - 3), C (n : ℂ) * fVar n * mVar ((k : ℤ) - 2 - n) := by
  rw [map_sum]
  have hi : ∀ i ∈ Finset.range 5, clmPar k (∑ j ∈ Finset.range (k + 1),
      ∑ l ∈ Finset.range (k + 1), if i + j + l = k then
        C ((Nat.choose 4 i : ℂ) * (l + 1)) * mVar (j + 1) * fVar (l + 1) else 0) =
      if Even (2 - (i : ℤ)) then ∑ l ∈ Finset.range (k + 1 - i),
        C ((Nat.choose 4 i : ℂ) * (l + 1)) * mVar (((k - i - l : ℕ) : ℤ) + 1) *
          fVar ((l : ℤ) + 1) else 0 := by
    intro i _
    rw [clm_sum_if_two i k
      (fun j l => C ((Nat.choose 4 i : ℂ) * (l + 1)) * mVar (j + 1) * fVar (l + 1)), map_sum]
    have hd : ∀ l ∈ Finset.range (k + 1 - i),
        ((k - i - l : ℕ) : ℤ) + 1 + ((l : ℤ) + 1) - k = 2 - i := by
      intro l hl; rw [Finset.mem_range] at hl; omega
    split_ifs with he
    · refine Finset.sum_congr rfl fun l hl => ?_
      rw [clmPar_Cmf, hd l hl]
      simp only [he, ↓reduceIte]
    · refine Finset.sum_eq_zero fun l hl => ?_
      rw [clmPar_Cmf, hd l hl]
      simp only [he, ↓reduceIte]
  rw [Finset.sum_congr rfl hi]
  have ev0 : Even (2 - ((0 : ℕ) : ℤ)) := ⟨1, by norm_num⟩
  have ev1 : ¬ Even (2 - ((1 : ℕ) : ℤ)) := by rw [clm_even_iff]; norm_num
  have ev2 : Even (2 - ((2 : ℕ) : ℤ)) := ⟨0, by norm_num⟩
  have ev3 : ¬ Even (2 - ((3 : ℕ) : ℤ)) := by rw [clm_even_iff]; norm_num
  have ev4 : Even (2 - ((4 : ℕ) : ℤ)) := ⟨-1, by norm_num⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ev0, ev1, ev2, ev3, ev4,
    ↓reduceIte, add_zero]
  have s0 : ∑ l ∈ Finset.range (k + 1 - 0), C ((Nat.choose 4 0 : ℂ) * (l + 1)) *
      mVar (((k - 0 - l : ℕ) : ℤ) + 1) * fVar ((l : ℤ) + 1) =
      ∑ n ∈ Finset.Icc 1 (k + 1), C (n : ℂ) * fVar n * mVar ((k : ℤ) + 2 - n) := by
    rw [clm_sum_Icc, Nat.sub_zero]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [show ((k - 0 - l : ℕ) : ℤ) + 1 = (k : ℤ) + 2 - ((l + 1 : ℕ) : ℤ) by omega]
    push_cast; simp; ring
  have s2 : ∑ l ∈ Finset.range (k + 1 - 2), C ((Nat.choose 4 2 : ℂ) * (l + 1)) *
      mVar (((k - 2 - l : ℕ) : ℤ) + 1) * fVar ((l : ℤ) + 1) =
      C 6 * ∑ n ∈ Finset.Icc 1 (k - 1), C (n : ℂ) * fVar n * mVar ((k : ℤ) - n) := by
    rw [clm_sum_Icc, show k + 1 - 2 = k - 1 by omega, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [show ((k - 2 - l : ℕ) : ℤ) + 1 = (k : ℤ) - ((l + 1 : ℕ) : ℤ) by omega,
      show (Nat.choose 4 2 : ℂ) = 6 by norm_num [Nat.choose], map_mul]
    push_cast; ring
  have s4 : ∑ l ∈ Finset.range (k + 1 - 4), C ((Nat.choose 4 4 : ℂ) * (l + 1)) *
      mVar (((k - 4 - l : ℕ) : ℤ) + 1) * fVar ((l : ℤ) + 1) =
      ∑ n ∈ Finset.Icc 1 (k - 3), C (n : ℂ) * fVar n * mVar ((k : ℤ) - 2 - n) := by
    rw [clm_sum_Icc, show k + 1 - 4 = k - 3 by omega]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [show ((k - 4 - l : ℕ) : ℤ) + 1 = (k : ℤ) - 2 - ((l + 1 : ℕ) : ℤ) by omega]
    push_cast; simp; ring
  rw [s0, s2, s4]

private lemma clmPar_odd (k n : ℤ) {p : ObsPoly} (hp : IsWeightedHomogeneous ObsVar.idx p n)
    (h : ¬ Even (n - k)) : clmPar k p = 0 := by
  rw [clmPar_hom k n hp]; simp [h]

private lemma clmPar_even (k n : ℤ) {p : ObsPoly} (hp : IsWeightedHomogeneous ObsVar.idx p n)
    (h : Even (n - k)) : clmPar k p = p := by
  rw [clmPar_hom k n hp]; simp [h]

/-- The last term keeps `m_1 f_1 f_k` and `m_{−1} f_{−1} f_k`. -/
private lemma clmPar_L (k : ℕ) :
    clmPar k (((1 + mVar 1) * fVar 1 + (1 + mVar (-1)) * fVar (-1)) * fVar k) =
      fVar k * (mVar 1 * fVar 1 + mVar (-1) * fVar (-1)) := by
  have e : ((1 + mVar 1) * fVar 1 + (1 + mVar (-1)) * fVar (-1)) * fVar k =
      fVar 1 * fVar k + mVar 1 * fVar 1 * fVar k + fVar (-1) * fVar k +
        mVar (-1) * fVar (-1) * fVar k := by ring
  rw [e, map_add, map_add, map_add,
    clmPar_odd k _ ((clm_hom_f 1).mul (clm_hom_f k)) (by rw [clm_even_iff]; omega),
    clmPar_even k _ (((clm_hom_m 1).mul (clm_hom_f 1)).mul (clm_hom_f k))
      (by rw [clm_even_iff]; omega),
    clmPar_odd k _ ((clm_hom_f (-1)).mul (clm_hom_f k)) (by rw [clm_even_iff]; omega),
    clmPar_even k _ (((clm_hom_m (-1)).mul (clm_hom_f (-1))).mul (clm_hom_f k))
      (by rw [clm_even_iff]; omega)]
  ring

/-- The parity-`k` part of `𝒟_1 f_k` is (11.51) [lg:eq:center-corner]. -/
theorem parityPart_diffMarked {k : ℕ} (hk : 1 ≤ k) :
    parityPart k (diffMarked k) = centerCorner k := by
  rw [← clmPar_apply, diffMarked, map_add, map_sub, map_neg, clmPar_S1 hk, clmPar_S2 hk,
    clmPar_L, centerCorner]
  ring

end LSBA
