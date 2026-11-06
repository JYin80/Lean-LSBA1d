import LSBA.Gauss.WickConfig

/-!
# Algebraic properties of the Wick contraction

Properties of the formal expectation `cfgWick` used for Lemma 11.7 [lg:lem:ideal]: its `W⁰` part
is multiplicative (a `W⁰` term never pairs two different factors); conjugation of configurations
(`cfgConj`: adjoint words, conjugated coefficients); a configuration of traces only gives a
polynomial in the traces with even powers of `W⁻¹` (property (iii)); and the `W⁰` part of a
configuration whose monomials all contain a marked form of a word with letters `C`, `V` only,
ending in `C`, lies in the ideal of the `f_k` (property (i)).
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The adjoint letter: `C ↔ C⁻¹`, `V ↦ V`. -/
def WLetter.adj : WLetter → WLetter
  | .c => .cInv
  | .cInv => .c
  | .v => .v

/-- The adjoint factor: reversed word with adjoint letters. -/
def CfgVar.adj : CfgVar → CfgVar
  | .trc u => .trc (u.reverse.map WLetter.adj)
  | .mrk u => .mrk (u.reverse.map WLetter.adj)
  | .w => .w
  | .γ => .γ

/-- Conjugation of configurations: adjoint words, conjugated coefficients. -/
def cfgConj : CfgPoly →+* CfgPoly :=
  eval₂Hom (C.comp (starRingEnd ℂ)) fun x => X x.adj

/-! ### Letters `V`, weights and the pivot -/

private theorem count_split {u : List WLetter} {j : ℕ} (h : u[j]? = some .v) :
    u.count .v = (u.take j).count .v + 1 + (u.drop (j + 1)).count .v := by
  obtain ⟨hj, hu⟩ := List.getElem?_eq_some_iff.mp h
  conv_lhs => rw [← List.take_append_drop j u, List.drop_eq_getElem_cons hj, hu]
  simp [List.count_append]
  omega

private theorem idxOf_v {u : List WLetter} (h : WLetter.v ∈ u) :
    u[u.idxOf .v]? = some .v := by
  have hl := List.idxOf_lt_length_iff.mpr h
  rw [List.getElem?_eq_getElem hl, List.getElem_idxOf hl]

private theorem mem_vPos {u : List WLetter} {j : ℕ} (hj : j ∈ vPos u) : u[j]? = some .v := by
  simpa [vPos] using (List.mem_filter.mp hj).2

private theorem weight_single_one (x : CfgVar) :
    Finsupp.weight CfgVar.vc (Finsupp.single x 1) = x.vc := by
  simp [Finsupp.weight_single]

private theorem vc_ite (φ : CfgVar) (u : List WLetter) :
    (if φ.isMrk then CfgVar.mrk u else CfgVar.trc u).vc = u.count .v := by
  split_ifs <;> rfl

private theorem vc_eq_zero_of_weight {d : CfgVar →₀ ℕ} (hd : Finsupp.weight CfgVar.vc d = 0)
    {x : CfgVar} (hx : x ∈ d.support) : x.vc = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff] at hd
  have := hd x hx
  simp only [smul_eq_mul, mul_eq_zero] at this
  exact this.resolve_left (Finsupp.mem_support_iff.mp hx)

private theorem weight_eq_zero_of_vc {d : CfgVar →₀ ℕ} (hd : ∀ x ∈ d.support, x.vc = 0) :
    Finsupp.weight CfgVar.vc d = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_eq_zero fun x hx => by simp [hd x hx]

private theorem weight_sub_single {d : CfgVar →₀ ℕ} {x : CfgVar} (hx : x ∈ d.support) :
    Finsupp.weight CfgVar.vc d =
      Finsupp.weight CfgVar.vc (d - Finsupp.single x 1) + x.vc := by
  conv_lhs => rw [← tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr
    (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hx)))]
  rw [map_add, weight_single_one]

private theorem vc_trc (u : List WLetter) : (CfgVar.trc u).vc = u.count .v := rfl

private theorem vc_mrk (u : List WLetter) : (CfgVar.mrk u).vc = u.count .v := rfl

private theorem weight_selfPair {φ : CfgVar} (hφ : 0 < φ.vc) {j : ℕ}
    (hj : j ∈ vPos (φ.word.drop (φ.word.idxOf .v + 1))) :
    Finsupp.weight CfgVar.vc (selfPair φ j) + 2 = φ.vc := by
  have hv : WLetter.v ∈ φ.word := List.count_pos_iff.mp hφ
  have h1 := count_split (idxOf_v hv)
  have h2 := count_split (mem_vPos hj)
  rw [selfPair, map_add, weight_single_one, weight_single_one, vc_ite, vc_trc,
    show φ.vc = φ.word.count .v from rfl, h1, h2, List.count_append]
  omega

private theorem weight_crossPair {φ ψ : CfgVar} (hφ : 0 < φ.vc) {j : ℕ}
    (hj : j ∈ vPos ψ.word) :
    Finsupp.weight CfgVar.vc (crossPair φ ψ j).2 + 2 = φ.vc + ψ.vc := by
  have hv : WLetter.v ∈ φ.word := List.count_pos_iff.mp hφ
  have h1 := count_split (idxOf_v hv)
  have h2 := count_split (mem_vPos hj)
  unfold crossPair
  rw [show φ.vc = φ.word.count .v from rfl, show ψ.vc = ψ.word.count .v from rfl, h1, h2]
  generalize φ.word.take (φ.word.idxOf .v) = A
  generalize φ.word.drop (φ.word.idxOf .v + 1) = B
  generalize ψ.word.take j = C'
  generalize ψ.word.drop (j + 1) = D
  cases φ.isMrk <;> cases ψ.isMrk <;>
    simp only [map_add, weight_single_one, vc_trc, vc_mrk, List.count_append] <;> omega

private theorem crossPair_fst_ne_zero (φ ψ : CfgVar) (j : ℕ) : (crossPair φ ψ j).1 ≠ 0 := by
  unfold crossPair
  cases φ.isMrk <;> cases ψ.isMrk <;> simp

private theorem cfgPick_mem {d : CfgVar →₀ ℕ}
    (h : (d.support.filter fun x => 0 < x.vc).Nonempty) :
    cfgPick d ∈ d.support ∧ 0 < (cfgPick d).vc := by
  have := (Classical.choose_spec
    ((d.support.filter fun x => 0 < x.vc).exists_min_image CfgVar.key h)).1
  simp only [cfgPick, h, ↓reduceDIte]
  exact Finset.mem_filter.mp this

private theorem cfgPick_min {d : CfgVar →₀ ℕ}
    (h : (d.support.filter fun x => 0 < x.vc).Nonempty) {y : CfgVar} (hy : y ∈ d.support)
    (hyv : 0 < y.vc) : (cfgPick d).key ≤ y.key := by
  have := (Classical.choose_spec
    ((d.support.filter fun x => 0 < x.vc).exists_min_image CfgVar.key h)).2
  simp only [cfgPick, h, ↓reduceDIte]
  exact this y (Finset.mem_filter.mpr ⟨hy, hyv⟩)

private theorem vc_of_not_nonempty {d : CfgVar →₀ ℕ}
    (h : ¬ (d.support.filter fun x => 0 < x.vc).Nonempty) : ∀ x ∈ d.support, x.vc = 0 := by
  intro x hx
  by_contra hne
  exact h ⟨x, Finset.mem_filter.mpr ⟨hx, Nat.pos_of_ne_zero hne⟩⟩

private theorem code_injective : Function.Injective WLetter.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [WLetter.code]

private theorem key_injective : Function.Injective CfgVar.key := by
  intro x y h
  have hm := List.map_injective_iff.mpr code_injective
  cases x <;> cases y <;> simp only [CfgVar.key, List.cons.injEq] at h <;>
    first | exact absurd h.1 (by decide) | exact congrArg _ (hm h.2) | rfl

/-- The pivot is the unique factor with `V` of least key. -/
private theorem cfgPick_eq {d : CfgVar →₀ ℕ} {x : CfgVar} (hx : x ∈ d.support) (hxv : 0 < x.vc)
    (hmin : ∀ y ∈ d.support, 0 < y.vc → x.key ≤ y.key) : cfgPick d = x := by
  have h : (d.support.filter fun x => 0 < x.vc).Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, hxv⟩⟩
  obtain ⟨hpd, hpv⟩ := cfgPick_mem h
  exact key_injective (le_antisymm (cfgPick_min h hx hxv) (hmin _ hpd hpv))

/-- If the pivot of `d + e` is a factor of `d`, it is the pivot of `d`. -/
private theorem cfgPick_add {d e : CfgVar →₀ ℕ}
    (h : ((d + e).support.filter fun x => 0 < x.vc).Nonempty)
    (hd : cfgPick (d + e) ∈ d.support) : cfgPick d = cfgPick (d + e) := by
  obtain ⟨-, hv⟩ := cfgPick_mem h
  refine cfgPick_eq hd hv fun y hy hyv => cfgPick_min h ?_ hyv
  rw [Finsupp.mem_support_iff] at hy ⊢
  simp only [Finsupp.coe_add, Pi.add_apply]
  omega

/-! ### The expansion of a monomial and its fuel -/

/-- The Wick expansion of a monomial with the fuel of `cfgWick`. -/
private def wickZ (d : CfgVar →₀ ℕ) : ObsPoly := cfgWickAux (Finsupp.weight CfgVar.vc d) d

/-- Any fuel at least the number of letters `V` gives the same expansion. -/
private theorem cfgWickAux_fuel (n : ℕ) : ∀ d : CfgVar →₀ ℕ,
    Finsupp.weight CfgVar.vc d ≤ n → cfgWickAux n d = wickZ d := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d hd
  rcases n with _ | m
  · rw [wickZ, Nat.le_zero.mp hd]
  · by_cases hne : (d.support.filter fun x => 0 < x.vc).Nonempty
    · obtain ⟨hφd, hφ⟩ := cfgPick_mem hne
      have hw := weight_sub_single hφd
      obtain ⟨k, hk⟩ : ∃ k, Finsupp.weight CfgVar.vc d = k + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
      rw [wickZ, hk, cfgWickAux.eq_2, cfgWickAux.eq_2, ite_eq_left hne, ite_eq_left hne]
      refine congrArg₂ (· + ·) ?_ ?_
      · refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
        have := weight_selfPair hφ hj
        rw [ih m (by omega) _ (by rw [map_add]; omega), ih k (by omega) _ (by rw [map_add]; omega)]
      · refine Finset.sum_congr rfl fun ψ hψ => ?_
        refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
        have h1 := weight_crossPair hφ hj
        have h2 := weight_sub_single hψ
        rw [ih m (by omega) _ (by rw [map_add]; omega), ih k (by omega) _ (by rw [map_add]; omega)]
    · rw [wickZ, weight_eq_zero_of_vc (vc_of_not_nonempty hne), cfgWickAux.eq_2, ite_eq_right hne,
        cfgWickAux.eq_1]

private theorem wickZ_of_not {d : CfgVar →₀ ℕ}
    (h : ¬ (d.support.filter fun x => 0 < x.vc).Nonempty) :
    wickZ d = d.prod fun x k => x.base ^ k := by
  rw [wickZ, weight_eq_zero_of_vc (vc_of_not_nonempty h), cfgWickAux.eq_1]

/-- `cfgWick` as a sum over any finite set of monomials containing the support. -/
private theorem cfgWick_eq_sum (c : CfgPoly) {s : Finset (CfgVar →₀ ℕ)} (hs : c.support ⊆ s) :
    cfgWick c = ∑ d ∈ s, c.coeff d • wickZ d :=
  Finset.sum_subset hs fun d _ hd => by rw [notMem_support_iff.mp hd, zero_smul]

private theorem cfgWick_add (p q : CfgPoly) : cfgWick (p + q) = cfgWick p + cfgWick q := by
  rw [cfgWick_eq_sum (p + q) support_add, cfgWick_eq_sum p Finset.subset_union_left,
    cfgWick_eq_sum q Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by simp [add_smul]

private theorem cfgWick_monomial (d : CfgVar →₀ ℕ) (a : ℂ) :
    cfgWick (monomial d a) = a • wickZ d := by
  rw [cfgWick_eq_sum _ support_monomial_subset, Finset.sum_singleton, coeff_monomial,
    ite_eq_left rfl]

/-! ### The `W⁰` part -/

private theorem zeroW_X_w : zeroW (X ObsVar.w) = 0 := by
  simp [zeroW]

/-- A cross pair carries a positive power of `W⁻¹`. -/
private theorem zeroW_cross {k : ℕ} (hk : k ≠ 0) (a : ℂ) (p : ObsPoly) :
    zeroW (a • (X ObsVar.w ^ k * p)) = 0 := by
  rw [map_smul, map_mul, map_pow, zeroW_X_w, zero_pow hk, zero_mul, smul_zero]

/-- The `W⁰` part of one expansion step: only the pairs inside the pivot survive. -/
private theorem zeroW_cfgWickAux_succ (n : ℕ) {d : CfgVar →₀ ℕ}
    (h : (d.support.filter fun x => 0 < x.vc).Nonempty) :
    zeroW (cfgWickAux (n + 1) d) =
      ((vPos ((cfgPick d).word.drop ((cfgPick d).word.idxOf .v + 1))).map fun j =>
        zeroW (cfgWickAux n (d - Finsupp.single (cfgPick d) 1 + selfPair (cfgPick d) j))).sum := by
  rw [cfgWickAux.eq_2, ite_eq_left h, map_add, map_list_sum, List.map_map, map_sum,
    Finset.sum_eq_zero, add_zero]
  · rfl
  · intro ψ _
    rw [map_list_sum, List.map_map]
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact zeroW_cross (crossPair_fst_ne_zero _ _ _) _ _

private theorem zeroW_wickZ {d : CfgVar →₀ ℕ}
    (h : (d.support.filter fun x => 0 < x.vc).Nonempty) :
    zeroW (wickZ d) =
      ((vPos ((cfgPick d).word.drop ((cfgPick d).word.idxOf .v + 1))).map fun j =>
        zeroW (wickZ (d - Finsupp.single (cfgPick d) 1 + selfPair (cfgPick d) j))).sum := by
  obtain ⟨hφd, hφ⟩ := cfgPick_mem h
  have hw := weight_sub_single hφd
  obtain ⟨k, hk⟩ : ∃ k, Finsupp.weight CfgVar.vc d = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  rw [wickZ, hk, zeroW_cfgWickAux_succ k h]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have := weight_selfPair hφ hj
  rw [cfgWickAux_fuel k _ (by rw [map_add]; omega)]

private theorem zeroW_wickZ_base {d e : CfgVar →₀ ℕ}
    (h : ¬ ((d + e).support.filter fun x => 0 < x.vc).Nonempty) :
    zeroW (wickZ (d + e)) = zeroW (wickZ d) * zeroW (wickZ e) := by
  have hde := vc_of_not_nonempty h
  have hsub : ∀ {f : CfgVar →₀ ℕ}, f ≤ d + e → ¬ (f.support.filter fun x => 0 < x.vc).Nonempty :=
    fun {f} hf ⟨x, hx⟩ => by
      rw [Finset.mem_filter] at hx
      have hx' : x ∈ (d + e).support := Finsupp.support_mono hf hx.1
      exact absurd (hde x hx') hx.2.ne'
  rw [wickZ_of_not h, wickZ_of_not (hsub le_self_add), wickZ_of_not (hsub le_add_self),
    Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _, map_mul]

private theorem zeroW_wickZ_add_aux {d e : CfgVar →₀ ℕ}
    (ih : ∀ d' : CfgVar →₀ ℕ,
      Finsupp.weight CfgVar.vc (d' + e) < Finsupp.weight CfgVar.vc (d + e) →
        zeroW (wickZ (d' + e)) = zeroW (wickZ d') * zeroW (wickZ e))
    (h : ((d + e).support.filter fun x => 0 < x.vc).Nonempty)
    (hd : cfgPick (d + e) ∈ d.support) :
    zeroW (wickZ (d + e)) = zeroW (wickZ d) * zeroW (wickZ e) := by
  have hpd := cfgPick_add h hd
  obtain ⟨-, hv⟩ := cfgPick_mem h
  have hd' : (d.support.filter fun x => 0 < x.vc).Nonempty :=
    ⟨_, Finset.mem_filter.mpr ⟨hd, hv⟩⟩
  have hs : Finsupp.single (cfgPick (d + e)) 1 ≤ d :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hd))
  have h1 := weight_sub_single hd
  rw [zeroW_wickZ h, zeroW_wickZ hd', hpd, ← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have h2 := weight_selfPair hv hj
  rw [← tsub_add_eq_add_tsub hs, add_right_comm]
  exact ih _ (by simp only [map_add]; omega)

/-- The `W⁰` part of the expansion of a product of two monomials. -/
private theorem zeroW_wickZ_add (N : ℕ) : ∀ d e : CfgVar →₀ ℕ,
    Finsupp.weight CfgVar.vc (d + e) ≤ N →
      zeroW (wickZ (d + e)) = zeroW (wickZ d) * zeroW (wickZ e) := by
  induction N with
  | zero =>
    intro d e hN
    by_cases h : ((d + e).support.filter fun x => 0 < x.vc).Nonempty
    · obtain ⟨hφ, hv⟩ := cfgPick_mem h
      have := weight_sub_single hφ
      omega
    · exact zeroW_wickZ_base h
  | succ N ih =>
    intro d e hN
    by_cases h : ((d + e).support.filter fun x => 0 < x.vc).Nonempty
    · obtain ⟨hφ, hv⟩ := cfgPick_mem h
      have hc := congrArg (Finsupp.weight CfgVar.vc) (add_comm d e)
      have hφ' : cfgPick (d + e) ∈ d.support ∨ cfgPick (d + e) ∈ e.support := by
        simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply] at hφ ⊢
        omega
      rcases hφ' with hd | he
      · exact zeroW_wickZ_add_aux (fun d' hd' => ih d' e (by omega)) h hd
      · have := zeroW_wickZ_add_aux (d := e) (e := d)
          (fun d' hd' => ih d' d (by omega)) (by rwa [add_comm]) (by rwa [add_comm])
        rwa [add_comm, mul_comm]
    · exact zeroW_wickZ_base h

/-- The `W⁰` part of the expectation is multiplicative. -/
theorem zeroW_cfgWick_mul (c c' : CfgPoly) :
    zeroW (cfgWick (c * c')) = zeroW (cfgWick c) * zeroW (cfgWick c') := by
  induction c using MvPolynomial.induction_on' with
  | monomial d a =>
    induction c' using MvPolynomial.induction_on' with
    | monomial e b =>
      rw [monomial_mul_monomial, cfgWick_monomial, cfgWick_monomial, cfgWick_monomial, map_smul,
        map_smul, map_smul, zeroW_wickZ_add _ d e le_rfl, smul_mul_smul_comm]
    | add p q hp hq => rw [mul_add, cfgWick_add, cfgWick_add, map_add, map_add, hp, hq, mul_add]
  | add p q hp hq => rw [add_mul, cfgWick_add, cfgWick_add, map_add, map_add, hp, hq, add_mul]

/-! ### Traces only -/

open scoped Pointwise in
/-- Polynomials in `m_k`, `γ`, `w` all of whose monomials have even degree in `w`. -/
private def evenW : Subalgebra ℂ ObsPoly where
  carrier := {p | ∀ m ∈ p.support, Even (Finsupp.weight ObsVar.wWt m) ∧
    ∀ v ∈ m.support, v ∈ traceVars ∪ {ObsVar.w}}
  mul_mem' := by
    intro p q hp hq m hm
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul p q hm)
    refine ⟨by rw [map_add]; exact (hp a ha).1.add (hq b hb).1, fun v hv => ?_⟩
    rcases Finset.mem_union.mp (Finsupp.support_add hv) with h | h
    · exact (hp a ha).2 v h
    · exact (hq b hb).2 v h
  one_mem' := by
    intro m hm
    rw [mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · subst h
      simp
    · exact absurd rfl hm
  add_mem' := by
    intro p q hp hq m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hp m h
    · exact hq m h
  zero_mem' := by
    intro m hm
    simp at hm
  algebraMap_mem' := by
    intro r m hm
    rw [MvPolynomial.algebraMap_eq, mem_support_iff, coeff_C] at hm
    split_ifs at hm with h
    · subst h
      simp
    · exact absurd rfl hm

private theorem X_mem_evenW {v : ObsVar} (hv : v ∈ traceVars) : X v ∈ evenW := by
  intro m hm
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  have h0 : v.wWt = 0 := by
    rcases hv with ⟨_, hne⟩ | ⟨k, rfl⟩
    · cases v <;> simp_all [ObsVar.wWt]
    · rfl
  refine ⟨by simp [Finsupp.weight_single, h0], fun x hx => ?_⟩
  rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hx
  exact Set.mem_union_left _ (hx ▸ hv)

private theorem X_w_sq_mem_evenW : X ObsVar.w ^ 2 ∈ evenW := by
  intro m hm
  rw [X_pow_eq_monomial, support_monomial, ite_eq_right one_ne_zero, Finset.mem_singleton] at hm
  subst hm
  refine ⟨by simp [Finsupp.weight_single, ObsVar.wWt], fun x hx => ?_⟩
  rw [Finsupp.support_single _ two_ne_zero, Finset.mem_singleton] at hx
  exact Set.mem_union_right _ hx

private theorem base_mem_evenW {x : CfgVar} (hx : x.isMrk = false ∧ x ≠ .w) :
    x.base ∈ evenW := by
  rcases x with u | u | _ | _
  · simp only [CfgVar.base, mVar]
    split_ifs with h
    · exact one_mem _
    · exact X_mem_evenW (Set.mem_union_right _ ⟨_, rfl⟩)
  · simp [CfgVar.isMrk] at hx
  · simp at hx
  · exact X_mem_evenW (Set.mem_union_left _ ⟨rfl, by simp⟩)

private theorem crossPair_trc {φ ψ : CfgVar} (hφ : φ.isMrk = false) (hψ : ψ.isMrk = false)
    (j : ℕ) : (crossPair φ ψ j).1 = 2 ∧
      ∀ x ∈ (crossPair φ ψ j).2.support, x.isMrk = false ∧ x ≠ .w := by
  simp only [crossPair, hφ, hψ, true_and]
  intro x hx
  rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hx
  subst hx
  simp [CfgVar.isMrk]

private theorem selfPair_trc {φ : CfgVar} (hφ : φ.isMrk = false) (j : ℕ) :
    ∀ x ∈ (selfPair φ j).support, x.isMrk = false ∧ x ≠ .w := by
  intro x hx
  simp only [selfPair, hφ, Bool.false_eq_true, ↓reduceIte] at hx
  rcases Finset.mem_union.mp (Finsupp.support_add hx) with h | h <;>
  · rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at h
    subst h
    simp [CfgVar.isMrk]

private theorem cfgWickAux_mem_evenW (n : ℕ) : ∀ d : CfgVar →₀ ℕ,
    (∀ x ∈ d.support, x.isMrk = false ∧ x ≠ .w) → cfgWickAux n d ∈ evenW := by
  have hbase : ∀ d : CfgVar →₀ ℕ, (∀ x ∈ d.support, x.isMrk = false ∧ x ≠ .w) →
      (d.prod fun x k => x.base ^ k) ∈ evenW := fun d hd =>
    prod_mem fun x hx => pow_mem (base_mem_evenW (hd x hx)) _
  induction n with
  | zero => intro d hd; rw [cfgWickAux.eq_1]; exact hbase d hd
  | succ n ih =>
    intro d hd
    rw [cfgWickAux.eq_2]
    split_ifs with h
    · obtain ⟨hφd, -⟩ := cfgPick_mem h
      have hφ := (hd _ hφd).1
      refine add_mem (list_sum_mem fun y hy => ?_) (sum_mem fun ψ hψ => list_sum_mem fun y hy => ?_)
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
        refine ih _ fun x hx => ?_
        rcases Finset.mem_union.mp (Finsupp.support_add hx) with h | h
        · exact hd x (Finsupp.support_tsub h)
        · exact selfPair_trc hφ j x h
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
        have hψ' := (hd ψ (Finsupp.support_tsub hψ)).1
        obtain ⟨h2, hx2⟩ := crossPair_trc hφ hψ' j
        refine Subalgebra.smul_mem _ (mul_mem ?_ (ih _ fun x hx => ?_)) _
        · rw [h2]
          exact X_w_sq_mem_evenW
        · rcases Finset.mem_union.mp (Finsupp.support_add hx) with h | h
          · exact hd x (Finsupp.support_tsub (Finsupp.support_tsub h))
          · exact hx2 x h
    · exact hbase d hd

/-- Traces only (no marked form, no `W⁻¹`): the expectation is a polynomial in the `m_k`, `W⁻¹`,
`g⁻²` with even powers of `W⁻¹` only. -/
theorem cfgWick_trace (c : CfgPoly) (hc : c ∈ supported ℂ {x : CfgVar | x.isMrk = false ∧ x ≠ .w}) :
    cfgWick c ∈ supported ℂ (traceVars ∪ {.w}) ∧
      ∀ j : ℕ, Odd j → weightedHomogeneousComponent ObsVar.wWt j (cfgWick c) = 0 := by
  have hmem : cfgWick c ∈ evenW := by
    refine Subalgebra.sum_mem _ fun d hd => Subalgebra.smul_mem _
      (cfgWickAux_mem_evenW _ d fun x hx => ?_) _
    rw [mem_supported] at hc
    exact hc ((mem_vars_iff_mem_support x).mpr ⟨d, hd, hx⟩)
  refine ⟨mem_supported.mpr fun v hv => ?_, fun j hj => ?_⟩
  · obtain ⟨m, hm, hvm⟩ := (mem_vars_iff_mem_support v).mp hv
    exact (hmem m hm).2 v hvm
  · rw [weightedHomogeneousComponent_apply]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Finset.mem_filter] at hm
    exact absurd (hm.2 ▸ (hmem m hm.1).1) (Nat.not_even_iff_odd.mpr hj)

/-! ### Marked words in `C`, `V` ending in `C` -/

private theorem X_f_mem_fIdeal (k : NzInt) : X (ObsVar.f k) ∈ fIdeal :=
  Ideal.subset_span ⟨k, rfl⟩

private theorem zeroW_mem_fIdeal {p : ObsPoly} (hp : p ∈ fIdeal) : zeroW p ∈ fIdeal := by
  have h : ∀ k : NzInt, zeroW (X (.f k)) ∈ fIdeal := fun k => by
    simp only [zeroW, aeval_X]
    rw [ite_eq_right (by simp)]
    exact X_f_mem_fIdeal k
  have hle : fIdeal ≤ fIdeal.comap zeroW :=
    Ideal.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact h k)
  exact hle hp

private theorem getLast?_append_of_ne_nil {l l' : List WLetter} (h : l' ≠ []) :
    (l ++ l').getLast? = l'.getLast? := by
  rw [List.getLast?_append, List.getLast?_eq_some_getLast h, Option.some_or]

/-- A monomial without `V` containing a marked form of a nonempty word in `C` only. -/
private theorem prod_base_mem_fIdeal {d : CfgVar →₀ ℕ} (hd : ∀ x ∈ d.support, x.vc = 0)
    {u : List WLetter} (hu : 0 < d (.mrk u)) (hc : WLetter.cInv ∉ u)
    (hl : u.getLast? = some .c) : (d.prod fun x k => x.base ^ k) ∈ fIdeal := by
  have hmem : CfgVar.mrk u ∈ d.support := Finsupp.mem_support_iff.mpr hu.ne'
  have hv : WLetter.v ∉ u := fun h => (List.count_pos_iff.mpr h).ne' (hd _ hmem)
  have hall : ∀ l ∈ u, WLetter.c = l := by
    intro l hl
    cases l
    · rfl
    · exact absurd hl hc
    · exact absurd hl hv
  have hne : u ≠ [] := by
    rintro rfl
    simp at hl
  have hexp : wordExp u = u.length := by
    rw [wordExp, List.count_eq_length.mpr hall, List.count_eq_zero.mpr hc]
    simp
  have hk : wordExp u ≠ 0 := by
    rw [hexp]
    exact_mod_cast (List.length_pos_iff.mpr hne).ne'
  rw [Finsupp.prod]
  refine Ideal.prod_mem _ hmem ?_
  simp only [CfgVar.base, fVar, hk, ↓reduceDIte]
  exact Ideal.pow_mem_of_mem _ (X_f_mem_fIdeal _) _ hu

/-- The marked word after pairing its first `V` with a later `V` still ends in `C`. -/
private theorem getLast?_selfPair {u : List WLetter} {j : ℕ}
    (hj : j ∈ vPos (u.drop (u.idxOf .v + 1))) (hl : u.getLast? = some .c) :
    (u.take (u.idxOf .v) ++ (u.drop (u.idxOf .v + 1)).drop (j + 1)).getLast? = some .c := by
  set B := u.drop (u.idxOf .v + 1) with hBdef
  obtain ⟨hjB, hBj⟩ := List.getElem?_eq_some_iff.mp (mem_vPos hj)
  have hB : B ≠ [] := List.ne_nil_of_length_pos (by omega)
  have huB : u.getLast? = B.getLast? := by
    conv_lhs => rw [← List.take_append_drop (u.idxOf .v + 1) u]
    exact getLast?_append_of_ne_nil hB
  have hD : B.drop (j + 1) ≠ [] := by
    intro hD
    have hlen := List.drop_eq_nil_iff.mp hD
    rw [hl, List.getLast?_eq_getElem?, show B.length - 1 = j by omega,
      List.getElem?_eq_getElem hjB, hBj] at huB
    exact absurd huB (by simp)
  have hDB : (B.drop (j + 1)).getLast? = B.getLast? := by
    conv_rhs => rw [← List.take_append_drop (j + 1) B]
    exact (getLast?_append_of_ne_nil hD).symm
  rw [getLast?_append_of_ne_nil hD, hDB, ← huB, hl]

private theorem zeroW_cfgWickAux_mem_fIdeal (n : ℕ) : ∀ d : CfgVar →₀ ℕ,
    Finsupp.weight CfgVar.vc d ≤ n →
      (∃ u : List WLetter, 0 < d (.mrk u) ∧ WLetter.cInv ∉ u ∧ u.getLast? = some .c) →
        zeroW (cfgWickAux n d) ∈ fIdeal := by
  induction n with
  | zero =>
    rintro d hw ⟨u, hu, hc, hl⟩
    rw [cfgWickAux.eq_1]
    exact zeroW_mem_fIdeal (prod_base_mem_fIdeal
      (fun x hx => vc_eq_zero_of_weight (Nat.le_zero.mp hw) hx) hu hc hl)
  | succ n ih =>
    rintro d hw ⟨u, hu, hc, hl⟩
    by_cases h : (d.support.filter fun x => 0 < x.vc).Nonempty
    · rw [zeroW_cfgWickAux_succ n h]
      obtain ⟨hφd, hφ⟩ := cfgPick_mem h
      have hwd := weight_sub_single hφd
      refine list_sum_mem fun y hy => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
      have hws := weight_selfPair hφ hj
      refine ih _ (by rw [map_add]; omega) ?_
      by_cases hφu : cfgPick d = .mrk u
      · rw [hφu] at hj ⊢
        refine ⟨u.take (u.idxOf .v) ++ (u.drop (u.idxOf .v + 1)).drop (j + 1), ?_, fun h => hc ?_,
          getLast?_selfPair hj hl⟩
        · simp only [selfPair, CfgVar.word, CfgVar.isMrk, ↓reduceIte, Finsupp.coe_add,
            Pi.add_apply, Finsupp.single_eq_same]
          omega
        · rcases List.mem_append.mp h with h | h
          · exact List.mem_of_mem_take h
          · exact List.mem_of_mem_drop (List.mem_of_mem_drop h)
      · refine ⟨u, ?_, hc, hl⟩
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_apply, ite_eq_right hφu]
        omega
    · rw [cfgWickAux.eq_2, ite_eq_right h]
      exact zeroW_mem_fIdeal (prod_base_mem_fIdeal (vc_of_not_nonempty h) hu hc hl)

/-- If every monomial contains a marked form of a nonempty word in `C`, `V` ending in `C`, the
`W⁰` part of the expectation lies in the ideal `(f_k : k ≠ 0)`. -/
theorem zeroW_cfgWick_mem_fIdeal (c : CfgPoly)
    (hc : ∀ d ∈ c.support, ∃ u : List WLetter, 0 < d (.mrk u) ∧ WLetter.cInv ∉ u ∧
      u.getLast? = some .c) :
    zeroW (cfgWick c) ∈ fIdeal := by
  rw [cfgWick, map_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  rw [map_smul, smul_eq_C_mul]
  exact Ideal.mul_mem_left _ _ (zeroW_cfgWickAux_mem_fIdeal _ d le_rfl (hc d hd))

end LSBA
