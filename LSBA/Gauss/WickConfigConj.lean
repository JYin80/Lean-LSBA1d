import LSBA.Gauss.WickConfigAlg

/-!
# The Wick contraction commutes with conjugation

The formal expectation `cfgWick` used for Lemma 11.7 [lg:lem:ideal] commutes with conjugation of
configurations (`cfgConj`: adjoint words, conjugated coefficients). In Lemma 11.7 [lg:lem:ideal] the
negative
powers are obtained from the positive ones by adjunction.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Letters `V`, weights and one expansion step -/

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

private theorem vPos_cons (l : WLetter) (u : List WLetter) :
    vPos (l :: u) = (if l = .v then [0] else []) ++ (vPos u).map (· + 1) := by
  simp only [vPos, List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
  by_cases h : l = .v <;> simp [h, Function.comp_def]

private theorem weight_single_one (x : CfgVar) :
    Finsupp.weight CfgVar.vc (Finsupp.single x 1) = x.vc := by
  simp [Finsupp.weight_single]

private theorem vc_ite (φ : CfgVar) (u : List WLetter) :
    (if φ.isMrk then CfgVar.mrk u else CfgVar.trc u).vc = u.count .v := by
  split_ifs <;> rfl

private theorem weight_eq_zero_of_vc {d : CfgVar →₀ ℕ} (hd : ∀ x ∈ d.support, x.vc = 0) :
    Finsupp.weight CfgVar.vc d = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_eq_zero fun x hx => by simp [hd x hx]

private theorem single_le {d : CfgVar →₀ ℕ} {x : CfgVar} (hx : x ∈ d.support) :
    Finsupp.single x 1 ≤ d :=
  Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hx))

private theorem weight_sub_single {d : CfgVar →₀ ℕ} {x : CfgVar} (hx : x ∈ d.support) :
    Finsupp.weight CfgVar.vc d =
      Finsupp.weight CfgVar.vc (d - Finsupp.single x 1) + x.vc := by
  conv_lhs => rw [← tsub_add_cancel_of_le (single_le hx)]
  rw [map_add, weight_single_one]

private theorem weight_selfPair {φ : CfgVar} (hφ : 0 < φ.vc) {j : ℕ}
    (hj : j ∈ vPos (φ.word.drop (φ.word.idxOf .v + 1))) :
    Finsupp.weight CfgVar.vc (selfPair φ j) + 2 = φ.vc := by
  have hv : WLetter.v ∈ φ.word := List.count_pos_iff.mp hφ
  have h1 := count_split (idxOf_v hv)
  have h2 := count_split (mem_vPos hj)
  rw [selfPair, map_add, weight_single_one, weight_single_one, vc_ite,
    show ∀ u, (CfgVar.trc u).vc = u.count .v from fun _ => rfl,
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
    simp only [map_add, weight_single_one] <;>
    simp only [CfgVar.vc, CfgVar.word, List.count_append] <;> omega

private theorem cfgPick_mem {d : CfgVar →₀ ℕ}
    (h : (d.support.filter fun x => 0 < x.vc).Nonempty) :
    cfgPick d ∈ d.support ∧ 0 < (cfgPick d).vc := by
  have := (Classical.choose_spec
    ((d.support.filter fun x => 0 < x.vc).exists_min_image CfgVar.key h)).1
  simp only [cfgPick, h, ↓reduceDIte]
  exact Finset.mem_filter.mp this

private theorem vc_of_not_nonempty {d : CfgVar →₀ ℕ}
    (h : ¬ (d.support.filter fun x => 0 < x.vc).Nonempty) : ∀ x ∈ d.support, x.vc = 0 := by
  intro x hx
  by_contra hne
  exact h ⟨x, Finset.mem_filter.mpr ⟨hx, Nat.pos_of_ne_zero hne⟩⟩

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

/-- One step of the expansion at the pivot. -/
private theorem wickZ_step {d : CfgVar →₀ ℕ}
    (h : (d.support.filter fun x => 0 < x.vc).Nonempty) :
    wickZ d = ((vPos ((cfgPick d).word.drop ((cfgPick d).word.idxOf .v + 1))).map fun j =>
          wickZ (d - Finsupp.single (cfgPick d) 1 + selfPair (cfgPick d) j)).sum +
        ∑ ψ ∈ (d - Finsupp.single (cfgPick d) 1).support,
          ((vPos ψ.word).map fun j =>
            (((d - Finsupp.single (cfgPick d) 1 : CfgVar →₀ ℕ) ψ : ℕ) : ℂ) •
              (X ObsVar.w ^ (crossPair (cfgPick d) ψ j).1 *
                wickZ (d - Finsupp.single (cfgPick d) 1 - Finsupp.single ψ 1 +
                  (crossPair (cfgPick d) ψ j).2))).sum := by
  obtain ⟨hφd, hφ⟩ := cfgPick_mem h
  have hw := weight_sub_single hφd
  obtain ⟨k, hk⟩ : ∃ k, Finsupp.weight CfgVar.vc d = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  rw [wickZ, hk, cfgWickAux.eq_2, ite_eq_left h]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    have := weight_selfPair hφ hj
    rw [cfgWickAux_fuel k _ (by rw [map_add]; omega)]
  · refine Finset.sum_congr rfl fun ψ hψ => ?_
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    have h1 := weight_crossPair hφ hj
    have h2 := weight_sub_single hψ
    rw [cfgWickAux_fuel k _ (by rw [map_add]; omega)]

private theorem wickZ_of_vc {d : CfgVar →₀ ℕ} (h : ∀ x ∈ d.support, x.vc = 0) :
    wickZ d = d.prod fun x k => x.base ^ k := by
  rw [wickZ, weight_eq_zero_of_vc h, cfgWickAux.eq_1]

/-- The expectation of a monomial. -/
private theorem cfgWick_monomial (d : CfgVar →₀ ℕ) (a : ℂ) :
    cfgWick (monomial d a) = a • wickZ d := by
  have hs : ∀ (c : CfgPoly) {s : Finset (CfgVar →₀ ℕ)}, c.support ⊆ s →
      cfgWick c = ∑ e ∈ s, c.coeff e • wickZ e := fun c s hs =>
    Finset.sum_subset hs fun e _ he => by rw [notMem_support_iff.mp he, zero_smul]
  rw [hs _ support_monomial_subset, Finset.sum_singleton, coeff_monomial, ite_eq_left rfl]

private theorem cfgWick_add (p q : CfgPoly) : cfgWick (p + q) = cfgWick p + cfgWick q := by
  have hs : ∀ (c : CfgPoly) {s : Finset (CfgVar →₀ ℕ)}, c.support ⊆ s →
      cfgWick c = ∑ e ∈ s, c.coeff e • wickZ e := fun c s hs =>
    Finset.sum_subset hs fun e _ he => by rw [notMem_support_iff.mp he, zero_smul]
  rw [hs (p + q) support_add, hs p Finset.subset_union_left, hs q Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by simp [add_smul]

/-! ### The expansion normalised by the number of traces -/

/-- `1` for a trace factor, `0` otherwise. -/
private def tw : CfgVar → ℕ
  | .trc _ => 1
  | _ => 0

/-- The number of trace factors of a monomial. -/
private def T (d : CfgVar →₀ ℕ) : ℕ := Finsupp.weight tw d

private theorem T_single (x : CfgVar) : T (Finsupp.single x 1) = tw x := by
  simp [T, Finsupp.weight_single]

private theorem T_add (d e : CfgVar →₀ ℕ) : T (d + e) = T d + T e := map_add _ _ _

private theorem T_sub {d : CfgVar →₀ ℕ} {x : CfgVar} (hx : x ∈ d.support) :
    T (d - Finsupp.single x 1) + tw x = T d := by
  conv_rhs => rw [← tsub_add_cancel_of_le (single_le hx)]
  rw [T_add, T_single]

private theorem tw_ite {φ : CfgVar} (hφ : 0 < φ.vc) (u : List WLetter) :
    tw (if φ.isMrk then .mrk u else .trc u) = tw φ := by
  cases φ <;> simp_all [CfgVar.isMrk, tw, CfgVar.vc, CfgVar.word]

private theorem T_selfPair {φ : CfgVar} (hφ : 0 < φ.vc) (j : ℕ) :
    T (selfPair φ j) = 1 + tw φ := by
  rw [selfPair, T_add, T_single, T_single, tw_ite hφ]
  rfl

private theorem T_crossPair {φ ψ : CfgVar} (hφ : 0 < φ.vc) {j : ℕ} (hj : j ∈ vPos ψ.word) :
    (crossPair φ ψ j).1 + T (crossPair φ ψ j).2 = 1 + tw φ + tw ψ := by
  have hψ : 0 < ψ.vc := List.count_pos_iff.mpr (List.mem_of_getElem? (mem_vPos hj))
  unfold crossPair
  cases φ <;> cases ψ <;> simp_all [CfgVar.isMrk, CfgVar.vc, CfgVar.word, tw, T,
    Finsupp.weight_single]

/-- The localisation inverting `w`. -/
private abbrev Loc : Type := Localization.Away (X ObsVar.w : ObsPoly)

private abbrev ι : ObsPoly →+* Loc := algebraMap ObsPoly Loc

private def tinv : Loc := IsLocalization.Away.invSelf (X ObsVar.w : ObsPoly)

private theorem ι_inj : Function.Injective ι :=
  IsLocalization.injective (M := Submonoid.powers (X ObsVar.w : ObsPoly)) Loc
    (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero _))

private theorem w_mul_tinv : ι (X .w) * tinv = 1 := IsLocalization.Away.mul_invSelf _

/-- The expansion times `w^{-#traces}`. -/
private def Zh (d : CfgVar →₀ ℕ) : Loc := ι (wickZ d) * tinv ^ T d

private theorem pow_shift {k m n : ℕ} (h : k + m = 1 + n) :
    ι (X .w) ^ k * tinv ^ n = ι (X .w) * tinv ^ m := by
  calc ι (X .w) ^ k * tinv ^ n = ι (X .w) ^ k * tinv ^ n * (ι (X .w) * tinv) ^ m := by
        rw [w_mul_tinv, one_pow, mul_one]
    _ = ι (X .w) ^ (k + m) * tinv ^ (n + m) := by ring
    _ = ι (X .w) * (ι (X .w) * tinv) ^ n * tinv ^ m := by rw [h]; ring
    _ = _ := by rw [w_mul_tinv, one_pow, mul_one]

/-- A one-step expansion at the factor `x`, normalised: every pair carries one factor `w`. -/
private theorem Zh_gen {d : CfgVar →₀ ℕ} {x : CfgVar} (hx : x ∈ d.support) (Js : List ℕ)
    (S : ℕ → CfgVar →₀ ℕ) (Jc : CfgVar → List ℕ) (K : CfgVar → ℕ → ℕ × (CfgVar →₀ ℕ))
    (hS : ∀ j ∈ Js, T (S j) = 1 + tw x)
    (hK : ∀ ψ, ∀ j ∈ Jc ψ, (K ψ j).1 + T (K ψ j).2 = 1 + tw x + tw ψ) :
    ι ((Js.map fun j => wickZ (d - Finsupp.single x 1 + S j)).sum +
        ∑ ψ ∈ (d - Finsupp.single x 1).support, ((Jc ψ).map fun j =>
          (((d - Finsupp.single x 1 : CfgVar →₀ ℕ) ψ : ℕ) : ℂ) • (X ObsVar.w ^ (K ψ j).1 *
            wickZ (d - Finsupp.single x 1 - Finsupp.single ψ 1 + (K ψ j).2))).sum) * tinv ^ T d =
    ι (X .w) * ((Js.map fun j => Zh (d - Finsupp.single x 1 + S j)).sum +
      (d - Finsupp.single x 1).sum fun ψ n => (n : Loc) *
        ((Jc ψ).map fun j =>
          Zh (d - Finsupp.single x 1 - Finsupp.single ψ 1 + (K ψ j).2)).sum) := by
  have hT := T_sub hx
  rw [map_add, add_mul, mul_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [map_list_sum, List.map_map, ← List.sum_map_mul_right, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    have he : T (d - Finsupp.single x 1 + S j) = T d + 1 := by rw [T_add, hS j hj]; omega
    have := pow_shift (k := 0) (m := T d + 1) (n := T d) (by omega)
    simp only [Function.comp_apply, Zh, he, pow_zero, one_mul] at this ⊢
    rw [this]; ring
  · rw [map_sum, Finset.sum_mul, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ hψ => ?_
    rw [map_list_sum, List.map_map, ← List.sum_map_mul_right, ← List.sum_map_mul_left,
      ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    have h1 := T_sub hψ
    have h2 := hK ψ j hj
    have := pow_shift (k := (K ψ j).1) (n := T d)
      (m := T (d - Finsupp.single x 1 - Finsupp.single ψ 1 + (K ψ j).2)) (by rw [T_add]; omega)
    simp only [Function.comp_apply, Zh, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, map_mul, map_pow,
      map_natCast]
    generalize ι (wickZ _) = z
    generalize (((d - Finsupp.single x 1 : CfgVar →₀ ℕ) ψ : ℕ) : Loc) = c
    linear_combination (c * z) * this

/-- One step of the normalised expansion at the pivot. -/
private theorem Zh_step {d : CfgVar →₀ ℕ} (h : (d.support.filter fun x => 0 < x.vc).Nonempty) :
    Zh d = ι (X .w) * (((vPos ((cfgPick d).word.drop ((cfgPick d).word.idxOf .v + 1))).map
        fun j => Zh (d - Finsupp.single (cfgPick d) 1 + selfPair (cfgPick d) j)).sum +
      (d - Finsupp.single (cfgPick d) 1).sum fun ψ n => (n : Loc) *
        ((vPos ψ.word).map fun j => Zh (d - Finsupp.single (cfgPick d) 1 - Finsupp.single ψ 1 +
          (crossPair (cfgPick d) ψ j).2)).sum) := by
  obtain ⟨hφd, hφ⟩ := cfgPick_mem h
  rw [Zh, wickZ_step h]
  exact Zh_gen hφd _ _ _ _ (fun j _ => T_selfPair hφ j) fun ψ j hj => T_crossPair hφ hj

/-! ### Cycles of labelled positions

A configuration is modelled by labelled positions and the successor permutation along each trace
or marked form; pairing two letters `V` at positions `a`, `b` multiplies the successor permutation
by the transposition of `a` and `b`. -/

private theorem fp_conj (τ : Equiv.Perm ℕ) (l : List ℕ) :
    (l.map τ).formPerm = τ * l.formPerm * τ⁻¹ := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil => simp
    | cons y l =>
      simp only [List.map_cons, List.formPerm_cons_cons] at ih ⊢
      rw [ih, Equiv.swap_apply_apply]; group

private theorem fp_conj_swap {a b : ℕ} {l : List ℕ} (ha : a ∉ l) (hb : b ∉ l) :
    Equiv.swap a b * (a :: l).formPerm * Equiv.swap a b = (b :: l).formPerm := by
  have hl : l.map (Equiv.swap a b) = l := by
    conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left fun x hx => Equiv.swap_apply_of_ne_of_ne
      (by rintro rfl; exact ha hx) (by rintro rfl; exact hb hx)
  have h := fp_conj (Equiv.swap a b) (a :: l)
  rw [List.map_cons, Equiv.swap_apply_left, Equiv.swap_inv, hl] at h
  exact h.symm

private theorem fp_app (l m : List ℕ) (x y : ℕ) :
    (l ++ x :: y :: m).formPerm = (l ++ [x]).formPerm * Equiv.swap x y * (y :: m).formPerm := by
  induction l with
  | nil => simp
  | cons z l ih =>
    cases l with
    | nil => simp [mul_assoc]
    | cons w l =>
      simp only [List.cons_append, List.formPerm_cons_cons] at ih ⊢
      rw [ih]; simp only [mul_assoc]

private theorem fp_comm {l m : List ℕ} (h : l.Disjoint m) :
    Commute l.formPerm m.formPerm :=
  Equiv.Perm.Disjoint.commute fun x => by
    by_cases hx : x ∈ l
    · exact Or.inr (List.formPerm_apply_of_notMem fun hm => h hx hm)
    · exact Or.inl (List.formPerm_apply_of_notMem hx)

/-- Pairing the `V`s at `a` and `b` of one cycle `a X b Y` splits it into `a Y` and `b X`. -/
private theorem fp_split {a b : ℕ} {X Y : List ℕ} (h : (a :: X ++ b :: Y).Nodup) :
    (a :: X ++ b :: Y).formPerm * Equiv.swap a b = (a :: Y).formPerm * (b :: X).formPerm := by
  have hsub : (a :: X ++ [b]).Nodup :=
    h.sublist (List.Sublist.append (List.Sublist.refl _) (by simp))
  simp only [List.cons_append, List.nodup_cons, List.nodup_append, List.mem_append,
    List.mem_cons, not_or] at h
  obtain ⟨⟨haX, hab, haY⟩, hX, ⟨hbY, hY⟩, hXY⟩ := h
  have hbX : b ∉ X := fun hb => (hXY b hb b (Or.inl rfl)) rfl
  have hdis : (b :: X).Disjoint (a :: Y) := by
    intro x hx hy
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    exacts [hab rfl, hbY hy, haX hx, hXY x hx x (Or.inr hy) rfl]
  have hY' : (b :: Y).formPerm * Equiv.swap a b = Equiv.swap a b * (a :: Y).formPerm := by
    rw [← fp_conj_swap haY hbY, mul_assoc, Equiv.swap_mul_self, mul_one]
  rcases List.eq_nil_or_concat X with rfl | ⟨X', z, rfl⟩
  · rw [List.singleton_append, List.formPerm_cons_cons, List.formPerm_singleton, mul_one,
      mul_assoc, hY', ← mul_assoc, Equiv.swap_mul_self, one_mul]
  · simp only [List.concat_eq_append] at *
    have hrot : (a :: X' ++ [z, b]).formPerm = (b :: a :: X' ++ [z]).formPerm :=
      List.formPerm_eq_of_isRotated (by simpa using hsub) (by
        have := List.isRotated_append (l := a :: X' ++ [z]) (l' := [b])
        simpa using this)
    calc (a :: (X' ++ [z]) ++ b :: Y).formPerm * Equiv.swap a b
        = (a :: X' ++ [z]).formPerm * Equiv.swap z b * (b :: Y).formPerm * Equiv.swap a b := by
          rw [show a :: (X' ++ [z]) ++ b :: Y = (a :: X') ++ z :: b :: Y by simp, fp_app]
      _ = Equiv.swap b a * (a :: X' ++ [z]).formPerm * ((b :: Y).formPerm * Equiv.swap a b) := by
          rw [← List.formPerm_append_pair, hrot, List.cons_append, List.cons_append,
            List.formPerm_cons_cons]
          simp only [mul_assoc]
      _ = Equiv.swap a b * (a :: (X' ++ [z])).formPerm * Equiv.swap a b * (a :: Y).formPerm := by
          rw [hY', Equiv.swap_comm]; simp only [mul_assoc, List.cons_append]
      _ = (a :: Y).formPerm * (b :: (X' ++ [z])).formPerm := by
          rw [fp_conj_swap haX hbX]; exact (fp_comm hdis).eq

/-- The successor permutation of a list of disjoint cycles. -/
private def sg (C : List (List ℕ)) : Equiv.Perm ℕ := (C.map List.formPerm).prod

private theorem sg_perm {C C' : List (List ℕ)} (h : List.Perm C C') (hnd : C.flatten.Nodup) :
    sg C = sg C' :=
  (h.map _).prod_eq' (List.pairwise_map.mpr ((List.nodup_flatten.mp hnd).2.imp fp_comm))

private theorem sg_fix {C : List (List ℕ)} {x : ℕ} (hx : x ∉ C.flatten) : sg C x = x := by
  induction C with
  | nil => rfl
  | cons c C ih =>
    simp only [List.flatten_cons, List.mem_append, not_or] at hx
    show c.formPerm (sg C x) = x
    rw [ih hx.2, List.formPerm_apply_of_notMem hx.1]

private theorem sg_apply {C : List (List ℕ)} (hnd : C.flatten.Nodup) {c : List ℕ} (hc : c ∈ C)
    {x : ℕ} (hx : x ∈ c) : sg C x = c.formPerm x := by
  induction C with
  | nil => simp at hc
  | cons c' C ih =>
    rw [List.flatten_cons, List.nodup_append] at hnd
    show c'.formPerm (sg C x) = _
    by_cases hx' : x ∈ c'
    · have hxC : x ∉ C.flatten := fun h => hnd.2.2 x hx' x h rfl
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [sg_fix hxC]
      · exact absurd (List.mem_flatten_of_mem hc hx) hxC
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact absurd hx hx'
      rw [ih hnd.2.1 hc]
      refine List.formPerm_apply_of_notMem fun h => hnd.2.2 _ h _
        (List.mem_flatten_of_mem hc (List.formPerm_apply_mem_of_mem hx)) rfl

/-- Pairing two `V`s inside one cycle. -/
private theorem sg_split {R : List (List ℕ)} {c c₁ c₂ X Y : List ℕ} {a b : ℕ}
    (hnd : (c :: R).flatten.Nodup) (hc : c ~r a :: X ++ b :: Y) (h1 : c₁ ~r a :: Y)
    (h2 : c₂ ~r b :: X) :
    sg (c₁ :: c₂ :: R) = sg (c :: R) * Equiv.swap a b ∧
      List.Perm (c₁ :: c₂ :: R).flatten (c :: R).flatten := by
  have hp : List.Perm (c₁ :: c₂ :: R).flatten (c :: R).flatten := by
    have := h1.perm; have := h2.perm; have := hc.perm
    rw [List.perm_iff_count] at *
    intro x; simp_all [List.count_append, List.count_cons]; omega
  refine ⟨?_, hp⟩
  rw [List.flatten_cons, List.nodup_append] at hnd
  have hnc : (a :: X ++ b :: Y).Nodup := hc.nodup_iff.mp hnd.1
  have hab : a ∉ R.flatten ∧ b ∉ R.flatten :=
    ⟨fun h => hnd.2.2 a (hc.mem_iff.mpr (by simp)) a h rfl,
      fun h => hnd.2.2 b (hc.mem_iff.mpr (by simp)) b h rfl⟩
  have hsw : sg R * Equiv.swap a b = Equiv.swap a b * sg R := by
    rw [Equiv.mul_swap_eq_swap_mul, sg_fix hab.1, sg_fix hab.2]
  simp only [sg, List.map_cons, List.prod_cons] at hsw ⊢
  rw [List.formPerm_eq_of_isRotated hnd.1 hc, mul_assoc (a :: X ++ b :: Y).formPerm, hsw,
    ← mul_assoc (a :: X ++ b :: Y).formPerm, fp_split hnc,
    List.formPerm_eq_of_isRotated ((h1.nodup_iff).mpr (hnc.sublist (by simp))) h1,
    List.formPerm_eq_of_isRotated ((h2.nodup_iff).mpr ((List.perm_append_singleton b X).nodup_iff.mp
      (hnc.sublist (((List.Sublist.refl X).append (List.singleton_sublist.mpr (by simp))).cons a))))
      h2, mul_assoc]

/-- Pairing two `V`s of different cycles. -/
private theorem sg_merge {R : List (List ℕ)} {c c₁ c₂ X Y : List ℕ} {a b : ℕ}
    (hnd : (c₁ :: c₂ :: R).flatten.Nodup) (h1 : c₁ ~r a :: X) (h2 : c₂ ~r b :: Y)
    (hc : c ~r a :: Y ++ b :: X) :
    sg (c :: R) = sg (c₁ :: c₂ :: R) * Equiv.swap a b ∧
      List.Perm (c :: R).flatten (c₁ :: c₂ :: R).flatten := by
  have hp : List.Perm (c₁ :: c₂ :: R).flatten (c :: R).flatten := by
    have := h1.perm; have := h2.perm; have := hc.perm
    rw [List.perm_iff_count] at *
    intro x; simp_all [List.count_append, List.count_cons]; omega
  obtain ⟨h, -⟩ := sg_split (hp.nodup_iff.mp hnd) hc h1 h2
  refine ⟨?_, hp.symm⟩
  rw [h, Equiv.mul_swap_mul_self]

/-! ### Configurations as lists of cycles

A cycle is a list of pieces: an optional marker position (the rank-one projection `v v*`) followed
by a segment of letter positions. A cycle without marker is a normalised trace, a cycle with `k`
markers is the product of `k` marked forms. -/

/-- A piece of a cycle: an optional marker position and a segment. -/
private abbrev Pc : Type := Option ℕ × List ℕ

private def cF (c : List Pc) : List ℕ := c.flatMap fun pc => pc.1.toList ++ pc.2

private def pos (L : List (List Pc)) : List ℕ := (L.map cF).flatten

private def σL (L : List (List Pc)) : Equiv.Perm ℕ := sg (L.map cF)

/-- The word read off a segment. -/
private def fgt (ℓ : ℕ → Option WLetter) (s : List ℕ) : List WLetter := s.filterMap ℓ

/-- A marked form if there is a marker, a trace otherwise. -/
private def kd (o : Option ℕ) (u : List WLetter) : CfgVar := if o.isSome then .mrk u else .trc u

/-- The factors read off a cycle. -/
private def rdc (ℓ : ℕ → Option WLetter) (c : List Pc) : CfgVar →₀ ℕ :=
  (c.map fun pc => Finsupp.single (kd pc.1 (fgt ℓ pc.2)) 1).sum

private def rdL (ℓ : ℕ → Option WLetter) (L : List (List Pc)) : CfgVar →₀ ℕ :=
  (L.map (rdc ℓ)).sum

/-- Erasing the letters at two positions (after pairing them). -/
private def ers (ℓ : ℕ → Option WLetter) (a b : ℕ) : ℕ → Option WLetter :=
  fun x => if x = a ∨ x = b then none else ℓ x

variable (Ps : Set ℕ) (D : Finset ℕ) (d₀ : CfgVar →₀ ℕ)

/-- A well-formed cycle: marker positions in `Ps`, segment positions outside `Ps`, and a cycle
without marker is a single nonempty segment. -/
private def okc (c : List Pc) : Prop :=
  c ≠ [] ∧ ∀ pc ∈ c, (∀ x ∈ pc.2, x ∉ Ps) ∧ (∀ p ∈ pc.1, p ∈ Ps) ∧
    (pc.1 = none → c = [pc] ∧ pc.2 ≠ [])

/-- `L` is a configuration on the positions `D` with letters `ℓ`. -/
private def Rep (ℓ : ℕ → Option WLetter) (L : List (List Pc)) : Prop :=
  (pos L).Nodup ∧ (pos L).toFinset = D ∧ (∀ x ∈ D, x ∈ Ps → ℓ x = none) ∧ ∀ c ∈ L, okc Ps c

/-- The positions of the letters `V`. -/
private def Vs (ℓ : ℕ → Option WLetter) : Finset ℕ := D.filter fun x => ℓ x = some .v

/-- The normalised expansion of the configurations with successor permutation `σ`. -/
private def Val (ℓ : ℕ → Option WLetter) (σ : Equiv.Perm ℕ) : Loc :=
  if h : ∃ L, Rep Ps D ℓ L ∧ σL L = σ then Zh (d₀ + rdL ℓ h.choose) else 0

private theorem ers_comm (ℓ : ℕ → Option WLetter) (a b : ℕ) : ers ℓ a b = ers ℓ b a := by
  funext x; simp only [ers, or_comm]

private theorem ers_ers (ℓ : ℕ → Option WLetter) (a b c d : ℕ) :
    ers (ers ℓ a b) c d = ers (ers ℓ c d) a b := by
  funext x; simp only [ers]; split_ifs <;> tauto

private theorem Vs_ers {ℓ : ℕ → Option WLetter} (a b : ℕ) :
    Vs D (ers ℓ a b) = ((Vs D ℓ).erase a).erase b := by
  ext x; by_cases h : x = a ∨ x = b <;> simp [Vs, ers] <;> tauto

private theorem fgt_ers {ℓ : ℕ → Option WLetter} {a b : ℕ} {s : List ℕ} (ha : a ∉ s)
    (hb : b ∉ s) : fgt (ers ℓ a b) s = fgt ℓ s :=
  List.filterMap_congr fun x hx => by
    simp only [ers]; rw [ite_eq_right_iff.mpr (by rintro (rfl | rfl) <;> contradiction)]

private theorem rdc_ers {ℓ : ℕ → Option WLetter} {a b : ℕ} {c : List Pc} (ha : a ∉ cF c)
    (hb : b ∉ cF c) : rdc (ers ℓ a b) c = rdc ℓ c := by
  simp only [rdc, cF, List.mem_flatMap, List.mem_append, not_exists, not_and, not_or] at *
  exact congrArg List.sum (List.map_congr_left fun pc hpc => by
    rw [fgt_ers (ha pc hpc).2 (hb pc hpc).2])

private theorem rdL_ers {ℓ : ℕ → Option WLetter} {a b : ℕ} {L : List (List Pc)} (ha : a ∉ pos L)
    (hb : b ∉ pos L) : rdL (ers ℓ a b) L = rdL ℓ L := by
  simp only [rdL, pos, List.mem_flatten, List.mem_map, not_exists, not_and] at *
  exact congrArg List.sum (List.map_congr_left fun c hc => rdc_ers
    (fun h => ha _ ⟨c, hc, rfl⟩ h) (fun h => hb _ ⟨c, hc, rfl⟩ h))

private theorem rep_perm {ℓ : ℕ → Option WLetter} {L L' : List (List Pc)} (h : List.Perm L L')
    (hR : Rep Ps D ℓ L) :
    Rep Ps D ℓ L' ∧ σL L' = σL L ∧ ∀ ℓ', rdL ℓ' L' = rdL ℓ' L := by
  have hp : List.Perm (pos L) (pos L') := (h.map cF).flatten
  refine ⟨⟨hp.nodup_iff.mp hR.1, (List.toFinset_eq_of_perm _ _ hp).symm.trans hR.2.1, hR.2.2.1,
    fun c hc => hR.2.2.2 c (h.mem_iff.mpr hc)⟩, (sg_perm (h.map cF) hR.1).symm,
    fun ℓ' => (h.map _).sum_eq.symm⟩

/-- Rotating a cycle by whole pieces changes nothing. -/
private theorem rep_rot {ℓ : ℕ → Option WLetter} {c₁ c₂ : List Pc} {L : List (List Pc)}
    (hR : Rep Ps D ℓ ((c₁ ++ c₂) :: L)) :
    Rep Ps D ℓ ((c₂ ++ c₁) :: L) ∧ σL ((c₂ ++ c₁) :: L) = σL ((c₁ ++ c₂) :: L) ∧
      ∀ ℓ', rdL ℓ' ((c₂ ++ c₁) :: L) = rdL ℓ' ((c₁ ++ c₂) :: L) := by
  have hrot : cF (c₂ ++ c₁) ~r cF (c₁ ++ c₂) := by
    simpa [cF] using List.isRotated_append (l := cF c₂) (l' := cF c₁)
  have hp : List.Perm (pos ((c₂ ++ c₁) :: L)) (pos ((c₁ ++ c₂) :: L)) := by
    simpa [pos] using hrot.perm.append_right _
  obtain ⟨hnd, hD, hP, hok⟩ := hR
  refine ⟨⟨hp.nodup_iff.mpr hnd, (List.toFinset_eq_of_perm _ _ hp).trans hD, hP, ?_⟩, ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨hne, hpc⟩ := hok _ (List.mem_cons_self ..)
      refine ⟨by simp only [ne_eq, List.append_eq_nil_iff, not_and] at hne ⊢; tauto,
        fun pc hpc' => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hpc pc (by simpa [or_comm] using hpc')
      refine ⟨h1, h2, fun hn => ⟨?_, (h3 hn).2⟩⟩
      have := (h3 hn).1
      rcases c₁ with _ | ⟨x, _ | ⟨y, c₁⟩⟩ <;> rcases c₂ with _ | ⟨z, c₂⟩ <;> simp_all
    · exact hok c (List.mem_cons_of_mem _ hc)
  · simp only [σL, sg, List.map_cons, List.prod_cons]
    rw [List.formPerm_eq_of_isRotated (hrot.nodup_iff.mpr (List.nodup_append.mp hnd).1) hrot]
  · intro ℓ'; simp [rdL, rdc, add_comm]

private theorem cF_cons (pc : Pc) (c : List Pc) : cF (pc :: c) = pc.1.toList ++ pc.2 ++ cF c := by
  simp [cF]

private theorem cF_append (c c' : List Pc) : cF (c ++ c') = cF c ++ cF c' := by simp [cF]

private theorem pos_cons (c : List Pc) (L : List (List Pc)) : pos (c :: L) = cF c ++ pos L := rfl

private theorem rdc_cons (ℓ : ℕ → Option WLetter) (pc : Pc) (c : List Pc) :
    rdc ℓ (pc :: c) = Finsupp.single (kd pc.1 (fgt ℓ pc.2)) 1 + rdc ℓ c := by simp [rdc]

private theorem rdc_append (ℓ : ℕ → Option WLetter) (c c' : List Pc) :
    rdc ℓ (c ++ c') = rdc ℓ c + rdc ℓ c' := by simp [rdc]

private theorem rdL_cons (ℓ : ℕ → Option WLetter) (c : List Pc) (L : List (List Pc)) :
    rdL ℓ (c :: L) = rdc ℓ c + rdL ℓ L := by simp [rdL]

private theorem fgt_append (ℓ : ℕ → Option WLetter) (s s' : List ℕ) :
    fgt ℓ (s ++ s') = fgt ℓ s ++ fgt ℓ s' := List.filterMap_append

private theorem fgt_nil (ℓ : ℕ → Option WLetter) : fgt ℓ [] = [] := rfl

private theorem fgt_ersc {ℓ : ℕ → Option WLetter} {a b : ℕ} {s : List ℕ} (ha : s.count a = 0)
    (hb : s.count b = 0) : fgt (ers ℓ a b) s = fgt ℓ s :=
  fgt_ers (List.count_eq_zero.mp ha) (List.count_eq_zero.mp hb)

private theorem rdc_ersc {ℓ : ℕ → Option WLetter} {a b : ℕ} {c : List Pc}
    (ha : (cF c).count a = 0) (hb : (cF c).count b = 0) : rdc (ers ℓ a b) c = rdc ℓ c :=
  rdc_ers (List.count_eq_zero.mp ha) (List.count_eq_zero.mp hb)

private theorem rdL_ersc {ℓ : ℕ → Option WLetter} {a b : ℕ} {L : List (List Pc)}
    (ha : (pos L).count a = 0) (hb : (pos L).count b = 0) : rdL (ers ℓ a b) L = rdL ℓ L :=
  rdL_ers (List.count_eq_zero.mp ha) (List.count_eq_zero.mp hb)

private theorem fgt_ers_cons {ℓ : ℕ → Option WLetter} {a b x : ℕ} (hx : x = a ∨ x = b)
    (s : List ℕ) : fgt (ers ℓ a b) (x :: s) = fgt (ers ℓ a b) s := by
  simp [fgt, ers, hx]

private theorem okc_some {p : ℕ} {s : List ℕ} {c₁ c₂ : List Pc}
    (h : okc Ps (c₁ ++ (some p, s) :: c₂)) :
    ∀ pc ∈ c₁ ++ (some p, s) :: c₂, (∃ q ∈ Ps, pc.1 = some q) ∧ ∀ x ∈ pc.2, x ∉ Ps := by
  intro pc hpc
  obtain ⟨h1, h2, h3⟩ := h.2 pc hpc
  refine ⟨?_, h1⟩
  rcases hq : pc.1 with _ | q
  · have h4 := (h3 hq).1
    have : (some p, s) ∈ c₁ ++ (some p, s) :: c₂ := by simp
    rw [h4, List.mem_singleton] at this; rw [← this] at hq; simp at hq
  · exact ⟨q, h2 q hq, rfl⟩

private theorem okc_none {s : List ℕ} {c₁ c₂ : List Pc} (h : okc Ps (c₁ ++ (none, s) :: c₂)) :
    c₁ = [] ∧ c₂ = [] ∧ s ≠ [] ∧ ∀ x ∈ s, x ∉ Ps := by
  obtain ⟨h1, -, h3⟩ := h.2 (none, s) (by simp)
  obtain ⟨h4, h5⟩ := h3 rfl
  have := congrArg List.length h4
  simp at this
  obtain ⟨rfl, rfl⟩ : c₁ = [] ∧ c₂ = [] := ⟨List.eq_nil_of_length_eq_zero (by omega),
    List.eq_nil_of_length_eq_zero (by omega)⟩
  exact ⟨rfl, rfl, h5, h1⟩

private theorem okc_mk {c : List Pc} (hne : c ≠ [])
    (h : ∀ pc ∈ c, (∃ q ∈ Ps, pc.1 = some q) ∧ ∀ x ∈ pc.2, x ∉ Ps) : okc Ps c :=
  ⟨hne, fun pc hpc => by
    obtain ⟨⟨q, hq, hpq⟩, h2⟩ := h pc hpc
    exact ⟨h2, fun r hr => by rw [hpq] at hr; cases hr; exact hq, fun hn => by simp_all⟩⟩

private theorem okc_trc {s : List ℕ} (hne : s ≠ []) (h : ∀ x ∈ s, x ∉ Ps) :
    okc Ps [(none, s)] :=
  ⟨by simp, fun pc hpc => by
    rw [List.mem_singleton] at hpc; subst hpc; exact ⟨h, by simp, fun _ => ⟨rfl, hne⟩⟩⟩

private theorem rep_new {ℓ : ℕ → Option WLetter} {L N : List (List Pc)} {a b : ℕ}
    (hR : Rep Ps D ℓ L) (hp : List.Perm (pos N) (pos L)) (hok : ∀ c ∈ N, okc Ps c) :
    Rep Ps D (ers ℓ a b) N :=
  ⟨hp.nodup_iff.mpr hR.1, (List.toFinset_eq_of_perm _ _ hp).trans hR.2.1, fun x hx hxP => by
    simp only [ers]; split_ifs; exacts [rfl, hR.2.2.1 x hx hxP], hok⟩

/-- Pairing inside one cycle, at the level of configurations. -/
private theorem rep_split {ℓ : ℕ → Option WLetter} {c c₁ c₂ : List Pc} {L : List (List Pc)}
    {X Y : List ℕ} {a b : ℕ} (hR : Rep Ps D ℓ (c :: L)) (hc : cF c ~r a :: X ++ b :: Y)
    (h1 : cF c₁ ~r a :: Y) (h2 : cF c₂ ~r b :: X) (hok1 : okc Ps c₁) (hok2 : okc Ps c₂) :
    Rep Ps D (ers ℓ a b) (c₁ :: c₂ :: L) ∧
      σL (c₁ :: c₂ :: L) = σL (c :: L) * Equiv.swap a b := by
  obtain ⟨h, hp⟩ := sg_split (c := cF c) (R := L.map cF) hR.1 hc h1 h2
  refine ⟨rep_new Ps D hR hp fun c' hc' => ?_, h⟩
  rcases List.mem_cons.mp hc' with rfl | hc'
  · exact hok1
  rcases List.mem_cons.mp hc' with rfl | hc'
  exacts [hok2, hR.2.2.2 c' (List.mem_cons_of_mem _ hc')]

/-- Pairing in two different cycles, at the level of configurations. -/
private theorem rep_merge {ℓ : ℕ → Option WLetter} {c c₁ c₂ : List Pc} {L : List (List Pc)}
    {X Y : List ℕ} {a b : ℕ} (hR : Rep Ps D ℓ (c₁ :: c₂ :: L)) (h1 : cF c₁ ~r a :: X)
    (h2 : cF c₂ ~r b :: Y) (hc : cF c ~r a :: Y ++ b :: X) (hok : okc Ps c) :
    Rep Ps D (ers ℓ a b) (c :: L) ∧ σL (c :: L) = σL (c₁ :: c₂ :: L) * Equiv.swap a b := by
  obtain ⟨h, hp⟩ := sg_merge (c := cF c) (R := L.map cF) hR.1 h1 h2 hc
  refine ⟨rep_new Ps D hR hp fun c' hc' => ?_, h⟩
  rcases List.mem_cons.mp hc' with rfl | hc'
  exacts [hok, hR.2.2.2 c' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc'))]

private theorem rot_app {x r : List ℕ} (l l' : List ℕ) (h₁ : x = l ++ l') (h₂ : l' ++ l = r) :
    x ~r r :=
  h₁ ▸ h₂ ▸ List.isRotated_append

private theorem cF_nil : cF [] = [] := rfl

/-- Pairing two `V`s of one piece. -/
private theorem st_self {ℓ : ℕ → Option WLetter} {o : Option ℕ} {A m₁ m₂ : List ℕ}
    {c' : List Pc} {L : List (List Pc)} {a b : ℕ}
    (hR : Rep Ps D ℓ (((o, A ++ a :: m₁ ++ b :: m₂) :: c') :: L)) :
    Rep Ps D (ers ℓ a b) (((o, A ++ a :: m₂) :: c') :: [(none, b :: m₁)] :: L) ∧
    σL (((o, A ++ a :: m₂) :: c') :: [(none, b :: m₁)] :: L) =
      σL (((o, A ++ a :: m₁ ++ b :: m₂) :: c') :: L) * Equiv.swap a b ∧
    rdL (ers ℓ a b) (((o, A ++ a :: m₂) :: c') :: [(none, b :: m₁)] :: L) =
      Finsupp.single (kd o (fgt ℓ A ++ fgt ℓ m₂)) 1 + rdc ℓ c' +
        Finsupp.single (.trc (fgt ℓ m₁)) 1 + rdL ℓ L := by
  have hok := hR.2.2.2 _ (List.mem_cons_self ..)
  have hseg := (hok.2 _ (List.mem_cons_self ..)).1
  have hok1 : okc Ps ((o, A ++ a :: m₂) :: c') := by
    rcases o with _ | p
    · obtain ⟨-, rfl, -, -⟩ := okc_none Ps (c₁ := []) hok
      exact okc_trc Ps (by simp) fun x hx => hseg x (by simp at hx ⊢; tauto)
    · have := okc_some Ps (c₁ := []) hok
      refine okc_mk Ps (by simp) fun pc hpc => ?_
      rcases List.mem_cons.mp hpc with rfl | hpc
      · exact ⟨(this _ (List.mem_cons_self ..)).1, fun x hx => hseg x (by simp at hx ⊢; tauto)⟩
      · exact this pc (List.mem_cons_of_mem _ hpc)
  obtain ⟨h1, h2⟩ := rep_split Ps D (c₁ := (o, A ++ a :: m₂) :: c') (c₂ := [(none, b :: m₁)])
    (a := a) (b := b) (X := m₁) (Y := m₂ ++ cF c' ++ o.toList ++ A) hR
    (rot_app (o.toList ++ A) (a :: m₁ ++ b :: m₂ ++ cF c') (by simp [cF_cons]) (by simp))
    (rot_app (o.toList ++ A) (a :: m₂ ++ cF c') (by simp [cF_cons]) (by simp))
    (by simp [cF_cons, cF_nil]; exact List.IsRotated.refl _) hok1
    (okc_trc Ps (by simp) fun x hx => hseg x (by simp at hx ⊢; tauto))
  refine ⟨h1, h2, ?_⟩
  have hn := hR.1
  simp only [pos_cons, cF_cons] at hn
  have hab : a ≠ b := fun h => by subst h; simp [List.nodup_append] at hn
  have ca := List.nodup_iff_count_le_one.mp hn a
  have cb := List.nodup_iff_count_le_one.mp hn b
  simp [List.count_append, hab, hab.symm] at ca cb
  simp (disch := omega) only [rdL_cons, rdc_cons, fgt_append, fgt_ers_cons, fgt_ersc, rdc_ersc,
    rdL_ersc]
  simp [rdc, kd, add_assoc]

/-- Pairing the `V`s of two pieces of one cycle with markers. -/
private theorem st_mms {ℓ : ℕ → Option WLetter} {p q : ℕ} {A B m₁ m₂ : List ℕ}
    {c₁ c₂ : List Pc} {L : List (List Pc)} {a b : ℕ}
    (hR : Rep Ps D ℓ (((some p, A ++ a :: B) :: c₁ ++ (some q, m₁ ++ b :: m₂) :: c₂) :: L)) :
    Rep Ps D (ers ℓ a b) (((some p, A ++ a :: m₂) :: c₂) :: ((some q, m₁ ++ b :: B) :: c₁) :: L) ∧
    σL (((some p, A ++ a :: m₂) :: c₂) :: ((some q, m₁ ++ b :: B) :: c₁) :: L) =
      σL (((some p, A ++ a :: B) :: c₁ ++ (some q, m₁ ++ b :: m₂) :: c₂) :: L) *
        Equiv.swap a b ∧
    rdL (ers ℓ a b) (((some p, A ++ a :: m₂) :: c₂) :: ((some q, m₁ ++ b :: B) :: c₁) :: L) =
      Finsupp.single (.mrk (fgt ℓ A ++ fgt ℓ m₂)) 1 +
        Finsupp.single (.mrk (fgt ℓ m₁ ++ fgt ℓ B)) 1 + rdc ℓ (c₁ ++ c₂) + rdL ℓ L := by
  have hok := okc_some Ps (c₁ := []) (hR.2.2.2 _ (List.mem_cons_self ..))
  have h1 := hok _ (List.mem_cons_self ..)
  have h2 := hok (some q, m₁ ++ b :: m₂) (by simp)
  obtain ⟨hr1, hr2⟩ := rep_split Ps D (c₁ := (some p, A ++ a :: m₂) :: c₂)
    (c₂ := (some q, m₁ ++ b :: B) :: c₁) (a := a) (b := b) (X := B ++ cF c₁ ++ q :: m₁)
    (Y := m₂ ++ cF c₂ ++ p :: A) hR
    (rot_app (p :: A) (a :: B ++ cF c₁ ++ q :: m₁ ++ b :: m₂ ++ cF c₂)
      (by simp [cF_cons, cF_append]) (by simp))
    (rot_app (p :: A) (a :: m₂ ++ cF c₂) (by simp [cF_cons]) (by simp))
    (rot_app (q :: m₁) (b :: B ++ cF c₁) (by simp [cF_cons]) (by simp))
    (okc_mk Ps (by simp) fun pc hpc => by
      rcases List.mem_cons.mp hpc with rfl | hpc
      · exact ⟨h1.1, fun x hx => by
          simp at hx; rcases hx with hx | rfl | hx
          exacts [h1.2 x (by simp [hx]), h1.2 x (by simp), h2.2 x (by simp [hx])]⟩
      · exact hok pc (by simp [hpc]))
    (okc_mk Ps (by simp) fun pc hpc => by
      rcases List.mem_cons.mp hpc with rfl | hpc
      · exact ⟨h2.1, fun x hx => by
          simp at hx; rcases hx with hx | rfl | hx
          exacts [h2.2 x (by simp [hx]), h2.2 x (by simp), h1.2 x (by simp [hx])]⟩
      · exact hok pc (by simp [hpc]))
  refine ⟨hr1, hr2, ?_⟩
  have hn := hR.1
  simp only [pos_cons, cF_cons, cF_append] at hn
  have hab : a ≠ b := fun h => by subst h; simp [List.nodup_append] at hn
  have hP : ∀ x, x ∈ Ps → x ≠ a ∧ x ≠ b := fun x hx => ⟨fun h => h1.2 a (by simp) (h ▸ hx),
    fun h => h2.2 b (by simp) (h ▸ hx)⟩
  obtain ⟨⟨r, hr, hpr⟩, -⟩ := h1
  obtain ⟨⟨r', hr', hqr⟩, -⟩ := h2
  cases hpr; cases hqr
  have ca := List.nodup_iff_count_le_one.mp hn a
  have cb := List.nodup_iff_count_le_one.mp hn b
  simp [List.count_append, hab, hab.symm, hP _ hr, hP _ hr'] at ca cb
  simp (disch := omega) only [rdL_cons, rdc_cons, fgt_append, fgt_ers_cons, fgt_ersc, rdc_ersc,
    rdL_ersc, rdc_append]
  simp only [kd, Option.isSome_some, ite_true]
  abel

/-- The factors produced by pairing the `V`s of `A V B` and `C V D` (for `r = false` those of
`crossPair`; for `r = true` the trace `Tr(BADC)` is read from `D`). -/
private def cpx (r : Bool) : Bool → Bool → List WLetter → List WLetter → List WLetter →
    List WLetter → CfgVar →₀ ℕ
  | false, false, A, B, C', D =>
    Finsupp.single (.trc (if r then D ++ C' ++ B ++ A else B ++ A ++ D ++ C')) 1
  | true, false, A, B, C', D => Finsupp.single (.mrk (A ++ D ++ C' ++ B)) 1
  | false, true, A, B, C', D => Finsupp.single (.mrk (C' ++ B ++ A ++ D)) 1
  | true, true, A, B, C', D => Finsupp.single (.mrk (A ++ D)) 1 + Finsupp.single (.mrk (C' ++ B)) 1

private theorem crossPair_eq (φ ψ : CfgVar) (j : ℕ) :
    (crossPair φ ψ j).2 = cpx false φ.isMrk ψ.isMrk (φ.word.take (φ.word.idxOf .v))
      (φ.word.drop (φ.word.idxOf .v + 1)) (ψ.word.take j) (ψ.word.drop (j + 1)) := by
  unfold crossPair; cases φ.isMrk <;> cases ψ.isMrk <;> rfl

/-- Pairing the `V`s of two different cycles. -/
private theorem st_cross {ℓ : ℕ → Option WLetter} {o o' : Option ℕ} {A B m₁ m₂ : List ℕ}
    {c' c₁ c₂ : List Pc} {L : List (List Pc)} {a b : ℕ} (r : Bool)
    (hR : Rep Ps D ℓ (((o, A ++ a :: B) :: c') :: (c₁ ++ (o', m₁ ++ b :: m₂) :: c₂) :: L)) :
    ∃ N, Rep Ps D (ers ℓ a b) N ∧
      σL N = σL (((o, A ++ a :: B) :: c') :: (c₁ ++ (o', m₁ ++ b :: m₂) :: c₂) :: L) *
        Equiv.swap a b ∧
      rdL (ers ℓ a b) N = cpx r o.isSome o'.isSome (fgt ℓ A) (fgt ℓ B) (fgt ℓ m₁) (fgt ℓ m₂) +
        rdc ℓ c' + rdc ℓ (c₁ ++ c₂) + rdL ℓ L := by
  have hok := hR.2.2.2 _ (List.mem_cons_self ..)
  have hok' := hR.2.2.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hn := hR.1
  simp only [pos_cons, cF_cons, cF_append] at hn
  have hab : a ≠ b := fun h => by subst h; simp [List.nodup_append] at hn
  have ca := List.nodup_iff_count_le_one.mp hn a
  have cb := List.nodup_iff_count_le_one.mp hn b
  simp [List.count_append, hab, hab.symm] at ca cb
  have hX := (hok.2 _ (List.mem_cons_self ..)).1
  have hY := (hok'.2 (o', m₁ ++ b :: m₂) (by simp)).1
  rcases o with _ | p <;> rcases o' with _ | q
  · obtain ⟨-, rfl, -, -⟩ := okc_none Ps (c₁ := []) hok
    obtain ⟨rfl, rfl, -, -⟩ := okc_none Ps hok'
    cases r
    · obtain ⟨h1, h2⟩ := rep_merge Ps D (c := [(none, B ++ A ++ a :: m₂ ++ m₁ ++ [b])]) (a := a)
        (b := b) (X := B ++ A) (Y := m₂ ++ m₁) hR (rot_app A (a :: B) (by simp [cF]) (by simp))
        (rot_app m₁ (b :: m₂) (by simp [cF]) (by simp))
        (rot_app (B ++ A) (a :: m₂ ++ m₁ ++ [b]) (by simp [cF]) (by simp))
        (okc_trc Ps (by simp) fun x hx => by
          simp at hx; rcases hx with hx | hx | rfl | hx | hx | rfl <;> simp_all)
      refine ⟨_, h1, h2, ?_⟩
      simp (disch := omega) only [rdL_cons, rdc_cons, fgt_append, fgt_ers_cons, fgt_ersc,
        rdc_ersc, rdL_ersc, fgt_nil]
      simp [cpx, kd, rdc]
    · obtain ⟨h1, h2⟩ := rep_merge Ps D (c := [(none, a :: m₂ ++ m₁ ++ b :: B ++ A)]) (a := a)
        (b := b) (X := B ++ A) (Y := m₂ ++ m₁) hR (rot_app A (a :: B) (by simp [cF]) (by simp))
        (rot_app m₁ (b :: m₂) (by simp [cF]) (by simp))
        (rot_app [] (a :: m₂ ++ m₁ ++ b :: B ++ A) (by simp [cF]) (by simp))
        (okc_trc Ps (by simp) fun x hx => by
          simp at hx; rcases hx with rfl | hx | hx | rfl | hx | hx <;> simp_all)
      refine ⟨_, h1, h2, ?_⟩
      simp (disch := omega) only [rdL_cons, rdc_cons, fgt_append, fgt_ers_cons, fgt_ersc,
        rdc_ersc, rdL_ersc]
      simp [cpx, kd, rdc]
  · obtain ⟨-, rfl, -, -⟩ := okc_none Ps (c₁ := []) hok
    have hm := okc_some Ps hok'
    obtain ⟨h1, h2⟩ := rep_merge Ps D (c := (some q, m₁ ++ b :: B ++ A ++ a :: m₂) :: c₂ ++ c₁)
      (a := a) (b := b) (X := B ++ A) (Y := m₂ ++ cF c₂ ++ cF c₁ ++ q :: m₁) hR
      (rot_app A (a :: B) (by simp [cF]) (by simp))
      (rot_app (cF c₁ ++ q :: m₁) (b :: m₂ ++ cF c₂) (by simp [cF_cons, cF_append]) (by simp))
      (rot_app (q :: m₁ ++ b :: B ++ A) (a :: m₂ ++ cF c₂ ++ cF c₁) (by simp [cF_cons, cF_append])
        (by simp))
      (okc_mk Ps (by simp) fun pc hpc => by
        rcases List.mem_cons.mp hpc with rfl | hpc
        · refine ⟨(hm (some q, m₁ ++ b :: m₂) (by simp)).1, fun x hx => ?_⟩
          simp at hx; rcases hx with hx | rfl | hx | hx | rfl | hx <;> simp_all
        · exact hm pc (by simp at hpc ⊢; tauto))
    refine ⟨_, h1, h2, ?_⟩
    simp (disch := omega) only [rdL_cons, rdc_cons, fgt_append, fgt_ers_cons, fgt_ersc, rdc_ersc,
      rdL_ersc, rdc_append]
    simp [cpx, kd, rdc]; abel
  · obtain ⟨rfl, rfl, -, -⟩ := okc_none Ps hok'
    have hm := okc_some Ps (c₁ := []) hok
    obtain ⟨h1, h2⟩ := rep_merge Ps D (c := (some p, A ++ a :: m₂ ++ m₁ ++ b :: B) :: c')
      (a := a) (b := b) (X := B ++ cF c' ++ p :: A) (Y := m₂ ++ m₁) hR
      (rot_app (p :: A) (a :: B ++ cF c') (by simp [cF_cons]) (by simp))
      (rot_app m₁ (b :: m₂) (by simp [cF]) (by simp))
      (rot_app (p :: A) (a :: m₂ ++ m₁ ++ b :: B ++ cF c') (by simp [cF_cons]) (by simp))
      (okc_mk Ps (by simp) fun pc hpc => by
        rcases List.mem_cons.mp hpc with rfl | hpc
        · refine ⟨(hm _ (List.mem_cons_self ..)).1, fun x hx => ?_⟩
          simp at hx; rcases hx with hx | rfl | hx | hx | rfl | hx <;> simp_all
        · exact hm pc (List.mem_cons_of_mem _ hpc))
    refine ⟨_, h1, h2, ?_⟩
    simp (disch := omega) only [rdL_cons, rdc_cons, fgt_append, fgt_ers_cons, fgt_ersc, rdc_ersc,
      rdL_ersc]
    simp [cpx, kd, rdc, add_assoc]
  · have hm := okc_some Ps (c₁ := []) hok
    have hm' := okc_some Ps hok'
    obtain ⟨h1, h2⟩ := rep_merge Ps D
      (c := (some p, A ++ a :: m₂) :: c₂ ++ c₁ ++ (some q, m₁ ++ b :: B) :: c')
      (a := a) (b := b) (X := B ++ cF c' ++ p :: A) (Y := m₂ ++ cF c₂ ++ cF c₁ ++ q :: m₁) hR
      (rot_app (p :: A) (a :: B ++ cF c') (by simp [cF_cons]) (by simp))
      (rot_app (cF c₁ ++ q :: m₁) (b :: m₂ ++ cF c₂) (by simp [cF_cons, cF_append]) (by simp))
      (rot_app (p :: A) (a :: m₂ ++ cF c₂ ++ cF c₁ ++ q :: m₁ ++ b :: B ++ cF c')
        (by simp [cF_cons, cF_append]) (by simp))
      (okc_mk Ps (by simp) fun pc hpc => by
        simp only [List.cons_append, List.mem_cons, List.mem_append] at hpc
        obtain rfl | hpc := hpc
        · refine ⟨(hm _ (List.mem_cons_self ..)).1, fun x hx => ?_⟩
          simp only [List.mem_append, List.mem_cons] at hx
          rcases hx with hx | rfl | hx
          exacts [hX x (by simp [hx]), hX _ (by simp), hY x (by simp [hx])]
        obtain (hpc | hpc) | rfl | hpc := hpc
        · exact hm' pc (by simp [hpc])
        · exact hm' pc (by simp [hpc])
        · refine ⟨(hm' (some q, m₁ ++ b :: m₂) (by simp)).1, fun x hx => ?_⟩
          simp only [List.mem_append, List.mem_cons] at hx
          rcases hx with hx | rfl | hx
          exacts [hY x (by simp [hx]), hY _ (by simp), hX x (by simp [hx])]
        · exact hm pc (List.mem_cons_of_mem _ hpc))
    refine ⟨_, h1, h2, ?_⟩
    simp (disch := omega) only [rdL_cons, rdc_cons, fgt_append, fgt_ers_cons, fgt_ersc, rdc_ersc,
      rdL_ersc, rdc_append]
    simp [cpx, kd, rdc]; abel

/-! ### Configurations with the same successor permutation -/

private theorem sg_sub {C₁ C₂ : List (List ℕ)} (h₁ : C₁.flatten.Nodup) (h₂ : C₂.flatten.Nodup)
    (hσ : sg C₁ = sg C₂) {c₁ c₂ : List ℕ} (hc₁ : c₁ ∈ C₁) (hc₂ : c₂ ∈ C₂) {x : ℕ}
    (hx₁ : x ∈ c₁) (hx₂ : x ∈ c₂) : ∀ y ∈ c₁, y ∈ c₂ := by
  have hn := (List.nodup_flatten.mp h₁).1 c₁ hc₁
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx₁
  have key : ∀ k, (c₁.formPerm ^ k) c₁[i] ∈ c₂ := by
    intro k
    induction k with
    | zero => exact hx₂
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ← sg_apply h₁ hc₁
        (by rw [List.formPerm_pow_apply_getElem _ hn]; exact List.getElem_mem _), hσ,
        sg_apply h₂ hc₂ ih]
      exact List.formPerm_apply_mem_of_mem ih
  intro y hy
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have := key (j + c₁.length - i)
  rw [List.formPerm_pow_apply_getElem _ hn] at this
  have e : (i + (j + c₁.length - i)) % c₁.length = j := by
    rw [show i + (j + c₁.length - i) = j + c₁.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hj]
  simpa only [e] using this

/-- Two cycles of the same successor permutation through one position are rotations. -/
private theorem sg_rot {C₁ C₂ : List (List ℕ)} (h₁ : C₁.flatten.Nodup) (h₂ : C₂.flatten.Nodup)
    (hσ : sg C₁ = sg C₂) {c₁ c₂ : List ℕ} (hc₁ : c₁ ∈ C₁) (hc₂ : c₂ ∈ C₂) {x : ℕ}
    (hx₁ : x ∈ c₁) (hx₂ : x ∈ c₂) : c₁ ~r c₂ := by
  have s₁ := sg_sub h₁ h₂ hσ hc₁ hc₂ hx₁ hx₂
  have s₂ := sg_sub h₂ h₁ hσ.symm hc₂ hc₁ hx₂ hx₁
  have hn₁ := (List.nodup_flatten.mp h₁).1 c₁ hc₁
  have hn₂ := (List.nodup_flatten.mp h₂).1 c₂ hc₂
  have he : c₁.formPerm = c₂.formPerm := Equiv.ext fun y => by
    by_cases hy : y ∈ c₁
    · rw [← sg_apply h₁ hc₁ hy, hσ, sg_apply h₂ hc₂ (s₁ y hy)]
    · rw [List.formPerm_apply_of_notMem hy, List.formPerm_apply_of_notMem fun h => hy (s₂ y h)]
  rcases (List.formPerm_eq_formPerm_iff hn₁ hn₂).mp he with h | ⟨h1, h2⟩
  · exact h
  · rcases c₁ with _ | ⟨u, _ | ⟨u', c₁⟩⟩ <;> rcases c₂ with _ | ⟨w, _ | ⟨w', c₂⟩⟩ <;>
      simp_all

/-- A cycle with markers reads off the segments between consecutive markers. -/
private theorem rdc_splitOnP {ℓ : ℕ → Option WLetter} : ∀ {p : ℕ} {s : List ℕ} {c : List Pc},
    (∀ pc ∈ (some p, s) :: c, (∃ q ∈ Ps, pc.1 = some q) ∧ ∀ x ∈ pc.2, x ∉ Ps) →
    rdc ℓ ((some p, s) :: c) = (((s ++ cF c).splitOnP fun x => decide (x ∈ Ps)).map
      fun u => Finsupp.single (CfgVar.mrk (fgt ℓ u)) 1).sum
  | p, s, [], h => by
    rw [cF_nil, List.append_nil, List.splitOnP_eq_singleton fun x hx => by
      simpa using (h _ (List.mem_cons_self ..)).2 x hx]
    simp [rdc, kd]
  | p, s, (o, s') :: c, h => by
    obtain ⟨⟨q, hq, hq'⟩, -⟩ := h (o, s') (by simp)
    cases hq'
    rw [rdc_cons, rdc_splitOnP fun pc hpc => h pc (List.mem_cons_of_mem _ hpc), cF_cons,
      show (some q).toList ++ s' ++ cF c = q :: (s' ++ cF c) by simp,
      List.splitOnP_append_cons s _ (by simpa using hq),
      List.splitOnP_eq_singleton (xs := s) fun x hx => by
        simpa using (h _ (List.mem_cons_self ..)).2 x hx]
    simp [kd]

private theorem splitOnP_rot {P : ℕ → Bool} {p q : ℕ} {t t' : List ℕ} (hp : P p) (hq : P q)
    (h : p :: t ~r q :: t') : List.Perm (t.splitOnP P) (t'.splitOnP P) := by
  obtain ⟨n, hn, hr⟩ := List.isRotated_iff_mod.mp h
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · simp_all
  rcases Nat.lt_or_ge n (p :: t).length with hlt | hge
  · rw [List.rotate_eq_drop_append_take hn] at hr
    obtain ⟨X, hX⟩ : ∃ X, (p :: t).take n = p :: X :=
      ⟨((p :: t).take n).tail, by cases n <;> simp_all⟩
    obtain ⟨Y, hY⟩ : ∃ Y, (p :: t).drop n = q :: Y := by
      rcases hd : (p :: t).drop n with _ | ⟨z, Y⟩
      · simp at hd hlt; omega
      · rw [hd] at hr; exact ⟨Y, by simp_all⟩
    have ht : p :: t = p :: X ++ q :: Y := by rw [← hX, ← hY, List.take_append_drop]
    rw [hX, hY] at hr
    simp only [List.cons_append, List.cons.injEq] at ht hr
    rw [ht.2, ← hr.2, List.splitOnP_append_cons _ _ hq, List.splitOnP_append_cons _ _ hp]
    exact List.perm_append_comm
  · rw [show n = (p :: t).length by omega, List.rotate_length] at hr
    simp_all

private theorem cF_ne {c : List Pc} (h : okc Ps c) : cF c ≠ [] := by
  obtain ⟨pc, c', rfl⟩ := List.exists_cons_of_ne_nil h.1
  obtain ⟨-, -, h3⟩ := h.2 pc (List.mem_cons_self ..)
  rcases ho : pc.1 with _ | p
  · simp [cF_cons, ho, (h3 ho).2]
  · simp [cF_cons, ho]

private theorem Zh_trc {u : List WLetter} (hu : WLetter.v ∉ u) :
    Zh (Finsupp.single (.trc u) 1) = ι (mVar (wordExp u)) * tinv := by
  rw [Zh, wickZ_of_vc fun x hx => by
    rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hx
    subst hx; exact List.count_eq_zero.mpr hu, Finsupp.prod_single_index (by simp), T_single]
  simp [CfgVar.base, tw]

/-- Two cycles through the same positions in the same cyclic order give the same value. -/
private theorem Zh_rdc_rot {ℓ : ℕ → Option WLetter} {c c₂ : List Pc} (h : okc Ps c)
    (h₂ : okc Ps c₂) (hr : cF c ~r cF c₂) (hv : ∀ x ∈ cF c, ℓ x ≠ some .v) :
    Zh (rdc ℓ c) = Zh (rdc ℓ c₂) := by
  obtain ⟨⟨o, s⟩, c', rfl⟩ := List.exists_cons_of_ne_nil h.1
  obtain ⟨⟨o₂, s₂⟩, c₂', rfl⟩ := List.exists_cons_of_ne_nil h₂.1
  have hm : ∀ x, x ∈ cF ((o, s) :: c') ↔ x ∈ cF ((o₂, s₂) :: c₂') := fun x => hr.mem_iff
  rcases o with _ | p <;> rcases o₂ with _ | q
  · obtain ⟨-, rfl, -, -⟩ := okc_none Ps (c₁ := []) h
    obtain ⟨-, rfl, -, -⟩ := okc_none Ps (c₁ := []) h₂
    simp only [cF_cons, cF_nil, Option.toList_none, List.nil_append, List.append_nil] at hr hv
    have hfp : List.Perm (fgt ℓ s) (fgt ℓ s₂) := hr.perm.filterMap ℓ
    have hvs : WLetter.v ∉ fgt ℓ s := fun h => by
      obtain ⟨x, hx, hxv⟩ := List.mem_filterMap.mp h; exact hv x hx hxv
    simp only [rdc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, kd,
      Option.isSome_none, Bool.false_eq_true, ite_false]
    rw [Zh_trc hvs, Zh_trc fun h => hvs (hfp.mem_iff.mpr h), wordExp, wordExp, hfp.count_eq,
      hfp.count_eq]
  · obtain ⟨-, rfl, -, hP⟩ := okc_none Ps (c₁ := []) h
    obtain ⟨⟨r, hr', hqr⟩, -⟩ := okc_some Ps (c₁ := []) h₂ _ (List.mem_cons_self ..)
    cases hqr
    have hq : q ∈ s := by simpa [cF_cons, cF_nil] using (hm q).mpr (by simp [cF_cons])
    exact absurd hr' (hP q hq)
  · obtain ⟨-, rfl, -, hP⟩ := okc_none Ps (c₁ := []) h₂
    obtain ⟨⟨r, hr', hpr⟩, -⟩ := okc_some Ps (c₁ := []) h _ (List.mem_cons_self ..)
    cases hpr
    have hp : p ∈ s₂ := by simpa [cF_cons, cF_nil] using (hm p).mp (by simp [cF_cons])
    exact absurd hr' (hP p hp)
  · have h1 := okc_some Ps (c₁ := []) h
    have h2 := okc_some Ps (c₁ := []) h₂
    obtain ⟨⟨r, hr', hpr⟩, -⟩ := h1 _ (List.mem_cons_self ..)
    obtain ⟨⟨r₂, hr₂, hqr⟩, -⟩ := h2 _ (List.mem_cons_self ..)
    cases hpr; cases hqr
    rw [rdc_splitOnP Ps h1, rdc_splitOnP Ps h2,
      ((splitOnP_rot (by simpa using hr') (by simpa using hr₂) (by simpa [cF_cons] using hr)).map
        _).sum_eq]

private theorem uniq {ℓ : ℕ → Option WLetter} : ∀ (L₁ L₂ : List (List Pc)), (pos L₁).Nodup →
    (pos L₂).Nodup → List.Perm (pos L₁) (pos L₂) → σL L₁ = σL L₂ → (∀ c ∈ L₁, okc Ps c) →
    (∀ c ∈ L₂, okc Ps c) → (∀ x ∈ pos L₁, ℓ x ≠ some .v) →
    (L₁.map fun c => Zh (rdc ℓ c)).prod = (L₂.map fun c => Zh (rdc ℓ c)).prod
  | [], L₂, _, _, hp, _, _, h₂, _ => by
    cases L₂ with
    | nil => rfl
    | cons c L₂ =>
      exact absurd (List.append_eq_nil_iff.mp (hp.symm.eq_nil)).1
        (cF_ne Ps (h₂ c (List.mem_cons_self ..)))
  | c :: L₁, L₂, n₁, n₂, hp, hσ, h₁, h₂, hv => by
    obtain ⟨x, t, hx⟩ := List.exists_cons_of_ne_nil (cF_ne Ps (h₁ c (List.mem_cons_self ..)))
    obtain ⟨c₂, hc₂, hxc₂⟩ : ∃ c₂ ∈ L₂, x ∈ cF c₂ := by
      have := hp.subset (show x ∈ pos (c :: L₁) by simp [pos_cons, hx])
      simpa [pos] using this
    have hrot := sg_rot n₁ n₂ hσ (List.mem_map_of_mem (List.mem_cons_self ..))
      (List.mem_map_of_mem hc₂) (by simp [hx]) hxc₂
    have hL := List.perm_cons_erase hc₂
    have hpL : List.Perm (pos L₂) (cF c₂ ++ pos (L₂.erase c₂)) := (hL.map cF).flatten
    rw [pos_cons] at n₁ hp hv
    have n₂' := hpL.nodup_iff.mp n₂
    have hp' : List.Perm (pos L₁) (pos (L₂.erase c₂)) :=
      List.perm_append_left_iff _ |>.mp ((hrot.perm.append_right _).symm.trans (hp.trans hpL))
    have hσ' : σL L₁ = σL (L₂.erase c₂) := by
      have e := hσ.trans (sg_perm (hL.map cF) n₂)
      simp only [σL, List.map_cons, sg, List.prod_cons] at e ⊢
      rwa [List.formPerm_eq_of_isRotated (List.nodup_append.mp n₁).1 hrot, mul_right_inj] at e
    rw [List.map_cons, List.prod_cons, (hL.map _).prod_eq, List.map_cons, List.prod_cons,
      Zh_rdc_rot Ps (h₁ c (List.mem_cons_self ..)) (h₂ c₂ hc₂) hrot
        fun y hy => hv y (List.mem_append_left _ hy),
      uniq L₁ (L₂.erase c₂) (List.nodup_append.mp n₁).2.1 (List.nodup_append.mp n₂').2.1 hp' hσ'
        (fun c' hc' => h₁ c' (List.mem_cons_of_mem _ hc'))
        (fun c' hc' => h₂ c' (List.mem_of_mem_erase hc'))
        fun y hy => hv y (List.mem_append_right _ hy)]

private theorem Zh_add {d e : CfgVar →₀ ℕ} (h : ∀ x ∈ (d + e).support, x.vc = 0) :
    Zh (d + e) = Zh d * Zh e := by
  have hd : ∀ x ∈ d.support, x.vc = 0 := fun x hx => h x (by
    simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply] at hx ⊢; omega)
  have he : ∀ x ∈ e.support, x.vc = 0 := fun x hx => h x (by
    simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply] at hx ⊢; omega)
  rw [Zh, Zh, Zh, wickZ_of_vc h, wickZ_of_vc hd, wickZ_of_vc he, Finsupp.prod_add_index'
    (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), T_add, map_mul, pow_add]
  ring

private theorem vc_rdc {ℓ : ℕ → Option WLetter} {c : List Pc} (h : ∀ x ∈ cF c, ℓ x ≠ some .v) :
    ∀ y ∈ (rdc ℓ c).support, y.vc = 0 := by
  induction c with
  | nil => simp [rdc]
  | cons pc c ih =>
    intro y hy
    rw [rdc_cons] at hy
    rcases Finset.mem_union.mp (Finsupp.support_add hy) with hy | hy
    · rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hy
      subst hy
      refine List.count_eq_zero.mpr fun hv => ?_
      have : WLetter.v ∈ fgt ℓ pc.2 := by unfold kd at hv; split_ifs at hv <;> exact hv
      obtain ⟨x, hx, hxv⟩ := List.mem_filterMap.mp this
      exact h x (by simp [cF_cons, hx]) hxv
    · exact ih (fun x hx => h x (by simp [cF_cons, hx])) y hy

private theorem vc_rdL {ℓ : ℕ → Option WLetter} {L : List (List Pc)}
    (h : ∀ x ∈ pos L, ℓ x ≠ some .v) : ∀ y ∈ (rdL ℓ L).support, y.vc = 0 := by
  induction L with
  | nil => simp [rdL]
  | cons c L ih =>
    intro y hy
    rw [rdL_cons] at hy
    rcases Finset.mem_union.mp (Finsupp.support_add hy) with hy | hy
    · exact vc_rdc (fun x hx => h x (by simp [pos_cons, hx])) y hy
    · exact ih (fun x hx => h x (by simp [pos_cons, hx])) y hy

private theorem Zh_rdL {ℓ : ℕ → Option WLetter} {L : List (List Pc)}
    (h : ∀ x ∈ pos L, ℓ x ≠ some .v) : Zh (rdL ℓ L) = (L.map fun c => Zh (rdc ℓ c)).prod := by
  induction L with
  | nil => simp [rdL, Zh, wickZ, T, cfgWickAux.eq_1]
  | cons c L ih =>
    rw [rdL_cons, Zh_add (fun y hy => ?_), ih fun x hx => h x (by simp [pos_cons, hx])]
    · rfl
    rcases Finset.mem_union.mp (Finsupp.support_add hy) with hy | hy
    · exact vc_rdc (fun x hx => h x (by simp [pos_cons, hx])) y hy
    · exact vc_rdL (fun x hx => h x (by simp [pos_cons, hx])) y hy

/-- Two configurations without `V` with the same successor permutation have the same value. -/
private theorem Zh_uniq {ℓ : ℕ → Option WLetter} {L₁ L₂ : List (List Pc)}
    (hd₀ : ∀ x ∈ d₀.support, x.vc = 0) (h₁ : Rep Ps D ℓ L₁) (h₂ : Rep Ps D ℓ L₂)
    (hσ : σL L₁ = σL L₂) (hV : Vs D ℓ = ∅) :
    Zh (d₀ + rdL ℓ L₁) = Zh (d₀ + rdL ℓ L₂) := by
  have hv : ∀ {L}, Rep Ps D ℓ L → ∀ x ∈ pos L, ℓ x ≠ some .v := fun hR x hx hxv => by
    have : x ∈ Vs D ℓ := Finset.mem_filter.mpr ⟨hR.2.1 ▸ List.mem_toFinset.mpr hx, hxv⟩
    rw [hV] at this; simp at this
  have hz : ∀ {L}, Rep Ps D ℓ L → Zh (d₀ + rdL ℓ L) = Zh d₀ * Zh (rdL ℓ L) := fun hR =>
    Zh_add fun y hy => by
      rcases Finset.mem_union.mp (Finsupp.support_add hy) with hy | hy
      exacts [hd₀ y hy, vc_rdL (hv hR) y hy]
  rw [hz h₁, hz h₂, Zh_rdL (hv h₁), Zh_rdL (hv h₂), uniq Ps L₁ L₂ h₁.1 h₂.1
    (List.perm_of_nodup_nodup_toFinset_eq h₁.1 h₂.1 (h₁.2.1.trans h₂.2.1.symm)) hσ h₁.2.2.2
    h₂.2.2.2 (hv h₁)]

/-! ### The letters `V` of a segment -/

/-- The decompositions `s = m₁ ++ b :: m₂` with a letter `V` at `b`. -/
private def spl (ℓ : ℕ → Option WLetter) : List ℕ → List (List ℕ × ℕ × List ℕ)
  | [] => []
  | x :: s => (if ℓ x = some .v then [([], x, s)] else []) ++
      (spl ℓ s).map fun t => (x :: t.1, t.2.1, t.2.2)

private theorem spl_mem {ℓ : ℕ → Option WLetter} : ∀ {s : List ℕ} {t : List ℕ × ℕ × List ℕ},
    t ∈ spl ℓ s → s = t.1 ++ t.2.1 :: t.2.2 ∧ ℓ t.2.1 = some .v
  | [], t, h => by simp [spl] at h
  | x :: s, t, h => by
    simp only [spl, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨t', ht', rfl⟩
    · split_ifs at h with hx
      · rw [List.mem_singleton] at h; subst h; exact ⟨rfl, hx⟩
      · simp at h
    · obtain ⟨h1, h2⟩ := spl_mem ht'; exact ⟨by simp [h1], h2⟩

private theorem spl_map (ℓ : ℕ → Option WLetter) : ∀ s : List ℕ,
    (spl ℓ s).map (·.2.1) = s.filter fun x => ℓ x = some .v
  | [] => rfl
  | x :: s => by
    by_cases hx : ℓ x = some .v <;> simp [spl, hx, ← spl_map ℓ s, Function.comp_def]

private theorem vsum_spl {M : Type*} [AddCommMonoid M] (ℓ : ℕ → Option WLetter) :
    ∀ (s : List ℕ) (G : List WLetter → List WLetter → M),
    ((vPos (fgt ℓ s)).map fun j => G ((fgt ℓ s).take j) ((fgt ℓ s).drop (j + 1))).sum =
      ((spl ℓ s).map fun t => G (fgt ℓ t.1) (fgt ℓ t.2.2)).sum
  | [], G => rfl
  | x :: s, G => by
    rcases hx : ℓ x with _ | l
    · have : ∀ u, fgt ℓ (x :: u) = fgt ℓ u := fun u => by simp [fgt, hx]
      rw [this, vsum_spl ℓ s]
      simp [spl, hx, this, Function.comp_def]
    · have : ∀ u, fgt ℓ (x :: u) = l :: fgt ℓ u := fun u => by simp [fgt, hx]
      rw [this, vPos_cons, List.map_append, List.sum_append, List.map_map]
      have ih := vsum_spl ℓ s (fun A B => G (l :: A) B)
      simp only [spl, hx, List.map_append, List.sum_append, List.map_map, Function.comp_def,
        this, List.take_succ_cons, List.drop_succ_cons] at ih ⊢
      rw [ih]
      congr 1
      by_cases hl : l = .v <;> simp [hl, fgt]

/-! ### One pairing step at a letter `V` of a configuration -/

private theorem pos_eq : ∀ L : List (List Pc), pos L = cF L.flatten
  | [] => rfl
  | c :: L => by rw [pos_cons, List.flatten_cons, cF_append, pos_eq L]

private theorem rdL_flat (ℓ : ℕ → Option WLetter) : ∀ L : List (List Pc), rdL ℓ L = rdc ℓ L.flatten
  | [] => rfl
  | c :: L => by rw [rdL_cons, List.flatten_cons, rdc_append, rdL_flat ℓ L]

private theorem rdc_perm (ℓ : ℕ → Option WLetter) {P Q : List Pc} (h : List.Perm P Q) :
    rdc ℓ P = rdc ℓ Q := (h.map _).sum_eq

private theorem single_le_rdc (ℓ : ℕ → Option WLetter) {P : List Pc} {pc : Pc} (h : pc ∈ P) :
    Finsupp.single (kd pc.1 (fgt ℓ pc.2)) 1 ≤ rdc ℓ P := by
  rw [rdc_perm ℓ (List.perm_cons_erase h), rdc_cons]; exact le_self_add

private theorem mem_rdc {ℓ : ℕ → Option WLetter} {P : List Pc} {x : CfgVar}
    (hx : x ∈ (rdc ℓ P).support) : ∃ pc ∈ P, kd pc.1 (fgt ℓ pc.2) = x := by
  induction P with
  | nil => simp [rdc] at hx
  | cons pc P ih =>
    rw [rdc_cons] at hx
    rcases Finset.mem_union.mp (Finsupp.support_add hx) with hx | hx
    · rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hx
      exact ⟨pc, List.mem_cons_self .., hx.symm⟩
    · obtain ⟨q, hq, e⟩ := ih hx; exact ⟨q, List.mem_cons_of_mem _ hq, e⟩

private theorem kd_word (o : Option ℕ) (u : List WLetter) : (kd o u).word = u := by
  unfold kd; split <;> rfl

private theorem kd_isMrk (o : Option ℕ) (u : List WLetter) : (kd o u).isMrk = o.isSome := by
  unfold kd; split <;> simp_all [CfgVar.isMrk]

private theorem vc_kd {o : Option ℕ} {ℓ : ℕ → Option WLetter} {s : List ℕ}
    (h : 0 < (kd o (fgt ℓ s)).vc) : ∃ y ∈ s, ℓ y = some .v := by
  have : 0 < (fgt ℓ s).count .v := by rw [← kd_word o (fgt ℓ s)]; exact h
  obtain ⟨y, hy, e⟩ := List.mem_filterMap.mp (List.count_pos_iff.mp this)
  exact ⟨y, hy, e⟩

/-- Any piece can be brought to the front of the first cycle. -/
private theorem front {ℓ : ℕ → Option WLetter} {L : List (List Pc)} (hR : Rep Ps D ℓ L)
    {c : List Pc} (hc : c ∈ L) {pc : Pc} (hpc : pc ∈ c) : ∃ c' L', Rep Ps D ℓ ((pc :: c') :: L') ∧
      σL ((pc :: c') :: L') = σL L ∧ List.Perm ((pc :: c') :: L').flatten L.flatten := by
  obtain ⟨c₁, c₂, rfl⟩ := List.append_of_mem hpc
  have hp := List.perm_cons_erase hc
  obtain ⟨h1, h2, -⟩ := rep_perm Ps D hp hR
  obtain ⟨h3, h4, -⟩ := rep_rot Ps D (c₁ := c₁) (c₂ := pc :: c₂) h1
  refine ⟨c₂ ++ c₁, _, h3, h4.trans h2, ?_⟩
  rw [List.flatten_cons]
  refine ((List.perm_append_comm (l₁ := pc :: c₂)).append_right _).trans ?_
  rw [← List.flatten_cons]; exact hp.flatten.symm

private theorem split_first {ℓ : ℕ → Option WLetter} : ∀ {s : List ℕ}, (∃ y ∈ s, ℓ y = some .v) →
    ∃ A a B, s = A ++ a :: B ∧ ℓ a = some .v ∧ ∀ y ∈ A, ℓ y ≠ some .v
  | [], h => by simp at h
  | x :: s, h => by
    by_cases hx : ℓ x = some .v
    · exact ⟨[], x, s, rfl, hx, by simp⟩
    · obtain ⟨A, a, B, rfl, ha, hA⟩ := split_first (by simpa [hx] using h)
      exact ⟨x :: A, a, B, rfl, ha, fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy; exacts [hx, hA y hy]⟩

private theorem split_last {ℓ : ℕ → Option WLetter} {s : List ℕ} (h : ∃ y ∈ s, ℓ y = some .v) :
    ∃ A a B, s = A ++ a :: B ∧ ℓ a = some .v ∧ ∀ y ∈ B, ℓ y ≠ some .v := by
  obtain ⟨A, a, B, hs, ha, hA⟩ := split_first (s := s.reverse) (by simpa using h)
  exact ⟨B.reverse, a, A.reverse, by rw [← List.reverse_reverse s, hs]; simp, ha,
    fun y hy => hA y (List.mem_reverse.mp hy)⟩

private theorem fgt_split {ℓ : ℕ → Option WLetter} {A B : List ℕ} {a : ℕ} (ha : ℓ a = some .v) :
    fgt ℓ (A ++ a :: B) = fgt ℓ A ++ WLetter.v :: fgt ℓ B := by
  simp [fgt, List.filterMap_append, ha]

private theorem fgt_nv {ℓ : ℕ → Option WLetter} {A : List ℕ} (hA : ∀ y ∈ A, ℓ y ≠ some .v) :
    WLetter.v ∉ fgt ℓ A := fun h => by
  obtain ⟨y, hy, e⟩ := List.mem_filterMap.mp h; exact hA y hy e

private theorem spl_nil {ℓ : ℕ → Option WLetter} {A : List ℕ} (hA : ∀ y ∈ A, ℓ y ≠ some .v) :
    spl ℓ A = [] := by
  have := spl_map ℓ A
  rw [List.filter_eq_nil_iff.mpr fun y hy => by simpa using hA y hy] at this
  exact List.map_eq_nil_iff.mp this

private theorem spl_ex {ℓ : ℕ → Option WLetter} {s : List ℕ} {b : ℕ} (hb : b ∈ s)
    (hv : ℓ b = some .v) : ∃ t ∈ spl ℓ s, t.2.1 = b := by
  have : b ∈ (spl ℓ s).map (·.2.1) := by rw [spl_map]; simpa [hb] using hv
  simpa using this

section front
variable {ℓ : ℕ → Option WLetter} {o : Option ℕ} {A B : List ℕ} {a : ℕ} {c' : List Pc}
  {L' : List (List Pc)}

/-- Pairing `a` with a later `V` of its own piece. -/
private theorem pr_aft (hR : Rep Ps D ℓ (((o, A ++ a :: B) :: c') :: L'))
    {t : List ℕ × ℕ × List ℕ} (ht : t ∈ spl ℓ B) :
    ∃ N, Rep Ps D (ers ℓ a t.2.1) N ∧
      σL N = σL (((o, A ++ a :: B) :: c') :: L') * Equiv.swap a t.2.1 ∧
      rdL (ers ℓ a t.2.1) N = rdc ℓ (c' ++ L'.flatten) + (Finsupp.single (.trc (fgt ℓ t.1)) 1 +
        Finsupp.single (kd o (fgt ℓ A ++ fgt ℓ t.2.2)) 1) := by
  obtain ⟨hB, -⟩ := spl_mem ht
  have e : A ++ a :: B = A ++ a :: t.1 ++ t.2.1 :: t.2.2 := by rw [hB]; simp
  rw [e] at hR ⊢
  obtain ⟨h1, h2, h3⟩ := st_self Ps D hR
  refine ⟨_, h1, h2, ?_⟩
  rw [h3, rdc_append, ← rdL_flat]; abel

/-- Pairing `a` with an earlier `V` of its own piece. -/
private theorem pr_bef (hR : Rep Ps D ℓ (((o, A ++ a :: B) :: c') :: L'))
    {t : List ℕ × ℕ × List ℕ} (ht : t ∈ spl ℓ A) :
    ∃ N, Rep Ps D (ers ℓ a t.2.1) N ∧
      σL N = σL (((o, A ++ a :: B) :: c') :: L') * Equiv.swap a t.2.1 ∧
      rdL (ers ℓ a t.2.1) N = rdc ℓ (c' ++ L'.flatten) + (Finsupp.single (.trc (fgt ℓ t.2.2)) 1 +
        Finsupp.single (kd o (fgt ℓ t.1 ++ fgt ℓ B)) 1) := by
  obtain ⟨hA, -⟩ := spl_mem ht
  rw [hA] at hR ⊢
  obtain ⟨h1, h2, h3⟩ := st_self Ps D hR
  refine ⟨_, by rw [ers_comm]; exact h1, by rw [h2, Equiv.swap_comm], ?_⟩
  rw [ers_comm, h3, rdc_append, ← rdL_flat]; abel

/-- Pairing `a` with a `V` of another piece. -/
private theorem pr_crs (hR : Rep Ps D ℓ (((o, A ++ a :: B) :: c') :: L')) (r : Bool) {pc : Pc}
    (hpc : pc ∈ c' ++ L'.flatten) {t : List ℕ × ℕ × List ℕ} (ht : t ∈ spl ℓ pc.2) :
    ∃ N, Rep Ps D (ers ℓ a t.2.1) N ∧
      σL N = σL (((o, A ++ a :: B) :: c') :: L') * Equiv.swap a t.2.1 ∧
      Finsupp.single (kd pc.1 (fgt ℓ pc.2)) 1 + rdL (ers ℓ a t.2.1) N = rdc ℓ (c' ++ L'.flatten) +
        cpx r o.isSome pc.1.isSome (fgt ℓ A) (fgt ℓ B) (fgt ℓ t.1) (fgt ℓ t.2.2) := by
  obtain ⟨hs, -⟩ := spl_mem ht
  obtain ⟨o', s'⟩ := pc
  simp only at hs ⊢
  subst hs
  rcases List.mem_append.mp hpc with hpc | hpc
  · obtain ⟨c₁, c₂, rfl⟩ := List.append_of_mem hpc
    have hok := hR.2.2.2 _ (List.mem_cons_self ..)
    obtain ⟨p, rfl⟩ : ∃ p, o = some p := by
      rcases o with _ | p
      · exact absurd (okc_none Ps (c₁ := []) hok).2.1 (by simp)
      · exact ⟨p, rfl⟩
    obtain ⟨⟨q, -, hq⟩, -⟩ := okc_some Ps (c₁ := []) hok (o', t.1 ++ t.2.1 :: t.2.2) (by simp)
    simp only at hq; subst hq
    obtain ⟨h1, h2, h3⟩ := st_mms Ps D hR
    refine ⟨_, h1, h2, ?_⟩
    rw [h3]
    simp only [rdc_append, rdc_cons, ← rdL_flat, cpx, kd, Option.isSome_some, ite_true]
    abel
  · obtain ⟨c'', hc'', hpc⟩ := List.mem_flatten.mp hpc
    obtain ⟨c₁, c₂, rfl⟩ := List.append_of_mem hpc
    have hp : List.Perm (((o, A ++ a :: B) :: c') :: L')
        (((o, A ++ a :: B) :: c') :: (c₁ ++ (o', t.1 ++ t.2.1 :: t.2.2) :: c₂) :: L'.erase _) :=
      (List.perm_cons_erase hc'').cons _
    obtain ⟨h0, hσ, -⟩ := rep_perm Ps D hp hR
    obtain ⟨N, h1, h2, h3⟩ := st_cross Ps D r h0
    refine ⟨N, h1, by rw [h2, hσ], ?_⟩
    have hL : rdL ℓ L' = rdL ℓ ((c₁ ++ (o', t.1 ++ t.2.1 :: t.2.2) :: c₂) ::
        L'.erase (c₁ ++ (o', t.1 ++ t.2.1 :: t.2.2) :: c₂)) := by
      rw [rdL_flat, rdL_flat]; exact rdc_perm ℓ (List.perm_cons_erase hc'').flatten
    rw [h3, rdc_append ℓ c', ← rdL_flat ℓ L', hL, rdL_cons]
    simp only [rdc_append, rdc_cons]
    abel

end front

private theorem mk_none {ℓ : ℕ → Option WLetter} {L : List (List Pc)} (hR : Rep Ps D ℓ L) :
    ∀ pc ∈ L.flatten, ∀ p ∈ pc.1, ℓ p = none := by
  intro pc hpc p hp
  obtain ⟨c, hc, hpc'⟩ := List.mem_flatten.mp hpc
  refine hR.2.2.1 p ?_ (((hR.2.2.2 c hc).2 pc hpc').2.1 p hp)
  rw [← hR.2.1, List.mem_toFinset, pos_eq]
  exact List.mem_flatMap.mpr ⟨pc, hpc, List.mem_append_left _ (Option.mem_toList.mpr hp)⟩

private theorem seg_of_V {ℓ : ℕ → Option WLetter} {L : List (List Pc)} (hR : Rep Ps D ℓ L)
    {y : ℕ} (hy : y ∈ Vs D ℓ) : ∃ pc ∈ L.flatten, y ∈ pc.2 := by
  obtain ⟨hyD, hyv⟩ := Finset.mem_filter.mp hy
  rw [← hR.2.1, List.mem_toFinset, pos_eq] at hyD
  obtain ⟨pc, hpc, hy⟩ := List.mem_flatMap.mp hyD
  refine ⟨pc, hpc, (List.mem_append.mp hy).resolve_left fun h => ?_⟩
  rw [mk_none Ps D hR pc hpc y (Option.mem_toList.mp h)] at hyv; cases hyv

private theorem filter_cF {ℓ : ℕ → Option WLetter} {P : List Pc}
    (h : ∀ pc ∈ P, ∀ p ∈ pc.1, ℓ p = none) : (cF P).filter (fun x => ℓ x = some .v) =
      P.flatMap fun pc => pc.2.filter fun x => ℓ x = some .v := by
  induction P with
  | nil => rfl
  | cons pc P ih =>
    rw [cF_cons, List.flatMap_cons, List.filter_append, List.filter_append,
      ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    rcases hp : pc.1 with _ | p
    · simp
    · simp [h pc (List.mem_cons_self ..) p hp]

private theorem sum_flatMap {α β : Type*} (P : List α) (g : α → List β) (f : β → Loc) :
    ((P.flatMap g).map f).sum = (P.map fun x => ((g x).map f).sum).sum := by
  induction P with
  | nil => rfl
  | cons x P ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem sum_spl (ℓ : ℕ → Option WLetter) (s : List ℕ) (f : ℕ → Loc) :
    ((spl ℓ s).map fun t => f t.2.1).sum = ((s.filter fun x => ℓ x = some .v).map f).sum := by
  rw [← spl_map, List.map_map]; rfl

private theorem mem_Vs {ℓ : ℕ → Option WLetter} {o : Option ℕ} {A B : List ℕ} {a : ℕ}
    {c' : List Pc} {L' : List (List Pc)} (hR : Rep Ps D ℓ (((o, A ++ a :: B) :: c') :: L'))
    (ha : ℓ a = some .v) : a ∈ Vs D ℓ :=
  Finset.mem_filter.mpr ⟨by rw [← hR.2.1, List.mem_toFinset, pos_eq]; simp [cF_cons], ha⟩

/-- The partners of `a` are the letters `V` before and after it in its piece and in the other
pieces. -/
private theorem sumV {ℓ : ℕ → Option WLetter} {o : Option ℕ} {A B : List ℕ} {a : ℕ}
    {c' : List Pc} {L' : List (List Pc)} (hR : Rep Ps D ℓ (((o, A ++ a :: B) :: c') :: L'))
    (ha : ℓ a = some .v) (f : ℕ → Loc) :
    ∑ b ∈ (Vs D ℓ).erase a, f b = ((spl ℓ A).map fun t => f t.2.1).sum +
      ((spl ℓ B).map fun t => f t.2.1).sum +
      ((c' ++ L'.flatten).map fun pc => ((spl ℓ pc.2).map fun t => f t.2.1).sum).sum := by
  have hV : Vs D ℓ = ((cF (((o, A ++ a :: B) :: c') :: L').flatten).filter
      fun x => ℓ x = some .v).toFinset := by
    ext x; simp [Vs, ← hR.2.1, pos_eq]
  have hnd := ((pos_eq _ ▸ hR.1 : (cF (((o, A ++ a :: B) :: c') :: L').flatten).Nodup)).filter
    (fun x => decide (ℓ x = some .v))
  rw [Finset.sum_erase_eq_sub (mem_Vs Ps D hR ha), hV, List.sum_toFinset _ hnd,
    filter_cF (mk_none Ps D hR), sum_flatMap]
  simp only [sum_spl, List.flatten_cons, List.cons_append, List.map_cons, List.sum_cons,
    List.filter_append, List.filter_cons, ha, decide_true, ite_true, List.map_append,
    List.sum_append]
  abel

/-- Configurations of `ℓ` with the same successor permutation have the same value. -/
private def Qu (ℓ : ℕ → Option WLetter) : Prop :=
  ∀ L₁ L₂, Rep Ps D ℓ L₁ → Rep Ps D ℓ L₂ → σL L₁ = σL L₂ → Zh (d₀ + rdL ℓ L₁) = Zh (d₀ + rdL ℓ L₂)

/-- The value of a configuration of `ℓ` is the sum over the partners of any of its letters `V`. -/
private def Rx (ℓ : ℕ → Option WLetter) : Prop :=
  ∀ L, Rep Ps D ℓ L → ∀ a ∈ Vs D ℓ, Zh (d₀ + rdL ℓ L) =
    ι (X .w) * ∑ b ∈ (Vs D ℓ).erase a, Val Ps D d₀ (ers ℓ a b) (σL L * Equiv.swap a b)

private theorem Val_eq {ℓ : ℕ → Option WLetter} (hQ : Qu Ps D d₀ ℓ) {N : List (List Pc)}
    (hN : Rep Ps D ℓ N) : Val Ps D d₀ ℓ (σL N) = Zh (d₀ + rdL ℓ N) := by
  have h : ∃ L, Rep Ps D ℓ L ∧ σL L = σL N := ⟨N, hN, rfl⟩
  unfold Val
  split_ifs
  exact hQ _ _ h.choose_spec.1 hN h.choose_spec.2

/-- The sum over the partners of a letter `V` at `a`, read off the configuration. -/
private theorem Exp {ℓ : ℕ → Option WLetter} {o : Option ℕ} {A B : List ℕ} {a : ℕ}
    {c' : List Pc} {L' : List (List Pc)} (hR : Rep Ps D ℓ (((o, A ++ a :: B) :: c') :: L'))
    (ha : ℓ a = some .v) (hQ : ∀ b, Qu Ps D d₀ (ers ℓ a b)) (r : Bool) :
    ∑ b ∈ (Vs D ℓ).erase a,
        Val Ps D d₀ (ers ℓ a b) (σL (((o, A ++ a :: B) :: c') :: L') * Equiv.swap a b) =
      ((spl ℓ A).map fun t => Zh (d₀ + rdc ℓ (c' ++ L'.flatten) +
        (Finsupp.single (.trc (fgt ℓ t.2.2)) 1 +
          Finsupp.single (kd o (fgt ℓ t.1 ++ fgt ℓ B)) 1))).sum +
      ((spl ℓ B).map fun t => Zh (d₀ + rdc ℓ (c' ++ L'.flatten) +
        (Finsupp.single (.trc (fgt ℓ t.1)) 1 +
          Finsupp.single (kd o (fgt ℓ A ++ fgt ℓ t.2.2)) 1))).sum +
      ((c' ++ L'.flatten).map fun pc => ((spl ℓ pc.2).map fun t =>
        Zh (d₀ + rdc ℓ (c' ++ L'.flatten) - Finsupp.single (kd pc.1 (fgt ℓ pc.2)) 1 +
          cpx r o.isSome pc.1.isSome (fgt ℓ A) (fgt ℓ B) (fgt ℓ t.1) (fgt ℓ t.2.2))).sum).sum := by
  rw [sumV Ps D hR ha]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    obtain ⟨N, h1, h2, h3⟩ := pr_bef Ps D hR ht
    rw [← h2, Val_eq Ps D d₀ (hQ _) h1, h3, add_assoc]
  · refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    obtain ⟨N, h1, h2, h3⟩ := pr_aft Ps D hR ht
    rw [← h2, Val_eq Ps D d₀ (hQ _) h1, h3, add_assoc]
  · refine congrArg List.sum (List.map_congr_left fun pc hpc =>
      congrArg List.sum (List.map_congr_left fun t ht => ?_))
    obtain ⟨N, h1, h2, h3⟩ := pr_crs Ps D hR r hpc ht
    rw [← h2, Val_eq Ps D d₀ (hQ _) h1]
    congr 1
    ext y
    have h4 := congrArg (· y) h3
    have h5 := Finsupp.le_def.mp (single_le_rdc ℓ hpc) y
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply] at h4 h5 ⊢
    omega

private theorem vPos_nil' {u : List WLetter} (h : u.count .v = 0) : vPos u = [] :=
  List.filter_eq_nil_iff.mpr fun j _ hj =>
    List.count_eq_zero.mp h (List.mem_of_getElem? (by simpa using hj))

private theorem fsum_rdc {ℓ : ℕ → Option WLetter} (hd₀ : ∀ x ∈ d₀.support, x.vc = 0)
    (P : List Pc) (g : CfgVar → Loc) (hg : ∀ x : CfgVar, x.vc = 0 → g x = 0) :
    (d₀ + rdc ℓ P).sum (fun ψ n => (n : Loc) * g ψ) =
      (P.map fun pc => g (kd pc.1 (fgt ℓ pc.2))).sum := by
  have h0 : ∀ ψ, (fun ψ (n : ℕ) => (n : Loc) * g ψ) ψ 0 = 0 := fun _ => by simp
  have h1 : ∀ ψ (m n : ℕ), (fun ψ (n : ℕ) => (n : Loc) * g ψ) ψ (m + n) =
      (fun ψ (n : ℕ) => (n : Loc) * g ψ) ψ m + (fun ψ (n : ℕ) => (n : Loc) * g ψ) ψ n :=
    fun _ _ _ => by push_cast; ring
  rw [Finsupp.sum_add_index' (f := d₀) (g := rdc ℓ P) h0 h1, Finsupp.sum,
    Finset.sum_eq_zero fun x hx => by simp [hg x (hd₀ x hx)], zero_add]
  induction P with
  | nil => simp [rdc]
  | cons pc P ih =>
    rw [rdc_cons, Finsupp.sum_add_index' (f := Finsupp.single _ 1) (g := rdc ℓ P) h0 h1, ih,
      Finsupp.sum_single_index (by simp)]
    simp

/-- The one-step expansion at `A V B` read as sums over the letters `V` of the configuration. -/
private theorem conv {ℓ : ℕ → Option WLetter} (hd₀ : ∀ x ∈ d₀.support, x.vc = 0) (P : List Pc)
    (s : List ℕ) (G : List WLetter → List WLetter → Loc)
    (H : CfgVar → List WLetter → List WLetter → Loc) :
    ((vPos (fgt ℓ s)).map fun j => G ((fgt ℓ s).take j) ((fgt ℓ s).drop (j + 1))).sum +
      (d₀ + rdc ℓ P).sum (fun ψ n => (n : Loc) *
        ((vPos ψ.word).map fun j => H ψ (ψ.word.take j) (ψ.word.drop (j + 1))).sum) =
    ((spl ℓ s).map fun t => G (fgt ℓ t.1) (fgt ℓ t.2.2)).sum +
      (P.map fun pc => ((spl ℓ pc.2).map fun t =>
        H (kd pc.1 (fgt ℓ pc.2)) (fgt ℓ t.1) (fgt ℓ t.2.2)).sum).sum := by
  rw [vsum_spl, fsum_rdc d₀ hd₀ P _ fun x hx => by rw [vPos_nil' hx]; rfl]
  congr 1
  exact congrArg List.sum (List.map_congr_left fun pc _ => by
    rw [kd_word]; exact vsum_spl ℓ pc.2 (H (kd pc.1 (fgt ℓ pc.2))))

private theorem idx_split {u w : List WLetter} (hu : WLetter.v ∉ u) :
    (u ++ WLetter.v :: w).idxOf .v = u.length := by
  rw [List.idxOf_append_of_notMem hu]; simp

private theorem word_drop {o : Option ℕ} {u w : List WLetter} (hu : WLetter.v ∉ u) :
    (kd o (u ++ WLetter.v :: w)).word.drop
      ((kd o (u ++ WLetter.v :: w)).word.idxOf .v + 1) = w := by
  rw [kd_word, idx_split hu]; simp

private theorem selfPair_kd {o : Option ℕ} {u w : List WLetter} (hu : WLetter.v ∉ u) (j : ℕ) :
    selfPair (kd o (u ++ WLetter.v :: w)) j =
      Finsupp.single (.trc (w.take j)) 1 + Finsupp.single (kd o (u ++ w.drop (j + 1))) 1 := by
  rw [selfPair, word_drop hu, kd_word, kd_isMrk, idx_split hu, List.take_left' rfl]; rfl

private theorem cross_kd {o : Option ℕ} {u w : List WLetter} (hu : WLetter.v ∉ u) (ψ : CfgVar)
    (j : ℕ) : (crossPair (kd o (u ++ WLetter.v :: w)) ψ j).2 =
      cpx false o.isSome ψ.isMrk u w (ψ.word.take j) (ψ.word.drop (j + 1)) := by
  rw [crossPair_eq, word_drop hu, kd_word, kd_isMrk, idx_split hu, List.take_left' rfl]

/-- The value of a configuration at its pivot letter `V`. -/
private theorem bridge (hd₀ : ∀ x ∈ d₀.support, x.vc = 0) {ℓ : ℕ → Option WLetter}
    {L : List (List Pc)} (hR : Rep Ps D ℓ L) (hne : (Vs D ℓ).Nonempty)
    (hQ : ∀ p ∈ Vs D ℓ, ∀ b, Qu Ps D d₀ (ers ℓ p b)) :
    ∃ p ∈ Vs D ℓ, Zh (d₀ + rdL ℓ L) =
      ι (X .w) * ∑ b ∈ (Vs D ℓ).erase p, Val Ps D d₀ (ers ℓ p b) (σL L * Equiv.swap p b) := by
  have h : ((d₀ + rdL ℓ L).support.filter fun x => 0 < x.vc).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨pc, hpc, hy2⟩ := seg_of_V Ps D hR hy
    refine ⟨kd pc.1 (fgt ℓ pc.2), Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · have := Finsupp.le_def.mp (single_le_rdc ℓ hpc) (kd pc.1 (fgt ℓ pc.2))
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, rdL_flat]
      simp only [Finsupp.single_eq_same] at this; omega
    · show 0 < (kd pc.1 (fgt ℓ pc.2)).word.count .v
      rw [kd_word]
      exact List.count_pos_iff.mpr (List.mem_filterMap.mpr ⟨y, hy2, (Finset.mem_filter.mp hy).2⟩)
  obtain ⟨hx, hxv⟩ := cfgPick_mem h
  set q := cfgPick (d₀ + rdL ℓ L) with hq
  have hx' : q ∈ (rdc ℓ L.flatten).support := by
    have h0 : d₀ q = 0 := Finsupp.notMem_support_iff.mp fun h0 => by
      have := hd₀ _ h0; omega
    rw [Finsupp.mem_support_iff] at hx ⊢
    rwa [Finsupp.add_apply, h0, zero_add, rdL_flat] at hx
  obtain ⟨pc, hpc, hpx⟩ := mem_rdc hx'
  obtain ⟨c, hc, hpc⟩ := List.mem_flatten.mp hpc
  obtain ⟨c', L', hF, hσ, hp⟩ := front Ps D hR hc hpc
  obtain ⟨o, s⟩ := pc
  have hv : 0 < (kd o (fgt ℓ s)).vc := by rw [hpx]; exact hxv
  obtain ⟨A, a, B, rfl, ha, hA⟩ := split_first (vc_kd hv)
  have hsub : d₀ + rdL ℓ L - Finsupp.single (kd o (fgt ℓ A ++ WLetter.v :: fgt ℓ B)) 1 =
      d₀ + rdc ℓ (c' ++ L'.flatten) := by
    rw [rdL_flat, ← rdc_perm ℓ hp, List.flatten_cons, List.cons_append, rdc_cons, fgt_split ha,
      add_left_comm, add_tsub_cancel_left]
  have haV := mem_Vs Ps D hF ha
  refine ⟨a, haV, ?_⟩
  rw [Zh_step h, ← hq, ← hpx, fgt_split ha]
  simp only [word_drop (fgt_nv hA), selfPair_kd (fgt_nv hA), cross_kd (fgt_nv hA), hsub]
  have e := conv d₀ (ℓ := ℓ) hd₀ (c' ++ L'.flatten) B
    (fun p q => Zh (d₀ + rdc ℓ (c' ++ L'.flatten) +
      (Finsupp.single (.trc p) 1 + Finsupp.single (kd o (fgt ℓ A ++ q)) 1)))
    (fun ψ p q => Zh (d₀ + rdc ℓ (c' ++ L'.flatten) - Finsupp.single ψ 1 +
      cpx false o.isSome ψ.isMrk (fgt ℓ A) (fgt ℓ B) p q))
  rw [e, ← hσ, Exp Ps D d₀ hF ha (hQ a haV) false, spl_nil hA]
  simp [kd_isMrk]

/-- Any two letters `V` of a configuration can be paired. -/
private theorem pair_ex {ℓ : ℕ → Option WLetter} {L : List (List Pc)} (hR : Rep Ps D ℓ L)
    {a b : ℕ} (ha : a ∈ Vs D ℓ) (hb : b ∈ (Vs D ℓ).erase a) :
    ∃ N, Rep Ps D (ers ℓ a b) N ∧ σL N = σL L * Equiv.swap a b := by
  obtain ⟨hba, hbV⟩ := Finset.mem_erase.mp hb
  have hbv : ℓ b = some .v := (Finset.mem_filter.mp hbV).2
  obtain ⟨pc, hpc, hapc⟩ := seg_of_V Ps D hR ha
  obtain ⟨c, hc, hpc⟩ := List.mem_flatten.mp hpc
  obtain ⟨c', L', hF, hσ, -⟩ := front Ps D hR hc hpc
  obtain ⟨o, s⟩ := pc
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hapc
  obtain ⟨pc', hpc', hbpc⟩ := seg_of_V Ps D hF hbV
  rw [← hσ]
  rw [List.flatten_cons, List.cons_append] at hpc'
  rcases List.mem_cons.mp hpc' with rfl | hpc'
  · simp only [List.mem_append, List.mem_cons] at hbpc
    rcases hbpc with hbA | rfl | hbB
    · obtain ⟨t, ht, rfl⟩ := spl_ex hbA hbv
      obtain ⟨N, h1, h2, -⟩ := pr_bef Ps D hF ht; exact ⟨N, h1, h2⟩
    · exact absurd rfl hba
    · obtain ⟨t, ht, rfl⟩ := spl_ex hbB hbv
      obtain ⟨N, h1, h2, -⟩ := pr_aft Ps D hF ht; exact ⟨N, h1, h2⟩
  · obtain ⟨t, ht, rfl⟩ := spl_ex hbpc hbv
    obtain ⟨N, h1, h2, -⟩ := pr_crs Ps D hF false hpc' ht; exact ⟨N, h1, h2⟩

/-- Every configuration has the value given by its successor permutation, and this value is the
sum over the partners of any letter `V`. -/
private theorem main (hd₀ : ∀ x ∈ d₀.support, x.vc = 0) (n : ℕ) :
    ∀ ℓ, (Vs D ℓ).card = n → Qu Ps D d₀ ℓ ∧ Rx Ps D d₀ ℓ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ℓ hn
  have IH : ∀ a ∈ Vs D ℓ, ∀ b, Qu Ps D d₀ (ers ℓ a b) ∧ Rx Ps D d₀ (ers ℓ a b) := fun a ha b =>
    ih _ (by
      rw [← hn, Vs_ers]; exact Finset.card_erase_le.trans_lt (Finset.card_erase_lt_of_mem ha))
      _ rfl
  have key : ∀ L, Rep Ps D ℓ L → ∀ x ∈ Vs D ℓ, ∀ y ∈ (Vs D ℓ).erase x,
      ∀ z ∈ ((Vs D ℓ).erase x).erase y,
      Val Ps D d₀ (ers ℓ x y) (σL L * Equiv.swap x y) = ι (X .w) *
        ∑ u ∈ (((Vs D ℓ).erase x).erase y).erase z,
          Val Ps D d₀ (ers (ers ℓ x y) z u) (σL L * Equiv.swap x y * Equiv.swap z u) := by
    intro L hL x hx y hy z hz
    obtain ⟨N, hN, hσ⟩ := pair_ex Ps D hL hx hy
    rw [← hσ, Val_eq Ps D d₀ (IH x hx y).1 hN, (IH x hx y).2 N hN z (by rwa [Vs_ers]), Vs_ers]
  have hRx : Rx Ps D d₀ ℓ := by
    intro L hL a ha
    obtain ⟨p, hp, hZ⟩ := bridge Ps D d₀ hd₀ hL ⟨a, ha⟩ fun p hp b => (IH p hp b).1
    rw [hZ]
    rcases eq_or_ne a p with rfl | hap
    · rfl
    have h1 : a ∈ (Vs D ℓ).erase p := Finset.mem_erase.mpr ⟨hap, ha⟩
    have h2 : p ∈ (Vs D ℓ).erase a := Finset.mem_erase.mpr ⟨hap.symm, hp⟩
    have e : Val Ps D d₀ (ers ℓ a p) (σL L * Equiv.swap a p) =
        Val Ps D d₀ (ers ℓ p a) (σL L * Equiv.swap p a) := by rw [ers_comm, Equiv.swap_comm]
    rw [← Finset.add_sum_erase _ _ h1, ← Finset.add_sum_erase _ _ h2, e,
      Finset.sum_congr rfl fun b hb => key L hL p hp b (Finset.mem_of_mem_erase hb) a
        (by simp only [Finset.mem_erase] at hb ⊢; exact ⟨fun h => hb.1 h.symm, hap, ha⟩),
      Finset.sum_congr rfl fun b hb => key L hL a ha b (Finset.mem_of_mem_erase hb) p
        (by simp only [Finset.mem_erase] at hb ⊢; exact ⟨fun h => hb.1 h.symm, hap.symm, hp⟩),
      ← Finset.mul_sum, ← Finset.mul_sum]
    congr 1; congr 1; congr 1
    refine (Finset.sum_comm' fun b b' => ?_).trans (Finset.sum_congr rfl fun b' hb' =>
      Finset.sum_congr rfl fun b hb => ?_)
    · simp only [Finset.mem_erase]; tauto
    · simp only [Finset.mem_erase] at hb hb'
      rw [ers_ers, mul_assoc, mul_assoc, ((Equiv.Perm.disjoint_swap_swap (by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil]
        tauto)).commute).eq]
  refine ⟨fun L₁ L₂ h₁ h₂ hσ => ?_, hRx⟩
  rcases (Vs D ℓ).eq_empty_or_nonempty with hV | ⟨a, ha⟩
  · exact Zh_uniq Ps D d₀ hd₀ h₁ h₂ hσ hV
  · rw [hRx L₁ h₁ a ha, hRx L₂ h₂ a ha, hσ]

/-! ### A configuration for every monomial -/

/-- The cycles of a list of factors: the factor `i` sits at the positions `Nat.pair i j`. -/
private def cfgL : ℕ → List CfgVar → List (List Pc)
  | _, [] => []
  | k, x :: xs => [(if x.isMrk then some (Nat.pair k 0) else none,
      (List.range x.word.length).map fun j => Nat.pair k (j + 1))] :: cfgL (k + 1) xs

/-- The letter `j` of the word `g i` at the position `Nat.pair i (j + 1)`. -/
private def labL (g : ℕ → List WLetter) (y : ℕ) : Option WLetter :=
  if (Nat.unpair y).2 = 0 then none else (g (Nat.unpair y).1)[(Nat.unpair y).2 - 1]?

private theorem fm_range {α : Type*} (u : List α) :
    (List.range u.length).filterMap (fun j => u[j]?) = u := by
  induction u using List.reverseRecOn with
  | nil => rfl
  | append_singleton u x ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.filterMap_append,
      List.filterMap_congr fun j hj => List.getElem?_append_left (List.mem_range.mp hj), ih]
    simp

private theorem cfgL_spec (g : ℕ → List WLetter) : ∀ (k : ℕ) (xs : List CfgVar),
    (∀ x ∈ xs, 0 < x.vc) → (∀ i (h : i < xs.length), g (k + i) = xs[i].word) →
    (∀ y ∈ pos (cfgL k xs), k ≤ (Nat.unpair y).1) ∧ (pos (cfgL k xs)).Nodup ∧
    (∀ c ∈ cfgL k xs, okc {y | (Nat.unpair y).2 = 0} c) ∧
    rdL (labL g) (cfgL k xs) = (xs.map fun x => Finsupp.single x 1).sum
  | k, [], _, _ => by simp [cfgL, pos, rdL]
  | k, x :: xs, hv, hg => by
    obtain ⟨h1, h2, h3, h4⟩ := cfgL_spec g (k + 1) xs
      (fun y hy => hv y (List.mem_cons_of_mem _ hy)) fun i h => by
        rw [show k + 1 + i = k + (i + 1) by omega, hg (i + 1) (by simp; omega)]; simp
    have hx := hv x (List.mem_cons_self ..)
    have hg0 : g k = x.word := hg 0 (Nat.succ_pos _)
    have hm : ∀ y ∈ cF [(if x.isMrk then some (Nat.pair k 0) else none,
        (List.range x.word.length).map fun j => Nat.pair k (j + 1))],
        y = Nat.pair k 0 ∨ ∃ j < x.word.length, y = Nat.pair k (j + 1) := by
      intro y hy
      simp only [cF, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
        List.mem_map, List.mem_range] at hy
      rcases hy with hy | ⟨j, hj, rfl⟩
      · split_ifs at hy <;> simp_all
      · exact Or.inr ⟨j, hj, rfl⟩
    have hk : ∀ y ∈ cF [(if x.isMrk then some (Nat.pair k 0) else none,
        (List.range x.word.length).map fun j => Nat.pair k (j + 1))], (Nat.unpair y).1 = k :=
      fun y hy => by rcases hm y hy with rfl | ⟨j, -, rfl⟩ <;> simp
    refine ⟨fun y hy => ?_, ?_, fun c hc => ?_, ?_⟩
    · rcases List.mem_append.mp hy with hy | hy
      · exact (hk y hy).ge
      · exact (Nat.le_succ k).trans (h1 y hy)
    · refine List.nodup_append.mpr ⟨?_, h2, fun y hy y' hy' e => ?_⟩
      · simp only [cF, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        refine List.nodup_append.mpr ⟨by split_ifs <;> simp,
          (List.nodup_range).map fun i j e => by simpa using e, fun y hy y' hy' e => ?_⟩
        subst e
        split_ifs at hy <;> simp at hy hy'
        obtain ⟨j, -, hj⟩ := hy'
        rw [hy, Nat.pair_eq_pair] at hj; omega
      · subst e; have := h1 y hy'; rw [hk y hy] at this; omega
    · rcases List.mem_cons.mp hc with rfl | hc
      · refine ⟨by simp, fun pc hpc => ?_⟩
        rw [List.mem_singleton] at hpc; subst hpc
        refine ⟨fun y hy => ?_, fun p hp => ?_, fun hn => ⟨rfl, ?_⟩⟩
        · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy; simp
        · split_ifs at hp
          · simp only [Option.mem_def, Option.some.injEq] at hp; subst hp; simp
          · simp at hp
        · simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
          intro h0; rw [List.length_eq_zero_iff] at h0
          simp [CfgVar.vc, h0] at hx
      · exact h3 c hc
    · show rdL (labL g) (_ :: cfgL (k + 1) xs) = _
      rw [rdL_cons, h4, List.map_cons, List.sum_cons]
      congr 1
      have hf : fgt (labL g) ((List.range x.word.length).map fun j => Nat.pair k (j + 1)) =
          x.word := by
        rw [fgt, List.filterMap_map]
        conv_rhs => rw [← fm_range x.word]
        exact List.filterMap_congr fun j _ => by simp [labL, hg0]
      simp only [rdc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hf]
      congr 1
      cases x <;> simp_all [kd, CfgVar.isMrk, CfgVar.vc, CfgVar.word]

/-! ### Adjunction -/

private theorem WLetter.adj_adj (l : WLetter) : l.adj.adj = l := by cases l <;> rfl

private theorem adj_adj (x : CfgVar) : x.adj.adj = x := by
  cases x <;> simp [CfgVar.adj, List.map_reverse, Function.comp_def, WLetter.adj_adj]

private theorem adj_inj : Function.Injective CfgVar.adj := fun x y h => by
  rw [← adj_adj x, h, adj_adj]

/-- The adjoint monomial. -/
private def dA (d : CfgVar →₀ ℕ) : CfgVar →₀ ℕ := d.mapDomain CfgVar.adj

private theorem dA_apply (d : CfgVar →₀ ℕ) (x : CfgVar) : dA d x = d x.adj := by
  conv_lhs => rw [← adj_adj x]
  exact Finsupp.mapDomain_apply_of_injective adj_inj d x.adj

private theorem dA_dA (d : CfgVar →₀ ℕ) : dA (dA d) = d := by
  ext x; rw [dA_apply, dA_apply, adj_adj]

private theorem dA_single (x : CfgVar) : dA (Finsupp.single x 1) = Finsupp.single x.adj 1 :=
  Finsupp.mapDomain_single

private theorem dA_sub (d e : CfgVar →₀ ℕ) : dA (d - e) = dA d - dA e := by
  ext x; simp [dA_apply]

private theorem dA_add (d e : CfgVar →₀ ℕ) : dA (d + e) = dA d + dA e := Finsupp.mapDomain_add

private theorem cnt_adj (u : List WLetter) (l : WLetter) :
    (u.reverse.map WLetter.adj).count l.adj = u.count l := by
  rw [List.count_map_of_injective _ _ (fun a b h => by rw [← WLetter.adj_adj a, h,
    WLetter.adj_adj]), List.count_reverse]

private theorem vc_adj (x : CfgVar) : x.adj.vc = x.vc := by
  cases x <;> first | rfl | exact cnt_adj _ .v

private theorem weight_dA (d : CfgVar →₀ ℕ) :
    Finsupp.weight CfgVar.vc (dA d) = Finsupp.weight CfgVar.vc d := by
  simp only [Finsupp.weight_apply, dA]
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => add_smul ..)]
  simp [vc_adj]

private theorem base_adj (x : CfgVar) : x.adj.base = conjPoly x.base := by
  have he : ∀ u : List WLetter, wordExp (u.reverse.map WLetter.adj) = -wordExp u := fun u => by
    simp only [wordExp]
    rw [show WLetter.c = WLetter.cInv.adj from rfl, show WLetter.cInv = WLetter.c.adj from rfl,
      cnt_adj, cnt_adj]
    simp [WLetter.adj]
  have hm : ∀ k, conjPoly (mVar k) = mVar (-k) := fun k => by
    by_cases hk : k = 0 <;> simp [mVar, hk, conjPoly, ObsVar.neg]
  have hf : ∀ k, conjPoly (fVar k) = fVar (-k) := fun k => by
    by_cases hk : k = 0 <;> simp [fVar, hk, conjPoly, ObsVar.neg]
  cases x with
  | trc u => simp only [CfgVar.adj, CfgVar.base]; rw [he, hm]
  | mrk u => simp only [CfgVar.adj, CfgVar.base]; rw [he, hf]
  | w => simp [CfgVar.adj, CfgVar.base, conjPoly, ObsVar.neg]
  | γ => simp [CfgVar.adj, CfgVar.base, conjPoly, ObsVar.neg]

/-- The one-step expansion of a monomial at the last `V` of the factor `φ`: the expansion of the
adjoint configuration at the first `V` of `φ*`, read back by adjunction. -/
private def mirExp (d : CfgVar →₀ ℕ) (φ : CfgVar) : ObsPoly :=
  ((vPos (φ.adj.word.drop (φ.adj.word.idxOf .v + 1))).map fun j =>
      wickZ (d - Finsupp.single φ 1 + dA (selfPair φ.adj j))).sum +
    ∑ ψ ∈ (d - Finsupp.single φ 1).support,
      ((vPos ψ.adj.word).map fun j =>
        (((d - Finsupp.single φ 1 : CfgVar →₀ ℕ) ψ : ℕ) : ℂ) •
          (X ObsVar.w ^ (crossPair φ.adj ψ.adj j).1 *
            wickZ (d - Finsupp.single φ 1 - Finsupp.single ψ 1 +
              dA (crossPair φ.adj ψ.adj j).2))).sum

private theorem rr (u : List WLetter) :
    (u.reverse.map WLetter.adj).reverse.map WLetter.adj = u := by
  simp [List.map_reverse, Function.comp_def, WLetter.adj_adj]

private theorem adj_word (x : CfgVar) : x.adj.word = x.word.reverse.map WLetter.adj := by
  cases x <;> rfl

private theorem adj_isMrk (x : CfgVar) : x.adj.isMrk = x.isMrk := by cases x <;> rfl

private theorem kd_adj (o : Option ℕ) (u : List WLetter) :
    (kd o u).adj = kd o (u.reverse.map WLetter.adj) := by
  unfold kd; split <;> rfl

private theorem adj_trc (v : List WLetter) :
    (CfgVar.trc v).adj = .trc (v.reverse.map WLetter.adj) := rfl

private theorem tw_adj (x : CfgVar) : tw x.adj = tw x := by cases x <;> rfl

private theorem T_dA (d : CfgVar →₀ ℕ) : T (dA d) = T d := by
  simp only [T, Finsupp.weight_apply, dA]
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => add_smul ..)]
  simp [tw_adj]

private theorem dA_cpx (m n : Bool) (A B C D : List WLetter) :
    dA (cpx false m n (B.reverse.map WLetter.adj) (A.reverse.map WLetter.adj)
      (D.reverse.map WLetter.adj) (C.reverse.map WLetter.adj)) = cpx true m n A B C D := by
  have h : WLetter.adj ∘ WLetter.adj = id := funext WLetter.adj_adj
  cases m <;> cases n <;>
    simp [cpx, dA_add, dA_single, CfgVar.adj, List.reverse_append, h]
  exact add_comm _ _

private theorem vPos_lt {u : List WLetter} {j : ℕ} (hj : j ∈ vPos u) : j < u.length := by
  simpa [vPos] using (List.mem_filter.mp hj).1

private theorem vsum_snoc {M : Type*} [AddCommMonoid M] (u : List WLetter) (l : WLetter)
    (G : List WLetter → List WLetter → M) :
    ((vPos (u ++ [l])).map fun j => G ((u ++ [l]).take j) ((u ++ [l]).drop (j + 1))).sum =
      ((vPos u).map fun j => G (u.take j) (u.drop (j + 1) ++ [l])).sum +
        if l = .v then G u [] else 0 := by
  have hv : vPos (u ++ [l]) = vPos u ++ if l = .v then [u.length] else [] := by
    simp only [vPos, List.length_append, List.length_singleton, List.range_succ,
      List.filter_append]
    congr 1
    · exact List.filter_congr fun j hj => by simp [List.getElem?_append_left (List.mem_range.mp hj)]
    · by_cases hl : l = .v <;> simp [hl]
  rw [hv, List.map_append, List.sum_append]
  congr 1
  · exact congrArg List.sum (List.map_congr_left fun j hj => by
      have := vPos_lt hj
      rw [List.take_append_of_le_length this.le, List.drop_append_of_le_length this])
  · by_cases hl : l = .v <;> simp [hl]

/-- The positions of `V` in an adjoint word, counted from the other end. -/
private theorem vsum_rev {M : Type*} [AddCommMonoid M] : ∀ (u : List WLetter)
    (G : List WLetter → List WLetter → M),
    ((vPos (u.reverse.map WLetter.adj)).map fun j => G ((u.reverse.map WLetter.adj).take j)
        ((u.reverse.map WLetter.adj).drop (j + 1))).sum =
      ((vPos u).map fun j => G ((u.drop (j + 1)).reverse.map WLetter.adj)
        ((u.take j).reverse.map WLetter.adj)).sum
  | [], _ => rfl
  | l :: u, G => by
    rw [List.reverse_cons, List.map_append, List.map_singleton, vsum_snoc,
      vsum_rev u fun p q => G p (q ++ [l.adj]), vPos_cons, List.map_append, List.sum_append,
      add_comm]
    congr 1
    · cases l <;> simp [WLetter.adj]
    · simp [Function.comp_def]

/-- The one-step expansion at the last `V` of `x = u V w`, normalised. -/
private theorem Zh_mir {d : CfgVar →₀ ℕ} {o : Option ℕ} {u w : List WLetter} (hw : WLetter.v ∉ w)
    (hx : kd o (u ++ WLetter.v :: w) ∈ d.support) :
    ι (mirExp d (kd o (u ++ WLetter.v :: w))) * tinv ^ T d = ι (X .w) *
      (((vPos u).map fun j => Zh (d - Finsupp.single (kd o (u ++ WLetter.v :: w)) 1 +
        (Finsupp.single (.trc (u.drop (j + 1))) 1 + Finsupp.single (kd o (u.take j ++ w)) 1))).sum +
      (d - Finsupp.single (kd o (u ++ WLetter.v :: w)) 1).sum fun ψ n => (n : Loc) *
        ((vPos ψ.word).map fun j => Zh (d - Finsupp.single (kd o (u ++ WLetter.v :: w)) 1 -
          Finsupp.single ψ 1 + cpx true o.isSome ψ.isMrk u w (ψ.word.take j)
            (ψ.word.drop (j + 1)))).sum) := by
  set x := kd o (u ++ WLetter.v :: w) with hxdef
  have hw' : WLetter.v ∉ w.reverse.map WLetter.adj := fun h => by
    obtain ⟨l, hl, e⟩ := List.mem_map.mp h
    exact hw (by cases l <;> simp_all [WLetter.adj])
  have hxa :
      x.adj = kd o (w.reverse.map WLetter.adj ++ WLetter.v :: u.reverse.map WLetter.adj) := by
    rw [hxdef, kd_adj]; simp [List.reverse_append, WLetter.adj]
  have hxv : 0 < x.adj.vc := by
    rw [hxa]; show 0 < (kd _ _).word.count _; rw [kd_word]; exact List.count_pos_iff.mpr (by simp)
  rw [mirExp]
  refine (Zh_gen hx _ (fun j => dA (selfPair x.adj j)) (fun ψ => vPos ψ.adj.word)
    (fun ψ j => ((crossPair x.adj ψ.adj j).1, dA (crossPair x.adj ψ.adj j).2))
    (fun j _ => by rw [T_dA, T_selfPair hxv, tw_adj])
    (fun ψ j hj => by
      have := T_crossPair hxv hj
      rw [tw_adj, tw_adj] at this
      simpa [T_dA] using this)).trans ?_
  dsimp only
  congr 1
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [hxa, word_drop hw']
    simp only [selfPair_kd hw']
    have e := vsum_rev u fun p q => Zh (d - Finsupp.single x 1 + dA (Finsupp.single (.trc p) 1 +
      Finsupp.single (kd o (w.reverse.map WLetter.adj ++ q)) 1))
    rw [e]
    refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    rw [dA_add, dA_single, dA_single, adj_trc, rr, kd_adj, List.reverse_append, List.map_append, rr,
      rr]
  · unfold Finsupp.sum
    refine Finset.sum_congr rfl fun ψ _ => congrArg (_ * ·) ?_
    rw [hxa]
    simp only [cross_kd hw', adj_word, adj_isMrk]
    have e := vsum_rev ψ.word fun p q => Zh (d - Finsupp.single x 1 - Finsupp.single ψ 1 +
      dA (cpx false o.isSome ψ.isMrk (w.reverse.map WLetter.adj) (u.reverse.map WLetter.adj) p q))
    rw [e]
    exact congrArg List.sum (List.map_congr_left fun j _ => by rw [dA_cpx])

private theorem sum_single_toList (m : Multiset CfgVar) :
    (m.toList.map fun x => Finsupp.single x 1).sum = Multiset.toFinsupp m := by
  conv_rhs => rw [← Multiset.coe_toList m]
  induction m.toList with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ih, ← Multiset.cons_coe, ← Multiset.singleton_add,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

/-- Pivot independence of the contraction calculus of Lemma 11.7 [lg:lem:ideal]: the expansion
of a monomial equals its one-step expansion at the last `V` of any factor containing `V`. -/
private theorem wickZ_mirExp {d : CfgVar →₀ ℕ} {φ : CfgVar} (hφ : φ ∈ d.support)
    (hv : 0 < φ.vc) : wickZ d = mirExp d φ := by
  set d₀ := d.filter fun x => x.vc = 0
  set xs := (d.filter fun x => ¬ x.vc = 0).toMultiset.toList
  have hxv : ∀ x ∈ xs, 0 < x.vc := fun x hx => by
    rw [Multiset.mem_toList, Finsupp.mem_toMultiset, Finsupp.support_filter,
      Finset.mem_filter] at hx
    exact Nat.pos_of_ne_zero hx.2
  have hd₀ : ∀ x ∈ d₀.support, x.vc = 0 := fun x hx => by
    rw [Finsupp.support_filter, Finset.mem_filter] at hx; exact hx.2
  obtain ⟨-, hnd, hok, hrd⟩ := cfgL_spec (fun i => (xs.getD i .w).word) 0 xs hxv
    fun i h => by simp only [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
      Option.getD_some]
  set L := cfgL 0 xs
  set ℓ := labL fun i => (xs.getD i .w).word
  have hR : Rep {y | (Nat.unpair y).2 = 0} (pos L).toFinset ℓ L :=
    ⟨hnd, rfl, fun y _ hy => by simp [ℓ, labL, show (Nat.unpair y).2 = 0 from hy], hok⟩
  have hd : d = d₀ + rdL ℓ L := by
    rw [hrd, sum_single_toList, Finsupp.toMultiset_toFinsupp, Finsupp.filter_add_filter_not]
  have hφL : φ ∈ (rdc ℓ L.flatten).support := by
    rw [← rdL_flat, hrd, sum_single_toList, Finsupp.toMultiset_toFinsupp, Finsupp.support_filter,
      Finset.mem_filter]
    exact ⟨hφ, by omega⟩
  obtain ⟨pc, hpc, hpx⟩ := mem_rdc hφL
  obtain ⟨c, hc, hpc⟩ := List.mem_flatten.mp hpc
  obtain ⟨c', L', hF, hσ, hp⟩ := front _ _ hR hc hpc
  obtain ⟨o, s⟩ := pc
  simp only at hpx
  subst hpx
  obtain ⟨A, a, B, rfl, ha, hB⟩ := split_last (vc_kd hv)
  have hsub : d - Finsupp.single (kd o (fgt ℓ A ++ WLetter.v :: fgt ℓ B)) 1 =
      d₀ + rdc ℓ (c' ++ L'.flatten) := by
    rw [hd, rdL_flat, ← rdc_perm ℓ hp, List.flatten_cons, List.cons_append, rdc_cons, fgt_split ha,
      add_left_comm, add_tsub_cancel_left]
  have hM := Zh_mir (d := d) (o := o) (u := fgt ℓ A) (fgt_nv hB) (by rwa [← fgt_split ha])
  simp only [hsub] at hM
  have e := conv d₀ (ℓ := ℓ) hd₀ (c' ++ L'.flatten) A
    (fun p q => Zh (d₀ + rdc ℓ (c' ++ L'.flatten) +
      (Finsupp.single (.trc q) 1 + Finsupp.single (kd o (p ++ fgt ℓ B)) 1)))
    (fun ψ p q => Zh (d₀ + rdc ℓ (c' ++ L'.flatten) - Finsupp.single ψ 1 +
      cpx true o.isSome ψ.isMrk (fgt ℓ A) (fgt ℓ B) p q))
  rw [e] at hM
  have hZ := (main _ _ d₀ hd₀ _ ℓ rfl).2 _ hF a (mem_Vs _ _ hF ha)
  rw [Exp _ _ d₀ hF ha (fun b => (main _ _ d₀ hd₀ _ _ rfl).1) true, spl_nil hB] at hZ
  have hLF : rdL ℓ (((o, A ++ a :: B) :: c') :: L') = rdL ℓ L := by
    rw [rdL_flat, rdL_flat]; exact rdc_perm ℓ hp
  rw [hLF, ← hd] at hZ
  have h1 : ι (wickZ d) * tinv ^ T d = ι (mirExp d (kd o (fgt ℓ (A ++ a :: B)))) * tinv ^ T d := by
    rw [← Zh, hZ, fgt_split ha, hM]
    simp [kd_isMrk]
  have h2 : ∀ z : Loc, z * tinv ^ T d * ι (X .w) ^ T d = z := fun z => by
    rw [mul_assoc, ← mul_pow, mul_comm tinv, w_mul_tinv, one_pow, mul_one]
  have h3 : ι (wickZ d) = ι (mirExp d (kd o (fgt ℓ (A ++ a :: B)))) := by
    rw [← h2 (ι (wickZ d)), h1, h2]
  exact ι_inj h3

private theorem wickZ_dA (n : ℕ) : ∀ d : CfgVar →₀ ℕ, Finsupp.weight CfgVar.vc d ≤ n →
    wickZ (dA d) = conjPoly (wickZ d) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d hd
  by_cases h : ((dA d).support.filter fun x => 0 < x.vc).Nonempty
  · obtain ⟨hq₀, hq₀v⟩ := cfgPick_mem h
    set q₀ := cfgPick (dA d) with hq₀def
    have hφ : q₀.adj ∈ d.support := Finsupp.mem_support_iff.mpr (by
      rw [← dA_apply]; exact Finsupp.mem_support_iff.mp hq₀)
    have hw := weight_sub_single hφ
    rw [vc_adj] at hw
    have key : ∀ e, Finsupp.weight CfgVar.vc e < n → conjPoly (wickZ e) = wickZ (dA e) :=
      fun e he => (ih _ he e le_rfl).symm
    have hdA : dA d - Finsupp.single q₀ 1 = dA (d - Finsupp.single q₀.adj 1) := by
      rw [dA_sub, dA_single, adj_adj]
    rw [wickZ_mirExp hφ (by rwa [vc_adj]), mirExp, adj_adj, wickZ_step h, ← hq₀def, hdA, map_add,
      map_list_sum, map_sum, List.map_map]
    refine congrArg₂ (· + ·) (congrArg List.sum (List.map_congr_left fun j hj => ?_)) ?_
    · have := weight_selfPair hq₀v hj
      rw [Function.comp_apply, key _ (by rw [map_add, weight_dA]; omega), dA_add, dA_dA]
    · rw [show (dA (d - Finsupp.single q₀.adj 1)).support =
          (d - Finsupp.single q₀.adj 1).support.image CfgVar.adj by
          simp only [dA]; exact Finsupp.mapDomain_support_of_injective adj_inj _,
        Finset.sum_image fun x _ y _ h => adj_inj h]
      refine Finset.sum_congr rfl fun ψ hψ => ?_
      rw [map_list_sum, List.map_map]
      refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
      have h1 := weight_crossPair hq₀v hj
      have h2 := weight_sub_single hψ
      rw [vc_adj] at h1
      rw [Function.comp_apply, dA_apply, adj_adj, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul,
        map_pow, key _ (by rw [map_add, weight_dA]; omega), dA_add, dA_dA]
      simp [conjPoly, ObsVar.neg, dA_sub, dA_single, adj_adj]
  · have hv : ∀ x ∈ d.support, x.vc = 0 := fun x hx => by
      have := vc_of_not_nonempty h x.adj (Finsupp.mem_support_iff.mpr (by
        rw [dA_apply, adj_adj]; exact Finsupp.mem_support_iff.mp hx))
      rwa [vc_adj] at this
    rw [wickZ_of_vc (vc_of_not_nonempty h), wickZ_of_vc hv, dA,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod, Finsupp.prod, map_prod]
    exact Finset.prod_congr rfl fun x _ => by rw [map_pow, base_adj]

/-- The expectation commutes with conjugation. -/
theorem cfgWick_cfgConj (c : CfgPoly) : cfgWick (cfgConj c) = conjPoly (cfgWick c) := by
  induction c using MvPolynomial.induction_on' with
  | monomial d a =>
    have h : cfgConj (monomial d a) = monomial (dA d) (starRingEnd ℂ a) := by
      rw [dA, ← rename_monomial]
      conv_rhs => rw [monomial_eq, map_mul, rename_C, Finsupp.prod, map_prod]
      simp [cfgConj, eval₂_monomial, Finsupp.prod]
    rw [h, cfgWick_monomial, cfgWick_monomial, wickZ_dA _ _ le_rfl, smul_eq_C_mul, smul_eq_C_mul,
      map_mul]
    simp [conjPoly]
  | add p q hp hq => rw [map_add, cfgWick_add, cfgWick_add, hp, hq, map_add]

end LSBA
