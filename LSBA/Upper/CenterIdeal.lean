import LSBA.Upper.CenterWickAlg

/-!
# Uniform polynomial expansions: the ideal property

Lemma 11.7 (i) [lg:lem:ideal]: `q_r` maps the ideal `𝒥 = (W⁻¹, f_k : k ≠ 0)` into itself; and the
positive-order coefficients of the mean increment have `W⁰` part in `(f_k : k ≠ 0)` (Section 11.3.4
[lg:sec:cocycle-correction]).
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Words and their spans -/

private theorem centerIdeal_wordOf_append (u u' : List WLetter) :
    wordOf (u ++ u') = wordOf u * wordOf u' := by
  simp [wordOf]

private theorem centerIdeal_eq_wordOf (u : List WLetter) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := WLetter) (wordOf u) =
      MonoidAlgebra.of ℂ (FreeMonoid WLetter) (FreeMonoid.ofList u) := by
  induction u with
  | nil => simp [wordOf]; rfl
  | cons l u ih =>
    simp only [wordOf, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]

private theorem centerIdeal_wordFun_wordOf (φ : List WLetter → CfgPoly) (u : List WLetter) :
    wordFun φ (wordOf u) = φ u := by
  simp only [wordFun, LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
    centerIdeal_eq_wordOf]
  simp [MonoidAlgebra.of_apply]

private theorem centerIdeal_mrkFun_wordOf (u : List WLetter) :
    mrkFun (wordOf u) = if u = [] then 1 else X (.mrk u) := by
  rw [mrkFun, centerIdeal_wordFun_wordOf]

/-- The span of the words all of whose letters satisfy `P`. -/
private def centerIdealSpan (P : WLetter → Prop) : Submodule ℂ WordAlg :=
  Submodule.span ℂ {a | ∃ u : List WLetter, (∀ l ∈ u, P l) ∧ wordOf u = a}

private theorem centerIdealSpan_word (P : WLetter → Prop) {u : List WLetter}
    (hu : ∀ l ∈ u, P l) : wordOf u ∈ centerIdealSpan P :=
  Submodule.subset_span ⟨u, hu, rfl⟩

private theorem centerIdealSpan_one (P : WLetter → Prop) : (1 : WordAlg) ∈ centerIdealSpan P :=
  centerIdealSpan_word P (u := []) (by simp)

private theorem centerIdealSpan_mul (P : WLetter → Prop) {x y : WordAlg}
    (hx : x ∈ centerIdealSpan P) (hy : y ∈ centerIdealSpan P) : x * y ∈ centerIdealSpan P := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨u', hu', rfl⟩ := hb
      rw [← centerIdeal_wordOf_append]
      exact centerIdealSpan_word P fun l hl => (List.mem_append.mp hl).elim (hu l) (hu' l)
    | zero => simp
    | add b b' _ _ hb hb' => rw [mul_add]; exact add_mem hb hb'
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hb
  | zero => simp
  | add a a' _ _ ha ha' => rw [add_mul]; exact add_mem ha ha'
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

/-- The subalgebra spanned by the words all of whose letters satisfy `P`. -/
private def centerIdealAlg (P : WLetter → Prop) : Subalgebra ℂ WordAlg :=
  (centerIdealSpan P).toSubalgebra (centerIdealSpan_one P) fun _ _ =>
    centerIdealSpan_mul P

private theorem centerIdealAlg_ι (P : WLetter → Prop) {l : WLetter} (hl : P l) :
    FreeAlgebra.ι ℂ l ∈ centerIdealAlg P := by
  have h := centerIdealSpan_word P (u := [l]) (by simpa using hl)
  exact Submodule.mem_toSubalgebra.mpr (by simpa [wordOf] using h)

/-- Every element of the algebra of words is in the span of the words. -/
private theorem centerIdealSpan_top (a : WordAlg) : a ∈ centerIdealSpan fun _ => True := by
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (centerIdealSpan_one _)
  | grade1 x => exact centerIdealAlg_ι (fun _ => True) trivial
  | mul a b ha hb => exact centerIdealSpan_mul _ ha hb
  | add a b ha hb => exact add_mem ha hb

/-- Power series in `t` whose coefficients are in `centerIdealAlg P`. -/
private def centerIdealSer (P : WLetter → Prop) : Subring (PowerSeries WordAlg) where
  carrier := {S | ∀ n, PowerSeries.coeff n S ∈ centerIdealAlg P}
  mul_mem' := by
    intro S T hS hT n
    rw [PowerSeries.coeff_mul]
    exact Subalgebra.sum_mem _ fun p _ => Subalgebra.mul_mem _ (hS _) (hT _)
  one_mem' := by
    intro n
    rw [PowerSeries.coeff_one]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  add_mem' := by
    intro S T hS hT n
    rw [map_add]
    exact Subalgebra.add_mem _ (hS n) (hT n)
  zero_mem' := by
    intro n
    rw [map_zero]
    exact Subalgebra.zero_mem _
  neg_mem' := by
    intro S hS n
    rw [map_neg]
    exact Subalgebra.neg_mem _ (hS n)

private theorem centerIdealSer_C (P : WLetter → Prop) {a : WordAlg}
    (ha : a ∈ centerIdealAlg P) : PowerSeries.C a ∈ centerIdealSer P := by
  intro n
  rw [PowerSeries.coeff_C]
  split_ifs
  · exact ha
  · exact Subalgebra.zero_mem _

private theorem centerIdealSer_X (P : WLetter → Prop) :
    (PowerSeries.X : PowerSeries WordAlg) ∈ centerIdealSer P := by
  intro n
  rw [PowerSeries.coeff_X]
  split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

/-! ### The `W⁰` part of the formal expectation -/

private theorem centerIdeal_cfgWick_eq_sum (c : CfgPoly) {s : Finset (CfgVar →₀ ℕ)}
    (hs : c.support ⊆ s) :
    cfgWick c = ∑ d ∈ s, c.coeff d • cfgWickAux (Finsupp.weight CfgVar.vc d) d :=
  Finset.sum_subset hs fun d _ hd => by rw [notMem_support_iff.mp hd, zero_smul]

private theorem centerIdeal_cfgWick_add (p q : CfgPoly) :
    cfgWick (p + q) = cfgWick p + cfgWick q := by
  rw [centerIdeal_cfgWick_eq_sum (p + q) support_add,
    centerIdeal_cfgWick_eq_sum p Finset.subset_union_left,
    centerIdeal_cfgWick_eq_sum q Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by simp [add_smul]

private theorem centerIdeal_cfgWick_smul (a : ℂ) (c : CfgPoly) :
    cfgWick (a • c) = a • cfgWick c := by
  rw [centerIdeal_cfgWick_eq_sum (a • c) (MvPolynomial.support_smul), cfgWick, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul]

private theorem centerIdeal_cfgWick_monomial (d : CfgVar →₀ ℕ) (a : ℂ) :
    cfgWick (monomial d a) = a • cfgWickAux (Finsupp.weight CfgVar.vc d) d := by
  rw [centerIdeal_cfgWick_eq_sum _ support_monomial_subset, Finset.sum_singleton, coeff_monomial,
    ite_eq_left rfl]

private theorem centerIdeal_weight_single_one (x : CfgVar) :
    Finsupp.weight CfgVar.vc (Finsupp.single x 1) = x.vc := by
  simp [Finsupp.weight_single]

private theorem centerIdeal_cfgWick_X (x : CfgVar) :
    cfgWick (X x) = cfgWickAux x.vc (Finsupp.single x 1) := by
  rw [X, centerIdeal_cfgWick_monomial, one_smul, centerIdeal_weight_single_one]

private theorem centerIdeal_cfgWick_one : cfgWick (1 : CfgPoly) = 1 := by
  rw [← C_1, C_apply, centerIdeal_cfgWick_monomial, one_smul, map_zero, cfgWickAux,
    Finsupp.prod_zero_index]

/-- The `W⁰` part of the formal expectation, an algebra map (`zeroW_cfgWick_mul`). -/
private def centerIdealPhi : CfgPoly →ₐ[ℂ] ObsPoly :=
  AlgHom.ofLinearMap
    { toFun := fun c => zeroW (cfgWick c)
      map_add' := fun p q => by rw [centerIdeal_cfgWick_add, map_add]
      map_smul' := fun a p => by rw [centerIdeal_cfgWick_smul, map_smul]; rfl }
    (by simp only [LinearMap.coe_mk, AddHom.coe_mk, centerIdeal_cfgWick_one, map_one])
    zeroW_cfgWick_mul

private theorem centerIdealPhi_apply (c : CfgPoly) : centerIdealPhi c = zeroW (cfgWick c) := rfl

private theorem centerIdealPhi_X_base {x : CfgVar} (hx : x.vc = 0) :
    centerIdealPhi (X x) = zeroW x.base := by
  rw [centerIdealPhi_apply, centerIdeal_cfgWick_X, hx, cfgWickAux, Finsupp.prod_single_index]
  · rw [pow_one]
  · exact pow_zero _

/-! ### One expansion step of a single factor -/

private theorem centerIdeal_count_split {u : List WLetter} {j : ℕ} (h : u[j]? = some .v) :
    u.count .v = (u.take j).count .v + 1 + (u.drop (j + 1)).count .v := by
  obtain ⟨hj, hu⟩ := List.getElem?_eq_some_iff.mp h
  conv_lhs => rw [← List.take_append_drop j u, List.drop_eq_getElem_cons hj, hu]
  simp [List.count_append]
  omega

private theorem centerIdeal_idxOf_v {u : List WLetter} (h : WLetter.v ∈ u) :
    u[u.idxOf .v]? = some .v := by
  have hl := List.idxOf_lt_length_iff.mpr h
  rw [List.getElem?_eq_getElem hl, List.getElem_idxOf hl]

private theorem centerIdeal_mem_vPos {u : List WLetter} {j : ℕ} (hj : j ∈ vPos u) :
    u[j]? = some .v := by
  simpa [vPos] using (List.mem_filter.mp hj).2

private theorem centerIdeal_vc_ite (φ : CfgVar) (u : List WLetter) :
    (if φ.isMrk then CfgVar.mrk u else CfgVar.trc u).vc = u.count .v := by
  split_ifs <;> rfl

private theorem centerIdeal_vc_trc (u : List WLetter) : (CfgVar.trc u).vc = u.count .v := rfl

private theorem centerIdeal_weight_eq_zero_of_vc {d : CfgVar →₀ ℕ}
    (hd : ∀ x ∈ d.support, x.vc = 0) : Finsupp.weight CfgVar.vc d = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_eq_zero fun x hx => by simp [hd x hx]

private theorem centerIdeal_weight_sub_single {d : CfgVar →₀ ℕ} {x : CfgVar}
    (hx : x ∈ d.support) :
    Finsupp.weight CfgVar.vc d =
      Finsupp.weight CfgVar.vc (d - Finsupp.single x 1) + x.vc := by
  conv_lhs => rw [← tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr
    (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hx)))]
  rw [map_add, centerIdeal_weight_single_one]

private theorem centerIdeal_weight_selfPair {φ : CfgVar} (hφ : 0 < φ.vc) {j : ℕ}
    (hj : j ∈ vPos (φ.word.drop (φ.word.idxOf .v + 1))) :
    Finsupp.weight CfgVar.vc (selfPair φ j) + 2 = φ.vc := by
  have hv : WLetter.v ∈ φ.word := List.count_pos_iff.mp hφ
  have h1 := centerIdeal_count_split (centerIdeal_idxOf_v hv)
  have h2 := centerIdeal_count_split (centerIdeal_mem_vPos hj)
  rw [selfPair, map_add, centerIdeal_weight_single_one, centerIdeal_weight_single_one,
    centerIdeal_vc_ite, centerIdeal_vc_trc,
    show φ.vc = φ.word.count .v from rfl, h1, h2, List.count_append]
  omega

private theorem centerIdeal_cfgPick_mem {d : CfgVar →₀ ℕ}
    (h : (d.support.filter fun x => 0 < x.vc).Nonempty) :
    cfgPick d ∈ d.support ∧ 0 < (cfgPick d).vc := by
  have := (Classical.choose_spec
    ((d.support.filter fun x => 0 < x.vc).exists_min_image CfgVar.key h)).1
  simp only [cfgPick, h, ↓reduceDIte]
  exact Finset.mem_filter.mp this

private theorem centerIdeal_vc_of_not_nonempty {d : CfgVar →₀ ℕ}
    (h : ¬ (d.support.filter fun x => 0 < x.vc).Nonempty) : ∀ x ∈ d.support, x.vc = 0 := by
  intro x hx
  by_contra hne
  exact h ⟨x, Finset.mem_filter.mpr ⟨hx, Nat.pos_of_ne_zero hne⟩⟩

private theorem centerIdeal_zeroW_X_w : zeroW (X ObsVar.w) = 0 := by
  simp [zeroW]

/-- The `W⁰` part of one expansion step: the pairs with another factor carry `W⁻¹`. -/
private theorem centerIdeal_zeroW_cfgWickAux_succ (n : ℕ) {d : CfgVar →₀ ℕ}
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
    have hk : (crossPair (cfgPick d) ψ j).1 ≠ 0 := by
      unfold crossPair
      cases (cfgPick d).isMrk <;> cases ψ.isMrk <;> simp
    simp only [Function.comp_apply]
    rw [map_smul, map_mul, map_pow, centerIdeal_zeroW_X_w, zero_pow hk, zero_mul, smul_zero]

/-- The `W⁰` part of the expansion does not depend on the fuel. -/
private theorem centerIdeal_zeroW_fuel (n : ℕ) : ∀ d : CfgVar →₀ ℕ,
    Finsupp.weight CfgVar.vc d ≤ n →
      zeroW (cfgWickAux n d) = zeroW (cfgWickAux (Finsupp.weight CfgVar.vc d) d) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d hd
  rcases n with _ | m
  · rw [Nat.le_zero.mp hd]
  · by_cases hne : (d.support.filter fun x => 0 < x.vc).Nonempty
    · obtain ⟨hφd, hφ⟩ := centerIdeal_cfgPick_mem hne
      have hw := centerIdeal_weight_sub_single hφd
      obtain ⟨k, hk⟩ : ∃ k, Finsupp.weight CfgVar.vc d = k + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
      rw [hk, centerIdeal_zeroW_cfgWickAux_succ m hne, centerIdeal_zeroW_cfgWickAux_succ k hne]
      refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
      have := centerIdeal_weight_selfPair hφ hj
      rw [ih m (by omega) _ (by rw [map_add]; omega), ih k (by omega) _ (by rw [map_add]; omega)]
    · rw [centerIdeal_weight_eq_zero_of_vc (centerIdeal_vc_of_not_nonempty hne), cfgWickAux.eq_2,
        ite_eq_right hne, cfgWickAux.eq_1]

/-! ### Splittings at a letter `V` -/

/-- `Σ F(B₁, B₂)` over the splittings `B = B₁ V B₂`. -/
private def centerIdealSplit :
    (List WLetter → List WLetter → ObsPoly) → List WLetter → ObsPoly
  | _, [] => 0
  | F, l :: B => (if l = .v then F [] B else 0) + centerIdealSplit (fun Y Z => F (l :: Y) Z) B

private theorem centerIdeal_vPos_cons (l : WLetter) (u : List WLetter) :
    vPos (l :: u) = (if l = .v then [0] else []) ++ (vPos u).map (· + 1) := by
  simp only [vPos, List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
  by_cases h : l = .v <;> simp [h, Function.comp_def]

private theorem centerIdeal_split_vPos (B : List WLetter) :
    ∀ F : List WLetter → List WLetter → ObsPoly,
      ((vPos B).map fun j => F (B.take j) (B.drop (j + 1))).sum = centerIdealSplit F B := by
  induction B with
  | nil => intro F; simp [vPos, centerIdealSplit]
  | cons l B ih =>
    intro F
    rw [centerIdeal_vPos_cons, List.map_append, List.sum_append, List.map_map, centerIdealSplit,
      ← ih]
    congr 1
    split_ifs <;> simp

private theorem centerIdeal_split_congr (B : List WLetter) :
    ∀ F G : List WLetter → List WLetter → ObsPoly,
      (∀ Y Z, Y ++ .v :: Z = B → F Y Z = G Y Z) → centerIdealSplit F B = centerIdealSplit G B := by
  induction B with
  | nil => intro F G _; rfl
  | cons l B ih =>
    intro F G h
    rw [centerIdealSplit, centerIdealSplit]
    congr 1
    · split_ifs with hl
      · exact h [] B (by rw [hl]; rfl)
      · rfl
    · exact ih _ _ fun Y Z hYZ => h (l :: Y) Z (by rw [← hYZ]; rfl)

private theorem centerIdeal_split_append (B₁ B₂ : List WLetter) :
    ∀ F : List WLetter → List WLetter → ObsPoly,
      centerIdealSplit F (B₁ ++ B₂) = centerIdealSplit (fun Y Z => F Y (Z ++ B₂)) B₁ +
        centerIdealSplit (fun Y Z => F (B₁ ++ Y) Z) B₂ := by
  induction B₁ with
  | nil => intro F; simp [centerIdealSplit]
  | cons l B₁ ih =>
    intro F
    rw [List.cons_append, centerIdealSplit, centerIdealSplit, ih, add_assoc]
    rfl

private theorem centerIdeal_split_cons_ne {l : WLetter} (hl : l ≠ .v) (B : List WLetter)
    (F : List WLetter → List WLetter → ObsPoly) :
    centerIdealSplit F (l :: B) = centerIdealSplit (fun Y Z => F (l :: Y) Z) B := by
  simp [centerIdealSplit, hl]

/-! ### Cancellation of `C C⁻¹` in a single factor -/

/-- A marked form (`true`) or a normalized trace (`false`). -/
private def centerIdealVar : Bool → List WLetter → CfgVar
  | true, u => .mrk u
  | false, u => .trc u

/-- `f_k` (`true`) or `m_k` (`false`). -/
private def centerIdealBase : Bool → ℤ → ObsPoly
  | true, k => fVar k
  | false, k => mVar k

private theorem centerIdeal_phi_base (b : Bool) {u : List WLetter} (hu : WLetter.v ∉ u) :
    centerIdealPhi (X (centerIdealVar b u)) = centerIdealBase b (wordExp u) := by
  have hvc : (centerIdealVar b u).vc = 0 := by
    cases b <;> exact List.count_eq_zero.mpr hu
  rw [centerIdealPhi_X_base hvc]
  cases b
  · change zeroW (mVar _) = mVar _
    unfold mVar
    split_ifs <;> simp [zeroW]
  · change zeroW (fVar _) = fVar _
    unfold fVar
    split_ifs <;> simp [zeroW]

private theorem centerIdeal_idxOf {A : List WLetter} (hA : WLetter.v ∉ A) (B : List WLetter) :
    (A ++ .v :: B).idxOf .v = A.length := by
  induction A with
  | nil => simp
  | cons l A ih =>
    have hl : l ≠ .v := fun h => hA (h ▸ List.mem_cons_self)
    rw [List.cons_append, List.idxOf_cons, ih (fun h => hA (List.mem_cons_of_mem _ h))]
    simp [hl]

/-- One expansion step of a single factor `A V B` (`V ∉ A`): the first `V` is paired with each
later `V`, `B = B₁ V B₂`, giving `W⁻¹Tr(B₁)` times the factor of `A B₂`. -/
private theorem centerIdeal_phi_rec (b : Bool) {A : List WLetter} (hA : WLetter.v ∉ A)
    (B : List WLetter) :
    centerIdealPhi (X (centerIdealVar b (A ++ .v :: B))) =
      centerIdealSplit (fun Y Z => centerIdealPhi (X (.trc Y)) *
        centerIdealPhi (X (centerIdealVar b (A ++ Z)))) B := by
  set x := centerIdealVar b (A ++ .v :: B) with hx
  have hword : x.word = A ++ .v :: B := by cases b <;> rfl
  have hidx : x.word.idxOf .v = A.length := by rw [hword]; exact centerIdeal_idxOf hA B
  have hvc : x.vc = B.count .v + 1 := by
    change x.word.count .v = _
    rw [hword, List.count_append, List.count_eq_zero.mpr hA, List.count_cons_self]
    omega
  have hne : ((Finsupp.single x 1).support.filter fun y => 0 < y.vc).Nonempty :=
    ⟨x, by simp [hvc]⟩
  have hpick : cfgPick (Finsupp.single x 1) = x := by
    have := (centerIdeal_cfgPick_mem hne).1
    exact Finset.mem_singleton.mp (Finsupp.support_single_subset this)
  have hd : (A ++ .v :: B).drop (A.length + 1) = B := by
    simp [List.drop_append]
  have hsp : ∀ j, selfPair x j = Finsupp.single (.trc (B.take j)) 1 +
      Finsupp.single (centerIdealVar b (A ++ B.drop (j + 1))) 1 := by
    intro j
    rw [selfPair, hidx, hword]
    simp only [List.take_left', hd, hx]
    cases b <;> rfl
  rw [centerIdealPhi_apply, centerIdeal_cfgWick_X, hvc, centerIdeal_zeroW_cfgWickAux_succ _ hne,
    hpick, tsub_self]
  simp only [zero_add]
  rw [← centerIdeal_split_vPos]
  have hvB : vPos (x.word.drop (x.word.idxOf .v + 1)) = vPos B := by rw [hidx, hword, hd]
  rw [hvB]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hw := centerIdeal_weight_selfPair (φ := x) (by omega) (hvB ▸ hj)
  have hm : monomial (Finsupp.single (CfgVar.trc (B.take j)) 1 +
      Finsupp.single (centerIdealVar b (A ++ B.drop (j + 1))) 1) (1 : ℂ) =
      X (.trc (B.take j)) * X (centerIdealVar b (A ++ B.drop (j + 1))) := by
    rw [X, X, monomial_mul_monomial, one_mul]
  rw [centerIdeal_zeroW_fuel _ _ (by omega), ← one_smul ℂ (cfgWickAux _ _),
    ← centerIdeal_cfgWick_monomial, ← centerIdealPhi_apply, hsp, hm, map_mul]

private theorem centerIdeal_first_v {u : List WLetter} (h : WLetter.v ∈ u) :
    ∃ A B, WLetter.v ∉ A ∧ u = A ++ .v :: B := by
  induction u with
  | nil => simp at h
  | cons l u ih =>
    by_cases hl : l = .v
    · exact ⟨[], u, by simp, by simp [hl]⟩
    · obtain ⟨A, B, hA, rfl⟩ := ih (by simpa [Ne.symm hl] using h)
      exact ⟨l :: A, B, by simp [hA, Ne.symm hl], rfl⟩

/-- `C C⁻¹` cancels in the `W⁰` part of a single trace or marked form. -/
private theorem centerIdeal_phi_cancel (n : ℕ) : ∀ (b : Bool) (u₁ u₂ : List WLetter),
    (u₁ ++ u₂).count .v ≤ n →
      centerIdealPhi (X (centerIdealVar b (u₁ ++ .c :: .cInv :: u₂))) =
        centerIdealPhi (X (centerIdealVar b (u₁ ++ u₂))) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro b u₁ u₂ hn
  by_cases h₁ : WLetter.v ∈ u₁
  · obtain ⟨A, B, hA, rfl⟩ := centerIdeal_first_v h₁
    rw [show A ++ .v :: B ++ .c :: .cInv :: u₂ = A ++ .v :: (B ++ .c :: .cInv :: u₂) by simp,
      show A ++ .v :: B ++ u₂ = A ++ .v :: (B ++ u₂) by simp, centerIdeal_phi_rec b hA,
      centerIdeal_phi_rec b hA, centerIdeal_split_append, centerIdeal_split_append,
      centerIdeal_split_cons_ne (l := .c) (by decide),
      centerIdeal_split_cons_ne (l := .cInv) (by decide)]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine centerIdeal_split_congr _ _ _ fun Y Z hYZ => ?_
      subst hYZ
      simp only [List.count_append, List.count_cons_self] at hn
      rw [show A ++ (Z ++ .c :: .cInv :: u₂) = A ++ Z ++ .c :: .cInv :: u₂ by simp,
        show A ++ (Z ++ u₂) = A ++ Z ++ u₂ by simp,
        ih ((A ++ Z ++ u₂).count .v) (by simp only [List.count_append]; omega) b (A ++ Z) u₂ le_rfl]
    · refine centerIdeal_split_congr _ _ _ fun Y Z hYZ => ?_
      subst hYZ
      simp only [List.count_append, List.count_cons_self] at hn
      have h := ih ((B ++ Y).count .v) (by simp only [List.count_append]; omega) false B Y le_rfl
      simp only [centerIdealVar] at h
      rw [h]
  · by_cases h₂ : WLetter.v ∈ u₂
    · obtain ⟨A, B, hA, rfl⟩ := centerIdeal_first_v h₂
      have hA' : WLetter.v ∉ u₁ ++ .c :: .cInv :: A := by simp [h₁, hA]
      have hA'' : WLetter.v ∉ u₁ ++ A := by simp [h₁, hA]
      rw [show u₁ ++ .c :: .cInv :: (A ++ .v :: B) = (u₁ ++ .c :: .cInv :: A) ++ .v :: B by simp,
        show u₁ ++ (A ++ .v :: B) = (u₁ ++ A) ++ .v :: B by simp, centerIdeal_phi_rec b hA',
        centerIdeal_phi_rec b hA'']
      refine centerIdeal_split_congr _ _ _ fun Y Z hYZ => ?_
      subst hYZ
      simp only [List.count_append, List.count_cons_self] at hn
      rw [show u₁ ++ .c :: .cInv :: A ++ Z = u₁ ++ .c :: .cInv :: (A ++ Z) by simp,
        show u₁ ++ A ++ Z = u₁ ++ (A ++ Z) by simp,
        ih ((u₁ ++ (A ++ Z)).count .v) (by simp only [List.count_append]; omega) b u₁ (A ++ Z)
          le_rfl]
    · rw [centerIdeal_phi_base b (by simp [h₁, h₂]), centerIdeal_phi_base b (by simp [h₁, h₂])]
      congr 1
      simp [wordExp, List.count_append]
      ring

/-! ### The `W⁰` part of marked forms of words -/

private theorem centerIdeal_psi_word (u : List WLetter) :
    centerIdealPhi (mrkFun (wordOf u)) = centerIdealPhi (X (centerIdealVar true u)) := by
  rw [centerIdeal_mrkFun_wordOf]
  split_ifs with h
  · subst h
    rw [map_one, centerIdeal_phi_base true (by simp)]
    simp [centerIdealBase, wordExp, fVar]
  · rfl

/-- `C C⁻¹ = I` under the `W⁰` part of marked forms. -/
private theorem centerIdeal_psi_cancel (y z : WordAlg) :
    centerIdealPhi (mrkFun (y * (wC * wCi) * z)) = centerIdealPhi (mrkFun (y * z)) := by
  have key : ∀ u₁ u₂ : List WLetter,
      centerIdealPhi (mrkFun (wordOf u₁ * (wC * wCi) * wordOf u₂)) =
        centerIdealPhi (mrkFun (wordOf u₁ * wordOf u₂)) := by
    intro u₁ u₂
    rw [show wordOf u₁ * (wC * wCi) * wordOf u₂ = wordOf (u₁ ++ .c :: .cInv :: u₂) by
        simp [wordOf, wC, wCi, mul_assoc],
      ← centerIdeal_wordOf_append, centerIdeal_psi_word, centerIdeal_psi_word]
    exact centerIdeal_phi_cancel _ true u₁ u₂ le_rfl
  have hy := centerIdealSpan_top y
  induction hy using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u₁, -, rfl⟩ := ha
    have hz := centerIdealSpan_top z
    induction hz using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨u₂, -, rfl⟩ := hb
      exact key u₁ u₂
    | zero => simp
    | add b b' _ _ hb hb' => rw [mul_add, mul_add, map_add, map_add, hb, hb', map_add, map_add]
    | smul c b _ hb => rw [mul_smul_comm, mul_smul_comm, map_smul, map_smul, hb, map_smul,
        map_smul]
  | zero => simp
  | add a a' _ _ ha ha' => rw [add_mul, add_mul, add_mul, map_add, map_add, ha, ha', map_add,
      map_add]
  | smul c a _ ha => rw [smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, map_smul, map_smul, ha,
      map_smul, map_smul]

private theorem centerIdeal_smul_mem {a : ℂ} {p : ObsPoly} (hp : p ∈ fIdeal) : a • p ∈ fIdeal := by
  rw [smul_eq_C_mul]
  exact Ideal.mul_mem_left _ _ hp

/-- Marked forms of words in `C`, `V` ending in `C` have `W⁰` part in `(f_k : k ≠ 0)`. -/
private theorem centerIdeal_psi_mul_c {y : WordAlg} (hy : y ∈ centerIdealAlg (· ≠ .cInv)) :
    centerIdealPhi (mrkFun (y * wC)) ∈ fIdeal := by
  have hy' : y ∈ centerIdealSpan (· ≠ .cInv) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    rw [show wordOf u * wC = wordOf (u ++ [.c]) by simp [wordOf, wC], centerIdeal_psi_word,
      centerIdealPhi_apply]
    refine zeroW_cfgWick_mem_fIdeal _ fun d hd => ⟨u ++ [.c], ?_, ?_, by simp⟩
    · rw [support_X, Finset.mem_singleton] at hd
      simp [hd, centerIdealVar]
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact hu _ h rfl
      · simp at h
  | zero => simp
  | add a a' _ _ ha ha' => rw [add_mul, map_add, map_add]; exact add_mem ha ha'
  | smul c a _ ha => rw [smul_mul_assoc, map_smul, map_smul]; exact centerIdeal_smul_mem ha

private theorem centerIdeal_zeroW_conjPoly (p : ObsPoly) :
    zeroW (conjPoly p) = conjPoly (zeroW p) := by
  have h : (zeroW : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom.comp conjPoly =
      conjPoly.comp (zeroW : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [conjPoly, zeroW]
    · intro v
      cases v <;> simp [conjPoly, zeroW, ObsVar.neg]
  exact RingHom.congr_fun h p

private theorem centerIdeal_conjPoly_mem {p : ObsPoly} (hp : p ∈ fIdeal) : conjPoly p ∈ fIdeal := by
  have hle : fIdeal ≤ fIdeal.comap conjPoly := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    change conjPoly (X (.f k)) ∈ fIdeal
    simp only [conjPoly, eval₂Hom_X', ObsVar.neg]
    exact Ideal.subset_span ⟨_, rfl⟩
  exact hle hp

private theorem centerIdeal_adj_adj (l : WLetter) : l.adj.adj = l := by cases l <;> rfl

/-- Marked forms of words in `C⁻¹`, `V` starting with `C⁻¹` have `W⁰` part in
`(f_k : k ≠ 0)` (by conjugation). -/
private theorem centerIdeal_psi_ci_mul {y : WordAlg} (hy : y ∈ centerIdealAlg (· ≠ .c)) :
    centerIdealPhi (mrkFun (wCi * y)) ∈ fIdeal := by
  have hy' : y ∈ centerIdealSpan (· ≠ .c) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    set u' := (u.reverse.map WLetter.adj) ++ [.c] with hu'
    have hconj : X (CfgVar.mrk (.cInv :: u)) = cfgConj (X (.mrk u')) := by
      rw [cfgConj, eval₂Hom_X', CfgVar.adj, hu']
      have hc : WLetter.adj .c = .cInv := rfl
      simp [List.map_reverse, Function.comp_def, centerIdeal_adj_adj, hc]
    rw [show wCi * wordOf u = wordOf (.cInv :: u) by simp [wordOf, wCi], centerIdeal_psi_word,
      show centerIdealVar true (.cInv :: u) = CfgVar.mrk (.cInv :: u) from rfl, hconj,
      centerIdealPhi_apply, cfgWick_cfgConj, centerIdeal_zeroW_conjPoly]
    refine centerIdeal_conjPoly_mem (zeroW_cfgWick_mem_fIdeal _ fun d hd => ⟨u', ?_, ?_, ?_⟩)
    · rw [support_X, Finset.mem_singleton] at hd
      simp [hd]
    · intro h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨l, hl, hl'⟩ := List.mem_map.mp h
        cases l
        · exact hu _ (List.mem_reverse.mp hl) rfl
        · simp [WLetter.adj] at hl'
        · simp [WLetter.adj] at hl'
      · simp at h
    · simp [hu']
  | zero => simp
  | add a a' _ _ ha ha' => rw [mul_add, map_add, map_add]; exact add_mem ha ha'
  | smul c a _ ha => rw [mul_smul_comm, map_smul, map_smul]; exact centerIdeal_smul_mem ha

/-! ### The one-step series modulo `C C⁻¹ = I` -/

/-- `t · iV` as a power series in `t`. -/
private def centerIdealA : PowerSeries WordAlg := PowerSeries.X * PowerSeries.C (Complex.I • wV)

/-- `F = I − itV(I + C)`. -/
private def centerIdealF : PowerSeries WordAlg := 1 - centerIdealA * (1 + PowerSeries.C wC)

/-- `F^♯ = I + it(I + C⁻¹)V`, the adjoint of `F` with `C* = C⁻¹`. -/
private def centerIdealFs : PowerSeries WordAlg := 1 + (1 + PowerSeries.C wCi) * centerIdealA

/-- `γ + δ_0 C = (I + C) − F`. -/
private def centerIdealD : PowerSeries WordAlg := 1 + PowerSeries.C wC - centerIdealF

/-- `(F⁻¹(γ + δ_0 C))^n F⁻¹ ((γ + δ_0 C)F⁻¹ · itV + I + itV)`. -/
private def centerIdealY (n : ℕ) : PowerSeries WordAlg :=
  (fInvSeries * centerIdealD) ^ n * fInvSeries *
    (centerIdealD * fInvSeries * centerIdealA + 1 + centerIdealA)

private theorem centerIdeal_geom (m : WordAlg) :
    PowerSeries.mk (fun n => m ^ n) * (1 - PowerSeries.X * PowerSeries.C m) = 1 ∧
      (1 - PowerSeries.X * PowerSeries.C m) * PowerSeries.mk (fun n => m ^ n) = 1 := by
  constructor
  · ext n
    rw [mul_sub, mul_one, ← mul_assoc, (PowerSeries.commute_X _).eq, mul_assoc, map_sub]
    rcases n with _ | n
    · simp
    · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mk,
        PowerSeries.coeff_mk, PowerSeries.coeff_one, pow_succ]
      simp
  · ext n
    rw [sub_mul, one_mul, mul_assoc, map_sub]
    rcases n with _ | n
    · simp
    · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
        PowerSeries.coeff_mk, PowerSeries.coeff_one, pow_succ']
      simp

private theorem centerIdeal_fInv_eq :
    fInvSeries = PowerSeries.mk fun n => (Complex.I • (wV * (1 + wC))) ^ n := by
  ext n
  rw [fInvSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk, smul_pow]

private theorem centerIdeal_fInvAdj_eq :
    fInvAdjSeries = PowerSeries.mk fun n => (-(Complex.I • ((1 + wCi) * wV))) ^ n := by
  ext n
  rw [fInvAdjSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk, ← neg_smul, smul_pow]

private theorem centerIdeal_F_eq :
    centerIdealF = 1 - PowerSeries.X * PowerSeries.C (Complex.I • (wV * (1 + wC))) := by
  rw [centerIdealF, centerIdealA, mul_assoc,
    show (1 + PowerSeries.C wC : PowerSeries WordAlg) = PowerSeries.C (1 + wC) by simp,
    ← map_mul, smul_mul_assoc]

private theorem centerIdeal_Fs_eq :
    centerIdealFs = 1 - PowerSeries.X * PowerSeries.C (-(Complex.I • ((1 + wCi) * wV))) := by
  rw [centerIdealFs, centerIdealA,
    show (1 + PowerSeries.C wCi : PowerSeries WordAlg) = PowerSeries.C (1 + wCi) by simp,
    ← mul_assoc, (PowerSeries.commute_X _).eq, mul_assoc, ← map_mul, mul_smul_comm, map_neg,
    mul_neg, sub_neg_eq_add]

private theorem centerIdeal_HF : fInvSeries * centerIdealF = 1 := by
  rw [centerIdeal_fInv_eq, centerIdeal_F_eq]
  exact (centerIdeal_geom _).1

private theorem centerIdeal_FH : centerIdealF * fInvSeries = 1 := by
  rw [centerIdeal_fInv_eq, centerIdeal_F_eq]
  exact (centerIdeal_geom _).2

private theorem centerIdeal_FsG : centerIdealFs * fInvAdjSeries = 1 := by
  rw [centerIdeal_fInvAdj_eq, centerIdeal_Fs_eq]
  exact (centerIdeal_geom _).2

private theorem centerIdeal_GFs : fInvAdjSeries * centerIdealFs = 1 := by
  rw [centerIdeal_fInvAdj_eq, centerIdeal_Fs_eq]
  exact (centerIdeal_geom _).1

/-- `K̃ = (I + C)F⁻¹ − I`. -/
private theorem centerIdeal_K_eq : kSeries = (1 + PowerSeries.C wC) * fInvSeries - 1 := by
  ext n
  rw [show (1 + PowerSeries.C wC : PowerSeries WordAlg) = PowerSeries.C (1 + wC) by simp,
    map_sub, PowerSeries.coeff_C_mul, kSeries, fInvSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases n with _ | n
  · simp
  · simp

/-- `F⁻¹K̃^{n+1}F^{−*} = Y_n C + Y_n (I − C C⁻¹) itV F^{−*}`: the formal analogue of the
`z^{n+1}` coefficient of (11.42) [lg:eq:poisson]. -/
private theorem centerIdeal_T_eq (n : ℕ) :
    fInvSeries * kSeries ^ (n + 1) * fInvAdjSeries =
      centerIdealY n * PowerSeries.C wC +
        centerIdealY n * PowerSeries.C (1 - wC * wCi) * (centerIdealA * fInvAdjSeries) := by
  have hHF := centerIdeal_HF
  have hFsG := centerIdeal_FsG
  have hK := centerIdeal_K_eq
  unfold centerIdealY centerIdealD
  unfold centerIdealFs at hFsG
  rw [map_sub, map_one, map_mul]
  generalize fInvSeries = H at hHF hK ⊢
  generalize fInvAdjSeries = G at hFsG ⊢
  generalize kSeries = K at hK ⊢
  generalize PowerSeries.C wCi = ci at hFsG ⊢
  have hF : centerIdealF = 1 - centerIdealA * (1 + PowerSeries.C wC) := rfl
  generalize centerIdealF = F at hHF hF ⊢
  generalize PowerSeries.C wC = c at hF hK ⊢
  generalize centerIdealA = a at hF hFsG ⊢
  subst hF hK
  have hHK : H * ((1 + c) * H - 1) = H * (1 + c - (1 - a * (1 + c))) * H := by
    calc H * ((1 + c) * H - 1) = H * (1 + c) * H - H * (1 - a * (1 + c)) * H := by
          rw [hHF]; noncomm_ring
      _ = _ := by noncomm_ring
  have hpow : ∀ m : ℕ, H * ((1 + c) * H - 1) ^ m =
      (H * (1 + c - (1 - a * (1 + c)))) ^ m * H := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hHK, pow_succ]; noncomm_ring
  have e1 : a * (a + c * (1 + a)) + (1 - a * (1 + c)) * (1 + a) = 1 := by noncomm_ring
  have e2 : (1 + a) * (a + c * (1 + a)) = (1 + c - (1 - a * (1 + c))) * (1 + a) := by
    noncomm_ring
  have hDH : (1 + c - (1 - a * (1 + c))) * H =
      ((1 + c - (1 - a * (1 + c))) * H * a + 1 + a) * (a + c * (1 + a)) := by
    calc (1 + c - (1 - a * (1 + c))) * H =
          (1 + c - (1 - a * (1 + c))) * H * (a * (a + c * (1 + a)) +
            (1 - a * (1 + c)) * (1 + a)) := by rw [e1, mul_one]
      _ = (1 + c - (1 - a * (1 + c))) * H * a * (a + c * (1 + a)) +
            (1 + c - (1 - a * (1 + c))) * (H * (1 - a * (1 + c))) * (1 + a) := by noncomm_ring
      _ = _ := by rw [hHF, mul_one, ← e2]; noncomm_ring
  have hG : (a + c * (1 + a)) * G = c + (1 - c * ci) * (a * G) := by
    have e3 : a + c * (1 + a) = c * (1 + (1 + ci) * a) + (1 - c * ci) * a := by noncomm_ring
    rw [e3, add_mul, mul_assoc, hFsG, mul_one, mul_assoc]
  rw [hpow, pow_succ]
  calc (H * (1 + c - (1 - a * (1 + c)))) ^ n * (H * (1 + c - (1 - a * (1 + c)))) * H * G =
        (H * (1 + c - (1 - a * (1 + c)))) ^ n * H * ((1 + c - (1 - a * (1 + c))) * H) * G := by
        noncomm_ring
    _ = (H * (1 + c - (1 - a * (1 + c)))) ^ n * H *
          ((1 + c - (1 - a * (1 + c))) * H * a + 1 + a) * ((a + c * (1 + a)) * G) := by
        conv_lhs => rw [hDH]
        noncomm_ring
    _ = _ := by rw [hG]; noncomm_ring

/-- `F⁻¹F^{−*} = I + F⁻¹ itV C − C⁻¹ itV F^{−*} + F⁻¹ itV (I − C C⁻¹) itV F^{−*}`: the formal
analogue of the `z⁰` coefficient of (11.42) [lg:eq:poisson]. -/
private theorem centerIdeal_HG_eq :
    fInvSeries * fInvAdjSeries = 1 + fInvSeries * centerIdealA * PowerSeries.C wC -
      PowerSeries.C wCi * (centerIdealA * fInvAdjSeries) +
      fInvSeries * centerIdealA * PowerSeries.C (1 - wC * wCi) *
        (centerIdealA * fInvAdjSeries) := by
  have hHF := centerIdeal_HF
  have hFH := centerIdeal_FH
  have hFsG := centerIdeal_FsG
  have hGFs := centerIdeal_GFs
  have hF : centerIdealF = 1 - centerIdealA * (1 + PowerSeries.C wC) := rfl
  have hFs : centerIdealFs = 1 + (1 + PowerSeries.C wCi) * centerIdealA := rfl
  rw [map_sub, map_one, map_mul]
  generalize fInvSeries = H at hHF hFH ⊢
  generalize fInvAdjSeries = G at hFsG hGFs ⊢
  generalize centerIdealF = F at hHF hFH hF ⊢
  generalize centerIdealFs = Fs at hFsG hGFs hFs ⊢
  generalize PowerSeries.C wCi = ci at hFs ⊢
  generalize PowerSeries.C wC = c at hF ⊢
  generalize centerIdealA = a at hF hFs ⊢
  set R := 1 + H * a * c - ci * (a * G) + H * a * (1 - c * ci) * (a * G) with hR
  have h1 : H * (F * R * Fs) * G = R := by
    calc H * (F * R * Fs) * G = (H * F) * R * (Fs * G) := by noncomm_ring
      _ = R := by rw [hHF, hFsG, one_mul, mul_one]
  have h2 : F * R * Fs = 1 := by
    calc F * R * Fs = F * Fs + (F * H) * a * c * Fs - F * ci * a * (G * Fs) +
          (F * H) * a * (1 - c * ci) * a * (G * Fs) := by rw [hR]; noncomm_ring
      _ = 1 := by rw [hFH, hGFs, hF, hFs]; noncomm_ring
  rw [← h1, h2, mul_one]

/-! ### Coefficients -/

private theorem centerIdeal_psi_junk (S T : PowerSeries WordAlg) (e : WordAlg)
    (he : ∀ y z, centerIdealPhi (mrkFun (y * e * z)) = 0) (i : ℕ) :
    centerIdealPhi (mrkFun (PowerSeries.coeff i (S * PowerSeries.C e * T))) = 0 := by
  rw [PowerSeries.coeff_mul, map_sum, map_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [PowerSeries.coeff_mul_C]
  exact he _ _

private theorem centerIdeal_psi_e (y z : WordAlg) :
    centerIdealPhi (mrkFun (y * (1 - wC * wCi) * z)) = 0 := by
  rw [mul_sub, mul_one, sub_mul, map_sub, map_sub, centerIdeal_psi_cancel, sub_self]

private theorem centerIdeal_wV_mem (P : WLetter → Prop) (hP : P .v) : wV ∈ centerIdealAlg P :=
  centerIdealAlg_ι P hP

private theorem centerIdeal_A_mem (P : WLetter → Prop) (hP : P .v) :
    centerIdealA ∈ centerIdealSer P :=
  Subring.mul_mem _ (centerIdealSer_X P)
    (centerIdealSer_C P (Subalgebra.smul_mem _ (centerIdeal_wV_mem P hP) _))

private theorem centerIdeal_c_mem : PowerSeries.C wC ∈ centerIdealSer (· ≠ .cInv) :=
  centerIdealSer_C _ (centerIdealAlg_ι _ (by decide))

private theorem centerIdeal_H_mem : fInvSeries ∈ centerIdealSer (· ≠ .cInv) := by
  intro n
  rw [fInvSeries, PowerSeries.coeff_mk]
  exact Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (Subalgebra.mul_mem _
    (centerIdeal_wV_mem _ (by decide)) (Subalgebra.add_mem _ (Subalgebra.one_mem _)
      (centerIdealAlg_ι _ (by decide)))) _) _

private theorem centerIdeal_G_mem : fInvAdjSeries ∈ centerIdealSer (· ≠ .c) := by
  intro n
  rw [fInvAdjSeries, PowerSeries.coeff_mk]
  exact Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (Subalgebra.mul_mem _
    (Subalgebra.add_mem _ (Subalgebra.one_mem _) (centerIdealAlg_ι _ (by decide)))
    (centerIdeal_wV_mem _ (by decide))) _) _

private theorem centerIdeal_Y_mem (n : ℕ) : centerIdealY n ∈ centerIdealSer (· ≠ .cInv) := by
  have hA := centerIdeal_A_mem (· ≠ .cInv) (by decide)
  have hD : centerIdealD ∈ centerIdealSer (· ≠ .cInv) :=
    Subring.sub_mem _ (Subring.add_mem _ (Subring.one_mem _) centerIdeal_c_mem)
      (Subring.sub_mem _ (Subring.one_mem _) (Subring.mul_mem _ hA
        (Subring.add_mem _ (Subring.one_mem _) centerIdeal_c_mem)))
  exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _
    (Subring.mul_mem _ centerIdeal_H_mem hD) _) centerIdeal_H_mem)
    (Subring.add_mem _ (Subring.add_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hD
      centerIdeal_H_mem) hA) (Subring.one_mem _)) hA)

private theorem centerIdeal_mrkFun_one : mrkFun (1 : WordAlg) = 1 := by
  simpa [wordOf] using centerIdeal_mrkFun_wordOf []

/-- The generators `f_k`, `k ≥ 1`: the `W⁰` part of `q_r(f_k)` lies in `(f_j : j ≠ 0)`. -/
private theorem centerIdeal_zeroW_wick_f_pos (r : ℕ) (k : NzInt) (hk : 0 < k.1) :
    zeroW (wickMap r (X (.f k))) ∈ fIdeal := by
  obtain ⟨n, hn⟩ : ∃ n, k.1.toNat = n + 1 := ⟨k.1.toNat - 1, by omega⟩
  have hstep : stepSeries (X (.f k)) =
      seriesMap mrkFun (fInvSeries * kSeries ^ (n + 1) * fInvAdjSeries) * yInvSeries := by
    simp [stepSeries, kPowSeries, hk.le, hn]
  rw [wickMap, ← centerIdealPhi_apply, hstep, PowerSeries.coeff_mul, map_sum]
  refine Ideal.sum_mem _ fun p _ => ?_
  rw [map_mul]
  refine Ideal.mul_mem_right _ _ ?_
  rw [seriesMap, PowerSeries.coeff_mk, centerIdeal_T_eq, map_add, map_add, map_add,
    centerIdeal_psi_junk _ _ _ centerIdeal_psi_e, add_zero, PowerSeries.coeff_mul_C]
  exact centerIdeal_psi_mul_c (centerIdeal_Y_mem n _)

private theorem centerIdeal_zeroW_wick_f (r : ℕ) (k : NzInt) :
    zeroW (wickMap r (X (.f k))) ∈ fIdeal := by
  rcases lt_or_gt_of_ne k.2 with hk | hk
  · have hX : X (ObsVar.f k) = conjPoly (X (.f ⟨-k.1, neg_ne_zero.mpr k.2⟩)) := by
      simp [conjPoly, ObsVar.neg]
    rw [hX, wickMap_conjPoly, centerIdeal_zeroW_conjPoly]
    exact centerIdeal_conjPoly_mem (centerIdeal_zeroW_wick_f_pos r _ (by simp; omega))
  · exact centerIdeal_zeroW_wick_f_pos r k hk

private theorem centerIdeal_zeroW_wick_w (r : ℕ) : zeroW (wickMap r (X .w)) = 0 := by
  rw [wickMap, ← centerIdealPhi_apply]
  have h : stepSeries (X ObsVar.w) = PowerSeries.C (X CfgVar.w) := by simp [stepSeries]
  rw [h, PowerSeries.coeff_C]
  split_ifs
  · rw [centerIdealPhi_X_base rfl]
    exact centerIdeal_zeroW_X_w
  · exact map_zero _

private theorem centerIdeal_wickMap_zero (r : ℕ) : wickMap r 0 = 0 := by
  simp [wickMap, cfgWick]

/-- `P − π₀P ∈ (W⁻¹)`. -/
private theorem centerIdeal_sub_zeroW_mem (P : ObsPoly) : P - zeroW P ∈ obsIdeal := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [zeroW]
  | add p q hp hq => rw [map_add, add_sub_add_comm]; exact add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul]
    by_cases hv : v = .w
    · subst hv
      rw [centerIdeal_zeroW_X_w, mul_zero, sub_zero]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_union_left _ rfl))
    · have : zeroW (X v) = X v := by simp [zeroW, hv]
      rw [this, ← sub_mul]
      exact Ideal.mul_mem_right _ _ hp

private theorem centerIdeal_mem_obsIdeal {P : ObsPoly} (hP : zeroW P ∈ fIdeal) :
    P ∈ obsIdeal := by
  have hle : fIdeal ≤ obsIdeal := Ideal.span_mono Set.subset_union_right
  rw [← sub_add_cancel P (zeroW P)]
  exact add_mem (centerIdeal_sub_zeroW_mem P) (hle hP)

/-- The coefficients of `Y − 1` have `W⁰` part in `(f_k : k ≠ 0)`. -/
private theorem centerIdeal_phi_Y (q : ℕ) :
    centerIdealPhi (PowerSeries.coeff q (ySeries - 1)) ∈ fIdeal := by
  rw [map_sub, ySeries, seriesMap, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases q with _ | q
  · simp [PowerSeries.coeff_mul, fInvSeries, fInvAdjSeries, centerIdeal_mrkFun_one]
  · have hq : q + 1 ≠ 0 := Nat.add_one_ne_zero q
    simp only [hq, ↓reduceIte, sub_zero]
    rw [centerIdeal_HG_eq, map_add, map_sub, map_add, map_add, map_sub, map_add, map_add,
      map_sub, map_add, centerIdeal_psi_junk _ _ _ centerIdeal_psi_e, add_zero,
      PowerSeries.coeff_one]
    simp only [hq, ↓reduceIte, map_zero, zero_add]
    rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul]
    exact sub_mem (centerIdeal_psi_mul_c (Subring.mul_mem _ centerIdeal_H_mem
      (centerIdeal_A_mem _ (by decide)) _))
      (centerIdeal_psi_ci_mul (Subring.mul_mem _ (centerIdeal_A_mem _ (by decide))
        centerIdeal_G_mem _))

/-- Lemma 11.7 (i) [lg:lem:ideal]: `p ∈ 𝒥 ⇒ q_r(p) ∈ 𝒥`. -/
theorem wickMap_mem_obsIdeal (r : ℕ) {p : ObsPoly} (hp : p ∈ obsIdeal) :
    wickMap r p ∈ obsIdeal := by
  have hall : ∀ r, zeroW (wickMap r p) ∈ fIdeal := by
    induction hp using Submodule.span_induction with
    | mem x hx =>
      intro r
      rcases hx with hx | ⟨k, rfl⟩
      · rw [Set.mem_singleton_iff.mp hx, centerIdeal_zeroW_wick_w]
        exact zero_mem _
      · exact centerIdeal_zeroW_wick_f r k
    | zero =>
      intro r
      rw [centerIdeal_wickMap_zero, map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      intro r
      have h := (wickMap_linear r 1 x y).1
      rw [one_smul, one_smul] at h
      rw [h, map_add]
      exact add_mem (hx r) (hy r)
    | smul a x _ hx =>
      intro r
      rw [smul_eq_mul, zeroW_wickMap_mul]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hx _)
  exact centerIdeal_mem_obsIdeal (hall r)

/-- The positive-order coefficients of `P_g c` have `W⁰` part in `(f_k : k ≠ 0)` (Section 11.3.4
[lg:sec:cocycle-correction]). -/
theorem zeroW_incWick_mem_fIdeal {r : ℕ} (hr : 1 ≤ r) : zeroW (incWick r) ∈ fIdeal := by
  rw [incWick, ← centerIdealPhi_apply, incSeries, PowerSeries.coeff_smul, map_smul, logSeries,
    PowerSeries.coeff_mk, map_sum]
  refine centerIdeal_smul_mem (Ideal.sum_mem _ fun j _ => ?_)
  rw [map_smul]
  refine centerIdeal_smul_mem ?_
  rcases j with _ | j
  · have h2r : 2 * r ≠ 0 := by omega
    rw [pow_zero, PowerSeries.coeff_one]
    simp only [h2r, ↓reduceIte, map_zero]
    exact zero_mem _
  · rw [pow_succ, PowerSeries.coeff_mul, map_sum]
    exact Ideal.sum_mem _ fun q _ => by
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (centerIdeal_phi_Y _)

end LSBA
