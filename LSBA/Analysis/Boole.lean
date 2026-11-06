import LSBA.Volume.LocalComparison

/-!
# The Boole identity and energy-integrated resolvent entries

Boole's identity [PSZ, (1.5)], used before (8.16) [uvg:eq:energyapriori] in the proof of
Proposition 8.4(ii) [up:prop:conversion]: for distinct real `λ_j` and positive `w_j`, the function
`F(E) = Σ_j w_j/(λ_j − E)` satisfies `|{E : |F(E)| > T}| = 2 Σ_j w_j / T`. Consequently
(8.16) [uvg:eq:energyapriori]: `∫_{J₀} ‖ι_x^* (H₀ − E)^{-1} ι_y‖^p dE ≤ C_p W² |J₀|^{1-p}` for every
Hermitian `H₀`, isometries `ι_x, ι_y : ℂ^W → ℂ^N` and `0 < p < 1`, with `C_p = 4 · 2^p/(1 − p)`,
independently of the dimension and the entries of `H₀`; and the same bound for the blocks of a
Hermitian matrix on `ℂ^L ⊗ ℂ^W`.
-/

open MeasureTheory Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

section BooleOne

open Filter Topology

variable {ι : Type*}

/-- The function `F(E) = Σ_j w_j/(λ_j − E)` of Boole's identity [PSZ, (1.5)]. -/
private def booleF [Fintype ι] (lam w : ι → ℝ) (E : ℝ) : ℝ := ∑ j, w j / (lam j - E)

/-- The component of `ℝ ∖ {λ_j}` immediately to the left of the pole `λ_k`. -/
private def booleI (lam : ι → ℝ) (k : ι) : Set ℝ :=
  {E | E < lam k ∧ ∀ i, lam i < lam k → lam i < E}

private lemma booleI_ne {lam : ι → ℝ} {k : ι} {E : ℝ} (hE : E ∈ booleI lam k) (i : ι) :
    lam i ≠ E := by
  intro h
  rcases lt_or_ge (lam i) (lam k) with hi | hi
  · exact absurd (hE.2 i hi) (by rw [h]; exact lt_irrefl _)
  · exact absurd (hE.1) (by rw [← h]; exact not_lt.mpr hi)

private lemma booleI_ordConnected {lam : ι → ℝ} {k : ι} {c d E : ℝ} (hc : c ∈ booleI lam k)
    (hd : d ∈ booleI lam k) (h1 : c ≤ E) (h2 : E ≤ d) : E ∈ booleI lam k :=
  ⟨lt_of_le_of_lt h2 hd.1, fun i hi => lt_of_lt_of_le (hc.2 i hi) h1⟩

private lemma booleF_lt [Fintype ι] {lam w : ι → ℝ} (hw : ∀ j, 0 < w j) {k : ι} {E E' : ℝ}
    (hE : E ∈ booleI lam k) (hE' : E' ∈ booleI lam k) (h : E < E') :
    booleF lam w E < booleF lam w E' := by
  unfold booleF
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨k, Finset.mem_univ _, ?_⟩
  · rcases lt_or_ge (lam i) (lam k) with hi | hi
    · have h1 : lam i < E := hE.2 i hi
      have e1 : w i / (lam i - E) = -(w i / (E - lam i)) := by
        rw [← neg_sub, div_neg]
      have e2 : w i / (lam i - E') = -(w i / (E' - lam i)) := by
        rw [← neg_sub, div_neg]
      rw [e1, e2, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (hw i).le (by linarith) (by linarith)
    · have h1 : E' < lam i := lt_of_lt_of_le hE'.1 hi
      exact div_le_div_of_nonneg_left (hw i).le (by linarith) (by linarith)
  · exact div_lt_div_of_pos_left (hw k) (by linarith [hE'.1]) (by linarith)

private lemma booleF_le [Fintype ι] {lam w : ι → ℝ} (hw : ∀ j, 0 < w j) {k : ι} {E E' : ℝ}
    (hE : E ∈ booleI lam k) (hE' : E' ∈ booleI lam k) (h : E ≤ E') :
    booleF lam w E ≤ booleF lam w E' := by
  rcases h.eq_or_lt with h | h
  · rw [h]
  · exact (booleF_lt hw hE hE' h).le


/-- On each pole-free interval `F` is continuous. -/
private lemma booleF_continuousOn [Fintype ι] {lam w : ι → ℝ} {S : Set ℝ}
    (hS : ∀ E ∈ S, ∀ i, lam i ≠ E) : ContinuousOn (booleF lam w) S := by
  unfold booleF
  refine continuousOn_finsetSum _ fun i _ => ?_
  refine continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun E hE => ?_
  exact sub_ne_zero.mpr (hS E hE i)

/-- Just to the left of the pole `λ_k`, `F` is large. -/
private lemma booleF_eventually_gt [Fintype ι] {lam w : ι → ℝ} (hlam : Function.Injective lam)
    (hw : ∀ j, 0 < w j) (k : ι) (T : ℝ) :
    ∀ᶠ E in 𝓝[<] (lam k), T < booleF lam w E := by
  have h1 : Tendsto (fun E : ℝ => w k * (lam k - E)⁻¹) (𝓝[<] (lam k)) atTop := by
    refine Tendsto.const_mul_atTop (hw k) ?_
    refine tendsto_inv_nhdsGT_zero.comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun E : ℝ => lam k - E) (𝓝 (lam k)) (𝓝 (lam k - lam k)) :=
        (tendsto_const_nhds.sub tendsto_id)
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with E hE
      exact sub_pos.mpr (show E < lam k from hE)
  have h2 : Tendsto (fun E : ℝ => ∑ i ∈ Finset.univ.erase k, w i / (lam i - E)) (𝓝[<] (lam k))
      (𝓝 (∑ i ∈ Finset.univ.erase k, w i / (lam i - lam k))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    refine tendsto_finsetSum _ fun i hi => ?_
    have hne : lam i - lam k ≠ 0 := sub_ne_zero.mpr fun h =>
      (Finset.ne_of_mem_erase hi) (hlam h)
    exact (tendsto_const_nhds.div (tendsto_const_nhds.sub tendsto_id) hne)
  have h3 := (h1.atTop_add h2).eventually_gt_atTop T
  filter_upwards [h3] with E hE
  unfold booleF
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  simpa [div_eq_mul_inv] using hE

/-- Just to the right of a pole `a = λ_i`, `F` is very negative. -/
private lemma booleF_eventually_lt [Fintype ι] {lam w : ι → ℝ} (hlam : Function.Injective lam)
    (hw : ∀ j, 0 < w j) (i₀ : ι) (T : ℝ) :
    ∀ᶠ E in 𝓝[>] (lam i₀), booleF lam w E < T := by
  have h1 : Tendsto (fun E : ℝ => w i₀ * (lam i₀ - E)⁻¹) (𝓝[>] (lam i₀)) atBot := by
    refine Tendsto.const_mul_atBot (hw i₀) ?_
    refine tendsto_inv_nhdsLT_zero.comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun E : ℝ => lam i₀ - E) (𝓝 (lam i₀)) (𝓝 (lam i₀ - lam i₀)) :=
        (tendsto_const_nhds.sub tendsto_id)
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with E hE
      exact sub_neg.mpr (show lam i₀ < E from hE)
  have h2 : Tendsto (fun E : ℝ => ∑ i ∈ Finset.univ.erase i₀, w i / (lam i - E)) (𝓝[>] (lam i₀))
      (𝓝 (∑ i ∈ Finset.univ.erase i₀, w i / (lam i - lam i₀))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    refine tendsto_finsetSum _ fun i hi => ?_
    have hne : lam i - lam i₀ ≠ 0 := sub_ne_zero.mpr fun h =>
      (Finset.ne_of_mem_erase hi) (hlam h)
    exact (tendsto_const_nhds.div (tendsto_const_nhds.sub tendsto_id) hne)
  have h3 := (h1.atBot_add h2).eventually_lt_atBot T
  filter_upwards [h3] with E hE
  unfold booleF
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  simpa [div_eq_mul_inv] using hE

/-- Far to the left, `F` is small. -/
private lemma booleF_eventually_lt_atBot [Fintype ι] (lam w : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    ∀ᶠ E in atBot, booleF lam w E < T := by
  have h : Tendsto (booleF lam w) atBot (𝓝 0) := by
    have : (0 : ℝ) = ∑ _i : ι, 0 := by simp
    unfold booleF
    rw [this]
    refine tendsto_finsetSum _ fun i _ => ?_
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_neg_atBot_atTop)
  exact h.eventually (gt_mem_nhds hT)

/-- `F = T` has a root in the component immediately to the left of each pole. -/
private lemma booleF_exists_root [Fintype ι] {lam w : ι → ℝ} (hlam : Function.Injective lam)
    (hw : ∀ j, 0 < w j) {T : ℝ} (hT : 0 < T) (k : ι) :
    ∃ r ∈ booleI lam k, booleF lam w r = T := by
  -- a point of the component where `F > T`
  obtain ⟨d, hdT, hdI⟩ : ∃ d, T < booleF lam w d ∧ d ∈ booleI lam k := by
    have h1 := booleF_eventually_gt hlam hw k T
    have h2 : ∀ᶠ E in 𝓝[<] (lam k), E ∈ booleI lam k := by
      have hmem : ∀ᶠ E in 𝓝 (lam k), ∀ i, lam i < lam k → lam i < E := by
        refine Filter.eventually_all.2 fun i => ?_
        by_cases hi : lam i < lam k
        · filter_upwards [lt_mem_nhds hi] with E hE _ using hE
        · exact Filter.Eventually.of_forall fun E h => absurd h hi
      filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with E h3 h4
      exact ⟨h4, h3⟩
    exact (h1.and h2).exists.imp fun E hE => ⟨hE.1, hE.2⟩
  -- a point of the component where `F < T`
  obtain ⟨c, hcT, hcI⟩ : ∃ c, booleF lam w c < T ∧ c ∈ booleI lam k := by
    by_cases hS : (Finset.univ.filter fun i => lam i < lam k).Nonempty
    · obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image _ lam hS
      have hi₀k : lam i₀ < lam k := (Finset.mem_filter.mp hi₀).2
      have h1 := booleF_eventually_lt hlam hw i₀ T
      have h2 : ∀ᶠ E in 𝓝[>] (lam i₀), E ∈ Set.Ioo (lam i₀) (lam k) := Ioo_mem_nhdsGT hi₀k
      refine (h1.and h2).exists.imp fun E hE => ⟨hE.1, hE.2.2, fun i hi => ?_⟩
      exact lt_of_le_of_lt (hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)) hE.2.1
    · have h1 := booleF_eventually_lt_atBot lam w hT
      have h2 : ∀ᶠ E in atBot, E < lam k := eventually_lt_atBot _
      refine (h1.and h2).exists.imp fun E hE => ⟨hE.1, hE.2, fun i hi => ?_⟩
      exact absurd ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩ hS
  have hcd : c ≤ d := by
    by_contra h
    exact absurd (booleF_le hw hdI hcI (not_le.mp h).le) (not_le.mpr (hcT.trans hdT))
  have hcont : ContinuousOn (booleF lam w) (Set.Icc c d) :=
    booleF_continuousOn fun E hE => booleI_ne (booleI_ordConnected hcI hdI hE.1 hE.2)
  obtain ⟨r, hr, hrT⟩ := intermediate_value_Icc hcd hcont ⟨hcT.le, hdT.le⟩
  exact ⟨r, booleI_ordConnected hcI hdI hr.1 hr.2, hrT⟩

open Polynomial in
/-- Vieta's formula for the `m` roots of `F = T`: comparing the two highest coefficients of
`∏(X − λ_j) + T⁻¹ Σ_j w_j ∏_{i ≠ j}(X − λ_i)` gives `Σ r_k = Σ λ_j − Σ w_j / T`. -/
private lemma booleF_vieta [Fintype ι] [Nonempty ι] {lam w r : ι → ℝ} {T : ℝ} (hT : 0 < T)
    (hr : Function.Injective r) (hroot : ∀ k, booleF lam w (r k) = T)
    (hnp : ∀ k i, lam i ≠ r k) :
    ∑ k, r k = ∑ j, lam j - (∑ j, w j) / T := by
  set m := Fintype.card ι with hm
  have hmpos : 0 < m := Fintype.card_pos
  set p : ℝ[X] := ∏ i, (X - C (lam i)) with hp
  set q : ℝ[X] := ∑ j, C (w j) * ∏ i ∈ Finset.univ.erase j, (X - C (lam i)) with hq
  set h : ℝ[X] := p + C T⁻¹ * q with hh
  set h' : ℝ[X] := ∏ k, (X - C (r k)) with hh'
  have hpm : p.Monic := monic_prod_X_sub_C _ _
  have hpd : p.natDegree = m := by
    rw [hp, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (lam i))]
    simp [hm]
  have hh'm : h'.Monic := monic_prod_X_sub_C _ _
  have hh'd : h'.natDegree = m := by
    rw [hh', natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (r i))]
    simp [hm]
  have hprodm : ∀ j, (∏ i ∈ Finset.univ.erase j, (X - C (lam i))).Monic := fun j =>
    monic_prod_X_sub_C _ _
  have hprodd : ∀ j, (∏ i ∈ Finset.univ.erase j, (X - C (lam i))).natDegree = m - 1 := by
    intro j
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (lam i))]
    simp [hm, Finset.card_erase_of_mem]
  have hqd : q.natDegree ≤ m - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    exact (natDegree_C_mul_le _ _).trans (hprodd j).le
  have hqd' : (C T⁻¹ * q).natDegree ≤ m - 1 := (natDegree_C_mul_le _ _).trans hqd
  have hlt : (C T⁻¹ * q).natDegree < p.natDegree := by omega
  have hhm : h.Monic := hpm.add_of_left (degree_lt_degree hlt)
  have hhd : h.natDegree = m := by
    rw [hh, natDegree_add_eq_left_of_natDegree_lt hlt, hpd]
  -- `h` vanishes at each root
  have hev : ∀ k, h.eval (r k) = 0 := by
    intro k
    set E := r k with hE
    have hne : ∀ i, E - lam i ≠ 0 := fun i => sub_ne_zero.mpr (hnp k i).symm
    have hqe : q.eval E = -(p.eval E * booleF lam w E) := by
      simp only [hq, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
      unfold booleF
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h1 := Finset.mul_prod_erase Finset.univ (fun i => E - lam i) (Finset.mem_univ j)
      have h2 : ∏ i ∈ Finset.univ.erase j, (E - lam i) =
          (∏ i, (E - lam i)) / (E - lam j) := by
        rw [eq_div_iff (hne j), mul_comm]; exact h1
      simp only [hp, eval_prod, eval_sub, eval_X, eval_C]
      rw [h2]
      have h3 : lam j - E = -(E - lam j) := by ring
      rw [h3, div_neg]
      field_simp [hne j]
    have hpe : p.eval E ≠ 0 := by
      simp only [hp, eval_prod, eval_sub, eval_X, eval_C]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => hne i
    have hFE : booleF lam w E = T := hroot k
    simp only [hh, eval_add, eval_mul, eval_C, hqe, hFE]
    field_simp
    ring
  have heq : h = h' := by
    refine eq_of_degree_sub_lt_of_eval_finset_eq (Finset.univ.image r) ?_ ?_
    · rw [Finset.card_image_of_injective _ hr, Finset.card_univ, ← hm]
      have hdeg : h.degree = h'.degree := by
        rw [degree_eq_natDegree hhm.ne_zero, degree_eq_natDegree hh'm.ne_zero, hhd, hh'd]
      have := degree_sub_lt_left hdeg hhm.ne_zero (by rw [hhm.leadingCoeff, hh'm.leadingCoeff])
      rwa [degree_eq_natDegree hhm.ne_zero, hhd] at this
    · intro x hx
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
      rw [hev k, hh', eval_prod]
      exact (Finset.prod_eq_zero (Finset.mem_univ k) (by simp)).symm
  have hc := congrArg (fun f : ℝ[X] => f.coeff (m - 1)) heq
  simp only [hh, hh', coeff_add, coeff_C_mul] at hc
  rw [hp] at hc
  have hc1 : (∏ i, (X - C (lam i))).coeff (m - 1) = -∑ i, lam i := by
    have := prod_X_sub_C_coeff_card_pred (Finset.univ : Finset ι) lam (by simpa [hm] using hmpos)
    simpa [hm] using this
  have hc2 : (∏ i, (X - C (r i))).coeff (m - 1) = -∑ i, r i := by
    have := prod_X_sub_C_coeff_card_pred (Finset.univ : Finset ι) r (by simpa [hm] using hmpos)
    simpa [hm] using this
  have hc3 : q.coeff (m - 1) = ∑ j, w j := by
    rw [hq, finsetSum_coeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_C_mul, ← hprodd j, (hprodm j).coeff_natDegree, mul_one]
  rw [hc1, hc2, hc3] at hc
  have : T⁻¹ * ∑ j, w j = (∑ j, w j) / T := by rw [div_eq_inv_mul]
  linarith

/-- The one-sided half of Boole's identity [PSZ, (1.5)]: `|{E : F(E) > T}| = Σ w_j / T`. -/
private lemma volume_lt_booleF [Fintype ι] {lam w : ι → ℝ} (hlam : Function.Injective lam)
    (hw : ∀ j, 0 < w j) {T : ℝ} (hT : 0 < T) :
    volume {E : ℝ | T < booleF lam w E} = ENNReal.ofReal ((∑ j, w j) / T) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [booleF, hT.not_gt]
  choose r hrI hrF using booleF_exists_root hlam hw hT
  have hrinj : Function.Injective r := by
    intro k k' h
    by_contra hne
    rcases lt_or_gt_of_ne (hlam.ne hne) with hl | hl
    · exact absurd (hrI k').2 (by
        intro H
        have := H k hl
        rw [← h] at this
        exact absurd (hrI k).1 (not_lt.mpr this.le))
    · exact absurd (hrI k).2 (by
        intro H
        have := H k' hl
        rw [h] at this
        exact absurd (hrI k').1 (not_lt.mpr this.le))
  -- the sets `(r_k, λ_k)` are pairwise disjoint
  have hIoo : ∀ k, Set.Ioo (r k) (lam k) ⊆ booleI lam k := fun k E hE =>
    ⟨hE.2, fun i hi => lt_trans ((hrI k).2 i hi) hE.1⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun k => Set.Ioo (r k) (lam k)) := by
    intro k k' hne
    rw [Function.onFun, Set.disjoint_left]
    intro E hE hE'
    rcases lt_or_gt_of_ne (hlam.ne hne) with hl | hl
    · have h1 := (hrI k').2 k hl
      linarith [hE.2, hE'.1]
    · have h1 := (hrI k).2 k' hl
      linarith [hE'.2, hE.1]
  -- `{F > T}` agrees with `⋃_k (r_k, λ_k)` away from the finitely many poles
  have hsub1 : (⋃ k, Set.Ioo (r k) (lam k)) ⊆ {E : ℝ | T < booleF lam w E} := by
    intro E hE
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hE
    have := booleF_lt hw (hrI k) (hIoo k hk) hk.1
    rw [hrF k] at this
    exact this
  have hsub2 : {E : ℝ | T < booleF lam w E} ⊆ (⋃ k, Set.Ioo (r k) (lam k)) ∪ Set.range lam := by
    intro E hE
    by_cases hpole : E ∈ Set.range lam
    · exact Or.inr hpole
    left
    have hEne : ∀ i, lam i ≠ E := fun i h => hpole ⟨i, h⟩
    have hS : (Finset.univ.filter fun i => E < lam i).Nonempty := by
      by_contra hS
      rw [Finset.not_nonempty_iff_eq_empty] at hS
      have hall : ∀ i, lam i < E := fun i => by
        by_contra hi
        have : i ∈ Finset.univ.filter fun i => E < lam i :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_ne (not_lt.mp hi) (hEne i).symm⟩
        rw [hS] at this
        simp at this
      have hneg : booleF lam w E ≤ 0 :=
        Finset.sum_nonpos fun i _ => div_nonpos_of_nonneg_of_nonpos (hw i).le
          (by linarith [hall i])
      exact absurd hE (not_lt.mpr (hneg.trans hT.le))
    obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image _ lam hS
    have hEk : E < lam k := (Finset.mem_filter.mp hk).2
    have hEI : E ∈ booleI lam k := by
      refine ⟨hEk, fun i hi => ?_⟩
      by_contra hle
      have hlt : E < lam i := lt_of_le_of_ne (not_lt.mp hle) (hEne i).symm
      have := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
      exact absurd hi (not_lt.mpr this)
    have hrE : r k < E := by
      by_contra hle
      have := booleF_le hw hEI (hrI k) (not_lt.mp hle)
      rw [hrF k] at this
      exact absurd hE (not_lt.mpr this)
    exact Set.mem_iUnion.mpr ⟨k, hrE, hEk⟩
  have hvol : volume (⋃ k, Set.Ioo (r k) (lam k)) = ENNReal.ofReal (∑ k, (lam k - r k)) := by
    rw [measure_iUnion hdisj (fun k => measurableSet_Ioo), tsum_fintype]
    simp_rw [Real.volume_Ioo]
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro k _
    exact sub_nonneg.mpr (hrI k).1.le
  have hV := booleF_vieta hT hrinj hrF (fun k i => booleI_ne (hrI k) i)
  have hsum : ∑ k, (lam k - r k) = (∑ j, w j) / T := by
    rw [Finset.sum_sub_distrib]; linarith
  apply le_antisymm
  · calc volume {E : ℝ | T < booleF lam w E}
        ≤ volume ((⋃ k, Set.Ioo (r k) (lam k)) ∪ Set.range lam) := measure_mono hsub2
      _ ≤ volume (⋃ k, Set.Ioo (r k) (lam k)) + volume (Set.range lam) := measure_union_le _ _
      _ = volume (⋃ k, Set.Ioo (r k) (lam k)) := by
          rw [(Set.finite_range lam).measure_zero, add_zero]
      _ = _ := by rw [hvol, hsum]
  · rw [← hsum, ← hvol]
    exact measure_mono hsub1

private lemma measurable_booleF [Fintype ι] (lam w : ι → ℝ) : Measurable (booleF lam w) := by
  unfold booleF
  exact Finset.measurable_sum _ fun j _ => measurable_const.div (measurable_const.sub measurable_id)

/-- Boole's identity [PSZ, (1.5)] for distinct poles and positive weights over a finite index type.
-/
private lemma volume_abs_booleF [Fintype ι] {lam w : ι → ℝ} (hlam : Function.Injective lam)
    (hw : ∀ j, 0 < w j) {T : ℝ} (hT : 0 < T) :
    volume {E : ℝ | T < |booleF lam w E|} = ENNReal.ofReal (2 * (∑ j, w j) / T) := by
  have hneg : ∀ E, booleF (fun j => -lam j) w (-E) = -booleF lam w E := by
    intro E
    unfold booleF
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show -lam j - -E = -(lam j - E) by ring, div_neg]
  have hset : {E : ℝ | T < |booleF lam w E|} =
      {E | T < booleF lam w E} ∪ Neg.neg ⁻¹' {E | T < booleF (fun j => -lam j) w E} := by
    ext E
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_preimage, hneg]
    exact lt_abs
  have hmeas : MeasurableSet (Neg.neg ⁻¹' {E : ℝ | T < booleF (fun j => -lam j) w E}) :=
    measurable_neg (measurableSet_lt measurable_const (measurable_booleF _ _))
  have hdisj : Disjoint {E : ℝ | T < booleF lam w E}
      (Neg.neg ⁻¹' {E : ℝ | T < booleF (fun j => -lam j) w E}) := by
    rw [Set.disjoint_left]
    intro E h1 h2
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hneg] at h1 h2
    linarith
  rw [hset, measure_union hdisj hmeas, Measure.measure_preimage_neg,
    volume_lt_booleF hlam hw hT, volume_lt_booleF (fun a b h => hlam (neg_injective h)) hw hT,
    ← ENNReal.ofReal_add (div_nonneg (Finset.sum_nonneg fun j _ => (hw j).le) hT.le)
      (div_nonneg (Finset.sum_nonneg fun j _ => (hw j).le) hT.le)]
  congr 1
  ring

/-- Boole's identity [PSZ, (1.5)] with arbitrary poles and nonnegative weights: the weights at
coincident poles add and zero weights drop out. -/
private lemma volume_abs_booleF_of_nonneg [Fintype ι] (lam s : ι → ℝ) (hs : ∀ j, 0 ≤ s j)
    {T : ℝ} (hT : 0 < T) :
    volume {E : ℝ | T < |booleF lam s E|} = ENNReal.ofReal (2 * (∑ j, s j) / T) := by
  set W : ℝ → ℝ := fun μ => ∑ k ∈ Finset.univ.filter (fun k => lam k = μ), s k with hW
  set S : Finset ℝ := (Finset.univ.image lam).filter fun μ => 0 < W μ with hS
  have hWnn : ∀ μ, 0 ≤ W μ := fun μ => Finset.sum_nonneg fun k _ => hs k
  have hmaps : ∀ k ∈ (Finset.univ : Finset ι), lam k ∈ Finset.univ.image lam :=
    fun k _ => Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have hsumS : ∑ μ ∈ S, W μ = ∑ k, s k := by
    rw [hS, Finset.sum_filter_of_ne (fun μ _ h => lt_of_le_of_ne (hWnn μ) (Ne.symm h))]
    exact Finset.sum_fiberwise_of_maps_to hmaps s
  have hFS : ∀ E, booleF lam s E = ∑ μ ∈ S, W μ / (μ - E) := by
    intro E
    rw [hS, Finset.sum_filter_of_ne (fun μ _ h => by
      refine lt_of_le_of_ne (hWnn μ) (Ne.symm fun h0 => h ?_)
      rw [h0, zero_div])]
    unfold booleF
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun k => s k / (lam k - E))]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hW]
    simp only
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [(Finset.mem_filter.mp hk).2]
  have hinj : Function.Injective (fun μ : S => (μ : ℝ)) := Subtype.val_injective
  have hpos : ∀ μ : S, 0 < W μ := fun μ => (Finset.mem_filter.mp μ.2).2
  have := volume_abs_booleF hinj (w := fun μ : S => W μ) hpos hT
  have hcoe : ∀ E, booleF (fun μ : S => (μ : ℝ)) (fun μ : S => W μ) E = booleF lam s E := by
    intro E
    rw [hFS E]
    unfold booleF
    exact Finset.sum_coe_sort S fun μ => W μ / (μ - E)
  simp only [hcoe] at this
  rw [this]
  congr 3
  rw [Finset.sum_coe_sort S W, hsumS]

end BooleOne

/-- The constant `C_p = 4 · 2^p/(1 − p)` of (8.16) [uvg:eq:energyapriori]. -/
def booleConst (p : ℝ) : ℝ := 4 * 2 ^ p / (1 - p)

/-- Real arithmetic of the layer-cake computation: with `t₀ = a/ℓ` the two pieces add up to
`a^p ℓ^(1-p)/(1-p)`. -/
private lemma boole_layer_alg {a ℓ p : ℝ} (ha : 0 < a) (hℓ : 0 < ℓ) (hp0 : 0 < p) (hp1 : p < 1) :
    p * (ℓ * ((a / ℓ) ^ p / p)) + p * (a * (a / ℓ) ^ (p - 1) / (1 - p)) =
      a ^ p * ℓ ^ (1 - p) / (1 - p) := by
  have hA : 0 < a ^ p := Real.rpow_pos_of_pos ha p
  have hL : 0 < ℓ ^ p := Real.rpow_pos_of_pos hℓ p
  rw [Real.div_rpow ha.le hℓ.le, Real.div_rpow ha.le hℓ.le, Real.rpow_sub_one ha.ne',
    Real.rpow_sub_one hℓ.ne', Real.rpow_sub hℓ 1 p, Real.rpow_one]
  have h1 : (1 - p) ≠ 0 := by linarith
  have h2 : p ≠ 0 := by
    exact hp0.ne'
  field_simp
  ring

/-- Layer cake with the distribution function truncated at the length of `J` and bounded by
`a / t`: `∫_J f^p ≤ a^p |J|^(1-p) / (1-p)`. -/
private lemma boole_lintegral_rpow_le {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ E, 0 ≤ f E)
    {J : Set ℝ} (hJf : volume J ≠ ⊤) {a : ℝ} (ha : 0 < a) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hdist : ∀ t, 0 < t → (volume.restrict J) {E | t < f E} ≤ ENNReal.ofReal (a / t)) :
    ∫⁻ E in J, ENNReal.ofReal (f E ^ p) ≤
      ENNReal.ofReal (a ^ p * (volume J).toReal ^ (1 - p) / (1 - p)) := by
  by_cases hJ0 : volume J = 0
  · simp [Measure.restrict_eq_zero.mpr hJ0]
  set ℓ := (volume J).toReal with hℓ
  have hℓpos : 0 < ℓ := ENNReal.toReal_pos hJ0 hJf
  have hvol : volume J = ENNReal.ofReal ℓ := (ENNReal.ofReal_toReal hJf).symm
  set t₀ := a / ℓ with ht₀
  have ht₀pos : 0 < t₀ := div_pos ha hℓpos
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul (volume.restrict J) (ae_of_all _ hf0)
    hf.aemeasurable hp0]
  -- the two ranges of `t`
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 t₀ ∪ Set.Ioi t₀ :=
    (Set.Ioc_union_Ioi_eq_Ioi ht₀pos.le).symm
  have h1 : ∫⁻ t in Set.Ioc 0 t₀, (volume.restrict J) {E | t < f E} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal (ℓ * (t₀ ^ p / p)) := by
    calc _ ≤ ∫⁻ t in Set.Ioc 0 t₀, ENNReal.ofReal ℓ * ENNReal.ofReal (t ^ (p - 1)) := by
          refine lintegral_mono fun t => ?_
          gcongr
          calc (volume.restrict J) {E | t < f E} ≤ (volume.restrict J) Set.univ :=
                measure_mono (Set.subset_univ _)
            _ = ENNReal.ofReal ℓ := by rw [Measure.restrict_apply_univ, hvol]
      _ = ENNReal.ofReal ℓ * ∫⁻ t in Set.Ioc 0 t₀, ENNReal.ofReal (t ^ (p - 1)) := by
          rw [lintegral_const_mul]
          exact (measurable_id.pow_const _).ennreal_ofReal
      _ = ENNReal.ofReal (ℓ * (t₀ ^ p / p)) := by
          rw [ENNReal.ofReal_mul hℓpos.le]
          congr 1
          have hint : IntervalIntegrable (fun t : ℝ => t ^ (p - 1)) volume 0 t₀ :=
            intervalIntegral.intervalIntegrable_rpow' (by linarith)
          rw [← ofReal_integral_eq_lintegral_ofReal
            ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht₀pos.le).mp hint)
            ((ae_restrict_iff' measurableSet_Ioc).mpr
              (ae_of_all _ fun t ht => Real.rpow_nonneg ht.1.le _)),
            ← intervalIntegral.integral_of_le ht₀pos.le,
            integral_rpow (Or.inl (by linarith))]
          rw [show p - 1 + 1 = p by ring, Real.zero_rpow hp0.ne', sub_zero]
  have h2 : ∫⁻ t in Set.Ioi t₀, (volume.restrict J) {E | t < f E} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal (a * t₀ ^ (p - 1) / (1 - p)) := by
    calc _ ≤ ∫⁻ t in Set.Ioi t₀, ENNReal.ofReal (a * t ^ (p - 2)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          have htpos : 0 < t := ht₀pos.trans ht
          calc _ ≤ ENNReal.ofReal (a / t) * ENNReal.ofReal (t ^ (p - 1)) := by
                gcongr; exact hdist t htpos
            _ = ENNReal.ofReal (a / t * t ^ (p - 1)) :=
                (ENNReal.ofReal_mul (div_pos ha htpos).le).symm
            _ = ENNReal.ofReal (a * t ^ (p - 2)) := by
                congr 1
                rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add_one htpos.ne']
                field_simp
      _ = ENNReal.ofReal (a * t₀ ^ (p - 1) / (1 - p)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal
            ((integrableOn_Ioi_rpow_of_lt (by linarith) ht₀pos).const_mul a)
            ((ae_restrict_iff' measurableSet_Ioi).mpr
              (ae_of_all _ fun t ht => mul_nonneg ha.le (Real.rpow_nonneg (ht₀pos.trans ht).le _))),
            integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ht₀pos]
          congr 1
          rw [show p - 2 + 1 = p - 1 by ring, mul_div_assoc,
            show (1 - p) = -(p - 1) by ring, div_neg, neg_div]
  calc _ ≤ ENNReal.ofReal p * ∫⁻ t in Set.Ioc 0 t₀ ∪ Set.Ioi t₀,
          (volume.restrict J) {E | t < f E} * ENNReal.ofReal (t ^ (p - 1)) := by
        rw [← hsplit]
    _ ≤ ENNReal.ofReal p * (ENNReal.ofReal (ℓ * (t₀ ^ p / p)) +
          ENNReal.ofReal (a * t₀ ^ (p - 1) / (1 - p))) := by
        gcongr
        exact (lintegral_union_le _ _ _).trans (add_le_add h1 h2)
    _ = ENNReal.ofReal (a ^ p * ℓ ^ (1 - p) / (1 - p)) := by
        rw [← ENNReal.ofReal_add, ← ENNReal.ofReal_mul hp0.le, ht₀]
        · congr 1
          rw [mul_add]
          exact boole_layer_alg ha hℓpos hp0 hp1
        · exact mul_nonneg hℓpos.le (div_nonneg (Real.rpow_nonneg ht₀pos.le _) hp0.le)
        · exact div_nonneg (mul_nonneg ha.le (Real.rpow_nonneg ht₀pos.le _)) (by linarith)

/-- The matrix unit has operator norm at most one. -/
private lemma boole_norm_single_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (i : m) (j : n) : ‖(Matrix.single i j (1 : ℂ) : Matrix m n ℂ)‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  change ‖Matrix.toEuclideanLin (Matrix.single i j (1 : ℂ)) x‖ ≤ 1 * ‖x‖
  rw [Matrix.toLpLin_apply, Matrix.single_mulVec]
  have h : (WithLp.toLp 2 (Function.update (0 : m → ℂ) i ((1 : ℂ) * x.ofLp j)) :
      EuclideanSpace ℂ m) = EuclideanSpace.single i ((1 : ℂ) * x j) := rfl
  rw [h, EuclideanSpace.single, PiLp.norm_single 2 (fun _ => ℂ) i, one_mul, one_mul]
  exact PiLp.norm_apply_le x j

/-- The operator norm is bounded by the sum of the absolute values of the entries. -/
private lemma boole_norm_le_sum {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) : ‖M‖ ≤ ∑ i, ∑ j, ‖M i j‖ := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : ℂ) by
    rw [Matrix.smul_single]; simp, norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (boole_norm_single_le i j)

/-- The four unit phases of the polarization identity. -/
private def booleCs : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]

/-- The phases `booleCs` have modulus one. -/
private lemma booleCs_norm (i : Fin 4) : ‖booleCs i‖ = 1 := by
  fin_cases i <;> simp [booleCs]

/-- Polarization: `conj a · b = (1/4) Σ_c conj c · |a + c b|²` over `c ∈ {1, -1, i, -i}`. -/
private lemma boole_polarization (a b : ℂ) :
    star a * b = ∑ i : Fin 4, (1 / 4 : ℂ) * star (booleCs i) *
      ((‖a + booleCs i * b‖ ^ 2 : ℝ) : ℂ) := by
  have h : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := fun z => by
    rw [mul_comm, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  simp only [h, Fin.sum_univ_four, booleCs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, star_one, star_neg, Complex.star_def, Complex.conj_I, Matrix.head_cons,
    Matrix.tail_cons, map_add, map_mul, map_neg, map_one]
  ring_nf
  simp only [Complex.I_sq]
  ring

section BooleSpectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `A - z` is diagonalized by the unitary of eigenvectors, with diagonal `λ_k - z`. -/
private lemma boole_sub_smul_one_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : ℂ) :
    A - z • (1 : Matrix n n ℂ) =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ) - z) *
        (star (hA.eigenvectorUnitary : Matrix n n ℂ)) := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  have hU : (hA.eigenvectorUnitary : Matrix n n ℂ) * (star (hA.eigenvectorUnitary : Matrix n n ℂ))
      = 1 := Unitary.coe_mul_star_self _
  have hD : Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ) - z) =
      Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) - z • (1 : Matrix n n ℂ) := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
    rfl
  rw [hD, Matrix.mul_sub, Matrix.sub_mul, ← h]
  congr 1
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

/-- At a real energy `E` that is not an eigenvalue, the resolvent is `U diag((λ_k - E)⁻¹) U*`. -/
private lemma boole_resolventMat_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) {E : ℝ}
    (hE : ∀ k, hA.eigenvalues k ≠ E) :
    resolventMat A (E : ℂ) =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ) - E)⁻¹) *
        (star (hA.eigenvectorUnitary : Matrix n n ℂ)) := by
  have hU : (hA.eigenvectorUnitary : Matrix n n ℂ) * (star (hA.eigenvectorUnitary : Matrix n n ℂ))
      = 1 := Unitary.coe_mul_star_self _
  have hU' : (star (hA.eigenvectorUnitary : Matrix n n ℂ)) * (hA.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_star_mul_self _
  have hne : ∀ k, (hA.eigenvalues k : ℂ) - E ≠ 0 := fun k =>
    sub_ne_zero.mpr (by exact_mod_cast hE k)
  refine Matrix.inv_eq_right_inv ?_
  rw [boole_sub_smul_one_eq hA]
  calc _ = (hA.eigenvectorUnitary : Matrix n n ℂ) *
          (Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ) - E) *
            Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ) - E)⁻¹)) *
          (star (hA.eigenvectorUnitary : Matrix n n ℂ)) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (star (hA.eigenvectorUnitary : Matrix n n ℂ)), hU', Matrix.one_mul]
    _ = 1 := by
        rw [Matrix.diagonal_mul_diagonal]
        have : (fun k => ((hA.eigenvalues k : ℂ) - E) * ((hA.eigenvalues k : ℂ) - E)⁻¹) =
            fun _ => (1 : ℂ) := by
          funext k
          exact mul_inv_cancel₀ (hne k)
        rw [this, Matrix.diagonal_one, Matrix.mul_one, hU]

/-- The `(α, β)` entry of `ι_x^* (A - E)^{-1} ι_y` in the eigenbasis of `A`. -/
private lemma boole_entry_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) {E : ℝ}
    (hE : ∀ k, hA.eigenvalues k ≠ E) {W : ℕ} (ιx ιy : Matrix n (Fin W) ℂ) (α β : Fin W) :
    (ιxᴴ * resolventMat A (E : ℂ) * ιy) α β =
      ∑ k, star (((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * ιx) k α) *
        ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * ιy) k β / ((hA.eigenvalues k : ℂ) - E) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  have h1 : ιxᴴ * resolventMat A (E : ℂ) * ιy =
      (Uᴴ * ιx)ᴴ * Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ) - E)⁻¹) * (Uᴴ * ιy) := by
    rw [boole_resolventMat_eq hA hE, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hU]
  rw [h1, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, div_eq_mul_inv]
  ring

/-- The columns of a matrix `X` with `Xᴴ X = 1` have unit mass. -/
private lemma boole_sum_norm_sq {K : Type*} [Fintype K] {W : ℕ} {X : Matrix K (Fin W) ℂ}
    (hX : Xᴴ * X = 1) (α : Fin W) : ∑ k, ‖X k α‖ ^ 2 = 1 := by
  have h := congrFun (congrFun hX α) α
  rw [Matrix.mul_apply] at h
  simp only [Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h2 : ∀ k, star (X k α) * X k α = ((‖X k α‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  simp only [h2] at h
  exact_mod_cast h

end BooleSpectral

/-- Subadditivity of `x ↦ x^p` on finite sums of nonnegative reals, for `0 < p ≤ 1`. -/
private lemma boole_rpow_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) : (∑ i ∈ s, x i) ^ p ≤ ∑ i ∈ s, x i ^ p := by
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hp0.ne']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
    calc _ ≤ x a ^ p + (∑ i ∈ s, x i) ^ p :=
          Real.rpow_add_le_add_rpow (hx a (Finset.mem_insert_self _ _)) hs hp0.le hp1
      _ ≤ _ := by
          gcongr
          exact ih fun i hi => hx i (Finset.mem_insert_of_mem hi)

/-- The `L^p(J)` bound for the resolvent quadratic form `Σ_j s_j/(λ_j − E)` of a positive atomic
measure of mass at most `4` (Boole's identity [PSZ, (1.5)], layer-cake part). -/
private lemma boole_lintegral_booleF_le {ι : Type*} [Fintype ι] (lam s : ι → ℝ)
    (hs : ∀ j, 0 ≤ s j) (hS : ∑ j, s j ≤ 4) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {J : Set ℝ}
    (hJf : volume J ≠ ⊤) :
    ∫⁻ E in J, ENNReal.ofReal (|booleF lam s E| ^ p) ≤
      ENNReal.ofReal (8 ^ p * (volume J).toReal ^ (1 - p) / (1 - p)) := by
  refine boole_lintegral_rpow_le (measurable_booleF lam s).abs (fun E => abs_nonneg _) hJf
    (a := 8) (by norm_num) hp0 hp1 fun t ht => ?_
  calc (volume.restrict J) {E | t < |booleF lam s E|} ≤ volume {E | t < |booleF lam s E|} :=
        Measure.le_iff'.mp Measure.restrict_le_self _
    _ = ENNReal.ofReal (2 * (∑ j, s j) / t) := volume_abs_booleF_of_nonneg lam s hs ht
    _ ≤ ENNReal.ofReal (8 / t) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by linarith) ht.le)

/-- (8.16) [uvg:eq:energyapriori] for one entry: with `Σ|a_k|² = Σ|b_k|² = 1`,
`∫_J |Σ_k conj(a_k) b_k/(μ_k − E)|^p dE ≤ C_p |J|^{1-p}`. Polarization writes the sum as four
resolvent quadratic forms of mass at most `4`. -/
private lemma boole_lintegral_entry_le {K : Type*} [Fintype K] (μ : K → ℝ) (a b : K → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) (hb : ∑ k, ‖b k‖ ^ 2 = 1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {J : Set ℝ} (hJf : volume J ≠ ⊤) :
    ∫⁻ E in J, ENNReal.ofReal (‖∑ k, star (a k) * b k / ((μ k : ℂ) - E)‖ ^ p) ≤
      ENNReal.ofReal (booleConst p * (volume J).toReal ^ (1 - p)) := by
  set s : Fin 4 → K → ℝ := fun i k => ‖a k + booleCs i * b k‖ ^ 2 with hs
  have hs0 : ∀ i k, 0 ≤ s i k := fun i k => by positivity
  have hsum : ∀ i, ∑ k, s i k ≤ 4 := by
    intro i
    calc ∑ k, s i k ≤ ∑ k, (2 * ‖a k‖ ^ 2 + 2 * ‖b k‖ ^ 2) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have h := norm_add_le (a k) (booleCs i * b k)
          rw [norm_mul, booleCs_norm, one_mul] at h
          have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
          simp only [hs]
          nlinarith [sq_nonneg (‖a k‖ - ‖b k‖)]
      _ = 4 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ha, hb]; norm_num
  -- the entry is a combination of four quadratic forms
  have hpt : ∀ E : ℝ, ‖∑ k, star (a k) * b k / ((μ k : ℂ) - E)‖ ≤
      ∑ i, (1 / 4) * |booleF μ (s i) E| := by
    intro E
    have e : ∑ k, star (a k) * b k / ((μ k : ℂ) - E) =
        ∑ i, (1 / 4 : ℂ) * star (booleCs i) * ((booleF μ (s i) E : ℝ) : ℂ) := by
      calc _ = ∑ k, ∑ i, (1 / 4 : ℂ) * star (booleCs i) * ((s i k : ℝ) : ℂ) / ((μ k : ℂ) - E) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [boole_polarization (a k) (b k), Finset.sum_div]
        _ = ∑ i, ∑ k, (1 / 4 : ℂ) * star (booleCs i) * ((s i k : ℝ) : ℂ) / ((μ k : ℂ) - E) :=
            Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [booleF, Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_sub,
              Finset.mul_sum, mul_div_assoc]
    rw [e]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_mul, norm_mul, norm_star, booleCs_norm, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  -- subadditivity of `x ↦ x^p`
  have hsub : ∀ E : ℝ, ENNReal.ofReal (‖∑ k, star (a k) * b k / ((μ k : ℂ) - E)‖ ^ p) ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ p) * ∑ i, ENNReal.ofReal (|booleF μ (s i) E| ^ p) := by
    intro E
    calc _ ≤ ENNReal.ofReal ((∑ i, (1 / 4) * |booleF μ (s i) E|) ^ p) :=
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) (hpt E) hp0.le)
      _ ≤ ENNReal.ofReal (∑ i, ((1 / 4) * |booleF μ (s i) E|) ^ p) := by
          refine ENNReal.ofReal_le_ofReal ?_
          exact boole_rpow_sum_le _ _ (fun i _ => by positivity) hp0 hp1.le
      _ = _ := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Real.mul_rpow (by norm_num) (abs_nonneg _), ENNReal.ofReal_mul (by positivity)]
  calc _ ≤ ∫⁻ E in J, ENNReal.ofReal ((1 / 4 : ℝ) ^ p) *
          ∑ i, ENNReal.ofReal (|booleF μ (s i) E| ^ p) := lintegral_mono fun E => hsub E
    _ = ENNReal.ofReal ((1 / 4 : ℝ) ^ p) *
          ∑ i, ∫⁻ E in J, ENNReal.ofReal (|booleF μ (s i) E| ^ p) := by
        rw [lintegral_const_mul, lintegral_finsetSum]
        · exact fun i _ => ((measurable_booleF μ (s i)).abs.pow_const p).ennreal_ofReal
        · exact Finset.measurable_sum _ fun i _ =>
            ((measurable_booleF μ (s i)).abs.pow_const p).ennreal_ofReal
    _ ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ p) *
          ∑ _i : Fin 4, ENNReal.ofReal (8 ^ p * (volume J).toReal ^ (1 - p) / (1 - p)) := by
        gcongr with i
        exact boole_lintegral_booleF_le μ (s i) (hs0 i) (hsum i) hp0 hp1 hJf
    _ = ENNReal.ofReal (booleConst p * (volume J).toReal ^ (1 - p)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have h1 : (1 / 4 : ℝ) ^ p * 8 ^ p = 2 ^ p := by
          rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
        unfold booleConst
        push_cast
        calc (1 / 4 : ℝ) ^ p * (4 * (8 ^ p * (volume J).toReal ^ (1 - p) / (1 - p)))
            = 4 * ((1 / 4 : ℝ) ^ p * 8 ^ p) * (volume J).toReal ^ (1 - p) / (1 - p) := by ring
          _ = _ := by rw [h1]; ring

/-- (8.16) [uvg:eq:energyapriori]: `∫_{J₀} ‖ι_x^* (H₀ − E)^{-1} ι_y‖^p dE ≤ C_p W² |J₀|^{1-p}` for
Hermitian `H₀`, isometries `ι_x, ι_y` and `J₀` of finite length. -/
theorem lintegral_isometry_resolvent_le {n : Type*} [Fintype n] [DecidableEq n] {W : ℕ}
    {H₀ : Matrix n n ℂ} (hH₀ : H₀.IsHermitian) {ιx ιy : Matrix n (Fin W) ℂ}
    (hx : ιxᴴ * ιx = 1) (hy : ιyᴴ * ιy = 1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {J₀ : Set ℝ} (hJ₀ : MeasurableSet J₀) (hJf : volume J₀ ≠ ⊤) :
    ∫⁻ E in J₀, ‖ιxᴴ * resolventMat H₀ E * ιy‖ₑ ^ p ≤
      ENNReal.ofReal (booleConst p * (W : ℝ) ^ 2 * (volume J₀).toReal ^ (1 - p)) := by
  have _ := hJ₀
  set U : Matrix n n ℂ := (hH₀.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : U * Uᴴ = 1 := by
    rw [hU, ← Matrix.star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  have hX : (Uᴴ * ιx)ᴴ * (Uᴴ * ιx) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc U, hUU, Matrix.one_mul, hx]
  have hY : (Uᴴ * ιy)ᴴ * (Uᴴ * ιy) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc U, hUU, Matrix.one_mul, hy]
  have hae : ∀ᵐ E ∂(volume.restrict J₀), ∀ k, hH₀.eigenvalues k ≠ E := by
    refine ae_restrict_of_ae ?_
    have h0 : volume (Set.range hH₀.eigenvalues) = 0 := (Set.finite_range _).measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with E hE k hk
    exact hE ⟨k, hk⟩
  have hmeas : ∀ α β : Fin W, Measurable fun E : ℝ => ENNReal.ofReal (‖∑ k,
      star ((Uᴴ * ιx) k α) * (Uᴴ * ιy) k β / ((hH₀.eigenvalues k : ℂ) - E)‖ ^ p) := by
    intro α β
    refine Measurable.ennreal_ofReal (Measurable.pow_const (Measurable.norm ?_) _)
    exact Finset.measurable_sum _ fun k _ =>
      measurable_const.div (measurable_const.sub Complex.measurable_ofReal)
  calc ∫⁻ E in J₀, ‖ιxᴴ * resolventMat H₀ E * ιy‖ₑ ^ p
      ≤ ∫⁻ E in J₀, ∑ α, ∑ β, ENNReal.ofReal (‖∑ k, star ((Uᴴ * ιx) k α) * (Uᴴ * ιy) k β /
          ((hH₀.eigenvalues k : ℂ) - E)‖ ^ p) := by
        refine lintegral_mono_ae (hae.mono fun E hE => ?_)
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
        calc _ ≤ ENNReal.ofReal (∑ α, ∑ β, ‖(ιxᴴ * resolventMat H₀ (E : ℂ) * ιy) α β‖ ^ p) := by
              refine ENNReal.ofReal_le_ofReal ?_
              refine (Real.rpow_le_rpow (norm_nonneg _) (boole_norm_le_sum _) hp0.le).trans ?_
              refine (boole_rpow_sum_le _ _ (fun α _ => Finset.sum_nonneg fun β _ => norm_nonneg _)
                hp0 hp1.le).trans (Finset.sum_le_sum fun α _ => ?_)
              exact boole_rpow_sum_le _ _ (fun β _ => norm_nonneg _) hp0 hp1.le
          _ = _ := by
              rw [ENNReal.ofReal_sum_of_nonneg fun α _ =>
                Finset.sum_nonneg fun β _ => by positivity]
              refine Finset.sum_congr rfl fun α _ => ?_
              rw [ENNReal.ofReal_sum_of_nonneg fun β _ => by positivity]
              refine Finset.sum_congr rfl fun β _ => ?_
              rw [boole_entry_eq hH₀ hE ιx ιy α β]
    _ = ∑ α, ∑ β, ∫⁻ E in J₀, ENNReal.ofReal (‖∑ k, star ((Uᴴ * ιx) k α) * (Uᴴ * ιy) k β /
          ((hH₀.eigenvalues k : ℂ) - E)‖ ^ p) := by
        rw [lintegral_finsetSum _ fun α _ => Finset.measurable_sum _ fun β _ => hmeas α β]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [lintegral_finsetSum _ fun β _ => hmeas α β]
    _ ≤ ∑ _α : Fin W, ∑ _β : Fin W,
          ENNReal.ofReal (booleConst p * (volume J₀).toReal ^ (1 - p)) := by
        refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => ?_
        exact boole_lintegral_entry_le hH₀.eigenvalues _ _ (boole_sum_norm_sq hX α)
          (boole_sum_norm_sq hY β) hp0 hp1 hJf
    _ = ENNReal.ofReal (booleConst p * (W : ℝ) ^ 2 * (volume J₀).toReal ^ (1 - p)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- The isometry `ℂ^W → ℂ^L ⊗ ℂ^W` onto the `a`-th block. -/
private def booleEmb {L : ℕ} (W : ℕ) (a : Fin L) : Matrix (Fin L × Fin W) (Fin W) ℂ :=
  Matrix.of fun p β => if p = (a, β) then 1 else 0

private lemma booleEmb_isometry {L : ℕ} (W : ℕ) (a : Fin L) :
    (booleEmb W a)ᴴ * booleEmb W a = 1 := by
  ext α β
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, booleEmb, Matrix.of_apply]
  by_cases h : α = β
  · subst h; simp
  · rw [Matrix.one_apply_ne h]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h1 : x = (a, α)
    · by_cases h2 : x = (a, β)
      · exact absurd ((congrArg Prod.snd h1).symm.trans (congrArg Prod.snd h2)) h
      · simp [h2]
    · simp [h1]

private lemma booleEmb_mul {L : ℕ} (W : ℕ) (a b : Fin L)
    (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    (booleEmb W a)ᴴ * A * booleEmb W b = blockOf A a b := by
  ext α β
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, booleEmb, blockOf]

/-- (8.16) [uvg:eq:energyapriori] for the blocks `G(a, b; E)` of a Hermitian matrix on
`ℂ^L ⊗ ℂ^W`. -/
theorem lintegral_blockOf_resolventMat_le {W L : ℕ}
    {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hA : A.IsHermitian) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) {J₀ : Set ℝ} (hJ₀ : MeasurableSet J₀) (hJf : volume J₀ ≠ ⊤) (a b : Fin L) :
    ∫⁻ E in J₀, ‖blockOf (resolventMat A E) a b‖ₑ ^ p ≤
      ENNReal.ofReal (booleConst p * (W : ℝ) ^ 2 * (volume J₀).toReal ^ (1 - p)) := by
  simp only [← booleEmb_mul W a b]
  exact lintegral_isometry_resolvent_le hA (booleEmb_isometry W a) (booleEmb_isometry W b)
    hp0 hp1 hJ₀ hJf

end LSBA
