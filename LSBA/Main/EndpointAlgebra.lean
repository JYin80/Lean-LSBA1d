import LSBA.Main.CountMono
import LSBA.Model.Bulk
import LSBA.Dyson.Distribution

/-!
# Endpoint algebra

The derivation of the lower half of (1.17) [eq:main] from (2.12) [uv:eq:lower-regions-output]
and Lemma 1.3 [lem:rough-density] (the last display (3.12) [uv:eq:sampling] of the proof in
Section 3.7 [sec:upper-regions], without `B_+`), and of the lower half of (1.18) [eq:simultaneous]
from (2.12) [uv:eq:lower-regions-output] by
Markov's inequality, as implications between the endpoint statements: (E1) is the count form (2.12)
[uv:eq:lower-regions-output], (E2) the lower half of (1.17) [eq:main], (E3) the lower half of (1.18)
[eq:simultaneous] and (E4) Lemma 1.3 [lem:rough-density].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `ν_g` has no atoms, (1.10) [eq:distribution]. -/
private lemma endpointAlgebra_singleton (g : ℝ) (hg : 0 ≤ g) (x : ℝ) : nuDyson g {x} = 0 := by
  have hP := (nuDyson_spec g hg).1
  have h0 : (nuDyson g {x}).toReal ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨h₀, hh₀, H⟩ := nuDyson_noatoms_uniform ε hε
    have h1 := H h₀ ⟨hh₀, le_rfl⟩ g hg x
    have h2 : (nuDyson g {x}).toReal ≤ (nuDyson g (Set.Icc (x - h₀) (x + h₀))).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (by
        intro t ht
        rw [Set.mem_singleton_iff] at ht
        subst ht
        constructor <;> linarith))
    linarith
  exact (ENNReal.toReal_eq_zero_iff _).mp (le_antisymm h0 ENNReal.toReal_nonneg) |>.resolve_right
    (measure_ne_top _ _)

/-- `F_g(-x) = 1 - F_g(x)`: `ν_g` is even and has no atoms (Section 1.1 [sec:model], (1.10)
[eq:distribution]). -/
theorem Fdist_neg (g : ℝ) (hg : 0 ≤ g) (x : ℝ) : Fdist g (-x) = 1 - Fdist g x := by
  have hP := (nuDyson_spec g hg).1
  have hev := nuDyson_map_neg g hg
  have : NullSingletonClass (nuDyson g) := ⟨endpointAlgebra_singleton g hg⟩
  have h1 : nuDyson g (Set.Iic (-x)) = nuDyson g (Set.Ici x) := by
    conv_lhs => rw [← hev]
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext t
    simp
  have h2 : nuDyson g (Set.Ici x) = nuDyson g (Set.Ioi x) := measure_congr Ioi_ae_eq_Ici.symm
  have h3 : nuDyson g (Set.Ioi x) = 1 - nuDyson g (Set.Iic x) := by
    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]
  unfold Fdist
  rw [h1, h2, h3, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]

/-- If the empirical distribution function is within `κ/2` of a continuous, nondecreasing `F`
with `F(-x) = 1 - F(x)`, then `{E : κ/2 ≤ F(-|E|)}` contains at least `(1 - 2κ) N` eigenvalues
(the count after (1.16) [eq:bulk-sampling]). -/
theorem countIn_bulk_ge {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {F : ℝ → ℝ} (hFc : Continuous F) (hFm : Monotone F)
    (hFs : ∀ x, F (-x) = 1 - F x) {κ : ℝ} (hclose : ∀ x, |empCDF A x - F x| ≤ κ / 2) :
    (1 - 2 * κ) * (Fintype.card n : ℝ) ≤ (countIn A {E | κ / 2 ≤ F (-|E|)} : ℝ) := by
  set N : ℝ := (Fintype.card n : ℝ) with hN
  set ev := hA.eigenvalues with hev
  have hκ : 0 ≤ κ := by have := hclose 0; linarith [abs_nonneg (empCDF A 0 - F 0)]
  rcases (Nat.cast_nonneg (Fintype.card n) : (0 : ℝ) ≤ _).eq_or_lt with hN0 | hNpos
  · rw [hN, ← hN0, mul_zero]
    exact Nat.cast_nonneg _
  have hcnt : ∀ J : Set ℝ, (countIn A J : ℝ) = (#(univ.filter fun k => ev k ∈ J) : ℝ) := by
    intro J
    simp [countIn, hA, hev]
  have hc : ∀ x, |(#(univ.filter fun k => ev k ≤ x) : ℝ) / N - F x| ≤ κ / 2 := by
    intro x
    have := hclose x
    rw [empCDF, hcnt] at this
    simpa using this
  have hup : ∀ x, (#(univ.filter fun k => ev k ≤ x) : ℝ) ≤ N * (F x + κ / 2) := by
    intro x
    have h := (abs_le.mp (hc x)).2
    have : (#(univ.filter fun k => ev k ≤ x) : ℝ) / N ≤ F x + κ / 2 := by linarith
    rw [div_le_iff₀ hNpos] at this
    linarith
  have hlo : ∀ x, N * (F x - κ / 2) ≤ (#(univ.filter fun k => ev k ≤ x) : ℝ) := by
    intro x
    have h := (abs_le.mp (hc x)).1
    have : F x - κ / 2 ≤ (#(univ.filter fun k => ev k ≤ x) : ℝ) / N := by linarith
    rw [le_div_iff₀ hNpos] at this
    linarith
  -- the lower tail `{F < κ/2}`
  have hLo : (#(univ.filter fun k => F (ev k) < κ / 2) : ℝ) ≤ κ * N := by
    by_cases hne : (univ.filter fun k => F (ev k) < κ / 2).Nonempty
    · obtain ⟨k₀, hk₀, hmax⟩ := Finset.exists_max_image _ ev hne
      have hk₀' : F (ev k₀) < κ / 2 := (Finset.mem_filter.mp hk₀).2
      have hsub : (univ.filter fun k => F (ev k) < κ / 2) ⊆
          (univ.filter fun k => ev k ≤ ev k₀) := by
        intro k hk
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmax k hk⟩
      have h1 : (#(univ.filter fun k => F (ev k) < κ / 2) : ℝ) ≤
          (#(univ.filter fun k => ev k ≤ ev k₀) : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have h2 := hup (ev k₀)
      nlinarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
      positivity
  -- the upper tail `{F > 1 - κ/2}`
  have hUp : (#(univ.filter fun k => 1 - κ / 2 < F (ev k)) : ℝ) ≤ κ * N := by
    by_cases hne : (univ.filter fun k => 1 - κ / 2 < F (ev k)).Nonempty
    · obtain ⟨k₁, hk₁, hmin⟩ := Finset.exists_min_image _ ev hne
      have hk₁' : 1 - κ / 2 < F (ev k₁) := (Finset.mem_filter.mp hk₁).2
      have hev1 : ∀ᶠ y in nhdsWithin (ev k₁) (Set.Iio (ev k₁)), 1 - κ / 2 < F y :=
        nhdsWithin_le_nhds (hFc.continuousAt.eventually (lt_mem_nhds hk₁'))
      have hev2 : ∀ᶠ y in nhdsWithin (ev k₁) (Set.Iio (ev k₁)), y < ev k₁ :=
        self_mem_nhdsWithin
      obtain ⟨y, hy1, hy2⟩ := (hev1.and hev2).exists
      have hsub : (univ.filter fun k => 1 - κ / 2 < F (ev k)) ⊆
          (univ.filter fun k => ¬ ev k ≤ y) := by
        intro k hk
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have := hmin k hk
        linarith
      have h1 : (#(univ.filter fun k => 1 - κ / 2 < F (ev k)) : ℝ) ≤
          (#(univ.filter fun k => ¬ ev k ≤ y) : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have h3 : (#(univ.filter fun k => ev k ≤ y) : ℝ) + (#(univ.filter fun k => ¬ ev k ≤ y) : ℝ)
          = N := by
        rw [hN]
        exact_mod_cast Finset.card_filter_add_card_filter_not _
      have h2 := hlo y
      nlinarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
      positivity
  -- the complement of the bulk set lies in the two tails
  have hsub : (univ.filter fun k => ¬ ev k ∈ {E | κ / 2 ≤ F (-|E|)}) ⊆
      (univ.filter fun k => F (ev k) < κ / 2) ∪ (univ.filter fun k => 1 - κ / 2 < F (ev k)) := by
    intro k hk
    have hk' : F (-|ev k|) < κ / 2 := by simpa using (Finset.mem_filter.mp hk).2
    rcases le_or_gt (ev k) 0 with h | h
    · rw [abs_of_nonpos h, neg_neg] at hk'
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩)
    · rw [abs_of_pos h, hFs] at hk'
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩)
  have hcomp : (#(univ.filter fun k => ¬ ev k ∈ {E | κ / 2 ≤ F (-|E|)}) : ℝ) ≤ 2 * κ * N := by
    have := Finset.card_le_card hsub
    have h' := (Finset.card_union_le (univ.filter fun k => F (ev k) < κ / 2)
      (univ.filter fun k => 1 - κ / 2 < F (ev k)))
    have : (#(univ.filter fun k => ¬ ev k ∈ {E | κ / 2 ≤ F (-|E|)}) : ℝ) ≤
        (#(univ.filter fun k => F (ev k) < κ / 2) : ℝ) +
          (#(univ.filter fun k => 1 - κ / 2 < F (ev k)) : ℝ) := by
      exact_mod_cast this.trans h'
    linarith
  have htot : (#(univ.filter fun k => ev k ∈ {E | κ / 2 ≤ F (-|E|)}) : ℝ) +
      (#(univ.filter fun k => ¬ ev k ∈ {E | κ / 2 ≤ F (-|E|)}) : ℝ) = N := by
    rw [hN]
    exact_mod_cast Finset.card_filter_add_card_filter_not _
  rw [hcnt]
  linarith

/-- Lower bound on the expected ratio `good / count` with `0/0 = 0`: the measure-level step of
(3.12) [uv:eq:sampling]. -/
theorem integral_ratio_ge {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] (good bad cnt : α → ℕ) (hsum : ∀ x, good x + bad x = cnt x)
    (hR : AEMeasurable (fun x => (good x : ℝ) / cnt x) P)
    (hb : Integrable (fun x => (bad x : ℝ)) P) (G : Set α) {m : ℝ} (hm : 0 < m)
    (hG : ∀ x ∈ G, m ≤ cnt x) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hGc : P Gᶜ ≤ ENNReal.ofReal ε₁)
    (hbad : ∫ x, (bad x : ℝ) ∂P ≤ ε₂ * m) :
    1 - ε₁ - ε₂ ≤ ∫ x, (good x : ℝ) / cnt x ∂P := by
  set B := toMeasurable P Gᶜ with hBdef
  have hBm : MeasurableSet B := measurableSet_toMeasurable _ _
  have hGB : Gᶜ ⊆ B := subset_toMeasurable _ _
  have hRle : ∀ x, (good x : ℝ) / cnt x ≤ 1 := by
    intro x
    refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
    rw [← hsum x]
    exact_mod_cast Nat.le_add_right _ _
  have hRnn : ∀ x, 0 ≤ (good x : ℝ) / cnt x := fun x => by positivity
  have hRi : Integrable (fun x => (good x : ℝ) / cnt x) P := by
    refine Integrable.of_bound hR.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (hRnn x)]
    exact hRle x
  have hi1 : Integrable (Bᶜ.indicator (1 : α → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hBm.compl
  have hfi : Integrable (fun x => Bᶜ.indicator (1 : α → ℝ) x - (bad x : ℝ) / m) P :=
    hi1.sub (hb.div_const m)
  have hpt : ∀ x, Bᶜ.indicator (1 : α → ℝ) x - (bad x : ℝ) / m ≤ (good x : ℝ) / cnt x := by
    intro x
    by_cases hx : x ∈ Bᶜ
    · rw [Set.indicator_of_mem hx, Pi.one_apply]
      have hxG : x ∈ G := by
        by_contra h
        exact hx (hGB h)
      have hc := hG x hxG
      have hcpos : (0 : ℝ) < cnt x := lt_of_lt_of_le hm hc
      have hg : (good x : ℝ) = cnt x - bad x := by
        rw [← hsum x, Nat.cast_add]
        ring
      rw [hg, sub_div, div_self hcpos.ne']
      have : (bad x : ℝ) / cnt x ≤ (bad x : ℝ) / m :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hm hc
      linarith
    · rw [Set.indicator_of_notMem hx]
      have : 0 ≤ (bad x : ℝ) / m := by positivity
      linarith [hRnn x]
  have hint := integral_mono hfi hRi hpt
  rw [integral_sub hi1 (hb.div_const m),
    integral_indicator_one hBm.compl, integral_div] at hint
  have hPB : P.real Bᶜ = 1 - P.real B := by
    rw [measureReal_compl hBm, probReal_univ]
  have hPB' : P.real B ≤ ε₁ := by
    rw [Measure.real, hBdef, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε₁ hGc
  have hdiv : (∫ x, (bad x : ℝ) ∂P) / m ≤ ε₂ := by
    rw [div_le_iff₀ hm]
    exact hbad
  linarith

/-- Markov's inequality for a count: `P{b > 0} ≤ E b`. -/
theorem measure_pos_le_integral {α : Type*} [MeasurableSpace α] (P : Measure α) (b : α → ℕ)
    (hb : Integrable (fun x => (b x : ℝ)) P) :
    P {x | 0 < b x} ≤ ENNReal.ofReal (∫ x, (b x : ℝ) ∂P) := by
  have h1 := mul_meas_ge_le_lintegral₀ hb.aemeasurable.ennreal_ofReal 1
  rw [one_mul] at h1
  rw [ofReal_integral_eq_lintegral_ofReal hb
    (Filter.Eventually.of_forall fun x => Nat.cast_nonneg _)]
  refine le_trans (measure_mono ?_) h1
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hx)

/-- The ratio `good / count` of the model is integrable (it lies in `[0, 1]`). -/
private lemma endpointAlgebra_ratio_integrable (g : ℝ) (W L : ℕ) {J : Set ℝ}
    (hJ : MeasurableSet J) (r : ℝ) :
    Integrable (fun ω => (goodCount W L (Hmat g W L ω) J r : ℝ) /
      (countIn (Hmat g W L ω) J : ℝ)) (μ W L) := by
  have hR : AEMeasurable (fun ω => (goodCount W L (Hmat g W L ω) J r : ℝ) /
      (countIn (Hmat g W L ω) J : ℝ)) (μ W L) :=
    (aemeasurable_goodCount_Hmat g W L hJ r).div
      (measurable_from_nat.comp (measurable_countIn_Hmat g W L hJ)).aemeasurable
  refine Integrable.of_bound hR.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
  rw [← goodCount_add_badCount W L (Hmat g W L ω) J r]
  exact_mod_cast Nat.le_add_right _ _

/-- For large `W`, `C e^{-c W² L} ≤ W^{-D}/2` for every `L ≥ 3`. -/
private lemma endpointAlgebra_exp_small (C c D : ℝ) (hC : 0 < C) (hc : 0 < c) :
    ∀ᶠ W : ℕ in Filter.atTop, ∀ L : ℕ, 3 ≤ L →
      C * Real.exp (-c * (W : ℝ) ^ 2 * L) ≤ (W : ℝ) ^ (-D) / 2 := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero D (3 * c) (by positivity)
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, x ^ D * Real.exp (-(3 * c) * x) < 1 / (2 * C) :=
    ht.eventually (gt_mem_nhds (by positivity))
  have h2 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h1
  filter_upwards [h2, Filter.eventually_ge_atTop 1] with W hW hW1 L hL
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hexp : Real.exp (-c * (W : ℝ) ^ 2 * L) ≤ Real.exp (-(3 * c) * W) := by
    apply Real.exp_le_exp.mpr
    have h3 : 3 * (W : ℝ) ≤ (W : ℝ) ^ 2 * L := by nlinarith
    nlinarith
  have hWD : 0 < (W : ℝ) ^ D := Real.rpow_pos_of_pos hWpos D
  rw [Real.rpow_neg hWpos.le D]
  rw [lt_div_iff₀ (by positivity)] at hW
  have h4 : C * Real.exp (-(3 * c) * W) * 2 * (W : ℝ) ^ D < 1 := by linarith
  have h5 : C * Real.exp (-(3 * c) * W) ≤ ((W : ℝ) ^ D)⁻¹ / 2 := by
    have h7 : C * Real.exp (-(3 * c) * W) * 2 ≤ 1 / (W : ℝ) ^ D :=
      (le_div_iff₀ hWD).mpr (by linarith)
    rw [one_div] at h7
    linarith
  have h6 : C * Real.exp (-c * (W : ℝ) ^ 2 * L) ≤ C * Real.exp (-(3 * c) * W) :=
    mul_le_mul_of_nonneg_left hexp hC.le
  linarith

/-- (E1) and (E4) imply (E2): the lower half of (1.17) [eq:main] from (2.12)
[uv:eq:lower-regions-output] and Lemma 1.3 [lem:rough-density], as in (3.12) [uv:eq:sampling];
`τ ≥ 1` by monotonicity in `τ`. -/
theorem lowerRatio_of_count_rough (κ : ℝ) (hκ : 0 < κ ∧ κ < 1 / 2)
    (hE1 : ∀ D τ : ℝ, 0 < D → 0 < τ ∧ τ < 1 → ∀ L₀ : ℕ,
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        AEMeasurable (fun ω => (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
            ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ)) (μ W L) ∧
        ((W : ℝ) * L)⁻¹ * ∫ ω, (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
            ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ) ∂(μ W L) ≤ (W : ℝ) ^ (-D))
    (hE4 : ∃ Wδ Lδ : ℕ, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ W : ℕ, Wδ ≤ W → ∀ L : ℕ, max Lδ 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        μ W L {ω | ∃ x : ℝ, κ / 2 < |empCDF (Hmat g W L ω) x - Fdist g x|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (W : ℝ) ^ 2 * L))) :
    ∃ L₀ : ℕ, ∀ L₁ : ℕ, L₀ ≤ L₁ → ∀ D τ : ℝ, 0 < D → 0 < τ →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        1 - (W : ℝ) ^ (-D) ≤
          ∫ ω, (goodCount W L (Hmat g W L ω) (bulkSet g κ L₁ L)
                  ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ) /
                (countIn (Hmat g W L ω) (bulkSet g κ L₁ L) : ℝ) ∂(μ W L) := by
  obtain ⟨Wδ, Lδ, C, c, hC, hc, hE4'⟩ := hE4
  refine ⟨Lδ, fun L₁ hL₁ D τ hD hτ => ?_⟩
  set τ' := min τ (1 / 2) with hτ'def
  have hτ' : 0 < τ' ∧ τ' < 1 :=
    ⟨lt_min hτ (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
  obtain ⟨W₁, hW₁⟩ := hE1 (D + 1) τ' (by linarith) hτ' L₁
  have hκ2 : 0 < 1 - 2 * κ := by linarith [hκ.2]
  have hev : ∀ᶠ W : ℕ in Filter.atTop, W₁ ≤ W ∧ Wδ ≤ W ∧ 1 ≤ W ∧
      2 / (1 - 2 * κ) ≤ (W : ℝ) ∧
      ∀ L : ℕ, 3 ≤ L → C * Real.exp (-c * (W : ℝ) ^ 2 * L) ≤ (W : ℝ) ^ (-D) / 2 :=
    (Filter.eventually_ge_atTop W₁).and ((Filter.eventually_ge_atTop Wδ).and
      ((Filter.eventually_ge_atTop 1).and
        ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and
          (endpointAlgebra_exp_small C c D hC hc))))
  obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨W₀, fun W hW L hL g hg => ?_⟩
  obtain ⟨hWW₁, hWWδ, hW1, hWκ, hWexp⟩ := hW₀ W hW
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  set J := bulkSet g κ L₁ L with hJdef
  have hJm : MeasurableSet J := measurableSet_bulkSet g κ L₁ L
  set r := (W : ℝ) ^ (-τ) * ellStar W L g with hrdef
  set r' := (W : ℝ) ^ (-τ') * ellStar W L g with hr'def
  have hrr : r ≤ r' := rpow_neg_mul_ellStar_le hW1 L g (min_le_left τ (1 / 2))
  obtain ⟨-, hbadW⟩ := hW₁ W hWW₁ L hL g hg
  have hbad : ∫ ω, (badCount W L (Hmat g W L ω) J r' : ℝ) ∂(μ W L) ≤
      (W : ℝ) ^ (-(D + 1)) * ((L : ℝ) * W) := by
    rw [inv_mul_le_iff₀ (by positivity)] at hbadW
    linarith
  have hmono : ∫ ω, (goodCount W L (Hmat g W L ω) J r' : ℝ) / (countIn (Hmat g W L ω) J : ℝ)
        ∂(μ W L) ≤
      ∫ ω, (goodCount W L (Hmat g W L ω) J r : ℝ) / (countIn (Hmat g W L ω) J : ℝ) ∂(μ W L) := by
    refine integral_mono (endpointAlgebra_ratio_integrable g W L hJm r')
      (endpointAlgebra_ratio_integrable g W L hJm r) fun ω => ?_
    exact div_le_div_of_nonneg_right (by exact_mod_cast goodCount_anti W L _ J hrr)
      (Nat.cast_nonneg _)
  refine le_trans ?_ hmono
  have hsum := fun ω => goodCount_add_badCount W L (Hmat g W L ω) J r'
  have hR := (endpointAlgebra_ratio_integrable g W L hJm r').aemeasurable
  have hb := integrable_badCount_Hmat g W L hJm r'
  have hcard : (Fintype.card (Fin L × Fin W) : ℝ) = (L : ℝ) * W := by simp
  have hWD : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg hWpos.le _
  by_cases hLL : L < L₁
  · -- `L < L₁`: `J = ℝ` and the count is `L W`
    have hJu : J = Set.univ := by simp [hJdef, bulkSet, hLL]
    have h := integral_ratio_ge (μ W L) (fun ω => goodCount W L (Hmat g W L ω) J r')
      (fun ω => badCount W L (Hmat g W L ω) J r') (fun ω => countIn (Hmat g W L ω) J) hsum hR hb
      Set.univ (m := (L : ℝ) * W) (by positivity)
      (fun ω _ => by
        rw [hJu, countIn_univ (Hmat_isHermitian g W L ω), hcard])
      (ε₁ := 0) le_rfl (by simp) (ε₂ := (W : ℝ) ^ (-(D + 1))) hbad
    have : (W : ℝ) ^ (-(D + 1)) ≤ (W : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_exponent_le hW1' (by linarith)
    linarith
  · -- `L ≥ L₁`: the bulk set of (1.16) [eq:bulk-sampling] and the event of Lemma 1.3
    -- [lem:rough-density]
    have hJb : J = {E | κ / 2 ≤ Fdist g (-|E|)} := by simp [hJdef, bulkSet, hLL]
    set G := {ω : Ω W L | ∀ x, |empCDF (Hmat g W L ω) x - Fdist g x| ≤ κ / 2} with hGdef
    have hGc : μ W L Gᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * (W : ℝ) ^ 2 * L)) := by
      refine le_trans (measure_mono ?_)
        (hE4' W hWWδ L (max_le (hL₁.trans (not_lt.mp hLL)) hL) g hg)
      intro ω hω
      simpa [hGdef, not_forall, not_le] using hω
    have h := integral_ratio_ge (μ W L) (fun ω => goodCount W L (Hmat g W L ω) J r')
      (fun ω => badCount W L (Hmat g W L ω) J r') (fun ω => countIn (Hmat g W L ω) J) hsum hR hb
      G (m := (1 - 2 * κ) * ((L : ℝ) * W)) (by positivity)
      (fun ω hω => by
        rw [hJb, ← hcard]
        exact countIn_bulk_ge (Hmat_isHermitian g W L ω) (Fdist_continuous g hg)
          (Fdist_monotone g) (Fdist_neg g hg) hω)
      (by positivity) hGc (ε₂ := (1 - 2 * κ)⁻¹ * (W : ℝ) ^ (-(D + 1)))
      (by
        have : (1 - 2 * κ)⁻¹ * (W : ℝ) ^ (-(D + 1)) * ((1 - 2 * κ) * ((L : ℝ) * W)) =
            (W : ℝ) ^ (-(D + 1)) * ((L : ℝ) * W) := by
          field_simp
        rw [this]
        exact hbad)
    have h1 := hWexp L hL
    have hsplit : (W : ℝ) ^ (-(D + 1)) = (W : ℝ) ^ (-D) * (W : ℝ)⁻¹ := by
      rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
    have hq : (1 - 2 * κ)⁻¹ * (W : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [div_le_iff₀ hκ2] at hWκ
      calc (1 - 2 * κ)⁻¹ * (W : ℝ)⁻¹ = ((1 - 2 * κ) * W)⁻¹ := (mul_inv _ _).symm
        _ ≤ 2⁻¹ := inv_anti₀ (by norm_num) (by linarith)
        _ = 1 / 2 := by norm_num
    have h2 : (1 - 2 * κ)⁻¹ * (W : ℝ) ^ (-(D + 1)) ≤ (W : ℝ) ^ (-D) / 2 := by
      rw [hsplit]
      have := mul_le_mul_of_nonneg_left hq hWD
      calc (1 - 2 * κ)⁻¹ * ((W : ℝ) ^ (-D) * (W : ℝ)⁻¹) =
          (W : ℝ) ^ (-D) * ((1 - 2 * κ)⁻¹ * (W : ℝ)⁻¹) := by ring
        _ ≤ (W : ℝ) ^ (-D) * (1 / 2) := this
        _ = (W : ℝ) ^ (-D) / 2 := by ring
    linarith

/-- (E1) implies (E3): the lower half of (1.18) [eq:simultaneous] by Markov's inequality. -/
theorem simultaneous_of_count (BL D τ κ : ℝ) (hBL : 0 < BL) (hD : 0 < D) (hτ : 0 < τ) (L₀ : ℕ)
    (hE1 : ∀ D' τ' : ℝ, 0 < D' → 0 < τ' ∧ τ' < 1 →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        AEMeasurable (fun ω => (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
            ((W : ℝ) ^ (-τ') * ellStar W L g) : ℝ)) (μ W L) ∧
        ((W : ℝ) * L)⁻¹ * ∫ ω, (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
            ((W : ℝ) ^ (-τ') * ellStar W L g) : ℝ) ∂(μ W L) ≤ (W : ℝ) ^ (-D')) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → (L : ℝ) ≤ (W : ℝ) ^ BL → ∀ g : ℝ, 0 ≤ g →
      μ W L {ω | 0 < badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ (-τ) * ellStar W L g)} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  set τ' := min τ (1 / 2) with hτ'def
  have hτ' : 0 < τ' ∧ τ' < 1 :=
    ⟨lt_min hτ (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
  obtain ⟨W₁, hW₁⟩ := hE1 (D + BL + 2) τ' (by linarith) hτ'
  refine ⟨max W₁ 1, fun W hW L hL hLW g hg => ?_⟩
  have hWW₁ : W₁ ≤ W := (le_max_left _ _).trans hW
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  set J := bulkSet g κ L₀ L with hJdef
  have hJm : MeasurableSet J := measurableSet_bulkSet g κ L₀ L
  have hrr : (W : ℝ) ^ (-τ) * ellStar W L g ≤ (W : ℝ) ^ (-τ') * ellStar W L g :=
    rpow_neg_mul_ellStar_le hW1 L g (min_le_left τ (1 / 2))
  obtain ⟨-, hbadW⟩ := hW₁ W hWW₁ L hL g hg
  have hsub : {ω | 0 < badCount W L (Hmat g W L ω) J ((W : ℝ) ^ (-τ) * ellStar W L g)} ⊆
      {ω | 0 < badCount W L (Hmat g W L ω) J ((W : ℝ) ^ (-τ') * ellStar W L g)} :=
    fun ω hω => lt_of_lt_of_le hω (badCount_mono W L _ subset_rfl hrr)
  refine (measure_mono hsub).trans ((measure_pos_le_integral _ _
    (integrable_badCount_Hmat g W L hJm _)).trans (ENNReal.ofReal_le_ofReal ?_))
  rw [inv_mul_le_iff₀ (by positivity)] at hbadW
  have hWD' : 0 ≤ (W : ℝ) ^ (-(D + BL + 2)) := Real.rpow_nonneg hWpos.le _
  calc _ ≤ ((W : ℝ) * L) * (W : ℝ) ^ (-(D + BL + 2)) := hbadW
    _ ≤ ((W : ℝ) * (W : ℝ) ^ BL) * (W : ℝ) ^ (-(D + BL + 2)) := by gcongr
    _ = (W : ℝ) ^ (-(D + 1)) := by
      rw [show (W : ℝ) * (W : ℝ) ^ BL = (W : ℝ) ^ (1 + BL) by
        rw [Real.rpow_add hWpos, Real.rpow_one], ← Real.rpow_add hWpos]
      congr 1
      ring
    _ ≤ (W : ℝ) ^ (-D) := Real.rpow_le_rpow_of_exponent_le hW1' (by linarith)

end LSBA
