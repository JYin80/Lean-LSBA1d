import LSBA.Main.EndpointAlgebra

/-!
# The energy window of the lower-bound assembly

For `L ≥ L₀` the energy set `J_{g,κ,L}` of (1.16) [eq:bulk-sampling] is a deterministic interval
`[-a, a]` with `F_g(-a) ≥ κ/2` and `0 ≤ a ≤ 4` (by (1.12) [eq:bounded-physical-bulk]), as
Theorem 2.2 [uv:lem:lower-volume] requires; and on the window `[-a - η, a + η]` with
`0 < η ≤ κ²/32` the distribution function stays above `κ/4`, by (1.13) [rd:eq:noatoms].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- For `L ≥ L₀` the energy set `J_{g,κ,L}` of (1.16) [eq:bulk-sampling] is a deterministic
interval `[-a, a]` with `F_g(-a) ≥ κ/2`; by (1.12) [eq:bounded-physical-bulk], `0 ≤ a ≤ 4`. -/
theorem bulkSet_eq_Icc (g κ : ℝ) (hg : 0 ≤ g) (hκ : 0 < κ ∧ κ < 1 / 2) (L₀ L : ℕ)
    (hL : L₀ ≤ L) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 4 ∧ κ / 2 ≤ Fdist g (-a) ∧ bulkSet g κ L₀ L = Set.Icc (-a) a := by
  obtain ⟨hκ0, hκ1⟩ := hκ
  set S : Set ℝ := {x | 0 ≤ x ∧ κ / 2 ≤ Fdist g (-x)} with hS
  set b : ℝ := (2 * g + 2) / max 1 g with hb
  have hb4 : b ≤ 4 := by
    rcases le_total g 1 with h1 | h1
    · rw [hb, max_eq_left h1, div_one]
      linarith
    · have hgpos : 0 < g := by linarith
      rw [hb, max_eq_right h1, div_le_iff₀ hgpos]
      linarith
  have hF0 : Fdist g 0 = 1 / 2 := by
    have h := Fdist_neg g hg 0
    rw [neg_zero] at h
    linarith
  have h0S : (0 : ℝ) ∈ S := ⟨le_rfl, by rw [neg_zero, hF0]; linarith⟩
  have hSb : ∀ x ∈ S, x ≤ b := by
    intro x hx
    by_contra hxb
    have hxb := not_le.mp hxb
    have hnull : nuDyson g (Set.Iic (-x)) = 0 := by
      refine measure_mono_null (fun t ht => ?_) (nuDyson_compl_support g hg)
      simp only [Set.mem_Iic] at ht
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le]
      exact Or.inl (by linarith)
    have hFx : Fdist g (-x) = 0 := by
      unfold Fdist
      rw [hnull]
      simp
    linarith [hx.2]
  have hSc : IsClosed S :=
    isClosed_Ici.inter
      (isClosed_le continuous_const ((Fdist_continuous g hg).comp continuous_neg))
  have hbdd : BddAbove S := ⟨b, hSb⟩
  have hne : S.Nonempty := ⟨0, h0S⟩
  have haS : sSup S ∈ S := hSc.csSup_mem hne hbdd
  have hab : sSup S ≤ b := csSup_le hne hSb
  refine ⟨sSup S, haS.1, hab.trans hb4, haS.2, ?_⟩
  ext E
  have hbs : bulkSet g κ L₀ L = {E | κ / 2 ≤ Fdist g (-|E|)} := by
    simp [bulkSet, not_lt.mpr hL]
  rw [hbs]
  simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · intro hE
    have hmem : |E| ∈ S := ⟨abs_nonneg E, hE⟩
    exact abs_le.mp (le_csSup hbdd hmem)
  · intro hE
    have hEa : |E| ≤ sSup S := abs_le.mpr hE
    exact haS.2.trans (Fdist_monotone g (neg_le_neg hEa))

/-- The energy window of Theorem 2.2 [uv:lem:lower-volume] around `[-a, a]`: if `F_g(-a) ≥ κ/2`
and `0 < η ≤ κ²/32`, then `F_g(-|E|) ≥ κ/4` on `[-a - η, a + η]`, by (1.13) [rd:eq:noatoms]. -/
theorem fdist_window (g κ a η : ℝ) (hg : 0 ≤ g) (hκ : 0 < κ ∧ κ < 1 / 2) (ha : 0 ≤ a)
    (hFa : κ / 2 ≤ Fdist g (-a)) (hη : 0 < η) (hηκ : η ≤ κ ^ 2 / 32) :
    ∀ E ∈ Set.Icc (-a - η) (a + η), κ / 4 ≤ Fdist g (-|E|) := by
  obtain ⟨hκ0, hκ1⟩ := hκ
  intro E hE
  have hP : IsProbabilityMeasure (nuDyson g) := (nuDyson_spec g hg).1
  have hEabs : |E| ≤ a + η := abs_le.mpr ⟨by linarith [hE.1], hE.2⟩
  have hκ2 : κ ^ 2 ≤ 1 / 4 := by nlinarith
  have hη1 : η ≤ 1 := by nlinarith
  have hh : 0 < η / 2 := by positivity
  have hh2 : η / 2 ≤ 1 / 2 := by linarith
  have hIcc := nuDyson_Icc_le g hg (-a - η / 2) (η / 2) hh hh2
  have hsq : Real.sqrt (2 * (η / 2)) ≤ κ / 4 := by
    have h2 : 2 * (η / 2) = η := by ring
    rw [h2, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith
  have hsub : Set.Iic (-a) ⊆
      Set.Iic (-|E|) ∪ Set.Icc (-a - η / 2 - η / 2) (-a - η / 2 + η / 2) := by
    intro t ht
    simp only [Set.mem_Iic] at ht
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]
    by_cases hc : t ≤ -|E|
    · exact Or.inl hc
    · have hc := not_le.mp hc
      right
      constructor <;> linarith
  have hmeas : nuDyson g (Set.Iic (-a)) ≤
      nuDyson g (Set.Iic (-|E|)) + nuDyson g (Set.Icc (-a - η / 2 - η / 2) (-a - η / 2 + η / 2)) :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have hreal : Fdist g (-a) ≤
      Fdist g (-|E|) + (nuDyson g (Set.Icc (-a - η / 2 - η / 2) (-a - η / 2 + η / 2))).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hmeas
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h
    exact h
  linarith

end LSBA
