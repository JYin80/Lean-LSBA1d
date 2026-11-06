import LSBA.Dyson.Distribution

/-!
# Lemma 1.2 [da:lem:distribution]: spectral windows of the limiting distribution

Lemma 1.2 [da:lem:distribution] for the measures `ν_g` and the distribution functions `F_g` of
(1.9) [eq:dyson] and (1.10) [eq:distribution], for every `g ≥ 0`: (i) `ν_g` is supported in
`[-4, 4]`; (ii) the measures are uniformly atomless; (iii) the bulk-window implication (1.14)
[eq:bulk-bridge].
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- Lemma 1.2 [da:lem:distribution]: (i) `ν_g([-4, 4]ᶜ) = 0`; (ii) for every `ε > 0` there is
`h₀ > 0` such that every interval of length at most `2h₀` has `ν_g`-mass at most `ε`, for all
`g ≥ 0`; (iii) for every `κ ∈ (0, 1/2)` there are `κ₀ ∈ (0, 2)` and `0 < c_κ < C_κ` such that
`g ∈ [0, c_κ] ∪ [C_κ, ∞)` and `F_g(-|E|) ≥ κ` imply `|E| ≤ 2 - κ₀`, (1.14) [eq:bulk-bridge]. -/
theorem distribution_lemma :
    (∀ g : ℝ, 0 ≤ g → nuDyson g (Set.Icc (-4) 4)ᶜ = 0) ∧
    (∀ ε > 0, ∃ h₀ > 0, ∀ h ∈ Set.Ioc 0 h₀, ∀ g : ℝ, 0 ≤ g → ∀ x : ℝ,
      (nuDyson g (Set.Icc (x - h) (x + h))).toReal ≤ ε) ∧
    (∀ κ : ℝ, 0 < κ ∧ κ < 1 / 2 → ∃ κ₀ c C : ℝ, 0 < κ₀ ∧ κ₀ < 2 ∧ 0 < c ∧ c < C ∧
      ∀ g : ℝ, 0 ≤ g → (g ≤ c ∨ C ≤ g) → ∀ E : ℝ, κ ≤ Fdist g (-|E|) → |E| ≤ 2 - κ₀) := by
  refine ⟨?_, nuDyson_noatoms_uniform, ?_⟩
  · intro g hg
    refine le_antisymm ?_ zero_le
    refine (measure_mono ?_).trans (nuDyson_compl_support g hg).le
    refine Set.compl_subset_compl.mpr (Set.Icc_subset_Icc ?_ ?_)
    · linarith [support_bound_le_four g hg]
    · exact support_bound_le_four g hg
  · intro κ hκ
    obtain ⟨hκ0, hκ1⟩ := hκ
    have hκ2 : κ ^ 2 < 1 / 4 := by nlinarith
    have hκ2' : 0 < κ ^ 2 := by positivity
    have h32 : 32 < 8 / κ ^ 2 := by
      rw [lt_div_iff₀ hκ2']; linarith
    refine ⟨κ ^ 2 / 4, κ ^ 2 / 4, 8 / κ ^ 2, by positivity, by linarith, by positivity,
      by linarith, ?_⟩
    intro g hg hgc E hE
    exact bulk_window_explicit κ ⟨hκ0, hκ1⟩ g hg hgc E hE

end LSBA
