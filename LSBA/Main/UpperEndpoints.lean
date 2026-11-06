import LSBA.Main.Endpoints
import LSBA.Upper.Assembly
import LSBA.Main.EndpointAlgebraTwoSided
import LSBA.Upper.StrongUpper
import LSBA.Upper.SharpSmall
import LSBA.Upper.CompactUpper
import LSBA.Upper.LargeUpper

/-!
# The endpoints of the upper bound

(U1) the upper count (3.11) [uv:eq:upper-count], from Theorems 3.1 [thm:strong-upper], 3.2
[thm:sharp-small-upper], 3.3 [thm:compact-upper] and 3.4 [thm:large-upper]; (U2) Theorem 1.4
[thm:main], (1.17) [eq:main]; (U3) Corollary 1.5 [cor:simultaneous], (1.18) [eq:simultaneous].
(U2) and (U3) combine (U1) with the count form of the lower bound and Lemma 1.3
[lem:rough-density].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- (U1) the upper count (3.11) [uv:eq:upper-count]. -/
theorem upper_count_endpoint (κ D τ : ℝ) (hκ : 0 < κ ∧ κ < 1 / 2) (hD : 0 < D)
    (hτ : 0 < τ ∧ τ < 1) (L₀ : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
      AEMeasurable (fun ω => (badCountUp W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ τ * ellStar W L g) : ℝ)) (μ W L) ∧
      ((W : ℝ) * L)⁻¹ * ∫ ω, (badCountUp W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ τ * ellStar W L g) : ℝ) ∂(μ W L) ≤ (W : ℝ) ^ (-D) := by
  exact upperCount_of_averagedTail strong_upper sharp_small_upper compact_upper large_upper
    κ D τ hκ hD hτ L₀

/-- (U2) Theorem 1.4 [thm:main], (1.17) [eq:main]; `x / 0 = 0` is real division. -/
theorem main_ratio_endpoint (κ : ℝ) (hκ : 0 < κ ∧ κ < 1 / 2) :
    ∃ L₀ : ℕ, ∀ L₁ : ℕ, L₀ ≤ L₁ → ∀ D τ : ℝ, 0 < D → 0 < τ →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        1 - (W : ℝ) ^ (-D) ≤
          ∫ ω, (goodCountTwoSided W L (Hmat g W L ω) (bulkSet g κ L₁ L)
                  ((W : ℝ) ^ (-τ) * ellStar W L g) ((W : ℝ) ^ τ * ellStar W L g) : ℝ) /
                (countIn (Hmat g W L ω) (bulkSet g κ L₁ L) : ℝ) ∂(μ W L) := by
  exact ratio_of_counts_rough κ hκ
    (fun D τ hD hτ L₀ => lower_count_endpoint κ D τ hκ hD hτ L₀)
    (fun D τ hD hτ L₀ => upper_count_endpoint κ D τ hκ hD hτ L₀)
    (rough_density_endpoint (κ / 2) (by linarith [hκ.1]))

/-- (U3) Corollary 1.5 [cor:simultaneous], (1.18) [eq:simultaneous], every fixed threshold
`L₀`. -/
theorem simultaneous_endpoint (BL D τ κ : ℝ) (hBL : 0 < BL) (hD : 0 < D) (hτ : 0 < τ)
    (hκ : 0 < κ ∧ κ < 1 / 2) (L₀ : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → (L : ℝ) ≤ (W : ℝ) ^ BL → ∀ g : ℝ, 0 ≤ g →
      μ W L {ω | 0 < badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ (-τ) * ellStar W L g) +
        badCountUp W L (Hmat g W L ω) (bulkSet g κ L₀ L) ((W : ℝ) ^ τ * ellStar W L g)} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  exact simultaneous_of_counts BL D τ κ hBL hD hτ L₀
    (fun D' τ' hD' hτ' => lower_count_endpoint κ D' τ' hκ hD' hτ' L₀)
    (fun D' τ' hD' hτ' => upper_count_endpoint κ D' τ' hκ hD' hτ' L₀)

/-- (U2) implies (E2): the two-sided good count is at most the one-sided one, and the larger
ratio is integrable (values in `[0, 1]`). -/
example (κ : ℝ) (hκ : 0 < κ ∧ κ < 1 / 2) :
    ∃ L₀ : ℕ, ∀ L₁ : ℕ, L₀ ≤ L₁ → ∀ D τ : ℝ, 0 < D → 0 < τ →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        1 - (W : ℝ) ^ (-D) ≤
          ∫ ω, (goodCount W L (Hmat g W L ω) (bulkSet g κ L₁ L)
                  ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ) /
                (countIn (Hmat g W L ω) (bulkSet g κ L₁ L) : ℝ) ∂(μ W L) := by
  obtain ⟨L₀, h⟩ := main_ratio_endpoint κ hκ
  refine ⟨L₀, fun L₁ hL₁ D τ hD hτ => ?_⟩
  obtain ⟨W₀, hW⟩ := h L₁ hL₁ D τ hD hτ
  refine ⟨W₀, fun W hW' L hL g hg => (hW W hW' L hL g hg).trans ?_⟩
  have hJ := measurableSet_bulkSet g κ L₁ L
  refine integral_mono_of_nonneg (Eventually.of_forall fun ω => by positivity) ?_
    (Eventually.of_forall fun ω => ?_)
  · have hR : AEMeasurable (fun ω => (goodCount W L (Hmat g W L ω) (bulkSet g κ L₁ L)
        ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ) / (countIn (Hmat g W L ω) (bulkSet g κ L₁ L) : ℝ))
        (μ W L) :=
      (aemeasurable_goodCount_Hmat g W L hJ _).div
        (measurable_from_nat.comp (measurable_countIn_Hmat g W L hJ)).aemeasurable
    refine Integrable.of_bound hR.aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
    rw [← goodCount_add_badCount W L (Hmat g W L ω) _ _]
    exact_mod_cast Nat.le_add_right _ _
  · exact div_le_div_of_nonneg_right
      (by exact_mod_cast goodCountTwoSided_le_goodCount W L _ _ _ _) (Nat.cast_nonneg _)

/-- (U3) implies (E3): the bad event of (E3) lies in that of (U3). -/
example (BL D τ κ : ℝ) (hBL : 0 < BL) (hD : 0 < D) (hτ : 0 < τ) (hκ : 0 < κ ∧ κ < 1 / 2)
    (L₀ : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → (L : ℝ) ≤ (W : ℝ) ^ BL → ∀ g : ℝ, 0 ≤ g →
      μ W L {ω | 0 < badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ (-τ) * ellStar W L g)} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  obtain ⟨W₀, h⟩ := simultaneous_endpoint BL D τ κ hBL hD hτ hκ L₀
  refine ⟨W₀, fun W hW L hL hLW g hg => le_trans (measure_mono ?_) (h W hW L hL hLW g hg)⟩
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  omega

/-- Witness of (U1): `κ = 1/4`, `D = 1`, `τ = 1/2`, `L₀ = 5`, at `L = W` and `g = W⁻¹`
(range of Theorem 3.1 [thm:strong-upper], outside the cap case `L ≤ W^{1/2}`). -/
example : ∃ W : ℕ, 5 ≤ W ∧
    ((W : ℝ) * W)⁻¹ * ∫ ω, (badCountUp W W (Hmat (W : ℝ)⁻¹ W W ω)
      (bulkSet (W : ℝ)⁻¹ (1 / 4) 5 W) ((W : ℝ) ^ (1 / 2 : ℝ) * ellStar W W (W : ℝ)⁻¹) : ℝ)
      ∂(μ W W) ≤ (W : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨W₀, hW₀⟩ := upper_count_endpoint (1 / 4) 1 (1 / 2) ⟨by norm_num, by norm_num⟩
    (by norm_num) ⟨by norm_num, by norm_num⟩ 5
  refine ⟨max W₀ 5, le_max_right _ _, ?_⟩
  exact (hW₀ _ (le_max_left _ _) (max W₀ 5) (le_trans (by norm_num) (le_max_right _ _))
    _ (by positivity)).2

/-- Witness of (U1) at a long cycle: `κ = 1/4`, `D = 1`, `τ = 1/2`, `L₀ = 5`, `L = W ^ 3` and
`g = W⁻¹`. Here `ℓ_{W,g,L} = W`, so the radius `W^{1/2} ℓ_{W,g,L}` equals `W ^ (3/2)`, which is
well below `L = W ^ 3`. -/
example : ∃ W : ℕ, 5 ≤ W ∧
    ((W : ℝ) * (W ^ 3 : ℕ))⁻¹ * ∫ ω, (badCountUp W (W ^ 3) (Hmat (W : ℝ)⁻¹ W (W ^ 3) ω)
      (bulkSet (W : ℝ)⁻¹ (1 / 4) 5 (W ^ 3))
      ((W : ℝ) ^ (1 / 2 : ℝ) * ellStar W (W ^ 3) (W : ℝ)⁻¹) : ℝ)
      ∂(μ W (W ^ 3)) ≤ (W : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨W₀, hW₀⟩ := upper_count_endpoint (1 / 4) 1 (1 / 2) ⟨by norm_num, by norm_num⟩
    (by norm_num) ⟨by norm_num, by norm_num⟩ 5
  refine ⟨max W₀ 5, le_max_right _ _, ?_⟩
  have h5 : 5 ≤ max W₀ 5 := le_max_right _ _
  exact (hW₀ _ (le_max_left _ _) ((max W₀ 5) ^ 3)
    (le_trans (by norm_num) (le_trans h5 (Nat.le_self_pow (by norm_num) _))) _
    (by positivity)).2

end LSBA
