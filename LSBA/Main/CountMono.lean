import LSBA.Spectral.Measurability
import LSBA.Model.Scales

/-!
# Monotonicity of the counts

Monotonicity of `badCount` and `goodCount` in the energy set and the length threshold, the
trivial bounds, integrability of the bad count of the model, and the monotonicity of the
threshold `W^{-τ} ℓ*` in `τ` used for `τ ≥ 1` in Theorem 1.4 [thm:main].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The bad count is monotone in the energy set and in the length threshold. -/
theorem badCount_mono (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {J J' : Set ℝ}
    (hJ : J ⊆ J') {r r' : ℝ} (hr : r ≤ r') : badCount W L A J r ≤ badCount W L A J' r' := by
  by_cases hA : A.IsHermitian
  · simp only [badCount, hA, ↓reduceDIte]
    refine Finset.card_le_card fun k hk => ?_
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, hJ hk.2.1, hk.2.2.imp_right fun h => lt_of_lt_of_le h hr⟩
  · simp [badCount, hA]

/-- The good count is antitone in the length threshold. -/
theorem goodCount_anti (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (J : Set ℝ)
    {r r' : ℝ} (hr : r ≤ r') : goodCount W L A J r' ≤ goodCount W L A J r := by
  by_cases hA : A.IsHermitian
  · simp only [goodCount, hA, ↓reduceDIte]
    refine Finset.card_le_card fun k hk => ?_
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.1, hk.2.2.1, le_trans hr hk.2.2.2⟩
  · simp [goodCount, hA]

theorem badCount_le_card (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (J : Set ℝ)
    (r : ℝ) : badCount W L A J r ≤ L * W := by
  by_cases hA : A.IsHermitian
  · simp only [badCount, hA, ↓reduceDIte]
    calc _ ≤ (Finset.univ : Finset (Fin L × Fin W)).card := Finset.card_filter_le _ _
      _ = L * W := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  · simp [badCount, hA]

theorem countIn_univ {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : countIn A Set.univ = Fintype.card n := by
  simp [countIn, hA]

theorem integrable_badCount_Hmat (g : ℝ) (W L : ℕ) {J : Set ℝ} (hJ : MeasurableSet J) (r : ℝ) :
    Integrable (fun ω => (badCount W L (Hmat g W L ω) J r : ℝ)) (μ W L) := by
  refine Integrable.of_bound (aemeasurable_badCount_Hmat g W L hJ r).aestronglyMeasurable
    ((L : ℝ) * W) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast badCount_le_card W L (Hmat g W L ω) J r

/-- The threshold `W^{-τ} ℓ_{W,g,L}` of (1.17) [eq:main] decreases in `τ` for `W ≥ 1`. -/
theorem rpow_neg_mul_ellStar_le {W : ℕ} (hW : 1 ≤ W) (L : ℕ) (g : ℝ) {τ τ' : ℝ} (h : τ' ≤ τ) :
    (W : ℝ) ^ (-τ) * ellStar W L g ≤ (W : ℝ) ^ (-τ') * ellStar W L g := by
  have h1 : (W : ℝ) ^ (-τ) ≤ (W : ℝ) ^ (-τ') :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hW) (by linarith)
  have h2 : 0 ≤ ellStar W L g :=
    le_min (by positivity) (le_max_of_le_left (Nat.cast_nonneg _))
  exact mul_le_mul_of_nonneg_right h1 h2

end LSBA
