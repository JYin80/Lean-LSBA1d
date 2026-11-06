import LSBA.Upper.Interface
import LSBA.Upper.AssemblyBounds

/-!
# The upper count (3.11) [uv:eq:upper-count]

(3.11) [uv:eq:upper-count] from Theorems 3.1 [thm:strong-upper]–3.4 [thm:large-upper], stated as the
propositions of
`LSBA.Upper.Interface`, as in the proof of the upper bound of Theorem 1.4 [thm:main].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- One branch of the proof of (3.11) [uv:eq:upper-count]: if the energy set (1.16)
[eq:bulk-sampling] lies in `J'`, `W(2⌈R⌉+1) ≤ r` and (3.6) [eq:averaged-tail] holds at `(J', R)`
with `A = 1`, then the averaged `B₊` at threshold `r` is at most `W^{-D}`. -/
private lemma assembly_branch {W L : ℕ} {g κ : ℝ} {L₀ : ℕ} {J' : Set ℝ} {R r D : ℝ}
    (hJ' : MeasurableSet J') (hsub : bulkSet g κ L₀ L ⊆ J') (hR : 0 ≤ R)
    (hr : (W : ℝ) * (2 * ⌈R⌉ + 1) ≤ r) (hW : 2 ≤ W)
    (hT : AveragedTailBound W L g J' R 1 D) :
    ((W : ℝ) * L)⁻¹ * ∫ ω, (badCountUp W L (Hmat g W L ω) (bulkSet g κ L₀ L) r : ℝ) ∂(μ W L)
      ≤ (W : ℝ) ^ (-D) := by
  have ha : (W : ℝ) ^ (-(1 : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ (by norm_num) (by exact_mod_cast hW)
  have hle : ∫ ω, (badCountUp W L (Hmat g W L ω) (bulkSet g κ L₀ L) r : ℝ) ∂(μ W L) ≤
      ∫ ω, (tailCount W L (Hmat g W L ω) J' R 1 : ℝ) ∂(μ W L) := by
    refine integral_mono_ae
      (integrable_badCountUp_Hmat g W L (measurableSet_bulkSet g κ L₀ L) r)
      (integrable_tailCount_Hmat g W L hJ' R 1) ?_
    filter_upwards [ae_injective_eigenvalues g W L] with ω hω
    exact Nat.cast_le.2
      ((badCountUp_le_tailCount W L _ (Hmat_isHermitian g W L ω) hω _ hR hr ha).trans
        (tailCount_mono W L _ hsub le_rfl 1))
  exact (mul_le_mul_of_nonneg_left hle (inv_nonneg.2 (by positivity))).trans hT

/-- For large `W`: `W ≥ 2`, `L₀ ≤ W^τ`, `W^{-τ/8} ≤ κ²/16` and `32/κ² ≤ W^{τ/4}`. -/
private lemma assembly_eventually {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (L₀ : ℕ) :
    ∀ᶠ W : ℕ in atTop, 2 ≤ W ∧ (L₀ : ℝ) ≤ (W : ℝ) ^ τ ∧ (W : ℝ) ^ (-(τ / 8)) ≤ κ ^ 2 / 16 ∧
      32 / κ ^ 2 ≤ (W : ℝ) ^ (τ / 4) := by
  have h1 : ∀ᶠ W : ℕ in atTop, 2 ≤ W := eventually_ge_atTop 2
  have h2 : ∀ᶠ W : ℕ in atTop, (L₀ : ℝ) ≤ (W : ℝ) ^ τ :=
    ((tendsto_rpow_atTop hτ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have h3 : ∀ᶠ W : ℕ in atTop, (W : ℝ) ^ (-(τ / 8)) ≤ κ ^ 2 / 16 :=
    ((tendsto_rpow_neg_atTop (by linarith : 0 < τ / 8)).comp
      tendsto_natCast_atTop_atTop).eventually (ge_mem_nhds (by positivity))
  have h4 : ∀ᶠ W : ℕ in atTop, 32 / κ ^ 2 ≤ (W : ℝ) ^ (τ / 4) :=
    ((tendsto_rpow_atTop (by linarith : 0 < τ / 4)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [h1, h2, h3, h4] with W a b c d using ⟨a, b, c, d⟩

/-- (3.11) [uv:eq:upper-count] from Theorems 3.1 [thm:strong-upper], 3.2
[thm:sharp-small-upper], 3.3 [thm:compact-upper] and 3.4 [thm:large-upper], as in the proof of
the upper bound of Theorem 1.4 [thm:main]. -/
theorem upperCount_of_averagedTail (h11 : StrongUpper) (h12 : SharpSmallUpper)
    (h13 : CompactUpper) (h14 : LargeUpper) (κ D τ : ℝ) (hκ : 0 < κ ∧ κ < 1 / 2) (hD : 0 < D)
    (hτ : 0 < τ ∧ τ < 1) (L₀ : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
      AEMeasurable (fun ω => (badCountUp W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ τ * ellStar W L g) : ℝ)) (μ W L) ∧
      ((W : ℝ) * L)⁻¹ * ∫ ω, (badCountUp W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ τ * ellStar W L g) : ℝ) ∂(μ W L) ≤ (W : ℝ) ^ (-D) := by
  obtain ⟨hκ0, hκ1⟩ := hκ
  obtain ⟨hτ0, hτ1⟩ := hτ
  have hκ2 : 0 < κ ^ 2 / 16 := by positivity
  obtain ⟨cs, hcs0, hcs1, h11'⟩ := h11
  obtain ⟨W₁, hW₁⟩ := h11' 1 D one_pos hD
  obtain ⟨W₂, hW₂⟩ := h12 (τ / 8) cs 1 D (τ / 2) (κ ^ 2 / 16) (by linarith) (by linarith) hcs0
    one_pos hD (by linarith) hκ2 (by nlinarith)
  obtain ⟨W₃, hW₃⟩ := h13 (τ / 4) 4 1 D (by linarith) (by norm_num) one_pos hD
  obtain ⟨W₄, hW₄⟩ := h14 (κ ^ 2 / 16) 1 D (τ / 4) hκ2 (by nlinarith) one_pos hD (by linarith)
  have hev := (eventually_ge_atTop W₁).and ((eventually_ge_atTop W₂).and
    ((eventually_ge_atTop W₃).and ((eventually_ge_atTop W₄).and
    ((upperRadius_strong hτ0).and ((upperRadius_sharpSmall hτ0).and
    ((upperRadius_compact ⟨hτ0, hτ1⟩).and ((upperRadius_large hτ0).and
    (assembly_eventually hκ0 hτ0 L₀))))))))
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.1 hev
  refine ⟨W₀, fun W hW L hL g hg => ⟨aemeasurable_badCountUp_Hmat g W L
    (measurableSet_bulkSet g κ L₀ L) _, ?_⟩⟩
  obtain ⟨hW1, hW2, hW3, hW4, hrs, hrss, hrc, hrl, hW2', hL₀, hκ8, hκ4⟩ := hW₀ W hW
  have hWpos : (0 : ℝ) < W := by
    have : (2 : ℝ) ≤ W := by exact_mod_cast hW2'
    linarith
  have hW1r : (1 : ℝ) ≤ W := by
    have : (2 : ℝ) ≤ W := by exact_mod_cast hW2'
    linarith
  have hW1n : 1 ≤ W := by omega
  by_cases hcap : (L : ℝ) ≤ (W : ℝ) ^ τ * max 1 ((W : ℝ) * g ^ 2)
  · -- cap case: `B₊ = 0` almost surely
    have hvol := mul_le_rpow_mul_ellStar hW1n hτ0.le hcap
    have hz : ∀ᵐ ω ∂(μ W L), (badCountUp W L (Hmat g W L ω) (bulkSet g κ L₀ L)
        ((W : ℝ) ^ τ * ellStar W L g) : ℝ) = 0 := by
      filter_upwards [ae_injective_eigenvalues g W L] with ω hω
      rw [badCountUp_eq_zero_of_le (Hmat_isHermitian g W L ω) hω _ hvol]
      simp
    rw [integral_eq_zero_of_ae hz, mul_zero]
    positivity
  · push Not at hcap
    have hEll : ellStar W L g = ellScale W g := ellStar_eq_ellScale_of_lt hW1n hτ0.le hcap
    have hM1 : (1 : ℝ) ≤ max 1 ((W : ℝ) * g ^ 2) := le_max_left _ _
    have hP0 : (0 : ℝ) ≤ (W : ℝ) ^ τ := Real.rpow_nonneg hWpos.le _
    have hLL : L₀ ≤ L := by
      have : (L₀ : ℝ) ≤ L := by nlinarith
      exact_mod_cast this
    have hκ16 : (W : ℝ) ^ (-(τ / 8)) ≤ κ ^ 2 / 16 := hκ8
    by_cases h1 : g ≤ cs * (W : ℝ) ^ (-(1 / 2 : ℝ))
    · -- Theorem 3.1 [thm:strong-upper]
      refine assembly_branch (J' := Set.univ) (R := (⌈Real.log W ^ 2⌉₊ : ℝ))
        MeasurableSet.univ (Set.subset_univ _) (Nat.cast_nonneg _) ?_ hW2' (hW₁ W hW1 L hL g hg h1)
      rw [hEll]
      exact hrs g
    by_cases h2 : g ≤ (W : ℝ) ^ (-(τ / 8))
    · -- Theorem 3.2 [thm:sharp-small-upper]
      refine assembly_branch (J' := Set.Icc (-2 + κ ^ 2 / 16) (2 - κ ^ 2 / 16))
        (R := (W : ℝ) ^ (τ / 2) * max 1 ((W : ℝ) * g ^ 2)) measurableSet_Icc
        (bulkSet_subset_Icc_of_window hg ⟨hκ0, hκ1⟩ hLL (Or.inl (h2.trans hκ16)))
        (by positivity) ?_ hW2' (hW₂ W hW2 L hL g (not_le.mp h1).le h2)
      rw [hEll]
      exact hrss g
    by_cases h3 : g ≤ (W : ℝ) ^ (τ / 4)
    · -- Theorem 3.3 [thm:compact-upper]
      have h2' : (W : ℝ) ^ (-(τ / 8)) ≤ g := (not_le.mp h2).le
      have hgB : (W : ℝ) ^ (-(τ / 4)) ≤ g :=
        (Real.rpow_le_rpow_of_exponent_le hW1r (by linarith)).trans h2'
      refine assembly_branch (J' := Set.Icc (-4) 4)
        (R := (W : ℝ) * max (g ^ 2)⁻¹ (g ^ 4) * Real.log W ^ 2) measurableSet_Icc
        (bulkSet_subset_Icc_four hg hκ0 hLL) (by positivity) ?_ hW2' (hW₃ W hW3 L hL g hgB h3)
      rw [hEll]
      exact hrc g h2' h3
    · -- Theorem 3.4 [thm:large-upper]
      have h3' : (W : ℝ) ^ (τ / 4) ≤ g := (not_le.mp h3).le
      have hg1 : 1 ≤ g :=
        (Real.one_le_rpow hW1r (by linarith)).trans h3'
      refine assembly_branch (J' := Set.Icc (-2 + κ ^ 2 / 16) (2 - κ ^ 2 / 16))
        (R := (W : ℝ) * g ^ 2 * Real.log W ^ 2) measurableSet_Icc
        (bulkSet_subset_Icc_of_window hg ⟨hκ0, hκ1⟩ hLL (Or.inr (hκ4.trans h3')))
        (by positivity) ?_ hW2' (hW₄ W hW4 L hL g h3')
      rw [hEll]
      exact hrl g hg1

end LSBA
