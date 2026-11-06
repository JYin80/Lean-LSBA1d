import LSBA.Spectral.ProfileCount

/-!
# Two-sided counts

The count `B₊` of the proof of the upper bound of Theorem 1.4 [thm:main] (eigenvalues in `J` that
are multiple, or simple with `ℓ > r`) and the two-sided good count (simple, `r ≤ ℓ ≤ R`), beside
`badCount` and `goodCount`; the covering inequality behind (3.12) [uv:eq:sampling]; monotonicity;
a.e.-measurability and integrability for the model (1.3) [eq:model].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `B₊` of the proof of the upper bound in Theorem 1.4 [thm:main], before (3.11)
[uv:eq:upper-count]: eigenvalues in `J` that are multiple, or simple with `r < ℓ`. -/
def badCountUp (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (J : Set ℝ) (r : ℝ) :
    ℕ :=
  if hA : A.IsHermitian then
    #(univ.filter fun k => hA.eigenvalues k ∈ J ∧
      (2 ≤ mult hA.eigenvalues k ∨
        r < ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ)
          : ℝ)))
  else 0

/-- Two-sided good count: simple eigenvalues in `J` with `r ≤ ℓ ≤ R`. -/
def goodCountTwoSided (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (J : Set ℝ)
    (r R : ℝ) : ℕ :=
  if hA : A.IsHermitian then
    #(univ.filter fun k => hA.eigenvalues k ∈ J ∧ mult hA.eigenvalues k = 1 ∧
      r ≤ ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ)
        : ℝ) ∧
      ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ) : ℝ)
        ≤ R)
  else 0

/-- Every eigenvalue in `J` is two-sided good, or counted by `B₋` or by `B₊`. -/
theorem countIn_le_goodTwoSided_add (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (J : Set ℝ) (r R : ℝ) :
    countIn A J ≤ goodCountTwoSided W L A J r R + badCount W L A J r + badCountUp W L A J R := by
  by_cases hA : A.IsHermitian
  · simp only [countIn, goodCountTwoSided, badCount, badCountUp, hA, ↓reduceDIte]
    have hsub : (univ.filter fun k => hA.eigenvalues k ∈ J) ⊆
        ((univ.filter fun k => hA.eigenvalues k ∈ J ∧ mult hA.eigenvalues k = 1 ∧
          r ≤ ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ)
            : ℝ) ∧
          ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ) : ℝ)
            ≤ R) ∪
        (univ.filter fun k => hA.eigenvalues k ∈ J ∧
          (2 ≤ mult hA.eigenvalues k ∨
            ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ)
              : ℝ) < r))) ∪
        (univ.filter fun k => hA.eigenvalues k ∈ J ∧
          (2 ≤ mult hA.eigenvalues k ∨
            R < ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ)
              : ℝ))) := by
      intro k hk
      have hkJ : hA.eigenvalues k ∈ J := (Finset.mem_filter.mp hk).2
      have hm : 1 ≤ mult hA.eigenvalues k := Finset.card_pos.mpr ⟨k, by simp⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h2 : 2 ≤ mult hA.eigenvalues k
      · exact Or.inl (Or.inr ⟨hkJ, Or.inl h2⟩)
      · have h1 : mult hA.eigenvalues k = 1 := by omega
        by_cases h3 : ((ellProf W L (projDiag hA.eigenvalues
            (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ) : ℝ) < r
        · exact Or.inl (Or.inr ⟨hkJ, Or.inr h3⟩)
        · by_cases h4 : R < ((ellProf W L (projDiag hA.eigenvalues
              (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ) : ℝ)
          · exact Or.inr ⟨hkJ, Or.inr h4⟩
          · exact Or.inl (Or.inl ⟨hkJ, h1, not_lt.mp h3, not_lt.mp h4⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  · simp [countIn, goodCountTwoSided, badCount, badCountUp, hA]

/-- The two-sided good count is at most the one-sided good count. -/
theorem goodCountTwoSided_le_goodCount (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (J : Set ℝ) (r R : ℝ) : goodCountTwoSided W L A J r R ≤ goodCount W L A J r := by
  by_cases hA : A.IsHermitian
  · simp only [goodCountTwoSided, goodCount, hA, ↓reduceDIte]
    exact Finset.card_le_card fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact ⟨hk.1, hk.2.1, hk.2.2.1⟩
  · simp [goodCountTwoSided, goodCount, hA]

/-- The two-sided good count grows when the window `[r, R]` grows. -/
theorem goodCountTwoSided_mono (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (J : Set ℝ) {r r' R R' : ℝ} (hr : r' ≤ r) (hR : R ≤ R') :
    goodCountTwoSided W L A J r R ≤ goodCountTwoSided W L A J r' R' := by
  by_cases hA : A.IsHermitian
  · simp only [goodCountTwoSided, hA, ↓reduceDIte]
    exact Finset.card_le_card fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact ⟨hk.1, hk.2.1, hr.trans hk.2.2.1, hk.2.2.2.trans hR⟩
  · simp [goodCountTwoSided, hA]

/-- `B₊` is monotone in the energy set and antitone in the length threshold. -/
theorem badCountUp_mono (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {J J' : Set ℝ}
    (hJ : J ⊆ J') {r r' : ℝ} (hr : r ≤ r') : badCountUp W L A J r' ≤ badCountUp W L A J' r := by
  by_cases hA : A.IsHermitian
  · simp only [badCountUp, hA, ↓reduceDIte]
    exact Finset.card_le_card fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact ⟨hJ hk.1, hk.2.imp_right fun h => lt_of_le_of_lt hr h⟩
  · simp [badCountUp, hA]

/-- On simple spectrum, `B₊` vanishes once the threshold reaches the volume `N = LW`. -/
theorem badCountUp_eq_zero_of_le {W L : ℕ} {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hA : A.IsHermitian) (hinj : Function.Injective hA.eigenvalues) (J : Set ℝ) {r : ℝ}
    (hr : ((L * W : ℕ) : ℝ) ≤ r) : badCountUp W L A J r = 0 := by
  simp only [badCountUp, hA, ↓reduceDIte]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _ hk
  have hm : mult hA.eigenvalues k = 1 := by
    unfold mult
    rw [Finset.card_eq_one]
    exact ⟨k, by ext j; simp [hinj.eq_iff]⟩
  rcases hk.2 with h | h
  · omega
  · have hle : (ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℝ)
        ≤ ((L * W : ℕ) : ℝ) := by
      exact_mod_cast ellMass_le (L * W) _
    exact absurd (lt_of_le_of_lt hle (lt_of_le_of_lt hr h)) (lt_irrefl _)

theorem aemeasurable_badCountUp_Hmat (g : ℝ) (W L : ℕ) {J : Set ℝ} (hJ : MeasurableSet J)
    (r : ℝ) : AEMeasurable (fun ω => (badCountUp W L (Hmat g W L ω) J r : ℝ)) (μ W L) := by
  have hS : MeasurableSet {p : Fin L × Fin W → ℝ | r < ((ellProf W L p : ℕ) : ℝ)} :=
    measurableSet_lt measurable_const (measurable_from_nat.comp (measurable_ellProf W L))
  refine (aemeasurable_profCount_Hmat g W L hJ hS).congr ?_
  filter_upwards [ae_injective_eigenvalues g W L] with ω hω
  have hA := Hmat_isHermitian g W L ω
  have hm : ∀ k, mult hA.eigenvalues k = 1 := fun k => by
    unfold mult
    rw [Finset.card_eq_one]
    exact ⟨k, by ext j; simp [hω.eq_iff]⟩
  simp only [profCount, badCountUp, hA, ↓reduceDIte]
  congr 2
  refine Finset.filter_congr fun k _ => ?_
  have h2 : ¬ 2 ≤ mult hA.eigenvalues k := by rw [hm k]; omega
  simp [h2]

theorem integrable_badCountUp_Hmat (g : ℝ) (W L : ℕ) {J : Set ℝ} (hJ : MeasurableSet J)
    (r : ℝ) : Integrable (fun ω => (badCountUp W L (Hmat g W L ω) J r : ℝ)) (μ W L) := by
  have hb : ∀ A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ,
      ((badCountUp W L A J r : ℕ) : ℝ) ≤ ((L * W : ℕ) : ℝ) := fun A => by
    by_cases hA : A.IsHermitian
    · simp only [badCountUp, hA, ↓reduceDIte]
      have := Finset.card_filter_le (univ : Finset (Fin L × Fin W)) fun k => hA.eigenvalues k ∈ J ∧
        (2 ≤ mult hA.eigenvalues k ∨
          r < ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ)
            : ℝ))
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
      exact_mod_cast this
    · simp only [badCountUp, hA, ↓reduceDIte, Nat.cast_zero]
      exact Nat.cast_nonneg _
  refine Integrable.of_bound (aemeasurable_badCountUp_Hmat g W L hJ r).aestronglyMeasurable
    ((L * W : ℕ) : ℝ) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact hb _

theorem aemeasurable_goodCountTwoSided_Hmat (g : ℝ) (W L : ℕ) {J : Set ℝ}
    (hJ : MeasurableSet J) (r R : ℝ) :
    AEMeasurable (fun ω => (goodCountTwoSided W L (Hmat g W L ω) J r R : ℝ)) (μ W L) := by
  have hl : Measurable fun p : Fin L × Fin W → ℝ => ((ellProf W L p : ℕ) : ℝ) :=
    measurable_from_nat.comp (measurable_ellProf W L)
  have hS : MeasurableSet {p : Fin L × Fin W → ℝ |
      r ≤ ((ellProf W L p : ℕ) : ℝ) ∧ ((ellProf W L p : ℕ) : ℝ) ≤ R} :=
    (measurableSet_le measurable_const hl).inter (measurableSet_le hl measurable_const)
  refine (aemeasurable_profCount_Hmat g W L hJ hS).congr ?_
  filter_upwards [ae_injective_eigenvalues g W L] with ω hω
  have hA := Hmat_isHermitian g W L ω
  have hm : ∀ k, mult hA.eigenvalues k = 1 := fun k => by
    unfold mult
    rw [Finset.card_eq_one]
    exact ⟨k, by ext j; simp [hω.eq_iff]⟩
  simp only [profCount, goodCountTwoSided, hA, ↓reduceDIte]
  congr 2
  refine Finset.filter_congr fun k _ => ?_
  simp [hm k]

end LSBA
