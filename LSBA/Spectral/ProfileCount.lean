import LSBA.Spectral.Measurability

/-!
# Profile counts

The number of eigenvalues in an energy set `J` whose spectral-projection profile lies in a set `S`,
and its a.e.-measurability for the model (1.3) [eq:model]. The count `B₋` of (2.12)
[uv:eq:lower-regions-output], the count `B₊` and the two-sided good count of the proof of (3.11)
[uv:eq:upper-count], and the count of (3.6) [eq:averaged-tail] are instances.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Number of eigenvalues in `J` whose spectral-projection profile lies in `S`. -/
def profCount (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (J : Set ℝ)
    (S : Set (Fin L × Fin W → ℝ)) : ℕ :=
  if hA : A.IsHermitian then
    #(univ.filter fun k => hA.eigenvalues k ∈ J ∧
      projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k ∈ S)
  else 0

/-- For measurable `J` and `S`, the profile count of the model (1.3) [eq:model] is
a.e.-measurable. -/
theorem aemeasurable_profCount_Hmat (g : ℝ) (W L : ℕ) {J : Set ℝ} (hJ : MeasurableSet J)
    {S : Set (Fin L × Fin W → ℝ)} (hS : MeasurableSet S) :
    AEMeasurable (fun ω => (profCount W L (Hmat g W L ω) J S : ℝ)) (μ W L) := by
  have hF : Measurable fun ω : Ω W L => ∑ k, if eigAt (Hmat g W L ω) k ∈ J ∧
      eigProfile (Hmat g W L ω) k ∈ S then (1 : ℝ) else 0 := by
    refine Finset.measurable_sum _ fun k _ => Measurable.ite ?_ measurable_const measurable_const
    have h1 : MeasurableSet {ω : Ω W L | eigAt (Hmat g W L ω) k ∈ J} :=
      hJ.preimage (continuous_sortedEig_Hmat g W L _).measurable
    have h2 : MeasurableSet {ω : Ω W L | eigProfile (Hmat g W L ω) k ∈ S} :=
      hS.preimage (measurable_eigProfile_Hmat g W L k)
    exact h1.inter h2
  refine hF.aemeasurable.congr ?_
  filter_upwards [ae_injective_eigenvalues g W L] with ω hω
  have hA := Hmat_isHermitian g W L ω
  have hev : ∀ k, hA.eigenvalues k = eigAt (Hmat g W L ω) k := fun k =>
    eigenvalues_eq_sortedEig hA k
  have hmult : ∀ k, mult hA.eigenvalues k = 1 := by
    intro k
    unfold mult
    rw [Finset.card_eq_one]
    exact ⟨k, by ext j; simp [hω.eq_iff]⟩
  have hp : ∀ k, projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k =
      eigProfile (Hmat g W L ω) k := by
    intro k
    funext i
    rw [projDiag_of_mult_eq_one _ _ (hmult k), norm_sq_eigenvectorBasis_eq_adjugate hA hω, hev]
    simp only [eigProfile, hev]
  symm
  simp only [profCount, hA, ↓reduceDIte, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hp, hev]

end LSBA
