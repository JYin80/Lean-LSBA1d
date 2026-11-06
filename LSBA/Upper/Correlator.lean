import LSBA.Spectral.EigCorr

/-!
# Block correlators of the model

The block correlator `𝒬_{ab}(J) = Σ_{λ_k ∈ J} ‖ψ_{k,a}‖ ‖ψ_{k,b}‖` of the proof of
Lemma 8.1(i) [uva:thm:upper-audit], the coordinate bound `𝒬_{ab}(J) ≤ Σ_{x ∈ 𝓘_a, y ∈ 𝓘_b}
Q_{xy}(J)`, and integrability of `Q_{xy}(J)` and `𝒬_{ab}(J)` for the model (1.3) [eq:model].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The block correlator `𝒬_{ab}(J) = Σ_{λ_k ∈ J} ‖ψ_{k,a}‖ ‖ψ_{k,b}‖` (proof of
Lemma 8.1(i) [uva:thm:upper-audit]). -/
def blockCorr {W L : ℕ} (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (J : Set ℝ) (a b : Fin L) :
    ℝ :=
  if hA : A.IsHermitian then
    ∑ k, if hA.eigenvalues k ∈ J then
      Real.sqrt (∑ α, ‖hA.eigenvectorBasis k (a, α)‖ ^ 2) *
        Real.sqrt (∑ α, ‖hA.eigenvectorBasis k (b, α)‖ ^ 2) else 0
  else 0

/-- `𝒬_{ab}(J) ≤ Σ_{x ∈ 𝓘_a, y ∈ 𝓘_b} Q_{xy}(J)` (proof of Lemma 8.1(i)
[uva:thm:upper-audit]), for every Hermitian matrix and the same eigenvectors on both sides. -/
theorem blockCorr_le_sum_eigCorr {W L : ℕ} (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (J : Set ℝ) (a b : Fin L) :
    blockCorr A J a b ≤ ∑ α, ∑ β, eigCorr A J (a, α) (b, β) := by
  have hsq : ∀ v : Fin W → ℂ, Real.sqrt (∑ α, ‖v α‖ ^ 2) ≤ ∑ α, ‖v α‖ := fun v =>
    Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun _ _ => norm_nonneg _,
      Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _⟩
  unfold blockCorr eigCorr
  by_cases hA : A.IsHermitian
  · simp only [hA, ↓reduceDIte]
    have hcomm : ∀ F : Fin W → Fin W → Fin L × Fin W → ℝ,
        ∑ α, ∑ β, ∑ k, F α β k = ∑ k, ∑ α, ∑ β, F α β k := fun F =>
      (Finset.sum_congr rfl fun α _ => Finset.sum_comm).trans Finset.sum_comm
    rw [hcomm fun α β k => if hA.eigenvalues k ∈ J then
      ‖hA.eigenvectorBasis k (a, α)‖ * ‖hA.eigenvectorBasis k (b, β)‖ else 0]
    refine Finset.sum_le_sum fun k _ => ?_
    split_ifs with hk
    · rw [← Finset.sum_mul_sum]
      exact mul_le_mul (hsq _) (hsq _)
        (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    · simp
  · simp [hA]

/-- `0 ≤ 𝒬_{ab}(J) ≤ W`. -/
theorem blockCorr_nonneg_le {W L : ℕ} (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (J : Set ℝ) (a b : Fin L) : 0 ≤ blockCorr A J a b ∧ blockCorr A J a b ≤ W := by
  refine ⟨?_, ?_⟩
  · unfold blockCorr
    split_ifs with hA
    · exact Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
    · exact le_rfl
  · have hbridge : blockCorr A J a b = eigMassCorr A (univ.image fun α : Fin W => (a, α))
        (univ.image fun α : Fin W => (b, α)) J := by
      unfold blockCorr eigMassCorr
      split_ifs with hA
      · rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs with hk
        · rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => by positivity),
            Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2),
            Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2)]
        · rfl
      · rfl
    rw [hbridge]
    have h := eigMassCorr_le_sqrt_card A (univ.image fun α : Fin W => (a, α))
      (univ.image fun α : Fin W => (b, α)) J
    rwa [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), Finset.card_univ,
      Fintype.card_fin, Real.sqrt_mul_self (Nat.cast_nonneg _)] at h

/-- `Q_{xy}(J)` of the model (1.3) [eq:model] is integrable for measurable `J`. -/
theorem integrable_eigCorr_Hmat (g : ℝ) (W L : ℕ) {J : Set ℝ} (hJ : MeasurableSet J)
    (x y : Fin L × Fin W) : Integrable (fun ω => eigCorr (Hmat g W L ω) J x y) (μ W L) := by
  have hF : Measurable fun ω : Ω W L => ∑ k, if eigAt (Hmat g W L ω) k ∈ J then
      Real.sqrt (eigProfile (Hmat g W L ω) k x) * Real.sqrt (eigProfile (Hmat g W L ω) k y)
      else 0 := by
    refine Finset.measurable_sum _ fun k _ => Measurable.ite ?_ ?_ measurable_const
    · exact hJ.preimage (continuous_sortedEig_Hmat g W L _).measurable
    · exact (Real.continuous_sqrt.measurable.comp
        ((measurable_pi_apply x).comp (measurable_eigProfile_Hmat g W L k))).mul
        (Real.continuous_sqrt.measurable.comp
        ((measurable_pi_apply y).comp (measurable_eigProfile_Hmat g W L k)))
  refine Integrable.of_bound (C := 1) ?_ ?_
  · refine (hF.aemeasurable.congr ?_).aestronglyMeasurable
    filter_upwards [ae_injective_eigenvalues g W L] with ω hω
    exact (eigCorr_eq_sum_eigProfile (Hmat_isHermitian g W L ω) hω J x y).symm
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_of_nonneg (eigCorr_nonneg _ _ _ _)]
    exact eigCorr_le_one _ _ _ _

/-- `𝒬_{ab}(J)` of the model (1.3) [eq:model] is integrable for measurable `J`. -/
theorem integrable_blockCorr_Hmat (g : ℝ) (W L : ℕ) {J : Set ℝ} (hJ : MeasurableSet J)
    (a b : Fin L) : Integrable (fun ω => blockCorr (Hmat g W L ω) J a b) (μ W L) := by
  have hF : Measurable fun ω : Ω W L => ∑ k, if eigAt (Hmat g W L ω) k ∈ J then
      Real.sqrt (∑ α, eigProfile (Hmat g W L ω) k (a, α)) *
        Real.sqrt (∑ β, eigProfile (Hmat g W L ω) k (b, β)) else 0 := by
    refine Finset.measurable_sum _ fun k _ => Measurable.ite ?_ ?_ measurable_const
    · exact hJ.preimage (continuous_sortedEig_Hmat g W L _).measurable
    · exact (Real.continuous_sqrt.measurable.comp
        (Finset.measurable_sum _ fun α _ =>
          (measurable_pi_apply (a, α)).comp (measurable_eigProfile_Hmat g W L k))).mul
        (Real.continuous_sqrt.measurable.comp
        (Finset.measurable_sum _ fun β _ =>
          (measurable_pi_apply (b, β)).comp (measurable_eigProfile_Hmat g W L k)))
  refine Integrable.of_bound (C := (W : ℝ)) ?_ ?_
  · refine (hF.aemeasurable.congr ?_).aestronglyMeasurable
    filter_upwards [ae_injective_eigenvalues g W L] with ω hω
    have hA := Hmat_isHermitian g W L ω
    have hev : ∀ k, hA.eigenvalues k = eigAt (Hmat g W L ω) k := fun k =>
      eigenvalues_eq_sortedEig hA k
    have hp : ∀ k i, eigProfile (Hmat g W L ω) k i = ‖hA.eigenvectorBasis k i‖ ^ 2 := by
      intro k i
      rw [norm_sq_eigenvectorBasis_eq_adjugate hA hω]
      simp only [eigProfile, hev]
    unfold blockCorr
    simp only [hA, ↓reduceDIte]
    refine (Finset.sum_congr rfl fun k _ => ?_).symm
    simp only [hev, hp]
  · refine Filter.Eventually.of_forall fun ω => ?_
    have h := blockCorr_nonneg_le (Hmat g W L ω) J a b
    rw [Real.norm_of_nonneg h.1]
    exact h.2

end LSBA
