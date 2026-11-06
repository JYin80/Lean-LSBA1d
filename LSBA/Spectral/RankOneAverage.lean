import LSBA.Spectral.RankOne
import LSBA.Spectral.RankOneCross
import LSBA.Spectral.LineArea

/-!
# Spectral averaging for a rank-one diagonal perturbation

For Hermitian `K` and measurable `φ ≥ 0`,
`∫ ⟨e_x, φ(K + v e_x e_x^*) e_x⟩ dv ≤ ∫ φ(E) dE`: the spectral integral representation of
the diagonal spectral measure in [ASFH, proof of Theorem A.1], integrated over the diagonal
entry `v` (the two sides are equal).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Spectral averaging: `∫ Σ_k |ψ_k(x)|² φ(λ_k) dv ≤ ∫ φ(E) dE` for the eigenpairs of
`K + v e_x e_x^*` and measurable `φ ≥ 0`. -/
theorem lintegral_eigMassSum_rankOnePert_le {K : Matrix n n ℂ} (hK : K.IsHermitian) (x : n)
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ v, eigMassSum (rankOnePert K x v) {x} φ ≤ ∫⁻ E, φ E := by
  simp_rw [rankOnePert_eq_add_smul_coordProj]
  refine (lintegral_eigMassSum_line_le hK {x} one_pos (G := fun E _ => φ E)
    (hφ.comp measurable_fst)).trans ?_
  rw [inv_one, ENNReal.ofReal_one, one_mul]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_tsum_crossCount_rankOne_le hK x] with E hE
  calc ∑' ℓ : ℤ, crossCount (fun u => K + ((1 * u : ℝ) : ℂ) • coordProj ({x} : Finset n)) E
        (Set.Icc (ℓ : ℝ) (ℓ + 1)) * (⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), φ E)
      ≤ ∑' ℓ : ℤ, crossCount (fun u => K + ((1 * u : ℝ) : ℂ) • coordProj ({x} : Finset n)) E
        (Set.Icc (ℓ : ℝ) (ℓ + 1)) * φ E :=
        ENNReal.tsum_le_tsum fun ℓ => by
          gcongr
          exact iSup₂_le fun _ _ => le_rfl
    _ = (∑' ℓ : ℤ, crossCount (fun u => K + ((1 * u : ℝ) : ℂ) • coordProj ({x} : Finset n)) E
        (Set.Icc (ℓ : ℝ) (ℓ + 1))) * φ E := ENNReal.tsum_mul_right
    _ ≤ 1 * φ E := by gcongr
    _ = φ E := one_mul _

end LSBA
