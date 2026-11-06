import LSBA.Upper.Score
import LSBA.Upper.SmallPrefix
import LSBA.Upper.SmallScoreSmooth

/-!
# Lemma 9.4 [us:lem:score] at the preparation of a sample

In the proof of Lemma 8.12 [up:lem:small-contraction], at a sample `ω'` with `pre ω' = 1`,
Lemma 9.4 [us:lem:score] applies at the preparation `(R_4, v_4)` of `ω'` with `C_K = C`, when
`χ̂(R_4; ·; v_4)` is not identically zero; otherwise the cut field vanishes. Inserting the pointwise
bound (9.37) [su:eq:chosen-generator-cut-costs] of the source energy and the terminal correction
`W g⁴ ‖[χ L, R_{q-1}]‖²_HS ≤ 36 C⁴ W⁻¹ g⁴` (Section 9.3 [su:sec:generator-bounds]), at every
sample where `χ̂ ≠ 0`, bounds `𝔼 |δ_G(χ̂ X)|²` at that preparation by integrals of `χ̂`, `K̂` and
`∇_{v_4} χ̂` alone.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Lemma 9.4 [us:lem:score] at the preparation of a sample `ω'` with `pre ω' ≠ 0`, with (9.37)
[su:eq:chosen-generator-cut-costs] and the terminal correction (Section 9.3
[su:sec:generator-bounds]) inserted; the constants `C_s, c` depend only on the constant `C` of
Lemma 9.3 [su:lem:chosen-generator]. -/
theorem lintegral_gaussDiv_smallScore_le (C : ℝ) (hC : 0 < C) :
    ∃ Cs c : ℝ, 0 < Cs ∧ 0 < c ∧ ∀ (W q : ℕ) (g E σ M₀ : ℝ) (x : IsoFlag W)
      (Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ) (pre : Ω W q → ℝ)
      (Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ) (vf : Ω W q → Fin W → ℂ)
      (Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ)
      (χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ),
      1 ≤ W → 7 ≤ q → 0 < g → g ≤ 1 → 0 ≤ σ → 0 ≤ M₀ →
      ChosenGenerator W q g E x Pf C σ M₀ pre Rf vf Kh χh → ∀ ω' : Ω W q, pre ω' ≠ 0 →
      ∫⁻ ω, ‖gaussDiv (smallScoreField W g E q (Rf ω') (vf ω') (Kh (Rf ω')) (χh (Rf ω'))) ω‖ₑ
          ^ 2 ∂(μ W q) ≤
        ENNReal.ofReal Cs * ∫⁻ ω, ENNReal.ofReal
            (2 * χh (Rf ω') ω (vf ω') ^ 2 * C ^ 2 *
                (C * W * σ + 2 * W * hsSq (Kh (Rf ω') ω (vf ω'))) +
              2 * (∑ i, ‖(Pf (Rf ω') *ᵥ vf ω') i‖ ^ 2) * hsSq (Kh (Rf ω') ω (vf ω')) *
                tangGradSq (Pf (Rf ω')) (vf ω') (χh (Rf ω') ω)) ∂(μ W q) +
          ENNReal.ofReal (Cs * W * (1 + M₀ ^ 2)) *
            ∫⁻ ω, ENNReal.ofReal (χh (Rf ω') ω (vf ω') ^ 2 * hsSq (Kh (Rf ω') ω (vf ω')))
              ∂(μ W q) +
          ENNReal.ofReal (36 * C ^ 4 * (W : ℝ)⁻¹ * g ^ 4) +
          ENNReal.ofReal (Cs * W * M₀ * Real.exp (-c * W)) := by
  obtain ⟨Cs, c, hCs, hc, hbound⟩ := score_bound C
  refine ⟨Cs, c, hCs, hc, fun W q g E σ M₀ x Pf pre Rf vf Kh χh hW hq hg hg1 hσ hM₀ hG ω'
    hpre => ?_⟩
  by_cases hne : ∃ ω, χh (Rf ω') ω (vf ω') ≠ 0
  · -- some sample has `χ̂ ≠ 0`: Lemma 9.4 [us:lem:score] applies at the preparation
    have hD := scoreData_of_chosenGenerator hW hq hg hg1 hM₀ hG hpre hne
    have hb := hbound W q g E M₀ (Rf ω') (Pf (Rf ω')) (vf ω') (Kh (Rf ω')) (χh (Rf ω')) hD
    obtain ⟨-, -, -, -, -, -, hv, -⟩ := hD
    obtain ⟨-, -, -, -, -, -, -, -, -, hfam, -⟩ := id hG
    obtain ⟨hPh, hPP, -, hF⟩ := hfam ω' hpre
    have hGP : ∀ ω, χh (Rf ω') ω (vf ω') ≠ 0 →
        GenPoint W q g E (Pf (Rf ω')) (Rf ω') (vf ω') C M₀ σ (Kh (Rf ω') ω) ω :=
      fun ω hω => genPoint_of_chosenGenerator hG hpre hω
    have hsq : ∀ (r : ℝ) (A : Matrix (Fin W) (Fin W) ℂ), hsSq (r • A) = r ^ 2 * hsSq A := by
      intro r A
      unfold hsSq
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [mul_pow, sq_abs]
    refine hb.trans (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) le_rfl)
    · -- (9.37) [su:eq:chosen-generator-cut-costs] pointwise
      refine mul_le_mul' le_rfl (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_)
      exact srcEnergy_cut_le hPh hPP hF hv fun hω => hGP ω hω
    · refine mul_le_mul' le_rfl (lintegral_mono fun ω => le_of_eq ?_)
      rw [hsq]
    · -- the terminal correction, pointwise, then integrated against the probability measure
      have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
      have hB0 : 0 ≤ 36 * C ^ 4 * (W : ℝ)⁻¹ * g ^ 4 := by positivity
      refine (le_of_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm).trans ?_
      refine (lintegral_mono fun ω => ?_).trans (le_of_eq (by simp) :
        ∫⁻ _ : Ω W q, ENNReal.ofReal (36 * C ^ 4 * (W : ℝ)⁻¹ * g ^ 4) ∂(μ W q) ≤ _)
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      by_cases hχ : χh (Rf ω') ω (vf ω') = 0
      · simpa [hχ, hsSq] using hB0
      · exact terminal_corr_le hW hC.le (hF.2.1 ω (vf ω')) (hGP ω hχ)
  · -- `χ̂(R_4; ·; v_4) ≡ 0`: the cut field vanishes
    have hne' : ∀ ω, χh (Rf ω') ω (vf ω') = 0 := fun ω => by_contra fun h => hne ⟨ω, h⟩
    have hz : smallScoreField W g E q (Rf ω') (vf ω') (Kh (Rf ω')) (χh (Rf ω')) =
        fun _ => 0 := by
      funext η
      simp [smallScoreField, hne' η]
    rw [hz]
    simp [gaussDiv, lineDeriv]

end LSBA
