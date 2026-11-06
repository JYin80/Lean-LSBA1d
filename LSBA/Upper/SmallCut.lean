import LSBA.Upper.FieldGeometry
import LSBA.Upper.ChosenGenerator

/-!
# The cutoff and the field of Lemma 8.12 [up:lem:small-contraction]

The cutoff `χ = pre · χ̂(R_4; ·; v_4)` and the field `X` of (9.10) [us:eq:physical], in standard
coordinates, built from the data of Lemma 9.3 [su:lem:chosen-generator]: the preparation
indicator, the prepared chart `R_4`, the source `v_4` and the generator `K = K̂(R_4; ·; v_4)`
(proof of Lemma 8.12 [up:lem:small-contraction]). The cutoff is measurable with values in
`[0, 1]` and mean at least `½`, and Lemma 9.2 [su:lem:field-geometry] with Lemma 9.3
[su:lem:chosen-generator](i) gives (8.34) [up:eq:angular-geometry] with `K_out = K - L` wherever
`χ ≠ 0`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The cutoff `χ = pre · χ̂(R_4; ·; v_4)` of Lemma 8.12 [up:lem:small-contraction], with the
preparation indicator, chart and source of the sample. -/
def smallCut {W q : ℕ} (pre : Ω W q → ℝ) (Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ)
    (vf : Ω W q → Fin W → ℂ) (χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ) :
    Ω W q → ℝ :=
  fun ω => pre ω * χh (Rf ω) ω (vf ω)

/-- The field `X` of (9.10) [us:eq:physical] of Lemma 8.12 [up:lem:small-contraction] in standard
coordinates, built from the chart `R_4`, the source `v_4` and `K = K̂(R_4; ω; v_4)` of the
sample. -/
def smallVec (W : ℕ) (g E : ℝ) (q : ℕ) (Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ)
    (vf : Ω W q → Fin W → ℂ)
    (Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ) :
    Ω W q → Ω W q :=
  fun ω => hermCoord W q (smallField W g E q (Rf ω) (vf ω) (Kh (Rf ω) ω (vf ω)) ω)

/-- The cutoff of Lemma 8.12 [up:lem:small-contraction] is measurable, takes values in `[0, 1]`
and has mean at least `½`. -/
theorem smallCut_basic {W q : ℕ} {g E C σ M₀ : ℝ} {x : IsoFlag W}
    {Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} {pre : Ω W q → ℝ}
    {Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ} {vf : Ω W q → Fin W → ℂ}
    {Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ}
    (hG : ChosenGenerator W q g E x Pf C σ M₀ pre Rf vf Kh χh) :
    Measurable (smallCut pre Rf vf χh) ∧
      (∀ ω, 0 ≤ smallCut pre Rf vf χh ω ∧ smallCut pre Rf vf χh ω ≤ 1) ∧
      (1 / 2 : ℝ) ≤ ∫ ω, smallCut pre Rf vf χh ω ∂(μ W q) := by
  obtain ⟨hpre, hpm, hRm, hvm, -, -, -, -, hχm, hfam, -, hmean, -, -⟩ := hG
  refine ⟨hpm.mul (hχm.comp (hRm.prodMk (measurable_id.prodMk hvm))), fun ω => ?_, hmean⟩
  rcases hpre ω with h | h
  · simp [smallCut, h]
  · have hb := (hfam ω (by rw [h]; exact one_ne_zero)).2.2.2.2.1 ω (vf ω)
    simpa [smallCut, h] using hb

/-- (8.34) [up:eq:angular-geometry] for the field of Lemma 8.12 [up:lem:small-contraction] wherever
the cutoff is nonzero, with `K_out = K - L` (Lemma 9.2 [su:lem:field-geometry] and Lemma 9.3
[su:lem:chosen-generator](i)). -/
theorem smallCut_geom {W q : ℕ} {g E C σ M₀ : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hq : 7 ≤ q)
    {x : IsoFlag W} {Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ}
    {pre : Ω W q → ℝ} {Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ} {vf : Ω W q → Fin W → ℂ}
    {Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ}
    (hG : ChosenGenerator W q g E x Pf C σ M₀ pre Rf vf Kh χh) (ω : Ω W q)
    (hω : smallCut pre Rf vf χh ω ≠ 0) :
    ∃ K : Matrix (Fin W) (Fin W) ℂ, Kᴴ = -K ∧
      FlagFieldGeom W g E q x (smallVec W g E q Rf vf Kh) ω K := by
  obtain ⟨-, -, -, -, -, hprep, -, -, -, -, hpt, -, -, -⟩ := hG
  obtain ⟨-, hK, -, hn, hRu, -⟩ := hpt ω hω
  have h := field_geometry hg hg1 hq x ω (hprep ω (left_ne_zero_of_mul hω)) hRu hK hn
    (Y := smallVec W g E q Rf vf Kh) rfl
  exact ⟨_, h.1, h.2⟩

end LSBA
