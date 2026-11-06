import LSBA.Upper.Operator
import LSBA.Transfer.GraphChart
import LSBA.Analysis.RotCorrection
import LSBA.Gauss.HermCoord

/-!
# The data of the small-coupling field

Section 9.1 [su:sec:construction] for a batch of `q` inputs. The input `V_i` of the paper is
block `i - 1` of `Ω W q`. The prepared chart: after the four preparation blocks,
`T_4 ⋯ T_1 S Y = ran (I; -g R_4)` and `T_4 ⋯ T_1 S U = {(x, -g R_4 x) : v_4* x = 0}` (9.1)
[su:eq:graph-input]. The graph coordinates `R_j = (V_j - E - g² R_{j-1})⁻¹` and normals
`v_j = R_j ⋯ R_5 v_4` of (9.2) [su:eq:transported-normal], the normalization (9.8)
[su:eq:generator-normalization], the correction `L` of (9.9) [us:eq:L], the field `X` of (9.10)
[us:eq:physical], and the Hermiticity of its components (Lemma 9.2 [su:lem:field-geometry]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The input blocks of `Ω W q` as a sequence: `blockSeq W q ω k = V_{k+1}` for `k < q`, and `0`
from `k = q` on (the inputs of `batchMat`). -/
def blockSeq (W q : ℕ) (ω : Ω W q) : ℕ → Matrix (Fin W) (Fin W) ℂ :=
  fun k => if h : k < q then gueBlock W q ω ⟨k, h⟩ else 0

/-- The preparation product `T_4 T_3 T_2 T_1 S` of Section 9.1 [su:sec:construction]. -/
def prepMat (W : ℕ) (g E : ℝ) (q : ℕ) (ω : Ω W q) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  transferProd g ((max 1 g * E / g : ℝ) : ℂ) (blockSeq W q ω) 4 * freeConj W 0

/-- The prepared chart (9.1) [su:eq:graph-input] at `j = 4`: `R_4` is Hermitian, `v_4 ≠ 0`,
`T_4 ⋯ T_1 S Y = ran (I; -g R_4)` and `T_4 ⋯ T_1 S U = {(x, -g R_4 x) : v_4* x = 0}`. -/
def IsPrepChart (W : ℕ) (g E : ℝ) (q : ℕ) (x : IsoFlag W) (ω : Ω W q)
    (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) : Prop :=
  R.IsHermitian ∧ v ≠ 0 ∧
  LinearMap.range (prepMat W g E q ω * x.1.2).mulVecLin =
    LinearMap.range (graphFrame g R).mulVecLin ∧
  LinearMap.range (prepMat W g E q ω * x.1.1).mulVecLin =
    LinearMap.range
      (graphFrame g R * (1 - (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v))).mulVecLin

/-- The graph coordinates `R_j = (V_j - E - g² R_{j-1})⁻¹` of (9.2) [su:eq:transported-normal]
for `j ≥ 5`, started at `R_4 = R`; `chartR … j = R` for `j ≤ 4`. -/
def chartR (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) :
    ℕ → Matrix (Fin W) (Fin W) ℂ
  | 0 => R
  | j + 1 => if j < 4 then R else
      (blockSeq W q ω j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω j)⁻¹

/-- The product `R_{[j,5]} = R_j ⋯ R_5` for `j ≥ 5`; `1` for `j ≤ 4`. -/
def chartProd (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) :
    ℕ → Matrix (Fin W) (Fin W) ℂ
  | 0 => 1
  | j + 1 => if j < 4 then 1 else chartR W g E q R ω (j + 1) * chartProd W g E q R ω j

/-- The normalization (9.8) [su:eq:generator-normalization]:
`Re(v_{q-1}* R_{[q-1,5]} K v_4) = ‖v_{q-1}‖²` with `v_{q-1} = R_{[q-1,5]} v_4`. -/
def IsGenNormalized (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ)
    (K : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) : Prop :=
  (star (chartProd W g E q R ω (q - 1) *ᵥ v) ⬝ᵥ (chartProd W g E q R ω (q - 1) *ᵥ (K *ᵥ v))).re =
    ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2

/-- The correction `L` of (9.9) [us:eq:L] for `v_corr = R_{[q-1,5]} K v_4 - v_{q-1}`. -/
def smallCorr (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ)
    (K : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) : Matrix (Fin W) (Fin W) ℂ :=
  rotCorr (chartProd W g E q R ω (q - 1) *ᵥ v)
    (chartProd W g E q R ω (q - 1) *ᵥ (K *ᵥ v) - chartProd W g E q R ω (q - 1) *ᵥ v)

/-- The field `X` of (9.10) [us:eq:physical] at the sample `ω` (block `i` of `Ω W q` is the input
`V_{i+1}`): `0` on the preparation blocks, `[K, V_5 - g² R_4]`, `[K, V_i]` for `6 ≤ i ≤ q - 1`, and
`[K, V_q] - [L, V_q - g² R_{q-1}]`. -/
def smallField (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ)
    (K : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) : Fin q → Matrix (Fin W) (Fin W) ℂ := fun i =>
  if (i : ℕ) < 4 then 0
  else if (i : ℕ) = 4 then
    K * (gueBlock W q ω i - ((g : ℂ) ^ 2) • R) - (gueBlock W q ω i - ((g : ℂ) ^ 2) • R) * K
  else if (i : ℕ) + 1 < q then K * gueBlock W q ω i - gueBlock W q ω i * K
  else K * gueBlock W q ω i - gueBlock W q ω i * K -
    (smallCorr W g E q R v K ω *
        (gueBlock W q ω i - ((g : ℂ) ^ 2) • chartR W g E q R ω (q - 1)) -
      (gueBlock W q ω i - ((g : ℂ) ^ 2) • chartR W g E q R ω (q - 1)) *
        smallCorr W g E q R v K ω)

/-- Lemma 9.2 [su:lem:field-geometry], first assertion: every component of `X` is Hermitian, by
(9.8) [su:eq:generator-normalization] and (9.12) [su:eq:correction-identities]. -/
theorem smallField_isHermitian {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) {v : Fin W → ℂ} {K : Matrix (Fin W) (Fin W) ℂ} (hK : Kᴴ = -K)
    (ω : Ω W q) (hn : IsGenNormalized W g E q R v K ω) (i : Fin q) :
    (smallField W g E q R v K ω i).IsHermitian := by
  have hB : ∀ k, (blockSeq W q ω k).IsHermitian := by
    intro k
    unfold blockSeq
    split_ifs
    · exact gueBlock_isHermitian W q ω _
    · exact Matrix.isHermitian_zero
  have hs : ∀ (r : ℝ) (A : Matrix (Fin W) (Fin W) ℂ), A.IsHermitian →
      (((r : ℂ)) • A).IsHermitian := by
    intro r A hA
    unfold Matrix.IsHermitian at hA ⊢
    rw [Matrix.conjTranspose_smul, hA]
    simp
  have hs2 : ∀ A : Matrix (Fin W) (Fin W) ℂ, A.IsHermitian →
      (((g : ℂ) ^ 2) • A).IsHermitian := by
    intro A hA
    have := hs (g ^ 2) A hA
    simpa using this
  have hE : ((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
    exact hs E 1 Matrix.isHermitian_one
  have hC : ∀ j, (chartR W g E q R ω j).IsHermitian := by
    intro j
    induction j with
    | zero => simpa [chartR] using hR
    | succ j ih =>
      simp only [chartR]
      split_ifs
      · exact hR
      · exact ((hB j).sub hE |>.sub (hs2 _ ih)).inv
  have hcomm : ∀ S H : Matrix (Fin W) (Fin W) ℂ, Sᴴ = -S → H.IsHermitian →
      (S * H - H * S).IsHermitian := by
    intro S H hS hH
    unfold Matrix.IsHermitian at hH ⊢
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS, hH]
    simp only [Matrix.mul_neg, Matrix.neg_mul]
    abel
  have hL : (smallCorr W g E q R v K ω)ᴴ = -smallCorr W g E q R v K ω := by
    apply (rotCorr_spec _).1
    set P := chartProd W g E q R ω (q - 1)
    have h1 : (star (P *ᵥ v) ⬝ᵥ (P *ᵥ (K *ᵥ v) - P *ᵥ v)).re = 0 := by
      rw [dotProduct_sub, Complex.sub_re]
      have h2 : star (P *ᵥ v) ⬝ᵥ (P *ᵥ v) = ((∑ i, ‖(P *ᵥ v) i‖ ^ 2 : ℝ) : ℂ) := by
        simp [dotProduct, Complex.conj_mul', Complex.ofReal_sum]
      rw [h2, Complex.ofReal_re]
      have hn' := hn
      unfold IsGenNormalized at hn'
      rw [hn']
      ring
    exact h1
  unfold smallField
  have hG : ∀ A : Matrix (Fin W) (Fin W) ℂ, A.IsHermitian →
      (gueBlock W q ω i - ((g : ℂ) ^ 2) • A).IsHermitian := fun A hA =>
    (gueBlock_isHermitian W q ω i).sub (hs2 A hA)
  split_ifs
  · exact Matrix.isHermitian_zero
  · exact hcomm K _ hK (hG R hR)
  · exact hcomm K _ hK (gueBlock_isHermitian W q ω i)
  · exact (hcomm K _ hK (gueBlock_isHermitian W q ω i)).sub (hcomm _ _ hL (hG _ (hC _)))

end LSBA
