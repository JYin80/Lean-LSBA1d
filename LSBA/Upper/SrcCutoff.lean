import LSBA.Upper.ActiveChain
import LSBA.Upper.CutLevels
import LSBA.Upper.RegularState
import LSBA.Analysis.StepCutoff
import LSBA.Spectral.RankTrace
import LSBA.Spectral.SpecProjSmooth

/-!
# The cutoff of Section 9.4.4 [su:sec:cutoff-estimates]

Section 9.4.4 [su:sec:cutoff-estimates], at a fixed chart `R_4 = R`, projection `P` and levels.
The matrix cutoff imposes, with nested margins: regularity (9.3) [us:eq:regular] of
`R_5, …, R_{q-2}` through `‖R_j‖²_HS ≤ W⁶` and the rank surrogate of `#{|g² r| > g}`; existence and
size of `R_{q-1}`, of the right-cavity inverses and of `R̃`; the active-chain bound (9.66)
[su:eq:active-chain-inverse]; a gap of the singular values of `A` at `t` (the invariant open set
on which the retained projection is smooth); the rank restriction of Section 9.4.1
[su:sec:retained-geometry] through the rank surrogate of `A* A`; the compatibility cut (9.83)
[su:eq:compatibility-cutoff] through `Tr ((Q (1 - P) Q)^k)`; and bounds on the active blocks. The
source cutoff in `v̂` is the product of `‖v̂‖² ≤ 2 W^{20} ‖P v̂‖²`, the overlap cuts (9.79)
[su:eq:cuts], (9.80) [nc:eq:sourcecuts] and the output cut `‖v_{q-1}‖ ≥ v_min` of (9.67)
[su:eq:output-cutoff-scale]; each factor is a smooth step of a ratio homogeneous of degree zero
in `v̂`. On the topological support the closed conditions `CutSupp` hold; on `CutPlat` the cutoff
equals one.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The regularity cutoff of a state `Y`: `‖Y‖²_HS ≤ W⁶` and
`rankSurr (1/g) (Y* Y) ≤ W g^{1/2}`, with nested margins. -/
def regCut (W : ℕ) (g : ℝ) (Y : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  normCut ((W : ℝ) ^ 6 / 2) Y * stepDown (2 * rankSurr g⁻¹ (Yᴴ * Y) / (W * Real.sqrt g))

/-- The matrix cutoff of Section 9.4.4 [su:sec:cutoff-estimates]: a function of the active blocks
`4, …, q - 2` at the chart `R`, the projection `P` and the levels `c`. -/
def matCut (W : ℕ) (g E : ℝ) (q : ℕ) (R P : Matrix (Fin W) (Fin W) ℂ) (c : CutLevels)
    (ω : Ω W q) : ℝ :=
  (∏ j ∈ Finset.Icc 5 (q - 2), regCut W g (chartR W g E q R ω j)) *
  normCut ((W : ℝ) ^ 6 / 2) (chartR W g E q R ω (q - 1)) *
  (∏ m ∈ Finset.range (q - 6), normCut ((W : ℝ) ^ 6 / 2) (cavR W g E q ω m)) *
  normCut ((W : ℝ) ^ 6 / 2) (cavRes W g E q R ω) *
  normCut ((W : ℝ) ^ 6 / 2) (activeMat W g E q R ω)⁻¹ *
  normCut c.Lgap ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) -
    ((c.t ^ 2 : ℝ) : ℂ) • 1)⁻¹ *
  stepDown (rankSurr c.t ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) / c.Lrk) *
  stepDown (2 * 8 ^ c.kP * ((retProj W g E q R c.t ω * (1 - P) * retProj W g E q R c.t ω) ^
    c.kP).trace.re) *
  stepDown (hsSq (blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R) / (W : ℝ) ^ 8) *
  ∏ i ∈ Finset.Icc 5 (q - 2), stepDown (hsSq (blockSeq W q ω i) / (W : ℝ) ^ 8)

/-- The source cutoff of Section 9.4.4 [su:sec:cutoff-estimates] at the source `v̂`: the factor
`‖v̂‖² ≤ 2 W^{20} ‖P v̂‖²`, the overlap cuts of (9.79) [su:eq:cuts] and (9.80)
[nc:eq:sourcecuts], and the output cut of (9.67) [su:eq:output-cutoff-scale]. -/
def srcCutV (W : ℕ) (g E : ℝ) (q : ℕ) (R P : Matrix (Fin W) (Fin W) ℂ) (c : CutLevels)
    (ω : Ω W q) (v : Fin W → ℂ) : ℝ :=
  stepUp (2 * (W : ℝ) ^ 20 * (∑ i, ‖(P *ᵥ v) i‖ ^ 2) / ∑ i, ‖v i‖ ^ 2) *
  stepDown ((∑ i, ‖(retProj W g E q R c.t ω *ᵥ v) i‖ ^ 2) /
    (c.Lov * ∑ i, ‖(P *ᵥ v) i‖ ^ 2)) *
  stepDown (16 * (∑ i, ‖(retProj W g E q R c.t ω *ᵥ (P *ᵥ v)) i‖ ^ 2) /
    ∑ i, ‖(P *ᵥ v) i‖ ^ 2) *
  stepUp ((∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2) /
    (c.kOut ^ 2 * ∑ i, ‖(P *ᵥ v) i‖ ^ 2))

/-- The cutoff `χ̂(R; ω; v̂)` of Section 9.4.4 [su:sec:cutoff-estimates]. -/
def srcCut (W : ℕ) (g E : ℝ) (q : ℕ) (R P : Matrix (Fin W) (Fin W) ℂ) (c : CutLevels)
    (ω : Ω W q) (v : Fin W → ℂ) : ℝ :=
  matCut W g E q R P c ω * srcCutV W g E q R P c ω v

/-- The closed conditions on the topological support of the cutoff. -/
def CutSupp (W : ℕ) (g E : ℝ) (q : ℕ) (R P : Matrix (Fin W) (Fin W) ℂ) (c : CutLevels)
    (ω : Ω W q) (v : Fin W → ℂ) : Prop :=
  (∀ j, 5 ≤ j → j ≤ q - 2 → IsUnit (chartR W g E q R ω j) ∧
    hsSq (chartR W g E q R ω j) ≤ (W : ℝ) ^ 6 ∧
    rankSurr g⁻¹ ((chartR W g E q R ω j)ᴴ * chartR W g E q R ω j) ≤ W * Real.sqrt g) ∧
  (IsUnit (chartR W g E q R ω (q - 1)) ∧ hsSq (chartR W g E q R ω (q - 1)) ≤ (W : ℝ) ^ 6) ∧
  (∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m) ∧ hsSq (cavR W g E q ω m) ≤ (W : ℝ) ^ 6) ∧
  (IsUnit (cavRes W g E q R ω) ∧ hsSq (cavRes W g E q R ω) ≤ (W : ℝ) ^ 6) ∧
  (IsUnit (activeMat W g E q R ω) ∧ hsSq (activeMat W g E q R ω)⁻¹ ≤ (W : ℝ) ^ 6) ∧
  (IsUnit ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) - ((c.t ^ 2 : ℝ) : ℂ) • 1) ∧
    hsSq ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) -
      ((c.t ^ 2 : ℝ) : ℂ) • 1)⁻¹ ≤ 2 * c.Lgap) ∧
  rankSurr c.t ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) ≤ 2 * c.Lrk ∧
  8 ^ c.kP * ((retProj W g E q R c.t ω * (1 - P) * retProj W g E q R c.t ω) ^
    c.kP).trace.re ≤ 1 ∧
  hsSq (blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R) ≤ 2 * (W : ℝ) ^ 8 ∧
  (∀ i, 5 ≤ i → i ≤ q - 2 → hsSq (blockSeq W q ω i) ≤ 2 * (W : ℝ) ^ 8) ∧
  ∑ i, ‖v i‖ ^ 2 ≤ 2 * (W : ℝ) ^ 20 * ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ∧
  ∑ i, ‖(retProj W g E q R c.t ω *ᵥ v) i‖ ^ 2 ≤ 2 * c.Lov * ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ∧
  8 * ∑ i, ‖(retProj W g E q R c.t ω *ᵥ (P *ᵥ v)) i‖ ^ 2 ≤ ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ∧
  c.kOut ^ 2 * ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ≤ ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2

/-- The plateau of the chain part of the matrix cutoff: the regularity, inverse and block
conditions with the inner margins. -/
def ChainPlat (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) : Prop :=
  (∀ j, 5 ≤ j → j ≤ q - 2 → IsUnit (chartR W g E q R ω j) ∧
    hsSq (chartR W g E q R ω j) ≤ (W : ℝ) ^ 6 / 2 ∧
    2 * rankSurr g⁻¹ ((chartR W g E q R ω j)ᴴ * chartR W g E q R ω j) ≤ W * Real.sqrt g) ∧
  (IsUnit (chartR W g E q R ω (q - 1)) ∧ hsSq (chartR W g E q R ω (q - 1)) ≤ (W : ℝ) ^ 6 / 2) ∧
  (∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m) ∧ hsSq (cavR W g E q ω m) ≤ (W : ℝ) ^ 6 / 2) ∧
  (IsUnit (cavRes W g E q R ω) ∧ hsSq (cavRes W g E q R ω) ≤ (W : ℝ) ^ 6 / 2) ∧
  hsSq (blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R) ≤ (W : ℝ) ^ 8 ∧
  ∀ i, 5 ≤ i → i ≤ q - 2 → hsSq (blockSeq W q ω i) ≤ (W : ℝ) ^ 8

/-- The plateau of the cutoff: `ChainPlat`, the active-chain, gap, rank and compatibility
conditions with the inner margins, and the source conditions with the inner margins. -/
def CutPlat (W : ℕ) (g E : ℝ) (q : ℕ) (R P : Matrix (Fin W) (Fin W) ℂ) (c : CutLevels)
    (ω : Ω W q) (v : Fin W → ℂ) : Prop :=
  ChainPlat W g E q R ω ∧
  (IsUnit (activeMat W g E q R ω) ∧ hsSq (activeMat W g E q R ω)⁻¹ ≤ (W : ℝ) ^ 6 / 2) ∧
  (IsUnit ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) - ((c.t ^ 2 : ℝ) : ℂ) • 1) ∧
    hsSq ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) -
      ((c.t ^ 2 : ℝ) : ℂ) • 1)⁻¹ ≤ c.Lgap) ∧
  rankSurr c.t ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) ≤ c.Lrk ∧
  2 * 8 ^ c.kP * ((retProj W g E q R c.t ω * (1 - P) * retProj W g E q R c.t ω) ^
    c.kP).trace.re ≤ 1 ∧
  P *ᵥ v ≠ 0 ∧ ∑ i, ‖v i‖ ^ 2 ≤ (W : ℝ) ^ 20 * ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ∧
  ∑ i, ‖(retProj W g E q R c.t ω *ᵥ v) i‖ ^ 2 ≤ c.Lov * ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ∧
  16 * ∑ i, ‖(retProj W g E q R c.t ω *ᵥ (P *ᵥ v)) i‖ ^ 2 ≤ ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ∧
  2 * c.kOut ^ 2 * ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ≤ ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2

/-! ### Auxiliary lemmas -/

/-- The smooth steps: `stepDown s ≠ 0` forces `s < 2` and `stepUp s ≠ 0` forces `1 < s`; both take
values in `[0, 1]`; `stepDown s = 1` for `s ≤ 1` and `stepUp s = 1` for `2 ≤ s`. -/
private lemma SrcCutoff_step :
    (∀ s, stepDown s ≠ 0 → s < 2) ∧ (∀ s, stepUp s ≠ 0 → 1 < s) ∧
    (∀ s, 0 ≤ stepDown s ∧ stepDown s ≤ 1) ∧ (∀ s, 0 ≤ stepUp s ∧ stepUp s ≤ 1) ∧
    (∀ s, s ≤ 1 → stepDown s = 1) ∧ ∀ s, 2 ≤ s → stepUp s = 1 := by
  obtain ⟨-, -, -, -, hb, h1, h2, -⟩ := step_spec
  refine ⟨fun s hs => ?_, fun s hs => ?_, fun s => ⟨(hb s).1, (hb s).2.1⟩,
    fun s => ⟨(hb s).2.2.1, (hb s).2.2.2⟩, fun s hs => (h1 s hs).1, fun s hs => (h2 s hs).2⟩
  · by_contra h
    exact hs (h2 s (not_lt.1 h)).1
  · by_contra h
    exact hs (h1 s (not_lt.1 h)).2

/-- `normCut L Y` takes values in `[0, 1]`. -/
private lemma SrcCutoff_normCut_mem {n : Type*} [Fintype n] [DecidableEq n] (L : ℝ)
    (Y : Matrix n n ℂ) : 0 ≤ normCut L Y ∧ normCut L Y ≤ 1 := by
  unfold normCut
  split_ifs
  · exact SrcCutoff_step.2.2.1 _
  · exact ⟨le_rfl, zero_le_one⟩

/-- `normCut L Y = 1` for an invertible `Y` with `‖Y‖²_HS ≤ L`. -/
private lemma SrcCutoff_normCut_eq_one {n : Type*} [Fintype n] [DecidableEq n] {L : ℝ}
    (hL : 0 < L) {Y : Matrix n n ℂ} (hY : IsUnit Y) (h : hsSq Y ≤ L) : normCut L Y = 1 := by
  unfold normCut
  simp only [hY, ↓reduceIte]
  exact SrcCutoff_step.2.2.2.2.1 _ ((div_le_one hL).2 h)

/-- Products of numbers in `[0, 1]` lie in `[0, 1]`. -/
private lemma SrcCutoff_mem_mul {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    0 ≤ a * b ∧ a * b ≤ 1 :=
  ⟨mul_nonneg ha.1 hb.1, (mul_le_of_le_one_left hb.1 ha.2).trans hb.2⟩

/-- Finite products of numbers in `[0, 1]` lie in `[0, 1]`. -/
private lemma SrcCutoff_mem_prod {s : Finset ℕ} {f : ℕ → ℝ} (h : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    0 ≤ ∏ i ∈ s, f i ∧ ∏ i ∈ s, f i ≤ 1 :=
  ⟨Finset.prod_nonneg fun i hi => (h i hi).1,
    Finset.prod_le_one₀ (fun i hi => (h i hi).1) fun i hi => (h i hi).2⟩

/-- `‖x‖² > 0` for a nonzero vector. -/
private lemma SrcCutoff_sumSq_pos {W : ℕ} {x : Fin W → ℂ} (hx : x ≠ 0) : 0 < ∑ i, ‖x i‖ ^ 2 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  have hj' : 0 < ‖x j‖ ^ 2 := by
    have : x j ≠ 0 := hj
    positivity
  exact lt_of_lt_of_le hj' (Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2)
    (fun i _ => by positivity) (Finset.mem_univ j))

/-- If `1 < x / y` with `y ≥ 0`, then `0 < y < x`. -/
private lemma SrcCutoff_of_one_lt_div {x y : ℝ} (hy : 0 ≤ y) (h : 1 < x / y) : 0 < y ∧ y < x := by
  rcases hy.eq_or_lt with h0 | h0
  · rw [← h0, div_zero] at h
    linarith
  · exact ⟨h0, (one_lt_div h0).1 h⟩

/-- `‖M v‖² ≤ ‖M‖²_HS ‖v‖²` (Cauchy–Schwarz row by row). -/
private lemma SrcCutoff_vecSq_mulVec_le {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) :
    ∑ i, ‖(M *ᵥ v) i‖ ^ 2 ≤ hsSq M * ∑ j, ‖v j‖ ^ 2 := by
  unfold hsSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ‖(M *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ * ‖v j‖) ^ 2 := by
        gcongr
        simp only [Matrix.mulVec, dotProduct]
        exact (norm_sum_le _ _).trans (by simp)
    _ ≤ (∑ j, ‖M i j‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- The operator norm is at most the Hilbert–Schmidt norm. -/
private lemma SrcCutoff_norm_le_sqrt_hsSq {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    ‖A‖ ≤ Real.sqrt (hsSq A) := by
  have h0 : 0 ≤ hsSq A := by unfold hsSq; positivity
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  change ‖Matrix.toEuclideanLin A x‖ ≤ _ * ‖x‖
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul h0]
  refine Real.sqrt_le_sqrt ?_
  exact SrcCutoff_vecSq_mulVec_le A x.ofLp

/-- A frequent non-strict inequality between functions continuous at `y₀` holds at `y₀`. -/
private lemma SrcCutoff_le_of_frequently {Y : Type*} [TopologicalSpace Y] {φ ψ : Y → ℝ} {y₀ : Y}
    (hφ : ContinuousAt φ y₀) (hψ : ContinuousAt ψ y₀) (h : ∃ᶠ y in nhds y₀, φ y ≤ ψ y) :
    φ y₀ ≤ ψ y₀ :=
  (isClosed_le continuous_fst continuous_snd).mem_of_frequently_of_tendsto
    (f := fun y => (φ y, ψ y)) h (hφ.prodMk_nhds hψ)

/-- If `normCut L (M y)⁻¹ ≠ 0` frequently near `y₀` and `M` is continuous at `y₀`, then `M y₀` is
invertible with `‖(M y₀)⁻¹‖²_HS ≤ 2 L`. -/
private lemma SrcCutoff_normCut_closure {Y : Type*} [TopologicalSpace Y] {n : Type*} [Fintype n]
    [DecidableEq n] {L : ℝ} (hL : 0 < L) {M : Y → Matrix n n ℂ} {y₀ : Y} (hM : ContinuousAt M y₀)
    (h : ∃ᶠ y in nhds y₀, normCut L (M y)⁻¹ ≠ 0) : IsUnit (M y₀) ∧ hsSq (M y₀)⁻¹ ≤ 2 * L :=
  (normCut_inv_spec hL).2.1 _ ((isClosed_tsupport _).mem_of_frequently_of_tendsto
    (h.mono fun _ hy => subset_tsupport _ hy) hM.tendsto)

/-- The inverse is `C^k` at a point where the argument is `C^k` and invertible. -/
private lemma SrcCutoff_contDiffAt_inv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : Type*} [Fintype n] [DecidableEq n] {k : WithTop ℕ∞} {f : X → Matrix n n ℂ} {x : X}
    (hf : ContDiffAt ℝ k f x) (hu : IsUnit (f x)) : ContDiffAt ℝ k (fun y => (f y)⁻¹) x := by
  have h1 := contDiffAt_ringInverse ℝ (n := k) hu.unit
  rw [hu.unit_spec] at h1
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  exact h1.comp x hf

open scoped ComplexOrder in
/-- `Y* Y + s` is invertible for `s > 0`. -/
private lemma SrcCutoff_isUnit_gram_add {n : Type*} [Fintype n] [DecidableEq n]
    (Y : Matrix n n ℂ) {s : ℝ} (hs : 0 < s) : IsUnit (Yᴴ * Y + ((s : ℝ) : ℂ) • 1) := by
  have h1 : (((s : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hs)
  exact (Matrix.PosDef.posSemidef_add (Matrix.posSemidef_conjTranspose_mul_self Y) h1).isUnit

section Smooth

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : WithTop ℕ∞} {x : X}

/-- A matrix-valued map is `C^k` at a point iff all its entries are. -/
private lemma SrcCutoff_contDiffAt_matrix_iff {m : Type*} [Fintype m] [DecidableEq m]
    {Φ : X → Matrix m m ℂ} : ContDiffAt ℝ k Φ x ↔ ∀ i j, ContDiffAt ℝ k (fun y => Φ y i j) x := by
  let e : Matrix m m ℂ ≃L[ℝ] (m → m → ℂ) :=
    (Matrix.ofLinearEquiv ℝ).symm.toContinuousLinearEquiv
  rw [← e.comp_contDiffAt_iff, contDiffAt_pi]
  refine forall_congr' fun i => ?_
  rw [contDiffAt_pi]
  rfl

/-- The adjoint of a `C^k` matrix-valued map is `C^k`. -/
private lemma SrcCutoff_contDiffAt_conjTranspose {W : ℕ} {A : X → Matrix (Fin W) (Fin W) ℂ}
    (hA : ContDiffAt ℝ k A x) : ContDiffAt ℝ k (fun y => (A y)ᴴ) x := by
  rw [SrcCutoff_contDiffAt_matrix_iff] at hA ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact Complex.conjCLE.contDiff.contDiffAt.comp x (hA j i)

/-- `y ↦ ‖M y‖²_HS` is `C^k` at `x` when `M` is. -/
private lemma SrcCutoff_contDiffAt_hsSq {m : Type*} [Fintype m] [DecidableEq m]
    {M : X → Matrix m m ℂ} (hM : ContDiffAt ℝ k M x) : ContDiffAt ℝ k (fun y => hsSq (M y)) x := by
  rw [SrcCutoff_contDiffAt_matrix_iff] at hM
  unfold hsSq
  exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => (hM a b).norm_sq ℝ

/-- `y ↦ ‖A(y) u(y)‖²` is `C^k` at `x` when `A` and `u` are. -/
private lemma SrcCutoff_contDiffAt_sumSq {W : ℕ} {A : X → Matrix (Fin W) (Fin W) ℂ}
    {u : X → Fin W → ℂ} (hA : ContDiffAt ℝ k A x) (hu : ContDiffAt ℝ k u x) :
    ContDiffAt ℝ k (fun y => ∑ i, ‖(A y *ᵥ u y) i‖ ^ 2) x := by
  rw [SrcCutoff_contDiffAt_matrix_iff] at hA
  rw [contDiffAt_pi] at hu
  refine ContDiffAt.sum fun i _ => ContDiffAt.norm_sq ℝ ?_
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiffAt.sum fun j _ => (hA i j).mul (hu j)

/-- `y ↦ Re Tr M(y)` is `C^k` at `x` when `M` is. -/
private lemma SrcCutoff_contDiffAt_traceRe {W : ℕ} {M : X → Matrix (Fin W) (Fin W) ℂ}
    (hM : ContDiffAt ℝ k M x) : ContDiffAt ℝ k (fun y => (M y).trace.re) x := by
  rw [SrcCutoff_contDiffAt_matrix_iff] at hM
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  exact ContDiffAt.sum fun i _ => Complex.reCLM.contDiff.contDiffAt.comp x (hM i i)

/-- The rank surrogate `rankSurr s (M y)` is `C^k` at `x` when `M` is and `M x + s²` is
invertible. -/
private lemma SrcCutoff_contDiffAt_rankSurr {W : ℕ} {s : ℝ} {M : X → Matrix (Fin W) (Fin W) ℂ}
    (hM : ContDiffAt ℝ k M x) (hu : IsUnit (M x + ((s ^ 2 : ℝ) : ℂ) • 1)) :
    ContDiffAt ℝ k (fun y => rankSurr s (M y)) x := by
  unfold rankSurr
  exact contDiffAt_const.mul (SrcCutoff_contDiffAt_traceRe
    (hM.mul (SrcCutoff_contDiffAt_inv (hM.add contDiffAt_const) hu)))

end Smooth

/-- Each block `ω ↦ gueBlock W q ω i` is a smooth (real-linear) function of the sample. -/
private lemma SrcCutoff_contDiff_gueBlock (W q : ℕ) (i : Fin q) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun ω : Ω W q => gueBlock W q ω i) := by
  rw [contDiff_iff_contDiffAt]
  intro ω₀
  rw [SrcCutoff_contDiffAt_matrix_iff]
  intro α β
  have hc : ∀ p : Fin q × Fin W × Fin W,
      ContDiff ℝ k (fun ω : Ω W q => ((ω p : ℝ) : ℂ)) := fun p =>
    Complex.ofRealCLM.contDiff.comp (contDiff_pi.1 contDiff_id p)
  simp only [gueBlock, Matrix.of_apply]
  split_ifs
  · exact ((hc _).div_const _).contDiffAt
  · exact (((hc _).add (contDiff_const.mul (hc _))).div_const _).contDiffAt
  · exact (((hc _).sub (contDiff_const.mul (hc _))).div_const _).contDiffAt

/-- The input sequence `ω ↦ blockSeq W q ω j` is smooth. -/
private lemma SrcCutoff_contDiff_blockSeq (W q j : ℕ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun ω : Ω W q => blockSeq W q ω j) := by
  unfold blockSeq
  by_cases hj : j < q
  · simp only [hj, ↓reduceDIte]
    exact SrcCutoff_contDiff_gueBlock W q ⟨j, hj⟩
  · simp only [hj, ↓reduceDIte]
    exact contDiff_const

/-- The blocks `V_{j+1}` are Hermitian. -/
private lemma SrcCutoff_blockSeq_isHermitian {W q : ℕ} (ω : Ω W q) (j : ℕ) :
    (blockSeq W q ω j).IsHermitian := by
  unfold blockSeq
  split_ifs
  · exact gueBlock_isHermitian W q ω _
  · exact Matrix.isHermitian_zero

/-- The recursion `R_{j+1} = (V_{j+1} - E - g² R_j)⁻¹` of (9.2) [su:eq:transported-normal] for
`j ≥ 4`. -/
private lemma SrcCutoff_chartR_succ {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {ω : Ω W q} {j : ℕ} (hj : 4 ≤ j) :
    chartR W g E q R ω (j + 1) =
      (blockSeq W q ω j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω j)⁻¹ := by
  simp only [chartR, show ¬ j < 4 by omega, ↓reduceIte]

/-- For a Hermitian `R_4`, all graph coordinates `R_j` are Hermitian. -/
private lemma SrcCutoff_chartR_isHermitian {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (ω : Ω W q) : ∀ j, (chartR W g E q R ω j).IsHermitian
  | 0 => by simpa only [chartR] using hR
  | j + 1 => by
    by_cases h4 : j < 4
    · simpa only [chartR, h4, ↓reduceIte] using hR
    · rw [SrcCutoff_chartR_succ (by omega)]
      have hE : IsSelfAdjoint (E : ℂ) := by rw [isSelfAdjoint_iff]; simp
      have hg : IsSelfAdjoint ((g : ℂ) ^ 2) := by rw [isSelfAdjoint_iff]; simp
      exact (((SrcCutoff_blockSeq_isHermitian ω j).sub (Matrix.isHermitian_one.smul hE)).sub
        ((SrcCutoff_chartR_isHermitian hR ω j).smul hg)).inv

/-- The graph coordinates `R_j` are `C^k` at `ω₀` when `R_5, …, R_j` are invertible there. -/
private lemma SrcCutoff_contDiffAt_chartR {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {ω₀ : Ω W q} {k : WithTop ℕ∞} :
    ∀ j, (∀ i, 5 ≤ i → i ≤ j → IsUnit (chartR W g E q R ω₀ i)) →
      ContDiffAt ℝ k (fun ω => chartR W g E q R ω j) ω₀
  | 0, _ => by
    simp only [chartR]
    exact contDiffAt_const
  | j + 1, hU => by
    by_cases h4 : j < 4
    · simp only [chartR, h4, ↓reduceIte]
      exact contDiffAt_const
    · have ih := SrcCutoff_contDiffAt_chartR (k := k) j fun i h5 hi => hU i h5 (by omega)
      have hu := hU (j + 1) (by omega) le_rfl
      simp only [SrcCutoff_chartR_succ (show 4 ≤ j by omega)] at hu ⊢
      rw [Matrix.isUnit_nonsing_inv_iff] at hu
      exact SrcCutoff_contDiffAt_inv ((((SrcCutoff_contDiff_blockSeq W q j).contDiffAt).sub
        contDiffAt_const).sub (ih.const_smul _)) hu

/-- The products `R_{[j,5]}` are `C^k` at `ω₀` when `R_5, …, R_j` are invertible there. -/
private lemma SrcCutoff_contDiffAt_chartProd {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {ω₀ : Ω W q} {k : WithTop ℕ∞} :
    ∀ j, (∀ i, 5 ≤ i → i ≤ j → IsUnit (chartR W g E q R ω₀ i)) →
      ContDiffAt ℝ k (fun ω => chartProd W g E q R ω j) ω₀
  | 0, _ => by
    simp only [chartProd]
    exact contDiffAt_const
  | j + 1, hU => by
    by_cases h4 : j < 4
    · simp only [chartProd, h4, ↓reduceIte]
      exact contDiffAt_const
    · simp only [chartProd, h4, ↓reduceIte]
      exact (SrcCutoff_contDiffAt_chartR (j + 1) hU).mul
        (SrcCutoff_contDiffAt_chartProd j fun i h5 hi => hU i h5 (by omega))

/-- The right-cavity inverses `cavR … m` are `C^k` at `ω₀` when `cavR … i`, `i ≤ m`, are
invertible there. -/
private lemma SrcCutoff_contDiffAt_cavR {W q : ℕ} {g E : ℝ} {ω₀ : Ω W q} {k : WithTop ℕ∞} :
    ∀ m, (∀ i, i ≤ m → IsUnit (cavR W g E q ω₀ i)) →
      ContDiffAt ℝ k (fun ω => cavR W g E q ω m) ω₀
  | 0, hU => by
    have hu := hU 0 le_rfl
    simp only [cavR] at hu ⊢
    rw [Matrix.isUnit_nonsing_inv_iff] at hu
    exact SrcCutoff_contDiffAt_inv
      (((SrcCutoff_contDiff_blockSeq W q _).contDiffAt).sub contDiffAt_const) hu
  | m + 1, hU => by
    have ih := SrcCutoff_contDiffAt_cavR (k := k) m fun i hi => hU i (by omega)
    have hu := hU (m + 1) le_rfl
    simp only [cavR] at hu ⊢
    rw [Matrix.isUnit_nonsing_inv_iff] at hu
    exact SrcCutoff_contDiffAt_inv ((((SrcCutoff_contDiff_blockSeq W q _).contDiffAt).sub
      contDiffAt_const).sub (ih.const_smul _)) hu

/-- The products `cavProd … m` are `C^k` at `ω₀` when `cavR … i`, `i < m`, are invertible
there. -/
private lemma SrcCutoff_contDiffAt_cavProd {W q : ℕ} {g E : ℝ} {ω₀ : Ω W q} {k : WithTop ℕ∞} :
    ∀ m, (∀ i, i < m → IsUnit (cavR W g E q ω₀ i)) →
      ContDiffAt ℝ k (fun ω => cavProd W g E q ω m) ω₀
  | 0, _ => by
    simp only [cavProd]
    exact contDiffAt_const
  | m + 1, hU => by
    simp only [cavProd]
    exact (SrcCutoff_contDiffAt_cavProd m fun i hi => hU i (by omega)).mul
      (SrcCutoff_contDiffAt_cavR m fun i hi => hU i (by omega))

/-- `R̃` is `C^k` at `ω₀` when the right-cavity inverses and `R̃` exist there. -/
private lemma SrcCutoff_contDiffAt_cavRes {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {ω₀ : Ω W q} {k : WithTop ℕ∞} (hK : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω₀ m))
    (hT : IsUnit (cavRes W g E q R ω₀)) : ContDiffAt ℝ k (fun ω => cavRes W g E q R ω) ω₀ := by
  unfold cavRes at hT ⊢
  rw [Matrix.isUnit_nonsing_inv_iff] at hT
  exact SrcCutoff_contDiffAt_inv (((((SrcCutoff_contDiff_blockSeq W q 4).contDiffAt).sub
    contDiffAt_const).sub contDiffAt_const).sub ((SrcCutoff_contDiffAt_cavR (q - 7) hK).const_smul
    _)) hT

/-- `A* A` is `C^k` at `ω₀` when the right-cavity inverses exist there. -/
private lemma SrcCutoff_contDiffAt_gram {W q : ℕ} {g E : ℝ} {ω₀ : Ω W q} {k : WithTop ℕ∞}
    (hK : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω₀ m)) :
    ContDiffAt ℝ k (fun ω => (cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) ω₀ := by
  have h := SrcCutoff_contDiffAt_cavProd (k := k) (g := g) (E := E) (q - 6) fun i hi =>
    hK i (by omega)
  exact (SrcCutoff_contDiffAt_conjTranspose h).mul h

/-- The retained spectral projection `1_{(t², ∞)}(A* A)` is smooth at `ω₀` when the right-cavity
inverses exist there and `t²` is not an eigenvalue of `A* A`. -/
private lemma SrcCutoff_contDiffAt_retSpec {W q : ℕ} {g E t : ℝ} {ω₀ : Ω W q}
    (hK : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω₀ m))
    (hgap : IsUnit ((cavProd W g E q ω₀ (q - 6))ᴴ * cavProd W g E q ω₀ (q - 6) -
      ((t ^ 2 : ℝ) : ℂ) • 1)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ω => retSpec W g E q t ω) ω₀ := by
  set F : Ω W q → Matrix (Fin W) (Fin W) ℂ :=
    fun ω => (cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) with hFdef
  have hF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ω₀ := SrcCutoff_contDiffAt_gram hK
  set T : Set (Matrix (Fin W) (Fin W) ℂ) :=
    {M | M.IsHermitian ∧ IsUnit (M - ((t ^ 2 : ℝ) : ℂ) • 1)} with hTdef
  have hopen : {M : Matrix (Fin W) (Fin W) ℂ | IsUnit (M - ((t ^ 2 : ℝ) : ℂ) • 1)} ∈
      nhds (F ω₀) :=
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      (Units.isOpen.mem_nhds hgap)
  have hmem : F ⁻¹' T ∈ nhds ω₀ := by
    filter_upwards [hF.continuousAt.preimage_mem_nhds hopen] with ω hω
    exact ⟨Matrix.isHermitian_conjTranspose_mul_self _, hω⟩
  have h := (contDiffOn_specProj_Ioi (n := Fin W) (t ^ 2) (F ω₀)
    ⟨Matrix.isHermitian_conjTranspose_mul_self _, hgap⟩).comp ω₀ hF.contDiffWithinAt
    (Set.mapsTo_preimage F T)
  exact h.contDiffAt hmem

open scoped ComplexOrder in
/-- `P T* T P + (1 - P)` is invertible for invertible `T` and a Hermitian idempotent `P`. -/
private lemma SrcCutoff_isUnit_flagGram {n : Type*} [Fintype n] [DecidableEq n]
    {T P : Matrix n n ℂ} (hT : IsUnit T) (hP : Pᴴ = P) (hPP : P * P = P) :
    IsUnit (P * Tᴴ * T * P + (1 - P)) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have hker : ∀ z : n → ℂ, (P * Tᴴ * T * P + (1 - P)) *ᵥ z = 0 → z = 0 := by
    intro z hz
    have h1 : P *ᵥ ((P * Tᴴ * T * P + (1 - P)) *ᵥ z) = 0 := by rw [hz, Matrix.mulVec_zero]
    have h2 : P * (P * Tᴴ * T * P + (1 - P)) = P * Tᴴ * T * P := by
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPP]
      abel
    rw [Matrix.mulVec_mulVec, h2] at h1
    set w : n → ℂ := P *ᵥ z with hw
    have hPw : P *ᵥ w = w := by rw [hw, Matrix.mulVec_mulVec, hPP]
    have h3 : P *ᵥ (Tᴴ *ᵥ (T *ᵥ w)) = 0 := by
      rw [← h1, hw]; simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have hs : star w = star w ᵥ* P := by
      conv_lhs => rw [← hPw]
      rw [Matrix.star_mulVec, hP]
    have h4 : star (T *ᵥ w) ⬝ᵥ (T *ᵥ w) = 0 := by
      calc star (T *ᵥ w) ⬝ᵥ (T *ᵥ w) = star w ⬝ᵥ (Tᴴ *ᵥ (T *ᵥ w)) := by
            rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
        _ = (star w ᵥ* P) ⬝ᵥ (Tᴴ *ᵥ (T *ᵥ w)) := by rw [← hs]
        _ = star w ⬝ᵥ (P *ᵥ (Tᴴ *ᵥ (T *ᵥ w))) := (Matrix.dotProduct_mulVec _ _ _).symm
        _ = 0 := by rw [h3, dotProduct_zero]
    have h5 : T *ᵥ w = 0 := dotProduct_star_self_eq_zero.mp h4
    have h6 : w = 0 := by
      obtain ⟨U, rfl⟩ := hT
      have := congrArg (fun v => (↑U⁻¹ : Matrix n n ℂ) *ᵥ v) h5
      simpa [Matrix.mulVec_mulVec] using this
    have h7 : (1 - P) *ᵥ z = 0 := by
      have : (P * Tᴴ * T * P + (1 - P)) *ᵥ z = (P * Tᴴ * T * P) *ᵥ z + (1 - P) *ᵥ z :=
        Matrix.add_mulVec _ _ _
      rw [hz, h1, zero_add] at this
      exact this.symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hw, h6, sub_zero] at h7
    exact h7
  intro a b hab
  have := hker (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self])
  exact sub_eq_zero.mp this

/-- The retained projection `Q` is smooth at every point of the invariant set of Section 9.4.4
[su:sec:cutoff-estimates]. -/
private lemma SrcCutoff_contDiffAt_retProj {W q : ℕ} {g E t : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {ω₀ : Ω W q} (hK : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω₀ m))
    (hT : IsUnit (cavRes W g E q R ω₀))
    (hgap : IsUnit ((cavProd W g E q ω₀ (q - 6))ᴴ * cavProd W g E q ω₀ (q - 6) -
      ((t ^ 2 : ℝ) : ℂ) • 1)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ω => retProj W g E q R t ω) ω₀ := by
  have hS := SrcCutoff_contDiffAt_retSpec (t := t) hK hgap
  have hTd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ω => cavRes W g E q R ω) ω₀ :=
    SrcCutoff_contDiffAt_cavRes hK hT
  have hTs := SrcCutoff_contDiffAt_conjTranspose hTd
  have hspec := specProj_spec (Matrix.isHermitian_conjTranspose_mul_self
    (cavProd W g E q ω₀ (q - 6))) (Set.Ioi (t ^ 2))
  have hG : IsUnit (retSpec W g E q t ω₀ * (cavRes W g E q R ω₀)ᴴ * cavRes W g E q R ω₀ *
      retSpec W g E q t ω₀ + (1 - retSpec W g E q t ω₀)) :=
    SrcCutoff_isUnit_flagGram hT hspec.1 hspec.2.1
  unfold retProj flagProj
  exact (((hTd.mul hS).mul (SrcCutoff_contDiffAt_inv ((((hS.mul hTs).mul hTd).mul hS).add
    (contDiffAt_const.sub hS)) hG)).mul hS).mul hTs

/-- The active-chain matrix is smooth in the sample. -/
private lemma SrcCutoff_contDiff_activeMat {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {k : WithTop ℕ∞} : ContDiff ℝ k (fun ω : Ω W q => activeMat W g E q R ω) := by
  refine contDiff_iff_contDiffAt.2 fun ω₀ => ?_
  rw [SrcCutoff_contDiffAt_matrix_iff]
  intro a b
  simp only [activeMat, Matrix.of_apply]
  by_cases h1 : a.1 = b.1
  · simp only [h1, ↓reduceIte]
    exact (SrcCutoff_contDiffAt_matrix_iff.1 ((((SrcCutoff_contDiff_blockSeq W q
      ((b.1 : ℕ) + 4)).contDiffAt).sub contDiffAt_const).sub contDiffAt_const)) a.2 b.2
  · simp only [h1, ↓reduceIte]
    exact contDiffAt_const

/-- The factors of a nonzero cutoff are nonzero. -/
private lemma SrcCutoff_factors {W q : ℕ} {g E : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {c : CutLevels} {ω : Ω W q} {v : Fin W → ℂ} (h : srcCut W g E q R P c ω v ≠ 0) :
    (∀ j ∈ Finset.Icc 5 (q - 2), normCut ((W : ℝ) ^ 6 / 2) (chartR W g E q R ω j) ≠ 0 ∧
      stepDown (2 * rankSurr g⁻¹ ((chartR W g E q R ω j)ᴴ * chartR W g E q R ω j) /
        (W * Real.sqrt g)) ≠ 0) ∧
    normCut ((W : ℝ) ^ 6 / 2) (chartR W g E q R ω (q - 1)) ≠ 0 ∧
    (∀ m ∈ Finset.range (q - 6), normCut ((W : ℝ) ^ 6 / 2) (cavR W g E q ω m) ≠ 0) ∧
    normCut ((W : ℝ) ^ 6 / 2) (cavRes W g E q R ω) ≠ 0 ∧
    normCut ((W : ℝ) ^ 6 / 2) (activeMat W g E q R ω)⁻¹ ≠ 0 ∧
    normCut c.Lgap ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) -
      ((c.t ^ 2 : ℝ) : ℂ) • 1)⁻¹ ≠ 0 ∧
    stepDown (rankSurr c.t ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) /
      c.Lrk) ≠ 0 ∧
    stepDown (2 * 8 ^ c.kP * ((retProj W g E q R c.t ω * (1 - P) * retProj W g E q R c.t ω) ^
      c.kP).trace.re) ≠ 0 ∧
    stepDown (hsSq (blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R) / (W : ℝ) ^ 8) ≠ 0 ∧
    (∀ i ∈ Finset.Icc 5 (q - 2), stepDown (hsSq (blockSeq W q ω i) / (W : ℝ) ^ 8) ≠ 0) ∧
    stepUp (2 * (W : ℝ) ^ 20 * (∑ i, ‖(P *ᵥ v) i‖ ^ 2) / ∑ i, ‖v i‖ ^ 2) ≠ 0 ∧
    stepDown ((∑ i, ‖(retProj W g E q R c.t ω *ᵥ v) i‖ ^ 2) /
      (c.Lov * ∑ i, ‖(P *ᵥ v) i‖ ^ 2)) ≠ 0 ∧
    stepDown (16 * (∑ i, ‖(retProj W g E q R c.t ω *ᵥ (P *ᵥ v)) i‖ ^ 2) /
      ∑ i, ‖(P *ᵥ v) i‖ ^ 2) ≠ 0 ∧
    stepUp ((∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2) /
      (c.kOut ^ 2 * ∑ i, ‖(P *ᵥ v) i‖ ^ 2)) ≠ 0 := by
  unfold srcCut matCut srcCutV regCut at h
  simp only [mul_ne_zero_iff, Finset.prod_ne_zero_iff] at h
  tauto

/-- Closure step along the chain: if, frequently near `y₀`, the cutoffs of `R_5, …, R_J` are
nonzero, then `R_5, …, R_J` are invertible at `y₀` with `‖R_j‖²_HS ≤ 2 L`. -/
private lemma SrcCutoff_chain_closure {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ} {L : ℝ}
    (hL : 0 < L) {V : Type*} [TopologicalSpace V] {y₀ : Ω W q × V} {J : ℕ}
    (h : ∀ j, 5 ≤ j → j ≤ J → ∃ᶠ y in nhds y₀, normCut L (chartR W g E q R y.1 j) ≠ 0) :
    ∀ j, 5 ≤ j → j ≤ J →
      IsUnit (chartR W g E q R y₀.1 j) ∧ hsSq (chartR W g E q R y₀.1 j) ≤ 2 * L := by
  have key : ∀ j, ∀ i, 5 ≤ i → i ≤ j → i ≤ J →
      IsUnit (chartR W g E q R y₀.1 i) ∧ hsSq (chartR W g E q R y₀.1 i) ≤ 2 * L := by
    intro j
    induction j with
    | zero => intro i h5 hi; omega
    | succ j ih =>
      intro i h5 hi hJ
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact ih i h5 (by omega) hJ
      · obtain rfl : i = j + 1 := by omega
        have hU : ∀ i, 5 ≤ i → i ≤ j → IsUnit (chartR W g E q R y₀.1 i) :=
          fun i h5' hi' => (ih i h5' hi' (by omega)).1
        have h1 : ContinuousAt (fun ω => blockSeq W q ω j - (E : ℂ) • 1 -
            ((g : ℂ) ^ 2) • chartR W g E q R ω j) y₀.1 :=
          ((((SrcCutoff_contDiff_blockSeq (k := 0) W q j).contDiffAt).sub contDiffAt_const).sub
            ((SrcCutoff_contDiffAt_chartR (k := 0) j hU).const_smul _)).continuousAt
        have hc : ContinuousAt (fun y : Ω W q × V => blockSeq W q y.1 j - (E : ℂ) • 1 -
            ((g : ℂ) ^ 2) • chartR W g E q R y.1 j) y₀ := h1.comp continuousAt_fst
        have hfr := h (j + 1) h5 hJ
        simp only [SrcCutoff_chartR_succ (show 4 ≤ j by omega)] at hfr ⊢
        have := SrcCutoff_normCut_closure hL hc hfr
        exact ⟨Matrix.isUnit_nonsing_inv_iff.2 this.1, this.2⟩
  exact fun j h5 hJ => key j j h5 le_rfl hJ

/-- Closure step along the right-cavity chain: if, frequently near `y₀`, the cutoffs of
`cavR … m`, `m ≤ J`, are nonzero, then these are invertible at `y₀` with `‖·‖²_HS ≤ 2 L`. -/
private lemma SrcCutoff_cav_closure {W q : ℕ} {g E : ℝ} {L : ℝ} (hL : 0 < L) {V : Type*}
    [TopologicalSpace V] {y₀ : Ω W q × V} {J : ℕ}
    (h : ∀ m, m ≤ J → ∃ᶠ y in nhds y₀, normCut L (cavR W g E q y.1 m) ≠ 0) :
    ∀ m, m ≤ J → IsUnit (cavR W g E q y₀.1 m) ∧ hsSq (cavR W g E q y₀.1 m) ≤ 2 * L := by
  have key : ∀ m, ∀ i, i ≤ m → i ≤ J →
      IsUnit (cavR W g E q y₀.1 i) ∧ hsSq (cavR W g E q y₀.1 i) ≤ 2 * L := by
    intro m
    induction m with
    | zero =>
      intro i hi hJ
      obtain rfl : i = 0 := by omega
      have h1 : ContinuousAt (fun ω => blockSeq W q ω (q - 2) - (E : ℂ) • 1) y₀.1 :=
        (((SrcCutoff_contDiff_blockSeq (k := 0) W q _).contDiffAt).sub
          contDiffAt_const).continuousAt
      have hc : ContinuousAt (fun y : Ω W q × V => blockSeq W q y.1 (q - 2) - (E : ℂ) • 1) y₀ :=
        h1.comp continuousAt_fst
      have hfr := h 0 hJ
      simp only [cavR] at hfr ⊢
      have := SrcCutoff_normCut_closure hL hc hfr
      exact ⟨Matrix.isUnit_nonsing_inv_iff.2 this.1, this.2⟩
    | succ m ih =>
      intro i hi hJ
      rcases Nat.lt_or_ge i (m + 1) with hlt | hge
      · exact ih i (by omega) hJ
      · obtain rfl : i = m + 1 := by omega
        have hU : ∀ i, i ≤ m → IsUnit (cavR W g E q y₀.1 i) :=
          fun i hi' => (ih i hi' (by omega)).1
        have h1 : ContinuousAt (fun ω => blockSeq W q ω (q - 3 - m) - (E : ℂ) • 1 -
            ((g : ℂ) ^ 2) • cavR W g E q ω m) y₀.1 :=
          ((((SrcCutoff_contDiff_blockSeq (k := 0) W q _).contDiffAt).sub contDiffAt_const).sub
            ((SrcCutoff_contDiffAt_cavR (k := 0) m hU).const_smul _)).continuousAt
        have hc : ContinuousAt (fun y : Ω W q × V => blockSeq W q y.1 (q - 3 - m) - (E : ℂ) • 1 -
            ((g : ℂ) ^ 2) • cavR W g E q y.1 m) y₀ := h1.comp continuousAt_fst
        have hfr := h (m + 1) hJ
        simp only [cavR] at hfr ⊢
        have := SrcCutoff_normCut_closure hL hc hfr
        exact ⟨Matrix.isUnit_nonsing_inv_iff.2 this.1, this.2⟩
  exact fun m hJ => key m m le_rfl hJ

/-- Eigenvalue counts of `U diag(d) U*` for the eigenvector unitary `U` of a Hermitian `A`. -/
private lemma SrcCutoff_countIn_diag {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian)
    (d : Fin W → ℝ) {M : Matrix (Fin W) (Fin W) ℂ} (hMH : M.IsHermitian)
    (hM : M = (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) *
      Matrix.diagonal (fun k => (d k : ℂ)) * (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)ᴴ)
    (S : Set ℝ) : countIn M S = #(univ.filter fun k => d k ∈ S) := by
  have hU1 : (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)ᴴ *
      (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hcp : M.charpoly = ∏ k, (Polynomial.X - Polynomial.C ((d k : ℂ))) := by
    rw [hM, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul,
      Matrix.charpoly_diagonal]
  have hroots : M.charpoly.roots = Multiset.map (fun k => ((d k : ℝ) : ℂ)) Finset.univ.val := by
    rw [hcp, Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    · exact Finset.prod_ne_zero_iff.mpr fun k _ => Polynomial.X_sub_C_ne_zero _
  rw [countIn_eq_card_roots hMH, hroots, Multiset.filter_map]
  simp [Finset.card_def, Finset.filter_val]

/-- For a Hermitian `Y` and `g > 0`: `#{|g² y| > g} ≤ #{eigenvalues of Y* Y above g⁻²}`. -/
private lemma SrcCutoff_countIn_le {W : ℕ} {Y : Matrix (Fin W) (Fin W) ℂ} (hY : Y.IsHermitian)
    {g : ℝ} (hg : 0 < g) :
    countIn (((g : ℂ) ^ 2) • Y) {x | g < |x|} ≤ countIn (Yᴴ * Y) (Set.Ioi (g⁻¹ ^ 2)) := by
  set U : Matrix (Fin W) (Fin W) ℂ := (hY.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
    with hUdef
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hY.eigenvectorUnitary.2
  have hspec : Y = U * Matrix.diagonal (fun k => (hY.eigenvalues k : ℂ)) * Uᴴ := by
    have h := hY.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hk : IsSelfAdjoint ((g : ℂ) ^ 2) := by rw [isSelfAdjoint_iff]; simp
  have h1 : ((g : ℂ) ^ 2) • Y =
      U * Matrix.diagonal (fun k => ((g ^ 2 * hY.eigenvalues k : ℝ) : ℂ)) * Uᴴ := by
    have hD : Matrix.diagonal (fun k => ((g ^ 2 * hY.eigenvalues k : ℝ) : ℂ)) =
        ((g : ℂ) ^ 2) • Matrix.diagonal (fun k => (hY.eigenvalues k : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    conv_lhs => rw [hspec]
    rw [hD, Matrix.mul_smul, Matrix.smul_mul]
  have h2 : Yᴴ * Y = U * Matrix.diagonal (fun k => ((hY.eigenvalues k ^ 2 : ℝ) : ℂ)) * Uᴴ := by
    rw [hY.eq]
    conv_lhs => rw [hspec]
    calc U * Matrix.diagonal (fun k => (hY.eigenvalues k : ℂ)) * Uᴴ *
          (U * Matrix.diagonal (fun k => (hY.eigenvalues k : ℂ)) * Uᴴ)
        = U * (Matrix.diagonal (fun k => (hY.eigenvalues k : ℂ)) * (Uᴴ * U) *
          Matrix.diagonal (fun k => (hY.eigenvalues k : ℂ))) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          have hd : (fun k => (hY.eigenvalues k : ℂ) * (hY.eigenvalues k : ℂ)) =
              fun k => ((hY.eigenvalues k ^ 2 : ℝ) : ℂ) := by
            funext k
            rw [Complex.ofReal_pow, sq]
          rw [hU1, Matrix.mul_one, Matrix.diagonal_mul_diagonal, hd]
  rw [SrcCutoff_countIn_diag hY _ (hY.smul hk) h1,
    SrcCutoff_countIn_diag hY _ (Matrix.isHermitian_conjTranspose_mul_self Y) h2]
  refine Finset.card_le_card fun k hk' => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
    Set.mem_Ioi] at hk' ⊢
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < g ^ 2)] at hk'
  have h3 : g * g⁻¹ < g * |hY.eigenvalues k| := by
    rw [mul_inv_cancel₀ hg.ne']
    nlinarith [abs_nonneg (hY.eigenvalues k)]
  have h4 : g⁻¹ < |hY.eigenvalues k| := lt_of_mul_lt_mul_left h3 hg.le
  calc g⁻¹ ^ 2 < |hY.eigenvalues k| ^ 2 := by gcongr
    _ = hY.eigenvalues k ^ 2 := sq_abs _

/-- On the topological support of the cutoff, off `v̂ = 0`, the closed conditions `CutSupp`
hold. -/
theorem srcCut_tsupport {W q : ℕ} {g E : ℝ} (hW : 1 ≤ W) (hq : 7 ≤ q) (hg : 0 < g)
    {R : Matrix (Fin W) (Fin W) ℂ} (hR : R.IsHermitian) (P : Matrix (Fin W) (Fin W) ℂ)
    {c : CutLevels} (hLov : 0 < c.Lov) (hLrk : 0 < c.Lrk) (hLgap : 0 < c.Lgap)
    (hkOut : 0 < c.kOut) (p : Ω W q × (Fin W → ℂ))
    (hp : p ∈ tsupport (fun p : Ω W q × (Fin W → ℂ) => srcCut W g E q R P c p.1 p.2))
    (hv : p.2 ≠ 0) : CutSupp W g E q R P c p.1 p.2 := by
  obtain ⟨ω₀, v₀⟩ := p
  have hfr : ∃ᶠ y in nhds (ω₀, v₀), srcCut W g E q R P c y.1 y.2 ≠ 0 :=
    mem_closure_iff_frequently.1 hp
  have hF := hfr.mono fun y hy => SrcCutoff_factors hy
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hW6 : (0 : ℝ) < (W : ℝ) ^ 6 / 2 := by positivity
  have hW8 : (0 : ℝ) < (W : ℝ) ^ 8 := by positivity
  -- the chain `R_5, …, R_{q-1}`
  have hC := SrcCutoff_chain_closure (g := g) (E := E) (R := R) (y₀ := (ω₀, v₀)) (J := q - 1)
    hW6 fun j h5 hj => hF.mono fun y hy => by
      rcases Nat.lt_or_ge j (q - 1) with hlt | hge
      · exact (hy.1 j (Finset.mem_Icc.2 ⟨h5, by omega⟩)).1
      · obtain rfl : j = q - 1 := by omega
        exact hy.2.1
  have hCu : ∀ i, 5 ≤ i → i ≤ q - 1 → IsUnit (chartR W g E q R ω₀ i) :=
    fun i h5 hi => (hC i h5 hi).1
  -- the right-cavity chain
  have hK := SrcCutoff_cav_closure (g := g) (E := E) (y₀ := (ω₀, v₀)) (J := q - 7) hW6
    fun m hm => hF.mono fun y hy => hy.2.2.1 m (Finset.mem_range.2 (by omega))
  have hKu : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω₀ m) := fun m hm => (hK m hm).1
  -- `R̃`
  have hTω : ContinuousAt (fun ω => blockSeq W q ω 4 - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • R - ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) ω₀ :=
    (((((SrcCutoff_contDiff_blockSeq (k := 0) W q 4).contDiffAt).sub contDiffAt_const).sub
      contDiffAt_const).sub ((SrcCutoff_contDiffAt_cavR (k := 0) (q - 7) hKu).const_smul
      _)).continuousAt
  have hTc : ContinuousAt ((fun ω => blockSeq W q ω 4 - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • R - ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) ∘ Prod.fst)
      ((ω₀, v₀) : Ω W q × (Fin W → ℂ)) :=
    hTω.comp continuousAt_fst
  have hT := SrcCutoff_normCut_closure hW6 hTc (hF.mono fun y hy => hy.2.2.2.1)
  have hTu : IsUnit (cavRes W g E q R ω₀) := Matrix.isUnit_nonsing_inv_iff.2 hT.1
  have hT2 : hsSq (cavRes W g E q R ω₀) ≤ 2 * ((W : ℝ) ^ 6 / 2) := hT.2
  -- the active-chain matrix
  have hH := SrcCutoff_normCut_closure hW6
    ((SrcCutoff_contDiff_activeMat (k := 0) (g := g) (E := E) (R := R)).continuous.continuousAt.comp
      continuousAt_fst) (hF.mono fun y hy => hy.2.2.2.2.1)
  have hH1 : IsUnit (activeMat W g E q R ω₀) := hH.1
  have hH2 : hsSq (activeMat W g E q R ω₀)⁻¹ ≤ 2 * ((W : ℝ) ^ 6 / 2) := hH.2
  -- the gap of `A` at `t`
  have hgramd : ContDiffAt ℝ 0 (fun y : Ω W q × (Fin W → ℂ) =>
      (cavProd W g E q y.1 (q - 6))ᴴ * cavProd W g E q y.1 (q - 6)) (ω₀, v₀) :=
    (SrcCutoff_contDiffAt_gram hKu).comp (ω₀, v₀) contDiffAt_fst
  have hgram := hgramd.continuousAt
  have hG := SrcCutoff_normCut_closure hLgap (hgram.sub continuousAt_const)
    (hF.mono fun y hy => hy.2.2.2.2.2.1)
  have hG1 : IsUnit ((cavProd W g E q ω₀ (q - 6))ᴴ * cavProd W g E q ω₀ (q - 6) -
      ((c.t ^ 2 : ℝ) : ℂ) • 1) := hG.1
  -- the rank surrogate of `A* A`
  have hu : IsUnit ((cavProd W g E q ω₀ (q - 6))ᴴ * cavProd W g E q ω₀ (q - 6) +
      ((c.t ^ 2 : ℝ) : ℂ) • 1) := by
    rcases (sq_nonneg c.t).eq_or_lt with h0 | h0
    · have h1 := hG1
      rw [← h0] at h1 ⊢
      simpa using h1
    · exact SrcCutoff_isUnit_gram_add _ h0
  have hrA : rankSurr c.t ((cavProd W g E q ω₀ (q - 6))ᴴ * cavProd W g E q ω₀ (q - 6)) ≤
      2 * c.Lrk := by
    refine SrcCutoff_le_of_frequently (SrcCutoff_contDiffAt_rankSurr hgramd hu).continuousAt
      continuousAt_const (hF.mono fun y hy => ?_)
    have h2 := SrcCutoff_step.1 _ hy.2.2.2.2.2.2.1
    rw [div_lt_iff₀ hLrk] at h2
    exact h2.le
  -- the compatibility cut
  have hQ : ContDiffAt ℝ 0 (fun y : Ω W q × (Fin W → ℂ) => retProj W g E q R c.t y.1) (ω₀, v₀) :=
    ((SrcCutoff_contDiffAt_retProj hKu hTu hG1).of_le (by simp)).comp (ω₀, v₀) contDiffAt_fst
  have htr : 8 ^ c.kP * ((retProj W g E q R c.t ω₀ * (1 - P) * retProj W g E q R c.t ω₀) ^
      c.kP).trace.re ≤ 1 := by
    have hc : ContinuousAt (fun y : Ω W q × (Fin W → ℂ) => 8 ^ c.kP *
        ((retProj W g E q R c.t y.1 * (1 - P) * retProj W g E q R c.t y.1) ^
          c.kP).trace.re) (ω₀, v₀) :=
      (contDiffAt_const.mul (SrcCutoff_contDiffAt_traceRe
        (((hQ.mul contDiffAt_const).mul hQ).pow c.kP))).continuousAt
    refine SrcCutoff_le_of_frequently hc continuousAt_const (hF.mono fun y hy => ?_)
    have h2 := SrcCutoff_step.1 _ hy.2.2.2.2.2.2.2.1
    linarith
  -- the blocks
  have hB4 : hsSq (blockSeq W q ω₀ 4 - ((g : ℂ) ^ 2) • R) ≤ 2 * (W : ℝ) ^ 8 := by
    have hc : ContinuousAt (fun y : Ω W q × (Fin W → ℂ) =>
        hsSq (blockSeq W q y.1 4 - ((g : ℂ) ^ 2) • R)) (ω₀, v₀) :=
      (SrcCutoff_contDiffAt_hsSq (k := 0) ((((SrcCutoff_contDiff_blockSeq W q 4).sub
        contDiff_const).comp contDiff_fst).contDiffAt)).continuousAt
    refine SrcCutoff_le_of_frequently hc continuousAt_const (hF.mono fun y hy => ?_)
    have h2 := SrcCutoff_step.1 _ hy.2.2.2.2.2.2.2.2.1
    rw [div_lt_iff₀ hW8] at h2
    exact h2.le
  have hBi : ∀ i, 5 ≤ i → i ≤ q - 2 → hsSq (blockSeq W q ω₀ i) ≤ 2 * (W : ℝ) ^ 8 := by
    intro i h5 hi
    have hc : ContinuousAt (fun y : Ω W q × (Fin W → ℂ) => hsSq (blockSeq W q y.1 i)) (ω₀, v₀) :=
      (SrcCutoff_contDiffAt_hsSq (k := 0)
        (((SrcCutoff_contDiff_blockSeq W q i).comp contDiff_fst).contDiffAt)).continuousAt
    refine SrcCutoff_le_of_frequently hc continuousAt_const (hF.mono fun y hy => ?_)
    have h2 := SrcCutoff_step.1 _ (hy.2.2.2.2.2.2.2.2.2.1 i (Finset.mem_Icc.2 ⟨h5, hi⟩))
    rw [div_lt_iff₀ hW8] at h2
    exact h2.le
  -- the rank surrogates of the regular states
  have hrk : ∀ j, 5 ≤ j → j ≤ q - 2 →
      rankSurr g⁻¹ ((chartR W g E q R ω₀ j)ᴴ * chartR W g E q R ω₀ j) ≤ W * Real.sqrt g := by
    intro j h5 hj
    have hd : ContDiffAt ℝ 0 (fun ω => chartR W g E q R ω j) ω₀ :=
      SrcCutoff_contDiffAt_chartR j fun i h5' hi => hCu i h5' (by omega)
    have hcj : ContDiffAt ℝ 0 (fun y : Ω W q × (Fin W → ℂ) =>
        (chartR W g E q R y.1 j)ᴴ * chartR W g E q R y.1 j) (ω₀, v₀) :=
      ((SrcCutoff_contDiffAt_conjTranspose hd).mul hd).comp (ω₀, v₀) contDiffAt_fst
    have hcont := SrcCutoff_contDiffAt_rankSurr (s := g⁻¹) hcj
      (SrcCutoff_isUnit_gram_add _ (pow_pos (inv_pos.2 hg) 2))
    refine SrcCutoff_le_of_frequently hcont.continuousAt continuousAt_const (hF.mono fun y hy => ?_)
    have h2 := SrcCutoff_step.1 _ (hy.1 j (Finset.mem_Icc.2 ⟨h5, hj⟩)).2
    have hpos : (0 : ℝ) < W * Real.sqrt g := mul_pos hW0 (Real.sqrt_pos.2 hg)
    rw [div_lt_iff₀ hpos] at h2
    linarith
  -- the source conditions
  have hsnd : ContDiffAt ℝ 0 (fun y : Ω W q × (Fin W → ℂ) => y.2) (ω₀, v₀) := contDiffAt_snd
  have ha : ContinuousAt (fun y : Ω W q × (Fin W → ℂ) => ∑ i, ‖(P *ᵥ y.2) i‖ ^ 2) (ω₀, v₀) :=
    (SrcCutoff_contDiffAt_sumSq contDiffAt_const hsnd).continuousAt
  have hb : ContinuousAt (fun y : Ω W q × (Fin W → ℂ) => ∑ i, ‖y.2 i‖ ^ 2) (ω₀, v₀) :=
    (ContDiffAt.sum fun i _ => (contDiffAt_pi.1 hsnd i).norm_sq ℝ).continuousAt
  have hPv : ContDiffAt ℝ 0 (fun y : Ω W q × (Fin W → ℂ) => P *ᵥ y.2) (ω₀, v₀) := by
    rw [contDiffAt_pi]
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact ContDiffAt.sum fun j _ => contDiffAt_const.mul (contDiffAt_pi.1 hsnd j)
  have hE24 : ∀ y : Ω W q × (Fin W → ℂ),
      stepUp (2 * (W : ℝ) ^ 20 * (∑ i, ‖(P *ᵥ y.2) i‖ ^ 2) / ∑ i, ‖y.2 i‖ ^ 2) ≠ 0 →
      0 < ∑ i, ‖(P *ᵥ y.2) i‖ ^ 2 ∧
        ∑ i, ‖y.2 i‖ ^ 2 ≤ 2 * (W : ℝ) ^ 20 * ∑ i, ‖(P *ᵥ y.2) i‖ ^ 2 := by
    intro y h
    obtain ⟨hb0, hlt⟩ := SrcCutoff_of_one_lt_div (by positivity) (SrcCutoff_step.2.1 _ h)
    refine ⟨?_, hlt.le⟩
    rcases (show (0 : ℝ) ≤ ∑ i, ‖(P *ᵥ y.2) i‖ ^ 2 by positivity).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at hlt
      linarith
    · exact h0
  have h11 : ∑ i, ‖v₀ i‖ ^ 2 ≤ 2 * (W : ℝ) ^ 20 * ∑ i, ‖(P *ᵥ v₀) i‖ ^ 2 :=
    SrcCutoff_le_of_frequently hb (continuousAt_const.mul ha)
      (hF.mono fun y hy => (hE24 y hy.2.2.2.2.2.2.2.2.2.2.1).2)
  have h12 : ∑ i, ‖(retProj W g E q R c.t ω₀ *ᵥ v₀) i‖ ^ 2 ≤
      2 * c.Lov * ∑ i, ‖(P *ᵥ v₀) i‖ ^ 2 := by
    refine SrcCutoff_le_of_frequently (SrcCutoff_contDiffAt_sumSq hQ hsnd).continuousAt
      (continuousAt_const.mul ha) (hF.mono fun y hy => ?_)
    have ha0 := (hE24 y hy.2.2.2.2.2.2.2.2.2.2.1).1
    have h2 := SrcCutoff_step.1 _ hy.2.2.2.2.2.2.2.2.2.2.2.1
    rw [div_lt_iff₀ (mul_pos hLov ha0)] at h2
    simp only [Pi.mul_apply]
    linarith
  have h13 : 8 * ∑ i, ‖(retProj W g E q R c.t ω₀ *ᵥ (P *ᵥ v₀)) i‖ ^ 2 ≤
      ∑ i, ‖(P *ᵥ v₀) i‖ ^ 2 := by
    refine SrcCutoff_le_of_frequently
      (continuousAt_const.mul (SrcCutoff_contDiffAt_sumSq hQ hPv).continuousAt) ha
      (hF.mono fun y hy => ?_)
    have ha0 := (hE24 y hy.2.2.2.2.2.2.2.2.2.2.1).1
    have h2 := SrcCutoff_step.1 _ hy.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [div_lt_iff₀ ha0] at h2
    simp only [Pi.mul_apply]
    linarith
  have h14 : c.kOut ^ 2 * ∑ i, ‖(P *ᵥ v₀) i‖ ^ 2 ≤
      ∑ i, ‖(chartProd W g E q R ω₀ (q - 1) *ᵥ v₀) i‖ ^ 2 := by
    have hRv : ContDiffAt ℝ 0 (fun y : Ω W q × (Fin W → ℂ) => chartProd W g E q R y.1 (q - 1))
        (ω₀, v₀) :=
      (SrcCutoff_contDiffAt_chartProd (q - 1) hCu).comp (ω₀, v₀) contDiffAt_fst
    refine SrcCutoff_le_of_frequently (continuousAt_const.mul ha)
      (SrcCutoff_contDiffAt_sumSq hRv hsnd).continuousAt (hF.mono fun y hy => ?_)
    exact (SrcCutoff_of_one_lt_div (by positivity)
      (SrcCutoff_step.2.1 _ hy.2.2.2.2.2.2.2.2.2.2.2.2.2)).2.le
  refine ⟨fun j h5 hj => ⟨(hC j h5 (by omega)).1, by linarith [(hC j h5 (by omega)).2],
      hrk j h5 hj⟩,
    ⟨(hC (q - 1) (by omega) le_rfl).1, by linarith [(hC (q - 1) (by omega) le_rfl).2]⟩,
    fun m hm => ⟨(hK m hm).1, by linarith [(hK m hm).2]⟩, ⟨hTu, by linarith⟩,
    ⟨hH1, by linarith⟩, hG, hrA, htr, hB4, hBi, h11, h12, h13, h14⟩

/-- The cutoff takes values in `[0, 1]` and equals one on `CutPlat`. -/
theorem srcCut_eq_one {W q : ℕ} {g E : ℝ} (hW : 1 ≤ W) (hg : 0 < g)
    (R P : Matrix (Fin W) (Fin W) ℂ) {c : CutLevels} (hLov : 0 < c.Lov) (hLrk : 0 < c.Lrk)
    (hLgap : 0 < c.Lgap) (hkOut : 0 < c.kOut) (ω : Ω W q) (v : Fin W → ℂ) :
    (0 ≤ srcCut W g E q R P c ω v ∧ srcCut W g E q R P c ω v ≤ 1) ∧
      (CutPlat W g E q R P c ω v → srcCut W g E q R P c ω v = 1) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hW6 : (0 : ℝ) < (W : ℝ) ^ 6 / 2 := by positivity
  refine ⟨?_, fun h => ?_⟩
  · unfold srcCut matCut srcCutV regCut
    repeat' first
      | exact SrcCutoff_normCut_mem _ _
      | exact SrcCutoff_step.2.2.1 _
      | exact SrcCutoff_step.2.2.2.1 _
      | apply SrcCutoff_mem_mul
      | (apply SrcCutoff_mem_prod; intro i _)
  · obtain ⟨⟨hC, hq1, hK, hT, hB4, hBi⟩, hH, hgap, hrk, htr, hPv, hE24, hov, hQP, hout⟩ := h
    have ha := SrcCutoff_sumSq_pos hPv
    have hv : v ≠ 0 := by
      rintro rfl
      exact hPv (Matrix.mulVec_zero P)
    have hb := SrcCutoff_sumSq_pos hv
    have hWg : (0 : ℝ) < W * Real.sqrt g := mul_pos hW0 (Real.sqrt_pos.2 hg)
    have hW8 : (0 : ℝ) < (W : ℝ) ^ 8 := by positivity
    have e1 : ∏ j ∈ Finset.Icc 5 (q - 2), regCut W g (chartR W g E q R ω j) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      obtain ⟨h5, hj'⟩ := Finset.mem_Icc.1 hj
      obtain ⟨hu, hs, hr⟩ := hC j h5 hj'
      unfold regCut
      rw [SrcCutoff_normCut_eq_one hW6 hu hs,
        SrcCutoff_step.2.2.2.2.1 _ ((div_le_one hWg).2 hr), one_mul]
    have e2 : normCut ((W : ℝ) ^ 6 / 2) (chartR W g E q R ω (q - 1)) = 1 :=
      SrcCutoff_normCut_eq_one hW6 hq1.1 hq1.2
    have e3 : ∏ m ∈ Finset.range (q - 6), normCut ((W : ℝ) ^ 6 / 2) (cavR W g E q ω m) = 1 := by
      refine Finset.prod_eq_one fun m hm => ?_
      have hm' : m ≤ q - 7 := by
        have := Finset.mem_range.1 hm
        omega
      exact SrcCutoff_normCut_eq_one hW6 (hK m hm').1 (hK m hm').2
    have e4 : normCut ((W : ℝ) ^ 6 / 2) (cavRes W g E q R ω) = 1 :=
      SrcCutoff_normCut_eq_one hW6 hT.1 hT.2
    have e5 : normCut ((W : ℝ) ^ 6 / 2) (activeMat W g E q R ω)⁻¹ = 1 :=
      (normCut_inv_spec hW6).2.2.1 _ hH.1 hH.2
    have e6 : normCut c.Lgap ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) -
        ((c.t ^ 2 : ℝ) : ℂ) • 1)⁻¹ = 1 :=
      (normCut_inv_spec hLgap).2.2.1 _ hgap.1 hgap.2
    have e7 : stepDown (rankSurr c.t ((cavProd W g E q ω (q - 6))ᴴ *
        cavProd W g E q ω (q - 6)) / c.Lrk) = 1 :=
      SrcCutoff_step.2.2.2.2.1 _ ((div_le_one hLrk).2 hrk)
    have e8 : stepDown (2 * 8 ^ c.kP * ((retProj W g E q R c.t ω * (1 - P) *
        retProj W g E q R c.t ω) ^ c.kP).trace.re) = 1 :=
      SrcCutoff_step.2.2.2.2.1 _ htr
    have e9 : stepDown (hsSq (blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R) / (W : ℝ) ^ 8) = 1 :=
      SrcCutoff_step.2.2.2.2.1 _ ((div_le_one hW8).2 hB4)
    have e10 : ∏ i ∈ Finset.Icc 5 (q - 2), stepDown (hsSq (blockSeq W q ω i) / (W : ℝ) ^ 8) = 1 :=
      Finset.prod_eq_one fun i hi => SrcCutoff_step.2.2.2.2.1 _
        ((div_le_one hW8).2 (hBi i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2))
    have e11 : stepUp (2 * (W : ℝ) ^ 20 * (∑ i, ‖(P *ᵥ v) i‖ ^ 2) / ∑ i, ‖v i‖ ^ 2) = 1 :=
      SrcCutoff_step.2.2.2.2.2 _ (by rw [le_div_iff₀ hb]; linarith)
    have e12 : stepDown ((∑ i, ‖(retProj W g E q R c.t ω *ᵥ v) i‖ ^ 2) /
        (c.Lov * ∑ i, ‖(P *ᵥ v) i‖ ^ 2)) = 1 :=
      SrcCutoff_step.2.2.2.2.1 _ ((div_le_one (mul_pos hLov ha)).2 hov)
    have e13 : stepDown (16 * (∑ i, ‖(retProj W g E q R c.t ω *ᵥ (P *ᵥ v)) i‖ ^ 2) /
        ∑ i, ‖(P *ᵥ v) i‖ ^ 2) = 1 :=
      SrcCutoff_step.2.2.2.2.1 _ ((div_le_one ha).2 hQP)
    have e14 : stepUp ((∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2) /
        (c.kOut ^ 2 * ∑ i, ‖(P *ᵥ v) i‖ ^ 2)) = 1 :=
      SrcCutoff_step.2.2.2.2.2 _ (by rw [le_div_iff₀ (by positivity)]; linarith)
    unfold srcCut matCut srcCutV
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]
    norm_num

/-- On `CutSupp`, the states `R_5, …, R_{q-2}` are regular (9.3) [us:eq:regular]. -/
theorem cutSupp_regular {W q : ℕ} {g E : ℝ} (hW : 1 ≤ W) (hg : 0 < g)
    {R : Matrix (Fin W) (Fin W) ℂ} (hR : R.IsHermitian) {P : Matrix (Fin W) (Fin W) ℂ}
    {c : CutLevels} {ω : Ω W q} {v : Fin W → ℂ} (h : CutSupp W g E q R P c ω v) :
    ∀ j, 5 ≤ j → j ≤ q - 2 → IsRegularState W g (chartR W g E q R ω j) := by
  intro j h5 hj
  obtain ⟨hC, -⟩ := h
  obtain ⟨-, hhs, hrk⟩ := hC j h5 hj
  have hH := SrcCutoff_chartR_isHermitian (g := g) (E := E) hR ω j
  refine ⟨hH, ?_, ?_⟩
  · calc ‖chartR W g E q R ω j‖ ≤ Real.sqrt (hsSq (chartR W g E q R ω j)) :=
          SrcCutoff_norm_le_sqrt_hsSq _
      _ ≤ Real.sqrt ((W : ℝ) ^ 6) := Real.sqrt_le_sqrt hhs
      _ = (W : ℝ) ^ 3 := by
          rw [show (W : ℝ) ^ 6 = ((W : ℝ) ^ 3) ^ 2 by ring]
          exact Real.sqrt_sq (by positivity)
  · calc (countIn (((g : ℂ) ^ 2) • chartR W g E q R ω j) {x | g < |x|} : ℝ)
        ≤ countIn ((chartR W g E q R ω j)ᴴ * chartR W g E q R ω j) (Set.Ioi (g⁻¹ ^ 2)) := by
          exact_mod_cast SrcCutoff_countIn_le hH hg
      _ ≤ rankSurr g⁻¹ ((chartR W g E q R ω j)ᴴ * chartR W g E q R ω j) :=
          (countIn_le_rankSurr _ (inv_pos.2 hg) two_pos le_rfl).1
      _ ≤ W * Real.sqrt g := hrk

/-- The retained projection is smooth on the invariant open set of Section 9.4.4
[su:sec:cutoff-estimates] where the right-cavity inverses and `R̃` exist and `t²` is not an
eigenvalue of `A* A`. -/
theorem contDiffOn_retProj {W q : ℕ} (hq : 7 ≤ q) (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (t : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ω : Ω W q => retProj W g E q R t ω)
      {ω | (∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m)) ∧ IsUnit (cavRes W g E q R ω) ∧
        IsUnit ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) -
          ((t ^ 2 : ℝ) : ℂ) • 1)} := by
  intro ω hω
  exact (SrcCutoff_contDiffAt_retProj hω.1 hω.2.1 hω.2.2).contDiffWithinAt

end LSBA
