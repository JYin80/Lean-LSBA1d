import LSBA.Upper.ChosenGenerator
import LSBA.Spectral.SpecProj
import LSBA.Upper.SrcCutoffReg
import LSBA.Upper.SrcCutoffCost
import LSBA.Upper.CutoffMassWeak
import LSBA.Upper.CutoffMassCrit
import LSBA.Upper.Preparation
import LSBA.Upper.PrepMeasure
import LSBA.Gauss.PrefixEvent

/-!
# Lemma 9.3 [su:lem:chosen-generator]: existence of the cutoff and the generator

Lemma 9.3 [su:lem:chosen-generator] in the two regimes of Lemma 8.12
[up:lem:small-contraction], with `J = [-2 + κ₀, 2 - κ₀]` and `P` of (9.4)
[su:eq:source-projection]. Regime (i): for `0 < α < β < 1/2` there is `ε₀ > 0` such that for
`0 < ε ≤ ε₀` (Section 9.2 [su:sec:generator-choice]: `ε` may be taken small in terms of
`α, β`) and `g = W^{-a}`, `a ∈ [α, β]`, the predicate `ChosenGenerator` holds with
`P = 1_{[-W^{ε/800}, W^{ε/800}]}(g² R_4)`, `σ = g² W^{ε/4}` and `M₀ = W^{ε/800}`. Regime (ii):
for `c_* > 0`, `0 < θ ≤ 1/100` and `c_* W^{-1/2} ≤ g ≤ W^{-1/2+θ/2}` ((8.37)
[eq:critical-window]), it holds with `P = 1`, `σ = W^{-1+14θ}` and `M₀ = C W^{2θ}`. The local
length `q ≥ 7`, the constant and the width threshold depend only on the fixed parameters.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Block `i` of the sample depends only on the coordinates of block `i`. -/
private lemma chosenGeneratorExists_gueBlock_congr {W q : ℕ} {ω ω' : Ω W q} {i : Fin q}
    (h : ∀ α β : Fin W, ω (i, α, β) = ω' (i, α, β)) : gueBlock W q ω i = gueBlock W q ω' i := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, h]

/-- Block `i` of the sample is continuous in the sample. -/
private lemma chosenGeneratorExists_continuous_gueBlock {W q : ℕ} (i : Fin q) :
    Continuous fun ω : Ω W q => gueBlock W q ω i := by
  refine continuous_matrix fun α β => ?_
  have hc : ∀ p : Fin q × Fin W × Fin W, Continuous fun ω : Ω W q => ((ω p : ℝ) : ℂ) :=
    fun p => Complex.continuous_ofReal.comp (continuous_apply p)
  simp only [gueBlock, Matrix.of_apply]
  split_ifs
  · exact (hc _).div_const _
  · exact ((hc _).add (continuous_const.mul (hc _))).div_const _
  · exact ((hc _).sub (continuous_const.mul (hc _))).div_const _

/-- The graph coordinates `R_j` and the products `R_{[j,5]}` of (9.2) [su:eq:transported-normal]
at a fixed `R_4` do not depend on the blocks `0, 1, 2, 3`. -/
private lemma chosenGeneratorExists_chart_congr {W q : ℕ} {g E : ℝ}
    {R : Matrix (Fin W) (Fin W) ℂ} {ω ω' : Ω W q}
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → gueBlock W q ω i = gueBlock W q ω' i) :
    ∀ j, chartR W g E q R ω j = chartR W g E q R ω' j ∧
      chartProd W g E q R ω j = chartProd W g E q R ω' j
  | 0 => by simp [chartR, chartProd]
  | j + 1 => by
    obtain ⟨ih1, ih2⟩ := chosenGeneratorExists_chart_congr (g := g) (E := E) (R := R) h j
    by_cases h4 : j < 4
    · simp [chartR, chartProd, h4]
    · have hb : blockSeq W q ω j = blockSeq W q ω' j := by
        unfold blockSeq
        split_ifs with hjq
        · exact h ⟨j, hjq⟩ (by simp only; omega)
        · rfl
      have hR : chartR W g E q R ω (j + 1) = chartR W g E q R ω' (j + 1) := by
        simp only [chartR, h4, ↓reduceIte, hb, ih1]
      refine ⟨hR, ?_⟩
      simp only [chartProd, h4, ↓reduceIte]
      rw [hR, ih2]

/-- The matrix inverse `M ↦ M⁻¹ = det(M)⁻¹ adj(M)` is Borel. -/
private lemma chosenGeneratorExists_measurable_inv {W : ℕ} :
    Measurable fun M : Matrix (Fin W) (Fin W) ℂ => M⁻¹ := by
  have h : (fun M : Matrix (Fin W) (Fin W) ℂ => M⁻¹) = fun M => Ring.inverse M.det • M.adjugate :=
    funext Matrix.inv_def
  rw [h, Ring.inverse_eq_inv']
  exact ((Continuous.matrix_det continuous_id).measurable.inv).smul
    (Continuous.matrix_adjugate continuous_id).measurable

/-- `R_j` of (9.2) [su:eq:transported-normal] is jointly measurable in `(R_4, ω)`. -/
private lemma chosenGeneratorExists_measurable_chartR {W q : ℕ} {α : Type*} [MeasurableSpace α]
    (g E : ℝ) {R : α → Matrix (Fin W) (Fin W) ℂ} {ω : α → Ω W q} (hR : Measurable R)
    (hω : Measurable ω) : ∀ j, Measurable fun y => chartR W g E q (R y) (ω y) j
  | 0 => by
    simp only [chartR]
    exact hR
  | j + 1 => by
    by_cases hj : j < 4
    · simp only [chartR, hj, ↓reduceIte]
      exact hR
    · simp only [chartR, hj, ↓reduceIte]
      have hb : Measurable fun y => blockSeq W q (ω y) j := by
        unfold blockSeq
        split_ifs with hjq
        · exact (chosenGeneratorExists_continuous_gueBlock _).measurable.comp hω
        · exact measurable_const
      have hc : Measurable fun y => ((g : ℂ) ^ 2) • chartR W g E q (R y) (ω y) j :=
        (continuous_const_smul ((g : ℂ) ^ 2)).measurable.comp
          (chosenGeneratorExists_measurable_chartR g E hR hω j)
      exact chosenGeneratorExists_measurable_inv.comp ((hb.sub measurable_const).sub hc)

/-- `R_{[j,5]}` of (9.2) [su:eq:transported-normal] is jointly measurable in `(R_4, ω)`. -/
private lemma chosenGeneratorExists_measurable_chartProd {W q : ℕ} {α : Type*}
    [MeasurableSpace α] (g E : ℝ) {R : α → Matrix (Fin W) (Fin W) ℂ} {ω : α → Ω W q}
    (hR : Measurable R) (hω : Measurable ω) :
    ∀ j, Measurable fun y => chartProd W g E q (R y) (ω y) j
  | 0 => by
    simp only [chartProd]
    exact measurable_const
  | j + 1 => by
    by_cases hj : j < 4
    · simp only [chartProd, hj, ↓reduceIte]
      exact measurable_const
    · simp only [chartProd, hj, ↓reduceIte]
      exact (chosenGeneratorExists_measurable_chartR g E hR hω (j + 1)).mul
        (chosenGeneratorExists_measurable_chartProd g E hR hω j)

/-- The count of eigenvalues in a set is at most the dimension. -/
private lemma chosenGeneratorExists_countIn_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (J : Set ℝ) : (countIn A J : ℝ) ≤ W := by
  have h : countIn A J ≤ W := by
    unfold countIn
    split_ifs
    · exact (Finset.card_filter_le _ _).trans (by simp)
    · exact Nat.zero_le _
  exact_mod_cast h

/-- For `W ≥ 1` and `0 < g ≤ 1`, the regular states (9.3) [us:eq:regular] form a Borel set. -/
private lemma chosenGeneratorExists_measurableSet_regular {W : ℕ} (hW : 1 ≤ W) {g : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) :
    MeasurableSet {X : Matrix (Fin W) (Fin W) ℂ | IsRegularState W g X} := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hset : {X : Matrix (Fin W) (Fin W) ℂ | IsRegularState W g X} =
      (fun X => (X, (0 : Fin W → ℂ))) ⁻¹' PrepGoodCrit W g 2 := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, PrepGoodCrit]
    constructor
    · intro hX
      have hn : ‖X‖ ≤ (W : ℝ) ^ 3 := hX.2.1
      have h3 : (W : ℝ) ^ (1 + 2 : ℝ) = (W : ℝ) ^ 3 := by norm_num
      have h6 : (W : ℝ) ≤ (W : ℝ) ^ (3 * 2 : ℝ) := by
        calc (W : ℝ) = (W : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (W : ℝ) ^ (3 * 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
      have h4 : (W : ℝ) ^ 3 ≤ (W : ℝ) ^ (2 * 2 : ℝ) := by
        rw [show (2 * 2 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
        exact pow_le_pow_right₀ hW1 (by norm_num)
      have hg2 : g ^ 2 ≤ 1 := pow_le_one₀ hg.le hg1
      refine ⟨hX, h3 ▸ hn, (chosenGeneratorExists_countIn_le _ _).trans h6, ?_⟩
      calc g ^ 2 * ‖X‖ ≤ 1 * (W : ℝ) ^ 3 := by gcongr
        _ ≤ (W : ℝ) ^ (2 * 2 : ℝ) := by rw [one_mul]; exact h4
    · exact fun h => h.1
  rw [hset]
  exact (measurableSet_prepGood W g 0 0 2).2.preimage (measurable_id.prodMk measurable_const)

/-- The proof of Lemma 9.3 [su:lem:chosen-generator] (Section 9.4 [su:sec:construction-estimates])
at given levels `c` and a
measurable set `G` of prepared data: with `pre = 1` on the prepared chart with `(R_4, v_4) ∈ G`,
the generator `K̂ = smallGen` and the cutoff `χ̂ = srcCut`, the predicate `ChosenGenerator` holds
once `C ≥ C₀`, the level rows hold, `M₀` bounds `g² ‖P R_4 P‖` on `G`, `P(pre = 0) ≤ 1/3`, the
plateau of the cutoff fails with probability `≤ 1/4` at every datum of `G`, and the output event
of (9.68) [us:eq:profile] has probability `≤ W^{-26}` at every datum of `G`. -/
private lemma chosenGeneratorExists_assembly : ∃ C₀ : ℝ, 64 ≤ C₀ ∧
    ∀ {W q : ℕ} {g E C σ M₀ : ℝ} {x : IsoFlag W}
      {Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} {c : CutLevels}
      {G : Set (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ))},
      1 ≤ W → 7 ≤ q → 0 < g → g ≤ 1 → MeasurableSet G → Measurable Pf →
      (∀ R : Matrix (Fin W) (Fin W) ℂ, R.IsHermitian →
        (Pf R).IsHermitian ∧ Pf R * Pf R = Pf R ∧ Pf R * R = R * Pf R) →
      (∀ (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ), (R, v) ∈ G → R.IsHermitian →
        g ^ 2 * ‖Pf R * R * Pf R‖ ≤ M₀) →
      0 < c.t → 0 < c.Lov → 64 * c.Lov ≤ 1 → 0 < c.kOut → 1 ≤ c.kP → 0 < c.Lrk → 0 < c.Lgap →
      32 * c.t ^ 2 * (W : ℝ) ^ 34 ≤ c.kOut ^ 2 →
      2 * c.t ^ 2 * (W : ℝ) ^ 26 * (c.kOut ^ 2 + (W : ℝ) ^ 6 / g ^ (2 * (q - 6))) ≤
        c.kOut ^ 4 →
      (W : ℝ) ^ 6 / (g ^ (2 * (q - 6)) * c.kOut ^ 2) ≤ (W : ℝ) ^ 26 →
      4 * c.Lrk + 1 ≤ C * W * σ → 64 * c.Lov ≤ C * σ → C₀ ≤ C →
      μ W q {ω | ¬ (PrepOK W g E q x ω ∧
          (prepR W g E q x ω 4, prepV W g E q x ω 4) ∈ G)} ≤ ENNReal.ofReal (1 / 3) →
      (∀ (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ), (R, v) ∈ G → v ≠ 0 →
        μ W q {ω | ¬ CutPlat W g E q R (Pf R) c ω v} ≤ ENNReal.ofReal (1 / 4)) →
      (∀ (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ), (R, v) ∈ G →
        μ W q {ω | (∀ j, 5 ≤ j → j ≤ q - 2 → IsRegularState W g (chartR W g E q R ω j)) ∧
          ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 <
            2 * c.kOut ^ 2 * ∑ i, ‖(Pf R *ᵥ v) i‖ ^ 2} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-(26 : ℝ)))) →
      ChosenGenerator W q g E x Pf C σ M₀ (prepInd W g E q x G)
        (fun ω => prepR W g E q x ω 4) (fun ω => prepV W g E q x ω 4)
        (fun R ω w => smallGen W g E q R c.t (Pf R) ω w)
        (fun R ω w => srcCut W g E q R (Pf R) c ω w) := by
  obtain ⟨C₁, hC₁, hpt⟩ := genPoint_of_cutSupp
  obtain ⟨C₂, hC₂, hcost⟩ := srcCut_cost_le
  refine ⟨max (max C₁ (2 * C₂)) 64, le_max_right _ _, ?_⟩
  intro W q g E C σ M₀ x Pf c G hW hq hg hg1 hG hPf hPs hM₀ ht hLov h64 hkOut hkP hLrk hLgap
    herr hprod hratio hrk hσ hC hprep hplat hout
  have : NeZero W := ⟨by omega⟩
  have hC1 : C₁ ≤ C := (le_max_left _ _).trans ((le_max_left _ _).trans hC)
  have hC2 : 2 * C₂ ≤ C := (le_max_right _ _).trans ((le_max_left _ _).trans hC)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨h01, hmpre, hmR, hmv, hpref, hchart⟩ := prepInd_spec (E := E) (q := q) hg hg1 x hG
  set pre := prepInd W g E q x G with hpre_def
  set Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ := fun ω => prepR W g E q x ω 4 with hRf_def
  set vf : Ω W q → Fin W → ℂ := fun ω => prepV W g E q x ω 4 with hvf_def
  -- the prepared set `S = {pre = 1}`
  have hpre_iff : ∀ ω, pre ω = 1 ↔ (PrepOK W g E q x ω ∧ (Rf ω, vf ω) ∈ G) := by
    intro ω
    simp only [hpre_def, prepInd, hRf_def, hvf_def]
    split_ifs with h <;> simp [h]
  have hpre1 : ∀ ω, pre ω ≠ 0 → pre ω = 1 := fun ω h => (h01 ω).resolve_left h
  have hfam : ∀ R : Matrix (Fin W) (Fin W) ℂ, R.IsHermitian →
      GenFamily W q g E (Pf R) R (fun ω w => smallGen W g E q R c.t (Pf R) ω w)
        (fun ω w => srcCut W g E q R (Pf R) c ω w) := fun R hR =>
    genFamily_srcCut hW hq hg hg1 hR (hPs R hR).1 (hPs R hR).2.1 (hPs R hR).2.2 ht hLov h64
      hkOut hkP hLrk hLgap herr
  have hχ01 : ∀ (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) (v : Fin W → ℂ),
      0 ≤ srcCut W g E q R (Pf R) c ω v ∧ srcCut W g E q R (Pf R) c ω v ≤ 1 := fun R ω v =>
    (srcCut_eq_one hW hg R (Pf R) hLov hLrk hLgap hkOut ω v).1
  -- the pointwise clauses on the support
  have hsupp : ∀ ω, pre ω * srcCut W g E q (Rf ω) (Pf (Rf ω)) c ω (vf ω) ≠ 0 →
      GenPoint W q g E (Pf (Rf ω)) (Rf ω) (vf ω) C M₀ σ
        (fun w => smallGen W g E q (Rf ω) c.t (Pf (Rf ω)) ω w) ω ∧
      hsSq (smallGen W g E q (Rf ω) c.t (Pf (Rf ω)) ω (vf ω)) ≤ 64 * c.Lov := by
    intro ω hne
    have hp : pre ω ≠ 0 := left_ne_zero_of_mul hne
    have hχ : srcCut W g E q (Rf ω) (Pf (Rf ω)) c ω (vf ω) ≠ 0 := right_ne_zero_of_mul hne
    obtain ⟨hR, hv, -⟩ := hchart ω hp
    have hGω : (Rf ω, vf ω) ∈ G := ((hpre_iff ω).1 (hpre1 ω hp)).2
    obtain ⟨hPh, hPP, -⟩ := hPs _ hR
    have hcs : CutSupp W g E q (Rf ω) (Pf (Rf ω)) c ω (vf ω) :=
      srcCut_tsupport hW hq hg hR (Pf (Rf ω)) hLov hLrk hLgap hkOut (ω, vf ω)
        (subset_tsupport _ hχ) hv
    exact hpt hW hq hg hg1 hR hPh hPP hv ht hLov h64 hkOut hkP herr hprod hrk hC1
      (hM₀ _ _ hGω hR) hcs
  -- prefix data
  have hblk_lt : ∀ ω ω' : Ω W q, (∀ y : Fin q × Fin W × Fin W, (y.1 : ℕ) < 4 → ω y = ω' y) →
      ∀ i : Fin q, (i : ℕ) < 4 → gueBlock W q ω i = gueBlock W q ω' i :=
    fun ω ω' h i hi => chosenGeneratorExists_gueBlock_congr fun α β => h (i, α, β) hi
  have hblk_ge : ∀ ω ω' : Ω W q, (∀ y : Fin q × Fin W × Fin W, 4 ≤ (y.1 : ℕ) → ω y = ω' y) →
      ∀ i : Fin q, 4 ≤ (i : ℕ) → gueBlock W q ω i = gueBlock W q ω' i :=
    fun ω ω' h i hi => chosenGeneratorExists_gueBlock_congr fun α β => h (i, α, β) hi
  set S : Set (Ω W q) := {ω | pre ω = 1} with hS_def
  have hSm : MeasurableSet S := measurableSet_eq_fun hmpre measurable_const
  set D : Ω W q → Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) := fun ω => (Rf ω, vf ω) with hD_def
  have hDm : Measurable D := hmR.prodMk hmv
  have hDa : PrefixData W q 4 D := by
    intro ω ω' h
    obtain ⟨-, h2, h3⟩ := hpref ω ω' (hblk_lt ω ω' h)
    simp only [hD_def, hRf_def, hvf_def, h2, h3]
  have hSa : PrefixData W q 4 (· ∈ S) := by
    intro ω ω' h
    obtain ⟨h1, -, -⟩ := hpref ω ω' (hblk_lt ω ω' h)
    exact congrArg (fun r : ℝ => r = 1) h1
  have hS_mem : ∀ ω ∈ S, (Rf ω).IsHermitian ∧ vf ω ≠ 0 ∧ (Rf ω, vf ω) ∈ G := by
    intro ω hω
    have hω' : pre ω = 1 := hω
    obtain ⟨hR, hv, -⟩ := hchart ω (by rw [hω']; exact one_ne_zero)
    exact ⟨hR, hv, ((hpre_iff ω).1 hω').2⟩
  have hμS : (2 / 3 : ℝ) ≤ (μ W q).real S := by
    have hc : Sᶜ = {ω | ¬ (PrepOK W g E q x ω ∧
        (prepR W g E q x ω 4, prepV W g E q x ω 4) ∈ G)} := by
      ext ω
      simp only [Set.mem_compl_iff, hS_def, Set.mem_ofPred_eq, hpre_iff]
      exact Iff.rfl
    have h1 : (μ W q).real Sᶜ ≤ 1 / 3 := by
      rw [measureReal_def, hc]
      exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hprep
    have h2 := probReal_add_probReal_compl (μ := μ W q) hSm
    linarith
  have hmulVec : ∀ {A : (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) × Ω W q →
      Matrix (Fin W) (Fin W) ℂ} {u : (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) × Ω W q → Fin W → ℂ},
      Measurable A → Measurable u → Measurable fun p => A p *ᵥ u p :=
    fun hA hu => (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp
      (hA.prodMk hu)
  have hm1 : Measurable fun p : (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) × Ω W q => p.1.1 :=
    measurable_fst.comp measurable_fst
  have hm2 : Measurable fun p : (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) × Ω W q => p.1.2 :=
    measurable_snd.comp measurable_fst
  -- the mass `𝔼 χ ≥ 1/2`
  have hmass : (1 / 2 : ℝ) ≤
      ∫ ω, pre ω * srcCut W g E q (Rf ω) (Pf (Rf ω)) c ω (vf ω) ∂(μ W q) := by
    set T₁ : Set ((Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) × Ω W q) :=
      {p | p.1.1.IsHermitian ∧ srcCut W g E q p.1.1 (Pf p.1.1) c p.2 p.1.2 < 1} with hT₁_def
    have hHerm : MeasurableSet {X : Matrix (Fin W) (Fin W) ℂ | X.IsHermitian} :=
      (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
    have hT₁m : MeasurableSet T₁ :=
      (hHerm.preimage hm1).inter (measurableSet_lt ((measurable_srcCut W g E q c hPf).comp
        (hm1.prodMk (measurable_snd.prodMk hm2))) measurable_const)
    have hT₁a : ∀ (d : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) (ω ω' : Ω W q),
        (∀ y : Fin q × Fin W × Fin W, 4 ≤ (y.1 : ℕ) → ω y = ω' y) →
        ((d, ω) ∈ T₁ ↔ (d, ω') ∈ T₁) := by
      intro d ω ω' h
      by_cases hR : d.1.IsHermitian
      · have he : srcCut W g E q d.1 (Pf d.1) c ω d.2 = srcCut W g E q d.1 (Pf d.1) c ω' d.2 :=
          ((hfam d.1 hR).1 ω ω' (fun i hi _ => hblk_ge ω ω' h i hi) d.2).2
        simp only [hT₁_def, Set.mem_ofPred_eq, hR, true_and]
        rw [he]
      · simp only [hT₁_def, Set.mem_ofPred_eq, hR, false_and]
    have hb₁ : ∀ ω ∈ S, μ W q {ω' | (D ω, ω') ∈ T₁} ≤ ENNReal.ofReal (1 / 4) := by
      intro ω hω
      obtain ⟨-, hv, hGω⟩ := hS_mem ω hω
      refine (measure_mono ?_).trans (hplat _ _ hGω hv)
      intro ω' hω' hpl
      have h1 := (srcCut_eq_one hW hg (Rf ω) (Pf (Rf ω)) hLov hLrk hLgap hkOut ω' (vf ω)).2 hpl
      have h2 : srcCut W g E q (Rf ω) (Pf (Rf ω)) c ω' (vf ω) < 1 := hω'.2
      linarith
    have hB₁ := measure_prefix_le W q 4 hDm hDa hSm hSa hT₁m hT₁a hb₁
    set B₁ : Set (Ω W q) := {ω | ω ∈ S ∧ (D ω, ω) ∈ T₁} with hB₁_def
    have hB₁m : MeasurableSet B₁ := hSm.inter (hT₁m.preimage (hDm.prodMk measurable_id))
    have hB₁r : (μ W q).real B₁ ≤ 1 / 4 * (μ W q).real S := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top _ _)) hB₁
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at this
    have hχm : Measurable fun ω => srcCut W g E q (Rf ω) (Pf (Rf ω)) c ω (vf ω) :=
      (measurable_srcCut W g E q c hPf).comp (f := fun ω => (Rf ω, ω, vf ω))
        (hmR.prodMk (measurable_id.prodMk hmv))
    have hf_meas : Measurable fun ω => pre ω * srcCut W g E q (Rf ω) (Pf (Rf ω)) c ω (vf ω) :=
      hmpre.mul hχm
    have hf_int : Integrable
        (fun ω => pre ω * srcCut W g E q (Rf ω) (Pf (Rf ω)) c ω (vf ω)) (μ W q) := by
      refine Integrable.of_bound hf_meas.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω => ?_)
      obtain ⟨h0, h1⟩ := hχ01 (Rf ω) ω (vf ω)
      rcases h01 ω with h | h <;> simp [h, abs_of_nonneg h0, h1]
    have hlow : ∀ ω, S.indicator (1 : Ω W q → ℝ) ω - B₁.indicator 1 ω ≤
        pre ω * srcCut W g E q (Rf ω) (Pf (Rf ω)) c ω (vf ω) := by
      intro ω
      obtain ⟨h0, -⟩ := hχ01 (Rf ω) ω (vf ω)
      by_cases hω : ω ∈ S
      · have hω' : pre ω = 1 := hω
        rw [Set.indicator_of_mem hω, hω', one_mul]
        by_cases hb : ω ∈ B₁
        · rw [Set.indicator_of_mem hb]
          simpa using h0
        · rw [Set.indicator_of_notMem hb]
          have hRω : (Rf ω).IsHermitian := (hS_mem ω hω).1
          have hn : ¬ srcCut W g E q (Rf ω) (Pf (Rf ω)) c ω (vf ω) < 1 := by
            intro hlt
            apply hb
            change ω ∈ S ∧ (D ω, ω) ∈ T₁
            exact ⟨hω, hRω, hlt⟩
          simp only [Pi.one_apply, sub_zero]
          linarith
      · have hω' : pre ω = 0 := (h01 ω).resolve_right hω
        have hb : ω ∉ B₁ := fun h => hω (show ω ∈ S ∧ (D ω, ω) ∈ T₁ from h).1
        rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hb, hω']
        simp
    have hSi : Integrable (S.indicator (1 : Ω W q → ℝ)) (μ W q) :=
      (integrable_const (1 : ℝ)).indicator hSm
    have hBi : Integrable (B₁.indicator (1 : Ω W q → ℝ)) (μ W q) :=
      (integrable_const (1 : ℝ)).indicator hB₁m
    have hlow_int : Integrable (fun ω => S.indicator (1 : Ω W q → ℝ) ω - B₁.indicator 1 ω)
        (μ W q) := hSi.sub hBi
    have hlow_eq : ∫ ω, (S.indicator (1 : Ω W q → ℝ) ω - B₁.indicator 1 ω) ∂(μ W q) =
        (μ W q).real S - (μ W q).real B₁ := by
      rw [integral_sub hSi hBi, integral_indicator_one hSm, integral_indicator_one hB₁m]
    calc (1 / 2 : ℝ) ≤ (μ W q).real S - (μ W q).real B₁ := by linarith
      _ = ∫ ω, (S.indicator (1 : Ω W q → ℝ) ω - B₁.indicator 1 ω) ∂(μ W q) := hlow_eq.symm
      _ ≤ _ := integral_mono hlow_int hf_int hlow
  -- the size `𝔼 ‖χ K‖² ≤ C σ`
  have hsq : ∫⁻ ω, ENNReal.ofReal ((pre ω * srcCut W g E q (Rf ω) (Pf (Rf ω)) c ω (vf ω)) ^ 2 *
      hsSq (smallGen W g E q (Rf ω) c.t (Pf (Rf ω)) ω (vf ω))) ∂(μ W q) ≤
      ENNReal.ofReal (C * σ) := by
    calc _ ≤ ∫⁻ _ω, ENNReal.ofReal (C * σ) ∂(μ W q) := lintegral_mono fun ω => ?_
      _ = ENNReal.ofReal (C * σ) := by simp
    by_cases h0 : pre ω * srcCut W g E q (Rf ω) (Pf (Rf ω)) c ω (vf ω) = 0
    · rw [h0]
      simp
    · apply ENNReal.ofReal_le_ofReal
      have hK := (hsupp ω h0).2
      have hK0 : 0 ≤ hsSq (smallGen W g E q (Rf ω) c.t (Pf (Rf ω)) ω (vf ω)) := by
        unfold hsSq
        positivity
      obtain ⟨hc0, hc1⟩ := hχ01 (Rf ω) ω (vf ω)
      have hp1 : (pre ω * srcCut W g E q (Rf ω) (Pf (Rf ω)) c ω (vf ω)) ^ 2 ≤ 1 := by
        rcases h01 ω with h | h
        · simp [h]
        · rw [h, one_mul]
          exact pow_le_one₀ hc0 hc1
      calc _ ≤ 1 * (64 * c.Lov) := mul_le_mul hp1 hK hK0 zero_le_one
        _ ≤ C * σ := by rw [one_mul]; exact hσ
  -- the cost (9.30) [su:eq:pair-cutoff-derivative]
  have hcostI : ∫⁻ ω, ENNReal.ofReal (pre ω * (∑ i, ‖(Pf (Rf ω) *ᵥ vf ω) i‖ ^ 2) *
      hsSq (smallGen W g E q (Rf ω) c.t (Pf (Rf ω)) ω (vf ω)) *
      tangGradSq (Pf (Rf ω)) (vf ω) (fun w => srcCut W g E q (Rf ω) (Pf (Rf ω)) c ω w))
      ∂(μ W q) ≤ ENNReal.ofReal C := by
    set T₂ : Set ((Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) × Ω W q) :=
      {p | (∀ j, 5 ≤ j → j ≤ q - 2 → IsRegularState W g (chartR W g E q p.1.1 p.2 j)) ∧
        ∑ i, ‖(chartProd W g E q p.1.1 p.2 (q - 1) *ᵥ p.1.2) i‖ ^ 2 <
          2 * c.kOut ^ 2 * ∑ i, ‖(Pf p.1.1 *ᵥ p.1.2) i‖ ^ 2} with hT₂_def
    have hT₂m : MeasurableSet T₂ := by
      have hreg := chosenGeneratorExists_measurableSet_regular hW hg hg1
      have he : {p : (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) × Ω W q |
          ∀ j, 5 ≤ j → j ≤ q - 2 → IsRegularState W g (chartR W g E q p.1.1 p.2 j)} =
          ⋂ j, ⋂ (_ : 5 ≤ j), ⋂ (_ : j ≤ q - 2),
            (fun p : (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) × Ω W q =>
              chartR W g E q p.1.1 p.2 j) ⁻¹' {X | IsRegularState W g X} := by
        ext p
        simp
      have h1 : MeasurableSet {p : (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) × Ω W q |
          ∀ j, 5 ≤ j → j ≤ q - 2 → IsRegularState W g (chartR W g E q p.1.1 p.2 j)} := by
        rw [he]
        exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
          MeasurableSet.iInter fun _ =>
            hreg.preimage (chosenGeneratorExists_measurable_chartR g E hm1 measurable_snd j)
      have h2 : MeasurableSet {p : (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) × Ω W q |
          ∑ i, ‖(chartProd W g E q p.1.1 p.2 (q - 1) *ᵥ p.1.2) i‖ ^ 2 <
            2 * c.kOut ^ 2 * ∑ i, ‖(Pf p.1.1 *ᵥ p.1.2) i‖ ^ 2} := by
        refine measurableSet_lt (Finset.measurable_sum _ fun i _ => ?_)
          (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_))
        · exact ((measurable_pi_apply i).comp (hmulVec
            (chosenGeneratorExists_measurable_chartProd g E hm1 measurable_snd (q - 1))
            hm2)).norm.pow_const 2
        · exact ((measurable_pi_apply i).comp (hmulVec (hPf.comp hm1) hm2)).norm.pow_const 2
      exact h1.inter h2
    have hT₂a : ∀ (d : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) (ω ω' : Ω W q),
        (∀ y : Fin q × Fin W × Fin W, 4 ≤ (y.1 : ℕ) → ω y = ω' y) →
        ((d, ω) ∈ T₂ ↔ (d, ω') ∈ T₂) := by
      intro d ω ω' h
      have hc := chosenGeneratorExists_chart_congr (g := g) (E := E) (R := d.1)
        (hblk_ge ω ω' h)
      have hc1 : ∀ j, chartR W g E q d.1 ω j = chartR W g E q d.1 ω' j := fun j => (hc j).1
      have hc2 : ∀ j, chartProd W g E q d.1 ω j = chartProd W g E q d.1 ω' j :=
        fun j => (hc j).2
      simp only [hT₂_def, Set.mem_ofPred_eq, hc1, hc2]
    have hb₂ : ∀ ω ∈ S, μ W q {ω' | (D ω, ω') ∈ T₂} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-(26 : ℝ))) := by
      intro ω hω
      exact hout _ _ (hS_mem ω hω).2.2
    have hB₂ := measure_prefix_le W q 4 hDm hDa hSm hSa hT₂m hT₂a hb₂
    set B₂ : Set (Ω W q) := {ω | ω ∈ S ∧ (D ω, ω) ∈ T₂} with hB₂_def
    have hB₂m : MeasurableSet B₂ := hSm.inter (hT₂m.preimage (hDm.prodMk measurable_id))
    have hW26 : (0 : ℝ) ≤ C₂ * (W : ℝ) ^ 26 := by positivity
    have hpw : ∀ ω, ENNReal.ofReal (pre ω * (∑ i, ‖(Pf (Rf ω) *ᵥ vf ω) i‖ ^ 2) *
        hsSq (smallGen W g E q (Rf ω) c.t (Pf (Rf ω)) ω (vf ω)) *
        tangGradSq (Pf (Rf ω)) (vf ω) (fun w => srcCut W g E q (Rf ω) (Pf (Rf ω)) c ω w)) ≤
        ENNReal.ofReal C₂ + ENNReal.ofReal (C₂ * (W : ℝ) ^ 26) * B₂.indicator 1 ω := by
      intro ω
      rcases h01 ω with h0 | h1
      · rw [h0, zero_mul, zero_mul, zero_mul, ENNReal.ofReal_zero]
        positivity
      · have hω : ω ∈ S := h1
        obtain ⟨hR, hv, -⟩ := hS_mem ω hω
        obtain ⟨hPh, hPP, -⟩ := hPs _ hR
        have hc := hcost (E := E) (c := c) ω (vf ω) hW hq hg hg1 hR hPh hPP hv ht hLov h64 hkOut
          hkP hLrk hLgap herr
        rw [h1, one_mul]
        by_cases hB : (∀ j, 5 ≤ j → j ≤ q - 2 →
            IsRegularState W g (chartR W g E q (Rf ω) ω j)) ∧
            ∑ i, ‖(chartProd W g E q (Rf ω) ω (q - 1) *ᵥ vf ω) i‖ ^ 2 <
              2 * c.kOut ^ 2 * ∑ i, ‖(Pf (Rf ω) *ᵥ vf ω) i‖ ^ 2
        · have hb : ω ∈ B₂ := by
            change ω ∈ S ∧ (D ω, ω) ∈ T₂
            exact ⟨hω, hB⟩
          rw [Set.indicator_of_mem hb, Pi.one_apply, mul_one,
            ← ENNReal.ofReal_add hC₂.le hW26]
          apply ENNReal.ofReal_le_ofReal
          rw [ite_eq_left hB] at hc
          have := mul_le_mul_of_nonneg_left (add_le_add_left hratio 1) hC₂.le
          linarith
        · rw [ite_eq_right hB, add_zero, mul_one] at hc
          exact (ENNReal.ofReal_le_ofReal hc).trans le_self_add
    have hWW : (W : ℝ) ^ 26 * (W : ℝ) ^ (-(26 : ℝ)) = 1 := by
      rw [Real.rpow_neg hW0.le, Real.rpow_ofNat]
      exact mul_inv_cancel₀ (by positivity)
    calc _ ≤ ∫⁻ ω, (ENNReal.ofReal C₂ + ENNReal.ofReal (C₂ * (W : ℝ) ^ 26) * B₂.indicator 1 ω)
          ∂(μ W q) := lintegral_mono hpw
      _ = ENNReal.ofReal C₂ + ENNReal.ofReal (C₂ * (W : ℝ) ^ 26) * μ W q B₂ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ (measurable_one.indicator hB₂m), lintegral_indicator_one hB₂m]
      _ ≤ ENNReal.ofReal C₂ + ENNReal.ofReal (C₂ * (W : ℝ) ^ 26) *
            ENNReal.ofReal ((W : ℝ) ^ (-(26 : ℝ))) := by
        gcongr
        exact hB₂.trans (mul_le_of_le_one_right' prob_le_one)
      _ = ENNReal.ofReal (2 * C₂) := by
        rw [← ENNReal.ofReal_mul hW26, mul_assoc, hWW, mul_one,
          ← ENNReal.ofReal_add hC₂.le hC₂.le, two_mul]
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC2
  unfold ChosenGenerator
  refine ⟨h01, hmpre, hmR, hmv, hpref, hchart, hPf, measurable_smallGen W g E q c.t hPf,
    measurable_srcCut W g E q c hPf, fun ω hω => ?_, fun ω hω => (hsupp ω hω).1, hmass, hsq,
    hcostI⟩
  obtain ⟨hR, -, -⟩ := hchart ω hω
  exact ⟨(hPs _ hR).1, (hPs _ hR).2.1, (hPs _ hR).2.2, hfam _ hR⟩

/-- `W^{-y} → 0` along the integers, for `y > 0`. -/
private lemma chosenGeneratorExists_tendsto_rpow_neg {y : ℝ} (hy : 0 < y) :
    Filter.Tendsto (fun W : ℕ => (W : ℝ) ^ (-y)) Filter.atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop hy).comp tendsto_natCast_atTop_atTop

/-- The source projection (9.4) [su:eq:source-projection] `P = 1_{[-s, s]}(g² R)` at a Hermitian
`R`: an orthogonal projection commuting with `R`, with `g² ‖P R P‖ ≤ s`. -/
private lemma chosenGeneratorExists_specProj_props {W : ℕ} {g s : ℝ} (hg : g ≠ 0) (hs : 0 ≤ s)
    (R : Matrix (Fin W) (Fin W) ℂ) (hR : R.IsHermitian) :
    ((specProj ((g ^ 2 : ℝ) • R) (Set.Icc (-s) s)).IsHermitian ∧
      specProj ((g ^ 2 : ℝ) • R) (Set.Icc (-s) s) * specProj ((g ^ 2 : ℝ) • R) (Set.Icc (-s) s) =
        specProj ((g ^ 2 : ℝ) • R) (Set.Icc (-s) s) ∧
      specProj ((g ^ 2 : ℝ) • R) (Set.Icc (-s) s) * R =
        R * specProj ((g ^ 2 : ℝ) • R) (Set.Icc (-s) s)) ∧
    g ^ 2 * ‖specProj ((g ^ 2 : ℝ) • R) (Set.Icc (-s) s) * R *
      specProj ((g ^ 2 : ℝ) • R) (Set.Icc (-s) s)‖ ≤ s := by
  set P := specProj ((g ^ 2 : ℝ) • R) (Set.Icc (-s) s) with hP_def
  have hA : ((g ^ 2 : ℝ) • R).IsHermitian := hR.smul (IsSelfAdjoint.all _)
  obtain ⟨hPh, hPP, hAP, -⟩ := specProj_spec hA (Set.Icc (-s) s)
  have hg2 : (g ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hg
  have hPR : P * R = R * P := by
    apply smul_right_injective (Matrix (Fin W) (Fin W) ℂ) hg2
    simp only
    rw [← Matrix.mul_smul, ← Matrix.smul_mul]
    exact hAP.symm
  refine ⟨⟨hPh, hPP, hPR⟩, ?_⟩
  have hPRP : P * R * P = R * P := by rw [hPR, mul_assoc, hPP]
  have hn := (norm_mul_specProj_le hA hs (subset_refl _) (1 : Matrix (Fin W) (Fin W) ℂ)
    zero_le_one).1
  rw [Matrix.smul_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hn
  rw [hPRP]
  exact hn

/-- Lemma 9.3 [su:lem:chosen-generator], regime (i) of Lemma 8.12 [up:lem:small-contraction]. -/
theorem chosen_generator_weak (κ₀ α β : ℝ) (hκ₀ : 0 < κ₀) (hκ₂ : κ₀ < 2) (hα : 0 < α)
    (hαβ : α < β) (hβ : β < 1 / 2) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ q : ℕ, 7 ≤ q ∧ ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        ∀ a ∈ Set.Icc α β, ∀ E ∈ Set.Icc (-2 + κ₀) (2 - κ₀), ∀ x : IsoFlag W,
          ∃ (pre : Ω W q → ℝ) (Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ)
            (vf : Ω W q → Fin W → ℂ)
            (Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ)
            (χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ),
            ChosenGenerator W q ((W : ℝ) ^ (-a)) E x
              (fun R => specProj ((((W : ℝ) ^ (-a)) ^ 2 : ℝ) • R)
                (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800))))
              C (((W : ℝ) ^ (-a)) ^ 2 * (W : ℝ) ^ (ε / 4)) ((W : ℝ) ^ (ε / 800))
              pre Rf vf Kh χh := by
  obtain ⟨C₀, hC₀, hasm⟩ := chosenGeneratorExists_assembly
  refine ⟨min 1 (100 * α), lt_min one_pos (by linarith), fun ε hε hεε => ?_⟩
  have hε1 : ε ≤ 1 := hεε.trans (min_le_left _ _)
  have hεα : ε ≤ 100 * α := hεε.trans (min_le_right _ _)
  obtain ⟨hq7, -, -, W₁, hlev⟩ := levels_weak α β ε hα hαβ hβ hε hε1 hεα
  obtain ⟨Cp, hCp, W₂, hprepW⟩ := preparation_weak κ₀ α β ε hκ₀ hκ₂ hα hαβ hβ hε
  obtain ⟨W₃, hplatW⟩ := cutPlat_weak κ₀ α β ε Cp hκ₀ hκ₂ hα hαβ hβ hε hε1 hεα hCp
  obtain ⟨W₄, houtW⟩ :=
    output_lower_weak κ₀ α β ε Cp hκ₀ hκ₂ hα hαβ hβ hε hε1 hCp 26 (by norm_num)
  obtain ⟨W₅, hW₅⟩ : ∃ W₅ : ℕ, ∀ W : ℕ, W₅ ≤ W →
      Cp * ((W : ℝ) ^ (-2 : ℝ) + (W : ℝ) ^ (-α / 2) + (W : ℝ) ^ (-(ε / 800))) ≤ 1 / 3 := by
    have t1 := chosenGeneratorExists_tendsto_rpow_neg (y := 2) (by norm_num)
    have t2 := chosenGeneratorExists_tendsto_rpow_neg (y := α / 2) (by positivity)
    have t3 := chosenGeneratorExists_tendsto_rpow_neg (y := ε / 800) (by positivity)
    have h := ((t1.add t2).add t3).const_mul Cp
    rw [add_zero, add_zero, mul_zero] at h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (h.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3)))
    refine ⟨N, fun W hW => ?_⟩
    have := hN W hW
    rw [neg_div]
    exact this
  refine ⟨qWeak β ε, hq7, C₀, by linarith,
    max (max (max W₁ W₂) (max W₃ W₄)) (max W₅ 1), fun W hW a ha E hE x => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (by simp) hW
  have hW2 : W₂ ≤ W := le_trans (by simp) hW
  have hW3 : W₃ ≤ W := le_trans (by simp) hW
  have hW4 : W₄ ≤ W := le_trans (by simp) hW
  have hW5 : W₅ ≤ W := le_trans (by simp) hW
  have hWpos : 1 ≤ W := le_trans (by simp) hW
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hWpos
  have hW0 : (0 : ℝ) < W := by linarith
  have hg : 0 < (W : ℝ) ^ (-a) := Real.rpow_pos_of_pos hW0 _
  have hg1 : (W : ℝ) ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith [ha.1])
  have hEabs : |E| ≤ 2 - κ₀ := abs_le.2 ⟨by linarith [hE.1], hE.2⟩
  have ht : ∀ L, 0 < (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).t := fun L =>
    mul_pos (Real.rpow_pos_of_pos hW0 _) (inv_pos.2 (pow_pos hg _))
  obtain ⟨L, hL, hLgap⟩ := exists_gap_level W (qWeak β ε) hq7 ((W : ℝ) ^ (-a)) E
    (levelsWeak W ((W : ℝ) ^ (-a)) α β ε 1).t (ht 1) (η := 1 / 40) (by norm_num)
  obtain ⟨hLov, h64, hkOut, herr, hprod, hrk, hratio⟩ := hlev W hW1 a ha L
  have hkP : 1 ≤ (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).kP :=
    Nat.ceil_pos.2 (by positivity)
  have hLrk : 0 < (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).Lrk :=
    mul_pos (mul_pos two_pos (Real.rpow_pos_of_pos (ht 1) _)) (Real.rpow_pos_of_pos hW0 _)
  have hσ0 : 0 ≤ (W : ℝ) * (((W : ℝ) ^ (-a)) ^ 2 * (W : ℝ) ^ (ε / 4)) := by positivity
  have hrk' : 4 * (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).Lrk + 1 ≤
      C₀ * W * (((W : ℝ) ^ (-a)) ^ 2 * (W : ℝ) ^ (ε / 4)) := by
    have : 3 * (W : ℝ) * (((W : ℝ) ^ (-a)) ^ 2 * (W : ℝ) ^ (ε / 4)) ≤
        C₀ * W * (((W : ℝ) ^ (-a)) ^ 2 * (W : ℝ) ^ (ε / 4)) := by
      rw [mul_assoc, mul_assoc C₀]
      exact mul_le_mul_of_nonneg_right (by linarith) hσ0
    linarith
  have hσ : 64 * (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).Lov ≤
      C₀ * (((W : ℝ) ^ (-a)) ^ 2 * (W : ℝ) ^ (ε / 4)) := by
    change 64 * (((W : ℝ) ^ (-a)) ^ 2 * (W : ℝ) ^ (3 * ε / 200)) ≤ _
    have h1 : (W : ℝ) ^ (3 * ε / 200) ≤ (W : ℝ) ^ (ε / 4) :=
      Real.rpow_le_rpow_of_exponent_le hW1r (by linarith)
    gcongr
  have hPfm : Measurable fun R : Matrix (Fin W) (Fin W) ℂ =>
      specProj ((((W : ℝ) ^ (-a)) ^ 2 : ℝ) • R)
        (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800))) :=
    (measurable_specProj isClosed_Icc).comp (continuous_const_smul _).measurable
  have hPs := chosenGeneratorExists_specProj_props (W := W) (g := (W : ℝ) ^ (-a))
    (s := (W : ℝ) ^ (ε / 800)) hg.ne' (by positivity)
  have hprepB : μ W (qWeak β ε) {ω | ¬ (PrepOK W ((W : ℝ) ^ (-a)) E (qWeak β ε) x ω ∧
      (prepR W ((W : ℝ) ^ (-a)) E (qWeak β ε) x ω 4,
        prepV W ((W : ℝ) ^ (-a)) E (qWeak β ε) x ω 4) ∈
        PrepGoodWeak W ((W : ℝ) ^ (-a)) ε Cp)} ≤ ENNReal.ofReal (1 / 3) :=
    (hprepW W (qWeak β ε) hW2 (by omega) a E x ha.1 ha.2 hEabs).trans
      (ENNReal.ofReal_le_ofReal (hW₅ W hW5))
  exact ⟨_, _, _, _, _, hasm hWpos hq7 hg hg1 (measurableSet_prepGood W _ ε Cp 0).1 hPfm
    (fun R hR => (hPs R hR).1) (fun R _ _ hR => (hPs R hR).2) (ht L) hLov h64 hkOut hkP hLrk hL
    herr hprod hratio hrk' hσ le_rfl hprepB
    (fun R v hG hv => hplatW W hW3 a ha E hEabs L hL hLgap R v hG hv)
    (fun R v hG => houtW W hW4 a ha E hEabs R v hG)⟩

/-- Lemma 9.3 [su:lem:chosen-generator], regime (ii) of Lemma 8.12 [up:lem:small-contraction]:
the critical window (8.37) [eq:critical-window]. -/
theorem chosen_generator_crit (κ₀ cs θ : ℝ) (hκ₀ : 0 < κ₀) (hκ₂ : κ₀ < 2) (hcs : 0 < cs)
    (hθ : 0 < θ) (hθ' : θ ≤ 1 / 100) :
    ∃ q : ℕ, 7 ≤ q ∧ ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ g : ℝ, cs * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ g → g ≤ (W : ℝ) ^ (-(1 / 2 : ℝ) + θ / 2) →
        ∀ E ∈ Set.Icc (-2 + κ₀) (2 - κ₀), ∀ x : IsoFlag W,
          ∃ (pre : Ω W q → ℝ) (Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ)
            (vf : Ω W q → Fin W → ℂ)
            (Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ)
            (χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ),
            ChosenGenerator W q g E x (fun _ => 1) C ((W : ℝ) ^ (-1 + 14 * θ))
              (C * (W : ℝ) ^ (2 * θ)) pre Rf vf Kh χh := by
  obtain ⟨C₀, hC₀, hasm⟩ := chosenGeneratorExists_assembly
  obtain ⟨hq7, -, -, W₁, hlev⟩ := levels_crit θ cs hθ hθ' hcs
  obtain ⟨Cp, hCp, W₂, hprepW⟩ := preparation_crit θ hθ hθ'
  obtain ⟨W₃, hplatW⟩ := cutPlat_crit κ₀ θ hκ₀ hκ₂ hθ hθ'
  obtain ⟨W₄, houtW⟩ := output_lower_crit κ₀ θ hκ₀ hκ₂ hθ hθ' 26 (by norm_num)
  obtain ⟨W₅, hW₅⟩ : ∃ W₅ : ℕ, ∀ W : ℕ, W₅ ≤ W → Cp * (W : ℝ) ^ (-θ) ≤ 1 / 3 := by
    have h := (chosenGeneratorExists_tendsto_rpow_neg hθ).const_mul Cp
    rw [mul_zero] at h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (h.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3)))
    exact ⟨N, fun W hW => hN W hW⟩
  refine ⟨qCrit θ, hq7, C₀, by linarith,
    max (max (max W₁ W₂) (max W₃ W₄)) (max W₅ 1), fun W hW g hg₁ hg₂ E hE x => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (by simp) hW
  have hW2 : W₂ ≤ W := le_trans (by simp) hW
  have hW3 : W₃ ≤ W := le_trans (by simp) hW
  have hW4 : W₄ ≤ W := le_trans (by simp) hW
  have hW5 : W₅ ≤ W := le_trans (by simp) hW
  have hWpos : 1 ≤ W := le_trans (by simp) hW
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hWpos
  have hW0 : (0 : ℝ) < W := by linarith
  have hg : 0 < g := lt_of_lt_of_le (mul_pos hcs (Real.rpow_pos_of_pos hW0 _)) hg₁
  have hg1 : g ≤ 1 := hg₂.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith))
  have hEabs : |E| ≤ 2 - κ₀ := abs_le.2 ⟨by linarith [hE.1], hE.2⟩
  have ht : ∀ L, 0 < (levelsCrit W θ L).t := fun L => Real.rpow_pos_of_pos hW0 _
  obtain ⟨L, hL, hLgap⟩ := exists_gap_level W (qCrit θ) hq7 g E (levelsCrit W θ 1).t (ht 1)
    (η := 1 / 40) (by norm_num)
  obtain ⟨hLov, h64, hkOut, herr, hprod, hrk, hratio⟩ := hlev W hW1 g hg₁ hg₂ L
  have hkP : 1 ≤ (levelsCrit W θ L).kP := le_rfl
  have hLrk : 0 < (levelsCrit W θ L).Lrk :=
    mul_pos (mul_pos two_pos (Real.rpow_pos_of_pos (ht 1) _)) (Real.rpow_pos_of_pos hW0 _)
  have hσ0 : 0 ≤ (W : ℝ) * (W : ℝ) ^ (-1 + 14 * θ) := by positivity
  have hrk' : 4 * (levelsCrit W θ L).Lrk + 1 ≤ C₀ * W * (W : ℝ) ^ (-1 + 14 * θ) := by
    have : 3 * (W : ℝ) * (W : ℝ) ^ (-1 + 14 * θ) ≤ C₀ * W * (W : ℝ) ^ (-1 + 14 * θ) := by
      rw [mul_assoc, mul_assoc C₀]
      exact mul_le_mul_of_nonneg_right (by linarith) hσ0
    linarith
  have hσ : 64 * (levelsCrit W θ L).Lov ≤ C₀ * (W : ℝ) ^ (-1 + 14 * θ) := by
    change 64 * (W : ℝ) ^ (-1 + 14 * θ) ≤ _
    gcongr
  have hM₀ : ∀ (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ), (R, v) ∈ PrepGoodCrit W g θ →
      R.IsHermitian → g ^ 2 * ‖(fun _ => (1 : Matrix (Fin W) (Fin W) ℂ)) R * R *
        (fun _ => (1 : Matrix (Fin W) (Fin W) ℂ)) R‖ ≤ C₀ * (W : ℝ) ^ (2 * θ) := by
    intro R v hG _
    have h1 : g ^ 2 * ‖R‖ ≤ (W : ℝ) ^ (2 * θ) := hG.2.2.2
    have h2 : (W : ℝ) ^ (2 * θ) ≤ C₀ * (W : ℝ) ^ (2 * θ) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    simp only [one_mul, mul_one]
    linarith
  have hg₂' : g ≤ (W : ℝ) ^ (-1 / 2 + θ / 2) := by
    rw [show (-1 / 2 + θ / 2 : ℝ) = -(1 / 2 : ℝ) + θ / 2 by ring]
    exact hg₂
  have hprepB : μ W (qCrit θ) {ω | ¬ (PrepOK W g E (qCrit θ) x ω ∧
      (prepR W g E (qCrit θ) x ω 4, prepV W g E (qCrit θ) x ω 4) ∈ PrepGoodCrit W g θ)} ≤
        ENNReal.ofReal (1 / 3) :=
    (hprepW W (qCrit θ) hW2 (by omega) g E x hg hg₂').trans
      (ENNReal.ofReal_le_ofReal (hW₅ W hW5))
  have hout : ∀ (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ), (R, v) ∈ PrepGoodCrit W g θ →
      μ W (qCrit θ) {ω | (∀ j, 5 ≤ j → j ≤ qCrit θ - 2 →
          IsRegularState W g (chartR W g E (qCrit θ) R ω j)) ∧
        ∑ i, ‖(chartProd W g E (qCrit θ) R ω (qCrit θ - 1) *ᵥ v) i‖ ^ 2 <
          2 * (levelsCrit W θ L).kOut ^ 2 *
            ∑ i, ‖((fun _ => (1 : Matrix (Fin W) (Fin W) ℂ)) R *ᵥ v) i‖ ^ 2} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-(26 : ℝ))) := by
    intro R v hG
    simp only [Matrix.one_mulVec]
    exact houtW W hW4 g hg hg₂ E hEabs R v hG
  exact ⟨_, _, _, _, _, hasm hWpos hq7 hg hg1 (measurableSet_prepGood W g 0 0 θ).2
    measurable_const (fun R _ => ⟨Matrix.isHermitian_one, mul_one 1, by rw [one_mul, mul_one]⟩)
    hM₀ (ht L) hLov h64 hkOut hkP hLrk hL herr hprod hratio hrk' hσ le_rfl hprepB
    (fun R v hG hv => hplatW W hW3 g hg hg₂ E hEabs L hL hLgap R v hG hv) hout⟩

end LSBA
