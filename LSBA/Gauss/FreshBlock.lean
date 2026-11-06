import LSBA.Gauss.OneBlockWegner
import LSBA.Gauss.BlockSplit

/-!
# One fresh GUE block with a shift depending on the other blocks

Integrating block `a` of the model (1.2) [eq:covariance] first: a bound for the `W × W` GUE
matrix that holds for every value of the other blocks passes to the full sample. Consequences for
a Hermitian shift that is a measurable function of the other blocks: the half moment [PSSS, (2.6)]
behind [PSSS, Theorem 1], which the proof of Theorem 3.1 [thm:strong-upper] cites, and the
eigenvalue-count bound of (9.58) [us:eq:wegner].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The `W × W` GUE matrix of (1.2) [eq:covariance] built from the coordinates `u` of one block. -/
private def freshBlock_G (W : ℕ) (u : Fin W × Fin W → ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun α β =>
    if α = β then (u (α, α) : ℂ) / Real.sqrt W
    else if α < β then ((u (α, β) : ℂ) + Complex.I * u (β, α)) / Real.sqrt (2 * W)
    else ((u (β, α) : ℂ) - Complex.I * u (α, β)) / Real.sqrt (2 * W)

private lemma freshBlock_measurable_G (W : ℕ) : Measurable (freshBlock_G W) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [freshBlock_G, Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma freshBlock_measurable_fst (W L : ℕ) (a : Fin L) :
    Measurable fun ω : Ω W L => (blockSplit W L a ω).1 :=
  (measurePreserving_blockSplit W L a).measurable.fst

/-- The law of the coordinates of block `0` of the one-block sample is `stdGauss`. -/
private lemma freshBlock_map_fst (W : ℕ) :
    Measure.map (fun ω : Ω W 1 => (blockSplit W 1 0 ω).1) (μ W 1) =
      stdGauss (Fin W × Fin W) := by
  have h := measurePreserving_blockSplit W 1 0
  have h1 : (fun ω : Ω W 1 => (blockSplit W 1 0 ω).1) = Prod.fst ∘ blockSplit W 1 0 := rfl
  rw [h1, ← Measure.map_map measurable_fst h.measurable, h.map_eq, Measure.map_fst_prod]
  simp

/-- An integral of a function of the GUE matrix under `stdGauss` is its integral under `μ W 1`. -/
private lemma freshBlock_lintegral_fiber (W : ℕ) (g : Matrix (Fin W) (Fin W) ℂ → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ u, g (freshBlock_G W u) ∂(stdGauss (Fin W × Fin W)) = ∫⁻ ω', g (gueMat W ω') ∂(μ W 1) := by
  rw [← freshBlock_map_fst]
  exact lintegral_map (f := fun V => g (freshBlock_G W V))
    (hg.comp (freshBlock_measurable_G W)) (freshBlock_measurable_fst W 1 0)

/-- The sample that is `ρ` on the blocks other than `a` and `0` on block `a`. -/
private def freshBlock_ext (W L : ℕ) (a : Fin L)
    (ρ : {x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) : Ω W L :=
  fun x => if h : x.1 ≠ a then ρ ⟨x, h⟩ else 0

private lemma freshBlock_measurable_ext (W L : ℕ) (a : Fin L) :
    Measurable (freshBlock_ext W L a) := by
  refine measurable_pi_iff.mpr fun x => ?_
  unfold freshBlock_ext
  by_cases h : x.1 = a
  · simp only [ne_eq, h, not_true_eq_false, ↓reduceDIte]
    exact measurable_const
  · simp only [ne_eq, h, not_false_eq_true, ↓reduceDIte]
    exact measurable_pi_apply _

private lemma freshBlock_ext_split (W L : ℕ) (a : Fin L) (ω : Ω W L) (x : Fin L × Fin W × Fin W)
    (hx : x.1 ≠ a) : freshBlock_ext W L a (blockSplit W L a ω).2 x = ω x := by
  simp [freshBlock_ext, blockSplit, hx]

/-- The matrix inverse `X ↦ X⁻¹ = det(X)⁻¹ adj(X)` is Borel. -/
private lemma freshBlock_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable fun X : Matrix ι ι ℂ => X⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have h : (fun X : Matrix ι ι ℂ => X⁻¹ i j) = fun X => (X.det)⁻¹ * X.adjugate i j := by
    funext X
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [h]
  have hd : Continuous fun X : Matrix ι ι ℂ => X.det := continuous_id.matrix_det
  have ha : Continuous fun X : Matrix ι ι ℂ => X.adjugate i j :=
    (continuous_id.matrix_adjugate).matrix_elem i j
  exact hd.measurable.inv.mul ha.measurable

private lemma freshBlock_continuous_l2Norm {ι : Type*} [Fintype ι] :
    Continuous fun v : ι → ℂ => l2Norm v := by
  unfold l2Norm
  fun_prop

/-- `p ↦ √‖M p w p‖₂` is measurable for measurable `M` and `w`. -/
private lemma freshBlock_measurable_sqrt_mulVec {α : Type*} [MeasurableSpace α] (W : ℕ)
    {M : α → Matrix (Fin W) (Fin W) ℂ} {w : α → Fin W → ℂ} (hM : Measurable M)
    (hw : Measurable w) : Measurable fun p => Real.sqrt (l2Norm (M p *ᵥ w p)) := by
  have h : Measurable fun p => M p *ᵥ w p := by
    refine measurable_pi_iff.mpr fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.measurable_sum _ fun j _ =>
      (measurable_pi_iff.mp (measurable_pi_iff.mp hM i) j).mul (measurable_pi_iff.mp hw j)
  exact (freshBlock_continuous_l2Norm.sqrt).measurable.comp h

/-- The decreasing eigenvalue of index `j` is Borel on all matrices. -/
private lemma freshBlock_measurable_sortedEig (n : ℕ) (j : Fin (Fintype.card (Fin n))) :
    Measurable fun M : Matrix (Fin n) (Fin n) ℂ => sortedEig M j := by
  have hS : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | M.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have heq : (fun M : Matrix (Fin n) (Fin n) ℂ => sortedEig M j) =
      Set.piecewise {M : Matrix (Fin n) (Fin n) ℂ | M.IsHermitian}
        (fun M => sortedEig M j) (fun _ => 0) := by
    funext M
    by_cases hM : M.IsHermitian
    · rw [Set.piecewise_eq_of_mem _ _ _ hM]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hM]
      simp [sortedEig, hM]
  rw [heq]
  exact ContinuousOn.measurable_piecewise
    ((continuous_apply j).comp_continuousOn continuousOn_sortedEig)
    continuousOn_const hS.measurableSet

/-- `M ↦ #{eigenvalues of M in J}` is Borel on all matrices for measurable `J`. -/
private lemma freshBlock_measurable_countIn (n : ℕ) {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable fun M : Matrix (Fin n) (Fin n) ℂ => (countIn M J : ℝ≥0∞) := by
  have hS : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | M.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hsum : Measurable fun M : Matrix (Fin n) (Fin n) ℂ =>
      ∑ j, if sortedEig M j ∈ J then 1 else 0 :=
    Finset.measurable_sum _ fun j _ => Measurable.ite
      (hJ.preimage (freshBlock_measurable_sortedEig n j)) measurable_const measurable_const
  have heq : (fun M : Matrix (Fin n) (Fin n) ℂ => countIn M J) =
      Set.piecewise {M : Matrix (Fin n) (Fin n) ℂ | M.IsHermitian}
        (fun M => ∑ j, if sortedEig M j ∈ J then 1 else 0) (fun _ => 0) := by
    funext M
    by_cases hM : M.IsHermitian
    · rw [Set.piecewise_eq_of_mem _ _ _ hM]
      simp only [countIn, hM, ↓reduceDIte, Finset.card_filter, eigenvalues_eq_sortedEig hM]
      exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
        (fun j => if sortedEig M j ∈ J then 1 else 0)
    · rw [Set.piecewise_eq_of_notMem _ _ _ hM]
      simp [countIn, hM]
  have hm : Measurable fun M : Matrix (Fin n) (Fin n) ℂ => countIn M J := by
    rw [heq]
    exact hsum.piecewise hS.measurableSet measurable_const
  exact (measurable_from_top : Measurable fun m : ℕ => (m : ℝ≥0∞)).comp hm

/-- If `∫ F(V, ρ) dV ≤ B(ρ)` under the `W × W` GUE law for every value `ρ` of the blocks other
than `a`, then `∫ F(V_a, ρ_a) dμ ≤ ∫ B(ρ_a) dμ`, `ρ_a` the other blocks of the sample. -/
theorem lintegral_gueBlock_fresh_le (W L : ℕ) (a : Fin L)
    {F : Matrix (Fin W) (Fin W) ℂ → ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F))
    {B : ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) → ℝ≥0∞}
    (hB : ∀ ρ, ∫⁻ ω', F (gueMat W ω') ρ ∂(μ W 1) ≤ B ρ) :
    ∫⁻ ω, F (gueBlock W L ω a) (blockSplit W L a ω).2 ∂(μ W L) ≤
      ∫⁻ ω, B (blockSplit W L a ω).2 ∂(μ W L) := by
  have hbs := measurePreserving_blockSplit W L a
  have hf : Measurable fun z : (Fin W × Fin W → ℝ) ×
      ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) => F (freshBlock_G W z.1) z.2 :=
    hF.comp (((freshBlock_measurable_G W).comp measurable_fst).prodMk measurable_snd)
  have h1 : ∫⁻ ω, F (gueBlock W L ω a) (blockSplit W L a ω).2 ∂(μ W L) =
      ∫⁻ z, F (freshBlock_G W z.1) z.2
        ∂((stdGauss (Fin W × Fin W)).prod
          (stdGauss {x : Fin L × Fin W × Fin W // x.1 ≠ a})) :=
    hbs.lintegral_comp hf
  rw [h1, lintegral_prod_symm _ hf.aemeasurable]
  calc _ ≤ ∫⁻ ρ, B ρ ∂(stdGauss {x : Fin L × Fin W × Fin W // x.1 ≠ a}) := by
        refine lintegral_mono fun ρ => ?_
        have hg : Measurable fun V : Matrix (Fin W) (Fin W) ℂ => F V ρ :=
          hF.comp (measurable_id.prodMk measurable_const)
        rw [freshBlock_lintegral_fiber W (fun V => F V ρ) hg]
        exact hB ρ
    _ ≤ _ := by
        have hmap : Measure.map (fun ω : Ω W L => (blockSplit W L a ω).2) (μ W L) =
            stdGauss {x : Fin L × Fin W × Fin W // x.1 ≠ a} := by
          have h2 : (fun ω : Ω W L => (blockSplit W L a ω).2) = Prod.snd ∘ blockSplit W L a := rfl
          rw [h2, ← Measure.map_map measurable_snd hbs.measurable, hbs.map_eq,
            Measure.map_snd_prod]
          simp
        rw [← hmap]
        exact lintegral_map_le B hbs.measurable.snd.aemeasurable

/-- Half moment with a shift and a vector depending only on the blocks other than `a`
([PSSS, (2.6)] at `s = 1/2`): `E‖(A + V_a)⁻¹ v‖₂^{1/2} ≤ C W^{1/4} E‖v‖₂^{1/2}`. -/
theorem gueBlock_shift_halfMoment : ∃ C : ℝ, 0 < C ∧
    ∀ (W L : ℕ) (a : Fin L) (A : Ω W L → Matrix (Fin W) (Fin W) ℂ) (v : Ω W L → Fin W → ℂ),
      Measurable A → Measurable v → (∀ ω, (A ω).IsHermitian) →
      (∀ ω ω' : Ω W L, (∀ x, x.1 ≠ a → ω x = ω' x) → A ω = A ω' ∧ v ω = v ω') →
      ∫⁻ ω, ENNReal.ofReal (Real.sqrt (l2Norm ((A ω + gueBlock W L ω a)⁻¹ *ᵥ v ω))) ∂(μ W L) ≤
        ENNReal.ofReal (C * (W : ℝ) ^ (1 / 4 : ℝ)) *
          ∫⁻ ω, ENNReal.ofReal (Real.sqrt (l2Norm (v ω))) ∂(μ W L) := by
  obtain ⟨C, hC, h⟩ := gueMat_inv_mulVec_halfMoment
  refine ⟨C, hC, fun W L a A v hAm hvm hAh hoff => ?_⟩
  have hAe : ∀ ω, A (freshBlock_ext W L a (blockSplit W L a ω).2) = A ω := fun ω =>
    (hoff _ _ (fun x hx => freshBlock_ext_split W L a ω x hx)).1
  have hve : ∀ ω, v (freshBlock_ext W L a (blockSplit W L a ω).2) = v ω := fun ω =>
    (hoff _ _ (fun x hx => freshBlock_ext_split W L a ω x hx)).2
  have hAρ : Measurable fun p : Matrix (Fin W) (Fin W) ℂ ×
      ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) => A (freshBlock_ext W L a p.2) :=
    hAm.comp ((freshBlock_measurable_ext W L a).comp measurable_snd)
  have hvρ : Measurable fun p : Matrix (Fin W) (Fin W) ℂ ×
      ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) => v (freshBlock_ext W L a p.2) :=
    hvm.comp ((freshBlock_measurable_ext W L a).comp measurable_snd)
  have hF : Measurable (Function.uncurry fun (V : Matrix (Fin W) (Fin W) ℂ)
      (ρ : {x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) =>
        ENNReal.ofReal (Real.sqrt (l2Norm ((A (freshBlock_ext W L a ρ) + V)⁻¹ *ᵥ
          v (freshBlock_ext W L a ρ))))) := by
    have hinv : Measurable fun p : Matrix (Fin W) (Fin W) ℂ ×
        ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) =>
        (A (freshBlock_ext W L a p.2) + p.1)⁻¹ :=
      freshBlock_measurable_inv.comp (hAρ.add measurable_fst)
    have hsq : Measurable fun p : Matrix (Fin W) (Fin W) ℂ ×
        ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) =>
        Real.sqrt (l2Norm ((A (freshBlock_ext W L a p.2) + p.1)⁻¹ *ᵥ
          v (freshBlock_ext W L a p.2))) :=
      freshBlock_measurable_sqrt_mulVec W hinv hvρ
    exact ENNReal.measurable_ofReal.comp hsq
  have hB : ∀ ρ : {x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ,
      ∫⁻ ω', ENNReal.ofReal (Real.sqrt (l2Norm ((A (freshBlock_ext W L a ρ) + gueMat W ω')⁻¹ *ᵥ
        v (freshBlock_ext W L a ρ)))) ∂(μ W 1) ≤
      ENNReal.ofReal (C * (W : ℝ) ^ (1 / 4 : ℝ)) *
        ENNReal.ofReal (Real.sqrt (l2Norm (v (freshBlock_ext W L a ρ)))) := fun ρ => by
    have := h W (A (freshBlock_ext W L a ρ)) (hAh _) (v (freshBlock_ext W L a ρ))
    rwa [ENNReal.ofReal_mul (by positivity)] at this
  have key := lintegral_gueBlock_fresh_le W L a hF hB
  simp only [hAe, hve] at key
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at key
  exact key

/-- Eigenvalue count of (9.58) [us:eq:wegner] with a shift depending only on the blocks other
than `a`: `E #{eigenvalues of A + V_a in [α, β]} ≤ C W (β - α)`. -/
theorem gueBlock_shift_countIn_le : ∃ C : ℝ, 0 < C ∧
    ∀ (W L : ℕ) (a : Fin L) (A : Ω W L → Matrix (Fin W) (Fin W) ℂ), Measurable A →
      (∀ ω, (A ω).IsHermitian) → (∀ ω ω' : Ω W L, (∀ x, x.1 ≠ a → ω x = ω' x) → A ω = A ω') →
      ∀ α β : ℝ,
        ∫⁻ ω, (countIn (A ω + gueBlock W L ω a) (Set.Icc α β) : ℝ≥0∞) ∂(μ W L) ≤
          ENNReal.ofReal (C * W * (β - α)) := by
  obtain ⟨C, hC, h⟩ := lintegral_countIn_add_gueMat_le
  refine ⟨C, hC, fun W L a A hAm hAh hoff α β => ?_⟩
  have hAe : ∀ ω, A (freshBlock_ext W L a (blockSplit W L a ω).2) = A ω := fun ω =>
    hoff _ _ (fun x hx => freshBlock_ext_split W L a ω x hx)
  have hAρ : Measurable fun p : Matrix (Fin W) (Fin W) ℂ ×
      ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) => A (freshBlock_ext W L a p.2) :=
    hAm.comp ((freshBlock_measurable_ext W L a).comp measurable_snd)
  have hF : Measurable (Function.uncurry fun (V : Matrix (Fin W) (Fin W) ℂ)
      (ρ : {x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) =>
        (countIn (A (freshBlock_ext W L a ρ) + V) (Set.Icc α β) : ℝ≥0∞)) :=
    (freshBlock_measurable_countIn W measurableSet_Icc).comp (hAρ.add measurable_fst)
  have hB : ∀ ρ : {x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ,
      ∫⁻ ω', (countIn (A (freshBlock_ext W L a ρ) + gueMat W ω') (Set.Icc α β) : ℝ≥0∞)
        ∂(μ W 1) ≤ ENNReal.ofReal (C * W * (β - α)) := fun ρ =>
    h W _ (hAh _) α β
  have key := lintegral_gueBlock_fresh_le W L a hF hB
  simp only [hAe] at key
  rw [lintegral_const, measure_univ, mul_one] at key
  exact key

end LSBA
