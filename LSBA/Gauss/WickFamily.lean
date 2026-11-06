import LSBA.Gauss.Wick
import LSBA.Gauss.BlockSplit

/-!
# Wick recursion for a family of independent GUE blocks

For `m` independent GUE blocks with the covariance (1.2) [eq:covariance] and linear functionals
`ℓ_i = x_i* G_{j_i} w_i`: `𝔼[ℓ_0 ∏_{i∈s} ℓ_i] = Σ_{k∈s, j_k = j_0} W⁻¹ (x_0* w_k)(x_k* w_0)
𝔼[∏_{i∈s∖{k}} ℓ_i]`; only functionals of the same block contract. This is the moment calculus
of the tensor bound in Appendix G.4 [app:compact-gaussian].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Splitting off the block `j₀` -/

/-- The coordinates `u` of one block, read as a point of `Ω W 1`. -/
private def wickFamilyEmbed (W : ℕ) (u : Fin W × Fin W → ℝ) : Ω W 1 := fun y => u y.2

/-- The coordinates of block `a` of `ω`, read as a point of `Ω W 1`. -/
private def wickFamilyBlock (W m : ℕ) (a : Fin m) (ω : Ω W m) : Ω W 1 := fun y => ω (a, y.2)

/-- The coordinates outside the block `a`, extended by zero on the block `a`. -/
private def wickFamilyExt (W m : ℕ) (a : Fin m)
    (v : {x : Fin m × Fin W × Fin W // x.1 ≠ a} → ℝ) : Ω W m :=
  fun x => if h : x.1 = a then 0 else v ⟨x, h⟩

private lemma wickFamily_gueBlock_block (W m : ℕ) (a : Fin m) (ω : Ω W m) :
    gueBlock W m ω a = gueBlock W 1 (wickFamilyBlock W m a ω) 0 := rfl

private lemma wickFamily_gueBlock_congr (W m : ℕ) (a : Fin m) (ω ω' : Ω W m)
    (h : ∀ α β, ω (a, α, β) = ω' (a, α, β)) : gueBlock W m ω a = gueBlock W m ω' a := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, h]

private lemma wickFamily_gueBlock_ext (W m : ℕ) (a b : Fin m) (hab : b ≠ a) (ω : Ω W m) :
    gueBlock W m ω b = gueBlock W m (wickFamilyExt W m a fun x => ω x.1) b :=
  wickFamily_gueBlock_congr W m b _ _ fun α β => by simp [wickFamilyExt, hab]

private lemma wickFamily_continuous_lin (W L : ℕ) (a : Fin L) (x w : Fin W → ℂ) :
    Continuous fun ω : Ω W L => star x ⬝ᵥ (gueBlock W L ω a *ᵥ w) := by
  have h : ∀ α β, Continuous fun ω : Ω W L => gueBlock W L ω a α β := fun α β => by
    simp only [gueBlock, Matrix.of_apply]
    split_ifs <;> fun_prop
  simp only [dotProduct, Matrix.mulVec]
  exact continuous_finsetSum _ fun α _ => continuous_const.mul
    (continuous_finsetSum _ fun β _ => (h α β).mul continuous_const)

private lemma wickFamily_measurable_ext (W m : ℕ) (a : Fin m) :
    Measurable (wickFamilyExt W m a) := by
  refine Measurable.of_eval fun x => ?_
  by_cases h : x.1 = a
  · simp only [wickFamilyExt, h, dite_true]
    exact measurable_const
  · simp only [wickFamilyExt, h, dite_false]
    exact measurable_pi_apply _

/-- The embedding of the coordinates of one block into `Ω W 1` carries the standard Gaussian of
`ℝ^{W×W}` to `μ W 1`. -/
private lemma wickFamily_measurePreserving_embed (W : ℕ) :
    MeasurePreserving (wickFamilyEmbed W) (stdGauss (Fin W × Fin W)) (μ W 1) := by
  have hp : MeasurePreserving (fun ω : Ω W 1 => (blockSplit W 1 0 ω).1) (μ W 1)
      (stdGauss (Fin W × Fin W)) :=
    (measurePreserving_fst (μ := stdGauss (Fin W × Fin W))
      (ν := stdGauss {x : Fin 1 × Fin W × Fin W // x.1 ≠ 0})).comp
      (measurePreserving_blockSplit W 1 0)
  have hι : Measurable (wickFamilyEmbed W) :=
    Measurable.of_eval fun y => measurable_pi_apply y.2
  have hcomp : wickFamilyEmbed W ∘ (fun ω : Ω W 1 => (blockSplit W 1 0 ω).1) = id := by
    funext ω
    funext y
    obtain ⟨a, k⟩ := y
    rw [Subsingleton.elim a 0]
    rfl
  refine ⟨hι, ?_⟩
  rw [← hp.map_eq, Measure.map_map hι hp.measurable, hcomp, Measure.map_id]

/-- Integrals of `f(block j₀) · g(other blocks)` factor over the independent pieces. -/
private lemma wickFamily_integral_split (W m : ℕ) (a : Fin m) (f : Ω W 1 → ℂ)
    (g : ({x : Fin m × Fin W × Fin W // x.1 ≠ a} → ℝ) → ℂ) (hf : Measurable f)
    (hg : Measurable g) (F : Ω W m → ℂ)
    (hF : ∀ ω, F ω = f (wickFamilyBlock W m a ω) * g fun x => ω x.1) :
    ∫ ω, F ω ∂(μ W m) =
      (∫ ω', f ω' ∂(μ W 1)) * ∫ v, g v ∂(stdGauss {x : Fin m × Fin W × Fin W // x.1 ≠ a}) := by
  have hr := (wickFamily_measurePreserving_embed W).prod
    (MeasurePreserving.id (stdGauss {x : Fin m × Fin W × Fin W // x.1 ≠ a})) |>.comp
    (measurePreserving_blockSplit W m a)
  have hmeas : Measurable fun z : Ω W 1 × ({x : Fin m × Fin W × Fin W // x.1 ≠ a} → ℝ) =>
      f z.1 * g z.2 := (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  rw [← integral_prod_mul, ← hr.map_eq,
    integral_map hr.measurable.aemeasurable hmeas.aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall hF)

/-- Wick recursion for a family of `m` independent GUE blocks of (1.2) [eq:covariance]:
`𝔼[(x_0* G_{j_0} w_0) ∏_{i∈s} (x_i* G_{j_i} w_i)]
= Σ_{k∈s, j_k = j_0} W⁻¹ (x_0* w_k)(x_k* w_0) 𝔼[∏_{i∈s∖{k}} (x_i* G_{j_i} w_i)]`. -/
theorem integral_gueLin_mul_prod_family (W m : ℕ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (j : ι → Fin m) (x w : ι → Fin W → ℂ) (j₀ : Fin m) (x₀ w₀ : Fin W → ℂ) :
    ∫ ω, (star x₀ ⬝ᵥ (gueBlock W m ω j₀ *ᵥ w₀)) *
        ∏ i ∈ s, (star (x i) ⬝ᵥ (gueBlock W m ω (j i) *ᵥ w i)) ∂(μ W m) =
      ∑ k ∈ s.filter (fun k => j k = j₀), (W : ℂ)⁻¹ * (star x₀ ⬝ᵥ w k) * (star (x k) ⬝ᵥ w₀) *
        ∫ ω, ∏ i ∈ s.erase k, (star (x i) ⬝ᵥ (gueBlock W m ω (j i) *ᵥ w i)) ∂(μ W m) := by
  have key : ∀ (T : Finset ι) (c : Ω W 1 → ℂ), Measurable c →
      ∫ ω, c (wickFamilyBlock W m j₀ ω) *
          ∏ i ∈ T, (star (x i) ⬝ᵥ (gueBlock W m ω (j i) *ᵥ w i)) ∂(μ W m) =
        (∫ ω', c ω' * ∏ i ∈ T.filter (fun i => j i = j₀),
            (star (x i) ⬝ᵥ (gueBlock W 1 ω' 0 *ᵥ w i)) ∂(μ W 1)) *
          ∫ v, ∏ i ∈ T.filter (fun i => ¬ j i = j₀),
            (star (x i) ⬝ᵥ (gueBlock W m (wickFamilyExt W m j₀ v) (j i) *ᵥ w i))
            ∂(stdGauss {x : Fin m × Fin W × Fin W // x.1 ≠ j₀}) := by
    intro T c hc
    refine wickFamily_integral_split W m j₀ _ _ ?_ ?_ _ ?_
    · exact hc.mul (Finset.measurable_prod _ fun i _ =>
        (wickFamily_continuous_lin W 1 0 (x i) (w i)).measurable)
    · exact Finset.measurable_prod _ fun i _ =>
        (wickFamily_continuous_lin W m (j i) (x i) (w i)).measurable.comp
          (wickFamily_measurable_ext W m j₀)
    · intro ω
      have h1 : ∏ i ∈ T.filter (fun i => j i = j₀), (star (x i) ⬝ᵥ (gueBlock W m ω (j i) *ᵥ w i)) =
          ∏ i ∈ T.filter (fun i => j i = j₀),
            (star (x i) ⬝ᵥ (gueBlock W 1 (wickFamilyBlock W m j₀ ω) 0 *ᵥ w i)) :=
        Finset.prod_congr rfl fun i hi => by
          rw [(Finset.mem_filter.1 hi).2, wickFamily_gueBlock_block]
      have h2 : ∏ i ∈ T.filter (fun i => ¬ j i = j₀),
            (star (x i) ⬝ᵥ (gueBlock W m ω (j i) *ᵥ w i)) =
          ∏ i ∈ T.filter (fun i => ¬ j i = j₀),
            (star (x i) ⬝ᵥ (gueBlock W m (wickFamilyExt W m j₀ fun y => ω y.1) (j i) *ᵥ w i)) :=
        Finset.prod_congr rfl fun i hi => by
          rw [wickFamily_gueBlock_ext W m j₀ (j i) (Finset.mem_filter.1 hi).2 ω]
      rw [← Finset.prod_filter_mul_prod_filter_not T (fun i => j i = j₀), h1, h2, mul_assoc]
  have hc0 : Measurable fun ω' : Ω W 1 => star x₀ ⬝ᵥ (gueBlock W 1 ω' 0 *ᵥ w₀) :=
    (wickFamily_continuous_lin W 1 0 x₀ w₀).measurable
  refine Eq.trans (key s _ hc0) ?_
  rw [integral_gueLin_mul_prod W (s.filter (fun i => j i = j₀)) x w x₀ w₀, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkj : j k = j₀ := (Finset.mem_filter.1 hk).2
  have hk' := key (s.erase k) (fun _ => 1) measurable_const
  have hS : (s.erase k).filter (fun i => j i = j₀) = (s.filter (fun i => j i = j₀)).erase k :=
    Finset.filter_erase _ _ _
  have hD : (s.erase k).filter (fun i => ¬ j i = j₀) = s.filter (fun i => ¬ j i = j₀) := by
    rw [Finset.filter_erase]
    exact Finset.erase_eq_of_notMem (by simp [hkj])
  simp only [one_mul, hS, hD] at hk'
  rw [hk', mul_assoc]

end LSBA
