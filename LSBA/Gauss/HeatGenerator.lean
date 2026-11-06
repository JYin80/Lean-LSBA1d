import LSBA.Gauss.Heat
import LSBA.Gauss.StdGauss

/-!
# The generator form of Itô's formula

For `F` in the bounded `C^{1,2}` class on `(a,b) ⊇ [0,v]`, the map `u ↦ E F(u, √(uσ²) ξ)`, with
`ξ` standard Gaussian, is continuous on `[0,v]` and has derivative `E 𝒢F` on `(0,v)`: the
generator form of (5.4) [fo:eq:ito] at a single time.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The sup norm `‖x‖` is integrable under the standard Gaussian on `ℝ^ι`. -/
private theorem heatGenerator_integrable_norm (ι : Type*) [Fintype ι] :
    Integrable (fun x : ι → ℝ => ‖x‖) (stdGauss ι) := by
  have h1 : Integrable (fun t : ℝ => |t|) (gaussianReal 0 1) := by
    have h := (memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) 1 ENNReal.one_ne_top).integrable
      le_rfl
    simpa [Real.norm_eq_abs] using h.norm
  have hi : ∀ i : ι, Integrable (fun x : ι → ℝ => |x i|) (stdGauss ι) := by
    intro i
    have hmp := measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i
    exact (hmp.integrable_comp h1.aestronglyMeasurable).mpr h1
  refine (integrable_finsetSum Finset.univ fun i _ => hi i).mono'
    continuous_norm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun i => |x i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)

/-- For `σ² ≥ 0` and `r > 0`, `r ↦ √(rσ²)` has derivative `σ² / (2√(rσ²))` at `r` (both sides
are `0` when `σ² = 0`). -/
private theorem heatGenerator_hasDerivAt_sqrt {σ2 : ℝ} (hσ2 : 0 ≤ σ2) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r => Real.sqrt (r * σ2)) (σ2 / (2 * Real.sqrt (r * σ2))) r := by
  rcases hσ2.eq_or_lt with h | h
  · subst h
    simpa using hasDerivAt_const r (0 : ℝ)
  · have hpos : 0 < r * σ2 := mul_pos hr h
    have hl : HasDerivAt (fun r => r * σ2) σ2 r := by
      simpa using (hasDerivAt_id r).mul_const σ2
    exact ((Real.hasDerivAt_sqrt hpos.ne').comp r hl).congr_deriv (by ring)

/-- Chain rule for `r ↦ F(r, p(r))` when `F` has jointly continuous partial derivatives `∂_u F`
and `D_x F` on `(a,b) × ℝ^ι`. -/
private theorem heatGenerator_hasDerivAt_comp {ι : Type*} [Fintype ι] {F Fu : ℝ → (ι → ℝ) → ℂ}
    {DF : ℝ → (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℂ)} {a b : ℝ}
    (hu : ∀ r ∈ Set.Ioo a b, ∀ x, HasDerivAt (fun r' => F r' x) (Fu r x) r)
    (hcu : ContinuousOn (Function.uncurry Fu) (Set.Ioo a b ×ˢ Set.univ))
    (hD : ∀ r ∈ Set.Ioo a b, ∀ x, HasFDerivAt (F r) (DF r x) x)
    (hcD : ContinuousOn (Function.uncurry DF) (Set.Ioo a b ×ˢ Set.univ))
    {p : ℝ → ι → ℝ} {p' : ι → ℝ} {r : ℝ} (hr : r ∈ Set.Ioo a b) (hp : HasDerivAt p p' r) :
    HasDerivAt (fun r => F r (p r)) (Fu r (p r) + DF r (p r) p') r := by
  have hopen : IsOpen (Set.Ioo a b ×ˢ (Set.univ : Set (ι → ℝ))) := isOpen_Ioo.prod isOpen_univ
  have hnhds : Set.Ioo a b ×ˢ (Set.univ : Set (ι → ℝ)) ∈ 𝓝 (r, p r) :=
    hopen.mem_nhds ⟨hr, trivial⟩
  have hS : HasStrictFDerivAt (Function.uncurry F)
      ((ContinuousLinearMap.toSpanSingleton ℝ (Fu r (p r))).coprod (DF r (p r))) (r, p r) := by
    refine hasStrictFDerivAt_uncurry_coprod (u := (r, p r)) (f := F)
      (f₁ := fun r x => ContinuousLinearMap.toSpanSingleton ℝ (Fu r x)) (f₂ := DF) ?_ ?_ ?_ ?_
    · filter_upwards [hnhds] with q hq
      exact (hu q.1 hq.1 q.2).hasFDerivAt
    · filter_upwards [hnhds] with q hq
      exact hD q.1 hq.1 q.2
    · exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℂ)).continuous.continuousAt.comp
        (hcu.continuousAt hnhds)
    · exact hcD.continuousAt hnhds
  have h2 : HasDerivAt (fun r' => (r', p r')) ((1 : ℝ), p') r := (hasDerivAt_id r).prodMk hp
  have h3 := hS.hasFDerivAt.comp_hasDerivAt r h2
  exact h3.congr_deriv (by simp)

/-- Along a line, `e ↦ G(y + e v)` has second derivative `D²G(y) v v` at `0`, when `G` has
derivative `DG` and `DG` has derivative `D²G` everywhere. -/
private theorem heatGenerator_iteratedDeriv_line {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℂ}
    {DG : (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℂ)} {D2G : (ι → ℝ) → ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ)}
    (hD : ∀ x, HasFDerivAt G (DG x) x) (hD2 : ∀ x, HasFDerivAt DG (D2G x) x) (y v : ι → ℝ) :
    iteratedDeriv 2 (fun e : ℝ => G (y + e • v)) 0 = D2G y v v := by
  have hl : ∀ e : ℝ, HasDerivAt (fun e : ℝ => y + e • v) v e := fun e => by
    simpa using ((hasDerivAt_id e).smul_const v).const_add y
  have h1 : deriv (fun e : ℝ => G (y + e • v)) = fun e => DG (y + e • v) v :=
    funext fun e => ((hD _).comp_hasDerivAt e (hl e)).deriv
  have h2 : HasDerivAt (fun e : ℝ => DG (y + e • v) v) (D2G y v v) 0 := by
    have h := ((hD2 _).comp_hasDerivAt 0 (hl 0)).clm_apply (hasDerivAt_const (0 : ℝ) v)
    simpa using h
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2.deriv]

/-- Gaussian integration by parts for the radial term: with `DG` bounded and differentiable with
bounded continuous derivative `D²G`, `E[DG(sξ) ξ] = s Σ_i E[D²G(sξ) e_i e_i]`. -/
private theorem heatGenerator_stein {ι : Type*} [Fintype ι] {DG : (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℂ)}
    {D2G : (ι → ℝ) → ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ)} (hD2 : ∀ x, HasFDerivAt DG (D2G x) x)
    (hc2 : Continuous D2G) {C : ℝ} (hb : ∀ x, ‖DG x‖ ≤ C ∧ ‖D2G x‖ ≤ C) (s : ℝ) :
    ∫ x, DG (s • x) x ∂(stdGauss ι) =
      (s : ℂ) * ∑ i, ∫ x, D2G (s • x) (Pi.single i 1) (Pi.single i 1) ∂(stdGauss ι) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hb 0).1
  have hc1 : Continuous DG := continuous_iff_continuousAt.2 fun x => (hD2 x).continuousAt
  have hei : ∀ i : ι, ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ ≤ 1 := fun i => by
    rw [Pi.norm_single]; simp
  -- the coordinate decomposition of `DG(sx) x`
  have hdec' : ∀ (L : (ι → ℝ) →L[ℝ] ℂ) (x : ι → ℝ),
      L x = ∑ i, (x i : ℂ) * L (Pi.single i 1) := by
    intro L x
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (Pi.single i (x i) : ι → ℝ) = x i • Pi.single i 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this, ContinuousLinearMap.map_smul, Complex.real_smul]
  have hdec : ∀ x : ι → ℝ, DG (s • x) x = ∑ i, (x i : ℂ) * DG (s • x) (Pi.single i 1) :=
    fun x => hdec' (DG (s • x)) x
  -- each summand, by the vector Stein identity
  have hstein : ∀ i : ι, ∫ x, (x i : ℂ) * DG (s • x) (Pi.single i 1) ∂(stdGauss ι) =
      (s : ℂ) * ∫ x, D2G (s • x) (Pi.single i 1) (Pi.single i 1) ∂(stdGauss ι) := by
    intro i
    set e : ι → ℝ := Pi.single i 1
    set G : (ι → ℝ) → ℂ := fun x => DG (s • x) e with hGdef
    have hGd : ∀ x, HasFDerivAt G
        ((ContinuousLinearMap.apply ℝ ℂ e).comp
          ((D2G (s • x)).comp (s • ContinuousLinearMap.id ℝ (ι → ℝ)))) x := by
      intro x
      have hsm : HasFDerivAt (fun x : ι → ℝ => s • x) (s • ContinuousLinearMap.id ℝ (ι → ℝ)) x :=
        (hasFDerivAt_id x).const_smul s
      exact (ContinuousLinearMap.apply ℝ ℂ e).hasFDerivAt.comp x ((hD2 (s • x)).comp x hsm)
    have hfd : ∀ x h, fderiv ℝ G x h = D2G (s • x) (s • h) e := fun x h => by
      rw [(hGd x).fderiv]; rfl
    have hfdc : Continuous fun x => fderiv ℝ G x := by
      have : (fun x => fderiv ℝ G x) = fun x => (ContinuousLinearMap.apply ℝ ℂ e).comp
          ((D2G (s • x)).comp (s • ContinuousLinearMap.id ℝ (ι → ℝ))) :=
        funext fun x => (hGd x).fderiv
      rw [this]
      exact continuous_const.clm_comp ((hc2.comp (continuous_const_smul s)).clm_comp
        continuous_const)
    have hG1 : ContDiff ℝ 1 G :=
      contDiff_one_iff_fderiv.2 ⟨fun x => (hGd x).differentiableAt, hfdc⟩
    have hGb : ∀ x, ‖G x‖ ≤ (C + |s| * C) * (1 + ‖x‖) ^ 0 := fun x => by
      rw [pow_zero, mul_one]
      calc ‖G x‖ ≤ ‖DG (s • x)‖ * ‖e‖ := (DG (s • x)).le_opNorm e
        _ ≤ C * 1 := mul_le_mul (hb _).1 (hei i) (norm_nonneg _) hC
        _ ≤ C + |s| * C := by nlinarith [abs_nonneg s]
    have hGb' : ∀ x, ‖fderiv ℝ G x‖ ≤ (C + |s| * C) * (1 + ‖x‖) ^ 0 := fun x => by
      rw [pow_zero, mul_one]
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
      rw [hfd]
      calc ‖D2G (s • x) (s • h) e‖ ≤ ‖D2G (s • x) (s • h)‖ * ‖e‖ :=
            (D2G (s • x) (s • h)).le_opNorm e
        _ ≤ (‖D2G (s • x)‖ * ‖s • h‖) * 1 :=
            mul_le_mul ((D2G (s • x)).le_opNorm _) (hei i) (norm_nonneg _) (by positivity)
        _ = ‖D2G (s • x)‖ * (|s| * ‖h‖) := by rw [norm_smul, Real.norm_eq_abs, mul_one]
        _ ≤ C * (|s| * ‖h‖) := mul_le_mul_of_nonneg_right (hb _).2 (by positivity)
        _ ≤ (C + |s| * C) * ‖h‖ := by nlinarith [abs_nonneg s, norm_nonneg h]
    have key := integral_coord_mul_stdGauss G hG1 hGb hGb' i
    rw [key, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hfd, ContinuousLinearMap.map_smul, FunLike.coe_smul, Pi.smul_apply,
      Complex.real_smul]
    rfl
  -- integrability of the summands
  have hint : ∀ i : ι, Integrable (fun x : ι → ℝ => (x i : ℂ) * DG (s • x) (Pi.single i 1))
      (stdGauss ι) := by
    intro i
    refine ((heatGenerator_integrable_norm ι).const_mul C).mono' ?_
      (Eventually.of_forall fun x => ?_)
    · exact ((Complex.continuous_ofReal.comp (continuous_apply i)).mul
        ((hc1.comp (continuous_const_smul s)).clm_apply continuous_const)).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hxi : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
      have hD : ‖DG (s • x) (Pi.single i 1)‖ ≤ C :=
        ((DG (s • x)).le_opNorm _).trans
          ((mul_le_mul (hb _).1 (hei i) (norm_nonneg _) hC).trans (by rw [mul_one]))
      calc |x i| * ‖DG (s • x) (Pi.single i 1)‖ ≤ ‖x‖ * C :=
            mul_le_mul hxi hD (norm_nonneg _) (norm_nonneg _)
        _ = C * ‖x‖ := mul_comm _ _
  simp_rw [hdec]
  rw [integral_finsetSum _ fun i _ => hint i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => hstein i

/-- A function jointly continuous on `(a,b) × ℝ^ι` is continuous in `x` at each time in `(a,b)`. -/
private theorem heatGenerator_slice {ι E : Type*} [TopologicalSpace E] {g : ℝ → (ι → ℝ) → E}
    {a b : ℝ} (hg : ContinuousOn (Function.uncurry g) (Set.Ioo a b ×ˢ Set.univ)) {r : ℝ}
    (hr : r ∈ Set.Ioo a b) : Continuous (g r) :=
  hg.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hr, trivial⟩

/-- The generator form of Itô's formula: for `F` in the bounded `C^{1,2}` class on `(a,b) ⊇ [0,v]`,
the map `u ↦ E F(u, √(uσ²) ξ)` is continuous on `[0,v]` and has derivative `E 𝒢F` on `(0,v)`. -/
theorem heat_generator {ι : Type*} [Fintype ι] (σ2 : ℝ) (hσ2 : 0 ≤ σ2) (F : ℝ → (ι → ℝ) → ℂ)
    {a b v : ℝ} (ha : a < 0) (hv : 0 ≤ v) (hvb : v < b) (hF : HeatClass F a b) :
    ContinuousOn (fun u => ∫ x, F u (Real.sqrt (u * σ2) • x) ∂(stdGauss ι)) (Set.Icc 0 v) ∧
      ∀ u ∈ Set.Ioo 0 v, HasDerivAt (fun r => ∫ x, F r (Real.sqrt (r * σ2) • x) ∂(stdGauss ι))
        (∫ x, coordGen σ2 F u (Real.sqrt (u * σ2) • x) ∂(stdGauss ι)) u := by
  obtain ⟨hc, ⟨C₀, hC₀⟩, ⟨Fu, hu, hcu, C₁, hC₁⟩, ⟨DF, D2F, hD, hD2, hcD, hcD2, C₂, hC₂⟩⟩ := hF
  have hsub : Set.Icc 0 v ⊆ Set.Ioo a b := fun r hr => ⟨ha.trans_le hr.1, hr.2.trans_lt hvb⟩
  have hFx : ∀ r ∈ Set.Ioo a b, Continuous (F r) := fun r hr =>
    continuous_iff_continuousAt.2 fun x => (hD r hr x).continuousAt
  refine ⟨?_, ?_⟩
  · -- continuity on `[0,v]` by dominated convergence
    refine continuousOn_of_dominated (bound := fun _ => C₀) (fun r hr => ?_) (fun r hr => ?_)
      (integrable_const _) (Eventually.of_forall fun x => ?_)
    · exact ((hFx r (hsub hr)).comp (continuous_const_smul _)).aestronglyMeasurable
    · exact Eventually.of_forall fun x => hC₀ r (hsub hr) _
    · have hpath : ContinuousOn (fun r : ℝ => (r, Real.sqrt (r * σ2) • x)) (Set.Icc 0 v) :=
        (continuous_id.prodMk
          ((continuous_id.mul continuous_const).sqrt.smul continuous_const)).continuousOn
      exact hc.comp hpath fun r hr => ⟨hsub hr, trivial⟩
  · intro u hu0
    have hu0' : 0 < u := hu0.1
    have hub : u < b := hu0.2.trans hvb
    set s : ℝ := Real.sqrt (u * σ2) with hs
    set K : ℝ := σ2 / (2 * Real.sqrt (u / 2 * σ2)) with hK
    have hK0 : 0 ≤ K := by positivity
    set N : Set ℝ := Set.Ioo (u / 2) ((u + b) / 2) with hNdef
    have hN : N ∈ 𝓝 u := Ioo_mem_nhds (by linarith) (by linarith)
    have hNab : ∀ r ∈ N, r ∈ Set.Ioo a b ∧ 0 < r := fun r hr =>
      ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩, by linarith [hr.1]⟩
    have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (hC₂ u (hNab u (mem_of_mem_nhds hN)).1 0).1
    -- the derivative of the speed `r ↦ √(rσ²)` is bounded by `K` on `N`
    have hspeed : ∀ r ∈ N, |σ2 / (2 * Real.sqrt (r * σ2))| ≤ K := by
      intro r hr
      rw [abs_of_nonneg (by positivity)]
      rcases hσ2.eq_or_lt with h | h
      · subst h; simp [hK]
      · refine div_le_div_of_nonneg_left hσ2 (by positivity) ?_
        gcongr
        linarith [hr.1]
    set F' : ℝ → (ι → ℝ) → ℂ := fun r x =>
      Fu r (Real.sqrt (r * σ2) • x) +
        DF r (Real.sqrt (r * σ2) • x) ((σ2 / (2 * Real.sqrt (r * σ2))) • x) with hF'
    have hderiv : ∀ x, ∀ r ∈ N,
        HasDerivAt (fun r => F r (Real.sqrt (r * σ2) • x)) (F' r x) r := fun x r hr =>
      heatGenerator_hasDerivAt_comp hu hcu hD hcD (hNab r hr).1
        ((heatGenerator_hasDerivAt_sqrt hσ2 (hNab r hr).2).smul_const x)
    have hbound : ∀ x, ∀ r ∈ N, ‖F' r x‖ ≤ C₁ + C₂ * (K * ‖x‖) := by
      intro x r hr
      refine (norm_add_le _ _).trans (add_le_add (hC₁ r (hNab r hr).1 _) ?_)
      calc ‖DF r (Real.sqrt (r * σ2) • x) ((σ2 / (2 * Real.sqrt (r * σ2))) • x)‖
          ≤ ‖DF r (Real.sqrt (r * σ2) • x)‖ * ‖(σ2 / (2 * Real.sqrt (r * σ2))) • x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ C₂ * (K * ‖x‖) := by
            refine mul_le_mul (hC₂ r (hNab r hr).1 _).1 ?_ (norm_nonneg _) hC₂0
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (hspeed r hr) (norm_nonneg _)
    have hF'c : Continuous (F' u) := by
      have huab : u ∈ Set.Ioo a b := (hNab u (mem_of_mem_nhds hN)).1
      exact ((heatGenerator_slice hcu huab).comp (continuous_const_smul _)).add
        (((heatGenerator_slice hcD huab).comp (continuous_const_smul _)).clm_apply
          (continuous_const_smul _))
    have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := stdGauss ι)
      (F := fun r x => F r (Real.sqrt (r * σ2) • x)) (F' := F') (x₀ := u)
      (bound := fun x => C₁ + C₂ * (K * ‖x‖)) hN
      (Filter.eventually_of_mem hN fun r hr =>
        ((hFx r (hNab r hr).1).comp (continuous_const_smul _)).aestronglyMeasurable)
      ((integrable_const C₀).mono'
        ((hFx u (hNab u (mem_of_mem_nhds hN)).1).comp
          (continuous_const_smul _)).aestronglyMeasurable
        (Eventually.of_forall fun x => hC₀ u (hNab u (mem_of_mem_nhds hN)).1 _))
      hF'c.aestronglyMeasurable
      (Eventually.of_forall hbound)
      ((integrable_const C₁).add (((heatGenerator_integrable_norm ι).const_mul K).const_mul C₂))
      (Eventually.of_forall hderiv)
    refine hmain.2.congr_deriv ?_
    -- identification of the derivative with `E 𝒢F`
    have huab : u ∈ Set.Ioo a b := (hNab u (mem_of_mem_nhds hN)).1
    have hcFu : Continuous (Fu u) := heatGenerator_slice hcu huab
    have hcDF : Continuous (DF u) := heatGenerator_slice hcD huab
    have hcD2F : Continuous (D2F u) := heatGenerator_slice hcD2 huab
    have hgen : ∀ y, coordGen σ2 F u y =
        Fu u y + ((σ2 / 2 : ℝ) : ℂ) * ∑ i, D2F u y (Pi.single i 1) (Pi.single i 1) := by
      intro y
      simp only [coordGen, (hu u huab y).deriv]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      exact heatGenerator_iteratedDeriv_line (hD u huab) (hD2 u huab) y _
    have hei : ∀ i : ι, ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ ≤ 1 := fun i => by
      rw [Pi.norm_single]; simp
    have hintFu : Integrable (fun x : ι → ℝ => Fu u (s • x)) (stdGauss ι) :=
      (integrable_const C₁).mono' (hcFu.comp (continuous_const_smul _)).aestronglyMeasurable
        (Eventually.of_forall fun x => hC₁ u huab _)
    have hintD2 : ∀ i : ι, Integrable
        (fun x : ι → ℝ => D2F u (s • x) (Pi.single i 1) (Pi.single i 1)) (stdGauss ι) := by
      intro i
      refine (integrable_const C₂).mono'
        (((hcD2F.comp (continuous_const_smul _)).clm_apply continuous_const).clm_apply
          continuous_const).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      calc ‖D2F u (s • x) (Pi.single i 1) (Pi.single i 1)‖
          ≤ ‖D2F u (s • x) (Pi.single i 1)‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖D2F u (s • x)‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖) * 1 :=
            mul_le_mul ((D2F u (s • x)).le_opNorm _) (hei i) (norm_nonneg _) (by positivity)
        _ ≤ (C₂ * 1) * 1 := by
            gcongr
            · exact (hC₂ u huab _).2
            · exact hei i
        _ = C₂ := by ring
    have hintDF : Integrable (fun x : ι → ℝ => DF u (s • x) x) (stdGauss ι) := by
      refine ((heatGenerator_integrable_norm ι).const_mul C₂).mono'
        ((hcDF.comp (continuous_const_smul _)).clm_apply continuous_id).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      exact ((DF u (s • x)).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hC₂ u huab _).1 (norm_nonneg _))
    have hstein := heatGenerator_stein (ι := ι) (hD2 u huab) hcD2F
      (fun x => hC₂ u huab x) s
    have hss : σ2 / (2 * s) * s = σ2 / 2 := by
      rcases (Real.sqrt_nonneg (u * σ2)).eq_or_lt with h | h
      · rw [← hs] at h
        have : u * σ2 = 0 := by
          rcases hσ2.eq_or_lt with h' | h'
          · rw [← h', mul_zero]
          · exact absurd h.symm (Real.sqrt_pos.2 (mul_pos hu0' h')).ne'
        have hσ0 : σ2 = 0 := (mul_eq_zero.1 this).resolve_left hu0'.ne'
        rw [← h, hσ0]; simp
      · rw [← hs] at h
        field_simp
    -- both sides as `E ∂_u F + (σ²/2) Σ_i E D²F e_i e_i`
    simp only [hF', hgen]
    rw [integral_add hintFu, integral_add hintFu, integral_const_mul,
      integral_finsetSum _ fun i _ => hintD2 i]
    · congr 1
      simp only [ContinuousLinearMap.map_smul, Complex.real_smul]
      rw [integral_const_mul, hstein, ← mul_assoc, ← Complex.ofReal_mul, hss]
    · exact ((integrable_finsetSum _ fun i _ => hintD2 i).const_mul _)
    · exact (hintDF.smul (σ2 / (2 * s))).congr (Eventually.of_forall fun x => by simp [hs])

end LSBA
