import LSBA.Spectral.RankOneAverage
import LSBA.Spectral.CorrAverage
import LSBA.Gauss.AbsMoment
import LSBA.Upper.Correlator
import LSBA.Gauss.LineDecomp

/-!
# Spectral averaging of the eigenfunction correlator of the model

The spectral averaging of [ASFH, Appendix A, proof of Theorem A.1, (A.10)–(A.12)] for the model,
which the proof of Lemma 8.1(i) [uva:thm:upper-audit] applies to reach (E.1)
[up:eq:correlator-intro]: the diagonal entry `v = H_{xx} = ω(a, α, α)/(√W max{1, g})` is
`N(0, 1/(W max{1, g}²))` and independent of the other coordinates, so the finite-matrix bound
applies with `ρ_W = max{1, g} √(W/(2π))` and `𝔼|v|^u = C_u W^{-u/2} max{1, g}^{-u}`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The coordinate vector `e_{(a, α, α)}` of `Ω W L` has unit length. -/
private lemma correlatorAverage_sum_sq_single {W L : ℕ} (i₀ : Fin L × Fin W × Fin W) :
    ∑ i, (Pi.single i₀ (1 : ℝ) : Ω W L) i ^ 2 = 1 := by
  simp [Pi.single_apply]

/-- Moving the sample along the coordinate `(a, α, α)` moves only the diagonal entry
`H_{xx}`, `x = (a, α)`, of the model (1.3) [eq:model], by `t/(√W max{1, g})`. -/
private lemma correlatorAverage_Hmat_add (g : ℝ) {W L : ℕ} (ω : Ω W L) (x : Fin L × Fin W)
    (t : ℝ) :
    Hmat g W L (ω + t • Pi.single (x.1, x.2, x.2) 1) =
      rankOnePert (Hmat g W L ω) x (t / (Real.sqrt W * max 1 g)) := by
  obtain ⟨a₀, α₀⟩ := x
  ext ⟨a, α⟩ ⟨b, β⟩
  simp only [Hmat, Hdet, rankOnePert, gueBlock, blockDiagOp, Matrix.smul_apply,
    Matrix.add_apply, Matrix.of_apply, smul_eq_mul, Matrix.single_apply, Pi.add_apply,
    Pi.smul_apply, Pi.single_apply, Prod.mk.injEq]
  by_cases hab : a = b
  · subst hab
    by_cases hαβ : α = β
    · subst hαβ
      by_cases h : a₀ = a ∧ α₀ = α
      · obtain ⟨rfl, rfl⟩ := h
        simp
        ring
      · have h' : ¬(a = a₀ ∧ α = α₀) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
        simp [h, h']
    · have h1 : ¬(a = a₀ ∧ α = α₀ ∧ β = α₀) := fun h => hαβ (h.2.1.trans h.2.2.symm)
      have h2 : ¬(a = a₀ ∧ β = α₀ ∧ α = α₀) := fun h => hαβ (h.2.2.trans h.2.1.symm)
      have h3 : ¬((a₀ = a ∧ α₀ = α) ∧ a₀ = a ∧ α₀ = β) := fun h =>
        hαβ (h.1.2.symm.trans h.2.2)
      simp [hαβ, h1, h2, h3]
  · simp only [hab, ite_false, add_zero]
    have h3 : ¬((a₀ = a ∧ α₀ = α) ∧ a₀ = b ∧ α₀ = β) := fun h => hab (h.1.1.symm.trans h.2.1)
    simp [h3]

/-- `(E, ω) ↦ |G_{xy}(E)|^u` for the model (1.3) [eq:model] is measurable (with the total
inverse, `0` on the spectrum), composed with measurable maps `z ↦ E(z)`, `z ↦ ω(z)`. -/
private lemma correlatorAverage_measurable_resolvent (g : ℝ) {W L : ℕ} (x y : Fin L × Fin W)
    (u : ℝ) {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {f : X → ℝ} {h : X → Ω W L} (hf : Continuous f)
    (hh : Continuous h) :
    Measurable fun z => ‖resolventMat (Hmat g W L (h z)) (f z : ℂ) x y‖ₑ ^ u := by
  have hA : Continuous fun z =>
      Hmat g W L (h z) - (f z : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :=
    ((continuous_Hmat g W L).comp hh).sub
      ((Complex.continuous_ofReal.comp hf).smul continuous_const)
  have he : (fun z => resolventMat (Hmat g W L (h z)) (f z : ℂ) x y) =
      fun z => ((Hmat g W L (h z) - (f z : ℂ) • (1 : Matrix _ _ ℂ)).det)⁻¹ *
        (Hmat g W L (h z) - (f z : ℂ) • (1 : Matrix _ _ ℂ)).adjugate x y := by
    funext z
    rw [resolventMat, Matrix.inv_def, Ring.inverse_eq_inv']
    rfl
  have hR : Measurable fun z => resolventMat (Hmat g W L (h z)) (f z : ℂ) x y := by
    rw [he]
    exact (measurable_inv.comp hA.matrix_det.measurable).mul
      (hA.matrix_adjugate.matrix_elem x y).measurable
  exact hR.enorm.pow_const u

/-- Jensen's inequality for `t ↦ t^θ`, `0 < θ < 1`, under a probability measure. -/
private lemma correlatorAverage_lintegral_rpow_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ≥0∞} (hf : AEMeasurable f μ) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) : ∫⁻ a, f a ^ θ ∂μ ≤ (∫⁻ a, f a ∂μ) ^ θ := by
  have hp : 1 < 1 / θ := by rw [lt_div_iff₀ hθ0]; linarith
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (f := fun a => f a ^ θ)
    (g := fun _ => 1) (hf.pow_const θ) aemeasurable_const
  have h1 : ∀ a, (f a ^ θ) ^ (1 / θ) = f a := fun a => by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hθ0.ne', ENNReal.rpow_one]
  simp only [Pi.mul_apply, mul_one, h1, ENNReal.one_rpow, lintegral_const, measure_univ,
    one_div_one_div] at h
  simpa using h

/-- A property of almost every sample holds, for almost every `ω`, at almost every point
`ω - ⟨ω, e⟩ e + t e` of the line through `ω` along a unit vector `e`. -/
private lemma correlatorAverage_ae_line {ι : Type*} [Fintype ι] (e : ι → ℝ)
    (he : ∑ i, e i ^ 2 = 1) {P : (ι → ℝ) → Prop} (hP : ∀ᵐ ω ∂(stdGauss ι), P ω) :
    ∀ᵐ ω ∂(stdGauss ι), ∀ᵐ t ∂(gaussianReal 0 1),
      P (ω - (∑ i, ω i * e i) • e + t • e) := by
  set N := toMeasurable (stdGauss ι) {ω | ¬ P ω}
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : stdGauss ι N = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp hP
  have hline : Continuous fun q : (ι → ℝ) × ℝ => q.1 - (∑ i, q.1 i * e i) • e + q.2 • e := by
    fun_prop
  have hF : Measurable fun q : (ι → ℝ) × ℝ =>
      N.indicator (1 : (ι → ℝ) → ℝ≥0∞) (q.1 - (∑ i, q.1 i * e i) • e + q.2 • e) :=
    (measurable_one.indicator hN).comp hline.measurable
  have h := lintegral_stdGauss_line e he (measurable_one.indicator hN)
  rw [lintegral_indicator_one hN, hN0, eq_comm,
    lintegral_eq_zero_iff hF.lintegral_prod_right'] at h
  filter_upwards [h] with ω hω
  rw [Pi.zero_apply] at hω
  have hω' := (lintegral_eq_zero_iff (f := fun t : ℝ =>
    N.indicator (1 : (ι → ℝ) → ℝ≥0∞) (ω - (∑ i, ω i * e i) • e + t • e))
    ((measurable_one.indicator hN).comp (by fun_prop))).mp hω
  filter_upwards [hω'] with t ht
  have ht' : (ω - (∑ i, ω i * e i) • e + t • e) ∉ N := by
    intro hmem
    simp [Set.indicator_of_mem hmem] at ht
  by_contra hc
  exact ht' (subset_toMeasurable _ _ hc)

/-- Equal Hermitian matrices have the same simplicity of spectrum. -/
private lemma correlatorAverage_injective_congr {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    Function.Injective hA.eigenvalues ↔ Function.Injective hB.eigenvalues := by
  subst h
  rfl

/-- The spectral averaging of [ASFH, Appendix A, proof of Theorem A.1, (A.10)–(A.12)] for the
model (1.3) [eq:model], with `ρ_W = max{1,g} √(W/(2π))` and
`𝔼|v|^u = C_u W^{-u/2} max{1,g}^{-u}` for `v = H_{xx}`. -/
theorem correlator_spectral_average {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) {g : ℝ} (hg : 0 ≤ g)
    {W L : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJb : Bornology.IsBounded J) (x y : Fin L × Fin W) :
    ENNReal.ofReal (∫ ω, eigCorr (Hmat g W L ω) J x y ∂(μ W L)) ≤
      (ENNReal.ofReal (2 * (absMomentConst u * (W : ℝ) ^ (-u / 2) * (max 1 g) ^ (-u)) *
          (max 1 g * Real.sqrt (W / (2 * π)))) *
        ∫⁻ E in J, ∫⁻ ω, ‖resolventMat (Hmat g W L ω) E x y‖ₑ ^ u ∂(μ W L)) ^ (1 / (4 - u)) := by
  have hm0 : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left 1 g)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
  set c : ℝ := 1 / (Real.sqrt W * max 1 g) with hc
  have hc0 : 0 < c := by positivity
  set e : Ω W L := Pi.single (x.1, x.2, x.2) 1 with he
  have he1 : ∑ i, e i ^ 2 = 1 := correlatorAverage_sum_sq_single _
  have hp0 : 0 < 1 / (4 - u) := by
    have : 0 < 4 - u := by linarith
    positivity
  have hp1 : 1 / (4 - u) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  set M : ℝ := absMomentConst u * (W : ℝ) ^ (-u / 2) * (max 1 g) ^ (-u) with hMdef
  set κ : ℝ := max 1 g * Real.sqrt (W / (2 * π)) with hκdef
  have hemb : MeasurableEmbedding fun t : ℝ => c * t := measurableEmbedding_mulLeft₀ hc0.ne'
  -- the law of `v = H_{xx}`: density at most `κ = ρ_W` and `𝔼|v|^u = M`
  have hκ : (gaussianReal 0 1).map (fun t => c * t) ≤
      ENNReal.ofReal κ • (volume : Measure ℝ) := by
    have h := map_const_mul_gaussianReal_le hc0.ne'
    have hκc : 1 / (|c| * Real.sqrt (2 * π)) = κ := by
      rw [abs_of_pos hc0, hκdef, hc, Real.sqrt_div hW0.le]
      have : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
      field_simp
    rwa [hκc] at h
  have hM : ∫⁻ v, ‖v‖ₑ ^ u ∂((gaussianReal 0 1).map fun t => c * t) ≤ ENNReal.ofReal M := by
    rw [hemb.lintegral_map, lintegral_enorm_const_mul_rpow_gaussianReal c hu0]
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    rw [hMdef, abs_of_pos hc0, hc, one_div, Real.inv_rpow (by positivity),
      Real.mul_rpow hsW.le hm0.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hW0.le, mul_inv,
      Real.rpow_neg hm0.le, neg_div, Real.rpow_neg hW0.le]
    ring_nf
  -- the line through `ω` along `e`
  have hline : ∀ (ω : Ω W L) (t : ℝ), Hmat g W L (ω - (∑ i, ω i * e i) • e + t • e) =
      rankOnePert (Hmat g W L (ω - (∑ i, ω i * e i) • e)) x (c * t) := by
    intro ω t
    rw [he, correlatorAverage_Hmat_add, hc]
    congr 1
    ring
  -- `Q_{xy}(J)` and `|G_{xy}(E)|^u`
  have hint := integrable_eigCorr_Hmat g W L hJ x y
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => eigCorr_nonneg _ _ _ _)]
  have hAm : AEMeasurable (fun ω => ENNReal.ofReal (eigCorr (Hmat g W L ω) J x y)) (μ W L) :=
    hint.aemeasurable.ennreal_ofReal
  have hB3 : Measurable fun q : (Ω W L × ℝ) × ℝ =>
      ‖resolventMat (Hmat g W L (q.1.1 - (∑ i, q.1.1 i * e i) • e + q.2 • e)) (q.1.2 : ℂ) x y‖ₑ ^
        u :=
    correlatorAverage_measurable_resolvent g x y u (by fun_prop) (by fun_prop)
  have hB2 : Measurable fun q : Ω W L × ℝ => ∫⁻ t,
      ‖resolventMat (Hmat g W L (q.1 - (∑ i, q.1 i * e i) • e + t • e)) (q.2 : ℂ) x y‖ₑ ^ u
        ∂(gaussianReal 0 1) :=
    hB3.lintegral_prod_right'
  have hB1 : Measurable fun ω : Ω W L => ∫⁻ E in J, ∫⁻ t,
      ‖resolventMat (Hmat g W L (ω - (∑ i, ω i * e i) • e + t • e)) (E : ℂ) x y‖ₑ ^ u
        ∂(gaussianReal 0 1) :=
    hB2.lintegral_prod_right'
  -- almost every line has `Q = Q̃` (a measurable version) and simple spectrum a.e.
  have hgood := correlatorAverage_ae_line e he1 (P := fun ω =>
    ENNReal.ofReal (eigCorr (Hmat g W L ω) J x y) = hAm.mk _ ω ∧
      Function.Injective (Hmat_isHermitian g W L ω).eigenvalues)
    (hAm.ae_eq_mk.and (ae_injective_eigenvalues g W L))
  -- the finite-matrix bound on each line
  have hstep : ∀ᵐ ω ∂(μ W L), ∫⁻ t, hAm.mk _ (ω - (∑ i, ω i * e i) • e + t • e)
      ∂(gaussianReal 0 1) ≤
      (ENNReal.ofReal (2 * M * κ) * ∫⁻ E in J, ∫⁻ t,
        ‖resolventMat (Hmat g W L (ω - (∑ i, ω i * e i) • e + t • e)) (E : ℂ) x y‖ₑ ^ u
          ∂(gaussianReal 0 1)) ^ (1 / (4 - u)) := by
    filter_upwards [hgood] with ω hω
    have hK := Hmat_isHermitian g W L (ω - (∑ i, ω i * e i) • e)
    have hsimple : ∀ᵐ v ∂((gaussianReal 0 1).map fun t => c * t),
        Function.Injective (rankOnePert_isHermitian hK x v).eigenvalues := by
      rw [hemb.ae_map_iff]
      filter_upwards [hω] with t ht
      exact (correlatorAverage_injective_congr _ _ (hline ω t)).mp ht.2
    have h := lintegral_eigCorr_rankOnePert_le hK x y hu0 hu1.le hκ hM hsimple
      (fun φ hφ => lintegral_eigMassSum_rankOnePert_le hK x hφ) hJ
    rw [hemb.lintegral_map] at h
    simp_rw [hemb.lintegral_map, ← hline] at h
    calc ∫⁻ t, hAm.mk _ (ω - (∑ i, ω i * e i) • e + t • e) ∂(gaussianReal 0 1)
        = ∫⁻ t, ENNReal.ofReal (eigCorr (Hmat g W L (ω - (∑ i, ω i * e i) • e + t • e)) J x y)
            ∂(gaussianReal 0 1) := lintegral_congr_ae (hω.mono fun t ht => ht.1.symm)
      _ ≤ _ := h
  calc ∫⁻ ω, ENNReal.ofReal (eigCorr (Hmat g W L ω) J x y) ∂(μ W L)
      = ∫⁻ ω, hAm.mk _ ω ∂(μ W L) := lintegral_congr_ae hAm.ae_eq_mk
    _ = ∫⁻ ω, ∫⁻ t, hAm.mk _ (ω - (∑ i, ω i * e i) • e + t • e) ∂(gaussianReal 0 1) ∂(μ W L) :=
        lintegral_stdGauss_line e he1 hAm.measurable_mk
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (2 * M * κ) * ∫⁻ E in J, ∫⁻ t,
        ‖resolventMat (Hmat g W L (ω - (∑ i, ω i * e i) • e + t • e)) (E : ℂ) x y‖ₑ ^ u
          ∂(gaussianReal 0 1)) ^ (1 / (4 - u)) ∂(μ W L) := lintegral_mono_ae hstep
    _ ≤ (∫⁻ ω, ENNReal.ofReal (2 * M * κ) * (∫⁻ E in J, ∫⁻ t,
        ‖resolventMat (Hmat g W L (ω - (∑ i, ω i * e i) • e + t • e)) (E : ℂ) x y‖ₑ ^ u
          ∂(gaussianReal 0 1)) ∂(μ W L)) ^ (1 / (4 - u)) :=
        correlatorAverage_lintegral_rpow_le _ (hB1.const_mul _).aemeasurable hp0 hp1
    _ = (ENNReal.ofReal (2 * M * κ) * ∫⁻ E in J, (∫⁻ ω, ∫⁻ t,
        ‖resolventMat (Hmat g W L (ω - (∑ i, ω i * e i) • e + t • e)) (E : ℂ) x y‖ₑ ^ u
          ∂(gaussianReal 0 1) ∂(μ W L))) ^ (1 / (4 - u)) := by
        rw [lintegral_const_mul _ hB1, lintegral_lintegral_swap hB2.aemeasurable]
    _ = _ := by
        refine congrArg (fun z => (ENNReal.ofReal (2 * M * κ) * z) ^ (1 / (4 - u)))
          (lintegral_congr fun E => ?_)
        exact (lintegral_stdGauss_line e he1
          (correlatorAverage_measurable_resolvent g x y u continuous_const continuous_id)).symm

end LSBA
