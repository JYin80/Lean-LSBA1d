import LSBA.Flow.Surrogate
import LSBA.Prop.Objects
import LSBA.Loop.ErrorHierarchy

/-!
# The surrogate field of the mixed-pair errors

The `ℓ^{2q}` surrogate of a finite family of fields in the bounded `C^{1,2}` class is in the class,
with the chain rules for its generator and carré du champ; the mixed-pair loop errors `D₂` along
the flow as such a field, the bridge between the coordinate generator and the block generator,
and the generator identity for `D₂` split into the kernel-linear, quadratic and light terms of the
error hierarchy (5.17) [fo:eq:error-hierarchy].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

set_option maxSynthPendingDepth 3 in
/-- A real `C²` function of a vector field with bounded, jointly continuous `C^{1,2}` jet data is
in the bounded `C^{1,2}` class. -/
private theorem surrField_heat_vec {ι V : Type*} [Fintype ι] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [ProperSpace V] {Φ : V → ℝ} (hΦ : ContDiff ℝ 2 Φ) {a b : ℝ}
    (Yv Fv : ℝ → (ι → ℝ) → V) (DY : ℝ → (ι → ℝ) → ((ι → ℝ) →L[ℝ] V))
    (D2Y : ℝ → (ι → ℝ) → ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] V))
    (hYc : ContinuousOn (Function.uncurry Yv) (Set.Ioo a b ×ˢ Set.univ))
    (hFc : ContinuousOn (Function.uncurry Fv) (Set.Ioo a b ×ˢ Set.univ))
    (hDc : ContinuousOn (Function.uncurry DY) (Set.Ioo a b ×ˢ Set.univ))
    (hD2c : ContinuousOn (Function.uncurry D2Y) (Set.Ioo a b ×ˢ Set.univ))
    (hYt : ∀ r ∈ Set.Ioo a b, ∀ x, HasDerivAt (fun r' => Yv r' x) (Fv r x) r)
    (hYx : ∀ r ∈ Set.Ioo a b, ∀ x, HasFDerivAt (Yv r) (DY r x) x)
    (hDx : ∀ r ∈ Set.Ioo a b, ∀ x, HasFDerivAt (DY r) (D2Y r x) x) (K : ℝ)
    (hK : ∀ r ∈ Set.Ioo a b, ∀ x,
      ‖Yv r x‖ ≤ K ∧ ‖Fv r x‖ ≤ K ∧ ‖DY r x‖ ≤ K ∧ ‖D2Y r x‖ ≤ K) :
    HeatClass (fun r y => ((Φ (Yv r y) : ℝ) : ℂ)) a b := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hΦ1 : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (m := 1) (by norm_num)
  have hΦ1c : Continuous (fderiv ℝ Φ) := hΦ1.continuous
  have hΦ1d : Differentiable ℝ (fderiv ℝ Φ) := hΦ1.differentiable (by norm_num)
  have hΦ2c : Continuous (fderiv ℝ (fderiv ℝ Φ)) := hΦ1.continuous_fderiv (by norm_num)
  obtain ⟨B0, hB0⟩ := (isCompact_closedBall (0 : V) K).exists_bound_of_continuousOn
    hΦ.continuous.continuousOn
  obtain ⟨B1, hB1⟩ := (isCompact_closedBall (0 : V) K).exists_bound_of_continuousOn
    hΦ1c.continuousOn
  obtain ⟨B2, hB2⟩ := (isCompact_closedBall (0 : V) K).exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ Φ)) hΦ2c.continuousOn
  have hmem : ∀ r ∈ Set.Ioo a b, ∀ x, Yv r x ∈ Metric.closedBall (0 : V) K := fun r hr x =>
    mem_closedBall_zero_iff.2 (hK r hr x).1
  set P1 := ContinuousLinearMap.compL ℝ (ι → ℝ) ℝ ℂ Complex.ofRealCLM with hP1
  set Q1 := ContinuousLinearMap.compL ℝ (ι → ℝ) V ℝ with hQ1
  set Q2 := (ContinuousLinearMap.compL ℝ (ι → ℝ) V ℝ).flip with hQ2
  have hYc' : ContinuousOn (fun p : ℝ × (ι → ℝ) => Yv p.1 p.2) (Set.Ioo a b ×ˢ Set.univ) := hYc
  have hFc' : ContinuousOn (fun p : ℝ × (ι → ℝ) => Fv p.1 p.2) (Set.Ioo a b ×ˢ Set.univ) := hFc
  have hDc' : ContinuousOn (fun p : ℝ × (ι → ℝ) => DY p.1 p.2) (Set.Ioo a b ×ˢ Set.univ) := hDc
  have hD2c' : ContinuousOn (fun p : ℝ × (ι → ℝ) => D2Y p.1 p.2) (Set.Ioo a b ×ˢ Set.univ) := hD2c
  have h1c : ContinuousOn (fun p : ℝ × (ι → ℝ) => fderiv ℝ Φ (Yv p.1 p.2))
      (Set.Ioo a b ×ˢ Set.univ) := hΦ1c.comp_continuousOn hYc'
  have h2c : ContinuousOn (fun p : ℝ × (ι → ℝ) => fderiv ℝ (fderiv ℝ Φ) (Yv p.1 p.2))
      (Set.Ioo a b ×ˢ Set.univ) := hΦ2c.comp_continuousOn hYc'
  refine ⟨Complex.continuous_ofReal.comp_continuousOn (hΦ.continuous.comp_continuousOn hYc'),
    ⟨B0, fun r hr x => ?_⟩,
    ⟨fun r x => ((fderiv ℝ Φ (Yv r x) (Fv r x) : ℝ) : ℂ),
      fun r hr x => ((hΦd _).hasFDerivAt.comp_hasDerivAt r (hYt r hr x)).ofReal_comp,
      Complex.continuous_ofReal.comp_continuousOn (h1c.clm_apply hFc'), B1 * K,
      fun r hr x => ?_⟩,
    ⟨fun r x => P1 ((fderiv ℝ Φ (Yv r x)).comp (DY r x)),
      fun r x => P1.comp ((Q1 (fderiv ℝ Φ (Yv r x))).comp (D2Y r x) +
        (Q2 (DY r x)).comp ((fderiv ℝ (fderiv ℝ Φ) (Yv r x)).comp (DY r x))),
      fun r hr x => ?_, fun r hr x => ?_,
      P1.continuous.comp_continuousOn (h1c.clm_comp hDc'),
      continuousOn_const.clm_comp
        (((Q1.continuous.comp_continuousOn h1c).clm_comp hD2c').add
          ((Q2.continuous.comp_continuousOn hDc').clm_comp (h2c.clm_comp hDc'))),
      ‖P1‖ * (B1 * K) + ‖P1‖ * (‖Q1‖ * B1 * K + ‖Q2‖ * K * (B2 * K)),
      fun r hr x => ⟨?_, ?_⟩⟩⟩
  · rw [Complex.norm_real]
    exact hB0 _ (hmem r hr x)
  · obtain ⟨-, hF, -, -⟩ := hK r hr x
    have h1 := hB1 _ (hmem r hr x)
    rw [Complex.norm_real]
    exact ((fderiv ℝ Φ (Yv r x)).le_opNorm _).trans
      (mul_le_mul h1 hF (norm_nonneg _) ((norm_nonneg _).trans h1))
  · exact Complex.ofRealCLM.hasFDerivAt.comp x ((hΦd _).hasFDerivAt.comp x (hYx r hr x))
  · exact P1.hasFDerivAt.comp x
      (((hΦ1d _).hasFDerivAt.comp x (hYx r hr x)).clm_comp (hDx r hr x))
  · obtain ⟨hY0, -, hD, hD2⟩ := hK r hr x
    have h1 := hB1 _ (hmem r hr x)
    have h2 := hB2 _ (hmem r hr x)
    have hK0 : 0 ≤ K := (norm_nonneg _).trans hY0
    have hB10 : 0 ≤ B1 := (norm_nonneg _).trans h1
    have hB20 : 0 ≤ B2 := (norm_nonneg _).trans h2
    have hrest : 0 ≤ ‖P1‖ * (‖Q1‖ * B1 * K + ‖Q2‖ * K * (B2 * K)) := by positivity
    calc ‖P1 ((fderiv ℝ Φ (Yv r x)).comp (DY r x))‖
        ≤ ‖P1‖ * ‖(fderiv ℝ Φ (Yv r x)).comp (DY r x)‖ := P1.le_opNorm _
      _ ≤ ‖P1‖ * (B1 * K) := by
          gcongr
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul h1 hD (norm_nonneg _) hB10)
      _ ≤ _ := le_add_of_nonneg_right hrest
  · obtain ⟨hY0, -, hD, hD2⟩ := hK r hr x
    have h1 := hB1 _ (hmem r hr x)
    have h2 := hB2 _ (hmem r hr x)
    have hK0 : 0 ≤ K := (norm_nonneg _).trans hY0
    have hB10 : 0 ≤ B1 := (norm_nonneg _).trans h1
    have hB20 : 0 ≤ B2 := (norm_nonneg _).trans h2
    have hfirst : 0 ≤ ‖P1‖ * (B1 * K) := by positivity
    have hA : ‖(Q1 (fderiv ℝ Φ (Yv r x))).comp (D2Y r x)‖ ≤ ‖Q1‖ * B1 * K := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      refine mul_le_mul ((Q1.le_opNorm _).trans ?_) hD2 (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    have hB : ‖(Q2 (DY r x)).comp ((fderiv ℝ (fderiv ℝ Φ) (Yv r x)).comp (DY r x))‖ ≤
        ‖Q2‖ * K * (B2 * K) := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      refine mul_le_mul ((Q2.le_opNorm _).trans ?_) ?_ (norm_nonneg _) (by positivity)
      · exact mul_le_mul_of_nonneg_left hD (norm_nonneg _)
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul h2 hD (norm_nonneg _) hB20)
    calc ‖P1.comp ((Q1 (fderiv ℝ Φ (Yv r x))).comp (D2Y r x) +
          (Q2 (DY r x)).comp ((fderiv ℝ (fderiv ℝ Φ) (Yv r x)).comp (DY r x)))‖
        ≤ ‖P1‖ * ‖(Q1 (fderiv ℝ Φ (Yv r x))).comp (D2Y r x) +
          (Q2 (DY r x)).comp ((fderiv ℝ (fderiv ℝ Φ) (Yv r x)).comp (DY r x))‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖P1‖ * (‖Q1‖ * B1 * K + ‖Q2‖ * K * (B2 * K)) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hA hB)
      _ ≤ _ := le_add_of_nonneg_left hfirst

/-- A real `C²` function of a finite family of fields in the bounded `C^{1,2}` class is in the
class. -/
private theorem surrField_heat_comp {ι S : Type*} [Fintype ι] [Fintype S] {Φ : (S → ℂ) → ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (Y : S → ℝ → (ι → ℝ) → ℂ) {a b : ℝ}
    (hY : ∀ s, HeatClass (Y s) a b) :
    HeatClass (fun r y => ((Φ (fun s => Y s r y) : ℝ) : ℂ)) a b := by
  choose C hC using fun s => (hY s).bdd
  choose Fu hFu hFuc Cu hCu using fun s => (hY s).du
  choose DF D2F hD hD2 hDc hD2c Cd hCd using fun s => (hY s).dx
  have hKs : ∀ s, C s ≤ ∑ s, (|C s| + |Cu s| + |Cd s|) ∧ Cu s ≤ ∑ s, (|C s| + |Cu s| + |Cd s|) ∧
      Cd s ≤ ∑ s, (|C s| + |Cu s| + |Cd s|) := by
    intro s
    have h := Finset.single_le_sum (f := fun s => |C s| + |Cu s| + |Cd s|)
      (fun s _ => by positivity) (Finset.mem_univ s)
    have h1 := le_abs_self (C s)
    have h2 := le_abs_self (Cu s)
    have h3 := le_abs_self (Cd s)
    have h4 := abs_nonneg (C s)
    have h5 := abs_nonneg (Cu s)
    have h6 := abs_nonneg (Cd s)
    refine ⟨by linarith, by linarith, by linarith⟩
  have hK0 : 0 ≤ ∑ s, (|C s| + |Cu s| + |Cd s|) := Finset.sum_nonneg fun s _ => by positivity
  set eL := (ContinuousLinearMap.piEquivL ℝ (ι → ℝ) (fun _ : S => ℂ)).toContinuousLinearMap
    with heL
  set e2 := (ContinuousLinearMap.piEquivL ℝ (ι → ℝ)
    (fun _ : S => (ι → ℝ) →L[ℝ] ℂ)).toContinuousLinearMap with he2
  refine surrField_heat_vec hΦ (fun r x s => Y s r x) (fun r x s => Fu s r x)
    (fun r x => eL (fun s => DF s r x)) (fun r x => eL.comp (e2 (fun s => D2F s r x)))
    (continuousOn_pi.2 fun s => (hY s).cont) (continuousOn_pi.2 fun s => hFuc s)
    (eL.continuous.comp_continuousOn (continuousOn_pi.2 fun s => hDc s))
    (continuousOn_const.clm_comp
      (e2.continuous.comp_continuousOn (continuousOn_pi.2 fun s => hD2c s)))
    (fun r hr x => hasDerivAt_pi.2 fun s => hFu s r hr x)
    (fun r hr x => hasFDerivAt_pi.2 fun s => hD s r hr x)
    (fun r hr x => eL.hasFDerivAt.comp x (hasFDerivAt_pi.2 fun s => hD2 s r hr x))
    ((‖eL‖ + 1) * ∑ s, (|C s| + |Cu s| + |Cd s|)) fun r hr x => ?_
  set K := ∑ s, (|C s| + |Cu s| + |Cd s|) with hK
  have hKle : K ≤ (‖eL‖ + 1) * K := by nlinarith [norm_nonneg eL]
  have hKle' : ‖eL‖ * K ≤ (‖eL‖ + 1) * K := by nlinarith [norm_nonneg eL]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ((pi_norm_le_iff_of_nonneg hK0).2 fun s => ?_).trans hKle
    exact (hC s r hr x).trans (hKs s).1
  · refine ((pi_norm_le_iff_of_nonneg hK0).2 fun s => ?_).trans hKle
    exact (hCu s r hr x).trans (hKs s).2.1
  · refine (eL.le_opNorm _).trans (le_trans ?_ hKle')
    refine mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg hK0).2 fun s => ?_) (norm_nonneg _)
    exact (hCd s r hr x).1.trans (hKs s).2.2
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (le_trans ?_ hKle')
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine ContinuousLinearMap.norm_pi_le_of_le (fun s => ?_) hK0
    exact (hCd s r hr x).2.trans (hKs s).2.2

/-- The `ℓ^{2q}` surrogate of a finite family of fields in the bounded `C^{1,2}` class is in the
class. -/
theorem heatClass_lqSurr {ι S : Type*} [Fintype ι] [Fintype S] {q : ℕ} (hq : 1 ≤ q)
    {env : S → ℝ} (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ) (Y : S → ℝ → (ι → ℝ) → ℂ)
    {a b : ℝ} (hY : ∀ s, HeatClass (Y s) a b) :
    HeatClass (fun r y => ((lqSurr q env δ (fun s => Y s r y) : ℝ) : ℂ)) a b := by
  exact surrField_heat_comp (lqSurr_contDiff hq henv hδ) Y hY

/-- The second derivative of the complex cast of a real `C²` function is the cast of its second
derivative. -/
private theorem surrField_iter2_ofReal {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) :
    iteratedDeriv 2 (fun e : ℝ => ((g e : ℝ) : ℂ)) 0 = ((iteratedDeriv 2 g 0 : ℝ) : ℂ) := by
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdg : Differentiable ℝ (deriv g) := hg.differentiable_deriv_two
  have hd1 : deriv (fun e : ℝ => ((g e : ℝ) : ℂ)) = fun e => ((deriv g e : ℝ) : ℂ) :=
    funext fun e => (hg1 e).hasDerivAt.ofReal_comp.deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd1, iteratedDeriv_succ, iteratedDeriv_one]
  exact (hdg 0).hasDerivAt.ofReal_comp.deriv

/-- Second-order chain rule `(Φ ∘ g)''(0) = D²Φ(g 0)[g'(0), g'(0)] + DΦ(g 0)[g''(0)]`. -/
private theorem surrField_iter2_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → ℝ} (hΦ : ContDiff ℝ 2 Φ) {g : ℝ → E} (hg : ContDiff ℝ 2 g) :
    iteratedDeriv 2 (fun e => Φ (g e)) 0 =
      fderiv ℝ (fderiv ℝ Φ) (g 0) (deriv g 0) (deriv g 0) +
        fderiv ℝ Φ (g 0) (deriv (deriv g) 0) := by
  have hΦ1 : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hΦ2 : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hg2 : Differentiable ℝ (deriv g) := hg.differentiable_deriv_two
  have hd : deriv (fun e => Φ (g e)) = fun e => fderiv ℝ Φ (g e) (deriv g e) :=
    funext fun e => ((hΦ1 (g e)).hasFDerivAt.comp_hasDerivAt e (hg1 e).hasDerivAt).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
  exact (((hΦ2 (g 0)).hasFDerivAt.comp_hasDerivAt 0 (hg1 0).hasDerivAt).clm_apply
    (hg2 0).hasDerivAt).deriv

/-- The coordinate line `e ↦ (Y_s(y + e δ_i))_s` of a finite family. -/
private theorem surrField_line {ι S : Type*} [Fintype ι] [Fintype S] (Y : S → (ι → ℝ) → ℂ)
    (y : ι → ℝ) (hYy : ∀ s, ContDiff ℝ 2 (Y s)) (i : ι) :
    ContDiff ℝ 2 (fun e : ℝ => fun s => Y s (y + e • Pi.single i 1)) ∧
    (fun s => Y s (y + (0 : ℝ) • Pi.single i 1)) = (fun s => Y s y) ∧
    deriv (fun e : ℝ => fun s => Y s (y + e • Pi.single i 1)) 0 =
      (fun s => deriv (fun e : ℝ => Y s (y + e • Pi.single i 1)) 0) ∧
    deriv (deriv (fun e : ℝ => fun s => Y s (y + e • Pi.single i 1))) 0 =
      (fun s => iteratedDeriv 2 (fun e : ℝ => Y s (y + e • Pi.single i 1)) 0) := by
  have hl : ∀ s, ContDiff ℝ 2 (fun e : ℝ => Y s (y + e • Pi.single i 1)) := fun s =>
    (hYy s).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hd1 : ∀ s, Differentiable ℝ (fun e : ℝ => Y s (y + e • Pi.single i 1)) := fun s =>
    (hl s).differentiable (by norm_num)
  have hd2 : ∀ s, Differentiable ℝ (deriv (fun e : ℝ => Y s (y + e • Pi.single i 1))) := fun s =>
    (hl s).differentiable_deriv_two
  have hD : deriv (fun e : ℝ => fun s => Y s (y + e • Pi.single i 1)) =
      fun e => fun s => deriv (fun e : ℝ => Y s (y + e • Pi.single i 1)) e :=
    funext fun e => deriv_pi fun s => hd1 s e
  refine ⟨contDiff_pi.2 hl, by simp, by rw [hD], ?_⟩
  rw [hD, deriv_pi fun s => hd2 s 0]
  funext s
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- Chain rule for a real `C²` function of a finite family of fields:
`𝒢(Φ ∘ Y) = DΦ(Y)[𝒢Y] + (σ²/2) Σ_i D²Φ(Y)[∂_iY, ∂_iY]`. -/
theorem coordGen_comp_vec {ι S : Type*} [Fintype ι] [Fintype S] (σ2 : ℝ) (Φ : (S → ℂ) → ℝ)
    (hΦ : ContDiff ℝ 2 Φ) (Y : S → ℝ → (ι → ℝ) → ℂ) (u : ℝ) (y : ι → ℝ)
    (hYu : ∀ s, DifferentiableAt ℝ (fun r => Y s r y) u) (hYy : ∀ s, ContDiff ℝ 2 (Y s u)) :
    coordGen σ2 (fun r z => ((Φ (fun s => Y s r z) : ℝ) : ℂ)) u y =
      ((fderiv ℝ Φ (fun s => Y s u y) (fun s => coordGen σ2 (Y s) u y) +
        σ2 / 2 * ∑ i, fderiv ℝ (fderiv ℝ Φ) (fun s => Y s u y)
          (fun s => deriv (fun e : ℝ => Y s u (y + e • Pi.single i 1)) 0)
          (fun s => deriv (fun e : ℝ => Y s u (y + e • Pi.single i 1)) 0) : ℝ) : ℂ) := by
  have hΦ1 : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hT : deriv (fun r => ((Φ (fun s => Y s r y) : ℝ) : ℂ)) u =
      ((fderiv ℝ Φ (fun s => Y s u y) (fun s => deriv (fun r => Y s r y) u) : ℝ) : ℂ) :=
    ((hΦ1 _).hasFDerivAt.comp_hasDerivAt u
      (hasDerivAt_pi.2 fun s => (hYu s).hasDerivAt)).ofReal_comp.deriv
  have hS : ∀ i : ι, iteratedDeriv 2
      (fun e : ℝ => ((Φ (fun s => Y s u (y + e • Pi.single i 1)) : ℝ) : ℂ)) 0 =
      ((fderiv ℝ (fderiv ℝ Φ) (fun s => Y s u y)
          (fun s => deriv (fun e : ℝ => Y s u (y + e • Pi.single i 1)) 0)
          (fun s => deriv (fun e : ℝ => Y s u (y + e • Pi.single i 1)) 0) +
        fderiv ℝ Φ (fun s => Y s u y)
          (fun s => iteratedDeriv 2 (fun e : ℝ => Y s u (y + e • Pi.single i 1)) 0) : ℝ) : ℂ) := by
    intro i
    obtain ⟨hc, h0, h1, h2⟩ := surrField_line (fun s => Y s u) y hYy i
    have h := surrField_iter2_ofReal
      (g := fun e : ℝ => Φ (fun s => Y s u (y + e • Pi.single i 1))) (hΦ.comp hc)
    rw [h, surrField_iter2_comp hΦ hc, h0, h1, h2]
  have hV : (fun s => coordGen σ2 (Y s) u y) = (fun s => deriv (fun r => Y s r y) u) +
      (σ2 / 2) • ∑ i : ι,
        (fun s => iteratedDeriv 2 (fun e : ℝ => Y s u (y + e • Pi.single i 1)) 0) := by
    funext s
    simp [coordGen, Finset.sum_apply, Complex.real_smul]
  rw [hV]
  simp only [coordGen]
  rw [hT]
  simp only [hS, map_add, map_smul, map_sum, smul_eq_mul]
  push_cast
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  ring

/-- Carré du champ of a real `C²` function of a finite family of fields:
`Γ(Φ ∘ Y) = σ² Σ_i (DΦ(Y)[∂_iY])²`. -/
theorem coordGamma_comp_vec {ι S : Type*} [Fintype ι] [Fintype S] (σ2 : ℝ) (Φ : (S → ℂ) → ℝ)
    (hΦ : ContDiff ℝ 2 Φ) (Y : S → (ι → ℝ) → ℂ) (y : ι → ℝ) (hYy : ∀ s, ContDiff ℝ 2 (Y s)) :
    coordGamma σ2 (fun z => ((Φ (fun s => Y s z) : ℝ) : ℂ))
        (fun z => ((Φ (fun s => Y s z) : ℝ) : ℂ)) y =
      ((σ2 * ∑ i, (fderiv ℝ Φ (fun s => Y s y)
        (fun s => deriv (fun e : ℝ => Y s (y + e • Pi.single i 1)) 0)) ^ 2 : ℝ) : ℂ) := by
  have hΦ1 : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hD : ∀ i : ι, deriv (fun e : ℝ => ((Φ (fun s => Y s (y + e • Pi.single i 1)) : ℝ) : ℂ)) 0 =
      ((fderiv ℝ Φ (fun s => Y s y)
        (fun s => deriv (fun e : ℝ => Y s (y + e • Pi.single i 1)) 0) : ℝ) : ℂ) := by
    intro i
    obtain ⟨hc, h0, h1, -⟩ := surrField_line Y y hYy i
    have := ((hΦ1 _).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hc.differentiable (by norm_num)) 0).hasDerivAt).ofReal_comp.deriv
    rw [h0, h1] at this
    exact this
  unfold coordGamma
  simp only [hD, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring_nf

/-- A convex `C²` function has nonnegative second derivative in every direction. -/
private theorem surrField_hess_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → ℝ} (hΦ : ContDiff ℝ 2 Φ) (hc : ConvexOn ℝ Set.univ Φ) (y v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ Φ) y v v := by
  have hΦ1 : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hΦ2 : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => y + t • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => Φ (y + t • v)) := by
    refine ⟨convex_univ, fun t _ t' _ a b ha hb hab => ?_⟩
    have h := hc.2 (Set.mem_univ (y + t • v)) (Set.mem_univ (y + t' • v)) ha hb hab
    have e : a • (y + t • v) + b • (y + t' • v) = y + (a • t + b • t') • v := by
      rw [smul_eq_mul, smul_eq_mul, smul_add, smul_add, smul_smul, smul_smul, add_smul]
      calc a • y + (a * t) • v + (b • y + (b * t') • v)
          = (a • y + b • y) + ((a * t) • v + (b * t') • v) := by abel
        _ = y + ((a * t) • v + (b * t') • v) := by rw [← add_smul, hab, one_smul]
    rw [e] at h
    exact h
  have hd : ∀ t, DifferentiableAt ℝ (fun t : ℝ => Φ (y + t • v)) t := fun t =>
    ((hΦ1 _).hasFDerivAt.comp_hasDerivAt t (hg t)).differentiableAt
  have hmono : Monotone (deriv fun t : ℝ => Φ (y + t • v)) :=
    monotoneOn_univ.1 (hconv.monotoneOn_deriv fun t _ => hd t)
  have h0 := hmono.deriv_nonneg (x := 0)
  have hD : deriv (fun t : ℝ => Φ (y + t • v)) = fun t => fderiv ℝ Φ (y + t • v) v :=
    funext fun t => ((hΦ1 _).hasFDerivAt.comp_hasDerivAt t (hg t)).deriv
  rw [hD] at h0
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ Φ (y + t • v) v)
      (fderiv ℝ (fderiv ℝ Φ) y v v + fderiv ℝ Φ (y + (0 : ℝ) • v) 0) 0 :=
    ((hΦ2 y).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hg 0) (by simp)).clm_apply
      (hasDerivAt_const (0 : ℝ) v)
  rw [h2.deriv, map_zero, add_zero] at h0
  exact h0

/-- The surrogate of the empty family is `0`. -/
private theorem surrField_lqSurr_empty {S : Type*} [Fintype S] [IsEmpty S] {q : ℕ} (hq : 1 ≤ q)
    (env : S → ℝ) (δ : ℝ) : lqSurr q env δ = fun _ => 0 := by
  funext y
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [lqSurr, Finset.univ_eq_empty, Finset.sum_empty]
  exact Real.zero_rpow (by positivity)

/-- `Re Γ(Y) = σ² Σ_i |∂_i Y|²`. -/
private theorem surrField_gamma_re {ι : Type*} [Fintype ι] (σ2 : ℝ) (F : (ι → ℝ) → ℂ)
    (y : ι → ℝ) :
    (coordGamma σ2 F F y).re =
      σ2 * ∑ i, ‖deriv (fun e : ℝ => F (y + e • Pi.single i 1)) 0‖ ^ 2 := by
  unfold coordGamma
  simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e : ((σ2 : ℂ) * ∑ i, ((‖deriv (fun e : ℝ => F (y + e • Pi.single i 1)) 0‖ : ℝ) : ℂ) ^ 2) =
      ((σ2 * ∑ i, ‖deriv (fun e : ℝ => F (y + e • Pi.single i 1)) 0‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  push_cast
  rw [e, Complex.ofReal_re]

/-- Rates of the surrogate from rates of its components: `|𝒢Y_s|/env_s ≤ κ₁` and
`Re Γ(Y_s)/env_s² ≤ h` give `|Re 𝒢X| ≤ |S|^{1/(2q)}κ₁ + q|S|^{1/q}h/X` and
`Re Γ(X) ≤ |S|^{1/q}h` for `X = lqSurr q env δ Y`. -/
theorem coordGen_lqSurr_le {ι S : Type*} [Fintype ι] [Fintype S] (σ2 : ℝ) (hσ2 : 0 ≤ σ2)
    {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ} (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ)
    (Y : S → ℝ → (ι → ℝ) → ℂ) (u : ℝ) (y : ι → ℝ)
    (hYu : ∀ s, DifferentiableAt ℝ (fun r => Y s r y) u) (hYy : ∀ s, ContDiff ℝ 2 (Y s u))
    {κ₁ h : ℝ} (hgen : ∀ s, ‖coordGen σ2 (Y s) u y‖ / env s ≤ κ₁)
    (hgam : ∀ s, (coordGamma σ2 (Y s u) (Y s u) y).re / env s ^ 2 ≤ h) :
    |(coordGen σ2 (fun r z => ((lqSurr q env δ (fun s => Y s r z) : ℝ) : ℂ)) u y).re| ≤
        (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) * κ₁ +
          q * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * h / lqSurr q env δ (fun s => Y s u y) ∧
      (coordGamma σ2 (fun z => ((lqSurr q env δ (fun s => Y s u z) : ℝ) : ℂ))
          (fun z => ((lqSurr q env δ (fun s => Y s u z) : ℝ) : ℂ)) y).re ≤
        (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * h := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hΦ := lqSurr_contDiff hq henv hδ
  have hG := coordGamma_comp_vec σ2 (lqSurr q env δ) hΦ (fun s => Y s u) y hYy
  rw [coordGen_comp_vec σ2 (lqSurr q env δ) hΦ Y u y hYu hYy, hG, Complex.ofReal_re,
    Complex.ofReal_re]
  rcases isEmpty_or_nonempty S with hS | hS
  · have hc : (Fintype.card S : ℝ) = 0 := by simp
    rw [surrField_lqSurr_empty hq env δ, hc, Real.zero_rpow (by positivity),
      Real.zero_rpow (by positivity)]
    simp
  set X := lqSurr q env δ (fun s => Y s u y) with hX
  set c1 := (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) with hc1
  set c2 := (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) with hc2
  set dY : ι → S → ℂ := fun i s => deriv (fun e : ℝ => Y s u (y + e • Pi.single i 1)) 0 with hdY
  set G := ⨆ s, ∑ i, ‖dY i s‖ ^ 2 / env s ^ 2 with hGdef
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have hXpos : 0 < X := by
    have hN : 0 < ∑ s, (‖Y s u y‖ ^ 2 / env s ^ 2 + δ ^ 2) ^ q :=
      Finset.sum_pos (fun s _ => by have := henv s; positivity) Finset.univ_nonempty
    exact Real.rpow_pos_of_pos hN _
  have hσG : σ2 * G ≤ h := by
    rw [hGdef, Real.mul_iSup_of_nonneg hσ2]
    refine ciSup_le fun s => ?_
    have := hgam s
    rw [surrField_gamma_re] at this
    have hs := henv s
    calc σ2 * ∑ i, ‖dY i s‖ ^ 2 / env s ^ 2
        = (σ2 * ∑ i, ‖deriv (fun e : ℝ => Y s u (y + e • Pi.single i 1)) 0‖ ^ 2) / env s ^ 2 := by
          rw [← Finset.sum_div, mul_div_assoc]
      _ ≤ h := this
  have hA := lqSurr_fderiv_le hq henv hδ (fun s => Y s u y) (fun s => coordGen σ2 (Y s) u y)
  have hA' : c1 * (⨆ s, ‖coordGen σ2 (Y s) u y‖ / env s) ≤ c1 * κ₁ :=
    mul_le_mul_of_nonneg_left (ciSup_le hgen) hc10
  have hH := lqSurr_hessian_le hq henv hδ dY (fun s => Y s u y)
  have hH0 : 0 ≤ ∑ i, fderiv ℝ (fderiv ℝ (lqSurr q env δ)) (fun s => Y s u y) (dY i) (dY i) :=
    Finset.sum_nonneg fun i _ =>
      surrField_hess_nonneg hΦ (lqSurr_convexOn hq henv hδ) _ _
  have hΓ := lqSurr_gamma_le hq henv hδ dY (fun s => Y s u y)
  constructor
  · set H := ∑ i, fderiv ℝ (fderiv ℝ (lqSurr q env δ)) (fun s => Y s u y) (dY i) (dY i) with hHdef
    have hB : σ2 / 2 * H ≤ q * c2 * h / X := by
      have h1 : σ2 / 2 * H ≤ σ2 / 2 * (2 * q * c2 * G / X) :=
        mul_le_mul_of_nonneg_left hH (by positivity)
      have h2 : σ2 / 2 * (2 * q * c2 * G / X) = q * c2 * (σ2 * G) / X := by
        field_simp
      have h3 : q * c2 * (σ2 * G) / X ≤ q * c2 * h / X := by
        apply div_le_div_of_nonneg_right _ hXpos.le
        exact mul_le_mul_of_nonneg_left hσG (by positivity)
      linarith
    have hB0 : 0 ≤ σ2 / 2 * H := mul_nonneg (by positivity) hH0
    calc |fderiv ℝ (lqSurr q env δ) (fun s => Y s u y) (fun s => coordGen σ2 (Y s) u y) +
          σ2 / 2 * H|
        ≤ |fderiv ℝ (lqSurr q env δ) (fun s => Y s u y) (fun s => coordGen σ2 (Y s) u y)| +
            |σ2 / 2 * H| := abs_add_le _ _
      _ ≤ c1 * κ₁ + q * c2 * h / X := by
          rw [abs_of_nonneg hB0]
          linarith
  · calc σ2 * ∑ i, (fderiv ℝ (lqSurr q env δ) (fun s => Y s u y) (dY i)) ^ 2
        ≤ σ2 * (c2 * G) := mul_le_mul_of_nonneg_left hΓ hσ2
      _ = c2 * (σ2 * G) := by ring
      _ ≤ c2 * h := mul_le_mul_of_nonneg_left hσG hc20

/-- The mixed two-loop error `D₂(r; a, b; +, -) = ℒ₂ - 𝒦₂` of (5.17) [fo:eq:error-hierarchy] as a
field of the Gaussian block coordinates, at the slice `A_g ⊗ I + Σ x_{c,k} T_{c,k}`. -/
def pairErrField (g E : ℝ) (m : ℂ) (W L : ℕ) (r : ℝ) (x : Ω W L) (ab : Fin L × Fin L) : ℂ :=
  loopTr (resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) x)
      (zChar g E m r)) ![ab.1, ab.2] ![true, false] -
    primLoop g W L E m r ![ab.1, ab.2] ![true, false]

/-- The mixed two-loop error at a flow point is the field `pairErrField` at the scaled Gaussian
coordinates `√(uγ_g/W) ω`, the single-time realization of (5.1) [fo:eq:flow]. -/
theorem flowErr_eq_pairErrField (W : ℕ) (p : FlowPt) (hu : 0 ≤ p.u) (a b : Fin p.L)
    (ω : Ω W p.L) :
    flowErr W p ![a, b] ![true, false] ω =
      pairErrField p.g p.E (mRoot p.g p.L p.E) W p.L p.u
        (Real.sqrt (p.u * (gammaG p.g / W)) • ω) (a, b) := by
  have hγ : 0 ≤ gammaG p.g := by unfold gammaG; positivity
  unfold flowErr flowG flowH pairErrField
  rw [blockFlow_eq_blockSlice _ _ _ (mul_nonneg hu hγ), mul_div_assoc]

/-- `A_g ⊗ I` is Hermitian. -/
private theorem surrField_herm (g : ℝ) (W L : ℕ) :
    (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
  have hA : (Ag g L).IsHermitian := by
    unfold Matrix.IsHermitian Ag
    rw [Matrix.conjTranspose_smul, (cycleAdj_isHermitian L).eq]
    simp
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, hA.eq, Matrix.conjTranspose_one]

/-- Primitive loops of every length are continuous in time on `(-1, 1)` at a root. -/
private theorem surrField_primLoop_contOn (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L) (E : ℝ)
    (m : ℂ) (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {n : ℕ} (a : Fin n → Fin L)
    (σ : Fin n → Bool) : ContinuousOn (fun r => primLoop g W L E m r a σ) (Set.Ioo (-1) 1) := by
  rcases n with _ | _ | n
  · exact continuousOn_const (c := primLoop g W L E m 0 a σ)
  · exact continuousOn_const (c := primLoop g W L E m 0 a σ)
  · exact fun r hr => (primLoop_hasDerivAt g W L hW hL E m hm r hr (by omega) a σ).continuousAt
      |>.continuousWithinAt

/-- The primitive loops satisfy (5.10) [fo:eq:primitive] at every `u ∈ (-1, 1)`, all lengths. -/
private theorem surrField_primDeriv (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (u : ℝ) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    IsPrimDeriv (gammaG g) W L (fun r n b τ => primLoop g W L E m r (k := n) b τ) u := by
  intro n a σ
  rcases n with _ | _ | n
  · have h0 : cutSumFam (fun n b τ => primLoop g W L E m u (k := n) b τ) a σ = 0 := by
      simp [cutSumFam]
    rw [h0, mul_zero]
    exact hasDerivAt_const u (primLoop g W L E m 0 a σ)
  · have h1 : cutSumFam (fun n b τ => primLoop g W L E m u (k := n) b τ) a σ = 0 := by
      simp [cutSumFam]
    rw [h1, mul_zero]
    exact hasDerivAt_const u (primLoop g W L E m 0 a σ)
  · exact primLoop_hasDerivAt g W L hW hL E m hm u hu (by omega) a σ

/-- The mixed two-loop error field is in the bounded `C^{1,2}` class on every `(a, b)` with
`-1 < a` and `b < 1`, at a root of (5.2) [fo:eq:dyson-family]. -/
theorem heatClass_pairErrField (g E : ℝ) (m : ℂ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (ab : Fin L × Fin L) {a b : ℝ} (ha : -1 < a)
    (hb : b < 1) :
    HeatClass (fun r x => pairErrField g E m W L r x ab) a b := by
  have hsub : Set.Ioo a b ⊆ Set.Ioo (-1) 1 := fun r hr => ⟨ha.trans hr.1, hr.2.trans hb⟩
  have hIcc : Set.Icc a b ⊆ Set.Ioo (-1) 1 := fun r hr =>
    ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  set κ : ℝ → ℂ := fun r => primLoop g W L E m r ![ab.1, ab.2] ![true, false] with hκdef
  set κ' : ℝ → ℂ := fun r => ((gammaG g * W : ℝ) : ℂ) *
    cutSumFam (fun n c τ => primLoop g W L E m r (k := n) c τ) ![ab.1, ab.2] ![true, false]
    with hκ'def
  have hc : ContinuousOn κ (Set.Ioo (-1) 1) :=
    surrField_primLoop_contOn g W L hW hL E m hm _ _
  have hc' : ContinuousOn κ' (Set.Ioo (-1) 1) := by
    refine continuousOn_const.mul ?_
    unfold cutSumFam
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    split_ifs
    · exact continuousOn_finsetSum _ fun c _ =>
        (surrField_primLoop_contOn g W L hW hL E m hm _ _).mul
          (surrField_primLoop_contOn g W L hW hL E m hm _ _)
    · exact continuousOn_const
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.mono hIcc)
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc'.mono hIcc)
  have h := (heatClass_loopTr W L 2 _ (surrField_herm g W L) g E m hm.1 ![ab.1, ab.2]
    ![true, false] (a' := a) hb).sub_time κ κ'
    (fun r hr => primLoop_hasDerivAt g W L hW hL E m hm r (hsub hr) le_rfl _ _)
    (hc'.mono hsub)
    ⟨max C₁ C₂, fun r hr => ⟨(hC₁ r (Set.Ioo_subset_Icc_self hr)).trans (le_max_left _ _),
      (hC₂ r (Set.Ioo_subset_Icc_self hr)).trans (le_max_right _ _)⟩⟩
  exact h

/-- The cut terms of (5.17) [fo:eq:error-hierarchy] at `k = 2`, `(a, b; +, -)`. -/
private theorem surrField_cutErrSum_two {L : ℕ} (K D : LoopFam L) (a b : Fin L) :
    cutErrSum K D ![a, b] ![true, false] = ∑ c : Fin L,
      (K 2 ![c, b] ![true, false] * D 2 ![a, c] ![true, false] +
        D 2 ![c, b] ![true, false] * K 2 ![a, c] ![true, false] +
        D 2 ![c, b] ![true, false] * D 2 ![a, c] ![true, false]) := by
  unfold cutErrSum
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  have h00 : ¬((0 : Fin 2) < 0) := by decide
  have h01 : (0 : Fin 2) < 1 := by decide
  have h10 : ¬((1 : Fin 2) < 0) := by decide
  have h11 : ¬((1 : Fin 2) < 1) := by decide
  simp only [h00, h01, h10, h11, ↓reduceIte, zero_add, add_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hL : cutLLab ![a, b] (0 : Fin 2) 1 c = ![c, b] := by
    funext p; fin_cases p <;> rfl
  have hLs : cutLSgn ![true, false] (0 : Fin 2) 1 = ![true, false] := by
    funext p; fin_cases p <;> rfl
  have hR : cutRLab ![a, b] (0 : Fin 2) 1 c = ![a, c] := by
    funext p; fin_cases p <;> rfl
  have hRs : cutRSgn ![true, false] (0 : Fin 2) 1 = ![true, false] := by
    funext p; fin_cases p <;> rfl
  rw [hL, hLs, hR, hRs]
  rfl

/-- (C.16) [fo:eq:pair-error] in generator form: `𝒢D₂(a,b;+,-) = 𝒲₂ + (P_u D₂ + D₂ P_u)(a,b) +
γ_gW Σ_c D₂(a,c) D₂(c,b)` with `P_u = P(I - uP)⁻¹`, from (5.17) [fo:eq:error-hierarchy] at the
primitive loops. -/
theorem blockGen_pairErr (g E : ℝ) (m : ℂ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian) (a b : Fin L) :
    blockGen W L (gammaG g) (fun r N => resLoop g E m ![a, b] ![true, false] r N -
        primLoop g W L E m r ![a, b] ![true, false]) u M =
      lightW g E m ![a, b] ![true, false] u M +
        ∑ c : Fin L,
          ((((mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) u a c : ℝ) : ℂ) *
              (resLoop g E m ![c, b] ![true, false] u M -
                primLoop g W L E m u ![c, b] ![true, false])) +
            (resLoop g E m ![a, c] ![true, false] u M -
                primLoop g W L E m u ![a, c] ![true, false]) *
              ((mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) u c b : ℝ) : ℂ)) +
        ((gammaG g * W : ℝ) : ℂ) * ∑ c : Fin L,
          (resLoop g E m ![a, c] ![true, false] u M - primLoop g W L E m u ![a, c] ![true, false]) *
            (resLoop g E m ![c, b] ![true, false] u M -
              primLoop g W L E m u ![c, b] ![true, false]) := by
  have h := blockGen_errorLoop g E m hm.1 hu.2 hM _ (surrField_primDeriv g W L hW hL E m hm u hu)
    ![a, b] ![true, false]
  rw [h, add_assoc]
  congr 1
  have hγ : 0 < gammaG g := by
    unfold gammaG
    have : (1 : ℝ) ≤ max 1 g := le_max_left _ _
    positivity
  have hγW : ((gammaG g * W : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < W := by exact_mod_cast hW
    exact_mod_cast (mul_pos hγ this).ne'
  have hK : ∀ x y : Fin L, ((gammaG g * W : ℝ) : ℂ) * primLoop g W L E m u ![x, y] ![true, false] =
      ((mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) u x y : ℝ) : ℂ) := by
    intro x y
    rw [primLoop_two_pm, ← mul_assoc, mul_inv_cancel₀ hγW, one_mul]
  rw [surrField_cutErrSum_two]
  simp only [errFam, resLoop]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  linear_combination
    (loopTr (resolventMat M (zChar g E m u)) ![a, c] ![true, false] -
      primLoop g W L E m u ![a, c] ![true, false]) * hK c b +
    (loopTr (resolventMat M (zChar g E m u)) ![c, b] ![true, false] -
      primLoop g W L E m u ![c, b] ![true, false]) * hK a c

/-- The bracket of the mixed two-loop error is the bracket of the loop, (5.9) [gc:eq:bracket]:
the deterministic primitive loop does not move with the matrix. -/
theorem blockGamma_pairErr (g E : ℝ) (m : ℂ) (W L : ℕ) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    blockGamma W L (gammaG g)
        (fun N => resLoop g E m ![a, b] ![true, false] u N - primLoop g W L E m u ![a, b] ![true, false])
        (fun N => resLoop g E m ![a, b] ![true, false] u N - primLoop g W L E m u ![a, b] ![true, false])
        M =
      blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, false] u)
        (resLoop g E m ![a, b] ![true, false] u) M := by
  unfold blockGamma
  simp only [deriv_sub_const]

end LSBA
