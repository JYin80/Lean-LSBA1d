import LSBA.Upper.CoercivityMap

/-!
# Smooth steps and inverse-norm cutoffs

Two smooth steps built from `Real.smoothTransition`: `stepDown` is `1` on `(-∞, 1]` and `0` on
`[2, ∞)`; `stepUp` is `0` on `(-∞, 1]` and `1` on `[2, ∞)`; both take values in `[0, 1]` and have
bounded derivatives. The inverse-norm cutoff `normCut L Y` is `stepDown (‖Y‖²_HS / L)` for an
invertible `Y` and `0` otherwise. As a function of `X`, `X ↦ normCut L X⁻¹` is smooth on all
matrices: it vanishes on a neighbourhood of every singular matrix, because `‖X⁻¹‖_HS` blows up
there; its topological support lies in `{X invertible, ‖X⁻¹‖²_HS ≤ 2 L}` and it equals `1` where
`‖X⁻¹‖²_HS ≤ L`. These are the smooth support restrictions with nested margins of Section 9.4.4
[su:sec:cutoff-estimates].
-/

open Real

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The smooth step `1` on `(-∞, 1]`, `0` on `[2, ∞)`. -/
def stepDown (s : ℝ) : ℝ := Real.smoothTransition (2 - s)

/-- The smooth step `0` on `(-∞, 1]`, `1` on `[2, ∞)`. -/
def stepUp (s : ℝ) : ℝ := Real.smoothTransition (s - 1)

/-- The inverse-norm cutoff: `stepDown (‖Y‖²_HS / L)` for invertible `Y`, `0` otherwise. -/
def normCut {n : Type*} [Fintype n] [DecidableEq n] (L : ℝ) (Y : Matrix n n ℂ) : ℝ :=
  if IsUnit Y then stepDown (hsSq Y / L) else 0

private lemma StepCutoff_deriv_phi_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have h : Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [h.deriv_eq]; simp
  · have h : Real.smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [h.deriv_eq]; simp

private lemma StepCutoff_deriv_phi_bound : ∃ M : ℝ, ∀ x, |deriv Real.smoothTransition x| ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 1) isCompact_Icc ?_
    intro x hx
    apply StepCutoff_deriv_phi_zero
    by_contra h
    rw [not_or, not_lt, not_lt] at h
    exact hx ⟨h.1, h.2⟩
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨M, fun x => by simpa using hM x⟩

private lemma StepCutoff_stepDown_of_le {s : ℝ} (h : s ≤ 1) : stepDown s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private lemma StepCutoff_stepDown_of_ge {s : ℝ} (h : 2 ≤ s) : stepDown s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private lemma StepCutoff_stepDown_nonneg (s : ℝ) : 0 ≤ stepDown s := Real.smoothTransition.nonneg _

private lemma StepCutoff_stepDown_le_one (s : ℝ) : stepDown s ≤ 1 := Real.smoothTransition.le_one _

private lemma StepCutoff_contDiff_stepDown {n : ℕ∞} : ContDiff ℝ n stepDown :=
  (Real.smoothTransition.contDiff (n := n)).comp (contDiff_const.sub contDiff_id)

/-- The two steps are smooth, take values in `[0, 1]`, are constant outside `(1, 2)` and have
derivatives bounded by a constant `C_φ`. -/
theorem step_spec : ∃ Cφ : ℝ, 0 < Cφ ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) stepDown ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) stepUp ∧
    (∀ s, 0 ≤ stepDown s ∧ stepDown s ≤ 1 ∧ 0 ≤ stepUp s ∧ stepUp s ≤ 1) ∧
    (∀ s, s ≤ 1 → stepDown s = 1 ∧ stepUp s = 0) ∧
    (∀ s, 2 ≤ s → stepDown s = 0 ∧ stepUp s = 1) ∧
    ∀ s, |deriv stepDown s| ≤ Cφ ∧ |deriv stepUp s| ≤ Cφ := by
  obtain ⟨M, hM⟩ := StepCutoff_deriv_phi_bound
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨M + 1, by linarith, StepCutoff_contDiff_stepDown, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const)
  · intro s
    exact ⟨StepCutoff_stepDown_nonneg s, StepCutoff_stepDown_le_one s,
      Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro s hs
    exact ⟨StepCutoff_stepDown_of_le hs, Real.smoothTransition.zero_of_nonpos (by linarith)⟩
  · intro s hs
    exact ⟨StepCutoff_stepDown_of_ge hs, Real.smoothTransition.one_of_one_le (by linarith)⟩
  · intro s
    have h1 : deriv stepDown s = -deriv Real.smoothTransition (2 - s) :=
      deriv_comp_const_sub Real.smoothTransition 2 s
    have h2 : deriv stepUp s = deriv Real.smoothTransition (s - 1) :=
      deriv_comp_sub_const Real.smoothTransition 1 s
    rw [h1, h2, abs_neg]
    exact ⟨(hM _).trans (by linarith), (hM _).trans (by linarith)⟩

private lemma StepCutoff_hsSq_nonneg {n : Type*} [Fintype n] (A : Matrix n n ℂ) : 0 ≤ hsSq A := by
  unfold hsSq; positivity

private lemma StepCutoff_hsSq_zero {n : Type*} [Fintype n] : hsSq (0 : Matrix n n ℂ) = 0 := by
  simp [hsSq]

/-- `‖M v‖² ≤ ‖M‖²_HS ‖v‖²` for the Euclidean norm of a vector (Cauchy–Schwarz row by row). -/
private lemma StepCutoff_vecSq_mulVec_le {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) :
    ∑ i, ‖(M.mulVec v) i‖ ^ 2 ≤ hsSq M * ∑ j, ‖v j‖ ^ 2 := by
  unfold hsSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ‖(M.mulVec v) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ * ‖v j‖) ^ 2 := by
        gcongr
        simp only [Matrix.mulVec, dotProduct]
        exact (norm_sum_le _ _).trans (by simp)
    _ ≤ (∑ j, ‖M i j‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- If `X₀` is singular and `X` is invertible, then `1 ≤ ‖X⁻¹‖²_HS ‖X - X₀‖²_HS`: the inverse
norm blows up near every singular matrix. -/
private lemma StepCutoff_one_le {n : Type*} [Fintype n] [DecidableEq n] {X X₀ : Matrix n n ℂ}
    (h₀ : ¬ IsUnit X₀) (hX : IsUnit X) : 1 ≤ hsSq X⁻¹ * hsSq (X - X₀) := by
  have hdet : X₀.det = 0 := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at h₀; exact h₀
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have h1 : v = X⁻¹.mulVec ((X - X₀).mulVec v) := by
    rw [Matrix.sub_mulVec, hv0, sub_zero, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hX), Matrix.one_mulVec]
  have hpos : 0 < ∑ j, ‖v j‖ ^ 2 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    have hj' : 0 < ‖v j‖ ^ 2 := by
      have : v j ≠ 0 := hj
      positivity
    exact lt_of_lt_of_le hj'
      (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j))
  have h2 := StepCutoff_vecSq_mulVec_le X⁻¹ ((X - X₀).mulVec v)
  have h3 := StepCutoff_vecSq_mulVec_le (X - X₀) v
  have h4 : ∑ j, ‖v j‖ ^ 2 ≤ hsSq X⁻¹ * (hsSq (X - X₀) * ∑ j, ‖v j‖ ^ 2) := by
    calc ∑ j, ‖v j‖ ^ 2 = ∑ i, ‖(X⁻¹.mulVec ((X - X₀).mulVec v)) i‖ ^ 2 := by rw [← h1]
      _ ≤ hsSq X⁻¹ * ∑ j, ‖((X - X₀).mulVec v) j‖ ^ 2 := h2
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (StepCutoff_hsSq_nonneg _)
  rw [← mul_assoc] at h4
  exact le_of_mul_le_mul_right (by linarith) hpos

private lemma StepCutoff_contDiff_hsSq {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ∞} :
    ContDiff ℝ m (fun A : Matrix n n ℂ => hsSq A) := by
  unfold hsSq
  refine ContDiff.sum fun a _ => ContDiff.sum fun b _ => ?_
  let e : Matrix n n ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun A => A a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : ContDiff ℝ m (fun A : Matrix n n ℂ => A a b) :=
    (LinearMap.toContinuousLinearMap e).contDiff
  exact (contDiff_norm_sq ℝ).comp he

private lemma StepCutoff_contDiffAt_inv {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ∞}
    {X : Matrix n n ℂ} (hX : IsUnit X) :
    ContDiffAt ℝ m (fun Y : Matrix n n ℂ => Y⁻¹) X := by
  have h := contDiffAt_ringInverse ℝ (n := m) hX.unit
  simp only [IsUnit.unit_spec] at h
  simpa [Matrix.nonsing_inv_eq_ringInverse] using h

private lemma StepCutoff_normCut_inv_eq {n : Type*} [Fintype n] [DecidableEq n] (L : ℝ)
    (X : Matrix n n ℂ) :
    normCut L X⁻¹ = if IsUnit X then stepDown (hsSq X⁻¹ / L) else 0 := by
  simp [normCut, Matrix.isUnit_nonsing_inv_iff]

private lemma StepCutoff_eventuallyEq_zero {n : Type*} [Fintype n] [DecidableEq n] {L : ℝ}
    (hL : 0 < L) {X₀ : Matrix n n ℂ}
    (h : ∀ᶠ X in nhds X₀, IsUnit X → 2 * L < hsSq X⁻¹) :
    (fun X : Matrix n n ℂ => normCut L X⁻¹) =ᶠ[nhds X₀] 0 := by
  filter_upwards [h] with X hX
  rw [StepCutoff_normCut_inv_eq]
  split_ifs with hu
  · exact StepCutoff_stepDown_of_ge ((le_div_iff₀ hL).2 (by linarith [hX hu]))
  · rfl

private lemma StepCutoff_eventually_of_singular {n : Type*} [Fintype n] [DecidableEq n] {L : ℝ}
    (hL : 0 < L) {X₀ : Matrix n n ℂ} (h₀ : ¬ IsUnit X₀) :
    ∀ᶠ X in nhds X₀, IsUnit X → 2 * L < hsSq X⁻¹ := by
  have hg : Continuous fun X : Matrix n n ℂ => hsSq (X - X₀) :=
    (StepCutoff_contDiff_hsSq (m := 0)).continuous.comp (continuous_id.sub continuous_const)
  have h0 : hsSq (X₀ - X₀) < 1 / (2 * L) := by
    rw [sub_self, StepCutoff_hsSq_zero]; positivity
  filter_upwards [hg.continuousAt.eventually (gt_mem_nhds h0)] with X hX hu
  have h1 := StepCutoff_one_le h₀ hu
  by_contra hcon
  push Not at hcon
  have h2 : hsSq (X - X₀) * (2 * L) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hX
  have h3 := StepCutoff_hsSq_nonneg (X - X₀)
  nlinarith

private lemma StepCutoff_eventually_of_unit {n : Type*} [Fintype n] [DecidableEq n] {L : ℝ}
    {X₀ : Matrix n n ℂ} (h₀ : IsUnit X₀) (h : 2 * L < hsSq X₀⁻¹) :
    ∀ᶠ X in nhds X₀, IsUnit X → 2 * L < hsSq X⁻¹ := by
  have hc : ContinuousAt (fun X : Matrix n n ℂ => hsSq X⁻¹) X₀ :=
    ((StepCutoff_contDiff_hsSq (m := 0)).continuous.continuousAt).comp
      (StepCutoff_contDiffAt_inv (m := 0) h₀).continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds h)] with X hX _ using hX

/-- For `L > 0`, `X ↦ normCut L X⁻¹` is smooth on all matrices, its topological support lies in
`{X invertible, ‖X⁻¹‖²_HS ≤ 2 L}`, it equals `1` where `X` is invertible with `‖X⁻¹‖²_HS ≤ L`,
and `normCut L` takes values in `[0, 1]`. -/
theorem normCut_inv_spec {n : Type*} [Fintype n] [DecidableEq n] {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun X : Matrix n n ℂ => normCut L X⁻¹) ∧
    (∀ X ∈ tsupport (fun X : Matrix n n ℂ => normCut L X⁻¹), IsUnit X ∧ hsSq X⁻¹ ≤ 2 * L) ∧
    (∀ X : Matrix n n ℂ, IsUnit X → hsSq X⁻¹ ≤ L → normCut L X⁻¹ = 1) ∧
    ∀ Y : Matrix n n ℂ, 0 ≤ normCut L Y ∧ normCut L Y ≤ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun X₀ => ?_
    by_cases hU : IsUnit X₀
    · have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun X : Matrix n n ℂ => stepDown (hsSq X⁻¹ / L)) X₀ :=
        (StepCutoff_contDiff_stepDown.contDiffAt).comp X₀
          ((StepCutoff_contDiff_hsSq.contDiffAt.comp X₀
            (StepCutoff_contDiffAt_inv hU)).div_const L)
      refine hG.congr_of_eventuallyEq ?_
      filter_upwards [Units.isOpen.mem_nhds hU] with X hX
      simp only [StepCutoff_normCut_inv_eq, hX, ↓reduceIte]
    · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (StepCutoff_eventuallyEq_zero hL (StepCutoff_eventually_of_singular hL hU))
  · intro X hX
    by_contra hcon
    have hev : ∀ᶠ Y in nhds X, IsUnit Y → 2 * L < hsSq Y⁻¹ := by
      by_cases hU : IsUnit X
      · refine StepCutoff_eventually_of_unit hU ?_
        by_contra h2
        exact hcon ⟨hU, not_lt.1 h2⟩
      · exact StepCutoff_eventually_of_singular hL hU
    exact (notMem_tsupport_iff_eventuallyEq.2 (StepCutoff_eventuallyEq_zero hL hev)) hX
  · intro X hX hle
    simp only [StepCutoff_normCut_inv_eq, hX, ↓reduceIte]
    exact StepCutoff_stepDown_of_le ((div_le_one hL).2 hle)
  · intro Y
    unfold normCut
    split_ifs
    · exact ⟨StepCutoff_stepDown_nonneg _, StepCutoff_stepDown_le_one _⟩
    · exact ⟨le_rfl, zero_le_one⟩

end LSBA
