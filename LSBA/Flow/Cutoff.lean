import LSBA.Gauss.Heat

/-!
# Smooth cutoffs for the no-exit lemma

C² ramps from `0` to `1` with slope at most `(1 − ε)⁻¹`, the cutoffs `ψ(x) = (x/J)^{2r} χ(x)` and
`Φ = 1` above `J(1 + β)`, and the off-diagonal rates of the cooperative system for
`(E ψ(X), E Φ(X))`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- A `C²` ramp from `0` to `1` on `[0,1]` with slope at most `(1-ε)⁻¹` and curvature at most
`3/(2ε(1-ε))`. -/
structure IsRamp (ε : ℝ) (ρ : ℝ → ℝ) : Prop where
  eps : 0 < ε ∧ ε ≤ 1 / 2
  smooth : ContDiff ℝ 2 ρ
  zero : ∀ x ≤ 0, ρ x = 0
  one : ∀ x, 1 ≤ x → ρ x = 1
  slope : ∀ x, 0 ≤ deriv ρ x ∧ deriv ρ x ≤ (1 - ε)⁻¹
  curv : ∀ x, |iteratedDeriv 2 ρ x| ≤ 3 / (2 * ε * (1 - ε))

/-- Clamp to `[0,1]`. -/
private def cutoffClamp (t : ℝ) : ℝ := max 0 (min 1 t)

/-- The `C¹` smoothstep `3c² − 2c³` of the clamped argument. -/
private def cutoffStep (t : ℝ) : ℝ := 3 * cutoffClamp t ^ 2 - 2 * cutoffClamp t ^ 3

/-- The derivative `6c(1 − c)` of the smoothstep. -/
private def cutoffStep' (t : ℝ) : ℝ := 6 * cutoffClamp t * (1 - cutoffClamp t)

/-- The antiderivative of the smoothstep. -/
private def cutoffStepInt (t : ℝ) : ℝ :=
  cutoffClamp t ^ 3 - cutoffClamp t ^ 4 / 2 + max (t - 1) 0

private theorem cutoffClamp_of_nonpos {t : ℝ} (h : t ≤ 0) : cutoffClamp t = 0 := by
  unfold cutoffClamp
  rw [min_eq_right (by linarith)]
  exact max_eq_left h

private theorem cutoffClamp_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : cutoffClamp t = t := by
  unfold cutoffClamp
  rw [min_eq_right h1]
  exact max_eq_right h0

private theorem cutoffClamp_of_one_le {t : ℝ} (h : 1 ≤ t) : cutoffClamp t = 1 := by
  unfold cutoffClamp
  rw [min_eq_left h]
  exact max_eq_right zero_le_one

private theorem cutoffClamp_mem (t : ℝ) : 0 ≤ cutoffClamp t ∧ cutoffClamp t ≤ 1 := by
  refine ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private theorem continuous_cutoffClamp : Continuous cutoffClamp :=
  continuous_const.max (continuous_const.min continuous_id)

/-- A function equal to three smooth pieces on `(-∞,0]`, `[0,1]`, `[1,∞)`, with a derivative
function `d` that agrees with the piece derivatives, has derivative `d` everywhere. -/
private theorem cutoff_hasDerivAt_glue {f A B C d dA dB dC : ℝ → ℝ}
    (hA : ∀ x, HasDerivAt A (dA x) x) (hB : ∀ x, HasDerivAt B (dB x) x)
    (hC : ∀ x, HasDerivAt C (dC x) x)
    (fA : ∀ x ≤ 0, f x = A x) (fB : ∀ x, 0 ≤ x → x ≤ 1 → f x = B x)
    (fC : ∀ x, 1 ≤ x → f x = C x)
    (eA : ∀ x ≤ 0, d x = dA x) (eB : ∀ x, 0 ≤ x → x ≤ 1 → d x = dB x)
    (eC : ∀ x, 1 ≤ x → d x = dC x) (t : ℝ) : HasDerivAt f (d t) t := by
  -- one-sided glue at a point `a` between two pieces
  have glue : ∀ {g₁ g₂ : ℝ → ℝ} {a lo hi e : ℝ}, lo < a → a < hi →
      (∀ x ∈ Set.Icc lo a, f x = g₁ x) → (∀ x ∈ Set.Icc a hi, f x = g₂ x) →
      HasDerivAt g₁ e a → HasDerivAt g₂ e a → HasDerivAt f e a := by
    intro g₁ g₂ a lo hi e hlo hhi e₁ e₂ d₁ d₂
    have L : HasDerivWithinAt f e (Set.Iic a) a :=
      ((d₁.hasDerivWithinAt (s := Set.Icc lo a)).congr e₁
        (e₁ a ⟨hlo.le, le_rfl⟩)).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hlo)
    have R : HasDerivWithinAt f e (Set.Ici a) a :=
      ((d₂.hasDerivWithinAt (s := Set.Icc a hi)).congr e₂
        (e₂ a ⟨le_rfl, hhi.le⟩)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hhi)
    have := L.union R
    rw [Set.Iic_union_Ici] at this
    exact hasDerivWithinAt_univ.mp this
  rcases lt_trichotomy t 0 with h0 | h0 | h0
  · refine glue (g₁ := A) (g₂ := A) (lo := t - 1) (hi := 0) (by linarith) h0
      (fun x hx => fA x (by linarith [hx.2])) (fun x hx => fA x hx.2) ?_ ?_
    · rw [eA t h0.le]; exact hA t
    · rw [eA t h0.le]; exact hA t
  · subst h0
    refine glue (g₁ := A) (g₂ := B) (lo := -1) (hi := 1) (by norm_num) (by norm_num)
      (fun x hx => fA x hx.2) (fun x hx => fB x hx.1 hx.2) ?_ ?_
    · rw [eA 0 le_rfl]; exact hA 0
    · rw [eB 0 le_rfl zero_le_one]; exact hB 0
  · rcases lt_trichotomy t 1 with h1 | h1 | h1
    · refine glue (g₁ := B) (g₂ := B) (lo := 0) (hi := 1) h0 h1
        (fun x hx => fB x hx.1 (by linarith [hx.2]))
        (fun x hx => fB x (by linarith [hx.1]) hx.2) ?_ ?_
      · rw [eB t h0.le h1.le]; exact hB t
      · rw [eB t h0.le h1.le]; exact hB t
    · subst h1
      refine glue (g₁ := B) (g₂ := C) (lo := 0) (hi := 2) (by norm_num) (by norm_num)
        (fun x hx => fB x hx.1 hx.2) (fun x hx => fC x hx.1) ?_ ?_
      · rw [eB 1 zero_le_one le_rfl]; exact hB 1
      · rw [eC 1 le_rfl]; exact hC 1
    · refine glue (g₁ := C) (g₂ := C) (lo := 1) (hi := t + 1) h1 (by linarith)
        (fun x hx => fC x hx.1) (fun x hx => fC x (by linarith [hx.1])) ?_ ?_
      · rw [eC t h1.le]; exact hC t
      · rw [eC t h1.le]; exact hC t

private theorem hasDerivAt_cutoffStep (t : ℝ) : HasDerivAt cutoffStep (cutoffStep' t) t := by
  refine cutoff_hasDerivAt_glue (A := fun _ => 0) (B := fun x => 3 * x ^ 2 - 2 * x ^ 3)
    (C := fun _ => 1) (dA := fun _ => 0) (dB := fun x => 6 * x - 6 * x ^ 2) (dC := fun _ => 0)
    (fun x => hasDerivAt_const x 0) (fun x => ?_) (fun x => hasDerivAt_const x 1)
    (fun x hx => ?_) (fun x h0 h1 => ?_) (fun x hx => ?_) (fun x hx => ?_)
    (fun x h0 h1 => ?_) (fun x hx => ?_) t
  · exact (((hasDerivAt_pow 2 x).const_mul 3).sub ((hasDerivAt_pow 3 x).const_mul 2)).congr_deriv
      (by simp; ring)
  · simp [cutoffStep, cutoffClamp_of_nonpos hx]
  · simp [cutoffStep, cutoffClamp_of_mem h0 h1]
  · simp [cutoffStep, cutoffClamp_of_one_le hx]; norm_num
  · simp [cutoffStep', cutoffClamp_of_nonpos hx]
  · simp [cutoffStep', cutoffClamp_of_mem h0 h1]; ring
  · simp [cutoffStep', cutoffClamp_of_one_le hx]

private theorem hasDerivAt_cutoffStepInt (t : ℝ) : HasDerivAt cutoffStepInt (cutoffStep t) t := by
  refine cutoff_hasDerivAt_glue (A := fun _ => 0) (B := fun x => x ^ 3 - x ^ 4 / 2)
    (C := fun x => x - 1 / 2) (dA := fun _ => 0) (dB := fun x => 3 * x ^ 2 - 2 * x ^ 3)
    (dC := fun _ => 1) (fun x => hasDerivAt_const x 0) (fun x => ?_)
    (fun x => (hasDerivAt_id x).sub_const (1 / 2))
    (fun x hx => ?_) (fun x h0 h1 => ?_) (fun x hx => ?_) (fun x hx => ?_)
    (fun x h0 h1 => ?_) (fun x hx => ?_) t
  · exact (((hasDerivAt_pow 3 x)).sub ((hasDerivAt_pow 4 x).div_const 2)).congr_deriv
      (by simp; ring)
  · simp [cutoffStepInt, cutoffClamp_of_nonpos hx, max_eq_right (by linarith : x - 1 ≤ 0)]
  · simp [cutoffStepInt, cutoffClamp_of_mem h0 h1, max_eq_right (by linarith : x - 1 ≤ 0)]
  · simp [cutoffStepInt, cutoffClamp_of_one_le hx, max_eq_left (by linarith : 0 ≤ x - 1)]
  · simp [cutoffStep, cutoffClamp_of_nonpos hx]
  · simp [cutoffStep, cutoffClamp_of_mem h0 h1]
  · simp [cutoffStep, cutoffClamp_of_one_le hx]; norm_num

private theorem cutoffStepInt_of_nonpos {t : ℝ} (h : t ≤ 0) : cutoffStepInt t = 0 := by
  simp [cutoffStepInt, cutoffClamp_of_nonpos h, max_eq_right (by linarith : t - 1 ≤ 0)]

private theorem cutoffStepInt_of_one_le {t : ℝ} (h : 1 ≤ t) : cutoffStepInt t = t - 1 / 2 := by
  simp [cutoffStepInt, cutoffClamp_of_one_le h, max_eq_left (by linarith : 0 ≤ t - 1)]

private theorem cutoffStep_mem (t : ℝ) : 0 ≤ cutoffStep t ∧ cutoffStep t ≤ 1 := by
  obtain ⟨h0, h1⟩ := cutoffClamp_mem t
  unfold cutoffStep
  constructor <;> nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.2 h1),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1)) h0, sq_nonneg (1 - cutoffClamp t)]

private theorem cutoffStep'_mem (t : ℝ) : 0 ≤ cutoffStep' t ∧ cutoffStep' t ≤ 3 / 2 := by
  obtain ⟨h0, h1⟩ := cutoffClamp_mem t
  unfold cutoffStep'
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) h0) (sub_nonneg.2 h1)
  · nlinarith [sq_nonneg (cutoffClamp t - 1 / 2)]

private theorem continuous_cutoffStep' : Continuous cutoffStep' := by
  unfold cutoffStep'
  have := continuous_cutoffClamp
  fun_prop

private theorem cutoffStep_mono : Monotone cutoffStep := by
  refine monotone_of_deriv_nonneg (fun t => (hasDerivAt_cutoffStep t).differentiableAt) fun t => ?_
  rw [(hasDerivAt_cutoffStep t).deriv]
  exact (cutoffStep'_mem t).1

/-- Chain rule for an affine inner map `x ↦ (x - c) / d`. -/
private theorem cutoff_hasDerivAt_affine {F F' : ℝ → ℝ} (hF : ∀ t, HasDerivAt F (F' t) t)
    (c d x : ℝ) : HasDerivAt (fun x => F ((x - c) / d)) (F' ((x - c) / d) / d) x := by
  have h : HasDerivAt (fun x : ℝ => (x - c) / d) (1 / d) x :=
    ((hasDerivAt_id' x).sub_const c).div_const d
  exact ((hF _).comp x h).congr_deriv (by ring)

/-- The explicit ramp: a difference of two shifted copies of the antiderivative of the smoothstep,
scaled by `ε`. -/
private def cutoffRamp (ε x : ℝ) : ℝ :=
  ε / (1 - ε) * (cutoffStepInt (x / ε) - cutoffStepInt ((x - (1 - ε)) / ε))

private theorem hasDerivAt_cutoffRamp {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (cutoffRamp ε)
      ((1 - ε)⁻¹ * (cutoffStep (x / ε) - cutoffStep ((x - (1 - ε)) / ε))) x := by
  have h1 := cutoff_hasDerivAt_affine hasDerivAt_cutoffStepInt 0 ε x
  have h2 := cutoff_hasDerivAt_affine hasDerivAt_cutoffStepInt (1 - ε) ε x
  simp only [sub_zero] at h1
  refine ((h1.sub h2).const_mul (ε / (1 - ε))).congr_deriv ?_
  field_simp

/-- The second iterated derivative is the derivative of the derivative. -/
private theorem cutoff_iteratedDeriv_two (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

private theorem deriv_cutoffRamp {ε : ℝ} (hε : 0 < ε) :
    deriv (cutoffRamp ε) =
      fun x => (1 - ε)⁻¹ * (cutoffStep (x / ε) - cutoffStep ((x - (1 - ε)) / ε)) :=
  funext fun x => (hasDerivAt_cutoffRamp hε x).deriv

private theorem hasDerivAt_deriv_cutoffRamp {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (deriv (cutoffRamp ε))
      ((1 - ε)⁻¹ * (cutoffStep' (x / ε) / ε - cutoffStep' ((x - (1 - ε)) / ε) / ε)) x := by
  rw [deriv_cutoffRamp hε]
  have h1 := cutoff_hasDerivAt_affine hasDerivAt_cutoffStep 0 ε x
  have h2 := cutoff_hasDerivAt_affine hasDerivAt_cutoffStep (1 - ε) ε x
  simp only [sub_zero] at h1
  exact (h1.sub h2).const_mul (1 - ε)⁻¹

private theorem iteratedDeriv_two_cutoffRamp {ε : ℝ} (hε : 0 < ε) :
    iteratedDeriv 2 (cutoffRamp ε) =
      fun x => (1 - ε)⁻¹ * (cutoffStep' (x / ε) / ε - cutoffStep' ((x - (1 - ε)) / ε) / ε) := by
  rw [cutoff_iteratedDeriv_two]
  exact funext fun x => (hasDerivAt_deriv_cutoffRamp hε x).deriv

private theorem contDiff_cutoffRamp {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 2 (cutoffRamp ε) := by
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h2, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_cutoffRamp hε x).differentiableAt, fun h => absurd h (by simp), ?_⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hasDerivAt_deriv_cutoffRamp hε x).differentiableAt, ?_⟩
  have : deriv (deriv (cutoffRamp ε)) =
      fun x => (1 - ε)⁻¹ * (cutoffStep' (x / ε) / ε - cutoffStep' ((x - (1 - ε)) / ε) / ε) :=
    funext fun x => (hasDerivAt_deriv_cutoffRamp hε x).deriv
  rw [this]
  have := continuous_cutoffStep'
  fun_prop

theorem exists_isRamp (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) : ∃ ρ, IsRamp ε ρ := by
  have hε1 : 0 < 1 - ε := by linarith
  refine ⟨cutoffRamp ε, ⟨h0, h1⟩, contDiff_cutoffRamp h0, fun x hx => ?_, fun x hx => ?_,
    fun x => ?_, fun x => ?_⟩
  · have ha : x / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx h0.le
    have hb : (x - (1 - ε)) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) h0.le
    simp [cutoffRamp, cutoffStepInt_of_nonpos ha, cutoffStepInt_of_nonpos hb]
  · have ha : 1 ≤ x / ε := (le_div_iff₀ h0).2 (by linarith)
    have hb : 1 ≤ (x - (1 - ε)) / ε := (le_div_iff₀ h0).2 (by linarith)
    simp only [cutoffRamp, cutoffStepInt_of_one_le ha, cutoffStepInt_of_one_le hb]
    field_simp
    ring
  · rw [deriv_cutoffRamp h0]
    have hab : (x - (1 - ε)) / ε ≤ x / ε := div_le_div_of_nonneg_right (by linarith) h0.le
    have h1 := cutoffStep_mono hab
    have h2 := cutoffStep_mem (x / ε)
    have h3 := cutoffStep_mem ((x - (1 - ε)) / ε)
    have hinv : 0 ≤ (1 - ε)⁻¹ := inv_nonneg.2 hε1.le
    refine ⟨mul_nonneg hinv (by linarith), ?_⟩
    exact mul_le_of_le_one_right hinv (by linarith [h2.2, h3.1])
  · rw [iteratedDeriv_two_cutoffRamp h0]
    have h2 := cutoffStep'_mem (x / ε)
    have h3 := cutoffStep'_mem ((x - (1 - ε)) / ε)
    have hinv : 0 ≤ (1 - ε)⁻¹ := inv_nonneg.2 hε1.le
    rw [abs_mul, abs_of_nonneg hinv]
    have hq : |cutoffStep' (x / ε) / ε - cutoffStep' ((x - (1 - ε)) / ε) / ε| ≤ 3 / 2 / ε := by
      rw [← sub_div]
      rw [abs_div, abs_of_pos h0]
      exact div_le_div_of_nonneg_right (abs_le.2 ⟨by linarith, by linarith⟩) h0.le
    calc (1 - ε)⁻¹ * |cutoffStep' (x / ε) / ε - cutoffStep' ((x - (1 - ε)) / ε) / ε|
        ≤ (1 - ε)⁻¹ * (3 / 2 / ε) := mul_le_mul_of_nonneg_left hq hinv
      _ = 3 / (2 * ε * (1 - ε)) := by field_simp

/-- `ψ(x) = (x/J)^{2r} χ(x)`, `χ = 1` on `[0, J(1+β)]`, `0` beyond `J(1+2β)` (the factor
`ρ(x+1)` makes `ψ` bounded on `x < 0` and equals `1` on `x ≥ 0`). -/
def cutPsi (ρ : ℝ → ℝ) (J β : ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  (x / J) ^ (2 * r) * (1 - ρ ((x - J * (1 + β)) / (β * J))) * ρ (x + 1)

/-- `Φ = 0` on `(-∞, J]`, `1` on `[J(1+β), ∞)`. -/
def cutPhi (ρ : ℝ → ℝ) (J β : ℝ) (x : ℝ) : ℝ := ρ ((x - J) / (β * J))

section RampFacts

variable {ε : ℝ} {ρ : ℝ → ℝ}

private theorem IsRamp.hasDerivAt (hρ : IsRamp ε ρ) (y : ℝ) : HasDerivAt ρ (deriv ρ y) y :=
  ((hρ.smooth.differentiable (by norm_num)) y).hasDerivAt

private theorem IsRamp.contDiff_deriv (hρ : IsRamp ε ρ) : ContDiff ℝ 1 (deriv ρ) := by
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  have h : ContDiff ℝ (1 + 1) ρ := by rw [← h2]; exact hρ.smooth
  exact (contDiff_succ_iff_deriv.1 h).2.2

private theorem IsRamp.hasDerivAt_deriv (hρ : IsRamp ε ρ) (y : ℝ) :
    HasDerivAt (deriv ρ) (iteratedDeriv 2 ρ y) y := by
  rw [cutoff_iteratedDeriv_two]
  exact ((hρ.contDiff_deriv.differentiable (by norm_num)) y).hasDerivAt

private theorem IsRamp.mono (hρ : IsRamp ε ρ) : Monotone ρ :=
  monotone_of_deriv_nonneg (hρ.smooth.differentiable (by norm_num)) fun x => (hρ.slope x).1

private theorem IsRamp.mem (hρ : IsRamp ε ρ) (x : ℝ) : 0 ≤ ρ x ∧ ρ x ≤ 1 := by
  constructor
  · rcases le_or_gt x 0 with h | h
    · rw [hρ.zero x h]
    · rw [← hρ.zero 0 le_rfl]; exact hρ.mono h.le
  · rcases le_or_gt 1 x with h | h
    · rw [hρ.one x h]
    · rw [← hρ.one 1 le_rfl]; exact hρ.mono h.le

end RampFacts

section CutDerivs

variable {ε : ℝ} {ρ : ℝ → ℝ}

private theorem cutPhi_hasDerivAt (hρ : IsRamp ε ρ) (J β x : ℝ) :
    HasDerivAt (cutPhi ρ J β) (deriv ρ ((x - J) / (β * J)) / (β * J)) x :=
  cutoff_hasDerivAt_affine hρ.hasDerivAt J (β * J) x

private theorem deriv_cutPhi (hρ : IsRamp ε ρ) (J β : ℝ) :
    deriv (cutPhi ρ J β) = fun x => deriv ρ ((x - J) / (β * J)) / (β * J) :=
  funext fun x => (cutPhi_hasDerivAt hρ J β x).deriv

private theorem cutPhi_hasDerivAt_deriv (hρ : IsRamp ε ρ) (J β x : ℝ) :
    HasDerivAt (deriv (cutPhi ρ J β))
      (iteratedDeriv 2 ρ ((x - J) / (β * J)) / (β * J) / (β * J)) x := by
  rw [deriv_cutPhi hρ]
  exact (cutoff_hasDerivAt_affine hρ.hasDerivAt_deriv J (β * J) x).div_const (β * J)

private theorem iteratedDeriv_two_cutPhi (hρ : IsRamp ε ρ) (J β x : ℝ) :
    iteratedDeriv 2 (cutPhi ρ J β) x =
      iteratedDeriv 2 ρ ((x - J) / (β * J)) / (β * J) / (β * J) := by
  rw [cutoff_iteratedDeriv_two]
  exact (cutPhi_hasDerivAt_deriv hρ J β x).deriv

private theorem contDiff_cutPhi (hρ : IsRamp ε ρ) (J β : ℝ) : ContDiff ℝ 2 (cutPhi ρ J β) :=
  hρ.smooth.comp ((contDiff_id.sub contDiff_const).div_const _)

private theorem contDiff_cutPsi (hρ : IsRamp ε ρ) (J β : ℝ) (r : ℕ) :
    ContDiff ℝ 2 (cutPsi ρ J β r) :=
  (((contDiff_id.div_const J).pow _).mul
    (contDiff_const.sub (hρ.smooth.comp ((contDiff_id.sub contDiff_const).div_const _)))).mul
    (hρ.smooth.comp (contDiff_id.add contDiff_const))

end CutDerivs

theorem cutPsi_C2b {ε : ℝ} {ρ : ℝ → ℝ} (hρ : IsRamp ε ρ) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (r : ℕ) : C2b (cutPsi ρ J β r) := by
  refine ⟨contDiff_cutPsi hρ J β r, ?_⟩
  have hcs : HasCompactSupport (cutPsi ρ J β r) := by
    refine HasCompactSupport.intro (K := Set.Icc (-1) (J * (1 + 2 * β))) isCompact_Icc
      fun x hx => ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have : ρ (x + 1) = 0 := hρ.zero _ (by linarith)
      simp [cutPsi, this]
    · have hβJ : 0 < β * J := mul_pos hβ hJ
      have : ρ ((x - J * (1 + β)) / (β * J)) = 1 :=
        hρ.one _ ((le_div_iff₀ hβJ).2 (by nlinarith))
      simp [cutPsi, this]
  have c0 := (contDiff_cutPsi hρ J β r).continuous
  have c1 : Continuous (deriv (cutPsi ρ J β r)) :=
    (contDiff_cutPsi hρ J β r).continuous_deriv (by norm_num)
  have c2 : Continuous (iteratedDeriv 2 (cutPsi ρ J β r)) :=
    (contDiff_cutPsi hρ J β r).continuous_iteratedDeriv 2 (by norm_num)
  have s1 : HasCompactSupport (deriv (cutPsi ρ J β r)) := hcs.deriv
  have s2 : HasCompactSupport (iteratedDeriv 2 (cutPsi ρ J β r)) := by
    rw [cutoff_iteratedDeriv_two]; exact hcs.deriv.deriv
  obtain ⟨C0, h0⟩ := hcs.exists_bound_of_continuous c0
  obtain ⟨C1, h1⟩ := s1.exists_bound_of_continuous c1
  obtain ⟨C2, h2⟩ := s2.exists_bound_of_continuous c2
  refine ⟨max C0 (max C1 C2), fun x => ⟨?_, ?_, ?_⟩⟩
  · exact (Real.norm_eq_abs _ ▸ h0 x).trans (le_max_left _ _)
  · exact (Real.norm_eq_abs _ ▸ h1 x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (Real.norm_eq_abs _ ▸ h2 x).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem cutPhi_C2b {ε : ℝ} {ρ : ℝ → ℝ} (hρ : IsRamp ε ρ) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    C2b (cutPhi ρ J β) := by
  have hm : 0 < β * J := mul_pos hβ hJ
  have hinv : 0 ≤ (1 - ε)⁻¹ := (hρ.slope 0).1.trans (hρ.slope 0).2
  have hcurv : 0 ≤ 3 / (2 * ε * (1 - ε)) := le_trans (abs_nonneg _) (hρ.curv 0)
  have hA : 0 ≤ (1 - ε)⁻¹ / (β * J) := div_nonneg hinv hm.le
  have hB : 0 ≤ 3 / (2 * ε * (1 - ε)) / (β * J) / (β * J) :=
    div_nonneg (div_nonneg hcurv hm.le) hm.le
  refine ⟨contDiff_cutPhi hρ J β, 1 + (1 - ε)⁻¹ / (β * J) +
    3 / (2 * ε * (1 - ε)) / (β * J) / (β * J), fun x => ⟨?_, ?_, ?_⟩⟩
  · have := hρ.mem ((x - J) / (β * J))
    change |ρ ((x - J) / (β * J))| ≤ _
    rw [abs_of_nonneg this.1]
    linarith [this.2]
  · rw [deriv_cutPhi hρ]
    have h := hρ.slope ((x - J) / (β * J))
    rw [abs_of_nonneg (div_nonneg h.1 hm.le)]
    have := div_le_div_of_nonneg_right h.2 hm.le
    linarith
  · rw [iteratedDeriv_two_cutPhi hρ, abs_div, abs_div, abs_of_pos hm]
    have := div_le_div_of_nonneg_right (hρ.curv ((x - J) / (β * J))) hm.le
    have := div_le_div_of_nonneg_right this hm.le
    linarith

theorem cutPhi_props {ε : ℝ} {ρ : ℝ → ℝ} (hρ : IsRamp ε ρ) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (r : ℕ) (x : ℝ) :
    0 ≤ cutPhi ρ J β x ∧ cutPhi ρ J β x ≤ 1 ∧ (J * (1 + β) ≤ x → cutPhi ρ J β x = 1) ∧
      0 ≤ cutPsi ρ J β r x := by
  have hm : 0 < β * J := mul_pos hβ hJ
  refine ⟨(hρ.mem _).1, (hρ.mem _).2, fun h => hρ.one _ ((le_div_iff₀ hm).2 (by nlinarith)), ?_⟩
  unfold cutPsi
  have h1 := hρ.mem ((x - J * (1 + β)) / (β * J))
  have h2 := hρ.mem (x + 1)
  have h3 : 0 ≤ (x / J) ^ (2 * r) := (even_two_mul r).pow_nonneg _
  exact mul_nonneg (mul_nonneg h3 (by linarith [h1.2])) h2.1

/-- Off-diagonal rate `a₁₂` of the cutoff system. -/
def rateA12 (ε β κ : ℝ) (r : ℕ) : ℝ := (1 + 2 * β) ^ (2 * r + 1) * (1 - ε)⁻¹ * κ / β

/-- Off-diagonal rate `a₂₁` of the cutoff system. -/
def rateA21 (ε β κ : ℝ) : ℝ := (1 + β) * (1 - ε)⁻¹ * κ / β

section Rates

variable {ε : ℝ} {ρ : ℝ → ℝ}

end Rates

end LSBA
