import LSBA.Volume.LowerVolume
import LSBA.Spectral.ResolventBounds

/-!
# Moment tools for the completion of the resolvent moment bounds

The terminal height `η_L = W^ν/ℓ_{W,g,L}` of (2.9) [eq:bounded-lower-moment] and (2.11)
[uvu:eq:local-moments], the bounds `0 ≤ Im G_xx(E + iη) ≤ 1/η` and their comparison between
heights, continuity of `Im G_xx` in the sample for the model (1.3) [eq:model], and the splitting
of a moment
of a nonnegative variable into a good event and an exceptional event of small probability (the
last steps of the proofs of Theorems 2.3 [thm:bounded-lower] and 2.5 [uvu:thm:terminal] in Section
5.5 [sec:fo-completion]).
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The terminal height `η_L = W^ν / ℓ_{W,g,L}` of (2.9) [eq:bounded-lower-moment] and (2.11)
[uvu:eq:local-moments]. -/
def etaL (W L : ℕ) (g ν : ℝ) : ℝ := (W : ℝ) ^ ν / ellStar W L g

/-- `0 ≤ Im G_xx(E + iη) ≤ 1/η` for a Hermitian matrix and `η > 0`. -/
theorem im_resolvent_bounds {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (E : ℝ) {η : ℝ} (hη : 0 < η) (x : n) :
    0 ≤ (resolventMat A (E + η * Complex.I) x x).im ∧
      (resolventMat A (E + η * Complex.I) x x).im ≤ 1 / η := by
  have h0 : 0 ≤ (resolventMat A (E + η * Complex.I) x x).im := by
    rw [im_resolventMat_diag hA E hη.ne' x]
    exact Finset.sum_nonneg fun k _ => by positivity
  refine ⟨h0, ?_⟩
  set y := (resolventMat A (E + η * Complex.I) x x).im with hy
  have hw := ward hA E hη.ne' x
  have h1 : y ^ 2 ≤ ‖resolventMat A (E + η * Complex.I) x x‖ ^ 2 :=
    pow_le_pow_left₀ h0 (Complex.abs_im_le_norm _ |>.trans' (le_abs_self _)) 2
  have h2 : ‖resolventMat A (E + η * Complex.I) x x‖ ^ 2 ≤
      ∑ y', ‖resolventMat A (E + η * Complex.I) x y'‖ ^ 2 :=
    Finset.single_le_sum (f := fun y' => ‖resolventMat A (E + η * Complex.I) x y'‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ x)
  rw [hw, ← hy] at h2
  have h3 : η * y ^ 2 ≤ y := by
    have := mul_le_mul_of_nonneg_left (h1.trans h2) hη.le
    rwa [mul_div_cancel₀ _ hη.ne'] at this
  rw [le_div_iff₀ hη]
  nlinarith

/-- One spectral term of `Im G_xx(E + iη)`, `η w/(s + η²)` with `s ≥ 0` and weight `w ≥ 0`, at the
heights `a` and `b`. -/
private lemma moments_term_le {s a b w : ℝ} (hs : 0 ≤ s) (ha : 0 < a) (hb : 0 < b)
    (hw : 0 ≤ w) :
    a * w / (s + a ^ 2) ≤ max (a / b) (b / a) * (b * w / (s + b ^ 2)) := by
  have hden1 : 0 < s + a ^ 2 := by positivity
  have hden2 : 0 < s + b ^ 2 := by positivity
  have hnn : 0 ≤ b * w / (s + b ^ 2) := by positivity
  rcases le_total a b with hab | hab
  · calc a * w / (s + a ^ 2) ≤ (b / a) * (b * w / (s + b ^ 2)) := by
          rw [div_mul_div_comm, div_le_div_iff₀ hden1 (by positivity)]
          nlinarith [mul_nonneg (mul_nonneg hw hs) (sub_nonneg.2 (pow_le_pow_left₀ ha.le hab 2))]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hnn
  · calc a * w / (s + a ^ 2) ≤ (a / b) * (b * w / (s + b ^ 2)) := by
          rw [div_mul_div_comm, div_le_div_iff₀ hden1 (by positivity)]
          nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ha.le hb.le) hw)
            (sub_nonneg.2 (pow_le_pow_left₀ hb.le hab 2))]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hnn

/-- Comparison of Poisson kernels at two heights:
`Im G_xx(E + iη₁) ≤ max{η₁/η₂, η₂/η₁} Im G_xx(E + iη₂)` for a Hermitian matrix (proof of
Theorem 2.5 [uvu:thm:terminal]). -/
theorem im_resolvent_height_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (E : ℝ) {η₁ η₂ : ℝ} (h₁ : 0 < η₁) (h₂ : 0 < η₂) (x : n) :
    (resolventMat A (E + η₁ * Complex.I) x x).im ≤
      max (η₁ / η₂) (η₂ / η₁) * (resolventMat A (E + η₂ * Complex.I) x x).im := by
  rw [im_resolventMat_diag hA E h₁.ne' x, im_resolventMat_diag hA E h₂.ne' x, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => moments_term_le (sq_nonneg _) h₁ h₂ (by positivity)

/-- The model (1.3) [eq:model] depends continuously on the sample. -/
private lemma moments_continuous_Hmat (g : ℝ) (W L : ℕ) : Continuous (Hmat g W L) := by
  refine continuous_matrix fun p q => ?_
  simp only [Hmat, Hdet, gueBlock, blockDiagOp, Matrix.smul_apply, Matrix.add_apply,
    Matrix.of_apply, smul_eq_mul]
  split_ifs <;> fun_prop

/-- `(ω, E) ↦ Im G_xx(E + iη)` is continuous for `η ≠ 0`. -/
private lemma moments_continuous_im (g : ℝ) (W L : ℕ) {η : ℝ} (hη : η ≠ 0)
    (x : Fin L × Fin W) :
    Continuous fun q : Ω W L × ℝ =>
      (resolventMat (Hmat g W L q.1) (q.2 + η * Complex.I) x x).im := by
  have hdet : ∀ q : Ω W L × ℝ, (Hmat g W L q.1 - ((q.2 : ℂ) + η * Complex.I) •
      (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)).det ≠ 0 :=
    fun q => Matrix.det_ne_zero_of_right_inverse
      (sub_smul_mul_resolventMat (Hmat_isHermitian g W L q.1) (by simpa using hη))
  have hM : Continuous fun q : Ω W L × ℝ => Hmat g W L q.1 - ((q.2 : ℂ) + η * Complex.I) •
      (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :=
    ((moments_continuous_Hmat g W L).comp continuous_fst).sub
      (((Complex.continuous_ofReal.comp continuous_snd).add continuous_const).smul
        continuous_const)
  simp only [resolventMat, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact Complex.continuous_im.comp
    ((hM.matrix_det.inv₀ hdet).mul (hM.matrix_adjugate.matrix_elem x x))

/-- `ω ↦ Im G_xx(E + iη)` is continuous for the model (1.3) [eq:model] and `η ≠ 0`. -/
theorem continuous_im_resolvent_Hmat (g : ℝ) (W L : ℕ) (E : ℝ) {η : ℝ} (hη : η ≠ 0)
    (x : Fin L × Fin W) :
    Continuous fun ω : Ω W L => (resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im := by
  have hc : Continuous fun ω : Ω W L => (ω, E) := continuous_id.prodMk continuous_const
  have h := (moments_continuous_im g W L hη x).comp hc
  simpa only [Function.comp_def] using h

/-- Moments from a good event: if `0 ≤ Y ≤ Z`, `Y ≤ K₀` off a set of probability at most `δ`, and
`E Z^{2p} ≤ C_s`, then `E Y^p ≤ K₀^p + C_s^{1/2} δ^{1/2}` (Cauchy–Schwarz on the exceptional event,
as in the proof of Theorem 2.5 [uvu:thm:terminal]). -/
theorem moment_good_bad {X : Type*} [MeasurableSpace X] {P : Measure X} [IsProbabilityMeasure P]
    {Y Z : X → ℝ} (hY : Measurable Y) (hY0 : ∀ x, 0 ≤ Y x) (hYZ : ∀ x, Y x ≤ Z x)
    {p K₀ Cs δ : ℝ} (hp : 0 < p) (hK₀ : 0 ≤ K₀)
    (hZi : Integrable (fun x => Z x ^ (2 * p)) P) (hZ : ∫ x, Z x ^ (2 * p) ∂P ≤ Cs)
    (S : Set X) (hS : P S ≤ ENNReal.ofReal δ) (hgood : ∀ x ∉ S, Y x ≤ K₀) :
    Integrable (fun x => Y x ^ p) P ∧
      ∫ x, Y x ^ p ∂P ≤ K₀ ^ p + Real.sqrt Cs * Real.sqrt δ := by
  set S' : Set X := {x | K₀ < Y x} with hS'def
  have hS'meas : MeasurableSet S' := measurableSet_lt measurable_const hY
  have hS'S : S' ⊆ S := fun x hx => by
    by_contra hxS
    exact absurd (hgood x hxS) (not_le.2 hx)
  have hPS' : P S' ≤ ENNReal.ofReal δ := (measure_mono hS'S).trans hS
  have h2p : 0 < 2 * p := by positivity
  have hY2m : Measurable fun x => Y x ^ (2 * p) := hY.pow_const _
  have hYpm : Measurable fun x => Y x ^ p := hY.pow_const _
  have hY2le : ∀ x, Y x ^ (2 * p) ≤ Z x ^ (2 * p) := fun x =>
    Real.rpow_le_rpow (hY0 x) (hYZ x) h2p.le
  have hY2nn : ∀ x, 0 ≤ Y x ^ (2 * p) := fun x => Real.rpow_nonneg (hY0 x) _
  have hYpnn : ∀ x, 0 ≤ Y x ^ p := fun x => Real.rpow_nonneg (hY0 x) _
  have hY2i : Integrable (fun x => Y x ^ (2 * p)) P :=
    hZi.mono' hY2m.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (hY2nn x)]; exact hY2le x)
  have hY2int : ∫ x, Y x ^ (2 * p) ∂P ≤ Cs := (integral_mono hY2i hZi hY2le).trans hZ
  have hCs : 0 ≤ Cs := (integral_nonneg hY2nn).trans hY2int
  have hYpi : Integrable (fun x => Y x ^ p) P := by
    refine ((integrable_const (1 : ℝ)).add hY2i).mono' hYpm.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (hYpnn x)]
    simp only [Pi.add_apply]
    rcases le_total 1 (Y x) with h | h
    · have : Y x ^ p ≤ Y x ^ (2 * p) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
      linarith
    · have : Y x ^ p ≤ 1 := Real.rpow_le_one (hY0 x) h hp.le
      linarith [hY2nn x]
  refine ⟨hYpi, ?_⟩
  have hind : Integrable (S'.indicator fun x => Y x ^ p) P := hYpi.indicator hS'meas
  have hpt : ∀ x, Y x ^ p ≤ K₀ ^ p + S'.indicator (fun x => Y x ^ p) x := by
    intro x
    by_cases hx : x ∈ S'
    · rw [Set.indicator_of_mem hx]; linarith [Real.rpow_nonneg hK₀ p]
    · rw [Set.indicator_of_notMem hx]
      have h1 : Y x ≤ K₀ := not_lt.1 hx
      have := Real.rpow_le_rpow (hY0 x) h1 hp.le
      linarith
  have hint1 : ∫ x, Y x ^ p ∂P ≤ K₀ ^ p + ∫ x, S'.indicator (fun x => Y x ^ p) x ∂P := by
    calc ∫ x, Y x ^ p ∂P ≤ ∫ x, (K₀ ^ p + S'.indicator (fun x => Y x ^ p) x) ∂P :=
          integral_mono hYpi ((integrable_const _).add hind) hpt
      _ = _ := by rw [integral_add (integrable_const _) hind]; simp
  -- Cauchy–Schwarz
  have hg2 : ∀ x, (S'.indicator (1 : X → ℝ) x) ^ (2 : ℝ) = S'.indicator (1 : X → ℝ) x := fun x => by
    by_cases hx : x ∈ S' <;> simp [hx]
  have hf2 : ∀ x, (Y x ^ p) ^ (2 : ℝ) = Y x ^ (2 * p) := fun x => by
    rw [← Real.rpow_mul (hY0 x), mul_comm]
  have hf2n : ∀ x, (Y x ^ p) ^ (2 : ℕ) = Y x ^ (2 * p) := fun x => by
    rw [← hf2 x]; norm_cast
  have hfL2 : MemLp (fun x => Y x ^ p) (ENNReal.ofReal 2) P := by
    rw [show ENNReal.ofReal 2 = 2 by simp, memLp_two_iff_integrable_sq hYpm.aestronglyMeasurable]
    exact hY2i.congr (ae_of_all _ fun x => (hf2n x).symm)
  have hgL2 : MemLp (S'.indicator (1 : X → ℝ)) (ENNReal.ofReal 2) P := by
    rw [show ENNReal.ofReal 2 = 2 by simp,
      memLp_two_iff_integrable_sq (f := S'.indicator (1 : X → ℝ))
        (measurable_const.indicator hS'meas).aestronglyMeasurable]
    refine (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all _ fun x => ?_)
    · exact ((measurable_const.indicator hS'meas).pow_const 2).aestronglyMeasurable
    · by_cases hx : x ∈ S' <;> simp [hx]
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (f := fun x => Y x ^ p) (g := S'.indicator (1 : X → ℝ))
    (ae_of_all _ hYpnn) (ae_of_all _ fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
    hfL2 hgL2
  simp only [hf2, hg2] at hCS
  have hE : ∫ x, Y x ^ p * S'.indicator (1 : X → ℝ) x ∂P =
      ∫ x, S'.indicator (fun x => Y x ^ p) x ∂P := by
    congr 1
    funext x
    by_cases hx : x ∈ S' <;> simp [hx]
  rw [hE, integral_indicator_one hS'meas, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hCS
  have hsq : Real.sqrt (P.real S') ≤ Real.sqrt δ := by
    rcases le_or_gt 0 δ with hδ | hδ
    · apply Real.sqrt_le_sqrt
      rw [measureReal_def]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hPS').trans
        (by rw [ENNReal.toReal_ofReal hδ])
    · have h0 : P S' = 0 := by
        rw [ENNReal.ofReal_of_nonpos hδ.le] at hPS'
        exact le_antisymm hPS' bot_le
      rw [measureReal_def, h0]
      simp
  calc ∫ x, Y x ^ p ∂P ≤ K₀ ^ p + ∫ x, S'.indicator (fun x => Y x ^ p) x ∂P := hint1
    _ ≤ K₀ ^ p + Real.sqrt (∫ x, Y x ^ (2 * p) ∂P) * Real.sqrt (P.real S') := by linarith
    _ ≤ K₀ ^ p + Real.sqrt Cs * Real.sqrt δ := by
        gcongr

end LSBA
