import LSBA.Dyson.FreeGreen
import LSBA.Dyson.FiniteCycle
import LSBA.Dyson.Distribution

/-!
# Line and cycle Dyson solutions: perturbation

Lemma A.3 [bl:lem:finite] in local form in the `(b, β)` family, from the line to the cycle, with
rate `e^{-cL}`; the explicit decay of (A.4) [da:eq:free-decay-factor]; and the finite-cycle boundary
value at a `ℂ_+` root of (5.2) [fo:eq:dyson-family] for every `L ≥ 1`.
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Averages of the resolvent `R_w = (a - w)⁻¹` of a real variable `a`

The line transform `f_b` and the cycle transform `f_{b,L}` of (A.1) [bl:eq:physical] are both
`⟨R_w⟩ = ∫ (a - w)⁻¹ dν` for a probability measure `ν`: the normalized Lebesgue measure on
`(-π, π]` with `a(p) = 2b cos p`, and the uniform measure on `Fin L` with
`a(k) = 2b cos(2πk/L)`. -/

section Generic

open scoped ComplexOrder

variable {α : Type*}

/-- `R_w(x) = (a(x) - w)⁻¹`. -/
private def pR (a : α → ℝ) (w : ℂ) (x : α) : ℂ := ((a x : ℂ) - w)⁻¹

private lemma pR_base_ne (a : α → ℝ) {w : ℂ} (hw : 0 < w.im) (x : α) : (a x : ℂ) - w ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

private lemma norm_pR_le (a : α → ℝ) {w : ℂ} (hw : 0 < w.im) (x : α) : ‖pR a w x‖ ≤ w.im⁻¹ := by
  unfold pR
  rw [norm_inv]
  apply inv_anti₀ hw
  calc w.im = |((a x : ℂ) - w).im| := by simp [abs_of_pos hw]
    _ ≤ ‖(a x : ℂ) - w‖ := Complex.abs_im_le_norm _

private lemma im_pR (a : α → ℝ) (w : ℂ) (x : α) : (pR a w x).im = w.im * ‖pR a w x‖ ^ 2 := by
  unfold pR
  rw [Complex.inv_im, Complex.sq_norm, Complex.normSq_inv]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  ring

private lemma pR_sub (a : α → ℝ) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) (x : α) :
    pR a w x - pR a w' x = (w - w') * (pR a w x * pR a w' x) := by
  unfold pR
  have h1 := pR_base_ne a hw x
  have h2 := pR_base_ne a hw' x
  field_simp
  ring

variable [MeasurableSpace α]

/-- `⟨R_w⟩ = ∫ (a - w)⁻¹ dν`. -/
private def pT (ν : Measure α) (a : α → ℝ) (w : ℂ) : ℂ := ∫ x, pR a w x ∂ν

/-- `⟨R_w R_{w'}⟩`. -/
private def pK (ν : Measure α) (a : α → ℝ) (w w' : ℂ) : ℂ := ∫ x, pR a w x * pR a w' x ∂ν

/-- `⟨|R_w|²⟩`. -/
private def pN (ν : Measure α) (a : α → ℝ) (w : ℂ) : ℝ := ∫ x, ‖pR a w x‖ ^ 2 ∂ν

private lemma measurable_pR {a : α → ℝ} (ha : Measurable a) (w : ℂ) : Measurable (pR a w) :=
  ((Complex.measurable_ofReal.comp ha).sub_const w).inv

private lemma integrable_of_bdd {E : Type*} [NormedAddCommGroup E] (ν : Measure α)
    [IsFiniteMeasure ν] {φ : α → E} (hφ : AEStronglyMeasurable φ ν) (C : ℝ)
    (h : ∀ x, ‖φ x‖ ≤ C) : Integrable φ ν :=
  (integrable_const C).mono' hφ (ae_of_all _ h)

variable (ν : Measure α) [IsProbabilityMeasure ν] {a : α → ℝ}

private lemma integrable_pR (ha : Measurable a) {w : ℂ} (hw : 0 < w.im) :
    Integrable (pR a w) ν :=
  integrable_of_bdd ν (measurable_pR ha w).aestronglyMeasurable _ (norm_pR_le a hw)

private lemma integrable_pR_mul (ha : Measurable a) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) :
    Integrable (fun x => pR a w x * pR a w' x) ν :=
  integrable_of_bdd ν ((measurable_pR ha w).mul (measurable_pR ha w')).aestronglyMeasurable
    (w.im⁻¹ * w'.im⁻¹) (fun x => by
      rw [norm_mul]
      exact mul_le_mul (norm_pR_le a hw x) (norm_pR_le a hw' x) (norm_nonneg _)
        (inv_nonneg.mpr hw.le))

private lemma integrable_pR_sq (ha : Measurable a) {w : ℂ} (hw : 0 < w.im) :
    Integrable (fun x => ‖pR a w x‖ ^ 2) ν :=
  integrable_of_bdd ν ((measurable_pR ha w).norm.pow_const 2).aestronglyMeasurable
    (w.im⁻¹ ^ 2) (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_pR_le a hw x) 2)

private lemma norm_pT_le {w : ℂ} (hw : 0 < w.im) : ‖pT ν a w‖ ≤ w.im⁻¹ := by
  have := norm_integral_le_of_norm_le_const (μ := ν) (ae_of_all _ (norm_pR_le a hw))
  simpa [pT] using this

private lemma norm_pK_le {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) :
    ‖pK ν a w w'‖ ≤ w.im⁻¹ * w'.im⁻¹ := by
  have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun x => pR a w x * pR a w' x)
    (ae_of_all _ (fun x => by
      rw [norm_mul]
      exact mul_le_mul (norm_pR_le a hw x) (norm_pR_le a hw' x) (norm_nonneg _)
        (inv_nonneg.mpr hw.le)))
  simpa [pK] using this

/-- Resolvent identity, averaged: `⟨R_w⟩ - ⟨R_{w'}⟩ = (w - w') ⟨R_w R_{w'}⟩`. -/
private lemma pT_sub (ha : Measurable a) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) :
    pT ν a w - pT ν a w' = (w - w') * pK ν a w w' := by
  unfold pT pK
  rw [← integral_sub (integrable_pR ν ha hw) (integrable_pR ν ha hw'), ← integral_const_mul]
  congr 1
  funext x
  exact pR_sub a hw hw' x

/-- Ward identity: `Im ⟨R_w⟩ = Im w · ⟨|R_w|²⟩`. -/
private lemma im_pT (ha : Measurable a) {w : ℂ} (hw : 0 < w.im) :
    (pT ν a w).im = w.im * pN ν a w := by
  unfold pT pN
  have h := integral_im (μ := ν) (integrable_pR ν ha hw)
  simp only [RCLike.im_to_complex] at h
  rw [← h, ← integral_const_mul]
  congr 1
  funext x
  exact im_pR a w x

/-- Lipschitz bound for the kernel `⟨R_{w₁} R_{w₂}⟩` on `Im ≥ ι`. -/
private lemma pK_lip (ha : Measurable a) {ι : ℝ} (hι : 0 < ι) {w₁ w₂ w₃ w₄ : ℂ}
    (h₁ : ι ≤ w₁.im) (h₂ : ι ≤ w₂.im) (h₃ : ι ≤ w₃.im) (h₄ : ι ≤ w₄.im) :
    ‖pK ν a w₁ w₂ - pK ν a w₃ w₄‖ ≤ (‖w₁ - w₃‖ + ‖w₂ - w₄‖) / ι ^ 3 := by
  have p₁ := lt_of_lt_of_le hι h₁
  have p₂ := lt_of_lt_of_le hι h₂
  have p₃ := lt_of_lt_of_le hι h₃
  have p₄ := lt_of_lt_of_le hι h₄
  have hb : ∀ {w : ℂ} (hw : ι ≤ w.im) (x : α), ‖pR a w x‖ ≤ ι⁻¹ := fun hw x =>
    (norm_pR_le a (lt_of_lt_of_le hι hw) x).trans (inv_anti₀ hι hw)
  unfold pK
  rw [← integral_sub (integrable_pR_mul ν ha p₁ p₂) (integrable_pR_mul ν ha p₃ p₄)]
  have := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun x => pR a w₁ x * pR a w₂ x - pR a w₃ x * pR a w₄ x)
    (C := (‖w₁ - w₃‖ + ‖w₂ - w₄‖) / ι ^ 3) (ae_of_all _ (fun x => by
      have e : pR a w₁ x * pR a w₂ x - pR a w₃ x * pR a w₄ x =
          (w₁ - w₃) * (pR a w₁ x * pR a w₃ x) * pR a w₂ x +
            pR a w₃ x * ((w₂ - w₄) * (pR a w₂ x * pR a w₄ x)) := by
        rw [← pR_sub a p₁ p₃, ← pR_sub a p₂ p₄]; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul]
      have b1 := hb h₁ x; have b2 := hb h₂ x; have b3 := hb h₃ x; have b4 := hb h₄ x
      have n1 := norm_nonneg (pR a w₁ x); have n2 := norm_nonneg (pR a w₂ x)
      have n3 := norm_nonneg (pR a w₃ x); have n4 := norm_nonneg (pR a w₄ x)
      have m1 := norm_nonneg (w₁ - w₃); have m2 := norm_nonneg (w₂ - w₄)
      have hi : ι⁻¹ ^ 3 = 1 / ι ^ 3 := by rw [inv_pow, one_div]
      have k1 : ‖pR a w₁ x‖ * ‖pR a w₃ x‖ * ‖pR a w₂ x‖ ≤ ι⁻¹ ^ 3 := by
        calc _ ≤ ι⁻¹ * ι⁻¹ * ι⁻¹ := by gcongr
          _ = _ := by ring
      have k2 : ‖pR a w₃ x‖ * (‖pR a w₂ x‖ * ‖pR a w₄ x‖) ≤ ι⁻¹ ^ 3 := by
        calc _ ≤ ι⁻¹ * (ι⁻¹ * ι⁻¹) := by gcongr
          _ = _ := by ring
      calc ‖w₁ - w₃‖ * (‖pR a w₁ x‖ * ‖pR a w₃ x‖) * ‖pR a w₂ x‖ +
            ‖pR a w₃ x‖ * (‖w₂ - w₄‖ * (‖pR a w₂ x‖ * ‖pR a w₄ x‖))
          = ‖w₁ - w₃‖ * (‖pR a w₁ x‖ * ‖pR a w₃ x‖ * ‖pR a w₂ x‖) +
            ‖w₂ - w₄‖ * (‖pR a w₃ x‖ * (‖pR a w₂ x‖ * ‖pR a w₄ x‖)) := by ring
        _ ≤ ‖w₁ - w₃‖ * ι⁻¹ ^ 3 + ‖w₂ - w₄‖ * ι⁻¹ ^ 3 := by gcongr
        _ = (‖w₁ - w₃‖ + ‖w₂ - w₄‖) / ι ^ 3 := by rw [hi]; ring))
  simpa using this

/-- `(∫ f)² ≤ ∫ f²` for a probability measure. -/
private lemma sq_integral_le {f : α → ℝ} (hf : Integrable f ν)
    (hf2 : Integrable (fun x => f x ^ 2) ν) :
    (∫ x, f x ∂ν) ^ 2 ≤ ∫ x, f x ^ 2 ∂ν := by
  set m := ∫ x, f x ∂ν with hm
  have h0 : 0 ≤ ∫ x, (f x - m) ^ 2 ∂ν := integral_nonneg (fun x => sq_nonneg _)
  have e : ∫ x, (f x - m) ^ 2 ∂ν = ∫ x, f x ^ 2 ∂ν - m ^ 2 := by
    have e1 : ∀ x, (f x - m) ^ 2 = f x ^ 2 - (2 * m * f x - m ^ 2) := fun x => by ring
    simp_rw [e1]
    rw [integral_sub (f := fun x => f x ^ 2) (g := fun x => 2 * m * f x - m ^ 2) hf2
        (by exact (hf.const_mul _).sub (integrable_const _)),
      integral_sub (f := fun x => 2 * m * f x) (g := fun _ => m ^ 2) (hf.const_mul _)
        (integrable_const _), integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul, ← hm]
    ring
  linarith

/-- Stability bound of (A.6) [da:eq:ward]: at a solution `u = ⟨R_w⟩`, `w = z + βu`,
`Im z ≥ 0`, one has `Re(1 - β⟨R_w²⟩) ≥ 2β(Im u)²`. -/
private lemma stab_pK (ha : Measurable a) {β : ℝ} (hβ : 0 < β) {z u : ℂ} (hz : 0 ≤ z.im)
    (hu : 0 < u.im) (hroot : u = pT ν a (z + β * u)) :
    2 * β * u.im ^ 2 ≤ (1 - β * pK ν a (z + β * u) (z + β * u)).re := by
  set w := z + β * u with hwdef
  have hwim : w.im = z.im + β * u.im := by simp [hwdef]
  have hw : 0 < w.im := by rw [hwim]; positivity
  have hward := im_pT ν ha hw
  rw [← hroot] at hward
  -- `β ⟨|R|²⟩ ≤ 1`
  have hN : β * pN ν a w ≤ 1 := by
    have hN0 : 0 ≤ pN ν a w := integral_nonneg (fun x => sq_nonneg _)
    have h1 : u.im * (β * pN ν a w) ≤ u.im * 1 := by
      have h2 := hward
      rw [hwim] at h2
      nlinarith [mul_nonneg hz hN0]
    exact le_of_mul_le_mul_left h1 hu
  -- `Re⟨R²⟩ = ⟨|R|²⟩ - 2⟨(Im R)²⟩`
  have hIm : Integrable (fun x => (pR a w x).im) ν :=
    integrable_of_bdd ν (Complex.continuous_im.measurable.comp
      (measurable_pR ha w)).aestronglyMeasurable w.im⁻¹
      (fun x => (Complex.abs_im_le_norm _).trans (norm_pR_le a hw x))
  have hIm2 : Integrable (fun x => (pR a w x).im ^ 2) ν :=
    integrable_of_bdd ν ((Complex.continuous_im.measurable.comp
      (measurable_pR ha w)).pow_const 2).aestronglyMeasurable (w.im⁻¹ ^ 2)
      (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have := (Complex.abs_im_le_norm (pR a w x)).trans (norm_pR_le a hw x)
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2)
  have hre : (pK ν a w w).re = pN ν a w - 2 * ∫ x, (pR a w x).im ^ 2 ∂ν := by
    unfold pK pN
    have h := integral_re (μ := ν) (integrable_pR_mul ν ha hw hw)
    simp only [RCLike.re_to_complex] at h
    rw [← h, ← integral_const_mul, ← integral_sub (integrable_pR_sq ν ha hw) (hIm2.const_mul 2)]
    congr 1
    funext x
    rw [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hJ : u.im ^ 2 ≤ ∫ x, (pR a w x).im ^ 2 ∂ν := by
    have h := integral_im (μ := ν) (integrable_pR ν ha hw)
    simp only [RCLike.im_to_complex] at h
    have hu' : u.im = ∫ x, (pR a w x).im ∂ν := by rw [h, hroot]; rfl
    rw [hu']
    exact sq_integral_le ν hIm hIm2
  have : (1 - (β : ℂ) * pK ν a w w).re = 1 - β * (pK ν a w w).re := by
    simp [Complex.mul_re]
  rw [this, hre]
  nlinarith

end Generic

/-! ### Quantitative contraction -/

/-- A map which is a `1/2`-contraction on `B̄(x₀, r)` and moves `x₀` by at most `r/2` has a fixed
point in the ball, at distance at most `2‖T x₀ - x₀‖` from `x₀`. -/
private lemma fixed_of_contr (T : ℂ → ℂ) (x₀ : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hlip : ∀ u ∈ Metric.closedBall x₀ r, ∀ v ∈ Metric.closedBall x₀ r,
      ‖T u - T v‖ ≤ ‖u - v‖ / 2)
    (h0 : ‖T x₀ - x₀‖ ≤ r / 2) :
    ∃ p ∈ Metric.closedBall x₀ r, T p = p ∧ ‖p - x₀‖ ≤ 2 * ‖T x₀ - x₀‖ := by
  set S := Metric.closedBall x₀ r with hS
  have hx₀ : x₀ ∈ S := Metric.mem_closedBall_self hr
  have hmaps : ∀ u ∈ S, T u ∈ S := by
    intro u hu
    have h1 := hlip u hu x₀ hx₀
    rw [Metric.mem_closedBall, dist_eq_norm] at hu ⊢
    calc ‖T u - x₀‖ ≤ ‖T u - T x₀‖ + ‖T x₀ - x₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖u - x₀‖ / 2 + r / 2 := add_le_add h1 h0
      _ ≤ r := by linarith
  let f : S → S := fun u => ⟨T u, hmaps u u.2⟩
  have : Nonempty S := ⟨⟨x₀, hx₀⟩⟩
  have : CompleteSpace S := Metric.isClosed_closedBall.completeSpace_coe
  have hf : ContractingWith (1 / 2 : NNReal) f := by
    refine ⟨by norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    simp only [Subtype.dist_eq, dist_eq_norm, f]
    have := hlip u u.2 v v.2
    push_cast
    linarith
  set p := ContractingWith.fixedPoint f hf
  have hp : f p = p := hf.fixedPoint_isFixedPt
  have hTp : T p = p := congrArg Subtype.val hp
  refine ⟨p, p.2, hTp, ?_⟩
  have h1 := hlip p p.2 x₀ hx₀
  rw [hTp] at h1
  have h2 : ‖(p : ℂ) - x₀‖ ≤ ‖(p : ℂ) - T x₀‖ + ‖T x₀ - x₀‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  linarith

private lemma im_ge_of_mem_ball {u u₀ : ℂ} {r : ℝ} (hu : u ∈ Metric.closedBall u₀ r) :
    u₀.im - r ≤ u.im := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hu
  have := Complex.abs_im_le_norm (u - u₀)
  rw [Complex.sub_im] at this
  linarith [neg_abs_le (u.im - u₀.im)]

/-- Perturbation of a root (quantitative implicit function theorem behind Lemma A.3
[bl:lem:finite]): a solution `u₀` of `u = ⟨R_{z₁ + βu}⟩₁` with `Im u₀ ≥ c₀` gives a solution of
`u = ⟨R_{z₂ + βu}⟩₂` near `u₀`, when the kernels and the defect at `u₀` are small. -/
private lemma root_perturb {α₁ α₂ : Type*} [MeasurableSpace α₁] [MeasurableSpace α₂]
    (ν₁ : Measure α₁) [IsProbabilityMeasure ν₁] (ν₂ : Measure α₂) [IsProbabilityMeasure ν₂]
    {a₁ : α₁ → ℝ} {a₂ : α₂ → ℝ} (ha₁ : Measurable a₁) (ha₂ : Measurable a₂)
    {β c₀ r : ℝ} (hβ : 0 < β) (hc₀ : 0 < c₀) (hr : 0 ≤ r) (hrc : r < c₀) {z₁ z₂ u₀ : ℂ}
    (hz₁ : 0 ≤ z₁.im) (hz₂ : 0 ≤ z₂.im) (hu₀ : c₀ ≤ u₀.im)
    (hroot : u₀ = pT ν₁ a₁ (z₁ + β * u₀))
    (hK : ∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
      ‖pK ν₂ a₂ (z₂ + β * u) (z₂ + β * v) - pK ν₁ a₁ (z₁ + β * u₀) (z₁ + β * u₀)‖ ≤ c₀ ^ 2)
    (hF : ‖pT ν₂ a₂ (z₂ + β * u₀) - u₀‖ ≤ β * c₀ ^ 2 * r) :
    ∃ u : ℂ, c₀ - r ≤ u.im ∧ u = pT ν₂ a₂ (z₂ + β * u) ∧
      ‖u - u₀‖ ≤ ‖pT ν₂ a₂ (z₂ + β * u₀) - u₀‖ / (β * c₀ ^ 2) := by
  set K₁ := pK ν₁ a₁ (z₁ + β * u₀) (z₁ + β * u₀) with hK₁
  set D : ℂ := 1 - β * K₁ with hDdef
  have hd : 0 < 2 * β * c₀ ^ 2 := by positivity
  have hDre : 2 * β * c₀ ^ 2 ≤ D.re := by
    have h := stab_pK ν₁ ha₁ hβ hz₁ (lt_of_lt_of_le hc₀ hu₀) hroot
    have : c₀ ^ 2 ≤ u₀.im ^ 2 := pow_le_pow_left₀ hc₀.le hu₀ 2
    nlinarith
  have hDn : 2 * β * c₀ ^ 2 ≤ ‖D‖ := hDre.trans (Complex.re_le_norm D)
  have hD0 : D ≠ 0 := by
    intro h; rw [h, norm_zero] at hDn; linarith
  have hDpos : 0 < ‖D‖ := lt_of_lt_of_le hd hDn
  set T : ℂ → ℂ := fun u => u - (u - pT ν₂ a₂ (z₂ + β * u)) / D with hT
  have hwpos : ∀ u ∈ Metric.closedBall u₀ r, 0 < (z₂ + β * u).im := by
    intro u hu
    have := im_ge_of_mem_ball hu
    have hpos : 0 < u.im := by linarith
    simp only [Complex.add_im, Complex.im_ofReal_mul]
    positivity
  have hlip : ∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
      ‖T u - T v‖ ≤ ‖u - v‖ / 2 := by
    intro u hu v hv
    have hsub := pT_sub ν₂ ha₂ (hwpos u hu) (hwpos v hv)
    have e : T u - T v =
        (u - v) * (β * (pK ν₂ a₂ (z₂ + β * u) (z₂ + β * v) - K₁)) / D := by
      simp only [hT]
      have e2 : pT ν₂ a₂ (z₂ + β * u) = pT ν₂ a₂ (z₂ + β * v) +
          (z₂ + β * u - (z₂ + β * v)) * pK ν₂ a₂ (z₂ + β * u) (z₂ + β * v) := by
        rw [← hsub]; ring
      rw [e2]
      field_simp
      rw [hDdef]
      ring
    rw [e, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ.le]
    rw [div_le_div_iff₀ hDpos (by norm_num : (0 : ℝ) < 2)]
    have := hK u hu v hv
    have hn := norm_nonneg (u - v)
    calc ‖u - v‖ * (β * ‖pK ν₂ a₂ (z₂ + β * u) (z₂ + β * v) - K₁‖) * 2
        ≤ ‖u - v‖ * (β * c₀ ^ 2) * 2 := by gcongr
      _ = ‖u - v‖ * (2 * β * c₀ ^ 2) := by ring
      _ ≤ ‖u - v‖ * ‖D‖ := by gcongr
  have hT0 : T u₀ - u₀ = (pT ν₂ a₂ (z₂ + β * u₀) - u₀) / D := by
    simp only [hT]; ring
  have hT0n : ‖T u₀ - u₀‖ ≤ ‖pT ν₂ a₂ (z₂ + β * u₀) - u₀‖ / (2 * β * c₀ ^ 2) := by
    rw [hT0, norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hd hDn
  have h0 : ‖T u₀ - u₀‖ ≤ r / 2 := by
    refine hT0n.trans ?_
    rw [div_le_iff₀ hd]
    nlinarith
  obtain ⟨p, hp, hTp, hdist⟩ := fixed_of_contr T u₀ hr hlip h0
  refine ⟨p, ?_, ?_, ?_⟩
  · have := im_ge_of_mem_ball hp
    linarith
  · have h1 : (p - pT ν₂ a₂ (z₂ + β * p)) / D = 0 := by
      have : T p - p = 0 := by rw [hTp]; ring
      simp only [hT] at this
      linear_combination -this
    rcases div_eq_zero_iff.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hD0
  · calc ‖p - u₀‖ ≤ 2 * ‖T u₀ - u₀‖ := hdist
      _ ≤ 2 * (‖pT ν₂ a₂ (z₂ + β * u₀) - u₀‖ / (2 * β * c₀ ^ 2)) := by gcongr
      _ = ‖pT ν₂ a₂ (z₂ + β * u₀) - u₀‖ / (β * c₀ ^ 2) := by
        field_simp

/-- Comparison of the kernels `⟨R_w²⟩` of two averages, through the defect `⟨R⟩₂ - ⟨R⟩₁` at
`w` and at `w + it`. -/
private lemma pK_cross {α₁ α₂ : Type*} [MeasurableSpace α₁] [MeasurableSpace α₂]
    (ν₁ : Measure α₁) [IsProbabilityMeasure ν₁] (ν₂ : Measure α₂) [IsProbabilityMeasure ν₂]
    {a₁ : α₁ → ℝ} {a₂ : α₂ → ℝ} (ha₁ : Measurable a₁) (ha₂ : Measurable a₂)
    {ι t : ℝ} (hι : 0 < ι) (ht : 0 < t) {w : ℂ} (hw : ι ≤ w.im) :
    ‖pK ν₂ a₂ w w - pK ν₁ a₁ w w‖ ≤ 2 * t / ι ^ 3 +
      (‖pT ν₂ a₂ w - pT ν₁ a₁ w‖ + ‖pT ν₂ a₂ (w + t * I) - pT ν₁ a₁ (w + t * I)‖) / t := by
  set w' := w + t * I with hw'def
  have hw' : ι ≤ w'.im := by simp [hw'def]; linarith
  have p : 0 < w.im := lt_of_lt_of_le hι hw
  have p' : 0 < w'.im := lt_of_lt_of_le hι hw'
  have hdw : ‖w - w'‖ = t := by
    rw [hw'def, show w - (w + t * I) = -(t * I) by ring, norm_neg, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_of_nonneg ht.le]
  have l₂ := pK_lip ν₂ ha₂ hι hw hw hw hw'
  have l₁ := pK_lip ν₁ ha₁ hι hw hw' hw hw
  rw [sub_self, norm_zero, zero_add, hdw] at l₂
  rw [sub_self, norm_zero, zero_add, norm_sub_rev w' w, hdw] at l₁
  have hmid : ‖pK ν₂ a₂ w w' - pK ν₁ a₁ w w'‖ ≤
      (‖pT ν₂ a₂ w - pT ν₁ a₁ w‖ + ‖pT ν₂ a₂ w' - pT ν₁ a₁ w'‖) / t := by
    have s₂ := pT_sub ν₂ ha₂ p p'
    have s₁ := pT_sub ν₁ ha₁ p p'
    have e : (w - w') * (pK ν₂ a₂ w w' - pK ν₁ a₁ w w') =
        (pT ν₂ a₂ w - pT ν₁ a₁ w) - (pT ν₂ a₂ w' - pT ν₁ a₁ w') := by
      rw [mul_sub, ← s₂, ← s₁]; ring
    rw [le_div_iff₀ ht, ← hdw, mul_comm, ← norm_mul, e]
    exact norm_sub_le _ _
  calc ‖pK ν₂ a₂ w w - pK ν₁ a₁ w w‖
      ≤ ‖pK ν₂ a₂ w w - pK ν₂ a₂ w w'‖ + ‖pK ν₂ a₂ w w' - pK ν₁ a₁ w w'‖ +
          ‖pK ν₁ a₁ w w' - pK ν₁ a₁ w w‖ :=
        (norm_sub_le_norm_sub_add_norm_sub _ (pK ν₁ a₁ w w') _).trans
          (add_le_add_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) _)
    _ ≤ t / ι ^ 3 + (‖pT ν₂ a₂ w - pT ν₁ a₁ w‖ + ‖pT ν₂ a₂ w' - pT ν₁ a₁ w'‖) / t +
          t / ι ^ 3 := add_le_add (add_le_add l₂ hmid) l₁
    _ = _ := by ring

/-! ### The line and cycle averages -/

/-- Normalized Lebesgue measure on `(-π, π]`. -/
private def lineMeas : Measure ℝ := ENNReal.ofReal (2 * π)⁻¹ • volume.restrict (Set.Ioc (-π) π)

private instance : IsProbabilityMeasure lineMeas := by
  constructor
  have hπ := Real.pi_pos
  simp only [lineMeas, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioc, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity)]
  rw [show (2 * π)⁻¹ * (π - -π) = 1 by field_simp; ring]
  simp

/-- Uniform probability measure on `Fin L`. -/
private def gridMeas (L : ℕ) : Measure (Fin L) := (L : ℝ≥0∞)⁻¹ • Measure.count

private lemma isProb_gridMeas {L : ℕ} (hL : 1 ≤ L) : IsProbabilityMeasure (gridMeas L) := by
  constructor
  have hL0 : (L : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  simp only [gridMeas, Measure.smul_apply, Measure.count_univ, smul_eq_mul]
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin, ENat.toENNReal_coe]
  exact ENNReal.inv_mul_cancel hL0 (ENNReal.natCast_ne_top L)

private lemma freeT_eq_pT (b : ℝ) (w : ℂ) :
    freeT b w = pT lineMeas (fun p => 2 * b * Real.cos p) w := by
  have hπ := Real.pi_pos
  unfold freeT pT pR lineMeas
  rw [integral_smul_measure, intervalIntegral.integral_of_le (by linarith),
    ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
  push_cast
  ring

private lemma freeTL_eq_pT (b : ℝ) (L : ℕ) (w : ℂ) :
    freeTL b L w = pT (gridMeas L) (fun k : Fin L => 2 * b * Real.cos (2 * π * k / L)) w := by
  unfold freeTL pT pR gridMeas
  rw [integral_smul_measure, integral_count, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Complex.real_smul]
  push_cast
  ring

private lemma measurable_lineA (b : ℝ) : Measurable (fun p : ℝ => 2 * b * Real.cos p) := by
  fun_prop

private lemma measurable_gridA (b : ℝ) (L : ℕ) :
    Measurable (fun k : Fin L => 2 * b * Real.cos (2 * π * k / L)) :=
  measurable_from_top

/-! ### The decay factor -/

/-- (A.4) [da:eq:free-decay-factor], explicit: `|ρ(w)| ≤ 2b/(2b + Im w)`. -/
theorem norm_freeRho_le (b : ℝ) (hb : 0 ≤ b) (w : ℂ) (hw : 0 < w.im) :
    ‖freeRho b w‖ ≤ 2 * b / (2 * b + w.im) := by
  set s := freeS b w with hsdef
  set t := w + s with htdef
  have hs := freeS_sq b w
  have hsim := freeS_im_pos b w hw
  have htim : 0 < t.im := by rw [htdef, Complex.add_im]; linarith
  have ht0 : t ≠ 0 := fun h => by rw [h] at htim; simp at htim
  have hd : w - s = ((4 * b ^ 2 : ℝ) : ℂ) * t⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ ht0, htdef]
    push_cast
    linear_combination -hs
  set N := Complex.normSq t with hN
  have hNpos : 0 < N := Complex.normSq_pos.mpr ht0
  have him : 2 * w.im * N = t.im * (N - 4 * b ^ 2) := by
    have e : 2 * w = t + (w - s) := by rw [htdef]; ring
    have e2 := congrArg Complex.im e
    rw [hd, Complex.add_im, Complex.im_ofReal_mul, Complex.inv_im, ← hN] at e2
    have e3 : (2 * w).im = 2 * w.im := by simp
    rw [e3] at e2
    field_simp at e2
    linear_combination e2
  set n := ‖t‖ with hn
  have hn0 : 0 < n := norm_pos_iff.mpr ht0
  have hNn : N = n ^ 2 := by rw [hN, Complex.normSq_eq_norm_sq]
  have hy : t.im ≤ n := (le_abs_self _).trans (Complex.abs_im_le_norm t)
  have hgap : 0 < N - 4 * b ^ 2 := by
    by_contra h
    have h' : t.im * (N - 4 * b ^ 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htim.le (not_lt.mp h)
    nlinarith
  have hn2b : 2 * b < n := by
    rw [hNn] at hgap
    nlinarith
  have hkey : w.im ≤ n - 2 * b := by
    have h1 : 2 * w.im * n ^ 2 ≤ n * (n ^ 2 - 4 * b ^ 2) := by
      rw [← hNn, him]
      exact mul_le_mul_of_nonneg_right hy hgap.le
    have h2 : 2 * w.im * n ≤ n ^ 2 - 4 * b ^ 2 := by
      have : n * (2 * w.im * n) ≤ n * (n ^ 2 - 4 * b ^ 2) := by nlinarith
      exact le_of_mul_le_mul_left this hn0
    nlinarith
  have hρ : ‖freeRho b w‖ = 2 * b / ‖t‖ := by
    rw [freeRho, ← hsdef, ← htdef, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb]
    norm_num
  rw [hρ, ← hn]
  exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)

/-! ### The finite average in closed form -/

private lemma one_sub_mul_ne {ρ e : ℂ} (hρ : ‖ρ‖ < 1) (he : ‖e‖ = 1) : 1 - ρ * e ≠ 0 := by
  intro h
  have h1 : ρ * e = 1 := by linear_combination -h
  have := congrArg norm h1
  rw [norm_mul, he, mul_one, norm_one] at this
  linarith

/-- `L⁻¹ Σ_{k<L} (1 - ρ ξ^k)⁻¹ = (1 - ρ^L)⁻¹` for a primitive `L`-th root of unity `ξ`. -/
private lemma sum_inv_one_sub {L : ℕ} (hL : 1 ≤ L) {ξ : ℂ} (hξ : IsPrimitiveRoot ξ L) {ρ : ℂ}
    (hρ : ‖ρ‖ < 1) : ∑ k : Fin L, (1 - ρ * ξ ^ (k : ℕ))⁻¹ = L / (1 - ρ ^ L) := by
  have hξn : ‖ξ‖ = 1 := hξ.norm'_eq_one (by omega)
  have hρL : 1 - ρ ^ L ≠ 0 := by
    have := one_sub_mul_ne (e := 1) (ρ := ρ ^ L) (by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hρ (by omega)) norm_one
    rwa [mul_one] at this
  have hterm : ∀ k : ℕ, (1 - ρ * ξ ^ k)⁻¹ =
      (∑ j ∈ Finset.range L, ρ ^ j * (ξ ^ j) ^ k) / (1 - ρ ^ L) := by
    intro k
    have hne := one_sub_mul_ne hρ (by rw [norm_pow, hξn, one_pow] : ‖ξ ^ k‖ = 1)
    have h1 := geom_sum_mul (ρ * ξ ^ k) L
    have h2 : (ρ * ξ ^ k) ^ L = ρ ^ L := by
      rw [mul_pow, ← pow_mul, mul_comm k L, pow_mul, hξ.pow_eq_one, one_pow, mul_one]
    have h3 : ∑ j ∈ Finset.range L, ρ ^ j * (ξ ^ j) ^ k =
        ∑ j ∈ Finset.range L, (ρ * ξ ^ k) ^ j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j k]
    rw [h3, eq_div_iff hρL, inv_mul_eq_iff_eq_mul₀ hne]
    linear_combination h1 + h2
  rw [Fin.sum_univ_eq_sum_range (fun k => (1 - ρ * ξ ^ k)⁻¹) L]
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  have hinner : ∀ j ∈ Finset.range L, ∑ k ∈ Finset.range L, ρ ^ j * (ξ ^ j) ^ k =
      if j = 0 then (L : ℂ) else 0 := by
    intro j hj
    rw [← Finset.mul_sum]
    split_ifs with h0
    · subst h0; simp
    · have hx : ξ ^ j ≠ 1 := hξ.pow_ne_one_of_pos_of_lt h0 (Finset.mem_range.mp hj)
      have h1 := geom_sum_mul (ξ ^ j) L
      have hxL : (ξ ^ j) ^ L = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
      rw [hxL, sub_self] at h1
      have : ∑ i ∈ Finset.range L, (ξ ^ j) ^ i = 0 :=
        (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hx)
      rw [this, mul_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' (Finset.range L) 0 (fun _ => (L : ℂ))]
  simp [show 0 < L by omega]

/-- `2 cos(2πk/L) = ξ^k + ξ^{-k}`, `ξ = e^{2πi/L}`. -/
private lemma two_cos_grid (L k : ℕ) :
    ((2 * Real.cos (2 * π * k / L) : ℝ) : ℂ) =
      Complex.exp (2 * π * I / L) ^ k + (Complex.exp (2 * π * I / L))⁻¹ ^ k := by
  have e : ((2 * π * k / L : ℝ) : ℂ) * I = k * (2 * π * I / L) := by push_cast; ring
  rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_ofNat, Complex.two_cos, neg_mul, e,
    Complex.exp_neg, Complex.exp_nat_mul, inv_pow]

/-- (A.5) [bl:eq:free] averaged over the cycle: `f_L(w) - f(w) = 2f(w)ρ^L/(1 - ρ^L)`. -/
private lemma freeTL_sub_freeT (b : ℝ) {L : ℕ} (hL : 1 ≤ L) {w : ℂ} (hw : 0 < w.im) :
    freeTL b L w - freeT b w = 2 * freeT b w * freeRho b w ^ L / (1 - freeRho b w ^ L) := by
  by_cases hb : b = 0
  · subst hb
    have := isProb_gridMeas hL
    have hρ : freeRho 0 w = 0 := by simp [freeRho]
    rw [hρ, zero_pow (by omega), mul_zero, zero_div, freeT_eq_pT, freeTL_eq_pT]
    simp [pT, pR]
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  set ρ := freeRho b w with hρdef
  set s := freeS b w with hsdef
  have hρ1 : ‖ρ‖ < 1 := norm_freeRho_lt_one b w hw
  have hsim : 0 < s.im := freeS_im_pos b w hw
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsim; simp at hsim
  have ht0 : w + s ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hρt : ρ * (w + s) = 2 * b := by
    rw [hρdef, freeRho, ← hsdef]; field_simp
  have hss : s ^ 2 = w ^ 2 - 4 * (b : ℂ) ^ 2 := freeS_sq b w
  have hρw : ρ * w = b * (1 + ρ ^ 2) := by
    have hws : w - s = 2 * b * ρ := by
      have h3 : (w - s) * (w + s) = (2 * b * ρ) * (w + s) := by
        linear_combination (-1 : ℂ) * hss - (2 * (b : ℂ)) * hρt
      exact mul_right_cancel₀ ht0 h3
    linear_combination (1 / 2 : ℂ) * hρt + (1 / 2 : ℂ) * ρ * hws
  have hρs : ρ * s = b * (1 - ρ ^ 2) := by
    have hws : w - s = 2 * b * ρ := by
      have h3 : (w - s) * (w + s) = (2 * b * ρ) * (w + s) := by
        linear_combination (-1 : ℂ) * hss - (2 * (b : ℂ)) * hρt
      exact mul_right_cancel₀ ht0 h3
    linear_combination (1 / 2 : ℂ) * hρt - (1 / 2 : ℂ) * ρ * hws
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hρt
    exact (mul_ne_zero two_ne_zero hb') hρt.symm
  have hρ2 : 1 - ρ ^ 2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hρs
    exact (mul_ne_zero hρ0 hs0) hρs
  have hf : freeT b w = -s⁻¹ := freeT_eq b w hw
  set ξ := Complex.exp (2 * π * I / L) with hξdef
  have hξ : IsPrimitiveRoot ξ L := Complex.isPrimitiveRoot_exp L (by omega)
  have hξn : ‖ξ‖ = 1 := hξ.norm'_eq_one (by omega)
  have hξ0 : ξ ≠ 0 := fun h => by rw [h, norm_zero] at hξn; exact zero_ne_one hξn
  have hpt : ∀ k : ℕ, (((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ) - w)⁻¹ =
      freeT b w * ((1 - ρ * ξ ^ k)⁻¹ + (1 - ρ * ξ⁻¹ ^ k)⁻¹ - 1) := by
    intro k
    set e := ξ ^ k with he
    have he0 : e ≠ 0 := pow_ne_zero _ hξ0
    have hen : ‖e‖ = 1 := by rw [he, norm_pow, hξn, one_pow]
    have hein : ‖e⁻¹‖ = 1 := by rw [norm_inv, hen, inv_one]
    have h1 := one_sub_mul_ne hρ1 hen
    have h2 := one_sub_mul_ne hρ1 hein
    have h2' : e - ρ ≠ 0 := fun h => h2 (by
      rw [show ρ = e by linear_combination -h, mul_inv_cancel₀ he0, sub_self])
    have hcos : ((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ) = b * (e + e⁻¹) := by
      have := two_cos_grid L k
      rw [← hξdef, inv_pow, ← he] at this
      rw [show (((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ)) =
        (b : ℂ) * ((2 * Real.cos (2 * π * k / L) : ℝ) : ℂ) by push_cast; ring, this]
    rw [hcos, inv_pow, ← he, hf]
    have hbase : (b : ℂ) * (e + e⁻¹) - w = -(b * ρ⁻¹) * ((1 - ρ * e) * (1 - ρ * e⁻¹)) := by
      field_simp
      linear_combination (-e) * hρw
    have hs' : s = b * (1 - ρ ^ 2) * ρ⁻¹ := by
      field_simp
      linear_combination hρs
    rw [hbase, hs']
    field_simp
    ring
  have hS₁ := sum_inv_one_sub hL hξ hρ1
  have hS₂ := sum_inv_one_sub hL hξ.inv hρ1
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  have hρL : 1 - ρ ^ L ≠ 0 := by
    have := one_sub_mul_ne (e := 1) (ρ := ρ ^ L) (by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hρ1 (by omega)) norm_one
    rwa [mul_one] at this
  have hTL : freeTL b L w = freeT b w * (2 / (1 - ρ ^ L) - 1) := by
    unfold freeTL
    simp_rw [hpt]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, hS₁, hS₂]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
    ring
  rw [hTL]
  field_simp
  ring

/-! ### The cycle–line defect -/

private lemma rate_pos {B ι : ℝ} (hB : 0 < B) (hι : 0 < ι) :
    0 < 2 * B / (2 * B + ι) ∧ 2 * B / (2 * B + ι) < 1 :=
  ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩

private lemma norm_freeRho_le_rate {B ι b : ℝ} (hB : 0 < B) (hι : 0 < ι) (hb : 0 ≤ b)
    (hbB : b ≤ B) {w : ℂ} (hw : ι ≤ w.im) : ‖freeRho b w‖ ≤ 2 * B / (2 * B + ι) := by
  have hwpos := lt_of_lt_of_le hι hw
  refine (norm_freeRho_le b hb w hwpos).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul hbB hw hι.le hB.le]

private lemma norm_freeT_le' (b : ℝ) {ι : ℝ} (hι : 0 < ι) {w : ℂ} (hw : ι ≤ w.im) :
    ‖freeT b w‖ ≤ ι⁻¹ := by
  rw [freeT_eq_pT]
  exact (norm_pT_le lineMeas (lt_of_lt_of_le hι hw)).trans (inv_anti₀ hι hw)

/-- `|f_L(w) - f(w)| ≤ 2q^L/(ι(1 - q))` on `Im w ≥ ι`, `q = 2B/(2B + ι)`, `0 ≤ b ≤ B`. -/
private lemma freeTL_defect {B ι : ℝ} (hB : 0 < B) (hι : 0 < ι) {b : ℝ} (hb : 0 ≤ b)
    (hbB : b ≤ B) {L : ℕ} (hL : 1 ≤ L) {w : ℂ} (hw : ι ≤ w.im) :
    ‖freeTL b L w - freeT b w‖ ≤
      2 / (ι * (1 - 2 * B / (2 * B + ι))) * (2 * B / (2 * B + ι)) ^ L := by
  set q := 2 * B / (2 * B + ι) with hqdef
  obtain ⟨hq0, hq1⟩ := rate_pos hB hι
  have hwpos := lt_of_lt_of_le hι hw
  have hρ := norm_freeRho_le_rate hB hι hb hbB hw
  have hf := norm_freeT_le' b hι hw
  have hρL : ‖freeRho b w ^ L‖ ≤ q ^ L := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hρ L
  have hqL : q ^ L ≤ q := pow_le_of_le_one hq0.le hq1.le (by omega)
  have hden : 1 - q ≤ ‖1 - freeRho b w ^ L‖ := by
    have := norm_sub_norm_le (1 : ℂ) (freeRho b w ^ L)
    rw [norm_one] at this; linarith
  have h1q : 0 < 1 - q := by linarith
  rw [freeTL_sub_freeT b hL hwpos, norm_div, norm_mul, norm_mul, div_le_iff₀ (by linarith)]
  have hqL0 : 0 ≤ q ^ L := pow_nonneg hq0.le L
  calc ‖(2 : ℂ)‖ * ‖freeT b w‖ * ‖freeRho b w ^ L‖ ≤ 2 * ι⁻¹ * q ^ L := by
        rw [Complex.norm_two]; gcongr
    _ = 2 / (ι * (1 - q)) * q ^ L * (1 - q) := by field_simp
    _ ≤ 2 / (ι * (1 - q)) * q ^ L * ‖1 - freeRho b w ^ L‖ := by gcongr

private lemma pow_eq_exp {q : ℝ} (hq : 0 < q) (L : ℕ) : q ^ L = Real.exp (-(-Real.log q * L)) := by
  rw [show -(-Real.log q * L) = L * Real.log q by ring, Real.exp_nat_mul, Real.exp_log hq]

/-- Radius of the contraction ball, `min(c'/2, c'²ι³/4)` with `ι = β₀c'/2`. -/
private def tRad (β₀ c' : ℝ) : ℝ := min (c' / 2) (c' ^ 2 * (β₀ * c' / 2) ^ 3 / 4)

/-- Admissible defect, `min(c'⁴ι³/64, β₀c'²r)`. -/
private def tThr (β₀ c' : ℝ) : ℝ :=
  min (c' ^ 4 * (β₀ * c' / 2) ^ 3 / 64) (β₀ * c' ^ 2 * tRad β₀ c')

private lemma tThr_pos {β₀ c' : ℝ} (hβ₀ : 0 < β₀) (hc' : 0 < c') : 0 < tThr β₀ c' := by
  unfold tThr tRad
  have : 0 < min (c' / 2) (c' ^ 2 * (β₀ * c' / 2) ^ 3 / 4) := lt_min (by positivity) (by positivity)
  exact lt_min (by positivity) (by positivity)

/-- Transfer of a root between two averages whose transforms differ by at most `δ` on
`Im w ≥ β₀c'/2` (the local comparison in the proof of Lemma A.3 [bl:lem:finite]). -/
private lemma root_transfer {α₁ α₂ : Type*} [MeasurableSpace α₁] [MeasurableSpace α₂]
    (ν₁ : Measure α₁) [IsProbabilityMeasure ν₁] (ν₂ : Measure α₂) [IsProbabilityMeasure ν₂]
    {a₁ : α₁ → ℝ} {a₂ : α₂ → ℝ} (ha₁ : Measurable a₁) (ha₂ : Measurable a₂)
    {β₀ c' β δ : ℝ} (hβ₀ : 0 < β₀) (hc' : 0 < c') (hβ₀β : β₀ ≤ β) (hβ1 : β ≤ 1)
    (hδ : ∀ w : ℂ, β₀ * c' / 2 ≤ w.im → ‖pT ν₂ a₂ w - pT ν₁ a₁ w‖ ≤ δ)
    (hδθ : δ ≤ tThr β₀ c') {z u₀ : ℂ} (hz : 0 ≤ z.im) (hu₀ : c' ≤ u₀.im)
    (hroot : u₀ = pT ν₁ a₁ (z + β * u₀)) :
    ∃ u : ℂ, c' / 2 ≤ u.im ∧ u = pT ν₂ a₂ (z + β * u) ∧ ‖u - u₀‖ ≤ δ / (β₀ * c' ^ 2) := by
  set ι := β₀ * c' / 2 with hιdef
  set r := tRad β₀ c' with hrdef
  have hι : 0 < ι := by positivity
  have hβ : 0 < β := lt_of_lt_of_le hβ₀ hβ₀β
  have hr1 : r ≤ c' / 2 := min_le_left _ _
  have hr2 : r ≤ c' ^ 2 * ι ^ 3 / 4 := min_le_right _ _
  have hr0 : 0 < r := lt_min (by positivity) (by positivity)
  have hθ1 : δ ≤ c' ^ 4 * ι ^ 3 / 64 := hδθ.trans (min_le_left _ _)
  have hθ2 : δ ≤ β₀ * c' ^ 2 * r := hδθ.trans (min_le_right _ _)
  have hball : ∀ u ∈ Metric.closedBall u₀ r, ι ≤ (z + β * u).im := by
    intro u hu
    have := im_ge_of_mem_ball hu
    simp only [Complex.add_im, Complex.im_ofReal_mul]
    have h1 : c' / 2 ≤ u.im := by linarith
    have h2 : β₀ * (c' / 2) ≤ β * u.im := mul_le_mul hβ₀β h1 (by positivity) hβ.le
    rw [hιdef]; linarith
  have hu₀b : u₀ ∈ Metric.closedBall u₀ r := Metric.mem_closedBall_self hr0.le
  set w₀ := z + β * u₀ with hw₀
  have hw₀ι : ι ≤ w₀.im := hball u₀ hu₀b
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ w₀ hw₀ι)
  set t := c' ^ 2 * ι ^ 3 / 8 with htdef
  have ht : 0 < t := by positivity
  have hwt : ι ≤ (w₀ + t * I).im := by simp; linarith
  have hcross := pK_cross ν₁ ν₂ ha₁ ha₂ hι ht hw₀ι
  have hcross' : ‖pK ν₂ a₂ w₀ w₀ - pK ν₁ a₁ w₀ w₀‖ ≤ c' ^ 2 / 2 := by
    refine hcross.trans ?_
    have e1 : 2 * t / ι ^ 3 = c' ^ 2 / 4 := by rw [htdef]; field_simp; ring
    have e2 : (‖pT ν₂ a₂ w₀ - pT ν₁ a₁ w₀‖ + ‖pT ν₂ a₂ (w₀ + t * I) - pT ν₁ a₁ (w₀ + t * I)‖) / t
        ≤ c' ^ 2 / 4 := by
      rw [div_le_iff₀ ht]
      have := add_le_add (hδ w₀ hw₀ι) (hδ _ hwt)
      calc _ ≤ δ + δ := this
        _ ≤ c' ^ 4 * ι ^ 3 / 64 + c' ^ 4 * ι ^ 3 / 64 := by linarith
        _ = c' ^ 2 / 4 * t := by rw [htdef]; ring
    linarith
  have hK : ∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
      ‖pK ν₂ a₂ (z + β * u) (z + β * v) - pK ν₁ a₁ w₀ w₀‖ ≤ c' ^ 2 := by
    intro u hu v hv
    have hl := pK_lip ν₂ ha₂ hι (hball u hu) (hball v hv) hw₀ι hw₀ι
    have hdu : ‖z + β * u - w₀‖ ≤ r := by
      rw [hw₀, show z + β * u - (z + β * u₀) = β * (u - u₀) by ring, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg hβ.le]
      rw [Metric.mem_closedBall, dist_eq_norm] at hu
      nlinarith [norm_nonneg (u - u₀)]
    have hdv : ‖z + β * v - w₀‖ ≤ r := by
      rw [hw₀, show z + β * v - (z + β * u₀) = β * (v - u₀) by ring, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg hβ.le]
      rw [Metric.mem_closedBall, dist_eq_norm] at hv
      nlinarith [norm_nonneg (v - u₀)]
    have hl' : ‖pK ν₂ a₂ (z + β * u) (z + β * v) - pK ν₂ a₂ w₀ w₀‖ ≤ c' ^ 2 / 2 := by
      refine hl.trans ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc _ ≤ ‖pK ν₂ a₂ (z + β * u) (z + β * v) - pK ν₂ a₂ w₀ w₀‖ +
          ‖pK ν₂ a₂ w₀ w₀ - pK ν₁ a₁ w₀ w₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ c' ^ 2 / 2 + c' ^ 2 / 2 := add_le_add hl' hcross'
      _ = c' ^ 2 := by ring
  have hFd : ‖pT ν₂ a₂ w₀ - u₀‖ ≤ δ := by
    have := hδ w₀ hw₀ι
    rwa [← hroot] at this
  have hF : ‖pT ν₂ a₂ (z + β * u₀) - u₀‖ ≤ β * c' ^ 2 * r := by
    refine hFd.trans (hθ2.trans ?_)
    gcongr
  obtain ⟨u, hu1, hu2, hu3⟩ := root_perturb ν₁ ν₂ ha₁ ha₂ hβ hc' hr0.le (by linarith) hz hz hu₀
    hroot hK hF
  refine ⟨u, by linarith, hu2, hu3.trans ?_⟩
  calc ‖pT ν₂ a₂ (z + β * u₀) - u₀‖ / (β * c' ^ 2) ≤ δ / (β * c' ^ 2) := by gcongr
    _ ≤ δ / (β₀ * c' ^ 2) := by gcongr

/-- Lemma A.3 [bl:lem:finite], from the line to the cycle: near a line solution with
`Im ≥ c'` there is a finite-cycle solution, `e^{-cL}`-close ((A.10) [da:eq:finite-regularity]). -/
theorem finiteRoot_of_lineRoot (B β₀ c' : ℝ) (hB : 0 < B) (hβ₀ : 0 < β₀) (hc' : 0 < c') :
    ∃ c C' : ℝ, ∃ L₀ : ℕ, 0 < c ∧ 0 < C' ∧
      ∀ b : ℝ, 0 ≤ b → b ≤ B → ∀ β : ℝ, β₀ ≤ β → β ≤ 1 → ∀ L : ℕ, L₀ ≤ L →
      ∀ z : ℂ, 0 ≤ z.im → ∀ mInf : ℂ, 0 < mInf.im → mInf = freeT b (z + β * mInf) →
        c' ≤ mInf.im →
        ∃ m : ℂ, 0 < m.im ∧ m = freeTL b L (z + β * m) ∧ c' / 2 ≤ m.im ∧
          ‖m - mInf‖ ≤ C' * Real.exp (-(c * L)) := by
  set ι := β₀ * c' / 2 with hιdef
  have hι : 0 < ι := by positivity
  set q := 2 * B / (2 * B + ι) with hqdef
  obtain ⟨hq0, hq1⟩ := rate_pos hB hι
  set K₀ := 2 / (ι * (1 - q)) with hK₀def
  have hK₀ : 0 < K₀ := div_pos two_pos (mul_pos hι (by linarith))
  have hθ := tThr_pos hβ₀ hc'
  obtain ⟨L₁, hL₁⟩ := exists_pow_lt_of_lt_one (div_pos hθ hK₀) hq1
  refine ⟨-Real.log q, K₀ / (β₀ * c' ^ 2), max L₁ 1, neg_pos.mpr (Real.log_neg hq0 hq1),
    by positivity, ?_⟩
  intro b hb hbB β hβ₀β hβ1 L hL z hz mInf _ hroot hmc
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have := isProb_gridMeas hL1
  have hqL : K₀ * q ^ L ≤ tThr β₀ c' := by
    have h1 : q ^ L ≤ q ^ L₁ := pow_le_pow_of_le_one hq0.le hq1.le (le_trans (le_max_left _ _) hL)
    have h2 : K₀ * q ^ L₁ < tThr β₀ c' := by rwa [lt_div_iff₀' hK₀] at hL₁
    nlinarith
  have hdef : ∀ w : ℂ, β₀ * c' / 2 ≤ w.im →
      ‖pT (gridMeas L) (fun k : Fin L => 2 * b * Real.cos (2 * π * k / L)) w -
        pT lineMeas (fun p => 2 * b * Real.cos p) w‖ ≤ K₀ * q ^ L := by
    intro w hw
    rw [← freeT_eq_pT, ← freeTL_eq_pT]
    exact freeTL_defect hB hι hb hbB hL1 hw
  rw [freeT_eq_pT] at hroot
  obtain ⟨m, hmim, hmroot, hmd⟩ := root_transfer lineMeas (gridMeas L) (measurable_lineA b)
    (measurable_gridA b L) hβ₀ hc' hβ₀β hβ1 hdef hqL hz hmc hroot
  refine ⟨m, by linarith, by rw [freeTL_eq_pT]; exact hmroot, hmim, ?_⟩
  rw [← pow_eq_exp hq0]
  calc ‖m - mInf‖ ≤ K₀ * q ^ L / (β₀ * c' ^ 2) := hmd
    _ = K₀ / (β₀ * c' ^ 2) * q ^ L := by ring

/-! ### The finite-cycle boundary value at a root -/

/-- A solution of (5.2) [fo:eq:dyson-family] in `ℂ_+` at a real energy is the boundary value
`m_{g,L}(E)`, and `Im m_{g,L} ≥ Im m/2` on a box around `E` (every `L ≥ 1`). -/
theorem mDysonL_tendsto_root (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 1 ≤ L) (E : ℝ) (m : ℂ)
    (hm : 0 < m.im) (h : m = dysonRHSL g L E m) :
    Tendsto (fun η : ℝ => mDysonL g L (E + η * I)) (𝓝[>] 0) (𝓝 m) ∧
      mDysonLBdry g L E = m ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ E' ∈ Set.Ioo (E - δ) (E + δ), ∀ η ∈ Set.Ioc 0 δ,
        m.im / 2 ≤ (mDysonL g L (E' + η * I)).im := by
  have := isProb_gridMeas hL
  set β := gammaG g with hβdef
  have hβ : 0 < β := by
    rw [hβdef, gammaG]
    have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  have hβ1 : β ≤ 1 := by
    rw [hβdef, gammaG]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_max_left _ _))
  set a := fun k : Fin L => 2 * hopB g * Real.cos (2 * π * k / L) with hadef
  have ha : Measurable a := measurable_gridA (hopB g) L
  set c₀ := m.im with hc₀
  set ι := β * c₀ / 2 with hιdef
  have hι : 0 < ι := by positivity
  set r := min (c₀ / 2) (c₀ ^ 2 * ι ^ 3 / 4) with hrdef
  have hr0 : 0 < r := lt_min (by positivity) (by positivity)
  have hr1 : r ≤ c₀ / 2 := min_le_left _ _
  have hr2 : r ≤ c₀ ^ 2 * ι ^ 3 / 4 := min_le_right _ _
  set ρ₀ := min (c₀ ^ 2 * ι ^ 3 / 4) (β * c₀ ^ 2 * r * ι ^ 2) with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min (by positivity) (by positivity)
  have hρ₁ : ρ₀ ≤ c₀ ^ 2 * ι ^ 3 / 4 := min_le_left _ _
  have hρ₂ : ρ₀ ≤ β * c₀ ^ 2 * r * ι ^ 2 := min_le_right _ _
  set Cst := (ι ^ 2 * (β * c₀ ^ 2))⁻¹ with hCst
  have hCst0 : 0 < Cst := by positivity
  have hroot : m = pT (gridMeas L) a (E + β * m) := by
    rw [hadef, ← freeTL_eq_pT]; exact h
  -- the perturbed root near `E`
  have key : ∀ z : ℂ, 0 ≤ z.im → ‖z - E‖ ≤ ρ₀ → ∃ u : ℂ, c₀ / 2 ≤ u.im ∧
      u = pT (gridMeas L) a (z + β * u) ∧ ‖u - m‖ ≤ ‖z - E‖ * Cst := by
    intro z hz hzE
    have hball : ∀ u ∈ Metric.closedBall m r, ∀ z' : ℂ, 0 ≤ z'.im → ι ≤ (z' + β * u).im := by
      intro u hu z' hz'
      have := im_ge_of_mem_ball hu
      simp only [Complex.add_im, Complex.im_ofReal_mul]
      have h1 : c₀ / 2 ≤ u.im := by linarith
      have h2 : β * (c₀ / 2) ≤ β * u.im := mul_le_mul_of_nonneg_left h1 hβ.le
      rw [hιdef]; linarith
    have hmb : m ∈ Metric.closedBall m r := Metric.mem_closedBall_self hr0.le
    have hE0 : (0 : ℝ) ≤ (E : ℂ).im := by simp
    have hwE := hball m hmb E hE0
    have hdist : ∀ u ∈ Metric.closedBall m r, ‖z + β * u - (E + β * m)‖ ≤ ρ₀ + r := by
      intro u hu
      rw [show z + β * u - (E + β * m) = (z - E) + β * (u - m) by ring]
      refine (norm_add_le _ _).trans (add_le_add hzE ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ.le]
      rw [Metric.mem_closedBall, dist_eq_norm] at hu
      nlinarith [norm_nonneg (u - m)]
    have hK : ∀ u ∈ Metric.closedBall m r, ∀ v ∈ Metric.closedBall m r,
        ‖pK (gridMeas L) a (z + β * u) (z + β * v) -
          pK (gridMeas L) a (E + β * m) (E + β * m)‖ ≤ c₀ ^ 2 := by
      intro u hu v hv
      refine (pK_lip (gridMeas L) ha hι (hball u hu z hz) (hball v hv z hz) hwE hwE).trans ?_
      rw [div_le_iff₀ (by positivity)]
      have := add_le_add (hdist u hu) (hdist v hv)
      nlinarith
    have hzm := hball m hmb z hz
    have hF0 : ‖pT (gridMeas L) a (z + β * m) - m‖ ≤ ‖z - E‖ * (ι ^ 2)⁻¹ := by
      have hp : 0 < (z + β * m).im := lt_of_lt_of_le hι hzm
      have hpE : 0 < ((E : ℂ) + β * m).im := lt_of_lt_of_le hι hwE
      rw [show pT (gridMeas L) a (z + β * m) - m =
        pT (gridMeas L) a (z + β * m) - pT (gridMeas L) a (E + β * m) by rw [← hroot]]
      rw [pT_sub (gridMeas L) ha hp hpE, show z + β * m - (E + β * m) = z - E by ring, norm_mul]
      gcongr
      refine (norm_pK_le (gridMeas L) hp hpE).trans ?_
      rw [sq, mul_inv]
      exact mul_le_mul (inv_anti₀ hι hzm) (inv_anti₀ hι hwE) (inv_nonneg.mpr hpE.le)
        (inv_nonneg.mpr hι.le)
    have hF : ‖pT (gridMeas L) a (z + β * m) - m‖ ≤ β * c₀ ^ 2 * r := by
      refine hF0.trans ?_
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      linarith
    obtain ⟨u, hu1, hu2, hu3⟩ := root_perturb (gridMeas L) (gridMeas L) ha ha hβ hm hr0.le
      (by linarith) hE0 hz le_rfl hroot hK hF
    refine ⟨u, by linarith, hu2, hu3.trans ?_⟩
    rw [div_le_iff₀ (by positivity)]
    calc ‖pT (gridMeas L) a (z + β * m) - m‖ ≤ ‖z - E‖ * (ι ^ 2)⁻¹ := hF0
      _ = ‖z - E‖ * Cst * (β * c₀ ^ 2) := by rw [hCst]; field_simp
  -- identification with `m_{g,L}` on `ℂ_+`
  have hid : ∀ z : ℂ, 0 < z.im → ‖z - E‖ ≤ ρ₀ →
      c₀ / 2 ≤ (mDysonL g L z).im ∧ ‖mDysonL g L z - m‖ ≤ ‖z - E‖ * Cst := by
    intro z hz hzE
    obtain ⟨u, hu1, hu2, hu3⟩ := key z hz.le hzE
    have hupos : 0 < u.im := lt_of_lt_of_le (by positivity) hu1
    have hu' : u = dysonRHSL g L z u := by
      rw [dysonRHSL, freeTL_eq_pT]; exact hu2
    have e := mDysonL_unique g hg L hL z hz u hupos hu'
    rw [← e]
    exact ⟨hu1, hu3⟩
  have hnormη : ∀ E' η : ℝ, 0 ≤ η → ‖((E' : ℂ) + η * I) - E‖ ≤ |E' - E| + η := by
    intro E' η hη
    rw [show ((E' : ℂ) + η * I) - E = ((E' - E : ℝ) : ℂ) + η * I by push_cast; ring]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_of_nonneg hη]
  have hT : Tendsto (fun η : ℝ => mDysonL g L (E + η * I)) (𝓝[>] 0) (𝓝 m) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
      (g := fun η => η * Cst)
    · filter_upwards [Ioo_mem_nhdsGT hρ₀] with η hη
      have hz : 0 < ((E : ℂ) + η * I).im := by simpa using hη.1
      have hn := hnormη E η hη.1.le
      rw [sub_self, abs_zero, zero_add] at hn
      have := (hid _ hz (hn.trans hη.2.le)).2
      exact this.trans (by gcongr)
    · have hc : Continuous fun η : ℝ => η * Cst := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
  refine ⟨hT, hT.limUnder_eq, ρ₀ / 2, by positivity, ?_⟩
  intro E' hE' η hη
  have hz : 0 < ((E' : ℂ) + η * I).im := by simpa using hη.1
  have hn := hnormη E' η hη.1.le
  have habs : |E' - E| < ρ₀ / 2 := abs_lt.mpr ⟨by linarith [hE'.1], by linarith [hE'.2]⟩
  exact (hid _ hz (hn.trans (by linarith [hη.2]))).1

end LSBA
