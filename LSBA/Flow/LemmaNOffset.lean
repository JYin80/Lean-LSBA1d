import LSBA.Flow.SurrField
import LSBA.Prop.Inputs
import LSBA.Prop.Domination
import LSBA.Flow.Comparison

/-!
# The off-set bound for the mixed-pair bound

The off-set term of the no-exit lemma by Cauchy–Schwarz, `E|f| 1_B ≤ ‖f‖₂ ℙ(B)^{1/2}`, the `L²`
bound of the generator of the cutoffs of the surrogate, and the moments of the generator and carré
du champ of the mixed-pair loops from the crude moments of the inputs.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Off-set term by Cauchy–Schwarz: `E|f| 1_B ≤ ‖f‖₂ ℙ(B)^{1/2}`. -/
theorem lemmaNOffset_cs {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] (f : Ω' → ℝ) (hf : MemLp f 2 P) {B : Set Ω'} (hB : MeasurableSet B)
    {K δ : ℝ} (hK : 0 ≤ K) (hfK : ∫ x, f x ^ 2 ∂P ≤ K ^ 2) (hδ : P.real B ≤ δ) :
    ∫ x, B.indicator (fun x => |f x|) x ∂P ≤ K * Real.sqrt δ := by
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have hind : ∀ x, B.indicator (fun x => |f x|) x = B.indicator (fun _ => (1 : ℝ)) x * |f x| := by
    intro x
    by_cases hx : x ∈ B <;> simp [hx]
  simp_rw [hind]
  have hm1 : MemLp (B.indicator (fun _ => (1 : ℝ))) (ENNReal.ofReal 2) P := by
    rw [h2]
    exact memLp_indicator_const 2 hB.nullMeasurableSet 1 (Or.inr (measure_ne_top P B))
  have hm2 : MemLp (fun x => |f x|) (ENNReal.ofReal 2) P := by
    rw [h2]
    simpa [Real.norm_eq_abs] using hf.norm
  have hC := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := B.indicator (fun _ => (1 : ℝ))) (g := fun x => |f x|)
    (Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ B <;> simp [hx])
    (Filter.Eventually.of_forall fun x => abs_nonneg _) hm1 hm2
  have e1 : ∫ x, (B.indicator (fun _ => (1 : ℝ)) x) ^ (2 : ℝ) ∂P = P.real B := by
    have : ∀ x, (B.indicator (fun _ => (1 : ℝ)) x) ^ (2 : ℝ) =
        B.indicator (fun _ => (1 : ℝ)) x := by
      intro x
      by_cases hx : x ∈ B <;> simp [hx]
    simp_rw [this]
    exact integral_indicator_one hB
  have e2 : ∫ x, (|f x|) ^ (2 : ℝ) ∂P = ∫ x, f x ^ 2 ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.rpow_two, sq_abs]
  rw [e1, e2] at hC
  refine hC.trans ?_
  have hI0 : 0 ≤ ∫ x, f x ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
  have hP0 : 0 ≤ P.real B := measureReal_nonneg
  have hd0 : 0 ≤ δ := hP0.trans hδ
  calc (P.real B) ^ (1 / (2 : ℝ)) * (∫ x, f x ^ 2 ∂P) ^ (1 / (2 : ℝ))
      ≤ δ ^ (1 / (2 : ℝ)) * (K ^ 2) ^ (1 / (2 : ℝ)) := by
        gcongr
    _ = K * Real.sqrt δ := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq hK, mul_comm]

/-- The maximum of a finite family in `L²` from `L^p` moments, `p ≥ 2`, with integrability of the
square. -/
private theorem lemmaNOffset_max_aux {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {S : Type*} [Fintype S] (Y : S → Ω' → ℝ)
    (hY : ∀ s, AEStronglyMeasurable (Y s) P) (hY0 : ∀ s x, 0 ≤ Y s x) (p : ℕ) (hp : 2 ≤ p)
    {B : ℝ} (hB : 0 ≤ B) (hmom : ∀ s, Integrable (fun x => Y s x ^ p) P ∧ ∫ x, Y s x ^ p ∂P ≤ B ^ p) :
    Integrable (fun x => (⨆ s, Y s x) ^ 2) P ∧
      ∫ x, (⨆ s, Y s x) ^ 2 ∂P ≤ (Fintype.card S : ℝ) ^ ((2 : ℝ) / p) * B ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rcases isEmpty_or_nonempty S with hS | hS
  · have h0 : ∀ x, (⨆ s, Y s x) = 0 := fun x => Real.iSup_of_isEmpty _
    simp only [h0]
    have hc : (Fintype.card S : ℝ) = 0 := by simp
    rw [hc, Real.zero_rpow (by positivity)]
    simp
  set M : Ω' → ℝ := fun x => ⨆ s, Y s x with hMdef
  have hM0 : ∀ x, 0 ≤ M x := fun x => Real.iSup_nonneg fun s => hY0 s x
  have hMex : ∀ x, ∃ s, M x = Y s x := fun x => by
    obtain ⟨s, hs⟩ := exists_eq_ciSup_of_finite (f := fun s => Y s x)
    exact ⟨s, hs.symm⟩
  have hMp : ∀ x, M x ^ p ≤ ∑ s, Y s x ^ p := by
    intro x
    obtain ⟨s, hs⟩ := hMex x
    rw [hs]
    exact Finset.single_le_sum (f := fun s => Y s x ^ p) (fun s _ => pow_nonneg (hY0 s x) p)
      (Finset.mem_univ s)
  have hMmeas : AEStronglyMeasurable M P :=
    (AEMeasurable.iSup (fun s => (hY s).aemeasurable)).aestronglyMeasurable
  have hMpint : Integrable (fun x => M x ^ p) P := by
    refine Integrable.mono' (integrable_finsetSum Finset.univ fun s _ => (hmom s).1) (hMmeas.pow p)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (hM0 x) p)]
    exact hMp x
  have hMsq : Integrable (fun x => M x ^ 2) P := by
    refine Integrable.mono' (hMpint.add (integrable_const (1 : ℝ))) (hMmeas.pow 2)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (hM0 x) 2)]
    change M x ^ 2 ≤ M x ^ p + 1
    rcases le_total (M x) 1 with h | h
    · have : M x ^ 2 ≤ 1 := pow_le_one₀ (hM0 x) h
      have := pow_nonneg (hM0 x) p
      linarith
    · have : M x ^ 2 ≤ M x ^ p := pow_le_pow_right₀ h hp
      linarith
  refine ⟨hMsq, ?_⟩
  have hint_p : ∫ x, M x ^ p ∂P ≤ (Fintype.card S : ℝ) * B ^ p := by
    calc ∫ x, M x ^ p ∂P ≤ ∫ x, ∑ s, Y s x ^ p ∂P :=
          integral_mono hMpint (integrable_finsetSum Finset.univ fun s _ => (hmom s).1) hMp
      _ = ∑ s, ∫ x, Y s x ^ p ∂P := integral_finsetSum Finset.univ fun s _ => (hmom s).1
      _ ≤ ∑ _s : S, B ^ p := Finset.sum_le_sum fun s _ => (hmom s).2
      _ = (Fintype.card S : ℝ) * B ^ p := by simp
  -- Jensen for `t ↦ t^(p/2)`
  have hq1 : (1 : ℝ) ≤ (p : ℝ) / 2 := by linarith
  have hconv := convexOn_rpow hq1
  have hcomp : ∀ x, (M x ^ 2) ^ ((p : ℝ) / 2) = M x ^ p := by
    intro x
    rw [← Real.rpow_natCast (M x) 2, ← Real.rpow_mul (hM0 x), ← Real.rpow_natCast (M x) p]
    congr 1
    push_cast
    ring
  have hJ := ConvexOn.map_integral_le (μ := P) (f := fun x => M x ^ 2)
    (g := fun t : ℝ => t ^ ((p : ℝ) / 2)) hconv
    ((Real.continuous_rpow_const (by positivity)).continuousOn) isClosed_Ici
    (Filter.Eventually.of_forall fun x => (sq_nonneg (M x) : (0 : ℝ) ≤ M x ^ 2))
    hMsq (by
      have : (fun t : ℝ => t ^ ((p : ℝ) / 2)) ∘ (fun x => M x ^ 2) = fun x => M x ^ p :=
        funext hcomp
      rw [this]; exact hMpint)
  simp only [hcomp] at hJ
  have hI0 : 0 ≤ ∫ x, M x ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
  have hcard0 : (0 : ℝ) ≤ Fintype.card S := Nat.cast_nonneg _
  have h1 : ∫ x, M x ^ 2 ∂P ≤ ((Fintype.card S : ℝ) * B ^ p) ^ ((2 : ℝ) / p) := by
    have hJ' : (∫ x, M x ^ 2 ∂P) ^ ((p : ℝ) / 2) ≤ (Fintype.card S : ℝ) * B ^ p :=
      hJ.trans hint_p
    have := Real.rpow_le_rpow (by positivity) hJ' (by positivity : (0 : ℝ) ≤ 2 / p)
    rwa [← Real.rpow_mul hI0, show (p : ℝ) / 2 * (2 / p) = 1 by field_simp, Real.rpow_one] at this
  refine h1.trans (le_of_eq ?_)
  rw [Real.mul_rpow hcard0 (pow_nonneg hB p), ← Real.rpow_natCast B p, ← Real.rpow_mul hB,
    show (p : ℝ) * (2 / p) = 2 by field_simp]
  norm_num

/-- `Γ(F, F)` is the real number `σ² Σ_i ‖∂_i F‖²`. -/
private theorem lemmaNOffset_gamma_eq {ι : Type*} [Fintype ι] (σ2 : ℝ) (F : (ι → ℝ) → ℂ)
    (y : ι → ℝ) :
    coordGamma σ2 F F y =
      ((σ2 * ∑ i, ‖deriv (fun e : ℝ => F (y + e • Pi.single i 1)) 0‖ ^ 2 : ℝ) : ℂ) := by
  simp only [coordGamma, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- `Re Γ(F, F) ≥ 0` for `σ² ≥ 0`. -/
private theorem lemmaNOffset_gamma_re_nonneg {ι : Type*} [Fintype ι] {σ2 : ℝ} (hσ2 : 0 ≤ σ2)
    (F : (ι → ℝ) → ℂ) (y : ι → ℝ) : 0 ≤ (coordGamma σ2 F F y).re := by
  rw [lemmaNOffset_gamma_eq, Complex.ofReal_re]
  exact mul_nonneg hσ2 (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- Along a line, `e ↦ G(y + e v)` has first derivative `DG(y) v` at `0`. -/
private theorem lemmaNOffset_deriv_line {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℂ}
    {DG : (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℂ)} (hD : ∀ x, HasFDerivAt G (DG x) x) (y v : ι → ℝ) :
    deriv (fun e : ℝ => G (y + e • v)) 0 = DG y v := by
  have hl : HasDerivAt (fun e : ℝ => y + e • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have h := ((hD (y + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) hl)
  have h2 : HasDerivAt (fun e : ℝ => G (y + e • v)) (DG y v) 0 := by
    simpa [Function.comp_def] using h
  exact h2.deriv

/-- Along a line, `e ↦ G(y + e v)` has second derivative `D²G(y) v v` at `0`, when `G` has
derivative `DG` and `DG` has derivative `D²G` everywhere. -/
private theorem lemmaNOffset_iteratedDeriv_line {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℂ}
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

/-- A function jointly continuous on `(a,b) × ℝ^ι` is continuous in `x` at each time in `(a,b)`. -/
private theorem lemmaNOffset_slice {ι E : Type*} [TopologicalSpace E] {g : ℝ → (ι → ℝ) → E}
    {a b : ℝ} (hg : ContinuousOn (Function.uncurry g) (Set.Ioo a b ×ˢ Set.univ)) {r : ℝ}
    (hr : r ∈ Set.Ioo a b) : Continuous (g r) :=
  hg.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hr, trivial⟩

/-- Jet data of a member of the class at a time `u ∈ (a,b)`: differentiability in time, `C²`
regularity in space, and continuity and boundedness of `F u`, `𝒢F u`, `Γ(F u, F u)`. -/
private theorem lemmaNOffset_class_jet {ι : Type*} [Fintype ι] {F : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (hF : HeatClass F a b) {u : ℝ} (hu : u ∈ Set.Ioo a b) (σ2 : ℝ) :
    (∀ y, DifferentiableAt ℝ (fun r => F r y) u) ∧ ContDiff ℝ 2 (F u) ∧
      (∃ C : ℝ, ∀ y, ‖F u y‖ ≤ C) ∧
      (Continuous (coordGen σ2 F u) ∧ ∃ C : ℝ, ∀ y, ‖coordGen σ2 F u y‖ ≤ C) ∧
      (Continuous (coordGamma σ2 (F u) (F u)) ∧
        ∃ C : ℝ, ∀ y, ‖coordGamma σ2 (F u) (F u) y‖ ≤ C) := by
  obtain ⟨hc, ⟨C₀, hC₀⟩, ⟨Fu, hu', hcu, C₁, hC₁⟩, ⟨DF, D2F, hD, hD2, hcD, hcD2, C₂, hC₂⟩⟩ := hF
  have hei : ∀ i : ι, ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ ≤ 1 := fun i => by
    rw [Pi.norm_single]; simp
  have hDc : Continuous (DF u) := lemmaNOffset_slice hcD hu
  have hD2c : Continuous (D2F u) := lemmaNOffset_slice hcD2 hu
  have hFuc : Continuous (Fu u) := lemmaNOffset_slice hcu hu
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (hC₂ u hu 0).1
  have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ u hu 0)
  have hb1 : ∀ (y : ι → ℝ) (i : ι), ‖DF u y (Pi.single i 1)‖ ≤ C₂ := fun y i =>
    calc ‖DF u y (Pi.single i 1)‖ ≤ ‖DF u y‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ :=
          (DF u y).le_opNorm _
      _ ≤ C₂ * 1 := mul_le_mul (hC₂ u hu y).1 (hei i) (norm_nonneg _) hC₂0
      _ = C₂ := mul_one _
  have hb2 : ∀ (y : ι → ℝ) (i : ι), ‖D2F u y (Pi.single i 1) (Pi.single i 1)‖ ≤ C₂ := fun y i =>
    calc ‖D2F u y (Pi.single i 1) (Pi.single i 1)‖
        ≤ ‖D2F u y (Pi.single i 1)‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ := (D2F u y _).le_opNorm _
      _ ≤ (‖D2F u y‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖) * 1 :=
          mul_le_mul ((D2F u y).le_opNorm _) (hei i) (norm_nonneg _) (by positivity)
      _ ≤ (C₂ * 1) * 1 := by
          gcongr
          · exact (hC₂ u hu y).2
          · exact hei i
      _ = C₂ := by ring
  have hgen : ∀ y, coordGen σ2 F u y =
      Fu u y + ((σ2 / 2 : ℝ) : ℂ) * ∑ i, D2F u y (Pi.single i 1) (Pi.single i 1) := by
    intro y
    simp only [coordGen, (hu' u hu y).deriv]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    exact lemmaNOffset_iteratedDeriv_line (hD u hu) (hD2 u hu) y _
  have hgam : ∀ y, coordGamma σ2 (F u) (F u) y =
      (σ2 : ℂ) * ∑ i, DF u y (Pi.single i 1) * star (DF u y (Pi.single i 1)) := by
    intro y
    simp only [coordGamma, lemmaNOffset_deriv_line (hD u hu)]
  have hFdiff : Differentiable ℝ (F u) := fun x => (hD u hu x).differentiableAt
  have hDdiff : Differentiable ℝ (DF u) := fun x => (hD2 u hu x).differentiableAt
  refine ⟨fun y => (hu' u hu y).differentiableAt, ?_, ⟨C₀, fun y => hC₀ u hu y⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
    refine ⟨hFdiff, by simp, ?_⟩
    have hfd : fderiv ℝ (F u) = DF u := funext fun x => (hD u hu x).fderiv
    rw [hfd, contDiff_one_iff_fderiv]
    refine ⟨hDdiff, ?_⟩
    have : fderiv ℝ (DF u) = D2F u := funext fun x => (hD2 u hu x).fderiv
    rw [this]; exact hD2c
  · have : coordGen σ2 F u = fun y => Fu u y + ((σ2 / 2 : ℝ) : ℂ) *
        ∑ i, D2F u y (Pi.single i 1) (Pi.single i 1) := funext hgen
    rw [this]
    refine hFuc.add (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_))
    exact (hD2c.clm_apply continuous_const).clm_apply continuous_const
  · refine ⟨C₁ + |σ2 / 2| * (Fintype.card ι * C₂), fun y => ?_⟩
    rw [hgen]
    refine (norm_add_le _ _).trans (add_le_add (hC₁ u hu y) ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖D2F u y (Pi.single i 1) (Pi.single i 1)‖ ≤ ∑ _i : ι, C₂ :=
          Finset.sum_le_sum fun i _ => hb2 y i
      _ = Fintype.card ι * C₂ := by simp
  · have : coordGamma σ2 (F u) (F u) = fun y => (σ2 : ℂ) *
        ∑ i, DF u y (Pi.single i 1) * star (DF u y (Pi.single i 1)) := funext hgam
    rw [this]
    refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
    exact (hDc.clm_apply continuous_const).mul
      (continuous_star.comp (hDc.clm_apply continuous_const))
  · refine ⟨|σ2| * (Fintype.card ι * (C₂ * C₂)), fun y => ?_⟩
    rw [hgam, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖DF u y (Pi.single i 1) * star (DF u y (Pi.single i 1))‖ ≤ ∑ _i : ι, C₂ * C₂ :=
          Finset.sum_le_sum fun i _ => by
            rw [norm_mul, norm_star]
            exact mul_le_mul (hb1 y i) (hb1 y i) (norm_nonneg _) hC₂0
      _ = Fintype.card ι * (C₂ * C₂) := by simp


/-- The surrogate with floor `δ > 0` is at least `δ` when the family is nonempty. -/
private theorem lemmaNOffset_lqSurr_ge {S : Type*} [Fintype S] [Nonempty S] {q : ℕ} (hq : 1 ≤ q)
    {env : S → ℝ} (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ) (y : S → ℂ) :
    δ ≤ lqSurr q env δ y := by
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hq0 : (2 * q : ℕ) ≠ 0 := by omega
  have h1 : δ ^ (2 * q) ≤ ∑ s, (‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2) ^ q := by
    calc δ ^ (2 * q) = (δ ^ 2) ^ q := by rw [pow_mul]
      _ ≤ (‖y s₀‖ ^ 2 / env s₀ ^ 2 + δ ^ 2) ^ q := by
          have := henv s₀
          gcongr
          exact le_add_of_nonneg_left (by positivity)
      _ ≤ _ := Finset.single_le_sum (f := fun s => (‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2) ^ q)
          (fun s _ => by have := henv s; positivity) (Finset.mem_univ s₀)
  have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ 1 / (2 * q))
  have h3 : (δ ^ (2 * q)) ^ ((1 : ℝ) / (2 * q)) = δ := by
    have := Real.pow_rpow_inv_natCast hδ.le hq0
    push_cast at this
    rwa [one_div]
  rw [h3] at h2
  exact h2

/-- Pointwise bound of the generator of the cutoff of the surrogate: `|Re 𝒢(φ ∘ X)| ≤
C_φ (q + 2) |S|^{1/q} T` with `T = max_s (|𝒢Y_s|/env_s + Re Γ(Y_s)/env_s²)`. -/
private theorem lemmaNOffset_pointwise {ι S : Type*} [Fintype ι] [Fintype S] (σ2 : ℝ)
    (hσ2 : 0 ≤ σ2) {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ} (henv : ∀ s, 0 < env s) {δ : ℝ}
    (hδ : 1 ≤ δ) (Y : S → ℝ → (ι → ℝ) → ℂ) (u : ℝ) (y : ι → ℝ)
    (hYu : ∀ s, DifferentiableAt ℝ (fun r => Y s r y) u) (hYy : ∀ s, ContDiff ℝ 2 (Y s u))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) {Cφ : ℝ}
    (hCφ : ∀ x, |deriv φ x| ≤ Cφ ∧ |iteratedDeriv 2 φ x| ≤ Cφ) :
    |(coordGen σ2 (fun r z => ((φ (lqSurr q env δ (fun s => Y s r z)) : ℝ) : ℂ)) u y).re| ≤
      Cφ * (q + 2) * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) *
        ⨆ s, (‖coordGen σ2 (Y s) u y‖ / env s +
          (coordGamma σ2 (Y s u) (Y s u) y).re / env s ^ 2) := by
  have hδ0 : 0 < δ := by linarith
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hCφ0 : 0 ≤ Cφ := (abs_nonneg _).trans (hCφ 0).1
  set T : ℝ := ⨆ s, (‖coordGen σ2 (Y s) u y‖ / env s +
    (coordGamma σ2 (Y s u) (Y s u) y).re / env s ^ 2) with hTdef
  have ha : ∀ s, 0 ≤ ‖coordGen σ2 (Y s) u y‖ / env s := fun s => by
    have := henv s; positivity
  have hb : ∀ s, 0 ≤ (coordGamma σ2 (Y s u) (Y s u) y).re / env s ^ 2 := fun s =>
    div_nonneg (lemmaNOffset_gamma_re_nonneg hσ2 _ _) (by have := henv s; positivity)
  have hle : ∀ s, ‖coordGen σ2 (Y s) u y‖ / env s +
      (coordGamma σ2 (Y s u) (Y s u) y).re / env s ^ 2 ≤ T := fun s =>
    le_ciSup (f := fun s => ‖coordGen σ2 (Y s) u y‖ / env s +
      (coordGamma σ2 (Y s u) (Y s u) y).re / env s ^ 2) (Set.finite_range _).bddAbove s
  have hT0 : 0 ≤ T := Real.iSup_nonneg fun s => add_nonneg (ha s) (hb s)
  have hlq := coordGen_lqSurr_le σ2 hσ2 hq henv hδ0 Y u y hYu hYy (κ₁ := T) (h := T)
    (fun s => by linarith [hle s, hb s]) (fun s => by linarith [hle s, ha s])
  obtain ⟨hA, hΓ⟩ := hlq
  have hΦ := lqSurr_contDiff hq henv hδ0
  have hXu : DifferentiableAt ℝ (fun r => lqSurr q env δ (fun s => Y s r y)) u :=
    ((hΦ.differentiable (by norm_num)) _).comp u (differentiableAt_pi.2 hYu)
  have hXy : ContDiff ℝ 2 (fun z => lqSurr q env δ (fun s => Y s u z)) :=
    hΦ.comp (contDiff_pi.2 hYy)
  have hcomp := coordGen_comp σ2 φ hφ (fun r z => lqSurr q env δ (fun s => Y s r z)) u y hXu hXy
  rw [hcomp, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  set X := lqSurr q env δ (fun s => Y s u y) with hX
  set c1 := (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) with hc1
  set c2 := (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) with hc2
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have hc12 : c1 ≤ c2 := by
    rcases isEmpty_or_nonempty S with hS | hS
    · have : (Fintype.card S : ℝ) = 0 := by simp
      rw [hc1, hc2, this, Real.zero_rpow (by positivity), Real.zero_rpow (by positivity)]
    · have hcard : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
      refine Real.rpow_le_rpow_of_exponent_le hcard ?_
      rw [div_le_div_iff₀ (by positivity) hqpos]
      nlinarith
  have hXq : q * c2 * T / X ≤ q * c2 * T := by
    rcases isEmpty_or_nonempty S with hS | hS
    · have : c2 = 0 := by
        rw [hc2, show (Fintype.card S : ℝ) = 0 by simp, Real.zero_rpow (by positivity)]
      rw [this]; simp
    · refine div_le_self (by positivity) ?_
      exact (hδ).trans (lemmaNOffset_lqSurr_ge hq henv hδ0 _)
  have hG0 : 0 ≤ (coordGamma σ2 (fun z => ((lqSurr q env δ (fun s => Y s u z) : ℝ) : ℂ))
      (fun z => ((lqSurr q env δ (fun s => Y s u z) : ℝ) : ℂ)) y).re :=
    lemmaNOffset_gamma_re_nonneg hσ2 _ _
  set A := (coordGen σ2 (fun r z => ((lqSurr q env δ (fun s => Y s r z) : ℝ) : ℂ)) u y).re
    with hAdef
  set Γ := (coordGamma σ2 (fun z => ((lqSurr q env δ (fun s => Y s u z) : ℝ) : ℂ))
    (fun z => ((lqSurr q env δ (fun s => Y s u z) : ℝ) : ℂ)) y).re with hΓdef
  have h1 : |deriv φ X * A| ≤ Cφ * (c1 * T + q * c2 * T) := by
    rw [abs_mul]
    refine mul_le_mul (hCφ X).1 ?_ (abs_nonneg _) hCφ0
    exact hA.trans (add_le_add le_rfl hXq)
  have h2 : |iteratedDeriv 2 φ X / 2 * Γ| ≤ Cφ / 2 * (c2 * T) := by
    rw [abs_mul, abs_div, abs_two, abs_of_nonneg hG0]
    refine mul_le_mul (div_le_div_of_nonneg_right (hCφ X).2 (by norm_num)) ?_ hG0
      (by positivity)
    exact hΓ
  calc |deriv φ X * A + iteratedDeriv 2 φ X / 2 * Γ|
      ≤ |deriv φ X * A| + |iteratedDeriv 2 φ X / 2 * Γ| := abs_add_le _ _
    _ ≤ Cφ * (c1 * T + q * c2 * T) + Cφ / 2 * (c2 * T) := add_le_add h1 h2
    _ ≤ Cφ * (q + 2) * c2 * T := by
        have : c1 * T ≤ c2 * T := mul_le_mul_of_nonneg_right hc12 hT0
        have h3 : 0 ≤ c2 * T := mul_nonneg hc20 hT0
        nlinarith [mul_nonneg hCφ0 h3, mul_nonneg hCφ0 (sub_nonneg.2 this)]

/-- `L²` bound of `Re 𝒢(φ ∘ X)` for the surrogate `X = lqSurr q env δ Y` with floor `δ ≥ 1`,
from `L^p` moments of `|𝒢Y_s|/env_s + Re Γ(Y_s)/env_s²`, `p ≥ 2`. -/
theorem lemmaNOffset_L2 {ι S : Type*} [Fintype ι] [Fintype S] (σ2 : ℝ) (hσ2 : 0 ≤ σ2) {q : ℕ}
    (hq : 1 ≤ q) {env : S → ℝ} (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 1 ≤ δ)
    (Y : S → ℝ → (ι → ℝ) → ℂ) {a b u : ℝ} (hY : ∀ s, HeatClass (Y s) a b) (hu : u ∈ Set.Ioo a b)
    (φ : ℝ → ℝ) (hφ : C2b φ) {Cφ : ℝ} (hCφ : ∀ x, |deriv φ x| ≤ Cφ ∧ |iteratedDeriv 2 φ x| ≤ Cφ)
    (p : ℕ) (hp : 2 ≤ p) {B : ℝ} (hB : 0 ≤ B)
    (hmom : ∀ s, Integrable (fun x : ι → ℝ =>
        (‖coordGen σ2 (Y s) u (Real.sqrt (u * σ2) • x)‖ / env s +
          (coordGamma σ2 (Y s u) (Y s u) (Real.sqrt (u * σ2) • x)).re / env s ^ 2) ^ p)
        (stdGauss ι) ∧
      ∫ x, (‖coordGen σ2 (Y s) u (Real.sqrt (u * σ2) • x)‖ / env s +
          (coordGamma σ2 (Y s u) (Y s u) (Real.sqrt (u * σ2) • x)).re / env s ^ 2) ^ p
        ∂(stdGauss ι) ≤ B ^ p) :
    MemLp (fun x => (coordGen σ2 (fun r z => ((φ (lqSurr q env δ (fun s => Y s r z)) : ℝ) : ℂ)) u
        (Real.sqrt (u * σ2) • x)).re) 2 (stdGauss ι) ∧
      ∫ x, ((coordGen σ2 (fun r z => ((φ (lqSurr q env δ (fun s => Y s r z)) : ℝ) : ℂ)) u
          (Real.sqrt (u * σ2) • x)).re) ^ 2 ∂(stdGauss ι) ≤
        (Cφ * (q + 2) * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q)) ^ 2 *
          (Fintype.card S : ℝ) ^ ((2 : ℝ) / p) * B ^ 2 := by
  have hδ0 : 0 < δ := by linarith
  have hCφ0 : 0 ≤ Cφ := (abs_nonneg _).trans (hCφ 0).1
  set Fφ : ℝ → (ι → ℝ) → ℂ := fun r z => ((φ (lqSurr q env δ (fun s => Y s r z)) : ℝ) : ℂ)
    with hFφ
  have hX : HeatClass (fun r y => ((lqSurr q env δ (fun s => Y s r y) : ℝ) : ℂ)) a b :=
    heatClass_lqSurr hq henv hδ0 Y hY
  have hF : HeatClass Fφ a b := HeatClass.comp_real hX hφ
  set yy : (ι → ℝ) → (ι → ℝ) := fun x => Real.sqrt (u * σ2) • x with hyy
  have hy : Continuous yy := by
    change Continuous (fun x : ι → ℝ => Real.sqrt (u * σ2) • x)
    fun_prop
  set Y' : S → (ι → ℝ) → ℝ := fun s x => ‖coordGen σ2 (Y s) u (yy x)‖ / env s +
    (coordGamma σ2 (Y s u) (Y s u) (yy x)).re / env s ^ 2 with hY'
  have hjet := fun s => lemmaNOffset_class_jet (hY s) hu σ2
  have hY'cont : ∀ s, Continuous (Y' s) := fun s =>
    (((hjet s).2.2.2.1.1.comp hy).norm.div_const _).add
      ((Complex.continuous_re.comp ((hjet s).2.2.2.2.1.comp hy)).div_const _)
  have hY'0 : ∀ s x, 0 ≤ Y' s x := fun s x => by
    have := henv s
    exact add_nonneg (by positivity)
      (div_nonneg (lemmaNOffset_gamma_re_nonneg hσ2 _ _) (by positivity))
  obtain ⟨hTint, hTbd⟩ := lemmaNOffset_max_aux (stdGauss ι) Y'
    (fun s => (hY'cont s).aestronglyMeasurable) hY'0 p hp hB hmom
  set K₂ : ℝ := Cφ * (q + 2) * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) with hK₂
  have hpt : ∀ x, |(coordGen σ2 Fφ u (yy x)).re| ≤ K₂ * ⨆ s, Y' s x := fun x =>
    lemmaNOffset_pointwise σ2 hσ2 hq henv hδ Y u (yy x) (fun s => (hjet s).1 _)
      (fun s => (hjet s).2.1) φ hφ.1 hCφ
  obtain ⟨-, -, -, ⟨hgcF, C, hC⟩, -⟩ := lemmaNOffset_class_jet hF hu σ2
  have hfc : Continuous (fun x => (coordGen σ2 Fφ u (yy x)).re) :=
    Complex.continuous_re.comp (hgcF.comp hy)
  refine ⟨MemLp.of_bound hfc.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => ?_), ?_⟩
  · exact (Complex.abs_re_le_norm _).trans (hC _)
  · have hK0 : 0 ≤ K₂ := by positivity
    calc ∫ x, ((coordGen σ2 Fφ u (yy x)).re) ^ 2 ∂(stdGauss ι)
        ≤ ∫ x, K₂ ^ 2 * (⨆ s, Y' s x) ^ 2 ∂(stdGauss ι) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
            (hTint.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
          calc ((coordGen σ2 Fφ u (yy x)).re) ^ 2 = |(coordGen σ2 Fφ u (yy x)).re| ^ 2 :=
                (sq_abs _).symm
            _ ≤ (K₂ * ⨆ s, Y' s x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hpt x) 2
            _ = _ := mul_pow _ _ _
      _ = K₂ ^ 2 * ∫ x, (⨆ s, Y' s x) ^ 2 ∂(stdGauss ι) := integral_const_mul _ _
      _ ≤ K₂ ^ 2 * ((Fintype.card S : ℝ) ^ ((2 : ℝ) / p) * B ^ 2) :=
          mul_le_mul_of_nonneg_left hTbd (sq_nonneg _)
      _ = K₂ ^ 2 * (Fintype.card S : ℝ) ^ ((2 : ℝ) / p) * B ^ 2 := by ring

/-! ### Entry bounds for loops -/

section LoopEntry

variable {W L : ℕ}

/-- The number of sites in a block: `∑_{r} 1_{r.1 = a} f = W f`. -/
private lemma lemmaNOffset_sum_block (a : Fin L) (f : ℝ) :
    ∑ r : Fin L × Fin W, (if r.1 = a then f else 0) = (W : ℝ) * f := by
  rw [Fintype.sum_prod_type]
  have h : ∀ x : Fin L, ∑ _y : Fin W, (if x = a then f else 0) =
      if x = a then (W : ℝ) * f else 0 := fun x => by split_ifs <;> simp
  simp only [h]
  simp

/-- Bounds on the entries of a product of loop factors `S_i E_{a_i}`: supported on the columns of
block `a`, with entries on rows of the labels `Lab` at most `B / W`. -/
private def LoopBd (Lab : Finset (Fin L)) (P : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin L) (B : ℝ) : Prop :=
  (∀ p q : Fin L × Fin W, q.1 ≠ a → P p q = 0) ∧
    ∀ p q : Fin L × Fin W, p.1 ∈ Lab → ‖P p q‖ ≤ B * (W : ℝ)⁻¹

/-- One loop factor `S E_a`. -/
private lemma LoopBd.factor {Lab : Finset (Fin L)} {S : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    {K : ℝ} (hK : 0 ≤ K) (hS : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖S p q‖ ≤ K)
    {a : Fin L} (ha : a ∈ Lab) : LoopBd Lab (S * blockE W L a) a K := by
  refine ⟨fun p q hq => ?_, fun p q hp => ?_⟩
  · simp [blockE, Matrix.mul_diagonal, hq]
  · simp only [blockE, Matrix.mul_diagonal]
    by_cases hq : q.1 = a
    · simp only [hq, ite_true, norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_right (hS p q hp (hq ▸ ha)) (by positivity) |>.trans_eq (by ring)
    · simp only [hq, ite_false, mul_zero, norm_zero]
      positivity

/-- Product of two loop-factor products. -/
private lemma LoopBd.mul {Lab : Finset (Fin L)} {P Q : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    {a b : Fin L} {B C : ℝ} (hW : 1 ≤ W) (hB : 0 ≤ B) (hP : LoopBd Lab P a B)
    (ha : a ∈ Lab) (hQ : LoopBd Lab Q b C) : LoopBd Lab (P * Q) b (B * C) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  refine ⟨fun p q hq => ?_, fun p q hp => ?_⟩
  · rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun r _ => by rw [hQ.1 r q hq, mul_zero]
  · rw [Matrix.mul_apply]
    calc ‖∑ r, P p r * Q r q‖ ≤ ∑ r : Fin L × Fin W,
          (if r.1 = a then B * (W : ℝ)⁻¹ * (C * (W : ℝ)⁻¹) else 0) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
          by_cases hr : r.1 = a
          · simp only [hr, ite_true, norm_mul]
            exact mul_le_mul (hP.2 p r hp) (hQ.2 r q (hr ▸ ha)) (norm_nonneg _)
              (by positivity)
          · simp [hP.1 p r hr, hr]
      _ = B * C * (W : ℝ)⁻¹ := by
          rw [lemmaNOffset_sum_block]
          field_simp

/-- The trace of a loop-factor product. -/
private lemma LoopBd.trace_le {Lab : Finset (Fin L)}
    {P : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {a : Fin L} {B : ℝ} (hW : 1 ≤ W)
    (hP : LoopBd Lab P a B) (ha : a ∈ Lab) : ‖P.trace‖ ≤ B := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [Matrix.trace]
  calc ‖∑ p, P.diag p‖ ≤ ∑ p : Fin L × Fin W, (if p.1 = a then B * (W : ℝ)⁻¹ else 0) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        by_cases hp : p.1 = a
        · simp only [hp, ite_true, Matrix.diag]
          exact hP.2 p p (hp ▸ ha)
        · simp [Matrix.diag, hP.1 p p hp, hp]
    _ = B := by
        rw [lemmaNOffset_sum_block]
        field_simp

/-- A loop-factor product times a matrix bounded on the blocks `Lab`. -/
private lemma LoopBd.mul_bdd {Lab : Finset (Fin L)}
    {P S : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {a : Fin L} {B K : ℝ} (hW : 1 ≤ W)
    (hB : 0 ≤ B) (hP : LoopBd Lab P a B) (ha : a ∈ Lab)
    (hS : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖S p q‖ ≤ K) {p q : Fin L × Fin W}
    (hp : p.1 ∈ Lab) (hq : q.1 ∈ Lab) : ‖(P * S) p q‖ ≤ B * K := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [Matrix.mul_apply]
  calc ‖∑ r, P p r * S r q‖ ≤ ∑ r : Fin L × Fin W,
        (if r.1 = a then B * (W : ℝ)⁻¹ * K else 0) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
        by_cases hr : r.1 = a
        · simp only [hr, ite_true, norm_mul]
          exact mul_le_mul (hP.2 p r hp) (hS r q (hr ▸ ha) hq) (norm_nonneg _) (by positivity)
        · simp [hP.1 p r hr, hr]
    _ = B * K := by
        rw [lemmaNOffset_sum_block]
        field_simp

/-- Bounds on the entries of `G` on the blocks `Lab` pass to `G^σ`. -/
private lemma lemmaNOffset_sgn_bound {Lab : Finset (Fin L)}
    {G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ}
    (hG : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖G p q‖ ≤ K) (σ : Bool) :
    ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖sgnMat G σ p q‖ ≤ K := by
  intro p q hp hq
  cases σ
  · simp only [sgnMat, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, norm_star]
    exact hG q p hq hp
  · simpa [sgnMat] using hG p q hp hq

/-- A one-letter loop is at most `K`. -/
private lemma lemmaNOffset_loopTr_one_le {Lab : Finset (Fin L)}
    {G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ} (hW : 1 ≤ W) (hK : 0 ≤ K)
    (hG : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖G p q‖ ≤ K) {c : Fin L}
    (hc : c ∈ Lab) (σ : Bool) : ‖loopTr G ![c] ![σ]‖ ≤ K := by
  have h := (LoopBd.factor hK (lemmaNOffset_sgn_bound hG σ) hc).trace_le hW hc
  simpa [loopTr] using h

/-- A two-letter loop is at most `K²`. -/
private lemma lemmaNOffset_loopTr_two_le {Lab : Finset (Fin L)}
    {G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ} (hW : 1 ≤ W) (hK : 0 ≤ K)
    (hG : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖G p q‖ ≤ K) (a : Fin 2 → Fin L)
    (σ : Fin 2 → Bool) (ha : ∀ i, a i ∈ Lab) : ‖loopTr G a σ‖ ≤ K ^ 2 := by
  have h0 := LoopBd.factor hK (lemmaNOffset_sgn_bound hG (σ 0)) (ha 0)
  have h1 := LoopBd.factor hK (lemmaNOffset_sgn_bound hG (σ 1)) (ha 1)
  have h := (h0.mul hW hK (ha 0) h1).trace_le hW (ha 1)
  have e : loopTr G a σ = ((sgnMat G (σ 0) * blockE W L (a 0)) *
      (sgnMat G (σ 1) * blockE W L (a 1))).trace := by
    simp [loopTr, List.ofFn_succ]
  rw [e]
  nlinarith [h]

/-- A three-letter loop is at most `K³`. -/
private lemma lemmaNOffset_loopTr_three_le {Lab : Finset (Fin L)}
    {G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ} (hW : 1 ≤ W) (hK : 0 ≤ K)
    (hG : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖G p q‖ ≤ K) (a : Fin 3 → Fin L)
    (σ : Fin 3 → Bool) (ha : ∀ i, a i ∈ Lab) : ‖loopTr G a σ‖ ≤ K ^ 3 := by
  have h0 := LoopBd.factor hK (lemmaNOffset_sgn_bound hG (σ 0)) (ha 0)
  have h1 := LoopBd.factor hK (lemmaNOffset_sgn_bound hG (σ 1)) (ha 1)
  have h2 := LoopBd.factor hK (lemmaNOffset_sgn_bound hG (σ 2)) (ha 2)
  have h := (h0.mul hW hK (ha 0) (h1.mul hW hK (ha 1) h2)).trace_le hW (ha 2)
  have e : loopTr G a σ = ((sgnMat G (σ 0) * blockE W L (a 0)) *
      ((sgnMat G (σ 1) * blockE W L (a 1)) * (sgnMat G (σ 2) * blockE W L (a 2)))).trace := by
    simp [loopTr, List.ofFn_succ]
  rw [e]
  nlinarith [h]

/-- The cut loops `B_i` of a two-letter loop have entries at most `K³` on the blocks `Lab`. -/
private lemma lemmaNOffset_loopB_two_le {Lab : Finset (Fin L)}
    {G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ} (hW : 1 ≤ W) (hK : 0 ≤ K)
    (hG : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖G p q‖ ≤ K) (a : Fin 2 → Fin L)
    (σ : Fin 2 → Bool) (ha : ∀ i, a i ∈ Lab) (i : Fin 2) {p q : Fin L × Fin W} (hp : p.1 ∈ Lab)
    (hq : q.1 ∈ Lab) : ‖loopB G a σ i p q‖ ≤ K ^ 3 := by
  have h0 := LoopBd.factor hK (lemmaNOffset_sgn_bound hG (σ 0)) (ha 0)
  have h1 := LoopBd.factor hK (lemmaNOffset_sgn_bound hG (σ 1)) (ha 1)
  have h01 := h0.mul hW hK (ha 0) h1
  have h10 := (LoopBd.factor hK (lemmaNOffset_sgn_bound hG (σ 1)) (ha 1)).mul hW hK (ha 1)
    (LoopBd.factor hK (lemmaNOffset_sgn_bound hG (σ 0)) (ha 0))
  fin_cases i
  · have := h01.mul_bdd hW (mul_nonneg hK hK) (ha 1)
      (lemmaNOffset_sgn_bound hG (σ 0)) hp hq
    simpa [loopB, List.ofFn_succ, pow_succ, mul_assoc] using this
  · have := h10.mul_bdd hW (mul_nonneg hK hK) (ha 0)
      (lemmaNOffset_sgn_bound hG (σ 1)) hp hq
    simpa [loopB, List.ofFn_succ, pow_succ, mul_assoc] using this

/-- The trace in the carré du champ of a loop (5.9) [gc:eq:bracket] on entries of the block
`c`. -/
private lemma lemmaNOffset_gamma_trace_le (hW : 1 ≤ W) {c : Fin L}
    {X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {KX KY : ℝ} (hKX : 0 ≤ KX)
    (hX : ∀ p q : Fin L × Fin W, p.1 = c → q.1 = c → ‖X p q‖ ≤ KX)
    (hY : ∀ p q : Fin L × Fin W, p.1 = c → q.1 = c → ‖Y p q‖ ≤ KY) :
    ‖(((W : ℂ) • blockE W L c) * X * ((W : ℂ) • blockE W L c) * Yᴴ).trace‖ ≤
      (W : ℝ) ^ 2 * (KX * KY) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hD : ((W : ℂ) • blockE W L c) = Matrix.diagonal
      (fun p : Fin L × Fin W => if p.1 = c then (1 : ℂ) else 0) := by
    ext p q
    by_cases hpq : p = q
    · subst hpq
      by_cases hp : p.1 = c
      · simp only [blockE, hp, ite_true, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 (by omega))
      · simp [blockE, hp]
    · simp [blockE, Matrix.diagonal_apply_ne _ hpq]
  rw [hD, Matrix.trace]
  calc ‖∑ p, ((Matrix.diagonal (fun p : Fin L × Fin W => if p.1 = c then (1 : ℂ) else 0)) * X *
          (Matrix.diagonal (fun p : Fin L × Fin W => if p.1 = c then (1 : ℂ) else 0)) * Yᴴ).diag p‖
      ≤ ∑ p : Fin L × Fin W, (if p.1 = c then (W : ℝ) * (KX * KY) else 0) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        by_cases hp : p.1 = c
        · simp only [Matrix.diag, hp, ite_true]
          rw [Matrix.mul_apply]
          calc ‖∑ q, ((Matrix.diagonal (fun p : Fin L × Fin W => if p.1 = c then (1 : ℂ) else 0)) *
                  X * (Matrix.diagonal (fun p : Fin L × Fin W => if p.1 = c then (1 : ℂ) else 0)))
                  p q * Yᴴ q p‖
              ≤ ∑ q : Fin L × Fin W, (if q.1 = c then KX * KY else 0) := by
                refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
                by_cases hq : q.1 = c
                · simp only [hq, ite_true, Matrix.diagonal_mul, Matrix.mul_diagonal, norm_mul,
                    Matrix.conjTranspose_apply, norm_star, hp]
                  simp only [norm_one, one_mul, mul_one]
                  exact mul_le_mul (hX p q hp hq) (hY p q hp hq) (norm_nonneg _) hKX
                · simp [Matrix.mul_diagonal, hq]
            _ = (W : ℝ) * (KX * KY) := lemmaNOffset_sum_block c _
        · simp only [Matrix.diag]
          rw [Matrix.mul_apply]
          have h0 : ∑ q, ((Matrix.diagonal
              (fun p : Fin L × Fin W => if p.1 = c then (1 : ℂ) else 0)) * X *
              (Matrix.diagonal (fun p : Fin L × Fin W => if p.1 = c then (1 : ℂ) else 0)))
              p q * Yᴴ q p = 0 :=
            Finset.sum_eq_zero fun q _ => by
              simp [Matrix.mul_diagonal, Matrix.diagonal_mul, hp]
          rw [h0]
          simp [hp]
    _ = (W : ℝ) ^ 2 * (KX * KY) := by
        rw [lemmaNOffset_sum_block]; ring

end LoopEntry

/-! ### Pointwise bound of the generator and bracket of the mixed two-loop error -/

section PairPointwise

variable {W L : ℕ}

private lemma lemmaNOffset_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : (1 : ℝ) ≤ max 1 g := le_max_left _ _
  positivity

/-- `‖m^σ‖ = ‖m‖`. -/
private lemma lemmaNOffset_norm_sgnScalar (m : ℂ) (s : Bool) : ‖sgnScalar m s‖ = ‖m‖ := by
  cases s <;> simp [sgnScalar]

/-- The labels `a, b, c`. -/
private lemma lemmaNOffset_insLab_mem (a b c : Fin L) (i : Fin 2) (j : Fin 3) :
    insLab ![a, b] i c j ∈ ({a, b, c} : Finset (Fin L)) := by
  fin_cases i
  · have : insLab ![a, b] 0 c = ![c, a, b] := by funext j; fin_cases j <;> rfl
    simp only [Fin.zero_eta, this]
    fin_cases j <;> simp
  · have : insLab ![a, b] 1 c = ![a, c, b] := by funext j; fin_cases j <;> rfl
    simp only [Fin.mk_one, this]
    fin_cases j <;> simp

/-- The right side of (C.16) [fo:eq:pair-error], the generator of the mixed two-loop error, is
bounded by a weighted sum of powers of the entry bound `K_c`: pointwise in the matrix. -/
private lemma lemmaNOffset_gen_pointwise (g E : ℝ) (m : ℂ) (hW : 1 ≤ W) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) (w₁ w₂ : Fin L → ℝ)
    (hw₁ : ∀ c, 0 ≤ w₁ c) (hw₂ : ∀ c, 0 ≤ w₂ c)
    (hpr : ∀ x y : Fin L, ‖primLoop g W L E m u ![x, y] ![true, false]‖ ≤ W) (hm : ‖m‖ ≤ W)
    (K : Fin L → ℝ) (hK : ∀ c, (W : ℝ) + 1 ≤ K c)
    (hG : ∀ c, ∀ p q : Fin L × Fin W, p.1 ∈ ({a, b, c} : Finset (Fin L)) →
      q.1 ∈ ({a, b, c} : Finset (Fin L)) → ‖resolventMat M (zChar g E m u) p q‖ ≤ K c) :
    ‖lightW g E m ![a, b] ![true, false] u M + ∑ c : Fin L, (((w₁ c : ℝ) : ℂ) *
        (resLoop g E m ![c, b] ![true, false] u M - primLoop g W L E m u ![c, b] ![true, false]) +
        (resLoop g E m ![a, c] ![true, false] u M - primLoop g W L E m u ![a, c] ![true, false]) *
          ((w₂ c : ℝ) : ℂ)) +
      ((gammaG g * W : ℝ) : ℂ) * ∑ c : Fin L,
        (resLoop g E m ![a, c] ![true, false] u M - primLoop g W L E m u ![a, c] ![true, false]) *
          (resLoop g E m ![c, b] ![true, false] u M - primLoop g W L E m u ![c, b] ![true, false])‖
      ≤ ∑ c : Fin L, (2 * w₁ c + 2 * w₂ c + 8 * (gammaG g * W)) * K c ^ 6 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγW : 0 ≤ gammaG g * W := mul_nonneg (lemmaNOffset_gammaG_pos g).le hW0.le
  have hK1 : ∀ c, 1 ≤ K c := fun c => by linarith [hK c]
  have hKW : ∀ c, (W : ℝ) ≤ K c := fun c => by linarith [hK c]
  have hK0 : ∀ c, 0 ≤ K c := fun c => by linarith [hK1 c]
  have hlab : ∀ c : Fin L, a ∈ ({a, b, c} : Finset (Fin L)) ∧ b ∈ ({a, b, c} : Finset (Fin L)) ∧
      c ∈ ({a, b, c} : Finset (Fin L)) := fun c => by simp
  have hD1 : ∀ c, ‖resLoop g E m ![c, b] ![true, false] u M -
      primLoop g W L E m u ![c, b] ![true, false]‖ ≤ 2 * K c ^ 2 := fun c => by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖resLoop g E m ![c, b] ![true, false] u M‖ ≤ K c ^ 2 := by
      refine lemmaNOffset_loopTr_two_le hW (hK0 c) (hG c) _ _ fun i => ?_
      fin_cases i
      · exact (hlab c).2.2
      · exact (hlab c).2.1
    have h2 := hpr c b
    nlinarith [hKW c, hK1 c]
  have hD2 : ∀ c, ‖resLoop g E m ![a, c] ![true, false] u M -
      primLoop g W L E m u ![a, c] ![true, false]‖ ≤ 2 * K c ^ 2 := fun c => by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖resLoop g E m ![a, c] ![true, false] u M‖ ≤ K c ^ 2 := by
      refine lemmaNOffset_loopTr_two_le hW (hK0 c) (hG c) _ _ fun i => ?_
      fin_cases i
      · exact (hlab c).1
      · exact (hlab c).2.2
    have h2 := hpr a c
    nlinarith [hKW c, hK1 c]
  have hL1 : ∀ (c : Fin L) (s : Bool), ‖loopTr (resolventMat M (zChar g E m u)) ![c] ![s] -
      sgnScalar m s‖ ≤ 2 * K c := fun c s => by
    refine (norm_sub_le _ _).trans ?_
    have h1 := lemmaNOffset_loopTr_one_le hW (hK0 c) (hG c) (hlab c).2.2 s
    rw [lemmaNOffset_norm_sgnScalar]
    linarith [hKW c]
  have hL3 : ∀ (c : Fin L) (i : Fin 2), ‖loopTr (resolventMat M (zChar g E m u))
      (insLab ![a, b] i c) (insSgn ![true, false] i)‖ ≤ K c ^ 3 := fun c i =>
    lemmaNOffset_loopTr_three_le hW (hK0 c) (hG c) _ _ (lemmaNOffset_insLab_mem a b c i)
  have hsum : lightW g E m ![a, b] ![true, false] u M + ∑ c : Fin L, (((w₁ c : ℝ) : ℂ) *
        (resLoop g E m ![c, b] ![true, false] u M - primLoop g W L E m u ![c, b] ![true, false]) +
        (resLoop g E m ![a, c] ![true, false] u M - primLoop g W L E m u ![a, c] ![true, false]) *
          ((w₂ c : ℝ) : ℂ)) +
      ((gammaG g * W : ℝ) : ℂ) * ∑ c : Fin L,
        (resLoop g E m ![a, c] ![true, false] u M - primLoop g W L E m u ![a, c] ![true, false]) *
          (resLoop g E m ![c, b] ![true, false] u M - primLoop g W L E m u ![c, b] ![true, false])
      = ∑ c : Fin L, (((gammaG g * W : ℝ) : ℂ) * ∑ i : Fin 2,
          (loopTr (resolventMat M (zChar g E m u)) ![c] ![(![true, false] : Fin 2 → Bool) i] -
            sgnScalar m ((![true, false] : Fin 2 → Bool) i)) *
          loopTr (resolventMat M (zChar g E m u)) (insLab ![a, b] i c)
            (insSgn ![true, false] i) +
        (((w₁ c : ℝ) : ℂ) *
          (resLoop g E m ![c, b] ![true, false] u M - primLoop g W L E m u ![c, b] ![true, false]) +
          (resLoop g E m ![a, c] ![true, false] u M - primLoop g W L E m u ![a, c] ![true, false]) *
            ((w₂ c : ℝ) : ℂ)) +
        ((gammaG g * W : ℝ) : ℂ) *
          ((resLoop g E m ![a, c] ![true, false] u M -
              primLoop g W L E m u ![a, c] ![true, false]) *
            (resLoop g E m ![c, b] ![true, false] u M -
              primLoop g W L E m u ![c, b] ![true, false]))) := by
    have hl : lightW g E m ![a, b] ![true, false] u M = ∑ c : Fin L,
        ((gammaG g * W : ℝ) : ℂ) * ∑ i : Fin 2,
          (loopTr (resolventMat M (zChar g E m u)) ![c] ![(![true, false] : Fin 2 → Bool) i] -
            sgnScalar m ((![true, false] : Fin 2 → Bool) i)) *
          loopTr (resolventMat M (zChar g E m u)) (insLab ![a, b] i c)
            (insSgn ![true, false] i) := by
      unfold lightW
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    rw [hl, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  have hKc := hK1 c
  have e1 : ‖((gammaG g * W : ℝ) : ℂ) * ∑ i : Fin 2,
      (loopTr (resolventMat M (zChar g E m u)) ![c] ![(![true, false] : Fin 2 → Bool) i] -
        sgnScalar m ((![true, false] : Fin 2 → Bool) i)) *
      loopTr (resolventMat M (zChar g E m u)) (insLab ![a, b] i c) (insSgn ![true, false] i)‖
      ≤ (gammaG g * W) * (4 * K c ^ 4) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγW]
    refine mul_le_mul_of_nonneg_left ?_ hγW
    rw [Fin.sum_univ_two]
    refine (norm_add_le _ _).trans ?_
    have t : ∀ i : Fin 2, ‖(loopTr (resolventMat M (zChar g E m u)) ![c]
        ![(![true, false] : Fin 2 → Bool) i] -
        sgnScalar m ((![true, false] : Fin 2 → Bool) i)) *
        loopTr (resolventMat M (zChar g E m u)) (insLab ![a, b] i c)
          (insSgn ![true, false] i)‖ ≤ 2 * K c ^ 4 := fun i => by
      rw [norm_mul]
      calc _ ≤ (2 * K c) * K c ^ 3 :=
            mul_le_mul (hL1 c _) (hL3 c i) (norm_nonneg _) (by positivity)
        _ = 2 * K c ^ 4 := by ring
    linarith [t 0, t 1]
  have e2 : ‖((w₁ c : ℝ) : ℂ) * (resLoop g E m ![c, b] ![true, false] u M -
      primLoop g W L E m u ![c, b] ![true, false]) +
      (resLoop g E m ![a, c] ![true, false] u M - primLoop g W L E m u ![a, c] ![true, false]) *
        ((w₂ c : ℝ) : ℂ)‖ ≤ 2 * w₁ c * K c ^ 2 + 2 * w₂ c * K c ^ 2 := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw₁ c)]
      calc _ ≤ w₁ c * (2 * K c ^ 2) := mul_le_mul_of_nonneg_left (hD1 c) (hw₁ c)
        _ = _ := by ring
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw₂ c)]
      calc _ ≤ (2 * K c ^ 2) * w₂ c := mul_le_mul_of_nonneg_right (hD2 c) (hw₂ c)
        _ = _ := by ring
  have e3 : ‖((gammaG g * W : ℝ) : ℂ) *
      ((resLoop g E m ![a, c] ![true, false] u M - primLoop g W L E m u ![a, c] ![true, false]) *
        (resLoop g E m ![c, b] ![true, false] u M - primLoop g W L E m u ![c, b] ![true, false]))‖
      ≤ (gammaG g * W) * (4 * K c ^ 4) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγW, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ hγW
    calc _ ≤ (2 * K c ^ 2) * (2 * K c ^ 2) :=
          mul_le_mul (hD2 c) (hD1 c) (norm_nonneg _) (by positivity)
      _ = 4 * K c ^ 4 := by ring
  have h4 : K c ^ 4 ≤ K c ^ 6 := pow_le_pow_right₀ hKc (by norm_num)
  have h2' : K c ^ 2 ≤ K c ^ 6 := pow_le_pow_right₀ hKc (by norm_num)
  have hfin := add_le_add (add_le_add e1 e2) e3
  refine ((norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)).trans (hfin.trans ?_)
  have i1 : (gammaG g * W) * (4 * K c ^ 4) ≤ (gammaG g * W) * (4 * K c ^ 6) := by gcongr
  have i2 : 2 * w₁ c * K c ^ 2 ≤ 2 * w₁ c * K c ^ 6 := by
    have := hw₁ c
    gcongr
  have i3 : 2 * w₂ c * K c ^ 2 ≤ 2 * w₂ c * K c ^ 6 := by
    have := hw₂ c
    gcongr
  nlinarith [i1, i2, i3]

/-- The bracket (5.9) [gc:eq:bracket] of the two-loop `ℒ₂(a,b;+,-)` is bounded by a weighted sum
of powers of the entry bound `K_c`: pointwise in the matrix. -/
private lemma lemmaNOffset_gamma_pointwise (g E : ℝ) (m : ℂ) (hm : 0 < m.im) (hW : 1 ≤ W)
    {u : ℝ} (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (a b : Fin L) (K : Fin L → ℝ) (hK : ∀ c, 1 ≤ K c)
    (hG : ∀ c, ∀ p q : Fin L × Fin W, p.1 ∈ ({a, b, c} : Finset (Fin L)) →
      q.1 ∈ ({a, b, c} : Finset (Fin L)) → ‖resolventMat M (zChar g E m u) p q‖ ≤ K c) :
    ‖blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, false] u)
        (resLoop g E m ![a, b] ![true, false] u) M‖ ≤
      ∑ c : Fin L, 4 * (gammaG g * W) * K c ^ 6 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγ := lemmaNOffset_gammaG_pos g
  have hK0 : ∀ c, 0 ≤ K c := fun c => by linarith [hK c]
  rw [blockGamma_loopTr g E m hm hu hM ![a, b] ![true, false] ![a, b] ![true, false], norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hterm : ∀ (c : Fin L) (i j : Fin 2),
      ‖(((W : ℂ) • blockE W L c) * loopB (resolventMat M (zChar g E m u)) ![a, b]
          ![true, false] i * ((W : ℂ) • blockE W L c) *
          (loopB (resolventMat M (zChar g E m u)) ![a, b] ![true, false] j)ᴴ).trace‖ ≤
        (W : ℝ) ^ 2 * (K c ^ 3 * K c ^ 3) := fun c i j => by
    have hlab : ∀ k : Fin 2, (![a, b] : Fin 2 → Fin L) k ∈ ({a, b, c} : Finset (Fin L)) := by
      intro k; fin_cases k <;> simp
    refine lemmaNOffset_gamma_trace_le hW (pow_nonneg (hK0 c) 3) ?_ ?_
    · intro p q hp hq
      exact lemmaNOffset_loopB_two_le hW (hK0 c) (hG c) _ _ hlab i (by simp [hp])
        (by simp [hq])
    · intro p q hp hq
      exact lemmaNOffset_loopB_two_le hW (hK0 c) (hG c) _ _ hlab j (by simp [hp])
        (by simp [hq])
  calc (gammaG g / W) * ‖∑ c : Fin L, ∑ i : Fin 2, ∑ j : Fin 2,
        (((W : ℂ) • blockE W L c) * loopB (resolventMat M (zChar g E m u)) ![a, b]
          ![true, false] i * ((W : ℂ) • blockE W L c) *
          (loopB (resolventMat M (zChar g E m u)) ![a, b] ![true, false] j)ᴴ).trace‖
      ≤ (gammaG g / W) * ∑ c : Fin L, ∑ i : Fin 2, ∑ j : Fin 2,
          (W : ℝ) ^ 2 * (K c ^ 3 * K c ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm c i j)
    _ = ∑ c : Fin L, 4 * (gammaG g * W) * K c ^ 6 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
        push_cast
        ring

end PairPointwise

/-! ### Continuity in the sample -/

section Cont

variable {W L : ℕ}

/-- The resolvent of the single-time realization is continuous in the sample off the real
axis. -/
private lemma lemmaNOffset_continuous_resolvent (g u : ℝ) (W L : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun ω : Ω W L => resolventMat (flowH g W L u ω) z := by
  have hV : Continuous fun ω : Ω W L => blockV W L ω := by
    simp only [blockV_eq_sum_blockBasis]
    fun_prop
  have hF : Continuous fun ω : Ω W L => flowH g W L u ω := by
    unfold flowH blockFlow
    fun_prop
  have hc : Continuous fun ω : Ω W L => flowH g W L u ω - z • (1 : Matrix _ _ ℂ) :=
    hF.sub continuous_const
  refine continuous_iff_continuousAt.2 fun ω => ?_
  have hu := isUnit_sub_smul_one (flowH_isHermitian g W L u ω) hz
  have hdet : (flowH g W L u ω - z • (1 : Matrix _ _ ℂ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  refine (continuousAt_matrix_inv _ ?_).comp hc.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hdet

/-- A loop of a continuous family of matrices is continuous. -/
private lemma lemmaNOffset_continuous_loopTr {X : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hX : Continuous X) {k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) :
    Continuous fun ω => loopTr (X ω) a σ := by
  unfold loopTr
  refine Continuous.matrix_trace ?_
  rw [show (fun ω => (List.ofFn fun i : Fin k => sgnMat (X ω) (σ i) * blockE W L (a i)).prod) =
    fun ω => ((List.finRange k).map fun i => sgnMat (X ω) (σ i) * blockE W L (a i)).prod from by
      funext ω; rw [List.ofFn_eq_map]]
  refine continuous_list_prod _ fun i _ => ?_
  refine Continuous.matrix_mul ?_ continuous_const
  cases σ i
  · exact hX.matrix_conjTranspose
  · exact hX

/-- The cut loops of a continuous family of matrices are continuous. -/
private lemma lemmaNOffset_continuous_loopB {X : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hX : Continuous X) {k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) (i : Fin k) :
    Continuous fun ω => loopB (X ω) a σ i := by
  unfold loopB
  refine Continuous.matrix_mul ?_ ?_
  · rw [show (fun ω => (List.ofFn fun p : Fin k => sgnMat (X ω) (σ (i + p)) *
        blockE W L (a (i + p))).prod) = fun ω => ((List.finRange k).map fun p =>
        sgnMat (X ω) (σ (i + p)) * blockE W L (a (i + p))).prod from by
      funext ω; rw [List.ofFn_eq_map]]
    refine continuous_list_prod _ fun p _ => ?_
    refine Continuous.matrix_mul ?_ continuous_const
    cases σ (i + p)
    · exact hX.matrix_conjTranspose
    · exact hX
  · cases σ i
    · exact hX.matrix_conjTranspose
    · exact hX

/-- The right side of the generator identity of the mixed two-loop error is continuous in the
sample. -/
private lemma lemmaNOffset_gen_expr_continuous (g E : ℝ) (m : ℂ) (u : ℝ) (a b : Fin L)
    (w₁ w₂ : Fin L → ℝ) {M : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hM : Continuous fun ω => resolventMat (M ω) (zChar g E m u)) :
    Continuous fun ω => lightW g E m ![a, b] ![true, false] u (M ω) + ∑ c : Fin L,
      (((w₁ c : ℝ) : ℂ) *
        (resLoop g E m ![c, b] ![true, false] u (M ω) -
          primLoop g W L E m u ![c, b] ![true, false]) +
        (resLoop g E m ![a, c] ![true, false] u (M ω) -
          primLoop g W L E m u ![a, c] ![true, false]) * ((w₂ c : ℝ) : ℂ)) +
      ((gammaG g * W : ℝ) : ℂ) * ∑ c : Fin L,
        (resLoop g E m ![a, c] ![true, false] u (M ω) -
          primLoop g W L E m u ![a, c] ![true, false]) *
          (resLoop g E m ![c, b] ![true, false] u (M ω) -
            primLoop g W L E m u ![c, b] ![true, false]) := by
  have hl : ∀ {k : ℕ} (x : Fin k → Fin L) (σ : Fin k → Bool),
      Continuous fun ω => resLoop g E m x σ u (M ω) := fun x σ =>
    lemmaNOffset_continuous_loopTr hM x σ
  refine Continuous.add (Continuous.add ?_ ?_) ?_
  · unfold lightW
    refine continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun c _ => Continuous.mul (Continuous.sub ?_ continuous_const) ?_)
    · exact lemmaNOffset_continuous_loopTr hM _ _
    · exact lemmaNOffset_continuous_loopTr hM _ _
  · refine continuous_finsetSum _ fun c _ =>
      Continuous.add (continuous_const.mul ?_) (Continuous.mul ?_ continuous_const)
    · exact (hl _ _).sub continuous_const
    · exact (hl _ _).sub continuous_const
  · refine continuous_const.mul (continuous_finsetSum _ fun c _ => Continuous.mul ?_ ?_)
    · exact (hl _ _).sub continuous_const
    · exact (hl _ _).sub continuous_const

/-- The bracket of the two-loop `ℒ₂(a,b;+,-)` in the form of (5.9) [gc:eq:bracket] is continuous in
the sample. -/
private lemma lemmaNOffset_gamma_expr_continuous (g E : ℝ) (m : ℂ) (u : ℝ) (a b : Fin L)
    {M : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hM : Continuous fun ω => resolventMat (M ω) (zChar g E m u)) :
    Continuous fun ω => ((gammaG g / W : ℝ) : ℂ) * ∑ c : Fin L, ∑ i : Fin 2, ∑ j : Fin 2,
        (((W : ℂ) • blockE W L c) * loopB (resolventMat (M ω) (zChar g E m u)) ![a, b]
          ![true, false] i * ((W : ℂ) • blockE W L c) *
          (loopB (resolventMat (M ω) (zChar g E m u)) ![a, b] ![true, false] j)ᴴ).trace := by
  refine continuous_const.mul (continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ?_)
  refine Continuous.matrix_trace ?_
  refine Continuous.matrix_mul (Continuous.matrix_mul (Continuous.matrix_mul continuous_const ?_)
    continuous_const) ?_
  · exact lemmaNOffset_continuous_loopB hM _ _ i
  · exact (lemmaNOffset_continuous_loopB hM _ _ j).matrix_conjTranspose

end Cont

/-! ### Moments of weighted sums -/

section WSum

/-- Jensen for weighted sums: `(Σ w_i f_i)^n ≤ (Σ w_i)^{n-1} Σ w_i f_i^n`. -/
private lemma lemmaNOffset_wsum_pow_le {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) {n : ℕ} (hn : 1 ≤ n) :
    (∑ i, w i * f i) ^ n ≤ (∑ i, w i) ^ (n - 1) * ∑ i, w i * f i ^ n := by
  set S := ∑ i, w i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hw i
  rcases hS0.eq_or_lt with h0 | hpos
  · have hw0 : ∀ i, w i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw i)).1 h0.symm i (Finset.mem_univ i)
    simp [hw0, zero_pow (by omega : n ≠ 0)]
  · have hw1 : ∑ i, w i / S = 1 := by rw [← Finset.sum_div]; exact div_self hpos.ne'
    have h := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun i => w i / S) f
      (fun i _ => div_nonneg (hw i) hS0) hw1 (fun i _ => hf i) n
    have e1 : ∑ i, w i / S * f i = (∑ i, w i * f i) / S := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, w i / S * f i ^ n = (∑ i, w i * f i ^ n) / S := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2, div_pow] at h
    have hSn : 0 < S ^ n := pow_pos hpos n
    rw [div_le_div_iff₀ hSn hpos] at h
    have : S ^ n = S ^ (n - 1) * S := by rw [← pow_succ]; congr 1; omega
    rw [this] at h
    nlinarith [h, pow_pos hpos (n - 1)]

/-- A weighted sum of nonnegative functions with integrable `n`-th powers has an integrable
`n`-th power, with the weighted moment bound. -/
private lemma lemmaNOffset_wsum_moment {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : ι → Ω' → ℝ) (hf0 : ∀ i x, 0 ≤ f i x) {n : ℕ} (hn : 1 ≤ n) {B : ℝ}
    (hfi : ∀ i, Integrable (fun x => f i x ^ n) P ∧ ∫ x, f i x ^ n ∂P ≤ B)
    (Q : Ω' → ℝ) (hQm : AEStronglyMeasurable Q P) (hQ0 : ∀ x, 0 ≤ Q x)
    (hQ : ∀ x, Q x ≤ ∑ i, w i * f i x) :
    Integrable (fun x => Q x ^ n) P ∧ ∫ x, Q x ^ n ∂P ≤ (∑ i, w i) ^ n * B := by
  set S := ∑ i, w i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hw i
  have hpt : ∀ x, Q x ^ n ≤ S ^ (n - 1) * ∑ i, w i * f i x ^ n := fun x =>
    (pow_le_pow_left₀ (hQ0 x) (hQ x) n).trans
      (lemmaNOffset_wsum_pow_le w (fun i => f i x) hw (fun i => hf0 i x) hn)
  have hRi : Integrable (fun x => S ^ (n - 1) * ∑ i, w i * f i x ^ n) P :=
    (integrable_finsetSum Finset.univ fun i _ => (hfi i).1.const_mul (w i)).const_mul _
  refine ⟨Integrable.mono' hRi (hQm.pow n) (Filter.Eventually.of_forall fun x => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (pow_nonneg (hQ0 x) n)]
    exact hpt x
  · calc ∫ x, Q x ^ n ∂P ≤ ∫ x, S ^ (n - 1) * ∑ i, w i * f i x ^ n ∂P :=
          integral_mono (Integrable.mono' hRi (hQm.pow n)
            (Filter.Eventually.of_forall fun x => by
              rw [Real.norm_of_nonneg (pow_nonneg (hQ0 x) n)]; exact hpt x)) hRi hpt
      _ = S ^ (n - 1) * ∑ i, w i * ∫ x, f i x ^ n ∂P := by
          rw [integral_const_mul, integral_finsetSum Finset.univ fun i _ =>
            (hfi i).1.const_mul (w i)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      _ ≤ S ^ (n - 1) * ∑ i, w i * B := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (pow_nonneg hS0 _)
          exact mul_le_mul_of_nonneg_left (hfi i).2 (hw i)
      _ = S ^ n * B := by
          rw [← Finset.sum_mul]
          have : S ^ n = S ^ (n - 1) * S := by rw [← pow_succ]; congr 1; omega
          rw [this]; ring

/-- A constant plus a finite sum of nonnegative functions with integrable `n`-th powers. -/
private lemma lemmaNOffset_const_sum_moment {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] {A : ℝ} (hA : 0 ≤ A) (z : ι → Ω' → ℝ)
    (hz0 : ∀ i x, 0 ≤ z i x) {n : ℕ} (hn : 1 ≤ n) {B : ℝ}
    (hzi : ∀ i, Integrable (fun x => z i x ^ n) P ∧ ∫ x, z i x ^ n ∂P ≤ B)
    (hm : AEStronglyMeasurable (fun x => A + ∑ i, z i x) P) :
    Integrable (fun x => (A + ∑ i, z i x) ^ n) P ∧
      ∫ x, (A + ∑ i, z i x) ^ n ∂P ≤ 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ n * B) := by
  have hZ0 : ∀ x, 0 ≤ ∑ i, z i x := fun x => Finset.sum_nonneg fun i _ => hz0 i x
  have hpt : ∀ x, (A + ∑ i, z i x) ^ n ≤
      2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, z i x ^ n) := by
    intro x
    refine (add_pow_le hA (hZ0 x) n).trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
    have h := lemmaNOffset_wsum_pow_le (fun _ : ι => (1 : ℝ)) (fun i => z i x)
      (fun _ => zero_le_one) (fun i => hz0 i x) hn
    simpa using h
  have hRi : Integrable (fun x => 2 ^ (n - 1) *
      (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, z i x ^ n)) P :=
    ((integrable_const _).add
      ((integrable_finsetSum Finset.univ fun i _ => (hzi i).1).const_mul _)).const_mul _
  have hI : Integrable (fun x => (A + ∑ i, z i x) ^ n) P :=
    Integrable.mono' hRi (hm.pow n) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (pow_nonneg (add_nonneg hA (hZ0 x)) n)]; exact hpt x)
  refine ⟨hI, ?_⟩
  calc ∫ x, (A + ∑ i, z i x) ^ n ∂P
      ≤ ∫ x, 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, z i x ^ n) ∂P :=
        integral_mono hI hRi hpt
    _ = 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, ∫ x, z i x ^ n ∂P) := by
        rw [integral_const_mul, integral_add (integrable_const _)
          ((integrable_finsetSum Finset.univ fun i _ => (hzi i).1).const_mul _),
          integral_const_mul, integral_finsetSum Finset.univ fun i _ => (hzi i).1]
        simp
    _ ≤ 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ _i : ι, B) := by
        refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hzi i).2) (by positivity)
    _ = 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ n * B) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : (Fintype.card ι : ℝ) ^ n = (Fintype.card ι : ℝ) ^ (n - 1) * Fintype.card ι := by
          rw [← pow_succ]; congr 1; omega
        rw [this]; ring

end WSum

/-! ### The entry bound `K_c` and its moments -/

section KMoment

open scoped Matrix.Norms.L2Operator

/-- An entry is bounded by the operator norm. -/
private lemma lemmaNOffset_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (i j : n) : ‖X i j‖ ≤ ‖X‖ := by
  have h := Matrix.l2_opNorm_mulVec X ((EuclideanSpace.equiv n ℂ).symm (Pi.single j 1))
  have hx : ‖(EuclideanSpace.equiv n ℂ).symm (Pi.single j (1 : ℂ))‖ = 1 := by simp
  rw [hx, mul_one] at h
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans h)
  simp [Matrix.mulVec_single]

/-- The bound `K_c = W + 1 + Σ_{u,v ∈ {a,b,c}} ‖G_{uv}‖` on the entries of `G` between the
blocks `a, b, c`. -/
private def lemmaNOffsetK (W : ℕ) (x : FlowPt) (a b c : Fin x.L) (ω : Ω W x.L) : ℝ :=
  ((W : ℝ) + 1) + ∑ ij : Fin 3 × Fin 3,
    ‖blockOf (flowG W x ω) (![a, b, c] ij.1) (![a, b, c] ij.2)‖

private lemma lemmaNOffsetK_ge (W : ℕ) (x : FlowPt) (a b c : Fin x.L) (ω : Ω W x.L) :
    (W : ℝ) + 1 ≤ lemmaNOffsetK W x a b c ω := by
  unfold lemmaNOffsetK
  have : 0 ≤ ∑ ij : Fin 3 × Fin 3,
      ‖blockOf (flowG W x ω) (![a, b, c] ij.1) (![a, b, c] ij.2)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  linarith

private lemma lemmaNOffsetK_entry (W : ℕ) (x : FlowPt) (a b c : Fin x.L) (ω : Ω W x.L)
    {p q : Fin x.L × Fin W} (hp : p.1 ∈ ({a, b, c} : Finset (Fin x.L)))
    (hq : q.1 ∈ ({a, b, c} : Finset (Fin x.L))) :
    ‖flowG W x ω p q‖ ≤ lemmaNOffsetK W x a b c ω := by
  have hidx : ∀ r : Fin x.L, r ∈ ({a, b, c} : Finset (Fin x.L)) →
      ∃ i : Fin 3, ![a, b, c] i = r := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨2, by simp [h]⟩
  obtain ⟨i, hi⟩ := hidx _ hp
  obtain ⟨j, hj⟩ := hidx _ hq
  have h1 : ‖flowG W x ω p q‖ ≤ ‖blockOf (flowG W x ω) p.1 q.1‖ :=
    lemmaNOffset_norm_entry_le (blockOf (flowG W x ω) p.1 q.1) p.2 q.2
  have h2 : ‖blockOf (flowG W x ω) p.1 q.1‖ ≤ ∑ ij : Fin 3 × Fin 3,
      ‖blockOf (flowG W x ω) (![a, b, c] ij.1) (![a, b, c] ij.2)‖ := by
    have := Finset.single_le_sum (f := fun ij : Fin 3 × Fin 3 =>
      ‖blockOf (flowG W x ω) (![a, b, c] ij.1) (![a, b, c] ij.2)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (i, j))
    simpa [hi, hj] using this
  unfold lemmaNOffsetK
  linarith [h1, h2, (Nat.cast_nonneg W : (0 : ℝ) ≤ W)]

end KMoment

/-! ### Moments of the generator and bracket at one point -/

section PointMoment

open scoped Matrix.Norms.L2Operator

/-- The moments of `K_c^{6p}` from the moments of the blocks of `G`. -/
private lemma lemmaNOffsetK_moment (x : FlowPt) (W : ℕ) (hm : 0 < (mRoot x.g x.L x.E).im)
    (hu1 : x.u < 1) {p : ℕ} (hp : 1 ≤ p) {Bc : ℝ}
    (hcr : ∀ y z : Fin x.L, Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ (6 * p))
        (μ W x.L) ∧ ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ (6 * p) ∂(μ W x.L) ≤ Bc)
    (a b c : Fin x.L) :
    Continuous (fun ω => lemmaNOffsetK W x a b c ω) ∧
    Integrable (fun ω => (lemmaNOffsetK W x a b c ω ^ 6) ^ p) (μ W x.L) ∧
      ∫ ω, (lemmaNOffsetK W x a b c ω ^ 6) ^ p ∂(μ W x.L) ≤
        2 ^ (6 * p - 1) * (((W : ℝ) + 1) ^ (6 * p) + 9 ^ (6 * p) * Bc) := by
  have hz : (zChar x.g x.E (mRoot x.g x.L x.E) x.u).im ≠ 0 := by
    rw [im_zChar]; exact (etaChar_pos x.g _ hm hu1).ne'
  have hGc : Continuous fun ω : Ω W x.L => flowG W x ω :=
    lemmaNOffset_continuous_resolvent x.g x.u W x.L hz
  have hbc : ∀ y z : Fin x.L, Continuous fun ω : Ω W x.L => ‖blockOf (flowG W x ω) y z‖ := by
    intro y z
    refine Continuous.norm (continuous_matrix fun α β => ?_)
    exact (continuous_apply (z, β)).comp ((continuous_apply (y, α)).comp hGc)
  have hKc : Continuous (fun ω : Ω W x.L => lemmaNOffsetK W x a b c ω) := by
    unfold lemmaNOffsetK
    exact continuous_const.add (continuous_finsetSum _ fun ij _ => hbc _ _)
  have hn : 1 ≤ 6 * p := by omega
  have h := lemmaNOffset_const_sum_moment (μ W x.L) (A := (W : ℝ) + 1) (by positivity)
    (fun (ij : Fin 3 × Fin 3) ω => ‖blockOf (flowG W x ω) (![a, b, c] ij.1) (![a, b, c] ij.2)‖)
    (fun _ _ => norm_nonneg _) hn (B := Bc) (fun ij => hcr _ _) hKc.aestronglyMeasurable
  have e : ∀ ω, (lemmaNOffsetK W x a b c ω ^ 6) ^ p = lemmaNOffsetK W x a b c ω ^ (6 * p) :=
    fun ω => (pow_mul _ _ _).symm
  simp only [e]
  refine ⟨hKc, h.1, h.2.trans (le_of_eq ?_)⟩
  simp [Fintype.card_prod]

end PointMoment

section PointMoment2

open scoped Matrix.Norms.L2Operator

/-- Moments of `𝒢D₂(a,b)` and `Γ(ℒ₂(a,b))` at one point from the moments of the blocks of `G`
as in (5.33) [fo:eq:coarse-time-input], the kernel sums, the primitive-loop bound and the
budget. -/
private lemma lemmaNOffset_gen_moment_point (x : FlowPt) (W : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ x.L)
    (hm : IsDysonRootV (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))
    (hmW : ‖mRoot x.g x.L x.E‖ ≤ W) (hu0 : -1 < x.u) (hu1 : x.u < 1)
    (hpr : ∀ y z : Fin x.L,
      ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u ![y, z] ![true, false]‖ ≤ W)
    {S1 S2 : ℝ}
    (hk0 : ∀ y z, 0 ≤ mixedKer (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u y z)
    (hk1 : ∀ y, ∑ z, mixedKer (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u y z ≤ S1)
    (hk2 : ∀ z, ∑ y, mixedKer (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u y z ≤ S1)
    (hS2 : gammaG x.g * x.L ≤ S2) {p : ℕ} (hp : 1 ≤ p) {Bc : ℝ}
    (hcr : ∀ y z : Fin x.L, Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ (6 * p))
        (μ W x.L) ∧ ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ (6 * p) ∂(μ W x.L) ≤ Bc)
    (a b : Fin x.L) :
    Integrable (fun ω => ‖blockGen W x.L (gammaG x.g) (fun r N =>
            resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] r N -
              primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r ![a, b] ![true, false]) x.u
            (flowH x.g W x.L x.u ω)‖ ^ p) (μ W x.L) ∧
      ∫ ω, ‖blockGen W x.L (gammaG x.g) (fun r N =>
            resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] r N -
              primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r ![a, b] ![true, false]) x.u
            (flowH x.g W x.L x.u ω)‖ ^ p ∂(μ W x.L) ≤
        (4 * S1 + 8 * W * S2) ^ p *
          (2 ^ (6 * p - 1) * (((W : ℝ) + 1) ^ (6 * p) + 9 ^ (6 * p) * Bc)) ∧
      Integrable (fun ω => ‖blockGamma W x.L (gammaG x.g)
            (resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] x.u)
            (resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] x.u)
            (flowH x.g W x.L x.u ω)‖ ^ p) (μ W x.L) ∧
      ∫ ω, ‖blockGamma W x.L (gammaG x.g)
            (resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] x.u)
            (resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] x.u)
            (flowH x.g W x.L x.u ω)‖ ^ p ∂(μ W x.L) ≤
        (4 * S1 + 8 * W * S2) ^ p *
          (2 ^ (6 * p - 1) * (((W : ℝ) + 1) ^ (6 * p) + 9 ^ (6 * p) * Bc)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγ := lemmaNOffset_gammaG_pos x.g
  have hγW : 0 ≤ gammaG x.g * W := mul_nonneg hγ.le hW0.le
  have hz : (zChar x.g x.E (mRoot x.g x.L x.E) x.u).im ≠ 0 := by
    rw [im_zChar]; exact (etaChar_pos x.g _ hm.1 hu1).ne'
  have hGc : Continuous fun ω : Ω W x.L => flowG W x ω :=
    lemmaNOffset_continuous_resolvent x.g x.u W x.L hz
  have hMom := fun c => lemmaNOffsetK_moment x W hm.1 hu1 hp hcr a b c
  have hf0 : ∀ (c : Fin x.L) (ω : Ω W x.L), 0 ≤ lemmaNOffsetK W x a b c ω ^ 6 := fun c ω =>
    pow_nonneg (by linarith [lemmaNOffsetK_ge W x a b c ω, hW0]) 6
  have hKp : ∀ (c : Fin x.L) (ω : Ω W x.L), (W : ℝ) + 1 ≤ lemmaNOffsetK W x a b c ω :=
    lemmaNOffsetK_ge W x a b
  set Pm := pairP (gammaG x.g) (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))
    with hPm
  -- the sums of the weights
  have hsum : ∑ c : Fin x.L, (2 * mixedKer Pm x.u a c + 2 * mixedKer Pm x.u c b +
      8 * (gammaG x.g * W)) ≤ 4 * S1 + 8 * W * S2 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith [hk1 a, hk2 b, mul_le_mul_of_nonneg_left hS2 hW0.le]
  have hsumG : ∑ c : Fin x.L, 4 * (gammaG x.g * W) ≤ 4 * S1 + 8 * W * S2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left hS2 hW0.le
    have h2 : 0 ≤ S1 := (Finset.sum_nonneg fun c _ => hk0 a c).trans (hk1 a)
    nlinarith
  have hu : x.u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hu0, hu1⟩
  have hSw0 : 0 ≤ 4 * S1 + 8 * W * S2 := (Finset.sum_nonneg fun c _ => by
    have := hk0 a c
    have := hk0 c b
    positivity).trans hsum
  have hflowc : Continuous fun ω : Ω W x.L => resolventMat (flowH x.g W x.L x.u ω)
      (zChar x.g x.E (mRoot x.g x.L x.E) x.u) := hGc
  -- the generator
  have hgenc : Continuous fun ω : Ω W x.L => blockGen W x.L (gammaG x.g) (fun r N =>
      resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] r N -
        primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r ![a, b] ![true, false]) x.u
      (flowH x.g W x.L x.u ω) := by
    have h := lemmaNOffset_gen_expr_continuous x.g x.E (mRoot x.g x.L x.E) x.u a b
      (fun c => mixedKer Pm x.u a c) (fun c => mixedKer Pm x.u c b) (W := W)
      (M := fun ω => flowH x.g W x.L x.u ω) hflowc
    exact h.congr fun ω => (blockGen_pairErr x.g x.E (mRoot x.g x.L x.E) W x.L hW hL hm hu
      (flowH_isHermitian x.g W x.L x.u ω) a b).symm
  have hgenb : ∀ ω : Ω W x.L, ‖blockGen W x.L (gammaG x.g) (fun r N =>
      resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] r N -
        primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r ![a, b] ![true, false]) x.u
      (flowH x.g W x.L x.u ω)‖ ≤ ∑ c : Fin x.L, (2 * mixedKer Pm x.u a c +
        2 * mixedKer Pm x.u c b + 8 * (gammaG x.g * W)) * lemmaNOffsetK W x a b c ω ^ 6 := by
    intro ω
    rw [blockGen_pairErr x.g x.E (mRoot x.g x.L x.E) W x.L hW hL hm hu
      (flowH_isHermitian x.g W x.L x.u ω) a b]
    exact lemmaNOffset_gen_pointwise x.g x.E (mRoot x.g x.L x.E) hW x.u (flowH x.g W x.L x.u ω)
      a b (fun c => mixedKer Pm x.u a c) (fun c => mixedKer Pm x.u c b) (fun c => hk0 a c)
      (fun c => hk0 c b) hpr hmW (fun c => lemmaNOffsetK W x a b c ω) (fun c => hKp c ω)
      (fun c p q hp hq => lemmaNOffsetK_entry W x a b c ω hp hq)
  -- the bracket
  have hgamc : Continuous fun ω : Ω W x.L => blockGamma W x.L (gammaG x.g)
      (resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] x.u)
      (resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] x.u)
      (flowH x.g W x.L x.u ω) := by
    have h := lemmaNOffset_gamma_expr_continuous x.g x.E (mRoot x.g x.L x.E) x.u a b (W := W)
      (M := fun ω => flowH x.g W x.L x.u ω) hflowc
    exact h.congr fun ω => (blockGamma_loopTr x.g x.E (mRoot x.g x.L x.E) hm.1 hu1
      (flowH_isHermitian x.g W x.L x.u ω) ![a, b] ![true, false] ![a, b] ![true, false]).symm
  have hgamb : ∀ ω : Ω W x.L, ‖blockGamma W x.L (gammaG x.g)
      (resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] x.u)
      (resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] x.u)
      (flowH x.g W x.L x.u ω)‖ ≤
      ∑ c : Fin x.L, 4 * (gammaG x.g * W) * lemmaNOffsetK W x a b c ω ^ 6 := fun ω =>
    lemmaNOffset_gamma_pointwise x.g x.E (mRoot x.g x.L x.E) hm.1 hW hu1
      (flowH_isHermitian x.g W x.L x.u ω) a b (fun c => lemmaNOffsetK W x a b c ω)
      (fun c => by linarith [hKp c ω]) (fun c p q hp hq => lemmaNOffsetK_entry W x a b c ω hp hq)
  have hfi : ∀ c : Fin x.L, Integrable (fun ω => (lemmaNOffsetK W x a b c ω ^ 6) ^ p) (μ W x.L) ∧
      ∫ ω, (lemmaNOffsetK W x a b c ω ^ 6) ^ p ∂(μ W x.L) ≤
        2 ^ (6 * p - 1) * (((W : ℝ) + 1) ^ (6 * p) + 9 ^ (6 * p) * Bc) := fun c => (hMom c).2
  have hweights : ∀ c : Fin x.L, 0 ≤ 2 * mixedKer Pm x.u a c + 2 * mixedKer Pm x.u c b +
      8 * (gammaG x.g * W) := fun c => by
    have := hk0 a c
    have := hk0 c b
    positivity
  have hG1 := lemmaNOffset_wsum_moment (μ W x.L)
    (fun c : Fin x.L => 2 * mixedKer Pm x.u a c + 2 * mixedKer Pm x.u c b +
      8 * (gammaG x.g * W)) hweights (fun c ω => lemmaNOffsetK W x a b c ω ^ 6)
    (fun c ω => hf0 c ω) hp hfi _ hgenc.norm.aestronglyMeasurable (fun ω => norm_nonneg _) hgenb
  have hG2 := lemmaNOffset_wsum_moment (μ W x.L)
    (fun c : Fin x.L => 4 * (gammaG x.g * W)) (fun c => by positivity)
    (fun c ω => lemmaNOffsetK W x a b c ω ^ 6)
    (fun c ω => hf0 c ω) hp hfi _ hgamc.norm.aestronglyMeasurable (fun ω => norm_nonneg _) hgamb
  have hBk : 0 ≤ 2 ^ (6 * p - 1) * (((W : ℝ) + 1) ^ (6 * p) + 9 ^ (6 * p) * Bc) := by
    have hBc : 0 ≤ Bc := (integral_nonneg fun ω => pow_nonneg (norm_nonneg _) _).trans (hcr a a).2
    positivity
  refine ⟨hG1.1, hG1.2.trans ?_, hG2.1, hG2.2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Finset.sum_nonneg fun c _ => hweights c)
      hsum p) hBk
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Finset.sum_nonneg fun c _ => by positivity)
      hsumG p) hBk

end PointMoment2

/-! ### The regime facts at a reached point -/

section RegimeFacts

/-- Every reached point has `1/2 ≤ u` and `W^{-3} ≤ 1 - u`. -/
private lemma lemmaNOffset_cmpReach_time (R : PropRegime) (W : ℕ) :
    ∀ (d : ℕ) (p : FlowPt), CmpReach R.base W d p →
      1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u := by
  intro d p h
  induction h with
  | base hp => exact R.time W _ hp
  | earlier v _ hv1 hv2 ih => exact ⟨hv1, by have := ih.2; simp only; linarith⟩
  | cmp s _ hs1 hs2 ih => exact ⟨hs1, by have := ih.2; simp only [cmpPt]; linarith⟩
  | lift _ ih => exact ih

/-- `‖m‖ ≤ C` from the bound on the Dyson matrix. -/
private lemma lemmaNOffset_norm_mRoot_le {g E C : ℝ} {L : ℕ} (hL : 3 ≤ L) {m : ℂ}
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m)
    (hbd : ∀ a b, ‖dysonMat (hopB g) (gammaG g) L E m a b‖ ≤ C) : ‖m‖ ≤ C := by
  have hγ := lemmaNOffset_gammaG_pos g
  have hw : 0 < ((E : ℂ) + (gammaG g : ℂ) * m).im := by simpa using mul_pos hγ hm.1
  have hd := dysonMat_diag (hopB g) (gammaG g) L (by omega) E m hw ⟨0, by omega⟩
  rw [← hm.2] at hd
  have := hbd ⟨0, by omega⟩ ⟨0, by omega⟩
  rwa [hd] at this

/-- `ℓ_u ≥ 1` when `g ≥ 0` and `L ≥ 1`. -/
private lemma lemmaNOffset_ellProp_ge_one {g : ℝ} (hg : 0 ≤ g) {L : ℕ} (hL : 1 ≤ L) (t : ℝ) :
    1 ≤ ellProp g L t := by
  unfold ellProp
  refine le_min (by exact_mod_cast hL) ?_
  have : 0 ≤ g / Real.sqrt (gammaG g * (1 - t)) := div_nonneg hg (Real.sqrt_nonneg _)
  linarith

/-- The row and column sums of a kernel with the profile of (6.3) [fo:eq:kernel-bounds]. -/
private lemma lemmaNOffset_kernel_sum_le {L W : ℕ} (hW : 1 ≤ W) {K : Fin L → Fin L → ℝ}
    {C c ℓ u Cb : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hℓ : 1 ≤ ℓ) (hu : u < 1)
    (hK : ∀ y z, 0 ≤ K y z ∧ K y z ≤ C / ((1 - u) * ℓ) *
      Real.exp (-(c * (cycDist y z : ℝ) / ℓ)) + ℓ⁻¹ * (W : ℝ) ^ (-(1 : ℝ)))
    (hLℓ : (L : ℝ) / ℓ ≤ Cb) (htime : ((W : ℝ) ^ (-3 : ℝ)) ≤ 1 - u) :
    (∀ y, ∑ z, K y z ≤ Cb * (C * (W : ℝ) ^ 3 + 1)) ∧
      ∀ z, ∑ y, K y z ≤ Cb * (C * (W : ℝ) ^ 3 + 1) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hℓ0 : 0 < ℓ := by linarith
  have hu0 : 0 < 1 - u := by linarith
  have hW3 : (0 : ℝ) < (W : ℝ) ^ 3 := by positivity
  have hinv : (1 - u)⁻¹ ≤ (W : ℝ) ^ 3 := by
    have h1 : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
    have h2 := inv_anti₀ h1 htime
    rw [Real.rpow_neg hW0.le, inv_inv] at h2
    have e : (W : ℝ) ^ (3 : ℝ) = (W : ℝ) ^ 3 := by simp
    rwa [e] at h2
  have hbound : ∀ y z, K y z ≤ (C * (W : ℝ) ^ 3 + 1) * ℓ⁻¹ := by
    intro y z
    refine (hK y z).2.trans ?_
    have hexp : Real.exp (-(c * (cycDist y z : ℝ) / ℓ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ c * (cycDist y z : ℝ) / ℓ := by positivity
      linarith
    have hWm : (W : ℝ) ^ (-(1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
    have h1 : C / ((1 - u) * ℓ) * Real.exp (-(c * (cycDist y z : ℝ) / ℓ)) ≤
        C * (W : ℝ) ^ 3 * ℓ⁻¹ := by
      calc _ ≤ C / ((1 - u) * ℓ) * 1 := by gcongr
        _ = C * (1 - u)⁻¹ * ℓ⁻¹ := by rw [mul_one, div_eq_mul_inv, mul_inv]; ring
        _ ≤ C * (W : ℝ) ^ 3 * ℓ⁻¹ := by gcongr
    have h2 : ℓ⁻¹ * (W : ℝ) ^ (-(1 : ℝ)) ≤ 1 * ℓ⁻¹ := by
      rw [mul_comm]; gcongr
    linarith
  have hsum : ∀ s : Fin L → ℝ, (∀ y, s y ≤ (C * (W : ℝ) ^ 3 + 1) * ℓ⁻¹) →
      ∑ y, s y ≤ Cb * (C * (W : ℝ) ^ 3 + 1) := by
    intro s hs
    calc ∑ y, s y ≤ ∑ _y : Fin L, (C * (W : ℝ) ^ 3 + 1) * ℓ⁻¹ := Finset.sum_le_sum fun y _ => hs y
      _ = (L : ℝ) / ℓ * (C * (W : ℝ) ^ 3 + 1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      _ ≤ Cb * (C * (W : ℝ) ^ 3 + 1) := by gcongr
  exact ⟨fun y => hsum _ fun z => hbound y z, fun z => hsum _ fun y => hbound y z⟩

/-- The anchor point of the flow: the segment pair at the characteristic height has the resolvent
of the flow. -/
private lemma lemmaNOffset_segG_eq (W : ℕ) (x : FlowPt) (ω : Ω W x.L) :
    segG W (x, etaChar x.g (mRoot x.g x.L x.E) x.u) ω = flowG W x ω := by
  unfold segG flowG
  simp only
  rw [← im_zChar x.g x.E (mRoot x.g x.L x.E) x.u, Complex.re_add_im]

/-- The exponent bookkeeping of the moment bound: the point bound is at most `C_p W^{C₁ p}` with
`C₁ = C + 3 + 6 max(C₀, 1)`. -/
private lemma lemmaNOffset_final_arith {C C₀ Bn : ℝ} (hC : 1 ≤ C) (hBn : 0 ≤ Bn) {p : ℕ}
    (hp : 1 ≤ p) {W : ℕ} (hW : 1 ≤ W) :
    (4 * ((W : ℝ) ^ C * (C * (W : ℝ) ^ 3 + 1)) + 8 * W * (W : ℝ) ^ C) ^ p *
      (2 ^ (6 * p - 1) * (((W : ℝ) + 1) ^ (6 * p) +
        9 ^ (6 * p) * (Bn * (W : ℝ) ^ (C₀ * ((6 * p : ℕ) : ℝ))))) ≤
    (4 * C + 12) ^ p * (2 ^ (6 * p - 1) * (2 ^ (6 * p) + 9 ^ (6 * p) * Bn)) *
      (W : ℝ) ^ ((C + 3 + 6 * max C₀ 1) * p) := by
  have hw1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hw0 : (0 : ℝ) < W := by linarith
  set w : ℝ := (W : ℝ) with hwdef
  set κ : ℝ := max C₀ 1 with hκ
  have hκ1 : 1 ≤ κ := le_max_right _ _
  have hκC : C₀ ≤ κ := le_max_left _ _
  have hC0 : 0 ≤ C := by linarith
  set N : ℕ := 6 * p with hN
  have hN1 : 1 ≤ N := by omega
  have hwC : 0 < w ^ C := Real.rpow_pos_of_pos hw0 _
  have hw3 : 1 ≤ w ^ 3 := one_le_pow₀ hw1
  -- the weight
  have hA : 4 * (w ^ C * (C * w ^ 3 + 1)) + 8 * w * w ^ C ≤ (4 * C + 12) * (w ^ C * w ^ 3) := by
    have hw3' : w ≤ w ^ 3 := by
      calc w = w ^ 1 := (pow_one w).symm
        _ ≤ w ^ 3 := pow_le_pow_right₀ hw1 (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hw3 hwC.le, mul_le_mul_of_nonneg_left hw3' hwC.le]
  have hA0 : 0 ≤ 4 * (w ^ C * (C * w ^ 3 + 1)) + 8 * w * w ^ C := by positivity
  have e1 : w ^ C * w ^ 3 = w ^ (C + 3) := by rw [Real.rpow_add hw0]; simp
  have e2 : ∀ r : ℝ, (w ^ r) ^ p = w ^ (r * p) := fun r => by
    rw [Real.rpow_mul hw0.le, Real.rpow_natCast]
  have hAp : (4 * (w ^ C * (C * w ^ 3 + 1)) + 8 * w * w ^ C) ^ p ≤
      (4 * C + 12) ^ p * w ^ ((C + 3) * p) := by
    refine (pow_le_pow_left₀ hA0 hA p).trans (le_of_eq ?_)
    rw [mul_pow, e1, e2]
  -- the moment of `K^{6p}`
  have hexp1 : w ^ N ≤ w ^ (κ * N) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hw1 (by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith)
  have hexp2 : w ^ (C₀ * (N : ℝ)) ≤ w ^ (κ * N) :=
    Real.rpow_le_rpow_of_exponent_le hw1 (by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith)
  have hwk : 0 < w ^ (κ * N) := Real.rpow_pos_of_pos hw0 _
  have hB : (w + 1) ^ N + 9 ^ N * (Bn * w ^ (C₀ * (N : ℝ))) ≤
      (2 ^ N + 9 ^ N * Bn) * w ^ (κ * N) := by
    have h1 : (w + 1) ^ N ≤ 2 ^ N * w ^ (κ * N) := by
      calc (w + 1) ^ N ≤ (2 * w) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
        _ = 2 ^ N * w ^ N := mul_pow _ _ _
        _ ≤ 2 ^ N * w ^ (κ * N) := by gcongr
    have h2 : 9 ^ N * (Bn * w ^ (C₀ * (N : ℝ))) ≤ 9 ^ N * (Bn * w ^ (κ * N)) := by gcongr
    nlinarith
  have hBk : 2 ^ (N - 1) * ((w + 1) ^ N + 9 ^ N * (Bn * w ^ (C₀ * (N : ℝ)))) ≤
      2 ^ (N - 1) * (2 ^ N + 9 ^ N * Bn) * w ^ (κ * N) := by
    rw [mul_assoc]; gcongr
  have hexpo : w ^ ((C + 3) * p) * w ^ (κ * N) = w ^ ((C + 3 + 6 * κ) * p) := by
    rw [← Real.rpow_add hw0]
    congr 1
    simp only [hN]
    push_cast
    ring
  calc _ ≤ ((4 * C + 12) ^ p * w ^ ((C + 3) * p)) *
        (2 ^ (N - 1) * (2 ^ N + 9 ^ N * Bn) * w ^ (κ * N)) :=
        mul_le_mul hAp hBk (by positivity) (by positivity)
    _ = (4 * C + 12) ^ p * (2 ^ (N - 1) * (2 ^ N + 9 ^ N * Bn)) *
        (w ^ ((C + 3) * p) * w ^ (κ * N)) := by ring
    _ = _ := by rw [hexpo]

end RegimeFacts

section GenMoment

open scoped Matrix.Norms.L2Operator

/-- Moments of the generator and bracket of the mixed two-loop error at the reached points with
`ζ_u ≤ 1`, from the crude moments (5.33) [fo:eq:coarse-time-input], the regime bounds and (C.16)
[fo:eq:pair-error]: `E|𝒢D₂|^p, E|Γ(ℒ₂)|^p ≤ C_p W^{C₁p}` with `C₁` independent of `p`. -/
theorem lemmaNOffset_gen_moment (R : PropRegime) (I : PropInputs R.base R.J) :
    ∃ C₁ : ℝ, ∀ p : ℕ, 1 ≤ p → ∃ Cp : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ (d : ℕ) (x : FlowPt),
      d ≤ R.J → CmpReach R.base W d x → zetaProp x.g W x.L x.u ≤ 1 → ∀ a b : Fin x.L,
        Integrable (fun ω => ‖blockGen W x.L (gammaG x.g) (fun r N =>
            resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] r N -
              primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r ![a, b] ![true, false]) x.u
            (flowH x.g W x.L x.u ω)‖ ^ p) (μ W x.L) ∧
        ∫ ω, ‖blockGen W x.L (gammaG x.g) (fun r N =>
            resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] r N -
              primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r ![a, b] ![true, false]) x.u
            (flowH x.g W x.L x.u ω)‖ ^ p ∂(μ W x.L) ≤ Cp * (W : ℝ) ^ (C₁ * p) ∧
        Integrable (fun ω => ‖blockGamma W x.L (gammaG x.g)
            (resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] x.u)
            (resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] x.u)
            (flowH x.g W x.L x.u ω)‖ ^ p) (μ W x.L) ∧
        ∫ ω, ‖blockGamma W x.L (gammaG x.g)
            (resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] x.u)
            (resLoop x.g x.E (mRoot x.g x.L x.E) ![a, b] ![true, false] x.u)
            (flowH x.g W x.L x.u ω)‖ ^ p ∂(μ W x.L) ≤ Cp * (W : ℝ) ^ (C₁ * p) := by
  obtain ⟨C₀, hcrude⟩ := I.crude
  refine ⟨R.C + 3 + 6 * max C₀ 1, fun p hp => ?_⟩
  obtain ⟨Bn, W₁, hW₁⟩ := hcrude (6 * p) (by omega)
  obtain ⟨W₂, hW₂⟩ := R.dyson
  obtain ⟨W₃, hW₃⟩ := R.kernel 1 one_pos
  obtain ⟨W₄, hW₄⟩ := R.budget
  obtain ⟨W₅, hW₅⟩ := R.prim 2 1 one_pos
  refine ⟨(4 * R.C + 12) ^ p * (2 ^ (6 * p - 1) * (2 ^ (6 * p) + 9 ^ (6 * p) * max Bn 0)),
    max (max (max W₁ W₂) (max W₃ W₄)) (max W₅ (max 1 ⌈R.C⌉₊)), fun W hWW d x hd hreach hζ a b => ?_⟩
  simp only [max_le_iff] at hWW
  obtain ⟨⟨⟨hW1, hW2⟩, hW3, hW4⟩, hW5, hWone, hWceil⟩ := hWW
  have hWC : R.C ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWceil)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hWone
  have hC0 : 0 ≤ R.C := by linarith [R.one_le_C]
  obtain ⟨hL, hg, hroot, -, -, hbd, -, -⟩ := hW₂ W hW2 d x hd hreach
  obtain ⟨htime0, htime⟩ := lemmaNOffset_cmpReach_time R W d x hreach
  have hu1 : x.u < 1 := by
    have : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
    linarith
  have hmW : ‖mRoot x.g x.L x.E‖ ≤ W := (lemmaNOffset_norm_mRoot_le hL hroot hbd).trans hWC
  have hbud := hW₄ W hW4 d x hd hreach
  have hℓ := lemmaNOffset_ellProp_ge_one hg (by omega : 1 ≤ x.L) x.u
  have hLpos : (0 : ℝ) ≤ x.L := Nat.cast_nonneg _
  have hγ := lemmaNOffset_gammaG_pos x.g
  have hLℓ : (x.L : ℝ) / ellProp x.g x.L x.u ≤ (W : ℝ) ^ R.C := by
    have : 0 ≤ gammaG x.g * x.L := by positivity
    linarith
  have hγL : gammaG x.g * x.L ≤ (W : ℝ) ^ R.C := by
    have : 0 ≤ (x.L : ℝ) / ellProp x.g x.L x.u := by
      have : 0 < ellProp x.g x.L x.u := by linarith
      positivity
    linarith
  have hker := fun y z => hW₃ W hW3 d x hd hreach y z
  obtain ⟨hk1, hk2⟩ := lemmaNOffset_kernel_sum_le (L := x.L) (W := W) hWone (K := fun y z =>
    mixedKer (pairP (gammaG x.g) (dysonMat (hopB x.g) (gammaG x.g) x.L x.E
      (mRoot x.g x.L x.E))) x.u y z) hC0 R.c_pos hℓ hu1 hker hLℓ htime
  have hpr : ∀ y z : Fin x.L,
      ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u ![y, z] ![true, false]‖ ≤ W := by
    intro y z
    have h := hW₅ W hW5 d x hd hreach 2 le_rfl le_rfl ![y, z] ![true, false]
    refine h.trans ?_
    simp only [Real.rpow_one]
    simpa using mul_le_of_le_one_right hW0.le hζ
  have hadm : SegAdm R.base R.J W (x, etaChar x.g (mRoot x.g x.L x.E) x.u) :=
    ⟨d, hd, hreach, Or.inl rfl⟩
  have hcr : ∀ y z : Fin x.L, Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ (6 * p))
      (μ W x.L) ∧ ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ (6 * p) ∂(μ W x.L) ≤
        max Bn 0 * (W : ℝ) ^ (C₀ * ((6 * p : ℕ) : ℝ)) := by
    intro y z
    have h := hW₁ W hW1 _ hadm y z
    simp only [lemmaNOffset_segG_eq] at h
    refine ⟨h.1, h.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hW0.le _)
  have hpt := lemmaNOffset_gen_moment_point x W hWone hL hroot hmW (by linarith) hu1 hpr
    (S1 := (W : ℝ) ^ R.C * (R.C * (W : ℝ) ^ 3 + 1)) (S2 := (W : ℝ) ^ R.C)
    (fun y z => (hker y z).1) hk1 hk2 hγL hp hcr a b
  have hfin := lemmaNOffset_final_arith (C₀ := C₀) (Bn := max Bn 0) R.one_le_C
    (le_max_right _ _) hp hWone
  obtain ⟨i1, i2, i3, i4⟩ := hpt
  exact ⟨i1, i2.trans hfin, i3, i4.trans hfin⟩

end GenMoment

end LSBA
