import LSBA.Flow.Moment

/-!
# The moment comparison iterated on short subintervals

The moment comparison of Appendix C.3 [sec:gc-one-step] for a nonnegative field with multiplicative
rates on a good set and crude bounds off it, iterated on consecutive subintervals of `[0, 1/2]`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Jet data of the class -/

/-- Along a line, `e ↦ G(y + e v)` has first derivative `DG(y) v` at `0`. -/
private theorem momentIter_deriv_line {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℂ}
    {DG : (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℂ)} (hD : ∀ x, HasFDerivAt G (DG x) x) (y v : ι → ℝ) :
    deriv (fun e : ℝ => G (y + e • v)) 0 = DG y v := by
  have hl : HasDerivAt (fun e : ℝ => y + e • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have h := ((hD (y + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) hl)
  have h2 : HasDerivAt (fun e : ℝ => G (y + e • v)) (DG y v) 0 := by
    simpa [Function.comp_def] using h
  exact h2.deriv

/-- Along a line, `e ↦ G(y + e v)` has second derivative `D²G(y) v v` at `0`. -/
private theorem momentIter_iteratedDeriv_line {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℂ}
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
private theorem momentIter_slice {ι E : Type*} [TopologicalSpace E] {g : ℝ → (ι → ℝ) → E}
    {a b : ℝ} (hg : ContinuousOn (Function.uncurry g) (Set.Ioo a b ×ˢ Set.univ)) {r : ℝ}
    (hr : r ∈ Set.Ioo a b) : Continuous (g r) :=
  hg.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hr, trivial⟩

/-- For a member of the class and a time `u ∈ (a,b)`, `𝒢F u` and `Γ(F u, F u)` are continuous
and bounded in space. -/
private theorem momentIter_jet {ι : Type*} [Fintype ι] {F : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (hF : HeatClass F a b) {u : ℝ} (hu : u ∈ Set.Ioo a b) (σ2 : ℝ) :
    (Continuous (coordGen σ2 F u) ∧ ∃ C : ℝ, ∀ y, ‖coordGen σ2 F u y‖ ≤ C) ∧
      (Continuous (coordGamma σ2 (F u) (F u)) ∧
        ∃ C : ℝ, ∀ y, ‖coordGamma σ2 (F u) (F u) y‖ ≤ C) := by
  obtain ⟨-, -, ⟨Fu, hu', hcu, C₁, hC₁⟩, ⟨DF, D2F, hD, hD2, hcD, hcD2, C₂, hC₂⟩⟩ := hF
  have hei : ∀ i : ι, ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ ≤ 1 := fun i => by
    rw [Pi.norm_single]; simp
  have hDc : Continuous (DF u) := momentIter_slice hcD hu
  have hD2c : Continuous (D2F u) := momentIter_slice hcD2 hu
  have hFuc : Continuous (Fu u) := momentIter_slice hcu hu
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (hC₂ u hu 0).1
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
    exact momentIter_iteratedDeriv_line (hD u hu) (hD2 u hu) y _
  have hgam : ∀ y, coordGamma σ2 (F u) (F u) y =
      (σ2 : ℂ) * ∑ i, DF u y (Pi.single i 1) * star (DF u y (Pi.single i 1)) := by
    intro y
    simp only [coordGamma, momentIter_deriv_line (hD u hu)]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
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

/-! ### `L^n` norms -/

/-- The `L^n` seminorm as the real moment `(∫ ‖f‖^n)^{1/n}`. -/
private theorem momentIter_eLpNorm_eq {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} {n : ℕ} (hn : 1 ≤ n) (hf : MemLp f n μ) :
    eLpNorm f n μ = ENNReal.ofReal ((∫ x, ‖f x‖ ^ n ∂μ) ^ (1 / (n : ℝ))) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by simp; omega) (ENNReal.natCast_ne_top n)]
  simp [ENNReal.toReal_natCast, Real.rpow_natCast, one_div]

/-- A crude moment bound `∫ ‖g‖^n ≤ K^n` as an `L^n` bound. -/
private theorem momentIter_crude_le {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {g : α → E} {n : ℕ} (hn : 1 ≤ n) (hg : MemLp g n μ) {K : ℝ}
    (hK : 0 ≤ K) (h : ∫ x, ‖g x‖ ^ n ∂μ ≤ K ^ n) : eLpNorm g n μ ≤ ENNReal.ofReal K := by
  rw [momentIter_eLpNorm_eq hn hg]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (∫ x, ‖g x‖ ^ n ∂μ) ^ (1 / (n : ℝ)) ≤ (K ^ n) ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow (integral_nonneg fun x => by positivity) h (by positivity)
    _ = K := by rw [one_div, Real.pow_rpow_inv_natCast hK (by omega)]

/-- Hölder on a set: `‖1_T g‖_m ≤ ‖g‖_{2m} μ(T)^{1/(2m)}`. -/
private theorem momentIter_indicator_le {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {g : α → E} (hg : AEStronglyMeasurable g μ) {T : Set α}
    (hT : MeasurableSet T) (m m2 : ℕ) (hm : 1 ≤ m) (hm2 : m2 = 2 * m) :
    eLpNorm (T.indicator g) m μ ≤ eLpNorm g m2 μ * μ T ^ (1 / (m2 : ℝ)) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hT.nullMeasurableSet]
  have hle : (m : ℝ≥0∞) ≤ m2 := by exact_mod_cast (show m ≤ m2 by omega)
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hle hg.restrict).trans ?_
  rw [Measure.restrict_apply_univ]
  have hexp : 1 / (m : ℝ≥0∞).toReal - 1 / (m2 : ℝ≥0∞).toReal = 1 / (m2 : ℝ) := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    rw [ENNReal.toReal_natCast, ENNReal.toReal_natCast, hm2]
    push_cast
    field_simp
    ring
  rw [hexp]
  gcongr
  exact Measure.restrict_le_self

/-- The good-set/bad-set split of an `L^m` norm: if `‖g‖ ≤ c₁ f + c₀` off a measurable `T` with
`μ(T) ≤ δ`, `‖f‖_m ≤ L` and `‖g‖_{2m} ≤ K`, then `‖g‖_m ≤ c₁ L + c₀ + K δ^{1/(2m)}`. -/
private theorem momentIter_split {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] [NormedAddCommGroup E] {g : α → E} {f : α → ℝ}
    (hg : AEStronglyMeasurable g μ) (hf0 : ∀ x, 0 ≤ f x) {T : Set α} (hT : MeasurableSet T)
    {c₁ c₀ L K δ : ℝ} (hc₁ : 0 ≤ c₁) (hc₀ : 0 ≤ c₀) (hL : 0 ≤ L) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hgood : ∀ x, x ∉ T → ‖g x‖ ≤ c₁ * f x + c₀) (m m2 : ℕ) (hm : 1 ≤ m) (hm2 : m2 = 2 * m)
    (hTμ : μ T ≤ ENNReal.ofReal δ) (hfL : eLpNorm f m μ ≤ ENNReal.ofReal L)
    (hgK : eLpNorm g m2 μ ≤ ENNReal.ofReal K) :
    eLpNorm g m μ ≤ ENNReal.ofReal (c₁ * L + c₀ + K * δ ^ (1 / (m2 : ℝ))) := by
  have hm1 : (1 : ℝ≥0∞) ≤ m := by exact_mod_cast hm
  have hpt : ∀ x, ‖g x‖ ≤ ‖(((fun x => c₁ * f x) + (fun _ => c₀) +
      (fun x => ‖T.indicator g x‖) : α → ℝ)) x‖ := by
    intro x
    have h0 : 0 ≤ c₁ * f x + c₀ := add_nonneg (mul_nonneg hc₁ (hf0 x)) hc₀
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (add_nonneg h0 (norm_nonneg _))]
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx]; linarith
    · rw [Set.indicator_of_notMem hx, norm_zero, add_zero]; exact hgood x hx
  have h1 := eLpNorm_mono (p := (m : ℝ≥0∞)) hg hpt
  have h2 := eLpNorm_add_le (μ := μ) (p := (m : ℝ≥0∞))
    (f := (fun x => c₁ * f x) + (fun _ => c₀)) (g := fun x => ‖T.indicator g x‖) hm1
  have h3 := eLpNorm_add_le (μ := μ) (p := (m : ℝ≥0∞))
    (f := fun x => c₁ * f x) (g := fun _ => c₀) hm1
  have h4 : eLpNorm (fun x => c₁ * f x) m μ = ENNReal.ofReal c₁ * eLpNorm f m μ := by
    have := eLpNorm_const_smul c₁ f (m : ℝ≥0∞) μ
    rw [Real.enorm_of_nonneg hc₁] at this
    exact this
  have h5 : eLpNorm (fun _ : α => c₀) m μ = ENNReal.ofReal c₀ := by
    rw [eLpNorm_const' _ (by simp; omega) (ENNReal.natCast_ne_top m), measure_univ,
      ENNReal.one_rpow, mul_one, Real.enorm_of_nonneg hc₀]
  have h6 : eLpNorm (fun x => ‖T.indicator g x‖) m μ = eLpNorm (T.indicator g) m μ :=
    eLpNorm_norm _ (hg.indicator hT)
  have h7 := momentIter_indicator_le hg hT m m2 hm hm2
  have h8 : eLpNorm g m2 μ * μ T ^ (1 / (m2 : ℝ)) ≤
      ENNReal.ofReal K * ENNReal.ofReal δ ^ (1 / (m2 : ℝ)) := by
    gcongr
  rw [ENNReal.ofReal_rpow_of_nonneg hδ (by positivity), ← ENNReal.ofReal_mul hK] at h8
  calc eLpNorm g m μ
      ≤ eLpNorm (fun x => c₁ * f x) m μ + eLpNorm (fun _ : α => c₀) m μ +
          eLpNorm (fun x => ‖T.indicator g x‖) m μ := h1.trans (h2.trans (add_le_add h3 le_rfl))
    _ ≤ ENNReal.ofReal c₁ * ENNReal.ofReal L + ENNReal.ofReal c₀ +
          ENNReal.ofReal (K * δ ^ (1 / (m2 : ℝ))) := by
        rw [h4, h5, h6]
        gcongr
        exact h7.trans h8
    _ = ENNReal.ofReal (c₁ * L + c₀ + K * δ ^ (1 / (m2 : ℝ))) := by
        rw [← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_add (mul_nonneg hc₁ hL) hc₀,
          ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hc₁ hL) hc₀)
            (mul_nonneg hK (Real.rpow_nonneg hδ _))]

/-- `(I^{1/(2p)})² = I^{1/p}` for `I ≥ 0`. -/
private theorem momentIter_sq_rpow {I : ℝ} (hI : 0 ≤ I) (p : ℕ) (hp : 1 ≤ p) :
    (I ^ (1 / (2 * (p : ℝ)))) ^ 2 = I ^ (1 / (p : ℝ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hI]
  congr 1
  push_cast
  field_simp

/-- A nonnegative function bounded by `c` has `L^k` norm at most `c` under a probability
measure. -/
private theorem momentIter_moment_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {g : α → ℝ} (hg0 : ∀ x, 0 ≤ g x) {c : ℝ} (hc : 0 ≤ c)
    (hgc : ∀ x, g x ≤ c) (k : ℕ) (hk : 1 ≤ k) : (∫ x, g x ^ k ∂μ) ^ (1 / (k : ℝ)) ≤ c := by
  have h1 : ∫ x, g x ^ k ∂μ ≤ c ^ k := by
    have := integral_mono_of_nonneg (μ := μ) (f := fun x => g x ^ k) (g := fun _ => c ^ k)
      (ae_of_all _ fun x => pow_nonneg (hg0 x) k) (integrable_const _)
      (ae_of_all _ fun x => pow_le_pow_left₀ (hg0 x) (hgc x) k)
    simpa using this
  calc (∫ x, g x ^ k ∂μ) ^ (1 / (k : ℝ)) ≤ (c ^ k) ^ (1 / (k : ℝ)) :=
        Real.rpow_le_rpow (integral_nonneg fun x => pow_nonneg (hg0 x) k) h1 (by positivity)
    _ = c := by
        rw [one_div, Real.pow_rpow_inv_natCast hc (by omega)]

/-! ### The moment comparison on one interval with a good set -/

/-- The moment comparison of Appendix C.3 [sec:gc-one-step] on one interval `[s, t]` for a
nonnegative field `X` in the heat class, with rates on a good set: if, off a set `Bad u` of Gaussian
measure at most `δ_b`, `|𝒢X| ≤ α(u) X + β(u)` and `Γ(X, X) ≤ a₂(u) X² + b₀(u)`, the `L^{4p}` norm of
`𝒢X` and the `L^{2p}` norm of `Γ(X, X)` are at most `K`, and `‖X_u‖_{2p} ≤ M` on `(s, t)`, then
`‖X_t‖_{2p} ≤ (‖X_s‖²_{2p} + (2p - 1)∫_s^t (a₂M² + b₀ + Kδ_b^{1/(2p)}))^{1/2} + ∫_s^t (αM + β +
Kδ_b^{1/(4p)})`. -/
theorem momentIter_step {ι : Type*} [Fintype ι] (σ2 : ℝ) (hσ2 : 0 ≤ σ2) (X : ℝ → (ι → ℝ) → ℝ)
    {a b s t : ℝ} (ha : a < 0) (hs : 0 ≤ s) (hst : s ≤ t) (htb : t < b)
    (hX : HeatClass (fun r y => ((X r y : ℝ) : ℂ)) a b) (hX0 : ∀ r y, 0 ≤ X r y)
    (p : ℕ) (hp : 1 ≤ p) {K δb M : ℝ} (hK : 0 ≤ K) (hδb : 0 ≤ δb) (hM0 : 0 ≤ M)
    (α β a₂ b₀ : ℝ → ℝ) (hα : ContinuousOn α (Set.Icc s t)) (hβ : ContinuousOn β (Set.Icc s t))
    (ha₂ : ContinuousOn a₂ (Set.Icc s t)) (hb₀ : ContinuousOn b₀ (Set.Icc s t))
    (hα0 : ∀ u ∈ Set.Icc s t, 0 ≤ α u) (hβ0 : ∀ u ∈ Set.Icc s t, 0 ≤ β u)
    (ha₂0 : ∀ u ∈ Set.Icc s t, 0 ≤ a₂ u) (hb₀0 : ∀ u ∈ Set.Icc s t, 0 ≤ b₀ u)
    (Bad : ℝ → Set (ι → ℝ))
    (hbad : ∀ u ∈ Set.Ioo s t,
      stdGauss ι {x | Real.sqrt (u * σ2) • x ∈ Bad u} ≤ ENNReal.ofReal δb)
    (hrate : ∀ u ∈ Set.Ioo s t, ∀ y, y ∉ Bad u →
      ‖coordGen σ2 (fun r z => ((X r z : ℝ) : ℂ)) u y‖ ≤ α u * X u y + β u ∧
      ‖coordGamma σ2 (fun z => ((X u z : ℝ) : ℂ)) (fun z => ((X u z : ℝ) : ℂ)) y‖ ≤
        a₂ u * X u y ^ 2 + b₀ u)
    (hcrude : ∀ u ∈ Set.Ioo s t,
      ∫ x, ‖coordGen σ2 (fun r z => ((X r z : ℝ) : ℂ)) u (Real.sqrt (u * σ2) • x)‖ ^ (4 * p)
          ∂(stdGauss ι) ≤ K ^ (4 * p) ∧
      ∫ x, ‖coordGamma σ2 (fun z => ((X u z : ℝ) : ℂ)) (fun z => ((X u z : ℝ) : ℂ))
          (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι) ≤ K ^ (2 * p))
    (hM : ∀ u ∈ Set.Ioo s t,
      (∫ x, X u (Real.sqrt (u * σ2) • x) ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) ≤ M) :
    (∫ x, X t (Real.sqrt (t * σ2) • x) ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) ≤
      Real.sqrt ((∫ x, X s (Real.sqrt (s * σ2) • x) ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (p : ℝ)) +
          (2 * p - 1) * ∫ u in s..t, (a₂ u * M ^ 2 + b₀ u + K * δb ^ (1 / (2 * (p : ℝ))))) +
        ∫ u in s..t, (α u * M + β u + K * δb ^ (1 / (4 * (p : ℝ)))) := by
  have hnorm : ∀ r z, ‖((X r z : ℝ) : ℂ)‖ = X r z := fun r z => by
    rw [Complex.norm_real, Real.norm_of_nonneg (hX0 r z)]
  have hint : ∀ r, (∫ x, ‖((X r (Real.sqrt (r * σ2) • x) : ℝ) : ℂ)‖ ^ (2 * p) ∂(stdGauss ι)) =
      ∫ x, X r (Real.sqrt (r * σ2) • x) ^ (2 * p) ∂(stdGauss ι) := fun r => by
    simp only [hnorm]
  have hδ4 : 0 ≤ δb ^ (1 / (4 * (p : ℝ))) := Real.rpow_nonneg hδb _
  have hδ2 : 0 ≤ δb ^ (1 / (2 * (p : ℝ))) := Real.rpow_nonneg hδb _
  have hc4 : ((4 * p : ℕ) : ℝ) = 4 * (p : ℝ) := by push_cast; ring
  have hc2 : ((2 * p : ℕ) : ℝ) = 2 * (p : ℝ) := by push_cast; ring
  have hcp : 1 ≤ 2 * p := by omega
  -- the data at one time `u ∈ (s, t)`
  have data : ∀ u ∈ Set.Ioo s t,
      (∫ x, ‖coordGen σ2 (fun r z => ((X r z : ℝ) : ℂ)) u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p)
          ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) ≤ α u * M + β u + K * δb ^ (1 / (4 * (p : ℝ))) ∧
      (∫ x, ‖coordGamma σ2 (fun z => ((X u z : ℝ) : ℂ)) (fun z => ((X u z : ℝ) : ℂ))
          (Real.sqrt (u * σ2) • x)‖ ^ p ∂(stdGauss ι)) ^ (1 / (p : ℝ)) ≤
        a₂ u * M ^ 2 + b₀ u + K * δb ^ (1 / (2 * (p : ℝ))) := by
    intro u hu
    have hu' : u ∈ Set.Icc s t := Set.Ioo_subset_Icc_self hu
    have hua : u ∈ Set.Ioo a b := ⟨ha.trans_le (hs.trans hu'.1), hu'.2.trans_lt htb⟩
    obtain ⟨⟨hGc, CG, hCG⟩, ⟨hΓc, CΓ, hCΓ⟩⟩ := momentIter_jet hX hua σ2
    obtain ⟨CX, hCX⟩ := hX.bdd
    have hYc : Continuous (fun z => ((X u z : ℝ) : ℂ)) := momentIter_slice hX.cont hua
    have hXc : Continuous (X u) := by
      have := Complex.continuous_re.comp hYc
      simpa [Function.comp_def] using this
    set S : ℝ := Real.sqrt (u * σ2) with hS
    have hSc : Continuous (fun x : ι → ℝ => S • x) := continuous_const_smul S
    set T : Set (ι → ℝ) := toMeasurable (stdGauss ι) {x | S • x ∈ Bad u} with hTdef
    have hT : MeasurableSet T := measurableSet_toMeasurable _ _
    have hTμ : stdGauss ι T ≤ ENNReal.ofReal δb := by
      rw [hTdef, measure_toMeasurable]; exact hbad u hu
    have hTsub : ∀ x, x ∉ T → S • x ∉ Bad u := fun x hx h => hx (subset_toMeasurable _ _ h)
    -- the field
    set f : (ι → ℝ) → ℝ := fun x => X u (S • x) with hf
    have hfc : Continuous f := hXc.comp hSc
    have hf0 : ∀ x, 0 ≤ f x := fun x => hX0 _ _
    have hfb : ∀ x, ‖f x‖ ≤ CX := fun x => by
      have := hCX u hua (S • x)
      rw [hnorm] at this
      rwa [Real.norm_of_nonneg (hf0 x)]
    set N : ℝ := (∫ x, X u (S • x) ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) with hN
    have hI0 : 0 ≤ ∫ x, X u (S • x) ^ (2 * p) ∂(stdGauss ι) :=
      integral_nonneg fun x => pow_nonneg (hX0 _ _) _
    have hN0 : 0 ≤ N := Real.rpow_nonneg hI0 _
    have hNM : N ≤ M := hM u hu
    have hfL : eLpNorm f (2 * p : ℕ) (stdGauss ι) ≤ ENNReal.ofReal N := by
      rw [momentIter_eLpNorm_eq hcp (MemLp.of_bound hfc.aestronglyMeasurable CX
        (ae_of_all _ hfb)), hc2]
      refine le_of_eq ?_
      congr 2
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [hf, Real.norm_of_nonneg (hX0 _ _)]
    have hf2L : eLpNorm (fun x => f x ^ 2) p (stdGauss ι) ≤ ENNReal.ofReal (N ^ 2) := by
      rw [momentIter_eLpNorm_eq hp (MemLp.of_bound (f := fun x => f x ^ 2)
        (hfc.pow 2).aestronglyMeasurable (CX ^ 2)
        (ae_of_all _ fun x => by
          rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hfb x) 2)),
        hN, momentIter_sq_rpow hI0 p hp]
      refine le_of_eq ?_
      congr 2
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [hf, Real.norm_of_nonneg (sq_nonneg _), ← pow_mul]
    -- generator
    set g : (ι → ℝ) → ℂ := fun x => coordGen σ2 (fun r z => ((X r z : ℝ) : ℂ)) u (S • x)
      with hg
    have hgc : Continuous g := hGc.comp hSc
    have hgm : ∀ n : ℕ, MemLp g n (stdGauss ι) := fun n =>
      MemLp.of_bound hgc.aestronglyMeasurable CG (ae_of_all _ fun x => hCG _)
    have hgK : eLpNorm g (4 * p : ℕ) (stdGauss ι) ≤ ENNReal.ofReal K :=
      momentIter_crude_le (by omega) (hgm _) hK (hcrude u hu).1
    have hgsplit := momentIter_split (μ := stdGauss ι) hgc.aestronglyMeasurable hf0 hT
      (hα0 u hu') (hβ0 u hu') hN0 hK hδb (fun x hx => (hrate u hu _ (hTsub x hx)).1)
      (2 * p) (4 * p) hcp (by ring) hTμ hfL hgK
    rw [momentIter_eLpNorm_eq hcp (hgm _), hc4, hc2] at hgsplit
    have hA0 : 0 ≤ α u * N + β u + K * δb ^ (1 / (4 * (p : ℝ))) :=
      add_nonneg (add_nonneg (mul_nonneg (hα0 u hu') hN0) (hβ0 u hu')) (mul_nonneg hK hδ4)
    rw [ENNReal.ofReal_le_ofReal_iff hA0] at hgsplit
    -- carré du champ
    set G : (ι → ℝ) → ℂ := fun x => coordGamma σ2 (fun z => ((X u z : ℝ) : ℂ))
      (fun z => ((X u z : ℝ) : ℂ)) (S • x) with hG
    have hGc' : Continuous G := hΓc.comp hSc
    have hGm : ∀ n : ℕ, MemLp G n (stdGauss ι) := fun n =>
      MemLp.of_bound hGc'.aestronglyMeasurable CΓ (ae_of_all _ fun x => hCΓ _)
    have hGK : eLpNorm G (2 * p : ℕ) (stdGauss ι) ≤ ENNReal.ofReal K :=
      momentIter_crude_le hcp (hGm _) hK (hcrude u hu).2
    have hGsplit := momentIter_split (μ := stdGauss ι) (f := fun x => f x ^ 2)
      hGc'.aestronglyMeasurable (fun x => sq_nonneg _) hT
      (ha₂0 u hu') (hb₀0 u hu') (sq_nonneg N) hK hδb (fun x hx => (hrate u hu _ (hTsub x hx)).2)
      p (2 * p) hp rfl hTμ hf2L hGK
    rw [momentIter_eLpNorm_eq hp (hGm _), hc2] at hGsplit
    have hB0 : 0 ≤ a₂ u * N ^ 2 + b₀ u + K * δb ^ (1 / (2 * (p : ℝ))) :=
      add_nonneg (add_nonneg (mul_nonneg (ha₂0 u hu') (sq_nonneg _)) (hb₀0 u hu'))
        (mul_nonneg hK hδ2)
    rw [ENNReal.ofReal_le_ofReal_iff hB0] at hGsplit
    refine ⟨hgsplit.trans ?_, hGsplit.trans ?_⟩
    · gcongr
      exact hα0 u hu'
    · gcongr
      exact ha₂0 u hu'
  have key := lemmaM_gaussian σ2 hσ2 (fun r z => ((X r z : ℝ) : ℂ)) ha hs hst htb hX p hp
    (fun u => α u * M + β u + K * δb ^ (1 / (4 * (p : ℝ))))
    (fun u => a₂ u * M ^ 2 + b₀ u + K * δb ^ (1 / (2 * (p : ℝ))))
    (((hα.mul continuousOn_const).add hβ).add continuousOn_const)
    (((ha₂.mul continuousOn_const).add hb₀).add continuousOn_const)
    (fun u hu => add_nonneg (add_nonneg (mul_nonneg (hα0 u hu) hM0) (hβ0 u hu))
      (mul_nonneg hK hδ4))
    (fun u hu => add_nonneg (add_nonneg (mul_nonneg (ha₂0 u hu) (sq_nonneg _)) (hb₀0 u hu))
      (mul_nonneg hK hδ2))
    (fun u hu => (data u hu).1) (fun u hu => (data u hu).2)
  rw [hint, hint] at key
  exact key

/-! ### Iteration -/

/-- The arithmetic of one step: with `h (8κ) ≤ 1` and `4 b_Γ P ≤ κ`, the bound of
`momentIter_step` at rates `2κ`, `2b_Γ` gives `N' ≤ N_s + Ñ/2 + (P + 1 + K) δ'/2`. -/
private theorem momentIter_arith {Ns Nt Nt' h P bΓ κ K δ : ℝ} (hP1 : 1 ≤ P) (hκ : 1 ≤ κ)
    (hPb : bΓ * (4 * P) ≤ κ) (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hNs : 0 ≤ Ns)
    (hNt : 0 ≤ Nt) (hh0 : 0 ≤ h) (hh : h * (8 * κ) ≤ 1)
    (h1 : Nt' ≤ Real.sqrt (Ns ^ 2 + P * (h * (2 * bΓ * Nt ^ 2 + K * δ ^ 2))) +
      h * (2 * κ * Nt + K * δ)) :
    Nt' ≤ Ns + Nt / 2 + (P + 1 + K) * δ / 2 := by
  have hi : P * (2 * bΓ) * h ≤ 1 / 16 := by
    have g1 : P * (2 * bΓ) * h = (bΓ * (4 * P)) * h / 2 := by ring
    have g2 := mul_le_mul_of_nonneg_right hPb hh0
    rw [g1]
    nlinarith
  have hh8 : h ≤ 1 / 8 := by nlinarith
  set d : ℝ := δ * (P / 2 + K / 16) with hd
  have hd0 : 0 ≤ d := mul_nonneg hδ (by positivity)
  have hW : 0 ≤ Ns + Nt / 4 + d := by positivity
  have e1 : P * (h * (2 * bΓ * Nt ^ 2)) ≤ Nt ^ 2 / 16 := by
    have := mul_le_mul_of_nonneg_right hi (sq_nonneg Nt)
    calc P * (h * (2 * bΓ * Nt ^ 2)) = P * (2 * bΓ) * h * Nt ^ 2 := by ring
      _ ≤ 1 / 16 * Nt ^ 2 := this
      _ = Nt ^ 2 / 16 := by ring
  have e2 : P * (h * (K * δ ^ 2)) ≤ d ^ 2 := by
    have hPK : 0 ≤ P * K := mul_nonneg (by linarith) hK
    have f1 : P * h * K ≤ P * K / 8 := by
      have := mul_le_mul_of_nonneg_left hh8 hPK
      calc P * h * K = P * K * h := by ring
        _ ≤ P * K * (1 / 8) := this
        _ = P * K / 8 := by ring
    have f2 : P * K / 8 ≤ (P / 2 + K / 16) ^ 2 := by nlinarith [sq_nonneg (P / 2 - K / 16)]
    have f3 := mul_le_mul_of_nonneg_right (f1.trans f2) (sq_nonneg δ)
    calc P * (h * (K * δ ^ 2)) = P * h * K * δ ^ 2 := by ring
      _ ≤ (P / 2 + K / 16) ^ 2 * δ ^ 2 := f3
      _ = d ^ 2 := by rw [hd]; ring
  have hsq : Real.sqrt (Ns ^ 2 + P * (h * (2 * bΓ * Nt ^ 2 + K * δ ^ 2))) ≤ Ns + Nt / 4 + d := by
    calc Real.sqrt (Ns ^ 2 + P * (h * (2 * bΓ * Nt ^ 2 + K * δ ^ 2)))
        ≤ Real.sqrt ((Ns + Nt / 4 + d) ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          have ex : (Ns + Nt / 4 + d) ^ 2 = Ns ^ 2 + Nt ^ 2 / 16 + d ^ 2 +
              (Ns * Nt / 2 + 2 * (Ns * d) + Nt * d / 2) := by ring
          have ex2 : P * (h * (2 * bΓ * Nt ^ 2 + K * δ ^ 2)) =
              P * (h * (2 * bΓ * Nt ^ 2)) + P * (h * (K * δ ^ 2)) := by ring
          rw [ex, ex2]
          have : 0 ≤ Ns * Nt / 2 + 2 * (Ns * d) + Nt * d / 2 := by positivity
          linarith
      _ = Ns + Nt / 4 + d := Real.sqrt_sq hW
  have e3 : h * (2 * κ * Nt + K * δ) ≤ Nt / 4 + K * δ / 8 := by
    have g1 : h * κ ≤ 1 / 8 := by linarith
    have g2 := mul_le_mul_of_nonneg_right g1 hNt
    have g3 := mul_le_mul_of_nonneg_right hh8 (mul_nonneg hK hδ)
    have ex : h * (2 * κ * Nt + K * δ) = 2 * (h * κ * Nt) + h * (K * δ) := by ring
    rw [ex]
    linarith
  have e4 : d + K * δ / 8 ≤ (P + 1 + K) * δ / 2 := by
    have ex : (P + 1 + K) * δ / 2 - (d + K * δ / 8) = δ / 2 + 5 * (K * δ) / 16 := by
      rw [hd]; ring
    have : 0 ≤ K * δ := mul_nonneg hK hδ
    linarith
  linarith

/-- The moment comparison of Appendix C.3 [sec:gc-one-step] iterated on `⌈4κ⌉` consecutive
subintervals of `[0, v] ⊆ [0, 1/2]`, for a nonnegative field `X` in the heat class: if, off a set
`Bad u` of Gaussian measure at most `δ_b`, `|𝒢X| ≤ κ X/(1 - u)` and `Γ(X, X) ≤ b_Γ X²/(1 - u)` with
`4 b_Γ (2p - 1) ≤ κ`, and the `L^{4p}` and `L^{2p}` norms of `𝒢X` and `Γ(X, X)` are at most `K`,
then `‖X_v‖_{2p} ≤ 2^{⌈4κ⌉+1} (X_0(0) + (2p + K) δ_b^{1/(4p)})`. -/
theorem lemmaM_iter {ι : Type*} [Fintype ι] (σ2 : ℝ) (hσ2 : 0 ≤ σ2) (X : ℝ → (ι → ℝ) → ℝ)
    {a b v : ℝ} (ha : a < 0) (hv : 0 < v) (hv1 : v ≤ 1 / 2) (hvb : v < b)
    (hX : HeatClass (fun r y => ((X r y : ℝ) : ℂ)) a b) (hX0 : ∀ r y, 0 ≤ X r y)
    (p : ℕ) (hp : 1 ≤ p) {κ bΓ K δb : ℝ} (hκ : 1 ≤ κ) (hbΓ : 0 ≤ bΓ)
    (hbΓκ : bΓ * (4 * (2 * p - 1)) ≤ κ) (hK : 0 ≤ K) (hδb : 0 ≤ δb) (Bad : ℝ → Set (ι → ℝ))
    (hbad : ∀ u ∈ Set.Ioo 0 v,
      stdGauss ι {x | Real.sqrt (u * σ2) • x ∈ Bad u} ≤ ENNReal.ofReal δb)
    (hrate : ∀ u ∈ Set.Ioo 0 v, ∀ y, y ∉ Bad u →
      ‖coordGen σ2 (fun t z => ((X t z : ℝ) : ℂ)) u y‖ ≤ κ * X u y / (1 - u) ∧
      ‖coordGamma σ2 (fun z => ((X u z : ℝ) : ℂ)) (fun z => ((X u z : ℝ) : ℂ)) y‖ ≤
        bΓ * X u y ^ 2 / (1 - u))
    (hcrude : ∀ u ∈ Set.Ioo 0 v,
      ∫ x, ‖coordGen σ2 (fun t z => ((X t z : ℝ) : ℂ)) u (Real.sqrt (u * σ2) • x)‖ ^ (4 * p)
          ∂(stdGauss ι) ≤ K ^ (4 * p) ∧
      ∫ x, ‖coordGamma σ2 (fun z => ((X u z : ℝ) : ℂ)) (fun z => ((X u z : ℝ) : ℂ))
          (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι) ≤ K ^ (2 * p)) :
    (∫ x, X v (Real.sqrt (v * σ2) • x) ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) ≤
      2 ^ (⌈4 * κ⌉₊ + 1) * (X 0 0 + (2 * p + K) * δb ^ (1 / (4 * (p : ℝ)))) := by
  set N : ℝ → ℝ := fun u =>
    (∫ x, X u (Real.sqrt (u * σ2) • x) ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) with hN
  set δ' : ℝ := δb ^ (1 / (4 * (p : ℝ))) with hδ'
  set c : ℝ := (2 * p + K) * δ' with hc
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hδ'0 : 0 ≤ δ' := Real.rpow_nonneg hδb _
  have hc0 : 0 ≤ c := mul_nonneg (by positivity) hδ'0
  have hδ2 : δb ^ (1 / (2 * (p : ℝ))) = δ' ^ 2 := by
    rw [hδ']
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδb]
    congr 1
    push_cast
    field_simp
    ring
  have hI0 : ∀ u, 0 ≤ ∫ x, X u (Real.sqrt (u * σ2) • x) ^ (2 * p) ∂(stdGauss ι) :=
    fun u => integral_nonneg fun x => pow_nonneg (hX0 _ _) _
  have hN0 : ∀ u, 0 ≤ N u := fun u => Real.rpow_nonneg (hI0 u) _
  -- `N` is bounded on the window
  obtain ⟨C, hC⟩ := hX.bdd
  have hab0 : (0 : ℝ) ∈ Set.Ioo a b := ⟨ha, hv.trans hvb⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 hab0 0)
  have hNC : ∀ u ∈ Set.Ioo a b, N u ≤ C := by
    intro u hu
    refine momentIter_moment_le (fun x => hX0 _ _) hC0 (fun x => ?_) (2 * p) (by omega) |>.trans_eq'
      (by simp only [hN]; push_cast; ring_nf)
    have := hC u hu (Real.sqrt (u * σ2) • x)
    rwa [Complex.norm_real, Real.norm_of_nonneg (hX0 _ _)] at this
  -- one step of length at most `1/(8κ)` doubles `N` up to `c`
  have step : ∀ s t, 0 ≤ s → s ≤ t → t ≤ v → t - s ≤ 1 / (8 * κ) → N t ≤ 2 * N s + c := by
    intro s t hs hst htv hh
    have hIcc : ∀ u ∈ Set.Icc s t, u ∈ Set.Ioo a b := fun u hu =>
      ⟨ha.trans_le (hs.trans hu.1), (hu.2.trans htv).trans_lt hvb⟩
    have hbdd : BddAbove (N '' Set.Icc s t) :=
      ⟨C, by rintro _ ⟨u, hu, rfl⟩; exact hNC u (hIcc u hu)⟩
    have hne : (N '' Set.Icc s t).Nonempty := ⟨N s, s, ⟨le_rfl, hst⟩, rfl⟩
    set Nt : ℝ := sSup (N '' Set.Icc s t) with hNt
    have hle : ∀ u ∈ Set.Icc s t, N u ≤ Nt := fun u hu => le_csSup hbdd ⟨u, hu, rfl⟩
    have hNt0 : 0 ≤ Nt := (hN0 s).trans (hle s ⟨le_rfl, hst⟩)
    have hall : ∀ t' ∈ Set.Icc s t, N t' ≤ N s + Nt / 2 + c / 2 := by
      intro t' ht'
      have hsub : ∀ u ∈ Set.Ioo s t', u ∈ Set.Ioo 0 v := fun u hu =>
        ⟨hs.trans_lt hu.1, hu.2.trans_le (ht'.2.trans htv)⟩
      have h1 := momentIter_step σ2 hσ2 X ha hs ht'.1 ((ht'.2.trans htv).trans_lt hvb) hX hX0 p hp
        hK hδb hNt0 (fun _ => 2 * κ) (fun _ => 0) (fun _ => 2 * bΓ) (fun _ => 0)
        continuousOn_const continuousOn_const continuousOn_const continuousOn_const
        (fun _ _ => by positivity) (fun _ _ => le_rfl) (fun _ _ => by positivity)
        (fun _ _ => le_rfl) Bad (fun u hu => hbad u (hsub u hu))
        (fun u hu y hy => by
          have hu0 := hsub u hu
          have hu1 : 0 < 1 - u := by linarith [hu0.2]
          have hu2 : u ≤ 1 / 2 := by linarith [hu0.2]
          obtain ⟨r1, r2⟩ := hrate u hu0 y hy
          have hXy := hX0 u y
          refine ⟨r1.trans ?_, r2.trans ?_⟩
          · rw [div_le_iff₀ hu1]
            nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ κ) hXy]
          · rw [div_le_iff₀ hu1]
            nlinarith [mul_nonneg hbΓ (sq_nonneg (X u y))])
        (fun u hu => hcrude u (hsub u hu)) (fun u hu => hle u ⟨hu.1.le, hu.2.le.trans ht'.2⟩)
      simp only [intervalIntegral.integral_const, smul_eq_mul, add_zero] at h1
      rw [momentIter_sq_rpow (hI0 s) p hp |>.symm, hδ2] at h1
      change N t' ≤ Real.sqrt (N s ^ 2 + (2 * p - 1) * ((t' - s) * (2 * bΓ * Nt ^ 2 +
        K * δ' ^ 2))) + (t' - s) * (2 * κ * Nt + K * δ') at h1
      have hh'le : (t' - s) * (8 * κ) ≤ 1 := by
        have : t' - s ≤ 1 / (8 * κ) := by linarith [ht'.2]
        rwa [le_div_iff₀ (by positivity)] at this
      have := momentIter_arith (P := 2 * p - 1) (by linarith) hκ hbΓκ hK hδ'0 (hN0 s) hNt0
        (by linarith [ht'.1]) hh'le h1
      refine this.trans_eq ?_
      rw [hc]; ring
    have hNt : Nt ≤ N s + Nt / 2 + c / 2 := by
      refine csSup_le hne ?_
      rintro _ ⟨u, hu, rfl⟩
      exact hall u hu
    have := hle t ⟨hst, le_rfl⟩
    linarith
  -- iteration over `⌈4κ⌉` steps
  set n : ℕ := ⌈4 * κ⌉₊ with hn
  have hn4 : 4 * κ ≤ n := Nat.le_ceil _
  have hnpos : (0 : ℝ) < n := by linarith
  set h : ℝ := v / n with hhdef
  have hh0 : 0 ≤ h := by positivity
  have hh8 : h ≤ 1 / (8 * κ) := by
    rw [hhdef, div_le_div_iff₀ hnpos (by positivity)]; nlinarith
  have iter : ∀ j : ℕ, j ≤ n → N (j * h) ≤ 2 ^ j * N 0 + (2 ^ j - 1) * c := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
      have hdiff : ((j + 1 : ℕ) : ℝ) * h - j * h = h := by push_cast; ring
      have hs := step (j * h) ((j + 1 : ℕ) * h) (by positivity)
        (by push_cast; nlinarith) (by
          push_cast
          rw [hhdef, mul_div_assoc', div_le_iff₀ hnpos]
          nlinarith) (by rw [hdiff]; exact hh8)
      have := ih (by omega)
      rw [pow_succ]
      nlinarith
  have hv' : (n : ℝ) * h = v := by rw [hhdef]; field_simp
  have hfin := iter n le_rfl
  rw [hv'] at hfin
  have hN00 : N 0 = X 0 0 := by
    have h2p : ((2 * p : ℕ) : ℝ) = 2 * (p : ℝ) := by push_cast; ring
    simp only [hN, zero_mul, Real.sqrt_zero, zero_smul, integral_const, probReal_univ,
      one_smul]
    rw [← h2p, one_div, Real.pow_rpow_inv_natCast (hX0 0 0) (by omega)]
  rw [hN00] at hfin
  have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hX00 := hX0 0 0
  calc N v ≤ 2 ^ n * X 0 0 + (2 ^ n - 1) * c := hfin
    _ ≤ 2 ^ (n + 1) * (X 0 0 + c) := by
      rw [pow_succ]; nlinarith

/-! ### The moment comparison for a complex field with additive good-set bounds -/

/-- The moment comparison of Appendix C.3 [sec:gc-one-step] on one interval `[s, t]` for a complex
field `Y` in the heat class, with deterministic bounds on a good set: if, off a set `Bad u` of
Gaussian measure at most `δ_b`, `|𝒢Y| ≤ β(u)` and `Γ(Y, Y) ≤ b₀(u)`, and the `L^{4p}` norm of `𝒢Y`
and the `L^{2p}` norm of `Γ(Y, Y)` are at most `K`, then
`‖Y_t‖_{2p} ≤ (‖Y_s‖²_{2p} + (2p - 1)∫_s^t (b₀ + Kδ_b^{1/(2p)}))^{1/2} + ∫_s^t (β +
Kδ_b^{1/(4p)})`. -/
theorem momentIter_step' {ι : Type*} [Fintype ι] (σ2 : ℝ) (hσ2 : 0 ≤ σ2) (Y : ℝ → (ι → ℝ) → ℂ)
    {a b s t : ℝ} (ha : a < 0) (hs : 0 ≤ s) (hst : s ≤ t) (htb : t < b) (hY : HeatClass Y a b)
    (p : ℕ) (hp : 1 ≤ p) {K δb : ℝ} (hK : 0 ≤ K) (hδb : 0 ≤ δb) (β b₀ : ℝ → ℝ)
    (hβ : ContinuousOn β (Set.Icc s t)) (hb₀ : ContinuousOn b₀ (Set.Icc s t))
    (hβ0 : ∀ u ∈ Set.Icc s t, 0 ≤ β u) (hb₀0 : ∀ u ∈ Set.Icc s t, 0 ≤ b₀ u)
    (Bad : ℝ → Set (ι → ℝ))
    (hbad : ∀ u ∈ Set.Ioo s t,
      stdGauss ι {x | Real.sqrt (u * σ2) • x ∈ Bad u} ≤ ENNReal.ofReal δb)
    (hrate : ∀ u ∈ Set.Ioo s t, ∀ y, y ∉ Bad u →
      ‖coordGen σ2 Y u y‖ ≤ β u ∧ ‖coordGamma σ2 (Y u) (Y u) y‖ ≤ b₀ u)
    (hcrude : ∀ u ∈ Set.Ioo s t,
      ∫ x, ‖coordGen σ2 Y u (Real.sqrt (u * σ2) • x)‖ ^ (4 * p) ∂(stdGauss ι) ≤ K ^ (4 * p) ∧
      ∫ x, ‖coordGamma σ2 (Y u) (Y u) (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι) ≤
        K ^ (2 * p)) :
    (∫ x, ‖Y t (Real.sqrt (t * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) ≤
      Real.sqrt ((∫ x, ‖Y s (Real.sqrt (s * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (p : ℝ)) +
          (2 * p - 1) * ∫ u in s..t, (b₀ u + K * δb ^ (1 / (2 * (p : ℝ))))) +
        ∫ u in s..t, (β u + K * δb ^ (1 / (4 * (p : ℝ)))) := by
  have hδ4 : 0 ≤ δb ^ (1 / (4 * (p : ℝ))) := Real.rpow_nonneg hδb _
  have hδ2 : 0 ≤ δb ^ (1 / (2 * (p : ℝ))) := Real.rpow_nonneg hδb _
  have hc4 : ((4 * p : ℕ) : ℝ) = 4 * (p : ℝ) := by push_cast; ring
  have hc2 : ((2 * p : ℕ) : ℝ) = 2 * (p : ℝ) := by push_cast; ring
  have hcp : 1 ≤ 2 * p := by omega
  have data : ∀ u ∈ Set.Ioo s t,
      (∫ x, ‖coordGen σ2 Y u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^
          (1 / (2 * (p : ℝ))) ≤ β u + K * δb ^ (1 / (4 * (p : ℝ))) ∧
      (∫ x, ‖coordGamma σ2 (Y u) (Y u) (Real.sqrt (u * σ2) • x)‖ ^ p ∂(stdGauss ι)) ^
          (1 / (p : ℝ)) ≤ b₀ u + K * δb ^ (1 / (2 * (p : ℝ))) := by
    intro u hu
    have hu' : u ∈ Set.Icc s t := Set.Ioo_subset_Icc_self hu
    have hua : u ∈ Set.Ioo a b := ⟨ha.trans_le (hs.trans hu'.1), hu'.2.trans_lt htb⟩
    obtain ⟨⟨hGc, CG, hCG⟩, ⟨hΓc, CΓ, hCΓ⟩⟩ := momentIter_jet hY hua σ2
    set S : ℝ := Real.sqrt (u * σ2) with hS
    have hSc : Continuous (fun x : ι → ℝ => S • x) := continuous_const_smul S
    set T : Set (ι → ℝ) := toMeasurable (stdGauss ι) {x | S • x ∈ Bad u} with hTdef
    have hT : MeasurableSet T := measurableSet_toMeasurable _ _
    have hTμ : stdGauss ι T ≤ ENNReal.ofReal δb := by
      rw [hTdef, measure_toMeasurable]; exact hbad u hu
    have hTsub : ∀ x, x ∉ T → S • x ∉ Bad u := fun x hx h => hx (subset_toMeasurable _ _ h)
    have hf0 : ∀ x : ι → ℝ, (0 : ℝ) ≤ (fun _ => (0 : ℝ)) x := fun _ => le_rfl
    have hfL : ∀ m : ℕ, eLpNorm (fun _ : ι → ℝ => (0 : ℝ)) m (stdGauss ι) ≤ ENNReal.ofReal 0 := by
      intro m
      have : (fun _ : ι → ℝ => (0 : ℝ)) = 0 := rfl
      rw [this, eLpNorm_zero]; simp
    -- generator
    set g : (ι → ℝ) → ℂ := fun x => coordGen σ2 Y u (S • x) with hg
    have hgc : Continuous g := hGc.comp hSc
    have hgm : ∀ n : ℕ, MemLp g n (stdGauss ι) := fun n =>
      MemLp.of_bound hgc.aestronglyMeasurable CG (ae_of_all _ fun x => hCG _)
    have hgK : eLpNorm g (4 * p : ℕ) (stdGauss ι) ≤ ENNReal.ofReal K :=
      momentIter_crude_le (by omega) (hgm _) hK (hcrude u hu).1
    have hgsplit := momentIter_split (μ := stdGauss ι) (f := fun _ => (0 : ℝ))
      hgc.aestronglyMeasurable hf0 hT (c₁ := 0) (c₀ := β u) (L := 0) le_rfl (hβ0 u hu') le_rfl hK
      hδb (fun x hx => by simpa using (hrate u hu _ (hTsub x hx)).1)
      (2 * p) (4 * p) hcp (by ring) hTμ (hfL _) hgK
    rw [momentIter_eLpNorm_eq hcp (hgm _), hc4, hc2] at hgsplit
    have hA0 : 0 ≤ (0 : ℝ) * 0 + β u + K * δb ^ (1 / (4 * (p : ℝ))) := by
      simpa using add_nonneg (hβ0 u hu') (mul_nonneg hK hδ4)
    rw [ENNReal.ofReal_le_ofReal_iff hA0] at hgsplit
    -- carré du champ
    set G : (ι → ℝ) → ℂ := fun x => coordGamma σ2 (Y u) (Y u) (S • x) with hG
    have hGc' : Continuous G := hΓc.comp hSc
    have hGm : ∀ n : ℕ, MemLp G n (stdGauss ι) := fun n =>
      MemLp.of_bound hGc'.aestronglyMeasurable CΓ (ae_of_all _ fun x => hCΓ _)
    have hGK : eLpNorm G (2 * p : ℕ) (stdGauss ι) ≤ ENNReal.ofReal K :=
      momentIter_crude_le hcp (hGm _) hK (hcrude u hu).2
    have hGsplit := momentIter_split (μ := stdGauss ι) (f := fun _ => (0 : ℝ))
      hGc'.aestronglyMeasurable hf0 hT (c₁ := 0) (c₀ := b₀ u) (L := 0) le_rfl (hb₀0 u hu') le_rfl
      hK hδb (fun x hx => by simpa using (hrate u hu _ (hTsub x hx)).2)
      p (2 * p) hp rfl hTμ (hfL _) hGK
    rw [momentIter_eLpNorm_eq hp (hGm _), hc2] at hGsplit
    have hB0 : 0 ≤ (0 : ℝ) * 0 + b₀ u + K * δb ^ (1 / (2 * (p : ℝ))) := by
      simpa using add_nonneg (hb₀0 u hu') (mul_nonneg hK hδ2)
    rw [ENNReal.ofReal_le_ofReal_iff hB0] at hGsplit
    refine ⟨?_, ?_⟩
    · simpa using hgsplit
    · simpa using hGsplit
  exact lemmaM_gaussian σ2 hσ2 Y ha hs hst htb hY p hp
    (fun u => β u + K * δb ^ (1 / (4 * (p : ℝ)))) (fun u => b₀ u + K * δb ^ (1 / (2 * (p : ℝ))))
    (hβ.add continuousOn_const) (hb₀.add continuousOn_const)
    (fun u hu => add_nonneg (hβ0 u hu) (mul_nonneg hK hδ4))
    (fun u hu => add_nonneg (hb₀0 u hu) (mul_nonneg hK hδ2))
    (fun u hu => (data u hu).1) (fun u hu => (data u hu).2)

end LSBA
