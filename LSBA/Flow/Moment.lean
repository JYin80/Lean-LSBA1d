import LSBA.Gauss.HeatGenerator
import LSBA.Flow.Comparison

/-!
# The moment comparison

The pointwise inequality `𝒢|Y|^{2p} ≤ 2p|Y|^{2p-1}|𝒢Y| + (2p² − p)|Y|^{2p-2} Γ(Y,Y)` and the moment
comparison: `‖Y_v‖_{2p} ≤ (‖Y_s‖²_{2p} + (2p − 1)∫ B)^{1/2} + ∫ A` along the Gaussian flow, with
`A ≥ ‖𝒢Y‖_{2p}` and `B ≥ ‖Γ(Y,Y)‖_p`, used for the moment estimates of Appendix C.3
[sec:gc-one-step].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The second derivative at `0` of `e ↦ ‖g e‖^(2p)` for a `C²` curve `g` in `ℂ`. -/
private theorem moment_iter2_pow (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (p : ℕ) (hp : 1 ≤ p) :
    iteratedDeriv 2 (fun e => ‖g e‖ ^ (2 * p)) 0 =
      p * (‖g 0‖ ^ 2) ^ (p - 1) *
          (2 * (inner ℝ (g 0) (iteratedDeriv 2 g 0) + ‖deriv g 0‖ ^ 2)) +
        p * ((p : ℝ) - 1) * (‖g 0‖ ^ 2) ^ (p - 2) * (2 * inner ℝ (g 0) (deriv g 0)) ^ 2 := by
  have hg1 : ∀ e, HasDerivAt g (deriv g e) e := fun e =>
    ((hg.differentiable (by norm_num)) e).hasDerivAt
  have hg2 : ∀ e, HasDerivAt (deriv g) (deriv (deriv g) e) e := fun e =>
    ((hg.differentiable_deriv_two) e).hasDerivAt
  have hit : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hϕ : ∀ e, HasDerivAt (fun e => ‖g e‖ ^ 2) (2 * inner ℝ (g e) (deriv g e)) e :=
    fun e => (hg1 e).norm_sq
  have hfun : (fun e => ‖g e‖ ^ (2 * p)) = fun e => (‖g e‖ ^ 2) ^ p :=
    funext fun e => pow_mul _ _ _
  have hψ : ∀ e, HasDerivAt (fun e => (‖g e‖ ^ 2) ^ p)
      (p * (‖g e‖ ^ 2) ^ (p - 1) * (2 * inner ℝ (g e) (deriv g e))) e := fun e =>
    (hϕ e).pow p
  have hd : deriv (fun e => ‖g e‖ ^ (2 * p)) =
      fun e => p * (‖g e‖ ^ 2) ^ (p - 1) * (2 * inner ℝ (g e) (deriv g e)) := by
    rw [hfun]; funext e; exact (hψ e).deriv
  have h2 : HasDerivAt (fun e => (p : ℝ) * (‖g e‖ ^ 2) ^ (p - 1) * (2 * inner ℝ (g e) (deriv g e)))
      ((p : ℝ) * (((p - 1 : ℕ) : ℝ) * (‖g 0‖ ^ 2) ^ (p - 1 - 1) * (2 * inner ℝ (g 0) (deriv g 0)))
          * (2 * inner ℝ (g 0) (deriv g 0)) +
        (p : ℝ) * (‖g 0‖ ^ 2) ^ (p - 1) *
          (2 * (inner ℝ (g 0) (deriv (deriv g) 0) + inner ℝ (deriv g 0) (deriv g 0)))) 0 := by
    have hA := ((hϕ 0).pow (p - 1)).const_mul (p : ℝ)
    have hB := ((((hg1 0).inner ℝ (hg2 0))).const_mul 2)
    exact (hA.mul hB).congr_deriv (by simp only [Pi.pow_apply])
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd, h2.deriv, hit, real_inner_self_eq_norm_sq]
  have h1 : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp]; simp
  have h3 : p - 1 - 1 = p - 2 := by omega
  rw [h1, h3]
  ring


/-- Upper bound for the second derivative of `‖g‖^(2p)`: `(∂ϕ)² ≤ 4ϕ|g'|²` for `ϕ = ‖g‖²`. -/
private theorem moment_iter2_pow_le (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (p : ℕ) (hp : 1 ≤ p) :
    iteratedDeriv 2 (fun e => ‖g e‖ ^ (2 * p)) 0 ≤
      2 * p * (‖g 0‖ ^ 2) ^ (p - 1) * inner ℝ (g 0) (iteratedDeriv 2 g 0) +
        (4 * (p : ℝ) ^ 2 - 2 * p) * (‖g 0‖ ^ 2) ^ (p - 1) * ‖deriv g 0‖ ^ 2 := by
  rw [moment_iter2_pow g hg p hp]
  have hc : inner ℝ (g 0) (deriv g 0) ^ 2 ≤ ‖g 0‖ ^ 2 * ‖deriv g 0‖ ^ 2 := by
    have := abs_real_inner_le_norm (g 0) (deriv g 0)
    calc inner ℝ (g 0) (deriv g 0) ^ 2 = |inner ℝ (g 0) (deriv g 0)| ^ 2 := (sq_abs _).symm
      _ ≤ (‖g 0‖ * ‖deriv g 0‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = ‖g 0‖ ^ 2 * ‖deriv g 0‖ ^ 2 := by ring
  rcases Nat.lt_or_ge p 2 with h | h
  · obtain rfl : p = 1 := by omega
    norm_num
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
    have e1 : k + 2 - 1 = k + 1 := by omega
    have e2 : k + 2 - 2 = k := by omega
    rw [e1, e2]
    have hϕ : 0 ≤ (‖g 0‖ ^ 2) ^ k := by positivity
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have key : ((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) - 1) * (‖g 0‖ ^ 2) ^ k *
          (2 * inner ℝ (g 0) (deriv g 0)) ^ 2 ≤
        ((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) - 1) * (‖g 0‖ ^ 2) ^ k *
          (4 * (‖g 0‖ ^ 2 * ‖deriv g 0‖ ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (mul_nonneg (by positivity) (by push_cast; linarith)) hϕ)
      nlinarith [hc]
    push_cast at key ⊢
    rw [pow_succ]
    nlinarith [key]


/-- For a `C²` real function `h`, the complex-valued function `e ↦ (h e : ℂ)` has second
derivative `(h''(0) : ℂ)` at `0`. -/
private theorem moment_iter2_ofReal {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) :
    iteratedDeriv 2 (fun e : ℝ => ((h e : ℝ) : ℂ)) 0 = ((iteratedDeriv 2 h 0 : ℝ) : ℂ) := by
  have hg1 : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hdg : Differentiable ℝ (deriv h) := hh.differentiable_deriv_two
  have hd1 : deriv (fun e : ℝ => ((h e : ℝ) : ℂ)) = fun e => ((deriv h e : ℝ) : ℂ) :=
    funext fun e => (hg1 e).hasDerivAt.ofReal_comp.deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd1, iteratedDeriv_succ, iteratedDeriv_one]
  exact (hdg 0).hasDerivAt.ofReal_comp.deriv

/-- `Γ(F, F)` is the real number `σ² Σ_i ‖∂_i F‖²`. -/
private theorem moment_gamma_eq {ι : Type*} [Fintype ι] (σ2 : ℝ) (F : (ι → ℝ) → ℂ) (y : ι → ℝ) :
    coordGamma σ2 F F y =
      ((σ2 * ∑ i, ‖deriv (fun e : ℝ => F (y + e • Pi.single i 1)) 0‖ ^ 2 : ℝ) : ℂ) := by
  simp only [coordGamma, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- The time derivative at `u` of `r ↦ ‖c r‖^(2p)`. -/
private theorem moment_time_deriv (c : ℝ → ℂ) (u : ℝ) (hc : DifferentiableAt ℝ c u) (p : ℕ) :
    deriv (fun r => ((‖c r‖ ^ (2 * p) : ℝ) : ℂ)) u =
      ((p * (‖c u‖ ^ 2) ^ (p - 1) * (2 * inner ℝ (c u) (deriv c u)) : ℝ) : ℂ) := by
  have h1 := (hc.hasDerivAt.norm_sq).pow p
  have hfun : (fun r => ‖c r‖ ^ (2 * p)) = (fun r => ‖c r‖ ^ 2) ^ p :=
    funext fun r => by simp [pow_mul]
  have h2 := h1.ofReal_comp
  rw [show (fun r => ((‖c r‖ ^ (2 * p) : ℝ) : ℂ)) = fun r => (((fun r => ‖c r‖ ^ 2) ^ p) r : ℂ) by
    funext r; rw [Pi.pow_apply, pow_mul]]
  rw [h2.deriv]


/-- Along a line, `e ↦ G(y + e v)` has first derivative `DG(y) v` at `0`. -/
private theorem moment_deriv_line {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℂ}
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
private theorem moment_iteratedDeriv_line {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℂ}
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
private theorem moment_slice {ι E : Type*} [TopologicalSpace E] {g : ℝ → (ι → ℝ) → E}
    {a b : ℝ} (hg : ContinuousOn (Function.uncurry g) (Set.Ioo a b ×ˢ Set.univ)) {r : ℝ}
    (hr : r ∈ Set.Ioo a b) : Continuous (g r) :=
  hg.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hr, trivial⟩

/-- Jet data of a member of the class at a time `u ∈ (a,b)`: differentiability in time, `C²`
regularity in space, and continuity and boundedness of `F u`, `𝒢F u`, `Γ(F u, F u)`. -/
private theorem moment_class_jet {ι : Type*} [Fintype ι] {F : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (hF : HeatClass F a b) {u : ℝ} (hu : u ∈ Set.Ioo a b) (σ2 : ℝ) :
    (∀ y, DifferentiableAt ℝ (fun r => F r y) u) ∧ ContDiff ℝ 2 (F u) ∧
      (∃ C : ℝ, ∀ y, ‖F u y‖ ≤ C) ∧
      (Continuous (coordGen σ2 F u) ∧ ∃ C : ℝ, ∀ y, ‖coordGen σ2 F u y‖ ≤ C) ∧
      (Continuous (coordGamma σ2 (F u) (F u)) ∧
        ∃ C : ℝ, ∀ y, ‖coordGamma σ2 (F u) (F u) y‖ ≤ C) := by
  obtain ⟨hc, ⟨C₀, hC₀⟩, ⟨Fu, hu', hcu, C₁, hC₁⟩, ⟨DF, D2F, hD, hD2, hcD, hcD2, C₂, hC₂⟩⟩ := hF
  have hei : ∀ i : ι, ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ ≤ 1 := fun i => by
    rw [Pi.norm_single]; simp
  have hDc : Continuous (DF u) := moment_slice hcD hu
  have hD2c : Continuous (D2F u) := moment_slice hcD2 hu
  have hFuc : Continuous (Fu u) := moment_slice hcu hu
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
    exact moment_iteratedDeriv_line (hD u hu) (hD2 u hu) y _
  have hgam : ∀ y, coordGamma σ2 (F u) (F u) y =
      (σ2 : ℂ) * ∑ i, DF u y (Pi.single i 1) * star (DF u y (Pi.single i 1)) := by
    intro y
    simp only [coordGamma, moment_deriv_line (hD u hu)]
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

/-- Pointwise `𝒢|Y|^{2p} ≤ 2p|Y|^{2p-1}|𝒢Y| + (2p²-p)|Y|^{2p-2} Γ(Y,Y)`. -/
theorem coordGen_normPow_le {ι : Type*} [Fintype ι] (σ2 : ℝ) (hσ2 : 0 ≤ σ2) (p : ℕ) (hp : 1 ≤ p)
    (Y : ℝ → (ι → ℝ) → ℂ) (u : ℝ) (y : ι → ℝ) (hYu : DifferentiableAt ℝ (fun r => Y r y) u)
    (hYy : ContDiff ℝ 2 (Y u)) :
    (coordGen σ2 (fun r z => ((‖Y r z‖ ^ (2 * p) : ℝ) : ℂ)) u y).re ≤
      2 * p * ‖Y u y‖ ^ (2 * p - 1) * ‖coordGen σ2 Y u y‖ +
        (2 * (p : ℝ) ^ 2 - p) * ‖Y u y‖ ^ (2 * p - 2) * (coordGamma σ2 (Y u) (Y u) y).re := by
  set g : ι → ℝ → ℂ := fun i e => Y u (y + e • Pi.single i (1 : ℝ)) with hg
  have hline : ∀ i : ι, ContDiff ℝ 2 (g i) := fun i =>
    hYy.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hz : ∀ i : ι, g i 0 = Y u y := fun i => by simp [hg]
  have hnp : ∀ i : ι, ContDiff ℝ 2 (fun e : ℝ => ‖g i e‖ ^ (2 * p)) := fun i => by
    have : (fun e : ℝ => ‖g i e‖ ^ (2 * p)) = fun e => (‖g i e‖ ^ 2) ^ p :=
      funext fun e => pow_mul _ _ _
    rw [this]
    exact ((contDiff_norm_sq ℝ).comp (hline i)).pow p
  set ϕ0 : ℝ := ‖Y u y‖ ^ 2 with hϕ0
  have hϕ0nn : 0 ≤ ϕ0 := by positivity
  have hϕpow : ϕ0 ^ (p - 1) = ‖Y u y‖ ^ (2 * p - 2) := by
    rw [hϕ0, ← pow_mul]; congr 1; omega
  -- the time part
  set c' : ℂ := deriv (fun r => Y r y) u with hc'
  set T : ℝ := p * ϕ0 ^ (p - 1) * (2 * inner ℝ (Y u y) c') with hT
  have hTd : deriv (fun r => ((‖Y r y‖ ^ (2 * p) : ℝ) : ℂ)) u = (T : ℂ) :=
    moment_time_deriv (fun r => Y r y) u hYu p
  -- the space part
  set W : ι → ℝ := fun i => iteratedDeriv 2 (fun e : ℝ => ‖g i e‖ ^ (2 * p)) 0 with hW
  have hWd : ∀ i : ι,
      iteratedDeriv 2 (fun e : ℝ => ((‖Y u (y + e • Pi.single i (1 : ℝ))‖ ^ (2 * p) : ℝ) : ℂ)) 0 =
        (W i : ℂ) := fun i => moment_iter2_ofReal (h := fun e : ℝ => ‖g i e‖ ^ (2 * p)) (hnp i)
  have hGen : coordGen σ2 (fun r z => ((‖Y r z‖ ^ (2 * p) : ℝ) : ℂ)) u y =
      ((T + σ2 / 2 * ∑ i, W i : ℝ) : ℂ) := by
    simp only [coordGen, hTd, hWd]
    push_cast
    rfl
  rw [hGen, Complex.ofReal_re]
  have hWle : ∀ i : ι, W i ≤ 2 * p * ϕ0 ^ (p - 1) * inner ℝ (Y u y) (iteratedDeriv 2 (g i) 0) +
      (4 * (p : ℝ) ^ 2 - 2 * p) * ϕ0 ^ (p - 1) * ‖deriv (g i) 0‖ ^ 2 := fun i => by
    have := moment_iter2_pow_le (g i) (hline i) p hp
    rwa [hz i] at this
  have hGY : coordGen σ2 Y u y = c' + ((σ2 / 2 : ℝ) : ℂ) * ∑ i, iteratedDeriv 2 (g i) 0 := rfl
  have hinner : inner ℝ (Y u y) (coordGen σ2 Y u y) =
      inner ℝ (Y u y) c' + σ2 / 2 * ∑ i, inner ℝ (Y u y) (iteratedDeriv 2 (g i) 0) := by
    rw [hGY, ← Complex.real_smul, inner_add_right, real_inner_smul_right, inner_sum]
  have hΓ : (coordGamma σ2 (Y u) (Y u) y).re = σ2 * ∑ i, ‖deriv (g i) 0‖ ^ 2 := by
    rw [moment_gamma_eq, Complex.ofReal_re]
  have hsum : T + σ2 / 2 * ∑ i, W i ≤ 2 * p * ϕ0 ^ (p - 1) * inner ℝ (Y u y) (coordGen σ2 Y u y) +
      (2 * (p : ℝ) ^ 2 - p) * ϕ0 ^ (p - 1) * (coordGamma σ2 (Y u) (Y u) y).re := by
    have h1 : σ2 / 2 * ∑ i, W i ≤ σ2 / 2 * ∑ i, (2 * p * ϕ0 ^ (p - 1) *
        inner ℝ (Y u y) (iteratedDeriv 2 (g i) 0) +
        (4 * (p : ℝ) ^ 2 - 2 * p) * ϕ0 ^ (p - 1) * ‖deriv (g i) 0‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hWle i) (by positivity)
    rw [hinner, hΓ]
    calc T + σ2 / 2 * ∑ i, W i
        ≤ T + σ2 / 2 * ∑ i, (2 * p * ϕ0 ^ (p - 1) * inner ℝ (Y u y) (iteratedDeriv 2 (g i) 0) +
          (4 * (p : ℝ) ^ 2 - 2 * p) * ϕ0 ^ (p - 1) * ‖deriv (g i) 0‖ ^ 2) := by linarith
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp only [hT]
        ring
  have hfin : 2 * p * ϕ0 ^ (p - 1) * inner ℝ (Y u y) (coordGen σ2 Y u y) ≤
      2 * p * ‖Y u y‖ ^ (2 * p - 1) * ‖coordGen σ2 Y u y‖ := by
    have h1 : ϕ0 ^ (p - 1) * ‖Y u y‖ = ‖Y u y‖ ^ (2 * p - 1) := by
      rw [hϕ0, ← pow_mul, ← pow_succ]; congr 1; omega
    calc 2 * p * ϕ0 ^ (p - 1) * inner ℝ (Y u y) (coordGen σ2 Y u y)
        ≤ 2 * p * ϕ0 ^ (p - 1) * (‖Y u y‖ * ‖coordGen σ2 Y u y‖) :=
          mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) (by positivity)
      _ = 2 * p * (ϕ0 ^ (p - 1) * ‖Y u y‖) * ‖coordGen σ2 Y u y‖ := by ring
      _ = _ := by rw [h1]
  rw [← hϕpow]
  linarith

/-- Hölder with exponents `(q/(q-1), q)` for bounded nonnegative measurable factors:
`∫ N^{m(q-1)} G ≤ (∫ N^{mq})^{1-1/q} (∫ G^q)^{1/q}`. -/
private theorem moment_holder {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (N G : α → ℝ) (hN0 : ∀ x, 0 ≤ N x) (hG0 : ∀ x, 0 ≤ G x)
    (hNm : AEStronglyMeasurable N μ) (hGm : AEStronglyMeasurable G μ) {CN CG : ℝ}
    (hNb : ∀ x, N x ≤ CN) (hGb : ∀ x, G x ≤ CG) (m q : ℕ) (hq : 2 ≤ q) :
    ∫ x, N x ^ (m * (q - 1)) * G x ∂μ ≤
      (∫ x, N x ^ (m * q) ∂μ) ^ (1 - 1 / (q : ℝ)) * (∫ x, G x ^ q ∂μ) ^ (1 / (q : ℝ)) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hqm1 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  set P : ℝ := (q : ℝ) / ((q : ℝ) - 1) with hP
  have hqm1pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hP1 : 1 < P := by
    rw [hP, lt_div_iff₀ hqm1pos]; linarith
  have hconj : P.HolderConjugate (q : ℝ) := by
    rw [Real.holderConjugate_iff]
    refine ⟨hP1, ?_⟩
    rw [hP]; field_simp; ring
  have hfP : ∀ x, (N x ^ (m * (q - 1))) ^ P = N x ^ (m * q) := fun x => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hN0 x), ← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_mul, Nat.cast_mul, hqm1, hP]
    field_simp
  have hgQ : ∀ x, G x ^ (q : ℝ) = G x ^ q := fun x => Real.rpow_natCast _ q
  have hfm : AEStronglyMeasurable (fun x => N x ^ (m * (q - 1))) μ := hNm.pow _
  have hgm : AEStronglyMeasurable G μ := hGm
  have hmemf : MemLp (fun x => N x ^ (m * (q - 1))) (ENNReal.ofReal P) μ := by
    refine MemLp.of_bound hfm (CN ^ (m * (q - 1))) (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (hN0 x) _)]
    exact pow_le_pow_left₀ (hN0 x) (hNb x) _
  have hmemg : MemLp G (ENNReal.ofReal (q : ℝ)) μ := by
    refine MemLp.of_bound hgm CG (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (hG0 x)]
    exact hGb x
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hconj (μ := μ)
    (f := fun x => N x ^ (m * (q - 1))) (g := G)
    (ae_of_all _ fun x => pow_nonneg (hN0 x) _) (ae_of_all _ hG0) hmemf hmemg
  simp only [hfP, hgQ] at h
  have h1P : 1 / P = 1 - 1 / (q : ℝ) := by
    rw [hP]; field_simp
  rwa [h1P] at h

/-- A bounded continuous function is integrable under the standard Gaussian. -/
private theorem moment_integrable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [SecondCountableTopology E] {g : (ι → ℝ) → E} (hg : Continuous g) {C : ℝ}
    (hC : ∀ y, ‖g y‖ ≤ C) : Integrable g (stdGauss ι) :=
  (integrable_const C).mono' hg.aestronglyMeasurable (ae_of_all _ hC)

/-- `|Y|^{2p}` lies in the class when `Y` does. -/
private theorem moment_class_normPow {ι : Type*} [Fintype ι] {Y : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (hY : HeatClass Y a b) (p : ℕ) (hp : 1 ≤ p) :
    HeatClass (fun r z => ((‖Y r z‖ ^ (2 * p) : ℝ) : ℂ)) a b := by
  have h0 : HeatClass (fun r z => Y r z * star (Y r z)) a b := hY.mul hY.star
  have hpow : ∀ n : ℕ, 1 ≤ n → HeatClass (fun r z => (Y r z * star (Y r z)) ^ n) a b := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simpa using h0
    | succ n hn ih =>
      have := ih.mul h0
      simpa [pow_succ] using this
  have hfun : (fun r z => ((‖Y r z‖ ^ (2 * p) : ℝ) : ℂ)) =
      fun r z => (Y r z * star (Y r z)) ^ p := by
    funext r z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow,
      ← pow_mul]
  rw [hfun]
  exact hpow p hp

/-- `N^k G` is integrable for bounded nonnegative continuous `N` and `G`. -/
private theorem moment_integrable_pow_mul {ι : Type*} [Fintype ι] {N G : (ι → ℝ) → ℝ}
    (hN : Continuous N) (hG : Continuous G) (hN0 : ∀ x, 0 ≤ N x) (hG0 : ∀ x, 0 ≤ G x)
    {CN CG : ℝ} (hNb : ∀ x, N x ≤ CN) (hGb : ∀ x, G x ≤ CG) (k : ℕ) :
    Integrable (fun x => N x ^ k * G x) (stdGauss ι) := by
  refine moment_integrable ((hN.pow k).mul hG) (C := CN ^ k * CG) fun x => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (hN0 x) _) (hG0 x))]
  exact mul_le_mul (pow_le_pow_left₀ (hN0 x) (hNb x) _) (hGb x) (hG0 x)
    ((pow_nonneg (hN0 x) _).trans (pow_le_pow_left₀ (hN0 x) (hNb x) _))

/-- `‖Γ(F,F)‖` is the real number `Γ(F,F)` for `σ² ≥ 0`. -/
private theorem moment_gamma_norm {ι : Type*} [Fintype ι] {σ2 : ℝ} (hσ2 : 0 ≤ σ2)
    (F : (ι → ℝ) → ℂ) (y : ι → ℝ) :
    ‖coordGamma σ2 F F y‖ = (coordGamma σ2 F F y).re ∧ 0 ≤ (coordGamma σ2 F F y).re := by
  have h0 : 0 ≤ σ2 * ∑ i, ‖deriv (fun e : ℝ => F (y + e • Pi.single i 1)) 0‖ ^ 2 :=
    mul_nonneg hσ2 (Finset.sum_nonneg fun i _ => by positivity)
  rw [moment_gamma_eq, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg h0]
  exact ⟨rfl, h0⟩

/-- The moment comparison (Gaussian form): `‖Y_v‖_{2p} ≤ (‖Y_s‖²_{2p} + (2p-1)∫ B)^{1/2} + ∫ A`,
with `A ≥ ‖𝒢Y‖_{2p}` and `B ≥ ‖Γ(Y,Y)‖_p`. -/
theorem lemmaM_gaussian {ι : Type*} [Fintype ι] (σ2 : ℝ) (hσ2 : 0 ≤ σ2) (Y : ℝ → (ι → ℝ) → ℂ)
    {a b s v : ℝ} (ha : a < 0) (hs : 0 ≤ s) (hsv : s ≤ v) (hvb : v < b) (hY : HeatClass Y a b)
    (p : ℕ) (hp : 1 ≤ p) (A B : ℝ → ℝ) (hA : ContinuousOn A (Set.Icc s v))
    (hB : ContinuousOn B (Set.Icc s v)) (hA0 : ∀ u ∈ Set.Icc s v, 0 ≤ A u)
    (hB0 : ∀ u ∈ Set.Icc s v, 0 ≤ B u)
    (hAg : ∀ u ∈ Set.Ioo s v, (∫ x, ‖coordGen σ2 Y u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p)
        ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) ≤ A u)
    (hBg : ∀ u ∈ Set.Ioo s v, (∫ x, ‖coordGamma σ2 (Y u) (Y u) (Real.sqrt (u * σ2) • x)‖ ^ p
        ∂(stdGauss ι)) ^ (1 / (p : ℝ)) ≤ B u) :
    (∫ x, ‖Y v (Real.sqrt (v * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) ≤
      Real.sqrt ((∫ x, ‖Y s (Real.sqrt (s * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (p : ℝ)) +
          (2 * p - 1) * ∫ u in s..v, B u) + ∫ u in s..v, A u := by
  have hv0 : 0 ≤ v := hs.trans hsv
  have hF : HeatClass (fun r z => ((‖Y r z‖ ^ (2 * p) : ℝ) : ℂ)) a b :=
    moment_class_normPow hY p hp
  obtain ⟨hcont, hderiv⟩ := heat_generator σ2 hσ2 _ ha hv0 hvb hF
  set f : ℝ → ℝ := fun u => ∫ x, ‖Y u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι) with hf
  have hfF : ∀ u, (∫ x, ((‖Y u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) : ℝ) : ℂ) ∂(stdGauss ι)) =
      ((f u : ℝ) : ℂ) := fun u => integral_ofReal
  have hf0 : ∀ u, 0 ≤ f u := fun u => integral_nonneg fun x => by positivity
  have hfc : ContinuousOn f (Set.Icc s v) := by
    have h1 : ContinuousOn (fun u => ((f u : ℝ) : ℂ)) (Set.Icc s v) := by
      have := hcont.mono (Set.Icc_subset_Icc hs le_rfl)
      simpa only [hfF] using this
    have h2 := Complex.continuous_re.comp_continuousOn h1
    exact h2.congr fun u _ => by simp
  -- derivative and bound on `(s,v)`
  have key : ∀ u ∈ Set.Ioo s v, HasDerivAt f
      (∫ x, (coordGen σ2 (fun r z => ((‖Y r z‖ ^ (2 * p) : ℝ) : ℂ)) u
        (Real.sqrt (u * σ2) • x)).re ∂(stdGauss ι)) u ∧
      (∫ x, (coordGen σ2 (fun r z => ((‖Y r z‖ ^ (2 * p) : ℝ) : ℂ)) u
        (Real.sqrt (u * σ2) • x)).re ∂(stdGauss ι)) ≤
        2 * p * f u ^ (1 - 1 / (2 * (p : ℝ))) * A u +
          (2 * (p : ℝ) ^ 2 - p) * f u ^ (1 - 1 / (p : ℝ)) * B u := by
    intro u hu
    have hu0 : u ∈ Set.Ioo 0 v := ⟨hs.trans_lt hu.1, hu.2⟩
    have hua : u ∈ Set.Ioo a b := ⟨ha.trans hu0.1, hu.2.trans hvb⟩
    obtain ⟨hdiff, hc2, ⟨CY, hCY⟩, ⟨hGc, CG, hCG⟩, ⟨hΓc, CΓ, hCΓ⟩⟩ := moment_class_jet hY hua σ2
    obtain ⟨-, -, -, ⟨hFGc, CFG, hCFG⟩, -⟩ := moment_class_jet hF hua σ2
    set S : ℝ := Real.sqrt (u * σ2) with hS
    have hSc : Continuous (fun x : ι → ℝ => S • x) := continuous_const_smul S
    have hintC : Integrable (fun x => coordGen σ2 (fun r z => ((‖Y r z‖ ^ (2 * p) : ℝ) : ℂ)) u
        (S • x)) (stdGauss ι) := moment_integrable (hFGc.comp hSc) fun x => hCFG _
    refine ⟨?_, ?_⟩
    · have h : HasDerivAt (fun r => ((f r : ℝ) : ℂ))
          (∫ x, coordGen σ2 (fun r z => ((‖Y r z‖ ^ (2 * p) : ℝ) : ℂ)) u (S • x)
            ∂(stdGauss ι)) u := by
        have := hderiv u hu0
        simpa only [hfF] using this
      have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u h
      have hre := integral_re hintC
      simp only [RCLike.re_to_complex] at hre
      rw [hre]
      simpa [Function.comp_def] using h3
    · have hYc : Continuous (Y u) := hc2.continuous
      set N : (ι → ℝ) → ℝ := fun x => ‖Y u (S • x)‖ with hN
      set G : (ι → ℝ) → ℝ := fun x => ‖coordGen σ2 Y u (S • x)‖ with hG
      set Γr : (ι → ℝ) → ℝ := fun x => (coordGamma σ2 (Y u) (Y u) (S • x)).re with hΓr
      have hNc : Continuous N := (hYc.comp hSc).norm
      have hGcn : Continuous G := (hGc.comp hSc).norm
      have hΓcn : Continuous Γr := Complex.continuous_re.comp (hΓc.comp hSc)
      have hN0 : ∀ x, 0 ≤ N x := fun x => norm_nonneg _
      have hG0 : ∀ x, 0 ≤ G x := fun x => norm_nonneg _
      have hΓ0 : ∀ x, 0 ≤ Γr x := fun x => (moment_gamma_norm hσ2 (Y u) (S • x)).2
      have hNb : ∀ x, N x ≤ CY := fun x => hCY _
      have hGb : ∀ x, G x ≤ CG := fun x => hCG _
      have hΓb : ∀ x, Γr x ≤ CΓ := fun x => by
        have := hCΓ (S • x)
        rwa [(moment_gamma_norm hσ2 (Y u) (S • x)).1] at this
      have hI1 := moment_integrable_pow_mul hNc hGcn hN0 hG0 hNb hGb (2 * p - 1)
      have hI2 := moment_integrable_pow_mul hNc hΓcn hN0 hΓ0 hNb hΓb (2 * p - 2)
      have hpt : ∀ x, (coordGen σ2 (fun r z => ((‖Y r z‖ ^ (2 * p) : ℝ) : ℂ)) u (S • x)).re ≤
          2 * p * (N x ^ (2 * p - 1) * G x) +
            (2 * (p : ℝ) ^ 2 - p) * (N x ^ (2 * p - 2) * Γr x) := by
        intro x
        have := coordGen_normPow_le σ2 hσ2 p hp Y u (S • x) (hdiff _) hc2
        calc _ ≤ _ := this
          _ = _ := by ring
      have hmono : ∫ x, (coordGen σ2 (fun r z => ((‖Y r z‖ ^ (2 * p) : ℝ) : ℂ)) u (S • x)).re
            ∂(stdGauss ι) ≤
          ∫ x, (2 * p * (N x ^ (2 * p - 1) * G x) +
            (2 * (p : ℝ) ^ 2 - p) * (N x ^ (2 * p - 2) * Γr x)) ∂(stdGauss ι) :=
        integral_mono hintC.re ((hI1.const_mul _).add (hI2.const_mul _)) hpt
      rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul,
        integral_const_mul] at hmono
      have hT1 : ∫ x, N x ^ (2 * p - 1) * G x ∂(stdGauss ι) ≤
          f u ^ (1 - 1 / (2 * (p : ℝ))) * A u := by
        have hh := moment_holder (stdGauss ι) N G hN0 hG0 hNc.aestronglyMeasurable
          hGcn.aestronglyMeasurable hNb hGb 1 (2 * p) (by omega)
        simp only [one_mul] at hh
        push_cast at hh
        exact hh.trans (mul_le_mul_of_nonneg_left (hAg u hu) (Real.rpow_nonneg (hf0 u) _))
      have hΓint : ∫ x, Γr x ^ p ∂(stdGauss ι) =
          ∫ x, ‖coordGamma σ2 (Y u) (Y u) (S • x)‖ ^ p ∂(stdGauss ι) :=
        integral_congr_ae (ae_of_all _ fun x => by
          change ((coordGamma σ2 (Y u) (Y u) (S • x)).re) ^ p =
            ‖coordGamma σ2 (Y u) (Y u) (S • x)‖ ^ p
          rw [(moment_gamma_norm hσ2 (Y u) (S • x)).1])
      have hT2 : ∫ x, N x ^ (2 * p - 2) * Γr x ∂(stdGauss ι) ≤
          f u ^ (1 - 1 / (p : ℝ)) * B u := by
        rcases Nat.lt_or_ge p 2 with h | h
        · obtain rfl : p = 1 := by omega
          have hb := hBg u hu
          rw [← hΓint] at hb
          simp only [Nat.cast_one, div_one, Real.rpow_one, pow_one] at hb
          simpa using hb
        · have hh := moment_holder (stdGauss ι) N Γr hN0 hΓ0 hNc.aestronglyMeasurable
            hΓcn.aestronglyMeasurable hNb hΓb 2 p h
          rw [show 2 * (p - 1) = 2 * p - 2 by omega] at hh
          rw [hΓint] at hh
          exact hh.trans (mul_le_mul_of_nonneg_left (hBg u hu) (Real.rpow_nonneg (hf0 u) _))
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
      have hc1 : 0 ≤ 2 * (p : ℝ) := by positivity
      have hc2' : 0 ≤ 2 * (p : ℝ) ^ 2 - p := by nlinarith
      calc _ ≤ _ := hmono
        _ ≤ 2 * p * (f u ^ (1 - 1 / (2 * (p : ℝ))) * A u) +
            (2 * (p : ℝ) ^ 2 - p) * (f u ^ (1 - 1 / (p : ℝ)) * B u) :=
          add_le_add (mul_le_mul_of_nonneg_left hT1 hc1) (mul_le_mul_of_nonneg_left hT2 hc2')
        _ = _ := by ring
  exact moment_ode_comparison (f := f)
    (f' := fun u => ∫ x, (coordGen σ2 (fun r z => ((‖Y r z‖ ^ (2 * p) : ℝ) : ℂ)) u
      (Real.sqrt (u * σ2) • x)).re ∂(stdGauss ι)) (a := A) (b := B) p hp hsv
    (fun u _ => hf0 u) hA0 hB0 hfc hA hB (fun u hu => (key u hu).1) (fun u hu => (key u hu).2)

end LSBA
