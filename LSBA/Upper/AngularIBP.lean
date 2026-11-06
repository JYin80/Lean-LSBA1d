import LSBA.Upper.AngularField
import LSBA.Upper.InvariantApprox
import LSBA.Upper.BatchSmooth

/-!
# Gaussian integration by parts for the angular ratio

The integration by parts in the proof of Lemma 8.11 [up:lem:angular] for the bounded function
`φ(log R_T(Y))`, where `φ' ∈ [0, 1]` equals `1` on `[-t, t]` and `0` off `[-2t, 2t]`: the
invariant function `h` is replaced by smooth invariant approximants, along which the field moves
the terminal flag without changing them ((8.34) [up:eq:angular-geometry]); (8.33)
[up:eq:gaussian-divergence] is applied to the approximants, and dominated convergence passes to
the limit.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The cutoff `ψ_t(s) = min{1, max{0, 3 - 2|s|/t}}`, the derivative `φ'` in the proof of
Lemma 8.11 [up:lem:angular]: it lies in `[0, 1]`, equals `1` on `[-t, t]` and `0` off
`(-3t/2, 3t/2)`. -/
private def angularIBP_ψ (t s : ℝ) : ℝ := min 1 (max 0 (3 - 2 * |s| / t))

/-- `φ_t(s) = ∫₀ˢ ψ_t`, with `|φ_t| ≤ 3t/2`. -/
private def angularIBP_φ (t s : ℝ) : ℝ := ∫ u in (0 : ℝ)..s, angularIBP_ψ t u

private theorem angularIBP_ψ_nonneg (t s : ℝ) : 0 ≤ angularIBP_ψ t s :=
  le_min zero_le_one (le_max_left _ _)

private theorem angularIBP_ψ_le_one (t s : ℝ) : angularIBP_ψ t s ≤ 1 := min_le_left _ _

private theorem angularIBP_ψ_continuous (t : ℝ) : Continuous (angularIBP_ψ t) := by
  unfold angularIBP_ψ; fun_prop

private theorem angularIBP_ψ_eq_one {t s : ℝ} (ht : 0 < t) (hs : |s| ≤ t) :
    angularIBP_ψ t s = 1 := by
  have : 1 ≤ 3 - 2 * |s| / t := by
    rw [le_sub_comm, div_le_iff₀ ht]; linarith
  exact min_eq_left (this.trans (le_max_right _ _))

private theorem angularIBP_ψ_eq_zero {t s : ℝ} (ht : 0 < t) (hs : 3 * t / 2 ≤ |s|) :
    angularIBP_ψ t s = 0 := by
  have : 3 - 2 * |s| / t ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ ht]; linarith
  unfold angularIBP_ψ
  rw [max_eq_left this, min_eq_right zero_le_one]

private theorem angularIBP_ψ_lip {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    |angularIBP_ψ t a - angularIBP_ψ t b| ≤ 2 / t * |a - b| := by
  unfold angularIBP_ψ
  calc |min 1 (max 0 (3 - 2 * |a| / t)) - min 1 (max 0 (3 - 2 * |b| / t))|
      ≤ max |1 - 1| |max 0 (3 - 2 * |a| / t) - max 0 (3 - 2 * |b| / t)| :=
        abs_min_sub_min_le_max _ _ _ _
    _ ≤ |(3 - 2 * |a| / t) - (3 - 2 * |b| / t)| := by
        rw [sub_self, abs_zero]
        refine max_le (abs_nonneg _) ?_
        rw [max_comm 0, max_comm 0]
        exact abs_max_sub_max_le_abs _ _ _
    _ = 2 / t * |(|a| - |b|)| := by
        rw [show (3 - 2 * |a| / t) - (3 - 2 * |b| / t) = -(2 / t * (|a| - |b|)) by ring, abs_neg,
          abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / t)]
    _ ≤ 2 / t * |a - b| :=
        mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub a b) (by positivity)

private theorem angularIBP_φ_hasDerivAt (t s : ℝ) :
    HasDerivAt (angularIBP_φ t) (angularIBP_ψ t s) s :=
  ((angularIBP_ψ_continuous t).integral_hasStrictDerivAt 0 s).hasDerivAt

private theorem angularIBP_φ_contDiff (t : ℝ) : ContDiff ℝ 1 (angularIBP_φ t) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (angularIBP_φ_hasDerivAt t s).differentiableAt, ?_⟩
  have : deriv (angularIBP_φ t) = angularIBP_ψ t :=
    funext fun s => (angularIBP_φ_hasDerivAt t s).deriv
  rw [this]; exact angularIBP_ψ_continuous t

/-- `0 ≤ ∫₀ˢ ψ_t ≤ 3t/2` for `s ≥ 0`. -/
private theorem angularIBP_φ_bound {t : ℝ} (ht : 0 < t) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ angularIBP_φ t s ∧ angularIBP_φ t s ≤ 3 * t / 2 := by
  have hii : ∀ a b : ℝ, IntervalIntegrable (angularIBP_ψ t) volume a b := fun a b =>
    (angularIBP_ψ_continuous t).intervalIntegrable a b
  refine ⟨intervalIntegral.integral_nonneg hs fun u _ => angularIBP_ψ_nonneg t u, ?_⟩
  unfold angularIBP_φ
  rcases le_total s (3 * t / 2) with h | h
  · calc ∫ u in (0 : ℝ)..s, angularIBP_ψ t u ≤ ∫ u in (0 : ℝ)..s, (1 : ℝ) :=
          intervalIntegral.integral_mono_on hs (hii 0 s) intervalIntegrable_const
            fun u _ => angularIBP_ψ_le_one t u
      _ = s := by simp
      _ ≤ 3 * t / 2 := h
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 (3 * t / 2)) (hii _ s)]
    have h1 : ∫ u in (0 : ℝ)..(3 * t / 2), angularIBP_ψ t u ≤
        ∫ u in (0 : ℝ)..(3 * t / 2), (1 : ℝ) :=
      intervalIntegral.integral_mono_on (by positivity) (hii _ _) intervalIntegrable_const
        fun u _ => angularIBP_ψ_le_one t u
    have h2 : ∫ u in (3 * t / 2)..s, angularIBP_ψ t u ≤ ∫ u in (3 * t / 2)..s, (0 : ℝ) :=
      intervalIntegral.integral_mono_on h (hii _ _) intervalIntegrable_const
        fun u hu => (angularIBP_ψ_eq_zero ht (by
          rw [abs_of_nonneg (by linarith [hu.1, ht])]; exact hu.1)).le
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, mul_zero, sub_zero] at h1 h2
    linarith

private theorem angularIBP_φ_abs_le {t : ℝ} (ht : 0 < t) (s : ℝ) :
    |angularIBP_φ t s| ≤ 3 * t / 2 := by
  rcases le_total 0 s with hs | hs
  · obtain ⟨h1, h2⟩ := angularIBP_φ_bound ht hs
    rw [abs_of_nonneg h1]; exact h2
  · have heq : angularIBP_φ t s = -angularIBP_φ t (-s) := by
      unfold angularIBP_φ
      rw [intervalIntegral.integral_symm, neg_inj]
      have hneg : ∀ u, angularIBP_ψ t (-u) = angularIBP_ψ t u := fun u => by
        unfold angularIBP_ψ; rw [abs_neg]
      calc ∫ u in s..0, angularIBP_ψ t u = ∫ u in (-(-s))..(-0), angularIBP_ψ t u := by simp
        _ = ∫ u in (0 : ℝ)..(-s), angularIBP_ψ t (-u) :=
            (intervalIntegral.integral_comp_neg (a := 0) (b := -s) (angularIBP_ψ t)).symm
        _ = ∫ u in (0 : ℝ)..(-s), angularIBP_ψ t u := by simp_rw [hneg]
    obtain ⟨h1, h2⟩ := angularIBP_φ_bound ht (neg_nonneg.mpr hs)
    rw [heq, abs_neg, abs_of_nonneg h1]; exact h2

/-- `A ↦ 1 ⊗ A` as a continuous real-linear map. -/
private def angularIBP_kronCLM (W : ℕ) :
    Matrix (Fin W) (Fin W) ℂ →L[ℝ] Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A
      map_add' := fun A B => Matrix.kronecker_add _ _ _
      map_smul' := fun c A => by
        ext i j
        simp [Matrix.kroneckerMap_apply, mul_left_comm] }

/-- A differentiable function of the projection pair that is invariant under
`(P, P') ↦ (D P D*, D P' D*)`, `D = 1 ⊗ V`, for every unitary `V` has zero derivative along
`([1 ⊗ K, P], [1 ⊗ K, P'])` for skew-Hermitian `K`: the motion of (8.34)
[up:eq:angular-geometry] is the first-order motion under `D = 1 ⊗ e^{sK}`. -/
private theorem angularIBP_fderiv_comm_eq_zero {W : ℕ}
    {p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ}
    (hinv : ∀ V ∈ Matrix.unitaryGroup (Fin W) ℂ,
        ∀ z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
          p (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) * z.1 * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)ᴴ,
            ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) * z.2 * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)ᴴ) =
            p z)
    (z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hp : DifferentiableAt ℝ p z) {K : Matrix (Fin W) (Fin W) ℂ} (hK : Kᴴ = -K) :
    fderiv ℝ p z
      (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) * z.1 - z.1 * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K),
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) * z.2 - z.2 * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K)) =
      0 := by
  set D : ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
    fun s => (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ NormedSpace.exp (s • K) with hD
  have hE : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • K)) K 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) K 0
  have hDd : HasDerivAt D ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) 0 :=
    (angularIBP_kronCLM W).hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hE
  have hDs : HasDerivAt (fun s => (D s)ᴴ) ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K)ᴴ 0 := hDd.star
  have hD0 : D 0 = 1 := by simp [hD]
  have hcurve : ∀ A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      HasDerivAt (fun s => D s * A * (D s)ᴴ)
        (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) * A - A * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K))
        0 := by
    intro A
    have := (hDd.mul (hasDerivAt_const (0 : ℝ) A)).mul hDs
    convert this using 1
    have hneg : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (-K) = -((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) :=
      (angularIBP_kronCLM W).map_neg K
    simp only [Pi.mul_apply, hD0, Matrix.conjTranspose_kronecker, hK, Matrix.conjTranspose_one,
      hneg, mul_one, one_mul, mul_zero, add_zero, mul_neg]
    abel
  have hγ := (hcurve z.1).prodMk (hcurve z.2)
  have hγ0 : (D 0 * z.1 * (D 0)ᴴ, D 0 * z.2 * (D 0)ᴴ) = z := by simp [hD0]
  have hc := (hγ0 ▸ hp).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ
  have hconst : (p ∘ fun s => (D s * z.1 * (D s)ᴴ, D s * z.2 * (D s)ᴴ)) = fun _ => p z := by
    funext s
    -- `e^{sK}` is unitary
    have hu : NormedSpace.exp (s • K) ∈ Matrix.unitaryGroup (Fin W) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]
      have h1 : star (NormedSpace.exp (s • K)) = NormedSpace.exp (-(s • K)) := by
        rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul,
          hK]
        simp
      rw [h1, Matrix.exp_neg]
      exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_exp _).map Matrix.detMonoidHom)
    exact hinv _ hu z
  rw [hconst] at hc
  have := hc.unique (hasDerivAt_const (0 : ℝ) (p z))
  rw [hγ0] at this
  exact this

/-- `log h` is bounded and measurable for bounded measurable `h ≥ ε > 0`. -/
private theorem angularIBP_isBddMeas_log {W : ℕ} {h : IsoFlag W → ℝ} (hh : IsBddMeas h) {ε : ℝ}
    (hε : 0 < ε) (hhε : ∀ z, ε ≤ h z) : IsBddMeas (fun z => Real.log (h z)) := by
  obtain ⟨hm, M, hM⟩ := hh
  refine ⟨Real.measurable_log.comp hm, |Real.log ε| + |M|, fun z => ?_⟩
  have hz : 0 < h z := hε.trans_le (hhε z)
  have h1 : Real.log ε ≤ Real.log (h z) := Real.log_le_log hε (hhε z)
  have h2 : Real.log (h z) ≤ h z - 1 := Real.log_le_sub_one_of_pos hz
  have h3 : h z ≤ |M| := (le_abs_self _).trans ((hM z).trans (le_abs_self M))
  rw [abs_le]; constructor
  · linarith [neg_abs_le (Real.log ε), abs_nonneg M]
  · linarith [abs_nonneg (Real.log ε)]

open Filter Topology in
/-- The integration by parts of the proof of Lemma 8.11 [up:lem:angular] for any `C¹` functions
`p n` of the projection pair with `∫ |p n - log h| dν → 0`, `ν` the law of the terminal flag,
whose derivative at the terminal flag vanishes along the motion of the flag wherever `χ ≠ 0`. -/
private theorem angularIBP_core {W : ℕ} {q : ℕ} {χ : Ω W q → ℝ} {Y : Ω W q → Ω W q}
    (hχm : Measurable χ) (hχ : ∀ ω, 0 ≤ χ ω ∧ χ ω ≤ 1)
    (hadm : IBPAdmissible (fun ω => χ ω • Y ω))
    (Λ : Ω W q → IsoFlag W) (c : Ω W q → ℝ) (hΛm : Measurable Λ) (hcm : Measurable c)
    (hcC : ContDiff ℝ 1 c) (hcPG : PolyGrowth (fderiv ℝ c))
    (hΛC : ContDiff ℝ 1 (fun ω => (Λ ω : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)))
    (hΛPG : PolyGrowth (fderiv ℝ (fun ω => (Λ ω : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))))
    {h : IsoFlag W → ℝ} (hh : IsBddMeas h) {ε : ℝ} (hε : 0 < ε) (hhε : ∀ z, ε ≤ h z)
    (r : ℝ) {t : ℝ} (ht : 0 < t)
    (p : ℕ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ)
    (hp : ∀ n, ContDiff ℝ 1 (p n))
    (hconv : Tendsto (fun n => ∫ x, |p n x.1 - Real.log (h x)| ∂(Measure.map Λ (μ W q))) atTop
      (𝓝 0))
    (hgeom : ∀ n ω, χ ω ≠ 0 → HasLineDerivAt ℝ c 1 ω (Y ω) ∧
      ∃ v, HasLineDerivAt ℝ (fun η => (Λ η : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
          Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) v ω (Y ω) ∧
        fderiv ℝ (p n) (Λ ω : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
          Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) v = 0) :
    2 * ∫ ω, χ ω * Set.indicator {ω | |-Real.log r - 2 * c ω + 4 * Real.log (h (Λ ω))| ≤ t}
        (fun _ => (1 : ℝ)) ω ∂(μ W q) ≤
      3 * t / 2 * ∫ ω, |gaussDiv (fun η => χ η • Y η) ω| ∂(μ W q) := by
  set δ : Ω W q → ℝ := gaussDiv (fun η => χ η • Y η) with hδdef
  obtain ⟨hβm, Bβ, hBβ⟩ := angularIBP_isBddMeas_log hh hε hhε
  have hpc : ∀ n, Continuous (p n) := fun n => (hp n).continuous
  -- `δ_G (χ Y)` is integrable: the test function `1`
  have hconstTest : IsIBPTest (fun _ : Ω W q => (1 : ℝ)) :=
    ⟨contDiff_const, ⟨1, fun _ => by simp⟩, ⟨0, 0, fun x => by simp⟩⟩
  have hδi : Integrable δ (μ W q) := by
    have := (hadm.2 _ hconstTest).2.1
    simp only [one_mul] at this
    exact this
  -- the approximate ratios `L_n = -log r - 2 c + 4 p_n(P_{TU}, P_{TY})`
  set L : ℕ → Ω W q → ℝ := fun n ω => -Real.log r - 2 * c ω + 4 * p n (Λ ω).1 with hLdef
  have hLC : ∀ n, ContDiff ℝ 1 (L n) := fun n =>
    (contDiff_const.sub (contDiff_const.mul hcC)).add (contDiff_const.mul ((hp n).comp hΛC))
  have hint : ∀ F : Ω W q → ℝ, Measurable F →
      Integrable (fun ω => χ ω * angularIBP_ψ t (F ω)) (μ W q) := by
    intro F hF
    refine Integrable.of_bound
      (hχm.mul ((angularIBP_ψ_continuous t).measurable.comp hF)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ ω).1,
      abs_of_nonneg (angularIBP_ψ_nonneg _ _)]
    exact (mul_le_mul (hχ ω).2 (angularIBP_ψ_le_one _ _) (angularIBP_ψ_nonneg _ _)
      zero_le_one).trans_eq (one_mul 1)
  -- (8.33) [up:eq:gaussian-divergence] for `φ_t(L_n)`: `2 𝔼[χ ψ_t(L_n)] ≤ (3t/2) 𝔼 |δ_G (χ Y)|`
  have hstep : ∀ n, 2 * ∫ ω, χ ω * angularIBP_ψ t (L n ω) ∂(μ W q) ≤
      3 * t / 2 * ∫ ω, |δ ω| ∂(μ W q) := by
    intro n
    obtain ⟨B, hB⟩ := (isCompact_isoFlags W).exists_bound_of_continuousOn
      ((hp n).continuous_fderiv one_ne_zero).continuousOn
    obtain ⟨C₁, k₁, hC₁⟩ := hcPG
    obtain ⟨C₂, k₂, hC₂⟩ := hΛPG
    have hderiv : ∀ ω, HasFDerivAt (fun η => angularIBP_φ t (L n η))
        (angularIBP_ψ t (L n ω) • (-((2 : ℝ) • fderiv ℝ c ω) +
          (4 : ℝ) • (fderiv ℝ (p n) (Λ ω).1).comp (fderiv ℝ (fun η => (Λ η).1) ω))) ω := by
      intro ω
      have hc1 : HasFDerivAt c (fderiv ℝ c ω) ω := (hcC.differentiable one_ne_zero ω).hasFDerivAt
      have hΛ1 : HasFDerivAt (fun η => (Λ η).1) (fderiv ℝ (fun η => (Λ η).1) ω) ω :=
        (hΛC.differentiable one_ne_zero ω).hasFDerivAt
      have hp1 : HasFDerivAt (p n) (fderiv ℝ (p n) (Λ ω).1) (Λ ω).1 :=
        ((hp n).differentiable one_ne_zero _).hasFDerivAt
      have hL1 : HasFDerivAt (L n) (-((2 : ℝ) • fderiv ℝ c ω) +
          (4 : ℝ) • (fderiv ℝ (p n) (Λ ω).1).comp (fderiv ℝ (fun η => (Λ η).1) ω)) ω :=
        ((hc1.const_mul 2).const_sub _).add ((hp1.comp ω hΛ1).const_mul 4)
      exact (angularIBP_φ_hasDerivAt t (L n ω)).comp_hasFDerivAt ω hL1
    have htest : IsIBPTest (fun η => angularIBP_φ t (L n η)) := by
      refine ⟨(angularIBP_φ_contDiff t).comp (hLC n),
        ⟨3 * t / 2, fun x => angularIBP_φ_abs_le ht _⟩, ?_⟩
      refine ⟨2 * |C₁| + 4 * (|B| * |C₂|), k₁ + k₂, fun ω => ?_⟩
      rw [(hderiv ω).fderiv]
      have h1x : (1 : ℝ) ≤ 1 + ‖ω‖ := by linarith [norm_nonneg ω]
      have hX : 0 ≤ (1 + ‖ω‖) ^ (k₁ + k₂) := by positivity
      have a1 : ‖fderiv ℝ c ω‖ ≤ |C₁| * (1 + ‖ω‖) ^ (k₁ + k₂) :=
        (hC₁ ω).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1x (by omega)) (abs_nonneg _)))
      have a2 : ‖fderiv ℝ (fun η => (Λ η).1) ω‖ ≤ |C₂| * (1 + ‖ω‖) ^ (k₁ + k₂) :=
        (hC₂ ω).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1x (by omega)) (abs_nonneg _)))
      have a3 : ‖fderiv ℝ (p n) (Λ ω).1‖ ≤ |B| := (hB _ (Λ ω).2).trans (le_abs_self _)
      have a4 : ‖(fderiv ℝ (p n) (Λ ω).1).comp (fderiv ℝ (fun η => (Λ η).1) ω)‖ ≤
          |B| * (|C₂| * (1 + ‖ω‖) ^ (k₁ + k₂)) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul a3 a2 (norm_nonneg _) (abs_nonneg _))
      have hψ : ‖angularIBP_ψ t (L n ω)‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (angularIBP_ψ_nonneg _ _)]; exact angularIBP_ψ_le_one _ _
      rw [norm_smul]
      refine (mul_le_of_le_one_left (norm_nonneg _) hψ).trans ?_
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      nlinarith
    have hval : ∀ ω, fderiv ℝ (fun η => angularIBP_φ t (L n η)) ω (χ ω • Y ω) =
        -2 * (χ ω * angularIBP_ψ t (L n ω)) := by
      intro ω
      rw [(hderiv ω).fderiv, smul_apply, map_smul]
      by_cases h0 : χ ω = 0
      · simp [h0]
      obtain ⟨hcl, v, hΛl, hpv⟩ := hgeom n ω h0
      have e1 : fderiv ℝ c ω (Y ω) = 1 :=
        ((hcC.differentiable one_ne_zero ω).hasFDerivAt.hasLineDerivAt (Y ω)).unique hcl
      have e2 : fderiv ℝ (fun η => (Λ η).1) ω (Y ω) = v :=
        ((hΛC.differentiable one_ne_zero ω).hasFDerivAt.hasLineDerivAt (Y ω)).unique hΛl
      simp only [add_apply, neg_apply,
        smul_apply, ContinuousLinearMap.comp_apply, e1, e2, smul_eq_mul]
      rw [hpv]
      ring
    obtain ⟨-, hint2, heq⟩ := hadm.2 _ htest
    rw [← μ_eq_stdGauss W q] at hint2 heq
    simp_rw [hval] at heq
    rw [integral_const_mul] at heq
    have hle : -∫ ω, angularIBP_φ t (L n ω) * δ ω ∂(μ W q) ≤
        3 * t / 2 * ∫ ω, |δ ω| ∂(μ W q) := by
      rw [← integral_neg, ← integral_const_mul]
      refine integral_mono hint2.neg (hδi.abs.const_mul _) fun ω => ?_
      have := angularIBP_φ_abs_le ht (L n ω)
      calc -(angularIBP_φ t (L n ω) * δ ω) ≤ |angularIBP_φ t (L n ω) * δ ω| := neg_le_abs _
        _ = |angularIBP_φ t (L n ω)| * |δ ω| := abs_mul _ _
        _ ≤ 3 * t / 2 * |δ ω| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
    linarith
  -- passage to the limit `p n → log h` in `L¹(ν)`
  set LA : Ω W q → ℝ := fun ω => -Real.log r - 2 * c ω + 4 * Real.log (h (Λ ω)) with hLAdef
  have hLAm : Measurable LA := (measurable_const.sub (hcm.const_mul 2)).add
      ((Real.measurable_log.comp (hh.1.comp hΛm)).const_mul 4)
  have hint2 : ∀ n, Integrable (fun ω => |p n (Λ ω).1 - Real.log (h (Λ ω))|) (μ W q) := by
    intro n
    obtain ⟨Bp, hBp⟩ := (isCompact_isoFlags W).exists_bound_of_continuousOn (hpc n).continuousOn
    refine Integrable.of_bound ((((hpc n).measurable.comp (measurable_subtype_coe.comp hΛm)).sub
      (hβm.comp hΛm)).abs.aestronglyMeasurable) (Bp + Bβ) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := hBp _ (Λ ω).2
    rw [Real.norm_eq_abs] at h1
    exact (abs_sub _ _).trans (add_le_add h1 (hBβ _))
  have hmap : ∀ n, ∫ ω, |p n (Λ ω).1 - Real.log (h (Λ ω))| ∂(μ W q) =
      ∫ x, |p n x.1 - Real.log (h x)| ∂(Measure.map Λ (μ W q)) := fun n =>
    (integral_map hΛm.aemeasurable
      (((hpc n).comp continuous_subtype_val).measurable.sub hβm).abs.aestronglyMeasurable).symm
  have hpt : ∀ n ω, χ ω * angularIBP_ψ t (LA ω) ≤
      χ ω * angularIBP_ψ t (L n ω) + 8 / t * |p n (Λ ω).1 - Real.log (h (Λ ω))| := by
    intro n ω
    have hd : LA ω - L n ω =
        -(4 * (p n (Λ ω).1 - Real.log (h (Λ ω)))) := by
      simp only [hLAdef, hLdef]; ring
    have hl := angularIBP_ψ_lip ht (LA ω) (L n ω)
    rw [hd, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hl
    have h1 : χ ω * (angularIBP_ψ t (LA ω) - angularIBP_ψ t (L n ω)) ≤
        |angularIBP_ψ t (LA ω) - angularIBP_ψ t (L n ω)| :=
      (mul_le_mul_of_nonneg_left (le_abs_self _) (hχ ω).1).trans
        (mul_le_of_le_one_left (abs_nonneg _) (hχ ω).2)
    have e1 : 2 / t * (4 * |p n (Λ ω).1 - Real.log (h (Λ ω))|) =
        8 / t * |p n (Λ ω).1 - Real.log (h (Λ ω))| := by ring
    have e2 : χ ω * (angularIBP_ψ t (LA ω) - angularIBP_ψ t (L n ω)) =
        χ ω * angularIBP_ψ t (LA ω) - χ ω * angularIBP_ψ t (L n ω) := by
      ring
    linarith
  have hlim : ∀ n, 2 * ∫ ω, χ ω * angularIBP_ψ t (LA ω) ∂(μ W q) ≤
      3 * t / 2 * ∫ ω, |δ ω| ∂(μ W q) +
        16 / t * ∫ x, |p n x.1 - Real.log (h x)| ∂(Measure.map Λ (μ W q)) := by
    intro n
    have hm := integral_mono (hint _ hLAm)
      ((hint _ (hLC n).continuous.measurable).add ((hint2 n).const_mul (8 / t))) (hpt n)
    simp only [Pi.add_apply] at hm
    rw [integral_add (hint _ (hLC n).continuous.measurable) ((hint2 n).const_mul _),
      integral_const_mul, hmap n] at hm
    have := hstep n
    have e : 16 / t * ∫ x, |p n x.1 - Real.log (h x)| ∂(Measure.map Λ (μ W q)) =
        2 * (8 / t * ∫ x, |p n x.1 - Real.log (h x)| ∂(Measure.map Λ (μ W q))) := by ring
    linarith
  have hA : 2 * ∫ ω, χ ω * angularIBP_ψ t (LA ω) ∂(μ W q) ≤
      3 * t / 2 * ∫ ω, |δ ω| ∂(μ W q) := by
    have ht0 := (tendsto_const_nhds (x := 3 * t / 2 * ∫ ω, |δ ω| ∂(μ W q))).add
      (hconv.const_mul (16 / t))
    rw [mul_zero, add_zero] at ht0
    exact ge_of_tendsto' ht0 hlim
  have hind : ∫ ω, χ ω * Set.indicator {ω | |LA ω| ≤ t}
      (fun _ => (1 : ℝ)) ω ∂(μ W q) ≤
      ∫ ω, χ ω * angularIBP_ψ t (LA ω) ∂(μ W q) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun ω => ?_) (hint _ hLAm)
      (Eventually.of_forall fun ω => ?_)
    · exact mul_nonneg (hχ ω).1 (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    · refine mul_le_mul_of_nonneg_left ?_ (hχ ω).1
      by_cases hω : |LA ω| ≤ t
      · rw [Set.indicator_of_mem (show ω ∈ {ω | |LA ω| ≤ t} from hω),
          angularIBP_ψ_eq_one ht hω]
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | |LA ω| ≤ t} from hω)]
        exact angularIBP_ψ_nonneg _ _
  linarith

/-- Proof of Lemma 8.11 [up:lem:angular]: for bounded measurable `h ≥ ε > 0` satisfying (8.25)
[up:eq:invariant-function], `r > 0` and `t > 0`,
`2 𝔼[χ 1{|log R_T(Y)| ≤ t}] ≤ (3t/2) 𝔼 |δ_G (χ Y)|`. -/
theorem two_mul_integral_cutoff_le {W : ℕ} {g E : ℝ} {q : ℕ} {b C : ℝ} {y : IsoFlag W}
    {χ : Ω W q → ℝ} {Y : Ω W q → Ω W q} (hfield : AngularFieldAt W g E q b C y χ Y)
    {h : IsoFlag W → ℝ} (hh : IsBddMeas h) {ε : ℝ} (hε : 0 < ε) (hhε : ∀ z, ε ≤ h z)
    (hinv : IsSimulInvariant h) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    2 * ∫ ω, χ ω * Set.indicator {ω | |logAngRatio W g E q h r y ω| ≤ t} (fun _ => (1 : ℝ)) ω
        ∂(μ W q) ≤
      3 * t / 2 * ∫ ω, |gaussDiv (fun η => χ η • Y η) ω| ∂(μ W q) := by
  obtain ⟨hχm, hχ, hgeomK, hadm, -, -⟩ := hfield
  have hBy := (measurable_batchMat W g E q).prodMk
    (measurable_const : Measurable fun _ : Ω W q => y)
  have h1 := (measurable_flagAct W).comp hBy
  have h2 := (measurable_volCocycle W).comp hBy
  have hΛm : Measurable fun ω : Ω W q => flagAct (batchMat W g E q ω) y := h1
  have hcm : Measurable fun ω : Ω W q => volCocycle (batchMat W g E q ω) y := h2
  obtain ⟨hcC, hcPG⟩ := contDiff_volCocycle_batchMat W g E q y
  obtain ⟨hΛC, hΛPG⟩ := contDiff_flagAct_batchMat W g E q y
  obtain ⟨p, hp, hpinv, hconv⟩ := exists_invariant_contDiff_flagApprox
    (Measure.map (fun ω : Ω W q => flagAct (batchMat W g E q ω) y) (μ W q))
    (angularIBP_isBddMeas_log hh hε hhε) (fun V hV x => congrArg Real.log (hinv V hV x))
  exact angularIBP_core hχm hχ hadm _ _ hΛm hcm hcC hcPG hΛC hΛPG hh hε hhε r ht p hp hconv
    fun n ω hω => by
      obtain ⟨K, hK, hc1, hΛ1⟩ := hgeomK ω hω
      exact ⟨hc1, _, hΛ1, angularIBP_fderiv_comm_eq_zero (hpinv n) _
        ((hp n).differentiable one_ne_zero _) hK⟩

/-- The same with `K_out = 0`, for every bounded measurable `h ≥ ε > 0`. -/
theorem two_mul_integral_cutoff_le_of_zero {W : ℕ} {g E : ℝ} {q : ℕ} {b C : ℝ} {y : IsoFlag W}
    {χ : Ω W q → ℝ} {Y : Ω W q → Ω W q} (hfield : AngularFieldZeroAt W g E q b C y χ Y)
    {h : IsoFlag W → ℝ} (hh : IsBddMeas h) {ε : ℝ} (hε : 0 < ε) (hhε : ∀ z, ε ≤ h z)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    2 * ∫ ω, χ ω * Set.indicator {ω | |logAngRatio W g E q h r y ω| ≤ t} (fun _ => (1 : ℝ)) ω
        ∂(μ W q) ≤
      3 * t / 2 * ∫ ω, |gaussDiv (fun η => χ η • Y η) ω| ∂(μ W q) := by
  obtain ⟨hχm, hχ, hgeom0, hadm, -, -⟩ := hfield
  have hBy := (measurable_batchMat W g E q).prodMk
    (measurable_const : Measurable fun _ : Ω W q => y)
  have h1 := (measurable_flagAct W).comp hBy
  have h2 := (measurable_volCocycle W).comp hBy
  have hΛm : Measurable fun ω : Ω W q => flagAct (batchMat W g E q ω) y := h1
  have hcm : Measurable fun ω : Ω W q => volCocycle (batchMat W g E q ω) y := h2
  obtain ⟨hcC, hcPG⟩ := contDiff_volCocycle_batchMat W g E q y
  obtain ⟨hΛC, hΛPG⟩ := contDiff_flagAct_batchMat W g E q y
  obtain ⟨p, hp, hconv⟩ := exists_contDiff_flagApprox
    (Measure.map (fun ω : Ω W q => flagAct (batchMat W g E q ω) y) (μ W q))
    (angularIBP_isBddMeas_log hh hε hhε)
  exact angularIBP_core hχm hχ hadm _ _ hΛm hcm hcC hcPG hΛC hΛPG hh hε hhε r ht p hp hconv
    fun n ω hω => by
      obtain ⟨hc1, hΛ1⟩ := hgeom0 ω hω
      refine ⟨hc1, _, hΛ1, ?_⟩
      simp only [Matrix.kronecker_zero, zero_mul, mul_zero, sub_zero, Prod.mk_zero_zero, map_zero]

end LSBA
