import LSBA.Gauss.QuadSmallBall

/-!
# Ratio of `‖Q x‖` to a centred quadratic form

For a nonzero Hermitian `Q`, a standard complex Gaussian vector `γ`, `x = γ + b` and `a ∈ ℝ`:
`P(‖Q x‖₂ ≥ t |x* Q x - a|) ≤ C / t`. This is the complex form of [APSSS, Lemma 2.1 (2.7)],
proved by diagonalizing `Q` and splitting the eigenvalues into a dominant index or two halves of
comparable weight.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Conditioning on all coordinates but some -/

/-- If, for every value of the other coordinates, the conditional probability of `S` given the
coordinates outside `s` is at most `c`, then `P(S) ≤ c`. -/
private lemma quadRatio_le_of_lmarginal_le {ι : Type*} [Fintype ι] (s : Finset ι)
    {S : Set (ι → ℂ)} (hS : MeasurableSet S) {c : ℝ≥0∞}
    (h : ∀ x, (∫⋯∫⁻_s, S.indicator 1 ∂fun _ : ι => cGauss) x ≤ c) : stdCGauss ι S ≤ c := by
  have hconst : (∫⋯∫⁻_s, (fun _ => c) ∂fun _ : ι => cGauss) = fun _ => c := by
    ext x
    simp [lmarginal]
  calc stdCGauss ι S = ∫⁻ x, S.indicator 1 x ∂stdCGauss ι := (lintegral_indicator_one hS).symm
    _ ≤ ∫⁻ _, c ∂stdCGauss ι := by
      unfold stdCGauss
      exact lintegral_le_of_lmarginal_le s (measurable_one.indicator hS) measurable_const
        (by rw [hconst]; exact h)
    _ = c := by simp

/-! ### The second moment of a block -/

/-- `E ∑_{j ∈ S} E_j² |x_j + b_j|² = ∑_{j ∈ S} E_j² (1 + |b_j|²)`. -/
private lemma quadRatio_lintegral_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → ℝ)
    (b : ι → ℂ) (S : Finset ι) :
    ∫⁻ z, ENNReal.ofReal (∑ j ∈ S, E j ^ 2 * ‖z j + b j‖ ^ 2) ∂stdCGauss ι =
      ENNReal.ofReal (∑ j ∈ S, E j ^ 2 * (1 + ‖b j‖ ^ 2)) := by
  obtain ⟨d, hd⟩ : ∃ d : ι → ℂ, d = fun j => if j ∈ S then (E j : ℂ) else 0 := ⟨_, rfl⟩
  have hl : ∀ v : ι → ℂ,
      l2Norm (Matrix.diagonal d *ᵥ v) ^ 2 = ∑ j ∈ S, E j ^ 2 * ‖v j‖ ^ 2 := by
    intro v
    rw [l2Norm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    simp only [Matrix.mulVec_diagonal, hd]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun j => j ∉ S)
      (fun j hj => by simp [(Finset.mem_filter.mp hj).2]), add_zero]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [hj, ↓reduceIte, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have h := lintegral_l2Norm_sq_stdCGauss (Matrix.diagonal d) b
  simp only [Pi.add_apply, hl] at h
  rw [h]
  congr 1
  have hdiag : ∑ i, ∑ j, ‖Matrix.diagonal d i j‖ ^ 2 = ∑ j ∈ S, E j ^ 2 := by
    have hrow : ∀ i, ∑ j, ‖Matrix.diagonal d i j‖ ^ 2 = ‖d i‖ ^ 2 := fun i => by
      rw [Fintype.sum_eq_single i fun j hj => by
        rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), norm_zero, zero_pow two_ne_zero],
        Matrix.diagonal_apply_eq]
    rw [Finset.sum_congr rfl fun i _ => hrow i, hd]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun j => j ∉ S)
      (fun j hj => by simp [(Finset.mem_filter.mp hj).2]), add_zero]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [hj, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hdiag, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### One block of the eigenvalues carries a quarter of the weight -/

/-- If the indices in `T` carry at least a quarter of `ν² = ∑ E_j² (1 + |b_j|²)`, then
`P(t |∑ E_j |x_j + b_j|² - a| ≤ 2 ‖diag(E) 1_{Tᶜ} x‖₂) ≤ 4 C₇ / t`, where `C₇` is the constant
of the small-ball bound for `∑ E_j |x_j + b_j|²`. -/
private lemma quadRatio_part.{u} {ι : Type u} [Fintype ι] {C₇ : ℝ} (hC₇ : 0 < C₇)
    (h₇ : ∀ {κ : Type u} [Fintype κ] (E : κ → ℝ) (b : κ → ℂ) (a ε : ℝ), 0 < ε →
      (∃ j, E j ≠ 0) →
      stdCGauss κ {x | |∑ j, E j * ‖x j + b j‖ ^ 2 - a| ≤ ε} ≤
        ENNReal.ofReal (C₇ * ε / Real.sqrt (∑ k, E k ^ 2 * (1 + ‖b k‖ ^ 2))))
    (E : ι → ℝ) (b : ι → ℂ) (a t : ℝ) (ht : 0 < t) (T : Finset ι)
    (hν : 0 < ∑ k, E k ^ 2 * (1 + ‖b k‖ ^ 2))
    (hT : ∑ k, E k ^ 2 * (1 + ‖b k‖ ^ 2) ≤ 4 * ∑ k ∈ T, E k ^ 2 * (1 + ‖b k‖ ^ 2)) :
    stdCGauss ι {z | t * |∑ j, E j * ‖z j + b j‖ ^ 2 - a| ≤
      2 * Real.sqrt (∑ j ∈ Tᶜ, E j ^ 2 * ‖z j + b j‖ ^ 2)} ≤ ENNReal.ofReal (4 * C₇ / t) := by
  set w : ι → ℝ := fun k => E k ^ 2 * (1 + ‖b k‖ ^ 2) with hw
  set V := ∑ k, w k with hV
  set ν := Real.sqrt V with hνdef
  have hνpos : 0 < ν := Real.sqrt_pos.mpr hν
  have hνsq : ν ^ 2 = V := Real.sq_sqrt hν.le
  set σ : (ι → ℂ) → ℝ := fun z => ∑ j ∈ Tᶜ, E j ^ 2 * ‖z j + b j‖ ^ 2 with hσ
  have hσ0 : ∀ z, 0 ≤ σ z := fun z => Finset.sum_nonneg fun _ _ => by positivity
  have hσc : Continuous σ := by
    simp only [hσ]
    fun_prop
  set Ev := {z : ι → ℂ | t * |∑ j, E j * ‖z j + b j‖ ^ 2 - a| ≤ 2 * Real.sqrt (σ z)} with hEv
  have hEvm : MeasurableSet Ev :=
    measurableSet_le (by fun_prop) (continuous_const.mul hσc.sqrt).measurable
  set c₁ := 2 * C₇ / (t * V) with hc₁
  set c₂ := 2 * C₇ / t with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  set g : (ι → ℂ) → ℝ≥0∞ := fun z => ENNReal.ofReal c₁ * ENNReal.ofReal (σ z) + ENNReal.ofReal c₂
    with hg
  have hgm : Measurable g :=
    ((ENNReal.measurable_ofReal.comp hσc.measurable).const_mul _).add_const _
  -- `σ`, hence `g`, does not depend on the coordinates in `T`
  have hσu : ∀ x (y : T → ℂ), σ (Function.updateFinset x T y) = σ x := by
    intro x y
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_compl] at hj
    simp [Function.updateFinset_def, hj]
  have hgT : (∫⋯∫⁻_T, g ∂fun _ : ι => cGauss) = g := by
    ext x
    simp only [lmarginal, hg, hσu]
    simp
  have hWT : ∑ k : T, w k = ∑ k ∈ T, w k := Finset.sum_coe_sort T w
  have hslice : ∀ x, (∫⋯∫⁻_T, Ev.indicator 1 ∂fun _ : ι => cGauss) x ≤ g x := by
    intro x
    have hE : ∃ j : T, E j ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : ∑ k ∈ T, w k = 0 := Finset.sum_eq_zero fun k hk => by simp [hw, h ⟨k, hk⟩]
      linarith
    set ε := (σ x / ν + ν) / t with hε
    have hεpos : 0 < ε := by
      have := hσ0 x
      positivity
    have hsub : (fun y : T → ℂ => Function.updateFinset x T y) ⁻¹' Ev ⊆
        {y : T → ℂ | |∑ j : T, E j * ‖y j + b j‖ ^ 2 -
          (a - ∑ j ∈ Tᶜ, E j * ‖x j + b j‖ ^ 2)| ≤ ε} := by
      intro y hy
      simp only [Set.mem_preimage, hEv, Set.mem_ofPred_eq, hσu] at hy
      have hsplit : ∑ j, E j * ‖Function.updateFinset x T y j + b j‖ ^ 2 =
          ∑ j : T, E j * ‖y j + b j‖ ^ 2 + ∑ j ∈ Tᶜ, E j * ‖x j + b j‖ ^ 2 := by
        rw [← Finset.sum_add_sum_compl T, ← Finset.sum_coe_sort T]
        congr 1
        · refine Finset.sum_congr rfl fun j _ => ?_
          simp [Function.updateFinset_def, j.2]
        · refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.mem_compl] at hj
          simp [Function.updateFinset_def, hj]
      rw [hsplit] at hy
      simp only [Set.mem_ofPred_eq]
      have h2 : 2 * Real.sqrt (σ x) ≤ σ x / ν + ν := by
        rw [div_add' _ _ _ hνpos.ne', le_div_iff₀ hνpos]
        nlinarith [sq_nonneg (Real.sqrt (σ x) - ν), Real.sq_sqrt (hσ0 x)]
      rw [hε, le_div_iff₀ ht]
      have heq : ∑ j : T, E j * ‖y j + b j‖ ^ 2 - (a - ∑ j ∈ Tᶜ, E j * ‖x j + b j‖ ^ 2) =
          ∑ j : T, E j * ‖y j + b j‖ ^ 2 + ∑ j ∈ Tᶜ, E j * ‖x j + b j‖ ^ 2 - a := by ring
      rw [heq, mul_comm]
      linarith
    have hsqT : ν / 2 ≤ Real.sqrt (∑ k : T, w k) := by
      rw [hWT, hνdef, show Real.sqrt V / 2 = Real.sqrt (V / 4) by
        rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    calc (∫⋯∫⁻_T, Ev.indicator 1 ∂fun _ : ι => cGauss) x
        = stdCGauss T ((fun y : T → ℂ => Function.updateFinset x T y) ⁻¹' Ev) := by
          rw [← lintegral_indicator_one (measurable_updateFinset hEvm)]
          rfl
      _ ≤ ENNReal.ofReal (C₇ * ε / Real.sqrt (∑ k : T, w k)) :=
          (measure_mono hsub).trans (h₇ (fun j : T => E j) (fun j : T => b j) _ ε hεpos hE)
      _ ≤ g x := by
          simp only [hg]
          rw [← ENNReal.ofReal_mul hc₁0, ← ENNReal.ofReal_add (by positivity) hc₂0]
          apply ENNReal.ofReal_le_ofReal
          have hν2 : 0 < ν / 2 := by positivity
          calc C₇ * ε / Real.sqrt (∑ k : T, w k) ≤ C₇ * ε / (ν / 2) :=
                div_le_div_of_nonneg_left (by positivity) hν2 hsqT
            _ = c₁ * σ x + c₂ := by
                rw [hε, hc₁, hc₂, ← hνsq]
                field_simp
  have hWS : ∑ k ∈ Tᶜ, w k ≤ V :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => by positivity
  calc stdCGauss ι Ev = ∫⁻ z, Ev.indicator 1 z ∂stdCGauss ι := (lintegral_indicator_one hEvm).symm
    _ ≤ ∫⁻ z, g z ∂stdCGauss ι := by
        unfold stdCGauss
        exact lintegral_le_of_lmarginal_le T (measurable_one.indicator hEvm) hgm
          (by rw [hgT]; exact hslice)
    _ = ENNReal.ofReal c₁ * ENNReal.ofReal (∑ k ∈ Tᶜ, w k) + ENNReal.ofReal c₂ := by
        rw [hg, lintegral_add_right _ measurable_const,
          lintegral_const_mul _ hσc.measurable.ennreal_ofReal]
        simp only [hσ]
        rw [quadRatio_lintegral_sq, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (4 * C₇ / t) := by
        rw [← ENNReal.ofReal_mul hc₁0, ← ENNReal.ofReal_add (by positivity) hc₂0]
        apply ENNReal.ofReal_le_ofReal
        calc c₁ * ∑ k ∈ Tᶜ, w k + c₂ ≤ c₁ * V + c₂ := by gcongr
          _ = 4 * C₇ / t := by
              rw [hc₁, hc₂]
              field_simp
              ring

/-! ### The dominant index -/

/-- `P(t |∑ E_i |x_i + b_i|² - a| ≤ 2 |E_j| |x_j + b_j|) ≤ 2 C₃ / t` for `E_j ≠ 0`, where `C₃` is
the constant of the bound `P(|x| ≥ t ||x|² - c|) ≤ C₃ / t` for one coordinate. -/
private lemma quadRatio_single {ι : Type*} [Fintype ι] {C₃ : ℝ}
    (h₃ : ∀ (β : ℂ) (c t : ℝ), 0 < t →
      cGauss {z | t * |‖z + β‖ ^ 2 - c| ≤ ‖z + β‖} ≤ ENNReal.ofReal (C₃ / t))
    (E : ι → ℝ) (b : ι → ℂ) (a t : ℝ) (ht : 0 < t) (j : ι) (hj : E j ≠ 0) :
    stdCGauss ι {z | t * |∑ i, E i * ‖z i + b i‖ ^ 2 - a| ≤ 2 * (|E j| * ‖z j + b j‖)} ≤
      ENNReal.ofReal (2 * C₃ / t) := by
  set Ev := {z : ι → ℂ | t * |∑ i, E i * ‖z i + b i‖ ^ 2 - a| ≤ 2 * (|E j| * ‖z j + b j‖)}
    with hEv
  have hm : MeasurableSet Ev := measurableSet_le (by fun_prop) (by fun_prop)
  have hEa : 0 < |E j| := abs_pos.mpr hj
  refine quadRatio_le_of_lmarginal_le {j} hm fun x => ?_
  rw [lmarginal_singleton]
  dsimp only
  set R := ∑ i ∈ Finset.univ.erase j, E i * ‖x i + b i‖ ^ 2 with hR
  set c := (a - R) / E j with hc
  have hsub : (fun z => Function.update x j z) ⁻¹' Ev ⊆
      {z | t / 2 * |‖z + b j‖ ^ 2 - c| ≤ ‖z + b j‖} := by
    intro z hz
    simp only [Set.mem_preimage, hEv, Set.mem_ofPred_eq] at hz
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self] at hz
    have hrest : ∑ i ∈ Finset.univ.erase j, E i * ‖Function.update x j z i + b i‖ ^ 2 = R := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hrest] at hz
    have heq : E j * ‖z + b j‖ ^ 2 + R - a = E j * (‖z + b j‖ ^ 2 - c) := by
      simp only [hc]
      field_simp
      ring
    rw [heq, abs_mul] at hz
    simp only [Set.mem_ofPred_eq]
    have h1 : |E j| * (t / 2 * |‖z + b j‖ ^ 2 - c|) ≤ |E j| * ‖z + b j‖ := by nlinarith
    exact le_of_mul_le_mul_left h1 hEa
  have hind : ∫⁻ z, Ev.indicator 1 (Function.update x j z) ∂cGauss =
      cGauss ((fun z => Function.update x j z) ⁻¹' Ev) := by
    rw [← lintegral_indicator_one (measurable_update x hm)]
    rfl
  rw [hind]
  refine (measure_mono hsub).trans ((h₃ (b j) c (t / 2) (by positivity)).trans (le_of_eq ?_))
  congr 1
  field_simp

/-! ### Splitting the weights into two comparable halves -/

/-- Nonnegative weights each at most half of the total split into a set `T` and its complement,
each carrying at least a quarter of the total. -/
private lemma quadRatio_exists_split {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hsp : ∀ k, w k ≤ (∑ i, w i) / 2) :
    ∃ T : Finset ι, ∑ i, w i ≤ 4 * ∑ k ∈ T, w k ∧ ∑ i, w i ≤ 4 * ∑ k ∈ Tᶜ, w k := by
  set V := ∑ i, w i with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun k _ => hw k
  have hne : ∀ V : ℝ, 0 ≤ V →
      ((Finset.univ : Finset (Finset ι)).filter fun T => ∑ k ∈ T, w k ≤ 3 * V / 4).Nonempty :=
    fun V hV => ⟨∅, by simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.sum_empty]; positivity⟩
  obtain ⟨T, hTmem, hTmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (Finset ι)).filter fun T => ∑ k ∈ T, w k ≤ 3 * V / 4)
    (fun T => ∑ k ∈ T, w k) (hne V hV0)
  rw [Finset.mem_filter] at hTmem
  have hc : ∑ k ∈ T, w k + ∑ k ∈ Tᶜ, w k = V := Finset.sum_add_sum_compl T w
  refine ⟨T, ?_, by linarith [hTmem.2]⟩
  by_contra hlt
  push Not at hlt
  have hT0 : 0 ≤ ∑ k ∈ T, w k := Finset.sum_nonneg fun k _ => hw k
  obtain ⟨k, hk, hwk⟩ : ∃ k ∈ Tᶜ, 0 < w k := by
    by_contra h
    push Not at h
    have : ∑ k ∈ Tᶜ, w k ≤ 0 := Finset.sum_nonpos h
    linarith
  have hkT : k ∉ T := Finset.mem_compl.mp hk
  have hins : insert k T ∈
      (Finset.univ : Finset (Finset ι)).filter fun T => ∑ k ∈ T, w k ≤ 3 * V / 4 := by
    rw [Finset.mem_filter, Finset.sum_insert hkT]
    exact ⟨Finset.mem_univ _, by linarith [hsp k]⟩
  have := hTmax _ hins
  rw [Finset.sum_insert hkT] at this
  linarith

/-! ### The diagonal case -/

/-- The diagonal form of the ratio bound: if some `E_j ≠ 0`, then
`P(t |∑ E_j |x_j + b_j|² - a| ≤ (∑ E_j² |x_j + b_j|²)^{1/2}) ≤ (2 C₃ + 8 C₇) / t`. -/
private lemma quadRatio_diag.{u} {ι : Type u} [Fintype ι] {C₃ C₇ : ℝ}
    (hC₃ : 0 < C₃) (hC₇ : 0 < C₇)
    (h₃ : ∀ (β : ℂ) (c t : ℝ), 0 < t →
      cGauss {z | t * |‖z + β‖ ^ 2 - c| ≤ ‖z + β‖} ≤ ENNReal.ofReal (C₃ / t))
    (h₇ : ∀ {κ : Type u} [Fintype κ] (E : κ → ℝ) (b : κ → ℂ) (a ε : ℝ), 0 < ε →
      (∃ j, E j ≠ 0) →
      stdCGauss κ {x | |∑ j, E j * ‖x j + b j‖ ^ 2 - a| ≤ ε} ≤
        ENNReal.ofReal (C₇ * ε / Real.sqrt (∑ k, E k ^ 2 * (1 + ‖b k‖ ^ 2))))
    (E : ι → ℝ) (hE : ∃ j, E j ≠ 0) (b : ι → ℂ) (a t : ℝ) (ht : 0 < t) :
    stdCGauss ι {z | t * |∑ j, E j * ‖z j + b j‖ ^ 2 - a| ≤
      Real.sqrt (∑ j, E j ^ 2 * ‖z j + b j‖ ^ 2)} ≤ ENNReal.ofReal ((2 * C₃ + 8 * C₇) / t) := by
  set w : ι → ℝ := fun k => E k ^ 2 * (1 + ‖b k‖ ^ 2) with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => by positivity
  obtain ⟨j₀, hj₀⟩ := hE
  have hν : 0 < ∑ k, w k := by
    have h1 : 0 < w j₀ := by simp only [hw]; positivity
    exact h1.trans_le (Finset.single_le_sum (fun k _ => hw0 k) (Finset.mem_univ j₀))
  set σ : Finset ι → (ι → ℂ) → ℝ := fun S z => ∑ j ∈ S, E j ^ 2 * ‖z j + b j‖ ^ 2 with hσ
  have hσ0 : ∀ S z, 0 ≤ σ S z := fun S z => Finset.sum_nonneg fun _ _ => by positivity
  have hσsplit : ∀ (S : Finset ι) z, ∑ j, E j ^ 2 * ‖z j + b j‖ ^ 2 = σ S z + σ Sᶜ z :=
    fun S z => (Finset.sum_add_sum_compl S _).symm
  have hsqrt : ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → Real.sqrt (p + q) ≤ Real.sqrt p + Real.sqrt q := by
    intro p q hp hq
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hp, Real.sq_sqrt hq, Real.sqrt_nonneg p, Real.sqrt_nonneg q]
  have hor : ∀ r u v : ℝ, r ≤ u + v → r ≤ 2 * u ∨ r ≤ 2 * v := by
    intro r u v h
    by_contra h'
    push Not at h'
    linarith [h'.1, h'.2]
  have hpos : 0 ≤ 2 * C₃ / t := by positivity
  have hpos' : 0 ≤ 4 * C₇ / t := by positivity
  by_cases hdom : ∃ j, (∑ k, w k) / 2 < w j
  · -- one dominant index
    obtain ⟨j, hj⟩ := hdom
    have hEj : E j ≠ 0 := by
      rintro h0
      have : w j = 0 := by simp [hw, h0]
      linarith
    have hsub : {z : ι → ℂ | t * |∑ j, E j * ‖z j + b j‖ ^ 2 - a| ≤
        Real.sqrt (∑ j, E j ^ 2 * ‖z j + b j‖ ^ 2)} ⊆
        {z | t * |∑ i, E i * ‖z i + b i‖ ^ 2 - a| ≤ 2 * (|E j| * ‖z j + b j‖)} ∪
        {z | t * |∑ i, E i * ‖z i + b i‖ ^ 2 - a| ≤
          2 * Real.sqrt (∑ i ∈ ({j} : Finset ι)ᶜ, E i ^ 2 * ‖z i + b i‖ ^ 2)} := by
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz
      rw [hσsplit {j} z] at hz
      have h1 : Real.sqrt (σ {j} z) = |E j| * ‖z j + b j‖ := by
        simp only [hσ, Finset.sum_singleton]
        rw [show E j ^ 2 * ‖z j + b j‖ ^ 2 = (|E j| * ‖z j + b j‖) ^ 2 by rw [mul_pow, sq_abs],
          Real.sqrt_sq (by positivity)]
      have h2 := hsqrt _ _ (hσ0 {j} z) (hσ0 {j}ᶜ z)
      rw [h1] at h2
      exact hor _ _ _ (hz.trans h2)
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have hT : ∑ k, w k ≤ 4 * ∑ k ∈ ({j} : Finset ι), w k := by
      rw [Finset.sum_singleton]
      linarith
    calc _ ≤ ENNReal.ofReal (2 * C₃ / t) + ENNReal.ofReal (4 * C₇ / t) :=
          add_le_add (quadRatio_single h₃ E b a t ht j hEj)
            (quadRatio_part hC₇ h₇ E b a t ht {j} hν hT)
      _ ≤ ENNReal.ofReal ((2 * C₃ + 8 * C₇) / t) := by
          rw [← ENNReal.ofReal_add hpos hpos']
          apply ENNReal.ofReal_le_ofReal
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by linarith) ht.le
  · -- the weight is spread: split it into two halves
    push Not at hdom
    obtain ⟨T, hT1, hT2⟩ := quadRatio_exists_split w hw0 hdom
    have hsub : {z : ι → ℂ | t * |∑ j, E j * ‖z j + b j‖ ^ 2 - a| ≤
        Real.sqrt (∑ j, E j ^ 2 * ‖z j + b j‖ ^ 2)} ⊆
        {z | t * |∑ i, E i * ‖z i + b i‖ ^ 2 - a| ≤
          2 * Real.sqrt (∑ i ∈ Tᶜᶜ, E i ^ 2 * ‖z i + b i‖ ^ 2)} ∪
        {z | t * |∑ i, E i * ‖z i + b i‖ ^ 2 - a| ≤
          2 * Real.sqrt (∑ i ∈ Tᶜ, E i ^ 2 * ‖z i + b i‖ ^ 2)} := by
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz
      rw [hσsplit T z] at hz
      simp only [Set.mem_union, Set.mem_ofPred_eq, compl_compl]
      exact hor _ _ _ (hz.trans (hsqrt _ _ (hσ0 T z) (hσ0 Tᶜ z)))
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    calc _ ≤ ENNReal.ofReal (4 * C₇ / t) + ENNReal.ofReal (4 * C₇ / t) :=
          add_le_add (quadRatio_part hC₇ h₇ E b a t ht Tᶜ hν hT2)
            (quadRatio_part hC₇ h₇ E b a t ht T hν hT1)
      _ ≤ ENNReal.ofReal ((2 * C₃ + 8 * C₇) / t) := by
          rw [← ENNReal.ofReal_add hpos' hpos']
          apply ENNReal.ofReal_le_ofReal
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by linarith) ht.le

/-! ### Diagonalization -/

/-- A unitary matrix preserves `∑ᵢ |yᵢ|²`. -/
private lemma quadRatio_sum_norm_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (y : ι → ℂ) :
    ∑ i, ‖((U : Matrix ι ι ℂ) *ᵥ y) i‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
  have hU : star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  have hdot : ∀ z : ι → ℂ, star z ⬝ᵥ z = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
    push_cast
    rfl
  have h : star ((U : Matrix ι ι ℂ) *ᵥ y) ⬝ᵥ ((U : Matrix ι ι ℂ) *ᵥ y) = star y ⬝ᵥ y := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, hU, Matrix.one_mulVec]
  rw [hdot, hdot] at h
  exact_mod_cast h

/-- `P(‖Q(γ + b)‖₂ ≥ t |(γ + b)* Q (γ + b) - a|) ≤ C / t` for every nonzero Hermitian `Q`,
`b ∈ ℂ^ι`, `a ∈ ℝ` and `t > 0`; the complex form of [APSSS, Lemma 2.1 (2.7)]. -/
theorem stdCGauss_quadForm_ratio_le : ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℂ), Q.IsHermitian → Q ≠ 0 →
      ∀ (b : ι → ℂ) (a t : ℝ), 0 < t →
        stdCGauss ι {x | t * ‖star (x + b) ⬝ᵥ (Q *ᵥ (x + b)) - a‖ ≤ l2Norm (Q *ᵥ (x + b))} ≤
          ENNReal.ofReal (C / t) := by
  obtain ⟨C₃, hC₃, h₃⟩ := cGauss_norm_ge_mul_abs_le
  obtain ⟨C₇, hC₇, h₇⟩ := stdCGauss_abs_quadSum_sub_le.{u_1}
  refine ⟨2 * C₃ + 8 * C₇, by positivity, ?_⟩
  intro ι _ _ Q hQ hQ0 b a t ht
  set U := hQ.eigenvectorUnitary with hUdef
  set E := hQ.eigenvalues with hEdef
  have hE : ∃ j, E j ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ0 (hQ.eigenvalues_eq_zero_iff.mp (funext h))
  set D : Matrix ι ι ℂ := Matrix.diagonal fun j => (E j : ℂ) with hD
  have hQU : Q = (U : Matrix ι ι ℂ) * D * star (U : Matrix ι ι ℂ) := by
    conv_lhs => rw [hQ.spectral_theorem]
    rfl
  set Us : Matrix.unitaryGroup ι ℂ := star U with hUs
  have hUs' : (Us : Matrix ι ι ℂ) = star (U : Matrix ι ι ℂ) := rfl
  have hmp := measurePreserving_stdCGauss_unitary Us
  set b' := star (U : Matrix ι ι ℂ) *ᵥ b with hb'
  set S' := {y : ι → ℂ | t * |∑ j, E j * ‖y j + b' j‖ ^ 2 - a| ≤
    Real.sqrt (∑ j, E j ^ 2 * ‖y j + b' j‖ ^ 2)} with hS'
  have hS'm : MeasurableSet S' := measurableSet_le (by fun_prop) (by fun_prop)
  have hset : {x | t * ‖star (x + b) ⬝ᵥ (Q *ᵥ (x + b)) - a‖ ≤ l2Norm (Q *ᵥ (x + b))} =
      (fun x => (Us : Matrix ι ι ℂ) *ᵥ x) ⁻¹' S' := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hS']
    set y := star (U : Matrix ι ι ℂ) *ᵥ (x + b) with hy
    have hy' : ∀ j, ((Us : Matrix ι ι ℂ) *ᵥ x) j + b' j = y j := by
      intro j
      rw [hy, Matrix.mulVec_add, hUs', Pi.add_apply]
    have hQv : Q *ᵥ (x + b) = (U : Matrix ι ι ℂ) *ᵥ (D *ᵥ y) := by
      rw [hQU, hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have key1 : star (x + b) ⬝ᵥ (Q *ᵥ (x + b)) = ((∑ j, E j * ‖y j‖ ^ 2 : ℝ) : ℂ) := by
      rw [hQv, Matrix.dotProduct_mulVec]
      have : star (x + b) ᵥ* (U : Matrix ι ι ℂ) = star y := by
        rw [hy, Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_conjTranspose]
      rw [this]
      simp only [dotProduct, Matrix.mulVec_diagonal, hD, Pi.star_apply, RCLike.star_def]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, Complex.conj_mul']
    have key2 : l2Norm (Q *ᵥ (x + b)) = Real.sqrt (∑ j, E j ^ 2 * ‖y j‖ ^ 2) := by
      rw [hQv, l2Norm, quadRatio_sum_norm_mulVec U]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [key1, key2]
    simp only [hy']
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hset, hmp.measure_preimage hS'm.nullMeasurableSet]
  exact quadRatio_diag hC₃ hC₇ h₃ h₇ E hE b' a t ht

end LSBA
