import LSBA.Spectral.RankOne

/-!
# The finite-matrix spectral-averaging bound for the eigenfunction correlator

[ASFH, proof of Theorem A.1] with `s = δ = u` and `α = u/2`, for the family `K + v e_x e_x^*`
with `v` of law `ν`: if `ν` has density at most `κ`, `∫ |v|^u dν ≤ M`, the family has simple
spectrum for `ν`-a.e. `v`, and the spectral averaging inequality
`∫ Σ_k |ψ_k(x)|² φ(λ_k) dv ≤ ∫ φ` holds, then
`𝔼 Q_{xy}(J) ≤ (2 M κ ∫_J 𝔼|G_{xy}(E)|^u dE)^{1/(4-u)}`. This is the spectral
averaging of [ASFH, Appendix A, proof of Theorem A.1, (A.10)–(A.12)], which the proof of Lemma
8.1(i)
[uva:thm:upper-audit] applies to reach (E.1) [up:eq:correlator-intro], before the model (1.3)
[eq:model] is inserted.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- `v ↦ K + v e_x e_x^*` is continuous. -/
private lemma corrAverage_continuous_rankOnePert (K : Matrix n n ℂ) (x : n) :
    Continuous fun v : ℝ => rankOnePert K x v := by
  unfold rankOnePert
  refine continuous_const.add (continuous_matrix fun i j => ?_)
  simp only [Matrix.single_apply]
  split_ifs
  · exact Complex.continuous_ofReal
  · exact continuous_const

/-- `(v, E) ↦ G_{xy}(E)` for the matrix `K + v e_x e_x^*` is measurable (with the total inverse,
`0` on the spectrum). -/
private lemma corrAverage_measurable_resolventMat (K : Matrix n n ℂ) (x y : n) :
    Measurable fun p : ℝ × ℝ => resolventMat (rankOnePert K x p.1) (p.2 : ℂ) x y := by
  have hA : Continuous fun p : ℝ × ℝ =>
      rankOnePert K x p.1 - (p.2 : ℂ) • (1 : Matrix n n ℂ) :=
    ((corrAverage_continuous_rankOnePert K x).comp continuous_fst).sub
      ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_const)
  have h : (fun p : ℝ × ℝ => resolventMat (rankOnePert K x p.1) (p.2 : ℂ) x y) =
      fun p => ((rankOnePert K x p.1 - (p.2 : ℂ) • (1 : Matrix n n ℂ)).det)⁻¹ *
        (rankOnePert K x p.1 - (p.2 : ℂ) • (1 : Matrix n n ℂ)).adjugate x y := by
    funext p
    rw [resolventMat, Matrix.inv_def, Ring.inverse_eq_inv']
    rfl
  rw [h]
  exact (measurable_inv.comp hA.matrix_det.measurable).mul
    (hA.matrix_adjugate.matrix_elem x y).measurable

/-- For every exponent `s`, `((v, v'), E) ↦ 1_J(E) |G'_{xy}(E)|^s` is measurable, where `G'` is
the resolvent of `K + v' e_x e_x^*`. -/
private lemma corrAverage_measurable_indicator (K : Matrix n n ℂ) (x y : n) {J : Set ℝ}
    (hJ : MeasurableSet J) (s : ℝ) :
    Measurable (Function.uncurry fun (p : ℝ × ℝ) (E : ℝ) =>
      J.indicator (fun E => ‖resolventMat (rankOnePert K x p.2) E x y‖ₑ ^ s) E) := by
  have hR := corrAverage_measurable_resolventMat K x y
  have hm : Measurable fun q : (ℝ × ℝ) × ℝ =>
      ‖resolventMat (rankOnePert K x q.1.2) (q.2 : ℂ) x y‖ₑ ^ s :=
    ((hR.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).enorm).pow_const s
  have he : (Function.uncurry fun (p : ℝ × ℝ) (E : ℝ) =>
      J.indicator (fun E => ‖resolventMat (rankOnePert K x p.2) E x y‖ₑ ^ s) E) =
      (Prod.snd ⁻¹' J).indicator fun q : (ℝ × ℝ) × ℝ =>
        ‖resolventMat (rankOnePert K x q.1.2) (q.2 : ℂ) x y‖ₑ ^ s := by
    funext q
    simp only [Function.uncurry, Set.indicator_apply, Set.mem_preimage]
  rw [he]
  exact hm.indicator (hJ.preimage measurable_snd)

/-- Jensen's inequality for the concave power `t ↦ t^θ`, `0 < θ < 1`, under a probability
measure, from Hölder's inequality with the second factor `1`. -/
private lemma corrAverage_lintegral_rpow_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {f : X → ℝ≥0∞} (hf : AEMeasurable f μ) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) : ∫⁻ a, f a ^ θ ∂μ ≤ (∫⁻ a, f a ∂μ) ^ θ := by
  have hp : 1 < 1 / θ := by rw [lt_div_iff₀ hθ0]; linarith
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (f := fun a => f a ^ θ)
    (g := fun _ => 1) (hf.pow_const θ) aemeasurable_const
  have h1 : ∀ a, (f a ^ θ) ^ (1 / θ) = f a := fun a => by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hθ0.ne', ENNReal.rpow_one]
  simp only [Pi.mul_apply, mul_one, h1, ENNReal.one_rpow, lintegral_const, measure_univ,
    one_div_one_div] at h
  simpa using h

/-- `ν` has no atoms when `ν ≤ c • Leb`. -/
private lemma corrAverage_measure_singleton {ν : Measure ℝ} {κ : ℝ}
    (hκ : ν ≤ ENNReal.ofReal κ • (volume : Measure ℝ)) (a : ℝ) : ν {a} = 0 := by
  have h := Measure.le_iff'.1 hκ {a}
  rw [Measure.smul_apply, Real.volume_singleton, smul_eq_mul, mul_zero] at h
  exact nonpos_iff_eq_zero.1 h

/-- A probability measure with `ν ≤ ofReal κ • Leb` forces `0 ≤ κ`. -/
private lemma corrAverage_nonneg {ν : Measure ℝ} [IsProbabilityMeasure ν] {κ : ℝ}
    (hκ : ν ≤ ENNReal.ofReal κ • (volume : Measure ℝ)) : 0 ≤ κ := by
  by_contra h
  have h0 : ENNReal.ofReal κ = 0 := ENNReal.ofReal_of_nonpos (le_of_not_ge h)
  have h1 := Measure.le_iff'.1 hκ Set.univ
  rw [h0, zero_smul, Measure.coe_zero, Pi.zero_apply, measure_univ] at h1
  exact one_ne_zero (nonpos_iff_eq_zero.1 h1)

/-- The factor `2 𝔼|v|^u` of [ASFH, proof of Theorem A.1]: for `0 < u ≤ 1`,
`∫∫ |v - v'|^u dν(v) dν(v') ≤ 2 ∫ |v|^u dν`. -/
private lemma corrAverage_lintegral_enorm_sub_rpow_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ∫⁻ p, ‖p.1 - p.2‖ₑ ^ u ∂(ν.prod ν) ≤ 2 * ∫⁻ v, ‖v‖ₑ ^ u ∂ν := by
  have hg : Measurable fun v : ℝ => ‖v‖ₑ ^ u := measurable_id.enorm.pow_const u
  have hg1 : Measurable fun p : ℝ × ℝ => ‖p.1‖ₑ ^ u := hg.comp measurable_fst
  have hg2 : Measurable fun p : ℝ × ℝ => ‖p.2‖ₑ ^ u := hg.comp measurable_snd
  calc ∫⁻ p, ‖p.1 - p.2‖ₑ ^ u ∂(ν.prod ν)
      ≤ ∫⁻ p, (‖p.1‖ₑ ^ u + ‖p.2‖ₑ ^ u) ∂(ν.prod ν) := by
        refine lintegral_mono fun p => ?_
        calc ‖p.1 - p.2‖ₑ ^ u ≤ (‖p.1‖ₑ + ‖p.2‖ₑ) ^ u :=
              ENNReal.rpow_le_rpow (enorm_sub_le) hu0.le
          _ ≤ _ := ENNReal.rpow_add_le_add_rpow _ _ hu0.le hu1
    _ = ∫⁻ v, ‖v‖ₑ ^ u ∂ν + ∫⁻ v, ‖v‖ₑ ^ u ∂ν := by
        rw [lintegral_add_left hg1, lintegral_prod _ hg1.aemeasurable,
          lintegral_prod _ hg2.aemeasurable]
        simp [lintegral_const]
    _ = 2 * ∫⁻ v, ‖v‖ₑ ^ u ∂ν := (two_mul _).symm

/-- [ASFH, proof of Theorem A.1] for one resampled diagonal entry: the two Hölder steps, Jensen,
the factor `2 𝔼|v|^u` and the density bound give
`𝔼 Q_{xy}(J) ≤ (2 M κ ∫_J 𝔼|G_{xy}(E)|^u dE)^{1/(4-u)}`. -/
theorem lintegral_eigCorr_rankOnePert_le {K : Matrix n n ℂ} (hK : K.IsHermitian) (x y : n)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {u κ M : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hκ : ν ≤ ENNReal.ofReal κ • (volume : Measure ℝ))
    (hM : ∫⁻ v, ‖v‖ₑ ^ u ∂ν ≤ ENNReal.ofReal M)
    (hsimple : ∀ᵐ v ∂ν, Function.Injective (rankOnePert_isHermitian hK x v).eigenvalues)
    (hSA : ∀ φ : ℝ → ℝ≥0∞, Measurable φ →
      ∫⁻ v, eigMassSum (rankOnePert K x v) {x} φ ≤ ∫⁻ E, φ E)
    {J : Set ℝ} (hJ : MeasurableSet J) :
    ∫⁻ v, ENNReal.ofReal (eigCorr (rankOnePert K x v) J x y) ∂ν ≤
      (ENNReal.ofReal (2 * M * κ) *
        ∫⁻ E in J, ∫⁻ v, ‖resolventMat (rankOnePert K x v) E x y‖ₑ ^ u ∂ν) ^ (1 / (4 - u)) := by
  have hα0 : 0 < u / 2 := by positivity
  have hα1 : u / 2 ≤ 1 := by linarith
  have hθ0 : 0 < 1 / (2 - u / 2) := by
    have : 0 < 2 - u / 2 := by linarith
    positivity
  have hθ1 : 1 / (2 - u / 2) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hκ0 : 0 ≤ κ := corrAverage_nonneg hκ
  have hR := corrAverage_measurable_resolventMat K x y
  have hH : Measurable fun p : ℝ × ℝ => rankOnePert K x p.1 :=
    ((corrAverage_continuous_rankOnePert K x).comp continuous_fst).measurable
  -- `Z(v, v') = Σ_{λ_k ∈ J} |ψ_k(x)|² |G'_{xy}(λ_k)|^{u/2}` and `D(v, v') = |v - v'|^{u/2}`
  have hZ : Measurable fun p : ℝ × ℝ => eigMassSum (rankOnePert K x p.1) {x}
      (J.indicator fun E => ‖resolventMat (rankOnePert K x p.2) E x y‖ₑ ^ (u / 2)) :=
    measurable_eigMassSum hH {x} (corrAverage_measurable_indicator K x y hJ (u / 2))
  have hD : Measurable fun p : ℝ × ℝ => ‖p.1 - p.2‖ₑ ^ (u / 2) :=
    (measurable_fst.sub measurable_snd).enorm.pow_const _
  have hF : Measurable fun p : ℝ × ℝ => ‖p.1 - p.2‖ₑ ^ (u / 2) *
      eigMassSum (rankOnePert K x p.1) {x}
        (J.indicator fun E => ‖resolventMat (rankOnePert K x p.2) E x y‖ₑ ^ (u / 2)) :=
    hD.mul hZ
  -- the first Hölder step, pointwise off the null diagonal
  have h1 : ∫⁻ v, ENNReal.ofReal (eigCorr (rankOnePert K x v) J x y) ∂ν ≤
      ∫⁻ p, (‖p.1 - p.2‖ₑ ^ (u / 2) * eigMassSum (rankOnePert K x p.1) {x}
        (J.indicator fun E => ‖resolventMat (rankOnePert K x p.2) E x y‖ₑ ^ (u / 2))) ^
          (1 / (2 - u / 2)) ∂(ν.prod ν) := by
    rw [lintegral_prod _ (hF.pow_const _).aemeasurable]
    refine lintegral_mono_ae (hsimple.mono fun v hv => ?_)
    have hne : ∀ᵐ v' ∂ν, v ≠ v' := by
      rw [ae_iff]
      have : {v' : ℝ | ¬ v ≠ v'} = {v} := by
        ext v'
        simp [eq_comm]
      rw [this]
      exact corrAverage_measure_singleton hκ v
    calc ENNReal.ofReal (eigCorr (rankOnePert K x v) J x y)
        = ∫⁻ _, ENNReal.ofReal (eigCorr (rankOnePert K x v) J x y) ∂ν := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := lintegral_mono_ae (hne.mono fun v' hvv =>
          eigCorr_rankOnePert_le hK x y hvv hv J hα0 hα1)
  -- Jensen in `(v, v')`
  have h2 := corrAverage_lintegral_rpow_le (ν.prod ν) hF.aemeasurable hθ0 hθ1
  -- the second Hölder step (Cauchy–Schwarz)
  have h3 := ENNReal.lintegral_mul_le_Lp_mul_Lq (ν.prod ν) Real.HolderConjugate.two_two
    hD.aemeasurable hZ.aemeasurable
  -- the factor `2 𝔼|v|^u`
  have h4 : ∫⁻ p, (‖p.1 - p.2‖ₑ ^ (u / 2)) ^ (2 : ℝ) ∂(ν.prod ν) ≤ 2 * ENNReal.ofReal M := by
    have he : ∀ p : ℝ × ℝ, (‖p.1 - p.2‖ₑ ^ (u / 2)) ^ (2 : ℝ) = ‖p.1 - p.2‖ₑ ^ u := fun p => by
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    simp_rw [he]
    exact (corrAverage_lintegral_enorm_sub_rpow_le hu0 hu1).trans (by gcongr)
  -- Jensen over `k`, the density bound, the spectral averaging inequality, and Tonelli
  have h5 : ∫⁻ p, (eigMassSum (rankOnePert K x p.1) {x}
      (J.indicator fun E => ‖resolventMat (rankOnePert K x p.2) E x y‖ₑ ^ (u / 2))) ^ (2 : ℝ)
        ∂(ν.prod ν) ≤
      ENNReal.ofReal κ * ∫⁻ E in J, ∫⁻ v, ‖resolventMat (rankOnePert K x v) E x y‖ₑ ^ u ∂ν := by
    have hsq : ∀ p : ℝ × ℝ, (eigMassSum (rankOnePert K x p.1) {x}
        (J.indicator fun E => ‖resolventMat (rankOnePert K x p.2) E x y‖ₑ ^ (u / 2))) ^ (2 : ℝ) ≤
        eigMassSum (rankOnePert K x p.1) {x}
          (J.indicator fun E => ‖resolventMat (rankOnePert K x p.2) E x y‖ₑ ^ u) := fun p => by
      rw [ENNReal.rpow_two]
      refine (eigMassSum_singleton_sq_le _ x _).trans (le_of_eq ?_)
      congr 1
      funext E
      by_cases hE : E ∈ J
      · simp only [Set.indicator_of_mem hE]
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
        push_cast
        ring
      · simp [Set.indicator_of_notMem hE]
    have hZu : Measurable fun p : ℝ × ℝ => eigMassSum (rankOnePert K x p.1) {x}
        (J.indicator fun E => ‖resolventMat (rankOnePert K x p.2) E x y‖ₑ ^ u) :=
      measurable_eigMassSum hH {x} (corrAverage_measurable_indicator K x y hJ u)
    have hdens : ∀ v' : ℝ, ∫⁻ v, eigMassSum (rankOnePert K x v) {x}
        (J.indicator fun E => ‖resolventMat (rankOnePert K x v') E x y‖ₑ ^ u) ∂ν ≤
        ENNReal.ofReal κ * ∫⁻ E in J, ‖resolventMat (rankOnePert K x v') E x y‖ₑ ^ u := by
      intro v'
      have hφ : Measurable (J.indicator fun E : ℝ =>
          ‖resolventMat (rankOnePert K x v') E x y‖ₑ ^ u) :=
        ((hR.comp (measurable_const.prodMk measurable_id)).enorm.pow_const u).indicator hJ
      calc _ ≤ ∫⁻ v, eigMassSum (rankOnePert K x v) {x}
            (J.indicator fun E => ‖resolventMat (rankOnePert K x v') E x y‖ₑ ^ u)
              ∂(ENNReal.ofReal κ • (volume : Measure ℝ)) := lintegral_mono' hκ le_rfl
        _ = ENNReal.ofReal κ * ∫⁻ v, eigMassSum (rankOnePert K x v) {x}
            (J.indicator fun E => ‖resolventMat (rankOnePert K x v') E x y‖ₑ ^ u) := by
          rw [lintegral_smul_measure, smul_eq_mul]
        _ ≤ ENNReal.ofReal κ * ∫⁻ E, J.indicator (fun E =>
            ‖resolventMat (rankOnePert K x v') E x y‖ₑ ^ u) E := by
          exact mul_le_mul' le_rfl (hSA _ hφ)
        _ = _ := by rw [lintegral_indicator hJ]
    have hG : Measurable fun p : ℝ × ℝ =>
        ‖resolventMat (rankOnePert K x p.1) (p.2 : ℂ) x y‖ₑ ^ u :=
      hR.enorm.pow_const u
    calc _ ≤ ∫⁻ p, eigMassSum (rankOnePert K x p.1) {x}
          (J.indicator fun E => ‖resolventMat (rankOnePert K x p.2) E x y‖ₑ ^ u) ∂(ν.prod ν) :=
          lintegral_mono hsq
      _ = ∫⁻ v', ∫⁻ v, eigMassSum (rankOnePert K x v) {x}
          (J.indicator fun E => ‖resolventMat (rankOnePert K x v') E x y‖ₑ ^ u) ∂ν ∂ν :=
          lintegral_prod_symm _ hZu.aemeasurable
      _ ≤ ∫⁻ v', ENNReal.ofReal κ *
          (∫⁻ E in J, ‖resolventMat (rankOnePert K x v') E x y‖ₑ ^ u) ∂ν :=
          lintegral_mono hdens
      _ = ENNReal.ofReal κ *
          ∫⁻ v', (∫⁻ E in J, ‖resolventMat (rankOnePert K x v') E x y‖ₑ ^ u) ∂ν :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = _ := by
          rw [lintegral_lintegral_swap (f := fun (v' E : ℝ) =>
            ‖resolventMat (rankOnePert K x v') E x y‖ₑ ^ u) hG.aemeasurable]
  -- the close
  have hc : ENNReal.ofReal (2 * M * κ) = 2 * ENNReal.ofReal M * ENNReal.ofReal κ := by
    rw [ENNReal.ofReal_mul' hκ0, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hexp : (1 / 2 : ℝ) * (1 / (2 - u / 2)) = 1 / (4 - u) := by
    rw [one_div_mul_one_div]
    congr 1
    ring
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ ((∫⁻ p, (‖p.1 - p.2‖ₑ ^ (u / 2)) ^ (2 : ℝ) ∂(ν.prod ν)) ^ (1 / 2 : ℝ) *
          (∫⁻ p, (eigMassSum (rankOnePert K x p.1) {x}
            (J.indicator fun E => ‖resolventMat (rankOnePert K x p.2) E x y‖ₑ ^ (u / 2))) ^
              (2 : ℝ) ∂(ν.prod ν)) ^ (1 / 2 : ℝ)) ^ (1 / (2 - u / 2)) :=
        ENNReal.rpow_le_rpow h3 hθ0.le
    _ ≤ ((2 * ENNReal.ofReal M) ^ (1 / 2 : ℝ) * (ENNReal.ofReal κ *
          ∫⁻ E in J, ∫⁻ v, ‖resolventMat (rankOnePert K x v) E x y‖ₑ ^ u ∂ν) ^ (1 / 2 : ℝ)) ^
            (1 / (2 - u / 2)) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, hexp, hc]
        congr 1
        ring

end LSBA
