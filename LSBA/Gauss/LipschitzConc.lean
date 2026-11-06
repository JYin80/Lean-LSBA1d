import LSBA.Gauss.Concentration
import LSBA.Analysis.Mollify

/-!
# Gaussian concentration for Lipschitz functions

The two-sided Gaussian concentration bound `P(|f - 𝔼f| > u) ≤ 2 exp(-2u²/(π²K²))` of
`concentration_real` (stated there for `C¹` functions), for every `K`-Lipschitz `f` on `ℝ^ι`
(Euclidean norm, standard Gaussian law), and the variance bound `Var f ≤ π² K²`. These give
(G.11) [cg:eq:SG] and the norm tails in Appendix G.4 [app:compact-gaussian].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

namespace LSBA

/-! ### Integrability of Euclidean-Lipschitz functions -/

/-- `exp (c |t|)` is integrable against the standard Gaussian on `ℝ`. -/
private lemma lipschitzConc_integrable_exp_abs (c : ℝ) :
    Integrable (fun t : ℝ => Real.exp (c * |t|)) (gaussianReal 0 1) := by
  have h := (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) c).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-c))
  refine h.mono' (by fun_prop : Continuous fun t : ℝ => Real.exp (c * |t|)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  change _ ≤ Real.exp (c * t) + Real.exp (-c * t)
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]; linarith [Real.exp_pos (-c * t)]
  · rw [abs_of_nonpos ht, show c * -t = -c * t by ring]; linarith [Real.exp_pos (c * t)]

/-- `exp (∑ᵢ |xᵢ|)` is integrable against the standard Gaussian on `ℝ^ι`. -/
private lemma lipschitzConc_integrable_exp_sum {ι : Type*} [Fintype ι] :
    Integrable (fun x : ι → ℝ => Real.exp (∑ i, |x i|)) (stdGauss ι) := by
  have hprod : (fun x : ι → ℝ => Real.exp (∑ i, |x i|)) =
      fun x => ∏ i, Real.exp (1 * |x i|) := by
    funext x
    rw [Real.exp_sum]
    simp
  rw [hprod]
  exact Integrable.fintype_prod (f := fun _ (t : ℝ) => Real.exp (1 * |t|))
    (fun _ => lipschitzConc_integrable_exp_abs 1)

/-- The Euclidean norm is at most `√|ι|` times the sup norm. -/
private lemma lipschitzConc_toLp_norm_le {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ ≤ Real.sqrt (Fintype.card ι) * ‖v‖ := by
  rw [EuclideanSpace.norm_eq]
  have h : ∑ i, ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι) i‖ ^ 2 ≤ (Fintype.card ι) * ‖v‖ ^ 2 := by
    calc ∑ i, ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι) i‖ ^ 2 ≤ ∑ _i : ι, ‖v‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
      _ = (Fintype.card ι) * ‖v‖ ^ 2 := by simp
  calc Real.sqrt (∑ i, ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι) i‖ ^ 2)
      ≤ Real.sqrt ((Fintype.card ι) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (Fintype.card ι) * ‖v‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The sup norm is at most `∑ᵢ |xᵢ|`. -/
private lemma lipschitzConc_norm_le_sum {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ‖x‖ ≤ ∑ i, |x i| := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun i => |x i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)

/-- Affine functions of the sup norm are integrable under `stdGauss ι`. -/
private lemma lipschitzConc_integrable_affine {ι : Type*} [Fintype ι] (A B : ℝ) :
    Integrable (fun x : ι → ℝ => A + B * ‖x‖) (stdGauss ι) := by
  refine (integrable_const A).add (Integrable.const_mul ?_ B)
  refine (lipschitzConc_integrable_exp_sum (ι := ι)).mono'
    continuous_norm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_norm]
  have h1 := lipschitzConc_norm_le_sum x
  linarith [Real.add_one_le_exp (∑ i, |x i|)]

/-- A function that is Lipschitz for the Euclidean norm is continuous and integrable against
`stdGauss ι`. -/
private lemma lipschitzConc_continuous_integrable {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ)
    (K : ℝ≥0) (hf : LipschitzWith K (fun x : EuclideanSpace ℝ ι => f x.ofLp)) :
    Continuous f ∧ Integrable f (stdGauss ι) := by
  have hc : Continuous f := by
    have := hf.continuous.comp (PiLp.continuous_toLp 2 (fun _ : ι => ℝ))
    exact this
  refine ⟨hc, ?_⟩
  refine (lipschitzConc_integrable_affine |f 0| (K * Real.sqrt (Fintype.card ι))).mono'
    hc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have h : |f x - f 0| ≤ (K : ℝ) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ := by
    have := hf.dist_le_mul (WithLp.toLp 2 x) 0
    simpa [Real.dist_eq, dist_eq_norm] using this
  have h3 := lipschitzConc_toLp_norm_le x
  have h4 : (K : ℝ) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ≤
      K * (Real.sqrt (Fintype.card ι) * ‖x‖) := by gcongr
  calc ‖f x‖ = |f x| := Real.norm_eq_abs _
    _ ≤ |f 0| + |f x - f 0| := by
        calc |f x| = |f 0 + (f x - f 0)| := by rw [add_sub_cancel]
          _ ≤ |f 0| + |f x - f 0| := abs_add_le _ _
    _ ≤ |f 0| + (K : ℝ) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ := by linarith
    _ ≤ |f 0| + K * (Real.sqrt (Fintype.card ι) * ‖x‖) := by linarith
    _ = |f 0| + (K * Real.sqrt (Fintype.card ι)) * ‖x‖ := by ring

/-! ### Mollification at a fixed radius -/

/-- For a `K`-Lipschitz `f` and `r > 0` with `2 K r ≤ u`, the tail `P(|f - 𝔼f| > u)` is at most
the `C¹` concentration bound at level `u - 2 K r` (mollification of `f` at radius `r`). -/
private lemma lipschitzConc_tail_mollified {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K (fun x : EuclideanSpace ℝ ι => f x.ofLp)) {u r : ℝ} (hr : 0 < r)
    (hur : 2 * K * r ≤ u) :
    stdGauss ι {x | u < |f x - ∫ y, f y ∂(stdGauss ι)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 * (u - 2 * K * r) ^ 2) / (π ^ 2 * (K : ℝ) ^ 2))) := by
  obtain ⟨g, hgd, hgL, hgle, hgge⟩ := exists_contDiff_lipschitz_near hf hr
  set fr : (ι → ℝ) → ℝ := fun x => g (WithLp.toLp 2 x) with hfr
  have hfrL : LipschitzWith K (fun x : EuclideanSpace ℝ ι => fr x.ofLp) := by
    have : (fun x : EuclideanSpace ℝ ι => fr x.ofLp) = g := by
      funext x; rfl
    rw [this]; exact hgL
  have hfr1 : ContDiff ℝ 1 fr := by
    have h1 : ContDiff ℝ 1 g := hgd.of_le (by exact_mod_cast le_top)
    exact h1.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.contDiff
  obtain ⟨hfc, hfi⟩ := lipschitzConc_continuous_integrable f K hf
  obtain ⟨hfrc, hfri⟩ := lipschitzConc_continuous_integrable fr K hfrL
  -- pointwise closeness
  have hclose : ∀ x, |fr x - f x| ≤ K * r := by
    intro x
    obtain ⟨y, hy, hyle⟩ := hgle (WithLp.toLp 2 x)
    obtain ⟨y', hy', hy'ge⟩ := hgge (WithLp.toLp 2 x)
    have h1 := hf.dist_le_mul y (WithLp.toLp 2 x)
    have h2 := hf.dist_le_mul y' (WithLp.toLp 2 x)
    rw [Real.dist_eq, abs_le] at h1 h2
    have h3 : (K : ℝ) * dist y (WithLp.toLp 2 x) ≤ K * r := by gcongr
    have h4 : (K : ℝ) * dist y' (WithLp.toLp 2 x) ≤ K * r := by gcongr
    have e : f x = (fun z : EuclideanSpace ℝ ι => f z.ofLp) (WithLp.toLp 2 x) := rfl
    rw [abs_le]
    constructor
    · change -(K * r) ≤ g (WithLp.toLp 2 x) - f x
      rw [e]; linarith [h2.1, h2.2]
    · change g (WithLp.toLp 2 x) - f x ≤ K * r
      rw [e]; linarith [h1.1, h1.2]
  -- the means are close
  have hmean : |∫ y, fr y ∂(stdGauss ι) - ∫ y, f y ∂(stdGauss ι)| ≤ K * r := by
    rw [← integral_sub hfri hfi]
    have := norm_integral_le_of_norm_le_const (μ := stdGauss ι)
      (f := fun y => fr y - f y) (C := K * r)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hclose x)
    simpa using this
  set m := ∫ y, f y ∂(stdGauss ι) with hm
  set mr := ∫ y, fr y ∂(stdGauss ι) with hmr
  have hsub : {x | u < |f x - m|} ⊆ {x | u - 2 * K * r < |fr x - mr|} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have h1 := hclose x
    have h2 : |f x - m| ≤ |fr x - mr| + 2 * (K * r) := by
      calc |f x - m| = |(fr x - mr) - (fr x - f x) + (mr - m)| := by ring_nf
        _ ≤ |(fr x - mr) - (fr x - f x)| + |mr - m| := abs_add_le _ _
        _ ≤ |fr x - mr| + |fr x - f x| + |mr - m| := by
            gcongr; exact abs_sub _ _
        _ ≤ |fr x - mr| + 2 * (K * r) := by linarith
    linarith
  have hu' : 0 ≤ u - 2 * K * r := by linarith
  have := concentration_real fr hfr1 K hfrL (u - 2 * K * r) hu'
  exact (measure_mono hsub).trans this

/-- Gaussian concentration for a `K`-Lipschitz function on `ℝ^ι` with the Euclidean norm:
`P(|f - 𝔼f| > u) ≤ 2 exp(-2u²/(π²K²))`. -/
theorem concentration_lipschitz {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K (fun x : EuclideanSpace ℝ ι => f x.ofLp)) (u : ℝ) (hu : 0 ≤ u) :
    stdGauss ι {x | u < |f x - ∫ y, f y ∂(stdGauss ι)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 * u ^ 2) / (π ^ 2 * (K : ℝ) ^ 2))) := by
  by_cases hdeg : (K : ℝ) = 0 ∨ u = 0
  · have h2 : (2 : ℝ) * Real.exp (-(2 * u ^ 2) / (π ^ 2 * (K : ℝ) ^ 2)) = 2 := by
      rcases hdeg with h | h <;> simp [h]
    rw [h2]
    exact prob_le_one.trans (by simp)
  · push Not at hdeg
    obtain ⟨hK0, hu0⟩ := hdeg
    have hK : 0 < (K : ℝ) := lt_of_le_of_ne K.coe_nonneg (Ne.symm hK0)
    have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    set G : ℝ → ℝ≥0∞ := fun r =>
      ENNReal.ofReal (2 * Real.exp (-(2 * (u - 2 * K * r) ^ 2) / (π ^ 2 * (K : ℝ) ^ 2))) with hG
    have hGc : Continuous G := by
      refine ENNReal.continuous_ofReal.comp ?_
      fun_prop
    have hG0 : G 0 =
        ENNReal.ofReal (2 * Real.exp (-(2 * u ^ 2) / (π ^ 2 * (K : ℝ) ^ 2))) := by
      simp [hG]
    have hlim : Filter.Tendsto G (nhdsWithin 0 (Set.Ioi 0)) (nhds (G 0)) :=
      (hGc.tendsto 0).mono_left nhdsWithin_le_nhds
    rw [← hG0]
    refine ge_of_tendsto hlim ?_
    have hmem : Set.Ioo (0 : ℝ) (u / (2 * K)) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      Ioo_mem_nhdsGT (div_pos hu' (by positivity))
    filter_upwards [hmem] with r hr
    have hr2 : 2 * (K : ℝ) * r ≤ u := by
      have := hr.2.le
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    exact lipschitzConc_tail_mollified f K hf hr.1 hr2

/-- Variance of a `K`-Lipschitz function on `ℝ^ι` under the standard Gaussian law:
`𝔼(f - 𝔼f)² ≤ π² K²`. -/
theorem variance_le_of_lipschitz {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K (fun x : EuclideanSpace ℝ ι => f x.ofLp)) :
    ∫ x, (f x - ∫ y, f y ∂(stdGauss ι)) ^ 2 ∂(stdGauss ι) ≤ π ^ 2 * (K : ℝ) ^ 2 := by
  obtain ⟨hfc, hfi⟩ := lipschitzConc_continuous_integrable f K hf
  set m := ∫ y, f y ∂(stdGauss ι) with hm
  rcases eq_or_lt_of_le K.coe_nonneg with hK | hK
  · have hconst : ∀ x, f x = f 0 := by
      intro x
      have h := hf.dist_le_mul (WithLp.toLp 2 x) 0
      rw [← hK] at h
      have h' : |f x - f 0| ≤ 0 := by simpa [Real.dist_eq] using h
      exact sub_eq_zero.mp (abs_nonpos_iff.mp h')
    have hm0 : m = f 0 := by
      rw [hm]
      simp [hconst]
    have : ∀ x, (f x - m) ^ 2 = 0 := fun x => by rw [hm0, hconst x]; simp
    simp only [this, integral_zero]
    rw [← hK]
    simp
  · set X : (ι → ℝ) → ℝ := fun x => |f x - m| with hX
    have hXc : Continuous X := (hfc.sub continuous_const).abs
    have hnn : 0 ≤ᵐ[stdGauss ι] X := Filter.Eventually.of_forall fun x => abs_nonneg _
    have hlay := lintegral_rpow_eq_lintegral_meas_lt_mul (stdGauss ι) hnn hXc.aemeasurable
      (p := 2) two_pos
    set b : ℝ := 2 / (π ^ 2 * (K : ℝ) ^ 2) with hb
    have hbpos : 0 < b := by positivity
    have hbound : ∫⁻ t in Set.Ioi (0 : ℝ), stdGauss ι {a | t < X a} *
        ENNReal.ofReal (t ^ ((2 : ℝ) - 1)) ≤
        ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * (t * Real.exp (-b * t ^ 2))) := by
      refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := ht
      have h1 := concentration_lipschitz f K hf t ht0.le
      have h2 : (2 : ℝ) * Real.exp (-(2 * t ^ 2) / (π ^ 2 * (K : ℝ) ^ 2)) * t =
          2 * (t * Real.exp (-b * t ^ 2)) := by
        have : -(2 * t ^ 2) / (π ^ 2 * (K : ℝ) ^ 2) = -b * t ^ 2 := by rw [hb]; ring
        rw [this]; ring
      calc stdGauss ι {a | t < X a} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1))
          ≤ ENNReal.ofReal (2 * Real.exp (-(2 * t ^ 2) / (π ^ 2 * (K : ℝ) ^ 2))) *
              ENNReal.ofReal (t ^ ((2 : ℝ) - 1)) := by gcongr
        _ = ENNReal.ofReal (2 * (t * Real.exp (-b * t ^ 2))) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← h2]
            norm_num
    have hint : Integrable (fun t : ℝ => 2 * (t * Real.exp (-b * t ^ 2)))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      ((integrable_mul_exp_neg_mul_sq hbpos).integrableOn).const_mul 2
    have hnn' : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun t : ℝ => 2 * (t * Real.exp (-b * t ^ 2))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      positivity
    have hval : ∫ t in Set.Ioi (0 : ℝ), 2 * (t * Real.exp (-b * t ^ 2)) = 1 / b := by
      rw [integral_const_mul]
      have key := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := b) two_pos
        (by norm_num) hbpos
      simp_rw [Real.rpow_two, Real.rpow_one] at key
      have e1 : (-(1 + 1) / 2 : ℝ) = -1 := by norm_num
      have e2 : ((1 + 1) / 2 : ℝ) = 1 := by norm_num
      rw [e1, e2, Real.Gamma_one, Real.rpow_neg_one] at key
      rw [key]
      field_simp
    have htotal : ∫⁻ x, ENNReal.ofReal (X x ^ (2 : ℝ)) ∂(stdGauss ι) ≤
        ENNReal.ofReal (π ^ 2 * (K : ℝ) ^ 2) := by
      rw [hlay]
      calc ENNReal.ofReal 2 * ∫⁻ t in Set.Ioi (0 : ℝ), stdGauss ι {a | t < X a} *
            ENNReal.ofReal (t ^ ((2 : ℝ) - 1))
          ≤ ENNReal.ofReal 2 *
              ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * (t * Real.exp (-b * t ^ 2))) := by
            gcongr
        _ = ENNReal.ofReal 2 * ENNReal.ofReal (1 / b) := by
            rw [← hval, ofReal_integral_eq_lintegral_ofReal hint hnn']
        _ = ENNReal.ofReal (π ^ 2 * (K : ℝ) ^ 2) := by
            rw [← ENNReal.ofReal_mul (by norm_num)]
            congr 1
            rw [hb]
            field_simp
    have hsq : ∀ x, X x ^ (2 : ℝ) = (f x - m) ^ 2 := fun x => by
      rw [Real.rpow_two, hX]
      exact sq_abs _
    have hcont2 : Continuous fun x => (f x - m) ^ 2 := (hfc.sub continuous_const).pow 2
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => sq_nonneg _) hcont2.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    simpa only [hsq] using htotal

end LSBA
