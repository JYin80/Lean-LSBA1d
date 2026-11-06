import LSBA.Upper.FracMoment
import LSBA.Upper.ConversionCycle
import LSBA.Upper.NearZeroTransfer

/-!
# The finite-volume criterion

Proposition 8.2 [up:prop:fr-concentration]: the endpoint bound (8.6)
[uv:eq:upper-volume-input] at one length `n ≤ C₀ 𝔟 log W` gives (8.2) [up:eq:fmr-pointwise] with
`q = s/2` on every Dirichlet path and every cycle, through (E.14) [eq:c-interval], (E.15)
[eq:c-cycle-Schur], (E.16) [eq:c-cycle] and (8.7) [eq:c-apriori] (Appendix E.2
[app:finite-volume-criterion]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The path operator with zero shifts is the free part plus the scaled diagonal block
potential. -/
private lemma fracCriterion_pathOp_decomp (g : ℝ) {W n : ℕ} (ω : Ω W n) :
    pathOp g (gueBlock W n ω) 0 0 =
      pathOp g (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) 0 0 +
        (((max 1 g)⁻¹ : ℝ) : ℂ) • blockDiagOp (gueBlock W n ω) := by
  have h0 : blockDiagOp (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) = 0 := by
    ext p q
    simp [blockDiagOp]
  simp only [pathOp, h0, add_zero, smul_add, Complex.ofReal_inv, ite_self]

/-- The `x, y` block norm of the resolvent of the path operator is a measurable function of the
sample. -/
private lemma fracCriterion_measurable {W n : ℕ} (g E : ℝ) (x y : Fin n) :
    Measurable fun ω : Ω W n =>
      ‖blockOf (resolventMat (pathOp g (gueBlock W n ω) 0 0) E) x y‖ₑ := by
  have h := measurable_resolventMat_gueBlock (W := W) (n := n)
    (pathOp g (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) 0 0) ((max 1 g)⁻¹) (E : ℂ)
  have hblk : Measurable fun X : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ => blockOf X x y := by
    refine Measurable.of_eval_matrix _ fun α β => ?_
    exact measurable_id.eval_matrix (i := (x, α)) (j := (y, β))
  simp only [fracCriterion_pathOp_decomp]
  exact continuous_enorm.measurable.comp (hblk.comp h)

/-- Jensen's inequality on a probability space: `𝔼 f^{s/2} ≤ (𝔼 f^s)^{1/2}`. -/
private lemma fracCriterion_jensen {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {f : α → ℝ≥0∞} (hf : Measurable f) {s x : ℝ} (hx : 0 ≤ x)
    (h : ∫⁻ ω, f ω ^ s ∂ν ≤ ENNReal.ofReal x) :
    ∫⁻ ω, f ω ^ (s / 2) ∂ν ≤ ENNReal.ofReal (Real.sqrt x) := by
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
    (hf.pow_const (s / 2)).aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    ENNReal.one_rpow] at key
  refine key.trans ?_
  have e : ∀ ω, (f ω ^ (s / 2)) ^ (2 : ℝ) = f ω ^ s := fun ω => by
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  simp_rw [e]
  calc (∫⁻ ω, f ω ^ s ∂ν) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal x) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt x) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), Real.sqrt_eq_rpow]

/-- Proposition 8.2 [up:prop:fr-concentration]: for fixed `C₀ ≥ 1` and `s ∈ (0, 1/2)` there are
`C, c > 0` and a width threshold, independent of `L, g, 𝔟, J, n`, such that for `0 < g ≤ W^{C₀}`,
`𝔟 ≥ 1`, every energy set `J` and `1 ≤ n ≤ C₀ 𝔟 log W`, (8.6) [uv:eq:upper-volume-input] at length
`n` gives (8.2) [up:eq:fmr-pointwise] with `q = s/2` and scale `𝔟` on every Dirichlet path and
on every cycle of `L ≥ 3` blocks. -/
theorem frac_criterion {C₀ s : ℝ} (hC₀ : 1 ≤ C₀) (hs0 : 0 < s) (hs1 : s < 1 / 2) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g b : ℝ, 0 < g →
      g ≤ (W : ℝ) ^ C₀ → 1 ≤ b → ∀ (J : Set ℝ) (n : ℕ), 1 ≤ n →
      (n : ℝ) ≤ C₀ * b * Real.log W → EndpointMomentAt W g J s n ((W : ℝ) ^ (-2 : ℝ)) →
        (∀ m : ℕ, FracPath W m g J (s / 2) C c b) ∧
          ∀ L : ℕ, 3 ≤ L → FracCycle W L g J (s / 2) C c b := by
  have hB : 0 < C₀ := by linarith
  have hs1' : s < 1 := by linarith
  have hC' : 0 < C₀ + 1 := by linarith
  have hap : ∀ p : ℝ, p < 1 → 0 < aprioriConst p := fun p hp => by
    unfold aprioriConst
    have : 0 < 1 - p := by linarith
    positivity
  have hP0 : 0 < (C₀ + 2) * s := by positivity
  refine ⟨(C₀ + 2) * s + 3, 1 / (C₀ + 1), by positivity, by positivity,
    max 3 (max ⌈2 * aprioriConst s⌉₊ ⌈aprioriConst (s / 2)⌉₊), ?_⟩
  intro W hW g b hg0 hgB hb1 J n hn1 hn hEP
  have hW3 : 3 ≤ W := le_trans (le_max_left _ _) hW
  have hWa : 2 * aprioriConst s ≤ (W : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW)
  have hWb : aprioriConst (s / 2) ≤ (W : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW)
  have hW3' : (3 : ℝ) ≤ W := by exact_mod_cast hW3
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hW1' : 1 ≤ W := by omega
  have hb0 : 0 < b := by linarith
  have hlog : 1 ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le hW0]
    linarith [Real.exp_one_lt_three]
  have hbl : 1 ≤ b * Real.log W := one_le_mul_of_one_le_of_one_le hb1 hlog
  have hnb : (n : ℝ) + 1 ≤ (C₀ + 1) * b * Real.log W := by
    have e : (C₀ + 1) * b * Real.log W = C₀ * b * Real.log W + b * Real.log W := by ring
    rw [e]
    linarith
  have hmB : max 1 g ≤ (W : ℝ) ^ C₀ := max_le (Real.one_le_rpow hW1 hB.le) hgB
  have hC_s := hap s hs1'
  have hC_q := hap (s / 2) (by linarith)
  have hX : (max 1 g * (W : ℝ) ^ 2) ^ (s / 2) ≤ (W : ℝ) ^ ((C₀ + 2) * (s / 2)) := by
    have h1 : max 1 g * (W : ℝ) ^ 2 ≤ (W : ℝ) ^ (C₀ + 2) := by
      rw [Real.rpow_add hW0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_right hmB (by positivity)
    have h2 : 0 ≤ max 1 g * (W : ℝ) ^ 2 :=
      mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (by positivity)
    calc (max 1 g * (W : ℝ) ^ 2) ^ (s / 2) ≤ ((W : ℝ) ^ (C₀ + 2)) ^ (s / 2) :=
          Real.rpow_le_rpow h2 h1 (by positivity)
      _ = _ := (Real.rpow_mul hW0.le _ _).symm
  constructor
  · intro m E hE x y
    have hdec := interval_moment_decay_scale hs0 hs1' hB hb0 hC' hW1' hg0 hgB hnb hEP m hE x y
    refine (fracCriterion_jensen (fracCriterion_measurable g E x y) (by positivity) hdec).trans
      (ENNReal.ofReal_le_ofReal ?_)
    set d : ℝ := |((x : ℕ) : ℝ) - (y : ℕ)| with hd
    refine (Real.sqrt_le_left (by positivity)).2 ?_
    have hE2 : Real.exp (-(2 / (C₀ + 1)) * d / b) = Real.exp (-(1 / (C₀ + 1)) * d / b) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hA : aprioriConst s * (W : ℝ) ^ ((C₀ + 2) * s + 2) ≤
        ((W : ℝ) ^ ((C₀ + 2) * s + 3)) ^ 2 := by
      have h1 : aprioriConst s ≤ (W : ℝ) := by linarith
      have e : ((W : ℝ) ^ ((C₀ + 2) * s + 3)) ^ 2 =
          (W : ℝ) * ((W : ℝ) ^ ((C₀ + 2) * s + 2) * (W : ℝ) ^ ((C₀ + 2) * s + 3)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_add hW0,
          show ((W : ℝ) * (W : ℝ) ^ ((C₀ + 2) * s + 2 + ((C₀ + 2) * s + 3))) =
            (W : ℝ) ^ (1 : ℝ) * (W : ℝ) ^ ((C₀ + 2) * s + 2 + ((C₀ + 2) * s + 3)) by
            rw [Real.rpow_one], ← Real.rpow_add hW0]
        congr 1
        push_cast
        ring
      have h2 : 1 ≤ (W : ℝ) ^ ((C₀ + 2) * s + 3) := Real.one_le_rpow hW1 (by positivity)
      have h3 : 0 ≤ (W : ℝ) ^ ((C₀ + 2) * s + 2) := by positivity
      rw [e]
      calc aprioriConst s * (W : ℝ) ^ ((C₀ + 2) * s + 2)
          ≤ W * (W : ℝ) ^ ((C₀ + 2) * s + 2) := by gcongr
        _ ≤ W * ((W : ℝ) ^ ((C₀ + 2) * s + 2) * (W : ℝ) ^ ((C₀ + 2) * s + 3)) := by
            refine mul_le_mul_of_nonneg_left ?_ hW0.le
            exact le_mul_of_one_le_right h3 h2
    rw [hE2, mul_pow]
    gcongr
  · intro L hL E hE x y
    by_cases hxy : x = y
    · subst hxy
      have hd : cycDist x x = 0 := by simp [cycDist]
      simp only [hd, Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, mul_one]
      refine (Hmat_moment_le g (by positivity) (by linarith) E x x).trans
        (ENNReal.ofReal_le_ofReal ?_)
      calc aprioriConst (s / 2) * (max 1 g * (W : ℝ) ^ 2) ^ (s / 2)
          ≤ W * (W : ℝ) ^ ((C₀ + 2) * (s / 2)) := mul_le_mul hWb hX (by positivity) hW0.le
        _ = (W : ℝ) ^ (1 + (C₀ + 2) * (s / 2)) := by
            rw [Real.rpow_add hW0, Real.rpow_one]
        _ ≤ (W : ℝ) ^ ((C₀ + 2) * s + 3) := Real.rpow_le_rpow_of_exponent_le hW1 (by nlinarith)
    · refine (cycle_moment_decay_scale hs0 hs1' hB hb0 hC' hW1' hg0 hgB hnb hEP hL hE hxy).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have e : (W : ℝ) ^ ((C₀ + 2) * s + 3) = (W : ℝ) * (W : ℝ) ^ ((C₀ + 2) * s + 2) := by
        rw [show (C₀ + 2) * s + 3 = 1 + ((C₀ + 2) * s + 2) by ring, Real.rpow_add hW0,
          Real.rpow_one]
      rw [e]
      gcongr

end LSBA
