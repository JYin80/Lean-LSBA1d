import Mathlib

/-!
# A moment tool

A generic tool for the moment recursion (11.59) [lg:eq:momentrec] (proof of Lemma 11.8
[lg:lem:dynamic]): the centered moment expansion
`𝔼|a + ξ|^{2p} ≤ |a|^{2p} + K_p Σ_{j=2}^{2p} |a|^{2p−j} 𝔼|ξ|^j` for `𝔼ξ = 0`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- Second-order Taylor bound for `x ↦ x^(p+2)` on `[0, M]`. -/
private lemma momentTools_taylor (M A B : ℝ) (hA : 0 ≤ A) (hAM : A ≤ M) (hB : 0 ≤ B)
    (hBM : B ≤ M) (p : ℕ) :
    A ^ (p + 2) ≤ B ^ (p + 2) + ((p : ℝ) + 2) * B ^ (p + 1) * (A - B)
      + ((p : ℝ) + 2) ^ 2 * (A - B) ^ 2 * M ^ p := by
  induction p with
  | zero => simp; nlinarith [sq_nonneg (A - B)]
  | succ p ih =>
    have hX : 0 ≤ (A - B) ^ 2 := sq_nonneg _
    have hM : 0 ≤ M := hA.trans hAM
    have h1 : B ^ (p + 1) ≤ M ^ (p + 1) := pow_le_pow_left₀ hB hBM _
    have h2 : A * M ^ p ≤ M ^ (p + 1) := by
      rw [pow_succ]; nlinarith [pow_nonneg hM p]
    have h3 : A * A ^ (p + 2) ≤ A * (B ^ (p + 2) + ((p : ℝ) + 2) * B ^ (p + 1) * (A - B)
        + ((p : ℝ) + 2) ^ 2 * (A - B) ^ 2 * M ^ p) := mul_le_mul_of_nonneg_left ih hA
    have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have h4 : ((p : ℝ) + 2) * B ^ (p + 1) * (A - B) ^ 2
        ≤ ((p : ℝ) + 2) * M ^ (p + 1) * (A - B) ^ 2 := by
      have := mul_le_mul_of_nonneg_right h1 hX
      nlinarith
    have h5 : A * (((p : ℝ) + 2) ^ 2 * (A - B) ^ 2 * M ^ p)
        ≤ ((p : ℝ) + 2) ^ 2 * (A - B) ^ 2 * M ^ (p + 1) := by
      have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ ((p : ℝ) + 2) ^ 2 * (A - B) ^ 2)
      nlinarith
    have h6 : (((p : ℝ) + 2) + ((p : ℝ) + 2) ^ 2) * ((A - B) ^ 2 * M ^ (p + 1))
        ≤ ((p : ℝ) + 3) ^ 2 * ((A - B) ^ 2 * M ^ (p + 1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    have e : A ^ (p + 1 + 2) = A * A ^ (p + 2) := by ring
    have e2 : A * (B ^ (p + 2) + ((p : ℝ) + 2) * B ^ (p + 1) * (A - B))
        = (B ^ (p + 1 + 2) + (((p : ℝ) + 1) + 2) * B ^ (p + 1 + 1) * (A - B))
          + ((p : ℝ) + 2) * B ^ (p + 1) * (A - B) ^ 2 := by
      ring
    rw [e]
    push_cast
    nlinarith [h3, h4, h5, h6, e2]

/-- `s² (r + s)^(2m) ≤ 4^m Σ_{j=2}^{2m+2} r^(2m+2−j) s^j` for `r, s ≥ 0`. -/
private lemma momentTools_sum (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (m : ℕ) :
    s ^ 2 * (r + s) ^ (2 * m) ≤
      4 ^ m * ∑ j ∈ Finset.Icc 2 (2 * (m + 1)), r ^ (2 * (m + 1) - j) * s ^ j := by
  have hI : Finset.Icc 2 (2 * (m + 1)) = Finset.Ico 2 (2 * m + 3) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range, add_comm r s, add_pow, Finset.mul_sum, Finset.mul_sum]
  have hn : 2 * m + 3 - 2 = 2 * m + 1 := by omega
  rw [hn]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ 2 * m := by have := Finset.mem_range.mp hi; omega
  have hc : ((2 * m).choose i : ℝ) ≤ 4 ^ m := by
    have := Nat.choose_le_two_pow (2 * m) i
    have h2 : ((2 * m).choose i : ℝ) ≤ ((2 ^ (2 * m) : ℕ) : ℝ) := by exact_mod_cast this
    calc ((2 * m).choose i : ℝ) ≤ ((2 ^ (2 * m) : ℕ) : ℝ) := h2
      _ = 4 ^ m := by push_cast; rw [pow_mul]; norm_num
  have he : 2 * (m + 1) - (2 + i) = 2 * m - i := by omega
  rw [he]
  have h0 : 0 ≤ r ^ (2 * m - i) * s ^ (2 + i) := by positivity
  calc s ^ 2 * (s ^ i * r ^ (2 * m - i) * ((2 * m).choose i : ℝ))
      = (r ^ (2 * m - i) * s ^ (2 + i)) * ((2 * m).choose i : ℝ) := by ring
    _ ≤ (r ^ (2 * m - i) * s ^ (2 + i)) * 4 ^ m := mul_le_mul_of_nonneg_left hc h0
    _ = 4 ^ m * (r ^ (2 * m - i) * s ^ (2 + i)) := by ring

/-- Pointwise bound: the expansion of `|a + z|^(2p)` with the linear term kept explicitly. -/
private lemma momentTools_pointwise (p : ℕ) (a z : ℂ) :
    ‖a + z‖ ^ (2 * p) ≤ ‖a‖ ^ (2 * p) +
      2 * (p : ℝ) * ‖a‖ ^ (2 * p - 2) * (a.re * z.re + a.im * z.im) +
      (1 + p + (p : ℝ) ^ 2 * 4 ^ p) *
        ∑ j ∈ Finset.Icc 2 (2 * p), ‖a‖ ^ (2 * p - j) * ‖z‖ ^ j := by
  have hsq : ‖a + z‖ ^ 2 = ‖a‖ ^ 2 + 2 * (a.re * z.re + a.im * z.im) + ‖z‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im]; ring
  have hr : 0 ≤ ‖a‖ := norm_nonneg _
  have hs : 0 ≤ ‖z‖ := norm_nonneg _
  have hK0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rcases p with _ | _ | q
  · simp
  · have hI : Finset.Icc 2 (2 * (0 + 1)) = {2} := by decide
    rw [hI]
    simp only [Finset.sum_singleton]
    norm_num
    nlinarith [hsq, sq_nonneg ‖z‖]
  · set S := ∑ j ∈ Finset.Icc 2 (2 * (q + 1 + 1)), ‖a‖ ^ (2 * (q + 1 + 1) - j) * ‖z‖ ^ j
      with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => by positivity
    have hle := momentTools_sum ‖a‖ ‖z‖ hr hs (q + 1)
    rw [← hS] at hle
    have h2mem : 2 ∈ Finset.Icc 2 (2 * (q + 1 + 1)) := by
      simp only [Finset.mem_Icc]; omega
    have hsingle : ‖a‖ ^ (2 * (q + 1 + 1) - 2) * ‖z‖ ^ 2 ≤ S :=
      Finset.single_le_sum (f := fun j => ‖a‖ ^ (2 * (q + 1 + 1) - j) * ‖z‖ ^ j)
        (fun j _ => by positivity) h2mem
    have htay := momentTools_taylor ((‖a‖ + ‖z‖) ^ 2) (‖a + z‖ ^ 2) (‖a‖ ^ 2) (by positivity)
      (by rw [sq_le_sq₀ (norm_nonneg _) (by positivity)]; exact norm_add_le a z)
      (by positivity) (by gcongr; linarith) q
    have habs : |‖a + z‖ - ‖a‖| ≤ ‖z‖ := by
      have := abs_norm_sub_norm_le (a + z) a
      simpa using this
    have hdif : (‖a + z‖ ^ 2 - ‖a‖ ^ 2) ^ 2 ≤ 4 * (‖z‖ ^ 2 * (‖a‖ + ‖z‖) ^ 2) := by
      have h1 : (‖a + z‖ - ‖a‖) ^ 2 ≤ ‖z‖ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      have h2 : ‖a + z‖ ≤ ‖a‖ + ‖z‖ := norm_add_le a z
      have h3 : (‖a + z‖ + ‖a‖) ^ 2 ≤ 4 * (‖a‖ + ‖z‖) ^ 2 := by
        nlinarith [norm_nonneg (a + z)]
      calc (‖a + z‖ ^ 2 - ‖a‖ ^ 2) ^ 2
          = (‖a + z‖ - ‖a‖) ^ 2 * (‖a + z‖ + ‖a‖) ^ 2 := by ring
        _ ≤ ‖z‖ ^ 2 * (4 * (‖a‖ + ‖z‖) ^ 2) :=
          mul_le_mul h1 h3 (by positivity) (by positivity)
        _ = 4 * (‖z‖ ^ 2 * (‖a‖ + ‖z‖) ^ 2) := by ring
    have hpow : ((‖a‖ + ‖z‖) ^ 2) ^ q = (‖a‖ + ‖z‖) ^ (2 * q) := by rw [← pow_mul]
    have hterm : (((q : ℝ) + 2) ^ 2 * (‖a + z‖ ^ 2 - ‖a‖ ^ 2) ^ 2 * ((‖a‖ + ‖z‖) ^ 2) ^ q)
        ≤ ((q : ℝ) + 2) ^ 2 * 4 * (‖z‖ ^ 2 * (‖a‖ + ‖z‖) ^ (2 * (q + 1))) := by
      rw [hpow]
      have : (‖a + z‖ ^ 2 - ‖a‖ ^ 2) ^ 2 * (‖a‖ + ‖z‖) ^ (2 * q) ≤
          4 * (‖z‖ ^ 2 * (‖a‖ + ‖z‖) ^ 2) * (‖a‖ + ‖z‖) ^ (2 * q) :=
        mul_le_mul_of_nonneg_right hdif (by positivity)
      have e : (‖a‖ + ‖z‖) ^ (2 * (q + 1)) = (‖a‖ + ‖z‖) ^ 2 * (‖a‖ + ‖z‖) ^ (2 * q) := by
        rw [show 2 * (q + 1) = 2 + 2 * q by ring, pow_add]
      rw [e]
      have hq : (0 : ℝ) ≤ ((q : ℝ) + 2) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hq]
    have hfin : ((q : ℝ) + 2) ^ 2 * 4 * (‖z‖ ^ 2 * (‖a‖ + ‖z‖) ^ (2 * (q + 1)))
        ≤ ((q : ℝ) + 2) ^ 2 * 4 ^ (q + 2) * S := by
      have h4 : ‖z‖ ^ 2 * (‖a‖ + ‖z‖) ^ (2 * (q + 1)) ≤ 4 ^ (q + 1) * S := hle
      have hq : (0 : ℝ) ≤ ((q : ℝ) + 2) ^ 2 * 4 := by positivity
      calc ((q : ℝ) + 2) ^ 2 * 4 * (‖z‖ ^ 2 * (‖a‖ + ‖z‖) ^ (2 * (q + 1)))
          ≤ ((q : ℝ) + 2) ^ 2 * 4 * (4 ^ (q + 1) * S) := mul_le_mul_of_nonneg_left h4 hq
        _ = ((q : ℝ) + 2) ^ 2 * 4 ^ (q + 2) * S := by ring
    have hlhs : ‖a + z‖ ^ (2 * (q + 1 + 1)) = (‖a + z‖ ^ 2) ^ (q + 2) := by
      rw [← pow_mul]
    have hB : ‖a‖ ^ (2 * (q + 1 + 1)) = (‖a‖ ^ 2) ^ (q + 2) := by
      rw [← pow_mul]
    have hlin : ((q : ℝ) + 2) * (‖a‖ ^ 2) ^ (q + 1) * (‖a + z‖ ^ 2 - ‖a‖ ^ 2)
        = 2 * ((q + 1 + 1 : ℕ) : ℝ) * ‖a‖ ^ (2 * (q + 1 + 1) - 2) *
            (a.re * z.re + a.im * z.im) +
          ((q : ℝ) + 2) * (‖a‖ ^ (2 * (q + 1 + 1) - 2) * ‖z‖ ^ 2) := by
      have e1 : (‖a‖ ^ 2) ^ (q + 1) = ‖a‖ ^ (2 * (q + 1 + 1) - 2) := by
        rw [← pow_mul]; congr 1
      rw [e1]; push_cast
      have : ‖a + z‖ ^ 2 - ‖a‖ ^ 2 = 2 * (a.re * z.re + a.im * z.im) + ‖z‖ ^ 2 := by
        linarith
      rw [this]; ring
    have hKS : ((q : ℝ) + 2) * (‖a‖ ^ (2 * (q + 1 + 1) - 2) * ‖z‖ ^ 2) +
        ((q : ℝ) + 2) ^ 2 * 4 ^ (q + 2) * S ≤
        (1 + ((q + 1 + 1 : ℕ) : ℝ) + ((q + 1 + 1 : ℕ) : ℝ) ^ 2 * 4 ^ (q + 1 + 1)) * S := by
      push_cast
      have h1 : ((q : ℝ) + 2) * (‖a‖ ^ (2 * (q + 1 + 1) - 2) * ‖z‖ ^ 2) ≤ ((q : ℝ) + 2) * S :=
        mul_le_mul_of_nonneg_left hsingle (by positivity)
      have h2 : (0 : ℝ) ≤ S := hS0
      nlinarith
    rw [hlhs, hB]
    push_cast at *
    nlinarith [htay, hterm, hfin, hlin, hKS]

/-- Centered moment expansion: the linear term cancels when `𝔼ξ = 0`. -/
theorem integral_norm_add_pow_le (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (a : ℂ) (ξ : Ω → ℂ), Integrable ξ P → ∫ ω, ξ ω ∂P = 0 →
        (∀ j ≤ 2 * p, Integrable (fun ω => ‖ξ ω‖ ^ j) P) →
        ∫ ω, ‖a + ξ ω‖ ^ (2 * p) ∂P ≤
          ‖a‖ ^ (2 * p) +
            K * ∑ j ∈ Finset.Icc 2 (2 * p), ‖a‖ ^ (2 * p - j) * ∫ ω, ‖ξ ω‖ ^ j ∂P := by
  refine ⟨1 + p + (p : ℝ) ^ 2 * 4 ^ p, by positivity, ?_⟩
  intro Ω _ P _ a ξ hξ h0 hint
  set K : ℝ := 1 + p + (p : ℝ) ^ 2 * 4 ^ p with hK
  have hξre : Integrable (fun ω => (ξ ω).re) P := hξ.re
  have hξim : Integrable (fun ω => (ξ ω).im) P := hξ.im
  have hre : ∫ ω, (ξ ω).re ∂P = 0 := by
    have := integral_re hξ
    simpa [h0] using this
  have him : ∫ ω, (ξ ω).im ∂P = 0 := by
    have := integral_im hξ
    simpa [h0] using this
  have htint : Integrable (fun ω => a.re * (ξ ω).re + a.im * (ξ ω).im) P :=
    (hξre.const_mul a.re).add (hξim.const_mul a.im)
  have ht0 : ∫ ω, (a.re * (ξ ω).re + a.im * (ξ ω).im) ∂P = 0 := by
    rw [integral_add (hξre.const_mul a.re) (hξim.const_mul a.im),
      integral_const_mul, integral_const_mul, hre, him]; simp
  have hSint : Integrable (fun ω => ∑ j ∈ Finset.Icc 2 (2 * p),
      ‖a‖ ^ (2 * p - j) * ‖ξ ω‖ ^ j) P :=
    integrable_finsetSum _ fun j hj =>
      (hint j (Finset.mem_Icc.mp hj).2).const_mul _
  have hgint : Integrable (fun ω => ‖a‖ ^ (2 * p) +
      2 * (p : ℝ) * ‖a‖ ^ (2 * p - 2) * (a.re * (ξ ω).re + a.im * (ξ ω).im) +
      K * ∑ j ∈ Finset.Icc 2 (2 * p), ‖a‖ ^ (2 * p - j) * ‖ξ ω‖ ^ j) P :=
    ((integrable_const _).add (htint.const_mul _)).add (hSint.const_mul _)
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω => by positivity) hgint
    (Filter.Eventually.of_forall fun ω => momentTools_pointwise p a (ξ ω))
  refine hmono.trans (le_of_eq ?_)
  have hlin : Integrable (fun ω => ‖a‖ ^ (2 * p) +
      2 * (p : ℝ) * ‖a‖ ^ (2 * p - 2) * (a.re * (ξ ω).re + a.im * (ξ ω).im)) P :=
    (integrable_const _).add (htint.const_mul _)
  have hSint' : Integrable (fun ω => K * ∑ j ∈ Finset.Icc 2 (2 * p),
      ‖a‖ ^ (2 * p - j) * ‖ξ ω‖ ^ j) P := hSint.const_mul _
  have hlin0 : ∫ ω, (‖a‖ ^ (2 * p) +
      2 * (p : ℝ) * ‖a‖ ^ (2 * p - 2) * (a.re * (ξ ω).re + a.im * (ξ ω).im)) ∂P
        = ‖a‖ ^ (2 * p) := by
    rw [integral_add (integrable_const _) (htint.const_mul _), integral_const_mul, ht0]
    simp
  have hS0 : ∫ ω, ∑ j ∈ Finset.Icc 2 (2 * p), ‖a‖ ^ (2 * p - j) * ‖ξ ω‖ ^ j ∂P
      = ∑ j ∈ Finset.Icc 2 (2 * p), ‖a‖ ^ (2 * p - j) * ∫ ω, ‖ξ ω‖ ^ j ∂P := by
    rw [integral_finsetSum _ fun j hj => (hint j (Finset.mem_Icc.mp hj).2).const_mul _]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  rw [integral_add hlin hSint', hlin0, integral_const_mul, hS0]

end LSBA
