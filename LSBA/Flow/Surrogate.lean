import Mathlib

/-!
# The `ℓ^{2q}` surrogate

`X = (Σ_s (|y_s|²/env_s² + δ²)^q)^{1/(2q)}`, a smooth convex surrogate of `max_s |y_s|/env_s`, with
its gradient, Hessian and carré du champ bounds and the choice `q ≍ log|S|` that makes
`|S|^{1/(2q)} ≤ 1 + δ_q` (used by the mixed-pair bound).
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The `ℓ^{2q}` surrogate `(Σ_s (|y_s|²/env_s² + δ²)^q)^{1/(2q)}`. -/
def lqSurr {S : Type*} [Fintype S] (q : ℕ) (env : S → ℝ) (δ : ℝ) (y : S → ℂ) : ℝ :=
  (∑ s, (‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2) ^ q) ^ ((1 : ℝ) / (2 * q))

/-- Power-mean inequality `Σ xᵢ^θ ≤ |ι|^{1-θ} (Σ xᵢ)^θ` for `0 ≤ θ ≤ 1`. -/
private lemma surr_sum_rpow_le {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∑ i, x i ^ θ ≤ (Fintype.card ι : ℝ) ^ (1 - θ) * (∑ i, x i) ^ θ := by
  rcases h0.eq_or_lt with rfl | hpos
  · simp
  · have hp : 1 ≤ 1 / θ := by rw [le_div_iff₀ hpos]; linarith
    have key := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ)
      (f := fun i => x i ^ θ) hp (fun i _ => Real.rpow_nonneg (hx i) θ)
    have e1 : ∀ i, (x i ^ θ) ^ (1 / θ) = x i := fun i => by
      rw [← Real.rpow_mul (hx i), mul_one_div_cancel hpos.ne', Real.rpow_one]
    simp only [e1, Finset.card_univ] at key
    have hS : 0 ≤ ∑ i, x i ^ θ := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hx i) θ
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hS _) key h0
    rw [← Real.rpow_mul hS, one_div, inv_mul_cancel₀ hpos.ne', Real.rpow_one,
      Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Finset.sum_nonneg fun i _ => hx i),
      ← Real.rpow_mul (Nat.cast_nonneg _)] at h2
    convert h2 using 3
    field_simp

section Core

variable {ι : Type*} [Fintype ι]

/-- The quadratic `a + 2 b t + c t²` in the line parameter `t`. -/
private def surrQ (a b c : ι → ℝ) (s : ι) (t : ℝ) : ℝ := a s + 2 * b s * t + c s * t ^ 2

/-- The power sum `Σ_s (a_s + 2 b_s t + c_s t²)^q` along the line. -/
private def surrN (q : ℕ) (a b c : ι → ℝ) (t : ℝ) : ℝ := ∑ s, surrQ a b c s t ^ q

/-- The `t`-derivative of `surrN`. -/
private def surrN1 (q : ℕ) (a b c : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ s, (q : ℝ) * surrQ a b c s t ^ (q - 1) * (2 * b s + 2 * c s * t)

/-- The `t`-derivative of `surrN1`. -/
private def surrN2 (q : ℕ) (a b c : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ s, ((q : ℝ) * (((q - 1 : ℕ) : ℝ) * surrQ a b c s t ^ (q - 1 - 1) * (2 * b s + 2 * c s * t)) *
      (2 * b s + 2 * c s * t) + (q : ℝ) * surrQ a b c s t ^ (q - 1) * (2 * c s))

/-- The surrogate along the line: `(surrN q a b c t)^{1/(2q)}`. -/
private def surrPhi (q : ℕ) (a b c : ι → ℝ) (t : ℝ) : ℝ :=
  surrN q a b c t ^ ((1 : ℝ) / (2 * q))

omit [Fintype ι] in
private lemma surrQ_hasDerivAt (a b c : ι → ℝ) (s : ι) (t : ℝ) :
    HasDerivAt (surrQ a b c s) (2 * b s + 2 * c s * t) t := by
  have h := ((hasDerivAt_const t (a s)).add ((hasDerivAt_id t).const_mul (2 * b s))).add
    ((hasDerivAt_pow 2 t).const_mul (c s))
  convert h using 1
  · ext u; simp [surrQ]
  · simp; ring

private lemma surrN_hasDerivAt (q : ℕ) (a b c : ι → ℝ) (t : ℝ) :
    HasDerivAt (surrN q a b c) (surrN1 q a b c t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun s _ => (surrQ_hasDerivAt a b c s t).fun_pow q)
  exact h

private lemma surrN1_hasDerivAt (q : ℕ) (a b c : ι → ℝ) (t : ℝ) :
    HasDerivAt (surrN1 q a b c) (surrN2 q a b c t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun s _ =>
    (((surrQ_hasDerivAt a b c s t).fun_pow (q - 1)).const_mul (q : ℝ)).mul
      (((hasDerivAt_id t).const_mul (2 * c s)).const_add (2 * b s)))
  convert h using 1
  · ext u; simp [surrN1]
  · simp [surrN2]


private lemma surrN_pos [Nonempty ι] (q : ℕ) (a b c : ι → ℝ) (hpos : ∀ s t, 0 < surrQ a b c s t)
    (t : ℝ) : 0 < surrN q a b c t :=
  Finset.sum_pos (fun s _ => pow_pos (hpos s t) q) Finset.univ_nonempty

private lemma surrPhi_hasDerivAt [Nonempty ι] (q : ℕ) (a b c : ι → ℝ)
    (hpos : ∀ s t, 0 < surrQ a b c s t) (t : ℝ) :
    HasDerivAt (surrPhi q a b c)
      ((1 / (2 * q) : ℝ) * surrN q a b c t ^ ((1 : ℝ) / (2 * q) - 1) * surrN1 q a b c t) t :=
  by
  have h := (surrN_hasDerivAt q a b c t).rpow_const (p := (1 : ℝ) / (2 * q))
    (Or.inl (surrN_pos q a b c hpos t).ne')
  exact h.congr_deriv (by ring)

private lemma surrPhi_deriv [Nonempty ι] (q : ℕ) (a b c : ι → ℝ)
    (hpos : ∀ s t, 0 < surrQ a b c s t) :
    deriv (surrPhi q a b c) =
      fun t => (1 / (2 * q) : ℝ) * surrN q a b c t ^ ((1 : ℝ) / (2 * q) - 1) * surrN1 q a b c t :=
  funext fun t => (surrPhi_hasDerivAt q a b c hpos t).deriv

private lemma surrPhi_deriv2 [Nonempty ι] (q : ℕ) (a b c : ι → ℝ)
    (hpos : ∀ s t, 0 < surrQ a b c s t) :
    deriv (deriv (surrPhi q a b c)) 0 =
      (1 / (2 * q) : ℝ) * (((1 : ℝ) / (2 * q) - 1) * surrN q a b c 0 ^ ((1 : ℝ) / (2 * q) - 1 - 1) *
        surrN1 q a b c 0 * surrN1 q a b c 0 +
          surrN q a b c 0 ^ ((1 : ℝ) / (2 * q) - 1) * surrN2 q a b c 0) := by
  rw [surrPhi_deriv q a b c hpos]
  have h1 := (((surrN_hasDerivAt q a b c 0).rpow_const
    (p := (1 : ℝ) / (2 * q) - 1) (Or.inl (surrN_pos q a b c hpos 0).ne')).const_mul
      (1 / (2 * q) : ℝ)).mul (surrN1_hasDerivAt q a b c 0)
  have h2 : HasDerivAt (fun t => (1 / (2 * q) : ℝ) * surrN q a b c t ^ ((1 : ℝ) / (2 * q) - 1) *
      surrN1 q a b c t) _ 0 := h1
  rw [h2.deriv]
  ring

end Core

section CoreBounds

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
private lemma surrQ_zero (a b c : ι → ℝ) (s : ι) : surrQ a b c s 0 = a s := by
  simp [surrQ]

private lemma surrN_zero (q : ℕ) (a b c : ι → ℝ) : surrN q a b c 0 = ∑ s, a s ^ q := by
  simp [surrN, surrQ_zero]

private lemma surrN1_zero (q : ℕ) (a b c : ι → ℝ) :
    surrN1 q a b c 0 = ∑ s, (q : ℝ) * a s ^ (q - 1) * (2 * b s) := by
  simp [surrN1, surrQ_zero]

private lemma surrN2_zero (q : ℕ) (a b c : ι → ℝ) :
    surrN2 q a b c 0 = ∑ s, ((q : ℝ) * (((q - 1 : ℕ) : ℝ) * a s ^ (q - 1 - 1) * (2 * b s)) *
      (2 * b s) + (q : ℝ) * a s ^ (q - 1) * (2 * c s)) := by
  simp [surrN2, surrQ_zero]

/-- First-derivative bound at the base point of the line. -/
private lemma surr_grad_le [Nonempty ι] (q : ℕ) (hq : 1 ≤ q) (a b c : ι → ℝ)
    (hpos : ∀ s t, 0 < surrQ a b c s t) (hb : ∀ s, b s ^ 2 ≤ a s * c s) :
    |deriv (surrPhi q a b c) 0| ≤ (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) *
      ∑ s, (a s ^ (q - 1) * Real.sqrt (a s)) * Real.sqrt (c s) := by
  have ha : ∀ s, 0 < a s := fun s => by simpa [surrQ_zero] using hpos s 0
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hN : 0 < ∑ s, a s ^ q := Finset.sum_pos (fun s _ => pow_pos (ha s) q) Finset.univ_nonempty
  rw [surrPhi_deriv q a b c hpos]
  simp only [surrN_zero, surrN1_zero]
  have hθ : (0 : ℝ) < 1 / (2 * q) := by positivity
  rw [abs_mul, abs_mul, abs_of_pos hθ, abs_of_pos (Real.rpow_pos_of_pos hN _)]
  have h1 : |∑ s, (q : ℝ) * a s ^ (q - 1) * (2 * b s)| ≤
      ∑ s, 2 * q * ((a s ^ (q - 1) * Real.sqrt (a s)) * Real.sqrt (c s)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    have hbs : |b s| ≤ Real.sqrt (a s) * Real.sqrt (c s) := by
      rw [← Real.sqrt_mul (ha s).le]; exact Real.abs_le_sqrt (hb s)
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ q),
      abs_of_nonneg (by have := ha s; positivity : (0 : ℝ) ≤ a s ^ (q - 1)), abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have has := ha s
    calc (q : ℝ) * a s ^ (q - 1) * (2 * |b s|)
        ≤ (q : ℝ) * a s ^ (q - 1) * (2 * (Real.sqrt (a s) * Real.sqrt (c s))) := by gcongr
      _ = _ := by ring
  calc (1 / (2 * q) : ℝ) * (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) *
        |∑ s, (q : ℝ) * a s ^ (q - 1) * (2 * b s)|
      ≤ (1 / (2 * q) : ℝ) * (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) *
        ∑ s, 2 * q * ((a s ^ (q - 1) * Real.sqrt (a s)) * Real.sqrt (c s)) := by gcongr
    _ = _ := by
      rw [← Finset.mul_sum]; field_simp

end CoreBounds

section CoreHess

variable {ι : Type*} [Fintype ι]

private lemma surr_pow_aux (m : ℕ) {a b c : ℝ} (ha : 0 < a) (hb : b ^ 2 ≤ a * c) :
    (m : ℝ) * a ^ (m - 1) * b ^ 2 ≤ m * a ^ m * c := by
  rcases m with _ | k
  · simp
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    calc ((k : ℝ) + 1) * a ^ k * b ^ 2 ≤ ((k : ℝ) + 1) * a ^ k * (a * c) := by gcongr
      _ = _ := by ring

/-- Second-derivative bound at the base point of the line. -/
private lemma surr_hess_le [Nonempty ι] (q : ℕ) (hq : 1 ≤ q) (a b c : ι → ℝ)
    (hpos : ∀ s t, 0 < surrQ a b c s t) (hb : ∀ s, b s ^ 2 ≤ a s * c s) :
    deriv (deriv (surrPhi q a b c)) 0 ≤
      (2 * q - 1) * (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) * ∑ s, a s ^ (q - 1) * c s := by
  have ha : ∀ s, 0 < a s := fun s => by simpa [surrQ_zero] using hpos s 0
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hN : 0 < ∑ s, a s ^ q := Finset.sum_pos (fun s _ => pow_pos (ha s) q) Finset.univ_nonempty
  rw [surrPhi_deriv2 q a b c hpos, surrN_zero]
  have hθ : (0 : ℝ) < 1 / (2 * q) := by positivity
  have hθ1 : (1 : ℝ) / (2 * q) - 1 ≤ 0 := by
    have : (1 : ℝ) / (2 * q) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hN2 : surrN2 q a b c 0 ≤ 2 * q * (2 * q - 1) * ∑ s, a s ^ (q - 1) * c s := by
    rw [surrN2_zero, Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have h := surr_pow_aux (q - 1) (ha s) (hb s)
    have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub hq]; simp
    have e1 : (q : ℝ) * (((q - 1 : ℕ) : ℝ) * a s ^ (q - 1 - 1) * (2 * b s)) * (2 * b s) =
        4 * q * (((q - 1 : ℕ) : ℝ) * a s ^ (q - 1 - 1) * b s ^ 2) := by ring
    rw [e1]
    have h' : (4 * (q : ℝ)) * (((q - 1 : ℕ) : ℝ) * a s ^ (q - 1 - 1) * b s ^ 2) ≤
        (4 * (q : ℝ)) * (((q - 1 : ℕ) : ℝ) * a s ^ (q - 1) * c s) := by gcongr
    rw [hcast] at h' ⊢
    nlinarith [h']
  have hterm : ((1 : ℝ) / (2 * q) - 1) * (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1 - 1) *
      surrN1 q a b c 0 * surrN1 q a b c 0 ≤ 0 := by
    have h1 : 0 ≤ (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1 - 1) := (Real.rpow_pos_of_pos hN _).le
    have h2 : 0 ≤ surrN1 q a b c 0 * surrN1 q a b c 0 := mul_self_nonneg _
    calc _ = (((1 : ℝ) / (2 * q) - 1) * (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1 - 1)) *
          (surrN1 q a b c 0 * surrN1 q a b c 0) := by ring
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hθ1 h1) h2
  have hNr : 0 < (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) := Real.rpow_pos_of_pos hN _
  calc (1 / (2 * q) : ℝ) * (((1 : ℝ) / (2 * q) - 1) * (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1 - 1) *
        surrN1 q a b c 0 * surrN1 q a b c 0 +
          (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) * surrN2 q a b c 0)
      ≤ (1 / (2 * q) : ℝ) * (0 +
          (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) *
            (2 * q * (2 * q - 1) * ∑ s, a s ^ (q - 1) * c s)) := by
        gcongr
    _ = _ := by field_simp; ring

end CoreHess

section Weights

variable {ι : Type*} [Fintype ι]

private lemma surr_pow_sqrt_eq {a : ℝ} (ha : 0 < a) {q : ℕ} (hq : 1 ≤ q) :
    a ^ (q - 1) * Real.sqrt a = (a ^ q) ^ (1 - (1 : ℝ) / (2 * q)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  rw [← Real.rpow_natCast a q, ← Real.rpow_mul ha.le, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast a (q - 1), ← Real.rpow_add ha, Nat.cast_sub hq]
  congr 1
  field_simp
  push_cast
  ring

private lemma surr_pow_eq {a : ℝ} (ha : 0 < a) {q : ℕ} (hq : 1 ≤ q) :
    a ^ (q - 1) = (a ^ q) ^ (1 - (1 : ℝ) / q) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  rw [← Real.rpow_natCast a q, ← Real.rpow_mul ha.le, ← Real.rpow_natCast a (q - 1),
    Nat.cast_sub hq]
  congr 1
  field_simp
  push_cast
  ring

/-- `Σ a^{q-1} √a ≤ |ι|^{1/(2q)} (Σ a^q)^{1-1/(2q)}`. -/
private lemma surr_weight_sqrt_le (q : ℕ) (hq : 1 ≤ q) (a : ι → ℝ) (ha : ∀ s, 0 < a s) :
    ∑ s, a s ^ (q - 1) * Real.sqrt (a s) ≤
      (Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * q)) * (∑ s, a s ^ q) ^ (1 - (1 : ℝ) / (2 * q)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h0 : (0 : ℝ) ≤ 1 - (1 : ℝ) / (2 * q) := by
    have : (1 : ℝ) / (2 * q) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have h1 : 1 - (1 : ℝ) / (2 * q) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / (2 * q) := by positivity
    linarith
  have := surr_sum_rpow_le (fun s => a s ^ q) (fun s => (pow_pos (ha s) q).le) h0 h1
  simp only [← surr_pow_sqrt_eq (ha _) hq, sub_sub_cancel] at this
  exact this

/-- `Σ a^{q-1} ≤ |ι|^{1/q} (Σ a^q)^{1-1/q}`. -/
private lemma surr_weight_le (q : ℕ) (hq : 1 ≤ q) (a : ι → ℝ) (ha : ∀ s, 0 < a s) :
    ∑ s, a s ^ (q - 1) ≤
      (Fintype.card ι : ℝ) ^ ((1 : ℝ) / q) * (∑ s, a s ^ q) ^ (1 - (1 : ℝ) / q) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h0 : (0 : ℝ) ≤ 1 - (1 : ℝ) / q := by
    have : (1 : ℝ) / q ≤ 1 := by rw [div_le_one hqpos]; linarith
    linarith
  have h1 : 1 - (1 : ℝ) / q ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / q := by positivity
    linarith
  have := surr_sum_rpow_le (fun s => a s ^ q) (fun s => (pow_pos (ha s) q).le) h0 h1
  simp only [← surr_pow_eq (ha _) hq, sub_sub_cancel] at this
  exact this

end Weights

section Assembled

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
private lemma surr_ha {a b c : ι → ℝ} (hpos : ∀ s t, 0 < surrQ a b c s t) (s : ι) :
    0 < a s := by simpa [surrQ_zero] using hpos s 0

private lemma surr_grad_sup_le [Nonempty ι] (q : ℕ) (hq : 1 ≤ q) (a b c : ι → ℝ)
    (hpos : ∀ s t, 0 < surrQ a b c s t) (hb : ∀ s, b s ^ 2 ≤ a s * c s) {M : ℝ}
    (hM : ∀ s, Real.sqrt (c s) ≤ M) :
    |deriv (surrPhi q a b c) 0| ≤ (Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * q)) * M := by
  have ha := surr_ha hpos
  have hN : 0 < ∑ s, a s ^ q := Finset.sum_pos (fun s _ => pow_pos (ha s) q) Finset.univ_nonempty
  have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans (hM (Classical.arbitrary ι))
  refine (surr_grad_le q hq a b c hpos hb).trans ?_
  have hW := surr_weight_sqrt_le q hq a ha
  have h1 : ∑ s, (a s ^ (q - 1) * Real.sqrt (a s)) * Real.sqrt (c s) ≤
      (∑ s, a s ^ (q - 1) * Real.sqrt (a s)) * M := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun s _ => ?_
    have := ha s
    gcongr
    exact hM s
  have hNr : 0 < (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) := Real.rpow_pos_of_pos hN _
  calc (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) * ∑ s, (a s ^ (q - 1) * Real.sqrt (a s)) *
        Real.sqrt (c s)
      ≤ (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) *
        ((∑ s, a s ^ (q - 1) * Real.sqrt (a s)) * M) := by
        gcongr
    _ ≤ (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) * (((Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * q)) *
        (∑ s, a s ^ q) ^ (1 - (1 : ℝ) / (2 * q))) * M) := by gcongr
    _ = (Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * q)) * M := by
        have : (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) * (∑ s, a s ^ q) ^ (1 - (1 : ℝ) / (2 * q)) =
            1 := by
          rw [← Real.rpow_add hN]; simp
        calc _ = ((∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) *
              (∑ s, a s ^ q) ^ (1 - (1 : ℝ) / (2 * q))) *
              ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * q)) * M) := by ring
          _ = _ := by rw [this, one_mul]


private lemma surr_hess_sum_le [Nonempty ι] {Λ : Type*} [Fintype Λ] (q : ℕ) (hq : 1 ≤ q)
    (a : ι → ℝ) (ha : ∀ s, 0 < a s) (b c : Λ → ι → ℝ)
    (hpos : ∀ l s t, 0 < surrQ a (b l) (c l) s t)
    (hb : ∀ l s, b l s ^ 2 ≤ a s * c l s) (hc : ∀ l s, 0 ≤ c l s) {G : ℝ}
    (hG : ∀ s, ∑ l, c l s ≤ G) :
    ∑ l, deriv (deriv (surrPhi q a (b l) (c l))) 0 ≤
      (2 * q - 1) * (Fintype.card ι : ℝ) ^ ((1 : ℝ) / q) * G /
        (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hN : 0 < ∑ s, a s ^ q := Finset.sum_pos (fun s _ => pow_pos (ha s) q) Finset.univ_nonempty
  have hG0 : 0 ≤ G := (Finset.sum_nonneg fun l _ => hc l (Classical.arbitrary ι)).trans
    (hG (Classical.arbitrary ι))
  have hNr : 0 < (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) := Real.rpow_pos_of_pos hN _
  have h1 : ∑ l, deriv (deriv (surrPhi q a (b l) (c l))) 0 ≤
      ∑ l, (2 * q - 1) * (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) * ∑ s, a s ^ (q - 1) * c l s := by
    refine Finset.sum_le_sum fun l _ => ?_
    have := surr_hess_le q hq a (b l) (c l) (hpos l) (hb l)
    simpa using this
  refine h1.trans ?_
  have hsum : ∑ l, ∑ s, a s ^ (q - 1) * c l s ≤ G * ∑ s, a s ^ (q - 1) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [← Finset.mul_sum]
    have := ha s
    calc a s ^ (q - 1) * ∑ l, c l s ≤ a s ^ (q - 1) * G := by gcongr; exact hG s
      _ = G * a s ^ (q - 1) := mul_comm _ _
  have hNN : (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) * (∑ s, a s ^ q) ^ (1 - (1 : ℝ) / q) =
      ((∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q)))⁻¹ := by
    rw [← Real.rpow_add hN, ← Real.rpow_neg hN.le]; congr 1; ring
  have hK : 0 ≤ (2 * (q : ℝ) - 1) * (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) := by
    have : (0 : ℝ) ≤ 2 * q - 1 := by linarith
    positivity
  calc ∑ l, (2 * (q : ℝ) - 1) * (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) *
        ∑ s, a s ^ (q - 1) * c l s
      = (2 * (q : ℝ) - 1) * (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) *
        ∑ l, ∑ s, a s ^ (q - 1) * c l s := (Finset.mul_sum _ _ _).symm
    _ ≤ (2 * (q : ℝ) - 1) * (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) *
          (G * ∑ s, a s ^ (q - 1)) := by
        gcongr
    _ ≤ (2 * (q : ℝ) - 1) * (∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q) - 1) *
        (G * ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / q) * (∑ s, a s ^ q) ^ (1 - (1 : ℝ) / q))) := by
        gcongr; exact surr_weight_le q hq a ha
    _ = (2 * (q : ℝ) - 1) * (Fintype.card ι : ℝ) ^ ((1 : ℝ) / q) * G *
          ((∑ s, a s ^ q) ^ ((1 : ℝ) / (2 * q)))⁻¹ := by
        rw [← hNN]; ring
    _ = _ := (div_eq_mul_inv _ _).symm

private lemma surr_gamma_sum_le [Nonempty ι] {Λ : Type*} [Fintype Λ] (q : ℕ) (hq : 1 ≤ q)
    (a : ι → ℝ) (ha : ∀ s, 0 < a s) (b c : Λ → ι → ℝ)
    (hpos : ∀ l s t, 0 < surrQ a (b l) (c l) s t)
    (hb : ∀ l s, b l s ^ 2 ≤ a s * c l s) (hc : ∀ l s, 0 ≤ c l s) {G : ℝ}
    (hG : ∀ s, ∑ l, c l s ≤ G) :
    ∑ l, (deriv (surrPhi q a (b l) (c l)) 0) ^ 2 ≤ (Fintype.card ι : ℝ) ^ ((1 : ℝ) / q) * G := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hN : 0 < ∑ s, a s ^ q := Finset.sum_pos (fun s _ => pow_pos (ha s) q) Finset.univ_nonempty
  have hG0 : 0 ≤ G := (Finset.sum_nonneg fun l _ => hc l (Classical.arbitrary ι)).trans
    (hG (Classical.arbitrary ι))
  set N := ∑ s, a s ^ q with hNdef
  set w : ι → ℝ := fun s => a s ^ (q - 1) * Real.sqrt (a s) with hw
  have hw0 : ∀ s, 0 ≤ w s := fun s => by have := ha s; simp only [hw]; positivity
  set W := ∑ s, w s with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun s _ => hw0 s
  have hW : W ≤ (Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * q)) * N ^ (1 - (1 : ℝ) / (2 * q)) :=
    surr_weight_sqrt_le q hq a ha
  have hNr : 0 < N ^ ((1 : ℝ) / (2 * q) - 1) := Real.rpow_pos_of_pos hN _
  -- per-direction bound
  have h1 : ∀ l, (deriv (surrPhi q a (b l) (c l)) 0) ^ 2 ≤
      (N ^ ((1 : ℝ) / (2 * q) - 1)) ^ 2 * (W * ∑ s, w s * c l s) := by
    intro l
    have hg := surr_grad_le q hq a (b l) (c l) (hpos l) (hb l)
    have hCS : (∑ s, w s * Real.sqrt (c l s)) ^ 2 ≤ W * ∑ s, w s * c l s := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ (fun s _ => hw0 s)
        (fun s _ => mul_nonneg (hw0 s) (hc l s)) fun s _ => ?_
      rw [mul_pow, Real.sq_sqrt (hc l s)]; nlinarith [hw0 s, hc l s]
    calc (deriv (surrPhi q a (b l) (c l)) 0) ^ 2 = |deriv (surrPhi q a (b l) (c l)) 0| ^ 2 :=
          (sq_abs _).symm
      _ ≤ (N ^ ((1 : ℝ) / (2 * q) - 1) * ∑ s, w s * Real.sqrt (c l s)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hg 2
      _ = (N ^ ((1 : ℝ) / (2 * q) - 1)) ^ 2 * (∑ s, w s * Real.sqrt (c l s)) ^ 2 := mul_pow _ _ _
      _ ≤ _ := by gcongr
  have h2 : ∑ l, (deriv (surrPhi q a (b l) (c l)) 0) ^ 2 ≤
      (N ^ ((1 : ℝ) / (2 * q) - 1)) ^ 2 * (W * (W * G)) := by
    refine (Finset.sum_le_sum fun l _ => h1 l).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    gcongr
    rw [Finset.sum_comm]
    calc ∑ s, ∑ l, w s * c l s = ∑ s, w s * ∑ l, c l s := by
          refine Finset.sum_congr rfl fun s _ => ?_; rw [Finset.mul_sum]
      _ ≤ ∑ s, w s * G := Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (hG s) (hw0 s)
      _ = W * G := by rw [Finset.sum_mul]
  have h3 : N ^ ((1 : ℝ) / (2 * q) - 1) * W ≤ (Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * q)) := by
    calc N ^ ((1 : ℝ) / (2 * q) - 1) * W
        ≤ N ^ ((1 : ℝ) / (2 * q) - 1) * ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * q)) *
          N ^ (1 - (1 : ℝ) / (2 * q))) := by gcongr
      _ = (N ^ ((1 : ℝ) / (2 * q) - 1) * N ^ (1 - (1 : ℝ) / (2 * q))) *
          (Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * q)) := by ring
      _ = _ := by rw [← Real.rpow_add hN]; simp
  have h4 : ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * q))) ^ 2 =
      (Fintype.card ι : ℝ) ^ ((1 : ℝ) / q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1; push_cast; field_simp
  calc ∑ l, (deriv (surrPhi q a (b l) (c l)) 0) ^ 2
      ≤ (N ^ ((1 : ℝ) / (2 * q) - 1)) ^ 2 * (W * (W * G)) := h2
    _ = (N ^ ((1 : ℝ) / (2 * q) - 1) * W) ^ 2 * G := by ring
    _ ≤ ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * q))) ^ 2 * G := by
        gcongr
    _ = _ := by rw [h4]

end Assembled

section Line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private lemma surr_hasDerivAt_line (y h : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => y + s • h) h t := by
  simpa using ((hasDerivAt_id t).smul_const h).const_add y

private lemma surr_fderiv_line {F : E → ℝ} (hF : Differentiable ℝ F) (y h : E) (t : ℝ) :
    fderiv ℝ F (y + t • h) h = deriv (fun s : ℝ => F (y + s • h)) t :=
  (((hF (y + t • h)).hasFDerivAt.comp_hasDerivAt t (surr_hasDerivAt_line y h t))).deriv.symm

private lemma surr_fderiv2_line {F : E → ℝ} (hF : ContDiff ℝ 2 F) (y h : E) :
    fderiv ℝ (fderiv ℝ F) y h h = deriv (deriv (fun s : ℝ => F (y + s • h))) 0 := by
  have hF1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hd : deriv (fun s : ℝ => F (y + s • h)) = fun t => fderiv ℝ F (y + t • h) h :=
    funext fun t => (surr_fderiv_line hF1 y h t).symm
  rw [hd]
  have hD : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) y) (y + (0 : ℝ) • h) := by
    simpa using (hD y).hasFDerivAt
  have h2 := h1.comp_hasDerivAt (0 : ℝ) (surr_hasDerivAt_line y h 0)
  have h3 := h2.clm_apply (hasDerivAt_const (0 : ℝ) h)
  simpa using h3.deriv.symm

end Line

section Bridge

variable {S : Type*}

/-- The base term `‖y_s‖²/env_s² + δ²` at the point `y`. -/
private def surrA (env : S → ℝ) (δ : ℝ) (y : S → ℂ) (s : S) : ℝ := ‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2

/-- The coefficient `⟨y_s, h_s⟩/env_s²` of `t` in the base term along direction `h`. -/
private def surrB (env : S → ℝ) (y h : S → ℂ) (s : S) : ℝ := inner ℝ (y s) (h s) / env s ^ 2

/-- The coefficient `‖h_s‖²/env_s²` of `t²` in the base term along direction `h`. -/
private def surrC (env : S → ℝ) (h : S → ℂ) (s : S) : ℝ := ‖h s‖ ^ 2 / env s ^ 2

private lemma surrQ_eq (env : S → ℝ) (henv : ∀ s, 0 < env s) (δ : ℝ) (y h : S → ℂ) (s : S) (t : ℝ) :
    surrQ (surrA env δ y) (surrB env y h) (surrC env h) s t =
      ‖(y + t • h) s‖ ^ 2 / env s ^ 2 + δ ^ 2 := by
  have := henv s
  simp only [surrQ, surrA, surrB, surrC, Pi.add_apply, Pi.smul_apply]
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp
  ring

private lemma surr_line_eq [Fintype S] (q : ℕ) (env : S → ℝ) (henv : ∀ s, 0 < env s) (δ : ℝ)
    (y h : S → ℂ)
    (t : ℝ) :
    lqSurr q env δ (y + t • h) = surrPhi q (surrA env δ y) (surrB env y h) (surrC env h) t := by
  unfold lqSurr surrPhi surrN
  simp only [surrQ_eq env henv δ y h]

private lemma surrA_pos (env : S → ℝ) (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ) (y : S → ℂ)
    (s : S) : 0 < surrA env δ y s := by
  have := henv s
  unfold surrA; positivity

private lemma surrQ_pos (env : S → ℝ) (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ)
    (y h : S → ℂ) (s : S) (t : ℝ) :
    0 < surrQ (surrA env δ y) (surrB env y h) (surrC env h) s t := by
  rw [surrQ_eq env henv]
  have := henv s
  positivity

private lemma surrC_nonneg (env : S → ℝ) (h : S → ℂ) (s : S) : 0 ≤ surrC env h s := by
  unfold surrC; positivity

private lemma surrC_sqrt (env : S → ℝ) (henv : ∀ s, 0 < env s) (h : S → ℂ) (s : S) :
    Real.sqrt (surrC env h s) = ‖h s‖ / env s := by
  have := henv s
  unfold surrC
  rw [← div_pow, Real.sqrt_sq (by positivity)]

private lemma surrB_sq_le (env : S → ℝ) (henv : ∀ s, 0 < env s) (δ : ℝ) (y h : S → ℂ) (s : S) :
    surrB env y h s ^ 2 ≤ surrA env δ y s * surrC env h s := by
  have hs := henv s
  have hi : inner ℝ (y s) (h s) ^ 2 ≤ ‖y s‖ ^ 2 * ‖h s‖ ^ 2 := by
    rw [← mul_pow, ← sq_abs (inner ℝ (y s) (h s))]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
  unfold surrB surrA surrC
  calc (inner ℝ (y s) (h s) / env s ^ 2) ^ 2 = inner ℝ (y s) (h s) ^ 2 / (env s ^ 2) ^ 2 :=
        div_pow _ _ _
    _ ≤ (‖y s‖ ^ 2 * ‖h s‖ ^ 2) / (env s ^ 2) ^ 2 := by gcongr
    _ = (‖y s‖ ^ 2 / env s ^ 2) * (‖h s‖ ^ 2 / env s ^ 2) := by field_simp
    _ ≤ (‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2) * (‖h s‖ ^ 2 / env s ^ 2) := by
        have : 0 ≤ ‖h s‖ ^ 2 / env s ^ 2 := by positivity
        nlinarith [sq_nonneg δ]

end Bridge

private lemma surr_eq_zero_of_isEmpty {S : Type*} [Fintype S] [IsEmpty S] {q : ℕ} (hq : 1 ≤ q)
    (env : S → ℝ) (δ : ℝ) : lqSurr q env δ = fun _ => 0 := by
  funext y
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [lqSurr, Finset.univ_eq_empty, Finset.sum_empty]
  exact Real.zero_rpow (by positivity)

theorem lqSurr_contDiff {S : Type*} [Fintype S] {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ}
    (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ 2 (lqSurr q env δ) := by
  rcases isEmpty_or_nonempty S with hS | hS
  · rw [surr_eq_zero_of_isEmpty hq]; exact contDiff_const
  · unfold lqSurr
    have hN : ContDiff ℝ 2 (fun y : S → ℂ => ∑ s, (‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2) ^ q) := by
      refine ContDiff.sum fun s _ => ?_
      have h1 : ContDiff ℝ 2 (fun y : S → ℂ => y s) := contDiff_apply ℝ (fun _ : S => ℂ) s
      exact ((((contDiff_norm_sq ℝ).comp h1).div_const _).add contDiff_const).pow q
    refine hN.rpow_const_of_ne fun y => ?_
    exact (Finset.sum_pos (fun s _ => by have := henv s; positivity)
      Finset.univ_nonempty).ne'

private lemma surr_pow_rpow_inv {x : ℝ} (hx : 0 ≤ x) {q : ℕ} (hq : 1 ≤ q) :
    (x ^ (2 * q)) ^ ((1 : ℝ) / (2 * q)) = x := by
  have h := Real.pow_rpow_inv_natCast hx (n := 2 * q) (by omega)
  convert h using 3
  push_cast
  rw [one_div]

private lemma surr_le_iSup {S : Type*} [Finite S] (f : S → ℝ) (s : S) : f s ≤ ⨆ s, f s :=
  le_ciSup (Set.finite_range f).bddAbove s

theorem lqSurr_label_le {S : Type*} [Fintype S] {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ}
    (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ) (y : S → ℂ) (s : S) :
    ‖y s‖ / env s ≤ lqSurr q env δ y := by
  have hs := henv s
  have hp : 0 ≤ ‖y s‖ / env s := by positivity
  have h1 : (‖y s‖ / env s) ^ (2 * q) ≤ ∑ s', (‖y s'‖ ^ 2 / env s' ^ 2 + δ ^ 2) ^ q := by
    calc (‖y s‖ / env s) ^ (2 * q) = (‖y s‖ ^ 2 / env s ^ 2) ^ q := by
          rw [pow_mul, div_pow]
      _ ≤ (‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2) ^ q := by
          gcongr; exact le_add_of_nonneg_right (sq_nonneg δ)
      _ ≤ _ := Finset.single_le_sum (f := fun s' => (‖y s'‖ ^ 2 / env s' ^ 2 + δ ^ 2) ^ q)
          (fun s' _ => by have := henv s'; positivity) (Finset.mem_univ s)
  calc ‖y s‖ / env s = ((‖y s‖ / env s) ^ (2 * q)) ^ ((1 : ℝ) / (2 * q)) :=
        (surr_pow_rpow_inv hp hq).symm
    _ ≤ _ := by
        unfold lqSurr
        gcongr

theorem lqSurr_le {S : Type*} [Fintype S] {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ}
    (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ) (y : S → ℂ) :
    lqSurr q env δ y ≤
      (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) * ((⨆ s, ‖y s‖ / env s) + δ) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hM0 : 0 ≤ ⨆ s, ‖y s‖ / env s := Real.iSup_nonneg fun s => by have := henv s; positivity
  rcases isEmpty_or_nonempty S with hS | hS
  · rw [surr_eq_zero_of_isEmpty hq]
    positivity
  · set M := ⨆ s, ‖y s‖ / env s with hM
    have hle : ∀ s, ‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2 ≤ (M + δ) ^ 2 := fun s => by
      have hs := henv s
      have h1 : ‖y s‖ / env s ≤ M := surr_le_iSup (fun s => ‖y s‖ / env s) s
      have h2 : 0 ≤ ‖y s‖ / env s := by positivity
      rw [← div_pow]
      nlinarith [mul_nonneg hM0 hδ.le]
    have hN : ∑ s, (‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2) ^ q ≤
        (Fintype.card S : ℝ) * (M + δ) ^ (2 * q) := by
      calc _ ≤ ∑ _s : S, ((M + δ) ^ 2) ^ q := Finset.sum_le_sum fun s _ => by
            have hs := henv s
            gcongr
            exact hle s
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pow_mul]
    unfold lqSurr
    calc _ ≤ ((Fintype.card S : ℝ) * (M + δ) ^ (2 * q)) ^ ((1 : ℝ) / (2 * q)) := by
          gcongr
      _ = _ := by
          rw [Real.mul_rpow (Nat.cast_nonneg _) (by positivity),
            surr_pow_rpow_inv (by positivity) hq]

private lemma surr_fderiv_eq {S : Type*} [Fintype S] {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ}
    (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ) (y h : S → ℂ) :
    fderiv ℝ (lqSurr q env δ) y h =
      deriv (surrPhi q (surrA env δ y) (surrB env y h) (surrC env h)) 0 := by
  have hX : Differentiable ℝ (lqSurr q env δ) :=
    (lqSurr_contDiff hq henv hδ).differentiable (by norm_num)
  have h1 := surr_fderiv_line hX y h 0
  simp only [zero_smul, add_zero] at h1
  rw [h1]
  congr 1
  funext t
  exact surr_line_eq q env henv δ y h t

private lemma surr_fderiv2_eq {S : Type*} [Fintype S] {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ}
    (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ) (y h : S → ℂ) :
    fderiv ℝ (fderiv ℝ (lqSurr q env δ)) y h h =
      deriv (deriv (surrPhi q (surrA env δ y) (surrB env y h) (surrC env h))) 0 := by
  rw [surr_fderiv2_line (lqSurr_contDiff hq henv hδ) y h]
  congr 2
  funext t
  exact surr_line_eq q env henv δ y h t

theorem lqSurr_fderiv_le {S : Type*} [Fintype S] {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ}
    (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ) (y h : S → ℂ) :
    |fderiv ℝ (lqSurr q env δ) y h| ≤
      (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) * ⨆ s, ‖h s‖ / env s := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  rcases isEmpty_or_nonempty S with hS | hS
  · rw [surr_eq_zero_of_isEmpty hq]
    simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, abs_zero]
    have : 0 ≤ ⨆ s, ‖h s‖ / env s := Real.iSup_nonneg fun s => by have := henv s; positivity
    positivity
  · rw [surr_fderiv_eq hq henv hδ]
    refine surr_grad_sup_le q hq _ _ _ (fun s t => surrQ_pos env henv hδ y h s t)
      (surrB_sq_le env henv δ y h) fun s => ?_
    rw [surrC_sqrt env henv]
    exact surr_le_iSup (fun s => ‖h s‖ / env s) s

section Convex

private lemma surr_mix_le (δ p p' : ℝ) :
    p * p' + δ ^ 2 ≤ Real.sqrt (p ^ 2 + δ ^ 2) * Real.sqrt (p' ^ 2 + δ ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  nlinarith [sq_nonneg (δ * (p - p'))]

/-- Convexity of `z ↦ √(‖z‖²/e² + δ²)` on `ℂ`. -/
private lemma surr_sqrt_convex (e δ : ℝ) (he : 0 < e) (z z' : ℂ) {c₁ c₂ : ℝ} (h₁ : 0 ≤ c₁)
    (h₂ : 0 ≤ c₂) (h : c₁ + c₂ = 1) :
    Real.sqrt (‖c₁ • z + c₂ • z'‖ ^ 2 / e ^ 2 + δ ^ 2) ≤
      c₁ * Real.sqrt (‖z‖ ^ 2 / e ^ 2 + δ ^ 2) + c₂ * Real.sqrt (‖z'‖ ^ 2 / e ^ 2 + δ ^ 2) := by
  set p := ‖z‖ / e with hp
  set p' := ‖z'‖ / e with hp'
  have hp0 : 0 ≤ p := by positivity
  have hp'0 : 0 ≤ p' := by positivity
  have e1 : ‖z‖ ^ 2 / e ^ 2 = p ^ 2 := by rw [hp, div_pow]
  have e2 : ‖z'‖ ^ 2 / e ^ 2 = p' ^ 2 := by rw [hp', div_pow]
  have hr : ‖c₁ • z + c₂ • z'‖ / e ≤ c₁ * p + c₂ * p' := by
    rw [div_le_iff₀ he]
    calc ‖c₁ • z + c₂ • z'‖ ≤ ‖c₁ • z‖ + ‖c₂ • z'‖ := norm_add_le _ _
      _ = c₁ * ‖z‖ + c₂ * ‖z'‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h₁,
            abs_of_nonneg h₂]
      _ = (c₁ * p + c₂ * p') * e := by rw [hp, hp']; field_simp
  have hr0 : 0 ≤ ‖c₁ • z + c₂ • z'‖ / e := by positivity
  rw [e1, e2, ← div_pow]
  have hA := Real.sq_sqrt (by positivity : 0 ≤ p ^ 2 + δ ^ 2)
  have hB := Real.sq_sqrt (by positivity : 0 ≤ p' ^ 2 + δ ^ 2)
  have hAB := surr_mix_le δ p p'
  rw [Real.sqrt_le_left (by positivity)]
  have hm : (‖c₁ • z + c₂ • z'‖ / e) ^ 2 ≤ (c₁ * p + c₂ * p') ^ 2 := pow_le_pow_left₀ hr0 hr 2
  have hc : c₂ = 1 - c₁ := by linarith
  set A := Real.sqrt (p ^ 2 + δ ^ 2)
  set B := Real.sqrt (p' ^ 2 + δ ^ 2)
  have : (c₁ * p + c₂ * p') ^ 2 + δ ^ 2 ≤ (c₁ * A + c₂ * B) ^ 2 := by
    have h3 : 0 ≤ c₁ * c₂ := mul_nonneg h₁ h₂
    have key : (c₁ * A + c₂ * B) ^ 2 - ((c₁ * p + c₂ * p') ^ 2 + δ ^ 2) =
        2 * (c₁ * c₂) * (A * B - (p * p' + δ ^ 2)) := by
      linear_combination c₁ ^ 2 * hA + c₂ ^ 2 * hB + δ ^ 2 * (c₁ + c₂ + 1) * h
    have : 0 ≤ 2 * (c₁ * c₂) * (A * B - (p * p' + δ ^ 2)) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  linarith

end Convex

private lemma surr_smul_Lp {S : Type*} [Fintype S] (f : S → ℝ) (hf : ∀ s, 0 ≤ f s) {c : ℝ}
    (hc : 0 ≤ c) {P : ℝ} (hP : 0 < P) :
    (∑ s, (c * f s) ^ P) ^ (1 / P) = c * (∑ s, f s ^ P) ^ (1 / P) := by
  simp only [Real.mul_rpow hc (hf _)]
  rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg hc _)
    (Finset.sum_nonneg fun s _ => Real.rpow_nonneg (hf s) _), ← Real.rpow_mul hc,
    mul_one_div_cancel hP.ne', Real.rpow_one]

private lemma surr_eq_Lp {S : Type*} [Fintype S] {q : ℕ} (env : S → ℝ) (δ : ℝ) (y : S → ℂ) :
    lqSurr q env δ y = (∑ s, (Real.sqrt (‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2)) ^ ((2 * q : ℕ) : ℝ)) ^
      (1 / ((2 * q : ℕ) : ℝ)) := by
  unfold lqSurr
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [Real.rpow_natCast, pow_mul, Real.sq_sqrt (by positivity)]
  · push_cast; rfl

theorem lqSurr_convexOn {S : Type*} [Fintype S] {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ}
    (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ) : ConvexOn ℝ Set.univ (lqSurr q env δ) := by
  rcases isEmpty_or_nonempty S with hS | hS
  · rw [surr_eq_zero_of_isEmpty hq]; exact convexOn_const _ convex_univ
  · refine ⟨convex_univ, fun y _ y' _ c₁ c₂ h₁ h₂ h => ?_⟩
    have hP : (1 : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * q)
    have hP0 : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by linarith
    set v : (S → ℂ) → S → ℝ := fun z s => Real.sqrt (‖z s‖ ^ 2 / env s ^ 2 + δ ^ 2) with hv
    have hv0 : ∀ z s, 0 ≤ v z s := fun z s => Real.sqrt_nonneg _
    have hconv : ∀ s, v (c₁ • y + c₂ • y') s ≤ c₁ * v y s + c₂ * v y' s := fun s => by
      simpa [hv] using surr_sqrt_convex (env s) δ (henv s) (y s) (y' s) h₁ h₂ h
    simp only [surr_eq_Lp env δ, smul_eq_mul]
    calc (∑ s, (v (c₁ • y + c₂ • y') s) ^ ((2 * q : ℕ) : ℝ)) ^ (1 / ((2 * q : ℕ) : ℝ))
        ≤ (∑ s, (c₁ * v y s + c₂ * v y' s) ^ ((2 * q : ℕ) : ℝ)) ^ (1 / ((2 * q : ℕ) : ℝ)) := by
          gcongr with s _
          exact hconv s
      _ ≤ (∑ s, (c₁ * v y s) ^ ((2 * q : ℕ) : ℝ)) ^ (1 / ((2 * q : ℕ) : ℝ)) +
          (∑ s, (c₂ * v y' s) ^ ((2 * q : ℕ) : ℝ)) ^ (1 / ((2 * q : ℕ) : ℝ)) :=
          Real.Lp_add_le_of_nonneg Finset.univ hP (fun s _ => mul_nonneg h₁ (hv0 y s))
            (fun s _ => mul_nonneg h₂ (hv0 y' s))
      _ = _ := by
          rw [surr_smul_Lp (v y) (hv0 y) h₁ hP0, surr_smul_Lp (v y') (hv0 y') h₂ hP0]

theorem lqSurr_hessian_le {S : Type*} [Fintype S] {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ}
    (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ) {Λ : Type*} [Fintype Λ] (h : Λ → S → ℂ)
    (y : S → ℂ) :
    ∑ l, fderiv ℝ (fderiv ℝ (lqSurr q env δ)) y (h l) (h l) ≤
      2 * q * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) *
        (⨆ s, ∑ l, ‖h l s‖ ^ 2 / env s ^ 2) / lqSurr q env δ y := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  rcases isEmpty_or_nonempty S with hS | hS
  · rw [surr_eq_zero_of_isEmpty hq]
    simp
  · have hG0 : 0 ≤ ⨆ s, ∑ l, ‖h l s‖ ^ 2 / env s ^ 2 :=
      Real.iSup_nonneg fun s => Finset.sum_nonneg fun l _ => by have := henv s; positivity
    have hN : 0 < ∑ s, (‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2) ^ q :=
      Finset.sum_pos (fun s _ => by have := henv s; positivity) Finset.univ_nonempty
    have hX : 0 < lqSurr q env δ y := Real.rpow_pos_of_pos hN _
    have key := surr_hess_sum_le q hq (surrA env δ y) (surrA_pos env henv hδ y)
      (fun l => surrB env y (h l)) (fun l => surrC env (h l))
      (fun l s t => surrQ_pos env henv hδ y (h l) s t)
      (fun l s => surrB_sq_le env henv δ y (h l) s) (fun l s => surrC_nonneg env (h l) s)
      (G := ⨆ s, ∑ l, ‖h l s‖ ^ 2 / env s ^ 2)
      (fun s => surr_le_iSup (fun s => ∑ l, ‖h l s‖ ^ 2 / env s ^ 2) s)
    simp only [surr_fderiv2_eq hq henv hδ]
    have key' : _ ≤ ((2 * (q : ℝ) - 1) * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) *
        ⨆ s, ∑ l, ‖h l s‖ ^ 2 / env s ^ 2) / lqSurr q env δ y := key
    refine key'.trans ?_
    apply div_le_div_of_nonneg_right _ hX.le
    have : 0 ≤ (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * ⨆ s, ∑ l, ‖h l s‖ ^ 2 / env s ^ 2 := by
      positivity
    nlinarith

theorem lqSurr_gamma_le {S : Type*} [Fintype S] {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ}
    (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ) {Λ : Type*} [Fintype Λ] (h : Λ → S → ℂ)
    (y : S → ℂ) :
    ∑ l, (fderiv ℝ (lqSurr q env δ) y (h l)) ^ 2 ≤
      (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * ⨆ s, ∑ l, ‖h l s‖ ^ 2 / env s ^ 2 := by
  have hG0 : 0 ≤ ⨆ s, ∑ l, ‖h l s‖ ^ 2 / env s ^ 2 :=
    Real.iSup_nonneg fun s => Finset.sum_nonneg fun l _ => by have := henv s; positivity
  rcases isEmpty_or_nonempty S with hS | hS
  · rw [surr_eq_zero_of_isEmpty hq]
    simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  · simp only [surr_fderiv_eq hq henv hδ]
    exact surr_gamma_sum_le q hq (surrA env δ y) (surrA_pos env henv hδ y)
      (fun l => surrB env y (h l)) (fun l => surrC env (h l))
      (fun l s t => surrQ_pos env henv hδ y (h l) s t)
      (fun l s => surrB_sq_le env henv δ y (h l) s) (fun l s => surrC_nonneg env (h l) s)
      (G := ⨆ s, ∑ l, ‖h l s‖ ^ 2 / env s ^ 2)
      (fun s => surr_le_iSup (fun s => ∑ l, ‖h l s‖ ^ 2 / env s ^ 2) s)

theorem card_rpow_le_of_q (n : ℕ) (hn : 1 ≤ n) {δq : ℝ} (hδq : 0 < δq) {q : ℕ} (hq1 : 1 ≤ q)
    (hq : Real.log n / (2 * Real.log (1 + δq)) ≤ q) : (n : ℝ) ^ ((1 : ℝ) / (2 * q)) ≤ 1 + δq := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log (1 + δq) := Real.log_pos (by linarith)
  have h1 : Real.log n ≤ q * (2 * Real.log (1 + δq)) := (div_le_iff₀ (by positivity)).mp hq
  rw [Real.rpow_def_of_pos hnpos]
  calc Real.exp (Real.log n * (1 / (2 * q))) ≤ Real.exp (Real.log (1 + δq)) := by
        apply Real.exp_le_exp.mpr
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        linarith
    _ = 1 + δq := Real.exp_log (by linarith)

end LSBA
