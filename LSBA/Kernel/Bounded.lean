import LSBA.Kernel.Algebra
import LSBA.Kernel.LineKernel
import LSBA.Dyson.Perturb
import LSBA.Dyson.FiniteRegular
import LSBA.Kernel.Root

/-!
# Bounded coupling

Lemma A.5 [ba:lem:kernels] (the value at zero, the exponential profile, the weighted rows (A.24)
[ba:eq:weighted-rows], the coercivity (A.25) [ba:eq:coercivity] and the inverse average (A.26)
[ba:eq:inverse-average]), (A.29) [gc:eq:gradient] of Lemma A.7 [da:lem:transport-refinements] and
Lemma 6.1 [da:lem:scales-propagators] at bounded coupling, uniformly in `0 ≤ g ≤ C`, `|E| ≤ B₀`,
`L ≥ L₀`.
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

section BdCyc

open Fin.CommRing

variable {L : ℕ}

/-- The cyclic size `‖y‖_L` of `y ∈ ℤ_L`. -/
private def bdD (y : Fin L) : ℕ := min y.val (-y).val

private lemma bd_cycDist_eq [NeZero L] (a c : Fin L) : cycDist a c = bdD (c - a) := by
  have ha := a.isLt
  have hc := c.isLt
  unfold bdD cycDist
  rw [neg_sub, Fin.sub_def, Fin.sub_def, min_comm]
  simp only
  congr 2 <;> omega

private lemma bdD_neg [NeZero L] (y : Fin L) : bdD (-y) = bdD y := by
  unfold bdD; rw [neg_neg, min_comm]

private lemma bdD_le_val (y : Fin L) : bdD y ≤ y.val := min_le_left _ _

private lemma bdD_natCast_le [NeZero L] (n : ℕ) : bdD (n : Fin L) ≤ n :=
  (bdD_le_val _).trans (by rw [Fin.val_natCast]; exact Nat.mod_le _ _)

private lemma bdD_intCast_le [NeZero L] (z : ℤ) : bdD (z : Fin L) ≤ z.natAbs := by
  rcases Int.natAbs_eq z with h | h
  · rw [h, Int.cast_natCast]; exact bdD_natCast_le (L := L) _
  · rw [h, Int.cast_neg, Int.cast_natCast, bdD_neg, Int.natAbs_neg, Int.natAbs_natCast]
    exact bdD_natCast_le (L := L) _

private lemma bdD_lift [NeZero L] (y : Fin L) : ∃ z : ℤ, (z : Fin L) = y ∧ z.natAbs = bdD y := by
  by_cases h : y.val ≤ (-y).val
  · refine ⟨(y.val : ℤ), by rw [Int.cast_natCast, Fin.cast_val_eq_self], ?_⟩
    rw [Int.natAbs_natCast]; unfold bdD; exact (min_eq_left h).symm
  · refine ⟨-((-y).val : ℤ), by rw [Int.cast_neg, Int.cast_natCast, Fin.cast_val_eq_self (-y),
      neg_neg], ?_⟩
    rw [Int.natAbs_neg, Int.natAbs_natCast]; unfold bdD; exact (min_eq_right (by omega)).symm

private lemma bdD_add_le [NeZero L] (x y : Fin L) : bdD (x + y) ≤ bdD x + bdD y := by
  obtain ⟨u, hu, hu'⟩ := bdD_lift x
  obtain ⟨v, hv, hv'⟩ := bdD_lift y
  have := bdD_intCast_le (L := L) (u + v)
  rw [Int.cast_add, hu, hv] at this
  have := Int.natAbs_add_le u v
  omega

private lemma bdD_zero [NeZero L] : bdD (0 : Fin L) = 0 := by simp [bdD]

private lemma bdD_eq_zero [NeZero L] {y : Fin L} : bdD y = 0 ↔ y = 0 := by
  constructor
  · intro h
    unfold bdD at h
    rcases Nat.min_eq_zero_iff.mp h with h | h
    · exact Fin.ext h
    · have : -y = 0 := Fin.ext h
      simpa using this
  · rintro rfl; exact bdD_zero

private lemma bdD_two_mul_le (y : Fin L) : 2 * bdD y ≤ L := by
  have hy := y.isLt
  unfold bdD
  rw [Fin.neg_def]
  simp only
  by_cases h0 : y.val = 0
  · simp [h0]
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

private lemma bdD_val_cases [NeZero L] (y : Fin L) : y.val = bdD y ∨ y.val + bdD y = L := by
  have hy := y.isLt
  unfold bdD
  rw [Fin.neg_def]
  simp only
  by_cases h0 : y.val = 0
  · left; simp [h0]
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

private lemma bd_cycDist_comm [NeZero L] (a c : Fin L) : cycDist a c = cycDist c a := by
  rw [bd_cycDist_eq, bd_cycDist_eq, ← neg_sub, bdD_neg]

lemma bd_cycDist_tri [NeZero L] (a b c : Fin L) : cycDist a c ≤ cycDist a b + cycDist b c :=
    by
  rw [bd_cycDist_eq, bd_cycDist_eq, bd_cycDist_eq]
  have : c - a = (b - a) + (c - b) := by abel
  rw [this]; exact bdD_add_le _ _

private lemma bd_cycDist_self [NeZero L] (a : Fin L) : cycDist a a = 0 := by
  rw [bd_cycDist_eq, sub_self, bdD_zero]

private lemma bd_cycDist_half [NeZero L] (a c : Fin L) : 2 * cycDist a c ≤ L := by
  rw [bd_cycDist_eq]; exact bdD_two_mul_le _

/-- The reflection identity: `cosh(μ‖x+y‖) + cosh(μ‖x-y‖) ≤ 2 cosh(μ‖x‖) cosh(μ‖y‖)`. -/
private lemma bd_cosh_pair [NeZero L] (μ : ℝ) (hμ : 0 ≤ μ) (x y : Fin L) :
    Real.cosh (μ * bdD (x + y)) + Real.cosh (μ * bdD (x - y)) ≤
      2 * Real.cosh (μ * bdD x) * Real.cosh (μ * bdD y) := by
  obtain ⟨u, hu, hu'⟩ := bdD_lift x
  obtain ⟨v, hv, hv'⟩ := bdD_lift y
  have h1 := bdD_intCast_le (L := L) (u + v)
  have h2 := bdD_intCast_le (L := L) (u - v)
  rw [Int.cast_add, hu, hv] at h1
  rw [Int.cast_sub, hu, hv] at h2
  have e1 : Real.cosh (μ * bdD (x + y)) ≤ Real.cosh (μ * ((u : ℝ) + v)) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg hμ, abs_of_nonneg (by positivity)]
    gcongr
    have : ((u + v).natAbs : ℝ) = |(u : ℝ) + v| := by
      rw [Nat.cast_natAbs]; push_cast; rfl
    rw [← this]; exact_mod_cast h1
  have e2 : Real.cosh (μ * bdD (x - y)) ≤ Real.cosh (μ * ((u : ℝ) - v)) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg hμ, abs_of_nonneg (by positivity)]
    gcongr
    have : ((u - v).natAbs : ℝ) = |(u : ℝ) - v| := by
      rw [Nat.cast_natAbs]; push_cast; rfl
    rw [← this]; exact_mod_cast h2
  have e3 : Real.cosh (μ * bdD x) = Real.cosh (μ * u) := by
    have : ((bdD x : ℕ) : ℝ) = |(u : ℝ)| := by rw [← hu', Nat.cast_natAbs, Int.cast_abs]
    rw [this, show μ * |(u : ℝ)| = |μ * u| by rw [abs_mul, abs_of_nonneg hμ], Real.cosh_abs]
  have e4 : Real.cosh (μ * bdD y) = Real.cosh (μ * v) := by
    have : ((bdD y : ℕ) : ℝ) = |(v : ℝ)| := by rw [← hv', Nat.cast_natAbs, Int.cast_abs]
    rw [this, show μ * |(v : ℝ)| = |μ * v| by rw [abs_mul, abs_of_nonneg hμ], Real.cosh_abs]
  rw [e3, e4]
  have : Real.cosh (μ * ((u : ℝ) + v)) + Real.cosh (μ * ((u : ℝ) - v)) =
      2 * Real.cosh (μ * u) * Real.cosh (μ * v) := by
    rw [mul_add, mul_sub, Real.cosh_add, Real.cosh_sub]; ring
  linarith

/-- Sums over a row of a function of `c - a`. -/
private lemma bd_sum_sub [NeZero L] {M : Type*} [AddCommMonoid M] (a : Fin L) (f : Fin L → M) :
    ∑ c, f (c - a) = ∑ y, f y :=
  Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)

end BdCyc

/-! ### Discrete Fourier analysis of circulant kernels -/

section BdFourier

variable {L : ℕ}

/-- `ζ = e^{2πi/L}`. -/
private def bdZ (L : ℕ) : ℂ := Complex.exp (2 * π * I / L)

private lemma bdZ_ne_zero (L : ℕ) : bdZ L ≠ 0 := Complex.exp_ne_zero _

private lemma bdZ_prim (hL : 1 ≤ L) : IsPrimitiveRoot (bdZ L) L :=
  Complex.isPrimitiveRoot_exp L (by omega)

private lemma bdZ_pow (L n : ℕ) :
    bdZ L ^ n =
      ((Real.cos (2 * π * n / L) : ℝ) : ℂ) + ((Real.sin (2 * π * n / L) : ℝ) : ℂ) * I := by
  rw [bdZ, ← Complex.exp_nat_mul]
  have : (n : ℂ) * (2 * π * I / L) = ((2 * π * n / L : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma bdZ_norm (L n : ℕ) : ‖bdZ L ^ n‖ = 1 := by
  rw [bdZ, ← Complex.exp_nat_mul]
  have : (n : ℂ) * (2 * π * I / L) = ((2 * π * n / L : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private lemma bdZ_inv_norm (L n : ℕ) : ‖(bdZ L)⁻¹ ^ n‖ = 1 := by
  rw [inv_pow, norm_inv, bdZ_norm, inv_one]

private lemma bdZ_pow_mod (hL : 1 ≤ L) (n : ℕ) : bdZ L ^ n = bdZ L ^ (n % L) := by
  conv_lhs => rw [← Nat.div_add_mod n L, pow_add, pow_mul, (bdZ_prim hL).pow_eq_one, one_pow,
    one_mul]

/-- `ζ^{kx} ζ^{-ka} = e^{2πik(x-a)/L}`, real part `cos(2πk(x-a)/L)`. -/
private lemma bdZ_re (L k x a : ℕ) :
    (bdZ L ^ (k * x) * (bdZ L)⁻¹ ^ (k * a)).re = Real.cos (2 * π * k * ((x : ℝ) - a) / L) := by
  rw [bdZ, inv_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_neg,
    ← Complex.exp_add]
  have : ((k * x : ℕ) : ℂ) * (2 * π * I / L) + -(((k * a : ℕ) : ℂ) * (2 * π * I / L)) =
      ((2 * π * k * ((x : ℝ) - a) / L : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

/-- Orthogonality `Σ_k ζ^{ka} ζ^{-kc} = L δ_{ac}`. -/
private lemma bdZ_orth (hL : 1 ≤ L) (a c : Fin L) :
    ∑ k : Fin L, bdZ L ^ (k.val * a.val) * (bdZ L)⁻¹ ^ (k.val * c.val) =
      if a = c then (L : ℂ) else 0 := by
  have hp := bdZ_prim hL
  have hz := bdZ_ne_zero L
  set x := bdZ L ^ a.val * (bdZ L)⁻¹ ^ c.val with hx
  have hk : ∀ k : Fin L,
      bdZ L ^ (k.val * a.val) * (bdZ L)⁻¹ ^ (k.val * c.val) = x ^ k.val := by
    intro k
    rw [hx, mul_pow, ← pow_mul, ← pow_mul, mul_comm a.val, mul_comm c.val]
  simp_rw [hk]
  rw [Fin.sum_univ_eq_sum_range (fun i => x ^ i) L]
  split_ifs with hac
  · subst hac
    have : x = 1 := by rw [hx, ← mul_pow, mul_inv_cancel₀ hz, one_pow]
    simp [this]
  · have hx1 : x ≠ 1 := by
      intro h
      apply hac
      have h' : bdZ L ^ a.val = bdZ L ^ c.val := by
        rw [eq_inv_of_mul_eq_one_left h, inv_pow, inv_inv]
      exact Fin.ext (hp.pow_inj a.isLt c.isLt h')
    have hxL : x ^ L = 1 := by
      rw [hx, mul_pow, ← pow_mul, ← pow_mul, mul_comm a.val L, mul_comm c.val L, pow_mul,
        pow_mul, inv_pow, hp.pow_eq_one, inv_one, one_pow, one_pow, one_mul]
    rw [geom_sum_eq hx1, hxL, sub_self, zero_div]

/-- The vectors `(ζ^{kc})_c` are eigenvectors of the real matrix `X`, with eigenvalues `μ k`. -/
private def BdEig (X : Matrix (Fin L) (Fin L) ℝ) (μ : Fin L → ℂ) : Prop :=
  ∀ k a : Fin L, ∑ c, (X a c : ℂ) * bdZ L ^ (k.val * c.val) = μ k * bdZ L ^ (k.val * a.val)

/-- Spectral formula for the entries. -/
private lemma bdEig_entry (hL : 1 ≤ L) {X : Matrix (Fin L) (Fin L) ℝ} {μ : Fin L → ℂ}
    (hX : BdEig X μ) (a b : Fin L) :
    (X a b : ℂ) = (L : ℂ)⁻¹ * ∑ k, μ k * bdZ L ^ (k.val * a.val) * (bdZ L)⁻¹ ^ (k.val * b.val) := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  have h1 : ∀ k : Fin L, μ k * bdZ L ^ (k.val * a.val) * (bdZ L)⁻¹ ^ (k.val * b.val) =
      ∑ c, (X a c : ℂ) * (bdZ L ^ (k.val * c.val) * (bdZ L)⁻¹ ^ (k.val * b.val)) := by
    intro k
    rw [← hX k a, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  have h : ∑ k, μ k * bdZ L ^ (k.val * a.val) * (bdZ L)⁻¹ ^ (k.val * b.val) =
      L * (X a b : ℂ) := by
    rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, bdZ_orth hL]
    simp [mul_comm]
  rw [h, ← mul_assoc, inv_mul_cancel₀ hL', one_mul]

/-- Entries are bounded by the average of the absolute eigenvalues. -/
private lemma bdEig_abs_le (hL : 1 ≤ L) {X : Matrix (Fin L) (Fin L) ℝ} {μ : Fin L → ℂ}
    (hX : BdEig X μ) (a b : Fin L) : |X a b| ≤ (L : ℝ)⁻¹ * ∑ k, ‖μ k‖ := by
  have h := congrArg norm (bdEig_entry hL hX a b)
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  rw [h, norm_mul, norm_inv, Complex.norm_natCast]
  gcongr
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [norm_mul, norm_mul, bdZ_norm, bdZ_inv_norm, mul_one, mul_one]

/-- Diagonal entries are averages of the eigenvalues. -/
private lemma bdEig_diag (hL : 1 ≤ L) {X : Matrix (Fin L) (Fin L) ℝ} {μ : Fin L → ℂ}
    (hX : BdEig X μ) (a : Fin L) : (X a a : ℂ) = (L : ℂ)⁻¹ * ∑ k, μ k := by
  rw [bdEig_entry hL hX a a]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (bdZ_ne_zero L), one_pow, mul_one]

private lemma bdEig_one : BdEig (1 : Matrix (Fin L) (Fin L) ℝ) (fun _ => 1) := by
  intro k a
  simp [Matrix.one_apply, apply_ite]

private lemma bdEig_mul {X Y : Matrix (Fin L) (Fin L) ℝ} {μ ν : Fin L → ℂ} (hX : BdEig X μ)
    (hY : BdEig Y ν) : BdEig (X * Y) (fun k => μ k * ν k) := by
  intro k a
  have e : ∀ c, ((X * Y) a c : ℂ) * bdZ L ^ (k.val * c.val) =
      ∑ d, (X a d : ℂ) * ((Y d c : ℂ) * bdZ L ^ (k.val * c.val)) := by
    intro c
    rw [Matrix.mul_apply]; push_cast
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun d _ => by ring
  rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hY k]
  have e2 : ∀ d, (X a d : ℂ) * (ν k * bdZ L ^ (k.val * d.val)) =
      ν k * ((X a d : ℂ) * bdZ L ^ (k.val * d.val)) := fun d => by ring
  simp_rw [e2, ← Finset.mul_sum, hX k a]
  ring

private lemma bdEig_add {X Y : Matrix (Fin L) (Fin L) ℝ} {μ ν : Fin L → ℂ} (hX : BdEig X μ)
    (hY : BdEig Y ν) : BdEig (X + Y) (fun k => μ k + ν k) := by
  intro k a
  simp only [Matrix.add_apply]; push_cast
  simp_rw [add_mul, Finset.sum_add_distrib, hX k a, hY k a]

private lemma bdEig_smul {X : Matrix (Fin L) (Fin L) ℝ} {μ : Fin L → ℂ} (hX : BdEig X μ) (s : ℝ) :
    BdEig (s • X) (fun k => s * μ k) := by
  intro k a
  simp only [Matrix.smul_apply, smul_eq_mul]; push_cast
  simp_rw [mul_assoc, ← Finset.mul_sum, hX k a]

private lemma bdEig_pow {X : Matrix (Fin L) (Fin L) ℝ} {μ : Fin L → ℂ} (hX : BdEig X μ) (n : ℕ) :
    BdEig (X ^ n) (fun k => μ k ^ n) := by
  induction n with
  | zero => simpa using (bdEig_one (L := L))
  | succ n ih =>
    rw [pow_succ]
    have := bdEig_mul ih hX
    simpa [pow_succ] using this

private lemma bdEig_inv {X : Matrix (Fin L) (Fin L) ℝ} {μ : Fin L → ℂ} (hX : BdEig X μ)
    (hμ : ∀ k, μ k ≠ 0) (hinv : X⁻¹ * X = 1) : BdEig X⁻¹ (fun k => (μ k)⁻¹) := by
  have h := bdEig_mul (X := X⁻¹) (Y := X) (μ := fun _ => 0) (ν := μ)
  intro k a
  have hk : ∀ d, ((X⁻¹ * X) d a : ℂ) = (if d = a then 1 else 0) := by
    intro d; rw [hinv, Matrix.one_apply]; split_ifs <;> simp
  have e : ∑ c, ((X⁻¹) a c : ℂ) * (μ k * bdZ L ^ (k.val * c.val)) =
      bdZ L ^ (k.val * a.val) := by
    simp_rw [← hX k]
    have : ∀ c, ((X⁻¹) a c : ℂ) * ∑ d, (X c d : ℂ) * bdZ L ^ (k.val * d.val) =
        ∑ d, ((X⁻¹) a c : ℂ) * (X c d : ℂ) * bdZ L ^ (k.val * d.val) := by
      intro c; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
    simp_rw [this]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    have : ∀ d, ∑ c, ((X⁻¹) a c : ℂ) * (X c d : ℂ) = (if a = d then 1 else 0) := by
      intro d
      have := congrFun (congrFun hinv a) d
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      have := congrArg (fun r : ℝ => (r : ℂ)) this
      push_cast at this
      rw [this]; split_ifs <;> simp
    simp_rw [this]
    simp
  have e2 : ∑ c, ((X⁻¹) a c : ℂ) * bdZ L ^ (k.val * c.val) =
      (μ k)⁻¹ * ∑ c, ((X⁻¹) a c : ℂ) * (μ k * bdZ L ^ (k.val * c.val)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    field_simp [hμ k]
  rw [e2, e]

/-- Circulant matrices `X_{ac} = f(c - a)` are diagonalized by the vectors `(ζ^{kc})_c`. -/
private lemma bdEig_circ [NeZero L] (f : Fin L → ℝ) :
    BdEig (Matrix.of fun a c : Fin L => f (c - a))
      (fun k => ∑ y, (f y : ℂ) * bdZ L ^ (k.val * y.val)) := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  intro k a
  simp only [Matrix.of_apply]
  rw [← bd_sum_sub a (fun y => (f y : ℂ) * bdZ L ^ (k.val * y.val)), Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : bdZ L ^ (k.val * c.val) = bdZ L ^ (k.val * a.val) * bdZ L ^ (k.val * (c - a).val) := by
    rw [← pow_add, bdZ_pow_mod hL, bdZ_pow_mod hL (k.val * a.val + _), ← mul_add, Nat.mul_mod,
      Nat.mul_mod k.val (a.val + _)]
    congr 3
    rw [Fin.sub_def]; simp only
    have := a.isLt; have := c.isLt
    rw [Nat.add_mod_mod, show a.val + (L - a.val + c.val) = c.val + L by omega, Nat.add_mod_right]
  rw [this]; ring

end BdFourier

/-! ### The symbol of a symmetric circulant kernel -/

section BdSymbol

variable {L : ℕ}

/-- The symbol `Σ_y F(‖y‖) cos(2πk‖y‖/L)`. -/
private def bdSym (F : ℕ → ℝ) (L : ℕ) (k : Fin L) : ℝ :=
  ∑ y : Fin L, F (bdD y) * Real.cos (2 * π * k * bdD y / L)

/-- The circulant kernel `P_{ac} = F(‖c - a‖)`. -/
private def bdP (F : ℕ → ℝ) (L : ℕ) : Matrix (Fin L) (Fin L) ℝ :=
  Matrix.of fun a c => F (cycDist a c)

private lemma bd_cos_val [NeZero L] (k : ℕ) (y : Fin L) :
    Real.cos (2 * π * k * (y.val : ℕ) / L) = Real.cos (2 * π * k * bdD y / L) := by
  rcases bdD_val_cases y with h | h
  · rw [h]
  · have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    have e : 2 * π * k * ((y.val : ℕ) : ℝ) / L = k * (2 * π) - 2 * π * k * (bdD y : ℝ) / L := by
      have : ((y.val : ℕ) : ℝ) = L - bdD y := by
        rw [eq_sub_iff_add_eq]; exact_mod_cast h
      rw [this]; field_simp
    rw [e, Real.cos_nat_mul_two_pi_sub]

private lemma bd_sin_neg [NeZero L] (k : ℕ) (y : Fin L) :
    Real.sin (2 * π * k * ((-y).val : ℕ) / L) = -Real.sin (2 * π * k * (y.val : ℕ) / L) := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  by_cases hy : y = 0
  · subst hy; simp
  · have hv : ((-y).val : ℝ) = L - y.val := by
      have hyv : y.val ≠ 0 := fun h => hy (Fin.ext h)
      have := y.isLt
      rw [Fin.neg_def]; simp only
      rw [Nat.mod_eq_of_lt (by omega), Nat.cast_sub this.le]
    rw [hv, show 2 * π * k * ((L : ℝ) - y.val) / L = k * (2 * π) - 2 * π * k * (y.val : ℝ) / L by
      field_simp, Real.sin_nat_mul_two_pi_sub]

/-- The eigenvalues of `bdP F L` are the real numbers `bdSym F L k`. -/
private lemma bdEig_P [NeZero L] (F : ℕ → ℝ) :
    BdEig (bdP F L) (fun k => (bdSym F L k : ℂ)) := by
  have h := bdEig_circ (fun y : Fin L => F (bdD y))
  have e1 : bdP F L = Matrix.of fun a c : Fin L => F (bdD (c - a)) := by
    ext a c; simp [bdP, bd_cycDist_eq]
  rw [e1]
  convert h using 2 with k
  -- the eigenvalue is real
  have hsin : ∑ y : Fin L, F (bdD y) * Real.sin (2 * π * (k.val : ℕ) * (y.val : ℕ) / L) = 0 := by
    have h1 : ∑ y : Fin L, F (bdD y) * Real.sin (2 * π * (k.val : ℕ) * (y.val : ℕ) / L) =
        ∑ y : Fin L, F (bdD (-y)) * Real.sin (2 * π * (k.val : ℕ) * ((-y).val : ℕ) / L) :=
      (Fintype.sum_equiv (Equiv.neg (Fin L)) _ _ (fun _ => rfl)).symm
    have h2 : ∑ y : Fin L, F (bdD (-y)) * Real.sin (2 * π * (k.val : ℕ) * ((-y).val : ℕ) / L) =
        -∑ y : Fin L, F (bdD y) * Real.sin (2 * π * (k.val : ℕ) * (y.val : ℕ) / L) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [bdD_neg, bd_sin_neg]; ring
    linarith
  have e2 : ∀ y : Fin L, (F (bdD y) : ℂ) * bdZ L ^ (k.val * y.val) =
      ((F (bdD y) * Real.cos (2 * π * k * bdD y / L) : ℝ) : ℂ) +
        ((F (bdD y) * Real.sin (2 * π * (k.val : ℕ) * (y.val : ℕ) / L) : ℝ) : ℂ) * I := by
    intro y
    rw [bdZ_pow, ← bd_cos_val]
    push_cast; ring_nf
  rw [Finset.sum_congr rfl fun y _ => e2 y, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Complex.ofReal_sum, ← Complex.ofReal_sum, hsin]
  simp [bdSym]

/-- `kerSymbol` of the circulant kernel is `bdSym`. -/
private lemma bd_kerSymbol [NeZero L] (F : ℕ → ℝ) (k : Fin L) :
    kerSymbol (bdP F L) k = bdSym F L k := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have h := bdEig_P (L := L) F
  have hrow : ∀ a : Fin L, ∑ x : Fin L, bdP F L a x * Real.cos (2 * π * k * ((x : ℝ) - a) / L) =
      bdSym F L k := by
    intro a
    have e := congrArg (fun z : ℂ => (z * (bdZ L)⁻¹ ^ (k.val * a.val)).re) (h k a)
    simp only at e
    rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (bdZ_ne_zero L), one_pow, mul_one,
      Complex.ofReal_re, Finset.sum_mul, Complex.re_sum] at e
    rw [← e]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc ((bdP F L a x : ℝ) : ℂ), Complex.re_ofReal_mul, bdZ_re]
  unfold kerSymbol
  rw [Finset.sum_congr rfl fun a _ => hrow a, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-- Rows of the circulant kernel. -/
private lemma bdP_row [NeZero L] (F : ℕ → ℝ) (a : Fin L) :
    ∑ c, bdP F L a c = ∑ y : Fin L, F (bdD y) := by
  simp only [bdP, Matrix.of_apply, bd_cycDist_eq]
  exact bd_sum_sub a (fun y => F (bdD y))

private lemma bd_abs_sin_mul (n : ℕ) (α : ℝ) : |Real.sin (n * α)| ≤ n * |Real.sin α| := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [add_mul, one_mul, Real.sin_add]
    calc |Real.sin (n * α) * Real.cos α + Real.cos (n * α) * Real.sin α|
        ≤ |Real.sin (n * α)| * |Real.cos α| + |Real.cos (n * α)| * |Real.sin α| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ n * |Real.sin α| * 1 + 1 * |Real.sin α| := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ = (n + 1) * |Real.sin α| := by ring

private lemma bd_one_sub_cos (x : ℝ) : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have := Real.cos_two_mul' (x / 2)
  rw [show 2 * (x / 2) = x by ring, Real.cos_sq'] at this
  linarith

/-- `1 - cos(nθ) ≤ n²(1 - cos θ)`. -/
private lemma bd_one_sub_cos_mul (n : ℕ) (θ : ℝ) :
    1 - Real.cos (n * θ) ≤ (n : ℝ) ^ 2 * (1 - Real.cos θ) := by
  rw [bd_one_sub_cos, bd_one_sub_cos, show n * θ / 2 = n * (θ / 2) by ring]
  have h := bd_abs_sin_mul n (θ / 2)
  have h0 : 0 ≤ |Real.sin (n * (θ / 2))| := abs_nonneg _
  have h2 : |Real.sin (n * (θ / 2))| ^ 2 ≤ (n * |Real.sin (θ / 2)|) ^ 2 := pow_le_pow_left₀ h0 h 2
  rw [sq_abs, mul_pow, sq_abs] at h2
  nlinarith

section Props

private lemma bdSym_abs_le (F : ℕ → ℝ) (hF0 : ∀ r, 0 ≤ F r)
    (hF1 : ∑ y : Fin L, F (bdD y) = 1) (k : Fin L) : |bdSym F L k| ≤ 1 := by
  unfold bdSym
  rw [← hF1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [abs_mul, abs_of_nonneg (hF0 _)]
  exact mul_le_of_le_one_right (hF0 _) (Real.abs_cos_le_one _)

private lemma bdSym_one_sub (F : ℕ → ℝ) (hF1 : ∑ y : Fin L, F (bdD y) = 1) (k : Fin L) :
    1 - bdSym F L k = ∑ y : Fin L, F (bdD y) * (1 - Real.cos (2 * π * k * bdD y / L)) := by
  unfold bdSym
  conv_lhs => rw [← hF1]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

private lemma bdSym_one_add [NeZero L] (F : ℕ → ℝ) (hF0 : ∀ r, 0 ≤ F r)
    (hF1 : ∑ y : Fin L, F (bdD y) = 1) (k : Fin L) : 2 * F 0 ≤ 1 + bdSym F L k := by
  have e : 1 + bdSym F L k = ∑ y : Fin L, F (bdD y) * (1 + Real.cos (2 * π * k * bdD y / L)) := by
    unfold bdSym
    conv_lhs => rw [← hF1]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [e]
  have h := Finset.single_le_sum (f := fun y : Fin L => F (bdD y) *
    (1 + Real.cos (2 * π * k * bdD y / L))) (fun y _ => mul_nonneg (hF0 _)
      (by linarith [Real.neg_one_le_cos (2 * π * k * bdD y / L)])) (Finset.mem_univ 0)
  simp only [bdD_zero, Nat.cast_zero, mul_zero, zero_div, Real.cos_zero] at h
  linarith

private lemma bdSym_lower [NeZero L] (F : ℕ → ℝ) (hF0 : ∀ r, 0 ≤ F r)
    (hF1 : ∑ y : Fin L, F (bdD y) = 1) (hL : 3 ≤ L) (k : Fin L) :
    2 * F 1 * (1 - Real.cos (2 * π * k / L)) ≤ 1 - bdSym F L k := by
  rw [bdSym_one_sub F hF1]
  have v1 : (1 : Fin L).val = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have v2 : (-1 : Fin L).val = L - 1 := by
    rw [Fin.neg_def]; simp only; rw [v1]; exact Nat.mod_eq_of_lt (by omega)
  have h1 : bdD (1 : Fin L) = 1 := by
    unfold bdD; rw [v1, v2]; omega
  have h2 : bdD (-1 : Fin L) = 1 := by rw [bdD_neg, h1]
  have hne : (1 : Fin L) ≠ -1 := by
    intro h
    have := congrArg Fin.val h
    rw [v1, v2] at this
    omega
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (f := fun y : Fin L => F (bdD y) *
    (1 - Real.cos (2 * π * k * bdD y / L))) (Finset.subset_univ {1, -1})
    (fun y _ _ => mul_nonneg (hF0 _) (by linarith [Real.cos_le_one (2 * π * k * bdD y / L)]))
  rw [Finset.sum_pair hne, h1, h2] at hsub
  simp only [Nat.cast_one, mul_one] at hsub
  linarith

private lemma bdSym_upper [NeZero L] (F : ℕ → ℝ) (hF0 : ∀ r, 0 ≤ F r)
    (hF1 : ∑ y : Fin L, F (bdD y) = 1) (k : Fin L) :
    1 - bdSym F L k ≤
      (∑ y : Fin L, F (bdD y) * (bdD y : ℝ) ^ 2) * (1 - Real.cos (2 * π * k / L)) := by
  rw [bdSym_one_sub F hF1, Finset.sum_mul]
  refine Finset.sum_le_sum fun y _ => ?_
  have := bd_one_sub_cos_mul (bdD y) (2 * π * k / L)
  rw [show (bdD y : ℝ) * (2 * π * k / L) = 2 * π * k * bdD y / L by ring] at this
  calc F (bdD y) * (1 - Real.cos (2 * π * k * bdD y / L))
      ≤ F (bdD y) * ((bdD y : ℝ) ^ 2 * (1 - Real.cos (2 * π * k / L))) :=
        mul_le_mul_of_nonneg_left this (hF0 _)
    _ = _ := by ring

end Props

end BdSymbol

/-! ### Riemann sums on the Fourier grid -/

section BdRiemann

/-- `Σ_{j=1}^{N} (1 + (j/a)²)⁻¹ ≤ 2a`. -/
private lemma bd_sum_lorentz (a : ℝ) (ha : 0 < a) (N : ℕ) :
    ∑ j ∈ Finset.range N, (1 + (((j + 1 : ℕ) : ℝ) / a) ^ 2)⁻¹ ≤ 2 * a := by
  have hterm : ∀ j : ℕ, (1 + (((j + 1 : ℕ) : ℝ) / a) ^ 2)⁻¹ ≤
      2 * a ^ 2 * (1 / ((j : ℝ) + a) - 1 / ((j : ℝ) + 1 + a)) := by
    intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    push_cast
    have h1 : 0 < (j : ℝ) + a := by linarith
    have h2 : 0 < (j : ℝ) + 1 + a := by linarith
    rw [show 1 / ((j : ℝ) + a) - 1 / ((j : ℝ) + 1 + a) = 1 / (((j : ℝ) + a) * ((j : ℝ) + 1 + a)) by
      field_simp; ring]
    rw [show (1 + (((j : ℝ) + 1) / a) ^ 2)⁻¹ = a ^ 2 / (a ^ 2 + ((j : ℝ) + 1) ^ 2) by
      field_simp]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((j : ℝ) + 1 - a)]
  calc ∑ j ∈ Finset.range N, (1 + (((j + 1 : ℕ) : ℝ) / a) ^ 2)⁻¹
      ≤ ∑ j ∈ Finset.range N, 2 * a ^ 2 * (1 / ((j : ℝ) + a) - 1 / ((j : ℝ) + 1 + a)) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = 2 * a ^ 2 * (1 / ((0 : ℕ) + a) - 1 / ((N : ℕ) + a)) := by
        rw [← Finset.mul_sum]
        congr 1
        have := Finset.sum_range_sub' (fun i : ℕ => 1 / ((i : ℝ) + a)) N
        simp only [Nat.cast_add, Nat.cast_one] at this
        rw [← this]
    _ ≤ 2 * a ^ 2 * (1 / a) := by
        have h0 : 0 ≤ 1 / (((N : ℕ) : ℝ) + a) := by positivity
        have e : 1 / (((0 : ℕ) : ℝ) + a) = 1 / a := by simp
        rw [e]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 2 * a := by field_simp

/-- Symmetrization of a sum over the Fourier grid. -/
private lemma bd_sum_min_le (L : ℕ) (h : ℕ → ℝ) (h0 : ∀ j, 0 ≤ h j) :
    ∑ k : Fin L, h (min k.val (L - k.val)) ≤
      h 0 + 2 * ∑ j ∈ Finset.range L, h (j + 1) := by
  have e1 : ∀ k : Fin L, h (min k.val (L - k.val)) ≤ h k.val + h (L - k.val) := by
    intro k
    rcases min_choice k.val (L - k.val) with e | e <;> rw [e]
    · linarith [h0 (L - k.val)]
    · linarith [h0 k.val]
  have e2 : ∑ k : Fin L, h (L - k.val) = ∑ j ∈ Finset.range L, h (j + 1) := by
    have : ∑ k : Fin L, h (L - k.val) = ∑ k : Fin L, h (k.val + 1) :=
      Fintype.sum_equiv Fin.revPerm _ _ (fun k => by
        rw [Fin.revPerm_apply, Fin.val_rev]; congr 1; have := k.isLt; omega)
    rw [this, Fin.sum_univ_eq_sum_range (fun j => h (j + 1)) L]
  have e3 : ∑ k : Fin L, h k.val ≤ h 0 + ∑ j ∈ Finset.range L, h (j + 1) := by
    rw [Fin.sum_univ_eq_sum_range h L]
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL; simp [h0 0]
    · obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      linarith [h0 (n + 1)]
  calc ∑ k : Fin L, h (min k.val (L - k.val))
      ≤ ∑ k : Fin L, (h k.val + h (L - k.val)) := Finset.sum_le_sum fun k _ => e1 k
    _ = ∑ k : Fin L, h k.val + ∑ k : Fin L, h (L - k.val) := Finset.sum_add_distrib
    _ ≤ h 0 + 2 * ∑ j ∈ Finset.range L, h (j + 1) := by rw [e2]; linarith

/-- The grid sum `L⁻¹ Σ_k (δ + g²|k|²)⁻¹`. -/
private def bdRS (L : ℕ) (δ g : ℝ) : ℝ :=
  (L : ℝ)⁻¹ * ∑ k : Fin L, (δ + g ^ 2 * torusAbs L k ^ 2)⁻¹

/-- Upper bound `L⁻¹ Σ_k (δ + g²|k|²)⁻¹ ≤ (2 + 2C)/(δ ℓ)`. -/
private lemma bdRS_le (Cm γ : ℝ) (hγ : 0 < γ) (hγC : 1 ≤ γ * Cm ^ 2) (hCm : 1 ≤ Cm) (L : ℕ)
    (hL : 1 ≤ L) (δ g : ℝ) (hδ : 0 < δ) (hg : 0 ≤ g) :
    bdRS L δ g ≤ (2 + 2 * Cm) / (δ * min (L : ℝ) (1 + g / Real.sqrt (γ * δ))) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  set lam := g / Real.sqrt (γ * δ) with hlam
  have hsq : 0 < Real.sqrt (γ * δ) := Real.sqrt_pos.mpr (by positivity)
  have hlam0 : 0 ≤ lam := div_nonneg hg hsq.le
  have hℓpos : 0 < min (L : ℝ) (1 + lam) := lt_min hLpos (by linarith)
  have hℓle : min (L : ℝ) (1 + lam) ≤ 1 + lam := min_le_right _ _
  have hℓL : min (L : ℝ) (1 + lam) ≤ L := min_le_left _ _
  -- the trivial bound
  have h1 : bdRS L δ g ≤ 1 / δ := by
    unfold bdRS
    have : ∀ k : Fin L, (δ + g ^ 2 * torusAbs L k ^ 2)⁻¹ ≤ 1 / δ := by
      intro k
      rw [one_div]
      exact inv_anti₀ hδ (by nlinarith [sq_nonneg (g * torusAbs L k)])
    calc (L : ℝ)⁻¹ * ∑ k : Fin L, (δ + g ^ 2 * torusAbs L k ^ 2)⁻¹
        ≤ (L : ℝ)⁻¹ * ∑ _k : Fin L, 1 / δ := by gcongr with k; exact this k
      _ = 1 / δ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul];
                      field_simp
  by_cases hl : lam ≤ 1
  · calc bdRS L δ g ≤ 1 / δ := h1
      _ ≤ 2 / (δ * min (L : ℝ) (1 + lam)) := by
          rw [div_le_div_iff₀ hδ (by positivity)]
          nlinarith
      _ ≤ (2 + 2 * Cm) / (δ * min (L : ℝ) (1 + lam)) := by
          gcongr; linarith
  push Not at hl
  have hgpos : 0 < g := by
    rcases hg.lt_or_eq with h | h
    · exact h
    · rw [hlam, ← h, zero_div] at hl; linarith
  -- the Lorentzian bound
  set a := (L : ℝ) * Real.sqrt δ / (2 * π * g) with ha
  have hapos : 0 < a := by rw [ha]; have := Real.sqrt_pos.mpr hδ; positivity
  have hterm : ∀ j : ℕ,
      (δ + g ^ 2 * (2 * π * (j : ℝ) / L) ^ 2)⁻¹ = δ⁻¹ * (1 + ((j : ℝ) / a) ^ 2)⁻¹ :=
      by
    intro j
    have hs : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
    rw [ha, ← mul_inv]
    congr 1
    field_simp
    rw [hs]; ring
  have h2 : bdRS L δ g ≤ δ⁻¹ * (1 / L + 4 * a / L) := by
    unfold bdRS
    have e : ∀ k : Fin L, (δ + g ^ 2 * torusAbs L k ^ 2)⁻¹ =
        (fun j : ℕ => δ⁻¹ * (1 + ((j : ℝ) / a) ^ 2)⁻¹) (min k.val (L - k.val)) := by
      intro k
      simp only
      rw [← hterm]
      rfl
    rw [Finset.sum_congr rfl fun k _ => e k]
    have hs := bd_sum_min_le L (fun j : ℕ => δ⁻¹ * (1 + ((j : ℝ) / a) ^ 2)⁻¹)
      (fun j => by positivity)
    have hl2 := bd_sum_lorentz a hapos L
    have : ∑ j ∈ Finset.range L, δ⁻¹ * (1 + (((j + 1 : ℕ) : ℝ) / a) ^ 2)⁻¹ ≤ δ⁻¹ * (2 * a) := by
      rw [← Finset.mul_sum]; gcongr
    have hs' : ∑ k : Fin L, δ⁻¹ * (1 + (((min k.val (L - k.val) : ℕ) : ℝ) / a) ^ 2)⁻¹ ≤
        δ⁻¹ * (1 + 4 * a) := by
      refine hs.trans ?_
      simp only [Nat.cast_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, add_zero, inv_one, mul_one]
      push_cast at this ⊢
      nlinarith [inv_pos.mpr hδ]
    calc (L : ℝ)⁻¹ * ∑ k : Fin L, δ⁻¹ * (1 + (((min k.val (L - k.val) : ℕ) : ℝ) / a) ^ 2)⁻¹
        ≤ (L : ℝ)⁻¹ * (δ⁻¹ * (1 + 4 * a)) := by gcongr
      _ = δ⁻¹ * (1 / L + 4 * a / L) := by field_simp
  have h3 : 4 * a / L ≤ 2 * Cm / (1 + lam) := by
    have hs : Real.sqrt (γ * δ) = Real.sqrt γ * Real.sqrt δ := Real.sqrt_mul hγ.le δ
    have hsγ : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
    have hγC' : 1 ≤ Real.sqrt γ * Cm := by
      have : Real.sqrt (γ * Cm ^ 2) = Real.sqrt γ * Cm := by
        rw [Real.sqrt_mul hγ.le, Real.sqrt_sq (by linarith)]
      rw [← this]; exact Real.one_le_sqrt.mpr hγC
    have hlam' : lam * Real.sqrt γ * Real.sqrt δ = g := by
      rw [hlam, hs]; field_simp
    have e4 : 4 * a / L = 2 * Real.sqrt δ / (π * g) := by rw [ha]; field_simp; ring
    rw [e4, div_le_div_iff₀ (by positivity) (by linarith)]
    have hπ : 2 < π := by linarith [Real.pi_gt_three]
    have hsδ := Real.sqrt_pos.mpr hδ
    have h4 : 2 * Real.sqrt δ * (1 + lam) ≤ 4 * lam * Real.sqrt δ := by nlinarith
    have hCg : lam * Real.sqrt δ ≤ Cm * g := by
      rw [← hlam']
      have := mul_le_mul_of_nonneg_left hγC' (by positivity : (0:ℝ) ≤ lam * Real.sqrt δ)
      nlinarith
    have h5 := mul_le_mul_of_nonneg_left hCg (le_of_lt Real.pi_pos)
    have h6 : 0 ≤ lam * Real.sqrt δ := by positivity
    nlinarith
  calc bdRS L δ g ≤ δ⁻¹ * (1 / L + 4 * a / L) := h2
    _ ≤ δ⁻¹ * (1 / min (L : ℝ) (1 + lam) + 2 * Cm / min (L : ℝ) (1 + lam)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
        · exact one_div_le_one_div_of_le hℓpos hℓL
        · exact h3.trans (div_le_div_of_nonneg_left (by positivity) hℓpos hℓle)
    _ = (1 + 2 * Cm) / (δ * min (L : ℝ) (1 + lam)) := by field_simp
    _ ≤ (2 + 2 * Cm) / (δ * min (L : ℝ) (1 + lam)) := by gcongr; linarith

/-- Lower bound `L⁻¹ Σ_k (δ + g²|k|²)⁻¹ ≥ (4π δ ℓ)⁻¹`. -/
private lemma bdRS_ge (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (L : ℕ) (hL : 1 ≤ L) (δ g : ℝ) (hδ : 0 < δ)
    (hg : 0 ≤ g) :
    1 / (4 * π) / (δ * min (L : ℝ) (1 + g / Real.sqrt (γ * δ))) ≤ bdRS L δ g := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  set lam := g / Real.sqrt (γ * δ) with hlam
  have hsq : 0 < Real.sqrt (γ * δ) := Real.sqrt_pos.mpr (by positivity)
  have hlam0 : 0 ≤ lam := div_nonneg hg hsq.le
  set ℓ := min (L : ℝ) (1 + lam) with hℓdef
  have hℓpos : 0 < ℓ := lt_min hLpos (by linarith)
  have hℓ1 : 1 ≤ ℓ := le_min (by exact_mod_cast hL) (by linarith)
  have hπ : 3 < π := Real.pi_gt_three
  have hterm0 : ∀ k : Fin L, 0 ≤ (δ + g ^ 2 * torusAbs L k ^ 2)⁻¹ := fun k => by positivity
  -- the zero mode
  have h1 : 1 / (δ * L) ≤ bdRS L δ g := by
    unfold bdRS
    have := Finset.single_le_sum (fun k _ => hterm0 k) (Finset.mem_univ (⟨0, by omega⟩ : Fin L))
    have e : torusAbs L ⟨0, by omega⟩ = 0 := by simp [torusAbs]
    rw [e] at this
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at this
    rw [one_div, mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  by_cases hLℓ : (L : ℝ) ≤ 1 + lam
  · have : ℓ = L := min_eq_left hLℓ
    rw [this]
    refine le_trans ?_ h1
    rw [div_div, one_div, one_div]
    exact inv_anti₀ (by positivity) (by nlinarith [mul_pos hδ hLpos])
  push Not at hLℓ
  have hℓeq : ℓ = 1 + lam := min_eq_right hLℓ.le
  -- the low modes `k ≤ x`
  have hgpos_or : g = 0 ∨ 0 < g := hg.eq_or_lt.imp (fun h => h.symm) id
  have hsδ := Real.sqrt_pos.mpr hδ
  have hlow : ∀ k : Fin L, 2 * π * g * k.val ≤ L * Real.sqrt δ →
      1 / (2 * δ) ≤ (δ + g ^ 2 * torusAbs L k ^ 2)⁻¹ := by
    intro k hk
    have ht : torusAbs L k ≤ 2 * π * k.val / L := by
      unfold torusAbs
      gcongr
      exact_mod_cast min_le_left _ _
    have ht0 : 0 ≤ torusAbs L k := by unfold torusAbs; positivity
    have hgt : g * torusAbs L k ≤ Real.sqrt δ := by
      calc g * torusAbs L k ≤ g * (2 * π * k.val / L) := by gcongr
        _ = 2 * π * g * k.val / L := by ring
        _ ≤ Real.sqrt δ := by rw [div_le_iff₀ hLpos]; linarith
    have : (g * torusAbs L k) ^ 2 ≤ δ := by
      calc (g * torusAbs L k) ^ 2 ≤ Real.sqrt δ ^ 2 :=
            pow_le_pow_left₀ (by positivity) hgt 2
        _ = δ := Real.sq_sqrt hδ.le
    rw [one_div]
    apply inv_anti₀ (by positivity)
    nlinarith
  set x := L * Real.sqrt δ / (2 * π * g) with hx
  by_cases hall : g = 0 ∨ (L : ℝ) - 1 ≤ x
  · -- every mode is low
    have hall' : ∀ k : Fin L, 2 * π * g * k.val ≤ L * Real.sqrt δ := by
      intro k
      rcases hall with h | h
      · rw [h]; simp only [mul_zero, zero_mul]; positivity
      · have hgp : 0 < g := by
          rcases hgpos_or with h' | h'
          · exfalso
            have hx0 : x = 0 := by rw [hx, h', mul_zero, div_zero]
            rw [h', zero_div] at hlam; rw [hlam] at hLℓ; rw [hx0] at h; linarith
          · exact h'
        have hk : (k.val : ℝ) ≤ L - 1 := by
          have := k.isLt
          have : (k.val : ℝ) + 1 ≤ L := by exact_mod_cast this
          linarith
        have := hk.trans h
        rw [hx, le_div_iff₀ (by positivity)] at this
        linarith
    have : 1 / (2 * δ) ≤ bdRS L δ g := by
      unfold bdRS
      calc 1 / (2 * δ) = (L : ℝ)⁻¹ * ∑ _k : Fin L, 1 / (2 * δ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
        _ ≤ (L : ℝ)⁻¹ * ∑ k : Fin L, (δ + g ^ 2 * torusAbs L k ^ 2)⁻¹ := by
            gcongr with k; exact hlow k (hall' k)
    refine le_trans ?_ this
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hδ hℓpos]
  push Not at hall
  obtain ⟨hg0, hxL⟩ := hall
  have hgp : 0 < g := lt_of_le_of_ne hg (Ne.symm hg0)
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  set M := ⌊x⌋₊ with hM
  have hML : M + 1 ≤ L := by
    have h1 : (M : ℝ) ≤ x := Nat.floor_le hx0
    have : (M : ℝ) + 1 < L := by linarith
    exact_mod_cast this.le
  have hMx : x < (M : ℝ) + 1 := Nat.lt_floor_add_one x
  have hsum : ((M : ℝ) + 1) * (1 / (2 * δ)) ≤ ∑ k : Fin L, (δ + g ^ 2 * torusAbs L k ^ 2)⁻¹ := by
    have e : ∑ k : Fin L, (δ + g ^ 2 * torusAbs L k ^ 2)⁻¹ =
        ∑ j ∈ Finset.range L, (δ + g ^ 2 * (2 * π * (min j (L - j) : ℕ) / L) ^ 2)⁻¹ := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => (δ + g ^ 2 * (2 * π * (min j (L - j) : ℕ) / L) ^ 2)⁻¹) L]
      rfl
    rw [e]
    have hsub : Finset.range (M + 1) ⊆ Finset.range L := Finset.range_subset_range.mpr hML
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity))
    have : ∀ j ∈ Finset.range (M + 1), 1 / (2 * δ) ≤
        (δ + g ^ 2 * (2 * π * (min j (L - j) : ℕ) / L) ^ 2)⁻¹ := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hjL : j < L := by omega
      have := hlow ⟨j, hjL⟩ (by
        have hj' : (j : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp hj
        have : (j : ℝ) ≤ x := hj'.trans (Nat.floor_le hx0)
        rw [hx, le_div_iff₀ (by positivity)] at this
        simp only; linarith)
      simpa [torusAbs] using this
    calc ((M : ℝ) + 1) * (1 / (2 * δ)) = ∑ _j ∈ Finset.range (M + 1), 1 / (2 * δ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := Finset.sum_le_sum this
  have h2 : x / L * (1 / (2 * δ)) ≤ bdRS L δ g := by
    unfold bdRS
    rw [div_eq_mul_inv x, mul_comm x, mul_assoc]
    gcongr
    exact le_trans (by gcongr) hsum
  refine le_trans ?_ h2
  rw [hℓeq]
  -- x/L = √δ/(2πg) ≥ 1/(2π(1+λ))
  have hs : Real.sqrt (γ * δ) ≤ Real.sqrt δ := Real.sqrt_le_sqrt (by nlinarith)
  have hgl : g ≤ lam * Real.sqrt δ := by
    rw [hlam, div_mul_eq_mul_div, le_div_iff₀ hsq]
    exact mul_le_mul_of_nonneg_left hs hg
  have hxL' : x / L = Real.sqrt δ / (2 * π * g) := by rw [hx]; field_simp
  rw [hxL']
  have key : g / Real.sqrt δ ≤ 1 + lam := by rw [div_le_iff₀ hsδ]; linarith
  have hgs : 0 < g / Real.sqrt δ := by positivity
  calc 1 / (4 * π) / (δ * (1 + lam)) = 1 / (4 * π * δ * (1 + lam)) := by
        rw [div_div]; ring
    _ ≤ 1 / (4 * π * δ * (g / Real.sqrt δ)) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact mul_le_mul_of_nonneg_left key (by positivity)
    _ = Real.sqrt δ / (2 * π * g) * (1 / (2 * δ)) := by field_simp; ring

end BdRiemann

/-! ### The mixed kernel of a probability kernel -/

section BdMixed

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `1 - tP` is invertible for a probability kernel and `|t| < 1`. -/
private lemma bd_isUnit (P : Matrix n n ℝ) (hP : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1)
    (t : ℝ) (ht : |t| < 1) : IsUnit (1 - t • P) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  refine det_ne_zero_of_sum_row_lt_diag fun k => ?_
  have hdiag : ‖(1 - t • P) k k‖ = |1 - t * P k k| := by
    simp [Matrix.sub_apply, Matrix.smul_apply, Real.norm_eq_abs]
  have hoff : ∀ j ∈ Finset.univ.erase k, ‖(1 - t • P) k j‖ = |t| * P k j := by
    intro j hj
    have hjk : k ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
    simp [Matrix.sub_apply, Matrix.smul_apply, hjk, Real.norm_eq_abs, abs_of_nonneg (hP k j)]
  rw [Finset.sum_congr rfl hoff, ← Finset.mul_sum, hdiag]
  have hs : ∑ j ∈ Finset.univ.erase k, P k j = 1 - P k k := by
    rw [← hrow k, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]; ring
  rw [hs]
  have hPk : P k k ≤ 1 := by
    rw [← hrow k]
    exact Finset.single_le_sum (fun j _ => hP k j) (Finset.mem_univ k)
  have h1 : 1 - |t| * P k k ≤ |1 - t * P k k| := by
    have := abs_sub_abs_le_abs_sub 1 (t * P k k)
    rw [abs_one, abs_mul, abs_of_nonneg (hP k k)] at this
    linarith
  have h0 : 0 ≤ P k k := hP k k
  nlinarith [abs_nonneg t]

private lemma bd_inv_mul (P : Matrix n n ℝ) (t : ℝ) (hU : IsUnit (1 - t • P)) :
    (1 - t • P)⁻¹ * (1 - t • P) = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)

private lemma bd_mul_inv (P : Matrix n n ℝ) (t : ℝ) (hU : IsUnit (1 - t • P)) :
    (1 - t • P) * (1 - t • P)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)

/-- `(1 - tP)⁻¹ = 1 + tP(1 - tP)⁻¹ = 1 + t(1 - tP)⁻¹P`. -/
private lemma bd_R_eqs (P : Matrix n n ℝ) (t : ℝ) (hU : IsUnit (1 - t • P)) :
    (1 - t • P)⁻¹ = 1 + t • (P * (1 - t • P)⁻¹) ∧
      (1 - t • P)⁻¹ = 1 + t • ((1 - t • P)⁻¹ * P) := by
  have h1 := bd_inv_mul P t hU
  have h2 := bd_mul_inv P t hU
  have e2 : (1 - t • P)⁻¹ - t • (P * (1 - t • P)⁻¹) = 1 := by
    have : (1 - t • P) * (1 - t • P)⁻¹ = (1 - t • P)⁻¹ - t • (P * (1 - t • P)⁻¹) := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [← this, h2]
  have e1 : (1 - t • P)⁻¹ - t • ((1 - t • P)⁻¹ * P) = 1 := by
    have : (1 - t • P)⁻¹ * (1 - t • P) = (1 - t • P)⁻¹ - t • ((1 - t • P)⁻¹ * P) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
    rw [← this, h1]
  constructor
  · calc (1 - t • P)⁻¹ = ((1 - t • P)⁻¹ - t • (P * (1 - t • P)⁻¹)) + t • (P * (1 - t • P)⁻¹) := by
          abel
      _ = 1 + t • (P * (1 - t • P)⁻¹) := by rw [e2]
  · calc (1 - t • P)⁻¹ = ((1 - t • P)⁻¹ - t • ((1 - t • P)⁻¹ * P)) + t • ((1 - t • P)⁻¹ * P) := by
          abel
      _ = 1 + t • ((1 - t • P)⁻¹ * P) := by rw [e1]

/-- `K = P + tPK = P + tKP`. -/
private lemma bd_K_eq (P : Matrix n n ℝ) (t : ℝ) (hU : IsUnit (1 - t • P)) :
    mixedKer P t = P + t • (P * mixedKer P t) ∧ mixedKer P t = P + t • (mixedKer P t * P) := by
  obtain ⟨hR, hR'⟩ := bd_R_eqs P t hU
  unfold mixedKer
  constructor
  · calc P * (1 - t • P)⁻¹ = P * (1 + t • (P * (1 - t • P)⁻¹)) := by rw [← hR]
      _ = P + t • (P * (P * (1 - t • P)⁻¹)) := by
          rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  · calc P * (1 - t • P)⁻¹ = P * (1 + t • ((1 - t • P)⁻¹ * P)) := by rw [← hR']
      _ = P + t • (P * (1 - t • P)⁻¹ * P) := by
          rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_assoc]

/-- `(1 - tP)⁻¹ = 1 + tK`. -/
private lemma bd_R_eq (P : Matrix n n ℝ) (t : ℝ) (hU : IsUnit (1 - t • P)) :
    (1 - t • P)⁻¹ = 1 + t • mixedKer P t :=
  (bd_R_eqs P t hU).1

/-- `K = Σ_{n<N} tⁿ P^{n+1} + t^N P^N K`. -/
private lemma bd_K_partial (P : Matrix n n ℝ) (t : ℝ) (hU : IsUnit (1 - t • P)) (N : ℕ) :
    mixedKer P t = ∑ i ∈ Finset.range N, t ^ i • P ^ (i + 1) + t ^ N • (P ^ N * mixedKer P t) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hK := (bd_K_eq P t hU).1
    have : t ^ N • (P ^ N * mixedKer P t) =
        t ^ N • P ^ (N + 1) + t ^ (N + 1) • (P ^ (N + 1) * mixedKer P t) := by
      calc t ^ N • (P ^ N * mixedKer P t) = t ^ N • (P ^ N * (P + t • (P * mixedKer P t))) := by
            rw [← hK]
        _ = t ^ N • P ^ (N + 1) + t ^ (N + 1) • (P ^ (N + 1) * mixedKer P t) := by
            rw [Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, ← pow_succ, smul_add,
              smul_smul, pow_succ t N]
    calc mixedKer P t =
          ∑ i ∈ Finset.range N, t ^ i • P ^ (i + 1) + t ^ N • (P ^ N * mixedKer P t) := ih
      _ = ∑ i ∈ Finset.range N, t ^ i • P ^ (i + 1) +
            (t ^ N • P ^ (N + 1) + t ^ (N + 1) • (P ^ (N + 1) * mixedKer P t)) := by rw [this]
      _ = _ := by rw [Finset.sum_range_succ, add_assoc]

/-- Powers of a probability kernel are probability kernels. -/
private lemma bd_pow_prob (P : Matrix n n ℝ) (hP : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1)
    (N : ℕ) : (∀ a b, 0 ≤ (P ^ N) a b) ∧ ∀ a, ∑ b, (P ^ N) a b = 1 := by
  induction N with
  | zero =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [Matrix.one_apply]
  | succ N ih =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun c _ => mul_nonneg (ih.1 a c) (hP c b)
    · rw [pow_succ]
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hrow, mul_one, ih.2 a]

end BdMixed

/-! ### Weighted rows: the reflection argument -/

section BdLyap

variable {L : ℕ} [NeZero L]

/-- `φ_μ = Σ_y F(‖y‖) cosh(μ‖y‖)`. -/
private def bdPhi (F : ℕ → ℝ) (L : ℕ) (μ : ℝ) : ℝ :=
  ∑ y : Fin L, F (bdD y) * Real.cosh (μ * bdD y)

/-- `P cosh(μ d(a,·)) ≤ φ_μ cosh(μ d(a,·))`. -/
private lemma bd_PV (F : ℕ → ℝ) (hF0 : ∀ r, 0 ≤ F r) (μ : ℝ) (hμ : 0 ≤ μ) (a x : Fin L) :
    ∑ c, bdP F L x c * Real.cosh (μ * cycDist a c) ≤
      bdPhi F L μ * Real.cosh (μ * cycDist a x) := by
  simp only [bdP, Matrix.of_apply, bd_cycDist_eq]
  have e1 : ∑ c, F (bdD (c - x)) * Real.cosh (μ * bdD (c - a)) =
      ∑ y : Fin L, F (bdD y) * Real.cosh (μ * bdD ((x - a) + y)) := by
    rw [← bd_sum_sub x (fun y => F (bdD y) * Real.cosh (μ * bdD ((x - a) + y)))]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 4; abel_nf
  have e2 : ∑ y : Fin L, F (bdD y) * Real.cosh (μ * bdD ((x - a) + y)) =
      ∑ y : Fin L, F (bdD y) * Real.cosh (μ * bdD ((x - a) - y)) := by
    rw [← Fintype.sum_equiv (Equiv.neg (Fin L)) (fun y => F (bdD (-y)) *
      Real.cosh (μ * bdD ((x - a) + -y))) _ (fun _ => rfl)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [bdD_neg, ← sub_eq_add_neg]
  rw [e1]
  have h2 : 2 * ∑ y : Fin L, F (bdD y) * Real.cosh (μ * bdD ((x - a) + y)) ≤
      2 * (bdPhi F L μ * Real.cosh (μ * bdD (x - a))) := by
    calc 2 * ∑ y : Fin L, F (bdD y) * Real.cosh (μ * bdD ((x - a) + y))
        = ∑ y : Fin L, F (bdD y) * (Real.cosh (μ * bdD ((x - a) + y)) +
            Real.cosh (μ * bdD ((x - a) - y))) := by
          rw [two_mul]; nth_rewrite 2 [e2]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ ∑ y : Fin L, F (bdD y) * (2 * Real.cosh (μ * bdD (x - a)) * Real.cosh (μ * bdD y)) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (bd_cosh_pair μ hμ _ _) (hF0 _)
      _ = 2 * (bdPhi F L μ * Real.cosh (μ * bdD (x - a))) := by
          unfold bdPhi
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
  linarith

omit [NeZero L] in
private lemma bdP_nonneg (F : ℕ → ℝ) (hF0 : ∀ r, 0 ≤ F r) (a c : Fin L) : 0 ≤ bdP F L a c :=
  hF0 _

private lemma bdP_row_one (F : ℕ → ℝ) (hF1 : ∑ y : Fin L, F (bdD y) = 1) (a : Fin L) :
    ∑ c, bdP F L a c = 1 := by
  rw [bdP_row, hF1]

private lemma bdP_symm (F : ℕ → ℝ) : (bdP F L).transpose = bdP F L := by
  ext a c
  simp [bdP, Matrix.transpose_apply, bd_cycDist_comm]

/-- `Pⁿ cosh(μ d(a,·)) ≤ φ_μⁿ cosh(μ d(a,·))`. -/
private lemma bd_PnV (F : ℕ → ℝ) (hF0 : ∀ r, 0 ≤ F r) (μ : ℝ) (hμ : 0 ≤ μ) (a : Fin L) (N : ℕ)
    (x : Fin L) :
    ∑ c, (bdP F L ^ N) x c * Real.cosh (μ * cycDist a c) ≤
      bdPhi F L μ ^ N * Real.cosh (μ * cycDist a x) := by
  induction N generalizing x with
  | zero =>
    simp [Matrix.one_apply]
  | succ N ih =>
    rw [pow_succ']
    simp only [Matrix.mul_apply]
    calc ∑ c, (∑ d, bdP F L x d * (bdP F L ^ N) d c) * Real.cosh (μ * cycDist a c)
        = ∑ d, bdP F L x d * ∑ c, (bdP F L ^ N) d c * Real.cosh (μ * cycDist a c) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by ring
      _ ≤ ∑ d, bdP F L x d * (bdPhi F L μ ^ N * Real.cosh (μ * cycDist a d)) :=
          Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (ih d) (bdP_nonneg F hF0 x d)
      _ = bdPhi F L μ ^ N * ∑ d, bdP F L x d * Real.cosh (μ * cycDist a d) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
      _ ≤ bdPhi F L μ ^ N * (bdPhi F L μ * Real.cosh (μ * cycDist a x)) := by
          have h0 : 0 ≤ bdPhi F L μ := Finset.sum_nonneg fun y _ =>
            mul_nonneg (hF0 _) (le_trans zero_le_one (Real.one_le_cosh _))
          exact mul_le_mul_of_nonneg_left (bd_PV F hF0 μ hμ a x) (pow_nonneg h0 N)
      _ = bdPhi F L μ ^ (N + 1) * Real.cosh (μ * cycDist a x) := by ring

/-- `K cosh(μ d(a,·)) ≤ φ/(1-tφ) cosh(μ d(a,·))` when `tφ < 1`. -/
private lemma bd_KV (F : ℕ → ℝ) (hF0 : ∀ r, 0 ≤ F r) (hF1 : ∑ y : Fin L, F (bdD y) = 1) (μ : ℝ)
    (hμ : 0 ≤ μ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hφ : t * bdPhi F L μ < 1) (a x : Fin L) :
    ∑ c, mixedKer (bdP F L) t x c * Real.cosh (μ * cycDist a c) ≤
      bdPhi F L μ / (1 - t * bdPhi F L μ) * Real.cosh (μ * cycDist a x) := by
  have hP0 := bdP_nonneg (L := L) F hF0
  have hrow := bdP_row_one (L := L) F hF1
  have hU := bd_isUnit (bdP F L) hP0 hrow t (by rw [abs_of_nonneg ht0]; exact ht1)
  obtain ⟨hK0, -⟩ := mixedKer_nonneg_row (bdP F L) hP0 hrow t ht0 ht1
  set K := mixedKer (bdP F L) t
  set u : Fin L → ℝ := fun x => ∑ c, K x c * Real.cosh (μ * cycDist a c) with hu
  have hφ0 : 0 ≤ bdPhi F L μ := Finset.sum_nonneg fun y _ =>
    mul_nonneg (hF0 _) (le_trans zero_le_one (Real.one_le_cosh _))
  have key : ∀ x, u x ≤ bdPhi F L μ * Real.cosh (μ * cycDist a x) + t * bdPhi F L μ * u x := by
    intro x
    have hK : K = bdP F L + t • (K * bdP F L) := (bd_K_eq (bdP F L) t hU).2
    have hKe : ∀ c, K x c = bdP F L x c + t * ∑ j, K x j * bdP F L j c := by
      intro c
      have := congrFun (congrFun hK x) c
      simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply] using this
    have e : u x = ∑ c, bdP F L x c * Real.cosh (μ * cycDist a c) +
        t * ∑ d, K x d * ∑ c, bdP F L d c * Real.cosh (μ * cycDist a c) := by
      calc u x = ∑ c, (bdP F L x c + t * ∑ j, K x j * bdP F L j c) * Real.cosh (μ * cycDist a c) :=
            Finset.sum_congr rfl fun c _ => by rw [← hKe c]
        _ = ∑ c, bdP F L x c * Real.cosh (μ * cycDist a c) +
              ∑ c, ∑ j, t * (K x j * (bdP F L j c * Real.cosh (μ * cycDist a c))) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [add_mul, Finset.mul_sum, Finset.sum_mul]
            congr 1
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = _ := by
            rw [Finset.sum_comm, Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [e]
    have h1 := bd_PV F hF0 μ hμ a x
    have h2 : ∑ d, K x d * ∑ c, bdP F L d c * Real.cosh (μ * cycDist a c) ≤
        bdPhi F L μ * u x := by
      calc ∑ d, K x d * ∑ c, bdP F L d c * Real.cosh (μ * cycDist a c)
          ≤ ∑ d, K x d * (bdPhi F L μ * Real.cosh (μ * cycDist a d)) :=
            Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (bd_PV F hF0 μ hμ a d) (hK0 x d)
        _ = bdPhi F L μ * u x := by
            simp only [hu]; rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun d _ => by ring
    nlinarith
  have := key x
  have hpos : 0 < 1 - t * bdPhi F L μ := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith

end BdLyap

/-! ### Kernel bounds from the profile -/

section BdCore

variable {L : ℕ}

/-- Hypotheses on the profile `F` of a symmetric circulant probability kernel at coupling `g`:
mass `≥ p₀` at `0`, mass `≥ c₁g²` at distance `1`, and weighted off-diagonal mass `≤ C_P g²`. -/
private structure BdGood (L : ℕ) (F : ℕ → ℝ) (g p₀ c₁ μ₀ CP : ℝ) : Prop where
  hL : 3 ≤ L
  nonneg : ∀ r, 0 ≤ F r
  sum : ∀ [NeZero L], ∑ y : Fin L, F (bdD y) = 1
  zero : p₀ ≤ F 0
  one : c₁ * g ^ 2 ≤ F 1
  off : ∀ [NeZero L], ∑ y : Fin L, (if y = 0 then 0 else Real.exp (μ₀ * bdD y) * F (bdD y)) ≤
    CP * g ^ 2
  hp₀ : 0 < p₀
  hc₁ : 0 < c₁
  hμ₀ : 0 < μ₀
  hCP : 0 < CP

private lemma bd_cos_torus (L : ℕ) (hL : 1 ≤ L) (k : Fin L) :
    Real.cos (2 * π * k / L) = Real.cos (torusAbs L k) ∧ 0 ≤ torusAbs L k ∧ torusAbs L k ≤ π := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hk := k.isLt
  refine ⟨?_, by unfold torusAbs; positivity, ?_⟩
  · unfold torusAbs
    rcases le_total k.val (L - k.val) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Nat.cast_sub hk.le]
      rw [show 2 * π * ((L : ℝ) - k.val) / L = ((1 : ℕ) : ℝ) * (2 * π) - 2 * π * k.val / L by
        field_simp; ring, Real.cos_nat_mul_two_pi_sub]
  · unfold torusAbs
    rw [div_le_iff₀ hLp]
    have : 2 * (min k.val (L - k.val) : ℕ) ≤ L := by omega
    have : (2 : ℝ) * (min k.val (L - k.val) : ℕ) ≤ L := by exact_mod_cast this
    nlinarith [Real.pi_pos]

private lemma bd_one_sub_cos_ge (τ : ℝ) (h0 : 0 ≤ τ) (hπ : τ ≤ π) :
    2 / π ^ 2 * τ ^ 2 ≤ 1 - Real.cos τ := by
  have := Real.cos_le_one_sub_mul_cos_sq (x := τ) (by rw [abs_of_nonneg h0]; exact hπ)
  linarith

private lemma bd_one_sub_cos_le (τ : ℝ) : 1 - Real.cos τ ≤ τ ^ 2 / 2 := by
  have := Real.one_sub_sq_div_two_le_cos (x := τ)
  linarith

private lemma bd_cosh_sub_one (z : ℝ) (hz : 0 ≤ z) : Real.cosh z - 1 ≤ z ^ 2 * Real.exp z := by
  rcases le_or_gt z 1 with h | h
  · have h1 := Real.abs_exp_sub_one_sub_id_le (x := z) (by rw [abs_of_nonneg hz]; exact h)
    have h2 := Real.abs_exp_sub_one_sub_id_le (x := -z) (by rw [abs_neg, abs_of_nonneg hz]; exact h)
    rw [Real.cosh_eq]
    have h3 := (abs_le.mp h1).2
    have h4 := (abs_le.mp h2).2
    have h5 : 1 ≤ Real.exp z := Real.one_le_exp hz
    nlinarith [sq_nonneg z]
  · have h1 : Real.cosh z ≤ Real.exp z := by
      rw [Real.cosh_eq]
      have : Real.exp (-z) ≤ Real.exp z := Real.exp_le_exp.mpr (by linarith)
      linarith
    have h2 : Real.exp z ≤ z ^ 2 * Real.exp z := by
      have : 1 ≤ z ^ 2 := by nlinarith
      nlinarith [Real.exp_pos z]
    linarith

/-- `d² ≤ (16/μ₀²) e^{μ₀ d/2}`. -/
private lemma bd_sq_le_exp (μ₀ : ℝ) (hμ₀ : 0 < μ₀) (d : ℝ) (hd : 0 ≤ d) :
    d ^ 2 ≤ 16 / μ₀ ^ 2 * Real.exp (μ₀ * d / 2) := by
  have h1 : μ₀ * d / 4 ≤ Real.exp (μ₀ * d / 4) := by
    linarith [Real.add_one_le_exp (μ₀ * d / 4)]
  have h2 : (μ₀ * d / 4) ^ 2 ≤ Real.exp (μ₀ * d / 4) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  rw [← Real.exp_nat_mul] at h2
  have e : ((2 : ℕ) : ℝ) * (μ₀ * d / 4) = μ₀ * d / 2 := by push_cast; ring
  rw [e] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

variable [NeZero L]

/-- Second moment `Σ_y F(‖y‖)‖y‖² ≤ (16 C_P/μ₀²) g²`. -/
private lemma bd_second (F : ℕ → ℝ) (g p₀ c₁ μ₀ CP : ℝ) (h : BdGood L F g p₀ c₁ μ₀ CP) :
    ∑ y : Fin L, F (bdD y) * (bdD y : ℝ) ^ 2 ≤ 16 * CP / μ₀ ^ 2 * g ^ 2 := by
  have hμ₀ := h.hμ₀
  have e : ∀ y : Fin L, F (bdD y) * (bdD y : ℝ) ^ 2 ≤
      16 / μ₀ ^ 2 * (if y = 0 then 0 else Real.exp (μ₀ * bdD y) * F (bdD y)) := by
    intro y
    split_ifs with hy
    · subst hy; simp [bdD_zero]
    · have h1 := bd_sq_le_exp μ₀ hμ₀ (bdD y) (Nat.cast_nonneg _)
      have h2 : Real.exp (μ₀ * bdD y / 2) ≤ Real.exp (μ₀ * bdD y) :=
        Real.exp_le_exp.mpr (by have : 0 ≤ μ₀ * (bdD y : ℝ) := by positivity
                                linarith)
      have h3 := h.nonneg (bdD y)
      have : (bdD y : ℝ) ^ 2 ≤ 16 / μ₀ ^ 2 * Real.exp (μ₀ * bdD y) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
      nlinarith
  calc ∑ y : Fin L, F (bdD y) * (bdD y : ℝ) ^ 2
      ≤ ∑ y : Fin L, 16 / μ₀ ^ 2 * (if y = 0 then 0 else Real.exp (μ₀ * bdD y) * F (bdD y)) :=
        Finset.sum_le_sum fun y _ => e y
    _ = 16 / μ₀ ^ 2 * ∑ y : Fin L, (if y = 0 then 0 else Real.exp (μ₀ * bdD y) * F (bdD y)) := by
        rw [Finset.mul_sum]
    _ ≤ 16 / μ₀ ^ 2 * (CP * g ^ 2) := by gcongr; exact h.off
    _ = 16 * CP / μ₀ ^ 2 * g ^ 2 := by ring

/-- `φ_μ ≤ 1 + μ² (16 C_P/μ₀²) g²` for `0 ≤ μ ≤ μ₀/2`. -/
private lemma bd_phi_le (F : ℕ → ℝ) (g p₀ c₁ μ₀ CP : ℝ) (h : BdGood L F g p₀ c₁ μ₀ CP) (μ : ℝ)
    (hμ : 0 ≤ μ) (hμ2 : μ ≤ μ₀ / 2) :
    bdPhi F L μ ≤ 1 + μ ^ 2 * (16 * CP / μ₀ ^ 2 * g ^ 2) := by
  have hμ₀ := h.hμ₀
  have e : ∀ y : Fin L, F (bdD y) * Real.cosh (μ * bdD y) ≤ F (bdD y) +
      μ ^ 2 * (16 / μ₀ ^ 2 * (if y = 0 then 0 else Real.exp (μ₀ * bdD y) * F (bdD y))) := by
    intro y
    have hF := h.nonneg (bdD y)
    split_ifs with hy
    · subst hy; simp [bdD_zero]
    · have hd : (0 : ℝ) ≤ bdD y := Nat.cast_nonneg _
      have h1 := bd_cosh_sub_one (μ * bdD y) (by positivity)
      have h2 := bd_sq_le_exp μ₀ hμ₀ (bdD y) hd
      have h3 : Real.exp (μ * bdD y) ≤ Real.exp (μ₀ * bdD y / 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h4 : (bdD y : ℝ) ^ 2 * Real.exp (μ * bdD y) ≤ 16 / μ₀ ^ 2 * Real.exp (μ₀ * bdD y) := by
        calc (bdD y : ℝ) ^ 2 * Real.exp (μ * bdD y)
            ≤ 16 / μ₀ ^ 2 * Real.exp (μ₀ * bdD y / 2) * Real.exp (μ₀ * bdD y / 2) :=
              mul_le_mul h2 h3 (by positivity) (by positivity)
          _ = 16 / μ₀ ^ 2 * Real.exp (μ₀ * bdD y) := by
              rw [mul_assoc, ← Real.exp_add]; ring_nf
      have h5 : Real.cosh (μ * bdD y) ≤ 1 + μ ^ 2 * (16 / μ₀ ^ 2 * Real.exp (μ₀ * bdD y)) := by
        have : (μ * bdD y) ^ 2 * Real.exp (μ * bdD y) =
            μ ^ 2 * ((bdD y : ℝ) ^ 2 * Real.exp (μ * bdD y)) := by ring
        nlinarith [sq_nonneg μ]
      calc F (bdD y) * Real.cosh (μ * bdD y)
          ≤ F (bdD y) * (1 + μ ^ 2 * (16 / μ₀ ^ 2 * Real.exp (μ₀ * bdD y))) :=
            mul_le_mul_of_nonneg_left h5 hF
        _ = _ := by ring
  unfold bdPhi
  calc ∑ y : Fin L, F (bdD y) * Real.cosh (μ * bdD y)
      ≤ ∑ y : Fin L, (F (bdD y) + μ ^ 2 * (16 / μ₀ ^ 2 *
          (if y = 0 then 0 else Real.exp (μ₀ * bdD y) * F (bdD y)))) :=
        Finset.sum_le_sum fun y _ => e y
    _ = 1 + μ ^ 2 * (16 / μ₀ ^ 2 *
          ∑ y : Fin L, (if y = 0 then 0 else Real.exp (μ₀ * bdD y) * F (bdD y))) := by
        rw [Finset.sum_add_distrib, h.sum, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 1 + μ ^ 2 * (16 / μ₀ ^ 2 * (CP * g ^ 2)) := by gcongr; exact h.off
    _ = _ := by ring

omit [NeZero L] in
private lemma bd_phi_ge_one (F : ℕ → ℝ) (hF0 : ∀ r, 0 ≤ F r) (hF1 : ∑ y : Fin L, F (bdD y) = 1)
    (μ : ℝ) : 1 ≤ bdPhi F L μ := by
  unfold bdPhi
  rw [← hF1]
  exact Finset.sum_le_sum fun y _ => le_mul_of_one_le_right (hF0 _) (Real.one_le_cosh _)

/-- Entries of `Pⁿ`: `|Pⁿ_{ab}| ≤ L⁻¹ Σ_k |P̂(k)|ⁿ`. -/
private lemma bd_Pn_abs (F : ℕ → ℝ) (N : ℕ) (a b : Fin L) :
    |(bdP F L ^ N) a b| ≤ (L : ℝ)⁻¹ * ∑ k, |bdSym F L k| ^ N := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have h := bdEig_abs_le hL (bdEig_pow (bdEig_P (L := L) F) N) a b
  simpa [norm_pow, Complex.norm_real, Real.norm_eq_abs] using h

/-- The tilt of `P^{n+1}`. -/
private lemma bd_Pn_tilt (F : ℕ → ℝ) (hF0 : ∀ r, 0 ≤ F r) (hF1 : ∑ y : Fin L, F (bdD y) = 1)
    (μ : ℝ) (hμ : 0 ≤ μ) (N : ℕ) (a b : Fin L) :
    Real.exp (μ * cycDist a b / 2) * (bdP F L ^ (N + 1)) a b ≤
      4 * bdPhi F L μ ^ (N + 1) *
        ((L : ℝ)⁻¹ * ∑ k, Real.sqrt |bdSym F L k| ^ N) := by
  set n₁ := (N + 1) / 2 with hn₁
  set n₂ := N + 1 - n₁ with hn₂
  have hsplit : bdP F L ^ (N + 1) = bdP F L ^ n₁ * bdP F L ^ n₂ := by
    rw [← pow_add]; congr 1; omega
  have hP0 := bdP_nonneg (L := L) F hF0
  have hrow := bdP_row_one (L := L) F hF1
  have hpow := bd_pow_prob (bdP F L) hP0 hrow
  have hφ1 := bd_phi_ge_one F hF0 hF1 μ
  have hsym1 : ∀ k, |bdSym F L k| ≤ 1 := fun k => bdSym_abs_le F hF0 hF1 k
  -- weighted rows of powers
  have hW : ∀ m (x : Fin L), ∑ c, Real.exp (μ * cycDist x c) * (bdP F L ^ m) x c ≤
      2 * bdPhi F L μ ^ m := by
    intro m x
    have h1 := bd_PnV F hF0 μ hμ x m x
    rw [bd_cycDist_self, Nat.cast_zero, mul_zero, Real.cosh_zero, mul_one] at h1
    calc ∑ c, Real.exp (μ * cycDist x c) * (bdP F L ^ m) x c
        ≤ ∑ c, 2 * ((bdP F L ^ m) x c * Real.cosh (μ * cycDist x c)) := by
          refine Finset.sum_le_sum fun c _ => ?_
          have : Real.exp (μ * cycDist x c) ≤ 2 * Real.cosh (μ * cycDist x c) := by
            rw [Real.cosh_eq]; linarith [Real.exp_pos (-(μ * cycDist x c))]
          nlinarith [(hpow m).1 x c]
      _ ≤ 2 * bdPhi F L μ ^ m := by rw [← Finset.mul_sum]; linarith
  -- symmetric powers
  have hT : ∀ m, (bdP F L ^ m).transpose = bdP F L ^ m := by
    intro m; rw [Matrix.transpose_pow, bdP_symm]
  have hS : ∀ m (x y : Fin L), (bdP F L ^ m) x y ≤ (L : ℝ)⁻¹ * ∑ k, |bdSym F L k| ^ m :=
    fun m x y => (le_abs_self _).trans (bd_Pn_abs F m x y)
  have hmono : ∀ k, |bdSym F L k| ^ n₂ ≤ |bdSym F L k| ^ n₁ := fun k =>
    pow_le_pow_of_le_one (abs_nonneg _) (hsym1 k) (by omega)
  have hsq : ∀ k, |bdSym F L k| ^ n₁ ≤ Real.sqrt |bdSym F L k| ^ N := by
    intro k
    have h0 := Real.sqrt_nonneg |bdSym F L k|
    have h1 : Real.sqrt |bdSym F L k| ≤ 1 := Real.sqrt_le_one.mpr (hsym1 k)
    calc |bdSym F L k| ^ n₁ = Real.sqrt |bdSym F L k| ^ (2 * n₁) := by
          rw [pow_mul, Real.sq_sqrt (abs_nonneg _)]
      _ ≤ Real.sqrt |bdSym F L k| ^ N := pow_le_pow_of_le_one h0 h1 (by omega)
  set A := (L : ℝ)⁻¹ * ∑ k, Real.sqrt |bdSym F L k| ^ N with hA
  have hS1 : ∀ x y, (bdP F L ^ n₁) x y ≤ A := fun x y => (hS n₁ x y).trans (by
    rw [hA]; gcongr with k; exact hsq k)
  have hS2 : ∀ x y, (bdP F L ^ n₂) x y ≤ A := fun x y => (hS n₂ x y).trans (by
    rw [hA]; gcongr with k; exact (hmono k).trans (hsq k))
  have hφn : ∀ m, m ≤ N + 1 → bdPhi F L μ ^ m ≤ bdPhi F L μ ^ (N + 1) := fun m hm =>
    pow_le_pow_right₀ hφ1 hm
  rw [hsplit, Matrix.mul_apply, Finset.mul_sum]
  have hsplitexp : ∀ c, Real.exp (μ * cycDist a b / 2) ≤
      Real.exp (μ * cycDist a c) + Real.exp (μ * cycDist c b) := by
    intro c
    have htri : (cycDist a b : ℝ) ≤ cycDist a c + cycDist c b := by
      exact_mod_cast bd_cycDist_tri a c b
    rcases le_total (cycDist a c : ℝ) (cycDist c b) with h | h
    · have : Real.exp (μ * cycDist a b / 2) ≤ Real.exp (μ * cycDist c b) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith [Real.exp_pos (μ * cycDist a c)]
    · have : Real.exp (μ * cycDist a b / 2) ≤ Real.exp (μ * cycDist a c) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith [Real.exp_pos (μ * cycDist c b)]
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  calc ∑ c, Real.exp (μ * cycDist a b / 2) * ((bdP F L ^ n₁) a c * (bdP F L ^ n₂) c b)
      ≤ ∑ c, (Real.exp (μ * cycDist a c) * (bdP F L ^ n₁) a c * A +
          A * (Real.exp (μ * cycDist b c) * (bdP F L ^ n₂) b c)) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 := (hpow n₁).1 a c
        have h2 := (hpow n₂).1 c b
        have hsymm : (bdP F L ^ n₂) c b = (bdP F L ^ n₂) b c := by
          have := congrFun (congrFun (hT n₂) b) c
          rw [Matrix.transpose_apply] at this
          exact this
        have hcb : cycDist c b = cycDist b c := bd_cycDist_comm c b
        calc Real.exp (μ * cycDist a b / 2) * ((bdP F L ^ n₁) a c * (bdP F L ^ n₂) c b)
            ≤ (Real.exp (μ * cycDist a c) + Real.exp (μ * cycDist c b)) *
                ((bdP F L ^ n₁) a c * (bdP F L ^ n₂) c b) :=
              mul_le_mul_of_nonneg_right (hsplitexp c) (mul_nonneg h1 h2)
          _ = Real.exp (μ * cycDist a c) * (bdP F L ^ n₁) a c * (bdP F L ^ n₂) c b +
                (bdP F L ^ n₁) a c * (Real.exp (μ * cycDist b c) * (bdP F L ^ n₂) b c) := by
              rw [hcb, ← hsymm]; ring
          _ ≤ _ := add_le_add
              (mul_le_mul_of_nonneg_left (hS2 c b) (mul_nonneg (Real.exp_pos _).le h1))
              (mul_le_mul_of_nonneg_right (hS1 a c)
                (mul_nonneg (Real.exp_pos _).le ((hpow n₂).1 b c)))
    _ = (∑ c, Real.exp (μ * cycDist a c) * (bdP F L ^ n₁) a c) * A +
          A * ∑ c, Real.exp (μ * cycDist b c) * (bdP F L ^ n₂) b c := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ ≤ (2 * bdPhi F L μ ^ n₁) * A + A * (2 * bdPhi F L μ ^ n₂) := by
        gcongr
        · exact hW n₁ a
        · exact hW n₂ b
    _ ≤ (2 * bdPhi F L μ ^ (N + 1)) * A + A * (2 * bdPhi F L μ ^ (N + 1)) := by
        have := hφn n₁ (by omega)
        have := hφn n₂ (by omega)
        gcongr
    _ = 4 * bdPhi F L μ ^ (N + 1) * A := by ring

end BdCore

section BdCore2

variable {L : ℕ} [NeZero L]

/-- The tilted kernel: `e^{μ d/2} K_{ab} ≤ 4φ L⁻¹ Σ_k (1 - tφ√|P̂(k)|)⁻¹`. -/
private lemma bd_K_tilt (F : ℕ → ℝ) (hF0 : ∀ r, 0 ≤ F r) (hF1 : ∑ y : Fin L, F (bdD y) = 1)
    (μ : ℝ) (hμ : 0 ≤ μ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hφ : t * bdPhi F L μ < 1)
    (a b : Fin L) :
    Real.exp (μ * cycDist a b / 2) * mixedKer (bdP F L) t a b ≤
      4 * bdPhi F L μ * ((L : ℝ)⁻¹ *
        ∑ k, (1 - t * bdPhi F L μ * Real.sqrt |bdSym F L k|)⁻¹) := by
  have hP0 := bdP_nonneg (L := L) F hF0
  have hrow := bdP_row_one (L := L) F hF1
  have hU := bd_isUnit (bdP F L) hP0 hrow t (by rw [abs_of_nonneg ht0]; exact ht1)
  obtain ⟨hK0, hKr⟩ := mixedKer_nonneg_row (bdP F L) hP0 hrow t ht0 ht1
  have hpow := bd_pow_prob (bdP F L) hP0 hrow
  have hφ1 := bd_phi_ge_one F hF0 hF1 μ
  have hsym1 : ∀ k, |bdSym F L k| ≤ 1 := fun k => bdSym_abs_le F hF0 hF1 k
  set φ := bdPhi F L μ with hφdef
  set B := 4 * φ * ((L : ℝ)⁻¹ * ∑ k, (1 - t * φ * Real.sqrt |bdSym F L k|)⁻¹) with hB
  have hρ : ∀ k, 0 ≤ t * φ * Real.sqrt |bdSym F L k| ∧ t * φ * Real.sqrt |bdSym F L k| < 1 := by
    intro k
    have h0 := Real.sqrt_nonneg |bdSym F L k|
    have h1 : Real.sqrt |bdSym F L k| ≤ 1 := Real.sqrt_le_one.mpr (hsym1 k)
    have htφ : 0 ≤ t * φ := mul_nonneg ht0 (by linarith)
    exact ⟨mul_nonneg htφ h0, lt_of_le_of_lt (mul_le_of_le_one_right htφ h1) hφ⟩
  -- partial sums
  have hpart : ∀ N : ℕ, Real.exp (μ * cycDist a b / 2) *
      (∑ i ∈ Finset.range N, t ^ i • bdP F L ^ (i + 1)) a b ≤ B := by
    intro N
    rw [Matrix.sum_apply, Finset.mul_sum]
    calc ∑ i ∈ Finset.range N, Real.exp (μ * cycDist a b / 2) * (t ^ i • bdP F L ^ (i + 1)) a b
        ≤ ∑ i ∈ Finset.range N, t ^ i * (4 * φ ^ (i + 1) *
            ((L : ℝ)⁻¹ * ∑ k, Real.sqrt |bdSym F L k| ^ i)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm]
          exact mul_le_mul_of_nonneg_left (bd_Pn_tilt F hF0 hF1 μ hμ i a b) (pow_nonneg ht0 i)
      _ = ∑ i ∈ Finset.range N, 4 * φ * ((L : ℝ)⁻¹ * ∑ k,
            (t * φ * Real.sqrt |bdSym F L k|) ^ i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have : ∑ k, (t * φ * Real.sqrt |bdSym F L k|) ^ i =
              t ^ i * φ ^ i * ∑ k, Real.sqrt |bdSym F L k| ^ i := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
          rw [this]; ring
      _ = 4 * φ * ((L : ℝ)⁻¹ * ∑ k, ∑ i ∈ Finset.range N,
            (t * φ * Real.sqrt |bdSym F L k|) ^ i) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
      _ ≤ B := by
          rw [hB]
          have hφ0 : 0 ≤ 4 * φ := by linarith
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun k _ => ?_) (by positivity)) hφ0
          obtain ⟨h0, h1⟩ := hρ k
          rw [geom_sum_eq h1.ne, div_eq_mul_inv, show (t * φ * Real.sqrt |bdSym F L k|) - 1 =
            -(1 - t * φ * Real.sqrt |bdSym F L k|) by ring, inv_neg]
          have : 0 ≤ (t * φ * Real.sqrt |bdSym F L k|) ^ N := pow_nonneg h0 N
          have hpos : 0 < (1 - t * φ * Real.sqrt |bdSym F L k|)⁻¹ := inv_pos.mpr (by linarith)
          nlinarith
  -- remainder
  have hKle : ∀ c d, mixedKer (bdP F L) t c d ≤ (1 - t)⁻¹ := by
    intro c d
    rw [← hKr c]
    exact Finset.single_le_sum (fun j _ => hK0 c j) (Finset.mem_univ d)
  have hrem : ∀ N : ℕ, (t ^ N • (bdP F L ^ N * mixedKer (bdP F L) t)) a b ≤ t ^ N * (1 - t)⁻¹ := by
    intro N
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht0 N)
    calc ∑ j, (bdP F L ^ N) a j * mixedKer (bdP F L) t j b ≤ ∑ j, (bdP F L ^ N) a j * (1 - t)⁻¹ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hKle j b) ((hpow N).1 a j)
      _ = (1 - t)⁻¹ := by rw [← Finset.sum_mul, (hpow N).2 a, one_mul]
  have hE : Real.exp (μ * cycDist a b / 2) ≤ Real.exp (μ * L) := by
    apply Real.exp_le_exp.mpr
    have : (cycDist a b : ℝ) ≤ L := by
      have := bd_cycDist_half a b
      have : cycDist a b ≤ L := by omega
      exact_mod_cast this
    nlinarith
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (div_pos hε (mul_pos (Real.exp_pos (μ * L)) (inv_pos.mpr (by linarith : (0:ℝ) < 1 - t)))) ht1
  have hdec := congrFun (congrFun (bd_K_partial (bdP F L) t hU N) a) b
  rw [Matrix.add_apply] at hdec
  rw [hdec, mul_add]
  have h1 := hpart N
  have h2 : Real.exp (μ * cycDist a b / 2) *
      (t ^ N • (bdP F L ^ N * mixedKer (bdP F L) t)) a b < ε := by
    have h0 : 0 ≤ (t ^ N • (bdP F L ^ N * mixedKer (bdP F L) t)) a b := by
      rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
      exact mul_nonneg (pow_nonneg ht0 N) (Finset.sum_nonneg fun j _ =>
        mul_nonneg ((hpow N).1 a j) (hK0 j b))
    calc Real.exp (μ * cycDist a b / 2) * (t ^ N • (bdP F L ^ N * mixedKer (bdP F L) t)) a b
        ≤ Real.exp (μ * L) * (t ^ N * (1 - t)⁻¹) :=
          mul_le_mul hE (hrem N) h0 (Real.exp_pos _).le
      _ = t ^ N * (Real.exp (μ * L) * (1 - t)⁻¹) := by ring
      _ < ε / (Real.exp (μ * L) * (1 - t)⁻¹) * (Real.exp (μ * L) * (1 - t)⁻¹) := by
          gcongr
      _ = ε := by
          have : Real.exp (μ * L) * (1 - t)⁻¹ ≠ 0 :=
            mul_ne_zero (Real.exp_pos _).ne' (inv_ne_zero (by linarith))
          field_simp
  linarith

/-- The diagonal of `(1 - tP)⁻¹` is the Fourier average of `(1 - tP̂)⁻¹`. -/
private lemma bd_diag_eq (F : ℕ → ℝ) (hF0 : ∀ r, 0 ≤ F r) (hF1 : ∑ y : Fin L, F (bdD y) = 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin L) :
    (L : ℝ)⁻¹ * ∑ k, (1 - t * bdSym F L k)⁻¹ = 1 + t * mixedKer (bdP F L) t a a := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hP0 := bdP_nonneg (L := L) F hF0
  have hrow := bdP_row_one (L := L) F hF1
  have hU := bd_isUnit (bdP F L) hP0 hrow t (by rw [abs_of_nonneg ht0]; exact ht1)
  have hE : BdEig (1 - t • bdP F L) (fun k => 1 + (-t) * (bdSym F L k : ℂ)) := by
    have h := bdEig_add (bdEig_one (L := L)) (bdEig_smul (bdEig_P (L := L) F) (-t))
    have e : (1 : Matrix (Fin L) (Fin L) ℝ) + (-t) • bdP F L = 1 - t • bdP F L := by
      rw [neg_smul, ← sub_eq_add_neg]
    rw [e] at h
    simpa using h
  have hne : ∀ k, (1 + (-t) * (bdSym F L k : ℂ)) ≠ 0 := by
    intro k h
    have h2 : 1 - t * bdSym F L k = 0 := by
      have := congrArg Complex.re h
      simpa [sub_eq_add_neg] using this
    have h3 := (abs_le.mp (bdSym_abs_le F hF0 hF1 k)).2
    have : t * bdSym F L k ≤ t := by nlinarith
    linarith
  have hI := bdEig_inv hE hne (bd_inv_mul (bdP F L) t hU)
  have hd := bdEig_diag hL hI a
  rw [bd_R_eq (bdP F L) t hU] at hd
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul] at hd
  have e : ∀ k, (1 + (-t) * (bdSym F L k : ℂ))⁻¹ = (((1 - t * bdSym F L k)⁻¹ : ℝ) : ℂ) := by
    intro k; push_cast; ring_nf
  simp_rw [e] at hd
  have h2 : ((1 + t * mixedKer (bdP F L) t a a : ℝ) : ℂ) =
      (((L : ℝ)⁻¹ * ∑ k, (1 - t * bdSym F L k)⁻¹ : ℝ) : ℂ) := by
    rw [hd]; push_cast; rfl
  exact (Complex.ofReal_injective h2).symm

end BdCore2

/-! ### Constants of the bounded-coupling kernel estimates -/

section BdCore3

/-- Second-moment constant. -/
private def bdC2 (μ₀ CP : ℝ) : ℝ := 16 * CP / μ₀ ^ 2

/-- Tilt rate. -/
private def bdCmu (μ₀ CP : ℝ) : ℝ := min (μ₀ / 2) (1 / (2 * (bdC2 μ₀ CP + 1)))

/-- Spectral gap constant. -/
private def bdc3 (C p₀ c₁ : ℝ) : ℝ := min (4 * c₁ / π ^ 2) (2 * p₀ / (C ^ 2 * π ^ 2))

private def bdc4 (C p₀ c₁ : ℝ) : ℝ := min (3 / 8) (bdc3 C p₀ c₁ / 4)

private def bdcB (C c₁ : ℝ) : ℝ := min (min 1 (2 * c₁ / π ^ 2)) (1 / (2 * (1 + C ^ 2 * π ^ 2)))

private lemma bdC2_pos {μ₀ CP : ℝ} (hμ₀ : 0 < μ₀) (hCP : 0 < CP) : 0 < bdC2 μ₀ CP := by
  unfold bdC2; positivity

private lemma bdCmu_pos {μ₀ CP : ℝ} (hμ₀ : 0 < μ₀) (hCP : 0 < CP) : 0 < bdCmu μ₀ CP := by
  have := bdC2_pos hμ₀ hCP
  unfold bdCmu; exact lt_min (by positivity) (by positivity)

private lemma bdCmu_le {μ₀ CP : ℝ} (hμ₀ : 0 < μ₀) (hCP : 0 < CP) :
    bdCmu μ₀ CP ≤ μ₀ / 2 ∧ bdCmu μ₀ CP ≤ 1 / 2 ∧ bdCmu μ₀ CP ^ 2 * bdC2 μ₀ CP ≤ 1 / 4 := by
  have hC2 := bdC2_pos hμ₀ hCP
  have h1 : bdCmu μ₀ CP ≤ 1 / (2 * (bdC2 μ₀ CP + 1)) := min_le_right _ _
  have h0 := bdCmu_pos hμ₀ hCP
  refine ⟨min_le_left _ _, h1.trans ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · have h2 : bdCmu μ₀ CP ^ 2 ≤ (1 / (2 * (bdC2 μ₀ CP + 1))) ^ 2 := pow_le_pow_left₀ h0.le h1 2
    have h3 : (1 / (2 * (bdC2 μ₀ CP + 1))) ^ 2 * bdC2 μ₀ CP ≤ 1 / 4 := by
      rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity)
        (by norm_num)]
      nlinarith
    nlinarith

private lemma bdc3_pos {C p₀ c₁ : ℝ} (hC : 0 < C) (hp₀ : 0 < p₀) (hc₁ : 0 < c₁) :
    0 < bdc3 C p₀ c₁ := by
  unfold bdc3; exact lt_min (by positivity) (by positivity)

private lemma bdc4_pos {C p₀ c₁ : ℝ} (hC : 0 < C) (hp₀ : 0 < p₀) (hc₁ : 0 < c₁) :
    0 < bdc4 C p₀ c₁ := by
  have := bdc3_pos hC hp₀ hc₁
  unfold bdc4; exact lt_min (by norm_num) (by positivity)

private lemma bdcB_pos {C c₁ : ℝ} (hc₁ : 0 < c₁) : 0 < bdcB C c₁ := by
  unfold bdcB; exact lt_min (lt_min one_pos (by positivity)) (by positivity)

/-- The scale `ℓ = min{L, ℓ_∞}`: `1 ≤ ℓ ≤ ℓ_∞`, and `ℓ = ℓ_∞` or `ℓ = L`. -/
private lemma bd_ell (L : ℕ) (hL : 1 ≤ L) (X : ℝ) (hX : 0 ≤ X) :
    1 ≤ min (L : ℝ) (1 + X) ∧ min (L : ℝ) (1 + X) ≤ 1 + X ∧
      (min (L : ℝ) (1 + X) = 1 + X ∨ min (L : ℝ) (1 + X) = L) := by
  refine ⟨le_min (by exact_mod_cast hL) (by linarith), min_le_right _ _, ?_⟩
  rcases le_total (L : ℝ) (1 + X) with h | h
  · right; exact min_eq_left h
  · left; exact min_eq_right h

private lemma bd_exp_conv (L : ℕ) (hL : 1 ≤ L) (X : ℝ) (hX : 0 ≤ X) (c : ℝ) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (d : ℝ) (hd0 : 0 ≤ d) (hd : 2 * d ≤ L) :
    Real.exp (-(c * d / (1 + X))) ≤ 2 * Real.exp (-(c * d / min (L : ℝ) (1 + X))) ∧
      Real.exp (c * d / min (L : ℝ) (1 + X)) ≤ 2 * Real.exp (c * d / (1 + X)) := by
  obtain ⟨h1, h2, h3⟩ := bd_ell L hL X hX
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  rcases h3 with e | e
  · rw [e]
    constructor <;> linarith [Real.exp_pos (-(c * d / (1 + X))), Real.exp_pos (c * d / (1 + X))]
  · rw [e]
    have hb : c * d / L ≤ 1 / 2 := by
      rw [div_le_iff₀ hLp]; nlinarith
    have hb0 : 0 ≤ c * d / L := by positivity
    have hb' : 0 ≤ c * d / (1 + X) := by positivity
    have e2 : Real.exp (1 / 2) ≤ 2 := by
      have := Real.exp_bound_div_one_sub_of_interval (x := 1 / 2) (by norm_num) (by norm_num)
      linarith
    constructor
    · have : Real.exp (-(c * d / (1 + X))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have : 1 ≤ 2 * Real.exp (-(c * d / L)) := by
        have h4 : Real.exp (-(c * d / L)) * Real.exp (c * d / L) = 1 := by
          rw [← Real.exp_add]; simp
        have h5 : Real.exp (c * d / L) ≤ 2 := (Real.exp_le_exp.mpr hb).trans e2
        nlinarith [Real.exp_pos (-(c * d / L))]
      linarith
    · have : Real.exp (c * d / L) ≤ 2 := (Real.exp_le_exp.mpr hb).trans e2
      have : 1 ≤ Real.exp (c * d / (1 + X)) := Real.one_le_exp hb'
      linarith

variable {L : ℕ} [NeZero L]

/-- (A.25) [ba:eq:coercivity]: `2c₁g²(1 - cos θ) ≤ 1 - P̂ ≤ C₂g²(1 - cos θ)`. -/
private lemma bd_sym_bounds (F : ℕ → ℝ) (g p₀ c₁ μ₀ CP : ℝ) (h : BdGood L F g p₀ c₁ μ₀ CP)
    (k : Fin L) :
    2 * c₁ * g ^ 2 * (1 - Real.cos (2 * π * k / L)) ≤ 1 - bdSym F L k ∧
      1 - bdSym F L k ≤ bdC2 μ₀ CP * g ^ 2 * (1 - Real.cos (2 * π * k / L)) := by
  have hcos : 0 ≤ 1 - Real.cos (2 * π * k / L) := by linarith [Real.cos_le_one (2 * π * k / L)]
  constructor
  · have h1 := bdSym_lower F h.nonneg h.sum h.hL k
    have h2 : 2 * (c₁ * g ^ 2) * (1 - Real.cos (2 * π * k / L)) ≤
        2 * F 1 * (1 - Real.cos (2 * π * k / L)) := by
      gcongr; exact h.one
    linarith
  · have h1 := bdSym_upper F h.nonneg h.sum k
    have h2 := bd_second F g p₀ c₁ μ₀ CP h
    unfold bdC2
    calc 1 - bdSym F L k
        ≤ (∑ y : Fin L, F (bdD y) * (bdD y : ℝ) ^ 2) * (1 - Real.cos (2 * π * k / L)) := h1
      _ ≤ 16 * CP / μ₀ ^ 2 * g ^ 2 * (1 - Real.cos (2 * π * k / L)) := by gcongr

/-- `1 - |P̂(k)| ≥ c₃ g² |k|²`. -/
private lemma bd_gap_abs (F : ℕ → ℝ) (C g p₀ c₁ μ₀ CP : ℝ) (h : BdGood L F g p₀ c₁ μ₀ CP)
    (hC : 0 < C) (hg : 0 ≤ g) (hgC : g ≤ C) (k : Fin L) :
    bdc3 C p₀ c₁ * g ^ 2 * torusAbs L k ^ 2 ≤ 1 - |bdSym F L k| := by
  have hL1 : 1 ≤ L := by have := h.hL; omega
  obtain ⟨hct, ht0, htπ⟩ := bd_cos_torus L hL1 k
  have hgap := bd_one_sub_cos_ge (torusAbs L k) ht0 htπ
  have hlow := (bd_sym_bounds F g p₀ c₁ μ₀ CP h k).1
  rw [hct] at hlow
  have hplus := bdSym_one_add F h.nonneg h.sum k
  have hz := h.zero
  have hc3a : bdc3 C p₀ c₁ ≤ 4 * c₁ / π ^ 2 := min_le_left _ _
  have hc3b : bdc3 C p₀ c₁ ≤ 2 * p₀ / (C ^ 2 * π ^ 2) := min_le_right _ _
  have hc3 := bdc3_pos hC h.hp₀ h.hc₁
  have hgt : g ^ 2 * torusAbs L k ^ 2 ≤ C ^ 2 * π ^ 2 := by
    have : g * torusAbs L k ≤ C * π := mul_le_mul hgC htπ ht0 hC.le
    nlinarith [mul_nonneg hg ht0]
  have hc1 := h.hc₁
  have hπ := Real.pi_pos
  rcases abs_cases (bdSym F L k) with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
  · -- `1 - P̂ ≥ 2c₁g²(1 - cos) ≥ (4c₁/π²) g²τ²`
    have : 4 * c₁ / π ^ 2 * g ^ 2 * torusAbs L k ^ 2 ≤ 1 - bdSym F L k := by
      have : 4 * c₁ / π ^ 2 * g ^ 2 * torusAbs L k ^ 2 =
          2 * c₁ * g ^ 2 * (2 / π ^ 2 * torusAbs L k ^ 2) := by ring
      rw [this]
      exact le_trans (by gcongr) hlow
    exact le_trans (by gcongr) this
  · -- `1 + P̂ ≥ 2p₀ ≥ (2p₀/(C²π²)) g²τ²`
    have : 2 * p₀ / (C ^ 2 * π ^ 2) * (g ^ 2 * torusAbs L k ^ 2) ≤ 2 * p₀ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [h.hp₀]
    calc bdc3 C p₀ c₁ * g ^ 2 * torusAbs L k ^ 2
        = bdc3 C p₀ c₁ * (g ^ 2 * torusAbs L k ^ 2) := by ring
      _ ≤ 2 * p₀ / (C ^ 2 * π ^ 2) * (g ^ 2 * torusAbs L k ^ 2) := by gcongr
      _ ≤ 2 * p₀ := this
      _ ≤ 1 - -bdSym F L k := by linarith

/-- (A.26) [ba:eq:inverse-average], symbol:
`c_B (δ + g²|k|²) ≤ 1 - tP̂(k) ≤ (1 + C₂/2)(δ + g²|k|²)`. -/
private lemma bd_tsym (F : ℕ → ℝ) (C g p₀ c₁ μ₀ CP : ℝ) (h : BdGood L F g p₀ c₁ μ₀ CP)
    (hC : 0 < C) (hg : 0 ≤ g) (hgC : g ≤ C) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (k : Fin L) :
    bdcB C c₁ * ((1 - t) + g ^ 2 * torusAbs L k ^ 2) ≤ 1 - t * bdSym F L k ∧
      1 - t * bdSym F L k ≤ (1 + bdC2 μ₀ CP / 2) * ((1 - t) + g ^ 2 * torusAbs L k ^ 2) := by
  have hL1 : 1 ≤ L := by have := h.hL; omega
  obtain ⟨hct, ht0', htπ⟩ := bd_cos_torus L hL1 k
  obtain ⟨hlow, hup⟩ := bd_sym_bounds F g p₀ c₁ μ₀ CP h k
  rw [hct] at hlow hup
  have hgap := bd_one_sub_cos_ge (torusAbs L k) ht0' htπ
  have hcosu := bd_one_sub_cos_le (torusAbs L k)
  have hs1 := bdSym_abs_le F h.nonneg h.sum k
  have hC2 := bdC2_pos h.hμ₀ h.hCP
  have hc1 := h.hc₁
  have hπ := Real.pi_pos
  have hτ2 : 0 ≤ g ^ 2 * torusAbs L k ^ 2 := by positivity
  have e : 1 - t * bdSym F L k = (1 - t) + t * (1 - bdSym F L k) := by ring
  constructor
  · rw [e]
    by_cases ht : 1 / 2 ≤ t
    · have h1 : 2 * c₁ / π ^ 2 * (g ^ 2 * torusAbs L k ^ 2) ≤ t * (1 - bdSym F L k) := by
        have : 2 * c₁ * g ^ 2 * (2 / π ^ 2 * torusAbs L k ^ 2) ≤ 1 - bdSym F L k :=
          le_trans (by gcongr) hlow
        have h0 : 0 ≤ 1 - bdSym F L k := by linarith [(abs_le.mp hs1).2]
        have : 2 * c₁ / π ^ 2 * (g ^ 2 * torusAbs L k ^ 2) ≤ (1 / 2) * (1 - bdSym F L k) := by
          have : 2 * c₁ * g ^ 2 * (2 / π ^ 2 * torusAbs L k ^ 2) =
              2 * (2 * c₁ / π ^ 2 * (g ^ 2 * torusAbs L k ^ 2)) := by ring
          linarith
        nlinarith
      have hb1 : bdcB C c₁ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
      have hb2 : bdcB C c₁ ≤ 2 * c₁ / π ^ 2 := (min_le_left _ _).trans (min_le_right _ _)
      have hb0 := bdcB_pos (C := C) hc1
      nlinarith
    · push Not at ht
      have hb3 : bdcB C c₁ ≤ 1 / (2 * (1 + C ^ 2 * π ^ 2)) := min_le_right _ _
      have hb0 := bdcB_pos (C := C) hc1
      have hgt : g ^ 2 * torusAbs L k ^ 2 ≤ C ^ 2 * π ^ 2 := by
        have : g * torusAbs L k ≤ C * π := mul_le_mul hgC htπ ht0' hC.le
        nlinarith [mul_nonneg hg ht0']
      have h1 : bdcB C c₁ * ((1 - t) + g ^ 2 * torusAbs L k ^ 2) ≤ 1 / 2 := by
        calc bdcB C c₁ * ((1 - t) + g ^ 2 * torusAbs L k ^ 2)
            ≤ 1 / (2 * (1 + C ^ 2 * π ^ 2)) * (1 + C ^ 2 * π ^ 2) := by
              apply mul_le_mul hb3 (by linarith) (by positivity) (by positivity)
          _ = 1 / 2 := by field_simp
      have h2 : 0 ≤ t * (1 - bdSym F L k) := mul_nonneg ht0 (by linarith [(abs_le.mp hs1).2])
      linarith
  · rw [e]
    have h0 : 0 ≤ 1 - bdSym F L k := by linarith [(abs_le.mp hs1).2]
    have h1 : t * (1 - bdSym F L k) ≤ 1 - bdSym F L k := mul_le_of_le_one_left h0 ht1.le
    have h2 : 1 - bdSym F L k ≤ bdC2 μ₀ CP / 2 * (g ^ 2 * torusAbs L k ^ 2) := by
      calc 1 - bdSym F L k ≤ bdC2 μ₀ CP * g ^ 2 * (torusAbs L k ^ 2 / 2) :=
            le_trans hup (by gcongr)
        _ = _ := by ring
    have h3 : 0 ≤ 1 - t := by linarith
    nlinarith

end BdCore3

section BdCore4

variable {L : ℕ} [NeZero L]

private lemma bdGood_p₀_le (F : ℕ → ℝ) (g p₀ c₁ μ₀ CP : ℝ) (h : BdGood L F g p₀ c₁ μ₀ CP) :
    p₀ ≤ 1 := by
  have h1 := Finset.single_le_sum (f := fun y : Fin L => F (bdD y)) (fun y _ => h.nonneg _)
    (Finset.mem_univ 0)
  simp only [bdD_zero] at h1
  linarith [h.zero, h.sum]

/-- The tilt rate `μ = c_μ/ℓ_∞` satisfies `φ_μ ≤ 1 + δ/4`. -/
private lemma bd_phi_tilt (F : ℕ → ℝ) (γ g p₀ c₁ μ₀ CP : ℝ) (h : BdGood L F g p₀ c₁ μ₀ CP)
    (hg : 0 ≤ g) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (t : ℝ) (ht1 : t < 1) :
    let μ := bdCmu μ₀ CP / (1 + g / Real.sqrt (γ * (1 - t)))
    0 ≤ μ ∧ μ ≤ μ₀ / 2 ∧ bdPhi F L μ ≤ 1 + (1 - t) / 4 := by
  intro μ
  have hδ : 0 < 1 - t := by linarith
  have hsq : 0 < Real.sqrt (γ * (1 - t)) := Real.sqrt_pos.mpr (by positivity)
  set X := g / Real.sqrt (γ * (1 - t)) with hX
  have hX0 : 0 ≤ X := div_nonneg hg hsq.le
  obtain ⟨hc1, hc2, hc3⟩ := bdCmu_le h.hμ₀ h.hCP
  have hc0 := bdCmu_pos h.hμ₀ h.hCP
  have hμ0 : 0 ≤ μ := by positivity
  have hμle : μ ≤ bdCmu μ₀ CP := div_le_self hc0.le (by linarith)
  refine ⟨hμ0, hμle.trans hc1, ?_⟩
  have hphi := bd_phi_le F g p₀ c₁ μ₀ CP h μ hμ0 (hμle.trans hc1)
  -- `μ g ≤ c_μ √(γδ)`
  have hgX : g ≤ (1 + X) * Real.sqrt (γ * (1 - t)) := by
    have : X * Real.sqrt (γ * (1 - t)) = g := by rw [hX]; field_simp
    nlinarith
  have hμg : μ * g ≤ bdCmu μ₀ CP * Real.sqrt (γ * (1 - t)) := by
    change bdCmu μ₀ CP / (1 + X) * g ≤ _
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  have hμg2 : μ ^ 2 * g ^ 2 ≤ bdCmu μ₀ CP ^ 2 * (1 - t) := by
    have h1 : (μ * g) ^ 2 ≤ (bdCmu μ₀ CP * Real.sqrt (γ * (1 - t))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hμg 2
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)] at h1
    have h2 : bdCmu μ₀ CP ^ 2 * (γ * (1 - t)) ≤ bdCmu μ₀ CP ^ 2 * (1 - t) :=
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hδ.le hγ1) (by positivity)
    linarith
  have hC2 := bdC2_pos h.hμ₀ h.hCP
  calc bdPhi F L μ ≤ 1 + μ ^ 2 * (16 * CP / μ₀ ^ 2 * g ^ 2) := hphi
    _ = 1 + bdC2 μ₀ CP * (μ ^ 2 * g ^ 2) := by unfold bdC2; ring
    _ ≤ 1 + bdC2 μ₀ CP * (bdCmu μ₀ CP ^ 2 * (1 - t)) := by gcongr
    _ ≤ 1 + (1 - t) / 4 := by nlinarith

/-- (6.3) [fo:eq:kernel-bounds] for a good profile: `K ≤ C_K/(δℓ) e^{-c d/ℓ}`. -/
private lemma bd_profile (F : ℕ → ℝ) (C Cm γ g p₀ c₁ μ₀ CP : ℝ) (h : BdGood L F g p₀ c₁ μ₀ CP)
    (hC : 0 < C) (hCm : 1 ≤ Cm) (hg : 0 ≤ g) (hgC : g ≤ C) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hγC : 1 ≤ γ * Cm ^ 2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (a b : Fin L) :
    mixedKer (bdP F L) t a b ≤
      10 * (2 + 2 * Cm) / bdc4 C p₀ c₁ /
          ((1 - t) * min (L : ℝ) (1 + g / Real.sqrt (γ * (1 - t)))) *
        Real.exp (-(bdCmu μ₀ CP / 2 * cycDist a b /
          min (L : ℝ) (1 + g / Real.sqrt (γ * (1 - t))))) := by
  have hL1 : 1 ≤ L := by have := h.hL; omega
  have hδ : 0 < 1 - t := by linarith
  have hsq : 0 < Real.sqrt (γ * (1 - t)) := Real.sqrt_pos.mpr (by positivity)
  set X := g / Real.sqrt (γ * (1 - t)) with hX
  have hX0 : 0 ≤ X := div_nonneg hg hsq.le
  set ℓ := min (L : ℝ) (1 + X) with hℓ
  obtain ⟨hℓ1, hℓX, -⟩ := bd_ell L hL1 X hX0
  obtain ⟨hμ0, hμ2, hφ⟩ := bd_phi_tilt F γ g p₀ c₁ μ₀ CP h hg hγ hγ1 t ht1
  set μ := bdCmu μ₀ CP / (1 + X) with hμ
  set φ := bdPhi F L μ with hφdef
  have hφ1 := bd_phi_ge_one F h.nonneg h.sum μ
  have htφ : t * φ ≤ 1 - 3 * (1 - t) / 4 := by nlinarith
  have htφ1 : t * φ < 1 := by linarith
  have htilt := bd_K_tilt F h.nonneg h.sum μ hμ0 t ht0 ht1 htφ1 a b
  have hc4 := bdc4_pos hC h.hp₀ h.hc₁
  have hp₀1 := bdGood_p₀_le F g p₀ c₁ μ₀ CP h
  -- each Fourier term
  have hterm : ∀ k, (1 - t * φ * Real.sqrt |bdSym F L k|)⁻¹ ≤
      (bdc4 C p₀ c₁)⁻¹ * ((1 - t) + g ^ 2 * torusAbs L k ^ 2)⁻¹ := by
    intro k
    have hgap := bd_gap_abs F C g p₀ c₁ μ₀ CP h hC hg hgC k
    have hs1 := bdSym_abs_le F h.nonneg h.sum k
    set Y := bdc3 C p₀ c₁ * g ^ 2 * torusAbs L k ^ 2 / 2 with hY
    have hY0 : 0 ≤ Y := by have := bdc3_pos hC h.hp₀ h.hc₁; positivity
    have hY1 : Y ≤ 1 := by linarith [abs_nonneg (bdSym F L k)]
    have hρ : Real.sqrt |bdSym F L k| ≤ 1 - Y := by
      have h1 : Real.sqrt |bdSym F L k| ≤ (1 + |bdSym F L k|) / 2 := by
        have := Real.sqrt_nonneg |bdSym F L k|
        have h2 := Real.sq_sqrt (abs_nonneg (bdSym F L k))
        nlinarith [sq_nonneg (Real.sqrt |bdSym F L k| - 1)]
      linarith
    have hρ0 := Real.sqrt_nonneg |bdSym F L k|
    have htφ0 : 0 ≤ t * φ := mul_nonneg ht0 (by linarith)
    have hprod : t * φ * Real.sqrt |bdSym F L k| ≤ (1 - 3 * (1 - t) / 4) * (1 - Y) :=
      mul_le_mul htφ hρ hρ0 (by linarith)
    have hlow : bdc4 C p₀ c₁ * ((1 - t) + g ^ 2 * torusAbs L k ^ 2) ≤
        1 - t * φ * Real.sqrt |bdSym F L k| := by
      have hc4a : bdc4 C p₀ c₁ ≤ 3 / 8 := min_le_left _ _
      have hc4b : bdc4 C p₀ c₁ ≤ bdc3 C p₀ c₁ / 4 := min_le_right _ _
      have hgt : 0 ≤ g ^ 2 * torusAbs L k ^ 2 := by positivity
      have e1 : bdc4 C p₀ c₁ * (g ^ 2 * torusAbs L k ^ 2) ≤ Y / 2 := by
        rw [hY]
        have : bdc4 C p₀ c₁ * (g ^ 2 * torusAbs L k ^ 2) ≤
            bdc3 C p₀ c₁ / 4 * (g ^ 2 * torusAbs L k ^ 2) := by gcongr
        linarith
      have e2 : bdc4 C p₀ c₁ * (1 - t) ≤ 3 * (1 - t) / 8 := by nlinarith
      have e3 : 3 * (1 - t) / 4 * Y ≤ (3 * (1 - t) / 4 + Y) / 2 := by nlinarith
      nlinarith
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) (by linarith)
  have hsum : (L : ℝ)⁻¹ * ∑ k, (1 - t * φ * Real.sqrt |bdSym F L k|)⁻¹ ≤
      (bdc4 C p₀ c₁)⁻¹ * ((2 + 2 * Cm) / ((1 - t) * ℓ)) := by
    have hRS := bdRS_le Cm γ hγ hγC hCm L hL1 (1 - t) g hδ hg
    calc (L : ℝ)⁻¹ * ∑ k, (1 - t * φ * Real.sqrt |bdSym F L k|)⁻¹
        ≤ (L : ℝ)⁻¹ * ∑ k, (bdc4 C p₀ c₁)⁻¹ * ((1 - t) + g ^ 2 * torusAbs L k ^ 2)⁻¹ := by
          gcongr with k; exact hterm k
      _ = (bdc4 C p₀ c₁)⁻¹ * bdRS L (1 - t) g := by
          unfold bdRS; rw [← Finset.mul_sum]; ring
      _ ≤ _ := by gcongr
  have hB : Real.exp (μ * cycDist a b / 2) * mixedKer (bdP F L) t a b ≤
      5 * (2 + 2 * Cm) / bdc4 C p₀ c₁ / ((1 - t) * ℓ) := by
    refine htilt.trans ?_
    have h45 : 4 * φ ≤ 5 := by linarith
    calc 4 * φ * ((L : ℝ)⁻¹ * ∑ k, (1 - t * φ * Real.sqrt |bdSym F L k|)⁻¹)
        ≤ 4 * φ * ((bdc4 C p₀ c₁)⁻¹ * ((2 + 2 * Cm) / ((1 - t) * ℓ))) :=
          mul_le_mul_of_nonneg_left hsum (by linarith)
      _ ≤ 5 * ((bdc4 C p₀ c₁)⁻¹ * ((2 + 2 * Cm) / ((1 - t) * ℓ))) := by
          have : 0 < (1 - t) * ℓ := by positivity
          exact mul_le_mul_of_nonneg_right h45 (by positivity)
      _ = _ := by field_simp
  have hd0 : (0 : ℝ) ≤ cycDist a b := Nat.cast_nonneg _
  have hdL : 2 * (cycDist a b : ℝ) ≤ L := by exact_mod_cast bd_cycDist_half a b
  obtain ⟨hc1', hc2', -⟩ := bdCmu_le h.hμ₀ h.hCP
  have hconv := (bd_exp_conv L hL1 X hX0 (bdCmu μ₀ CP / 2)
    (by have := bdCmu_pos h.hμ₀ h.hCP; positivity) (by linarith) (cycDist a b) hd0 hdL).1
  have e1 : Real.exp (-(bdCmu μ₀ CP / 2 * cycDist a b / (1 + X))) =
      (Real.exp (μ * cycDist a b / 2))⁻¹ := by
    rw [← Real.exp_neg, hμ]; ring_nf
  rw [e1] at hconv
  have hK0 : 0 ≤ mixedKer (bdP F L) t a b :=
    (mixedKer_nonneg_row (bdP F L) (bdP_nonneg F h.nonneg) (bdP_row_one F h.sum) t ht0 ht1).1 a b
  have hE := Real.exp_pos (μ * cycDist a b / 2)
  have hK : mixedKer (bdP F L) t a b ≤
      5 * (2 + 2 * Cm) / bdc4 C p₀ c₁ / ((1 - t) * ℓ) * (Real.exp (μ * cycDist a b / 2))⁻¹ := by
    rw [le_mul_inv_iff₀ hE]; linarith
  calc mixedKer (bdP F L) t a b
      ≤ 5 * (2 + 2 * Cm) / bdc4 C p₀ c₁ / ((1 - t) * ℓ) * (Real.exp (μ * cycDist a b / 2))⁻¹ := hK
    _ ≤ 5 * (2 + 2 * Cm) / bdc4 C p₀ c₁ / ((1 - t) * ℓ) *
          (2 * Real.exp (-(bdCmu μ₀ CP / 2 * cycDist a b / ℓ))) := by gcongr
    _ = _ := by ring

/-- (A.24) [ba:eq:weighted-rows], second row, for a good profile. -/
private lemma bd_weighted (F : ℕ → ℝ) (γ g p₀ c₁ μ₀ CP : ℝ) (h : BdGood L F g p₀ c₁ μ₀ CP)
    (hg : 0 ≤ g) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin L) :
    ∑ b, Real.exp (bdCmu μ₀ CP * cycDist a b / min (L : ℝ) (1 + g / Real.sqrt (γ * (1 - t)))) *
      mixedKer (bdP F L) t a b ≤ 7 / (1 - t) := by
  have hL1 : 1 ≤ L := by have := h.hL; omega
  have hδ : 0 < 1 - t := by linarith
  have hsq : 0 < Real.sqrt (γ * (1 - t)) := Real.sqrt_pos.mpr (by positivity)
  set X := g / Real.sqrt (γ * (1 - t)) with hX
  have hX0 : 0 ≤ X := div_nonneg hg hsq.le
  obtain ⟨hμ0, hμ2, hφ⟩ := bd_phi_tilt F γ g p₀ c₁ μ₀ CP h hg hγ hγ1 t ht1
  set μ := bdCmu μ₀ CP / (1 + X) with hμ
  have hφ1 := bd_phi_ge_one F h.nonneg h.sum μ
  have htφ : t * bdPhi F L μ ≤ 1 - 3 * (1 - t) / 4 := by nlinarith
  have hKV := bd_KV F h.nonneg h.sum μ hμ0 t ht0 ht1 (by linarith) a a
  rw [bd_cycDist_self, Nat.cast_zero, mul_zero, Real.cosh_zero, mul_one] at hKV
  obtain ⟨hK0, -⟩ := mixedKer_nonneg_row (bdP F L) (bdP_nonneg F h.nonneg) (bdP_row_one F h.sum)
    t ht0 ht1
  obtain ⟨hc1', hc2', -⟩ := bdCmu_le h.hμ₀ h.hCP
  have hc0 := bdCmu_pos h.hμ₀ h.hCP
  have hterm : ∀ b, Real.exp (bdCmu μ₀ CP * cycDist a b / min (L : ℝ) (1 + X)) *
      mixedKer (bdP F L) t a b ≤ 4 * (mixedKer (bdP F L) t a b * Real.cosh (μ * cycDist a b)) := by
    intro b
    have hd0 : (0 : ℝ) ≤ cycDist a b := Nat.cast_nonneg _
    have hdL : 2 * (cycDist a b : ℝ) ≤ L := by exact_mod_cast bd_cycDist_half a b
    have hconv := (bd_exp_conv L hL1 X hX0 (bdCmu μ₀ CP) hc0.le (by linarith) (cycDist a b) hd0
      hdL).2
    have e1 : bdCmu μ₀ CP * cycDist a b / (1 + X) = μ * cycDist a b := by rw [hμ]; ring
    rw [e1] at hconv
    have : Real.exp (μ * cycDist a b) ≤ 2 * Real.cosh (μ * cycDist a b) := by
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-(μ * cycDist a b))]
    nlinarith [hK0 a b]
  calc ∑ b, Real.exp (bdCmu μ₀ CP * cycDist a b / min (L : ℝ) (1 + X)) * mixedKer (bdP F L) t a b
      ≤ ∑ b, 4 * (mixedKer (bdP F L) t a b * Real.cosh (μ * cycDist a b)) :=
        Finset.sum_le_sum fun b _ => hterm b
    _ = 4 * ∑ b, mixedKer (bdP F L) t a b * Real.cosh (μ * cycDist a b) := by rw [Finset.mul_sum]
    _ ≤ 4 * (bdPhi F L μ / (1 - t * bdPhi F L μ)) := by gcongr
    _ ≤ 7 / (1 - t) := by
        have hpos : 0 < 1 - t * bdPhi F L μ := by linarith
        rw [mul_div_assoc', div_le_div_iff₀ hpos hδ]
        nlinarith

/-- (A.26) [ba:eq:inverse-average] and the bounds on the diagonal of `K`, for a good profile. -/
private lemma bd_diag (F : ℕ → ℝ) (C Cm γ g p₀ c₁ μ₀ CP : ℝ) (h : BdGood L F g p₀ c₁ μ₀ CP)
    (hC : 0 < C) (hCm : 1 ≤ Cm) (hg : 0 ≤ g) (hgC : g ≤ C) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hγC : 1 ≤ γ * Cm ^ 2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin L) :
    let ℓ := min (L : ℝ) (1 + g / Real.sqrt (γ * (1 - t)))
    1 / (4 * π * (1 + bdC2 μ₀ CP / 2)) / ((1 - t) * ℓ) ≤ 1 + t * mixedKer (bdP F L) t a a ∧
      1 + t * mixedKer (bdP F L) t a a ≤ (2 + 2 * Cm) / bdcB C c₁ / ((1 - t) * ℓ) ∧
      p₀ / (8 * π * (1 + bdC2 μ₀ CP / 2)) / ((1 - t) * ℓ) ≤ mixedKer (bdP F L) t a a := by
  intro ℓ
  have hL1 : 1 ≤ L := by have := h.hL; omega
  have hδ : 0 < 1 - t := by linarith
  have hsq : 0 < Real.sqrt (γ * (1 - t)) := Real.sqrt_pos.mpr (by positivity)
  have hX0 : 0 ≤ g / Real.sqrt (γ * (1 - t)) := div_nonneg hg hsq.le
  obtain ⟨hℓ1, -, -⟩ := bd_ell L hL1 _ hX0
  have hC2 := bdC2_pos h.hμ₀ h.hCP
  have hcB := bdcB_pos (C := C) h.hc₁
  have hid := bd_diag_eq F h.nonneg h.sum t ht0 ht1 a
  have hts := fun k => bd_tsym F C g p₀ c₁ μ₀ CP h hC hg hgC t ht0 ht1 k
  have hpos : ∀ k, 0 < (1 - t) + g ^ 2 * torusAbs L k ^ 2 := fun k => by positivity
  have hup : 1 + t * mixedKer (bdP F L) t a a ≤ (2 + 2 * Cm) / bdcB C c₁ / ((1 - t) * ℓ) := by
    rw [← hid]
    calc (L : ℝ)⁻¹ * ∑ k, (1 - t * bdSym F L k)⁻¹
        ≤ (L : ℝ)⁻¹ * ∑ k, (bdcB C c₁)⁻¹ * ((1 - t) + g ^ 2 * torusAbs L k ^ 2)⁻¹ := by
          gcongr with k
          rw [← mul_inv]
          exact inv_anti₀ (by have := hpos k; positivity) (hts k).1
      _ = (bdcB C c₁)⁻¹ * bdRS L (1 - t) g := by unfold bdRS; rw [← Finset.mul_sum]; ring
      _ ≤ (bdcB C c₁)⁻¹ * ((2 + 2 * Cm) / ((1 - t) * ℓ)) := by
          gcongr; exact bdRS_le Cm γ hγ hγC hCm L hL1 (1 - t) g hδ hg
      _ = _ := by field_simp
  have hlo : 1 / (4 * π * (1 + bdC2 μ₀ CP / 2)) / ((1 - t) * ℓ) ≤
      1 + t * mixedKer (bdP F L) t a a := by
    rw [← hid]
    calc 1 / (4 * π * (1 + bdC2 μ₀ CP / 2)) / ((1 - t) * ℓ)
        = (1 + bdC2 μ₀ CP / 2)⁻¹ * (1 / (4 * π) / ((1 - t) * ℓ)) := by field_simp
      _ ≤ (1 + bdC2 μ₀ CP / 2)⁻¹ * bdRS L (1 - t) g := by
          gcongr; exact bdRS_ge γ hγ hγ1 L hL1 (1 - t) g hδ hg
      _ = (L : ℝ)⁻¹ * ∑ k, (1 + bdC2 μ₀ CP / 2)⁻¹ * ((1 - t) + g ^ 2 * torusAbs L k ^ 2)⁻¹ := by
          unfold bdRS; rw [← Finset.mul_sum]; ring
      _ ≤ (L : ℝ)⁻¹ * ∑ k, (1 - t * bdSym F L k)⁻¹ := by
          gcongr with k
          rw [← mul_inv]
          have h1 := (hts k).1
          have h2 : 0 < 1 - t * bdSym F L k := lt_of_lt_of_le (by have := hpos k; positivity) h1
          exact inv_anti₀ h2 (hts k).2
  refine ⟨hlo, hup, ?_⟩
  -- the diagonal of `K`
  have hP0 := bdP_nonneg (L := L) F h.nonneg
  have hrow := bdP_row_one (L := L) F h.sum
  have hU := bd_isUnit (bdP F L) hP0 hrow t (by rw [abs_of_nonneg ht0]; exact ht1)
  obtain ⟨hK0, -⟩ := mixedKer_nonneg_row (bdP F L) hP0 hrow t ht0 ht1
  have hKP : p₀ ≤ mixedKer (bdP F L) t a a := by
    have hK := congrFun (congrFun (bd_K_eq (bdP F L) t hU).1 a) a
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at hK
    have h1 : 0 ≤ ∑ j, bdP F L a j * mixedKer (bdP F L) t j a :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hP0 a j) (hK0 j a)
    have h2 : bdP F L a a = F 0 := by simp [bdP, bd_cycDist_self]
    rw [hK, h2]
    nlinarith [h.zero]
  have hp₀1 := bdGood_p₀_le F g p₀ c₁ μ₀ CP h
  set c₆ := 1 / (4 * π * (1 + bdC2 μ₀ CP / 2)) with hc₆
  have hc₆0 : 0 < c₆ := by rw [hc₆]; positivity
  have hδℓ : 0 < (1 - t) * ℓ := by positivity
  have e : p₀ / (8 * π * (1 + bdC2 μ₀ CP / 2)) / ((1 - t) * ℓ) = p₀ * (c₆ / 2) / ((1 - t) * ℓ) := by
    rw [hc₆]; field_simp; ring
  rw [e]
  by_cases hc : c₆ / 2 ≤ (1 - t) * ℓ
  · have : c₆ / 2 / ((1 - t) * ℓ) ≤ 1 := by rw [div_le_one hδℓ]; exact hc
    calc p₀ * (c₆ / 2) / ((1 - t) * ℓ) = p₀ * (c₆ / 2 / ((1 - t) * ℓ)) := by ring
      _ ≤ p₀ * 1 := by gcongr; linarith [h.hp₀]
      _ ≤ _ := by linarith
  · push Not at hc
    have h1 : 1 < c₆ / 2 / ((1 - t) * ℓ) := by rw [one_lt_div hδℓ]; exact hc
    have h2 : c₆ / ((1 - t) * ℓ) = 2 * (c₆ / 2 / ((1 - t) * ℓ)) := by ring
    have h3 : t * mixedKer (bdP F L) t a a ≤ mixedKer (bdP F L) t a a :=
      mul_le_of_le_one_left (hK0 a a) ht1.le
    have h4 : c₆ / 2 / ((1 - t) * ℓ) ≤ mixedKer (bdP F L) t a a := by
      rw [hc₆] at h2 ⊢; linarith
    calc p₀ * (c₆ / 2) / ((1 - t) * ℓ) = p₀ * (c₆ / 2 / ((1 - t) * ℓ)) := by ring
      _ ≤ 1 * (c₆ / 2 / ((1 - t) * ℓ)) := by gcongr
      _ ≤ _ := by linarith

end BdCore4

/-! ### Periodized geometric kernels on `ℤ_L` -/

section BdGeom

/-- `c - a` on `ℤ_L` as a natural number below `L`. -/
private def bgD (L : ℕ) (a c : Fin L) : ℕ :=
  if a.val ≤ c.val then c.val - a.val else c.val + L - a.val

private lemma bgD_lt {L : ℕ} (a c : Fin L) : bgD L a c < L := by
  have := a.isLt; have := c.isLt
  unfold bgD; split_ifs <;> omega

private lemma bg_mod_eq (u v L : ℕ) (hu : u < L) (hv : v < L) :
    (u + L - v) % L = if v ≤ u then u - v else u + L - v := by
  split_ifs with h
  · have : u + L - v = (u - v) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

private lemma bg_cycDist_cases {L : ℕ} (a c : Fin L) :
    cycDist a c = bgD L a c ∨ (cycDist a c = L - bgD L a c ∧ bgD L a c ≠ 0) := by
  have ha := a.isLt; have hc := c.isLt
  unfold cycDist bgD
  rw [bg_mod_eq _ _ _ ha hc, bg_mod_eq _ _ _ hc ha]
  split_ifs <;> omega

/-- The successor on `ℤ_L`. -/
private def bgSucc {L : ℕ} (a : Fin L) : Fin L :=
  ⟨if a.val + 1 < L then a.val + 1 else 0, by have := a.isLt; split_ifs <;> omega⟩

/-- The predecessor on `ℤ_L`. -/
private def bgPred {L : ℕ} (a : Fin L) : Fin L :=
  ⟨if 0 < a.val then a.val - 1 else L - 1, by have := a.isLt; split_ifs <;> omega⟩

private lemma bg_succ_mod_eq (L x : ℕ) (hx : x < L) :
    (x + 1) % L = if x + 1 < L then x + 1 else 0 := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : x + 1 = L := by omega
    rw [this, Nat.mod_self]

private lemma bg_cycleAdj_apply {L : ℕ} (a k : Fin L) :
    cycleAdj L a k = (if k = bgSucc a then 1 else 0) + (if k = bgPred a then 1 else 0) := by
  simp only [cycleAdj, Matrix.of_apply]
  have hk := k.isLt
  have ha := a.isLt
  have h1 : (k.val = (a.val + 1) % L) ↔ k = bgSucc a := by
    rw [bg_succ_mod_eq L a.val ha, Fin.ext_iff]
    simp only [bgSucc]
  have h2 : (a.val = (k.val + 1) % L) ↔ k = bgPred a := by
    rw [bg_succ_mod_eq L k.val hk, Fin.ext_iff]
    simp only [bgPred]
    split_ifs <;> omega
  rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl]

section Field

variable {𝕜 : Type*} [Field 𝕜]

/-- The periodized two-sided geometric profile `k ↦ (τ^k + τ^{L-k})/(1 - τ^L)`. -/
private def bgV (τ : 𝕜) (L k : ℕ) : 𝕜 := (τ ^ k + τ ^ (L - k)) / (1 - τ ^ L)

/-- The circulant matrix with profile `bgV τ L`. -/
private def bgC (τ : 𝕜) (L : ℕ) : Matrix (Fin L) (Fin L) 𝕜 :=
  Matrix.of fun a c => bgV τ L (bgD L a c)

private lemma bgV_L (τ : 𝕜) (L : ℕ) : bgV τ L L = bgV τ L 0 := by
  unfold bgV
  simp only [Nat.sub_self, Nat.sub_zero, pow_zero]
  rw [add_comm]

private lemma bgV_symm (τ : 𝕜) (L k : ℕ) (hk : k ≤ L) : bgV τ L (L - k) = bgV τ L k := by
  unfold bgV; rw [Nat.sub_sub_self hk, add_comm]

/-- The profile depends only on the cyclic distance. -/
private lemma bgV_cycDist (τ : 𝕜) {L : ℕ} (a c : Fin L) :
    bgV τ L (bgD L a c) = bgV τ L (cycDist a c) := by
  rcases bg_cycDist_cases a c with e | ⟨e, -⟩
  · rw [e]
  · rw [e, bgV_symm τ L _ (bgD_lt a c).le]

private lemma bgV_rec_int {τ : 𝕜} (hτ : τ ≠ 0) (L d : ℕ) (hd : 1 ≤ d) (hd' : d + 1 ≤ L) :
    bgV τ L (d - 1) + bgV τ L (d + 1) = (τ + τ⁻¹) * bgV τ L d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, L = e + n + 2 := ⟨L - e - 2, by omega⟩
  unfold bgV
  have e1 : e + n + 2 - (e + 1 - 1) = n + 2 := by omega
  have e2 : e + n + 2 - (e + 1 + 1) = n := by omega
  have e3 : e + n + 2 - (e + 1) = n + 1 := by omega
  rw [e1, e2, e3, Nat.add_sub_cancel]
  rw [← add_div, mul_div_assoc']
  congr 1
  field_simp
  ring

private lemma bgV_rec_zero {τ : 𝕜} (hτ : τ ≠ 0) {L : ℕ} (hD : 1 - τ ^ L ≠ 0) (hL : 2 ≤ L) :
    bgV τ L (L - 1) + bgV τ L 1 = (τ + τ⁻¹) * bgV τ L 0 - (τ⁻¹ - τ) := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 2 := ⟨L - 2, by omega⟩
  unfold bgV
  have e2 : n + 2 - 1 = n + 1 := by omega
  have e3 : n + 2 - (n + 1) = 1 := by omega
  rw [e2, e3, Nat.sub_zero]
  field_simp
  ring

/-- `((τ + τ⁻¹) I - A_L) G_τ = (τ⁻¹ - τ) I`. -/
private theorem bgC_mul {τ : 𝕜} (hτ : τ ≠ 0) {L : ℕ} (hD : 1 - τ ^ L ≠ 0) (hL : 3 ≤ L)
    (A : Matrix (Fin L) (Fin L) 𝕜)
    (hA : ∀ a k, A a k = (if k = bgSucc a then 1 else 0) + (if k = bgPred a then 1 else 0)) :
    ((τ + τ⁻¹) • (1 : Matrix (Fin L) (Fin L) 𝕜) - A) * bgC τ L =
      (τ⁻¹ - τ) • (1 : Matrix (Fin L) (Fin L) 𝕜) := by
  ext a c
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin L,
      ((τ + τ⁻¹) • (1 : Matrix (Fin L) (Fin L) 𝕜) - A) a k * bgC τ L k c =
        (if k = a then (τ + τ⁻¹) * bgC τ L k c else 0) -
        ((if k = bgSucc a then bgC τ L k c else 0) +
        (if k = bgPred a then bgC τ L k c else 0)) := by
    intro k
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      hA, eq_comm (a := a) (b := k)]
    split_ifs <;> ring
  simp_rw [key]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [bgC, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hA' := a.isLt
  have hC := c.isLt
  have hs : (bgSucc a).val = if a.val + 1 < L then a.val + 1 else 0 := rfl
  have hp : (bgPred a).val = if 0 < a.val then a.val - 1 else L - 1 := rfl
  by_cases hac : a = c
  · subst hac
    have e0 : bgD L a a = 0 := by simp [bgD]
    have e1 : bgD L (bgSucc a) a = L - 1 := by
      unfold bgD; rw [hs]; split_ifs <;> omega
    have e2 : bgD L (bgPred a) a = 1 := by
      unfold bgD; rw [hp]; split_ifs <;> omega
    rw [e0, e1, e2]
    simp only [↓reduceIte, mul_one]
    linear_combination (-1 : 𝕜) * bgV_rec_zero hτ hD (by omega : 2 ≤ L)
  · have hne : a.val ≠ c.val := fun h => hac (Fin.ext h)
    have hd1 : 1 ≤ bgD L a c := by unfold bgD; split_ifs <;> omega
    have hd2 : bgD L a c < L := bgD_lt a c
    have e1 : bgD L (bgSucc a) c = bgD L a c - 1 := by
      unfold bgD; rw [hs]; split_ifs <;> omega
    rw [e1]
    simp only [hac, ↓reduceIte, mul_zero]
    by_cases hlt : bgD L a c + 1 < L
    · have e2 : bgD L (bgPred a) c = bgD L a c + 1 := by
        unfold bgD at hlt ⊢; rw [hp]; split_ifs at hlt ⊢ <;> omega
      rw [e2]
      linear_combination (-1 : 𝕜) * bgV_rec_int hτ L _ hd1 hlt.le
    · have e2 : bgD L (bgPred a) c = 0 := by
        unfold bgD at hlt ⊢; rw [hp]; split_ifs at hlt ⊢ <;> omega
      rw [e2, ← bgV_L τ L]
      have : bgD L a c + 1 = L := by omega
      have h := bgV_rec_int hτ L _ hd1 this.le
      rw [this] at h
      linear_combination (-1 : 𝕜) * h

/-- Over any field: `I + B G_τ` inverts `I - (tα) G_σ` under the energy relation. -/
private lemma bg_geom_inv {L : ℕ} (hL : 3 ≤ L) (σ τ α B t : 𝕜) (hσ0 : σ ≠ 0)
    (hσL : 1 - σ ^ L ≠ 0) (hτ0 : τ ≠ 0) (hτL : 1 - τ ^ L ≠ 0) (hστ : σ⁻¹ - σ ≠ 0)
    (hM3 : σ + σ⁻¹ - t * α * (σ⁻¹ - σ) = τ + τ⁻¹) (hB : B * (τ⁻¹ - τ) = t * α * (σ⁻¹ - σ)) :
    (1 - (t * α) • bgC σ L) * (1 + B • bgC τ L) = 1 := by
  set A : Matrix (Fin L) (Fin L) 𝕜 :=
    Matrix.of fun a k => (if k = bgSucc a then 1 else 0) + (if k = bgPred a then 1 else 0)
    with hAdef
  have hA : ∀ a k, A a k = (if k = bgSucc a then 1 else 0) + (if k = bgPred a then 1 else 0) :=
    fun a k => rfl
  set Gσ := bgC σ L
  set Gτ := bgC τ L
  have hTσ := bgC_mul hσ0 hσL hL A hA
  have hTτ := bgC_mul hτ0 hτL hL A hA
  set Tσ := (σ + σ⁻¹) • (1 : Matrix (Fin L) (Fin L) 𝕜) - A
  set Tτ := (τ + τ⁻¹) • (1 : Matrix (Fin L) (Fin L) 𝕜) - A
  have h1 : Tσ * (1 - (t * α) • Gσ) = Tτ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hTσ, smul_smul]
    simp only [Tσ, Tτ, ← hM3]
    module
  have h2 : Tτ * (1 + B • Gτ) = Tσ := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hTτ, smul_smul, hB]
    simp only [Tσ, Tτ, ← hM3]
    module
  have hYT : ((σ⁻¹ - σ)⁻¹ • Gσ) * Tσ = 1 := by
    rw [mul_eq_one_comm, Matrix.mul_smul, hTσ, smul_smul, inv_mul_cancel₀ hστ, one_smul]
  have : Tσ * ((1 - (t * α) • Gσ) * (1 + B • Gτ)) = Tσ := by rw [← Matrix.mul_assoc, h1, h2]
  have := congrArg (fun X => ((σ⁻¹ - σ)⁻¹ • Gσ) * X) this
  simp only [← Matrix.mul_assoc, hYT, Matrix.one_mul] at this
  exact this

end Field

/-- The row sum of the periodized geometric profile, `(1 + τ)/(1 - τ)`. -/
private lemma bg_row_sum {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1) {L : ℕ} (hL : 1 ≤ L) (a : Fin L) :
    ∑ c, bgC τ L a c = (1 + τ) / (1 - τ) := by
  have hD : 1 - τ ^ L ≠ 0 := by
    have := pow_lt_one₀ h0 h1 (show L ≠ 0 by omega); linarith
  have h1' : (1 : ℝ) - τ ≠ 0 := by linarith
  have e : ∑ c, bgC τ L a c = ∑ k ∈ Finset.range L, bgV τ L k := by
    simp only [bgC, Matrix.of_apply]
    have : NeZero L := ⟨by omega⟩
    have hlg : ∀ c : Fin L, bgD L a c = (c - a).val := by
      intro c
      have ha := a.isLt; have hc := c.isLt
      rw [Fin.sub_def]; simp only [bgD]
      rw [show L - a.val + c.val = c.val + L - a.val by omega, bg_mod_eq _ _ _ hc ha]
    simp_rw [hlg]
    rw [Fintype.sum_equiv (Equiv.subRight a) (fun c => bgV τ L (c - a).val) (fun c => bgV τ L c.val)
      (fun c => rfl)]
    exact Fin.sum_univ_eq_sum_range (fun k => bgV τ L k) L
  rw [e]
  unfold bgV
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hA : ∑ k ∈ Finset.range L, τ ^ k = (1 - τ ^ L) / (1 - τ) := by
    rw [geom_sum_eq h1.ne, div_eq_div_iff (sub_ne_zero.mpr h1.ne) h1']; ring
  have hB : ∑ k ∈ Finset.range L, τ ^ (L - k) = τ * ((1 - τ ^ L) / (1 - τ)) := by
    rw [← hA, Finset.mul_sum]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [← pow_succ']
    congr 1
    omega
  rw [hA, hB]
  field_simp

end BdGeom

/-! ### The free resolvent on the cycle at bounded coupling -/

section BdFree

private lemma bd_s_ne (b : ℝ) {w : ℂ} (hw : 0 < w.im) : freeS b w ≠ 0 := by
  intro h
  have := freeS_im_pos b w hw
  rw [h] at this
  simp at this

private lemma bd_ws_ne (b : ℝ) {w : ℂ} (hw : 0 < w.im) : w + freeS b w ≠ 0 := by
  intro h
  have h1 : 0 < (w + freeS b w).im := by rw [Complex.add_im]; linarith [freeS_im_pos b w hw]
  rw [h] at h1
  simp at h1

private lemma bd_rho_mul (b : ℝ) {w : ℂ} (hw : 0 < w.im) :
    freeRho b w * (w + freeS b w) = 2 * b := by
  unfold freeRho
  field_simp [bd_ws_ne b hw]

private lemma bd_sub_s (b : ℝ) {w : ℂ} (hw : 0 < w.im) :
    w - freeS b w = 2 * b * freeRho b w := by
  have h1 := bd_rho_mul b hw
  have h2 := freeS_sq b w
  have h3 : (w - freeS b w) * (w + freeS b w) = (2 * b * freeRho b w) * (w + freeS b w) := by
    linear_combination (-1 : ℂ) * h2 - (2 * (b : ℂ)) * h1
  exact mul_right_cancel₀ (bd_ws_ne b hw) h3

private lemma bd_T_s (b : ℝ) {w : ℂ} (hw : 0 < w.im) : freeT b w * freeS b w = -1 := by
  rw [freeT_eq b w hw]
  field_simp [bd_s_ne b hw]

/-- The free resolvent of `bA_L` on the cycle: `(bA - w)⁻¹_{ac} = f(w) G_ρ(‖c - a‖)`. -/
private lemma bd_resolvent (b : ℝ) (hb : 0 ≤ b) {w : ℂ} (hw : 0 < w.im) {L : ℕ} (hL : 3 ≤ L) :
    ((b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ =
      Matrix.of fun a c => freeT b w * bgV (freeRho b w) L (cycDist a c) := by
  have hρ1 := norm_freeRho_lt_one b w hw
  have hD : 1 - freeRho b w ^ L ≠ 0 := by
    intro h
    have h1 : freeRho b w ^ L = 1 := by linear_combination -h
    have h2 : ‖freeRho b w‖ ^ L < 1 := pow_lt_one₀ (norm_nonneg _) hρ1 (by omega)
    rw [← norm_pow, h1, norm_one] at h2
    exact lt_irrefl _ h2
  have e : (Matrix.of fun a c => freeT b w * bgV (freeRho b w) L (cycDist a c)) =
      freeT b w • bgC (freeRho b w) L := by
    ext a c; simp [bgC, bgV_cycDist]
  rw [e]
  apply Matrix.inv_eq_right_inv
  rcases hb.lt_or_eq with hb | hb
  · -- `b > 0`
    have hbne : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
    have h1 := bd_rho_mul b hw
    have h2 := bd_sub_s b hw
    have hρ0 : freeRho b w ≠ 0 := by
      intro h; rw [h, zero_mul] at h1
      exact hbne (by linear_combination -h1 / 2)
    have e1 : (b : ℂ) * freeRho b w = (w - freeS b w) / 2 := by linear_combination -h2 / 2
    have e2 : (b : ℂ) * (freeRho b w)⁻¹ = (w + freeS b w) / 2 := by
      have : (b : ℂ) = freeRho b w * (w + freeS b w) / 2 := by linear_combination -h1 / 2
      rw [this]; field_simp
    have hsum : (b : ℂ) * (freeRho b w + (freeRho b w)⁻¹) = w := by
      rw [mul_add, e1, e2]; ring
    have hdiff : (b : ℂ) * ((freeRho b w)⁻¹ - freeRho b w) = freeS b w := by
      rw [mul_sub, e1, e2]; ring
    have hG := bgC_mul hρ0 hD hL (cycleAdj L) (fun a k => by rw [bg_cycleAdj_apply])
    have hrel : (b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ) =
        -(b : ℂ) • ((freeRho b w + (freeRho b w)⁻¹) • (1 : Matrix (Fin L) (Fin L) ℂ) -
          cycleAdj L) := by
      calc (b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ)
          = (b : ℂ) • cycleAdj L - ((b : ℂ) * (freeRho b w + (freeRho b w)⁻¹)) •
              (1 : Matrix (Fin L) (Fin L) ℂ) := by rw [hsum]
        _ = _ := by module
    rw [hrel, Matrix.mul_smul, Matrix.smul_mul, hG, smul_smul, smul_smul]
    have : freeT b w * -(b : ℂ) * ((freeRho b w)⁻¹ - freeRho b w) = 1 := by
      have := bd_T_s b hw
      linear_combination -(freeT b w) * hdiff - this
    rw [this, one_smul]
  · -- `b = 0`
    subst hb
    have hρ : freeRho 0 w = 0 := by simp [freeRho]
    have hs : freeS 0 w = w := by
      have h1 := freeS_sq 0 w
      simp only [Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, sub_zero] at h1
      have h2 : (freeS 0 w - w) * (freeS 0 w + w) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h2 with h | h
      · linear_combination h
      · exfalso
        have := freeS_im_pos 0 w hw
        have h3 : (freeS 0 w + w).im = 0 := by rw [h]; simp
        rw [Complex.add_im] at h3
        linarith
    have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
    have hT : freeT 0 w = -w⁻¹ := by rw [freeT_eq 0 w hw, hs]
    have hC : bgC (0 : ℂ) L = 1 := by
      ext a c
      simp only [bgC, bgV, Matrix.of_apply, Matrix.one_apply]
      have hLz : (0 : ℂ) ^ L = 0 := zero_pow (by omega)
      have hlt := bgD_lt a c
      by_cases hac : a = c
      · subst hac
        have : bgD L a a = 0 := by simp [bgD]
        rw [this, Nat.sub_zero, hLz]; simp
      · have hd : bgD L a c ≠ 0 := by
          have ha := a.isLt; have hc := c.isLt
          have hne : a.val ≠ c.val := fun h => hac (Fin.ext h)
          unfold bgD; split_ifs <;> omega
        rw [hLz, zero_pow hd, zero_pow (by omega)]; simp [hac]
    rw [hρ, hC, hT]
    simp only [Complex.ofReal_zero, zero_smul, zero_sub]
    rw [Matrix.neg_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul]
    rw [show w * -w⁻¹ = -1 by field_simp]
    simp

end BdFree

/-! ### The bounded-coupling kernel -/

section BdModel

/-- `max{1, C}`. -/
private def bdCm (C : ℝ) : ℝ := max 1 C
/-- Lower bound `c'/max{1,C}²` for `Im w`. -/
private def bdι (C c' : ℝ) : ℝ := c' / bdCm C ^ 2
/-- Upper bound `2/(2 + ι)` for `|ρ|`. -/
private def bdq (C c' : ℝ) : ℝ := 2 / (2 + bdι C c')
/-- Lower bound `c'²/max{1,C}²` for `P(0)`. -/
private def bdp₀ (C c' : ℝ) : ℝ := c' ^ 2 / bdCm C ^ 2
private def bdCT (C c' : ℝ) : ℝ := 2 * bdCm C / (1 - bdq C c')
private def bdθ (C c' : ℝ) : ℝ := 2 * bdq C c' / (1 + bdq C c')
private def bdμ₀ (C c' : ℝ) : ℝ := (1 - bdq C c') / 2
private def bdc₁ (C B₀ c' : ℝ) : ℝ :=
  (1 - bdq C c') ^ 2 / (4 * bdCm C ^ 4 * (B₀ + 3) ^ 2 * (B₀ + 2) ^ 2)
private def bdCF (C c' : ℝ) : ℝ := bdCT C c' ^ 2 * (2 / (1 - bdq C c')) ^ 2 * (2 / bdι C c') ^ 2
private def bdCP (C c' : ℝ) : ℝ := bdCF C c' / bdq C c' ^ 2 * (2 * bdθ C c' / (1 - bdθ C c'))
private def bdCM (C c' : ℝ) : ℝ :=
  bdCT C c' * (2 / (1 - bdq C c')) * (1 + 2 * bdθ C c' / (1 - bdθ C c'))

private lemma bdCm_ge (C : ℝ) : 1 ≤ bdCm C ∧ C ≤ bdCm C := ⟨le_max_left _ _, le_max_right _ _⟩

section Consts

variable (C : ℝ) {c' : ℝ} (hc' : 0 < c')
include hc'

private lemma bdι_pos : 0 < bdι C c' := by
  have := (bdCm_ge C).1; unfold bdι; positivity

private lemma bdq_facts : 0 < bdq C c' ∧ bdq C c' < 1 := by
  have := bdι_pos C hc'
  unfold bdq
  exact ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩

private lemma bdθ_facts : 0 < bdθ C c' ∧ bdθ C c' < 1 := by
  obtain ⟨h0, h1⟩ := bdq_facts C hc'
  unfold bdθ
  exact ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩

private lemma bdμ₀_facts : 0 < bdμ₀ C c' ∧ Real.exp (bdμ₀ C c') * bdq C c' ≤ bdθ C c' := by
  obtain ⟨h0, h1⟩ := bdq_facts C hc'
  refine ⟨by unfold bdμ₀; linarith, ?_⟩
  have he := Real.exp_bound_div_one_sub_of_interval (x := bdμ₀ C c') (by unfold bdμ₀; linarith)
    (by unfold bdμ₀; linarith)
  have e : 1 / (1 - bdμ₀ C c') = 2 / (1 + bdq C c') := by
    unfold bdμ₀; rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  rw [e] at he
  unfold bdθ
  calc Real.exp (bdμ₀ C c') * bdq C c' ≤ 2 / (1 + bdq C c') * bdq C c' := by gcongr
    _ = 2 * bdq C c' / (1 + bdq C c') := by ring

private lemma bdp₀_pos : 0 < bdp₀ C c' := by
  have := (bdCm_ge C).1; unfold bdp₀; positivity

private lemma bdCT_pos : 0 < bdCT C c' := by
  have := (bdCm_ge C).1; have := bdq_facts C hc'
  unfold bdCT; apply div_pos (by linarith) (by linarith)

private lemma bdCP_pos : 0 < bdCP C c' := by
  have hT := bdCT_pos C hc'; have hq := bdq_facts C hc'; have hθ := bdθ_facts C hc'
  have hι := bdι_pos C hc'
  have h1 : 0 < 1 - bdq C c' := by linarith
  have h2 : 0 < 1 - bdθ C c' := by linarith
  unfold bdCP bdCF
  exact mul_pos (div_pos (mul_pos (mul_pos (pow_pos hT 2) (pow_pos (div_pos two_pos h1) 2))
    (pow_pos (div_pos two_pos hι) 2)) (pow_pos hq.1 2)) (div_pos (by linarith) h2)

private lemma bdCM_pos : 0 < bdCM C c' := by
  have hT := bdCT_pos C hc'; have hq := bdq_facts C hc'; have hθ := bdθ_facts C hc'
  have h1 : 0 < 1 - bdq C c' := by linarith
  have h2 : 0 < 1 - bdθ C c' := by linarith
  have h3 : 0 < 2 * bdθ C c' / (1 - bdθ C c') := div_pos (by linarith) h2
  unfold bdCM
  exact mul_pos (mul_pos hT (div_pos two_pos h1)) (by linarith)

end Consts

private lemma bdc₁_pos (C : ℝ) {B₀ c' : ℝ} (hB₀ : 0 < B₀) (hc' : 0 < c') :
    0 < bdc₁ C B₀ c' := by
  have hm := (bdCm_ge C).1; have := bdq_facts C hc'
  have h1 : 0 < 1 - bdq C c' := by linarith
  unfold bdc₁
  exact div_pos (pow_pos h1 2) (by positivity)

/-- `γ_g`, `b = hopB g` on `0 ≤ g ≤ C`. -/
private lemma bd_gamma {C g : ℝ} (hg : 0 ≤ g) (hgC : g ≤ C) :
    0 < gammaG g ∧ gammaG g ≤ 1 ∧ 1 ≤ gammaG g * bdCm C ^ 2 ∧ 0 ≤ hopB g ∧ hopB g ≤ 1 ∧
      hopB g ≤ g ∧ g ≤ bdCm C * hopB g := by
  have h1 : 1 ≤ max 1 g := le_max_left _ _
  have h2 : g ≤ max 1 g := le_max_right _ _
  have h3 : max 1 g ≤ bdCm C := max_le_max le_rfl hgC
  have hm0 : 0 < max 1 g := by linarith
  unfold gammaG hopB
  refine ⟨inv_pos.mpr (pow_pos hm0 2), inv_le_one_of_one_le₀ (by nlinarith), ?_,
    div_nonneg hg hm0.le,
    by rw [div_le_one hm0]; exact h2, by rw [div_le_iff₀ hm0]; nlinarith, ?_⟩
  · rw [← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_left₀ hm0.le h3 2
  · rw [mul_div_assoc', le_div_iff₀ hm0]; nlinarith

/-- `Σ_{y ≠ 0} θ^{‖y‖} ≤ 2θ/(1-θ)` and `Σ_y θ^{‖y‖} ≤ 1 + 2θ/(1-θ)`. -/
private lemma bd_sum_geom {L : ℕ} [NeZero L] (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑ y : Fin L, (if y = 0 then 0 else θ ^ bdD y) ≤ 2 * θ / (1 - θ) ∧
      ∑ y : Fin L, θ ^ bdD y ≤ 1 + 2 * θ / (1 - θ) := by
  have hmin : ∀ y : Fin L, bdD y = min y.val (L - y.val) := by
    intro y
    unfold bdD
    rw [Fin.neg_def]; simp only
    by_cases hy : y.val = 0
    · rw [hy]; simp
    · rw [Nat.mod_eq_of_lt (by have := y.isLt; omega)]
  have hgeom : ∑ j ∈ Finset.range L, θ ^ (j + 1) ≤ θ / (1 - θ) := by
    have hs : ∑ j ∈ Finset.range L, θ ^ (j + 1) = θ * ∑ j ∈ Finset.range L, θ ^ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have h2 : ∑ j ∈ Finset.range L, θ ^ j ≤ 1 / (1 - θ) := by
      rw [geom_sum_eq h1.ne, show (θ ^ L - 1) / (θ - 1) = (1 - θ ^ L) / (1 - θ) by
        rw [div_eq_div_iff (by linarith) (by linarith)]; ring]
      apply div_le_div_of_nonneg_right _ (by linarith)
      linarith [pow_nonneg h0 L]
    rw [hs]
    calc θ * ∑ j ∈ Finset.range L, θ ^ j ≤ θ * (1 / (1 - θ)) := mul_le_mul_of_nonneg_left h2 h0
      _ = θ / (1 - θ) := by ring
  have e : ∀ y : Fin L, (if y = 0 then 0 else θ ^ bdD y) =
      (fun j : ℕ => if j = 0 then (0 : ℝ) else θ ^ j) (min y.val (L - y.val)) := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp
    · have h3 : bdD y ≠ 0 := fun h => hy (bdD_eq_zero.mp h)
      rw [hmin] at h3
      simp only [hy, h3, ↓reduceIte, hmin]
  have hA : ∑ y : Fin L, (if y = 0 then 0 else θ ^ bdD y) ≤ 2 * θ / (1 - θ) := by
    rw [Finset.sum_congr rfl fun y _ => e y]
    refine (bd_sum_min_le L (fun j : ℕ => if j = 0 then (0 : ℝ) else θ ^ j)
      (fun j => by split_ifs <;> positivity)).trans ?_
    simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, zero_add]
    rw [mul_div_assoc]
    linarith
  refine ⟨hA, ?_⟩
  have e2 : ∀ y : Fin L,
      θ ^ bdD y = (if y = 0 then 1 else 0) + (if y = 0 then 0 else θ ^ bdD y) := by
    intro y; by_cases hy : y = 0
    · subst hy; simp [bdD_zero]
    · simp [hy]
  rw [Finset.sum_congr rfl fun y _ => e2 y, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  linarith

end BdModel

section BdModel2

/-- The profile `F(r) = γ |f(w) G_ρ(r)|²` of the pair kernel `P`. -/
private def bdF (g : ℝ) (L : ℕ) (E : ℝ) (m : ℂ) (r : ℕ) : ℝ :=
  gammaG g * ‖freeT (hopB g) ((E : ℂ) + gammaG g * m) *
    bgV (freeRho (hopB g) ((E : ℂ) + gammaG g * m)) L r‖ ^ 2

/-- `‖G_ρ(r)‖ ≤ 2q^r/(1 - q₀)` for `‖ρ‖ = q ≤ q₀ < 1`, `2r ≤ L`. -/
private lemma bd_bgV_le (ρ : ℂ) (q₀ : ℝ) (hq : ‖ρ‖ ≤ q₀) (hq₀ : q₀ < 1) {L : ℕ} (hL : 1 ≤ L)
    (r : ℕ) (hr : 2 * r ≤ L) : ‖bgV ρ L r‖ ≤ 2 * ‖ρ‖ ^ r / (1 - q₀) := by
  unfold bgV
  have hq0 := norm_nonneg ρ
  have hqL : ‖ρ‖ ^ L ≤ q₀ := (pow_le_of_le_one hq0 (by linarith) (by omega)).trans hq
  have h1 : 1 - q₀ ≤ ‖1 - ρ ^ L‖ := by
    have := norm_sub_norm_le (1 : ℂ) (ρ ^ L); rw [norm_one, norm_pow] at this; linarith
  have h2 : ‖ρ ^ r + ρ ^ (L - r)‖ ≤ 2 * ‖ρ‖ ^ r := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow, norm_pow]
    have : ‖ρ‖ ^ (L - r) ≤ ‖ρ‖ ^ r := pow_le_pow_of_le_one hq0 (by linarith) (by omega)
    linarith
  rw [norm_div, div_le_div_iff₀ (by linarith) (by linarith)]
  have h3 : 0 ≤ ‖ρ‖ ^ r := by positivity
  nlinarith [norm_nonneg (ρ ^ r + ρ ^ (L - r))]

/-- The facts on the bounded-coupling kernel used below. -/
private structure BdModel (C B₀ c' g : ℝ) (L : ℕ) (E : ℝ) (m : ℂ) : Prop where
  gam : 0 < gammaG g ∧ gammaG g ≤ 1 ∧ 1 ≤ gammaG g * bdCm C ^ 2
  w_im : 0 < ((E : ℂ) + gammaG g * m).im
  M_eq : ∀ a c, dysonMat (hopB g) (gammaG g) L E m a c =
    freeT (hopB g) ((E : ℂ) + gammaG g * m) *
      bgV (freeRho (hopB g) ((E : ℂ) + gammaG g * m)) L (cycDist a c)
  P_eq : pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) = bdP (bdF g L E m) L
  good : BdGood L (bdF g L E m) g (bdp₀ C c') (bdc₁ C B₀ c') (bdμ₀ C c') (bdCP C c')
  Mrow : ∀ [NeZero L] (a : Fin L), ∑ c, Real.exp (bdμ₀ C c' * cycDist a c) *
    ‖dysonMat (hopB g) (gammaG g) L E m a c‖ ≤ bdCM C c'
  m_le : ‖m‖ ≤ bdCm C
  m_sq : gammaG g * ‖m‖ ^ 2 ≤ 1
  diag : ∀ a, dysonMat (hopB g) (gammaG g) L E m a a = m
  rho_le : ‖freeRho (hopB g) ((E : ℂ) + gammaG g * m)‖ ≤ bdq C c'
  rho_ge : hopB g / (B₀ + 2) ≤ ‖freeRho (hopB g) ((E : ℂ) + gammaG g * m)‖
  T_le : ‖freeT (hopB g) ((E : ℂ) + gammaG g * m)‖ ≤ bdCT C c'

/-- Bounds on `f(w)` and `ρ(w)` at bounded coupling. -/
private lemma bd_free_bounds {C B₀ c' : ℝ} (hc' : 0 < c') {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    {w : ℂ} (hw : 0 < w.im) (hwι : bdι C c' ≤ w.im) (hwle : ‖w‖ ≤ B₀ + 1) {L : ℕ} (hL : 3 ≤ L)
    {m : ℂ} (hm0 : m = freeT b w * bgV (freeRho b w) L 0) (hmle : ‖m‖ ≤ bdCm C) :
    1 / (B₀ + 3) ≤ ‖freeT b w‖ ∧ ‖freeRho b w‖ ≤ bdq C c' ∧ ‖freeRho b w‖ ≤ 2 * b / bdι C c' ∧
      b / (B₀ + 2) ≤ ‖freeRho b w‖ ∧ ‖freeT b w‖ ≤ bdCT C c' := by
  have hι := bdι_pos C hc'
  have hq := bdq_facts C hc'
  set T := freeT b w with hTdef
  set ρ := freeRho b w with hρdef
  set s := freeS b w with hsdef
  have hsle : ‖s‖ ≤ ‖w‖ + 2 * b := by
    have h1 : ‖s‖ ^ 2 ≤ (‖w‖ + 2 * b) ^ 2 := by
      have := freeS_sq b w
      have h2 : ‖s‖ ^ 2 = ‖w ^ 2 - 4 * (b : ℂ) ^ 2‖ := by rw [← this, norm_pow]
      rw [h2]
      calc ‖w ^ 2 - 4 * (b : ℂ) ^ 2‖ ≤ ‖w ^ 2‖ + ‖4 * (b : ℂ) ^ 2‖ := norm_sub_le _ _
        _ = ‖w‖ ^ 2 + 4 * b ^ 2 := by
            rw [norm_pow, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb0]
            norm_num
        _ ≤ (‖w‖ + 2 * b) ^ 2 := by nlinarith [norm_nonneg w]
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h1
  have hs0 : 0 < ‖s‖ := norm_pos_iff.mpr (bd_s_ne b hw)
  have hTn : ‖T‖ = ‖s‖⁻¹ := by rw [hTdef, freeT_eq b w hw, norm_neg, norm_inv]
  have hTge : 1 / (B₀ + 3) ≤ ‖T‖ := by
    rw [hTn, one_div]; exact inv_anti₀ hs0 (by linarith)
  have hρle1 := norm_freeRho_le b hb0 w hw
  have hρq : ‖ρ‖ ≤ bdq C c' := by
    refine hρle1.trans ?_
    unfold bdq
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hρb : ‖ρ‖ ≤ 2 * b / bdι C c' :=
    hρle1.trans (div_le_div_of_nonneg_left (by positivity) hι (by linarith))
  have hρge : b / (B₀ + 2) ≤ ‖ρ‖ := by
    have h1 := bd_rho_mul b hw
    have h2 : ‖ρ‖ * ‖w + s‖ = 2 * b := by
      rw [← norm_mul, h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
      norm_num
    have h3 : ‖w + s‖ ≤ 2 * B₀ + 4 := (norm_add_le _ _).trans (by linarith)
    have hB2 : 0 < B₀ + 2 := by linarith [norm_nonneg w]
    rw [div_le_iff₀ hB2]
    nlinarith [norm_nonneg ρ]
  have hρ1 : ‖ρ‖ < 1 := lt_of_le_of_lt hρq hq.2
  have hG0 : (1 - bdq C c') / 2 ≤ ‖bgV ρ L 0‖ := by
    unfold bgV
    rw [pow_zero, Nat.sub_zero, norm_div]
    have hρL : ‖ρ‖ ^ L ≤ bdq C c' :=
      (pow_le_of_le_one (norm_nonneg _) hρ1.le (by omega)).trans hρq
    have h1 : 1 - bdq C c' ≤ ‖1 + ρ ^ L‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-(ρ ^ L))
      rw [norm_one, norm_neg, norm_pow, sub_neg_eq_add] at this; linarith
    have h2 : ‖1 - ρ ^ L‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, norm_pow]; linarith [pow_le_one₀ (norm_nonneg ρ) hρ1.le (n := L)]
    have h3 : 0 < ‖1 - ρ ^ L‖ := by
      have := norm_sub_norm_le (1 : ℂ) (ρ ^ L)
      rw [norm_one, norm_pow] at this
      linarith [pow_lt_one₀ (norm_nonneg ρ) hρ1 (show L ≠ 0 by omega)]
    rw [le_div_iff₀ h3]
    nlinarith
  have hTle : ‖T‖ ≤ bdCT C c' := by
    have h2 : ‖m‖ = ‖T‖ * ‖bgV ρ L 0‖ := by rw [hm0, norm_mul]
    unfold bdCT
    rw [le_div_iff₀ (by linarith)]
    have h3 : ‖T‖ * ((1 - bdq C c') / 2) ≤ ‖m‖ := by
      rw [h2]; exact mul_le_mul_of_nonneg_left hG0 (norm_nonneg _)
    have h4 : ‖T‖ * (1 - bdq C c') = 2 * (‖T‖ * ((1 - bdq C c') / 2)) := by ring
    linarith
  exact ⟨hTge, hρq, hρb, hρge, hTle⟩

/-- `‖G_ρ(1)‖ ≥ ‖ρ‖(1 - q₀)/2`. -/
private lemma bd_bgV_one {ρ : ℂ} {q₀ : ℝ} (hρq : ‖ρ‖ ≤ q₀) (hq₀ : q₀ < 1) {L : ℕ} (hL : 3 ≤ L) :
    ‖ρ‖ * ((1 - q₀) / 2) ≤ ‖bgV ρ L 1‖ := by
  have hρ1 : ‖ρ‖ < 1 := lt_of_le_of_lt hρq hq₀
  unfold bgV
  rw [pow_one, norm_div]
  have h1 : ‖ρ‖ - ‖ρ‖ ^ (L - 1) ≤ ‖ρ + ρ ^ (L - 1)‖ := by
    have := norm_sub_norm_le ρ (-(ρ ^ (L - 1)))
    rw [norm_neg, norm_pow, sub_neg_eq_add] at this; exact this
  have h2 : ‖ρ‖ ^ (L - 1) ≤ ‖ρ‖ * q₀ := by
    have : ‖ρ‖ ^ (L - 1) = ‖ρ‖ * ‖ρ‖ ^ (L - 2) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]
    exact mul_le_mul_of_nonneg_left ((pow_le_of_le_one (norm_nonneg _) hρ1.le (by omega)).trans
      hρq) (norm_nonneg _)
  have h3 : ‖1 - ρ ^ L‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_pow]; linarith [pow_le_one₀ (norm_nonneg ρ) hρ1.le (n := L)]
  have h4 : 0 < ‖1 - ρ ^ L‖ := by
    have := norm_sub_norm_le (1 : ℂ) (ρ ^ L)
    rw [norm_one, norm_pow] at this
    linarith [pow_lt_one₀ (norm_nonneg ρ) hρ1 (show L ≠ 0 by omega)]
  rw [le_div_iff₀ h4]
  have h5 : 0 ≤ ‖ρ‖ := norm_nonneg _
  have hq1 : 0 ≤ 1 - q₀ := by linarith
  calc ‖ρ‖ * ((1 - q₀) / 2) * ‖1 - ρ ^ L‖ ≤ ‖ρ‖ * ((1 - q₀) / 2) * 2 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ‖ρ‖ - ‖ρ‖ * q₀ := by ring
    _ ≤ ‖ρ‖ - ‖ρ‖ ^ (L - 1) := by linarith
    _ ≤ _ := h1

/-- The weighted off-diagonal mass of the profile. -/
private lemma bd_off_le {C c' : ℝ} (hc' : 0 < c') {L : ℕ} [NeZero L] {γ b g : ℝ} {T ρ : ℂ}
    (hγ1 : γ ≤ 1) (hb0 : 0 ≤ b) (hbg : b ≤ g) (hTle : ‖T‖ ≤ bdCT C c')
    (hρq : ‖ρ‖ ≤ bdq C c') (hρb : ‖ρ‖ ≤ 2 * b / bdι C c') :
    ∑ y : Fin L, (if y = 0 then 0 else
      Real.exp (bdμ₀ C c' * bdD y) * (γ * ‖T * bgV ρ L (bdD y)‖ ^ 2)) ≤ bdCP C c' * g ^ 2 := by
  have hq := bdq_facts C hc'
  have hq1 : 0 < 1 - bdq C c' := by linarith [hq.2]
  have hι := bdι_pos C hc'
  obtain ⟨hμ0, hμq⟩ := bdμ₀_facts C hc'
  obtain ⟨hθ0, hθ1⟩ := bdθ_facts C hc'
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hbgV : ∀ r, 2 * r ≤ L → ‖bgV ρ L r‖ ≤ 2 * ‖ρ‖ ^ r / (1 - bdq C c') :=
    fun r hr => bd_bgV_le ρ (bdq C c') hρq hq.2 hL1 r hr
  have hterm : ∀ y : Fin L, (if y = 0 then 0 else
      Real.exp (bdμ₀ C c' * bdD y) * (γ * ‖T * bgV ρ L (bdD y)‖ ^ 2)) ≤
      bdCF C c' * b ^ 2 / bdq C c' ^ 2 * (if y = 0 then 0 else bdθ C c' ^ bdD y) := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    simp only [hy, ↓reduceIte]
    set r := bdD y with hr
    have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (fun h => hy (bdD_eq_zero.mp h))
    have hr2 : 2 * r ≤ L := bdD_two_mul_le y
    have hρr : ‖ρ‖ ^ r ≤ 2 * b / bdι C c' * bdq C c' ^ (r - 1) := by
      have : ‖ρ‖ ^ r = ‖ρ‖ * ‖ρ‖ ^ (r - 1) := by rw [← pow_succ']; congr 1; omega
      rw [this]
      exact mul_le_mul hρb (pow_le_pow_left₀ (norm_nonneg _) hρq _) (by positivity)
        (by positivity)
    have hFle : γ * ‖T * bgV ρ L r‖ ^ 2 ≤ bdCF C c' * b ^ 2 * (bdq C c' ^ (r - 1)) ^ 2 := by
      have h1 : ‖bgV ρ L r‖ ≤ 2 / (1 - bdq C c') * (2 * b / bdι C c' * bdq C c' ^ (r - 1)) := by
        refine (hbgV r hr2).trans ?_
        calc 2 * ‖ρ‖ ^ r / (1 - bdq C c') ≤
            2 * (2 * b / bdι C c' * bdq C c' ^ (r - 1)) / (1 - bdq C c') := by gcongr
          _ = _ := by ring
      have h2 : ‖T‖ ^ 2 * ‖bgV ρ L r‖ ^ 2 ≤ bdCT C c' ^ 2 *
          (2 / (1 - bdq C c') * (2 * b / bdι C c' * bdq C c' ^ (r - 1))) ^ 2 := by
        gcongr
      calc γ * ‖T * bgV ρ L r‖ ^ 2 = γ * (‖T‖ ^ 2 * ‖bgV ρ L r‖ ^ 2) := by rw [norm_mul]; ring
        _ ≤ 1 * (‖T‖ ^ 2 * ‖bgV ρ L r‖ ^ 2) := mul_le_mul_of_nonneg_right hγ1 (by positivity)
        _ ≤ bdCT C c' ^ 2 * (2 / (1 - bdq C c') * (2 * b / bdι C c' * bdq C c' ^ (r - 1))) ^ 2 :=
            by rw [one_mul]; exact h2
        _ = bdCF C c' * b ^ 2 * (bdq C c' ^ (r - 1)) ^ 2 := by unfold bdCF; ring
    have hexp : Real.exp (bdμ₀ C c' * r) * (bdq C c' ^ (r - 1)) ^ 2 ≤
        bdθ C c' ^ r / bdq C c' ^ 2 := by
      rw [le_div_iff₀ (pow_pos hq.1 2)]
      have e1 : Real.exp (bdμ₀ C c' * r) = Real.exp (bdμ₀ C c') ^ r := by
        rw [← Real.exp_nat_mul]; ring_nf
      have e2 : (bdq C c' ^ (r - 1)) ^ 2 * bdq C c' ^ 2 = (bdq C c' ^ 2) ^ r := by
        calc (bdq C c' ^ (r - 1)) ^ 2 * bdq C c' ^ 2 = (bdq C c' ^ (r - 1) * bdq C c') ^ 2 := by
              rw [mul_pow]
          _ = (bdq C c' ^ r) ^ 2 := by rw [← pow_succ, Nat.sub_add_cancel hr1]
          _ = (bdq C c' ^ 2) ^ r := by rw [← pow_mul, ← pow_mul, mul_comm]
      rw [e1, mul_assoc, e2, ← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      calc Real.exp (bdμ₀ C c') * bdq C c' ^ 2 ≤ Real.exp (bdμ₀ C c') * bdq C c' * 1 := by
            rw [sq, ← mul_assoc]
            exact mul_le_mul_of_nonneg_left hq.2.le (mul_nonneg (Real.exp_pos _).le hq.1.le)
        _ ≤ bdθ C c' := by rw [mul_one]; exact hμq
    have hCF : 0 ≤ bdCF C c' := by unfold bdCF; positivity
    calc Real.exp (bdμ₀ C c' * r) * (γ * ‖T * bgV ρ L r‖ ^ 2)
        ≤ Real.exp (bdμ₀ C c' * r) * (bdCF C c' * b ^ 2 * (bdq C c' ^ (r - 1)) ^ 2) :=
          mul_le_mul_of_nonneg_left hFle (Real.exp_pos _).le
      _ = bdCF C c' * b ^ 2 * (Real.exp (bdμ₀ C c' * r) * (bdq C c' ^ (r - 1)) ^ 2) := by ring
      _ ≤ bdCF C c' * b ^ 2 * (bdθ C c' ^ r / bdq C c' ^ 2) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  have hCF : 0 ≤ bdCF C c' := by unfold bdCF; positivity
  calc ∑ y : Fin L, (if y = 0 then 0 else
        Real.exp (bdμ₀ C c' * bdD y) * (γ * ‖T * bgV ρ L (bdD y)‖ ^ 2))
      ≤ ∑ y : Fin L, bdCF C c' * b ^ 2 / bdq C c' ^ 2 * (if y = 0 then 0 else bdθ C c' ^ bdD y) :=
        Finset.sum_le_sum fun y _ => hterm y
    _ = bdCF C c' * b ^ 2 / bdq C c' ^ 2 *
          ∑ y : Fin L, (if y = 0 then 0 else bdθ C c' ^ bdD y) := by rw [Finset.mul_sum]
    _ ≤ bdCF C c' * b ^ 2 / bdq C c' ^ 2 * (2 * bdθ C c' / (1 - bdθ C c')) :=
        mul_le_mul_of_nonneg_left (bd_sum_geom (bdθ C c') hθ0.le hθ1).1 (by positivity)
    _ = bdCP C c' * b ^ 2 := by unfold bdCP; ring
    _ ≤ bdCP C c' * g ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbg 2) (bdCP_pos C hc').le

/-- The weighted rows of `M`. -/
private lemma bd_M_row_le {C c' : ℝ} (hc' : 0 < c') {L : ℕ} [NeZero L] {T ρ : ℂ}
    (hTle : ‖T‖ ≤ bdCT C c') (hρq : ‖ρ‖ ≤ bdq C c') (a : Fin L) :
    ∑ c, Real.exp (bdμ₀ C c' * cycDist a c) * ‖T * bgV ρ L (cycDist a c)‖ ≤ bdCM C c' := by
  have hq := bdq_facts C hc'
  have hq1 : 0 < 1 - bdq C c' := by linarith [hq.2]
  obtain ⟨hμ0, hμq⟩ := bdμ₀_facts C hc'
  obtain ⟨hθ0, hθ1⟩ := bdθ_facts C hc'
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hT0' : 0 ≤ bdCT C c' := (norm_nonneg _).trans hTle
  have hsumrow : ∑ c, Real.exp (bdμ₀ C c' * cycDist a c) * (‖ρ‖ ^ cycDist a c) ≤
      1 + 2 * bdθ C c' / (1 - bdθ C c') := by
    have h1 : ∀ c, Real.exp (bdμ₀ C c' * cycDist a c) * (‖ρ‖ ^ cycDist a c) ≤
        bdθ C c' ^ cycDist a c := by
      intro c
      rw [show bdμ₀ C c' * (cycDist a c : ℝ) = (cycDist a c : ℕ) * bdμ₀ C c' by ring,
        Real.exp_nat_mul, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) ((mul_le_mul_of_nonneg_left hρq
        (Real.exp_pos _).le).trans hμq) _
    calc ∑ c, Real.exp (bdμ₀ C c' * cycDist a c) * (‖ρ‖ ^ cycDist a c)
        ≤ ∑ c, bdθ C c' ^ cycDist a c := Finset.sum_le_sum fun c _ => h1 c
      _ = ∑ y : Fin L, bdθ C c' ^ bdD y := by
          simp only [bd_cycDist_eq]; exact bd_sum_sub a (fun y => bdθ C c' ^ bdD y)
      _ ≤ _ := (bd_sum_geom (bdθ C c') hθ0.le hθ1).2
  calc ∑ c, Real.exp (bdμ₀ C c' * cycDist a c) * ‖T * bgV ρ L (cycDist a c)‖
      ≤ ∑ c, bdCT C c' * (2 / (1 - bdq C c')) *
          (Real.exp (bdμ₀ C c' * cycDist a c) * ‖ρ‖ ^ cycDist a c) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [norm_mul]
        have h1 := bd_bgV_le ρ (bdq C c') hρq hq.2 hL1 (cycDist a c) (bd_cycDist_half a c)
        have h2 : ‖T‖ * ‖bgV ρ L (cycDist a c)‖ ≤
            bdCT C c' * (2 * ‖ρ‖ ^ cycDist a c / (1 - bdq C c')) :=
          mul_le_mul hTle h1 (norm_nonneg _) hT0'
        calc Real.exp (bdμ₀ C c' * cycDist a c) * (‖T‖ * ‖bgV ρ L (cycDist a c)‖)
            ≤ Real.exp (bdμ₀ C c' * cycDist a c) *
                (bdCT C c' * (2 * ‖ρ‖ ^ cycDist a c / (1 - bdq C c'))) :=
              mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
          _ = _ := by ring
    _ = bdCT C c' * (2 / (1 - bdq C c')) *
          ∑ c, Real.exp (bdμ₀ C c' * cycDist a c) * ‖ρ‖ ^ cycDist a c := by rw [Finset.mul_sum]
    _ ≤ bdCT C c' * (2 / (1 - bdq C c')) * (1 + 2 * bdθ C c' / (1 - bdθ C c')) :=
        mul_le_mul_of_nonneg_left hsumrow (by positivity)
    _ = bdCM C c' := by unfold bdCM; ring

private lemma bd_model {C B₀ c' : ℝ} (hB₀ : 0 < B₀) (hc' : 0 < c') {g : ℝ}
    (hg : 0 ≤ g) (hgC : g ≤ C) {L : ℕ} (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ B₀) {m : ℂ}
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (hcm : c' ≤ m.im) :
    BdModel C B₀ c' g L E m := by
  have : NeZero L := ⟨by omega⟩
  obtain ⟨hγ0, hγ1, hγC, hb0, hb1, hbg, hgb⟩ := bd_gamma hg hgC
  have hCm := bdCm_ge C
  have hCm0 : 0 < bdCm C := by linarith [hCm.1]
  have hmim : 0 < m.im := hm.1
  have hwim : ((E : ℂ) + gammaG g * m).im = gammaG g * m.im := by simp
  have hw : 0 < ((E : ℂ) + gammaG g * m).im := by rw [hwim]; positivity
  have hwι : bdι C c' ≤ ((E : ℂ) + gammaG g * m).im := by
    rw [hwim]
    unfold bdι
    rw [div_le_iff₀ (pow_pos hCm0 2)]
    calc c' ≤ m.im := hcm
      _ ≤ gammaG g * bdCm C ^ 2 * m.im := le_mul_of_one_le_left hmim.le hγC
      _ = gammaG g * m.im * bdCm C ^ 2 := by ring
  set γ := gammaG g with hγdef
  set b := hopB g with hbdef
  set w : ℂ := (E : ℂ) + γ * m with hwdef
  set T := freeT b w with hTdef
  set ρ := freeRho b w with hρdef
  -- the explicit resolvent
  have hMac : ∀ a c, dysonMat b γ L E m a c = T * bgV ρ L (cycDist a c) := by
    intro a c
    have h := bd_resolvent b hb0 hw hL
    have e : dysonMat b γ L E m = ((b : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ :=
      rfl
    rw [e, h]; rfl
  have hdiag : ∀ a, dysonMat b γ L E m a a = m := by
    intro a
    have h := dysonMat_diag b γ L (by omega) E m hw a
    rw [h]; exact hm.2.symm
  have hrow := pairP_row_sum b γ hγ0 L (by omega) E m hm
  have hmsq : γ * ‖m‖ ^ 2 ≤ 1 := by
    have h1 := hrow 0
    have h2 := Finset.single_le_sum (f := fun c => pairP γ (dysonMat b γ L E m) 0 c)
      (fun c _ => by simp only [pairP, Matrix.of_apply]; positivity) (Finset.mem_univ 0)
    simp only [pairP, Matrix.of_apply, hdiag] at h2
    simp only [pairP, Matrix.of_apply] at h1
    linarith
  have hmle : ‖m‖ ≤ bdCm C := by
    have h1 : ‖m‖ ^ 2 ≤ bdCm C ^ 2 := by
      have := mul_le_mul_of_nonneg_right hmsq (by positivity : (0 : ℝ) ≤ bdCm C ^ 2)
      nlinarith
    exact le_of_pow_le_pow_left₀ two_ne_zero hCm0.le h1
  have hγm : γ * ‖m‖ ≤ 1 := by
    have : (γ * ‖m‖) ^ 2 ≤ 1 ^ 2 := by nlinarith
    exact le_of_pow_le_pow_left₀ two_ne_zero zero_le_one this
  have hwle : ‖w‖ ≤ B₀ + 1 := by
    calc ‖w‖ ≤ ‖(E : ℂ)‖ + ‖(γ : ℂ) * m‖ := norm_add_le _ _
      _ = |E| + γ * ‖m‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hγ0]
      _ ≤ B₀ + 1 := by linarith
  have hT0 : m = T * bgV ρ L 0 := by rw [← hdiag 0, hMac, bd_cycDist_self]
  obtain ⟨hTge, hρq, hρb, hρge, hTle⟩ := bd_free_bounds hc' hb0 hb1 hw hwι hwle hL hT0 hmle
  have hPeq : pairP γ (dysonMat b γ L E m) = bdP (bdF g L E m) L := by
    ext a c
    change γ * ‖dysonMat b γ L E m a c‖ ^ 2 = bdF g L E m (cycDist a c)
    rw [hMac]; rfl
  have hF0 : ∀ r, 0 ≤ bdF g L E m r := fun r => by unfold bdF; positivity
  have hFsum : ∑ y : Fin L, bdF g L E m (bdD y) = 1 := by
    rw [← bdP_row (bdF g L E m) (0 : Fin L), ← hPeq]; exact hrow 0
  have hFr : ∀ r, bdF g L E m r = γ * ‖T‖ ^ 2 * ‖bgV ρ L r‖ ^ 2 := by
    intro r; change γ * ‖T * bgV ρ L r‖ ^ 2 = _; rw [norm_mul]; ring
  have hγinv : 1 / bdCm C ^ 2 ≤ γ := by rw [div_le_iff₀ (by positivity)]; linarith
  have hzero : bdp₀ C c' ≤ bdF g L E m 0 := by
    have h1 : bdF g L E m 0 = γ * ‖m‖ ^ 2 := by
      rw [hFr, hT0, norm_mul]; ring
    have h2 : c' ≤ ‖m‖ := hcm.trans (Complex.im_le_norm m)
    have h3 : c' ^ 2 ≤ ‖m‖ ^ 2 := pow_le_pow_left₀ hc'.le h2 2
    rw [h1]; unfold bdp₀
    calc c' ^ 2 / bdCm C ^ 2 = 1 / bdCm C ^ 2 * c' ^ 2 := by ring
      _ ≤ γ * ‖m‖ ^ 2 := mul_le_mul hγinv h3 (by positivity) hγ0.le
  have hq := bdq_facts C hc'
  have hG1 := bd_bgV_one hρq hq.2 hL
  have hone : bdc₁ C B₀ c' * g ^ 2 ≤ bdF g L E m 1 := by
    rw [hFr]
    have hb' : g / bdCm C / (B₀ + 2) * ((1 - bdq C c') / 2) ≤ ‖bgV ρ L 1‖ := by
      refine le_trans ?_ hG1
      have hq1 : 0 ≤ (1 - bdq C c') / 2 := by linarith [hq.2]
      refine mul_le_mul_of_nonneg_right (le_trans ?_ hρge) hq1
      exact div_le_div_of_nonneg_right (by rw [div_le_iff₀ hCm0]; linarith) (by linarith)
    have hnn : 0 ≤ g / bdCm C / (B₀ + 2) * ((1 - bdq C c') / 2) :=
      mul_nonneg (by positivity) (by linarith [hq.2])
    calc bdc₁ C B₀ c' * g ^ 2
        = 1 / bdCm C ^ 2 * (1 / (B₀ + 3)) ^ 2 *
            (g / bdCm C / (B₀ + 2) * ((1 - bdq C c') / 2)) ^ 2 := by
          unfold bdc₁; field_simp; ring
      _ ≤ γ * ‖T‖ ^ 2 * ‖bgV ρ L 1‖ ^ 2 := by gcongr
  exact {
    gam := ⟨hγ0, hγ1, hγC⟩
    w_im := hw
    M_eq := hMac
    P_eq := hPeq
    good := {
      hL := hL
      nonneg := hF0
      sum := fun {_} => hFsum
      zero := hzero
      one := hone
      off := fun {_} => bd_off_le hc' hγ1 hb0 hbg hTle hρq hρb
      hp₀ := bdp₀_pos C hc'
      hc₁ := bdc₁_pos C hB₀ hc'
      hμ₀ := (bdμ₀_facts C hc').1
      hCP := bdCP_pos C hc' }
    Mrow := fun {_} a => le_trans (le_of_eq (Finset.sum_congr rfl fun c _ => by rw [hMac]))
      (bd_M_row_le hc' hTle hρq a)
    m_le := hmle
    m_sq := hmsq
    diag := hdiag
    rho_le := hρq
    rho_ge := hρge
    T_le := hTle }

end BdModel2

/-! ### The same-sign kernel -/

section BdStable

/-- The gap `|1 - tγm²| - t(1 - γ|m|²) ≥ γ(Im m)²`, (A.31) [ba:eq:gap]. -/
private lemma bd_gap (γ : ℝ) (hγ : 0 < γ) (m : ℂ) (hm : γ * ‖m‖ ^ 2 ≤ 1) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    γ * m.im ^ 2 ≤ ‖1 - (t : ℂ) * ((γ : ℂ) * m ^ 2)‖ - t * (1 - γ * ‖m‖ ^ 2) := by
  set x := γ * ‖m‖ ^ 2 with hx
  set y := γ * m.im ^ 2 with hy
  have hnorm : ‖m‖ ^ 2 = m.re ^ 2 + m.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hy0 : 0 ≤ y := by positivity
  have hyx : y ≤ x := by rw [hx, hy, hnorm]; nlinarith [sq_nonneg m.re]
  have hsq : ‖1 - (t : ℂ) * ((γ : ℂ) * m ^ 2)‖ ^ 2 = (1 - t * x) ^ 2 + 4 * t * y := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im, sq]
    rw [hx, hy, hnorm]
    ring
  set S := ‖1 - (t : ℂ) * ((γ : ℂ) * m ^ 2)‖ with hS
  have hS0 : 0 ≤ S := norm_nonneg _
  have hA0 : 0 ≤ 1 - t * x := by nlinarith
  have hA1 : 1 - t * x ≤ 1 := by nlinarith
  have hty : t * y ≤ 1 := by nlinarith
  have hSA : 1 - t * x ≤ S := by
    have : (1 - t * x) ^ 2 ≤ S ^ 2 := by rw [hsq]; nlinarith
    exact le_of_pow_le_pow_left₀ two_ne_zero hS0 this
  have hS3 : S ≤ 3 := by
    have : S ^ 2 ≤ 3 ^ 2 := by rw [hsq]; nlinarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) this
  -- `S - A ≥ ty` from `(S - A)(S + A) = 4ty` and `S + A ≤ 4`
  have h1 : (S - (1 - t * x)) * (S + (1 - t * x)) = 4 * t * y := by nlinarith
  have h2 : t * y ≤ S - (1 - t * x) := by nlinarith
  nlinarith

/-- `e^{sx} - 1 ≤ s e^x` for `0 ≤ s ≤ 1`. -/
private lemma bd_exp_scale (s x : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (s * x) - 1 ≤ s * Real.exp x := by
  have h := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ 0) hs0 (by linarith : 0 ≤ 1 - s)
    (by ring : s + (1 - s) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  linarith

variable {L : ℕ} [NeZero L]

/-- Weighted rows of `(1 - tQ)⁻¹` for a diagonally dominant `1 - tQ`, (A.32)
[ba:eq:stableinverse]. -/
private lemma bd_stable_weighted (Q : Matrix (Fin L) (Fin L) ℂ) (P : Matrix (Fin L) (Fin L) ℝ)
    (q₀ : ℂ) (hdiag : ∀ a, Q a a = q₀) (hoff : ∀ a b, a ≠ b → ‖Q a b‖ = P a b)
    (hP : ∀ a b, 0 ≤ P a b) (t μ y : ℝ) (ht0 : 0 ≤ t) (hμ : 0 ≤ μ) (hy : 0 < y)
    (hgap : ∀ a, t * ∑ b, (if b = a then 0 else Real.exp (μ * cycDist a b) * P a b) ≤
      ‖1 - (t : ℂ) * q₀‖ - y) :
    IsUnit (1 - (t : ℂ) • Q) ∧
      (∀ a, ∑ b, Real.exp (μ * cycDist a b) * ‖(1 - (t : ℂ) • Q)⁻¹ a b‖ ≤ 1 / y) ∧
      ∀ a b, a ≠ b → ‖1 - (t : ℂ) * q₀‖ * ‖(1 - (t : ℂ) • Q)⁻¹ a b‖ ≤
        t * ∑ c, (if c = b then 0 else ‖(1 - (t : ℂ) • Q)⁻¹ a c‖ * P c b) := by
  have hexp1 : ∀ a b : Fin L, 1 ≤ Real.exp (μ * cycDist a b) := fun a b =>
    Real.one_le_exp (by positivity)
  have hite : ∀ (f : Fin L → ℝ) (b : Fin L),
      ∑ c, (if c = b then 0 else f c) = ∑ c ∈ Finset.univ.erase b, f c := by
    intro f b
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
    simp only [↓reduceIte, zero_add]
    exact Finset.sum_congr rfl fun c hc => by simp [(Finset.mem_erase.mp hc).1]
  have hsplitC : ∀ (f : Fin L → ℂ) (b : Fin L),
      ∑ c, f c = f b + ∑ c, (if c = b then 0 else f c) := by
    intro f b
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
    simp only [↓reduceIte, zero_add]
    exact Finset.sum_congr rfl fun c hc => by simp [(Finset.mem_erase.mp hc).1]
  have hU : IsUnit (1 - (t : ℂ) • Q) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    refine det_ne_zero_of_sum_row_lt_diag fun k => ?_
    have hd : ‖(1 - (t : ℂ) • Q) k k‖ = ‖1 - (t : ℂ) * q₀‖ := by
      simp [Matrix.sub_apply, Matrix.smul_apply, hdiag]
    have ho : ∑ j ∈ Finset.univ.erase k, ‖(1 - (t : ℂ) • Q) k j‖ =
        t * ∑ j, (if j = k then 0 else P k j) := by
      rw [hite (fun j => P k j) k, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
      simp [Matrix.sub_apply, Matrix.smul_apply, hjk.symm, hoff k j hjk.symm, abs_of_nonneg ht0]
    rw [ho, hd]
    have h1 : t * ∑ j, (if j = k then 0 else P k j) ≤
        t * ∑ j, (if j = k then 0 else Real.exp (μ * cycDist k j) * P k j) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) ht0
      split_ifs
      · exact le_rfl
      · exact le_mul_of_one_le_left (hP k j) (hexp1 k j)
    linarith [hgap k]
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hU
  set R := (1 - (t : ℂ) • Q)⁻¹ with hR
  have hmul : R * (1 - (t : ℂ) • Q) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hent : ∀ a b, R a b * (1 - (t : ℂ) * q₀) =
      (if a = b then 1 else 0) + (t : ℂ) * ∑ c, (if c = b then 0 else R a c * Q c b) := by
    intro a b
    have h := congrFun (congrFun hmul a) b
    rw [Matrix.mul_apply] at h
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
      at h
    have h1 : ∑ c, R a c * (1 : Matrix (Fin L) (Fin L) ℂ) c b = R a b := by
      simp [Matrix.one_apply]
    have h2 : ∑ c, R a c * ((t : ℂ) * Q c b) =
        R a b * ((t : ℂ) * q₀) + (t : ℂ) * ∑ c, (if c = b then 0 else R a c * Q c b) := by
      rw [hsplitC (fun c => R a c * ((t : ℂ) * Q c b)) b, hdiag, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun c _ => by split_ifs <;> ring
    rw [h1, h2, Matrix.one_apply] at h
    linear_combination h
  have hnorm : ∀ a b, ‖R a b‖ * ‖1 - (t : ℂ) * q₀‖ ≤
      (if a = b then 1 else 0) + t * ∑ c, (if c = b then 0 else ‖R a c‖ * P c b) := by
    intro a b
    rw [← norm_mul, hent]
    refine (norm_add_le _ _).trans (add_le_add (by split_ifs <;> simp) ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)) ht0
    split_ifs with hcb
    · simp
    · rw [norm_mul, hoff c b hcb]
  refine ⟨hU, fun a => ?_, fun a b hab => ?_⟩
  · set N := ‖1 - (t : ℂ) * q₀‖ with hN
    set X := ∑ b, Real.exp (μ * cycDist a b) * ‖R a b‖ with hX
    have hX0 : 0 ≤ X := Finset.sum_nonneg fun b _ => by positivity
    have key : X * N ≤ 1 + X * (N - y) := by
      calc X * N = ∑ b, Real.exp (μ * cycDist a b) * (‖R a b‖ * N) := by
            rw [hX, Finset.sum_mul]; exact Finset.sum_congr rfl fun b _ => by ring
        _ ≤ ∑ b, Real.exp (μ * cycDist a b) * ((if a = b then 1 else 0) +
              t * ∑ c, (if c = b then 0 else ‖R a c‖ * P c b)) :=
            Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hnorm a b) (by positivity)
        _ = 1 + t * ∑ c, ∑ b, (if c = b then 0 else
              Real.exp (μ * cycDist a b) * (‖R a c‖ * P c b)) := by
            have e1 : ∑ b, Real.exp (μ * cycDist a b) * ((if a = b then (1 : ℝ) else 0) +
                t * ∑ c, (if c = b then 0 else ‖R a c‖ * P c b)) =
                ∑ b, Real.exp (μ * cycDist a b) * (if a = b then (1 : ℝ) else 0) +
                ∑ b, Real.exp (μ * cycDist a b) *
                  (t * ∑ c, (if c = b then 0 else ‖R a c‖ * P c b)) := by
              rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => by ring
            have e2 : ∑ b, Real.exp (μ * cycDist a b) * (if a = b then (1 : ℝ) else 0) = 1 := by
              simp [bd_cycDist_self]
            have e3 : ∑ b, Real.exp (μ * cycDist a b) *
                (t * ∑ c, (if c = b then 0 else ‖R a c‖ * P c b)) =
                t * ∑ c, ∑ b, (if c = b then 0 else
                  Real.exp (μ * cycDist a b) * (‖R a c‖ * P c b)) := by
              rw [Finset.sum_comm, Finset.mul_sum]
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
              exact Finset.sum_congr rfl fun c _ => by split_ifs <;> ring
            rw [e1, e2, e3]
        _ ≤ 1 + ∑ c, Real.exp (μ * cycDist a c) * ‖R a c‖ *
              (t * ∑ b, (if b = c then 0 else Real.exp (μ * cycDist c b) * P c b)) := by
            rw [Finset.mul_sum]
            refine add_le_add le_rfl (Finset.sum_le_sum fun c _ => ?_)
            have hc0 : 0 ≤ Real.exp (μ * cycDist a c) * ‖R a c‖ := by positivity
            calc t * ∑ b, (if c = b then 0 else Real.exp (μ * cycDist a b) * (‖R a c‖ * P c b))
                = ∑ b, t * (if c = b then 0 else
                    Real.exp (μ * cycDist a b) * (‖R a c‖ * P c b)) := Finset.mul_sum _ _ _
              _ ≤ ∑ b, Real.exp (μ * cycDist a c) * ‖R a c‖ *
                    (t * (if b = c then 0 else Real.exp (μ * cycDist c b) * P c b)) := by
                  refine Finset.sum_le_sum fun b _ => ?_
                  by_cases hcb : c = b
                  · subst hcb; simp
                  · have hbc : ¬ b = c := fun h => hcb h.symm
                    simp only [hcb, hbc, ↓reduceIte]
                    have htri : Real.exp (μ * cycDist a b) ≤
                        Real.exp (μ * cycDist a c) * Real.exp (μ * cycDist c b) := by
                      rw [← Real.exp_add, ← mul_add]
                      apply Real.exp_le_exp.mpr
                      have : (cycDist a b : ℝ) ≤ cycDist a c + cycDist c b := by
                        exact_mod_cast bd_cycDist_tri a c b
                      nlinarith
                    have h0 : 0 ≤ ‖R a c‖ * P c b := mul_nonneg (norm_nonneg _) (hP c b)
                    calc t * (Real.exp (μ * cycDist a b) * (‖R a c‖ * P c b))
                        ≤ t * (Real.exp (μ * cycDist a c) * Real.exp (μ * cycDist c b) *
                            (‖R a c‖ * P c b)) :=
                          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htri h0) ht0
                      _ = _ := by ring
              _ = Real.exp (μ * cycDist a c) * ‖R a c‖ *
                    (t * ∑ b, (if b = c then 0 else Real.exp (μ * cycDist c b) * P c b)) := by
                  rw [← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ 1 + ∑ c, Real.exp (μ * cycDist a c) * ‖R a c‖ * (N - y) := by
            gcongr with c
            exact hgap c
        _ = 1 + X * (N - y) := by rw [hX, Finset.sum_mul]
    rw [le_div_iff₀ hy]
    nlinarith
  · have h := hnorm a b
    simp only [hab, ↓reduceIte, zero_add] at h
    rw [mul_comm]; exact h

end BdStable

section BdStable2

/-- Tilt rate of the same-sign kernel. -/
private def bdμs (C c' : ℝ) : ℝ := bdμ₀ C c' * bdp₀ C c' / (2 * bdCP C c' * bdCm C ^ 2 + 2)

private lemma bdμs_facts {C c' : ℝ} (hc' : 0 < c') (hp₀ : bdp₀ C c' ≤ 1) :
    0 < bdμs C c' ∧ bdμs C c' ≤ bdμ₀ C c' ∧
      bdμs C c' / bdμ₀ C c' * (bdCP C c' * bdCm C ^ 2) ≤ bdp₀ C c' / 2 := by
  have hμ₀ := (bdμ₀_facts C hc').1
  have hp := bdp₀_pos C hc'
  have hCP := bdCP_pos C hc'
  have hD : 0 < 2 * bdCP C c' * bdCm C ^ 2 + 2 := by positivity
  refine ⟨by unfold bdμs; positivity, ?_, ?_⟩
  · unfold bdμs
    rw [div_le_iff₀ hD]
    have h1 : bdp₀ C c' ≤ 2 * bdCP C c' * bdCm C ^ 2 + 2 := by nlinarith [sq_nonneg (bdCm C)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hμ₀.le]
  · unfold bdμs
    rw [show bdμ₀ C c' * bdp₀ C c' / (2 * bdCP C c' * bdCm C ^ 2 + 2) / bdμ₀ C c' =
      bdp₀ C c' / (2 * bdCP C c' * bdCm C ^ 2 + 2) by field_simp]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hD (by norm_num)]
    nlinarith [sq_nonneg (bdCm C)]

variable {C B₀ c' g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ}

/-- Off-diagonal mass of `P` with weight `e^{μ₀ d}`. -/
private lemma bd_model_offmass [NeZero L] (h : BdModel C B₀ c' g L E m) (a : Fin L) :
    ∑ b, (if b = a then 0 else Real.exp (bdμ₀ C c' * cycDist a b) *
      pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) a b) ≤ bdCP C c' * g ^ 2 := by
  rw [h.P_eq]
  refine le_of_eq_of_le ?_ h.good.off
  simp only [bdP, Matrix.of_apply, bd_cycDist_eq]
  rw [← bd_sum_sub a (fun y => if y = 0 then 0 else
    Real.exp (bdμ₀ C c' * bdD y) * bdF g L E m (bdD y))]
  exact Finset.sum_congr rfl fun b _ => by simp [sub_eq_zero]

/-- Off-diagonal weighted rows of `P`: `Σ_{b ≠ a} e^{μ d} P_{ab} ≤ (1 - γ|m|²) + (μ/μ₀) C_P g²`. -/
private lemma bd_model_offrow [NeZero L] (hc' : 0 < c') (h : BdModel C B₀ c' g L E m) (μ : ℝ)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ bdμ₀ C c') (a : Fin L) :
    ∑ b, (if b = a then 0 else Real.exp (μ * cycDist a b) *
      pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) a b) ≤
        (1 - gammaG g * ‖m‖ ^ 2) + μ / bdμ₀ C c' * (bdCP C c' * g ^ 2) := by
  have hμ₀ := (bdμ₀_facts C hc').1
  rw [h.P_eq]
  set F := bdF g L E m
  have hF0 := h.good.nonneg
  have hF1 := h.good.sum
  have hPaa : bdP F L a a = gammaG g * ‖m‖ ^ 2 := by
    rw [← h.P_eq]; simp [pairP, h.diag]
  have hrow := bdP_row_one (L := L) F hF1 a
  have e1 : ∑ b, (if b = a then 0 else bdP F L a b) = 1 - gammaG g * ‖m‖ ^ 2 := by
    have hs : ∑ b, bdP F L a b = ∑ b, (if b = a then bdP F L a b else 0) +
        ∑ b, (if b = a then 0 else bdP F L a b) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by split_ifs <;> ring
    rw [Finset.sum_ite_eq', hrow] at hs
    simp only [Finset.mem_univ, ↓reduceIte, hPaa] at hs
    linarith
  have e2 : ∑ b, (if b = a then 0 else Real.exp (bdμ₀ C c' * cycDist a b) * bdP F L a b) ≤
      bdCP C c' * g ^ 2 := by
    have := bd_model_offmass h a
    rw [h.P_eq] at this
    exact this
  have hs : 0 ≤ μ / bdμ₀ C c' := div_nonneg hμ0 hμ₀.le
  have hs1 : μ / bdμ₀ C c' ≤ 1 := (div_le_one hμ₀).mpr hμ
  calc ∑ b, (if b = a then 0 else Real.exp (μ * cycDist a b) * bdP F L a b)
      ≤ ∑ b, ((if b = a then 0 else bdP F L a b) + μ / bdμ₀ C c' *
          (if b = a then 0 else Real.exp (bdμ₀ C c' * cycDist a b) * bdP F L a b)) := by
        refine Finset.sum_le_sum fun b _ => ?_
        split_ifs
        · simp
        · have h1 := bd_exp_scale (μ / bdμ₀ C c') (bdμ₀ C c' * cycDist a b) hs hs1
          rw [show μ / bdμ₀ C c' * (bdμ₀ C c' * cycDist a b) = μ * cycDist a b by
            field_simp] at h1
          have h2 : 0 ≤ bdP F L a b := hF0 _
          nlinarith
    _ = (1 - gammaG g * ‖m‖ ^ 2) + μ / bdμ₀ C c' *
          ∑ b, (if b = a then 0 else Real.exp (bdμ₀ C c' * cycDist a b) * bdP F L a b) := by
        rw [Finset.sum_add_distrib, e1, Finset.mul_sum]
    _ ≤ _ := by gcongr

/-- Weighted and off-diagonal bounds for `(1 - tQ)⁻¹`, `0 ≤ t ≤ 1`. -/
private lemma bd_model_stable [NeZero L] (hc' : 0 < c') (hgC : g ≤ C) (hg : 0 ≤ g)
    (h : BdModel C B₀ c' g L E m) (hcm : c' ≤ m.im) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (μ : ℝ)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ bdμs C c') :
    let Q := pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)
    let P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)
    (∀ a, ∑ b, Real.exp (μ * cycDist a b) * ‖(1 - (t : ℂ) • Q)⁻¹ a b‖ ≤ 2 / bdp₀ C c') ∧
      ∀ a b, a ≠ b → ‖(1 - (t : ℂ) • Q)⁻¹ a b‖ ≤
        1 / bdp₀ C c' * ∑ c, (if c = b then 0 else ‖(1 - (t : ℂ) • Q)⁻¹ a c‖ * P c b) := by
  intro Q P
  have hp₀1 := bdGood_p₀_le _ _ _ _ _ _ h.good
  obtain ⟨hμs0, hμs1, hμs2⟩ := bdμs_facts hc' hp₀1
  have hp := bdp₀_pos C hc'
  obtain ⟨hγ0, hγ1, hγC⟩ := h.gam
  set γ := gammaG g
  set M := dysonMat (hopB g) γ L E m
  have hdiag : ∀ a, Q a a = (γ : ℂ) * m ^ 2 := fun a => by
    change (γ : ℂ) * (dysonMat (hopB g) γ L E m a a) ^ 2 = _
    rw [h.diag]
  have hoff : ∀ a b, a ≠ b → ‖Q a b‖ = P a b := fun a b _ => by
    change ‖(γ : ℂ) * M a b ^ 2‖ = γ * ‖M a b‖ ^ 2
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hγ0]
  have hP0 : ∀ a b, 0 ≤ P a b := fun a b => by
    change 0 ≤ γ * ‖M a b‖ ^ 2
    exact mul_nonneg hγ0.le (sq_nonneg _)
  have hgapm := bd_gap γ hγ0 m h.m_sq t ht0 ht1
  have hyim : bdp₀ C c' ≤ γ * m.im ^ 2 := by
    have h1 : 1 / bdCm C ^ 2 ≤ γ := by
      have := (bdCm_ge C).1
      rw [div_le_iff₀ (by positivity)]; linarith
    have h2 : c' ^ 2 ≤ m.im ^ 2 := pow_le_pow_left₀ hc'.le hcm 2
    unfold bdp₀
    calc c' ^ 2 / bdCm C ^ 2 = 1 / bdCm C ^ 2 * c' ^ 2 := by ring
      _ ≤ γ * m.im ^ 2 := mul_le_mul h1 h2 (by positivity) hγ0.le
  have hgC2 : g ^ 2 ≤ bdCm C ^ 2 := pow_le_pow_left₀ hg (hgC.trans (bdCm_ge C).2) 2
  have hgap : ∀ a, t * ∑ b, (if b = a then 0 else Real.exp (μ * cycDist a b) * P a b) ≤
      ‖1 - (t : ℂ) * ((γ : ℂ) * m ^ 2)‖ - bdp₀ C c' / 2 := by
    intro a
    have h1 := bd_model_offrow hc' h μ hμ0 (hμ.trans hμs1) a
    have h2 : μ / bdμ₀ C c' * (bdCP C c' * g ^ 2) ≤ bdp₀ C c' / 2 := by
      have hμ₀ := (bdμ₀_facts C hc').1
      refine le_trans ?_ hμs2
      have hCP := (bdCP_pos C hc').le
      apply mul_le_mul (div_le_div_of_nonneg_right hμ hμ₀.le) (by gcongr)
        (by positivity) (div_nonneg hμs0.le hμ₀.le)
    have h3 : 0 ≤ ∑ b, (if b = a then 0 else Real.exp (μ * cycDist a b) * P a b) :=
      Finset.sum_nonneg fun b _ => by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (by positivity) (hP0 a b)
    have h4 : 0 ≤ 1 - γ * ‖m‖ ^ 2 := by linarith [h.m_sq]
    calc t * ∑ b, (if b = a then 0 else Real.exp (μ * cycDist a b) * P a b)
        ≤ t * ((1 - γ * ‖m‖ ^ 2) + bdp₀ C c' / 2) := by
          apply mul_le_mul_of_nonneg_left _ ht0; linarith
      _ = t * (1 - γ * ‖m‖ ^ 2) + t * (bdp₀ C c' / 2) := by ring
      _ ≤ t * (1 - γ * ‖m‖ ^ 2) + bdp₀ C c' / 2 := by nlinarith
      _ ≤ _ := by linarith
  obtain ⟨-, hrow, hoffb⟩ := bd_stable_weighted Q P ((γ : ℂ) * m ^ 2) hdiag hoff hP0 t μ
    (bdp₀ C c' / 2) ht0 hμ0 (by positivity) hgap
  refine ⟨fun a => by rw [show 2 / bdp₀ C c' = 1 / (bdp₀ C c' / 2) by field_simp]; exact hrow a,
    fun a b hab => ?_⟩
  have h1 := hoffb a b hab
  have h2 : bdp₀ C c' ≤ ‖1 - (t : ℂ) * ((γ : ℂ) * m ^ 2)‖ := by
    have h3 : 0 ≤ t * (1 - γ * ‖m‖ ^ 2) := mul_nonneg ht0 (by linarith [h.m_sq])
    linarith
  have h3 : 0 ≤ ∑ c, (if c = b then 0 else ‖(1 - (t : ℂ) • Q)⁻¹ a c‖ * P c b) :=
    Finset.sum_nonneg fun c _ => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (norm_nonneg _) (hP0 c b)
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hp]
  calc ‖(1 - (t : ℂ) • Q)⁻¹ a b‖ * bdp₀ C c'
      ≤ ‖(1 - (t : ℂ) • Q)⁻¹ a b‖ * ‖1 - (t : ℂ) * ((γ : ℂ) * m ^ 2)‖ :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ ≤ t * ∑ c, (if c = b then 0 else ‖(1 - (t : ℂ) • Q)⁻¹ a c‖ * P c b) := by
        rw [mul_comm]; exact h1
    _ ≤ _ := mul_le_of_le_one_left h3 ht1

end BdStable2

/-! ### Kernel bounds for the bounded-coupling kernel -/

section BdPkg

variable {C B₀ c' g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ}

/-- `ℓ_t ≥ 1`. -/
private lemma bd_ell_ge (hL : 1 ≤ L) (hg : 0 ≤ g) (t : ℝ) :
    1 ≤ ellProp g L t := by
  unfold ellProp
  have hγ : 0 < gammaG g := by unfold gammaG; have : 0 < max 1 g := by positivity
                               positivity
  have hX : 0 ≤ g / Real.sqrt (gammaG g * (1 - t)) := div_nonneg hg (Real.sqrt_nonneg _)
  exact (bd_ell L hL _ hX).1

/-- The profile, the weighted row and the diagonal of `K` at bounded coupling. -/
private lemma bd_pkg (hC : 0 < C) (hg : 0 ≤ g) (hgC : g ≤ C) [NeZero L]
    (h : BdModel C B₀ c' g L E m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    let K := mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) t
    let ℓ := ellProp g L t
    (∀ a b, 0 ≤ K a b) ∧ (∀ a, ∑ b, K a b = (1 - t)⁻¹) ∧
    (∀ a b, K a b ≤ 10 * (2 + 2 * bdCm C) / bdc4 C (bdp₀ C c') (bdc₁ C B₀ c') / ((1 - t) * ℓ) *
        Real.exp (-(bdCmu (bdμ₀ C c') (bdCP C c') / 2 * cycDist a b / ℓ))) ∧
    (∀ a, ∑ b, Real.exp (bdCmu (bdμ₀ C c') (bdCP C c') * cycDist a b / ℓ) * K a b ≤ 7 / (1 - t)) ∧
    ∀ a, 1 / (4 * π * (1 + bdC2 (bdμ₀ C c') (bdCP C c') / 2)) / ((1 - t) * ℓ) ≤ 1 + t * K a a ∧
      1 + t * K a a ≤ (2 + 2 * bdCm C) / bdcB C (bdc₁ C B₀ c') / ((1 - t) * ℓ) ∧
      bdp₀ C c' / (8 * π * (1 + bdC2 (bdμ₀ C c') (bdCP C c') / 2)) / ((1 - t) * ℓ) ≤ K a a := by
  intro K ℓ
  obtain ⟨hγ0, hγ1, hγC⟩ := h.gam
  have hK : K = mixedKer (bdP (bdF g L E m) L) t := by simp only [K, h.P_eq]
  have hℓ : ℓ = min (L : ℝ) (1 + g / Real.sqrt (gammaG g * (1 - t))) := rfl
  have hCm := (bdCm_ge C).1
  rw [hK, hℓ]
  obtain ⟨hK0, hKr⟩ := mixedKer_nonneg_row (bdP (bdF g L E m) L)
    (bdP_nonneg _ h.good.nonneg) (bdP_row_one _ h.good.sum) t ht0 ht1
  refine ⟨hK0, hKr, fun a b => ?_, fun a => ?_, fun a => ?_⟩
  · exact bd_profile _ C (bdCm C) (gammaG g) g _ _ _ _ h.good hC hCm hg hgC hγ0 hγ1 hγC t ht0 ht1
      a b
  · exact bd_weighted _ (gammaG g) g _ _ _ _ h.good hg hγ0 hγ1 t ht0 ht1 a
  · exact bd_diag _ C (bdCm C) (gammaG g) g _ _ _ _ h.good hC hCm hg hgC hγ0 hγ1 hγC t ht0 ht1 a

end BdPkg

/-! ### Time derivatives of the mixed kernel -/

section BdDeriv

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Operator in
/-- Derivative in `t` of an entry of `X(1 - tP)⁻¹` at an invertible point. -/
private lemma bd_hasDeriv_inv (X P : Matrix n n ℝ) (t : ℝ) (hU : IsUnit (1 - t • P)) (a b : n) :
    HasDerivAt (fun t' : ℝ => (X * (1 - t' • P)⁻¹) a b)
      ((X * ((1 - t • P)⁻¹ * P * (1 - t • P)⁻¹)) a b) t := by
  let ℓ : Matrix n n ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous (Matrix.entryLinearMap ℝ ℝ a b) 1 (by
      intro A
      simp only [Matrix.entryLinearMap_apply, one_mul]
      have h : ‖A a b‖₊ ≤ ‖A‖₊ := by
        rw [Matrix.linfty_opNNNorm_def]
        exact le_trans (Finset.single_le_sum (f := fun j => ‖A a j‖₊) (fun _ _ => zero_le)
          (Finset.mem_univ b)) (Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ a))
      exact_mod_cast h)
  have hg := ((hasDerivAt_id t).smul_const P).const_sub (1 : Matrix n n ℝ)
  obtain ⟨x, hx⟩ := hU
  have h1 := hasFDerivAt_ringInverse (𝕜 := ℝ) x
  rw [hx] at h1
  have h2 := (h1.comp_hasDerivAt t (by simpa using hg)).const_mul X
  have h3 := ℓ.hasFDerivAt.comp_hasDerivAt t h2
  convert h3 using 1
  · funext t'
    simp [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  · simp [ℓ, hx, Matrix.nonsing_inv_eq_ringInverse]

omit [DecidableEq n] in
/-- Entrywise product rule for matrix-valued functions. -/
private lemma bd_hasDeriv_mul (X Y : ℝ → Matrix n n ℝ) (X' Y' : Matrix n n ℝ) (t : ℝ)
    (hX : ∀ a b, HasDerivAt (fun s => X s a b) (X' a b) t)
    (hY : ∀ a b, HasDerivAt (fun s => Y s a b) (Y' a b) t) (a b : n) :
    HasDerivAt (fun s => (X s * Y s) a b) ((X' * Y t + X t * Y') a b) t := by
  simp only [Matrix.mul_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun c _ => (hX a c).mul (hY c b)

/-- `∂_t K_t = K_t²` for `|t| < 1`. -/
private lemma bd_hasDeriv_K (P : Matrix n n ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) (t : ℝ) (ht : |t| < 1) (a b : n) :
    HasDerivAt (fun s => mixedKer P s a b) ((mixedKer P t ^ 2) a b) t := by
  have hU := bd_isUnit P hP hrow t ht
  have h := bd_hasDeriv_inv P P t hU a b
  have hc : (1 - t • P)⁻¹ * P = P * (1 - t • P)⁻¹ := by
    have h1 := bd_inv_mul P t hU
    have h2 := bd_mul_inv P t hU
    calc (1 - t • P)⁻¹ * P = (1 - t • P)⁻¹ * P * ((1 - t • P) * (1 - t • P)⁻¹) := by
          rw [h2, Matrix.mul_one]
      _ = (1 - t • P)⁻¹ * (P * (1 - t • P)) * (1 - t • P)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (1 - t • P)⁻¹ * ((1 - t • P) * P) * (1 - t • P)⁻¹ := by
          congr 2; simp [Matrix.mul_sub, Matrix.sub_mul]
      _ = P * (1 - t • P)⁻¹ := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have e : P * ((1 - t • P)⁻¹ * P * (1 - t • P)⁻¹) = mixedKer P t ^ 2 := by
    unfold mixedKer
    rw [sq]; simp only [Matrix.mul_assoc]
  rw [e] at h
  exact h

/-- `∂_t K_t^{k+1} = (k+1) K_t^{k+2}` for `|t| < 1`. -/
private lemma bd_hasDeriv_Kpow (P : Matrix n n ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) (t : ℝ) (ht : |t| < 1) (k : ℕ) (a b : n) :
    HasDerivAt (fun s => (mixedKer P s ^ (k + 1)) a b)
      ((((k : ℝ) + 1) • mixedKer P t ^ (k + 2)) a b) t := by
  induction k generalizing a b with
  | zero =>
    simpa using bd_hasDeriv_K P hP hrow t ht a b
  | succ k ih =>
    have h := bd_hasDeriv_mul (fun s => mixedKer P s ^ (k + 1)) (fun s => mixedKer P s)
      (((k : ℝ) + 1) • mixedKer P t ^ (k + 2)) (mixedKer P t ^ 2) t ih
      (fun a b => bd_hasDeriv_K P hP hrow t ht a b) a b
    have e1 : (fun s => (mixedKer P s ^ (k + 1 + 1)) a b) =
        (fun s => (mixedKer P s ^ (k + 1) * mixedKer P s) a b) := by
      funext s; rw [pow_succ]
    have e2 : (((k : ℝ) + 1) • mixedKer P t ^ (k + 2)) * mixedKer P t +
        mixedKer P t ^ (k + 1) * mixedKer P t ^ 2 =
        ((((k + 1 : ℕ) : ℝ) + 1) • mixedKer P t ^ (k + 1 + 2)) := by
      rw [Matrix.smul_mul, ← pow_succ, ← pow_add]
      push_cast
      rw [show k + 1 + 2 = k + 2 + 1 by ring, show k + 1 + 2 = k + 3 by ring]
      module
    rw [e1, ← e2]
    exact h

/-- `∂_t^j K_t = j! K_t^{j+1}` for `0 ≤ t < 1`. -/
private lemma bd_iteratedDeriv_K (P : Matrix n n ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) (j : ℕ) (a b : n) :
    ∀ t : ℝ, |t| < 1 → iteratedDeriv j (fun t' : ℝ => mixedKer P t' a b) t =
      (j.factorial : ℝ) * (mixedKer P t ^ (j + 1)) a b := by
  induction j with
  | zero =>
    intro t _
    simp
  | succ j ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have hopen : IsOpen {s : ℝ | |s| < 1} := isOpen_lt continuous_abs continuous_const
    have hev : iteratedDeriv j (fun t' : ℝ => mixedKer P t' a b) =ᶠ[𝓝 t]
        fun s => (j.factorial : ℝ) * (mixedKer P s ^ (j + 1)) a b := by
      filter_upwards [hopen.mem_nhds ht] with s hs
      exact ih s hs
    rw [hev.deriv_eq]
    have hd := (bd_hasDeriv_Kpow P hP hrow t ht j a b).const_mul (j.factorial : ℝ)
    rw [hd.deriv]
    rw [Matrix.smul_apply, smul_eq_mul, Nat.factorial_succ]
    push_cast
    ring

end BdDeriv

/-! ### The comparison kernel -/

section BdCompare

private lemma bd_cosh_lamGeo {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    Real.cosh (lamGeo D δ) = 1 + δ / (2 * D) :=
  Real.cosh_arcosh (by have : 0 < δ / (2 * D) := by positivity
                       linarith)

private lemma bd_lamGeo_pos {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) : 0 < lamGeo D δ :=
  Real.arcosh_pos (by have : 0 < δ / (2 * D) := by positivity
                      linarith)

private lemma bd_sqrt_eq_sinh {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    Real.sqrt (δ * (δ + 4 * D)) = 2 * D * Real.sinh (lamGeo D δ) := by
  have hx1 : 1 ≤ 1 + δ / (2 * D) := by
    have : 0 < δ / (2 * D) := by positivity
    linarith
  unfold lamGeo
  rw [Real.sinh_arcosh hx1]
  have h2D : 0 ≤ 2 * D := by positivity
  rw [show 2 * D * Real.sqrt ((1 + δ / (2 * D)) ^ 2 - 1) =
      Real.sqrt ((2 * D) ^ 2 * ((1 + δ / (2 * D)) ^ 2 - 1)) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h2D]]
  congr 1
  field_simp
  ring

/-- `λ = arcosh(1 + δ/(2D)) ≤ √(δ/D)`. -/
private lemma bd_lamGeo_le {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    lamGeo D δ ≤ Real.sqrt (δ / D) := by
  have hx : 0 ≤ Real.sqrt (δ / D) := Real.sqrt_nonneg _
  have h1 : 1 + δ / (2 * D) ≤ Real.cosh (Real.sqrt (δ / D)) := by
    -- `cosh u ≥ 1 + u²/2`
    have hsq : Real.sqrt (δ / D) ^ 2 = δ / D := Real.sq_sqrt (by positivity)
    have hc : 1 + Real.sqrt (δ / D) ^ 2 / 2 ≤ Real.cosh (Real.sqrt (δ / D)) := by
      set u := Real.sqrt (δ / D)
      have h2 := Real.cosh_two_mul (u / 2)
      rw [show 2 * (u / 2) = u by ring, Real.cosh_sq] at h2
      have h3 : u / 2 ≤ Real.sinh (u / 2) := Real.self_le_sinh_iff.mpr (by positivity)
      have h4 : (u / 2) ^ 2 ≤ Real.sinh (u / 2) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
      nlinarith
    rw [hsq] at hc
    have : δ / (2 * D) = δ / D / 2 := by field_simp
    linarith
  unfold lamGeo
  calc Real.arcosh (1 + δ / (2 * D)) ≤ Real.arcosh (Real.cosh (Real.sqrt (δ / D))) :=
        (Real.arcosh_le_arcosh (by have : 0 < δ / (2 * D) := by positivity
                                   linarith) (Real.cosh_pos _)).mpr h1
    _ = Real.sqrt (δ / D) := Real.arcosh_cosh hx

/-- The line ratio `τ = e^{-λ}` of the comparison mixed kernel. -/
private lemma bd_tau_facts {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    0 < Real.exp (-lamGeo D δ) ∧ Real.exp (-lamGeo D δ) < 1 ∧
      Real.exp (-lamGeo D δ) + (Real.exp (-lamGeo D δ))⁻¹ = 2 + δ / D ∧
      (Real.exp (-lamGeo D δ))⁻¹ - Real.exp (-lamGeo D δ) = Real.sqrt (δ * (δ + 4 * D)) / D := by
  have hlam := bd_lamGeo_pos hD hδ
  have hc := bd_cosh_lamGeo hD hδ
  have hs := bd_sqrt_eq_sinh hD hδ
  refine ⟨Real.exp_pos _, by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith), ?_, ?_⟩
  · rw [← Real.exp_neg, neg_neg]
    have : Real.exp (-lamGeo D δ) + Real.exp (lamGeo D δ) = 2 * Real.cosh (lamGeo D δ) := by
      rw [Real.cosh_eq]; ring
    rw [this, hc]; field_simp
  · rw [← Real.exp_neg, neg_neg, hs]
    have : Real.exp (lamGeo D δ) - Real.exp (-lamGeo D δ) = 2 * Real.sinh (lamGeo D δ) := by
      rw [Real.sinh_eq]; ring
    rw [this]; field_simp

/-- The comparison mixed kernel is explicit:
`P₀ = φ₀ G_σ`, `φ₀ = (1-σ)/(1+σ)` gives `P₀(1 - tP₀)⁻¹ = S⁻¹ G_τ`, `S = √(δ(δ+4D))`. -/
private lemma bd_K0_eq {L : ℕ} (hL : 3 ≤ L) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (D : ℝ) (hDdef : D = σ / (1 - σ) ^ 2)
    (P₀ : Matrix (Fin L) (Fin L) ℝ) (hP₀ : P₀ = ((1 - σ) / (1 + σ)) • bgC σ L) :
    mixedKer P₀ (1 - δ) =
      (Real.sqrt (δ * (δ + 4 * D)))⁻¹ • bgC (Real.exp (-lamGeo D δ)) L := by
  have hD : 0 < D := by rw [hDdef]; have : 0 < 1 - σ := by linarith
                        positivity
  obtain ⟨hτ0, hτ1, hτsum, hτdiff⟩ := bd_tau_facts hD hδ
  set τ := Real.exp (-lamGeo D δ)
  set S := Real.sqrt (δ * (δ + 4 * D)) with hS
  have hSpos : 0 < S := Real.sqrt_pos.mpr (by positivity)
  have hσL : 1 - σ ^ L ≠ 0 := by
    have := pow_lt_one₀ hσ0.le hσ1 (show L ≠ 0 by omega); linarith
  have hτL : 1 - τ ^ L ≠ 0 := by
    have := pow_lt_one₀ hτ0.le hτ1 (show L ≠ 0 by omega); linarith
  have hστ : σ⁻¹ - σ ≠ 0 := by
    have : σ < σ⁻¹ := by
      calc σ < 1 := hσ1
        _ < σ⁻¹ := (one_lt_inv₀ hσ0).mpr hσ1
    linarith
  have h1σ : 1 - σ ≠ 0 := by linarith
  have h1σ' : 1 + σ ≠ 0 := by linarith
  have hφσ : (1 - σ) / (1 + σ) * (σ⁻¹ - σ) = 1 / D := by
    rw [hDdef]; field_simp; ring
  have hM3 : σ + σ⁻¹ - (1 - δ) * ((1 - σ) / (1 + σ)) * (σ⁻¹ - σ) = τ + τ⁻¹ := by
    rw [hτsum, mul_assoc, hφσ, hDdef]; field_simp; ring
  have hB : (1 - δ) / S * (τ⁻¹ - τ) = (1 - δ) * ((1 - σ) / (1 + σ)) * (σ⁻¹ - σ) := by
    rw [hτdiff, mul_assoc, hφσ]; field_simp
  have hinv := bg_geom_inv hL σ τ ((1 - σ) / (1 + σ)) ((1 - δ) / S) (1 - δ) hσ0.ne' hσL hτ0.ne'
    hτL hστ hM3 hB
  have hsm : (1 - δ) • P₀ = ((1 - δ) * ((1 - σ) / (1 + σ))) • bgC σ L := by
    rw [hP₀, smul_smul]
  have hinv' : (1 - (1 - δ) • P₀) * (1 + ((1 - δ) / S) • bgC τ L) = 1 := by rw [hsm]; exact hinv
  have hI : (1 - (1 - δ) • P₀)⁻¹ = 1 + ((1 - δ) / S) • bgC τ L := Matrix.inv_eq_right_inv hinv'
  have hdet : IsUnit (1 - (1 - δ) • P₀).det := Matrix.isUnit_det_of_right_inverse hinv'
  have hmul : (1 - (1 - δ) • P₀) * (1 - (1 - δ) • P₀)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have htK : (1 - δ) • mixedKer P₀ (1 - δ) = ((1 - δ) / S) • bgC τ L := by
    have e : (1 - δ) • mixedKer P₀ (1 - δ) = (1 - (1 - δ) • P₀)⁻¹ - 1 := by
      have e1 : (1 - (1 - δ) • P₀) * (1 - (1 - δ) • P₀)⁻¹ =
          (1 - (1 - δ) • P₀)⁻¹ - (1 - δ) • mixedKer P₀ (1 - δ) := by
        unfold mixedKer
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
      rw [hmul] at e1
      calc (1 - δ) • mixedKer P₀ (1 - δ) =
          (1 - (1 - δ) • P₀)⁻¹ - ((1 - (1 - δ) • P₀)⁻¹ - (1 - δ) • mixedKer P₀ (1 - δ)) := by
            abel
        _ = (1 - (1 - δ) • P₀)⁻¹ - 1 := by rw [← e1]
    rw [e, hI]; abel
  have ht : (1 - δ) ≠ 0 := by linarith
  have := congrArg (fun X => (1 - δ)⁻¹ • X) htK
  simp only [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
  rw [this]
  congr 1
  field_simp

/-- `|e^{-x} - e^{-y}| ≤ |x - y| (e^{-x} + e^{-y})` for `x, y ≥ 0`. -/
private lemma bd_exp_neg_lip (x y : ℝ) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| * (Real.exp (-x) + Real.exp (-y)) := by
  rcases le_total x y with h | h
  · have h1 : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    have h2 : Real.exp (-x) - Real.exp (-y) ≤ (y - x) * Real.exp (-x) := by
      have h3 : Real.exp (-y) = Real.exp (-x) * Real.exp (-(y - x)) := by
        rw [← Real.exp_add]; ring_nf
      rw [h3]
      have h4 := Real.add_one_le_exp (-(y - x))
      nlinarith [Real.exp_pos (-x)]
    nlinarith [Real.exp_pos (-y)]
  · have h1 : Real.exp (-x) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    have h2 : Real.exp (-y) - Real.exp (-x) ≤ (x - y) * Real.exp (-y) := by
      have h3 : Real.exp (-x) = Real.exp (-y) * Real.exp (-(x - y)) := by
        rw [← Real.exp_add]; ring_nf
      rw [h3]
      have h4 := Real.add_one_le_exp (-(x - y))
      nlinarith [Real.exp_pos (-y)]
    nlinarith [Real.exp_pos (-x)]

/-- Lipschitz bound for the periodized two-sided exponential profile. -/
private lemma bd_bgV_lip {lam : ℝ} (hlam : 0 < lam) {L : ℕ} (hL : 1 ≤ L) (r r' : ℕ) (hr : r ≤ L)
    (hr' : r' ≤ L) :
    |bgV (Real.exp (-lam)) L r - bgV (Real.exp (-lam)) L r'| ≤
      lam * |(r : ℝ) - r'| * (bgV (Real.exp (-lam)) L r + bgV (Real.exp (-lam)) L r') := by
  set τ := Real.exp (-lam)
  have hτ0 : 0 < τ := Real.exp_pos _
  have hτ1 : τ < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hτL : 0 < 1 - τ ^ L := by have := pow_lt_one₀ hτ0.le hτ1 (show L ≠ 0 by omega); linarith
  have hp : ∀ k : ℕ, τ ^ k = Real.exp (-(lam * k)) := fun k => by
    rw [← Real.exp_nat_mul]; ring_nf
  unfold bgV
  rw [← sub_div, abs_div, abs_of_pos hτL, ← add_div, mul_div_assoc',
    div_le_div_iff_of_pos_right hτL]
  have h1 := bd_exp_neg_lip (lam * r) (lam * r')
  have h2 := bd_exp_neg_lip (lam * (L - r : ℕ)) (lam * (L - r' : ℕ))
  rw [← hp, ← hp] at h1 h2
  have e1 : |lam * (r : ℝ) - lam * r'| = lam * |(r : ℝ) - r'| := by
    rw [← mul_sub, abs_mul, abs_of_pos hlam]
  have e2 : |lam * ((L - r : ℕ) : ℝ) - lam * ((L - r' : ℕ) : ℝ)| = lam * |(r : ℝ) - r'| := by
    rw [← mul_sub, abs_mul, abs_of_pos hlam, Nat.cast_sub hr, Nat.cast_sub hr']
    congr 1
    rw [show (L : ℝ) - r - (L - r') = -((r : ℝ) - r') by ring, abs_neg]
  rw [e1] at h1
  rw [e2] at h2
  calc |τ ^ r + τ ^ (L - r) - (τ ^ r' + τ ^ (L - r'))|
      = |(τ ^ r - τ ^ r') + (τ ^ (L - r) - τ ^ (L - r'))| := by ring_nf
    _ ≤ |τ ^ r - τ ^ r'| + |τ ^ (L - r) - τ ^ (L - r')| := abs_add_le _ _
    _ ≤ lam * |(r : ℝ) - r'| * (τ ^ r + τ ^ r') +
          lam * |(r : ℝ) - r'| * (τ ^ (L - r) + τ ^ (L - r')) := add_le_add h1 h2
    _ = _ := by ring

/-- `‖x + y‖² = ‖x‖² + ‖y‖² + e` with `|e| ≤ 2‖x‖‖y‖`. -/
private lemma bd_norm_add_sq (x y : ℂ) :
    |‖x + y‖ ^ 2 - (‖x‖ ^ 2 + ‖y‖ ^ 2)| ≤ 2 * (‖x‖ * ‖y‖) := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
  have h := Complex.abs_re_le_norm (x * (starRingEnd ℂ) y)
  rw [norm_mul, Complex.norm_conj] at h
  rw [show Complex.normSq x + Complex.normSq y + 2 * (x * (starRingEnd ℂ) y).re -
    (Complex.normSq x + Complex.normSq y) = 2 * (x * (starRingEnd ℂ) y).re by ring, abs_mul,
    abs_two]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- `|‖G_ρ(r)‖² - G_{|ρ|²}(r)| ≤ 10 |ρ|^L/(1-q₀)³`. -/
private lemma bd_G_diff {ρ : ℂ} {q₀ : ℝ} (hρq : ‖ρ‖ ≤ q₀) (hq₀ : q₀ < 1) {L : ℕ} (hL : 1 ≤ L)
    (r : ℕ) (hr : r ≤ L) :
    |‖bgV ρ L r‖ ^ 2 - bgV (‖ρ‖ ^ 2) L r| ≤ 10 * ‖ρ‖ ^ L / (1 - q₀) ^ 3 := by
  set q := ‖ρ‖ with hqdef
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq1 : q < 1 := lt_of_le_of_lt hρq hq₀
  have hqL : q ^ L ≤ q₀ := (pow_le_of_le_one hq0 hq1.le (by omega)).trans hρq
  have hqL0 : 0 ≤ q ^ L := pow_nonneg hq0 L
  have h1q : 0 < 1 - q₀ := by linarith
  set N := ‖ρ ^ r + ρ ^ (L - r)‖ ^ 2 with hN
  set N₀ := (q ^ 2) ^ r + (q ^ 2) ^ (L - r) with hN₀
  set D := ‖1 - ρ ^ L‖ ^ 2 with hD
  set D₀ := 1 - (q ^ 2) ^ L with hD₀
  have hNN : |N - N₀| ≤ 2 * q ^ L := by
    have h := bd_norm_add_sq (ρ ^ r) (ρ ^ (L - r))
    rw [norm_pow, norm_pow] at h
    have e1 : (q ^ r) ^ 2 + (q ^ (L - r)) ^ 2 = N₀ := by rw [hN₀, ← pow_mul, ← pow_mul]; ring_nf
    have e2 : q ^ r * q ^ (L - r) = q ^ L := by rw [← pow_add]; congr 1; omega
    rw [e1, e2] at h
    exact h
  have hDD : |D - D₀| ≤ 4 * q ^ L := by
    have h := bd_norm_add_sq (1 : ℂ) (-(ρ ^ L))
    rw [norm_one, norm_neg, norm_pow, ← sub_eq_add_neg] at h
    have h2 : (q ^ L) ^ 2 ≤ q ^ L := by nlinarith
    have e : D - D₀ = (‖1 - ρ ^ L‖ ^ 2 - (1 ^ 2 + (q ^ L) ^ 2)) + 2 * (q ^ L) ^ 2 := by
      rw [hD, hD₀, ← pow_mul, ← pow_mul]; ring_nf
    rw [e]
    calc |(‖1 - ρ ^ L‖ ^ 2 - (1 ^ 2 + (q ^ L) ^ 2)) + 2 * (q ^ L) ^ 2|
        ≤ |‖1 - ρ ^ L‖ ^ 2 - (1 ^ 2 + (q ^ L) ^ 2)| + |2 * (q ^ L) ^ 2| := abs_add_le _ _
      _ ≤ 2 * (1 * q ^ L) + 2 * q ^ L := by
          gcongr
          rw [abs_of_nonneg (by positivity)]; linarith
      _ = 4 * q ^ L := by ring
  have hDlow : (1 - q₀) ^ 2 ≤ D := by
    have h := norm_sub_norm_le (1 : ℂ) (ρ ^ L)
    rw [norm_one, norm_pow] at h
    have : 1 - q₀ ≤ ‖1 - ρ ^ L‖ := by linarith
    exact pow_le_pow_left₀ h1q.le this 2
  have hD₀low : 1 - q₀ ≤ D₀ := by
    rw [hD₀, ← pow_mul]
    have : q ^ (2 * L) ≤ q₀ := (pow_le_of_le_one hq0 hq1.le (by omega)).trans hρq
    linarith
  have hD₀le : D₀ ≤ 1 := by rw [hD₀]; linarith [pow_nonneg (sq_nonneg q) L]
  have hN₀le : N₀ ≤ 2 := by
    have h1 : (q ^ 2) ^ r ≤ 1 := pow_le_one₀ (sq_nonneg _) (by nlinarith)
    have h2 : (q ^ 2) ^ (L - r) ≤ 1 := pow_le_one₀ (sq_nonneg _) (by nlinarith)
    linarith
  have hN₀0 : 0 ≤ N₀ := by positivity
  have hGv : ‖bgV ρ L r‖ ^ 2 = N / D := by rw [bgV, norm_div, div_pow]
  have hG₀v : bgV (q ^ 2) L r = N₀ / D₀ := rfl
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hDlow
  have hD₀pos : 0 < D₀ := lt_of_lt_of_le h1q hD₀low
  rw [hGv, hG₀v, div_sub_div _ _ hDpos.ne' hD₀pos.ne', abs_div, abs_of_pos (mul_pos hDpos hD₀pos)]
  rw [div_le_div_iff₀ (mul_pos hDpos hD₀pos) (by positivity)]
  have hnum : |N * D₀ - D * N₀| ≤ 10 * q ^ L := by
    have e : N * D₀ - D * N₀ = (N - N₀) * D₀ + N₀ * (D₀ - D) := by ring
    rw [e]
    calc |(N - N₀) * D₀ + N₀ * (D₀ - D)| ≤ |N - N₀| * D₀ + N₀ * |D - D₀| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos hD₀pos, abs_of_nonneg hN₀0, abs_sub_comm D₀ D]
      _ ≤ 2 * q ^ L * 1 + 2 * (4 * q ^ L) := by gcongr
      _ = 10 * q ^ L := by ring
  have hden : (1 - q₀) ^ 3 ≤ D * D₀ := by
    calc (1 - q₀) ^ 3 = (1 - q₀) ^ 2 * (1 - q₀) := by ring
      _ ≤ D * D₀ := mul_le_mul hDlow hD₀low h1q.le hDpos.le
  calc |N * D₀ - D * N₀| * (1 - q₀) ^ 3 ≤ 10 * q ^ L * (D * D₀) :=
        mul_le_mul hnum hden (by positivity) (by positivity)
    _ = _ := by ring

private lemma bd_bgV_zero_ge {ρ : ℂ} {q₀ : ℝ} (hρq : ‖ρ‖ ≤ q₀) (hq₀ : q₀ < 1) {L : ℕ}
    (hL : 1 ≤ L) : (1 - q₀) / 2 ≤ ‖bgV ρ L 0‖ := by
  have hρ1 : ‖ρ‖ < 1 := lt_of_le_of_lt hρq hq₀
  unfold bgV
  rw [pow_zero, Nat.sub_zero, norm_div]
  have hρL : ‖ρ‖ ^ L ≤ q₀ := (pow_le_of_le_one (norm_nonneg _) hρ1.le (by omega)).trans hρq
  have h1 : 1 - q₀ ≤ ‖1 + ρ ^ L‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(ρ ^ L))
    rw [norm_one, norm_neg, norm_pow, sub_neg_eq_add] at this; linarith
  have h2 : ‖1 - ρ ^ L‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_pow]; linarith [pow_le_one₀ (norm_nonneg ρ) hρ1.le (n := L)]
  have h3 : 0 < ‖1 - ρ ^ L‖ := by
    have := norm_sub_norm_le (1 : ℂ) (ρ ^ L)
    rw [norm_one, norm_pow] at this
    linarith [pow_lt_one₀ (norm_nonneg ρ) hρ1 (show L ≠ 0 by omega)]
  rw [le_div_iff₀ h3]
  nlinarith

/-- The pair kernel is `C(1+L)q₀^L`-close to the stochastic geometric kernel `φ₀ G_{|ρ|²}`, in sup
and in row norm. -/
private lemma bd_P_P0 {L : ℕ} [NeZero L] (hL : 3 ≤ L) {ρ T : ℂ} {γ q₀ : ℝ} (hγ : 0 < γ)
    (hρq : ‖ρ‖ ≤ q₀) (hq₀ : q₀ < 1)
    (hrow : ∀ a : Fin L, ∑ c, γ * ‖T * bgV ρ L (cycDist a c)‖ ^ 2 = 1) :
    let σ := ‖ρ‖ ^ 2
    let P₀ := ((1 - σ) / (1 + σ)) • bgC σ L
    (∀ a c, |γ * ‖T * bgV ρ L (cycDist a c)‖ ^ 2 - P₀ a c| ≤
        80 / (1 - q₀) ^ 6 * (1 + L) * q₀ ^ L) ∧
      ∀ a, ∑ c, |γ * ‖T * bgV ρ L (cycDist a c)‖ ^ 2 - P₀ a c| ≤
        80 / (1 - q₀) ^ 6 * (1 + L) * q₀ ^ L := by
  intro σ P₀
  have hL1 : 1 ≤ L := by omega
  set q := ‖ρ‖ with hqdef
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq1 : q < 1 := lt_of_le_of_lt hρq hq₀
  have h1q : 0 < 1 - q₀ := by linarith
  have hσ0 : 0 ≤ σ := sq_nonneg q
  have hσ1 : σ < 1 := by change q ^ 2 < 1; nlinarith
  have hqLq : q ^ L ≤ q₀ ^ L := pow_le_pow_left₀ hq0 hρq L
  set e₁ := 10 * q ^ L / (1 - q₀) ^ 3 with he₁
  have he₁0 : 0 ≤ e₁ := by positivity
  have hLr : (L : ℝ) ≥ 1 := by exact_mod_cast hL1
  -- the profile pieces
  have hP₀ : ∀ a c, P₀ a c = (1 - σ) / (1 + σ) * bgV σ L (cycDist a c) := by
    intro a c; simp [P₀, bgC, bgV_cycDist]
  have hG0le : ∀ r, r ≤ L → bgV σ L r ≤ 2 / (1 - q₀) := by
    intro r hr
    unfold bgV
    have hσL : σ ^ L ≤ q₀ := by
      calc σ ^ L ≤ σ := pow_le_of_le_one hσ0 hσ1.le (by omega)
        _ ≤ q := by change q ^ 2 ≤ q; nlinarith
        _ ≤ q₀ := hρq
    rw [div_le_div_iff₀ (by linarith) h1q]
    have : σ ^ r ≤ 1 := pow_le_one₀ hσ0 hσ1.le
    have : σ ^ (L - r) ≤ 1 := pow_le_one₀ hσ0 hσ1.le
    nlinarith
  have hG0nn : ∀ r, 0 ≤ bgV σ L r := by
    intro r; unfold bgV
    have : σ ^ L < 1 := pow_lt_one₀ hσ0 hσ1 (by omega)
    exact div_nonneg (by positivity) (by linarith)
  have hS₀ : ∀ a : Fin L, ∑ c, bgV σ L (cycDist a c) = (1 + σ) / (1 - σ) := by
    intro a
    have := bg_row_sum hσ0 hσ1 hL1 a
    simp only [bgC, Matrix.of_apply, bgV_cycDist] at this
    exact this
  have hφS : (1 - σ) / (1 + σ) * ((1 + σ) / (1 - σ)) = 1 := by
    field_simp
  have hφ1 : (1 - σ) / (1 + σ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hφ0 : 0 ≤ (1 - σ) / (1 + σ) := div_nonneg (by linarith) (by linarith)
  have hT0 : 0 ≤ γ * ‖T‖ ^ 2 := mul_nonneg hγ.le (sq_nonneg _)
  -- the per-row data
  have key : ∀ a : Fin L, ∀ c,
      |γ * ‖T * bgV ρ L (cycDist a c)‖ ^ 2 - P₀ a c| ≤
        γ * ‖T‖ ^ 2 * |‖bgV ρ L (cycDist a c)‖ ^ 2 - bgV σ L (cycDist a c)| +
          γ * ‖T‖ ^ 2 * ((1 - σ) / (1 + σ)) * (L * e₁) * bgV σ L (cycDist a c) := by
    intro a c
    have hrowa : γ * ‖T‖ ^ 2 * ∑ c, ‖bgV ρ L (cycDist a c)‖ ^ 2 = 1 := by
      rw [← hrow a, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [norm_mul]; ring
    have hdiff : ∀ c, |‖bgV ρ L (cycDist a c)‖ ^ 2 - bgV σ L (cycDist a c)| ≤ e₁ := fun c =>
      bd_G_diff hρq hq₀ hL1 _ (by have := bd_cycDist_half a c; omega)
    have hSS : |∑ c, ‖bgV ρ L (cycDist a c)‖ ^ 2 - (1 + σ) / (1 - σ)| ≤ L * e₁ := by
      rw [← hS₀ a, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ c, |‖bgV ρ L (cycDist a c)‖ ^ 2 - bgV σ L (cycDist a c)| ≤ ∑ _c : Fin L, e₁ :=
            Finset.sum_le_sum fun c _ => hdiff c
        _ = L * e₁ := by simp
    have hTφ : |γ * ‖T‖ ^ 2 - (1 - σ) / (1 + σ)| ≤ γ * ‖T‖ ^ 2 * ((1 - σ) / (1 + σ)) * (L * e₁) :=
        by
      have e : γ * ‖T‖ ^ 2 - (1 - σ) / (1 + σ) = γ * ‖T‖ ^ 2 * ((1 - σ) / (1 + σ)) *
          ((1 + σ) / (1 - σ) - ∑ c, ‖bgV ρ L (cycDist a c)‖ ^ 2) := by
        have : γ * ‖T‖ ^ 2 * ((1 - σ) / (1 + σ)) * ((1 + σ) / (1 - σ)) = γ * ‖T‖ ^ 2 := by
          rw [mul_assoc, hφS, mul_one]
        linear_combination (-1 : ℝ) * this + ((1 - σ) / (1 + σ)) * hrowa
      rw [e, abs_mul, abs_mul (γ * ‖T‖ ^ 2), abs_of_nonneg hT0, abs_of_nonneg hφ0, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left hSS (mul_nonneg hT0 hφ0)
    have e2 : γ * ‖T * bgV ρ L (cycDist a c)‖ ^ 2 - P₀ a c =
        γ * ‖T‖ ^ 2 * (‖bgV ρ L (cycDist a c)‖ ^ 2 - bgV σ L (cycDist a c)) +
          (γ * ‖T‖ ^ 2 - (1 - σ) / (1 + σ)) * bgV σ L (cycDist a c) := by
      rw [hP₀, norm_mul]; ring
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul (γ * ‖T‖ ^ 2), abs_of_nonneg hT0, abs_mul _ (bgV σ L (cycDist a c)),
      abs_of_nonneg (hG0nn _)]
    have hGn := hG0nn (cycDist a c)
    gcongr
  -- the bound on `γ|f|²`
  have hT2le : γ * ‖T‖ ^ 2 ≤ 4 / (1 - q₀) ^ 2 := by
    have : NeZero L := inferInstance
    have hrowa := hrow 0
    have h1 : γ * ‖T * bgV ρ L (cycDist (0 : Fin L) 0)‖ ^ 2 ≤ 1 := by
      rw [← hrowa]
      exact Finset.single_le_sum (f := fun c => γ * ‖T * bgV ρ L (cycDist (0 : Fin L) c)‖ ^ 2)
        (fun c _ => by positivity) (Finset.mem_univ 0)
    rw [bd_cycDist_self, norm_mul, mul_pow] at h1
    have h2 := bd_bgV_zero_ge hρq hq₀ hL1
    have h3 : ((1 - q₀) / 2) ^ 2 ≤ ‖bgV ρ L 0‖ ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
    have h4 : γ * ‖T‖ ^ 2 * ((1 - q₀) / 2) ^ 2 ≤ 1 := by
      calc γ * ‖T‖ ^ 2 * ((1 - q₀) / 2) ^ 2 ≤ γ * ‖T‖ ^ 2 * ‖bgV ρ L 0‖ ^ 2 :=
            mul_le_mul_of_nonneg_left h3 hT0
        _ ≤ 1 := by linarith
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hfin1 : 4 / (1 - q₀) ^ 2 * e₁ * (1 + 2 * L / (1 - q₀)) ≤
      80 / (1 - q₀) ^ 6 * (1 + L) * q₀ ^ L := by
    rw [he₁]
    have h1 : 10 * q ^ L ≤ 10 * q₀ ^ L := by linarith
    have h2 : (1 - q₀) ≤ 1 := by linarith [hq0.trans hρq]
    have h3 : 0 < (1 - q₀) ^ 6 := by positivity
    rw [show 4 / (1 - q₀) ^ 2 * (10 * q ^ L / (1 - q₀) ^ 3) * (1 + 2 * L / (1 - q₀)) =
      40 * q ^ L * ((1 - q₀) + 2 * L) / (1 - q₀) ^ 6 by field_simp; ring]
    rw [show 80 / (1 - q₀) ^ 6 * (1 + L) * q₀ ^ L = 80 * q₀ ^ L * (1 + L) / (1 - q₀) ^ 6 by ring]
    apply div_le_div_of_nonneg_right _ h3.le
    have : 0 ≤ q ^ L := pow_nonneg hq0 L
    nlinarith
  constructor
  · intro a c
    refine (key a c).trans ?_
    have hT := hT2le
    have hG := hG0le (cycDist a c) (by have := bd_cycDist_half a c; omega)
    have hdc := bd_G_diff hρq hq₀ hL1 (cycDist a c) (by have := bd_cycDist_half a c; omega)
    have hGn := hG0nn (cycDist a c)
    refine le_trans ?_ hfin1
    calc γ * ‖T‖ ^ 2 * |‖bgV ρ L (cycDist a c)‖ ^ 2 - bgV σ L (cycDist a c)| +
          γ * ‖T‖ ^ 2 * ((1 - σ) / (1 + σ)) * (L * e₁) * bgV σ L (cycDist a c)
        ≤ 4 / (1 - q₀) ^ 2 * e₁ + 4 / (1 - q₀) ^ 2 * 1 * (L * e₁) * (2 / (1 - q₀)) := by
          gcongr
      _ = 4 / (1 - q₀) ^ 2 * e₁ * (1 + 2 * L / (1 - q₀)) := by ring
  · intro a
    have hsum : ∑ c, |γ * ‖T * bgV ρ L (cycDist a c)‖ ^ 2 - P₀ a c| ≤
        2 * (γ * ‖T‖ ^ 2) * (L * e₁) := by
      refine (Finset.sum_le_sum fun c _ => key a c).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hS₀ a,
        mul_assoc (γ * ‖T‖ ^ 2 * ((1 - σ) / (1 + σ))), mul_comm (L * e₁), ← mul_assoc,
        mul_assoc (γ * ‖T‖ ^ 2), hφS, mul_one]
      have h1 : ∑ c, |‖bgV ρ L (cycDist a c)‖ ^ 2 - bgV σ L (cycDist a c)| ≤ L * e₁ := by
        calc ∑ c, |‖bgV ρ L (cycDist a c)‖ ^ 2 - bgV σ L (cycDist a c)| ≤ ∑ _c : Fin L, e₁ :=
              Finset.sum_le_sum fun c _ =>
                bd_G_diff hρq hq₀ hL1 _ (by have := bd_cycDist_half a c; omega)
          _ = L * e₁ := by simp
      nlinarith
    refine hsum.trans ?_
    rw [he₁]
    have h1 : 10 * q ^ L ≤ 10 * q₀ ^ L := by linarith
    have h3 : 0 < (1 - q₀) ^ 6 := by positivity
    have h2 : (1 - q₀) ≤ 1 := by linarith [hq0.trans hρq]
    calc 2 * (γ * ‖T‖ ^ 2) * (L * (10 * q ^ L / (1 - q₀) ^ 3))
        ≤ 2 * (4 / (1 - q₀) ^ 2) * (L * (10 * q₀ ^ L / (1 - q₀) ^ 3)) := by gcongr
      _ = 80 * L * q₀ ^ L * (1 - q₀) / (1 - q₀) ^ 6 := by field_simp; ring
      _ ≤ 80 * (1 + L) * q₀ ^ L / (1 - q₀) ^ 6 := by
          apply div_le_div_of_nonneg_right _ h3.le
          have h0 : 0 ≤ q₀ ^ L := pow_nonneg (hq0.trans hρq) L
          have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 80 * L * q₀ ^ L)
          nlinarith
      _ = 80 / (1 - q₀) ^ 6 * (1 + L) * q₀ ^ L := by ring

end BdCompare

/-! ### The gradient of the mixed kernel -/

section BdGrad

/-- `λ ℓ ≤ 2 Cm² (B₀ + 2)` in the diffusive regime. -/
private lemma bd_lam_ell {Cm B₀ g γ δ σ ℓ : ℝ} (hCm : 1 ≤ Cm) (hB₀ : 0 < B₀) (hg : 0 < g)
    (hγ : 0 < γ) (hγC : 1 ≤ γ * Cm ^ 2) (hδ : 0 < δ) (hσ : (g / (Cm * (B₀ + 2))) ^ 2 ≤ σ)
    (hσ1 : σ < 1) (hX : 1 ≤ g / Real.sqrt (γ * δ)) (hℓ : ℓ ≤ 1 + g / Real.sqrt (γ * δ))
    (hℓ0 : 0 ≤ ℓ) :
    lamGeo (σ / (1 - σ) ^ 2) δ * ℓ ≤ 2 * Cm ^ 2 * (B₀ + 2) := by
  have hσ0 : 0 < σ := lt_of_lt_of_le (by positivity) hσ
  have h1σ : 0 < 1 - σ := by linarith
  set D := σ / (1 - σ) ^ 2 with hD
  have hD0 : 0 < D := by positivity
  have hDσ : σ ≤ D := by
    rw [hD, le_div_iff₀ (by positivity)]
    have : (1 - σ) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hlam := bd_lamGeo_le hD0 hδ
  have hlam0 := (bd_lamGeo_pos hD0 hδ).le
  have hsδ := Real.sqrt_pos.mpr hδ
  have hsγ := Real.sqrt_pos.mpr hγ
  have hB2 : 0 < B₀ + 2 := by linarith
  -- `λ ≤ √δ Cm (B₀+2)/g`
  have h1 : Real.sqrt (δ / D) ≤ Real.sqrt δ * (Cm * (B₀ + 2)) / g := by
    rw [Real.sqrt_div' δ hD0.le, div_le_iff₀ (Real.sqrt_pos.mpr hD0)]
    have h2 : g / (Cm * (B₀ + 2)) ≤ Real.sqrt D := by
      rw [Real.le_sqrt (by positivity) hD0.le]; linarith
    rw [div_le_iff₀ (by positivity)] at h2
    calc Real.sqrt δ = Real.sqrt δ * (Cm * (B₀ + 2)) / g * (g / (Cm * (B₀ + 2))) := by
          field_simp
      _ ≤ Real.sqrt δ * (Cm * (B₀ + 2)) / g * Real.sqrt D := by
          apply mul_le_mul_of_nonneg_left (by rw [div_le_iff₀ (by positivity)]; linarith)
          positivity
  -- `ℓ ≤ 2 Cm g/√δ`
  have h3 : ℓ ≤ 2 * Cm * g / Real.sqrt δ := by
    have hX2 : ℓ ≤ 2 * (g / Real.sqrt (γ * δ)) := by linarith
    have hγs : 1 ≤ Real.sqrt γ * Cm := by
      have : Real.sqrt (γ * Cm ^ 2) = Real.sqrt γ * Cm := by
        rw [Real.sqrt_mul hγ.le, Real.sqrt_sq (by linarith)]
      rw [← this]; exact Real.one_le_sqrt.mpr hγC
    refine hX2.trans ?_
    have hinv : 1 / Real.sqrt γ ≤ Cm := by rw [div_le_iff₀ hsγ]; linarith
    rw [Real.sqrt_mul hγ.le]
    calc 2 * (g / (Real.sqrt γ * Real.sqrt δ)) = 2 * (g / Real.sqrt δ) * (1 / Real.sqrt γ) := by
          field_simp
      _ ≤ 2 * (g / Real.sqrt δ) * Cm := by gcongr
      _ = 2 * Cm * g / Real.sqrt δ := by ring
  calc lamGeo D δ * ℓ ≤ (Real.sqrt δ * (Cm * (B₀ + 2)) / g) * (2 * Cm * g / Real.sqrt δ) :=
        mul_le_mul (hlam.trans h1) h3 hℓ0 (by positivity)
    _ = 2 * Cm ^ 2 * (B₀ + 2) := by field_simp

/-- Combination of the trivial and the Lipschitz bounds. -/
private lemma bd_grad_comb {x K K' A A' lamd R Cl d ℓ : ℝ} (hx1 : x ≤ K + K')
    (hx2 : x ≤ lamd * (K + K') + R) (hR : 0 ≤ R) (hlamd : lamd ≤ Cl * (d / ℓ))
    (hK : K ≤ A) (hK' : K' ≤ A') (hK0 : 0 ≤ K) (hK0' : 0 ≤ K') (hd : 0 ≤ d) (hℓ : 0 < ℓ) :
    x ≤ max Cl 1 * min (d / ℓ) 1 * (A + A') + R := by
  have hA : 0 ≤ A + A' := by linarith
  have hm1 : 1 ≤ max Cl 1 := le_max_right _ _
  rcases le_total (d / ℓ) 1 with h | h
  · rw [min_eq_left h]
    rcases le_total lamd 1 with h' | h'
    · calc x ≤ lamd * (K + K') + R := hx2
        _ ≤ (max Cl 1 * (d / ℓ)) * (A + A') + R := by
            have h1 : lamd ≤ max Cl 1 * (d / ℓ) :=
              hlamd.trans (by gcongr; exact le_max_left _ _)
            have h2 : K + K' ≤ A + A' := by linarith
            gcongr
    · -- `λd ≥ 1`, so `C_λ d/ℓ ≥ 1`
      have : 1 ≤ max Cl 1 * (d / ℓ) :=
        h'.trans (hlamd.trans (by gcongr; exact le_max_left _ _))
      nlinarith
  · rw [min_eq_right h, mul_one]
    nlinarith

/-- The gradient constant. -/
private def bdG₀ (C B₀ c' : ℝ) : ℝ :=
  max (2 + 2 * C * bdCm C) (max (2 * bdCm C ^ 2 * (B₀ + 2)) 1) *
    (10 * (2 + 2 * bdCm C) / bdc4 C (bdp₀ C c') (bdc₁ C B₀ c'))

/-- The comparison error `80(1-q₀)⁻⁶ (1+L) q₀^L`. -/
private def bdε (C c' : ℝ) (L : ℕ) : ℝ := 80 / (1 - bdq C c') ^ 6 * (1 + L) * bdq C c' ^ L

private lemma bdε_nonneg (C : ℝ) {c' : ℝ} (hc' : 0 < c') (L : ℕ) : 0 ≤ bdε C c' L := by
  have hq := bdq_facts C hc'
  have h1 : 0 < 1 - bdq C c' := by linarith [hq.2]
  unfold bdε
  exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) (pow_pos h1 6).le) (by positivity))
    (pow_nonneg hq.1.le L)

/-- In the diffusive regime `ℓ_t > 2 + 2C max{1,C}`: `g > 0`, `1 - t < 1/2` and `g/√(γδ) ≥ 1`. -/
private lemma bd_regime {C g γ t : ℝ} {L : ℕ} (hC : 0 < C) (hg : 0 ≤ g) (hgC : g ≤ C) (hγ : 0 < γ)
    (hγC : 1 ≤ γ * bdCm C ^ 2) (ht1 : t < 1)
    (hℓ : 2 + 2 * C * bdCm C < min (L : ℝ) (1 + g / Real.sqrt (γ * (1 - t)))) :
    0 < g ∧ 1 - t < 1 / 2 ∧ 1 ≤ g / Real.sqrt (γ * (1 - t)) := by
  have hδ : 0 < 1 - t := by linarith
  have hCm := bdCm_ge C
  have hX : 1 + 2 * C * bdCm C < g / Real.sqrt (γ * (1 - t)) := by
    have := hℓ.trans_le (min_le_right _ _); linarith
  have hCC : 0 ≤ C * bdCm C := by have := hCm.1; positivity
  refine ⟨?_, ?_, by linarith⟩
  · rcases hg.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, zero_div] at hX; linarith
  · by_contra hcon
    push Not at hcon
    -- `1 - t ≥ 1/2` gives `g/√(γδ) ≤ 2 C max{1,C}`
    have hs : 1 ≤ 2 * bdCm C * Real.sqrt (γ * (1 - t)) := by
      have h1 : 1 ≤ (2 * bdCm C * Real.sqrt (γ * (1 - t))) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        nlinarith
      exact le_of_pow_le_pow_left₀ two_ne_zero (by have := hCm.1; positivity)
        (by rw [one_pow]; exact h1)
    have hsq : 0 < Real.sqrt (γ * (1 - t)) := Real.sqrt_pos.mpr (by positivity)
    have : g / Real.sqrt (γ * (1 - t)) ≤ 2 * C * bdCm C := by
      rw [div_le_iff₀ hsq]
      calc g ≤ C * 1 := by linarith
        _ ≤ C * (2 * bdCm C * Real.sqrt (γ * (1 - t))) := by gcongr
        _ = 2 * C * bdCm C * Real.sqrt (γ * (1 - t)) := by ring
    linarith

/-- The comparison step: in the diffusive regime, the increment of `K` is Lipschitz at rate `λ`,
`λℓ ≤ 2 max{1,C}² (B₀+2)`, up to `2ε/δ²`. -/
private lemma bd_grad_cmp {C B₀ c' g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ} (hC : 0 < C) (hB₀ : 0 < B₀)
    (hc' : 0 < c') (hg : 0 ≤ g) (hgC : g ≤ C) [NeZero L] (h : BdModel C B₀ c' g L E m) (t : ℝ)
    (ht1 : t < 1) (hreg : 2 + 2 * C * bdCm C < ellProp g L t) :
    ∃ lam : ℝ, 0 ≤ lam ∧ lam * ellProp g L t ≤ 2 * bdCm C ^ 2 * (B₀ + 2) ∧ ∀ c b b' : Fin L,
      |mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) t c b' -
        mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) t c b| ≤
        lam * cycDist b b' *
          (mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) t c b +
            mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) t c b') +
        (2 * lam * cycDist b b' + 2) * (2 * bdε C c' L / (1 - t) ^ 2) := by
  have hL3 := h.good.hL
  have hL1 : 1 ≤ L := by omega
  obtain ⟨hγ0, hγ1, hγC⟩ := h.gam
  obtain ⟨hg0, hδ2, hX⟩ := bd_regime hC hg hgC hγ0 hγC ht1 hreg
  have hδ : 0 < 1 - t := by linarith
  obtain ⟨-, -, -, hb0, -, -, hgb⟩ := bd_gamma hg hgC
  have hCm := bdCm_ge C
  set M := dysonMat (hopB g) (gammaG g) L E m
  set ρ := freeRho (hopB g) ((E : ℂ) + gammaG g * m)
  set T := freeT (hopB g) ((E : ℂ) + gammaG g * m)
  have hq := bdq_facts C hc'
  have hρq := h.rho_le
  have hb : 0 < hopB g := by
    have : g / bdCm C ≤ hopB g := by rw [div_le_iff₀ (by linarith [hCm.1])]; linarith
    exact lt_of_lt_of_le (by have := hCm.1; positivity) this
  have hρ0 : 0 < ‖ρ‖ := lt_of_lt_of_le (by positivity) h.rho_ge
  set σ := ‖ρ‖ ^ 2 with hσ
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ < 1 := by
    have : ‖ρ‖ < 1 := lt_of_le_of_lt hρq hq.2
    nlinarith
  have hσg : (g / (bdCm C * (B₀ + 2))) ^ 2 ≤ σ := by
    rw [hσ]
    apply pow_le_pow_left₀ (div_nonneg hg (mul_pos (by linarith [hCm.1]) (by linarith)).le)
    refine le_trans ?_ h.rho_ge
    rw [div_le_div_iff₀ (mul_pos (by linarith [hCm.1]) (by linarith)) (by linarith),
      mul_comm (bdCm C)]
    nlinarith
  set D := σ / (1 - σ) ^ 2 with hD
  set lam := lamGeo D (1 - t) with hlam
  have hD0 : 0 < D := by have : 0 < 1 - σ := by linarith
                         positivity
  have hlam0 : 0 < lam := bd_lamGeo_pos hD0 hδ
  have hlamℓ : lam * ellProp g L t ≤ 2 * bdCm C ^ 2 * (B₀ + 2) :=
    bd_lam_ell hCm.1 hB₀ hg0 hγ0 hγC hδ hσg hσ1 hX (min_le_right _ _)
      (by have := bd_ell_ge hL1 hg t; linarith)
  refine ⟨lam, hlam0.le, hlamℓ, fun c b b' => ?_⟩
  -- the comparison kernel
  set P₀ := ((1 - σ) / (1 + σ)) • bgC σ L with hP₀
  set P := pairP (gammaG g) M with hPdef
  have hPe : ∀ a c, P a c = gammaG g * ‖T * bgV ρ L (cycDist a c)‖ ^ 2 := fun a c => by
    simp only [hPdef, pairP, Matrix.of_apply, M, h.M_eq]; rfl
  have hrowP : ∀ a : Fin L, ∑ c, gammaG g * ‖T * bgV ρ L (cycDist a c)‖ ^ 2 = 1 := by
    intro a
    rw [← bdP_row_one _ h.good.sum a, ← h.P_eq]
    exact Finset.sum_congr rfl fun c _ => (hPe a c).symm
  obtain ⟨hεs, hεr⟩ := bd_P_P0 hL3 hγ0 hρq hq.2 hrowP
  have hP₀0 : ∀ x y, 0 ≤ P₀ x y := by
    intro x y
    simp only [hP₀, Matrix.smul_apply, smul_eq_mul, bgC, Matrix.of_apply, bgV]
    have : σ ^ L < 1 := pow_lt_one₀ hσ0.le hσ1 (by omega)
    exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (div_nonneg (by positivity)
      (by linarith))
  have hP₀r : ∀ x, ∑ y, P₀ x y = 1 := by
    intro x
    simp only [hP₀, Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, bg_row_sum hσ0.le hσ1 hL1 x]
    field_simp
  have hP₀s : P₀.transpose = P₀ := by
    ext x y
    simp only [hP₀, Matrix.transpose_apply, Matrix.smul_apply, bgC, Matrix.of_apply,
      bgV_cycDist, bd_cycDist_comm]
  have hP0 : ∀ x y, 0 ≤ P x y := fun x y => by rw [hPe]; positivity
  have hPr : ∀ x, ∑ y, P x y = 1 := fun x => by
    rw [Finset.sum_congr rfl fun y _ => hPe x y]; exact hrowP x
  set ε := bdε C c' L
  have hε0 : 0 ≤ ε := bdε_nonneg C hc' L
  have hpert := kernel_perturb P₀ P hP₀0 hP0 hP₀r hPr hP₀s ε 1 (1 - t) one_pos hδ (by linarith)
    (fun x => by
      rw [Finset.sum_congr rfl fun y _ => by rw [hPe x y]]; exact hεr x)
    (fun x y => by rw [div_one, hPe x y]; exact hεs x y)
  have ht' : 1 - (1 - t) = t := by ring
  rw [ht'] at hpert
  set K := mixedKer P t
  set K₀ := mixedKer P₀ t
  have hKK : ∀ x y, |K x y - K₀ x y| ≤ 2 * ε / (1 - t) ^ 2 := by
    intro x y
    have h1 := hpert.2 x y
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < t), one_mul] at h1
    have h2 : |K x y - K₀ x y| ≤ ε / (1 - t) ^ 2 / t := by
      rw [le_div_iff₀ (by linarith)]; linarith
    refine h2.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ ε / (1 - t) ^ 2 := by positivity
    have e : 2 * ε / (1 - t) ^ 2 = 2 * (ε / (1 - t) ^ 2) := by ring
    rw [e]
    nlinarith
  -- `K₀` is the explicit periodized exponential
  have hK₀e := bd_K0_eq hL3 hσ0 hσ1 hδ (by linarith) D rfl P₀ rfl
  rw [ht'] at hK₀e
  have hK₀v : ∀ x y, K₀ x y = (Real.sqrt ((1 - t) * ((1 - t) + 4 * D)))⁻¹ *
      bgV (Real.exp (-lam)) L (cycDist x y) := by
    intro x y
    change mixedKer P₀ t x y = _
    rw [hK₀e, Matrix.smul_apply, smul_eq_mul]
    simp only [bgC, Matrix.of_apply]
    rw [bgV_cycDist]
  have hS0 : 0 < Real.sqrt ((1 - t) * ((1 - t) + 4 * D)) := Real.sqrt_pos.mpr (by positivity)
  have hlip : |K₀ c b' - K₀ c b| ≤ lam * cycDist b b' * (K₀ c b + K₀ c b') := by
    rw [hK₀v, hK₀v, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hS0)]
    have h1 := bd_bgV_lip hlam0 hL1 (cycDist c b') (cycDist c b)
      (by have := bd_cycDist_half c b'; omega) (by have := bd_cycDist_half c b; omega)
    have h2 : |(cycDist c b' : ℝ) - cycDist c b| ≤ cycDist b b' := by
      rw [abs_le]
      have t1 : (cycDist c b' : ℝ) ≤ cycDist c b + cycDist b b' := by
        exact_mod_cast bd_cycDist_tri c b b'
      have t2 : (cycDist c b : ℝ) ≤ cycDist c b' + cycDist b' b := by
        exact_mod_cast bd_cycDist_tri c b' b
      rw [bd_cycDist_comm b' b] at t2
      constructor <;> linarith
    have h3 : 0 ≤ bgV (Real.exp (-lam)) L (cycDist c b') +
        bgV (Real.exp (-lam)) L (cycDist c b) := by
      have hτ1 : Real.exp (-lam) < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      have : Real.exp (-lam) ^ L < 1 := pow_lt_one₀ (Real.exp_pos _).le hτ1 (by omega)
      unfold bgV
      exact add_nonneg (div_nonneg (by positivity) (by linarith))
        (div_nonneg (by positivity) (by linarith))
    calc (Real.sqrt ((1 - t) * ((1 - t) + 4 * D)))⁻¹ *
          |bgV (Real.exp (-lam)) L (cycDist c b') - bgV (Real.exp (-lam)) L (cycDist c b)|
        ≤ (Real.sqrt ((1 - t) * ((1 - t) + 4 * D)))⁻¹ * (lam * cycDist b b' *
            (bgV (Real.exp (-lam)) L (cycDist c b') + bgV (Real.exp (-lam)) L (cycDist c b))) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hS0.le)
          refine h1.trans ?_
          gcongr
      _ = _ := by ring
  set E₁ := 2 * ε / (1 - t) ^ 2
  have hE₁ : 0 ≤ E₁ := by positivity
  have hb1 := hKK c b
  have hb2 := hKK c b'
  have hd0 : (0 : ℝ) ≤ cycDist b b' := Nat.cast_nonneg _
  have hld : 0 ≤ lam * cycDist b b' := by positivity
  have hK0b : K₀ c b ≤ K c b + E₁ := by rw [abs_le] at hb1; linarith [hb1.1]
  have hK0b' : K₀ c b' ≤ K c b' + E₁ := by rw [abs_le] at hb2; linarith [hb2.1]
  calc |K c b' - K c b| ≤ |K₀ c b' - K₀ c b| + |K c b' - K₀ c b'| + |K c b - K₀ c b| := by
        rw [abs_le]; rw [abs_le] at hb1 hb2
        have := abs_le.mp (le_refl |K₀ c b' - K₀ c b|)
        constructor <;> linarith [abs_nonneg (K₀ c b' - K₀ c b), le_abs_self (K₀ c b' - K₀ c b),
          neg_abs_le (K₀ c b' - K₀ c b), abs_nonneg (K c b' - K₀ c b'),
          abs_nonneg (K c b - K₀ c b), le_abs_self (K c b' - K₀ c b'),
          neg_abs_le (K c b' - K₀ c b'), le_abs_self (K c b - K₀ c b), neg_abs_le (K c b - K₀ c b)]
    _ ≤ lam * cycDist b b' * (K₀ c b + K₀ c b') + E₁ + E₁ := by linarith
    _ ≤ lam * cycDist b b' * ((K c b + E₁) + (K c b' + E₁)) + E₁ + E₁ := by gcongr
    _ = lam * cycDist b b' * (K c b + K c b') + (2 * lam * cycDist b b' + 2) * E₁ := by ring

/-- The real-number combination behind (A.29) [gc:eq:gradient]: the trivial bound, the short-scale
case, and the comparison case. -/
private lemma bd_grad_final {x K K' e e' d ℓ δ CK Cl ℓ₁ G₀ R : ℝ} (hx1 : x ≤ K + K')
    (hK : K ≤ CK / (δ * ℓ) * e) (hK' : K' ≤ CK / (δ * ℓ) * e') (hK0 : 0 ≤ K) (hK0' : 0 ≤ K')
    (he : 0 ≤ e) (he' : 0 ≤ e') (hd0 : 0 ≤ d) (hxd : x ≤ 0 ∨ 1 ≤ d) (hℓ1 : 1 ≤ ℓ) (hδ : 0 < δ)
    (hR0 : 0 ≤ R) (hCK : 0 < CK) (hℓ₁ : 1 ≤ ℓ₁) (hG₀ : max ℓ₁ (max Cl 1) * CK ≤ G₀)
    (hcmp : ℓ₁ < ℓ → ∃ lam : ℝ, lam * d ≤ Cl * (d / ℓ) ∧ x ≤ lam * d * (K + K') + R) :
    x ≤ G₀ / (δ * ℓ) * min (d / ℓ) 1 * (e + e') + R := by
  have hℓ0 : 0 < ℓ := by linarith
  have hmin0 : 0 ≤ min (d / ℓ) 1 := le_min (by positivity) zero_le_one
  have hm : 0 ≤ max ℓ₁ (max Cl 1) :=
    le_trans zero_le_one ((le_max_right _ _).trans (le_max_right _ _))
  have hG0 : 0 ≤ G₀ := le_trans (mul_nonneg hm hCK.le) hG₀
  have hRHS0 : 0 ≤ G₀ / (δ * ℓ) * min (d / ℓ) 1 * (e + e') := by positivity
  have hfin : ∀ M₀ : ℝ, 0 ≤ M₀ → M₀ * CK ≤ G₀ →
      M₀ * min (d / ℓ) 1 * (CK / (δ * ℓ) * e + CK / (δ * ℓ) * e') ≤
        G₀ / (δ * ℓ) * min (d / ℓ) 1 * (e + e') := by
    intro M₀ hM₀ h
    have e1 : M₀ * min (d / ℓ) 1 * (CK / (δ * ℓ) * e + CK / (δ * ℓ) * e') =
        M₀ * CK / (δ * ℓ) * min (d / ℓ) 1 * (e + e') := by ring
    rw [e1]
    gcongr
  rcases hxd with hx0 | hd1
  · linarith
  by_cases hs : ℓ ≤ ℓ₁
  · have hmin : 1 / ℓ₁ ≤ min (d / ℓ) 1 := by
      apply le_min
      · rw [div_le_div_iff₀ (by linarith) hℓ0]; nlinarith
      · rw [div_le_one (by linarith)]; exact hℓ₁
    have h2 : 1 ≤ ℓ₁ * min (d / ℓ) 1 := by
      have := mul_le_mul_of_nonneg_left hmin (by linarith : (0 : ℝ) ≤ ℓ₁)
      rwa [mul_one_div_cancel (by linarith)] at this
    have h3 := hfin ℓ₁ (by linarith) ((mul_le_mul_of_nonneg_right (le_max_left _ _) hCK.le).trans
      hG₀)
    have hA : 0 ≤ CK / (δ * ℓ) * e + CK / (δ * ℓ) * e' := by positivity
    nlinarith
  · push Not at hs
    obtain ⟨lam, hlamd, hx2⟩ := hcmp hs
    have hc := bd_grad_comb hx1 hx2 hR0 hlamd hK hK' hK0 hK0' hd0 hℓ0
    have h3 := hfin (max Cl 1) (le_trans zero_le_one (le_max_right _ _))
      ((mul_le_mul_of_nonneg_right ((le_max_right _ _)) hCK.le).trans hG₀)
    linarith

variable {C B₀ c' g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ}

/-- (A.29) [gc:eq:gradient] for `j = 0`: the increment of `K_t(c, ·)` is controlled by the profile
at scale `ℓ_t`, up to the comparison error. -/
private lemma bd_grad0 (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') (hg : 0 ≤ g) (hgC : g ≤ C)
    [NeZero L] (h : BdModel C B₀ c' g L E m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (c b b' : Fin L) :
    |mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) t c b' -
        mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) t c b| ≤
      bdG₀ C B₀ c' / ((1 - t) * ellProp g L t) * min ((cycDist b b' : ℝ) / ellProp g L t) 1 *
        (Real.exp (-(bdCmu (bdμ₀ C c') (bdCP C c') / 2 * cycDist c b / ellProp g L t)) +
          Real.exp (-(bdCmu (bdμ₀ C c') (bdCP C c') / 2 * cycDist c b' / ellProp g L t))) +
      (2 * bdCm C ^ 2 * (B₀ + 2) * L + 2) * (2 * bdε C c' L / (1 - t) ^ 2) := by
  have hL1 : 1 ≤ L := by have := h.good.hL; omega
  obtain ⟨hK0, -, hprof, -, -⟩ := bd_pkg hC hg hgC h t ht0 ht1
  have hCm := bdCm_ge C
  have hp₀ := bdp₀_pos C hc'
  have hc₁ := bdc₁_pos C hB₀ hc'
  have hc4 := bdc4_pos hC hp₀ hc₁
  have hCK0 : 0 < 10 * (2 + 2 * bdCm C) / bdc4 C (bdp₀ C c') (bdc₁ C B₀ c') :=
    div_pos (by linarith [hCm.1]) hc4
  have hCl0 : 0 < 2 * bdCm C ^ 2 * (B₀ + 2) := by
    have := hCm.1; exact mul_pos (by positivity) (by linarith)
  have hδ : 0 < 1 - t := by linarith
  have hℓ1 : 1 ≤ ellProp g L t := bd_ell_ge hL1 hg t
  have hε0 := bdε_nonneg C hc' L
  have hR0 : 0 ≤ (2 * bdCm C ^ 2 * (B₀ + 2) * L + 2) * (2 * bdε C c' L / (1 - t) ^ 2) := by
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have : 0 ≤ 2 * bdCm C ^ 2 * (B₀ + 2) * L + 2 := by positivity
    positivity
  have hd0 : (0 : ℝ) ≤ cycDist b b' := Nat.cast_nonneg _
  have hxd : |mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) t c b' -
      mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) t c b| ≤ 0 ∨
      1 ≤ (cycDist b b' : ℝ) := by
    by_cases hbb : b = b'
    · left; subst hbb; simp
    · right
      have : cycDist b b' ≠ 0 := fun h0 => hbb (by
        rw [bd_cycDist_eq, bdD_eq_zero, sub_eq_zero] at h0; exact h0.symm)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  refine bd_grad_final (by rw [abs_le]; constructor <;> linarith [hK0 c b, hK0 c b'])
    (hprof c b) (hprof c b') (hK0 c b) (hK0 c b') (Real.exp_pos _).le (Real.exp_pos _).le hd0 hxd
    hℓ1 hδ hR0 hCK0 (by have := hCm.1; nlinarith) le_rfl ?_
  intro hs
  obtain ⟨lam, hlam0, hlamℓ, hcmp⟩ := bd_grad_cmp hC hB₀ hc' hg hgC h t ht1 hs
  have hℓ0 : 0 < ellProp g L t := by linarith
  refine ⟨lam, ?_, (hcmp c b b').trans ?_⟩
  · have : lam ≤ 2 * bdCm C ^ 2 * (B₀ + 2) / ellProp g L t := by
      rw [le_div_iff₀ hℓ0]; exact hlamℓ
    calc lam * cycDist b b' ≤ 2 * bdCm C ^ 2 * (B₀ + 2) / ellProp g L t * cycDist b b' := by
          gcongr
      _ = _ := by ring
  · have hdL : 2 * (cycDist b b' : ℝ) ≤ L := by exact_mod_cast bd_cycDist_half b b'
    have h1 : 2 * lam * cycDist b b' ≤ 2 * bdCm C ^ 2 * (B₀ + 2) * L := by
      have h2 : lam ≤ 2 * bdCm C ^ 2 * (B₀ + 2) := by nlinarith
      nlinarith
    have hE : 0 ≤ 2 * bdε C c' L / (1 - t) ^ 2 := by positivity
    nlinarith

end BdGrad

section BdRemainder

/-- The finite-volume remainder of (A.29) [gc:eq:gradient] is at most `W^{-A}`. -/
private lemma bd_remainder {q₀ εC Cl A BL : ℝ} (j : ℕ) (hq0 : 0 < q₀) (hq1 : q₀ < 1)
    (hεC : 0 ≤ εC) (hCl : 0 ≤ Cl) {X : ℝ} (hX : 2 ≤ X)
    (hXK : 8 * (j.factorial : ℝ) * (Cl + 2) * εC ≤ X) {L : ℕ} (hL : 1 ≤ L)
    (hLlog : (A + 3 * j + 2 * BL + 7) / Real.log (1 / q₀) * Real.log X ≤ L)
    (hLW : (L : ℝ) ≤ X ^ BL) {δ : ℝ} (hδ : X ^ (-3 : ℝ) ≤ δ) :
    (j.factorial : ℝ) * (δ ^ j)⁻¹ * ((Cl * L + 2) * (2 * (εC * (1 + L) * q₀ ^ L) / δ ^ 2)) ≤
      X ^ (-A) := by
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlq : 0 < Real.log (1 / q₀) := Real.log_pos (by rw [lt_div_iff₀ hq0]; linarith)
  have hX3 : X ^ (-3 : ℝ) = (X ^ 3)⁻¹ := by
    rw [Real.rpow_neg hX0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hδ0 : 0 < δ := lt_of_lt_of_le (by rw [hX3]; positivity) hδ
  have hinv : δ⁻¹ ≤ X ^ 3 := by
    rw [hX3] at hδ
    have := inv_anti₀ (by positivity) hδ
    rwa [inv_inv] at this
  have hp1 : (δ ^ j)⁻¹ ≤ X ^ (3 * j) := by
    rw [← inv_pow, pow_mul]; exact pow_le_pow_left₀ (by positivity) hinv j
  have hp2 : (δ ^ 2)⁻¹ ≤ X ^ 6 := by
    rw [← inv_pow, show (6 : ℕ) = 3 * 2 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hinv 2
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLL : (Cl * L + 2) * (1 + L) ≤ 4 * (Cl + 2) * (L : ℝ) ^ 2 := by
    have h1 : Cl * L + 2 ≤ (Cl + 2) * L := by nlinarith
    have h2 : 1 + (L : ℝ) ≤ 2 * L := by linarith
    calc (Cl * L + 2) * (1 + L) ≤ (Cl + 2) * L * (2 * L) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ ≤ 4 * (Cl + 2) * (L : ℝ) ^ 2 := by nlinarith
  have hL2 : (L : ℝ) ^ 2 ≤ X ^ (2 * BL) := by
    rw [show 2 * BL = BL * ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_mul hX0.le,
      Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) hLW 2
  set a := A + 3 * j + 2 * BL + 7 with ha
  have hq : q₀ ^ L ≤ X ^ (-a) := by
    have e1 : q₀ ^ L = Real.exp (-(Real.log (1 / q₀) * L)) := by
      rw [one_div, Real.log_inv, neg_mul, neg_neg, mul_comm, ← Real.exp_log hq0,
        ← Real.exp_nat_mul, Real.exp_log hq0]
    rw [e1, Real.rpow_def_of_pos hX0]
    apply Real.exp_le_exp.mpr
    have : a * Real.log X ≤ Real.log (1 / q₀) * L := by
      have h := mul_le_mul_of_nonneg_left hLlog hlq.le
      rw [← mul_assoc, mul_div_cancel₀ _ hlq.ne'] at h
      linarith
    nlinarith
  have hδp : (δ ^ j)⁻¹ * (δ ^ 2)⁻¹ ≤ X ^ ((3 * j + 6 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, pow_add]
    exact mul_le_mul hp1 hp2 (by positivity) (by positivity)
  have hLp : (Cl * L + 2) * (1 + L) ≤ 4 * (Cl + 2) * X ^ (2 * BL) :=
    hLL.trans (mul_le_mul_of_nonneg_left hL2 (by positivity))
  have hcomb : X ^ ((3 * j + 6 : ℕ) : ℝ) * X ^ (2 * BL) * X ^ (-a) = X ^ (-A - 1) := by
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
    congr 1
    rw [ha]; push_cast; ring
  have hK0 : 0 ≤ 2 * (j.factorial : ℝ) * εC := by positivity
  calc (j.factorial : ℝ) * (δ ^ j)⁻¹ * ((Cl * L + 2) * (2 * (εC * (1 + L) * q₀ ^ L) / δ ^ 2))
      = 2 * (j.factorial : ℝ) * εC * ((δ ^ j)⁻¹ * (δ ^ 2)⁻¹) * ((Cl * L + 2) * (1 + L)) *
          q₀ ^ L := by
        field_simp
    _ ≤ 2 * (j.factorial : ℝ) * εC * X ^ ((3 * j + 6 : ℕ) : ℝ) * (4 * (Cl + 2) * X ^ (2 * BL)) *
          X ^ (-a) := by
        apply mul_le_mul _ hq (by positivity) (by positivity)
        apply mul_le_mul _ hLp (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hδp hK0
    _ = 8 * (j.factorial : ℝ) * (Cl + 2) * εC *
          (X ^ ((3 * j + 6 : ℕ) : ℝ) * X ^ (2 * BL) * X ^ (-a)) := by ring
    _ = 8 * (j.factorial : ℝ) * (Cl + 2) * εC * X ^ (-A - 1) := by rw [hcomb]
    _ ≤ X * X ^ (-A - 1) := by gcongr
    _ = X ^ (-A) := by
        have : X * X ^ (-A - 1) = X ^ (1 : ℝ) * X ^ (-A - 1) := by rw [Real.rpow_one]
        rw [this, ← Real.rpow_add hX0]; congr 1; ring

end BdRemainder

section BdGradJ

/-- Weighted rows of powers: `Σ_b e^{μ d} (Xʲ)_{ab} ≤ Bʲ`. -/
private lemma bd_wpow {L : ℕ} [NeZero L] (X : Matrix (Fin L) (Fin L) ℝ) (hX : ∀ a b, 0 ≤ X a b)
    (μ B : ℝ) (hμ : 0 ≤ μ) (hrow : ∀ a, ∑ b, Real.exp (μ * cycDist a b) * X a b ≤ B) (j : ℕ) :
    (∀ a b, 0 ≤ (X ^ j) a b) ∧ ∀ a, ∑ b, Real.exp (μ * cycDist a b) * (X ^ j) a b ≤ B ^ j := by
  induction j with
  | zero =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [Matrix.one_apply, bd_cycDist_self]
  | succ j ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun c _ => mul_nonneg (h0 a c) (hX c b)
    · have hB : 0 ≤ B := le_trans (Finset.sum_nonneg fun b _ =>
        mul_nonneg (Real.exp_pos _).le (hX a b)) (hrow a)
      rw [pow_succ]
      simp only [Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      calc ∑ c, ∑ b, Real.exp (μ * cycDist a b) * ((X ^ j) a c * X c b)
          ≤ ∑ c, (X ^ j) a c * Real.exp (μ * cycDist a c) *
              ∑ b, Real.exp (μ * cycDist c b) * X c b := by
            refine Finset.sum_le_sum fun c _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun b _ => ?_
            have htri : Real.exp (μ * cycDist a b) ≤
                Real.exp (μ * cycDist a c) * Real.exp (μ * cycDist c b) := by
              rw [← Real.exp_add, ← mul_add]
              apply Real.exp_le_exp.mpr
              have : (cycDist a b : ℝ) ≤ cycDist a c + cycDist c b := by
                exact_mod_cast bd_cycDist_tri a c b
              nlinarith
            have h2 : 0 ≤ (X ^ j) a c * X c b := mul_nonneg (h0 a c) (hX c b)
            calc Real.exp (μ * cycDist a b) * ((X ^ j) a c * X c b)
                ≤ Real.exp (μ * cycDist a c) * Real.exp (μ * cycDist c b) *
                    ((X ^ j) a c * X c b) := mul_le_mul_of_nonneg_right htri h2
              _ = _ := by ring
        _ ≤ ∑ c, (X ^ j) a c * Real.exp (μ * cycDist a c) * B := by
            refine Finset.sum_le_sum fun c _ => ?_
            exact mul_le_mul_of_nonneg_left (hrow c) (mul_nonneg (h0 a c) (Real.exp_pos _).le)
        _ = (∑ c, Real.exp (μ * cycDist a c) * (X ^ j) a c) * B := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
        _ ≤ B ^ j * B := by gcongr; exact h1 a
        _ = B ^ (j + 1) := by ring

variable {C B₀ c' g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ}

/-- (A.29) [gc:eq:gradient] for `K_t^{j+1}`. -/
private lemma bd_gradj (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') (hg : 0 ≤ g) (hgC : g ≤ C)
    [NeZero L] (h : BdModel C B₀ c' g L E m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (j : ℕ)
    (a b b' : Fin L) :
    let K := mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) t
    let ℓ := ellProp g L t
    |(K ^ (j + 1)) a b' - (K ^ (j + 1)) a b| ≤
      7 ^ j * bdG₀ C B₀ c' / ((1 - t) ^ (j + 1) * ℓ) * min ((cycDist b b' : ℝ) / ℓ) 1 *
        (Real.exp (-(bdCmu (bdμ₀ C c') (bdCP C c') / 2 * cycDist a b / ℓ)) +
          Real.exp (-(bdCmu (bdμ₀ C c') (bdCP C c') / 2 * cycDist a b' / ℓ))) +
      ((1 - t) ^ j)⁻¹ * ((2 * bdCm C ^ 2 * (B₀ + 2) * L + 2) * (2 * bdε C c' L / (1 - t) ^ 2)) := by
  intro K ℓ
  have hL1 : 1 ≤ L := by have := h.good.hL; omega
  obtain ⟨hK0, hKr, -, hwt, -⟩ := bd_pkg hC hg hgC h t ht0 ht1
  set cμ := bdCmu (bdμ₀ C c') (bdCP C c') with hcμ
  have hcμ0 : 0 < cμ := bdCmu_pos (bdμ₀_facts C hc').1 (bdCP_pos C hc')
  have hδ : 0 < 1 - t := by linarith
  have hℓ1 : 1 ≤ ℓ := bd_ell_ge hL1 hg t
  have hℓ0 : 0 < ℓ := by linarith
  set G₀ := bdG₀ C B₀ c'
  set R₀ := (2 * bdCm C ^ 2 * (B₀ + 2) * L + 2) * (2 * bdε C c' L / (1 - t) ^ 2) with hR₀
  set mn := min ((cycDist b b' : ℝ) / ℓ) 1 with hmn
  -- weighted rows of `Kʲ`
  have hw : ∀ x, ∑ y, Real.exp (cμ / ℓ * cycDist x y) * K x y ≤ 7 / (1 - t) := by
    intro x
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_)) (hwt x)
    congr 2; ring
  obtain ⟨hKj0, hKjw⟩ := bd_wpow K hK0 (cμ / ℓ) (7 / (1 - t)) (by positivity) hw j
  have hw0 : ∀ x, ∑ y, Real.exp (0 * cycDist x y) * K x y ≤ (1 - t)⁻¹ := by
    intro x; simp only [zero_mul, Real.exp_zero, one_mul]; exact (hKr x).le
  obtain ⟨-, hKjr⟩ := bd_wpow K hK0 0 (1 - t)⁻¹ le_rfl hw0 j
  simp only [zero_mul, Real.exp_zero, one_mul] at hKjr
  -- the increment
  have hexp : ∀ c y : Fin L, Real.exp (-(cμ / 2 * cycDist c y / ℓ)) ≤
      Real.exp (-(cμ / 2 * cycDist a y / ℓ)) * Real.exp (cμ / ℓ * cycDist a c) := by
    intro c y
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have htri : (cycDist a y : ℝ) ≤ cycDist a c + cycDist c y := by
      exact_mod_cast bd_cycDist_tri a c y
    have hd0 : (0 : ℝ) ≤ cycDist a c := Nat.cast_nonneg _
    have h1 : cμ / 2 * cycDist a y / ℓ ≤ cμ / 2 * (cycDist a c + cycDist c y) / ℓ := by gcongr
    have h2 : cμ / 2 * ((cycDist a c : ℝ) + cycDist c y) / ℓ =
        cμ / 2 * cycDist c y / ℓ + (cμ / ℓ * cycDist a c) / 2 := by ring
    have h3 : 0 ≤ cμ / ℓ * cycDist a c := by positivity
    linarith
  have hsumexp : ∀ y : Fin L, ∑ c, (K ^ j) a c * Real.exp (-(cμ / 2 * cycDist c y / ℓ)) ≤
      Real.exp (-(cμ / 2 * cycDist a y / ℓ)) * (7 / (1 - t)) ^ j := by
    intro y
    calc ∑ c, (K ^ j) a c * Real.exp (-(cμ / 2 * cycDist c y / ℓ))
        ≤ ∑ c, (K ^ j) a c * (Real.exp (-(cμ / 2 * cycDist a y / ℓ)) *
            Real.exp (cμ / ℓ * cycDist a c)) :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hexp c y) (hKj0 a c)
      _ = Real.exp (-(cμ / 2 * cycDist a y / ℓ)) *
            ∑ c, Real.exp (cμ / ℓ * cycDist a c) * (K ^ j) a c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hKjw a) (Real.exp_pos _).le
  have hg0 := fun c => bd_grad0 hC hB₀ hc' hg hgC h t ht0 ht1 c b b'
  have hmn0 : 0 ≤ mn := le_min (by positivity) zero_le_one
  have hG₀0 : 0 ≤ G₀ / ((1 - t) * ℓ) * mn := by
    have : 0 ≤ G₀ := by
      unfold G₀ bdG₀
      have hp₀ := bdp₀_pos C hc'
      have hc4 := bdc4_pos hC hp₀ (bdc₁_pos C hB₀ hc')
      have hCm := (bdCm_ge C).1
      exact mul_nonneg (le_trans zero_le_one ((le_max_right _ _).trans (le_max_right _ _)))
        (div_pos (by linarith) hc4).le
    positivity
  have e1 : (K ^ (j + 1)) a b' - (K ^ (j + 1)) a b = ∑ c, (K ^ j) a c * (K c b' - K c b) := by
    rw [pow_succ, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [e1]
  calc |∑ c, (K ^ j) a c * (K c b' - K c b)|
      ≤ ∑ c, (K ^ j) a c * |K c b' - K c b| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
        rw [abs_mul, abs_of_nonneg (hKj0 a c)]
    _ ≤ ∑ c, (K ^ j) a c * (G₀ / ((1 - t) * ℓ) * mn *
          (Real.exp (-(cμ / 2 * cycDist c b / ℓ)) +
            Real.exp (-(cμ / 2 * cycDist c b' / ℓ))) + R₀) :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hg0 c) (hKj0 a c)
    _ = G₀ / ((1 - t) * ℓ) * mn *
          (∑ c, (K ^ j) a c * Real.exp (-(cμ / 2 * cycDist c b / ℓ)) +
            ∑ c, (K ^ j) a c * Real.exp (-(cμ / 2 * cycDist c b' / ℓ))) +
          R₀ * ∑ c, (K ^ j) a c := by
        have e2 : ∀ c, (K ^ j) a c * (G₀ / ((1 - t) * ℓ) * mn *
            (Real.exp (-(cμ / 2 * cycDist c b / ℓ)) + Real.exp (-(cμ / 2 * cycDist c b' / ℓ))) +
              R₀) = G₀ / ((1 - t) * ℓ) * mn * ((K ^ j) a c * Real.exp (-(cμ / 2 * cycDist c b / ℓ)))
              + G₀ / ((1 - t) * ℓ) * mn * ((K ^ j) a c * Real.exp (-(cμ / 2 * cycDist c b' / ℓ)))
              + R₀ * (K ^ j) a c := fun c => by ring
        rw [Finset.sum_congr rfl fun c _ => e2 c, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ ≤ G₀ / ((1 - t) * ℓ) * mn *
          (Real.exp (-(cμ / 2 * cycDist a b / ℓ)) * (7 / (1 - t)) ^ j +
            Real.exp (-(cμ / 2 * cycDist a b' / ℓ)) * (7 / (1 - t)) ^ j) +
          R₀ * ((1 - t)⁻¹) ^ j := by
        have hR0 : 0 ≤ R₀ := by
          have := bdε_nonneg C hc' L
          have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
          have : 0 ≤ 2 * bdCm C ^ 2 * (B₀ + 2) * L + 2 := by
            have := (bdCm_ge C).1; positivity
          positivity
        gcongr
        · exact hsumexp b
        · exact hsumexp b'
        · exact hKjr a
    _ = _ := by
        rw [div_pow, inv_pow]
        field_simp
        ring

end BdGradJ

/-- Lemma A.5 [ba:lem:kernels]: value at zero, exponential profile and the weighted rows (A.24)
[ba:eq:weighted-rows] at bounded coupling. -/
theorem bdd_kernels (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') :
    ∃ c C' : ℝ, ∃ L₀ : ℕ, 0 < c ∧ 0 < C' ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      ∀ t : ℝ, 0 ≤ t → t < 1 →
      let M := dysonMat (hopB g) (gammaG g) L E m
      let K := mixedKer (pairP (gammaG g) M) t
      let ℓ := ellProp g L t
      (∀ a, c / ((1 - t) * ℓ) ≤ K a a) ∧
      (∀ a b, K a b ≤ C' / ((1 - t) * ℓ) * Real.exp (-(c * cycDist a b / ℓ))) ∧
      (∀ a, ∑ b, Real.exp (c * cycDist a b) * ‖M a b‖ ≤ C') ∧
      (∀ a, ∑ b, Real.exp (c * cycDist a b / ℓ) * K a b ≤ C' / (1 - t)) ∧
      (∀ a, ∑ b, Real.exp (c * cycDist a b) *
          ‖(1 - (t : ℂ) • pairQ (gammaG g) M)⁻¹ a b‖ ≤ C') := by
  set p₀ := bdp₀ C c'
  set cμ := bdCmu (bdμ₀ C c') (bdCP C c')
  set C₂ := bdC2 (bdμ₀ C c') (bdCP C c')
  set CK := 10 * (2 + 2 * bdCm C) / bdc4 C p₀ (bdc₁ C B₀ c')
  have hp₀ := bdp₀_pos C hc'
  have hμ₀ := (bdμ₀_facts C hc').1
  have hCP := bdCP_pos C hc'
  have hcμ := bdCmu_pos hμ₀ hCP
  have hC₂ := bdC2_pos hμ₀ hCP
  have hc₁ := bdc₁_pos C hB₀ hc'
  have hc4 := bdc4_pos hC hp₀ hc₁
  have hCm := (bdCm_ge C).1
  have hCK : 0 < CK := by positivity
  have hμs : 0 < bdμs C c' := by
    have hD : 0 < 2 * bdCP C c' * bdCm C ^ 2 + 2 := by nlinarith [sq_nonneg (bdCm C)]
    exact div_pos (mul_pos hμ₀ hp₀) hD
  set cD := p₀ / (8 * π * (1 + C₂ / 2))
  have hcD : 0 < cD := by positivity
  set c := min (min cD (cμ / 2)) (min (bdμ₀ C c') (bdμs C c'))
  set C' := max (max CK 7) (max (bdCM C c') (2 / p₀))
  have hc : 0 < c := lt_min (lt_min hcD (by positivity)) (lt_min hμ₀ hμs)
  have hc1 : c ≤ cD := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ cμ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ bdμ₀ C c' := (min_le_right _ _).trans (min_le_left _ _)
  have hc4' : c ≤ bdμs C c' := (min_le_right _ _).trans (min_le_right _ _)
  have hC'1 : CK ≤ C' := (le_max_left _ _).trans (le_max_left _ _)
  have hC'2 : (7 : ℝ) ≤ C' := (le_max_right _ _).trans (le_max_left _ _)
  have hC'3 : bdCM C c' ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
  have hC'4 : 2 / p₀ ≤ C' := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨c, C', 0, hc, by linarith, ?_⟩
  intro g hg hgC L hL _ E hE m hm hcm t ht0 ht1 M K ℓ
  have : NeZero L := ⟨by omega⟩
  have h := bd_model hB₀ hc' hg hgC hL hE hm hcm
  obtain ⟨hK0, hKr, hprof, hwt, hdiag⟩ := bd_pkg hC hg hgC h t ht0 ht1
  have hℓ1 : 1 ≤ ℓ := bd_ell_ge (by omega) hg t
  have hδ : 0 < 1 - t := by linarith
  have hd0 : ∀ a b : Fin L, (0 : ℝ) ≤ cycDist a b := fun a b => Nat.cast_nonneg _
  refine ⟨fun a => ?_, fun a b => ?_, fun a => ?_, fun a => ?_, fun a => ?_⟩
  · refine le_trans ?_ (hdiag a).2.2
    gcongr
  · refine (hprof a b).trans ?_
    gcongr
  · refine le_trans ?_ (hC'3.trans' (h.Mrow a))
    refine Finset.sum_le_sum fun b _ => ?_
    gcongr
  · refine le_trans ?_ ((hwt a).trans (by gcongr))
    refine Finset.sum_le_sum fun b _ => ?_
    have := hK0 a b
    gcongr
    linarith
  · obtain ⟨hS, -⟩ := bd_model_stable hc' hgC hg h hcm t ht0 ht1.le c hc.le hc4'
    exact (hS a).trans hC'4

/-- (A.25) [ba:eq:coercivity] and (A.26) [ba:eq:inverse-average], Lemma A.5 [ba:lem:kernels]. -/
theorem bdd_symbol (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') :
    ∃ c C' : ℝ, ∃ L₀ : ℕ, 0 < c ∧ 0 < C' ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      let P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)
      (∀ k : Fin L, c * g ^ 2 * (1 - Real.cos (2 * π * k / L)) ≤ 1 - kerSymbol P k ∧
          1 - kerSymbol P k ≤ C' * g ^ 2 * (1 - Real.cos (2 * π * k / L))) ∧
      ∀ t : ℝ, 0 ≤ t → t < 1 →
        (∀ k : Fin L, c / ((1 - t) + g ^ 2 * torusAbs L k ^ 2) ≤ (1 - t * kerSymbol P k)⁻¹ ∧
          (1 - t * kerSymbol P k)⁻¹ ≤ C' / ((1 - t) + g ^ 2 * torusAbs L k ^ 2)) ∧
        ∀ a : Fin L, (L : ℝ)⁻¹ * ∑ k : Fin L, (1 - t * kerSymbol P k)⁻¹ =
            1 + t * mixedKer P t a a ∧
          c / ((1 - t) * ellProp g L t) ≤ 1 + t * mixedKer P t a a ∧
          1 + t * mixedKer P t a a ≤ C' / ((1 - t) * ellProp g L t) := by
  set p₀ := bdp₀ C c'
  set c₁ := bdc₁ C B₀ c'
  set C₂ := bdC2 (bdμ₀ C c') (bdCP C c')
  set cB := bdcB C c₁
  have hp₀ := bdp₀_pos C hc'
  have hμ₀ := (bdμ₀_facts C hc').1
  have hCP := bdCP_pos C hc'
  have hC₂ := bdC2_pos hμ₀ hCP
  have hc₁ := bdc₁_pos C hB₀ hc'
  have hcB : 0 < cB := bdcB_pos hc₁
  have hCm := (bdCm_ge C).1
  set c := min (2 * c₁) (min (1 / (1 + C₂ / 2)) (1 / (4 * π * (1 + C₂ / 2))))
  set C' := max C₂ (max (1 / cB) ((2 + 2 * bdCm C) / cB))
  have hc : 0 < c := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hc1 : c ≤ 2 * c₁ := min_le_left _ _
  have hc2 : c ≤ 1 / (1 + C₂ / 2) := (min_le_right _ _).trans (min_le_left _ _)
  have hc3 : c ≤ 1 / (4 * π * (1 + C₂ / 2)) := (min_le_right _ _).trans (min_le_right _ _)
  have hC'1 : C₂ ≤ C' := le_max_left _ _
  have hC'2 : 1 / cB ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
  have hC'3 : (2 + 2 * bdCm C) / cB ≤ C' := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨c, C', 0, hc, lt_of_lt_of_le hC₂ hC'1, ?_⟩
  intro g hg hgC L hL _ E hE m hm hcm P
  have : NeZero L := ⟨by omega⟩
  have h := bd_model hB₀ hc' hg hgC hL hE hm hcm
  have hP : P = bdP (bdF g L E m) L := h.P_eq
  have hsym : ∀ k, kerSymbol P k = bdSym (bdF g L E m) L k := fun k => by
    rw [hP, bd_kerSymbol]
  have hcos : ∀ k : Fin L, 0 ≤ 1 - Real.cos (2 * π * k / L) := fun k => by
    linarith [Real.cos_le_one (2 * π * k / L)]
  refine ⟨fun k => ?_, fun t ht0 ht1 => ⟨fun k => ?_, fun a => ?_⟩⟩
  · obtain ⟨h1, h2⟩ := bd_sym_bounds _ g _ _ _ _ h.good k
    rw [hsym]
    have hg2 := sq_nonneg g
    constructor
    · refine le_trans ?_ h1
      have := hcos k
      gcongr
    · refine h2.trans ?_
      have := hcos k
      gcongr
  · obtain ⟨h1, h2⟩ := bd_tsym _ C g _ _ _ _ h.good hC hg hgC t ht0 ht1 k
    rw [hsym]
    have hpos : 0 < (1 - t) + g ^ 2 * torusAbs L k ^ 2 := by
      have : 0 < 1 - t := by linarith
      positivity
    have hpos2 : 0 < 1 - t * bdSym (bdF g L E m) L k := lt_of_lt_of_le (by positivity) h1
    constructor
    · rw [div_le_iff₀ hpos]
      calc c ≤ 1 / (1 + C₂ / 2) := hc2
        _ ≤ ((1 - t) + g ^ 2 * torusAbs L k ^ 2) / (1 - t * bdSym (bdF g L E m) L k) := by
            rw [div_le_div_iff₀ (by positivity) hpos2]; linarith
        _ = (1 - t * bdSym (bdF g L E m) L k)⁻¹ * ((1 - t) + g ^ 2 * torusAbs L k ^ 2) := by
            rw [div_eq_inv_mul]
    · rw [le_div_iff₀ hpos]
      calc (1 - t * bdSym (bdF g L E m) L k)⁻¹ * ((1 - t) + g ^ 2 * torusAbs L k ^ 2)
          ≤ (1 - t * bdSym (bdF g L E m) L k)⁻¹ * ((1 - t * bdSym (bdF g L E m) L k) / cB) := by
            apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hpos2.le)
            rw [le_div_iff₀ hcB, mul_comm]; exact h1
        _ = 1 / cB := by field_simp
        _ ≤ C' := hC'2
  · obtain ⟨-, -, -, -, hdiag⟩ := bd_pkg hC hg hgC h t ht0 ht1
    obtain ⟨hlo, hup, -⟩ := hdiag a
    have hid := bd_diag_eq (bdF g L E m) h.good.nonneg h.good.sum t ht0 ht1 a
    have hℓ1 : 1 ≤ ellProp g L t := bd_ell_ge (by omega) hg t
    have hδ : 0 < 1 - t := by linarith
    simp only [hsym]
    rw [← hP] at hid
    refine ⟨hid, le_trans ?_ hlo, hup.trans ?_⟩
    · gcongr
    · gcongr

/-- (A.29) [gc:eq:gradient], Lemma A.7 [da:lem:transport-refinements], for the `j`-th time
derivative. -/
theorem bdd_gradient (C B₀ c' BL : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') (hBL : 0 < BL)
    (j : ℕ) :
    ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧ ∀ A : ℝ, 0 < A → ∃ CA : ℝ, ∃ W₀ : ℕ, 0 < CA ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L →
      CA * Real.log W ≤ L → (L : ℝ) ≤ (W : ℝ) ^ BL →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      ∀ t : ℝ, 0 ≤ t → (W : ℝ) ^ (-3 : ℝ) ≤ 1 - t →
      let P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)
      let ℓ := ellProp g L t
      ∀ a b b' : Fin L,
        |iteratedDeriv j (fun t' : ℝ => mixedKer P t' a b') t -
            iteratedDeriv j (fun t' : ℝ => mixedKer P t' a b) t| ≤
          C' / ((1 - t) ^ (j + 1) * ℓ) * min ((cycDist b b' : ℝ) / ℓ) 1 *
              (Real.exp (-(c * cycDist a b / ℓ)) + Real.exp (-(c * cycDist a b' / ℓ))) +
            (W : ℝ) ^ (-A) := by
  have hμ₀ := (bdμ₀_facts C hc').1
  have hCP := bdCP_pos C hc'
  have hcμ := bdCmu_pos hμ₀ hCP
  have hp₀ := bdp₀_pos C hc'
  have hc₁ := bdc₁_pos C hB₀ hc'
  have hc4 := bdc4_pos hC hp₀ hc₁
  have hCm := (bdCm_ge C).1
  have hG₀ : 0 < bdG₀ C B₀ c' := by
    unfold bdG₀
    exact mul_pos (lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans (le_max_right _ _)))
      (div_pos (by linarith) hc4)
  refine ⟨bdCmu (bdμ₀ C c') (bdCP C c') / 2, (j.factorial : ℝ) * 7 ^ j * bdG₀ C B₀ c',
    by positivity, by positivity, ?_⟩
  intro A hA
  have hq := bdq_facts C hc'
  have h1q : 0 < 1 - bdq C c' := by linarith [hq.2]
  have hlq : 0 < Real.log (1 / bdq C c') :=
    Real.log_pos (by rw [lt_div_iff₀ hq.1]; linarith [hq.2])
  have hCl : 0 ≤ 2 * bdCm C ^ 2 * (B₀ + 2) := by positivity
  have hεC : 0 ≤ 80 / (1 - bdq C c') ^ 6 := by positivity
  refine ⟨(A + 3 * j + 2 * BL + 7) / Real.log (1 / bdq C c'),
    ⌈8 * (j.factorial : ℝ) * (2 * bdCm C ^ 2 * (B₀ + 2) + 2) * (80 / (1 - bdq C c') ^ 6)⌉₊ + 2,
    by positivity, ?_⟩
  intro W hW g hg hgC L hL hLlog hLW E hE m hm hcm t ht0 hδW P ℓ a b b'
  have hW2 : (2 : ℝ) ≤ W := by
    have : 2 ≤ W := le_trans (Nat.le_add_left 2 _) hW
    exact_mod_cast this
  have hXK : 8 * (j.factorial : ℝ) * (2 * bdCm C ^ 2 * (B₀ + 2) + 2) *
      (80 / (1 - bdq C c') ^ 6) ≤ W := by
    refine (Nat.le_ceil _).trans ?_
    have : ⌈8 * (j.factorial : ℝ) * (2 * bdCm C ^ 2 * (B₀ + 2) + 2) *
        (80 / (1 - bdq C c') ^ 6)⌉₊ ≤ W := le_trans (Nat.le_add_right _ 2) hW
    exact_mod_cast this
  have hWpos : (0 : ℝ) < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have ht1 : t < 1 := by linarith
  have : NeZero L := ⟨by omega⟩
  have h := bd_model hB₀ hc' hg hgC hL hE hm hcm
  have hP : P = bdP (bdF g L E m) L := h.P_eq
  have hP0 : ∀ x y, 0 ≤ P x y := by rw [hP]; exact bdP_nonneg _ h.good.nonneg
  have hrow : ∀ x, ∑ y, P x y = 1 := by rw [hP]; exact bdP_row_one _ h.good.sum
  have habs : |t| < 1 := by rw [abs_of_nonneg ht0]; exact ht1
  rw [bd_iteratedDeriv_K P hP0 hrow j a b' t habs, bd_iteratedDeriv_K P hP0 hrow j a b t habs,
    ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  have hgj := bd_gradj hC hB₀ hc' hg hgC h t ht0 ht1 j a b b'
  have hrem := bd_remainder j hq.1 hq.2 hεC hCl hW2 hXK (by omega : 1 ≤ L) hLlog hLW hδW
  have e : (2 * bdCm C ^ 2 * (B₀ + 2) * L + 2) * (2 * bdε C c' L / (1 - t) ^ 2) =
      (2 * bdCm C ^ 2 * (B₀ + 2) * L + 2) *
        (2 * (80 / (1 - bdq C c') ^ 6 * (1 + L) * bdq C c' ^ L) / (1 - t) ^ 2) := by
    unfold bdε; ring
  rw [e] at hgj
  have hj : 0 ≤ (j.factorial : ℝ) := by positivity
  calc (j.factorial : ℝ) * |(mixedKer P t ^ (j + 1)) a b' - (mixedKer P t ^ (j + 1)) a b|
      ≤ (j.factorial : ℝ) * (7 ^ j * bdG₀ C B₀ c' / ((1 - t) ^ (j + 1) * ℓ) *
          min ((cycDist b b' : ℝ) / ℓ) 1 *
            (Real.exp (-(bdCmu (bdμ₀ C c') (bdCP C c') / 2 * cycDist a b / ℓ)) +
              Real.exp (-(bdCmu (bdμ₀ C c') (bdCP C c') / 2 * cycDist a b' / ℓ))) +
          ((1 - t) ^ j)⁻¹ * ((2 * bdCm C ^ 2 * (B₀ + 2) * L + 2) *
            (2 * (80 / (1 - bdq C c') ^ 6 * (1 + L) * bdq C c' ^ L) / (1 - t) ^ 2))) :=
        mul_le_mul_of_nonneg_left hgj hj
    _ = (j.factorial : ℝ) * 7 ^ j * bdG₀ C B₀ c' / ((1 - t) ^ (j + 1) * ℓ) *
          min ((cycDist b b' : ℝ) / ℓ) 1 *
            (Real.exp (-(bdCmu (bdμ₀ C c') (bdCP C c') / 2 * cycDist a b / ℓ)) +
              Real.exp (-(bdCmu (bdμ₀ C c') (bdCP C c') / 2 * cycDist a b' / ℓ))) +
          (j.factorial : ℝ) * ((1 - t) ^ j)⁻¹ * ((2 * bdCm C ^ 2 * (B₀ + 2) * L + 2) *
            (2 * (80 / (1 - bdq C c') ^ 6 * (1 + L) * bdq C c' ^ L) / (1 - t) ^ 2)) := by ring
    _ ≤ _ := by gcongr

/-- Lemma 6.1 [da:lem:scales-propagators], bounded coupling: (6.2) [fo:eq:propagation-dyson] and
(6.3) [fo:eq:kernel-bounds] for every `0 ≤ u < 1`, with no finite-volume remainder. -/
theorem scalesProp_bdd (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') :
    ∃ c C' : ℝ, ∃ L₀ : ℕ, 0 < c ∧ 0 < C' ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      let M := dysonMat (hopB g) (gammaG g) L E m
      m.im ≤ C' ∧ (∀ a b, ‖M a b‖ ≤ C') ∧
      (∀ a, gammaG g * ∑ b, (‖M a b‖ + ‖M a b‖ ^ 2) ≤ C') ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ a, ∑ b, ‖(1 - (u : ℂ) • pairQ (gammaG g) M)⁻¹ a b‖ ≤ C') ∧
      ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ a b,
        0 ≤ mixedKer (pairP (gammaG g) M) u a b ∧
        mixedKer (pairP (gammaG g) M) u a b ≤
          C' / ((1 - u) * ellProp g L u) * Real.exp (-(c * cycDist a b / ellProp g L u)) := by
  set p₀ := bdp₀ C c'
  set cμ := bdCmu (bdμ₀ C c') (bdCP C c')
  set CK := 10 * (2 + 2 * bdCm C) / bdc4 C p₀ (bdc₁ C B₀ c')
  have hp₀ := bdp₀_pos C hc'
  have hμ₀ := (bdμ₀_facts C hc').1
  have hCP := bdCP_pos C hc'
  have hcμ := bdCmu_pos hμ₀ hCP
  have hc₁ := bdc₁_pos C hB₀ hc'
  have hc4 := bdc4_pos hC hp₀ hc₁
  have hCm := (bdCm_ge C).1
  have hCK : 0 < CK := by positivity
  have hCM := bdCM_pos C hc'
  set C' := max (max (bdCm C) (bdCM C c' + 1)) (max (2 / p₀) CK)
  have hC'1 : bdCm C ≤ C' := (le_max_left _ _).trans (le_max_left _ _)
  have hC'2 : bdCM C c' + 1 ≤ C' := (le_max_right _ _).trans (le_max_left _ _)
  have hC'3 : 2 / p₀ ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
  have hC'4 : CK ≤ C' := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨cμ / 2, C', 0, by positivity, by linarith, ?_⟩
  intro g hg hgC L hL _ E hE m hm hcm M
  have : NeZero L := ⟨by omega⟩
  have h := bd_model hB₀ hc' hg hgC hL hE hm hcm
  obtain ⟨hγ0, hγ1, hγC⟩ := h.gam
  have hMb : ∀ a b, ‖M a b‖ ≤ bdCM C c' := by
    intro a b
    refine le_trans ?_ (h.Mrow a)
    have h1 : ‖M a b‖ ≤ Real.exp (bdμ₀ C c' * cycDist a b) * ‖M a b‖ :=
      le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))
    exact h1.trans (Finset.single_le_sum (f := fun c => Real.exp (bdμ₀ C c' * cycDist a c) *
      ‖M a c‖) (fun c _ => by positivity) (Finset.mem_univ b))
  refine ⟨?_, fun a b => (hMb a b).trans (by linarith), fun a => ?_, fun u hu0 hu1 a => ?_,
    fun u hu0 hu1 a b => ?_⟩
  · exact (Complex.im_le_norm m).trans (h.m_le.trans hC'1)
  · have hrow := pairP_row_sum (hopB g) (gammaG g) hγ0 L (by omega) E m hm a
    simp only [pairP, Matrix.of_apply] at hrow
    have h1 : ∑ b, ‖M a b‖ ≤ bdCM C c' := by
      refine le_trans (Finset.sum_le_sum fun b _ => ?_) (h.Mrow a)
      exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))
    rw [Finset.sum_add_distrib, mul_add]
    have h2 : gammaG g * ∑ b, ‖M a b‖ ≤ ∑ b, ‖M a b‖ :=
      mul_le_of_le_one_left (Finset.sum_nonneg fun b _ => norm_nonneg _) hγ1
    have h3 : gammaG g * ∑ b, ‖M a b‖ ^ 2 = 1 := by rw [Finset.mul_sum]; exact hrow
    linarith
  · have h1 := sameSign_row_le (hopB g) (gammaG g) hγ0 L (by omega) E m hm u hu0 hu1 a
    refine h1.trans (le_trans ?_ hC'3)
    have hy : p₀ ≤ gammaG g * m.im ^ 2 := by
      have h2 : 1 / bdCm C ^ 2 ≤ gammaG g := by rw [div_le_iff₀ (by positivity)]; linarith
      have h3 : c' ^ 2 ≤ m.im ^ 2 := pow_le_pow_left₀ hc'.le hcm 2
      calc p₀ = 1 / bdCm C ^ 2 * c' ^ 2 := by unfold p₀ bdp₀; ring
        _ ≤ _ := mul_le_mul h2 h3 (by positivity) hγ0.le
    exact div_le_div_of_nonneg_left (by norm_num) hp₀ hy
  · obtain ⟨hK0, -, hprof, -, -⟩ := bd_pkg hC hg hgC h u hu0 hu1
    refine ⟨hK0 a b, (hprof a b).trans ?_⟩
    have hℓ1 : 1 ≤ ellProp g L u := bd_ell_ge (by omega) hg u
    have hδ : 0 < 1 - u := by linarith
    gcongr

end LSBA
