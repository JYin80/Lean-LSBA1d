import LSBA.Kernel.Defs

/-!
# Algebra of the deterministic kernels

Row identities and positivity of the mixed kernel and of the propagators of (5.15)
[fo:eq:propagators], the small-perturbation bound of Lemma A.9 [uvp:lem:perturb], and the abstract
early-time inverse bound of Lemma A.15 [da:lem:early-pair-inverses].
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

section Aux

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `1 - tP` is invertible for a probability kernel `P` and `0 ≤ t < 1`. -/
private lemma kalg_isUnit (P : Matrix n n ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    IsUnit (1 - t • P) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have : Nonempty n := ⟨i₀⟩
  obtain ⟨a, ha⟩ := Finite.exists_max (fun i => |v i|)
  have hva : ∀ i, v i = t * ∑ b, P i b * v b := by
    intro i
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hmv
    have := congrFun hmv i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.mulVec,
      dotProduct] at this
    linarith
  have h1 : |v a| ≤ t * |v a| := by
    calc |v a| = |t * ∑ b, P a b * v b| := by rw [← hva a]
      _ = t * |∑ b, P a b * v b| := by rw [abs_mul, abs_of_nonneg ht0]
      _ ≤ t * ∑ b, |P a b * v b| := by gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ t * ∑ b, P a b * |v a| := by
          gcongr with b _
          rw [abs_mul, abs_of_nonneg (hP a b)]
          exact mul_le_mul_of_nonneg_left (ha b) (hP a b)
      _ = t * |v a| := by rw [← Finset.sum_mul, hrow a, one_mul]
  have h2 : |v a| ≤ 0 := by nlinarith [abs_nonneg (v a)]
  apply hi₀
  have := ha i₀
  have h3 : |v i₀| ≤ 0 := le_trans this h2
  exact abs_nonpos_iff.mp h3

/-- The inverse `(1 - tP)⁻¹` is entrywise nonnegative. -/
private lemma kalg_inv_nonneg (P : Matrix n n ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (a b : n) :
    0 ≤ (1 - t • P)⁻¹ a b := by
  have hU := kalg_isUnit P hP hrow t ht0 ht1
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hmul : (1 - t • P) * (1 - t • P)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  set R := (1 - t • P)⁻¹ with hR
  have hy : ∀ c, R c b = (if c = b then 1 else 0) + t * ∑ d, P c d * R d b := by
    intro c
    have := congrFun (congrFun hmul c) b
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul, sub_mul, Finset.sum_sub_distrib] at this
    have h2 : ∑ x, t * P c x * R x b = t * ∑ d, P c d * R d b := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    have h3 : ∑ x, (if c = x then (1 : ℝ) else 0) * R x b = R c b := by simp
    rw [h2, h3] at this
    by_cases hcb : c = b <;> simp [hcb] at this ⊢ <;> linarith
  have : Nonempty n := ⟨a⟩
  obtain ⟨m, hm⟩ := Finite.exists_min (fun c => R c b)
  have h1 : t * R m b ≤ t * ∑ d, P m d * R d b := by
    apply mul_le_mul_of_nonneg_left _ ht0
    calc R m b = ∑ d, P m d * R m b := by rw [← Finset.sum_mul, hrow m, one_mul]
      _ ≤ ∑ d, P m d * R d b :=
          Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hm d) (hP m d)
  have h2 := hy m
  have h3 : 0 ≤ (if m = b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have h4 : 0 ≤ R m b := by nlinarith
  exact le_trans h4 (hm a)

open Matrix in
/-- Row sums of `(1 - tP)⁻¹` are `(1 - t)⁻¹`. -/
private lemma kalg_inv_row (P : Matrix n n ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : n) :
    ∑ b, (1 - t • P)⁻¹ a b = (1 - t)⁻¹ := by
  have hU := kalg_isUnit P hP hrow t ht0 ht1
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hmul : (1 - t • P)⁻¹ * (1 - t • P) = 1 := Matrix.nonsing_inv_mul _ hdet
  have h1 : (1 - t • P) *ᵥ (1 : n → ℝ) = (1 - t) • (1 : n → ℝ) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    funext i
    have := hrow i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply,
      mul_one, this]
  have h2 : (1 : n → ℝ) = (1 - t) • ((1 - t • P)⁻¹ *ᵥ (1 : n → ℝ)) := by
    have := congrArg (fun M => M *ᵥ (1 : n → ℝ)) hmul
    simp only [← Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_smul] at this
    exact this.symm
  have h3 := congrFun h2 a
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.one_apply, mul_one] at h3
  have h4 : (1 - t) ≠ 0 := by linarith
  field_simp
  linarith

/-- `(1 - tP)(1 - tP)⁻¹ = 1`. -/
private lemma kalg_mul_inv (P : Matrix n n ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 - t • P) * (1 - t • P)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (kalg_isUnit P hP hrow t ht0 ht1))

/-- `(1 - tP)⁻¹(1 - tP) = 1`. -/
private lemma kalg_inv_mul (P : Matrix n n ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 - t • P)⁻¹ * (1 - t • P) = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (kalg_isUnit P hP hrow t ht0 ht1))

/-- `P` commutes with `(1 - tP)⁻¹`. -/
private lemma kalg_comm (P : Matrix n n ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    P * (1 - t • P)⁻¹ = (1 - t • P)⁻¹ * P := by
  have h1 := kalg_mul_inv P hP hrow t ht0 ht1
  have h2 := kalg_inv_mul P hP hrow t ht0 ht1
  calc P * (1 - t • P)⁻¹ = (1 - t • P)⁻¹ * (1 - t • P) * (P * (1 - t • P)⁻¹) := by
        rw [h2, one_mul]
    _ = (1 - t • P)⁻¹ * ((1 - t • P) * P) * (1 - t • P)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (1 - t • P)⁻¹ * (P * (1 - t • P)) * (1 - t • P)⁻¹ := by
        congr 2
        simp [sub_mul, mul_sub]
    _ = (1 - t • P)⁻¹ * P := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]

/-- `t • P(1 - tP)⁻¹ = (1 - tP)⁻¹ - I`. -/
private lemma kalg_smul_mixedKer (P : Matrix n n ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t • mixedKer P t = (1 - t • P)⁻¹ - 1 := by
  have h1 := kalg_mul_inv P hP hrow t ht0 ht1
  unfold mixedKer
  calc t • (P * (1 - t • P)⁻¹) = (t • P) * (1 - t • P)⁻¹ := (Matrix.smul_mul _ _ _).symm
    _ = (1 - t • P)⁻¹ - (1 - t • P) * (1 - t • P)⁻¹ := by rw [sub_mul, Matrix.one_mul]; abel
    _ = (1 - t • P)⁻¹ - 1 := by rw [h1]

/-- `(1 - sP)(1 - tP)⁻¹ = I + (t - s) P(1 - tP)⁻¹`. -/
private lemma kalg_propPM_eq (P : Matrix n n ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) (s t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    propPM P s t = 1 + (t - s) • mixedKer P t := by
  have h1 := kalg_mul_inv P hP hrow t ht0 ht1
  unfold propPM mixedKer
  have : (1 - s • P) = (1 - t • P) + (t - s) • P := by
    ext i j; simp [Matrix.sub_apply]; ring
  rw [this, add_mul, h1, Matrix.smul_mul]

open scoped Matrix.Norms.Operator in
/-- Derivative in `t` of an entry of `(1 - sP)(1 - tP)⁻¹` at an invertible point. -/
private lemma kalg_hasDeriv (P : Matrix n n ℝ) (s t : ℝ)
    (hU : IsUnit (1 - t • P)) (a b : n) :
    HasDerivAt (fun t' : ℝ => ((1 - s • P) * (1 - t' • P)⁻¹) a b)
      (((1 - s • P) * ((1 - t • P)⁻¹ * P * (1 - t • P)⁻¹)) a b) t := by
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
  have h2 := (h1.comp_hasDerivAt t (by simpa using hg)).const_mul (1 - s • P)
  have h3 := ℓ.hasFDerivAt.comp_hasDerivAt t h2
  convert h3 using 1
  · funext t'
    simp [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  · simp [ℓ, hx, Matrix.nonsing_inv_eq_ringInverse]

private lemma kalg_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The cyclic distance satisfies the triangle inequality. -/
private lemma kalg_cycDist_tri {L : ℕ} (a b c : Fin L) :
    cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [cycDist, kalg_mod ha hb, kalg_mod hb ha, kalg_mod ha hc, kalg_mod hc ha,
    kalg_mod hb hc, kalg_mod hc hb]
  split_ifs <;> omega

/-- Weighted row bound for the inverse of `1 - uM` when `‖M‖ ≤ P` entrywise. -/
private lemma kalg_weighted {𝕜 : Type*} [RCLike 𝕜] {L : ℕ} (P : Matrix (Fin L) (Fin L) ℝ)
    (M : Matrix (Fin L) (Fin L) 𝕜) (μ : ℝ) (hμ : 0 ≤ μ) (hP : ∀ a b, 0 ≤ P a b)
    (hM : ∀ a b, ‖M a b‖ ≤ P a b)
    (hw : ∀ a, ∑ b, Real.exp (μ * cycDist a b) * P a b ≤ 3 / 2)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) (a : Fin L) :
    ∑ b, Real.exp (μ * cycDist a b) * ‖(1 - u • M)⁻¹ a b‖ ≤ 4 := by
  by_cases hU : IsUnit (1 - u • M).det
  swap
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hU]
    simp
  set N := (1 - u • M)⁻¹ with hN
  have hmul : N * (1 - u • M) = 1 := Matrix.nonsing_inv_mul _ hU
  set w : Fin L → Fin L → ℝ := fun a b => Real.exp (μ * cycDist a b) with hwdef
  have hw_tri : ∀ a b c, w a c ≤ w a b * w b c := by
    intro a b c
    simp only [hwdef, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ hμ
    exact_mod_cast kalg_cycDist_tri a b c
  have hw_self : ∀ a, w a a = 1 := by intro a; simp [hwdef, cycDist]
  have hw_pos : ∀ a b, 0 < w a b := fun a b => Real.exp_pos _
  -- entrywise identity
  have hent : ∀ b, N a b = (if a = b then 1 else 0) + u • ∑ c, N a c * M c b := by
    intro b
    have := congrFun (congrFun hmul a) b
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      mul_sub, Finset.sum_sub_distrib] at this
    have h2 : ∑ c, N a c * (u • M c b) = u • ∑ c, N a c * M c b := by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun c _ => by
        rw [mul_smul_comm]
    have h3 : ∑ c, N a c * (if c = b then (1 : 𝕜) else 0) = N a b := by simp
    rw [h2, h3] at this
    by_cases hab : a = b
    · subst hab; simp at this ⊢; rw [← this]; abel
    · simp [hab] at this ⊢; exact sub_eq_zero.mp this
  have hnorm : ∀ b, ‖N a b‖ ≤ (if a = b then 1 else 0) + u * ∑ c, ‖N a c‖ * P c b := by
    intro b
    rw [hent b]
    calc ‖(if a = b then (1 : 𝕜) else 0) + u • ∑ c, N a c * M c b‖
        ≤ ‖(if a = b then (1 : 𝕜) else 0)‖ + ‖u • ∑ c, N a c * M c b‖ := norm_add_le _ _
      _ ≤ (if a = b then 1 else 0) + u * ∑ c, ‖N a c‖ * P c b := by
          gcongr
          · split_ifs <;> simp
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu0]
            gcongr
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hM c b) (norm_nonneg _)
  set X := ∑ b, w a b * ‖N a b‖ with hX
  have hX1 : X ≤ 1 + (3 * u / 2) * X := by
    calc X ≤ ∑ b, w a b * ((if a = b then 1 else 0) + u * ∑ c, ‖N a c‖ * P c b) :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hnorm b) (hw_pos a b).le
      _ = ∑ b, w a b * (if a = b then 1 else 0) +
            u * ∑ b, ∑ c, w a b * (‖N a c‖ * P c b) := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
      _ ≤ 1 + u * ∑ c, ‖N a c‖ * (w a c * (3 / 2)) := by
          have h1 : ∑ b, w a b * (if a = b then (1 : ℝ) else 0) ≤ 1 := by simp [hw_self]
          have h2 : ∑ b, ∑ c, w a b * (‖N a c‖ * P c b) ≤ ∑ c, ‖N a c‖ * (w a c * (3 / 2)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_le_sum fun c _ => ?_
            calc ∑ b, w a b * (‖N a c‖ * P c b)
                ≤ ∑ b, ‖N a c‖ * (w a c * (w c b * P c b)) := by
                  refine Finset.sum_le_sum fun b _ => ?_
                  have := hw_tri a c b
                  have h1 : 0 ≤ ‖N a c‖ * P c b := mul_nonneg (norm_nonneg _) (hP c b)
                  nlinarith [mul_le_mul_of_nonneg_right this h1]
              _ = ‖N a c‖ * (w a c * ∑ b, w c b * P c b) := by
                  rw [Finset.mul_sum, Finset.mul_sum]
              _ ≤ ‖N a c‖ * (w a c * (3 / 2)) := by
                  gcongr
                  exact hw c
          exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 hu0)
      _ = 1 + (3 * u / 2) * X := by
          rw [hX, Finset.mul_sum, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun c _ => by ring
  nlinarith [Finset.sum_nonneg
    (fun b (_ : b ∈ Finset.univ) => mul_nonneg (hw_pos a b).le (norm_nonneg (N a b)))]

end Aux

/-- A probability kernel gives a nonnegative mixed kernel with row `(1-u)⁻¹`, after (5.13)
[fo:eq:pairs]. -/
theorem mixedKer_nonneg_row {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (∀ a b, 0 ≤ mixedKer P u a b) ∧ ∀ a, ∑ b, mixedKer P u a b = (1 - u)⁻¹ := by
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · unfold mixedKer
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun c _ => mul_nonneg (hP a c) (kalg_inv_nonneg P hP hrow u hu0 hu1 c b)
  · unfold mixedKer
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, kalg_inv_row P hP hrow u hu0 hu1, ← Finset.sum_mul, hrow, one_mul]

/-- (A.47) [gc:eq:propagator-input], first line: `U^{+-}_{s,t} ≥ 0` with row `(1-s)/(1-t)`. -/
theorem propPM_nonneg_row {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) :
    (∀ a b, 0 ≤ propPM P s t a b) ∧ ∀ a, ∑ b, propPM P s t a b = (1 - s) / (1 - t) := by
  have ht0 : 0 ≤ t := le_trans hs hst
  obtain ⟨hK, hKr⟩ := mixedKer_nonneg_row P hP hrow t ht0 ht
  rw [kalg_propPM_eq P hP hrow s t ht0 ht]
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    have : 0 ≤ (if a = b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    nlinarith [hK a b, sub_nonneg.mpr hst]
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hKr a, Matrix.one_apply]
    have : (1 - t) ≠ 0 := by linarith
    field_simp
    simp

/-- The identities after (5.15) [fo:eq:propagators]: `U^{+-}_{s,t} = I + (t-s)P(I-tP)⁻¹`,
`U_{s,u}U_{u,t} = U_{s,t}`, and `∂_t U^{+-}_{s,t} = P(I-tP)⁻¹ U^{+-}_{s,t}`. -/
theorem propPM_identities {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1) (s u t : ℝ) (hs : 0 ≤ s)
    (hsu : s ≤ u) (hut : u ≤ t) (ht : t < 1) :
    propPM P s t = 1 + (t - s) • mixedKer P t ∧ propPM P s u * propPM P u t = propPM P s t ∧
      ∀ a b, HasDerivAt (fun t' : ℝ => propPM P s t' a b)
        ((mixedKer P t * propPM P s t) a b) t := by
  have hu0 : 0 ≤ u := le_trans hs hsu
  have ht0 : 0 ≤ t := le_trans hu0 hut
  refine ⟨kalg_propPM_eq P hP hrow s t ht0 ht, ?_, ?_⟩
  · unfold propPM
    have h2 := kalg_inv_mul P hP hrow u hu0 (lt_of_le_of_lt hut ht)
    calc (1 - s • P) * (1 - u • P)⁻¹ * ((1 - u • P) * (1 - t • P)⁻¹)
        = (1 - s • P) * ((1 - u • P)⁻¹ * (1 - u • P)) * (1 - t • P)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (1 - s • P) * (1 - t • P)⁻¹ := by rw [h2, Matrix.mul_one]
  · intro a b
    have hU := kalg_isUnit P hP hrow t ht0 ht
    have h := kalg_hasDeriv P s t hU a b
    have hc := kalg_comm P hP hrow t ht0 ht
    have e : (1 - s • P) * ((1 - t • P)⁻¹ * P * (1 - t • P)⁻¹) =
        mixedKer P t * propPM P s t := by
      unfold mixedKer propPM
      have hc' : (1 - t • P)⁻¹ * P = P * (1 - t • P)⁻¹ := hc.symm
      have hAP : (1 - s • P) * P = P * (1 - s • P) := by simp [sub_mul, mul_sub]
      have hAR : (1 - s • P) * (1 - t • P)⁻¹ = (1 - t • P)⁻¹ * (1 - s • P) := by
        simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
          Matrix.mul_smul, hc]
      calc (1 - s • P) * ((1 - t • P)⁻¹ * P * (1 - t • P)⁻¹)
          = ((1 - s • P) * (1 - t • P)⁻¹) * P * (1 - t • P)⁻¹ := by simp only [Matrix.mul_assoc]
        _ = (1 - t • P)⁻¹ * ((1 - s • P) * P) * (1 - t • P)⁻¹ := by
            rw [hAR]; simp only [Matrix.mul_assoc]
        _ = ((1 - t • P)⁻¹ * P) * ((1 - s • P) * (1 - t • P)⁻¹) := by
            rw [hAP]; simp only [Matrix.mul_assoc]
        _ = P * (1 - t • P)⁻¹ * ((1 - s • P) * (1 - t • P)⁻¹) := by rw [hc']
    rw [e] at h
    exact h

/-- Lemma A.9 [uvp:lem:perturb], with constant `1` and without the hypothesis `ε ≤ cδ²`. -/
theorem kernel_perturb {n : Type*} [Fintype n] [DecidableEq n] (P₀ P₁ : Matrix n n ℝ)
    (h₀ : ∀ x y, 0 ≤ P₀ x y) (h₁ : ∀ x y, 0 ≤ P₁ x y) (hr₀ : ∀ x, ∑ y, P₀ x y = 1)
    (hr₁ : ∀ x, ∑ y, P₁ x y = 1) (hsym : P₀.transpose = P₀) (ε a δ : ℝ) (ha : 0 < a)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε1 : ∀ x, ∑ y, |P₁ x y - P₀ x y| ≤ ε)
    (hεsup : ∀ x y, |P₁ x y - P₀ x y| ≤ ε / a) :
    (∀ x, ∑ y, |(1 - δ) * (mixedKer P₁ (1 - δ) x y - mixedKer P₀ (1 - δ) x y)| ≤ ε / δ ^ 2) ∧
      ∀ x y, |(1 - δ) * (mixedKer P₁ (1 - δ) x y - mixedKer P₀ (1 - δ) x y)| ≤
        ε / (a * δ ^ 2) := by
  set t : ℝ := 1 - δ with ht
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t < 1 := by linarith
  have hδt : 1 - t = δ := by rw [ht]; ring
  set R₀ := (1 - t • P₀)⁻¹ with hR₀
  set R₁ := (1 - t • P₁)⁻¹ with hR₁
  have hR0n : ∀ x y, 0 ≤ R₀ x y := kalg_inv_nonneg P₀ h₀ hr₀ t ht0 ht1
  have hR1n : ∀ x y, 0 ≤ R₁ x y := kalg_inv_nonneg P₁ h₁ hr₁ t ht0 ht1
  have hR0r : ∀ x, ∑ y, R₀ x y = δ⁻¹ := fun x => by
    rw [hR₀, kalg_inv_row P₀ h₀ hr₀ t ht0 ht1, hδt]
  have hR1r : ∀ x, ∑ y, R₁ x y = δ⁻¹ := fun x => by
    rw [hR₁, kalg_inv_row P₁ h₁ hr₁ t ht0 ht1, hδt]
  have hR0c : ∀ y, ∑ x, R₀ x y = δ⁻¹ := fun y => by
    have : R₀.transpose = R₀ := by
      rw [hR₀, Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.transpose_smul, hsym]
    calc ∑ x, R₀ x y = ∑ x, R₀.transpose y x := by simp [Matrix.transpose_apply]
      _ = ∑ x, R₀ y x := by rw [this]
      _ = δ⁻¹ := hR0r y
  have hδ0 : δ⁻¹ ≠ 0 := inv_ne_zero hδ.ne'
  have hU0 := kalg_mul_inv P₀ h₀ hr₀ t ht0 ht1
  have hU1 := kalg_inv_mul P₁ h₁ hr₁ t ht0 ht1
  -- `t (K₁ - K₀) = R₁ - R₀ = t R₁ (P₁ - P₀) R₀`
  have hE : ∀ x y, t * (mixedKer P₁ t x y - mixedKer P₀ t x y) =
      t * ∑ w, ∑ z, R₁ x z * (P₁ z w - P₀ z w) * R₀ w y := by
    intro x y
    have e1 : t • mixedKer P₁ t - t • mixedKer P₀ t = t • (R₁ * (P₁ - P₀) * R₀) := by
      rw [kalg_smul_mixedKer P₁ h₁ hr₁ t ht0 ht1, kalg_smul_mixedKer P₀ h₀ hr₀ t ht0 ht1]
      have h2 : R₁ * ((1 - t • P₀) - (1 - t • P₁)) * R₀ = R₁ - R₀ := by
        calc R₁ * ((1 - t • P₀) - (1 - t • P₁)) * R₀
            = R₁ * ((1 - t • P₀) * R₀) - (R₁ * (1 - t • P₁)) * R₀ := by
              simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
          _ = R₁ - R₀ := by rw [hU0, hU1, Matrix.mul_one, Matrix.one_mul]
      have h3 : (1 - t • P₀) - (1 - t • P₁) = t • (P₁ - P₀) := by module
      rw [h3, Matrix.mul_smul, Matrix.smul_mul] at h2
      rw [h2]; abel
    have e2 := congrFun (congrFun e1 x) y
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at e2
    rw [mul_sub, e2]
    refine congrArg (t * ·) (Finset.sum_congr rfl fun w _ => ?_)
    rw [Finset.sum_mul]
  have hB : ∀ x y, |t * (mixedKer P₁ t x y - mixedKer P₀ t x y)| ≤
      t * ∑ w, ∑ z, R₁ x z * |P₁ z w - P₀ z w| * R₀ w y := by
    intro x y
    rw [hE x y, abs_mul, abs_of_nonneg ht0]
    refine mul_le_mul_of_nonneg_left ?_ ht0
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (hR1n x z), abs_of_nonneg (hR0n w y)]
  have hε0 : ∀ x : n, 0 ≤ ε := fun x =>
    le_trans (Finset.sum_nonneg fun y _ => abs_nonneg _) (hε1 x)
  have hδ2 : 0 < δ ^ 2 := by positivity
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · have hε := hε0 x
    calc ∑ y, |t * (mixedKer P₁ t x y - mixedKer P₀ t x y)|
        ≤ ∑ y, t * ∑ w, ∑ z, R₁ x z * |P₁ z w - P₀ z w| * R₀ w y :=
          Finset.sum_le_sum fun y _ => hB x y
      _ = t * ∑ w, ∑ z, R₁ x z * |P₁ z w - P₀ z w| * ∑ y, R₀ w y := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.mul_sum]
      _ = t * (δ⁻¹ * ∑ z, R₁ x z * ∑ w, |P₁ z w - P₀ z w|) := by
          simp only [hR0r]
          congr 1
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          ring
      _ ≤ t * (δ⁻¹ * ∑ z, R₁ x z * ε) := by
          gcongr with z _
          · exact hR1n x z
          · exact hε1 z
      _ = t * (δ⁻¹ * δ⁻¹ * ε) := by rw [← Finset.sum_mul, hR1r]; ring
      _ ≤ 1 * (δ⁻¹ * δ⁻¹ * ε) := by
          gcongr
      _ = ε / δ ^ 2 := by field_simp
  · have hε := hε0 x
    have hεa : 0 ≤ ε / a := div_nonneg hε ha.le
    calc |t * (mixedKer P₁ t x y - mixedKer P₀ t x y)|
        ≤ t * ∑ w, ∑ z, R₁ x z * |P₁ z w - P₀ z w| * R₀ w y := hB x y
      _ ≤ t * ∑ w, ∑ z, R₁ x z * (ε / a) * R₀ w y := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ =>
            Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hεsup z w) (hR1n x z)) (hR0n w y)) ht0
      _ = t * ((∑ z, R₁ x z) * (ε / a) * ∑ w, R₀ w y) := by
          simp only [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ 1 * (δ⁻¹ * (ε / a) * δ⁻¹) := by
          rw [hR1r, hR0c]
          gcongr
      _ = ε / (a * δ ^ 2) := by field_simp

/-- Neumann form of Lemma A.15 [da:lem:early-pair-inverses]: a weighted row bound `3/2` for `P`
and `|Q| ≤ P` give weighted inverse rows at most `8` for `u ≤ 1/2`. -/
theorem early_inverse_abstract {L : ℕ} (P : Matrix (Fin L) (Fin L) ℝ)
    (Q : Matrix (Fin L) (Fin L) ℂ) (μ : ℝ) (hμ : 0 ≤ μ) (hP : ∀ a b, 0 ≤ P a b)
    (hQ : ∀ a b, ‖Q a b‖ ≤ P a b) (hw : ∀ a, ∑ b, Real.exp (μ * cycDist a b) * P a b ≤ 3 / 2)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) (a : Fin L) :
    ∑ b, Real.exp (μ * cycDist a b) * (|(1 - u • P)⁻¹ a b| + ‖(1 - (u : ℂ) • Q)⁻¹ a b‖) ≤ 8 := by
  have h1 := kalg_weighted P P μ hμ hP (fun a b => by rw [Real.norm_eq_abs, abs_of_nonneg (hP a b)])
    hw u hu0 hu a
  have h2 := kalg_weighted P Q μ hμ hP hQ hw u hu0 hu a
  have hc : (u : ℂ) • Q = u • Q := by ext i j; simp [Complex.real_smul]
  rw [hc]
  simp only [Real.norm_eq_abs] at h1
  simp only [mul_add, Finset.sum_add_distrib]
  linarith

end LSBA
