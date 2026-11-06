import LSBA.Averaging.Loops
import LSBA.Averaging.Ward

/-!
# Lemma 5.6 [fo:prop:inputs] at a fixed time

The far-block, pair and tail fields of Lemma 5.6 [fo:prop:inputs], and the lemma in fixed-time
form: (5.23) [gc:eq:iteration-input] at each deterministic `u ∈ [0, 1/2]` on the large-coupling
family, with no upper bound on `g`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Cyclic distance and cells -/

private theorem lemma46_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The cyclic distance is symmetric. -/
private theorem lemma46_cd_comm {L : ℕ} (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

/-- The cyclic distance satisfies the triangle inequality. -/
private theorem lemma46_cd_tri {L : ℕ} (a b c : Fin L) :
    cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [cycDist, lemma46_mod ha hb, lemma46_mod hb ha, lemma46_mod ha hc, lemma46_mod hc ha,
    lemma46_mod hb hc, lemma46_mod hc hb]
  split_ifs <;> omega

/-- The cyclic distance is at most the difference of the representatives. -/
private theorem lemma46_cd_le_sub {L : ℕ} (a b : Fin L) (h : b.val ≤ a.val) :
    cycDist a b ≤ a.val - b.val := by
  unfold cycDist
  rw [lemma46_mod a.isLt b.isLt]
  simp only [h, ↓reduceIte]
  exact min_le_left _ _

private theorem lemma46_val_finRotate {L : ℕ} (x : Fin L) :
    (finRotate L x).val = (x.val + 1) % L := by
  cases L with
  | zero => exact x.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : x = Fin.last n
    · subst h
      simp
    · simp only [h, ↓reduceIte]
      have : x.val < n := by
        have h1 := x.isLt
        have h2 : x.val ≠ n := fun h' => h (Fin.ext (by simpa using h'))
        omega
      rw [Nat.mod_eq_of_lt (by omega)]

/-- Neighbours on the cycle are at distance at most one. -/
private theorem lemma46_cd_rot {L : ℕ} (x : Fin L) : cycDist x (finRotate L x) ≤ 1 := by
  have hx := x.isLt
  have hy := (finRotate L x).isLt
  have hv := lemma46_val_finRotate x
  simp only [cycDist, lemma46_mod hx hy, lemma46_mod hy hx]
  by_cases h : x.val + 1 < L
  · rw [Nat.mod_eq_of_lt h] at hv
    split_ifs <;> omega
  · have e : (x.val + 1) % L = 0 := by
      rw [show x.val + 1 = L by omega, Nat.mod_self]
    rw [e] at hv
    split_ifs <;> omega

/-- A block is within `n - 1` of the first block of its cell. -/
private theorem lemma46_cd_start (n : ℕ) (hn : 1 ≤ n) {L : ℕ} (a : Fin L) :
    cycDist a (cellStart n a) + 1 ≤ n := by
  have h1 : (cellStart n a).val = a.val / n * n := rfl
  have h2 := Nat.div_add_mod a.val n
  have h3 := Nat.mod_lt a.val (show 0 < n by omega)
  have h4 := lemma46_cd_le_sub a (cellStart n a) (by rw [h1]; exact Nat.div_mul_le_self _ _)
  rw [h1] at h4
  have h2' : a.val / n * n + a.val % n = a.val := by rw [Nat.mul_comm]; exact h2
  omega

/-- A block is within `n` of the predecessor of the first block of its cell. -/
private theorem lemma46_cd_prev (n : ℕ) (hn : 1 ≤ n) {L : ℕ} (a : Fin L) :
    cycDist a (cellPrev n a) ≤ n := by
  have h1 := lemma46_cd_start n hn a
  have h2 : cycDist (cellStart n a) (cellPrev n a) ≤ 1 := by
    rw [lemma46_cd_comm]
    have := lemma46_cd_rot (cellPrev n a)
    unfold cellPrev at this ⊢
    rwa [Equiv.apply_symm_apply] at this
  have := lemma46_cd_tri a (cellStart n a) (cellPrev n a)
  omega

/-- Two blocks of the same cell are at distance at most `2(n - 1)`. -/
private theorem lemma46_cd_same (n : ℕ) (hn : 1 ≤ n) {L : ℕ} (a b : Fin L)
    (h : cellStart n b = cellStart n a) : cycDist a b + 2 ≤ 2 * n := by
  have h1 := lemma46_cd_start n hn a
  have h2 := lemma46_cd_start n hn b
  have h3 := lemma46_cd_tri a (cellStart n a) b
  rw [h] at h2
  rw [lemma46_cd_comm (cellStart n a) b] at h3
  omega

/-- The free source coefficient vanishes for blocks at distance at least `2n`. -/
private theorem lemma46_src_far (n : ℕ) (hn : 1 ≤ n) (E : ℝ) {L : ℕ} (a b : Fin L)
    (h : 2 * n ≤ cycDist a b) : cellSrc n E a b = 0 := by
  unfold cellSrc
  have hn' : ¬ (cellStart n b = cellStart n a ∧ b.val % n < a.val % n) := by
    rintro ⟨h1, -⟩
    have := lemma46_cd_same n hn a b h1
    omega
  simp only [hn', ↓reduceIte]

/-- The source coefficient `d_{ab}` of Proposition 7.4 [uvc:prop:green] vanishes for blocks at
distance at least `3n`. -/
private theorem lemma46_cellD_far (n : ℕ) (hn : 1 ≤ n) (E : ℝ) {L : ℕ} (a b : Fin L)
    (h : 3 * n ≤ cycDist a b) : cellD n E a b = 0 := by
  unfold cellD
  rw [lemma46_src_far n hn E a b (by omega), zero_add]
  refine Finset.sum_eq_zero fun α _ => ?_
  by_cases h1 : α = cellStart n a
  · have h2 := lemma46_cd_start n hn a
    have h3 := lemma46_cd_tri a α b
    rw [lemma46_src_far n hn E b α (by rw [lemma46_cd_comm]; subst h1; omega), mul_zero]
  · by_cases h2 : α = cellPrev n a
    · have h4 := lemma46_cd_prev n hn a
      have h3 := lemma46_cd_tri a α b
      rw [lemma46_src_far n hn E b α (by rw [lemma46_cd_comm]; subst h2; omega), mul_zero]
    · have : cellCoef n E a α = 0 := by unfold cellCoef; simp only [h1, h2, ↓reduceIte]
      rw [this, zero_mul]

/-- The anchors of the cells of `a` and `b` are at distance at least `d(a, b) - 2n`. -/
private theorem lemma46_anchor_far (n : ℕ) (hn : 1 ≤ n) {L : ℕ} (a b α β : Fin L)
    (hα : α = cellStart n a ∨ α = cellPrev n a) (hβ : β = cellStart n b ∨ β = cellPrev n b) :
    cycDist a b ≤ cycDist α β + 2 * n := by
  have h1 : cycDist a α ≤ n := by
    rcases hα with rfl | rfl
    · have := lemma46_cd_start n hn a; omega
    · exact lemma46_cd_prev n hn a
  have h2 : cycDist β b ≤ n := by
    rw [lemma46_cd_comm]
    rcases hβ with rfl | rfl
    · have := lemma46_cd_start n hn b; omega
    · exact lemma46_cd_prev n hn b
  have h3 := lemma46_cd_tri a α b
  have h4 := lemma46_cd_tri α β b
  omega

/-! ### The free coefficients -/

private lemma lemma46_sin_ge {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) :
    κ / 2 ≤ Real.sin (Real.arccos (E / 2)) := by
  rw [Real.sin_arccos]
  have hE2 : (E / 2) ^ 2 ≤ (1 - κ / 2) ^ 2 := by
    rw [div_pow, ← sq_abs]
    have : |E| / 2 ≤ 1 - κ / 2 := by linarith
    have h0 : 0 ≤ |E| / 2 := by positivity
    calc |E| ^ 2 / 2 ^ 2 = (|E| / 2) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ h0 this 2
  have h1 : (κ / 2) ^ 2 ≤ 1 - (E / 2) ^ 2 := by nlinarith
  calc κ / 2 = Real.sqrt ((κ / 2) ^ 2) := (Real.sqrt_sq (by linarith)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h1

private lemma lemma46_coef_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a α : Fin L) : |cellCoef n E a α| ≤ 2 / κ := by
  have hs := lemma46_sin_ge hκ hκ2 hE
  have hs0 : 0 < Real.sin (Real.arccos (E / 2)) := by linarith
  have hk : (Real.sin (Real.arccos (E / 2)))⁻¹ ≤ 2 / κ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hs0 hκ]
    linarith
  have hb : ∀ t : ℝ, |Real.sin t / Real.sin (Real.arccos (E / 2))| ≤ 2 / κ := fun t => by
    rw [abs_div, abs_of_pos hs0, div_eq_mul_inv]
    calc |Real.sin t| * (Real.sin (Real.arccos (E / 2)))⁻¹ ≤ 1 * (2 / κ) :=
          mul_le_mul (Real.abs_sin_le_one t) hk (by positivity) zero_le_one
      _ = 2 / κ := one_mul _
  unfold cellCoef
  split_ifs
  · exact hb _
  · rw [abs_neg]; exact hb _
  · simp only [abs_zero]; positivity

private lemma lemma46_coef_sum_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a : Fin L) : ∑ α : Fin L, |cellCoef n E a α| ≤ 4 / κ := by
  have h : ∀ α : Fin L, |cellCoef n E a α| ≤
      (if α = cellStart n a then 2 / κ else 0) + (if α = cellPrev n a then 2 / κ else 0) := by
    intro α
    have hc := lemma46_coef_abs_le hκ hκ2 hE n a α
    have hk : (0 : ℝ) ≤ 2 / κ := by positivity
    by_cases h1 : α = cellStart n a
    · have e1 : (if α = cellStart n a then 2 / κ else 0) = 2 / κ := by simp [h1]
      have : (0 : ℝ) ≤ if α = cellPrev n a then 2 / κ else 0 := by split_ifs <;> linarith
      rw [e1]
      linarith
    · have e1 : (if α = cellStart n a then 2 / κ else 0) = 0 := by simp [h1]
      by_cases h2 : α = cellPrev n a
      · have e2 : (if α = cellPrev n a then 2 / κ else 0) = 2 / κ := by simp [h2]
        rw [e1, e2]
        linarith
      · have h0 : cellCoef n E a α = 0 := by unfold cellCoef; simp only [h1, h2, ↓reduceIte]
        have e2 : (if α = cellPrev n a then 2 / κ else 0) = 0 := by simp [h2]
        rw [h0, e1, e2]
        simp
  calc ∑ α, |cellCoef n E a α| ≤ ∑ α : Fin L, ((if α = cellStart n a then 2 / κ else 0) +
        (if α = cellPrev n a then 2 / κ else 0)) := Finset.sum_le_sum fun α _ => h α
    _ = 4 / κ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp only [Finset.mem_univ, ite_true]
        ring

private lemma lemma46_coef_ne (n : ℕ) (E : ℝ) {L : ℕ} (a α : Fin L) (h : cellCoef n E a α ≠ 0) :
    α = cellStart n a ∨ α = cellPrev n a := by
  unfold cellCoef at h
  by_cases h1 : α = cellStart n a
  · exact Or.inl h1
  · by_cases h2 : α = cellPrev n a
    · exact Or.inr h2
    · simp [h1, h2] at h

/-- The interpolation through the four anchor pairs of the cells of `a` and `b` is at most
`(4/κ)²` times their largest block. -/
private lemma lemma46_norming {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) (n : ℕ)
    {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (t : ℝ) (ht : 0 ≤ t) (a b : Fin L)
    (hX : anchorNorm n G a b ≤ t) :
    ‖∑ α : Fin L, ∑ β : Fin L, ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) • blockOf G α β‖ ≤
      (4 / κ) ^ 2 * t := by
  have hX' : ∀ α β, (α = cellStart n a ∨ α = cellPrev n a) →
      (β = cellStart n b ∨ β = cellPrev n b) → ‖blockOf G α β‖ ≤ t := by
    intro α β hα hβ
    refine le_trans ?_ hX
    unfold anchorNorm
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_of_le_right (le_max_right _ _)
  have hterm : ∀ α β : Fin L, ‖((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) • blockOf G α β‖ ≤
      |cellCoef n E a α| * |cellCoef n E b β| * t := by
    intro α β
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    by_cases h1 : cellCoef n E a α = 0
    · simp [h1]
    by_cases h2 : cellCoef n E b β = 0
    · simp [h2]
    exact mul_le_mul_of_nonneg_left (hX' α β (lemma46_coef_ne n E a α h1)
      (lemma46_coef_ne n E b β h2)) (by positivity)
  calc _ ≤ ∑ α : Fin L, ∑ β : Fin L,
        ‖((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) • blockOf G α β‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => norm_sum_le _ _)
    _ ≤ ∑ α : Fin L, ∑ β : Fin L, |cellCoef n E a α| * |cellCoef n E b β| * t :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hterm α β
    _ = (∑ α, |cellCoef n E a α|) * (∑ β, |cellCoef n E b β|) * t := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (4 / κ) * (4 / κ) * t := by
        have h1 := lemma46_coef_sum_le hκ hκ2 hE n a
        have h2 := lemma46_coef_sum_le hκ hκ2 hE n b
        have h0 : 0 ≤ ∑ β, |cellCoef n E b β| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 h0 (by positivity)) ht
    _ = (4 / κ) ^ 2 * t := by ring

/-- A far block through the anchor pairs, deterministic form: if `d_{ab} = 0`, the four anchor
blocks are at most `t ≤ 1` and the error of Proposition 7.4 [uvc:prop:green] holds with `e`, then
`‖G_{ab}‖ ≤ (4/κ)² t + 2 C e`. -/
private lemma lemma46_far_block {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) (n : ℕ)
    {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (Cg e t : ℝ) (hCg : 0 ≤ Cg)
    (he : 0 ≤ e) (ht : 0 ≤ t) (ht1 : t ≤ 1) (a b : Fin L) (hD : cellD n E a b = 0)
    (hX : anchorNorm n G a b ≤ t)
    (hGi : ‖blockOf G a b - interpBlock n E G a b‖ ≤ Cg * e * (1 + anchorNorm n G a b)) :
    ‖blockOf G a b‖ ≤ (4 / κ) ^ 2 * t + 2 * Cg * e := by
  have h1 := lemma46_norming hκ hκ2 hE n G t ht a b hX
  have hI : interpBlock n E G a b = ∑ α : Fin L, ∑ β : Fin L,
      ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) • blockOf G α β := by
    unfold interpBlock; rw [hD]; simp
  have h2 : Cg * e * (1 + anchorNorm n G a b) ≤ 2 * Cg * e := by
    have : 1 + anchorNorm n G a b ≤ 2 := by linarith
    calc Cg * e * (1 + anchorNorm n G a b) ≤ Cg * e * 2 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * Cg * e := by ring
  calc ‖blockOf G a b‖ = ‖(blockOf G a b - interpBlock n E G a b) + interpBlock n E G a b‖ := by
        rw [sub_add_cancel]
    _ ≤ 2 * Cg * e + (4 / κ) ^ 2 * t :=
        (norm_add_le _ _).trans (add_le_add (hGi.trans h2) (by rw [hI]; exact h1))
    _ = _ := by ring

/-! ### Markov bounds and counting -/

/-- Markov's inequality for the `p`-th moment: `P(f > t) ≤ K t^{-p}` when `E f^p ≤ K`. -/
private lemma lemma46_markov {X : Type*} [MeasurableSpace X] (P : Measure X) [IsFiniteMeasure P]
    (f : X → ℝ) (p : ℕ) (t K : ℝ) (ht : 0 < t) (hf0 : ∀ ω, 0 ≤ f ω)
    (hf : Integrable (fun ω => f ω ^ p) P) (hK : ∫ ω, f ω ^ p ∂P ≤ K) :
    P {ω | t < f ω} ≤ ENNReal.ofReal (K / t ^ p) := by
  have htp : 0 < t ^ p := pow_pos ht p
  have hsub : {ω | t < f ω} ⊆ {ω | t ^ p ≤ f ω ^ p} := fun ω hω =>
    pow_le_pow_left₀ ht.le (le_of_lt hω) p
  have hM := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => pow_nonneg (hf0 ω) p) hf (t ^ p)
  refine (measure_mono hsub).trans ?_
  have hK0 : 0 ≤ K := (integral_nonneg fun ω => pow_nonneg (hf0 ω) p).trans hK
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity), le_div_iff₀ htp]
  rw [measureReal_def] at hM
  nlinarith

/-- The exponential tail of an anchor pair at distance `≥ (K/2) g² log W` with `cK/2 = A + 2`:
`C_q e^{-qcd/g²} (W^{-(A+1)})^{-q} ≤ C_q W^{-q}`. -/
private lemma lemma46_tail_rate (W g c A Cq d : ℝ) (q : ℕ) (hW : 1 ≤ W) (hg : 0 < g ^ 2)
    (hc : 0 < c) (hCq : 0 ≤ Cq) (hd : 2 * (A + 2) / c / 2 * g ^ 2 * Real.log W ≤ d) :
    Cq * Real.exp (-(q * c * d / g ^ 2)) / (W ^ (-(A + 1))) ^ q ≤ Cq * W ^ (-(q : ℝ)) := by
  have hW0 : 0 < W := by linarith
  have hl : 0 ≤ Real.log W := Real.log_nonneg hW
  have e1 : (W ^ (-(A + 1))) ^ q = Real.exp (-(A + 1) * q * Real.log W) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, Real.rpow_def_of_pos hW0]
    congr 1; ring
  have e2 : W ^ (-(q : ℝ)) = Real.exp (-(q * Real.log W)) := by
    rw [Real.rpow_def_of_pos hW0]; congr 1; ring
  rw [e1, e2, mul_div_assoc, ← Real.exp_sub]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCq
  have hd' : (A + 2) * Real.log W ≤ c * d / g ^ 2 := by
    rw [le_div_iff₀ hg]
    have : 2 * (A + 2) / c / 2 * g ^ 2 * Real.log W * c = (A + 2) * Real.log W * g ^ 2 := by
      field_simp
    nlinarith
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have : q * c * d / g ^ 2 = q * (c * d / g ^ 2) := by ring
  rw [this]
  nlinarith

/-- The count of the union bound: `W^{-D-1} + N C_q W^{-q} ≤ W^{-D}` for `N ≤ 36 W^{2B+6}`,
`q ≥ 2B + D + 8` and `W ≥ max(2, 36 C_q)`. -/
private lemma lemma46_count (W D B Cq N : ℝ) (q : ℕ) (hW : 2 ≤ W) (hCq : 0 ≤ Cq)
    (hWC : 36 * Cq ≤ W) (hq : 2 * B + D + 8 ≤ q)
    (hN : N ≤ 36 * W ^ (2 * B + 6)) :
    W ^ (-(D + 1)) + N * (Cq * W ^ (-(q : ℝ))) ≤ W ^ (-D) := by
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have h1 : N * (Cq * W ^ (-(q : ℝ))) ≤ W ^ (-(D + 1)) := by
    calc N * (Cq * W ^ (-(q : ℝ))) ≤ 36 * W ^ (2 * B + 6) * (Cq * W ^ (-(q : ℝ))) :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = (36 * Cq) * (W ^ (2 * B + 6) * W ^ (-(q : ℝ))) := by ring
      _ ≤ W * (W ^ (2 * B + 6) * W ^ (-(q : ℝ))) :=
          mul_le_mul_of_nonneg_right hWC (by positivity)
      _ = W ^ (1 + (2 * B + 6) + -(q : ℝ)) := by
          rw [Real.rpow_add hW0 (1 + (2 * B + 6)), Real.rpow_add hW0 1, Real.rpow_one]; ring
      _ ≤ W ^ (-(D + 1)) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have h2 : 2 * W ^ (-(D + 1)) ≤ W ^ (-D) := by
    have e : W ^ (-D) = W * W ^ (-(D + 1)) := by
      rw [show -D = 1 + -(D + 1) by ring, Real.rpow_add hW0, Real.rpow_one]
    rw [e]
    exact mul_le_mul_of_nonneg_right hW (by positivity)
  linarith

/-! ### Scales and the anchor on the range of Lemma 5.6 [fo:prop:inputs] -/

private lemma lemma46_gammaG {g : ℝ} (hg : 1 ≤ g) : gammaG g = (g ^ 2)⁻¹ := by
  unfold gammaG; rw [max_eq_right hg]

private lemma lemma46_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold gammaG
  positivity

/-- `ℓ_u ≥ g²` for `g ≥ 1`, `u ≤ 1/2` and `L ≥ g²` ((5.18) [fo:eq:scale]). -/
private lemma lemma46_ell_ge (p : FlowPt) (hg : 1 ≤ p.g) (hu0 : 0 ≤ p.u) (hu1 : p.u ≤ 1 / 2)
    (hL : p.g ^ 2 ≤ p.L) : p.g ^ 2 ≤ flowEll p := by
  unfold flowEll ellProp
  refine le_min hL ?_
  rw [lemma46_gammaG hg]
  have hg0 : 0 < p.g := by linarith
  have hin : 0 < (p.g ^ 2)⁻¹ * (1 - p.u) := by
    have : 0 < 1 - p.u := by linarith
    positivity
  set s : ℝ := Real.sqrt ((p.g ^ 2)⁻¹ * (1 - p.u)) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hin
  have hss : s ^ 2 = (p.g ^ 2)⁻¹ * (1 - p.u) := Real.sq_sqrt hin.le
  have hgs : p.g * s ≤ 1 := by
    have h1 : (p.g * s) ^ 2 ≤ 1 := by
      rw [mul_pow, hss]
      have : p.g ^ 2 * ((p.g ^ 2)⁻¹ * (1 - p.u)) = 1 - p.u := by field_simp
      rw [this]
      linarith
    nlinarith [mul_pos hg0 hs0]
  have : p.g ^ 2 ≤ p.g / s := by
    rw [le_div_iff₀ hs0]
    nlinarith
  linarith

/-- `ζ_u ≥ (2W)⁻¹` for `g ≥ 1`, `u ∈ [0, 1/2]`, `L ≥ 1` ((5.18) [fo:eq:scale]). -/
private lemma lemma46_zeta_lower (W : ℕ) (hW : 1 ≤ W) (p : FlowPt) (hg : 1 ≤ p.g)
    (hu0 : 0 ≤ p.u) (hu1 : p.u ≤ 1 / 2) (hL : 1 ≤ p.L) : ((2 : ℝ) * W)⁻¹ ≤ flowZeta W p := by
  unfold flowZeta zetaProp ellProp
  rw [lemma46_gammaG hg]
  have hg0 : 0 < p.g := by linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hL1 : (1 : ℝ) ≤ p.L := by exact_mod_cast hL
  set s : ℝ := Real.sqrt ((p.g ^ 2)⁻¹ * (1 - p.u)) with hs
  have hin : 0 < (p.g ^ 2)⁻¹ * (1 - p.u) := by
    have : 0 < 1 - p.u := by linarith
    positivity
  have hs0 : 0 < s := Real.sqrt_pos.2 hin
  have hss : s ^ 2 = (p.g ^ 2)⁻¹ * (1 - p.u) := Real.sq_sqrt hin.le
  have hs2 : s ^ 2 ≤ 1 := by
    rw [hss]
    have : (p.g ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hg)
    nlinarith
  have hgs : p.g * s ≤ 1 := by
    have h1 : (p.g * s) ^ 2 ≤ 1 := by
      rw [mul_pow, hss]
      have : p.g ^ 2 * ((p.g ^ 2)⁻¹ * (1 - p.u)) = 1 - p.u := by field_simp
      rw [this]; linarith
    nlinarith [mul_pos hg0 hs0]
  set ℓ : ℝ := min (p.L : ℝ) (1 + p.g / s) with hℓ
  have hℓ0 : 0 < ℓ := lt_min (by linarith) (by positivity)
  have hℓ1 : ℓ ≤ 1 + p.g / s := min_le_right _ _
  have hP : ℓ * (1 - p.u) * (p.g ^ 2)⁻¹ ≤ 2 := by
    calc ℓ * (1 - p.u) * (p.g ^ 2)⁻¹ = ℓ * s ^ 2 := by rw [hss]; ring
      _ ≤ (1 + p.g / s) * s ^ 2 := by gcongr
      _ = s ^ 2 + p.g * s := by field_simp
      _ ≤ 2 := by linarith
  have hP0 : 0 < ℓ * (1 - p.u) * (p.g ^ 2)⁻¹ := by
    have : 0 < 1 - p.u := by linarith
    positivity
  have e : (W : ℝ) * ℓ * (1 - p.u) * (p.g ^ 2)⁻¹ = W * (ℓ * (1 - p.u) * (p.g ^ 2)⁻¹) := by ring
  rw [e]
  refine inv_anti₀ (by positivity) ?_
  nlinarith

/-- On the range of Lemma 5.6 [fo:prop:inputs], for `W` large: `g ≥ 1`, `L ≥ R g² log W`,
`L ≥ R g²`, `L ≥ 3`, and the anchor `m = m_{g,L}(E)` is a root with `|m| ≤ C`, `Im m ≥ C⁻¹`,
`C` depending on `κ` only. -/
private lemma lemma46_pt (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ₀ C : ℝ, 1 ≤ Cκ₀ ∧ 1 ≤ C ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ,
      Tendsto ρ atTop atTop → ∀ R : ℝ, ∀ᶠ W : ℕ in atTop, ∀ CV : ℝ,
        ∀ p ∈ initLarge κ Cκ CV ρ W, 1 ≤ p.g ∧ R * p.g ^ 2 * Real.log W ≤ p.L ∧
          R * p.g ^ 2 ≤ p.L ∧ 3 ≤ p.L ∧
          IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ∧
          ‖mRoot p.g p.L p.E‖ ≤ C ∧ C⁻¹ ≤ (mRoot p.g p.L p.E).im := by
  obtain ⟨Cκl, Rl, cl, Cl, hCκl, hRl, hcl, hCl, Hl⟩ := large_periodic_comparison κ hκ hκ2
  refine ⟨Cκl, max 1 Cl, hCκl, le_max_left _ _, fun Cκ hCκ ρ hρ R => ?_⟩
  set R' : ℝ := max (max R Rl) 3 with hR'
  filter_upwards [hρ.eventually_ge_atTop R',
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with W hρW hlog CV p hp
  obtain ⟨hgC, hE, hLlog, -, -, -⟩ := hp
  have hgl : Cκl ≤ p.g := hCκ.trans hgC
  have hg1 : 1 ≤ p.g := hCκl.trans hgl
  have hg0 : 0 < p.g := by linarith
  have hgg : 1 ≤ p.g ^ 2 := one_le_pow₀ hg1
  have hR3 : (3 : ℝ) ≤ R' := le_max_right _ _
  have hρ0 : 0 ≤ ρ W := by linarith
  have hlog' : (1 : ℝ) ≤ Real.log W := hlog
  have hLR : R' * p.g ^ 2 * Real.log W ≤ p.L :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρW (by positivity))
      (by linarith)) hLlog
  have hLR' : R' * p.g ^ 2 ≤ p.L := by
    have h1 : 0 ≤ R' * p.g ^ 2 := by positivity
    exact le_trans (le_mul_of_one_le_right h1 hlog') hLR
  have hRR : R ≤ R' := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRl : Rl ≤ R' := le_trans (le_max_right _ _) (le_max_left _ _)
  have hRlL : Rl * p.g ^ 2 ≤ p.L :=
    le_trans (mul_le_mul_of_nonneg_right hRl (by positivity)) hLR'
  have hL3 : 3 ≤ p.L := by
    have : (3 : ℝ) ≤ p.L := by nlinarith
    exact_mod_cast this
  obtain ⟨m, -, hroot, -, hmim, hmC, -⟩ := Hl p.g hgl p.L hRlL p.E hE
  have hb0 : 0 ≤ hopB p.g := by
    unfold hopB; rw [max_eq_right hg1, div_self hg0.ne']; norm_num
  have hmR : mRoot p.g p.L p.E = m :=
    (mRootV_spec (hopB p.g) (gammaG p.g) hb0 (lemma46_gammaG_pos _) p.L hL3
      (p.E : ℂ) (by simp)).2 m hroot
  rw [hmR]
  refine ⟨hg1, le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRR
    (by positivity)) (by linarith)) hLR,
    le_trans (mul_le_mul_of_nonneg_right hRR (by positivity)) hLR', hL3, hroot,
    hmC.trans (le_max_right _ _), le_trans (inv_anti₀ hCl (le_max_right _ _)) hmim⟩

/-- Real multiples of the GUE blocks are Hermitian. -/
private lemma lemma46_herm (W L : ℕ) (ω : Ω W L) (b : ℝ) (r : Fin L) :
    (((b : ℝ) : ℂ) • gueBlock W L ω r).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (gueBlock_isHermitian W L ω r).eq, Complex.star_def,
    Complex.conj_ofReal]

private lemma lemma46_isAnchor_start (n : ℕ) {L : ℕ} (a : Fin L) : IsAnchor n (cellStart n a) := by
  left
  simp [cellStart]

private lemma lemma46_isAnchor_prev (n : ℕ) {L : ℕ} (a : Fin L) : IsAnchor n (cellPrev n a) := by
  right
  unfold cellPrev
  rw [Equiv.apply_symm_apply]
  simp [cellStart]

/-! ### Far blocks -/

-- the proof treats both cases of the cell partition in one declaration
set_option maxHeartbeats 1000000 in
/-- Far blocks at the characteristic point beyond a logarithmic distance: for every `A > 0` there
is `K > 0` such that `max_{d(a,b) ≥ K g² log W} ‖G_{ab}(z_u)‖ ≤ W^{-A}` with probability at least
`1 - W^{-D}` ((7.9) [uvc:eq:seed-tails] at the anchor pairs and Proposition 7.4
[uvc:prop:green], or all pairs when `g² < W^B`). -/
private theorem lemma46_farCore (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 < K ∧ ∀ D : ℝ, 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        ∀ p ∈ initLarge κ Cκ CV ρ W,
          μ W p.L {ω | ∃ a b : Fin p.L, K * p.g ^ 2 * Real.log W ≤ cycDist a b ∧
            (W : ℝ) ^ (-A) < ‖blockOf (flowG W p ω) a b‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  obtain ⟨Cκp, C, hCκp, hC1, Hp⟩ := lemma46_pt κ hκ hκ2
  obtain ⟨Cκχ, Cχ, hCκχ, hCχ, Hχ⟩ := char_large κ C hκ hκ2 hC1
  have hk : 0 < κ / 2 := by linarith
  have hk2 : κ / 2 < 2 := by linarith
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ, c₀ = (2 * Cχ)⁻¹ := ⟨_, rfl⟩
  have hc₀ : 0 < c₀ := by rw [hc₀def]; have : (0 : ℝ) < Cχ := by linarith
                          positivity
  have hc₀C : c₀ ≤ Cχ := by
    rw [hc₀def]
    calc (2 * Cχ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      _ ≤ Cχ := hCχ
  obtain ⟨Cκs, c, hCκs, hc, Hs⟩ := seed_tails (κ / 2) c₀ Cχ hk hk2 hc₀ hc₀C
  obtain ⟨Ct, hCt, Ht⟩ := cellClose_perturb (κ / 2) hk hk2
  obtain ⟨Cg, hCg, Hg⟩ := green_interp (κ / 2) hk hk2
  refine ⟨max (max Cκp Cκχ) Cκs, le_trans hCκp (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun Cκ hCκ ρ hρ A hA => ?_⟩
  have hCκp' : Cκp ≤ Cκ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCκ
  have hCκχ' : Cκχ ≤ Cκ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCκ
  have hCκs' : Cκs ≤ Cκ := le_trans (le_max_right _ _) hCκ
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 2 * (A + 2) / c := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; positivity
  refine ⟨K, hK0, fun D hD => ?_⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 4 * (A + 2) := ⟨_, rfl⟩
  have hB2 : 2 < B := by rw [hBdef]; linarith
  have hB4 : B / 4 = A + 2 := by rw [hBdef]; ring
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = ⌈2 * B + D + 8⌉₊ := ⟨_, rfl⟩
  have hq : 2 * B + D + 8 ≤ (q : ℝ) := by rw [hqdef]; exact Nat.le_ceil _
  have hq1 : 1 ≤ q := by
    have : (1 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  obtain ⟨Cq, hCq, Hq⟩ := Hs q hq1
  obtain ⟨Wc, HWc⟩ := cells_prefix (κ / 2) B 3 (D + 1) hk hk2 hB2 (by norm_num) (by linarith)
  obtain ⟨Kt, hKtdef⟩ : ∃ Kt : ℝ, Kt = (4 / (κ / 2)) ^ 2 + 4 * Cg := ⟨_, rfl⟩
  have hev : ∀ᶠ W : ℕ in atTop, (∀ CV' : ℝ, ∀ p ∈ initLarge κ Cκ CV' ρ W, 1 ≤ p.g ∧
      4 * p.g ^ 2 * Real.log W ≤ p.L ∧ 4 * p.g ^ 2 ≤ p.L ∧ 3 ≤ p.L ∧
      IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ∧
      ‖mRoot p.g p.L p.E‖ ≤ C ∧ C⁻¹ ≤ (mRoot p.g p.L p.E).im) ∧
      4 * q ≤ W ∧ Wc ≤ W ∧ 2 ≤ W ∧ CV ≤ (W : ℝ) ∧ 36 * Cq ≤ (W : ℝ) ∧ Kt ≤ (W : ℝ) ∧
      Ct * Cχ ≤ (W : ℝ) ^ (3 * B / 4) ∧ Cχ ≤ (W : ℝ) ^ B ∧ 4 ≤ K * Real.log W := by
    have hrp : ∀ {a : ℝ}, 0 < a → ∀ c' : ℝ, ∀ᶠ W : ℕ in atTop, c' ≤ (W : ℝ) ^ a :=
      fun ha c' => ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c'
    have hnat : ∀ c' : ℝ, ∀ᶠ W : ℕ in atTop, c' ≤ (W : ℝ) :=
      fun c' => tendsto_natCast_atTop_atTop.eventually_ge_atTop c'
    filter_upwards [Hp Cκ hCκp' ρ hρ 4, eventually_ge_atTop (4 * q), eventually_ge_atTop Wc,
      eventually_ge_atTop 2, hnat CV, hnat (36 * Cq), hnat Kt,
      hrp (by positivity : (0 : ℝ) < 3 * B / 4) (Ct * Cχ), hrp (by positivity : (0 : ℝ) < B) Cχ,
      (Tendsto.const_mul_atTop hK0
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 4]
      with W h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨W₀, HW₀⟩ := eventually_atTop.1 hev
  refine ⟨W₀, fun W hW p hp => ?_⟩
  obtain ⟨hpt, h4q, hWc, hW2, hWCV, hWCq, hWKt, hWCt, hWCχ, hKlog⟩ := HW₀ W hW
  obtain ⟨hg1, -, h4L, hL3, -, hmC, hmim⟩ := hpt CV p hp
  have hp' := hp
  obtain ⟨hgC, hE, -, hLV, hu0, hu1⟩ := hp'
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW2r : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  have hg0 : 0 < p.g := by linarith
  have hgg : 0 < p.g ^ 2 := by positivity
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1r
  have hgχ : Cκχ ≤ p.g := hCκχ'.trans hgC
  have hgs : Cκs ≤ p.g := hCκs'.trans hgC
  obtain ⟨hre, -, hη0, hηC, hgη⟩ := Hχ p.g hgχ p.E (mRoot p.g p.L p.E) hE hmC hmim p.u hu0
    (by linarith)
  obtain ⟨E', hE'⟩ : ∃ E' : ℝ, E' = (zChar p.g p.E (mRoot p.g p.L p.E) p.u).re := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = etaChar p.g (mRoot p.g p.L p.E) p.u := ⟨_, rfl⟩
  rw [← hE'] at hre
  rw [← hη] at hη0 hηC hgη
  have hηlo : c₀ / p.g ^ 2 ≤ η := by
    rw [div_le_iff₀ hgg]
    have h1 : c₀ ≤ (1 - p.u) / Cχ := by
      rw [hc₀def, mul_inv, div_eq_mul_inv]
      have : (2 : ℝ)⁻¹ ≤ 1 - p.u := by linarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    nlinarith
  have hzu : zChar p.g p.E (mRoot p.g p.L p.E) p.u = (E' : ℂ) + (η : ℂ) * Complex.I := by
    rw [hE', hη, ← im_zChar]; exact (Complex.re_add_im _).symm
  have hG : ∀ ω, flowG W p ω =
      resolventMat (flowH p.g W p.L p.u ω) ((E' : ℂ) + (η : ℂ) * Complex.I) := by
    intro ω; unfold flowG; rw [hzu]
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (W : ℝ) ^ (-(A + 1)) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; exact Real.rpow_pos_of_pos hW0 _
  have ht1 : t ≤ 1 := by
    rw [htdef]; exact Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith)
  have htA : t ≤ (W : ℝ) ^ (-A) := by
    rw [htdef]; exact Real.rpow_le_rpow_of_exponent_le hW1r (by linarith)
  have htW : (W : ℝ) * t = (W : ℝ) ^ (-A) := by
    rw [htdef, show -A = 1 + -(A + 1) by ring, Real.rpow_add hW0, Real.rpow_one]
  -- one pair at distance `≥ (K/2) g² log W`
  have hPB : ∀ α β : Fin p.L, K / 2 * p.g ^ 2 * Real.log W ≤ cycDist α β →
      μ W p.L {ω | t < ‖blockOf (flowG W p ω) α β‖} ≤
        ENNReal.ofReal (Cq * (W : ℝ) ^ (-(q : ℝ))) := by
    intro α β hd
    obtain ⟨hint, hmom⟩ := Hq W h4q p.g hgs p.L h4L E' η p.u hre hηlo hηC hu0 (by linarith) α β
    simp only [hG]
    refine (lemma46_markov _ (fun ω => ‖blockOf (resolventMat (flowH p.g W p.L p.u ω)
      ((E' : ℂ) + (η : ℂ) * Complex.I)) α β‖) q t _ ht0 (fun ω => norm_nonneg _) hint
      hmom).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [htdef]
    exact lemma46_tail_rate (W : ℝ) p.g c A Cq (cycDist α β) q hW1r hgg hc hCq.le
      (by rw [hKdef] at hd; exact hd)
  have hKd : ∀ a b : Fin p.L, K * p.g ^ 2 * Real.log W ≤ cycDist a b →
      K / 2 * p.g ^ 2 * Real.log W ≤ cycDist a b := fun a b h => by
    have : 0 ≤ K / 2 * p.g ^ 2 * Real.log W := by positivity
    linarith
  have hCqW : 0 ≤ Cq * (W : ℝ) ^ (-(q : ℝ)) := by positivity
  by_cases hbig : (W : ℝ) ^ B ≤ p.g ^ 2
  swap
  · -- `g² < W^B`: all pairs
    set S : Finset (Fin p.L × Fin p.L) :=
      Finset.univ.filter (fun ab => K / 2 * p.g ^ 2 * Real.log W ≤ cycDist ab.1 ab.2) with hS
    have hsub : {ω | ∃ a b : Fin p.L, K * p.g ^ 2 * Real.log W ≤ cycDist a b ∧
        (W : ℝ) ^ (-A) < ‖blockOf (flowG W p ω) a b‖} ⊆
        ⋃ ab ∈ S, {ω | t < ‖blockOf (flowG W p ω) ab.1 ab.2‖} := by
      rintro ω ⟨a, b, hd, hab⟩
      refine Set.mem_iUnion₂.2 ⟨(a, b), ?_, lt_of_le_of_lt htA hab⟩
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hKd a b hd
    have hLW : (p.L : ℝ) ≤ (W : ℝ) ^ (B + 3) := by
      have e : (W : ℝ) ^ (B + 3) = (W : ℝ) * (W : ℝ) ^ B * (W : ℝ) ^ 2 := by
        rw [Real.rpow_add hW0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
      rw [e]
      calc (p.L : ℝ) ≤ CV * p.g ^ 2 * (W : ℝ) ^ 2 := hLV
        _ ≤ (W : ℝ) * (W : ℝ) ^ B * (W : ℝ) ^ 2 := by
            gcongr
            exact (not_le.mp hbig).le
    have hcard : (S.card : ℝ) ≤ 36 * (W : ℝ) ^ (2 * B + 6) := by
      have h1 : (S.card : ℝ) ≤ (p.L : ℝ) * p.L := by
        have : S.card ≤ p.L * p.L := by
          calc S.card ≤ (Finset.univ : Finset (Fin p.L × Fin p.L)).card := Finset.card_filter_le _ _
            _ = p.L * p.L := by simp
        exact_mod_cast this
      have e : (W : ℝ) ^ (2 * B + 6) = (W : ℝ) ^ (B + 3) * (W : ℝ) ^ (B + 3) := by
        rw [← Real.rpow_add hW0]; ring_nf
      have h0 : (0 : ℝ) ≤ (W : ℝ) ^ (2 * B + 6) := by positivity
      calc (S.card : ℝ) ≤ (p.L : ℝ) * p.L := h1
        _ ≤ (W : ℝ) ^ (B + 3) * (W : ℝ) ^ (B + 3) :=
            mul_le_mul hLW hLW (by positivity) (by positivity)
        _ = (W : ℝ) ^ (2 * B + 6) := e.symm
        _ ≤ 36 * (W : ℝ) ^ (2 * B + 6) := by linarith
    calc _ ≤ μ W p.L (⋃ ab ∈ S, {ω | t < ‖blockOf (flowG W p ω) ab.1 ab.2‖}) := measure_mono hsub
      _ ≤ ∑ ab ∈ S, μ W p.L {ω | t < ‖blockOf (flowG W p ω) ab.1 ab.2‖} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ ab ∈ S, ENNReal.ofReal (Cq * (W : ℝ) ^ (-(q : ℝ))) := by
          refine Finset.sum_le_sum fun ab hab => hPB ab.1 ab.2 ?_
          simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hab
          exact hab
      _ = ENNReal.ofReal (S.card * (Cq * (W : ℝ) ^ (-(q : ℝ)))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := lemma46_count (W : ℝ) D B Cq S.card q hW2r hCq.le hWCq hq hcard
          have h0 : (0 : ℝ) ≤ (W : ℝ) ^ (-(D + 1)) := by positivity
          linarith
  -- `g² ≥ W^B`: the anchor pairs
  obtain ⟨n, hndef⟩ : ∃ n : ℕ, n = cellLen p.g W B := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by rw [hndef]; exact le_max_left _ _
  have hnb : (n : ℝ) ≤ p.g ^ 2 * (W : ℝ) ^ (-B) := by
    rw [hndef]; exact (cellLen_bounds p.g B W hW1 hbig).2
  have hWB : (W : ℝ) ^ (-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith)
  have hng : (n : ℝ) ≤ p.g ^ 2 := hnb.trans (mul_le_of_le_one_right hgg.le hWB)
  have hL3' : (p.L : ℝ) ≤ p.g ^ 2 * (W : ℝ) ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (p.L : ℝ) ≤ CV * p.g ^ 2 * (W : ℝ) ^ 2 := hLV
      _ ≤ (W : ℝ) * p.g ^ 2 * (W : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = p.u * gammaG p.g := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := by rw [hβdef]; exact mul_nonneg hu0 (lemma46_gammaG_pos _).le
  have hβg : β * p.g ^ 2 ≤ 1 := by
    rw [hβdef, lemma46_gammaG hg1, mul_assoc, inv_mul_cancel₀ hgg.ne', mul_one]
    linarith
  have hcell := HWc W hWc p.g p.L E' β hbig hL3' hre hβ0 hβg
  rw [← hndef] at hcell
  set V : Ω W p.L → Fin p.L → Matrix (Fin W) (Fin W) ℂ :=
    fun ω r => ((Real.sqrt β : ℝ) : ℂ) • gueBlock W p.L ω r with hV
  set S : Finset (Fin p.L × Fin p.L) :=
    ((Finset.univ.filter fun α : Fin p.L => IsAnchor n α) ×ˢ
      (Finset.univ.filter fun α : Fin p.L => IsAnchor n α)).filter
        (fun ab => K / 2 * p.g ^ 2 * Real.log W ≤ cycDist ab.1 ab.2) with hS
  have hcard : (S.card : ℝ) ≤ 36 * (W : ℝ) ^ (2 * B + 6) := by
    have hc := (card_cells_le_pow p.g B 3 W p.L hW1 (by linarith) (by norm_num) hbig hL3').2
    rw [← hndef] at hc
    have h1 : S.card ≤ (Finset.univ.filter fun α : Fin p.L => IsAnchor n α).card *
        (Finset.univ.filter fun α : Fin p.L => IsAnchor n α).card := by
      rw [hS, ← Finset.card_product]
      exact Finset.card_filter_le _ _
    have h1' : (S.card : ℝ) ≤ ((Finset.univ.filter fun α : Fin p.L => IsAnchor n α).card : ℝ) *
        ((Finset.univ.filter fun α : Fin p.L => IsAnchor n α).card : ℝ) := by exact_mod_cast h1
    have e : (W : ℝ) ^ (2 * B + 6) = (W : ℝ) ^ (B + 3) * (W : ℝ) ^ (B + 3) := by
      rw [← Real.rpow_add hW0]; ring_nf
    rw [e]
    calc (S.card : ℝ) ≤ _ := h1'
      _ ≤ (6 * (W : ℝ) ^ (B + 3)) * (6 * (W : ℝ) ^ (B + 3)) :=
          mul_le_mul hc hc (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) hc)
      _ = 36 * ((W : ℝ) ^ (B + 3) * (W : ℝ) ^ (B + 3)) := by ring
  -- the scales of the cell argument
  have hWB4 : (W : ℝ) ^ (-(B / 4)) ≤ 1 / 2 := by
    have h1 : (W : ℝ) ^ (1 : ℝ) ≤ (W : ℝ) ^ (B / 4) :=
      Real.rpow_le_rpow_of_exponent_le hW1r (by linarith)
    rw [Real.rpow_one] at h1
    rw [Real.rpow_neg hW0.le, inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hWB40 : 0 < (W : ℝ) ^ (-(B / 4)) := Real.rpow_pos_of_pos hW0 _
  have hnη : (n : ℝ) * η ≤ Cχ * (W : ℝ) ^ (-B) := by
    calc (n : ℝ) * η ≤ p.g ^ 2 * (W : ℝ) ^ (-B) * (Cχ / p.g ^ 2) :=
          mul_le_mul hnb hηC hη0.le (by positivity)
      _ = Cχ * (W : ℝ) ^ (-B) := by field_simp
  have hnη1 : (n : ℝ) * η ≤ 1 := by
    refine hnη.trans ?_
    calc Cχ * (W : ℝ) ^ (-B) ≤ (W : ℝ) ^ B * (W : ℝ) ^ (-B) :=
          mul_le_mul_of_nonneg_right hWCχ (by positivity)
      _ = 1 := by rw [← Real.rpow_add hW0, add_neg_cancel, Real.rpow_zero]
  have hCtn : Ct * n * η ≤ (W : ℝ) ^ (-(B / 4)) := by
    calc Ct * n * η = Ct * ((n : ℝ) * η) := by ring
      _ ≤ Ct * (Cχ * (W : ℝ) ^ (-B)) := mul_le_mul_of_nonneg_left hnη hCt.le
      _ = (Ct * Cχ) * (W : ℝ) ^ (-B) := by ring
      _ ≤ (W : ℝ) ^ (3 * B / 4) * (W : ℝ) ^ (-B) :=
          mul_le_mul_of_nonneg_right hWCt (by positivity)
      _ = (W : ℝ) ^ (-(B / 4)) := by rw [← Real.rpow_add hW0]; ring_nf
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 2 * (W : ℝ) ^ (-(B / 4)) := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by rw [hedef]; positivity
  have he1 : e ≤ 1 := by rw [hedef]; linarith
  set z : ℂ := zChar p.g p.E (mRoot p.g p.L p.E) p.u with hz
  have hzE : ‖z - (E' : ℂ)‖ = η := by
    rw [hzu, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hη0.le]
  have hzE' : ‖(starRingEnd ℂ) z - (E' : ℂ)‖ = η := by
    rw [show (starRingEnd ℂ) z - (E' : ℂ) = (starRingEnd ℂ) (z - (E' : ℂ)) by
      rw [map_sub, Complex.conj_ofReal], Complex.norm_conj, hzE]
  have hzim : z.im ≠ 0 := by
    rw [hz, im_zChar, ← hη]; exact hη0.ne'
  have hsub : {ω | ∃ a b : Fin p.L, K * p.g ^ 2 * Real.log W ≤ cycDist a b ∧
      (W : ℝ) ^ (-A) < ‖blockOf (flowG W p ω) a b‖} ⊆
      {ω | ¬ CellClose n E' (E' : ℂ) (V ω) ((W : ℝ) ^ (-(B / 4)))} ∪
        ⋃ ab ∈ S, {ω | t < ‖blockOf (flowG W p ω) ab.1 ab.2‖} := by
    rintro ω ⟨a, b, hd, hab⟩
    by_contra hcon
    have hcl : CellClose n E' (E' : ℂ) (V ω) ((W : ℝ) ^ (-(B / 4))) := by
      by_contra h
      exact hcon (Or.inl h)
    have hanc : ∀ ab ∈ S, ‖blockOf (flowG W p ω) ab.1 ab.2‖ ≤ t := fun ab hab' => by
      by_contra h
      exact hcon (Or.inr (Set.mem_iUnion₂.2 ⟨ab, hab', not_le.mp h⟩))
    set Gr := resolventMat (cycleAdj p.L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) +
      blockDiagOp (V ω)) z with hGr
    have hGeq : flowG W p ω = Gr := by
      unfold flowG
      rw [flowH_cycle _ hg1, ← hβdef]
    rw [hGeq] at hab hanc
    -- the anchor pairs of the cells of `a` and `b` are far
    have hfar : ∀ α β' : Fin p.L, (α = cellStart n a ∨ α = cellPrev n a) →
        (β' = cellStart n b ∨ β' = cellPrev n b) → ‖blockOf Gr α β'‖ ≤ t := by
      intro α β' hα hβ'
      refine hanc (α, β') ?_
      simp only [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rcases hα with rfl | rfl
        · exact lemma46_isAnchor_start n a
        · exact lemma46_isAnchor_prev n a
      · rcases hβ' with rfl | rfl
        · exact lemma46_isAnchor_start n b
        · exact lemma46_isAnchor_prev n b
      · have h1 := lemma46_anchor_far n hn1 a b α β' hα hβ'
        have h2 : (cycDist a b : ℝ) ≤ cycDist α β' + 2 * n := by exact_mod_cast h1
        have h3 : 2 * (n : ℝ) ≤ K / 2 * p.g ^ 2 * Real.log W := by
          have e1 : K / 2 * p.g ^ 2 * Real.log W = (K * Real.log W) * p.g ^ 2 / 2 := by ring
          have e2 := mul_le_mul_of_nonneg_right hKlog hgg.le
          rw [e1]
          linarith
        linarith
    have hAN : anchorNorm n Gr a b ≤ t := by
      unfold anchorNorm
      exact max_le
        (max_le (hfar _ _ (Or.inl rfl) (Or.inl rfl)) (hfar _ _ (Or.inl rfl) (Or.inr rfl)))
        (max_le (hfar _ _ (Or.inr rfl) (Or.inl rfl)) (hfar _ _ (Or.inr rfl) (Or.inr rfl)))
    have hD0 : cellD n E' a b = 0 := by
      refine lemma46_cellD_far n hn1 E' a b ?_
      have h1 : 3 * (n : ℝ) ≤ cycDist a b := by
        have e1 : K * p.g ^ 2 * Real.log W = (K * Real.log W) * p.g ^ 2 := by ring
        have e2 := mul_le_mul_of_nonneg_right hKlog hgg.le
        linarith
      exact_mod_cast h1
    have hVh : ∀ r, (V ω r).IsHermitian := fun r => lemma46_herm W p.L ω _ r
    have hclz : CellClose n E' z (V ω) e := by
      have h := Ht W p.L n E' ((W : ℝ) ^ (-(B / 4))) z (V ω) hre hWB40.le (by linarith)
        (by rw [hzE]; exact hnη1) hcl
      intro b' j h1 h2
      refine (h b' j h1 h2).trans ?_
      rw [hzE, hedef]; linarith
    have hclz' : CellClose n E' ((starRingEnd ℂ) z) (V ω) e := by
      have h := Ht W p.L n E' ((W : ℝ) ^ (-(B / 4))) ((starRingEnd ℂ) z) (V ω) hre hWB40.le
        (by linarith) (by rw [hzE']; exact hnη1) hcl
      intro b' j h1 h2
      refine (h b' j h1 h2).trans ?_
      rw [hzE', hedef]; linarith
    have hGi := Hg W p.L n E' e z (V ω) hL3 hn1 hre hVh hzim he0 he1 hclz hclz' a b
    have hblk := lemma46_far_block hk hk2 hre n Gr Cg e t hCg.le he0 ht0.le ht1 a b hD0 hAN hGi
    have hfin : (4 / (κ / 2)) ^ 2 * t + 2 * Cg * e ≤ (W : ℝ) ^ (-A) := by
      have h1 : (W : ℝ) ^ (-(B / 4)) ≤ t := by
        rw [htdef, hB4]; exact Real.rpow_le_rpow_of_exponent_le hW1r (by linarith)
      have h2 : 2 * Cg * e ≤ 4 * Cg * t := by
        have h3 : e ≤ 2 * t := by rw [hedef]; linarith
        have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * Cg)
        linarith
      have e3 : Kt * t = (4 / (κ / 2)) ^ 2 * t + 4 * Cg * t := by rw [hKtdef]; ring
      calc (4 / (κ / 2)) ^ 2 * t + 2 * Cg * e ≤ Kt * t := by rw [e3]; linarith
        _ ≤ (W : ℝ) * t := mul_le_mul_of_nonneg_right hWKt ht0.le
        _ = _ := htW
    linarith
  calc _ ≤ μ W p.L ({ω | ¬ CellClose n E' (E' : ℂ) (V ω) ((W : ℝ) ^ (-(B / 4)))} ∪
        ⋃ ab ∈ S, {ω | t < ‖blockOf (flowG W p ω) ab.1 ab.2‖}) := measure_mono hsub
    _ ≤ μ W p.L {ω | ¬ CellClose n E' (E' : ℂ) (V ω) ((W : ℝ) ^ (-(B / 4)))} +
        ∑ ab ∈ S, μ W p.L {ω | t < ‖blockOf (flowG W p ω) ab.1 ab.2‖} :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) +
        ∑ ab ∈ S, ENNReal.ofReal (Cq * (W : ℝ) ^ (-(q : ℝ))) := by
        refine add_le_add hcell (Finset.sum_le_sum fun ab hab => hPB ab.1 ab.2 ?_)
        simp only [hS, Finset.mem_filter] at hab
        exact hab.2
    _ = ENNReal.ofReal ((W : ℝ) ^ (-(D + 1)) + S.card * (Cq * (W : ℝ) ^ (-(q : ℝ)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add
            (Real.rpow_nonneg hW0.le _) (mul_nonneg (Nat.cast_nonneg _) hCqW)]
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) :=
        ENNReal.ofReal_le_ofReal (lemma46_count (W : ℝ) D B Cq S.card q hW2r hCq.le hWCq hq hcard)

/-! ### The envelope of a loop by the norms of its edges -/

section Envelope

variable {W L : ℕ}

/-- An entry of a matrix is at most its operator norm. -/
private lemma lemma46_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
  have hn : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [hn, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  convert this using 2
  simp

/-- The unnormalized projection onto block `x`. -/
private def lemma46P (W L : ℕ) (x : Fin L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.diagonal fun p => if p.1 = x then 1 else 0

/-- The inclusion of `ℂ^W` as block `x` of `ℂ^L ⊗ ℂ^W`. -/
private def lemma46J (W L : ℕ) (x : Fin L) : Matrix (Fin L × Fin W) (Fin W) ℂ :=
  Matrix.of fun p α => if p = (x, α) then 1 else 0

private lemma lemma46_blockE_eq (a : Fin L) :
    blockE W L a = (W : ℂ)⁻¹ • lemma46P W L a := by
  ext p q
  by_cases h : p = q
  · subst h
    by_cases h1 : p.1 = a <;> simp [blockE, lemma46P, h1]
  · simp [blockE, lemma46P, h]

private lemma lemma46P_mul_self (x : Fin L) : lemma46P W L x * lemma46P W L x = lemma46P W L x := by
  unfold lemma46P
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  by_cases h : p.1 = x <;> simp [h]

private lemma lemma46P_conjTranspose (x : Fin L) : (lemma46P W L x)ᴴ = lemma46P W L x := by
  unfold lemma46P
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases h : p.1 = x <;> simp [h]

private lemma lemma46J_conjTranspose_mul (x : Fin L) :
    (lemma46J W L x)ᴴ * lemma46J W L x = 1 := by
  ext α β
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, lemma46J, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (x, α)]
  · by_cases h : α = β <;> simp [h]
  · intro p _ hp
    simp [hp]
  · simp

private lemma lemma46P_sandwich (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (x y : Fin L) :
    lemma46P W L x * A * lemma46P W L y =
      lemma46J W L x * blockOf A x y * (lemma46J W L y)ᴴ := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  simp only [lemma46P, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, lemma46J, blockOf, Matrix.of_apply, Matrix.conjTranspose_apply,
    Prod.mk.injEq]
  by_cases h1 : p1 = x <;> by_cases h2 : q1 = y <;> simp [h1, h2]

private lemma lemma46J_norm_le (x : Fin L) : ‖lemma46J W L x‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (lemma46J W L x)
  rw [lemma46J_conjTranspose_mul] at h
  have h1 : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp
  nlinarith [norm_nonneg (lemma46J W L x)]

private lemma lemma46_norm_sandwich_le (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x y : Fin L) : ‖lemma46P W L x * A * lemma46P W L y‖ ≤ ‖blockOf A x y‖ := by
  rw [lemma46P_sandwich]
  have h1 := Matrix.l2_opNorm_mul (lemma46J W L x * blockOf A x y) (lemma46J W L y)ᴴ
  have h2 := Matrix.l2_opNorm_mul (lemma46J W L x) (blockOf A x y)
  rw [Matrix.l2_opNorm_conjTranspose] at h1
  have hJx := lemma46J_norm_le (W := W) x
  have hJy := lemma46J_norm_le (W := W) y
  have hB := norm_nonneg (blockOf A x y)
  calc _ ≤ ‖lemma46J W L x * blockOf A x y‖ * ‖lemma46J W L y‖ := h1
    _ ≤ (‖lemma46J W L x‖ * ‖blockOf A x y‖) * ‖lemma46J W L y‖ := by gcongr
    _ ≤ 1 * ‖blockOf A x y‖ * 1 := by gcongr
    _ = ‖blockOf A x y‖ := by ring

private lemma lemma46_norm_P_le (x : Fin L) : ‖lemma46P W L x‖ ≤ 1 := by
  unfold lemma46P
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
  by_cases h : p.1 = x <;> simp [h]

/-- An edge of a loop with sign `s` is at most the larger of the blocks `G_{cd}`, `G_{dc}`. -/
private lemma lemma46_edge_le (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (Y : ℝ) (s : Bool)
    (c d : Fin L) (h1 : ‖blockOf G c d‖ ≤ Y) (h2 : ‖blockOf G d c‖ ≤ Y) :
    ‖lemma46P W L c * sgnMat G s * lemma46P W L d‖ ≤ Y := by
  cases s
  · have h := lemma46_norm_sandwich_le G d c
    have e : lemma46P W L c * sgnMat G false * lemma46P W L d =
        (lemma46P W L d * G * lemma46P W L c)ᴴ := by
      simp only [sgnMat, Bool.false_eq_true, ite_false, Matrix.conjTranspose_mul,
        lemma46P_conjTranspose, Matrix.mul_assoc]
    rw [e, Matrix.l2_opNorm_conjTranspose]
    exact h.trans h2
  · exact (lemma46_norm_sandwich_le G c d).trans h1

private lemma lemma46_prod_E : ∀ (n : ℕ) (S : Fin n → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x : Fin n → Fin L), (List.ofFn fun p => S p * blockE W L (x p)).prod =
      ((W : ℂ)⁻¹) ^ n • (List.ofFn fun p => S p * lemma46P W L (x p)).prod
  | 0, S, x => by simp
  | n + 1, S, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      lemma46_prod_E n (fun p => S p.succ) (fun p => x p.succ), lemma46_blockE_eq]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1

private lemma lemma46_idem_split {n : Type*} [Fintype n] (P0 S0 P1 R : Matrix n n ℂ)
    (h : P1 * P1 = P1) : P0 * (S0 * P1 * R) = (P0 * S0 * P1) * (P1 * R) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P1 P1 R, h]

/-- A chain of edges is at most the product of the edge bounds. -/
private lemma lemma46_chain_norm : ∀ (n : ℕ) (Y : Fin n → ℝ)
    (S : Fin n → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (x : Fin (n + 1) → Fin L),
    (∀ p, 0 ≤ Y p) →
    (∀ p : Fin n, ‖lemma46P W L (x p.castSucc) * S p * lemma46P W L (x p.succ)‖ ≤ Y p) →
    ‖lemma46P W L (x 0) * (List.ofFn fun p : Fin n => S p * lemma46P W L (x p.succ)).prod‖ ≤
      ∏ p, Y p
  | 0, Y, S, x, _, _ => by
    simpa using lemma46_norm_P_le (W := W) (x 0)
  | n + 1, Y, S, x, hY0, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    have ih := lemma46_chain_norm n (fun p => Y p.succ) (fun p => S p.succ) (fun p => x p.succ)
      (fun p => hY0 _) (fun p => by
        have := h p.succ
        change ‖lemma46P W L (x p.castSucc.succ) * S p.succ * lemma46P W L (x p.succ.succ)‖ ≤ _
        rw [Fin.succ_castSucc]
        exact this)
    rw [lemma46_idem_split _ _ _ _ (lemma46P_mul_self _)]
    have h0 := h 0
    rw [Fin.castSucc_zero] at h0
    calc _ ≤ ‖lemma46P W L (x 0) * S 0 * lemma46P W L (x (Fin.succ 0))‖ *
          ‖lemma46P W L (x (Fin.succ 0)) *
            (List.ofFn fun i : Fin n => S i.succ * lemma46P W L (x i.succ.succ)).prod‖ :=
          Matrix.l2_opNorm_mul _ _
      _ ≤ Y 0 * ∏ i : Fin n, Y i.succ :=
          mul_le_mul h0 ih (norm_nonneg _) (hY0 0)

/-- A product of factors `S_p P_{a_p}` absorbs the last projection on the right. -/
private lemma lemma46_prod_absorb (n : ℕ)
    (S : Fin (n + 1) → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a : Fin (n + 1) → Fin L) :
    (List.ofFn fun p => S p * lemma46P W L (a p)).prod * lemma46P W L (a (Fin.last n)) =
      (List.ofFn fun p => S p * lemma46P W L (a p)).prod := by
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
  simp only [Matrix.mul_assoc, lemma46P_mul_self]

/-- `|Tr(P_c M)| ≤ W ‖P_c M‖`. -/
private lemma lemma46_trace_P_le (c : Fin L) (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    ‖(lemma46P W L c * M).trace‖ ≤ W * ‖lemma46P W L c * M‖ := by
  rw [Matrix.trace]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ q, ‖Matrix.diag (lemma46P W L c * M) q‖ ≤
        ∑ q : Fin L × Fin W, (if q.1 = c then ‖lemma46P W L c * M‖ else 0) :=
        Finset.sum_le_sum fun q _ => by
          by_cases hq : q.1 = c
          · simp only [hq, ite_true, Matrix.diag]
            exact lemma46_norm_entry_le _ q q
          · simp [Matrix.diag, lemma46P, Matrix.diagonal_mul, hq]
    _ = W * ‖lemma46P W L c * M‖ := by
        rw [Fintype.sum_prod_type]
        have h : ∀ x : Fin L, ∑ _y : Fin W, (if x = c then ‖lemma46P W L c * M‖ else 0) =
            if x = c then (W : ℝ) * ‖lemma46P W L c * M‖ else 0 := fun x => by
          split_ifs <;> simp
        simp only [h]
        simp

/-- The envelope of a loop by its edges: if the edge `p` of the cyclic word `a` (between the
cyclic predecessor of `a_p` and `a_p`) has both blocks at most `Y_p`, then
`W^{k-1} |ℒ_k(a, σ)| ≤ ∏_p Y_p`. -/
private lemma lemma46_envelope (hW : 1 ≤ W) {n : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (Y : Fin (n + 1) → ℝ) (hY0 : ∀ p, 0 ≤ Y p) (a : Fin (n + 1) → Fin L)
    (σ : Fin (n + 1) → Bool)
    (hY : ∀ p, ‖blockOf G ((Fin.cons (a (Fin.last n)) a : Fin (n + 2) → Fin L) p.castSucc) (a p)‖ ≤
        Y p ∧
      ‖blockOf G (a p) ((Fin.cons (a (Fin.last n)) a : Fin (n + 2) → Fin L) p.castSucc)‖ ≤ Y p) :
    (W : ℝ) ^ n * ‖loopTr G a σ‖ ≤ ∏ p, Y p := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hchain := lemma46_chain_norm (n + 1) Y (fun p => sgnMat G (σ p))
    (Fin.cons (a (Fin.last n)) a) hY0 (fun p => by
      have h := lemma46_edge_le (W := W) G (Y p) (σ p) _ _ (hY p).1 (hY p).2
      simpa only [Fin.cons_succ] using h)
  simp only [Fin.cons_zero, Fin.cons_succ] at hchain
  have htr : (List.ofFn fun p => sgnMat G (σ p) * lemma46P W L (a p)).prod.trace =
      (lemma46P W L (a (Fin.last n)) *
        (List.ofFn fun p => sgnMat G (σ p) * lemma46P W L (a p)).prod).trace := by
    rw [Matrix.trace_mul_comm, lemma46_prod_absorb]
  have hT := lemma46_trace_P_le (a (Fin.last n))
    (List.ofFn fun p => sgnMat G (σ p) * lemma46P W L (a p)).prod
  have hP0 : 0 ≤ ∏ p, Y p := Finset.prod_nonneg fun p _ => hY0 p
  unfold loopTr
  rw [lemma46_prod_E (n + 1) (fun p => sgnMat G (σ p)) a, Matrix.trace_smul, smul_eq_mul,
    norm_mul, norm_pow, norm_inv, Complex.norm_natCast, htr]
  calc (W : ℝ) ^ n * ((W : ℝ)⁻¹ ^ (n + 1) * ‖(lemma46P W L (a (Fin.last n)) *
        (List.ofFn fun p => sgnMat G (σ p) * lemma46P W L (a p)).prod).trace‖) ≤
      (W : ℝ) ^ n * ((W : ℝ)⁻¹ ^ (n + 1) * (W * ∏ p, Y p)) := by
        gcongr
        exact hT.trans (mul_le_mul_of_nonneg_left hchain hW0.le)
    _ = ∏ p, Y p := by
        rw [inv_pow]
        field_simp
        ring

end Envelope

/-! ### Asymptotic helpers -/

/-- `K log W ≤ W^ε` for all large `W`. -/
private lemma lemma46_ev_log (K ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ W : ℕ in atTop, K * Real.log W ≤ (W : ℝ) ^ ε := by
  have h := (isLittleO_log_rpow_atTop hε).bound (c := (|K| + 1)⁻¹) (by positivity)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop 1] with W hW hW1
  have hW' : ‖Real.log W‖ ≤ (|K| + 1)⁻¹ * ‖(W : ℝ) ^ ε‖ := hW
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hl : 0 ≤ Real.log W := Real.log_nonneg hW1'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl,
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hW'
  have h1 : K * Real.log W ≤ (|K| + 1) * Real.log W :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) hl
  have h2 : (|K| + 1) * Real.log W ≤ (W : ℝ) ^ ε := by
    have := mul_le_mul_of_nonneg_left hW' (by positivity : (0 : ℝ) ≤ |K| + 1)
    rwa [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this
  linarith

/-- `W^{-D-1} + W^{-D-1} ≤ W^{-D}` for `W ≥ 2`. -/
private lemma lemma46_two (W : ℕ) (hW : 2 ≤ W) (D : ℝ) :
    ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) ≤
      ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : (W : ℝ) ^ (-D) = W * (W : ℝ) ^ (-(D + 1)) := by
    rw [show -D = 1 + -(D + 1) by ring, Real.rpow_add hW0, Real.rpow_one]
  rw [e]
  have := mul_le_mul_of_nonneg_right hW2 (by positivity : (0 : ℝ) ≤ (W : ℝ) ^ (-(D + 1)))
  linarith

/-! ### The pair field -/

/-- `|log(1 - u)| ≤ 1` for `0 ≤ u ≤ 1/2`. -/
private lemma lemma46_abs_log_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    |Real.log (1 - u)| ≤ 1 := by
  have h0 : 0 < 1 - u := by linarith
  have hle : Real.log (1 - u) ≤ 0 := Real.log_nonpos h0.le (by linarith)
  rw [abs_of_nonpos hle, ← Real.log_inv]
  have := Real.log_le_sub_one_of_pos (inv_pos.2 h0)
  have h2 : (1 - u)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ h0 (by norm_num)]; linarith
  linarith

/-- The word `(a, b)` has diameter at least `d(a, b)`. -/
private lemma lemma46_diam_two {L : ℕ} (a b : Fin L) : cycDist a b ≤ wordDiam ![a, b] := by
  unfold wordDiam
  have := Finset.le_sup (f := fun p : Fin 2 × Fin 2 => cycDist (![a, b] p.1) (![a, b] p.2))
    (Finset.mem_univ ((0 : Fin 2), (1 : Fin 2)))
  simpa using this

/-- Lemma 5.6 [fo:prop:inputs], the pair component of (5.22) [gc:eq:one-step-input] at each fixed
`u ∈ [0, 1/2]`: `max_{a,b} |D_2^{+-}(a, b)|/(ζ_u² w(d(a,b))) ≺ 1` with the profile
`w = e^{-c_p (d/ℓ_u)^{1/2}} + W^{-F}`, `c_p` fixed before `C_κ`. -/
theorem lemma46_pair (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) :
    ∃ Cκ₀ cp : ℝ, 1 ≤ Cκ₀ ∧ 0 < cp ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ F : ℝ, 0 < F → PrecMax (fun p : FlowPt => p.L) (initLarge κ Cκ CV ρ)
        (Λ := fun _ p => Fin p.L × Fin p.L)
        (fun W p ab ω => flowErr W p ![ab.1, ab.2] ![true, false] ω)
        (fun W p ab => flowZeta W p ^ 2 * weightFn cp (1 / 2) F W (flowEll p) (cycDist ab.1 ab.2)) := by
  obtain ⟨Cf, hCf, Hf⟩ := lemma46_farCore κ CV hκ hκ2
  obtain ⟨Ce, hCe, He⟩ := lemma46_err κ CV hκ hκ2 hCV
  obtain ⟨Cp, C, hCp, hC1, Hp⟩ := lemma46_pt κ hκ hκ2
  obtain ⟨Cκw, Csw, C₁, c₁, hCκw, hCsw, hC₁, hc₁, Hw⟩ :=
    primLoopF_large_weighted κ hκ hκ2 2 le_rfl
  refine ⟨max (max Cf Ce) (max Cp Cκw), 1,
    le_trans hCf (le_trans (le_max_left _ _) (le_max_left _ _)), one_pos,
    fun Cκ hCκ ρ hρ F hF => ?_⟩
  have hCf' : Cf ≤ Cκ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCκ
  have hCe' : Ce ≤ Cκ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCκ
  have hCp' : Cp ≤ Cκ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCκ
  have hCw' : Cκw ≤ Cκ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCκ
  obtain ⟨K, hK, HK⟩ := Hf Cκ hCf' ρ hρ (F + 3) (by linarith)
  obtain ⟨K', hK'def⟩ : ∃ K' : ℝ, K' = max K (2 * (F + 3) / c₁) := ⟨_, rfl⟩
  have hKK : K ≤ K' := hK'def ▸ le_max_left _ _
  have hKc : 2 * (F + 3) / c₁ ≤ K' := hK'def ▸ le_max_right _ _
  have hK'0 : 0 < K' := lt_of_lt_of_le hK hKK
  intro ε D hε hD
  obtain ⟨W₁, HW₁⟩ := HK (D + 1) (by linarith)
  obtain ⟨W₂, HW₂⟩ := He Cκ hCe' ρ hρ 2 (by norm_num) (ε / 2) (D + 1) (by positivity)
    (by linarith)
  obtain ⟨Kw, hKwdef⟩ : ∃ Kw : ℝ, Kw = 1 + C₁ * (1 / 2 : ℝ) ^ (-C₁) := ⟨_, rfl⟩
  have hev : ∀ᶠ W : ℕ in atTop, (∀ CV' : ℝ, ∀ p ∈ initLarge κ Cκ CV' ρ W, 1 ≤ p.g ∧
      (2 * Csw + 1) * p.g ^ 2 * Real.log W ≤ p.L ∧ (2 * Csw + 1) * p.g ^ 2 ≤ p.L ∧ 3 ≤ p.L ∧
      IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ∧
      ‖mRoot p.g p.L p.E‖ ≤ C ∧ C⁻¹ ≤ (mRoot p.g p.L p.E).im) ∧
      max W₁ W₂ ≤ W ∧ 2 ≤ W ∧ 4 * Kw ≤ (W : ℝ) ∧ 4 * K' / ε ^ 2 ≤ Real.log W := by
    filter_upwards [Hp Cκ hCp' ρ hρ (2 * Csw + 1), eventually_ge_atTop (max W₁ W₂),
      eventually_ge_atTop 2, tendsto_natCast_atTop_atTop.eventually_ge_atTop (4 * Kw),
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
        (4 * K' / ε ^ 2)] with W h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨W₀, HW₀⟩ := eventually_atTop.1 hev
  refine ⟨W₀, fun W hW p hp => ?_⟩
  obtain ⟨hpt, hWb, hW2, hWKw, hlogK⟩ := HW₀ W hW
  obtain ⟨hg1, -, hLC, hL3, hroot, -, -⟩ := hpt CV p hp
  have hp' := hp
  obtain ⟨hgC, hE, -, -, hu0, hu1⟩ := hp'
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hg0 : 0 < p.g := by linarith
  have hgg : 0 < p.g ^ 2 := by positivity
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1r
  have hgL : p.g ^ 2 ≤ p.L := le_trans (le_mul_of_one_le_left hgg.le (by linarith)) hLC
  have hℓ : p.g ^ 2 ≤ flowEll p := lemma46_ell_ge p hg1 hu0 hu1 hgL
  have hL1 : 1 ≤ p.L := by omega
  have hζ := lemma46_zeta_lower W hW1 p hg1 hu0 hu1 hL1
  have hζ0 : 0 ≤ flowZeta W p := le_trans (by positivity) hζ
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = (W : ℝ) ^ (-(F + 3)) := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hYdef]; positivity
  have hY1 : Y ≤ 1 := by
    rw [hYdef]; exact Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith)
  -- the deterministic bound outside the two exceptional events
  have hdet : ∀ ω : Ω W p.L, (∀ l : Word 2 p.L,
      ‖flowErr W p l.1 l.2 ω‖ ≤ (W : ℝ) ^ (ε / 2) * flowZeta W p ^ 2) →
      (∀ c d : Fin p.L, K * p.g ^ 2 * Real.log W ≤ cycDist c d →
        ‖blockOf (flowG W p ω) c d‖ ≤ Y) → ∀ a b : Fin p.L,
      ‖flowErr W p ![a, b] ![true, false] ω‖ ≤
        (W : ℝ) ^ ε * (flowZeta W p ^ 2 *
          weightFn 1 (1 / 2) F W (flowEll p) (cycDist a b)) := by
    intro ω hE1 hF1 a b
    have hw0 : (W : ℝ) ^ (-F) ≤ weightFn 1 (1 / 2) F W (flowEll p) (cycDist a b) := by
      unfold weightFn
      have := Real.exp_pos (-(1 * ((cycDist a b : ℝ) / flowEll p) ^ (1 / 2 : ℝ)))
      linarith
    by_cases hd : K' * p.g ^ 2 * Real.log W ≤ cycDist a b
    · -- far pairs: the loop by its two edges, the primitive loop by its weighted bound
      have hab : K * p.g ^ 2 * Real.log W ≤ cycDist a b := by
        have : K * p.g ^ 2 * Real.log W ≤ K' * p.g ^ 2 * Real.log W := by
          gcongr
        linarith
      have hba : K * p.g ^ 2 * Real.log W ≤ cycDist b a := by rwa [lemma46_cd_comm]
      have hG1 := hF1 a b hab
      have hG2 := hF1 b a hba
      have henv := lemma46_envelope (n := 1) hW1 (flowG W p ω) (fun _ => Y) (fun _ => hY0)
        ![a, b] ![true, false] (by
          intro q
          fin_cases q
          · exact ⟨hG2, hG1⟩
          · exact ⟨hG1, hG2⟩)
      rw [Fin.prod_univ_two, pow_one] at henv
      have hL2 : ‖loopTr (flowG W p ω) ![a, b] ![true, false]‖ ≤ Y := by
        have h1 : Y * Y ≤ Y := mul_le_of_le_one_left hY0 hY1
        have h2 : ‖loopTr (flowG W p ω) ![a, b] ![true, false]‖ ≤
            (W : ℝ) * ‖loopTr (flowG W p ω) ![a, b] ![true, false]‖ :=
          le_mul_of_one_le_left (norm_nonneg _) hW1r
        linarith
      have hK2 : ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u ![a, b] ![true, false]‖ ≤
          C₁ * (1 / 2 : ℝ) ^ (-C₁) * Y := by
        have e : primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u ![a, b] ![true, false] =
            ((W : ℂ))⁻¹ * primLoopF p.g p.L p.E (mRoot p.g p.L p.E) p.u ![a, b] ![true, false] := by
          simp [primLoop, primK, primLoopF]
        have hCs : Csw * (1 + |Real.log (1 - p.u)|) * p.g ^ 2 ≤ p.L := by
          have h1 := lemma46_abs_log_le hu0 hu1
          calc Csw * (1 + |Real.log (1 - p.u)|) * p.g ^ 2 ≤ Csw * 2 * p.g ^ 2 := by gcongr; linarith
            _ ≤ (2 * Csw + 1) * p.g ^ 2 := by linarith only [hgg]
            _ ≤ p.L := hLC
        have hF := Hw p.g (hCw'.trans hgC) p.u hu0 (by linarith) p.L hL3 hCs p.E hE _ hroot
          ![a, b] ![true, false]
        have hpow : (1 - p.u) ^ (-C₁) ≤ (1 / 2 : ℝ) ^ (-C₁) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
        set mn : ℝ := min (p.L : ℝ) (p.g ^ 2 / Real.sqrt (1 - p.u)) with hmn
        have hmn0 : 0 < mn := lt_min (by exact_mod_cast hL1) (by
          have : 0 < Real.sqrt (1 - p.u) := Real.sqrt_pos.2 (by linarith)
          positivity)
        have hmn2 : mn ≤ 2 * p.g ^ 2 := by
          refine (min_le_right _ _).trans ?_
          have hs : 1 / 2 ≤ Real.sqrt (1 - p.u) := by
            rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
          rw [div_le_iff₀ (by linarith)]
          have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * p.g ^ 2)
          linarith only [this]
        have hexp : Real.exp (-(c₁ * wordDiam ![a, b] / mn)) ≤ Y := by
          have hdiam : (cycDist a b : ℝ) ≤ wordDiam ![a, b] := by
            exact_mod_cast lemma46_diam_two a b
          have h1 : c₁ * (cycDist a b : ℝ) / (2 * p.g ^ 2) ≤ c₁ * wordDiam ![a, b] / mn := by
            calc c₁ * (cycDist a b : ℝ) / (2 * p.g ^ 2) ≤
                c₁ * wordDiam ![a, b] / (2 * p.g ^ 2) := by
                  gcongr
              _ ≤ c₁ * wordDiam ![a, b] / mn :=
                  div_le_div_of_nonneg_left (by positivity) hmn0 hmn2
          have h2 : (F + 3) * Real.log W ≤ c₁ * (cycDist a b : ℝ) / (2 * p.g ^ 2) := by
            rw [le_div_iff₀ (by positivity)]
            have h3 : 2 * (F + 3) * Real.log W * p.g ^ 2 ≤ c₁ * (K' * p.g ^ 2 * Real.log W) := by
              have h4 : 2 * (F + 3) ≤ c₁ * K' := by
                rw [div_le_iff₀ hc₁] at hKc; linarith
              have h5 : 0 ≤ Real.log W * p.g ^ 2 := by positivity
              have := mul_le_mul_of_nonneg_right h4 h5
              linarith only [this]
            have := mul_le_mul_of_nonneg_left hd hc₁.le
            linarith only [h3, this]
          rw [hYdef, Real.rpow_def_of_pos hW0]
          refine Real.exp_le_exp.2 ?_
          linarith only [h1, h2]
        rw [e, norm_mul, norm_inv, Complex.norm_natCast]
        calc (W : ℝ)⁻¹ * ‖primLoopF p.g p.L p.E (mRoot p.g p.L p.E) p.u ![a, b] ![true, false]‖ ≤
            1 * (C₁ * (1 - p.u) ^ (-C₁) * Real.exp (-(c₁ * wordDiam ![a, b] / mn))) :=
              mul_le_mul (inv_le_one_of_one_le₀ hW1r) hF (norm_nonneg _) zero_le_one
          _ ≤ C₁ * (1 / 2 : ℝ) ^ (-C₁) * Y := by
              rw [one_mul]
              gcongr
      have hD2 : ‖flowErr W p ![a, b] ![true, false] ω‖ ≤ Kw * Y := by
        unfold flowErr
        refine (norm_sub_le _ _).trans ?_
        rw [hKwdef]
        linarith
      have hfin : Kw * Y ≤ ((2 : ℝ) * W)⁻¹ ^ 2 * (W : ℝ) ^ (-F) := by
        have e : Y = (W : ℝ) ^ (-F) / (W : ℝ) ^ 3 := by
          rw [hYdef, show -(F + 3) = -F + -((3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_add hW0,
            Real.rpow_neg hW0.le ((3 : ℕ) : ℝ), Real.rpow_natCast, div_eq_mul_inv]
        have hF0 : 0 < (W : ℝ) ^ (-F) := Real.rpow_pos_of_pos hW0 _
        have hKw4 : Kw / W ≤ 1 / 4 := by rw [div_le_iff₀ hW0]; linarith
        have e1 : Kw * Y = (Kw / W) * ((W : ℝ) ^ (-F) / (W : ℝ) ^ 2) := by
          rw [e]; field_simp
        have e2 : ((2 : ℝ) * W)⁻¹ ^ 2 * (W : ℝ) ^ (-F) =
            (1 / 4) * ((W : ℝ) ^ (-F) / (W : ℝ) ^ 2) := by
          field_simp; ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_right hKw4 (by positivity)
      calc ‖flowErr W p ![a, b] ![true, false] ω‖ ≤ Kw * Y := hD2
        _ ≤ ((2 : ℝ) * W)⁻¹ ^ 2 * (W : ℝ) ^ (-F) := hfin
        _ ≤ 1 * (flowZeta W p ^ 2 * weightFn 1 (1 / 2) F W (flowEll p) (cycDist a b)) := by
            rw [one_mul]
            exact mul_le_mul (pow_le_pow_left₀ (by positivity) hζ 2) hw0
              (Real.rpow_nonneg hW0.le _) (sq_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.one_le_rpow hW1r hε.le)
              (mul_nonneg (sq_nonneg _) (le_trans (Real.rpow_nonneg hW0.le _) hw0))
    · -- near pairs: the weight is at least `W^{-ε/2}`
      have hd' : (cycDist a b : ℝ) < K' * p.g ^ 2 * Real.log W := not_le.mp hd
      have hℓ0 : 0 < flowEll p := lt_of_lt_of_le hgg hℓ
      have hr : (cycDist a b : ℝ) / flowEll p ≤ K' * Real.log W := by
        rw [div_le_iff₀ hℓ0]
        have : K' * p.g ^ 2 * Real.log W ≤ K' * Real.log W * flowEll p := by
          have := mul_le_mul_of_nonneg_left hℓ (by positivity : (0 : ℝ) ≤ K' * Real.log W)
          linarith only [this]
        linarith
      have hsq : ((cycDist a b : ℝ) / flowEll p) ^ (1 / 2 : ℝ) ≤ ε / 2 * Real.log W := by
        rw [← Real.sqrt_eq_rpow]
        have h1 : Real.sqrt ((cycDist a b : ℝ) / flowEll p) ≤ Real.sqrt (K' * Real.log W) :=
          Real.sqrt_le_sqrt hr
        have h2 : K' * Real.log W ≤ (ε / 2 * Real.log W) ^ 2 := by
          have h3 : 4 * K' ≤ ε ^ 2 * Real.log W := by
            rw [div_le_iff₀ (by positivity)] at hlogK; linarith
          have := mul_le_mul_of_nonneg_right h3 hlog0
          linarith only [this]
        have h4 : Real.sqrt (K' * Real.log W) ≤ ε / 2 * Real.log W := by
          rw [Real.sqrt_le_left (by positivity)]
          exact h2
        linarith
      have hw : (W : ℝ) ^ (-(ε / 2)) ≤ weightFn 1 (1 / 2) F W (flowEll p) (cycDist a b) := by
        unfold weightFn
        have h1 : (W : ℝ) ^ (-(ε / 2)) ≤
            Real.exp (-(1 * ((cycDist a b : ℝ) / flowEll p) ^ (1 / 2 : ℝ))) := by
          rw [Real.rpow_def_of_pos hW0]
          refine Real.exp_le_exp.2 ?_
          rw [one_mul]
          linarith only [hsq]
        have h2 : 0 ≤ (W : ℝ) ^ (-F) := Real.rpow_nonneg hW0.le _
        linarith only [h1, h2]
      have hE2 := hE1 (![a, b], ![true, false])
      have e : (W : ℝ) ^ (ε / 2) = (W : ℝ) ^ ε * (W : ℝ) ^ (-(ε / 2)) := by
        rw [← Real.rpow_add hW0]; ring_nf
      calc ‖flowErr W p ![a, b] ![true, false] ω‖ ≤ (W : ℝ) ^ (ε / 2) * flowZeta W p ^ 2 := hE2
        _ = (W : ℝ) ^ ε * (flowZeta W p ^ 2 * (W : ℝ) ^ (-(ε / 2))) := by rw [e]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (sq_nonneg _))
              (Real.rpow_nonneg hW0.le _)
  have hsub : {ω | ∃ ab : Fin p.L × Fin p.L, (W : ℝ) ^ ε * (flowZeta W p ^ 2 *
      weightFn 1 (1 / 2) F W (flowEll p) (cycDist ab.1 ab.2)) <
        ‖flowErr W p ![ab.1, ab.2] ![true, false] ω‖} ⊆
      {ω | ∃ l : Word 2 p.L, (W : ℝ) ^ (ε / 2) * flowZeta W p ^ 2 < ‖flowErr W p l.1 l.2 ω‖} ∪
      {ω | ∃ a b : Fin p.L, K * p.g ^ 2 * Real.log W ≤ cycDist a b ∧
        (W : ℝ) ^ (-(F + 3)) < ‖blockOf (flowG W p ω) a b‖} := by
    rintro ω ⟨⟨a, b⟩, hab⟩
    by_contra hcon
    have hE1 : ∀ l : Word 2 p.L, ‖flowErr W p l.1 l.2 ω‖ ≤ (W : ℝ) ^ (ε / 2) * flowZeta W p ^ 2 :=
      fun l => by
        by_contra h
        exact hcon (Or.inl ⟨l, not_le.mp h⟩)
    have hF1 : ∀ c d : Fin p.L, K * p.g ^ 2 * Real.log W ≤ cycDist c d →
        ‖blockOf (flowG W p ω) c d‖ ≤ Y := fun c d hcd => by
      by_contra h
      rw [hYdef] at h
      exact hcon (Or.inr ⟨c, d, hcd, not_le.mp h⟩)
    exact absurd hab (not_lt.2 (hdet ω hE1 hF1 a b))
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have h1 := HW₂ W (le_trans (le_max_right _ _) hWb) p hp
  have h2 := HW₁ W (le_trans (le_max_left _ _) hWb) p hp
  exact (add_le_add h1 h2).trans (lemma46_two W hW2 D)

/-! ### The tail field -/

/-- If consecutive labels of a word are within `T`, its diameter is at most `2(k - 1)T`. -/
private lemma lemma46_diam_le {L n : ℕ} (a : Fin (n + 1) → Fin L) (T : ℝ) (hT : 0 ≤ T)
    (h : ∀ j : ℕ, ∀ hj : j + 1 < n + 1,
      (cycDist (a ⟨j, by omega⟩) (a ⟨j + 1, hj⟩) : ℝ) ≤ T) :
    (wordDiam a : ℝ) ≤ 2 * n * T := by
  have h0 : ∀ j : ℕ, ∀ hj : j < n + 1, (cycDist (a 0) (a ⟨j, hj⟩) : ℝ) ≤ j * T := by
    intro j
    induction j with
    | zero =>
      intro hj
      have e : (⟨0, hj⟩ : Fin (n + 1)) = 0 := rfl
      rw [e]
      simp [cycDist]
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := h j hj
      have h3 := lemma46_cd_tri (a 0) (a ⟨j, by omega⟩) (a ⟨j + 1, hj⟩)
      have h3' : (cycDist (a 0) (a ⟨j + 1, hj⟩) : ℝ) ≤
          cycDist (a 0) (a ⟨j, by omega⟩) + cycDist (a ⟨j, by omega⟩) (a ⟨j + 1, hj⟩) := by
        exact_mod_cast h3
      push_cast
      linarith
  have hb : ∀ q : Fin (n + 1), (cycDist (a 0) (a q) : ℝ) ≤ n * T := fun q => by
    have := h0 q.val q.isLt
    have hq : (q.val : ℝ) ≤ n := by exact_mod_cast (by omega : q.val ≤ n)
    calc (cycDist (a 0) (a q) : ℝ) = cycDist (a 0) (a ⟨q.val, q.isLt⟩) := rfl
      _ ≤ q.val * T := this
      _ ≤ n * T := mul_le_mul_of_nonneg_right hq hT
  unfold wordDiam
  obtain ⟨pq, -, hpq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1)))
    Finset.univ_nonempty (fun pq => cycDist (a pq.1) (a pq.2))
  rw [hpq]
  have h1 := lemma46_cd_tri (a pq.1) (a 0) (a pq.2)
  rw [lemma46_cd_comm (a pq.1) (a 0)] at h1
  have h1' : (cycDist (a pq.1) (a pq.2) : ℝ) ≤ cycDist (a 0) (a pq.1) + cycDist (a 0) (a pq.2) := by
    exact_mod_cast h1
  have := hb pq.1
  have := hb pq.2
  linarith

/-- Lemma 5.6 [fo:prop:inputs], the tail component of (5.22) [gc:eq:one-step-input] at each fixed
`u ∈ [0, 1/2]`: loops and loop errors of words with diameter above `W^ε ℓ_u` are `≺ W^{-A}`. -/
theorem lemma46_tail (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ k : ℕ, 2 ≤ k → ∀ ε A : ℝ, 0 < ε → 0 < A →
        PrecMax (fun p : FlowPt => p.L) (initLarge κ Cκ CV ρ)
          (Λ := fun W p => {w : Word k p.L // (W : ℝ) ^ ε * flowEll p < wordDiam w.1})
          (fun W p w ω => ((‖loopTr (flowG W p ω) w.1.1 w.1.2‖ + ‖flowErr W p w.1.1 w.1.2 ω‖ :
            ℝ) : ℂ))
          (fun W _ _ => (W : ℝ) ^ (-A)) := by
  obtain ⟨Cf, hCf, Hf⟩ := lemma46_farCore κ CV hκ hκ2
  obtain ⟨Cv, hCv, Hv⟩ := vert_max κ CV hκ hκ2 hCV
  obtain ⟨Cp, C, hCp, hC1, Hp⟩ := lemma46_pt κ hκ hκ2
  obtain ⟨Ct, hCt, Ht⟩ := primLoop_large_tail' κ hκ hκ2
  refine ⟨max (max Cf Cv) (max Cp Ct),
    le_trans hCf (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun Cκ hCκ ρ hρ k hk ε A hε hA => ?_⟩
  have hCf' : Cf ≤ Cκ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCκ
  have hCv' : Cv ≤ Cκ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCκ
  have hCp' : Cp ≤ Cκ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCκ
  have hCt' : Ct ≤ Cκ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCκ
  obtain ⟨K, hK, HK⟩ := Hf Cκ hCf' ρ hρ (A + 1) (by linarith)
  obtain ⟨Cs, Wt, hCs, HWt⟩ := Ht ε (A + 1) hε (by linarith) k hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  intro ε' D hε' hD
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = ε' / (2 * ((n + 1 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hε₁ : 0 < ε₁ := by rw [hε₁def]; positivity
  have hε₁n : ε₁ * n ≤ ε' / 2 := by
    rw [hε₁def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    push_cast
    nlinarith
  obtain ⟨W₁, HW₁⟩ := HK (D + 1) (by linarith)
  obtain ⟨W₂, HW₂⟩ := Hv Cκ hCv' ρ hρ ε₁ (D + 1) hε₁ (by linarith)
  have hev : ∀ᶠ W : ℕ in atTop, (∀ CV' : ℝ, ∀ p ∈ initLarge κ Cκ CV' ρ W, 1 ≤ p.g ∧
      (Cs + 1) * p.g ^ 2 * Real.log W ≤ p.L ∧ (Cs + 1) * p.g ^ 2 ≤ p.L ∧ 3 ≤ p.L ∧
      IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ∧
      ‖mRoot p.g p.L p.E‖ ≤ C ∧ C⁻¹ ≤ (mRoot p.g p.L p.E).im) ∧
      max (max W₁ W₂) Wt ≤ W ∧ 3 ≤ W ∧ C ≤ (W : ℝ) ^ (1 / 2 : ℝ) ∧
      (2 * n * K) * Real.log W ≤ (W : ℝ) ^ ε := by
    filter_upwards [Hp Cκ hCp' ρ hρ (Cs + 1), eventually_ge_atTop (max (max W₁ W₂) Wt),
      eventually_ge_atTop 3,
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop).eventually_ge_atTop C,
      lemma46_ev_log (2 * n * K) ε hε] with W h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨W₀, HW₀⟩ := eventually_atTop.1 hev
  refine ⟨W₀, fun W hW p hp => ?_⟩
  obtain ⟨hpt, hWb, hW3, hCW, hlogε⟩ := HW₀ W hW
  obtain ⟨hg1, hLC, hLC', hL3, hroot, hmC, -⟩ := hpt CV p hp
  have hp' := hp
  obtain ⟨hgC, hE, -, -, hu0, hu1⟩ := hp'
  have hW1 : 1 ≤ W := by omega
  have hW2 : 2 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW3r : (3 : ℝ) ≤ W := by exact_mod_cast hW3
  have hg0 : 0 < p.g := by linarith
  have hgg : 0 < p.g ^ 2 := by positivity
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1r
  have hgL : p.g ^ 2 ≤ p.L := le_trans (le_mul_of_one_le_left hgg.le (by linarith)) hLC'
  have hℓ : p.g ^ 2 ≤ flowEll p := lemma46_ell_ge p hg1 hu0 hu1 hgL
  -- the envelope at the characteristic point
  set η : ℝ := etaChar p.g (mRoot p.g p.L p.E) p.u with hη
  have hgη : p.g ^ 2 * η ≤ (W : ℝ) ^ (1 / 2 : ℝ) := by
    have e : p.g ^ 2 * η = (1 - p.u) * (mRoot p.g p.L p.E).im := by
      rw [hη]; unfold etaChar; rw [lemma46_gammaG hg1]
      field_simp
    rw [e]
    have him : (mRoot p.g p.L p.E).im ≤ C := (Complex.im_le_norm _).trans hmC
    have hm0 : 0 < (mRoot p.g p.L p.E).im := hroot.1
    have : (1 - p.u) * (mRoot p.g p.L p.E).im ≤ (mRoot p.g p.L p.E).im :=
      mul_le_of_le_one_left hm0.le (by linarith)
    linarith
  have hseg : ∀ ω, segG W (p, η) ω = flowG W p ω := by
    intro ω
    have him : (zChar p.g p.E (mRoot p.g p.L p.E) p.u).im = η := by
      rw [hη, im_zChar]
    simp only [segG, flowG]
    congr 1
    rw [← him]
    exact Complex.re_add_im _
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (W : ℝ) ^ (-(A + 1)) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; exact Real.rpow_pos_of_pos hW0 _
  have htW : (W : ℝ) * t = (W : ℝ) ^ (-A) := by
    rw [htdef, show -A = 1 + -(A + 1) by ring, Real.rpow_add hW0, Real.rpow_one]
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = (W : ℝ) ^ ε₁ := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hXn : X ^ n ≤ (W : ℝ) ^ (ε' / 2) := by
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    exact Real.rpow_le_rpow_of_exponent_le hW1r hε₁n
  have hW3t : (W : ℝ) ^ (-(3 : ℝ)) ≤ 1 - p.u := by
    rw [Real.rpow_neg hW0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h8 : (8 : ℝ) ≤ (W : ℝ) ^ 3 :=
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ (W : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    have : ((W : ℝ) ^ 3)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hsub : {ω | ∃ w : {w : Word (n + 1) p.L // (W : ℝ) ^ ε * flowEll p < wordDiam w.1},
      (W : ℝ) ^ ε' * (W : ℝ) ^ (-A) <
        ‖((‖loopTr (flowG W p ω) w.1.1 w.1.2‖ + ‖flowErr W p w.1.1 w.1.2 ω‖ : ℝ) : ℂ)‖} ⊆
      {ω | ∃ a b : Fin (p, η).1.L, (W : ℝ) ^ ε₁ < ‖blockOf (segG W (p, η) ω) a b‖ ∨
          (W : ℝ) ^ (ε₁ - 1) < ‖segRes W (p, η) ω a b‖ ∨ ∃ i j : Fin W, (W : ℝ) ^ (ε₁ - 1 / 2) <
            ‖segG W (p, η) ω (a, i) (b, j) - if i = j then blockTr (segG W (p, η) ω) a b else 0‖} ∪
      {ω | ∃ a b : Fin p.L, K * p.g ^ 2 * Real.log W ≤ cycDist a b ∧
        (W : ℝ) ^ (-(A + 1)) < ‖blockOf (flowG W p ω) a b‖} := by
    rintro ω ⟨⟨⟨a, σ⟩, hdiam⟩, hl⟩
    by_contra hcon
    have hX : ∀ c d : Fin p.L, ‖blockOf (flowG W p ω) c d‖ ≤ X := fun c d => by
      by_contra h
      refine hcon (Or.inl ⟨c, d, Or.inl ?_⟩)
      rw [hseg ω, ← hXdef]
      exact not_le.mp h
    have hF : ∀ c d : Fin p.L, K * p.g ^ 2 * Real.log W ≤ cycDist c d →
        ‖blockOf (flowG W p ω) c d‖ ≤ t := fun c d hcd => by
      by_contra h
      rw [htdef] at h
      exact hcon (Or.inr ⟨c, d, hcd, not_le.mp h⟩)
    have hl' : (W : ℝ) ^ ε' * (W : ℝ) ^ (-A) <
        ‖loopTr (flowG W p ω) a σ‖ + ‖flowErr W p a σ ω‖ := by
      have := hl
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)] at this
      exact this
    -- a far edge
    have hedge : ∃ j : ℕ, ∃ hj : j + 1 < n + 1,
        K * p.g ^ 2 * Real.log W ≤ cycDist (a ⟨j, by omega⟩) (a ⟨j + 1, hj⟩) := by
      by_contra hne
      have hall : ∀ j : ℕ, ∀ hj : j + 1 < n + 1,
          (cycDist (a ⟨j, by omega⟩) (a ⟨j + 1, hj⟩) : ℝ) ≤ K * p.g ^ 2 * Real.log W :=
        fun j hj => le_of_lt (not_le.mp fun h => hne ⟨j, hj, h⟩)
      have h1 := lemma46_diam_le a (K * p.g ^ 2 * Real.log W) (by positivity) hall
      have h2 : 2 * n * (K * p.g ^ 2 * Real.log W) ≤ (W : ℝ) ^ ε * flowEll p := by
        calc 2 * n * (K * p.g ^ 2 * Real.log W) = (2 * n * K) * Real.log W * p.g ^ 2 := by ring
          _ ≤ (W : ℝ) ^ ε * p.g ^ 2 := mul_le_mul_of_nonneg_right hlogε hgg.le
          _ ≤ (W : ℝ) ^ ε * flowEll p := mul_le_mul_of_nonneg_left hℓ (by positivity)
      have h3 : (W : ℝ) ^ ε * flowEll p < wordDiam a := hdiam
      linarith only [h1, h2, h3]
    obtain ⟨j, hj, hfar⟩ := hedge
    set q₀ : Fin (n + 1) := ⟨j + 1, hj⟩ with hq₀
    have hprev : ((Fin.cons (a (Fin.last n)) a : Fin (n + 2) → Fin p.L) q₀.castSucc) =
        a ⟨j, by omega⟩ := by
      have e : q₀.castSucc = (⟨j, by omega⟩ : Fin (n + 1)).succ := Fin.ext rfl
      rw [e, Fin.cons_succ]
    obtain ⟨Y, hYdef⟩ : ∃ Y : Fin (n + 1) → ℝ, Y = fun q => if q = q₀ then t else X := ⟨_, rfl⟩
    have hY0 : ∀ q, 0 ≤ Y q := fun q => by
      rw [hYdef]; dsimp only; split_ifs
      · exact ht0.le
      · exact hX0
    have henv := lemma46_envelope hW1 (flowG W p ω) Y hY0 a σ (by
      intro q
      by_cases hq : q = q₀
      · have hY : Y q = t := by rw [hYdef]; simp [hq]
        rw [hY, hq, hprev]
        refine ⟨hF _ _ ?_, hF _ _ ?_⟩
        · exact hfar
        · rw [lemma46_cd_comm]; exact hfar
      · have hY : Y q = X := by rw [hYdef]; simp [hq]
        rw [hY]
        exact ⟨hX _ _, hX _ _⟩)
    have hprod : ∏ q, Y q = t * X ^ n := by
      rw [← Finset.mul_prod_erase Finset.univ Y (Finset.mem_univ q₀)]
      have h1 : Y q₀ = t := by rw [hYdef]; simp
      have h2 : ∏ q ∈ Finset.univ.erase q₀, Y q = ∏ q ∈ Finset.univ.erase q₀, X :=
        Finset.prod_congr rfl fun q hq => by
          rw [hYdef]; simp [Finset.ne_of_mem_erase hq]
      rw [h1, h2, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
    rw [hprod] at henv
    have hLp : ‖loopTr (flowG W p ω) a σ‖ ≤ t * (W : ℝ) ^ (ε' / 2) := by
      have h1 : ‖loopTr (flowG W p ω) a σ‖ ≤ (W : ℝ) ^ n * ‖loopTr (flowG W p ω) a σ‖ :=
        le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hW1r)
      have h2 : t * X ^ n ≤ t * (W : ℝ) ^ (ε' / 2) := mul_le_mul_of_nonneg_left hXn ht0.le
      linarith only [h1, h2, henv]
    have hK : ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u a σ‖ ≤ t := by
      rw [htdef]
      refine HWt W (le_trans (le_max_right _ _) hWb) p.g (hCt'.trans hgC) p.L hL3 ?_ p.E hE _
        hroot p.u hu0 hW3t a σ hdiam
      have : Cs * p.g ^ 2 * Real.log W ≤ (Cs + 1) * p.g ^ 2 * Real.log W := by
        have : 0 ≤ p.g ^ 2 * Real.log W := by positivity
        linarith only [this]
      linarith only [this, hLC]
    have hD : ‖flowErr W p a σ ω‖ ≤ t * (W : ℝ) ^ (ε' / 2) + t := by
      unfold flowErr
      exact (norm_sub_le _ _).trans (add_le_add hLp hK)
    have hfin : t * (W : ℝ) ^ (ε' / 2) + (t * (W : ℝ) ^ (ε' / 2) + t) ≤
        (W : ℝ) ^ ε' * (W : ℝ) ^ (-A) := by
      have h1 : (W : ℝ) ^ (ε' / 2) ≤ (W : ℝ) ^ ε' :=
        Real.rpow_le_rpow_of_exponent_le hW1r (by linarith)
      have h2 : 1 ≤ (W : ℝ) ^ ε' := Real.one_le_rpow hW1r hε'.le
      rw [← htW]
      have h3 : t * (W : ℝ) ^ (ε' / 2) ≤ t * (W : ℝ) ^ ε' := mul_le_mul_of_nonneg_left h1 ht0.le
      have h4 : t ≤ t * (W : ℝ) ^ ε' := le_mul_of_one_le_right ht0.le h2
      have h5 : 3 * (t * (W : ℝ) ^ ε') ≤ (W : ℝ) * (t * (W : ℝ) ^ ε') :=
        mul_le_mul_of_nonneg_right hW3r (by positivity)
      linarith only [h3, h4, h5]
    linarith only [hl', hLp, hD, hfin]
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have h1 := HW₂ W (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hWb) (p, η) hp
    le_rfl hgη
  have h2 := HW₁ W (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hWb) p hp
  exact (add_le_add h1 h2).trans (lemma46_two W hW2 D)

/-! ### Lemma 5.6 [fo:prop:inputs] at a fixed time -/

/-- Lemma 5.6 [fo:prop:inputs] in fixed-time form: (5.23) [gc:eq:iteration-input] at each
deterministic `u ∈ [0, 1/2]`, on `g ≥ C_κ`, `|E| ≤ 2 - κ`,
`ρ(W) g² log W ≤ L ≤ C g² W²`, `ρ → ∞`, no upper bound on `g`. -/
theorem lemma46_fixedTime (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 2 ≤ CV) :
    ∃ Cκ₀ cp : ℝ, 1 ≤ Cκ₀ ∧ 0 < cp ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      OneStepInput cp (1 / 2) id (fun W => {p : FlowPt | Cκ ≤ p.g ∧ |p.E| ≤ 2 - κ ∧
        ρ W * p.g ^ 2 * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ CV * p.g ^ 2 * (W : ℝ) ^ 2 ∧
        0 ≤ p.u ∧ p.u ≤ 1 / 2}) := by
  have hCV0 : 0 < CV := by linarith
  obtain ⟨C1, hC1, H1⟩ := lemma46_loop κ CV hκ hκ2 hCV0
  obtain ⟨C2, -, H2⟩ := lemma46_err κ CV hκ hκ2 hCV0
  obtain ⟨C3, -, H3⟩ := lemma46_avg κ CV hκ hκ2 hCV0
  obtain ⟨C4, -, H4⟩ := lemma46_entry κ CV hκ hκ2 hCV0
  obtain ⟨C5, cp, -, hcp, H5⟩ := lemma46_pair κ CV hκ hκ2 hCV0
  obtain ⟨C6, -, H6⟩ := lemma46_tail κ CV hκ hκ2 hCV0
  refine ⟨max (max (max C1 C2) (max C3 C4)) (max C5 C6), cp,
    le_trans hC1 (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))), hcp,
    fun Cκ hCκ ρ hρ => ?_⟩
  have h1 : C1 ≤ Cκ :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hCκ
  have h2 : C2 ≤ Cκ :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hCκ
  have h3 : C3 ≤ Cκ :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hCκ
  have h4 : C4 ≤ Cκ :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hCκ
  have h5 : C5 ≤ Cκ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCκ
  have h6 : C6 ≤ Cκ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCκ
  have hdom : ∀ W, (fun W => {p : FlowPt | Cκ ≤ p.g ∧ |p.E| ≤ 2 - κ ∧
      ρ W * p.g ^ 2 * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ CV * p.g ^ 2 * (W : ℝ) ^ 2 ∧
      0 ≤ p.u ∧ p.u ≤ 1 / 2}) W ⊆ initLarge κ Cκ CV ρ W := fun W p hp => hp
  exact
    { loop := fun k hk => (H1 Cκ h1 ρ hρ k hk).anti hdom
      err := fun k hk => (H2 Cκ h2 ρ hρ k hk).anti hdom
      avg := (H3 Cκ h3 ρ hρ).anti hdom
      entry := (H4 Cκ h4 ρ hρ).anti hdom
      pair := fun F hF => (H5 Cκ h5 ρ hρ F hF).anti hdom
      tail := fun k hk ε A hε hA => (H6 Cκ h6 ρ hρ k hk ε A hε hA).anti hdom }

end LSBA
