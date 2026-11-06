import Mathlib

/-!
# A Rademacher chaos bound

The order-two Rademacher chaos moment bound (decoupling, Khintchine, Minkowski), used with random
signs in Appendix G.1 [app:relative-local-law-proof].
-/

open scoped Matrix

noncomputable section
open scoped Classical

namespace LSBA

section RademacherChaosAux

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The sign flip at the coordinate `j`: it multiplies the `j`-th sign by `-1`. -/
private def rcFlip (j : κ) : Equiv.Perm (κ → ℤˣ) := Equiv.mulRight (Pi.mulSingle j (-1))

omit [Fintype κ] in
private lemma rcFlip_apply (j : κ) (s : κ → ℤˣ) (k : κ) :
    rcFlip j s k = if k = j then -s k else s k := by
  by_cases h : k = j
  · subst h; simp [rcFlip]
  · simp [rcFlip, h]

omit [Fintype κ] in
private lemma rcFlip_self (j : κ) (s : κ → ℤˣ) :
    (((rcFlip j s j : ℤˣ) : ℤ) : ℝ) = -(((s j : ℤˣ) : ℤ) : ℝ) := by
  simp [rcFlip_apply]

omit [Fintype κ] in
private lemma rcFlip_ne (j k : κ) (s : κ → ℤˣ) (h : k ≠ j) : rcFlip j s k = s k := by
  simp [rcFlip_apply, h]

/-- For a sign `u`: `e^{u y} + e^{-u y} ≤ 2 e^{y²/2}`. -/
private lemma rc_exp_pair (u : ℤˣ) (y : ℝ) :
    Real.exp ((((u : ℤˣ) : ℤ) : ℝ) * y) + Real.exp (-((((u : ℤˣ) : ℤ) : ℝ) * y)) ≤
      2 * Real.exp (y ^ 2 / 2) := by
  have h := Real.cosh_le_exp_half_sq y
  rw [Real.cosh_eq] at h
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp; linarith
  · simp; linarith

/-- Moment generating function bound behind Khintchine's inequality in Appendix G.1
[app:relative-local-law-proof]: for `W ≥ 0` and coefficients `x k` invariant under the sign flips
at the coordinates of `S`,
`Σ_s W(s) exp(Σ_{k ∈ S} s_k x_k(s)) ≤ Σ_s W(s) exp(½ Σ_{k ∈ S} x_k(s)²)`. -/
private lemma rc_mgf (S : Finset κ) :
    ∀ (W : (κ → ℤˣ) → ℝ) (x : κ → (κ → ℤˣ) → ℝ), (∀ s, 0 ≤ W s) →
      (∀ j ∈ S, ∀ s, W (rcFlip j s) = W s) →
      (∀ k ∈ S, ∀ j ∈ S, ∀ s, x k (rcFlip j s) = x k s) →
      ∑ s, W s * Real.exp (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * x k s) ≤
        ∑ s, W s * Real.exp (1 / 2 * ∑ k ∈ S, x k s ^ 2) := by
  induction S using Finset.induction_on with
  | empty => intro W x _ _ _; simp
  | insert j S hj ih =>
    intro W x hW hWi hx
    set T : (κ → ℤˣ) → ℝ := fun s => Real.exp (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * x k s) with hT
    have hjS : j ∈ insert j S := Finset.mem_insert_self j S
    have hTi : ∀ s, T (rcFlip j s) = T s := by
      intro s
      simp only [hT]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkj : k ≠ j := fun h => hj (h ▸ hk)
      rw [rcFlip_ne j k s hkj, hx k (Finset.mem_insert_of_mem hk) j hjS]
    set F : (κ → ℤˣ) → ℝ :=
      fun s => W s * T s * Real.exp ((((s j : ℤˣ) : ℤ) : ℝ) * x j s) with hF
    have h1 : ∑ s, W s * Real.exp (∑ k ∈ insert j S, (((s k : ℤˣ) : ℤ) : ℝ) * x k s) =
        ∑ s, F s := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_insert hj, Real.exp_add]; simp only [hF, hT]; ring
    have h2 : ∑ s, F (rcFlip j s) = ∑ s, F s := Equiv.sum_comp (rcFlip j) F
    have h3 : ∀ s, F s + F (rcFlip j s) ≤ 2 * (W s * T s * Real.exp (x j s ^ 2 / 2)) := by
      intro s
      have hxj : x j (rcFlip j s) = x j s := hx j hjS j hjS s
      have hFf : F (rcFlip j s) =
          W s * T s * Real.exp (-((((s j : ℤˣ) : ℤ) : ℝ) * x j s)) := by
        simp only [hF]
        rw [hWi j hjS, hTi, hxj, rcFlip_self]
        congr 2; ring
      rw [hFf]
      have := rc_exp_pair (s j) (x j s)
      have hnn : 0 ≤ W s * T s := mul_nonneg (hW s) (Real.exp_nonneg _)
      calc F s + W s * T s * Real.exp (-((((s j : ℤˣ) : ℤ) : ℝ) * x j s))
          = W s * T s * (Real.exp ((((s j : ℤˣ) : ℤ) : ℝ) * x j s) +
              Real.exp (-((((s j : ℤˣ) : ℤ) : ℝ) * x j s))) := by simp only [hF]; ring
        _ ≤ W s * T s * (2 * Real.exp (x j s ^ 2 / 2)) := mul_le_mul_of_nonneg_left this hnn
        _ = _ := by ring
    have h4 : ∑ s, F s ≤ ∑ s, W s * Real.exp (x j s ^ 2 / 2) * T s := by
      have : 2 * ∑ s, F s ≤ 2 * ∑ s, W s * Real.exp (x j s ^ 2 / 2) * T s := by
        calc 2 * ∑ s, F s = ∑ s, (F s + F (rcFlip j s)) := by
              rw [Finset.sum_add_distrib, h2]; ring
          _ ≤ ∑ s, 2 * (W s * T s * Real.exp (x j s ^ 2 / 2)) := Finset.sum_le_sum fun s _ => h3 s
          _ = 2 * ∑ s, W s * Real.exp (x j s ^ 2 / 2) * T s := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_; ring
      linarith
    have h5 := ih (fun s => W s * Real.exp (x j s ^ 2 / 2)) x
      (fun s => mul_nonneg (hW s) (Real.exp_nonneg _))
      (fun i hi s => by
        rw [hWi i (Finset.mem_insert_of_mem hi),
          hx j hjS i (Finset.mem_insert_of_mem hi)])
      (fun k hk i hi => hx k (Finset.mem_insert_of_mem hk) i (Finset.mem_insert_of_mem hi))
    rw [h1]
    refine h4.trans (h5.trans (le_of_eq (Finset.sum_congr rfl fun s _ => ?_)))
    rw [Finset.sum_insert hj, mul_add, Real.exp_add]
    have : (1 / 2 * x j s ^ 2) = x j s ^ 2 / 2 := by ring
    rw [this]; ring

/-- `u^{2n} ≤ (2n)! (e^u + e^{-u})`. -/
private lemma rc_pow_le_exp (u : ℝ) (n : ℕ) :
    u ^ (2 * n) ≤ (2 * n).factorial * (Real.exp u + Real.exp (-u)) := by
  have h := Real.pow_div_factorial_le_exp |u| (abs_nonneg u) (2 * n)
  have hf : (0 : ℝ) < (2 * n).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_iff₀ hf] at h
  have h2 : |u| ^ (2 * n) = u ^ (2 * n) := (Even.pow_abs ⟨n, by ring⟩ u)
  have h3 : Real.exp |u| ≤ Real.exp u + Real.exp (-u) := by
    rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; linarith [Real.exp_pos (-u)]
    · rw [h]; linarith [Real.exp_pos u]
  rw [h2] at h
  calc u ^ (2 * n) ≤ Real.exp |u| * (2 * n).factorial := h
    _ ≤ (Real.exp u + Real.exp (-u)) * (2 * n).factorial :=
        mul_le_mul_of_nonneg_right h3 hf.le
    _ = _ := by ring

/-- Khintchine's inequality of Appendix G.1 [app:relative-local-law-proof] with real coefficients
`x k` that are invariant under the sign flips at the coordinates of `S`:
`Σ_s (Σ_{k ∈ S} s_k x_k(s))^{2p} ≤ 2 e^{1/2} (2p)! Σ_s (Σ_{k ∈ S} x_k(s)²)^p`. -/
private lemma rc_khin_real (p : ℕ) (S : Finset κ) (x : κ → (κ → ℤˣ) → ℝ)
    (hx : ∀ k ∈ S, ∀ j ∈ S, ∀ s, x k (rcFlip j s) = x k s) :
    ∑ s, (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * x k s) ^ (2 * p) ≤
      2 * Real.exp (1 / 2) * (2 * p).factorial * ∑ s, (∑ k ∈ S, x k s ^ 2) ^ p := by
  set σ : (κ → ℤˣ) → ℝ := fun s => Real.sqrt (∑ k ∈ S, x k s ^ 2) with hσ
  set z : κ → (κ → ℤˣ) → ℝ := fun k s => x k s / σ s with hz
  have hσi : ∀ j ∈ S, ∀ s, σ (rcFlip j s) = σ s := by
    intro j hj s
    simp only [hσ]
    congr 1
    exact Finset.sum_congr rfl fun k hk => by rw [hx k hk j hj]
  have hzi : ∀ k ∈ S, ∀ j ∈ S, ∀ s, z k (rcFlip j s) = z k s := by
    intro k hk j hj s
    simp only [hz]
    rw [hx k hk j hj, hσi j hj]
  have hW : ∀ s, 0 ≤ σ s ^ (2 * p) := fun s => by positivity
  have hWi : ∀ j ∈ S, ∀ s, σ (rcFlip j s) ^ (2 * p) = σ s ^ (2 * p) := by
    intro j hj s; rw [hσi j hj]
  have hm1 := rc_mgf S (fun s => σ s ^ (2 * p)) z hW hWi hzi
  have hm2 := rc_mgf S (fun s => σ s ^ (2 * p)) (fun k s => -z k s) hW hWi
    (fun k hk j hj s => by rw [hzi k hk j hj])
  have hσ2 : ∀ s, σ s ^ 2 = ∑ k ∈ S, x k s ^ 2 := fun s =>
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hz2 : ∀ s, ∑ k ∈ S, z k s ^ 2 ≤ 1 := by
    intro s
    simp only [hz, div_pow]
    rw [← Finset.sum_div, hσ2]
    by_cases h : ∑ k ∈ S, x k s ^ 2 = 0
    · simp [h]
    · rw [div_self h]
  have hpt : ∀ s, (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * x k s) ^ (2 * p) ≤
      (2 * p).factorial * (σ s ^ (2 * p) * Real.exp (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * z k s) +
        σ s ^ (2 * p) * Real.exp (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * (-z k s))) := by
    intro s
    by_cases h : σ s = 0
    · have hx0 : ∀ k ∈ S, x k s = 0 := by
        intro k hk
        have h0 : ∑ k ∈ S, x k s ^ 2 = 0 := by rw [← hσ2 s, h]; ring
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h0 k hk
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      have hy : ∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * x k s = 0 :=
        Finset.sum_eq_zero fun k hk => by rw [hx0 k hk, mul_zero]
      have hz0 : ∀ k, z k s = 0 := fun k => by simp [hz, h]
      simp only [hy, h, hz0, mul_zero, Finset.sum_const_zero, neg_zero, Real.exp_zero, mul_one]
      have hf : (1 : ℝ) ≤ (2 * p).factorial := by exact_mod_cast Nat.factorial_pos _
      have hnn : (0 : ℝ) ≤ 0 ^ (2 * p) := by positivity
      nlinarith
    · have hpos : 0 < σ s := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h)
      have hu : ∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * x k s =
          σ s * ∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * z k s := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hz]; field_simp
      have hneg : ∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * (-z k s) =
          -∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * z k s := by
        rw [← Finset.sum_neg_distrib]; simp
      rw [hu, hneg, mul_pow]
      have := mul_le_mul_of_nonneg_left
        (rc_pow_le_exp (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * z k s) p) (hW s)
      calc _ ≤ _ := this
        _ = _ := by ring
  have hb1 : ∑ s, σ s ^ (2 * p) * Real.exp (1 / 2 * ∑ k ∈ S, z k s ^ 2) ≤
      ∑ s, σ s ^ (2 * p) * Real.exp (1 / 2) :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith [hz2 s])) (hW s)
  have hb2 : ∑ s, σ s ^ (2 * p) * Real.exp (1 / 2 * ∑ k ∈ S, (-z k s) ^ 2) ≤
      ∑ s, σ s ^ (2 * p) * Real.exp (1 / 2) :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by simp only [neg_sq]; linarith [hz2 s])) (hW s)
  have hσp : ∀ s, σ s ^ (2 * p) = (∑ k ∈ S, x k s ^ 2) ^ p := fun s => by
    rw [pow_mul, hσ2]
  have hf : (0 : ℝ) ≤ (2 * p).factorial := by positivity
  calc _ ≤ ∑ s, ((2 * p).factorial : ℝ) *
        (σ s ^ (2 * p) * Real.exp (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * z k s) +
          σ s ^ (2 * p) * Real.exp (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * (-z k s))) :=
        Finset.sum_le_sum fun s _ => hpt s
    _ = (2 * p).factorial *
        (∑ s, σ s ^ (2 * p) * Real.exp (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * z k s) +
          ∑ s, σ s ^ (2 * p) * Real.exp (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * (-z k s))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (2 * p).factorial * (∑ s, σ s ^ (2 * p) * Real.exp (1 / 2) +
          ∑ s, σ s ^ (2 * p) * Real.exp (1 / 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hm1.trans hb1) (hm2.trans hb2)) hf
    _ = 2 * Real.exp (1 / 2) * (2 * p).factorial * ∑ s, (∑ k ∈ S, x k s ^ 2) ^ p := by
        simp only [hσp, ← Finset.sum_mul]
        ring

/-- `(u + v)^p ≤ 2^p (u^p + v^p)` for `u, v ≥ 0`. -/
private lemma rc_add_pow_le (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (p : ℕ) :
    (u + v) ^ p ≤ 2 ^ p * (u ^ p + v ^ p) := by
  have hup : 0 ≤ u ^ p := pow_nonneg hu p
  have hvp : 0 ≤ v ^ p := pow_nonneg hv p
  rcases le_total u v with h | h
  · calc (u + v) ^ p ≤ (2 * v) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
      _ = 2 ^ p * v ^ p := mul_pow _ _ _
      _ ≤ _ := by gcongr; linarith
  · calc (u + v) ^ p ≤ (2 * u) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
      _ = 2 ^ p * u ^ p := mul_pow _ _ _
      _ ≤ _ := by gcongr; linarith

/-- Khintchine's inequality of Appendix G.1 [app:relative-local-law-proof] with complex
coefficients `a k` that are invariant under the sign flips at the coordinates of `S`:
`Σ_s ‖Σ_{k ∈ S} s_k a_k(s)‖^{2p} ≤ 2^{p+2} e^{1/2} (2p)! Σ_s (Σ_{k ∈ S} ‖a_k(s)‖²)^p`. -/
private lemma rc_khin_cplx (p : ℕ) (S : Finset κ) (a : κ → (κ → ℤˣ) → ℂ)
    (ha : ∀ k ∈ S, ∀ j ∈ S, ∀ s, a k (rcFlip j s) = a k s) :
    ∑ s, ‖∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℂ) * a k s‖ ^ (2 * p) ≤
      2 ^ (p + 2) * (Real.exp (1 / 2) * (2 * p).factorial) * ∑ s, (∑ k ∈ S, ‖a k s‖ ^ 2) ^ p := by
  have hre := rc_khin_real p S (fun k s => (a k s).re)
    (fun k hk j hj s => by rw [ha k hk j hj])
  have him := rc_khin_real p S (fun k s => (a k s).im)
    (fun k hk j hj s => by rw [ha k hk j hj])
  have hr : ∀ s, (∑ k ∈ S, (a k s).re ^ 2) ^ p ≤ (∑ k ∈ S, ‖a k s‖ ^ 2) ^ p := by
    intro s
    refine pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_le_sum fun k _ => ?_) p
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (a k s).im]
  have hi : ∀ s, (∑ k ∈ S, (a k s).im ^ 2) ^ p ≤ (∑ k ∈ S, ‖a k s‖ ^ 2) ^ p := by
    intro s
    refine pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_le_sum fun k _ => ?_) p
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (a k s).re]
  have hK : (0 : ℝ) ≤ 2 * Real.exp (1 / 2) * (2 * p).factorial := by positivity
  have hpt : ∀ s, ‖∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℂ) * a k s‖ ^ (2 * p) ≤
      2 ^ p * ((∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * (a k s).re) ^ (2 * p) +
        (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * (a k s).im) ^ (2 * p)) := by
    intro s
    set Q := ∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℂ) * a k s with hQ
    have h1 : Q.re = ∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * (a k s).re := by
      simp [hQ, Complex.re_sum]
    have h2 : Q.im = ∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * (a k s).im := by
      simp [hQ, Complex.im_sum]
    rw [← h1, ← h2, pow_mul, Complex.sq_norm, Complex.normSq_apply]
    have := rc_add_pow_le (Q.re ^ 2) (Q.im ^ 2) (sq_nonneg _) (sq_nonneg _) p
    rw [← pow_mul, ← pow_mul] at this
    calc _ = (Q.re ^ 2 + Q.im ^ 2) ^ p := by ring_nf
      _ ≤ _ := this
  calc _ ≤ ∑ s, 2 ^ p * ((∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * (a k s).re) ^ (2 * p) +
        (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * (a k s).im) ^ (2 * p)) :=
        Finset.sum_le_sum fun s _ => hpt s
    _ = 2 ^ p * (∑ s, (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * (a k s).re) ^ (2 * p) +
        ∑ s, (∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℝ) * (a k s).im) ^ (2 * p)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 ^ p * (2 * Real.exp (1 / 2) * (2 * p).factorial * ∑ s, (∑ k ∈ S, ‖a k s‖ ^ 2) ^ p +
        2 * Real.exp (1 / 2) * (2 * p).factorial * ∑ s, (∑ k ∈ S, ‖a k s‖ ^ 2) ^ p) := by
        gcongr
        · exact hre.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => hr s) hK)
        · exact him.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => hi s) hK)
    _ = _ := by ring

/-- The constant `2^{p+2} e^{1/2} (2p)!` of Khintchine's inequality for complex coefficients. -/
private def rcK (p : ℕ) : ℝ := 2 ^ (p + 2) * (Real.exp (1 / 2) * (2 * p).factorial)

private lemma rcK_pos (p : ℕ) : 0 < rcK p := by unfold rcK; positivity

/-- A weighted power mean: for `w, b ≥ 0` with `b k = 0` whenever `w k = 0` and `p ≥ 1`,
`(Σ b)^p ≤ (Σ w)^{p-1} Σ w_k (b_k / w_k)^p`. -/
private lemma rc_wjensen {ι : Type*} (p : ℕ) (hp : 1 ≤ p) (T : Finset ι) (w b : ι → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hb : ∀ k, 0 ≤ b k) (hz : ∀ k, w k = 0 → b k = 0) :
    (∑ k ∈ T, b k) ^ p ≤ (∑ k ∈ T, w k) ^ (p - 1) * ∑ k ∈ T, w k * (b k / w k) ^ p := by
  set A := ∑ k ∈ T, w k with hA
  by_cases hA0 : A = 0
  · have h0 : ∀ k ∈ T, w k = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hw k)).mp hA0
    have hb0 : ∑ k ∈ T, b k = 0 := Finset.sum_eq_zero fun k hk => hz k (h0 k hk)
    rw [hb0, zero_pow (by omega)]
    refine mul_nonneg (pow_nonneg (Finset.sum_nonneg fun k _ => hw k) _)
      (Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (pow_nonneg (div_nonneg (hb k) (hw k)) p))
  · have hApos : 0 < A := lt_of_le_of_ne (Finset.sum_nonneg fun k _ => hw k) (Ne.symm hA0)
    have h := Real.pow_arith_mean_le_arith_mean_pow T (fun k => w k / A) (fun k => b k / w k)
      (fun k _ => div_nonneg (hw k) hApos.le) (by rw [← Finset.sum_div]; exact div_self hA0)
      (fun k _ => div_nonneg (hb k) (hw k)) p
    have e1 : ∑ k ∈ T, w k / A * (b k / w k) = (∑ k ∈ T, b k) / A := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h0 : w k = 0
      · simp [h0, hz k h0]
      · field_simp
    rw [e1, div_pow, div_le_iff₀ (pow_pos hApos p)] at h
    refine h.trans (le_of_eq ?_)
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp

/-- The chaos bound for a fixed splitting `S`, `Sᶜ` of the index set and `p ≥ 1`:
`Σ_s ‖Σ_{k ∈ S} s_k Σ_{l ∈ Sᶜ} c_kl s_l‖^{2p} ≤ K² 2^{|κ|} (Σ_{k ∈ S} Σ_{l ∈ Sᶜ} ‖c_kl‖²)^p` with
`K = rcK p` (Khintchine in the signs of `S`, then in those of `Sᶜ`, and a weighted power mean in
`k`). -/
private lemma rc_fixed (p : ℕ) (hp : 1 ≤ p) (S : Finset κ) (c : κ → κ → ℂ) :
    ∑ s : κ → ℤˣ, ‖∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℂ) *
        ∑ l ∈ Sᶜ, c k l * (((s l : ℤˣ) : ℤ) : ℂ)‖ ^ (2 * p) ≤
      rcK p * (rcK p * (Fintype.card (κ → ℤˣ) : ℝ) *
        (∑ k ∈ S, ∑ l ∈ Sᶜ, ‖c k l‖ ^ 2) ^ p) := by
  set a : κ → (κ → ℤˣ) → ℂ := fun k s => ∑ l ∈ Sᶜ, c k l * (((s l : ℤˣ) : ℤ) : ℂ) with ha
  set w : κ → ℝ := fun k => ∑ l ∈ Sᶜ, ‖c k l‖ ^ 2 with hw
  set N : ℝ := (Fintype.card (κ → ℤˣ) : ℝ) with hN
  have hai : ∀ k ∈ S, ∀ j ∈ S, ∀ s, a k (rcFlip j s) = a k s := by
    intro k _ j hj s
    simp only [ha]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlj : l ≠ j := fun h => (Finset.mem_compl.mp hl) (h ▸ hj)
    rw [rcFlip_ne j l s hlj]
  have h1 := rc_khin_cplx p S a hai
  -- the bound for each `a k`
  have hk : ∀ k, ∑ s, (‖a k s‖ ^ 2) ^ p ≤ rcK p * (N * w k ^ p) := by
    intro k
    have h : ∑ s : κ → ℤˣ, ‖∑ l ∈ Sᶜ, (((s l : ℤˣ) : ℤ) : ℂ) * c k l‖ ^ (2 * p) ≤
        rcK p * ∑ s : κ → ℤˣ, (∑ l ∈ Sᶜ, ‖c k l‖ ^ 2) ^ p :=
      rc_khin_cplx p Sᶜ (fun l _ => c k l) (fun _ _ _ _ _ => rfl)
    have hs : ∀ s : κ → ℤˣ, ∑ l ∈ Sᶜ, (((s l : ℤˣ) : ℤ) : ℂ) * c k l = a k s := by
      intro s
      simp only [ha]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    simp only [hs] at h
    have h2 : ∀ s : κ → ℤˣ, (‖a k s‖ ^ 2) ^ p = ‖a k s‖ ^ (2 * p) := fun s => (pow_mul _ _ _).symm
    simp only [h2]
    refine h.trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hw, hN]
  have hwnn : ∀ k, 0 ≤ w k := fun k => Finset.sum_nonneg fun l _ => by positivity
  have hbnn : ∀ k s, 0 ≤ ‖a k s‖ ^ 2 := fun _ _ => by positivity
  have hwz : ∀ k s, w k = 0 → ‖a k s‖ ^ 2 = 0 := by
    intro k s h0
    have hc : ∀ l ∈ Sᶜ, c k l = 0 := by
      intro l hl
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg ‖c k l‖)).mp h0 l hl
      simpa using this
    have : a k s = 0 := Finset.sum_eq_zero fun l hl => by rw [hc l hl, zero_mul]
    simp [this]
  have h2 : ∀ s, (∑ k ∈ S, ‖a k s‖ ^ 2) ^ p ≤
      (∑ k ∈ S, w k) ^ (p - 1) * ∑ k ∈ S, w k * (‖a k s‖ ^ 2 / w k) ^ p :=
    fun s => rc_wjensen p hp S w (fun k => ‖a k s‖ ^ 2) hwnn (fun k => hbnn k s)
      (fun k => hwz k s)
  have h3 : ∀ k, ∑ s, w k * (‖a k s‖ ^ 2 / w k) ^ p ≤ rcK p * N * w k := by
    intro k
    by_cases h0 : w k = 0
    · simp [h0]
    · have hpos : 0 < w k := lt_of_le_of_ne (hwnn k) (Ne.symm h0)
      calc ∑ s, w k * (‖a k s‖ ^ 2 / w k) ^ p = (w k / w k ^ p) * ∑ s, (‖a k s‖ ^ 2) ^ p := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [div_pow]; ring
        _ ≤ (w k / w k ^ p) * (rcK p * (N * w k ^ p)) :=
            mul_le_mul_of_nonneg_left (hk k) (by positivity)
        _ = rcK p * N * w k := by field_simp
  have hA : 0 ≤ ∑ k ∈ S, w k := Finset.sum_nonneg fun k _ => hwnn k
  calc _ ≤ rcK p * ∑ s, (∑ k ∈ S, ‖a k s‖ ^ 2) ^ p := h1
    _ ≤ rcK p * ∑ s, ((∑ k ∈ S, w k) ^ (p - 1) * ∑ k ∈ S, w k * (‖a k s‖ ^ 2 / w k) ^ p) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => h2 s) (rcK_pos p).le
    _ = rcK p * ((∑ k ∈ S, w k) ^ (p - 1) * ∑ k ∈ S, ∑ s, w k * (‖a k s‖ ^ 2 / w k) ^ p) := by
        rw [← Finset.mul_sum, Finset.sum_comm (s := (Finset.univ : Finset (κ → ℤˣ)))]
    _ ≤ rcK p * ((∑ k ∈ S, w k) ^ (p - 1) * ∑ k ∈ S, rcK p * N * w k) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun k _ => h3 k) (pow_nonneg hA _)) (rcK_pos p).le
    _ = _ := by
        rw [← Finset.mul_sum]
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        ring

/-- A function that is odd under the sign flip at `j` has sum zero over all signs. -/
private lemma rc_sum_flip (j : κ) (f : (κ → ℤˣ) → ℝ) (hf : ∀ t, f (rcFlip j t) = -f t) :
    ∑ t, f t = 0 := by
  have h := Equiv.sum_comp (rcFlip j) f
  simp only [hf, Finset.sum_neg_distrib] at h
  linarith

/-- For `k ≠ l`, a quarter of the selectors `t` have `t k = 1` and `t l ≠ 1`. -/
private lemma rc_count (k l : κ) (hkl : k ≠ l) :
    ∑ t : κ → ℤˣ, (if t k = 1 ∧ t l ≠ 1 then (1 : ℝ) else 0) =
      (Fintype.card (κ → ℤˣ) : ℝ) / 4 := by
  have hpt : ∀ t : κ → ℤˣ, (if t k = 1 ∧ t l ≠ 1 then (1 : ℝ) else 0) =
      1 / 4 + 1 / 4 * (((t k : ℤˣ) : ℤ) : ℝ) - 1 / 4 * (((t l : ℤˣ) : ℤ) : ℝ) -
        1 / 4 * ((((t k : ℤˣ) : ℤ) : ℝ) * (((t l : ℤˣ) : ℤ) : ℝ)) := by
    intro t
    rcases Int.units_eq_one_or (t k) with hk | hk <;>
      rcases Int.units_eq_one_or (t l) with hl | hl <;> simp [hk, hl]
    all_goals norm_num
  have e1 : ∑ t : κ → ℤˣ, (((t k : ℤˣ) : ℤ) : ℝ) = 0 :=
    rc_sum_flip k _ (fun t => by rw [rcFlip_self])
  have e2 : ∑ t : κ → ℤˣ, (((t l : ℤˣ) : ℤ) : ℝ) = 0 :=
    rc_sum_flip l _ (fun t => by rw [rcFlip_self])
  have e3 : ∑ t : κ → ℤˣ, ((((t k : ℤˣ) : ℤ) : ℝ) * (((t l : ℤˣ) : ℤ) : ℝ)) = 0 :=
    rc_sum_flip k (fun t => (((t k : ℤˣ) : ℤ) : ℝ) * (((t l : ℤˣ) : ℤ) : ℝ)) (fun t => by
      rw [rcFlip_self, rcFlip_ne k l t (Ne.symm hkl)]; ring)
  simp only [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, e1, e2, e3,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The chaos form `Σ_{k ≠ l} c_kl s_k s_l`. -/
private def rcQ (c : κ → κ → ℂ) (s : κ → ℤˣ) : ℂ :=
  ∑ k, ∑ l, (if k = l then 0 else c k l * (((s k : ℤˣ) : ℤ) : ℂ) * (((s l : ℤˣ) : ℤ) : ℂ))

/-- The set of coordinates where a selector `t` is `1`. -/
private def rcSet (t : κ → ℤˣ) : Finset κ := Finset.univ.filter fun k => t k = 1

/-- The part of the chaos form with first index in `S` and second index outside `S`. -/
private def rcQS (S : Finset κ) (c : κ → κ → ℂ) (s : κ → ℤˣ) : ℂ :=
  ∑ k ∈ S, (((s k : ℤˣ) : ℤ) : ℂ) * ∑ l ∈ Sᶜ, c k l * (((s l : ℤˣ) : ℤ) : ℂ)

/-- Decoupling by a random subset (Appendix G.1 [app:relative-local-law-proof]): averaging the
split forms over the selectors `t` gives the chaos form, `Σ_t Q_{S(t)} = (2^{|κ|} / 4) Q`. -/
private lemma rc_decomp (c : κ → κ → ℂ) (s : κ → ℤˣ) :
    ∑ t, rcQS (rcSet t) c s = (((Fintype.card (κ → ℤˣ) : ℝ) / 4 : ℝ) : ℂ) * rcQ c s := by
  have e1 : ∀ t : κ → ℤˣ, rcQS (rcSet t) c s = ∑ k, ∑ l,
      (((if t k = 1 ∧ t l ≠ 1 then (1 : ℝ) else 0 : ℝ) : ℂ) *
        (c k l * (((s k : ℤˣ) : ℤ) : ℂ) * (((s l : ℤˣ) : ℤ) : ℂ))) := by
    intro t
    unfold rcQS
    have hc : (rcSet t)ᶜ = Finset.univ.filter fun l => t l ≠ 1 := by
      ext l; simp [rcSet]
    rw [hc]
    simp only [rcSet, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : t k = 1
    · simp only [hk, ↓reduceIte, true_and]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : t l = 1 <;> simp [hl]
      all_goals ring
    · simp [hk]
  simp only [e1]
  rw [Finset.sum_comm]
  calc _ = ∑ k, ∑ l, (((Fintype.card (κ → ℤˣ) : ℝ) / 4 : ℝ) : ℂ) *
          (if k = l then 0 else
            c k l * (((s k : ℤˣ) : ℤ) : ℂ) * (((s l : ℤˣ) : ℤ) : ℂ)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        by_cases h : k = l
        · subst h; simp
        · rw [← Finset.sum_mul, ← Complex.ofReal_sum, rc_count k l h]
          simp [h]
    _ = _ := by
        unfold rcQ
        simp only [← Finset.mul_sum]

/-- Jensen's inequality for the decoupling: `‖Q‖^{2p} ≤ 16^p avg_t ‖Q_{S(t)}‖^{2p}`. -/
private lemma rc_jensen (p : ℕ) (c : κ → κ → ℂ) (s : κ → ℤˣ) :
    ‖rcQ c s‖ ^ (2 * p) ≤ 16 ^ p *
      ((Fintype.card (κ → ℤˣ) : ℝ)⁻¹ * ∑ t, ‖rcQS (rcSet t) c s‖ ^ (2 * p)) := by
  set N : ℝ := (Fintype.card (κ → ℤˣ) : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hQ : rcQ c s = ((4 / N : ℝ) : ℂ) * ∑ t, rcQS (rcSet t) c s := by
    rw [rc_decomp, ← mul_assoc, ← Complex.ofReal_mul]
    have : 4 / N * (N / 4) = 1 := by field_simp
    rw [this]; simp
  have h1 : ‖rcQ c s‖ ≤ 4 * ∑ t, N⁻¹ * ‖rcQS (rcSet t) c s‖ := by
    rw [hQ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc 4 / N * ‖∑ t, rcQS (rcSet t) c s‖ ≤ 4 / N * ∑ t, ‖rcQS (rcSet t) c s‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring
  have h2 := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun _ : κ → ℤˣ => N⁻¹)
    (fun t => ‖rcQS (rcSet t) c s‖) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN]; field_simp)
    (fun _ _ => norm_nonneg _)
    (2 * p)
  calc ‖rcQ c s‖ ^ (2 * p) ≤ (4 * ∑ t, N⁻¹ * ‖rcQS (rcSet t) c s‖) ^ (2 * p) :=
        pow_le_pow_left₀ (norm_nonneg _) h1 _
    _ = 16 ^ p * (∑ t, N⁻¹ * ‖rcQS (rcSet t) c s‖) ^ (2 * p) := by
        rw [mul_pow, pow_mul]; norm_num
    _ ≤ 16 ^ p * ∑ t, N⁻¹ * ‖rcQS (rcSet t) c s‖ ^ (2 * p) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by rw [← Finset.mul_sum]

/-- The chaos bound for `p ≥ 1` with the constant `16^p K²`, `K = rcK p`. -/
private lemma rc_chaos (p : ℕ) (hp : 1 ≤ p) (c : κ → κ → ℂ) :
    (Fintype.card (κ → ℤˣ) : ℝ)⁻¹ * ∑ s : κ → ℤˣ, ‖rcQ c s‖ ^ (2 * p) ≤
      16 ^ p * rcK p ^ 2 * (∑ k, ∑ l, if k = l then 0 else ‖c k l‖ ^ 2) ^ p := by
  set N : ℝ := (Fintype.card (κ → ℤˣ) : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  set σ2 : ℝ := ∑ k, ∑ l, if k = l then (0 : ℝ) else ‖c k l‖ ^ 2 with hσ2
  have hσ : ∀ S : Finset κ, ∑ k ∈ S, ∑ l ∈ Sᶜ, ‖c k l‖ ^ 2 ≤ σ2 := by
    intro S
    calc ∑ k ∈ S, ∑ l ∈ Sᶜ, ‖c k l‖ ^ 2
        = ∑ k ∈ S, ∑ l ∈ Sᶜ, (if k = l then (0 : ℝ) else ‖c k l‖ ^ 2) := by
          refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
          have : k ≠ l := fun h => (Finset.mem_compl.mp hl) (h ▸ hk)
          simp [this]
      _ ≤ ∑ k ∈ S, ∑ l, (if k = l then (0 : ℝ) else ‖c k l‖ ^ 2) :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) (fun l _ _ => by split_ifs <;> positivity)
      _ ≤ σ2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun k _ _ => Finset.sum_nonneg fun l _ => by split_ifs <;> positivity)
  have hfix : ∀ t : κ → ℤˣ, ∑ s, ‖rcQS (rcSet t) c s‖ ^ (2 * p) ≤ rcK p * (rcK p * N * σ2 ^ p) := by
    intro t
    refine (rc_fixed p hp (rcSet t) c).trans ?_
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => by positivity)
        (hσ _) p) (mul_nonneg (rcK_pos p).le hNpos.le)) (rcK_pos p).le
  calc N⁻¹ * ∑ s : κ → ℤˣ, ‖rcQ c s‖ ^ (2 * p)
      ≤ N⁻¹ * ∑ s : κ → ℤˣ, 16 ^ p * (N⁻¹ * ∑ t, ‖rcQS (rcSet t) c s‖ ^ (2 * p)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => rc_jensen p c s) (by positivity)
    _ = 16 ^ p * (N⁻¹ * (N⁻¹ * ∑ t : κ → ℤˣ, ∑ s, ‖rcQS (rcSet t) c s‖ ^ (2 * p))) := by
        simp only [← Finset.mul_sum]
        rw [Finset.sum_comm]; ring
    _ ≤ 16 ^ p * (N⁻¹ * (N⁻¹ * ∑ t : κ → ℤˣ, rcK p * (rcK p * N * σ2 ^ p))) := by
        gcongr with t
        exact hfix t
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN]
        field_simp

end RademacherChaosAux

/-- Order-two Rademacher chaos bound of Appendix G.1 [app:relative-local-law-proof]
(decoupling, Khintchine, Minkowski), with random signs in place of uniform phases:
`E_s |Σ_{k ≠ l} c_kl s_k s_l|^{2p} ≤ C (Σ_{k ≠ l} |c_kl|²)^p`. -/
theorem rademacher_chaos (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (c : κ → κ → ℂ),
      (Fintype.card (κ → ℤˣ) : ℝ)⁻¹ *
          ∑ s : κ → ℤˣ, ‖∑ k, ∑ l,
            (if k = l then 0 else c k l * ((s k : ℤ) : ℂ) * ((s l : ℤ) : ℂ))‖ ^ (2 * p) ≤
        C * (∑ k, ∑ l, if k = l then 0 else ‖c k l‖ ^ 2) ^ p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · refine ⟨1, one_pos, fun {κ} _ _ c => ?_⟩
    simp [Finset.sum_const, Finset.card_univ]
  · refine ⟨16 ^ p * rcK p ^ 2, by have := rcK_pos p; positivity, fun {κ} _ _ c => ?_⟩
    exact rc_chaos p hp c

end LSBA
