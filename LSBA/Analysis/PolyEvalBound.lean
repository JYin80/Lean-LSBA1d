import Mathlib

/-!
# Size and Lipschitz bounds for evaluations of polynomials

For a complex multivariate polynomial `p` and points `x`, `y` whose coordinates on the variables
of `p` have modulus at most `B`: `|p(x)| ≤ Σ_d |p_d| B^{|d|}` and
`|p(x) − p(y)| ≤ (Σ_d |p_d| |d| B^{|d|−1}) δ` when `|x_v − y_v| ≤ δ` on the variables of `p`,
where `|d|` is the total degree of the monomial `d`.
-/

open MvPolynomial

noncomputable section

namespace LSBA

/-- `|p(x)| ≤ Σ_d |p_d| B^{|d|}` when `|x_v| ≤ B` for every variable `v` of `p`. -/
theorem norm_aeval_le_sum_coeff {σ : Type*} (p : MvPolynomial σ ℂ) {x : σ → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hx : ∀ v ∈ p.vars, ‖x v‖ ≤ B) :
    ‖aeval x p‖ ≤ ∑ d ∈ p.support, ‖p.coeff d‖ * B ^ Finsupp.degree d := by
  classical
  have hmono : ∀ d ∈ p.support, ‖d.prod fun i k => x i ^ k‖ ≤ B ^ Finsupp.degree d := by
    intro d hd
    rw [Finsupp.prod, norm_prod]
    calc ∏ i ∈ d.support, ‖x i ^ d i‖ ≤ ∏ i ∈ d.support, B ^ d i := by
          refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi => ?_)
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _)
            (hx i ((mem_vars_iff_mem_support i).2 ⟨d, hd, hi⟩)) _
      _ = B ^ Finsupp.degree d := by
          rw [Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  rw [aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply, norm_mul]
  exact mul_le_mul_of_nonneg_left (hmono d hd) (norm_nonneg _)

/-- `|p(x) − p(y)| ≤ (Σ_d |p_d| |d| B^{|d|−1}) δ` when `|x_v|, |y_v| ≤ B` and `|x_v − y_v| ≤ δ`
for every variable `v` of `p`. -/
theorem norm_aeval_sub_aeval_le {σ : Type*} (p : MvPolynomial σ ℂ) {x y : σ → ℂ} {B δ : ℝ}
    (hB : 0 ≤ B) (hx : ∀ v ∈ p.vars, ‖x v‖ ≤ B) (hy : ∀ v ∈ p.vars, ‖y v‖ ≤ B)
    (hxy : ∀ v ∈ p.vars, ‖x v - y v‖ ≤ δ) :
    ‖aeval x p - aeval y p‖ ≤
      (∑ d ∈ p.support, ‖p.coeff d‖ * Finsupp.degree d * B ^ (Finsupp.degree d - 1)) * δ := by
  classical
  -- one multiplication step of the telescoping bound
  have step : ∀ (u u' w w' : ℂ) (j l : ℕ), 0 ≤ δ → ‖u‖ ≤ B ^ j → ‖w'‖ ≤ B ^ l →
      ‖u - u'‖ ≤ (j : ℝ) * B ^ (j - 1) * δ → ‖w - w'‖ ≤ (l : ℝ) * B ^ (l - 1) * δ →
      ‖u * w - u' * w'‖ ≤ ((j + l : ℕ) : ℝ) * B ^ (j + l - 1) * δ := by
    intro u u' w w' j l hδ hu hw' huu hww
    have e : u * w - u' * w' = u * (w - w') + (u - u') * w' := by ring
    have h1 : B ^ j * ((l : ℝ) * B ^ (l - 1)) = (l : ℝ) * B ^ (j + l - 1) := by
      rcases Nat.eq_zero_or_pos l with rfl | hl
      · simp
      · obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
        rw [show j + (m + 1) - 1 = j + m by omega, show m + 1 - 1 = m by omega, pow_add]
        ring
    have h2 : (j : ℝ) * B ^ (j - 1) * B ^ l = (j : ℝ) * B ^ (j + l - 1) := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
        rw [show m + 1 + l - 1 = m + l by omega, show m + 1 - 1 = m by omega, pow_add]
        ring
    calc ‖u * w - u' * w'‖ = ‖u * (w - w') + (u - u') * w'‖ := by rw [e]
      _ ≤ ‖u‖ * ‖w - w'‖ + ‖u - u'‖ * ‖w'‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ B ^ j * ((l : ℝ) * B ^ (l - 1) * δ) + ((j : ℝ) * B ^ (j - 1) * δ) * B ^ l := by
          gcongr
      _ = ((j + l : ℕ) : ℝ) * B ^ (j + l - 1) * δ := by
          have : B ^ j * ((l : ℝ) * B ^ (l - 1) * δ) + ((j : ℝ) * B ^ (j - 1) * δ) * B ^ l
              = (B ^ j * ((l : ℝ) * B ^ (l - 1)) + (j : ℝ) * B ^ (j - 1) * B ^ l) * δ := by ring
          rw [this, h1, h2]
          push_cast
          ring
  -- single variable
  have hpow : ∀ (a b : ℂ), 0 ≤ δ → ‖a‖ ≤ B → ‖b‖ ≤ B → ‖a - b‖ ≤ δ → ∀ k : ℕ,
      ‖a ^ k - b ^ k‖ ≤ (k : ℝ) * B ^ (k - 1) * δ := by
    intro a b hδ ha hb hab k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, pow_succ]
        have := step (a ^ k) (b ^ k) a b k 1 hδ (by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ha _)
          (by simpa using hb) ih (by simpa using hab)
        simpa using this
  -- finite product over variables
  have hprod : ∀ (k : σ → ℕ) (s : Finset σ), 0 ≤ δ → (∀ v ∈ s, ‖x v‖ ≤ B) → (∀ v ∈ s, ‖y v‖ ≤ B) →
      (∀ v ∈ s, ‖x v - y v‖ ≤ δ) →
      ‖∏ v ∈ s, x v ^ k v - ∏ v ∈ s, y v ^ k v‖ ≤
        ((∑ v ∈ s, k v : ℕ) : ℝ) * B ^ ((∑ v ∈ s, k v) - 1) * δ := by
    intro k s hδ
    induction s using Finset.induction_on with
    | empty => intros; simp
    | insert w s hw ih =>
        intro hx' hy' hxy'
        rw [Finset.prod_insert hw, Finset.prod_insert hw, Finset.sum_insert hw]
        have hxs : ‖∏ v ∈ s, x v ^ k v‖ ≤ B ^ (∑ v ∈ s, k v) := by
          rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun v hv => ?_)
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hx' v (Finset.mem_insert_of_mem hv)) _
        have hys : ‖∏ v ∈ s, y v ^ k v‖ ≤ B ^ (∑ v ∈ s, k v) := by
          rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun v hv => ?_)
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hy' v (Finset.mem_insert_of_mem hv)) _
        have hxw : ‖x w ^ k w‖ ≤ B ^ k w := by
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hx' w (Finset.mem_insert_self _ _)) _
        have hyw : ‖y w ^ k w‖ ≤ B ^ k w := by
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hy' w (Finset.mem_insert_self _ _)) _
        exact step _ _ _ _ (k w) (∑ v ∈ s, k v) hδ hxw hys
          (hpow _ _ hδ (hx' w (Finset.mem_insert_self _ _)) (hy' w (Finset.mem_insert_self _ _))
            (hxy' w (Finset.mem_insert_self _ _)) _)
          (ih (fun v hv => hx' v (Finset.mem_insert_of_mem hv))
            (fun v hv => hy' v (Finset.mem_insert_of_mem hv))
            (fun v hv => hxy' v (Finset.mem_insert_of_mem hv)))
  have hmono : ∀ d ∈ p.support,
      ‖(d.prod fun i k => x i ^ k) - d.prod fun i k => y i ^ k‖ ≤
        ((Finsupp.degree d : ℕ) : ℝ) * B ^ (Finsupp.degree d - 1) * δ := by
    intro d hd
    have hv : ∀ v ∈ d.support, v ∈ p.vars := fun v hv => (mem_vars_iff_mem_support v).2 ⟨d, hd, hv⟩
    rcases d.support.eq_empty_or_nonempty with h0 | ⟨v0, hv0⟩
    · have hd0 : d = 0 := Finsupp.support_eq_empty.1 h0
      subst hd0
      simp
    · have hδ : 0 ≤ δ := (norm_nonneg _).trans (hxy v0 (hv v0 hv0))
      have := hprod d d.support hδ (fun v h => hx v (hv v h)) (fun v h => hy v (hv v h))
        (fun v h => hxy v (hv v h))
      rw [Finsupp.degree_apply]
      simpa [Finsupp.prod] using this
  have hdiff : aeval x p - aeval y p = ∑ d ∈ p.support,
      p.coeff d * ((d.prod fun i k => x i ^ k) - d.prod fun i k => y i ^ k) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [aeval_monomial, aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply, mul_sub]
  rw [hdiff, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  rw [norm_mul]
  calc ‖p.coeff d‖ * ‖(d.prod fun i k => x i ^ k) - d.prod fun i k => y i ^ k‖
      ≤ ‖p.coeff d‖ * (((Finsupp.degree d : ℕ) : ℝ) * B ^ (Finsupp.degree d - 1) * δ) :=
        mul_le_mul_of_nonneg_left (hmono d hd) (norm_nonneg _)
    _ = _ := by ring

end LSBA
