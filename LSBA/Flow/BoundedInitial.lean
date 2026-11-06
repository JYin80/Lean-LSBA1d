import LSBA.Flow.Realization
import LSBA.Loop.ErrorHierarchy
import LSBA.Flow.Moment
import LSBA.Primitive.Early

/-!
# Lemma 5.3 [fo:lem:bounded-initial] in fixed-time form

The Combes–Thomas bound behind Appendix C.2 [sec:bounded-proof] for block-diagonal perturbations,
the cyclic length of a label word, and Lemma 5.3 [fo:lem:bounded-initial] at each deterministic
`u ∈ [0, 1/2]`: the loop-error component and the entrywise component of (5.22)
[gc:eq:one-step-input], for any primitive family with the initial value, the primitive equation
(5.10) [fo:eq:primitive], the two-loop symmetry and the bound (B.13) [b:eq:early-primitive].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Operator-norm tools for block matrices -/

section BoundedInitialNorms

open scoped Matrix.Norms.L2Operator

/-- An entry is bounded by the operator norm. -/
private theorem boundedInitial_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  have h1 := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j 1)
  rw [← Matrix.cstar_norm_def] at h1
  have h2 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [h2, mul_one] at h1
  refine le_trans ?_ h1
  have h3 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)).ofLp i =
      A i j := by
    rw [Matrix.ofLp_toEuclideanCLM]
    simp [Matrix.mulVec, dotProduct]
  rw [← h3]
  exact PiLp.norm_apply_le _ i

/-- Schur test: row and column sums of the entry norms at most `r` give `‖X‖ ≤ r`. -/
private theorem boundedInitial_schur {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    {r : ℝ} (hr : 0 ≤ r) (hrow : ∀ i, ∑ j, ‖X i j‖ ≤ r) (hcol : ∀ j, ∑ i, ‖X i j‖ ≤ r) :
    ‖X‖ ≤ r := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hr fun v => ?_
  have hsq : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) X v‖ ^ 2 ≤ (r * ‖v‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM, mul_pow, EuclideanSpace.norm_sq_eq]
    have hi : ∀ i, ‖(X *ᵥ v.ofLp) i‖ ^ 2 ≤ r * ∑ j, ‖X i j‖ * ‖v.ofLp j‖ ^ 2 := by
      intro i
      have e1 : ‖(X *ᵥ v.ofLp) i‖ ≤ ∑ j, ‖X i j‖ * ‖v.ofLp j‖ := by
        simp only [Matrix.mulVec, dotProduct]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
      have e2 : (∑ j, ‖X i j‖ * ‖v.ofLp j‖) ^ 2 ≤
          (∑ j, ‖X i j‖) * ∑ j, ‖X i j‖ * ‖v.ofLp j‖ ^ 2 := by
        have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => Real.sqrt ‖X i j‖)
          (fun j => Real.sqrt ‖X i j‖ * ‖v.ofLp j‖)
        have hs : ∀ j, Real.sqrt ‖X i j‖ ^ 2 = ‖X i j‖ := fun j => Real.sq_sqrt (norm_nonneg _)
        simp only [mul_pow, hs, ← mul_assoc] at this
        refine le_trans (le_of_eq ?_) this
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Real.mul_self_sqrt (norm_nonneg _)]
      have e3 : 0 ≤ ∑ j, ‖X i j‖ * ‖v.ofLp j‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => by positivity
      calc ‖(X *ᵥ v.ofLp) i‖ ^ 2 ≤ (∑ j, ‖X i j‖ * ‖v.ofLp j‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) e1 2
        _ ≤ _ := e2
        _ ≤ r * ∑ j, ‖X i j‖ * ‖v.ofLp j‖ ^ 2 := mul_le_mul_of_nonneg_right (hrow i) e3
    calc ∑ i, ‖(X *ᵥ v.ofLp) i‖ ^ 2 ≤ ∑ i, r * ∑ j, ‖X i j‖ * ‖v.ofLp j‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hi i
      _ = r * ∑ j, (∑ i, ‖X i j‖) * ‖v.ofLp j‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
      _ ≤ r * ∑ j, r * ‖v.ofLp j‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hr
          exact mul_le_mul_of_nonneg_right (hcol j) (by positivity)
      _ = r ^ 2 * ∑ j, ‖v.ofLp j‖ ^ 2 := by rw [← Finset.mul_sum]; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hsq

/-- A submatrix along injective maps has operator norm at most that of the matrix. -/
private theorem boundedInitial_submatrix_le {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (A : Matrix n n ℂ) (f g : m → n) (hf : Function.Injective f)
    (hg : Function.Injective g) : ‖A.submatrix f g‖ ≤ ‖A‖ := by
  set Rf : Matrix m n ℂ := Matrix.of fun i p => if p = f i then 1 else 0 with hRf
  set Rg : Matrix m n ℂ := Matrix.of fun i p => if p = g i then 1 else 0 with hRg
  have hR : ∀ (h : m → n), Function.Injective h →
      ‖(Matrix.of fun i p => if p = h i then (1 : ℂ) else 0 : Matrix m n ℂ)‖ ≤ 1 := by
    intro h hh
    set R : Matrix m n ℂ := Matrix.of fun i p => if p = h i then (1 : ℂ) else 0
    have hRR : R * Rᴴ = 1 := by
      ext i j
      simp only [R, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
      rw [Finset.sum_eq_single (h i)]
      · by_cases hij : i = j
        · subst hij; simp
        · have : h i ≠ h j := fun e => hij (hh e)
          simp [this, hij]
      · intro p _ hp; simp [hp]
      · simp
    have h1 : ‖(1 : Matrix m m ℂ)‖ ≤ 1 := by
      rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp
    have h2 : ‖Rᴴ‖ * ‖Rᴴ‖ ≤ 1 := by
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self, Matrix.conjTranspose_conjTranspose, hRR]
      exact h1
    rw [← Matrix.l2_opNorm_conjTranspose]
    nlinarith [norm_nonneg Rᴴ]
  have he : A.submatrix f g = Rf * A * Rgᴴ := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hRf, hRg,
      Matrix.of_apply]
    rw [Finset.sum_eq_single (g j)]
    · rw [Finset.sum_eq_single (f i)]
      · simp
      · intro p _ hp; simp [hp]
      · simp
    · intro p _ hp; simp [hp]
    · simp
  rw [he]
  calc ‖Rf * A * Rgᴴ‖ ≤ ‖Rf * A‖ * ‖Rgᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Rf‖ * ‖A‖) * ‖Rgᴴ‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * ‖A‖) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
        · exact hR f hf
        · exact hR g hg
    _ = ‖A‖ := by ring

end BoundedInitialNorms

/-! ### Cyclic distance -/

private theorem boundedInitial_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private theorem boundedInitial_succ_mod {L y : ℕ} (hy : y < L) :
    (y + 1) % L = if y + 1 = L then 0 else y + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

private theorem boundedInitial_cycDist_comm {L : ℕ} (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

private theorem boundedInitial_cycDist_self {L : ℕ} (a : Fin L) : cycDist a a = 0 := by
  simp [cycDist]

private theorem boundedInitial_cycDist_tri {L : ℕ} (a b c : Fin L) :
    cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [cycDist, boundedInitial_mod ha hb, boundedInitial_mod hb ha, boundedInitial_mod ha hc,
    boundedInitial_mod hc ha, boundedInitial_mod hb hc, boundedInitial_mod hc hb]
  split_ifs <;> omega

/-- Neighbours of the cycle are at distance at most `1`. -/
private theorem boundedInitial_cycDist_adj {L : ℕ} (x y : Fin L) (h : cycleAdj L x y ≠ 0) :
    cycDist x y ≤ 1 := by
  have hx := x.isLt
  have hy := y.isLt
  have h' : y.val = (x.val + 1) % L ∨ x.val = (y.val + 1) % L := by
    by_contra hc
    rw [not_or] at hc
    apply h
    simp [cycleAdj, hc.1, hc.2]
  simp only [cycDist, boundedInitial_mod hx hy, boundedInitial_mod hy hx]
  rw [boundedInitial_succ_mod hx, boundedInitial_succ_mod hy] at h'
  split_ifs at h' ⊢ <;> omega

/-- `|‖a-x‖ - ‖a-y‖| ≤ 1` for neighbours `x, y`. -/
private theorem boundedInitial_dist_diff {L : ℕ} (a x y : Fin L) (h : cycleAdj L x y ≠ 0) :
    |((cycDist a y : ℕ) : ℝ) - ((cycDist a x : ℕ) : ℝ)| ≤ 1 := by
  have h1 := boundedInitial_cycDist_adj x y h
  have h2 := boundedInitial_cycDist_tri a x y
  have h3 := boundedInitial_cycDist_tri a y x
  rw [boundedInitial_cycDist_comm y x] at h3
  rw [abs_le]
  constructor
  · have : (cycDist a x : ℝ) ≤ cycDist a y + 1 := by exact_mod_cast (by omega : cycDist a x ≤ cycDist a y + 1)
    linarith
  · have : (cycDist a y : ℝ) ≤ cycDist a x + 1 := by exact_mod_cast (by omega : cycDist a y ≤ cycDist a x + 1)
    linarith

/-- The cycle adjacency is symmetric entrywise. -/
private theorem boundedInitial_cycleAdj_symm (L : ℕ) (x y : Fin L) : cycleAdj L x y = cycleAdj L y x := by
  simp only [cycleAdj, Matrix.of_apply]
  ring

/-- Each row of the cycle adjacency has entry norms summing to at most `2`. -/
private theorem boundedInitial_cycleAdj_row (L : ℕ) (x : Fin L) : ∑ y, ‖cycleAdj L x y‖ ≤ 2 := by
  have hx := x.isLt
  have h1 : ∑ y : Fin L, ‖(if y.val = (x.val + 1) % L then (1 : ℂ) else 0)‖ ≤ 1 := by
    have e : ∀ y : Fin L, ‖(if y.val = (x.val + 1) % L then (1 : ℂ) else 0)‖ =
        if y ∈ Finset.univ.filter (fun y : Fin L => y.val = (x.val + 1) % L) then 1 else 0 := by
      intro y; split_ifs <;> simp_all
    simp only [e, Finset.sum_boole, Nat.cast_le_one]
    refine Finset.card_le_one.mpr fun y hy y' hy' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy hy'
    exact Fin.ext (hy.trans hy'.symm)
  have h2 : ∑ y : Fin L, ‖(if x.val = (y.val + 1) % L then (1 : ℂ) else 0)‖ ≤ 1 := by
    have e : ∀ y : Fin L, ‖(if x.val = (y.val + 1) % L then (1 : ℂ) else 0)‖ =
        if y ∈ Finset.univ.filter (fun y : Fin L => x.val = (y.val + 1) % L) then 1 else 0 := by
      intro y; split_ifs <;> simp_all
    simp only [e, Finset.sum_boole, Nat.cast_le_one]
    refine Finset.card_le_one.mpr fun y hy y' hy' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy hy'
    have hyL := y.isLt
    have hyL' := y'.isLt
    rw [boundedInitial_succ_mod hyL] at hy
    rw [boundedInitial_succ_mod hyL'] at hy'
    apply Fin.ext
    split_ifs at hy hy' <;> omega
  calc ∑ y, ‖cycleAdj L x y‖ ≤ ∑ y : Fin L, (‖(if y.val = (x.val + 1) % L then (1 : ℂ) else 0)‖ +
        ‖(if x.val = (y.val + 1) % L then (1 : ℂ) else 0)‖) :=
        Finset.sum_le_sum fun y _ => by simp only [cycleAdj, Matrix.of_apply]; exact norm_add_le _ _
    _ ≤ 1 + 1 := by rw [Finset.sum_add_distrib]; exact add_le_add h1 h2
    _ = 2 := by norm_num

/-- `Σ_b f(‖a-b‖_L) ≤ 2 Σ_{j<L} f(j)` for nonnegative `f`. -/
private theorem boundedInitial_sum_dist {L : ℕ} (a : Fin L) (h : ℕ → ℝ) (h0 : ∀ j, 0 ≤ h j) :
    ∑ b, h (cycDist a b) ≤ 2 * ∑ j ∈ Finset.range L, h j := by
  have ha := a.isLt
  have hinj : ∀ (g : Fin L → ℕ), Function.Injective g → (∀ b, g b < L) →
      ∑ b, h (g b) ≤ ∑ j ∈ Finset.range L, h j := by
    intro g hg hlt
    rw [← Finset.sum_image (f := h) (s := Finset.univ) (g := g) (fun x _ y _ hxy => hg hxy)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj
      obtain ⟨b, hb⟩ := hj
      rw [Finset.mem_range, ← hb]
      exact hlt b
    · intro i _ _
      exact h0 i
  have h1 : ∑ b : Fin L, h ((a.val + L - b.val) % L) ≤ ∑ j ∈ Finset.range L, h j := by
    apply hinj (fun b : Fin L => (a.val + L - b.val) % L)
    · intro b b' hbb
      have hb := b.isLt
      have hb' := b'.isLt
      simp only [boundedInitial_mod ha hb, boundedInitial_mod ha hb'] at hbb
      apply Fin.ext
      split_ifs at hbb <;> omega
    · intro b
      exact Nat.mod_lt _ (by omega)
  have h2 : ∑ b : Fin L, h ((b.val + L - a.val) % L) ≤ ∑ j ∈ Finset.range L, h j := by
    apply hinj (fun b : Fin L => (b.val + L - a.val) % L)
    · intro b b' hbb
      have hb := b.isLt
      have hb' := b'.isLt
      simp only [boundedInitial_mod hb ha, boundedInitial_mod hb' ha] at hbb
      apply Fin.ext
      split_ifs at hbb <;> omega
    · intro b
      exact Nat.mod_lt _ (by omega)
  have h3 : ∀ b : Fin L, h (cycDist a b) ≤
      h ((a.val + L - b.val) % L) + h ((b.val + L - a.val) % L) := by
    intro b
    unfold cycDist
    rcases min_choice ((a.val + L - b.val) % L) ((b.val + L - a.val) % L) with e | e
    · rw [e]; linarith [h0 ((b.val + L - a.val) % L)]
    · rw [e]; linarith [h0 ((a.val + L - b.val) % L)]
  calc ∑ b, h (cycDist a b) ≤ ∑ b : Fin L, (h ((a.val + L - b.val) % L) +
        h ((b.val + L - a.val) % L)) := Finset.sum_le_sum fun b _ => h3 b
    _ ≤ 2 * ∑ j ∈ Finset.range L, h j := by
        rw [Finset.sum_add_distrib]; linarith

/-- The geometric sum over the cycle: `Σ_b e^{-λ‖a-b‖_L} ≤ 2/(1 - e^{-λ})` for `λ > 0`. -/
private theorem boundedInitial_sum_exp {L : ℕ} (a : Fin L) {l : ℝ} (hl : 0 < l) :
    ∑ b, Real.exp (-(l * cycDist a b)) ≤ 2 / (1 - Real.exp (-l)) := by
  have hq0 : 0 ≤ Real.exp (-l) := (Real.exp_pos _).le
  have hq1 : Real.exp (-l) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := boundedInitial_sum_dist a (fun j => Real.exp (-(l * j))) fun j => (Real.exp_pos _).le
  refine h.trans ?_
  have e : ∀ j : ℕ, Real.exp (-(l * j)) = Real.exp (-l) ^ j := by
    intro j; rw [← Real.exp_nat_mul]; ring_nf
  simp only [e]
  have h1 : 0 < 1 - Real.exp (-l) := by linarith
  have hg : (∑ j ∈ Finset.range L, Real.exp (-l) ^ j) * (1 - Real.exp (-l)) ≤ 1 := by
    have := geom_sum_mul (Real.exp (-l)) L
    have hp : 0 ≤ Real.exp (-l) ^ L := pow_nonneg hq0 L
    nlinarith
  have hg' : ∑ j ∈ Finset.range L, Real.exp (-l) ^ j ≤ 1 / (1 - Real.exp (-l)) := by
    rw [le_div_iff₀ h1]; exact hg
  calc 2 * ∑ j ∈ Finset.range L, Real.exp (-l) ^ j ≤ 2 * (1 / (1 - Real.exp (-l))) := by linarith
    _ = 2 / (1 - Real.exp (-l)) := by ring

/-! ### Block projections and the Combes–Thomas estimate -/

/-- The block projection `P_a = W E_a`. -/
private def biP (W L : ℕ) (a : Fin L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.diagonal fun p => if p.1 = a then 1 else 0

private theorem biP_mul_self (W L : ℕ) (a : Fin L) : biP W L a * biP W L a = biP W L a := by
  unfold biP
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> simp

private theorem biP_isHermitian (W L : ℕ) (a : Fin L) : (biP W L a).IsHermitian := by
  unfold biP
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases h : p.1 = a <;> simp [h]

private theorem blockE_eq_biP (W L : ℕ) (a : Fin L) :
    blockE W L a = ((W : ℂ)⁻¹) • biP W L a := by
  unfold blockE biP
  rw [← Matrix.diagonal_smul]
  congr 1
  funext p
  by_cases h : p.1 = a <;> simp [h]

section BoundedInitialCT

open scoped Matrix.Norms.L2Operator

private theorem norm_biP_le (W L : ℕ) (a : Fin L) : ‖biP W L a‖ ≤ 1 := by
  unfold biP
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

/-- `‖P_a X P_b‖ ≤ ‖X‖`. -/
private theorem norm_biP_mul_biP_le (W L : ℕ) (a b : Fin L)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) : ‖biP W L a * X * biP W L b‖ ≤ ‖X‖ := by
  calc ‖biP W L a * X * biP W L b‖ ≤ ‖biP W L a * X‖ * ‖biP W L b‖ := norm_mul_le _ _
    _ ≤ (‖biP W L a‖ * ‖X‖) * ‖biP W L b‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖X‖) * 1 := by
        gcongr
        · exact norm_biP_le W L a
        · exact norm_biP_le W L b
    _ = ‖X‖ := by ring

/-- `A_g ⊗ I` is Hermitian. -/
private theorem boundedInitial_Ag_isHermitian (g : ℝ) (W L : ℕ) :
    (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
  have hA : (Ag g L).IsHermitian := by
    unfold Matrix.IsHermitian Ag
    rw [Matrix.conjTranspose_smul, (cycleAdj_isHermitian L).eq]
    simp
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, hA.eq, Matrix.conjTranspose_one]

/-- The Combes–Thomas estimate in projection form: `‖P_a G P_b‖ ≤ (2/η) e^{-μ‖a-b‖_L}`. -/
private theorem boundedInitial_ct (W L : ℕ) (g : ℝ) (hg : 0 ≤ g)
    (V : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (hV : V.IsHermitian)
    (hVb : ∀ p q : Fin L × Fin W, p.1 ≠ q.1 → V p q = 0) (z : ℂ) {η μ : ℝ} (hη : 0 < η)
    (hz : η ≤ z.im) (hμ : 0 ≤ μ) (hμη : Real.exp μ - 1 ≤ η / 4) (a b : Fin L) :
    ‖biP W L a * resolventMat (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + V) z * biP W L b‖ ≤
      2 / η * Real.exp (-(μ * cycDist a b)) := by
  set A₀ : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)
    with hA₀
  set H := A₀ + V with hH
  have hHh : H.IsHermitian := (boundedInitial_Ag_isHermitian g W L).add hV
  have hzim : z.im ≠ 0 := by linarith
  set Z : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := H - z • 1 with hZ
  have hZu : IsUnit Z := isUnit_sub_smul_one hHh hzim
  have hZdet : IsUnit Z.det := (Matrix.isUnit_iff_isUnit_det Z).mp hZu
  set G := resolventMat H z with hG
  have hGZ : G = Z⁻¹ := rfl
  have hZG : Z * G = 1 := by rw [hGZ]; exact Matrix.mul_nonsing_inv Z hZdet
  have hGZ' : G * Z = 1 := by rw [hGZ]; exact Matrix.nonsing_inv_mul Z hZdet
  have hGn : ‖G‖ ≤ η⁻¹ := norm_resolventMat_le hHh hη (by rw [abs_of_pos (by linarith)]; exact hz)
  -- the weights
  set w : Fin L → ℝ := fun x => Real.exp (-(μ * cycDist a x)) with hw
  have hw0 : ∀ x, 0 < w x := fun x => Real.exp_pos _
  set D : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := Matrix.diagonal fun p => ((w p.1 : ℝ) : ℂ)
    with hD
  set D' : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    Matrix.diagonal fun p => (((w p.1)⁻¹ : ℝ) : ℂ) with hD'
  have hDD' : D * D' = 1 := by
    rw [hD, hD', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext p
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hw0 p.1).ne', Complex.ofReal_one]
  have hD'D : D' * D = 1 := by
    rw [hD, hD', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext p
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hw0 p.1).ne', Complex.ofReal_one]
  have hDV : D * V * D' = V := by
    ext p q
    rw [hD, hD', Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hpq : p.1 = q.1
    · rw [hpq, mul_comm, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (hw0 q.1).ne',
        Complex.ofReal_one, one_mul]
    · rw [hVb p q hpq]; simp
  have hDz : D * (z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) * D' = z • 1 := by
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, hDD']
  set Δ := D * A₀ * D' - A₀ with hΔ
  have hDZ : D * Z * D' = Z + Δ := by
    rw [hZ, hH, hΔ, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, hDV, hDz]
    abel
  -- the perturbation is small
  have hΔe : ∀ p q, ‖Δ p q‖ ≤
      if p.2 = q.2 then (Real.exp μ - 1) * ‖cycleAdj L p.1 q.1‖ else 0 := by
    intro p q
    have e : Δ p q = (((w p.1 * (w q.1)⁻¹ - 1 : ℝ) : ℂ)) * A₀ p q := by
      rw [hΔ, Matrix.sub_apply, hD, hD', Matrix.mul_diagonal, Matrix.diagonal_mul]
      push_cast
      ring
    rw [e, norm_mul]
    have hA : A₀ p q = ((g / max 1 g : ℝ) : ℂ) * cycleAdj L p.1 q.1 *
        (1 : Matrix (Fin W) (Fin W) ℂ) p.2 q.2 := by
      rw [hA₀, Matrix.kroneckerMap_apply]
      simp [Ag]
    have hb0 : 0 ≤ g / max 1 g := div_nonneg hg (le_trans zero_le_one (le_max_left _ _))
    have hb1 : g / max 1 g ≤ 1 := by
      rw [div_le_one (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]; exact le_max_right _ _
    by_cases h2 : p.2 = q.2
    · rw [hA, h2, Matrix.one_apply_eq, mul_one, norm_mul]
      simp only [Complex.norm_real, ↓reduceIte]
      rw [Real.norm_of_nonneg hb0]
      by_cases hc : cycleAdj L p.1 q.1 = 0
      · simp [hc]
      · have hd := boundedInitial_dist_diff a p.1 q.1 hc
        have hr : ‖(w p.1 * (w q.1)⁻¹ - 1 : ℝ)‖ ≤ Real.exp μ - 1 := by
          rw [Real.norm_eq_abs]
          have ew : w p.1 * (w q.1)⁻¹ =
              Real.exp (μ * ((cycDist a q.1 : ℝ) - (cycDist a p.1 : ℝ))) := by
            rw [hw]; simp only
            rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
          rw [ew]
          set t := μ * ((cycDist a q.1 : ℝ) - (cycDist a p.1 : ℝ)) with ht
          have htb : |t| ≤ μ := by
            rw [ht, abs_mul, abs_of_nonneg hμ]
            exact mul_le_of_le_one_right hμ hd
          rw [abs_le] at htb
          rw [abs_le]
          constructor
          · have h1 : Real.exp (-μ) ≤ Real.exp t := Real.exp_le_exp.mpr htb.1
            have h2 : Real.exp μ * Real.exp (-μ) = 1 := by rw [← Real.exp_add]; simp
            have h3 : 0 < Real.exp (-μ) := Real.exp_pos _
            have h4 : 1 ≤ Real.exp μ := Real.one_le_exp hμ
            nlinarith
          · have := Real.exp_le_exp.mpr htb.2
            linarith
        calc ‖(w p.1 * (w q.1)⁻¹ - 1 : ℝ)‖ * ((g / max 1 g) * ‖cycleAdj L p.1 q.1‖)
            ≤ (Real.exp μ - 1) * (1 * ‖cycleAdj L p.1 q.1‖) := by
              have : 0 ≤ Real.exp μ - 1 := (norm_nonneg _).trans hr
              gcongr
          _ = _ := by ring
    · rw [hA, Matrix.one_apply_ne h2]; simp [h2]
  have hΔn : ‖Δ‖ ≤ η / 2 := by
    have hr0 : 0 ≤ 2 * (Real.exp μ - 1) := by
      have := Real.one_le_exp hμ; linarith
    have hrow : ∀ (x : Fin L) (α : Fin W),
        ∑ q : Fin L × Fin W, (if α = q.2 then (Real.exp μ - 1) * ‖cycleAdj L x q.1‖ else 0) ≤
          2 * (Real.exp μ - 1) := by
      intro x α
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rw [← Finset.mul_sum]
      have := boundedInitial_cycleAdj_row L x
      have h1 : 0 ≤ Real.exp μ - 1 := by have := Real.one_le_exp hμ; linarith
      nlinarith
    refine (boundedInitial_schur Δ hr0 (fun p => ?_) (fun q => ?_)).trans (by linarith)
    · exact (Finset.sum_le_sum fun q _ => hΔe p q).trans (hrow p.1 p.2)
    · refine (Finset.sum_le_sum fun p _ => hΔe p q).trans ?_
      have e : ∀ p : Fin L × Fin W,
          (if p.2 = q.2 then (Real.exp μ - 1) * ‖cycleAdj L p.1 q.1‖ else 0) =
            (if q.2 = p.2 then (Real.exp μ - 1) * ‖cycleAdj L q.1 p.1‖ else 0) := by
        intro p
        rw [boundedInitial_cycleAdj_symm L p.1 q.1]
        simp only [eq_comm]
      simp only [e]
      exact hrow q.1 q.2
  -- the conjugated resolvent
  set K := D * G * D' with hK
  have hYK : (Z + Δ) * K = 1 := by
    rw [← hDZ, hK]
    calc D * Z * D' * (D * G * D') = D * Z * (D' * D) * G * D' := by noncomm_ring
      _ = D * (Z * G) * D' := by rw [hD'D]; noncomm_ring
      _ = 1 := by rw [hZG, mul_one, hDD']
  have hKn : ‖K‖ ≤ 2 / η := by
    rw [Matrix.cstar_norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    set T := Matrix.toEuclideanCLM (n := Fin L × Fin W) (𝕜 := ℂ)
    set u := T K v with hu
    have h1 : T (Z + Δ) u = v := by
      have e1 : T ((Z + Δ) * K) v = T (Z + Δ) u := by rw [map_mul]; rfl
      rw [← e1, hYK, map_one]; rfl
    have h2 : ‖u‖ ≤ η⁻¹ * ‖T Z u‖ := by
      have : T G (T Z u) = u := by
        have e1 : T (G * Z) u = T G (T Z u) := by rw [map_mul]; rfl
        rw [← e1, hGZ', map_one]; rfl
      calc ‖u‖ = ‖T G (T Z u)‖ := by rw [this]
        _ ≤ ‖T G‖ * ‖T Z u‖ := (T G).le_opNorm _
        _ ≤ η⁻¹ * ‖T Z u‖ := by
            rw [← Matrix.cstar_norm_def]
            exact mul_le_mul_of_nonneg_right hGn (norm_nonneg _)
    have h3 : ‖T Δ u‖ ≤ η / 2 * ‖u‖ := by
      calc ‖T Δ u‖ ≤ ‖T Δ‖ * ‖u‖ := (T Δ).le_opNorm _
        _ ≤ η / 2 * ‖u‖ := by
            rw [← Matrix.cstar_norm_def]
            exact mul_le_mul_of_nonneg_right hΔn (norm_nonneg _)
    have h4 : T (Z + Δ) u = T Z u + T Δ u := by rw [map_add]; rfl
    have h5 : ‖T Z u‖ ≤ ‖v‖ + ‖T Δ u‖ := by
      rw [← h1, h4]
      calc ‖T Z u‖ = ‖(T Z u + T Δ u) - T Δ u‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖T Z u + T Δ u‖ + ‖T Δ u‖ := norm_sub_le _ _
    have h6 : η * ‖u‖ ≤ ‖T Z u‖ := by
      have := h2
      rw [inv_mul_eq_div, le_div_iff₀ hη] at this
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hη]
    nlinarith [norm_nonneg u, norm_nonneg v]
  -- back to the blocks
  have hPK : biP W L a * K * biP W L b =
      ((w a * (w b)⁻¹ : ℝ) : ℂ) • (biP W L a * G * biP W L b) := by
    ext p q
    simp only [hK, hD, hD', biP, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      smul_eq_mul]
    by_cases hp : p.1 = a
    · by_cases hq : q.1 = b
      · simp only [hp, hq, ↓reduceIte]; push_cast; ring
      · simp [hq]
    · simp [hp]
  have hwa : w a = 1 := by simp [hw, boundedInitial_cycDist_self]
  have hfac : (w a * (w b)⁻¹) = Real.exp (μ * cycDist a b) := by
    rw [hwa, one_mul, hw]; simp only; rw [← Real.exp_neg]; ring_nf
  have hn : ‖biP W L a * K * biP W L b‖ ≤ 2 / η := (norm_biP_mul_biP_le W L a b K).trans hKn
  rw [hPK, norm_smul, hfac, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hn
  have he : Real.exp (μ * cycDist a b) * Real.exp (-(μ * cycDist a b)) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖biP W L a * G * biP W L b‖ =
      Real.exp (-(μ * cycDist a b)) *
        (Real.exp (μ * cycDist a b) * ‖biP W L a * G * biP W L b‖) := by
        rw [← mul_assoc, mul_comm (Real.exp (-(μ * cycDist a b))), he, one_mul]
    _ ≤ Real.exp (-(μ * cycDist a b)) * (2 / η) :=
        mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le
    _ = 2 / η * Real.exp (-(μ * cycDist a b)) := by ring

end BoundedInitialCT

open scoped Matrix.Norms.L2Operator in
/-- Combes–Thomas bound behind Appendix C.2 [sec:bounded-proof]: for every Hermitian
block-diagonal `V`, `Im z ≥ η > 0` and `e^μ - 1 ≤ η/4`, `‖G_{ab}‖ ≤ (2/η) e^{-μ ‖a-b‖_L}`. -/
theorem combesThomas_block (W L : ℕ) (g : ℝ) (hg : 0 ≤ g)
    (V : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (hV : V.IsHermitian)
    (hVb : ∀ p q : Fin L × Fin W, p.1 ≠ q.1 → V p q = 0) (z : ℂ) {η μ : ℝ} (hη : 0 < η)
    (hz : η ≤ z.im) (hμ : 0 ≤ μ) (hμη : Real.exp μ - 1 ≤ η / 4) (a b : Fin L) :
    ‖(resolventMat (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + V) z).submatrix
        (fun α => (a, α)) (fun β => (b, β))‖ ≤ 2 / η * Real.exp (-(μ * cycDist a b)) := by
  set G := resolventMat (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + V) z
  have he : G.submatrix (fun α => (a, α)) (fun β => (b, β)) =
      (biP W L a * G * biP W L b).submatrix (fun α => (a, α)) (fun β => (b, β)) := by
    ext α β
    simp [biP, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [he]
  refine (boundedInitial_submatrix_le _ _ _ (fun α α' h => by simpa using h)
    (fun β β' h => by simpa using h)).trans ?_
  exact boundedInitial_ct W L g hg V hV hVb z hη hz hμ hμη a b

/-- Cyclic length `Σ_i ‖a_i - a_{i+1}‖_L` of a label word. -/
def loopLen {L n : ℕ} (a : Fin n → Fin L) : ℕ := ∑ i : Fin n, cycDist (a i) (a (finRotate n i))

/-! ### Loop bounds from block bounds -/

section BoundedInitialLoops

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ}

/-- The chain bound `‖Q_0 X_0 Q_1 X_1 ⋯ X_{q-1} Q_q‖ ≤ Π_p ‖Q_p X_p Q_{p+1}‖` for idempotent
contractions `Q_j`. -/
private theorem boundedInitial_chain {n : Type*} [Fintype n] [DecidableEq n] :
    ∀ (q : ℕ) (Q : Fin (q + 1) → Matrix n n ℂ) (X : Fin q → Matrix n n ℂ),
      (∀ j, Q j * Q j = Q j) → (∀ j, ‖Q j‖ ≤ 1) →
      ‖Q 0 * (List.ofFn fun p => X p * Q p.succ).prod‖ ≤ ∏ p, ‖Q p.castSucc * X p * Q p.succ‖
  | 0, Q, X, _, hn => by simpa using hn 0
  | q + 1, Q, X, hQ, hn => by
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    have IH := boundedInitial_chain q (fun j => Q j.succ) (fun i => X i.succ) (fun j => hQ _)
      (fun j => hn _)
    set R := (List.ofFn fun i : Fin q => X i.succ * Q i.succ.succ).prod with hR
    have e : Q 0 * (X 0 * Q (0 : Fin (q + 1)).succ * R) =
        (Q (0 : Fin (q + 1)).castSucc * X 0 * Q (0 : Fin (q + 1)).succ) *
          (Q (0 : Fin (q + 1)).succ * R) := by
      have h1 := hQ (0 : Fin (q + 1)).succ
      calc Q 0 * (X 0 * Q (0 : Fin (q + 1)).succ * R) =
          Q 0 * X 0 * (Q (0 : Fin (q + 1)).succ * Q (0 : Fin (q + 1)).succ) * R := by
            rw [h1]; noncomm_ring
        _ = _ := by simp only [Fin.castSucc_zero]; noncomm_ring
    rw [e]
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine IH.trans (le_of_eq ?_)
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Fin.succ_castSucc]

/-- `(Π_p Y_p (c P_p)) = c^q Π_p Y_p P_p`. -/
private theorem boundedInitial_prod_smul {n : Type*} [Fintype n] [DecidableEq n] (c : ℂ) :
    ∀ (q : ℕ) (Y P : Fin q → Matrix n n ℂ),
      (List.ofFn fun p => Y p * (c • P p)).prod = c ^ q • (List.ofFn fun p => Y p * P p).prod
  | 0, Y, P => by simp
  | q + 1, Y, P => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons,
      boundedInitial_prod_smul c q (fun i => Y i.succ) (fun i => P i.succ), pow_succ]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]

/-- `|Tr(P_c Z)| ≤ W ‖P_c Z‖`. -/
private theorem boundedInitial_trace_le (c : Fin L) (Z : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    ‖(biP W L c * Z).trace‖ ≤ W * ‖biP W L c * Z‖ := by
  have e : (biP W L c * Z).trace = ∑ p : Fin L × Fin W,
      if p.1 = c then (biP W L c * Z) p p else 0 := by
    unfold Matrix.trace
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Matrix.diag, biP, Matrix.diagonal_mul]
    split_ifs <;> simp
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p : Fin L × Fin W, ‖(if p.1 = c then (biP W L c * Z) p p else 0)‖ ≤
      ∑ p : Fin L × Fin W, (if p.1 = c then ‖biP W L c * Z‖ else 0) := by
        refine Finset.sum_le_sum fun p _ => ?_
        split_ifs
        · exact boundedInitial_norm_entry_le _ p p
        · simp
    _ = W * ‖biP W L c * Z‖ := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
        · simp
        · intro b _ hb; simp [hb]
        · simp

/-- The cyclic predecessor in `Fin (q+1)`. -/
private def boundedInitial_prev {q : ℕ} (p : Fin (q + 1)) : Fin (q + 1) :=
  if h : p.val = 0 then Fin.last q else ⟨p.val - 1, by omega⟩

private theorem boundedInitial_rot_prev {q : ℕ} (p : Fin (q + 1)) :
    finRotate (q + 1) (boundedInitial_prev p) = p := by
  unfold boundedInitial_prev
  split_ifs with h
  · rw [finRotate_last]; exact Fin.ext h.symm
  · apply Fin.ext
    rw [coe_finRotate_of_ne_last]
    · simp; omega
    · intro e
      have := congrArg Fin.val e
      simp at this
      omega

/-- `loopLen` as the sum over legs `(prev p, p)`. -/
private theorem boundedInitial_loopLen_prev {q : ℕ} (w : Fin (q + 1) → Fin L) :
    ∑ p, (cycDist (w (boundedInitial_prev p)) (w p) : ℝ) = loopLen w := by
  have hinj : Function.Injective (boundedInitial_prev (q := q)) := by
    intro p p' h
    have := congrArg (finRotate (q + 1)) h
    rwa [boundedInitial_rot_prev, boundedInitial_rot_prev] at this
  have hbij : Function.Bijective (boundedInitial_prev (q := q)) :=
    (Finite.injective_iff_bijective).mp hinj
  unfold loopLen
  push_cast
  refine Fintype.sum_bijective _ hbij _ _ fun p => ?_
  rw [boundedInitial_rot_prev]

/-- The loop bound `|ℒ_q(w)| ≤ W^{1-q} g^q e^{-μ loopLen(w)}` from leg bounds
`‖P_x X^s P_y‖ ≤ g e^{-μ‖x-y‖_L}`. -/
private theorem boundedInitial_loop_le (hW : 1 ≤ W) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    {g₀ μ : ℝ}
    (hleg : ∀ x y s, ‖biP W L x * sgnMat X s * biP W L y‖ ≤ g₀ * Real.exp (-(μ * cycDist x y)))
    {q : ℕ} (hq : 1 ≤ q) (w : Fin q → Fin L) (τ : Fin q → Bool) :
    ‖loopTr X w τ‖ ≤ (W : ℝ) ^ (1 - (q : ℝ)) * (g₀ ^ q * Real.exp (-(μ * loopLen w))) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set Y := (List.ofFn fun p : Fin (q' + 1) => sgnMat X (τ p) * biP W L (w p)).prod with hY
  have hl : loopTr X w τ = ((W : ℂ)⁻¹) ^ (q' + 1) * Y.trace := by
    unfold loopTr
    simp only [blockE_eq_biP]
    rw [boundedInitial_prod_smul, Matrix.trace_smul, smul_eq_mul]
  have hYP : Y * biP W L (w (Fin.last q')) = Y := by
    rw [hY, List.ofFn_succ', List.prod_concat, Matrix.mul_assoc, Matrix.mul_assoc,
      biP_mul_self]
  have htr : Y.trace = (biP W L (w (Fin.last q')) * Y).trace := by
    rw [← Matrix.trace_mul_comm, hYP]
  -- the chain
  set Q : Fin (q' + 2) → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := fun j =>
    biP W L (w (if h : j.val = 0 then Fin.last q' else ⟨j.val - 1, by omega⟩)) with hQ
  have hQ0 : Q 0 = biP W L (w (Fin.last q')) := by simp [hQ]
  have hQs : ∀ p : Fin (q' + 1), Q p.succ = biP W L (w p) := by
    intro p; simp only [hQ, Fin.val_succ]; simp
  have hQc : ∀ p : Fin (q' + 1), Q p.castSucc = biP W L (w (boundedInitial_prev p)) := by
    intro p; simp only [hQ, boundedInitial_prev, Fin.val_castSucc]
  have hch := boundedInitial_chain (q' + 1) Q (fun p => sgnMat X (τ p))
    (fun j => biP_mul_self W L _) (fun j => norm_biP_le W L _)
  simp only [hQ0, hQs, hQc] at hch
  have hprod : ∏ p : Fin (q' + 1), ‖biP W L (w (boundedInitial_prev p)) * sgnMat X (τ p) *
      biP W L (w p)‖ ≤ g₀ ^ (q' + 1) * Real.exp (-(μ * loopLen w)) := by
    calc ∏ p : Fin (q' + 1), ‖biP W L (w (boundedInitial_prev p)) * sgnMat X (τ p) *
        biP W L (w p)‖ ≤ ∏ p : Fin (q' + 1),
          g₀ * Real.exp (-(μ * cycDist (w (boundedInitial_prev p)) (w p))) :=
          Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) fun p _ => hleg _ _ _
      _ = g₀ ^ (q' + 1) * Real.exp (-(μ * loopLen w)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← Real.exp_sum, ← boundedInitial_loopLen_prev w, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [hl, htr, norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
  have hT := (boundedInitial_trace_le (w (Fin.last q')) Y).trans
    (mul_le_mul_of_nonneg_left (hch.trans hprod) (Nat.cast_nonneg W))
  have hWp : (W : ℝ) ^ (1 - ((q' + 1 : ℕ) : ℝ)) = ((W : ℝ)⁻¹) ^ (q' + 1) * W := by
    rw [Real.rpow_sub hW0, Real.rpow_one, Real.rpow_natCast, inv_pow]; ring
  rw [hWp, mul_assoc]
  exact mul_le_mul_of_nonneg_left hT (by positivity)

/-- The bracket factor `‖P_c B_i P_c‖ ≤ W^{-k} g^{k+1} e^{-μ‖c-a_i‖_L}`. -/
private theorem boundedInitial_loopB_le (hW : 1 ≤ W) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    {g₀ μ : ℝ} (hg₀ : 0 ≤ g₀)
    (hleg : ∀ x y s, ‖biP W L x * sgnMat X s * biP W L y‖ ≤ g₀ * Real.exp (-(μ * cycDist x y)))
    (hX : ∀ s, ‖sgnMat X s‖ ≤ g₀) {k : ℕ} (hk : 1 ≤ k) (a : Fin k → Fin L) (σ : Fin k → Bool)
    (i : Fin k) (c : Fin L) :
    ‖biP W L c * loopB X a σ i * biP W L c‖ ≤
      ((W : ℝ)⁻¹) ^ k * (g₀ ^ (k + 1) * Real.exp (-(μ * cycDist c (a i)))) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set b : Fin (k' + 1) → Fin L := fun p => a (i + p) with hb
  set Y := (List.ofFn fun p : Fin (k' + 1) => sgnMat X (σ (i + p)) * biP W L (b p)).prod with hY
  have hl : loopB X a σ i = ((W : ℂ)⁻¹) ^ (k' + 1) • Y * sgnMat X (σ i) := by
    unfold loopB
    simp only [blockE_eq_biP]
    rw [boundedInitial_prod_smul]
  set Q : Fin (k' + 2) → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    Fin.cons (biP W L c) (fun p => biP W L (b p)) with hQ
  have hch := boundedInitial_chain (k' + 1) Q (fun p => sgnMat X (σ (i + p)))
    (fun j => by refine Fin.cases ?_ (fun j => ?_) j <;> simp [hQ, biP_mul_self])
    (fun j => by refine Fin.cases ?_ (fun j => ?_) j <;> simp [hQ, norm_biP_le])
  have hQ0 : Q 0 = biP W L c := rfl
  have hQs : ∀ p : Fin (k' + 1), Q p.succ = biP W L (b p) := fun p => rfl
  simp only [hQ0, hQs] at hch
  have hprod : ∏ p : Fin (k' + 1), ‖Q p.castSucc * sgnMat X (σ (i + p)) * biP W L (b p)‖ ≤
      g₀ ^ (k' + 1) * Real.exp (-(μ * cycDist c (a i))) := by
    rw [Fin.prod_univ_succ]
    have h0 : ‖Q (0 : Fin (k' + 1)).castSucc * sgnMat X (σ (i + 0)) * biP W L (b 0)‖ ≤
        g₀ * Real.exp (-(μ * cycDist c (a i))) := by
      have := hleg c (a i) (σ i)
      simpa [hQ, hb] using this
    have hs : ∏ p : Fin k', ‖Q p.succ.castSucc * sgnMat X (σ (i + p.succ)) *
        biP W L (b p.succ)‖ ≤ g₀ ^ k' := by
      calc ∏ p : Fin k', ‖Q p.succ.castSucc * sgnMat X (σ (i + p.succ)) * biP W L (b p.succ)‖
          ≤ ∏ p : Fin k', g₀ := by
            refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) fun p _ => ?_
            rw [← Fin.succ_castSucc, hQs]
            exact (norm_biP_mul_biP_le W L _ _ _).trans (hX _)
        _ = g₀ ^ k' := by simp
    calc _ ≤ (g₀ * Real.exp (-(μ * cycDist c (a i)))) * g₀ ^ k' :=
          mul_le_mul h0 hs (Finset.prod_nonneg fun p _ => norm_nonneg _)
            (by positivity)
      _ = g₀ ^ (k' + 1) * Real.exp (-(μ * cycDist c (a i))) := by ring
  rw [hl]
  have e : biP W L c * (((W : ℂ)⁻¹) ^ (k' + 1) • Y * sgnMat X (σ i)) * biP W L c =
      ((W : ℂ)⁻¹) ^ (k' + 1) • ((biP W L c * Y) * (sgnMat X (σ i) * biP W L c)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]; noncomm_ring
  rw [e, norm_smul, norm_pow, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖biP W L c * Y * (sgnMat X (σ i) * biP W L c)‖ ≤
      ‖biP W L c * Y‖ * ‖sgnMat X (σ i) * biP W L c‖ := norm_mul_le _ _
    _ ≤ (g₀ ^ (k' + 1) * Real.exp (-(μ * cycDist c (a i)))) * g₀ := by
        refine mul_le_mul (hch.trans hprod) ?_ (norm_nonneg _) (by positivity)
        calc ‖sgnMat X (σ i) * biP W L c‖ ≤ ‖sgnMat X (σ i)‖ * ‖biP W L c‖ := norm_mul_le _ _
          _ ≤ g₀ * 1 := mul_le_mul (hX _) (norm_biP_le W L c) (norm_nonneg _) hg₀
          _ = g₀ := mul_one _
    _ = g₀ ^ (k' + 1 + 1) * Real.exp (-(μ * cycDist c (a i))) := by ring

end BoundedInitialLoops

/-! ### Moments along the flow -/

section BoundedInitialMoments

/-- The moment `‖F_u‖_{2p} = (E|F(u, √(uσ²) x)|^{2p})^{1/(2p)}` along the Gaussian flow. -/
private def bMom {ι : Type*} [Fintype ι] (σ2 : ℝ) (p : ℕ) (F : ℝ → (ι → ℝ) → ℂ) (u : ℝ) : ℝ :=
  (∫ x, ‖F u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ)))

private theorem boundedInitial_rpow_pow {p : ℕ} (hp : 1 ≤ p) {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (2 * p)) ^ (1 / (2 * (p : ℝ))) = x := by
  have h : (1 / (2 * (p : ℝ))) = (((2 * p : ℕ) : ℝ))⁻¹ := by push_cast; ring
  rw [h, Real.pow_rpow_inv_natCast hx (by omega)]

private theorem boundedInitial_pow_rpow {p : ℕ} (hp : 1 ≤ p) {y : ℝ} (hy : 0 ≤ y) :
    (y ^ (1 / (2 * (p : ℝ)))) ^ (2 * p) = y := by
  have h : (1 / (2 * (p : ℝ))) = (((2 * p : ℕ) : ℝ))⁻¹ := by push_cast; ring
  rw [h, Real.rpow_inv_natCast_pow hy (by omega)]

private theorem boundedInitial_rpow_half {p : ℕ} (hp : 1 ≤ p) {y : ℝ} (hy : 0 ≤ y) :
    y ^ (1 / (p : ℝ)) = (y ^ (1 / (2 * (p : ℝ)))) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  congr 1
  have : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  field_simp
  norm_num

private theorem bMom_nonneg {ι : Type*} [Fintype ι] (σ2 : ℝ) (p : ℕ) (F : ℝ → (ι → ℝ) → ℂ)
    (u : ℝ) : 0 ≤ bMom σ2 p F u :=
  Real.rpow_nonneg (integral_nonneg fun x => by positivity) _

/-- A pointwise bound `|F| ≤ K` bounds the moment by `K`. -/
private theorem bMom_le_of_bound {ι : Type*} [Fintype ι] (σ2 : ℝ) {p : ℕ} (hp : 1 ≤ p)
    (F : ℝ → (ι → ℝ) → ℂ) (u : ℝ) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ y, ‖F u y‖ ≤ K) :
    bMom σ2 p F u ≤ K := by
  unfold bMom
  have h1 : ∫ x, ‖F u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι) ≤ K ^ (2 * p) := by
    have := integral_mono_of_nonneg (μ := stdGauss ι)
      (f := fun x => ‖F u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p)) (g := fun _ => K ^ (2 * p))
      (ae_of_all _ fun x => by positivity) (integrable_const _)
      (ae_of_all _ fun x => pow_le_pow_left₀ (norm_nonneg _) (hK _) _)
    simpa using this
  calc (∫ x, ‖F u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) ≤
      (K ^ (2 * p)) ^ (1 / (2 * (p : ℝ))) :=
        Real.rpow_le_rpow (integral_nonneg fun x => by positivity) h1 (by positivity)
    _ = K := boundedInitial_rpow_pow hp hK0

/-- The moment at `u = 0` of a function vanishing at `(0, 0)`. -/
private theorem bMom_zero {ι : Type*} [Fintype ι] (σ2 : ℝ) {p : ℕ} (hp : 1 ≤ p)
    (F : ℝ → (ι → ℝ) → ℂ) (h0 : F 0 0 = 0) : bMom σ2 p F 0 = 0 := by
  unfold bMom
  simp only [zero_mul, Real.sqrt_zero, zero_smul, h0, norm_zero]
  rw [zero_pow (by omega), integral_zero, Real.zero_rpow]
  have : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  positivity

private theorem boundedInitial_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x ^ 2 + y) ≤ x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hy, Real.sqrt_nonneg y]

/-- The constant of the short-interval bootstrap. -/
private def bootC (T : ℝ) (p : ℕ) : ℝ := 2 ^ (⌈T⌉₊ + 2) * Real.sqrt (2 * p)

private theorem bootC_nonneg (T : ℝ) (p : ℕ) : 0 ≤ bootC T p := by
  unfold bootC; positivity

/-- Moments of a family of flow functionals with a linear generator bound: if
`‖𝒢Y_i‖_{2p} ≤ T max_j ‖Y_j‖_{2p} + β`, `‖Γ(Y_i, Y_i)‖_p ≤ B` and `Y_i = 0` at time `0`,
then `‖Y_i‖_{2p} ≤ C(T, p)(√B + β)` on `[0, 1/2]` (the moment comparison on short intervals). -/
private theorem boundedInitial_boot {ι I : Type*} [Fintype ι] [Fintype I] (σ2 : ℝ) (hσ2 : 0 ≤ σ2)
    (p : ℕ) (hp : 1 ≤ p) (Y : I → ℝ → (ι → ℝ) → ℂ) {a b : ℝ} (ha : a < 0) (hb : 1 / 2 < b)
    (hY : ∀ i, HeatClass (Y i) a b) (h0 : ∀ i, Y i 0 0 = 0) {T β B : ℝ} (hT : 0 ≤ T)
    (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hA : ∀ u ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ S : ℝ, 0 ≤ S → (∀ j, bMom σ2 p (Y j) u ≤ S) →
      ∀ i, bMom σ2 p (coordGen σ2 (Y i)) u ≤ T * S + β)
    (hΓ : ∀ u ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ i,
      (∫ x, ‖coordGamma σ2 (Y i u) (Y i u) (Real.sqrt (u * σ2) • x)‖ ^ p ∂(stdGauss ι)) ^
        (1 / (p : ℝ)) ≤ B) :
    ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ i, bMom σ2 p (Y i) u ≤ bootC T p * (Real.sqrt B + β) := by
  rcases isEmpty_or_nonempty I with hI | hI
  · intro u _ i; exact (IsEmpty.false i).elim
  set N : ℕ := ⌈T⌉₊ + 1 with hN
  have hN0 : (0 : ℝ) < N := by positivity
  set h : ℝ := 1 / (2 * N) with hh
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := by
    rw [hh, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    linarith
  have hTh : T * h ≤ 1 / 2 := by
    have hT' : T ≤ N := by
      have := Nat.le_ceil T
      have : (⌈T⌉₊ : ℝ) + 1 = N := by rw [hN]; push_cast; ring
      linarith
    rw [hh, mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hNh : (N : ℝ) * h = 1 / 2 := by rw [hh]; field_simp
  set X : ℝ := Real.sqrt (2 * p) * (Real.sqrt B + β) with hX
  have hs2 : 1 ≤ Real.sqrt (2 * p) := by
    rw [Real.one_le_sqrt]
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hX0 : 0 ≤ X := by positivity
  -- uniform bound on the family
  have hK : ∃ K : ℝ, 0 ≤ K ∧ ∀ i, ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ y, ‖Y i u y‖ ≤ K := by
    choose C hC using fun i => (hY i).bdd
    refine ⟨∑ i, |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i u hu y => ?_⟩
    have hu' : u ∈ Set.Ioo a b := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    calc ‖Y i u y‖ ≤ C i := hC i u hu' y
      _ ≤ |C i| := le_abs_self _
      _ ≤ ∑ j, |C j| := Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i)
  obtain ⟨K, hK0, hKb⟩ := hK
  have hMK : ∀ i, ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), bMom σ2 p (Y i) u ≤ K := fun i u hu =>
    bMom_le_of_bound σ2 hp (Y i) u hK0 (hKb i u hu)
  -- the induction over the intervals `[jh, (j+1)h]`
  have key : ∀ j : ℕ, j ≤ N → ∀ u ∈ Set.Icc (0 : ℝ) (j * h), ∀ i,
      bMom σ2 p (Y i) u ≤ (2 ^ (j + 1) - 2) * X := by
    intro j
    induction j with
    | zero =>
      intro _ u hu i
      have hu0 : u = 0 := le_antisymm (by simpa using hu.2) hu.1
      rw [hu0, bMom_zero σ2 hp (Y i) (h0 i)]
      simp
    | succ j IH =>
      intro hj u hu i
      have hjN : j ≤ N := by omega
      set s : ℝ := j * h with hs
      set t : ℝ := (j + 1 : ℕ) * h with ht
      have hs0 : 0 ≤ s := by positivity
      have hst : s ≤ t := by rw [hs, ht]; push_cast; nlinarith
      have ht2 : t ≤ 1 / 2 := by
        rw [ht, ← hNh]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh0.le
      have hts : t - s = h := by rw [hs, ht]; push_cast; ring
      set Sset : Set ℝ := {r | ∃ i, ∃ v ∈ Set.Icc s t, r = bMom σ2 p (Y i) v} with hSset
      have hbdd : BddAbove Sset := by
        refine ⟨K, fun r hr => ?_⟩
        obtain ⟨i, v, hv, rfl⟩ := hr
        exact hMK i v ⟨hs0.trans hv.1, hv.2.trans ht2⟩
      obtain ⟨i₀⟩ := hI
      have hne : (bMom σ2 p (Y i₀) s) ∈ Sset := ⟨i₀, s, ⟨le_rfl, hst⟩, rfl⟩
      set S := sSup Sset with hS
      have hmS : ∀ i, ∀ v ∈ Set.Icc s t, bMom σ2 p (Y i) v ≤ S :=
        fun i v hv => le_csSup hbdd ⟨i, v, hv, rfl⟩
      have hS0 : 0 ≤ S := (bMom_nonneg σ2 p _ s).trans (le_csSup hbdd hne)
      have hRj : 0 ≤ (2 ^ (j + 1) - 2 : ℝ) * X := by
        have : (2 : ℝ) ≤ 2 ^ (j + 1) := by
          calc (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith
      have hstep : ∀ i, ∀ v ∈ Set.Icc s t,
          bMom σ2 p (Y i) v ≤ (2 ^ (j + 1) - 2) * X + X + S / 2 := by
        intro i v hv
        have hms : bMom σ2 p (Y i) s ≤ (2 ^ (j + 1) - 2) * X :=
          IH hjN s ⟨hs0, le_rfl⟩ i
        rcases eq_or_lt_of_le hv.1 with hsv | hsv
        · rw [← hsv]; linarith
        · have hvb : v < b := by linarith [hv.2]
          have hM := lemmaM_gaussian σ2 hσ2 (Y i) ha hs0 hv.1 hvb (hY i) p hp
            (fun _ => T * S + β) (fun _ => B) continuousOn_const continuousOn_const
            (fun _ _ => by positivity) (fun _ _ => hB)
            (fun r hr => hA r ⟨hs0.trans_lt hr.1, hr.2.trans_le (hv.2.trans ht2)⟩ S hS0
              (fun j' => hmS j' r ⟨hr.1.le, hr.2.le.trans hv.2⟩) i)
            (fun r hr => hΓ r ⟨hs0.trans_lt hr.1, hr.2.trans_le (hv.2.trans ht2)⟩ i)
          simp only [intervalIntegral.integral_const, smul_eq_mul] at hM
          have hsq : (∫ x, ‖Y i s (Real.sqrt (s * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^
              (1 / (p : ℝ)) = bMom σ2 p (Y i) s ^ 2 :=
            boundedInitial_rpow_half hp (integral_nonneg fun x => by positivity)
          rw [hsq] at hM
          change bMom σ2 p (Y i) v ≤ _ at hM
          have hvs : v - s ≤ h := by linarith [hv.2]
          have hvs0 : 0 ≤ v - s := by linarith
          have hp1 : (0 : ℝ) ≤ 2 * p - 1 := by
            have : (1 : ℝ) ≤ p := by exact_mod_cast hp
            linarith
          have h1 := boundedInitial_sqrt_add_le (bMom_nonneg σ2 p (Y i) s)
            (mul_nonneg hp1 (mul_nonneg hvs0 hB) : 0 ≤ (2 * (p : ℝ) - 1) * ((v - s) * B))
          have h2 : Real.sqrt ((2 * (p : ℝ) - 1) * ((v - s) * B)) ≤ Real.sqrt (2 * p) * Real.sqrt B := by
            rw [← Real.sqrt_mul (by positivity)]
            refine Real.sqrt_le_sqrt ?_
            have : (2 * (p : ℝ) - 1) * ((v - s) * B) ≤ (2 * p) * (1 * B) := by
              apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right (hvs.trans hh1) hB)
                (by positivity) (by positivity)
            linarith
          have h3 : (v - s) * (T * S + β) ≤ S / 2 + Real.sqrt (2 * p) * β := by
            have e1 : (v - s) * (T * S) ≤ S / 2 := by
              calc (v - s) * (T * S) ≤ h * (T * S) :=
                    mul_le_mul_of_nonneg_right hvs (by positivity)
                _ = (T * h) * S := by ring
                _ ≤ (1 / 2) * S := mul_le_mul_of_nonneg_right hTh hS0
                _ = S / 2 := by ring
            have e2 : (v - s) * β ≤ Real.sqrt (2 * p) * β := by
              calc (v - s) * β ≤ 1 * β := mul_le_mul_of_nonneg_right (hvs.trans hh1) hβ
                _ ≤ Real.sqrt (2 * p) * β := mul_le_mul_of_nonneg_right hs2 hβ
            nlinarith
          rw [hX]
          nlinarith
      have hSle : S ≤ (2 ^ (j + 1) - 2) * X + X + S / 2 := by
        refine csSup_le ⟨_, hne⟩ fun r hr => ?_
        obtain ⟨i, v, hv, rfl⟩ := hr
        exact hstep i v hv
      have hS2 : S ≤ (2 ^ (j + 1 + 1) - 2) * X := by
        have : (2 : ℝ) ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
        rw [this]; linarith
      rcases le_or_gt u s with hus | hus
      · refine (IH hjN u ⟨hu.1, hus⟩ i).trans ?_
        have : (2 : ℝ) ^ (j + 1) ≤ 2 ^ (j + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith
      · exact (hmS i u ⟨hus.le, by simpa [ht] using hu.2⟩).trans hS2
  intro u hu i
  have h1 := key N le_rfl u ⟨hu.1, by rw [hNh]; exact hu.2⟩ i
  refine h1.trans ?_
  have hb0 : 0 ≤ Real.sqrt B + β := by positivity
  have : ((2 : ℝ) ^ (N + 1) - 2) * X ≤ 2 ^ (⌈T⌉₊ + 2) * X := by
    have : (N + 1) = ⌈T⌉₊ + 2 := by omega
    rw [this]
    nlinarith
  refine this.trans (le_of_eq ?_)
  rw [bootC, hX]; ring

end BoundedInitialMoments

section BoundedInitialMomentSums

/-- A function of the class is continuous in space at each time of the interval. -/
private theorem boundedInitial_heat_cont {ι : Type*} [Fintype ι] {F : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (hF : HeatClass F a b) {r : ℝ} (hr : r ∈ Set.Ioo a b) : Continuous (F r) := by
  have h := hF.cont
  rw [continuous_iff_continuousAt]
  intro x
  have hx : (r, x) ∈ Set.Ioo a b ×ˢ (Set.univ : Set (ι → ℝ)) := ⟨hr, Set.mem_univ x⟩
  have hca : ContinuousAt (Function.uncurry F) (r, x) :=
    h.continuousAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hx)
  exact hca.comp (Continuous.prodMk continuous_const continuous_id).continuousAt

/-- Powers of a scaled function of the class are integrable under the standard Gaussian. -/
private theorem boundedInitial_heat_integrable {ι : Type*} [Fintype ι] {F : ℝ → (ι → ℝ) → ℂ}
    {a b : ℝ} (hF : HeatClass F a b) {r : ℝ} (hr : r ∈ Set.Ioo a b) (S : ℝ) (q : ℕ) :
    Integrable (fun x => ‖F r (S • x)‖ ^ q) (stdGauss ι) := by
  obtain ⟨C, hC⟩ := hF.bdd
  have hc : Continuous fun x : ι → ℝ => ‖F r (S • x)‖ ^ q :=
    ((boundedInitial_heat_cont hF hr).comp (continuous_const_smul S)).norm.pow q
  refine Integrable.of_bound hc.aestronglyMeasurable (|C| ^ q) (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) ((hC r hr _).trans (le_abs_self C)) q

/-- From a moment bound to a bound on the `2p`-th moment. -/
private theorem boundedInitial_int_le_of_bMom {ι : Type*} [Fintype ι] (σ2 : ℝ) {p : ℕ} (hp : 1 ≤ p)
    (F : ℝ → (ι → ℝ) → ℂ) (u : ℝ) {M : ℝ} (h : bMom σ2 p F u ≤ M) :
    (∫ x, ‖F u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ≤ M ^ (2 * p) := by
  have h0 : 0 ≤ ∫ x, ‖F u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι) :=
    integral_nonneg fun x => by positivity
  rw [← boundedInitial_pow_rpow hp h0]
  exact pow_le_pow_left₀ (bMom_nonneg σ2 p F u) h _

/-- Minkowski-type bound: `|F| ≤ Σ_j c_j |f_j|` and `‖f_j‖_{2p} ≤ M_j` give
`‖F‖_{2p} ≤ Σ_j c_j M_j`. -/
private theorem boundedInitial_mom_sum {ι J : Type*} [Fintype ι] [Fintype J] (σ2 : ℝ) {p : ℕ}
    (hp : 1 ≤ p) (F : ℝ → (ι → ℝ) → ℂ) (u : ℝ) (f : J → (ι → ℝ) → ℂ) (c M : J → ℝ)
    (hc : ∀ j, 0 ≤ c j) (hM : ∀ j, 0 ≤ M j)
    (hfi : ∀ j, c j ≠ 0 →
      Integrable (fun x => ‖f j (Real.sqrt (u * σ2) • x)‖ ^ (2 * p)) (stdGauss ι))
    (hfM : ∀ j, c j ≠ 0 →
      (∫ x, ‖f j (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ≤ M j ^ (2 * p))
    (hF : ∀ y, ‖F u y‖ ≤ ∑ j, c j * ‖f j y‖) :
    bMom σ2 p F u ≤ ∑ j, c j * M j := by
  set Sx := Real.sqrt (u * σ2)
  -- the case with strictly positive `M`
  have pos : ∀ M' : J → ℝ, (∀ j, 0 < M' j) → (∀ j, M j ≤ M' j) →
      bMom σ2 p F u ≤ ∑ j, c j * M' j := by
    intro M' hM' hMM'
    set Z := ∑ j, c j * M' j with hZ
    have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (hM' j).le
    rcases eq_or_lt_of_le hZ0 with hZ0' | hZpos
    · have hc0 : ∀ j, c j = 0 := by
        intro j
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => mul_nonneg (hc j) (hM' j).le)).mp hZ0'.symm j (Finset.mem_univ j)
        rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · exact absurd h (hM' j).ne'
      refine bMom_le_of_bound σ2 hp F u hZ0 fun y => ?_
      refine (hF y).trans (le_of_eq ?_)
      simp [hc0, ← hZ0']
    · set κ : J → ℝ := fun j => (c j * M' j / Z) * (Z / M' j) ^ (2 * p) with hκ
      have hκ0 : ∀ j, 0 ≤ κ j := fun j => by
        have := hM' j; have := hc j; simp only [hκ]; positivity
      have hpt : ∀ x, ‖F u (Sx • x)‖ ^ (2 * p) ≤ ∑ j, κ j * ‖f j (Sx • x)‖ ^ (2 * p) := by
        intro x
        have hw1 : ∑ j, c j * M' j / Z = 1 := by rw [← Finset.sum_div, div_self hZpos.ne']
        have hJ := Real.pow_arith_mean_le_arith_mean_pow Finset.univ
          (fun j => c j * M' j / Z) (fun j => Z * ‖f j (Sx • x)‖ / M' j)
          (fun j _ => by have := hM' j; have := hc j; positivity) hw1
          (fun j _ => by have := hM' j; positivity) (2 * p)
        have e1 : ∑ j, c j * M' j / Z * (Z * ‖f j (Sx • x)‖ / M' j) = ∑ j, c j * ‖f j (Sx • x)‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have := (hM' j).ne'
          field_simp
        have e2 : ∀ j, c j * M' j / Z * (Z * ‖f j (Sx • x)‖ / M' j) ^ (2 * p) =
            κ j * ‖f j (Sx • x)‖ ^ (2 * p) := by
          intro j
          simp only [hκ]
          rw [div_pow, mul_pow, div_pow]
          ring
        rw [e1] at hJ
        simp only [e2] at hJ
        exact (pow_le_pow_left₀ (norm_nonneg _) (hF _) _).trans hJ
      have hint : Integrable (fun x => ∑ j, κ j * ‖f j (Sx • x)‖ ^ (2 * p)) (stdGauss ι) := by
        refine integrable_finsetSum _ fun j _ => ?_
        by_cases hcj : c j = 0
        · have : κ j = 0 := by simp [hκ, hcj]
          simp [this]
        · exact (hfi j hcj).const_mul _
      have h1 : ∫ x, ‖F u (Sx • x)‖ ^ (2 * p) ∂(stdGauss ι) ≤ Z ^ (2 * p) := by
        calc ∫ x, ‖F u (Sx • x)‖ ^ (2 * p) ∂(stdGauss ι) ≤
            ∫ x, ∑ j, κ j * ‖f j (Sx • x)‖ ^ (2 * p) ∂(stdGauss ι) :=
              integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) hint (ae_of_all _ hpt)
          _ = ∑ j, κ j * ∫ x, ‖f j (Sx • x)‖ ^ (2 * p) ∂(stdGauss ι) := by
              rw [integral_finsetSum]
              · exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
              · intro j _
                by_cases hcj : c j = 0
                · have : κ j = 0 := by simp [hκ, hcj]
                  simp [this]
                · exact (hfi j hcj).const_mul _
          _ ≤ ∑ j, κ j * M' j ^ (2 * p) := by
              refine Finset.sum_le_sum fun j _ => ?_
              by_cases hcj : c j = 0
              · have : κ j = 0 := by simp [hκ, hcj]
                simp [this]
              · refine mul_le_mul_of_nonneg_left ((hfM j hcj).trans ?_) (hκ0 j)
                exact pow_le_pow_left₀ (hM j) (hMM' j) _
          _ = ∑ j, c j * M' j / Z * Z ^ (2 * p) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              have := (hM' j).ne'
              simp only [hκ]
              rw [div_pow]
              field_simp
          _ = Z ^ (2 * p) := by
              rw [← Finset.sum_mul, ← Finset.sum_div, div_self hZpos.ne', one_mul]
      unfold bMom
      calc (∫ x, ‖F u (Sx • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) ≤
          (Z ^ (2 * p)) ^ (1 / (2 * (p : ℝ))) :=
            Real.rpow_le_rpow (integral_nonneg fun x => by positivity) h1 (by positivity)
        _ = Z := boundedInitial_rpow_pow hp hZ0
  -- perturb `M`
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε / (∑ j, c j + 1) with hδ
  have hc0 : 0 ≤ ∑ j, c j := Finset.sum_nonneg fun j _ => hc j
  have hδ0 : 0 < δ := by positivity
  have h := pos (fun j => M j + δ) (fun j => by have := hM j; positivity) (fun j => by linarith)
  refine h.trans ?_
  have e : ∑ j, c j * (M j + δ) = ∑ j, c j * M j + δ * ∑ j, c j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  have : δ * ∑ j, c j ≤ ε := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- A pointwise bound on the bracket bounds its `p`-th moment. -/
private theorem boundedInitial_gamma_mom {ι : Type*} [Fintype ι] {p : ℕ} (hp : 1 ≤ p)
    (Γ : (ι → ℝ) → ℂ) (S : ℝ) {B : ℝ} (hB : 0 ≤ B) (h : ∀ y, ‖Γ y‖ ≤ B) :
    (∫ x, ‖Γ (S • x)‖ ^ p ∂(stdGauss ι)) ^ (1 / (p : ℝ)) ≤ B := by
  have h1 : ∫ x, ‖Γ (S • x)‖ ^ p ∂(stdGauss ι) ≤ B ^ p := by
    have := integral_mono_of_nonneg (μ := stdGauss ι)
      (f := fun x => ‖Γ (S • x)‖ ^ p) (g := fun _ => B ^ p)
      (ae_of_all _ fun x => by positivity) (integrable_const _)
      (ae_of_all _ fun x => pow_le_pow_left₀ (norm_nonneg _) (h _) _)
    simpa using this
  have e : (1 / (p : ℝ)) = ((p : ℕ) : ℝ)⁻¹ := by rw [one_div]
  calc (∫ x, ‖Γ (S • x)‖ ^ p ∂(stdGauss ι)) ^ (1 / (p : ℝ)) ≤ (B ^ p) ^ (1 / (p : ℝ)) :=
        Real.rpow_le_rpow (integral_nonneg fun x => by positivity) h1 (by positivity)
    _ = B := by rw [e, Real.pow_rpow_inv_natCast hB (by omega)]

end BoundedInitialMomentSums

/-! ### The bounded-coupling setting -/

/-- `η₀ = c'/(2 max{1,C}²)`, a lower bound for `η_u` at `u ≤ 1/2` on the regular domain. -/
private def biEta (C c' : ℝ) : ℝ := c' / (2 * (max 1 C) ^ 2)

/-- The Combes–Thomas rate `μ₀ = log(1 + η₀/4)`. -/
private def biMu (C c' : ℝ) : ℝ := Real.log (1 + biEta C c' / 4)

/-- The Combes–Thomas constant `g₀ = max{2/η₀, 1}`. -/
private def biG (C c' : ℝ) : ℝ := max (2 / biEta C c') 1

/-- The cycle sum `Σ_b e^{-μ₀‖a-b‖_L} ≤ 2/(1 - e^{-μ₀})`. -/
private def biS (C c' : ℝ) : ℝ := 2 / (1 - Real.exp (-biMu C c'))

private theorem biEta_pos {C c' : ℝ} (hc' : 0 < c') : 0 < biEta C c' := by
  unfold biEta; positivity

private theorem biMu_pos {C c' : ℝ} (hc' : 0 < c') : 0 < biMu C c' := by
  unfold biMu
  have := biEta_pos (C := C) hc'
  exact Real.log_pos (by linarith)

private theorem biMu_exp {C c' : ℝ} (hc' : 0 < c') : Real.exp (biMu C c') - 1 = biEta C c' / 4 := by
  unfold biMu
  have := biEta_pos (C := C) hc'
  rw [Real.exp_log (by linarith)]; ring

private theorem one_le_biG (C c' : ℝ) : 1 ≤ biG C c' := le_max_right _ _

private theorem biG_pos (C c' : ℝ) : 0 < biG C c' := lt_of_lt_of_le one_pos (one_le_biG C c')

private theorem biS_pos {C c' : ℝ} (hc' : 0 < c') : 0 < biS C c' := by
  unfold biS
  have : Real.exp (-biMu C c') < 1 := Real.exp_lt_one_iff.mpr (by linarith [biMu_pos (C := C) hc'])
  have : 0 < 1 - Real.exp (-biMu C c') := by linarith
  positivity

private theorem biS_sum {C c' : ℝ} (hc' : 0 < c') {L : ℕ} (a : Fin L) :
    ∑ b, Real.exp (-(biMu C c' * cycDist a b)) ≤ biS C c' :=
  boundedInitial_sum_exp a (biMu_pos hc')

private theorem gammaG_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

private theorem gammaG_le_one (g : ℝ) : gammaG g ≤ 1 := by
  unfold gammaG
  have h : (1 : ℝ) ≤ max 1 g := le_max_left _ _
  have : (1 : ℝ) ≤ (max 1 g) ^ 2 := one_le_pow₀ h
  exact inv_le_one_of_one_le₀ this

/-- `η_u ≥ η₀` on the regular domain for `u ≤ 1/2`. -/
private theorem biEta_le_im {C B c' : ℝ} (hc' : 0 < c') {L : ℕ} {g E : ℝ}
    (hreg : RegBdd C B c' L g E) {u : ℝ} (hu : u ≤ 1 / 2) :
    biEta C c' ≤ (zChar g E (mRoot g L E) u).im := by
  obtain ⟨hg0, hgC, -, hroot, hcm⟩ := hreg
  rw [im_zChar, etaChar]
  have hγ : ((max 1 C) ^ 2)⁻¹ ≤ gammaG g := by
    unfold gammaG
    have h1 : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
    have h2 : max 1 g ≤ max 1 C := max_le_max le_rfl hgC
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h1.le h2 2)
  unfold biEta
  have hC2 : (0 : ℝ) < (max 1 C) ^ 2 := by
    have : (0 : ℝ) < max 1 C := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  have hm : c' ≤ (mRoot g L E).im := hcm
  have hγ0 : 0 < gammaG g := gammaG_pos g
  calc c' / (2 * (max 1 C) ^ 2) = (1 / 2) * ((max 1 C) ^ 2)⁻¹ * c' := by field_simp
    _ ≤ (1 - u) * gammaG g * (mRoot g L E).im := by
        have h1 : (1 / 2 : ℝ) ≤ 1 - u := by linarith
        have hc0 : 0 ≤ c' := hc'.le
        gcongr

/-- The slice `A_g ⊗ I + Σ x_{c,k} T_{c,k}` is `A_g ⊗ I` plus a Hermitian block-diagonal matrix. -/
private theorem boundedInitial_slice_split (g : ℝ) (W L : ℕ) (y : Ω W L) :
    ∃ V : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ, V.IsHermitian ∧
      (∀ p q : Fin L × Fin W, p.1 ≠ q.1 → V p q = 0) ∧
      blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y =
        Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + V := by
  refine ⟨∑ c : Fin L, ∑ k : Fin W × Fin W, ((y (c, k.1, k.2) : ℝ) : ℂ) • blockBasis W L c k,
    ?_, ?_, rfl⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_smul, (blockBasis_isHermitian W L c k).eq]
    simp
  · intro p q hpq
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.smul_apply]
    have : blockBasis W L c k p q = 0 := by
      have hn : ¬(p.1 = c ∧ q.1 = c) := fun h => hpq (h.1.trans h.2.symm)
      simp [blockBasis, hn]
    rw [this, smul_zero]

/-- The slice is Hermitian. -/
private theorem boundedInitial_slice_isHermitian (g : ℝ) (W L : ℕ) (y : Ω W L) :
    (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y).IsHermitian := by
  obtain ⟨V, hV, -, he⟩ := boundedInitial_slice_split g W L y
  rw [he]
  exact (boundedInitial_Ag_isHermitian g W L).add hV

section BoundedInitialSlice

open scoped Matrix.Norms.L2Operator

/-- Leg and norm bounds for the resolvent at a slice point at time `u ≤ 1/2`. -/
private theorem boundedInitial_slice_legs {C B c' : ℝ} (hc' : 0 < c') {W L : ℕ} {g E : ℝ}
    (hreg : RegBdd C B c' L g E) {u : ℝ} (hu : u ≤ 1 / 2) (y : Ω W L) :
    (∀ (x x' : Fin L) (s : Bool),
      ‖biP W L x * sgnMat (resolventMat (blockSlice W L (Ag g L ⊗ₖ
          (1 : Matrix (Fin W) (Fin W) ℂ)) y) (zChar g E (mRoot g L E) u)) s * biP W L x'‖ ≤
        biG C c' * Real.exp (-(biMu C c' * cycDist x x'))) ∧
    (∀ s : Bool, ‖sgnMat (resolventMat (blockSlice W L (Ag g L ⊗ₖ
          (1 : Matrix (Fin W) (Fin W) ℂ)) y) (zChar g E (mRoot g L E) u)) s‖ ≤ biG C c') := by
  obtain ⟨V, hV, hVb, he⟩ := boundedInitial_slice_split g W L y
  have hg : 0 ≤ g := hreg.1
  have hη := biEta_pos (C := C) hc'
  have hz := biEta_le_im hc' hreg hu
  set G := resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)
    (zChar g E (mRoot g L E) u) with hG
  have h2 : 2 / biEta C c' ≤ biG C c' := le_max_left _ _
  have hct : ∀ x x' : Fin L, ‖biP W L x * G * biP W L x'‖ ≤
      biG C c' * Real.exp (-(biMu C c' * cycDist x x')) := by
    intro x x'
    rw [hG, he]
    refine (boundedInitial_ct W L g hg V hV hVb _ hη hz (biMu_pos hc').le
      (biMu_exp hc').le x x').trans ?_
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  have hGn : ‖G‖ ≤ biG C c' := by
    have hM := boundedInitial_slice_isHermitian g W L y
    have h1 : ‖G‖ ≤ (biEta C c')⁻¹ :=
      norm_resolventMat_le hM hη (hz.trans (le_abs_self _))
    refine h1.trans ((le_trans ?_ h2))
    rw [div_eq_mul_inv]
    have := inv_pos.mpr hη
    linarith
  refine ⟨fun x x' s => ?_, fun s => ?_⟩
  · cases s
    · have e : biP W L x * sgnMat G false * biP W L x' = (biP W L x' * G * biP W L x)ᴴ := by
        simp only [sgnMat, Bool.false_eq_true, ↓reduceIte, Matrix.conjTranspose_mul,
          (biP_isHermitian W L x).eq, (biP_isHermitian W L x').eq, Matrix.mul_assoc]
      rw [e, Matrix.l2_opNorm_conjTranspose, boundedInitial_cycDist_comm x x']
      exact hct x' x
    · simpa [sgnMat] using hct x x'
  · cases s
    · simpa [sgnMat, Matrix.l2_opNorm_conjTranspose] using hGn
    · simpa [sgnMat] using hGn

end BoundedInitialSlice

/-! ### Deterministic loop bounds along the slice -/

private theorem boundedInitial_rpow_eq {W : ℕ} (hW : 1 ≤ W) (q : ℕ) :
    (W : ℝ) ^ (1 - (q : ℝ)) = W * ((W : ℝ)⁻¹) ^ q := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [Real.rpow_sub hW0, Real.rpow_one, Real.rpow_natCast, inv_pow, div_eq_mul_inv]

/-- A single leg is at most the cyclic length. -/
private theorem boundedInitial_leg_le {L q : ℕ} (w : Fin q → Fin L) (p : Fin q) :
    (cycDist (w p) (w (finRotate q p)) : ℝ) ≤ loopLen w := by
  unfold loopLen
  push_cast
  exact Finset.single_le_sum (f := fun i => (cycDist (w i) (w (finRotate q i)) : ℝ))
    (fun i _ => Nat.cast_nonneg _) (Finset.mem_univ p)

private theorem boundedInitial_exp_leg {L q : ℕ} (w : Fin q → Fin L) (p : Fin q) {μ : ℝ}
    (hμ : 0 ≤ μ) :
    Real.exp (-(μ * loopLen w)) ≤ Real.exp (-(μ * cycDist (w p) (w (finRotate q p)))) := by
  refine Real.exp_le_exp.mpr ?_
  have := boundedInitial_leg_le w p
  nlinarith

/-- The inserted word has the leg `c → a_i`. -/
private theorem boundedInitial_loopLen_ins {L k : ℕ} (a : Fin k → Fin L) (i : Fin k) (c : Fin L)
    {μ : ℝ} (hμ : 0 ≤ μ) :
    Real.exp (-(μ * loopLen (insLab a i c))) ≤ Real.exp (-(μ * cycDist c (a i))) := by
  refine (boundedInitial_exp_leg (insLab a i c) i.castSucc hμ).trans (le_of_eq ?_)
  have h1 : insLab a i c i.castSucc = c := by simp [insLab]
  have h2 : finRotate (k + 1) i.castSucc = i.succ := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last i).ne]
    simp
  have h3 : insLab a i c i.succ = a i := by
    simp only [insLab]
    rw [← Fin.succAbove_castSucc_self, Fin.insertNth_apply_succAbove]
  rw [h1, h2, h3]

section BoundedInitialSliceLoops

open scoped Matrix.Norms.L2Operator

variable {C B c' : ℝ} {W L : ℕ} {g E : ℝ}

/-- `|ℒ_q| ≤ W W^{-q} g₀^q e^{-μ₀ loopLen}` at a slice point. -/
private theorem boundedInitial_slice_loop (hc' : 0 < c') (hW : 1 ≤ W) (hreg : RegBdd C B c' L g E)
    {u : ℝ} (hu : u ≤ 1 / 2) (y : Ω W L) {q : ℕ} (hq : 1 ≤ q) (w : Fin q → Fin L)
    (τ : Fin q → Bool) :
    ‖loopTr (resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)
        (zChar g E (mRoot g L E) u)) w τ‖ ≤
      W * ((W : ℝ)⁻¹) ^ q * (biG C c' ^ q * Real.exp (-(biMu C c' * loopLen w))) := by
  have h := boundedInitial_loop_le hW _ (boundedInitial_slice_legs hc' hreg hu y).1 hq w τ
  rwa [boundedInitial_rpow_eq hW] at h

/-- The bracket of a resolvent loop at a slice point: `|Γ(ℒ_k)| ≤ k² g₀^{2k+2} S W^{-2k}`. -/
private theorem boundedInitial_slice_gamma (hc' : 0 < c') (hW : 1 ≤ W)
    (hreg : RegBdd C B c' L g E) {u : ℝ} (hu : u ≤ 1 / 2) (y : Ω W L) {k : ℕ} (hk : 1 ≤ k)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ‖blockGamma W L (gammaG g) (resLoop g E (mRoot g L E) a σ u)
        (resLoop g E (mRoot g L E) a σ u)
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)‖ ≤
      (k : ℝ) ^ 2 * biG C c' ^ (2 * k + 2) * biS C c' * ((W : ℝ)⁻¹) ^ (2 * k) := by
  have hm : 0 < (mRoot g L E).im := hreg.2.2.2.1.1
  have hM := boundedInitial_slice_isHermitian g W L y
  have hu1 : u < 1 := by linarith
  rw [blockGamma_loopTr g E _ hm hu1 hM a σ a σ]
  set G := resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)
    (zChar g E (mRoot g L E) u) with hG
  obtain ⟨hleg, hX⟩ := boundedInitial_slice_legs hc' hreg hu y
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW0.ne'
  have hPE : ∀ c : Fin L, (W : ℂ) • blockE W L c = biP W L c := by
    intro c; rw [blockE_eq_biP, smul_smul, mul_inv_cancel₀ hWc, one_smul]
  have hg0 := (biG_pos C c').le
  set ω : ℝ := (W : ℝ)⁻¹ with hω
  have hω0 : 0 ≤ ω := by positivity
  have hBi : ∀ (c : Fin L) (i : Fin k), ‖biP W L c * loopB G a σ i * biP W L c‖ ≤
      ω ^ k * (biG C c' ^ (k + 1) * Real.exp (-(biMu C c' * cycDist c (a i)))) :=
    fun c i => boundedInitial_loopB_le hW G hg0 hleg hX hk a σ i c
  have hterm : ∀ (c : Fin L) (i j : Fin k),
      ‖((W : ℂ) • blockE W L c * loopB G a σ i * ((W : ℂ) • blockE W L c) *
        (loopB G a σ j)ᴴ).trace‖ ≤
      W * (ω ^ (2 * k) * biG C c' ^ (2 * k + 2) * Real.exp (-(biMu C c' * cycDist c (a i)))) := by
    intro c i j
    rw [hPE]
    set P := biP W L c
    set Bi := loopB G a σ i
    set Bj := loopB G a σ j
    have hPP : P * P = P := biP_mul_self W L c
    have hPh : Pᴴ = P := (biP_isHermitian W L c).eq
    have e : (P * Bi * P * Bjᴴ).trace = (P * ((P * Bi * P) * (P * Bj * P)ᴴ)).trace := by
      have e1 : (P * Bi * P * Bjᴴ).trace = (Bi * P * Bjᴴ * P).trace := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
      have e2 : (Bi * P * Bjᴴ * P).trace = (Bi * P * Bjᴴ * P * P).trace := by
        rw [Matrix.mul_assoc _ P P, hPP]
      have e3 : (Bi * P * Bjᴴ * P * P).trace = (P * (Bi * P * Bjᴴ * P)).trace := by
        rw [Matrix.trace_mul_comm]
      have e4 : P * ((P * Bi * P) * (P * Bj * P)ᴴ) = P * (Bi * P * Bjᴴ * P) := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPh]
        calc P * (P * Bi * P * (P * (Bjᴴ * P))) = (P * P) * Bi * (P * P) * Bjᴴ * P := by
              noncomm_ring
          _ = _ := by rw [hPP]; noncomm_ring
      rw [e1, e2, e3, e4]
    rw [e]
    refine (boundedInitial_trace_le c _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg W)
    calc ‖P * ((P * Bi * P) * (P * Bj * P)ᴴ)‖ ≤ ‖P‖ * ‖(P * Bi * P) * (P * Bj * P)ᴴ‖ :=
          norm_mul_le _ _
      _ ≤ 1 * (‖P * Bi * P‖ * ‖(P * Bj * P)ᴴ‖) :=
          mul_le_mul (norm_biP_le W L c) (norm_mul_le _ _) (norm_nonneg _) zero_le_one
      _ = ‖P * Bi * P‖ * ‖P * Bj * P‖ := by rw [one_mul, Matrix.l2_opNorm_conjTranspose]
      _ ≤ (ω ^ k * (biG C c' ^ (k + 1) * Real.exp (-(biMu C c' * cycDist c (a i))))) *
            (ω ^ k * (biG C c' ^ (k + 1) * 1)) := by
          refine mul_le_mul (hBi c i) ((hBi c j).trans ?_) (norm_nonneg _) (by positivity)
          gcongr
          exact Real.exp_le_one_iff.mpr (by
            have := (biMu_pos (C := C) hc').le
            have : (0 : ℝ) ≤ cycDist c (a j) := Nat.cast_nonneg _
            nlinarith)
      _ = ω ^ (2 * k) * biG C c' ^ (2 * k + 2) * Real.exp (-(biMu C c' * cycDist c (a i))) := by
          ring
  have hγ0 := gammaG_pos g
  have hγ1 := gammaG_le_one g
  calc ‖((gammaG g / W : ℝ) : ℂ) * ∑ c : Fin L, ∑ i : Fin k, ∑ j : Fin k,
        ((W : ℂ) • blockE W L c * loopB G a σ i * ((W : ℂ) • blockE W L c) *
          (loopB G a σ j)ᴴ).trace‖
      ≤ (gammaG g / W) * ∑ c : Fin L, ∑ i : Fin k, ∑ j : Fin k,
          W * (ω ^ (2 * k) * biG C c' ^ (2 * k + 2) *
            Real.exp (-(biMu C c' * cycDist c (a i)))) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        exact hterm c i j
    _ = gammaG g * (ω ^ (2 * k) * biG C c' ^ (2 * k + 2)) *
          ((k : ℝ) * ∑ i : Fin k, ∑ c : Fin L, Real.exp (-(biMu C c' * cycDist (a i) c))) := by
        have hs : ∑ c : Fin L, ∑ i : Fin k, ∑ j : Fin k,
            W * (ω ^ (2 * k) * biG C c' ^ (2 * k + 2) *
              Real.exp (-(biMu C c' * cycDist c (a i)))) =
            W * (ω ^ (2 * k) * biG C c' ^ (2 * k + 2)) *
              ((k : ℝ) * ∑ i : Fin k, ∑ c : Fin L, Real.exp (-(biMu C c' * cycDist (a i) c))) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [boundedInitial_cycDist_comm c (a i)]
          ring
        rw [hs]
        field_simp
    _ ≤ 1 * (ω ^ (2 * k) * biG C c' ^ (2 * k + 2)) * ((k : ℝ) * ∑ i : Fin k, biS C c') := by
        gcongr with i
        exact biS_sum (C := C) hc' (a i)
    _ = (k : ℝ) ^ 2 * biG C c' ^ (2 * k + 2) * biS C c' * ω ^ (2 * k) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end BoundedInitialSliceLoops

/-! ### Time-only functions in the class -/

/-- A `C¹` function of time alone lies in the class. -/
private theorem boundedInitial_heat_time {ι : Type*} [Fintype ι] {f f' : ℝ → ℂ} {a b : ℝ}
    (hf : ∀ r ∈ Set.Icc a b, HasDerivAt f (f' r) r) (hf' : ContinuousOn f' (Set.Icc a b)) :
    HeatClass (fun r (_ : ι → ℝ) => f r) a b := by
  have hfc : ContinuousOn f (Set.Icc a b) := fun r hr => (hf r hr).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hf'
  have hsub : ∀ r ∈ Set.Ioo a b, r ∈ Set.Icc a b := fun r hr => Set.Ioo_subset_Icc_self hr
  refine ⟨?_, ⟨C₀, fun r hr _ => hC₀ r (hsub r hr)⟩,
    ⟨fun r _ => f' r, fun r hr _ => hf r (hsub r hr), ?_, ⟨C₁, fun r hr _ => hC₁ r (hsub r hr)⟩⟩,
    ⟨fun _ _ => 0, fun _ _ => 0, fun r _ x => hasFDerivAt_const _ _,
      fun r _ x => hasFDerivAt_const _ _, continuousOn_const, continuousOn_const,
      ⟨0, fun r _ x => ⟨le_of_eq (norm_zero (E := (ι → ℝ) →L[ℝ] ℂ)),
        le_of_eq (norm_zero (E := (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ))⟩⟩⟩⟩
  · exact (hfc.mono Set.Ioo_subset_Icc_self).comp continuousOn_fst fun p hp => hp.1
  · exact (hf'.mono Set.Ioo_subset_Icc_self).comp continuousOn_fst fun p hp => hp.1

/-- Subtracting a `C¹` function of time keeps a function in the class. -/
private theorem boundedInitial_heat_sub_time {ι : Type*} [Fintype ι] {F : ℝ → (ι → ℝ) → ℂ}
    {f f' : ℝ → ℂ} {a b : ℝ} (hF : HeatClass F a b)
    (hf : ∀ r ∈ Set.Icc a b, HasDerivAt f (f' r) r) (hf' : ContinuousOn f' (Set.Icc a b)) :
    HeatClass (fun r y => F r y - f r) a b := by
  have h := hF.add (boundedInitial_heat_time (ι := ι) (f := fun r => -f r) (f' := fun r => -f' r)
    (fun r hr => (hf r hr).neg) hf'.neg)
  simpa only [sub_eq_add_neg] using h

/-! ### The one-loop errors `⟨G̃⟩_{cc}` -/

/-- `D_1(c, s) = ⟨G_r^s⟩_{cc} - m^s` along the slice. -/
private def bY1 (g E : ℝ) (W L : ℕ) (i : (Fin 1 → Fin L) × (Fin 1 → Bool)) (r : ℝ)
    (y : Ω W L) : ℂ :=
  loopTr (resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)
    (zChar g E (mRoot g L E) r)) i.1 i.2 - sgnScalar (mRoot g L E) (i.2 0)

private theorem bY1_heat {g E : ℝ} {W L : ℕ} (hm : 0 < (mRoot g L E).im)
    (i : (Fin 1 → Fin L) × (Fin 1 → Bool)) : HeatClass (bY1 g E W L i) (-1 / 2) (3 / 4) := by
  have h := heatClass_loopTr W L 1 (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
    (boundedInitial_Ag_isHermitian g W L) g E (mRoot g L E) hm i.1 i.2 (a' := -1 / 2)
    (b' := 3 / 4) (by norm_num)
  exact boundedInitial_heat_sub_time h (f := fun _ => sgnScalar (mRoot g L E) (i.2 0))
    (f' := fun _ => 0) (fun r _ => hasDerivAt_const _ _) continuousOn_const

/-- The slice at `0` is `A_g ⊗ I`, and `G_0 = M_B ⊗ I`. -/
private theorem boundedInitial_resolvent_zero (g E : ℝ) (W L : ℕ) (m : ℂ) :
    resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) 0) (zChar g E m 0) =
      dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
  have h0 : blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) 0 = flowH g W L 0 0 := by
    simp [blockSlice, flowH, blockFlow]
  rw [h0, resolvent_flow_zero]

private theorem boundedInitial_fin_one {α : Type*} (w : Fin 1 → α) : w = ![w 0] := by
  funext j; fin_cases j; rfl

private theorem bY1_zero {g E : ℝ} {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hroot : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E))
    (i : (Fin 1 → Fin L) × (Fin 1 → Bool)) : bY1 g E W L i 0 0 = 0 := by
  unfold bY1
  rw [boundedInitial_resolvent_zero, boundedInitial_fin_one i.1, boundedInitial_fin_one i.2,
    loopTr_one_dysonMat g E W L hW hL _ hroot]
  simp [sgnScalar]

/-- Subtracting a constant does not change the block generator. -/
private theorem boundedInitial_blockGen_sub_const {W L : ℕ} (γ : ℝ)
    (F : ℝ → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ → ℂ) (c : ℂ) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    blockGen W L γ (fun r N => F r N - c) u M = blockGen W L γ F u M := by
  unfold blockGen
  rw [deriv_sub_const]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one,
    deriv_sub_const_fun]

/-- Subtracting a constant does not change the bracket. -/
private theorem boundedInitial_blockGamma_sub_const {W L : ℕ} (γ : ℝ)
    (f : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ → ℂ) (c : ℂ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    blockGamma W L γ (fun N => f N - c) (fun N => f N - c) M = blockGamma W L γ f f M := by
  unfold blockGamma
  simp only [deriv_sub_const]

private theorem bY1_gen {g E : ℝ} {W L : ℕ} (hm : 0 < (mRoot g L E).im) {u : ℝ} (hu : u < 1)
    (i : (Fin 1 → Fin L) × (Fin 1 → Bool)) (y : Ω W L) :
    coordGen (gammaG g / W) (bY1 g E W L i) u y =
      lightW g E (mRoot g L E) i.1 i.2 u
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) := by
  have h := (blockGen_slice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (gammaG g)
    (fun r N => resLoop g E (mRoot g L E) i.1 i.2 r N - sgnScalar (mRoot g L E) (i.2 0)) u y).symm
  refine h.trans ?_
  rw [boundedInitial_blockGen_sub_const, blockGen_loopTr g E _ hm hu
    (boundedInitial_slice_isHermitian g W L y)]
  have : cutSumFam (fun n b τ => loopTr (resolventMat (blockSlice W L
      (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) (zChar g E (mRoot g L E) u)) b τ) i.1 i.2 = 0 := by
    simp [cutSumFam]
  rw [this, mul_zero, add_zero]

private theorem bY1_gamma {C B c' : ℝ} (hc' : 0 < c') {W L : ℕ} (hW : 1 ≤ W) {g E : ℝ}
    (hreg : RegBdd C B c' L g E) {u : ℝ} (hu : u ≤ 1 / 2) (i : (Fin 1 → Fin L) × (Fin 1 → Bool))
    (y : Ω W L) :
    ‖coordGamma (gammaG g / W) (bY1 g E W L i u) (bY1 g E W L i u) y‖ ≤
      biG C c' ^ 4 * biS C c' * ((W : ℝ)⁻¹) ^ 2 := by
  have h := (blockGamma_slice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (gammaG g)
    (fun N => resLoop g E (mRoot g L E) i.1 i.2 u N - sgnScalar (mRoot g L E) (i.2 0))
    (fun N => resLoop g E (mRoot g L E) i.1 i.2 u N - sgnScalar (mRoot g L E) (i.2 0)) y).symm
  have e : coordGamma (gammaG g / W) (bY1 g E W L i u) (bY1 g E W L i u) y =
      blockGamma W L (gammaG g) (resLoop g E (mRoot g L E) i.1 i.2 u)
        (resLoop g E (mRoot g L E) i.1 i.2 u)
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) :=
    h.trans (boundedInitial_blockGamma_sub_const _ _ _ _)
  rw [e]
  have := boundedInitial_slice_gamma hc' hW hreg hu y le_rfl i.1 i.2
  simpa using this

section BoundedInitialLight

open scoped Matrix.Norms.L2Operator

/-- The insertion term: `|𝒲_k| ≤ Σ_{i,c} W W^{-k} g₀^{k+1} e^{-μ₀‖c-a_i‖_L} |D_1(c, σ_i)|`. -/
private theorem boundedInitial_light_le {C B c' : ℝ} (hc' : 0 < c') {W L : ℕ} (hW : 1 ≤ W)
    {g E : ℝ} (hreg : RegBdd C B c' L g E) {u : ℝ} (hu : u ≤ 1 / 2) (y : Ω W L) {k : ℕ}
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ‖lightW g E (mRoot g L E) a σ u
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)‖ ≤
      ∑ i : Fin k, ∑ c : Fin L, (W * ((W : ℝ)⁻¹) ^ k * biG C c' ^ (k + 1) *
        Real.exp (-(biMu C c' * cycDist c (a i)))) * ‖bY1 g E W L (![c], ![σ i]) u y‖ := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγ0 := gammaG_pos g
  have hγ1 := gammaG_le_one g
  unfold lightW
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have hD : loopTr (resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)
      (zChar g E (mRoot g L E) u)) ![c] ![σ i] - sgnScalar (mRoot g L E) (σ i) =
      bY1 g E W L (![c], ![σ i]) u y := by simp [bY1]
  rw [hD, norm_mul, mul_comm ‖bY1 g E W L (![c], ![σ i]) u y‖, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hl := boundedInitial_slice_loop hc' hW hreg hu y (q := k + 1) (by omega) (insLab a i c)
    (insSgn σ i)
  have hleg := boundedInitial_loopLen_ins a i c (biMu_pos (C := C) hc').le
  have hg0 := (biG_pos C c').le
  calc gammaG g * W * ‖loopTr (resolventMat (blockSlice W L
        (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) (zChar g E (mRoot g L E) u))
        (insLab a i c) (insSgn σ i)‖
      ≤ 1 * W * (W * ((W : ℝ)⁻¹) ^ (k + 1) * (biG C c' ^ (k + 1) *
          Real.exp (-(biMu C c' * cycDist c (a i))))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hγ1 hW0.le) (hl.trans ?_) (norm_nonneg _)
          (by positivity)
        gcongr
    _ = W * ((W : ℝ)⁻¹) ^ k * biG C c' ^ (k + 1) * Real.exp (-(biMu C c' * cycDist c (a i))) := by
        have : (W : ℝ) * (W : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hW0.ne'
        rw [pow_succ]
        linear_combination (W * ((W : ℝ)⁻¹) ^ k * biG C c' ^ (k + 1) *
          Real.exp (-(biMu C c' * cycDist c (a i)))) * this

end BoundedInitialLight

/-- Moments of the one-loop errors: `‖⟨G̃_u⟩_{cc}‖_{2p} ≤ R₁ W^{-1}` on `[0, 1/2]` (the `k = 1`
recursion of Appendix C.2 [sec:bounded-proof], linear with zero source). -/
private def bR1 (C c' : ℝ) (p : ℕ) : ℝ :=
  bootC (biG C c' ^ 2 * biS C c') p * (biG C c' ^ 2 * Real.sqrt (biS C c'))

private theorem bR1_nonneg (C c' : ℝ) (p : ℕ) : 0 ≤ bR1 C c' p := by
  unfold bR1
  have := (biG_pos C c').le
  exact mul_nonneg (bootC_nonneg _ _) (by positivity)

private theorem bY1_mom {C B c' : ℝ} (hc' : 0 < c') {p : ℕ} (hp : 1 ≤ p) {W L : ℕ} (hW : 1 ≤ W)
    (hL : 1 ≤ L) {g E : ℝ} (hreg : RegBdd C B c' L g E) :
    ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ i, bMom (gammaG g / W) p (bY1 g E W L i) u ≤
      bR1 C c' p * (W : ℝ)⁻¹ := by
  have hm : 0 < (mRoot g L E).im := hreg.2.2.2.1.1
  have hroot := hreg.2.2.2.1
  have hσ : 0 ≤ gammaG g / W := div_nonneg (gammaG_pos g).le (Nat.cast_nonneg W)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hS := biS_pos (C := C) hc'
  have hg0 := (biG_pos C c').le
  have h := boundedInitial_boot (gammaG g / W) hσ p hp (bY1 g E W L) (by norm_num : (-1 / 2 : ℝ) < 0)
    (by norm_num : (1 / 2 : ℝ) < 3 / 4) (bY1_heat hm) (bY1_zero hW hL hroot)
    (T := biG C c' ^ 2 * biS C c') (β := 0) (B := biG C c' ^ 4 * biS C c' * ((W : ℝ)⁻¹) ^ 2)
    (by positivity) le_rfl (by positivity) ?_ ?_
  · intro u hu i
    refine (h u hu i).trans (le_of_eq ?_)
    unfold bR1
    rw [add_zero]
    have : Real.sqrt (biG C c' ^ 4 * biS C c' * ((W : ℝ)⁻¹) ^ 2) =
        biG C c' ^ 2 * Real.sqrt (biS C c') * (W : ℝ)⁻¹ := by
      rw [show biG C c' ^ 4 * biS C c' * ((W : ℝ)⁻¹) ^ 2 =
          (biG C c' ^ 2 * (W : ℝ)⁻¹) ^ 2 * biS C c' by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      ring
    rw [this]; ring
  · intro u hu S hS0 hSb i
    have hu2 : u ≤ 1 / 2 := hu.2.le
    have hu1 : u < 1 := by linarith [hu.2]
    have hur : u ∈ Set.Ioo (-1 / 2 : ℝ) (3 / 4) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hb := boundedInitial_mom_sum (gammaG g / W) hp (coordGen (gammaG g / W) (bY1 g E W L i))
      u (fun c : Fin L => bY1 g E W L (![c], ![i.2 0]) u)
      (fun c => biG C c' ^ 2 * Real.exp (-(biMu C c' * cycDist c (i.1 0)))) (fun _ => S)
      (fun c => by positivity) (fun _ => hS0)
      (fun c _ => boundedInitial_heat_integrable (bY1_heat hm _) hur _ _)
      (fun c _ => boundedInitial_int_le_of_bMom _ hp _ _ (hSb _)) ?_
    · refine hb.trans ?_
      rw [← Finset.sum_mul, add_zero]
      refine mul_le_mul_of_nonneg_right ?_ hS0
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := biS_sum (C := C) hc' (i.1 0)
      simpa only [boundedInitial_cycDist_comm _ (i.1 0)] using this
    · intro y
      rw [bY1_gen hm hu1]
      refine (boundedInitial_light_le hc' hW hreg hu2 y i.1 i.2).trans (le_of_eq ?_)
      simp only [Fin.sum_univ_one]
      refine Finset.sum_congr rfl fun c _ => ?_
      field_simp
      ring
  · intro u hu i
    exact boundedInitial_gamma_mom hp _ _ (by positivity)
      (bY1_gamma hc' hW hreg hu.2.le i)

/-! ### The entries `G̃_{pq}` -/

/-- `G̃_{pq} = (G_r - M_B ⊗ I)_{pq}` along the slice. -/
private def bYe (g E : ℝ) (W L : ℕ) (i : (Fin L × Fin W) × (Fin L × Fin W)) (r : ℝ)
    (y : Ω W L) : ℂ :=
  resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)
      (zChar g E (mRoot g L E) r) i.1 i.2 -
    (dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) i.1 i.2

private theorem bYe_heat {g E : ℝ} {W L : ℕ} (hm : 0 < (mRoot g L E).im)
    (i : (Fin L × Fin W) × (Fin L × Fin W)) : HeatClass (bYe g E W L i) (-1 / 2) (3 / 4) := by
  have h := heatClass_resolventEntry W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
    (boundedInitial_Ag_isHermitian g W L) g E (mRoot g L E) hm i.1 i.2 (a' := -1 / 2)
    (b' := 3 / 4) (by norm_num)
  exact boundedInitial_heat_sub_time h
    (f := fun _ => (dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ)) i.1 i.2) (f' := fun _ => 0) (fun r _ => hasDerivAt_const _ _)
    continuousOn_const

private theorem bYe_zero (g E : ℝ) (W L : ℕ) (i : (Fin L × Fin W) × (Fin L × Fin W)) :
    bYe g E W L i 0 0 = 0 := by
  unfold bYe
  rw [boundedInitial_resolvent_zero, sub_self]

/-- Completeness of the Hermitian basis: `Σ_k |Tr(T_k X)|² = ‖X‖²_HS`. -/
private theorem boundedInitial_sum_trace_sq (W : ℕ) (X : Matrix (Fin W) (Fin W) ℂ) :
    ∑ k : Fin W × Fin W, ‖∑ α, ∑ β, hermBasis W k α β * X β α‖ ^ 2 =
      ∑ α, ∑ β, ‖X β α‖ ^ 2 := by
  have hH : ∀ k α β, star (hermBasis W k α β) = hermBasis W k β α := by
    intro k α β
    have := congrFun (congrFun (hermBasis_isHermitian W k) β) α
    simpa [Matrix.conjTranspose_apply] using this
  have e1 : ∀ k : Fin W × Fin W, ((‖∑ α, ∑ β, hermBasis W k α β * X β α‖ ^ 2 : ℝ) : ℂ) =
      ∑ α, ∑ β, ∑ α', ∑ β', X β' α' * star (X β α) *
        (hermBasis W k α' β' * hermBasis W k β α) := by
    intro k
    rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def]
    simp only [star_sum, star_mul', hH, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    refine Finset.sum_congr rfl fun α' _ => Finset.sum_congr rfl fun β' _ => ?_
    ring
  apply Complex.ofReal_injective
  push_cast
  simp only [Complex.ofReal_pow] at e1
  rw [Finset.sum_congr rfl fun k _ => e1 k]
  have e2 : ∑ k : Fin W × Fin W, ∑ α, ∑ β, ∑ α', ∑ β', X β' α' * star (X β α) *
      (hermBasis W k α' β' * hermBasis W k β α) =
      ∑ α, ∑ β, ∑ α', ∑ β', X β' α' * star (X β α) *
        ∑ k : Fin W × Fin W, hermBasis W k α' β' * hermBasis W k β α := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β' _ => ?_
    rw [Finset.mul_sum]
  rw [e2]
  simp only [sum_hermBasis_apply_mul_apply]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.sum_eq_single α, Finset.sum_eq_single β]
  · simp only [and_self, ↓reduceIte, mul_one]
    rw [Complex.star_def, Complex.mul_conj']
  · intro β' _ hβ'; simp [hβ']
  · simp
  · intro α' _ hα'
    refine Finset.sum_eq_zero fun β' _ => ?_
    simp [hα']
  · simp

section BoundedInitialEntries

open scoped Matrix.Norms.L2Operator

/-- The entry functional as a continuous linear map. -/
private def boundedInitialEntry {n : Type*} [Fintype n] (p q : n) : Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M p q
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- `∂_T G_{pq} = -(G T G)_{pq}` along a Hermitian direction. -/
private theorem boundedInitial_deriv_entry {n : Type*} [Fintype n] [DecidableEq n]
    {M T : Matrix n n ℂ} (hM : M.IsHermitian) (hT : T.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (p q : n) :
    deriv (fun e : ℝ => resolventMat (M + (e : ℂ) • T) z p q) 0 =
      -(resolventMat M z * T * resolventMat M z) p q := by
  have h := hasDerivAt_resolventMat_line hM hT hz 0
  have h2 := (boundedInitialEntry p q).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e := h2.deriv
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at e
  exact e


/-- A column has Euclidean norm at most the operator norm. -/
private theorem boundedInitial_col_le {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (j : n) : ∑ i, ‖A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  have h1 := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j 1)
  rw [← Matrix.cstar_norm_def] at h1
  have h2 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [h2, mul_one] at h1
  have h3 : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)‖ ^ 2 =
      ∑ i, ‖A i j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM]
    simp [Matrix.mulVec, dotProduct]
  rw [← h3]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- A row has Euclidean norm at most the operator norm. -/
private theorem boundedInitial_row_le {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (i : n) : ∑ j, ‖A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  have := boundedInitial_col_le Aᴴ i
  rw [Matrix.l2_opNorm_conjTranspose] at this
  simpa [Matrix.conjTranspose_apply] using this

variable {C B c' : ℝ} {W L : ℕ} {g E : ℝ}

/-- `|γW(G E_c G)_{pq}| ≤ g₀² e^{-μ₀‖p_1-c‖_L}` at a slice point. -/
private theorem boundedInitial_slice_GPG (hc' : 0 < c') (hW : 1 ≤ W) (hreg : RegBdd C B c' L g E)
    {u : ℝ} (hu : u ≤ 1 / 2) (y : Ω W L) (c : Fin L) (p q : Fin L × Fin W) :
    ‖((gammaG g * W : ℝ) : ℂ) * (resolventMat (blockSlice W L (Ag g L ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ)) y) (zChar g E (mRoot g L E) u) * blockE W L c *
        resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)
          (zChar g E (mRoot g L E) u)) p q‖ ≤
      biG C c' ^ 2 * Real.exp (-(biMu C c' * cycDist p.1 c)) := by
  set G := resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)
    (zChar g E (mRoot g L E) u)
  obtain ⟨hleg, hX⟩ := boundedInitial_slice_legs hc' hreg hu y
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW0.ne'
  have e1 : ((gammaG g * W : ℝ) : ℂ) * (G * blockE W L c * G) p q =
      (gammaG g : ℂ) * (biP W L p.1 * G * biP W L c * (biP W L c * G * biP W L q.1)) p q := by
    rw [blockE_eq_biP]
    have e2 : (biP W L p.1 * G * biP W L c * (biP W L c * G * biP W L q.1)) p q =
        (G * biP W L c * G) p q := by
      have hPP := biP_mul_self W L c
      have : biP W L p.1 * G * biP W L c * (biP W L c * G * biP W L q.1) =
          biP W L p.1 * (G * biP W L c * G) * biP W L q.1 := by
        calc biP W L p.1 * G * biP W L c * (biP W L c * G * biP W L q.1) =
            biP W L p.1 * G * (biP W L c * biP W L c) * G * biP W L q.1 := by noncomm_ring
          _ = _ := by rw [hPP]; noncomm_ring
      rw [this]
      simp [biP, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [e2, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  rw [e1, norm_mul, Complex.norm_real, Real.norm_of_nonneg (gammaG_pos g).le]
  have hg0 := (biG_pos C c').le
  calc gammaG g * ‖(biP W L p.1 * G * biP W L c * (biP W L c * G * biP W L q.1)) p q‖ ≤
      1 * (‖biP W L p.1 * G * biP W L c‖ * ‖biP W L c * G * biP W L q.1‖) := by
        refine mul_le_mul (gammaG_le_one g) ((boundedInitial_norm_entry_le _ p q).trans
          (norm_mul_le _ _)) (norm_nonneg _) zero_le_one
    _ ≤ 1 * ((biG C c' * Real.exp (-(biMu C c' * cycDist p.1 c))) * biG C c') := by
        gcongr
        · simpa [sgnMat] using hleg p.1 c true
        · exact (norm_biP_mul_biP_le W L c q.1 G).trans (by simpa [sgnMat] using hX true)
    _ = biG C c' ^ 2 * Real.exp (-(biMu C c' * cycDist p.1 c)) := by ring

/-- The bracket of an entry at a slice point: `|Γ(G_{pq})| ≤ g₀⁴ S W^{-1}`. -/
private theorem boundedInitial_slice_gamma_entry (hc' : 0 < c') (hW : 1 ≤ W)
    (hreg : RegBdd C B c' L g E) {u : ℝ} (hu : u ≤ 1 / 2) (y : Ω W L) (p q : Fin L × Fin W) :
    ‖blockGamma W L (gammaG g)
        (fun N => resolventMat N (zChar g E (mRoot g L E) u) p q)
        (fun N => resolventMat N (zChar g E (mRoot g L E) u) p q)
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)‖ ≤
      biG C c' ^ 4 * biS C c' * (W : ℝ)⁻¹ := by
  set M := blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y
  have hM : M.IsHermitian := boundedInitial_slice_isHermitian g W L y
  have hm : 0 < (mRoot g L E).im := hreg.2.2.2.1.1
  have hz : (zChar g E (mRoot g L E) u).im ≠ 0 := by
    have := biEta_le_im hc' hreg hu
    have := biEta_pos (C := C) hc'
    linarith
  set G := resolventMat M (zChar g E (mRoot g L E) u) with hG
  obtain ⟨hleg, hX⟩ := boundedInitial_slice_legs hc' hreg hu y
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hg0 := (biG_pos C c').le
  -- the derivative along a basis direction
  have hd : ∀ (c : Fin L) (κ : Fin W × Fin W),
      deriv (fun e : ℝ => resolventMat (M + (e : ℂ) • blockBasis W L c κ)
        (zChar g E (mRoot g L E) u) p q) 0 =
      -∑ α, ∑ β, hermBasis W κ α β * (G (c, β) q * G p (c, α)) := by
    intro c κ
    rw [boundedInitial_deriv_entry hM (blockBasis_isHermitian W L c κ) hz p q]
    congr 1
    simp only [Matrix.mul_apply, blockBasis, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single c, Finset.sum_comm, Finset.sum_eq_single c]
    · refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
      simp only [and_self, ↓reduceIte]
      ring
    · intro b _ hb
      refine Finset.sum_eq_zero fun β _ => Finset.sum_eq_zero fun α _ => ?_
      simp [hb]
    · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun x _ => ?_
      refine Finset.sum_eq_zero fun β _ => ?_
      simp [hb]
    · simp
  have hsum : ∀ c : Fin L, ∑ κ : Fin W × Fin W,
      ‖deriv (fun e : ℝ => resolventMat (M + (e : ℂ) • blockBasis W L c κ)
        (zChar g E (mRoot g L E) u) p q) 0‖ ^ 2 ≤
      biG C c' ^ 4 * Real.exp (-(biMu C c' * cycDist p.1 c)) := by
    intro c
    simp only [hd, norm_neg]
    have hst := boundedInitial_sum_trace_sq W (Matrix.of fun β α => G (c, β) q * G p (c, α))
    simp only [Matrix.of_apply] at hst
    rw [hst]
    simp only [norm_mul, mul_pow]
    have hr : ∑ α, ‖G p (c, α)‖ ^ 2 ≤ ‖biP W L p.1 * G * biP W L c‖ ^ 2 := by
      refine le_trans ?_ (boundedInitial_row_le _ p)
      have : ∀ α, G p (c, α) = (biP W L p.1 * G * biP W L c) p (c, α) := by
        intro α; simp [biP, Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [this]
      rw [Fintype.sum_prod_type]
      exact Finset.single_le_sum (f := fun b => ∑ α, ‖(biP W L p.1 * G * biP W L c) p (b, α)‖ ^ 2)
        (fun b _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ c)
    have hc : ∑ β, ‖G (c, β) q‖ ^ 2 ≤ ‖biP W L c * G * biP W L q.1‖ ^ 2 := by
      refine le_trans ?_ (boundedInitial_col_le _ q)
      have : ∀ β, G (c, β) q = (biP W L c * G * biP W L q.1) (c, β) q := by
        intro β; simp [biP, Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [this]
      rw [Fintype.sum_prod_type]
      exact Finset.single_le_sum (f := fun b => ∑ β, ‖(biP W L c * G * biP W L q.1) (b, β) q‖ ^ 2)
        (fun b _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ c)
    have e : ∑ α, ∑ β, ‖G (c, β) q‖ ^ 2 * ‖G p (c, α)‖ ^ 2 =
        (∑ α, ‖G p (c, α)‖ ^ 2) * ∑ β, ‖G (c, β) q‖ ^ 2 := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      ring
    rw [e]
    have h1 : ‖biP W L p.1 * G * biP W L c‖ ≤ biG C c' * Real.exp (-(biMu C c' * cycDist p.1 c)) := by
      simpa [sgnMat] using hleg p.1 c true
    have h2 : ‖biP W L c * G * biP W L q.1‖ ≤ biG C c' :=
      (norm_biP_mul_biP_le W L c q.1 G).trans (by simpa [sgnMat] using hX true)
    have hex : Real.exp (-(biMu C c' * cycDist p.1 c)) ^ 2 ≤ Real.exp (-(biMu C c' * cycDist p.1 c)) := by
      have h0 : 0 ≤ Real.exp (-(biMu C c' * cycDist p.1 c)) := (Real.exp_pos _).le
      have h1' : Real.exp (-(biMu C c' * cycDist p.1 c)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have := (biMu_pos (C := C) hc').le
        have : (0 : ℝ) ≤ cycDist p.1 c := Nat.cast_nonneg _
        nlinarith)
      nlinarith
    calc (∑ α, ‖G p (c, α)‖ ^ 2) * ∑ β, ‖G (c, β) q‖ ^ 2 ≤
        (biG C c' * Real.exp (-(biMu C c' * cycDist p.1 c))) ^ 2 * biG C c' ^ 2 := by
          refine mul_le_mul (hr.trans (pow_le_pow_left₀ (norm_nonneg _) h1 2))
            (hc.trans (pow_le_pow_left₀ (norm_nonneg _) h2 2))
            (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
      _ = biG C c' ^ 4 * Real.exp (-(biMu C c' * cycDist p.1 c)) ^ 2 := by ring
      _ ≤ biG C c' ^ 4 * Real.exp (-(biMu C c' * cycDist p.1 c)) :=
          mul_le_mul_of_nonneg_left hex (by positivity)
  unfold blockGamma
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by have := gammaG_pos g; positivity)]
  have hnorm : ‖∑ c : Fin L, ∑ κ : Fin W × Fin W,
      deriv (fun e : ℝ => resolventMat (M + (e : ℂ) • blockBasis W L c κ)
        (zChar g E (mRoot g L E) u) p q) 0 *
      star (deriv (fun e : ℝ => resolventMat (M + (e : ℂ) • blockBasis W L c κ)
        (zChar g E (mRoot g L E) u) p q) 0)‖ ≤ biG C c' ^ 4 * biS C c' := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c : Fin L, ‖∑ κ : Fin W × Fin W,
          deriv (fun e : ℝ => resolventMat (M + (e : ℂ) • blockBasis W L c κ)
            (zChar g E (mRoot g L E) u) p q) 0 *
          star (deriv (fun e : ℝ => resolventMat (M + (e : ℂ) • blockBasis W L c κ)
            (zChar g E (mRoot g L E) u) p q) 0)‖ ≤
        ∑ c : Fin L, biG C c' ^ 4 * Real.exp (-(biMu C c' * cycDist p.1 c)) := by
          refine Finset.sum_le_sum fun c _ => ((norm_sum_le _ _).trans (le_of_eq ?_)).trans
            (hsum c)
          refine Finset.sum_congr rfl fun κ _ => ?_
          rw [norm_mul, norm_star, sq]
      _ ≤ biG C c' ^ 4 * biS C c' := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (biS_sum hc' p.1) (by positivity)
  calc gammaG g / W * ‖∑ c : Fin L, ∑ κ : Fin W × Fin W,
        deriv (fun e : ℝ => resolventMat (M + (e : ℂ) • blockBasis W L c κ)
          (zChar g E (mRoot g L E) u) p q) 0 *
        star (deriv (fun e : ℝ => resolventMat (M + (e : ℂ) • blockBasis W L c κ)
          (zChar g E (mRoot g L E) u) p q) 0)‖ ≤ 1 / W * (biG C c' ^ 4 * biS C c') := by
        refine mul_le_mul (div_le_div_of_nonneg_right (gammaG_le_one g) hW0.le) hnorm
          (norm_nonneg _) (by positivity)
    _ = biG C c' ^ 4 * biS C c' * (W : ℝ)⁻¹ := by ring

end BoundedInitialEntries

private theorem bYe_gen_le {C B c' : ℝ} (hc' : 0 < c') {W L : ℕ} (hW : 1 ≤ W) {g E : ℝ}
    (hreg : RegBdd C B c' L g E) {u : ℝ} (hu : u ≤ 1 / 2) (i : (Fin L × Fin W) × (Fin L × Fin W))
    (y : Ω W L) :
    ‖coordGen (gammaG g / W) (bYe g E W L i) u y‖ ≤
      ∑ c : Fin L, biG C c' ^ 2 * Real.exp (-(biMu C c' * cycDist i.1.1 c)) *
        ‖bY1 g E W L (![c], ![true]) u y‖ := by
  have hm : 0 < (mRoot g L E).im := hreg.2.2.2.1.1
  have hu1 : u < 1 := by linarith
  have h := (blockGen_slice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (gammaG g)
    (fun r N => resolventMat N (zChar g E (mRoot g L E) r) i.1 i.2 -
      (dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) i.1 i.2)
    u y).symm
  have e : coordGen (gammaG g / W) (bYe g E W L i) u y =
      ∑ c : Fin L, bY1 g E W L (![c], ![true]) u y *
        (((gammaG g * W : ℝ) : ℂ) * (resolventMat (blockSlice W L (Ag g L ⊗ₖ
          (1 : Matrix (Fin W) (Fin W) ℂ)) y) (zChar g E (mRoot g L E) u) * blockE W L c *
          resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)
            (zChar g E (mRoot g L E) u)) i.1 i.2) := by
    refine h.trans ?_
    rw [boundedInitial_blockGen_sub_const, blockGen_resolvent g E _ hm hu1
      (boundedInitial_slice_isHermitian g W L y), Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [bY1, Matrix.cons_val_zero, sgnScalar, ↓reduceIte]
    ring
  rw [e]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (boundedInitial_slice_GPG hc' hW hreg hu y c i.1 i.2)
    (norm_nonneg _)

private theorem bYe_gamma {C B c' : ℝ} (hc' : 0 < c') {W L : ℕ} (hW : 1 ≤ W) {g E : ℝ}
    (hreg : RegBdd C B c' L g E) {u : ℝ} (hu : u ≤ 1 / 2) (i : (Fin L × Fin W) × (Fin L × Fin W))
    (y : Ω W L) :
    ‖coordGamma (gammaG g / W) (bYe g E W L i u) (bYe g E W L i u) y‖ ≤
      biG C c' ^ 4 * biS C c' * (W : ℝ)⁻¹ := by
  have h := (blockGamma_slice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (gammaG g)
    (fun N => resolventMat N (zChar g E (mRoot g L E) u) i.1 i.2 -
      (dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) i.1 i.2)
    (fun N => resolventMat N (zChar g E (mRoot g L E) u) i.1 i.2 -
      (dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) i.1 i.2)
    y).symm
  have e : coordGamma (gammaG g / W) (bYe g E W L i u) (bYe g E W L i u) y =
      blockGamma W L (gammaG g) (fun N => resolventMat N (zChar g E (mRoot g L E) u) i.1 i.2)
        (fun N => resolventMat N (zChar g E (mRoot g L E) u) i.1 i.2)
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) :=
    h.trans (boundedInitial_blockGamma_sub_const _ _ _ _)
  rw [e]
  exact boundedInitial_slice_gamma_entry hc' hW hreg hu y i.1 i.2

/-- The entry constant `R_e`. -/
private def bRe (C c' : ℝ) (p : ℕ) : ℝ :=
  bootC 0 p * (biG C c' ^ 2 * (Real.sqrt (biS C c') + biS C c' * bR1 C c' p))

/-- Moments of the entries: `‖G̃_{pq}(u)‖_{2p} ≤ R_e W^{-1/2}` on `[0, 1/2]`. -/
private theorem bYe_mom {C B c' : ℝ} (hc' : 0 < c') {p : ℕ} (hp : 1 ≤ p) {W L : ℕ} (hW : 1 ≤ W)
    (hL : 1 ≤ L) {g E : ℝ} (hreg : RegBdd C B c' L g E) :
    ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ i, bMom (gammaG g / W) p (bYe g E W L i) u ≤
      bRe C c' p * Real.sqrt ((W : ℝ)⁻¹) := by
  have hm : 0 < (mRoot g L E).im := hreg.2.2.2.1.1
  have hσ : 0 ≤ gammaG g / W := div_nonneg (gammaG_pos g).le (Nat.cast_nonneg W)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hS := biS_pos (C := C) hc'
  have hg0 := (biG_pos C c').le
  have hR1 := bR1_nonneg C c' p
  have hω0 : 0 ≤ (W : ℝ)⁻¹ := by positivity
  have hω1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hW)
  have h := boundedInitial_boot (gammaG g / W) hσ p hp (bYe g E W L) (by norm_num : (-1 / 2 : ℝ) < 0)
    (by norm_num : (1 / 2 : ℝ) < 3 / 4) (bYe_heat hm) (bYe_zero g E W L)
    (T := 0) (β := biG C c' ^ 2 * biS C c' * (bR1 C c' p * (W : ℝ)⁻¹))
    (B := biG C c' ^ 4 * biS C c' * (W : ℝ)⁻¹) le_rfl (by positivity) (by positivity) ?_ ?_
  · intro u hu i
    refine (h u hu i).trans ?_
    unfold bRe
    have hsq : Real.sqrt (biG C c' ^ 4 * biS C c' * (W : ℝ)⁻¹) =
        biG C c' ^ 2 * Real.sqrt (biS C c') * Real.sqrt ((W : ℝ)⁻¹) := by
      rw [show biG C c' ^ 4 * biS C c' * (W : ℝ)⁻¹ = (biG C c' ^ 2) ^ 2 * (biS C c' * (W : ℝ)⁻¹)
          by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
        Real.sqrt_mul hS.le]
      ring
    have hωs : (W : ℝ)⁻¹ ≤ Real.sqrt ((W : ℝ)⁻¹) := by
      rw [Real.le_sqrt hω0 hω0]; nlinarith
    rw [hsq]
    have hb0 := bootC_nonneg 0 p
    have : biG C c' ^ 2 * Real.sqrt (biS C c') * Real.sqrt ((W : ℝ)⁻¹) +
        biG C c' ^ 2 * biS C c' * (bR1 C c' p * (W : ℝ)⁻¹) ≤
        biG C c' ^ 2 * (Real.sqrt (biS C c') + biS C c' * bR1 C c' p) *
          Real.sqrt ((W : ℝ)⁻¹) := by
      have : biG C c' ^ 2 * biS C c' * (bR1 C c' p * (W : ℝ)⁻¹) ≤
          biG C c' ^ 2 * biS C c' * (bR1 C c' p * Real.sqrt ((W : ℝ)⁻¹)) := by gcongr
      nlinarith
    calc bootC 0 p * (biG C c' ^ 2 * Real.sqrt (biS C c') * Real.sqrt ((W : ℝ)⁻¹) +
          biG C c' ^ 2 * biS C c' * (bR1 C c' p * (W : ℝ)⁻¹)) ≤
        bootC 0 p * (biG C c' ^ 2 * (Real.sqrt (biS C c') + biS C c' * bR1 C c' p) *
          Real.sqrt ((W : ℝ)⁻¹)) := mul_le_mul_of_nonneg_left this hb0
      _ = _ := by ring
  · intro u hu S hS0 _ i
    have hu2 : u ≤ 1 / 2 := hu.2.le
    have hur : u ∈ Set.Ioo (-1 / 2 : ℝ) (3 / 4) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hb := boundedInitial_mom_sum (gammaG g / W) hp (coordGen (gammaG g / W) (bYe g E W L i))
      u (fun c : Fin L => bY1 g E W L (![c], ![true]) u)
      (fun c => biG C c' ^ 2 * Real.exp (-(biMu C c' * cycDist i.1.1 c)))
      (fun _ => bR1 C c' p * (W : ℝ)⁻¹)
      (fun c => by positivity) (fun _ => by positivity)
      (fun c _ => boundedInitial_heat_integrable (bY1_heat hm _) hur _ _)
      (fun c _ => boundedInitial_int_le_of_bMom _ hp _ _
        (bY1_mom hc' hp hW hL hreg u ⟨hu.1.le, hu2⟩ _))
      (fun y => bYe_gen_le hc' hW hreg hu2 i y)
    refine hb.trans ?_
    rw [← Finset.sum_mul, zero_mul, zero_add, ← Finset.mul_sum]
    have := biS_sum (C := C) hc' i.1.1
    have h1 : biG C c' ^ 2 * ∑ c : Fin L, Real.exp (-(biMu C c' * cycDist i.1.1 c)) ≤
        biG C c' ^ 2 * biS C c' := mul_le_mul_of_nonneg_left this (by positivity)
    nlinarith [mul_nonneg hR1 hω0]
  · intro u hu i
    exact boundedInitial_gamma_mom hp _ _ (by positivity) (bYe_gamma hc' hW hreg hu.2.le i)

/-! ### From moments to probabilities -/

/-- Markov's inequality at order `2p` with a union bound over a finite family. -/
private theorem boundedInitial_markov {W L : ℕ} {I : Type*} [Fintype I] {p : ℕ} (hp : 1 ≤ p)
    (σ2 u : ℝ) (Y : I → ℝ → Ω W L → ℂ) {a b : ℝ} (hY : ∀ i, HeatClass (Y i) a b)
    (hu : u ∈ Set.Ioo a b) {t M : ℝ} (ht : 0 < t) (hM : ∀ i, bMom σ2 p (Y i) u ≤ M) :
    μ W L {ω | ∃ i, t < ‖Y i u (Real.sqrt (u * σ2) • ω)‖} ≤
      ENNReal.ofReal (Fintype.card I * (M / t) ^ (2 * p)) := by
  have hset : {ω | ∃ i, t < ‖Y i u (Real.sqrt (u * σ2) • ω)‖} =
      ⋃ i, {ω | t < ‖Y i u (Real.sqrt (u * σ2) • ω)‖} := by
    ext ω; simp
  rw [hset]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  have hμ : μ W L = stdGauss (Fin L × Fin W × Fin W) := rfl
  have hone : ∀ i, μ W L {ω | t < ‖Y i u (Real.sqrt (u * σ2) • ω)‖} ≤
      ENNReal.ofReal ((M / t) ^ (2 * p)) := by
    intro i
    set f : Ω W L → ℝ := fun ω => ‖Y i u (Real.sqrt (u * σ2) • ω)‖ ^ (2 * p) with hf
    have hsub : {ω | t < ‖Y i u (Real.sqrt (u * σ2) • ω)‖} ⊆ {ω | t ^ (2 * p) ≤ f ω} := by
      intro ω hω
      exact pow_le_pow_left₀ ht.le (le_of_lt hω) _
    refine (measure_mono hsub).trans ?_
    have hint : Integrable f (μ W L) := by
      rw [hμ]; exact boundedInitial_heat_integrable (hY i) hu _ _
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ W L) (ae_of_all _ fun ω => by
      simp only [hf]; positivity) hint (t ^ (2 * p))
    have hI : ∫ ω, f ω ∂(μ W L) ≤ M ^ (2 * p) := by
      rw [hμ]; exact boundedInitial_int_le_of_bMom σ2 hp (Y i) u (hM i)
    have htp : 0 < t ^ (2 * p) := by positivity
    have hreal : (μ W L).real {ω | t ^ (2 * p) ≤ f ω} ≤ (M / t) ^ (2 * p) := by
      rw [div_pow, le_div_iff₀ htp]
      linarith
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hreal
  calc ∑ i, μ W L {ω | t < ‖Y i u (Real.sqrt (u * σ2) • ω)‖} ≤
      ∑ _i : I, ENNReal.ofReal ((M / t) ^ (2 * p)) := Finset.sum_le_sum fun i _ => hone i
    _ = ENNReal.ofReal (Fintype.card I * (M / t) ^ (2 * p)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]

/-- `ζ_u ≥ ℓ_max^{-1} W^{-1}` on `[0, 1/2]` at bounded coupling. -/
private theorem boundedInitial_zeta_ge {C : ℝ} {g : ℝ} (hg : 0 ≤ g) (hgC : g ≤ C)
    {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    (1 + 2 * C * max 1 C)⁻¹ * (W : ℝ)⁻¹ ≤ zetaProp g W L u := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγ0 := gammaG_pos g
  have hγ1 := gammaG_le_one g
  have hm1 : (1 : ℝ) ≤ max 1 g := le_max_left _ _
  have hmC : max 1 g ≤ max 1 C := max_le_max le_rfl hgC
  have hC0 : 0 ≤ C := hg.trans hgC
  have h1u : 0 < 1 - u := by linarith
  have hs : Real.sqrt (gammaG g * (1 - u)) = (max 1 g)⁻¹ * Real.sqrt (1 - u) := by
    rw [Real.sqrt_mul hγ0.le, gammaG, Real.sqrt_inv, Real.sqrt_sq (by linarith)]
  have hsu : (1 / 2 : ℝ) ≤ Real.sqrt (1 - u) := by
    rw [Real.le_sqrt (by norm_num) h1u.le]; nlinarith
  have hspos : 0 < Real.sqrt (1 - u) := by linarith
  have key : g / Real.sqrt (gammaG g * (1 - u)) ≤ 2 * C * max 1 C := by
    rw [hs, div_eq_mul_inv, mul_inv, inv_inv]
    have hinv : (Real.sqrt (1 - u))⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hspos (by norm_num)]; linarith
    calc g * (max 1 g * (Real.sqrt (1 - u))⁻¹) ≤ C * (max 1 C * 2) := by
          gcongr
      _ = 2 * C * max 1 C := by ring
  set ℓ := ellProp g L u with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, ellProp]
    refine le_min (by exact_mod_cast hL) ?_
    have : 0 ≤ g / Real.sqrt (gammaG g * (1 - u)) := by positivity
    linarith
  have hℓb : ℓ ≤ 1 + 2 * C * max 1 C := by
    rw [hℓ, ellProp]
    exact (min_le_right _ _).trans (by linarith)
  rw [zetaProp, ← hℓ, ← mul_inv]
  refine inv_anti₀ (by positivity) ?_
  have h1 : ℓ * (1 - u) * gammaG g ≤ ℓ := by
    have : (1 - u) * gammaG g ≤ 1 := by nlinarith
    nlinarith
  calc (W : ℝ) * ℓ * (1 - u) * gammaG g = W * (ℓ * (1 - u) * gammaG g) := by ring
    _ ≤ W * (1 + 2 * C * max 1 C) := by
        refine mul_le_mul_of_nonneg_left (h1.trans hℓb) hW0.le
    _ = (1 + 2 * C * max 1 C) * W := by ring

/-- The realization on the slice: `H_u = A_g ⊗ I + Σ (√(uγ/W) ω)_{c,k} T_{c,k}`. -/
private theorem boundedInitial_flowH_slice (g : ℝ) (W L : ℕ) {u : ℝ} (hu : 0 ≤ u) (ω : Ω W L) :
    flowH g W L u ω = blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
      (Real.sqrt (u * (gammaG g / W)) • ω) := by
  unfold flowH
  rw [blockFlow_eq_blockSlice W L _ (mul_nonneg hu (gammaG_pos g).le) ω, mul_div_assoc]

/-- The final count: `N ≤ W^a`, `X ≤ K W^{-2pε}`, `K ≤ W` and `a + 1 + D ≤ 2pε` give
`N X ≤ W^{-D}`. -/
private theorem boundedInitial_final {W : ℕ} (hW : 1 ≤ W) {N X K s D : ℝ} {a : ℕ} (hN0 : 0 ≤ N)
    (hN : N ≤ (W : ℝ) ^ a) (hX : X ≤ K * (W : ℝ) ^ (-s)) (hK : K ≤ W)
    (hs : (a : ℝ) + 1 + D ≤ s) : N * X ≤ (W : ℝ) ^ (-D) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hX0 : X ≤ W * (W : ℝ) ^ (-s) :=
    hX.trans (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hW0.le _))
  calc N * X ≤ (W : ℝ) ^ a * (W * (W : ℝ) ^ (-s)) := by
        rcases le_or_gt 0 X with h | h
        · exact mul_le_mul hN hX0 h (by positivity)
        · have : N * X ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN0 h.le
          exact this.trans (by positivity)
    _ = (W : ℝ) ^ ((a : ℝ) + 1 + -s) := by
        rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one, Real.rpow_natCast]; ring
    _ ≤ (W : ℝ) ^ (-D) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)

/-- `(M/t)^{2p}` with `M/t ≤ R W^{-ε}`. -/
private theorem boundedInitial_pow_ratio {W : ℕ} (hW : 1 ≤ W) {X R ε : ℝ} {p : ℕ} (hX0 : 0 ≤ X)
    (hX : X ≤ R * (W : ℝ) ^ (-ε)) :
    X ^ (2 * p) ≤ R ^ (2 * p) * (W : ℝ) ^ (-(2 * p * ε)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hR : 0 ≤ R * (W : ℝ) ^ (-ε) := hX0.trans hX
  calc X ^ (2 * p) ≤ (R * (W : ℝ) ^ (-ε)) ^ (2 * p) := pow_le_pow_left₀ hX0 hX _
    _ = R ^ (2 * p) * (W : ℝ) ^ (-(2 * p * ε)) := by
        rw [mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ (-ε)), ← Real.rpow_mul hW0.le]
        congr 2
        push_cast; ring

/-! ### Primitive families -/

/-- The primitive family is continuous on `[-1/2, 3/4]`. -/
private theorem boundedInitial_Kp_cont {W L : ℕ} {γ : ℝ} {Kp : ℝ → LoopFam L}
    (hK : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, IsPrimDeriv γ W L Kp u) (n : ℕ) (w : Fin n → Fin L)
    (τ : Fin n → Bool) : ContinuousOn (fun r => Kp r n w τ) (Set.Icc (-1 / 2) (3 / 4)) :=
  fun r hr => ((hK r ⟨by linarith [hr.1], by linarith [hr.2]⟩) n w τ).continuousAt.continuousWithinAt

private theorem boundedInitial_cutSum_cont {W L : ℕ} {γ : ℝ} {Kp : ℝ → LoopFam L}
    (hK : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, IsPrimDeriv γ W L Kp u) {n : ℕ} (w : Fin n → Fin L)
    (τ : Fin n → Bool) :
    ContinuousOn (fun r => ((γ * W : ℝ) : ℂ) * cutSumFam (Kp r) w τ) (Set.Icc (-1 / 2) (3 / 4)) := by
  refine continuousOn_const.mul ?_
  unfold cutSumFam
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  split_ifs
  · exact continuousOn_finsetSum _ fun c _ =>
      (boundedInitial_Kp_cont hK _ _ _).mul (boundedInitial_Kp_cont hK _ _ _)
  · exact continuousOn_const

/-- The length-one member of a primitive family is `m^σ` on `(-1, 1)`. -/
private theorem boundedInitial_Kp_one {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L) {g E : ℝ}
    (hroot : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E)) {Kp : ℝ → LoopFam L}
    (h0 : ∀ n (a : Fin n → Fin L) (σ : Fin n → Bool), 1 ≤ n →
      Kp 0 n a σ = loopTr (dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ)) a σ)
    (hK : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, IsPrimDeriv (gammaG g) W L Kp u) {u : ℝ}
    (hu : u ∈ Set.Ioo (-1 : ℝ) 1) (w : Fin 1 → Fin L) (τ : Fin 1 → Bool) :
    Kp u 1 w τ = sgnScalar (mRoot g L E) (τ 0) := by
  have hd : ∀ r ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (fun r => Kp r 1 w τ) 0 r := by
    intro r hr
    have h := (hK r hr) 1 w τ
    have : cutSumFam (Kp r) w τ = 0 := by simp [cutSumFam]
    rw [this, mul_zero] at h
    exact h
  have hc := IsOpen.is_const_of_deriv_eq_zero (f := fun r => Kp r 1 w τ) isOpen_Ioo
    isPreconnected_Ioo (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hu (⟨by norm_num, by norm_num⟩ : (0 : ℝ) ∈ Set.Ioo (-1) 1)
  rw [hc, h0 1 w τ le_rfl, boundedInitial_fin_one w, boundedInitial_fin_one τ,
    loopTr_one_dysonMat g E W L hW hL _ hroot]
  simp [sgnScalar]

/-- `D_n(b, τ) = ℒ_n(b, τ) - 𝒦_n(b, τ)` along the slice. -/
private def bYn (g E : ℝ) (W L : ℕ) (Kp : ℝ → LoopFam L) (n : ℕ)
    (i : (Fin n → Fin L) × (Fin n → Bool)) (r : ℝ) (y : Ω W L) : ℂ :=
  loopTr (resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)
    (zChar g E (mRoot g L E) r)) i.1 i.2 - Kp r n i.1 i.2

private theorem bYn_heat {g E : ℝ} {W L : ℕ} (hm : 0 < (mRoot g L E).im) {Kp : ℝ → LoopFam L}
    (hK : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, IsPrimDeriv (gammaG g) W L Kp u) (n : ℕ)
    (i : (Fin n → Fin L) × (Fin n → Bool)) :
    HeatClass (bYn g E W L Kp n i) (-1 / 2) (3 / 4) := by
  have h := heatClass_loopTr W L n (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
    (boundedInitial_Ag_isHermitian g W L) g E (mRoot g L E) hm i.1 i.2 (a' := -1 / 2)
    (b' := 3 / 4) (by norm_num)
  exact boundedInitial_heat_sub_time h (f := fun r => Kp r n i.1 i.2)
    (f' := fun r => ((gammaG g * W : ℝ) : ℂ) * cutSumFam (Kp r) i.1 i.2)
    (fun r hr => (hK r ⟨by linarith [hr.1], by linarith [hr.2]⟩) n i.1 i.2)
    (boundedInitial_cutSum_cont hK i.1 i.2)

private theorem bYn_zero {g E : ℝ} {W L : ℕ} {Kp : ℝ → LoopFam L}
    (h0 : ∀ n (a : Fin n → Fin L) (σ : Fin n → Bool), 1 ≤ n →
      Kp 0 n a σ = loopTr (dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ)) a σ) {n : ℕ} (hn : 1 ≤ n)
    (i : (Fin n → Fin L) × (Fin n → Bool)) : bYn g E W L Kp n i 0 0 = 0 := by
  unfold bYn
  rw [boundedInitial_resolvent_zero, h0 n i.1 i.2 hn, sub_self]

private theorem bYn_gen {g E : ℝ} {W L : ℕ} (hm : 0 < (mRoot g L E).im) {Kp : ℝ → LoopFam L}
    {u : ℝ} (hKu : IsPrimDeriv (gammaG g) W L Kp u) (hu : u < 1) (n : ℕ)
    (i : (Fin n → Fin L) × (Fin n → Bool)) (y : Ω W L) :
    coordGen (gammaG g / W) (bYn g E W L Kp n i) u y =
      lightW g E (mRoot g L E) i.1 i.2 u
          (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) +
        ((gammaG g * W : ℝ) : ℂ) * cutErrSum (Kp u)
          (fun q b τ => bYn g E W L Kp q (b, τ) u y) i.1 i.2 := by
  have h := (blockGen_slice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (gammaG g)
    (fun r N => resLoop g E (mRoot g L E) i.1 i.2 r N - Kp r n i.1 i.2) u y).symm
  refine h.trans ?_
  rw [blockGen_errorLoop g E _ hm hu (boundedInitial_slice_isHermitian g W L y) Kp hKu]
  rfl

private theorem bYn_gamma {C B c' : ℝ} (hc' : 0 < c') {W L : ℕ} (hW : 1 ≤ W) {g E : ℝ}
    (hreg : RegBdd C B c' L g E) {Kp : ℝ → LoopFam L} {u : ℝ} (hu : u ≤ 1 / 2) {n : ℕ}
    (hn : 1 ≤ n) (i : (Fin n → Fin L) × (Fin n → Bool)) (y : Ω W L) :
    ‖coordGamma (gammaG g / W) (bYn g E W L Kp n i u) (bYn g E W L Kp n i u) y‖ ≤
      (n : ℝ) ^ 2 * biG C c' ^ (2 * n + 2) * biS C c' * ((W : ℝ)⁻¹) ^ (2 * n) := by
  have h := (blockGamma_slice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (gammaG g)
    (fun N => resLoop g E (mRoot g L E) i.1 i.2 u N - Kp u n i.1 i.2)
    (fun N => resLoop g E (mRoot g L E) i.1 i.2 u N - Kp u n i.1 i.2) y).symm
  have e : coordGamma (gammaG g / W) (bYn g E W L Kp n i u) (bYn g E W L Kp n i u) y =
      blockGamma W L (gammaG g) (resLoop g E (mRoot g L E) i.1 i.2 u)
        (resLoop g E (mRoot g L E) i.1 i.2 u)
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) :=
    h.trans (boundedInitial_blockGamma_sub_const _ _ _ _)
  rw [e]
  exact boundedInitial_slice_gamma hc' hW hreg hu y hn i.1 i.2

/-! ### Legs of the cut words -/

private theorem boundedInitial_leg_cutL {L k : ℕ} (a : Fin k → Fin L) (i j : Fin k) (hij : i < j)
    (c : Fin L) {μ : ℝ} (hμ : 0 ≤ μ) :
    Real.exp (-(μ * loopLen (cutLLab a i j c))) ≤ Real.exp (-(μ * cycDist c (a j))) := by
  have hj := j.isLt
  have hij' : i.val < j.val := hij
  have hp : i.val < k + i - j + 1 := by omega
  refine (boundedInitial_exp_leg (cutLLab a i j c) ⟨i.val, hp⟩ hμ).trans (le_of_eq ?_)
  have h1 : cutLLab a i j c ⟨i.val, hp⟩ = c := by simp [cutLLab]
  have hrot : finRotate (k + i - j + 1) ⟨i.val, hp⟩ = ⟨i.val + 1, by omega⟩ := by
    apply Fin.ext
    have e : k + i - j + 1 = (k + i - j) + 1 := rfl
    have hne : (⟨i.val, hp⟩ : Fin (k + i - j + 1)) ≠ Fin.last (k + i - j) := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    rw [coe_finRotate_of_ne_last hne]
  have h2 : cutLLab a i j c ⟨i.val + 1, by omega⟩ = a j := by
    have hlt : ¬ (i.val + 1 < i.val) := by omega
    have hne : ¬ (i.val + 1 = i.val) := by omega
    simp only [cutLLab, hlt, hne, ↓reduceDIte, ↓reduceIte]
    congr 1; apply Fin.ext; simp; omega
  rw [h1, hrot, h2]

private theorem boundedInitial_leg_cutR {L k : ℕ} (a : Fin k → Fin L) (i j : Fin k) (hij : i < j)
    (c : Fin L) {μ : ℝ} (hμ : 0 ≤ μ) :
    Real.exp (-(μ * loopLen (cutRLab a i j c))) ≤ Real.exp (-(μ * cycDist c (a i))) := by
  have hij' : i.val < j.val := hij
  have hp : j.val - i.val < j - i + 1 := by omega
  refine (boundedInitial_exp_leg (cutRLab a i j c) ⟨j.val - i.val, hp⟩ hμ).trans (le_of_eq ?_)
  have h1 : cutRLab a i j c ⟨j.val - i.val, hp⟩ = c := by simp [cutRLab]
  have hrot : finRotate (j - i + 1) ⟨j.val - i.val, hp⟩ = ⟨0, by omega⟩ := by
    have : (⟨j.val - i.val, hp⟩ : Fin (j - i + 1)) = Fin.last (j - i) := Fin.ext rfl
    rw [this, finRotate_last]; rfl
  have h2 : cutRLab a i j c ⟨0, by omega⟩ = a i := by
    have hlt : (0 : ℕ) < j.val - i.val := by omega
    simp only [cutRLab, hlt, ↓reduceDIte, add_zero]
  rw [h1, hrot, h2]

/-- The cut terms of (5.17) [fo:eq:error-hierarchy], written `ℒ_L D_R + D_L 𝒦_R` and bounded
termwise at a slice point. -/
private theorem boundedInitial_cut_le {C B c' : ℝ} (hc' : 0 < c') {W L : ℕ} (hW : 1 ≤ W) {g E : ℝ}
    (hreg : RegBdd C B c' L g E) {u : ℝ} (hu : u ≤ 1 / 2) (y : Ω W L) {Kp : ℝ → LoopFam L}
    {n : ℕ} {CKm lK : ℝ} (hlK : 0 ≤ lK)
    (hKb : ∀ q, 2 ≤ q → q ≤ n → ∀ (w : Fin q → Fin L) (τ : Fin q → Bool),
      ‖Kp u q w τ‖ ≤ CKm * (W * ((W : ℝ)⁻¹) ^ q) * Real.exp (-(lK * loopLen w)))
    (a : Fin n → Fin L) (σ : Fin n → Bool) :
    ‖((gammaG g * W : ℝ) : ℂ) * cutErrSum (Kp u) (fun q b τ => bYn g E W L Kp q (b, τ) u y) a σ‖ ≤
      ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin L, if i < j then
        (W * (W * ((W : ℝ)⁻¹) ^ (n + (i : ℕ) - j + 1) * biG C c' ^ n *
          Real.exp (-(biMu C c' * cycDist c (a j))))) *
            ‖bYn g E W L Kp ((j : ℕ) - i + 1) (cutRLab a i j c, cutRSgn σ i j) u y‖ +
        (W * (CKm * (W * ((W : ℝ)⁻¹) ^ ((j : ℕ) - i + 1)) * Real.exp (-(lK * cycDist c (a i))))) *
            ‖bYn g E W L Kp (n + (i : ℕ) - j + 1) (cutLLab a i j c, cutLSgn σ i j) u y‖
      else 0 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγ0 := gammaG_pos g
  have hγ1 := gammaG_le_one g
  have hg1 := one_le_biG C c'
  have hμ0 := (biMu_pos (C := C) hc').le
  unfold cutErrSum
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hij : i < j
  · simp only [hij, ↓reduceIte]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have hj := j.isLt
    have hij' : i.val < j.val := hij
    set DL := bYn g E W L Kp (n + (i : ℕ) - j + 1) (cutLLab a i j c, cutLSgn σ i j) u y
    set DR := bYn g E W L Kp ((j : ℕ) - i + 1) (cutRLab a i j c, cutRSgn σ i j) u y
    set KL := Kp u (n + (i : ℕ) - j + 1) (cutLLab a i j c) (cutLSgn σ i j)
    set KR := Kp u ((j : ℕ) - i + 1) (cutRLab a i j c) (cutRSgn σ i j)
    set LL := loopTr (resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)
      (zChar g E (mRoot g L E) u)) (cutLLab a i j c) (cutLSgn σ i j)
    have hLL : KL + DL = LL := by simp only [DL, KL, LL, bYn]; ring
    have e : KL * DR + DL * KR + DL * DR = LL * DR + DL * KR := by rw [← hLL]; ring
    rw [e]
    have hl := boundedInitial_slice_loop hc' hW hreg hu y (q := n + i - j + 1) (by omega)
      (cutLLab a i j c) (cutLSgn σ i j)
    have hlegL := boundedInitial_leg_cutL a i j hij c hμ0
    have hlegR := boundedInitial_leg_cutR a i j hij c hlK
    have hk := hKb ((j : ℕ) - i + 1) (by omega) (by omega) (cutRLab a i j c) (cutRSgn σ i j)
    have hgp : biG C c' ^ (n + (i : ℕ) - j + 1) ≤ biG C c' ^ n := pow_le_pow_right₀ hg1 (by omega)
    have hLLb : ‖LL‖ ≤ W * ((W : ℝ)⁻¹) ^ (n + (i : ℕ) - j + 1) * biG C c' ^ n *
        Real.exp (-(biMu C c' * cycDist c (a j))) := by
      refine hl.trans ?_
      calc (W : ℝ) * ((W : ℝ)⁻¹) ^ (n + (i : ℕ) - j + 1) * (biG C c' ^ (n + (i : ℕ) - j + 1) *
            Real.exp (-(biMu C c' * loopLen (cutLLab a i j c)))) ≤
          (W : ℝ) * ((W : ℝ)⁻¹) ^ (n + (i : ℕ) - j + 1) * (biG C c' ^ n *
            Real.exp (-(biMu C c' * cycDist c (a j)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hgp hlegL (Real.exp_pos _).le (by positivity))
              (by positivity)
        _ = _ := by ring
    have hKRb : ‖KR‖ ≤ CKm * (W * ((W : ℝ)⁻¹) ^ ((j : ℕ) - i + 1)) *
        Real.exp (-(lK * cycDist c (a i))) := by
      refine hk.trans ?_
      have hCK : 0 ≤ CKm * (W * ((W : ℝ)⁻¹) ^ ((j : ℕ) - i + 1)) := by
        have : 0 ≤ CKm := by
          by_contra hneg
          push Not at hneg
          have h1 : CKm * (W * ((W : ℝ)⁻¹) ^ ((j : ℕ) - i + 1)) * Real.exp (-(lK * loopLen (cutRLab a i j c))) < 0 :=
            mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg (by positivity)) (Real.exp_pos _)
          linarith [norm_nonneg KR]
        positivity
      exact mul_le_mul_of_nonneg_left hlegR hCK
    calc gammaG g * W * ‖LL * DR + DL * KR‖ ≤ W * (‖LL‖ * ‖DR‖ + ‖DL‖ * ‖KR‖) := by
          have : ‖LL * DR + DL * KR‖ ≤ ‖LL‖ * ‖DR‖ + ‖DL‖ * ‖KR‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
          calc gammaG g * W * ‖LL * DR + DL * KR‖ ≤ 1 * W * ‖LL * DR + DL * KR‖ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hγ1 hW0.le) (norm_nonneg _)
            _ ≤ W * (‖LL‖ * ‖DR‖ + ‖DL‖ * ‖KR‖) := by
                rw [one_mul]; exact mul_le_mul_of_nonneg_left this hW0.le
      _ ≤ W * ((W * ((W : ℝ)⁻¹) ^ (n + (i : ℕ) - j + 1) * biG C c' ^ n *
            Real.exp (-(biMu C c' * cycDist c (a j)))) * ‖DR‖ +
          ‖DL‖ * (CKm * (W * ((W : ℝ)⁻¹) ^ ((j : ℕ) - i + 1)) *
            Real.exp (-(lK * cycDist c (a i))))) := by
          gcongr
      _ = _ := by ring
  · simp [hij]

/-- `Σ_b e^{-l‖a-b‖_L} ≤ 2/(1 - e^{-l})`, the constant `S_l`. -/
private def biSl (l : ℝ) : ℝ := 2 / (1 - Real.exp (-l))

private theorem biSl_pos {l : ℝ} (hl : 0 < l) : 0 < biSl l := by
  unfold biSl
  have : Real.exp (-l) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have : 0 < 1 - Real.exp (-l) := by linarith
  positivity

/-- The linear rate `T_n = n²(g₀^n S + C_K S_λ)` of the `n`-th error equation. -/
private def bTn (C c' : ℝ) (n : ℕ) (CKm lK : ℝ) : ℝ :=
  (n : ℝ) ^ 2 * (biG C c' ^ n * biS C c' + CKm * biSl lK)

/-- The constant `R_n` produced from the lower constant at level `n`. -/
private def bRn (C c' : ℝ) (p n : ℕ) (CKm lK Rlow : ℝ) : ℝ :=
  bootC (bTn C c' n CKm lK) p * ((n : ℝ) * biG C c' ^ (n + 1) * Real.sqrt (biS C c') +
    (bTn C c' n CKm lK * Rlow + (n : ℝ) * biG C c' ^ (n + 1) * bR1 C c' p * biS C c'))

private theorem boundedInitial_W_pow {W : ℕ} (hW : 1 ≤ W) {n a b : ℕ} (hab : a + b = n + 2) :
    (W : ℝ) * (W * ((W : ℝ)⁻¹) ^ a) * ((W : ℝ)⁻¹) ^ b = ((W : ℝ)⁻¹) ^ n := by
  have hW0' : (0 : ℝ) < W := by exact_mod_cast hW
  have hW0 : (W : ℝ) ≠ 0 := hW0'.ne'
  have h1 : (W : ℝ) * (W : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hW0
  calc (W : ℝ) * (W * ((W : ℝ)⁻¹) ^ a) * ((W : ℝ)⁻¹) ^ b =
      (W * (W : ℝ)⁻¹) * (W * (W : ℝ)⁻¹) * ((W : ℝ)⁻¹) ^ n := by
        rw [mul_assoc, mul_assoc, ← pow_add, hab, pow_add]; ring
    _ = ((W : ℝ)⁻¹) ^ n := by rw [h1]; ring

/-- The `n`-th step of the induction: moments of `D_n` from those of `D_1` and `D_q`, `q < n`,
through the error equation (5.17) [fo:eq:error-hierarchy] and the moment comparison. -/
private theorem bYn_step {C B c' : ℝ} (hc' : 0 < c') {p : ℕ} (hp : 1 ≤ p) {W L : ℕ} (hW : 1 ≤ W)
    (hL : 1 ≤ L) {g E : ℝ} (hreg : RegBdd C B c' L g E) {Kp : ℝ → LoopFam L}
    (h0 : ∀ n (a : Fin n → Fin L) (σ : Fin n → Bool), 1 ≤ n →
      Kp 0 n a σ = loopTr (dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ)) a σ)
    (hK : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, IsPrimDeriv (gammaG g) W L Kp u) {n : ℕ} (hn : 2 ≤ n)
    {CKm lK : ℝ} (hCK : 0 ≤ CKm) (hlK : 0 < lK)
    (hKb : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ q, 2 ≤ q → q ≤ n → ∀ (w : Fin q → Fin L)
      (τ : Fin q → Bool), ‖Kp u q w τ‖ ≤ CKm * (W * ((W : ℝ)⁻¹) ^ q) * Real.exp (-(lK * loopLen w)))
    {Rlow : ℝ} (hRlow : 0 ≤ Rlow)
    (hIH : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ q, 2 ≤ q → q < n → ∀ i,
      bMom (gammaG g / W) p (bYn g E W L Kp q i) u ≤ Rlow * ((W : ℝ)⁻¹) ^ q) :
    ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ i, bMom (gammaG g / W) p (bYn g E W L Kp n i) u ≤
      bRn C c' p n CKm lK Rlow * ((W : ℝ)⁻¹) ^ n := by
  have hm : 0 < (mRoot g L E).im := hreg.2.2.2.1.1
  have hσ : 0 ≤ gammaG g / W := div_nonneg (gammaG_pos g).le (Nat.cast_nonneg W)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hS := biS_pos (C := C) hc'
  have hSl := biSl_pos hlK
  have hg0 := (biG_pos C c').le
  have hR1 := bR1_nonneg C c' p
  set ω : ℝ := (W : ℝ)⁻¹ with hω
  have hω0 : 0 ≤ ω := by positivity
  have hWω : (W : ℝ) * ω = 1 := mul_inv_cancel₀ hW0.ne'
  have hTn : 0 ≤ bTn C c' n CKm lK := by unfold bTn; positivity
  have hb := boundedInitial_boot (gammaG g / W) hσ p hp (bYn g E W L Kp n)
    (by norm_num : (-1 / 2 : ℝ) < 0) (by norm_num : (1 / 2 : ℝ) < 3 / 4) (bYn_heat hm hK n)
    (bYn_zero h0 (by omega)) (T := bTn C c' n CKm lK)
    (β := ω ^ n * (bTn C c' n CKm lK * Rlow + (n : ℝ) * biG C c' ^ (n + 1) * bR1 C c' p * biS C c'))
    (B := (n : ℝ) ^ 2 * biG C c' ^ (2 * n + 2) * biS C c' * ω ^ (2 * n)) hTn (by positivity)
    (by positivity) ?_ ?_
  · intro u hu i
    refine (hb u hu i).trans (le_of_eq ?_)
    have hsq : Real.sqrt ((n : ℝ) ^ 2 * biG C c' ^ (2 * n + 2) * biS C c' * ω ^ (2 * n)) =
        (n : ℝ) * biG C c' ^ (n + 1) * Real.sqrt (biS C c') * ω ^ n := by
      rw [show (n : ℝ) ^ 2 * biG C c' ^ (2 * n + 2) * biS C c' * ω ^ (2 * n) =
          ((n : ℝ) * biG C c' ^ (n + 1) * ω ^ n) ^ 2 * biS C c' by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      ring
    rw [hsq, bRn]; ring
  · intro u hu S hS0 hSb i
    have hu2 : u ≤ 1 / 2 := hu.2.le
    have hu1 : u < 1 := by linarith [hu.2]
    have huI : u ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨hu.1.le, hu2⟩
    have hur : u ∈ Set.Ioo (-1 / 2 : ℝ) (3 / 4) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    set a := i.1
    set σ := i.2
    set Rh : ℝ := (W : ℝ) ^ n * S + Rlow with hRh
    have hRh0 : 0 ≤ Rh := by positivity
    -- moments of all errors of length `2 ≤ q ≤ n`
    have hqb : ∀ q, 2 ≤ q → q ≤ n → ∀ w, bMom (gammaG g / W) p (bYn g E W L Kp q w) u ≤
        ω ^ q * Rh := by
      intro q hq2 hqn w
      rcases lt_or_eq_of_le hqn with hlt | heq
      · refine (hIH u huI q hq2 hlt w).trans ?_
        rw [mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : 0 ≤ (W : ℝ) ^ n * S := by positivity
        linarith
      · subst heq
        refine (hSb w).trans ?_
        have : ω ^ q * ((W : ℝ) ^ q * S) = S := by
          rw [← mul_assoc, ← mul_pow, mul_comm ω, hWω, one_pow, one_mul]
        have h2 : ω ^ q * ((W : ℝ) ^ q * S) ≤ ω ^ q * Rh :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
    -- the index set of the terms
    let f : (Fin n × Fin L) ⊕ ((Fin n × Fin n × Fin L) ⊕ (Fin n × Fin n × Fin L)) → Ω W L → ℂ := fun j => match j with
      | Sum.inl (i', c) => bY1 g E W L (![c], ![σ i']) u
      | Sum.inr (Sum.inl (i', j', c)) =>
          bYn g E W L Kp ((j' : ℕ) - i' + 1) (cutRLab a i' j' c, cutRSgn σ i' j') u
      | Sum.inr (Sum.inr (i', j', c)) =>
          bYn g E W L Kp (n + (i' : ℕ) - j' + 1) (cutLLab a i' j' c, cutLSgn σ i' j') u
    let cf : (Fin n × Fin L) ⊕ ((Fin n × Fin n × Fin L) ⊕ (Fin n × Fin n × Fin L)) → ℝ := fun j => match j with
      | Sum.inl (i', c) => W * ω ^ n * biG C c' ^ (n + 1) *
          Real.exp (-(biMu C c' * cycDist c (a i')))
      | Sum.inr (Sum.inl (i', j', c)) => if i' < j' then
          W * (W * ω ^ (n + (i' : ℕ) - j' + 1) * biG C c' ^ n *
            Real.exp (-(biMu C c' * cycDist c (a j')))) else 0
      | Sum.inr (Sum.inr (i', j', c)) => if i' < j' then
          W * (CKm * (W * ω ^ ((j' : ℕ) - i' + 1)) * Real.exp (-(lK * cycDist c (a i')))) else 0
    let Mf : (Fin n × Fin L) ⊕ ((Fin n × Fin n × Fin L) ⊕ (Fin n × Fin n × Fin L)) → ℝ := fun j => match j with
      | Sum.inl _ => bR1 C c' p * ω
      | Sum.inr (Sum.inl (i', j', _)) => ω ^ ((j' : ℕ) - i' + 1) * Rh
      | Sum.inr (Sum.inr (i', j', _)) => ω ^ (n + (i' : ℕ) - j' + 1) * Rh
    have hcf0 : ∀ j, 0 ≤ cf j := by
      intro j
      rcases j with ⟨i', c⟩ | ⟨i', j', c⟩ | ⟨i', j', c⟩
      · simp only [cf]; positivity
      · simp only [cf]; split_ifs <;> positivity
      · simp only [cf]; split_ifs <;> positivity
    have hMf0 : ∀ j, 0 ≤ Mf j := by
      intro j
      rcases j with ⟨i', c⟩ | ⟨i', j', c⟩ | ⟨i', j', c⟩ <;> simp only [Mf] <;> positivity
    have hfi : ∀ j, Integrable (fun x => ‖f j (Real.sqrt (u * (gammaG g / W)) • x)‖ ^ (2 * p))
        (stdGauss (Fin L × Fin W × Fin W)) := by
      intro j
      rcases j with ⟨i', c⟩ | ⟨i', j', c⟩ | ⟨i', j', c⟩
      · exact boundedInitial_heat_integrable (bY1_heat hm _) hur _ _
      · exact boundedInitial_heat_integrable (bYn_heat hm hK _ _) hur _ _
      · exact boundedInitial_heat_integrable (bYn_heat hm hK _ _) hur _ _
    have hfM : ∀ j, cf j ≠ 0 →
        (∫ x, ‖f j (Real.sqrt (u * (gammaG g / W)) • x)‖ ^ (2 * p)
          ∂(stdGauss (Fin L × Fin W × Fin W))) ≤ Mf j ^ (2 * p) := by
      intro j hj
      rcases j with ⟨i', c⟩ | ⟨i', j', c⟩ | ⟨i', j', c⟩
      · exact boundedInitial_int_le_of_bMom _ hp _ _ (bY1_mom hc' hp hW hL hreg u huI _)
      · have hij : i' < j' := by
          by_contra h; apply hj; simp only [cf, h, ↓reduceIte]
        have hij' : (i' : ℕ) < j' := hij
        exact boundedInitial_int_le_of_bMom _ hp _ _ (hqb _ (by omega) (by omega) _)
      · have hij : i' < j' := by
          by_contra h; apply hj; simp only [cf, h, ↓reduceIte]
        have hij' : (i' : ℕ) < j' := hij
        have hj' := j'.isLt
        exact boundedInitial_int_le_of_bMom _ hp _ _ (hqb _ (by omega) (by omega) _)
    have hF : ∀ y, ‖coordGen (gammaG g / W) (bYn g E W L Kp n i) u y‖ ≤
        ∑ j, cf j * ‖f j y‖ := by
      intro y
      rw [bYn_gen hm (hK u ⟨by linarith [hu.1], hu1⟩) hu1 n i y]
      refine (norm_add_le _ _).trans ?_
      have hl := boundedInitial_light_le hc' hW hreg hu2 y a σ
      have hc := boundedInitial_cut_le hc' hW hreg hu2 y hlK.le (hKb u huI) a σ
      refine (add_le_add hl hc).trans (le_of_eq ?_)
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, cf, f]
      rw [hω]
      congr 1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> ring
    have hms := boundedInitial_mom_sum (gammaG g / W) hp (coordGen (gammaG g / W) (bYn g E W L Kp n i))
      u f cf Mf hcf0 hMf0
      (fun j _ => hfi j) hfM hF
    refine hms.trans ?_
    -- the sum of the weights
    have hsμ : ∀ x : Fin L, ∑ c : Fin L, Real.exp (-(biMu C c' * cycDist c x)) ≤ biS C c' := by
      intro x
      have := biS_sum (C := C) hc' x
      simpa only [boundedInitial_cycDist_comm _ x] using this
    have hsl : ∀ x : Fin L, ∑ c : Fin L, Real.exp (-(lK * cycDist c x)) ≤ biSl lK := by
      intro x
      have := boundedInitial_sum_exp x hlK
      rw [biSl]
      simpa only [boundedInitial_cycDist_comm _ x] using this
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, cf, Mf]
    have p1 : ∑ i' : Fin n, ∑ c : Fin L, W * ω ^ n * biG C c' ^ (n + 1) *
        Real.exp (-(biMu C c' * cycDist c (a i'))) * (bR1 C c' p * ω) ≤
        ω ^ n * ((n : ℝ) * biG C c' ^ (n + 1) * bR1 C c' p * biS C c') := by
      have e : ∀ (i' : Fin n) (c : Fin L), W * ω ^ n * biG C c' ^ (n + 1) *
          Real.exp (-(biMu C c' * cycDist c (a i'))) * (bR1 C c' p * ω) =
          ω ^ n * biG C c' ^ (n + 1) * bR1 C c' p * Real.exp (-(biMu C c' * cycDist c (a i'))) := by
        intro i' c
        calc W * ω ^ n * biG C c' ^ (n + 1) * Real.exp (-(biMu C c' * cycDist c (a i'))) *
            (bR1 C c' p * ω) = (W * ω) * (ω ^ n * biG C c' ^ (n + 1) * bR1 C c' p *
              Real.exp (-(biMu C c' * cycDist c (a i')))) := by ring
          _ = _ := by rw [hWω, one_mul]
      rw [Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun c _ => e i' c]
      calc ∑ i' : Fin n, ∑ c : Fin L, ω ^ n * biG C c' ^ (n + 1) * bR1 C c' p *
          Real.exp (-(biMu C c' * cycDist c (a i'))) =
          ω ^ n * biG C c' ^ (n + 1) * bR1 C c' p *
            ∑ i' : Fin n, ∑ c : Fin L, Real.exp (-(biMu C c' * cycDist c (a i'))) := by
            simp only [Finset.mul_sum]
        _ ≤ ω ^ n * biG C c' ^ (n + 1) * bR1 C c' p * ∑ _i' : Fin n, biS C c' :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i' _ => hsμ _) (by positivity)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have p2 : ∑ i' : Fin n, ∑ j' : Fin n, ∑ c : Fin L, (if i' < j' then
        W * (W * ω ^ (n + (i' : ℕ) - j' + 1) * biG C c' ^ n *
          Real.exp (-(biMu C c' * cycDist c (a j')))) else 0) * (ω ^ ((j' : ℕ) - i' + 1) * Rh) ≤
        ω ^ n * ((n : ℝ) ^ 2 * (biG C c' ^ n * biS C c') * Rh) := by
      have e : ∀ (i' j' : Fin n) (c : Fin L), (if i' < j' then
          W * (W * ω ^ (n + (i' : ℕ) - j' + 1) * biG C c' ^ n *
            Real.exp (-(biMu C c' * cycDist c (a j')))) else 0) * (ω ^ ((j' : ℕ) - i' + 1) * Rh) ≤
          ω ^ n * biG C c' ^ n * Rh * Real.exp (-(biMu C c' * cycDist c (a j'))) := by
        intro i' j' c
        split_ifs with h
        · have h' : (i' : ℕ) < j' := h
          have hj := j'.isLt
          have hpow := boundedInitial_W_pow hW (n := n) (a := n + (i' : ℕ) - j' + 1)
            (b := (j' : ℕ) - i' + 1) (by omega)
          refine le_of_eq ?_
          calc W * (W * ω ^ (n + (i' : ℕ) - j' + 1) * biG C c' ^ n *
              Real.exp (-(biMu C c' * cycDist c (a j')))) * (ω ^ ((j' : ℕ) - i' + 1) * Rh) =
              ((W : ℝ) * (W * ((W : ℝ)⁻¹) ^ (n + (i' : ℕ) - j' + 1)) *
                ((W : ℝ)⁻¹) ^ ((j' : ℕ) - i' + 1)) *
              (biG C c' ^ n * Rh * Real.exp (-(biMu C c' * cycDist c (a j')))) := by
                rw [hω]; ring
            _ = _ := by rw [hpow, hω]; ring
        · rw [zero_mul]; positivity
      calc _ ≤ ∑ i' : Fin n, ∑ j' : Fin n, ∑ c : Fin L,
          ω ^ n * biG C c' ^ n * Rh * Real.exp (-(biMu C c' * cycDist c (a j'))) :=
            Finset.sum_le_sum fun i' _ => Finset.sum_le_sum fun j' _ =>
              Finset.sum_le_sum fun c _ => e i' j' c
        _ ≤ ∑ _i' : Fin n, ∑ _j' : Fin n, ω ^ n * biG C c' ^ n * Rh * biS C c' := by
            refine Finset.sum_le_sum fun i' _ => Finset.sum_le_sum fun j' _ => ?_
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left (hsμ _) (by positivity)
        _ = _ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have p3 : ∑ i' : Fin n, ∑ j' : Fin n, ∑ c : Fin L, (if i' < j' then
        W * (CKm * (W * ω ^ ((j' : ℕ) - i' + 1)) * Real.exp (-(lK * cycDist c (a i')))) else 0) *
          (ω ^ (n + (i' : ℕ) - j' + 1) * Rh) ≤
        ω ^ n * ((n : ℝ) ^ 2 * (CKm * biSl lK) * Rh) := by
      have e : ∀ (i' j' : Fin n) (c : Fin L), (if i' < j' then
          W * (CKm * (W * ω ^ ((j' : ℕ) - i' + 1)) * Real.exp (-(lK * cycDist c (a i')))) else 0) *
            (ω ^ (n + (i' : ℕ) - j' + 1) * Rh) ≤
          ω ^ n * CKm * Rh * Real.exp (-(lK * cycDist c (a i'))) := by
        intro i' j' c
        split_ifs with h
        · have h' : (i' : ℕ) < j' := h
          have hj := j'.isLt
          have hpow := boundedInitial_W_pow hW (n := n) (a := (j' : ℕ) - i' + 1)
            (b := n + (i' : ℕ) - j' + 1) (by omega)
          refine le_of_eq ?_
          calc W * (CKm * (W * ω ^ ((j' : ℕ) - i' + 1)) * Real.exp (-(lK * cycDist c (a i')))) *
              (ω ^ (n + (i' : ℕ) - j' + 1) * Rh) =
              ((W : ℝ) * (W * ((W : ℝ)⁻¹) ^ ((j' : ℕ) - i' + 1)) *
                ((W : ℝ)⁻¹) ^ (n + (i' : ℕ) - j' + 1)) *
              (CKm * Rh * Real.exp (-(lK * cycDist c (a i')))) := by
                rw [hω]; ring
            _ = _ := by rw [hpow, hω]; ring
        · rw [zero_mul]; positivity
      calc _ ≤ ∑ i' : Fin n, ∑ j' : Fin n, ∑ c : Fin L,
          ω ^ n * CKm * Rh * Real.exp (-(lK * cycDist c (a i'))) :=
            Finset.sum_le_sum fun i' _ => Finset.sum_le_sum fun j' _ =>
              Finset.sum_le_sum fun c _ => e i' j' c
        _ ≤ ∑ _i' : Fin n, ∑ _j' : Fin n, ω ^ n * CKm * Rh * biSl lK := by
            refine Finset.sum_le_sum fun i' _ => Finset.sum_le_sum fun j' _ => ?_
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left (hsl _) (by positivity)
        _ = _ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have hfin : ω ^ n * ((n : ℝ) * biG C c' ^ (n + 1) * bR1 C c' p * biS C c') +
        (ω ^ n * ((n : ℝ) ^ 2 * (biG C c' ^ n * biS C c') * Rh) +
          ω ^ n * ((n : ℝ) ^ 2 * (CKm * biSl lK) * Rh)) =
        bTn C c' n CKm lK * S + ω ^ n * (bTn C c' n CKm lK * Rlow +
          (n : ℝ) * biG C c' ^ (n + 1) * bR1 C c' p * biS C c') := by
      have hωW : ω ^ n * (W : ℝ) ^ n = 1 := by rw [← mul_pow, mul_comm, hWω, one_pow]
      rw [hRh, bTn]
      linear_combination ((n : ℝ) ^ 2 * (biG C c' ^ n * biS C c' + CKm * biSl lK) * S) * hωW
    linarith
  · intro u hu i
    exact boundedInitial_gamma_mom hp _ _ (by positivity)
      (fun y => bYn_gamma hc' hW hreg hu.2.le (by omega) i y)

/-- The cumulative constants `R_2 + ⋯ + R_n` of the induction over the length. -/
private def bRc (C c' : ℝ) (p : ℕ) (CKm lK : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => bRc C c' p CKm lK n + bRn C c' p (n + 1) CKm lK (bRc C c' p CKm lK n)

private theorem bRn_nonneg {C c' : ℝ} (hc' : 0 < c') (p n : ℕ) {CKm lK Rlow : ℝ} (hCK : 0 ≤ CKm)
    (hlK : 0 < lK) (hR : 0 ≤ Rlow) : 0 ≤ bRn C c' p n CKm lK Rlow := by
  have := (biG_pos C c').le
  have := (biS_pos (C := C) hc').le
  have := (biSl_pos hlK).le
  have := bR1_nonneg C c' p
  have hT : 0 ≤ bTn C c' n CKm lK := by unfold bTn; positivity
  unfold bRn
  exact mul_nonneg (bootC_nonneg _ _) (by positivity)

private theorem bRc_nonneg {C c' : ℝ} (hc' : 0 < c') (p : ℕ) {CKm lK : ℝ} (hCK : 0 ≤ CKm)
    (hlK : 0 < lK) : ∀ n, 0 ≤ bRc C c' p CKm lK n
  | 0 => le_rfl
  | n + 1 => by
    have h := bRc_nonneg (C := C) hc' p hCK hlK n
    simp only [bRc]
    exact add_nonneg h (bRn_nonneg (C := C) hc' p (n + 1) hCK hlK h)

/-- Moments of all loop errors of lengths `2 ≤ q ≤ n`: `‖D_q‖_{2p} ≤ R W^{-q}`. -/
private theorem bYn_all {C B c' : ℝ} (hc' : 0 < c') {p : ℕ} (hp : 1 ≤ p) {W L : ℕ} (hW : 1 ≤ W)
    (hL : 1 ≤ L) {g E : ℝ} (hreg : RegBdd C B c' L g E) {Kp : ℝ → LoopFam L}
    (h0 : ∀ n (a : Fin n → Fin L) (σ : Fin n → Bool), 1 ≤ n →
      Kp 0 n a σ = loopTr (dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ)) a σ)
    (hK : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, IsPrimDeriv (gammaG g) W L Kp u) {k : ℕ}
    {CKm lK : ℝ} (hCK : 0 ≤ CKm) (hlK : 0 < lK)
    (hKb : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ q, 2 ≤ q → q ≤ k → ∀ (w : Fin q → Fin L)
      (τ : Fin q → Bool), ‖Kp u q w τ‖ ≤ CKm * (W * ((W : ℝ)⁻¹) ^ q) * Real.exp (-(lK * loopLen w))) :
    ∀ n, n ≤ k → ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ q, 2 ≤ q → q ≤ n → ∀ i,
      bMom (gammaG g / W) p (bYn g E W L Kp q i) u ≤ bRc C c' p CKm lK n * ((W : ℝ)⁻¹) ^ q := by
  intro n
  induction n with
  | zero => intro _ u _ q hq hq0; omega
  | succ n IH =>
    intro hn u hu q hq2 hqn i
    have hRn := bRc_nonneg (C := C) hc' p hCK hlK n
    have hω : 0 ≤ ((W : ℝ)⁻¹) ^ q := by positivity
    rcases lt_or_eq_of_le hqn with hlt | heq
    · refine (IH (by omega) u hu q hq2 (by omega) i).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hω
      simp only [bRc]
      linarith [bRn_nonneg (C := C) hc' p (n + 1) hCK hlK hRn]
    · subst heq
      have hstep := bYn_step hc' hp hW hL hreg h0 hK (n := n + 1) hq2 hCK hlK
        (fun u hu q hq2' hq' w τ => hKb u hu q hq2' (by omega) w τ) hRn
        (fun u hu q hq2' hq' i => IH (by omega) u hu q hq2' (by omega) i) u hu i
      refine hstep.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hω
      simp only [bRc]
      linarith

/-- Lemma 5.3 [fo:lem:bounded-initial] in fixed-time form, loop-error component of (5.22)
[gc:eq:one-step-input] at `s = u ∈ [0, 1/2]`, for any primitive family with the initial value,
the equation (5.10) [fo:eq:primitive], the two-loop symmetry and the bound (B.13)
[b:eq:early-primitive]. -/
theorem boundedInitial_loopError (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') (k : ℕ)
    (hk : 1 ≤ k) (CK cK : ℕ → ℝ) (hCK : ∀ n, 0 < CK n) (hcK : ∀ n, 0 < cK n) (ε D : ℝ)
    (hε : 0 < ε) (hD : 0 < D) :
    ∃ W₀ : ℕ, ∀ W L : ℕ, W₀ ≤ W → 3 ≤ L → L ≤ W ^ 2 → ∀ g E : ℝ, 0 < g → RegBdd C B c' L g E →
      ∀ Kp : ℝ → LoopFam L,
      (∀ n (a : Fin n → Fin L) (σ : Fin n → Bool), 1 ≤ n →
        Kp 0 n a σ =
          loopTr (dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⊗ₖ
            (1 : Matrix (Fin W) (Fin W) ℂ)) a σ) →
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1, IsPrimDeriv (gammaG g) W L Kp u) →
      (∀ u (x y : Fin L) (s t : Bool), Kp u 2 ![x, y] ![s, t] = Kp u 2 ![y, x] ![t, s]) →
      (∀ n, n ≤ k → ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ (a : Fin n → Fin L) (σ : Fin n → Bool),
        ‖Kp u n a σ‖ ≤ CK n * (W : ℝ) ^ (1 - (n : ℝ)) * Real.exp (-(cK n * loopLen a))) →
      ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
        μ W L {ω | ∃ (a : Fin k → Fin L) (σ : Fin k → Bool),
          (W : ℝ) ^ ε * zetaProp g W L u ^ k <
            ‖loopTr (resolventMat (flowH g W L u ω) (zChar g E (mRoot g L E) u)) a σ -
              Kp u k a σ‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  set p : ℕ := ⌈(D + 3 * k + 1) / (2 * ε)⌉₊ + 1 with hpdef
  have hp : 1 ≤ p := by omega
  have h2p : ((3 * k : ℕ) : ℝ) + 1 + D ≤ 2 * (p : ℝ) * ε := by
    have h1 := Nat.le_ceil ((D + 3 * k + 1) / (2 * ε))
    have h2 : (D + 3 * k + 1) / (2 * ε) ≤ p := by rw [hpdef]; push_cast; linarith
    rw [div_le_iff₀ (by positivity)] at h2
    push_cast
    linarith
  set CKm : ℝ := ∑ q ∈ Finset.range (k + 1), CK q with hCKm
  have hCKm0 : 0 ≤ CKm := Finset.sum_nonneg fun q _ => (hCK q).le
  have hCKle : ∀ q, q ≤ k → CK q ≤ CKm := fun q hq =>
    Finset.single_le_sum (f := CK) (fun q _ => (hCK q).le) (Finset.mem_range.mpr (by omega))
  set lK : ℝ := (Finset.range (k + 1)).inf' ⟨0, by simp⟩ cK with hlKdef
  have hlK : 0 < lK := (Finset.lt_inf'_iff _).mpr fun q _ => hcK q
  have hlKle : ∀ q, q ≤ k → lK ≤ cK q := fun q hq =>
    Finset.inf'_le _ (Finset.mem_range.mpr (by omega))
  set cz : ℝ := (1 + 2 * C * max 1 C)⁻¹ with hcz
  have hcz0 : 0 < cz := by
    have : 0 ≤ 2 * C * max 1 C := by have := le_max_left 1 C; positivity
    positivity
  set R : ℝ := bR1 C c' p + bRc C c' p CKm lK k with hR
  have hR0 : 0 ≤ R := add_nonneg (bR1_nonneg C c' p) (bRc_nonneg hc' p hCKm0 hlK k)
  set R' : ℝ := (R + 1) / cz ^ k with hR'
  have hR'0 : 0 < R' := by positivity
  set K : ℝ := R' ^ (2 * p) with hK
  refine ⟨⌈K⌉₊ + 2, fun W L hW hL hLW g E hg hreg Kp h0 hKd _ hKb u hu => ?_⟩
  have hW1 : 1 ≤ W := by omega
  have hW2 : 2 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hKW : K ≤ W := by
    have := Nat.le_ceil K
    have : ((⌈K⌉₊ + 2 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at this
    linarith
  have hL1 : 1 ≤ L := by omega
  set ω : ℝ := (W : ℝ)⁻¹ with hω
  have hω0 : 0 < ω := by positivity
  set σ2 := gammaG g / W with hσ2
  -- the bounds (B.13) [b:eq:early-primitive] in the normalized form
  have hKb' : ∀ v ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ q, 2 ≤ q → q ≤ k → ∀ (w : Fin q → Fin L)
      (τ : Fin q → Bool), ‖Kp v q w τ‖ ≤ CKm * (W * ω ^ q) * Real.exp (-(lK * loopLen w)) := by
    intro v hv q _ hqk w τ
    refine (hKb q hqk v hv w τ).trans ?_
    rw [boundedInitial_rpow_eq hW1]
    have hl : (0 : ℝ) ≤ loopLen w := Nat.cast_nonneg _
    have he : Real.exp (-(cK q * loopLen w)) ≤ Real.exp (-(lK * loopLen w)) :=
      Real.exp_le_exp.mpr (by nlinarith [hlKle q hqk])
    have : 0 < (W : ℝ) * ω ^ q := by positivity
    calc CK q * (W * ω ^ q) * Real.exp (-(cK q * loopLen w)) ≤
        CKm * (W * ω ^ q) * Real.exp (-(lK * loopLen w)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hCKle q hqk) this.le) he
            (Real.exp_pos _).le (by positivity)
      _ = _ := rfl
  -- moments of `D_k`
  have hmom : ∀ i, bMom σ2 p (bYn g E W L Kp k i) u ≤ R * ω ^ k := by
    intro i
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      have e : bMom σ2 p (bYn g E W L Kp 1 i) u = bMom σ2 p (bY1 g E W L i) u := by
        unfold bMom
        congr 1
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [bYn, bY1]
        rw [boundedInitial_Kp_one hW1 hL1 hreg.2.2.2.1 h0 hKd ⟨by linarith [hu.1], by
          linarith [hu.2]⟩ i.1 i.2]
      rw [e, pow_one]
      refine (bY1_mom hc' hp hW1 hL1 hreg u hu i).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hω0.le
      linarith [bRc_nonneg (C := C) hc' p hCKm0 hlK 1]
    · refine (bYn_all hc' hp hW1 hL1 hreg h0 hKd hCKm0 hlK hKb' k le_rfl u hu k hk2 le_rfl i).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith [bR1_nonneg C c' p]
  have hset : {ω : Ω W L | ∃ (a : Fin k → Fin L) (σ : Fin k → Bool),
      (W : ℝ) ^ ε * zetaProp g W L u ^ k <
        ‖loopTr (resolventMat (flowH g W L u ω) (zChar g E (mRoot g L E) u)) a σ - Kp u k a σ‖} =
      {ω | ∃ i : (Fin k → Fin L) × (Fin k → Bool), (W : ℝ) ^ ε * zetaProp g W L u ^ k <
        ‖bYn g E W L Kp k i u (Real.sqrt (u * σ2) • ω)‖} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Prod.exists]
    rw [boundedInitial_flowH_slice g W L hu.1 ω]
    rfl
  rw [hset]
  have hζ : cz * ω ≤ zetaProp g W L u :=
    boundedInitial_zeta_ge hreg.1 hreg.2.1 hW1 hL1 hu.1 hu.2
  have hζk : (cz * ω) ^ k ≤ zetaProp g W L u ^ k := pow_le_pow_left₀ (by positivity) hζ k
  have hWe : 0 < (W : ℝ) ^ ε := Real.rpow_pos_of_pos hW0 ε
  have ht : 0 < (W : ℝ) ^ ε * zetaProp g W L u ^ k :=
    mul_pos hWe (lt_of_lt_of_le (by positivity) hζk)
  refine (boundedInitial_markov hp σ2 u (bYn g E W L Kp k)
    (fun i => bYn_heat hreg.2.2.2.1.1 hKd k i) ⟨by linarith [hu.1], by linarith [hu.2]⟩ ht
    hmom).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hcard : (Fintype.card ((Fin k → Fin L) × (Fin k → Bool)) : ℝ) ≤ (W : ℝ) ^ (3 * k) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    push_cast
    have hLW' : (L : ℝ) ≤ (W : ℝ) ^ 2 := by exact_mod_cast hLW
    have hW2' : (2 : ℝ) ≤ W := by exact_mod_cast hW2
    calc (L : ℝ) ^ k * 2 ^ k ≤ ((W : ℝ) ^ 2) ^ k * (W : ℝ) ^ k :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hLW' k)
            (pow_le_pow_left₀ (by norm_num) hW2' k) (by positivity) (by positivity)
      _ = (W : ℝ) ^ (3 * k) := by rw [← pow_mul, ← pow_add]; ring_nf
  refine boundedInitial_final hW1 (by positivity) hcard (s := 2 * p * ε) ?_ hKW h2p
  refine boundedInitial_pow_ratio hW1 (div_nonneg (by positivity) ht.le) ?_
  rw [div_le_iff₀ ht]
  have hczk : 0 < cz ^ k := by positivity
  calc R * ω ^ k ≤ (R + 1) * ω ^ k := by nlinarith [pow_pos hω0 k]
    _ = R' * (W : ℝ) ^ (-ε) * ((W : ℝ) ^ ε * (cz * ω) ^ k) := by
        rw [hR', Real.rpow_neg hW0.le, mul_pow]
        field_simp
    _ ≤ R' * (W : ℝ) ^ (-ε) * ((W : ℝ) ^ ε * zetaProp g W L u ^ k) := by
        gcongr

/-- Lemma 5.3 [fo:lem:bounded-initial], entrywise component `‖G̃_u‖_max ≺ √ζ_u` of (5.22)
[gc:eq:one-step-input] at `s = u ∈ [0, 1/2]`. -/
theorem boundedInitial_entry (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') (ε D : ℝ)
    (hε : 0 < ε) (hD : 0 < D) :
    ∃ W₀ : ℕ, ∀ W L : ℕ, W₀ ≤ W → 3 ≤ L → L ≤ W ^ 2 → ∀ g E : ℝ, 0 < g → RegBdd C B c' L g E →
      ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
        μ W L {ω | ∃ p q : Fin L × Fin W,
          (W : ℝ) ^ ε * Real.sqrt (zetaProp g W L u) <
            ‖(resolventMat (flowH g W L u ω) (zChar g E (mRoot g L E) u) -
              dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⊗ₖ
                (1 : Matrix (Fin W) (Fin W) ℂ)) p q‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  set p : ℕ := ⌈(D + 7) / (2 * ε)⌉₊ + 1 with hpdef
  have hp : 1 ≤ p := by omega
  have h2p : 6 + 1 + D ≤ 2 * (p : ℝ) * ε := by
    have h1 := Nat.le_ceil ((D + 7) / (2 * ε))
    have h2 : (D + 7) / (2 * ε) ≤ p := by rw [hpdef]; push_cast; linarith
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  set cz : ℝ := (1 + 2 * C * max 1 C)⁻¹ with hcz
  have hcz0 : 0 < cz := by
    have : 0 ≤ 2 * C * max 1 C := by have := le_max_left 1 C; positivity
    positivity
  set R := bRe C c' p with hR
  set R' := (|R| + 1) / Real.sqrt cz with hR'
  have hR'0 : 0 < R' := by positivity
  set K := R' ^ (2 * p) with hK
  refine ⟨⌈K⌉₊ + 1, fun W L hW hL hLW g E hg hreg u hu => ?_⟩
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hKW : K ≤ W := by
    have := Nat.le_ceil K
    have : ((⌈K⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at this
    linarith
  have hL1 : 1 ≤ L := by omega
  set σ2 := gammaG g / W with hσ2
  have hset : {ω : Ω W L | ∃ p q : Fin L × Fin W, (W : ℝ) ^ ε * Real.sqrt (zetaProp g W L u) <
      ‖(resolventMat (flowH g W L u ω) (zChar g E (mRoot g L E) u) -
        dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) p q‖} =
      {ω | ∃ i : (Fin L × Fin W) × (Fin L × Fin W), (W : ℝ) ^ ε * Real.sqrt (zetaProp g W L u) <
        ‖bYe g E W L i u (Real.sqrt (u * σ2) • ω)‖} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Prod.exists]
    rw [boundedInitial_flowH_slice g W L hu.1 ω]
    rfl
  rw [hset]
  have hζ : cz * (W : ℝ)⁻¹ ≤ zetaProp g W L u :=
    boundedInitial_zeta_ge hreg.1 hreg.2.1 hW1 hL1 hu.1 hu.2
  have hω0 : 0 < (W : ℝ)⁻¹ := by positivity
  have ht : 0 < (W : ℝ) ^ ε * Real.sqrt (zetaProp g W L u) := by
    have : 0 < zetaProp g W L u := lt_of_lt_of_le (by positivity) hζ
    positivity
  have hM := bYe_mom hc' hp hW1 hL1 hreg u hu
  refine (boundedInitial_markov hp σ2 u (bYe g E W L) (fun i => bYe_heat hreg.2.2.2.1.1 i)
    ⟨by linarith [hu.1], by linarith [hu.2]⟩ ht hM).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hcard : (Fintype.card ((Fin L × Fin W) × (Fin L × Fin W)) : ℝ) ≤ (W : ℝ) ^ 6 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    have hLW' : (L : ℝ) ≤ (W : ℝ) ^ 2 := by exact_mod_cast hLW
    have : (L : ℝ) * W ≤ (W : ℝ) ^ 2 * W := mul_le_mul_of_nonneg_right hLW' hW0.le
    have h0 : (0 : ℝ) ≤ L * W := by positivity
    nlinarith [mul_le_mul this this h0 (by positivity)]
  have hRe0 : 0 ≤ bRe C c' p := by
    unfold bRe
    have := (biG_pos C c').le
    have := (biS_pos (C := C) hc').le
    have := bR1_nonneg C c' p
    exact mul_nonneg (bootC_nonneg _ _) (by positivity)
  refine boundedInitial_final hW1 (by positivity) hcard (s := 2 * p * ε) ?_ hKW
    (by push_cast; linarith)
  refine boundedInitial_pow_ratio hW1 (div_nonneg (by positivity) ht.le) ?_
  -- `R √(1/W) / (W^ε √ζ) ≤ R' W^{-ε}`
  have hsζ : Real.sqrt cz * Real.sqrt ((W : ℝ)⁻¹) ≤ Real.sqrt (zetaProp g W L u) := by
    rw [← Real.sqrt_mul hcz0.le]; exact Real.sqrt_le_sqrt hζ
  have hsω : 0 < Real.sqrt ((W : ℝ)⁻¹) := Real.sqrt_pos.mpr hω0
  have hscz : 0 < Real.sqrt cz := Real.sqrt_pos.mpr hcz0
  have hWe : 0 < (W : ℝ) ^ ε := Real.rpow_pos_of_pos hW0 ε
  rw [div_le_iff₀ ht]
  calc R * Real.sqrt ((W : ℝ)⁻¹) ≤ (|R| + 1) * Real.sqrt ((W : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self R]) hsω.le
    _ = R' * (W : ℝ) ^ (-ε) * ((W : ℝ) ^ ε * (Real.sqrt cz * Real.sqrt ((W : ℝ)⁻¹))) := by
        rw [hR', Real.rpow_neg hW0.le]
        field_simp
    _ ≤ R' * (W : ℝ) ^ (-ε) * ((W : ℝ) ^ ε * Real.sqrt (zetaProp g W L u)) := by
        gcongr

end LSBA
