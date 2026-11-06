import LSBA.Upper.CenterCenters
import LSBA.Analysis.PolyEvalBound

/-!
# The corrector and the good set

The corrector `Q_g = Re Σ_{k} q_k F_k` of (11.68) [lg:eq:Q-definition] for a coefficient vector
`q` on a finite index set, as a function of the state through the evaluation of the corrected
observables (11.50) [lg:eq:corrected-observables]; its size and Lipschitz bounds (11.28)
[lg:eq:Q-regularity], in the operator norm of `C` and the Euclidean norm of `v`; and the set of
states on which the bounds of the event (11.44) [lg:eq:burnevent] hold.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The states with `|M_k − a_k| ≤ W^{η−1}` and `|F_k| ≤ W^{η−1/2}` for every `k` in the index
set (the bounds of (11.44) [lg:eq:burnevent]). -/
def corrGood (g E : ℝ) (R : ℕ) (Ks : Finset NzInt) (η : ℝ) {W : ℕ} (X : State W) : Prop :=
  ∀ k ∈ Ks, ‖obsEval g X (corrObsM E R k) - center g E R k.1‖ ≤ (W : ℝ) ^ (η - 1) ∧
    ‖obsEval g X (corrObsF E R k)‖ ≤ (W : ℝ) ^ (η - 1 / 2)

/-- The corrector `Q_g(C, v) = Re Σ_{k ∈ Ks} q_k F_k(C, v)` of (11.68) [lg:eq:Q-definition]. -/
def corrQ (g E : ℝ) (R : ℕ) (Ks : Finset NzInt) (q : NzInt → ℂ) {W : ℕ} (X : State W) : ℝ :=
  (∑ k ∈ Ks, q k * obsEval g X (corrObsF E R k)).re

/-- A unitary matrix has an invertible determinant. -/
private theorem cq_isUnit_det {W : ℕ} {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) : IsUnit C.det :=
  Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hC)

/-- The inverse of a unitary matrix is its conjugate transpose. -/
private theorem cq_inv_eq {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ) : U⁻¹ = Uᴴ := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff.mp hU

/-- Integer powers of a unitary matrix are unitary. -/
private theorem cq_zpow_mem {W : ℕ} {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (k : ℤ) : C ^ k ∈ Matrix.unitaryGroup (Fin W) ℂ := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast]
    exact pow_mem hC n
  · rw [Matrix.zpow_neg (cq_isUnit_det hC), zpow_natCast, cq_inv_eq (pow_mem hC n),
      ← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem (pow_mem hC n)

/-- `C^{-n} = (C^n)*` for unitary `C`. -/
private theorem cq_zpow_neg_natCast {W : ℕ} {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (n : ℕ) : C ^ (-(n : ℤ)) = (C ^ n)ᴴ := by
  rw [Matrix.zpow_neg (cq_isUnit_det hC), zpow_natCast, cq_inv_eq (pow_mem hC n)]

/-- A unitary matrix has operator norm at most `1`, for `W ≥ 1`. -/
private theorem cq_norm_unitary_le {W : ℕ} (hW : 1 ≤ W) {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) : ‖C‖ ≤ 1 := by
  have : Nonempty (Fin W) := ⟨⟨0, hW⟩⟩
  exact (CStarRing.norm_of_mem_unitary hC).le

/-- `‖C^n − C'^n‖ ≤ n ‖C − C'‖` for unitary `C`, `C'`. -/
private theorem cq_pow_sub {W : ℕ} (hW : 1 ≤ W) {C C' : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hC' : C' ∈ Matrix.unitaryGroup (Fin W) ℂ)
    (n : ℕ) : ‖C ^ n - C' ^ n‖ ≤ n * ‖C - C'‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : C ^ (n + 1) - C' ^ (n + 1) = C ^ n * (C - C') + (C ^ n - C' ^ n) * C' := by
      rw [pow_succ, pow_succ]
      noncomm_ring
    have h1 : ‖C ^ n‖ ≤ 1 := cq_norm_unitary_le hW (pow_mem hC n)
    have h2 : ‖C'‖ ≤ 1 := cq_norm_unitary_le hW hC'
    calc ‖C ^ (n + 1) - C' ^ (n + 1)‖
        = ‖C ^ n * (C - C') + (C ^ n - C' ^ n) * C'‖ := by rw [e]
      _ ≤ ‖C ^ n‖ * ‖C - C'‖ + ‖C ^ n - C' ^ n‖ * ‖C'‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 1 * ‖C - C'‖ + (n * ‖C - C'‖) * 1 := by gcongr
      _ = ((n + 1 : ℕ) : ℝ) * ‖C - C'‖ := by push_cast; ring

/-- `‖C^j − C'^j‖ ≤ |j| ‖C − C'‖` for unitary `C`, `C'` and `j ∈ ℤ`. -/
private theorem cq_zpow_sub {W : ℕ} (hW : 1 ≤ W) {C C' : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hC' : C' ∈ Matrix.unitaryGroup (Fin W) ℂ)
    (j : ℤ) : ‖C ^ j - C' ^ j‖ ≤ (j.natAbs : ℝ) * ‖C - C'‖ := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · rw [zpow_natCast, zpow_natCast]
    simpa using cq_pow_sub hW hC hC' n
  · rw [cq_zpow_neg_natCast hC, cq_zpow_neg_natCast hC', ← Matrix.conjTranspose_sub,
      Matrix.l2_opNorm_conjTranspose]
    simpa using cq_pow_sub hW hC hC' n

/-- `‖M w‖ ≤ ‖M‖ ‖w‖` for the Euclidean action of a matrix. -/
private theorem cq_norm_lin_le {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ)
    (w : EuclideanSpace ℂ (Fin W)) : ‖Matrix.toEuclideanLin M w‖ ≤ ‖M‖ * ‖w‖ :=
  (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) M).le_opNorm w

/-- `‖w* M u‖ ≤ ‖M‖ ‖w‖ ‖u‖`. -/
private theorem cq_norm_inner_le {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ)
    (w u : EuclideanSpace ℂ (Fin W)) :
    ‖inner ℂ w (Matrix.toEuclideanLin M u)‖ ≤ ‖M‖ * (‖w‖ * ‖u‖) :=
  calc ‖inner ℂ w (Matrix.toEuclideanLin M u)‖ ≤ ‖w‖ * ‖Matrix.toEuclideanLin M u‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖w‖ * (‖M‖ * ‖u‖) := by gcongr; exact cq_norm_lin_le M u
    _ = ‖M‖ * (‖w‖ * ‖u‖) := by ring

/-- A diagonal entry of a matrix is bounded by its operator norm. -/
private theorem cq_norm_diag_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) (i : Fin W) :
    ‖A i i‖ ≤ ‖A‖ := by
  have h : A i i = inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (Matrix.toEuclideanLin A (EuclideanSpace.single i (1 : ℂ))) := by
    simp [Matrix.toLpLin_apply, EuclideanSpace.inner_single_left]
  rw [h]
  simpa using cq_norm_inner_le A (EuclideanSpace.single i (1 : ℂ)) (EuclideanSpace.single i 1)

/-- `|Tr A| ≤ W ‖A‖`. -/
private theorem cq_norm_trace_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    ‖A.trace‖ ≤ W * ‖A‖ :=
  calc ‖A.trace‖ = ‖∑ i, A i i‖ := rfl
    _ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin W, ‖A‖ := Finset.sum_le_sum fun i _ => cq_norm_diag_le A i
    _ = W * ‖A‖ := by simp

/-- `|m_k(X) − m_k(Y)| ≤ |k| ‖C_X − C_Y‖`. -/
private theorem cq_obsM_sub {W : ℕ} (hW : 1 ≤ W) {X Y : State W} (hX : IsState X)
    (hY : IsState Y) (k : ℤ) : ‖obsM k X - obsM k Y‖ ≤ (k.natAbs : ℝ) * ‖X.1 - Y.1‖ := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  unfold obsM
  rw [← mul_sub, ← Matrix.trace_sub, norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖(X.1 ^ k - Y.1 ^ k).trace‖
      ≤ (W : ℝ)⁻¹ * (W * ‖X.1 ^ k - Y.1 ^ k‖) := by gcongr; exact cq_norm_trace_le _
    _ = ‖X.1 ^ k - Y.1 ^ k‖ := by field_simp
    _ ≤ _ := cq_zpow_sub hW hX.1 hY.1 k

/-- `|f_k(X) − f_k(Y)| ≤ |k| ‖C_X − C_Y‖ + 2 ‖v_X − v_Y‖`. -/
private theorem cq_obsF_sub {W : ℕ} (hW : 1 ≤ W) {X Y : State W} (hX : IsState X)
    (hY : IsState Y) (k : ℤ) :
    ‖obsF k X - obsF k Y‖ ≤ (k.natAbs : ℝ) * ‖X.1 - Y.1‖ + 2 * ‖X.2 - Y.2‖ := by
  have hA : ‖X.1 ^ k‖ ≤ 1 := cq_norm_unitary_le hW (cq_zpow_mem hX.1 k)
  have hA' : ‖Y.1 ^ k‖ ≤ 1 := cq_norm_unitary_le hW (cq_zpow_mem hY.1 k)
  have e : obsF k X - obsF k Y =
      inner ℂ (X.2 - Y.2) (Matrix.toEuclideanLin (X.1 ^ k) X.2) +
        inner ℂ Y.2 (Matrix.toEuclideanLin (X.1 ^ k - Y.1 ^ k) X.2) +
        inner ℂ Y.2 (Matrix.toEuclideanLin (Y.1 ^ k) (X.2 - Y.2)) := by
    simp only [obsF, vecForm, map_sub, LinearMap.sub_apply, inner_sub_left, inner_sub_right]
    ring
  have t1 : ‖inner ℂ (X.2 - Y.2) (Matrix.toEuclideanLin (X.1 ^ k) X.2)‖ ≤ ‖X.2 - Y.2‖ := by
    refine (cq_norm_inner_le _ _ _).trans ?_
    rw [hX.2]
    nlinarith [norm_nonneg (X.2 - Y.2), norm_nonneg (X.1 ^ k)]
  have t2 : ‖inner ℂ Y.2 (Matrix.toEuclideanLin (X.1 ^ k - Y.1 ^ k) X.2)‖ ≤
      (k.natAbs : ℝ) * ‖X.1 - Y.1‖ := by
    refine (cq_norm_inner_le _ _ _).trans ?_
    rw [hX.2, hY.2, mul_one, mul_one]
    exact cq_zpow_sub hW hX.1 hY.1 k
  have t3 : ‖inner ℂ Y.2 (Matrix.toEuclideanLin (Y.1 ^ k) (X.2 - Y.2))‖ ≤ ‖X.2 - Y.2‖ := by
    refine (cq_norm_inner_le _ _ _).trans ?_
    rw [hY.2]
    nlinarith [norm_nonneg (X.2 - Y.2), norm_nonneg (Y.1 ^ k)]
  rw [e]
  calc _ ≤ ‖inner ℂ (X.2 - Y.2) (Matrix.toEuclideanLin (X.1 ^ k) X.2)‖ +
        ‖inner ℂ Y.2 (Matrix.toEuclideanLin (X.1 ^ k - Y.1 ^ k) X.2)‖ +
        ‖inner ℂ Y.2 (Matrix.toEuclideanLin (Y.1 ^ k) (X.2 - Y.2))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

/-- Every formal variable evaluates to modulus at most `1` on a state (`W ≥ 1`, `g ≥ 1`). -/
private theorem cq_var_norm {W : ℕ} (hW : 1 ≤ W) {g : ℝ} (hg : 1 ≤ g) {X : State W}
    (hX : IsState X) (u : ObsVar) : ‖obsEval g X (MvPolynomial.X u)‖ ≤ 1 := by
  simpa [MvPolynomial.support_X, MvPolynomial.coeff_X] using
    norm_obsEval_le hW hg hX (MvPolynomial.X u)

/-- The evaluation of a variable moves by at most `(2 + |idx|) (‖C_X − C_Y‖ + ‖v_X − v_Y‖)`
between two states. -/
private theorem cq_var_sub {W : ℕ} (hW : 1 ≤ W) {g : ℝ} {X Y : State W} (hX : IsState X)
    (hY : IsState Y) (u : ObsVar) :
    ‖obsEval g X (MvPolynomial.X u) - obsEval g Y (MvPolynomial.X u)‖ ≤
      (2 + (u.idx.natAbs : ℝ)) * (‖X.1 - Y.1‖ + ‖X.2 - Y.2‖) := by
  have h1 : 0 ≤ ‖X.1 - Y.1‖ := norm_nonneg _
  have h2 : 0 ≤ ‖X.2 - Y.2‖ := norm_nonneg _
  have hn : (0 : ℝ) ≤ (u.idx.natAbs : ℝ) := Nat.cast_nonneg _
  cases u with
  | m k =>
    have := cq_obsM_sub hW hX hY k.1
    simp only [obsEval, aeval_X, ObsVar.idx]
    nlinarith [mul_nonneg hn h2]
  | f k =>
    have := cq_obsF_sub hW hX hY k.1
    simp only [obsEval, aeval_X, ObsVar.idx]
    nlinarith [mul_nonneg hn h2]
  | w =>
    simp only [obsEval, aeval_X, sub_self, norm_zero, ObsVar.idx]
    positivity
  | γ =>
    simp only [obsEval, aeval_X, sub_self, norm_zero, ObsVar.idx]
    positivity

/-- Size and Lipschitz bounds for the evaluation of a polynomial supported in `S` with
coefficients of modulus at most `K₀`. -/
private theorem cq_poly_bounds {W : ℕ} (hW : 1 ≤ W) {g : ℝ} (hg : 1 ≤ g) {X Y : State W}
    (hX : IsState X) (hY : IsState Y) (p : ObsPoly) (S : Finset (ObsVar →₀ ℕ)) (K₀ : ℝ)
    (hS : p.support ⊆ S) (hK : ∀ d, ‖p.coeff d‖ ≤ K₀) (hK₀ : 0 ≤ K₀) :
    ‖obsEval g X p‖ ≤ S.card * K₀ ∧
      ‖obsEval g X p - obsEval g Y p‖ ≤
        K₀ * (∑ d ∈ S, ((Finsupp.degree d : ℕ) : ℝ)) *
          (2 + ∑ u ∈ S.biUnion Finsupp.support, (u.idx.natAbs : ℝ)) *
            (‖X.1 - Y.1‖ + ‖X.2 - Y.2‖) := by
  have hev : ∀ (Z : State W) (r : ObsPoly), obsEval g Z r =
      aeval (fun v => obsEval g Z (MvPolynomial.X v)) r := fun Z r =>
    congrArg (fun φ => φ r) (aeval_unique (obsEval g Z))
  refine ⟨?_, ?_⟩
  · calc ‖obsEval g X p‖ ≤ ∑ d ∈ p.support, ‖p.coeff d‖ := norm_obsEval_le hW hg hX p
      _ ≤ p.support.card • K₀ := Finset.sum_le_card_nsmul _ _ _ fun d _ => hK d
      _ ≤ S.card * K₀ := by
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hS) hK₀
  · set δ : ℝ := ‖X.1 - Y.1‖ + ‖X.2 - Y.2‖ with hδ
    set L : ℝ := 2 + ∑ u ∈ S.biUnion Finsupp.support, (u.idx.natAbs : ℝ) with hL
    have hδ0 : 0 ≤ δ := by positivity
    have hL0 : 0 ≤ L := by positivity
    have hvars : ∀ v ∈ p.vars, ‖obsEval g X (MvPolynomial.X v) - obsEval g Y (MvPolynomial.X v)‖ ≤
        L * δ := by
      intro v hv
      obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support v).1 hv
      have hvV : v ∈ S.biUnion Finsupp.support :=
        Finset.mem_biUnion.2 ⟨d, hS hd, hvd⟩
      have hle : (v.idx.natAbs : ℝ) ≤ ∑ u ∈ S.biUnion Finsupp.support, (u.idx.natAbs : ℝ) :=
        Finset.single_le_sum (f := fun u : ObsVar => (u.idx.natAbs : ℝ))
          (fun _ _ => Nat.cast_nonneg _) hvV
      exact (cq_var_sub hW hX hY v).trans (mul_le_mul_of_nonneg_right (by linarith) hδ0)
    have key := norm_aeval_sub_aeval_le p (x := fun v => obsEval g X (MvPolynomial.X v))
      (y := fun v => obsEval g Y (MvPolynomial.X v)) (B := 1) (δ := L * δ) zero_le_one
      (fun v _ => cq_var_norm hW hg hX v) (fun v _ => cq_var_norm hW hg hY v) hvars
    rw [← hev X p, ← hev Y p] at key
    refine key.trans ?_
    simp only [one_pow, mul_one]
    have hsum : ∑ d ∈ p.support, ‖p.coeff d‖ * ((Finsupp.degree d : ℕ) : ℝ) ≤
        K₀ * ∑ d ∈ S, ((Finsupp.degree d : ℕ) : ℝ) := by
      calc ∑ d ∈ p.support, ‖p.coeff d‖ * ((Finsupp.degree d : ℕ) : ℝ)
          ≤ ∑ d ∈ p.support, K₀ * ((Finsupp.degree d : ℕ) : ℝ) :=
            Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_right (hK d) (Nat.cast_nonneg _)
        _ ≤ ∑ d ∈ S, K₀ * ((Finsupp.degree d : ℕ) : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hS fun d _ _ =>
              mul_nonneg hK₀ (Nat.cast_nonneg _)
        _ = K₀ * ∑ d ∈ S, ((Finsupp.degree d : ℕ) : ℝ) := by rw [Finset.mul_sum]
    calc (∑ d ∈ p.support, ‖p.coeff d‖ * ((Finsupp.degree d : ℕ) : ℝ)) * (L * δ)
        ≤ (K₀ * ∑ d ∈ S, ((Finsupp.degree d : ℕ) : ℝ)) * (L * δ) :=
          mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = _ := by ring

/-- (11.28) [lg:eq:Q-regularity] for every coefficient vector: on a window fixed after `R` and the
index set, `|Q_g| ≤ K Σ |q_k|` and `|Q_g(X) − Q_g(Y)| ≤ K Σ |q_k| (‖C_X − C_Y‖ + ‖v_X − v_Y‖)`
on states, uniformly in `W ≥ 1` and `g ≥ 1`. -/
theorem corrQ_bounds (R : ℕ) (Ks : Finset NzInt) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₁ →
      ∀ q : NzInt → ℂ, ∀ X Y : State W, IsState X → IsState Y →
        |corrQ g E R Ks q X| ≤ K * ∑ k ∈ Ks, ‖q k‖ ∧
          |corrQ g E R Ks q X - corrQ g E R Ks q Y| ≤
            K * (∑ k ∈ Ks, ‖q k‖) * (‖X.1 - Y.1‖ + ‖X.2 - Y.2‖) := by
  obtain ⟨E₁, hE₁, S, K₀, hK₀, h⟩ := corrCoeff_bounded R Ks
  set N : ℝ := S.card * K₀ with hN
  set M : ℝ := K₀ * (∑ d ∈ S, ((Finsupp.degree d : ℕ) : ℝ)) *
    (2 + ∑ u ∈ S.biUnion Finsupp.support, (u.idx.natAbs : ℝ)) with hM
  have hN0 : 0 ≤ N := by positivity
  have hM0 : 0 ≤ M := by positivity
  refine ⟨E₁, hE₁, N + M + 1, by positivity, ?_⟩
  intro W hW g hg E hE q X Y hX hY
  have hF : ∀ k ∈ Ks, ‖obsEval g X (corrObsF E R k)‖ ≤ N ∧
      ‖obsEval g X (corrObsF E R k) - obsEval g Y (corrObsF E R k)‖ ≤
        M * (‖X.1 - Y.1‖ + ‖X.2 - Y.2‖) := by
    intro k hk
    have hv := h E hE k hk (ObsVar.f k) (by simp)
    exact cq_poly_bounds hW hg hX hY (corrObsF E R k) S K₀ hv.1 (fun d => (hv.2.2.2 d).1) hK₀.le
  have hs0 : 0 ≤ ∑ k ∈ Ks, ‖q k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hδ0 : 0 ≤ ‖X.1 - Y.1‖ + ‖X.2 - Y.2‖ := by positivity
  refine ⟨?_, ?_⟩
  · calc |corrQ g E R Ks q X| ≤ ‖∑ k ∈ Ks, q k * obsEval g X (corrObsF E R k)‖ :=
          Complex.abs_re_le_norm _
      _ ≤ ∑ k ∈ Ks, ‖q k * obsEval g X (corrObsF E R k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Ks, ‖q k‖ * N := Finset.sum_le_sum fun k hk => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hF k hk).1 (norm_nonneg _)
      _ = N * ∑ k ∈ Ks, ‖q k‖ := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ (N + M + 1) * ∑ k ∈ Ks, ‖q k‖ :=
          mul_le_mul_of_nonneg_right (by linarith) hs0
  · have e : corrQ g E R Ks q X - corrQ g E R Ks q Y =
        (∑ k ∈ Ks, q k * (obsEval g X (corrObsF E R k) - obsEval g Y (corrObsF E R k))).re := by
      simp only [corrQ, ← Complex.sub_re, ← Finset.sum_sub_distrib, mul_sub]
    rw [e]
    calc |(∑ k ∈ Ks, q k * (obsEval g X (corrObsF E R k) - obsEval g Y (corrObsF E R k))).re|
        ≤ ‖∑ k ∈ Ks, q k * (obsEval g X (corrObsF E R k) - obsEval g Y (corrObsF E R k))‖ :=
          Complex.abs_re_le_norm _
      _ ≤ ∑ k ∈ Ks, ‖q k * (obsEval g X (corrObsF E R k) - obsEval g Y (corrObsF E R k))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k ∈ Ks, ‖q k‖ * (M * (‖X.1 - Y.1‖ + ‖X.2 - Y.2‖)) :=
          Finset.sum_le_sum fun k hk => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hF k hk).2 (norm_nonneg _)
      _ = M * (∑ k ∈ Ks, ‖q k‖) * (‖X.1 - Y.1‖ + ‖X.2 - Y.2‖) := by
          rw [← Finset.sum_mul]; ring
      _ ≤ (N + M + 1) * (∑ k ∈ Ks, ‖q k‖) * (‖X.1 - Y.1‖ + ‖X.2 - Y.2‖) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hs0) hδ0

end LSBA
