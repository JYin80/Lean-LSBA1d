import LSBA.Upper.CoercivityMap

/-!
# The coercivity inequality (G.13) [cg:eq:coercive]

`Φ_G(P) = Σ_j G_j P* G_j`, its mean `𝔼Φ(P) = m W⁻¹ conj(Tr P) I` under the covariance (1.2)
[eq:covariance], the numerical radius `N(G) = sup_{‖P‖=1} |⟨P, (Φ_G - 𝔼Φ) P⟩|`, and the
deterministic form of (G.13) [cg:eq:coercive] for Hermitian `G_j`:
`S_W(G)² ≥ 2 λ_min(Σ_j G_j²) - 2 N(G)`, from `𝓛_G* 𝓛_G = 2S + 2Φ_G` and
`⟨P, 𝔼Φ(P)⟩ = m W⁻¹ (Re Tr P)² ≥ 0` on `𝒬_W` (Appendix G.4 [app:compact-gaussian]).
-/

open Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `Φ_G(P) = Σ_j G_j P* G_j` (proof of Lemma G.4 [lem:c-gaussian]). -/
def phiMap {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ) (P : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  ∑ j, G j * Pᴴ * G j

/-- The numerical radius `N(G) = sup_{‖P‖ = 1} |Re Tr(P* (Φ_G(P) - m W⁻¹ conj(Tr P) I))|` of
`Φ_G - 𝔼Φ` for the real Hilbert–Schmidt inner product (proof of Lemma G.4 [lem:c-gaussian]). -/
def numRad {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ⨆ P : {P : Matrix (Fin W) (Fin W) ℂ // hsSq P = 1},
    |(P.1ᴴ * (phiMap G P.1 -
      ((m : ℂ) / W * star P.1.trace) • (1 : Matrix (Fin W) (Fin W) ℂ))).trace.re|

section CoercivityQuadraticAux

private lemma CoercivityQuadratic_hsSq_eq_trace {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    hsSq A = (Aᴴ * A).trace.re := by
  unfold hsSq
  rw [Finset.sum_comm, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']
  norm_cast

private lemma CoercivityQuadratic_hsSq_conjTranspose {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    hsSq Aᴴ = hsSq A := by
  unfold hsSq
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

private lemma CoercivityQuadratic_hsSq_add {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) :
    hsSq (A + B) = hsSq A + hsSq B + 2 * (Aᴴ * B).trace.re := by
  have h : (Bᴴ * A).trace = star (Aᴴ * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h2 : (Bᴴ * A).trace.re = (Aᴴ * B).trace.re := by
    rw [h]; simp
  simp only [CoercivityQuadratic_hsSq_eq_trace, Matrix.conjTranspose_add, add_mul, mul_add,
    Matrix.trace_add, Complex.add_re, h2]
  ring

private lemma CoercivityQuadratic_sum_hsSq_cohMap {m W : ℕ}
    (G : Fin m → Matrix (Fin W) (Fin W) ℂ) (hG : ∀ j, (G j).IsHermitian)
    (P : Matrix (Fin W) (Fin W) ℂ) :
    ∑ j, hsSq (cohMap G P j) =
      2 * ∑ j, hsSq (G j * P) + 2 * (Pᴴ * phiMap G P).trace.re := by
  have hj : ∀ j, hsSq (cohMap G P j) =
      2 * hsSq (G j * P) + 2 * (Pᴴ * (G j * Pᴴ * G j)).trace.re := by
    intro j
    have hA : (G j * P)ᴴ = Pᴴ * G j := by rw [Matrix.conjTranspose_mul, (hG j).eq]
    have h1 : cohMap G P j = G j * P + (G j * P)ᴴ := by rw [hA]; rfl
    rw [h1, CoercivityQuadratic_hsSq_add, CoercivityQuadratic_hsSq_conjTranspose, hA]
    have : Pᴴ * G j * (Pᴴ * G j) = Pᴴ * (G j * Pᴴ * G j) := by
      simp only [Matrix.mul_assoc]
    rw [this]
    ring
  simp only [hj, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 2
  unfold phiMap
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

private lemma CoercivityQuadratic_quadMin_mul_le {m W : ℕ}
    (G : Fin m → Matrix (Fin W) (Fin W) ℂ) (y : Fin W → ℂ) :
    quadMin G * ∑ a, ‖y a‖ ^ 2 ≤ ∑ j, ∑ a, ‖(G j *ᵥ y) a‖ ^ 2 := by
  have hbdd : BddBelow (Set.range fun z : {z : Fin W → ℂ // ∑ a, ‖z a‖ ^ 2 = 1} =>
      ∑ j, ∑ a, ‖(G j *ᵥ z.1) a‖ ^ 2) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; positivity⟩
  rcases (show 0 ≤ ∑ a, ‖y a‖ ^ 2 by positivity).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; positivity
  · set N := ∑ a, ‖y a‖ ^ 2 with hN
    have hspos : 0 < Real.sqrt N := Real.sqrt_pos.2 hpos
    have hs2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hpos.le
    have hmem : ∑ a, ‖((Real.sqrt N)⁻¹ • y) a‖ ^ 2 = 1 := by
      simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← Finset.mul_sum]
      rw [← hN, inv_pow, hs2]
      exact inv_mul_cancel₀ hpos.ne'
    have h := ciInf_le hbdd (⟨(Real.sqrt N)⁻¹ • y, hmem⟩ : {z : Fin W → ℂ //
      ∑ a, ‖z a‖ ^ 2 = 1})
    have hq : ∑ j, ∑ a, ‖(G j *ᵥ ((Real.sqrt N)⁻¹ • y)) a‖ ^ 2 =
        (Real.sqrt N)⁻¹ ^ 2 * ∑ j, ∑ a, ‖(G j *ᵥ y) a‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [Matrix.mulVec_smul, mul_pow]
    have h' : quadMin G ≤ (Real.sqrt N)⁻¹ ^ 2 * ∑ j, ∑ a, ‖(G j *ᵥ y) a‖ ^ 2 := by
      rw [← hq]; exact h
    have h3 : quadMin G * N ≤ (Real.sqrt N)⁻¹ ^ 2 * (∑ j, ∑ a, ‖(G j *ᵥ y) a‖ ^ 2) * N :=
      mul_le_mul_of_nonneg_right h' hpos.le
    have h4 : (Real.sqrt N)⁻¹ ^ 2 * N = 1 := by
      rw [inv_pow, hs2]; exact inv_mul_cancel₀ hpos.ne'
    calc quadMin G * N ≤ (Real.sqrt N)⁻¹ ^ 2 * (∑ j, ∑ a, ‖(G j *ᵥ y) a‖ ^ 2) * N := h3
      _ = ∑ j, ∑ a, ‖(G j *ᵥ y) a‖ ^ 2 := by
          rw [mul_right_comm, h4, one_mul]

private lemma CoercivityQuadratic_quadMin_le_sum {m W : ℕ}
    (G : Fin m → Matrix (Fin W) (Fin W) ℂ) {P : Matrix (Fin W) (Fin W) ℂ} (hP : hsSq P = 1) :
    quadMin G ≤ ∑ j, hsSq (G j * P) := by
  have key : ∀ j, hsSq (G j * P) = ∑ b, ∑ a, ‖(G j *ᵥ fun c => P c b) a‖ ^ 2 := by
    intro j
    unfold hsSq
    rw [Finset.sum_comm]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp only [key]
  rw [Finset.sum_comm]
  have hP' : ∑ b, ∑ a, ‖P a b‖ ^ 2 = 1 := by
    rw [← hP]; unfold hsSq; rw [Finset.sum_comm]
  calc quadMin G = quadMin G * ∑ b, ∑ a, ‖P a b‖ ^ 2 := by rw [hP', mul_one]
    _ = ∑ b, quadMin G * ∑ a, ‖(fun c => P c b) a‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ∑ b, ∑ j, ∑ a, ‖(G j *ᵥ fun c => P c b) a‖ ^ 2 :=
        Finset.sum_le_sum fun b _ => CoercivityQuadratic_quadMin_mul_le G _

private lemma CoercivityQuadratic_mean_term_nonneg {m W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.trace.im = 0) :
    0 ≤ (Pᴴ * (((m : ℂ) / W * star P.trace) • (1 : Matrix (Fin W) (Fin W) ℂ))).trace.re := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_conjTranspose,
    smul_eq_mul]
  have hz : P.trace = (P.trace.re : ℂ) := Complex.ext (by simp) (by simpa using hP)
  rw [hz]
  simp only [Complex.star_def, Complex.conj_ofReal]
  have : ((m : ℂ) / W * (P.trace.re : ℂ) * (P.trace.re : ℂ)) =
      (((m : ℝ) / W * P.trace.re * P.trace.re : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]
  have : 0 ≤ ((m : ℝ) / W) * (P.trace.re * P.trace.re) :=
    mul_nonneg (by positivity) (mul_self_nonneg _)
  linarith

private lemma CoercivityQuadratic_unit_nonempty {W : ℕ} (hW : W ≠ 0) :
    Nonempty {P : Matrix (Fin W) (Fin W) ℂ // P.trace.im = 0 ∧ hsSq P = 1} := by
  have i : Fin W := ⟨0, Nat.pos_of_ne_zero hW⟩
  refine ⟨⟨Matrix.single i i 1, ?_, ?_⟩⟩
  · simp
  · unfold hsSq
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [Ne.symm ha]
    · simp

private lemma CoercivityQuadratic_numRad_bddAbove {m W : ℕ}
    (G : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    BddAbove (Set.range fun P : {P : Matrix (Fin W) (Fin W) ℂ // hsSq P = 1} =>
      |(P.1ᴴ * (phiMap G P.1 -
        ((m : ℂ) / W * star P.1.trace) • (1 : Matrix (Fin W) (Fin W) ℂ))).trace.re|) := by
  set S : Set (Matrix (Fin W) (Fin W) ℂ) := {P | hsSq P = 1} with hS
  have hcont : Continuous fun P : Matrix (Fin W) (Fin W) ℂ => hsSq P := by
    unfold hsSq; fun_prop
  have hclosed : IsClosed S := isClosed_eq hcont continuous_const
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin W =>
      Set.pi Set.univ fun _ : Fin W => Metric.closedBall (0 : ℂ) 1 :
        Set (Matrix (Fin W) (Fin W) ℂ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hsub : S ⊆ (Set.pi Set.univ fun _ : Fin W =>
      Set.pi Set.univ fun _ : Fin W => Metric.closedBall (0 : ℂ) 1 :
        Set (Matrix (Fin W) (Fin W) ℂ)) := by
    intro P hP a _ b _
    have h1 : ‖P a b‖ ^ 2 ≤ 1 := by
      calc ‖P a b‖ ^ 2 ≤ ∑ b', ‖P a b'‖ ^ 2 :=
            Finset.single_le_sum (f := fun b' => ‖P a b'‖ ^ 2) (fun _ _ => by positivity)
              (Finset.mem_univ b)
        _ ≤ ∑ a', ∑ b', ‖P a' b'‖ ^ 2 :=
            Finset.single_le_sum (f := fun a' => ∑ b', ‖P a' b'‖ ^ 2)
              (fun _ _ => by positivity) (Finset.mem_univ a)
        _ = 1 := hP
    simpa using (pow_le_one_iff_of_nonneg (norm_nonneg _) (two_ne_zero)).1 h1
  have hcompact : IsCompact S := hbox.of_isClosed_subset hclosed hsub
  have hf : Continuous fun P : Matrix (Fin W) (Fin W) ℂ =>
      |(Pᴴ * (phiMap G P - ((m : ℂ) / W * star P.trace) •
        (1 : Matrix (Fin W) (Fin W) ℂ))).trace.re| := by
    have c1 : Continuous fun P : Matrix (Fin W) (Fin W) ℂ => Pᴴ :=
      continuous_id.matrix_conjTranspose
    have c2 : Continuous fun P : Matrix (Fin W) (Fin W) ℂ => P.trace :=
      continuous_id.matrix_trace
    have c3 : Continuous fun P : Matrix (Fin W) (Fin W) ℂ => phiMap G P := by
      unfold phiMap
      refine continuous_finsetSum _ fun j _ => ?_
      exact (continuous_const.matrix_mul c1).matrix_mul continuous_const
    have c4 : Continuous fun P : Matrix (Fin W) (Fin W) ℂ =>
        ((m : ℂ) / W * star P.trace) • (1 : Matrix (Fin W) (Fin W) ℂ) :=
      (continuous_const.mul (continuous_star.comp c2)).smul continuous_const
    exact (Complex.continuous_re.comp
      (((c1.matrix_mul (c3.sub c4)).matrix_trace))).abs
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image hf.continuousOn
  refine ⟨B, ?_⟩
  rintro _ ⟨P, rfl⟩
  exact hB ⟨P.1, P.2, rfl⟩

private lemma CoercivityQuadratic_pointwise {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (hG : ∀ j, (G j).IsHermitian) {P : Matrix (Fin W) (Fin W) ℂ} (hPim : P.trace.im = 0)
    (hP1 : hsSq P = 1) :
    2 * quadMin G - 2 * numRad G ≤ ∑ j, hsSq (cohMap G P j) := by
  rw [CoercivityQuadratic_sum_hsSq_cohMap G hG P]
  have h1 := CoercivityQuadratic_quadMin_le_sum G hP1
  have h2 := CoercivityQuadratic_mean_term_nonneg (m := m) hPim
  have h3 : -numRad G ≤ (Pᴴ * (phiMap G P -
      ((m : ℂ) / W * star P.trace) • (1 : Matrix (Fin W) (Fin W) ℂ))).trace.re := by
    have h := le_ciSup (CoercivityQuadratic_numRad_bddAbove G)
      (⟨P, hP1⟩ : {P : Matrix (Fin W) (Fin W) ℂ // hsSq P = 1})
    have h' : |(Pᴴ * (phiMap G P -
      ((m : ℂ) / W * star P.trace) • (1 : Matrix (Fin W) (Fin W) ℂ))).trace.re| ≤ numRad G := h
    have := neg_abs_le (Pᴴ * (phiMap G P -
      ((m : ℂ) / W * star P.trace) • (1 : Matrix (Fin W) (Fin W) ℂ))).trace.re
    linarith
  have h4 : (Pᴴ * phiMap G P).trace.re = (Pᴴ * (phiMap G P -
      ((m : ℂ) / W * star P.trace) • (1 : Matrix (Fin W) (Fin W) ℂ))).trace.re +
      (Pᴴ * (((m : ℂ) / W * star P.trace) • (1 : Matrix (Fin W) (Fin W) ℂ))).trace.re := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]; ring
  linarith

end CoercivityQuadraticAux

/-- (G.13) [cg:eq:coercive] for Hermitian `G_j`: `S_W(G)² ≥ 2 λ_min(Σ_j G_j²) - 2 N(G)`. -/
theorem coerMin_sq_ge {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (hG : ∀ j, (G j).IsHermitian) :
    2 * quadMin G - 2 * numRad G ≤ coerMin G ^ 2 := by
  have hcnn : 0 ≤ coerMin G ^ 2 := sq_nonneg _
  by_cases hW : W = 0
  · subst hW
    have : IsEmpty {y : Fin 0 → ℂ // ∑ a, ‖y a‖ ^ 2 = 1} :=
      ⟨fun ⟨y, h⟩ => by simp at h⟩
    have hq : quadMin G = 0 := Real.iInf_of_isEmpty _
    have hn : 0 ≤ numRad G := Real.iSup_nonneg fun _ => abs_nonneg _
    rw [hq]
    linarith
  · have := CoercivityQuadratic_unit_nonempty hW
    have hbdd : BddBelow (Set.range fun P : {P : Matrix (Fin W) (Fin W) ℂ //
        P.trace.im = 0 ∧ hsSq P = 1} => Real.sqrt (∑ j, hsSq (cohMap G P.1 j))) :=
      ⟨0, by rintro _ ⟨Q, rfl⟩; exact Real.sqrt_nonneg _⟩
    have hle : Real.sqrt (2 * quadMin G - 2 * numRad G) ≤ coerMin G :=
      le_ciInf fun ⟨P, hPim, hP1⟩ =>
        Real.sqrt_le_sqrt (CoercivityQuadratic_pointwise G hG hPim hP1)
    rcases le_or_gt 0 (2 * quadMin G - 2 * numRad G) with ht | ht
    · calc 2 * quadMin G - 2 * numRad G
          = Real.sqrt (2 * quadMin G - 2 * numRad G) ^ 2 := (Real.sq_sqrt ht).symm
        _ ≤ coerMin G ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
    · linarith

end LSBA
