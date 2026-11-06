import LSBA.Gauss.FreshEvent
import LSBA.Dyson.DeformClass
import LSBA.Spectral.InvSpectrum

/-!
# Regular inverse Riccati states and the one-block bounds

Appendix G [app:upper-gue]. A Hermitian state `R` is regular (9.3)
[us:eq:regular] if `‖R‖ ≤ W³` and `#{|g² r| > g} ≤ W g^{1/2}` over its eigenvalues `r`. For
`0 < g ≤ 1`, a regular `R` gives a deformation `g² R` in the class of Lemma G.1
[us:lem:local-law] with `ε = g^{1/2}`.

The one-block bounds (9.58) [us:eq:wegner] for the fresh deformed GUE matrix
`Γ = V_a - E - g² R`, with `R` fixed before block `a`, in the form used for the preparation,
the product moment and the buffered lower bound, and restricted to a set `S` fixed before
block `a`: `P(S, ‖Γ⁻¹‖ ≥ t W) ≤ (C/t) P(S)`; the Markov bound
`P(S, #{|g² r| > s} > T) ≤ (2 C W g² / (s T)) P(S)` for the eigenvalues `r` of `Γ⁻¹`; and
regularity of the outgoing state `Γ⁻¹` with failure `C (W⁻² + g^{1/2}) P(S)`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- A regular inverse Riccati state (9.3) [us:eq:regular]: `R` is Hermitian, `‖R‖ ≤ W³` and
`#{k : |g² r_k| > g} ≤ W g^{1/2}`. -/
def IsRegularState (W : ℕ) (g : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) : Prop :=
  R.IsHermitian ∧ ‖R‖ ≤ (W : ℝ) ^ 3 ∧
    (countIn (((g : ℂ) ^ 2) • R) {x | g < |x|} : ℝ) ≤ W * Real.sqrt g

/-- For `0 < g ≤ 1`, a regular state gives the deformation `g² R` in the class of Lemma G.1
[us:lem:local-law] with `ε = g^{1/2}` (Appendix G [app:upper-gue]). -/
theorem IsRegularState.deformClass {W : ℕ} {g : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : IsRegularState W g R) (hg : 0 < g) (hg1 : g ≤ 1) :
    DeformClass (Real.sqrt g) (((g : ℂ) ^ 2) • R) := by
  obtain ⟨hH, -, hc⟩ := hR
  have hk : IsSelfAdjoint ((g : ℂ) ^ 2) := by
    rw [isSelfAdjoint_iff]; simp
  refine deformClass_of_countIn_le (hH.smul hk) hg.le ?_ ?_
  · exact (Real.le_sqrt' hg).2 (by nlinarith)
  · rw [Fintype.card_fin, mul_comm]
    exact hc

/-- The zero state is regular; it is the initial state of the right-cavity chain of Section 9.2
[su:sec:explicit-generator]. -/
theorem isRegularState_zero (W : ℕ) {g : ℝ} (hg : 0 ≤ g) : IsRegularState W g 0 := by
  refine ⟨Matrix.isHermitian_zero, by rw [norm_zero]; positivity, ?_⟩
  have h := countIn_abs_gt_le_rank (B := ((g : ℂ) ^ 2) • (0 : Matrix (Fin W) (Fin W) ℂ))
    (Bs := 0) (Bb := 0) (ε := g) (by simp) (by simp) (by simp [hg])
  rw [Matrix.rank_zero, Nat.le_zero] at h
  rw [h, Nat.cast_zero]
  positivity

/-- The matrix inverse `X ↦ X⁻¹ = det(X)⁻¹ adj(X)` is Borel. -/
private lemma regularState_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable fun X : Matrix ι ι ℂ => X⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have h : (fun X : Matrix ι ι ℂ => X⁻¹ i j) = fun X => (X.det)⁻¹ * X.adjugate i j := by
    funext X
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [h]
  have hd : Continuous fun X : Matrix ι ι ℂ => X.det := continuous_id.matrix_det
  have ha : Continuous fun X : Matrix ι ι ℂ => X.adjugate i j :=
    (continuous_id.matrix_adjugate).matrix_elem i j
  exact hd.measurable.inv.mul ha.measurable

/-- The decreasing eigenvalue of index `j` is Borel on all matrices. -/
private lemma regularState_measurable_sortedEig (n : ℕ) (j : Fin (Fintype.card (Fin n))) :
    Measurable fun M : Matrix (Fin n) (Fin n) ℂ => sortedEig M j := by
  have hS : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | M.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have heq : (fun M : Matrix (Fin n) (Fin n) ℂ => sortedEig M j) =
      Set.piecewise {M : Matrix (Fin n) (Fin n) ℂ | M.IsHermitian}
        (fun M => sortedEig M j) (fun _ => 0) := by
    funext M
    by_cases hM : M.IsHermitian
    · rw [Set.piecewise_eq_of_mem _ _ _ hM]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hM]
      simp [sortedEig, hM]
  rw [heq]
  exact ContinuousOn.measurable_piecewise
    ((continuous_apply j).comp_continuousOn continuousOn_sortedEig)
    continuousOn_const hS.measurableSet

/-- `M ↦ #{eigenvalues of M in J}` is Borel on all matrices for measurable `J`. -/
private lemma regularState_measurable_countIn (n : ℕ) {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable fun M : Matrix (Fin n) (Fin n) ℂ => countIn M J := by
  have hS : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | M.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hsum : Measurable fun M : Matrix (Fin n) (Fin n) ℂ =>
      ∑ j, if sortedEig M j ∈ J then 1 else 0 :=
    Finset.measurable_sum _ fun j _ => Measurable.ite
      (hJ.preimage (regularState_measurable_sortedEig n j)) measurable_const measurable_const
  have heq : (fun M : Matrix (Fin n) (Fin n) ℂ => countIn M J) =
      Set.piecewise {M : Matrix (Fin n) (Fin n) ℂ | M.IsHermitian}
        (fun M => ∑ j, if sortedEig M j ∈ J then 1 else 0) (fun _ => 0) := by
    funext M
    by_cases hM : M.IsHermitian
    · rw [Set.piecewise_eq_of_mem _ _ _ hM]
      simp only [countIn, hM, ↓reduceDIte, Finset.card_filter, eigenvalues_eq_sortedEig hM]
      exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
        (fun j => if sortedEig M j ∈ J then 1 else 0)
    · rw [Set.piecewise_eq_of_notMem _ _ _ hM]
      simp [countIn, hM]
  rw [heq]
  exact hsum.piecewise hS.measurableSet measurable_const

/-- `V - E - g² R` is Hermitian for Hermitian `V` and `R` and real `E`, `g`. -/
private lemma regularState_shift_isHermitian {W : ℕ} {V R : Matrix (Fin W) (Fin W) ℂ}
    (hV : V.IsHermitian) (hR : R.IsHermitian) (E g : ℝ) :
    (V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R).IsHermitian := by
  have hE : IsSelfAdjoint (E : ℂ) := by rw [isSelfAdjoint_iff]; simp
  have hk : IsSelfAdjoint ((g : ℂ) ^ 2) := by rw [isSelfAdjoint_iff]; simp
  exact (hV.sub (Matrix.isHermitian_one.smul hE)).sub (hR.smul hk)

/-- `-(E + g² R)` is Hermitian for Hermitian `R` and real `E`, `g`. -/
private lemma regularState_neg_isHermitian {W : ℕ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (E g : ℝ) :
    (-((E : ℂ) • 1 + ((g : ℂ) ^ 2) • R)).IsHermitian := by
  have hE : IsSelfAdjoint (E : ℂ) := by rw [isSelfAdjoint_iff]; simp
  have hk : IsSelfAdjoint ((g : ℂ) ^ 2) := by rw [isSelfAdjoint_iff]; simp
  exact ((Matrix.isHermitian_one.smul hE).add (hR.smul hk)).neg

/-- `V - E - g² R = -(E + g² R) + V`. -/
private lemma regularState_shift_eq {W : ℕ} (V R : Matrix (Fin W) (Fin W) ℂ) (E g : ℝ) :
    V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R = -((E : ℂ) • 1 + ((g : ℂ) ^ 2) • R) + V := by
  abel

/-- `(V, R) ↦ V - E - g² R` is Borel. -/
private lemma regularState_measurable_shift {W : ℕ} (E g : ℝ) :
    Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
      p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2 :=
  Continuous.measurable (by fun_prop)

/-- Eigenvalue counts of a scaled inverse: for an invertible Hermitian `A` and real `c`,
`#{k : λ_k(c A⁻¹) ∈ S} = #{k : c λ_k(A)⁻¹ ∈ S}`. -/
private lemma regularState_countIn_smul_inv {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (hu : IsUnit A) (c : ℝ) (S : Set ℝ) :
    countIn ((c : ℂ) • A⁻¹) S = countIn A {x | c * x⁻¹ ∈ S} := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hdet : ∀ k, (hA.eigenvalues k : ℂ) ≠ 0 := by
    have h := (Matrix.isUnit_iff_isUnit_det A).mp hu
    rw [hA.det_eq_prod_eigenvalues] at h
    intro k
    exact (Finset.prod_ne_zero_iff.mp h.ne_zero) k (Finset.mem_univ k)
  have hspec : A = U * Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ)) * Uᴴ := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hinv : A⁻¹ = U * Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ))⁻¹) * Uᴴ := by
    apply Matrix.inv_eq_right_inv
    calc A * (U * Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ))⁻¹) * Uᴴ)
        = (U * Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ)) * Uᴴ) *
          (U * Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ))⁻¹) * Uᴴ) := by
            rw [← hspec]
      _ = U * (Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ)) * (Uᴴ * U) *
          Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ))⁻¹)) * Uᴴ := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hU1, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
        have : (fun k => (hA.eigenvalues k : ℂ) * ((hA.eigenvalues k : ℂ))⁻¹) = fun _ => 1 := by
          funext k; exact mul_inv_cancel₀ (hdet k)
        rw [this, Matrix.diagonal_one, Matrix.mul_one, hU2]
  have hinv' : (c : ℂ) • A⁻¹ =
      U * Matrix.diagonal (fun k => ((c * (hA.eigenvalues k)⁻¹ : ℝ) : ℂ)) * Uᴴ := by
    have hD : Matrix.diagonal (fun k => ((c * (hA.eigenvalues k)⁻¹ : ℝ) : ℂ)) =
        (c : ℂ) • Matrix.diagonal (fun k => ((hA.eigenvalues k : ℂ))⁻¹) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [hD, hinv, Matrix.mul_smul, Matrix.smul_mul]
  have hk : IsSelfAdjoint (c : ℂ) := by rw [isSelfAdjoint_iff]; simp
  have hcp : ((c : ℂ) • A⁻¹).charpoly =
      ∏ k, (Polynomial.X - Polynomial.C (((c * (hA.eigenvalues k)⁻¹ : ℝ)) : ℂ)) := by
    rw [hinv', Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul,
      Matrix.charpoly_diagonal]
  have hroots : ((c : ℂ) • A⁻¹).charpoly.roots =
      Multiset.map (fun k => (((c * (hA.eigenvalues k)⁻¹ : ℝ)) : ℂ)) Finset.univ.val := by
    rw [hcp, Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    · exact Finset.prod_ne_zero_iff.mpr fun k _ => Polynomial.X_sub_C_ne_zero _
  rw [countIn_eq_card_roots (hA.inv.smul hk), hroots, Multiset.filter_map]
  simp [countIn, hA, Finset.card_def, Finset.filter_val]

/-- For a Hermitian `Γ` and `s > 0`, the eigenvalues `r` of `Γ⁻¹` with `|g² r| > s` correspond to
eigenvalues of `Γ` in `[-g²/s, g²/s]`. -/
private lemma regularState_countIn_inv_le {n : Type*} [Fintype n] [DecidableEq n]
    {Γ : Matrix n n ℂ} (hΓ : Γ.IsHermitian) {s : ℝ} (hs : 0 < s) (g : ℝ) :
    countIn (((g : ℂ) ^ 2) • Γ⁻¹) {x | s < |x|} ≤
      countIn Γ (Set.Icc (-(g ^ 2 / s)) (g ^ 2 / s)) := by
  by_cases hu : IsUnit Γ
  · have hg2 : ((g : ℂ) ^ 2) = ((g ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hg2, regularState_countIn_smul_inv hΓ hu]
    simp only [countIn, hΓ, ↓reduceDIte]
    refine Finset.card_le_card fun k hk => ?_
    simp only [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    have hx := hk.2
    simp only [Set.mem_ofPred_eq] at hx
    simp only [Set.mem_Icc]
    have hx0 : hΓ.eigenvalues k ≠ 0 := by
      intro h0
      rw [h0] at hx
      simp at hx
      linarith
    have hxpos : 0 < |hΓ.eigenvalues k| := abs_pos.2 hx0
    rw [abs_mul, abs_inv, abs_of_nonneg (sq_nonneg g), ← div_eq_mul_inv,
      lt_div_iff₀ hxpos] at hx
    rw [← abs_le, le_div_iff₀ hs]
    nlinarith
  · have h0 : Γ⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ (by rwa [← Matrix.isUnit_iff_isUnit_det])
    rw [h0, smul_zero]
    have h := countIn_abs_gt_le_rank (B := (0 : Matrix n n ℂ)) (Bs := 0) (Bb := 0) (ε := s)
      Matrix.isHermitian_zero (by simp) (by simp [hs.le])
    rw [Matrix.rank_zero, Nat.le_zero] at h
    rw [h]
    exact Nat.zero_le _

/-- (9.58) [us:eq:wegner], second estimate, at block `a` with a state `R` and a set `S` fixed
before block `a`: `P(S, ‖(V_a - E - g² R)⁻¹‖ ≥ t W) ≤ (C/t) P(S)`. -/
theorem fresh_inv_norm_tail : ∃ C : ℝ, 0 < C ∧
    ∀ (W L : ℕ) (a : Fin L) (Rp : Ω W L → Matrix (Fin W) (Fin W) ℂ) (S : Set (Ω W L)),
      1 ≤ W → Measurable Rp → (∀ ω, (Rp ω).IsHermitian) → OffBlock W L a Rp →
      MeasurableSet S → OffBlock W L a (· ∈ S) → ∀ g E t : ℝ, 0 < t →
      μ W L {ω | ω ∈ S ∧
          t * W ≤ ‖(gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹‖} ≤
        ENNReal.ofReal (C / t) * μ W L S := by
  obtain ⟨C, hC, h⟩ := gueMat_inv_norm_tail
  refine ⟨C, hC, fun W L a Rp S hW hRm hRh hRa hS hSa g E t ht => ?_⟩
  have hTm : MeasurableSet {p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ |
      t * W ≤ ‖(p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2)⁻¹‖} :=
    measurableSet_le measurable_const (continuous_norm.measurable.comp
      (regularState_measurable_inv.comp (regularState_measurable_shift E g)))
  refine measure_gueBlock_fresh_le W L a hRm hRa hS hSa hTm (fun ω _ => ?_)
  have hA := regularState_neg_isHermitian (hRh ω) E g
  have e : {ω' : Ω W 1 | (gueMat W ω', Rp ω) ∈ {p : Matrix (Fin W) (Fin W) ℂ ×
      Matrix (Fin W) (Fin W) ℂ | t * W ≤ ‖(p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2)⁻¹‖}} =
      {ω' | t * W ≤ ‖(-((E : ℂ) • 1 + ((g : ℂ) ^ 2) • Rp ω) + gueMat W ω')⁻¹‖} := by
    ext ω'
    simp only [Set.mem_ofPred_eq, regularState_shift_eq]
  rw [e]
  exact h W hW _ hA t ht

/-- (9.58) [us:eq:wegner], first estimate, as a Markov bound for the outgoing state: the number
of eigenvalues `r` of `(V_a - E - g² R)⁻¹` with `|g² r| > s` exceeds `T` with probability at most
`(2 C W g² / (s T)) P(S)` on a set `S` fixed before block `a`. -/
theorem fresh_inv_count_tail : ∃ C : ℝ, 0 < C ∧
    ∀ (W L : ℕ) (a : Fin L) (Rp : Ω W L → Matrix (Fin W) (Fin W) ℂ) (S : Set (Ω W L)),
      1 ≤ W → Measurable Rp → (∀ ω, (Rp ω).IsHermitian) → OffBlock W L a Rp →
      MeasurableSet S → OffBlock W L a (· ∈ S) → ∀ g E s T : ℝ, 0 < s → 0 < T →
      μ W L {ω | ω ∈ S ∧ T < (countIn (((g : ℂ) ^ 2) •
          (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹) {x | s < |x|} : ℝ)} ≤
        ENNReal.ofReal (2 * C * W * g ^ 2 / (s * T)) * μ W L S := by
  obtain ⟨C, hC, h⟩ := lintegral_countIn_add_gueMat_le
  refine ⟨C, hC, fun W L a Rp S hW hRm hRh hRa hS hSa g E s T hs hT => ?_⟩
  have hTm : MeasurableSet {p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ |
      T < (countIn (((g : ℂ) ^ 2) • (p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2)⁻¹)
        {x | s < |x|} : ℝ)} := by
    have hm : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
        countIn (((g : ℂ) ^ 2) • (p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2)⁻¹) {x | s < |x|} :=
      (regularState_measurable_countIn W (measurableSet_lt measurable_const measurable_id.abs)
        ).comp ((regularState_measurable_inv.comp
          (regularState_measurable_shift E g)).fun_const_smul ((g : ℂ) ^ 2))
    exact measurableSet_lt measurable_const
      ((measurable_from_top : Measurable fun m : ℕ => (m : ℝ)).comp hm)
  refine measure_gueBlock_fresh_le W L a hRm hRa hS hSa hTm (fun ω _ => ?_)
  obtain ⟨A, hAdef, hA⟩ : ∃ A : Matrix (Fin W) (Fin W) ℂ,
      A = -((E : ℂ) • 1 + ((g : ℂ) ^ 2) • Rp ω) ∧ A.IsHermitian :=
    ⟨_, rfl, regularState_neg_isHermitian (hRh ω) E g⟩
  have hshift : ∀ ω' : Ω W 1, gueMat W ω' - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω =
      A + gueMat W ω' := fun ω' => by rw [hAdef]; exact regularState_shift_eq _ _ E g
  have hsub : {ω' : Ω W 1 | (gueMat W ω', Rp ω) ∈ {p : Matrix (Fin W) (Fin W) ℂ ×
      Matrix (Fin W) (Fin W) ℂ | T < (countIn (((g : ℂ) ^ 2) •
        (p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2)⁻¹) {x | s < |x|} : ℝ)}} ⊆
      {ω' : Ω W 1 | ENNReal.ofReal T ≤
        (countIn (A + gueMat W ω') (Set.Icc (-(g ^ 2 / s)) (g ^ 2 / s)) : ℝ≥0∞)} := by
    intro ω' hω'
    simp only [Set.mem_ofPred_eq, hshift] at hω' ⊢
    have h1 := regularState_countIn_inv_le (Γ := A + gueMat W ω')
      (hA.add (gueBlock_isHermitian W 1 ω' 0)) hs g
    have h2 : T < (countIn (A + gueMat W ω') (Set.Icc (-(g ^ 2 / s)) (g ^ 2 / s)) : ℝ) :=
      lt_of_lt_of_le hω' (by exact_mod_cast h1)
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal h2.le
  have hmeas : Measurable fun ω' : Ω W 1 =>
      (countIn (A + gueMat W ω') (Set.Icc (-(g ^ 2 / s)) (g ^ 2 / s)) : ℝ≥0∞) :=
    (measurable_from_top : Measurable fun m : ℕ => (m : ℝ≥0∞)).comp
      (measurable_countIn_add_gueMat W hA measurableSet_Icc)
  have hTpos : ENNReal.ofReal T ≠ 0 := (ENNReal.ofReal_pos.2 hT).ne'
  calc _ ≤ μ W 1 {ω' : Ω W 1 | ENNReal.ofReal T ≤
        (countIn (A + gueMat W ω') (Set.Icc (-(g ^ 2 / s)) (g ^ 2 / s)) : ℝ≥0∞)} :=
        measure_mono hsub
    _ ≤ (∫⁻ ω', (countIn (A + gueMat W ω') (Set.Icc (-(g ^ 2 / s)) (g ^ 2 / s)) : ℝ≥0∞)
        ∂(μ W 1)) / ENNReal.ofReal T :=
        meas_ge_le_lintegral_div hmeas.aemeasurable hTpos ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C * W * (g ^ 2 / s - -(g ^ 2 / s))) / ENNReal.ofReal T :=
        ENNReal.div_le_div_right (h W A hA _ _) _
    _ = ENNReal.ofReal (2 * C * W * g ^ 2 / (s * T)) := by
        rw [← ENNReal.ofReal_div_of_pos hT]
        congr 1
        field_simp
        ring

/-- Regularity of the outgoing state (Appendix G [app:upper-gue], after (9.58)
[us:eq:wegner], with `δ = 2` and Markov's inequality on `[-g, g]`): on a set `S` fixed before
block `a`, `(V_a - E - g² R)⁻¹` fails (9.3) [us:eq:regular] with probability at most
`C (W⁻² + g^{1/2}) P(S)`, uniformly in the earlier state `R`. -/
theorem fresh_regular : ∃ C : ℝ, 0 < C ∧
    ∀ (W L : ℕ) (a : Fin L) (Rp : Ω W L → Matrix (Fin W) (Fin W) ℂ) (S : Set (Ω W L)),
      1 ≤ W → Measurable Rp → (∀ ω, (Rp ω).IsHermitian) → OffBlock W L a Rp →
      MeasurableSet S → OffBlock W L a (· ∈ S) → ∀ g E : ℝ, 0 < g →
      μ W L {ω | ω ∈ S ∧
          ¬ IsRegularState W g (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹} ≤
        ENNReal.ofReal (C * ((W : ℝ) ^ (-2 : ℝ) + Real.sqrt g)) * μ W L S := by
  obtain ⟨C₁, hC₁, h₁⟩ := fresh_inv_norm_tail
  obtain ⟨C₂, hC₂, h₂⟩ := fresh_inv_count_tail
  refine ⟨max C₁ (2 * C₂), lt_max_of_lt_left hC₁, fun W L a Rp S hW hRm hRh hRa hS hSa g E hg => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  have hsq : Real.sqrt g * Real.sqrt g = g := Real.mul_self_sqrt hg.le
  have hsub : {ω : Ω W L | ω ∈ S ∧ ¬ IsRegularState W g
      (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹} ⊆
      {ω | ω ∈ S ∧ (W : ℝ) ^ 2 * W ≤
        ‖(gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹‖} ∪
      {ω | ω ∈ S ∧ (W * Real.sqrt g) < (countIn (((g : ℂ) ^ 2) •
        (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹) {x | g < |x|} : ℝ)} := by
    rintro ω ⟨hωS, hω⟩
    have hH : ((gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹).IsHermitian :=
      (regularState_shift_isHermitian (gueBlock_isHermitian W L ω a) (hRh ω) E g).inv
    by_cases hn : ‖(gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹‖ ≤ (W : ℝ) ^ 3
    · refine Or.inr ⟨hωS, ?_⟩
      by_contra hc
      exact hω ⟨hH, hn, not_lt.mp hc⟩
    · refine Or.inl ⟨hωS, ?_⟩
      have : (W : ℝ) ^ 2 * W = (W : ℝ) ^ 3 := by ring
      rw [this]
      exact (not_le.mp hn).le
  have hb1 := h₁ W L a Rp S hW hRm hRh hRa hS hSa g E ((W : ℝ) ^ 2) (by positivity)
  have hb2 := h₂ W L a Rp S hW hRm hRh hRa hS hSa g E g (W * Real.sqrt g) hg (by positivity)
  have e1 : C₁ / (W : ℝ) ^ 2 = C₁ * (W : ℝ) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hW0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have e2 : 2 * C₂ * W * g ^ 2 / (g * (W * Real.sqrt g)) = 2 * C₂ * Real.sqrt g := by
    rw [div_eq_iff (by positivity)]
    linear_combination (-(2 * C₂ * W * g)) * hsq
  rw [e1] at hb1
  rw [e2] at hb2
  have hx : 0 ≤ (W : ℝ) ^ (-2 : ℝ) := by positivity
  have hy : 0 ≤ Real.sqrt g := hsg.le
  calc _ ≤ μ W L _ := measure_mono hsub
    _ ≤ μ W L {ω : Ω W L | ω ∈ S ∧ (W : ℝ) ^ 2 * W ≤
        ‖(gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹‖} +
        μ W L {ω | ω ∈ S ∧ (W * Real.sqrt g) < (countIn (((g : ℂ) ^ 2) •
        (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹) {x | g < |x|} : ℝ)} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₁ * (W : ℝ) ^ (-2 : ℝ)) * μ W L S +
        ENNReal.ofReal (2 * C₂ * Real.sqrt g) * μ W L S := add_le_add hb1 hb2
    _ = ENNReal.ofReal (C₁ * (W : ℝ) ^ (-2 : ℝ) + 2 * C₂ * Real.sqrt g) * μ W L S := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), add_mul]
    _ ≤ _ := by
        gcongr
        have h1 : C₁ * (W : ℝ) ^ (-2 : ℝ) ≤ max C₁ (2 * C₂) * (W : ℝ) ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hx
        have h2 : 2 * C₂ * Real.sqrt g ≤ max C₁ (2 * C₂) * Real.sqrt g :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hy
        linarith

end LSBA
