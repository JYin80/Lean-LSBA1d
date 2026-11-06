import LSBA.Upper.RegularState
import LSBA.Upper.RicChain
import LSBA.Spectral.DeformedRelLaw

/-!
# The buffered product lower bound

Lemma G.3 [nc:lem:buffer], (9.69) [nc:eq:profile], in the critical window of Lemma 8.12
[up:lem:small-contraction](ii). Let `0 < θ ≤ 1/100`, `υ = W^{-1+2θ}` and
`0 < g ≤ W^{-1/2+θ/2}`, so that `g² ≤ υ` and `W υ = W^{2θ}`. For a deterministic state `R_4` with
`‖R_4‖ ≤ W^{1+θ}` that is regular (9.3) [us:eq:regular], a fixed `v_4 ≠ 0`, `h = q - 5` active
blocks and every `D > 0`, the chain `R_j = (V_j - E - g² R_{j-1})⁻¹` satisfies
`‖R_{q-1} ⋯ R_5 v_4‖ ≥ c_{q-5} υ^{-(q-5)/2} ‖v_4‖ W^{-3θ}` whenever `R_4, …, R_{q-2}` are regular,
except with probability `W^{-D}`.

Each step uses the identity `u* R_j F_j R_j u = υ⁻¹ Im u* (R_j⁻¹ - iυ)⁻¹ u` with
`F_j = (1 + υ² R_j²)⁻¹`, the lower bound of the relative local law (G.2)
[us:eq:relative-local-law] at `η = υ` for `B = g² R_{j-1}`, and `g² ≤ υ` ((G.9)
[nc:eq:bufferstep]). The lower bound `c_* W^{-1/2} ≤ g` of (8.37) [eq:critical-window] is not
used.

The same iteration holds at a generic spectral scale `η` with `g² ≤ η` and
`W^{-1+δ} ≤ η ≤ C_*`, for `0 < g ≤ g₀`: with `F_j = (1 + η² R_j²)⁻¹`, whenever `R_4, …, R_{q-2}`
are regular, `‖R_{q-1} ⋯ R_5 v_4‖² ≥ c η^{-(q-5)} v_4* F_4 v_4` except with probability `W^{-D}`,
where `c = C^{-(q-5)}` with `C` the constant of (G.2) [us:eq:relative-local-law]. At `η = υ`
the bound `υ ‖R_4‖ ≤ W^{3θ}` gives Lemma G.3 [nc:lem:buffer]; at `η = g²` it is the lower half of
(9.68) [us:eq:profile] at `j = q - 1`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Quadratic forms of `(1 + a R²)⁻¹` -/

open scoped MatrixOrder ComplexOrder in
/-- Inversion reverses the Loewner order on a strictly positive matrix: the real part of the
quadratic form of `B⁻¹` is at most that of `A⁻¹` when `A ≤ B`. -/
private lemma buffer_inv_le {W : ℕ} {A B : Matrix (Fin W) (Fin W) ℂ}
    (hA : IsStrictlyPositive A) (hAB : A ≤ B) (u : Fin W → ℂ) :
    (star u ⬝ᵥ (B⁻¹ *ᵥ u)).re ≤ (star u ⬝ᵥ (A⁻¹ *ᵥ u)).re := by
  have h := CStarAlgebra.ringInverse_le_ringInverse hAB hA
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse] at h
  have h2 := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg u
  rw [Matrix.sub_mulVec, dotProduct_sub] at h2
  have := (Complex.nonneg_iff.mp h2).1
  rw [Complex.sub_re] at this
  linarith

open scoped MatrixOrder ComplexOrder in
private lemma buffer_nonneg_smul {W : ℕ} (R : Matrix (Fin W) (Fin W) ℂ) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ ((a : ℂ)) • (star R * R) := by
  have h : (0 : Matrix (Fin W) (Fin W) ℂ) ≤ star R * R := star_mul_self_nonneg R
  exact smul_nonneg (show (0 : ℂ) ≤ (a : ℂ) from Complex.zero_le_real.mpr ha) h

open scoped MatrixOrder ComplexOrder in
private lemma buffer_isStrictlyPositive {W : ℕ} (R : Matrix (Fin W) (Fin W) ℂ) {a : ℝ}
    (ha : 0 ≤ a) : IsStrictlyPositive (1 + ((a : ℂ)) • (star R * R)) :=
  IsStrictlyPositive.add_nonneg isStrictlyPositive_one (buffer_nonneg_smul R ha)

open scoped MatrixOrder ComplexOrder in
/-- `Re u*(1 + t R*R)⁻¹ u` is decreasing in `t ≥ 0`. -/
private lemma buffer_inv_mono {W : ℕ} (R : Matrix (Fin W) (Fin W) ℂ) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (u : Fin W → ℂ) :
    (star u ⬝ᵥ ((1 + (t : ℂ) • (star R * R))⁻¹ *ᵥ u)).re ≤
      (star u ⬝ᵥ ((1 + (s : ℂ) • (star R * R))⁻¹ *ᵥ u)).re := by
  refine buffer_inv_le (buffer_isStrictlyPositive R hs) ?_ u
  rw [Matrix.le_iff]
  have : (1 + (t : ℂ) • (star R * R)) - (1 + (s : ℂ) • (star R * R)) =
      ((t - s : ℝ) : ℂ) • (star R * R) := by
    push_cast; rw [sub_smul]; abel
  rw [this]
  exact Matrix.nonneg_iff_posSemidef.mp (buffer_nonneg_smul R (by linarith))

open scoped MatrixOrder ComplexOrder in
/-- `Re u*(1 + a R*R)⁻¹ u ≥ (1 + a ‖R‖²)⁻¹ Re u*u`. -/
private lemma buffer_inv_lower {W : ℕ} (R : Matrix (Fin W) (Fin W) ℂ) {a : ℝ} (ha : 0 ≤ a)
    (u : Fin W → ℂ) :
    (1 + a * ‖R‖ ^ 2)⁻¹ * (star u ⬝ᵥ u).re ≤
      (star u ⬝ᵥ ((1 + (a : ℂ) • (star R * R))⁻¹ *ᵥ u)).re := by
  have hc : (0 : ℝ) < 1 + a * ‖R‖ ^ 2 := by positivity
  have hle : 1 + (a : ℂ) • (star R * R) ≤
      ((1 + a * ‖R‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    have h1 := CStarAlgebra.star_mul_le_algebraMap_norm_sq R
    have h2 : (a : ℂ) • (star R * R) ≤
        (a : ℂ) • algebraMap ℝ (Matrix (Fin W) (Fin W) ℂ) (‖R‖ ^ 2) :=
      smul_le_smul_of_nonneg_left h1 (Complex.zero_le_real.mpr ha)
    have h3 := add_le_add (le_refl (1 : Matrix (Fin W) (Fin W) ℂ)) h2
    refine h3.trans_eq ?_
    have e : algebraMap ℝ (Matrix (Fin W) (Fin W) ℂ) (‖R‖ ^ 2) =
        ((‖R‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
    rw [e, smul_smul]
    push_cast
    rw [add_smul, one_smul]
  have hinv := buffer_inv_le (buffer_isStrictlyPositive R ha) hle u
  have hci : (((1 + a * ‖R‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹ =
      (((1 + a * ‖R‖ ^ 2)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hc.ne', Complex.ofReal_one, one_smul]
  rw [hci, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.re_ofReal_mul] at hinv
  exact hinv

/-! ### The spectral identity of one step -/

private lemma buffer_form_mulVec {W : ℕ} (N F : Matrix (Fin W) (Fin W) ℂ) (u : Fin W → ℂ) :
    star (N *ᵥ u) ⬝ᵥ (F *ᵥ (N *ᵥ u)) = star u ⬝ᵥ ((Nᴴ * F * N) *ᵥ u) := by
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [Matrix.dotProduct_mulVec]

private lemma buffer_star_form {W : ℕ} (G : Matrix (Fin W) (Fin W) ℂ) (u : Fin W → ℂ) :
    star (star u ⬝ᵥ (G *ᵥ u)) = star u ⬝ᵥ (Gᴴ *ᵥ u) := by
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Matrix.conjTranspose_apply,
    Pi.star_apply, star_star]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `Γ⁻¹ (1 + c Γ⁻²)⁻¹ Γ⁻¹ = (Γ² + c)⁻¹` for invertible `Γ`. -/
private lemma buffer_inv_sandwich {W : ℕ} {Γ : Matrix (Fin W) (Fin W) ℂ} (hu : IsUnit Γ.det)
    (c : ℂ) :
    Γ⁻¹ * (1 + c • (Γ⁻¹ * Γ⁻¹))⁻¹ * Γ⁻¹ = (Γ * Γ + c • 1)⁻¹ := by
  have h1 : Γ * Γ⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : Γ⁻¹ * Γ = 1 := Matrix.nonsing_inv_mul _ hu
  have e : Γ * (1 + c • (Γ⁻¹ * Γ⁻¹)) * Γ = Γ * Γ + c • 1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
    congr 2
    calc Γ * (Γ⁻¹ * Γ⁻¹) * Γ = (Γ * Γ⁻¹) * (Γ⁻¹ * Γ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, h2, Matrix.mul_one]
  rw [← e, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]

private lemma buffer_sandwich_aux {W : ℕ} (Γ : Matrix (Fin W) (Fin W) ℂ) {c d : ℂ}
    (hcc : c * c = -d) :
    (Γ - c • (1 : Matrix (Fin W) (Fin W) ℂ)) * (Γ + c • 1) = Γ * Γ + d • 1 := by
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]
  rw [smul_sub, smul_smul, hcc, neg_smul]
  abel

/-- `G* G = ((A - E)² + η²)⁻¹` for `G = (A - E - iη)⁻¹` and Hermitian `A`. -/
private lemma buffer_ward_sandwich {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian)
    (E : ℝ) {η : ℝ} (hη : η ≠ 0) :
    (resolventMat A (E + η * Complex.I))ᴴ * resolventMat A (E + η * Complex.I) =
      ((A - (E : ℂ) • 1) * (A - (E : ℂ) • 1) + ((η : ℂ) ^ 2) • 1)⁻¹ := by
  have hz : (E + η * Complex.I : ℂ).im ≠ 0 := by simpa using hη
  have hKG := sub_smul_mul_resolventMat hA hz
  have hKH : (A - (E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
    have hE : IsSelfAdjoint (E : ℂ) := by rw [isSelfAdjoint_iff]; simp
    exact hA.sub (Matrix.isHermitian_one.smul hE)
  set Γ := A - (E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) with hΓ
  set c : ℂ := (η : ℂ) * Complex.I with hc
  have hK : A - ((E : ℂ) + c) • (1 : Matrix (Fin W) (Fin W) ℂ) = Γ - c • 1 := by
    rw [hΓ, add_smul]; abel
  have hKc : (Γ - c • (1 : Matrix (Fin W) (Fin W) ℂ))ᴴ = Γ + c • 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hKH.eq]
    have : star c = -c := by
      rw [hc, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [this, neg_smul, sub_neg_eq_add]
  have hKe : (Γ - c • (1 : Matrix (Fin W) (Fin W) ℂ)) * (Γ + c • 1) =
      Γ * Γ + ((η : ℂ) ^ 2) • 1 := by
    have hcc : c * c = -((η : ℂ) ^ 2) := by
      rw [hc]; ring_nf; rw [Complex.I_sq]; ring
    exact buffer_sandwich_aux Γ hcc
  have hz' : (E : ℂ) + (η : ℂ) * Complex.I = (E : ℂ) + c := rfl
  rw [hz'] at hKG ⊢
  rw [hK] at hKG
  have hu : IsUnit (Γ - c • (1 : Matrix (Fin W) (Fin W) ℂ)).det :=
    (Matrix.isUnit_det_of_right_inverse hKG)
  rw [resolventMat, hK, Matrix.conjTranspose_nonsing_inv, hKc, ← Matrix.mul_inv_rev, ← hKe]

/-- One step of the iteration: for Hermitian `A` and invertible `A - E`, the quantity
`Re u*(A-E)⁻¹ (1 + η² (A-E)⁻²)⁻¹ (A-E)⁻¹ u` equals `η⁻¹ Im u* (A - E - iη)⁻¹ u`. -/
private lemma buffer_step_identity {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian)
    (E : ℝ) {η : ℝ} (hη : η ≠ 0)
    (hu : IsUnit (A - (E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)).det) (u : Fin W → ℂ) :
    (star ((A - (E : ℂ) • 1)⁻¹ *ᵥ u) ⬝ᵥ ((1 + ((η : ℂ) ^ 2) • ((A - (E : ℂ) • 1)⁻¹ *
        (A - (E : ℂ) • 1)⁻¹))⁻¹ *ᵥ ((A - (E : ℂ) • 1)⁻¹ *ᵥ u))).re =
      η⁻¹ * (star u ⬝ᵥ (resolventMat A (E + η * Complex.I) *ᵥ u)).im := by
  have hKH : (A - (E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
    have hE : IsSelfAdjoint (E : ℂ) := by rw [isSelfAdjoint_iff]; simp
    exact hA.sub (Matrix.isHermitian_one.smul hE)
  have hz : (E + η * Complex.I : ℂ).im ≠ 0 := by simpa using hη
  rw [buffer_form_mulVec, hKH.inv.eq, buffer_inv_sandwich hu, ← buffer_ward_sandwich hA E hη,
    ward_matrix hA hz, Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul, dotProduct_sub,
    ← buffer_star_form]
  set w := star u ⬝ᵥ (resolventMat A (E + η * Complex.I) *ᵥ u) with hw
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  have h2 : w - star w = ((2 * w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [two_mul]
  have him : (E + η * Complex.I : ℂ).im = η := by simp
  rw [smul_eq_mul, h2, him]
  have : ((2 * (η : ℂ) * Complex.I)⁻¹ * (((2 * w.im : ℝ) : ℂ) * Complex.I)) =
      ((η⁻¹ * w.im : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [this, Complex.ofReal_re]


/-! ### Measurability and fresh-block data -/

/-- The matrix inverse `X ↦ X⁻¹ = det(X)⁻¹ adj(X)` is Borel. -/
private lemma buffer_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
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
private lemma buffer_measurable_sortedEig (n : ℕ) (j : Fin (Fintype.card (Fin n))) :
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
private lemma buffer_measurable_countIn (n : ℕ) {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable fun M : Matrix (Fin n) (Fin n) ℂ => countIn M J := by
  have hS : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | M.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hsum : Measurable fun M : Matrix (Fin n) (Fin n) ℂ =>
      ∑ j, if sortedEig M j ∈ J then 1 else 0 :=
    Finset.measurable_sum _ fun j _ => Measurable.ite
      (hJ.preimage (buffer_measurable_sortedEig n j)) measurable_const measurable_const
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

/-- Regularity (9.3) [us:eq:regular] is a Borel condition on the state. -/
private lemma buffer_measurableSet_regular (W : ℕ) (g : ℝ) :
    MeasurableSet {R : Matrix (Fin W) (Fin W) ℂ | IsRegularState W g R} := by
  have h1 : MeasurableSet {R : Matrix (Fin W) (Fin W) ℂ | R.IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  have h2 : MeasurableSet {R : Matrix (Fin W) (Fin W) ℂ | ‖R‖ ≤ (W : ℝ) ^ 3} :=
    measurableSet_le continuous_norm.measurable measurable_const
  have h3 : MeasurableSet {R : Matrix (Fin W) (Fin W) ℂ |
      (countIn (((g : ℂ) ^ 2) • R) {x | g < |x|} : ℝ) ≤ W * Real.sqrt g} := by
    have hm : Measurable fun R : Matrix (Fin W) (Fin W) ℂ =>
        countIn (((g : ℂ) ^ 2) • R) {x | g < |x|} :=
      (buffer_measurable_countIn W (measurableSet_lt measurable_const measurable_id.abs)).comp
        (measurable_id.const_smul ((g : ℂ) ^ 2))
    exact measurableSet_le ((measurable_from_top : Measurable fun m : ℕ => (m : ℝ)).comp hm)
      measurable_const
  exact h1.inter (h2.inter h3)

private lemma buffer_measurable_gueBlock (W L : ℕ) (a : Fin L) :
    Measurable fun ω : Ω W L => gueBlock W L ω a := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma buffer_measurable_block (W h : ℕ) (j : ℕ) :
    Measurable fun ω : Ω W h =>
      (if hj : j < h then gueBlock W h ω ⟨j, hj⟩ else 0 : Matrix (Fin W) (Fin W) ℂ) := by
  by_cases hj : j < h
  · simp only [hj, ↓reduceDIte]
    exact buffer_measurable_gueBlock W h ⟨j, hj⟩
  · simp only [hj, ↓reduceDIte]
    exact measurable_const

private lemma buffer_measurable_chain (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) : Measurable fun ω : Ω W h => ricChain W g E h R ω j := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    simp only [ricChain]
    refine buffer_measurable_inv.comp ?_
    exact ((buffer_measurable_block W h j).sub measurable_const).sub
      (ih.fun_const_smul ((g : ℂ) ^ 2))

private lemma buffer_measurable_prod (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) : Measurable fun ω : Ω W h => ricProd W g E h R ω j := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    simp only [ricProd]
    exact (buffer_measurable_chain W g E h R (j + 1)).mul ih

private lemma buffer_gueBlock_congr {W L : ℕ} {ω ω' : Ω W L} (b : Fin L)
    (hω : ∀ x y, ω (b, x, y) = ω' (b, x, y)) : gueBlock W L ω b = gueBlock W L ω' b := by
  unfold gueBlock
  simp only [hω]

/-- State `j` of the chain does not see block `a` when `j ≤ a`. -/
private lemma buffer_offBlock_chain (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ)
    (a : Fin h) (j : ℕ) (hj : j ≤ a.1) :
    OffBlock W h a (fun ω => ricChain W g E h R ω j) := by
  induction j with
  | zero => intro ω ω' _; rfl
  | succ j ih =>
    intro ω ω' hω
    have hjh : j < h := lt_of_lt_of_le (Nat.lt_of_succ_le hj) a.2.le
    simp only [ricChain, hjh, ↓reduceDIte]
    have hb : gueBlock W h ω ⟨j, hjh⟩ = gueBlock W h ω' ⟨j, hjh⟩ :=
      buffer_gueBlock_congr _ fun x y => hω (⟨j, hjh⟩, x, y) (by
        simp only [ne_eq, Fin.ext_iff]; omega)
    have h1 : ricChain W g E h R ω j = ricChain W g E h R ω' j := ih (by omega) ω ω' hω
    rw [hb, h1]

/-- Product `j` of the chain does not see block `a` when `j ≤ a`. -/
private lemma buffer_offBlock_prod (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ)
    (a : Fin h) (j : ℕ) (hj : j ≤ a.1) :
    OffBlock W h a (fun ω => ricProd W g E h R ω j) := by
  induction j with
  | zero => intro ω ω' _; rfl
  | succ j ih =>
    intro ω ω' hω
    simp only [ricProd]
    have h1 : ricChain W g E h R ω (j + 1) = ricChain W g E h R ω' (j + 1) :=
      buffer_offBlock_chain W g E h R a (j + 1) hj ω ω' hω
    have h2 : ricProd W g E h R ω j = ricProd W g E h R ω' j := ih (by omega) ω ω' hω
    rw [h1, h2]

private lemma buffer_measurable_form {X : Type*} [MeasurableSpace X] {W : ℕ}
    {N : X → Matrix (Fin W) (Fin W) ℂ} {w : X → (Fin W → ℂ)} (hN : Measurable N)
    (hw : Measurable w) :
    Measurable fun x => (star (w x) ⬝ᵥ (N x *ᵥ w x)).re := by
  refine Complex.measurable_re.comp ?_
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.mul ?_ (Finset.measurable_sum _ fun j _ => ?_)
  · exact (continuous_star.measurable).comp ((measurable_pi_apply i).comp hw)
  · exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hN))).mul
      ((measurable_pi_apply j).comp hw)

/-- The quadratic form `Re u*(1 + η² M²)⁻¹ u`. -/
private def bufQ (W : ℕ) (η : ℝ) (M : Matrix (Fin W) (Fin W) ℂ) (u : Fin W → ℂ) : ℝ :=
  (star u ⬝ᵥ ((1 + ((η : ℂ) ^ 2) • (M * M))⁻¹ *ᵥ u)).re

/-- The data `(V, (R, u))` for which one step of the iteration loses the factor `(C η)⁻¹`:
`bufQ η R u > (C η) bufQ η R' u'` with `R' = (V - E - g² R)⁻¹` and `u' = R' u`. -/
private def bufBad (W : ℕ) (g E η C : ℝ) :
    Set (Matrix (Fin W) (Fin W) ℂ × (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ))) :=
  {p | ¬ ((C * η)⁻¹ * bufQ W η p.2.1 p.2.2 ≤
    bufQ W η (p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2.1)⁻¹
      ((p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2.1)⁻¹ *ᵥ p.2.2))}

private lemma buffer_measurable_bufQ (W : ℕ) (η : ℝ) :
    Measurable fun q : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) => bufQ W η q.1 q.2 := by
  unfold bufQ
  refine buffer_measurable_form (X := Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ))
    (N := fun q => (1 + ((η : ℂ) ^ 2) • (q.1 * q.1))⁻¹) (w := fun q => q.2) ?_ measurable_snd
  refine buffer_measurable_inv.comp ?_
  exact (continuous_const.add
    ((continuous_fst.matrix_mul continuous_fst).fun_const_smul _)).measurable

private lemma buffer_measurable_bufQ' {X : Type*} [MeasurableSpace X] {W : ℕ} (η : ℝ)
    {M : X → Matrix (Fin W) (Fin W) ℂ} {u : X → (Fin W → ℂ)} (hM : Measurable M)
    (hu : Measurable u) : Measurable fun x => bufQ W η (M x) (u x) :=
  (buffer_measurable_bufQ W η).comp (hM.prodMk hu)

private lemma buffer_measurable_shift_inv (W : ℕ) (g E : ℝ) :
    Measurable fun p : Matrix (Fin W) (Fin W) ℂ × (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) =>
      (p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2.1)⁻¹ := by
  refine buffer_measurable_inv.comp ?_
  exact ((continuous_fst.sub continuous_const).sub
    (continuous_snd.fst.fun_const_smul _)).measurable

private lemma buffer_measurable_shift_vec (W : ℕ) (g E : ℝ) :
    Measurable fun p : Matrix (Fin W) (Fin W) ℂ × (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) =>
      (p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2.1)⁻¹ *ᵥ p.2.2 := by
  have hS := buffer_measurable_shift_inv W g E
  have hm : Measurable fun q : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) => q.1 *ᵥ q.2 :=
    (continuous_fst.matrix_mulVec continuous_snd).measurable
  exact hm.comp (hS.prodMk measurable_snd.snd)

private lemma buffer_measurableSet_bad (W : ℕ) (g E η C : ℝ) :
    MeasurableSet (bufBad W g E η C) := by
  have h1 : Measurable fun p : Matrix (Fin W) (Fin W) ℂ ×
      (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) => bufQ W η p.2.1 p.2.2 :=
    buffer_measurable_bufQ' η (measurable_snd.fst) (measurable_snd.snd)
  have h2 : Measurable fun p : Matrix (Fin W) (Fin W) ℂ ×
      (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) => bufQ W η
        (p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2.1)⁻¹
        ((p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2.1)⁻¹ *ᵥ p.2.2) :=
    buffer_measurable_bufQ' η (buffer_measurable_shift_inv W g E)
      (buffer_measurable_shift_vec W g E)
  have hset : bufBad W g E η C = {p : Matrix (Fin W) (Fin W) ℂ ×
      (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) | bufQ W η
        (p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2.1)⁻¹
        ((p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2.1)⁻¹ *ᵥ p.2.2) <
        (C * η)⁻¹ * bufQ W η p.2.1 p.2.2} :=
    Set.ext fun p => not_le
  rw [hset]
  exact measurableSet_lt h2 (h1.const_mul _)

/-! ### A shifted GUE matrix is almost surely invertible -/

/-- `A + V` is almost surely invertible for Hermitian `A` and `V` the `W × W` GUE matrix: by
the Wegner estimate `E #{eigenvalues in [-s, s]} ≤ C W s`. -/
private lemma buffer_sing_null {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) :
    μ W 1 {ω | ¬ IsUnit (A + gueMat W ω).det} = 0 := by
  obtain ⟨C₀, hC₀, hW⟩ := lintegral_countIn_add_gueMat_le
  have hbound : ∀ s : ℝ, 0 < s → μ W 1 {ω | ¬ IsUnit (A + gueMat W ω).det} ≤
      ENNReal.ofReal (C₀ * W * (s - -s)) := by
    intro s hs
    have hsub : {ω : Ω W 1 | ¬ IsUnit (A + gueMat W ω).det} ⊆
        {ω | ENNReal.ofReal 1 ≤ (countIn (A + gueMat W ω) (Set.Icc (-s) s) : ℝ≥0∞)} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have hH : (A + gueMat W ω).IsHermitian := hA.add (gueBlock_isHermitian W 1 ω 0)
      rw [isUnit_iff_ne_zero, not_not, hH.det_eq_prod_eigenvalues] at hω
      obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hω
      have hk0 : hH.eigenvalues k = 0 := by simpa using hk
      have hcnt : 1 ≤ countIn (A + gueMat W ω) (Set.Icc (-s) s) := by
        simp only [countIn, hH, ↓reduceDIte]
        exact Finset.card_pos.mpr ⟨k, by simp [hk0, hs.le]⟩
      rw [ENNReal.ofReal_one]
      exact_mod_cast hcnt
    have hmeas : Measurable fun ω : Ω W 1 =>
        (countIn (A + gueMat W ω) (Set.Icc (-s) s) : ℝ≥0∞) :=
      (measurable_from_top : Measurable fun m : ℕ => (m : ℝ≥0∞)).comp
        (measurable_countIn_add_gueMat W hA measurableSet_Icc)
    calc _ ≤ μ W 1 {ω | ENNReal.ofReal 1 ≤ (countIn (A + gueMat W ω) (Set.Icc (-s) s) : ℝ≥0∞)} :=
          measure_mono hsub
      _ ≤ (∫⁻ ω, (countIn (A + gueMat W ω) (Set.Icc (-s) s) : ℝ≥0∞) ∂(μ W 1)) /
            ENNReal.ofReal 1 :=
          meas_ge_le_lintegral_div hmeas.aemeasurable (by simp) ENNReal.ofReal_ne_top
      _ ≤ _ := by
          rw [ENNReal.ofReal_one, div_one]
          exact hW W A hA _ _
  by_contra hne
  have hfin : μ W 1 {ω | ¬ IsUnit (A + gueMat W ω).det} ≠ ∞ := measure_ne_top _ _
  set t : ℝ := (μ W 1 {ω | ¬ IsUnit (A + gueMat W ω).det}).toReal with ht
  have ht0 : 0 < t := ENNReal.toReal_pos hne hfin
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  set s : ℝ := t / (4 * C₀ * W + 1) with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have h1 := hbound s hs0
  have hs2 : 0 ≤ s - -s := by linarith
  have h2 : t ≤ C₀ * W * (s - -s) := ENNReal.toReal_le_of_le_ofReal (by positivity) h1
  have h3 : C₀ * W * (s - -s) < t := by
    rw [hs]
    have hd : 0 < 4 * C₀ * W + 1 := by positivity
    rw [show C₀ * W * (t / (4 * C₀ * W + 1) - -(t / (4 * C₀ * W + 1))) =
      2 * C₀ * W * t / (4 * C₀ * W + 1) by field_simp; ring, div_lt_iff₀ hd]
    have : 0 ≤ C₀ * W := by positivity
    nlinarith
  linarith


/-! ### One step in probability -/

/-- One step of the iteration at a fixed state `R` and vector `u`, given the lower bound of the
relative local law (G.2) [us:eq:relative-local-law] for the deformation `B = g² R`: with
probability at least `1 - b`, `V - E - g² R` is invertible and
`bufQ η R u ≤ C η bufQ η R' u'` for `R' = (V - E - g² R)⁻¹`, `u' = R' u`, as in (G.9)
[nc:eq:bufferstep]. -/
private lemma buffer_step_prob {W : ℕ} {g η E C : ℝ} (hg : 0 < g) (hgη : g ^ 2 ≤ η) (hη : 0 < η)
    (hC : 0 < C) {R : Matrix (Fin W) (Fin W) ℂ} (hR : R.IsHermitian) (u : Fin W → ℂ) {b : ℝ≥0∞}
    (hll : u ≠ 0 → μ W 1 {ω | ¬ (C⁻¹ * (star u ⬝ᵥ ((1 + (((g : ℂ) ^ 2) • R) *
          (((g : ℂ) ^ 2) • R))⁻¹ *ᵥ u)).re ≤
        (star u ⬝ᵥ (resolventMat (gueMat W ω - ((g : ℂ) ^ 2) • R) (E + η * Complex.I) *ᵥ
          u)).im)} ≤ b) :
    μ W 1 {ω | (gueMat W ω, (R, u)) ∈ bufBad W g E η C} ≤ b := by
  by_cases hu : u = 0
  · subst hu
    have hempty : {ω : Ω W 1 | (gueMat W ω, (R, (0 : Fin W → ℂ))) ∈ bufBad W g E η C} = ∅ := by
      ext ω
      simp [bufBad, bufQ]
    rw [hempty, measure_empty]
    exact zero_le
  have hE : IsSelfAdjoint (E : ℂ) := by rw [isSelfAdjoint_iff]; simp
  have hk : IsSelfAdjoint ((g : ℂ) ^ 2) := by rw [isSelfAdjoint_iff]; simp
  have hBH : (((g : ℂ) ^ 2) • R).IsHermitian := hR.smul hk
  have hA₀ : (-((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) + ((g : ℂ) ^ 2) • R)).IsHermitian :=
    ((Matrix.isHermitian_one.smul hE).add hBH).neg
  have hsub : {ω : Ω W 1 | (gueMat W ω, (R, u)) ∈ bufBad W g E η C} ⊆
      {ω | ¬ (C⁻¹ * (star u ⬝ᵥ ((1 + (((g : ℂ) ^ 2) • R) * (((g : ℂ) ^ 2) • R))⁻¹ *ᵥ u)).re ≤
        (star u ⬝ᵥ (resolventMat (gueMat W ω - ((g : ℂ) ^ 2) • R) (E + η * Complex.I) *ᵥ
          u)).im)} ∪
      {ω | ¬ IsUnit (-((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) + ((g : ℂ) ^ 2) • R) +
        gueMat W ω).det} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hnot
    obtain ⟨hlaw, hunit⟩ := hnot
    have hH : (gueMat W ω - ((g : ℂ) ^ 2) • R).IsHermitian :=
      (gueBlock_isHermitian W 1 ω 0).sub hBH
    have hΓ : gueMat W ω - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R =
        (gueMat W ω - ((g : ℂ) ^ 2) • R) - (E : ℂ) • 1 := by abel
    have hΓ' : -((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) + ((g : ℂ) ^ 2) • R) + gueMat W ω =
        (gueMat W ω - ((g : ℂ) ^ 2) • R) - (E : ℂ) • 1 := by abel
    rw [hΓ'] at hunit
    simp only [Set.mem_ofPred_eq, bufBad, hΓ] at hω
    apply hω
    unfold bufQ
    rw [buffer_step_identity hH E hη.ne' hunit u]
    have hBB : (((g : ℂ) ^ 2) • R) * (((g : ℂ) ^ 2) • R) =
        ((g ^ 4 : ℝ) : ℂ) • (star R * R) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.star_eq_conjTranspose, hR.eq]
      push_cast
      ring_nf
    have hη2 : ((η : ℂ) ^ 2) • (R * R) = ((η ^ 2 : ℝ) : ℂ) • (star R * R) := by
      rw [Matrix.star_eq_conjTranspose, hR.eq]
      push_cast
      rfl
    rw [hη2]
    have hmono := buffer_inv_mono R (s := g ^ 4) (t := η ^ 2) (by positivity)
      (by nlinarith [sq_nonneg (η - g ^ 2)]) u
    rw [hBB] at hlaw
    have hlaw' := mul_le_mul_of_nonneg_left hlaw (inv_nonneg.mpr hη.le)
    calc (C * η)⁻¹ * (star u ⬝ᵥ ((1 + ((η ^ 2 : ℝ) : ℂ) • (star R * R))⁻¹ *ᵥ u)).re
        ≤ (C * η)⁻¹ * (star u ⬝ᵥ ((1 + ((g ^ 4 : ℝ) : ℂ) • (star R * R))⁻¹ *ᵥ u)).re := by
          exact mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = η⁻¹ * (C⁻¹ * (star u ⬝ᵥ ((1 + ((g ^ 4 : ℝ) : ℂ) • (star R * R))⁻¹ *ᵥ u)).re) := by
          rw [mul_inv]; ring
      _ ≤ _ := hlaw'
  calc μ W 1 {ω | (gueMat W ω, (R, u)) ∈ bufBad W g E η C}
      ≤ μ W 1 ({ω | ¬ (C⁻¹ * (star u ⬝ᵥ ((1 + (((g : ℂ) ^ 2) • R) *
          (((g : ℂ) ^ 2) • R))⁻¹ *ᵥ u)).re ≤
        (star u ⬝ᵥ (resolventMat (gueMat W ω - ((g : ℂ) ^ 2) • R) (E + η * Complex.I) *ᵥ
          u)).im)} ∪
      {ω | ¬ IsUnit (-((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) + ((g : ℂ) ^ 2) • R) +
        gueMat W ω).det}) := measure_mono hsub
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ b + 0 := add_le_add (hll hu) (buffer_sing_null hA₀).le
    _ = b := add_zero b

/-- The bad event of step `j`: state `j` is regular and the step fails. -/
private lemma buffer_event_le {W h : ℕ} {g η E C : ℝ} (hg : 0 < g) (hgη : g ^ 2 ≤ η)
    (hη : 0 < η) (hC : 0 < C) (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) (j : Fin h)
    {b : ℝ≥0∞}
    (hll : ∀ (R' : Matrix (Fin W) (Fin W) ℂ) (u : Fin W → ℂ), IsRegularState W g R' → u ≠ 0 →
      μ W 1 {ω | ¬ (C⁻¹ * (star u ⬝ᵥ ((1 + (((g : ℂ) ^ 2) • R') * (((g : ℂ) ^ 2) • R'))⁻¹ *ᵥ
          u)).re ≤
        (star u ⬝ᵥ (resolventMat (gueMat W ω - ((g : ℂ) ^ 2) • R') (E + η * Complex.I) *ᵥ
          u)).im)} ≤ b) :
    μ W h {ω | IsRegularState W g (ricChain W g E h R ω j) ∧
      (gueBlock W h ω j, (ricChain W g E h R ω j, ricProd W g E h R ω j *ᵥ v)) ∈
        bufBad W g E η C} ≤ b := by
  have hDm : Measurable fun ω : Ω W h =>
      (ricChain W g E h R ω j, ricProd W g E h R ω j *ᵥ v) :=
    (buffer_measurable_chain W g E h R j).prodMk
      ((continuous_fst.matrix_mulVec continuous_snd).measurable.comp
        ((buffer_measurable_prod W g E h R j).prodMk measurable_const))
  have hDa : OffBlock W h j fun ω : Ω W h =>
      (ricChain W g E h R ω j, ricProd W g E h R ω j *ᵥ v) := by
    intro ω ω' hω
    have h1 : ricChain W g E h R ω j = ricChain W g E h R ω' j :=
      buffer_offBlock_chain W g E h R j j le_rfl ω ω' hω
    have h2 : ricProd W g E h R ω j = ricProd W g E h R ω' j :=
      buffer_offBlock_prod W g E h R j j le_rfl ω ω' hω
    simp only [h1, h2]
  have hSm : MeasurableSet {ω : Ω W h | IsRegularState W g (ricChain W g E h R ω j)} :=
    (buffer_measurable_chain W g E h R j) (buffer_measurableSet_regular W g)
  have hSa : OffBlock W h j fun ω : Ω W h =>
      ω ∈ {ω : Ω W h | IsRegularState W g (ricChain W g E h R ω j)} := by
    intro ω ω' hω
    have h1 : ricChain W g E h R ω j = ricChain W g E h R ω' j :=
      buffer_offBlock_chain W g E h R j j le_rfl ω ω' hω
    simp only [Set.mem_ofPred_eq, h1]
  have key := measure_gueBlock_fresh_le W h j hDm hDa hSm hSa
    (buffer_measurableSet_bad W g E η C) (b := b) (fun ω hω => by
      have hreg : IsRegularState W g (ricChain W g E h R ω j) := hω
      exact buffer_step_prob hg hgη hη hC hreg.1 _ (hll _ _ hreg))
  calc _ ≤ b * μ W h {ω : Ω W h | IsRegularState W g (ricChain W g E h R ω j)} := key
    _ ≤ b * 1 := mul_le_mul' le_rfl prob_le_one
    _ = b := mul_one b

/-! ### Assembly of the iteration -/

/-- The deformation class of Lemma G.1 [us:lem:local-law] is increasing in `ε`. -/
private lemma buffer_deformClass_mono {W : ℕ} {ε ε' : ℝ} {B : Matrix (Fin W) (Fin W) ℂ}
    (h : DeformClass ε B) (hε : ε ≤ ε') : DeformClass ε' B := by
  obtain ⟨hH, Bs, Bb, hsum, hs, hb⟩ := h
  exact ⟨hH, Bs, Bb, hsum, hs.trans hε,
    hb.trans (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _))⟩

private lemma buffer_l2Norm_sq {W : ℕ} (u : Fin W → ℂ) : l2Norm u ^ 2 = (star u ⬝ᵥ u).re := by
  unfold l2Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

/-- For Hermitian `M`, `Re u*(1 + η² M²)⁻¹ u` is the quadratic form of `(1 + η² M*M)⁻¹`. -/
private lemma buffer_bufQ_eq {W : ℕ} {M : Matrix (Fin W) (Fin W) ℂ} (hM : M.IsHermitian) (η : ℝ)
    (u : Fin W → ℂ) :
    bufQ W η M u = (star u ⬝ᵥ ((1 + ((η ^ 2 : ℝ) : ℂ) • (star M * M))⁻¹ *ᵥ u)).re := by
  unfold bufQ
  have hη2 : ((η : ℂ) ^ 2) • (M * M) = ((η ^ 2 : ℝ) : ℂ) • (star M * M) := by
    rw [Matrix.star_eq_conjTranspose, hM.eq]
    push_cast
    rfl
  rw [hη2]

open scoped MatrixOrder ComplexOrder in
/-- `Re u*(1 + η² M²)⁻¹ u ≤ ‖u‖²` for Hermitian `M`. -/
private lemma buffer_bufQ_le {W : ℕ} {M : Matrix (Fin W) (Fin W) ℂ} (hM : M.IsHermitian) (η : ℝ)
    (u : Fin W → ℂ) : bufQ W η M u ≤ l2Norm u ^ 2 := by
  have h := buffer_inv_mono M (s := 0) (t := η ^ 2) le_rfl (sq_nonneg η) u
  rw [buffer_bufQ_eq hM, buffer_l2Norm_sq]
  simpa using h

/-- `Re u*(1 + η² M²)⁻¹ u ≥ (1 + η² ‖M‖²)⁻¹ ‖u‖²` for Hermitian `M`. -/
private lemma buffer_bufQ_ge {W : ℕ} {M : Matrix (Fin W) (Fin W) ℂ} (hM : M.IsHermitian) (η : ℝ)
    (u : Fin W → ℂ) : (1 + η ^ 2 * ‖M‖ ^ 2)⁻¹ * l2Norm u ^ 2 ≤ bufQ W η M u := by
  rw [buffer_bufQ_eq hM, buffer_l2Norm_sq]
  exact buffer_inv_lower M (sq_nonneg η) u

/-- Along the chain, with every state regular and no step failing, `(C η)^{-j} bufQ η R v ≤
bufQ η R_j u_j` with `u_j = R_j ⋯ R_1 v`. -/
private lemma buffer_chain_lower {W h : ℕ} {g η E C : ℝ} (R : Matrix (Fin W) (Fin W) ℂ)
    (v : Fin W → ℂ) (ω : Ω W h)
    (hreg : ∀ j, j < h → IsRegularState W g (ricChain W g E h R ω j))
    (hgood : ∀ j : Fin h, ¬ (IsRegularState W g (ricChain W g E h R ω j) ∧
      (gueBlock W h ω j, (ricChain W g E h R ω j, ricProd W g E h R ω j *ᵥ v)) ∈
        bufBad W g E η C)) (hC : 0 ≤ (C * η)⁻¹) :
    ∀ j, j ≤ h → ((C * η)⁻¹) ^ j * bufQ W η R v ≤
      bufQ W η (ricChain W g E h R ω j) (ricProd W g E h R ω j *ᵥ v) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp [ricChain, ricProd, Matrix.one_mulVec]
  | succ j ih =>
    intro hj
    have hjh : j < h := hj
    have hb := not_and.mp (hgood ⟨j, hjh⟩) (hreg j hjh)
    simp only [bufBad, Set.mem_ofPred_eq, not_not] at hb
    have e1 : ricChain W g E h R ω (j + 1) = (gueBlock W h ω ⟨j, hjh⟩ - (E : ℂ) • 1 -
        ((g : ℂ) ^ 2) • ricChain W g E h R ω j)⁻¹ := by
      simp only [ricChain, hjh, ↓reduceDIte]
    have e2 : ricProd W g E h R ω (j + 1) *ᵥ v = (gueBlock W h ω ⟨j, hjh⟩ - (E : ℂ) • 1 -
        ((g : ℂ) ^ 2) • ricChain W g E h R ω j)⁻¹ *ᵥ (ricProd W g E h R ω j *ᵥ v) := by
      rw [ricProd, ← Matrix.mulVec_mulVec, e1]
    rw [e1, e2, pow_succ, mul_comm _ ((C * η)⁻¹), mul_assoc]
    exact (mul_le_mul_of_nonneg_left (ih hjh.le) hC).trans hb

/-- The iteration of Lemma G.3 [nc:lem:buffer] at a generic scale `η`: for `h ≥ 1` active blocks
there is `g₀ > 0` such that for every `δ > 0` there is `c > 0` such that for every `D > 0`,
`W ≥ W₀`, `0 < g ≤ g₀`, `g² ≤ η`, `W^{-1+δ} ≤ η ≤ C_*`, `|E| ≤ 2 - κ₀`, a regular `R` and `v ≠ 0`,
the event that `R_4, …, R_{q-2}` are regular and
`‖R_{q-1} ⋯ R_5 v‖² < c η^{-h} v* (1 + η² R²)⁻¹ v` has probability at most `W^{-D}`. -/
theorem buffer_lower_eta (κ₀ Cs : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hCs : 0 < Cs) (h : ℕ)
    (hh : 1 ≤ h) :
    ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ D : ℝ, 0 < D → ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W → ∀ (g η E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ), 0 < g →
        g ≤ g₀ → g ^ 2 ≤ η → (W : ℝ) ^ (-1 + δ) ≤ η → η ≤ Cs → |E| ≤ 2 - κ₀ →
        IsRegularState W g R → v ≠ 0 →
        μ W h {ω | (∀ j, j < h → IsRegularState W g (ricChain W g E h R ω j)) ∧
            l2Norm (ricProd W g E h R ω h *ᵥ v) ^ 2 <
              c * η ^ (-(h : ℝ)) * (star v ⬝ᵥ ((1 + ((η : ℂ) ^ 2) • (R * R))⁻¹ *ᵥ v)).re} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  obtain ⟨ε₀, CL, hε₀, hCL, hlaw⟩ := localLaw_rel κ₀ Cs hκ₀ hκ₀' hCs
  have hCL0 : 0 < CL := by linarith
  refine ⟨min 1 (ε₀ ^ 2), lt_min one_pos (by positivity), ?_⟩
  intro δ hδ
  refine ⟨(CL ^ h)⁻¹, by positivity, ?_⟩
  intro D hD
  obtain ⟨n₀, hn₀⟩ := hlaw ε₀ δ 1 (D + 1) hε₀ le_rfl hδ one_pos (by linarith)
  refine ⟨max n₀ (max h 1), ?_⟩
  intro W hW g η E R v hg hgg₀ hgη hηlow hηC hE hR hv
  have hWn : n₀ ≤ W := (le_max_left _ _).trans hW
  have hWh : h ≤ W := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hW1 : 1 ≤ W := ((le_max_right _ _).trans (le_max_right _ _)).trans hW
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hη0 : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hηlow
  have hg1 : g ≤ 1 := hgg₀.trans (min_le_left _ _)
  have hgε : Real.sqrt g ≤ ε₀ :=
    Real.sqrt_le_iff.mpr ⟨hε₀.le, hgg₀.trans (min_le_right _ _)⟩
  -- the lower bound of the relative local law at a regular state, with failure `W^{-D-1}`
  have hll : ∀ (R' : Matrix (Fin W) (Fin W) ℂ) (u : Fin W → ℂ), IsRegularState W g R' → u ≠ 0 →
      μ W 1 {ω | ¬ (CL⁻¹ * (star u ⬝ᵥ ((1 + (((g : ℂ) ^ 2) • R') * (((g : ℂ) ^ 2) • R'))⁻¹ *ᵥ
          u)).re ≤
        (star u ⬝ᵥ (resolventMat (gueMat W ω - ((g : ℂ) ^ 2) • R') (E + η * Complex.I) *ᵥ
          u)).im)} ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) := by
    intro R' u hR' hu
    have hdc : DeformClass ε₀ (((g : ℂ) ^ 2) • R') :=
      buffer_deformClass_mono (hR'.deformClass hg hg1) hgε
    have key := hn₀ W hWn (((g : ℂ) ^ 2) • R') E η hdc hE hηlow hηC u hu
    refine le_trans (measure_mono ?_) key
    intro ω hω hall
    exact hω hall.2.1
  -- on the complement of the `h` bad events the product grows by `(C η)⁻¹` at each step
  have hsub : {ω : Ω W h | (∀ j, j < h → IsRegularState W g (ricChain W g E h R ω j)) ∧
      l2Norm (ricProd W g E h R ω h *ᵥ v) ^ 2 <
        (CL ^ h)⁻¹ * η ^ (-(h : ℝ)) *
          (star v ⬝ᵥ ((1 + ((η : ℂ) ^ 2) • (R * R))⁻¹ *ᵥ v)).re} ⊆
      ⋃ j : Fin h, {ω : Ω W h | IsRegularState W g (ricChain W g E h R ω j) ∧
        (gueBlock W h ω j, (ricChain W g E h R ω j, ricProd W g E h R ω j *ᵥ v)) ∈
          bufBad W g E η CL} := by
    intro ω hω
    obtain ⟨hreg, hlt⟩ := hω
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] at hnot
    have hmain := buffer_chain_lower R v ω hreg hnot (by positivity) h le_rfl
    have hup := buffer_bufQ_le (ricChain_isHermitian (g := g) (E := E) hR.1 ω h) η
      (ricProd W g E h R ω h *ᵥ v)
    have hpow : ((CL * η)⁻¹) ^ h = (CL ^ h)⁻¹ * η ^ (-(h : ℝ)) := by
      rw [Real.rpow_neg hη0.le, Real.rpow_natCast, mul_inv, mul_pow, inv_pow, inv_pow]
    rw [hpow] at hmain
    exact absurd (hmain.trans hup) (not_le.mpr hlt)
  have hcard : ∀ j : Fin h, μ W h {ω : Ω W h | IsRegularState W g (ricChain W g E h R ω j) ∧
        (gueBlock W h ω j, (ricChain W g E h R ω j, ricProd W g E h R ω j *ᵥ v)) ∈
          bufBad W g E η CL} ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) :=
    fun j => buffer_event_le hg hgη hη0 hCL0 R v j hll
  have hsum : (h : ℝ≥0∞) * ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) ≤
      ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg h)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsplit : (W : ℝ) ^ (-(D + 1)) = (W : ℝ) ^ (-D) * (W : ℝ)⁻¹ := by
      rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
    have hhW : (h : ℝ) * (W : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hWpos]
      exact_mod_cast hWh
    have hp := Real.rpow_pos_of_pos hWpos (-D)
    rw [hsplit]
    nlinarith
  calc μ W h _ ≤ μ W h (⋃ j : Fin h, {ω : Ω W h | IsRegularState W g (ricChain W g E h R ω j) ∧
        (gueBlock W h ω j, (ricChain W g E h R ω j, ricProd W g E h R ω j *ᵥ v)) ∈
          bufBad W g E η CL}) := measure_mono hsub
    _ ≤ ∑ j : Fin h, μ W h {ω : Ω W h | IsRegularState W g (ricChain W g E h R ω j) ∧
        (gueBlock W h ω j, (ricChain W g E h R ω j, ricProd W g E h R ω j *ᵥ v)) ∈
          bufBad W g E η CL} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ j : Fin h, ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) := Finset.sum_le_sum fun j _ => hcard j
    _ = (h : ℝ≥0∞) * ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) := by simp
    _ ≤ _ := hsum

/-- Lemma G.3 [nc:lem:buffer], (9.69) [nc:eq:profile]: for `h = q - 5 ≥ 1` active blocks there
is `c > 0` such that for every `D > 0`, `W ≥ W₀`, `0 < g ≤ W^{-1/2+θ/2}`, `|E| ≤ 2 - κ₀`, a regular
`R` with `‖R‖ ≤ W^{1+θ}` and `v ≠ 0`, the event that `R_4, …, R_{q-2}` are regular and
`‖R_{q-1} ⋯ R_5 v‖ < c W^{(1-2θ)(q-5)/2} ‖v‖ W^{-3θ}` has probability at most `W^{-D}`. -/
theorem buffer_lower (κ₀ θ : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hθ : 0 < θ)
    (hθ' : θ ≤ 1 / 100) (h : ℕ) (hh : 1 ≤ h) :
    ∃ c : ℝ, 0 < c ∧ ∀ D : ℝ, 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ), 0 < g →
        g ≤ (W : ℝ) ^ (-1 / 2 + θ / 2) → |E| ≤ 2 - κ₀ → IsRegularState W g R →
        ‖R‖ ≤ (W : ℝ) ^ (1 + θ) → v ≠ 0 →
        μ W h {ω | (∀ j, j < h → IsRegularState W g (ricChain W g E h R ω j)) ∧
            l2Norm (ricProd W g E h R ω h *ᵥ v) <
              c * (W : ℝ) ^ ((1 - 2 * θ) * h / 2) * l2Norm v * (W : ℝ) ^ (-3 * θ)} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  obtain ⟨g₀, hg₀, hδ⟩ := buffer_lower_eta κ₀ 1 hκ₀ hκ₀' one_pos h hh
  obtain ⟨c, hc, hD⟩ := hδ (2 * θ) (by positivity)
  refine ⟨Real.sqrt (c / 2), by positivity, ?_⟩
  intro D hD0
  obtain ⟨W₁, hW₁⟩ := hD D hD0
  have hev : ∀ᶠ W : ℕ in Filter.atTop, (W : ℝ) ^ (-(1 / 4 : ℝ)) < g₀ :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hg₀)
  obtain ⟨W₂, hW₂⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max W₁ (max W₂ 1), ?_⟩
  intro W hW g E R v hg hgW hE hR hRW hv
  have hW1' : W₁ ≤ W := (le_max_left _ _).trans hW
  have hW2' : W₂ ≤ W := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hW1 : 1 ≤ W := ((le_max_right _ _).trans (le_max_right _ _)).trans hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  set η : ℝ := (W : ℝ) ^ (-1 + 2 * θ) with hη
  have hηpos : 0 < η := Real.rpow_pos_of_pos hWpos _
  have hgg₀ : g ≤ g₀ :=
    hgW.trans ((Real.rpow_le_rpow_of_exponent_le hWr (by linarith)).trans (hW₂ W hW2').le)
  have hgη : g ^ 2 ≤ η := by
    have h1 : g ^ 2 ≤ ((W : ℝ) ^ (-1 / 2 + θ / 2)) ^ 2 := pow_le_pow_left₀ hg.le hgW 2
    have h2 : ((W : ℝ) ^ (-1 / 2 + θ / 2)) ^ 2 = (W : ℝ) ^ (-1 + θ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]
      congr 1
      push_cast
      ring
    exact h1.trans (h2.le.trans (Real.rpow_le_rpow_of_exponent_le hWr (by linarith)))
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith)
  refine le_trans (measure_mono ?_) (hW₁ W hW1' g η E R v hg hgg₀ hgη le_rfl hη1 hE hR hv)
  intro ω hω
  obtain ⟨hreg, hlt⟩ := hω
  refine ⟨hreg, ?_⟩
  set X : ℝ := (W : ℝ) ^ (3 * θ) with hX
  set Y : ℝ := (W : ℝ) ^ ((1 - 2 * θ) * h / 2) with hY
  have hX1 : 1 ≤ X := Real.one_le_rpow hWr (by linarith)
  have hXpos : 0 < X := by linarith
  have hW3 : (W : ℝ) ^ (-3 * θ) = X⁻¹ := by
    rw [hX, ← Real.rpow_neg hWpos.le]
    congr 1
    ring
  have hY0 : 0 ≤ Y := (Real.rpow_pos_of_pos hWpos _).le
  have hηh : η ^ (-(h : ℝ)) = Y ^ 2 := by
    rw [hη, ← Real.rpow_mul hWpos.le, hY, ← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]
    congr 1
    push_cast
    ring
  have hηR : η * ‖R‖ ≤ X := by
    calc η * ‖R‖ ≤ (W : ℝ) ^ (-1 + 2 * θ) * (W : ℝ) ^ (1 + θ) :=
          mul_le_mul_of_nonneg_left hRW hηpos.le
      _ = X := by
          rw [← Real.rpow_add hWpos, hX]
          congr 1
          ring
  have hη2R : η ^ 2 * ‖R‖ ^ 2 ≤ X ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hηR 2
    rwa [mul_pow] at this
  have hbq : (2 * X ^ 2)⁻¹ * l2Norm v ^ 2 ≤ bufQ W η R v := by
    refine le_trans ?_ (buffer_bufQ_ge hR.1 η v)
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith [hX1]
  rw [hW3] at hlt
  have hT0 : 0 ≤ Real.sqrt (c / 2) * Y * l2Norm v * X⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hY0) (Real.sqrt_nonneg _))
      (inv_nonneg.mpr hXpos.le)
  have h1 := pow_lt_pow_left₀ hlt (Real.sqrt_nonneg _) (two_ne_zero)
  have h2 : (Real.sqrt (c / 2) * Y * l2Norm v * X⁻¹) ^ 2 =
      c / 2 * Y ^ 2 * l2Norm v ^ 2 * (X⁻¹) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  change l2Norm (ricProd W g E h R ω h *ᵥ v) ^ 2 < c * η ^ (-(h : ℝ)) * bufQ W η R v
  rw [hηh]
  calc l2Norm (ricProd W g E h R ω h *ᵥ v) ^ 2
      < (Real.sqrt (c / 2) * Y * l2Norm v * X⁻¹) ^ 2 := h1
    _ = c * Y ^ 2 * ((2 * X ^ 2)⁻¹ * l2Norm v ^ 2) := by
        rw [h2]
        field_simp
    _ ≤ c * Y ^ 2 * bufQ W η R v := mul_le_mul_of_nonneg_left hbq (by positivity)

end LSBA
