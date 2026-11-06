import LSBA.Upper.PrepMeasure
import LSBA.Upper.RegularState

/-!
# The prepared estimates

The good sets of prepared data `(R_4, v_4)` in Lemma 9.1 [su:lem:preparation], and the bound in
the critical window. In regime (i), with `P = 1_{[-W^{ε/800}, W^{ε/800}]}(g² R_4)` of (9.4)
[su:eq:source-projection]: `R_4` is regular (9.3) [us:eq:regular] (so `‖R_4‖ ≤ W³`),
`‖P v_4‖ ≥ W^{-10} ‖v_4‖` and `b_4 = v_4*(1 + g⁴R_4²)⁻¹v_4 ≤ C ‖P v_4‖²` (9.5) [su:eq:prep],
and `#{|g² r| > W^{-ε/800}} ≤ W g² W^{ε/400}` (9.6) [su:eq:prepared-large-rank]. In regime (ii):
`R_4` is regular, `‖R_4‖ ≤ W^{1+θ}`, `#{|g² r| > W^{-θ}} ≤ W^{3θ}` and `g² ‖R_4‖ ≤ W^{2θ}` (9.7)
[nc:eq:prepared]. Both sets are Borel.

In the critical window the four preparation steps enter the chart and the prepared data satisfy
(9.7) [nc:eq:prepared] except with probability `C W^{-θ}`, uniformly in the flag and the energy: the
inverse-norm
bound of (9.58) [us:eq:wegner] at `t = W^θ` gives `‖R_4‖ ≤ W^{1+θ}`, the count of (9.58)
[us:eq:wegner] with
`W g² ≤ W^θ` and Markov's inequality give the rank bound, and `g² ≤ W^{-1+θ}` gives
`g² ‖R_4‖ ≤ W^{2θ}`. The lower bound `c_* W^{-1/2} ≤ g` of (8.37) [eq:critical-window] is not
used.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The prepared estimates of Lemma 9.1 [su:lem:preparation] in regime (i) at `(R_4, v_4)`:
`R_4` regular (9.3) [us:eq:regular]; with `P = 1_{[-W^{ε/800}, W^{ε/800}]}(g² R_4)` of (9.4)
[su:eq:source-projection], `W^{-10} ‖v_4‖ ≤ ‖P v_4‖` and `v_4*(1 + g⁴R_4²)⁻¹v_4 ≤ C ‖P v_4‖²`
(9.5) [su:eq:prep]; and `#{|g² r| > W^{-ε/800}} ≤ W g² W^{ε/400}` (9.6)
[su:eq:prepared-large-rank]. -/
def PrepGoodWeak (W : ℕ) (g ε C : ℝ) : Set (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) :=
  {p | IsRegularState W g p.1 ∧
    (W : ℝ) ^ (-10 : ℝ) * l2Norm p.2 ≤
      l2Norm (specProj (((g : ℂ) ^ 2) • p.1)
        (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800))) *ᵥ p.2) ∧
    (star p.2 ⬝ᵥ ((1 + ((g : ℂ) ^ 4) • (p.1 * p.1))⁻¹ *ᵥ p.2)).re ≤
      C * l2Norm (specProj (((g : ℂ) ^ 2) • p.1)
        (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800))) *ᵥ p.2) ^ 2 ∧
    (countIn (((g : ℂ) ^ 2) • p.1) {y | (W : ℝ) ^ (-(ε / 800)) < |y|} : ℝ) ≤
      W * g ^ 2 * (W : ℝ) ^ (ε / 400)}

/-- The prepared estimates of Lemma 9.1 [su:lem:preparation] in regime (ii) at `R_4`: `R_4`
regular (9.3) [us:eq:regular], `‖R_4‖ ≤ W^{1+θ}`, `#{|g² r| > W^{-θ}} ≤ W^{3θ}` and
`g² ‖R_4‖ ≤ W^{2θ}` (9.7) [nc:eq:prepared]; the normal is not constrained. -/
def PrepGoodCrit (W : ℕ) (g θ : ℝ) : Set (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) :=
  {p | IsRegularState W g p.1 ∧ ‖p.1‖ ≤ (W : ℝ) ^ (1 + θ) ∧
    (countIn (((g : ℂ) ^ 2) • p.1) {y | (W : ℝ) ^ (-θ) < |y|} : ℝ) ≤ (W : ℝ) ^ (3 * θ) ∧
    g ^ 2 * ‖p.1‖ ≤ (W : ℝ) ^ (2 * θ)}

/-- The matrix inverse `X ↦ X⁻¹ = det(X)⁻¹ adj(X)` is Borel. -/
private lemma prepGood_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
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
private lemma prepGood_measurable_sortedEig (n : ℕ) (j : Fin (Fintype.card (Fin n))) :
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
private lemma prepGood_measurable_countIn (n : ℕ) {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable fun M : Matrix (Fin n) (Fin n) ℂ => countIn M J := by
  have hS : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | M.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hsum : Measurable fun M : Matrix (Fin n) (Fin n) ℂ =>
      ∑ j, if sortedEig M j ∈ J then 1 else 0 :=
    Finset.measurable_sum _ fun j _ => Measurable.ite
      (hJ.preimage (prepGood_measurable_sortedEig n j)) measurable_const measurable_const
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

/-- `{R : countIn (c R) J ≤ b}` is Borel. -/
private lemma prepGood_measurableSet_count_le {W : ℕ} (c : ℂ) {J : Set ℝ} (hJ : MeasurableSet J)
    (b : ℝ) :
    MeasurableSet {R : Matrix (Fin W) (Fin W) ℂ | (countIn (c • R) J : ℝ) ≤ b} := by
  have hm : Measurable fun R : Matrix (Fin W) (Fin W) ℂ => countIn (c • R) J :=
    (prepGood_measurable_countIn W hJ).comp (measurable_id.const_smul c)
  exact measurableSet_le ((measurable_from_top : Measurable fun m : ℕ => (m : ℝ)).comp hm)
    measurable_const

/-- Regular states (9.3) [us:eq:regular] form a Borel set. -/
private lemma prepGood_measurableSet_regular (W : ℕ) (g : ℝ) :
    MeasurableSet {R : Matrix (Fin W) (Fin W) ℂ | IsRegularState W g R} := by
  have hS : IsClosed {M : Matrix (Fin W) (Fin W) ℂ | M.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hn : MeasurableSet {R : Matrix (Fin W) (Fin W) ℂ | ‖R‖ ≤ (W : ℝ) ^ 3} :=
    measurableSet_le continuous_norm.measurable measurable_const
  have hc := prepGood_measurableSet_count_le (W := W) ((g : ℂ) ^ 2)
    (measurableSet_lt measurable_const measurable_id.abs : MeasurableSet {x : ℝ | g < |x|})
    (W * Real.sqrt g)
  exact hS.measurableSet.inter (hn.inter hc)

/-- The Euclidean norm of a vector is continuous. -/
private lemma prepGood_continuous_l2Norm {W : ℕ} :
    Continuous fun v : Fin W → ℂ => l2Norm v := by
  unfold l2Norm
  fun_prop

/-- `(A, v) ↦ A v` is measurable for measurable `A` and `v`. -/
private lemma prepGood_measurable_mulVec {W : ℕ} {α : Type*} [MeasurableSpace α]
    {A : α → Matrix (Fin W) (Fin W) ℂ} {v : α → Fin W → ℂ} (hA : Measurable A)
    (hv : Measurable v) : Measurable fun a => A a *ᵥ v a := by
  have hc : Continuous fun p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) => p.1 *ᵥ p.2 :=
    continuous_fst.matrix_mulVec continuous_snd
  exact hc.measurable.comp (hA.prodMk hv)

/-- `(R, v) ↦ Re (v* R v)` is continuous. -/
private lemma prepGood_continuous_form {W : ℕ} :
    Continuous fun p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) =>
      (star p.2 ⬝ᵥ (p.1 *ᵥ p.2)).re := by
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

/-- The two sets of prepared data are Borel. -/
theorem measurableSet_prepGood (W : ℕ) (g ε C θ : ℝ) :
    MeasurableSet (PrepGoodWeak W g ε C) ∧ MeasurableSet (PrepGoodCrit W g θ) := by
  have hreg : MeasurableSet {p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) |
      IsRegularState W g p.1} := measurable_fst (prepGood_measurableSet_regular W g)
  constructor
  · set S : Set ℝ := Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800)) with hS
    have hP : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) =>
        l2Norm (specProj (((g : ℂ) ^ 2) • p.1) S *ᵥ p.2) :=
      prepGood_continuous_l2Norm.measurable.comp (prepGood_measurable_mulVec
        ((measurable_specProj isClosed_Icc).comp
          (measurable_fst.const_smul ((g : ℂ) ^ 2) :
            Measurable fun p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) => ((g : ℂ) ^ 2) • p.1))
        measurable_snd)
    have h2 : MeasurableSet {p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) |
        (W : ℝ) ^ (-10 : ℝ) * l2Norm p.2 ≤ l2Norm (specProj (((g : ℂ) ^ 2) • p.1) S *ᵥ p.2)} :=
      measurableSet_le
        (measurable_const.mul (prepGood_continuous_l2Norm.measurable.comp measurable_snd)) hP
    have h3 : MeasurableSet {p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) |
        (star p.2 ⬝ᵥ ((1 + ((g : ℂ) ^ 4) • (p.1 * p.1))⁻¹ *ᵥ p.2)).re ≤
          C * l2Norm (specProj (((g : ℂ) ^ 2) • p.1) S *ᵥ p.2) ^ 2} := by
      have hM : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) =>
          (1 + ((g : ℂ) ^ 4) • (p.1 * p.1))⁻¹ :=
        prepGood_measurable_inv.comp
          (Continuous.measurable (by fun_prop : Continuous fun p : Matrix (Fin W) (Fin W) ℂ ×
            (Fin W → ℂ) => 1 + ((g : ℂ) ^ 4) • (p.1 * p.1)))
      have hF : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) =>
          (star p.2 ⬝ᵥ ((1 + ((g : ℂ) ^ 4) • (p.1 * p.1))⁻¹ *ᵥ p.2)).re :=
        by
          have := (prepGood_continuous_form (W := W)).measurable.comp (hM.prodMk measurable_snd)
          exact this
      have hG : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) =>
          C * l2Norm (specProj (((g : ℂ) ^ 2) • p.1) S *ᵥ p.2) ^ 2 :=
        measurable_const.mul (hP.pow_const 2)
      exact measurableSet_le hF hG
    have h4 : MeasurableSet {p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) |
        (countIn (((g : ℂ) ^ 2) • p.1) {y | (W : ℝ) ^ (-(ε / 800)) < |y|} : ℝ) ≤
          W * g ^ 2 * (W : ℝ) ^ (ε / 400)} :=
      measurable_fst (prepGood_measurableSet_count_le ((g : ℂ) ^ 2)
        (measurableSet_lt measurable_const measurable_id.abs) _)
    exact hreg.inter (h2.inter (h3.inter h4))
  · have h2 : MeasurableSet {p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) |
        ‖p.1‖ ≤ (W : ℝ) ^ (1 + θ)} :=
      measurableSet_le (continuous_norm.measurable.comp measurable_fst) measurable_const
    have h3 : MeasurableSet {p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) |
        (countIn (((g : ℂ) ^ 2) • p.1) {y | (W : ℝ) ^ (-θ) < |y|} : ℝ) ≤ (W : ℝ) ^ (3 * θ)} :=
      measurable_fst (prepGood_measurableSet_count_le ((g : ℂ) ^ 2)
        (measurableSet_lt measurable_const measurable_id.abs) _)
    have h4 : MeasurableSet {p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) |
        g ^ 2 * ‖p.1‖ ≤ (W : ℝ) ^ (2 * θ)} :=
      measurableSet_le (measurable_const.mul (continuous_norm.measurable.comp measurable_fst))
        measurable_const
    exact hreg.inter (h2.inter (h3.inter h4))

/-- Block `k` of the sample, as a `W × W` matrix, is measurable in the sample. -/
private lemma prepGood_measurable_gueBlock (W q : ℕ) (k : Fin q) :
    Measurable fun ω : Ω W q => gueBlock W q ω k := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The input blocks `V_{k+1}` are measurable in the sample. -/
private lemma prepGood_measurable_blockSeq (W q k : ℕ) :
    Measurable fun ω : Ω W q => blockSeq W q ω k := by
  by_cases h : k < q
  · have : (fun ω : Ω W q => blockSeq W q ω k) = fun ω => gueBlock W q ω ⟨k, h⟩ := by
      funext ω
      simp only [blockSeq, h, ↓reduceDIte]
    rw [this]
    exact prepGood_measurable_gueBlock W q ⟨k, h⟩
  · have : (fun ω : Ω W q => blockSeq W q ω k) = fun _ => 0 := by
      funext ω
      simp only [blockSeq, h, ↓reduceDIte]
    rw [this]
    exact measurable_const

/-- `V ↦ T(V)` is continuous on `W × W` matrices. -/
private lemma prepGood_continuous_transferMat {W : ℕ} (g : ℝ) (z : ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => transferMat g z V := by
  refine continuous_matrix fun i j => ?_
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  simp only [transferMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
    smul_eq_mul]
  fun_prop

/-- `X_1` and `Y_1` are measurable in the sample. -/
private lemma prepGood_measurable_topBot {W q : ℕ} (g E : ℝ) (x : IsoFlag W) :
    Measurable (prepTop W g E q x) ∧ Measurable (prepBot W g E q x) := by
  have hb := prepGood_measurable_blockSeq W q 0
  have hT := prepGood_continuous_transferMat (W := W) g ((max 1 g * E / g : ℝ) : ℂ)
  have hc : Continuous fun V : Matrix (Fin W) (Fin W) ℂ =>
      transferMat g ((max 1 g * E / g : ℝ) : ℂ) V * 1 * freeConj W 0 * prepFrame x :=
    ((hT.matrix_mul continuous_const).matrix_mul continuous_const).matrix_mul continuous_const
  have hc' : ∀ i : Fin 2, Measurable fun V : Matrix (Fin W) (Fin W) ℂ => (Matrix.of fun α β =>
      (transferMat g ((max 1 g * E / g : ℝ) : ℂ) V * 1 * freeConj W 0 * prepFrame x :
        Matrix (Fin 2 × Fin W) (Fin W) ℂ) (i, α) β : Matrix (Fin W) (Fin W) ℂ) :=
    fun i => (continuous_matrix fun α β => hc.matrix_elem (i, α) β).measurable
  exact ⟨(hc' 0).comp hb, (hc' 1).comp hb⟩

/-- `R_j` is measurable in the sample. -/
private lemma prepGood_measurable_R {W q : ℕ} (g E : ℝ) (x : IsoFlag W) (j : ℕ) :
    Measurable fun ω : Ω W q => prepR W g E q x ω j := by
  induction j with
  | zero => exact measurable_const
  | succ n ih =>
    cases n with
    | zero =>
      obtain ⟨hT, hB⟩ := prepGood_measurable_topBot (q := q) g E x
      have hc : Continuous fun p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
          -((g : ℂ)⁻¹ • (p.1 * p.2)) := by fun_prop
      have := hc.measurable.comp (hB.prodMk (prepGood_measurable_inv.comp hT))
      exact this
    | succ m =>
      have hc : Continuous fun p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
          p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2 := by fun_prop
      have := prepGood_measurable_inv.comp
        (hc.measurable.comp ((prepGood_measurable_blockSeq W q (m + 1)).prodMk ih))
      exact this

/-- Block `a` of two samples that agree on the coordinates of block `a` coincide. -/
private lemma prepGood_gueBlock_congr {W q : ℕ} {ω ω' : Ω W q} (a : Fin q)
    (h : ∀ α β, ω (a, α, β) = ω' (a, α, β)) : gueBlock W q ω a = gueBlock W q ω' a := by
  unfold gueBlock
  simp only [h]

/-- `R_j` depends only on the blocks `V_1, …, V_j`. -/
private lemma prepGood_R_congr {W q : ℕ} (g E : ℝ) (x : IsoFlag W) {ω ω' : Ω W q} {n : ℕ}
    (h : ∀ k, k < n → blockSeq W q ω k = blockSeq W q ω' k) :
    ∀ j, j ≤ n → prepR W g E q x ω j = prepR W g E q x ω' j := by
  have htop : 0 < n → prepTop W g E q x ω = prepTop W g E q x ω' ∧
      prepBot W g E q x ω = prepBot W g E q x ω' := fun hn => by
    have h0 := h 0 hn
    constructor <;> simp only [prepTop, prepBot, transferProd, h0]
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    cases j with
    | zero =>
      have := htop (by omega)
      change -((g : ℂ)⁻¹ • (prepBot W g E q x ω * (prepTop W g E q x ω)⁻¹)) =
        -((g : ℂ)⁻¹ • (prepBot W g E q x ω' * (prepTop W g E q x ω')⁻¹))
      rw [this.1, this.2]
    | succ m =>
      change (blockSeq W q ω (m + 1) - (E : ℂ) • 1 -
          ((g : ℂ) ^ 2) • prepR W g E q x ω (m + 1))⁻¹ =
        (blockSeq W q ω' (m + 1) - (E : ℂ) • 1 -
          ((g : ℂ) ^ 2) • prepR W g E q x ω' (m + 1))⁻¹
      rw [h (m + 1) (by omega), ih (by omega)]


/-- Where the four preparation steps are invertible, `R_3` is Hermitian: `R_4 = M_3⁻¹` is
Hermitian (prepared chart), so `M_3 = V_4 - E - g² R_3` is Hermitian, and so is `R_3`. -/
private lemma prepGood_R3_herm {W q : ℕ} [NeZero W] {g E : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (hq : 4 ≤ q) (x : IsoFlag W) {ω : Ω W q} (hP : PrepOK W g E q x ω) :
    (prepR W g E q x ω 3).IsHermitian := by
  have hq3 : 3 < q := by omega
  have hb3 : blockSeq W q ω 3 = gueBlock W q ω ⟨3, hq3⟩ := by
    simp only [blockSeq, hq3, ↓reduceDIte]
  have hR4 := (isPrepChart_of_prepOK hg hg1 x hP).1
  have hunit := hP.2 3 (by norm_num) le_rfl
  have hR4eq : prepR W g E q x ω 4 = (blockSeq W q ω 3 - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • prepR W g E q x ω 3)⁻¹ := rfl
  have hMH : (blockSeq W q ω 3 - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • prepR W g E q x ω 3).IsHermitian := by
    have h := hR4.inv
    rw [hR4eq, Matrix.nonsing_inv_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hunit)] at h
    exact h
  have hE : IsSelfAdjoint (E : ℂ) := by rw [isSelfAdjoint_iff]; simp
  have hk : IsSelfAdjoint ((g : ℂ) ^ 2) := by rw [isSelfAdjoint_iff]; simp
  have hk' : IsSelfAdjoint (((g : ℂ) ^ 2)⁻¹) := by rw [isSelfAdjoint_iff]; simp
  have hV : (blockSeq W q ω 3 - (E : ℂ) • 1).IsHermitian := by
    rw [hb3]
    exact (gueBlock_isHermitian W q ω _).sub (Matrix.isHermitian_one.smul hE)
  have hgR : (((g : ℂ) ^ 2) • prepR W g E q x ω 3).IsHermitian := by
    have := hV.sub hMH
    rwa [sub_sub_cancel] at this
  have hg2 : ((g : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hg.ne')
  have := hgR.smul hk'
  rwa [inv_smul_smul₀ hg2] at this

/-- Lemma 9.1 [su:lem:preparation] in regime (ii), (9.7) [nc:eq:prepared]: for `0 < θ ≤ 1/100`
there are `C, W₀` such that for `W ≥ W₀`, `q ≥ 4`, `0 < g ≤ W^{-1/2+θ/2}`, every energy and every
flag, the four preparation steps enter the chart and `(R_4, v_4) ∈ PrepGoodCrit` except with
probability `C W^{-θ}`. -/
theorem preparation_crit (θ : ℝ) (hθ : 0 < θ) (hθ' : θ ≤ 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℕ, ∀ W q : ℕ, W₀ ≤ W → 4 ≤ q →
      ∀ (g E : ℝ) (x : IsoFlag W), 0 < g → g ≤ (W : ℝ) ^ (-1 / 2 + θ / 2) →
        μ W q {ω | ¬ (PrepOK W g E q x ω ∧
            (prepR W g E q x ω 4, prepV W g E q x ω 4) ∈ PrepGoodCrit W g θ)} ≤
          ENNReal.ofReal (C * (W : ℝ) ^ (-θ)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := fresh_inv_norm_tail
  obtain ⟨C₂, hC₂, h₂⟩ := fresh_inv_count_tail
  obtain ⟨C₃, hC₃, h₃⟩ := fresh_regular
  refine ⟨C₁ + 2 * C₂ + 2 * C₃, by positivity, 1, fun W q hW hq g E x hg hgW => ?_⟩
  have : NeZero W := ⟨by omega⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hq3 : 3 < q := by omega
  set a : Fin q := ⟨3, hq3⟩ with ha
  have hg1 : g ≤ 1 :=
    hgW.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
  -- the state before block `a`, made Hermitian everywhere
  set R3 : Ω W q → Matrix (Fin W) (Fin W) ℂ := fun ω => prepR W g E q x ω 3 with hR3
  set Rp : Ω W q → Matrix (Fin W) (Fin W) ℂ :=
    fun ω => if (R3 ω).IsHermitian then R3 ω else 0 with hRp
  have hR3m : Measurable R3 := prepGood_measurable_R g E x 3
  have hHset : MeasurableSet {ω : Ω W q | (R3 ω).IsHermitian} :=
    hR3m (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  have hRm : Measurable Rp := Measurable.ite hHset hR3m measurable_const
  have hRh : ∀ ω, (Rp ω).IsHermitian := fun ω => by
    by_cases h : (R3 ω).IsHermitian
    · simp [hRp, h]
    · simp [hRp, h]
  have hRa : OffBlock W q a Rp := by
    intro ω ω' h
    have hcongr : R3 ω = R3 ω' := by
      refine prepGood_R_congr g E x (n := 3) (fun k hk => ?_) 3 le_rfl
      have hkq : k < q := by omega
      simp only [blockSeq, hkq, ↓reduceDIte]
      refine prepGood_gueBlock_congr ⟨k, hkq⟩ fun α β => h (⟨k, hkq⟩, α, β) ?_
      intro hka
      have := congrArg Fin.val hka
      simp only [ha] at this
      omega
    simp only [hRp, hcongr]
  -- the outgoing state
  have hRp_eq : ∀ ω, PrepOK W g E q x ω → Rp ω = R3 ω := fun ω hP => by
    have hH : (R3 ω).IsHermitian := prepGood_R3_herm hg hg1 hq x hP
    simp [hRp, hH]
  have hR4 : ∀ ω, PrepOK W g E q x ω → prepR W g E q x ω 4 =
      (gueBlock W q ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹ := fun ω hP => by
    rw [hRp_eq ω hP]
    have hb3 : blockSeq W q ω 3 = gueBlock W q ω a := by
      simp only [blockSeq, hq3, ↓reduceDIte, ha]
    change (blockSeq W q ω 3 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • prepR W g E q x ω 3)⁻¹ = _
    rw [hb3]
  -- exponent arithmetic
  have hg2 : g ^ 2 ≤ (W : ℝ) ^ (-1 + θ) := by
    calc g ^ 2 = g * g := sq g
      _ ≤ (W : ℝ) ^ (-1 / 2 + θ / 2) * (W : ℝ) ^ (-1 / 2 + θ / 2) :=
          mul_le_mul hgW hgW hg.le (by positivity)
      _ = (W : ℝ) ^ (-1 + θ) := by
          rw [← Real.rpow_add hW0]; congr 1; ring
  have hsq : Real.sqrt g ≤ (W : ℝ) ^ (-θ) := by
    rw [Real.sqrt_le_left (by positivity)]
    calc g ≤ (W : ℝ) ^ (-1 / 2 + θ / 2) := hgW
      _ ≤ (W : ℝ) ^ (-θ + -θ) :=
          Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      _ = ((W : ℝ) ^ (-θ)) ^ 2 := by rw [Real.rpow_add hW0, sq]
  have hW2 : (W : ℝ) ^ (-2 : ℝ) ≤ (W : ℝ) ^ (-θ) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  -- the three one-block bounds, at `S = univ`
  have hb1 := h₁ W q a Rp Set.univ hW hRm hRh hRa MeasurableSet.univ (fun _ _ _ => rfl) g E
    ((W : ℝ) ^ θ) (by positivity)
  have hb2 := h₂ W q a Rp Set.univ hW hRm hRh hRa MeasurableSet.univ (fun _ _ _ => rfl) g E
    ((W : ℝ) ^ (-θ)) ((W : ℝ) ^ (3 * θ)) (by positivity) (by positivity)
  have hb3 := h₃ W q a Rp Set.univ hW hRm hRh hRa MeasurableSet.univ (fun _ _ _ => rfl) g E hg
  rw [measure_univ, mul_one] at hb1 hb2 hb3
  have e1 : C₁ / (W : ℝ) ^ θ = C₁ * (W : ℝ) ^ (-θ) := by
    rw [Real.rpow_neg hW0.le, div_eq_mul_inv]
  have e2 : 2 * C₂ * W * g ^ 2 / ((W : ℝ) ^ (-θ) * (W : ℝ) ^ (3 * θ)) ≤
      2 * C₂ * (W : ℝ) ^ (-θ) := by
    have hst : (W : ℝ) ^ (-θ) * (W : ℝ) ^ (3 * θ) = (W : ℝ) ^ (2 * θ) := by
      rw [← Real.rpow_add hW0]; congr 1; ring
    have hw : (W : ℝ) * (W : ℝ) ^ (-1 + θ) = (W : ℝ) ^ θ := by
      rw [show (W : ℝ) * (W : ℝ) ^ (-1 + θ) = (W : ℝ) ^ (1 : ℝ) * (W : ℝ) ^ (-1 + θ) by
        rw [Real.rpow_one], ← Real.rpow_add hW0]
      congr 1; ring
    have hv : (W : ℝ) ^ (-θ) * (W : ℝ) ^ (2 * θ) = (W : ℝ) ^ θ := by
      rw [← Real.rpow_add hW0]; congr 1; ring
    rw [hst, div_le_iff₀ (by positivity), mul_assoc _ ((W : ℝ) ^ (-θ)), hv]
    calc 2 * C₂ * W * g ^ 2 = 2 * C₂ * (W * g ^ 2) := by ring
      _ ≤ 2 * C₂ * (W * (W : ℝ) ^ (-1 + θ)) := by gcongr
      _ = 2 * C₂ * (W : ℝ) ^ θ := by rw [hw]
  have e3 : C₃ * ((W : ℝ) ^ (-2 : ℝ) + Real.sqrt g) ≤ 2 * C₃ * (W : ℝ) ^ (-θ) := by
    nlinarith
  have hb1' := hb1.trans (ENNReal.ofReal_le_ofReal e1.le)
  have hb2' := hb2.trans (ENNReal.ofReal_le_ofReal e2)
  have hb3' := hb3.trans (ENNReal.ofReal_le_ofReal e3)
  have hA := ae_prepOK (E := E) hg hg1 hq x
  have hsub : {ω : Ω W q | ¬ (PrepOK W g E q x ω ∧
      (prepR W g E q x ω 4, prepV W g E q x ω 4) ∈ PrepGoodCrit W g θ)} ⊆
      (({ω | ¬ PrepOK W g E q x ω} ∪
        {ω | ω ∈ Set.univ ∧ ¬ IsRegularState W g
          (gueBlock W q ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹}) ∪
        {ω | ω ∈ Set.univ ∧ (W : ℝ) ^ θ * W ≤
          ‖(gueBlock W q ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹‖}) ∪
        {ω | ω ∈ Set.univ ∧ (W : ℝ) ^ (3 * θ) < (countIn (((g : ℂ) ^ 2) •
          (gueBlock W q ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹) {x | (W : ℝ) ^ (-θ) < |x|} :
          ℝ)} := by
    intro ω hω
    by_cases hP : PrepOK W g E q x ω
    · by_cases hr : IsRegularState W g (gueBlock W q ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹
      · by_cases hn : (W : ℝ) ^ θ * W ≤
            ‖(gueBlock W q ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹‖
        · exact Or.inl (Or.inr ⟨Set.mem_univ _, hn⟩)
        · by_cases hc : (W : ℝ) ^ (3 * θ) < (countIn (((g : ℂ) ^ 2) •
              (gueBlock W q ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹)
              {x | (W : ℝ) ^ (-θ) < |x|} : ℝ)
          · exact Or.inr ⟨Set.mem_univ _, hc⟩
          · exfalso
            refine hω ⟨hP, ?_⟩
            simp only [PrepGoodCrit, Set.mem_ofPred_eq, hR4 ω hP]
            have hn' := not_le.mp hn
            have h1θ : (W : ℝ) ^ (1 + θ) = (W : ℝ) ^ θ * W := by
              rw [Real.rpow_add hW0, Real.rpow_one, mul_comm]
            refine ⟨hr, ?_, not_lt.mp hc, ?_⟩
            · rw [h1θ]; exact hn'.le
            · calc g ^ 2 * ‖(gueBlock W q ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹‖
                  ≤ (W : ℝ) ^ (-1 + θ) * ((W : ℝ) ^ (1 + θ)) := by
                    rw [h1θ] at *
                    exact mul_le_mul hg2 (by rw [← h1θ]; exact hn'.le) (norm_nonneg _)
                      (by positivity)
                _ = (W : ℝ) ^ (2 * θ) := by
                    rw [← Real.rpow_add hW0]; congr 1; ring
      · exact Or.inl (Or.inl (Or.inr ⟨Set.mem_univ _, hr⟩))
    · exact Or.inl (Or.inl (Or.inl hP))
  calc μ W q _ ≤ μ W q _ := measure_mono hsub
    _ ≤ μ W q {ω | ¬ PrepOK W g E q x ω} + _ + _ + _ :=
        (measure_union_le _ _).trans (add_le_add
          ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ 0 + ENNReal.ofReal (2 * C₃ * (W : ℝ) ^ (-θ)) + ENNReal.ofReal (C₁ * (W : ℝ) ^ (-θ)) +
        ENNReal.ofReal (2 * C₂ * (W : ℝ) ^ (-θ)) := by
          rw [hA]; gcongr
    _ = ENNReal.ofReal ((C₁ + 2 * C₂ + 2 * C₃) * (W : ℝ) ^ (-θ)) := by
          have hu : 0 ≤ (W : ℝ) ^ (-θ) := by positivity
          rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring

end LSBA
