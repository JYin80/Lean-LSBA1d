import LSBA.Upper.SrcCutoff
import LSBA.Gauss.NormTail

/-!
# The chain plateau of the cutoff

Section 9.4.4 [su:sec:cutoff-estimates]: the plateau of the chain part of the matrix cutoff has
probability `1 - o(1)`. Each of `R_5, …, R_{q-1}`, the right-cavity inverses and `R̃` is the inverse
of a fresh GUE block shifted by a Hermitian matrix fixed before it, so (9.58) [us:eq:wegner] at
`t = W^{3/2}/√2` gives `‖·‖²_HS ≤ W ‖·‖² ≤ W⁶/2` except with probability `C √2 W^{-3/2}`; the
eigenvalue density bound of (9.58) [us:eq:wegner] integrated against `2 g² /(g² + x²)` bounds the
expected rank
surrogate of `#{|g² r| > g}` by `C W g`, and Markov's inequality gives failure `C g^{1/2}`; the
active blocks have norm at most `16` except with probability `e^{-W/2}`. The failure is at most
`C q (W^{-3/2} + g^{1/2})`, uniformly in the energy and the Hermitian chart.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Elementary matrix facts -/

/-- `‖M‖²_HS ≤ |k| ‖M‖²` for the operator norm of a square matrix. -/
private lemma ChainTail_hsSq_le {k : Type*} [Fintype k] [DecidableEq k] (M : Matrix k k ℂ) :
    hsSq M ≤ Fintype.card k * ‖M‖ ^ 2 := by
  unfold hsSq
  rw [Finset.sum_comm]
  have hcol : ∀ b : k, ∑ a, ‖M a b‖ ^ 2 ≤ ‖M‖ ^ 2 := by
    intro b
    have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single b (1 : ℂ))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)] at h2
    have h3 : ∑ x : k, ‖(if x = b then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single b] <;> simp (config := {contextual := true})
    simp only [PiLp.ofLp_single, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
      PiLp.continuousLinearEquiv_symm_apply, Matrix.col_apply, PiLp.single_apply] at h2
    rwa [h3, mul_one] at h2
  calc ∑ b, ∑ a, ‖M a b‖ ^ 2 ≤ ∑ _b : k, ‖M‖ ^ 2 := Finset.sum_le_sum fun b _ => hcol b
    _ = _ := by simp

/-- `‖A - B‖²_HS ≤ 2 ‖A‖²_HS + 2 ‖B‖²_HS`. -/
private lemma ChainTail_hsSq_sub_le {k l : Type*} [Fintype k] [Fintype l] (A B : Matrix k l ℂ) :
    hsSq (A - B) ≤ 2 * hsSq A + 2 * hsSq B := by
  unfold hsSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have h := norm_sub_le (A a b) (B a b)
  rw [Matrix.sub_apply]
  nlinarith [norm_nonneg (A a b - B a b), norm_nonneg (A a b), norm_nonneg (B a b),
    sq_nonneg (‖A a b‖ - ‖B a b‖)]

/-- `‖c M‖²_HS = |c|² ‖M‖²_HS`. -/
private lemma ChainTail_hsSq_smul {k l : Type*} [Fintype k] [Fintype l] (c : ℂ)
    (A : Matrix k l ℂ) : hsSq (c • A) = ‖c‖ ^ 2 * hsSq A := by
  unfold hsSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow]

/-- Every input block `blockSeq W q ω k` is Hermitian. -/
private lemma ChainTail_blockSeq_isHermitian {W q : ℕ} (ω : Ω W q) (k : ℕ) :
    (blockSeq W q ω k).IsHermitian := by
  unfold blockSeq
  split_ifs
  · exact gueBlock_isHermitian W q ω _
  · exact Matrix.isHermitian_zero

/-- `V - E - g² R` is Hermitian for Hermitian `V` and `R` and real `E`, `g`. -/
private lemma ChainTail_shift_isHermitian {W : ℕ} {V R : Matrix (Fin W) (Fin W) ℂ}
    (hV : V.IsHermitian) (hR : R.IsHermitian) (E g : ℝ) :
    (V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R).IsHermitian := by
  have hE : IsSelfAdjoint (E : ℂ) := by rw [isSelfAdjoint_iff]; simp
  have hk : IsSelfAdjoint ((g : ℂ) ^ 2) := by rw [isSelfAdjoint_iff]; simp
  exact (hV.sub (Matrix.isHermitian_one.smul hE)).sub (hR.smul hk)

/-- `-(E + g² R)` is Hermitian for Hermitian `R` and real `E`, `g`. -/
private lemma ChainTail_neg_isHermitian {W : ℕ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (E g : ℝ) :
    (-((E : ℂ) • 1 + ((g : ℂ) ^ 2) • R)).IsHermitian := by
  have hE : IsSelfAdjoint (E : ℂ) := by rw [isSelfAdjoint_iff]; simp
  have hk : IsSelfAdjoint ((g : ℂ) ^ 2) := by rw [isSelfAdjoint_iff]; simp
  exact ((Matrix.isHermitian_one.smul hE).add (hR.smul hk)).neg

/-- `V - E - g² R = -(E + g² R) + V`. -/
private lemma ChainTail_shift_eq {W : ℕ} (V R : Matrix (Fin W) (Fin W) ℂ) (E g : ℝ) :
    V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R = -((E : ℂ) • 1 + ((g : ℂ) ^ 2) • R) + V := by
  abel

/-! ### Measurability and dependence on the blocks -/

/-- Matrix inversion is a measurable map. -/
private lemma ChainTail_measurable_inv {m : Type*} [Fintype m] [DecidableEq m] :
    Measurable fun A : Matrix m m ℂ => A⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hd : Measurable fun A : Matrix m m ℂ => A.det :=
    (continuous_id.matrix_det).measurable
  have ha : Measurable fun A : Matrix m m ℂ => A.adjugate i j :=
    (continuous_id.matrix_adjugate).measurable.eval_matrix
  exact (hd.inv).mul ha

/-- `(V, R) ↦ V - E - g² R` is Borel. -/
private lemma ChainTail_measurable_shift {W : ℕ} (E g : ℝ) :
    Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
      p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2 :=
  Continuous.measurable (by fun_prop)

/-- Block `a` of the sample is measurable in the sample. -/
private lemma ChainTail_measurable_gueBlock (W L : ℕ) (a : Fin L) :
    Measurable fun ω : Ω W L => gueBlock W L ω a := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The input blocks `blockSeq W q ω k` are measurable in the sample. -/
private lemma ChainTail_measurable_blockSeq (W q k : ℕ) :
    Measurable fun ω : Ω W q => blockSeq W q ω k := by
  unfold blockSeq
  by_cases hk : k < q
  · simp only [hk, ↓reduceDIte]
    exact ChainTail_measurable_gueBlock W q _
  · simp only [hk, ↓reduceDIte]
    exact measurable_const

/-- `ω ↦ #{eigenvalues of G ω in J}` is measurable for a Hermitian-valued measurable `G`. -/
private lemma ChainTail_measurable_countIn {W L : ℕ} {G : Ω W L → Matrix (Fin W) (Fin W) ℂ}
    (hG : Measurable G) (hH : ∀ ω, (G ω).IsHermitian) {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable fun ω => countIn (G ω) J := by
  have hS : IsClosed {M : Matrix (Fin W) (Fin W) ℂ | M.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hsort : ∀ j : Fin (Fintype.card (Fin W)),
      Measurable fun M : Matrix (Fin W) (Fin W) ℂ => sortedEig M j := by
    intro j
    have heq : (fun M : Matrix (Fin W) (Fin W) ℂ => sortedEig M j) =
        Set.piecewise {M : Matrix (Fin W) (Fin W) ℂ | M.IsHermitian}
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
  have hcount : ∀ ω, countIn (G ω) J = ∑ j, if sortedEig (G ω) j ∈ J then 1 else 0 := by
    intro ω
    simp only [countIn, hH ω, ↓reduceDIte, Finset.card_filter, eigenvalues_eq_sortedEig (hH ω)]
    exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun j => if sortedEig (G ω) j ∈ J then 1 else 0)
  have heq : (fun ω => countIn (G ω) J) = fun ω => ∑ j, if sortedEig (G ω) j ∈ J then 1 else 0 :=
    funext hcount
  rw [heq]
  exact Finset.measurable_sum _ fun j _ => Measurable.ite
    (hJ.preimage ((hsort j).comp hG)) measurable_const measurable_const

/-- Block `b` does not depend on block `a ≠ b`. -/
private lemma ChainTail_off_gueBlock {W L : ℕ} {a b : Fin L} (h : b ≠ a) :
    OffBlock W L a fun ω => gueBlock W L ω b := by
  intro ω ω' hω
  have hx : ∀ i j, ω (b, i, j) = ω' (b, i, j) := fun i j => hω (b, i, j) h
  simp only [gueBlock, hx]

/-- The input block `k` does not depend on block `a ≠ k`. -/
private lemma ChainTail_off_blockSeq {W q : ℕ} {a : Fin q} {k : ℕ} (h : k ≠ (a : ℕ)) :
    OffBlock W q a fun ω => blockSeq W q ω k := by
  unfold blockSeq
  by_cases hk : k < q
  · simp only [hk, ↓reduceDIte]
    exact ChainTail_off_gueBlock fun hh => h (by rw [← hh])
  · simp only [hk, ↓reduceDIte]
    exact fun _ _ _ => rfl

private lemma ChainTail_off_map {W L : ℕ} {a : Fin L} {X Y : Type*} {f : Ω W L → X}
    (hf : OffBlock W L a f) (F : X → Y) : OffBlock W L a fun ω => F (f ω) :=
  fun ω ω' h => congrArg F (hf ω ω' h)

private lemma ChainTail_off_map₂ {W L : ℕ} {a : Fin L} {X Y Z : Type*} {f : Ω W L → X}
    {f' : Ω W L → Y} (hf : OffBlock W L a f) (hf' : OffBlock W L a f') (F : X → Y → Z) :
    OffBlock W L a fun ω => F (f ω) (f' ω) :=
  fun ω ω' h => congrArg₂ F (hf ω ω' h) (hf' ω ω' h)


/-! ### The chain of states -/

/-- `R_{j+1} = (V_{j+1} - E - g² R_j)⁻¹` for `j ≥ 4` in terms of the GUE blocks. -/
private lemma ChainTail_chartR_succ {W q : ℕ} (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) {j : ℕ} (hj : 4 ≤ j) (hjq : j < q) :
    chartR W g E q R ω (j + 1) =
      (gueBlock W q ω ⟨j, hjq⟩ - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω j)⁻¹ := by
  have h : ¬ j < 4 := by omega
  simp only [chartR, h, ↓reduceIte, blockSeq, hjq, ↓reduceDIte]

/-- The graph coordinates `R_j` are Hermitian for Hermitian `R_4`. -/
private lemma ChainTail_chartR_isHermitian {W q : ℕ} (g E : ℝ) {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (ω : Ω W q) (j : ℕ) : (chartR W g E q R ω j).IsHermitian := by
  induction j with
  | zero => simpa [chartR] using hR
  | succ j ih =>
    by_cases hj : j < 4
    · simpa [chartR, hj] using hR
    · simp only [chartR, hj, ↓reduceIte]
      exact (ChainTail_shift_isHermitian (ChainTail_blockSeq_isHermitian ω j) ih E g).inv

/-- The graph coordinates `R_j` are measurable in the sample. -/
private lemma ChainTail_chartR_measurable {W q : ℕ} (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) : Measurable fun ω : Ω W q => chartR W g E q R ω j := by
  induction j with
  | zero => simp only [chartR]; exact measurable_const
  | succ j ih =>
    by_cases hj : j < 4
    · simp only [chartR, hj, ↓reduceIte]; exact measurable_const
    · simp only [chartR, hj, ↓reduceIte]
      exact ChainTail_measurable_inv.comp
        ((ChainTail_measurable_shift E g).comp ((ChainTail_measurable_blockSeq W q j).prodMk ih))

/-- `R_j` does not depend on the blocks `a ≥ j`. -/
private lemma ChainTail_chartR_off {W q : ℕ} (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (a : Fin q) (j : ℕ) (hj : j ≤ (a : ℕ)) :
    OffBlock W q a fun ω => chartR W g E q R ω j := by
  induction j with
  | zero => simp only [chartR]; exact fun _ _ _ => rfl
  | succ j ih =>
    by_cases hj4 : j < 4
    · simp only [chartR, hj4, ↓reduceIte]; exact fun _ _ _ => rfl
    · simp only [chartR, hj4, ↓reduceIte]
      exact ChainTail_off_map₂ (ChainTail_off_blockSeq (by omega)) (ih (by omega))
        fun V Y => (V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Y)⁻¹

/-- `R←_{q-1} = (V_{q-1} - E)⁻¹` in terms of the GUE blocks. -/
private lemma ChainTail_cavR_zero {W q : ℕ} (g E : ℝ) (ω : Ω W q) (hq : 2 ≤ q) :
    cavR W g E q ω 0 = (gueBlock W q ω ⟨q - 2, by omega⟩ - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • (0 : Matrix (Fin W) (Fin W) ℂ))⁻¹ := by
  simp [cavR, blockSeq, show q - 2 < q by omega]

/-- `R←_{q-2-m} = (V_{q-2-m} - E - g² R←_{q-1-m})⁻¹` in terms of the GUE blocks. -/
private lemma ChainTail_cavR_succ {W q : ℕ} (g E : ℝ) (ω : Ω W q) (m : ℕ) (hq : 0 < q) :
    cavR W g E q ω (m + 1) =
      (gueBlock W q ω ⟨q - 3 - m, by omega⟩ - (E : ℂ) • 1 -
        ((g : ℂ) ^ 2) • cavR W g E q ω m)⁻¹ := by
  simp only [cavR, blockSeq, show q - 3 - m < q by omega, ↓reduceDIte]

/-- The right-cavity inverses are Hermitian. -/
private lemma ChainTail_cavR_isHermitian {W q : ℕ} (g E : ℝ) (ω : Ω W q) (m : ℕ) :
    (cavR W g E q ω m).IsHermitian := by
  induction m with
  | zero =>
    have h : cavR W g E q ω 0 = (blockSeq W q ω (q - 2) - (E : ℂ) • 1 -
        ((g : ℂ) ^ 2) • (0 : Matrix (Fin W) (Fin W) ℂ))⁻¹ := by simp [cavR]
    rw [h]
    exact (ChainTail_shift_isHermitian (ChainTail_blockSeq_isHermitian ω _)
      Matrix.isHermitian_zero E g).inv
  | succ m ih =>
    simp only [cavR]
    exact (ChainTail_shift_isHermitian (ChainTail_blockSeq_isHermitian ω _) ih E g).inv

/-- The right-cavity inverses are measurable in the sample. -/
private lemma ChainTail_cavR_measurable {W q : ℕ} (g E : ℝ) (m : ℕ) :
    Measurable fun ω : Ω W q => cavR W g E q ω m := by
  induction m with
  | zero =>
    have h : (fun ω : Ω W q => cavR W g E q ω 0) = fun ω => (blockSeq W q ω (q - 2) -
        (E : ℂ) • 1 - ((g : ℂ) ^ 2) • (0 : Matrix (Fin W) (Fin W) ℂ))⁻¹ := by
      funext ω; simp [cavR]
    rw [h]
    exact ChainTail_measurable_inv.comp
      ((ChainTail_measurable_shift E g).comp
        ((ChainTail_measurable_blockSeq W q _).prodMk measurable_const))
  | succ m ih =>
    simp only [cavR]
    exact ChainTail_measurable_inv.comp
      ((ChainTail_measurable_shift E g).comp ((ChainTail_measurable_blockSeq W q _).prodMk ih))

/-- `R←_{q-1-m}` does not depend on the blocks `a` with `a + m + 2 < q`. -/
private lemma ChainTail_cavR_off {W q : ℕ} (g E : ℝ) (a : Fin q) (m : ℕ)
    (hm : (a : ℕ) + m + 2 < q) : OffBlock W q a fun ω => cavR W g E q ω m := by
  induction m with
  | zero =>
    have h : (fun ω : Ω W q => cavR W g E q ω 0) = fun ω => (blockSeq W q ω (q - 2) -
        (E : ℂ) • 1 - ((g : ℂ) ^ 2) • (0 : Matrix (Fin W) (Fin W) ℂ))⁻¹ := by
      funext ω; simp [cavR]
    rw [h]
    exact ChainTail_off_map₂ (ChainTail_off_blockSeq (by omega)) (fun _ _ _ => rfl)
      fun V Y => (V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Y)⁻¹
  | succ m ih =>
    simp only [cavR]
    exact ChainTail_off_map₂ (ChainTail_off_blockSeq (by omega)) (ih (by omega))
      fun V Y => (V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Y)⁻¹

/-- `R̃ = (V_5 - E - g² (R_4 + R←_6))⁻¹` in terms of the GUE blocks, for `q ≥ 5`. -/
private lemma ChainTail_cavRes_eq {W q : ℕ} (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) (hq : 5 ≤ q) :
    cavRes W g E q R ω =
      (gueBlock W q ω ⟨4, by omega⟩ - (E : ℂ) • 1 -
        ((g : ℂ) ^ 2) • (R + cavR W g E q ω (q - 7)))⁻¹ := by
  simp only [cavRes, blockSeq, show 4 < q by omega, ↓reduceDIte, smul_add]
  congr 1
  abel

/-! ### The rank surrogate of an inverse -/

/-- For a Hermitian `Γ` with eigenvalues `λ_k` and `g > 0`,
`rankSurr g⁻¹ (Γ⁻ᴴ Γ⁻¹) ≤ 2 Σ_k g² / (g² + λ_k²)`, with equality for invertible `Γ`. -/
private lemma ChainTail_rankSurr_le {n : Type*} [Fintype n] [DecidableEq n] {Γ : Matrix n n ℂ}
    (hΓ : Γ.IsHermitian) {g : ℝ} (hg : 0 < g) :
    rankSurr g⁻¹ ((Γ⁻¹)ᴴ * Γ⁻¹) ≤ 2 * ∑ k, g ^ 2 / (g ^ 2 + hΓ.eigenvalues k ^ 2) := by
  have hnn : 0 ≤ ∑ k, g ^ 2 / (g ^ 2 + hΓ.eigenvalues k ^ 2) :=
    Finset.sum_nonneg fun k _ => by positivity
  by_cases hu : IsUnit Γ
  · set U : Matrix n n ℂ := (hΓ.eigenvectorUnitary : Matrix n n ℂ) with hUdef
    have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hΓ.eigenvectorUnitary.2
    have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hΓ.eigenvectorUnitary.2
    set d : n → ℝ := hΓ.eigenvalues with hdef
    have hd : ∀ k, d k ≠ 0 := by
      have h := (Matrix.isUnit_iff_isUnit_det Γ).mp hu
      rw [hΓ.det_eq_prod_eigenvalues] at h
      intro k
      exact Complex.ofReal_ne_zero.mp
        ((Finset.prod_ne_zero_iff.mp h.ne_zero) k (Finset.mem_univ k))
    set D : (n → ℝ) → Matrix n n ℂ := fun a => U * Matrix.diagonal (fun k => (a k : ℂ)) * Uᴴ
      with hD
    have hDmul : ∀ a b : n → ℝ, D a * D b = D (fun k => a k * b k) := by
      intro a b
      simp only [hD]
      calc U * Matrix.diagonal (fun k => (a k : ℂ)) * Uᴴ *
            (U * Matrix.diagonal (fun k => (b k : ℂ)) * Uᴴ)
          = U * (Matrix.diagonal (fun k => (a k : ℂ)) * (Uᴴ * U) *
            Matrix.diagonal (fun k => (b k : ℂ))) * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [hU1, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          simp only [Complex.ofReal_mul]
    have hDadd : ∀ a b : n → ℝ, D a + D b = D (fun k => a k + b k) := by
      intro a b
      simp only [hD]
      rw [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]
      simp only [Complex.ofReal_add]
    have hDsmul : ∀ c : ℝ, D (fun _ => c) = (c : ℂ) • (1 : Matrix n n ℂ) := by
      intro c
      simp only [hD]
      rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU2]
    have hDone : D (fun _ => 1) = 1 := by
      rw [hDsmul]; simp
    have hDtrace : ∀ a : n → ℝ, (D a).trace = ∑ k, (a k : ℂ) := by
      intro a
      simp only [hD]
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul, Matrix.trace_diagonal]
    have hDinv : ∀ b : n → ℝ, (∀ k, b k ≠ 0) → (D b)⁻¹ = D (fun k => (b k)⁻¹) := by
      intro b hb
      refine Matrix.inv_eq_right_inv ?_
      rw [hDmul, ← hDone]
      congr 1
      funext k
      exact mul_inv_cancel₀ (hb k)
    have hΓD : Γ = D d := by
      have h := hΓ.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at h
      exact h
    have hΓinv : Γ⁻¹ = D (fun k => (d k)⁻¹) := by
      rw [hΓD, hDinv d hd]
    have hHerm : (Γ⁻¹)ᴴ = Γ⁻¹ := hΓ.inv.eq
    have hM : (Γ⁻¹)ᴴ * Γ⁻¹ = D (fun k => (d k)⁻¹ * (d k)⁻¹) := by
      rw [hHerm, hΓinv, hDmul]
    have hs : (g⁻¹) ^ 2 ≠ 0 := by positivity
    have hMs : (Γ⁻¹)ᴴ * Γ⁻¹ + (((g⁻¹) ^ 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ) =
        D (fun k => (d k)⁻¹ * (d k)⁻¹ + (g⁻¹) ^ 2) := by
      rw [hM, ← hDsmul, hDadd]
    have hpos : ∀ k, (d k)⁻¹ * (d k)⁻¹ + (g⁻¹) ^ 2 ≠ 0 := by
      intro k
      have := mul_self_nonneg (d k)⁻¹
      positivity
    have htr : ((Γ⁻¹)ᴴ * Γ⁻¹ * ((Γ⁻¹)ᴴ * Γ⁻¹ + (((g⁻¹) ^ 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))⁻¹).trace
        = ∑ k, (((d k)⁻¹ * (d k)⁻¹ * ((d k)⁻¹ * (d k)⁻¹ + (g⁻¹) ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [hMs, hDinv _ hpos, hM, hDmul, hDtrace]
    unfold rankSurr
    rw [htr, Complex.re_sum]
    simp only [Complex.ofReal_re]
    refine le_of_eq (congrArg (2 * ·) (Finset.sum_congr rfl fun k _ => ?_))
    have hk := hd k
    field_simp
  · have h0 : Γ⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ (by rwa [← Matrix.isUnit_iff_isUnit_det])
    rw [h0]
    unfold rankSurr
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re,
      mul_zero]
    positivity

/-! ### Dyadic decomposition of `g² / (g² + x²)` -/

/-- `g² / (g² + x²) ≤ Σ_{k ≤ N} 4 · 4^{-k} 1_{|x| ≤ 2^k g} + 4^{-N}`. -/
private lemma ChainTail_dyadic {g : ℝ} (hg : 0 < g) (N : ℕ) (x : ℝ) :
    g ^ 2 / (g ^ 2 + x ^ 2) ≤
      ∑ k ∈ Finset.range (N + 1), 4 * (1 / 4 : ℝ) ^ k *
        (if x ∈ Set.Icc (-(2 ^ k * g)) (2 ^ k * g) then 1 else 0) + (1 / 4 : ℝ) ^ N := by
  have hf0 : 0 ≤ g ^ 2 / (g ^ 2 + x ^ 2) := by positivity
  have hf1 : g ^ 2 / (g ^ 2 + x ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg x]
  induction N with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one]
    split_ifs <;> linarith
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hu : 0 ≤ (1 / 4 : ℝ) ^ N := by positivity
    have hu' : (1 / 4 : ℝ) ^ (N + 1) = (1 / 4 : ℝ) ^ N / 4 := by rw [pow_succ]; ring
    have hS : 0 ≤ ∑ k ∈ Finset.range (N + 1), 4 * (1 / 4 : ℝ) ^ k *
        (if x ∈ Set.Icc (-(2 ^ k * g)) (2 ^ k * g) then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun k _ => by
        have : (0 : ℝ) ≤ if x ∈ Set.Icc (-(2 ^ k * g)) (2 ^ k * g) then 1 else 0 := by
          split_ifs <;> norm_num
        positivity
    by_cases hx : x ∈ Set.Icc (-(2 ^ (N + 1) * g)) (2 ^ (N + 1) * g)
    · simp only [hx, ↓reduceIte]
      linarith
    · simp only [hx, ↓reduceIte]
      have hr : 2 ^ (N + 1) * g < |x| := by
        by_contra h
        exact hx (abs_le.mp (not_lt.mp h))
      have hr2 : (2 ^ (N + 1) * g) ^ 2 < x ^ 2 := by
        have := pow_lt_pow_left₀ hr (by positivity) two_ne_zero
        rwa [sq_abs] at this
      have h4 : ((2 : ℝ) ^ (N + 1)) ^ 2 = 4 ^ (N + 1) := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      have hp : (1 / 4 : ℝ) ^ (N + 1) * ((2 : ℝ) ^ (N + 1)) ^ 2 = 1 := by
        rw [h4, ← mul_pow]
        norm_num
      have hf : g ^ 2 / (g ^ 2 + x ^ 2) ≤ (1 / 4 : ℝ) ^ (N + 1) := by
        rw [div_le_iff₀ (by positivity)]
        have hpp : 0 < (1 / 4 : ℝ) ^ (N + 1) := by positivity
        have := mul_lt_mul_of_pos_left hr2 hpp
        nlinarith [mul_pow (2 ^ (N + 1) : ℝ) g 2]
      linarith

/-- `Σ_k g² / (g² + λ_k²) ≤ Σ_{j ≤ N} 4 · 4^{-j} #{|λ_k| ≤ 2^j g} + |n| 4^{-N}`. -/
private lemma ChainTail_sum_dyadic {n : Type*} [Fintype n] [DecidableEq n] {Γ : Matrix n n ℂ}
    (hΓ : Γ.IsHermitian) {g : ℝ} (hg : 0 < g) (N : ℕ) :
    ∑ k, g ^ 2 / (g ^ 2 + hΓ.eigenvalues k ^ 2) ≤
      ∑ j ∈ Finset.range (N + 1), 4 * (1 / 4 : ℝ) ^ j *
        (countIn Γ (Set.Icc (-(2 ^ j * g)) (2 ^ j * g)) : ℝ) +
        (Fintype.card n : ℝ) * (1 / 4 : ℝ) ^ N := by
  have hcount : ∀ J : Set ℝ, (countIn Γ J : ℝ) =
      ∑ k, if hΓ.eigenvalues k ∈ J then (1 : ℝ) else 0 := by
    intro J
    have h : countIn Γ J = ∑ k, if hΓ.eigenvalues k ∈ J then 1 else 0 := by
      simp only [countIn, hΓ, ↓reduceDIte]
      exact Finset.card_filter _ _
    rw [h]
    push_cast
    rfl
  calc ∑ k, g ^ 2 / (g ^ 2 + hΓ.eigenvalues k ^ 2)
      ≤ ∑ k, (∑ j ∈ Finset.range (N + 1), 4 * (1 / 4 : ℝ) ^ j *
        (if hΓ.eigenvalues k ∈ Set.Icc (-(2 ^ j * g)) (2 ^ j * g) then 1 else 0) +
          (1 / 4 : ℝ) ^ N) := Finset.sum_le_sum fun k _ => ChainTail_dyadic hg N _
    _ = ∑ j ∈ Finset.range (N + 1), 4 * (1 / 4 : ℝ) ^ j *
        (countIn Γ (Set.Icc (-(2 ^ j * g)) (2 ^ j * g)) : ℝ) +
        (Fintype.card n : ℝ) * (1 / 4 : ℝ) ^ N := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp only [hcount, Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr!

/-! ### One fresh block -/

/-- (9.58) [us:eq:wegner], eigenvalue density: for a Hermitian `R` fixed before block `a`,
`E #{eigenvalues of V_a - E - g² R in [α, β]} ≤ C W (β - α)`. -/
private theorem ChainTail_intensity : ∃ C : ℝ, 0 < C ∧
    ∀ (W L : ℕ) (a : Fin L) (g E : ℝ) (Rp : Ω W L → Matrix (Fin W) (Fin W) ℂ),
      Measurable Rp → (∀ ω, (Rp ω).IsHermitian) → OffBlock W L a Rp → ∀ α β : ℝ,
      ∫⁻ ω, (countIn (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)
        (Set.Icc α β) : ℝ≥0∞) ∂(μ W L) ≤ ENNReal.ofReal (C * W * (β - α)) := by
  obtain ⟨C, hC, h⟩ := gueBlock_shift_countIn_le
  refine ⟨C, hC, fun W L a g E Rp hm hH hoff α β => ?_⟩
  have hA : Measurable fun ω => -((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) +
      ((g : ℂ) ^ 2) • Rp ω) :=
    (Continuous.measurable (f := fun M : Matrix (Fin W) (Fin W) ℂ =>
      -((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) + ((g : ℂ) ^ 2) • M)) (by fun_prop)).comp hm
  have key := h W L a _ hA (fun ω => ChainTail_neg_isHermitian (hH ω) E g)
    (fun ω ω' hh => by simp only [hoff ω ω' hh]) α β
  simpa only [ChainTail_shift_eq] using key

/-- `W^{-3/2} = (W √W)⁻¹`. -/
private lemma ChainTail_rpow {W : ℕ} (hW : 0 < W) :
    (W : ℝ) ^ (-(3 / 2 : ℝ)) = ((W : ℝ) * Real.sqrt W)⁻¹ := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [Real.rpow_neg hW0.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hW0,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- (9.58) [us:eq:wegner] at `t = W^{3/2}/2`: the fresh inverse `(V_a - E - g² R)⁻¹` is invertible
with `‖·‖²_HS ≤ W⁶/2` except with probability `C W^{-3/2}`. -/
private theorem ChainTail_norm_tail : ∃ C : ℝ, 0 < C ∧
    ∀ (W L : ℕ) (a : Fin L) (g E : ℝ) (Rp : Ω W L → Matrix (Fin W) (Fin W) ℂ),
      1 ≤ W → Measurable Rp → (∀ ω, (Rp ω).IsHermitian) → OffBlock W L a Rp →
      μ W L {ω | ¬ (IsUnit (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹ ∧
        hsSq (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹ ≤ (W : ℝ) ^ 6 / 2)} ≤
        ENNReal.ofReal (C * (W : ℝ) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := fresh_inv_norm_tail
  obtain ⟨C₂, hC₂, h₂⟩ := ChainTail_intensity
  refine ⟨2 * C₁ + 1, by positivity, fun W L a g E Rp hW hRm hRh hRa => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
  have hsqW : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt hW0.le
  have hwe : (W : ℝ) ^ (-(3 / 2 : ℝ)) = ((W : ℝ) * Real.sqrt W)⁻¹ := ChainTail_rpow hW
  have hwpos : 0 < (W : ℝ) ^ (-(3 / 2 : ℝ)) := by positivity
  have hΓm : Measurable fun ω => gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω :=
    (ChainTail_measurable_shift E g).comp ((ChainTail_measurable_gueBlock W L a).prodMk hRm)
  have hΓh : ∀ ω, (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω).IsHermitian :=
    fun ω => ChainTail_shift_isHermitian (gueBlock_isHermitian W L ω a) (hRh ω) E g
  set t : ℝ := (W : ℝ) * Real.sqrt W / 2 with ht_def
  have ht : 0 < t := by positivity
  have h1 := h₁ W L a Rp Set.univ hW hRm hRh hRa MeasurableSet.univ (fun _ _ _ => rfl) g E t ht
  set δ : ℝ := (W : ℝ) ^ (-(3 / 2 : ℝ)) / (2 * C₂ * W) with hδ_def
  have hδ : 0 < δ := by positivity
  have hG : Measurable fun ω => (countIn (gueBlock W L ω a - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • Rp ω) (Set.Icc (-δ) δ) : ℝ≥0∞) :=
    (measurable_from_top : Measurable fun m : ℕ => (m : ℝ≥0∞)).comp
      (ChainTail_measurable_countIn hΓm hΓh measurableSet_Icc)
  have hsing : ∀ ω, ¬ IsUnit (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω) →
      (1 : ℝ≥0∞) ≤ (countIn (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)
        (Set.Icc (-δ) δ) : ℝ≥0∞) := by
    intro ω hω
    have hdet : (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω).det = 0 := by
      by_contra h
      exact hω ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))
    rw [(hΓh ω).det_eq_prod_eigenvalues, Finset.prod_eq_zero_iff] at hdet
    obtain ⟨k, -, hk⟩ := hdet
    have hk0 : (hΓh ω).eigenvalues k = 0 := Complex.ofReal_eq_zero.mp hk
    have hc : 1 ≤ countIn (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)
        (Set.Icc (-δ) δ) := by
      simp only [countIn, hΓh ω, ↓reduceDIte]
      refine Finset.card_pos.mpr ⟨k, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hk0]
      exact ⟨neg_nonpos.2 hδ.le, hδ.le⟩
    exact_mod_cast hc
  have h2 : μ W L {ω | ¬ IsUnit (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)} ≤
      ENNReal.ofReal ((W : ℝ) ^ (-(3 / 2 : ℝ))) := by
    calc μ W L {ω | ¬ IsUnit (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)}
        ≤ μ W L {ω | (1 : ℝ≥0∞) ≤ (countIn (gueBlock W L ω a - (E : ℂ) • 1 -
          ((g : ℂ) ^ 2) • Rp ω) (Set.Icc (-δ) δ) : ℝ≥0∞)} :=
          measure_mono fun ω hω => hsing ω hω
      _ ≤ (∫⁻ ω, (countIn (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)
          (Set.Icc (-δ) δ) : ℝ≥0∞) ∂(μ W L)) / 1 :=
          meas_ge_le_lintegral_div hG.aemeasurable one_ne_zero ENNReal.one_ne_top
      _ ≤ ENNReal.ofReal (C₂ * W * (δ - -δ)) / 1 :=
          ENNReal.div_le_div_right (h₂ W L a g E Rp hRm hRh hRa _ _) _
      _ = ENNReal.ofReal ((W : ℝ) ^ (-(3 / 2 : ℝ))) := by
          rw [div_one]
          congr 1
          rw [hδ_def]
          field_simp
          ring
  have hsub : {ω | ¬ (IsUnit (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹ ∧
        hsSq (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹ ≤ (W : ℝ) ^ 6 / 2)} ⊆
      {ω | ω ∈ Set.univ ∧ t * W ≤
        ‖(gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹‖} ∪
      {ω | ¬ IsUnit (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)} := by
    intro ω hω
    by_cases hu : IsUnit (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)
    · left
      refine ⟨Set.mem_univ _, ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      apply hω
      refine ⟨Matrix.isUnit_nonsing_inv_iff.mpr hu, ?_⟩
      have hn := norm_nonneg (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹
      have hsq : ‖(gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹‖ ^ 2 ≤
          (t * W) ^ 2 := pow_le_pow_left₀ hn hlt.le 2
      have ht2 : t ^ 2 = (W : ℝ) ^ 3 / 4 := by
        rw [ht_def, div_pow, mul_pow, Real.sq_sqrt hW0.le]
        ring
      have hval : (W : ℝ) * (t * W) ^ 2 = (W : ℝ) ^ 6 / 4 := by
        rw [mul_pow, ht2]
        ring
      calc hsSq (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹
          ≤ Fintype.card (Fin W) * ‖(gueBlock W L ω a - (E : ℂ) • 1 -
            ((g : ℂ) ^ 2) • Rp ω)⁻¹‖ ^ 2 := ChainTail_hsSq_le _
        _ ≤ W * (t * W) ^ 2 := by
          rw [Fintype.card_fin]
          gcongr
        _ = (W : ℝ) ^ 6 / 4 := hval
        _ ≤ (W : ℝ) ^ 6 / 2 := by
          have : 0 ≤ (W : ℝ) ^ 6 := by positivity
          linarith
    · right
      exact hu
  calc μ W L {ω | ¬ (IsUnit (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹ ∧
        hsSq (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹ ≤ (W : ℝ) ^ 6 / 2)}
      ≤ μ W L ({ω | ω ∈ Set.univ ∧ t * W ≤
        ‖(gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹‖} ∪
        {ω | ¬ IsUnit (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)}) :=
        measure_mono hsub
    _ ≤ μ W L {ω | ω ∈ Set.univ ∧ t * W ≤
        ‖(gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹‖} +
        μ W L {ω | ¬ IsUnit (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₁ / t) * μ W L Set.univ +
        ENNReal.ofReal ((W : ℝ) ^ (-(3 / 2 : ℝ))) := add_le_add h1 h2
    _ = ENNReal.ofReal ((2 * C₁ + 1) * (W : ℝ) ^ (-(3 / 2 : ℝ))) := by
        rw [measure_univ, mul_one, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [ht_def, hwe]
        field_simp

/-- (9.58) [us:eq:wegner] integrated against `2 g² / (g² + x²)`, with Markov's inequality: the
rank surrogate `rankSurr g⁻¹ (Γ⁻ᴴ Γ⁻¹)` of the fresh inverse `Γ⁻¹ = (V_a - E - g² R)⁻¹` exceeds
`W g^{1/2} / 2` with probability at most `C g^{1/2}`. -/
private theorem ChainTail_rank_tail : ∃ C : ℝ, 0 < C ∧
    ∀ (W L : ℕ) (a : Fin L) (g E : ℝ) (Rp : Ω W L → Matrix (Fin W) (Fin W) ℂ),
      1 ≤ W → 0 < g → g ≤ 1 → Measurable Rp → (∀ ω, (Rp ω).IsHermitian) → OffBlock W L a Rp →
      μ W L {ω | ¬ (2 * rankSurr g⁻¹
          (((gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹)ᴴ *
            (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹) ≤
          W * Real.sqrt g)} ≤ ENNReal.ofReal (C * Real.sqrt g) := by
  obtain ⟨C₂, hC₂, h₂⟩ := ChainTail_intensity
  refine ⟨4 * (16 * C₂ + 1), by positivity, fun W L a g E Rp hW hg hg1 hRm hRh hRa => ?_⟩
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hg (by norm_num : (1 / 4 : ℝ) < 1)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  have hsq : Real.sqrt g * Real.sqrt g = g := Real.mul_self_sqrt hg.le
  have hΓm : Measurable fun ω => gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω :=
    (ChainTail_measurable_shift E g).comp ((ChainTail_measurable_gueBlock W L a).prodMk hRm)
  have hΓh : ∀ ω, (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω).IsHermitian :=
    fun ω => ChainTail_shift_isHermitian (gueBlock_isHermitian W L ω a) (hRh ω) E g
  -- the counts of eigenvalues in the dyadic windows
  let G : ℕ → Ω W L → ℝ≥0∞ := fun j ω => (countIn (gueBlock W L ω a - (E : ℂ) • 1 -
    ((g : ℂ) ^ 2) • Rp ω) (Set.Icc (-(2 ^ j * g)) (2 ^ j * g)) : ℝ≥0∞)
  have hG : ∀ j, Measurable (G j) := fun j =>
    (measurable_from_top : Measurable fun m : ℕ => (m : ℝ≥0∞)).comp
      (ChainTail_measurable_countIn hΓm hΓh measurableSet_Icc)
  let F : Ω W L → ℝ≥0∞ := fun ω => ∑ j ∈ Finset.range (N + 1),
    ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ j) * G j ω + ENNReal.ofReal (W * (1 / 4 : ℝ) ^ N)
  have hF : Measurable F :=
    (Finset.measurable_sum _ fun j _ => (hG j).const_mul _).add measurable_const
  -- the event is contained in `{W √g / 4 ≤ F}`
  have hFe : ∀ ω, F ω = ENNReal.ofReal (∑ j ∈ Finset.range (N + 1), 4 * (1 / 4 : ℝ) ^ j *
      (countIn (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)
        (Set.Icc (-(2 ^ j * g)) (2 ^ j * g)) : ℝ) + (W : ℝ) * (1 / 4 : ℝ) ^ N) := by
    intro ω
    have hnn : ∀ j ∈ Finset.range (N + 1), 0 ≤ 4 * (1 / 4 : ℝ) ^ j *
        (countIn (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)
          (Set.Icc (-(2 ^ j * g)) (2 ^ j * g)) : ℝ) := fun j _ => by positivity
    rw [ENNReal.ofReal_add (Finset.sum_nonneg hnn) (by positivity),
      ENNReal.ofReal_sum_of_nonneg hnn]
    simp only [F, G]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  have hsub : {ω | ¬ (2 * rankSurr g⁻¹
          (((gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹)ᴴ *
            (gueBlock W L ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp ω)⁻¹) ≤
          W * Real.sqrt g)} ⊆ {ω | ENNReal.ofReal ((W : ℝ) * Real.sqrt g / 4) ≤ F ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_le] at hω
    simp only [Set.mem_ofPred_eq]
    rw [hFe ω]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := ChainTail_rankSurr_le (hΓh ω) hg (g := g)
    have h2 := ChainTail_sum_dyadic (hΓh ω) hg N
    rw [Fintype.card_fin] at h2
    linarith
  -- the expectation of `F`
  have hint : ∫⁻ ω, F ω ∂(μ W L) ≤ ENNReal.ofReal ((16 * C₂ + 1) * W * g) := by
    have hc : ∀ j, ∫⁻ ω, G j ω ∂(μ W L) ≤ ENNReal.ofReal (C₂ * W * (2 ^ j * g - -(2 ^ j * g))) :=
      fun j => h₂ W L a g E Rp hRm hRh hRa _ _
    have e1 : ∫⁻ ω, F ω ∂(μ W L) = ∑ j ∈ Finset.range (N + 1),
        ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ j) * ∫⁻ ω, G j ω ∂(μ W L) +
        ENNReal.ofReal (W * (1 / 4 : ℝ) ^ N) := by
      simp only [F]
      rw [lintegral_add_right _ measurable_const,
        lintegral_finsetSum _ fun j _ => (hG j).const_mul _, lintegral_const, measure_univ,
        mul_one]
      congr 1
      exact Finset.sum_congr rfl fun j _ => lintegral_const_mul _ (hG j)
    have e2 : ∀ j ∈ Finset.range (N + 1), ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ j) *
        ∫⁻ ω, G j ω ∂(μ W L) ≤ ENNReal.ofReal (8 * C₂ * W * g * (1 / 2 : ℝ) ^ j) := by
      intro j _
      calc ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ j) * ∫⁻ ω, G j ω ∂(μ W L)
          ≤ ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ j) *
            ENNReal.ofReal (C₂ * W * (2 ^ j * g - -(2 ^ j * g))) := by gcongr; exact hc j
        _ = ENNReal.ofReal (8 * C₂ * W * g * (1 / 2 : ℝ) ^ j) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have : (1 / 4 : ℝ) ^ j * 2 ^ j = (1 / 2 : ℝ) ^ j := by
            rw [← mul_pow]; norm_num
          calc 4 * (1 / 4 : ℝ) ^ j * (C₂ * W * (2 ^ j * g - -(2 ^ j * g)))
              = 8 * C₂ * W * g * ((1 / 4 : ℝ) ^ j * 2 ^ j) := by ring
            _ = _ := by rw [this]
    have hgeo : ∑ j ∈ Finset.range (N + 1), 8 * C₂ * W * g * (1 / 2 : ℝ) ^ j ≤
        16 * C₂ * W * g := by
      rw [← Finset.mul_sum]
      have := sum_geometric_two_le (N + 1)
      have hp : 0 ≤ 8 * C₂ * W * g := by positivity
      nlinarith
    have hN' : (W : ℝ) * (1 / 4 : ℝ) ^ N ≤ W * g := mul_le_mul_of_nonneg_left hN.le hW0.le
    calc ∫⁻ ω, F ω ∂(μ W L)
        = ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ j) *
          ∫⁻ ω, G j ω ∂(μ W L) + ENNReal.ofReal (W * (1 / 4 : ℝ) ^ N) := e1
      _ ≤ ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (8 * C₂ * W * g * (1 / 2 : ℝ) ^ j) +
          ENNReal.ofReal (W * (1 / 4 : ℝ) ^ N) := by gcongr with j hj; exact e2 j hj
      _ = ENNReal.ofReal (∑ j ∈ Finset.range (N + 1), 8 * C₂ * W * g * (1 / 2 : ℝ) ^ j +
          W * (1 / 4 : ℝ) ^ N) := by
        rw [ENNReal.ofReal_add (Finset.sum_nonneg fun j _ => by positivity) (by positivity),
          ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
      _ ≤ ENNReal.ofReal ((16 * C₂ + 1) * W * g) := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith
  have hε : ENNReal.ofReal ((W : ℝ) * Real.sqrt g / 4) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  calc μ W L _ ≤ μ W L {ω | ENNReal.ofReal ((W : ℝ) * Real.sqrt g / 4) ≤ F ω} := measure_mono hsub
    _ ≤ (∫⁻ ω, F ω ∂(μ W L)) / ENNReal.ofReal ((W : ℝ) * Real.sqrt g / 4) :=
        meas_ge_le_lintegral_div hF.aemeasurable hε ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((16 * C₂ + 1) * W * g) / ENNReal.ofReal ((W : ℝ) * Real.sqrt g / 4) :=
        ENNReal.div_le_div_right hint _
    _ = ENNReal.ofReal (4 * (16 * C₂ + 1) * Real.sqrt g) := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        field_simp
        nlinarith [hsq]

/-! ### The active blocks and the union bound -/

/-- `e^{-W/2} ≤ 8 W^{-3/2}` for `W ≥ 1`. -/
private lemma ChainTail_exp_le {W : ℕ} (hW : 1 ≤ W) :
    Real.exp (-(W : ℝ) / 2) ≤ 8 * (W : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
  have hsle : Real.sqrt W ≤ W := by
    rw [Real.sqrt_le_iff]
    exact ⟨hW0.le, by nlinarith⟩
  rw [ChainTail_rpow (by omega), ← div_eq_mul_inv]
  have hq := Real.quadratic_le_exp_of_nonneg (x := (W : ℝ) / 2) (by positivity)
  have hx : Real.exp (-(W : ℝ) / 2) * Real.exp ((W : ℝ) / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hxp : 0 < Real.exp (-(W : ℝ) / 2) := Real.exp_pos _
  have h8 : Real.exp (-(W : ℝ) / 2) * (W : ℝ) ^ 2 ≤ 8 := by
    have h1 : (W : ℝ) ^ 2 / 8 ≤ Real.exp ((W : ℝ) / 2) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hxp.le
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  have h3 : Real.exp (-(W : ℝ) / 2) * ((W : ℝ) * Real.sqrt W) ≤
      Real.exp (-(W : ℝ) / 2) * (W : ℝ) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hxp.le
    nlinarith
  linarith

/-- Crude norm bound of an active block: `‖V_a‖ ≤ 16` except with probability `8 W^{-3/2}`. -/
private lemma ChainTail_block_tail {W q : ℕ} (hW : 32 ≤ W) (a : Fin q) :
    μ W q {ω | 16 < ‖gueBlock W q ω a‖} ≤
      ENNReal.ofReal (8 * (W : ℝ) ^ (-(3 / 2 : ℝ))) :=
  (gueBlock_norm_tail hW a).trans (ENNReal.ofReal_le_ofReal (ChainTail_exp_le (by omega)))

/-- `‖V‖ ≤ 16` gives `‖V‖²_HS ≤ 256 W`. -/
private lemma ChainTail_hsSq_block {W : ℕ} {V : Matrix (Fin W) (Fin W) ℂ} (hV : ‖V‖ ≤ 16) :
    hsSq V ≤ 256 * W := by
  have h := ChainTail_hsSq_le V
  rw [Fintype.card_fin] at h
  have h2 : ‖V‖ ^ 2 ≤ 16 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hV 2
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  nlinarith

/-- The size bounds for `W ≥ 32`: `512 W + 2 W⁷ ≤ W⁸` and `256 W ≤ W⁸`. -/
private lemma ChainTail_pow_le {W : ℕ} (hW : 32 ≤ W) :
    512 * (W : ℝ) + 2 * (W : ℝ) ^ 7 ≤ (W : ℝ) ^ 8 ∧ 256 * (W : ℝ) ≤ (W : ℝ) ^ 8 := by
  have hW32 : (32 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have h6 : (32 : ℝ) ^ 6 ≤ (W : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hW32 6
  have h7 : 512 * (W : ℝ) ≤ (W : ℝ) ^ 7 := by
    have : 512 ≤ (W : ℝ) ^ 6 := by norm_num at h6; linarith
    calc 512 * (W : ℝ) ≤ (W : ℝ) ^ 6 * W := by nlinarith
      _ = (W : ℝ) ^ 7 := by ring
  have h8 : 3 * (W : ℝ) ^ 7 ≤ (W : ℝ) ^ 8 := by
    have : 0 ≤ (W : ℝ) ^ 7 := by positivity
    calc 3 * (W : ℝ) ^ 7 ≤ W * (W : ℝ) ^ 7 := by nlinarith
      _ = (W : ℝ) ^ 8 := by ring
  constructor <;> nlinarith [pow_pos hW0 7]

/-- A finite union bound: if each `f i` is at most `ofReal b` and `s` has at most `k` elements,
the sum is at most `ofReal (k b)`. -/
private lemma ChainTail_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {b : ℝ} (hb : 0 ≤ b)
    {k : ℕ} (hk : s.card ≤ k) (hf : ∀ i ∈ s, f i ≤ ENNReal.ofReal b) :
    ∑ i ∈ s, f i ≤ ENNReal.ofReal (k * b) := by
  calc ∑ i ∈ s, f i ≤ s.card • ENNReal.ofReal b := Finset.sum_le_card_nsmul s f _ hf
    _ = ENNReal.ofReal (s.card * b) := by
        rw [nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (k * b) := by
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hb

/-! ### The exceptional events -/

/-- `R_j` is not invertible, or `‖R_j‖²_HS > W⁶/2`. -/
private def ChainTail_chartBad (W q : ℕ) (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    Set (Ω W q) :=
  {ω | ¬ (IsUnit (chartR W g E q R ω j) ∧ hsSq (chartR W g E q R ω j) ≤ (W : ℝ) ^ 6 / 2)}

/-- `R←_{q-1-m}` is not invertible, or `‖R←_{q-1-m}‖²_HS > W⁶/2`. -/
private def ChainTail_cavBad (W q : ℕ) (g E : ℝ) (m : ℕ) : Set (Ω W q) :=
  {ω | ¬ (IsUnit (cavR W g E q ω m) ∧ hsSq (cavR W g E q ω m) ≤ (W : ℝ) ^ 6 / 2)}

/-- `R̃` is not invertible, or `‖R̃‖²_HS > W⁶/2`. -/
private def ChainTail_resBad (W q : ℕ) (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) : Set (Ω W q) :=
  {ω | ¬ (IsUnit (cavRes W g E q R ω) ∧ hsSq (cavRes W g E q R ω) ≤ (W : ℝ) ^ 6 / 2)}

/-- The rank surrogate of `R_j* R_j` exceeds `W g^{1/2} / 2`. -/
private def ChainTail_rankBad (W q : ℕ) (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    Set (Ω W q) :=
  {ω | ¬ (2 * rankSurr g⁻¹ ((chartR W g E q R ω j)ᴴ * chartR W g E q R ω j) ≤
    W * Real.sqrt g)}

/-- `‖V_5 - g² R_4‖²_HS > W⁸`. -/
private def ChainTail_headBad (W q : ℕ) (g : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) : Set (Ω W q) :=
  {ω | ¬ (hsSq (blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R) ≤ (W : ℝ) ^ 8)}

/-- `‖V_{i+1}‖²_HS > W⁸`. -/
private def ChainTail_blockBad (W q : ℕ) (i : ℕ) : Set (Ω W q) :=
  {ω | ¬ (hsSq (blockSeq W q ω i) ≤ (W : ℝ) ^ 8)}

/-- Invertibility and the Hilbert–Schmidt bound of `R_5, …, R_{q-1}`, of the right-cavity inverses
and of `R̃`, each except with probability `C W^{-3/2}`. -/
private theorem ChainTail_inverse_events : ∃ C : ℝ, 0 < C ∧ ∀ (W q : ℕ) (g E : ℝ)
    (R : Matrix (Fin W) (Fin W) ℂ), 1 ≤ W → 7 ≤ q → R.IsHermitian →
    (∀ j ∈ Finset.Icc 5 (q - 1), μ W q (ChainTail_chartBad W q g E R j) ≤
      ENNReal.ofReal (C * (W : ℝ) ^ (-(3 / 2 : ℝ)))) ∧
    (∀ m ∈ Finset.range (q - 6), μ W q (ChainTail_cavBad W q g E m) ≤
      ENNReal.ofReal (C * (W : ℝ) ^ (-(3 / 2 : ℝ)))) ∧
    μ W q (ChainTail_resBad W q g E R) ≤ ENNReal.ofReal (C * (W : ℝ) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨CN, hCN, hN⟩ := ChainTail_norm_tail
  refine ⟨CN, hCN, fun W q g E R hW1 hq hR => ⟨?_, ?_, ?_⟩⟩
  · intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hi4 : 4 ≤ i := by omega
    have hiq : i < q := by omega
    have e : ∀ ω, chartR W g E q R ω (i + 1) = (gueBlock W q ω ⟨i, hiq⟩ - (E : ℂ) • 1 -
        ((g : ℂ) ^ 2) • chartR W g E q R ω i)⁻¹ :=
      fun ω => ChainTail_chartR_succ g E R ω hi4 hiq
    have key := hN W q ⟨i, hiq⟩ g E (fun ω => chartR W g E q R ω i) hW1
      (ChainTail_chartR_measurable g E R i) (fun ω => ChainTail_chartR_isHermitian g E hR ω i)
      (ChainTail_chartR_off g E R ⟨i, hiq⟩ i le_rfl)
    refine le_trans (measure_mono fun ω hω => ?_) key
    have h : ¬ (IsUnit (chartR W g E q R ω (i + 1)) ∧
        hsSq (chartR W g E q R ω (i + 1)) ≤ (W : ℝ) ^ 6 / 2) := hω
    rw [e ω] at h
    exact h
  · intro m hm
    rw [Finset.mem_range] at hm
    cases m with
    | zero =>
      have e : ∀ ω, cavR W g E q ω 0 = (gueBlock W q ω ⟨q - 2, by omega⟩ - (E : ℂ) • 1 -
          ((g : ℂ) ^ 2) • (0 : Matrix (Fin W) (Fin W) ℂ))⁻¹ :=
        fun ω => ChainTail_cavR_zero g E ω (by omega)
      have key := hN W q ⟨q - 2, by omega⟩ g E (fun _ => 0) hW1 measurable_const
        (fun _ => Matrix.isHermitian_zero) (fun _ _ _ => rfl)
      refine le_trans (measure_mono fun ω hω => ?_) key
      have h : ¬ (IsUnit (cavR W g E q ω 0) ∧ hsSq (cavR W g E q ω 0) ≤ (W : ℝ) ^ 6 / 2) := hω
      rw [e ω] at h
      exact h
    | succ m =>
      have hqm : q - 3 - m < q := by omega
      have e : ∀ ω, cavR W g E q ω (m + 1) = (gueBlock W q ω ⟨q - 3 - m, hqm⟩ - (E : ℂ) • 1 -
          ((g : ℂ) ^ 2) • cavR W g E q ω m)⁻¹ :=
        fun ω => ChainTail_cavR_succ g E ω m (by omega)
      have key := hN W q ⟨q - 3 - m, hqm⟩ g E (fun ω => cavR W g E q ω m) hW1
        (ChainTail_cavR_measurable g E m) (fun ω => ChainTail_cavR_isHermitian g E ω m)
        (ChainTail_cavR_off g E ⟨q - 3 - m, hqm⟩ m (by simp only; omega))
      refine le_trans (measure_mono fun ω hω => ?_) key
      have h : ¬ (IsUnit (cavR W g E q ω (m + 1)) ∧
          hsSq (cavR W g E q ω (m + 1)) ≤ (W : ℝ) ^ 6 / 2) := hω
      rw [e ω] at h
      exact h
  · have hq4 : 4 < q := by omega
    have key := hN W q ⟨4, hq4⟩ g E (fun ω => R + cavR W g E q ω (q - 7)) hW1
      ((Continuous.measurable (f := fun M : Matrix (Fin W) (Fin W) ℂ => R + M)
        (by fun_prop)).comp (ChainTail_cavR_measurable g E (q - 7)))
      (fun ω => hR.add (ChainTail_cavR_isHermitian g E ω (q - 7)))
      (ChainTail_off_map (ChainTail_cavR_off g E ⟨4, hq4⟩ (q - 7) (by simp only; omega))
        fun B => R + B)
    refine le_trans (measure_mono fun ω hω => ?_) key
    have h : ¬ (IsUnit (cavRes W g E q R ω) ∧ hsSq (cavRes W g E q R ω) ≤ (W : ℝ) ^ 6 / 2) := hω
    rw [ChainTail_cavRes_eq g E R ω (by omega)] at h
    exact h

/-- The rank surrogate of `R_j* R_j` for `5 ≤ j ≤ q - 2`, each except with probability
`C g^{1/2}`. -/
private theorem ChainTail_rank_events : ∃ C : ℝ, 0 < C ∧ ∀ (W q : ℕ) (g E : ℝ)
    (R : Matrix (Fin W) (Fin W) ℂ), 1 ≤ W → 7 ≤ q → 0 < g → g ≤ 1 → R.IsHermitian →
    ∀ j ∈ Finset.Icc 5 (q - 2), μ W q (ChainTail_rankBad W q g E R j) ≤
      ENNReal.ofReal (C * Real.sqrt g) := by
  obtain ⟨CK, hCK, hK⟩ := ChainTail_rank_tail
  refine ⟨CK, hCK, fun W q g E R hW1 hq hg hg1 hR j hj => ?_⟩
  rw [Finset.mem_Icc] at hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi4 : 4 ≤ i := by omega
  have hiq : i < q := by omega
  have e : ∀ ω, chartR W g E q R ω (i + 1) = (gueBlock W q ω ⟨i, hiq⟩ - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • chartR W g E q R ω i)⁻¹ :=
    fun ω => ChainTail_chartR_succ g E R ω hi4 hiq
  have key := hK W q ⟨i, hiq⟩ g E (fun ω => chartR W g E q R ω i) hW1 hg hg1
    (ChainTail_chartR_measurable g E R i) (fun ω => ChainTail_chartR_isHermitian g E hR ω i)
    (ChainTail_chartR_off g E R ⟨i, hiq⟩ i le_rfl)
  refine le_trans (measure_mono fun ω hω => ?_) key
  have h : ¬ (2 * rankSurr g⁻¹ ((chartR W g E q R ω (i + 1))ᴴ * chartR W g E q R ω (i + 1)) ≤
      W * Real.sqrt g) := hω
  rw [e ω] at h
  exact h

/-- The norms of the active blocks: `‖V_5 - g² R_4‖²_HS ≤ W⁸` and `‖V_{i+1}‖²_HS ≤ W⁸` except with
probability `8 W^{-3/2}` each, for `g⁴ ‖R_4‖²_HS ≤ W⁷`. -/
private theorem ChainTail_block_events {W q : ℕ} (g : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (hW : 32 ≤ W) (hq : 7 ≤ q) (hRs : g ^ 4 * hsSq R ≤ (W : ℝ) ^ 7) :
    μ W q (ChainTail_headBad W q g R) ≤ ENNReal.ofReal (8 * (W : ℝ) ^ (-(3 / 2 : ℝ))) ∧
    ∀ i ∈ Finset.Icc 5 (q - 2), μ W q (ChainTail_blockBad W q i) ≤
      ENNReal.ofReal (8 * (W : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hpow := ChainTail_pow_le hW
  refine ⟨?_, fun i hi => ?_⟩
  · refine le_trans (measure_mono fun ω hω => ?_) (ChainTail_block_tail hW ⟨4, by omega⟩)
    have h : ¬ (hsSq (blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R) ≤ (W : ℝ) ^ 8) := hω
    simp only [Set.mem_ofPred_eq]
    by_contra hle
    rw [not_lt] at hle
    apply h
    have hb : blockSeq W q ω 4 = gueBlock W q ω ⟨4, by omega⟩ := by
      simp [blockSeq, show 4 < q by omega]
    rw [hb]
    have hn : ‖((g : ℂ) ^ 2)‖ ^ 2 = g ^ 4 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, ← pow_mul, pow_mul', sq_abs]
      ring
    calc hsSq (gueBlock W q ω ⟨4, by omega⟩ - ((g : ℂ) ^ 2) • R)
        ≤ 2 * hsSq (gueBlock W q ω ⟨4, by omega⟩) + 2 * hsSq (((g : ℂ) ^ 2) • R) :=
          ChainTail_hsSq_sub_le _ _
      _ ≤ 2 * (256 * W) + 2 * (W : ℝ) ^ 7 := by
          rw [ChainTail_hsSq_smul, hn]
          have := ChainTail_hsSq_block hle
          nlinarith
      _ ≤ (W : ℝ) ^ 8 := by linarith [hpow.1]
  · rw [Finset.mem_Icc] at hi
    have hiq : i < q := by omega
    refine le_trans (measure_mono fun ω hω => ?_) (ChainTail_block_tail hW ⟨i, hiq⟩)
    have h : ¬ (hsSq (blockSeq W q ω i) ≤ (W : ℝ) ^ 8) := hω
    simp only [Set.mem_ofPred_eq]
    by_contra hle
    rw [not_lt] at hle
    apply h
    have hb : blockSeq W q ω i = gueBlock W q ω ⟨i, hiq⟩ := by simp [blockSeq, hiq]
    rw [hb]
    have := ChainTail_hsSq_block hle
    linarith [hpow.2]

/-- If none of the exceptional events occurs, the chain plateau holds. -/
private lemma ChainTail_plat_of_not_mem {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hq : 7 ≤ q) {ω : Ω W q}
    (h1 : ∀ j ∈ Finset.Icc 5 (q - 1), ω ∉ ChainTail_chartBad W q g E R j)
    (h2 : ∀ m ∈ Finset.range (q - 6), ω ∉ ChainTail_cavBad W q g E m)
    (h3 : ω ∉ ChainTail_resBad W q g E R)
    (h4 : ∀ j ∈ Finset.Icc 5 (q - 2), ω ∉ ChainTail_rankBad W q g E R j)
    (h5 : ω ∉ ChainTail_headBad W q g R)
    (h6 : ∀ i ∈ Finset.Icc 5 (q - 2), ω ∉ ChainTail_blockBad W q i) :
    ChainPlat W g E q R ω := by
  have g1 : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j) ∧
      hsSq (chartR W g E q R ω j) ≤ (W : ℝ) ^ 6 / 2 := fun j hj5 hjq =>
    not_not.mp (h1 j (Finset.mem_Icc.mpr ⟨hj5, hjq⟩))
  have g4 : ∀ j, 5 ≤ j → j ≤ q - 2 → 2 * rankSurr g⁻¹ ((chartR W g E q R ω j)ᴴ *
      chartR W g E q R ω j) ≤ W * Real.sqrt g := fun j hj5 hjq =>
    not_not.mp (h4 j (Finset.mem_Icc.mpr ⟨hj5, hjq⟩))
  unfold ChainPlat
  refine ⟨fun j hj5 hjq => ?_, g1 (q - 1) (by omega) le_rfl, fun m hm => ?_,
    not_not.mp h3, not_not.mp h5, fun i hi5 hiq => ?_⟩
  · exact ⟨(g1 j hj5 (by omega)).1, (g1 j hj5 (by omega)).2, g4 j hj5 hjq⟩
  · exact not_not.mp (h2 m (Finset.mem_range.mpr (by omega)))
  · exact not_not.mp (h6 i (Finset.mem_Icc.mpr ⟨hi5, hiq⟩))

/-- The chain plateau fails with probability at most `C q (W^{-3/2} + g^{1/2})` for `W ≥ 32`,
`q ≥ 7`, `0 < g ≤ 1`, every energy and every Hermitian chart `R` with `g² ‖R‖_HS ≤ W^{7/2}`. -/
theorem chainPlat_tail : ∃ C : ℝ, 0 < C ∧ ∀ (W q : ℕ) (g E : ℝ)
    (R : Matrix (Fin W) (Fin W) ℂ), 32 ≤ W → 7 ≤ q → 0 < g → g ≤ 1 → R.IsHermitian →
    g ^ 4 * hsSq R ≤ (W : ℝ) ^ 7 →
    μ W q {ω | ¬ ChainPlat W g E q R ω} ≤
      ENNReal.ofReal (C * q * ((W : ℝ) ^ (-(3 / 2 : ℝ)) + Real.sqrt g)) := by
  obtain ⟨CN, hCN, hN⟩ := ChainTail_inverse_events
  obtain ⟨CK, hCK, hK⟩ := ChainTail_rank_events
  refine ⟨3 * CN + 16 + CK, by positivity, fun W q g E R hW hq hg hg1 hR hRs => ?_⟩
  have hW1 : 1 ≤ W := by omega
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hw : 0 < (W : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have : (0 : ℝ) < W := by exact_mod_cast hW1
    positivity
  have hs : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  obtain ⟨b1, b2, b3⟩ := hN W q g E R hW1 hq hR
  have b4 := hK W q g E R hW1 hq hg hg1 hR
  obtain ⟨b5, b6⟩ := ChainTail_block_events g R hW hq hRs (q := q)
  -- the failure of the plateau lies in the union of the exceptional events
  have hsub : {ω | ¬ ChainPlat W g E q R ω} ⊆
      (((((⋃ j ∈ Finset.Icc 5 (q - 1), ChainTail_chartBad W q g E R j) ∪
        ⋃ m ∈ Finset.range (q - 6), ChainTail_cavBad W q g E m) ∪ ChainTail_resBad W q g E R) ∪
        ⋃ j ∈ Finset.Icc 5 (q - 2), ChainTail_rankBad W q g E R j) ∪ ChainTail_headBad W q g R) ∪
        ⋃ i ∈ Finset.Icc 5 (q - 2), ChainTail_blockBad W q i := by
    intro ω hω
    by_contra hno
    have hω' : ¬ ChainPlat W g E q R ω := hω
    apply hω'
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, exists_prop, not_and] at hno
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hno
    exact ChainTail_plat_of_not_mem hq h1 h2 h3 h4 h5 h6
  have u1 := (measure_biUnion_finset_le (μ := μ W q) (Finset.Icc 5 (q - 1))
    (ChainTail_chartBad W q g E R)).trans
    (ChainTail_sum_le _ _ (k := q) (by positivity) (by rw [Nat.card_Icc]; omega) b1)
  have u2 := (measure_biUnion_finset_le (μ := μ W q) (Finset.range (q - 6))
    (ChainTail_cavBad W q g E)).trans
    (ChainTail_sum_le _ _ (k := q) (by positivity) (by rw [Finset.card_range]; omega) b2)
  have u4 := (measure_biUnion_finset_le (μ := μ W q) (Finset.Icc 5 (q - 2))
    (ChainTail_rankBad W q g E R)).trans
    (ChainTail_sum_le _ _ (k := q) (by positivity) (by rw [Nat.card_Icc]; omega) b4)
  have u6 := (measure_biUnion_finset_le (μ := μ W q) (Finset.Icc 5 (q - 2))
    (ChainTail_blockBad W q)).trans
    (ChainTail_sum_le _ _ (k := q) (by positivity) (by rw [Nat.card_Icc]; omega) b6)
  have x2 := (measure_union_le _ _).trans (add_le_add u1 u2)
  have x3 := (measure_union_le _ _).trans (add_le_add x2 b3)
  have x4 := (measure_union_le _ _).trans (add_le_add x3 u4)
  have x5 := (measure_union_le _ _).trans (add_le_add x4 b5)
  have x6 := (measure_union_le _ _).trans (add_le_add x5 u6)
  calc μ W q {ω | ¬ ChainPlat W g E q R ω}
      ≤ _ := (measure_mono hsub).trans x6
    _ = ENNReal.ofReal (q * (CN * (W : ℝ) ^ (-(3 / 2 : ℝ))) + q * (CN * (W : ℝ) ^ (-(3 / 2 : ℝ))) +
        CN * (W : ℝ) ^ (-(3 / 2 : ℝ)) + q * (CK * Real.sqrt g) + 8 * (W : ℝ) ^ (-(3 / 2 : ℝ)) +
        q * (8 * (W : ℝ) ^ (-(3 / 2 : ℝ)))) := by
        repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((3 * CN + 16 + CK) * q * ((W : ℝ) ^ (-(3 / 2 : ℝ)) + Real.sqrt g)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have p1 : CN * (W : ℝ) ^ (-(3 / 2 : ℝ)) ≤ q * (CN * (W : ℝ) ^ (-(3 / 2 : ℝ))) := by
          nlinarith [mul_pos hCN hw]
        have p2 : 8 * (W : ℝ) ^ (-(3 / 2 : ℝ)) ≤ q * (8 * (W : ℝ) ^ (-(3 / 2 : ℝ))) := by
          nlinarith [hw]
        have e1 : 0 ≤ q * CK * (W : ℝ) ^ (-(3 / 2 : ℝ)) := by positivity
        have e2 : 0 ≤ q * CN * Real.sqrt g := by positivity
        have e3 : 0 ≤ q * Real.sqrt g := by positivity
        nlinarith [p1, p2, e1, e2, e3]

end LSBA
