import LSBA.Upper.ActiveChain
import LSBA.Gauss.ScalarDensity
import LSBA.Upper.CoercivityMap

/-!
# The inverse bound for the active-chain matrix

Section 9.4.2 [su:sec:discarded-output], (9.66) [su:eq:active-chain-inverse]. The mean `s` of the
`(q - 5) W` real diagonal entries of the active blocks is a centred Gaussian of variance
`1/((q - 5) W²)`, independent of `H - s`; the scalar density bound for `(s - A)⁻¹` with a union
over the `(q - 5) W` eigenvalues gives `P(‖H⁻¹‖ > h) ≤ C (q - 5)^{3/2} W² / h`, uniformly in the
Hermitian boundary `R_4`. At `h = W^{5/2}/√(2(q - 5))` this bounds
`‖H⁻¹‖²_HS ≤ (q - 5) W ‖H⁻¹‖² ≤ W⁶/2` except with probability `C (q - 5)² W^{-1/2}`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `‖M‖²_HS ≤ |k| ‖M‖²` for the operator norm of a square matrix. -/
private lemma ActiveChainTail_hsSq_le {k : Type*} [Fintype k] [DecidableEq k] (M : Matrix k k ℂ) :
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

/-- The Gaussian measure of the set of `t` where `tc - A` is not invertible with
`‖(tc - A)⁻¹‖²_HS ≤ |k| h²` is at most `2 |k| / (h |c| √(2π))`. -/
private lemma ActiveChainTail_line {k : Type*} [Fintype k] [DecidableEq k] {A : Matrix k k ℂ}
    (hA : A.IsHermitian) {c h : ℝ} (hc : c ≠ 0) (hh : 0 < h) :
    gaussianReal 0 1 {t : ℝ | ¬ (IsUnit (((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A) ∧
        hsSq (((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A)⁻¹ ≤ Fintype.card k * h ^ 2)} ≤
      ENNReal.ofReal (2 * Fintype.card k / (h * |c| * Real.sqrt (2 * π))) := by
  set N : Set ℝ := {t : ℝ | ¬ IsUnit (((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A)} with hN
  have hNfin : N.Finite := by
    have hpoly : A.charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
    have hfin : {x : ℂ | A.charpoly.IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hpoly
    let f : ℝ → ℂ := fun t => ((t * c : ℝ) : ℂ)
    have hf : Function.Injective f := by
      intro t t' ht
      have h' : t * c = t' * c := Complex.ofReal_injective ht
      exact mul_right_cancel₀ hc h'
    refine (hfin.preimage hf.injOn).subset ?_
    intro t ht
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Polynomial.IsRoot.def]
    rw [Matrix.eval_charpoly]
    by_contra hne
    apply ht
    have hmat : (Matrix.scalar k (f t) - A) = ((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A := by
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    rw [← hmat] at *
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne)
  have hnull : gaussianReal 0 1 N = 0 :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero (hNfin.measure_zero volume)
  have hsub : {t : ℝ | ¬ (IsUnit (((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A) ∧
        hsSq (((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A)⁻¹ ≤ Fintype.card k * h ^ 2)} ⊆
      {t : ℝ | h < ‖(((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A)⁻¹‖} ∪ N := by
    intro t ht
    by_cases hu : IsUnit (((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A)
    · left
      by_contra hle
      rw [Set.mem_ofPred_eq, not_lt] at hle
      apply ht
      refine ⟨hu, ?_⟩
      calc hsSq (((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A)⁻¹
          ≤ Fintype.card k * ‖(((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A)⁻¹‖ ^ 2 :=
            ActiveChainTail_hsSq_le _
        _ ≤ Fintype.card k * h ^ 2 := by
            gcongr
    · right
      exact hu
  calc _ ≤ gaussianReal 0 1
        ({t : ℝ | h < ‖(((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A)⁻¹‖} ∪ N) := measure_mono hsub
    _ ≤ gaussianReal 0 1 {t : ℝ | h < ‖(((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A)⁻¹‖} +
        gaussianReal 0 1 N := measure_union_le _ _
    _ = gaussianReal 0 1 {t : ℝ | h < ‖(((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A)⁻¹‖} := by
        rw [hnull, add_zero]
    _ ≤ _ := gaussianReal_norm_inv_gt_le A hA hc hh

/-- Every input block `blockSeq W q ω k` is Hermitian. -/
private lemma ActiveChainTail_blockSeq_isHermitian {W q : ℕ} (ω : Ω W q) (k : ℕ) :
    (blockSeq W q ω k).IsHermitian := by
  unfold blockSeq
  split_ifs
  · exact gueBlock_isHermitian W q ω _
  · exact Matrix.isHermitian_zero

/-- The active-chain matrix is Hermitian when `R_4` is, for real `g`, `E`. -/
private lemma ActiveChainTail_isHermitian {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (ω : Ω W q) : (activeMat W g E q R ω).IsHermitian := by
  have hE : ((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  have hG : ((g : ℂ) ^ 2 • R).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hR.eq]
    simp
  have hB : ∀ a : ℕ, (blockSeq W q ω (a + 4) - (E : ℂ) • 1 -
      (if a = 0 then ((g : ℂ) ^ 2) • R else 0)).IsHermitian := by
    intro a
    refine ((ActiveChainTail_blockSeq_isHermitian ω _).sub hE).sub ?_
    split_ifs
    · exact hG
    · exact Matrix.isHermitian_zero
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [Matrix.conjTranspose_apply]
  simp only [activeMat, Matrix.of_apply]
  by_cases hab : a = b
  · subst hab
    simp only [ite_true]
    exact (hB (a : ℕ)).apply i j
  · have hba : ¬ b = a := Ne.symm hab
    simp only [hab, hba, ite_false]
    by_cases h1 : (a : ℕ) + 1 = b ∨ (b : ℕ) + 1 = a
    · have h2 : (b : ℕ) + 1 = a ∨ (a : ℕ) + 1 = b := h1.symm
      simp only [h1, h2, ite_true]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    · have h2 : ¬ ((b : ℕ) + 1 = a ∨ (a : ℕ) + 1 = b) := fun h => h1 h.symm
      simp [h1, h2]

/-- Each entry of a GUE block is a measurable function of the sample. -/
private lemma ActiveChainTail_measurable_gueBlock_apply {W n : ℕ} (a : Fin n) (α β : Fin W) :
    Measurable fun ω : Ω W n => gueBlock W n ω a α β := by
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs
  · fun_prop
  · fun_prop
  · fun_prop

private lemma ActiveChainTail_measurable_blockSeq_apply {W q : ℕ} (k : ℕ) (α β : Fin W) :
    Measurable fun ω : Ω W q => blockSeq W q ω k α β := by
  unfold blockSeq
  by_cases hk : k < q
  · simp only [hk, ↓reduceDIte]
    exact ActiveChainTail_measurable_gueBlock_apply _ _ _
  · simp only [hk, ↓reduceDIte, Matrix.zero_apply]
    exact measurable_const

/-- The active-chain matrix is a measurable function of the sample. -/
private lemma ActiveChainTail_measurable_activeMat (W : ℕ) (g E : ℝ) (q : ℕ)
    (R : Matrix (Fin W) (Fin W) ℂ) : Measurable fun ω : Ω W q => activeMat W g E q R ω := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [activeMat, Matrix.of_apply]
  have hb := ActiveChainTail_measurable_blockSeq_apply (W := W) (q := q) ((x.1 : ℕ) + 4) x.2 y.2
  split_ifs with h h0
  · simp only [Matrix.sub_apply, Matrix.smul_apply]
    fun_prop
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply]
    fun_prop
  all_goals exact measurable_const

/-- Matrix inversion is a measurable map. -/
private lemma ActiveChainTail_measurable_inv {m : Type*} [Fintype m] [DecidableEq m] :
    Measurable fun A : Matrix m m ℂ => A⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hd : Measurable fun A : Matrix m m ℂ => A.det :=
    (continuous_id.matrix_det).measurable
  have ha : Measurable fun A : Matrix m m ℂ => A.adjugate i j :=
    (continuous_id.matrix_adjugate).measurable.eval_matrix
  exact (hd.inv).mul ha

/-- The exceptional set of (9.66) [su:eq:active-chain-inverse] is measurable. -/
private lemma ActiveChainTail_measurableSet_bad (W : ℕ) (g E : ℝ) (q : ℕ)
    (R : Matrix (Fin W) (Fin W) ℂ) (b : ℝ) :
    MeasurableSet {ω : Ω W q | ¬ (IsUnit (activeMat W g E q R ω) ∧
      hsSq (activeMat W g E q R ω)⁻¹ ≤ b)} := by
  have hH := ActiveChainTail_measurable_activeMat W g E q R
  have hdet : Measurable fun ω : Ω W q => (activeMat W g E q R ω).det :=
    (continuous_id.matrix_det).measurable.comp hH
  have hinv : Measurable fun ω : Ω W q => (activeMat W g E q R ω)⁻¹ :=
    ActiveChainTail_measurable_inv.comp hH
  have hhs : Measurable fun ω : Ω W q => hsSq (activeMat W g E q R ω)⁻¹ := by
    unfold hsSq
    refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
    exact (hinv.eval_matrix.norm).pow_const 2
  have hU : MeasurableSet {ω : Ω W q | IsUnit (activeMat W g E q R ω)} := by
    have : {ω : Ω W q | IsUnit (activeMat W g E q R ω)} =
        (fun ω : Ω W q => (activeMat W g E q R ω).det) ⁻¹' {0}ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    rw [this]
    exact hdet (measurableSet_singleton 0).compl
  exact (hU.inter (measurableSet_le hhs measurable_const)).compl

/-- The active blocks `V_5, …, V_{q-1}` as a subset of the blocks of `Ω W q`. -/
private def ActiveChainTail_S (q : ℕ) : Finset (Fin q) :=
  Finset.univ.image fun x : Fin (q - 5) => (⟨(x : ℕ) + 4, by have := x.2; omega⟩ : Fin q)

private lemma ActiveChainTail_card_S (q : ℕ) : (ActiveChainTail_S q).card = q - 5 := by
  unfold ActiveChainTail_S
  rw [Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    have := congrArg Fin.val hxy
    exact Fin.ext (by simpa using this)

/-- Moving the sample along `scalarDir W q S` adds a scalar to each active block. -/
private lemma ActiveChainTail_blockSeq_add {W q : ℕ} (ω : Ω W q) (t : ℝ) (x : Fin (q - 5)) :
    blockSeq W q (ω + t • scalarDir W q (ActiveChainTail_S q)) ((x : ℕ) + 4) =
      blockSeq W q ω ((x : ℕ) + 4) +
        ((t * ((W : ℝ) * Real.sqrt ((q - 5 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) •
          (1 : Matrix (Fin W) (Fin W) ℂ) := by
  have hk : (x : ℕ) + 4 < q := by have := x.2; omega
  have hmem : (⟨(x : ℕ) + 4, hk⟩ : Fin q) ∈ ActiveChainTail_S q :=
    Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  simp only [blockSeq, hk, ↓reduceDIte]
  rw [gueBlock_add_smul_scalarDir]
  simp only [hmem, ↓reduceIte, ActiveChainTail_card_S, div_eq_mul_inv]

/-- Along the scalar direction, the active-chain matrix moves by a multiple of the identity. -/
private lemma ActiveChainTail_activeMat_add {W q : ℕ} (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) (t : ℝ) :
    activeMat W g E q R (ω + t • scalarDir W q (ActiveChainTail_S q)) =
      activeMat W g E q R ω +
        ((t * ((W : ℝ) * Real.sqrt ((q - 5 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) •
          (1 : Matrix (Fin (q - 5) × Fin W) (Fin (q - 5) × Fin W) ℂ) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [activeMat, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab
    rw [ActiveChainTail_blockSeq_add]
    simp only [ite_true, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Prod.mk.injEq, true_and]
    ring
  · simp [hab]

/-- The real arithmetic of the exponents at `h = W^{5/2}/√(2(q - 5))`. -/
private lemma ActiveChainTail_arith (w m : ℝ) (hw : 0 < w) (hm : 0 < m) :
    (m * w) * (w ^ 2 * Real.sqrt w / Real.sqrt (2 * m)) ^ 2 = w ^ 6 / 2 ∧
    2 * (m * w) / (w ^ 2 * Real.sqrt w / Real.sqrt (2 * m) * |(w * Real.sqrt m)⁻¹| *
      Real.sqrt (2 * π)) = 2 / Real.sqrt π * m ^ 2 * w ^ (-(1 / 2 : ℝ)) := by
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have h2m : Real.sqrt (2 * m) = Real.sqrt 2 * Real.sqrt m := Real.sqrt_mul (by norm_num) m
  have h2p : Real.sqrt (2 * π) = Real.sqrt 2 * Real.sqrt π := Real.sqrt_mul (by norm_num) π
  have hwr : w ^ (-(1 / 2 : ℝ)) = (Real.sqrt w)⁻¹ := by
    rw [Real.rpow_neg hw.le, Real.sqrt_eq_rpow]
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqm : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm.le
  have hsqw : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw.le
  rw [abs_of_pos (by positivity), h2m, h2p, hwr]
  constructor
  · rw [div_pow, mul_pow, mul_pow, hsq2, hsqm, hsqw]
    field_simp
  · field_simp
    exact hsqm

/-- (9.66) [su:eq:active-chain-inverse], probability: for a Hermitian `R_4`, `H` is invertible
with `‖H⁻¹‖²_HS ≤ W⁶/2` except with probability `C (q - 5)² W^{-1/2}`. -/
theorem activeMat_inv_tail : ∃ C : ℝ, 0 < C ∧ ∀ (W q : ℕ) (g E : ℝ)
    (R : Matrix (Fin W) (Fin W) ℂ), 1 ≤ W → 6 ≤ q → R.IsHermitian →
    μ W q {ω | ¬ (IsUnit (activeMat W g E q R ω) ∧
        hsSq (activeMat W g E q R ω)⁻¹ ≤ (W : ℝ) ^ 6 / 2)} ≤
      ENNReal.ofReal (C * ((q : ℝ) - 5) ^ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ))) := by
  refine ⟨2 / Real.sqrt π, by positivity, ?_⟩
  intro W q g E R hW hq hR
  have hm1 : 1 ≤ q - 5 := by omega
  have hmR : (((q - 5 : ℕ) : ℝ)) = (q : ℝ) - 5 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hWp : (0 : ℝ) < W := by exact_mod_cast hW
  have hmp : (0 : ℝ) < ((q - 5 : ℕ) : ℝ) := by exact_mod_cast hm1
  set e : Ω W q := scalarDir W q (ActiveChainTail_S q) with he_def
  have hSne : (ActiveChainTail_S q).Nonempty := by
    rw [← Finset.card_pos, ActiveChainTail_card_S]; omega
  have he : ∑ p, e p ^ 2 = 1 := sum_sq_scalarDir hW hSne
  set c : ℝ := ((W : ℝ) * Real.sqrt ((q - 5 : ℕ) : ℝ))⁻¹ with hc_def
  set h : ℝ := (W : ℝ) ^ 2 * Real.sqrt (W : ℝ) / Real.sqrt (2 * ((q - 5 : ℕ) : ℝ)) with hh_def
  have hc : c ≠ 0 := by positivity
  have hh : 0 < h := by positivity
  obtain ⟨harith1, harith2⟩ := ActiveChainTail_arith (W : ℝ) ((q - 5 : ℕ) : ℝ) hWp hmp
  have hcardR : ((Fintype.card (Fin (q - 5) × Fin W) : ℕ) : ℝ) = ((q - 5 : ℕ) : ℝ) * (W : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
  have hcard : ((Fintype.card (Fin (q - 5) × Fin W) : ℕ) : ℝ) * h ^ 2 = (W : ℝ) ^ 6 / 2 := by
    rw [hcardR]
    exact harith1
  set Bad : Set (Ω W q) := {ω | ¬ (IsUnit (activeMat W g E q R ω) ∧
        hsSq (activeMat W g E q R ω)⁻¹ ≤ (W : ℝ) ^ 6 / 2)} with hBad_def
  have hBad : MeasurableSet Bad := ActiveChainTail_measurableSet_bad W g E q R _
  set B : ℝ := 2 * (Fintype.card (Fin (q - 5) × Fin W) : ℝ) / (h * |c| * Real.sqrt (2 * π))
    with hB_def
  have hBval : B = 2 / Real.sqrt π * ((q : ℝ) - 5) ^ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← hmR, hB_def, hcardR]
    exact harith2
  have hinner : ∀ ω : Ω W q, ∫⁻ t, Bad.indicator 1
      (ω - (∑ i, ω i * e i) • e + t • e) ∂(gaussianReal 0 1) ≤ ENNReal.ofReal B := by
    intro ω
    set ω₀ : Ω W q := ω - (∑ i, ω i * e i) • e with hω₀
    have hA : (-(activeMat W g E q R ω₀)).IsHermitian :=
      (ActiveChainTail_isHermitian hR ω₀).neg
    have h1 := ActiveChainTail_line hA hc hh
    set T : Set ℝ := {t : ℝ | ¬ (IsUnit (((t * c : ℝ) : ℂ) •
        (1 : Matrix (Fin (q - 5) × Fin W) (Fin (q - 5) × Fin W) ℂ) - -(activeMat W g E q R ω₀)) ∧
        hsSq (((t * c : ℝ) : ℂ) • (1 : Matrix (Fin (q - 5) × Fin W) (Fin (q - 5) × Fin W) ℂ) -
          -(activeMat W g E q R ω₀))⁻¹ ≤
          Fintype.card (Fin (q - 5) × Fin W) * h ^ 2)} with hT
    have hmem : ∀ t : ℝ, ω₀ + t • e ∈ Bad ↔ t ∈ T := by
      intro t
      have hshift : activeMat W g E q R (ω₀ + t • e) =
          ((t * c : ℝ) : ℂ) • (1 : Matrix (Fin (q - 5) × Fin W) (Fin (q - 5) × Fin W) ℂ) -
            -(activeMat W g E q R ω₀) := by
        rw [he_def, ActiveChainTail_activeMat_add, sub_neg_eq_add, add_comm]
      simp only [hBad_def, hT, Set.mem_ofPred_eq, hshift, hcard]
    calc ∫⁻ t, Bad.indicator 1 (ω₀ + t • e) ∂(gaussianReal 0 1)
        = ∫⁻ t, T.indicator 1 t ∂(gaussianReal 0 1) := by
          refine lintegral_congr fun t => ?_
          by_cases ht : t ∈ T
          · rw [Set.indicator_of_mem ((hmem t).2 ht), Set.indicator_of_mem ht]
            rfl
          · rw [Set.indicator_of_notMem (mt (hmem t).1 ht), Set.indicator_of_notMem ht]
      _ ≤ gaussianReal 0 1 T := lintegral_indicator_one_le T
      _ ≤ ENNReal.ofReal B := h1
  have hline := lintegral_stdGauss_line e he (F := Bad.indicator 1)
    (measurable_one.indicator hBad)
  rw [← hBval, μ_eq_stdGauss, ← lintegral_indicator_one hBad, hline]
  calc ∫⁻ ω, ∫⁻ t, Bad.indicator 1 (ω - (∑ i, ω i * e i) • e + t • e) ∂(gaussianReal 0 1)
        ∂(stdGauss (Fin q × Fin W × Fin W))
      ≤ ∫⁻ _ω, ENNReal.ofReal B ∂(stdGauss (Fin q × Fin W × Fin W)) := lintegral_mono hinner
    _ = ENNReal.ofReal B := by simp

end LSBA
