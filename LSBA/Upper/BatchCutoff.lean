import LSBA.Upper.Operator
import LSBA.Transfer.Cofactor

/-!
# The cutoff of a transfer batch

The cutoff of Step 1 of Appendix G.5 [sec:c-component-proof] for a batch of `1000 + n` GUE
inputs (Definition 8.5 [up:def:transfer-operator]): a cutoff `χ` of the first `1000` inputs,
which act first, times a smooth Hilbert–Schmidt cutoff `χ̃` of each further input. It is `C^∞`
with compact support and values in `[0, 1]`; it differs from one with probability at most
`C e^{-cW} + n e^{-W²/8}` (the weight bound of (8.27) [up:eq:coarse-density]); and on its support
`‖F‖ ≤ (max{1, g⁻¹} (1 + |E| + max{K₁, √(3W)}))^{1000+n}` (the support bound of (8.27)
[up:eq:coarse-density]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The Hilbert–Schmidt cutoff `χ̃(v) = s(3 - Σ_k v_k² / W²)` of one input in standard
coordinates, with `s` the smooth transition from `0` to `1`: it equals one for
`Σ_k v_k² ≤ 2W²` and vanishes for `Σ_k v_k² ≥ 3W²` (Step 1 of Appendix G.5
[sec:c-component-proof]). -/
def blockCut (W : ℕ) (v : Fin W × Fin W → ℝ) : ℝ :=
  Real.smoothTransition (3 - (∑ k, v k ^ 2) / (W : ℝ) ^ 2)

/-- The cutoff `χ_q(V) = χ(V_1, …, V_1000) ∏_{i > 1000} χ̃(V_i)` of a batch of `1000 + n`
inputs (Step 1 of Appendix G.5 [sec:c-component-proof]); the first `1000` inputs act first. -/
def batchCut (W n : ℕ) (χ : Ω W 1000 → ℝ) (ω : Ω W (1000 + n)) : ℝ :=
  χ (blockAppend W 1000 n ω).1 *
    ∏ i : Fin n, blockCut W fun k => (blockAppend W 1000 n ω).2 (i, k)

/-- The transition cutoff of one input is `C^∞`. -/
private theorem bc_contDiff_blockCut (W : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (blockCut W) := by
  unfold blockCut
  refine Real.smoothTransition.contDiff.comp ?_
  fun_prop

/-- The first `1000` blocks of a sample of `1000 + n` blocks are a `C^∞` (linear) function of
the sample. -/
private theorem bc_contDiff_first (W n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) fun ω : Ω W (1000 + n) => (blockAppend W 1000 n ω).1 :=
  contDiff_pi.2 fun x => contDiff_apply ℝ (fun _ => ℝ) (Fin.castAdd n x.1, x.2)

/-- The `i`-th of the last `n` blocks is a `C^∞` (linear) function of the sample. -/
private theorem bc_contDiff_rest (W n : ℕ) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) fun ω : Ω W (1000 + n) =>
      fun k : Fin W × Fin W => (blockAppend W 1000 n ω).2 (i, k) :=
  contDiff_pi.2 fun x => contDiff_apply ℝ (fun _ => ℝ) (Fin.natAdd 1000 i, x)

/-- The batch cutoff takes values in `[0, 1]` when `χ` does. -/
private theorem bc_nonneg_le {W n : ℕ} {χ : Ω W 1000 → ℝ} (hχ01 : ∀ ω, 0 ≤ χ ω ∧ χ ω ≤ 1)
    (ω : Ω W (1000 + n)) : 0 ≤ batchCut W n χ ω ∧ batchCut W n χ ω ≤ 1 := by
  unfold batchCut
  have h1 := hχ01 (blockAppend W 1000 n ω).1
  have h2 : 0 ≤ ∏ i : Fin n, blockCut W (fun k => (blockAppend W 1000 n ω).2 (i, k)) :=
    Finset.prod_nonneg fun i _ => Real.smoothTransition.nonneg _
  have h3 : ∏ i : Fin n, blockCut W (fun k => (blockAppend W 1000 n ω).2 (i, k)) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => Real.smoothTransition.nonneg _) fun i _ =>
      Real.smoothTransition.le_one _
  exact ⟨mul_nonneg h1.1 h2, (mul_le_mul h1.2 h3 h2 zero_le_one).trans_eq (one_mul 1)⟩

/-- Where the cutoff of one input does not vanish, `Σ_k v_k² ≤ 3 W²`. -/
private theorem bc_blockCut_ne_zero_le (W : ℕ) (v : Fin W × Fin W → ℝ) (h : blockCut W v ≠ 0) :
    ∑ k, v k ^ 2 ≤ 3 * (W : ℝ) ^ 2 := by
  by_contra hlt
  rw [not_le] at hlt
  apply h
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp at hlt
  · have hW2 : (0 : ℝ) < (W : ℝ) ^ 2 := by positivity
    apply Real.smoothTransition.zero_of_nonpos
    have : 3 < (∑ k, v k ^ 2) / (W : ℝ) ^ 2 := by
      rw [lt_div_iff₀ hW2]; linarith
    linarith

/-- The support of the batch cutoff lies in the closed set where the first `1000` blocks are in
the support of `χ` and each further block has `Σ_k v_k² ≤ 3 W²`. -/
private theorem bc_tsupport_subset (W n : ℕ) (χ : Ω W 1000 → ℝ) :
    tsupport (batchCut W n χ) ⊆
      (fun ω : Ω W (1000 + n) => (blockAppend W 1000 n ω).1) ⁻¹' tsupport χ ∩
        ⋂ i : Fin n, {ω : Ω W (1000 + n) |
          ∑ k, ((blockAppend W 1000 n ω).2 (i, k)) ^ 2 ≤ 3 * (W : ℝ) ^ 2} := by
  have hcl : IsClosed ((fun ω : Ω W (1000 + n) => (blockAppend W 1000 n ω).1) ⁻¹' tsupport χ ∩
        ⋂ i : Fin n, {ω : Ω W (1000 + n) |
          ∑ k, ((blockAppend W 1000 n ω).2 (i, k)) ^ 2 ≤ 3 * (W : ℝ) ^ 2}) := by
    refine IsClosed.inter (isClosed_tsupport χ |>.preimage (bc_contDiff_first W n).continuous) ?_
    refine isClosed_iInter fun i => isClosed_le ?_ continuous_const
    exact continuous_finsetSum _ fun k _ => (continuous_apply (Fin.natAdd 1000 i, k)).pow 2
  refine closure_minimal ?_ hcl
  intro ω hω
  have hω' : batchCut W n χ ω ≠ 0 := hω
  unfold batchCut at hω'
  have h1 := left_ne_zero_of_mul hω'
  have h2 := right_ne_zero_of_mul hω'
  refine ⟨subset_tsupport _ h1, Set.mem_iInter.2 fun i => bc_blockCut_ne_zero_le W _ ?_⟩
  exact (Finset.prod_ne_zero_iff.mp h2) i (Finset.mem_univ i)

/-- The batch cutoff is `C^∞` with compact support and values in `[0, 1]` when `χ` is (Step 1
of Appendix G.5 [sec:c-component-proof]). -/
theorem batchCut_spec {W n : ℕ} {χ : Ω W 1000 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχ01 : ∀ ω, 0 ≤ χ ω ∧ χ ω ≤ 1) :
    ContDiff ℝ (⊤ : ℕ∞) (batchCut W n χ) ∧ HasCompactSupport (batchCut W n χ) ∧
      ∀ ω, 0 ≤ batchCut W n χ ω ∧ batchCut W n χ ω ≤ 1 := by
  refine ⟨?_, ?_, bc_nonneg_le hχ01⟩
  · unfold batchCut
    exact (hχ.comp (bc_contDiff_first W n)).mul
      (contDiff_prod fun i _ => (bc_contDiff_blockCut W).comp (bc_contDiff_rest W n i))
  · obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 hχc.isCompact.isBounded
    have hbox : tsupport (batchCut W n χ) ⊆ Set.univ.pi fun _ : Fin (1000 + n) × Fin W × Fin W =>
        Set.Icc (-(max R (2 * W))) (max R (2 * W)) := by
      intro ω hω
      obtain ⟨h1, h2⟩ := bc_tsupport_subset W n χ hω
      have h2' := Set.mem_iInter.1 h2
      intro a _
      rcases a with ⟨a, α, β⟩
      induction a using Fin.addCases with
      | left a' =>
        have h3 := (norm_le_pi_norm ((blockAppend W 1000 n ω).1) (a', α, β)).trans (hR _ h1)
        rw [Real.norm_eq_abs] at h3
        have h4 := abs_le.1 h3
        have e : (blockAppend W 1000 n ω).1 (a', α, β) = ω (Fin.castAdd n a', α, β) := rfl
        rw [e] at h4
        exact ⟨by linarith [le_max_left R (2 * (W : ℝ))], by linarith [le_max_left R (2 * (W : ℝ))]⟩
      | right i =>
        have h5 : ((blockAppend W 1000 n ω).2 (i, α, β)) ^ 2 ≤ 3 * (W : ℝ) ^ 2 :=
          (Finset.single_le_sum
            (f := fun k : Fin W × Fin W => ((blockAppend W 1000 n ω).2 (i, k)) ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ (α, β))).trans (h2' i)
        have h6 : |(blockAppend W 1000 n ω).2 (i, α, β)| ≤ 2 * W := by
          refine abs_le_of_sq_le_sq ?_ (by positivity)
          nlinarith [sq_nonneg (W : ℝ)]
        have h7 := abs_le.1 h6
        have e : (blockAppend W 1000 n ω).2 (i, α, β) = ω (Fin.natAdd 1000 i, α, β) := rfl
        rw [e] at h7
        have hm := le_max_right R (2 * (W : ℝ))
        exact ⟨by linarith, by linarith⟩
    exact IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc)
      (isClosed_tsupport _) hbox

/-- The cutoff of one input equals one when `Σ_k v_k² ≤ 2 W²`, for `W ≥ 1`. -/
private theorem bc_blockCut_eq_one (W : ℕ) (hW : 1 ≤ W) (v : Fin W × Fin W → ℝ)
    (h : ∑ k, v k ^ 2 ≤ 2 * ((Fintype.card (Fin W × Fin W) : ℕ) : ℝ)) : blockCut W v = 1 := by
  have hW2 : (0 : ℝ) < (W : ℝ) ^ 2 := by positivity
  apply Real.smoothTransition.one_of_one_le
  have hc : ((Fintype.card (Fin W × Fin W) : ℕ) : ℝ) = (W : ℝ) ^ 2 := by simp [sq]
  rw [hc] at h
  have : (∑ k, v k ^ 2) / (W : ℝ) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ hW2]; linarith
  linarith

/-- The measure of a set depending on the first `p` blocks and on the last `q` blocks through
sets `A` and `B` is at most `μ A · μ B`. -/
private theorem bc_measure_blockAppend_preimage_le (W p q : ℕ) (A : Set (Ω W p))
    (B : Set (Ω W q)) :
    μ W (p + q) (blockAppend W p q ⁻¹' (A ×ˢ B)) ≤ μ W p A * μ W q B := by
  refine (Measure.le_map_apply (measurePreserving_blockAppend W p q).measurable.aemeasurable
    _).trans ?_
  rw [(measurePreserving_blockAppend W p q).map_eq, Measure.prod_prod]

/-- The indices of block `i` as a subtype of all indices. -/
private def bc_rowIdx (W n : ℕ) (i : Fin n) :
    Fin W × Fin W ≃ {x : Fin n × Fin W × Fin W // x.1 = i} where
  toFun k := ⟨(i, k), rfl⟩
  invFun x := x.1.2
  left_inv _ := rfl
  right_inv x := by
    obtain ⟨⟨j, k⟩, h⟩ := x
    simp only at h
    subst h
    rfl

/-- The coordinates of block `i` form a standard Gaussian vector. -/
private theorem bc_measurePreserving_row (W n : ℕ) (i : Fin n) :
    MeasurePreserving (fun η : Ω W n => fun k : Fin W × Fin W => η (i, k)) (μ W n)
      (stdGauss (Fin W × Fin W)) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n × Fin W × Fin W =>
    gaussianReal 0 1) (fun x => x.1 = i)
  have h2 := (measurePreserving_piCongrLeft
    (α := fun _ : {x : Fin n × Fin W × Fin W // x.1 = i} => ℝ)
    (fun _ => gaussianReal 0 1) (bc_rowIdx W n i)).symm
  have h3 := h2.comp ((measurePreserving_fst (ν := Measure.pi fun _ :
    {x : Fin n × Fin W × Fin W // ¬ x.1 = i} => gaussianReal 0 1)).comp h1)
  have key : (fun η : Ω W n => fun k : Fin W × Fin W => η (i, k)) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : {x : Fin n × Fin W × Fin W // x.1 = i} => ℝ)
        (bc_rowIdx W n i)).symm ∘ Prod.fst ∘
      ⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n × Fin W × Fin W => ℝ)
        (fun x => x.1 = i)) := by
    funext η k
    simp [bc_rowIdx, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      MeasurableEquiv.piEquivPiSubtypeProd]
  rw [key]
  exact h3

/-- The chi-square tail for one block: `Σ_k η_k² > 2 W²` has probability at most `e^{-W²/8}`. -/
private theorem bc_measure_row_le (W n : ℕ) (i : Fin n) :
    μ W n {η : Ω W n | 2 * ((Fintype.card (Fin W × Fin W) : ℕ) : ℝ) < ∑ k, η (i, k) ^ 2} ≤
      ENNReal.ofReal (Real.exp (-((W : ℝ) * W) / 8)) := by
  have hmp := bc_measurePreserving_row W n i
  have h1 := (Measure.le_map_apply (μ := μ W n) hmp.measurable.aemeasurable
    {x : Fin W × Fin W → ℝ | 2 * ((Fintype.card (Fin W × Fin W) : ℕ) : ℝ) < ∑ k, x k ^ 2})
  rw [hmp.map_eq] at h1
  refine h1.trans ?_
  refine (chiSq_tail (Fin W × Fin W)).trans (le_of_eq ?_)
  simp

/-- The weight bound of (8.27) [up:eq:coarse-density]: the batch cutoff differs from one with
probability at most `C e^{-cW} + n e^{-W²/8}`, by the chi-square tail of each further input. -/
theorem measure_batchCut_ne_one_le {W n : ℕ} {χ : Ω W 1000 → ℝ} {c C : ℝ} (hW : 1 ≤ W)
    (hC : 0 ≤ C) (hχ : μ W 1000 {ω | χ ω ≠ 1} ≤ ENNReal.ofReal (C * Real.exp (-c * W))) :
    μ W (1000 + n) {ω | batchCut W n χ ω ≠ 1} ≤
      ENNReal.ofReal (C * Real.exp (-c * W) + (n : ℝ) * Real.exp (-((W : ℝ) * W) / 8)) := by
  have hsub : {ω : Ω W (1000 + n) | batchCut W n χ ω ≠ 1} ⊆
      blockAppend W 1000 n ⁻¹' ({η | χ η ≠ 1} ×ˢ Set.univ) ∪
        ⋃ i : Fin n, blockAppend W 1000 n ⁻¹'
          (Set.univ ×ˢ {η : Ω W n |
            2 * ((Fintype.card (Fin W × Fin W) : ℕ) : ℝ) < ∑ k, η (i, k) ^ 2}) := by
    intro ω hω
    by_contra hnot
    apply hω
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_preimage, Set.mem_prod, Set.mem_ofPred_eq,
      Set.mem_univ, and_true, true_and, not_or, not_exists, not_not, not_lt] at hnot
    obtain ⟨h1, h2⟩ := hnot
    unfold batchCut
    rw [h1, one_mul]
    exact Finset.prod_eq_one fun i _ => bc_blockCut_eq_one W hW _ (h2 i)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hA : μ W (1000 + n) (blockAppend W 1000 n ⁻¹' ({η | χ η ≠ 1} ×ˢ Set.univ)) ≤
      ENNReal.ofReal (C * Real.exp (-c * W)) := by
    refine (bc_measure_blockAppend_preimage_le W 1000 n _ _).trans ?_
    simpa using hχ
  have hB : μ W (1000 + n) (⋃ i : Fin n, blockAppend W 1000 n ⁻¹'
        (Set.univ ×ˢ {η : Ω W n |
          2 * ((Fintype.card (Fin W × Fin W) : ℕ) : ℝ) < ∑ k, η (i, k) ^ 2})) ≤
      ENNReal.ofReal ((n : ℝ) * Real.exp (-((W : ℝ) * W) / 8)) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    have : ∀ i : Fin n, μ W (1000 + n) (blockAppend W 1000 n ⁻¹'
          (Set.univ ×ˢ {η : Ω W n |
            2 * ((Fintype.card (Fin W × Fin W) : ℕ) : ℝ) < ∑ k, η (i, k) ^ 2})) ≤
        ENNReal.ofReal (Real.exp (-((W : ℝ) * W) / 8)) := fun i => by
      refine (bc_measure_blockAppend_preimage_le W 1000 n _ _).trans ?_
      simpa using bc_measure_row_le W n i
    refine (Finset.sum_le_sum fun i _ => this i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_add (mul_nonneg hC (Real.exp_pos _).le)
    (mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le)]
  exact add_le_add hA hB

/-- The squared modulus of an entry of a GUE block (1.2) [eq:covariance] in real coordinates:
`|V_{αβ}|² = (ω_{αβ}² + ω_{βα}²) / (2 W)`. -/
private theorem bc_gueBlock_entry_sq {W L : ℕ} (ω : Ω W L) (a : Fin L) (α β : Fin W) :
    ‖gueBlock W L ω a α β‖ ^ 2 = (ω (a, α, β) ^ 2 + ω (a, β, α) ^ 2) / (2 * W) := by
  have hW : (0 : ℝ) < W := by exact_mod_cast Fin.pos α
  have hs : (0 : ℝ) < Real.sqrt (2 * W) := Real.sqrt_pos.2 (by positivity)
  have hss : Real.sqrt (2 * (W : ℝ)) ^ 2 = 2 * W := Real.sq_sqrt (by positivity)
  have hsW : (0 : ℝ) < Real.sqrt W := Real.sqrt_pos.2 hW
  have hsWs : Real.sqrt (W : ℝ) ^ 2 = W := Real.sq_sqrt hW.le
  simp only [gueBlock, Matrix.of_apply]
  split_ifs with h1 h2
  · subst h1
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      div_pow, sq_abs, abs_of_pos hsW, hsWs]
    field_simp
    ring
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, div_pow, hss,
      Complex.sq_norm]
    have : (ω (a, α, β) : ℂ) + Complex.I * (ω (a, β, α) : ℂ) =
        (ω (a, α, β) : ℂ) + (ω (a, β, α) : ℂ) * Complex.I := by ring
    rw [this, Complex.normSq_add_mul_I]
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, div_pow, hss,
      Complex.sq_norm]
    have : (ω (a, β, α) : ℂ) - Complex.I * (ω (a, α, β) : ℂ) =
        (ω (a, β, α) : ℂ) + ((-ω (a, α, β) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.normSq_add_mul_I]
    ring

/-- A GUE block (1.2) [eq:covariance] has operator norm squared at most its Hilbert–Schmidt norm
squared, `‖V‖² ≤ W⁻¹ Σ_k ω_k²`. -/
private theorem bc_norm_gueBlock_sq_le {W L : ℕ} (ω : Ω W L) (a : Fin L) :
    ‖gueBlock W L ω a‖ ^ 2 ≤ (∑ k : Fin W × Fin W, ω (a, k) ^ 2) / W := by
  have h := norm_rpow_le_sum_row_rpow (gueBlock W L ω a) (s := 2) (by norm_num) le_rfl
  rw [Real.rpow_two] at h
  have h3 : ∑ j : Fin W, Real.sqrt (∑ k, ‖gueBlock W L ω a j k‖ ^ 2) ^ (2 : ℝ) =
      ∑ j : Fin W, ∑ k : Fin W, ‖gueBlock W L ω a j k‖ ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.rpow_two]
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
  rw [h3] at h
  refine h.trans (le_of_eq ?_)
  simp only [bc_gueBlock_entry_sq]
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp
  · have hW' : (W : ℝ) ≠ 0 := by positivity
    simp only [← Finset.sum_div]
    have e1 : ∑ i : Fin W, ∑ j : Fin W, (ω (a, i, j) ^ 2 + ω (a, j, i) ^ 2) =
        2 * ∑ k : Fin W × Fin W, ω (a, k) ^ 2 := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => ω (a, j, i) ^ 2), Fintype.sum_prod_type]
      ring
    rw [e1]
    field_simp

/-- The identity has operator norm at most one. -/
private theorem bc_norm_one_le {n : Type*} [Fintype n] [DecidableEq n] :
    ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp

/-- A unitary matrix has operator norm at most one. -/
private theorem bc_norm_unitary_le {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : ‖U‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hU] at h
  have h1 := bc_norm_one_le (n := n)
  nlinarith [norm_nonneg U]

/-- `‖P₁ ⊗ V‖ ≤ ‖V‖` for the projection `P₁ = diag(1, 0)`. -/
private theorem bc_norm_kron_le {W : ℕ} (V : Matrix (Fin W) (Fin W) ℂ) :
    ‖(!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V‖ ≤ ‖V‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg V) fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  set y : EuclideanSpace ℂ (Fin W) := WithLp.toLp 2 (fun β => x.ofLp (0, β)) with hy
  have hVy : ‖Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) V y‖ ≤ ‖V‖ * ‖y‖ := by
    have := (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) V).le_opNorm y
    rwa [Matrix.l2_opNorm_toEuclideanCLM] at this
  have hyx : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    have : 0 ≤ ∑ β, ‖x.ofLp (1, β)‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    simp only [hy]
    linarith
  have key : ∀ (i : Fin 2) (β : Fin W),
      (((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) *ᵥ x.ofLp) (i, β) =
        if i = 0 then (V *ᵥ y.ofLp) β else 0 := by
    intro i β
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, hy]
  rw [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM]
  simp only [key, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Finset.sum_const_zero, add_zero]
  have h1 : ∑ β, ‖(V *ᵥ y.ofLp) β‖ ^ 2 =
      ‖Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) V y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM]
  rw [h1]
  calc _ ≤ (‖V‖ * ‖y‖) ^ 2 := by gcongr
    _ = ‖V‖ ^ 2 * ‖y‖ ^ 2 := by ring
    _ ≤ ‖V‖ ^ 2 * ‖x‖ ^ 2 := by gcongr
    _ = _ := by ring

/-- The rotation `[[0, -1], [1, 0]] ⊗ I_W` has operator norm at most one. -/
private theorem bc_norm_rot_le (W : ℕ) :
    ‖(!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := by
  refine bc_norm_unitary_le ?_
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one, Matrix.one_mul]
  have : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * !![0, -1; 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  rw [this, Matrix.one_kronecker_one]

/-- `‖T(V)‖ ≤ 1 + |z| + |g|⁻¹ ‖V‖` for the transfer matrix `T_j(z)` of (8.9) [eq:c-transfer]. -/
private theorem bc_norm_transferMat_le {W : ℕ} (g : ℝ) (z : ℂ) (V : Matrix (Fin W) (Fin W) ℂ) :
    ‖transferMat g z V‖ ≤ 1 + ‖z‖ + |g|⁻¹ * ‖V‖ := by
  have hdec : transferMat g z V =
      (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) +
        z • ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) -
        ((g : ℂ)⁻¹) • ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) := by
    unfold transferMat transferFree
    have : (!![z, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) =
        !![0, -1; 1, 0] + z • !![1, 0; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [this, Matrix.add_kronecker, Matrix.smul_kronecker]
  rw [hdec]
  refine (norm_sub_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans ?_) ?_
  · refine add_le_add (bc_norm_rot_le W) ?_
    rw [norm_smul]
    calc ‖z‖ * ‖(!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)‖
        ≤ ‖z‖ * 1 := by gcongr; exact (bc_norm_kron_le _).trans bc_norm_one_le
      _ = ‖z‖ := mul_one _
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact bc_norm_kron_le V

/-- `‖T_j‖ ≤ max{1, g⁻¹} (1 + |E| + ‖V‖)` for `g > 0` and `T_j = T_j(max{1,g} E / g)`
(8.9) [eq:c-transfer]. -/
private theorem bc_norm_transferMat_le_max {W : ℕ} {g : ℝ} (hg : 0 < g) (E : ℝ)
    (V : Matrix (Fin W) (Fin W) ℂ) :
    ‖transferMat g ((max 1 g * E / g : ℝ) : ℂ) V‖ ≤ max 1 g⁻¹ * (1 + |E| + ‖V‖) := by
  refine (bc_norm_transferMat_le g _ V).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hg,
    abs_of_pos (lt_max_of_lt_left one_pos)]
  have hh : max 1 g / g = max 1 g⁻¹ := by
    rcases le_total 1 g with h | h
    · rw [max_eq_right h, div_self hg.ne', max_eq_left (inv_le_one_of_one_le₀ h)]
    · rw [max_eq_left h, one_div, max_eq_right (one_le_inv₀ hg |>.2 h)]
  have h1 : (1 : ℝ) ≤ max 1 g⁻¹ := le_max_left _ _
  have h2 : g⁻¹ ≤ max 1 g⁻¹ := le_max_right _ _
  rw [mul_div_right_comm, hh]
  nlinarith [norm_nonneg V, abs_nonneg E]

/-- A product of `m` transfer matrices of norm at most `B` has norm at most `B ^ m`. -/
private theorem bc_norm_transferProd_le {W : ℕ} (g : ℝ) (z : ℂ)
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) {B : ℝ} (hB : 0 ≤ B) (m : ℕ)
    (hV : ∀ k < m, ‖transferMat g z (V k)‖ ≤ B) : ‖transferProd g z V m‖ ≤ B ^ m := by
  induction m with
  | zero => simpa [transferProd] using bc_norm_one_le (n := Fin 2 × Fin W)
  | succ m ih =>
    change ‖transferMat g z (V m) * transferProd g z V m‖ ≤ B ^ (m + 1)
    rw [pow_succ']
    exact (norm_mul_le _ _).trans (mul_le_mul (hV m (Nat.lt_succ_self m))
      (ih fun k hk => hV k (Nat.lt_succ_of_lt hk)) (norm_nonneg _) hB)

/-- The support bound of (8.27) [up:eq:coarse-density]: if the first `1000` inputs have norm at
most `K₁` on the support of `χ`, then on the support of the batch cutoff
`‖F‖ ≤ (max{1, g⁻¹} (1 + |E| + max{K₁, √(3W)}))^{1000+n}` for `g > 0`, since
`‖T_i‖ ≤ max{1, g⁻¹} (1 + |E| + ‖V_i‖)` and `‖V_i‖² ≤ W⁻¹ Σ_k v_k² ≤ 3W` on the support of `χ̃`. -/
theorem norm_batchMat_le_of_mem_tsupport {W n : ℕ} {χ : Ω W 1000 → ℝ} {g E K₁ : ℝ}
    (hg : 0 < g) (hK₁ : ∀ ω ∈ tsupport χ, ∀ i, ‖gueBlock W 1000 ω i‖ ≤ K₁)
    {ω : Ω W (1000 + n)} (hω : ω ∈ tsupport (batchCut W n χ)) :
    ‖batchMat W g E (1000 + n) ω‖ ≤
      (max 1 g⁻¹ * (1 + |E| + max K₁ (Real.sqrt (3 * W)))) ^ (1000 + n) := by
  obtain ⟨hfirst, hrest⟩ := bc_tsupport_subset W n χ hω
  have hrest' := Set.mem_iInter.1 hrest
  have hblock : ∀ j : Fin (1000 + n),
      ‖gueBlock W (1000 + n) ω j‖ ≤ max K₁ (Real.sqrt (3 * W)) := by
    intro j
    induction j using Fin.addCases with
    | left j' =>
      rw [← gueBlock_blockAppend_fst]
      exact (hK₁ _ hfirst j').trans (le_max_left _ _)
    | right i =>
      rw [← gueBlock_blockAppend_snd]
      refine le_trans ?_ (le_max_right _ _)
      have h1 := bc_norm_gueBlock_sq_le (blockAppend W 1000 n ω).2 i
      have h3 : ∑ k : Fin W × Fin W, (blockAppend W 1000 n ω).2 (i, k) ^ 2 ≤ 3 * (W : ℝ) ^ 2 :=
        hrest' i
      have h2 : (∑ k : Fin W × Fin W, (blockAppend W 1000 n ω).2 (i, k) ^ 2) / W ≤ 3 * W :=
        div_le_of_le_mul₀ (Nat.cast_nonneg W) (by positivity) (by nlinarith [h3])
      exact (le_abs_self _).trans (Real.abs_le_sqrt (h1.trans h2))
  set M := max K₁ (Real.sqrt (3 * W)) with hM
  have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans (le_max_right _ _)
  have hB0 : 0 ≤ max 1 g⁻¹ * (1 + |E| + M) :=
    mul_nonneg (zero_le_one.trans (le_max_left _ _)) (by positivity)
  have hprod := bc_norm_transferProd_le g ((max 1 g * E / g : ℝ) : ℂ)
    (fun k => if h : k < 1000 + n then gueBlock W (1000 + n) ω ⟨k, h⟩ else 0) hB0 (1000 + n)
    (fun k hk => by
      simp only [hk, dite_true]
      refine (bc_norm_transferMat_le_max hg E _).trans ?_
      gcongr
      exact hblock _)
  have hS := bc_norm_unitary_le (freeConj_zero_mem_unitaryGroup W)
  have hSH : ‖(freeConj W 0)ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]; exact hS
  unfold batchMat
  calc ‖(freeConj W 0)ᴴ * transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun k => if h : k < 1000 + n then gueBlock W (1000 + n) ω ⟨k, h⟩ else 0) (1000 + n) *
        freeConj W 0‖
      ≤ ‖(freeConj W 0)ᴴ‖ * ‖transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun k => if h : k < 1000 + n then gueBlock W (1000 + n) ω ⟨k, h⟩ else 0) (1000 + n)‖ *
        ‖freeConj W 0‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ 1 * (max 1 g⁻¹ * (1 + |E| + M)) ^ (1000 + n) * 1 := by gcongr
    _ = _ := by rw [one_mul, mul_one]

end LSBA
