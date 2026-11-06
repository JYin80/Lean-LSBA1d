import LSBA.Prop.Inputs
import LSBA.Gauss.HaarMoment
import LSBA.Main.HaarVector

/-!
# The Haar step of Lemma 5.9 [gc:lem:residual]

Conjugation invariance of the flow under a common unitary, the moments and tails of the traceless
entries of a resolvent block under an independent Haar unitary from (7.27)
[gc:eq:haar-fixed-moment], and the entrywise implication (5.30) [gc:eq:haar] of Lemma 5.9
[gc:lem:residual] (ii) for a deterministic `Ψ > 0`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The `(a, b)` block of a matrix on `ℂ^L ⊗ ℂ^W`. -/
private def averagingHaar_blk {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun α β => X (a, α) (b, β)

/-- `(I_L ⊗ U)* = I_L ⊗ U*`. -/
private lemma averagingHaar_star_kron (W L : ℕ) (U : Matrix (Fin W) (Fin W) ℂ) :
    star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ U) = (1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ star U := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.star_eq_conjTranspose]

/-- `((I_L ⊗ U) X (I_L ⊗ U)*)_{(a,i),(b,j)} = (U X_{ab} U*)_{ij}`. -/
private lemma averagingHaar_conj_apply {W L : ℕ} (U : Matrix (Fin W) (Fin W) ℂ)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) (i j : Fin W) :
    (((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ U) * X *
      star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ U)) (a, i) (b, j) =
      (U * averagingHaar_blk X a b * star U) i j := by
  rw [averagingHaar_star_kron]
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    averagingHaar_blk, ite_mul, mul_ite, Matrix.star_apply, Finset.sum_mul]

/-- Conjugating a block-diagonal operator by `I_L ⊗ U` conjugates each block by `U`. -/
private lemma averagingHaar_kron_blockDiagOp (W L : ℕ) (U : Matrix.unitaryGroup (Fin W) ℂ)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) * blockDiagOp V *
        star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) =
      blockDiagOp fun a => (U : Matrix (Fin W) (Fin W) ℂ) * V a *
        star (U : Matrix (Fin W) (Fin W) ℂ) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [averagingHaar_conj_apply]
  by_cases hab : a = b
  · subst hab
    have : averagingHaar_blk (blockDiagOp V) a a = V a := by
      ext α β
      simp [averagingHaar_blk, blockDiagOp]
    rw [this]
    simp [blockDiagOp]
  · have : averagingHaar_blk (blockDiagOp V) a b = 0 := by
      ext α β
      simp [averagingHaar_blk, blockDiagOp, hab]
    rw [this]
    simp [blockDiagOp, hab]

/-- Common conjugation of the blocks by `U ∈ U(W)` conjugates the single-time matrix of (5.1)
[fo:eq:flow] by `I_L ⊗ U` (Section 7.5 [app:uniform-continuation], proof of (ii)). -/
theorem flowH_conjMap (g : ℝ) (W L : ℕ) (u : ℝ) (U : Matrix.unitaryGroup (Fin W) ℂ)
    (ω : Ω W L) :
    flowH g W L u (conjMap W L U ω) =
      ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) * flowH g W L u ω *
        star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) := by
  have hUU : (U : Matrix (Fin W) (Fin W) ℂ) * star (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Unitary.coe_mul_star_self U
  have hV : gueBlock W L (conjMap W L U ω) = fun a =>
      (U : Matrix (Fin W) (Fin W) ℂ) * gueBlock W L ω a * star (U : Matrix (Fin W) (Fin W) ℂ) :=
    funext (gueBlock_conjMap W L U ω)
  have hA : ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) *
      (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
        star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) =
      Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
    rw [averagingHaar_star_kron, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, hUU]
  unfold flowH blockFlow blockV
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hA,
    averagingHaar_kron_blockDiagOp, hV]

/-! ### Invariants of the blocks under common conjugation -/

/-- `tr(Mᴴ M) = ∑ₖₗ |Mₖₗ|²`. -/
private lemma averagingHaar_trace_HS {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) :
    (Mᴴ * M).trace = ((∑ k, ∑ l, ‖M k l‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Complex.conj_mul']
  push_cast
  exact Finset.sum_comm

/-- `tr(U M U*) = tr M` for a unitary `U`. -/
private lemma averagingHaar_trace_conj {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ)
    (M : Matrix (Fin W) (Fin W) ℂ) :
    ((U : Matrix (Fin W) (Fin W) ℂ) * M * star (U : Matrix (Fin W) (Fin W) ℂ)).trace =
      M.trace := by
  have h : star (U : Matrix (Fin W) (Fin W) ℂ) * (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul]

/-- The Hilbert–Schmidt norm is invariant under conjugation by a unitary. -/
private lemma averagingHaar_HS_conj {W : ℕ} (U : Matrix.unitaryGroup (Fin W) ℂ)
    (M : Matrix (Fin W) (Fin W) ℂ) :
    ∑ k, ∑ l, ‖((U : Matrix (Fin W) (Fin W) ℂ) * M * star (U : Matrix (Fin W) (Fin W) ℂ)) k l‖ ^ 2 =
      ∑ k, ∑ l, ‖M k l‖ ^ 2 := by
  have h : star (U : Matrix (Fin W) (Fin W) ℂ) * (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  apply Complex.ofReal_injective
  rw [← averagingHaar_trace_HS, ← averagingHaar_trace_HS]
  have e : ((U : Matrix (Fin W) (Fin W) ℂ) * M * star (U : Matrix (Fin W) (Fin W) ℂ))ᴴ *
      ((U : Matrix (Fin W) (Fin W) ℂ) * M * star (U : Matrix (Fin W) (Fin W) ℂ)) =
      (U : Matrix (Fin W) (Fin W) ℂ) * (Mᴴ * M) * star (U : Matrix (Fin W) (Fin W) ℂ) := by
    have key : ∀ X : Matrix (Fin W) (Fin W) ℂ,
        star (U : Matrix (Fin W) (Fin W) ℂ) * ((U : Matrix (Fin W) (Fin W) ℂ) * X) = X :=
      fun X => by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
    have hs : (star (U : Matrix (Fin W) (Fin W) ℂ))ᴴ = (U : Matrix (Fin W) (Fin W) ℂ) := by
      rw [← Matrix.star_eq_conjTranspose, star_star]
    have hs2 : (U : Matrix (Fin W) (Fin W) ℂ)ᴴ = star (U : Matrix (Fin W) (Fin W) ℂ) :=
      (Matrix.star_eq_conjTranspose _).symm
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hs, hs2]
    simp only [Matrix.mul_assoc, key]
  rw [e, averagingHaar_trace_conj]

/-- Equivariance under common conjugation, as an identity of blocks. -/
private lemma averagingHaar_blk_equiv {W L : ℕ}
    {F : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hF : ∀ (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W L), F (conjMap W L U ω) =
      ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) * F ω *
        star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)))
    (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W L) (a b : Fin L) :
    averagingHaar_blk (F (conjMap W L U ω)) a b =
      (U : Matrix (Fin W) (Fin W) ℂ) * averagingHaar_blk (F ω) a b *
        star (U : Matrix (Fin W) (Fin W) ℂ) := by
  ext i j
  change F (conjMap W L U ω) (a, i) (b, j) = _
  rw [hF U ω]
  exact averagingHaar_conj_apply _ _ a b i j

private lemma averagingHaar_blockTr_eq {W L : ℕ}
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    blockTr X a b = (W : ℂ)⁻¹ * (averagingHaar_blk X a b).trace := by
  simp [blockTr, Matrix.trace, averagingHaar_blk]

private lemma averagingHaar_blockHS2_eq {W L : ℕ}
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    blockHS2 X a b = ∑ k, ∑ l, ‖averagingHaar_blk X a b k l‖ ^ 2 := rfl

private lemma averagingHaar_blockHS2_nonneg {W L : ℕ}
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) : 0 ≤ blockHS2 X a b :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- Conjugation by a common unitary does not change the trace of a block. -/
private lemma averagingHaar_blockTr_equiv {W L : ℕ}
    {F : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hF : ∀ (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W L), F (conjMap W L U ω) =
      ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) * F ω *
        star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)))
    (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W L) (a b : Fin L) :
    blockTr (F (conjMap W L U ω)) a b = blockTr (F ω) a b := by
  rw [averagingHaar_blockTr_eq, averagingHaar_blockTr_eq, averagingHaar_blk_equiv hF,
    averagingHaar_trace_conj]

/-- Conjugation by a common unitary does not change the Hilbert–Schmidt norm of a block. -/
private lemma averagingHaar_blockHS2_equiv {W L : ℕ}
    {F : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hF : ∀ (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W L), F (conjMap W L U ω) =
      ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) * F ω *
        star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)))
    (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W L) (a b : Fin L) :
    blockHS2 (F (conjMap W L U ω)) a b = blockHS2 (F ω) a b := by
  rw [averagingHaar_blockHS2_eq, averagingHaar_blockHS2_eq, averagingHaar_blk_equiv hF,
    averagingHaar_HS_conj]

/-- The sample integral is the iterated integral over the sample and an independent Haar
unitary applied through the common conjugation. -/
private lemma averagingHaar_lintegral_conj (W L : ℕ) {h : Ω W L → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ ω, h ω ∂(μ W L) = ∫⁻ ω, ∫⁻ U, h (conjMap W L U ω) ∂(haarU W) ∂(μ W L) := by
  have hm : Measurable fun q : Ω W L × Matrix.unitaryGroup (Fin W) ℂ => h q.1 :=
    hh.comp measurable_fst
  have h1 := (measurePreserving_conj_haar W L).lintegral_comp hm
  have h2 : ∫⁻ q, h q.1 ∂((μ W L).prod (haarU W)) = ∫⁻ ω, h ω ∂(μ W L) := by
    rw [lintegral_prod _ hm.aemeasurable]
    simp
  have h3 : Measurable fun q : Ω W L × Matrix.unitaryGroup (Fin W) ℂ => h (conjMap W L q.2 q.1) :=
    hh.comp (measurable_conjMap_uncurry W L)
  rw [← h2, ← h1, lintegral_prod _ h3.aemeasurable]

/-- The traceless entry of a conjugate is a continuous function of the unitary. -/
private lemma averagingHaar_continuous_entry (W : ℕ) (A : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W)
    (c : ℂ) (n : ℕ) :
    Continuous fun U : Matrix.unitaryGroup (Fin W) ℂ =>
      ‖((U : Matrix (Fin W) (Fin W) ℂ) * A * star (U : Matrix (Fin W) (Fin W) ℂ)) i j - c‖ ^ n := by
  have h1 : Continuous fun U : Matrix.unitaryGroup (Fin W) ℂ => (U : Matrix (Fin W) (Fin W) ℂ) :=
    continuous_subtype_val
  have hB : Continuous fun U : Matrix.unitaryGroup (Fin W) ℂ =>
      (U : Matrix (Fin W) (Fin W) ℂ) * A * star (U : Matrix (Fin W) (Fin W) ℂ) :=
    (h1.matrix_mul continuous_const).matrix_mul (continuous_star.comp h1)
  exact (((hB.matrix_elem i j).sub continuous_const).norm).pow n

/-- (7.27) [gc:eq:haar-fixed-moment] integrated over the sample: for a random matrix that is
equivariant under common conjugation of the blocks, the traceless entries of the block `(a, b)`
satisfy `E|G_{ai,bj} - δ_{ij}⟨G⟩_{ab}|^{2p} ≤ C W^{-2p} E‖G_{ab}‖_HS^{2p}`. -/
theorem haar_traceless_moment (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W L : ℕ, 1 ≤ W →
      ∀ F : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ,
      (∀ x y, Measurable fun ω => F ω x y) →
      (∀ (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W L), F (conjMap W L U ω) =
        ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) * F ω *
          star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ))) →
      ∀ a b : Fin L, Integrable (fun ω => blockHS2 (F ω) a b ^ p) (μ W L) →
      ∀ i j : Fin W,
        Integrable (fun ω => ‖F ω (a, i) (b, j) - if i = j then blockTr (F ω) a b else 0‖ ^ (2 * p))
          (μ W L) ∧
        ∫ ω, ‖F ω (a, i) (b, j) - if i = j then blockTr (F ω) a b else 0‖ ^ (2 * p) ∂(μ W L) ≤
          C / (W : ℝ) ^ (2 * p) * ∫ ω, blockHS2 (F ω) a b ^ p ∂(μ W L) := by
  obtain ⟨C, hC, hmom⟩ := haarU_entry_moment p
  refine ⟨C, hC, fun W L hW F hFm hFe a b hint i j => ?_⟩
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hTr : Measurable fun ω => blockTr (F ω) a b :=
    measurable_const.mul (Finset.measurable_sum _ fun α _ => hFm _ _)
  have hc : Measurable fun ω => (if i = j then blockTr (F ω) a b else 0) := by
    by_cases hij : i = j
    · simpa [hij] using hTr
    · simp [hij]
  set Z : Ω W L → ℝ := fun ω =>
    ‖F ω (a, i) (b, j) - if i = j then blockTr (F ω) a b else 0‖ ^ (2 * p) with hZ
  have hZm : Measurable Z := ((hFm _ _).sub hc).norm.pow_const _
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => by positivity
  have hK : 0 ≤ C / (W : ℝ) ^ (2 * p) := by positivity
  have hHS0 : ∀ ω, 0 ≤ blockHS2 (F ω) a b ^ p := fun ω =>
    pow_nonneg (averagingHaar_blockHS2_nonneg _ _ _) _
  have hpt : ∀ ω, ∫⁻ U, ENNReal.ofReal (Z (conjMap W L U ω)) ∂(haarU W) ≤
      ENNReal.ofReal (C / (W : ℝ) ^ (2 * p) * blockHS2 (F ω) a b ^ p) := by
    intro ω
    have hrew : ∀ U : Matrix.unitaryGroup (Fin W) ℂ, Z (conjMap W L U ω) =
        ‖((U : Matrix (Fin W) (Fin W) ℂ) * averagingHaar_blk (F ω) a b *
            star (U : Matrix (Fin W) (Fin W) ℂ)) i j -
          (if i = j then (W : ℂ)⁻¹ * (averagingHaar_blk (F ω) a b).trace else 0)‖ ^ (2 * p) := by
      intro U
      have h1 : F (conjMap W L U ω) (a, i) (b, j) =
          ((U : Matrix (Fin W) (Fin W) ℂ) * averagingHaar_blk (F ω) a b *
            star (U : Matrix (Fin W) (Fin W) ℂ)) i j := by
        rw [← averagingHaar_blk_equiv hFe U ω a b]
        rfl
      simp only [hZ]
      rw [h1, averagingHaar_blockTr_equiv hFe, averagingHaar_blockTr_eq]
    have hcont := averagingHaar_continuous_entry W (averagingHaar_blk (F ω) a b) i j
      (if i = j then (W : ℂ)⁻¹ * (averagingHaar_blk (F ω) a b).trace else 0) (2 * p)
    have hI : Integrable (fun U : Matrix.unitaryGroup (Fin W) ℂ => Z (conjMap W L U ω))
        (haarU W) := by
      simp only [hrew]
      exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun U => hZ0 _)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hrew]
    exact hmom W hW _ i j
  have hle : ∫⁻ ω, ENNReal.ofReal (Z ω) ∂(μ W L) ≤
      ENNReal.ofReal (C / (W : ℝ) ^ (2 * p) * ∫ ω, blockHS2 (F ω) a b ^ p ∂(μ W L)) := by
    rw [averagingHaar_lintegral_conj W L
      (show Measurable fun ω => ENNReal.ofReal (Z ω) from ENNReal.measurable_ofReal.comp hZm)]
    calc ∫⁻ ω, ∫⁻ U, ENNReal.ofReal (Z (conjMap W L U ω)) ∂(haarU W) ∂(μ W L)
        ≤ ∫⁻ ω, ENNReal.ofReal (C / (W : ℝ) ^ (2 * p)) *
            ENNReal.ofReal (blockHS2 (F ω) a b ^ p) ∂(μ W L) := by
          refine lintegral_mono fun ω => (hpt ω).trans ?_
          rw [ENNReal.ofReal_mul hK]
      _ = ENNReal.ofReal (C / (W : ℝ) ^ (2 * p)) *
            ∫⁻ ω, ENNReal.ofReal (blockHS2 (F ω) a b ^ p) ∂(μ W L) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (C / (W : ℝ) ^ (2 * p) * ∫ ω, blockHS2 (F ω) a b ^ p ∂(μ W L)) := by
          rw [ENNReal.ofReal_mul hK,
            ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hHS0)]
  have hZint : Integrable Z (μ W L) := by
    refine ⟨hZm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hZ0)]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  refine ⟨hZint, ?_⟩
  have hR : 0 ≤ C / (W : ℝ) ^ (2 * p) * ∫ ω, blockHS2 (F ω) a b ^ p ∂(μ W L) :=
    mul_nonneg hK (integral_nonneg hHS0)
  rw [← ENNReal.ofReal_le_ofReal_iff hR, ofReal_integral_eq_lintegral_ofReal hZint
    (Eventually.of_forall hZ0)]
  exact hle

private lemma averagingHaar_measurable_blockHS2 {W L : ℕ}
    {F : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hFm : ∀ x y, Measurable fun ω => F ω x y) (a b : Fin L) :
    Measurable fun ω => blockHS2 (F ω) a b :=
  Finset.measurable_sum _ fun _ _ => Finset.measurable_sum _ fun _ _ =>
    ((hFm _ _).norm).pow_const _

/-- The tail form of (5.30) [gc:eq:haar] at one pair of blocks: conditionally on the sample,
(7.27) [gc:eq:haar-fixed-moment], Markov at `tΨ` and a union over the `W²` entries give
`P(∃ i j, |G_{ai,bj} - δ_{ij}⟨G⟩_{ab}| > tΨ) ≤ P(W^{-2}‖G_{ab}‖²_HS > sΨ²) + C W² (s/t²)^p`. -/
theorem haar_traceless_tail (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W L : ℕ, 1 ≤ W →
      ∀ F : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ,
      (∀ x y, Measurable fun ω => F ω x y) →
      (∀ (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W L), F (conjMap W L U ω) =
        ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) * F ω *
          star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ))) →
      ∀ (a b : Fin L) (Ψ s t : ℝ), 0 < Ψ → 0 < t →
        μ W L {ω | ∃ i j : Fin W,
            t * Ψ < ‖F ω (a, i) (b, j) - if i = j then blockTr (F ω) a b else 0‖} ≤
          μ W L {ω | s * Ψ ^ 2 < ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b} +
            ENNReal.ofReal (C * (W : ℝ) ^ 2 * (s / t ^ 2) ^ p) := by
  obtain ⟨C, hC, hmom⟩ := haar_traceless_moment p
  refine ⟨C, hC, fun W L hW F hFm hFe a b Ψ s t hΨ ht => ?_⟩
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hHSm := averagingHaar_measurable_blockHS2 hFm a b
  by_cases hs : s < 0
  · have hBuniv : {ω | s * Ψ ^ 2 < ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b} = Set.univ := by
      refine Set.eq_univ_of_forall fun ω => ?_
      have h1 : s * Ψ ^ 2 < 0 := mul_neg_of_neg_of_pos hs (by positivity)
      have h2 : 0 ≤ ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b :=
        mul_nonneg (by positivity) (averagingHaar_blockHS2_nonneg _ _ _)
      exact lt_of_lt_of_le h1 h2
    calc _ ≤ (1 : ℝ≥0∞) := prob_le_one
      _ = μ W L {ω | s * Ψ ^ 2 < ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b} := by
          rw [hBuniv]; simp
      _ ≤ _ := le_self_add
  have hs0 : 0 ≤ s := not_lt.mp hs
  -- the sample restricted to `W⁻² ‖G_{ab}‖²_HS ≤ sΨ²`
  have hcm : MeasurableSet {ω : Ω W L | ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b ≤ s * Ψ ^ 2} :=
    measurableSet_le (measurable_const.mul hHSm) measurable_const
  set F' : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := fun ω =>
    if ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b ≤ s * Ψ ^ 2 then F ω else 0 with hF'
  have hF'm : ∀ x y, Measurable fun ω => F' ω x y := by
    intro x y
    have : (fun ω => F' ω x y) = fun ω =>
        if ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b ≤ s * Ψ ^ 2 then F ω x y else 0 := by
      funext ω
      by_cases h : ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b ≤ s * Ψ ^ 2 <;> simp [hF', h]
    rw [this]
    exact Measurable.ite hcm (hFm x y) measurable_const
  have hF'e : ∀ (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W L), F' (conjMap W L U ω) =
      ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) * F' ω *
        star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) := by
    intro U ω
    by_cases h : ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b ≤ s * Ψ ^ 2
    · have h' : ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F (conjMap W L U ω)) a b ≤ s * Ψ ^ 2 := by
        rwa [averagingHaar_blockHS2_equiv hFe]
      simp only [hF', h, h', reduceIte]
      exact hFe U ω
    · have h' : ¬ ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F (conjMap W L U ω)) a b ≤ s * Ψ ^ 2 := by
        rwa [averagingHaar_blockHS2_equiv hFe]
      simp only [hF', h, h', reduceIte, Matrix.mul_zero, Matrix.zero_mul]
  have hHS' : ∀ ω, blockHS2 (F' ω) a b ≤ s * Ψ ^ 2 * (W : ℝ) ^ 2 := by
    intro ω
    by_cases h : ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b ≤ s * Ψ ^ 2
    · simp only [hF', h, reduceIte]
      exact (inv_mul_le_iff₀ (by positivity)).mp h |>.trans (le_of_eq (mul_comm _ _))
    · simp only [hF', h, reduceIte]
      have : blockHS2 (0 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) a b = 0 := by
        simp [blockHS2]
      rw [this]
      positivity
  have hint' : Integrable (fun ω => blockHS2 (F' ω) a b ^ p) (μ W L) := by
    refine Integrable.of_bound (averagingHaar_measurable_blockHS2 hF'm a b |>.pow_const p
      |>.aestronglyMeasurable) ((s * Ψ ^ 2 * (W : ℝ) ^ 2) ^ p) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (averagingHaar_blockHS2_nonneg _ _ _) _)]
    exact pow_le_pow_left₀ (averagingHaar_blockHS2_nonneg _ _ _) (hHS' ω) p
  have hint'' : ∫ ω, blockHS2 (F' ω) a b ^ p ∂(μ W L) ≤ (s * Ψ ^ 2 * (W : ℝ) ^ 2) ^ p := by
    calc ∫ ω, blockHS2 (F' ω) a b ^ p ∂(μ W L) ≤ ∫ _ω, (s * Ψ ^ 2 * (W : ℝ) ^ 2) ^ p ∂(μ W L) :=
          integral_mono hint' (integrable_const _) fun ω =>
            pow_le_pow_left₀ (averagingHaar_blockHS2_nonneg _ _ _) (hHS' ω) p
      _ = _ := by simp
  -- Markov at `tΨ` for each entry of the restricted matrix
  have hMarkov : ∀ i j : Fin W, μ W L {ω | t * Ψ <
      ‖F' ω (a, i) (b, j) - if i = j then blockTr (F' ω) a b else 0‖} ≤
      ENNReal.ofReal (C * (s / t ^ 2) ^ p) := by
    intro i j
    obtain ⟨hI, hB⟩ := hmom W L hW F' hF'm hF'e a b hint' i j
    set f : Ω W L → ℝ := fun ω =>
      ‖F' ω (a, i) (b, j) - if i = j then blockTr (F' ω) a b else 0‖ ^ (2 * p) with hf
    have hc0 : 0 < (t * Ψ) ^ (2 * p) := by positivity
    have hf0 : 0 ≤ᵐ[μ W L] f :=
      Eventually.of_forall fun ω => pow_nonneg (norm_nonneg _) _
    have hMk := mul_meas_ge_le_integral_of_nonneg hf0 hI ((t * Ψ) ^ (2 * p))
    have hsub : {ω | t * Ψ < ‖F' ω (a, i) (b, j) - if i = j then blockTr (F' ω) a b else 0‖} ⊆
        {ω | (t * Ψ) ^ (2 * p) ≤ f ω} := fun ω hω =>
      pow_le_pow_left₀ (mul_pos ht hΨ).le (le_of_lt hω) _
    have hval : C / (W : ℝ) ^ (2 * p) * (s * Ψ ^ 2 * (W : ℝ) ^ 2) ^ p = C * (s * Ψ ^ 2) ^ p := by
      rw [mul_pow, ← pow_mul]
      field_simp
    have hreal : (μ W L).real {ω | (t * Ψ) ^ (2 * p) ≤ f ω} ≤ C * (s / t ^ 2) ^ p := by
      have h1 : (t * Ψ) ^ (2 * p) * (μ W L).real {ω | (t * Ψ) ^ (2 * p) ≤ f ω} ≤
          C * (s * Ψ ^ 2) ^ p := by
        refine hMk.trans (hB.trans ?_)
        rw [← hval]
        exact mul_le_mul_of_nonneg_left hint'' (by positivity)
      have h2 : C * (s / t ^ 2) ^ p * (t * Ψ) ^ (2 * p) = C * (s * Ψ ^ 2) ^ p := by
        rw [div_pow, pow_mul, mul_pow, ← pow_mul]
        field_simp
        ring
      rw [← h2] at h1
      rw [mul_comm] at h1
      exact le_of_mul_le_mul_right h1 hc0
    calc _ ≤ μ W L {ω | (t * Ψ) ^ (2 * p) ≤ f ω} := measure_mono hsub
      _ = ENNReal.ofReal ((μ W L).real {ω | (t * Ψ) ^ (2 * p) ≤ f ω}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  have hsubE : {ω | ∃ i j : Fin W,
        t * Ψ < ‖F ω (a, i) (b, j) - if i = j then blockTr (F ω) a b else 0‖} ⊆
      {ω | s * Ψ ^ 2 < ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b} ∪
        ⋃ q : Fin W × Fin W, {ω | t * Ψ <
          ‖F' ω (a, q.1) (b, q.2) - if q.1 = q.2 then blockTr (F' ω) a b else 0‖} := by
    intro ω hω
    obtain ⟨i, j, hij⟩ := hω
    by_cases h : ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b ≤ s * Ψ ^ 2
    · right
      refine Set.mem_iUnion.mpr ⟨(i, j), ?_⟩
      change t * Ψ < ‖F' ω (a, i) (b, j) - if i = j then blockTr (F' ω) a b else 0‖
      simp only [hF', h, reduceIte]
      exact hij
    · left
      exact not_le.mp h
  calc _ ≤ μ W L ({ω | s * Ψ ^ 2 < ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b} ∪
        ⋃ q : Fin W × Fin W, {ω | t * Ψ <
          ‖F' ω (a, q.1) (b, q.2) - if q.1 = q.2 then blockTr (F' ω) a b else 0‖}) :=
        measure_mono hsubE
    _ ≤ μ W L {ω | s * Ψ ^ 2 < ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b} +
        μ W L (⋃ q : Fin W × Fin W, {ω | t * Ψ <
          ‖F' ω (a, q.1) (b, q.2) - if q.1 = q.2 then blockTr (F' ω) a b else 0‖}) :=
        measure_union_le _ _
    _ ≤ μ W L {ω | s * Ψ ^ 2 < ((W : ℝ) ^ 2)⁻¹ * blockHS2 (F ω) a b} +
        ∑ q : Fin W × Fin W, ENNReal.ofReal (C * (s / t ^ 2) ^ p) :=
        add_le_add le_rfl ((measure_iUnion_fintype_le _ _).trans
          (Finset.sum_le_sum fun q _ => hMarkov q.1 q.2))
    _ = _ := by
        congr 1
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        ring

/-! ### The resolvent `segG` -/

/-- Measurability of the entries of a matrix inverse of a matrix-valued measurable function. -/
private lemma averagingHaar_measurable_det {α : Type*} [MeasurableSpace α] {n : Type*} [Fintype n]
    [DecidableEq n] (M : α → Matrix n n ℂ) (hM : ∀ p q, Measurable fun x => M x p q) :
    Measurable fun x => (M x).det := by
  simp_rw [Matrix.det_apply]
  exact Finset.measurable_sum _ fun σ _ =>
    Measurable.const_smul (Finset.measurable_prod _ fun i _ => hM _ _) _

private lemma averagingHaar_measurable_inv {α : Type*} [MeasurableSpace α] {n : Type*} [Fintype n]
    [DecidableEq n] (M : α → Matrix n n ℂ) (hM : ∀ p q, Measurable fun x => M x p q) (p q : n) :
    Measurable fun x => (M x)⁻¹ p q := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul,
    Ring.inverse_eq_inv']
  refine Measurable.mul (averagingHaar_measurable_det M hM).inv ?_
  refine averagingHaar_measurable_det _ fun r s => ?_
  simp only [Matrix.updateRow_apply]
  by_cases h : r = q
  · simp only [h, ite_true]
    by_cases h2 : s = p <;> simp [h2]
  · simp only [h, ite_false]
    exact hM r s

/-- The entries of `H_u(g)` are continuous in the Gaussian coordinates. -/
private lemma averagingHaar_continuous_flowH (g : ℝ) (W L : ℕ) (u : ℝ) (x y : Fin L × Fin W) :
    Continuous fun ω : Ω W L => flowH g W L u ω x y := by
  have h : ∀ a, Continuous fun ω : Ω W L => gueBlock W L ω a := fun a => by
    refine continuous_matrix fun α β => ?_
    simp only [gueBlock, Matrix.of_apply]
    split_ifs <;> fun_prop
  simp only [flowH, blockFlow, blockV, blockDiagOp, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul]
  refine continuous_const.add (continuous_const.mul ?_)
  by_cases hxy : x.1 = y.1
  · simp only [hxy, ite_true]
    exact (h y.1).matrix_elem x.2 y.2
  · simp only [hxy, ite_false]
    exact continuous_const

/-- The entries of `segG W x` are measurable. -/
private lemma averagingHaar_measurable_segG (W : ℕ) (x : FlowPt × ℝ) (p q : Fin x.1.L × Fin W) :
    Measurable fun ω : Ω W x.1.L => segG W x ω p q := by
  unfold segG resolventMat
  refine averagingHaar_measurable_inv (fun ω : Ω W x.1.L => flowH x.1.g W x.1.L x.1.u ω -
    (((zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re : ℂ) + (x.2 : ℂ) * Complex.I) •
      (1 : Matrix (Fin x.1.L × Fin W) (Fin x.1.L × Fin W) ℂ)) (fun r s => ?_) p q
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  exact (averagingHaar_continuous_flowH _ _ _ _ r s).measurable.sub measurable_const

/-- The resolvent of a conjugate is the conjugate of the resolvent. -/
private lemma averagingHaar_resolventMat_conj {n : Type*} [Fintype n] [DecidableEq n]
    (K B : Matrix n n ℂ) (z : ℂ) (h1 : K * star K = 1) (h2 : star K * K = 1) :
    resolventMat (K * B * star K) z = K * resolventMat B z * star K := by
  have e : K * B * star K - z • (1 : Matrix n n ℂ) = K * (B - z • (1 : Matrix n n ℂ)) * star K := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1]
  have hK : K⁻¹ = star K := Matrix.inv_eq_left_inv h2
  have hK' : (star K)⁻¹ = K := Matrix.inv_eq_left_inv h1
  unfold resolventMat
  rw [e, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hK, hK']
  simp only [Matrix.mul_assoc]

/-- `segG` is equivariant under the common conjugation. -/
private lemma averagingHaar_segG_equiv (W : ℕ) (x : FlowPt × ℝ)
    (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W x.1.L) :
    segG W x (conjMap W x.1.L U ω) =
      ((1 : Matrix (Fin x.1.L) (Fin x.1.L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) * segG W x ω *
        star ((1 : Matrix (Fin x.1.L) (Fin x.1.L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) := by
  have hUU : (U : Matrix (Fin W) (Fin W) ℂ) * star (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Unitary.coe_mul_star_self U
  have hUU' : star (U : Matrix (Fin W) (Fin W) ℂ) * (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  unfold segG
  rw [flowH_conjMap]
  refine averagingHaar_resolventMat_conj _ _ _ ?_ ?_
  · rw [averagingHaar_star_kron, ← Matrix.mul_kronecker_mul, Matrix.mul_one, hUU,
      Matrix.one_kronecker_one]
  · rw [averagingHaar_star_kron, ← Matrix.mul_kronecker_mul, Matrix.mul_one, hUU',
      Matrix.one_kronecker_one]

/-- Lemma 5.9 [gc:lem:residual](ii), (5.30) [gc:eq:haar], for a deterministic `Ψ > 0`: the
second clause of `AveragingInput`, for every base family and every depth (the common Haar
conjugation needs no property of the admissible pairs). -/
theorem averaging_haar (base : ℕ → Set FlowPt) (J : ℕ) :
    ∀ Dom : ℕ → Set (FlowPt × ℝ), (∀ W x, x ∈ Dom W → SegAdm base J W x) →
    ∀ Ψ : ℕ → FlowPt × ℝ → ℝ, (∀ W x, x ∈ Dom W → 0 < Ψ W x) →
    (∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ Dom W, ∀ a b : Fin x.1.L,
      μ W x.1.L {ω | (W : ℝ) ^ ε * Ψ W x ^ 2 < ((W : ℝ) ^ 2)⁻¹ * blockHS2 (segG W x ω) a b} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-D))) →
    ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ Dom W, ∀ a b : Fin x.1.L,
      μ W x.1.L {ω | ∃ i j : Fin W, (W : ℝ) ^ ε * Ψ W x <
        ‖segG W x ω (a, i) (b, j) - if i = j then blockTr (segG W x ω) a b else 0‖} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  intro Dom _ Ψ hΨ hprem ε D hε hD
  obtain ⟨W₁, hW₁⟩ := hprem ε (D + 1) hε (by linarith)
  set p : ℕ := ⌈(D + 3) / ε⌉₊ with hp
  have hpε : D + 3 ≤ p * ε := by
    have h := Nat.le_ceil ((D + 3) / ε)
    calc D + 3 = (D + 3) / ε * ε := by field_simp
      _ ≤ p * ε := mul_le_mul_of_nonneg_right h hε.le
  obtain ⟨C, hC, htail⟩ := haar_traceless_tail p
  refine ⟨max (max W₁ ⌈1 + C⌉₊) 1, fun W hW x hx a b => ?_⟩
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWC : 1 + C ≤ (W : ℝ) :=
    (Nat.le_ceil (1 + C)).trans
      (by exact_mod_cast ((le_max_right _ _).trans (le_max_left _ _)).trans hW)
  have hWW₁ : W₁ ≤ W := ((le_max_left _ _).trans (le_max_left _ _)).trans hW
  have h1 := hW₁ W hWW₁ x hx a b
  have h2 := htail W x.1.L hW1 (segG W x) (averagingHaar_measurable_segG W x)
    (averagingHaar_segG_equiv W x) a b (Ψ W x) ((W : ℝ) ^ ε) ((W : ℝ) ^ ε) (hΨ W x hx)
    (Real.rpow_pos_of_pos hWpos ε)
  refine h2.trans ((add_le_add h1 le_rfl).trans ?_)
  have hq : (W : ℝ) ^ ε / ((W : ℝ) ^ ε) ^ 2 = (W : ℝ) ^ (-ε) := by
    rw [Real.rpow_neg hWpos.le]
    have : (W : ℝ) ^ ε ≠ 0 := (Real.rpow_pos_of_pos hWpos ε).ne'
    field_simp
  have hpow : ((W : ℝ) ^ (-ε)) ^ p = (W : ℝ) ^ (-(p * ε)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]
    congr 1
    ring
  have hmid : (W : ℝ) ^ (2 : ℕ) * (W : ℝ) ^ (-(p * ε)) ≤ (W : ℝ) ^ (-(D + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hWpos]
    exact Real.rpow_le_rpow_of_exponent_le hW1r (by push_cast; linarith)
  have hfin : (W : ℝ) ^ (-(D + 1)) * W = (W : ℝ) ^ (-D) := by
    have : (W : ℝ) ^ (-(D + 1)) * (W : ℝ) ^ (1 : ℝ) = (W : ℝ) ^ (-D) := by
      rw [← Real.rpow_add hWpos]
      congr 1
      ring
    rwa [Real.rpow_one] at this
  have hpos : 0 < (W : ℝ) ^ (-(D + 1)) := Real.rpow_pos_of_pos hWpos _
  rw [← ENNReal.ofReal_add hpos.le (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hq, hpow, ← hfin]
  calc (W : ℝ) ^ (-(D + 1)) + C * (W : ℝ) ^ 2 * (W : ℝ) ^ (-(p * ε))
      = (W : ℝ) ^ (-(D + 1)) + C * ((W : ℝ) ^ (2 : ℕ) * (W : ℝ) ^ (-(p * ε))) := by ring
    _ ≤ (W : ℝ) ^ (-(D + 1)) + C * (W : ℝ) ^ (-(D + 1)) := by
        gcongr
    _ = (1 + C) * (W : ℝ) ^ (-(D + 1)) := by ring
    _ ≤ (W : ℝ) * (W : ℝ) ^ (-(D + 1)) := by gcongr
    _ = _ := by ring

end LSBA
