import LSBA.Upper.LiftDeriv
import LSBA.Gauss.DivergenceCutoff
import LSBA.Upper.CoercivityCutoff
import LSBA.Gauss.GUELaw

/-!
# Lemma 10.1 [lem:c-gaussian-lift]: the general lift

Lemma 10.1 [lem:c-gaussian-lift] with the general bound (10.6) [eq:c-gaussian-general]: for a
cutoff with the properties (10.5) [eq:c-main-cutoff] and the margins (10.14)
[eq:c-main-coercivity] at the pairs `(i_j, k_j)`, every `g > 0`, `|E| ≤ E₀` and every target
`M` of the algebra (10.3) [eq:c-Lie] with `‖M‖_HS = 1` there is a field `Y` in the standard
coordinates of the inputs with `D_Y F = √2 F M` on the support of the cutoff, `χ Y` of class
`C^∞` with Gaussian integration by parts, and `𝔼 |δ_G(χ Y)|² ≤ C W max{g⁻², g⁴}`, through (10.9)
[eq:c-input-divergence]. The reversal of the inputs (proof of Lemma 8.13
[up:lem:density-contraction]) carries cutoffs, fields and bounds to the batch order of
Definition 8.5 [up:def:transfer-operator], with `S* M S ∈ 𝔤` of (10.1) [up:eq:lie-algebra].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- A cut lift of the direction `M` for the matrix function `F` of the inputs: on the support
of `χ`, `Y` moves `F` as `D_Y F = √2 F M`; `χ Y` is `C^∞` and allows Gaussian integration by
parts; and `𝔼 |δ_G(χ Y)|² ≤ b` (Lemma 10.1 [lem:c-gaussian-lift]). -/
def IsCutLift (W q : ℕ) (F : Ω W q → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (b : ℝ) (χ : Ω W q → ℝ)
    (Y : Ω W q → Ω W q) : Prop :=
  (∀ ω ∈ tsupport χ, HasLineDerivAt ℝ F (((Real.sqrt 2 : ℝ) : ℂ) • (F ω * M)) ω (Y ω)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun ω => χ ω • Y ω) ∧ IBPAdmissible (fun ω => χ ω • Y ω) ∧
    ∫⁻ ω, ‖gaussDiv (fun η => χ η • Y η) ω‖ₑ ^ 2 ∂(μ W q) ≤ ENNReal.ofReal b

/-- Lemma 10.1 [lem:c-gaussian-lift], the general bound (10.6) [eq:c-gaussian-general], for the
product `F = T_1 ⋯ T_q`, `q = 1000`, and a given cutoff with the properties (10.5)
[eq:c-main-cutoff] and the margins (10.14) [eq:c-main-coercivity] at `liftLayout`; the constant
depends only on `E₀` and the margins, and every `g > 0` is allowed. -/
theorem gaussian_lift_general (E₀ c₁ ρ K₁ L : ℝ) (hE₀ : 0 < E₀) (hc₁ : 0 < c₁) (hK₁ : 0 < K₁)
    (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ) (c C' : ℝ) (χ : Ω W 1000 → ℝ),
      IsCoercivityCutoff W 1000 liftLayout c₁ ρ K₁ L c C' χ →
      ∀ g E : ℝ, 0 < g → |E| ≤ E₀ →
      ∀ M ∈ lieOmega W, hsSq M = 1 →
        ∃ Y : Ω W 1000 → Ω W 1000,
          IsCutLift W 1000 (fun ω => liftProd g (max 1 g * E / g) (gueBlock W 1000 ω)) M
            (C * (W * max (g⁻¹ ^ 2) (g ^ 4))) χ Y := by
  obtain ⟨CX, hCX, hX⟩ := sum_hsSq_liftField_le E₀ K₁ c₁ hE₀ hK₁ hc₁
  obtain ⟨CD, hCD, hDf⟩ := sum_sq_fderiv_liftField_le E₀ K₁ c₁ hE₀ hK₁ hc₁
  refine ⟨(1 + 2 * L ^ 2) * CX + 2 * CD, by positivity, ?_⟩
  intro W c C' χ hχ g E hg hE M hM hMn
  obtain ⟨hχs, hχc, hχ01, -, hgrad, hmarg⟩ := hχ
  set z := max 1 g * E / g with hz
  set m := max (g⁻¹ ^ 2) (g ^ 4) with hm
  have hm0 : 0 ≤ m := le_max_of_le_right (by positivity)
  set N := {ω : Ω W 1000 | 0 < coerMin (layoutBlocks liftLayout (gueBlock W 1000 ω))} with hN
  obtain ⟨hNo, hYs⟩ := contDiffOn_liftField g z M
  have hcoer : ∀ ω ∈ tsupport χ, c₁ ≤ coerMin (layoutBlocks liftLayout (gueBlock W 1000 ω)) ∧
      ∀ i, ‖gueBlock W 1000 ω i‖ ≤ K₁ := fun ω hω =>
    hmarg ω hω ω (by simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero]; positivity)
  have hherm : ∀ ω (i : Fin 1000), (gueBlock W 1000 ω i).IsHermitian :=
    fun ω i => gueBlock_isHermitian W 1000 ω i
  refine ⟨fun ω => hermCoord W 1000 (liftField g z (gueBlock W 1000 ω) M), ?_⟩
  obtain ⟨h1, h2, h3⟩ := cutField_divergence_le (l := L ^ 2 / W) (a := W * (CX * m))
    (b := CD * W * m) hχs hχc hχ01 hgrad hNo
    (fun ω hω => lt_of_lt_of_le hc₁ (hcoer ω hω).1) hYs
    (fun ω hω => by
      obtain ⟨hc, hK⟩ := hcoer ω hω
      rw [sum_sq_hermCoord (prodDiff_liftField hg hc₁ (hherm ω) hc M).1]
      have := hX W g E (gueBlock W 1000 ω) M hg hE (hherm ω) hK hc
      rw [hMn, mul_one] at this
      exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg W))
    (fun ω hω => by
      obtain ⟨hc, hK⟩ := hcoer ω hω
      have := hDf W g E M ω hg hE hc hK
      rwa [hMn, mul_one] at this)
  refine ⟨fun ω hω => ?_, h1, h2, h3.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · obtain ⟨hc, -⟩ := hcoer ω hω
    obtain ⟨hXh, hXd⟩ := prodDiff_liftField (z := z) hg hc₁ (hherm ω) hc M
    have hfun : (fun t : ℝ => liftProd g z (gueBlock W 1000
        (ω + t • hermCoord W 1000 (liftField g z (gueBlock W 1000 ω) M)))) =
        fun t : ℝ => liftProd g z (gueBlock W 1000 ω +
          t • liftField g z (gueBlock W 1000 ω) M) := by
      funext t
      congr 1
      funext i
      rw [gueBlock_add_smul_hermCoord hXh, Pi.add_apply, Pi.smul_apply, Complex.coe_smul]
    have hd := hasDerivAt_liftProd g z (gueBlock W 1000 ω) (liftField g z (gueBlock W 1000 ω) M)
    rw [hXd hM, Matrix.mul_smul] at hd
    change HasDerivAt _ _ 0
    simp only at hd ⊢
    rw [hfun]
    exact hd
  · have hW : (L ^ 2 / W) * W ≤ L ^ 2 * W := by
      rcases Nat.eq_zero_or_pos W with h0 | h0
      · simp [h0]
      · have : (1 : ℝ) ≤ W := by exact_mod_cast h0
        rw [div_mul_cancel₀ _ (by positivity)]
        nlinarith [sq_nonneg L]
    have hCXm : 0 ≤ CX * m := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hW hCXm]

/-- The layout of the pairs in the batch order: input `k` of the batch is the paper's input
`q - k` (proof of Lemma 8.13 [up:lem:density-contraction]). -/
def batchLayout : Matrix (Fin 128) (Fin 1000) ℝ :=
  pairLayout (fun j => Fin.rev (liftPairI j)) (fun j => Fin.rev (liftPairK j))

/-- The reversal `(k, a, b) ↦ (q - 1 - k, a, b)` of the coordinate labels. -/
private def LiftGeneral_revE (W q : ℕ) : Fin q × Fin W × Fin W ≃ Fin q × Fin W × Fin W :=
  Equiv.prodCongr Fin.revPerm (Equiv.refl _)

/-- The reversal of the inputs as a continuous linear equivalence of the standard
coordinates. -/
private def LiftGeneral_revL (W q : ℕ) : Ω W q ≃L[ℝ] Ω W q :=
  (LinearEquiv.funCongrLeft ℝ ℝ (LiftGeneral_revE W q)).toContinuousLinearEquiv

/-- The equivalence acts as `shiftMap` with the reversal. -/
private theorem LiftGeneral_revL_apply (W q : ℕ) (ω : Ω W q) :
    LiftGeneral_revL W q ω = shiftMap W q Fin.revPerm ω := rfl

/-- The reversal relabels the coordinates by `LiftGeneral_revE`. -/
private theorem LiftGeneral_shift_apply (W q : ℕ) (ω : Ω W q) (x : Fin q × Fin W × Fin W) :
    shiftMap W q Fin.revPerm ω x = ω (LiftGeneral_revE W q x) := rfl

/-- The relabelling is an involution. -/
private theorem LiftGeneral_revE_revE (W q : ℕ) (x : Fin q × Fin W × Fin W) :
    LiftGeneral_revE W q (LiftGeneral_revE W q x) = x := by
  change (Fin.revPerm (Fin.revPerm x.1), x.2) = x
  simp

/-- The reversal is an involution. -/
private theorem LiftGeneral_rev_rev (W q : ℕ) (ω : Ω W q) :
    shiftMap W q Fin.revPerm (shiftMap W q Fin.revPerm ω) = ω := by
  funext x
  simp only [LiftGeneral_shift_apply, LiftGeneral_revE_revE]

/-- The reversal maps the coordinate vector `e_p` to `e_{σ p}`. -/
private theorem LiftGeneral_shift_single (W q : ℕ) (p : Fin q × Fin W × Fin W) :
    shiftMap W q Fin.revPerm (Pi.single p 1) = Pi.single (LiftGeneral_revE W q p) 1 := by
  funext x
  simp only [LiftGeneral_shift_apply, Pi.single_apply]
  congr 1
  apply propext
  constructor
  · rintro rfl
    rw [LiftGeneral_revE_revE]
  · rintro rfl
    rw [LiftGeneral_revE_revE]

/-- The reversal preserves the sup norm. -/
private theorem LiftGeneral_norm_shift (W q : ℕ) (ω : Ω W q) :
    ‖shiftMap W q Fin.revPerm ω‖ = ‖ω‖ := by
  have h : ∀ ω : Ω W q, ‖shiftMap W q Fin.revPerm ω‖ ≤ ‖ω‖ := fun ω =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg ω)).2 fun x => norm_le_pi_norm ω _
  refine le_antisymm (h ω) ?_
  simpa only [LiftGeneral_rev_rev] using h (shiftMap W q Fin.revPerm ω)

/-- The reversal is a measurable embedding. -/
private theorem LiftGeneral_measurableEmbedding (W q : ℕ) :
    MeasurableEmbedding (shiftMap W q Fin.revPerm) := by
  have hm : Measurable (shiftMap W q Fin.revPerm) := (LiftGeneral_revL W q).continuous.measurable
  let e : Ω W q ≃ᵐ Ω W q :=
    { toEquiv := Function.Involutive.toPerm _ (LiftGeneral_rev_rev W q)
      measurable_toFun := hm
      measurable_invFun := hm }
  exact e.measurableEmbedding

/-- `tsupport (f ∘ σ) = σ⁻¹ (tsupport f)`. -/
private theorem LiftGeneral_tsupport {β : Type*} [Zero β] (W q : ℕ) (f : Ω W q → β) :
    tsupport (fun ω => f (shiftMap W q Fin.revPerm ω)) =
      shiftMap W q Fin.revPerm ⁻¹' tsupport f := by
  have h := (LiftGeneral_revL W q).toHomeomorph.preimage_closure (Function.support f)
  exact h.symm

/-- `δ_G` commutes with the reversal: `δ_G(σ ∘ G ∘ σ) = δ_G(G) ∘ σ`. -/
private theorem LiftGeneral_gaussDiv_rev (W q : ℕ) (G : Ω W q → Ω W q) (x : Ω W q) :
    gaussDiv (fun y => shiftMap W q Fin.revPerm (G (shiftMap W q Fin.revPerm y))) x =
      gaussDiv G (shiftMap W q Fin.revPerm x) := by
  unfold gaussDiv
  conv_rhs => rw [← Equiv.sum_comp (LiftGeneral_revE W q)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx : x i = shiftMap W q Fin.revPerm x (LiftGeneral_revE W q i) := by
    rw [LiftGeneral_shift_apply, LiftGeneral_revE_revE]
  rw [hx]
  congr 1
  unfold lineDeriv
  congr 1
  funext t
  simp only [LiftGeneral_shift_apply]
  congr 1
  funext y
  simp only [Pi.add_apply, Pi.smul_apply, LiftGeneral_shift_apply]
  have h := congrFun (LiftGeneral_shift_single W q i) y
  rw [LiftGeneral_shift_apply] at h
  rw [h]

/-- Gaussian integration by parts is preserved by the reversal `G ↦ σ ∘ G ∘ σ`. -/
private theorem LiftGeneral_ibp_rev (W q : ℕ) {G : Ω W q → Ω W q} (hG : IBPAdmissible G) :
    IBPAdmissible (fun y => shiftMap W q Fin.revPerm (G (shiftMap W q Fin.revPerm y))) := by
  set σ := shiftMap W q Fin.revPerm with hσ
  have hmp : MeasurePreserving σ (stdGauss _) (stdGauss _) := measurePreserving_shiftMap W q _
  have hemb := LiftGeneral_measurableEmbedding W q
  have hdiv : gaussDiv (fun y => σ (G (σ y))) = fun x => gaussDiv G (σ x) :=
    funext (LiftGeneral_gaussDiv_rev W q G)
  refine ⟨?_, fun φ hφ => ?_⟩
  · rw [hdiv]
    exact hG.1.comp hemb.measurable
  obtain ⟨hφc, ⟨B, hB⟩, ⟨Cφ, k, hCφ⟩⟩ := hφ
  set σL := LiftGeneral_revL W q
  have hfd : ∀ y, fderiv ℝ (fun y => φ (σ y)) y =
      (fderiv ℝ φ (σ y)).comp (σL : Ω W q →L[ℝ] Ω W q) := fun y =>
    σL.comp_right_fderiv (f := φ) (x := y)
  have hσL : ‖(σL : Ω W q →L[ℝ] Ω W q)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      rw [one_mul]
      exact (LiftGeneral_norm_shift W q v).le
  have hψ : IsIBPTest (fun y => φ (σ y)) := by
    refine ⟨hφc.comp σL.contDiff, ⟨B, fun x => hB _⟩, Cφ, k, fun y => ?_⟩
    rw [hfd]
    calc ‖(fderiv ℝ φ (σ y)).comp (σL : Ω W q →L[ℝ] Ω W q)‖
        ≤ ‖fderiv ℝ φ (σ y)‖ * ‖(σL : Ω W q →L[ℝ] Ω W q)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ φ (σ y)‖ * 1 := by gcongr
      _ ≤ Cφ * (1 + ‖y‖) ^ k := by
          rw [mul_one]
          simpa only [hσ, LiftGeneral_norm_shift] using hCφ (σ y)
  obtain ⟨i1, i2, i3⟩ := hG.2 _ hψ
  have e1 : (fun x => fderiv ℝ φ x (σ (G (σ x)))) =
      (fun y => fderiv ℝ (fun y => φ (σ y)) y (G y)) ∘ σ := by
    funext x
    rw [Function.comp_apply, hfd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LiftGeneral_revL_apply, hσ, LiftGeneral_rev_rev]
  have e2 : (fun x => φ x * gaussDiv (fun y => σ (G (σ y))) x) =
      (fun y => φ (σ y) * gaussDiv G y) ∘ σ := by
    funext x
    rw [Function.comp_apply, hdiv, hσ, LiftGeneral_rev_rev]
  rw [e1, e2]
  exact ⟨(hmp.integrable_comp_emb hemb).2 i1, (hmp.integrable_comp_emb hemb).2 i2,
    (hmp.integral_comp hemb _).trans (i3.trans (hmp.integral_comp hemb _).symm)⟩

/-- Reversal of the inputs carries a cutoff with the margins (10.14) [eq:c-main-coercivity] at
`batchLayout` to one at `liftLayout` (proof of Lemma 8.13 [up:lem:density-contraction]). -/
theorem isCoercivityCutoff_rev {W : ℕ} {c₁ ρ K₁ L c C : ℝ} {χ : Ω W 1000 → ℝ}
    (h : IsCoercivityCutoff W 1000 batchLayout c₁ ρ K₁ L c C χ) :
    IsCoercivityCutoff W 1000 liftLayout c₁ ρ K₁ L c C
      (fun ω => χ (shiftMap W 1000 Fin.revPerm ω)) := by
  obtain ⟨hs, hc, h01, hμ, hg, hm⟩ := h
  set σ := shiftMap W 1000 Fin.revPerm with hσ
  have hik : ∀ a b, liftPairI a ≠ liftPairK b := fun a b h => by
    simp [liftPairI, liftPairK, Fin.ext_iff] at h; omega
  have hlay : ∀ ω', layoutBlocks batchLayout (gueBlock W 1000 (σ ω')) =
      layoutBlocks liftLayout (gueBlock W 1000 ω') := by
    intro ω'
    funext j
    rw [batchLayout, liftLayout, layoutBlocks_pairLayout (fun a b h => hik a b
      (Fin.rev_injective h)), layoutBlocks_pairLayout hik]
    simp only [hσ, gueBlock_shiftMap, Fin.revPerm_apply, Fin.rev_rev]
  refine ⟨hs.comp (LiftGeneral_revL W 1000).contDiff, ?_, fun ω => h01 _, ?_, ?_, ?_⟩
  · unfold HasCompactSupport
    rw [LiftGeneral_tsupport]
    exact ((LiftGeneral_revL W 1000).toHomeomorph.isCompact_preimage).2 hc
  · calc μ W 1000 {ω | χ (σ ω) ≠ 1} = μ W 1000 (σ ⁻¹' {ω | χ ω ≠ 1}) := rfl
      _ = μ W 1000 {ω | χ ω ≠ 1} :=
        (measurePreserving_shiftMap W 1000 _).measure_preimage_emb
          (LiftGeneral_measurableEmbedding W 1000) _
      _ ≤ _ := hμ
  · intro ω
    have hfd : ∀ v, fderiv ℝ (fun ω => χ (shiftMap W 1000 Fin.revPerm ω)) ω v =
        fderiv ℝ χ (shiftMap W 1000 Fin.revPerm ω) (shiftMap W 1000 Fin.revPerm v) := fun v => by
      rw [show (fun ω => χ (shiftMap W 1000 Fin.revPerm ω)) = χ ∘ LiftGeneral_revL W 1000 from rfl,
        (LiftGeneral_revL W 1000).comp_right_fderiv]
      rfl
    refine le_of_eq_of_le ?_ (hg (shiftMap W 1000 Fin.revPerm ω))
    rw [← Equiv.sum_comp (LiftGeneral_revE W 1000)
      (fun k => (fderiv ℝ χ (shiftMap W 1000 Fin.revPerm ω) (Pi.single k 1)) ^ 2)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hfd, LiftGeneral_shift_single]
  · intro ω hω ω' hd
    rw [LiftGeneral_tsupport] at hω
    have hd' : ∑ k, (σ ω' k - σ ω k) ^ 2 ≤ W * ρ ^ 2 := by
      simp only [hσ, LiftGeneral_shift_apply]
      rw [Equiv.sum_comp (LiftGeneral_revE W 1000) (fun k => (ω' k - ω k) ^ 2)]
      exact hd
    obtain ⟨h1, h2⟩ := hm (σ ω) hω (σ ω') hd'
    refine ⟨hlay ω' ▸ h1, fun i => ?_⟩
    simpa only [hσ, gueBlock_shiftMap, Fin.revPerm_apply, Fin.rev_rev] using h2 (Fin.rev i)

/-- Reversal of the inputs (proof of Lemma 8.13 [up:lem:density-contraction]): a cut lift of
`M` for `F = T_1 ⋯ T_q` gives a cut lift of `S* M S` for the batch `S* T_q ⋯ T_1 S` with the
reversed cutoff and field and the same bound, by `measurePreserving_shiftMap`. -/
theorem isCutLift_rev {W q : ℕ} {g E b : ℝ} {M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {χ : Ω W q → ℝ} {Y : Ω W q → Ω W q}
    (h : IsCutLift W q (fun ω => liftProd g (max 1 g * E / g) (gueBlock W q ω)) M b χ Y) :
    IsCutLift W q (batchMat W g E q) ((freeConj W 0)ᴴ * M * freeConj W 0) b
      (fun ω => χ (shiftMap W q Fin.revPerm ω))
      (fun ω => shiftMap W q Fin.revPerm (Y (shiftMap W q Fin.revPerm ω))) := by
  obtain ⟨hD, hS, hI, hB⟩ := h
  set σ := shiftMap W q Fin.revPerm with hσ
  set S := freeConj W 0 with hSdef
  set F := fun ω => liftProd g (max 1 g * E / g) (gueBlock W q ω) with hF
  have hSS : S * Sᴴ = 1 := by
    have h := freeConj_zero_mem_unitaryGroup W
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have hbatch : ∀ ω, batchMat W g E q ω = Sᴴ * F (σ ω) * S := fun ω =>
    batchMat_eq_liftProd W g E q ω
  have hH : (fun ω => χ (σ ω) • σ (Y (σ ω))) = fun ω => σ ((fun η => χ η • Y η) (σ ω)) := rfl
  refine ⟨fun ω hω => ?_, ?_, ?_, ?_⟩
  · rw [LiftGeneral_tsupport] at hω
    have hd : HasDerivAt (fun t : ℝ => F (σ ω + t • Y (σ ω)))
        (((Real.sqrt 2 : ℝ) : ℂ) • (F (σ ω) * M)) 0 := hD (σ ω) hω
    change HasDerivAt (fun t : ℝ => batchMat W g E q (ω + t • σ (Y (σ ω)))) _ 0
    have hfun : (fun t : ℝ => batchMat W g E q (ω + t • σ (Y (σ ω)))) =
        fun t : ℝ => Sᴴ * F (σ ω + t • Y (σ ω)) * S := by
      funext t
      rw [hbatch]
      congr 3
      change σ ω + t • σ (σ (Y (σ ω))) = _
      rw [hσ, LiftGeneral_rev_rev]
    rw [hfun]
    convert (hd.const_mul Sᴴ).mul_const S using 1
    rw [hbatch, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc Sᴴ * F (σ ω) * S * (Sᴴ * M * S) = Sᴴ * F (σ ω) * (S * Sᴴ) * M * S := by
          simp only [Matrix.mul_assoc]
      _ = Sᴴ * (F (σ ω) * M) * S := by
          rw [hSS, Matrix.mul_one, Matrix.mul_assoc Sᴴ]
  · rw [hH]
    exact (LiftGeneral_revL W q).contDiff.comp (hS.comp (LiftGeneral_revL W q).contDiff)
  · rw [hH]
    exact LiftGeneral_ibp_rev W q hI
  · have hdv : (fun ω => ‖gaussDiv (fun ω => χ (σ ω) • σ (Y (σ ω))) ω‖ₑ ^ 2) =
        fun ω => (fun x => ‖gaussDiv (fun η => χ η • Y η) x‖ₑ ^ 2) (σ ω) :=
      funext fun ω => congrArg (fun r : ℝ => ‖r‖ₑ ^ 2)
        (LiftGeneral_gaussDiv_rev W q (fun η => χ η • Y η) ω)
    change ∫⁻ ω, (fun ω => ‖gaussDiv (fun ω => χ (σ ω) • σ (Y (σ ω))) ω‖ₑ ^ 2) ω ∂μ W q ≤ _
    rw [hdv]
    exact ((measurePreserving_shiftMap W q _).lintegral_comp_emb
      (LiftGeneral_measurableEmbedding W q) _).trans_le hB

/-- Lemma 10.1 [lem:c-gaussian-lift], the general bound (10.6) [eq:c-gaussian-general], in the
batch order of Definition 8.5 [up:def:transfer-operator]: for a cutoff with the margins at
`batchLayout`, every `g > 0`, `|E| ≤ E₀` and `M ∈ 𝔤` of (10.1) [up:eq:lie-algebra] with
`‖M‖_HS = 1`, a cut lift with `D_Y T = √2 T M` and `𝔼 |δ_G(χ Y)|² ≤ C W max{g⁻², g⁴}`. -/
theorem gaussian_lift_general_batch (E₀ c₁ ρ K₁ L : ℝ) (hE₀ : 0 < E₀) (hc₁ : 0 < c₁)
    (hK₁ : 0 < K₁) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ) (c C' : ℝ) (χ : Ω W 1000 → ℝ),
      IsCoercivityCutoff W 1000 batchLayout c₁ ρ K₁ L c C' χ →
      ∀ g E : ℝ, 0 < g → |E| ≤ E₀ →
      ∀ M ∈ lieJ W, hsSq M = 1 →
        ∃ Y : Ω W 1000 → Ω W 1000,
          IsCutLift W 1000 (batchMat W g E 1000) M (C * (W * max (g⁻¹ ^ 2) (g ^ 4))) χ Y := by
  obtain ⟨C, hC, hlift⟩ := gaussian_lift_general E₀ c₁ ρ K₁ L hE₀ hc₁ hK₁ hL
  refine ⟨C, hC, fun W c C' χ hχ g E hg hE M hM hMn => ?_⟩
  set S := freeConj W 0 with hSdef
  have hu := freeConj_zero_mem_unitaryGroup W
  have hSS : S * Sᴴ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu
    exact hu
  have hSS' : Sᴴ * S = 1 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
    exact hu
  have hback : Sᴴ * (S * M * Sᴴ) * S = M := by
    calc Sᴴ * (S * M * Sᴴ) * S = (Sᴴ * S) * M * (Sᴴ * S) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hSS', Matrix.one_mul, Matrix.mul_one]
  obtain ⟨hlie, hhs, -, -⟩ := conj_freeConj_lie (S * M * Sᴴ)
  rw [hback] at hlie hhs
  obtain ⟨Y, hY⟩ := hlift W c C' _ (isCoercivityCutoff_rev hχ) g E hg hE (S * M * Sᴴ)
    (hlie.1 hM) (hhs.symm.trans hMn)
  have h := isCutLift_rev hY
  rw [hback] at h
  have hχχ : (fun ω => χ (shiftMap W 1000 Fin.revPerm (shiftMap W 1000 Fin.revPerm ω))) = χ :=
    funext fun ω => by rw [LiftGeneral_rev_rev]
  rw [hχχ] at h
  exact ⟨_, h⟩

end LSBA
