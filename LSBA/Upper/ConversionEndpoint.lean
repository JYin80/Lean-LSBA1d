import LSBA.Upper.ConversionApriori
import LSBA.Upper.ConversionBoundary
import LSBA.Gauss.BlockWindow

/-!
# Small Green functions across one interval

The transfer input (8.11) [up:eq:input] and the endpoint moment (8.6) [uv:eq:upper-volume-input] at
fixed parameters, and that moment with bound `W^{-K}` from (8.11) [up:eq:input] (proof of
Proposition 8.4(i) [up:prop:conversion]; the paper fixes `K = 2`).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The blocks `V_0, …, V_{n-1}` as a sequence (zero beyond `n`). -/
def seqBlocks {W n : ℕ} (V : Fin n → Matrix (Fin W) (Fin W) ℂ) (k : ℕ) : Matrix (Fin W) (Fin W) ℂ :=
  if h : k < n then V ⟨k, h⟩ else 0

/-- (8.11) [up:eq:input] at fixed `W, g, J, D′` and length `n`:
`sup_{E ∈ J} sup_Φ P(‖D_n(Φ; E)^{-1}‖ > W^{-D′}) ≤ W^{-D′}` over `n` fresh GUE blocks. -/
def TransferInputAt (W : ℕ) (g : ℝ) (J : Set ℝ) (D' : ℝ) (n : ℕ) : Prop :=
  ∀ E ∈ J, ∀ Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ, IsBoundaryFrame Φ →
    (μ W n) {ω | (W : ℝ) ^ (-D') <
      ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ) (seqBlocks (gueBlock W n ω)) n) Φ)⁻¹‖} ≤
      ENNReal.ofReal ((W : ℝ) ^ (-D'))

/-- The endpoint moment bound of (8.6) [uv:eq:upper-volume-input], with general bound `ε`, at
fixed `W, g, J`: `sup_{E ∈ J} sup_{L₀, R₀} 𝔼‖G^{L₀,R₀}_{[0,n]}(0, n; E)‖^s ≤ ε`. -/
def EndpointMomentAt (W : ℕ) (g : ℝ) (J : Set ℝ) (s : ℝ) (n : ℕ) (ε : ℝ) : Prop :=
  ∀ E ∈ J, ∀ L₀ R₀ : Matrix (Fin W) (Fin W) ℂ, L₀.IsHermitian → R₀.IsHermitian →
    ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀) E) 0 (Fin.last n)‖ₑ ^ s
      ∂(μ W (n + 1)) ≤ ENNReal.ofReal ε

/-- The input exponent `D′ = (K + 1)/t + B + 2` of the proof of Proposition 8.4(i)
[up:prop:conversion]. -/
def endpointExponent (K t B : ℝ) : ℝ := (K + 1) / t + B + 2

/-- The reversing window `j ↦ n - j` from `n` blocks into `n + 1` blocks. -/
private def endpointWindow (n : ℕ) : Fin n → Fin (n + 1) := fun j => ⟨n - j.val, by omega⟩

/-- The reversing window is injective. -/
private lemma endpointWindow_injective (n : ℕ) : Function.Injective (endpointWindow n) := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [endpointWindow] at h'
  exact Fin.ext (by have := a.2; have := b.2; omega)

/-- The prefix product `P_m` only reads the blocks `V_0, …, V_{m-1}`. -/
private lemma endpoint_transferProd_congr {W : ℕ} (g : ℝ) (z : ℂ)
    {V V' : ℕ → Matrix (Fin W) (Fin W) ℂ} {m : ℕ} (h : ∀ j < m, V j = V' j) :
    transferProd g z V m = transferProd g z V' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [transferProd]
    rw [h m (Nat.lt_succ_self m), ih fun j hj => h j (by omega)]

/-- The sample of `n` blocks read in the reversing window gives the product of the reversed blocks
`V_n, …, V_1` of (8.14) [eq:c-boundary-comparison]. -/
private lemma endpoint_reverse {W n : ℕ} (g : ℝ) (z : ℂ) (ω : Ω W (n + 1)) :
    transferProd g z (seqBlocks (gueBlock W n (windowSample (endpointWindow n) ω))) n =
      transferProd g z (fun k => gueBlock W (n + 1) ω ⟨n - k, by omega⟩) n := by
  refine endpoint_transferProd_congr g z fun j hj => ?_
  simp only [seqBlocks, hj, dite_true]
  exact gueBlock_windowSample (endpointWindow n) ω ⟨j, hj⟩

private lemma endpoint_measurable_gueBlock_apply {W n : ℕ} (a : Fin n) (α β : Fin W) :
    Measurable fun ω : Ω W n => gueBlock W n ω a α β := by
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs
  · fun_prop
  · fun_prop
  · fun_prop

private lemma endpoint_measurable_inv {m : Type*} [Fintype m] [DecidableEq m] :
    Measurable fun A : Matrix m m ℂ => A⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hd : Measurable fun A : Matrix m m ℂ => A.det :=
    (continuous_id.matrix_det).measurable
  have ha : Measurable fun A : Matrix m m ℂ => A.adjugate i j :=
    (continuous_id.matrix_adjugate).measurable.eval_matrix
  exact (hd.inv).mul ha

private lemma endpoint_blockDiagOp_zero {W n : ℕ} :
    blockDiagOp (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) = 0 := by
  ext p q
  simp [blockDiagOp]

/-- The norm of a block of the resolvent of the path operator is a measurable function of the
sample. -/
private lemma endpoint_measurable_enorm {W n : ℕ} (g : ℝ) (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ)
    (E : ℝ) (x y : Fin n) :
    Measurable fun ω : Ω W n =>
      ‖blockOf (resolventMat (pathOp g (gueBlock W n ω) L₀ R₀) E) x y‖ₑ := by
  have hdecomp : ∀ ω, pathOp g (gueBlock W n ω) L₀ R₀ =
      pathOp g (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) L₀ R₀ +
        (((max 1 g)⁻¹ : ℝ) : ℂ) • blockDiagOp (gueBlock W n ω) := by
    intro ω
    simp only [pathOp, endpoint_blockDiagOp_zero, add_zero, smul_add, Complex.ofReal_inv]
    abel
  simp only [hdecomp]
  set K₀ := pathOp g (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) L₀ R₀
  set c : ℝ := (max 1 g)⁻¹
  have hmat : Measurable fun ω : Ω W n => K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω) -
      (E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) := by
    refine Measurable.of_eval_matrix _ fun p q => ?_
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, blockDiagOp,
      Matrix.of_apply, smul_eq_mul]
    by_cases h : p.1 = q.1
    · simp only [h, ite_true]
      have := endpoint_measurable_gueBlock_apply (W := W) (n := n) q.1 p.2 q.2
      fun_prop
    · simp only [h, ite_false]
      fun_prop
  have hres : Measurable fun ω : Ω W n =>
      resolventMat (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω)) E :=
    endpoint_measurable_inv.comp hmat
  have hblk : Measurable fun X : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ => blockOf X x y := by
    refine Measurable.of_eval_matrix _ fun α β => ?_
    exact measurable_id.eval_matrix (i := (x, α)) (j := (y, β))
  exact continuous_enorm.measurable.comp (hblk.comp hres)

private lemma endpoint_aprioriConst_pos {p : ℝ} (h1 : p < 1) :
    0 < aprioriConst p := by
  unfold aprioriConst
  have : 0 < 1 - p := by linarith
  positivity

/-- `(max{1, g} w²)^t ≤ w^{(B+2) t}`. -/
private lemma endpoint_X_rpow_le {t B g w : ℝ} (ht0 : 0 < t) (hw1 : 1 ≤ w)
    (hgB : max 1 g ≤ w ^ B) :
    (max 1 g * w ^ 2) ^ t ≤ w ^ ((B + 2) * t) := by
  have hw0 : 0 < w := by linarith
  have hX : max 1 g * w ^ 2 ≤ w ^ (B + 2) := by
    rw [Real.rpow_add hw0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right hgB (by positivity)
  have hX0 : 0 ≤ max 1 g * w ^ 2 := by positivity
  calc (max 1 g * w ^ 2) ^ t ≤ (w ^ (B + 2)) ^ t := Real.rpow_le_rpow hX0 hX ht0.le
    _ = w ^ ((B + 2) * t) := (Real.rpow_mul hw0.le _ _).symm

/-- The exponent arithmetic of the proof of Proposition 8.4(i) [up:prop:conversion] with
`D′ = endpointExponent K t B`, `W ≥ 2 C₁ + √C₂` and `max{1, g} ≤ W^B`: the good-event term
`(W^{-D′})^t · 2 C₁ (max{1, g} W²)^t` and the failure-event term
`(C₂ (max{1, g} W²)^{2t})^{1/2} (W^{-D′})^{1/2}` sum to at most `W^{-K}`. -/
private lemma endpoint_real_bounds {t K B g w C₁ C₂ : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2)
    (hK : 0 < K) (hB : 0 < B) (hw1 : 1 ≤ w) (hgB : max 1 g ≤ w ^ B) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hW : 2 * C₁ + Real.sqrt C₂ ≤ w) :
    (w ^ (-endpointExponent K t B)) ^ t *
        (C₁ * (max 1 g * w ^ 2) ^ t + C₁ * (max 1 g * w ^ 2) ^ t) +
      (C₂ * (max 1 g * w ^ 2) ^ (2 * t)) ^ (1 / 2 : ℝ) *
        (w ^ (-endpointExponent K t B)) ^ (1 / 2 : ℝ) ≤ w ^ (-K) := by
  have hw0 : 0 < w := by linarith
  have hX0 : 0 < max 1 g * w ^ 2 := by
    have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  have hXt := endpoint_X_rpow_le ht0 hw1 hgB
  set D' := endpointExponent K t B with hD'
  set a : ℝ := w ^ (-(K + 1)) with ha
  have ha0 : 0 ≤ a := by positivity
  have hDt : D' * t = (K + 1) + (B + 2) * t := by
    rw [hD']; unfold endpointExponent; field_simp; ring
  -- good term
  have hgood : (w ^ (-D')) ^ t * (max 1 g * w ^ 2) ^ t ≤ a := by
    rw [← Real.rpow_mul hw0.le]
    calc w ^ (-D' * t) * (max 1 g * w ^ 2) ^ t ≤ w ^ (-D' * t) * w ^ ((B + 2) * t) :=
          mul_le_mul_of_nonneg_left hXt (by positivity)
      _ = a := by
          rw [← Real.rpow_add hw0, ha]; congr 1; linarith
  -- bad term
  have hbad : (max 1 g * w ^ 2) ^ t * (w ^ (-D')) ^ (1 / 2 : ℝ) ≤ a := by
    rw [← Real.rpow_mul hw0.le]
    calc (max 1 g * w ^ 2) ^ t * w ^ (-D' * (1 / 2)) ≤ w ^ ((B + 2) * t) * w ^ (-D' * (1 / 2)) :=
          mul_le_mul_of_nonneg_right hXt (by positivity)
      _ = w ^ ((B + 2) * t + -D' * (1 / 2)) := (Real.rpow_add hw0 _ _).symm
      _ ≤ a := by
          rw [ha]
          refine Real.rpow_le_rpow_of_exponent_le hw1 ?_
          have e1 : K + 1 ≤ (K + 1) / (2 * t) := by
            rw [le_div_iff₀ (by positivity)]; nlinarith
          have e2 : (B + 2) * t ≤ (B + 2) / 2 := by nlinarith
          have : D' = (K + 1) / t + B + 2 := rfl
          have e3 : (K + 1) / (2 * t) = (K + 1) / t / 2 := by field_simp
          nlinarith
  have hsplit : (C₂ * (max 1 g * w ^ 2) ^ (2 * t)) ^ (1 / 2 : ℝ) =
      Real.sqrt C₂ * (max 1 g * w ^ 2) ^ t := by
    rw [Real.mul_rpow hC₂ (by positivity), ← Real.rpow_mul hX0.le, Real.sqrt_eq_rpow]
    congr 2; ring
  have h1 : (w ^ (-D')) ^ t * (C₁ * (max 1 g * w ^ 2) ^ t + C₁ * (max 1 g * w ^ 2) ^ t) ≤
      2 * C₁ * a := by
    calc _ = 2 * C₁ * ((w ^ (-D')) ^ t * (max 1 g * w ^ 2) ^ t) := by ring
      _ ≤ 2 * C₁ * a := mul_le_mul_of_nonneg_left hgood (by positivity)
  have h2 : (C₂ * (max 1 g * w ^ 2) ^ (2 * t)) ^ (1 / 2 : ℝ) * (w ^ (-D')) ^ (1 / 2 : ℝ) ≤
      Real.sqrt C₂ * a := by
    rw [hsplit]
    calc _ = Real.sqrt C₂ * ((max 1 g * w ^ 2) ^ t * (w ^ (-D')) ^ (1 / 2 : ℝ)) := by ring
      _ ≤ Real.sqrt C₂ * a := mul_le_mul_of_nonneg_left hbad (Real.sqrt_nonneg _)
  have hfin : w * a = w ^ (-K) := by
    rw [ha, show w * w ^ (-(K + 1)) = w ^ (1 + -(K + 1)) by
      rw [Real.rpow_add hw0, Real.rpow_one]]
    congr 1; ring
  calc _ ≤ 2 * C₁ * a + Real.sqrt C₂ * a := add_le_add h1 h2
    _ = (2 * C₁ + Real.sqrt C₂) * a := by ring
    _ ≤ w * a := mul_le_mul_of_nonneg_right hW ha0
    _ = w ^ (-K) := hfin

/-- (8.6) [uv:eq:upper-volume-input] with bound `W^{-K}` from (8.11) [up:eq:input] at one width
`W`. -/
theorem endpointMoment_of_transferInput {t K B : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) (hK : 0 < K)
    (hB : 0 < B) {W : ℕ} (hW : 2 * aprioriConst t + Real.sqrt (aprioriConst (2 * t)) ≤ (W : ℝ))
    {g : ℝ} (hg0 : 0 < g) (hgB : g ≤ (W : ℝ) ^ B) {J : Set ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hin : TransferInputAt W g J (endpointExponent K t B) n) :
    EndpointMomentAt W g J t n ((W : ℝ) ^ (-K)) := by
  intro E hE L₀ R₀ hL hR
  have hC1 : 0 < aprioriConst t := endpoint_aprioriConst_pos (by linarith)
  have hC2 : 0 < aprioriConst (2 * t) := endpoint_aprioriConst_pos (by linarith)
  have hwpos : (0 : ℝ) < W :=
    lt_of_lt_of_le (by have := Real.sqrt_nonneg (aprioriConst (2 * t)); linarith) hW
  have hw1 : (1 : ℝ) ≤ W := by
    have : 0 < W := by exact_mod_cast hwpos
    exact_mod_cast this
  have hmB : max 1 g ≤ (W : ℝ) ^ B := max_le (Real.one_le_rpow hw1 hB.le) hgB
  have hmpos : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hMnn : 0 ≤ (W : ℝ) ^ (-endpointExponent K t B) := by positivity
  have hreal := endpoint_real_bounds ht0 ht1 hK hB hw1 hmB hC1.le hC2.le hW
  set D' := endpointExponent K t B with hD'
  set z : ℂ := ((max 1 g * E / g : ℝ) : ℂ) with hz
  set Φ₀ := (freeConj W 0)ᴴ * phFrame g R₀ with hΦ₀
  have hΦ : IsBoundaryFrame Φ₀ := isBoundaryFrame_phFrame hg0 hR
  set M : ℝ := (W : ℝ) ^ (-D') with hMdef
  -- the failure event of the reversed product
  set bad : Set (Ω W (n + 1)) := {ω | M < ‖(frameD (transferProd g z
    (fun k => gueBlock W (n + 1) ω ⟨n - k, by omega⟩) n) Φ₀)⁻¹‖} with hbad_def
  have hmp := measurePreserving_windowSample W (n + 1) n (endpointWindow_injective n)
  have hbad : μ W (n + 1) bad ≤ ENNReal.ofReal M := by
    have h1 : bad = windowSample (endpointWindow n) ⁻¹' {ω' | M <
        ‖(frameD (transferProd g z (seqBlocks (gueBlock W n ω')) n) Φ₀)⁻¹‖} := by
      ext ω
      simp only [hbad_def, Set.mem_ofPred_eq, Set.mem_preimage, endpoint_reverse]
    rw [h1]
    refine (Measure.le_map_apply hmp.measurable.aemeasurable _).trans ?_
    rw [hmp.map_eq]
    exact hin E hE Φ₀ hΦ
  set B' : Set (Ω W (n + 1)) := toMeasurable (μ W (n + 1)) bad with hB'def
  have hB'm : MeasurableSet B' := measurableSet_toMeasurable _ _
  have hB'sub : bad ⊆ B' := subset_toMeasurable _ _
  have hB'μ : μ W (n + 1) B' = μ W (n + 1) bad := measure_toMeasurable _
  -- the integrands
  set f : Ω W (n + 1) → ℝ≥0∞ := fun ω =>
    ‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀) E) 0 (Fin.last n)‖ₑ ^ t
    with hf
  set a' : Ω W (n + 1) → ℝ≥0∞ := fun ω =>
    ‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀) E) 0 0‖ₑ ^ t with ha'
  set b' : Ω W (n + 1) → ℝ≥0∞ := fun ω =>
    ‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀) E) 1 0‖ₑ ^ t with hb'
  have hfm : Measurable f := (endpoint_measurable_enorm g L₀ R₀ E 0 (Fin.last n)).pow_const t
  have ham : Measurable a' := (endpoint_measurable_enorm g L₀ R₀ E 0 0).pow_const t
  have hbm : Measurable b' := (endpoint_measurable_enorm g L₀ R₀ E 1 0).pow_const t
  -- on the good event: the boundary comparison (8.14) [eq:c-boundary-comparison]
  have hgoodpt : ∀ ω, ω ∉ bad → f ω ≤ ENNReal.ofReal M ^ t * (a' ω + b' ω) := by
    intro ω hω
    have hω' : ‖(frameD (transferProd g z (fun k => gueBlock W (n + 1) ω ⟨n - k, by omega⟩) n)
        Φ₀)⁻¹‖ ≤ M := not_lt.mp hω
    have hcmp := pathOp_boundary_comparison hg0 hn (gueBlock W (n + 1) ω)
      (gueBlock_isHermitian W (n + 1) ω) L₀ R₀ hR E
    have hHerm : (pathOp g (gueBlock W (n + 1) ω) L₀ R₀).IsHermitian :=
      pathOp_isHermitian g (gueBlock_isHermitian W (n + 1) ω) hL hR
    have hswap := blockOf_resolventMat_swap hHerm E 0 (Fin.last n)
    have hnorm : ‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀) E)
        (Fin.last n) 0‖ =
        ‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀) E) 0 (Fin.last n)‖ := by
      rw [hswap, Matrix.l2_opNorm_conjTranspose]
    have h1 : ‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀) E) 0
        (Fin.last n)‖ ≤ M * (‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀) E)
          0 0‖ + ‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀) E) 1 0‖) := by
      rw [← hnorm]
      exact hcmp.trans (mul_le_mul_of_nonneg_right hω' (by positivity))
    have h2 : ‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀) E) 0
        (Fin.last n)‖ₑ ≤ ENNReal.ofReal M *
          (‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀) E) 0 0‖ₑ +
            ‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀) E) 1 0‖ₑ) := by
      rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ← ENNReal.ofReal_mul hMnn]
      exact ENNReal.ofReal_le_ofReal h1
    calc f ω ≤ (ENNReal.ofReal M * (‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀)
            E) 0 0‖ₑ + ‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀) E) 1 0‖ₑ)) ^
          t := ENNReal.rpow_le_rpow h2 ht0.le
      _ = ENNReal.ofReal M ^ t * (‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀)
            E) 0 0‖ₑ + ‖blockOf (resolventMat (pathOp g (gueBlock W (n + 1) ω) L₀ R₀) E) 1 0‖ₑ) ^
          t := ENNReal.mul_rpow_of_nonneg _ _ ht0.le
      _ ≤ ENNReal.ofReal M ^ t * (a' ω + b' ω) :=
          mul_le_mul_right (ENNReal.rpow_add_le_add_rpow _ _ ht0.le (by linarith)) _
  have hpt : ∀ ω, f ω ≤ ENNReal.ofReal M ^ t * (a' ω + b' ω) + B'.indicator f ω := by
    intro ω
    by_cases hω : ω ∈ B'
    · rw [Set.indicator_of_mem hω]
      exact le_add_self
    · rw [Set.indicator_of_notMem hω, add_zero]
      exact hgoodpt ω fun h => hω (hB'sub h)
  have hint : ∫⁻ ω, f ω ∂(μ W (n + 1)) ≤ ENNReal.ofReal M ^ t *
      (∫⁻ ω, a' ω ∂(μ W (n + 1)) + ∫⁻ ω, b' ω ∂(μ W (n + 1))) +
        ∫⁻ ω, B'.indicator f ω ∂(μ W (n + 1)) := by
    calc ∫⁻ ω, f ω ∂(μ W (n + 1)) ≤ ∫⁻ ω, (ENNReal.ofReal M ^ t * (a' ω + b' ω) +
          B'.indicator f ω) ∂(μ W (n + 1)) := lintegral_mono hpt
      _ = ∫⁻ ω, ENNReal.ofReal M ^ t * (a' ω + b' ω) ∂(μ W (n + 1)) +
          ∫⁻ ω, B'.indicator f ω ∂(μ W (n + 1)) :=
          lintegral_add_right _ (hfm.indicator hB'm)
      _ = _ := by
          have hab : Measurable fun ω => a' ω + b' ω := ham.add hbm
          rw [lintegral_const_mul _ hab, lintegral_add_left ham]
  -- on the bad event: Cauchy–Schwarz
  have hCS : ∫⁻ ω, B'.indicator f ω ∂(μ W (n + 1)) ≤
      (∫⁻ ω, f ω ^ (2 : ℝ) ∂(μ W (n + 1))) ^ (1 / 2 : ℝ) * (μ W (n + 1) B') ^ (1 / 2 : ℝ) := by
    have hg : Measurable (B'.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hB'm
    have e1 : B'.indicator f = f * B'.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      by_cases h : ω ∈ B' <;> simp [h]
    have e2 : ∀ ω, (B'.indicator (fun _ => (1 : ℝ≥0∞)) ω) ^ (2 : ℝ) =
        B'.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
      intro ω
      by_cases h : ω ∈ B' <;> simp [h]
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ W (n + 1)) Real.HolderConjugate.two_two
      hfm.aemeasurable hg.aemeasurable
    rw [e1]
    refine this.trans (le_of_eq ?_)
    simp only [e2, lintegral_indicator_const hB'm, one_mul]
  have hsq : ∫⁻ ω, f ω ^ (2 : ℝ) ∂(μ W (n + 1)) ≤
      ENNReal.ofReal (aprioriConst (2 * t) * (max 1 g * (W : ℝ) ^ 2) ^ (2 * t)) := by
    have := pathOp_moment_le g (W := W) (n := n + 1) (p := 2 * t) (by linarith) (by linarith)
      hL hR E 0 (Fin.last n)
    refine le_trans (le_of_eq ?_) this
    refine lintegral_congr fun ω => ?_
    simp only [hf]
    rw [← ENNReal.rpow_mul, mul_comm]
  have ha1 : ∫⁻ ω, a' ω ∂(μ W (n + 1)) ≤
      ENNReal.ofReal (aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t) :=
    pathOp_moment_le g (W := W) (n := n + 1) ht0 (by linarith) hL hR E 0 0
  have hb1 : ∫⁻ ω, b' ω ∂(μ W (n + 1)) ≤
      ENNReal.ofReal (aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t) :=
    pathOp_moment_le g (W := W) (n := n + 1) ht0 (by linarith) hL hR E 1 0
  have hXnn : 0 ≤ (max 1 g * (W : ℝ) ^ 2) ^ t := by positivity
  have hgood_int : ENNReal.ofReal M ^ t * (∫⁻ ω, a' ω ∂(μ W (n + 1)) +
      ∫⁻ ω, b' ω ∂(μ W (n + 1))) ≤ ENNReal.ofReal (M ^ t *
        (aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t +
          aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t)) := by
    have hc : 0 ≤ aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t := mul_nonneg hC1.le hXnn
    rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg hMnn ht0.le,
      ENNReal.ofReal_add hc hc]
    exact mul_le_mul_right (add_le_add ha1 hb1) _
  have hbad_int : (∫⁻ ω, f ω ^ (2 : ℝ) ∂(μ W (n + 1))) ^ (1 / 2 : ℝ) *
      (μ W (n + 1) B') ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal ((aprioriConst (2 * t) *
        (max 1 g * (W : ℝ) ^ 2) ^ (2 * t)) ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ)) := by
    have hc : 0 ≤ aprioriConst (2 * t) * (max 1 g * (W : ℝ) ^ 2) ^ (2 * t) :=
      mul_nonneg hC2.le (by positivity)
    rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg hc (by norm_num),
      ← ENNReal.ofReal_rpow_of_nonneg hMnn (by norm_num)]
    refine mul_le_mul' (ENNReal.rpow_le_rpow hsq (by norm_num))
      (ENNReal.rpow_le_rpow (hB'μ ▸ hbad) (by norm_num))
  have hc1 : 0 ≤ M ^ t * (aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t +
      aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t) := by positivity
  have hc2 : 0 ≤ (aprioriConst (2 * t) * (max 1 g * (W : ℝ) ^ 2) ^ (2 * t)) ^ (1 / 2 : ℝ) *
      M ^ (1 / 2 : ℝ) := by positivity
  calc ∫⁻ ω, f ω ∂(μ W (n + 1))
      ≤ ENNReal.ofReal M ^ t * (∫⁻ ω, a' ω ∂(μ W (n + 1)) + ∫⁻ ω, b' ω ∂(μ W (n + 1))) +
        ∫⁻ ω, B'.indicator f ω ∂(μ W (n + 1)) := hint
    _ ≤ ENNReal.ofReal (M ^ t * (aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t +
          aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t)) +
        ENNReal.ofReal ((aprioriConst (2 * t) * (max 1 g * (W : ℝ) ^ 2) ^ (2 * t)) ^
          (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ)) := add_le_add hgood_int (hCS.trans hbad_int)
    _ = ENNReal.ofReal (M ^ t * (aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t +
          aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t) +
        (aprioriConst (2 * t) * (max 1 g * (W : ℝ) ^ 2) ^ (2 * t)) ^ (1 / 2 : ℝ) *
          M ^ (1 / 2 : ℝ)) := (ENNReal.ofReal_add hc1 hc2).symm
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-K)) := ENNReal.ofReal_le_ofReal hreal

end LSBA
