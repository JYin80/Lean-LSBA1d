import LSBA.Upper.ConversionEndpoint
import LSBA.Transfer.PathSchur

/-!
# Decay on intervals

(E.14) [eq:c-interval]: fractional moments of `G_Γ(x, y)` decay like `exp(−(2 log W/(n₀+1))|x − y|)`
from the endpoint moment, by the finite-volume iteration with conditioning on the exterior of each
interval (proof of Proposition 8.2 [up:prop:fr-concentration], Appendix E.2
[app:finite-volume-criterion]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The block diagonal operator with zero blocks is zero. -/
private lemma interval_blockDiagOp_zero {W n : ℕ} :
    blockDiagOp (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) = 0 := by
  ext p q
  simp [blockDiagOp]

/-- The path operator with zero shifts is the free part plus the scaled diagonal block potential. -/
private lemma interval_pathOp_decomp (g : ℝ) {W n : ℕ} (ω : Ω W n) :
    pathOp g (gueBlock W n ω) 0 0 =
      pathOp g (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) 0 0 +
        (((max 1 g)⁻¹ : ℝ) : ℂ) • blockDiagOp (gueBlock W n ω) := by
  simp only [pathOp, interval_blockDiagOp_zero, add_zero, smul_add, Complex.ofReal_inv,
    ite_self]

/-- The `x, y` block norm to the power `t` of the resolvent of the path operator is a measurable
function of the sample. -/
private lemma interval_measurable_enorm {W n : ℕ} (g t E : ℝ) (x y : Fin n) :
    Measurable fun ω : Ω W n =>
      ‖blockOf (resolventMat (pathOp g (gueBlock W n ω) 0 0) E) x y‖ₑ ^ t := by
  have h := measurable_resolventMat_gueBlock (W := W) (n := n)
    (pathOp g (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) 0 0) ((max 1 g)⁻¹) (E : ℂ)
  have hblk : Measurable fun X : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ => blockOf X x y := by
    refine Measurable.of_eval_matrix _ fun α β => ?_
    exact measurable_id.eval_matrix (i := (x, α)) (j := (y, β))
  simp only [interval_pathOp_decomp]
  exact (continuous_enorm.measurable.comp (hblk.comp h)).pow_const t

/-- The determinant of `pathOp - E` over the Dirichlet path of GUE blocks is a.s. nonzero. -/
private lemma interval_ae_det (g : ℝ) (W n : ℕ) (E : ℝ) :
    ∀ᵐ ω ∂(μ W n), (pathOp g (gueBlock W n ω) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)).det ≠ 0 := by
  have hm : (max 1 g)⁻¹ ≠ 0 := inv_ne_zero (lt_of_lt_of_le one_pos (le_max_left 1 g)).ne'
  filter_upwards [ae_det_ne_zero_gueBlock
    (pathOp g (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) 0 0) hm (E : ℂ)] with ω hω
  rwa [interval_pathOp_decomp]

/-- A real multiple of a Hermitian matrix is Hermitian. -/
private lemma interval_isHermitian_neg_smul {W : ℕ} {r : ℝ} {M : Matrix (Fin W) (Fin W) ℂ}
    (hM : M.IsHermitian) : (-((r : ℝ) : ℂ) • M).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hM.eq]
  simp [star_neg]

/-- The shift induced from the left by a path of Hermitian blocks is Hermitian. -/
private lemma interval_shiftFromLeft_isHermitian (g : ℝ) {W n : ℕ}
    {V : Fin n → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ a, (V a).IsHermitian) (E : ℝ) :
    (shiftFromLeft g V 0 E).IsHermitian := by
  unfold shiftFromLeft
  split_ifs with h
  · have hH := pathOp_isHermitian g hV Matrix.isHermitian_zero Matrix.isHermitian_zero
    have hsw := blockOf_resolventMat_swap hH E ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩
    exact interval_isHermitian_neg_smul hsw.symm
  · exact Matrix.isHermitian_zero

/-- The shift induced from the right by a path of Hermitian blocks is Hermitian. -/
private lemma interval_shiftFromRight_isHermitian (g : ℝ) {W n : ℕ}
    {V : Fin n → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ a, (V a).IsHermitian) (E : ℝ) :
    (shiftFromRight g V 0 E).IsHermitian := by
  unfold shiftFromRight
  split_ifs with h
  · have hH := pathOp_isHermitian g hV Matrix.isHermitian_zero Matrix.isHermitian_zero
    have hsw := blockOf_resolventMat_swap hH E ⟨0, h⟩ ⟨0, h⟩
    exact interval_isHermitian_neg_smul hsw.symm
  · exact Matrix.isHermitian_zero

/-- Pointwise form of the interval split: the block norm to the power `t` is at most the product
of the norms of the two factors, since `g / max{1, g} ≤ 1`. -/
private lemma interval_split_enorm_le {t g : ℝ} (ht0 : 0 < t) (hg0 : 0 < g) {W : ℕ}
    (p n₀ q : ℕ) (hq : 0 < q) (V : Fin (p + (n₀ + 1) + q) → Matrix (Fin W) (Fin W) ℂ) (E : ℝ)
    (hL : (pathOp g (V ∘ Fin.castAdd q ∘ Fin.castAdd (n₀ + 1)) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ)).det ≠ 0)
    (hR : (pathOp g (V ∘ Fin.natAdd (p + (n₀ + 1))) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ)).det ≠ 0) (j : Fin q) :
    ‖blockOf (resolventMat (pathOp g V 0 0) E) (Fin.castAdd q (Fin.natAdd p 0))
        (Fin.natAdd (p + (n₀ + 1)) j)‖ₑ ^ t ≤
      ‖blockOf (resolventMat
          (pathOp g (V ∘ Fin.castAdd q ∘ Fin.natAdd p)
            (shiftFromLeft g (V ∘ Fin.castAdd q ∘ Fin.castAdd (n₀ + 1)) 0 E)
            (shiftFromRight g (V ∘ Fin.natAdd (p + (n₀ + 1))) 0 E)) E) 0 (Fin.last n₀)‖ₑ ^ t *
        ‖blockOf (resolventMat (pathOp g (V ∘ Fin.natAdd (p + (n₀ + 1))) 0 0) E) ⟨0, hq⟩ j‖ₑ ^
          t := by
  rw [pathOp_interval_split g hq V E hL hR j]
  set A := blockOf (resolventMat
          (pathOp g (V ∘ Fin.castAdd q ∘ Fin.natAdd p)
            (shiftFromLeft g (V ∘ Fin.castAdd q ∘ Fin.castAdd (n₀ + 1)) 0 E)
            (shiftFromRight g (V ∘ Fin.natAdd (p + (n₀ + 1))) 0 E)) E) 0 (Fin.last n₀) with hA
  set B := blockOf (resolventMat (pathOp g (V ∘ Fin.natAdd (p + (n₀ + 1))) 0 0) E) ⟨0, hq⟩ j
    with hB
  have hm : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left 1 g)
  have hr0 : 0 ≤ g / max 1 g := div_nonneg hg0.le hm.le
  have hr1 : g / max 1 g ≤ 1 := (div_le_one hm).mpr (le_max_right 1 g)
  have hnorm : ‖-((g / max 1 g : ℝ) : ℂ) • (A * B)‖ ≤ ‖A‖ * ‖B‖ := by
    rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hr0]
    calc g / max 1 g * ‖A * B‖ ≤ 1 * ‖A * B‖ := mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)
      _ ≤ ‖A‖ * ‖B‖ := by rw [one_mul]; exact norm_mul_le _ _
  have h2 : ‖-((g / max 1 g : ℝ) : ℂ) • (A * B)‖ₑ ≤ ‖A‖ₑ * ‖B‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hnorm
  calc ‖-((g / max 1 g : ℝ) : ℂ) • (A * B)‖ₑ ^ t ≤ (‖A‖ₑ * ‖B‖ₑ) ^ t :=
        ENNReal.rpow_le_rpow h2 ht0.le
    _ = ‖A‖ₑ ^ t * ‖B‖ₑ ^ t := ENNReal.mul_rpow_of_nonneg _ _ ht0.le

/-- One step of the interval iteration (proof of Proposition 8.2
[up:prop:fr-concentration]): conditioning on the exterior of the window `Λ = [p, p + n₀]` and using
the
endpoint moment on `Λ` at the shifts induced by the exterior, the `t`-th moment of
`G(p, p + n₀ + 1 + j)` on the path of `p + (n₀ + 1) + q` blocks is at most `ε` times that of
`G(0, j)` on the right path of `q` blocks. -/
private lemma interval_step {t g : ℝ} (ht0 : 0 < t) (hg0 : 0 < g) {W : ℕ} {J : Set ℝ} {n₀ : ℕ}
    {ε : ℝ} (hEP : EndpointMomentAt W g J t n₀ ε) {E : ℝ} (hE : E ∈ J) (p : ℕ) {q : ℕ}
    (hq : 0 < q) (j : Fin q) :
    ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W (p + (n₀ + 1) + q) ω) 0 0) E)
        (Fin.castAdd q (Fin.natAdd p 0)) (Fin.natAdd (p + (n₀ + 1)) j)‖ₑ ^ t
        ∂(μ W (p + (n₀ + 1) + q)) ≤
      ENNReal.ofReal ε * ∫⁻ ω', ‖blockOf (resolventMat (pathOp g (gueBlock W q ω') 0 0) E)
        ⟨0, hq⟩ j‖ₑ ^ t ∂(μ W q) := by
  set s : Fin (n₀ + 1) → Fin (p + (n₀ + 1) + q) := fun i => Fin.castAdd q (Fin.natAdd p i)
    with hs_def
  have hs : Function.Injective s := (Fin.castAdd_injective _ _).comp (Fin.natAdd_injective _ _)
  set sL : Fin p → Fin (p + (n₀ + 1) + q) := fun i => Fin.castAdd q (Fin.castAdd (n₀ + 1) i)
    with hsL_def
  have hsL : Function.Injective sL :=
    (Fin.castAdd_injective _ _).comp (Fin.castAdd_injective _ _)
  set sR : Fin q → Fin (p + (n₀ + 1) + q) := Fin.natAdd (p + (n₀ + 1)) with hsR_def
  have hsR : Function.Injective sR := Fin.natAdd_injective _ _
  have hnotL : ∀ i, sL i ∉ Set.range s := by
    rintro i ⟨i', hi'⟩
    have := congrArg Fin.val hi'
    simp only [hs_def, hsL_def, Fin.val_castAdd, Fin.val_natAdd] at this
    have := i.isLt
    omega
  have hnotR : ∀ i, sR i ∉ Set.range s := by
    rintro i ⟨i', hi'⟩
    have := congrArg Fin.val hi'
    simp only [hs_def, hsR_def, Fin.val_castAdd, Fin.val_natAdd] at this
    have := i'.isLt
    omega
  have hLjoin : ∀ (v : Ω W (n₀ + 1)) e,
      windowSample sL (windowJoin s v e) = windowSample sL (windowJoin s 0 e) := by
    intro v e
    funext pp
    have h := hnotL pp.1
    simp [windowSample, windowJoin, h]
  have hRjoin : ∀ (v : Ω W (n₀ + 1)) e,
      windowSample sR (windowJoin s v e) = windowSample sR (windowJoin s 0 e) := by
    intro v e
    funext pp
    have h := hnotR pp.1
    simp [windowSample, windowJoin, h]
  set Good : Ω W (p + (n₀ + 1) + q) → Prop := fun ω =>
    (pathOp g (gueBlock W (p + (n₀ + 1) + q) ω ∘ Fin.castAdd q ∘ Fin.castAdd (n₀ + 1)) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin p × Fin W) (Fin p × Fin W) ℂ)).det ≠ 0 ∧
    (pathOp g (gueBlock W (p + (n₀ + 1) + q) ω ∘ Fin.natAdd (p + (n₀ + 1))) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin q × Fin W) (Fin q × Fin W) ℂ)).det ≠ 0 with hGood_def
  have hGood : ∀ᵐ ω ∂(μ W (p + (n₀ + 1) + q)), Good ω := by
    have h1 := (measurePreserving_windowSample W (p + (n₀ + 1) + q) p
      hsL).quasiMeasurePreserving.ae (interval_ae_det g W p E)
    have h2 := (measurePreserving_windowSample W (p + (n₀ + 1) + q) q
      hsR).quasiMeasurePreserving.ae (interval_ae_det g W q E)
    filter_upwards [h1, h2] with ω h1 h2
    exact ⟨h1, h2⟩
  have hBad0 : μ W (p + (n₀ + 1) + q) {ω | ¬ Good ω} = 0 := ae_iff.mp hGood
  set B' := toMeasurable (μ W (p + (n₀ + 1) + q)) {ω | ¬ Good ω} with hB'def
  have hB'm : MeasurableSet B' := measurableSet_toMeasurable _ _
  have hB'sub : {ω | ¬ Good ω} ⊆ B' := subset_toMeasurable _ _
  have hB'0 : μ W (p + (n₀ + 1) + q) B' = 0 := by rw [hB'def, measure_toMeasurable]; exact hBad0
  set Fx : Ω W (p + (n₀ + 1) + q) → ℝ≥0∞ := fun ω =>
    ‖blockOf (resolventMat (pathOp g (gueBlock W (p + (n₀ + 1) + q) ω) 0 0) E)
        (Fin.castAdd q (Fin.natAdd p 0)) (Fin.natAdd (p + (n₀ + 1)) j)‖ₑ ^ t with hFx_def
  have hFx : Measurable Fx := interval_measurable_enorm g t E _ _
  have hF : Measurable (B'ᶜ.indicator Fx) := hFx.indicator hB'm.compl
  have h1 : ∫⁻ ω, Fx ω ∂(μ W (p + (n₀ + 1) + q)) =
      ∫⁻ ω, B'ᶜ.indicator Fx ω ∂(μ W (p + (n₀ + 1) + q)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hB'0] with ω hω
    rw [Set.indicator_of_mem (Set.mem_compl hω)]
  set Rg : Ω W q → ℝ≥0∞ := fun ω' =>
    ‖blockOf (resolventMat (pathOp g (gueBlock W q ω') 0 0) E) ⟨0, hq⟩ j‖ₑ ^ t with hRg_def
  have hRg : Measurable Rg := interval_measurable_enorm g t E _ _
  have hRfin : ∀ ω', Rg ω' ≠ ⊤ := fun ω' =>
    ENNReal.rpow_ne_top_of_nonneg ht0.le (by rw [← ofReal_norm]; exact ENNReal.ofReal_ne_top)
  have hmpR := measurePreserving_windowSample W (p + (n₀ + 1) + q) q hsR
  have hRW : Measurable fun ω => Rg (windowSample sR ω) := hRg.comp hmpR.measurable
  have hpt : ∀ e v, B'ᶜ.indicator Fx (windowJoin s v e) ≤
      ‖blockOf (resolventMat (pathOp g (gueBlock W (n₀ + 1) v)
        (shiftFromLeft g (gueBlock W p (windowSample sL (windowJoin s 0 e))) 0 E)
        (shiftFromRight g (gueBlock W q (windowSample sR (windowJoin s 0 e))) 0 E)) E) 0
          (Fin.last n₀)‖ₑ ^ t * Rg (windowSample sR (windowJoin s 0 e)) := by
    intro e v
    by_cases hmem : windowJoin s v e ∈ B'
    · rw [Set.indicator_of_notMem (by simpa using hmem)]
      exact bot_le
    · rw [Set.indicator_of_mem (show windowJoin s v e ∈ B'ᶜ from hmem)]
      have hG : Good (windowJoin s v e) := by
        by_contra hc
        exact hmem (hB'sub hc)
      obtain ⟨hL, hR⟩ := hG
      have key := interval_split_enorm_le ht0 hg0 p n₀ q hq
        (gueBlock W (p + (n₀ + 1) + q) (windowJoin s v e)) E hL hR j
      have eV : gueBlock W (p + (n₀ + 1) + q) (windowJoin s v e) ∘ Fin.castAdd q ∘ Fin.natAdd p =
          gueBlock W (n₀ + 1) v := by
        funext i
        exact gueBlock_windowJoin_apply hs v e i
      have eL : gueBlock W (p + (n₀ + 1) + q) (windowJoin s v e) ∘ Fin.castAdd q ∘
          Fin.castAdd (n₀ + 1) = gueBlock W p (windowSample sL (windowJoin s 0 e)) := by
        rw [← hLjoin v e]
        rfl
      have eR : gueBlock W (p + (n₀ + 1) + q) (windowJoin s v e) ∘ Fin.natAdd (p + (n₀ + 1)) =
          gueBlock W q (windowSample sR (windowJoin s 0 e)) := by
        rw [← hRjoin v e]
        rfl
      rw [eV, eL, eR] at key
      exact key
  have hinner : ∀ e, ∫⁻ v, B'ᶜ.indicator Fx (windowJoin s v e) ∂(μ W (n₀ + 1)) ≤
      ENNReal.ofReal ε * Rg (windowSample sR (windowJoin s 0 e)) := by
    intro e
    have hLh := interval_shiftFromLeft_isHermitian g (E := E)
      (V := gueBlock W p (windowSample sL (windowJoin s 0 e)))
      (fun a => gueBlock_isHermitian _ _ _ a)
    have hRh := interval_shiftFromRight_isHermitian g (E := E)
      (V := gueBlock W q (windowSample sR (windowJoin s 0 e)))
      (fun a => gueBlock_isHermitian _ _ _ a)
    calc ∫⁻ v, B'ᶜ.indicator Fx (windowJoin s v e) ∂(μ W (n₀ + 1))
        ≤ ∫⁻ v, ‖blockOf (resolventMat (pathOp g (gueBlock W (n₀ + 1) v)
          (shiftFromLeft g (gueBlock W p (windowSample sL (windowJoin s 0 e))) 0 E)
          (shiftFromRight g (gueBlock W q (windowSample sR (windowJoin s 0 e))) 0 E)) E) 0
            (Fin.last n₀)‖ₑ ^ t * Rg (windowSample sR (windowJoin s 0 e)) ∂(μ W (n₀ + 1)) :=
          lintegral_mono (hpt e)
      _ = (∫⁻ v, ‖blockOf (resolventMat (pathOp g (gueBlock W (n₀ + 1) v)
          (shiftFromLeft g (gueBlock W p (windowSample sL (windowJoin s 0 e))) 0 E)
          (shiftFromRight g (gueBlock W q (windowSample sR (windowJoin s 0 e))) 0 E)) E) 0
            (Fin.last n₀)‖ₑ ^ t ∂(μ W (n₀ + 1))) *
            Rg (windowSample sR (windowJoin s 0 e)) := lintegral_mul_const' _ _ (hRfin _)
      _ ≤ ENNReal.ofReal ε * Rg (windowSample sR (windowJoin s 0 e)) :=
          mul_le_mul_left (hEP E hE _ _ hLh hRh) _
  have hfold : ∫⁻ e, Rg (windowSample sR (windowJoin s 0 e)) ∂(stdGauss
      {p' : Fin (p + (n₀ + 1) + q) × Fin W × Fin W // p'.1 ∉ Set.range s}) =
      ∫⁻ ω', Rg ω' ∂(μ W q) := by
    rw [← hmpR.lintegral_comp hRg, lintegral_windowJoin W (p + (n₀ + 1) + q) (n₀ + 1) hs hRW]
    refine lintegral_congr fun e => ?_
    simp only [hRjoin _ e]
    rw [lintegral_const, measure_univ, mul_one]
  rw [h1, lintegral_windowJoin W (p + (n₀ + 1) + q) (n₀ + 1) hs hF]
  refine le_trans (lintegral_mono hinner) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hfold]

/-- The iteration in the proof of Proposition 8.2 [up:prop:fr-concentration]: if the two
blocks `a ≤ b` are at distance at least `k (n₀ + 1)`, then
`𝔼‖G(a, b)‖^t ≤ C_t (max{1, g} W²)^t (W^{-2})^k`, with `W^{-2}` the endpoint moment bound. -/
private lemma interval_claim {t g : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hg0 : 0 < g) {W : ℕ}
    {J : Set ℝ} {n₀ : ℕ} (hEP : EndpointMomentAt W g J t n₀ ((W : ℝ) ^ (-2 : ℝ))) {E : ℝ}
    (hE : E ∈ J) (k : ℕ) :
    ∀ (N a b : ℕ) (ha : a < N) (hb : b < N), a + k * (n₀ + 1) ≤ b →
      ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W N ω) 0 0) E) ⟨a, ha⟩ ⟨b, hb⟩‖ₑ ^ t
          ∂(μ W N) ≤
        ENNReal.ofReal (aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t *
          ((W : ℝ) ^ (-2 : ℝ)) ^ k) := by
  induction k with
  | zero =>
    intro N a b ha hb _
    simpa using pathOp_moment_le g ht0 ht1 Matrix.isHermitian_zero Matrix.isHermitian_zero E
      ⟨a, ha⟩ ⟨b, hb⟩
  | succ k ih =>
    intro N a b ha hb hab
    rw [add_mul, one_mul] at hab
    obtain ⟨q, rfl⟩ : ∃ q, N = a + (n₀ + 1) + q := ⟨N - (a + (n₀ + 1)), by omega⟩
    have hq : 0 < q := by omega
    set j : Fin q := ⟨b - (a + (n₀ + 1)), by omega⟩ with hj
    have hx : (⟨a, ha⟩ : Fin (a + (n₀ + 1) + q)) =
        Fin.castAdd q (Fin.natAdd a (0 : Fin (n₀ + 1))) := Fin.ext (by simp)
    have hy : (⟨b, hb⟩ : Fin (a + (n₀ + 1) + q)) = Fin.natAdd (a + (n₀ + 1)) j :=
      Fin.ext (by simp [hj]; omega)
    rw [hx, hy]
    refine (interval_step ht0 hg0 hEP hE a hq j).trans ?_
    have ih' := ih q 0 j.val hq j.isLt (by simp [hj]; omega)
    simp only [Fin.eta] at ih'
    have hε : 0 ≤ (W : ℝ) ^ (-2 : ℝ) := by positivity
    calc ENNReal.ofReal ((W : ℝ) ^ (-2 : ℝ)) * ∫⁻ ω', ‖blockOf (resolventMat
          (pathOp g (gueBlock W q ω') 0 0) E) ⟨0, hq⟩ j‖ₑ ^ t ∂(μ W q)
        ≤ ENNReal.ofReal ((W : ℝ) ^ (-2 : ℝ)) * ENNReal.ofReal (aprioriConst t *
            (max 1 g * (W : ℝ) ^ 2) ^ t * ((W : ℝ) ^ (-2 : ℝ)) ^ k) :=
          mul_le_mul_right ih' _
      _ = ENNReal.ofReal (aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t *
            ((W : ℝ) ^ (-2 : ℝ)) ^ (k + 1)) := by
          rw [← ENNReal.ofReal_mul hε]
          congr 1
          ring

/-- `(W^{-2})^{⌊d/(n₀+1)⌋} ≤ W² exp(-(2 log W/(n₀+1)) d)` for `W ≥ 1`. -/
private lemma interval_exponent_le {w : ℝ} (hw : 1 ≤ w) (a d : ℕ) :
    (w ^ (-2 : ℝ)) ^ (d / (a + 1)) ≤
      w ^ (2 : ℝ) * Real.exp (-(2 * Real.log w / ((a : ℝ) + 1)) * (d : ℝ)) := by
  have hw0 : 0 < w := by linarith
  have hL : 0 ≤ Real.log w := Real.log_nonneg hw
  set k := d / (a + 1) with hk
  have hd1 : (a + 1) * k + d % (a + 1) = d := Nat.div_add_mod d (a + 1)
  have hd2 : d % (a + 1) < a + 1 := Nat.mod_lt _ (Nat.succ_pos a)
  have hlt : d < (k + 1) * (a + 1) := by
    have : (k + 1) * (a + 1) = (a + 1) * k + (a + 1) := by ring
    omega
  have hdR : (d : ℝ) / ((a : ℝ) + 1) ≤ k + 1 := by
    rw [div_le_iff₀ (by positivity)]
    exact_mod_cast hlt.le
  have e1 : w ^ (-2 : ℝ) = Real.exp (Real.log w * (-2)) := Real.rpow_def_of_pos hw0 _
  have e2 : w ^ (2 : ℝ) = Real.exp (Real.log w * 2) := Real.rpow_def_of_pos hw0 _
  rw [e1, e2, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have e3 : -(2 * Real.log w / ((a : ℝ) + 1)) * (d : ℝ) =
      -2 * Real.log w * ((d : ℝ) / ((a : ℝ) + 1)) := by ring
  rw [e3]
  nlinarith [mul_nonneg hL (sub_nonneg.2 hdR)]

/-- The constant `C_p` of (8.7) [eq:c-apriori] is positive for `p < 1`. -/
private lemma interval_aprioriConst_pos {p : ℝ} (h1 : p < 1) : 0 < aprioriConst p := by
  unfold aprioriConst
  have : 0 < 1 - p := by linarith
  positivity

/-- `(max{1, g} w²)^t ≤ w^{(B+2) t}` when `max{1, g} ≤ w^B` and `w ≥ 1`. -/
private lemma interval_X_rpow_le {t B g w : ℝ} (ht0 : 0 < t) (hw1 : 1 ≤ w)
    (hgB : max 1 g ≤ w ^ B) : (max 1 g * w ^ 2) ^ t ≤ w ^ ((B + 2) * t) := by
  have hw0 : 0 < w := by linarith
  have hX : max 1 g * w ^ 2 ≤ w ^ (B + 2) := by
    rw [Real.rpow_add hw0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right hgB (by positivity)
  have hX0 : 0 ≤ max 1 g * w ^ 2 := by positivity
  calc (max 1 g * w ^ 2) ^ t ≤ (w ^ (B + 2)) ^ t := Real.rpow_le_rpow hX0 hX ht0.le
    _ = w ^ ((B + 2) * t) := (Real.rpow_mul hw0.le _ _).symm

/-- The decay (E.14) [eq:c-interval] for `x ≤ y`. -/
private lemma interval_decay_le {t B : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hB : 0 < B) {W : ℕ}
    (hW : 1 ≤ W) {g : ℝ} (hg0 : 0 < g) (hgB : g ≤ (W : ℝ) ^ B) {J : Set ℝ} {n₀ : ℕ}
    (hEP : EndpointMomentAt W g J t n₀ ((W : ℝ) ^ (-2 : ℝ))) (N : ℕ) {E : ℝ} (hE : E ∈ J)
    (x y : Fin N) (hxy : x ≤ y) :
    ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W N ω) 0 0) E) x y‖ₑ ^ t ∂(μ W N) ≤
      ENNReal.ofReal (aprioriConst t * (W : ℝ) ^ ((B + 2) * t + 2) *
        Real.exp (-(2 * Real.log W / (n₀ + 1)) * |((x : ℕ) : ℝ) - (y : ℕ)|)) := by
  have hxy' : x.val ≤ y.val := hxy
  have hk : (y.val - x.val) / (n₀ + 1) * (n₀ + 1) ≤ y.val - x.val := Nat.div_mul_le_self _ _
  have hclaim := interval_claim ht0 ht1 hg0 hEP hE ((y.val - x.val) / (n₀ + 1)) N x.val y.val
    x.isLt y.isLt (by omega)
  simp only [Fin.eta] at hclaim
  refine hclaim.trans (ENNReal.ofReal_le_ofReal ?_)
  have hw1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hw0 : (0 : ℝ) < W := by linarith
  have hmB : max 1 g ≤ (W : ℝ) ^ B := max_le (Real.one_le_rpow hw1 hB.le) hgB
  have hX := interval_X_rpow_le ht0 hw1 hmB
  have hE' := interval_exponent_le hw1 n₀ (y.val - x.val)
  have habs : |((x : ℕ) : ℝ) - (y : ℕ)| = ((y.val - x.val : ℕ) : ℝ) := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hxy')), Nat.cast_sub hxy']
  rw [habs, Real.rpow_add hw0]
  have hC : 0 < aprioriConst t := interval_aprioriConst_pos ht1
  calc aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t *
        ((W : ℝ) ^ (-2 : ℝ)) ^ ((y.val - x.val) / (n₀ + 1))
      ≤ aprioriConst t * (W : ℝ) ^ ((B + 2) * t) * ((W : ℝ) ^ (2 : ℝ) *
          Real.exp (-(2 * Real.log W / ((n₀ : ℝ) + 1)) * ((y.val - x.val : ℕ) : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hX hC.le) hE' (by positivity) (by positivity)
    _ = _ := by ring

/-- (E.14) [eq:c-interval] at one width `W`: on the Dirichlet path of `N` blocks,
`𝔼‖G(x, y)‖^t ≤ C_t W^{(B+2)t+2} exp(-(2 log W/(n₀+1)) |x - y|)`. -/
theorem interval_moment_decay {t B : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hB : 0 < B) {W : ℕ}
    (hW : 1 ≤ W) {g : ℝ} (hg0 : 0 < g) (hgB : g ≤ (W : ℝ) ^ B) {J : Set ℝ} {n₀ : ℕ}
    (hEP : EndpointMomentAt W g J t n₀ ((W : ℝ) ^ (-2 : ℝ))) (N : ℕ) {E : ℝ} (hE : E ∈ J)
    (x y : Fin N) :
    ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W N ω) 0 0) E) x y‖ₑ ^ t ∂(μ W N) ≤
      ENNReal.ofReal (aprioriConst t * (W : ℝ) ^ ((B + 2) * t + 2) *
        Real.exp (-(2 * Real.log W / (n₀ + 1)) * |((x : ℕ) : ℝ) - (y : ℕ)|)) := by
  rcases le_total x y with hxy | hxy
  · exact interval_decay_le ht0 ht1 hB hW hg0 hgB hEP N hE x y hxy
  · have hsw : ∀ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W N ω) 0 0) E) x y‖ₑ =
        ‖blockOf (resolventMat (pathOp g (gueBlock W N ω) 0 0) E) y x‖ₑ := by
      intro ω
      have hH := pathOp_isHermitian g (gueBlock_isHermitian W N ω) Matrix.isHermitian_zero
        Matrix.isHermitian_zero
      rw [blockOf_resolventMat_swap hH E y x, ← ofReal_norm, ← ofReal_norm,
        Matrix.l2_opNorm_conjTranspose]
    simp_rw [hsw]
    have := interval_decay_le ht0 ht1 hB hW hg0 hgB hEP N hE y x hxy
    rwa [abs_sub_comm] at this

/-- (E.14) [eq:c-interval] with `n₀ + 1 ≤ C′ 𝔟 log W`: decay `exp(-(2/C′) |x - y| / 𝔟)`. -/
theorem interval_moment_decay_scale {t B b C' : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hB : 0 < B)
    (hb : 0 < b) (hC' : 0 < C') {W : ℕ} (hW : 1 ≤ W) {g : ℝ} (hg0 : 0 < g)
    (hgB : g ≤ (W : ℝ) ^ B) {J : Set ℝ} {n₀ : ℕ} (hn₀ : (n₀ : ℝ) + 1 ≤ C' * b * Real.log W)
    (hEP : EndpointMomentAt W g J t n₀ ((W : ℝ) ^ (-2 : ℝ))) (N : ℕ) {E : ℝ} (hE : E ∈ J)
    (x y : Fin N) :
    ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W N ω) 0 0) E) x y‖ₑ ^ t ∂(μ W N) ≤
      ENNReal.ofReal (aprioriConst t * (W : ℝ) ^ ((B + 2) * t + 2) *
        Real.exp (-(2 / C') * |((x : ℕ) : ℝ) - (y : ℕ)| / b)) := by
  refine (interval_moment_decay ht0 ht1 hB hW hg0 hgB hEP N hE x y).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ ?_))
  · have hn : (0 : ℝ) < (n₀ : ℝ) + 1 := by positivity
    have hCb : 0 < C' * b := mul_pos hC' hb
    have hL : 0 < Real.log W := by
      by_contra hc
      have h0 : Real.log W ≤ 0 := not_lt.mp hc
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hCb.le h0]
    have hrate : 2 / C' / b ≤ 2 * Real.log W / ((n₀ : ℝ) + 1) := by
      rw [div_div, div_le_div_iff₀ hCb hn]
      nlinarith
    apply Real.exp_le_exp.mpr
    have hd : 0 ≤ |((x : ℕ) : ℝ) - (y : ℕ)| := abs_nonneg _
    have e : -(2 / C') * |((x : ℕ) : ℝ) - (y : ℕ)| / b =
        -(2 / C' / b) * |((x : ℕ) : ℝ) - (y : ℕ)| := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hrate hd]
  · have := interval_aprioriConst_pos ht1
    positivity

end LSBA
