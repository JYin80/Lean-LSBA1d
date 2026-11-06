import LSBA.Sampling.AuxModel
import LSBA.Gauss.HeatGenerator
import LSBA.Loop.Generator

/-!
# The expected hierarchy of the auxiliary model

Continuity in `t` and the derivative of the normalized expected loops of the auxiliary model:
the cut sum of (5.10) [fo:eq:primitive] up to an error `C/W̃`, from the generator form of Itô's
formula, the variance bound and the one-loop mean field.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

section AuxHierarchyNorms

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An entry is bounded by the operator norm. -/
private lemma auxHierarchy_norm_entry_le (X : Matrix n n ℂ) (i j : n) : ‖X i j‖ ≤ ‖X‖ := by
  have h := Matrix.l2_opNorm_mulVec X ((EuclideanSpace.equiv n ℂ).symm (Pi.single j 1))
  have hx : ‖(EuclideanSpace.equiv n ℂ).symm (Pi.single j (1 : ℂ))‖ = 1 := by simp
  rw [hx, mul_one] at h
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans h)
  simp [Matrix.mulVec_single]

/-- `|Tr X| ≤ |n| ‖X‖`. -/
private lemma auxHierarchy_norm_trace_le (X : Matrix n n ℂ) :
    ‖X.trace‖ ≤ Fintype.card n * ‖X‖ := by
  rw [Matrix.trace]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => auxHierarchy_norm_entry_le X i i).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `‖1‖ ≤ 1` for the operator norm. -/
private lemma auxHierarchy_norm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp

/-- A product of factors of norm at most `ρ` has norm at most `ρ ^ length`. -/
private lemma auxHierarchy_norm_prod_le {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ l : List (Matrix n n ℂ), (∀ x ∈ l, ‖x‖ ≤ ρ) → ‖l.prod‖ ≤ ρ ^ l.length
  | [], _ => by simpa using auxHierarchy_norm_one_le
  | x :: l, h => by
    rw [List.prod_cons, List.length_cons, pow_succ']
    calc ‖x * l.prod‖ ≤ ‖x‖ * ‖l.prod‖ := norm_mul_le _ _
      _ ≤ ρ * ρ ^ l.length :=
          mul_le_mul (h x (by simp))
            (auxHierarchy_norm_prod_le hρ l fun y hy => h y (by simp [hy])) (norm_nonneg _) hρ

/-- `‖X^σ‖ = ‖X‖`. -/
private lemma auxHierarchy_norm_sgnMat (X : Matrix n n ℂ) (σ : Bool) : ‖sgnMat X σ‖ = ‖X‖ := by
  cases σ
  · exact Matrix.l2_opNorm_conjTranspose X
  · rfl

/-- `‖E_a‖ ≤ W⁻¹`. -/
private lemma auxHierarchy_norm_blockE_le (W L : ℕ) (a : Fin L) :
    ‖blockE W L a‖ ≤ (W : ℝ)⁻¹ := by
  rw [blockE, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p => ?_
  split_ifs <;> simp

/-- `|W^{k-1} ℒ_k(X)| ≤ L ‖X‖^k` for `k ≥ 1`. -/
private lemma auxHierarchy_norm_loop_le {W L k : ℕ} (hW : 1 ≤ W) (hk : 1 ≤ k)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ‖(W : ℂ) ^ (k - 1) * loopTr X a σ‖ ≤ L * ‖X‖ ^ k := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hprod := auxHierarchy_norm_prod_le (by positivity : (0 : ℝ) ≤ ‖X‖ * (W : ℝ)⁻¹)
    (List.ofFn fun i => sgnMat X (σ i) * blockE W L (a i)) (fun x hx => by
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hx
      calc _ ≤ ‖sgnMat X (σ i)‖ * ‖blockE W L (a i)‖ := norm_mul_le _ _
        _ ≤ ‖X‖ * (W : ℝ)⁻¹ := by
          rw [auxHierarchy_norm_sgnMat]
          exact mul_le_mul_of_nonneg_left (auxHierarchy_norm_blockE_le W L (a i))
            (norm_nonneg _))
  rw [List.length_ofFn] at hprod
  rw [norm_mul, norm_pow, Complex.norm_natCast, loopTr]
  calc (W : ℝ) ^ (k - 1) * ‖_‖
      ≤ (W : ℝ) ^ (k - 1) * (Fintype.card (Fin L × Fin W) * (‖X‖ * (W : ℝ)⁻¹) ^ k) := by
        gcongr
        exact (auxHierarchy_norm_trace_le _).trans (by gcongr)
    _ = L * ‖X‖ ^ k := by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_pow, inv_pow]
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        push_cast
        field_simp

end AuxHierarchyNorms

/-- The auxiliary resolvent is the resolvent of `H_t = A_g ⊗ I + √(tγ_g) V` at `z_t`. -/
private lemma auxHierarchy_auxG_eq (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) (ω : Ω W L) :
    auxG g W L E m t ω = resolventMat (flowH g W L t ω) (zChar g E m t) := by
  have hmax : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hs : Real.sqrt (t * gammaG g) = Real.sqrt t * (max 1 g)⁻¹ := by
    rw [Real.sqrt_mul' _ (by unfold gammaG; positivity), gammaG, Real.sqrt_inv,
      Real.sqrt_sq hmax.le]
  unfold auxG resolventMat flowH blockFlow blockV
  congr 2
  ext p q
  simp only [Hdet, Ag, blockDiagOp, hs, Matrix.add_apply, Matrix.smul_apply,
    Matrix.kroneckerMap_apply, Matrix.of_apply, smul_eq_mul, Complex.ofReal_mul]
  split_ifs <;> push_cast <;> ring

/-- The loop is a continuous function of the matrix. -/
private lemma auxHierarchy_continuous_loopTr {W L k : ℕ} (a : Fin k → Fin L)
    (σ : Fin k → Bool) :
    Continuous fun X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ => loopTr X a σ := by
  unfold loopTr
  refine Continuous.matrix_trace ?_
  simp only [List.ofFn_eq_map]
  refine continuous_list_prod _ fun i _ => ?_
  refine Continuous.mul ?_ continuous_const
  cases σ i
  · exact continuous_id.matrix_conjTranspose
  · exact continuous_id

/-- The auxiliary resolvent is continuous in the sample for `t < 1`. -/
private lemma auxHierarchy_continuous_auxG (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (hm : 0 < m.im)
    (t : ℝ) (ht : t < 1) : Continuous fun ω => auxG g W L E m t ω := by
  simp only [auxHierarchy_auxG_eq]
  have hz : (zChar g E m t).im ≠ 0 := by
    rw [im_zChar]; exact (etaChar_pos g m hm ht).ne'
  have hV : Continuous fun ω => blockV W L ω := by
    simp only [blockV_eq_sum_blockBasis]
    fun_prop
  have hF : Continuous fun ω => flowH g W L t ω := by
    unfold flowH blockFlow
    fun_prop
  have hc : Continuous fun ω => flowH g W L t ω - zChar g E m t • (1 : Matrix _ _ ℂ) :=
    hF.sub continuous_const
  refine continuous_iff_continuousAt.2 fun ω => ?_
  have hu := isUnit_sub_smul_one (flowH_isHermitian g W L t ω) hz
  have hdet : (flowH g W L t ω - zChar g E m t • (1 : Matrix _ _ ℂ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  refine (continuousAt_matrix_inv _ ?_).comp hc.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hdet

section AuxHierarchyNorms2

open scoped Matrix.Norms.L2Operator

/-- `‖G_t‖ ≤ η_t⁻¹` on the auxiliary model. -/
private lemma auxHierarchy_norm_auxG_le (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (hm : 0 < m.im)
    (t : ℝ) (ht : t < 1) (ω : Ω W L) : ‖auxG g W L E m t ω‖ ≤ (etaChar g m t)⁻¹ := by
  rw [auxHierarchy_auxG_eq]
  exact norm_resolvent_zChar_le g E m hm ht (flowH_isHermitian g W L t ω)

/-- The normalized loop of the auxiliary resolvent: `|W̃^{k-1} ℒ_k(G_t)| ≤ L η_t^{-k}`. -/
private lemma auxHierarchy_norm_loop_auxG_le (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (E : ℝ) (m : ℂ)
    (hm : 0 < m.im) (t : ℝ) (ht : t < 1) {k : ℕ} (hk : 1 ≤ k) (a : Fin k → Fin L)
    (σ : Fin k → Bool) (ω : Ω W L) :
    ‖(W : ℂ) ^ (k - 1) * loopTr (auxG g W L E m t ω) a σ‖ ≤ L * (etaChar g m t)⁻¹ ^ k := by
  refine (auxHierarchy_norm_loop_le hW hk _ a σ).trans ?_
  gcongr
  exact auxHierarchy_norm_auxG_le g W L E m hm t ht ω

end AuxHierarchyNorms2

/-- `|W̃^{k-1} E ℒ_k^{(W̃)}(t)| ≤ L η_t^{-k}` for `k ≥ 1` and `t < 1`, with
`η_t = (1-t)γ_g Im m` of (5.3) [fo:eq:characteristic]. -/
theorem auxHierarchy_norm_auxLoop_le (g : ℝ) (L : ℕ) (E : ℝ) (m : ℂ) (hm : 0 < m.im) (Wt : ℕ)
    (hWt : 1 ≤ Wt) (t : ℝ) (ht : t < 1) (k : ℕ) (hk : 1 ≤ k) (a : Fin k → Fin L)
    (σ : Fin k → Bool) :
    ‖auxLoop g Wt L E m t k a σ‖ ≤ L * (etaChar g m t)⁻¹ ^ k := by
  rw [auxLoop, ← integral_const_mul]
  refine (norm_integral_le_of_norm_le_const (Eventually.of_forall fun ω =>
    auxHierarchy_norm_loop_auxG_le g Wt L hWt E m hm t ht hk a σ ω)).trans (le_of_eq ?_)
  simp

/-! ### Moment bounds on the Gaussian space -/

/-- A bounded continuous function is integrable for the Gaussian product measure. -/
private lemma auxHierarchy_integrable {W L : ℕ} {f : Ω W L → ℂ} (hf : Continuous f) (C : ℝ)
    (hb : ∀ ω, ‖f ω‖ ≤ C) : Integrable f (μ W L) :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hb)

/-- Covariance bound: `|E[XY] - EX EY| ≤ (E|X - EX|² + E|Y - EY|²)/2` for bounded continuous
`X, Y`. -/
private lemma auxHierarchy_cov_le {W L : ℕ} {X Y : Ω W L → ℂ} (hX : Continuous X)
    (hY : Continuous Y) {B : ℝ} (hXB : ∀ ω, ‖X ω‖ ≤ B) (hYB : ∀ ω, ‖Y ω‖ ≤ B) {v₁ v₂ : ℝ}
    (hv₁ : ∫ ω, ‖X ω - ∫ ω', X ω' ∂(μ W L)‖ ^ 2 ∂(μ W L) ≤ v₁)
    (hv₂ : ∫ ω, ‖Y ω - ∫ ω', Y ω' ∂(μ W L)‖ ^ 2 ∂(μ W L) ≤ v₂) :
    ‖∫ ω, X ω * Y ω ∂(μ W L) - (∫ ω, X ω ∂(μ W L)) * ∫ ω, Y ω ∂(μ W L)‖ ≤ (v₁ + v₂) / 2 := by
  set a := ∫ ω, X ω ∂(μ W L) with ha
  set b := ∫ ω, Y ω ∂(μ W L) with hb
  have hB : 0 ≤ B := (norm_nonneg _).trans (hXB 0)
  have iX := auxHierarchy_integrable hX B hXB
  have iY := auxHierarchy_integrable hY B hYB
  have iXY := auxHierarchy_integrable (hX.mul hY) (B * B) fun ω =>
    (norm_mul_le _ _).trans (mul_le_mul (hXB ω) (hYB ω) (norm_nonneg _) hB)
  have cX : Continuous fun ω => X ω - a := hX.sub continuous_const
  have cY : Continuous fun ω => Y ω - b := hY.sub continuous_const
  have bX : ∀ ω, ‖X ω - a‖ ≤ B + ‖a‖ := fun ω => (norm_sub_le _ _).trans (by linarith [hXB ω])
  have bY : ∀ ω, ‖Y ω - b‖ ≤ B + ‖b‖ := fun ω => (norm_sub_le _ _).trans (by linarith [hYB ω])
  have iX2 : Integrable (fun ω => ‖X ω - a‖ ^ 2) (μ W L) :=
    Integrable.of_bound (cX.norm.pow 2).aestronglyMeasurable ((B + ‖a‖) ^ 2)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (bX ω) 2)
  have iY2 : Integrable (fun ω => ‖Y ω - b‖ ^ 2) (μ W L) :=
    Integrable.of_bound (cY.norm.pow 2).aestronglyMeasurable ((B + ‖b‖) ^ 2)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (bY ω) 2)
  have iP : Integrable (fun ω => ‖(X ω - a) * (Y ω - b)‖) (μ W L) :=
    (auxHierarchy_integrable (cX.mul cY) ((B + ‖a‖) * (B + ‖b‖)) fun ω =>
      (norm_mul_le _ _).trans (mul_le_mul (bX ω) (bY ω) (norm_nonneg _) (by positivity))).norm
  have e : ∫ ω, X ω * Y ω ∂(μ W L) - a * b = ∫ ω, (X ω - a) * (Y ω - b) ∂(μ W L) := by
    have h1 : (fun ω => (X ω - a) * (Y ω - b)) =
        fun ω => (X ω * Y ω - b * X ω) - (a * Y ω - a * b) := funext fun ω => by ring
    have j0 : Integrable (fun ω => X ω * Y ω) (μ W L) := iXY
    have j1 : Integrable (fun ω => b * X ω) (μ W L) := iX.const_mul b
    have j2 : Integrable (fun ω => a * Y ω) (μ W L) := iY.const_mul a
    have j3 : Integrable (fun _ : Ω W L => a * b) (μ W L) := integrable_const _
    rw [h1, integral_sub (f := fun ω => X ω * Y ω - b * X ω) (g := fun ω => a * Y ω - a * b)
      (j0.sub j1) (j2.sub j3), integral_sub j0 j1, integral_sub j2 j3,
      integral_const_mul, integral_const_mul, integral_const, probReal_univ, one_smul, ← ha, ← hb]
    ring
  rw [e]
  calc ‖∫ ω, (X ω - a) * (Y ω - b) ∂(μ W L)‖
      ≤ ∫ ω, ‖(X ω - a) * (Y ω - b)‖ ∂(μ W L) := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (‖X ω - a‖ ^ 2 + ‖Y ω - b‖ ^ 2) / 2 ∂(μ W L) := by
        refine integral_mono iP ((iX2.add iY2).div_const 2) fun ω => ?_
        dsimp only
        rw [norm_mul]
        nlinarith [sq_nonneg (‖X ω - a‖ - ‖Y ω - b‖)]
    _ = ((∫ ω, ‖X ω - a‖ ^ 2 ∂(μ W L)) + ∫ ω, ‖Y ω - b‖ ^ 2 ∂(μ W L)) / 2 := by
        rw [integral_div, integral_add iX2 iY2]
    _ ≤ (v₁ + v₂) / 2 := by gcongr

/-- Light-insertion bound: `|E[(X - s) Y]| ≤ B ((v + 1)/2 + r)/w` when `|Y| ≤ B`,
`E|X - EX|² ≤ v/w²` and `|EX - s| ≤ r/w`. -/
private lemma auxHierarchy_light_le {W L : ℕ} {X Y : Ω W L → ℂ} (hX : Continuous X)
    (hY : Continuous Y) {BX B : ℝ} (hXB : ∀ ω, ‖X ω‖ ≤ BX) (hYB : ∀ ω, ‖Y ω‖ ≤ B) (s : ℂ)
    {w v r : ℝ} (hw : 0 < w)
    (hv : ∫ ω, ‖X ω - ∫ ω', X ω' ∂(μ W L)‖ ^ 2 ∂(μ W L) ≤ v / w ^ 2)
    (hr : ‖(∫ ω, X ω ∂(μ W L)) - s‖ ≤ r / w) :
    ‖∫ ω, (X ω - s) * Y ω ∂(μ W L)‖ ≤ B * ((v + 1) / 2 + r) / w := by
  set a := ∫ ω, X ω ∂(μ W L) with ha
  have hB : 0 ≤ B := (norm_nonneg _).trans (hYB 0)
  have cX : Continuous fun ω => X ω - a := hX.sub continuous_const
  have bX : ∀ ω, ‖X ω - a‖ ≤ BX + ‖a‖ := fun ω => (norm_sub_le _ _).trans (by linarith [hXB ω])
  have bXs : ∀ ω, ‖X ω - s‖ ≤ BX + ‖s‖ := fun ω => (norm_sub_le _ _).trans (by linarith [hXB ω])
  have hBX : 0 ≤ BX := (norm_nonneg _).trans (hXB 0)
  have iX2 : Integrable (fun ω => ‖X ω - a‖ ^ 2) (μ W L) :=
    Integrable.of_bound (cX.norm.pow 2).aestronglyMeasurable ((BX + ‖a‖) ^ 2)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (bX ω) 2)
  have iXs : Integrable (fun ω => ‖X ω - s‖) (μ W L) :=
    (auxHierarchy_integrable (hX.sub continuous_const) (BX + ‖s‖) bXs).norm
  have iP : Integrable (fun ω => ‖(X ω - s) * Y ω‖) (μ W L) :=
    (auxHierarchy_integrable ((hX.sub continuous_const).mul hY) ((BX + ‖s‖) * B) fun ω =>
      (norm_mul_le _ _).trans (mul_le_mul (bXs ω) (hYB ω) (norm_nonneg _) (by positivity))).norm
  have hpt : ∀ ω, ‖X ω - s‖ ≤ (w * ‖X ω - a‖ ^ 2 + w⁻¹) / 2 + ‖a - s‖ := by
    intro ω
    have h1 : ‖X ω - s‖ ≤ ‖X ω - a‖ + ‖a - s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h2 : ‖X ω - a‖ ≤ (w * ‖X ω - a‖ ^ 2 + w⁻¹) / 2 := by
      have hw' : w * w⁻¹ = 1 := mul_inv_cancel₀ hw.ne'
      nlinarith [sq_nonneg (w * ‖X ω - a‖ - 1), inv_pos.mpr hw]
    linarith
  calc ‖∫ ω, (X ω - s) * Y ω ∂(μ W L)‖
      ≤ ∫ ω, ‖(X ω - s) * Y ω‖ ∂(μ W L) := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, B * ((w * ‖X ω - a‖ ^ 2 + w⁻¹) / 2 + ‖a - s‖) ∂(μ W L) := by
        refine integral_mono iP ((((iX2.const_mul w).add (integrable_const _)).div_const 2).add
          (integrable_const _) |>.const_mul B) fun ω => ?_
        dsimp only
        rw [norm_mul, mul_comm]
        exact mul_le_mul (hYB ω) (hpt ω) (norm_nonneg _) hB
    _ = B * ((w * ∫ ω, ‖X ω - a‖ ^ 2 ∂(μ W L) + w⁻¹) / 2 + ‖a - s‖) := by
        have j1 : Integrable (fun ω => w * ‖X ω - a‖ ^ 2) (μ W L) := iX2.const_mul w
        have j2 : Integrable (fun _ : Ω W L => w⁻¹) (μ W L) := integrable_const _
        have j3 : Integrable (fun ω => (w * ‖X ω - a‖ ^ 2 + w⁻¹) / 2) (μ W L) :=
          (j1.add j2).div_const 2
        have j4 : Integrable (fun _ : Ω W L => ‖a - s‖) (μ W L) := integrable_const _
        rw [integral_const_mul, integral_add j3 j4, integral_div, integral_add j1 j2,
          integral_const_mul]
        simp
    _ ≤ B * ((w * (v / w ^ 2) + w⁻¹) / 2 + r / w) := by gcongr
    _ = B * ((v + 1) / 2 + r) / w := by field_simp

/-! ### Bookkeeping of the hierarchy -/

/-- The powers of `W̃` in the cut term: `W̃^{k-1} γW̃ Σ ℒ_p ℒ_q = γ Σ (W̃^{p-1}ℒ_p)(W̃^{q-1}ℒ_q)`,
since `p + q = k + 2`. -/
private lemma auxHierarchy_cut_scale {L k : ℕ} (w γ : ℂ) (ℓ : LoopFam L) (a : Fin k → Fin L)
    (σ : Fin k → Bool) :
    w ^ (k - 1) * ((γ * w) * cutSumFam ℓ a σ) =
      γ * cutSumFam (fun n b τ => w ^ (n - 1) * ℓ n b τ) a σ := by
  unfold cutSumFam
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hij' : i.val < j.val := hij
    have hj := j.isLt
    have hexp : w ^ (k - 1) * w =
        w ^ (k + i.val - j.val + 1 - 1) * w ^ (j.val - i.val + 1 - 1) := by
      rw [← pow_succ, ← pow_add]
      congr 1
      omega
    linear_combination (γ * ℓ _ (cutLLab a i j c) (cutLSgn σ i j) *
      ℓ _ (cutRLab a i j c) (cutRSgn σ i j)) * hexp
  · simp

/-- The powers of `W̃` in the light term: `W̃^{k-1} γW̃ Σ x ℒ_{k+1} = γ Σ x (W̃^k ℒ_{k+1})`. -/
private lemma auxHierarchy_light_scale {L k : ℕ} (hk : 1 ≤ k) (w γ : ℂ)
    (x y : Fin k → Fin L → ℂ) :
    w ^ (k - 1) * ((γ * w) * ∑ i, ∑ c, x i c * y i c) =
      γ * ∑ i, ∑ c, x i c * (w ^ (k + 1 - 1) * y i c) := by
  have hexp : w ^ (k - 1) * w = w ^ (k + 1 - 1) := by
    rw [← pow_succ]; congr 1; omega
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
  linear_combination (γ * x i c * y i c) * hexp

/-- `|Σ_{i<j} Σ_c f_{ijc}| ≤ k² L D` when every term is at most `D`. -/
private lemma auxHierarchy_norm_cut_le {k L : ℕ} (f : Fin k → Fin k → Fin L → ℂ) {D : ℝ}
    (hD : 0 ≤ D) (h : ∀ i j c, i < j → ‖f i j c‖ ≤ D) :
    ‖∑ i, ∑ j, if i < j then ∑ c, f i j c else 0‖ ≤ k * k * L * D := by
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ i : Fin k, ‖∑ j, if i < j then ∑ c, f i j c else 0‖ ≤ k * (L * D) := by
    intro i
    refine (norm_sum_le _ _).trans ?_
    have h2 : ∀ j : Fin k, ‖if i < j then ∑ c, f i j c else 0‖ ≤ L * D := by
      intro j
      split_ifs with hij
      · refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_sum fun c _ => h i j c hij).trans (le_of_eq ?_)
        simp
      · simp only [norm_zero]; positivity
    refine (Finset.sum_le_sum fun j _ => h2 j).trans (le_of_eq ?_)
    simp
  refine (Finset.sum_le_sum fun i _ => h1 i).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `|Σ_i Σ_c f_{ic}| ≤ k L D` when every term is at most `D`. -/
private lemma auxHierarchy_norm_double_le {k L : ℕ} (f : Fin k → Fin L → ℂ) {D : ℝ}
    (h : ∀ i c, ‖f i c‖ ≤ D) : ‖∑ i, ∑ c, f i c‖ ≤ k * L * D := by
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun c _ => h i c)).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The expectation of a cut-type sum is the cut-type sum of the expectations. -/
private lemma auxHierarchy_integral_cut {W L k : ℕ} (f : Fin k → Fin k → Fin L → Ω W L → ℂ)
    (hf : ∀ i j c, Integrable (f i j c) (μ W L)) :
    ∫ ω, (∑ i, ∑ j, if i < j then ∑ c, f i j c ω else 0) ∂(μ W L) =
      ∑ i, ∑ j, if i < j then ∑ c, ∫ ω, f i j c ω ∂(μ W L) else 0 := by
  have hi : ∀ i j, Integrable (fun ω => if i < j then ∑ c, f i j c ω else 0) (μ W L) := by
    intro i j
    by_cases hij : i < j
    · simp only [hij, ite_true]; exact integrable_finsetSum _ fun c _ => hf i j c
    · simp only [hij, ite_false]; exact integrable_zero _ _ _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hi i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i < j
  · simp only [hij, ite_true]; exact integral_finsetSum _ fun c _ => hf i j c
  · simp only [hij, ite_false]; simp

/-- A cut-type sum of integrable functions is integrable. -/
private lemma auxHierarchy_integrable_cut {W L k : ℕ} (f : Fin k → Fin k → Fin L → Ω W L → ℂ)
    (hf : ∀ i j c, Integrable (f i j c) (μ W L)) :
    Integrable (fun ω => ∑ i, ∑ j, if i < j then ∑ c, f i j c ω else 0) (μ W L) := by
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  by_cases hij : i < j
  · simp only [hij, ite_true]; exact integrable_finsetSum _ fun c _ => hf i j c
  · simp only [hij, ite_false]; exact integrable_zero _ _ _

/-- Difference of two cut-type sums. -/
private lemma auxHierarchy_cut_sub {k L : ℕ} (f h : Fin k → Fin k → Fin L → ℂ) :
    (∑ i, ∑ j, if i < j then ∑ c, f i j c else 0) -
        (∑ i, ∑ j, if i < j then ∑ c, h i j c else 0) =
      ∑ i, ∑ j, if i < j then ∑ c, (f i j c - h i j c) else 0 := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [Finset.sum_sub_distrib]
  · simp

/-- The expected loop hierarchy (5.8) [fo:eq:hierarchy] of the auxiliary model at fixed time:
`t ↦ W̃^{k-1} E ℒ_k^{(W̃)}(t)` is continuous on `[0, T]`, differentiable on `(0, T)`, and its
derivative is `γ_g` times the cut sum of the expected loops up to `C/W̃`. -/
theorem auxLoop_hierarchy (g : ℝ) (hg : 0 < g) (L : ℕ) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (T : ℝ) (hT0 : 0 ≤ T) (hT : T < 1) (k : ℕ)
    (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ Wt : ℕ, 1 ≤ Wt → ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
      ContinuousOn (fun t => auxLoop g Wt L E m t k a σ) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Ioo 0 T, ∃ d : ℂ, HasDerivAt (fun s => auxLoop g Wt L E m s k a σ) d t ∧
        ‖d - (gammaG g : ℂ) * cutSumFam (auxLoop g Wt L E m t) a σ‖ ≤ C / Wt := by
  have hγ : 0 < gammaG g := by
    have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
    unfold gammaG; positivity
  have hm0 : 0 < m.im := hm.1
  set γ := gammaG g with hγdef
  set η := etaChar g m T with hηdef
  have hη : 0 < η := etaChar_pos g m hm0 hT
  have hηt : ∀ t, t ≤ T → (etaChar g m t)⁻¹ ≤ η⁻¹ := by
    intro t ht
    refine inv_anti₀ hη ?_
    simp only [hηdef, etaChar]
    gcongr
  -- variance constants for every length
  have hv : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ (1 ≤ n → ∀ Wt : ℕ, 1 ≤ Wt → ∀ t : ℝ, 0 ≤ t → t ≤ T →
      ∀ (a : Fin n → Fin L) (σ : Fin n → Bool),
        Integrable (fun ω => ‖(Wt : ℂ) ^ (n - 1) * loopTr (auxG g Wt L E m t ω) a σ -
          auxLoop g Wt L E m t n a σ‖ ^ 2) (μ Wt L) ∧
        ∫ ω, ‖(Wt : ℂ) ^ (n - 1) * loopTr (auxG g Wt L E m t ω) a σ -
          auxLoop g Wt L E m t n a σ‖ ^ 2 ∂(μ Wt L) ≤ C / (Wt : ℝ) ^ 2) := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨C, hC, h⟩ := auxLoop_variance g hg L hL E m hm T hT0 hT n hn
      exact ⟨C, hC, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hn⟩
  choose Cv hCv0 hCv using hv
  obtain ⟨C1, hC1, hone⟩ := auxLoop_one g hg L hL E m hm T hT0 hT
  set Cm := ∑ n ∈ Finset.range (k + 2), Cv n with hCm
  have hCm_le : ∀ n, n ≤ k + 1 → Cv n ≤ Cm := fun n hn =>
    Finset.single_le_sum (f := Cv) (fun i _ => (hCv0 i).le) (Finset.mem_range.2 (by omega))
  have hCm0 : 0 ≤ Cm := (hCv0 0).le.trans (hCm_le 0 (by omega))
  set B := (L : ℝ) * (max 1 η⁻¹) ^ (k + 1) with hBdef
  have hB0 : 0 ≤ B := by positivity
  set C := γ * ((k : ℝ) * L * (B * ((Cv 1 + 1) / 2 + C1)) + (k : ℝ) * k * L * Cm) + 1
    with hCdef
  have hC0 : 0 < C := by
    have h1 := hCv0 1
    have h2 : 0 ≤ (k : ℝ) * k * L * Cm := by positivity
    have h3 : 0 ≤ (k : ℝ) * L * (B * ((Cv 1 + 1) / 2 + C1)) := by positivity
    have h4 : 0 ≤ γ * ((k : ℝ) * L * (B * ((Cv 1 + 1) / 2 + C1)) + (k : ℝ) * k * L * Cm) :=
      mul_nonneg hγ.le (add_nonneg h3 h2)
    linarith
  refine ⟨C, hC0, fun Wt hWt a σ => ?_⟩
  have hW' : (0 : ℝ) < Wt := by exact_mod_cast hWt
  set A : Matrix (Fin L × Fin Wt) (Fin L × Fin Wt) ℂ :=
    Ag g L ⊗ₖ (1 : Matrix (Fin Wt) (Fin Wt) ℂ) with hAdef
  have hA : A.IsHermitian := by
    have h := flowH_isHermitian g Wt L 0 0
    simpa [flowH, blockFlow] using h
  have hfun : (fun s => auxLoop g Wt L E m s k a σ) = fun s => (Wt : ℂ) ^ (k - 1) *
      ∫ ω, resLoop g E m a σ s (blockFlow Wt L A (s * γ) ω) ∂(μ Wt L) := by
    funext s
    simp only [auxLoop, auxHierarchy_auxG_eq]
    rfl
  have hgen := blockHeat_generator Wt L A γ hγ.le (resLoop g E m (W := Wt) a σ)
    (a := -1) (b := (T + 1) / 2) (v := T) (by norm_num) hT0 (by linarith)
    (heatClass_loopTr Wt L k A hA g E m hm0 a σ (by linarith))
  refine ⟨?_, fun t ht => ?_⟩
  · rw [hfun]; exact continuousOn_const.mul hgen.1
  obtain ⟨ht0, htT⟩ := ht
  have ht1 : t < 1 := by linarith
  refine ⟨_, by rw [hfun]; exact (hgen.2 t ⟨ht0, htT⟩).const_mul _, ?_⟩
  -- the sample functions
  set G : Ω Wt L → Matrix (Fin L × Fin Wt) (Fin L × Fin Wt) ℂ :=
    fun ω => auxG g Wt L E m t ω with hG
  have hGc : Continuous G := auxHierarchy_continuous_auxG g Wt L E m hm0 t ht1
  set NX : (n : ℕ) → (Fin n → Fin L) → (Fin n → Bool) → Ω Wt L → ℂ :=
    fun n b τ ω => (Wt : ℂ) ^ (n - 1) * loopTr (G ω) b τ with hNX
  have hNXc : ∀ n b τ, Continuous (NX n b τ) := fun n b τ =>
    continuous_const.mul ((auxHierarchy_continuous_loopTr b τ).comp hGc)
  have hNXb : ∀ n b τ, 1 ≤ n → n ≤ k + 1 → ∀ ω, ‖NX n b τ ω‖ ≤ B := by
    intro n b τ hn hnk ω
    refine (auxHierarchy_norm_loop_auxG_le g Wt L hWt E m hm0 t ht1 hn b τ ω).trans ?_
    rw [hBdef]
    gcongr
    calc (etaChar g m t)⁻¹ ^ n ≤ η⁻¹ ^ n :=
          pow_le_pow_left₀ (inv_nonneg.2 (etaChar_pos g m hm0 ht1).le) (hηt t htT.le) n
      _ ≤ (max 1 η⁻¹) ^ n := pow_le_pow_left₀ (inv_nonneg.2 hη.le) (le_max_right _ _) n
      _ ≤ (max 1 η⁻¹) ^ (k + 1) := pow_le_pow_right₀ (le_max_left _ _) hnk
  have hNXi : ∀ n b τ, ∫ ω, NX n b τ ω ∂(μ Wt L) = auxLoop g Wt L E m t n b τ :=
    fun n b τ => integral_const_mul _ _
  -- the light and cut parts of the generator
  set Lt : Ω Wt L → ℂ := fun ω => (γ : ℂ) * ∑ i : Fin k, ∑ c : Fin L,
    (loopTr (G ω) ![c] ![σ i] - sgnScalar m (σ i)) * NX (k + 1) (insLab a i c) (insSgn σ i) ω
    with hLt
  set Ct : Ω Wt L → ℂ := fun ω => (γ : ℂ) * cutSumFam (fun n b τ => NX n b τ ω) a σ with hCt
  have hpt : ∀ ω, (Wt : ℂ) ^ (k - 1) *
      blockGen Wt L γ (resLoop g E m a σ) t (blockFlow Wt L A (t * γ) ω) = Lt ω + Ct ω := by
    intro ω
    have h := blockGen_loopTr g E m hm0 ht1 (flowH_isHermitian g Wt L t ω) a σ
    change (Wt : ℂ) ^ (k - 1) * blockGen Wt L γ (resLoop g E m a σ) t (flowH g Wt L t ω) = _
    rw [h, lightW, ← auxHierarchy_auxG_eq, mul_add]
    have e : (((γ * Wt : ℝ) : ℂ)) = (γ : ℂ) * (Wt : ℂ) := by push_cast; ring
    rw [e, auxHierarchy_cut_scale, auxHierarchy_light_scale (by omega)]
  have hd : (Wt : ℂ) ^ (k - 1) * ∫ ω, blockGen Wt L γ (resLoop g E m a σ) t
      (blockFlow Wt L A (t * γ) ω) ∂(μ Wt L) = ∫ ω, (Lt ω + Ct ω) ∂(μ Wt L) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hpt)
  -- integrability
  have hX1c : ∀ (i : Fin k) (c : Fin L), Continuous fun ω => loopTr (G ω) ![c] ![σ i] :=
    fun i c => (auxHierarchy_continuous_loopTr _ _).comp hGc
  have hX1b : ∀ (i : Fin k) (c : Fin L) ω, ‖loopTr (G ω) ![c] ![σ i]‖ ≤ B := by
    intro i c ω
    have h := hNXb 1 ![c] ![σ i] le_rfl (by omega) ω
    simpa [hNX] using h
  have hX1i : ∀ (i : Fin k) (c : Fin L),
      ∫ ω, loopTr (G ω) ![c] ![σ i] ∂(μ Wt L) = auxLoop g Wt L E m t 1 ![c] ![σ i] := by
    intro i c
    simp only [auxLoop, Nat.sub_self, pow_zero, one_mul]
    rfl
  have iLterm : ∀ (i : Fin k) (c : Fin L), Integrable (fun ω =>
      (loopTr (G ω) ![c] ![σ i] - sgnScalar m (σ i)) * NX (k + 1) (insLab a i c) (insSgn σ i) ω)
      (μ Wt L) := by
    intro i c
    refine auxHierarchy_integrable (((hX1c i c).sub continuous_const).mul (hNXc _ _ _))
      ((B + ‖sgnScalar m (σ i)‖) * B) fun ω => ?_
    refine (norm_mul_le _ _).trans (mul_le_mul ((norm_sub_le _ _).trans ?_)
      (hNXb _ _ _ (by omega) le_rfl ω) (norm_nonneg _) (by positivity))
    linarith [hX1b i c ω]
  have iCterm : ∀ (i j : Fin k) (c : Fin L), i < j → Integrable (fun ω =>
      NX _ (cutLLab a i j c) (cutLSgn σ i j) ω * NX _ (cutRLab a i j c) (cutRSgn σ i j) ω)
      (μ Wt L) := by
    intro i j c hij
    have hij' : i.val < j.val := hij
    have hj := j.isLt
    exact auxHierarchy_integrable ((hNXc _ _ _).mul (hNXc _ _ _)) (B * B) fun ω =>
      (norm_mul_le _ _).trans (mul_le_mul (hNXb _ _ _ (by omega) (by omega) ω)
        (hNXb _ _ _ (by omega) (by omega) ω) (norm_nonneg _) hB0)
  have iCterm' : ∀ (i j : Fin k) (c : Fin L), Integrable (fun ω =>
      if i < j then NX _ (cutLLab a i j c) (cutLSgn σ i j) ω *
        NX _ (cutRLab a i j c) (cutRSgn σ i j) ω else 0) (μ Wt L) := by
    intro i j c
    by_cases hij : i < j
    · simp only [hij, ite_true]; exact iCterm i j c hij
    · simp only [hij, ite_false]; exact integrable_zero _ _ _
  have iLt : Integrable Lt (μ Wt L) :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun c _ => iLterm i c).const_mul _
  have iCt : Integrable Ct (μ Wt L) := by
    refine Integrable.const_mul ?_ _
    simp only [cutSumFam]
    exact auxHierarchy_integrable_cut (fun i j c ω => if i < j then
      NX _ (cutLLab a i j c) (cutLSgn σ i j) ω * NX _ (cutRLab a i j c) (cutRSgn σ i j) ω else 0)
      iCterm' |>.congr (Eventually.of_forall fun ω => by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        by_cases hij : i < j <;> simp [hij])
  -- the two expectations
  have hLi : ∫ ω, Lt ω ∂(μ Wt L) = (γ : ℂ) * ∑ i : Fin k, ∑ c : Fin L,
      ∫ ω, (loopTr (G ω) ![c] ![σ i] - sgnScalar m (σ i)) *
        NX (k + 1) (insLab a i c) (insSgn σ i) ω ∂(μ Wt L) := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun c _ => iLterm i c]
    congr 1
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun c _ => iLterm i c
  have hCi : ∫ ω, Ct ω ∂(μ Wt L) = (γ : ℂ) * ∑ i : Fin k, ∑ j : Fin k, if i < j then
      ∑ c : Fin L, ∫ ω, NX _ (cutLLab a i j c) (cutLSgn σ i j) ω *
        NX _ (cutRLab a i j c) (cutRSgn σ i j) ω ∂(μ Wt L) else 0 := by
    rw [integral_const_mul]
    congr 1
    have h := auxHierarchy_integral_cut (fun i j c ω => if i < j then
      NX _ (cutLLab a i j c) (cutLSgn σ i j) ω * NX _ (cutRLab a i j c) (cutRSgn σ i j) ω else 0)
      iCterm'
    refine Eq.trans ?_ (h.trans ?_)
    · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [cutSumFam]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i < j <;> simp [hij]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i < j <;> simp [hij]
  have hAux : cutSumFam (auxLoop g Wt L E m t) a σ = ∑ i : Fin k, ∑ j : Fin k, if i < j then
      ∑ c : Fin L, (∫ ω, NX _ (cutLLab a i j c) (cutLSgn σ i j) ω ∂(μ Wt L)) *
        ∫ ω, NX _ (cutRLab a i j c) (cutRSgn σ i j) ω ∂(μ Wt L) else 0 := by
    simp only [cutSumFam, hNXi]
  rw [hd, integral_add iLt iCt, hLi, hCi, hAux, add_sub_assoc, ← mul_sub, auxHierarchy_cut_sub]
  -- the bounds
  have hLb : ‖∑ i : Fin k, ∑ c : Fin L,
      ∫ ω, (loopTr (G ω) ![c] ![σ i] - sgnScalar m (σ i)) *
        NX (k + 1) (insLab a i c) (insSgn σ i) ω ∂(μ Wt L)‖ ≤
      k * L * (B * ((Cv 1 + 1) / 2 + C1) / Wt) := by
    refine auxHierarchy_norm_double_le _ fun i c => ?_
    refine auxHierarchy_light_le (hX1c i c) (hNXc _ _ _) (hX1b i c)
      (hNXb _ _ _ (by omega) le_rfl) (sgnScalar m (σ i)) hW' ?_ ?_
    · rw [hX1i]
      have h := (hCv 1 le_rfl Wt hWt t ht0.le htT.le ![c] ![σ i]).2
      simp only [Nat.sub_self, pow_zero, one_mul] at h
      exact h
    · rw [hX1i]
      exact hone Wt hWt t ht0.le htT.le c (σ i)
  have hCb : ‖∑ i : Fin k, ∑ j : Fin k, if i < j then ∑ c : Fin L,
      ((∫ ω, NX _ (cutLLab a i j c) (cutLSgn σ i j) ω *
        NX _ (cutRLab a i j c) (cutRSgn σ i j) ω ∂(μ Wt L)) -
        (∫ ω, NX _ (cutLLab a i j c) (cutLSgn σ i j) ω ∂(μ Wt L)) *
          ∫ ω, NX _ (cutRLab a i j c) (cutRSgn σ i j) ω ∂(μ Wt L)) else 0‖ ≤
      k * k * L * (Cm / Wt) := by
    refine auxHierarchy_norm_cut_le _ (by positivity) fun i j c hij => ?_
    have hij' : i.val < j.val := hij
    have hj := j.isLt
    refine (auxHierarchy_cov_le (hNXc _ _ _) (hNXc _ _ _)
      (hNXb _ _ _ (by omega) (by omega)) (hNXb _ _ _ (by omega) (by omega))
      (v₁ := Cv (k + i.val - j.val + 1) / (Wt : ℝ) ^ 2)
      (v₂ := Cv (j.val - i.val + 1) / (Wt : ℝ) ^ 2) ?_ ?_).trans ?_
    · rw [hNXi]; exact (hCv _ (by omega) Wt hWt t ht0.le htT.le _ _).2
    · rw [hNXi]; exact (hCv _ (by omega) Wt hWt t ht0.le htT.le _ _).2
    · have h1 := hCm_le (k + i.val - j.val + 1) (by omega)
      have h2 := hCm_le (j.val - i.val + 1) (by omega)
      have hW1 : (1 : ℝ) ≤ Wt := by exact_mod_cast hWt
      have hW2 : (Wt : ℝ) ≤ (Wt : ℝ) ^ 2 := by nlinarith
      calc (Cv (k + i.val - j.val + 1) / (Wt : ℝ) ^ 2 + Cv (j.val - i.val + 1) / (Wt : ℝ) ^ 2) / 2
          ≤ (Cm / (Wt : ℝ) ^ 2 + Cm / (Wt : ℝ) ^ 2) / 2 := by gcongr
        _ = Cm / (Wt : ℝ) ^ 2 := by ring
        _ ≤ Cm / Wt := div_le_div_of_nonneg_left hCm0 hW' hW2
  calc ‖(γ : ℂ) * _ + (γ : ℂ) * _‖
      ≤ ‖(γ : ℂ) * _‖ + ‖(γ : ℂ) * _‖ := norm_add_le _ _
    _ ≤ γ * (k * L * (B * ((Cv 1 + 1) / 2 + C1) / Wt)) + γ * (k * k * L * (Cm / Wt)) := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hγ]
        gcongr
    _ = (C - 1) / Wt := by rw [hCdef]; field_simp; ring
    _ ≤ C / Wt := by gcongr; linarith

end LSBA
