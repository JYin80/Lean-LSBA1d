import LSBA.Upper.ConversionTail
import LSBA.Transfer.Path

/-!
# A priori fractional moments of resolvent blocks

(8.7) [eq:c-apriori]: `𝔼‖G(x, y)‖^p ≤ C_p (W²/c)^p` for every deterministic Hermitian `K₀`, and the
corollaries for the block path with Hermitian shifts and for the cycle, uniformly in `E`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `C_p = (4/√π)^p / (1 - p)`, the constant of (8.7) [eq:c-apriori]. -/
def aprioriConst (p : ℝ) : ℝ := (4 / Real.sqrt π) ^ p / (1 - p)

/-- Each entry of a GUE block is a measurable function of the sample. -/
private lemma apriori_measurable_gueBlock_apply {W n : ℕ} (a : Fin n) (α β : Fin W) :
    Measurable fun ω : Ω W n => gueBlock W n ω a α β := by
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs
  · fun_prop
  · fun_prop
  · fun_prop

/-- The matrix inverse is measurable. -/
private lemma apriori_measurable_inv {m : Type*} [Fintype m] [DecidableEq m] :
    Measurable fun A : Matrix m m ℂ => A⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hd : Measurable fun A : Matrix m m ℂ => A.det :=
    (continuous_id.matrix_det).measurable
  have ha : Measurable fun A : Matrix m m ℂ => A.adjugate i j :=
    (continuous_id.matrix_adjugate).measurable.eval_matrix
  exact (hd.inv).mul ha

/-- The norm of a block of the resolvent is a measurable function of the sample. -/
private lemma apriori_measurable_norm {W n : ℕ}
    (K₀ : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (c E : ℝ) (x y : Fin n) :
    Measurable fun ω : Ω W n =>
      ‖blockOf (resolventMat (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω)) E) x y‖ := by
  have hmat : Measurable fun ω : Ω W n => K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω) -
      (E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) := by
    refine Measurable.of_eval_matrix _ fun p q => ?_
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, blockDiagOp,
      Matrix.of_apply, smul_eq_mul]
    by_cases h : p.1 = q.1
    · simp only [h, ite_true]
      have := apriori_measurable_gueBlock_apply (W := W) (n := n) q.1 p.2 q.2
      fun_prop
    · simp only [h, ite_false]
      fun_prop
  have hres : Measurable fun ω : Ω W n =>
      resolventMat (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω)) E :=
    apriori_measurable_inv.comp hmat
  have hblk : Measurable fun X : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ => blockOf X x y := by
    refine Measurable.of_eval_matrix _ fun α β => ?_
    exact measurable_id.eval_matrix (i := (x, α)) (j := (y, β))
  exact continuous_norm.measurable.comp (hblk.comp hres)

/-- Layer-cake integral of the tail profile `min{1, M/t}`. -/
private lemma apriori_layer {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 0 ≤ M)
    (m : ℝ → ℝ≥0∞) (h1 : ∀ t, 0 < t → m t ≤ 1)
    (h2 : ∀ t, 0 < t → m t ≤ ENNReal.ofReal (M / t)) :
    ENNReal.ofReal p * ∫⁻ t in Set.Ioi 0, m t * ENNReal.ofReal (t ^ (p - 1)) ≤
      ENNReal.ofReal (M ^ p / (1 - p)) := by
  rcases hM.eq_or_lt with rfl | hM
  · have : ∀ t ∈ Set.Ioi (0 : ℝ), m t * ENNReal.ofReal (t ^ (p - 1)) = 0 := by
      intro t ht
      have := h2 t ht
      simp only [zero_div, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at this
      simp [this]
    rw [setLIntegral_congr_fun measurableSet_Ioi this]
    simp
  · have hsub : ∀ t ∈ Set.Ioi (0 : ℝ), m t * ENNReal.ofReal (t ^ (p - 1)) ≤
        (Set.Ioc 0 M).indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t +
        (Set.Ioi M).indicator (fun t => ENNReal.ofReal (M * t ^ (p - 2))) t := by
      intro t ht
      have ht0 : 0 < t := ht
      by_cases htM : t ≤ M
      · have hmem : t ∈ Set.Ioc 0 M := ⟨ht0, htM⟩
        have hn : t ∉ Set.Ioi M := by simpa using htM
        rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hn, add_zero]
        calc m t * ENNReal.ofReal (t ^ (p - 1)) ≤ 1 * ENNReal.ofReal (t ^ (p - 1)) :=
              mul_le_mul_left (h1 t ht0) _
          _ = _ := one_mul _
      · have htM' : M < t := not_le.mp htM
        have hmem : t ∈ Set.Ioi M := htM'
        have hn : t ∉ Set.Ioc 0 M := fun h => htM h.2
        rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hn, zero_add]
        calc m t * ENNReal.ofReal (t ^ (p - 1)) ≤
              ENNReal.ofReal (M / t) * ENNReal.ofReal (t ^ (p - 1)) :=
              mul_le_mul_left (h2 t ht0) _
          _ = ENNReal.ofReal (M / t * t ^ (p - 1)) :=
              (ENNReal.ofReal_mul (by positivity)).symm
          _ = ENNReal.ofReal (M * t ^ (p - 2)) := by
              congr 1
              rw [show p - 2 = (p - 1) + (-1) by ring, Real.rpow_add ht0, Real.rpow_neg_one]
              field_simp
    have hI1 : ∫⁻ t in Set.Ioc 0 M, ENNReal.ofReal (t ^ (p - 1)) = ENNReal.ofReal (M ^ p / p) := by
      have hint : IntervalIntegrable (fun t : ℝ => t ^ (p - 1)) volume 0 M :=
        intervalIntegral.intervalIntegrable_rpow' (by linarith)
      have := intervalIntegral.integral_of_le (μ := volume) (f := fun t : ℝ => t ^ (p - 1)) hM.le
      rw [← ofReal_integral_eq_lintegral_ofReal (hint.1)
        (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
          have : 0 < t := ht.1
          positivity), ← this, integral_rpow (Or.inl (by linarith))]
      congr 1
      rw [show p - 1 + 1 = p by ring, Real.zero_rpow hp0.ne']
      ring
    have hI2 : ∫⁻ t in Set.Ioi M, ENNReal.ofReal (M * t ^ (p - 2)) =
        ENNReal.ofReal (M ^ p / (1 - p)) := by
      have hint : IntegrableOn (fun t : ℝ => t ^ (p - 2)) (Set.Ioi M) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) hM
      rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul M)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
          have : 0 < t := hM.trans ht
          positivity), integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hM]
      congr 1
      rw [show p - 2 + 1 = p - 1 by ring]
      have h3 : M ^ p = M * M ^ (p - 1) := by
        conv_lhs => rw [show p = 1 + (p - 1) by ring, Real.rpow_add hM, Real.rpow_one]
      rw [h3]
      have : (p - 1) ≠ 0 := by linarith
      field_simp
      ring
    calc ENNReal.ofReal p * ∫⁻ t in Set.Ioi 0, m t * ENNReal.ofReal (t ^ (p - 1))
        ≤ ENNReal.ofReal p * ∫⁻ t in Set.Ioi 0,
            ((Set.Ioc 0 M).indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t +
              (Set.Ioi M).indicator (fun t => ENNReal.ofReal (M * t ^ (p - 2))) t) :=
          mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi hsub) _
      _ ≤ ENNReal.ofReal p * (ENNReal.ofReal (M ^ p / p) + ENNReal.ofReal (M ^ p / (1 - p))) := by
          refine mul_le_mul_right ?_ _
          have hm1 : Measurable ((Set.Ioc (0 : ℝ) M).indicator
              fun t => ENNReal.ofReal (t ^ (p - 1))) :=
            Measurable.indicator (by fun_prop) measurableSet_Ioc
          rw [lintegral_add_left hm1, lintegral_indicator measurableSet_Ioc,
            lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioc,
            Measure.restrict_restrict measurableSet_Ioi]
          refine add_le_add ?_ ?_
          · rw [← hI1]
            exact lintegral_mono_set Set.inter_subset_left
          · rw [← hI2]
            exact lintegral_mono_set Set.inter_subset_left
      _ = ENNReal.ofReal (M ^ p / (1 - p)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by
            have : 0 < 1 - p := by linarith
            positivity), ← ENNReal.ofReal_mul hp0.le]
          congr 1
          have : 1 - p ≠ 0 := by linarith
          field_simp
          ring

/-- (8.7) [eq:c-apriori], generic form: `𝔼‖G(x, y)‖^p ≤ C_p (W²/c)^p` for `K₀ + c · diag(V_a)`. -/
theorem resolvent_block_moment_le {W n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {c : ℝ}
    (hc : 0 < c) (K₀ : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (hK₀ : K₀.IsHermitian) (E : ℝ)
    (x y : Fin n) :
    ∫⁻ ω, ‖blockOf (resolventMat (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω)) E) x y‖ₑ ^ p
        ∂(μ W n) ≤ ENNReal.ofReal (aprioriConst p * ((W : ℝ) ^ 2 / c) ^ p) := by
  set f : Ω W n → ℝ := fun ω =>
    ‖blockOf (resolventMat (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω)) E) x y‖ with hf
  have hfm : Measurable f := apriori_measurable_norm K₀ c E x y
  have hconv : ∀ ω, ‖blockOf (resolventMat (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω)) E) x y‖ₑ
      ^ p = ENNReal.ofReal (f ω ^ p) := by
    intro ω
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  simp only [hconv]
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul (μ W n)
    (Filter.Eventually.of_forall fun ω => norm_nonneg _) hfm.aemeasurable hp0]
  set M : ℝ := 4 / Real.sqrt π * (W : ℝ) ^ 2 / c with hM
  have hM0 : 0 ≤ M := by positivity
  have key := apriori_layer hp0 hp1 hM0 (fun t => (μ W n) {ω | t < f ω})
    (fun t _ => prob_le_one) (fun t ht => by
      have := resolvent_block_tail_le (W := W) (n := n) hc K₀ hK₀ E x y ht
      rwa [show 4 / Real.sqrt π * (W : ℝ) ^ 2 / (c * t) = M / t by rw [hM]; field_simp] at this)
  refine key.trans (le_of_eq ?_)
  congr 1
  rw [hM, aprioriConst, show 4 / Real.sqrt π * (W : ℝ) ^ 2 / c = 4 / Real.sqrt π * ((W : ℝ) ^ 2 / c)
    by ring, Real.mul_rpow (by positivity) (by positivity)]
  ring

private lemma apriori_blockDiagOp_zero {W n : ℕ} :
    blockDiagOp (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) = 0 := by
  ext p q
  simp [blockDiagOp]

/-- (8.7) [eq:c-apriori] on a block interval with Hermitian endpoint shifts (8.5)
[up:eq:shifted-resolvent]. -/
theorem pathOp_moment_le (g : ℝ) {W n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {L₀ R₀ : Matrix (Fin W) (Fin W) ℂ} (hL₀ : L₀.IsHermitian) (hR₀ : R₀.IsHermitian) (E : ℝ)
    (x y : Fin n) :
    ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W n ω) L₀ R₀) E) x y‖ₑ ^ p ∂(μ W n) ≤
      ENNReal.ofReal (aprioriConst p * (max 1 g * (W : ℝ) ^ 2) ^ p) := by
  have hm : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hdecomp : ∀ ω, pathOp g (gueBlock W n ω) L₀ R₀ =
      pathOp g (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) L₀ R₀ +
        (((max 1 g)⁻¹ : ℝ) : ℂ) • blockDiagOp (gueBlock W n ω) := by
    intro ω
    simp only [pathOp, apriori_blockDiagOp_zero, add_zero, smul_add, Complex.ofReal_inv]
    abel
  have hK : (pathOp g (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) L₀ R₀).IsHermitian :=
    pathOp_isHermitian g (fun _ => Matrix.isHermitian_zero) hL₀ hR₀
  have := resolvent_block_moment_le (W := W) (n := n) hp0 hp1 (inv_pos.mpr hm) _ hK E x y
  simp only [← hdecomp] at this
  rwa [div_inv_eq_mul, mul_comm ((W : ℝ) ^ 2)] at this

/-- (8.7) [eq:c-apriori] on the cycle of `L` blocks, (1.3) [eq:model]. -/
theorem Hmat_moment_le (g : ℝ) {W L : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (E : ℝ)
    (x y : Fin L) :
    ∫⁻ ω, ‖blockOf (resolventMat (Hmat g W L ω) E) x y‖ₑ ^ p ∂(μ W L) ≤
      ENNReal.ofReal (aprioriConst p * (max 1 g * (W : ℝ) ^ 2) ^ p) := by
  have hm : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hdecomp : ∀ ω, Hmat g W L ω =
      Hdet g (fun _ : Fin L => (0 : Matrix (Fin W) (Fin W) ℂ)) +
        (((max 1 g)⁻¹ : ℝ) : ℂ) • blockDiagOp (gueBlock W L ω) := by
    intro ω
    simp only [Hmat, Hdet, apriori_blockDiagOp_zero, add_zero, smul_add, Complex.ofReal_inv]
  have hK : (Hdet g (fun _ : Fin L => (0 : Matrix (Fin W) (Fin W) ℂ))).IsHermitian :=
    Hdet_isHermitian g (fun _ => Matrix.isHermitian_zero)
  have := resolvent_block_moment_le (W := W) (n := L) hp0 hp1 (inv_pos.mpr hm) _ hK E x y
  simp only [← hdecomp] at this
  rwa [div_inv_eq_mul, mul_comm ((W : ℝ) ^ 2)] at this

end LSBA
