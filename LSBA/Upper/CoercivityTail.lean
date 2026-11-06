import LSBA.Upper.CoercivityMean

/-!
# The small-singular-value bound (G.11) [cg:eq:SG]

(G.11) [cg:eq:SG] with explicit constants: for `128` independent GUE blocks with the covariance
(1.2) [eq:covariance] and large `W`, `P(S_W(G) < 5/2) ≤ 2 exp(-25W/(8π²))`, by Gaussian
concentration of the `2W^{-1/2}`-Lipschitz function `S_W` around its mean `≥ 5` (Appendix G.4
[app:compact-gaussian]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

section CoercivityTailAux

/-- The squared modulus of an entry of a block is `(x² + y²) / (2W)` for its two coordinates. -/
private lemma CoercivityTail_norm_sq_entry (W m : ℕ) (ω : Ω W m) (a : Fin m) (α β : Fin W) :
    ‖gueBlock W m ω a α β‖ ^ 2 = (ω (a, α, β) ^ 2 + ω (a, β, α) ^ 2) / (2 * W) := by
  have hW : (0 : ℝ) < W := by exact_mod_cast Fin.pos α
  have h2 : Real.sqrt (2 * (W : ℝ)) ^ 2 = 2 * W := Real.sq_sqrt (by positivity)
  have h1 : Real.sqrt (W : ℝ) ^ 2 = W := Real.sq_sqrt hW.le
  simp only [gueBlock, Matrix.of_apply]
  split_ifs with hab hlt
  · subst hab
    rw [norm_div, Complex.norm_real, Complex.norm_real, div_pow, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs, sq_abs, h1]
    field_simp
    ring
  · rw [norm_div, Complex.norm_real, div_pow, Real.norm_eq_abs, sq_abs, h2]
    have : ‖(ω (a, α, β) : ℂ) + Complex.I * (ω (a, β, α) : ℂ)‖ ^ 2 =
        ω (a, α, β) ^ 2 + ω (a, β, α) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    rw [this]
  · rw [norm_div, Complex.norm_real, div_pow, Real.norm_eq_abs, sq_abs, h2]
    have : ‖(ω (a, β, α) : ℂ) - Complex.I * (ω (a, α, β) : ℂ)‖ ^ 2 =
        ω (a, α, β) ^ 2 + ω (a, β, α) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    rw [this]

/-- `Σ_j ‖G_j‖_HS² = W⁻¹ Σ_x ω_x²` in the standard coordinates. -/
private lemma CoercivityTail_sum_hsSq (W m : ℕ) (ω : Ω W m) :
    ∑ j, hsSq (gueBlock W m ω j) = (∑ x : Fin m × Fin W × Fin W, ω x ^ 2) / W := by
  unfold hsSq
  simp only [CoercivityTail_norm_sq_entry, Fintype.sum_prod_type]
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp
  have hW' : (W : ℝ) ≠ 0 := by positivity
  have hsw : ∀ j : Fin m, ∑ α : Fin W, ∑ β : Fin W, ω (j, β, α) ^ 2 =
      ∑ α : Fin W, ∑ β : Fin W, ω (j, α, β) ^ 2 := fun j => Finset.sum_comm
  simp only [← Finset.sum_div, Finset.sum_add_distrib, hsw]
  field_simp
  ring

/-- The block map is real-linear. -/
private lemma CoercivityTail_gueBlock_sub (W m : ℕ) (ω ω' : Ω W m) (j : Fin m) :
    gueBlock W m (ω - ω') j = gueBlock W m ω j - gueBlock W m ω' j := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Matrix.sub_apply, Pi.sub_apply]
  split_ifs <;> push_cast <;> ring

/-- `S_W` is `2 W^{-1/2}`-Lipschitz in the standard coordinates. -/
private lemma CoercivityTail_lipschitz (W m : ℕ) :
    LipschitzWith (Real.toNNReal (2 / Real.sqrt W))
      (fun x : EuclideanSpace ℝ (Fin m × Fin W × Fin W) => coerMin (gueBlock W m x.ofLp)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := abs_coerMin_sub_le (gueBlock W m x.ofLp) (gueBlock W m y.ofLp)
  have hs : ∑ j, hsSq (gueBlock W m x.ofLp j - gueBlock W m y.ofLp j) =
      (∑ i, (x.ofLp i - y.ofLp i) ^ 2) / W := by
    have := CoercivityTail_sum_hsSq W m (x.ofLp - y.ofLp)
    simpa only [CoercivityTail_gueBlock_sub, Pi.sub_apply] using this
  rw [hs] at h
  have hd : dist x y = Real.sqrt (∑ i, (x.ofLp i - y.ofLp i) ^ 2) := by
    rw [EuclideanSpace.dist_eq]
    simp [Real.dist_eq, sq_abs]
  rw [Real.dist_eq, hd, Real.coe_toNNReal _ (by positivity)]
  refine h.trans (le_of_eq ?_)
  rw [Real.sqrt_div (by positivity)]
  ring

end CoercivityTailAux

/-- (G.11) [cg:eq:SG] with `τ = 5/2`, `c = 25/(8π²)`, `C = 2`: for large `W`,
`P(S_W(G) < 5/2) ≤ 2 exp(-25W/(8π²))`. -/
theorem coerMin_lt_prob_le :
    ∃ W₀ : ℕ, ∀ W, W₀ ≤ W →
      μ W 128 {ω | coerMin (gueBlock W 128 ω) < 5 / 2} ≤
        ENNReal.ofReal (2 * Real.exp (-(25 * W) / (8 * π ^ 2))) := by
  obtain ⟨W₀, h⟩ := coerMin_mean_ge
  refine ⟨max W₀ 1, fun W hW => ?_⟩
  have hW0 : W₀ ≤ W := (le_max_left _ _).trans hW
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hM := h W hW0
  have hc := concentration_lipschitz
    (fun x : Fin 128 × Fin W × Fin W → ℝ => coerMin (gueBlock W 128 x))
    (Real.toNNReal (2 / Real.sqrt W)) (CoercivityTail_lipschitz W 128) (5 / 2) (by norm_num)
  have hK : ((Real.toNNReal (2 / Real.sqrt W) : ℝ≥0) : ℝ) ^ 2 = 4 / W := by
    rw [Real.coe_toNNReal _ (by positivity), div_pow, Real.sq_sqrt hWpos.le]
    norm_num
  have hexp : -(2 * (5 / 2 : ℝ) ^ 2) / (π ^ 2 * ((Real.toNNReal (2 / Real.sqrt W) : ℝ≥0) : ℝ) ^ 2) =
      -(25 * W) / (8 * π ^ 2) := by
    rw [hK]
    have : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [hexp] at hc
  refine le_trans (measure_mono ?_) hc
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have : (∫ y, coerMin (gueBlock W 128 y) ∂(stdGauss (Fin 128 × Fin W × Fin W))) =
      ∫ ω, coerMin (gueBlock W 128 ω) ∂(μ W 128) := rfl
  rw [this]
  rw [abs_sub_comm]
  rw [abs_of_pos (by linarith)]
  linarith

end LSBA
