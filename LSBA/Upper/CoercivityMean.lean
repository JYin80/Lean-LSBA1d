import LSBA.Upper.CoercivityDecouple
import LSBA.Upper.CoercivityTensor
import LSBA.Gauss.LipschitzConc

/-!
# Mean bounds for `S_W` at `m = 128`

For `128` independent GUE blocks with the covariance (1.2) [eq:covariance]: the non-asymptotic
form of (G.16) [cg:eq:positive], `𝔼 S_W² ≥ 2·78 - 4·28.5 = 42 ≥ 40` for large `W` (from (G.13)
[cg:eq:coercive], (G.14) [cg:eq:decouple] and the two spectral inputs), and `𝔼 S_W ≥ 5` for large
`W` (from `Var S_W ≤ 4π²/W`, `S_W` being `2W^{-1/2}`-Lipschitz in the standard coordinates;
Appendix G.4 [app:compact-gaussian]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

section CoercivityMeanAux

/-- A coordinate of a standard Gaussian vector is square integrable. -/
private lemma CoercivityMean_memLp_coord (W m : ℕ) (x : Fin m × Fin W × Fin W) :
    MemLp (fun ω : Ω W m => ω x) 2 (μ W m) := by
  have h : MemLp id 2 (gaussianReal (0 : ℝ) 1) := memLp_id_gaussianReal' 2 ENNReal.ofNat_ne_top
  exact h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m × Fin W × Fin W =>
    gaussianReal (0 : ℝ) 1) x)

/-- The squared modulus of an entry of a block is `(x² + y²) / (2W)` for its two coordinates. -/
private lemma CoercivityMean_norm_sq_entry (W m : ℕ) (ω : Ω W m) (a : Fin m) (α β : Fin W) :
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
private lemma CoercivityMean_sum_hsSq (W m : ℕ) (ω : Ω W m) :
    ∑ j, hsSq (gueBlock W m ω j) = (∑ x : Fin m × Fin W × Fin W, ω x ^ 2) / W := by
  unfold hsSq
  simp only [CoercivityMean_norm_sq_entry, Fintype.sum_prod_type]
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp
  have hW' : (W : ℝ) ≠ 0 := by positivity
  have hsw : ∀ j : Fin m, ∑ α : Fin W, ∑ β : Fin W, ω (j, β, α) ^ 2 =
      ∑ α : Fin W, ∑ β : Fin W, ω (j, α, β) ^ 2 := fun j => Finset.sum_comm
  simp only [← Finset.sum_div, Finset.sum_add_distrib, hsw]
  field_simp
  ring

/-- The block map is real-linear. -/
private lemma CoercivityMean_gueBlock_sub (W m : ℕ) (ω ω' : Ω W m) (j : Fin m) :
    gueBlock W m (ω - ω') j = gueBlock W m ω j - gueBlock W m ω' j := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Matrix.sub_apply, Pi.sub_apply]
  split_ifs <;> push_cast <;> ring

/-- `S_W` is `2 W^{-1/2}`-Lipschitz in the standard coordinates. -/
private lemma CoercivityMean_lipschitz (W m : ℕ) :
    LipschitzWith (Real.toNNReal (2 / Real.sqrt W))
      (fun x : EuclideanSpace ℝ (Fin m × Fin W × Fin W) => coerMin (gueBlock W m x.ofLp)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := abs_coerMin_sub_le (gueBlock W m x.ofLp) (gueBlock W m y.ofLp)
  have hs : ∑ j, hsSq (gueBlock W m x.ofLp j - gueBlock W m y.ofLp j) =
      (∑ i, (x.ofLp i - y.ofLp i) ^ 2) / W := by
    have := CoercivityMean_sum_hsSq W m (x.ofLp - y.ofLp)
    simpa only [CoercivityMean_gueBlock_sub, Pi.sub_apply] using this
  rw [hs] at h
  have hd : dist x y = Real.sqrt (∑ i, (x.ofLp i - y.ofLp i) ^ 2) := by
    rw [EuclideanSpace.dist_eq]
    simp [Real.dist_eq, sq_abs]
  rw [Real.dist_eq, hd, Real.coe_toNNReal _ (by positivity)]
  refine h.trans (le_of_eq ?_)
  rw [Real.sqrt_div (by positivity)]
  ring

/-- `S_W` of the block family is continuous in the coordinates. -/
private lemma CoercivityMean_continuous (W m : ℕ) :
    Continuous fun ω : Ω W m => coerMin (gueBlock W m ω) :=
  (CoercivityMean_lipschitz W m).continuous.comp (PiLp.continuous_toLp 2 _)

/-- `S_W(G)² ≤ 4 W⁻¹ Σ_x ω_x²`. -/
private lemma CoercivityMean_sq_le (W m : ℕ) (ω : Ω W m) :
    coerMin (gueBlock W m ω) ^ 2 ≤ 4 * ((∑ x : Fin m × Fin W × Fin W, ω x ^ 2) / W) := by
  have h0 : gueBlock W m (0 : Ω W m) = 0 := by
    funext j; ext α β
    simp only [gueBlock, Matrix.of_apply, Pi.zero_apply]
    split_ifs <;> simp
  have hS0 : coerMin (gueBlock W m (0 : Ω W m)) = 0 := by
    have := coerMin_le (gueBlock W m (0 : Ω W m))
    rw [h0] at this ⊢
    have h00 : 2 * Real.sqrt (∑ j, ‖(0 : Fin m → Matrix (Fin W) (Fin W) ℂ) j‖ ^ 2) = 0 := by simp
    rw [h00] at this
    exact le_antisymm this.2 this.1
  have h := abs_coerMin_sub_le (gueBlock W m ω) (gueBlock W m 0)
  rw [hS0, sub_zero, h0] at h
  have hnn := (coerMin_le (gueBlock W m ω)).1
  have h' : coerMin (gueBlock W m ω) ≤ 2 * Real.sqrt (∑ j, hsSq (gueBlock W m ω j)) := by
    refine (le_abs_self _).trans (h.trans (le_of_eq ?_))
    simp
  rw [CoercivityMean_sum_hsSq] at h'
  have hq : 0 ≤ (∑ x : Fin m × Fin W × Fin W, ω x ^ 2) / W := by positivity
  calc coerMin (gueBlock W m ω) ^ 2
      ≤ (2 * Real.sqrt ((∑ x : Fin m × Fin W × Fin W, ω x ^ 2) / W)) ^ 2 :=
        pow_le_pow_left₀ hnn h' 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hq]; ring

/-- The Gaussian polynomial `W⁻¹ Σ_x ω_x²` is integrable. -/
private lemma CoercivityMean_integrable_quad (W m : ℕ) :
    Integrable (fun ω : Ω W m => (∑ x : Fin m × Fin W × Fin W, ω x ^ 2) / W) (μ W m) :=
  (integrable_finsetSum _ fun x _ => (CoercivityMean_memLp_coord W m x).integrable_sq).div_const _

/-- `S_W²` and `S_W` are integrable. -/
private lemma CoercivityMean_integrable_sq (W m : ℕ) :
    Integrable (fun ω : Ω W m => coerMin (gueBlock W m ω) ^ 2) (μ W m) :=
  ((CoercivityMean_integrable_quad W m).const_mul 4).mono'
    ((CoercivityMean_continuous W m).pow 2).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact CoercivityMean_sq_le W m ω)

private lemma CoercivityMean_integrable (W m : ℕ) :
    Integrable (fun ω : Ω W m => coerMin (gueBlock W m ω)) (μ W m) := by
  refine ((CoercivityMean_integrable_sq W m).add (integrable_const (1 : ℝ))).mono'
    (CoercivityMean_continuous W m).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (coerMin_le _).1]
  change coerMin (gueBlock W m ω) ≤ coerMin (gueBlock W m ω) ^ 2 + 1
  nlinarith [sq_nonneg (coerMin (gueBlock W m ω) - 1)]

/-- The squared Hilbert–Schmidt norm is submultiplicative. -/
private lemma CoercivityMean_hsSq_mul_le {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) :
    hsSq (A * B) ≤ hsSq A * hsSq B := by
  unfold hsSq
  have hB : ∑ k, ∑ j, ‖B j k‖ ^ 2 = ∑ j, ∑ k, ‖B j k‖ ^ 2 := Finset.sum_comm
  calc ∑ i, ∑ k, ‖(A * B) i k‖ ^ 2
      ≤ ∑ i, ∑ k, (∑ j, ‖A i j‖ ^ 2) * (∑ j, ‖B j k‖ ^ 2) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
        have h1 : ‖(A * B) i k‖ ≤ ∑ j, ‖A i j‖ * ‖B j k‖ := by
          rw [Matrix.mul_apply]
          exact (norm_sum_le _ _).trans (by simp)
        have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖) (fun j => ‖B j k‖)
        calc ‖(A * B) i k‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖B j k‖) ^ 2 := by gcongr
          _ ≤ _ := h2
    _ = (∑ i, ∑ j, ‖A i j‖ ^ 2) * ∑ j, ∑ k, ‖B j k‖ ^ 2 := by
        rw [← hB, Finset.sum_mul_sum]

/-- `hsSq` is invariant under the conjugate transpose. -/
private lemma CoercivityMean_hsSq_conjTranspose {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    hsSq Aᴴ = hsSq A := by
  unfold hsSq
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

/-- `|Tr(P* X)| ≤ ‖P‖_HS ‖X‖_HS`. -/
private lemma CoercivityMean_norm_trace_le {W : ℕ} (P X : Matrix (Fin W) (Fin W) ℂ) :
    ‖(Pᴴ * X).trace‖ ≤ Real.sqrt (hsSq P) * Real.sqrt (hsSq X) := by
  have h1 : ‖(Pᴴ * X).trace‖ ≤ ∑ a : Fin W × Fin W, ‖P a.2 a.1‖ * ‖X a.2 a.1‖ := by
    rw [Matrix.trace, Fintype.sum_prod_type]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
    rw [norm_mul, Matrix.conjTranspose_apply, norm_star]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a : Fin W × Fin W => ‖P a.2 a.1‖)
    (fun a : Fin W × Fin W => ‖X a.2 a.1‖)
  have hP : ∑ a : Fin W × Fin W, ‖P a.2 a.1‖ ^ 2 = hsSq P := by
    unfold hsSq
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hX : ∑ a : Fin W × Fin W, ‖X a.2 a.1‖ ^ 2 = hsSq X := by
    unfold hsSq
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hP, hX] at h2
  rw [← Real.sqrt_mul (by unfold hsSq; positivity)]
  refine h1.trans ?_
  have hnn : 0 ≤ ∑ a : Fin W × Fin W, ‖P a.2 a.1‖ * ‖X a.2 a.1‖ := by positivity
  exact Real.le_sqrt_of_sq_le h2

/-- `‖I‖_HS² = W`. -/
private lemma CoercivityMean_hsSq_one (W : ℕ) : hsSq (1 : Matrix (Fin W) (Fin W) ℂ) = W := by
  unfold hsSq
  have : ∀ a b : Fin W, ‖(1 : Matrix (Fin W) (Fin W) ℂ) a b‖ ^ 2 = if a = b then 1 else 0 := by
    intro a b
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  simp [this]

/-- `|Tr P| ≤ √W` for `‖P‖_HS = 1`. -/
private lemma CoercivityMean_norm_trace_sq_le {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : hsSq P = 1) : ‖P.trace‖ * ‖P.trace‖ ≤ W := by
  have h := CoercivityMean_norm_trace_le (1 : Matrix (Fin W) (Fin W) ℂ) P
  rw [Matrix.conjTranspose_one, one_mul, CoercivityMean_hsSq_one, hP, Real.sqrt_one, mul_one] at h
  calc ‖P.trace‖ * ‖P.trace‖ ≤ Real.sqrt W * Real.sqrt W := by gcongr
    _ = W := Real.mul_self_sqrt (Nat.cast_nonneg _)

/-- A uniform bound for the quantity inside the supremum defining `numRad`, for `‖P‖_HS = 1`. -/
private lemma CoercivityMean_term_le {m W : ℕ} (hW : 0 < W)
    (G : Fin m → Matrix (Fin W) (Fin W) ℂ) {P : Matrix (Fin W) (Fin W) ℂ} (hP : hsSq P = 1) :
    |(Pᴴ * (phiMap G P -
      ((m : ℂ) / W * star P.trace) • (1 : Matrix (Fin W) (Fin W) ℂ))).trace.re| ≤
      ∑ j, hsSq (G j) + m := by
  have hPh : hsSq Pᴴ = 1 := by rw [CoercivityMean_hsSq_conjTranspose, hP]
  have hA : ‖(Pᴴ * phiMap G P).trace‖ ≤ ∑ j, hsSq (G j) := by
    unfold phiMap
    rw [Matrix.mul_sum, Matrix.trace_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (CoercivityMean_norm_trace_le _ _).trans ?_
    rw [hP, Real.sqrt_one, one_mul]
    have h3 : hsSq (G j * Pᴴ * G j) ≤ hsSq (G j) ^ 2 := by
      calc hsSq (G j * Pᴴ * G j) ≤ hsSq (G j * Pᴴ) * hsSq (G j) :=
            CoercivityMean_hsSq_mul_le _ _
        _ ≤ (hsSq (G j) * hsSq Pᴴ) * hsSq (G j) := by
            gcongr
            · unfold hsSq; positivity
            · exact CoercivityMean_hsSq_mul_le _ _
        _ = hsSq (G j) ^ 2 := by rw [hPh]; ring
    calc Real.sqrt (hsSq (G j * Pᴴ * G j)) ≤ Real.sqrt (hsSq (G j) ^ 2) := Real.sqrt_le_sqrt h3
      _ = hsSq (G j) := Real.sqrt_sq (by unfold hsSq; positivity)
  have hB : ‖(Pᴴ * (((m : ℂ) / W * star P.trace) • (1 : Matrix (Fin W) (Fin W) ℂ))).trace‖ ≤
      m := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_conjTranspose,
      smul_eq_mul, norm_mul, norm_mul, norm_div, norm_star, Complex.norm_natCast,
      Complex.norm_natCast]
    have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
    have := CoercivityMean_norm_trace_sq_le hP
    calc (m : ℝ) / W * ‖P.trace‖ * ‖P.trace‖ = (m : ℝ) / W * (‖P.trace‖ * ‖P.trace‖) := by ring
      _ ≤ (m : ℝ) / W * W := by gcongr
      _ = m := by field_simp
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [Matrix.mul_sub, Matrix.trace_sub]
  exact (norm_sub_le _ _).trans (add_le_add hA hB)

/-- The blocks are continuous in the coordinates. -/
private lemma CoercivityMean_continuous_block (W m : ℕ) (j : Fin m) :
    Continuous fun ω : Ω W m => gueBlock W m ω j :=
  continuous_matrix fun α β => by
    simp only [gueBlock, Matrix.of_apply]
    split_ifs <;> fun_prop

/-- `N(G)` of the block family is measurable (a supremum of continuous functions, bounded
above). -/
private lemma CoercivityMean_measurable_numRad (W m : ℕ) (hW : 0 < W) :
    Measurable fun ω : Ω W m => numRad (gueBlock W m ω) := by
  have hsum : ∀ ω : Ω W m, ∑ j, hsSq (gueBlock W m ω j) =
      (∑ x : Fin m × Fin W × Fin W, ω x ^ 2) / W := CoercivityMean_sum_hsSq W m
  refine LowerSemicontinuous.measurable ?_
  refine lowerSemicontinuous_ciSup (f := fun (P : {P : Matrix (Fin W) (Fin W) ℂ // hsSq P = 1})
    (ω : Ω W m) => |(P.1ᴴ * (phiMap (gueBlock W m ω) P.1 -
      ((m : ℂ) / W * star P.1.trace) • (1 : Matrix (Fin W) (Fin W) ℂ))).trace.re|) ?_ ?_
  · intro ω
    refine ⟨∑ j, hsSq (gueBlock W m ω j) + m, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact CoercivityMean_term_le hW _ P.2
  · intro P
    refine Continuous.lowerSemicontinuous ?_
    have hΦ : Continuous fun ω : Ω W m => phiMap (gueBlock W m ω) P.1 :=
      continuous_finsetSum _ fun j _ =>
        (((CoercivityMean_continuous_block W m j).matrix_mul continuous_const).matrix_mul
          (CoercivityMean_continuous_block W m j))
    exact (Complex.continuous_re.comp
      ((continuous_const.matrix_mul (hΦ.sub continuous_const)).matrix_trace)).abs

/-- `N(G)` of the block family is integrable. -/
private lemma CoercivityMean_integrable_numRad (W m : ℕ) (hW : 0 < W) :
    Integrable (fun ω : Ω W m => numRad (gueBlock W m ω)) (μ W m) := by
  refine ((CoercivityMean_integrable_quad W m).add (integrable_const (m : ℝ))).mono'
    (CoercivityMean_measurable_numRad W m hW).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have h0 : 0 ≤ numRad (gueBlock W m ω) := Real.iSup_nonneg fun _ => abs_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  have hB : 0 ≤ (∑ x : Fin m × Fin W × Fin W, ω x ^ 2) / W + m := by positivity
  refine Real.iSup_le (fun P => ?_) hB
  have := CoercivityMean_term_le hW (gueBlock W m ω) P.2
  rw [CoercivityMean_sum_hsSq] at this
  exact this

end CoercivityMeanAux

/-- (G.16) [cg:eq:positive] in non-asymptotic form: `𝔼 S_W(G)² ≥ 40` for large `W`. -/
theorem coerMin_sq_mean_ge :
    ∃ W₀ : ℕ, ∀ W, W₀ ≤ W → 40 ≤ ∫ ω, coerMin (gueBlock W 128 ω) ^ 2 ∂(μ W 128) := by
  obtain ⟨W₁, h₁⟩ := quadMin_mean_ge
  obtain ⟨W₂, h₂⟩ := tensor_norm_mean_le
  refine ⟨max (max W₁ W₂) 1, fun W hW => ?_⟩
  have hW1 : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW2 : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW0 : 0 < W := (le_max_right _ _).trans hW
  have hq := h₁ W hW1
  have hF := h₂ W hW2
  have hN := integral_numRad_le W 128
  have hqi : Integrable (fun ω => quadMin (gueBlock W 128 ω)) (μ W 128) :=
    Integrable.of_integral_ne_zero (by intro h; rw [h] at hq; norm_num at hq)
  have hNi := CoercivityMean_integrable_numRad W 128 hW0
  have hSi := CoercivityMean_integrable_sq W 128
  have hmono : ∫ ω, (2 * quadMin (gueBlock W 128 ω) - 2 * numRad (gueBlock W 128 ω)) ∂(μ W 128) ≤
      ∫ ω, coerMin (gueBlock W 128 ω) ^ 2 ∂(μ W 128) :=
    integral_mono ((hqi.const_mul 2).sub (hNi.const_mul 2)) hSi fun ω =>
      coerMin_sq_ge _ (gueBlock_isHermitian W 128 ω)
  rw [integral_sub (hqi.const_mul 2) (hNi.const_mul 2), integral_const_mul,
    integral_const_mul] at hmono
  linarith

/-- `𝔼 S_W(G) ≥ 5` for large `W` (proof of (G.11) [cg:eq:SG]). -/
theorem coerMin_mean_ge :
    ∃ W₀ : ℕ, ∀ W, W₀ ≤ W → 5 ≤ ∫ ω, coerMin (gueBlock W 128 ω) ∂(μ W 128) := by
  obtain ⟨W₀, h⟩ := coerMin_sq_mean_ge
  refine ⟨max W₀ 3, fun W hW => ?_⟩
  have hW0 : W₀ ≤ W := (le_max_left _ _).trans hW
  have hW3 : (3 : ℝ) ≤ W := by exact_mod_cast (le_max_right _ _).trans hW
  have hWpos : (0 : ℝ) < W := by linarith
  have hS := h W hW0
  set f : Ω W 128 → ℝ := fun ω => coerMin (gueBlock W 128 ω) with hf
  set m : ℝ := ∫ ω, f ω ∂(μ W 128) with hm
  have hvar : ∫ ω, (f ω - m) ^ 2 ∂(μ W 128) ≤
      π ^ 2 * ((Real.toNNReal (2 / Real.sqrt W) : ℝ≥0) : ℝ) ^ 2 :=
    variance_le_of_lipschitz f _ (CoercivityMean_lipschitz W 128)
  have hfi : Integrable f (μ W 128) := CoercivityMean_integrable W 128
  have hfi2 : Integrable (fun ω => f ω ^ 2) (μ W 128) := CoercivityMean_integrable_sq W 128
  have hexp : ∫ ω, (f ω - m) ^ 2 ∂(μ W 128) = (∫ ω, f ω ^ 2 ∂(μ W 128)) - m ^ 2 := by
    have e : ∀ ω, (f ω - m) ^ 2 = f ω ^ 2 - 2 * m * f ω + m ^ 2 := fun ω => by ring
    have i1 : Integrable (fun ω => f ω ^ 2 - 2 * m * f ω) (μ W 128) :=
      hfi2.sub (hfi.const_mul (2 * m))
    simp_rw [e]
    rw [integral_add i1 (integrable_const _), integral_sub hfi2 (hfi.const_mul _),
      integral_const_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [← hm]
    ring
  have hK : ((Real.toNNReal (2 / Real.sqrt W) : ℝ≥0) : ℝ) ^ 2 = 4 / W := by
    rw [Real.coe_toNNReal _ (by positivity), div_pow, Real.sq_sqrt hWpos.le]
    norm_num
  rw [hK] at hvar
  have hpi : π ^ 2 ≤ 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have h43 : 4 / (W : ℝ) ≤ 4 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hW3
  have hπK : π ^ 2 * (4 / (W : ℝ)) ≤ 15 := by
    calc π ^ 2 * (4 / (W : ℝ)) ≤ 10 * (4 / 3) := by gcongr
      _ ≤ 15 := by norm_num
  have hm0 : 0 ≤ m := integral_nonneg fun ω => (coerMin_le _).1
  have hm2 : 25 ≤ m ^ 2 := by linarith
  nlinarith

end LSBA
