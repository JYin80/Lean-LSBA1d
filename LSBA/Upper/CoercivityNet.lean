import LSBA.Upper.CoercivityMap
import LSBA.Gauss.SphereNet
import LSBA.Gauss.GUEQuadSum

/-!
# Spectral bounds for `Σ_j G_j²` at `m = 128`

For `128` independent GUE blocks with the covariance (1.2) [eq:covariance], the non-asymptotic
replacement of the lower half of (G.15) [cg:eq:freebounds]: with probability `1 - e^{-cW}`,
`λ_min(Σ_j G_j²) ≥ 79` and `‖Σ_j G_j²‖ ≤ 192` (a `1/64`-net of the sphere and the two Chernoff
bounds at `ε = 0.35`, `0.45`), and hence `𝔼 λ_min(Σ_j G_j²) ≥ 78` for large `W`
(Appendix G.4 [app:compact-gaussian]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The stacked matrix `A_{(j,a),b} = (G_j)_{ab}` of a family of `m` blocks of size `W`. -/
private def CoercivityNet_stack {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin m × Fin W) (Fin W) ℂ :=
  Matrix.of fun p b => G p.1 p.2 b

/-- `‖A y‖² = Σ_j ‖G_j y‖²` for the stacked matrix `A`. -/
private lemma CoercivityNet_stack_sum {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (y : Fin W → ℂ) :
    ∑ p, ‖(CoercivityNet_stack G *ᵥ y) p‖ ^ 2 = ∑ j, ∑ a, ‖(G j *ᵥ y) a‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  rfl

/-- `A* A = Σ_j G_j²` for the stacked matrix `A` of Hermitian blocks. -/
private lemma CoercivityNet_stack_conjTranspose_mul {m W : ℕ}
    (G : Fin m → Matrix (Fin W) (Fin W) ℂ) (hG : ∀ j, (G j).IsHermitian) :
    (CoercivityNet_stack G)ᴴ * CoercivityNet_stack G = ∑ j, G j * G j := by
  ext b c
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, CoercivityNet_stack, Matrix.of_apply,
    Matrix.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  have h := congrFun (congrFun (hG j) b) a
  rw [Matrix.conjTranspose_apply] at h
  rw [h]

/-- The `L²` operator norm of `A` is at most `C ≥ 0` if `‖A y‖ ≤ C` for every unit vector `y`. -/
private lemma CoercivityNet_opNorm_le {k n : Type*} [Fintype k] [Fintype n]
    (A : Matrix k n ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ y : n → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 → Real.sqrt (∑ p, ‖(A *ᵥ y) p‖ ^ 2) ≤ C) :
    ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hC fun x hx => ?_
  have hx' : ∑ i, ‖x.ofLp i‖ ^ 2 = 1 := by
    have h2 := congrArg (fun r => r ^ 2) hx
    simp only [one_pow] at h2
    rwa [EuclideanSpace.norm_sq_eq] at h2
  refine le_of_eq_of_le ?_ (h x.ofLp hx')
  rw [EuclideanSpace.norm_eq]
  rfl

/-- The unit vector `e₀` of `ℂ^W` for `W ≥ 1`. -/
private lemma CoercivityNet_e0_unit {W : ℕ} (hW : 1 ≤ W) :
    ∑ a, ‖(Pi.single (⟨0, hW⟩ : Fin W) (1 : ℂ) : Fin W → ℂ) a‖ ^ 2 = 1 := by
  rw [Finset.sum_eq_single (⟨0, hW⟩ : Fin W) (fun b _ hb => by simp [hb])
    (by simp)]
  simp

/-- The deterministic step of (N1⁺): if a `1/64`-net `N` of the unit sphere of `ℂ^W` has
`9.12² ≤ Σ_j ‖G_j v‖² ≤ 13.63²` at every `v ∈ N`, then `λ_min(Σ_j G_j²) ≥ 79` and
`‖Σ_j G_j²‖ ≤ 192` (Appendix G.4 [app:compact-gaussian]). -/
private lemma CoercivityNet_det {m W : ℕ} (hW : 1 ≤ W) (G : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (hG : ∀ j, (G j).IsHermitian) {N : Finset (Fin W → ℂ)}
    (hN : ∀ y : Fin W → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 → ∃ v ∈ N, ∑ i, ‖y i - v i‖ ^ 2 ≤ (1 / 64) ^ 2)
    (hv : ∀ v ∈ N, (9.12 : ℝ) ^ 2 ≤ ∑ j, ∑ a, ‖(G j *ᵥ v) a‖ ^ 2 ∧
      ∑ j, ∑ a, ‖(G j *ᵥ v) a‖ ^ 2 ≤ (13.63 : ℝ) ^ 2) :
    79 ≤ quadMin G ∧ ‖∑ j, G j * G j‖ ≤ 192 := by
  set A := CoercivityNet_stack G
  have hα : ∀ v ∈ N, (9.12 : ℝ) ≤ Real.sqrt (∑ p, ‖(A *ᵥ v) p‖ ^ 2) := fun v hv' => by
    rw [CoercivityNet_stack_sum, Real.le_sqrt (by norm_num) (by positivity)]
    exact (hv v hv').1
  have hβ : ∀ v ∈ N, Real.sqrt (∑ p, ‖(A *ᵥ v) p‖ ^ 2) ≤ 13.63 := fun v hv' => by
    rw [CoercivityNet_stack_sum, Real.sqrt_le_left (by norm_num)]
    exact (hv v hv').2
  have hne : Nonempty {y : Fin W → ℂ // ∑ a, ‖y a‖ ^ 2 = 1} :=
    ⟨⟨Pi.single ⟨0, hW⟩ 1, CoercivityNet_e0_unit hW⟩⟩
  refine ⟨le_ciInf fun y => ?_, ?_⟩
  · have hl := sphere_net_lower A (by norm_num) (by norm_num) hN hα hβ y.1 y.2
    rw [CoercivityNet_stack_sum] at hl
    have h0 : (0 : ℝ) ≤ 9.12 - 1 / 64 * 13.63 / (1 - 1 / 64) := by norm_num
    have h2 := pow_le_pow_left₀ h0 hl 2
    rw [Real.sq_sqrt (by positivity)] at h2
    refine le_trans ?_ h2
    norm_num
  · have hA : ‖A‖ ≤ 13.63 / (1 - 1 / 64) :=
      CoercivityNet_opNorm_le A (by norm_num) fun y hy =>
        sphere_net_upper A (by norm_num) (by norm_num) hN hβ y hy
    rw [← CoercivityNet_stack_conjTranspose_mul G hG]
    erw [Matrix.l2_opNorm_conjTranspose_mul_self]
    calc ‖A‖ * ‖A‖ ≤ (13.63 / (1 - 1 / 64)) * (13.63 / (1 - 1 / 64)) :=
          mul_le_mul hA hA (norm_nonneg _) (by norm_num)
      _ ≤ 192 := by norm_num

/-- `log 129 ≤ 4.86`. -/
private lemma CoercivityNet_log129 : Real.log 129 ≤ 4.86 := by
  have h1 : Real.log 129 = 7 * Real.log 2 + Real.log (129 / 128) := by
    rw [show (129 : ℝ) = 2 ^ 7 * (129 / 128) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 129 / 128 by norm_num)
  have h3 := Real.log_two_lt_d9
  rw [h1]
  norm_num at h2 h3 ⊢
  linarith

/-- `log (1 - 7/20) ≤ -0.43`. -/
private lemma CoercivityNet_log_lo : Real.log (1 - 7 / 20) ≤ -0.43 := by
  have h := (abs_le.1 (Real.abs_log_sub_add_sum_range_le (x := 7 / 20)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 10)).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 7 / 20)] at h
  norm_num at h ⊢
  linarith

/-- `log (1 + 9/20) ≤ 0.372`. -/
private lemma CoercivityNet_log_up : Real.log (1 + 9 / 20) ≤ 0.372 := by
  have h := (abs_le.1 (Real.abs_log_sub_add_sum_range_le (x := 9 / 29)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 8)).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 9 / 29)] at h
  have he : Real.log (1 + 9 / 20) = -Real.log (1 - 9 / 29) := by
    rw [← Real.log_inv]
    norm_num
  rw [he]
  norm_num at h ⊢
  linarith

/-- `log ((1 - 9/20)/(1 + 9/20)) ≥ -2`. -/
private lemma CoercivityNet_log_ratio : -2 ≤ Real.log ((1 - 9 / 20) / (1 + 9 / 20)) := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < (1 - 9 / 20) / (1 + 9 / 20) by
    norm_num)
  norm_num at h ⊢
  linarith

/-- The union bound of (N1⁺) closes: if `K ≤ 129^{2w}` and `w ≥ 1000`, then `K` times the sum
of the two Chernoff bounds at `m = 128`, `ε = 7/20`, `9/20` is at most `e^{-w/100}`. -/
private lemma CoercivityNet_numeric {w K : ℝ} (hw : 1000 ≤ w)
    (hK : K ≤ Real.exp (2 * w * Real.log 129)) :
    K * (Real.exp (-(128 * (w - 1)) * (-(7 / 20) - Real.log (1 - 7 / 20)) + 128 * (7 / 20)) +
      Real.exp (-(128 * (w - 1)) * (9 / 20 - Real.log (1 + 9 / 20)) - 128 * (9 / 20) -
        128 / 2 * Real.log ((1 - 9 / 20) / (1 + 9 / 20)))) ≤
      Real.exp (-(1 / 100) * w) := by
  have l1 := CoercivityNet_log129
  have l2 := CoercivityNet_log_lo
  have l3 := CoercivityNet_log_up
  have l4 := CoercivityNet_log_ratio
  have hw1 : 0 ≤ w - 1 := by linarith
  have ea : 2 * w * Real.log 129 +
      (-(128 * (w - 1)) * (-(7 / 20) - Real.log (1 - 7 / 20)) + 128 * (7 / 20)) ≤
      -(1 / 100) * w - 1 := by
    nlinarith [mul_nonneg hw1 (show (0 : ℝ) ≤ -(7 / 20) - Real.log (1 - 7 / 20) - 0.08 by
      linarith)]
  have eb : 2 * w * Real.log 129 +
      (-(128 * (w - 1)) * (9 / 20 - Real.log (1 + 9 / 20)) - 128 * (9 / 20) -
        128 / 2 * Real.log ((1 - 9 / 20) / (1 + 9 / 20))) ≤ -(1 / 100) * w - 1 := by
    nlinarith [mul_nonneg hw1 (show (0 : ℝ) ≤ 9 / 20 - Real.log (1 + 9 / 20) - 0.078 by
      linarith)]
  have he : 2 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hs : Real.exp (-(1 / 100) * w - 1) = Real.exp (-(1 / 100) * w) / Real.exp 1 :=
    Real.exp_sub _ _
  calc _ ≤ Real.exp (2 * w * Real.log 129) * (Real.exp (-(128 * (w - 1)) *
        (-(7 / 20) - Real.log (1 - 7 / 20)) + 128 * (7 / 20)) +
      Real.exp (-(128 * (w - 1)) * (9 / 20 - Real.log (1 + 9 / 20)) - 128 * (9 / 20) -
        128 / 2 * Real.log ((1 - 9 / 20) / (1 + 9 / 20)))) :=
        mul_le_mul_of_nonneg_right hK (by positivity)
    _ = Real.exp (2 * w * Real.log 129 + (-(128 * (w - 1)) *
        (-(7 / 20) - Real.log (1 - 7 / 20)) + 128 * (7 / 20))) +
      Real.exp (2 * w * Real.log 129 + (-(128 * (w - 1)) * (9 / 20 - Real.log (1 + 9 / 20)) -
        128 * (9 / 20) - 128 / 2 * Real.log ((1 - 9 / 20) / (1 + 9 / 20)))) := by
        rw [mul_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (-(1 / 100) * w - 1) + Real.exp (-(1 / 100) * w - 1) :=
        add_le_add (Real.exp_le_exp.2 ea) (Real.exp_le_exp.2 eb)
    _ ≤ Real.exp (-(1 / 100) * w) := by
        rw [hs, ← add_div, div_le_iff₀ (Real.exp_pos 1)]
        nlinarith [Real.exp_pos (-(1 / 100) * w)]

/-- `ω ↦ Σ_j ‖G_j y‖²` is continuous on `Ω W L`. -/
private lemma CoercivityNet_continuous_quad {W L : ℕ} (y : Fin W → ℂ) :
    Continuous fun ω : Ω W L => ∑ j, ∑ a, ‖(gueBlock W L ω j *ᵥ y) a‖ ^ 2 := by
  have he : ∀ (j : Fin L) (a b : Fin W), Continuous fun ω : Ω W L => gueBlock W L ω j a b := by
    intro j a b
    simp only [gueBlock, Matrix.of_apply]
    split_ifs <;> fun_prop
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

/-- Two-sided spectral bound for `Σ_{j<128} G_j²`, (1.2) [eq:covariance]: for large `W`,
`P(λ_min < 79 or ‖Σ_j G_j²‖ > 192) ≤ e^{-cW}`. -/
theorem quadMin_norm_good :
    ∃ c : ℝ, 0 < c ∧ ∃ W₁ : ℕ, ∀ W, W₁ ≤ W →
      μ W 128 {ω | quadMin (gueBlock W 128 ω) < 79 ∨
        192 < ‖∑ j, gueBlock W 128 ω j * gueBlock W 128 ω j‖} ≤
        ENNReal.ofReal (Real.exp (-c * W)) := by
  refine ⟨1 / 100, by norm_num, 1000, fun W hW => ?_⟩
  have hW1 : 1 ≤ W := by omega
  obtain ⟨N, hcard, hunit, hN⟩ := exists_sphere_net (Fin W) (δ := 1 / 64) (by norm_num)
  set Lo : (Fin W → ℂ) → Set (Ω W 128) := fun v =>
    {ω | ∑ j, ∑ a, ‖(gueBlock W 128 ω j *ᵥ v) a‖ ^ 2 ≤ (1 - 7 / 20) * ((128 : ℕ) : ℝ)}
  set Up : (Fin W → ℂ) → Set (Ω W 128) := fun v =>
    {ω | (1 + 9 / 20) * ((128 : ℕ) : ℝ) ≤ ∑ j, ∑ a, ‖(gueBlock W 128 ω j *ᵥ v) a‖ ^ 2}
  have hsub : {ω | quadMin (gueBlock W 128 ω) < 79 ∨
      192 < ‖∑ j, gueBlock W 128 ω j * gueBlock W 128 ω j‖} ⊆ ⋃ v ∈ N, (Lo v ∪ Up v) := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_union, not_exists, not_or] at hcon
    have hdet := CoercivityNet_det hW1 (gueBlock W 128 ω) (gueBlock_isHermitian W 128 ω) hN
      fun v hv => by
        have h := hcon v hv
        simp only [Lo, Up, Set.mem_ofPred_eq, not_le] at h
        norm_num at h ⊢
        exact ⟨by linarith, by linarith⟩
    simp only [Set.mem_ofPred_eq] at hω
    rcases hω with h | h <;> linarith [hdet.1, hdet.2]
  have hcard' : (N.card : ℝ) ≤ Real.exp (2 * (W : ℝ) * Real.log 129) := by
    refine hcard.trans (le_of_eq ?_)
    rw [Fintype.card_fin, show (1 : ℝ) + 2 / (1 / 64) = Real.exp (Real.log 129) by
      rw [Real.exp_log (by norm_num)]; norm_num, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  calc μ W 128 _ ≤ μ W 128 (⋃ v ∈ N, (Lo v ∪ Up v)) := measure_mono hsub
    _ ≤ ∑ v ∈ N, μ W 128 (Lo v ∪ Up v) := measure_biUnion_finset_le _ _
    _ ≤ ∑ v ∈ N, (ENNReal.ofReal (Real.exp (-((128 : ℕ) * ((W : ℝ) - 1)) *
          (-(7 / 20) - Real.log (1 - 7 / 20)) + (128 : ℕ) * (7 / 20))) +
        ENNReal.ofReal (Real.exp (-((128 : ℕ) * ((W : ℝ) - 1)) * (9 / 20 - Real.log (1 + 9 / 20)) -
          (128 : ℕ) * (9 / 20) - ((128 : ℕ) : ℝ) / 2 *
            Real.log ((1 - 9 / 20) / (1 + 9 / 20))))) :=
        Finset.sum_le_sum fun v hv => (measure_union_le _ _).trans (add_le_add
          (gueBlock_quadSum_lower_tail hW1 128 (hunit v hv) (by norm_num) (by norm_num))
          (gueBlock_quadSum_upper_tail hW1 128 (hunit v hv) (by norm_num) (by norm_num)))
    _ = ENNReal.ofReal (N.card * (Real.exp (-((128 : ℕ) * ((W : ℝ) - 1)) *
          (-(7 / 20) - Real.log (1 - 7 / 20)) + (128 : ℕ) * (7 / 20)) +
        Real.exp (-((128 : ℕ) * ((W : ℝ) - 1)) * (9 / 20 - Real.log (1 + 9 / 20)) -
          (128 : ℕ) * (9 / 20) - ((128 : ℕ) : ℝ) / 2 *
            Real.log ((1 - 9 / 20) / (1 + 9 / 20))))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (Real.exp (-(1 / 100) * W)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hw : (1000 : ℝ) ≤ W := by exact_mod_cast hW
        have := CoercivityNet_numeric hw hcard'
        push_cast
        exact this

/-- `𝔼 λ_min(Σ_{j<128} G_j²) ≥ 78` for large `W`, (1.2) [eq:covariance]. -/
theorem quadMin_mean_ge :
    ∃ W₁ : ℕ, ∀ W, W₁ ≤ W → 78 ≤ ∫ ω, quadMin (gueBlock W 128 ω) ∂(μ W 128) := by
  obtain ⟨c, hc, W₁, hW₁⟩ := quadMin_norm_good
  refine ⟨max (max W₁ 3) ⌈79 / c⌉₊, fun W hW => ?_⟩
  have hW3 : 3 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWW₁ : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWc : 79 / c ≤ (W : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hW)
  have hW1 : 1 ≤ W := by omega
  set f : Ω W 128 → ℝ := fun ω => quadMin (gueBlock W 128 ω) with hf_def
  set Q : (Fin W → ℂ) → Ω W 128 → ℝ := fun y ω =>
    ∑ j, ∑ a, ‖(gueBlock W 128 ω j *ᵥ y) a‖ ^ 2 with hQ_def
  have hbdd : ∀ ω, BddBelow (Set.range fun y : {y : Fin W → ℂ // ∑ a, ‖y a‖ ^ 2 = 1} =>
      Q y.1 ω) := fun ω => ⟨0, by rintro _ ⟨y, rfl⟩; positivity⟩
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => Real.iInf_nonneg fun y => by positivity
  have hfm : Measurable f :=
    (upperSemicontinuous_ciInf hbdd fun y =>
      (CoercivityNet_continuous_quad (L := 128) y.1).upperSemicontinuous).measurable
  set y0 : Fin W → ℂ := Pi.single (⟨0, hW1⟩ : Fin W) 1
  have hy0 : ∑ a, ‖y0 a‖ ^ 2 = 1 := CoercivityNet_e0_unit hW1
  have hfle : ∀ ω, f ω ≤ Q y0 ω := fun ω => ciInf_le (hbdd ω) ⟨y0, hy0⟩
  have hWr : (3 : ℝ) ≤ W := by exact_mod_cast hW3
  have hint : Integrable (fun ω => Real.exp (1 * Q y0 ω)) (μ W 128) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [integral_exp_quadSum_gueBlock hW1 128 hy0 (by linarith)]
    have h1 : (0 : ℝ) < 1 - 2 * 1 / W := by
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    have h2 : (0 : ℝ) < 1 - 1 / W := by
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    exact (mul_pos (Real.rpow_pos_of_pos h1 _) (Real.rpow_pos_of_pos h2 _)).ne'
  have hfint : Integrable f (μ W 128) := by
    refine hint.mono' hfm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]
    exact (hfle ω).trans (by linarith [Real.add_one_le_exp (1 * Q y0 ω)])
  set F : Set (Ω W 128) := {ω | f ω < 79} with hF_def
  have hFm : MeasurableSet F := measurableSet_lt hfm measurable_const
  have hFle : (μ W 128).real F ≤ Real.exp (-c * W) := by
    refine ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le ?_
    refine le_trans (measure_mono fun ω hω => ?_) (hW₁ W hWW₁)
    exact Or.inl hω
  have hexp : Real.exp (-c * W) ≤ 1 / 80 := by
    have h1 : 80 ≤ Real.exp (c * W) := by
      have := Real.add_one_le_exp (c * W)
      have h2 : 79 ≤ c * W := by rwa [div_le_iff₀ hc, mul_comm] at hWc
      linarith
    rw [neg_mul, Real.exp_neg]
    exact inv_anti₀ (by norm_num) h1 |>.trans_eq (by norm_num)
  have hind : ∀ ω, Fᶜ.indicator (fun _ => (79 : ℝ)) ω ≤ f ω := by
    intro ω
    by_cases h : ω ∈ Fᶜ
    · rw [Set.indicator_of_mem h]
      simpa [hF_def] using h
    · rw [Set.indicator_of_notMem h]
      exact hf0 ω
  have hmono := integral_mono ((integrable_const (79 : ℝ)).indicator hFm.compl) hfint hind
  rw [integral_indicator_const _ hFm.compl, measureReal_compl hFm, probReal_univ,
    smul_eq_mul] at hmono
  refine le_trans ?_ hmono
  nlinarith

end LSBA
