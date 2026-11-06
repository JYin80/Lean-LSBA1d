import LSBA.Upper.CoercivityNet
import LSBA.Gauss.TensorMoment
import LSBA.Gauss.GUENormSharp

/-!
# The tensor bound at `m = 128`

For independent families `B`, `C` of `128` GUE blocks with the covariance (1.2)
[eq:covariance], the non-asymptotic replacement of the upper half of (G.15)
[cg:eq:freebounds]: `𝔼 ‖Σ_j B_j ⊗ C_jᵗ‖ ≤ 28.5` for large `W` (conditional trace moments of
order `2p ≍ 2√W`, the sharp GUE norm moments and `‖Σ_j C_j²‖ ≤ 192` with probability
`1 - e^{-cW}`; Appendix G.4 [app:compact-gaussian]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Matrix norm estimates -/

/-- An entry of a matrix is bounded by its operator norm. -/
private lemma CoercivityTensor_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
  have hn : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [hn, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  convert this using 2
  simp

/-- `‖Tr M‖ ≤ n ‖M‖` for a matrix of size `n`. -/
private lemma CoercivityTensor_norm_trace_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) : ‖M.trace‖ ≤ Fintype.card n * ‖M‖ := by
  rw [Matrix.trace]
  calc ‖∑ i, M.diag i‖ ≤ ∑ i, ‖M.diag i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : n, ‖M‖ := Finset.sum_le_sum fun i _ => CoercivityTensor_norm_entry_le M i i
    _ = _ := by simp

/-- The operator norm is at most the Frobenius norm. -/
private lemma CoercivityTensor_opNorm_le_frob {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  have hS : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have hx : ‖x‖ = Real.sqrt (∑ j, ‖x.ofLp j‖ ^ 2) := EuclideanSpace.norm_eq x
  rw [EuclideanSpace.norm_eq, hx, ← Real.sqrt_mul hS]
  change √(∑ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2) ≤ _
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ‖(A *ᵥ x.ofLp) i‖ ^ 2 = ‖∑ j, A i j * x.ofLp j‖ ^ 2 := by
        simp [Matrix.mulVec, dotProduct]
    _ ≤ (∑ j, ‖A i j * x.ofLp j‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
    _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 := by
        simp_rw [norm_mul]
        exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- If every entry satisfies `‖M i j‖ ≤ b`, then `‖M‖ ≤ n b`. -/
private lemma CoercivityTensor_opNorm_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) {b : ℝ} (hb : 0 ≤ b) (h : ∀ i j, ‖M i j‖ ≤ b) :
    ‖M‖ ≤ Fintype.card n * b := by
  refine (CoercivityTensor_opNorm_le_frob M).trans (Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩)
  calc ∑ i, ∑ j, ‖M i j‖ ^ 2 ≤ ∑ _i : n, ∑ _j : n, b ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (Fintype.card n * b) ^ 2 := by simp [Finset.sum_const]; ring

/-- `‖Aᵀ‖ ≤ ‖A‖` for the operator norm. -/
private lemma CoercivityTensor_norm_transpose_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ‖Aᵀ‖ ≤ ‖A‖ := by
  have hT : Aᵀ = (A.map star)ᴴ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [hT, Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  set y : EuclideanSpace ℂ n := (EuclideanSpace.equiv n ℂ).symm (star x.ofLp) with hy
  have hyx : ‖y‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [hy]
  have hA := Matrix.l2_opNorm_mulVec A y
  rw [hyx] at hA
  refine le_trans (le_of_eq ?_) hA
  change ‖(EuclideanSpace.equiv n ℂ).symm (A.map star *ᵥ x.ofLp)‖ = _
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (A.map star *ᵥ x.ofLp) i = star ((A *ᵥ y.ofLp) i) := by
    simp [Matrix.mulVec, dotProduct, hy, star_sum]
  change ‖(A.map star *ᵥ x.ofLp) i‖ ^ 2 = ‖(A *ᵥ y.ofLp) i‖ ^ 2
  rw [this, norm_star]

/-! ### GUE blocks as functions of the coordinates -/

/-- An entry of a GUE block is at most `2 ‖ω‖` (sup norm of the coordinates). -/
private lemma CoercivityTensor_gueBlock_entry_le {W L : ℕ} (ω : Ω W L) (a : Fin L)
    (α β : Fin W) : ‖gueBlock W L ω a α β‖ ≤ 2 * ‖ω‖ := by
  have hW : (1 : ℝ) ≤ W := by exact_mod_cast Fin.pos α
  have h1 : 1 ≤ Real.sqrt W := Real.one_le_sqrt.2 hW
  have h2 : 1 ≤ Real.sqrt (2 * W) := Real.one_le_sqrt.2 (by linarith)
  have hc : ∀ c, |ω c| ≤ ‖ω‖ := fun c => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm ω c
  have hdiv : ∀ (z : ℂ) (r : ℝ), 1 ≤ r → ‖z / (r : ℂ)‖ ≤ ‖z‖ := fun z r hr => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact div_le_self (norm_nonneg _) hr
  have hn : 0 ≤ ‖ω‖ := norm_nonneg ω
  simp only [gueBlock, Matrix.of_apply]
  split_ifs
  · refine (hdiv _ _ h1).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [hc (a, α, α)]
  · refine (hdiv _ _ h2).trans ?_
    calc ‖(ω (a, α, β) : ℂ) + Complex.I * ω (a, β, α)‖
        ≤ ‖(ω (a, α, β) : ℂ)‖ + ‖Complex.I * ω (a, β, α)‖ := norm_add_le _ _
      _ = |ω (a, α, β)| + |ω (a, β, α)| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 2 * ‖ω‖ := by linarith [hc (a, α, β), hc (a, β, α)]
  · refine (hdiv _ _ h2).trans ?_
    calc ‖(ω (a, β, α) : ℂ) - Complex.I * ω (a, α, β)‖
        ≤ ‖(ω (a, β, α) : ℂ)‖ + ‖Complex.I * ω (a, α, β)‖ := norm_sub_le _ _
      _ = |ω (a, β, α)| + |ω (a, α, β)| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 2 * ‖ω‖ := by linarith [hc (a, α, β), hc (a, β, α)]

/-- `‖G_a‖ ≤ 2 W ‖ω‖`. -/
private lemma CoercivityTensor_norm_gueBlock_le {W L : ℕ} (ω : Ω W L) (a : Fin L) :
    ‖gueBlock W L ω a‖ ≤ W * (2 * ‖ω‖) := by
  have := CoercivityTensor_opNorm_le (gueBlock W L ω a) (by positivity)
    (CoercivityTensor_gueBlock_entry_le ω a)
  simpa using this

/-- Each entry of a GUE block is continuous in the coordinates. -/
private lemma CoercivityTensor_continuous_entry (W L : ℕ) (a : Fin L) (α β : Fin W) :
    Continuous fun ω : Ω W L => gueBlock W L ω a α β := by
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The coordinates have all moments. -/
private lemma CoercivityTensor_memLp (W L n : ℕ) :
    MemLp (fun ω : Ω W L => ω) n (μ W L) := by
  refine memLp_pi_iff.2 fun i => ?_
  exact (memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) n
    (ENNReal.natCast_ne_top n)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin L × Fin W × Fin W => gaussianReal (0 : ℝ) 1) i)

/-- `𝔼 ‖ω‖² ≤ L W² · 𝔼 x²` for a standard Gaussian `x`. -/
private lemma CoercivityTensor_integral_norm_sq_le (W L : ℕ) :
    ∫ ω, ‖ω‖ ^ 2 ∂(μ W L) ≤ (L * W * W : ℝ) * ∫ x, x ^ 2 ∂(gaussianReal 0 1) := by
  have hle : ∀ ω : Ω W L, ‖ω‖ ^ 2 ≤ ∑ i, ω i ^ 2 := by
    intro ω
    have hS : 0 ≤ ∑ i, ω i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have : ‖ω‖ ≤ Real.sqrt (∑ i, ω i ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun i => ω i ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
    calc ‖ω‖ ^ 2 ≤ Real.sqrt (∑ i, ω i ^ 2) ^ 2 := by gcongr
      _ = _ := Real.sq_sqrt hS
  have hint : ∀ i : Fin L × Fin W × Fin W, Integrable (fun ω : Ω W L => ω i ^ 2) (μ W L) :=
    fun i => (memLp_pi_iff.1 (CoercivityTensor_memLp W L 2) i).integrable_sq
  calc ∫ ω, ‖ω‖ ^ 2 ∂(μ W L) ≤ ∫ ω, ∑ i, ω i ^ 2 ∂(μ W L) :=
        integral_mono (CoercivityTensor_memLp W L 2).integrable_norm_pow'
          (integrable_finsetSum _ fun i _ => hint i) hle
    _ = ∑ _i : Fin L × Fin W × Fin W, ∫ x, x ^ 2 ∂(gaussianReal 0 1) := by
        rw [integral_finsetSum _ fun i _ => hint i]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact integral_comp_eval (μ := fun _ : Fin L × Fin W × Fin W => gaussianReal (0 : ℝ) 1)
          (f := fun x : ℝ => x ^ 2) (by fun_prop)
    _ = _ := by simp [Finset.card_univ, mul_assoc]

/-! ### The conditional bound for fixed `D` -/

/-- The tensor sum `Σ_j G_j ⊗ D_j` is continuous in the coordinates. -/
private lemma CoercivityTensor_continuous_sum {W W' m : ℕ}
    (D : Fin m → Matrix (Fin W') (Fin W') ℂ) :
    Continuous fun ω : Ω W m => ∑ j, gueBlock W m ω j ⊗ₖ D j := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
  exact continuous_finsetSum _ fun j _ =>
    (CoercivityTensor_continuous_entry W m j _ _).mul continuous_const

/-- `‖Σ_j G_j ⊗ D_j‖ ≤ W W' · 2 ‖ω‖ Σ_j ‖D_j‖`. -/
private lemma CoercivityTensor_norm_sum_le {W W' m : ℕ}
    (D : Fin m → Matrix (Fin W') (Fin W') ℂ) (ω : Ω W m) :
    ‖∑ j, gueBlock W m ω j ⊗ₖ D j‖ ≤ ((W * W' : ℕ) : ℝ) * (2 * ‖ω‖ * ∑ j, ‖D j‖) := by
  have := CoercivityTensor_opNorm_le (∑ j, gueBlock W m ω j ⊗ₖ D j)
    (b := 2 * ‖ω‖ * ∑ j, ‖D j‖) (by positivity) ?_
  · simpa using this
  intro x y
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_mul]
  exact mul_le_mul (CoercivityTensor_gueBlock_entry_le ω j _ _)
    (CoercivityTensor_norm_entry_le _ _ _) (norm_nonneg _) (by positivity)

/-- The traces of the powers of the tensor sum are integrable. -/
private lemma CoercivityTensor_integrable_trace {W W' m : ℕ}
    (D : Fin m → Matrix (Fin W') (Fin W') ℂ) {n : ℕ} (hn : 0 < n) :
    Integrable (fun ω => ((∑ j, gueBlock W m ω j ⊗ₖ D j) ^ n).trace) (μ W m) := by
  set K : ℝ := ((W * W' : ℕ) : ℝ) * (2 * ∑ j, ‖D j‖) with hK
  have hK0 : 0 ≤ K := by positivity
  refine (((CoercivityTensor_memLp W m n).integrable_norm_pow').const_mul
    (((W * W' : ℕ) : ℝ) * K ^ n)).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (((CoercivityTensor_continuous_sum D).pow n).matrix_trace).aestronglyMeasurable
  · have hb : ‖∑ j, gueBlock W m ω j ⊗ₖ D j‖ ≤ K * ‖ω‖ := by
      refine (CoercivityTensor_norm_sum_le D ω).trans (le_of_eq ?_)
      rw [hK]; ring
    calc ‖((∑ j, gueBlock W m ω j ⊗ₖ D j) ^ n).trace‖
        ≤ Fintype.card (Fin W × Fin W') * ‖(∑ j, gueBlock W m ω j ⊗ₖ D j) ^ n‖ :=
          CoercivityTensor_norm_trace_le _
      _ ≤ ((W * W' : ℕ) : ℝ) * ‖∑ j, gueBlock W m ω j ⊗ₖ D j‖ ^ n := by
          rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
          push_cast
          gcongr
          exact norm_pow_le' _ hn
      _ ≤ ((W * W' : ℕ) : ℝ) * (K * ‖ω‖) ^ n := by gcongr
      _ = ((W * W' : ℕ) : ℝ) * K ^ n * ‖ω‖ ^ n := by ring

/-- `Re 𝔼 Tr G^{2p} ≤ W 𝔼 ‖G‖^{2p}` for one GUE block. -/
private lemma CoercivityTensor_re_trace_G_le (W p : ℕ) (hp : 1 ≤ p) :
    (∫ ω, ((gueBlock W 1 ω 0) ^ (2 * p)).trace ∂(μ W 1)).re ≤
      W * ∫ ω, ‖gueBlock W 1 ω 0‖ ^ (2 * p) ∂(μ W 1) := by
  have hpt : ∀ ω : Ω W 1, ‖((gueBlock W 1 ω 0) ^ (2 * p)).trace‖ ≤
      W * ‖gueBlock W 1 ω 0‖ ^ (2 * p) := by
    intro ω
    refine (CoercivityTensor_norm_trace_le _).trans ?_
    rw [Fintype.card_fin]
    gcongr
    exact norm_pow_le' _ (by omega)
  have hcont : Continuous fun ω : Ω W 1 => gueBlock W 1 ω 0 :=
    continuous_pi fun x => continuous_pi fun y => CoercivityTensor_continuous_entry W 1 0 x y
  have hInt : Integrable (fun ω => ((gueBlock W 1 ω 0) ^ (2 * p)).trace) (μ W 1) :=
    ((integrable_norm_gueBlock_pow W (2 * p)).const_mul (W : ℝ)).mono'
      ((hcont.pow (2 * p)).matrix_trace).aestronglyMeasurable
      (Filter.Eventually.of_forall hpt)
  have hre := integral_re hInt
  simp only [RCLike.re_to_complex] at hre
  rw [← hre, ← integral_const_mul]
  exact integral_mono hInt.re ((integrable_norm_gueBlock_pow W (2 * p)).const_mul _)
    fun ω => (Complex.re_le_norm _).trans (hpt ω)

/-- Conditional tensor bound: for Hermitian `D_j` of size `W'`,
`𝔼 ‖Σ_j G_j ⊗ D_j‖ ≤ (W' · W 𝔼‖G‖^{2p} · ‖Σ_j D_j²‖^p)^{1/(2p)}`. -/
private lemma CoercivityTensor_cond (W m p : ℕ) (hp : 1 ≤ p) {W' : ℕ}
    (D : Fin m → Matrix (Fin W') (Fin W') ℂ) (hD : ∀ a, (D a).IsHermitian) :
    ∫⁻ ω, ENNReal.ofReal ‖∑ j, gueBlock W m ω j ⊗ₖ D j‖ ∂(μ W m) ≤
      ENNReal.ofReal ((W' * (W * ∫ ω, ‖gueBlock W 1 ω 0‖ ^ (2 * p) ∂(μ W 1)) *
        ‖∑ j, D j * D j‖ ^ p) ^ ((2 * p : ℝ)⁻¹)) := by
  set f : Ω W m → Matrix (Fin W × Fin W') (Fin W × Fin W') ℂ :=
    fun ω => ∑ j, gueBlock W m ω j ⊗ₖ D j with hf
  have hfc : Continuous f := CoercivityTensor_continuous_sum D
  have hfH : ∀ ω, (f ω).IsHermitian := by
    intro ω
    change (∑ j, gueBlock W m ω j ⊗ₖ D j)ᴴ = _
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_kronecker, (gueBlock_isHermitian W m ω j).eq, (hD j).eq]
  set g : Ω W m → ℝ := fun ω => ‖f ω‖ with hg_def
  have hg : AEStronglyMeasurable g (μ W m) := (continuous_norm.comp hfc).aestronglyMeasurable
  set I : ℝ := ∫ ω, ‖gueBlock W 1 ω 0‖ ^ (2 * p) ∂(μ W 1) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => by positivity
  set s : ℝ := ‖∑ j, D j * D j‖ with hs
  have hInt := CoercivityTensor_integrable_trace (W := W) D (n := 2 * p) (by omega)
  have hnn : ∀ ω, 0 ≤ ((f ω ^ (2 * p)).trace).re := fun ω =>
    (by positivity : (0 : ℝ) ≤ ‖f ω‖ ^ (2 * p)).trans (norm_pow_le_trace_pow (hfH ω) hp)
  have hreal : ∫ ω, ((f ω ^ (2 * p)).trace).re ∂(μ W m) ≤ W' * (W * I) * s ^ p := by
    have hre := integral_re hInt
    simp only [RCLike.re_to_complex] at hre
    rw [hre]
    refine (trace_pow_kron_gueBlock_le W m p D hD).trans ?_
    have := CoercivityTensor_re_trace_G_le W p hp
    gcongr
  have hmain : ∫⁻ ω, ENNReal.ofReal (‖f ω‖ ^ (2 * p)) ∂(μ W m) ≤
      ENNReal.ofReal (W' * (W * I) * s ^ p) := by
    calc ∫⁻ ω, ENNReal.ofReal (‖f ω‖ ^ (2 * p)) ∂(μ W m)
        ≤ ∫⁻ ω, ENNReal.ofReal (((f ω ^ (2 * p)).trace).re) ∂(μ W m) :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (norm_pow_le_trace_pow (hfH ω) hp)
      _ = ENNReal.ofReal (∫ ω, ((f ω ^ (2 * p)).trace).re ∂(μ W m)) :=
          (ofReal_integral_eq_lintegral_ofReal hInt.re
            (Filter.Eventually.of_forall hnn)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  have h12 : (1 : ℝ≥0∞) ≤ ((2 * p : ℕ) : ℝ≥0∞) := by exact_mod_cast (by omega : 1 ≤ 2 * p)
  calc ∫⁻ ω, ENNReal.ofReal ‖f ω‖ ∂(μ W m) = eLpNorm g 1 (μ W m) := by
        rw [eLpNorm_one_eq_lintegral_enorm hg]
        refine lintegral_congr fun ω => ?_
        simp [g]
    _ ≤ eLpNorm g ((2 * p : ℕ) : ℝ≥0∞) (μ W m) := eLpNorm_le_eLpNorm_of_exponent_le h12
    _ = (∫⁻ ω, ENNReal.ofReal (‖f ω‖ ^ (2 * p)) ∂(μ W m)) ^ ((2 * p : ℝ)⁻¹) := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; omega) (ENNReal.natCast_ne_top _) hg]
        rw [ENNReal.toReal_natCast]
        congr 1
        · refine lintegral_congr fun ω => ?_
          rw [ENNReal.rpow_natCast, ← ofReal_norm, Real.norm_of_nonneg (norm_nonneg _),
            ENNReal.ofReal_pow (norm_nonneg _)]
        · push_cast; rw [one_div]
    _ ≤ (ENNReal.ofReal (W' * (W * I) * s ^ p)) ^ ((2 * p : ℝ)⁻¹) :=
        ENNReal.rpow_le_rpow hmain (by positivity)
    _ = _ := ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)

/-! ### The mean of `‖Σ_j C_j²‖^{1/2}` -/

/-- `‖Σ_j C_j²‖ ≤ m (2W)² ‖ω‖²`. -/
private lemma CoercivityTensor_norm_sq_sum_le {W m : ℕ} (ω : Ω W m) :
    ‖∑ j, gueBlock W m ω j * gueBlock W m ω j‖ ≤ m * (2 * W) ^ 2 * ‖ω‖ ^ 2 := by
  calc _ ≤ ∑ j, ‖gueBlock W m ω j * gueBlock W m ω j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, (W * (2 * ‖ω‖)) ^ 2 := Finset.sum_le_sum fun j _ => by
        refine (norm_mul_le _ _).trans ?_
        rw [sq]
        have := CoercivityTensor_norm_gueBlock_le ω j
        exact mul_le_mul this this (norm_nonneg _) (by positivity)
    _ = _ := by simp; ring

/-- Splitting on the event `‖Σ_j C_j²‖ > 192`: for every `t > 0`,
`𝔼 ‖Σ_j C_j²‖^{1/2} ≤ √192 + (t/2) P(‖Σ_j C_j²‖ > 192) + 𝔼 ‖Σ_j C_j²‖ / (2t)`. -/
private lemma CoercivityTensor_sqrt_mean (W m : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, ENNReal.ofReal (Real.sqrt ‖∑ j, gueBlock W m ω j * gueBlock W m ω j‖) ∂(μ W m) ≤
      ENNReal.ofReal (Real.sqrt 192) +
        ENNReal.ofReal (t / 2) *
          μ W m {ω | 192 < ‖∑ j, gueBlock W m ω j * gueBlock W m ω j‖} +
        ENNReal.ofReal (1 / (2 * t)) *
          ENNReal.ofReal
            (m * (2 * W) ^ 2 * ((m * W * W : ℝ) * ∫ x, x ^ 2 ∂(gaussianReal 0 1))) := by
  set S : Ω W m → ℝ := fun ω => ‖∑ j, gueBlock W m ω j * gueBlock W m ω j‖ with hS_def
  have hC : ∀ j, Continuous fun ω : Ω W m => gueBlock W m ω j := fun j =>
    continuous_pi fun x => continuous_pi fun y => CoercivityTensor_continuous_entry W m j x y
  have hSc : Continuous S :=
    continuous_norm.comp (continuous_finsetSum _ fun j _ => (hC j).matrix_mul (hC j))
  have hSm : MeasurableSet {ω | 192 < S ω} := measurableSet_lt measurable_const hSc.measurable
  have hpt : ∀ ω, ENNReal.ofReal (Real.sqrt (S ω)) ≤
      (ENNReal.ofReal (Real.sqrt 192) +
        {ω | 192 < S ω}.indicator (fun _ => ENNReal.ofReal (t / 2)) ω) +
        ENNReal.ofReal (1 / (2 * t)) * ENNReal.ofReal (S ω) := by
    intro ω
    have hS0 : 0 ≤ S ω := norm_nonneg _
    by_cases h : 192 < S ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | 192 < S ω} from h)]
      have hamgm : Real.sqrt (S ω) ≤ t / 2 + 1 / (2 * t) * S ω := by
        have hsq := Real.sq_sqrt hS0
        set u := Real.sqrt (S ω) with hu
        rw [← sub_nonneg]
        have : t / 2 + 1 / (2 * t) * S ω - u = (u - t) ^ 2 / (2 * t) := by
          rw [← hsq]
          field_simp
          ring
        rw [this]
        positivity
      calc ENNReal.ofReal (Real.sqrt (S ω))
          ≤ ENNReal.ofReal (t / 2 + 1 / (2 * t) * S ω) := ENNReal.ofReal_le_ofReal hamgm
        _ = ENNReal.ofReal (t / 2) + ENNReal.ofReal (1 / (2 * t)) * ENNReal.ofReal (S ω) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by positivity)]
        _ ≤ _ := by
          rw [add_assoc]
          exact le_add_self
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | 192 < S ω} from h), add_zero]
      calc ENNReal.ofReal (Real.sqrt (S ω)) ≤ ENNReal.ofReal (Real.sqrt 192) :=
            ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (not_lt.1 h))
        _ ≤ _ := le_self_add
  have hE : ∫⁻ ω, ENNReal.ofReal (S ω) ∂(μ W m) ≤
      ENNReal.ofReal (m * (2 * W) ^ 2 * ((m * W * W : ℝ) * ∫ x, x ^ 2 ∂(gaussianReal 0 1))) := by
    have hint : Integrable (fun ω : Ω W m => (m * (2 * W) ^ 2 : ℝ) * ‖ω‖ ^ 2) (μ W m) :=
      (CoercivityTensor_memLp W m 2).integrable_norm_pow'.const_mul _
    calc ∫⁻ ω, ENNReal.ofReal (S ω) ∂(μ W m)
        ≤ ∫⁻ ω, ENNReal.ofReal ((m * (2 * W) ^ 2 : ℝ) * ‖ω‖ ^ 2) ∂(μ W m) :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (CoercivityTensor_norm_sq_sum_le ω)
      _ = ENNReal.ofReal (∫ ω, (m * (2 * W) ^ 2 : ℝ) * ‖ω‖ ^ 2 ∂(μ W m)) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun _ => by positivity)).symm
      _ ≤ _ := by
          rw [integral_const_mul]
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (CoercivityTensor_integral_norm_sq_le W m) (by positivity))
  calc ∫⁻ ω, ENNReal.ofReal (Real.sqrt (S ω)) ∂(μ W m)
      ≤ ∫⁻ ω, ((ENNReal.ofReal (Real.sqrt 192) +
          {ω | 192 < S ω}.indicator (fun _ => ENNReal.ofReal (t / 2)) ω) +
          ENNReal.ofReal (1 / (2 * t)) * ENNReal.ofReal (S ω)) ∂(μ W m) := lintegral_mono hpt
    _ = ENNReal.ofReal (Real.sqrt 192) + ENNReal.ofReal (t / 2) * μ W m {ω | 192 < S ω} +
          ENNReal.ofReal (1 / (2 * t)) * ∫⁻ ω, ENNReal.ofReal (S ω) ∂(μ W m) := by
        rw [lintegral_add_left (f := fun ω => ENNReal.ofReal (Real.sqrt 192) +
            {ω | 192 < S ω}.indicator (fun _ => ENNReal.ofReal (t / 2)) ω)
            ((measurable_const.indicator hSm).const_add _),
          lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_indicator_const hSm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by gcongr

/-! ### The asymptotic bound -/

/-- `(4 p!)^{1/(2p)} ≤ 2 √p`. -/
private lemma CoercivityTensor_factorial_rpow_le {p : ℕ} (hp : 1 ≤ p) :
    (4 * (p.factorial : ℝ)) ^ ((2 * p : ℝ)⁻¹) ≤ 2 * Real.sqrt p := by
  have h1 : 4 * (p.factorial : ℝ) ≤ (4 * p) ^ p := by
    have hf : (p.factorial : ℝ) ≤ (p : ℝ) ^ p := by exact_mod_cast Nat.factorial_le_pow p
    have h4 : (4 : ℝ) ≤ 4 ^ p := by
      calc (4 : ℝ) = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ p := pow_le_pow_right₀ (by norm_num) hp
    rw [mul_pow]
    exact mul_le_mul h4 hf (by positivity) (by positivity)
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  calc _ ≤ ((4 * p : ℝ) ^ p) ^ ((2 * p : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ = Real.sqrt (4 * p) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.sqrt_eq_rpow]
        congr 1
        field_simp
    _ = 2 * Real.sqrt p := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]

/-- The explicit bound tends to `2 √192 < 57/2`, so it is below `57/2` for large `W`
(`p = ⌊√W⌋ + 1`). -/
private lemma CoercivityTensor_eventually {c : ℝ} (hc : 0 < c) (K : ℝ) :
    ∀ᶠ W : ℕ in Filter.atTop,
      Real.exp (Real.log W / ((Nat.sqrt W + 1 : ℕ) : ℝ)) *
        (2 + 2 * π * Real.sqrt (((Nat.sqrt W + 1 : ℕ) : ℝ) / (2 * W))) *
        (Real.sqrt 192 + Real.exp (-(c / 2 * W)) / 2 +
          K * ((W : ℝ) ^ 4 * Real.exp (-(c / 2 * W)))) < 57 / 2 := by
  have hW : Filter.Tendsto (fun W : ℕ => (W : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) Filter.atTop (nhds 0) := by
    refine (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero.congr'
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.sqrt_eq_rpow]
  have h1 : Filter.Tendsto (fun W : ℕ => Real.log W / ((Nat.sqrt W + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hlog.comp hW) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 1] with W hW1
      have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
      exact div_nonneg (Real.log_nonneg this) (by positivity)
    · filter_upwards [Filter.eventually_ge_atTop 1] with W hW1
      have h1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
      have hs : 0 < Real.sqrt W := Real.sqrt_pos.2 (by linarith)
      have hlt : Real.sqrt W ≤ ((Nat.sqrt W + 1 : ℕ) : ℝ) := by
        push_cast
        exact Real.real_sqrt_lt_nat_sqrt_succ.le
      exact div_le_div_of_nonneg_left (Real.log_nonneg h1') hs hlt
  have hE : Filter.Tendsto (fun W : ℕ => Real.exp (Real.log W / ((Nat.sqrt W + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 1) := by
    simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp h1
  have h2 : Filter.Tendsto (fun W : ℕ => ((Nat.sqrt W + 1 : ℕ) : ℝ) / (2 * W))
      Filter.atTop (nhds 0) := by
    have hinv : Filter.Tendsto (fun W : ℕ => (Real.sqrt W)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hW)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
    · filter_upwards with W
      positivity
    · filter_upwards [Filter.eventually_ge_atTop 1] with W hW1
      have h1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
      have hs1 : 1 ≤ Real.sqrt W := Real.one_le_sqrt.2 h1'
      have hsq : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt (by linarith)
      have hp : ((Nat.sqrt W + 1 : ℕ) : ℝ) ≤ Real.sqrt W + 1 := by
        push_cast
        linarith [Real.nat_sqrt_le_real_sqrt (a := W)]
      rw [div_le_iff₀ (by positivity)]
      calc ((Nat.sqrt W + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt W := by linarith
        _ = (Real.sqrt W)⁻¹ * (2 * W) := by
          rw [eq_comm, inv_mul_eq_iff_eq_mul₀ (by positivity)]
          linear_combination (-2) * hsq
  have hT : Filter.Tendsto
      (fun W : ℕ => 2 + 2 * π * Real.sqrt (((Nat.sqrt W + 1 : ℕ) : ℝ) / (2 * W)))
      Filter.atTop (nhds 2) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    simpa using (this.const_mul (2 * π)).const_add 2
  have hu : Filter.Tendsto (fun W : ℕ => c / 2 * (W : ℝ)) Filter.atTop Filter.atTop :=
    hW.const_mul_atTop (by positivity)
  have he : Filter.Tendsto (fun W : ℕ => Real.exp (-(c / 2 * W))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hu
  have hpe : Filter.Tendsto (fun W : ℕ => (W : ℝ) ^ 4 * Real.exp (-(c / 2 * W)))
      Filter.atTop (nhds 0) := by
    have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hu).const_mul ((2 / c) ^ 4)
    rw [mul_zero] at this
    refine this.congr' (Filter.Eventually.of_forall fun W => ?_)
    simp only [Function.comp]
    field_simp
  have hB : Filter.Tendsto (fun W : ℕ => Real.sqrt 192 + Real.exp (-(c / 2 * W)) / 2 +
      K * ((W : ℝ) ^ 4 * Real.exp (-(c / 2 * W)))) Filter.atTop (nhds (Real.sqrt 192)) := by
    simpa using ((he.div_const 2).const_add (Real.sqrt 192)).add (hpe.const_mul K)
  have hlt : 1 * 2 * Real.sqrt 192 < 57 / 2 := by
    have : Real.sqrt 192 < 57 / 4 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    linarith
  exact ((hE.mul hT).mul hB).eventually (gt_mem_nhds hlt)

/-- `𝔼 ‖Σ_{j<128} B_j ⊗ C_jᵗ‖ ≤ 57/2` for large `W`, `B`, `C` independent GUE families of (1.2)
[eq:covariance]. -/
theorem tensor_norm_mean_le :
    ∃ W₂ : ℕ, ∀ W, W₂ ≤ W →
      ∫ q, ‖∑ j, gueBlock W 128 q.1 j ⊗ₖ (gueBlock W 128 q.2 j)ᵀ‖
        ∂((μ W 128).prod (μ W 128)) ≤ 57 / 2 := by
  obtain ⟨c, hc, W₁, hgood⟩ := quadMin_norm_good
  set g₂ : ℝ := ∫ x, x ^ 2 ∂(gaussianReal 0 1) with hg₂
  have hg₂0 : 0 ≤ g₂ := integral_nonneg fun _ => sq_nonneg _
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (CoercivityTensor_eventually hc (32768 * g₂))
  refine ⟨max (max N W₁) 1, fun W hW => ?_⟩
  have hWN : N ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWW₁ : W₁ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hR := hN W hWN
  set p : ℕ := Nat.sqrt W + 1 with hp_def
  have hp : 1 ≤ p := by omega
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  set I : ℝ := ∫ ω, ‖gueBlock W 1 ω 0‖ ^ (2 * p) ∂(μ W 1) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => by positivity
  set r : ℝ := (2 * p : ℝ)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  set A : ℝ := ((W : ℝ) * W) ^ r * I ^ r with hA
  have hA0 : 0 ≤ A := by positivity
  set S : Ω W 128 → ℝ := fun ω => ‖∑ j, gueBlock W 128 ω j * gueBlock W 128 ω j‖ with hS
  -- the conditional bound for fixed `C`
  have hinner : ∀ ω₂ : Ω W 128, ∫⁻ ω₁, ENNReal.ofReal
      ‖∑ j, gueBlock W 128 ω₁ j ⊗ₖ (gueBlock W 128 ω₂ j)ᵀ‖ ∂(μ W 128) ≤
        ENNReal.ofReal (A * Real.sqrt (S ω₂)) := by
    intro ω₂
    refine (CoercivityTensor_cond W 128 p hp (fun j => (gueBlock W 128 ω₂ j)ᵀ)
      (fun j => (gueBlock_isHermitian W 128 ω₂ j).transpose)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hT : ∑ j, (gueBlock W 128 ω₂ j)ᵀ * (gueBlock W 128 ω₂ j)ᵀ =
        (∑ j, gueBlock W 128 ω₂ j * gueBlock W 128 ω₂ j)ᵀ := by
      rw [Matrix.transpose_sum]
      simp [Matrix.transpose_mul]
    have hs' : ‖∑ j, (gueBlock W 128 ω₂ j)ᵀ * (gueBlock W 128 ω₂ j)ᵀ‖ ≤ S ω₂ := by
      rw [hT]
      exact CoercivityTensor_norm_transpose_le _
    have hS0 : 0 ≤ S ω₂ := norm_nonneg _
    have hpr' : (p : ℝ) * r = 1 / 2 := by
      rw [hr]
      field_simp
    calc ((W : ℝ) * (W * I) * ‖∑ j, (gueBlock W 128 ω₂ j)ᵀ * (gueBlock W 128 ω₂ j)ᵀ‖ ^ p) ^ r
        ≤ ((W : ℝ) * W * I * S ω₂ ^ p) ^ r := by
          refine Real.rpow_le_rpow (by positivity) ?_ hr0
          rw [← mul_assoc]
          gcongr
      _ = A * Real.sqrt (S ω₂) := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hI0,
            ← Real.rpow_natCast, ← Real.rpow_mul hS0, hpr', ← Real.sqrt_eq_rpow]
  -- the numerical bound
  set t : ℝ := Real.exp (c / 2 * W) with ht
  have ht0 : 0 < t := Real.exp_pos _
  set K' : ℝ := ((128 : ℕ) : ℝ) * (2 * W) ^ 2 * (((128 : ℕ) : ℝ) * W * W * g₂) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hbad : μ W 128 {ω | 192 < S ω} ≤ ENNReal.ofReal (Real.exp (-c * W)) :=
    (measure_mono fun ω hω => Or.inr hω).trans (hgood W hWW₁)
  have hfinal : A * (Real.sqrt 192 + t / 2 * Real.exp (-c * W) + 1 / (2 * t) * K') ≤ 57 / 2 := by
    refine le_of_lt (lt_of_le_of_lt ?_ hR)
    have hA' : A ≤ Real.exp (Real.log W / p) * (2 + 2 * π * Real.sqrt (p / (2 * W))) := by
      have hWW : ((W : ℝ) * W) ^ r = Real.exp (Real.log W / p) := by
        rw [Real.rpow_def_of_pos (by positivity), Real.log_mul (by positivity) (by positivity)]
        congr 1
        rw [hr]
        field_simp
        ring
      have hM := gueBlock_norm_moment_le hW1 hp
      have hF := CoercivityTensor_factorial_rpow_le hp
      have hsq : 2 * Real.sqrt p * π / Real.sqrt (2 * W) =
          2 * π * Real.sqrt (p / (2 * W)) := by
        rw [Real.sqrt_div (by positivity)]
        ring
      rw [hA, hWW]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      calc I ^ r ≤ 2 + (4 * (p.factorial : ℝ)) ^ r * π / Real.sqrt (2 * W) := hM
        _ ≤ 2 + 2 * Real.sqrt p * π / Real.sqrt (2 * W) := by gcongr
        _ = _ := by rw [hsq]
    have hB' : Real.sqrt 192 + t / 2 * Real.exp (-c * W) + 1 / (2 * t) * K' =
        Real.sqrt 192 + Real.exp (-(c / 2 * W)) / 2 +
          32768 * g₂ * ((W : ℝ) ^ 4 * Real.exp (-(c / 2 * W))) := by
      have h1 : t * Real.exp (-c * W) = Real.exp (-(c / 2 * W)) := by
        rw [ht, ← Real.exp_add]
        ring_nf
      have h2 : 1 / t = Real.exp (-(c / 2 * W)) := by
        rw [ht, Real.exp_neg, one_div]
      calc _ = Real.sqrt 192 + (t * Real.exp (-c * W)) / 2 + (1 / t) * (K' / 2) := by ring
        _ = _ := by
          rw [h1, h2, hK']
          push_cast
          ring
    rw [hB']
    exact mul_le_mul_of_nonneg_right hA' (by positivity)
  -- assembly
  have hXc : Continuous fun q : Ω W 128 × Ω W 128 =>
      ∑ j, gueBlock W 128 q.1 j ⊗ₖ (gueBlock W 128 q.2 j)ᵀ := by
    refine continuous_pi fun x => continuous_pi fun y => ?_
    simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
    exact continuous_finsetSum _ fun j _ =>
      ((CoercivityTensor_continuous_entry W 128 j _ _).comp continuous_fst).mul
        ((CoercivityTensor_continuous_entry W 128 j _ _).comp continuous_snd)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (continuous_norm.comp hXc).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
  have hmeas : AEMeasurable (fun q : Ω W 128 × Ω W 128 => ENNReal.ofReal
      ‖∑ j, gueBlock W 128 q.1 j ⊗ₖ (gueBlock W 128 q.2 j)ᵀ‖) ((μ W 128).prod (μ W 128)) :=
    (ENNReal.continuous_ofReal.comp (continuous_norm.comp hXc)).measurable.aemeasurable
  rw [lintegral_prod_symm _ hmeas]
  refine (lintegral_mono fun ω₂ => hinner ω₂).trans ?_
  calc ∫⁻ ω₂, ENNReal.ofReal (A * Real.sqrt (S ω₂)) ∂(μ W 128)
      = ENNReal.ofReal A * ∫⁻ ω₂, ENNReal.ofReal (Real.sqrt (S ω₂)) ∂(μ W 128) := by
        simp_rw [ENNReal.ofReal_mul hA0]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal (Real.sqrt 192) +
          ENNReal.ofReal (t / 2) * ENNReal.ofReal (Real.exp (-c * W)) +
          ENNReal.ofReal (1 / (2 * t)) * ENNReal.ofReal K') := by
        gcongr
        exact (CoercivityTensor_sqrt_mean W 128 ht0).trans (by gcongr)
    _ = ENNReal.ofReal (A * (Real.sqrt 192 + t / 2 * Real.exp (-c * W) + 1 / (2 * t) * K')) := by
        rw [ENNReal.ofReal_mul hA0, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (p := t / 2) (by positivity),
          ENNReal.ofReal_mul (p := 1 / (2 * t)) (by positivity)]
    _ ≤ ENNReal.ofReal (57 / 2) := ENNReal.ofReal_le_ofReal hfinal

end LSBA
