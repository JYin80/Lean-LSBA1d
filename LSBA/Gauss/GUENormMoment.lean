import LSBA.Gauss.NormTail

/-!
# Norm moments of a GUE block

Moments of every order of the operator norm of one GUE block, uniform in the width: `𝔼‖V‖^p ≤ C_p`
and integrability. This is the moment half of (11.14) [uvg:eq:tail]; the net tail is not formalized.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The operator norm is at most the Frobenius norm. -/
private theorem guenm_opNorm_sq_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    ‖A‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have hS : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hle : ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
    rw [Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have hx : ‖x‖ = Real.sqrt (∑ j, ‖x.ofLp j‖ ^ 2) := EuclideanSpace.norm_eq x
    rw [EuclideanSpace.norm_eq, hx, ← Real.sqrt_mul hS]
    change √(∑ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2) ≤ _
    refine Real.sqrt_le_sqrt ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : ‖(A *ᵥ x.ofLp) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 := by
      calc ‖(A *ᵥ x.ofLp) i‖ ^ 2 = ‖∑ j, A i j * x.ofLp j‖ ^ 2 := by
            simp [Matrix.mulVec, dotProduct]
        _ ≤ (∑ j, ‖A i j * x.ofLp j‖) ^ 2 := by
            gcongr; exact norm_sum_le _ _
        _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 := by
            simp_rw [norm_mul]
            exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    exact h1
  calc ‖A‖ ^ 2 ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt hS

/-- A squared entry of the block: `W |V_{αβ}|² = (ω_{αβ}² + ω_{βα}²)/2`. -/
private lemma guenm_entry_sq {W L : ℕ} (hW : 0 < W) (ω : Ω W L) (a : Fin L) (α β : Fin W) :
    (W : ℝ) * ‖gueBlock W L ω a α β‖ ^ 2 = (ω (a, α, β) ^ 2 + ω (a, β, α) ^ 2) / 2 := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hdiv : ∀ (z : ℂ) (r : ℝ), 0 ≤ r → ‖z / (r : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / r ^ 2 := by
    intro z r hr
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr, div_pow]
  have hadd : ∀ x y : ℝ, ‖(x : ℂ) + Complex.I * y‖ ^ 2 = x ^ 2 + y ^ 2 := by
    intro x y
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp; ring
  have hsub : ∀ x y : ℝ, ‖(x : ℂ) - Complex.I * y‖ ^ 2 = x ^ 2 + y ^ 2 := by
    intro x y
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp; ring
  simp only [gueBlock, Matrix.of_apply]
  split_ifs with h1 h2
  · subst h1
    rw [hdiv _ _ (Real.sqrt_nonneg _), Real.sq_sqrt hWpos.le, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  · rw [hdiv _ _ (Real.sqrt_nonneg _), hadd, Real.sq_sqrt (by positivity)]
    field_simp
  · rw [hdiv _ _ (Real.sqrt_nonneg _), hsub, Real.sq_sqrt (by positivity)]
    field_simp
    ring

/-- `W ‖V‖² ≤ ∑_p ω_p²`: the squared operator norm of the block, scaled by `W`, is at most the
squared Euclidean norm of the coordinates. -/
private lemma guenm_W_sq_le {W : ℕ} (hW : 0 < W) (ω : Ω W 1) :
    (W : ℝ) * ‖gueBlock W 1 ω 0‖ ^ 2 ≤ ∑ p : Fin 1 × Fin W × Fin W, ω p ^ 2 := by
  have hfrob : ∑ α, ∑ β, (W : ℝ) * ‖gueBlock W 1 ω 0 α β‖ ^ 2 = ∑ α, ∑ β, ω (0, α, β) ^ 2 := by
    simp_rw [guenm_entry_sq hW]
    have hswap : ∑ α : Fin W, ∑ β : Fin W, ω (0, β, α) ^ 2 =
        ∑ α : Fin W, ∑ β : Fin W, ω (0, α, β) ^ 2 := Finset.sum_comm
    simp_rw [add_div, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hswap]
    ring
  calc (W : ℝ) * ‖gueBlock W 1 ω 0‖ ^ 2
      ≤ (W : ℝ) * ∑ α, ∑ β, ‖gueBlock W 1 ω 0 α β‖ ^ 2 := by
        gcongr; exact guenm_opNorm_sq_le _
    _ = ∑ α, ∑ β, (W : ℝ) * ‖gueBlock W 1 ω 0 α β‖ ^ 2 := by simp only [Finset.mul_sum]
    _ = ∑ α, ∑ β, ω (0, α, β) ^ 2 := hfrob
    _ = ∑ p : Fin 1 × Fin W × Fin W, ω p ^ 2 := by
        rw [Fintype.sum_prod_type, Fin.sum_univ_one]
        simp [Fintype.sum_prod_type]

/-- A finite constant bounding the `2p`-th moment of the standard Gaussian. -/
private lemma guenm_gauss_moment (p : ℕ) :
    ∃ m : ℝ, 0 ≤ m ∧
      ∫⁻ x : ℝ, ENNReal.ofReal (x ^ (2 * p)) ∂(gaussianReal 0 1) ≤ ENNReal.ofReal m := by
  have hm : MemLp id (((2 * p : ℕ)) : ℝ≥0∞) (gaussianReal (0 : ℝ) 1) :=
    memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) _ (ENNReal.natCast_ne_top _)
  have hm' : MemLp id (2 * p : ℕ) (gaussianReal (0 : ℝ) 1) := by simpa using hm
  have h1 : Integrable (fun x : ℝ => ‖id x‖ ^ (2 * p)) (gaussianReal 0 1) :=
    hm'.integrable_norm_pow'
  refine ⟨∫ x, ‖x‖ ^ (2 * p) ∂(gaussianReal 0 1), integral_nonneg fun _ => by positivity, ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal (by simpa using h1)
    (Filter.Eventually.of_forall fun _ => by positivity)]
  refine le_of_eq (lintegral_congr fun x => ?_)
  rw [Real.norm_eq_abs, (even_two_mul p).pow_abs]

/-- The `2p`-th moment of one coordinate of the sample. -/
private lemma guenm_coord (W L p : ℕ) (i : Fin L × Fin W × Fin W) :
    ∫⁻ ω, ENNReal.ofReal (ω i ^ (2 * p)) ∂(μ W L) =
      ∫⁻ x : ℝ, ENNReal.ofReal (x ^ (2 * p)) ∂(gaussianReal 0 1) :=
  (measurePreserving_eval (fun _ : Fin L × Fin W × Fin W => gaussianReal (0 : ℝ) 1)
      i).lintegral_comp (f := fun x : ℝ => ENNReal.ofReal (x ^ (2 * p)))
    (by fun_prop)

private lemma guenm_measurable (W L : ℕ) (a : Fin L) :
    Measurable fun ω : Ω W L => gueBlock W L ω a := by
  refine measurable_pi_iff.2 fun α => measurable_pi_iff.2 fun β => ?_
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma guenm_measurable_norm (W L : ℕ) (a : Fin L) :
    Measurable fun ω : Ω W L => ‖gueBlock W L ω a‖ :=
  (guenm_measurable W L a).norm

/-- Even moments of the norm grow at most like `W^p`: `𝔼‖V‖^{2p} ≤ m_p W^p` for `p ≥ 1`. -/
private lemma guenm_sq_moment (q : ℕ) :
    ∃ m : ℝ, 0 ≤ m ∧ ∀ W : ℕ, 0 < W →
      ∫⁻ ω, ‖gueBlock W 1 ω 0‖ₑ ^ (2 * (q + 1)) ∂(μ W 1) ≤
        ENNReal.ofReal (m * (W : ℝ) ^ (q + 1)) := by
  obtain ⟨m, hm0, hm⟩ := guenm_gauss_moment (q + 1)
  refine ⟨m, hm0, fun W hW => ?_⟩
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  set c : ℝ := ((W : ℝ) ^ 2) ^ q / (W : ℝ) ^ (q + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ ω : Ω W 1, ‖gueBlock W 1 ω 0‖ ^ (2 * (q + 1)) ≤
      c * ∑ i : Fin 1 × Fin W × Fin W, ω i ^ (2 * (q + 1)) := by
    intro ω
    have h1 := guenm_W_sq_le hW ω
    have h2 : (∑ i : Fin 1 × Fin W × Fin W, ω i ^ 2) ^ (q + 1) ≤
        ((Finset.univ : Finset (Fin 1 × Fin W × Fin W)).card : ℝ) ^ q *
          ∑ i : Fin 1 × Fin W × Fin W, (ω i ^ 2) ^ (q + 1) :=
      pow_sum_le_card_mul_sum_pow (fun i _ => by positivity) q
    have hcard : ((Finset.univ : Finset (Fin 1 × Fin W × Fin W)).card : ℝ) = (W : ℝ) ^ 2 := by
      simp [Finset.card_univ, Fintype.card_prod]; ring
    rw [hcard] at h2
    have h3 : ((W : ℝ) * ‖gueBlock W 1 ω 0‖ ^ 2) ^ (q + 1) ≤
        ((W : ℝ) ^ 2) ^ q * ∑ i : Fin 1 × Fin W × Fin W, (ω i ^ 2) ^ (q + 1) :=
      (pow_le_pow_left₀ (by positivity) h1 _).trans h2
    have h4 : ‖gueBlock W 1 ω 0‖ ^ (2 * (q + 1)) * (W : ℝ) ^ (q + 1) ≤
        ((W : ℝ) ^ 2) ^ q * ∑ i : Fin 1 × Fin W × Fin W, ω i ^ (2 * (q + 1)) := by
      have e1 : ((W : ℝ) * ‖gueBlock W 1 ω 0‖ ^ 2) ^ (q + 1) =
          ‖gueBlock W 1 ω 0‖ ^ (2 * (q + 1)) * (W : ℝ) ^ (q + 1) := by
        rw [mul_pow, ← pow_mul]; ring
      have e2 : ∀ i : Fin 1 × Fin W × Fin W, (ω i ^ 2) ^ (q + 1) = ω i ^ (2 * (q + 1)) :=
        fun i => (pow_mul _ _ _).symm
      rw [e1] at h3
      simpa only [e2] using h3
    rw [hc, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact h4
  have hmeas : ∀ i : Fin 1 × Fin W × Fin W,
      Measurable fun ω : Ω W 1 => ENNReal.ofReal (ω i ^ (2 * (q + 1))) := fun i =>
    ((measurable_pi_apply i).pow_const _).ennreal_ofReal
  calc ∫⁻ ω, ‖gueBlock W 1 ω 0‖ₑ ^ (2 * (q + 1)) ∂(μ W 1)
      ≤ ∫⁻ ω, ENNReal.ofReal c *
          ∑ i : Fin 1 × Fin W × Fin W, ENNReal.ofReal (ω i ^ (2 * (q + 1))) ∂(μ W 1) := by
        refine lintegral_mono fun ω => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
          ← ENNReal.ofReal_sum_of_nonneg (fun i _ => (even_two_mul _).pow_nonneg _),
          ← ENNReal.ofReal_mul hc0]
        exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal c * ∑ i : Fin 1 × Fin W × Fin W,
          ∫⁻ ω, ENNReal.ofReal (ω i ^ (2 * (q + 1))) ∂(μ W 1) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum _ fun i _ => hmeas i]
    _ ≤ ENNReal.ofReal c * ∑ i : Fin 1 × Fin W × Fin W, ENNReal.ofReal m := by
        gcongr with i
        rw [guenm_coord]
        exact hm
    _ = ENNReal.ofReal (m * (W : ℝ) ^ (q + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hn : ((Fintype.card (Fin 1 × Fin W × Fin W) : ℕ) : ℝ≥0∞) =
            ENNReal.ofReal ((W : ℝ) ^ 2) := by
          rw [← ENNReal.ofReal_natCast]
          simp [Fintype.card_prod]
          ring_nf
        rw [hn, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc0]
        congr 1
        rw [hc]
        field_simp
        ring

/-- The tail of one block against the polynomial weight: `W^p P(‖V‖ > 16) ≤ 31^p + 2^p p!`. -/
private lemma guenm_weighted_tail (W p : ℕ) :
    ENNReal.ofReal ((W : ℝ) ^ p) * (μ W 1) {ω | 16 < ‖gueBlock W 1 ω 0‖} ≤
      ENNReal.ofReal ((31 : ℝ) ^ p + 2 ^ p * (p.factorial : ℝ)) := by
  by_cases hW : W < 32
  · calc ENNReal.ofReal ((W : ℝ) ^ p) * (μ W 1) {ω | 16 < ‖gueBlock W 1 ω 0‖}
        ≤ ENNReal.ofReal ((W : ℝ) ^ p) * 1 := by gcongr; exact prob_le_one
      _ ≤ ENNReal.ofReal ((31 : ℝ) ^ p + 2 ^ p * (p.factorial : ℝ)) := by
          rw [mul_one]
          refine ENNReal.ofReal_le_ofReal ?_
          have h31 : (W : ℝ) ≤ 31 := by exact_mod_cast Nat.lt_succ_iff.mp hW
          have : (W : ℝ) ^ p ≤ 31 ^ p := pow_le_pow_left₀ (Nat.cast_nonneg _) h31 p
          have : (0 : ℝ) ≤ 2 ^ p * (p.factorial : ℝ) := by positivity
          linarith
  · have hW : 32 ≤ W := not_lt.mp hW
    have htail := gueBlock_norm_tail (L := 1) hW 0
    have hWr : (0 : ℝ) ≤ W := Nat.cast_nonneg W
    calc ENNReal.ofReal ((W : ℝ) ^ p) * (μ W 1) {ω | 16 < ‖gueBlock W 1 ω 0‖}
        ≤ ENNReal.ofReal ((W : ℝ) ^ p) * ENNReal.ofReal (Real.exp (-(W : ℝ) / 2)) := by
          gcongr
      _ = ENNReal.ofReal ((W : ℝ) ^ p * Real.exp (-(W : ℝ) / 2)) := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((31 : ℝ) ^ p + 2 ^ p * (p.factorial : ℝ)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := Real.pow_div_factorial_le_exp ((W : ℝ) / 2) (by positivity) p
          have hf : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
          have h2 : (W : ℝ) ^ p ≤ 2 ^ p * (p.factorial : ℝ) * Real.exp ((W : ℝ) / 2) := by
            rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h1
            have h3 : (W : ℝ) ^ p = (W : ℝ) ^ p / 2 ^ p * 2 ^ p := by field_simp
            nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) p]
          have h4 : (W : ℝ) ^ p * Real.exp (-(W : ℝ) / 2) ≤ 2 ^ p * (p.factorial : ℝ) := by
            calc (W : ℝ) ^ p * Real.exp (-(W : ℝ) / 2)
                ≤ 2 ^ p * (p.factorial : ℝ) * Real.exp ((W : ℝ) / 2) * Real.exp (-(W : ℝ) / 2) := by
                  gcongr
              _ = 2 ^ p * (p.factorial : ℝ) := by
                  rw [mul_assoc, ← Real.exp_add]
                  have : (W : ℝ) / 2 + -(W : ℝ) / 2 = 0 := by ring
                  rw [this, Real.exp_zero, mul_one]
          have : (0 : ℝ) ≤ 31 ^ p := by positivity
          linarith

/-- Operator-norm moments of one GUE block of (1.2) [eq:covariance] are bounded uniformly in
`W`: `𝔼‖V‖^p ≤ C_p` (the moment half of (11.14) [uvg:eq:tail]). -/
theorem lintegral_norm_gueBlock_pow_le (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ, ∫⁻ ω, ‖gueBlock W 1 ω 0‖ₑ ^ p ∂(μ W 1) ≤ ENNReal.ofReal C := by
  rcases p with _ | q
  · refine ⟨1, one_pos, fun W => ?_⟩
    simp
  obtain ⟨m, hm0, hm⟩ := guenm_sq_moment q
  refine ⟨1 + 16 ^ (q + 1) + ((31 : ℝ) ^ (q + 1) + 2 ^ (q + 1) * ((q + 1).factorial : ℝ)) + m,
    by positivity, fun W => ?_⟩
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · have h0 : ∀ ω : Ω 0 1, ‖gueBlock 0 1 ω 0‖ₑ ^ (q + 1) ≤ 1 := by
      intro ω
      have : gueBlock 0 1 ω 0 = 0 := Subsingleton.elim _ _
      simp [this]
    calc ∫⁻ ω, ‖gueBlock 0 1 ω 0‖ₑ ^ (q + 1) ∂(μ 0 1) ≤ ∫⁻ _, 1 ∂(μ 0 1) := lintegral_mono h0
      _ = 1 := by simp
      _ ≤ _ := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (by
            have : (0 : ℝ) ≤ 16 ^ (q + 1) := by positivity
            have : (0 : ℝ) ≤ (31 : ℝ) ^ (q + 1) + 2 ^ (q + 1) * ((q + 1).factorial : ℝ) := by
              positivity
            linarith)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  set P : ℕ := q + 1 with hP
  set A : Set (Ω W 1) := {ω | 16 < ‖gueBlock W 1 ω 0‖} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const (guenm_measurable_norm W 1 0)
  have hWp : (0 : ℝ) < (W : ℝ) ^ P := by positivity
  have hmeasE : Measurable fun ω : Ω W 1 => ‖gueBlock W 1 ω 0‖ₑ ^ (2 * P) :=
    ((guenm_measurable W 1 0).enorm).pow_const _
  have hpt : ∀ ω : Ω W 1, ‖gueBlock W 1 ω 0‖ₑ ^ P ≤
      ENNReal.ofReal ((W : ℝ) ^ P)⁻¹ * ‖gueBlock W 1 ω 0‖ₑ ^ (2 * P) +
        (ENNReal.ofReal (16 ^ P) + A.indicator (fun _ => ENNReal.ofReal ((W : ℝ) ^ P)) ω) := by
    intro ω
    by_cases hω : ω ∈ A
    · have hω' : 16 < ‖gueBlock W 1 ω 0‖ := hω
      set x : ℝ := ‖gueBlock W 1 ω 0‖ with hx
      have hx0 : 0 ≤ x := norm_nonneg _
      have hreal : x ^ P ≤ (W : ℝ) ^ P + ((W : ℝ) ^ P)⁻¹ * x ^ (2 * P) := by
        have hs : (0 : ℝ) < (W : ℝ) ^ P := hWp
        have e : ((W : ℝ) ^ P)⁻¹ * x ^ (2 * P) = (x ^ P) ^ 2 / (W : ℝ) ^ P := by
          rw [pow_mul', inv_mul_eq_div]
        rw [e]
        have : 2 * x ^ P ≤ (W : ℝ) ^ P + (x ^ P) ^ 2 / (W : ℝ) ^ P := by
          rw [← sub_nonneg]
          have : (W : ℝ) ^ P + (x ^ P) ^ 2 / (W : ℝ) ^ P - 2 * x ^ P =
              ((W : ℝ) ^ P - x ^ P) ^ 2 / (W : ℝ) ^ P := by field_simp; ring
          rw [this]; positivity
        have : 0 ≤ x ^ P := by positivity
        linarith
      rw [Set.indicator_of_mem hω, ← ofReal_norm, ← ENNReal.ofReal_pow hx0,
        ← ENNReal.ofReal_pow hx0]
      have h := ENNReal.ofReal_le_ofReal hreal
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity)] at h
      calc ENNReal.ofReal (x ^ P)
          ≤ ENNReal.ofReal ((W : ℝ) ^ P) +
              ENNReal.ofReal ((W : ℝ) ^ P)⁻¹ * ENNReal.ofReal (x ^ (2 * P)) := h
        _ = ENNReal.ofReal ((W : ℝ) ^ P)⁻¹ * ENNReal.ofReal (x ^ (2 * P)) +
              ENNReal.ofReal ((W : ℝ) ^ P) := add_comm _ _
        _ ≤ _ := add_le_add_right (le_add_self) _
    · have hω' : ‖gueBlock W 1 ω 0‖ ≤ 16 := not_lt.mp hω
      rw [Set.indicator_of_notMem hω, add_zero, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      refine le_add_left ?_
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hω' P)
  calc ∫⁻ ω, ‖gueBlock W 1 ω 0‖ₑ ^ P ∂(μ W 1)
      ≤ ∫⁻ ω, (ENNReal.ofReal ((W : ℝ) ^ P)⁻¹ * ‖gueBlock W 1 ω 0‖ₑ ^ (2 * P) +
        (ENNReal.ofReal (16 ^ P) + A.indicator (fun _ => ENNReal.ofReal ((W : ℝ) ^ P)) ω))
        ∂(μ W 1) := lintegral_mono hpt
    _ = ENNReal.ofReal ((W : ℝ) ^ P)⁻¹ * ∫⁻ ω, ‖gueBlock W 1 ω 0‖ₑ ^ (2 * P) ∂(μ W 1) +
        (ENNReal.ofReal (16 ^ P) +
          ENNReal.ofReal ((W : ℝ) ^ P) * (μ W 1) A) := by
        rw [lintegral_add_left (hmeasE.const_mul _), lintegral_const_mul _ hmeasE,
          lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_indicator_const hAm]
    _ ≤ ENNReal.ofReal m + (ENNReal.ofReal (16 ^ P) +
          ENNReal.ofReal ((31 : ℝ) ^ P + 2 ^ P * (P.factorial : ℝ))) := by
        gcongr
        · calc ENNReal.ofReal ((W : ℝ) ^ P)⁻¹ * ∫⁻ ω, ‖gueBlock W 1 ω 0‖ₑ ^ (2 * P) ∂(μ W 1)
              ≤ ENNReal.ofReal ((W : ℝ) ^ P)⁻¹ * ENNReal.ofReal (m * (W : ℝ) ^ P) := by
                gcongr; exact hm W hW
            _ = ENNReal.ofReal m := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                congr 1
                field_simp
        · exact guenm_weighted_tail W P
    _ ≤ ENNReal.ofReal (1 + 16 ^ P + ((31 : ℝ) ^ P + 2 ^ P * (P.factorial : ℝ)) + m) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        linarith

theorem integrable_norm_gueBlock_pow (W p : ℕ) :
    Integrable (fun ω => ‖gueBlock W 1 ω 0‖ ^ p) (μ W 1) := by
  refine ⟨((guenm_measurable_norm W 1 0).pow_const p).aestronglyMeasurable, ?_⟩
  obtain ⟨C, -, hC⟩ := lintegral_norm_gueBlock_pow_le p
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := C))
  refine le_trans (le_of_eq ?_) (hC W)
  refine lintegral_congr fun ω => ?_
  rw [enorm_pow, enorm_norm]

end LSBA
