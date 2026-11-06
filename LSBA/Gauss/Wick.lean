import LSBA.Gauss.GUELaw

/-!
# Wick recursion for one GUE block

The Gaussian integration-by-parts (Wick, Isserlis) recursion for products of linear functionals
`ℓ_i(V) = x_i* V w_i` of one GUE block with the covariance (1.2) [eq:covariance]:
`𝔼[ℓ_0 ∏_{i∈s} ℓ_i] = Σ_{j∈s} 𝔼[ℓ_0 ℓ_j] 𝔼[∏_{i∈s∖{j}} ℓ_i]` with
`𝔼[ℓ_0 ℓ_j] = W⁻¹ (x_0* w_j)(x_j* w_0)`. This is the contraction rule used in the proof of
Lemma 11.7 [lg:lem:ideal].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Gaussian integration by parts for products of continuous linear forms -/

/-- Polynomial moments of the sup norm are finite under the standard Gaussian on `ℝ^ι`. -/
private lemma wick_integrable_poly (ι : Type*) [Fintype ι] (m : ℕ) :
    Integrable (fun x : ι → ℝ => (1 + ‖x‖) ^ m) (stdGauss ι) := by
  have hpow1 : Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 1) := by
    have hm : MemLp id (m : ENNReal) (gaussianReal (0 : ℝ) 1) :=
      memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) m (ENNReal.natCast_ne_top m)
    have hm' : MemLp id (m : ℕ) (gaussianReal (0 : ℝ) 1) := by simpa using hm
    have h1 : Integrable (fun x : ℝ => ‖id x‖ ^ m) (gaussianReal 0 1) :=
      hm'.integrable_norm_pow'
    have h2 : Integrable (fun x : ℝ => (2 : ℝ) ^ m * (1 + |x| ^ m)) (gaussianReal 0 1) :=
      ((integrable_const (1 : ℝ)).add (by simpa using h1)).const_mul _
    refine h2.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (by fun_prop : Continuous fun x : ℝ => (1 + |x|) ^ m).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
      have hx : (0 : ℝ) ≤ |x| ^ m := by positivity
      rcases le_total |x| 1 with h | h
      · calc (1 + |x|) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
      · calc (1 + |x|) ^ m ≤ (2 * |x|) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ = 2 ^ m * |x| ^ m := by rw [mul_pow]
          _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
  have hprod : Integrable (fun x : ι → ℝ => ∏ j, (1 + |x j|) ^ m) (stdGauss ι) :=
    Integrable.fintype_prod (f := fun _ (t : ℝ) => (1 + |t|) ^ m) (fun _ => hpow1)
  refine hprod.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ι → ℝ => (1 + ‖x‖) ^ m).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity), Finset.prod_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ m
    have hone : ∀ s : Finset ι, (1 : ℝ) ≤ ∏ l ∈ s, (1 + |x l|) := fun s =>
      Finset.one_le_prod₀ fun l _ => by linarith [abs_nonneg (x l)]
    have : ‖x‖ ≤ (∏ j, (1 + |x j|)) - 1 := by
      refine (pi_norm_le_iff_of_nonneg (by linarith [hone Finset.univ])).mpr fun j => ?_
      have hj : 1 + |x j| ≤ ∏ l, (1 + |x l|) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        exact le_mul_of_one_le_right (by positivity) (hone _)
      rw [Real.norm_eq_abs]
      linarith
    linarith

/-- A continuous linear form on `ℝ^ι` is the sum of its values on the coordinate vectors. -/
private lemma wick_clm_expand {ι : Type*} [Fintype ι] [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℂ)
    (v : ι → ℝ) : L v = ∑ i, (v i : ℂ) * L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (Pi.single i (v i) : ι → ℝ) = v i • Pi.single i 1 := by
    rw [← Pi.single_smul]; simp
  rw [h, map_smul, Complex.real_smul]

/-- Gaussian integration by parts for a product of continuous linear forms: the contraction of
`L₀` with each factor. -/
private lemma wick_clm_prod {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (s : Finset κ) (L : κ → (ι → ℝ) →L[ℝ] ℂ) (L₀ : (ι → ℝ) →L[ℝ] ℂ) :
    ∫ ω, L₀ ω * ∏ i ∈ s, L i ω ∂(stdGauss ι) =
      ∑ j ∈ s, (∑ k, L₀ (Pi.single k 1) * L j (Pi.single k 1)) *
        ∫ ω, ∏ i ∈ s.erase j, L i ω ∂(stdGauss ι) := by
  set F : (ι → ℝ) → ℂ := fun ω => ∏ i ∈ s, L i ω with hFdef
  -- the growth bounds
  set M : ℝ := ∑ i ∈ s, ‖L i‖ with hM
  set M' : ℝ := max 1 M with hM'
  have hM'1 : 1 ≤ M' := le_max_left _ _
  have hM'0 : 0 < M' := lt_of_lt_of_le one_pos hM'1
  have hLM : ∀ i ∈ s, ‖L i‖ ≤ M' := fun i hi =>
    (Finset.single_le_sum (f := fun i => ‖L i‖) (fun _ _ => norm_nonneg _) hi).trans
      (le_max_right _ _)
  set C : ℝ := ((s.card : ℝ) + 1) * M' ^ (s.card + 1) with hC
  have hC0 : 0 ≤ C := by positivity
  have hL1 : ∀ i ∈ s, ∀ ω : ι → ℝ, ‖L i ω‖ ≤ M' * (1 + ‖ω‖) := by
    intro i hi ω
    calc ‖L i ω‖ ≤ ‖L i‖ * ‖ω‖ := (L i).le_opNorm ω
      _ ≤ M' * (1 + ‖ω‖) := by
        have := hLM i hi
        have h2 : 0 ≤ ‖ω‖ := norm_nonneg _
        nlinarith
  have hprod : ∀ t ⊆ s, ∀ ω : ι → ℝ,
      ‖∏ i ∈ t, L i ω‖ ≤ M' ^ s.card * (1 + ‖ω‖) ^ s.card := by
    intro t hts ω
    rw [← mul_pow, norm_prod]
    have hB1 : (1 : ℝ) ≤ M' * (1 + ‖ω‖) := by
      have h2 : 0 ≤ ‖ω‖ := norm_nonneg _
      nlinarith
    calc ∏ i ∈ t, ‖L i ω‖ ≤ ∏ i ∈ t, (M' * (1 + ‖ω‖)) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i hi => hL1 i (hts hi) ω
      _ = (M' * (1 + ‖ω‖)) ^ t.card := Finset.prod_const _
      _ ≤ (M' * (1 + ‖ω‖)) ^ s.card :=
          pow_le_pow_right₀ hB1 (Finset.card_le_card hts)
  have hM'pow : M' ^ s.card ≤ C := by
    calc M' ^ s.card ≤ M' ^ (s.card + 1) := pow_le_pow_right₀ hM'1 (Nat.le_succ _)
      _ ≤ C := by
        rw [hC]
        have h0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
        exact le_mul_of_one_le_left (by positivity) (by linarith)
  have hb : ∀ t ⊆ s, ∀ ω : ι → ℝ, ‖∏ i ∈ t, L i ω‖ ≤ C * (1 + ‖ω‖) ^ s.card := fun t hts ω =>
    (hprod t hts ω).trans (mul_le_mul_of_nonneg_right hM'pow (by positivity))
  -- smoothness and the derivative
  have hFderiv : ∀ ω : ι → ℝ, HasFDerivAt F
      (∑ j ∈ s, (∏ i ∈ s.erase j, L i ω) • L j) ω := fun ω =>
    HasFDerivAt.finsetProd (u := s) (g := fun i ω => L i ω) (g' := L) (x := ω)
      fun i _ => (L i).hasFDerivAt
  have hFc : ContDiff ℝ 1 F := contDiff_prod fun i _ => (L i).contDiff
  have hfd : ∀ ω, fderiv ℝ F ω = ∑ j ∈ s, (∏ i ∈ s.erase j, L i ω) • L j := fun ω =>
    (hFderiv ω).fderiv
  have hb' : ∀ ω : ι → ℝ, ‖fderiv ℝ F ω‖ ≤ C * (1 + ‖ω‖) ^ s.card := by
    intro ω
    rw [hfd]
    calc ‖∑ j ∈ s, (∏ i ∈ s.erase j, L i ω) • L j‖
        ≤ ∑ j ∈ s, ‖(∏ i ∈ s.erase j, L i ω) • L j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ s, (M' ^ s.card * (1 + ‖ω‖) ^ s.card) * M' := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [norm_smul]
          exact mul_le_mul (hprod _ (Finset.erase_subset _ _) ω) (hLM j hj) (norm_nonneg _)
            (by positivity)
      _ = s.card * (M' ^ s.card * (1 + ‖ω‖) ^ s.card * M') := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ C * (1 + ‖ω‖) ^ s.card := by
          have h1 : (s.card : ℝ) * (M' ^ s.card * (1 + ‖ω‖) ^ s.card * M') =
              (s.card : ℝ) * M' ^ (s.card + 1) * (1 + ‖ω‖) ^ s.card := by ring
          rw [h1, hC]
          have h2 : 0 ≤ M' ^ (s.card + 1) * (1 + ‖ω‖) ^ s.card := by positivity
          nlinarith
  -- integrability
  have hint : ∀ {g : (ι → ℝ) → ℂ} {m : ℕ}, Continuous g →
      (∀ ω, ‖g ω‖ ≤ C * (1 + ‖ω‖) ^ m) → Integrable g (stdGauss ι) := by
    intro g m hg hgb
    exact ((wick_integrable_poly ι m).const_mul C).mono' hg.aestronglyMeasurable
      (Filter.Eventually.of_forall hgb)
  have hcont : ∀ t : Finset κ, Continuous fun ω : ι → ℝ => ∏ i ∈ t, L i ω := fun t =>
    continuous_finsetProd _ fun i _ => (L i).continuous
  have hIt : ∀ t ⊆ s, Integrable (fun ω : ι → ℝ => ∏ i ∈ t, L i ω) (stdGauss ι) :=
    fun t hts => hint (hcont t) (hb t hts)
  have hIk : ∀ k : ι, Integrable (fun ω : ι → ℝ => (ω k : ℂ) * F ω) (stdGauss ι) := by
    intro k
    have hc : Continuous fun ω : ι → ℝ => (ω k : ℂ) * F ω :=
      (Complex.continuous_ofReal.comp (continuous_apply k)).mul (hcont s)
    refine ((wick_integrable_poly ι (s.card + 1)).const_mul C).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have hxk : |ω k| ≤ 1 + ‖ω‖ := by
      have := norm_le_pi_norm ω k
      rw [Real.norm_eq_abs] at this
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, pow_succ']
    calc |ω k| * ‖F ω‖ ≤ (1 + ‖ω‖) * (C * (1 + ‖ω‖) ^ s.card) :=
          mul_le_mul hxk (hb s subset_rfl ω) (norm_nonneg _) (by positivity)
      _ = C * ((1 + ‖ω‖) * (1 + ‖ω‖) ^ s.card) := by ring
  -- Stein's identity for each coordinate
  have hstein : ∀ k : ι, ∫ ω, (ω k : ℂ) * F ω ∂(stdGauss ι) =
      ∑ j ∈ s, L j (Pi.single k 1) * ∫ ω, ∏ i ∈ s.erase j, L i ω ∂(stdGauss ι) := by
    intro k
    rw [integral_coord_mul_stdGauss F hFc (C := C) (k := s.card) (fun ω => hb s subset_rfl ω)
      hb' k]
    have hpt : ∀ ω, fderiv ℝ F ω (Pi.single k 1) =
        ∑ j ∈ s, L j (Pi.single k 1) * ∏ i ∈ s.erase j, L i ω := by
      intro ω
      rw [hfd, _root_.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_apply, smul_eq_mul, mul_comm]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun j hj =>
      (hIt _ ((Finset.erase_subset _ _).trans subset_rfl)).const_mul _]
    exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul]
  -- assemble
  have hexp : ∀ ω : ι → ℝ, L₀ ω * F ω =
      ∑ k, L₀ (Pi.single k 1) * ((ω k : ℂ) * F ω) := by
    intro ω
    rw [wick_clm_expand L₀ ω, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  change ∫ ω, L₀ ω * F ω ∂(stdGauss ι) = _
  simp_rw [hexp]
  rw [integral_finsetSum _ fun k _ => (hIk k).const_mul _]
  simp_rw [integral_const_mul, hstein, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The linear functionals `x* V w` of one block -/

/-- Coefficient of the Gaussian coordinate `i` in the functional `V ↦ x* V w` of the block
`gueBlock W 1 · 0`. -/
private def wickCoef (W : ℕ) (x w : Fin W → ℂ) (i : Fin 1 × Fin W × Fin W) : ℂ :=
  ((Real.sqrt W : ℝ) : ℂ)⁻¹ * (star x ⬝ᵥ (hermBasis W i.2 *ᵥ w))

/-- The functional `ω ↦ x* V(ω) w` as a continuous linear form on the Gaussian coordinates. -/
private def wickLin (W : ℕ) (x w : Fin W → ℂ) : (Fin 1 × Fin W × Fin W → ℝ) →L[ℝ] ℂ :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin 1 × Fin W × Fin W → ℝ) →L[ℝ] ℝ).smulRight
    (wickCoef W x w i)

private lemma wickLin_single (W : ℕ) (x w : Fin W → ℂ) (k : Fin 1 × Fin W × Fin W) :
    wickLin W x w (Pi.single k 1) = wickCoef W x w k := by
  simp [wickLin, Pi.single_apply]

private lemma wickLin_eq (W : ℕ) (x w : Fin W → ℂ) (ω : Fin 1 × Fin W × Fin W → ℝ) :
    star x ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ w) = wickLin W x w ω := by
  rw [wick_clm_expand, gueBlock_eq_sum_hermBasis]
  simp only [wickLin_single, wickCoef]
  conv_rhs => rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  rw [Matrix.smul_mulVec, Matrix.sum_mulVec, dotProduct_smul, dotProduct_sum]
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Fin.isValue]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The pair weight: `Σ_k (coefficient of ℓ_0)_k (coefficient of ℓ_j)_k` is the covariance
`W⁻¹ (x_0* w_j)(x_j* w_0)` of (1.2) [eq:covariance]. -/
private lemma wickCoef_pair (W : ℕ) (x₀ w₀ x w : Fin W → ℂ) :
    ∑ k, wickCoef W x₀ w₀ k * wickCoef W x w k =
      (W : ℂ)⁻¹ * (star x₀ ⬝ᵥ w) * (star x ⬝ᵥ w₀) := by
  have e1 : ∀ (x w : Fin W → ℂ) (k : Fin W × Fin W), star x ⬝ᵥ (hermBasis W k *ᵥ w) =
      ∑ u : Fin W × Fin W, (star x u.1 * w u.2) * hermBasis W k u.1 u.2 := by
    intro x w k
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
  have hs : ((Real.sqrt W : ℝ) : ℂ)⁻¹ * ((Real.sqrt W : ℝ) : ℂ)⁻¹ = (W : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg W)]
    simp
  have h1 : ∀ k : Fin W × Fin W, wickCoef W x₀ w₀ (0, k) * wickCoef W x w (0, k) =
      (W : ℂ)⁻¹ * ∑ u : Fin W × Fin W, ∑ v : Fin W × Fin W,
        ((star x₀ u.1 * w₀ u.2) * (star x v.1 * w v.2)) *
          (hermBasis W k u.1 u.2 * hermBasis W k v.1 v.2) := by
    intro k
    simp only [wickCoef, e1]
    rw [mul_mul_mul_comm, hs, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  simp only [h1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∀ y : Fin W × Fin W, ∑ k : Fin W × Fin W, ∑ v : Fin W × Fin W,
      star x₀ y.1 * w₀ y.2 * (star x v.1 * w v.2) *
        (hermBasis W k y.1 y.2 * hermBasis W k v.1 v.2) =
      (star x₀ y.1 * w y.1) * (star x y.2 * w₀ y.2) := by
    intro y
    rw [Finset.sum_comm]
    have h3 : ∀ v : Fin W × Fin W, ∑ k : Fin W × Fin W,
        star x₀ y.1 * w₀ y.2 * (star x v.1 * w v.2) *
          (hermBasis W k y.1 y.2 * hermBasis W k v.1 v.2) =
        if v = (y.2, y.1) then star x₀ y.1 * w₀ y.2 * (star x v.1 * w v.2) else 0 := by
      intro v
      rw [← Finset.mul_sum, sum_hermBasis_apply_mul_apply]
      by_cases hv : v = (y.2, y.1)
      · subst hv; simp
      · have : ¬ (y.1 = v.2 ∧ y.2 = v.1) := fun h => hv (Prod.ext h.2.symm h.1.symm)
        simp [hv, this]
    simp only [h3, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  simp only [h2]
  rw [Fintype.sum_prod_type]
  rw [mul_assoc, dotProduct, dotProduct, Finset.sum_mul_sum]

/-- Wick recursion for one GUE block of (1.2) [eq:covariance]:
`𝔼[(x_0* V w_0) ∏_{i∈s} (x_i* V w_i)]
= Σ_{j∈s} W⁻¹ (x_0* w_j)(x_j* w_0) 𝔼[∏_{i∈s∖{j}} (x_i* V w_i)]`. -/
theorem integral_gueLin_mul_prod (W : ℕ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x w : ι → Fin W → ℂ) (x₀ w₀ : Fin W → ℂ) :
    ∫ ω, (star x₀ ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ w₀)) *
        ∏ i ∈ s, (star (x i) ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ w i)) ∂(μ W 1) =
      ∑ j ∈ s, (W : ℂ)⁻¹ * (star x₀ ⬝ᵥ w j) * (star (x j) ⬝ᵥ w₀) *
        ∫ ω, ∏ i ∈ s.erase j, (star (x i) ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ w i)) ∂(μ W 1) := by
  simp only [wickLin_eq]
  rw [μ_eq_stdGauss, wick_clm_prod s (fun i => wickLin W (x i) (w i)) (wickLin W x₀ w₀)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [wickLin_single, wickCoef_pair]

end LSBA
