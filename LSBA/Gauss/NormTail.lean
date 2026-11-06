import LSBA.Gauss.Net
import LSBA.Gauss.StdGauss
import LSBA.Model.Basic

/-!
# A crude operator-norm tail for one GUE block

`P(‖V_a‖ > 16) ≤ e^{-W/2}` for `W ≥ 32`, for one normalized GUE block (1.2) [eq:covariance], from a
net on the sphere and a chi-square tail.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The χ² tail for the sum of squares over a subset `S` of the coordinates of `ℝ^ι`. -/
private lemma normTail_marginal {ι : Type*} [Fintype ι] (S : Finset ι) :
    stdGauss ι {x | 2 * (S.card : ℝ) < ∑ i ∈ S, x i ^ 2} ≤
      ENNReal.ofReal (Real.exp (-(S.card : ℝ) / 8)) := by
  have he := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => gaussianReal 0 1) (· ∈ S)
  set C : Set ({i // i ∈ S} → ℝ) := {y | 2 * (S.card : ℝ) < ∑ i, y i ^ 2} with hCdef
  have hC : MeasurableSet C := by
    refine measurableSet_lt measurable_const ?_
    fun_prop
  have hpre : {x : ι → ℝ | 2 * (S.card : ℝ) < ∑ i ∈ S, x i ^ 2} =
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ∈ S)) ⁻¹' (C ×ˢ Set.univ) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, hCdef]
    rw [← Finset.sum_coe_sort S]
    rfl
  rw [hpre]
  have h1 := he.measure_preimage (hC.prod MeasurableSet.univ).nullMeasurableSet
  have h2 : stdGauss ι ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ∈ S)) ⁻¹'
      (C ×ˢ Set.univ)) = _ := h1
  rw [h2, Measure.prod_prod, measure_univ, mul_one]
  have h3 := chiSq_tail {i // i ∈ S}
  rw [Fintype.card_coe] at h3
  convert h3 using 2
  unfold stdGauss
  congr
  exact Subsingleton.elim _ _

/-- A real-linear map `T` from `ℝ^ι` to a space of dimension at most `m ≤ |ι|`, with `ν ∘ T`
bounded by the squared Euclidean norm, has `ν (T ω) > 2m` with probability at most `e^{-m/8}`
under the standard Gaussian: `T` factors through the coordinates of a rotated frame, of which only
`m` survive, and the χ² tail applies to those. -/
private lemma normTail_aux {ι G : Type*} [Fintype ι] [AddCommGroup G] [Module ℝ G]
    [FiniteDimensional ℝ G] (T : EuclideanSpace ℝ ι →ₗ[ℝ] G) (ν : G → ℝ) {m : ℕ}
    (hG : Module.finrank ℝ G ≤ m) (hm : m ≤ Fintype.card ι) (hν : ∀ x, ν (T x) ≤ ‖x‖ ^ 2) :
    stdGauss ι {ω | 2 * (m : ℝ) < ν (T (WithLp.toLp 2 ω))} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) / 8)) := by
  obtain ⟨S, -, hScard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (n := m) (by simpa using hm)
  obtain ⟨K, hK⟩ : ∃ K : Submodule ℝ (EuclideanSpace ℝ ι), K = LinearMap.ker T := ⟨_, rfl⟩
  have hrank : Fintype.card ι ≤ Module.finrank ℝ K + m := by
    have h1 := LinearMap.finrank_range_add_finrank_ker T
    have h2 : Module.finrank ℝ (LinearMap.range T) ≤ Module.finrank ℝ G := Submodule.finrank_le _
    rw [finrank_euclideanSpace, ← hK] at h1
    omega
  have hcardle : Fintype.card {j // j ∉ S} ≤ Fintype.card (Fin (Module.finrank ℝ K)) := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hScard, Fintype.card_fin]
    omega
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hcardle
  set bK := stdOrthonormalBasis ℝ K with hbK
  set u : {j // j ∉ S} → EuclideanSpace ℝ ι := fun j => ((bK (φ j) : K) : EuclideanSpace ℝ ι)
    with hu
  have huon : Orthonormal ℝ u := by
    have h1 : Orthonormal ℝ (K.subtypeₗᵢ ∘ bK) :=
      K.subtypeₗᵢ.orthonormal_comp_iff.mpr bK.orthonormal
    exact h1.comp φ φ.injective
  set v : ι → EuclideanSpace ℝ ι := fun j => if h : j ∉ S then u ⟨j, h⟩ else 0 with hv
  have hvu : (({j | j ∉ S} : Set ι)).domRestrict v = u := by
    funext j
    have hj : (j : ι) ∉ S := j.2
    change v j = u j
    simp [hv, hj]
  have hvon : Orthonormal ℝ ((({j | j ∉ S} : Set ι)).domRestrict v) := by
    rw [hvu]; exact huon
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp) hvon
  have hbK0 : ∀ j, j ∉ S → T (b j) = 0 := by
    intro j hj
    rw [hb j hj]
    have hmem : ((bK (φ ⟨j, hj⟩) : K) : EuclideanSpace ℝ ι) ∈ LinearMap.ker T := hK ▸ (bK _).2
    simpa [hv, hj, hu] using hmem
  have key : ∀ x : EuclideanSpace ℝ ι, ν (T x) ≤ ∑ j ∈ S, (b.repr x j) ^ 2 := by
    intro x
    have hx : x = b.repr.symm (b.repr x) := (b.repr.symm_apply_apply x).symm
    have hz : x - b.repr.symm (WithLp.toLp 2 (fun j => if j ∈ S then b.repr x j else 0)) =
        b.repr.symm (WithLp.toLp 2 (fun j => if j ∈ S then 0 else b.repr x j)) := by
      calc x - b.repr.symm (WithLp.toLp 2 (fun j => if j ∈ S then b.repr x j else 0))
          = b.repr.symm (b.repr x) -
            b.repr.symm (WithLp.toLp 2 (fun j => if j ∈ S then b.repr x j else 0)) := by
            rw [← hx]
        _ = _ := by
            rw [← map_sub]
            congr 1
            ext j
            simp only [PiLp.sub_apply]
            split_ifs <;> simp
    have hz' : T (x - b.repr.symm (WithLp.toLp 2 (fun j => if j ∈ S then b.repr x j else 0))) =
        0 := by
      rw [hz, ← b.sum_repr_symm, map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul]
      by_cases hj : j ∈ S
      · simp [hj]
      · rw [hbK0 j hj]; simp
    rw [map_sub, sub_eq_zero] at hz'
    rw [hz']
    refine (hν _).trans ?_
    rw [LinearIsometryEquiv.norm_map, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    refine le_of_eq ?_
    calc ∑ i, (if i ∈ S then b.repr x i else 0) ^ 2
        = ∑ i, (if i ∈ S then b.repr x i ^ 2 else 0) :=
          Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
      _ = ∑ i ∈ S, b.repr x i ^ 2 := by rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsub : {ω : ι → ℝ | 2 * (m : ℝ) < ν (T (WithLp.toLp 2 ω))} ⊆
      (fun ω : ι → ℝ => (b.repr (WithLp.toLp 2 ω)).ofLp) ⁻¹'
        {x | 2 * (S.card : ℝ) < ∑ i ∈ S, x i ^ 2} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hω ⊢
    rw [hScard]
    exact hω.trans_le (key _)
  have hmp := measurePreserving_stdGauss_linearIsometry b.repr
  have hmeas : MeasurableSet {x : ι → ℝ | 2 * (S.card : ℝ) < ∑ i ∈ S, x i ^ 2} := by
    refine measurableSet_lt measurable_const ?_
    fun_prop
  calc stdGauss ι {ω : ι → ℝ | 2 * (m : ℝ) < ν (T (WithLp.toLp 2 ω))}
      ≤ stdGauss ι ((fun ω : ι → ℝ => (b.repr (WithLp.toLp 2 ω)).ofLp) ⁻¹'
        {x | 2 * (S.card : ℝ) < ∑ i ∈ S, x i ^ 2}) := measure_mono hsub
    _ = stdGauss ι {x | 2 * (S.card : ℝ) < ∑ i ∈ S, x i ^ 2} :=
        hmp.measure_preimage hmeas.nullMeasurableSet
    _ ≤ ENNReal.ofReal (Real.exp (-(S.card : ℝ) / 8)) := normTail_marginal S
    _ = ENNReal.ofReal (Real.exp (-(m : ℝ) / 8)) := by rw [hScard]

/-- `gueBlock` is additive in the sample. -/
private lemma normTail_gueBlock_add (W L : ℕ) (x y : Ω W L) (a : Fin L) :
    gueBlock W L (x + y) a = gueBlock W L x a + gueBlock W L y a := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

/-- `gueBlock` is homogeneous in the sample. -/
private lemma normTail_gueBlock_smul (W L : ℕ) (c : ℝ) (x : Ω W L) (a : Fin L) :
    gueBlock W L (c • x) a = (c : ℂ) • gueBlock W L x a := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

/-- A squared entry of the block: `W |V_{αβ}|² = (ω_{αβ}² + ω_{βα}²)/2`. -/
private lemma normTail_entry_sq {W L : ℕ} (hW : 0 < W) (ω : Ω W L) (a : Fin L) (α β : Fin W) :
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

/-- The squared Frobenius norm of the block `a`, scaled by `W`, is the squared Euclidean norm of its
coordinates. -/
private lemma normTail_frob {W L : ℕ} (hW : 0 < W) (ω : Ω W L) (a : Fin L) :
    ∑ α, ∑ β, (W : ℝ) * ‖gueBlock W L ω a α β‖ ^ 2 = ∑ α, ∑ β, ω (a, α, β) ^ 2 := by
  simp_rw [normTail_entry_sq hW]
  have hswap : ∑ α : Fin W, ∑ β : Fin W, ω (a, β, α) ^ 2 =
      ∑ α : Fin W, ∑ β : Fin W, ω (a, α, β) ^ 2 := Finset.sum_comm
  simp_rw [add_div, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [hswap]
  ring

/-- Cauchy–Schwarz for one row of a matrix-vector product. -/
private lemma normTail_row_sq {W : ℕ} (G : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) (α : Fin W) :
    ‖(G *ᵥ v) α‖ ^ 2 ≤ (∑ β, ‖G α β‖ ^ 2) * ∑ β, ‖v β‖ ^ 2 := by
  have h1 : ‖(G *ᵥ v) α‖ ≤ ∑ β, ‖G α β‖ * ‖v β‖ := by
    have h0 : (G *ᵥ v) α = ∑ β, G α β * v β := rfl
    rw [h0]
    refine (norm_sum_le _ _).trans ?_
    simp
  calc ‖(G *ᵥ v) α‖ ^ 2 ≤ (∑ β, ‖G α β‖ * ‖v β‖) ^ 2 := by gcongr
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- For `∑ ‖v_i‖² ≤ 1`, `W ‖V_a v‖² ≤ ∑_p ω_p²`. -/
private lemma normTail_apply_sq_le {W L : ℕ} (hW : 0 < W) (ω : Ω W L) (a : Fin L) (v : Fin W → ℂ)
    (hv : ∑ i, ‖v i‖ ^ 2 ≤ 1) :
    (W : ℝ) * ∑ α, ‖(gueBlock W L ω a *ᵥ v) α‖ ^ 2 ≤ ∑ p : Fin L × Fin W × Fin W, ω p ^ 2 := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  calc (W : ℝ) * ∑ α, ‖(gueBlock W L ω a *ᵥ v) α‖ ^ 2
      ≤ (W : ℝ) * ∑ α, ((∑ β, ‖gueBlock W L ω a α β‖ ^ 2) * 1) := by
        gcongr with α
        exact (normTail_row_sq _ v α).trans
          (mul_le_mul_of_nonneg_left hv (Finset.sum_nonneg fun _ _ => by positivity))
    _ = ∑ α, ∑ β, (W : ℝ) * ‖gueBlock W L ω a α β‖ ^ 2 := by
        simp only [mul_one, Finset.mul_sum]
    _ = ∑ α, ∑ β, ω (a, α, β) ^ 2 := normTail_frob hW ω a
    _ ≤ ∑ p : Fin L × Fin W × Fin W, ω p ^ 2 := by
        rw [Fintype.sum_prod_type]
        refine le_trans ?_ (Finset.single_le_sum (f := fun a' : Fin L =>
          ∑ x : Fin W × Fin W, ω (a', x) ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ a))
        rw [Fintype.sum_prod_type]

/-- The real-linear map `ω ↦ V_a v` from the coordinates of the sample. -/
private def normTailMap (W L : ℕ) (a : Fin L) (v : Fin W → ℂ) :
    EuclideanSpace ℝ (Fin L × Fin W × Fin W) →ₗ[ℝ] (Fin W → ℂ) where
  toFun x := gueBlock W L x.ofLp a *ᵥ v
  map_add' x y := by
    simp only [WithLp.ofLp_add, normTail_gueBlock_add, Matrix.add_mulVec]
  map_smul' c x := by
    simp only [WithLp.ofLp_smul, normTail_gueBlock_smul, RingHom.id_apply]
    ext α
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- Crude operator-norm tail of one normalized GUE block (1.2) [eq:covariance]: for `W ≥ 32`,
`P(‖V_a‖ > 16) ≤ e^{-W/2}`. -/
theorem gueBlock_norm_tail {W L : ℕ} (hW : 32 ≤ W) (a : Fin L) :
    (μ W L) {ω | 16 < ‖gueBlock W L ω a‖} ≤ ENNReal.ofReal (Real.exp (-(W : ℝ) / 2)) := by
  have hW0 : 0 < W := by omega
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  obtain ⟨N, hNcard, hNball, hNnet⟩ := exists_half_net (Fin W)
  have hcard : 32 * W ≤ Fintype.card (Fin L × Fin W × Fin W) := by
    have hL : 1 ≤ L := Fin.pos a
    simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith
  have hone : ∀ v ∈ N, (μ W L) {ω | 2 * ((32 * W : ℕ) : ℝ) <
      (W : ℝ) * ∑ α, ‖(gueBlock W L ω a *ᵥ v) α‖ ^ 2} ≤
        ENNReal.ofReal (Real.exp (-((32 * W : ℕ) : ℝ) / 8)) := by
    intro v hv
    have hG : Module.finrank ℝ (Fin W → ℂ) ≤ 32 * W := by
      rw [Module.finrank_pi_fintype]
      simp
      omega
    exact normTail_aux (normTailMap W L a v) (fun g => (W : ℝ) * ∑ α, ‖g α‖ ^ 2) hG hcard
      (fun x => by
        rw [EuclideanSpace.real_norm_sq_eq]
        exact normTail_apply_sq_le hW0 x.ofLp a v (hNball v hv))
  have hsub : {ω | 16 < ‖gueBlock W L ω a‖} ⊆ ⋃ v ∈ N, {ω | 2 * ((32 * W : ℕ) : ℝ) <
      (W : ℝ) * ∑ α, ‖(gueBlock W L ω a *ᵥ v) α‖ ^ 2} := by
    intro ω hω
    obtain ⟨v, hv, hle⟩ := hNnet (gueBlock W L ω a)
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨v, hv, ?_⟩
    have h8 : 8 < Real.sqrt (∑ α, ‖(gueBlock W L ω a *ᵥ v) α‖ ^ 2) := by
      simp only [Set.mem_ofPred_eq] at hω
      linarith
    have h64 : 64 < ∑ α, ‖(gueBlock W L ω a *ᵥ v) α‖ ^ 2 := by
      have := (Real.lt_sqrt (by norm_num)).mp h8
      linarith
    push_cast
    nlinarith
  have hexp : (5 : ℝ) ^ (2 * W) * Real.exp (-((32 * W : ℕ) : ℝ) / 8) ≤ Real.exp (-(W : ℝ) / 2) := by
    have h25 : (5 : ℝ) ^ (2 * W) = 25 ^ W := by
      rw [pow_mul]; norm_num
    have hlog : (25 : ℝ) ≤ Real.exp (7 / 2) := by
      have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by
        have := Real.exp_one_gt_d9
        linarith
      have h2 : (1.5 : ℝ) ≤ Real.exp (1 / 2) := by
        have := Real.add_one_le_exp (1 / 2 : ℝ)
        linarith
      have h3 : Real.exp (7 / 2) = Real.exp 1 ^ 3 * Real.exp (1 / 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      rw [h3]
      have h4 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
      nlinarith [Real.exp_pos 1, Real.exp_pos (1 / 2)]
    calc (5 : ℝ) ^ (2 * W) * Real.exp (-((32 * W : ℕ) : ℝ) / 8)
        = 25 ^ W * Real.exp (-(4 * W : ℝ)) := by
          rw [h25]; congr 2; push_cast; ring
      _ ≤ Real.exp (7 / 2) ^ W * Real.exp (-(4 * W : ℝ)) := by gcongr
      _ = Real.exp (-(W : ℝ) / 2) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  calc (μ W L) {ω | 16 < ‖gueBlock W L ω a‖}
      ≤ (μ W L) (⋃ v ∈ N, {ω | 2 * ((32 * W : ℕ) : ℝ) <
          (W : ℝ) * ∑ α, ‖(gueBlock W L ω a *ᵥ v) α‖ ^ 2}) := measure_mono hsub
    _ ≤ ∑ v ∈ N, (μ W L) {ω | 2 * ((32 * W : ℕ) : ℝ) <
          (W : ℝ) * ∑ α, ‖(gueBlock W L ω a *ᵥ v) α‖ ^ 2} := measure_biUnion_finset_le _ _
    _ ≤ ∑ v ∈ N, ENNReal.ofReal (Real.exp (-((32 * W : ℕ) : ℝ) / 8)) :=
        Finset.sum_le_sum hone
    _ = N.card * ENNReal.ofReal (Real.exp (-((32 * W : ℕ) : ℝ) / 8)) := by simp
    _ ≤ ((5 ^ (2 * W) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-((32 * W : ℕ) : ℝ) / 8)) := by
        gcongr
        simpa using hNcard
    _ = ENNReal.ofReal ((5 : ℝ) ^ (2 * W) * Real.exp (-((32 * W : ℕ) : ℝ) / 8)) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← ENNReal.ofReal_natCast]
        push_cast
        rfl
    _ ≤ ENNReal.ofReal (Real.exp (-(W : ℝ) / 2)) := ENNReal.ofReal_le_ofReal hexp

end LSBA
