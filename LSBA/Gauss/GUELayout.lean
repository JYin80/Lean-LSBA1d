import LSBA.Gauss.GUELaw

/-!
# Orthonormal linear layouts of GUE inputs

For `n` independent GUE inputs `V` with the covariance (1.2) [eq:covariance] and a real
`m × n` matrix `d` with `d dᵀ = I`, the blocks `G_j = Σ_i d_{ji} V_i` are `m` independent GUE
blocks: in the standard coordinates the map `V ↦ G` preserves the Gaussian law. The layout of
disjoint normalized differences `G_j = 2^{-1/2} (V_{k_j} - V_{i_j})` is orthonormal. These are
the inputs of the cutoff in Lemma G.4 [lem:c-gaussian].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The linear layout `G_j = Σ_i d_{ji} V_i` of the inputs `V` (Lemma G.4 [lem:c-gaussian]). -/
def layoutBlocks {m n W : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    (V : Fin n → Matrix (Fin W) (Fin W) ℂ) : Fin m → Matrix (Fin W) (Fin W) ℂ :=
  fun j => ∑ i, ((d j i : ℝ) : ℂ) • V i

/-- The layout of disjoint normalized differences `G_j = 2^{-1/2} (V_{k_j} - V_{i_j})`
(Lemma 10.1 [lem:c-gaussian-lift], (10.14) [eq:c-main-coercivity]). -/
def pairLayout {m n : ℕ} (i k : Fin m → Fin n) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun j l =>
    (if l = k j then (Real.sqrt 2)⁻¹ else 0) - (if l = i j then (Real.sqrt 2)⁻¹ else 0)

/-- Disjoint pairs give an orthonormal layout: `d dᵀ = I`. -/
theorem pairLayout_mul_transpose {m n : ℕ} {i k : Fin m → Fin n} (hi : Function.Injective i)
    (hk : Function.Injective k) (hik : ∀ a b, i a ≠ k b) :
    pairLayout i k * (pairLayout i k)ᵀ = 1 := by
  have hs : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pairLayout, Matrix.of_apply, sub_mul,
    mul_sub, Finset.sum_sub_distrib, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.one_apply]
  have h1 : ¬ k b = i a := fun h => hik a b h.symm
  have h2 : ¬ i b = k a := hik b a
  by_cases hab : a = b
  · subst hab
    simp only [h1, h2, ite_true, ite_false, hs, sub_zero]
    norm_num
  · have h3 : ¬ k b = k a := fun h => hab (hk h).symm
    have h4 : ¬ i b = i a := fun h => hab (hi h).symm
    simp [h1, h2, h3, h4, hab]

/-- The pair layout gives `G_j = 2^{-1/2} (V_{k_j} - V_{i_j})`. -/
theorem layoutBlocks_pairLayout {m n W : ℕ} {i k : Fin m → Fin n} (hik : ∀ a b, i a ≠ k b)
    (V : Fin n → Matrix (Fin W) (Fin W) ℂ) (j : Fin m) :
    layoutBlocks (pairLayout i k) V j = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (V (k j) - V (i j)) := by
  have _ := hik
  simp only [layoutBlocks, pairLayout, Matrix.of_apply, Complex.ofReal_sub, sub_smul,
    Finset.sum_sub_distrib, apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_zero, ite_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_sub]

/-- An orthonormal layout `d dᵀ = I` maps `n` GUE inputs to `m` independent GUE blocks of
(1.2) [eq:covariance]: in the standard coordinates `V ↦ G = d V` preserves the Gaussian law. -/
theorem measurePreserving_layout {m n W : ℕ} {d : Matrix (Fin m) (Fin n) ℝ} (hd : d * dᵀ = 1) :
    MeasurePreserving (fun ω => gueCoord W m (layoutBlocks d (gueBlock W n ω))) (μ W n)
      (μ W m) := by
  have hcoord : ∀ (ω : Ω W n) (p : Fin m × Fin W × Fin W),
      gueCoord W m (layoutBlocks d (gueBlock W n ω)) p = ∑ i, d p.1 i * ω (i, p.2) := by
    intro ω p
    have h := gueCoord_gueBlock W n ω
    obtain ⟨j, α, β⟩ := p
    simp only [gueCoord, layoutBlocks, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.re_sum, Complex.im_sum, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    conv_rhs => rw [← h]
    simp only [gueCoord]
    split_ifs <;> simp only [Finset.mul_sum] <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> ring
  have hres : ∀ {κ ι : Type} [Fintype κ] [Fintype ι] (f : κ → ι), Function.Injective f →
      MeasurePreserving (fun ω : ι → ℝ => fun k => ω (f k)) (stdGauss ι) (stdGauss κ) := by
    intro κ ι _ _ f hf
    have hmeas : Measurable (fun ω : ι → ℝ => fun k => ω (f k)) :=
      measurable_pi_iff.mpr fun k => measurable_pi_apply (f k)
    refine ⟨hmeas, (Measure.pi_eq fun s hs => ?_).symm⟩
    let t : ι → Set ℝ := fun i => if h : ∃ k, f k = i then s h.choose else Set.univ
    have htf : ∀ k, t (f k) = s k := by
      intro k
      have h : ∃ k', f k' = f k := ⟨k, rfl⟩
      simp only [t, h, ↓reduceDIte]
      rw [hf h.choose_spec]
    have ht : (fun ω : ι → ℝ => fun k => ω (f k)) ⁻¹' Set.univ.pi s = Set.univ.pi t := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      constructor
      · intro hω i
        by_cases h : ∃ k, f k = i
        · simp only [t, h, ↓reduceDIte]
          have := hω h.choose
          rwa [h.choose_spec] at this
        · simp [t, h]
      · intro hω k
        have := hω (f k)
        rwa [htf] at this
    rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), ht, stdGauss, Measure.pi_pi]
    rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image f)), Finset.prod_image
      (fun a _ b _ h => hf h)]
    · simp only [htf]
    · intro i _ hi
      have h : ¬ ∃ k, f k = i := fun ⟨k, hk⟩ => hi (Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩)
      simp [t, h]
  let u : Fin m → EuclideanSpace ℝ (Fin n) := fun j => WithLp.toLp 2 (d j)
  have hu : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    intro a b
    have h := congrFun (congrFun hd a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    rw [← h]
    simp [u, PiLp.inner_apply, mul_comm]
  have hmn : m ≤ n := by simpa using hu.linearIndependent.fintype_card_le_finrank
  let σ : Fin m → Fin n := Fin.castLE hmn
  have hσ : Function.Injective σ := Fin.castLE_injective hmn
  let v : Fin n → EuclideanSpace ℝ (Fin n) := Function.extend σ u 0
  have hv : Orthonormal ℝ ((Set.range σ).domRestrict v) := by
    have h : (Set.range σ).domRestrict v = u ∘ (Equiv.ofInjective σ hσ).symm := by
      funext ⟨_, j, rfl⟩
      rw [Function.comp_apply, Equiv.ofInjective_symm_apply, Set.domRestrict_apply]
      exact hσ.extend_apply _ _ _
    rw [h]
    exact hu.comp _ (Equiv.injective _)
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hbσ : ∀ j, b (σ j) = u j := fun j => by
    rw [hb _ ⟨j, rfl⟩]
    exact hσ.extend_apply _ _ _
  let col : EuclideanSpace ℝ (Fin n × Fin W × Fin W) → Fin W × Fin W → EuclideanSpace ℝ (Fin n) :=
    fun z x => WithLp.toLp 2 fun i => z.ofLp (i, x)
  have hcol_add : ∀ z z' x, col (z + z') x = col z x + col z' x := by
    intro z z' x; ext i; simp [col]
  have hcol_smul : ∀ (c : ℝ) z x, col (c • z) x = c • col z x := by
    intro c z x; ext i; simp [col]
  let L : EuclideanSpace ℝ (Fin n × Fin W × Fin W) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n × Fin W × Fin W) :=
    { toFun := fun z => WithLp.toLp 2 fun p => b.repr (col z p.2) p.1
      map_add' := fun z z' => by ext p; simp [hcol_add]
      map_smul' := fun c z => by ext p; simp [hcol_smul]
      norm_map' := fun z => by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        congr 1
        simp only [Real.norm_eq_abs, sq_abs]
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        have h1 := b.repr.norm_map (col z x)
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h1
        simp only [Real.norm_eq_abs, sq_abs] at h1
        rw [Real.sqrt_inj (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h1
        simpa [col] using h1 }
  have hQ := measurePreserving_stdGauss_linearIsometry (L.toLinearIsometryEquiv rfl)
  have hR := hres (fun p : Fin m × Fin W × Fin W => ((σ p.1, p.2) : Fin n × Fin W × Fin W))
    (fun p q h => Prod.ext (hσ (Prod.ext_iff.1 h).1) (Prod.ext_iff.1 h).2)
  rw [μ_eq_stdGauss, μ_eq_stdGauss]
  convert hR.comp hQ using 1
  funext ω p
  rw [hcoord]
  simp [L, col, b.repr_apply_apply, hbσ, u, PiLp.inner_apply, mul_comm]

/-- The blocks of the layout sample are the layout blocks `G = d V`. -/
theorem gueBlock_gueCoord_layoutBlocks {m n W : ℕ} (d : Matrix (Fin m) (Fin n) ℝ) (ω : Ω W n) :
    gueBlock W m (gueCoord W m (layoutBlocks d (gueBlock W n ω))) =
      layoutBlocks d (gueBlock W n ω) := by
  refine gueBlock_gueCoord W m _ fun j => ?_
  unfold Matrix.IsHermitian layoutBlocks
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_smul, (gueBlock_isHermitian W n ω i).eq, Complex.star_def,
    Complex.conj_ofReal]

end LSBA
