import LSBA.Spectral.BorderInverse

/-!
# Measurability of inverse-image overlap events

The set of `(Γ, L, M, K)` such that `‖M x‖² ≤ K ‖x‖²` for every `x` with `L Γ x = 0` is Borel.
With `L = 1 - P_U` for an orthogonal projection `P_U`, the condition `L Γ x = 0` says
`Γ x ∈ ran P_U`, so this is the good event of (9.42) [us:eq:relative], (9.50) [us:eq:absolute] and
(9.52) [nc:eq:compression] as a function of the matrix `Γ = V - E - B` and of the data. Its
complement is a countable union of projections of closed sets along the compact unit sphere.
-/

open MeasureTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The Euclidean norm `l2Norm` is continuous on `ι → ℂ`. -/
private theorem InvImageMeas_continuous_l2Norm {ι : Type*} [Fintype ι] :
    Continuous (l2Norm : (ι → ℂ) → ℝ) := by
  unfold l2Norm
  fun_prop

/-- Scaling a vector by a nonnegative real scales `l2Norm` by the same factor. -/
private theorem InvImageMeas_l2Norm_smul {ι : Type*} [Fintype ι] {a : ℝ} (ha : 0 ≤ a)
    (z : ι → ℂ) : l2Norm ((a : ℂ) • z) = a * l2Norm z := by
  unfold l2Norm
  have h : ∀ i, ‖((a : ℂ) • z) i‖ ^ 2 = a ^ 2 * ‖z i‖ ^ 2 := by
    intro i
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
  simp_rw [h, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

/-- The inverse-image overlap event is Borel in `(Γ, L, M, K)`: the set where
`‖M x‖² ≤ K ‖x‖²` for every `x` with `L Γ x = 0`. -/
theorem measurableSet_invImage_le {n m k : Type*} [Fintype n] [Fintype m] [Fintype k] :
    MeasurableSet {p : Matrix n n ℂ × Matrix m n ℂ × Matrix k n ℂ × ℝ |
      ∀ x : n → ℂ, p.2.1 *ᵥ (p.1 *ᵥ x) = 0 →
        l2Norm (p.2.2.1 *ᵥ x) ^ 2 ≤ p.2.2.2 * l2Norm x ^ 2} := by
  -- the Borel structure of the product is the one of its (second countable) topology
  have hsc1 : SecondCountableTopology (Matrix n n ℂ) :=
    inferInstanceAs (SecondCountableTopology (n → n → ℂ))
  have hsc2 : SecondCountableTopology (Matrix m n ℂ) :=
    inferInstanceAs (SecondCountableTopology (m → n → ℂ))
  have hsc3 : SecondCountableTopology (Matrix k n ℂ) :=
    inferInstanceAs (SecondCountableTopology (k → n → ℂ))
  -- the closed pieces of the complement: witnesses on the unit sphere with a margin `1/(j+1)`
  set sph : Set (n → ℂ) := Metric.sphere (0 : n → ℂ) 1 with hsph
  have : CompactSpace sph := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : n → ℂ) 1)
  let T : ℕ → Set (Matrix n n ℂ × Matrix m n ℂ × Matrix k n ℂ × ℝ) := fun j =>
    {p | ∃ y ∈ sph, p.2.1 *ᵥ (p.1 *ᵥ y) = 0 ∧
      p.2.2.2 * l2Norm y ^ 2 + 1 / ((j : ℝ) + 1) ≤ l2Norm (p.2.2.1 *ᵥ y) ^ 2}
  have hT : ∀ j, IsClosed (T j) := by
    intro j
    let C : Set ((Matrix n n ℂ × Matrix m n ℂ × Matrix k n ℂ × ℝ) × sph) :=
      {q | q.1.2.1 *ᵥ (q.1.1 *ᵥ (q.2 : n → ℂ)) = 0} ∩
        {q | q.1.2.2.2 * l2Norm (q.2 : n → ℂ) ^ 2 + 1 / ((j : ℝ) + 1) ≤
          l2Norm (q.1.2.2.1 *ᵥ (q.2 : n → ℂ)) ^ 2}
    have hC : IsClosed C := by
      have hy : Continuous fun q : (Matrix n n ℂ × Matrix m n ℂ × Matrix k n ℂ × ℝ) × sph =>
          (q.2 : n → ℂ) := continuous_subtype_val.comp continuous_snd
      have hG : Continuous fun q : (Matrix n n ℂ × Matrix m n ℂ × Matrix k n ℂ × ℝ) × sph =>
          q.1.1 := by fun_prop
      have hL : Continuous fun q : (Matrix n n ℂ × Matrix m n ℂ × Matrix k n ℂ × ℝ) × sph =>
          q.1.2.1 := by fun_prop
      have hM : Continuous fun q : (Matrix n n ℂ × Matrix m n ℂ × Matrix k n ℂ × ℝ) × sph =>
          q.1.2.2.1 := by fun_prop
      have hK : Continuous fun q : (Matrix n n ℂ × Matrix m n ℂ × Matrix k n ℂ × ℝ) × sph =>
          q.1.2.2.2 := by fun_prop
      have hN := InvImageMeas_continuous_l2Norm (ι := n)
      have hN' := InvImageMeas_continuous_l2Norm (ι := k)
      refine IsClosed.inter ?_ ?_
      · exact isClosed_eq (hL.matrix_mulVec (hG.matrix_mulVec hy))
          (continuous_const : Continuous fun _ : (Matrix n n ℂ × Matrix m n ℂ × Matrix k n ℂ × ℝ)
            × sph => (0 : m → ℂ))
      · exact isClosed_le ((hK.mul ((hN.comp hy).pow 2)).add continuous_const)
          ((hN'.comp (hM.matrix_mulVec hy)).pow 2)
    have himg : T j = Prod.fst '' C := by
      ext p
      constructor
      · rintro ⟨y, hy, h1, h2⟩
        exact ⟨(p, ⟨y, hy⟩), ⟨h1, h2⟩, rfl⟩
      · rintro ⟨⟨p', y⟩, ⟨h1, h2⟩, rfl⟩
        exact ⟨y.1, y.2, h1, h2⟩
    rw [himg]
    exact isClosedMap_fst_of_compactSpace _ hC
  have hS : {p : Matrix n n ℂ × Matrix m n ℂ × Matrix k n ℂ × ℝ |
      ∀ x : n → ℂ, p.2.1 *ᵥ (p.1 *ᵥ x) = 0 →
        l2Norm (p.2.2.1 *ᵥ x) ^ 2 ≤ p.2.2.2 * l2Norm x ^ 2} = (⋃ j, T j)ᶜ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · intro h j ⟨y, hy, h1, h2⟩
      have := h y h1
      have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
    · intro h x hx
      by_contra hlt
      rw [not_le] at hlt
      -- rescale a witness `x` to the unit sphere
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp [l2Norm] at hlt
      have hc : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      set c : ℝ := ‖x‖ with hcdef
      have hysph : ((c⁻¹ : ℝ) : ℂ) • x ∈ sph := by
        rw [hsph, mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm]
        exact inv_mul_cancel₀ hc.ne'
      have hcpos : 0 < c⁻¹ ^ 2 := by positivity
      -- the margin of the rescaled witness
      have hd : 0 < l2Norm (p.2.2.1 *ᵥ x) ^ 2 - p.2.2.2 * l2Norm x ^ 2 := by linarith
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt
        (mul_pos hcpos hd)
      refine h j ⟨((c⁻¹ : ℝ) : ℂ) • x, hysph, ?_, ?_⟩
      · rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hx, smul_zero]
      · rw [Matrix.mulVec_smul, InvImageMeas_l2Norm_smul (inv_nonneg.mpr hc.le),
          InvImageMeas_l2Norm_smul (inv_nonneg.mpr hc.le)]
        nlinarith
  rw [hS]
  exact (MeasurableSet.iUnion fun j => (hT j).measurableSet).compl

end LSBA
