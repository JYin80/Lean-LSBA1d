import LSBA.Spectral.EigMass
import LSBA.Spectral.Resolvent

/-!
# Crossings of the rank-one family

For Hermitian `K` and almost every energy `E`, at most one parameter `u` of the line
`K + u P_{{x}}` has `E` as an eigenvalue, and then with a one-dimensional kernel: the root sum of
(E.7) [uva:eq:coarea-audit] for this line is at most `1`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real `E` with `det (M - E) = 0` form a finite set. -/
private lemma rankOneCross_finite_det_zero (M : Matrix n n ℂ) :
    {E : ℝ | (M - (E : ℂ) • (1 : Matrix n n ℂ)).det = 0}.Finite := by
  have hne : M.charpoly ≠ 0 := M.charpoly_monic.ne_zero
  refine ((M.charpoly.roots.toFinset.finite_toSet).preimage
    Complex.ofReal_injective.injOn).subset ?_
  intro E hE
  have hE' : (M - (E : ℂ) • (1 : Matrix n n ℂ)).det = 0 := hE
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne,
    Polynomial.IsRoot.def, Matrix.eval_charpoly]
  have h : Matrix.scalar n (E : ℂ) - M = -(M - (E : ℂ) • (1 : Matrix n n ℂ)) := by
    rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [h, Matrix.det_neg, hE', mul_zero]

/-- `(K + u P_{{x}} - E) v = (K - E) v + u v_x e_x`. -/
private lemma rankOneCross_mulVec (K : Matrix n n ℂ) (x : n) (E u : ℝ) (v : n → ℂ) :
    (K + ((1 * u : ℝ) : ℂ) • coordProj ({x} : Finset n) - (E : ℂ) • (1 : Matrix n n ℂ)) *ᵥ v =
      (K - (E : ℂ) • (1 : Matrix n n ℂ)) *ᵥ v + (u : ℂ) • (Pi.single x (v x) : n → ℂ) := by
  have h1 : K + ((1 * u : ℝ) : ℂ) • coordProj ({x} : Finset n) - (E : ℂ) • (1 : Matrix n n ℂ) =
      (K - (E : ℂ) • (1 : Matrix n n ℂ)) + (u : ℂ) • coordProj ({x} : Finset n) := by
    rw [one_mul]
    abel
  rw [h1, Matrix.add_mulVec, Matrix.smul_mulVec]
  congr 2
  funext i
  by_cases hi : i = x
  · subst hi
    simp [coordProj, Matrix.mulVec_diagonal]
  · simp [coordProj, Matrix.mulVec_diagonal, hi]

/-- A function with values `≤ 1`, vanishing off one point, has sum `≤ 1` over any set. -/
private lemma rankOneCross_window_le {g : ℝ → ℝ≥0∞} {u₀ : ℝ} (hg1 : ∀ u, g u ≤ 1)
    (hz : ∀ u, u ≠ u₀ → g u = 0) (I : Set ℝ) : ∑' u : I, g u ≤ 1 := by
  by_cases hu : u₀ ∈ I
  · rw [tsum_eq_single (⟨u₀, hu⟩ : I)]
    · exact hg1 u₀
    · intro b hb
      exact hz b.1 (fun h => hb (Subtype.ext h))
  · have h0 : ∀ u : I, g u = 0 := fun u => hz u.1 (fun h => hu (h ▸ u.2))
    simp [h0]

/-- A function with values `≤ 1`, supported on at most one point which is not an integer, has
`Σ_ℓ Σ_{u ∈ [ℓ, ℓ+1]} g u ≤ 1`. -/
private lemma rankOneCross_tsum_le {g : ℝ → ℝ≥0∞} (hg1 : ∀ u, g u ≤ 1)
    (hsub : ∀ u₁ u₂, g u₁ ≠ 0 → g u₂ ≠ 0 → u₁ = u₂) (hint : ∀ m : ℤ, g m = 0) :
    ∑' ℓ : ℤ, ∑' u : Set.Icc (ℓ : ℝ) (ℓ + 1), g u ≤ 1 := by
  by_cases h : ∃ u₀, g u₀ ≠ 0
  · obtain ⟨u₀, hu₀⟩ := h
    have hz : ∀ u, u ≠ u₀ → g u = 0 := fun u hu => by
      by_contra hne
      exact hu (hsub u u₀ hne hu₀)
    have hfl : ∀ ℓ : ℤ, ℓ ≠ ⌊u₀⌋ → ∑' u : Set.Icc (ℓ : ℝ) (ℓ + 1), g u = 0 := by
      intro ℓ hℓ
      have h0 : ∀ u : Set.Icc (ℓ : ℝ) (ℓ + 1), g u = 0 := by
        intro u
        by_contra hne
        have hu : u.1 = u₀ := hsub _ _ hne hu₀
        have h1 : (ℓ : ℝ) ≤ u₀ := hu ▸ u.2.1
        have h2 : u₀ ≤ ℓ + 1 := hu ▸ u.2.2
        apply hℓ
        rw [eq_comm, Int.floor_eq_iff]
        refine ⟨h1, lt_of_le_of_ne h2 ?_⟩
        intro h3
        have h4 := hint (ℓ + 1)
        push_cast at h4
        rw [← h3] at h4
        exact hu₀ h4
      simp [h0]
    rw [tsum_eq_single ⌊u₀⌋ hfl]
    exact rankOneCross_window_le hg1 hz _
  · push Not at h
    simp [h]

/-- If `K - E` is invertible, every kernel of `K + u P_{{x}} - E` has dimension at most `1`. -/
private lemma rankOneCross_finrank_le {K : Matrix n n ℂ} (x : n) {E : ℝ}
    (hA : (K - (E : ℂ) • (1 : Matrix n n ℂ)).det ≠ 0) (u : ℝ) :
    Module.finrank ℂ (LinearMap.ker (Matrix.toLin' (K + ((1 * u : ℝ) : ℂ) •
      coordProj ({x} : Finset n) - (E : ℂ) • (1 : Matrix n n ℂ)))) ≤ 1 := by
  let f : LinearMap.ker (Matrix.toLin' (K + ((1 * u : ℝ) : ℂ) • coordProj ({x} : Finset n) -
      (E : ℂ) • (1 : Matrix n n ℂ))) →ₗ[ℂ] ℂ :=
    (LinearMap.proj x : (n → ℂ) →ₗ[ℂ] ℂ).comp (Submodule.subtype _)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hvx : v.1 x = 0 := hv
    have hmem : (K + ((1 * u : ℝ) : ℂ) • coordProj ({x} : Finset n) -
        (E : ℂ) • (1 : Matrix n n ℂ)) *ᵥ v.1 = 0 := by
      have := v.2
      rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
    rw [rankOneCross_mulVec, hvx] at hmem
    simp only [Pi.single_zero, smul_zero, add_zero] at hmem
    exact Subtype.ext (Matrix.eq_zero_of_mulVec_eq_zero hA hmem)
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

/-- A nonzero dimension of the kernel gives a nonzero kernel vector. -/
private lemma rankOneCross_exists_vec {M : Matrix n n ℂ}
    (h : (Module.finrank ℂ (LinearMap.ker (Matrix.toLin' M)) : ℝ≥0∞) ≠ 0) :
    ∃ v : n → ℂ, v ≠ 0 ∧ M *ᵥ v = 0 := by
  have h1 : Module.finrank ℂ (LinearMap.ker (Matrix.toLin' M)) ≠ 0 := by exact_mod_cast h
  have h2 : LinearMap.ker (Matrix.toLin' M) ≠ ⊥ := fun hb => h1 (by rw [hb]; simp)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h2
  exact ⟨v, hv0, by simpa [Matrix.toLin'_apply] using hv⟩

/-- If `K - E` is invertible, at most one parameter `u` has a nonzero kernel of
`K + u P_{{x}} - E`. -/
private lemma rankOneCross_unique {K : Matrix n n ℂ} (x : n) {E : ℝ}
    (hA : (K - (E : ℂ) • (1 : Matrix n n ℂ)).det ≠ 0) {u₁ u₂ : ℝ} {v₁ v₂ : n → ℂ}
    (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0)
    (hv₁ : (K + ((1 * u₁ : ℝ) : ℂ) • coordProj ({x} : Finset n) -
      (E : ℂ) • (1 : Matrix n n ℂ)) *ᵥ v₁ = 0)
    (hv₂ : (K + ((1 * u₂ : ℝ) : ℂ) • coordProj ({x} : Finset n) -
      (E : ℂ) • (1 : Matrix n n ℂ)) *ᵥ v₂ = 0) : u₁ = u₂ := by
  rw [rankOneCross_mulVec] at hv₁ hv₂
  have e₁ : (K - (E : ℂ) • (1 : Matrix n n ℂ)) *ᵥ v₁ = -((u₁ : ℂ) • (Pi.single x (v₁ x) : n → ℂ)) :=
    eq_neg_of_add_eq_zero_left hv₁
  have e₂ : (K - (E : ℂ) • (1 : Matrix n n ℂ)) *ᵥ v₂ = -((u₂ : ℂ) • (Pi.single x (v₂ x) : n → ℂ)) :=
    eq_neg_of_add_eq_zero_left hv₂
  have hx₁ : v₁ x ≠ 0 := by
    intro h0
    apply h₁
    apply Matrix.eq_zero_of_mulVec_eq_zero hA
    rw [e₁, h0]
    simp
  have hx₂ : v₂ x ≠ 0 := by
    intro h0
    apply h₂
    apply Matrix.eq_zero_of_mulVec_eq_zero hA
    rw [e₂, h0]
    simp
  have hw : (K - (E : ℂ) • (1 : Matrix n n ℂ)) *ᵥ
      ((u₂ * v₂ x : ℂ) • v₁ - (u₁ * v₁ x : ℂ) • v₂) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, e₁, e₂]
    funext i
    by_cases hi : i = x
    · subst hi
      simp
      ring
    · simp [hi]
  have hx := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hA hw) x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx
  have h5 : ((u₂ : ℂ) - u₁) * (v₁ x * v₂ x) = 0 := by linear_combination hx
  rcases mul_eq_zero.1 h5 with h6 | h6
  · exact (Complex.ofReal_injective (sub_eq_zero.1 h6)).symm
  · exact absurd h6 (mul_ne_zero hx₁ hx₂)

/-- For almost every `E`, `Σ_ℓ N_ℓ(E) ≤ 1` for the line `K + u P_{{x}}`. -/
theorem ae_tsum_crossCount_rankOne_le {K : Matrix n n ℂ} (hK : K.IsHermitian) (x : n) :
    ∀ᵐ E : ℝ, ∑' ℓ : ℤ, crossCount (fun u => K + ((1 * u : ℝ) : ℂ) • coordProj ({x} : Finset n))
      E (Set.Icc (ℓ : ℝ) (ℓ + 1)) ≤ 1 := by
  let H : ℝ → Matrix n n ℂ := fun u => K + ((1 * u : ℝ) : ℂ) • coordProj ({x} : Finset n)
  let S : Set ℝ := {E | (K - (E : ℂ) • (1 : Matrix n n ℂ)).det = 0} ∪
    ⋃ m : ℤ, {E | (H m - (E : ℂ) • (1 : Matrix n n ℂ)).det = 0}
  have hS : S.Countable :=
    (rankOneCross_finite_det_zero K).countable.union
      (Set.countable_iUnion fun m => (rankOneCross_finite_det_zero (H m)).countable)
  rw [ae_iff]
  refine measure_mono_null (fun E hE => ?_) (hS.measure_zero volume)
  by_contra hES
  apply hE
  have hA : (K - (E : ℂ) • (1 : Matrix n n ℂ)).det ≠ 0 := fun h => hES (Or.inl h)
  exact rankOneCross_tsum_le
    (g := fun u => (Module.finrank ℂ (LinearMap.ker (Matrix.toLin' (H u - (E : ℂ) • 1))) : ℝ≥0∞))
    (fun u => by exact_mod_cast rankOneCross_finrank_le x hA u)
    (fun u₁ u₂ h₁ h₂ => by
      obtain ⟨v₁, hv₁, hk₁⟩ := rankOneCross_exists_vec h₁
      obtain ⟨v₂, hv₂, hk₂⟩ := rankOneCross_exists_vec h₂
      exact rankOneCross_unique x hA hv₁ hv₂ hk₁ hk₂)
    (fun m => by
      by_contra hne
      obtain ⟨v, hv, hk⟩ := rankOneCross_exists_vec hne
      exact hES (Or.inr (Set.mem_iUnion.2 ⟨m, Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, hk⟩⟩)))

end LSBA
