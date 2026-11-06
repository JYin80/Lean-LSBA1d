import LSBA.Upper.CoercivityQuadratic
import LSBA.Gauss.GUEContract

/-!
# Decoupling (G.14) [cg:eq:decouple]

For `m` independent GUE blocks with the covariance (1.2) [eq:covariance], the numerical radius of
`Φ_G - 𝔼Φ` satisfies `𝔼 N(G) ≤ 2 𝔼 ‖Σ_j B_j ⊗ C_jᵗ‖` with `B`, `C` independent copies of `G`
((G.14) [cg:eq:decouple], Appendix G.4 [app:compact-gaussian]): Jensen's inequality pointwise in
`P`, the rotation `G = (B + C)/√2`, `G' = (B - C)/√2`, and `vec(B Q C) = (B ⊗ Cᵗ) vec(Q)`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

section CoercivityDecoupleAux

/-- The operator norm of a square matrix is at most its Hilbert–Schmidt norm. -/
private lemma CoercivityDecouple_opNorm_le_hs {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp only [Matrix.ofLp_toEuclideanCLM]
  have h : ∀ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 := by
    intro i
    have h1 : ‖(A *ᵥ x.ofLp) i‖ ≤ ∑ j, ‖A i j‖ * ‖x.ofLp j‖ := by
      simp only [Matrix.mulVec, dotProduct]
      exact (norm_sum_le _ _).trans (by simp)
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖)
      (fun j => ‖x.ofLp j‖)
    calc _ ≤ (∑ j, ‖A i j‖ * ‖x.ofLp j‖) ^ 2 := by gcongr
      _ ≤ _ := h2
  calc ∑ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2 ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => h i
    _ = _ := by rw [Finset.sum_mul]

/-- The operator norm of a square matrix is at most the sum of the moduli of its entries. -/
private lemma CoercivityDecouple_opNorm_le_sum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  refine (CoercivityDecouple_opNorm_le_hs A).trans ?_
  have h : ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ (∑ i, ∑ j, ‖A i j‖) ^ 2 :=
    calc ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ i, (∑ j, ‖A i j‖) ^ 2 :=
          Finset.sum_le_sum fun i _ =>
            Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _
      _ ≤ (∑ i, ∑ j, ‖A i j‖) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => by positivity
  calc Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ Real.sqrt ((∑ i, ∑ j, ‖A i j‖) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = ∑ i, ∑ j, ‖A i j‖ := Real.sqrt_sq (by positivity)

/-- `|Tr(P* Σ_j B_j P* C_j)| ≤ ‖Σ_j B_j ⊗ C_jᵗ‖` for `‖P‖_HS = 1`, from
`vec(B Q C) = (B ⊗ Cᵗ) vec(Q)`. -/
private lemma CoercivityDecouple_norm_trace_le {m W : ℕ}
    (B C : Fin m → Matrix (Fin W) (Fin W) ℂ) {P : Matrix (Fin W) (Fin W) ℂ} (hP : hsSq P = 1) :
    ‖(Pᴴ * ∑ j, B j * Pᴴ * C j).trace‖ ≤ ‖∑ j, B j ⊗ₖ (C j)ᵀ‖ := by
  set X := ∑ j, B j ⊗ₖ (C j)ᵀ with hX
  let v : EuclideanSpace ℂ (Fin W × Fin W) := WithLp.toLp 2 fun p => Pᴴ p.1 p.2
  let u : EuclideanSpace ℂ (Fin W × Fin W) := WithLp.toLp 2 fun p => P p.1 p.2
  have hvec : ∀ p : Fin W × Fin W, (X *ᵥ v.ofLp) p = (∑ j, B j * Pᴴ * C j) p.1 p.2 := by
    rintro ⟨a, d⟩
    simp only [hX, v, Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.kronecker_apply,
      Matrix.transpose_apply, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul]
    calc ∑ b, ∑ c, ∑ i, B i a b * C i c d * Pᴴ b c
        = ∑ b, ∑ i, ∑ c, B i a b * C i c d * Pᴴ b c :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ i, ∑ b, ∑ c, B i a b * C i c d * Pᴴ b c := Finset.sum_comm
      _ = ∑ i, ∑ c, ∑ b, B i a b * C i c d * Pᴴ b c :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ =>
          Finset.sum_congr rfl fun b _ => by ring
  have htr : (Pᴴ * ∑ j, B j * Pᴴ * C j).trace =
      inner ℂ u ((EuclideanSpace.equiv (Fin W × Fin W) ℂ).symm (X *ᵥ v.ofLp)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Fintype.sum_prod_type]
    change _ = ∑ x, ∑ y, (X *ᵥ v.ofLp) (x, y) * star (P x y)
    simp only [hvec, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hu : ‖u‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    change Real.sqrt (∑ p : Fin W × Fin W, ‖P p.1 p.2‖ ^ 2) = 1
    rw [Fintype.sum_prod_type]
    change Real.sqrt (hsSq P) = 1
    rw [hP, Real.sqrt_one]
  have hv : ‖v‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    change Real.sqrt (∑ p : Fin W × Fin W, ‖Pᴴ p.1 p.2‖ ^ 2) = 1
    rw [Fintype.sum_prod_type]
    have : ∑ a, ∑ b, ‖Pᴴ a b‖ ^ 2 = hsSq P := by
      unfold hsSq
      rw [Finset.sum_comm]
      simp [Matrix.conjTranspose_apply]
    rw [this, hP, Real.sqrt_one]
  rw [htr]
  calc ‖inner ℂ u ((EuclideanSpace.equiv (Fin W × Fin W) ℂ).symm (X *ᵥ v.ofLp))‖
      ≤ ‖u‖ * ‖(EuclideanSpace.equiv (Fin W × Fin W) ℂ).symm (X *ᵥ v.ofLp)‖ :=
        norm_inner_le_norm _ _
    _ ≤ 1 * (‖X‖ * ‖v‖) := by
        rw [hu]; gcongr; exact Matrix.l2_opNorm_mulVec X v
    _ = ‖X‖ := by rw [hv]; ring

/-- The rotation `B = s (G + G')`, `C = s (G - G')` with `s² = 1/2` gives
`|Tr(P* Φ_G(P)) - Tr(P* Φ_{G'}(P))| ≤ 2 ‖Σ_j B_j ⊗ C_jᵗ‖` for `‖P‖_HS = 1`. -/
private lemma CoercivityDecouple_norm_sub_le {m W : ℕ}
    (G G' B C : Fin m → Matrix (Fin W) (Fin W) ℂ) (s : ℂ) (hs : s * s = 2⁻¹)
    (hB : ∀ j, B j = s • (G j + G' j)) (hC : ∀ j, C j = s • (G j - G' j))
    {P : Matrix (Fin W) (Fin W) ℂ} (hP : hsSq P = 1) :
    ‖(Pᴴ * phiMap G P).trace - (Pᴴ * phiMap G' P).trace‖ ≤ 2 * ‖∑ j, B j ⊗ₖ (C j)ᵀ‖ := by
  have h1 : ∀ j, G j * Pᴴ * G j - G' j * Pᴴ * G' j = B j * Pᴴ * C j + C j * Pᴴ * B j := by
    intro j
    rw [hB, hC]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub]
    match_scalars <;> first
      | ring1
      | linear_combination (2 : ℂ) * hs
      | linear_combination (-2 : ℂ) * hs
  have h2 : ∀ j, (Pᴴ * (C j * Pᴴ * B j)).trace = (Pᴴ * (B j * Pᴴ * C j)).trace := by
    intro j
    calc (Pᴴ * (C j * Pᴴ * B j)).trace = ((Pᴴ * C j) * (Pᴴ * B j)).trace := by
          simp only [Matrix.mul_assoc]
      _ = ((Pᴴ * B j) * (Pᴴ * C j)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  have h3 : (Pᴴ * phiMap G P).trace - (Pᴴ * phiMap G' P).trace =
      2 * (Pᴴ * ∑ j, B j * Pᴴ * C j).trace := by
    rw [← Matrix.trace_sub, ← Matrix.mul_sub]
    unfold phiMap
    rw [← Finset.sum_sub_distrib]
    simp only [h1, Matrix.trace_sum, Matrix.mul_add, Matrix.trace_add, h2,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h3, norm_mul]
  have : ‖(2 : ℂ)‖ = 2 := by simp
  rw [this]
  gcongr
  exact CoercivityDecouple_norm_trace_le B C hP

/-- `gueBlock` of `c ω + c ω'` is `c (G + G')`. -/
private lemma CoercivityDecouple_gueBlock_add {W m : ℕ} (c : ℝ) (ω ω' : Ω W m) (j : Fin m) :
    gueBlock W m (c • ω + c • ω') j = (c : ℂ) • (gueBlock W m ω j + gueBlock W m ω' j) := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

/-- `gueBlock` of `c ω - c ω'` is `c (G - G')`. -/
private lemma CoercivityDecouple_gueBlock_sub {W m : ℕ} (c : ℝ) (ω ω' : Ω W m) (j : Fin m) :
    gueBlock W m (c • ω - c • ω') j = (c : ℂ) • (gueBlock W m ω j - gueBlock W m ω' j) := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Matrix.smul_apply, Matrix.sub_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

/-- Each entry of a GUE block is square integrable. -/
private lemma CoercivityDecouple_memLp_entry (W m : ℕ) (j : Fin m) (α β : Fin W) :
    MemLp (fun ω => gueBlock W m ω j α β) 2 (μ W m) := by
  have hc : ∀ x : Fin m × Fin W × Fin W, MemLp (fun ω : Ω W m => (ω x : ℂ)) 2 (μ W m) := by
    intro x
    have h : MemLp id 2 (gaussianReal (0 : ℝ) 1) := memLp_id_gaussianReal' 2 ENNReal.ofNat_ne_top
    have h2 : MemLp (fun ω : Ω W m => ω x) 2 (μ W m) :=
      h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m × Fin W × Fin W =>
        gaussianReal (0 : ℝ) 1) x)
    exact h2.ofReal
  have key : ∀ ω : Ω W m, gueBlock W m ω j α β = ((Real.sqrt W : ℝ) : ℂ)⁻¹ *
      ∑ k : Fin W × Fin W, (ω (j, k.1, k.2) : ℂ) * hermBasis W k α β := by
    intro ω
    rw [gueBlock_eq_sum_hermBasis]
    simp [Matrix.smul_apply, Matrix.sum_apply]
  simp_rw [key]
  refine MemLp.const_mul ?_ _
  exact memLp_finsetSum _ fun (k : Fin W × Fin W) _ => (hc (j, k.1, k.2)).mul_const _

private lemma CoercivityDecouple_integrable_mul (W m : ℕ) (j : Fin m) (α β γ δ : Fin W) :
    Integrable (fun ω => gueBlock W m ω j α β * gueBlock W m ω j γ δ) (μ W m) :=
  (CoercivityDecouple_memLp_entry W m j α β).integrable_mul
    (CoercivityDecouple_memLp_entry W m j γ δ)

/-- Expansion of `(V X V)_{αβ}` in products of entries of `V`. -/
private lemma CoercivityDecouple_mul_mul_apply {W : ℕ} (V X : Matrix (Fin W) (Fin W) ℂ)
    (α β : Fin W) :
    (V * X * V) α β = ∑ γ, ∑ δ, X γ δ * (V α γ * V δ β) := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
  ring

private lemma CoercivityDecouple_integrable_mul_mul_apply (W m : ℕ) (j : Fin m)
    (X : Matrix (Fin W) (Fin W) ℂ) (α β : Fin W) :
    Integrable (fun ω => (gueBlock W m ω j * X * gueBlock W m ω j) α β) (μ W m) := by
  simp_rw [CoercivityDecouple_mul_mul_apply]
  exact integrable_finsetSum _ fun γ _ => integrable_finsetSum _ fun δ _ =>
    (CoercivityDecouple_integrable_mul W m j α γ δ β).const_mul _

/-- `𝔼[V_j X V_j] = W⁻¹ Tr(X) I` for each block, from (1.2) [eq:covariance]. -/
private lemma CoercivityDecouple_integral_mul_mul_apply (W m : ℕ) (j : Fin m)
    (X : Matrix (Fin W) (Fin W) ℂ) (α β : Fin W) :
    ∫ ω, (gueBlock W m ω j * X * gueBlock W m ω j) α β ∂(μ W m) =
      if α = β then (W : ℂ)⁻¹ * X.trace else 0 := by
  simp_rw [CoercivityDecouple_mul_mul_apply]
  have hi : ∀ γ δ : Fin W, Integrable (fun ω : Ω W m =>
      X γ δ * (gueBlock W m ω j α γ * gueBlock W m ω j δ β)) (μ W m) :=
    fun γ δ => (CoercivityDecouple_integrable_mul W m j α γ δ β).const_mul _
  rw [integral_finsetSum _ fun γ _ => integrable_finsetSum _ fun δ _ => hi γ δ]
  have h1 : ∀ γ, ∫ ω, ∑ δ, X γ δ * (gueBlock W m ω j α γ * gueBlock W m ω j δ β) ∂(μ W m) =
      ∑ δ, X γ δ * (if γ = δ ∧ α = β then (W : ℂ)⁻¹ else 0) := by
    intro γ
    rw [integral_finsetSum _ fun δ _ => hi γ δ]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [integral_const_mul, gueBlock_covariance]
    have hc : (α = β ∧ γ = δ) ↔ (γ = δ ∧ α = β) := and_comm
    simp only [true_and, hc]
  simp_rw [h1]
  by_cases hab : α = β
  · simp [hab, Matrix.trace, Finset.mul_sum, mul_comm]
  · simp [hab]

/-- Expansion of `Tr(P* Φ_G(P))` in entries of `G_j P* G_j`. -/
private lemma CoercivityDecouple_trace_phiMap {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (P : Matrix (Fin W) (Fin W) ℂ) :
    (Pᴴ * phiMap G P).trace = ∑ j, ∑ a, ∑ b, Pᴴ a b * (G j * Pᴴ * G j) b a := by
  unfold phiMap
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]

private lemma CoercivityDecouple_integrable_trace (W m : ℕ) (P : Matrix (Fin W) (Fin W) ℂ) :
    Integrable (fun ω => (Pᴴ * phiMap (gueBlock W m ω) P).trace) (μ W m) := by
  simp_rw [CoercivityDecouple_trace_phiMap]
  exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun a _ =>
    integrable_finsetSum _ fun b _ =>
      (CoercivityDecouple_integrable_mul_mul_apply W m j Pᴴ b a).const_mul _

/-- `𝔼 Tr(P* Φ_G(P)) = Tr(P* 𝔼Φ(P))` with `𝔼Φ(P) = m W⁻¹ conj(Tr P) I`, from (1.2)
[eq:covariance]. -/
private lemma CoercivityDecouple_integral_trace (W m : ℕ) (P : Matrix (Fin W) (Fin W) ℂ) :
    ∫ ω, (Pᴴ * phiMap (gueBlock W m ω) P).trace ∂(μ W m) =
      (Pᴴ * (((m : ℂ) / W * star P.trace) • (1 : Matrix (Fin W) (Fin W) ℂ))).trace := by
  simp_rw [CoercivityDecouple_trace_phiMap]
  have hi : ∀ j a b, Integrable (fun ω =>
      Pᴴ a b * (gueBlock W m ω j * Pᴴ * gueBlock W m ω j) b a) (μ W m) :=
    fun j a b => (CoercivityDecouple_integrable_mul_mul_apply W m j Pᴴ b a).const_mul _
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun a _ =>
    integrable_finsetSum _ fun b _ => hi j a b]
  have h1 : ∀ j, ∫ ω, ∑ a, ∑ b, Pᴴ a b * (gueBlock W m ω j * Pᴴ * gueBlock W m ω j) b a
      ∂(μ W m) = ∑ a, ∑ b, Pᴴ a b * (if b = a then (W : ℂ)⁻¹ * Pᴴ.trace else 0) := by
    intro j
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hi j a b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => hi j a b]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, CoercivityDecouple_integral_mul_mul_apply]
  simp_rw [h1]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  have : ∑ a, Pᴴ a a = star P.trace := by
    rw [← Matrix.trace_conjTranspose]; rfl
  rw [this, Matrix.trace_conjTranspose]
  ring

end CoercivityDecoupleAux

/-- (G.14) [cg:eq:decouple] with the numerical radius:
`𝔼 N(G) ≤ 2 𝔼 ‖Σ_j B_j ⊗ C_jᵗ‖` for independent GUE families `G`, `B`, `C` of (1.2)
[eq:covariance]. -/
theorem integral_numRad_le (W m : ℕ) :
    ∫ ω, numRad (gueBlock W m ω) ∂(μ W m) ≤
      2 * ∫ q, ‖∑ j, gueBlock W m q.1 j ⊗ₖ (gueBlock W m q.2 j)ᵀ‖ ∂((μ W m).prod (μ W m)) := by
  set s : ℝ := Real.sqrt 2 / 2 with hs_def
  have hs : (s : ℂ) * (s : ℂ) = 2⁻¹ := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have : s * s = 2⁻¹ := by rw [hs_def]; field_simp; linarith
    rw [← Complex.ofReal_mul, this]; push_cast; ring
  set R : Ω W m × Ω W m → Ω W m × Ω W m := fun q => (s • q.1 + s • q.2, s • q.1 - s • q.2)
    with hR_def
  have hR : MeasurePreserving R ((μ W m).prod (μ W m)) ((μ W m).prod (μ W m)) := by
    have h := measurePreserving_stdGauss_rotation (ι := Fin m × Fin W × Fin W) (π / 4)
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four] at h
    exact h
  set F : Ω W m × Ω W m → ℝ := fun q => ‖∑ j, gueBlock W m q.1 j ⊗ₖ (gueBlock W m q.2 j)ᵀ‖
    with hF_def
  have hGc : ∀ j, Continuous fun ω : Ω W m => gueBlock W m ω j := fun j =>
    continuous_matrix fun α β => by
      simp only [gueBlock, Matrix.of_apply]
      split_ifs <;> fun_prop
  have hXc : Continuous fun q : Ω W m × Ω W m =>
      ∑ j, gueBlock W m q.1 j ⊗ₖ (gueBlock W m q.2 j)ᵀ :=
    continuous_finsetSum _ fun j _ => continuous_matrix fun i k =>
      (((hGc j).comp continuous_fst).matrix_elem i.1 k.1).mul
        (((hGc j).comp continuous_snd).matrix_elem k.2 i.2)
  have hFc : Continuous F := continuous_norm.comp hXc
  have hFi : Integrable F ((μ W m).prod (μ W m)) := by
    refine Integrable.mono' (g := fun q => ∑ i : Fin W × Fin W, ∑ k : Fin W × Fin W, ∑ j,
        ‖gueBlock W m q.1 j i.1 k.1‖ * ‖gueBlock W m q.2 j k.2 i.2‖) ?_
      hFc.aestronglyMeasurable (ae_of_all _ fun q => ?_)
    · exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
        integrable_finsetSum _ fun j _ =>
          (integrable_gueBlock W m j i.1 k.1).norm.mul_prod (integrable_gueBlock W m j k.2 i.2).norm
    · rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      refine (CoercivityDecouple_opNorm_le_sum _).trans
        (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_)
      have hsum : (∑ j, gueBlock W m q.1 j ⊗ₖ (gueBlock W m q.2 j)ᵀ) i k =
          ∑ j, gueBlock W m q.1 j i.1 k.1 * gueBlock W m q.2 j k.2 i.2 := by
        rw [Matrix.sum_apply]; rfl
      rw [hsum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
  have hFR : Integrable (fun q => 2 * F (R q)) ((μ W m).prod (μ W m)) :=
    ((hR.integrable_comp hFc.aestronglyMeasurable).2 hFi).const_mul 2
  have hpt : ∀ᵐ ω ∂(μ W m), numRad (gueBlock W m ω) ≤ ∫ ω', 2 * F (R (ω, ω')) ∂(μ W m) := by
    filter_upwards [hFR.prod_right_ae] with ω hω
    refine Real.iSup_le (fun P => ?_) (integral_nonneg fun _ => by positivity)
    obtain ⟨P, hP⟩ := P
    dsimp only
    have hA := CoercivityDecouple_integrable_trace W m P
    have hAm := CoercivityDecouple_integral_trace W m P
    have heq : (Pᴴ * (phiMap (gueBlock W m ω) P -
        ((m : ℂ) / W * star P.trace) • (1 : Matrix (Fin W) (Fin W) ℂ))).trace =
        ∫ ω', ((Pᴴ * phiMap (gueBlock W m ω) P).trace -
          (Pᴴ * phiMap (gueBlock W m ω') P).trace) ∂(μ W m) := by
      rw [integral_sub (integrable_const _) hA, integral_const, hAm, Matrix.mul_sub,
        Matrix.trace_sub]
      simp
    rw [heq]
    refine (Complex.abs_re_le_norm _).trans (norm_integral_le_of_norm_le hω
      (ae_of_all _ fun ω' => ?_))
    exact CoercivityDecouple_norm_sub_le (gueBlock W m ω) (gueBlock W m ω')
      (fun j => gueBlock W m (s • ω + s • ω') j) (fun j => gueBlock W m (s • ω - s • ω') j)
      (s : ℂ) hs (fun j => CoercivityDecouple_gueBlock_add s ω ω' j)
      (fun j => CoercivityDecouple_gueBlock_sub s ω ω' j) hP
  calc ∫ ω, numRad (gueBlock W m ω) ∂(μ W m)
      ≤ ∫ ω, ∫ ω', 2 * F (R (ω, ω')) ∂(μ W m) ∂(μ W m) :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => Real.iSup_nonneg fun _ => abs_nonneg _)
          hFR.integral_prod_left hpt
    _ = ∫ q, 2 * F (R q) ∂((μ W m).prod (μ W m)) := (integral_prod _ hFR).symm
    _ = 2 * ∫ q, F (R q) ∂((μ W m).prod (μ W m)) := integral_const_mul _ _
    _ = 2 * ∫ q, F q ∂((μ W m).prod (μ W m)) := by
        rw [← integral_map hR.measurable.aemeasurable
          (by rw [hR.map_eq]; exact hFc.aestronglyMeasurable), hR.map_eq]

end LSBA
