import LSBA.Upper.SmallChart
import LSBA.Analysis.SkewBasis
import LSBA.Gauss.Divergence

/-!
# The statement of Lemma 9.3 [su:lem:chosen-generator]

Lemma 9.3 [su:lem:chosen-generator] as a predicate on a cutoff and a generator, with the objects
of Section 9.2 [su:sec:generator-choice] it uses. The unitary change (9.24)
[su:eq:cut-generator-equivariance] of the active inputs, `V_5 - g² R_4 ↦ U (V_5 - g² R_4) U*`
and `V_i ↦ U V_i U*` for `6 ≤ i ≤ q - 1`. The source energy
`‖P v‖² Σ_a ‖(e_a · ∇_v) F‖²_HS` of (9.29) [su:eq:pair-source-derivative-sum] and (9.31)
[us:eq:score] over a real orthonormal basis `(e_a)` of `𝓗_v`, written basis-free as a sum over
the real coordinate directions `e_j`, `i e_j` projected onto `𝓗_v`, and the tangential gradient
`‖∇_v f‖²` of (9.30) [su:eq:pair-cutoff-derivative].

The source families `K̂(V_5, …, V_{q-1}; v̂; R_4)` and `χ̂` are functions of `R_4`, of the sample
(through the active blocks `V_5, …, V_{q-1}` only) and of the source `v̂ ≠ 0`. `GenFamily`
collects, at a fixed `R_4` and `P`, the parameter dependence, the range of `χ̂`, the homogeneity
and unitary equivariance of part (ii) and the cutoff family of part (v), and the regularity used
for Gaussian integration by parts: `χ̂` is `C²`, `K̂` is `C²` on an open set containing the support
of `χ̂`, where `R_5, …, R_{q-1}` exist, and the active blocks are bounded on that support.
`GenPoint` collects the pointwise statements of parts (i), (iii), (iv), (v) at the actual data.
The expectations of (9.25) [su:eq:pair-generator-size], (9.30) [su:eq:pair-cutoff-derivative]
and `𝔼 χ ≥ ½` are over all inputs, with the preparation indicator, the prepared chart and `P` as
functions of the four preparation blocks. The regime enters through `P`, the rate `σ`
(`g² W^{ε/4}` in regime (i), `W^{-1+14θ}` in regime (ii), so that (9.28)
[su:eq:pair-exceptional-dimension] reads `dim ≤ C W σ`) and the bound `M₀` on `g² ‖P R_4 P‖`.

Two pointwise consequences used with Lemma 9.4 [us:lem:score] in the proof of Lemma 8.12
[up:lem:small-contraction]: the product rule with (9.27) [su:eq:pair-source-regularity]–(9.29)
[su:eq:pair-source-derivative-sum]
gives (9.37) [su:eq:chosen-generator-cut-costs]; and the terminal correction of Section 9.3
[su:sec:generator-bounds], `‖L‖_HS ≤ 3 ‖v_{q-1}‖⁻¹ ‖R_{[q-1,5]} K v_4 - v_{q-1}‖` with (9.26)
[su:eq:pair-matching-error] and `‖R_{q-1}‖ ≤ C W³`, gives
`W g⁴ ‖[χ L, R_{q-1}]‖²_HS ≤ 36 C⁴ W⁻¹ g⁴`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Auxiliary lemmas -/

/-- `‖A‖²_HS ≥ 0`. -/
private lemma ChosenGenerator_hsSq_nonneg {k l : Type*} [Fintype k] [Fintype l] (A : Matrix k l ℂ) :
    0 ≤ hsSq A := by
  unfold hsSq; positivity

/-- `‖r A‖²_HS = r² ‖A‖²_HS` for real `r`. -/
private lemma ChosenGenerator_hsSq_real_smul {k l : Type*} [Fintype k] [Fintype l] (r : ℝ)
    (A : Matrix k l ℂ) : hsSq (r • A) = r ^ 2 * hsSq A := by
  unfold hsSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [mul_pow, sq_abs]

/-- `‖(r : ℂ) A‖²_HS = r² ‖A‖²_HS` for real `r`. -/
private lemma ChosenGenerator_hsSq_ofReal_smul {k l : Type*} [Fintype k] [Fintype l] (r : ℝ)
    (A : Matrix k l ℂ) : hsSq ((r : ℂ) • A) = r ^ 2 * hsSq A := by
  rw [Complex.coe_smul]
  exact ChosenGenerator_hsSq_real_smul r A

/-- `‖A + B‖²_HS ≤ 2 ‖A‖²_HS + 2 ‖B‖²_HS`. -/
private lemma ChosenGenerator_hsSq_add_le {k l : Type*} [Fintype k] [Fintype l]
    (A B : Matrix k l ℂ) : hsSq (A + B) ≤ 2 * hsSq A + 2 * hsSq B := by
  unfold hsSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  simp only [Matrix.add_apply]
  have h := norm_add_le (A a b) (B a b)
  nlinarith [norm_nonneg (A a b), norm_nonneg (B a b), sq_nonneg (‖A a b‖ - ‖B a b‖),
    norm_nonneg (A a b + B a b)]

/-- `‖A - B‖²_HS ≤ 2 ‖A‖²_HS + 2 ‖B‖²_HS`. -/
private lemma ChosenGenerator_hsSq_sub_le {k l : Type*} [Fintype k] [Fintype l]
    (A B : Matrix k l ℂ) : hsSq (A - B) ≤ 2 * hsSq A + 2 * hsSq B := by
  have h := ChosenGenerator_hsSq_add_le A (-B)
  have h2 : hsSq (-B) = hsSq B := by unfold hsSq; simp
  rwa [h2, ← sub_eq_add_neg] at h

/-- `‖A*‖²_HS = ‖A‖²_HS`. -/
private lemma ChosenGenerator_hsSq_conjTranspose {k l : Type*} [Fintype k] [Fintype l]
    (A : Matrix k l ℂ) : hsSq Aᴴ = hsSq A := by
  unfold hsSq
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

/-- `‖A x‖² ≤ ‖A‖²_op ‖x‖²`. -/
private lemma ChosenGenerator_sum_sq_mulVec_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (x : Fin W → ℂ) : ∑ a, ‖(A *ᵥ x) a‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv (Fin W) ℂ).symm x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)] at h2
  simpa using h2

/-- `‖A B‖²_HS ≤ ‖A‖²_op ‖B‖²_HS`. -/
private lemma ChosenGenerator_hsSq_opNorm_mul_le {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) :
    hsSq (A * B) ≤ ‖A‖ ^ 2 * hsSq B := by
  have hB : ‖A‖ ^ 2 * hsSq B = ∑ b, ‖A‖ ^ 2 * ∑ c, ‖B c b‖ ^ 2 := by
    unfold hsSq; rw [Finset.sum_comm, Finset.mul_sum]
  rw [hB]
  unfold hsSq
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun b _ => ?_
  have := ChosenGenerator_sum_sq_mulVec_le A (fun c => B c b)
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

/-- `‖A B‖²_HS ≤ ‖A‖²_HS ‖B‖²_op`. -/
private lemma ChosenGenerator_hsSq_mul_opNorm_le {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) :
    hsSq (A * B) ≤ hsSq A * ‖B‖ ^ 2 := by
  have h := ChosenGenerator_hsSq_opNorm_mul_le Bᴴ Aᴴ
  rw [← Matrix.conjTranspose_mul, ChosenGenerator_hsSq_conjTranspose,
    ChosenGenerator_hsSq_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h
  linarith

/-- `R_{[j,5]} = R_j ⋯ R_5` is invertible when each `R_k`, `5 ≤ k ≤ j`, is. -/
private lemma ChosenGenerator_isUnit_chartProd (W : ℕ) (g E : ℝ) (q : ℕ)
    (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) (j : ℕ)
    (h : ∀ k, 5 ≤ k → k ≤ j → IsUnit (chartR W g E q R ω k)) :
    IsUnit (chartProd W g E q R ω j) := by
  induction j with
  | zero => simp [chartProd]
  | succ j ih =>
    simp only [chartProd]
    split_ifs with hj
    · exact isUnit_one
    · exact (h (j + 1) (by omega) le_rfl).mul (ih fun k hk hkj => h k hk (by omega))

/-- The real coordinates `(Re w_j, Im w_j)` of `ℂ^W`, as a Euclidean space. -/
private def ChosenGenerator_cE (W : ℕ) :
    (Fin W → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin W × Bool) where
  toFun a := WithLp.toLp 2 fun p => if p.2 then (a p.1).im else (a p.1).re
  invFun x := fun j => ⟨WithLp.ofLp x (j, false), WithLp.ofLp x (j, true)⟩
  map_add' a b := by ext p; rcases p with ⟨j, c⟩; cases c <;> simp
  map_smul' r a := by ext p; rcases p with ⟨j, c⟩; cases c <;> simp
  left_inv a := by ext j; simp
  right_inv x := by ext p; rcases p with ⟨j, c⟩; cases c <;> simp

/-- The real inner product of the coordinates is `Re(a* b)`. -/
private lemma ChosenGenerator_cE_inner {W : ℕ} (a b : Fin W → ℂ) :
    inner ℝ (ChosenGenerator_cE W a) (ChosenGenerator_cE W b) = (star a ⬝ᵥ b).re := by
  simp [ChosenGenerator_cE, PiLp.inner_apply, Fintype.sum_prod_type, dotProduct, Complex.re_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `Re(a* a) = Σ_i ‖a_i‖²`. -/
private lemma ChosenGenerator_re_dot_self {W : ℕ} (a : Fin W → ℂ) :
    (star a ⬝ᵥ a).re = ∑ i, ‖a i‖ ^ 2 := by
  simp [dotProduct, Complex.re_sum, Complex.sq_norm, Complex.normSq_apply]

/-- The Euclidean norm of the coordinates is `Σ_i ‖a_i‖²`, squared. -/
private lemma ChosenGenerator_cE_norm_sq {W : ℕ} (a : Fin W → ℂ) :
    ‖ChosenGenerator_cE W a‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ChosenGenerator_cE_inner, ChosenGenerator_re_dot_self]

/-- `Re(a* b) = Re(b* a)`. -/
private lemma ChosenGenerator_ip_comm {W : ℕ} (a b : Fin W → ℂ) :
    (star a ⬝ᵥ b).re = (star b ⬝ᵥ a).re := by
  rw [← ChosenGenerator_cE_inner, ← ChosenGenerator_cE_inner, real_inner_comm]

/-- `Re(a* (b - c)) = Re(a* b) - Re(a* c)`. -/
private lemma ChosenGenerator_ip_sub_right {W : ℕ} (a b c : Fin W → ℂ) :
    (star a ⬝ᵥ (b - c)).re = (star a ⬝ᵥ b).re - (star a ⬝ᵥ c).re := by
  simp [dotProduct_sub]

/-- `Re(a* (r b)) = r Re(a* b)` for real `r`. -/
private lemma ChosenGenerator_ip_ofReal_smul_right {W : ℕ} (a b : Fin W → ℂ) (r : ℝ) :
    (star a ⬝ᵥ ((r : ℂ) • b)).re = r * (star a ⬝ᵥ b).re := by
  simp [dotProduct_smul]

/-- `(P a)* b = a* (P b)` for Hermitian `P`. -/
private lemma ChosenGenerator_ip_mulVec {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (a b : Fin W → ℂ) :
    star (P *ᵥ a) ⬝ᵥ b = star a ⬝ᵥ (P *ᵥ b) := by
  rw [Matrix.star_mulVec, hP.eq, Matrix.dotProduct_mulVec]

/-- For `P v ≠ 0`, `tangProj P v` takes values in `𝓗_v = {w : P w = w, Re(v* w) = 0}`, is the
identity on `𝓗_v`, and is symmetric for `(a, b) ↦ Re(a* b)`. -/
private lemma ChosenGenerator_tangProj_props {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) {v : Fin W → ℂ} (hPv : P *ᵥ v ≠ 0) :
    (∀ w, P *ᵥ tangProj P v w = tangProj P v w ∧ (star v ⬝ᵥ tangProj P v w).re = 0) ∧
    (∀ w, P *ᵥ w = w → (star v ⬝ᵥ w).re = 0 → tangProj P v w = w) ∧
    (∀ a b, (star a ⬝ᵥ tangProj P v b).re = (star (tangProj P v a) ⬝ᵥ b).re) := by
  set Pv := P *ᵥ v with hPvdef
  set s : ℝ := ∑ i, ‖Pv i‖ ^ 2 with hsdef
  have hs : 0 < s := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hPv
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 (by simpa using hi)) 2) <|
      Finset.single_le_sum (f := fun i => ‖Pv i‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ i)
  have hPvP : P *ᵥ Pv = Pv := by rw [hPvdef, Matrix.mulVec_mulVec, hPP]
  have hT : ∀ w, tangProj P v w = P *ᵥ w - (((star Pv ⬝ᵥ w).re / s : ℝ) : ℂ) • Pv := fun w => rfl
  have hPvs : (star Pv ⬝ᵥ v).re = s := by
    have h := ChosenGenerator_ip_mulVec hP Pv v
    rw [hPvP] at h
    rw [h, ChosenGenerator_re_dot_self]
  have hvPv : (star v ⬝ᵥ Pv).re = s := by rw [ChosenGenerator_ip_comm, hPvs]
  have hvP : ∀ w, (star v ⬝ᵥ (P *ᵥ w)).re = (star Pv ⬝ᵥ w).re := fun w => by
    rw [← ChosenGenerator_ip_mulVec hP]
  refine ⟨fun w => ⟨?_, ?_⟩, fun w hw hvw => ?_, fun a b => ?_⟩
  · rw [hT, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hPP, hPvP]
  · rw [hT, ChosenGenerator_ip_sub_right, ChosenGenerator_ip_ofReal_smul_right, hvP, hvPv]
    field_simp
    ring
  · rw [hT]
    have : (star Pv ⬝ᵥ w).re = 0 := by
      rw [← hvP, hw]; exact hvw
    rw [this, hw]
    simp
  · have hTe : ∀ x w, (star x ⬝ᵥ tangProj P v w).re =
        (star x ⬝ᵥ P *ᵥ w).re - (star Pv ⬝ᵥ w).re / s * (star x ⬝ᵥ Pv).re := fun x w => by
      rw [hT, ChosenGenerator_ip_sub_right, ChosenGenerator_ip_ofReal_smul_right]
    rw [hTe a b, ChosenGenerator_ip_comm (tangProj P v a) b, hTe b a,
      ChosenGenerator_ip_comm a Pv, ChosenGenerator_ip_comm b Pv]
    have h1 : (star a ⬝ᵥ P *ᵥ b).re = (star b ⬝ᵥ P *ᵥ a).re := by
      rw [← ChosenGenerator_ip_mulVec hP, ChosenGenerator_ip_comm]
    rw [h1]
    ring

/-- Parseval: `Σ_i ⟨b_i, x⟩² = ‖x‖²` for an orthonormal basis `b` of a real inner product space. -/
private lemma ChosenGenerator_parseval {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ∑ i, inner ℝ (b i) x ^ 2 = ‖x‖ ^ 2 := by
  have := b.sum_sq_norm_inner_right x
  simpa [Real.norm_eq_abs, sq_abs] using this

/-- Riesz: a real linear functional on a finite-dimensional real inner product space is
`x ↦ ⟨λ, x⟩`. -/
private lemma ChosenGenerator_riesz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ℓ : E →ₗ[ℝ] ℝ) :
    ∃ lam : E, ∀ x, ℓ x = inner ℝ lam x :=
  ⟨(InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap ℓ), fun x => by
    rw [InnerProductSpace.toDual_symm_apply]; rfl⟩

/-- For a symmetric `S`, `Σ_i ⟨λ, S b_i⟩² = ‖S λ‖²`. -/
private lemma ChosenGenerator_sum_sym {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (lam : E) (S : E → E)
    (hS : ∀ x y, inner ℝ x (S y) = inner ℝ (S x) y) :
    ∑ i, inner ℝ lam (S (b i)) ^ 2 = ‖S lam‖ ^ 2 := by
  rw [← ChosenGenerator_parseval b (S lam)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hS, real_inner_comm]

/-- Trace bound for a sum of squares of real linear functionals `Q = Σ_k (ℓ_k)²` over the image
of an orthonormal basis `b` under a symmetric projection `T` onto `N`: if `Q ≤ A ‖·‖²` on `N` and
`Q ≤ B ‖·‖²` on `N ∩ Es^⊥` with `Es ⊆ N`, then `Σ_i Q(T b_i) ≤ A dim Es + B |ι|`. -/
private lemma ChosenGenerator_frame {E ι κ : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ E) (ℓ : κ → E →ₗ[ℝ] ℝ) (N Es : Submodule ℝ E)
    (hEN : Es ≤ N) (T : E → E) (hT : ∀ x, T x ∈ N) (hT2 : ∀ x ∈ N, T x = x)
    (hTs : ∀ x y, inner ℝ x (T y) = inner ℝ (T x) y) (A B : ℝ) (hB0 : 0 ≤ B)
    (hA : ∀ w ∈ N, ∑ k, ℓ k w ^ 2 ≤ A * ‖w‖ ^ 2)
    (hBd : ∀ w ∈ N, (∀ u ∈ Es, inner ℝ u w = 0) → ∑ k, ℓ k w ^ 2 ≤ B * ‖w‖ ^ 2) :
    ∑ i, ∑ k, ℓ k (T (b i)) ^ 2 ≤ A * Module.finrank ℝ Es + B * Fintype.card ι := by
  classical
  set T₁ : E → E := fun x => Es.starProjection x with hT₁
  set T₂ : E → E := fun x => T x - T₁ x with hT₂
  have h1mem : ∀ x, T₁ x ∈ Es := fun x => Submodule.starProjection_apply_mem Es x
  have h1id : ∀ x ∈ Es, T₁ x = x := fun x hx => Submodule.starProjection_eq_self_iff.mpr hx
  have h1s : ∀ x y, inner ℝ x (T₁ y) = inner ℝ (T₁ x) y := fun x y =>
    (Submodule.inner_starProjection_left_eq_right Es x y).symm
  have h2s : ∀ x y, inner ℝ x (T₂ y) = inner ℝ (T₂ x) y := by
    intro x y
    simp only [hT₂, inner_sub_right, inner_sub_left, hTs, h1s]
  have h2perp : ∀ x, ∀ u ∈ Es, inner ℝ u (T₂ x) = 0 := by
    intro x u hu
    simp only [hT₂, inner_sub_right]
    rw [hTs, h1s, h1id u hu, hT2 u (hEN hu), sub_self]
  have h2mem : ∀ x, T₂ x ∈ N := fun x => N.sub_mem (hT x) (hEN (h1mem x))
  choose lam hlam using fun k => ChosenGenerator_riesz (ℓ k)
  have hsum : ∀ S : E → E, (∀ x y, inner ℝ x (S y) = inner ℝ (S x) y) →
      ∑ i, ∑ k, ℓ k (S (b i)) ^ 2 = ∑ k, ‖S (lam k)‖ ^ 2 := by
    intro S hS
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hlam]
    exact ChosenGenerator_sum_sym b (lam k) S hS
  have hsplit : ∑ i, ∑ k, ℓ k (T (b i)) ^ 2 =
      ∑ i, ∑ k, ℓ k (T₁ (b i)) ^ 2 + ∑ i, ∑ k, ℓ k (T₂ (b i)) ^ 2 := by
    rw [hsum T hTs, hsum T₁ h1s, hsum T₂ h2s, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have horth : inner ℝ (T₁ (lam k)) (T₂ (lam k)) = 0 := h2perp _ _ (h1mem _)
    have : T (lam k) = T₁ (lam k) + T₂ (lam k) := by simp [hT₂]
    rw [this, norm_add_sq_real, horth]; ring
  have hn1 : ∀ x, ‖T₁ x‖ ^ 2 = inner ℝ x (T₁ x) := by
    intro x
    rw [← real_inner_self_eq_norm_sq, ← h1s, h1id _ (h1mem x)]
  -- trace of the projection onto `Es`
  have htr : ∑ i, ‖T₁ (b i)‖ ^ 2 = (Module.finrank ℝ Es : ℝ) := by
    have hP : LinearMap.IsProj Es (Es.starProjection : E →L[ℝ] E).toLinearMap :=
      ⟨h1mem, h1id⟩
    have h1 := LinearMap.IsProj.trace hP
    have h2 := LinearMap.trace_eq_sum_inner (Es.starProjection : E →L[ℝ] E).toLinearMap b
    rw [h1] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hn1]
    rfl
  have part1 : ∑ i, ∑ k, ℓ k (T₁ (b i)) ^ 2 ≤ A * Module.finrank ℝ Es := by
    calc ∑ i, ∑ k, ℓ k (T₁ (b i)) ^ 2 ≤ ∑ i, A * ‖T₁ (b i)‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hA _ (hEN (h1mem _))
      _ = A * Module.finrank ℝ Es := by rw [← Finset.mul_sum, htr]
  have hnT : ∀ x, ‖T x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    intro x
    have h1 : ‖T x‖ ^ 2 = inner ℝ x (T x) := by
      rw [← real_inner_self_eq_norm_sq, ← hTs, hT2 _ (hT x)]
    have h2 : inner ℝ x (T x) ≤ ‖x‖ * ‖T x‖ := real_inner_le_norm _ _
    nlinarith [norm_nonneg x, norm_nonneg (T x), sq_nonneg (‖T x‖ - ‖x‖)]
  have hn2 : ∀ x, ‖T₂ x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    intro x
    have hp : ‖T x‖ ^ 2 = ‖T₁ x‖ ^ 2 + ‖T₂ x‖ ^ 2 := by
      have horth : inner ℝ (T₁ x) (T₂ x) = 0 := h2perp _ _ (h1mem _)
      have : T x = T₁ x + T₂ x := by simp [hT₂]
      rw [this, norm_add_sq_real, horth]; ring
    nlinarith [hnT x, sq_nonneg ‖T₁ x‖]
  have part2 : ∑ i, ∑ k, ℓ k (T₂ (b i)) ^ 2 ≤ B * Fintype.card ι := by
    calc ∑ i, ∑ k, ℓ k (T₂ (b i)) ^ 2 ≤ ∑ i, B * ‖T₂ (b i)‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hBd _ (h2mem _) (fun u hu => h2perp _ _ hu)
      _ ≤ ∑ i : ι, B * 1 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hn2 (b i)
          rw [b.norm_eq_one] at this
          nlinarith
      _ = B * Fintype.card ι := by simp [mul_comm]
  rw [hsplit]
  linarith

/-- The real subspace `𝓗_v = {w : P w = w, Re(v* w) = 0}`. -/
private def ChosenGenerator_Hv {W : ℕ} (P : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) :
    Submodule ℝ (Fin W → ℂ) where
  carrier := {w | P *ᵥ w = w ∧ (star v ⬝ᵥ w).re = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨by rw [Matrix.mulVec_add, ha1, hb1], ?_⟩
    rw [dotProduct_add, Complex.add_re, ha2, hb2, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    rintro r a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mulVec_smul, ha1]
    · rw [dotProduct_smul]; simp [ha2]

/-- The trace identity behind (9.29) [su:eq:pair-source-derivative-sum]: for a real linear map
`D` and `s = ‖P v‖²`, `s Σ_j (‖D Π_v e_j‖²_HS + ‖D Π_v (i e_j)‖²_HS) ≤ A dim 𝓔 + B · 2W`, when
`s ‖D w‖²_HS ≤ A ‖w‖²` on `𝓗_v` and `s ‖D w‖²_HS ≤ B ‖w‖²` on `𝓗_v ∩ 𝓔^⊥`. -/
private lemma ChosenGenerator_energy_bound {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) {v : Fin W → ℂ} (hPv : P *ᵥ v ≠ 0)
    (D : (Fin W → ℂ) →ₗ[ℝ] Matrix (Fin W) (Fin W) ℂ) (Es : Submodule ℝ (Fin W → ℂ))
    (hEs : ∀ w ∈ Es, P *ᵥ w = w ∧ (star v ⬝ᵥ w).re = 0) (A B : ℝ) (hB0 : 0 ≤ B)
    (hA : ∀ w, P *ᵥ w = w → (star v ⬝ᵥ w).re = 0 →
      (∑ i, ‖(P *ᵥ v) i‖ ^ 2) * hsSq (D w) ≤ A * ∑ i, ‖w i‖ ^ 2)
    (hBd : ∀ w, P *ᵥ w = w → (star v ⬝ᵥ w).re = 0 → (∀ u ∈ Es, (star u ⬝ᵥ w).re = 0) →
      (∑ i, ‖(P *ᵥ v) i‖ ^ 2) * hsSq (D w) ≤ B * ∑ i, ‖w i‖ ^ 2) :
    (∑ i, ‖(P *ᵥ v) i‖ ^ 2) * ∑ j, (hsSq (D (tangProj P v (Pi.single j 1))) +
      hsSq (D (tangProj P v (Pi.single j Complex.I)))) ≤
      A * Module.finrank ℝ Es + B * (2 * W) := by
  obtain ⟨hT1, hT2, hT3⟩ := ChosenGenerator_tangProj_props hP hPP hPv
  set s : ℝ := ∑ i, ‖(P *ᵥ v) i‖ ^ 2 with hsdef
  have hs0 : 0 ≤ s := by positivity
  set cE := ChosenGenerator_cE W with hcE
  let b : OrthonormalBasis (Fin W × Bool) ℝ (EuclideanSpace ℝ (Fin W × Bool)) :=
    EuclideanSpace.basisFun _ ℝ
  let ℓ : ((Fin W × Fin W) × Bool) → EuclideanSpace ℝ (Fin W × Bool) →ₗ[ℝ] ℝ := fun k =>
    (Real.sqrt s) • ((if k.2 then Complex.imLm else Complex.reLm) ∘ₗ
      Matrix.entryLinearMap ℝ ℂ k.1.1 k.1.2 ∘ₗ D ∘ₗ cE.symm.toLinearMap)
  have hℓ : ∀ x, ∑ k, ℓ k x ^ 2 = s * hsSq (D (cE.symm x)) := by
    intro x
    simp only [ℓ, Fintype.sum_prod_type, Fintype.sum_bool, hsSq]
    simp
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_pow, mul_pow, ← mul_add, Real.sq_sqrt hs0, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hinner : ∀ a b, inner ℝ (cE a) (cE b) = (star a ⬝ᵥ b).re := ChosenGenerator_cE_inner
  have hnorm : ∀ a, ‖cE a‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := ChosenGenerator_cE_norm_sq
  let N : Submodule ℝ (EuclideanSpace ℝ (Fin W × Bool)) :=
    (ChosenGenerator_Hv P v).map (cE : (Fin W → ℂ) →ₗ[ℝ] EuclideanSpace ℝ (Fin W × Bool))
  let Es' : Submodule ℝ (EuclideanSpace ℝ (Fin W × Bool)) :=
    Es.map (cE : (Fin W → ℂ) →ₗ[ℝ] EuclideanSpace ℝ (Fin W × Bool))
  have hmemN : ∀ x, x ∈ N ↔ P *ᵥ cE.symm x = cE.symm x ∧ (star v ⬝ᵥ cE.symm x).re = 0 :=
    fun x => Submodule.mem_map_equiv (ChosenGenerator_Hv P v)
  have hEN : Es' ≤ N := Submodule.map_mono fun w hw => hEs w hw
  let T : EuclideanSpace ℝ (Fin W × Bool) → EuclideanSpace ℝ (Fin W × Bool) :=
    fun x => cE (tangProj P v (cE.symm x))
  have hTN : ∀ x, T x ∈ N := fun x => by
    rw [hmemN]
    simpa [T] using hT1 (cE.symm x)
  have hTid : ∀ x ∈ N, T x = x := fun x hx => by
    rw [hmemN] at hx
    simp only [T]
    rw [hT2 _ hx.1 hx.2, cE.apply_symm_apply]
  have hTs : ∀ x y, inner ℝ x (T y) = inner ℝ (T x) y := fun x y => by
    obtain ⟨a, rfl⟩ := cE.surjective x
    obtain ⟨c, rfl⟩ := cE.surjective y
    simp only [T, LinearEquiv.symm_apply_apply]
    rw [hinner, hinner]
    exact hT3 a c
  have hA' : ∀ w ∈ N, ∑ k, ℓ k w ^ 2 ≤ A * ‖w‖ ^ 2 := fun w hw => by
    rw [hmemN] at hw
    rw [hℓ, ← cE.apply_symm_apply w, hnorm, LinearEquiv.symm_apply_apply]
    exact hA _ hw.1 hw.2
  have hB' : ∀ w ∈ N, (∀ u ∈ Es', inner ℝ u w = 0) → ∑ k, ℓ k w ^ 2 ≤ B * ‖w‖ ^ 2 :=
    fun w hw hperp => by
    rw [hmemN] at hw
    rw [hℓ, ← cE.apply_symm_apply w, hnorm, LinearEquiv.symm_apply_apply]
    refine hBd _ hw.1 hw.2 fun u hu => ?_
    have := hperp (cE u) (Submodule.mem_map_of_mem hu)
    rwa [← cE.apply_symm_apply w, hinner] at this
  have key := ChosenGenerator_frame b ℓ N Es' hEN T hTN hTid hTs A B hB0 hA' hB'
  have hfin : Module.finrank ℝ Es' = Module.finrank ℝ Es := LinearEquiv.finrank_map_eq cE Es
  have hcard : (Fintype.card (Fin W × Bool) : ℝ) = 2 * W := by simp [mul_comm]
  have h1 : ∀ j, cE.symm (b (j, false)) = Pi.single j 1 := fun j => by
    ext j'
    simp only [b, cE, ChosenGenerator_cE, LinearEquiv.coe_symm_mk, EuclideanSpace.basisFun_apply,
      Pi.single_apply]
    by_cases h : j' = j <;> simp [h, Complex.ext_iff]
  have h2 : ∀ j, cE.symm (b (j, true)) = Pi.single j Complex.I := fun j => by
    ext j'
    simp only [b, cE, ChosenGenerator_cE, LinearEquiv.coe_symm_mk, EuclideanSpace.basisFun_apply,
      Pi.single_apply]
    by_cases h : j' = j <;> simp [h, Complex.ext_iff]
  have hlhs : ∑ i, ∑ k, ℓ k (T (b i)) ^ 2 = s * ∑ j, (hsSq (D (tangProj P v (Pi.single j 1))) +
      hsSq (D (tangProj P v (Pi.single j Complex.I)))) := by
    have : ∀ i, ∑ k, ℓ k (T (b i)) ^ 2 = s * hsSq (D (tangProj P v (cE.symm (b i)))) := fun i => by
      rw [hℓ]
      simp only [T, LinearEquiv.symm_apply_apply]
    simp only [this, ← Finset.mul_sum, Fintype.sum_prod_type, Fintype.sum_bool, h1, h2]
    congr 1
    exact Finset.sum_congr rfl fun j _ => add_comm _ _
  rw [hfin, hcard, hlhs] at key
  exact key

/-- The change (9.24) [su:eq:cut-generator-equivariance] of the active inputs by a unitary `U`:
block `4` (the input `V_5`) becomes `U (V_5 - g² R) U* + g² R`, blocks `5, …, q - 2` (the inputs
`V_6, …, V_{q-1}`) become `U V_i U*`, and the other blocks are unchanged. -/
def srcAct (W q : ℕ) (g : ℝ) (R U : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) : Ω W q :=
  gueCoord W q fun i =>
    if (i : ℕ) = 4 then
      U * (gueBlock W q ω i - ((g : ℂ) ^ 2) • R) * Uᴴ + ((g : ℂ) ^ 2) • R
    else if 5 ≤ (i : ℕ) ∧ (i : ℕ) + 2 ≤ q then U * gueBlock W q ω i * Uᴴ
    else gueBlock W q ω i

/-- The source energy `‖P v‖² Σ_a ‖(e_a · ∇_v) F‖²_HS` of (9.29)
[su:eq:pair-source-derivative-sum] and (9.31) [us:eq:score] at the source `v`, over the real
coordinate directions `e_j`, `i e_j` projected onto `𝓗_v`. -/
def srcEnergy {W : ℕ} (P : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ)
    (F : (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  (∑ i, ‖(P *ᵥ v) i‖ ^ 2) *
    ∑ j, (hsSq (lineDeriv ℝ F v (tangProj P v (Pi.single j 1))) +
      hsSq (lineDeriv ℝ F v (tangProj P v (Pi.single j Complex.I))))

/-- The squared tangential gradient `‖∇_v f‖²` along `𝓗_v` of (9.30)
[su:eq:pair-cutoff-derivative]. -/
def tangGradSq {W : ℕ} (P : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) (f : (Fin W → ℂ) → ℝ) :
    ℝ :=
  ∑ j, (lineDeriv ℝ f v (tangProj P v (Pi.single j 1)) ^ 2 +
    lineDeriv ℝ f v (tangProj P v (Pi.single j Complex.I)) ^ 2)

/-- The family clauses of Lemma 9.3 [su:lem:chosen-generator] at a fixed `R_4 = R` and `P`:
dependence on the active blocks only, `0 ≤ χ̂ ≤ 1`, homogeneity of degree zero in `v̂` and
equivariance under (9.24) [su:eq:cut-generator-equivariance] (parts (ii), (v)); `χ̂` is `C²` on
`{v̂ ≠ 0}`, `K̂` is `C²` on an open set containing the support of `χ̂` (off `v̂ = 0`), on which
`R_5, …, R_{q-1}` exist, and the active blocks are bounded on the support of `χ̂`. -/
def GenFamily (W q : ℕ) (g E : ℝ) (P R : Matrix (Fin W) (Fin W) ℂ)
    (Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ) (χh : Ω W q → (Fin W → ℂ) → ℝ) :
    Prop :=
  (∀ ω ω' : Ω W q, (∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q →
      gueBlock W q ω i = gueBlock W q ω' i) → ∀ w, Kh ω w = Kh ω' w ∧ χh ω w = χh ω' w) ∧
  (∀ ω w, 0 ≤ χh ω w ∧ χh ω w ≤ 1) ∧
  (∀ ω w (a : ℂ), a ≠ 0 → Kh ω (a • w) = Kh ω w ∧ χh ω (a • w) = χh ω w) ∧
  (∀ U ∈ Matrix.unitaryGroup (Fin W) ℂ, U * (1 - P) = 1 - P → ∀ ω w,
    Kh (srcAct W q g R U ω) (U *ᵥ w) = U * Kh ω w * Uᴴ ∧
      χh (srcAct W q g R U ω) (U *ᵥ w) = χh ω w) ∧
  ContDiffOn ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2) {p | p.2 ≠ 0} ∧
  (∃ G : Set (Ω W q × (Fin W → ℂ)), IsOpen G ∧
    ContDiffOn ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => Kh p.1 p.2) G ∧
    ∀ p ∈ tsupport (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2), p.2 ≠ 0 →
      p ∈ G ∧ ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R p.1 j)) ∧
  ∃ B : ℝ, ∀ ω w, χh ω w ≠ 0 → ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q →
    ‖gueBlock W q ω i‖ ≤ B

/-- The pointwise clauses of Lemma 9.3 [su:lem:chosen-generator] at the data `(R_4, v_4) = (R, v)`
and the sample `ω`, for the family `Kv = K̂(ω; ·)` and `K = K̂(ω; v)`: part (i), (9.22)
[su:eq:chosen-generator-geometry] with `P v ≠ 0` and `R_5, …, R_{q-1}` defined; part (iii),
`‖K‖²_HS ≤ C` of (9.25) [su:eq:pair-generator-size] and (9.26) [su:eq:pair-matching-error]
`‖R_{[q-1,5]} K v - v_{q-1}‖ ≤ C W⁻⁴ ‖v_{q-1}‖`; part (iv), (9.27) [su:eq:pair-source-regularity]
with an exceptional real subspace `𝓔_v ⊆ 𝓗_v` of dimension `≤ C W σ` (9.28)
[su:eq:pair-exceptional-dimension]; part (v), `‖R_{q-1}‖ ≤ C W³`, and `g² ‖P R P‖ ≤ M₀`. -/
def GenPoint (W q : ℕ) (g E : ℝ) (P R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) (C M₀ σ : ℝ)
    (Kv : (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) : Prop :=
  P *ᵥ v ≠ 0 ∧ (Kv v)ᴴ = -Kv v ∧ P * Kv v * P = Kv v ∧ IsGenNormalized W g E q R v (Kv v) ω ∧
  (∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j)) ∧
  hsSq (Kv v) ≤ C ∧
  ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ (Kv v *ᵥ v) - chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2
    ≤ C ^ 2 * (W : ℝ) ^ (-8 : ℝ) * ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 ∧
  (∃ Es : Submodule ℝ (Fin W → ℂ), (∀ w ∈ Es, P *ᵥ w = w ∧ (star v ⬝ᵥ w).re = 0) ∧
    (Module.finrank ℝ Es : ℝ) ≤ C * W * σ ∧
    (∀ w : Fin W → ℂ, P *ᵥ w = w → (star v ⬝ᵥ w).re = 0 →
      (∑ i, ‖(P *ᵥ v) i‖ ^ 2) * hsSq (lineDeriv ℝ Kv v w) ≤ C ^ 2 * ∑ i, ‖w i‖ ^ 2) ∧
    ∀ w : Fin W → ℂ, P *ᵥ w = w → (star v ⬝ᵥ w).re = 0 → (∀ u ∈ Es, (star u ⬝ᵥ w).re = 0) →
      (∑ i, ‖(P *ᵥ v) i‖ ^ 2) * hsSq (lineDeriv ℝ Kv v w) ≤
        C ^ 2 * hsSq (Kv v) * ∑ i, ‖w i‖ ^ 2) ∧
  ‖chartR W g E q R ω (q - 1)‖ ≤ C * (W : ℝ) ^ 3 ∧
  g ^ 2 * ‖P * R * P‖ ≤ M₀

/-- Lemma 9.3 [su:lem:chosen-generator] for the cutoff `χ = pre · χ̂(R_4; ·; v_4)` and the
generator `K = K̂(R_4; ·; v_4)`, at energy `E`, incoming flag `x`, projection rule `R ↦ P(R)`
((9.4) [su:eq:source-projection]), constant `C`, rate `σ` and bound `M₀`: the preparation
indicator `pre ∈ {0, 1}`, the chart `R_4` and the source `v_4` are measurable functions of the
four preparation blocks, with the prepared chart (9.1) [su:eq:graph-input] where `pre = 1`; `P`
is an orthogonal projection commuting with `R_4`; the family and pointwise clauses hold; and
`𝔼 χ ≥ ½`, `𝔼 ‖χ K‖²_HS ≤ C σ` (9.25) [su:eq:pair-generator-size] and
`𝔼[‖P v_4‖² ‖K‖²_HS ‖∇_{v_4} χ̂‖²] ≤ C` (9.30) [su:eq:pair-cutoff-derivative]. -/
def ChosenGenerator (W q : ℕ) (g E : ℝ) (x : IsoFlag W)
    (Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ) (C σ M₀ : ℝ)
    (pre : Ω W q → ℝ) (Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ) (vf : Ω W q → Fin W → ℂ)
    (Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ)
    (χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ) : Prop :=
  (∀ ω, pre ω = 0 ∨ pre ω = 1) ∧ Measurable pre ∧ Measurable Rf ∧ Measurable vf ∧
  (∀ ω ω' : Ω W q, (∀ i : Fin q, (i : ℕ) < 4 → gueBlock W q ω i = gueBlock W q ω' i) →
    pre ω = pre ω' ∧ Rf ω = Rf ω' ∧ vf ω = vf ω') ∧
  (∀ ω, pre ω ≠ 0 → IsPrepChart W g E q x ω (Rf ω) (vf ω)) ∧
  Measurable Pf ∧
  Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) => Kh p.1 p.2.1 p.2.2) ∧
  Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) => χh p.1 p.2.1 p.2.2) ∧
  (∀ ω, pre ω ≠ 0 → (Pf (Rf ω)).IsHermitian ∧ Pf (Rf ω) * Pf (Rf ω) = Pf (Rf ω) ∧
    Pf (Rf ω) * Rf ω = Rf ω * Pf (Rf ω) ∧
    GenFamily W q g E (Pf (Rf ω)) (Rf ω) (Kh (Rf ω)) (χh (Rf ω))) ∧
  (∀ ω, pre ω * χh (Rf ω) ω (vf ω) ≠ 0 →
    GenPoint W q g E (Pf (Rf ω)) (Rf ω) (vf ω) C M₀ σ (Kh (Rf ω) ω) ω) ∧
  (1 / 2 : ℝ) ≤ ∫ ω, pre ω * χh (Rf ω) ω (vf ω) ∂(μ W q) ∧
  ∫⁻ ω, ENNReal.ofReal ((pre ω * χh (Rf ω) ω (vf ω)) ^ 2 * hsSq (Kh (Rf ω) ω (vf ω))) ∂(μ W q) ≤
    ENNReal.ofReal (C * σ) ∧
  ∫⁻ ω, ENNReal.ofReal (pre ω * (∑ i, ‖(Pf (Rf ω) *ᵥ vf ω) i‖ ^ 2) *
      hsSq (Kh (Rf ω) ω (vf ω)) * tangGradSq (Pf (Rf ω)) (vf ω) (χh (Rf ω) ω)) ∂(μ W q) ≤
    ENNReal.ofReal C

/-- (9.37) [su:eq:chosen-generator-cut-costs] at a point of the support of the family. -/
theorem srcEnergy_cut_le {W q : ℕ} {g E C M₀ σ : ℝ} {P R : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) {v : Fin W → ℂ}
    {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {χh : Ω W q → (Fin W → ℂ) → ℝ}
    (hF : GenFamily W q g E P R Kh χh) {ω : Ω W q} (hv : v ≠ 0)
    (hpt : χh ω v ≠ 0 → GenPoint W q g E P R v C M₀ σ (Kh ω) ω) :
    srcEnergy P v (fun w => χh ω w • Kh ω w) ≤
      2 * χh ω v ^ 2 * C ^ 2 * (C * W * σ + 2 * W * hsSq (Kh ω v)) +
        2 * (∑ i, ‖(P *ᵥ v) i‖ ^ 2) * hsSq (Kh ω v) * tangGradSq P v (χh ω) := by
  obtain ⟨-, -, -, -, hχC2, ⟨G, hGo, hKC2, hGsupp⟩, -⟩ := hF
  set s : ℝ := ∑ i, ‖(P *ᵥ v) i‖ ^ 2 with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hTG0 : 0 ≤ tangGradSq P v (χh ω) := by
    unfold tangGradSq; positivity
  have hemb : DifferentiableAt ℝ (fun w : Fin W → ℂ => (ω, w)) v :=
    (differentiableAt_const ω).prodMk differentiableAt_id
  have hχd : DifferentiableAt ℝ (χh ω) v := by
    have hopen : IsOpen {p : Ω W q × (Fin W → ℂ) | p.2 ≠ 0} :=
      isOpen_ne_fun continuous_snd continuous_const
    have h1 : ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2) (ω, v) :=
      hχC2.contDiffAt (hopen.mem_nhds hv)
    exact (h1.differentiableAt (by norm_num)).comp v hemb
  by_cases hts : (ω, v) ∈ tsupport (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2)
  · obtain ⟨hGp, -⟩ := hGsupp (ω, v) hts hv
    have hKd : DifferentiableAt ℝ (Kh ω) v := by
      have h1 : ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => Kh p.1 p.2) (ω, v) :=
        hKC2.contDiffAt (hGo.mem_nhds hGp)
      exact (h1.differentiableAt (by norm_num)).comp v hemb
    have hFd : ∀ h, lineDeriv ℝ (fun w => χh ω w • Kh ω w) v h =
        lineDeriv ℝ (χh ω) v h • Kh ω v + χh ω v • lineDeriv ℝ (Kh ω) v h := fun h => by
      rw [(hχd.fun_smul hKd).lineDeriv_eq_fderiv, hχd.lineDeriv_eq_fderiv,
        hKd.lineDeriv_eq_fderiv, fderiv_fun_smul hχd hKd]
      simp [add_comm]
    have hterm : ∀ h, hsSq (lineDeriv ℝ (fun w => χh ω w • Kh ω w) v h) ≤
        2 * (lineDeriv ℝ (χh ω) v h) ^ 2 * hsSq (Kh ω v) +
          2 * χh ω v ^ 2 * hsSq (lineDeriv ℝ (Kh ω) v h) := fun h => by
      rw [hFd]
      refine (ChosenGenerator_hsSq_add_le _ _).trans ?_
      rw [ChosenGenerator_hsSq_real_smul, ChosenGenerator_hsSq_real_smul]
      exact le_of_eq (by ring)
    set k : ℝ := hsSq (Kh ω v) with hk
    set X : ℝ := ∑ j, (hsSq (lineDeriv ℝ (Kh ω) v (tangProj P v (Pi.single j 1))) +
      hsSq (lineDeriv ℝ (Kh ω) v (tangProj P v (Pi.single j Complex.I)))) with hX
    have hmain : srcEnergy P v (fun w => χh ω w • Kh ω w) ≤
        2 * s * k * tangGradSq P v (χh ω) + 2 * χh ω v ^ 2 * (s * X) := by
      unfold srcEnergy tangGradSq
      refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
        add_le_add (hterm (tangProj P v (Pi.single j 1)))
          (hterm (tangProj P v (Pi.single j Complex.I)))) hs0).trans (le_of_eq ?_)
      have e : ∀ c : ℝ, ∑ j, ((2 * lineDeriv ℝ (χh ω) v (tangProj P v (Pi.single j 1)) ^ 2 * k +
            2 * c * hsSq (lineDeriv ℝ (Kh ω) v (tangProj P v (Pi.single j 1)))) +
          (2 * lineDeriv ℝ (χh ω) v (tangProj P v (Pi.single j Complex.I)) ^ 2 * k +
            2 * c * hsSq (lineDeriv ℝ (Kh ω) v (tangProj P v (Pi.single j Complex.I))))) =
        2 * k * ∑ j, (lineDeriv ℝ (χh ω) v (tangProj P v (Pi.single j 1)) ^ 2 +
            lineDeriv ℝ (χh ω) v (tangProj P v (Pi.single j Complex.I)) ^ 2) + 2 * c * X := by
        intro c
        rw [hX, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e (χh ω v ^ 2)]
      ring
    by_cases hχ : χh ω v = 0
    · rw [hχ] at hmain ⊢
      refine hmain.trans (le_of_eq ?_)
      ring
    · obtain ⟨hPv, -, -, -, -, -, -, ⟨Es, hEs, hfin, hb1, hb2⟩, -, -⟩ := hpt hχ
      have hE := ChosenGenerator_energy_bound hP hPP hPv
        (fderiv ℝ (Kh ω) v : (Fin W → ℂ) →ₗ[ℝ] Matrix (Fin W) (Fin W) ℂ) Es hEs (C ^ 2)
        (C ^ 2 * k) (mul_nonneg (sq_nonneg C) (ChosenGenerator_hsSq_nonneg _))
        (fun w h1 h2 => by
          have := hb1 w h1 h2
          rwa [hKd.lineDeriv_eq_fderiv] at this)
        (fun w h1 h2 h3 => by
          have := hb2 w h1 h2 h3
          rwa [hKd.lineDeriv_eq_fderiv] at this)
      have hXe : X = ∑ j, (hsSq ((fderiv ℝ (Kh ω) v : (Fin W → ℂ) →ₗ[ℝ] Matrix (Fin W) (Fin W) ℂ)
            (tangProj P v (Pi.single j 1))) +
          hsSq ((fderiv ℝ (Kh ω) v : (Fin W → ℂ) →ₗ[ℝ] Matrix (Fin W) (Fin W) ℂ)
            (tangProj P v (Pi.single j Complex.I)))) := by
        rw [hX]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hKd.lineDeriv_eq_fderiv, hKd.lineDeriv_eq_fderiv]
        rfl
      rw [← hXe] at hE
      have hX' : s * X ≤ C ^ 2 * (C * W * σ + 2 * W * k) := by
        have h1 : C ^ 2 * (Module.finrank ℝ Es : ℝ) ≤ C ^ 2 * (C * W * σ) :=
          mul_le_mul_of_nonneg_left hfin (sq_nonneg C)
        nlinarith [hE, h1]
      calc srcEnergy P v (fun w => χh ω w • Kh ω w)
          ≤ 2 * s * k * tangGradSq P v (χh ω) + 2 * χh ω v ^ 2 * (s * X) := hmain
        _ ≤ 2 * s * k * tangGradSq P v (χh ω) +
              2 * χh ω v ^ 2 * (C ^ 2 * (C * W * σ + 2 * W * k)) :=
            add_le_add_right (mul_le_mul_of_nonneg_left hX' (by positivity)) _
        _ = _ := by ring
  · -- the cutoff vanishes near `v`
    have hev : (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2) =ᶠ[nhds (ω, v)] 0 :=
      notMem_tsupport_iff_eventuallyEq.1 hts
    have hχ0 : χh ω v = 0 := hev.self_of_nhds
    have hev2 : (fun w => χh ω w • Kh ω w) =ᶠ[nhds v] fun _ => (0 : Matrix (Fin W) (Fin W) ℂ) := by
      filter_upwards [hemb.continuousAt.tendsto.eventually hev] with w hw
      simp [hw]
    have hz : ∀ h, lineDeriv ℝ (fun w => χh ω w • Kh ω w) v h = 0 := fun h => by
      rw [hev2.lineDeriv_eq,
        (differentiableAt_const (0 : Matrix (Fin W) (Fin W) ℂ)).lineDeriv_eq_fderiv]
      simp
    have h0 : srcEnergy P v (fun w => χh ω w • Kh ω w) = 0 := by
      unfold srcEnergy
      simp [hz, hsSq]
    rw [h0, hχ0]
    have h1 : 2 * (0 : ℝ) ^ 2 * C ^ 2 * (C * W * σ + 2 * W * hsSq (Kh ω v)) = 0 := by ring
    have := ChosenGenerator_hsSq_nonneg (Kh ω v)
    rw [h1, zero_add]
    positivity

/-- The terminal correction (Section 9.3 [su:sec:generator-bounds]):
`W g⁴ ‖[χ L, R_{q-1}]‖²_HS ≤ 36 C⁴ W⁻¹ g⁴` at the pointwise clauses of Lemma 9.3
[su:lem:chosen-generator], for `0 ≤ χ ≤ 1`. -/
theorem terminal_corr_le {W q : ℕ} {g E C M₀ σ χ : ℝ} (hW : 1 ≤ W) (hC : 0 ≤ C)
    (hχ : 0 ≤ χ ∧ χ ≤ 1) {P R : Matrix (Fin W) (Fin W) ℂ} {v : Fin W → ℂ}
    {Kv : (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {ω : Ω W q}
    (hpt : GenPoint W q g E P R v C M₀ σ Kv ω) :
    (W : ℝ) * g ^ 4 * hsSq ((χ : ℂ) • smallCorr W g E q R v (Kv v) ω * chartR W g E q R ω (q - 1) -
        chartR W g E q R ω (q - 1) * (χ : ℂ) • smallCorr W g E q R v (Kv v) ω) ≤
      36 * C ^ 4 * (W : ℝ)⁻¹ * g ^ 4 := by
  have _ := hC
  obtain ⟨hPv, -, -, -, hunit, -, hmatch, -, hR, -⟩ := hpt
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hv0 : v ≠ 0 := fun h => hPv (by simp [h])
  have hprod : IsUnit (chartProd W g E q R ω (q - 1)) :=
    ChosenGenerator_isUnit_chartProd W g E q R ω (q - 1) fun k hk hkq => hunit k hk hkq
  have hu : chartProd W g E q R ω (q - 1) *ᵥ v ≠ 0 := by
    intro h
    exact hv0 (Matrix.mulVec_injective_iff_isUnit.2 hprod (by simpa using h))
  have hs : 0 < ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 (by simpa using hi)) 2) <|
      Finset.single_le_sum (f := fun i => ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ i)
  have hrpow : (W : ℝ) ^ (-8 : ℝ) = ((W : ℝ) ^ 8)⁻¹ := by
    rw [Real.rpow_neg hW0.le, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hL : hsSq (smallCorr W g E q R v (Kv v) ω) ≤ 9 * (C ^ 2 * ((W : ℝ) ^ 8)⁻¹) := by
    have h1 := hsSq_rotCorr_le hu (chartProd W g E q R ω (q - 1) *ᵥ (Kv v *ᵥ v) -
      chartProd W g E q R ω (q - 1) *ᵥ v)
    refine h1.trans ?_
    rw [div_le_iff₀ hs]
    rw [hrpow] at hmatch
    nlinarith [hmatch]
  set L := smallCorr W g E q R v (Kv v) ω with hLdef
  set Rq := chartR W g E q R ω (q - 1) with hRq
  have hcomm : (χ : ℂ) • L * Rq - Rq * (χ : ℂ) • L = (χ : ℂ) • (L * Rq - Rq * L) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  have hRsq : ‖Rq‖ ^ 2 ≤ (C * (W : ℝ) ^ 3) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hR 2
  have hLR : hsSq (L * Rq) ≤ hsSq L * (C * (W : ℝ) ^ 3) ^ 2 :=
    (ChosenGenerator_hsSq_mul_opNorm_le L Rq).trans
      (mul_le_mul_of_nonneg_left hRsq (ChosenGenerator_hsSq_nonneg L))
  have hRL : hsSq (Rq * L) ≤ hsSq L * (C * (W : ℝ) ^ 3) ^ 2 :=
    (ChosenGenerator_hsSq_opNorm_mul_le Rq L).trans <| by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hRsq (ChosenGenerator_hsSq_nonneg L)
  have hcm : hsSq (L * Rq - Rq * L) ≤ 4 * (hsSq L * (C * (W : ℝ) ^ 3) ^ 2) := by
    have := ChosenGenerator_hsSq_sub_le (L * Rq) (Rq * L)
    linarith
  have hχ2 : χ ^ 2 ≤ 1 := by nlinarith [hχ.1, hχ.2]
  have hA : hsSq ((χ : ℂ) • L * Rq - Rq * (χ : ℂ) • L) ≤
      4 * (9 * (C ^ 2 * ((W : ℝ) ^ 8)⁻¹)) * (C * (W : ℝ) ^ 3) ^ 2 := by
    rw [hcomm, ChosenGenerator_hsSq_ofReal_smul]
    have h0 := ChosenGenerator_hsSq_nonneg (L * Rq - Rq * L)
    have h1 : χ ^ 2 * hsSq (L * Rq - Rq * L) ≤ hsSq (L * Rq - Rq * L) := by
      nlinarith
    have hsq := sq_nonneg (C * (W : ℝ) ^ 3)
    nlinarith [mul_le_mul_of_nonneg_right hL hsq]
  have hg4 : 0 ≤ (W : ℝ) * g ^ 4 := by positivity
  calc (W : ℝ) * g ^ 4 * hsSq ((χ : ℂ) • L * Rq - Rq * (χ : ℂ) • L)
      ≤ (W : ℝ) * g ^ 4 * (4 * (9 * (C ^ 2 * ((W : ℝ) ^ 8)⁻¹)) * (C * (W : ℝ) ^ 3) ^ 2) :=
        mul_le_mul_of_nonneg_left hA hg4
    _ = 36 * C ^ 4 * (W : ℝ)⁻¹ * g ^ 4 := by
        field_simp
        ring

end LSBA
