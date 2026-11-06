import LSBA.Spectral.EigCorr
import LSBA.Spectral.Resolvent

/-!
# Rank-one perturbations of a Hermitian matrix at one diagonal entry

The family `K + v e_x e_x^*`; the eigenvector identity behind the spectral
integral representation in [ASFH, proof of Theorem A.1]; and the first Hölder step of that proof
with its `L²` normalization, pointwise: for `0 < α ≤ 1`,
`Q_{xy}(J) ≤ (|v - v'|^α Σ_{λ_k ∈ J} |ψ_k(x)|² |G'_{xy}(λ_k)|^α)^{1/(2-α)}`, where `G'` is the
resolvent of `K + v' e_x e_x^*`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rank-one family `K + v e_x e_x^*`. -/
def rankOnePert (K : Matrix n n ℂ) (x : n) (v : ℝ) : Matrix n n ℂ :=
  K + Matrix.single x x (v : ℂ)

theorem rankOnePert_isHermitian {K : Matrix n n ℂ} (hK : K.IsHermitian) (x : n) (v : ℝ) :
    (rankOnePert K x v).IsHermitian := by
  unfold rankOnePert
  refine hK.add ?_
  ext i j
  by_cases h : x = j ∧ x = i
  · obtain ⟨rfl, rfl⟩ := h
    simp [Matrix.conjTranspose_apply]
  · have h' : ¬ (x = i ∧ x = j) := fun h2 => h ⟨h2.2, h2.1⟩
    simp [Matrix.conjTranspose_apply, h, h']

/-- The family is the line `K + v P_{{x}}` through the coordinate projection. -/
theorem rankOnePert_eq_add_smul_coordProj (K : Matrix n n ℂ) (x : n) (v : ℝ) :
    rankOnePert K x v = K + ((1 * v : ℝ) : ℂ) • coordProj ({x} : Finset n) := by
  unfold rankOnePert coordProj
  congr 1
  ext i j
  simp only [Matrix.single_apply, Matrix.smul_apply, Matrix.diagonal_apply, Finset.mem_singleton,
    smul_eq_mul]
  by_cases h : x = i ∧ x = j
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · by_cases hij : i = j
    · subst hij
      have h1 : ¬ x = i := fun h1 => h ⟨h1, h1⟩
      have h2 : ¬ i = x := fun h2 => h1 h2.symm
      simp [h1, h2]
    · simp [h, hij]

/-- `(H + c e_x e_x^* - λ_k) ψ_k = c ψ_k(x) e_x` for an eigenpair `(λ_k, ψ_k)` of `H`. -/
private lemma rankOne_add_single_sub_mulVec {H : Matrix n n ℂ} (hH : H.IsHermitian) (x k : n)
    (c : ℝ) :
    (H + Matrix.single x x (c : ℂ) - ((hH.eigenvalues k : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ
        ⇑(hH.eigenvectorBasis k) =
      ((c : ℂ) * hH.eigenvectorBasis k x) • Pi.single x (1 : ℂ) := by
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, hH.mulVec_eigenvectorBasis, Matrix.single_mulVec_eq,
    Matrix.smul_mulVec, Matrix.one_mulVec, Complex.coe_smul]
  simp

omit [Fintype n] in
/-- The matrix `H - λ` of a Hermitian `H` and a real `λ` is Hermitian. -/
private lemma rankOne_sub_smul_one_isHermitian {H : Matrix n n ℂ} (hH : H.IsHermitian) (l : ℝ) :
    (H - (l : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH.eq]
  simp

/-- If `E` is an eigenvalue of `H` of multiplicity one with eigenvector `ψ`, `ψ(x) ≠ 0` and
`c ≠ 0`, then `H + c e_x e_x^* - E` is invertible. -/
private lemma rankOne_det_add_single_sub_ne_zero {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (hinj : Function.Injective hH.eigenvalues) (x k : n) (hk : hH.eigenvectorBasis k x ≠ 0)
    {c : ℝ} (hc : c ≠ 0) :
    (H + Matrix.single x x (c : ℂ) - ((hH.eigenvalues k : ℝ) : ℂ) • (1 : Matrix n n ℂ)).det ≠
      0 := by
  intro hdet
  obtain ⟨φ, hφ0, hφ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set M : Matrix n n ℂ := H - ((hH.eigenvalues k : ℝ) : ℂ) • (1 : Matrix n n ℂ) with hMdef
  have hMh : Mᴴ = M := (rankOne_sub_smul_one_isHermitian hH _).eq
  have hMψ : ∀ j, M *ᵥ ⇑(hH.eigenvectorBasis j) =
      ((hH.eigenvalues j - hH.eigenvalues k : ℝ) : ℂ) • ⇑(hH.eigenvectorBasis j) := by
    intro j
    rw [hMdef, Matrix.sub_mulVec, hH.mulVec_eigenvectorBasis, Matrix.smul_mulVec,
      Matrix.one_mulVec, Complex.coe_smul, ← sub_smul]
    exact (Complex.coe_smul _ _).symm
  have hMφ : M *ᵥ φ = -((c : ℂ) * φ x) • Pi.single x (1 : ℂ) := by
    have h1 : (M + Matrix.single x x (c : ℂ)) *ᵥ φ = 0 := by
      have : M + Matrix.single x x (c : ℂ) =
          H + Matrix.single x x (c : ℂ) - ((hH.eigenvalues k : ℝ) : ℂ) • (1 : Matrix n n ℂ) := by
        rw [hMdef]
        abel
      rw [this]
      exact hφ
    rw [Matrix.add_mulVec, Matrix.single_mulVec_eq] at h1
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h1
  have hpair : ∀ j, star (⇑(hH.eigenvectorBasis j)) ⬝ᵥ (M *ᵥ φ) =
      ((hH.eigenvalues j - hH.eigenvalues k : ℝ) : ℂ) * (star (⇑(hH.eigenvectorBasis j)) ⬝ᵥ φ) := by
    intro j
    rw [Matrix.dotProduct_mulVec]
    have : star (⇑(hH.eigenvectorBasis j)) ᵥ* M = star (M *ᵥ ⇑(hH.eigenvectorBasis j)) := by
      rw [Matrix.star_mulVec, hMh]
    rw [this, hMψ, star_smul, smul_dotProduct, smul_eq_mul]
    simp
  have hφx : φ x = 0 := by
    have h0 := hpair k
    rw [hMφ] at h0
    simp only [neg_smul, dotProduct_neg, dotProduct_smul, dotProduct_single, Pi.star_apply,
      RCLike.star_def, mul_one, smul_eq_mul, sub_self, Complex.ofReal_zero, zero_mul, neg_eq_zero,
      mul_eq_zero, Complex.ofReal_eq_zero, map_eq_zero] at h0
    rcases h0 with (h0 | h0) | h0
    · exact absurd h0 hc
    · exact h0
    · exact absurd h0 hk
  have hMφ0 : M *ᵥ φ = 0 := by
    rw [hMφ, hφx]
    simp
  have hcj : ∀ j, j ≠ k → star (⇑(hH.eigenvectorBasis j)) ⬝ᵥ φ = 0 := by
    intro j hj
    have h0 := hpair j
    rw [hMφ0] at h0
    simp only [dotProduct_zero] at h0
    replace h0 : (0 : ℂ) = _ := h0
    have hne : ((hH.eigenvalues j - hH.eigenvalues k : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, sub_ne_zero]
      exact fun h => hj (hinj h)
    exact (mul_eq_zero.mp h0.symm).resolve_left hne
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hφU : ∀ i, φ i = U i k * (star (⇑(hH.eigenvectorBasis k)) ⬝ᵥ φ) := by
    intro i
    have h1 : φ = U *ᵥ (star U *ᵥ φ) := by rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
    have h2 : ∀ j, (star U *ᵥ φ) j = star (⇑(hH.eigenvectorBasis j)) ⬝ᵥ φ := fun j => rfl
    have h3 : φ i = ∑ j, U i j * (star U *ᵥ φ) j := by
      conv_lhs => rw [h1]
      rfl
    rw [h3, Finset.sum_eq_single k]
    · rw [h2]
    · intro j _ hj
      rw [h2, hcj j hj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hUxk : U x k = hH.eigenvectorBasis k x := rfl
  have hck : star (⇑(hH.eigenvectorBasis k)) ⬝ᵥ φ = 0 := by
    have h1 := hφU x
    rw [hφx, hUxk] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hk
  apply hφ0
  ext i
  rw [hφU i, hck, mul_zero]
  rfl

/-- The eigenvector identity behind the spectral integral representation in
[ASFH, proof of Theorem A.1]: on
simple spectrum of `K + v e_x e_x^*`, if `v' ≠ v` and `ψ_k(x) ≠ 0`, then `λ_k` is not an
eigenvalue of `K + v' e_x e_x^*` and `ψ_k(y) = (v' - v) ψ_k(x) G'_{yx}(λ_k)`. -/
theorem eigenvectorBasis_rankOnePert_apply {K : Matrix n n ℂ} (hK : K.IsHermitian) (x y : n)
    {v v' : ℝ} (hvv : v ≠ v')
    (hinj : Function.Injective (rankOnePert_isHermitian hK x v).eigenvalues) (k : n)
    (hk : (rankOnePert_isHermitian hK x v).eigenvectorBasis k x ≠ 0) :
    (rankOnePert K x v' - (((rankOnePert_isHermitian hK x v).eigenvalues k : ℝ) : ℂ) •
        (1 : Matrix n n ℂ)).det ≠ 0 ∧
      (rankOnePert_isHermitian hK x v).eigenvectorBasis k y =
        ((v' - v : ℝ) : ℂ) * (rankOnePert_isHermitian hK x v).eigenvectorBasis k x *
          resolventMat (rankOnePert K x v') ((rankOnePert_isHermitian hK x v).eigenvalues k) y x :=
  by
  have hH' : rankOnePert K x v' =
      rankOnePert K x v + Matrix.single x x (((v' - v : ℝ)) : ℂ) := by
    unfold rankOnePert
    rw [add_assoc, ← Matrix.single_add]
    congr 3
    push_cast
    ring
  have hc : (v' - v : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hvv)
  have hdet := rankOne_det_add_single_sub_ne_zero (rankOnePert_isHermitian hK x v) hinj x k hk hc
  have hmul := rankOne_add_single_sub_mulVec (rankOnePert_isHermitian hK x v) x k (v' - v)
  rw [← hH'] at hdet hmul
  refine ⟨hdet, ?_⟩
  set A : Matrix n n ℂ := rankOnePert K x v' -
    (((rankOnePert_isHermitian hK x v).eigenvalues k : ℝ) : ℂ) • (1 : Matrix n n ℂ) with hA
  have key : ⇑((rankOnePert_isHermitian hK x v).eigenvectorBasis k) =
      A⁻¹ *ᵥ (A *ᵥ ⇑((rankOnePert_isHermitian hK x v).eigenvectorBasis k)) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  rw [hmul] at key
  have := congrFun key y
  rw [this, Matrix.mulVec_smul, Pi.smul_apply, Matrix.mulVec_single_one, smul_eq_mul]
  rfl


/-- Hölder's inequality for the weights `W` with `Σ_k W_k A_k² ≤ 1`, in the form
`Σ_k W_k A_k ≤ (Σ_k W_k A_k^α)^{1/(2-α)}` for `0 < α ≤ 1`, with both sums over the indices
satisfying `P`. -/
private lemma rankOne_holder {ι : Type*} [Fintype ι] (P : ι → Prop) (W A : ι → ℝ≥0∞) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hB : ∑ k, W k * A k ^ (2 : ℝ) ≤ 1) :
    ∑ k, (if P k then W k * A k else 0) ≤
      (∑ k, if P k then W k * A k ^ α else 0) ^ (1 / (2 - α)) := by
  classical
  rcases hα1.eq_or_lt with rfl | hα1
  · norm_num
  have h1α : 0 < 1 - α := sub_pos.mpr hα1
  have h2α : 0 < 2 - α := by linarith
  set p : ℝ := (2 - α) / (1 - α) with hp
  have hp1 : 1 ≤ p := by
    rw [hp, le_div_iff₀ h1α]
    linarith
  have hpinv : p⁻¹ = (1 - α) / (2 - α) := by rw [hp, inv_div]
  have hp1' : 1 - p⁻¹ = 1 / (2 - α) := by
    rw [hpinv]
    field_simp
    ring
  have key := ENNReal.inner_le_weight_mul_Lp_of_nonneg (Finset.univ : Finset ι) hp1
    (fun k => if P k then W k * A k ^ α else 0) (fun k => A k ^ (1 - α))
  have hL : ∑ k, (if P k then W k * A k ^ α else 0) * A k ^ (1 - α) =
      ∑ k, (if P k then W k * A k else 0) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : P k
    · simp only [hk, ite_true]
      rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hα0.le h1α.le]
      simp
    · simp [hk]
  have hR : ∑ k, (if P k then W k * A k ^ α else 0) * (A k ^ (1 - α)) ^ p ≤ 1 := by
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) hB
    by_cases hk : P k
    · simp only [hk, ite_true]
      rw [mul_assoc, ← ENNReal.rpow_mul, ← ENNReal.rpow_add_of_nonneg _ _ hα0.le
        (mul_nonneg h1α.le (by positivity))]
      have : α + (1 - α) * p = 2 := by
        rw [hp]
        field_simp
        ring
      rw [this]
    · simp [hk]
  rw [hL, hp1'] at key
  refine key.trans ?_
  calc _ ≤ (∑ k, if P k then W k * A k ^ α else 0) ^ (1 / (2 - α)) * 1 := by
        gcongr
        exact ENNReal.rpow_le_one hR (by positivity)
    _ = _ := mul_one _

/-- For an orthonormal eigenbasis, `Σ_k |ψ_k(i)|² = 1` for every coordinate `i`. -/
private lemma rankOne_sum_sq_eq_one {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) :
    ∑ k, ‖hA.eigenvectorBasis k i‖ ^ 2 = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have h2 := congrFun (congrFun h i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def] at h2
  have h3 : ∀ k, hA.eigenvectorUnitary.1 i k * (starRingEnd ℂ) (hA.eigenvectorUnitary.1 i k) =
      ((‖hA.eigenvectorBasis k i‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  simp only [h3] at h2
  exact_mod_cast h2

/-- The resolvent of a Hermitian matrix at a real energy is Hermitian: `|G_{yx}| = |G_{xy}|`. -/
private lemma rankOne_norm_resolventMat_swap {H : Matrix n n ℂ} (hH : H.IsHermitian) (E : ℝ)
    (x y : n) : ‖resolventMat H (E : ℂ) y x‖ = ‖resolventMat H (E : ℂ) x y‖ := by
  have h : (resolventMat H (E : ℂ))ᴴ = resolventMat H (E : ℂ) := by
    unfold resolventMat
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hH.eq]
    simp
  have h2 := congrFun (congrFun h x) y
  rw [Matrix.conjTranspose_apply] at h2
  rw [← h2]
  simp

/-- For every eigenpair `(λ_k, ψ_k)` of `K + v e_x e_x^*`:
`|ψ_k(x)||ψ_k(y)| = |ψ_k(x)|² |v-v'||G'_{xy}(λ_k)|` and the termwise form of the `L²` normalization,
`|ψ_k(x)|² (|v-v'||G'_{xy}(λ_k)|)² ≤ |ψ_k(y)|²`. -/
private lemma rankOne_term {K : Matrix n n ℂ} (hK : K.IsHermitian) (x y : n) {v v' : ℝ}
    (hvv : v ≠ v') (hinj : Function.Injective (rankOnePert_isHermitian hK x v).eigenvalues)
    (k : n) :
    ‖(rankOnePert_isHermitian hK x v).eigenvectorBasis k x‖ *
        ‖(rankOnePert_isHermitian hK x v).eigenvectorBasis k y‖ =
      ‖(rankOnePert_isHermitian hK x v).eigenvectorBasis k x‖ ^ 2 *
        (‖v - v'‖ * ‖resolventMat (rankOnePert K x v')
          (((rankOnePert_isHermitian hK x v).eigenvalues k : ℝ) : ℂ) x y‖) ∧
    ‖(rankOnePert_isHermitian hK x v).eigenvectorBasis k x‖ ^ 2 *
        (‖v - v'‖ * ‖resolventMat (rankOnePert K x v')
          (((rankOnePert_isHermitian hK x v).eigenvalues k : ℝ) : ℂ) x y‖) ^ 2 ≤
      ‖(rankOnePert_isHermitian hK x v).eigenvectorBasis k y‖ ^ 2 := by
  by_cases hk : (rankOnePert_isHermitian hK x v).eigenvectorBasis k x = 0
  · simp [hk]
  · have h2 := (eigenvectorBasis_rankOnePert_apply hK x y hvv hinj k hk).2
    have hn : ‖(rankOnePert_isHermitian hK x v).eigenvectorBasis k y‖ =
        ‖v - v'‖ * ‖(rankOnePert_isHermitian hK x v).eigenvectorBasis k x‖ *
          ‖resolventMat (rankOnePert K x v')
            (((rankOnePert_isHermitian hK x v).eigenvalues k : ℝ) : ℂ) x y‖ := by
      rw [h2, norm_mul, norm_mul, Complex.norm_real, norm_sub_rev,
        rankOne_norm_resolventMat_swap (rankOnePert_isHermitian hK x v') _ x y]
    rw [hn]
    constructor
    · ring
    · apply le_of_eq
      ring

/-- The first Hölder step of [ASFH, proof of Theorem A.1] with its `L²` normalization,
pointwise: on simple spectrum, for `v' ≠ v` and `0 < α ≤ 1`,
`Q_{xy}(J) ≤ (|v - v'|^α Σ_{λ_k ∈ J} |ψ_k(x)|² |G'_{xy}(λ_k)|^α)^{1/(2-α)}`. -/
theorem eigCorr_rankOnePert_le {K : Matrix n n ℂ} (hK : K.IsHermitian) (x y : n) {v v' : ℝ}
    (hvv : v ≠ v') (hinj : Function.Injective (rankOnePert_isHermitian hK x v).eigenvalues)
    (J : Set ℝ) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ENNReal.ofReal (eigCorr (rankOnePert K x v) J x y) ≤
      (‖v - v'‖ₑ ^ α * eigMassSum (rankOnePert K x v) {x}
        (J.indicator fun E => ‖resolventMat (rankOnePert K x v') E x y‖ₑ ^ α)) ^
          (1 / (2 - α)) := by
  have hH := rankOnePert_isHermitian hK x v
  have hterm := rankOne_term hK x y hvv hinj
  have hQ : ENNReal.ofReal (eigCorr (rankOnePert K x v) J x y) =
      ∑ k, if hH.eigenvalues k ∈ J then
        ENNReal.ofReal (‖hH.eigenvectorBasis k x‖ ^ 2) *
          (‖v - v'‖ₑ * ‖resolventMat (rankOnePert K x v') (hH.eigenvalues k : ℂ) x y‖ₑ) else 0 := by
    unfold eigCorr
    simp only [hH, ↓reduceDIte]
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by split_ifs <;> positivity)]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · rw [(hterm k).1, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ofReal_norm, ofReal_norm]
    · simp
  have hS : ‖v - v'‖ₑ ^ α * eigMassSum (rankOnePert K x v) {x}
        (J.indicator fun E => ‖resolventMat (rankOnePert K x v') E x y‖ₑ ^ α) =
      ∑ k, if hH.eigenvalues k ∈ J then
        ENNReal.ofReal (‖hH.eigenvectorBasis k x‖ ^ 2) *
          (‖v - v'‖ₑ * ‖resolventMat (rankOnePert K x v') (hH.eigenvalues k : ℂ) x y‖ₑ) ^ α
        else 0 := by
    unfold eigMassSum
    simp only [hH, ↓reduceDIte]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Finset.sum_singleton, Set.indicator_apply]
    split_ifs
    · rw [ENNReal.mul_rpow_of_nonneg _ _ hα0.le]
      ring
    · simp
  have hB : ∑ k, ENNReal.ofReal (‖hH.eigenvectorBasis k x‖ ^ 2) *
      (‖v - v'‖ₑ * ‖resolventMat (rankOnePert K x v') (hH.eigenvalues k : ℂ) x y‖ₑ) ^ (2 : ℝ) ≤
        1 := by
    calc _ ≤ ∑ k, ENNReal.ofReal (‖hH.eigenvectorBasis k y‖ ^ 2) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [ENNReal.rpow_two, ← ofReal_norm, ← ofReal_norm,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hterm k).2
      _ = 1 := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity),
            rankOne_sum_sq_eq_one hH, ENNReal.ofReal_one]
  rw [hQ, hS]
  exact rankOne_holder (fun k => hH.eigenvalues k ∈ J) _ _ hα0 hα1 hB

end LSBA
