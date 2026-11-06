import LSBA.Upper.ProjExp
import LSBA.Upper.RicChain
import LSBA.Spectral.SchattenBand

/-!
# The killed product moment

Lemma G.2 [us:lem:product], (G.6) [us:eq:product], proved in Appendix G.3
[app:product-moment-proof]. Fix `h ≥ 1`, `0 < p < 2/(h + 1)` and `e > 0`. For a deterministic
regular state `R_4` (9.3) [us:eq:regular] and independent GUE blocks `V_5, …, V_{h+4}`, the
product `R_{h+4} ⋯ R_5` of the chain `R_j = (V_j - E - g² R_{j-1})⁻¹` satisfies
`Tr |R_{h+4} ⋯ R_5|^p ≤ W^{1+e}` except with probability `C (W^{-δ₀} + g^{1/2})`, uniformly in
`|E| ≤ 2 - κ₀`, `0 < g ≤ g₀` and the regular `R_4`. The good event `{Tr |·|^p ≤ W^{1+e}}` is
invariant under simultaneous conjugation of `R_4, V_5, …, V_{h+4}`.

The chain is `ricChain` on the blocks of `Ω W h`, started at `R_4`. The proof kills a step where
the inverse norm exceeds `W^{1+δ}`, the outgoing state is not regular, or a dyadic count exceeds
`C W^{1+δ} 2^{-l}`; splits each killed state into dyadic bands; bounds the Hilbert–Schmidt moment
of a band product by (G.7) [us:eq:projexp] and its rank by the counts; and sums the bands with the
power-mean and band-summation inequalities for `Tr |·|^p`. The lower bound `W^{-b} ≤ g` of (G.5)
[us:eq:preliminary-range] is not used.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Spectral calculus in an eigenbasis -/

/-- `U diag(d) U*`. -/
private def pmConj {W : ℕ} (U : Matrix (Fin W) (Fin W) ℂ) (d : Fin W → ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  U * Matrix.diagonal d * Uᴴ

/-- `U diag(d) U* · U diag(e) U* = U diag(d e) U*` for `U*U = 1`. -/
private lemma pmConj_mul {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : Uᴴ * U = 1)
    (d e : Fin W → ℂ) : pmConj U d * pmConj U e = pmConj U (fun k => d k * e k) := by
  unfold pmConj
  calc U * Matrix.diagonal d * Uᴴ * (U * Matrix.diagonal e * Uᴴ)
      = U * Matrix.diagonal d * (Uᴴ * U) * Matrix.diagonal e * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun k => d k * e k) * Uᴴ := by
        rw [hU, Matrix.mul_one, Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]

/-- `(U diag(d) U*)⁻¹ = U diag(d⁻¹) U*` for unitary `U` and nonzero `d`. -/
private lemma pmConj_inv {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU1 : Uᴴ * U = 1)
    (hU2 : U * Uᴴ = 1) {d : Fin W → ℂ} (hd : ∀ k, d k ≠ 0) :
    (pmConj U d)⁻¹ = pmConj U (fun k => (d k)⁻¹) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [pmConj_mul hU1]
  simp only [mul_inv_cancel₀ (hd _)]
  unfold pmConj
  rw [Matrix.diagonal_one, Matrix.mul_one, hU2]

/-- `U diag(d) U* (U b) = U (d b)` for `U*U = 1`. -/
private lemma pmConj_mulVec {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : Uᴴ * U = 1)
    (d b : Fin W → ℂ) : pmConj U d *ᵥ (U *ᵥ b) = U *ᵥ (fun k => d k * b k) := by
  unfold pmConj
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hU, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  congr 1
  funext k
  exact Matrix.mulVec_diagonal d b k

/-- `‖U a‖² = Σ |a_k|²` for `U*U = 1`. -/
private lemma pm_l2Norm_sq {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : Uᴴ * U = 1)
    (a : Fin W → ℂ) : l2Norm (U *ᵥ a) ^ 2 = ∑ k, ‖a k‖ ^ 2 := by
  have h1 : l2Norm (U *ᵥ a) ^ 2 = ∑ i, ‖(U *ᵥ a) i‖ ^ 2 := by
    unfold l2Norm
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  have h2 : ∀ v : Fin W → ℂ, ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) = ∑ i, star (v i) * v i := fun v => by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have h3 : star (U *ᵥ a) ⬝ᵥ (U *ᵥ a) = ∑ k, star (a k) * a k := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU,
      Matrix.one_mulVec]; rfl
  rw [h1]
  exact_mod_cast (h2 (U *ᵥ a)).trans (h3.trans (h2 a).symm)

/-- The spectral projection of a Hermitian matrix in its eigenvector basis. -/
private lemma pm_specProj_eq {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian)
    (S : Set ℝ) :
    specProj A S = pmConj (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
      (fun k => if hA.eigenvalues k ∈ S then (1 : ℂ) else 0) := by
  unfold pmConj
  simp only [specProj, hA, ↓reduceDIte]
  ext i j
  rw [Finset.sum_filter, Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : hA.eigenvalues c ∈ S <;> simp [h, Matrix.vecMulVec_apply, mul_comm]

/-- A Hermitian matrix in its eigenvector basis. -/
private lemma pm_spectral {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) :
    A = pmConj (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
      (fun k => (hA.eigenvalues k : ℂ)) := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

/-- `1_{T \ S}(A) = 1_T(A) - 1_S(A)` for `S ⊆ T`. -/
private lemma pm_specProj_diff {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian)
    {S T : Set ℝ} (hST : S ⊆ T) : specProj A (T \ S) = specProj A T - specProj A S := by
  rw [pm_specProj_eq hA, pm_specProj_eq hA, pm_specProj_eq hA]
  unfold pmConj
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  congr 3
  funext k
  by_cases hS : hA.eigenvalues k ∈ S
  · simp [hS, hST hS]
  · by_cases hT : hA.eigenvalues k ∈ T <;> simp [hS, hT]

/-- Every eigenvalue of an invertible Hermitian matrix is nonzero. -/
private lemma pm_eig_ne_zero {W : ℕ} {Γ : Matrix (Fin W) (Fin W) ℂ} (hΓ : Γ.IsHermitian)
    (hdet : IsUnit Γ.det) (k : Fin W) : hΓ.eigenvalues k ≠ 0 := by
  intro hk
  have hdet0 : Γ.det ≠ 0 := hdet.ne_zero
  rw [Matrix.IsHermitian.det_eq_prod_eigenvalues hΓ] at hdet0
  exact Finset.prod_ne_zero_iff.mp hdet0 k (Finset.mem_univ k) (by simp [hk])

/-- The inverse of an invertible Hermitian matrix in its eigenvector basis. -/
private lemma pm_inv_eq {W : ℕ} {Γ : Matrix (Fin W) (Fin W) ℂ} (hΓ : Γ.IsHermitian)
    (hdet : IsUnit Γ.det) : Γ⁻¹ = pmConj (hΓ.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
      (fun k => ((hΓ.eigenvalues k : ℂ))⁻¹) := by
  calc Γ⁻¹ = (pmConj (hΓ.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
        (fun k => (hΓ.eigenvalues k : ℂ)))⁻¹ := by rw [← pm_spectral hΓ]
    _ = _ := pmConj_inv (Matrix.mem_unitaryGroup_iff'.mp hΓ.eigenvectorUnitary.2)
        (Matrix.mem_unitaryGroup_iff.mp hΓ.eigenvectorUnitary.2)
        fun k => by exact_mod_cast pm_eig_ne_zero hΓ hdet k

/-- For a Hermitian `Γ`: if, when `Γ` is invertible, every eigenvalue `λ ∈ S` has `λ ∈ T` and
`λ⁻² ≤ c`, then `‖Γ⁻¹ 1_S(Γ) u‖² ≤ c ‖1_T(Γ) u‖²`. -/
private lemma pm_inv_proj_le {W : ℕ} {Γ : Matrix (Fin W) (Fin W) ℂ} (hΓ : Γ.IsHermitian)
    {S T : Set ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : IsUnit Γ.det → ∀ k, hΓ.eigenvalues k ∈ S →
      (hΓ.eigenvalues k)⁻¹ ^ 2 ≤ c ∧ hΓ.eigenvalues k ∈ T) (u : Fin W → ℂ) :
    l2Norm (Γ⁻¹ *ᵥ (specProj Γ S *ᵥ u)) ^ 2 ≤ c * l2Norm (specProj Γ T *ᵥ u) ^ 2 := by
  by_cases hdet : IsUnit Γ.det
  swap
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hdet, Matrix.zero_mulVec]
    have : l2Norm (0 : Fin W → ℂ) = 0 := by simp [l2Norm]
    rw [this, sq, zero_mul]
    positivity
  set U := (hΓ.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hΓ.eigenvectorUnitary.2
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hΓ.eigenvectorUnitary.2
  obtain ⟨w, rfl⟩ : ∃ w : Fin W → ℂ, u = U *ᵥ w :=
    ⟨Uᴴ *ᵥ u, by rw [Matrix.mulVec_mulVec, hU2, Matrix.one_mulVec]⟩
  rw [pm_specProj_eq hΓ, pm_specProj_eq hΓ, pm_inv_eq hΓ hdet, pmConj_mulVec hU1,
    pmConj_mulVec hU1, pmConj_mulVec hU1, pm_l2Norm_sq hU1, pm_l2Norm_sq hU1, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hS : hΓ.eigenvalues k ∈ S
  · obtain ⟨hk1, hk2⟩ := h hdet k hS
    simp only [hS, hk2, ↓reduceIte, one_mul, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, inv_pow, sq_abs]
    rw [inv_pow] at hk1
    exact mul_le_mul_of_nonneg_right hk1 (by positivity)
  · simp only [hS, ↓reduceIte, zero_mul, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    positivity

/-- For an invertible Hermitian `Γ`, every eigenvalue satisfies `|λ|⁻¹ ≤ ‖Γ⁻¹‖`. -/
private lemma pm_eig_inv_le {W : ℕ} {Γ : Matrix (Fin W) (Fin W) ℂ} (hΓ : Γ.IsHermitian)
    (hdet : IsUnit Γ.det) (k : Fin W) : |hΓ.eigenvalues k|⁻¹ ≤ ‖Γ⁻¹‖ := by
  set U := (hΓ.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hΓ.eigenvectorUnitary.2
  obtain ⟨v, hv⟩ : ∃ v : Fin W → ℂ, v = Pi.single k 1 := ⟨_, rfl⟩
  have hsq : ∀ d : Fin W → ℂ, l2Norm (U *ᵥ (fun i => d i * v i)) ^ 2 = ‖d k‖ ^ 2 :=
    fun d => by
      rw [pm_l2Norm_sq hU1, Finset.sum_eq_single k (fun b _ hb => by simp [hv, hb]) (by simp)]
      simp [hv]
  have h1 := hsq fun i => ((hΓ.eigenvalues i : ℂ))⁻¹
  have h2 := hsq fun _ => 1
  rw [← pmConj_mulVec hU1, ← pm_inv_eq hΓ hdet] at h1
  simp only [one_mul, norm_one, one_pow] at h2
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs] at h1
  have h1' : l2Norm (Γ⁻¹ *ᵥ (U *ᵥ v)) = |hΓ.eigenvalues k|⁻¹ :=
    (pow_left_inj₀ (Real.sqrt_nonneg _) (by positivity) two_ne_zero).mp h1
  have h2' : l2Norm (U *ᵥ v) = 1 :=
    (pow_left_inj₀ (Real.sqrt_nonneg _) zero_le_one two_ne_zero).mp (by rw [one_pow]; exact h2)
  rw [← h1']
  calc l2Norm (Γ⁻¹ *ᵥ (U *ᵥ v)) ≤ ‖Γ⁻¹‖ * l2Norm (U *ᵥ v) := l2Norm_mulVec_le _ _
    _ = ‖Γ⁻¹‖ := by rw [h2', mul_one]

/-- `Σ_k ‖1_S(A) e_k‖² = #{λ ∈ S}` for Hermitian `A`. -/
private lemma pm_sum_col_sq {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian)
    (S : Set ℝ) :
    ∑ k, l2Norm (specProj A S *ᵥ Pi.single k 1) ^ 2 = (countIn A S : ℝ) := by
  obtain ⟨hH, hidem, -, htr⟩ := specProj_spec hA S
  set P := specProj A S
  have h1 : ∀ k, l2Norm (P *ᵥ Pi.single k 1) ^ 2 = ∑ i, ‖P i k‖ ^ 2 := fun k => by
    unfold l2Norm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), Matrix.mulVec_single_one]
    rfl
  simp only [h1]
  have h2 : ((∑ k, ∑ i, ‖P i k‖ ^ 2 : ℝ) : ℂ) = (Pᴴ * P).trace := by
    push_cast
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have h3 : (Pᴴ * P).trace = (countIn A S : ℂ) := by rw [hH.eq, hidem, htr]
  exact_mod_cast h2.trans h3

/-- `countIn` is monotone in the set. -/
private lemma pm_countIn_mono {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) {S T : Set ℝ}
    (hST : S ⊆ T) : countIn A S ≤ countIn A T := by
  unfold countIn
  split_ifs with hA
  · exact Finset.card_le_card (Finset.monotone_filter_right _ fun k _ hk => hST hk)
  · exact le_rfl

/-! ### Bands of the eigenvalues -/

/-- The window `[-β^m, β^m]`. -/
private def pmIcc (β : ℝ) (m : ℕ) : Set ℝ := Set.Icc (-β ^ m) (β ^ m)

/-- The bands of an eigenvalue `λ`: band `0` is `{|λ| > 1} ∪ {|λ| ≤ β^L}` and band `m + 1` is
`{β^{m+1} < |λ| ≤ β^m}`. -/
private def pmBand (β : ℝ) (L : ℕ) : ℕ → Set ℝ
  | 0 => (pmIcc β 0 \ pmIcc β L)ᶜ
  | m + 1 => pmIcc β m \ pmIcc β (m + 1)

private lemma pm_mem_Icc {β x : ℝ} {m : ℕ} : x ∈ pmIcc β m ↔ |x| ≤ β ^ m := by
  simp [pmIcc, abs_le]

private lemma pm_Icc_mono {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {m m' : ℕ} (h : m ≤ m') :
    pmIcc β m' ⊆ pmIcc β m := fun _ hx =>
  pm_mem_Icc.2 ((pm_mem_Icc.1 hx).trans (pow_le_pow_of_le_one hβ0 hβ1 h))

/-- `1_{band 0}(A) = 1 - 1_{[-1,1]}(A) + 1_{[-β^L, β^L]}(A)`. -/
private lemma pm_specProj_band_zero {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (L : ℕ) :
    specProj A (pmBand β L 0) = 1 - specProj A (pmIcc β 0) + specProj A (pmIcc β L) := by
  simp only [pmBand]
  rw [eq_sub_of_add_eq' (specProj_add_compl hA _).1,
    pm_specProj_diff hA (pm_Icc_mono hβ0 hβ1 (Nat.zero_le L))]
  abel

/-- `1_{band m+1}(A) = 1_{[-β^m, β^m]}(A) - 1_{[-β^{m+1}, β^{m+1}]}(A)`. -/
private lemma pm_specProj_band_succ {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (L m : ℕ) :
    specProj A (pmBand β L (m + 1)) = specProj A (pmIcc β m) - specProj A (pmIcc β (m + 1)) :=
  pm_specProj_diff hA (pm_Icc_mono hβ0 hβ1 (Nat.le_succ m))

/-- The band projections of a Hermitian matrix sum to `1`. -/
private lemma pm_sum_band {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (L : ℕ) :
    ∑ l : Fin (L + 1), specProj A (pmBand β L l) = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, pm_specProj_band_succ hA hβ0 hβ1,
    pm_specProj_band_zero hA hβ0 hβ1]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => specProj A (pmIcc β i) - specProj A (pmIcc β (i + 1))) L, Finset.sum_range_sub']
  abel

/-- Band `m + 1`: `‖Γ⁻¹ 1_{band}(Γ) u‖² ≤ β^{-2(m+1)} ‖1_{[-β^m, β^m]}(Γ) u‖²`. -/
private lemma pm_band_succ_le {W : ℕ} {Γ : Matrix (Fin W) (Fin W) ℂ} (hΓ : Γ.IsHermitian)
    {β : ℝ} (hβ : 0 < β) (L m : ℕ) (u : Fin W → ℂ) :
    l2Norm (Γ⁻¹ *ᵥ (specProj Γ (pmBand β L (m + 1)) *ᵥ u)) ^ 2 ≤
      ((β ^ (m + 1))⁻¹) ^ 2 * l2Norm (specProj Γ (pmIcc β m) *ᵥ u) ^ 2 := by
  have hc : ∀ k, hΓ.eigenvalues k ∈ pmBand β L (m + 1) →
      (hΓ.eigenvalues k)⁻¹ ^ 2 ≤ ((β ^ (m + 1))⁻¹) ^ 2 ∧ hΓ.eigenvalues k ∈ pmIcc β m := by
    intro k hk
    change _ ∈ pmIcc β m \ pmIcc β (m + 1) at hk
    refine ⟨?_, hk.1⟩
    have h1 : β ^ (m + 1) < |hΓ.eigenvalues k| := by
      by_contra hc
      exact hk.2 (pm_mem_Icc.2 (not_lt.mp hc))
    have h2 : |hΓ.eigenvalues k|⁻¹ ≤ (β ^ (m + 1))⁻¹ := inv_anti₀ (by positivity) h1.le
    rw [← sq_abs, abs_inv]
    exact pow_le_pow_left₀ (by positivity) h2 2
  exact pm_inv_proj_le hΓ (by positivity) (fun _ => hc) u

/-- Band `0`: if `‖Γ⁻¹‖ < β^{-L}`, then `‖Γ⁻¹ 1_{band 0}(Γ) u‖ ≤ ‖u‖`. -/
private lemma pm_band_zero_le {W : ℕ} {Γ : Matrix (Fin W) (Fin W) ℂ} (hΓ : Γ.IsHermitian)
    {β : ℝ} (L : ℕ) (hn : ‖Γ⁻¹‖ < (β ^ L)⁻¹) (u : Fin W → ℂ) :
    l2Norm (Γ⁻¹ *ᵥ (specProj Γ (pmBand β L 0) *ᵥ u)) ^ 2 ≤ l2Norm u ^ 2 := by
  have hc : IsUnit Γ.det → ∀ k, hΓ.eigenvalues k ∈ pmBand β L 0 →
      (hΓ.eigenvalues k)⁻¹ ^ 2 ≤ 1 ∧ hΓ.eigenvalues k ∈ Set.univ := by
    intro hdet k hk
    refine ⟨?_, Set.mem_univ _⟩
    have habs : 0 < |hΓ.eigenvalues k| := abs_pos.2 (pm_eig_ne_zero hΓ hdet k)
    rw [← sq_abs, abs_inv]
    change _ ∈ (pmIcc β 0 \ pmIcc β L)ᶜ at hk
    simp only [Set.mem_compl_iff, Set.mem_sdiff, not_and_or, not_not] at hk
    rcases hk with hk | hk
    · have h1 : 1 < |hΓ.eigenvalues k| := by
        by_contra hc
        exact hk (pm_mem_Icc.2 (by simpa using not_lt.mp hc))
      have h2 : |hΓ.eigenvalues k|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1.le
      nlinarith [inv_nonneg.2 habs.le]
    · exfalso
      have h1 : (β ^ L)⁻¹ ≤ |hΓ.eigenvalues k|⁻¹ := inv_anti₀ habs (pm_mem_Icc.1 hk)
      exact absurd ((h1.trans (pm_eig_inv_le hΓ hdet k)).trans_lt hn) (lt_irrefl _)
  have h := pm_inv_proj_le hΓ zero_le_one hc u
  rwa [(specProj_add_compl hΓ ∅).2, Matrix.one_mulVec, one_mul] at h

/-- A matrix-valued map is measurable if its entries are. -/
private lemma pm_meas {W : ℕ} {α : Type*} [MeasurableSpace α] {F : α → Matrix (Fin W) (Fin W) ℂ}
    (h : ∀ i j, Measurable fun x => F x i j) : Measurable F :=
  Measurable.of_eval_matrix F h

/-- `x ↦ 1_{band m}(G x)` is measurable for measurable Hermitian-valued `G`. -/
private lemma pm_measurable_band {W : ℕ} {α : Type*} [MeasurableSpace α]
    {G : α → Matrix (Fin W) (Fin W) ℂ} (hG : Measurable G) (hH : ∀ x, (G x).IsHermitian)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (L m : ℕ) :
    Measurable fun x => specProj (G x) (pmBand β L m) := by
  have hP : ∀ m' i j, Measurable fun x => specProj (G x) (pmIcc β m') i j := fun m' i j =>
    ((measurable_specProj isClosed_Icc).comp hG).eval_matrix
  cases m with
  | zero =>
    have e : (fun x => specProj (G x) (pmBand β L 0)) =
        fun x => 1 - specProj (G x) (pmIcc β 0) + specProj (G x) (pmIcc β L) :=
      funext fun x => pm_specProj_band_zero (hH x) hβ0 hβ1 L
    rw [e]
    refine pm_meas fun i j => ?_
    simp only [Matrix.add_apply, Matrix.sub_apply]
    exact (measurable_const.sub (hP 0 i j)).add (hP L i j)
  | succ m =>
    have e : (fun x => specProj (G x) (pmBand β L (m + 1))) =
        fun x => specProj (G x) (pmIcc β m) - specProj (G x) (pmIcc β (m + 1)) :=
      funext fun x => pm_specProj_band_succ (hH x) hβ0 hβ1 L m
    rw [e]
    refine pm_meas fun i j => ?_
    simp only [Matrix.sub_apply]
    exact (hP m i j).sub (hP (m + 1) i j)

/-! ### The chain: measurability and dependence on earlier blocks -/

/-- The fresh matrix `Γ_j = V_j - E - g² R_j` of the chain, so that `R_{j+1} = Γ_j⁻¹`. -/
private def pmGam (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W h) (j : ℕ) :
    Matrix (Fin W) (Fin W) ℂ :=
  (if hj : j < h then gueBlock W h ω ⟨j, hj⟩ else 0) - (E : ℂ) • 1 -
    ((g : ℂ) ^ 2) • ricChain W g E h R ω j

private lemma pm_chain_succ (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W h) (j : ℕ) : ricChain W g E h R ω (j + 1) = (pmGam W g E h R ω j)⁻¹ := rfl

private lemma pm_gam_of_lt (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W h) {j : ℕ} (hj : j < h) :
    pmGam W g E h R ω j = gueBlock W h ω ⟨j, hj⟩ - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • ricChain W g E h R ω j := by
  simp [pmGam, hj]

private lemma pm_gam_isHermitian {W : ℕ} {g E : ℝ} {h : ℕ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (ω : Ω W h) (j : ℕ) : (pmGam W g E h R ω j).IsHermitian := by
  have hV : (if hj : j < h then gueBlock W h ω ⟨j, hj⟩ else 0 :
      Matrix (Fin W) (Fin W) ℂ).IsHermitian := by
    split_ifs
    · exact gueBlock_isHermitian W h ω _
    · exact Matrix.isHermitian_zero
  have hE : IsSelfAdjoint (E : ℂ) := by rw [isSelfAdjoint_iff]; simp
  have hk : IsSelfAdjoint ((g : ℂ) ^ 2) := by rw [isSelfAdjoint_iff]; simp
  exact (hV.sub (Matrix.isHermitian_one.smul hE)).sub ((ricChain_isHermitian hR ω j).smul hk)

/-- The matrix inverse `X ↦ X⁻¹ = det(X)⁻¹ adj(X)` is Borel. -/
private lemma pm_measurable_inv {W : ℕ} :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => X⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have h : (fun X : Matrix (Fin W) (Fin W) ℂ => X⁻¹ i j) =
      fun X => (X.det)⁻¹ * X.adjugate i j := by
    funext X
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [h]
  have hd : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => X.det := continuous_id.matrix_det
  have ha : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => X.adjugate i j :=
    (continuous_id.matrix_adjugate).matrix_elem i j
  exact hd.measurable.inv.mul ha.measurable

/-- Block `a` of the sample is measurable in the sample. -/
private lemma pm_measurable_gueBlock (W h : ℕ) (a : Fin h) :
    Measurable fun ω : Ω W h => gueBlock W h ω a := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The states and the fresh matrices of the chain are measurable in the sample. -/
private lemma pm_measurable_chain (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) :
    ∀ j, Measurable (fun ω => ricChain W g E h R ω j) ∧
      Measurable (fun ω => pmGam W g E h R ω j) := by
  have hgam : ∀ j, Measurable (fun ω => ricChain W g E h R ω j) →
      Measurable (fun ω => pmGam W g E h R ω j) := by
    intro j hc
    have hblk : Measurable fun ω : Ω W h =>
        (if hj : j < h then gueBlock W h ω ⟨j, hj⟩ else 0 : Matrix (Fin W) (Fin W) ℂ) := by
      by_cases hj : j < h
      · simp only [hj, ↓reduceDIte]; exact pm_measurable_gueBlock W h _
      · simp only [hj, ↓reduceDIte]; exact measurable_const
    refine pm_meas fun i k => ?_
    simp only [pmGam, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact (hblk.eval_matrix.sub measurable_const).sub (hc.eval_matrix.const_mul _)
  intro j
  induction j with
  | zero => exact ⟨measurable_const, hgam 0 measurable_const⟩
  | succ j ih =>
    have hc : Measurable (fun ω => ricChain W g E h R ω (j + 1)) :=
      pm_measurable_inv.comp ih.2
    exact ⟨hc, hgam (j + 1) hc⟩

/-- `f` depends only on the blocks `0, …, j - 1`. -/
private def pmPast {X : Type*} (W h j : ℕ) (f : Ω W h → X) : Prop :=
  ∀ ω ω' : Ω W h, (∀ x : Fin h × Fin W × Fin W, (x.1 : ℕ) < j → ω x = ω' x) → f ω = f ω'

private lemma pm_past_offBlock {X : Type*} {W h j : ℕ} {f : Ω W h → X} (hf : pmPast W h j f)
    (a : Fin h) (ha : j ≤ a) : OffBlock W h a f := fun ω ω' hω =>
  hf ω ω' fun x hx => hω x fun hxa => by rw [hxa] at hx; omega

/-- The state `R_j` depends on the blocks before `j`, and `Γ_j` on the blocks up to `j`. -/
private lemma pm_past_chain (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) :
    ∀ j, pmPast W h j (fun ω => ricChain W g E h R ω j) ∧
      pmPast W h (j + 1) (fun ω => pmGam W g E h R ω j) := by
  have hgam : ∀ j, pmPast W h j (fun ω => ricChain W g E h R ω j) →
      pmPast W h (j + 1) (fun ω => pmGam W g E h R ω j) := by
    intro j hc ω ω' hω
    have hblk : (if hj : j < h then gueBlock W h ω ⟨j, hj⟩ else 0 :
        Matrix (Fin W) (Fin W) ℂ) = (if hj : j < h then gueBlock W h ω' ⟨j, hj⟩ else 0) := by
      by_cases hj : j < h
      · simp only [hj, ↓reduceDIte]
        have e : ∀ α β : Fin W, ω (⟨j, hj⟩, α, β) = ω' (⟨j, hj⟩, α, β) :=
          fun α β => hω _ (Nat.lt_succ_self j)
        simp only [gueBlock, e]
      · simp only [hj, ↓reduceDIte]
    have e2 : ricChain W g E h R ω j = ricChain W g E h R ω' j :=
      hc ω ω' fun x hx => hω x (Nat.lt_succ_of_lt hx)
    simp only [pmGam]
    rw [hblk, e2]
  intro j
  induction j with
  | zero => exact ⟨fun _ _ _ => rfl, hgam 0 fun _ _ _ => rfl⟩
  | succ j ih =>
    have hc : pmPast W h (j + 1) (fun ω => ricChain W g E h R ω (j + 1)) :=
      fun ω ω' hω => by
        change ricChain W g E h R ω (j + 1) = ricChain W g E h R ω' (j + 1)
        rw [pm_chain_succ, pm_chain_succ]
        exact congrArg _ (ih.2 ω ω' hω)
    exact ⟨hc, hgam (j + 1) hc⟩

/-! ### Killing -/

/-- `#{λ ∈ Sᶜ} = W - #{λ ∈ S}` for Hermitian `A`. -/
private lemma pm_countIn_compl {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian)
    (S : Set ℝ) : (countIn A Sᶜ : ℝ) = W - countIn A S := by
  have : countIn A S + countIn A Sᶜ = W := by
    simp only [countIn, hA, ↓reduceDIte, Set.mem_compl_iff]
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have h' : ((countIn A S + countIn A Sᶜ : ℕ) : ℝ) = W := by exact_mod_cast this
  push_cast at h'; linarith

/-- The regular states form a measurable set along a measurable Hermitian-valued map. -/
private lemma pm_measurableSet_regular {W : ℕ} {α : Type*} [MeasurableSpace α]
    {X : α → Matrix (Fin W) (Fin W) ℂ} (hX : Measurable X) (hH : ∀ x, (X x).IsHermitian)
    (g : ℝ) : MeasurableSet {x | IsRegularState W g (X x)} := by
  have hk : IsSelfAdjoint ((g : ℂ) ^ 2) := by rw [isSelfAdjoint_iff]; simp
  have e : {x | IsRegularState W g (X x)} = {x | ‖X x‖ ≤ (W : ℝ) ^ 3} ∩
      {x | (W : ℝ) - (specProj (((g : ℂ) ^ 2) • X x) (Set.Icc (-g) g)).trace.re ≤
        W * Real.sqrt g} := by
    ext x
    have hgX := (hH x).smul hk
    have hset : {y : ℝ | g < |y|} = (Set.Icc (-g) g)ᶜ := by
      ext y
      rw [Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le]
      rfl
    simp only [IsRegularState, hH x, true_and, Set.mem_ofPred_eq, Set.mem_inter_iff, hset,
      pm_countIn_compl hgX, (specProj_spec hgX _).2.2.2, Complex.natCast_re]
  rw [e]
  have hsm : Measurable fun x => specProj (((g : ℂ) ^ 2) • X x) (Set.Icc (-g) g) :=
    (measurable_specProj isClosed_Icc).comp
      (pm_meas fun i j => by simpa using hX.eval_matrix.const_mul ((g : ℂ) ^ 2))
  have htr : Measurable fun x => (specProj (((g : ℂ) ^ 2) • X x) (Set.Icc (-g) g)).trace.re := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact Finset.measurable_sum _ fun i _ => Complex.measurable_re.comp hsm.eval_matrix
  exact (measurableSet_le (continuous_norm.measurable.comp hX) measurable_const).inter
    (measurableSet_le (measurable_const.sub htr) measurable_const)

/-- The survival sets: `S_0` is everything, and `S_{j+1}` adds `‖R_{j+1}‖ < c` and the
regularity (9.3) [us:eq:regular] of `R_{j+1}`. -/
private def pmSurv (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (c : ℝ) :
    ℕ → Set (Ω W h)
  | 0 => Set.univ
  | j + 1 => pmSurv W g E h R c j ∩ {ω | ‖ricChain W g E h R ω (j + 1)‖ < c ∧
      IsRegularState W g (ricChain W g E h R ω (j + 1))}

private lemma pm_surv_succ_subset (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ)
    (c : ℝ) (j : ℕ) : pmSurv W g E h R c (j + 1) ⊆ pmSurv W g E h R c j :=
  Set.inter_subset_left

private lemma pm_surv_regular {W : ℕ} {g E : ℝ} {h : ℕ} {R : Matrix (Fin W) (Fin W) ℂ} {c : ℝ}
    (hR : IsRegularState W g R) :
    ∀ j, ∀ ω ∈ pmSurv W g E h R c j, IsRegularState W g (ricChain W g E h R ω j)
  | 0, _, _ => hR
  | _ + 1, _, hω => hω.2.2

private lemma pm_surv_past (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (c : ℝ) :
    ∀ j, pmPast W h j (· ∈ pmSurv W g E h R c j)
  | 0 => fun _ _ _ => rfl
  | j + 1 => fun ω ω' hω => by
    have h1 := pm_surv_past W g E h R c j ω ω' fun x hx => hω x (Nat.lt_succ_of_lt hx)
    have h2 : ricChain W g E h R ω (j + 1) = ricChain W g E h R ω' (j + 1) :=
      (pm_past_chain W g E h R (j + 1)).1 ω ω' hω
    simp only [pmSurv, Set.mem_inter_iff, Set.mem_ofPred_eq, eq_iff_iff] at h1 ⊢
    rw [h1, h2]

private lemma pm_surv_measurable {W : ℕ} (g E : ℝ) (h : ℕ) {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (c : ℝ) : ∀ j, MeasurableSet (pmSurv W g E h R c j)
  | 0 => MeasurableSet.univ
  | j + 1 => by
    have hm := (pm_measurable_chain W g E h R (j + 1)).1
    exact (pm_surv_measurable g E h hR c j).inter
      ((measurableSet_lt (continuous_norm.measurable.comp hm) measurable_const).inter
        (pm_measurableSet_regular hm (fun ω => ricChain_isHermitian hR ω (j + 1)) g))

/-- The killing failure (9.58) [us:eq:wegner]: with `c = W^{1+δ}`,
`P(S_hᶜ) ≤ h C (W^{-δ} + W^{-2} + g^{1/2})`. -/
private lemma pm_surv_compl : ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ) (g E : ℝ) (h : ℕ)
    (R : Matrix (Fin W) (Fin W) ℂ) (δ : ℝ), 1 ≤ W → 0 < g → R.IsHermitian →
    μ W h (pmSurv W g E h R ((W : ℝ) ^ (1 + δ)) h)ᶜ ≤
      ENNReal.ofReal (h * (C * ((W : ℝ) ^ (-δ) + (W : ℝ) ^ (-2 : ℝ) + Real.sqrt g))) := by
  obtain ⟨Cn, hCn, hn⟩ := fresh_inv_norm_tail
  obtain ⟨Cr, hCr, hr⟩ := fresh_regular
  refine ⟨Cn + Cr, by positivity, fun W g E h R δ hW hg hR => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set S := pmSurv W g E h R ((W : ℝ) ^ (1 + δ)) with hS
  set b : ℝ := (Cn + Cr) * ((W : ℝ) ^ (-δ) + (W : ℝ) ^ (-2 : ℝ) + Real.sqrt g) with hb
  have hb0 : 0 ≤ b := by positivity
  have step : ∀ j, j < h → μ W h (S j \ S (j + 1)) ≤ ENNReal.ofReal b := by
    intro j hj
    set a : Fin h := ⟨j, hj⟩
    have hm := (pm_measurable_chain W g E h R j).1
    have hRa : OffBlock W h a (fun ω => ricChain W g E h R ω j) :=
      pm_past_offBlock (pm_past_chain W g E h R j).1 a le_rfl
    have hSm := pm_surv_measurable g E h hR ((W : ℝ) ^ (1 + δ)) j
    have hSa : OffBlock W h a (· ∈ S j) :=
      pm_past_offBlock (pm_surv_past W g E h R _ j) a le_rfl
    have hsub : S j \ S (j + 1) ⊆ {ω | ω ∈ S j ∧ (W : ℝ) ^ δ * W ≤
        ‖(gueBlock W h ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • ricChain W g E h R ω j)⁻¹‖} ∪
        {ω | ω ∈ S j ∧ ¬ IsRegularState W g
          (gueBlock W h ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • ricChain W g E h R ω j)⁻¹} := by
      intro ω hω
      obtain ⟨h1, h2⟩ := hω
      have e : ricChain W g E h R ω (j + 1) = (gueBlock W h ω a - (E : ℂ) • 1 -
          ((g : ℂ) ^ 2) • ricChain W g E h R ω j)⁻¹ := by
        rw [pm_chain_succ, pm_gam_of_lt W g E h R ω hj]
      have hc : (W : ℝ) ^ (1 + δ) = (W : ℝ) ^ δ * W := by
        rw [Real.rpow_add hW0, Real.rpow_one, mul_comm]
      by_cases hn' : (W : ℝ) ^ δ * W ≤ ‖(gueBlock W h ω a - (E : ℂ) • 1 -
          ((g : ℂ) ^ 2) • ricChain W g E h R ω j)⁻¹‖
      · exact Or.inl ⟨h1, hn'⟩
      · refine Or.inr ⟨h1, fun hreg => h2 ⟨h1, ?_, ?_⟩⟩
        · rw [e, hc]; exact not_le.mp hn'
        · rw [e]; exact hreg
    have h1 := hn W h a (fun ω => ricChain W g E h R ω j) (S j) hW hm
      (fun ω => ricChain_isHermitian hR ω j) hRa hSm hSa g E ((W : ℝ) ^ δ) (by positivity)
    have h2 := hr W h a (fun ω => ricChain W g E h R ω j) (S j) hW hm
      (fun ω => ricChain_isHermitian hR ω j) hRa hSm hSa g E hg
    have hP : μ W h (S j) ≤ 1 := prob_le_one
    calc μ W h (S j \ S (j + 1)) ≤ _ := (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (Cn / (W : ℝ) ^ δ) * 1 +
          ENNReal.ofReal (Cr * ((W : ℝ) ^ (-2 : ℝ) + Real.sqrt g)) * 1 :=
        add_le_add (h1.trans (by gcongr)) (h2.trans (by gcongr))
      _ ≤ ENNReal.ofReal b := by
        rw [mul_one, mul_one, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hb, div_eq_mul_inv, ← Real.rpow_neg hW0.le]
        have : 0 ≤ (W : ℝ) ^ (-δ) := by positivity
        have : 0 ≤ (W : ℝ) ^ (-2 : ℝ) := by positivity
        have : 0 ≤ Real.sqrt g := Real.sqrt_nonneg g
        nlinarith
  have key : ∀ j, j ≤ h → μ W h (S j)ᶜ ≤ ENNReal.ofReal (j * b) := by
    intro j
    induction j with
    | zero => intro _; simp [hS, pmSurv]
    | succ j ih =>
      intro hj
      have hsub : (S (j + 1))ᶜ ⊆ (S j)ᶜ ∪ (S j \ S (j + 1)) := by
        intro ω hω
        by_cases h1 : ω ∈ S j
        · exact Or.inr ⟨h1, hω⟩
        · exact Or.inl h1
      calc μ W h (S (j + 1))ᶜ ≤ μ W h (S j)ᶜ + μ W h (S j \ S (j + 1)) :=
            (measure_mono hsub).trans (measure_union_le _ _)
        _ ≤ ENNReal.ofReal (j * b) + ENNReal.ofReal b :=
            add_le_add (ih (Nat.le_of_succ_le hj)) (step j hj)
        _ = ENNReal.ofReal ((j + 1 : ℕ) * b) := by
            rw [← ENNReal.ofReal_add (by positivity) hb0]; push_cast; ring_nf
  exact key h le_rfl

/-! ### Band products -/

/-- `x ↦ F x * G x` is measurable for measurable matrix-valued `F`, `G`. -/
private lemma pm_measurable_mul {W : ℕ} {α : Type*} [MeasurableSpace α]
    {F G : α → Matrix (Fin W) (Fin W) ℂ} (hF : Measurable F) (hG : Measurable G) :
    Measurable fun x => F x * G x :=
  pm_meas fun i j => by
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun k _ => hF.eval_matrix.mul hG.eval_matrix

/-- The band product `Π_{i ≤ j} R_i 1_{band l_i}(Γ_{i-1})`, with the latest factor on the
left. -/
private def pmProd (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (β : ℝ) (L : ℕ)
    (ω : Ω W h) : (j : ℕ) → (Fin j → Fin (L + 1)) → Matrix (Fin W) (Fin W) ℂ
  | 0, _ => 1
  | j + 1, l => ricChain W g E h R ω (j + 1) *
      specProj (pmGam W g E h R ω j) (pmBand β L (l (Fin.last j))) *
      pmProd W g E h R β L ω j (Fin.init l)

/-- On every sample, `R_j ⋯ R_1` is the sum of the band products. -/
private lemma pm_prod_sum {W : ℕ} {g E : ℝ} {h : ℕ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (L : ℕ) (ω : Ω W h) :
    ∀ j, ricProd W g E h R ω j = ∑ l : Fin j → Fin (L + 1), pmProd W g E h R β L ω j l
  | 0 => by simp [ricProd, pmProd]
  | j + 1 => by
    rw [ricProd, pm_prod_sum hR hβ0 hβ1 L ω j,
      ← (Fin.snocEquiv fun _ => Fin (L + 1)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.snocEquiv_apply, pmProd, Fin.snoc_last, Fin.init_snoc]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
      pm_sum_band (pm_gam_isHermitian hR ω j) hβ0 hβ1 L, Matrix.mul_one]

private lemma pm_measurable_prod {W : ℕ} (g E : ℝ) (h : ℕ) {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (L : ℕ) :
    ∀ j (l : Fin j → Fin (L + 1)), Measurable fun ω => pmProd W g E h R β L ω j l
  | 0, _ => measurable_const
  | j + 1, l => pm_measurable_mul (pm_measurable_mul
      (pm_measurable_chain W g E h R (j + 1)).1
      (pm_measurable_band (pm_measurable_chain W g E h R j).2
        (fun ω => pm_gam_isHermitian hR ω j) hβ0 hβ1 L _))
      (pm_measurable_prod g E h hR hβ0 hβ1 L j (Fin.init l))

private lemma pm_past_prod (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (β : ℝ)
    (L : ℕ) : ∀ j (l : Fin j → Fin (L + 1)), pmPast W h j fun ω => pmProd W g E h R β L ω j l
  | 0, _ => fun _ _ _ => rfl
  | j + 1, l => fun ω ω' hω => by
    have h1 : ricChain W g E h R ω (j + 1) = ricChain W g E h R ω' (j + 1) :=
      (pm_past_chain W g E h R (j + 1)).1 ω ω' hω
    have h2 : pmGam W g E h R ω j = pmGam W g E h R ω' j :=
      (pm_past_chain W g E h R j).2 ω ω' hω
    have h3 : pmProd W g E h R β L ω j (Fin.init l) = pmProd W g E h R β L ω' j (Fin.init l) :=
      pm_past_prod W g E h R β L j (Fin.init l) ω ω' fun x hx => hω x (Nat.lt_succ_of_lt hx)
    simp only [pmProd]
    rw [h1, h2, h3]

/-- The rank of a band product is at most the rank of each of its band projections. -/
private lemma pm_rank_prod_le (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (β : ℝ)
    (L : ℕ) (ω : Ω W h) : ∀ j (l : Fin j → Fin (L + 1)) (i : Fin j),
    (pmProd W g E h R β L ω j l).rank ≤
      (specProj (pmGam W g E h R ω i) (pmBand β L (l i))).rank
  | 0, _, i => i.elim0
  | j + 1, l, i => by
    simp only [pmProd]
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    · refine (Matrix.rank_mul_le_right _ _).trans ?_
      have := pm_rank_prod_le W g E h R β L ω j (Fin.init l) i'
      simpa [Fin.init] using this

/-- One column step: `Y_{j+1} v = Γ_j⁻¹ 1_{band}(Γ_j) Y_j v`. -/
private lemma pm_prod_mulVec (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (β : ℝ)
    (L : ℕ) (ω : Ω W h) (j : ℕ) (l : Fin (j + 1) → Fin (L + 1)) (v : Fin W → ℂ) :
    pmProd W g E h R β L ω (j + 1) l *ᵥ v = (pmGam W g E h R ω j)⁻¹ *ᵥ
      (specProj (pmGam W g E h R ω j) (pmBand β L (l (Fin.last j))) *ᵥ
        (pmProd W g E h R β L ω j (Fin.init l) *ᵥ v)) := by
  simp only [pmProd, pm_chain_succ, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-! ### Moments of band products and counts -/

/-- `x ↦ F x u(x)` is measurable for measurable `F` and `u`. -/
private lemma pm_measurable_mulVec {W : ℕ} {α : Type*} [MeasurableSpace α]
    {F : α → Matrix (Fin W) (Fin W) ℂ} {u : α → Fin W → ℂ} (hF : Measurable F)
    (hu : Measurable u) : Measurable fun x => F x *ᵥ u x := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _ => hF.eval_matrix.mul (measurable_pi_iff.mp hu j)

/-- `x ↦ ‖F x u(x)‖²` is measurable for measurable `F` and `u`. -/
private lemma pm_measurable_col {W : ℕ} {α : Type*} [MeasurableSpace α]
    {F : α → Matrix (Fin W) (Fin W) ℂ} {u : α → Fin W → ℂ} (hF : Measurable F)
    (hu : Measurable u) : Measurable fun x => l2Norm (F x *ᵥ u x) ^ 2 := by
  have hc : Continuous fun w : Fin W → ℂ => l2Norm w := by unfold l2Norm; fun_prop
  exact (hc.measurable.comp (pm_measurable_mulVec hF hu)).pow_const 2

/-- `‖e_k‖ = 1`. -/
private lemma pm_l2Norm_single {W : ℕ} (k : Fin W) : l2Norm (Pi.single k (1 : ℂ)) ^ 2 = 1 := by
  unfold l2Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- The squared Hilbert–Schmidt norm is the sum of the squared column norms. -/
private lemma pm_hs_eq {W : ℕ} (Y : Matrix (Fin W) (Fin W) ℂ) :
    ∑ i, ∑ j, ‖Y i j‖ ^ 2 = ∑ k, l2Norm (Y *ᵥ Pi.single k 1) ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold l2Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), Matrix.mulVec_single_one]
  rfl

/-- Markov's inequality on a set `S`. -/
private lemma pm_markov {W h : ℕ} {S : Set (Ω W h)} {f : Ω W h → ℝ} (hf : Measurable f)
    {T B : ℝ} (hT : 0 < T)
    (hB : ∫⁻ ω in S, ENNReal.ofReal (f ω) ∂(μ W h) ≤ ENNReal.ofReal B) :
    μ W h {ω | ω ∈ S ∧ T < f ω} ≤ ENNReal.ofReal (B / T) := by
  calc μ W h {ω | ω ∈ S ∧ T < f ω}
      ≤ μ W h ({ω | ENNReal.ofReal T ≤ ENNReal.ofReal (f ω)} ∩ S) :=
        measure_mono fun ω hω => ⟨ENNReal.ofReal_le_ofReal hω.2.le, hω.1⟩
    _ ≤ (μ W h).restrict S {ω | ENNReal.ofReal T ≤ ENNReal.ofReal (f ω)} :=
        Measure.le_restrict_apply _ _
    _ ≤ (∫⁻ ω in S, ENNReal.ofReal (f ω) ∂(μ W h)) / ENNReal.ofReal T :=
        meas_ge_le_lintegral_div hf.ennreal_ofReal.aemeasurable
          (by simpa using hT) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal B / ENNReal.ofReal T := by gcongr
    _ = ENNReal.ofReal (B / T) := (ENNReal.ofReal_div_of_pos hT).symm

/-- The integral of a finite sum of nonnegative measurable functions. -/
private lemma pm_lintegral_sum {W h : ℕ} {S : Set (Ω W h)} {f : Fin W → Ω W h → ℝ}
    (hf : ∀ k, Measurable (f k)) (hf0 : ∀ k ω, 0 ≤ f k ω) :
    ∫⁻ ω in S, ENNReal.ofReal (∑ k, f k ω) ∂(μ W h) =
      ∑ k, ∫⁻ ω in S, ENNReal.ofReal (f k ω) ∂(μ W h) := by
  rw [← lintegral_finsetSum _ fun k _ => (hf k).ennreal_ofReal]
  refine lintegral_congr fun ω => ?_
  exact ENNReal.ofReal_sum_of_nonneg fun k _ => hf0 k ω

/-- The input (G.7) [us:eq:projexp] at fixed `W`, `g`, `E`, with constant `C W^{2δ}`. -/
private def PmProjExp (W h : ℕ) (g E C δ : ℝ) : Prop :=
  ∀ (a : Fin h) (t : ℝ), (W : ℝ) ^ (-1 - δ) ≤ t → t ≤ 1 →
    ∀ (Rp : Ω W h → Matrix (Fin W) (Fin W) ℂ) (u : Ω W h → Fin W → ℂ) (S : Set (Ω W h)),
      Measurable Rp → OffBlock W h a Rp → Measurable u → OffBlock W h a u →
      MeasurableSet S → OffBlock W h a (· ∈ S) → (∀ ω ∈ S, IsRegularState W g (Rp ω)) →
      ∫⁻ ω in S, ENNReal.ofReal (l2Norm (specProj (gueBlock W h ω a - (E : ℂ) • 1 -
          ((g : ℂ) ^ 2) • Rp ω) (Set.Icc (-t) t) *ᵥ u ω) ^ 2) ∂(μ W h) ≤
        ENNReal.ofReal (C * (W : ℝ) ^ (2 * δ) * t) *
          ∫⁻ ω in S, ENNReal.ofReal (l2Norm (u ω) ^ 2) ∂(μ W h)

/-- (G.7) [us:eq:projexp] on the survival set, for the window `[-β^m, β^m]` of `Γ_j` and a vector
fixed before block `j`. -/
private lemma pm_projexp_step {W h : ℕ} {g E C δ β c : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {L : ℕ} (hR : IsRegularState W g R) (hpe : PmProjExp W h g E C δ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hwin : (W : ℝ) ^ (-1 - δ) ≤ β ^ (L - 1)) {j : ℕ} (hj : j < h) {m : ℕ}
    (hm : m + 1 ≤ L) {u : Ω W h → Fin W → ℂ} (hu : Measurable u) (hup : pmPast W h j u) :
    ∫⁻ ω in pmSurv W g E h R c j,
        ENNReal.ofReal (l2Norm (specProj (pmGam W g E h R ω j) (pmIcc β m) *ᵥ u ω) ^ 2)
          ∂(μ W h) ≤
      ENNReal.ofReal (C * (W : ℝ) ^ (2 * δ) * β ^ m) *
        ∫⁻ ω in pmSurv W g E h R c j, ENNReal.ofReal (l2Norm (u ω) ^ 2) ∂(μ W h) := by
  set a : Fin h := ⟨j, hj⟩
  have e : ∀ ω, pmGam W g E h R ω j =
      gueBlock W h ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • ricChain W g E h R ω j :=
    fun ω => pm_gam_of_lt W g E h R ω hj
  simp only [e, pmIcc]
  refine hpe a (β ^ m) (hwin.trans (pow_le_pow_of_le_one hβ0.le hβ1 (by omega)))
    (pow_le_one₀ hβ0.le hβ1) (fun ω => ricChain W g E h R ω j) u _
    (pm_measurable_chain W g E h R j).1
    (pm_past_offBlock (pm_past_chain W g E h R j).1 a le_rfl) hu
    (pm_past_offBlock hup a le_rfl) (pm_surv_measurable g E h hR.1 c j)
    (pm_past_offBlock (pm_surv_past W g E h R c j) a le_rfl) (pm_surv_regular hR j)

/-- The Hilbert–Schmidt moment of a band product on the survival set (Appendix G.3
[app:product-moment-proof]): `𝔼[‖Y e_k‖² ; S_j] ≤ K^j β^{-Σ l}`, with
`K = max(C, 1) W^{2δ} β⁻¹`. -/
private lemma pm_peel {W h : ℕ} {g E C δ β c : ℝ} {R : Matrix (Fin W) (Fin W) ℂ} {L : ℕ}
    (hR : IsRegularState W g R) (hpe : PmProjExp W h g E C δ) (hW : 1 ≤ W) (hδ : 0 ≤ δ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hwin : (W : ℝ) ^ (-1 - δ) ≤ β ^ (L - 1))
    (hc : c ≤ (β ^ L)⁻¹) (k : Fin W) :
    ∀ j, j ≤ h → ∀ l : Fin j → Fin (L + 1),
      ∫⁻ ω in pmSurv W g E h R c j,
          ENNReal.ofReal (l2Norm (pmProd W g E h R β L ω j l *ᵥ Pi.single k 1) ^ 2) ∂(μ W h) ≤
        ENNReal.ofReal ((max C 1 * (W : ℝ) ^ (2 * δ) * β⁻¹) ^ j *
          β⁻¹ ^ (∑ i, (l i : ℕ))) := by
  set K : ℝ := max C 1 * (W : ℝ) ^ (2 * δ) * β⁻¹ with hK
  have hb1 : 1 ≤ β⁻¹ := (one_le_inv₀ hβ0).mpr hβ1
  have hK1 : 1 ≤ K := by
    have h1 : 1 ≤ max C 1 := le_max_right _ _
    have h3 : 1 ≤ (W : ℝ) ^ (2 * δ) := Real.one_le_rpow (by exact_mod_cast hW) (by linarith)
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h3) hb1
  have hK0 : 0 ≤ K := by linarith
  intro j
  induction j with
  | zero =>
    intro _ l
    simp only [pmProd, Matrix.one_mulVec, pm_l2Norm_single]
    simp [pmSurv]
  | succ j ih =>
    intro hj l
    simp only [pm_prod_mulVec]
    have hYm := pm_measurable_prod g E h hR.1 hβ0.le hβ1 L j (Fin.init l)
    set u : Ω W h → Fin W → ℂ :=
      fun ω => pmProd W g E h R β L ω j (Fin.init l) *ᵥ Pi.single k 1 with hu
    have hum : Measurable u := pm_measurable_mulVec hYm measurable_const
    have hup : pmPast W h j u := fun ω ω' hω => by
      have e : pmProd W g E h R β L ω j (Fin.init l) = pmProd W g E h R β L ω' j (Fin.init l) :=
        pm_past_prod W g E h R β L j (Fin.init l) ω ω' hω
      simp only [hu]
      rw [e]
    have hstep : ∫⁻ ω in pmSurv W g E h R c (j + 1), ENNReal.ofReal (l2Norm
        ((pmGam W g E h R ω j)⁻¹ *ᵥ (specProj (pmGam W g E h R ω j)
          (pmBand β L (l (Fin.last j))) *ᵥ u ω)) ^ 2) ∂(μ W h) ≤
        ENNReal.ofReal (K * β⁻¹ ^ (l (Fin.last j) : ℕ)) *
          ∫⁻ ω in pmSurv W g E h R c j, ENNReal.ofReal (l2Norm (u ω) ^ 2) ∂(μ W h) := by
      by_cases hz : (l (Fin.last j) : ℕ) = 0
      · rw [hz, pow_zero, mul_one]
        calc _ ≤ ∫⁻ ω in pmSurv W g E h R c (j + 1), ENNReal.ofReal (l2Norm (u ω) ^ 2) ∂(μ W h) :=
              setLIntegral_mono (pm_measurable_col hYm measurable_const).ennreal_ofReal
                fun ω hω => ENNReal.ofReal_le_ofReal (pm_band_zero_le
                  (pm_gam_isHermitian hR.1 ω j) L (hω.2.1.trans_le hc) (u ω))
          _ ≤ ∫⁻ ω in pmSurv W g E h R c j, ENNReal.ofReal (l2Norm (u ω) ^ 2) ∂(μ W h) :=
              lintegral_mono_set (pm_surv_succ_subset W g E h R c j)
          _ ≤ _ := le_mul_of_one_le_left' (ENNReal.one_le_ofReal.mpr hK1)
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero hz
      have hmL : m + 1 ≤ L := by have := (l (Fin.last j)).isLt; omega
      rw [hm]
      have hP : Measurable fun ω => specProj (pmGam W g E h R ω j) (pmIcc β m) :=
        (measurable_specProj isClosed_Icc).comp (pm_measurable_chain W g E h R j).2
      have key : ((β ^ (m + 1))⁻¹) ^ 2 * β ^ m = β⁻¹ * β⁻¹ ^ (m + 1) := by
        calc ((β ^ (m + 1))⁻¹) ^ 2 * β ^ m = β⁻¹ ^ (m + 1) * β⁻¹ * (β⁻¹ ^ m * β ^ m) := by
              rw [inv_pow]; ring
          _ = _ := by rw [← mul_pow, inv_mul_cancel₀ hβ0.ne', one_pow, mul_one, mul_comm]
      have hnum : ((β ^ (m + 1))⁻¹) ^ 2 * (C * (W : ℝ) ^ (2 * δ) * β ^ m) ≤
          K * β⁻¹ ^ (m + 1) := by
        calc ((β ^ (m + 1))⁻¹) ^ 2 * (C * (W : ℝ) ^ (2 * δ) * β ^ m)
            = C * ((W : ℝ) ^ (2 * δ) * (((β ^ (m + 1))⁻¹) ^ 2 * β ^ m)) := by ring
          _ ≤ max C 1 * ((W : ℝ) ^ (2 * δ) * (β⁻¹ * β⁻¹ ^ (m + 1))) := by
              rw [key]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ = K * β⁻¹ ^ (m + 1) := by rw [hK]; ring
      calc _ ≤ ∫⁻ ω in pmSurv W g E h R c (j + 1), ENNReal.ofReal (((β ^ (m + 1))⁻¹) ^ 2 *
              l2Norm (specProj (pmGam W g E h R ω j) (pmIcc β m) *ᵥ u ω) ^ 2) ∂(μ W h) :=
            setLIntegral_mono ((pm_measurable_col hP hum).const_mul _).ennreal_ofReal
              fun ω _ => ENNReal.ofReal_le_ofReal
                (pm_band_succ_le (pm_gam_isHermitian hR.1 ω j) hβ0 L m (u ω))
        _ ≤ ∫⁻ ω in pmSurv W g E h R c j, ENNReal.ofReal (((β ^ (m + 1))⁻¹) ^ 2 *
              l2Norm (specProj (pmGam W g E h R ω j) (pmIcc β m) *ᵥ u ω) ^ 2) ∂(μ W h) :=
            lintegral_mono_set (pm_surv_succ_subset W g E h R c j)
        _ = ENNReal.ofReal (((β ^ (m + 1))⁻¹) ^ 2) * ∫⁻ ω in pmSurv W g E h R c j,
              ENNReal.ofReal (l2Norm (specProj (pmGam W g E h R ω j) (pmIcc β m) *ᵥ u ω) ^ 2)
                ∂(μ W h) := by
            rw [← lintegral_const_mul _ (pm_measurable_col hP hum).ennreal_ofReal]
            exact lintegral_congr fun ω => ENNReal.ofReal_mul (by positivity)
        _ ≤ ENNReal.ofReal (((β ^ (m + 1))⁻¹) ^ 2) * (ENNReal.ofReal
              (C * (W : ℝ) ^ (2 * δ) * β ^ m) *
                ∫⁻ ω in pmSurv W g E h R c j, ENNReal.ofReal (l2Norm (u ω) ^ 2) ∂(μ W h)) := by
            gcongr
            exact pm_projexp_step hR hpe hβ0 hβ1 hwin hj hmL hum hup
        _ ≤ _ := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            gcongr
    have hsum : ∑ i, (l i : ℕ) = ∑ i, (Fin.init l i : ℕ) + (l (Fin.last j) : ℕ) :=
      Fin.sum_univ_castSucc _
    calc _ ≤ ENNReal.ofReal (K * β⁻¹ ^ (l (Fin.last j) : ℕ)) *
          ENNReal.ofReal (K ^ j * β⁻¹ ^ (∑ i, (Fin.init l i : ℕ))) :=
          hstep.trans (by gcongr; exact ih (Nat.le_of_succ_le hj) (Fin.init l))
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), hsum, pow_add, pow_succ]; ring_nf

/-- The survival sets decrease. -/
private lemma pm_surv_anti (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (c : ℝ)
    {j : ℕ} : ∀ k, j ≤ k → pmSurv W g E h R c k ⊆ pmSurv W g E h R c j
  | 0, hk => by rw [Nat.le_zero.mp hk]
  | k + 1, hk => by
    rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · exact (pm_surv_succ_subset W g E h R c k).trans
        (pm_surv_anti W g E h R c k (Nat.lt_succ_iff.mp hj))
    · rw [le_antisymm hk hj]

/-- The count bound (Appendix G.3 [app:product-moment-proof]): on `S_j`, the number of eigenvalues
of `Γ_j` in `[-β^m, β^m]` exceeds `T` with probability at most `W C W^{2δ} β^m / T`. -/
private lemma pm_count {W h : ℕ} {g E C δ β c : ℝ} {R : Matrix (Fin W) (Fin W) ℂ} {L : ℕ}
    (hR : IsRegularState W g R) (hpe : PmProjExp W h g E C δ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hwin : (W : ℝ) ^ (-1 - δ) ≤ β ^ (L - 1)) {j : ℕ} (hj : j < h) {m : ℕ}
    (hm : m + 1 ≤ L) {T : ℝ} (hT : 0 < T) :
    μ W h {ω | ω ∈ pmSurv W g E h R c j ∧
        T < (countIn (pmGam W g E h R ω j) (pmIcc β m) : ℝ)} ≤
      ENNReal.ofReal (W * (C * (W : ℝ) ^ (2 * δ) * β ^ m) / T) := by
  have hP := (measurable_specProj (n := Fin W) (S := pmIcc β m) isClosed_Icc).comp
    (pm_measurable_chain W g E h R j).2
  have e : ∀ ω, (countIn (pmGam W g E h R ω j) (pmIcc β m) : ℝ) =
      ∑ k, l2Norm (specProj (pmGam W g E h R ω j) (pmIcc β m) *ᵥ Pi.single k 1) ^ 2 :=
    fun ω => (pm_sum_col_sq (pm_gam_isHermitian hR.1 ω j) _).symm
  simp only [e]
  refine pm_markov (Finset.measurable_sum _ fun k _ => pm_measurable_col hP measurable_const) hT ?_
  rw [pm_lintegral_sum (fun k => pm_measurable_col hP measurable_const) (fun k ω => by positivity)]
  calc ∑ k, ∫⁻ ω in pmSurv W g E h R c j, ENNReal.ofReal
        (l2Norm (specProj (pmGam W g E h R ω j) (pmIcc β m) *ᵥ Pi.single k 1) ^ 2) ∂(μ W h)
      ≤ ∑ _k : Fin W, ENNReal.ofReal (C * (W : ℝ) ^ (2 * δ) * β ^ m) := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine (pm_projexp_step (u := fun _ => Pi.single k 1) hR hpe hβ0 hβ1 hwin hj hm
          measurable_const fun _ _ _ => rfl).trans ?_
        simp only [pm_l2Norm_single, ENNReal.ofReal_one, lintegral_const, Measure.restrict_apply,
          MeasurableSet.univ, Set.univ_inter, one_mul]
        exact mul_le_of_le_one_right' prob_le_one
    _ = ENNReal.ofReal (W * (C * (W : ℝ) ^ (2 * δ) * β ^ m)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- The rank of a band product on the event where every count of `Γ_i` in `[-β^m, β^m]`
(`m < L`) is at most `T₀ β^m`: `rank Y_l ≤ T₀ β^{max_i l_i - 1}`. -/
private lemma pm_rank_bound {W h : ℕ} {g E β T₀ : ℝ} {R : Matrix (Fin W) (Fin W) ℂ} {L : ℕ}
    (hR : R.IsHermitian) (hh : 1 ≤ h) (hβ : 0 < β) (ω : Ω W h) (hW : (W : ℝ) ≤ T₀ * β⁻¹)
    (hcnt : ∀ (i : Fin h) (m : ℕ), m < L →
      (countIn (pmGam W g E h R ω i) (pmIcc β m) : ℝ) ≤ T₀ * β ^ m)
    (l : Fin h → Fin (L + 1)) :
    ((pmProd W g E h R β L ω h l).rank : ℝ) ≤
      T₀ * β⁻¹ * β ^ (Finset.univ.sup fun i => (l i : ℕ)) := by
  obtain ⟨mx, hmx⟩ : ∃ mx, mx = Finset.univ.sup fun i => (l i : ℕ) := ⟨_, rfl⟩
  rw [← hmx]
  by_cases hm0 : mx = 0
  · rw [hm0, pow_zero, mul_one]
    exact le_trans (by exact_mod_cast Matrix.rank_le_width _) hW
  · have : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun i => (l i : ℕ))
    obtain ⟨m', hm'⟩ := Nat.exists_eq_add_one_of_ne_zero hm0
    have hli : (l i : ℕ) = m' + 1 := by rw [← hm', hmx]; exact hi.symm
    have hm'L : m' < L := by have := (l i).isLt; omega
    calc ((pmProd W g E h R β L ω h l).rank : ℝ)
        ≤ ((specProj (pmGam W g E h R ω i) (pmBand β L (l i))).rank : ℝ) := by
          exact_mod_cast pm_rank_prod_le W g E h R β L ω h l i
      _ ≤ (countIn (pmGam W g E h R ω i) (pmIcc β m') : ℝ) := by
          rw [hli, rank_specProj (pm_gam_isHermitian hR ω i)]
          exact_mod_cast pm_countIn_mono _ Set.sdiff_subset
      _ ≤ T₀ * β ^ m' := hcnt i m' hm'L
      _ = T₀ * β⁻¹ * β ^ mx := by rw [hm', pow_succ]; field_simp

/-- The band summation (Appendix G.3 [app:product-moment-proof]): if every band product has
`Tr |Y_l|^p ≤ B`, then `Tr |R_h ⋯ R_1|^p ≤ M^p (M B)`, where `M = (L + 1)^h` is the number of
band products. -/
private lemma pm_band_sum {W h : ℕ} {g E β p B : ℝ} {R : Matrix (Fin W) (Fin W) ℂ} {L : ℕ}
    (hR : R.IsHermitian) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hp : 0 < p) (ω : Ω W h)
    (hY : ∀ l, schattenPow p (pmProd W g E h R β L ω h l) ≤ B) :
    schattenPow p (ricProd W g E h R ω h) ≤
      (((L + 1 : ℕ) : ℝ) ^ h) ^ p * (((L + 1 : ℕ) : ℝ) ^ h * B) := by
  have hcard : (Fintype.card (Fin h → Fin (L + 1)) : ℝ) = ((L + 1 : ℕ) : ℝ) ^ h := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
  rw [pm_prod_sum hR hβ0 hβ1 L ω h]
  refine (schattenPow_sum_le _ hp).trans ?_
  rw [hcard]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (Finset.sum_le_sum fun l _ => hY l).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]

/-- The exponent count of the Markov step: with `ε L = 1 + δ`, `Q = 2/p ≥ h + 1`,
`5δ ≤ e/4` and `2ε ≤ e/4`, the moment `W^{1 + (2δ + ε) h + ε s}` against the threshold
`W^{((1 + e) - (1 - q)(1 + 3δ + ε - ε m)) Q}` leaves `W^{-δ}` for `s ≤ h m`. -/
private lemma pm_exponent {h δ ε e q Q s m : ℝ} (hqQ : q * Q = 1) (hQh : h + 1 ≤ Q)
    (hh : 0 ≤ h) (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε) (he : 0 < e) (hδe : δ ≤ e / 20)
    (hεe : 2 * ε ≤ e / 4) (hm : 0 ≤ m) (hs : s ≤ h * m) :
    1 + (2 * δ + ε) * h + ε * s - ((1 + e) - (1 - q) * (1 + 3 * δ + ε - ε * m)) * Q ≤ -δ := by
  have e1 : ((1 + e) - (1 - q) * (1 + 3 * δ + ε - ε * m)) * Q =
      (1 + e) * Q - (Q - 1) * (1 + 3 * δ + ε - ε * m) := by
    linear_combination (1 + 3 * δ + ε - ε * m) * hqQ
  rw [e1]
  have F1 : ε * s ≤ ε * (h * m) := mul_le_mul_of_nonneg_left hs hε0
  have F2 : 0 ≤ (Q - 1 - h) * (ε * m) := mul_nonneg (by linarith) (mul_nonneg hε0 hm)
  have F3 : h * δ ≤ Q * δ := mul_le_mul_of_nonneg_right (by linarith) hδ0
  have F4 : h * ε ≤ Q * ε := mul_le_mul_of_nonneg_right (by linarith) hε0
  have F5 : Q * (5 * δ + 2 * ε) ≤ Q * (e / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have F6 : 0 ≤ (Q - 1) * e := mul_nonneg (by linarith) he.le
  linarith

/-- Lemma G.2 [us:lem:product], (G.6) [us:eq:product]: for `h ≥ 1`, `0 < p < 2/(h + 1)` and
`e > 0` there are `g₀, δ₀, C, W₀` such that for `W ≥ W₀`, `0 < g ≤ g₀`, `|E| ≤ 2 - κ₀` and every
regular `R`, `P(Tr |R_{h+4} ⋯ R_5|^p > W^{1+e}) ≤ C (W^{-δ₀} + g^{1/2})`. -/
theorem product_moment (κ₀ : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (h : ℕ) (hh : 1 ≤ h) (p e : ℝ)
    (hp : 0 < p) (hph : p < 2 / ((h : ℝ) + 1)) (he : 0 < e) :
    ∃ g₀ δ₀ C : ℝ, 0 < g₀ ∧ 0 < δ₀ ∧ 0 < C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ), 0 < g → g ≤ g₀ → |E| ≤ 2 - κ₀ →
        IsRegularState W g R →
        μ W h {ω | (W : ℝ) ^ (1 + e) < schattenPow p (ricProd W g E h R ω h)} ≤
          ENNReal.ofReal (C * ((W : ℝ) ^ (-δ₀) + Real.sqrt g)) := by
  obtain ⟨g₀, Cpe, hg₀, hCpe, hpe⟩ := projexp_fresh κ₀ hκ₀ hκ₀'
  obtain ⟨Cs, hCs, hsurv⟩ := pm_surv_compl
  -- the parameters `δ`, the number `L` of bands and the band ratio `W^ε`, `ε L = 1 + δ`
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (e / 20) (1 / 4) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min (by positivity) (by norm_num)
  have hδe : δ ≤ e / 20 := by rw [hδdef]; exact min_le_left _ _
  have hδ4 : δ ≤ 1 / 4 := by rw [hδdef]; exact min_le_right _ _
  obtain ⟨W₁, hW₁⟩ := hpe δ hδ0 (by linarith)
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = ⌈16 / e⌉₊ + 1 := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hLdef]; exact Nat.le_add_left 1 _
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL1
  have hLe : 16 < e * L := by
    have h1 : 16 / e < L := by
      rw [hLdef]; push_cast; linarith [Nat.le_ceil (16 / e)]
    rw [div_lt_iff₀ he] at h1; linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (1 + δ) / L := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hεL : ε * L = 1 + δ := by rw [hεdef]; field_simp
  have hεe : 2 * ε ≤ e / 4 := by
    have h1 : 2 * ε * L ≤ e / 4 * L := by rw [mul_assoc, hεL]; nlinarith
    exact le_of_mul_le_mul_right h1 hL0
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = p / 2 := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = 2 / p := ⟨_, rfl⟩
  have hqQ : q * Q = 1 := by rw [hqdef, hQdef]; field_simp
  have hQh : (h : ℝ) + 1 ≤ Q := by
    rw [hQdef, le_div_iff₀ hp]
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < (h : ℝ) + 1)).mp hph
    linarith
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hp2 : p ≤ 2 := by
    have : 2 / ((h : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hq1 : q ≤ 1 := by rw [hqdef]; linarith
  have hQ0 : 0 < Q := by rw [hQdef]; positivity
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ((L + 1 : ℕ) : ℝ) ^ h := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hMdef]; exact one_le_pow₀ (by exact_mod_cast Nat.le_add_left 1 L)
  have hM0 : 0 < M := by linarith
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = max Cpe 1 := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁]; exact lt_max_of_lt_right one_pos
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = c₁ ^ h * M ^ ((1 + p) * Q) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine ⟨g₀, δ, 2 * h * Cs + h * L * Cpe + M * A + 1, hg₀, hδ0, by positivity, max W₁ 1, ?_⟩
  intro W hW g E R hg hgg₀ hE hR
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hpeW : PmProjExp W h g E Cpe δ := fun a t ht1 ht2 Rp u S h1 h2 h3 h4 h5 h6 h7 =>
    hW₁ W h a (le_trans (le_max_left _ _) hW) g E t hg hgg₀ hE ht1 ht2 Rp u S h1 h2 h3 h4 h5 h6 h7
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = (W : ℝ) ^ (-ε) := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβdef]; exact Real.rpow_pos_of_pos hW0 _
  have hβ1 : β ≤ 1 := by rw [hβdef]; exact Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith)
  have hβpow : ∀ n : ℕ, β ^ n = (W : ℝ) ^ (-ε * n) := fun n => by
    rw [hβdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
  have hβinv : ∀ n : ℕ, β⁻¹ ^ n = (W : ℝ) ^ (ε * n) := fun n => by
    rw [inv_pow, hβpow, ← Real.rpow_neg hW0.le, neg_mul, neg_neg]
  have hc : (W : ℝ) ^ (1 + δ) ≤ (β ^ L)⁻¹ := by
    rw [hβpow, ← Real.rpow_neg hW0.le, neg_mul, neg_neg, hεL]
  have hwin : (W : ℝ) ^ (-1 - δ) ≤ β ^ (L - 1) := by
    rw [hβpow]
    refine Real.rpow_le_rpow_of_exponent_le hWr ?_
    rw [Nat.cast_sub hL1]
    push_cast
    nlinarith
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → Set (Ω W h), S = pmSurv W g E h R ((W : ℝ) ^ (1 + δ)) :=
    ⟨_, rfl⟩
  -- the thresholds: counts `T m`, Hilbert–Schmidt `τ l`, with `mx l = max_i l_i`
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ, ∀ m, T m = (W : ℝ) ^ (1 + 3 * δ) * β ^ m := ⟨_, fun _ => rfl⟩
  obtain ⟨mx, hmx⟩ : ∃ mx : (Fin h → Fin (L + 1)) → ℕ,
      ∀ l, mx l = Finset.univ.sup fun i => (l i : ℕ) := ⟨_, fun _ => rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : (Fin h → Fin (L + 1)) → ℝ, ∀ l, τ l = (W : ℝ) ^
      (((1 + e) - (1 - q) * (1 + 3 * δ + ε - ε * mx l)) * Q) * M ^ (-(1 + p) * Q) :=
    ⟨_, fun _ => rfl⟩
  have hτ0 : ∀ l, 0 < τ l := fun l => by rw [hτ]; positivity
  obtain ⟨HS, hHS⟩ : ∃ HS : (Fin h → Fin (L + 1)) → Ω W h → ℝ, ∀ l ω,
      HS l ω = ∑ k, l2Norm (pmProd W g E h R β L ω h l *ᵥ Pi.single k 1) ^ 2 :=
    ⟨_, fun _ _ => rfl⟩
  -- on the good event, the band summation gives `Tr |R_h ⋯ R_1|^p ≤ W^{1+e}`
  have hsub : {ω | (W : ℝ) ^ (1 + e) < schattenPow p (ricProd W g E h R ω h)} ⊆
      ((S h)ᶜ ∪ ⋃ jm : Fin h × Fin L, {ω | ω ∈ S jm.1 ∧
        T jm.2 < (countIn (pmGam W g E h R ω jm.1) (pmIcc β jm.2) : ℝ)}) ∪
      ⋃ l : Fin h → Fin (L + 1), {ω | ω ∈ S h ∧ τ l < HS l ω} := by
    intro ω hω
    have hω' : (W : ℝ) ^ (1 + e) < schattenPow p (ricProd W g E h R ω h) := hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, not_or,
      not_not, not_exists, not_and, not_lt] at hcon
    obtain ⟨⟨hS, hcnt⟩, hhs⟩ := hcon
    refine (not_lt.mpr ?_) hω'
    have hcnt' : ∀ (i : Fin h) (m : ℕ), m < L → (countIn (pmGam W g E h R ω i) (pmIcc β m) : ℝ)
        ≤ (W : ℝ) ^ (1 + 3 * δ) * β ^ m := fun i m hm => by
      rw [← hT]
      refine hcnt (i, ⟨m, hm⟩) ?_
      rw [hSdef] at hS ⊢
      exact pm_surv_anti W g E h R _ h i.isLt.le hS
    have hWT : (W : ℝ) ≤ (W : ℝ) ^ (1 + 3 * δ) * β⁻¹ := by
      have h1 : (W : ℝ) ≤ (W : ℝ) ^ (1 + 3 * δ) := by
        conv_lhs => rw [← Real.rpow_one (W : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le hWr (by linarith)
      have h2 : 1 ≤ β⁻¹ := (one_le_inv₀ hβ0).mpr hβ1
      nlinarith [Real.rpow_nonneg hW0.le (1 + 3 * δ)]
    refine (pm_band_sum (L := L) (B := (W : ℝ) ^ (1 + e) * M ^ (-(1 + p))) hR.1 hβ0.le hβ1 hp ω
      fun l => ?_).trans (le_of_eq ?_)
    · have hr := pm_rank_bound hR.1 hh hβ0 ω hWT hcnt' l
      rw [← hmx] at hr
      have hr' : ((W : ℝ) ^ (1 + 3 * δ) * β⁻¹ * β ^ mx l) =
          (W : ℝ) ^ (1 + 3 * δ + ε - ε * mx l) := by
        rw [hβinv 1 |>.symm.trans (pow_one _) |>.symm, hβpow, Nat.cast_one, mul_one,
          ← Real.rpow_add hW0, ← Real.rpow_add hW0]
        congr 1
        ring
      rw [hr'] at hr
      have h1 := schattenPow_le_rank_mul (pmProd W g E h R β L ω h l) hp hp2
      rw [pm_hs_eq, ← hHS, show p / 2 = q by rw [hqdef]] at h1
      have hHS0 : 0 ≤ HS l ω := by rw [hHS]; positivity
      have e1 : (1 + 3 * δ + ε - ε * mx l) * (1 - q) +
          ((1 + e) - (1 - q) * (1 + 3 * δ + ε - ε * mx l)) * Q * q = 1 + e := by
        linear_combination ((1 + e) - (1 - q) * (1 + 3 * δ + ε - ε * mx l)) * hqQ
      have e2 : -(1 + p) * Q * q = -(1 + p) := by linear_combination (-(1 + p)) * hqQ
      calc schattenPow p (pmProd W g E h R β L ω h l)
          ≤ ((pmProd W g E h R β L ω h l).rank : ℝ) ^ (1 - q) * (HS l ω) ^ q := h1
        _ ≤ ((W : ℝ) ^ (1 + 3 * δ + ε - ε * mx l)) ^ (1 - q) * (τ l) ^ q :=
            mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg _) hr (by linarith))
              (Real.rpow_le_rpow hHS0 (hhs l hS) hq0.le) (by positivity) (by positivity)
        _ = (W : ℝ) ^ ((1 + 3 * δ + ε - ε * mx l) * (1 - q) +
              ((1 + e) - (1 - q) * (1 + 3 * δ + ε - ε * mx l)) * Q * q) *
              M ^ (-(1 + p) * Q * q) := by
            rw [hτ, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hW0.le,
              ← Real.rpow_mul hW0.le, ← Real.rpow_mul hM0.le, ← mul_assoc,
              ← Real.rpow_add hW0]
        _ = (W : ℝ) ^ (1 + e) * M ^ (-(1 + p)) := by rw [e1, e2]
    · rw [← hMdef]
      calc M ^ p * (M * ((W : ℝ) ^ (1 + e) * M ^ (-(1 + p))))
          = (W : ℝ) ^ (1 + e) * (M ^ p * M ^ (1 : ℝ) * M ^ (-(1 + p))) := by
            rw [Real.rpow_one]; ring
        _ = (W : ℝ) ^ (1 + e) := by
            rw [← Real.rpow_add hM0, ← Real.rpow_add hM0,
              show p + 1 + -(1 + p) = (0 : ℝ) by ring, Real.rpow_zero, mul_one]
  -- the three failure bounds
  have hS_bound := hsurv W g E h R δ hW1 hg hR.1
  rw [← hSdef] at hS_bound
  have hcnt_bound : ∀ jm : Fin h × Fin L, μ W h {ω | ω ∈ S jm.1 ∧
      T jm.2 < (countIn (pmGam W g E h R ω jm.1) (pmIcc β jm.2) : ℝ)} ≤
        ENNReal.ofReal (Cpe * (W : ℝ) ^ (-δ)) := by
    rintro ⟨j, m⟩
    rw [hSdef]
    refine (pm_count hR hpeW hβ0 hβ1 hwin j.isLt (m := m) (by omega)
      (T := T m) (by rw [hT]; positivity)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hT, div_eq_iff (by positivity)]
    have h1 : (W : ℝ) ^ (1 + 3 * δ) = W * (W : ℝ) ^ (2 * δ) * (W : ℝ) ^ δ := by
      rw [show (1 : ℝ) + 3 * δ = 1 + 2 * δ + δ by ring, Real.rpow_add hW0, Real.rpow_add hW0,
        Real.rpow_one]
    have h2 : (W : ℝ) ^ (-δ) * (W : ℝ) ^ δ = 1 := by
      rw [← Real.rpow_add hW0]; simp
    rw [h1]
    linear_combination (-(W * Cpe * (W : ℝ) ^ (2 * δ) * β ^ (m : ℕ))) * h2
  have hHS_bound : ∀ l, μ W h {ω | ω ∈ S h ∧ τ l < HS l ω} ≤
      ENNReal.ofReal (A * (W : ℝ) ^ (-δ)) := by
    intro l
    have hYm := pm_measurable_prod g E h hR.1 hβ0.le hβ1 L h l
    obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max Cpe 1 * (W : ℝ) ^ (2 * δ) * β⁻¹ := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : ℕ, s = ∑ i, (l i : ℕ) := ⟨_, rfl⟩
    have hint : ∫⁻ ω in S h, ENNReal.ofReal (HS l ω) ∂(μ W h) ≤
        ENNReal.ofReal (W * (K ^ h * β⁻¹ ^ s)) := by
      simp only [hHS]
      rw [pm_lintegral_sum (fun k => pm_measurable_col hYm measurable_const)
        (fun _ _ => by positivity)]
      calc ∑ k, ∫⁻ ω in S h, ENNReal.ofReal
            (l2Norm (pmProd W g E h R β L ω h l *ᵥ Pi.single k 1) ^ 2) ∂(μ W h)
          ≤ ∑ _k : Fin W, ENNReal.ofReal (K ^ h * β⁻¹ ^ s) :=
            Finset.sum_le_sum fun k _ => by
              rw [hSdef, hK, hs]
              exact pm_peel hR hpeW hW1 hδ0.le hβ0 hβ1 hwin hc k h le_rfl l
        _ = ENNReal.ofReal (W * (K ^ h * β⁻¹ ^ s)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    have hHSm : Measurable (HS l) := by
      rw [show HS l = _ from funext (hHS l)]
      exact Finset.measurable_sum _ fun k _ => pm_measurable_col hYm measurable_const
    refine (pm_markov hHSm (hτ0 l) hint).trans (ENNReal.ofReal_le_ofReal ?_)
    have hsm : (s : ℝ) ≤ h * mx l := by
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
        (hmx l).symm ▸ Finset.le_sup (f := fun i => (l i : ℕ)) (Finset.mem_univ i)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← hs] at this
      exact_mod_cast this
    have hexp := pm_exponent hqQ hQh (by positivity) hδ0.le hε0 he hδe hεe
      (Nat.cast_nonneg (mx l)) hsm
    have hnum : W * (K ^ h * β⁻¹ ^ s) = c₁ ^ h * (W : ℝ) ^ (1 + (2 * δ + ε) * h + ε * s) := by
      rw [hK, ← hc₁, mul_pow, mul_pow, hβinv, ← Real.rpow_natCast ((W : ℝ) ^ (2 * δ)),
        ← Real.rpow_mul hW0.le, hβinv, Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one,
        show (2 * δ + ε) * (h : ℝ) = 2 * δ * h + ε * h by ring, Real.rpow_add hW0]
      ring
    have hMM : M ^ ((1 + p) * Q) * M ^ (-(1 + p) * Q) = 1 := by
      rw [← Real.rpow_add hM0]; ring_nf; simp
    rw [div_le_iff₀ (hτ0 l)]
    calc W * (K ^ h * β⁻¹ ^ s) = c₁ ^ h * (W : ℝ) ^ (1 + (2 * δ + ε) * h + ε * s) := hnum
      _ ≤ c₁ ^ h * (W : ℝ) ^ (-δ + ((1 + e) - (1 - q) * (1 + 3 * δ + ε - ε * mx l)) * Q) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hWr (by linarith))
            (by positivity)
      _ = A * (W : ℝ) ^ (-δ) * τ l := by
          rw [hA, hτ, Real.rpow_add hW0]
          linear_combination (-(c₁ ^ h * (W : ℝ) ^ (-δ) * (W : ℝ) ^
            (((1 + e) - (1 - q) * (1 + 3 * δ + ε - ε * mx l)) * Q))) * hMM
  -- assembly
  have hW2 : (W : ℝ) ^ (-2 : ℝ) ≤ (W : ℝ) ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le hWr (by linarith)
  have hsum1 : ∑ _jm : Fin h × Fin L, ENNReal.ofReal (Cpe * (W : ℝ) ^ (-δ)) =
      ENNReal.ofReal (h * L * (Cpe * (W : ℝ) ^ (-δ))) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    push_cast; ring_nf
  have hsum2 : ∑ _l : Fin h → Fin (L + 1), ENNReal.ofReal (A * (W : ℝ) ^ (-δ)) =
      ENNReal.ofReal (M * (A * (W : ℝ) ^ (-δ))) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hMdef]
    push_cast; ring_nf
  calc μ W h {ω | (W : ℝ) ^ (1 + e) < schattenPow p (ricProd W g E h R ω h)}
      ≤ μ W h (S h)ᶜ + ∑ jm : Fin h × Fin L, μ W h {ω | ω ∈ S jm.1 ∧
            T jm.2 < (countIn (pmGam W g E h R ω jm.1) (pmIcc β jm.2) : ℝ)} +
          ∑ l : Fin h → Fin (L + 1), μ W h {ω | ω ∈ S h ∧ τ l < HS l ω} :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add
          ((measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _)))
          (measure_iUnion_fintype_le _ _)))
    _ ≤ ENNReal.ofReal (h * (Cs * ((W : ℝ) ^ (-δ) + (W : ℝ) ^ (-2 : ℝ) + Real.sqrt g))) +
          ∑ _jm : Fin h × Fin L, ENNReal.ofReal (Cpe * (W : ℝ) ^ (-δ)) +
          ∑ _l : Fin h → Fin (L + 1), ENNReal.ofReal (A * (W : ℝ) ^ (-δ)) :=
        add_le_add (add_le_add hS_bound (Finset.sum_le_sum fun jm _ => hcnt_bound jm))
          (Finset.sum_le_sum fun l _ => hHS_bound l)
    _ = ENNReal.ofReal (h * (Cs * ((W : ℝ) ^ (-δ) + (W : ℝ) ^ (-2 : ℝ) + Real.sqrt g)) +
          h * L * (Cpe * (W : ℝ) ^ (-δ)) + M * (A * (W : ℝ) ^ (-δ))) := by
        rw [hsum1, hsum2, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((2 * h * Cs + h * L * Cpe + M * A + 1) *
          ((W : ℝ) ^ (-δ) + Real.sqrt g)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hx : 0 ≤ (W : ℝ) ^ (-δ) := by positivity
        have hy : 0 ≤ Real.sqrt g := Real.sqrt_nonneg g
        have G1 : 0 ≤ h * Cs * ((W : ℝ) ^ (-δ) - (W : ℝ) ^ (-2 : ℝ)) :=
          mul_nonneg (by positivity) (by linarith)
        have G2 : 0 ≤ h * L * Cpe * Real.sqrt g := by positivity
        have G3 : 0 ≤ M * A * Real.sqrt g := by positivity
        have G4 : 0 ≤ h * Cs * Real.sqrt g := by positivity
        have G5 : 0 ≤ h * Cs * (W : ℝ) ^ (-δ) := by positivity
        linarith

end LSBA
