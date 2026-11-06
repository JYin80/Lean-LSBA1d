import LSBA.Spectral.LocalLawCompress
import LSBA.Gauss.GaussProjection
import LSBA.Gauss.GUEFirstRow

/-!
# The spectrum of a compressed GUE inverse

(9.48) [us:eq:complement-spectrum], proved in Appendix G.2.2 [app:inverse-image-spectrum]. Let
`Q : W × n` have orthonormal columns with `n + d = W`, `W^δ ≤ d ≤ ε₀ W`, and let `B` be a
Hermitian `n × n` deformation of norm at most `ε₀`. Then the inverse
`R = (Q* V Q - E - B)⁻¹` of the compressed GUE matrix satisfies the spectral hypotheses (9.43)
[us:eq:spectrum] of Lemma 9.6 [us:lem:self] at `η = A d / W`, for every prescribed `C₀`, with
probability `1 - W^{-D}`: the averaged local law at `c η` and `η` gives at least `C₀ d`
eigenvalues of `Q* V Q - E - B` in `[-η, η]` once `A` is large, and at the dyadic scales
`η ≤ r ≤ 1` at most `C W r` eigenvalues in `[-r, r]`, whence the two truncated traces.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA


/-- The coordinates of a unit eigenvector have squared moduli summing to `1`. -/
private lemma compressSpec_sum_sq_eigvec {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) (k : Fin n) :
    ∑ x, ‖hM.eigenvectorBasis k x‖ ^ 2 = 1 := by
  have h := EuclideanSpace.norm_sq_eq (hM.eigenvectorBasis k)
  rw [(hM.eigenvectorBasis.orthonormal.1 k), one_pow] at h
  exact h.symm

/-- For a Hermitian `M`, `Im ⟨(M - i t)⁻¹⟩ = n⁻¹ Σ_k t / (λ_k² + t²)` over the eigenvalues `λ_k`
of `M`. -/
private lemma compressSpec_im_ntr {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian)
    {t : ℝ} (ht : t ≠ 0) :
    (ntr (resolventMat M (((0 : ℝ) : ℂ) + t * Complex.I))).im =
      (n : ℝ)⁻¹ * ∑ k, t / (hM.eigenvalues k ^ 2 + t ^ 2) := by
  unfold ntr
  have hcard : ((Fintype.card (Fin n) : ℂ))⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [hcard, Complex.im_ofReal_mul, Matrix.trace, Complex.im_sum]
  congr 1
  simp only [Matrix.diag_apply]
  simp_rw [im_resolventMat_diag hM 0 ht]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hpos : (hM.eigenvalues k - 0) ^ 2 + t ^ 2 ≠ 0 := by positivity
  rw [← Finset.sum_div, ← Finset.mul_sum, compressSpec_sum_sq_eigvec hM k]
  simp


/-- The eigenvalues of an invertible Hermitian matrix are nonzero. -/
private lemma compressSpec_eig_ne_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) (hu : IsUnit M) (k : Fin n) : hM.eigenvalues k ≠ 0 := by
  have h := (Matrix.isUnit_iff_isUnit_det M).mp hu
  rw [hM.det_eq_prod_eigenvalues] at h
  have := (Finset.prod_ne_zero_iff.mp h.ne_zero) k (Finset.mem_univ k)
  intro h0
  exact this (by simp [h0])

/-- The eigenvalue count as the cardinality of a filtered index set. -/
private lemma compressSpec_countIn_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) (S : Set ℝ) :
    (countIn M S : ℝ) = ((Finset.univ.filter fun k => hM.eigenvalues k ∈ S).card : ℝ) := by
  simp [countIn, hM]

/-- Monotonicity of the eigenvalue count in the set. -/
private lemma compressSpec_countIn_mono {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) {S T : Set ℝ} (h : ∀ k, hM.eigenvalues k ∈ S → hM.eigenvalues k ∈ T) :
    countIn M S ≤ countIn M T := by
  simp only [countIn, hM, ↓reduceDIte]
  exact Finset.card_le_card fun k hk => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact h k hk

/-- The eigenvalue count of `M⁻¹` at `|x| ≥ r⁻¹` is at most the count of `M` at `|x| ≤ r`. -/
private lemma compressSpec_inv_count_le {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) (hu : IsUnit M) {r : ℝ} (hr : 0 < r) :
    countIn M⁻¹ {x | r⁻¹ ≤ |x|} ≤ countIn M {x | |x| ≤ r} := by
  rw [countIn_inv hM hu]
  refine compressSpec_countIn_mono hM fun k hk => ?_
  have hk' : r⁻¹ ≤ |(hM.eigenvalues k)⁻¹| := hk
  rw [abs_inv] at hk'
  have h0 : hM.eigenvalues k ≠ 0 := compressSpec_eig_ne_zero hM hu k
  have hpos : 0 < |hM.eigenvalues k| := abs_pos.2 h0
  change |hM.eigenvalues k| ≤ r
  have := (inv_le_inv₀ hr hpos).1 hk'
  exact this

/-- The count of `M` at `|x| ≤ r` is at most that of `M⁻¹` at `|x| ≥ r⁻¹`. -/
private lemma compressSpec_count_le_inv {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) (hu : IsUnit M) {r : ℝ} (hr : 0 < r) :
    countIn M {x | |x| ≤ r} ≤ countIn M⁻¹ {x | r⁻¹ ≤ |x|} := by
  rw [countIn_inv hM hu]
  refine compressSpec_countIn_mono hM fun k hk => ?_
  have h0 : hM.eigenvalues k ≠ 0 := compressSpec_eig_ne_zero hM hu k
  have hpos : 0 < |hM.eigenvalues k| := abs_pos.2 h0
  have hk' : |hM.eigenvalues k| ≤ r := hk
  change r⁻¹ ≤ |(hM.eigenvalues k)⁻¹|
  rw [abs_inv]
  exact (inv_le_inv₀ hr hpos).2 hk'

/-- Upper count: `#{|λ| ≤ r} ≤ 2 r Σ_k r / (λ_k² + r²)`. -/
private lemma compressSpec_count_upper {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) {r : ℝ} (hr : 0 < r) :
    (countIn M {x | |x| ≤ r} : ℝ) ≤ 2 * r * ∑ k, r / (hM.eigenvalues k ^ 2 + r ^ 2) := by
  rw [compressSpec_countIn_eq hM]
  set S := Finset.univ.filter fun k => hM.eigenvalues k ∈ {x : ℝ | |x| ≤ r} with hS
  have h1 : ∀ k ∈ S, 1 / (2 * r) ≤ r / (hM.eigenvalues k ^ 2 + r ^ 2) := by
    intro k hk
    have hk' : |hM.eigenvalues k| ≤ r := (Finset.mem_filter.mp hk).2
    have : hM.eigenvalues k ^ 2 ≤ r ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hk' 2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : S.card • (1 / (2 * r)) ≤ ∑ k ∈ S, r / (hM.eigenvalues k ^ 2 + r ^ 2) :=
    Finset.card_nsmul_le_sum S _ _ h1
  have h3 : ∑ k ∈ S, r / (hM.eigenvalues k ^ 2 + r ^ 2) ≤
      ∑ k, r / (hM.eigenvalues k ^ 2 + r ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => by positivity)
  rw [nsmul_eq_mul] at h2
  have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity : (0 : ℝ) ≤ 2 * r)
  calc (S.card : ℝ) = 2 * r * (S.card * (1 / (2 * r))) := by field_simp
    _ ≤ _ := h4

/-- Splitting the kernel at the scale `c η` into the window `|λ| ≤ η` and its complement. -/
private lemma compressSpec_kernel_split {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∑ k, (c * η) / (hM.eigenvalues k ^ 2 + (c * η) ^ 2) ≤
      2 * c * ∑ k, η / (hM.eigenvalues k ^ 2 + η ^ 2) +
        (countIn M {x | |x| ≤ η} : ℝ) / (c * η) := by
  rw [compressSpec_countIn_eq hM]
  set S := Finset.univ.filter fun k => hM.eigenvalues k ∈ {x : ℝ | |x| ≤ η} with hS
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun k => hM.eigenvalues k ∈ {x : ℝ | |x| ≤ η})]
  have hin : ∑ k ∈ S, (c * η) / (hM.eigenvalues k ^ 2 + (c * η) ^ 2) ≤
      (S.card : ℝ) / (c * η) := by
    have : ∀ k ∈ S, (c * η) / (hM.eigenvalues k ^ 2 + (c * η) ^ 2) ≤ 1 / (c * η) := by
      intro k _
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (hM.eigenvalues k), mul_pos hc hη]
    calc _ ≤ ∑ k ∈ S, 1 / (c * η) := Finset.sum_le_sum this
      _ = (S.card : ℝ) / (c * η) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hout : ∑ k ∈ Finset.univ.filter (fun k => ¬ hM.eigenvalues k ∈ {x : ℝ | |x| ≤ η}),
      (c * η) / (hM.eigenvalues k ^ 2 + (c * η) ^ 2) ≤
      2 * c * ∑ k, η / (hM.eigenvalues k ^ 2 + η ^ 2) := by
    have hpt : ∀ k ∈ Finset.univ.filter (fun k => ¬ hM.eigenvalues k ∈ {x : ℝ | |x| ≤ η}),
        (c * η) / (hM.eigenvalues k ^ 2 + (c * η) ^ 2) ≤
          2 * c * (η / (hM.eigenvalues k ^ 2 + η ^ 2)) := by
      intro k hk
      have hk' : η < |hM.eigenvalues k| := by
        have := (Finset.mem_filter.mp hk).2
        simpa using this
      have hsq : η ^ 2 ≤ hM.eigenvalues k ^ 2 := by
        rw [← sq_abs (hM.eigenvalues k)]
        exact pow_le_pow_left₀ hη.le hk'.le 2
      have hη2 : 0 < η ^ 2 := by positivity
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hc hη, mul_nonneg (mul_pos hc hη).le (sq_nonneg (c * η)),
        mul_pos (mul_pos hc hη) hη2, mul_pos hc hη2]
    calc _ ≤ ∑ k ∈ Finset.univ.filter (fun k => ¬ hM.eigenvalues k ∈ {x : ℝ | |x| ≤ η}),
          2 * c * (η / (hM.eigenvalues k ^ 2 + η ^ 2)) := Finset.sum_le_sum hpt
      _ = 2 * c * ∑ k ∈ Finset.univ.filter (fun k => ¬ hM.eigenvalues k ∈ {x : ℝ | |x| ≤ η}),
          η / (hM.eigenvalues k ^ 2 + η ^ 2) := by rw [Finset.mul_sum]
      _ ≤ 2 * c * ∑ k, η / (hM.eigenvalues k ^ 2 + η ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => by positivity)
  linarith

/-- Dyadic comparison: `ρ ∈ [1, η⁻¹)` with `ρ ≥ (2^m η)⁻¹` lies above `r_l⁻¹` for some `l < m`,
`r_l = min (2^(l+1) η) 1`, and then `ρ^j ≤ (2^l η)^{-j}`. -/
private lemma compressSpec_dyadic_pointwise {η : ℝ} (hη : 0 < η) (j : ℕ) (m : ℕ) :
    ∀ ρ : ℝ, 1 ≤ ρ → ρ < η⁻¹ → (2 ^ m * η)⁻¹ ≤ ρ →
      ρ ^ j ≤ ∑ l ∈ range m, ((2 ^ l * η)⁻¹) ^ j *
        (if (min (2 ^ (l + 1) * η) 1)⁻¹ ≤ ρ then (1 : ℝ) else 0) := by
  induction m with
  | zero =>
    intro ρ h1 h2 h3
    simp only [pow_zero, one_mul] at h3
    linarith
  | succ m ih =>
    intro ρ h1 h2 h3
    rw [Finset.sum_range_succ]
    by_cases hcase : (2 ^ m * η)⁻¹ ≤ ρ
    · have h := ih ρ h1 h2 hcase
      have hnn : 0 ≤ ((2 ^ m * η)⁻¹) ^ j *
          (if (min (2 ^ (m + 1) * η) 1)⁻¹ ≤ ρ then (1 : ℝ) else 0) := by
        split_ifs <;> positivity
      linarith
    · have hcase := lt_of_not_ge hcase
      have hge : (min (2 ^ (m + 1) * η) 1)⁻¹ ≤ ρ := by
        rcases min_cases (2 ^ (m + 1) * η) 1 with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; exact h3
        · rw [h]; simpa using h1
      simp only [hge, ↓reduceIte, mul_one]
      have h4 : ρ ^ j ≤ ((2 ^ m * η)⁻¹) ^ j := pow_le_pow_left₀ (by linarith) hcase.le j
      have hnn : 0 ≤ ∑ l ∈ range m, ((2 ^ l * η)⁻¹) ^ j *
          (if (min (2 ^ (l + 1) * η) 1)⁻¹ ≤ ρ then (1 : ℝ) else 0) :=
        Finset.sum_nonneg fun l _ => by split_ifs <;> positivity
      linarith

/-- The truncated power sums of a Hermitian `R` at `η⁻¹`, bounded by the number of eigenvalues
plus dyadic counts at the scales `r_l = min (2^(l+1) η) 1`. -/
private lemma compressSpec_truncPowSum_le {n : ℕ} {R : Matrix (Fin n) (Fin n) ℂ}
    (hR : R.IsHermitian) {η : ℝ} (hη : 0 < η) (m : ℕ) (hm : 1 ≤ 2 ^ m * η) (j : ℕ) :
    truncPowSum R η⁻¹ j ≤ n + ∑ l ∈ range m, ((2 ^ l * η)⁻¹) ^ j *
        (countIn R {x | (min (2 ^ (l + 1) * η) 1)⁻¹ ≤ |x|} : ℝ) := by
  unfold truncPowSum
  simp only [hR, ↓reduceDIte]
  set g : Fin n → ℝ := fun k => 1 + ∑ l ∈ range m, ((2 ^ l * η)⁻¹) ^ j *
    (if (min (2 ^ (l + 1) * η) 1)⁻¹ ≤ |hR.eigenvalues k| then (1 : ℝ) else 0) with hg
  have hgnn : ∀ k, 0 ≤ g k := fun k => by
    refine add_nonneg zero_le_one (Finset.sum_nonneg fun l _ => ?_)
    split_ifs <;> positivity
  have hpt : ∀ k ∈ Finset.univ.filter (fun k => |hR.eigenvalues k| < η⁻¹),
      |hR.eigenvalues k| ^ j ≤ g k := by
    intro k hk
    have hk' : |hR.eigenvalues k| < η⁻¹ := (Finset.mem_filter.mp hk).2
    by_cases h1 : 1 ≤ |hR.eigenvalues k|
    · have hm' : (2 ^ m * η)⁻¹ ≤ |hR.eigenvalues k| :=
        (inv_le_one_of_one_le₀ hm).trans h1
      have := compressSpec_dyadic_pointwise hη j m _ h1 hk' hm'
      simp only [hg]
      linarith
    · have h1 := lt_of_not_ge h1
      have : |hR.eigenvalues k| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg _) h1.le
      have hs : 0 ≤ ∑ l ∈ range m, ((2 ^ l * η)⁻¹) ^ j *
          (if (min (2 ^ (l + 1) * η) 1)⁻¹ ≤ |hR.eigenvalues k| then (1 : ℝ) else 0) :=
        Finset.sum_nonneg fun l _ => by split_ifs <;> positivity
      simp only [hg]
      linarith
  calc ∑ k ∈ Finset.univ.filter (fun k => |hR.eigenvalues k| < η⁻¹), |hR.eigenvalues k| ^ j
      ≤ ∑ k ∈ Finset.univ.filter (fun k => |hR.eigenvalues k| < η⁻¹), g k :=
        Finset.sum_le_sum hpt
    _ ≤ ∑ k, g k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hgnn i)
    _ = n + ∑ l ∈ range m, ((2 ^ l * η)⁻¹) ^ j *
        (countIn R {x | (min (2 ^ (l + 1) * η) 1)⁻¹ ≤ |x|} : ℝ) := by
      simp only [hg]
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.mul_sum, Finset.sum_boole, compressSpec_countIn_eq hR]
      rfl

/-- The deterministic core of (9.48) [us:eq:complement-spectrum] (Appendix G.2.2
[app:inverse-image-spectrum]): if `M` is an invertible Hermitian matrix whose averaged imaginary
resolvent trace is `≤ L` at `η` and at the dyadic scales `r_l = min (2^(l+1) η) 1`, `l < m`, and
`≥ L⁻¹` at `c η`, `c = 1/(4L²)`, then `M⁻¹` satisfies the four conditions (9.43) [us:eq:spectrum]
at `η`. -/
private lemma compressSpec_det {n W d m : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) (hu : IsUnit M) {L c η C₀ : ℝ} (hL : 1 ≤ L) (hc : c = 1 / (4 * L ^ 2))
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hn0 : 0 < n) (hnW : n ≤ W)
    (hlow : C₀ * d ≤ c * η * n / (2 * L))
    (hIη : (ntr (resolventMat M (((0 : ℝ) : ℂ) + (η : ℂ) * Complex.I))).im ≤ L)
    (hIc : L⁻¹ ≤ (ntr (resolventMat M (((0 : ℝ) : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I))).im)
    (hIr : ∀ l < m, (ntr (resolventMat M (((0 : ℝ) : ℂ) +
      ((min (2 ^ (l + 1) * η) 1 : ℝ) : ℂ) * Complex.I))).im ≤ L)
    (hm1 : 1 ≤ 2 ^ m * η) (hmlog : (m : ℝ) ≤ 3 * Real.log W) (hlogW : 1 ≤ Real.log W) :
    InvSpecInput C₀ (1 + 12 * L) (2 * L) W d η M⁻¹ := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnW' : (n : ℝ) ≤ W := by exact_mod_cast hnW
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < c := by rw [hc]; positivity
  have hR : M⁻¹.IsHermitian := hM.inv
  -- kernel bounds from the imaginary resolvent traces
  have hKη : ∑ k, η / (hM.eigenvalues k ^ 2 + η ^ 2) ≤ L * n := by
    rw [compressSpec_im_ntr hM hη0.ne'] at hIη
    have h := mul_le_mul_of_nonneg_left hIη hnr.le
    rw [← mul_assoc, mul_inv_cancel₀ hnr.ne', one_mul] at h
    linarith
  have hKc : (n : ℝ) / L ≤ ∑ k, (c * η) / (hM.eigenvalues k ^ 2 + (c * η) ^ 2) := by
    rw [compressSpec_im_ntr hM (mul_pos hc0 hη0).ne'] at hIc
    have h := mul_le_mul_of_nonneg_left hIc hnr.le
    rw [← mul_assoc, mul_inv_cancel₀ hnr.ne', one_mul] at h
    calc (n : ℝ) / L = n * L⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ _ := h
  have hKr : ∀ l < m, ∑ k, (min (2 ^ (l + 1) * η) 1) /
      (hM.eigenvalues k ^ 2 + (min (2 ^ (l + 1) * η) 1) ^ 2) ≤ L * n := by
    intro l hl
    have hpos : 0 < min (2 ^ (l + 1) * η) 1 := lt_min (by positivity) one_pos
    have h0 := hIr l hl
    rw [compressSpec_im_ntr hM hpos.ne'] at h0
    have h := mul_le_mul_of_nonneg_left h0 hnr.le
    rw [← mul_assoc, mul_inv_cancel₀ hnr.ne', one_mul] at h
    linarith
  -- the count at η
  have hNη : (countIn M {x | |x| ≤ η} : ℝ) ≤ 2 * η * (L * n) := by
    refine (compressSpec_count_upper hM hη0).trans ?_
    exact mul_le_mul_of_nonneg_left hKη (by positivity)
  -- dyadic counts of M⁻¹
  have hN : ∀ l < m, (countIn M⁻¹ {x | (min (2 ^ (l + 1) * η) 1)⁻¹ ≤ |x|} : ℝ) ≤
      4 * 2 ^ l * η * L * n := by
    intro l hl
    have hpos : 0 < min (2 ^ (l + 1) * η) 1 := lt_min (by positivity) one_pos
    have h1 : (countIn M⁻¹ {x | (min (2 ^ (l + 1) * η) 1)⁻¹ ≤ |x|} : ℝ) ≤
        (countIn M {x | |x| ≤ min (2 ^ (l + 1) * η) 1} : ℝ) :=
      by exact_mod_cast compressSpec_inv_count_le hM hu hpos
    have h2 := compressSpec_count_upper hM hpos
    have h3 : 2 * min (2 ^ (l + 1) * η) 1 * ∑ k, min (2 ^ (l + 1) * η) 1 /
        (hM.eigenvalues k ^ 2 + (min (2 ^ (l + 1) * η) 1) ^ 2) ≤
        2 * min (2 ^ (l + 1) * η) 1 * (L * n) :=
      mul_le_mul_of_nonneg_left (hKr l hl) (by positivity)
    have h4 : min (2 ^ (l + 1) * η) 1 ≤ 2 ^ (l + 1) * η := min_le_left _ _
    have h5 : 2 * min (2 ^ (l + 1) * η) 1 * (L * n) ≤ 2 * (2 ^ (l + 1) * η) * (L * n) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc _ ≤ _ := h1
      _ ≤ _ := h2.trans (h3.trans h5)
      _ = 4 * 2 ^ l * η * L * n := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the lower count
    have hsplit := compressSpec_kernel_split hM hc0 hη0
    have hin : (countIn M {x | |x| ≤ η} : ℝ) ≤ (countIn M⁻¹ {x | η⁻¹ ≤ |x|} : ℝ) := by
      exact_mod_cast compressSpec_count_le_inv hM hu hη0
    have h2c : 2 * c * (L * n) = n / (2 * L) := by
      rw [hc]; field_simp; ring
    have h3 : (n : ℝ) / L ≤ n / (2 * L) + (countIn M {x | |x| ≤ η} : ℝ) / (c * η) := by
      calc (n : ℝ) / L ≤ _ := hKc
        _ ≤ _ := hsplit
        _ ≤ 2 * c * (L * n) + (countIn M {x | |x| ≤ η} : ℝ) / (c * η) := by
          have := mul_le_mul_of_nonneg_left hKη (by positivity : (0 : ℝ) ≤ 2 * c)
          linarith
        _ = _ := by rw [h2c]
    have hcη : 0 < c * η := mul_pos hc0 hη0
    have h4 : (n : ℝ) / (2 * L) ≤ (countIn M {x | |x| ≤ η} : ℝ) / (c * η) := by
      have : (n : ℝ) / L - n / (2 * L) = n / (2 * L) := by field_simp; ring
      linarith
    rw [le_div_iff₀ hcη] at h4
    have h5 : c * η * n / (2 * L) ≤ (countIn M {x | |x| ≤ η} : ℝ) := by
      calc c * η * n / (2 * L) = (n / (2 * L)) * (c * η) := by ring
        _ ≤ _ := h4
    linarith
  · -- the upper count
    have hin : (countIn M⁻¹ {x | η⁻¹ ≤ |x|} : ℝ) ≤ (countIn M {x | |x| ≤ η} : ℝ) := by
      exact_mod_cast compressSpec_inv_count_le hM hu hη0
    calc _ ≤ _ := hin
      _ ≤ 2 * η * (L * n) := hNη
      _ ≤ 2 * L * W * η := by
        have : (L * n) ≤ L * W := mul_le_mul_of_nonneg_left hnW' hL0.le
        nlinarith [mul_pos hL0 hη0]
  · -- the truncated trace of order one
    have h1 := compressSpec_truncPowSum_le hR hη0 m hm1 1
    have h2 : ∑ l ∈ range m, ((2 ^ l * η)⁻¹) ^ 1 *
        (countIn M⁻¹ {x | (min (2 ^ (l + 1) * η) 1)⁻¹ ≤ |x|} : ℝ) ≤
        ∑ l ∈ range m, (4 * L * n) := by
      refine Finset.sum_le_sum fun l hl => ?_
      have hp : 0 < 2 ^ l * η := by positivity
      calc _ ≤ ((2 ^ l * η)⁻¹) ^ 1 * (4 * 2 ^ l * η * L * n) :=
            mul_le_mul_of_nonneg_left (hN l (Finset.mem_range.mp hl)) (by positivity)
        _ = 4 * L * n := by field_simp
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    have h3 : (m : ℝ) * (4 * L * n) ≤ 3 * Real.log W * (4 * L * W) := by
      calc (m : ℝ) * (4 * L * n) ≤ 3 * Real.log W * (4 * L * n) :=
            mul_le_mul_of_nonneg_right hmlog (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have hW : (n : ℝ) ≤ W * Real.log W := by nlinarith
    nlinarith
  · -- the truncated trace of order two
    have h1 := compressSpec_truncPowSum_le hR hη0 m hm1 2
    have h2 : ∑ l ∈ range m, ((2 ^ l * η)⁻¹) ^ 2 *
        (countIn M⁻¹ {x | (min (2 ^ (l + 1) * η) 1)⁻¹ ≤ |x|} : ℝ) ≤
        ∑ l ∈ range m, (4 * L * n / η) * (1 / 2) ^ l := by
      refine Finset.sum_le_sum fun l hl => ?_
      have hp : 0 < 2 ^ l * η := by positivity
      calc _ ≤ ((2 ^ l * η)⁻¹) ^ 2 * (4 * 2 ^ l * η * L * n) :=
            mul_le_mul_of_nonneg_left (hN l (Finset.mem_range.mp hl)) (by positivity)
        _ = (4 * L * n / η) * (1 / 2) ^ l := by
          field_simp
          rw [← mul_pow]; norm_num
    rw [← Finset.mul_sum] at h2
    have h3 := sum_geometric_two_le m
    have h4 : (4 * L * n / η) * ∑ l ∈ range m, (1 / 2 : ℝ) ^ l ≤ (4 * L * n / η) * 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : (n : ℝ) ≤ W / η := by
      rw [le_div_iff₀ hη0]
      nlinarith
    have h6 : 4 * L * n / η * 2 ≤ 8 * L * (W / η) := by
      have : 4 * L * n / η * 2 = 8 * L * (n / η) := by ring
      rw [this]
      have : (n : ℝ) / η ≤ W / η := div_le_div_of_nonneg_right hnW' hη0.le
      nlinarith
    have hq : 0 ≤ (W : ℝ) / η := div_nonneg (Nat.cast_nonneg (α := ℝ) W) hη0.le
    rw [mul_div_assoc]
    nlinarith [mul_nonneg hL0.le hq]

/-- The entries of the GUE matrix are measurable in the sample. -/
private lemma compressSpec_measurable_entry (n : ℕ) (a b : Fin n) :
    Measurable fun ω : Ω n 1 => gueMat n ω a b := by
  unfold gueMat gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The resolvent of `X - B` at `E + i τ` is the resolvent of `X - E - B` at `i τ`. -/
private lemma compressSpec_resolvent_shift {n : ℕ} (X B : Matrix (Fin n) (Fin n) ℂ) (E τ : ℝ) :
    resolventMat (X - B) ((E : ℂ) + (τ : ℂ) * Complex.I) =
      resolventMat (X - (E : ℂ) • 1 - B) (((0 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) := by
  unfold resolventMat
  congr 1
  rw [Complex.ofReal_zero, zero_add, add_smul]
  abel

/-- The scalar matrix `E 1` is Hermitian for real `E`. -/
private lemma compressSpec_isHermitian_shift {n : ℕ} (E : ℝ) :
    ((E : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp [Complex.conj_ofReal]

/-- `Q^* V Q - E - B` is Hermitian for Hermitian `B`. -/
private lemma compressSpec_isHermitian {W n : ℕ} (Q : Matrix (Fin W) (Fin n) ℂ)
    {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) (E : ℝ) (ω : Ω W 1) :
    (Qᴴ * gueMat W ω * Q - (E : ℂ) • 1 - B).IsHermitian :=
  ((Matrix.isHermitian_conjTranspose_mul_mul Q (gueBlock_isHermitian W 1 ω 0)).sub
    (compressSpec_isHermitian_shift E)).sub hB

/-- Almost surely `Q^* V Q - E - B` is invertible, for the GUE matrix `V`. -/
private lemma compressSpec_null (W n : ℕ) (hn : 0 < n) (hnW : n ≤ W)
    (Q : Matrix (Fin W) (Fin n) ℂ) (hQ : Qᴴ * Q = 1) (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : B.IsHermitian) (E : ℝ) :
    μ W 1 {ω | (Qᴴ * gueMat W ω * Q - (E : ℂ) • 1 - B).det = 0} = 0 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast lt_of_lt_of_le hn hnW
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt ((n : ℝ) / W) := Real.sqrt_pos.2 (div_pos hn0 hW0)
  have hF : Measurable fun ω : Ω W 1 => Qᴴ * gueMat W ω * Q := by
    have hgm : Measurable fun ω : Ω W 1 => gueMat W ω :=
      Matrix.measurable_iff.2 fun a b => compressSpec_measurable_entry W a b
    exact ((continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const).measurable.comp hgm
  have hg : Measurable fun ω : Ω n 1 => ((Real.sqrt ((n : ℝ) / W) : ℝ) : ℂ) • gueMat n ω := by
    have hgm : Measurable fun ω : Ω n 1 => gueMat n ω :=
      Matrix.measurable_iff.2 fun a b => compressSpec_measurable_entry n a b
    exact (continuous_const_smul ((Real.sqrt ((n : ℝ) / W) : ℝ) : ℂ)).measurable.comp hgm
  have hS : MeasurableSet {X : Matrix (Fin n) (Fin n) ℂ | (X - (E : ℂ) • 1 - B).det = 0} := by
    refine (isClosed_eq ?_ continuous_const).measurableSet
    exact ((continuous_id.sub continuous_const).sub continuous_const).matrix_det
  have hA : (-((E : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + B)).IsHermitian :=
    ((compressSpec_isHermitian_shift E).add hB).neg
  have hae := ae_det_ne_zero_gueMat n hA hs.ne'
  rw [ae_iff] at hae
  calc μ W 1 {ω : Ω W 1 | (Qᴴ * gueMat W ω * Q - (E : ℂ) • 1 - B).det = (0 : ℂ)}
      = (μ W 1).map (fun ω => Qᴴ * gueMat W ω * Q)
          {X : Matrix (Fin n) (Fin n) ℂ | (X - (E : ℂ) • 1 - B).det = 0} :=
        (Measure.map_apply hF hS).symm
    _ = (μ n 1).map (fun ω => ((Real.sqrt ((n : ℝ) / W) : ℝ) : ℂ) • gueMat n ω)
          {X : Matrix (Fin n) (Fin n) ℂ | (X - (E : ℂ) • 1 - B).det = 0} := by
        rw [map_compress_gueMat W n Q hQ]
    _ = μ n 1 ((fun ω => ((Real.sqrt ((n : ℝ) / W) : ℝ) : ℂ) • gueMat n ω) ⁻¹'
          {X : Matrix (Fin n) (Fin n) ℂ | (X - (E : ℂ) • 1 - B).det = 0}) :=
        Measure.map_apply hg hS
    _ = 0 := by
        have heq : ((fun ω : Ω n 1 => ((Real.sqrt ((n : ℝ) / W) : ℝ) : ℂ) • gueMat n ω) ⁻¹'
            {X : Matrix (Fin n) (Fin n) ℂ | (X - (E : ℂ) • 1 - B).det = 0}) =
            {ω : Ω n 1 | ¬ (-((E : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + B) +
              ((Real.sqrt ((n : ℝ) / W) : ℝ) : ℂ) • gueMat n ω).det ≠ 0} := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_not]
          rw [show -((E : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + B) +
            ((Real.sqrt ((n : ℝ) / W) : ℝ) : ℂ) • gueMat n ω =
            ((Real.sqrt ((n : ℝ) / W) : ℝ) : ℂ) • gueMat n ω - (E : ℂ) • 1 - B by abel]
        rw [heq]
        exact hae

/-- The number `m = ⌊log₂ W⌋ + 1` of dyadic scales: `2^m η ≥ 1`, `m ≤ 3 log W`, `log W ≥ 1` and
`m + 2 ≤ W²`, for `W ≥ 8` and `W η ≥ 1`. -/
private lemma compressSpec_scales {W : ℕ} (hW : 8 ≤ W) {η : ℝ} (hη0 : 0 < η)
    (hWη : 1 ≤ (W : ℝ) * η) :
    1 ≤ 2 ^ (Nat.log 2 W + 1) * η ∧ ((Nat.log 2 W + 1 : ℕ) : ℝ) ≤ 3 * Real.log W ∧
      1 ≤ Real.log W ∧ ((Nat.log 2 W + 1 : ℕ) : ℝ) + 2 ≤ (W : ℝ) ^ 2 := by
  have hWr8 : (8 : ℝ) ≤ W := by exact_mod_cast hW
  have hWr0 : (0 : ℝ) < W := by linarith
  have hWr1 : (1 : ℝ) < W := by linarith
  have hlogW : 1 ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le hWr0]
    linarith [Real.exp_one_lt_d9]
  refine ⟨?_, ?_, hlogW, ?_⟩
  · have h1 : (W : ℝ) < 2 ^ (Nat.log 2 W + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) W
    exact hWη.trans (mul_le_mul_of_nonneg_right h1.le hη0.le)
  · have h1 : (Nat.log 2 W : ℝ) ≤ Real.logb 2 W := by
      simpa using Real.natLog_le_logb W 2
    have h2 : Real.logb 2 W ≤ 2 * Real.log W := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
      have := Real.log_two_gt_d9
      nlinarith [Real.log_nonneg hWr1.le]
    push_cast
    linarith
  · have h : (Nat.log 2 W : ℝ) ≤ W := by exact_mod_cast Nat.log_le_self 2 W
    push_cast
    nlinarith

/-- The lowest scale of the local law lies below `c η`, `η = A d / W`, once `W^{δ/2} ≥ 1/(c A)`. -/
private lemma compressSpec_lowscale {W d : ℕ} {δ c A : ℝ} (hW : 0 < W)
    (hc : 0 < c) (hA : 0 < A) (hdW : (W : ℝ) ^ δ ≤ d)
    (hkey : 1 ≤ c * A * (W : ℝ) ^ (δ / 2)) :
    (W : ℝ) ^ (-1 + δ / 2) ≤ c * (A * d / W) := by
  have hWr0 : (0 : ℝ) < W := by exact_mod_cast hW
  set t : ℝ := (W : ℝ) ^ (δ / 2) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hWr0 _
  have hμ0_eq : (W : ℝ) ^ (-1 + δ / 2) = t / W := by
    rw [Real.rpow_add hWr0, Real.rpow_neg_one]
    ring
  have h1 : A * (t * t) / W ≤ A * d / W := by
    have : (W : ℝ) ^ δ = t * t := by
      rw [ht, ← Real.rpow_add hWr0]; ring_nf
    refine div_le_div_of_nonneg_right ?_ hWr0.le
    rw [← this]
    exact mul_le_mul_of_nonneg_left hdW hA.le
  rw [hμ0_eq]
  have h2 : c * (A * (t * t) / W) = (c * A * t) * (t / W) := by field_simp
  calc t / W = 1 * (t / W) := (one_mul _).symm
    _ ≤ (c * A * t) * (t / W) :=
      mul_le_mul_of_nonneg_right hkey (div_nonneg ht0.le hWr0.le)
    _ = c * (A * (t * t) / W) := h2.symm
    _ ≤ c * (A * d / W) := mul_le_mul_of_nonneg_left h1 hc.le

/-- The union bound of Appendix G.2.2 [app:inverse-image-spectrum]: the local law at the scales
`η`, `c η` and the dyadic scales `min (2^(l+1) η) 1`, `l < m`, each with failure `W^{-(D+2)}`, and
the null set where `Q^* V Q - E - B` is singular, give (9.43) [us:eq:spectrum] for the inverse with
failure `W^{-D}`. -/
private lemma compressSpec_assemble {W n d m : ℕ} {L c η C₀ μ0 D : ℝ} (hL : 1 ≤ L)
    (hc : c = 1 / (4 * L ^ 2)) (hη0 : 0 < η) (hη1 : η ≤ 1) (hn0 : 0 < n) (hnW : n ≤ W)
    (hlow : C₀ * d ≤ c * η * n / (2 * L)) (hm1 : 1 ≤ 2 ^ m * η)
    (hmlog : (m : ℝ) ≤ 3 * Real.log W) (hlogW : 1 ≤ Real.log W) (hmW : (m : ℝ) + 2 ≤ (W : ℝ) ^ 2)
    (hμ0 : μ0 ≤ c * η) (hμ1 : μ0 ≤ 1) (hcη : c * η ≤ η)
    (Q : Matrix (Fin W) (Fin n) ℂ) (hQ : Qᴴ * Q = 1) (B : Matrix (Fin n) (Fin n) ℂ)
    (hBh : B.IsHermitian) (E : ℝ)
    (hbad : ∀ τ : ℝ, μ0 ≤ τ → τ ≤ 1 →
      μ W 1 {ω | ¬ (L⁻¹ ≤
        (ntr (resolventMat (Qᴴ * gueMat W ω * Q - B) ((E : ℂ) + (τ : ℂ) * Complex.I))).im ∧
        (ntr (resolventMat (Qᴴ * gueMat W ω * Q - B) ((E : ℂ) + (τ : ℂ) * Complex.I))).im ≤ L)} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-(D + 2)))) :
    μ W 1 {ω | ¬ InvSpecInput C₀ (1 + 12 * L) (2 * L) W d η
        (Qᴴ * gueMat W ω * Q - (E : ℂ) • 1 - B)⁻¹} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have hWr0 : (0 : ℝ) < W := by exact_mod_cast lt_of_lt_of_le hn0 hnW
  have hrsc : ∀ l : ℕ, μ0 ≤ min (2 ^ (l + 1) * η) 1 := by
    intro l
    refine le_min ?_ hμ1
    have : η ≤ 2 ^ (l + 1) * η := by
      have : (1 : ℝ) ≤ 2 ^ (l + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    linarith
  set Bad : ℝ → Set (Ω W 1) := fun τ => {ω | ¬ (L⁻¹ ≤
      (ntr (resolventMat (Qᴴ * gueMat W ω * Q - B) ((E : ℂ) + (τ : ℂ) * Complex.I))).im ∧
      (ntr (resolventMat (Qᴴ * gueMat W ω * Q - B) ((E : ℂ) + (τ : ℂ) * Complex.I))).im ≤ L)}
    with hBad
  set Z : Set (Ω W 1) := {ω | (Qᴴ * gueMat W ω * Q - (E : ℂ) • 1 - B).det = (0 : ℂ)} with hZdef
  have hZ : μ W 1 Z = 0 := compressSpec_null W n hn0 hnW Q hQ B hBh E
  have hsub : {ω | ¬ InvSpecInput C₀ (1 + 12 * L) (2 * L) W d η
      (Qᴴ * gueMat W ω * Q - (E : ℂ) • 1 - B)⁻¹} ⊆
      Z ∪ (Bad η ∪ (Bad (c * η) ∪ ⋃ l ∈ Finset.range m, Bad (min (2 ^ (l + 1) * η) 1))) := by
    intro ω hω
    by_contra hcon
    have hZ' : ω ∉ Z := fun h => hcon (Or.inl h)
    have hB1 : ω ∉ Bad η := fun h => hcon (Or.inr (Or.inl h))
    have hB2 : ω ∉ Bad (c * η) := fun h => hcon (Or.inr (Or.inr (Or.inl h)))
    have hB3 : ∀ l ∈ Finset.range m, ω ∉ Bad (min (2 ^ (l + 1) * η) 1) :=
      fun l hl h => hcon (Or.inr (Or.inr (Or.inr (Set.mem_biUnion hl h))))
    have hgood : ∀ τ : ℝ, ω ∉ Bad τ →
        L⁻¹ ≤ (ntr (resolventMat (Qᴴ * gueMat W ω * Q - (E : ℂ) • 1 - B)
          (((0 : ℝ) : ℂ) + (τ : ℂ) * Complex.I))).im ∧
        (ntr (resolventMat (Qᴴ * gueMat W ω * Q - (E : ℂ) • 1 - B)
          (((0 : ℝ) : ℂ) + (τ : ℂ) * Complex.I))).im ≤ L := by
      intro τ h
      have h' : L⁻¹ ≤ (ntr (resolventMat (Qᴴ * gueMat W ω * Q - B)
            ((E : ℂ) + (τ : ℂ) * Complex.I))).im ∧
          (ntr (resolventMat (Qᴴ * gueMat W ω * Q - B)
            ((E : ℂ) + (τ : ℂ) * Complex.I))).im ≤ L := by
        by_contra hc'
        exact h hc'
      rw [compressSpec_resolvent_shift] at h'
      exact h'
    have hMh := compressSpec_isHermitian Q hBh E ω
    have hMu : IsUnit (Qᴴ * gueMat W ω * Q - (E : ℂ) • 1 - B) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hZ')
    exact hω (compressSpec_det hMh hMu hL hc hη0 hη1 hn0 hnW hlow (hgood η hB1).2
      (hgood (c * η) hB2).1 (fun l hl => (hgood _ (hB3 l (Finset.mem_range.mpr hl))).2)
      hm1 hmlog hlogW)
  set x : ENNReal := ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) with hx
  have hxη : μ W 1 (Bad η) ≤ x := hbad η (hμ0.trans (by nlinarith [hη0, hcη])) hη1
  have hxc : μ W 1 (Bad (c * η)) ≤ x := hbad (c * η) hμ0 (hcη.trans hη1)
  have hxr : ∀ l ∈ Finset.range m, μ W 1 (Bad (min (2 ^ (l + 1) * η) 1)) ≤ x :=
    fun l _ => hbad _ (hrsc l) (min_le_right _ _)
  have hsum : ∑ l ∈ Finset.range m, μ W 1 (Bad (min (2 ^ (l + 1) * η) 1)) ≤ m * x := by
    calc _ ≤ ∑ l ∈ Finset.range m, x := Finset.sum_le_sum hxr
      _ = m * x := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hunion : μ W 1 (Z ∪ (Bad η ∪ (Bad (c * η) ∪ ⋃ l ∈ Finset.range m,
      Bad (min (2 ^ (l + 1) * η) 1)))) ≤
      μ W 1 Z + (μ W 1 (Bad η) + (μ W 1 (Bad (c * η)) +
        ∑ l ∈ Finset.range m, μ W 1 (Bad (min (2 ^ (l + 1) * η) 1)))) :=
    (measure_union_le _ _).trans (add_le_add le_rfl ((measure_union_le _ _).trans
      (add_le_add le_rfl ((measure_union_le _ _).trans
        (add_le_add le_rfl (measure_biUnion_finset_le _ _))))))
  have hfinal : ((m : ENNReal) + 2) * x ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
    have hcast : ((m : ENNReal) + 2) = ENNReal.ofReal ((m : ℝ) + 2) := by
      rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_two, ENNReal.ofReal_natCast,
        ENNReal.ofReal_ofNat]
    rw [hcast, hx, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (W : ℝ) ^ (-(D + 2)) = (W : ℝ) ^ (-D) * ((W : ℝ) ^ 2)⁻¹ := by
      rw [show -(D + 2) = -D + -(2 : ℝ) by ring, Real.rpow_add hWr0, Real.rpow_neg hWr0.le 2,
        Real.rpow_two]
    have h2 : ((m : ℝ) + 2) * ((W : ℝ) ^ 2)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]
      exact hmW
    have h3 : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg hWr0.le _
    calc ((m : ℝ) + 2) * (W : ℝ) ^ (-(D + 2))
        = (W : ℝ) ^ (-D) * (((m : ℝ) + 2) * ((W : ℝ) ^ 2)⁻¹) := by rw [h1]; ring
      _ ≤ (W : ℝ) ^ (-D) * 1 := mul_le_mul_of_nonneg_left h2 h3
      _ = _ := mul_one _
  calc μ W 1 {ω | ¬ InvSpecInput C₀ (1 + 12 * L) (2 * L) W d η
          (Qᴴ * gueMat W ω * Q - (E : ℂ) • 1 - B)⁻¹}
      ≤ μ W 1 (Z ∪ (Bad η ∪ (Bad (c * η) ∪ ⋃ l ∈ Finset.range m,
          Bad (min (2 ^ (l + 1) * η) 1)))) := measure_mono hsub
    _ ≤ _ := hunion
    _ ≤ 0 + (x + (x + m * x)) := by
        rw [hZ]
        exact add_le_add le_rfl (add_le_add hxη (add_le_add hxc hsum))
    _ = ((m : ENNReal) + 2) * x := by ring
    _ ≤ _ := hfinal

/-- (9.48) [us:eq:complement-spectrum]: for every `C₀ > 0` there are `ε₀, A, C, C₁` such that,
for `n + d = W`, `W^δ ≤ d ≤ ε₀ W`, an isometry `Q : W × n`, a Hermitian `B` with `‖B‖ ≤ ε₀` and
`|E| ≤ 2 - κ₀`, the inverse `(Q* V Q - E - B)⁻¹` satisfies (9.43) [us:eq:spectrum] at
`η = A d / W` with probability `≥ 1 - W^{-D}` (Appendix G.2.2 [app:inverse-image-spectrum]). -/
theorem compress_specInput (κ₀ : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ ε₀ A C C₁ : ℝ, 0 < ε₀ ∧ 0 < A ∧ 0 < C ∧ 0 < C₁ ∧ ∀ δ D : ℝ, 0 < δ → 0 < D →
      ∃ W₀ : ℕ, ∀ W n d : ℕ, W₀ ≤ W → n + d = W → (W : ℝ) ^ δ ≤ d → (d : ℝ) ≤ ε₀ * W →
        ∀ (Q : Matrix (Fin W) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (E : ℝ),
        Qᴴ * Q = 1 → B.IsHermitian → ‖B‖ ≤ ε₀ → |E| ≤ 2 - κ₀ →
        μ W 1 {ω | ¬ InvSpecInput C₀ C C₁ W d (A * d / W)
            (Qᴴ * gueMat W ω * Q - (E : ℂ) • 1 - B)⁻¹} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have _ := hC₀
  obtain ⟨εL, L, hεL, hL, hLL⟩ := localLaw_avg_asymp_compress κ₀ hκ₀ hκ₀'
  have hL0 : 0 < L := by linarith
  set c : ℝ := 1 / (4 * L ^ 2) with hc
  have hc0 : 0 < c := by positivity
  set A : ℝ := max 1 (4 * C₀ * L / c) with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA2 : 4 * C₀ * L / c ≤ A := le_max_right _ _
  have hA0 : 0 < A := by linarith
  set ε₀ : ℝ := min (min εL (κ₀ / 4)) (min (1 / A) (1 / 2)) with hε₀
  have hε₀0 : 0 < ε₀ :=
    lt_min (lt_min hεL (by linarith)) (lt_min (by positivity) (by norm_num))
  have hε₁ : ε₀ ≤ εL := (min_le_left _ _).trans (min_le_left _ _)
  have hε₂ : ε₀ ≤ κ₀ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hε₃ : ε₀ ≤ 1 / A := (min_le_right _ _).trans (min_le_left _ _)
  have hε₄ : ε₀ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε₀, A, 1 + 12 * L, 2 * L, hε₀0, hA0, by positivity, by positivity, ?_⟩
  intro δ D hδ hD
  obtain ⟨W₁, hW₁⟩ := hLL ε₀ (δ / 2) (D + 2) hε₀0 hε₁ (by positivity) (by linarith)
  refine ⟨max (max W₁ 8) ⌈(1 / (c * A)) ^ (2 / δ)⌉₊, ?_⟩
  intro W n d hW hnd hdW hdε Q B E hQ hBh hB hE
  have hW1 : W₁ ≤ W := ((le_max_left _ _).trans (le_max_left _ _)).trans hW
  have hW8 : 8 ≤ W := ((le_max_right _ _).trans (le_max_left _ _)).trans hW
  have hW2 : ⌈(1 / (c * A)) ^ (2 / δ)⌉₊ ≤ W := (le_max_right _ _).trans hW
  have hWr8 : (8 : ℝ) ≤ W := by exact_mod_cast hW8
  have hWr0 : (0 : ℝ) < W := by linarith
  have hndr : (n : ℝ) + d = W := by exact_mod_cast hnd
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le (Real.rpow_pos_of_pos hWr0 δ) hdW
  have hd1 : (1 : ℝ) ≤ d := by
    have : 0 < d := by exact_mod_cast hdpos
    exact_mod_cast this
  have hεW : ε₀ * W ≤ (1 / 2) * W := mul_le_mul_of_nonneg_right hε₄ hWr0.le
  have hnhalf : (W : ℝ) / 2 ≤ n := by linarith
  have hnr0 : (0 : ℝ) < n := by linarith
  have hn0 : 0 < n := by exact_mod_cast hnr0
  have hnW : n ≤ W := by omega
  have hcomp : ((W - n : ℕ) : ℝ) ≤ κ₀ * W / 4 := by
    have : W - n = d := by omega
    rw [this]
    calc (d : ℝ) ≤ ε₀ * W := hdε
      _ ≤ (κ₀ / 4) * W := mul_le_mul_of_nonneg_right hε₂ hWr0.le
      _ = κ₀ * W / 4 := by ring
  -- the scale `η = A d / W`
  set η : ℝ := A * d / W with hη
  have hη0 : 0 < η := by positivity
  have hWη' : (W : ℝ) * η = A * d := by rw [hη]; field_simp
  have hη1 : η ≤ 1 := by
    have h1 : η ≤ A * ε₀ := by
      rw [hη, div_le_iff₀ hWr0]
      calc A * d ≤ A * (ε₀ * W) := mul_le_mul_of_nonneg_left hdε hA0.le
        _ = A * ε₀ * W := by ring
    have h2 : A * ε₀ ≤ 1 :=
      calc A * ε₀ ≤ A * (1 / A) := mul_le_mul_of_nonneg_left hε₃ hA0.le
        _ = 1 := by field_simp
    linarith
  have hWη : 1 ≤ (W : ℝ) * η := by
    rw [hWη']
    exact one_le_mul_of_one_le_of_one_le hA1 hd1
  have hc1 : c ≤ 1 := by
    have : 1 ≤ L ^ 2 := one_le_pow₀ hL
    rw [hc, div_le_one (by positivity)]; linarith
  have hcη : c * η ≤ η :=
    calc c * η ≤ 1 * η := mul_le_mul_of_nonneg_right hc1 hη0.le
      _ = η := one_mul _
  -- the lowest scale of the local law
  have hkey : 1 ≤ c * A * (W : ℝ) ^ (δ / 2) := by
    have h1 : 1 / (c * A) ≤ (W : ℝ) ^ (δ / 2) := by
      have h2 : (1 / (c * A)) ^ (2 / δ) ≤ W :=
        (Nat.le_ceil _).trans (by exact_mod_cast hW2)
      have h3 := Real.rpow_le_rpow (by positivity) h2 (by positivity : (0 : ℝ) ≤ δ / 2)
      rwa [← Real.rpow_mul (by positivity), show 2 / δ * (δ / 2) = 1 by field_simp,
        Real.rpow_one] at h3
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  have hμ0η := compressSpec_lowscale (by omega : 0 < W) hc0 hA0 hdW hkey
  have hμ1 : (W : ℝ) ^ (-1 + δ / 2) ≤ 1 := by
    have hδ1 : δ < 1 := by
      by_contra hcon
      have h1 : (W : ℝ) ^ (1 : ℝ) ≤ (W : ℝ) ^ δ :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (not_lt.1 hcon)
      rw [Real.rpow_one] at h1
      linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hdef : DeformClass ε₀ B :=
    ⟨hBh, B, 0, (add_zero B).symm, hB, by
      simp only [Matrix.rank_zero, CharP.cast_eq_zero, Fintype.card_fin]; positivity⟩
  obtain ⟨hm1, hmlog, hlogW, hmW⟩ := compressSpec_scales hW8 hη0 hWη
  have hlow : C₀ * d ≤ c * η * n / (2 * L) := by
    have h1 : c * η * (W / 2) ≤ c * η * n := mul_le_mul_of_nonneg_left hnhalf (by positivity)
    have h4 : c * η * (W / 2) = c * (A * d) / 2 := by rw [← hWη']; ring
    have h5 : 4 * C₀ * L ≤ c * A := by
      have := hA2
      rw [div_le_iff₀ hc0] at this
      linarith
    have h3 : C₀ * d * (4 * L) ≤ c * (A * d) :=
      calc C₀ * d * (4 * L) = (4 * C₀ * L) * d := by ring
        _ ≤ (c * A) * d := mul_le_mul_of_nonneg_right h5 hdpos.le
        _ = c * (A * d) := by ring
    rw [le_div_iff₀ (by positivity)]
    linarith
  exact compressSpec_assemble hL hc hη0 hη1 hn0 hnW hlow hm1 hmlog hlogW hmW hμ0η hμ1 hcη
    Q hQ B hBh E (fun τ h0 h1 => hW₁ W n hW1 hnW hcomp Q B E τ hQ hdef hE h0 h1)

end LSBA
