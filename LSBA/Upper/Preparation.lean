import LSBA.Upper.PrepGood
import LSBA.Spectral.DeformedRelLaw

/-!
# Preparation of the incoming flag at weak coupling

Lemma 9.1 [su:lem:preparation] in regime (i) of Lemma 8.12 [up:lem:small-contraction]: for
`0 < α < β < 1/2`, `ε > 0` and `g = W^{-a}` with `a ∈ [α, β]`, the four preparation blocks put
every incoming flag in the graph chart (9.1) [su:eq:graph-input], and the prepared data satisfy
(9.5) [su:eq:prep] and (9.6) [su:eq:prepared-large-rank], except with probability
`C (W^{-2} + W^{-α/2} + W^{-ε/800})`, uniformly in the flag, `|E| ≤ 2 - κ₀` and `a`.

Regularity of `R_3` and `R_4` and the rank bound come from (9.58) [us:eq:wegner]. For
`b_4 ≤ C ‖P v_4‖²`, put `u = R_4⁻¹ v_4 = v_3`, fixed before `V_4`, so that
`b_4 = g⁻² Im u*(R_4⁻¹ - i g²)⁻¹ u`. The relative local law (G.2) [us:eq:relative-local-law] for
`B = g² R_3` at `η = c g², g², C g²` compares the three Poisson integrals with
`u*(1 + g⁴R_3²)⁻¹u`; small `c` and large `C` leave a fixed fraction of the integral at `g²` on the
annulus `c g² ≤ |λ| ≤ C g²`, which `P` retains for large `W`, and there the Poisson and
inverse-square kernels are comparable. With `‖R_3‖, ‖R_4‖ ≤ W³` this gives
`‖P v_4‖ ≥ W^{-10} ‖v_4‖`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `U diag(d) U*`, a matrix diagonal in the orthonormal basis of the columns of `U`. -/
private def preparation_conj {W : ℕ} (U : Matrix (Fin W) (Fin W) ℂ) (d : Fin W → ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  U * Matrix.diagonal d * Uᴴ

/-- `U diag(d) U* · U diag(e) U* = U diag(d e) U*` for `U*U = 1`. -/
private lemma preparation_conj_mul {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : Uᴴ * U = 1)
    (d e : Fin W → ℂ) :
    preparation_conj U d * preparation_conj U e = preparation_conj U (fun k => d k * e k) := by
  unfold preparation_conj
  calc U * Matrix.diagonal d * Uᴴ * (U * Matrix.diagonal e * Uᴴ)
      = U * Matrix.diagonal d * (Uᴴ * U) * Matrix.diagonal e * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hU, Matrix.mul_one, Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]

/-- `U diag(1) U* = 1` for `U U* = 1`. -/
private lemma preparation_conj_one {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : U * Uᴴ = 1) :
    preparation_conj U (fun _ => 1) = 1 := by
  unfold preparation_conj
  rw [Matrix.diagonal_one, Matrix.mul_one, hU]

/-- `c · U diag(d) U* = U diag(c d) U*`. -/
private lemma preparation_conj_smul {W : ℕ} (U : Matrix (Fin W) (Fin W) ℂ) (c : ℂ)
    (d : Fin W → ℂ) : c • preparation_conj U d = preparation_conj U (fun k => c * d k) := by
  unfold preparation_conj
  have : Matrix.diagonal (fun k => c * d k) = c • Matrix.diagonal d := by
    rw [← Matrix.diagonal_smul]; rfl
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

/-- `U diag(d) U* + U diag(e) U* = U diag(d + e) U*`. -/
private lemma preparation_conj_add {W : ℕ} (U : Matrix (Fin W) (Fin W) ℂ) (d e : Fin W → ℂ) :
    preparation_conj U d + preparation_conj U e = preparation_conj U (fun k => d k + e k) := by
  unfold preparation_conj
  rw [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]

/-- `U diag(d) U* - U diag(e) U* = U diag(d - e) U*`. -/
private lemma preparation_conj_sub {W : ℕ} (U : Matrix (Fin W) (Fin W) ℂ) (d e : Fin W → ℂ) :
    preparation_conj U d - preparation_conj U e = preparation_conj U (fun k => d k - e k) := by
  unfold preparation_conj
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]

/-- `(U diag(d) U*)⁻¹ = U diag(d⁻¹) U*` for unitary `U` and nonzero `d`. -/
private lemma preparation_conj_inv {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU1 : Uᴴ * U = 1)
    (hU2 : U * Uᴴ = 1) {d : Fin W → ℂ} (hd : ∀ k, d k ≠ 0) :
    (preparation_conj U d)⁻¹ = preparation_conj U (fun k => (d k)⁻¹) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [preparation_conj_mul hU1]
  simp only [mul_inv_cancel₀ (hd _)]
  exact preparation_conj_one hU2

/-- `U diag(d) U* (U b) = U (d b)` for `U*U = 1`. -/
private lemma preparation_conj_mulVec {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : Uᴴ * U = 1)
    (d b : Fin W → ℂ) :
    preparation_conj U d *ᵥ (U *ᵥ b) = U *ᵥ (fun k => d k * b k) := by
  unfold preparation_conj
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hU, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  congr 1
  funext k
  exact Matrix.mulVec_diagonal d b k

/-- `(U a)* (U b) = a* b` for `U*U = 1`. -/
private lemma preparation_dot {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : Uᴴ * U = 1)
    (a b : Fin W → ℂ) : star (U *ᵥ a) ⬝ᵥ (U *ᵥ b) = ∑ k, star (a k) * b k := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU,
    Matrix.one_mulVec]
  rfl

/-- `‖U a‖² = Σ |a_k|²` for `U*U = 1`. -/
private lemma preparation_l2Norm_sq {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : Uᴴ * U = 1)
    (a : Fin W → ℂ) : l2Norm (U *ᵥ a) ^ 2 = ∑ k, ‖a k‖ ^ 2 := by
  have h1 : l2Norm (U *ᵥ a) ^ 2 = ∑ i, ‖(U *ᵥ a) i‖ ^ 2 := by
    unfold l2Norm
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  have h2 : ∀ v : Fin W → ℂ, ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) = ∑ i, star (v i) * v i := fun v => by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  rw [h1]
  have h3 := preparation_dot hU a a
  have h4 : star (U *ᵥ a) ⬝ᵥ (U *ᵥ a) = ∑ i, star ((U *ᵥ a) i) * (U *ᵥ a) i := rfl
  rw [h4, ← h2, ← h2] at h3
  exact_mod_cast h3

/-- The spectral projection of a Hermitian matrix in its eigenvector basis. -/
private lemma preparation_specProj_eq {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian)
    (S : Set ℝ) :
    specProj A S = preparation_conj (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
      (fun k => if hA.eigenvalues k ∈ S then (1 : ℂ) else 0) := by
  unfold preparation_conj
  simp only [specProj, hA, ↓reduceDIte]
  ext i j
  rw [Finset.sum_filter, Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : hA.eigenvalues c ∈ S <;> simp [h, Matrix.vecMulVec_apply, mul_comm]

/-- A Hermitian matrix in its eigenvector basis. -/
private lemma preparation_spectral {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) :
    A = preparation_conj (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
      (fun k => (hA.eigenvalues k : ℂ)) := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

/-- `|λ_k| ≤ ‖A‖` for the eigenvalues of a Hermitian matrix. -/
private lemma preparation_abs_eig_le {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian)
    (k : Fin W) : |hA.eigenvalues k| ≤ ‖A‖ := by
  set v : EuclideanSpace ℂ (Fin W) := hA.eigenvectorBasis k with hv
  have hv1 : ‖v‖ = 1 := (hA.eigenvectorBasis).norm_eq_one k
  have h1 := hA.mulVec_eigenvectorBasis k
  have h2 := Matrix.l2_opNorm_mulVec A v
  have h3 : (EuclideanSpace.equiv (Fin W) ℂ).symm (A *ᵥ (v : Fin W → ℂ)) =
      ((hA.eigenvalues k : ℝ) : ℂ) • v := by
    rw [hv, h1]
    rfl
  rw [h3, norm_smul, hv1, mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs] at h2
  exact h2

/-- `Im z̄ (r⁻¹ - iη)⁻¹ z = |z|² η r² / (1 + η² r²)` for real `r ≠ 0`. -/
private lemma preparation_im_term {r : ℝ} (hr : r ≠ 0) (η : ℝ) (z : ℂ) :
    (star z * ((((r : ℂ))⁻¹ - (η : ℂ) * Complex.I)⁻¹ * z)).im =
      ‖z‖ ^ 2 * (η * r ^ 2 / (1 + η ^ 2 * r ^ 2)) := by
  have e : star z * ((((r : ℂ))⁻¹ - (η : ℂ) * Complex.I)⁻¹ * z) =
      (((r : ℂ))⁻¹ - (η : ℂ) * Complex.I)⁻¹ * ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, mul_left_comm, Complex.conj_mul']
    push_cast
    ring
  rw [e, Complex.im_mul_ofReal, Complex.inv_im, Complex.normSq_apply]
  have h1 : (((r : ℂ))⁻¹ - (η : ℂ) * Complex.I).re = r⁻¹ := by
    simp [← Complex.ofReal_inv]
  have h2 : (((r : ℂ))⁻¹ - (η : ℂ) * Complex.I).im = -η := by
    simp [← Complex.ofReal_inv]
  rw [h1, h2]
  have hr2 : 0 < r ^ 2 := by positivity
  field_simp

/-- `Re (r z)* (1 + g⁴ r²)⁻¹ (r z) = |z|² r² / (1 + g⁴ r²)` for real `r`, `g`. -/
private lemma preparation_re_term (r g : ℝ) (z : ℂ) :
    (star ((r : ℂ) * z) * ((1 + (g : ℂ) ^ 4 * ((r : ℂ) * (r : ℂ)))⁻¹ * ((r : ℂ) * z))).re =
      ‖z‖ ^ 2 * (r ^ 2 / (1 + g ^ 4 * r ^ 2)) := by
  have e : star ((r : ℂ) * z) * ((1 + (g : ℂ) ^ 4 * ((r : ℂ) * (r : ℂ)))⁻¹ * ((r : ℂ) * z)) =
      ((‖z‖ ^ 2 * (r ^ 2 / (1 + g ^ 4 * r ^ 2)) : ℝ) : ℂ) := by
    have hpos : (1 + g ^ 4 * r ^ 2 : ℝ) ≠ 0 := by positivity
    have hc : (1 + (g : ℂ) ^ 4 * ((r : ℂ) * (r : ℂ))) = ((1 + g ^ 4 * r ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hc, Complex.star_def, map_mul, Complex.conj_ofReal]
    have : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']; push_cast; ring
    calc (r : ℂ) * (starRingEnd ℂ) z * (((1 + g ^ 4 * r ^ 2 : ℝ) : ℂ)⁻¹ * ((r : ℂ) * z))
        = (r : ℂ) * (r : ℂ) * ((starRingEnd ℂ) z * z) * ((1 + g ^ 4 * r ^ 2 : ℝ) : ℂ)⁻¹ := by
          ring
      _ = _ := by
          rw [this]
          push_cast
          field_simp
  rw [e, Complex.ofReal_re]

/-- The kernel comparison in the proof of Lemma 9.1 [su:lem:preparation], regime (i), in the
eigenbasis: with weights `p_k ≥ 0`, eigenvalues `r_k` of `R` with `r_k² ≤ W⁶`, the Poisson
integrals `I(η) = Σ p_k η r_k² / (1 + η² r_k²)` with `I(c g²) ≤ C N`, `C⁻¹ N ≤ I(g²)` and
`c = 1/(4C²)`, and a cutoff `ind` equal to `1` where `|g² r_k| ≤ T` (`T ≥ 4C²`):
`b = Σ p_k r_k² / (1 + g⁴ r_k²) ≤ 2 Σ ind_k r_k² p_k` and
`W^{-20} Σ r_k² p_k ≤ Σ ind_k r_k² p_k`. -/
private lemma preparation_kernel {W : ℕ} (hW : 2 ≤ W) {g CL T η N : ℝ} (hg : 0 < g)
    (hg1 : g ≤ 1) (hCL : 1 ≤ CL) (hη : η = g ^ 2 / (4 * CL ^ 2)) (hT : 4 * CL ^ 2 ≤ T)
    (p r ind : Fin W → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hrW : ∀ k, r k ^ 2 ≤ ((W : ℝ) ^ 3) ^ 2)
    (hind0 : ∀ k, 0 ≤ ind k) (hind1 : ∀ k, |g ^ 2 * r k| ≤ T → ind k = 1)
    (h1 : ∑ k, p k * (η * r k ^ 2 / (1 + η ^ 2 * r k ^ 2)) ≤ CL * N)
    (h2 : CL⁻¹ * N ≤ ∑ k, p k * (g ^ 2 * r k ^ 2 / (1 + (g ^ 2) ^ 2 * r k ^ 2))) :
    ∑ k, p k * (r k ^ 2 / (1 + g ^ 4 * r k ^ 2)) ≤ 2 * ∑ k, ind k * (r k ^ 2 * p k) ∧
      ((W : ℝ) ^ (-10 : ℝ)) ^ 2 * ∑ k, r k ^ 2 * p k ≤ ∑ k, ind k * (r k ^ 2 * p k) := by
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  have hη0 : 0 < η := by rw [hη]; positivity
  have hCL0 : 0 < CL := by linarith
  set b := ∑ k, p k * (r k ^ 2 / (1 + g ^ 4 * r k ^ 2)) with hbdef
  set SQ := ∑ k, ind k * (r k ^ 2 * p k) with hSQ
  set Ic := ∑ k, p k * (η * r k ^ 2 / (1 + η ^ 2 * r k ^ 2)) with hIc
  have hSQ0 : 0 ≤ SQ := Finset.sum_nonneg fun k _ => by
    have := hp0 k
    have := hind0 k
    positivity
  have hI1b : ∑ k, p k * (g ^ 2 * r k ^ 2 / (1 + (g ^ 2) ^ 2 * r k ^ 2)) = g ^ 2 * b := by
    rw [hbdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hI1b] at h2
  -- pointwise comparison of the kernels
  have hpt : ∀ k, g ^ 2 * (p k * (r k ^ 2 / (1 + g ^ 4 * r k ^ 2))) ≤
      2 * (1 / (4 * CL ^ 2)) * (p k * (η * r k ^ 2 / (1 + η ^ 2 * r k ^ 2))) +
        g ^ 2 * (ind k * (r k ^ 2 * p k)) := by
    intro k
    have hpk := hp0 k
    have hik := hind0 k
    have hd : 0 < 1 + g ^ 4 * r k ^ 2 := by positivity
    have hd' : 0 < 1 + η ^ 2 * r k ^ 2 := by positivity
    by_cases hc : η ^ 2 * r k ^ 2 ≤ 1
    · have hin : ind k = 1 := by
        refine hind1 k ?_
        have hηr : |η * r k| ≤ 1 := by
          rw [← sq_le_one_iff_abs_le_one, mul_pow]; exact hc
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < g ^ 2)]
        have hg2η : g ^ 2 = 4 * CL ^ 2 * η := by rw [hη]; field_simp
        rw [abs_mul, abs_of_pos hη0] at hηr
        rw [hg2η]
        nlinarith [abs_nonneg (r k)]
      rw [hin]
      have h1' : 0 ≤ 2 * (1 / (4 * CL ^ 2)) * (p k * (η * r k ^ 2 / (1 + η ^ 2 * r k ^ 2))) := by
        positivity
      have h2' : r k ^ 2 / (1 + g ^ 4 * r k ^ 2) ≤ r k ^ 2 :=
        div_le_self (sq_nonneg _) (by nlinarith [sq_nonneg (r k), pow_nonneg hg.le 4])
      have h3' : g ^ 2 * (p k * (r k ^ 2 / (1 + g ^ 4 * r k ^ 2))) ≤ g ^ 2 * (p k * r k ^ 2) := by
        gcongr
      have e : g ^ 2 * (1 * (r k ^ 2 * p k)) = g ^ 2 * (p k * r k ^ 2) := by ring
      linarith
    · rw [not_le] at hc
      have hA1 : r k ^ 2 / (1 + g ^ 4 * r k ^ 2) ≤ 1 / g ^ 4 := by
        rw [div_le_div_iff₀ hd (by positivity)]
        nlinarith
      have hA2 : 1 / g ^ 2 ≤ 2 * (1 / (4 * CL ^ 2)) * (η * r k ^ 2 / (1 + η ^ 2 * r k ^ 2)) := by
        have hg2η : 1 / (4 * CL ^ 2) = η / g ^ 2 := by rw [hη]; field_simp
        rw [hg2η, div_le_iff₀ (by positivity)]
        rw [show 2 * (η / g ^ 2) * (η * r k ^ 2 / (1 + η ^ 2 * r k ^ 2)) * g ^ 2 =
          2 * (η ^ 2 * r k ^ 2) / (1 + η ^ 2 * r k ^ 2) by field_simp]
        rw [le_div_iff₀ hd']
        linarith
      have h4' : 0 ≤ g ^ 2 * (ind k * (r k ^ 2 * p k)) := by positivity
      calc g ^ 2 * (p k * (r k ^ 2 / (1 + g ^ 4 * r k ^ 2)))
          ≤ g ^ 2 * (p k * (1 / g ^ 4)) := by gcongr
        _ = p k * (1 / g ^ 2) := by field_simp
        _ ≤ p k * (2 * (1 / (4 * CL ^ 2)) * (η * r k ^ 2 / (1 + η ^ 2 * r k ^ 2))) := by
            gcongr
        _ = 2 * (1 / (4 * CL ^ 2)) * (p k * (η * r k ^ 2 / (1 + η ^ 2 * r k ^ 2))) := by ring
        _ ≤ _ := le_add_of_nonneg_right h4'
  have hsum : g ^ 2 * b ≤ 2 * (1 / (4 * CL ^ 2)) * Ic + g ^ 2 * SQ := by
    rw [hbdef, hIc, hSQ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => hpt k
  have hN : N ≤ CL * (g ^ 2 * b) := by
    rwa [inv_mul_le_iff₀ hCL0] at h2
  have hIcb : Ic ≤ CL * (CL * (g ^ 2 * b)) :=
    h1.trans (mul_le_mul_of_nonneg_left hN hCL0.le)
  have hhalf : 2 * (1 / (4 * CL ^ 2)) * (CL * (CL * (g ^ 2 * b))) = g ^ 2 * b / 2 := by
    field_simp
    ring
  have hb2 : b ≤ 2 * SQ := by
    have h5 : 2 * (1 / (4 * CL ^ 2)) * Ic ≤ g ^ 2 * b / 2 := by
      rw [← hhalf]; gcongr
    have h6 : g ^ 2 * b ≤ g ^ 2 * (2 * SQ) := by linarith
    exact le_of_mul_le_mul_left h6 (by positivity)
  refine ⟨hb2, ?_⟩
  -- `Σ r_k² p_k ≤ 2 W⁶ b`
  have hSV : ∑ k, r k ^ 2 * p k ≤ 2 * ((W : ℝ) ^ 3) ^ 2 * b := by
    rw [hbdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hpk := hp0 k
    have hd : 0 < 1 + g ^ 4 * r k ^ 2 := by positivity
    have hW3 : (1 : ℝ) ≤ ((W : ℝ) ^ 3) ^ 2 := one_le_pow₀ (one_le_pow₀ (by linarith))
    have hg4 : g ^ 4 ≤ 1 := pow_le_one₀ hg.le hg1
    have e : r k ^ 2 * p k =
        p k * (r k ^ 2 / (1 + g ^ 4 * r k ^ 2)) * (1 + g ^ 4 * r k ^ 2) := by
      field_simp
    rw [e]
    have hx : 0 ≤ p k * (r k ^ 2 / (1 + g ^ 4 * r k ^ 2)) := by positivity
    have hle : 1 + g ^ 4 * r k ^ 2 ≤ 2 * ((W : ℝ) ^ 3) ^ 2 := by
      have := mul_le_mul hg4 (hrW k) (sq_nonneg _) zero_le_one
      linarith
    calc p k * (r k ^ 2 / (1 + g ^ 4 * r k ^ 2)) * (1 + g ^ 4 * r k ^ 2)
        ≤ p k * (r k ^ 2 / (1 + g ^ 4 * r k ^ 2)) * (2 * ((W : ℝ) ^ 3) ^ 2) :=
          mul_le_mul_of_nonneg_left hle hx
      _ = _ := by ring
  have hW10 : ((W : ℝ) ^ (-10 : ℝ)) ^ 2 * (4 * ((W : ℝ) ^ 3) ^ 2) ≤ 1 := by
    have e : ((W : ℝ) ^ (-10 : ℝ)) ^ 2 = ((W : ℝ) ^ 20)⁻¹ := by
      rw [Real.rpow_neg (by positivity), show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, inv_pow, ← pow_mul]
    rw [e, inv_mul_le_iff₀ (by positivity), mul_one]
    have h14 : (4 : ℝ) ≤ (W : ℝ) ^ 14 :=
      calc (4 : ℝ) ≤ 2 ^ 14 := by norm_num
        _ ≤ (W : ℝ) ^ 14 := pow_le_pow_left₀ (by norm_num) hW2 14
    calc 4 * ((W : ℝ) ^ 3) ^ 2 ≤ (W : ℝ) ^ 14 * ((W : ℝ) ^ 3) ^ 2 := by gcongr
      _ = (W : ℝ) ^ 20 := by ring
  have hx : 0 ≤ ((W : ℝ) ^ (-10 : ℝ)) ^ 2 := sq_nonneg _
  calc ((W : ℝ) ^ (-10 : ℝ)) ^ 2 * ∑ k, r k ^ 2 * p k
      ≤ ((W : ℝ) ^ (-10 : ℝ)) ^ 2 * (4 * ((W : ℝ) ^ 3) ^ 2 * SQ) := by
        refine mul_le_mul_of_nonneg_left (hSV.trans ?_) hx
        have : 0 ≤ ((W : ℝ) ^ 3) ^ 2 := sq_nonneg _
        nlinarith
    _ = ((W : ℝ) ^ (-10 : ℝ)) ^ 2 * (4 * ((W : ℝ) ^ 3) ^ 2) * SQ := by ring
    _ ≤ 1 * SQ := mul_le_mul_of_nonneg_right hW10 hSQ0
    _ = SQ := one_mul _

/-- The deterministic core of the comparison in the proof of Lemma 9.1 [su:lem:preparation],
regime (i): let `Γ` be invertible with `R = Γ⁻¹` regular (9.3) [us:eq:regular], and let the
Poisson integrals `I(η) = Im u*(Γ - iη)⁻¹u` satisfy `I(c g²) ≤ C N` and `C⁻¹ N ≤ I(g²)` with
`c = 1/(4C²)`. Then, with `v = R u` and `P = 1_{[-T, T]}(g² R)` for `T ≥ 4C²`,
`v*(1 + g⁴R²)⁻¹v ≤ 2 ‖P v‖²` and `‖P v‖ ≥ W^{-10} ‖v‖`. -/
private lemma preparation_core {W : ℕ} (hW : 2 ≤ W) {g CL T η : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (hCL : 1 ≤ CL) (hη : η = g ^ 2 / (4 * CL ^ 2)) (hT : 4 * CL ^ 2 ≤ T)
    {Γ : Matrix (Fin W) (Fin W) ℂ} (hΓ : IsUnit Γ) (hR : IsRegularState W g Γ⁻¹)
    (u : Fin W → ℂ) (N : ℝ)
    (h1 : (star u ⬝ᵥ ((Γ - ((η : ℂ) * Complex.I) • 1)⁻¹ *ᵥ u)).im ≤ CL * N)
    (h2 : CL⁻¹ * N ≤ (star u ⬝ᵥ ((Γ - (((g ^ 2 : ℝ) : ℂ) * Complex.I) • 1)⁻¹ *ᵥ u)).im) :
    (W : ℝ) ^ (-10 : ℝ) * l2Norm (Γ⁻¹ *ᵥ u) ≤
        l2Norm (specProj (((g : ℂ) ^ 2) • Γ⁻¹) (Set.Icc (-T) T) *ᵥ (Γ⁻¹ *ᵥ u)) ∧
      (star (Γ⁻¹ *ᵥ u) ⬝ᵥ ((1 + ((g : ℂ) ^ 4) • (Γ⁻¹ * Γ⁻¹))⁻¹ *ᵥ (Γ⁻¹ *ᵥ u))).re ≤
        2 * l2Norm (specProj (((g : ℂ) ^ 2) • Γ⁻¹) (Set.Icc (-T) T) *ᵥ (Γ⁻¹ *ᵥ u)) ^ 2 := by
  have hk : IsSelfAdjoint ((g : ℂ) ^ 2) := by rw [isSelfAdjoint_iff]; simp
  have hg2 : ((g : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hg.ne')
  have hRH : (Γ⁻¹).IsHermitian := hR.1
  have hAH : (((g : ℂ) ^ 2) • Γ⁻¹).IsHermitian := hRH.smul hk
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (Fin W) (Fin W) ℂ,
      U = (hAH.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) := ⟨_, rfl⟩
  have hU1 : Uᴴ * U = 1 := by
    rw [hUdef]; exact Matrix.mem_unitaryGroup_iff'.mp hAH.eigenvectorUnitary.2
  have hU2 : U * Uᴴ = 1 := by
    rw [hUdef]; exact Matrix.mem_unitaryGroup_iff.mp hAH.eigenvectorUnitary.2
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin W → ℝ, μ = hAH.eigenvalues := ⟨_, rfl⟩
  set r : Fin W → ℝ := fun k => μ k / g ^ 2 with hr
  have hAconj : ((g : ℂ) ^ 2) • Γ⁻¹ = preparation_conj U (fun k => (μ k : ℂ)) := by
    rw [hUdef, hμ]; exact preparation_spectral hAH
  have hRconj : Γ⁻¹ = preparation_conj U (fun k => (r k : ℂ)) := by
    have e : Γ⁻¹ = ((g : ℂ) ^ 2)⁻¹ • (((g : ℂ) ^ 2) • Γ⁻¹) := by rw [inv_smul_smul₀ hg2]
    rw [e, hAconj, preparation_conj_smul]
    congr 1
    funext k
    simp only [hr]
    push_cast
    field_simp
  -- the eigenvalues are nonzero
  have hdetΓ : IsUnit Γ.det := (Matrix.isUnit_iff_isUnit_det Γ).mp hΓ
  have hμ0 : ∀ k, μ k ≠ 0 := by
    intro k
    have hAu : IsUnit (((g : ℂ) ^ 2) • Γ⁻¹).det := by
      rw [Matrix.det_smul]
      exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hg2)).mul
        (Matrix.isUnit_nonsing_inv_det Γ hdetΓ)
    rw [hAH.det_eq_prod_eigenvalues] at hAu
    have := (Finset.prod_ne_zero_iff.mp hAu.ne_zero) k (Finset.mem_univ k)
    rw [hμ]
    intro h
    apply this
    rw [h]
    simp
  have hr0 : ∀ k, r k ≠ 0 := fun k => div_ne_zero (hμ0 k) (by positivity)
  have hΓconj : Γ = preparation_conj U (fun k => ((r k : ℂ))⁻¹) := by
    rw [← Matrix.nonsing_inv_nonsing_inv Γ hdetΓ, hRconj]
    exact preparation_conj_inv hU1 hU2 fun k => Complex.ofReal_ne_zero.mpr (hr0 k)
  -- the resolvent
  have hres : ∀ η' : ℝ, η' ≠ 0 → (Γ - ((η' : ℂ) * Complex.I) • 1)⁻¹ =
      preparation_conj U (fun k => (((r k : ℂ))⁻¹ - (η' : ℂ) * Complex.I)⁻¹) := by
    intro η' hη'
    have e : Γ - ((η' : ℂ) * Complex.I) • 1 =
        preparation_conj U (fun k => ((r k : ℂ))⁻¹ - (η' : ℂ) * Complex.I) := by
      rw [hΓconj, ← preparation_conj_one hU2, preparation_conj_smul, preparation_conj_sub]
      simp only [mul_one]
    rw [e]
    refine preparation_conj_inv hU1 hU2 fun k h => hη' ?_
    have := congrArg Complex.im h
    simpa [← Complex.ofReal_inv] using this
  -- coordinates
  set w : Fin W → ℂ := Uᴴ *ᵥ u with hw
  have hu : u = U *ᵥ w := by rw [hw, Matrix.mulVec_mulVec, hU2, Matrix.one_mulVec]
  set p : Fin W → ℝ := fun k => ‖w k‖ ^ 2 with hp
  have hp0 : ∀ k, 0 ≤ p k := fun k => by positivity
  have hI : ∀ η' : ℝ, η' ≠ 0 → (star u ⬝ᵥ ((Γ - ((η' : ℂ) * Complex.I) • 1)⁻¹ *ᵥ u)).im =
      ∑ k, p k * (η' * r k ^ 2 / (1 + η' ^ 2 * r k ^ 2)) := by
    intro η' hη'
    rw [hres η' hη', hu, preparation_conj_mulVec hU1, preparation_dot hU1, Complex.im_sum]
    exact Finset.sum_congr rfl fun k _ => preparation_im_term (hr0 k) η' (w k)
  have hv : Γ⁻¹ *ᵥ u = U *ᵥ (fun k => (r k : ℂ) * w k) := by
    rw [hRconj, hu, preparation_conj_mulVec hU1]
  have hM : (1 + ((g : ℂ) ^ 4) • (Γ⁻¹ * Γ⁻¹))⁻¹ =
      preparation_conj U (fun k => (1 + (g : ℂ) ^ 4 * ((r k : ℂ) * (r k : ℂ)))⁻¹) := by
    rw [hRconj, preparation_conj_mul hU1, preparation_conj_smul, ← preparation_conj_one hU2,
      preparation_conj_add]
    refine preparation_conj_inv hU1 hU2 fun k => ?_
    have : (1 + (g : ℂ) ^ 4 * ((r k : ℂ) * (r k : ℂ))) = ((1 + g ^ 4 * r k ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hb : (star (Γ⁻¹ *ᵥ u) ⬝ᵥ ((1 + ((g : ℂ) ^ 4) • (Γ⁻¹ * Γ⁻¹))⁻¹ *ᵥ (Γ⁻¹ *ᵥ u))).re =
      ∑ k, p k * (r k ^ 2 / (1 + g ^ 4 * r k ^ 2)) := by
    rw [hM, hv, preparation_conj_mulVec hU1, preparation_dot hU1, Complex.re_sum]
    exact Finset.sum_congr rfl fun k _ => preparation_re_term (r k) g (w k)
  set ind : Fin W → ℝ := fun k => if μ k ∈ Set.Icc (-T) T then 1 else 0 with hind
  have hPv : l2Norm (specProj (((g : ℂ) ^ 2) • Γ⁻¹) (Set.Icc (-T) T) *ᵥ (Γ⁻¹ *ᵥ u)) ^ 2 =
      ∑ k, ind k * (r k ^ 2 * p k) := by
    rw [preparation_specProj_eq hAH, ← hUdef, ← hμ, hv, preparation_conj_mulVec hU1,
      preparation_l2Norm_sq hU1]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hind, hp]
    by_cases h : μ k ∈ Set.Icc (-T) T
    · simp [h, mul_pow]
    · simp [h]
  have hvn : l2Norm (Γ⁻¹ *ᵥ u) ^ 2 = ∑ k, r k ^ 2 * p k := by
    rw [hv, preparation_l2Norm_sq hU1]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hp, mul_pow]
  -- `|r_k| ≤ ‖R‖ ≤ W³`
  have hrW : ∀ k, r k ^ 2 ≤ ((W : ℝ) ^ 3) ^ 2 := by
    intro k
    have h1 := preparation_abs_eig_le hAH k
    rw [← hμ, norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg] at h1
    have h2 : |r k| ≤ (W : ℝ) ^ 3 := by
      simp only [hr, abs_div, abs_of_pos (by positivity : (0 : ℝ) < g ^ 2)]
      rw [div_le_iff₀ (by positivity)]
      calc |μ k| ≤ g ^ 2 * ‖Γ⁻¹‖ := h1
        _ ≤ g ^ 2 * (W : ℝ) ^ 3 := by gcongr; exact hR.2.1
        _ = _ := by ring
    have h3 := abs_le.mp h2
    exact sq_le_sq' h3.1 h3.2
  have hη0 : 0 < η := by rw [hη]; positivity
  rw [hI η hη0.ne'] at h1
  rw [hI (g ^ 2) (by positivity)] at h2
  have hind0 : ∀ k, 0 ≤ ind k := fun k => by simp only [hind]; split_ifs <;> norm_num
  have hind1 : ∀ k, |g ^ 2 * r k| ≤ T → ind k = 1 := fun k hk => by
    have hμr : μ k = g ^ 2 * r k := by simp only [hr]; field_simp
    have hmem : μ k ∈ Set.Icc (-T) T := by rw [hμr]; exact abs_le.mp hk
    simp only [hind, hmem, ↓reduceIte]
  obtain ⟨k1, k2⟩ := preparation_kernel hW hg hg1 hCL hη hT p r ind hp0 hrW hind0 hind1 h1 h2
  refine ⟨?_, by rw [hb, hPv]; exact k1⟩
  have hfin : ((W : ℝ) ^ (-10 : ℝ) * l2Norm (Γ⁻¹ *ᵥ u)) ^ 2 ≤
      l2Norm (specProj (((g : ℂ) ^ 2) • Γ⁻¹) (Set.Icc (-T) T) *ᵥ (Γ⁻¹ *ᵥ u)) ^ 2 := by
    rw [mul_pow, hvn, hPv]
    exact k2
  exact (pow_le_pow_iff_left₀ (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _) two_ne_zero).mp hfin

/-- The matrix inverse `X ↦ X⁻¹ = det(X)⁻¹ adj(X)` is Borel. -/
private lemma preparation_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable fun X : Matrix ι ι ℂ => X⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have h : (fun X : Matrix ι ι ℂ => X⁻¹ i j) = fun X => (X.det)⁻¹ * X.adjugate i j := by
    funext X
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [h]
  have hd : Continuous fun X : Matrix ι ι ℂ => X.det := continuous_id.matrix_det
  have ha : Continuous fun X : Matrix ι ι ℂ => X.adjugate i j :=
    (continuous_id.matrix_adjugate).matrix_elem i j
  exact hd.measurable.inv.mul ha.measurable

/-- The decreasing eigenvalue of index `j` is Borel on all matrices. -/
private lemma preparation_measurable_sortedEig (n : ℕ) (j : Fin (Fintype.card (Fin n))) :
    Measurable fun M : Matrix (Fin n) (Fin n) ℂ => sortedEig M j := by
  have hS : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | M.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have heq : (fun M : Matrix (Fin n) (Fin n) ℂ => sortedEig M j) =
      Set.piecewise {M : Matrix (Fin n) (Fin n) ℂ | M.IsHermitian}
        (fun M => sortedEig M j) (fun _ => 0) := by
    funext M
    by_cases hM : M.IsHermitian
    · rw [Set.piecewise_eq_of_mem _ _ _ hM]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hM]
      simp [sortedEig, hM]
  rw [heq]
  exact ContinuousOn.measurable_piecewise
    ((continuous_apply j).comp_continuousOn continuousOn_sortedEig)
    continuousOn_const hS.measurableSet

/-- `M ↦ #{eigenvalues of M in J}` is Borel on all matrices for measurable `J`. -/
private lemma preparation_measurable_countIn (n : ℕ) {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable fun M : Matrix (Fin n) (Fin n) ℂ => countIn M J := by
  have hS : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | M.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hsum : Measurable fun M : Matrix (Fin n) (Fin n) ℂ =>
      ∑ j, if sortedEig M j ∈ J then 1 else 0 :=
    Finset.measurable_sum _ fun j _ => Measurable.ite
      (hJ.preimage (preparation_measurable_sortedEig n j)) measurable_const measurable_const
  have heq : (fun M : Matrix (Fin n) (Fin n) ℂ => countIn M J) =
      Set.piecewise {M : Matrix (Fin n) (Fin n) ℂ | M.IsHermitian}
        (fun M => ∑ j, if sortedEig M j ∈ J then 1 else 0) (fun _ => 0) := by
    funext M
    by_cases hM : M.IsHermitian
    · rw [Set.piecewise_eq_of_mem _ _ _ hM]
      simp only [countIn, hM, ↓reduceDIte, Finset.card_filter, eigenvalues_eq_sortedEig hM]
      exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
        (fun j => if sortedEig M j ∈ J then 1 else 0)
    · rw [Set.piecewise_eq_of_notMem _ _ _ hM]
      simp [countIn, hM]
  rw [heq]
  exact hsum.piecewise hS.measurableSet measurable_const

/-- Regular states (9.3) [us:eq:regular] form a Borel set. -/
private lemma preparation_measurableSet_regular (W : ℕ) (g : ℝ) :
    MeasurableSet {R : Matrix (Fin W) (Fin W) ℂ | IsRegularState W g R} := by
  have hS : IsClosed {M : Matrix (Fin W) (Fin W) ℂ | M.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hn : MeasurableSet {R : Matrix (Fin W) (Fin W) ℂ | ‖R‖ ≤ (W : ℝ) ^ 3} :=
    measurableSet_le continuous_norm.measurable measurable_const
  have hm : Measurable fun R : Matrix (Fin W) (Fin W) ℂ => countIn (((g : ℂ) ^ 2) • R)
      {x : ℝ | g < |x|} :=
    (preparation_measurable_countIn W (measurableSet_lt measurable_const measurable_id.abs)).comp
      (measurable_id.const_smul ((g : ℂ) ^ 2))
  have hc : MeasurableSet {R : Matrix (Fin W) (Fin W) ℂ |
      (countIn (((g : ℂ) ^ 2) • R) {x : ℝ | g < |x|} : ℝ) ≤ W * Real.sqrt g} :=
    measurableSet_le ((measurable_from_top : Measurable fun m : ℕ => (m : ℝ)).comp hm)
      measurable_const
  exact hS.measurableSet.inter (hn.inter hc)

/-- Block `k` of the sample, as a `W × W` matrix, is measurable in the sample. -/
private lemma preparation_measurable_gueBlock (W q : ℕ) (k : Fin q) :
    Measurable fun ω : Ω W q => gueBlock W q ω k := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The input blocks `V_{k+1}` are measurable in the sample. -/
private lemma preparation_measurable_blockSeq (W q k : ℕ) :
    Measurable fun ω : Ω W q => blockSeq W q ω k := by
  by_cases h : k < q
  · have : (fun ω : Ω W q => blockSeq W q ω k) = fun ω => gueBlock W q ω ⟨k, h⟩ := by
      funext ω
      simp only [blockSeq, h, ↓reduceDIte]
    rw [this]
    exact preparation_measurable_gueBlock W q ⟨k, h⟩
  · have : (fun ω : Ω W q => blockSeq W q ω k) = fun _ => 0 := by
      funext ω
      simp only [blockSeq, h, ↓reduceDIte]
    rw [this]
    exact measurable_const

/-- `V ↦ T(V)` is continuous on `W × W` matrices. -/
private lemma preparation_continuous_transferMat {W : ℕ} (g : ℝ) (z : ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => transferMat g z V := by
  refine continuous_matrix fun i j => ?_
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  simp only [transferMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
    smul_eq_mul]
  fun_prop

/-- `X_1` and `Y_1` are measurable in the sample. -/
private lemma preparation_measurable_topBot {W q : ℕ} (g E : ℝ) (x : IsoFlag W) :
    Measurable (prepTop W g E q x) ∧ Measurable (prepBot W g E q x) := by
  have hb := preparation_measurable_blockSeq W q 0
  have hT := preparation_continuous_transferMat (W := W) g ((max 1 g * E / g : ℝ) : ℂ)
  have hc : Continuous fun V : Matrix (Fin W) (Fin W) ℂ =>
      transferMat g ((max 1 g * E / g : ℝ) : ℂ) V * 1 * freeConj W 0 * prepFrame x :=
    ((hT.matrix_mul continuous_const).matrix_mul continuous_const).matrix_mul continuous_const
  have hc' : ∀ i : Fin 2, Measurable fun V : Matrix (Fin W) (Fin W) ℂ => (Matrix.of fun α β =>
      (transferMat g ((max 1 g * E / g : ℝ) : ℂ) V * 1 * freeConj W 0 * prepFrame x :
        Matrix (Fin 2 × Fin W) (Fin W) ℂ) (i, α) β : Matrix (Fin W) (Fin W) ℂ) :=
    fun i => (continuous_matrix fun α β => hc.matrix_elem (i, α) β).measurable
  exact ⟨(hc' 0).comp hb, (hc' 1).comp hb⟩

/-- `R_j` is measurable in the sample. -/
private lemma preparation_measurable_R {W q : ℕ} (g E : ℝ) (x : IsoFlag W) (j : ℕ) :
    Measurable fun ω : Ω W q => prepR W g E q x ω j := by
  induction j with
  | zero => exact measurable_const
  | succ n ih =>
    cases n with
    | zero =>
      obtain ⟨hT, hB⟩ := preparation_measurable_topBot (q := q) g E x
      have hc : Continuous fun p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
          -((g : ℂ)⁻¹ • (p.1 * p.2)) := by fun_prop
      have := hc.measurable.comp (hB.prodMk (preparation_measurable_inv.comp hT))
      exact this
    | succ m =>
      have hc : Continuous fun p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
          p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2 := by fun_prop
      have := preparation_measurable_inv.comp
        (hc.measurable.comp ((preparation_measurable_blockSeq W q (m + 1)).prodMk ih))
      exact this

/-- `v_j` is measurable in the sample. -/
private lemma preparation_measurable_V {W q : ℕ} (g E : ℝ) (x : IsoFlag W) (j : ℕ) :
    Measurable fun ω : Ω W q => prepV W g E q x ω j := by
  have hc2 : Continuous fun p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) => p.1 *ᵥ p.2 :=
    continuous_fst.matrix_mulVec continuous_snd
  induction j with
  | zero => exact measurable_const
  | succ n ih =>
    cases n with
    | zero =>
      obtain ⟨hT, -⟩ := preparation_measurable_topBot (q := q) g E x
      have hc : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => Mᴴ := by fun_prop
      have := hc2.measurable.comp
        ((preparation_measurable_inv.comp (hc.measurable.comp hT)).prodMk
          (measurable_const (a := prepNormal x)))
      exact this
    | succ m =>
      have := hc2.measurable.comp ((preparation_measurable_R g E x (m + 2)).prodMk ih)
      exact this

/-- Two samples that agree off block `b` have the same input blocks `V_{k+1}` for `k < b`. -/
private lemma preparation_blockSeq_congr {W q : ℕ} {b : Fin q} {ω ω' : Ω W q}
    (h : ∀ y, y.1 ≠ b → ω y = ω' y) (k : ℕ) (hk : k < b.1) :
    blockSeq W q ω k = blockSeq W q ω' k := by
  have hkq : k < q := hk.trans b.2
  have hne : ∀ γ δ : Fin W, ((⟨k, hkq⟩ : Fin q), γ, δ).1 ≠ b := fun γ δ hkb => by
    have := congrArg Fin.val hkb
    simp only at this
    omega
  have h' : ∀ α β : Fin W, ω (⟨k, hkq⟩, α, β) = ω' (⟨k, hkq⟩, α, β) :=
    fun α β => h _ (hne α β)
  have hb : gueBlock W q ω ⟨k, hkq⟩ = gueBlock W q ω' ⟨k, hkq⟩ := by
    unfold gueBlock
    simp only [h']
  simp only [blockSeq, hkq, ↓reduceDIte]
  exact hb

/-- `R_j` and `v_j` depend only on the blocks `V_1, …, V_j`. -/
private lemma preparation_RV_congr {W q : ℕ} (g E : ℝ) (x : IsoFlag W) {ω ω' : Ω W q} {n : ℕ}
    (h : ∀ k, k < n → blockSeq W q ω k = blockSeq W q ω' k) :
    ∀ j, j ≤ n → prepR W g E q x ω j = prepR W g E q x ω' j ∧
      prepV W g E q x ω j = prepV W g E q x ω' j := by
  have htop : 0 < n → prepTop W g E q x ω = prepTop W g E q x ω' ∧
      prepBot W g E q x ω = prepBot W g E q x ω' := fun hn => by
    have h0 := h 0 hn
    constructor <;> simp only [prepTop, prepBot, transferProd, h0]
  intro j
  induction j with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ j ih =>
    intro hj
    cases j with
    | zero =>
      have := htop (by omega)
      constructor
      · change -((g : ℂ)⁻¹ • (prepBot W g E q x ω * (prepTop W g E q x ω)⁻¹)) =
          -((g : ℂ)⁻¹ • (prepBot W g E q x ω' * (prepTop W g E q x ω')⁻¹))
        rw [this.1, this.2]
      · change ((prepTop W g E q x ω)ᴴ)⁻¹ *ᵥ prepNormal x =
          ((prepTop W g E q x ω')ᴴ)⁻¹ *ᵥ prepNormal x
        rw [this.1]
    | succ m =>
      have hR : prepR W g E q x ω (m + 2) = prepR W g E q x ω' (m + 2) := by
        change (blockSeq W q ω (m + 1) - (E : ℂ) • 1 -
            ((g : ℂ) ^ 2) • prepR W g E q x ω (m + 1))⁻¹ =
          (blockSeq W q ω' (m + 1) - (E : ℂ) • 1 -
            ((g : ℂ) ^ 2) • prepR W g E q x ω' (m + 1))⁻¹
        rw [h (m + 1) (by omega), (ih (by omega)).1]
      refine ⟨hR, ?_⟩
      change prepR W g E q x ω (m + 2) *ᵥ prepV W g E q x ω (m + 1) =
        prepR W g E q x ω' (m + 2) *ᵥ prepV W g E q x ω' (m + 1)
      rw [hR, (ih (by omega)).2]

/-- If `M = V - E - g² R` is invertible with `M⁻¹` Hermitian and `V` Hermitian, then `R` is
Hermitian. -/
private lemma preparation_herm_step {W : ℕ} {g E : ℝ} (hg : 0 < g)
    {V R : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian)
    (hu : IsUnit (V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R))
    (hH : (V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R)⁻¹.IsHermitian) : R.IsHermitian := by
  have hMH : (V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R).IsHermitian := by
    have h := hH.inv
    rwa [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)] at h
  have hE : IsSelfAdjoint (E : ℂ) := by rw [isSelfAdjoint_iff]; simp
  have hk' : IsSelfAdjoint (((g : ℂ) ^ 2)⁻¹) := by rw [isSelfAdjoint_iff]; simp
  have hV' : (V - (E : ℂ) • 1).IsHermitian := hV.sub (Matrix.isHermitian_one.smul hE)
  have hgR : (((g : ℂ) ^ 2) • R).IsHermitian := by
    have := hV'.sub hMH
    rwa [sub_sub_cancel] at this
  have hg2 : ((g : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hg.ne')
  have := hgR.smul hk'
  rwa [inv_smul_smul₀ hg2] at this

/-- The class of Lemma G.1 [us:lem:local-law] grows with `ε`. -/
private lemma preparation_deformClass_mono {W : ℕ} {ε ε' : ℝ} {B : Matrix (Fin W) (Fin W) ℂ}
    (h : DeformClass ε B) (hε : ε ≤ ε') : DeformClass ε' B := by
  obtain ⟨hH, Bs, Bb, hsum, hs, hb⟩ := h
  exact ⟨hH, Bs, Bb, hsum, hs.trans hε,
    hb.trans (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _))⟩

/-- `(V - B - E - iη)⁻¹ = (Γ - iη)⁻¹` with `Γ = V - E - B`. -/
private lemma preparation_resolvent_eq {W : ℕ} (V B : Matrix (Fin W) (Fin W) ℂ) (E η : ℝ) :
    resolventMat (V - B) (E + η * Complex.I) =
      (V - (E : ℂ) • 1 - B - ((η : ℂ) * Complex.I) • 1)⁻¹ := by
  unfold resolventMat
  congr 1
  rw [add_smul]
  abel

/-- The Poisson integral `Im u*(V - g² R - E - iη)⁻¹u` at `p = (V, (R, u))`. -/
private def preparation_lawI (W : ℕ) (g E η : ℝ)
    (p : Matrix (Fin W) (Fin W) ℂ × (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ))) : ℝ :=
  (star p.2.2 ⬝ᵥ (resolventMat (p.1 - ((g : ℂ) ^ 2) • p.2.1) (E + η * Complex.I) *ᵥ p.2.2)).im

/-- The comparison quantity `u*(1 + B²)⁻¹u` with `B = g² R` at `p = (V, (R, u))`. -/
private def preparation_lawN (W : ℕ) (g : ℝ)
    (p : Matrix (Fin W) (Fin W) ℂ × (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ))) : ℝ :=
  (star p.2.2 ⬝ᵥ ((1 + (((g : ℂ) ^ 2) • p.2.1) * (((g : ℂ) ^ 2) • p.2.1))⁻¹ *ᵥ p.2.2)).re

/-- The failure of the two-sided bound of (G.2) [us:eq:relative-local-law] at `η` for the
deformation `B = g² R`, tested on `u ≠ 0`. -/
private def preparation_lawFail (W : ℕ) (g E η CL : ℝ) :
    Set (Matrix (Fin W) (Fin W) ℂ × (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ))) :=
  {p | p.2.2 ≠ 0 ∧ ¬ (CL⁻¹ * preparation_lawN W g p ≤ preparation_lawI W g E η p ∧
    preparation_lawI W g E η p ≤ CL * preparation_lawN W g p)}

/-- `(A, v) ↦ v* A v` is continuous. -/
private lemma preparation_continuous_form {W : ℕ} :
    Continuous fun p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) => star p.2 ⬝ᵥ (p.1 *ᵥ p.2) := by
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

/-- The Poisson integral is Borel in `(V, R, u)`. -/
private lemma preparation_measurable_lawI (W : ℕ) (g E η : ℝ) :
    Measurable (preparation_lawI W g E η) := by
  have hcG : Continuous fun p : Matrix (Fin W) (Fin W) ℂ ×
      (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) =>
      p.1 - ((g : ℂ) ^ 2) • p.2.1 - ((E : ℂ) + (η : ℂ) * Complex.I) • 1 := by
    fun_prop
  have hG : Measurable fun p : Matrix (Fin W) (Fin W) ℂ ×
      (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) =>
      resolventMat (p.1 - ((g : ℂ) ^ 2) • p.2.1) (E + η * Complex.I) :=
    preparation_measurable_inv.comp hcG.measurable
  have hF : Measurable fun p : Matrix (Fin W) (Fin W) ℂ ×
      (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) =>
      star p.2.2 ⬝ᵥ (resolventMat (p.1 - ((g : ℂ) ^ 2) • p.2.1) (E + η * Complex.I) *ᵥ p.2.2) :=
    preparation_continuous_form.measurable.comp (hG.prodMk measurable_snd.snd)
  unfold preparation_lawI
  exact Complex.measurable_im.comp hF

/-- The comparison quantity is Borel in `(R, u)`. -/
private lemma preparation_measurable_lawN (W : ℕ) (g : ℝ) :
    Measurable (preparation_lawN W g) := by
  have hcM : Continuous fun p : Matrix (Fin W) (Fin W) ℂ ×
      (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) =>
      1 + (((g : ℂ) ^ 2) • p.2.1) * (((g : ℂ) ^ 2) • p.2.1) := by
    fun_prop
  have hM : Measurable fun p : Matrix (Fin W) (Fin W) ℂ ×
      (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) =>
      (1 + (((g : ℂ) ^ 2) • p.2.1) * (((g : ℂ) ^ 2) • p.2.1))⁻¹ :=
    preparation_measurable_inv.comp hcM.measurable
  have hF : Measurable fun p : Matrix (Fin W) (Fin W) ℂ ×
      (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) =>
      star p.2.2 ⬝ᵥ ((1 + (((g : ℂ) ^ 2) • p.2.1) * (((g : ℂ) ^ 2) • p.2.1))⁻¹ *ᵥ p.2.2) :=
    preparation_continuous_form.measurable.comp (hM.prodMk measurable_snd.snd)
  unfold preparation_lawN
  exact Complex.measurable_re.comp hF

/-- The failure set of the two-sided bound is Borel. -/
private lemma preparation_measurableSet_lawFail (W : ℕ) (g E η CL : ℝ) :
    MeasurableSet (preparation_lawFail W g E η CL) := by
  have hI := preparation_measurable_lawI W g E η
  have hN := preparation_measurable_lawN W g
  have h0 : MeasurableSet {p : Matrix (Fin W) (Fin W) ℂ ×
      (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ)) | p.2.2 ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage measurable_snd.snd
  have h12 := (measurableSet_le ((measurable_const (a := CL⁻¹)).mul hN) hI).inter
    (measurableSet_le hI ((measurable_const (a := CL)).mul hN))
  exact h0.inter h12.compl

/-- The relative local law (G.2) [us:eq:relative-local-law] on the fresh block `a`: if, for every
regular state `R` and every `v ≠ 0`, the two-sided bound at `η` fails with probability at most
`b`, then it fails at `(V_a, R, u)` with `R`, `u` fixed before block `a` with probability at most
`b`, on the set where `R` is regular. -/
private lemma preparation_fresh_law {W q : ℕ} (a : Fin q) {Rp : Ω W q → Matrix (Fin W) (Fin W) ℂ}
    {u : Ω W q → Fin W → ℂ} (hRm : Measurable Rp) (hum : Measurable u)
    (hRa : OffBlock W q a Rp) (hua : OffBlock W q a u) {g E η CL b : ℝ}
    (hlaw : ∀ (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ), IsRegularState W g R → v ≠ 0 →
      μ W 1 {ω' | (gueMat W ω', (R, v)) ∈ preparation_lawFail W g E η CL} ≤ ENNReal.ofReal b) :
    μ W q {ω | ω ∈ {ω | IsRegularState W g (Rp ω)} ∧
      (gueBlock W q ω a, (Rp ω, u ω)) ∈ preparation_lawFail W g E η CL} ≤ ENNReal.ofReal b := by
  have hS : MeasurableSet {ω : Ω W q | IsRegularState W g (Rp ω)} :=
    hRm (preparation_measurableSet_regular W g)
  have hSa : OffBlock W q a (· ∈ {ω : Ω W q | IsRegularState W g (Rp ω)}) := fun ω ω' h => by
    change IsRegularState W g (Rp ω) = IsRegularState W g (Rp ω')
    rw [hRa ω ω' h]
  have hDa : OffBlock W q a (fun ω => (Rp ω, u ω)) := fun ω ω' h => by
    simp only [hRa ω ω' h, hua ω ω' h]
  have h := measure_gueBlock_fresh_le W q a (hRm.prodMk hum) hDa hS hSa
    (preparation_measurableSet_lawFail W g E η CL) (b := ENNReal.ofReal b) (fun ω hω => by
      by_cases hv : u ω = 0
      · have e : {ω' : Ω W 1 | (gueMat W ω', (Rp ω, u ω)) ∈ preparation_lawFail W g E η CL} =
            ∅ := by
          ext ω'
          simp [preparation_lawFail, hv]
        rw [e, measure_empty]
        exact bot_le
      · exact hlaw (Rp ω) (u ω) hω hv)
  refine h.trans ?_
  calc ENNReal.ofReal b * μ W q {ω | IsRegularState W g (Rp ω)} ≤ ENNReal.ofReal b * 1 := by
        gcongr
        exact prob_le_one
    _ = _ := mul_one _

/-- The good event of the proof of Lemma 9.1 [su:lem:preparation], regime (i), gives the prepared
estimates: on `PrepOK`, if `R_4 = (V_4 - E - g² R_3)⁻¹` is regular, satisfies the count of
(9.6) [su:eq:prepared-large-rank], and the two-sided bound of (G.2)
[us:eq:relative-local-law] holds at `η = g²/(4C²)` and `η = g²` for `B = g² R_3` and `u = v_3`,
then `(R_4, v_4) ∈ PrepGoodWeak`. -/
private lemma preparation_good {W q : ℕ} (hW : 2 ≤ W) {g E ε CL C : ℝ} (hg : 0 < g)
    (hg1 : g ≤ 1) (hCL : 1 ≤ CL) (hC : 2 ≤ C) (hT : 4 * CL ^ 2 ≤ (W : ℝ) ^ (ε / 800))
    (x : IsoFlag W) {ω : Ω W q} (a : Fin q) (hb : blockSeq W q ω 3 = gueBlock W q ω a)
    (hP : PrepOK W g E q x ω)
    (hreg : IsRegularState W g
      (gueBlock W q ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • prepR W g E q x ω 3)⁻¹)
    (hcount : (countIn (((g : ℂ) ^ 2) •
      (gueBlock W q ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • prepR W g E q x ω 3)⁻¹)
        {y | (W : ℝ) ^ (-(ε / 800)) < |y|} : ℝ) ≤ W * g ^ 2 * (W : ℝ) ^ (ε / 400))
    (hl1 : (gueBlock W q ω a, (prepR W g E q x ω 3, prepV W g E q x ω 3)) ∉
      preparation_lawFail W g E (g ^ 2 / (4 * CL ^ 2)) CL)
    (hl2 : (gueBlock W q ω a, (prepR W g E q x ω 3, prepV W g E q x ω 3)) ∉
      preparation_lawFail W g E (g ^ 2) CL) :
    PrepOK W g E q x ω ∧ (prepR W g E q x ω 4, prepV W g E q x ω 4) ∈ PrepGoodWeak W g ε C := by
  set Γ := gueBlock W q ω a - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • prepR W g E q x ω 3 with hΓdef
  set u := prepV W g E q x ω 3 with hudef
  have hR4 : prepR W g E q x ω 4 = Γ⁻¹ := by
    change (blockSeq W q ω 3 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • prepR W g E q x ω 3)⁻¹ = _
    rw [hb]
  have hV4 : prepV W g E q x ω 4 = Γ⁻¹ *ᵥ u := by
    change prepR W g E q x ω 4 *ᵥ prepV W g E q x ω 3 = _
    rw [hR4]
  have hΓ : IsUnit Γ := by
    have := hP.2 3 (by norm_num) le_rfl
    rwa [hb] at this
  refine ⟨hP, ?_⟩
  rw [hR4, hV4]
  -- the two Poisson integrals
  obtain ⟨N, h1, h2⟩ : ∃ N : ℝ,
      (star u ⬝ᵥ ((Γ - (((g ^ 2 / (4 * CL ^ 2) : ℝ) : ℂ) * Complex.I) • 1)⁻¹ *ᵥ u)).im ≤
        CL * N ∧
      CL⁻¹ * N ≤ (star u ⬝ᵥ ((Γ - (((g ^ 2 : ℝ) : ℂ) * Complex.I) • 1)⁻¹ *ᵥ u)).im := by
    by_cases hu0 : u = 0
    · refine ⟨0, ?_, ?_⟩ <;> simp [hu0]
    · refine ⟨preparation_lawN W g (gueBlock W q ω a, (prepR W g E q x ω 3, u)), ?_, ?_⟩
      · have hc : CL⁻¹ * preparation_lawN W g (gueBlock W q ω a, (prepR W g E q x ω 3, u)) ≤
            preparation_lawI W g E (g ^ 2 / (4 * CL ^ 2))
              (gueBlock W q ω a, (prepR W g E q x ω 3, u)) ∧
            preparation_lawI W g E (g ^ 2 / (4 * CL ^ 2))
              (gueBlock W q ω a, (prepR W g E q x ω 3, u)) ≤
            CL * preparation_lawN W g (gueBlock W q ω a, (prepR W g E q x ω 3, u)) := by
          by_contra hc
          exact hl1 ⟨hu0, hc⟩
        have h := hc.2
        unfold preparation_lawI at h
        rwa [preparation_resolvent_eq] at h
      · have hc : CL⁻¹ * preparation_lawN W g (gueBlock W q ω a, (prepR W g E q x ω 3, u)) ≤
            preparation_lawI W g E (g ^ 2) (gueBlock W q ω a, (prepR W g E q x ω 3, u)) ∧
            preparation_lawI W g E (g ^ 2) (gueBlock W q ω a, (prepR W g E q x ω 3, u)) ≤
            CL * preparation_lawN W g (gueBlock W q ω a, (prepR W g E q x ω 3, u)) := by
          by_contra hc
          exact hl2 ⟨hu0, hc⟩
        have h := hc.1
        unfold preparation_lawI at h
        rwa [preparation_resolvent_eq] at h
  obtain ⟨c1, c2⟩ := preparation_core hW hg hg1 hCL rfl hT hΓ hreg u N h1 h2
  refine ⟨hreg, c1, c2.trans ?_, hcount⟩
  gcongr

/-- Lemma 9.1 [su:lem:preparation] in regime (i), (9.5) [su:eq:prep] and (9.6)
[su:eq:prepared-large-rank]: for `0 < α < β < 1/2` and `ε > 0` there are `C, W₀` such that for
`W ≥ W₀`, `q ≥ 4`, `a ∈ [α, β]`, `|E| ≤ 2 - κ₀` and every flag, with `g = W^{-a}`, the four
preparation steps enter the chart and `(R_4, v_4) ∈ PrepGoodWeak` except with probability
`C (W^{-2} + W^{-α/2} + W^{-ε/800})`. -/
theorem preparation_weak (κ₀ α β ε : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hα : 0 < α)
    (hαβ : α < β) (hβ : β < 1 / 2) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℕ, ∀ W q : ℕ, W₀ ≤ W → 4 ≤ q →
      ∀ (a E : ℝ) (x : IsoFlag W), α ≤ a → a ≤ β → |E| ≤ 2 - κ₀ →
        μ W q {ω | ¬ (PrepOK W ((W : ℝ) ^ (-a)) E q x ω ∧
            (prepR W ((W : ℝ) ^ (-a)) E q x ω 4, prepV W ((W : ℝ) ^ (-a)) E q x ω 4) ∈
              PrepGoodWeak W ((W : ℝ) ^ (-a)) ε C)} ≤
          ENNReal.ofReal (C * ((W : ℝ) ^ (-2 : ℝ) + (W : ℝ) ^ (-α / 2) +
            (W : ℝ) ^ (-(ε / 800)))) := by
  obtain ⟨C₂, hC₂, h₂⟩ := fresh_inv_count_tail
  obtain ⟨C₃, hC₃, h₃⟩ := fresh_regular
  obtain ⟨ε₀, CL, hε₀, hCL, hLL⟩ := localLaw_rel κ₀ 1 hκ₀ hκ₀' one_pos
  have hδ : 0 < 1 / 2 - β := by linarith
  obtain ⟨n₀, hn₀⟩ := hLL ε₀ (1 / 2 - β) 1 2 hε₀ le_rfl hδ one_pos two_pos
  have ev3 : ∀ᶠ W : ℕ in Filter.atTop, 4 * CL ^ 2 ≤ (W : ℝ) ^ (ε / 800) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 800)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have ev4 : ∀ᶠ W : ℕ in Filter.atTop, 4 * CL ^ 2 ≤ (W : ℝ) ^ (1 / 2 - β) :=
    ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have ev5 : ∀ᶠ W : ℕ in Filter.atTop, (W : ℝ) ^ (-(α / 2)) ≤ ε₀ :=
    ((tendsto_rpow_neg_atTop (by positivity : 0 < α / 2)).comp
      tendsto_natCast_atTop_atTop).eventually (ge_mem_nhds hε₀)
  obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.mp
    ((Filter.eventually_ge_atTop (max n₀ 2)).and (ev3.and (ev4.and ev5)))
  refine ⟨2 * C₃ + 2 * C₂ + 2, by positivity, W₀, fun W q hW hq a E x haα haβ hE => ?_⟩
  obtain ⟨hWm, hWT, hWβ, hWε₀⟩ := hW₀ W hW
  have hWn₀ : n₀ ≤ W := le_of_max_le_left hWm
  have hW2 : 2 ≤ W := le_of_max_le_right hWm
  have : NeZero W := ⟨by omega⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hW0 : (0 : ℝ) < W := by linarith
  set g : ℝ := (W : ℝ) ^ (-a) with hgdef
  have hg : 0 < g := Real.rpow_pos_of_pos hW0 _
  have hg1 : g ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hsq : Real.sqrt g ≤ (W : ℝ) ^ (-α / 2) := by
    rw [Real.sqrt_eq_rpow, hgdef, ← Real.rpow_mul hW0.le]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hsε : Real.sqrt g ≤ ε₀ := hsq.trans (by rw [neg_div]; exact hWε₀)
  -- the two scales of the local law
  have hg2 : (W : ℝ) ^ (-1 + (1 / 2 - β)) * (4 * CL ^ 2) ≤ g ^ 2 := by
    calc (W : ℝ) ^ (-1 + (1 / 2 - β)) * (4 * CL ^ 2)
        ≤ (W : ℝ) ^ (-1 + (1 / 2 - β)) * (W : ℝ) ^ (1 / 2 - β) := by gcongr
      _ = (W : ℝ) ^ (-a + -a + 2 * (a - β)) := by
          rw [← Real.rpow_add hW0]; congr 1; ring
      _ ≤ (W : ℝ) ^ (-a + -a) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      _ = g ^ 2 := by rw [Real.rpow_add hW0, sq]
  have hg21 : g ^ 2 ≤ 1 := pow_le_one₀ hg.le hg1
  have hCL4 : (1 : ℝ) ≤ 4 * CL ^ 2 := by nlinarith
  have hη1 : (W : ℝ) ^ (-1 + (1 / 2 - β)) ≤ g ^ 2 / (4 * CL ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; exact hg2
  have hη1' : g ^ 2 / (4 * CL ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hη2 : (W : ℝ) ^ (-1 + (1 / 2 - β)) ≤ g ^ 2 :=
    hη1.trans (div_le_self (by positivity) hCL4)
  -- the blocks and the states fixed before them
  have hq3 : 3 < q := by omega
  have hq2 : 2 < q := by omega
  obtain ⟨a3, ha3⟩ : ∃ b : Fin q, b = ⟨3, hq3⟩ := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ b : Fin q, b = ⟨2, hq2⟩ := ⟨_, rfl⟩
  have hb3 : ∀ ω, blockSeq W q ω 3 = gueBlock W q ω a3 := fun ω => by
    simp only [blockSeq, hq3, ↓reduceDIte, ha3]
  have hb2 : ∀ ω, blockSeq W q ω 2 = gueBlock W q ω a2 := fun ω => by
    simp only [blockSeq, hq2, ↓reduceDIte, ha2]
  set Rp2 : Ω W q → Matrix (Fin W) (Fin W) ℂ := fun ω =>
    if (prepR W g E q x ω 2).IsHermitian then prepR W g E q x ω 2 else 0 with hRp2
  set Rp3 : Ω W q → Matrix (Fin W) (Fin W) ℂ := fun ω =>
    if (prepR W g E q x ω 3).IsHermitian then prepR W g E q x ω 3 else 0 with hRp3
  set u : Ω W q → Fin W → ℂ := fun ω => prepV W g E q x ω 3 with hu
  have hHm : ∀ j, MeasurableSet {ω : Ω W q | (prepR W g E q x ω j).IsHermitian} := fun j =>
    (preparation_measurable_R g E x j)
      (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  have hRp2m : Measurable Rp2 :=
    Measurable.ite (hHm 2) (preparation_measurable_R g E x 2) measurable_const
  have hRp3m : Measurable Rp3 :=
    Measurable.ite (hHm 3) (preparation_measurable_R g E x 3) measurable_const
  have hum : Measurable u := preparation_measurable_V g E x 3
  have hRp2h : ∀ ω, (Rp2 ω).IsHermitian := fun ω => by
    by_cases h : (prepR W g E q x ω 2).IsHermitian
    · simp [hRp2, h]
    · simp [hRp2, h]
  have hRp3h : ∀ ω, (Rp3 ω).IsHermitian := fun ω => by
    by_cases h : (prepR W g E q x ω 3).IsHermitian
    · simp [hRp3, h]
    · simp [hRp3, h]
  have hRp2a : OffBlock W q a2 Rp2 := fun ω ω' h => by
    have := (preparation_RV_congr g E x (n := 2)
      (fun k hk => preparation_blockSeq_congr h k (by rw [ha2]; exact hk)) 2 le_rfl).1
    simp only [hRp2, this]
  have hRp3a : OffBlock W q a3 Rp3 := fun ω ω' h => by
    have := (preparation_RV_congr g E x (n := 3)
      (fun k hk => preparation_blockSeq_congr h k (by rw [ha3]; exact hk)) 3 le_rfl).1
    simp only [hRp3, this]
  have hua : OffBlock W q a3 u := fun ω ω' h =>
    (preparation_RV_congr g E x (n := 3)
      (fun k hk => preparation_blockSeq_congr h k (by rw [ha3]; exact hk)) 3 le_rfl).2
  -- the one-block bounds (9.58) [us:eq:wegner] at blocks 2 and 3
  have hF1 := h₃ W q a2 Rp2 Set.univ (by omega) hRp2m hRp2h hRp2a MeasurableSet.univ
    (fun _ _ _ => rfl) g E hg
  have hF2 := h₃ W q a3 Rp3 Set.univ (by omega) hRp3m hRp3h hRp3a MeasurableSet.univ
    (fun _ _ _ => rfl) g E hg
  have hF3 := h₂ W q a3 Rp3 Set.univ (by omega) hRp3m hRp3h hRp3a MeasurableSet.univ
    (fun _ _ _ => rfl) g E ((W : ℝ) ^ (-(ε / 800))) (W * g ^ 2 * (W : ℝ) ^ (ε / 400))
    (by positivity) (by positivity)
  rw [measure_univ, mul_one] at hF1 hF2 hF3
  have e3 : 2 * C₂ * W * g ^ 2 / ((W : ℝ) ^ (-(ε / 800)) * (W * g ^ 2 * (W : ℝ) ^ (ε / 400))) =
      2 * C₂ * (W : ℝ) ^ (-(ε / 800)) := by
    have hp : (W : ℝ) ^ (-(ε / 800)) * (W : ℝ) ^ (-(ε / 800)) * (W : ℝ) ^ (ε / 400) = 1 := by
      rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
      rw [show -(ε / 800) + -(ε / 800) + ε / 400 = 0 by ring, Real.rpow_zero]
    rw [div_eq_iff (by positivity)]
    calc 2 * C₂ * W * g ^ 2 = 2 * C₂ * W * g ^ 2 * 1 := (mul_one _).symm
      _ = _ := by rw [← hp]; ring
  rw [e3] at hF3
  -- the relative local law (G.2) [us:eq:relative-local-law] at `η = g²/(4C²)` and `η = g²`
  have hlaw : ∀ η : ℝ, (W : ℝ) ^ (-1 + (1 / 2 - β)) ≤ η → η ≤ 1 →
      μ W q {ω | ω ∈ {ω | IsRegularState W g (Rp3 ω)} ∧
        (gueBlock W q ω a3, (Rp3 ω, u ω)) ∈ preparation_lawFail W g E η CL} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-2 : ℝ)) := by
    intro η hηl hηu
    refine preparation_fresh_law a3 hRp3m hum hRp3a hua fun R v hR hv => ?_
    refine (measure_mono ?_).trans (hn₀ W hWn₀ (((g : ℂ) ^ 2) • R) E η
      (preparation_deformClass_mono (hR.deformClass hg hg1) hsε) hE hηl hηu v hv)
    intro ω' hω'
    obtain ⟨-, hω'⟩ := hω'
    exact fun hc => hω' ⟨hc.2.1, hc.2.2⟩
  have hL1 := hlaw (g ^ 2 / (4 * CL ^ 2)) hη1 hη1'
  have hL2 := hlaw (g ^ 2) hη2 hg21
  have hA := ae_prepOK (E := E) hg hg1 hq x
  -- the failure set is covered by the six failure events
  have hsub : {ω : Ω W q | ¬ (PrepOK W g E q x ω ∧
      (prepR W g E q x ω 4, prepV W g E q x ω 4) ∈ PrepGoodWeak W g ε
        (2 * C₃ + 2 * C₂ + 2))} ⊆
      (((({ω | ¬ PrepOK W g E q x ω} ∪
        {ω | ω ∈ Set.univ ∧ ¬ IsRegularState W g
          (gueBlock W q ω a2 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp2 ω)⁻¹}) ∪
        {ω | ω ∈ Set.univ ∧ ¬ IsRegularState W g
          (gueBlock W q ω a3 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp3 ω)⁻¹}) ∪
        {ω | ω ∈ Set.univ ∧ W * g ^ 2 * (W : ℝ) ^ (ε / 400) < (countIn (((g : ℂ) ^ 2) •
          (gueBlock W q ω a3 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp3 ω)⁻¹)
            {x | (W : ℝ) ^ (-(ε / 800)) < |x|} : ℝ)}) ∪
        {ω | ω ∈ {ω | IsRegularState W g (Rp3 ω)} ∧
          (gueBlock W q ω a3, (Rp3 ω, u ω)) ∈
            preparation_lawFail W g E (g ^ 2 / (4 * CL ^ 2)) CL}) ∪
        {ω | ω ∈ {ω | IsRegularState W g (Rp3 ω)} ∧
          (gueBlock W q ω a3, (Rp3 ω, u ω)) ∈ preparation_lawFail W g E (g ^ 2) CL} := by
    intro ω hω
    by_contra hn
    simp only [Set.mem_union, not_or] at hn
    obtain ⟨⟨⟨⟨⟨n0, n1⟩, n2⟩, n3⟩, n4⟩, n5⟩ := hn
    have hP : PrepOK W g E q x ω := by simpa using n0
    have hH4 : (prepR W g E q x ω 4).IsHermitian := (isPrepChart_of_prepOK hg hg1 x hP).1
    have hV3 : (blockSeq W q ω 3).IsHermitian := by rw [hb3]; exact gueBlock_isHermitian W q ω _
    have hV2 : (blockSeq W q ω 2).IsHermitian := by rw [hb2]; exact gueBlock_isHermitian W q ω _
    have hH3 : (prepR W g E q x ω 3).IsHermitian :=
      preparation_herm_step hg hV3 (hP.2 3 (by norm_num) le_rfl) hH4
    have hH2 : (prepR W g E q x ω 2).IsHermitian :=
      preparation_herm_step hg hV2 (hP.2 2 (by norm_num) (by norm_num)) hH3
    have e3' : Rp3 ω = prepR W g E q x ω 3 := by simp [hRp3, hH3]
    have e2' : Rp2 ω = prepR W g E q x ω 2 := by simp [hRp2, hH2]
    have hR3 : IsRegularState W g (Rp3 ω) := by
      have h := n1
      simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, not_not] at h
      rw [e2', ← hb2] at h
      rw [e3']
      exact h
    have hS : ω ∈ {ω | IsRegularState W g (Rp3 ω)} := hR3
    have hreg : IsRegularState W g
        (gueBlock W q ω a3 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • prepR W g E q x ω 3)⁻¹ := by
      have h := n2
      simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, not_not] at h
      rwa [e3'] at h
    have hcount : (countIn (((g : ℂ) ^ 2) •
        (gueBlock W q ω a3 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • prepR W g E q x ω 3)⁻¹)
          {y | (W : ℝ) ^ (-(ε / 800)) < |y|} : ℝ) ≤ W * g ^ 2 * (W : ℝ) ^ (ε / 400) := by
      have h := n3
      simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, not_lt] at h
      rwa [e3'] at h
    have hl1 : (gueBlock W q ω a3, (prepR W g E q x ω 3, prepV W g E q x ω 3)) ∉
        preparation_lawFail W g E (g ^ 2 / (4 * CL ^ 2)) CL := fun h => by
      rw [← e3'] at h
      exact n4 ⟨hS, h⟩
    have hl2 : (gueBlock W q ω a3, (prepR W g E q x ω 3, prepV W g E q x ω 3)) ∉
        preparation_lawFail W g E (g ^ 2) CL := fun h => by
      rw [← e3'] at h
      exact n5 ⟨hS, h⟩
    exact hω (preparation_good hW2 hg hg1 hCL (by linarith) hWT x a3 (hb3 ω) hP hreg hcount
      hl1 hl2)
  -- summing the failure probabilities
  have hx : (0 : ℝ) ≤ (W : ℝ) ^ (-2 : ℝ) := by positivity
  have hy : (0 : ℝ) ≤ (W : ℝ) ^ (-α / 2) := by positivity
  have hz : (0 : ℝ) ≤ (W : ℝ) ^ (-(ε / 800)) := by positivity
  have hsg : 0 ≤ Real.sqrt g := Real.sqrt_nonneg _
  calc μ W q _ ≤ μ W q _ := measure_mono hsub
    _ ≤ μ W q {ω | ¬ PrepOK W g E q x ω} + _ + _ + _ + _ + _ :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add
          ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add
            (measure_union_le _ _) le_rfl)) le_rfl)) le_rfl)) le_rfl)
    _ ≤ 0 + ENNReal.ofReal (C₃ * ((W : ℝ) ^ (-2 : ℝ) + Real.sqrt g)) +
        ENNReal.ofReal (C₃ * ((W : ℝ) ^ (-2 : ℝ) + Real.sqrt g)) +
        ENNReal.ofReal (2 * C₂ * (W : ℝ) ^ (-(ε / 800))) +
        ENNReal.ofReal ((W : ℝ) ^ (-2 : ℝ)) + ENNReal.ofReal ((W : ℝ) ^ (-2 : ℝ)) := by
        rw [hA]
        gcongr
    _ = ENNReal.ofReal (2 * (C₃ * ((W : ℝ) ^ (-2 : ℝ) + Real.sqrt g)) +
        2 * C₂ * (W : ℝ) ^ (-(ε / 800)) + 2 * (W : ℝ) ^ (-2 : ℝ)) := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [mul_nonneg hC₃.le (sub_nonneg.2 hsq), mul_nonneg hC₃.le hz,
          mul_nonneg hC₂.le hx, mul_nonneg hC₂.le hy, mul_nonneg hC₃.le hy]

end LSBA
