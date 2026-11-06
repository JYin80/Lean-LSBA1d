import LSBA.Upper.LargeContract
import LSBA.Transfer.Transition
import LSBA.Gauss.GUENormMoment

/-!
# The mean increment

(11.12) [lg:eq:c2]: `|P_g c − h²g⁻²[1/(2W) + Re f₁ + Re(m₁f₁) − Re f₁²/(2W)]| ≤ K/g⁴` for every `W ≥
1`, `g ≥ 1` and state, with `K` depending only on `E₀`; the remainder is bounded on all Hermitian
blocks, without the cutoff of (11.14) [uvg:eq:tail].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The real part of the quadratic form `v* M v`. -/
private def li_phi {W : ℕ} (v : EuclideanSpace ℂ (Fin W)) (M : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  (vecForm M v).re

private theorem li_vecForm_add {W : ℕ} (v : EuclideanSpace ℂ (Fin W))
    (M N : Matrix (Fin W) (Fin W) ℂ) : vecForm (M + N) v = vecForm M v + vecForm N v := by
  unfold vecForm
  rw [map_add, LinearMap.add_apply, inner_add_right]

private theorem li_vecForm_smul {W : ℕ} (v : EuclideanSpace ℂ (Fin W)) (c : ℂ)
    (M : Matrix (Fin W) (Fin W) ℂ) : vecForm (c • M) v = c * vecForm M v := by
  unfold vecForm
  rw [map_smul, LinearMap.smul_apply, inner_smul_right]

private theorem li_phi_add {W : ℕ} (v : EuclideanSpace ℂ (Fin W))
    (M N : Matrix (Fin W) (Fin W) ℂ) : li_phi v (M + N) = li_phi v M + li_phi v N := by
  unfold li_phi
  rw [li_vecForm_add, Complex.add_re]

private theorem li_phi_neg {W : ℕ} (v : EuclideanSpace ℂ (Fin W))
    (M : Matrix (Fin W) (Fin W) ℂ) : li_phi v (-M) = - li_phi v M := by
  have : -M = (-1 : ℂ) • M := by simp
  unfold li_phi
  rw [this, li_vecForm_smul]
  simp

private theorem li_phi_sub {W : ℕ} (v : EuclideanSpace ℂ (Fin W))
    (M N : Matrix (Fin W) (Fin W) ℂ) : li_phi v (M - N) = li_phi v M - li_phi v N := by
  rw [sub_eq_add_neg, li_phi_add, li_phi_neg, sub_eq_add_neg]

private theorem li_phi_smul {W : ℕ} (v : EuclideanSpace ℂ (Fin W)) (r : ℝ)
    (M : Matrix (Fin W) (Fin W) ℂ) : li_phi v ((r : ℂ) • M) = r * li_phi v M := by
  unfold li_phi
  rw [li_vecForm_smul, Complex.re_ofReal_mul]

private theorem li_phi_one {W : ℕ} {v : EuclideanSpace ℂ (Fin W)} (hv : ‖v‖ = 1) :
    li_phi v 1 = 1 := by
  unfold li_phi vecForm
  rw [show Matrix.toEuclideanLin (1 : Matrix (Fin W) (Fin W) ℂ) v = v by simp,
    inner_self_eq_norm_sq_to_K, hv]
  simp

private theorem li_norm_lin_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : ‖Matrix.toEuclideanLin A v‖ ≤ ‖A‖ * ‖v‖ :=
  (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) A).le_opNorm v

private theorem li_abs_phi_le {W : ℕ} {v : EuclideanSpace ℂ (Fin W)} (hv : ‖v‖ = 1)
    (M : Matrix (Fin W) (Fin W) ℂ) : |li_phi v M| ≤ ‖M‖ := by
  unfold li_phi vecForm
  calc |(inner ℂ v (Matrix.toEuclideanLin M v)).re|
      ≤ ‖inner ℂ v (Matrix.toEuclideanLin M v)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖v‖ * ‖Matrix.toEuclideanLin M v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖M‖ * ‖v‖) := by gcongr; exact li_norm_lin_le M v
    _ = ‖M‖ := by rw [hv]; ring


/-- The Gram matrix `F* F` of `F = I - i t V (I + C)` is `I + t A + t² B` (proof of (11.12)
[lg:eq:c2]). -/
private theorem li_gram (t : ℝ) {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (hV : V.IsHermitian) :
    (1 - (Complex.I * (t : ℂ)) • (V * (1 + C)))ᴴ * (1 - (Complex.I * (t : ℂ)) • (V * (1 + C))) =
      1 + (t : ℂ) • quadA C V + ((t ^ 2 : ℝ) : ℂ) • quadB C V := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, hV.eq]
  have h1 : star (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ)) := by simp
  rw [h1]
  unfold quadA quadB
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, pow_two, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    smul_mul_assoc, mul_smul_comm, neg_mul, smul_add, smul_sub, smul_smul, neg_smul, sub_neg_eq_add,
    Matrix.mul_assoc]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq]


private theorem li_quadA_neg {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) :
    quadA C (-V) = -quadA C V := by
  unfold quadA
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_sub_neg]
  rw [← neg_sub, smul_neg, ← neg_smul]

private theorem li_quadB_neg {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) :
    quadB C (-V) = quadB C V := by
  unfold quadB
  rw [neg_sq]

private theorem li_norm_le_one {W : ℕ} {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) : ‖C‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial (Matrix (Fin W) (Fin W) ℂ) with hs | hn
  · rw [Subsingleton.elim C 0, norm_zero]
    exact zero_le_one
  · exact (CStarRing.norm_of_mem_unitary hC).le

private theorem li_norm_one_add_le {W : ℕ} {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) : ‖1 + C‖ ≤ 2 := by
  calc ‖1 + C‖ ≤ ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ + ‖C‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (li_norm_le_one (one_mem _)) (li_norm_le_one hC)
    _ = 2 := by norm_num

private theorem li_norm_quadA_le {W : ℕ} {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (V : Matrix (Fin W) (Fin W) ℂ) :
    ‖quadA C V‖ ≤ 2 * ‖V‖ := by
  have h1 := li_norm_le_one hC
  have h2 : ‖Cᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact h1
  unfold quadA
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  calc ‖V * C - Cᴴ * V‖ ≤ ‖V * C‖ + ‖Cᴴ * V‖ := norm_sub_le _ _
    _ ≤ ‖V‖ * ‖C‖ + ‖Cᴴ‖ * ‖V‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖V‖ * 1 + 1 * ‖V‖ := by gcongr
    _ = 2 * ‖V‖ := by ring

private theorem li_norm_quadB_le {W : ℕ} {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (V : Matrix (Fin W) (Fin W) ℂ) :
    ‖quadB C V‖ ≤ 4 * ‖V‖ ^ 2 := by
  have h1 := li_norm_one_add_le hC
  have h2 : ‖1 + Cᴴ‖ ≤ 2 := by
    rw [show (1 + Cᴴ) = (1 + C)ᴴ by simp, Matrix.l2_opNorm_conjTranspose]; exact h1
  unfold quadB
  calc ‖(1 + Cᴴ) * V ^ 2 * (1 + C)‖ ≤ ‖(1 + Cᴴ) * V ^ 2‖ * ‖1 + C‖ := norm_mul_le _ _
    _ ≤ (‖1 + Cᴴ‖ * ‖V ^ 2‖) * ‖1 + C‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ (2 * ‖V‖ ^ 2) * 2 := by
        gcongr
        exact norm_pow_le' V (by norm_num)
    _ = 4 * ‖V‖ ^ 2 := by ring

/-- `A` is Hermitian, so `v* A v` is real. -/
private theorem li_quadA_herm {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (hV : V.IsHermitian) :
    (quadA C V).IsHermitian := by
  unfold quadA Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hV.eq]
  simp only [star_neg, Complex.star_def, Complex.conj_I]
  rw [neg_neg, ← neg_sub, smul_neg, ← neg_smul]


/-- Fourth-order expansion of `K` from `(1 + y + w) K = 1`, with the exact remainder. -/
private theorem li_neumann {R : Type*} [Ring R] (y w K : R) (h : (1 + (y + w)) * K = 1) :
    K = (1 - y + (y * y - w) + (y * w + w * y - y * y * y)) +
      ((y + w) ^ 4 * K + w * w - ((y + w) ^ 3 - y ^ 3)) := by
  have h1 : (y + w) * K = 1 - K := by
    rw [add_mul, one_mul] at h
    exact eq_sub_of_add_eq' h
  have h2 : (y + w) ^ 2 * K = (y + w) - 1 + K := by
    calc (y + w) ^ 2 * K = (y + w) * ((y + w) * K) := by noncomm_ring
      _ = (y + w) * (1 - K) := by rw [h1]
      _ = (y + w) - (y + w) * K := by noncomm_ring
      _ = (y + w) - (1 - K) := by rw [h1]
      _ = (y + w) - 1 + K := by abel
  have h3 : (y + w) ^ 3 * K = (y + w) ^ 2 - (y + w) + 1 - K := by
    calc (y + w) ^ 3 * K = (y + w) * ((y + w) ^ 2 * K) := by noncomm_ring
      _ = (y + w) * ((y + w) - 1 + K) := by rw [h2]
      _ = (y + w) ^ 2 - (y + w) + (y + w) * K := by noncomm_ring
      _ = (y + w) ^ 2 - (y + w) + (1 - K) := by rw [h1]
      _ = (y + w) ^ 2 - (y + w) + 1 - K := by abel
  have h4 : (y + w) ^ 4 * K = (y + w) ^ 3 - (y + w) ^ 2 + (y + w) - 1 + K := by
    calc (y + w) ^ 4 * K = (y + w) * ((y + w) ^ 3 * K) := by noncomm_ring
      _ = (y + w) * ((y + w) ^ 2 - (y + w) + 1 - K) := by rw [h3]
      _ = (y + w) ^ 3 - (y + w) ^ 2 + (y + w) - (y + w) * K := by noncomm_ring
      _ = (y + w) ^ 3 - (y + w) ^ 2 + (y + w) - (1 - K) := by rw [h1]
      _ = (y + w) ^ 3 - (y + w) ^ 2 + (y + w) - 1 + K := by abel
  rw [h4]
  noncomm_ring

/-- Norm of the remainder in `li_neumann` for `x ≤ 1`. -/
private theorem li_rem_norm {R : Type*} [NormedRing R] (y w K : R) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (hy : ‖y‖ ≤ 2 * x) (hw : ‖w‖ ≤ 4 * x ^ 2) (hK : ‖K‖ ≤ 9) :
    ‖(y + w) ^ 4 * K + w * w - ((y + w) ^ 3 - y ^ 3)‖ ≤ 12000 * x ^ 4 := by
  have hx2 : x ^ 2 ≤ x := by nlinarith
  have hz : ‖y + w‖ ≤ 6 * x := by
    calc ‖y + w‖ ≤ ‖y‖ + ‖w‖ := norm_add_le _ _
      _ ≤ 2 * x + 4 * x ^ 2 := add_le_add hy hw
      _ ≤ 6 * x := by nlinarith
  have hz0 : 0 ≤ ‖y + w‖ := norm_nonneg _
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have e1 : ‖(y + w) ^ 4 * K‖ ≤ (6 * x) ^ 4 * 9 := by
    calc ‖(y + w) ^ 4 * K‖ ≤ ‖(y + w) ^ 4‖ * ‖K‖ := norm_mul_le _ _
      _ ≤ ‖y + w‖ ^ 4 * 9 := by
          gcongr
          exact norm_pow_le' _ (by norm_num)
      _ ≤ (6 * x) ^ 4 * 9 := by gcongr
  have e2 : ‖w * w‖ ≤ (4 * x ^ 2) * (4 * x ^ 2) := by
    calc ‖w * w‖ ≤ ‖w‖ * ‖w‖ := norm_mul_le _ _
      _ ≤ _ := by gcongr
  have hid : (y + w) ^ 3 - y ^ 3 = w * (y + w) ^ 2 + y * w * (y + w) + y ^ 2 * w := by
    noncomm_ring
  have e3 : ‖(y + w) ^ 3 - y ^ 3‖ ≤ (4 * x ^ 2) * (6 * x) ^ 2 + (2 * x) * (4 * x ^ 2) * (6 * x) +
      (2 * x) ^ 2 * (4 * x ^ 2) := by
    rw [hid]
    have t1 : ‖w * (y + w) ^ 2‖ ≤ (4 * x ^ 2) * (6 * x) ^ 2 := by
      calc ‖w * (y + w) ^ 2‖ ≤ ‖w‖ * ‖(y + w) ^ 2‖ := norm_mul_le _ _
        _ ≤ ‖w‖ * ‖y + w‖ ^ 2 := by gcongr; exact norm_pow_le' _ (by norm_num)
        _ ≤ (4 * x ^ 2) * (6 * x) ^ 2 := by gcongr
    have t2 : ‖y * w * (y + w)‖ ≤ (2 * x) * (4 * x ^ 2) * (6 * x) := by
      calc ‖y * w * (y + w)‖ ≤ ‖y * w‖ * ‖y + w‖ := norm_mul_le _ _
        _ ≤ (‖y‖ * ‖w‖) * ‖y + w‖ := by gcongr; exact norm_mul_le _ _
        _ ≤ (2 * x) * (4 * x ^ 2) * (6 * x) := by gcongr
    have t3 : ‖y ^ 2 * w‖ ≤ (2 * x) ^ 2 * (4 * x ^ 2) := by
      calc ‖y ^ 2 * w‖ ≤ ‖y ^ 2‖ * ‖w‖ := norm_mul_le _ _
        _ ≤ ‖y‖ ^ 2 * ‖w‖ := by gcongr; exact norm_pow_le' _ (by norm_num)
        _ ≤ (2 * x) ^ 2 * (4 * x ^ 2) := by gcongr
    calc _ ≤ ‖w * (y + w) ^ 2 + y * w * (y + w)‖ + ‖y ^ 2 * w‖ := norm_add_le _ _
      _ ≤ ‖w * (y + w) ^ 2‖ + ‖y * w * (y + w)‖ + ‖y ^ 2 * w‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ _ := by gcongr
  calc ‖(y + w) ^ 4 * K + w * w - ((y + w) ^ 3 - y ^ 3)‖
      ≤ ‖(y + w) ^ 4 * K + w * w‖ + ‖(y + w) ^ 3 - y ^ 3‖ := norm_sub_le _ _
    _ ≤ ‖(y + w) ^ 4 * K‖ + ‖w * w‖ + ‖(y + w) ^ 3 - y ^ 3‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ (6 * x) ^ 4 * 9 + (4 * x ^ 2) * (4 * x ^ 2) + ((4 * x ^ 2) * (6 * x) ^ 2 +
        (2 * x) * (4 * x ^ 2) * (6 * x) + (2 * x) ^ 2 * (4 * x ^ 2)) := by gcongr
    _ ≤ 12000 * x ^ 4 := by nlinarith [pow_nonneg hx0 4]


private theorem li_normalH_nonneg (E : ℝ) : 0 ≤ normalH E := by
  unfold normalH freeAngle
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg (E / 2))
    (Real.arccos_le_pi (E / 2))
  positivity

/-- The fourth-order expansion of `F⁻¹ F^{-*} = (F* F)⁻¹` in `t = h_θ/g`, with an exact remainder
of order `(t ‖V‖)⁴` for `t ‖V‖ ≤ 1` (proof of (11.12) [lg:eq:c2]). -/
private theorem li_K_expand (g E : ℝ) (hg : 0 < g) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian)
    (hx : normalH E / g * ‖V‖ ≤ 1) :
    ∃ R : Matrix (Fin W) (Fin W) ℂ,
      (stepF g E C V)⁻¹ * ((stepF g E C V)⁻¹)ᴴ =
        1 - ((normalH E / g : ℝ) : ℂ) • quadA C V +
        ((((normalH E / g) ^ 2 : ℝ)) : ℂ) • (quadA C V ^ 2 - quadB C V) +
        ((((normalH E / g) ^ 3 : ℝ)) : ℂ) •
          (quadA C V * quadB C V + quadB C V * quadA C V - quadA C V ^ 3) + R ∧
      ‖R‖ ≤ 12000 * (normalH E / g * ‖V‖) ^ 4 := by
  set t : ℝ := normalH E / g with ht_def
  have ht : 0 ≤ t := div_nonneg (li_normalH_nonneg E) hg.le
  have hFu := isUnit_stepF g E hC hV
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hFu
  have hFF : stepF g E C V * (stepF g E C V)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hFF' : (stepF g E C V)⁻¹ * stepF g E C V = 1 := Matrix.nonsing_inv_mul _ hdet
  have hgram : (stepF g E C V)ᴴ * stepF g E C V =
      1 + ((t : ℂ) • quadA C V + ((t ^ 2 : ℝ) : ℂ) • quadB C V) := by
    rw [← add_assoc]
    exact li_gram t C V hV
  have hGK : (1 + ((t : ℂ) • quadA C V + ((t ^ 2 : ℝ) : ℂ) • quadB C V)) *
      ((stepF g E C V)⁻¹ * ((stepF g E C V)⁻¹)ᴴ) = 1 := by
    rw [← hgram]
    calc (stepF g E C V)ᴴ * stepF g E C V * ((stepF g E C V)⁻¹ * ((stepF g E C V)⁻¹)ᴴ)
        = (stepF g E C V)ᴴ * (stepF g E C V * (stepF g E C V)⁻¹) * ((stepF g E C V)⁻¹)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = ((stepF g E C V)⁻¹ * stepF g E C V)ᴴ := by
          rw [hFF, Matrix.mul_one, Matrix.conjTranspose_mul]
      _ = 1 := by rw [hFF', Matrix.conjTranspose_one]
  have key := li_neumann ((t : ℂ) • quadA C V) (((t ^ 2 : ℝ) : ℂ) • quadB C V) _ hGK
  have hx0 : 0 ≤ t * ‖V‖ := by positivity
  have hA := li_norm_quadA_le hC V
  have hB := li_norm_quadB_le hC V
  have hFi := (norm_stepF_le hg E hC hV).2
  refine ⟨((t : ℂ) • quadA C V + ((t ^ 2 : ℝ) : ℂ) • quadB C V) ^ 4 *
      ((stepF g E C V)⁻¹ * ((stepF g E C V)⁻¹)ᴴ) +
      (((t ^ 2 : ℝ) : ℂ) • quadB C V) * (((t ^ 2 : ℝ) : ℂ) • quadB C V) -
      (((t : ℂ) • quadA C V + ((t ^ 2 : ℝ) : ℂ) • quadB C V) ^ 3 - ((t : ℂ) • quadA C V) ^ 3),
    ?_, ?_⟩
  · refine key.trans ?_
    congr 1
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ, pow_zero, one_mul, smul_sub,
      smul_add]
    match_scalars <;> ring
  · apply li_rem_norm _ _ _ hx0 hx
    · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ht]
      calc t * ‖quadA C V‖ ≤ t * (2 * ‖V‖) := by gcongr
        _ = 2 * (t * ‖V‖) := by ring
    · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc t ^ 2 * ‖quadB C V‖ ≤ t ^ 2 * (4 * ‖V‖ ^ 2) := by gcongr
        _ = 4 * (t * ‖V‖) ^ 2 := by ring
    · have h1 : ‖(stepF g E C V)⁻¹‖ ≤ 1 + 2 * (t * ‖V‖) := by
        have : 1 + 2 * normalH E * ‖V‖ / g = 1 + 2 * (t * ‖V‖) := by
          rw [ht_def]; ring
        rw [← this]; exact hFi
      calc ‖(stepF g E C V)⁻¹ * ((stepF g E C V)⁻¹)ᴴ‖
          ≤ ‖(stepF g E C V)⁻¹‖ * ‖((stepF g E C V)⁻¹)ᴴ‖ := norm_mul_le _ _
        _ = ‖(stepF g E C V)⁻¹‖ * ‖(stepF g E C V)⁻¹‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ (1 + 2 * (t * ‖V‖)) * (1 + 2 * (t * ‖V‖)) := by gcongr
        _ ≤ 3 * 3 := by gcongr <;> linarith
        _ = 9 := by norm_num


/-- The scalar part of the symmetrized expansion: with `Y_± = 1 ∓ α + u ± γ + R_±`,
`log Y_+ + log Y_- = 2u - α² + O(x⁴)` for `x ≤ 1`. -/
private theorem li_real_core {x α u γ Rp Rm Yp Ym : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hα : |α| ≤ 2 * x) (hu : |u| ≤ 8 * x ^ 2) (hγ : |γ| ≤ 24 * x ^ 3)
    (hRp : |Rp| ≤ 12000 * x ^ 4) (hRm : |Rm| ≤ 12000 * x ^ 4)
    (hYp : Yp = 1 - α + u + γ + Rp) (hYm : Ym = 1 + α + u - γ + Rm)
    (hlp : ((1 + 2 * x) ^ 2)⁻¹ ≤ Yp) (hlm : ((1 + 2 * x) ^ 2)⁻¹ ≤ Ym) :
    |Real.log Yp + Real.log Ym - (2 * u - α ^ 2)| ≤ 4 * 10 ^ 18 * x ^ 4 := by
  have hx2 : x ^ 2 ≤ x := by nlinarith
  have hx3 : x ^ 3 ≤ x ^ 2 := pow_le_pow_of_le_one hx0 hx1 (by norm_num)
  have hx4 : x ^ 4 ≤ x ^ 2 := pow_le_pow_of_le_one hx0 hx1 (by norm_num)
  have hx5 : x ^ 5 ≤ x ^ 4 := pow_le_pow_of_le_one hx0 hx1 (by norm_num)
  have hx40 : 0 ≤ x ^ 4 := by positivity
  have hx20 : 0 ≤ x ^ 2 := by positivity
  have hm : (1 / 9 : ℝ) ≤ ((1 + 2 * x) ^ 2)⁻¹ := by
    rw [← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hYp0 : 1 / 9 ≤ Yp := hm.trans hlp
  have hYm0 : 1 / 9 ≤ Ym := hm.trans hlm
  have hP : 1 / 81 ≤ Yp * Ym := by
    calc (1 / 81 : ℝ) = (1 / 9) * (1 / 9) := by norm_num
      _ ≤ Yp * Ym := mul_le_mul hYp0 hYm0 (by norm_num) (by linarith)
  have hPpos : 0 < Yp * Ym := lt_of_lt_of_le (by norm_num) hP
  have hlog : Real.log Yp + Real.log Ym = Real.log (Yp * Ym) :=
    (Real.log_mul (by linarith) (by linarith)).symm
  -- the logarithm against the first-order expansion at `Yp * Ym - 1`
  have hlog1 : Real.log (Yp * Ym) ≤ Yp * Ym - 1 := Real.log_le_sub_one_of_pos hPpos
  have hlog2 : 1 - (Yp * Ym)⁻¹ ≤ Real.log (Yp * Ym) := Real.one_sub_inv_le_log_of_pos hPpos
  have hinv : (Yp * Ym)⁻¹ ≤ 81 := by
    rw [inv_le_comm₀ hPpos (by norm_num)]
    linarith
  have hε2 : |Real.log (Yp * Ym) - (Yp * Ym - 1)| ≤ 81 * (Yp * Ym - 1) ^ 2 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have h1 : Yp * Ym - 1 - Real.log (Yp * Ym) ≤ (Yp * Ym)⁻¹ * (Yp * Ym - 1) ^ 2 := by
      have : (Yp * Ym)⁻¹ * (Yp * Ym - 1) ^ 2 = Yp * Ym - 2 + (Yp * Ym)⁻¹ := by
        field_simp
        ring
      rw [this]
      linarith
    calc _ ≤ (Yp * Ym)⁻¹ * (Yp * Ym - 1) ^ 2 := h1
      _ ≤ 81 * (Yp * Ym - 1) ^ 2 := by gcongr
  -- the second-order part
  have hid : Yp * Ym - 1 - (2 * u - α ^ 2) =
      Rp + Rm + α * (2 * γ + Rp - Rm) + (u + γ + Rp) * (u - γ + Rm) := by
    rw [hYp, hYm]; ring
  have hep : |u + γ + Rp| ≤ 12032 * x ^ 2 := by
    calc |u + γ + Rp| ≤ |u + γ| + |Rp| := abs_add_le _ _
      _ ≤ |u| + |γ| + |Rp| := by gcongr; exact abs_add_le _ _
      _ ≤ 12032 * x ^ 2 := by linarith
  have hem : |u - γ + Rm| ≤ 12032 * x ^ 2 := by
    calc |u - γ + Rm| ≤ |u - γ| + |Rm| := abs_add_le _ _
      _ ≤ |u| + |γ| + |Rm| := by gcongr; exact abs_sub _ _
      _ ≤ 12032 * x ^ 2 := by linarith
  have hee : |(u + γ + Rp) * (u - γ + Rm)| ≤ 144769024 * x ^ 4 := by
    rw [abs_mul]
    calc |u + γ + Rp| * |u - γ + Rm| ≤ (12032 * x ^ 2) * (12032 * x ^ 2) :=
          mul_le_mul hep hem (abs_nonneg _) (by positivity)
      _ = 144769024 * x ^ 4 := by ring
  have hg3 : |2 * γ + Rp - Rm| ≤ 48 * x ^ 3 + 24000 * x ^ 4 := by
    calc |2 * γ + Rp - Rm| ≤ |2 * γ + Rp| + |Rm| := abs_sub _ _
      _ ≤ |2 * γ| + |Rp| + |Rm| := by gcongr; exact abs_add_le _ _
      _ = 2 * |γ| + |Rp| + |Rm| := by rw [abs_mul]; norm_num
      _ ≤ 48 * x ^ 3 + 24000 * x ^ 4 := by linarith
  have hag : |α * (2 * γ + Rp - Rm)| ≤ 96 * x ^ 4 + 48000 * x ^ 4 := by
    rw [abs_mul]
    calc |α| * |2 * γ + Rp - Rm| ≤ (2 * x) * (48 * x ^ 3 + 24000 * x ^ 4) :=
          mul_le_mul hα hg3 (abs_nonneg _) (by positivity)
      _ = 96 * x ^ 4 + 48000 * x ^ 5 := by ring
      _ ≤ 96 * x ^ 4 + 48000 * x ^ 4 := by linarith
  have hrem : |Yp * Ym - 1 - (2 * u - α ^ 2)| ≤ 150000000 * x ^ 4 := by
    rw [hid]
    calc |Rp + Rm + α * (2 * γ + Rp - Rm) + (u + γ + Rp) * (u - γ + Rm)|
        ≤ |Rp + Rm + α * (2 * γ + Rp - Rm)| + |(u + γ + Rp) * (u - γ + Rm)| := abs_add_le _ _
      _ ≤ (|Rp + Rm| + |α * (2 * γ + Rp - Rm)|) + |(u + γ + Rp) * (u - γ + Rm)| := by
          gcongr; exact abs_add_le _ _
      _ ≤ ((|Rp| + |Rm|) + |α * (2 * γ + Rp - Rm)|) + |(u + γ + Rp) * (u - γ + Rm)| := by
          gcongr; exact abs_add_le _ _
      _ ≤ 150000000 * x ^ 4 := by linarith
  have hε : |Yp * Ym - 1| ≤ 200000000 * x ^ 2 := by
    have h2 : |2 * u - α ^ 2| ≤ 20 * x ^ 2 := by
      calc |2 * u - α ^ 2| ≤ |2 * u| + |α ^ 2| := abs_sub _ _
        _ = 2 * |u| + |α| ^ 2 := by rw [abs_mul, abs_pow]; norm_num
        _ ≤ 2 * (8 * x ^ 2) + (2 * x) ^ 2 := by gcongr
        _ = 20 * x ^ 2 := by ring
    calc |Yp * Ym - 1| = |(Yp * Ym - 1 - (2 * u - α ^ 2)) + (2 * u - α ^ 2)| := by ring_nf
      _ ≤ |Yp * Ym - 1 - (2 * u - α ^ 2)| + |2 * u - α ^ 2| := abs_add_le _ _
      _ ≤ 200000000 * x ^ 2 := by linarith
  have hsq : (Yp * Ym - 1) ^ 2 ≤ 4 * 10 ^ 16 * x ^ 4 := by
    have h0 := sq_abs (Yp * Ym - 1)
    rw [← h0]
    calc |Yp * Ym - 1| ^ 2 ≤ (200000000 * x ^ 2) ^ 2 := by gcongr
      _ = 4 * 10 ^ 16 * x ^ 4 := by ring
  rw [hlog]
  calc |Real.log (Yp * Ym) - (2 * u - α ^ 2)|
      = |(Real.log (Yp * Ym) - (Yp * Ym - 1)) + (Yp * Ym - 1 - (2 * u - α ^ 2))| := by ring_nf
    _ ≤ |Real.log (Yp * Ym) - (Yp * Ym - 1)| + |Yp * Ym - 1 - (2 * u - α ^ 2)| := abs_add_le _ _
    _ ≤ 4 * 10 ^ 18 * x ^ 4 := by nlinarith


/-- `‖F^{-*} v‖² = v* F⁻¹ F^{-*} v`. -/
private theorem li_normSq {W : ℕ} (F : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) :
    ‖Matrix.toEuclideanLin ((F⁻¹)ᴴ) v‖ ^ 2 = li_phi v (F⁻¹ * (F⁻¹)ᴴ) := by
  set w := Matrix.toEuclideanLin ((F⁻¹)ᴴ) v with hw
  have h1 : inner ℂ v (Matrix.toEuclideanLin ((F⁻¹)ᴴ)ᴴ w) = inner ℂ w w := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]
  have h2 : Matrix.toEuclideanLin ((F⁻¹)ᴴ)ᴴ w = Matrix.toEuclideanLin (F⁻¹ * (F⁻¹)ᴴ) v := by
    rw [Matrix.conjTranspose_conjTranspose, hw]
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  have h3 : ((‖w‖ ^ 2 : ℝ) : ℂ) = inner ℂ w w := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  unfold li_phi vecForm
  rw [← h2, h1, ← h3, Complex.ofReal_re]

/-- `‖F^{-*} v‖ ≥ (1 + 2x)⁻¹`, from `F* (F^{-*} v) = v` and `‖F‖ ≤ 1 + 2x`. -/
private theorem li_norm_stepVec_ge (g E : ℝ) (hg : 0 < g) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    (1 + 2 * (normalH E / g * ‖V‖))⁻¹ ≤ ‖stepVec g E X V‖ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_stepF g E hX.1 hV)
  have hFF' : (stepF g E X.1 V)⁻¹ * stepF g E X.1 V = 1 := Matrix.nonsing_inv_mul _ hdet
  have hadj : Matrix.toEuclideanLin (stepF g E X.1 V)ᴴ (stepVec g E X V) = X.2 := by
    unfold stepVec
    have : Matrix.toEuclideanLin (stepF g E X.1 V)ᴴ
        (Matrix.toEuclideanLin ((stepF g E X.1 V)⁻¹ᴴ) X.2) =
        Matrix.toEuclideanLin ((stepF g E X.1 V)ᴴ * (stepF g E X.1 V)⁻¹ᴴ) X.2 := by
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    rw [this, ← Matrix.conjTranspose_mul, hFF', Matrix.conjTranspose_one]
    simp
  have hF := (norm_stepF_le hg E hX.1 hV).1
  have hpos : 0 < 1 + 2 * (normalH E / g * ‖V‖) := by
    have := li_normalH_nonneg E
    positivity
  have h1 : 1 ≤ (1 + 2 * (normalH E / g * ‖V‖)) * ‖stepVec g E X V‖ := by
    calc (1 : ℝ) = ‖X.2‖ := hX.2.symm
      _ = ‖Matrix.toEuclideanLin (stepF g E X.1 V)ᴴ (stepVec g E X V)‖ := by rw [hadj]
      _ ≤ ‖(stepF g E X.1 V)ᴴ‖ * ‖stepVec g E X V‖ := li_norm_lin_le _ _
      _ = ‖stepF g E X.1 V‖ * ‖stepVec g E X V‖ := by rw [Matrix.l2_opNorm_conjTranspose]
      _ ≤ (1 + 2 * (normalH E / g * ‖V‖)) * ‖stepVec g E X V‖ := by
          gcongr
          calc ‖stepF g E X.1 V‖ ≤ 1 + 2 * normalH E * ‖V‖ / g := hF
            _ = 1 + 2 * (normalH E / g * ‖V‖) := by ring
  rw [inv_le_iff_one_le_mul₀ hpos]
  linarith

/-- The expansion of `‖F^{-*} v‖²` in `t = h_θ/g` to third order, with remainder `O(x⁴)`,
`x = t ‖V‖ ≤ 1`. -/
private theorem li_Y_expand (g E : ℝ) (hg : 0 < g) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) (hx : normalH E / g * ‖V‖ ≤ 1) :
    ∃ R : ℝ, ‖stepVec g E X V‖ ^ 2 =
      1 - normalH E / g * li_phi X.2 (quadA X.1 V) +
      (normalH E / g) ^ 2 * (li_phi X.2 (quadA X.1 V ^ 2) - li_phi X.2 (quadB X.1 V)) +
      (normalH E / g) ^ 3 * li_phi X.2 (quadA X.1 V * quadB X.1 V +
        quadB X.1 V * quadA X.1 V - quadA X.1 V ^ 3) + R ∧
      |R| ≤ 12000 * (normalH E / g * ‖V‖) ^ 4 := by
  obtain ⟨Rm, hK, hn⟩ := li_K_expand g E hg hX.1 hV hx
  refine ⟨li_phi X.2 Rm, ?_, (li_abs_phi_le hX.2 Rm).trans hn⟩
  change ‖Matrix.toEuclideanLin ((stepF g E X.1 V)⁻¹ᴴ) X.2‖ ^ 2 = _
  rw [li_normSq, hK]
  simp only [li_phi_add, li_phi_sub, li_phi_smul, li_phi_one hX.2]


/-- `c(V) + c(-V)` against `t² (v* B v - v* A² v + (v* A v)²/2)` when `t ‖V‖ ≤ 1` (proof of (11.12)
[lg:eq:c2]): the terms of odd order in `V` cancel. -/
private theorem li_pair_small (g E : ℝ) (hg : 0 < g) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) (hx : normalH E / g * ‖V‖ ≤ 1) :
    |stepInc g E X V + stepInc g E X (-V) -
        (normalH E / g) ^ 2 * (li_phi X.2 (quadB X.1 V) - li_phi X.2 (quadA X.1 V ^ 2) +
          li_phi X.2 (quadA X.1 V) ^ 2 / 2)| ≤ 2 * 10 ^ 18 * (normalH E / g * ‖V‖) ^ 4 := by
  set t : ℝ := normalH E / g with ht_def
  have ht : 0 ≤ t := div_nonneg (li_normalH_nonneg E) hg.le
  set x : ℝ := t * ‖V‖ with hx_def
  have hx0 : 0 ≤ x := by positivity
  set A := quadA X.1 V with hA_def
  set B := quadB X.1 V with hB_def
  have hxn : t * ‖-V‖ ≤ 1 := by rwa [norm_neg]
  obtain ⟨Rp, hYp, hRp⟩ := li_Y_expand g E hg hX hV hx
  obtain ⟨Rm, hYm, hRm⟩ := li_Y_expand g E hg hX hV.neg hxn
  rw [norm_neg] at hRm
  rw [li_quadA_neg, li_quadB_neg] at hYm
  have e1 : (-A) ^ 2 = A ^ 2 := neg_sq A
  have e2 : -A * B + B * -A - (-A) ^ 3 = -(A * B + B * A - A ^ 3) := by noncomm_ring
  rw [e1, e2, li_phi_neg, li_phi_neg] at hYm
  have hAn : ‖A‖ ≤ 2 * ‖V‖ := li_norm_quadA_le hX.1 V
  have hBn : ‖B‖ ≤ 4 * ‖V‖ ^ 2 := li_norm_quadB_le hX.1 V
  have hv := hX.2
  have hAA : ‖A ^ 2‖ ≤ 4 * ‖V‖ ^ 2 := by
    calc ‖A ^ 2‖ ≤ ‖A‖ ^ 2 := norm_pow_le' _ (by norm_num)
      _ ≤ (2 * ‖V‖) ^ 2 := by gcongr
      _ = 4 * ‖V‖ ^ 2 := by ring
  have hAAA : ‖A ^ 3‖ ≤ 8 * ‖V‖ ^ 3 := by
    calc ‖A ^ 3‖ ≤ ‖A‖ ^ 3 := norm_pow_le' _ (by norm_num)
      _ ≤ (2 * ‖V‖) ^ 3 := by gcongr
      _ = 8 * ‖V‖ ^ 3 := by ring
  have hcub : ‖A * B + B * A - A ^ 3‖ ≤ 24 * ‖V‖ ^ 3 := by
    calc ‖A * B + B * A - A ^ 3‖ ≤ ‖A * B + B * A‖ + ‖A ^ 3‖ := norm_sub_le _ _
      _ ≤ (‖A * B‖ + ‖B * A‖) + ‖A ^ 3‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (‖A‖ * ‖B‖ + ‖B‖ * ‖A‖) + ‖A ^ 3‖ := by
          gcongr <;> exact norm_mul_le _ _
      _ ≤ ((2 * ‖V‖) * (4 * ‖V‖ ^ 2) + (4 * ‖V‖ ^ 2) * (2 * ‖V‖)) + 8 * ‖V‖ ^ 3 := by
          gcongr
      _ = 24 * ‖V‖ ^ 3 := by ring
  have hα : |t * li_phi X.2 A| ≤ 2 * x := by
    rw [abs_mul, abs_of_nonneg ht]
    calc t * |li_phi X.2 A| ≤ t * (2 * ‖V‖) := by
          gcongr; exact (li_abs_phi_le hv A).trans hAn
      _ = 2 * x := by rw [hx_def]; ring
  have hu : |t ^ 2 * (li_phi X.2 (A ^ 2) - li_phi X.2 B)| ≤ 8 * x ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc t ^ 2 * |li_phi X.2 (A ^ 2) - li_phi X.2 B|
        ≤ t ^ 2 * (4 * ‖V‖ ^ 2 + 4 * ‖V‖ ^ 2) := by
          gcongr
          calc |li_phi X.2 (A ^ 2) - li_phi X.2 B|
              ≤ |li_phi X.2 (A ^ 2)| + |li_phi X.2 B| := abs_sub _ _
            _ ≤ ‖A ^ 2‖ + ‖B‖ := add_le_add (li_abs_phi_le hv _) (li_abs_phi_le hv _)
            _ ≤ 4 * ‖V‖ ^ 2 + 4 * ‖V‖ ^ 2 := add_le_add hAA hBn
      _ = 8 * x ^ 2 := by rw [hx_def]; ring
  have hγ : |t ^ 3 * li_phi X.2 (A * B + B * A - A ^ 3)| ≤ 24 * x ^ 3 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc t ^ 3 * |li_phi X.2 (A * B + B * A - A ^ 3)| ≤ t ^ 3 * (24 * ‖V‖ ^ 3) := by
          gcongr; exact (li_abs_phi_le hv _).trans hcub
      _ = 24 * x ^ 3 := by rw [hx_def]; ring
  have hlp : ((1 + 2 * x) ^ 2)⁻¹ ≤ ‖stepVec g E X V‖ ^ 2 := by
    have := li_norm_stepVec_ge g E hg hX hV
    rw [← inv_pow]
    gcongr
  have hlm : ((1 + 2 * x) ^ 2)⁻¹ ≤ ‖stepVec g E X (-V)‖ ^ 2 := by
    have := li_norm_stepVec_ge g E hg hX hV.neg
    rw [norm_neg] at this
    rw [← inv_pow]
    gcongr
  have core := li_real_core hx0 hx (α := t * li_phi X.2 A)
    (u := t ^ 2 * (li_phi X.2 (A ^ 2) - li_phi X.2 B))
    (γ := t ^ 3 * li_phi X.2 (A * B + B * A - A ^ 3)) (Rp := Rp) (Rm := Rm)
    (Yp := ‖stepVec g E X V‖ ^ 2) (Ym := ‖stepVec g E X (-V)‖ ^ 2)
    hα hu hγ hRp hRm (by linarith) (by linarith) hlp hlm
  have hlogp : Real.log (‖stepVec g E X V‖ ^ 2) = -2 * stepInc g E X V := by
    unfold stepInc; rw [Real.log_pow]; push_cast; ring
  have hlogm : Real.log (‖stepVec g E X (-V)‖ ^ 2) = -2 * stepInc g E X (-V) := by
    unfold stepInc; rw [Real.log_pow]; push_cast; ring
  rw [hlogp, hlogm] at core
  have : stepInc g E X V + stepInc g E X (-V) -
        t ^ 2 * (li_phi X.2 B - li_phi X.2 (A ^ 2) + li_phi X.2 A ^ 2 / 2) =
      -(1 / 2) * (-2 * stepInc g E X V + -2 * stepInc g E X (-V) -
        (2 * (t ^ 2 * (li_phi X.2 (A ^ 2) - li_phi X.2 B)) - (t * li_phi X.2 A) ^ 2)) := by
    ring
  rw [this, abs_mul]
  calc |-(1 / 2 : ℝ)| * |-2 * stepInc g E X V + -2 * stepInc g E X (-V) -
        (2 * (t ^ 2 * (li_phi X.2 (A ^ 2) - li_phi X.2 B)) - (t * li_phi X.2 A) ^ 2)|
      ≤ (1 / 2) * (4 * 10 ^ 18 * x ^ 4) := by
        rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        gcongr
    _ = 2 * 10 ^ 18 * x ^ 4 := by ring


/-- `|c| ≤ 2 t ‖V‖` for every Hermitian block, from (11.13) [uvg:eq:global]. -/
private theorem li_abs_inc_le (g E : ℝ) (hg : 0 < g) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    |stepInc g E X V| ≤ 2 * (normalH E / g * ‖V‖) := by
  refine (abs_stepInc_le hg E hX hV).trans ?_
  have h1 := Real.log_le_sub_one_of_pos
    (show 0 < 1 + 2 * normalH E * ‖V‖ / g by
      have := li_normalH_nonneg E
      positivity)
  have h2 : 1 + 2 * normalH E * ‖V‖ / g - 1 = 2 * (normalH E / g * ‖V‖) := by ring
  linarith

/-- `c(V) + c(-V)` against `t² (v* B v - v* A² v + (v* A v)²/2)` for every Hermitian `V`, without a
cutoff on `‖V‖` (proof of (11.12) [lg:eq:c2]). -/
private theorem li_pair_all (g E : ℝ) (hg : 0 < g) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    |stepInc g E X V + stepInc g E X (-V) -
        (normalH E / g) ^ 2 * (li_phi X.2 (quadB X.1 V) - li_phi X.2 (quadA X.1 V ^ 2) +
          li_phi X.2 (quadA X.1 V) ^ 2 / 2)| ≤ 2 * 10 ^ 18 * (normalH E / g * ‖V‖) ^ 4 := by
  by_cases hx : normalH E / g * ‖V‖ ≤ 1
  · exact li_pair_small g E hg hX hV hx
  · replace hx := not_le.mp hx
    set t : ℝ := normalH E / g with ht_def
    have ht : 0 ≤ t := div_nonneg (li_normalH_nonneg E) hg.le
    set x : ℝ := t * ‖V‖ with hx_def
    have hx0 : 0 ≤ x := by positivity
    have hcp : |stepInc g E X V| ≤ 2 * x := li_abs_inc_le g E hg hX hV
    have hcm : |stepInc g E X (-V)| ≤ 2 * x := by
      have := li_abs_inc_le g E hg hX hV.neg
      rwa [norm_neg] at this
    have hAn : ‖quadA X.1 V‖ ≤ 2 * ‖V‖ := li_norm_quadA_le hX.1 V
    have hBn : ‖quadB X.1 V‖ ≤ 4 * ‖V‖ ^ 2 := li_norm_quadB_le hX.1 V
    have hAA : ‖quadA X.1 V ^ 2‖ ≤ 4 * ‖V‖ ^ 2 := by
      calc ‖quadA X.1 V ^ 2‖ ≤ ‖quadA X.1 V‖ ^ 2 := norm_pow_le' _ (by norm_num)
        _ ≤ (2 * ‖V‖) ^ 2 := by gcongr
        _ = 4 * ‖V‖ ^ 2 := by ring
    have hv := hX.2
    have hT : |li_phi X.2 (quadB X.1 V) - li_phi X.2 (quadA X.1 V ^ 2) +
        li_phi X.2 (quadA X.1 V) ^ 2 / 2| ≤ 10 * ‖V‖ ^ 2 := by
      have a1 := (li_abs_phi_le hv (quadB X.1 V)).trans hBn
      have a2 := (li_abs_phi_le hv (quadA X.1 V ^ 2)).trans hAA
      have a3 : |li_phi X.2 (quadA X.1 V)| ≤ 2 * ‖V‖ := (li_abs_phi_le hv _).trans hAn
      have a4 : li_phi X.2 (quadA X.1 V) ^ 2 ≤ 4 * ‖V‖ ^ 2 := by
        calc li_phi X.2 (quadA X.1 V) ^ 2 = |li_phi X.2 (quadA X.1 V)| ^ 2 := (sq_abs _).symm
          _ ≤ (2 * ‖V‖) ^ 2 := by gcongr
          _ = 4 * ‖V‖ ^ 2 := by ring
      have a5 : 0 ≤ li_phi X.2 (quadA X.1 V) ^ 2 := sq_nonneg _
      rw [abs_le] at a1 a2 ⊢
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    have hTt : |t ^ 2 * (li_phi X.2 (quadB X.1 V) - li_phi X.2 (quadA X.1 V ^ 2) +
        li_phi X.2 (quadA X.1 V) ^ 2 / 2)| ≤ 10 * x ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      calc t ^ 2 * |_| ≤ t ^ 2 * (10 * ‖V‖ ^ 2) := by gcongr
        _ = 10 * x ^ 2 := by rw [hx_def]; ring
    have hx2 : x ≤ x ^ 2 := by nlinarith
    have hx4 : x ^ 2 ≤ x ^ 4 := by nlinarith [pow_nonneg hx0 2]
    have hx40 : 0 ≤ x ^ 4 := by positivity
    calc |stepInc g E X V + stepInc g E X (-V) - _|
        ≤ |stepInc g E X V + stepInc g E X (-V)| + |t ^ 2 * (li_phi X.2 (quadB X.1 V) -
          li_phi X.2 (quadA X.1 V ^ 2) + li_phi X.2 (quadA X.1 V) ^ 2 / 2)| := abs_sub _ _
      _ ≤ (|stepInc g E X V| + |stepInc g E X (-V)|) + 10 * x ^ 2 := by
          gcongr
          exact abs_add_le _ _
      _ ≤ 2 * 10 ^ 18 * x ^ 4 := by nlinarith


private theorem li_measurable_gueBlock (W : ℕ) :
    Measurable fun ω : Ω W 1 => gueBlock W 1 ω 0 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private theorem li_continuous_phi {W : ℕ} (v : EuclideanSpace ℂ (Fin W)) :
    Continuous (li_phi v : Matrix (Fin W) (Fin W) ℂ → ℝ) := by
  unfold li_phi vecForm
  have h1 : Continuous (fun M : Matrix (Fin W) (Fin W) ℂ => Matrix.toEuclideanLin M v) :=
    LinearMap.continuous_of_finiteDimensional
      ((LinearMap.applyₗ v).comp (Matrix.toEuclideanLin (n := Fin W) (𝕜 := ℂ)).toLinearMap)
  exact Complex.continuous_re.comp (continuous_const.inner h1)

private theorem li_continuous_quadA {W : ℕ} (C : Matrix (Fin W) (Fin W) ℂ) :
    Continuous (fun V : Matrix (Fin W) (Fin W) ℂ => quadA C V) := by
  unfold quadA
  fun_prop

private theorem li_continuous_quadB {W : ℕ} (C : Matrix (Fin W) (Fin W) ℂ) :
    Continuous (fun V : Matrix (Fin W) (Fin W) ℂ => quadB C V) := by
  unfold quadB
  exact (continuous_const.mul (continuous_id.pow 2)).mul continuous_const

/-- A bound by a moment of the block gives integrability. -/
private theorem li_integrable {W : ℕ} {f : Ω W 1 → ℝ} (hf : Measurable f) (K : ℝ) (p : ℕ)
    (hb : ∀ ω, |f ω| ≤ K * ‖gueBlock W 1 ω 0‖ ^ p) : Integrable f (μ W 1) := by
  refine Integrable.mono' ((integrable_norm_gueBlock_pow W p).const_mul K)
    hf.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  simpa [Real.norm_eq_abs] using hb ω

/-- The law of one GUE block is invariant under `V ↦ -V`. -/
private theorem li_integral_neg {W : ℕ} {f : Matrix (Fin W) (Fin W) ℂ → ℝ}
    (h1 : Integrable (fun ω => f (gueBlock W 1 ω 0)) (μ W 1))
    (h2 : Integrable (fun ω => f (-gueBlock W 1 ω 0)) (μ W 1)) :
    ∫ ω, f (-gueBlock W 1 ω 0) ∂(μ W 1) = ∫ ω, f (gueBlock W 1 ω 0) ∂(μ W 1) := by
  have h := integral_odd_gueBlock W (fun V => f V - f (-V)) (fun V => by simp)
  rw [integral_sub h1 h2] at h
  linarith

/-- The quadratic form of a Hermitian matrix is real. -/
private theorem li_vecForm_real {W : ℕ} {M : Matrix (Fin W) (Fin W) ℂ} (hM : M.IsHermitian)
    (v : EuclideanSpace ℂ (Fin W)) : vecForm M v = ((vecForm M v).re : ℂ) := by
  have h1 : inner ℂ v (Matrix.toEuclideanLin Mᴴ v) = inner ℂ (Matrix.toEuclideanLin M v) v := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]
  rw [hM.eq] at h1
  have h2 : (starRingEnd ℂ) (vecForm M v) = vecForm M v := by
    unfold vecForm
    rw [inner_conj_symm]
    exact h1.symm
  exact (Complex.conj_eq_iff_re.mp h2).symm

private theorem li_quadB_herm {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (hV : V.IsHermitian) :
    (quadB C V).IsHermitian := by
  unfold quadB Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hV.eq]
  simp [Matrix.mul_assoc]

/-- `𝔼 v* B v = 2 + 2 Re f_1` for the real part. -/
private theorem li_integral_phi_quadB {W : ℕ} (hW : 1 ≤ W) {X : State W} (hX : IsState X) :
    ∫ ω, li_phi X.2 (quadB X.1 (gueBlock W 1 ω 0)) ∂(μ W 1) = 2 + 2 * (obsF 1 X).re := by
  have h := integral_vecForm_quadB hW hX
  have hpt : ∀ ω : Ω W 1, vecForm (quadB X.1 (gueBlock W 1 ω 0)) X.2 =
      ((li_phi X.2 (quadB X.1 (gueBlock W 1 ω 0)) : ℝ) : ℂ) := fun ω =>
    li_vecForm_real (li_quadB_herm _ _ (gueBlock_isHermitian W 1 ω 0)) X.2
  simp_rw [hpt] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- `𝔼 v* A² v = 2 - 2 Re(m_1 f_1)` for the real part. -/
private theorem li_integral_phi_quadA_sq {W : ℕ} (hW : 1 ≤ W) {X : State W} (hX : IsState X) :
    ∫ ω, li_phi X.2 (quadA X.1 (gueBlock W 1 ω 0) ^ 2) ∂(μ W 1) =
      2 - 2 * (obsM 1 X * obsF 1 X).re := by
  have h := integral_vecForm_quadA_sq hW hX
  have hpt : ∀ ω : Ω W 1, vecForm (quadA X.1 (gueBlock W 1 ω 0) ^ 2) X.2 =
      ((li_phi X.2 (quadA X.1 (gueBlock W 1 ω 0) ^ 2) : ℝ) : ℂ) := fun ω =>
    li_vecForm_real ((li_quadA_herm _ _ (gueBlock_isHermitian W 1 ω 0)).pow 2) X.2
  simp_rw [hpt] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- `𝔼 (v* A v)² = 2 W⁻¹ (1 - Re f_1²)` for the real part. -/
private theorem li_integral_phi_quadA_sq' {W : ℕ} (hW : 1 ≤ W) {X : State W} (hX : IsState X) :
    ∫ ω, li_phi X.2 (quadA X.1 (gueBlock W 1 ω 0)) ^ 2 ∂(μ W 1) =
      2 * (W : ℝ)⁻¹ * (1 - (obsF 1 X ^ 2).re) := by
  have h := integral_sq_vecForm_quadA hW hX
  have hpt : ∀ ω : Ω W 1, vecForm (quadA X.1 (gueBlock W 1 ω 0)) X.2 ^ 2 =
      ((li_phi X.2 (quadA X.1 (gueBlock W 1 ω 0)) ^ 2 : ℝ) : ℂ) := fun ω => by
    rw [li_vecForm_real (li_quadA_herm _ _ (gueBlock_isHermitian W 1 ω 0)) X.2]
    push_cast
    rfl
  simp_rw [hpt] at h
  rw [integral_complex_ofReal] at h
  have e : (2 * (W : ℂ)⁻¹ * (1 - (((obsF 1 X ^ 2).re : ℝ) : ℂ))) =
      ((2 * (W : ℝ)⁻¹ * (1 - (obsF 1 X ^ 2).re) : ℝ) : ℂ) := by push_cast; ring
  rw [e] at h
  exact_mod_cast h


/-- Moments of `‖V‖` of one block as Bochner integrals, uniformly in `W`. -/
private theorem li_moment (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ, ∫ ω, ‖gueBlock W 1 ω 0‖ ^ p ∂(μ W 1) ≤ C := by
  obtain ⟨C, hC, h⟩ := lintegral_norm_gueBlock_pow_le p
  refine ⟨C, hC, fun W => ?_⟩
  have h1 := ofReal_integral_eq_lintegral_ofReal (integrable_norm_gueBlock_pow W p)
    (ae_of_all _ fun ω => by positivity)
  have h2 : ∫⁻ ω, ENNReal.ofReal (‖gueBlock W 1 ω 0‖ ^ p) ∂(μ W 1) =
      ∫⁻ ω, ‖gueBlock W 1 ω 0‖ₑ ^ p ∂(μ W 1) := by
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [h2] at h1
  exact (ENNReal.ofReal_le_ofReal_iff hC.le).mp (h1.le.trans (h W))


private theorem li_integrable_phiB {W : ℕ} {X : State W} (hX : IsState X) :
    Integrable (fun ω : Ω W 1 => li_phi X.2 (quadB X.1 (gueBlock W 1 ω 0))) (μ W 1) :=
  li_integrable (((li_continuous_phi X.2).comp (li_continuous_quadB X.1)).measurable.comp
    (li_measurable_gueBlock W)) 4 2 fun _ =>
    (li_abs_phi_le hX.2 _).trans (li_norm_quadB_le hX.1 _)

private theorem li_integrable_phiA2 {W : ℕ} {X : State W} (hX : IsState X) :
    Integrable (fun ω : Ω W 1 => li_phi X.2 (quadA X.1 (gueBlock W 1 ω 0) ^ 2)) (μ W 1) :=
  li_integrable (((li_continuous_phi X.2).comp ((li_continuous_quadA X.1).pow 2)).measurable.comp
    (li_measurable_gueBlock W)) 4 2 fun ω => by
      refine (li_abs_phi_le hX.2 _).trans ?_
      calc ‖quadA X.1 (gueBlock W 1 ω 0) ^ 2‖ ≤ ‖quadA X.1 (gueBlock W 1 ω 0)‖ ^ 2 :=
            norm_pow_le' _ (by norm_num)
        _ ≤ (2 * ‖gueBlock W 1 ω 0‖) ^ 2 := by gcongr; exact li_norm_quadA_le hX.1 _
        _ = 4 * ‖gueBlock W 1 ω 0‖ ^ 2 := by ring

private theorem li_integrable_phiAs {W : ℕ} {X : State W} (hX : IsState X) :
    Integrable (fun ω : Ω W 1 => li_phi X.2 (quadA X.1 (gueBlock W 1 ω 0)) ^ 2) (μ W 1) :=
  li_integrable ((((li_continuous_phi X.2).comp (li_continuous_quadA X.1)).pow 2).measurable.comp
    (li_measurable_gueBlock W)) 4 2 fun ω => by
      rw [abs_of_nonneg (sq_nonneg _)]
      calc li_phi X.2 (quadA X.1 (gueBlock W 1 ω 0)) ^ 2
          = |li_phi X.2 (quadA X.1 (gueBlock W 1 ω 0))| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * ‖gueBlock W 1 ω 0‖) ^ 2 := by
            gcongr
            exact (li_abs_phi_le hX.2 _).trans (li_norm_quadA_le hX.1 _)
        _ = 4 * ‖gueBlock W 1 ω 0‖ ^ 2 := by ring


/-- `t² (v* B v - v* A² v + (v* A v)²/2)`, the even part of the expansion of `c`. -/
private def li_T (t : ℝ) {W : ℕ} (X : State W) (V : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  t ^ 2 * (li_phi X.2 (quadB X.1 V) - li_phi X.2 (quadA X.1 V ^ 2) +
    li_phi X.2 (quadA X.1 V) ^ 2 / 2)

private theorem li_integrable_T {W : ℕ} (t : ℝ) {X : State W} (hX : IsState X) :
    Integrable (fun ω : Ω W 1 => li_T t X (gueBlock W 1 ω 0)) (μ W 1) :=
  (((li_integrable_phiB hX).sub (li_integrable_phiA2 hX)).add
    ((li_integrable_phiAs hX).div_const 2)).const_mul (t ^ 2)

private theorem li_integral_T {W : ℕ} (hW : 1 ≤ W) (t : ℝ) {X : State W} (hX : IsState X) :
    ∫ ω, li_T t X (gueBlock W 1 ω 0) ∂(μ W 1) =
      2 * (t ^ 2 * (1 / (2 * (W : ℝ)) + (obsF 1 X).re +
        (obsM 1 X * obsF 1 X).re - 1 / (2 * (W : ℝ)) * (obsF 1 X ^ 2).re)) := by
  have i1 : Integrable (fun ω : Ω W 1 => li_phi X.2 (quadB X.1 (gueBlock W 1 ω 0)) -
      li_phi X.2 (quadA X.1 (gueBlock W 1 ω 0) ^ 2)) (μ W 1) :=
    (li_integrable_phiB hX).sub (li_integrable_phiA2 hX)
  have i2 : Integrable (fun ω : Ω W 1 => li_phi X.2 (quadA X.1 (gueBlock W 1 ω 0)) ^ 2 / 2)
      (μ W 1) := (li_integrable_phiAs hX).div_const 2
  unfold li_T
  rw [integral_const_mul, integral_add i1 i2,
    integral_sub (li_integrable_phiB hX) (li_integrable_phiA2 hX), integral_div,
    li_integral_phi_quadB hW hX, li_integral_phi_quadA_sq hW hX,
    li_integral_phi_quadA_sq' hW hX]
  have hW0 : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

private theorem li_measurable_inc (g E : ℝ) {W : ℕ} (X : State W) :
    Measurable fun V : Matrix (Fin W) (Fin W) ℂ => stepInc g E X V := by
  have hS : Measurable fun V : Matrix (Fin W) (Fin W) ℂ => (X, V) :=
    Measurable.prodMk measurable_const measurable_id
  have h := (measurable_stepInc g E W).comp hS
  exact h

private theorem li_integrable_inc (g E : ℝ) (hg : 0 < g) {W : ℕ} {X : State W} (hX : IsState X) :
    Integrable (fun ω : Ω W 1 => stepInc g E X (gueBlock W 1 ω 0)) (μ W 1) := by
  have hm : Measurable (fun ω : Ω W 1 => stepInc g E X (gueBlock W 1 ω 0)) :=
    (li_measurable_inc g E X).comp (li_measurable_gueBlock W)
  refine li_integrable hm (2 * (normalH E / g)) 1 fun ω => ?_
  have := li_abs_inc_le g E hg hX (gueBlock_isHermitian W 1 ω 0)
  calc _ ≤ _ := this
    _ = _ := by ring

private theorem li_integrable_inc_neg (g E : ℝ) (hg : 0 < g) {W : ℕ} {X : State W}
    (hX : IsState X) :
    Integrable (fun ω : Ω W 1 => stepInc g E X (-gueBlock W 1 ω 0)) (μ W 1) := by
  have hm : Measurable (fun ω : Ω W 1 => stepInc g E X (-gueBlock W 1 ω 0)) :=
    ((li_measurable_inc g E X).comp continuous_neg.measurable).comp (li_measurable_gueBlock W)
  refine li_integrable hm (2 * (normalH E / g)) 1 fun ω => ?_
  have := li_abs_inc_le g E hg hX (gueBlock_isHermitian W 1 ω 0).neg
  rw [norm_neg] at this
  calc _ ≤ _ := this
    _ = _ := by ring


/-- The mean increment against `t² [W⁻¹/2 + Re f_1 + Re(m_1 f_1) - W⁻¹ Re f_1² / 2]`, with the
remainder bounded by `𝔼‖V‖⁴` (proof of (11.12) [lg:eq:c2]). -/
private theorem li_incMean_bound (g E : ℝ) (hg : 0 < g) {W : ℕ} (hW : 1 ≤ W) {X : State W}
    (hX : IsState X) {C₄ : ℝ} (hC₄ : ∫ ω, ‖gueBlock W 1 ω 0‖ ^ 4 ∂(μ W 1) ≤ C₄) :
    |incMean g E X - (normalH E / g) ^ 2 * (1 / (2 * (W : ℝ)) + (obsF 1 X).re +
        (obsM 1 X * obsF 1 X).re - 1 / (2 * (W : ℝ)) * (obsF 1 X ^ 2).re)| ≤
      10 ^ 18 * C₄ * (normalH E / g) ^ 4 := by
  set t : ℝ := normalH E / g with ht_def
  have ht : 0 ≤ t := div_nonneg (li_normalH_nonneg E) hg.le
  have hc1 := li_integrable_inc g E hg hX
  have hc2 := li_integrable_inc_neg g E hg hX
  have hsym := li_integral_neg (f := fun V => stepInc g E X V) hc1 hc2
  have hT := li_integrable_T t hX
  have hTint := li_integral_T hW t hX
  have hmom : Integrable (fun ω : Ω W 1 => 2 * 10 ^ 18 * t ^ 4 * ‖gueBlock W 1 ω 0‖ ^ 4)
      (μ W 1) := (integrable_norm_gueBlock_pow W 4).const_mul _
  have hDb : ‖∫ ω, (stepInc g E X (gueBlock W 1 ω 0) + stepInc g E X (-gueBlock W 1 ω 0) -
      li_T t X (gueBlock W 1 ω 0)) ∂(μ W 1)‖ ≤
      ∫ ω, 2 * 10 ^ 18 * t ^ 4 * ‖gueBlock W 1 ω 0‖ ^ 4 ∂(μ W 1) :=
    norm_integral_le_of_norm_le hmom (ae_of_all _ fun ω => by
      have := li_pair_all g E hg hX (gueBlock_isHermitian W 1 ω 0)
      rw [Real.norm_eq_abs]
      calc _ ≤ _ := this
        _ = 2 * 10 ^ 18 * t ^ 4 * ‖gueBlock W 1 ω 0‖ ^ 4 := by ring)
  have hs : Integrable (fun ω : Ω W 1 => stepInc g E X (gueBlock W 1 ω 0) +
      stepInc g E X (-gueBlock W 1 ω 0)) (μ W 1) := hc1.add hc2
  rw [integral_sub hs hT, integral_add hc1 hc2, hsym, hTint,
    integral_const_mul] at hDb
  have hinc : incMean g E X = ∫ ω, stepInc g E X (gueBlock W 1 ω 0) ∂(μ W 1) := rfl
  rw [← hinc] at hDb
  have ht4 : 0 ≤ 2 * 10 ^ 18 * t ^ 4 := by positivity
  rw [Real.norm_eq_abs] at hDb
  have hDb' := hDb.trans (mul_le_mul_of_nonneg_left hC₄ ht4)
  have e : incMean g E X + incMean g E X - 2 * (t ^ 2 * (1 / (2 * (W : ℝ)) +
      (obsF 1 X).re + (obsM 1 X * obsF 1 X).re - 1 / (2 * (W : ℝ)) * (obsF 1 X ^ 2).re)) =
      2 * (incMean g E X - t ^ 2 * (1 / (2 * (W : ℝ)) + (obsF 1 X).re +
        (obsM 1 X * obsF 1 X).re - 1 / (2 * (W : ℝ)) * (obsF 1 X ^ 2).re)) := by ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hDb'
  nlinarith


/-- `h_θ ≤ (2 √(1 - (E₀/2)²))⁻¹` for `|E| ≤ E₀ < 2`. -/
private theorem li_normalH_le {E₀ E : ℝ} (hE₀ : E₀ < 2) (hE : |E| ≤ E₀) :
    normalH E ≤ (2 * Real.sqrt (1 - (max E₀ 0 / 2) ^ 2))⁻¹ := by
  have h0 : 0 ≤ E₀ := (abs_nonneg E).trans hE
  rw [max_eq_left h0]
  have hlt : (E₀ / 2) ^ 2 < 1 := by nlinarith
  have hpos : 0 < Real.sqrt (1 - (E₀ / 2) ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hle : (E / 2) ^ 2 ≤ (E₀ / 2) ^ 2 := by
    have := sq_le_sq' (by linarith [abs_le.mp hE]) (abs_le.mp hE).2
    nlinarith [sq_abs E]
  have hsq : Real.sqrt (1 - (E₀ / 2) ^ 2) ≤ Real.sqrt (1 - (E / 2) ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  unfold normalH freeAngle
  rw [Real.sin_arccos]
  exact inv_anti₀ (by positivity) (by linarith)


/-- (11.12) [lg:eq:c2] for every `g ≥ 1`, uniformly in `W`, the state and `|E| ≤ E₀`:
`P_g c = h_θ² g⁻² [W⁻¹/2 + Re f_1 + Re(m_1 f_1) - W⁻¹ Re f_1² / 2] + O(g⁻⁴)`. -/
theorem incMean_expansion {E₀ : ℝ} (hE₀ : E₀ < 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X →
        |incMean g E X - normalH E ^ 2 / g ^ 2 *
            (1 / (2 * (W : ℝ)) + (obsF 1 X).re + (obsM 1 X * obsF 1 X).re -
              1 / (2 * (W : ℝ)) * (obsF 1 X ^ 2).re)| ≤ K / g ^ 4 := by
  obtain ⟨C₄, hC₄, hmom⟩ := li_moment 4
  have hδ : 0 < 1 - (max E₀ 0 / 2) ^ 2 := by
    have h1 : max E₀ 0 < 2 := max_lt hE₀ (by norm_num)
    have h2 : 0 ≤ max E₀ 0 := le_max_right _ _
    nlinarith
  set h₀ : ℝ := (2 * Real.sqrt (1 - (max E₀ 0 / 2) ^ 2))⁻¹ with hh₀
  have hh0 : 0 < h₀ := by
    have := Real.sqrt_pos.mpr hδ
    positivity
  refine ⟨10 ^ 18 * C₄ * h₀ ^ 4, by positivity, fun W hW g hg E hE X hX => ?_⟩
  have hg0 : 0 < g := by linarith
  have h1 := li_incMean_bound g E hg0 hW hX (hmom W)
  have hhE : normalH E ≤ h₀ := li_normalH_le hE₀ hE
  have hnH : 0 ≤ normalH E := li_normalH_nonneg E
  rw [div_pow (normalH E) g 2] at h1
  rw [show (normalH E / g) ^ 4 = normalH E ^ 4 / g ^ 4 from div_pow _ _ _] at h1
  refine h1.trans ?_
  calc 10 ^ 18 * C₄ * (normalH E ^ 4 / g ^ 4) ≤ 10 ^ 18 * C₄ * (h₀ ^ 4 / g ^ 4) := by
        gcongr
    _ = 10 ^ 18 * C₄ * h₀ ^ 4 / g ^ 4 := by ring


end LSBA
