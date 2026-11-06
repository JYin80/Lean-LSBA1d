import LSBA.Spectral.DeformedGridChain
import LSBA.Gauss.QuadLDE
import LSBA.Dyson.DeformedRootCont

/-!
# The averaged and entrywise local law

Lemma G.1 [us:lem:local-law]: the entrywise law (G.3) [us:eq:weighted-entry-law] for diagonal `B`,
the averaged law at rate `(nη)^{−1/2}` ((G.1) [us:eq:weighted-local-law]) and `Im⟨G⟩ ≍ 1`, for
`B ∈ 𝓑(ε)`.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal Matrix.Norms.L2Operator

noncomputable section
open scoped Classical

namespace LSBA

/-! ### Unitary conjugation -/

/-- The inverse of a matrix conjugated by a unitary. -/
private lemma localLaw_inv_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    ((W : Matrix ι ι ℂ) * X * star (W : Matrix ι ι ℂ))⁻¹ =
      (W : Matrix ι ι ℂ) * X⁻¹ * star (W : Matrix ι ι ℂ) := by
  have h1 : (W : Matrix ι ι ℂ) * star (W : Matrix ι ι ℂ) = 1 := Matrix.mem_unitaryGroup_iff.mp W.2
  have h2 : star (W : Matrix ι ι ℂ) * (W : Matrix ι ι ℂ) = 1 := Matrix.mem_unitaryGroup_iff'.mp W.2
  have e1 : (W : Matrix ι ι ℂ)⁻¹ = star (W : Matrix ι ι ℂ) := Matrix.inv_eq_right_inv h1
  have e2 : (star (W : Matrix ι ι ℂ))⁻¹ = (W : Matrix ι ι ℂ) := Matrix.inv_eq_right_inv h2
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, e1, e2, Matrix.mul_assoc]

/-- The resolvent of a unitary conjugate. -/
private lemma localLaw_resolventMat_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) (z : ℂ) :
    resolventMat ((W : Matrix ι ι ℂ) * A * star (W : Matrix ι ι ℂ)) z =
      (W : Matrix ι ι ℂ) * resolventMat A z * star (W : Matrix ι ι ℂ) := by
  have h1 : (W : Matrix ι ι ℂ) * star (W : Matrix ι ι ℂ) = 1 := Matrix.mem_unitaryGroup_iff.mp W.2
  have h : (W : Matrix ι ι ℂ) * A * star (W : Matrix ι ι ℂ) - z • (1 : Matrix ι ι ℂ) =
      (W : Matrix ι ι ℂ) * (A - z • (1 : Matrix ι ι ℂ)) * star (W : Matrix ι ι ℂ) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1]
  unfold resolventMat
  rw [h, localLaw_inv_conj]

/-- The normalized trace is invariant under unitary conjugation. -/
private lemma localLaw_ntr_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    ntr ((W : Matrix ι ι ℂ) * X * star (W : Matrix ι ι ℂ)) = ntr X := by
  have h2 : star (W : Matrix ι ι ℂ) * (W : Matrix ι ι ℂ) = 1 := Matrix.mem_unitaryGroup_iff'.mp W.2
  unfold ntr
  rw [Matrix.trace_mul_comm ((W : Matrix ι ι ℂ) * X) (star (W : Matrix ι ι ℂ)), ← Matrix.mul_assoc,
    h2, Matrix.one_mul]

/-- The class of Lemma A.21 [da:lem:deformed] is invariant under unitary conjugation. -/
private lemma localLaw_deformClass_conj {n : ℕ} (hn : 0 < n) {ε : ℝ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : DeformClass ε B) (W : Matrix.unitaryGroup (Fin n) ℂ) :
    DeformClass ε ((W : Matrix (Fin n) (Fin n) ℂ) * B * star (W : Matrix (Fin n) (Fin n) ℂ)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨hBh, Bs, Bb, hsum, hs, hb⟩ := hB
  have hWu : (W : Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := W.2
  have hn1 : ‖(W : Matrix (Fin n) (Fin n) ℂ)‖ = 1 := CStarRing.norm_of_mem_unitary hWu
  have hn1' : ‖star (W : Matrix (Fin n) (Fin n) ℂ)‖ = 1 :=
    CStarRing.norm_of_mem_unitary (Unitary.star_mem hWu)
  refine ⟨?_, (W : Matrix (Fin n) (Fin n) ℂ) * Bs * star (W : Matrix (Fin n) (Fin n) ℂ),
    (W : Matrix (Fin n) (Fin n) ℂ) * Bb * star (W : Matrix (Fin n) (Fin n) ℂ), ?_, ?_, ?_⟩
  · have := Matrix.isHermitian_conjTranspose_mul_mul (star (W : Matrix (Fin n) (Fin n) ℂ)) hBh
    rwa [← Matrix.star_eq_conjTranspose, star_star] at this
  · rw [hsum, Matrix.mul_add, Matrix.add_mul]
  · calc ‖(W : Matrix (Fin n) (Fin n) ℂ) * Bs * star (W : Matrix (Fin n) (Fin n) ℂ)‖
        ≤ ‖(W : Matrix (Fin n) (Fin n) ℂ) * Bs‖ * ‖star (W : Matrix (Fin n) (Fin n) ℂ)‖ :=
          norm_mul_le _ _
      _ ≤ ‖(W : Matrix (Fin n) (Fin n) ℂ)‖ * ‖Bs‖ * ‖star (W : Matrix (Fin n) (Fin n) ℂ)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ε := by rw [hn1, hn1', one_mul, mul_one]; exact hs
  · have h1 : ((W : Matrix (Fin n) (Fin n) ℂ) * Bb * star (W : Matrix (Fin n) (Fin n) ℂ)).rank ≤
        Bb.rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    exact (Nat.cast_le.mpr h1).trans hb

/-- A Hermitian element of the class is a unitary conjugate of a diagonal element of the same
class; the conjugation acts on the GUE law by a measure-preserving map, and leaves `m_B` and the
normalized trace of the resolvent unchanged. -/
private lemma localLaw_reduce {n : ℕ} (hn : 0 < n) {ε : ℝ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : DeformClass ε B) :
    ∃ (D : Matrix (Fin n) (Fin n) ℂ) (f : Ω n 1 → Ω n 1), D.IsDiag ∧ DeformClass ε D ∧
      MeasurePreserving f (μ n 1) (μ n 1) ∧
      (∀ z : ℂ, 0 < z.im → mB B z = mB D z) ∧
      ∀ (ω : Ω n 1) (z : ℂ),
        ntr (resolventMat (gueMat n (f ω) - D) z) = ntr (resolventMat (gueMat n ω - B) z) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hBh : B.IsHermitian := hB.1
  set U : Matrix.unitaryGroup (Fin n) ℂ := hBh.eigenvectorUnitary with hU
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (RCLike.ofReal ∘ hBh.eigenvalues) with hD
  have hspec : B = (U : Matrix (Fin n) (Fin n) ℂ) * D * star (U : Matrix (Fin n) (Fin n) ℂ) := by
    have := hBh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hUU : (U : Matrix (Fin n) (Fin n) ℂ) * star (U : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  have hUU' : star (U : Matrix (Fin n) (Fin n) ℂ) * (U : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  set W : Matrix.unitaryGroup (Fin n) ℂ := U⁻¹ with hW
  have hWv : (W : Matrix (Fin n) (Fin n) ℂ) = star (U : Matrix (Fin n) (Fin n) ℂ) := rfl
  have hWs : star (W : Matrix (Fin n) (Fin n) ℂ) = (U : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hWv, star_star]
  have hDW : D = (W : Matrix (Fin n) (Fin n) ℂ) * B * star (W : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hWv, star_star]
    conv_rhs => rw [hspec]
    symm
    calc star (U : Matrix (Fin n) (Fin n) ℂ) * (U * D * star (U : Matrix (Fin n) (Fin n) ℂ)) *
          (U : Matrix (Fin n) (Fin n) ℂ)
        = (star (U : Matrix (Fin n) (Fin n) ℂ) * U) * D *
            (star (U : Matrix (Fin n) (Fin n) ℂ) * U) := by simp only [Matrix.mul_assoc]
      _ = D := by rw [hUU', Matrix.one_mul, Matrix.mul_one]
  have hcl : DeformClass ε D := by
    rw [hDW]; exact localLaw_deformClass_conj hn hB W
  refine ⟨D, conjMap n 1 W, Matrix.isDiag_diagonal _, hcl, measurePreserving_conjMap n 1 W,
    ?_, ?_⟩
  · intro z hz
    have hmB := isDeformedRoot_mB hBh hz
    have e1 : mB B z = ntr (MB B z) := by
      have := hmB.2
      unfold deformedMap at this
      exact this
    have hDh : D.IsHermitian := hcl.1
    have e2 : MB B z =
        (U : Matrix (Fin n) (Fin n) ℂ) * MB D z * star (U : Matrix (Fin n) (Fin n) ℂ) := by
      conv_lhs => rw [hspec]
      exact MB_conj U hDh hz
    have e3 : mB D z = ntr (MB D z) := by
      have := (isDeformedRoot_mB hDh hz).2
      unfold deformedMap at this
      exact this
    rw [e1, e2, e3, localLaw_ntr_conj U]
  · intro ω z
    have hV : gueMat n (conjMap n 1 W ω) =
        (W : Matrix (Fin n) (Fin n) ℂ) * gueMat n ω * star (W : Matrix (Fin n) (Fin n) ℂ) :=
      gueBlock_conjMap n 1 W ω 0
    have h : gueMat n (conjMap n 1 W ω) - D = (W : Matrix (Fin n) (Fin n) ℂ) *
        (gueMat n ω - B) * star (W : Matrix (Fin n) (Fin n) ℂ) := by
      rw [hV, hDW, Matrix.mul_sub, Matrix.sub_mul]
    rw [h, localLaw_resolventMat_conj, localLaw_ntr_conj]

/-- A set preimage under a measure-preserving map has no larger measure. -/
private lemma localLaw_preimage_le {n : ℕ} {f : Ω n 1 → Ω n 1}
    (hf : MeasurePreserving f (μ n 1) (μ n 1)) (S : Set (Ω n 1)) :
    μ n 1 (f ⁻¹' S) ≤ μ n 1 S := by
  calc μ n 1 (f ⁻¹' S) ≤ (μ n 1).map f S := Measure.le_map_apply hf.aemeasurable S
    _ = μ n 1 S := by rw [hf.map_eq]

/-! ### Asymptotics -/

/-- The union bound over the `2 n⁴ + 1` heights and the `n` indices, at `t = n^ξ'`, is at most
`n^{-D}` for large `n`, when `D + 7 ≤ 2 p ξ'`. -/
private lemma localLaw_union_eventually {K ξ' D : ℝ} {p : ℕ} (hK : 0 < K) (hξ' : 0 < ξ')
    (hD : 0 < D) (hp : D + 7 ≤ 2 * p * ξ') :
    ∀ᶠ n : ℕ in Filter.atTop, ((2 * n ^ 4 + 1 : ℕ) : ℝ) *
      ((n : ℝ) * (K * ((n : ℝ) ^ ξ') ^ (-(2 * (p : ℝ))) +
        2 * Real.exp (-((n : ℝ) ^ ξ') ^ 2 / 2))) ≤ (n : ℝ) ^ (-D) := by
  have hT : Filter.Tendsto (fun x : ℝ => x ^ ((5 + D) / (2 * ξ')) * Real.exp (-(1 / 2) * x))
      Filter.atTop (nhds 0) := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (by norm_num)
  have hx : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (2 * ξ')) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  have hG := (hT.comp hx).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 12 by norm_num))
  filter_upwards [hG, Filter.eventually_ge_atTop 1, Filter.eventually_ge_atTop ⌈6 * K⌉₊]
    with n hG hn1 hn6
  simp only [Function.comp_apply] at hG
  set N : ℝ := (n : ℝ) with hNdef
  have hN1 : 1 ≤ N := by rw [hNdef]; exact_mod_cast hn1
  have hN0 : 0 < N := by linarith
  have hN6 : 6 * K ≤ N := (Nat.le_ceil _).trans (by rw [hNdef]; exact_mod_cast hn6)
  set X : ℝ := N ^ (-D) with hX
  have hX0 : 0 < X := Real.rpow_pos_of_pos hN0 _
  have hXD : N ^ D * X = 1 := by
    rw [hX, ← Real.rpow_add hN0]; simp
  -- the polynomial term
  have hpoly : (N ^ ξ') ^ (-(2 * (p : ℝ))) ≤ X / N ^ 7 := by
    rw [← Real.rpow_mul hN0.le]
    have h1 : N ^ (ξ' * -(2 * (p : ℝ))) ≤ N ^ (-(D + 7)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
    have h2 : N ^ (-(D + 7)) = X / N ^ 7 := by
      rw [hX, show -(D + 7) = -D + -7 by ring, Real.rpow_add hN0, Real.rpow_neg hN0.le,
        div_eq_mul_inv]
      norm_num
    rw [← h2]; exact h1
  -- the Gaussian term
  have hgauss : N ^ 5 * Real.exp (-(N ^ ξ') ^ 2 / 2) ≤ X / 12 := by
    have e1 : (N ^ ξ') ^ 2 = N ^ (2 * ξ') := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
    have e2 : (N ^ (2 * ξ')) ^ ((5 + D) / (2 * ξ')) = N ^ (5 + D) := by
      rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
    have e3 : N ^ (5 + D) = N ^ 5 * N ^ D := by
      rw [Real.rpow_add hN0]; norm_num
    rw [e2, e3] at hG
    have e4 : -(N ^ ξ') ^ 2 / 2 = -(1 / 2) * N ^ (2 * ξ') := by rw [e1]; ring
    rw [e4]
    have h5 : N ^ 5 * N ^ D * Real.exp (-(1 / 2) * N ^ (2 * ξ')) < 1 / 12 := hG
    have := mul_lt_mul_of_pos_right h5 hX0
    calc N ^ 5 * Real.exp (-(1 / 2) * N ^ (2 * ξ'))
        = N ^ 5 * N ^ D * Real.exp (-(1 / 2) * N ^ (2 * ξ')) * X := by
          have : N ^ 5 * Real.exp (-(1 / 2) * N ^ (2 * ξ')) =
              N ^ 5 * Real.exp (-(1 / 2) * N ^ (2 * ξ')) * (N ^ D * X) := by rw [hXD, mul_one]
          rw [this]; ring
      _ ≤ 1 / 12 * X := this.le
      _ = X / 12 := by ring
  have hc : ((2 * n ^ 4 + 1 : ℕ) : ℝ) = 2 * N ^ 4 + 1 := by push_cast; rfl
  have h4 : 1 ≤ N ^ 4 := one_le_pow₀ hN1
  have hA : (2 * N ^ 4 + 1) * N ≤ 3 * N ^ 5 := by nlinarith
  have hB0 : 0 ≤ K * (N ^ ξ') ^ (-(2 * (p : ℝ))) + 2 * Real.exp (-(N ^ ξ') ^ 2 / 2) := by
    positivity
  have hN2 : 6 * K ≤ N ^ 2 := by nlinarith
  have hKa : 3 * K * N ^ 5 * (N ^ ξ') ^ (-(2 * (p : ℝ))) ≤ X / 2 := by
    calc 3 * K * N ^ 5 * (N ^ ξ') ^ (-(2 * (p : ℝ))) ≤ 3 * K * N ^ 5 * (X / N ^ 7) := by
          gcongr
      _ = 3 * K * X / N ^ 2 := by field_simp
      _ ≤ X / 2 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hN2 hX0.le]
  rw [hc]
  calc (2 * N ^ 4 + 1) * (N * (K * (N ^ ξ') ^ (-(2 * (p : ℝ))) + 2 * Real.exp (-(N ^ ξ') ^ 2 / 2)))
      = ((2 * N ^ 4 + 1) * N) * (K * (N ^ ξ') ^ (-(2 * (p : ℝ))) +
          2 * Real.exp (-(N ^ ξ') ^ 2 / 2)) := by ring
    _ ≤ (3 * N ^ 5) * (K * (N ^ ξ') ^ (-(2 * (p : ℝ))) + 2 * Real.exp (-(N ^ ξ') ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right hA hB0
    _ = 3 * K * N ^ 5 * (N ^ ξ') ^ (-(2 * (p : ℝ))) +
          6 * (N ^ 5 * Real.exp (-(N ^ ξ') ^ 2 / 2)) := by
        ring
    _ ≤ X / 2 + 6 * (X / 12) := add_le_add hKa (by gcongr)
    _ = X := by ring

/-- `c ≤ n^θ` for large `n`, `θ > 0`. -/
private lemma localLaw_rpow_ge_eventually {θ : ℝ} (hθ : 0 < θ) (c : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, c ≤ (n : ℝ) ^ θ :=
  ((tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c

/-- `n^{-θ} ≤ c` for large `n`, `θ > 0`, `c > 0`. -/
private lemma localLaw_rpow_neg_le_eventually {θ : ℝ} (hθ : 0 < θ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-θ) ≤ c :=
  (((tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop).eventually
    (gt_mem_nhds hc)).mono fun _ h => h.le

/-- `t / √(nη) ≤ n^{-(7δ/16)}` for `t = n^ξ'`, `ξ' ≤ δ/16` and `η ≥ n^{-1+δ}`. -/
private lemma localLaw_rate_le {n : ℕ} (hn : 1 ≤ n) {δ ξ' η : ℝ} (hξδ : ξ' ≤ δ / 16)
    (hη : (n : ℝ) ^ (-1 + δ) ≤ η) :
    (n : ℝ) ^ ξ' / Real.sqrt (n * η) ≤ (n : ℝ) ^ (-(7 * δ / 16)) := by
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have h1 : (n : ℝ) ^ δ ≤ n * η := by
    calc (n : ℝ) ^ δ = (n : ℝ) * (n : ℝ) ^ (-1 + δ) := by
          conv_lhs => rw [show δ = 1 + (-1 + δ) by ring, Real.rpow_add hN0, Real.rpow_one]
      _ ≤ n * η := by gcongr
  have h2 : (n : ℝ) ^ (δ / 2) ≤ Real.sqrt (n * η) := by
    rw [Real.sqrt_eq_rpow]
    calc (n : ℝ) ^ (δ / 2) = ((n : ℝ) ^ δ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hN0.le]; congr 1; ring
      _ ≤ (n * η) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  calc (n : ℝ) ^ ξ' / Real.sqrt (n * η) ≤ (n : ℝ) ^ ξ' / (n : ℝ) ^ (δ / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h2
    _ = (n : ℝ) ^ (ξ' - δ / 2) := (Real.rpow_sub hN0 _ _).symm
    _ ≤ (n : ℝ) ^ (-(7 * δ / 16)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

/-! ### The probabilistic core for diagonal `B` -/

/-- With `t = n^ξ'`, `ξ' ≤ δ/16`: for diagonal `B` in the class, the averaged and entrywise bounds
of the grid chain hold with probability `≥ 1 - n^{-D}`. -/
private theorem localLaw_core (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ δ ξ' D : ℝ, 0 < δ → 0 < ξ' → ξ' ≤ δ / 16 → 0 < D →
      ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℂ) (ε E η : ℝ),
        B.IsDiag → 0 ≤ ε → ε ≤ ε₀ → DeformClass ε B → |E| ≤ 2 - κ₀ →
        (n : ℝ) ^ (-1 + δ) ≤ η → η ≤ Cstar →
        μ n 1 {ω | ¬ (‖ntr (resolventMat (gueMat n ω - B) (E + η * Complex.I)) -
              mB B (E + η * Complex.I)‖ ≤ C * ((n : ℝ) ^ ξ' / Real.sqrt (n * η)) ∧
            ∀ i, ‖resolventMat (gueMat n ω - B) (E + η * Complex.I) i i -
              MB B (E + η * Complex.I) i i‖ ≤
                C * ((n : ℝ) ^ ξ' / Real.sqrt (n * η)) * ‖MB B (E + η * Complex.I) i i‖ ^ 2)} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-D)) := by
  obtain ⟨ε₀, c₀, C, hε₀, hc₀, hC0, n₁, hchain⟩ := deformed_grid_chain κ₀ Cstar hκ₀ hκ₀' hC
  refine ⟨ε₀, C, hε₀, hC0, ?_⟩
  intro δ ξ' D hδ hξ' hξδ hD
  set p : ℕ := ⌈(D + 7) / (2 * ξ')⌉₊ + 1 with hp
  have hp' : D + 7 ≤ 2 * (p : ℝ) * ξ' := by
    have h1 : (D + 7) / (2 * ξ') ≤ (p : ℝ) := by
      rw [hp]; push_cast; linarith [Nat.le_ceil ((D + 7) / (2 * ξ'))]
    have := (div_le_iff₀ (by positivity : 0 < 2 * ξ')).mp h1
    linarith
  obtain ⟨K, hK, hfail⟩ := schurEvents_fail_le p
  have e3 := localLaw_rpow_neg_le_eventually (θ := 7 * δ / 16) (by positivity) hc₀
  have e4 := localLaw_union_eventually hK hξ' hD hp'
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    ((Filter.eventually_ge_atTop n₁).and ((Filter.eventually_ge_atTop 1).and (e3.and e4)))
  refine ⟨max n₀ 1, le_max_right _ _, ?_⟩
  intro n hn B ε E η hBd hε0 hεε hcl hE hηlow hηC
  obtain ⟨hn₁, hn1, he3, he4⟩ := hn₀ n ((le_max_left _ _).trans hn)
  have hn0 : 0 < n := hn1
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < n := by linarith
  have hη0 : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hηlow
  set t : ℝ := (n : ℝ) ^ ξ' with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
  have ht1 : 1 ≤ t := Real.one_le_rpow hN1 hξ'.le
  have hnη : 1 ≤ (n : ℝ) * η := by
    have : (n : ℝ) ^ δ ≤ n * η := by
      calc (n : ℝ) ^ δ = (n : ℝ) * (n : ℝ) ^ (-1 + δ) := by
            conv_lhs => rw [show δ = 1 + (-1 + δ) by ring, Real.rpow_add hN0, Real.rpow_one]
        _ ≤ n * η := by gcongr
    exact (Real.one_le_rpow hN1 hδ.le).trans this
  have htc : t / Real.sqrt (n * η) ≤ c₀ :=
    (localLaw_rate_le hn1 hξδ hηlow).trans he3
  have hBh : B.IsHermitian := hcl.1
  -- the failure sets at the heights `η + k n⁻⁴`
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Set (Ω n 1), ∀ k, S k = {ω : Ω n 1 | ∃ i,
      t / Real.sqrt n < ‖gueMat n ω i i‖ ∨
      t / n * Real.sqrt (∑ k', ∑ l, ‖resolventMat (minorMat (gueMat n ω - B) i)
        (E + (η + (k : ℝ) / (n : ℝ) ^ 4) * Complex.I) k' l‖ ^ 2) <
        ‖schurQuadDev (gueMat n ω - B) (E + (η + (k : ℝ) / (n : ℝ) ^ 4) * Complex.I) i‖} :=
    ⟨fun k => _, fun k => rfl⟩
  have hSk : ∀ k, μ n 1 (S k) ≤
      ENNReal.ofReal (n * (K * t ^ (-(2 * (p : ℝ))) + 2 * Real.exp (-t ^ 2 / 2))) := by
    intro k
    rw [hS k]
    refine hfail n B hBh hBd _ t ?_ ht0
    have h0 : 0 ≤ (k : ℝ) / (n : ℝ) ^ 4 := by positivity
    have e : (E + (η + (k : ℝ) / (n : ℝ) ^ 4) * Complex.I) =
        ((E : ℝ) : ℂ) + ((η + (k : ℝ) / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
    linarith
  have hbad : {ω | ¬ (‖ntr (resolventMat (gueMat n ω - B) (E + η * Complex.I)) -
              mB B (E + η * Complex.I)‖ ≤ C * ((n : ℝ) ^ ξ' / Real.sqrt (n * η)) ∧
            ∀ i, ‖resolventMat (gueMat n ω - B) (E + η * Complex.I) i i -
              MB B (E + η * Complex.I) i i‖ ≤
                C * ((n : ℝ) ^ ξ' / Real.sqrt (n * η)) * ‖MB B (E + η * Complex.I) i i‖ ^ 2)} ⊆
      ⋃ k ∈ Finset.range (2 * n ^ 4 + 1), S k := by
    intro ω hω
    by_contra hnot
    apply hω
    simp only [Set.mem_iUnion, Finset.mem_range, not_exists] at hnot
    have hω' : ∀ k, k < 2 * n ^ 4 + 1 → ∀ i,
        ¬ (t / Real.sqrt n < ‖gueMat n ω i i‖ ∨
        t / n * Real.sqrt (∑ k', ∑ l, ‖resolventMat (minorMat (gueMat n ω - B) i)
          (E + (η + (k : ℝ) / (n : ℝ) ^ 4) * Complex.I) k' l‖ ^ 2) <
          ‖schurQuadDev (gueMat n ω - B) (E + (η + (k : ℝ) / (n : ℝ) ^ 4) * Complex.I) i‖) := by
      intro k hk i hi
      exact hnot k hk (by rw [hS k]; exact ⟨i, hi⟩)
    have hVd : ∀ i, ‖gueMat n ω i i‖ ≤ t / Real.sqrt n := fun i =>
      not_lt.mp (fun hlt => hω' 0 (by omega) i (Or.inl hlt))
    have hQ : ∀ k : ℕ, k ≤ 2 * n ^ 4 → ∀ i,
        ‖schurQuadDev (gueMat n ω - B) (E + (η + (k : ℝ) / (n : ℝ) ^ 4) * Complex.I) i‖ ≤
          t / n * Real.sqrt (∑ k', ∑ l, ‖resolventMat (minorMat (gueMat n ω - B) i)
            (E + (η + (k : ℝ) / (n : ℝ) ^ 4) * Complex.I) k' l‖ ^ 2) :=
      fun k hk i => not_lt.mp (fun hlt => hω' k (by omega) i (Or.inr hlt))
    exact hchain n (gueMat n ω) B ε E η t hn₁ hn0 (gueBlock_isHermitian n 1 ω 0) hBd hε0 hεε hcl
      hE hη0 hηC hnη ht1 htc hVd hQ
  calc μ n 1 _ ≤ μ n 1 (⋃ k ∈ Finset.range (2 * n ^ 4 + 1), S k) := measure_mono hbad
    _ ≤ ∑ k ∈ Finset.range (2 * n ^ 4 + 1), μ n 1 (S k) :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range (2 * n ^ 4 + 1), ENNReal.ofReal
          (n * (K * t ^ (-(2 * (p : ℝ))) + 2 * Real.exp (-t ^ 2 / 2))) :=
        Finset.sum_le_sum fun k _ => hSk k
    _ = ENNReal.ofReal (((2 * n ^ 4 + 1 : ℕ) : ℝ) *
          (n * (K * t ^ (-(2 * (p : ℝ))) + 2 * Real.exp (-t ^ 2 / 2)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (p := ((2 * n ^ 4 + 1 : ℕ) : ℝ)) (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal he4

/-- If `C ≤ n^{ξ-ξ'}` then `C n^ξ' (nη)^{-1/2} ≤ n^ξ (nη)^{-1/2}`. -/
private lemma localLaw_rate_absorb {n : ℕ} (hn : 0 < n) {C ξ ξ' η : ℝ}
    (h : C ≤ (n : ℝ) ^ (ξ - ξ')) :
    C * ((n : ℝ) ^ ξ' / Real.sqrt (n * η)) ≤ (n : ℝ) ^ ξ / Real.sqrt (n * η) := by
  have hN0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  calc C * (n : ℝ) ^ ξ' ≤ (n : ℝ) ^ (ξ - ξ') * (n : ℝ) ^ ξ' :=
        mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hN0.le _)
    _ = (n : ℝ) ^ ξ := by rw [← Real.rpow_add hN0]; congr 1; ring

/-- The exponent `ξ' = min ξ (δ/4) / 4` is positive, at most `ξ/4` and at most `δ/16`. -/
private lemma localLaw_xi {δ ξ : ℝ} (hδ : 0 < δ) (hξ : 0 < ξ) :
    0 < min ξ (δ / 4) / 4 ∧ min ξ (δ / 4) / 4 ≤ ξ / 4 ∧ min ξ (δ / 4) / 4 ≤ δ / 16 := by
  refine ⟨by have := lt_min hξ (by linarith : 0 < δ / 4); linarith,
    by have := min_le_left ξ (δ / 4); linarith,
    by have := min_le_right ξ (δ / 4); linarith⟩

/-- Entry law (G.3) [us:eq:weighted-entry-law] for diagonal `B` in the class of Lemma G.1
[us:lem:local-law]: with probability `≥ 1 - n^{-D}`, simultaneously for all `i`,
`|G_ii - (M_B)_ii| ≤ n^ξ (nη)^{-1/2} |(M_B)_ii|²`. -/
theorem localLaw_entry (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε δ ξ D : ℝ, 0 < ε → ε ≤ ε₀ → 0 < δ → 0 < ξ → 0 < D →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℂ) (E η : ℝ),
        DeformClass ε B → B.IsDiag → |E| ≤ 2 - κ₀ → (n : ℝ) ^ (-1 + δ) ≤ η → η ≤ Cstar →
        μ n 1 {ω | ∃ i, (n : ℝ) ^ ξ / Real.sqrt (n * η) * ‖MB B (E + η * Complex.I) i i‖ ^ 2 <
            ‖resolventMat (gueMat n ω - B) (E + η * Complex.I) i i -
              MB B (E + η * Complex.I) i i‖} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-D)) := by
  obtain ⟨ε₀, C, hε₀, hC0, hcore⟩ := localLaw_core κ₀ Cstar hκ₀ hκ₀' hC
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε δ ξ D hε hεε₀ hδ hξ hD
  obtain ⟨hξ'0, hξ'ξ, hξ'δ⟩ := localLaw_xi hδ hξ
  set ξ' : ℝ := min ξ (δ / 4) / 4 with hξ'
  obtain ⟨n₀, hn₀1, hn₀⟩ := hcore δ ξ' D hδ hξ'0 hξ'δ hD
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp
    (localLaw_rpow_ge_eventually (θ := ξ - ξ') (by linarith) C)
  refine ⟨max n₀ n₁, ?_⟩
  intro n hn B E η hcl hBd hE hηlow hηC
  have hn0 : 0 < n := lt_of_lt_of_le hn₀1 ((le_max_left _ _).trans hn)
  refine le_trans (measure_mono ?_) (hn₀ n ((le_max_left _ _).trans hn) B ε E η hBd hε.le hεε₀
    hcl hE hηlow hηC)
  intro ω hω
  obtain ⟨i, hi⟩ := hω
  rintro ⟨-, hall⟩
  have h1 := hall i
  have h2 := localLaw_rate_absorb (η := η) hn0 (hn₁ n ((le_max_right _ _).trans hn))
  have h3 : C * ((n : ℝ) ^ ξ' / Real.sqrt (n * η)) * ‖MB B (E + η * Complex.I) i i‖ ^ 2 ≤
      (n : ℝ) ^ ξ / Real.sqrt (n * η) * ‖MB B (E + η * Complex.I) i i‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  exact absurd (lt_of_lt_of_le hi (h1.trans h3)) (lt_irrefl _)

/-- Averaged law of Lemma G.1 [us:lem:local-law], first estimate of (G.1)
[us:eq:weighted-local-law], at rate `(nη)^{-1/2}`: `|⟨G⟩ - m_B| ≤ n^ξ (nη)^{-1/2}` with
probability `≥ 1 - n^{-D}`, `G = (V - E - B - iη)⁻¹`. -/
theorem localLaw_avg (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε δ ξ D : ℝ, 0 < ε → ε ≤ ε₀ → 0 < δ → 0 < ξ → 0 < D →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℂ) (E η : ℝ),
        DeformClass ε B → |E| ≤ 2 - κ₀ → (n : ℝ) ^ (-1 + δ) ≤ η → η ≤ Cstar →
        μ n 1 {ω | (n : ℝ) ^ ξ / Real.sqrt (n * η) <
            ‖ntr (resolventMat (gueMat n ω - B) (E + η * Complex.I)) -
              mB B (E + η * Complex.I)‖} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-D)) := by
  obtain ⟨ε₀, C, hε₀, hC0, hcore⟩ := localLaw_core κ₀ Cstar hκ₀ hκ₀' hC
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε δ ξ D hε hεε₀ hδ hξ hD
  obtain ⟨hξ'0, hξ'ξ, hξ'δ⟩ := localLaw_xi hδ hξ
  set ξ' : ℝ := min ξ (δ / 4) / 4 with hξ'
  obtain ⟨n₀, hn₀1, hn₀⟩ := hcore δ ξ' D hδ hξ'0 hξ'δ hD
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp
    (localLaw_rpow_ge_eventually (θ := ξ - ξ') (by linarith) C)
  refine ⟨max n₀ n₁, ?_⟩
  intro n hn B E η hcl hE hηlow hηC
  have hn0 : 0 < n := lt_of_lt_of_le hn₀1 ((le_max_left _ _).trans hn)
  have hN0 : (0 : ℝ) < n := by exact_mod_cast hn0
  have hη0 : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hηlow
  have hz : 0 < (E + η * Complex.I).im := by simpa using hη0
  obtain ⟨D', f, hD'd, hD'c, hfmp, hmB, hntr⟩ := localLaw_reduce hn0 hcl
  have h2 := localLaw_rate_absorb (η := η) hn0 (hn₁ n ((le_max_right _ _).trans hn))
  refine le_trans (measure_mono ?_) (le_trans (localLaw_preimage_le hfmp _)
    (hn₀ n ((le_max_left _ _).trans hn) D' ε E η hD'd hε.le hεε₀ hD'c hE hηlow hηC))
  intro ω hω h
  have h1 := h.1
  rw [hntr ω, ← hmB _ hz] at h1
  exact absurd hω (not_lt.mpr (h1.trans h2))

/-- Averaged comparison `Im ⟨G⟩ ≍ 1` from Lemma G.1 [us:lem:local-law], the form used for
(9.48) [us:eq:complement-spectrum]: `C⁻¹ ≤ Im ⟨G⟩ ≤ C` with probability `≥ 1 - n^{-D}`. -/
theorem localLaw_avg_asymp (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 1 ≤ C ∧ ∀ ε δ D : ℝ, 0 < ε → ε ≤ ε₀ → 0 < δ → 0 < D →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℂ) (E η : ℝ),
        DeformClass ε B → |E| ≤ 2 - κ₀ → (n : ℝ) ^ (-1 + δ) ≤ η → η ≤ Cstar →
        μ n 1 {ω | ¬ (C⁻¹ ≤ (ntr (resolventMat (gueMat n ω - B) (E + η * Complex.I))).im ∧
            (ntr (resolventMat (gueMat n ω - B) (E + η * Complex.I))).im ≤ C)} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-D)) := by
  obtain ⟨ε₁, Cp, hε₁, hCp1, hprof⟩ := deformed_profile κ₀ Cstar hκ₀ hκ₀' hC
  obtain ⟨ε₂, C, hε₂, hC0, hcore⟩ := localLaw_core κ₀ Cstar hκ₀ hκ₀' hC
  have hCp0 : 0 < Cp := by linarith
  refine ⟨min ε₁ ε₂, 2 * Cp, lt_min hε₁ hε₂, by linarith, ?_⟩
  intro ε δ D hε hεε₀ hδ hD
  have hξ'0 : 0 < δ / 16 := by positivity
  obtain ⟨n₀, hn₀1, hn₀⟩ := hcore δ (δ / 16) D hδ hξ'0 le_rfl hD
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp
    (localLaw_rpow_neg_le_eventually (θ := 7 * δ / 16) (by positivity)
      (c := 1 / (2 * Cp * C)) (by positivity))
  refine ⟨max n₀ n₁, ?_⟩
  intro n hn B E η hcl hE hηlow hηC
  have hn0 : 0 < n := lt_of_lt_of_le hn₀1 ((le_max_left _ _).trans hn)
  have hN0 : (0 : ℝ) < n := by exact_mod_cast hn0
  have hη0 : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hηlow
  have hz : 0 < (E + η * Complex.I).im := by simpa using hη0
  have : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  obtain ⟨hlo, hhi, -⟩ := hprof (Fin n) B ε E η hε.le (hεε₀.trans (min_le_left _ _)) hcl hE hη0
    hηC
  obtain ⟨D', f, hD'd, hD'c, hfmp, hmB, hntr⟩ := localLaw_reduce hn0 hcl
  have hrate := localLaw_rate_le (η := η) hn0 (le_refl (δ / 16)) hηlow
  have hsmall : C * ((n : ℝ) ^ (δ / 16) / Real.sqrt (n * η)) ≤ (2 * Cp)⁻¹ := by
    calc C * ((n : ℝ) ^ (δ / 16) / Real.sqrt (n * η)) ≤ C * (1 / (2 * Cp * C)) := by
          exact mul_le_mul_of_nonneg_left
            (hrate.trans (hn₁ n ((le_max_right _ _).trans hn))) hC0.le
      _ = (2 * Cp)⁻¹ := by field_simp
  refine le_trans (measure_mono ?_) (le_trans (localLaw_preimage_le hfmp _)
    (hn₀ n ((le_max_left _ _).trans hn) D' ε E η hD'd hε.le
      (hεε₀.trans (min_le_right _ _)) hD'c hE hηlow hηC))
  intro ω hω h
  apply hω
  have h1 := h.1
  rw [hntr ω, ← hmB _ hz] at h1
  have h2 : ‖ntr (resolventMat (gueMat n ω - B) (E + η * Complex.I)) -
      mB B (E + η * Complex.I)‖ ≤ (2 * Cp)⁻¹ := h1.trans hsmall
  have h3 := (Complex.abs_im_le_norm _).trans h2
  rw [Complex.sub_im] at h3
  have hw2 : Cp⁻¹ = 2 * (2 * Cp)⁻¹ := by field_simp
  have hw1 : (2 * Cp)⁻¹ ≤ Cp := by
    have : (2 * Cp)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith
  have h4 := abs_le.mp h3
  constructor
  · linarith [h4.1]
  · linarith [h4.2]


end LSBA
