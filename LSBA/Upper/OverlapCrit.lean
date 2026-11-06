import LSBA.Upper.RetainedProb
import LSBA.Upper.AllowBound
import LSBA.Upper.PrepGood
import LSBA.Upper.CutLevels
import LSBA.Spectral.InvImageCompress
import LSBA.Spectral.InvImageMeas

/-!
# The small overlap in regime (ii)

(9.65) [su:eq:construction-overlap-goals], regime (ii) (Section 9.4.1
[su:sec:retained-geometry]), where `P = 1`. Fix prepared data `(R_4, v_4)` satisfying (9.7)
[nc:eq:prepared] and the parameters of (9.62) [nc:eq:parameters]. Split `g² R_4` and
`g² R←_6` spectrally at `W^{-θ}`; the large pieces have ranks at most `W^{3θ}` by (9.58)
[us:eq:wegner] and the small pieces have total norm at most `2 W^{-θ}`. Corollary 9.7
[nc:lem:compression] with `B = g² R_4 + g² R←_6`, `U = ran A_>*` and `d = ⌈W^{12θ}⌉`, the rank
bound (9.63) [nc:eq:dimension] and `ran Q = R̃ U` give (9.64) [nc:eq:geometry]; in the form used
by the cutoff, `‖Q v_4‖² ≤ W^{-1+14θ} ‖v_4‖²` except with probability at most any fixed `η > 0`
once `W` is large, uniformly in `0 < g ≤ W^{-1/2+θ/2}`, `|E| ≤ 2 - κ₀` and the prepared data.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### The right-cavity chain: dependence on blocks, symmetry and measurability -/

/-- A block of `blockSeq` other than block `a` is unchanged when the sample changes only on
block `a`. -/
private lemma overlapCrit_blockSeq_congr {W q : ℕ} {a : Fin q} {ω ω' : Ω W q}
    (h : ∀ x, x.1 ≠ a → ω x = ω' x) {k : ℕ} (hk : k ≠ a.val) :
    blockSeq W q ω k = blockSeq W q ω' k := by
  unfold blockSeq
  split_ifs with hkq
  · have hne : (⟨k, hkq⟩ : Fin q) ≠ a := fun e => hk (by rw [← e])
    have e : ∀ α β : Fin W, ω (⟨k, hkq⟩, α, β) = ω' (⟨k, hkq⟩, α, β) := fun α β => h _ hne
    ext α β
    simp only [gueBlock, Matrix.of_apply, e]
  · rfl

/-- `R←_{q-1-m}` depends only on the blocks `V_{q-1-m}, …, V_{q-1}`. -/
private lemma overlapCrit_cavR_congr {W q : ℕ} (g E : ℝ) {ω ω' : Ω W q} :
    ∀ m : ℕ, (∀ k, q - 2 - m ≤ k → blockSeq W q ω k = blockSeq W q ω' k) →
      cavR W g E q ω m = cavR W g E q ω' m
  | 0, h => by simp only [cavR, h (q - 2) (by omega)]
  | m + 1, h => by
    simp only [cavR]
    rw [h (q - 3 - m) (by omega), overlapCrit_cavR_congr g E m (fun k hk => h k (by omega))]

/-- `R←_{q-1} ⋯ R←_{q-m}` depends only on the blocks `V_{q-m}, …, V_{q-1}`. -/
private lemma overlapCrit_cavProd_congr {W q : ℕ} (g E : ℝ) {ω ω' : Ω W q} :
    ∀ m : ℕ, (∀ k, q - 1 - m ≤ k → blockSeq W q ω k = blockSeq W q ω' k) →
      cavProd W g E q ω m = cavProd W g E q ω' m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [cavProd]
    rw [overlapCrit_cavProd_congr g E m (fun k hk => h k (by omega)),
      overlapCrit_cavR_congr g E m (fun k hk => h k (by omega))]

/-- Every block of `blockSeq` is Hermitian. -/
private lemma overlapCrit_blockSeq_herm {W q : ℕ} (ω : Ω W q) (k : ℕ) :
    (blockSeq W q ω k).IsHermitian := by
  unfold blockSeq
  split_ifs
  · exact gueBlock_isHermitian W q ω _
  · exact Matrix.isHermitian_zero

/-- A real multiple of a Hermitian matrix is Hermitian. -/
private lemma overlapCrit_smul_herm {W : ℕ} (c : ℝ) {A : Matrix (Fin W) (Fin W) ℂ}
    (hA : A.IsHermitian) : ((c : ℂ) • A).IsHermitian := by
  have hc : IsSelfAdjoint (c : ℂ) := by
    rw [isSelfAdjoint_iff]
    simp
  exact hA.smul hc

/-- `g² A` is Hermitian for Hermitian `A`. -/
private lemma overlapCrit_sq_smul_herm {W : ℕ} (g : ℝ) {A : Matrix (Fin W) (Fin W) ℂ}
    (hA : A.IsHermitian) : (((g : ℂ) ^ 2) • A).IsHermitian := by
  have := overlapCrit_smul_herm (g ^ 2) hA
  simpa using this

/-- Every right-cavity inverse is Hermitian. -/
private lemma overlapCrit_cavR_herm {W q : ℕ} (g E : ℝ) (ω : Ω W q) :
    ∀ m, (cavR W g E q ω m).IsHermitian
  | 0 => by
    simp only [cavR]
    exact ((overlapCrit_blockSeq_herm ω _).sub
      (overlapCrit_smul_herm E Matrix.isHermitian_one)).inv
  | m + 1 => by
    simp only [cavR]
    exact (((overlapCrit_blockSeq_herm ω _).sub
      (overlapCrit_smul_herm E Matrix.isHermitian_one)).sub
      (overlapCrit_sq_smul_herm g (overlapCrit_cavR_herm g E ω m))).inv

/-- The matrix inverse is Borel. -/
private lemma overlapCrit_meas_inv {W : ℕ} :
    Measurable (fun M : Matrix (Fin W) (Fin W) ℂ => M⁻¹) := by
  have h : (fun M : Matrix (Fin W) (Fin W) ℂ => M⁻¹) = fun M => Ring.inverse M.det • M.adjugate :=
    funext Matrix.inv_def
  rw [h, Ring.inverse_eq_inv']
  exact ((Continuous.matrix_det continuous_id).measurable.inv).smul
    (Continuous.matrix_adjugate continuous_id).measurable

/-- Every block of `blockSeq` is measurable in the sample. -/
private lemma overlapCrit_meas_blockSeq {W q : ℕ} (k : ℕ) :
    Measurable fun ω : Ω W q => blockSeq W q ω k := by
  by_cases hk : k < q
  · simp only [blockSeq, hk, ↓reduceDIte]
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    unfold gueBlock
    simp only [Matrix.of_apply]
    split_ifs <;> fun_prop
  · simp only [blockSeq, hk, ↓reduceDIte]
    exact measurable_const

/-- Every right-cavity inverse is measurable in the sample. -/
private lemma overlapCrit_meas_cavR {W q : ℕ} (g E : ℝ) :
    ∀ m, Measurable fun ω : Ω W q => cavR W g E q ω m
  | 0 => by
    simp only [cavR]
    exact overlapCrit_meas_inv.comp ((overlapCrit_meas_blockSeq _).sub measurable_const)
  | m + 1 => by
    simp only [cavR]
    exact overlapCrit_meas_inv.comp (((overlapCrit_meas_blockSeq _).sub measurable_const).sub
      (show Measurable fun ω : Ω W q => ((g : ℂ) ^ 2) • cavR W g E q ω m from
        (overlapCrit_meas_cavR (W := W) (q := q) g E m).const_smul ((g : ℂ) ^ 2)))

/-- Every partial product of right-cavity inverses is measurable in the sample. -/
private lemma overlapCrit_meas_cavProd {W q : ℕ} (g E : ℝ) :
    ∀ m, Measurable fun ω : Ω W q => cavProd W g E q ω m
  | 0 => by
    simp only [cavProd]
    exact measurable_const
  | m + 1 => by
    simp only [cavProd]
    exact (overlapCrit_meas_cavProd g E m).mul (overlapCrit_meas_cavR g E m)

/-- `R←_6 = (V_6 - E - g² R←_7)⁻¹`. -/
private lemma overlapCrit_cavR_six {W q : ℕ} (hq : 8 ≤ q) (g E : ℝ) (ω : Ω W q) :
    cavR W g E q ω (q - 7) = (gueBlock W q ω ⟨5, by omega⟩ - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • cavR W g E q ω (q - 8))⁻¹ := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 8 := ⟨q - 8, by omega⟩
  have e1 : m + 8 - 7 = (m + 8 - 8) + 1 := by omega
  have e2 : m + 8 - 3 - (m + 8 - 8) = 5 := by omega
  rw [e1, cavR, e2]
  simp only [blockSeq, show 5 < m + 8 by omega, ↓reduceDIte]

/-- The data `1_{(t², ∞)}(A* A)` and `1_{|·| > s}(g² R←)` are measurable in the sample. -/
private lemma overlapCrit_meas_data {W q : ℕ} (m k : ℕ) (g E t s : ℝ) :
    (Measurable fun ω : Ω W q => specProj ((cavProd W g E q ω m)ᴴ * cavProd W g E q ω m)
      (Set.Ioi (t ^ 2))) ∧
    Measurable fun ω : Ω W q => specProj (((g : ℂ) ^ 2) • cavR W g E q ω k) {x | s < |x|} := by
  have hA : Measurable fun ω : Ω W q => (cavProd W g E q ω m)ᴴ * cavProd W g E q ω m :=
    (continuous_star.measurable.comp (overlapCrit_meas_cavProd g E m)).mul
      (overlapCrit_meas_cavProd g E m)
  have hR : Measurable fun ω : Ω W q => ((g : ℂ) ^ 2) • cavR W g E q ω k :=
    (overlapCrit_meas_cavR (W := W) (q := q) g E k).const_smul ((g : ℂ) ^ 2)
  refine ⟨?_, ?_⟩
  · have e : ∀ ω : Ω W q, specProj ((cavProd W g E q ω m)ᴴ * cavProd W g E q ω m)
        (Set.Ioi (t ^ 2)) = 1 - specProj ((cavProd W g E q ω m)ᴴ * cavProd W g E q ω m)
          (Set.Iic (t ^ 2)) := by
      intro ω
      have h := (specProj_add_compl (Matrix.isHermitian_conjTranspose_mul_self
        (cavProd W g E q ω m)) (Set.Iic (t ^ 2))).1
      rw [Set.compl_Iic] at h
      rw [← h]
      abel
    simp only [e]
    exact measurable_const.sub ((measurable_specProj isClosed_Iic).comp hA)
  · have hc : {x : ℝ | |x| ≤ s}ᶜ = {x | s < |x|} := by
      ext x
      simp [not_le]
    have e : ∀ ω : Ω W q, specProj (((g : ℂ) ^ 2) • cavR W g E q ω k) {x | s < |x|} =
        1 - specProj (((g : ℂ) ^ 2) • cavR W g E q ω k) {x | |x| ≤ s} := by
      intro ω
      have h := (specProj_add_compl (overlapCrit_sq_smul_herm g
        (overlapCrit_cavR_herm g E ω k)) {x : ℝ | |x| ≤ s}).1
      rw [hc] at h
      rw [← h]
      abel
    simp only [e]
    exact measurable_const.sub
      ((measurable_specProj (isClosed_le continuous_abs continuous_const)).comp hR)

/-! ### Linear algebra and the deterministic step -/

/-- The rank of a sum is at most the sum of the ranks. -/
private lemma overlapCrit_rank_add_le {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- `‖x‖₂² = Σ_i ‖x_i‖²`. -/
private lemma overlapCrit_sq_l2Norm {W : ℕ} (x : Fin W → ℂ) :
    l2Norm x ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)

/-- The row matrix `v*` sends `x` to `v* x`: `‖v* x‖₂² = |v* x|²`. -/
private lemma overlapCrit_row {W : ℕ} (v x : Fin W → ℂ) :
    l2Norm ((Matrix.of fun (_ : Fin 1) (j : Fin W) => star (v j)) *ᵥ x) ^ 2 =
      ‖star v ⬝ᵥ x‖ ^ 2 := by
  rw [overlapCrit_sq_l2Norm, Fin.sum_univ_one]
  rfl

/-- The deterministic step of Section 9.4.1 [su:sec:retained-geometry]: if `|v* x|² ≤ K ‖x‖²` for
every `x` with `(1 - 1_{(t²,∞)}(A* A)) (V_5 - E - g² R - g² R←_6) x = 0`, then
`‖Q v‖² ≤ K ≤ L ‖v‖²`; where `R̃` is singular, `Q = 0`. -/
private lemma overlapCrit_det {W q : ℕ} (hq : 7 ≤ q) {g E t K L : ℝ}
    (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) (v : Fin W → ℂ) (hK0 : 0 ≤ K)
    (hKL : K ≤ L * l2Norm v ^ 2) (hL : 0 ≤ L)
    (hG : ∀ x : Fin W → ℂ, (1 - retSpec W g E q t ω) *ᵥ ((blockSeq W q ω 4 - (E : ℂ) • 1 -
        ((g : ℂ) ^ 2) • R - ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) *ᵥ x) = 0 →
      ‖star v ⬝ᵥ x‖ ^ 2 ≤ K * l2Norm x ^ 2) :
    ∑ i, ‖(retProj W g E q R t ω *ᵥ v) i‖ ^ 2 ≤ L * ∑ i, ‖v i‖ ^ 2 := by
  by_cases hT : IsUnit (cavRes W g E q R ω)
  · obtain ⟨hQh, hQQ, -⟩ := trace_retProj (g := g) (E := E) R t ω hT
    have h := sq_l2Norm_proj_le hQh hQQ v hK0
      (fun x hx => hG x (retProj_mem_invImage hq R t ω hT x hx))
    rw [← overlapCrit_sq_l2Norm, ← overlapCrit_sq_l2Norm]
    exact h.trans hKL
  · have h0 : cavRes W g E q R ω = 0 := by
      unfold cavRes at hT ⊢
      refine Matrix.nonsing_inv_apply_not_isUnit _ fun h => hT ?_
      exact Matrix.isUnit_nonsing_inv_iff.2 ((Matrix.isUnit_iff_isUnit_det _).2 h)
    have hQ : retProj W g E q R t ω = 0 := by
      simp only [retProj, flagProj, h0, Matrix.zero_mul]
    simp only [hQ, Matrix.zero_mulVec, Pi.zero_apply, norm_zero]
    norm_num
    exact mul_nonneg hL (Finset.sum_nonneg fun i _ => by positivity)

/-! ### Powers of `W` -/

/-- Eventually in `W`, `K ≤ W^c` for `c > 0`. -/
private lemma overlapCrit_ev_le (K c : ℝ) (hc : 0 < c) :
    ∀ᶠ W : ℕ in Filter.atTop, K ≤ (W : ℝ) ^ c :=
  ((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K

/-- Eventually in `W`, `W^{-c} ≤ ε` for `c, ε > 0`. -/
private lemma overlapCrit_ev_neg_le (ε c : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ W : ℕ in Filter.atTop, (W : ℝ) ^ (-c) ≤ ε :=
  ((tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_le_nhds hε)

/-- The rank row of (9.63) [nc:eq:dimension]: `2 t^{-p} W^{1+θ/4} ≤ 2 W^{9θ}` at the parameters
(9.62) [nc:eq:parameters], with `t = W^{-30+(1-2θ)(q-6)/2}`. -/
private lemma overlapCrit_rank_row {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 1 / 100) {W : ℕ}
    (hW : 1 ≤ W) :
    2 * (levelsCrit W θ 0).t ^ (-pCrit θ) * (W : ℝ) ^ (1 + θ / 4) ≤ 2 * (W : ℝ) ^ (9 * θ) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈10 / θ⌉₊ := ⟨_, rfl⟩
  have hqR : (qCrit θ : ℝ) = 5 + N := by
    rw [hN]
    simp only [qCrit]
    push_cast
    ring
  have hp : pCrit θ = 2 * (1 - θ / 4) / (N : ℝ) := by rw [hN]; rfl
  have hNge : 10 / θ ≤ (N : ℝ) := by rw [hN]; exact Nat.le_ceil _
  have hNθ : 10 ≤ (N : ℝ) * θ := by
    have := mul_le_mul_of_nonneg_right hNge hθ.le
    rwa [div_mul_cancel₀ _ hθ.ne'] at this
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < 10 / θ := by positivity
    linarith
  have hw1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hw0 : (0 : ℝ) < W := by linarith
  set τ : ℝ := -30 + (1 - 2 * θ) * ((qCrit θ : ℝ) - 6) / 2 with hτ
  have ht : (levelsCrit W θ 0).t = (W : ℝ) ^ τ := rfl
  have hexp : τ * -pCrit θ + (1 + θ / 4) ≤ 9 * θ := by
    rw [hp, hτ, hqR]
    rw [show (-30 + (1 - 2 * θ) * (5 + (N : ℝ) - 6) / 2) * -(2 * (1 - θ / 4) / (N : ℝ)) +
        (1 + θ / 4) = ((60 - (1 - 2 * θ) * ((N : ℝ) - 1)) * (1 - θ / 4) + (1 + θ / 4) * N) / N by
      field_simp
      ring]
    rw [div_le_iff₀ hN0]
    nlinarith [mul_nonneg hθ.le (mul_nonneg hθ.le hN0.le), mul_nonneg hθ.le hθ.le]
  rw [ht, ← Real.rpow_mul hw0.le, mul_assoc, ← Real.rpow_add hw0]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hw1 hexp) (by norm_num)

/-- `d = ⌈W^{12θ}⌉ ≤ ε₀ W` once `W^{-(1-12θ)} ≤ ε₀/2` (window of Corollary 9.7
[nc:lem:compression]). -/
private lemma overlapCrit_d_le {W : ℕ} {θ ε₀ : ℝ} (hθ : 0 < θ) (hw1 : 1 ≤ (W : ℝ))
    (h : (W : ℝ) ^ (-(1 - 12 * θ)) ≤ ε₀ / 2) :
    (⌈(W : ℝ) ^ (12 * θ)⌉₊ : ℝ) ≤ ε₀ * W := by
  have hw0 : (0 : ℝ) < W := by linarith
  have h12 : 1 ≤ (W : ℝ) ^ (12 * θ) := Real.one_le_rpow hw1 (by positivity)
  have hd2 : (⌈(W : ℝ) ^ (12 * θ)⌉₊ : ℝ) < (W : ℝ) ^ (12 * θ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have e : (W : ℝ) ^ (12 * θ) = (W : ℝ) ^ (-(1 - 12 * θ)) * W := by
    rw [← Real.rpow_add_one hw0.ne']
    congr 1
    ring
  have := mul_le_mul_of_nonneg_right h hw0.le
  linarith

/-- The overlap row of (9.64) [nc:eq:geometry]: `C d / W ≤ W^{-1+14θ}` for `d = ⌈W^{12θ}⌉` once
`2C ≤ W^{2θ}`. -/
private lemma overlapCrit_KL {W : ℕ} {θ C : ℝ} (hθ : 0 < θ) (hw1 : 1 ≤ (W : ℝ))
    (h : 2 * C ≤ (W : ℝ) ^ (2 * θ)) :
    C * ((⌈(W : ℝ) ^ (12 * θ)⌉₊ : ℝ) / W) ≤ (W : ℝ) ^ (-1 + 14 * θ) := by
  have hw0 : (0 : ℝ) < W := by linarith
  have h12 : 1 ≤ (W : ℝ) ^ (12 * θ) := Real.one_le_rpow hw1 (by positivity)
  have hd2 : (⌈(W : ℝ) ^ (12 * θ)⌉₊ : ℝ) < (W : ℝ) ^ (12 * θ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hC : C ≤ (W : ℝ) ^ (2 * θ) / 2 := by linarith
  rcases le_or_gt C 0 with hC0 | hC0
  · have : C * ((⌈(W : ℝ) ^ (12 * θ)⌉₊ : ℝ) / W) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hC0 (by positivity)
    exact this.trans (by positivity)
  rw [← mul_div_assoc, div_le_iff₀ hw0, ← Real.rpow_add_one hw0.ne',
    show -1 + 14 * θ + 1 = 2 * θ + 12 * θ by ring, Real.rpow_add hw0]
  have h1 : C * (⌈(W : ℝ) ^ (12 * θ)⌉₊ : ℝ) ≤ C * (2 * (W : ℝ) ^ (12 * θ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hC0.le
  have h2 : C * (2 * (W : ℝ) ^ (12 * θ)) ≤ (W : ℝ) ^ (2 * θ) / 2 * (2 * (W : ℝ) ^ (12 * θ)) :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  linarith

/-- The dimension row (9.63) [nc:eq:dimension] with the two large pieces of (9.58)
[us:eq:wegner]: `L + 2 W^{3θ} + 1 ≤ ⌈W^{12θ}⌉` for `L ≤ 2 W^{9θ}` once `W^{3θ} ≥ 5`. -/
private lemma overlapCrit_dim {W : ℕ} {θ L : ℝ} (hθ : 0 < θ) (hw1 : 1 ≤ (W : ℝ))
    (hL : L ≤ 2 * (W : ℝ) ^ (9 * θ)) (h5 : 5 ≤ (W : ℝ) ^ (3 * θ)) :
    L + 2 * (W : ℝ) ^ (3 * θ) + 1 ≤ (⌈(W : ℝ) ^ (12 * θ)⌉₊ : ℝ) := by
  have hw0 : (0 : ℝ) < W := by linarith
  have h39 : (W : ℝ) ^ (3 * θ) ≤ (W : ℝ) ^ (9 * θ) :=
    Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)
  have h19 : 1 ≤ (W : ℝ) ^ (9 * θ) := Real.one_le_rpow hw1 (by positivity)
  have h912 : (W : ℝ) ^ (12 * θ) = (W : ℝ) ^ (3 * θ) * (W : ℝ) ^ (9 * θ) := by
    rw [← Real.rpow_add hw0]
    congr 1
    ring
  have hd1 : (W : ℝ) ^ (12 * θ) ≤ (⌈(W : ℝ) ^ (12 * θ)⌉₊ : ℝ) := Nat.le_ceil _
  have := mul_le_mul_of_nonneg_right h5 (by positivity : (0 : ℝ) ≤ (W : ℝ) ^ (9 * θ))
  linarith

/-- The failure of (9.53) [su:eq:retained-rank-moment]: `C (W^{-δ₀} + √g) ≤ η/3` for
`g ≤ W^{-1/4}` once `W^{-1/4} ≤ (η/(6C))²` and `W^{-δ₀} ≤ η/(6C)`. -/
private lemma overlapCrit_fail_rank {W : ℕ} {g C η δ₀ : ℝ} (hC : 0 < C) (hη : 0 < η)
    (hg : g ≤ (W : ℝ) ^ (-(1 / 4 : ℝ))) (h1 : (W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (η / (6 * C)) ^ 2)
    (h2 : (W : ℝ) ^ (-δ₀) ≤ η / (6 * C)) :
    C * ((W : ℝ) ^ (-δ₀) + Real.sqrt g) ≤ η / 3 := by
  have hsq : Real.sqrt g ≤ η / (6 * C) := by
    have := Real.sqrt_le_sqrt (hg.trans h1)
    rwa [Real.sqrt_sq (by positivity)] at this
  have e : C * (η / (6 * C)) = η / 6 := by field_simp
  have := mul_le_mul_of_nonneg_left (add_le_add h2 hsq) hC.le
  linarith

/-- The failure of (9.58) [us:eq:wegner] for `g² R←_6` at `s = W^{-θ}`, `T = W^{3θ}`:
`2 C W g² / (s T) ≤ η/3` for `g ≤ W^{-1/2+θ/2}` once `W^{-θ} ≤ η/(6C)`. -/
private lemma overlapCrit_fail_count {W : ℕ} {θ g C η : ℝ} (hw1 : 1 ≤ (W : ℝ)) (hg : 0 < g)
    (hgW : g ≤ (W : ℝ) ^ (-(1 / 2 : ℝ) + θ / 2)) (hC : 0 < C)
    (h : (W : ℝ) ^ (-θ) ≤ η / (6 * C)) :
    2 * C * W * g ^ 2 / ((W : ℝ) ^ (-θ) * (W : ℝ) ^ (3 * θ)) ≤ η / 3 := by
  have hw0 : (0 : ℝ) < W := by linarith
  have hsT : (W : ℝ) ^ (-θ) * (W : ℝ) ^ (3 * θ) = (W : ℝ) ^ (2 * θ) := by
    rw [← Real.rpow_add hw0]
    congr 1
    ring
  have hg2 : g ^ 2 ≤ (W : ℝ) ^ (-1 + θ) := by
    have h := pow_le_pow_left₀ hg.le hgW 2
    rwa [← Real.rpow_mul_natCast hw0.le, show (-(1 / 2 : ℝ) + θ / 2) * ((2 : ℕ) : ℝ) =
      -1 + θ by push_cast; ring] at h
  have hWg : (W : ℝ) * g ^ 2 ≤ (W : ℝ) ^ (-θ) * (W : ℝ) ^ (2 * θ) := by
    calc (W : ℝ) * g ^ 2 ≤ (W : ℝ) * (W : ℝ) ^ (-1 + θ) :=
          mul_le_mul_of_nonneg_left hg2 hw0.le
      _ = (W : ℝ) ^ (-θ) * (W : ℝ) ^ (2 * θ) := by
          rw [mul_comm, ← Real.rpow_add_one hw0.ne', ← Real.rpow_add hw0]
          congr 1
          ring
  have hpos : 0 < (W : ℝ) ^ (2 * θ) := by positivity
  rw [hsT, div_le_iff₀ hpos]
  have e : 2 * C * (η / (6 * C)) = η / 3 := by field_simp; ring
  have h2C : 0 ≤ 2 * C := by positivity
  have h1 := mul_le_mul_of_nonneg_left h h2C
  calc 2 * C * W * g ^ 2 = 2 * C * (W * g ^ 2) := by ring
    _ ≤ 2 * C * ((W : ℝ) ^ (-θ) * (W : ℝ) ^ (2 * θ)) := mul_le_mul_of_nonneg_left hWg h2C
    _ = 2 * C * (W : ℝ) ^ (-θ) * (W : ℝ) ^ (2 * θ) := by ring
    _ ≤ η / 3 * (W : ℝ) ^ (2 * θ) := by
        rw [← e]
        exact mul_le_mul_of_nonneg_right h1 hpos.le

/-- The failure of Corollary 9.7 [nc:lem:compression] at `D = 1`, `d = ⌈W^{12θ}⌉`:
`W^{-1} + C e^{-c d} ≤ η/3` once `W^{-1} ≤ η/6` and `W^{12θ} ≥ 6C/(cη)`. -/
private lemma overlapCrit_fail_compress {W : ℕ} {θ C c η : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hη : 0 < η) (h1 : (W : ℝ) ^ (-(1 : ℝ)) ≤ η / 6)
    (h2 : 6 * C / (c * η) ≤ (W : ℝ) ^ (12 * θ)) :
    (W : ℝ) ^ (-(1 : ℝ)) + C * Real.exp (-(c * ⌈(W : ℝ) ^ (12 * θ)⌉₊)) ≤ η / 3 := by
  have hcd : 6 * C / η ≤ c * ⌈(W : ℝ) ^ (12 * θ)⌉₊ := by
    have := mul_le_mul_of_nonneg_left (h2.trans (Nat.le_ceil _)) hc.le
    have e : c * (6 * C / (c * η)) = 6 * C / η := by field_simp
    linarith
  have hex : 6 * C / η ≤ Real.exp (c * ⌈(W : ℝ) ^ (12 * θ)⌉₊) := by
    have := Real.add_one_le_exp (c * ⌈(W : ℝ) ^ (12 * θ)⌉₊)
    linarith
  have hexp : C * Real.exp (-(c * ⌈(W : ℝ) ^ (12 * θ)⌉₊)) ≤ η / 6 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    have e : η / 6 * (6 * C / η) = C := by field_simp
    have := mul_le_mul_of_nonneg_left hex (by positivity : (0 : ℝ) ≤ η / 6)
    linarith
  linarith

/-- The splitting of Section 9.4.1 [su:sec:retained-geometry]: `g² R + g² R←_6 = B_s + B_b` with
`‖B_s‖ ≤ 2s ≤ ε₀` and `rank B_b + Tr P_U + 1 ≤ d`, when both large pieces `|·| > s` have at most
`T` eigenvalues and `Tr P_U ≤ L`, `L + 2T + 1 ≤ d`. -/
private lemma overlapCrit_split {W d : ℕ} {g s ε₀ T L : ℝ}
    {R Rc Pu : Matrix (Fin W) (Fin W) ℂ} (hRH : R.IsHermitian) (hRcH : Rc.IsHermitian)
    (hs : 0 ≤ s) (hsε : s ≤ ε₀ / 2)
    (hR : (countIn (((g : ℂ) ^ 2) • R) {x | s < |x|} : ℝ) ≤ T)
    (hRc : (specProj (((g : ℂ) ^ 2) • Rc) {x | s < |x|}).trace.re ≤ T)
    (hPu : Pu.trace.re ≤ L) (hd : L + 2 * T + 1 ≤ d) :
    ∃ Bs Bb : Matrix (Fin W) (Fin W) ℂ, ((g : ℂ) ^ 2) • R + ((g : ℂ) ^ 2) • Rc = Bs + Bb ∧
      ‖Bs‖ ≤ ε₀ ∧ (Bb.rank : ℝ) + Pu.trace.re + 1 ≤ d := by
  have hgR : (((g : ℂ) ^ 2) • R).IsHermitian := overlapCrit_sq_smul_herm g hRH
  have hgRc : (((g : ℂ) ^ 2) • Rc).IsHermitian := overlapCrit_sq_smul_herm g hRcH
  have hcomp : {x : ℝ | |x| ≤ s}ᶜ = {x | s < |x|} := by
    ext x
    simp [not_le]
  have e1 := (specProj_add_compl hgR {x : ℝ | |x| ≤ s}).1
  have e2 := (specProj_add_compl hgRc {x : ℝ | |x| ≤ s}).1
  rw [hcomp] at e1 e2
  refine ⟨((g : ℂ) ^ 2) • R * specProj (((g : ℂ) ^ 2) • R) {x | |x| ≤ s} +
      ((g : ℂ) ^ 2) • Rc * specProj (((g : ℂ) ^ 2) • Rc) {x | |x| ≤ s},
    ((g : ℂ) ^ 2) • R * specProj (((g : ℂ) ^ 2) • R) {x | s < |x|} +
      ((g : ℂ) ^ 2) • Rc * specProj (((g : ℂ) ^ 2) • Rc) {x | s < |x|}, ?_, ?_, ?_⟩
  · calc ((g : ℂ) ^ 2) • R + ((g : ℂ) ^ 2) • Rc =
        ((g : ℂ) ^ 2) • R * (specProj (((g : ℂ) ^ 2) • R) {x | |x| ≤ s} +
          specProj (((g : ℂ) ^ 2) • R) {x | s < |x|}) + ((g : ℂ) ^ 2) • Rc *
          (specProj (((g : ℂ) ^ 2) • Rc) {x | |x| ≤ s} +
            specProj (((g : ℂ) ^ 2) • Rc) {x | s < |x|}) := by
          rw [e1, e2, Matrix.mul_one, Matrix.mul_one]
      _ = _ := by
          simp only [Matrix.mul_add]
          abel
  · have hS0I : {x : ℝ | |x| ≤ s} ⊆ Set.Icc (-s) s := fun x hx => abs_le.1 hx
    have n1 := (norm_mul_specProj_le hgR hs hS0I 0 le_rfl).1
    have n2 := (norm_mul_specProj_le hgRc hs hS0I 0 le_rfl).1
    exact (norm_add_le _ _).trans (by linarith)
  · have r1 := (overlapCrit_rank_add_le
      (((g : ℂ) ^ 2) • R * specProj (((g : ℂ) ^ 2) • R) {x | s < |x|})
      (((g : ℂ) ^ 2) • Rc * specProj (((g : ℂ) ^ 2) • Rc) {x | s < |x|})).trans
      (add_le_add (Matrix.rank_mul_le_right _ _) (Matrix.rank_mul_le_right _ _))
    rw [rank_specProj hgR, rank_specProj hgRc] at r1
    rw [(specProj_spec hgRc _).2.2.2, Complex.natCast_re] at hRc
    have r1' : (((((g : ℂ) ^ 2) • R * specProj (((g : ℂ) ^ 2) • R) {x | s < |x|} +
        ((g : ℂ) ^ 2) • Rc * specProj (((g : ℂ) ^ 2) • Rc) {x | s < |x|}).rank : ℕ) : ℝ) ≤
        (countIn (((g : ℂ) ^ 2) • R) {x | s < |x|} : ℝ) +
          (countIn (((g : ℂ) ^ 2) • Rc) {x | s < |x|} : ℝ) := by exact_mod_cast r1
    linarith

/-- (9.65) [su:eq:construction-overlap-goals] in regime (ii), (9.64) [nc:eq:geometry] with
(9.63) [nc:eq:dimension], at fixed prepared data, in the form of the overlap cut (9.80)
[nc:eq:sourcecuts]. -/
theorem overlap_crit (κ₀ θ : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hθ : 0 < θ)
    (hθ' : θ ≤ 1 / 100) (η : ℝ) (hη : 0 < η) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, 0 < g → g ≤ (W : ℝ) ^ (-(1 / 2 : ℝ) + θ / 2) →
      ∀ E : ℝ, |E| ≤ 2 - κ₀ → ∀ (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ),
        (R, v) ∈ PrepGoodCrit W g θ →
        μ W (qCrit θ) {ω | ¬ (∑ i, ‖(retProj W g E (qCrit θ) R (levelsCrit W θ 0).t ω *ᵥ v) i‖ ^ 2 ≤
            (levelsCrit W θ 0).Lov * ∑ i, ‖v i‖ ^ 2)} ≤ ENNReal.ofReal η := by
  obtain ⟨hq7, hp0, hpq, -⟩ := levels_crit θ 1 hθ hθ' one_pos
  have hq8 : 8 ≤ qCrit θ := by
    have h1 : (2 : ℝ) < 10 / θ := by
      rw [lt_div_iff₀ hθ]
      linarith
    have h2 : 2 < ⌈10 / θ⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast h1)
    simp only [qCrit]
    omega
  obtain ⟨g₀, δ₀, C₁, hg₀, hδ₀, hC₁, W₁, h1⟩ :=
    cavRank_tail κ₀ hκ₀ hκ₀' (qCrit θ) hq7 (pCrit θ) (θ / 4) hp0 hpq (by positivity)
  obtain ⟨C₂, hC₂, h2⟩ := fresh_inv_count_tail
  obtain ⟨ε₀, C₃, c, hε₀, hC₃, hc, h3⟩ :=
    invImage_overlap_le κ₀ (12 * θ) hκ₀ hκ₀' (by positivity)
  obtain ⟨W₃, h3⟩ := h3 1 one_pos
  have ev := ((((((((((((Filter.eventually_ge_atTop W₁).and (Filter.eventually_ge_atTop W₃)).and
    (Filter.eventually_ge_atTop 1)).and
    (overlapCrit_ev_neg_le g₀ (1 / 4) (by norm_num) hg₀)).and
    (overlapCrit_ev_neg_le ((η / (6 * C₁)) ^ 2) (1 / 4) (by norm_num) (by positivity))).and
    (overlapCrit_ev_neg_le (η / (6 * C₁)) δ₀ hδ₀ (by positivity))).and
    (overlapCrit_ev_neg_le (η / (6 * C₂)) θ hθ (by positivity))).and
    (overlapCrit_ev_neg_le (η / 6) 1 one_pos (by positivity))).and
    (overlapCrit_ev_le (6 * C₃ / (c * η)) (12 * θ) (by positivity))).and
    (overlapCrit_ev_neg_le (ε₀ / 2) θ hθ (by positivity))).and
    (overlapCrit_ev_le 5 (3 * θ) (by positivity))).and
    (overlapCrit_ev_neg_le (ε₀ / 2) (1 - 12 * θ) (by linarith) (by positivity))).and
    (overlapCrit_ev_le (2 * C₃) (2 * θ) (by positivity))
  obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.1 ev
  refine ⟨W₀, fun W hW g hg hgW E hE R v hRv => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hW1, hW3⟩, hW1'⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩ :=
    hW₀ W hW
  obtain ⟨⟨hRH, -, -⟩, -, hRc, -⟩ := hRv
  have hw1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1'
  have hw0 : (0 : ℝ) < W := lt_of_lt_of_le one_pos hw1
  have hgq : g ≤ (W : ℝ) ^ (-(1 / 4 : ℝ)) :=
    hgW.trans (Real.rpow_le_rpow_of_exponent_le hw1 (by linarith))
  have ht : 0 < (levelsCrit W θ 0).t := Real.rpow_pos_of_pos hw0 _
  have hs0 : 0 < (W : ℝ) ^ (-θ) := Real.rpow_pos_of_pos hw0 _
  have hTc0 : 0 < (W : ℝ) ^ (3 * θ) := Real.rpow_pos_of_pos hw0 _
  have hd1 : (W : ℝ) ^ (12 * θ) ≤ (⌈(W : ℝ) ^ (12 * θ)⌉₊ : ℝ) := Nat.le_ceil _
  have hdε := overlapCrit_d_le hθ hw1 c12
  have hdim := overlapCrit_dim hθ hw1 (overlapCrit_rank_row hθ hθ' hW1') c11
  have hLov0 : 0 ≤ (levelsCrit W θ 0).Lov := Real.rpow_nonneg hw0.le _
  have hK0 : 0 ≤ C₃ * ((⌈(W : ℝ) ^ (12 * θ)⌉₊ : ℝ) / W) * l2Norm v ^ 2 := by positivity
  have hKL : C₃ * ((⌈(W : ℝ) ^ (12 * θ)⌉₊ : ℝ) / W) * l2Norm v ^ 2 ≤
      (levelsCrit W θ 0).Lov * l2Norm v ^ 2 :=
    mul_le_mul_of_nonneg_right (overlapCrit_KL hθ hw1 c13) (by positivity)
  have hq4 : 4 < qCrit θ := by omega
  have hq5 : 5 < qCrit θ := by omega
  have hb4 : ∀ ω : Ω W (qCrit θ), blockSeq W (qCrit θ) ω 4 = gueBlock W (qCrit θ) ω ⟨4, hq4⟩ :=
    fun ω => by simp only [blockSeq, hq4, ↓reduceDIte]
  -- the data of the blocks other than `V_5`, and the bad set of Corollary 9.7 [nc:lem:compression]
  obtain ⟨D, hDdef⟩ : ∃ D : Ω W (qCrit θ) → Matrix (Fin W) (Fin W) ℂ ×
      Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ,
      D = fun ω => (retSpec W g E (qCrit θ) (levelsCrit W θ 0).t ω,
        cavR W g E (qCrit θ) ω (qCrit θ - 7),
        specProj (((g : ℂ) ^ 2) • cavR W g E (qCrit θ) ω (qCrit θ - 7))
          {x | (W : ℝ) ^ (-θ) < |x|}) := ⟨_, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : Matrix (Fin W) (Fin W) ℂ × (Matrix (Fin W) (Fin W) ℂ ×
      Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ) → Matrix (Fin W) (Fin W) ℂ ×
      Matrix (Fin W) (Fin W) ℂ × Matrix (Fin 1) (Fin W) ℂ × ℝ,
      F = fun z => (z.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R - ((g : ℂ) ^ 2) • z.2.2.1, 1 - z.2.1,
        Matrix.of fun _ j => star (v j),
        C₃ * ((⌈(W : ℝ) ^ (12 * θ)⌉₊ : ℝ) / W) * l2Norm v ^ 2) := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Set (Matrix (Fin W) (Fin W) ℂ × (Matrix (Fin W) (Fin W) ℂ ×
      Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ)),
      T = {z | z.2.1.trace.re ≤ 2 * (levelsCrit W θ 0).t ^ (-pCrit θ) * (W : ℝ) ^ (1 + θ / 4) ∧
        z.2.2.2.trace.re ≤ (W : ℝ) ^ (3 * θ) ∧
        F z ∉ {p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ ×
          Matrix (Fin 1) (Fin W) ℂ × ℝ | ∀ x : Fin W → ℂ, p.2.1 *ᵥ (p.1 *ᵥ x) = 0 →
            l2Norm (p.2.2.1 *ᵥ x) ^ 2 ≤ p.2.2.2 * l2Norm x ^ 2}} := ⟨_, rfl⟩
  -- measurability and independence of block `V_5`
  have hm := overlapCrit_meas_data (W := W) (q := qCrit θ) (qCrit θ - 6) (qCrit θ - 7) g E
    (levelsCrit W θ 0).t ((W : ℝ) ^ (-θ))
  have hDm : Measurable D := by
    rw [hDdef]
    exact hm.1.prodMk ((overlapCrit_meas_cavR g E _).prodMk hm.2)
  have hDa : OffBlock W (qCrit θ) ⟨4, hq4⟩ D := by
    intro ω ω' h
    have hb : ∀ k, 5 ≤ k → blockSeq W (qCrit θ) ω k = blockSeq W (qCrit θ) ω' k :=
      fun k hk => overlapCrit_blockSeq_congr h (by simp only; omega)
    have e1 := overlapCrit_cavProd_congr g E (qCrit θ - 6) (fun k hk => hb k (by omega))
    have e2 := overlapCrit_cavR_congr g E (qCrit θ - 7) (fun k hk => hb k (by omega))
    simp only [hDdef, retSpec, e1, e2]
  have hFm : Measurable F := by
    rw [hFdef]
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ measurable_const)
    · exact ((measurable_fst.sub measurable_const).sub measurable_const).sub
        (show Measurable fun z : Matrix (Fin W) (Fin W) ℂ × (Matrix (Fin W) (Fin W) ℂ ×
            Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ) => ((g : ℂ) ^ 2) • z.2.2.1 from
          (measurable_snd.snd.fst).const_smul ((g : ℂ) ^ 2))
    · exact measurable_const.sub measurable_snd.fst
  have hmtr : Measurable fun M : Matrix (Fin W) (Fin W) ℂ => M.trace.re :=
    (Complex.continuous_re.comp (continuous_id.matrix_trace)).measurable
  have hTm : MeasurableSet T := by
    rw [hTdef]
    exact (measurableSet_le (hmtr.comp measurable_snd.fst) measurable_const).inter
      ((measurableSet_le (hmtr.comp measurable_snd.snd.snd) measurable_const).inter
        (measurableSet_invImage_le.compl.preimage hFm))
  -- Corollary 9.7 [nc:lem:compression] on the fresh block `V_5`, at fixed data of the other blocks
  have hb : ∀ ω ∈ (Set.univ : Set (Ω W (qCrit θ))), μ W 1 {ω' | (gueMat W ω', D ω) ∈ T} ≤
      ENNReal.ofReal ((W : ℝ) ^ (-(1 : ℝ)) +
        C₃ * Real.exp (-(c * ⌈(W : ℝ) ^ (12 * θ)⌉₊))) := by
    intro ω _
    by_cases htr : (D ω).1.trace.re ≤
        2 * (levelsCrit W θ 0).t ^ (-pCrit θ) * (W : ℝ) ^ (1 + θ / 4) ∧
      (D ω).2.2.trace.re ≤ (W : ℝ) ^ (3 * θ)
    swap
    · refine le_trans (measure_mono (t := ∅) ?_) (by simp)
      intro ω' hω'
      rw [hTdef] at hω'
      exact htr ⟨hω'.1, hω'.2.1⟩
    obtain ⟨htr1, htr2⟩ := htr
    simp only [hDdef] at htr1 htr2
    obtain ⟨Bs, Bb, hBeq, hBs, hrank⟩ := overlapCrit_split hRH
      (overlapCrit_cavR_herm g E ω (qCrit θ - 7)) hs0.le c10 hRc htr2 htr1 hdim
    have hAH := Matrix.isHermitian_conjTranspose_mul_self
      (cavProd W g E (qCrit θ) ω (qCrit θ - 6))
    obtain ⟨hPuH, hPuP, -, -⟩ := specProj_spec hAH (Set.Ioi ((levelsCrit W θ 0).t ^ 2))
    refine le_trans (measure_mono ?_) (h3 W _ hW3 hd1 hdε _ Bs Bb
      (retSpec W g E (qCrit θ) (levelsCrit W θ 0).t ω) v E
      ((overlapCrit_sq_smul_herm g hRH).add (overlapCrit_sq_smul_herm g
        (overlapCrit_cavR_herm g E ω (qCrit θ - 7)))) hBeq hBs hPuH hPuP hrank hE)
    intro ω' hω'
    rw [hTdef] at hω'
    obtain ⟨-, -, hnG⟩ := hω'
    rw [hFdef, hDdef] at hnG
    simp only [Set.mem_ofPred_eq, not_forall] at hnG
    obtain ⟨x, hx, hlt⟩ := hnG
    refine ⟨x, ?_, ?_⟩
    · rw [← sub_sub]
      exact hx
    · rw [not_le, overlapCrit_row] at hlt
      exact hlt
  -- the three bad events
  have hsub : {ω | ¬ (∑ i, ‖(retProj W g E (qCrit θ) R (levelsCrit W θ 0).t ω *ᵥ v) i‖ ^ 2 ≤
      (levelsCrit W θ 0).Lov * ∑ i, ‖v i‖ ^ 2)} ⊆
      ({ω | 2 * (levelsCrit W θ 0).t ^ (-pCrit θ) * (W : ℝ) ^ (1 + θ / 4) <
          rankSurr (levelsCrit W θ 0).t ((cavProd W g E (qCrit θ) ω (qCrit θ - 6))ᴴ *
            cavProd W g E (qCrit θ) ω (qCrit θ - 6))} ∪
        {ω | ω ∈ Set.univ ∧ (W : ℝ) ^ (3 * θ) < (countIn (((g : ℂ) ^ 2) •
          (gueBlock W (qCrit θ) ω ⟨5, hq5⟩ - (E : ℂ) • 1 -
            ((g : ℂ) ^ 2) • cavR W g E (qCrit θ) ω (qCrit θ - 8))⁻¹)
              {x | (W : ℝ) ^ (-θ) < |x|} : ℝ)}) ∪
        {ω | ω ∈ Set.univ ∧ (gueBlock W (qCrit θ) ω ⟨4, hq4⟩, D ω) ∈ T} := by
    intro ω hω
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, true_and, not_or, not_lt] at hn
    obtain ⟨⟨n1, n2⟩, n3⟩ := hn
    apply hω
    have tr1 : (retSpec W g E (qCrit θ) (levelsCrit W θ 0).t ω).trace.re ≤
        2 * (levelsCrit W θ 0).t ^ (-pCrit θ) * (W : ℝ) ^ (1 + θ / 4) := by
      have hAH := Matrix.isHermitian_conjTranspose_mul_self
        (cavProd W g E (qCrit θ) ω (qCrit θ - 6))
      have e := (specProj_spec hAH (Set.Ioi ((levelsCrit W θ 0).t ^ 2))).2.2.2
      simp only [retSpec]
      rw [e, Complex.natCast_re]
      exact ((countIn_le_rankSurr _ ht one_pos one_le_two).1).trans n1
    have tr2 : (specProj (((g : ℂ) ^ 2) • cavR W g E (qCrit θ) ω (qCrit θ - 7))
        {x | (W : ℝ) ^ (-θ) < |x|}).trace.re ≤ (W : ℝ) ^ (3 * θ) := by
      have e := (specProj_spec (overlapCrit_sq_smul_herm g
        (overlapCrit_cavR_herm g E ω (qCrit θ - 7))) {x | (W : ℝ) ^ (-θ) < |x|}).2.2.2
      rw [e, Complex.natCast_re, overlapCrit_cavR_six hq8]
      exact n2
    have hG : ∀ x : Fin W → ℂ, (1 - retSpec W g E (qCrit θ) (levelsCrit W θ 0).t ω) *ᵥ
        ((gueBlock W (qCrit θ) ω ⟨4, hq4⟩ - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R -
          ((g : ℂ) ^ 2) • cavR W g E (qCrit θ) ω (qCrit θ - 7)) *ᵥ x) = 0 →
        l2Norm ((Matrix.of fun (_ : Fin 1) (j : Fin W) => star (v j)) *ᵥ x) ^ 2 ≤
          C₃ * ((⌈(W : ℝ) ^ (12 * θ)⌉₊ : ℝ) / W) * l2Norm v ^ 2 * l2Norm x ^ 2 := by
      by_contra hG'
      apply n3
      rw [hTdef, hFdef, hDdef]
      exact ⟨tr1, tr2, hG'⟩
    refine overlapCrit_det hq7 R ω v hK0 hKL hLov0 (fun x hx => ?_)
    rw [← overlapCrit_row]
    rw [hb4] at hx
    exact hG x hx
  -- the bounds
  have hE1 := h1 W hW1 g E (levelsCrit W θ 0).t hg (hgq.trans c4) hE ht
  have hE2 := h2 W (qCrit θ) ⟨5, hq5⟩ (fun ω => cavR W g E (qCrit θ) ω (qCrit θ - 8)) Set.univ
    hW1' (overlapCrit_meas_cavR g E (qCrit θ - 8))
    (fun ω => overlapCrit_cavR_herm g E ω (qCrit θ - 8))
    (fun ω ω' h => overlapCrit_cavR_congr g E (qCrit θ - 8)
      (fun k hk => overlapCrit_blockSeq_congr h (by simp only; omega)))
    MeasurableSet.univ (fun _ _ _ => rfl) g E ((W : ℝ) ^ (-θ)) ((W : ℝ) ^ (3 * θ)) hs0 hTc0
  have hE3 := measure_gueBlock_fresh_le W (qCrit θ) ⟨4, hq4⟩ hDm hDa MeasurableSet.univ
    (fun _ _ _ => rfl) hTm hb
  rw [measure_univ, mul_one] at hE2 hE3
  have ha1 := overlapCrit_fail_rank hC₁ hη hgq c5 c6
  have ha2 := overlapCrit_fail_count hw1 hg hgW hC₂ c7
  have ha3 := overlapCrit_fail_compress hC₃ hc hη c8 c9
  have p1 : 0 ≤ C₁ * ((W : ℝ) ^ (-δ₀) + Real.sqrt g) := by positivity
  have p2 : 0 ≤ 2 * C₂ * W * g ^ 2 / ((W : ℝ) ^ (-θ) * (W : ℝ) ^ (3 * θ)) := by positivity
  have p3 : 0 ≤ (W : ℝ) ^ (-(1 : ℝ)) + C₃ * Real.exp (-(c * ⌈(W : ℝ) ^ (12 * θ)⌉₊)) := by
    positivity
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ _ := add_le_add (add_le_add hE1 hE2) hE3
    _ = ENNReal.ofReal (C₁ * ((W : ℝ) ^ (-δ₀) + Real.sqrt g) +
          2 * C₂ * W * g ^ 2 / ((W : ℝ) ^ (-θ) * (W : ℝ) ^ (3 * θ)) +
          ((W : ℝ) ^ (-(1 : ℝ)) + C₃ * Real.exp (-(c * ⌈(W : ℝ) ^ (12 * θ)⌉₊)))) := by
        rw [← ENNReal.ofReal_add p1 p2, ← ENNReal.ofReal_add (add_nonneg p1 p2) p3]
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (by linarith)

end LSBA
