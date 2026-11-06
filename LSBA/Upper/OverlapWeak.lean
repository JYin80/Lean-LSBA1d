import LSBA.Upper.RetainedProb
import LSBA.Upper.AllowBound
import LSBA.Upper.PrepGood
import LSBA.Upper.CutLevels
import LSBA.Spectral.InvImageRange
import LSBA.Spectral.InvImageCompressSub
import LSBA.Spectral.InvImageMeas

/-!
# The small overlap in regime (i)

(9.65) [su:eq:construction-overlap-goals], regime (i) (Section 9.4.1
[su:sec:retained-geometry]). Fix prepared data `(R_4, v_4)` satisfying (9.3) [us:eq:regular],
(9.5) [su:eq:prep] and (9.6) [su:eq:prepared-large-rank], with
`P = 1_{[-W^{ε/800}, W^{ε/800}]}(g² R_4)` of (9.4) [su:eq:source-projection], and the parameters
of (9.54) [su:eq:packet2]. With `Q₀ = 1_{|g² R_4| > W^{-ε/800}}`, the enlarged space
`U = ran A_>* + ran B_{1,>}` of (9.56) [us:eq:Haar], the inclusion (9.57) [us:eq:erase], the
dimension `d = ⌈8 W g² W^{ε/200}⌉` of (9.59) [su:eq:q], Lemma 9.5 [us:lem:range] at `v_4` and at
`P v_4` and the compression bound (9.50) [us:eq:absolute] give (9.60) [su:eq:geometry]:
`‖Q v_4‖² ≤ g² W^{ε/100} b_4`, `‖Q P v_4‖² ≤ g² W^{ε/100} ‖P v_4‖²` and
`‖(1 - P) Q‖² ≤ C d/W`, together with the rank bound (9.55) [su:eq:rank]. In the form used by the
cutoff: `‖Q v_4‖² ≤ g² W^{3ε/200} ‖P v_4‖²`, `16 ‖Q P v_4‖² ≤ ‖P v_4‖²` and
`2 · 8^k Tr ((Q (1 - P) Q)^k) ≤ 1` for `k = ⌈1/α⌉`, except with probability at most any fixed
`η > 0` once `W` is large, uniformly in `a ∈ [α, β]`, `|E| ≤ 2 - κ₀` and the prepared data.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

private lemma OverlapWeak_norm_proj_le {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) : ‖P‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [hP.eq, hPP] at h
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [norm_nonneg P]

private lemma OverlapWeak_one_sub {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) : (1 - P).IsHermitian ∧ (1 - P) * (1 - P) = 1 - P := by
  refine ⟨Matrix.isHermitian_one.sub hP, ?_⟩
  rw [sub_mul, mul_sub, mul_sub, hPP, one_mul, mul_one, one_mul]; abel

private lemma OverlapWeak_l2Norm_proj_le {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (x : Fin W → ℂ) : l2Norm (P *ᵥ x) ≤ l2Norm x := by
  calc l2Norm (P *ᵥ x) ≤ ‖P‖ * l2Norm x := l2Norm_mulVec_le P x
    _ ≤ 1 * l2Norm x := mul_le_mul_of_nonneg_right (OverlapWeak_norm_proj_le hP hPP)
        (Real.sqrt_nonneg _)
    _ = l2Norm x := one_mul _

private lemma OverlapWeak_opNorm_le {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Fin W → ℂ, l2Norm (M *ᵥ x) ≤ c * l2Norm x) : ‖M‖ ≤ c := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have hx := h (WithLp.ofLp x)
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp] at hx
  convert hx using 2
  rfl

private lemma OverlapWeak_abs_le_l2Norm {W : ℕ} (x : Fin W → ℂ) (i : Fin W) :
    ‖x i‖ ≤ l2Norm x := by
  unfold l2Norm
  rw [← Real.sqrt_sq (norm_nonneg (x i))]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

private lemma OverlapWeak_trace_re_le {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) :
    X.trace.re ≤ W * ‖X‖ := by
  have hdiag : ∀ i, ‖X i i‖ ≤ ‖X‖ := by
    intro i
    have h1 : X i i = (X *ᵥ Pi.single i 1) i := by simp [Matrix.mulVec_single]
    have h2 : l2Norm (Pi.single i (1 : ℂ) : Fin W → ℂ) = 1 := by
      unfold l2Norm
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
      simp
    calc ‖X i i‖ = ‖(X *ᵥ Pi.single i 1) i‖ := by rw [← h1]
      _ ≤ l2Norm (X *ᵥ Pi.single i 1) := OverlapWeak_abs_le_l2Norm _ i
      _ ≤ ‖X‖ * l2Norm (Pi.single i (1 : ℂ) : Fin W → ℂ) := l2Norm_mulVec_le X _
      _ = ‖X‖ := by rw [h2, mul_one]
  calc X.trace.re ≤ ‖X.trace‖ := Complex.re_le_norm _
    _ = ‖∑ i, X i i‖ := rfl
    _ ≤ ∑ i, ‖X i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin W, ‖X‖ := Finset.sum_le_sum fun i _ => hdiag i
    _ = W * ‖X‖ := by simp

/-- `Re Tr ((Q (1 - P) Q)^k) ≤ W ‖(1 - P) Q‖^{2k}` for orthogonal projections `P`, `Q`. -/
private lemma OverlapWeak_trace_pow_le {W : ℕ} {P Q : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hQ : Q.IsHermitian) {k : ℕ} (hk : 0 < k) :
    ((Q * (1 - P) * Q) ^ k).trace.re ≤ W * ‖(1 - P) * Q‖ ^ (2 * k) := by
  have hN : Q * (1 - P) * Q = ((1 - P) * Q)ᴴ * ((1 - P) * Q) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.eq,
      hQ.eq]
    rw [show Q * (1 - P) * ((1 - P) * Q) = Q * ((1 - P) * (1 - P)) * Q by
      simp only [Matrix.mul_assoc], (OverlapWeak_one_sub hP hPP).2]
  have hM : ‖Q * (1 - P) * Q‖ = ‖(1 - P) * Q‖ ^ 2 := by
    rw [hN, Matrix.l2_opNorm_conjTranspose_mul_self, sq]
  calc ((Q * (1 - P) * Q) ^ k).trace.re ≤ W * ‖(Q * (1 - P) * Q) ^ k‖ := OverlapWeak_trace_re_le _
    _ ≤ W * ‖Q * (1 - P) * Q‖ ^ k :=
        mul_le_mul_of_nonneg_left (norm_pow_le' _ hk) (Nat.cast_nonneg _)
    _ = W * ‖(1 - P) * Q‖ ^ (2 * k) := by rw [hM, ← pow_mul]

private lemma OverlapWeak_l2Norm_sq {W : ℕ} (z : Fin W → ℂ) :
    l2Norm z ^ 2 = (star z ⬝ᵥ z).re := by
  unfold l2Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

private lemma OverlapWeak_norm_dot_le {W : ℕ} (x y : Fin W → ℂ) :
    ‖star x ⬝ᵥ y‖ ≤ l2Norm x * l2Norm y := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin W))
    (WithLp.toLp 2 y)
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp]
  simpa using h

/-- For Hermitian `B`, `Re y*(1 + B B) y = ‖y‖² + ‖B y‖²`. -/
private lemma OverlapWeak_quad_eq {W : ℕ} {B : Matrix (Fin W) (Fin W) ℂ} (hB : B.IsHermitian)
    (y : Fin W → ℂ) :
    (star y ⬝ᵥ ((1 + B * B) *ᵥ y)).re = l2Norm y ^ 2 + l2Norm (B *ᵥ y) ^ 2 := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Complex.add_re,
    OverlapWeak_l2Norm_sq, OverlapWeak_l2Norm_sq (B *ᵥ y), ← Matrix.mulVec_mulVec,
    Matrix.star_mulVec, hB.eq, Matrix.dotProduct_mulVec]

/-- For Hermitian `B`, `Re x*(1 + B B)⁻¹ x ≤ ‖x‖²`. -/
private lemma OverlapWeak_quad_inv_le {W : ℕ} {B : Matrix (Fin W) (Fin W) ℂ} (hB : B.IsHermitian)
    (x : Fin W → ℂ) : (star x ⬝ᵥ ((1 + B * B)⁻¹ *ᵥ x)).re ≤ l2Norm x ^ 2 := by
  have hMH : (1 + B * B).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, hB.eq]
  have hu : IsUnit (1 + B * B) := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro y z hyz
    have h0 : (1 + B * B) *ᵥ (y - z) = 0 := by rw [Matrix.mulVec_sub, hyz, sub_self]
    have h := OverlapWeak_quad_eq hB (y - z)
    rw [h0, dotProduct_zero, Complex.zero_re] at h
    have hn : l2Norm (y - z) = 0 := by
      have h1 := sq_nonneg (l2Norm (y - z))
      have h2 := sq_nonneg (l2Norm (B *ᵥ (y - z)))
      have h3 : l2Norm (y - z) ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff two_ne_zero |>.mp h3
    rw [l2Norm_eq_norm_toLp, norm_eq_zero] at hn
    have hyz' : WithLp.toLp 2 y = (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin W)) := by
      simpa [sub_eq_zero] using hn
    exact congrArg WithLp.ofLp hyz'
  set y := (1 + B * B)⁻¹ *ᵥ x with hy
  have hMy : (1 + B * B) *ᵥ y = x := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu),
      Matrix.one_mulVec]
  have hdot : star x ⬝ᵥ y = star y ⬝ᵥ ((1 + B * B) *ᵥ y) := by
    rw [← hMy, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hMH.eq, hMy]
  clear_value y
  have hge : l2Norm y ^ 2 ≤ (star x ⬝ᵥ y).re := by
    rw [hdot, OverlapWeak_quad_eq hB]
    nlinarith [sq_nonneg (l2Norm (B *ᵥ y))]
  have hcs : (star x ⬝ᵥ y).re ≤ l2Norm x * l2Norm y :=
    (Complex.re_le_norm _).trans (OverlapWeak_norm_dot_le x y)
  have hyx : l2Norm y ≤ l2Norm x := by
    have hy0 : 0 ≤ l2Norm y := Real.sqrt_nonneg _
    have hx0 : 0 ≤ l2Norm x := Real.sqrt_nonneg _
    nlinarith
  have hx0 : 0 ≤ l2Norm x := Real.sqrt_nonneg _
  calc (star x ⬝ᵥ y).re ≤ l2Norm x * l2Norm y := hcs
    _ ≤ l2Norm x * l2Norm x := mul_le_mul_of_nonneg_left hyx hx0
    _ = l2Norm x ^ 2 := (sq _).symm

private lemma OverlapWeak_rank_add_le {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- The trace of `1 - 1_{(-∞, 0]}(1_{(c, ∞)}(X) + 1_S(Y))` is at most the two counts. -/
private lemma OverlapWeak_trace_union_le {W : ℕ} {X Y : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (c : ℝ) (S : Set ℝ) :
    (1 - specProj (specProj X (Set.Ioi c) + specProj Y S) (Set.Iic 0)).trace.re ≤
      (countIn X (Set.Ioi c) : ℝ) + countIn Y S := by
  have hM : (specProj X (Set.Ioi c) + specProj Y S).IsHermitian :=
    (specProj_spec hX _).1.add (specProj_spec hY _).1
  set M := specProj X (Set.Ioi c) + specProj Y S with hMdef
  have h1 : 1 - specProj M (Set.Iic 0) = specProj M (Set.Ioi 0) := by
    have := (specProj_add_compl hM (Set.Iic 0)).1
    rw [Set.compl_Iic] at this
    rw [← this]; abel
  rw [h1, (specProj_spec hM _).2.2.2, Complex.natCast_re]
  have h2 : (countIn M (Set.Ioi 0) : ℝ) ≤ M.rank := by
    rw [hM.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    unfold countIn
    simp only [hM, ↓reduceDIte]
    exact_mod_cast Finset.card_le_card fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ioi] at hi ⊢
      exact hi.ne'
  have h3 : (M.rank : ℝ) ≤ countIn X (Set.Ioi c) + countIn Y S := by
    have := OverlapWeak_rank_add_le (specProj X (Set.Ioi c)) (specProj Y S)
    rw [rank_specProj hX, rank_specProj hY] at this
    exact_mod_cast this
  exact h2.trans h3

/-! ### The right-cavity chain -/

private lemma OverlapWeak_blockSeq_isHermitian (W q : ℕ) (ω : Ω W q) (k : ℕ) :
    (blockSeq W q ω k).IsHermitian := by
  unfold blockSeq
  split_ifs
  · exact gueBlock_isHermitian _ _ _ _
  · exact Matrix.isHermitian_zero

private lemma OverlapWeak_gsq_herm {W : ℕ} (g : ℝ) {M : Matrix (Fin W) (Fin W) ℂ}
    (hM : M.IsHermitian) : (((g : ℂ) ^ 2) • M).IsHermitian := by
  unfold Matrix.IsHermitian at hM ⊢
  rw [Matrix.conjTranspose_smul, hM, Complex.star_def, map_pow, Complex.conj_ofReal]

private lemma OverlapWeak_cavR_isHermitian (W : ℕ) (g E : ℝ) (q : ℕ) (ω : Ω W q) (m : ℕ) :
    (cavR W g E q ω m).IsHermitian := by
  have hE : IsSelfAdjoint (E : ℂ) := by rw [isSelfAdjoint_iff]; simp
  induction m with
  | zero =>
    simp only [cavR]
    exact ((OverlapWeak_blockSeq_isHermitian W q ω _).sub (Matrix.isHermitian_one.smul hE)).inv
  | succ m ih =>
    simp only [cavR]
    exact (((OverlapWeak_blockSeq_isHermitian W q ω _).sub (Matrix.isHermitian_one.smul hE)).sub
      (OverlapWeak_gsq_herm g ih)).inv

private lemma OverlapWeak_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
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

private lemma OverlapWeak_measurable_mul {W : ℕ} {α : Type*} [MeasurableSpace α]
    {F G : α → Matrix (Fin W) (Fin W) ℂ} (hF : Measurable F) (hG : Measurable G) :
    Measurable fun x => F x * G x := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => hF.eval_matrix.mul hG.eval_matrix

private lemma OverlapWeak_measurable_blockSeq (W q k : ℕ) :
    Measurable fun ω : Ω W q => blockSeq W q ω k := by
  unfold blockSeq
  by_cases hk : k < q
  · simp only [hk, ↓reduceDIte]
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    unfold gueBlock
    simp only [Matrix.of_apply]
    split_ifs <;> fun_prop
  · simp only [hk, ↓reduceDIte]
    exact measurable_const

private lemma OverlapWeak_measurable_cavR (W : ℕ) (g E : ℝ) (q m : ℕ) :
    Measurable fun ω : Ω W q => cavR W g E q ω m := by
  induction m with
  | zero =>
    simp only [cavR]
    exact OverlapWeak_measurable_inv.comp
      ((OverlapWeak_measurable_blockSeq W q _).sub measurable_const)
  | succ m ih =>
    simp only [cavR]
    exact OverlapWeak_measurable_inv.comp
      (((OverlapWeak_measurable_blockSeq W q _).sub measurable_const).sub
        (ih.const_smul ((g : ℂ) ^ 2)))

private lemma OverlapWeak_blockSeq_congr {W q : ℕ} {ω ω' : Ω W q} (a : Fin q)
    (h : ∀ x, x.1 ≠ a → ω x = ω' x) {k : ℕ} (hk : k ≠ a.val) :
    blockSeq W q ω k = blockSeq W q ω' k := by
  unfold blockSeq
  split_ifs with hkq
  · have hne : (⟨k, hkq⟩ : Fin q) ≠ a := fun h' => hk (by rw [← h'])
    have hf : ∀ i j : Fin W, ω (⟨k, hkq⟩, i, j) = ω' (⟨k, hkq⟩, i, j) := fun i j => h _ hne
    ext i j
    simp only [gueBlock, Matrix.of_apply, hf]
  · rfl

/-- `cavR … m` reads only the blocks `V_{k+1}` with `k ≥ q - 2 - m`. -/
private lemma OverlapWeak_cavR_congr (W : ℕ) (g E : ℝ) (q : ℕ) (ω ω' : Ω W q) (m : ℕ)
    (h : ∀ k, q - 2 - m ≤ k → blockSeq W q ω k = blockSeq W q ω' k) :
    cavR W g E q ω m = cavR W g E q ω' m := by
  induction m with
  | zero =>
    simp only [cavR]
    rw [h (q - 2) (by omega)]
  | succ m ih =>
    simp only [cavR]
    rw [h (q - 3 - m) (by omega), ih fun k hk => h k (by omega)]

private lemma OverlapWeak_cavR_offBlock (W : ℕ) (g E : ℝ) (q : ℕ) (a : Fin q) (m : ℕ)
    (ha : a.val < q - 2 - m) : OffBlock W q a fun ω => cavR W g E q ω m := by
  intro ω ω' h
  exact OverlapWeak_cavR_congr W g E q ω ω' m fun k hk =>
    OverlapWeak_blockSeq_congr a h (by omega)

private lemma OverlapWeak_cavProd_congr (W : ℕ) (g E : ℝ) (q : ℕ) (ω ω' : Ω W q) (m : ℕ)
    (h : ∀ j < m, cavR W g E q ω j = cavR W g E q ω' j) :
    cavProd W g E q ω m = cavProd W g E q ω' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [cavProd]
    rw [ih fun j hj => h j (by omega), h m (by omega)]

private lemma OverlapWeak_cavU_offBlock {W q : ℕ} (hq : 7 ≤ q) (g E t s : ℝ) :
    OffBlock W q ⟨4, by omega⟩ fun ω => cavU W g E q t s ω := by
  intro ω ω' h
  have hR : ∀ j, j ≤ q - 7 → cavR W g E q ω j = cavR W g E q ω' j := fun j hj =>
    OverlapWeak_cavR_offBlock W g E q ⟨4, by omega⟩ j (by simp; omega) ω ω' h
  have hP := OverlapWeak_cavProd_congr W g E q ω ω' (q - 6) fun j hj => hR j (by omega)
  simp only [cavU, retSpec, hP, hR (q - 7) le_rfl]

private lemma OverlapWeak_cavU_measurable {W q : ℕ} (hq : 7 ≤ q) (g E t s : ℝ) :
    Measurable fun ω => cavU W g E q t s ω := by
  have hw : Measurable fun ω : Ω W q => windowSample (cavWin q) ω :=
    measurable_pi_iff.mpr fun p => measurable_pi_apply _
  have h : (fun ω => cavU W g E q t s ω) =
      fun ω => cavUWin W g E (q - 6) t s (windowSample (cavWin q) ω) := by
    funext ω; exact cavU_eq_cavUWin hq g E t s ω
  rw [h]
  exact (cavUWin_spec W g E (q - 6) t s).1.comp hw

private lemma OverlapWeak_cavU_proj {W q : ℕ} (hq : 7 ≤ q) (g E t s : ℝ) (ω : Ω W q) :
    (cavU W g E q t s ω).IsHermitian ∧ cavU W g E q t s ω * cavU W g E q t s ω =
      cavU W g E q t s ω := by
  rw [cavU_eq_cavUWin hq]
  exact (cavUWin_spec W g E (q - 6) t s).2.1 _

/-! ### Events of the fresh block `V_5` -/

/-- An inverse-image event of the fresh block `V_5` (block `4`), with data `(P_U, B_{1,<})` fixed
before it: if its law at each `ω ∈ S` is at most `b`, so is its probability on `S`. -/
private lemma OverlapWeak_fresh_event {W q : ℕ} (hq : 5 ≤ q) {k : Type*} [Fintype k]
    {D₁ D₂ : Ω W q → Matrix (Fin W) (Fin W) ℂ} (hD₁ : Measurable D₁) (hD₂ : Measurable D₂)
    (hD₁a : OffBlock W q ⟨4, by omega⟩ D₁) (hD₂a : OffBlock W q ⟨4, by omega⟩ D₂)
    {S : Set (Ω W q)} (hS : MeasurableSet S) (hSa : OffBlock W q ⟨4, by omega⟩ (· ∈ S)) (E : ℝ)
    (B₀ : Matrix (Fin W) (Fin W) ℂ) (K : Matrix k (Fin W) ℂ) (c : ℝ) {b : ℝ≥0∞}
    (hb : ∀ ω ∈ S, μ W 1 {ω' | ∃ x, (1 - D₁ ω) *ᵥ ((gueMat W ω' - (E : ℂ) • 1 - B₀ -
        D₂ ω) *ᵥ x) = 0 ∧ c * l2Norm x ^ 2 < l2Norm (K *ᵥ x) ^ 2} ≤ b) :
    μ W q {ω | ω ∈ S ∧ ¬ ∀ x, (1 - D₁ ω) *ᵥ ((gueBlock W q ω ⟨4, by omega⟩ - (E : ℂ) • 1 -
        B₀ - D₂ ω) *ᵥ x) = 0 → l2Norm (K *ᵥ x) ^ 2 ≤ c * l2Norm x ^ 2} ≤ b := by
  set φ : Matrix (Fin W) (Fin W) ℂ × (Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ) →
      Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ × Matrix k (Fin W) ℂ × ℝ :=
    fun p => (p.1 - (E : ℂ) • 1 - B₀ - p.2.2, 1 - p.2.1, K, c) with hφ
  have hφm : Measurable φ :=
    (((measurable_fst.sub measurable_const).sub measurable_const).sub
      (measurable_snd.comp measurable_snd)).prodMk
      ((measurable_const.sub (measurable_fst.comp measurable_snd)).prodMk
        (measurable_const.prodMk measurable_const))
  have hT : MeasurableSet (φ ⁻¹' {p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ ×
      Matrix k (Fin W) ℂ × ℝ | ∀ x : Fin W → ℂ, p.2.1 *ᵥ (p.1 *ᵥ x) = 0 →
        l2Norm (p.2.2.1 *ᵥ x) ^ 2 ≤ p.2.2.2 * l2Norm x ^ 2})ᶜ :=
    (measurableSet_invImage_le.preimage hφm).compl
  have hDa : OffBlock W q ⟨4, by omega⟩ fun ω => (D₁ ω, D₂ ω) := by
    intro ω ω' h
    simp only [hD₁a ω ω' h, hD₂a ω ω' h]
  have key := measure_gueBlock_fresh_le W q ⟨4, by omega⟩ (hD₁.prodMk hD₂) hDa hS hSa hT (b := b)
    (fun ω hω => by
      refine (measure_mono fun ω' hω' => ?_).trans (hb ω hω)
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_preimage, hφ, not_forall,
        not_le] at hω' ⊢
      obtain ⟨x, hx1, hx2⟩ := hω'
      exact ⟨x, hx1, hx2⟩)
  calc μ W q {ω | ω ∈ S ∧ ¬ ∀ x, (1 - D₁ ω) *ᵥ ((gueBlock W q ω ⟨4, by omega⟩ -
          (E : ℂ) • 1 - B₀ - D₂ ω) *ᵥ x) = 0 → l2Norm (K *ᵥ x) ^ 2 ≤ c * l2Norm x ^ 2}
      = μ W q {ω | ω ∈ S ∧ (gueBlock W q ω ⟨4, by omega⟩, (D₁ ω, D₂ ω)) ∈ (φ ⁻¹'
          {p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ × Matrix k (Fin W) ℂ × ℝ |
            ∀ x : Fin W → ℂ, p.2.1 *ᵥ (p.1 *ᵥ x) = 0 →
              l2Norm (p.2.2.1 *ᵥ x) ^ 2 ≤ p.2.2.2 * l2Norm x ^ 2})ᶜ} := by
        congr 1
    _ ≤ b * μ W q S := key
    _ ≤ b * 1 := mul_le_mul' le_rfl prob_le_one
    _ = b := mul_one b

private lemma OverlapWeak_l2Norm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℂ) : 0 ≤ l2Norm x :=
  Real.sqrt_nonneg _

private lemma OverlapWeak_l2Norm_row {W : ℕ} (v x : Fin W → ℂ) :
    l2Norm ((Matrix.of fun (_ : Fin 1) j => star (v j)) *ᵥ x) ^ 2 = ‖star v ⬝ᵥ x‖ ^ 2 := by
  unfold l2Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp [Matrix.mulVec, dotProduct]

/-! ### Numerical bounds -/

private lemma OverlapWeak_rpow_sq {w : ℝ} (hw : 0 ≤ w) (x : ℝ) : (w ^ x) ^ 2 = w ^ (2 * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hw]
  congr 1
  push_cast
  ring

/-- The rank row (9.55) [su:eq:rank] with room: `2 t^{-p} W^{1+ε/3200} ≤ W g² W^{ε/400}`. -/
private lemma OverlapWeak_rank_le {α β ε a : ℝ} (hβ : β < 1 / 2) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hαβ : α < β) (hα : 0 < α) (ha : a ∈ Set.Icc α β) {w : ℝ} (hw : 1 ≤ w)
    (h2 : 2 ≤ w ^ (ε / 1000)) :
    2 * ((w ^ (-40 : ℝ) * ((w ^ (-a)) ^ qWeak β ε)⁻¹) ^ (-pWeak β ε)) * w ^ (1 + ε / 3200) ≤
      w * (w ^ (-a)) ^ 2 * w ^ (ε / 400) := by
  have hw0 : 0 < w := by linarith
  set N : ℕ := ⌈25600 / ε * (40 + β)⌉₊ with hN
  have hNr : 25600 / ε * (40 + β) ≤ (N : ℝ) := Nat.le_ceil _
  have hβ0 : 0 < β := hα.trans hαβ
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le (by positivity) hNr
  have hq : (qWeak β ε : ℝ) = 5 + N := by simp [qWeak, hN]
  have hp : pWeak β ε = 2 * (1 - ε / 6400) / N := by simp [pWeak, hN]
  set p := pWeak β ε
  -- the exponent of the left side
  have hgq : (w ^ (-a)) ^ qWeak β ε = w ^ (-a * (5 + N)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le, hq]
  have hL : (w ^ (-40 : ℝ) * ((w ^ (-a)) ^ qWeak β ε)⁻¹) ^ (-p) =
      w ^ ((-40 + a * (5 + N)) * (-p)) := by
    rw [hgq, ← Real.rpow_neg hw0.le, ← Real.rpow_add hw0, ← Real.rpow_mul hw0.le]
    congr 1; ring
  have hR : w * (w ^ (-a)) ^ 2 * w ^ (ε / 400) = w ^ (1 - 2 * a + ε / 400) := by
    rw [OverlapWeak_rpow_sq hw0.le, show (1 - 2 * a + ε / 400) = 1 + 2 * (-a) + ε / 400 by ring,
      Real.rpow_add hw0, Real.rpow_add hw0, Real.rpow_one]
  have hNε : 1024000 ≤ ε * N := by
    have := mul_le_mul_of_nonneg_left hNr hε.le
    rw [show ε * (25600 / ε * (40 + β)) = 25600 * (40 + β) by field_simp] at this
    nlinarith
  have h40 : 40 * p ≤ ε / 12800 := by
    rw [hp, show 40 * (2 * (1 - ε / 6400) / N) = 80 * (1 - ε / 6400) / N by ring,
      div_le_div_iff₀ hNpos (by norm_num)]
    nlinarith
  have hap : 2 * a - ε / 6400 ≤ a * (5 + N) * p := by
    have ha0 : 0 ≤ a := hα.le.trans ha.1
    have hrw : a * (5 + N) * p = 2 * a * (1 - ε / 6400) + 10 * a * (1 - ε / 6400) / N := by
      rw [hp]; field_simp; ring
    have h10 : 0 ≤ 10 * a * (1 - ε / 6400) / N := by
      apply div_nonneg _ hNpos.le
      have : 0 ≤ 1 - ε / 6400 := by linarith
      positivity
    have hah : a ≤ 1 / 2 := ha.2.trans hβ.le
    rw [hrw]
    nlinarith
  have hexp : ε / 1000 + ((-40 + a * (5 + N)) * (-p) + (1 + ε / 3200)) ≤ 1 - 2 * a + ε / 400 := by
    nlinarith
  rw [hL, hR, mul_assoc, ← Real.rpow_add hw0]
  calc 2 * w ^ ((-40 + a * (5 + N)) * (-p) + (1 + ε / 3200))
      ≤ w ^ (ε / 1000) * w ^ ((-40 + a * (5 + N)) * (-p) + (1 + ε / 3200)) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = w ^ (ε / 1000 + ((-40 + a * (5 + N)) * (-p) + (1 + ε / 3200))) :=
        (Real.rpow_add hw0 _ _).symm
    _ ≤ w ^ (1 - 2 * a + ε / 400) := Real.rpow_le_rpow_of_exponent_le hw hexp

/-- The sizes around `d = ⌈8 W g² W^{ε/200}⌉` of (9.59) [su:eq:q], for `g = W^{-a}`. -/
private lemma OverlapWeak_sizes {α β ε a : ℝ} (hβ : β < 1 / 2) (hε : 0 < ε) (hεα : ε ≤ 100 * α)
    (ha : a ∈ Set.Icc α β) {w : ℝ} (hw : 1 ≤ w) :
    1 ≤ w * (w ^ (-a)) ^ 2 ∧ w ^ (1 - 2 * β) ≤ w * (w ^ (-a)) ^ 2 ∧
    4 * (w * (w ^ (-a)) ^ 2 * w ^ (ε / 400)) + 1 ≤
      (⌈8 * w * (w ^ (-a)) ^ 2 * w ^ (ε / 200)⌉₊ : ℝ) ∧
    w * (w ^ (-a)) ^ 2 ≤ (⌈8 * w * (w ^ (-a)) ^ 2 * w ^ (ε / 200)⌉₊ : ℝ) ∧
    (⌈8 * w * (w ^ (-a)) ^ 2 * w ^ (ε / 200)⌉₊ : ℝ) ≤ 9 * (w * ((w ^ (-a)) ^ 2 * w ^ (ε / 200))) ∧
    (w ^ (-a)) ^ 2 * w ^ (ε / 200) ≤ w ^ (-(3 * α / 2)) := by
  have hw0 : 0 < w := by linarith
  have hg2 : (w ^ (-a)) ^ 2 = w ^ (-2 * a) := by rw [OverlapWeak_rpow_sq hw0.le]; ring_nf
  have hY : w * (w ^ (-a)) ^ 2 = w ^ (1 - 2 * a) := by
    rw [hg2, show (1 - 2 * a) = 1 + -2 * a by ring, Real.rpow_add hw0, Real.rpow_one]
  have hY1 : 1 ≤ w * (w ^ (-a)) ^ 2 := by
    rw [hY]; exact Real.one_le_rpow hw (by linarith [ha.2])
  have hYβ : w ^ (1 - 2 * β) ≤ w * (w ^ (-a)) ^ 2 := by
    rw [hY]; exact Real.rpow_le_rpow_of_exponent_le hw (by linarith [ha.2])
  have h400 : 1 ≤ w ^ (ε / 400) := Real.one_le_rpow hw (by positivity)
  have h200 : 1 ≤ w ^ (ε / 200) := Real.one_le_rpow hw (by positivity)
  have h400' : w ^ (ε / 400) ≤ w ^ (ε / 200) :=
    Real.rpow_le_rpow_of_exponent_le hw (by linarith)
  set Y := w * (w ^ (-a)) ^ 2
  have hceil : 8 * w * (w ^ (-a)) ^ 2 * w ^ (ε / 200) ≤
      (⌈8 * w * (w ^ (-a)) ^ 2 * w ^ (ε / 200)⌉₊ : ℝ) := Nat.le_ceil _
  have hceil' : (⌈8 * w * (w ^ (-a)) ^ 2 * w ^ (ε / 200)⌉₊ : ℝ) <
      8 * w * (w ^ (-a)) ^ 2 * w ^ (ε / 200) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hE : 8 * w * (w ^ (-a)) ^ 2 * w ^ (ε / 200) = 8 * (Y * w ^ (ε / 200)) := by ring
  have hYX : 1 ≤ Y * w ^ (ε / 400) := one_le_mul_of_one_le_of_one_le hY1 h400
  have hYX' : Y * w ^ (ε / 400) ≤ Y * w ^ (ε / 200) :=
    mul_le_mul_of_nonneg_left h400' (by linarith)
  have hYZ : Y ≤ Y * w ^ (ε / 200) := le_mul_of_one_le_right (by linarith) h200
  refine ⟨hY1, hYβ, by linarith, by linarith, ?_, ?_⟩
  · have : w * ((w ^ (-a)) ^ 2 * w ^ (ε / 200)) = Y * w ^ (ε / 200) := by ring
    rw [this]; linarith
  · rw [hg2, ← Real.rpow_add hw0]
    exact Real.rpow_le_rpow_of_exponent_le hw (by linarith [ha.1])

private lemma OverlapWeak_tendsto_neg {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun W : ℕ => (W : ℝ) ^ (-c)) Filter.atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop

private lemma OverlapWeak_tendsto_pos {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun W : ℕ => (W : ℝ) ^ c) Filter.atTop Filter.atTop :=
  (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop

private lemma OverlapWeak_tendsto_exp {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) :
    Filter.Tendsto (fun W : ℕ => Real.exp (-(c * (W : ℝ) ^ γ))) Filter.atTop (nhds 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp ((OverlapWeak_tendsto_pos hγ).const_mul_atTop hc)

/-- `K (log W)² ≤ W^{2c}` once `W` is large, for `c > 0`. -/
private lemma OverlapWeak_ev_log {c K : ℝ} (hc : 0 < c) :
    ∀ᶠ W : ℕ in Filter.atTop, K * Real.log W ^ 2 ≤ (W : ℝ) ^ (4 * c) := by
  filter_upwards [(OverlapWeak_tendsto_pos (by positivity : 0 < 2 * c)).eventually_ge_atTop
    (|K| * (1 / c) ^ 2), Filter.eventually_ge_atTop 1] with W hW hW1
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hw0 : (0 : ℝ) ≤ W := by linarith
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1'
  have hlog : Real.log W ≤ (W : ℝ) ^ c / c := Real.log_le_rpow_div hw0 hc
  have hsq : Real.log W ^ 2 ≤ (W : ℝ) ^ (2 * c) * (1 / c) ^ 2 := by
    calc Real.log W ^ 2 ≤ ((W : ℝ) ^ c / c) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
      _ = (W : ℝ) ^ (2 * c) * (1 / c) ^ 2 := by
          rw [div_pow, OverlapWeak_rpow_sq hw0]; ring
  have hpos : 0 ≤ (W : ℝ) ^ (2 * c) := by positivity
  calc K * Real.log W ^ 2 ≤ |K| * Real.log W ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg _)
    _ ≤ |K| * ((W : ℝ) ^ (2 * c) * (1 / c) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (abs_nonneg K)
    _ = (|K| * (1 / c) ^ 2) * (W : ℝ) ^ (2 * c) := by ring
    _ ≤ (W : ℝ) ^ (2 * c) * (W : ℝ) ^ (2 * c) := mul_le_mul_of_nonneg_right hW hpos
    _ = (W : ℝ) ^ (4 * c) := by
        rw [← Real.rpow_add (by linarith)]; ring_nf

/-- The conditions on `W` alone used in the proof of `overlap_weak`. -/
private lemma OverlapWeak_eventually {α β ε : ℝ} (hα : 0 < α) (hβ : β < 1 / 2) (hε : 0 < ε)
    {g₀ δ₀ ε₁ ε₂ η : ℝ} (hg₀ : 0 < g₀) (hδ₀ : 0 < δ₀) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hη : 0 < η) (CR CF CT cT C₁ c₁ C₂ c₂ Cp : ℝ) (hcT : 0 < cT) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (k : ℕ) :
    ∀ᶠ W : ℕ in Filter.atTop, 1 ≤ (W : ℝ) ∧ (W : ℝ) ^ (-α) ≤ g₀ ∧ 2 ≤ (W : ℝ) ^ (ε / 1000) ∧
      9 * (W : ℝ) ^ (-(3 * α / 2)) ≤ min (min ε₁ ε₂) 1 ∧
      2 * (W : ℝ) ^ (-(ε / 800)) ≤ min ε₁ ε₂ ∧
      9 * C₁ * Cp * Real.log W ^ 2 ≤ (W : ℝ) ^ (ε / 100) ∧
      144 * C₁ * Real.log W ^ 2 * (W : ℝ) ^ (-(3 * α / 2)) ≤ 1 ∧
      2 * (72 * C₂ ^ 2) ^ k * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 ∧
      CR * ((W : ℝ) ^ (-δ₀) + (W : ℝ) ^ (-(α / 2))) + 2 * CF * (W : ℝ) ^ (-(ε / 800)) +
        CT * Real.exp (-(cT * (W : ℝ) ^ (1 - 2 * β))) + 3 * (W : ℝ) ^ (-(1 : ℝ)) +
        2 * C₁ * Real.exp (-(c₁ * (W : ℝ) ^ (1 - 2 * β))) +
        C₂ * Real.exp (-(c₂ * (W : ℝ) ^ (1 - 2 * β))) < η := by
  have hγ : 0 < 1 - 2 * β := by linarith
  have e1 : ∀ᶠ W : ℕ in Filter.atTop, 1 ≤ (W : ℝ) :=
    (Filter.eventually_ge_atTop 1).mono fun W hW => by exact_mod_cast hW
  have e2 := (OverlapWeak_tendsto_neg hα).eventually (ge_mem_nhds hg₀)
  have e3 := (OverlapWeak_tendsto_pos (by positivity : 0 < ε / 1000)).eventually_ge_atTop 2
  have e4 : ∀ᶠ W : ℕ in Filter.atTop, 9 * (W : ℝ) ^ (-(3 * α / 2)) ≤ min (min ε₁ ε₂) 1 := by
    have h := (OverlapWeak_tendsto_neg (by positivity : 0 < 3 * α / 2)).const_mul 9
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (lt_min (lt_min hε₁ hε₂) one_pos))
  have e5 : ∀ᶠ W : ℕ in Filter.atTop, 2 * (W : ℝ) ^ (-(ε / 800)) ≤ min ε₁ ε₂ := by
    have h := (OverlapWeak_tendsto_neg (by positivity : 0 < ε / 800)).const_mul 2
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (lt_min hε₁ hε₂))
  have e6 : ∀ᶠ W : ℕ in Filter.atTop, 9 * C₁ * Cp * Real.log W ^ 2 ≤ (W : ℝ) ^ (ε / 100) := by
    have h := OverlapWeak_ev_log (K := 9 * C₁ * Cp) (by positivity : 0 < ε / 400)
    refine h.mono fun W hW => ?_
    rwa [show 4 * (ε / 400) = ε / 100 by ring] at hW
  have e7 : ∀ᶠ W : ℕ in Filter.atTop, 144 * C₁ * Real.log W ^ 2 * (W : ℝ) ^ (-(3 * α / 2)) ≤ 1 := by
    have h := OverlapWeak_ev_log (K := 144 * C₁) (by positivity : 0 < 3 * α / 16)
    filter_upwards [h, e1] with W hW hW1
    have hw0 : (0 : ℝ) < W := by linarith
    calc 144 * C₁ * Real.log W ^ 2 * (W : ℝ) ^ (-(3 * α / 2))
        ≤ (W : ℝ) ^ (4 * (3 * α / 16)) * (W : ℝ) ^ (-(3 * α / 2)) :=
          mul_le_mul_of_nonneg_right hW (by positivity)
      _ = (W : ℝ) ^ (-(3 * α / 4)) := by rw [← Real.rpow_add hw0]; ring_nf
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have e8 : ∀ᶠ W : ℕ in Filter.atTop, 2 * (72 * C₂ ^ 2) ^ k * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    have h := (OverlapWeak_tendsto_neg (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
      (2 * (72 * C₂ ^ 2) ^ k)
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds one_pos)
  have e9 : ∀ᶠ W : ℕ in Filter.atTop,
      CR * ((W : ℝ) ^ (-δ₀) + (W : ℝ) ^ (-(α / 2))) + 2 * CF * (W : ℝ) ^ (-(ε / 800)) +
        CT * Real.exp (-(cT * (W : ℝ) ^ (1 - 2 * β))) + 3 * (W : ℝ) ^ (-(1 : ℝ)) +
        2 * C₁ * Real.exp (-(c₁ * (W : ℝ) ^ (1 - 2 * β))) +
        C₂ * Real.exp (-(c₂ * (W : ℝ) ^ (1 - 2 * β))) < η := by
    have h := ((((((OverlapWeak_tendsto_neg hδ₀).add
      (OverlapWeak_tendsto_neg (by positivity : 0 < α / 2))).const_mul CR).add
      ((OverlapWeak_tendsto_neg (by positivity : 0 < ε / 800)).const_mul (2 * CF))).add
      ((OverlapWeak_tendsto_exp hcT hγ).const_mul CT)).add
      ((OverlapWeak_tendsto_neg one_pos).const_mul 3)).add
      ((OverlapWeak_tendsto_exp hc₁ hγ).const_mul (2 * C₁)) |>.add
      ((OverlapWeak_tendsto_exp hc₂ hγ).const_mul C₂)
    simp only [add_zero, mul_zero] at h
    exact h.eventually (gt_mem_nhds hη)
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8, e9] with W h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-! ### The deterministic step -/

/-- Off the failure events: if every `x` with `Γ x ∈ U` obeys the relative bound of (9.42)
[us:eq:relative] at `u = v_4` and `u = P v_4` and the compression bound of (9.50)
[us:eq:absolute], then by the inclusion (9.57) [us:eq:erase] the three cuts hold for
`Q = retProj`. -/
private lemma OverlapWeak_det {W q : ℕ} (hq : 7 ≤ q) (g E t s : ℝ)
    (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) (v : Fin W → ℂ)
    {P Q₀ B₀ : Matrix (Fin W) (Fin W) ℂ} (hB₀H : B₀.IsHermitian) (hB₀ : B₀ = ((g : ℂ) ^ 2) • R)
    (hPH : P.IsHermitian) (hPP : P * P = P) (h1P : (1 - P) * Q₀ = 1 - P)
    {Kr Cp Lov c : ℝ} {k : ℕ} (hk : 0 < k) (hKr : 0 ≤ Kr) (hCp : 0 ≤ Cp) (hc : 0 ≤ c)
    (hbv : (star v ⬝ᵥ ((1 + B₀ * B₀)⁻¹ *ᵥ v)).re ≤ Cp * l2Norm (P *ᵥ v) ^ 2)
    (hLov : 0 ≤ Lov) (h1 : Kr * Cp ≤ Lov) (h2 : 16 * Kr ≤ 1)
    (h3 : 2 * 8 ^ k * (W * c ^ (2 * k)) ≤ 1)
    (hgr : ∀ u x, (u = v ∨ u = P *ᵥ v) → (1 - cavU W g E q t s ω) *ᵥ ((blockSeq W q ω 4 -
        (E : ℂ) • 1 - B₀ - ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7) *
          specProj (((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) {x | |x| ≤ s}) *ᵥ x) = 0 →
        ‖star u ⬝ᵥ x‖ ^ 2 ≤ Kr * (star u ⬝ᵥ ((1 + B₀ * B₀)⁻¹ *ᵥ u)).re * l2Norm x ^ 2)
    (hgc : ∀ x, (1 - cavU W g E q t s ω) *ᵥ ((blockSeq W q ω 4 -
        (E : ℂ) • 1 - B₀ - ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7) *
          specProj (((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) {x | |x| ≤ s}) *ᵥ x) = 0 →
        l2Norm (Q₀ *ᵥ x) ^ 2 ≤ c ^ 2 * l2Norm x ^ 2) :
    ∑ i, ‖(retProj W g E q R t ω *ᵥ v) i‖ ^ 2 ≤ Lov * ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ∧
      16 * ∑ i, ‖(retProj W g E q R t ω *ᵥ (P *ᵥ v)) i‖ ^ 2 ≤ ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ∧
      2 * 8 ^ k * ((retProj W g E q R t ω * (1 - P) * retProj W g E q R t ω) ^ k).trace.re ≤
        1 := by
  have hsum : ∀ x : Fin W → ℂ, ∑ i, ‖x i‖ ^ 2 = l2Norm x ^ 2 := fun x => by
    unfold l2Norm; rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp only [hsum]
  by_cases hTu : IsUnit (cavRes W g E q R ω)
  · obtain ⟨hQH, hQQ, -⟩ := trace_retProj R t ω hTu
    set Q := retProj W g E q R t ω with hQ
    have hinc : ∀ x, Q *ᵥ x = x → (1 - cavU W g E q t s ω) *ᵥ ((blockSeq W q ω 4 -
        (E : ℂ) • 1 - B₀ - ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7) *
          specProj (((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) {x | |x| ≤ s}) *ᵥ x) = 0 := by
      intro x hx
      rw [hB₀]
      exact retProj_mem_invImage_weak hq R t s ω hTu x hx
    have hPv0 : 0 ≤ l2Norm (P *ᵥ v) ^ 2 := sq_nonneg _
    have hQv : l2Norm (Q *ᵥ v) ^ 2 ≤ Kr * (Cp * l2Norm (P *ᵥ v) ^ 2) := by
      refine sq_l2Norm_proj_le hQH hQQ v (by positivity) fun x hx => ?_
      exact (hgr v x (Or.inl rfl) (hinc x hx)).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbv hKr) (sq_nonneg _))
    have hQPv : l2Norm (Q *ᵥ (P *ᵥ v)) ^ 2 ≤ Kr * l2Norm (P *ᵥ v) ^ 2 := by
      refine sq_l2Norm_proj_le hQH hQQ _ (by positivity) fun x hx => ?_
      exact (hgr _ x (Or.inr rfl) (hinc x hx)).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (OverlapWeak_quad_inv_le hB₀H _) hKr) (sq_nonneg _))
    have hop : ‖(1 - P) * Q‖ ≤ c := by
      refine OverlapWeak_opNorm_le _ hc fun y => ?_
      have hx : Q *ᵥ (Q *ᵥ y) = Q *ᵥ y := by rw [Matrix.mulVec_mulVec, hQQ]
      have h := hgc _ (hinc _ hx)
      have h' : l2Norm (Q₀ *ᵥ (Q *ᵥ y)) ≤ c * l2Norm (Q *ᵥ y) :=
        le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hc (OverlapWeak_l2Norm_nonneg _))
          (by rwa [mul_pow])
      obtain ⟨h1PH, h1PP⟩ := OverlapWeak_one_sub hPH hPP
      calc l2Norm (((1 - P) * Q) *ᵥ y) = l2Norm ((1 - P) *ᵥ (Q₀ *ᵥ (Q *ᵥ y))) := by
            rw [Matrix.mulVec_mulVec, h1P, Matrix.mulVec_mulVec]
        _ ≤ l2Norm (Q₀ *ᵥ (Q *ᵥ y)) := OverlapWeak_l2Norm_proj_le h1PH h1PP _
        _ ≤ c * l2Norm (Q *ᵥ y) := h'
        _ ≤ c * l2Norm y := mul_le_mul_of_nonneg_left (OverlapWeak_l2Norm_proj_le hQH hQQ y) hc
    have htr := OverlapWeak_trace_pow_le hPH hPP hQH hk (Q := Q)
    have hpow : ‖(1 - P) * Q‖ ^ (2 * k) ≤ c ^ (2 * k) := pow_le_pow_left₀ (norm_nonneg _) hop _
    refine ⟨by nlinarith [mul_le_mul_of_nonneg_right h1 hPv0],
      by nlinarith [mul_le_mul_of_nonneg_right h2 hPv0], ?_⟩
    exact (mul_le_mul_of_nonneg_left (htr.trans (mul_le_mul_of_nonneg_left hpow
      (Nat.cast_nonneg _))) (by positivity)).trans h3
  · have hzero : cavRes W g E q R ω = 0 := by
      unfold cavRes at hTu ⊢
      rw [Matrix.isUnit_nonsing_inv_iff] at hTu
      exact Matrix.nonsing_inv_apply_not_isUnit _
        (fun h => hTu ((Matrix.isUnit_iff_isUnit_det _).mpr h))
    have hQ0 : retProj W g E q R t ω = 0 := by simp [retProj, flagProj, hzero]
    rw [hQ0]
    simp only [Matrix.zero_mulVec, Matrix.zero_mul, zero_pow hk.ne',
      Matrix.trace_zero, Complex.zero_re, mul_zero]
    have hl : (0 : ℝ) ≤ l2Norm (P *ᵥ v) ^ 2 := sq_nonneg _
    have h0 : l2Norm (0 : Fin W → ℂ) = 0 := by simp [l2Norm]
    rw [h0]
    refine ⟨by nlinarith, by nlinarith, zero_le_one⟩

/-! ### Assembly -/

/-- Six events of probabilities at most `ofReal xᵢ` with `∑ xᵢ ≤ η`. -/
private lemma OverlapWeak_union_le {X : Type*} [MeasurableSpace X] (m : MeasureTheory.Measure X)
    {A₁ A₂ A₃ A₄ A₅ A₆ : Set X} {x₁ x₂ x₃ x₄ x₅ x₆ η : ℝ} (h₁ : m A₁ ≤ ENNReal.ofReal x₁)
    (h₂ : m A₂ ≤ ENNReal.ofReal x₂) (h₃ : m A₃ ≤ ENNReal.ofReal x₃)
    (h₄ : m A₄ ≤ ENNReal.ofReal x₄) (h₅ : m A₅ ≤ ENNReal.ofReal x₅)
    (h₆ : m A₆ ≤ ENNReal.ofReal x₆) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hx₃ : 0 ≤ x₃) (hx₄ : 0 ≤ x₄)
    (hx₅ : 0 ≤ x₅) (hx₆ : 0 ≤ x₆) (hsum : x₁ + x₂ + x₃ + x₄ + x₅ + x₆ ≤ η) :
    m (A₁ ∪ A₂ ∪ A₃ ∪ A₄ ∪ A₅ ∪ A₆) ≤ ENNReal.ofReal η := by
  calc m (A₁ ∪ A₂ ∪ A₃ ∪ A₄ ∪ A₅ ∪ A₆)
      ≤ m A₁ + m A₂ + m A₃ + m A₄ + m A₅ + m A₆ := by
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal x₁ + ENNReal.ofReal x₂ + ENNReal.ofReal x₃ + ENNReal.ofReal x₄ +
        ENNReal.ofReal x₅ + ENNReal.ofReal x₆ := by gcongr
    _ = ENNReal.ofReal (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) := by
        rw [ENNReal.ofReal_add (by positivity) hx₆, ENNReal.ofReal_add (by positivity) hx₅,
          ENNReal.ofReal_add (by positivity) hx₄, ENNReal.ofReal_add (by positivity) hx₃,
          ENNReal.ofReal_add hx₁ hx₂]
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hsum

/-- The failure of the count event (9.58) [us:eq:wegner] at `s = W^{-ε/800}`,
`T = W g² W^{ε/400}`. -/
private lemma OverlapWeak_count_fail {w g ε CF : ℝ} (hw : 0 < w) (hg : 0 < g) :
    2 * CF * w * g ^ 2 / (w ^ (-(ε / 800)) * (w * g ^ 2 * w ^ (ε / 400))) =
      2 * CF * w ^ (-(ε / 800)) := by
  have h4 : w ^ (ε / 400) = w ^ (ε / 800) * w ^ (ε / 800) := by
    rw [← Real.rpow_add hw]; ring_nf
  have hp : 0 < w ^ (ε / 800) := Real.rpow_pos_of_pos hw _
  rw [Real.rpow_neg hw.le, h4]
  field_simp

/-- The first two cut rows: `Kr Cp ≤ g² W^{3ε/200}` and `16 Kr ≤ 1` for
`Kr = C₁ (d/W) (log W)²`. -/
private lemma OverlapWeak_cut12 {w g ε α C₁ Cp x : ℝ} (hw : 1 ≤ w) (hC₁ : 0 < C₁) (hCp : 0 < Cp)
    (hx : x ≤ 9 * (g ^ 2 * w ^ (ε / 200)))
    (hx' : x ≤ 9 * w ^ (-(3 * α / 2)))
    (h1 : 9 * C₁ * Cp * Real.log w ^ 2 ≤ w ^ (ε / 100))
    (h2 : 144 * C₁ * Real.log w ^ 2 * w ^ (-(3 * α / 2)) ≤ 1) :
    C₁ * x * Real.log w ^ 2 * Cp ≤ g ^ 2 * w ^ (3 * ε / 200) ∧
      16 * (C₁ * x * Real.log w ^ 2) ≤ 1 := by
  have hw0 : 0 < w := by linarith
  have hl : 0 ≤ Real.log w ^ 2 := sq_nonneg _
  have hg2 : 0 ≤ g ^ 2 * w ^ (ε / 200) := by positivity
  constructor
  · calc C₁ * x * Real.log w ^ 2 * Cp
          ≤ C₁ * (9 * (g ^ 2 * w ^ (ε / 200))) * Real.log w ^ 2 * Cp := by gcongr
      _ = (g ^ 2 * w ^ (ε / 200)) * (9 * C₁ * Cp * Real.log w ^ 2) := by ring
      _ ≤ (g ^ 2 * w ^ (ε / 200)) * w ^ (ε / 100) := mul_le_mul_of_nonneg_left h1 hg2
      _ = g ^ 2 * w ^ (3 * ε / 200) := by
          rw [mul_assoc, ← Real.rpow_add hw0]; ring_nf
  · calc 16 * (C₁ * x * Real.log w ^ 2)
          ≤ 16 * (C₁ * (9 * w ^ (-(3 * α / 2))) * Real.log w ^ 2) := by gcongr
      _ = 144 * C₁ * Real.log w ^ 2 * w ^ (-(3 * α / 2)) := by ring
      _ ≤ 1 := h2

/-- The compatibility row: `2 · 8^k W (C₂ √x)^{2k} ≤ 1` for `x ≤ 9 W^{-3α/2}`, `α k ≥ 1`. -/
private lemma OverlapWeak_cut3 {w C₂ x α : ℝ} {k : ℕ} (hw : 1 ≤ w) (hx0 : 0 ≤ x)
    (hx : x ≤ 9 * w ^ (-(3 * α / 2))) (hkα : 1 ≤ α * k)
    (h : 2 * (72 * C₂ ^ 2) ^ k * w ^ (-(1 / 2 : ℝ)) ≤ 1) :
    2 * 8 ^ k * (w * (C₂ * Real.sqrt x) ^ (2 * k)) ≤ 1 := by
  have hw0 : 0 < w := by linarith
  have h1 : (C₂ * Real.sqrt x) ^ (2 * k) = (C₂ ^ 2 * x) ^ k := by
    rw [pow_mul, mul_pow, Real.sq_sqrt hx0]
  have h2 : (C₂ ^ 2 * x) ^ k ≤ (9 * C₂ ^ 2) ^ k * w ^ (-(3 * α / 2) * k) := by
    rw [Real.rpow_mul hw0.le, Real.rpow_natCast, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg C₂]) k
  have h3 : w * w ^ (-(3 * α / 2) * k) ≤ w ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_one_add' hw0.le (by nlinarith)]
    exact Real.rpow_le_rpow_of_exponent_le hw (by nlinarith)
  rw [h1]
  calc 2 * 8 ^ k * (w * (C₂ ^ 2 * x) ^ k)
      ≤ 2 * 8 ^ k * (w * ((9 * C₂ ^ 2) ^ k * w ^ (-(3 * α / 2) * k))) := by gcongr
    _ = 2 * (8 * (9 * C₂ ^ 2)) ^ k * (w * w ^ (-(3 * α / 2) * k)) := by
        rw [mul_pow 8 (9 * C₂ ^ 2) k]; ring
    _ ≤ 2 * (8 * (9 * C₂ ^ 2)) ^ k * w ^ (-(1 / 2 : ℝ)) := by gcongr
    _ = 2 * (72 * C₂ ^ 2) ^ k * w ^ (-(1 / 2 : ℝ)) := by ring_nf
    _ ≤ 1 := h

/-! ### The zero matrix -/

/-- (9.65) [su:eq:construction-overlap-goals] in regime (i), (9.60) [su:eq:geometry] with
(9.55) [su:eq:rank], at fixed prepared data, in the form of the overlap and compatibility cuts
(9.79) [su:eq:cuts] and (9.83) [su:eq:compatibility-cutoff]. -/
theorem overlap_weak (κ₀ α β ε Cp : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hα : 0 < α)
    (hαβ : α < β) (hβ : β < 1 / 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεα : ε ≤ 100 * α)
    (hCp : 0 < Cp) (η : ℝ) (hη : 0 < η) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ a ∈ Set.Icc α β, ∀ E : ℝ, |E| ≤ 2 - κ₀ →
      ∀ (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ),
        (R, v) ∈ PrepGoodWeak W ((W : ℝ) ^ (-a)) ε Cp →
        μ W (qWeak β ε) {ω | ¬ (
          ∑ i, ‖(retProj W ((W : ℝ) ^ (-a)) E (qWeak β ε) R
              (levelsWeak W ((W : ℝ) ^ (-a)) α β ε 0).t ω *ᵥ v) i‖ ^ 2 ≤
            (levelsWeak W ((W : ℝ) ^ (-a)) α β ε 0).Lov *
              ∑ i, ‖(specProj ((((W : ℝ) ^ (-a)) ^ 2 : ℝ) • R)
                (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800))) *ᵥ v) i‖ ^ 2 ∧
          16 * ∑ i, ‖(retProj W ((W : ℝ) ^ (-a)) E (qWeak β ε) R
              (levelsWeak W ((W : ℝ) ^ (-a)) α β ε 0).t ω *ᵥ
              (specProj ((((W : ℝ) ^ (-a)) ^ 2 : ℝ) • R)
                (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800))) *ᵥ v)) i‖ ^ 2 ≤
            ∑ i, ‖(specProj ((((W : ℝ) ^ (-a)) ^ 2 : ℝ) • R)
                (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800))) *ᵥ v) i‖ ^ 2 ∧
          2 * 8 ^ (levelsWeak W ((W : ℝ) ^ (-a)) α β ε 0).kP *
              ((retProj W ((W : ℝ) ^ (-a)) E (qWeak β ε) R
                  (levelsWeak W ((W : ℝ) ^ (-a)) α β ε 0).t ω *
                (1 - specProj ((((W : ℝ) ^ (-a)) ^ 2 : ℝ) • R)
                  (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800)))) *
                retProj W ((W : ℝ) ^ (-a)) E (qWeak β ε) R
                  (levelsWeak W ((W : ℝ) ^ (-a)) α β ε 0).t ω) ^
                (levelsWeak W ((W : ℝ) ^ (-a)) α β ε 0).kP).trace.re ≤ 1)} ≤
          ENNReal.ofReal η := by
  obtain ⟨hq7, hp0, hpq, -⟩ := levels_weak α β ε hα hαβ hβ hε hε1 hεα
  have hβ0 : 0 < β := hα.trans hαβ
  have hδ : 0 < (1 - 2 * β) / 4 := by linarith
  obtain ⟨g₀, δ₀, CR, hg₀, hδ₀, hCR, WR, hRk⟩ := cavRank_tail κ₀ hκ₀ hκ₀' (qWeak β ε) hq7
    (pWeak β ε) (ε / 3200) hp0 hpq (by positivity)
  obtain ⟨CF, hCF, hFr⟩ := fresh_inv_count_tail
  obtain ⟨CT, cT, hCT, hcT, hHaar⟩ := cavU_overlap_le
  obtain ⟨ε₁, C₁, c₁, hε₁, hC₁, hc₁, hrel⟩ :=
    invImage_relative_le κ₀ ((1 - 2 * β) / 4) CT hκ₀ hκ₀' hδ hCT
  obtain ⟨W₁, hW₁⟩ := hrel 1 one_pos
  obtain ⟨ε₂, C₂, c₂, hε₂, hC₂, hc₂, hcomp⟩ :=
    invImage_compress_sub_le κ₀ ((1 - 2 * β) / 4) hκ₀ hκ₀' hδ
  obtain ⟨W₂, hW₂⟩ := hcomp 1 one_pos
  obtain ⟨WN, hWN⟩ := Filter.eventually_atTop.mp (OverlapWeak_eventually hα hβ hε hg₀ hδ₀ hε₁ hε₂
    hη CR CF CT cT C₁ c₁ C₂ c₂ Cp hcT hc₁ hc₂ ⌈1 / α⌉₊)
  refine ⟨max (max WR W₁) (max W₂ WN), fun W hW a ha E hE R v hRv => ?_⟩
  obtain ⟨⟨hWR, hW1⟩, hW2, hWN'⟩ := by simpa only [max_le_iff] using hW
  obtain ⟨hw1, hwg₀, hw2, hw9, hws, hwlog1, hwlog2, hwk, hwfail⟩ := hWN W hWN'
  have hw0 : (0 : ℝ) < W := by linarith
  have hW1n : 1 ≤ W := by exact_mod_cast hw1
  have hq8 : 8 ≤ qWeak β ε := by
    have h1 : (25600 : ℝ) ≤ 25600 / ε := by
      rw [le_div_iff₀ hε]
      linarith [mul_le_mul_of_nonneg_left hε1 (by norm_num : (0 : ℝ) ≤ 25600)]
    have h3 : 3 < ⌈25600 / ε * (40 + β)⌉₊ := Nat.lt_ceil.mpr (by
      have := mul_le_mul h1 (show (40 : ℝ) ≤ 40 + β by linarith) (by norm_num) (by positivity)
      push_cast; linarith)
    simp only [qWeak]; omega
  -- the numerical rows, before naming `g`
  obtain ⟨hY1, hYβ, h4T, hYd, hd9, hg3⟩ := OverlapWeak_sizes hβ hε hεα ha hw1
  have hrank := OverlapWeak_rank_le hβ hε hε1 hαβ hα ha hw1 hw2
  have hga : (W : ℝ) ^ (-a) ≤ (W : ℝ) ^ (-α) :=
    Real.rpow_le_rpow_of_exponent_le hw1 (neg_le_neg ha.1)
  have hsqg : Real.sqrt ((W : ℝ) ^ (-a)) ≤ (W : ℝ) ^ (-(α / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hw0.le]
    exact Real.rpow_le_rpow_of_exponent_le hw1 (by linarith [ha.1])
  set q := qWeak β ε with hq
  set p := pWeak β ε with hp
  set g : ℝ := (W : ℝ) ^ (-a) with hg
  have hg0 : 0 < g := Real.rpow_pos_of_pos hw0 _
  set t : ℝ := (levelsWeak W g α β ε 0).t with ht
  have ht0 : 0 < t := by simp only [ht, levelsWeak]; positivity
  set s : ℝ := (W : ℝ) ^ (-(ε / 800)) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hw0 _
  set T : ℝ := W * g ^ 2 * (W : ℝ) ^ (ε / 400) with hT
  have hT0 : 0 < T := by positivity
  set d : ℕ := ⌈8 * (W : ℝ) * g ^ 2 * (W : ℝ) ^ (ε / 200)⌉₊ with hd
  -- the prepared data and the deterministic projections
  obtain ⟨hreg, -, hbv, hcnt⟩ := hRv
  have hRH : R.IsHermitian := hreg.1
  have hPeq : ((g ^ 2 : ℝ) • R) = ((g : ℂ) ^ 2) • R := by
    ext i j
    simp [Complex.real_smul]
  rw [hPeq]
  set B₀ : Matrix (Fin W) (Fin W) ℂ := ((g : ℂ) ^ 2) • R with hB₀
  have hB₀H : B₀.IsHermitian := OverlapWeak_gsq_herm g hRH
  set P := specProj B₀ (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800))) with hP
  obtain ⟨hPH, hPP, -, -⟩ := specProj_spec hB₀H
    (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800)))
  set Q₀ := specProj B₀ {y | s < |y|} with hQ₀
  obtain ⟨hQ₀H, hQ₀Q₀, hB₀Q₀, hQ₀tr⟩ := specProj_spec hB₀H {y | s < |y|}
  have hQ₀re : Q₀.trace.re = (countIn B₀ {y | s < |y|} : ℝ) := by
    rw [hQ₀tr, Complex.natCast_re]
  have hQ₀T : Q₀.trace.re ≤ T := hQ₀re ▸ hcnt
  have hQ₀0 : 0 ≤ Q₀.trace.re := hQ₀re ▸ Nat.cast_nonneg _
  have hsW : s ≤ (W : ℝ) ^ (ε / 800) :=
    Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)
  have h1P : (1 - P) * Q₀ = 1 - P := by
    have hc := (specProj_add_compl hB₀H (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800)))).1
    have h1 : 1 - P = specProj B₀ (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800)))ᶜ := by
      rw [← hc]; abel
    rw [h1]
    refine specProj_mul_of_subset hB₀H fun y hy => ?_
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hy
    simp only [Set.mem_ofPred_eq]
    rcases hy with hy | hy
    · exact lt_of_le_of_lt hsW (lt_abs.mpr (Or.inr (by linarith)))
    · exact lt_of_le_of_lt hsW (lt_abs.mpr (Or.inl hy))
  have hB₀n : ‖(1 - Q₀) * B₀ * (1 - Q₀)‖ ≤ s := by
    have hc := (specProj_add_compl hB₀H {y | s < |y|}).1
    have h1 : 1 - Q₀ = specProj B₀ {y | s < |y|}ᶜ := by rw [← hc]; abel
    obtain ⟨-, hPc2, hPc3, -⟩ := specProj_spec hB₀H {y | s < |y|}ᶜ
    rw [h1, ← hPc3, Matrix.mul_assoc, hPc2]
    refine (norm_mul_specProj_le hB₀H hs0.le (fun y hy => ?_) 0 le_rfl).1
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hy
    exact abs_le.mp hy
  have h1Qn : ‖(1 : Matrix (Fin W) (Fin W) ℂ) - Q₀‖ ≤ 1 :=
    OverlapWeak_norm_proj_le (OverlapWeak_one_sub hQ₀H hQ₀Q₀).1 (OverlapWeak_one_sub hQ₀H hQ₀Q₀).2
  -- the random data of the right cavity
  obtain ⟨Pu, hPu⟩ : ∃ f : Ω W q → Matrix (Fin W) (Fin W) ℂ, ∀ ω, f ω = cavU W g E q t s ω :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨B1, hB1⟩ : ∃ f : Ω W q → Matrix (Fin W) (Fin W) ℂ, ∀ ω,
      f ω = ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7) *
        specProj (((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) {x | |x| ≤ s} := ⟨_, fun _ => rfl⟩
  have hPuP : ∀ ω, (Pu ω).IsHermitian ∧ Pu ω * Pu ω = Pu ω := fun ω => by
    rw [hPu]; exact OverlapWeak_cavU_proj hq7 g E t s ω
  have hPum : Measurable Pu := by
    rw [show Pu = fun ω => cavU W g E q t s ω from funext hPu]
    exact OverlapWeak_cavU_measurable hq7 g E t s
  have hPua : OffBlock W q ⟨4, by omega⟩ Pu := by
    intro ω ω' h
    rw [hPu, hPu]; exact OverlapWeak_cavU_offBlock hq7 g E t s ω ω' h
  have hB1H : ∀ ω, (B1 ω).IsHermitian := fun ω => by
    rw [hB1]
    have hH := OverlapWeak_gsq_herm g (OverlapWeak_cavR_isHermitian W g E q ω (q - 7))
    obtain ⟨hPrH, -, hcomm, -⟩ := specProj_spec hH {x | |x| ≤ s}
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, hPrH.eq, hH.eq, hcomm]
  have hB1n : ∀ ω, ‖B1 ω‖ ≤ s := fun ω => by
    rw [hB1]
    exact (norm_mul_specProj_le (OverlapWeak_gsq_herm g (OverlapWeak_cavR_isHermitian W g E q ω
      (q - 7))) hs0.le (fun x hx => abs_le.mp hx) 0 le_rfl).1
  have hB1m : Measurable B1 := by
    have hR7 := (OverlapWeak_measurable_cavR W g E q (q - 7)).const_smul ((g : ℂ) ^ 2)
    rw [show B1 = fun ω => ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7) *
        specProj (((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) {x | |x| ≤ s} from funext hB1]
    exact OverlapWeak_measurable_mul hR7
      ((measurable_specProj (isClosed_le continuous_abs continuous_const)).comp hR7)
  have hB1a : OffBlock W q ⟨4, by omega⟩ B1 := by
    intro ω ω' h
    have h7 : cavR W g E q ω (q - 7) = cavR W g E q ω' (q - 7) :=
      OverlapWeak_cavR_offBlock W g E q ⟨4, by omega⟩ (q - 7) (by simp; omega) ω ω' h
    rw [hB1, hB1, h7]
  -- the sizes of Lemma 9.5 [us:lem:range] and of (9.50) [us:eq:absolute]
  have hWδ : (W : ℝ) ^ ((1 - 2 * β) / 4) ≤ d :=
    ((Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)).trans hYβ).trans hYd
  have hdmeso : (d : ℝ) ≤ (9 * (W : ℝ) ^ (-(3 * α / 2))) * W :=
    calc (d : ℝ) ≤ 9 * (W * (g ^ 2 * (W : ℝ) ^ (ε / 200))) := hd9
      _ ≤ 9 * (W * (W : ℝ) ^ (-(3 * α / 2))) := by gcongr
      _ = (9 * (W : ℝ) ^ (-(3 * α / 2))) * W := by ring
  have hdε₁ : (d : ℝ) ≤ ε₁ * W := hdmeso.trans (mul_le_mul_of_nonneg_right
    (hw9.trans ((min_le_left _ _).trans (min_le_left _ _))) hw0.le)
  have hdε₂ : (d : ℝ) ≤ ε₂ * W := hdmeso.trans (mul_le_mul_of_nonneg_right
    (hw9.trans ((min_le_left _ _).trans (min_le_right _ _))) hw0.le)
  have hdW : d ≤ W := by
    have h1 : (d : ℝ) ≤ 1 * W := hdmeso.trans
      (mul_le_mul_of_nonneg_right (hw9.trans (min_le_right _ _)) hw0.le)
    rw [one_mul] at h1
    exact_mod_cast h1
  have hsε₁ : s ≤ ε₁ := by
    have := hws.trans (min_le_left _ _); linarith
  have hsε₂ : 2 * s ≤ ε₂ := hws.trans (min_le_right _ _)
  -- the suffix event `S` (blocks `5, …, q - 2`)
  set S : Set (Ω W q) := {ω | (Pu ω).trace.re + 2 * Q₀.trace.re + 1 ≤ d ∧
    ‖Q₀ * Pu ω‖ ≤ CT * Real.sqrt (d / W)} with hS
  have hSm : MeasurableSet S := by
    have hf : Measurable fun ω => (Pu ω).trace.re + 2 * Q₀.trace.re + 1 :=
      (((Complex.continuous_re.comp (continuous_id.matrix_trace)).measurable.comp
        hPum).add_const _).add_const _
    have hn : Measurable fun ω => ‖Q₀ * Pu ω‖ :=
      (continuous_norm.comp (continuous_const.matrix_mul continuous_id)).measurable.comp hPum
    exact (measurableSet_le hf measurable_const).inter (measurableSet_le hn measurable_const)
  have hSa : OffBlock W q ⟨4, by omega⟩ (· ∈ S) := by
    intro ω ω' h
    simp only [hS, Set.mem_ofPred_eq, hPua ω ω' h]
  -- the three fresh-block events
  set Gr : (Fin W → ℂ) → Set (Ω W q) := fun u => {ω | ω ∈ S ∧ ¬ ∀ x, (1 - Pu ω) *ᵥ
      ((gueBlock W q ω ⟨4, by omega⟩ - (E : ℂ) • 1 - B₀ - B1 ω) *ᵥ x) = 0 →
        l2Norm ((Matrix.of fun (_ : Fin 1) j => star (u j)) *ᵥ x) ^ 2 ≤
          C₁ * (d / W) * Real.log W ^ 2 * (star u ⬝ᵥ ((1 + B₀ * B₀)⁻¹ *ᵥ u)).re *
            l2Norm x ^ 2} with hGr
  have hGrel : ∀ u : Fin W → ℂ, μ W q (Gr u) ≤
      ENNReal.ofReal ((W : ℝ) ^ (-(1 : ℝ)) + C₁ * Real.exp (-(c₁ * d))) := by
    intro u
    refine OverlapWeak_fresh_event (by omega) hPum hB1m hPua hB1a hSm hSa E B₀ _ _ fun ω hω => ?_
    obtain ⟨htr, hov⟩ := hω
    refine (measure_mono fun ω' hω' => ?_).trans (hW₁ W d hW1 hWδ hdε₁ B₀ Q₀ (B1 ω) (Pu ω) u E
      hB₀H hQ₀H hQ₀Q₀ hB₀Q₀.symm (hB₀n.trans hsε₁) (hB1H ω) ((hB1n ω).trans hsε₁) (hPuP ω).1
      (hPuP ω).2 hov htr hE)
    obtain ⟨x, hx1, hx2⟩ := hω'
    exact ⟨x, hx1, by rwa [OverlapWeak_l2Norm_row] at hx2⟩
  set Gc : Set (Ω W q) := {ω | ω ∈ S ∧ ¬ ∀ x, (1 - Pu ω) *ᵥ
      ((gueBlock W q ω ⟨4, by omega⟩ - (E : ℂ) • 1 - B₀ - B1 ω) *ᵥ x) = 0 →
        l2Norm (Q₀ *ᵥ x) ^ 2 ≤ (C₂ * Real.sqrt (d / W)) ^ 2 * l2Norm x ^ 2} with hGcd
  have hGc : μ W q Gc ≤ ENNReal.ofReal ((W : ℝ) ^ (-(1 : ℝ)) + C₂ * Real.exp (-(c₂ * d))) := by
    refine OverlapWeak_fresh_event (by omega) hPum hB1m hPua hB1a hSm hSa E B₀ _ _ fun ω hω => ?_
    obtain ⟨htr, -⟩ := hω
    have htr' : (Pu ω).trace.re + Q₀.trace.re ≤ d := by linarith
    have hBn : ‖(1 - Q₀) * (B₀ + B1 ω) * (1 - Q₀)‖ ≤ ε₂ := by
      rw [mul_add, add_mul]
      calc ‖(1 - Q₀) * B₀ * (1 - Q₀) + (1 - Q₀) * B1 ω * (1 - Q₀)‖
          ≤ ‖(1 - Q₀) * B₀ * (1 - Q₀)‖ + ‖(1 - Q₀) * B1 ω * (1 - Q₀)‖ := norm_add_le _ _
        _ ≤ s + 1 * s * 1 := by
            gcongr
            refine (norm_mul_le _ _).trans ?_
            refine mul_le_mul ((norm_mul_le _ _).trans ?_) h1Qn (norm_nonneg _) (by positivity)
            exact mul_le_mul h1Qn (hB1n ω) (norm_nonneg _) zero_le_one
        _ ≤ ε₂ := by linarith
    refine (measure_mono fun ω' hω' => ?_).trans (hW₂ W d hW2 hWδ hdε₂ hdW (Pu ω) Q₀ (B₀ + B1 ω) E
      (hPuP ω).1 (hPuP ω).2 hQ₀H hQ₀Q₀ htr' (hB₀H.add (hB1H ω)) hBn hE)
    obtain ⟨x, hx1, hx2⟩ := hω'
    refine ⟨x, by rwa [← sub_sub], ?_⟩
    exact lt_of_pow_lt_pow_left₀ 2 (OverlapWeak_l2Norm_nonneg _) (by rwa [mul_pow])
  -- the events of the suffix: rank (9.53) [su:eq:retained-rank-moment], count (9.58)
  -- [us:eq:wegner], Haar overlap (9.56) [us:eq:Haar]
  have hcavR7 : ∀ ω, cavR W g E q ω (q - 7) = (gueBlock W q ω ⟨5, by omega⟩ - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • cavR W g E q ω (q - 8))⁻¹ := by
    intro ω
    have h7 : q - 7 = (q - 8) + 1 := by omega
    have h5 : q - 3 - (q - 8) = 5 := by omega
    rw [h7]
    simp only [cavR]
    rw [h5]
    simp [blockSeq, show 5 < q by omega]
  have hblk4 : ∀ ω, blockSeq W q ω 4 = gueBlock W q ω ⟨4, by omega⟩ := by
    intro ω; simp [blockSeq, show 4 < q by omega]
  set F1 : Set (Ω W q) := {ω | 2 * t ^ (-p) * (W : ℝ) ^ (1 + ε / 3200) <
    rankSurr t ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6))} with hF1d
  have hF1 : μ W q F1 ≤ ENNReal.ofReal (CR * ((W : ℝ) ^ (-δ₀) + Real.sqrt g)) :=
    hRk W hWR g E t hg0 (hga.trans hwg₀) hE ht0
  set F2 : Set (Ω W q) := {ω | ω ∈ (Set.univ : Set (Ω W q)) ∧ T < (countIn (((g : ℂ) ^ 2) •
    (gueBlock W q ω ⟨5, by omega⟩ - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • cavR W g E q ω (q - 8))⁻¹)
      {x | s < |x|} : ℝ)} with hF2d
  have hF2 : μ W q F2 ≤ ENNReal.ofReal (2 * CF * W * g ^ 2 / (s * T)) * μ W q Set.univ :=
    hFr W q ⟨5, by omega⟩ (fun ω => cavR W g E q ω (q - 8)) Set.univ hW1n
      (OverlapWeak_measurable_cavR W g E q (q - 8))
      (fun ω => OverlapWeak_cavR_isHermitian W g E q ω (q - 8))
      (OverlapWeak_cavR_offBlock W g E q ⟨5, by omega⟩ (q - 8) (by simp; omega))
      MeasurableSet.univ (fun _ _ _ => rfl) g E s T hs0 hT0
  set F3 : Set (Ω W q) := {ω | CT * Real.sqrt (((cavU W g E q t s ω).trace.re + Q₀.trace.re +
    W * g ^ 2) / W) < ‖Q₀ * cavU W g E q t s ω‖} with hF3d
  have hF3 : μ W q F3 ≤ ENNReal.ofReal (CT * Real.exp (-cT * (W * g ^ 2))) :=
    hHaar W q hW1n hq7 g E t s Q₀ hQ₀H hQ₀Q₀ (W * g ^ 2) (by positivity)
  -- numerical consequences
  have hp2 : p ≤ 2 := by
    have hq5 : (1 : ℝ) ≤ (q : ℝ) - 5 := by
      have : (8 : ℝ) ≤ q := by exact_mod_cast hq8
      linarith
    exact hpq.le.trans (div_le_self (by norm_num) hq5)
  have hTg : (W : ℝ) * g ^ 2 ≤ T :=
    le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hw1 (by positivity))
  have hdW' : (d : ℝ) / W ≤ 9 * (g ^ 2 * (W : ℝ) ^ (ε / 200)) := by
    rw [div_le_iff₀ hw0]
    exact hd9.trans (le_of_eq (by ring))
  have hdW'' : (d : ℝ) / W ≤ 9 * (W : ℝ) ^ (-(3 * α / 2)) := hdW'.trans (by linarith [hg3])
  have hdW0 : 0 ≤ (d : ℝ) / W := by positivity
  have hk1 : 1 ≤ ⌈1 / α⌉₊ := Nat.one_le_iff_ne_zero.mpr
    (Nat.ceil_pos.mpr (by positivity)).ne'
  have hkα : 1 ≤ α * (⌈1 / α⌉₊ : ℝ) := by
    have := Nat.le_ceil (1 / α)
    rw [div_le_iff₀ hα] at this
    linarith
  have hlog0 : 0 ≤ Real.log W ^ 2 := sq_nonneg _
  have hcut12 := OverlapWeak_cut12 (Cp := Cp) hw1 hC₁ hCp hdW' hdW'' hwlog1 hwlog2
  have hcut3 := OverlapWeak_cut3 (C₂ := C₂) hw1 hdW0 hdW'' hkα hwk
  -- the deterministic step: off the six events, the three conclusions hold
  refine le_trans (measure_mono (t := F1 ∪ F2 ∪ F3 ∪ Gr v ∪ Gr (P *ᵥ v) ∪ Gc) ?_) ?_
  · intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hcon
    apply hω
    simp only [hF1d, hF2d, hF3d, Set.mem_ofPred_eq, not_lt, Set.mem_univ, true_and] at h1 h2 h3
    -- `ω ∈ S`
    have hc1 := (countIn_le_rankSurr (cavProd W g E q ω (q - 6)) ht0 hp0 hp2).1
    have hTrPu : (Pu ω).trace.re ≤ T + T := by
      rw [hPu]
      have hU := OverlapWeak_trace_union_le
        (Matrix.isHermitian_conjTranspose_mul_self (cavProd W g E q ω (q - 6)))
        (OverlapWeak_gsq_herm g (OverlapWeak_cavR_isHermitian W g E q ω (q - 7))) (t ^ 2)
        {x | s < |x|}
      have hc2 : (countIn (((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) {x | s < |x|} : ℝ) ≤ T := by
        rw [hcavR7]; exact h2
      have hrk : 2 * t ^ (-p) * (W : ℝ) ^ (1 + ε / 3200) ≤ T := hrank
      exact hU.trans (add_le_add (hc1.trans (h1.trans hrk)) hc2)
    have hSω : ω ∈ S := by
      refine ⟨by linarith only [hTrPu, hQ₀T, h4T], ?_⟩
      rw [hPu]
      refine h3.trans ?_
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hCT.le
      have hTrPu' : (cavU W g E q t s ω).trace.re ≤ T + T := hPu ω ▸ hTrPu
      exact div_le_div_of_nonneg_right (by linarith only [hTrPu', hQ₀T, h4T, hTg]) hw0.le
    have hgv := not_not.mp (not_and.mp h4 hSω)
    have hgPv := not_not.mp (not_and.mp h5 hSω)
    have hgc := not_not.mp (not_and.mp h6 hSω)
    have hB₀sq : B₀ * B₀ = ((g : ℂ) ^ 4) • (R * R) := by
      rw [hB₀, smul_mul_smul_comm, ← pow_add]
    refine OverlapWeak_det hq7 g E t s R ω v hB₀H hB₀ hPH hPP h1P (Nat.succ_le_iff.mp hk1)
      (by positivity) hCp.le (by positivity) (by rw [hB₀sq]; exact hbv)
      (by simp only [levelsWeak]; positivity)
      hcut12.1 hcut12.2 hcut3 (fun u x hu hx => ?_) (fun x hx => ?_)
    · rw [← hPu ω, hblk4, ← hB1 ω] at hx
      rcases hu with rfl | rfl
      · have h := hgv x hx
        rwa [OverlapWeak_l2Norm_row] at h
      · have h := hgPv x hx
        rwa [OverlapWeak_l2Norm_row] at h
    · rw [← hPu ω, hblk4, ← hB1 ω] at hx
      exact hgc x hx
  · -- the six failure probabilities
    have hy1 : μ W q F1 ≤ ENNReal.ofReal (CR * ((W : ℝ) ^ (-δ₀) + (W : ℝ) ^ (-(α / 2)))) :=
      hF1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hsqg) hCR.le))
    have hy2 : μ W q F2 ≤ ENNReal.ofReal (2 * CF * (W : ℝ) ^ (-(ε / 800))) := by
      rw [measure_univ, mul_one, hT, hs, OverlapWeak_count_fail hw0 hg0] at hF2
      exact hF2
    have hexpd : ∀ c : ℝ, 0 < c → Real.exp (-(c * d)) ≤
        Real.exp (-(c * (W : ℝ) ^ (1 - 2 * β))) := fun c hc =>
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (hYβ.trans hYd) hc.le))
    have hy3 : μ W q F3 ≤ ENNReal.ofReal (CT * Real.exp (-(cT * (W : ℝ) ^ (1 - 2 * β)))) :=
      hF3.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (by rw [neg_mul]; exact neg_le_neg (mul_le_mul_of_nonneg_left hYβ hcT.le))) hCT.le))
    have hy4 : ∀ u, μ W q (Gr u) ≤ ENNReal.ofReal ((W : ℝ) ^ (-(1 : ℝ)) +
        C₁ * Real.exp (-(c₁ * (W : ℝ) ^ (1 - 2 * β)))) := fun u =>
      (hGrel u).trans (ENNReal.ofReal_le_ofReal (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hexpd c₁ hc₁) hC₁.le)))
    have hy6 : μ W q Gc ≤ ENNReal.ofReal ((W : ℝ) ^ (-(1 : ℝ)) +
        C₂ * Real.exp (-(c₂ * (W : ℝ) ^ (1 - 2 * β)))) :=
      hGc.trans (ENNReal.ofReal_le_ofReal (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hexpd c₂ hc₂) hC₂.le)))
    exact OverlapWeak_union_le _ hy1 hy2 hy3 (hy4 v) (hy4 (P *ᵥ v)) hy6 (by positivity)
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      (by linarith only [hwfail])

end LSBA
