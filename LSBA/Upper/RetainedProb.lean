import LSBA.Upper.RetainedSpace
import LSBA.Upper.ProductMoment
import LSBA.Gauss.HaarSubspace
import LSBA.Spectral.RankTrace
import LSBA.Upper.CoercivityMap

/-!
# Probability bounds for the retained space

Section 9.4.1 [su:sec:retained-geometry]. The rank estimate (9.53) [su:eq:retained-rank-moment]:
the right product `A` is the adjoint of the product of the Riccati chain on the reversed
right-cavity window started at the regular state `0`, so Lemma G.2 [us:lem:product] with
`h = q - 6` gives `Tr |A|^p ≤ W^{1+e}` and the rank surrogate of `A* A` is at most
`2 t^{-p} W^{1+e}`, except with probability `C (W^{-δ₀} + g^{1/2})`. The singular values of `A`
avoid the threshold `t` almost surely (Section 9.4.4 [su:sec:cutoff-estimates]: clearing the
inverse denominators in `V_6` gives a nonzero polynomial), so a deterministic level bounds
`‖(A* A - t²)⁻¹‖²_HS` with arbitrarily small failure. The transversality (9.56) [us:eq:Haar]:
`U` is a function of the right-cavity window, equivariant under common conjugation, so for a
fixed projection `Q₀`, `‖Q₀ P_U‖ ≤ C √((dim U + rank Q₀ + s)/W)` except with probability
`C e^{-c s}`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Measurability of the Riccati product on the right-cavity window -/

private lemma RetainedProb_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
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

private lemma RetainedProb_measurable_mul {W : ℕ} {α : Type*} [MeasurableSpace α]
    {F G : α → Matrix (Fin W) (Fin W) ℂ} (hF : Measurable F) (hG : Measurable G) :
    Measurable fun x => F x * G x := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => hF.eval_matrix.mul hG.eval_matrix

private lemma RetainedProb_measurable_conjTranspose {W : ℕ} {α : Type*} [MeasurableSpace α]
    {F : α → Matrix (Fin W) (Fin W) ℂ} (hF : Measurable F) :
    Measurable fun x => (F x)ᴴ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.conjTranspose_apply]
  exact continuous_star.measurable.comp hF.eval_matrix

private lemma RetainedProb_measurable_block (W h : ℕ) (j : ℕ) :
    Measurable fun ω : Ω W h =>
      (if hj : j < h then gueBlock W h ω ⟨j, hj⟩ else 0 : Matrix (Fin W) (Fin W) ℂ) := by
  by_cases hj : j < h
  · simp only [hj, ↓reduceDIte]
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k => ?_
    unfold gueBlock
    simp only [Matrix.of_apply]
    split_ifs <;> fun_prop
  · simp only [hj, ↓reduceDIte]
    exact measurable_const

private lemma RetainedProb_measurable_chain (W : ℕ) (g E : ℝ) (h : ℕ)
    (R : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    Measurable fun ω : Ω W h => ricChain W g E h R ω j := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    simp only [ricChain]
    refine RetainedProb_measurable_inv.comp ?_
    exact ((RetainedProb_measurable_block W h j).sub measurable_const).sub
      (ih.fun_const_smul ((g : ℂ) ^ 2))

private lemma RetainedProb_measurable_prod (W : ℕ) (g E : ℝ) (h : ℕ)
    (R : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    Measurable fun ω : Ω W h => ricProd W g E h R ω j := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    simp only [ricProd]
    exact RetainedProb_measurable_mul (RetainedProb_measurable_chain W g E h R (j + 1)) ih

private lemma RetainedProb_measurable_hsSq {W : ℕ} {α : Type*} [MeasurableSpace α]
    {F : α → Matrix (Fin W) (Fin W) ℂ} (hF : Measurable F) :
    Measurable fun x => hsSq (F x) := by
  unfold hsSq
  exact Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
    (hF.eval_matrix (i := a) (j := b)).norm.pow_const 2

/-! ### The right-cavity window -/

private lemma RetainedProb_cavWin_injective (q : ℕ) : Function.Injective (cavWin q) := by
  intro a b hab
  have h := congrArg Fin.val hab
  have ha := a.isLt
  have hb := b.isLt
  simp only [cavWin] at h
  ext
  omega

/-- An event of the right-cavity window has at most the probability of the window event. -/
private lemma RetainedProb_preimage_le {W q : ℕ} (S : Set (Ω W (q - 6))) :
    μ W q (windowSample (cavWin q) ⁻¹' S) ≤ μ W (q - 6) S := by
  have hmp := measurePreserving_windowSample W q (q - 6) (RetainedProb_cavWin_injective q)
  calc μ W q (windowSample (cavWin q) ⁻¹' S)
      ≤ (μ W q).map (windowSample (cavWin q)) S :=
        Measure.le_map_apply hmp.measurable.aemeasurable S
    _ = μ W (q - 6) S := by rw [hmp.map_eq]

/-! ### Singular values avoid a fixed level almost surely

Section 9.4.4 [su:sec:cutoff-estimates]. -/

/-- For Hermitian `X`, if `X⁻¹ B (X⁻¹ B)* - t²` is singular then so is `B B* - t² X²`. -/
private lemma RetainedProb_det_eq_zero {W : ℕ} {X B : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) {t : ℝ} (ht : 0 < t)
    (h : ¬ IsUnit (X⁻¹ * B * (X⁻¹ * B)ᴴ - ((t ^ 2 : ℝ) : ℂ) • 1)) :
    (B * Bᴴ - ((t ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) * (X * X)).det = 0 := by
  set c : ℂ := ((t ^ 2 : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact_mod_cast (pow_pos ht 2).ne'
  by_cases hXu : IsUnit X.det
  · have hinv : X⁻¹ᴴ = X⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hX.eq]
    have h1 : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hXu
    have h2 : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hXu
    have heq : X⁻¹ * B * (X⁻¹ * B)ᴴ - c • 1 =
        X⁻¹ * (B * Bᴴ - c • (1 : Matrix (Fin W) (Fin W) ℂ) * (X * X)) * X⁻¹ := by
      rw [Matrix.conjTranspose_mul, hinv, Matrix.mul_sub, Matrix.sub_mul]
      congr 1
      · simp only [Matrix.mul_assoc]
      · rw [smul_one_mul, Matrix.mul_smul, Matrix.smul_mul]
        congr 1
        simp only [← Matrix.mul_assoc, h1, Matrix.one_mul, h2]
    rw [heq] at h
    by_contra hd
    apply h
    have hu : IsUnit (B * Bᴴ - c • (1 : Matrix (Fin W) (Fin W) ℂ) * (X * X)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
    have hXi : IsUnit X⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr
      ((Matrix.isUnit_iff_isUnit_det X).mpr hXu)
    exact (hXi.mul hu).mul hXi
  · exfalso
    apply h
    rw [Matrix.nonsing_inv_apply_not_isUnit X hXu]
    simp only [Matrix.zero_mul, Matrix.conjTranspose_zero, Matrix.mul_zero, zero_sub]
    rw [Matrix.isUnit_iff_isUnit_det]
    refine isUnit_iff_ne_zero.mpr ?_
    rw [Matrix.det_neg, Matrix.det_smul, Matrix.det_one, mul_one]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hc0)

/-- `B B* - c` is invertible for some `c = t² l²`: the spectrum of `B B*` is finite. -/
private lemma RetainedProb_exists_level {W : ℕ} (B : Matrix (Fin W) (Fin W) ℂ) {t : ℝ}
    (ht : 0 < t) :
    ∃ l : ℝ, (B * Bᴴ - ((t ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) *
      (((l : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) * ((l : ℂ) • 1))).det ≠ 0 := by
  have hfin : (spectrum ℝ (B * Bᴴ)).Finite := Matrix.finite_real_spectrum
  obtain ⟨c, hc0, hcS⟩ := ((Set.Ioi_infinite (0 : ℝ)).sdiff hfin).nonempty
  refine ⟨Real.sqrt c / t, ?_⟩
  have hc : ((t ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) *
      ((((Real.sqrt c / t : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) *
        (((Real.sqrt c / t : ℝ) : ℂ) • 1)) = ((c : ℝ) : ℂ) • 1 := by
    rw [smul_one_mul, smul_one_mul, smul_smul, smul_smul]
    congr 1
    have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt (le_of_lt hc0)
    have ht0 : t ≠ 0 := ht.ne'
    have hr : t ^ 2 * (Real.sqrt c / t * (Real.sqrt c / t)) = c := by
      rw [div_mul_div_comm, hsq]
      field_simp
    rw [mul_assoc]
    exact_mod_cast hr
  rw [hc]
  have hu : IsUnit (algebraMap ℝ (Matrix (Fin W) (Fin W) ℂ) c - B * Bᴴ) := by
    by_contra hn
    exact hcS (spectrum.mem_iff.mpr hn)
  rw [Algebra.algebraMap_eq_smul_one, RCLike.real_smul_eq_coe_smul (K := ℂ)] at hu
  have hneg : B * Bᴴ - ((c : ℝ) : ℂ) • 1 = -(((c : ℝ) : ℂ) • 1 - B * Bᴴ) := by abel
  rw [hneg]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu.neg).ne_zero

/-- The entry `(α, β)` of the GUE block of `Ω W 1` as a polynomial in the coordinates. -/
private def RetainedProb_entry (W : ℕ) (α β : Fin W) : MvPolynomial (Fin 1 × Fin W × Fin W) ℂ :=
  if α = β then MvPolynomial.X (0, α, α) * MvPolynomial.C (((Real.sqrt W : ℝ) : ℂ)⁻¹)
  else if α < β then
    (MvPolynomial.X (0, α, β) + MvPolynomial.C Complex.I * MvPolynomial.X (0, β, α)) *
      MvPolynomial.C (((Real.sqrt (2 * W) : ℝ) : ℂ)⁻¹)
  else
    (MvPolynomial.X (0, β, α) - MvPolynomial.C Complex.I * MvPolynomial.X (0, α, β)) *
      MvPolynomial.C (((Real.sqrt (2 * W) : ℝ) : ℂ)⁻¹)

private lemma RetainedProb_eval_entry {W : ℕ} (v : Ω W 1) (α β : Fin W) :
    MvPolynomial.eval (fun i => (v i : ℂ)) (RetainedProb_entry W α β) = gueBlock W 1 v 0 α β := by
  simp only [RetainedProb_entry, gueBlock, Matrix.of_apply]
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

/-- For fixed Hermitian `M` and `B`, the set of one-block samples `v` with
`(V - M)⁻¹ B ((V - M)⁻¹ B)* - t²` singular, `V` the block of `v`, is null. -/
private lemma RetainedProb_block_null {W : ℕ} {M : Matrix (Fin W) (Fin W) ℂ} (hM : M.IsHermitian)
    (B : Matrix (Fin W) (Fin W) ℂ) {t : ℝ} (ht : 0 < t) :
    μ W 1 {v | ¬ IsUnit ((gueBlock W 1 v 0 - M)⁻¹ * B * ((gueBlock W 1 v 0 - M)⁻¹ * B)ᴴ -
      ((t ^ 2 : ℝ) : ℂ) • 1)} = 0 := by
  set Vp : Matrix (Fin W) (Fin W) (MvPolynomial (Fin 1 × Fin W × Fin W) ℂ) :=
    Matrix.of fun α β => RetainedProb_entry W α β with hVp
  set Xp := Vp - M.map MvPolynomial.C with hXp
  set P : MvPolynomial (Fin 1 × Fin W × Fin W) ℂ :=
    ((B * Bᴴ).map MvPolynomial.C -
      ((((t ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)).map MvPolynomial.C) * (Xp * Xp)).det
    with hP
  have hCm : ∀ (f : Fin 1 × Fin W × Fin W → ℂ) (N : Matrix (Fin W) (Fin W) ℂ),
      (MvPolynomial.eval f).mapMatrix (N.map MvPolynomial.C) = N := by
    intro f N
    ext α β
    simp [RingHom.mapMatrix_apply]
  have hev : ∀ v : Ω W 1, MvPolynomial.eval (fun i => (v i : ℂ)) P =
      (B * Bᴴ - ((t ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) *
        ((gueBlock W 1 v 0 - M) * (gueBlock W 1 v 0 - M))).det := by
    intro v
    have hV : (MvPolynomial.eval fun i => (v i : ℂ)).mapMatrix Vp = gueBlock W 1 v 0 := by
      ext α β
      simp [RingHom.mapMatrix_apply, hVp, RetainedProb_eval_entry]
    rw [hP, RingHom.map_det, map_sub, map_mul, hCm, hCm, hXp, map_mul, map_sub, hCm, hV]
  have hsub : {v : Ω W 1 | ¬ IsUnit ((gueBlock W 1 v 0 - M)⁻¹ * B *
      ((gueBlock W 1 v 0 - M)⁻¹ * B)ᴴ - ((t ^ 2 : ℝ) : ℂ) • 1)} ⊆
      {v | MvPolynomial.eval (fun i => (v i : ℂ)) P = 0} := by
    intro v hv
    rw [Set.mem_ofPred_eq, hev]
    exact RetainedProb_det_eq_zero ((gueBlock_isHermitian W 1 v 0).sub hM) ht hv
  obtain ⟨l, hl⟩ := RetainedProb_exists_level B ht
  have hMl : (M + ((l : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ))).IsHermitian :=
    hM.add (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal]))
  set v₀ : Ω W 1 := gueCoord W 1 (fun _ => M + (l : ℂ) • 1) with hv₀
  have hv₀B : gueBlock W 1 v₀ 0 = M + (l : ℂ) • 1 :=
    congrFun (gueBlock_gueCoord W 1 (fun _ => M + (l : ℂ) • 1) (fun _ => hMl)) 0
  have hP₀ : MvPolynomial.eval (fun i => (v₀ i : ℂ)) P ≠ 0 := by
    rw [hev, hv₀B, add_sub_cancel_left]
    exact hl
  have : NullSingletonClass (gaussianReal (0 : ℝ) 1) :=
    nullSingletonClass_gaussianReal one_ne_zero
  have hnull := measure_zero_mvPolynomial (fun _ : Fin 1 × Fin W × Fin W => gaussianReal 0 1) P
    (fun i => v₀ i) hP₀
  exact measure_mono_null hsub hnull

/-- The chain and the product up to step `k` do not see the last block of `Ω W (k + 1)`. -/
private lemma RetainedProb_chain_join {W k : ℕ} (g E : ℝ) {s : Fin 1 → Fin (k + 1)}
    (hs : ∀ i, s i = Fin.last k) (v v' : Ω W 1)
    (e : {p : Fin (k + 1) × Fin W × Fin W // p.1 ∉ Set.range s} → ℝ) (j : ℕ) (hj : j ≤ k) :
    ricChain W g E (k + 1) 0 (windowJoin s v e) j =
        ricChain W g E (k + 1) 0 (windowJoin s v' e) j ∧
      ricProd W g E (k + 1) 0 (windowJoin s v e) j =
        ricProd W g E (k + 1) 0 (windowJoin s v' e) j := by
  induction j with
  | zero => exact ⟨rfl, rfl⟩
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hjk : j < k + 1 := by omega
    have hb : gueBlock W (k + 1) (windowJoin s v e) ⟨j, hjk⟩ =
        gueBlock W (k + 1) (windowJoin s v' e) ⟨j, hjk⟩ := by
      refine gueBlock_windowJoin_of_not_mem _ v v' e ?_
      rintro ⟨i, hi⟩
      rw [hs i] at hi
      simp only [Fin.ext_iff, Fin.val_last] at hi
      omega
    have hc : ricChain W g E (k + 1) 0 (windowJoin s v e) (j + 1) =
        ricChain W g E (k + 1) 0 (windowJoin s v' e) (j + 1) := by
      simp only [ricChain, hjk, ↓reduceDIte, hb, h1]
    refine ⟨hc, ?_⟩
    simp only [ricProd, hc, h2]

/-- Section 9.4.4 [su:sec:cutoff-estimates]: on the window `Ω W h`, `h ≥ 1`, the product
`Y = ricProd … h` from `0` has `t > 0` as a singular value only on a null set. -/
private lemma RetainedProb_null (W h : ℕ) (hh : 1 ≤ h) (g E t : ℝ) (ht : 0 < t) :
    μ W h {w | ¬ IsUnit (ricProd W g E h 0 w h * (ricProd W g E h 0 w h)ᴴ -
      ((t ^ 2 : ℝ) : ℂ) • 1)} = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  set s : Fin 1 → Fin (k + 1) := fun _ => Fin.last k with hs
  have hsi : Function.Injective s := fun a b _ => Subsingleton.elim a b
  set S : Set (Ω W (k + 1)) := {w | ¬ IsUnit (ricProd W g E (k + 1) 0 w (k + 1) *
      (ricProd W g E (k + 1) 0 w (k + 1))ᴴ - ((t ^ 2 : ℝ) : ℂ) • 1)} with hS
  have hN : Measurable fun w : Ω W (k + 1) => ricProd W g E (k + 1) 0 w (k + 1) *
      (ricProd W g E (k + 1) 0 w (k + 1))ᴴ - ((t ^ 2 : ℝ) : ℂ) • 1 :=
    (RetainedProb_measurable_mul (RetainedProb_measurable_prod W g E (k + 1) 0 (k + 1))
      (RetainedProb_measurable_conjTranspose
        (RetainedProb_measurable_prod W g E (k + 1) 0 (k + 1)))).sub measurable_const
  have hSm : MeasurableSet S := by
    have : S = (fun w : Ω W (k + 1) => (ricProd W g E (k + 1) 0 w (k + 1) *
        (ricProd W g E (k + 1) 0 w (k + 1))ᴴ - ((t ^ 2 : ℝ) : ℂ) • 1).det) ⁻¹' {0} := by
      ext w
      simp [hS, Matrix.isUnit_iff_isUnit_det]
    rw [this]
    exact (continuous_id.matrix_det.measurable.comp hN) (measurableSet_singleton 0)
  have key : ∀ e, ∫⁻ v, S.indicator (1 : Ω W (k + 1) → ℝ≥0∞) (windowJoin s v e) ∂(μ W 1) = 0 := by
    intro e
    set M : Matrix (Fin W) (Fin W) ℂ := (E : ℂ) • 1 + ((g : ℂ) ^ 2) •
      ricChain W g E (k + 1) 0 (windowJoin s 0 e) k with hM
    set B := ricProd W g E (k + 1) 0 (windowJoin s 0 e) k with hB
    have hMH : M.IsHermitian := by
      refine Matrix.IsHermitian.add ?_ ?_
      · exact Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal])
      · have := ricChain_isHermitian (W := W) (h := k + 1) (g := g) (E := E)
          Matrix.isHermitian_zero (windowJoin s 0 e) k
        unfold Matrix.IsHermitian at this ⊢
        rw [Matrix.conjTranspose_smul, this, Complex.star_def, map_pow, Complex.conj_ofReal]
    have hY : ∀ v, ricProd W g E (k + 1) 0 (windowJoin s v e) (k + 1) =
        (gueBlock W 1 v 0 - M)⁻¹ * B := by
      intro v
      obtain ⟨h1, h2⟩ := RetainedProb_chain_join g E (s := s) (fun _ => rfl) v 0 e k le_rfl
      have hblk : gueBlock W (k + 1) (windowJoin s v e) ⟨k, Nat.lt_succ_self k⟩ =
          gueBlock W 1 v 0 := gueBlock_windowJoin_apply hsi v e 0
      simp only [ricProd, ricChain, Nat.lt_succ_self, ↓reduceDIte, hblk, h1, h2, hM, hB,
        sub_sub]
    have hle : ∀ v, S.indicator (1 : Ω W (k + 1) → ℝ≥0∞) (windowJoin s v e) ≤
        {v : Ω W 1 | ¬ IsUnit ((gueBlock W 1 v 0 - M)⁻¹ * B *
          ((gueBlock W 1 v 0 - M)⁻¹ * B)ᴴ - ((t ^ 2 : ℝ) : ℂ) • 1)}.indicator 1 v := by
      intro v
      by_cases hv : windowJoin s v e ∈ S
      · have hv' : v ∈ {v : Ω W 1 | ¬ IsUnit ((gueBlock W 1 v 0 - M)⁻¹ * B *
            ((gueBlock W 1 v 0 - M)⁻¹ * B)ᴴ - ((t ^ 2 : ℝ) : ℂ) • 1)} := by
          have := hv
          simp only [hS, Set.mem_ofPred_eq, hY] at this
          exact this
        rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv']
        simp
      · rw [Set.indicator_of_notMem hv]
        exact zero_le
    refine le_antisymm ?_ zero_le
    calc ∫⁻ v, S.indicator (1 : Ω W (k + 1) → ℝ≥0∞) (windowJoin s v e) ∂(μ W 1)
        ≤ ∫⁻ v, {v : Ω W 1 | ¬ IsUnit ((gueBlock W 1 v 0 - M)⁻¹ * B *
          ((gueBlock W 1 v 0 - M)⁻¹ * B)ᴴ - ((t ^ 2 : ℝ) : ℂ) • 1)}.indicator
            (1 : Ω W 1 → ℝ≥0∞) v ∂(μ W 1) :=
          lintegral_mono hle
      _ ≤ μ W 1 {v : Ω W 1 | ¬ IsUnit ((gueBlock W 1 v 0 - M)⁻¹ * B *
          ((gueBlock W 1 v 0 - M)⁻¹ * B)ᴴ - ((t ^ 2 : ℝ) : ℂ) • 1)} :=
          lintegral_indicator_one_le _
      _ = 0 := RetainedProb_block_null hMH B ht
  have hint := lintegral_windowJoin W (k + 1) 1 hsi (F := S.indicator 1)
    (measurable_one.indicator hSm)
  rw [lintegral_indicator_one hSm] at hint
  rw [hint]
  simp only [key, lintegral_zero]


/-- (9.53) [su:eq:retained-rank-moment] with Lemma G.2 [us:lem:product] at `h = q - 6`: for
`0 < p < 2/(q - 5)`, `e > 0` and `t > 0`, `rankSurr t (A* A) ≤ 2 t^{-p} W^{1+e}` except with
probability `C (W^{-δ₀} + g^{1/2})`, uniformly in `0 < g ≤ g₀`, `|E| ≤ 2 - κ₀`. -/
theorem cavRank_tail (κ₀ : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (q : ℕ) (hq : 7 ≤ q) (p e : ℝ)
    (hp : 0 < p) (hpq : p < 2 / ((q : ℝ) - 5)) (he : 0 < e) :
    ∃ g₀ δ₀ C : ℝ, 0 < g₀ ∧ 0 < δ₀ ∧ 0 < C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ g E t : ℝ, 0 < g → g ≤ g₀ → |E| ≤ 2 - κ₀ → 0 < t →
        μ W q {ω | 2 * t ^ (-p) * (W : ℝ) ^ (1 + e) <
            rankSurr t ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6))} ≤
          ENNReal.ofReal (C * ((W : ℝ) ^ (-δ₀) + Real.sqrt g)) := by
  have hq7 : (7 : ℝ) ≤ q := by exact_mod_cast hq
  have hq6 : ((q - 6 : ℕ) : ℝ) + 1 = (q : ℝ) - 5 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  obtain ⟨g₀, δ₀, C, hg₀, hδ₀, hC, W₀, h⟩ :=
    product_moment κ₀ hκ₀ hκ₀' (q - 6) (by omega) p e hp (by rw [hq6]; exact hpq) he
  refine ⟨g₀, δ₀, C, hg₀, hδ₀, hC, W₀, fun W hW g E t hg hgg hE ht => ?_⟩
  have hp2 : p ≤ 2 := by
    have h2 : (2 : ℝ) / ((q : ℝ) - 5) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  refine le_trans (measure_mono ?_) ((RetainedProb_preimage_le _).trans
    (h W hW g E 0 hg hgg hE (isRegularState_zero W hg.le)))
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hω ⊢
  have hb := (countIn_le_rankSurr (cavProd W g E q ω (q - 6)) ht hp hp2).2
  have hadj := (schattenPow_unitary_mul (cavProd W g E q ω (q - 6))
    (one_mem (Matrix.unitaryGroup (Fin W) ℂ)) (one_mem (Matrix.unitaryGroup (Fin W) ℂ)) p).2
  rw [← cavProd_eq_ricProd hq g E ω, hadj]
  have htp : 0 < 2 * t ^ (-p) := mul_pos two_pos (Real.rpow_pos_of_pos ht _)
  by_contra hcon
  have := mul_le_mul_of_nonneg_left (not_lt.mp hcon) htp.le
  linarith

/-- The singular values of `A` avoid `t > 0` almost surely (Section 9.4.4
[su:sec:cutoff-estimates]); hence for every `η > 0` some level `L` bounds
`‖(A* A - t²)⁻¹‖²_HS` except with probability `η`. -/
theorem exists_gap_level (W q : ℕ) (hq : 7 ≤ q) (g E t : ℝ) (ht : 0 < t) {η : ℝ} (hη : 0 < η) :
    ∃ L : ℝ, 0 < L ∧
      μ W q {ω | ¬ (IsUnit ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) -
          ((t ^ 2 : ℝ) : ℂ) • 1) ∧
        hsSq ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) -
          ((t ^ 2 : ℝ) : ℂ) • 1)⁻¹ ≤ L)} ≤ ENNReal.ofReal η := by
  set N : Ω W (q - 6) → Matrix (Fin W) (Fin W) ℂ := fun w =>
    ricProd W g E (q - 6) 0 w (q - 6) * (ricProd W g E (q - 6) 0 w (q - 6))ᴴ -
      ((t ^ 2 : ℝ) : ℂ) • 1 with hNdef
  set T : ℕ → Set (Ω W (q - 6)) := fun n => {w | ¬ (IsUnit (N w) ∧ hsSq (N w)⁻¹ ≤ n)} with hT
  have hpre : ∀ L : ℝ, {ω : Ω W q | ¬ (IsUnit ((cavProd W g E q ω (q - 6))ᴴ *
      cavProd W g E q ω (q - 6) - ((t ^ 2 : ℝ) : ℂ) • 1) ∧
      hsSq ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6) -
        ((t ^ 2 : ℝ) : ℂ) • 1)⁻¹ ≤ L)} =
      windowSample (cavWin q) ⁻¹' {w | ¬ (IsUnit (N w) ∧ hsSq (N w)⁻¹ ≤ L)} := by
    intro L
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hNdef]
    rw [← cavProd_eq_ricProd hq g E ω, Matrix.conjTranspose_conjTranspose]
  have hN : Measurable N :=
    (RetainedProb_measurable_mul (RetainedProb_measurable_prod W g E (q - 6) 0 (q - 6))
      (RetainedProb_measurable_conjTranspose
        (RetainedProb_measurable_prod W g E (q - 6) 0 (q - 6)))).sub measurable_const
  have hU : MeasurableSet {w | IsUnit (N w)} := by
    have : {w | IsUnit (N w)} = (fun w => (N w).det) ⁻¹' {0}ᶜ := by
      ext w
      simp [Matrix.isUnit_iff_isUnit_det]
    rw [this]
    exact (continuous_id.matrix_det.measurable.comp hN) (measurableSet_singleton 0).compl
  have hTm : ∀ n, MeasurableSet (T n) := by
    intro n
    have : T n = ({w | IsUnit (N w)} ∩ {w | hsSq (N w)⁻¹ ≤ n})ᶜ := by
      ext w
      simp [hT]
    rw [this]
    exact (hU.inter (measurableSet_le
      (RetainedProb_measurable_hsSq (RetainedProb_measurable_inv.comp hN))
      measurable_const)).compl
  have hanti : Antitone T := by
    intro n m hnm w hw hc
    exact hw ⟨hc.1, hc.2.trans (by exact_mod_cast hnm)⟩
  have hinter : (⋂ n, T n) ⊆ {w | ¬ IsUnit (N w)} := by
    intro w hw hu
    have hmem := Set.mem_iInter.mp hw ⌈hsSq (N w)⁻¹⌉₊
    exact hmem ⟨hu, Nat.le_ceil _⟩
  have hnull : μ W (q - 6) {w | ¬ IsUnit (N w)} = 0 :=
    RetainedProb_null W (q - 6) (by omega) g E t ht
  have hlim := tendsto_measure_iInter_atTop (μ := μ W (q - 6))
    (fun n => (hTm n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [measure_mono_null hinter hnull] at hlim
  have hη' : (0 : ℝ≥0∞) < ENNReal.ofReal η := ENNReal.ofReal_pos.mpr hη
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hη')).exists
  refine ⟨n + 1, by positivity, ?_⟩
  rw [hpre]
  refine (RetainedProb_preimage_le _).trans ((measure_mono ?_).trans hn.le)
  intro w hw hc
  exact hw ⟨hc.1, hc.2.trans (by linarith)⟩

/-- (9.56) [us:eq:Haar]: for a fixed orthogonal projection `Q₀` and `s ≥ 0`,
`‖Q₀ P_U‖ ≤ C √((Tr P_U + Tr Q₀ + s)/W)` except with probability `C e^{-c s}`, with `U` of
(9.56) [us:eq:Haar] at any threshold `t` and split level `s'`. -/
theorem cavU_overlap_le : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ W q : ℕ, 1 ≤ W → 7 ≤ q →
    ∀ (g E t s' : ℝ) (Q₀ : Matrix (Fin W) (Fin W) ℂ), Q₀.IsHermitian → Q₀ * Q₀ = Q₀ →
      ∀ s : ℝ, 0 ≤ s →
        μ W q {ω | C * Real.sqrt (((cavU W g E q t s' ω).trace.re + Q₀.trace.re + s) / W) <
            ‖Q₀ * cavU W g E q t s' ω‖} ≤ ENNReal.ofReal (C * Real.exp (-c * s)) := by
  obtain ⟨C, c, hC, hc, h⟩ := proj_overlap_le_of_equivariant
  refine ⟨C, c, hC, hc, fun W q hW hq g E t s' Q₀ hQH hQQ s hs => ?_⟩
  obtain ⟨hm, hproj, hequiv⟩ := cavUWin_spec W g E (q - 6) t s'
  have hset : {ω : Ω W q | C * Real.sqrt (((cavU W g E q t s' ω).trace.re + Q₀.trace.re + s) / W) <
      ‖Q₀ * cavU W g E q t s' ω‖} = windowSample (cavWin q) ⁻¹'
        {w | C * Real.sqrt (((Matrix.trace (cavUWin W g E (q - 6) t s' w)).re +
          (Matrix.trace Q₀).re + s) / W) < ‖Q₀ * cavUWin W g E (q - 6) t s' w‖} := by
    ext ω
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq, cavU_eq_cavUWin hq]
  rw [hset]
  exact (RetainedProb_preimage_le _).trans (h W (q - 6) hW _ hm hproj hequiv Q₀ hQH hQQ s hs)

end LSBA
