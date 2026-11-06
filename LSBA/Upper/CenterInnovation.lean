import LSBA.Upper.CenterUpdate
import LSBA.Gauss.PoincareMoment
import LSBA.Upper.LargeGradState

/-!
# Innovations of the corrected observables

The conditional innovation bounds (11.58) [lg:eq:innovations]
`‖M_k′ − P_g M_k‖_{2p} ≤ K g⁻¹W⁻¹`, `‖F_k′ − P_g F_k‖_{2p} ≤ K g⁻¹W^{−1/2}` for the corrected
observables of (11.50) [lg:eq:corrected-observables], from the gradient formula of (11.15)
[lg:eq:gradients] and the Gaussian `L^{2p}` Poincaré inequality (proof of Lemma 11.8
[lg:lem:dynamic]).
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Coordinate gradients -/

/-- The vector `(L e_i)_i` of coordinate partial derivatives of a real-linear form. -/
private def ciV {ι : Type} [Fintype ι] : ((ι → ℝ) →L[ℝ] ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun L := WithLp.toLp 2 (fun i => L (Pi.single i 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma ci_gradSq {ι : Type} [Fintype ι] (f : (ι → ℝ) → ℂ) (x : ι → ℝ) :
    gradSq f x = ‖ciV (fderiv ℝ f x)‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  rfl

private lemma ci_apply_eq {ι : Type} [Fintype ι] {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] (L : (ι → ℝ) →L[ℝ] F) (y : ι → ℝ) :
    L y = ∑ i, y i • L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_smul]
  congr 1
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- A real form bounded by `c` times the Euclidean norm has coordinate vector of norm at most
`c`; for a complex form, `√2 c`. -/
private lemma ci_norm_le {ι : Type} [Fintype ι] (L : (ι → ℝ) →L[ℝ] ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y, ‖L y‖ ≤ c * √(∑ i, y i ^ 2)) : ‖ciV L‖ ≤ √2 * c := by
  have key : ∀ ℓ : (ι → ℝ) →L[ℝ] ℝ, (∀ y, |ℓ y| ≤ c * √(∑ i, y i ^ 2)) →
      ∑ i, ℓ (Pi.single i 1) ^ 2 ≤ c ^ 2 := by
    intro ℓ hℓ
    set a : ι → ℝ := fun i => ℓ (Pi.single i 1) with ha
    have hla : ℓ a = ∑ i, a i ^ 2 := by
      rw [ci_apply_eq ℓ a]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, sq]
    set S := ∑ i, a i ^ 2 with hSdef
    have hS : 0 ≤ S := by positivity
    have h1 : S ≤ c * √S := by
      have := (le_abs_self (ℓ a)).trans (hℓ a)
      rwa [hla] at this
    have h2 : √S ≤ c := by
      rcases hS.eq_or_lt with h0 | hpos
      · rw [← h0, Real.sqrt_zero]; exact hc
      · have hs : 0 < √S := Real.sqrt_pos.2 hpos
        have := Real.sq_sqrt hS
        nlinarith
    calc S = √S ^ 2 := (Real.sq_sqrt hS).symm
      _ ≤ c ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  have hre := key (Complex.reCLM.comp L) fun y => (Complex.abs_re_le_norm _).trans (h y)
  have him := key (Complex.imCLM.comp L) fun y => (Complex.abs_im_le_norm _).trans (h y)
  have hsq : ‖ciV L‖ ^ 2 ≤ (√2 * c) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have e : ∀ i, ‖(ciV L).ofLp i‖ ^ 2 = (Complex.reCLM.comp L) (Pi.single i 1) ^ 2 +
        (Complex.imCLM.comp L) (Pi.single i 1) ^ 2 := by
      intro i
      change ‖L (Pi.single i 1)‖ ^ 2 = (L (Pi.single i 1)).re ^ 2 + (L (Pi.single i 1)).im ^ 2
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    simp only [e, Finset.sum_add_distrib]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

private lemma ci_opNorm_le {ι : Type} [Fintype ι] (L : (ι → ℝ) →L[ℝ] ℂ) :
    ‖L‖ ≤ Fintype.card ι * ‖ciV L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  rw [ci_apply_eq L y]
  calc ‖∑ i, y i • L (Pi.single i 1)‖ ≤ ∑ i, ‖y i • L (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖y‖ * ‖ciV L‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul]
        exact mul_le_mul (norm_le_pi_norm y i) (PiLp.norm_apply_le (ciV L) i) (norm_nonneg _)
          (norm_nonneg _)
    _ = Fintype.card ι * ‖ciV L‖ * ‖y‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Products of factors bounded by `1`: the coordinate gradients add up. -/
private lemma ci_prod {ι : Type} [Fintype ι] {α : Type*} (s : Finset α) (u : α → (ι → ℝ) → ℂ)
    (x : ι → ℝ) (b : α → ℝ) (hd : ∀ a ∈ s, ∃ L, HasFDerivAt (u a) L x ∧ ‖ciV L‖ ≤ b a)
    (h1 : ∀ a ∈ s, ‖u a x‖ ≤ 1) :
    ∃ L, HasFDerivAt (fun y => ∏ a ∈ s, u a y) L x ∧ ‖ciV L‖ ≤ ∑ a ∈ s, b a := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using hasFDerivAt_const (1 : ℂ) x, by simp⟩
  | insert a s ha ih =>
    obtain ⟨L₁, hL₁, hb₁⟩ := hd a (Finset.mem_insert_self a s)
    obtain ⟨L₂, hL₂, hb₂⟩ := ih (fun a' h => hd a' (Finset.mem_insert_of_mem h))
      (fun a' h => h1 a' (Finset.mem_insert_of_mem h))
    have hp : ‖∏ a' ∈ s, u a' x‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        fun a' h => h1 a' (Finset.mem_insert_of_mem h)
    have hu := h1 a (Finset.mem_insert_self a s)
    refine ⟨u a x • L₂ + (∏ a' ∈ s, u a' x) • L₁, ?_, ?_⟩
    · have := hL₁.mul hL₂
      simp only [Finset.prod_insert ha]
      exact this
    · rw [map_add, map_smul, map_smul, Finset.sum_insert ha]
      calc ‖u a x • ciV L₂ + (∏ a' ∈ s, u a' x) • ciV L₁‖ ≤
            ‖u a x‖ * ‖ciV L₂‖ + ‖∏ a' ∈ s, u a' x‖ * ‖ciV L₁‖ := by
            rw [← norm_smul, ← norm_smul]; exact norm_add_le _ _
        _ ≤ 1 * ‖ciV L₂‖ + 1 * ‖ciV L₁‖ := by gcongr
        _ ≤ b a + ∑ a' ∈ s, b a' := by linarith

/-- Polynomials in factors bounded by `1`: the coordinate gradient is bounded by the
coefficients times the degrees times the gradients of the factors. -/
private lemma ci_aeval {ι : Type} [Fintype ι] (ψ : ObsVar → (ι → ℝ) → ℂ) (x : ι → ℝ)
    (G : ObsVar → ℝ) (hd : ∀ v, ∃ L, HasFDerivAt (ψ v) L x ∧ ‖ciV L‖ ≤ G v)
    (h1 : ∀ v, ‖ψ v x‖ ≤ 1) (P : ObsPoly) :
    ∃ L, HasFDerivAt (fun y => aeval (fun v => ψ v y) P) L x ∧
      ‖ciV L‖ ≤ ∑ d ∈ P.support, ‖P.coeff d‖ * ∑ v ∈ d.support, (d v : ℝ) * G v := by
  have hf : (fun y => aeval (fun v => ψ v y) P) = fun y => ∑ d ∈ P.support,
      P.coeff d * ∏ v ∈ d.support, ∏ _i ∈ Finset.range (d v), ψ v y := by
    funext y
    rw [aeval_def, eval₂_eq]
    simp [Finset.prod_const]
  have hmono : ∀ d ∈ P.support, ∃ L, HasFDerivAt
      (fun y => ∏ v ∈ d.support, ∏ _i ∈ Finset.range (d v), ψ v y) L x ∧
        ‖ciV L‖ ≤ ∑ v ∈ d.support, (d v : ℝ) * G v := by
    intro d _
    refine ci_prod d.support _ x _ (fun v _ => ?_) (fun v _ => ?_)
    · obtain ⟨L, hL, hb⟩ := ci_prod (Finset.range (d v)) (fun _ => ψ v) x (fun _ => G v)
        (fun _ _ => hd v) (fun _ _ => h1 v)
      exact ⟨L, hL, hb.trans (by simp)⟩
    · rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => h1 v
  choose! L hL hb using hmono
  rw [hf]
  refine ⟨∑ d ∈ P.support, P.coeff d • L d, ?_, ?_⟩
  · exact HasFDerivAt.fun_sum fun d hd => (hL d hd).const_mul _
  · rw [map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hb d hd) (norm_nonneg _)

private lemma ci_contDiff_aeval {ι : Type} [Fintype ι] (ψ : ObsVar → (ι → ℝ) → ℂ)
    (hψ : ∀ v, ContDiff ℝ 1 (ψ v)) (P : ObsPoly) :
    ContDiff ℝ 1 (fun y => aeval (fun v => ψ v y) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (hψ v)

/-- The directional derivatives along every line give the coordinate gradient. -/
private lemma ci_of_line {ι : Type} [Fintype ι] {φ : (ι → ℝ) → ℂ} {x : ι → ℝ}
    {L : (ι → ℝ) →L[ℝ] ℂ} (hL : HasFDerivAt φ L x) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y, ∃ D, HasDerivAt (fun s : ℝ => φ (x + s • y)) D 0 ∧
      ‖D‖ ≤ c * √(∑ i, y i ^ 2)) : ‖ciV L‖ ≤ √2 * c := by
  refine ci_norm_le L hc fun y => ?_
  obtain ⟨D, hD, hb⟩ := h y
  have hline : HasDerivAt (fun s : ℝ => x + s • y) y 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const y).const_add x
  have hL' : HasFDerivAt φ L (x + (0 : ℝ) • y) := by simpa using hL
  have := hL'.comp_hasDerivAt (0 : ℝ) hline
  rw [this.unique hD]
  exact hb

/-! ### Hilbert–Schmidt bounds -/

/-- The squared Hilbert–Schmidt norm `Σ_{αβ} |A_{αβ}|²`. -/
private def ciHS {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) : ℝ := ∑ α, ∑ β, ‖A α β‖ ^ 2

private lemma ci_col_le {W : ℕ} (B : Matrix (Fin W) (Fin W) ℂ) (α : Fin W) :
    ∑ β, ‖B β α‖ ^ 2 ≤ ‖B‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec B (EuclideanSpace.single α 1)
  have hn : ‖EuclideanSpace.single α (1 : ℂ)‖ = 1 := by simp
  rw [hn, mul_one] at h
  have e : (EuclideanSpace.single α (1 : ℂ)).ofLp = Pi.single α 1 := by
    ext β
    simp [Pi.single_apply]
  rw [e, Matrix.mulVec_single_one, EuclideanSpace.norm_eq] at h
  have h' := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt (by positivity)] at h'
  simpa [Matrix.col] using h'

private lemma ci_HS_le {W : ℕ} (B : Matrix (Fin W) (Fin W) ℂ) : ciHS B ≤ W * ‖B‖ ^ 2 := by
  unfold ciHS
  rw [Finset.sum_comm]
  calc ∑ β, ∑ α, ‖B α β‖ ^ 2 ≤ ∑ _β : Fin W, ‖B‖ ^ 2 :=
        Finset.sum_le_sum fun β _ => ci_col_le B β
    _ = W * ‖B‖ ^ 2 := by simp

/-- `|tr(X H Y)| ≤ √W ‖X‖ ‖Y‖ ‖H‖_HS`. -/
private lemma ci_trace_le {W : ℕ} (X H Y : Matrix (Fin W) (Fin W) ℂ) :
    ‖(X * H * Y).trace‖ ≤ √W * ‖X‖ * ‖Y‖ * √(ciHS H) := by
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm (Y * X)]
  set B := Y * X with hB
  have h1 : ‖(H * B).trace‖ ≤ ∑ α, ∑ β, ‖H α β‖ * ‖B β α‖ := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ =>
      (norm_sum_le _ _).trans (le_of_eq ?_))
    simp
  have h2 : ∑ α, ∑ β, ‖H α β‖ * ‖B β α‖ ≤ √(ciHS H) * √(ciHS B) := by
    rw [← Fintype.sum_prod_type' (f := fun α β => ‖H α β‖ * ‖B β α‖)]
    refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans (le_of_eq ?_)
    unfold ciHS
    rw [Fintype.sum_prod_type' (f := fun α β => ‖H α β‖ ^ 2),
      Fintype.sum_prod_type' (f := fun α β => ‖B β α‖ ^ 2)]
    congr 1
    rw [Finset.sum_comm]
  have h3 : √(ciHS B) ≤ √W * (‖Y‖ * ‖X‖) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ ‖Y‖ * ‖X‖), ← Real.sqrt_mul (Nat.cast_nonneg _)]
    refine Real.sqrt_le_sqrt ((ci_HS_le B).trans ?_)
    gcongr
    exact norm_mul_le _ _
  calc ‖(H * B).trace‖ ≤ √(ciHS H) * √(ciHS B) := h1.trans h2
    _ ≤ √(ciHS H) * (√W * (‖Y‖ * ‖X‖)) := by gcongr
    _ = √W * ‖X‖ * ‖Y‖ * √(ciHS H) := by ring

/-- `‖H‖ ≤ ‖H‖_HS`. -/
private lemma ci_opNorm_le_HS {W : ℕ} (H : Matrix (Fin W) (Fin W) ℂ) : ‖H‖ ≤ √(ciHS H) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  simp only [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap']
  rw [Matrix.toLpLin_apply, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (by unfold ciHS; positivity)]
  refine Real.sqrt_le_sqrt ?_
  unfold ciHS
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun α _ => ?_
  simp only [Matrix.mulVec, dotProduct]
  calc ‖∑ β, H α β * x.ofLp β‖ ^ 2 ≤ (∑ β, ‖H α β‖ * ‖x.ofLp β‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (by simp)) 2
    _ ≤ (∑ β, ‖H α β‖ ^ 2) * ∑ β, ‖x.ofLp β‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

private lemma ci_gueBlock_entry {W : ℕ} (y : Ω W 1) (α β : Fin W) :
    ‖gueBlock W 1 y 0 α β‖ ^ 2 = (y (0, α, β) ^ 2 + y (0, β, α) ^ 2) / (2 * W) := by
  have hW : (0 : ℝ) < W := by exact_mod_cast Fin.pos α
  have hs1 : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW.le
  have hs2 : Real.sqrt (2 * W) ^ 2 = 2 * W := Real.sq_sqrt (by positivity)
  have hs1' : Real.sqrt W ≠ 0 := (Real.sqrt_pos.2 hW).ne'
  have hs2' : Real.sqrt (2 * W) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  simp only [gueBlock, Matrix.of_apply]
  rcases lt_trichotomy α β with h | rfl | h
  · simp only [h.ne, h, ↓reduceIte]
    rw [Complex.sq_norm, Complex.normSq_div, Complex.normSq_ofReal,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    field_simp
    rw [hs2]
    ring
  · simp only [↓reduceIte]
    rw [Complex.sq_norm, Complex.normSq_div, Complex.normSq_ofReal,
      Complex.normSq_ofReal]
    field_simp
    rw [hs1]
    ring
  · simp only [h.ne', not_lt.2 h.le, ↓reduceIte]
    rw [Complex.sq_norm, Complex.normSq_div,
      Complex.normSq_ofReal, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    field_simp
    rw [hs2]
    ring

/-- `‖V‖²_HS = W⁻¹ Σ_i ω_i²` for one GUE block in the coordinates of (1.2) [eq:covariance]. -/
private lemma ci_HS_gueBlock {W : ℕ} (y : Ω W 1) :
    ciHS (gueBlock W 1 y 0) = (W : ℝ)⁻¹ * ∑ i, y i ^ 2 := by
  have hR : ∑ i, y i ^ 2 = ∑ α, ∑ β, y (0, α, β) ^ 2 := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_one, Fintype.sum_prod_type]
  rw [hR]
  unfold ciHS
  simp_rw [ci_gueBlock_entry, add_div, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun α β => y (0, β, α) ^ 2 / (2 * W)), ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

private lemma ci_gueBlock_line {W : ℕ} (x y : Ω W 1) (s : ℝ) :
    gueBlock W 1 (x + s • y) 0 = gueBlock W 1 x 0 + (s : ℂ) • gueBlock W 1 y 0 := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

/-! ### Scalars of the update -/

private lemma ci_herm_line {W : ℕ} {V H : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian)
    (hH : H.IsHermitian) (s : ℝ) : (V + (s : ℂ) • H).IsHermitian := by
  refine hV.add ?_
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hH.eq, Complex.star_def, Complex.conj_ofReal]

private lemma ci_norm_unitary_le {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ) : ‖U‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial (Matrix (Fin W) (Fin W) ℂ) with hs | hs
  · rw [Subsingleton.elim U 0, norm_zero]
    exact zero_le_one
  · exact (CStarRing.norm_of_mem_unitary hU).le

private lemma ci_norm_normalPhase (E : ℝ) : ‖normalPhase E‖ = 1 := by
  rw [normalPhase, norm_neg, show (2 : ℂ) * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma ci_norm_stepPhase (E : ℝ) : ‖stepPhase E‖ = 1 := by
  rw [stepPhase, show -((freeAngle E : ℂ) * Complex.I) =
    ((-freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma ci_normalH_nonneg (E : ℝ) : 0 ≤ normalH E := by
  unfold normalH
  rw [freeAngle, Real.sin_arccos]
  positivity

/-- `h_θ ≤ 1` for `|E| ≤ 1`. -/
private lemma ci_normalH_le {E : ℝ} (hE : |E| ≤ 1) : normalH E ≤ 1 := by
  unfold normalH
  rw [freeAngle, Real.sin_arccos]
  have h1 : (E / 2) ^ 2 ≤ 1 / 4 := by
    rw [div_pow]
    nlinarith [sq_abs E, abs_nonneg E]
  have h2 : 1 / 2 ≤ √(1 - (E / 2) ^ 2) := by
    rw [show (1 : ℝ) / 2 = √((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [inv_le_one₀ (by linarith)]
  linarith

private lemma ci_norm_tau (g E : ℝ) (hg : 0 < g) :
    ‖Complex.I * ((normalH E / g : ℝ) : ℂ)‖ = normalH E / g := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg (ci_normalH_nonneg E) hg.le)]

/-! ### Derivatives along a line of blocks -/

private lemma ci_hasDerivAt_lin {W : ℕ} (ℓ : Matrix (Fin W) (Fin W) ℂ →ₗ[ℂ] ℂ)
    {f : ℝ → Matrix (Fin W) (Fin W) ℂ} {f' : Matrix (Fin W) (Fin W) ℂ} (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun s => ℓ (f s)) (ℓ f') 0 :=
  ((LinearMap.toContinuousLinearMap ℓ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hf

/-- `d(F⁻¹) = F⁻¹ (i h_θ g⁻¹ dV (I + C)) F⁻¹`. -/
private lemma ci_hasDerivAt_inv (g E : ℝ) {W : ℕ} {C V H : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) :
    HasDerivAt (fun s : ℝ => (stepF g E C (V + (s : ℂ) • H))⁻¹)
      ((stepF g E C V)⁻¹ * ((Complex.I * ((normalH E / g : ℝ) : ℂ)) • (H * (1 + C))) *
        (stepF g E C V)⁻¹) 0 := by
  set t : ℂ := Complex.I * ((normalH E / g : ℝ) : ℂ)
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 0 :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_id (0 : ℝ))
  have hG : HasDerivAt (fun s : ℝ => V + (s : ℂ) • H) H 0 := by
    simpa using (h1.smul_const H).const_add V
  have hF : HasDerivAt (fun s : ℝ => stepF g E C (V + (s : ℂ) • H))
      (-(t • (H * (1 + C)))) 0 :=
    ((hG.mul_const (1 + C)).const_smul t).const_sub (1 : Matrix (Fin W) (Fin W) ℂ)
  obtain ⟨u, hu⟩ := isUnit_stepF g E hC hV
  have hui : ((u⁻¹ : (Matrix (Fin W) (Fin W) ℂ)ˣ) : Matrix (Fin W) (Fin W) ℂ) =
      (stepF g E C V)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  have hl : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℂ (Matrix (Fin W) (Fin W) ℂ) ↑u⁻¹ ↑u⁻¹)
      (stepF g E C (V + ((0 : ℝ) : ℂ) • H)) := by
    have h0 : stepF g E C (V + ((0 : ℝ) : ℂ) • H) = ↑u := by simp [hu]
    rw [h0]
    exact hasFDerivAt_ringInverse (𝕜 := ℂ) u
  have hd := (hl.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hF
  have hfun : (fun s : ℝ => (stepF g E C (V + (s : ℂ) • H))⁻¹) =
      Ring.inverse ∘ fun s : ℝ => stepF g E C (V + (s : ℂ) • H) := by
    funext s
    exact Matrix.nonsing_inv_eq_ringInverse _
  rw [hfun]
  exact hd.congr_deriv (by simp [hui])

/-- The derivative `Σ_{a<j} A^a D A^{j−1−a}` of the `j`-th power. -/
private def ciDP {W : ℕ} (D A : Matrix (Fin W) (Fin W) ℂ) : ℕ → Matrix (Fin W) (Fin W) ℂ
  | 0 => 0
  | j + 1 => D * A ^ j + A * ciDP D A j

private lemma ci_hasDerivAt_pow {W : ℕ} {f : ℝ → Matrix (Fin W) (Fin W) ℂ}
    {D : Matrix (Fin W) (Fin W) ℂ} (hf : HasDerivAt f D 0) (j : ℕ) :
    HasDerivAt (fun s => f s ^ j) (ciDP D (f 0) j) 0 := by
  induction j with
  | zero => simpa [ciDP] using hasDerivAt_const (0 : ℝ) (1 : Matrix (Fin W) (Fin W) ℂ)
  | succ j ih =>
    have := hf.mul ih
    simp only [pow_succ']
    exact this

private lemma ci_norm_DP_le {W : ℕ} (D : Matrix (Fin W) (Fin W) ℂ)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin W) ℂ) (j : ℕ) :
    ‖ciDP D A j‖ ≤ j * ‖D‖ := by
  induction j with
  | zero => simp [ciDP]
  | succ j ih =>
    have h1 : ‖A ^ j‖ ≤ 1 := ci_norm_unitary_le (pow_mem hA j)
    have h2 : ‖A‖ ≤ 1 := ci_norm_unitary_le hA
    calc ‖ciDP D A (j + 1)‖ ≤ ‖D‖ * ‖A ^ j‖ + ‖A‖ * ‖ciDP D A j‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ‖D‖ * 1 + 1 * (j * ‖D‖) := by gcongr
      _ = ((j + 1 : ℕ) : ℝ) * ‖D‖ := by push_cast; ring

private lemma ci_trace_DP_le {W : ℕ} (D : Matrix (Fin W) (Fin W) ℂ)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin W) ℂ) {c : ℝ}
    (hc : 0 ≤ c) (hD : ∀ X Z : Matrix (Fin W) (Fin W) ℂ, ‖(X * D * Z).trace‖ ≤ c * ‖X‖ * ‖Z‖)
    (j : ℕ) : ∀ X Z : Matrix (Fin W) (Fin W) ℂ,
      ‖(X * ciDP D A j * Z).trace‖ ≤ j * c * ‖X‖ * ‖Z‖ := by
  induction j with
  | zero => intro X Z; simp [ciDP]
  | succ j ih =>
    intro X Z
    have h1 : ‖A ^ j‖ ≤ 1 := ci_norm_unitary_le (pow_mem hA j)
    have h2 : ‖A‖ ≤ 1 := ci_norm_unitary_le hA
    have e : X * ciDP D A (j + 1) * Z = X * D * (A ^ j * Z) + X * A * ciDP D A j * Z := by
      simp only [ciDP, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    have hAZ : ‖A ^ j * Z‖ ≤ ‖Z‖ :=
      (norm_mul_le _ _).trans (by nlinarith [norm_nonneg Z, norm_nonneg (A ^ j)])
    have hXA : ‖X * A‖ ≤ ‖X‖ :=
      (norm_mul_le _ _).trans (by nlinarith [norm_nonneg X, norm_nonneg A])
    rw [e, Matrix.trace_add]
    calc _ ≤ ‖(X * D * (A ^ j * Z)).trace‖ + ‖(X * A * ciDP D A j * Z).trace‖ := norm_add_le _ _
      _ ≤ c * ‖X‖ * ‖A ^ j * Z‖ + j * c * ‖X * A‖ * ‖Z‖ := add_le_add (hD _ _) (ih _ _)
      _ ≤ c * ‖X‖ * ‖Z‖ + j * c * ‖X‖ * ‖Z‖ := by gcongr
      _ = ((j + 1 : ℕ) : ℝ) * c * ‖X‖ * ‖Z‖ := by push_cast; ring

/-- Bounds for the derivative `dC′ = i h_θ g⁻¹ (C′ − e^{−2iθ}) dV (I + C) F⁻¹` of (11.15)
[lg:eq:gradients]. -/
private lemma ci_stepC_deriv_le {g : ℝ} (hg : 0 < g) (E : ℝ) {W : ℕ}
    {C V H : Matrix (Fin W) (Fin W) ℂ} (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ)
    (hV : V.IsHermitian) :
    ‖(Complex.I * ((normalH E / g : ℝ) : ℂ)) • ((stepC g E C V - normalPhase E •
        (1 : Matrix (Fin W) (Fin W) ℂ)) * H * (1 + C) * (stepF g E C V)⁻¹)‖ ≤
      normalH E / g * (4 * (1 + 2 * normalH E * ‖V‖ / g)) * ‖H‖ ∧
    ∀ X Z : Matrix (Fin W) (Fin W) ℂ, ‖(X * ((Complex.I * ((normalH E / g : ℝ) : ℂ)) •
        ((stepC g E C V - normalPhase E • (1 : Matrix (Fin W) (Fin W) ℂ)) * H * (1 + C) *
          (stepF g E C V)⁻¹)) * Z).trace‖ ≤
      normalH E / g * (4 * (1 + 2 * normalH E * ‖V‖ / g)) * √W * √(ciHS H) * ‖X‖ * ‖Z‖ := by
  set n := 1 + 2 * normalH E * ‖V‖ / g with hn
  have hone : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := ci_norm_unitary_le (one_mem _)
  have hCn : ‖C‖ ≤ 1 := ci_norm_unitary_le hC
  have hC'n : ‖stepC g E C V‖ ≤ 1 := ci_norm_unitary_le (stepC_mem_unitaryGroup g E hC hV)
  have hA : ‖stepC g E C V - normalPhase E • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, ci_norm_normalPhase, one_mul]
    linarith
  have hB : ‖(1 : Matrix (Fin W) (Fin W) ℂ) + C‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
  have hN : ‖(stepF g E C V)⁻¹‖ ≤ n := (norm_stepF_le hg E hC hV).2
  have hn0 : 0 ≤ n := by
    have := ci_normalH_nonneg E
    rw [hn]; positivity
  have ht := ci_norm_tau g E hg
  have ht0 : 0 ≤ normalH E / g := div_nonneg (ci_normalH_nonneg E) hg.le
  have hBN : ‖(1 + C) * (stepF g E C V)⁻¹‖ ≤ 2 * n :=
    (norm_mul_le _ _).trans (mul_le_mul hB hN (norm_nonneg _) (by norm_num))
  constructor
  · rw [norm_smul, ht, show normalH E / g * (4 * n) * ‖H‖ = normalH E / g * (4 * n * ‖H‖) by
      ring]
    refine mul_le_mul_of_nonneg_left ?_ ht0
    calc ‖(stepC g E C V - normalPhase E • 1) * H * (1 + C) * (stepF g E C V)⁻¹‖ ≤
          ‖stepC g E C V - normalPhase E • 1‖ * ‖H‖ * ‖1 + C‖ * ‖(stepF g E C V)⁻¹‖ := by
          refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ 2 * ‖H‖ * 2 * n := by gcongr
      _ = 4 * n * ‖H‖ := by ring
  · intro X Z
    have e : X * ((Complex.I * ((normalH E / g : ℝ) : ℂ)) •
        ((stepC g E C V - normalPhase E • (1 : Matrix (Fin W) (Fin W) ℂ)) * H * (1 + C) *
          (stepF g E C V)⁻¹)) * Z = (Complex.I * ((normalH E / g : ℝ) : ℂ)) •
        ((X * (stepC g E C V - normalPhase E • 1)) * H * ((1 + C) * (stepF g E C V)⁻¹ * Z)) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [e, Matrix.trace_smul, norm_smul, ht]
    have h1 := ci_trace_le (X * (stepC g E C V - normalPhase E • 1)) H
      ((1 + C) * (stepF g E C V)⁻¹ * Z)
    have hXA : ‖X * (stepC g E C V - normalPhase E • 1)‖ ≤ 2 * ‖X‖ :=
      (norm_mul_le _ _).trans (by nlinarith [norm_nonneg X])
    have hBZ : ‖(1 + C) * (stepF g E C V)⁻¹ * Z‖ ≤ 2 * n * ‖Z‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hBN (norm_nonneg _))
    calc normalH E / g * ‖(X * (stepC g E C V - normalPhase E • 1) * H *
          ((1 + C) * (stepF g E C V)⁻¹ * Z)).trace‖ ≤
        normalH E / g * (√W * (2 * ‖X‖) * (2 * n * ‖Z‖) * √(ciHS H)) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) ht0
          gcongr
      _ = normalH E / g * (4 * n) * √W * √(ciHS H) * ‖X‖ * ‖Z‖ := by ring

/-- The quadratic form `M ↦ v* M v`. -/
private def ciQ {W : ℕ} (v : EuclideanSpace ℂ (Fin W)) : Matrix (Fin W) (Fin W) ℂ →ₗ[ℂ] ℂ where
  toFun M := vecForm M v
  map_add' M N := by simp [vecForm, map_add]
  map_smul' a M := by simp [vecForm]

private lemma ci_norm_Q_le {W : ℕ} {v : EuclideanSpace ℂ (Fin W)} (hv : ‖v‖ = 1)
    (M : Matrix (Fin W) (Fin W) ℂ) : ‖ciQ v M‖ ≤ ‖M‖ := by
  change ‖inner ℂ v (Matrix.toEuclideanLin M v)‖ ≤ ‖M‖
  calc ‖inner ℂ v (Matrix.toEuclideanLin M v)‖ ≤ ‖v‖ * ‖Matrix.toEuclideanLin M v‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖M‖ * ‖v‖) := mul_le_mul_of_nonneg_left
        ((Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) M).le_opNorm v) (norm_nonneg _)
    _ = ‖M‖ := by rw [hv]; ring

private lemma ci_vecForm_conj {W : ℕ} (A M : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) :
    vecForm (A * M * Aᴴ) v = vecForm M (Matrix.toEuclideanLin Aᴴ v) := by
  unfold vecForm
  have e : Matrix.toEuclideanLin (A * M * Aᴴ) v = Matrix.toEuclideanLin A
      (Matrix.toEuclideanLin M (Matrix.toEuclideanLin Aᴴ v)) := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  rw [e, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]

private lemma ci_vecForm_smul {W : ℕ} (α : ℂ) (M : Matrix (Fin W) (Fin W) ℂ)
    (w : EuclideanSpace ℂ (Fin W)) : vecForm M (α • w) = star α * α * vecForm M w := by
  simp only [vecForm, map_smul, inner_smul_left, inner_smul_right, Complex.star_def]
  ring

/-- `f_j(C′, v′) = v* F⁻¹ C′^j F^{−*} v / v* F⁻¹ F^{−*} v` for the update (11.7) [lg:eq:update]. -/
private lemma ci_obsF_step (g E : ℝ) {W : ℕ} (X : State W) (V : Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) : obsF (j : ℤ) (stepState g E X V) =
      ciQ X.2 ((stepF g E X.1 V)⁻¹ * stepC g E X.1 V ^ j * star (stepF g E X.1 V)⁻¹) /
        ciQ X.2 ((stepF g E X.1 V)⁻¹ * star (stepF g E X.1 V)⁻¹) := by
  change _ = vecForm _ X.2 / vecForm _ X.2
  rw [Matrix.star_eq_conjTranspose]
  have e2 := ci_vecForm_conj (stepF g E X.1 V)⁻¹ 1 X.2
  rw [Matrix.mul_one] at e2
  rw [ci_vecForm_conj, e2]
  have hu : Matrix.toEuclideanLin ((stepF g E X.1 V)⁻¹)ᴴ X.2 = stepVec g E X V := rfl
  rw [hu]
  have h1 : vecForm 1 (stepVec g E X V) = ((‖stepVec g E X V‖ ^ 2 : ℝ) : ℂ) := by
    simp [vecForm, inner_self_eq_norm_sq_to_K]
  have hα : star (stepPhase E * ((‖stepVec g E X V‖⁻¹ : ℝ) : ℂ)) *
      (stepPhase E * ((‖stepVec g E X V‖⁻¹ : ℝ) : ℂ)) =
        (((‖stepVec g E X V‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul', norm_mul, ci_norm_stepPhase, one_mul,
      Complex.norm_real, norm_inv, norm_norm]
    push_cast
    ring
  change vecForm (stepC g E X.1 V ^ (j : ℤ)) ((stepPhase E * ((‖stepVec g E X V‖⁻¹ : ℝ) : ℂ)) •
    stepVec g E X V) = _
  rw [zpow_natCast, ci_vecForm_smul, hα, h1, div_eq_mul_inv]
  push_cast
  ring

/-- The `m_k` part of (11.15) [lg:eq:gradients]: along `V + sH`,
`|d m_k(C′)| ≤ |k| h_θ g⁻¹ 4 (1 + 2h_θ‖V‖/g) W^{−1/2} ‖H‖_HS`. -/
private lemma ci_line_obsM {g : ℝ} (hg : 0 < g) (E : ℝ) {W : ℕ} (hW : 1 ≤ W) {X : State W}
    (hX : IsState X) {V H : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) (hH : H.IsHermitian)
    (k : ℤ) : ∃ D : ℂ, HasDerivAt (fun s : ℝ => obsM k (stepState g E X (V + (s : ℂ) • H))) D 0 ∧
      ‖D‖ ≤ k.natAbs * (normalH E / g * (4 * (1 + 2 * normalH E * ‖V‖ / g))) * (√W)⁻¹ *
        √(ciHS H) := by
  set c := normalH E / g * (4 * (1 + 2 * normalH E * ‖V‖ / g)) with hc
  have hc0 : 0 ≤ c := by
    have := ci_normalH_nonneg E
    rw [hc]
    positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hpos : ∀ j : ℕ, ∃ D : ℂ, HasDerivAt
      (fun s : ℝ => obsM (j : ℤ) (stepState g E X (V + (s : ℂ) • H))) D 0 ∧
        ‖D‖ ≤ j * c * (√W)⁻¹ * √(ciHS H) := by
    intro j
    have hC := hasDerivAt_stepC g E hX.1 hV H
    have hP := ci_hasDerivAt_pow hC j
    have e0 : stepC g E X.1 (V + ((0 : ℝ) : ℂ) • H) = stepC g E X.1 V := by simp
    rw [e0] at hP
    have htr := (ci_hasDerivAt_lin (Matrix.traceLinearMap (Fin W) ℂ ℂ) hP).const_mul
      ((W : ℂ)⁻¹)
    have hfun : (fun s : ℝ => obsM (j : ℤ) (stepState g E X (V + (s : ℂ) • H))) =
        fun s : ℝ => (W : ℂ)⁻¹ * Matrix.traceLinearMap (Fin W) ℂ ℂ
          (stepC g E X.1 (V + (s : ℂ) • H) ^ j) := by
      funext s
      simp [obsM, stepState]
    rw [hfun]
    refine ⟨_, htr, ?_⟩
    have hb := (ci_stepC_deriv_le hg E (H := H) hX.1 hV).2
    have hD := ci_trace_DP_le _ (stepC_mem_unitaryGroup g E hX.1 hV)
      (by positivity) hb j 1 1
    have hone : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := ci_norm_unitary_le (one_mem _)
    rw [Matrix.one_mul, Matrix.mul_one] at hD
    rw [norm_mul, norm_inv, Complex.norm_natCast, Matrix.traceLinearMap_apply]
    have hsW : (W : ℝ)⁻¹ * √W = (√W)⁻¹ := by
      have hs : √(W : ℝ) ^ 2 = W := Real.sq_sqrt hW0.le
      have : (√(W : ℝ)) ≠ 0 := (Real.sqrt_pos.2 hW0).ne'
      calc (W : ℝ)⁻¹ * √W = (√W ^ 2)⁻¹ * √W := by rw [hs]
        _ = (√W)⁻¹ := by field_simp
    calc (W : ℝ)⁻¹ * ‖(ciDP _ (stepC g E X.1 V) j).trace‖ ≤
        (W : ℝ)⁻¹ * (j * (c * √W * √(ciHS H)) * 1 * 1) := by
          refine mul_le_mul_of_nonneg_left (hD.trans ?_) (by positivity)
          gcongr
      _ = j * c * ((W : ℝ)⁻¹ * √W) * √(ciHS H) := by ring
      _ = j * c * (√W)⁻¹ * √(ciHS H) := by rw [hsW]
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa using hpos j
  · obtain ⟨D, hD, hb⟩ := hpos j
    refine ⟨star D, ?_, by simpa using hb⟩
    have hfun : (fun s : ℝ => obsM (-(j : ℤ)) (stepState g E X (V + (s : ℂ) • H))) =
        fun s : ℝ => star (obsM (j : ℤ) (stepState g E X (V + (s : ℂ) • H))) := by
      funext s
      exact (obsM_zero_neg hW (isState_stepState g E hX (ci_herm_line hV hH s)) j).2
    rw [hfun]
    exact hD.star

/-- The `f_k` part of (11.15) [lg:eq:gradients]: along `V + sH`,
`|d f_k(C′, v′)| ≤ (8 + 4|k|) h_θ g⁻¹ (1 + 2h_θ‖V‖/g)⁹ ‖H‖`. -/
private lemma ci_line_obsF {g : ℝ} (hg : 0 < g) (E : ℝ) {W : ℕ} {X : State W}
    (hX : IsState X) {V H : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) (hH : H.IsHermitian)
    (k : ℤ) : ∃ D : ℂ, HasDerivAt (fun s : ℝ => obsF k (stepState g E X (V + (s : ℂ) • H))) D 0 ∧
      ‖D‖ ≤ (8 + 4 * k.natAbs) * (normalH E / g * ‖H‖) * (1 + 2 * normalH E * ‖V‖ / g) ^ 9 := by
  set t := normalH E / g with ht
  set n := 1 + 2 * normalH E * ‖V‖ / g with hn
  have ht0 : 0 ≤ t := div_nonneg (ci_normalH_nonneg E) hg.le
  have hn1 : 1 ≤ n := by
    have := ci_normalH_nonneg E
    have : 0 ≤ 2 * normalH E * ‖V‖ / g := by positivity
    rw [hn]
    linarith
  set a := t * ‖H‖ with ha
  have ha0 : 0 ≤ a := by positivity
  have hpos : ∀ j : ℕ, ∃ D : ℂ, HasDerivAt
      (fun s : ℝ => obsF (j : ℤ) (stepState g E X (V + (s : ℂ) • H))) D 0 ∧
        ‖D‖ ≤ (8 + 4 * j) * a * n ^ 9 := by
    intro j
    set τ : ℂ := Complex.I * ((normalH E / g : ℝ) : ℂ) with hτ
    set N0 := (stepF g E X.1 V)⁻¹ with hN0
    set C0 := stepC g E X.1 V with hC0
    set D := τ • ((C0 - normalPhase E • (1 : Matrix (Fin W) (Fin W) ℂ)) * H * (1 + X.1) * N0)
      with hD
    set N' := N0 * (τ • (H * (1 + X.1))) * N0 with hN'
    set Nf : ℝ → Matrix (Fin W) (Fin W) ℂ := fun s => (stepF g E X.1 (V + (s : ℂ) • H))⁻¹
      with hNf
    set Pf : ℝ → Matrix (Fin W) (Fin W) ℂ := fun s => stepC g E X.1 (V + (s : ℂ) • H) ^ j
      with hPf
    have hN : HasDerivAt Nf N' 0 := ci_hasDerivAt_inv g E hX.1 hV
    have hC := hasDerivAt_stepC g E hX.1 hV H
    have hP : HasDerivAt Pf (ciDP D C0 j) 0 := by
      have := ci_hasDerivAt_pow hC j
      have e0 : stepC g E X.1 (V + ((0 : ℝ) : ℂ) • H) = C0 := by simp [hC0]
      rw [e0] at this
      exact this
    have hNf0 : Nf 0 = N0 := by simp [hNf, hN0]
    have hPf0 : Pf 0 = C0 ^ j := by simp [hPf, hC0]
    have hnum : HasDerivAt (fun s => Nf s * Pf s * star (Nf s))
        ((N' * C0 ^ j + N0 * ciDP D C0 j) * star N0 + N0 * C0 ^ j * star N') 0 := by
      have := (hN.mul hP).mul hN.star
      convert this using 1
      simp only [Pi.mul_apply, hNf0, hPf0]
    have hden : HasDerivAt (fun s => Nf s * star (Nf s)) (N' * star N0 + N0 * star N') 0 := by
      have := hN.mul hN.star
      convert this using 1
      simp only [hNf0]
    set q := ciQ X.2 with hq
    have hnumq := ci_hasDerivAt_lin q hnum
    have hdenq := ci_hasDerivAt_lin q hden
    -- the value of the denominator
    set u := stepVec g E X V with hu
    have hden0 : q (N0 * star N0) = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [hq]
      change vecForm _ X.2 = _
      rw [Matrix.star_eq_conjTranspose]
      have e2 := ci_vecForm_conj N0 1 X.2
      rw [Matrix.mul_one] at e2
      rw [e2]
      simp [vecForm, inner_self_eq_norm_sq_to_K, hu, stepVec, hN0]
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_stepF g E hX.1 hV)
    have hadj : Matrix.toEuclideanLin (stepF g E X.1 V)ᴴ u = X.2 := by
      rw [hu, stepVec]
      simp only [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
      rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.conjTranspose_one,
        Matrix.one_mulVec]
    have hu1 : 1 ≤ n * ‖u‖ := by
      have h1 : ‖X.2‖ ≤ ‖(stepF g E X.1 V)ᴴ‖ * ‖u‖ := by
        rw [← hadj]
        exact (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) (stepF g E X.1 V)ᴴ).le_opNorm u
      rw [hX.2, Matrix.l2_opNorm_conjTranspose] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (norm_stepF_le hg E hX.1 hV).1 (norm_nonneg _))
    have hupos : 0 < ‖u‖ := by
      by_contra h
      have : ‖u‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
      rw [this, mul_zero] at hu1
      linarith
    have hd0 : q (N0 * star N0) ≠ 0 := by
      rw [hden0]
      exact_mod_cast (pow_pos hupos 2).ne'
    have hr : ‖q (N0 * star N0)‖⁻¹ ≤ n ^ 2 := by
      rw [hden0, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      nlinarith
    have hdiv := hnumq.div hdenq (by simpa [hNf0] using hd0)
    have hfun : (fun s : ℝ => obsF (j : ℤ) (stepState g E X (V + (s : ℂ) • H))) =
        (fun s => q (Nf s * Pf s * star (Nf s))) / fun s => q (Nf s * star (Nf s)) := by
      funext s
      rw [ci_obsF_step]
      rfl
    rw [hfun]
    refine ⟨_, hdiv, ?_⟩
    simp only [hNf0, hPf0]
    -- norm bounds
    have hqle : ∀ M, ‖q M‖ ≤ ‖M‖ := ci_norm_Q_le hX.2
    have hN0n : ‖N0‖ ≤ n := (norm_stepF_le hg E hX.1 hV).2
    have hN0s : ‖star N0‖ ≤ n := by
      rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose]
      exact hN0n
    have hB : ‖(1 : Matrix (Fin W) (Fin W) ℂ) + X.1‖ ≤ 2 :=
      (norm_add_le _ _).trans (by linarith [ci_norm_unitary_le (one_mem
        (Matrix.unitaryGroup (Fin W) ℂ)), ci_norm_unitary_le hX.1])
    have hN'n : ‖N'‖ ≤ 2 * a * n ^ 2 := by
      calc ‖N'‖ ≤ ‖N0‖ * (‖τ‖ * (‖H‖ * ‖1 + X.1‖)) * ‖N0‖ := by
            refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))) (norm_nonneg _))
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ n * (t * (‖H‖ * 2)) * n := by
            rw [hτ, ci_norm_tau g E hg]
            gcongr
        _ = 2 * a * n ^ 2 := by rw [ha]; ring
    have hN's : ‖star N'‖ ≤ 2 * a * n ^ 2 := by
      rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose]
      exact hN'n
    have hDn : ‖D‖ ≤ 4 * a * n := by
      have := (ci_stepC_deriv_le hg E (H := H) hX.1 hV).1
      rw [hD]
      refine this.trans (le_of_eq ?_)
      rw [ha]
      ring
    have hP0 : ‖C0 ^ j‖ ≤ 1 := ci_norm_unitary_le (pow_mem (stepC_mem_unitaryGroup g E hX.1 hV) j)
    have hP' : ‖ciDP D C0 j‖ ≤ j * (4 * a * n) :=
      (ci_norm_DP_le D (stepC_mem_unitaryGroup g E hX.1 hV) j).trans (by gcongr)
    have hnum' : ‖q ((N' * C0 ^ j + N0 * ciDP D C0 j) * star N0 + N0 * C0 ^ j * star N')‖ ≤
        (4 + 4 * j) * a * n ^ 3 := by
      refine (hqle _).trans ?_
      calc ‖(N' * C0 ^ j + N0 * ciDP D C0 j) * star N0 + N0 * C0 ^ j * star N'‖ ≤
          (‖N'‖ * ‖C0 ^ j‖ + ‖N0‖ * ‖ciDP D C0 j‖) * ‖star N0‖ +
            ‖N0‖ * ‖C0 ^ j‖ * ‖star N'‖ := by
            refine (norm_add_le _ _).trans (add_le_add ((norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans
                (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))) (norm_nonneg _)))
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
                (norm_nonneg _))))
        _ ≤ (2 * a * n ^ 2 * 1 + n * (j * (4 * a * n))) * n + n * 1 * (2 * a * n ^ 2) := by
            gcongr
        _ = (4 + 4 * j) * a * n ^ 3 := by ring
    have hden' : ‖q (N' * star N0 + N0 * star N')‖ ≤ 4 * a * n ^ 3 := by
      refine (hqle _).trans ?_
      calc ‖N' * star N0 + N0 * star N'‖ ≤ ‖N'‖ * ‖star N0‖ + ‖N0‖ * ‖star N'‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ 2 * a * n ^ 2 * n + n * (2 * a * n ^ 2) := by gcongr
        _ = 4 * a * n ^ 3 := by ring
    have hnum0 : ‖q (N0 * C0 ^ j * star N0)‖ ≤ n ^ 2 := by
      refine (hqle _).trans ?_
      calc ‖N0 * C0 ^ j * star N0‖ ≤ ‖N0‖ * ‖C0 ^ j‖ * ‖star N0‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ n * 1 * n := by gcongr
        _ = n ^ 2 := by ring
    set A := q ((N' * C0 ^ j + N0 * ciDP D C0 j) * star N0 + N0 * C0 ^ j * star N')
    set B := q (N0 * C0 ^ j * star N0)
    set d := q (N0 * star N0)
    set d' := q (N' * star N0 + N0 * star N')
    have e : (A * d - B * d') / d ^ 2 = A * d⁻¹ - B * d' * d⁻¹ ^ 2 := by
      field_simp
    rw [e]
    have hn5 : n ^ 5 ≤ n ^ 9 := pow_le_pow_right₀ hn1 (by norm_num)
    have hr0 : 0 ≤ ‖d‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
    calc ‖A * d⁻¹ - B * d' * d⁻¹ ^ 2‖ ≤ ‖A‖ * ‖d‖⁻¹ + ‖B‖ * ‖d'‖ * ‖d‖⁻¹ ^ 2 := by
          refine (norm_sub_le _ _).trans (le_of_eq ?_)
          rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_inv]
      _ ≤ (4 + 4 * j) * a * n ^ 3 * n ^ 2 + n ^ 2 * (4 * a * n ^ 3) * (n ^ 2) ^ 2 := by
          gcongr
      _ = (4 + 4 * j) * a * n ^ 5 + 4 * a * n ^ 9 := by ring
      _ ≤ (4 + 4 * j) * a * n ^ 9 + 4 * a * n ^ 9 := by
          gcongr
      _ = (8 + 4 * j) * a * n ^ 9 := by ring
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa using hpos j
  · obtain ⟨D, hD, hb⟩ := hpos j
    refine ⟨star D, ?_, by simpa using hb⟩
    have hfun : (fun s : ℝ => obsF (-(j : ℤ)) (stepState g E X (V + (s : ℂ) • H))) =
        fun s : ℝ => star (obsF (j : ℤ) (stepState g E X (V + (s : ℂ) • H))) := by
      funext s
      exact (obsF_zero_neg (isState_stepState g E hX (ci_herm_line hV hH s)) j).2
    rw [hfun]
    exact hD.star

/-! ### Gradients of the observables in the block coordinates -/

/-- The gradient weights of the variables: `√2·4|k|/W` for `m_k`, `√2(8 + 4|k|)/√W` for `f_k`,
`0` for the constants `w`, `γ`. -/
private def ciG (W : ℕ) : ObsVar → ℝ
  | .m k => √2 * (4 * k.1.natAbs) * (W : ℝ)⁻¹
  | .f k => √2 * (8 + 4 * k.1.natAbs) * (√W)⁻¹
  | .w => 0
  | .γ => 0

/-- The index-dependent part of the weights. -/
private def ciC (v : ObsVar) : ℝ := √2 * (8 + 4 * v.idx.natAbs)

private lemma ci_sqrt_HS_gueBlock {W : ℕ} (y : Ω W 1) :
    √(ciHS (gueBlock W 1 y 0)) = (√W)⁻¹ * √(∑ i, y i ^ 2) := by
  rw [ci_HS_gueBlock, Real.sqrt_mul (inv_nonneg.2 (Nat.cast_nonneg _)), Real.sqrt_inv]

private lemma ci_var {W : ℕ} (hW : 1 ≤ W) {g : ℝ} (hg : 1 ≤ g) (E : ℝ) {X : State W}
    (hX : IsState X) (x : Ω W 1) (v : ObsVar) :
    (∃ L, HasFDerivAt (fun y : Ω W 1 => obsEval g (stepState g E X (gueBlock W 1 y 0))
        (MvPolynomial.X v)) L x ∧
      ‖ciV L‖ ≤ ciG W v * (normalH E / g * (1 + 2 * normalH E * ‖gueBlock W 1 x 0‖ / g) ^ 9)) ∧
    ‖obsEval g (stepState g E X (gueBlock W 1 x 0)) (MvPolynomial.X v)‖ ≤ 1 ∧
    ContDiff ℝ 1 (fun y : Ω W 1 => obsEval g (stepState g E X (gueBlock W 1 y 0))
      (MvPolynomial.X v)) := by
  have hg0 : 0 < g := by linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set t := normalH E / g with ht
  set n := 1 + 2 * normalH E * ‖gueBlock W 1 x 0‖ / g with hn
  have ht0 : 0 ≤ t := div_nonneg (ci_normalH_nonneg E) hg0.le
  have hn1 : 1 ≤ n := by
    have := ci_normalH_nonneg E
    have : 0 ≤ 2 * normalH E * ‖gueBlock W 1 x 0‖ / g := by positivity
    rw [hn]
    linarith
  have hn9 : n ≤ n ^ 9 := le_self_pow₀ hn1 (by norm_num)
  have hY : ∀ y : Ω W 1, IsState (stepState g E X (gueBlock W 1 y 0)) := fun y =>
    isState_stepState g E hX (gueBlock_isHermitian W 1 y 0)
  have hline : ∀ (φ : State W → ℂ) (y : Ω W 1),
      (fun s : ℝ => φ (stepState g E X (gueBlock W 1 (x + s • y) 0))) =
        fun s : ℝ => φ (stepState g E X (gueBlock W 1 x 0 + (s : ℂ) • gueBlock W 1 y 0)) := by
    intro φ y
    funext s
    rw [ci_gueBlock_line]
  cases v with
  | m k =>
    have hfun : (fun y : Ω W 1 => obsEval g (stepState g E X (gueBlock W 1 y 0))
        (MvPolynomial.X (ObsVar.m k))) =
          fun y => obsM k.1 (stepState g E X (gueBlock W 1 y 0)) := by
      funext y
      simp [obsEval]
    have hcd := contDiff_obsM_stepState g E hX k.1
    rw [hfun]
    refine ⟨⟨_, (hcd.differentiable one_ne_zero x).hasFDerivAt, ?_⟩, by
      simpa [obsEval] using norm_obsM_le_one k.1 (hY x), hcd⟩
    have hb := ci_of_line (hcd.differentiable one_ne_zero x).hasFDerivAt
      (c := 4 * k.1.natAbs * t * n * (W : ℝ)⁻¹) (by positivity) fun y => by
        obtain ⟨D, hD, hDb⟩ := ci_line_obsM hg0 E hW hX (gueBlock_isHermitian W 1 x 0)
          (gueBlock_isHermitian W 1 y 0) k.1
        refine ⟨D, by rw [hline (obsM k.1) y]; exact hD, hDb.trans (le_of_eq ?_)⟩
        rw [ci_sqrt_HS_gueBlock]
        have hWW : (√(W : ℝ))⁻¹ * (√(W : ℝ))⁻¹ = (W : ℝ)⁻¹ := by
          rw [← mul_inv, Real.mul_self_sqrt hW0.le]
        calc _ = (k.1.natAbs : ℝ) * (normalH E / g * (4 * (1 + 2 * normalH E *
              ‖gueBlock W 1 x 0‖ / g))) * ((√(W : ℝ))⁻¹ * (√(W : ℝ))⁻¹) * √(∑ i, y i ^ 2) := by
              ring
          _ = _ := by rw [hWW, ht, hn]; ring
    refine hb.trans ?_
    simp only [ciG]
    have : 0 ≤ √2 * (4 * (k.1.natAbs : ℝ)) * (W : ℝ)⁻¹ * t := by positivity
    calc √2 * (4 * k.1.natAbs * t * n * (W : ℝ)⁻¹) =
        √2 * (4 * (k.1.natAbs : ℝ)) * (W : ℝ)⁻¹ * t * n := by ring
      _ ≤ √2 * (4 * (k.1.natAbs : ℝ)) * (W : ℝ)⁻¹ * t * n ^ 9 :=
          mul_le_mul_of_nonneg_left hn9 this
      _ = _ := by ring
  | f k =>
    have hfun : (fun y : Ω W 1 => obsEval g (stepState g E X (gueBlock W 1 y 0))
        (MvPolynomial.X (ObsVar.f k))) =
          fun y => obsF k.1 (stepState g E X (gueBlock W 1 y 0)) := by
      funext y
      simp [obsEval]
    have hcd := contDiff_obsF_stepState g E hX k.1
    rw [hfun]
    refine ⟨⟨_, (hcd.differentiable one_ne_zero x).hasFDerivAt, ?_⟩, by
      simpa [obsEval] using norm_obsF_le_one k.1 (hY x), hcd⟩
    have hb := ci_of_line (hcd.differentiable one_ne_zero x).hasFDerivAt
      (c := (8 + 4 * k.1.natAbs) * t * n ^ 9 * (√W)⁻¹) (by positivity) fun y => by
        obtain ⟨D, hD, hDb⟩ := ci_line_obsF hg0 E hX (gueBlock_isHermitian W 1 x 0)
          (gueBlock_isHermitian W 1 y 0) k.1
        refine ⟨D, by rw [hline (obsF k.1) y]; exact hD, hDb.trans ?_⟩
        have hH := ci_opNorm_le_HS (gueBlock W 1 y 0)
        rw [ci_sqrt_HS_gueBlock] at hH
        calc (8 + 4 * (k.1.natAbs : ℝ)) * (t * ‖gueBlock W 1 y 0‖) * n ^ 9 ≤
            (8 + 4 * (k.1.natAbs : ℝ)) * (t * ((√W)⁻¹ * √(∑ i, y i ^ 2))) * n ^ 9 := by gcongr
          _ = _ := by ring
    refine hb.trans (le_of_eq ?_)
    simp only [ciG]
    ring
  | w =>
    have hc : (fun y : Ω W 1 => obsEval g (stepState g E X (gueBlock W 1 y 0))
        (MvPolynomial.X ObsVar.w)) = fun _ => (W : ℂ)⁻¹ := by
      funext y
      simp [obsEval]
    rw [hc]
    refine ⟨⟨0, hasFDerivAt_const _ x, by simp [ciG]⟩, ?_, contDiff_const⟩
    have e : obsEval g (stepState g E X (gueBlock W 1 x 0)) (MvPolynomial.X ObsVar.w) =
        (W : ℂ)⁻¹ := by simp [obsEval]
    rw [e, norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hW)
  | γ =>
    have hc : (fun y : Ω W 1 => obsEval g (stepState g E X (gueBlock W 1 y 0))
        (MvPolynomial.X ObsVar.γ)) = fun _ => (((g ^ 2)⁻¹ : ℝ) : ℂ) := by
      funext y
      simp [obsEval]
    rw [hc]
    refine ⟨⟨0, hasFDerivAt_const _ x, by simp [ciG]⟩, ?_, contDiff_const⟩
    have e : obsEval g (stepState g E X (gueBlock W 1 x 0)) (MvPolynomial.X ObsVar.γ) =
        (((g ^ 2)⁻¹ : ℝ) : ℂ) := by simp [obsEval]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hg)

private lemma ci_obsEval_eq (g : ℝ) {W : ℕ} (Y : State W) (P : ObsPoly) :
    obsEval g Y P = aeval (fun v => obsEval g Y (MvPolynomial.X v)) P := by
  have : obsEval g Y = aeval (fun v => obsEval g Y (MvPolynomial.X v)) :=
    MvPolynomial.algHom_ext fun v => by simp
  exact congrArg (fun φ : ObsPoly →ₐ[ℂ] ℂ => φ P) this

private lemma ci_one_add_two_pow_le (q : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (1 + 2 * a) ^ q ≤ 3 ^ q * (1 + a ^ q) := by
  have hq : 0 ≤ a ^ q := pow_nonneg ha q
  rcases le_total a 1 with h | h
  · calc (1 + 2 * a) ^ q ≤ 3 ^ q := pow_le_pow_left₀ (by positivity) (by linarith) q
      _ ≤ 3 ^ q * (1 + a ^ q) := le_mul_of_one_le_right (by positivity) (by linarith)
  · calc (1 + 2 * a) ^ q ≤ (3 * a) ^ q := pow_le_pow_left₀ (by positivity) (by linarith) q
      _ = 3 ^ q * a ^ q := mul_pow _ _ _
      _ ≤ 3 ^ q * (1 + a ^ q) := by gcongr; linarith

private lemma ci_integral_norm_pow_le (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ, ∫ ω, ‖gueBlock W 1 ω 0‖ ^ q ∂(μ W 1) ≤ C := by
  obtain ⟨C, hC, h⟩ := lintegral_norm_gueBlock_pow_le q
  refine ⟨C, hC, fun W => ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => by positivity)
    (integrable_norm_gueBlock_pow W q).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hC.le ((le_of_eq ?_).trans (h W))
  congr 1
  funext ω
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The moment Poincaré inequality applied to `ω ↦ P(C′, v′)` with the gradient bounds of the
variables. -/
private lemma ci_innov {W : ℕ} (hW : 1 ≤ W) {g : ℝ} (hg : 1 ≤ g) {E : ℝ} (hE : normalH E ≤ 1)
    {X : State W} (hX : IsState X) (P : ObsPoly) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∑ d ∈ P.support, ‖P.coeff d‖ * ∑ v ∈ d.support, (d v : ℝ) * ciG W v ≤ B)
    {p : ℕ} {Kp : ℝ} (hKp : 0 ≤ Kp)
    (hP : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℂ),
      ContDiff ℝ 1 f → ∀ {C : ℝ} {k : ℕ}, (∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k) →
        ∫ x, ‖f x - ∫ y, f y ∂(stdGauss ι)‖ ^ (2 * p) ∂(stdGauss ι) ≤
          Kp * ∫ x, gradSq f x ^ p ∂(stdGauss ι))
    {Cq : ℝ} (hC : ∫ ω, ‖gueBlock W 1 ω 0‖ ^ (18 * p) ∂(μ W 1) ≤ Cq) :
    ∫ ω, ‖obsEval g (stepState g E X (gueBlock W 1 ω 0)) P -
        transOp g E (fun Y => obsEval g Y P) X‖ ^ (2 * p) ∂(μ W 1) ≤
      Kp * ((B / g) ^ (2 * p) * (3 ^ (18 * p) * (1 + Cq))) := by
  have hg0 : 0 < g := by linarith
  set ψ : ObsVar → Ω W 1 → ℂ := fun v y =>
    obsEval g (stepState g E X (gueBlock W 1 y 0)) (MvPolynomial.X v) with hψ
  set f : Ω W 1 → ℂ := fun y => obsEval g (stepState g E X (gueBlock W 1 y 0)) P with hf
  have hfψ : f = fun y => aeval (fun v => ψ v y) P := by
    funext y
    exact ci_obsEval_eq g _ P
  set t := normalH E / g with ht
  set nf : Ω W 1 → ℝ := fun x => 1 + 2 * normalH E * ‖gueBlock W 1 x 0‖ / g with hnf
  have hh0 := ci_normalH_nonneg E
  have ht0 : 0 ≤ t := div_nonneg hh0 hg0.le
  have htg : t ≤ 1 / g := div_le_div_of_nonneg_right hE hg0.le
  have hnf1 : ∀ x, 1 ≤ nf x := fun x => by
    have : 0 ≤ 2 * normalH E * ‖gueBlock W 1 x 0‖ / g := by positivity
    simp only [hnf]
    linarith
  have hnfV : ∀ x, nf x ≤ 1 + 2 * ‖gueBlock W 1 x 0‖ := fun x => by
    simp only [hnf]
    have h1 : normalH E * ‖gueBlock W 1 x 0‖ / g ≤ ‖gueBlock W 1 x 0‖ := by
      rw [div_le_iff₀ hg0]
      nlinarith [norm_nonneg (gueBlock W 1 x 0)]
    have e : 2 * normalH E * ‖gueBlock W 1 x 0‖ / g = 2 * (normalH E * ‖gueBlock W 1 x 0‖ / g) := by
      ring
    linarith
  have hpt : ∀ x, ∃ L, HasFDerivAt f L x ∧ ‖ciV L‖ ≤ B * (t * nf x ^ 9) := by
    intro x
    obtain ⟨L, hL, hb⟩ := ci_aeval ψ x (fun v => ciG W v * (t * nf x ^ 9))
      (fun v => (ci_var hW hg E hX x v).1) (fun v => (ci_var hW hg E hX x v).2.1) P
    refine ⟨L, by rw [hfψ]; exact hL, hb.trans ?_⟩
    have e : ∑ d ∈ P.support, ‖P.coeff d‖ * ∑ v ∈ d.support, (d v : ℝ) * (ciG W v * (t * nf x ^ 9))
        = (∑ d ∈ P.support, ‖P.coeff d‖ * ∑ v ∈ d.support, (d v : ℝ) * ciG W v) *
          (t * nf x ^ 9) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun v _ => ?_
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hB (by have := hnf1 x; positivity)
  have hcd : ContDiff ℝ 1 f := by
    rw [hfψ]
    exact ci_contDiff_aeval ψ (fun v => (ci_var hW hg E hX 0 v).2.2) P
  have hfd : ∀ x, ‖ciV (fderiv ℝ f x)‖ ≤ B * (t * nf x ^ 9) := fun x => by
    obtain ⟨L, hL, hb⟩ := hpt x
    rwa [hL.fderiv]
  -- polynomial growth of the derivative
  set cd : ℝ := (Fintype.card (Fin 1 × Fin W × Fin W) : ℝ) with hcd'
  have hV : ∀ x : Ω W 1, ‖gueBlock W 1 x 0‖ ≤ √cd * ‖x‖ := fun x => by
    refine (ci_opNorm_le_HS _).trans ?_
    rw [ci_sqrt_HS_gueBlock, ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (by positivity)]
    have hW1 : (√(W : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by exact_mod_cast hW))
    calc (√(W : ℝ))⁻¹ * √(∑ i, x i ^ 2) ≤ 1 * √(∑ i, x i ^ 2) := by gcongr
      _ = √(∑ i, x i ^ 2) := one_mul _
      _ ≤ √(cd * ‖x‖ ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin 1 × Fin W × Fin W, ‖x‖ ^ 2 :=
                Finset.sum_le_sum fun i _ => by
                  rw [← sq_abs]
                  exact pow_le_pow_left₀ (abs_nonneg _)
                    (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i) 2
            _ = cd * ‖x‖ ^ 2 := by simp [hcd']
  have hgrowth : ∀ x, ‖fderiv ℝ f x‖ ≤ (cd * (B * t) * (1 + 2 * √cd) ^ 9) * (1 + ‖x‖) ^ 9 := by
    intro x
    refine (ci_opNorm_le _).trans ?_
    have h1 : nf x ≤ (1 + 2 * √cd) * (1 + ‖x‖) := by
      refine (hnfV x).trans ?_
      have := hV x
      nlinarith [norm_nonneg x, Real.sqrt_nonneg cd]
    have h2 : nf x ^ 9 ≤ (1 + 2 * √cd) ^ 9 * (1 + ‖x‖) ^ 9 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith [hnf1 x]) h1 9
    calc cd * ‖ciV (fderiv ℝ f x)‖ ≤ cd * (B * (t * nf x ^ 9)) := by
          gcongr
          exact hfd x
      _ ≤ cd * (B * (t * ((1 + 2 * √cd) ^ 9 * (1 + ‖x‖) ^ 9))) := by gcongr
      _ = _ := by ring
  have h1 := hP f hcd hgrowth
  rw [← μ_eq_stdGauss] at h1
  change ∫ ω, ‖f ω - ∫ ω', f ω' ∂(μ W 1)‖ ^ (2 * p) ∂(μ W 1) ≤ _
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hKp)
  -- the gradient moment
  set q := 18 * p with hq
  have hint : Integrable (fun x : Ω W 1 => (B / g) ^ (2 * p) *
      (3 ^ q * (1 + ‖gueBlock W 1 x 0‖ ^ q))) (μ W 1) :=
    (((integrable_const 1).add (integrable_norm_gueBlock_pow W q)).const_mul _).const_mul _
  have hpw : ∀ x, gradSq f x ^ p ≤ (B / g) ^ (2 * p) * (3 ^ q * (1 + ‖gueBlock W 1 x 0‖ ^ q)) := by
    intro x
    rw [ci_gradSq, ← pow_mul]
    have hBt : B * t ≤ B / g := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left htg hB0
    calc ‖ciV (fderiv ℝ f x)‖ ^ (2 * p) ≤ (B * (t * nf x ^ 9)) ^ (2 * p) :=
          pow_le_pow_left₀ (norm_nonneg _) (hfd x) _
      _ = (B * t) ^ (2 * p) * nf x ^ q := by rw [hq, ← mul_assoc, mul_pow, ← pow_mul]; ring_nf
      _ ≤ (B / g) ^ (2 * p) * (1 + 2 * ‖gueBlock W 1 x 0‖) ^ q :=
          mul_le_mul (pow_le_pow_left₀ (mul_nonneg hB0 ht0) hBt _)
            (pow_le_pow_left₀ (by linarith [hnf1 x]) (hnfV x) _) (by positivity)
            (pow_nonneg (div_nonneg hB0 hg0.le) _)
      _ ≤ (B / g) ^ (2 * p) * (3 ^ q * (1 + ‖gueBlock W 1 x 0‖ ^ q)) :=
          mul_le_mul_of_nonneg_left (ci_one_add_two_pow_le q (norm_nonneg _))
            (pow_nonneg (div_nonneg hB0 hg0.le) _)
  have hI : ∫ x, (B / g) ^ (2 * p) * (3 ^ q * (1 + ‖gueBlock W 1 x 0‖ ^ q)) ∂(μ W 1) =
      (B / g) ^ (2 * p) * (3 ^ q * (1 + ∫ ω, ‖gueBlock W 1 ω 0‖ ^ q ∂(μ W 1))) := by
    rw [integral_const_mul, integral_const_mul, integral_add (integrable_const 1)
      (integrable_norm_gueBlock_pow W q)]
    simp
  calc ∫ x, gradSq f x ^ p ∂(μ W 1) ≤
        ∫ x, (B / g) ^ (2 * p) * (3 ^ q * (1 + ‖gueBlock W 1 x 0‖ ^ q)) ∂(μ W 1) :=
        integral_mono_of_nonneg (ae_of_all _ fun x => by
          change 0 ≤ gradSq f x ^ p
          rw [ci_gradSq]; positivity) hint
          (ae_of_all _ hpw)
    _ = (B / g) ^ (2 * p) * (3 ^ q * (1 + ∫ ω, ‖gueBlock W 1 ω 0‖ ^ q ∂(μ W 1))) := hI
    _ ≤ (B / g) ^ (2 * p) * (3 ^ q * (1 + Cq)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
          (pow_nonneg (div_nonneg hB0 hg0.le) _)

private lemma ci_G_nonneg (W : ℕ) (v : ObsVar) : 0 ≤ ciG W v := by
  cases v <;> simp only [ciG] <;> positivity

private lemma ci_C_nonneg (v : ObsVar) : 0 ≤ ciC v := by
  unfold ciC
  positivity

/-- The weighted coefficient sum of a polynomial with support in `S` and coefficients bounded by
`K₀`. -/
private lemma ci_coef_le {P : ObsPoly} {S : Finset (ObsVar →₀ ℕ)} {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (hS : P.support ⊆ S) (hK : ∀ d, ‖P.coeff d‖ ≤ K₀) {ω : ℝ} (hω : 0 ≤ ω) (W : ℕ)
    (hv : ∀ d ∈ P.support, ∀ v ∈ d.support, ciG W v ≤ ciC v * ω) :
    ∑ d ∈ P.support, ‖P.coeff d‖ * ∑ v ∈ d.support, (d v : ℝ) * ciG W v ≤
      K₀ * (∑ d ∈ S, ∑ v ∈ d.support, (d v : ℝ) * ciC v) * ω := by
  have hw : ∀ d : ObsVar →₀ ℕ, 0 ≤ ∑ v ∈ d.support, (d v : ℝ) * ciC v := fun d =>
    Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (ci_C_nonneg v)
  calc ∑ d ∈ P.support, ‖P.coeff d‖ * ∑ v ∈ d.support, (d v : ℝ) * ciG W v ≤
      ∑ d ∈ P.support, K₀ * (∑ v ∈ d.support, (d v : ℝ) * ciC v) * ω := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [mul_assoc, Finset.sum_mul]
        refine mul_le_mul (hK d) (Finset.sum_le_sum fun v hv' => ?_)
          (Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (ci_G_nonneg W v)) hK₀
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hv d hd v hv') (Nat.cast_nonneg _)
    _ ≤ ∑ d ∈ S, K₀ * (∑ v ∈ d.support, (d v : ℝ) * ciC v) * ω :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun d _ _ =>
          mul_nonneg (mul_nonneg hK₀ (hw d)) hω
    _ = K₀ * (∑ d ∈ S, ∑ v ∈ d.support, (d v : ℝ) * ciC v) * ω := by
        rw [Finset.mul_sum, Finset.sum_mul]

/-- (11.58) [lg:eq:innovations]: conditional `L^{2p}` innovations of the corrected observables,
uniformly in `W ≥ 1`, `g ≥ 1`, the window and the state. -/
theorem innovation_moment_corrObs (R : ℕ) (Ks : Finset NzInt) (p : ℕ) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g →
      ∀ E : ℝ, |E| ≤ E₁ → ∀ X : State W, IsState X → ∀ k ∈ Ks,
        ∫ ω, ‖obsEval g (stepState g E X (gueBlock W 1 ω 0)) (corrObsM E R k) -
            transOp g E (fun Y => obsEval g Y (corrObsM E R k)) X‖ ^ (2 * p) ∂(μ W 1) ≤
          K * (1 / (g * W)) ^ (2 * p) ∧
        ∫ ω, ‖obsEval g (stepState g E X (gueBlock W 1 ω 0)) (corrObsF E R k) -
            transOp g E (fun Y => obsEval g Y (corrObsF E R k)) X‖ ^ (2 * p) ∂(μ W 1) ≤
          K * (1 / (g * Real.sqrt W)) ^ (2 * p) := by
  obtain ⟨E₀, hE₀, S, K₀, hK₀, hS⟩ := corrCoeff_bounded R Ks
  obtain ⟨Kp, hKp, hP⟩ := moment_poincare_grad_poly p
  obtain ⟨Cq, hCq, hC⟩ := ci_integral_norm_pow_le (18 * p)
  set A : ℝ := K₀ * ∑ d ∈ S, ∑ v ∈ d.support, (d v : ℝ) * ciC v with hA
  have hA0 : 0 ≤ A := mul_nonneg hK₀.le (Finset.sum_nonneg fun d _ => Finset.sum_nonneg
    fun v _ => mul_nonneg (Nat.cast_nonneg _) (ci_C_nonneg v))
  set M3 : ℝ := 3 ^ (18 * p) * (1 + Cq) with hM3
  have hM30 : 0 ≤ M3 := by positivity
  refine ⟨min E₀ 1, lt_min hE₀ one_pos, Kp * A ^ (2 * p) * M3 + 1, by positivity,
    fun W hW g hg E hE X hX k hk => ?_⟩
  have hg0 : 0 < g := by linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hsW1 : 1 ≤ √(W : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hW)
  have hWs : (W : ℝ)⁻¹ ≤ (√(W : ℝ))⁻¹ := by
    refine inv_anti₀ (by linarith) ?_
    nlinarith [Real.mul_self_sqrt hW0.le]
  have hEh : normalH E ≤ 1 := ci_normalH_le (hE.trans (min_le_right _ _))
  have hE₀' : |E| ≤ E₀ := hE.trans (min_le_left _ _)
  obtain ⟨hdM, -, -, hcM⟩ := hS E hE₀' k hk (.m k) (by simp)
  obtain ⟨hdF, -, -, hcF⟩ := hS E hE₀' k hk (.f k) (by simp)
  have htr := (corrObs_form E R k).2.2.1
  have hfin : ∀ {B x : ℝ}, 0 ≤ x → B = A * x →
      Kp * ((B / g) ^ (2 * p) * M3) ≤ (Kp * A ^ (2 * p) * M3 + 1) * (x / g) ^ (2 * p) := by
    intro B x hx hB
    rw [hB, mul_div_assoc, mul_pow]
    have h0 : 0 ≤ (x / g) ^ (2 * p) := pow_nonneg (div_nonneg hx hg0.le) _
    calc Kp * (A ^ (2 * p) * (x / g) ^ (2 * p) * M3) =
        Kp * A ^ (2 * p) * M3 * (x / g) ^ (2 * p) := by ring
      _ ≤ (Kp * A ^ (2 * p) * M3 + 1) * (x / g) ^ (2 * p) := by
          rw [add_mul, one_mul]
          linarith
  constructor
  · have hcoef := ci_coef_le (P := corrObsM E R k) hK₀.le hdM (fun d => (hcM d).1)
      (inv_nonneg.2 hW0.le) W fun d hd v hv => by
        have hv' : v ∈ traceVars :=
          (mem_supported.1 htr) ((mem_vars_iff_mem_support v).2 ⟨d, hd, hv⟩)
        cases v with
        | m k' =>
          simp only [ciG, ciC, ObsVar.idx]
          gcongr
          linarith
        | f k' =>
          exfalso
          rcases hv' with ⟨h1, -⟩ | ⟨j, hj⟩
          · exact k'.2 h1
          · exact ObsVar.noConfusion hj
        | w =>
          exfalso
          rcases hv' with ⟨-, h2⟩ | ⟨j, hj⟩
          · exact h2 rfl
          · exact ObsVar.noConfusion hj
        | γ =>
          simp only [ciG]
          exact mul_nonneg (ci_C_nonneg _) (inv_nonneg.2 hW0.le)
    have h := ci_innov hW hg hEh hX (corrObsM E R k) (mul_nonneg hA0 (inv_nonneg.2 hW0.le))
      hcoef hKp.le hP (hC W)
    refine h.trans ((hfin (inv_nonneg.2 hW0.le) rfl).trans (le_of_eq ?_))
    congr 2
    field_simp
  · have hcoef := ci_coef_le (P := corrObsF E R k) hK₀.le hdF (fun d => (hcF d).1)
      (inv_nonneg.2 (Real.sqrt_nonneg _)) W fun d _ v _ => by
        cases v with
        | m k' =>
          simp only [ciG, ciC, ObsVar.idx]
          have : 0 ≤ √2 * (4 * (k'.1.natAbs : ℝ)) := by positivity
          calc √2 * (4 * (k'.1.natAbs : ℝ)) * (W : ℝ)⁻¹ ≤
              √2 * (4 * (k'.1.natAbs : ℝ)) * (√(W : ℝ))⁻¹ :=
                mul_le_mul_of_nonneg_left hWs this
            _ ≤ √2 * (8 + 4 * (k'.1.natAbs : ℝ)) * (√(W : ℝ))⁻¹ := by
                gcongr
                linarith
        | f k' => simp [ciG, ciC, ObsVar.idx]
        | w => simpa [ciG] using mul_nonneg (ci_C_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _))
        | γ => simpa [ciG] using mul_nonneg (ci_C_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _))
    have h := ci_innov hW hg hEh hX (corrObsF E R k)
      (mul_nonneg hA0 (inv_nonneg.2 (Real.sqrt_nonneg _))) hcoef hKp.le hP (hC W)
    refine h.trans ((hfin (inv_nonneg.2 (Real.sqrt_nonneg _)) rfl).trans (le_of_eq ?_))
    congr 2
    field_simp

end LSBA
