import LSBA.Upper.ChainBridge

/-!
# The enlarged right space and the inverse-image inclusion

Section 9.4.1 [su:sec:retained-geometry], regime (i). With the right product `A` and
`B_1 = g² R←_6` split at `s` into `B_{1,>} = B_1 1_{|x| > s}(B_1)` and
`B_{1,<} = B_1 1_{|x| ≤ s}(B_1)`, the space `U = ran A_>* + ran B_{1,>}` is the range of
`1_{(t², ∞)}(A* A) + 1_{|x| > s}(B_1)`; its projection is `1 - 1_{(-∞, 0]}` of that sum. It is a
function of the right-cavity window alone, and conjugating the window blocks by a unitary `O`
conjugates it by `O`; this is the invariance behind (9.56) [us:eq:Haar]. Where `R̃` is invertible,
every vector of `ran Q` lies in the inverse image `{x : (V_5 - E - g² R_4 - B_{1,<}) x ∈ U}`, the
inclusion (9.57) [us:eq:erase]; in regime (ii), `{x : (V_5 - E - g² R_4 - g² R←_6) x ∈ ran A_>*}`
(Section 9.4.1 [su:sec:retained-geometry]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The projection onto `U = ran A_>* + ran B_{1,>}` of (9.56) [us:eq:Haar], with `A_>* ` from the
threshold `t` and `B_{1,>}` the part of `B_1 = g² R←_6` with `|x| > s`. -/
def cavU (W : ℕ) (g E : ℝ) (q : ℕ) (t s : ℝ) (ω : Ω W q) : Matrix (Fin W) (Fin W) ℂ :=
  1 - specProj (retSpec W g E q t ω +
    specProj (((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) {x | s < |x|}) (Set.Iic 0)

/-- The same projection as a function of the right-cavity window `w : Ω W h` (`h = q - 6`), through
the Riccati chain started at `0`: `A* = ricProd … h` and `R←_6 = ricChain … h`. -/
def cavUWin (W : ℕ) (g E : ℝ) (h : ℕ) (t s : ℝ) (w : Ω W h) : Matrix (Fin W) (Fin W) ℂ :=
  1 - specProj (specProj (ricProd W g E h 0 w h * (ricProd W g E h 0 w h)ᴴ) (Set.Ioi (t ^ 2)) +
    specProj (((g : ℂ) ^ 2) • ricChain W g E h 0 w h) {x | s < |x|}) (Set.Iic 0)

private lemma RetainedSpace_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
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

private lemma RetainedSpace_measurable_mul {W : ℕ} {α : Type*} [MeasurableSpace α]
    {F G : α → Matrix (Fin W) (Fin W) ℂ} (hF : Measurable F) (hG : Measurable G) :
    Measurable fun x => F x * G x := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => hF.eval_matrix.mul hG.eval_matrix

private lemma RetainedSpace_measurable_conjTranspose {W : ℕ} {α : Type*} [MeasurableSpace α]
    {F : α → Matrix (Fin W) (Fin W) ℂ} (hF : Measurable F) :
    Measurable fun x => (F x)ᴴ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.conjTranspose_apply]
  exact continuous_star.measurable.comp hF.eval_matrix

private lemma RetainedSpace_measurable_gueBlock (W L : ℕ) (a : Fin L) :
    Measurable fun ω : Ω W L => gueBlock W L ω a := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma RetainedSpace_measurable_block (W h : ℕ) (j : ℕ) :
    Measurable fun ω : Ω W h =>
      (if hj : j < h then gueBlock W h ω ⟨j, hj⟩ else 0 : Matrix (Fin W) (Fin W) ℂ) := by
  by_cases hj : j < h
  · simp only [hj, ↓reduceDIte]
    exact RetainedSpace_measurable_gueBlock W h ⟨j, hj⟩
  · simp only [hj, ↓reduceDIte]
    exact measurable_const

private lemma RetainedSpace_measurable_chain (W : ℕ) (g E : ℝ) (h : ℕ)
    (R : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    Measurable fun ω : Ω W h => ricChain W g E h R ω j := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    simp only [ricChain]
    refine RetainedSpace_measurable_inv.comp ?_
    exact ((RetainedSpace_measurable_block W h j).sub measurable_const).sub
      (ih.fun_const_smul ((g : ℂ) ^ 2))

private lemma RetainedSpace_measurable_prod (W : ℕ) (g E : ℝ) (h : ℕ)
    (R : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    Measurable fun ω : Ω W h => ricProd W g E h R ω j := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    simp only [ricProd]
    exact RetainedSpace_measurable_mul (RetainedSpace_measurable_chain W g E h R (j + 1)) ih

/-- For open `S` and Hermitian values, `1_S(F x)` is measurable: it is `1 - 1_{Sᶜ}(F x)` with
`Sᶜ` closed. -/
private lemma RetainedSpace_measurable_specProj_open {n : Type*} [Fintype n] [DecidableEq n]
    {α : Type*} [MeasurableSpace α] {F : α → Matrix n n ℂ} (hF : Measurable F)
    (hH : ∀ x, (F x).IsHermitian) {S : Set ℝ} (hS : IsOpen S) :
    Measurable fun x => specProj (F x) S := by
  have h : (fun x => specProj (F x) S) = fun x => 1 - specProj (F x) Sᶜ := by
    funext x
    exact eq_sub_of_add_eq (specProj_add_compl (hH x) S).1
  rw [h]
  exact measurable_const.sub ((measurable_specProj hS.isClosed_compl).comp hF)

private lemma RetainedSpace_gsq_herm {W : ℕ} (g : ℝ) {M : Matrix (Fin W) (Fin W) ℂ}
    (hM : M.IsHermitian) : (((g : ℂ) ^ 2) • M).IsHermitian := by
  unfold Matrix.IsHermitian at hM ⊢
  rw [Matrix.conjTranspose_smul, hM, Complex.star_def, map_pow, Complex.conj_ofReal]

/-- The projection `1 - 1_{(-∞, 0]}(P₁ + P₂)` of two spectral projections is measurable, for
measurable Hermitian-valued `F`, `G`. -/
private lemma RetainedSpace_proj_measurable {W : ℕ} {α : Type*} [MeasurableSpace α]
    {F G : α → Matrix (Fin W) (Fin W) ℂ} (hF : Measurable F) (hG : Measurable G)
    (hFH : ∀ x, (F x).IsHermitian) (hGH : ∀ x, (G x).IsHermitian) (a s : ℝ) :
    Measurable fun x => 1 - specProj (specProj (F x) (Set.Ioi a) +
      specProj (G x) {y | s < |y|}) (Set.Iic 0) := by
  have h1 := RetainedSpace_measurable_specProj_open hF hFH (isOpen_Ioi (a := a))
  have h2 := RetainedSpace_measurable_specProj_open hG hGH
    (isOpen_lt continuous_const continuous_abs : IsOpen {y : ℝ | s < |y|})
  exact measurable_const.sub ((measurable_specProj isClosed_Iic).comp (h1.add h2))

/-- `1 - 1_{(-∞, 0]}(P₁ + P₂)` of two spectral projections is an orthogonal projection. -/
private lemma RetainedSpace_proj_spec {W : ℕ} {F G : Matrix (Fin W) (Fin W) ℂ}
    (hF : F.IsHermitian) (hG : G.IsHermitian) (a s : ℝ) :
    (1 - specProj (specProj F (Set.Ioi a) + specProj G {y | s < |y|}) (Set.Iic 0)).IsHermitian ∧
    (1 - specProj (specProj F (Set.Ioi a) + specProj G {y | s < |y|}) (Set.Iic 0)) *
      (1 - specProj (specProj F (Set.Ioi a) + specProj G {y | s < |y|}) (Set.Iic 0)) =
      1 - specProj (specProj F (Set.Ioi a) + specProj G {y | s < |y|}) (Set.Iic 0) := by
  have h1 := (specProj_spec hF (Set.Ioi a)).1
  have h2 := (specProj_spec hG {y | s < |y|}).1
  obtain ⟨hK, hKK, -, -⟩ := specProj_spec (h1.add h2) (Set.Iic 0)
  refine ⟨Matrix.isHermitian_one.sub hK, ?_⟩
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hKK]
  abel

/-- Conjugating the two spectral projections by a unitary conjugates `1 - 1_{(-∞, 0]}(P₁ + P₂)`. -/
private lemma RetainedSpace_proj_conj {W : ℕ} {F G U : Matrix (Fin W) (Fin W) ℂ}
    (hF : F.IsHermitian) (hG : G.IsHermitian) (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ)
    (a s : ℝ) :
    1 - specProj (specProj (U * F * Uᴴ) (Set.Ioi a) + specProj (U * G * Uᴴ) {y | s < |y|})
        (Set.Iic 0) =
      U * (1 - specProj (specProj F (Set.Ioi a) + specProj G {y | s < |y|}) (Set.Iic 0)) * Uᴴ := by
  have hUU : U * Uᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
  have h1 := (specProj_spec hF (Set.Ioi a)).1
  have h2 := (specProj_spec hG {y | s < |y|}).1
  rw [specProj_conj hF hU, specProj_conj hG hU, ← Matrix.add_mul, ← Matrix.mul_add,
    specProj_conj (h1.add h2) hU, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU]

/-- `U` is a function of the right-cavity window. -/
theorem cavU_eq_cavUWin {W q : ℕ} (hq : 7 ≤ q) (g E t s : ℝ) (ω : Ω W q) :
    cavU W g E q t s ω = cavUWin W g E (q - 6) t s (windowSample (cavWin q) ω) := by
  have hA := cavProd_eq_ricProd hq g E ω
  have hR := cavR_eq_ricChain hq g E ω (m := q - 7) le_rfl
  rw [show q - 7 + 1 = q - 6 by omega] at hR
  unfold cavU cavUWin retSpec
  rw [← hA, ← hR, Matrix.conjTranspose_conjTranspose]

/-- On the right-cavity window, `U` is a measurable orthogonal projection, equivariant under the
common conjugation of the blocks. -/
theorem cavUWin_spec (W : ℕ) (g E : ℝ) (h : ℕ) (t s : ℝ) :
    Measurable (cavUWin W g E h t s) ∧
    (∀ w, (cavUWin W g E h t s w).IsHermitian ∧
      cavUWin W g E h t s w * cavUWin W g E h t s w = cavUWin W g E h t s w) ∧
    ∀ (O : Matrix.unitaryGroup (Fin W) ℂ) (w : Ω W h),
      cavUWin W g E h t s (conjMap W h O w) =
        (O : Matrix (Fin W) (Fin W) ℂ) * cavUWin W g E h t s w *
          star (O : Matrix (Fin W) (Fin W) ℂ) := by
  have hFH : ∀ w : Ω W h,
      (ricProd W g E h 0 w h * (ricProd W g E h 0 w h)ᴴ).IsHermitian := fun w =>
    Matrix.isHermitian_mul_conjTranspose_self _
  have hGH : ∀ w : Ω W h, (((g : ℂ) ^ 2) • ricChain W g E h 0 w h).IsHermitian := fun w =>
    RetainedSpace_gsq_herm g (ricChain_isHermitian Matrix.isHermitian_zero w h)
  refine ⟨?_, fun w => ?_, fun O w => ?_⟩
  · exact RetainedSpace_proj_measurable
      ((RetainedSpace_measurable_mul (RetainedSpace_measurable_prod W g E h 0 h)
        (RetainedSpace_measurable_conjTranspose (RetainedSpace_measurable_prod W g E h 0 h))))
      ((RetainedSpace_measurable_chain W g E h 0 h).fun_const_smul ((g : ℂ) ^ 2)) hFH hGH
      (t ^ 2) s
  · exact RetainedSpace_proj_spec (hFH w) (hGH w) (t ^ 2) s
  · have hOU : (O : Matrix (Fin W) (Fin W) ℂ) ∈ Matrix.unitaryGroup (Fin W) ℂ := O.2
    have hU' : (O : Matrix (Fin W) (Fin W) ℂ)ᴴ * (O : Matrix (Fin W) (Fin W) ℂ) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hOU
    have hc := (ricChain_conj W g E h 0 O w h).1
    have hp := (ricChain_conj W g E h 0 O w h).2
    rw [Matrix.mul_zero, Matrix.zero_mul] at hc hp
    unfold cavUWin
    rw [hc, hp, Matrix.star_eq_conjTranspose]
    have hM : (O : Matrix (Fin W) (Fin W) ℂ) * ricProd W g E h 0 w h *
          (O : Matrix (Fin W) (Fin W) ℂ)ᴴ *
        ((O : Matrix (Fin W) (Fin W) ℂ) * ricProd W g E h 0 w h *
          (O : Matrix (Fin W) (Fin W) ℂ)ᴴ)ᴴ =
        (O : Matrix (Fin W) (Fin W) ℂ) *
          (ricProd W g E h 0 w h * (ricProd W g E h 0 w h)ᴴ) * (O : Matrix (Fin W) (Fin W) ℂ)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (O : Matrix (Fin W) (Fin W) ℂ)ᴴ, hU', Matrix.one_mul]
    have hB : ((g : ℂ) ^ 2) • ((O : Matrix (Fin W) (Fin W) ℂ) * ricChain W g E h 0 w h *
          (O : Matrix (Fin W) (Fin W) ℂ)ᴴ) =
        (O : Matrix (Fin W) (Fin W) ℂ) * (((g : ℂ) ^ 2) • ricChain W g E h 0 w h) *
          (O : Matrix (Fin W) (Fin W) ℂ)ᴴ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hM, hB]
    exact RetainedSpace_proj_conj (hFH w) (hGH w) hOU (t ^ 2) s

open scoped ComplexOrder in
/-- For two Hermitian idempotents `P₁`, `P₂`, the spectral projection `K = 1_{(-∞, 0]}(P₁ + P₂)`
satisfies `K P₁ = 0` and `K P₂ = 0`: the sum is positive semidefinite, so `K` projects onto its
kernel. -/
private lemma RetainedSpace_K_mul {n : Type*} [Fintype n] [DecidableEq n] {P₁ P₂ : Matrix n n ℂ}
    (h₁ : P₁.IsHermitian) (i₁ : P₁ * P₁ = P₁) (h₂ : P₂.IsHermitian) (i₂ : P₂ * P₂ = P₂) :
    specProj (P₁ + P₂) (Set.Iic 0) * P₁ = 0 ∧ specProj (P₁ + P₂) (Set.Iic 0) * P₂ = 0 := by
  have hS : (P₁ + P₂).IsHermitian := h₁.add h₂
  have hpsd : (P₁ + P₂).PosSemidef := by
    have e : P₁ + P₂ = P₁ᴴ * P₁ + P₂ᴴ * P₂ := by rw [h₁.eq, h₂.eq, i₁, i₂]
    rw [e]
    exact (Matrix.posSemidef_conjTranspose_mul_self P₁).add
      (Matrix.posSemidef_conjTranspose_mul_self P₂)
  obtain ⟨hKH, hKK, -, -⟩ := specProj_spec hS (Set.Iic 0)
  have hKe : specProj (P₁ + P₂) (Set.Iic 0) = specProj (P₁ + P₂) (Set.Icc (-0) 0) := by
    simp only [specProj, hS, ↓reduceDIte]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Iic, Set.mem_Icc, neg_zero]
    exact ⟨fun h => ⟨hpsd.eigenvalues_nonneg k, h⟩, fun h => h.2⟩
  have hSK : (P₁ + P₂) * specProj (P₁ + P₂) (Set.Iic 0) = 0 := by
    have := (norm_mul_specProj_le hS (le_refl (0 : ℝ)) (S := Set.Icc (-0) 0) subset_rfl 0
      le_rfl).1
    rw [← hKe] at this
    exact norm_le_zero_iff.mp this
  generalize specProj (P₁ + P₂) (Set.Iic 0) = K at hKH hKK hSK
  have hX : K * P₁ * K + K * P₂ * K = 0 := by
    have : K * ((P₁ + P₂) * K) = 0 := by rw [hSK, Matrix.mul_zero]
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] using this
  have e₁ : (P₁ * K)ᴴ * (P₁ * K) = K * P₁ * K := by
    rw [Matrix.conjTranspose_mul, hKH.eq, h₁.eq]
    calc K * P₁ * (P₁ * K) = K * (P₁ * P₁) * K := by simp only [Matrix.mul_assoc]
      _ = K * P₁ * K := by rw [i₁]
  have e₂ : (P₂ * K)ᴴ * (P₂ * K) = K * P₂ * K := by
    rw [Matrix.conjTranspose_mul, hKH.eq, h₂.eq]
    calc K * P₂ * (P₂ * K) = K * (P₂ * P₂) * K := by simp only [Matrix.mul_assoc]
      _ = K * P₂ * K := by rw [i₂]
  have ht : (K * P₁ * K).trace + (K * P₂ * K).trace = 0 := by
    rw [← Matrix.trace_add, hX, Matrix.trace_zero]
  have t₁ : 0 ≤ (K * P₁ * K).trace := by
    rw [← e₁]; exact (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  have t₂ : 0 ≤ (K * P₂ * K).trace := by
    rw [← e₂]; exact (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  have z₁ : (K * P₁ * K).trace = 0 := by
    have : (K * P₁ * K).trace ≤ (K * P₁ * K).trace + (K * P₂ * K).trace :=
      le_add_of_nonneg_right t₂
    rw [ht] at this
    exact le_antisymm this t₁
  have z₂ : (K * P₂ * K).trace = 0 := by
    have : (K * P₂ * K).trace ≤ (K * P₁ * K).trace + (K * P₂ * K).trace :=
      le_add_of_nonneg_left t₁
    rw [ht] at this
    exact le_antisymm this t₂
  rw [← e₁] at z₁
  rw [← e₂] at z₂
  have y₁ := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp z₁
  have y₂ := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp z₂
  refine ⟨?_, ?_⟩
  · have : K * P₁ = (P₁ * K)ᴴ := by rw [Matrix.conjTranspose_mul, hKH.eq, h₁.eq]
    rw [this, y₁, Matrix.conjTranspose_zero]
  · have : K * P₂ = (P₂ * K)ᴴ := by rw [Matrix.conjTranspose_mul, hKH.eq, h₂.eq]
    rw [this, y₂, Matrix.conjTranspose_zero]

private lemma RetainedSpace_cavR_herm {W q : ℕ} (hq : 7 ≤ q) (g E : ℝ) (ω : Ω W q) :
    (((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)).IsHermitian := by
  rw [cavR_eq_ricChain hq g E ω (m := q - 7) le_rfl]
  exact RetainedSpace_gsq_herm g (ricChain_isHermitian Matrix.isHermitian_zero _ _)

/-- A vector `x` with `Q x = x` has `(V_5 - E - g² R_4 - g² R←_6) x` in the range of
`1_{(t², ∞)}(A* A)`: `x = R̃ z` with `z` in that range, or `R̃ = 0` and `x = 0`. -/
private lemma RetainedSpace_preimage {W q : ℕ} {g E : ℝ} (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ)
    (ω : Ω W q) (x : Fin W → ℂ) (hx : retProj W g E q R t ω *ᵥ x = x) :
    ∃ z : Fin W → ℂ, retSpec W g E q t ω *ᵥ z = z ∧
      (blockSeq W q ω 4 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R -
        ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) *ᵥ x = z := by
  have hP : retSpec W g E q t ω * retSpec W g E q t ω = retSpec W g E q t ω :=
    (specProj_spec (Matrix.isHermitian_conjTranspose_mul_self _) _).2.1
  generalize hG : (blockSeq W q ω 4 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R -
    ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) = G
  have hTG : cavRes W g E q R ω = G⁻¹ := by rw [← hG]; rfl
  by_cases hd : IsUnit G.det
  · set P := retSpec W g E q t ω with hPdef
    set N := (P * (G⁻¹)ᴴ * G⁻¹ * P + (1 - P))⁻¹ with hN
    refine ⟨P *ᵥ (N *ᵥ (P *ᵥ ((G⁻¹)ᴴ *ᵥ x))), ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, hP]
    · have hz : G⁻¹ *ᵥ (P *ᵥ (N *ᵥ (P *ᵥ ((G⁻¹)ᴴ *ᵥ x)))) = x := by
        conv_rhs => rw [← hx]
        unfold retProj flagProj
        rw [hTG, ← hPdef, ← hN]
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      calc G *ᵥ x = G *ᵥ (G⁻¹ *ᵥ (P *ᵥ (N *ᵥ (P *ᵥ ((G⁻¹)ᴴ *ᵥ x))))) := by rw [hz]
        _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
  · have h0 : G⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hd
    have hx0 : x = 0 := by
      rw [← hx]
      unfold retProj flagProj
      rw [hTG, h0]
      simp
    exact ⟨0, Matrix.mulVec_zero _, by rw [hx0, Matrix.mulVec_zero]⟩

/-- (9.57) [us:eq:erase]: where `R̃` is invertible, every `x` with `Q x = x` satisfies
`(V_5 - E - g² R_4 - B_{1,<}) x ∈ U`. -/
theorem retProj_mem_invImage_weak {W q : ℕ} (hq : 7 ≤ q) {g E : ℝ}
    (R : Matrix (Fin W) (Fin W) ℂ) (t s : ℝ) (ω : Ω W q) (hT : IsUnit (cavRes W g E q R ω))
    (x : Fin W → ℂ) (hx : retProj W g E q R t ω *ᵥ x = x) :
    (1 - cavU W g E q t s ω) *ᵥ ((blockSeq W q ω 4 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R -
        ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7) *
          specProj (((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) {x | |x| ≤ s}) *ᵥ x) = 0 := by
  have _hT := hT
  obtain ⟨z, hz1, hz2⟩ := RetainedSpace_preimage R t ω x hx
  have h1H : (retSpec W g E q t ω).IsHermitian :=
    (specProj_spec (Matrix.isHermitian_conjTranspose_mul_self _) _).1
  have h1I : retSpec W g E q t ω * retSpec W g E q t ω = retSpec W g E q t ω :=
    (specProj_spec (Matrix.isHermitian_conjTranspose_mul_self _) _).2.1
  have hBH := RetainedSpace_cavR_herm hq g E ω
  obtain ⟨h2H, h2I, h2C, -⟩ := specProj_spec hBH {y : ℝ | s < |y|}
  obtain ⟨hK1, hK2⟩ := RetainedSpace_K_mul h1H h1I h2H h2I
  have hP : specProj (((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) {y : ℝ | s < |y|} =
      1 - specProj (((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) {y : ℝ | |y| ≤ s} := by
    have hset : ({y : ℝ | s < |y|})ᶜ = {y : ℝ | |y| ≤ s} := by
      ext y; simp
    rw [← hset]
    exact eq_sub_of_add_eq (specProj_add_compl hBH {y : ℝ | s < |y|}).1
  have hU : 1 - cavU W g E q t s ω =
      specProj (retSpec W g E q t ω + specProj (((g : ℂ) ^ 2) • cavR W g E q ω (q - 7))
        {x | s < |x|}) (Set.Iic 0) := by
    unfold cavU
    rw [sub_sub_cancel]
  generalize hK : specProj (retSpec W g E q t ω + specProj (((g : ℂ) ^ 2) •
    cavR W g E q ω (q - 7)) {x | s < |x|}) (Set.Iic 0) = K at hU hK1 hK2
  generalize hB : ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7) = B at hP h2C hz2 hK2 ⊢
  generalize hP₂ : specProj B {y : ℝ | s < |y|} = P₂ at hP h2C hK2 ⊢
  generalize hP₁ : retSpec W g E q t ω = P₁ at hz1 hK1
  have hN : blockSeq W q ω 4 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R -
        B * specProj B {y : ℝ | |y| ≤ s} =
      (blockSeq W q ω 4 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R - B) + B * P₂ := by
    rw [hP, Matrix.mul_sub, Matrix.mul_one]
    abel
  have e1 : K *ᵥ z = 0 := by
    calc K *ᵥ z = K *ᵥ (P₁ *ᵥ z) := by rw [hz1]
      _ = (K * P₁) *ᵥ z := Matrix.mulVec_mulVec _ _ _
      _ = 0 := by rw [hK1, Matrix.zero_mulVec]
  have e2 : K *ᵥ ((B * P₂) *ᵥ x) = 0 := by
    rw [h2C, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hK2, Matrix.zero_mul, Matrix.zero_mulVec]
  rw [hU, hN, Matrix.add_mulVec, hz2, Matrix.mulVec_add, e1, e2, add_zero]

/-- Section 9.4.1 [su:sec:retained-geometry], regime (ii): where `R̃` is invertible, every `x` with
`Q x = x` satisfies `(V_5 - E - g² R_4 - g² R←_6) x ∈ ran A_>*`. -/
theorem retProj_mem_invImage {W q : ℕ} (hq : 7 ≤ q) {g E : ℝ} (R : Matrix (Fin W) (Fin W) ℂ)
    (t : ℝ) (ω : Ω W q) (hT : IsUnit (cavRes W g E q R ω)) (x : Fin W → ℂ)
    (hx : retProj W g E q R t ω *ᵥ x = x) :
    (1 - retSpec W g E q t ω) *ᵥ ((blockSeq W q ω 4 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R -
        ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) *ᵥ x) = 0 := by
  have _hq := hq
  have _hT := hT
  obtain ⟨z, hz1, hz2⟩ := RetainedSpace_preimage R t ω x hx
  rw [hz2, Matrix.sub_mulVec, Matrix.one_mulVec, hz1, sub_self]

end LSBA
