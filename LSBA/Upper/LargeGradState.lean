import LSBA.Transfer.StateChain

/-!
# Derivatives of the state update

The derivative of the graph update `C′` in the fresh block (the formula used for `dC_i` in Section
11.3
[lg:sec:drift-to-growth]), and smoothness of `m_k`, `f_k` and the increment `c` along the state
update; used
for the gradient bounds in the proof of Lemma 11.2 [uvg:lem:drifts].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- A real-linear map out of a finite-dimensional space is smooth. -/
private theorem lgs_contDiff_linear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {n : WithTop ℕ∞} (ℓ : F →ₗ[ℝ] E) : ContDiff ℝ n ℓ :=
  (LinearMap.toContinuousLinearMap ℓ).contDiff

/-- The entry `M ↦ M i j` is smooth. -/
private theorem lgs_contDiff_entry (W : ℕ) {n : WithTop ℕ∞} (i j : Fin W) :
    ContDiff ℝ n (fun M : Matrix (Fin W) (Fin W) ℂ => M i j) :=
  lgs_contDiff_linear (Matrix.entryLinearMap ℝ ℂ i j)

/-- `x ↦ (P x)ᴴ` is smooth when `P` is. -/
private theorem lgs_contDiff_conjTranspose (W : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : WithTop ℕ∞} {P : E → Matrix (Fin W) (Fin W) ℂ}
    (hP : ContDiff ℝ n P) : ContDiff ℝ n (fun x => (P x)ᴴ) := by
  have h : ContDiff ℝ n (fun M : Matrix (Fin W) (Fin W) ℂ => Mᴴ) :=
    lgs_contDiff_linear
      ({ toFun := fun M => Mᴴ
         map_add' := fun M N => Matrix.conjTranspose_add M N
         map_smul' := fun r M => by simp [Matrix.conjTranspose_smul] } :
        Matrix (Fin W) (Fin W) ℂ →ₗ[ℝ] Matrix (Fin W) (Fin W) ℂ)
  exact h.comp hP

/-- `x ↦ Tr (P x)` is smooth when `P` is. -/
private theorem lgs_contDiff_trace (W : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : WithTop ℕ∞} {P : E → Matrix (Fin W) (Fin W) ℂ}
    (hP : ContDiff ℝ n P) : ContDiff ℝ n (fun x => (P x).trace) :=
  (lgs_contDiff_linear (Matrix.traceLinearMap (Fin W) ℝ ℂ)).comp hP

/-- `x ↦ P x (u x)` is smooth when `P` and `u` are. -/
private theorem lgs_contDiff_toEuclideanLin (W : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : WithTop ℕ∞} {P : E → Matrix (Fin W) (Fin W) ℂ}
    {u : E → EuclideanSpace ℂ (Fin W)} (hP : ContDiff ℝ n P) (hu : ContDiff ℝ n u) :
    ContDiff ℝ n (fun x => Matrix.toEuclideanLin (P x) (u x)) := by
  refine (contDiff_piLp (𝕜 := ℝ) 2).2 fun i => ?_
  have h : ∀ x, Matrix.toEuclideanLin (P x) (u x) i = ∑ j, P x i j * u x j := fun x => by
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  simp only [h]
  exact ContDiff.sum fun j _ => (((lgs_contDiff_entry W i j).comp hP).mul
    (((contDiff_piLp (𝕜 := ℝ) 2).1 hu) j))

/-- `x ↦ (P x)⁻¹` is smooth when `P` is smooth with invertible values. -/
private theorem lgs_contDiff_inv (W : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : WithTop ℕ∞} {P : E → Matrix (Fin W) (Fin W) ℂ}
    (hP : ContDiff ℝ n P) (hu : ∀ x, IsUnit (P x)) : ContDiff ℝ n (fun x => (P x)⁻¹) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨u, hu'⟩ := hu x
  have h1 : ContDiffAt ℝ n Ring.inverse (P x) := by
    rw [← hu']
    exact (contDiffAt_ringInverse ℂ u).restrict_scalars ℝ
  have := h1.comp x hP.contDiffAt
  simpa [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using this

/-- The fresh block `ω ↦ gueBlock W 1 ω 0` is real-linear in the coordinates `ω`, hence
smooth. -/
private theorem lgs_contDiff_gueBlock (W : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun ω : Ω W 1 => gueBlock W 1 ω 0) := by
  refine lgs_contDiff_linear
    ({ toFun := fun ω : Ω W 1 => gueBlock W 1 ω 0
       map_add' := fun ω ω' => by
         ext α β
         simp only [gueBlock, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
         split_ifs <;> push_cast <;> ring
       map_smul' := fun r ω => by
         ext α β
         simp only [gueBlock, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply, RingHom.id_apply]
         split_ifs <;> simp <;> ring } :
      Ω W 1 →ₗ[ℝ] Matrix (Fin W) (Fin W) ℂ)

/-- A unitary matrix has inverse `Uᴴ`. -/
private theorem lgs_inv_eq_conjTranspose {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ) : U⁻¹ = Uᴴ := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff.mp hU

/-- Integer powers of a smooth unitary-valued matrix function are smooth. -/
private theorem lgs_contDiff_zpow (W : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : WithTop ℕ∞} {P : E → Matrix (Fin W) (Fin W) ℂ}
    (hP : ContDiff ℝ n P) (hU : ∀ x, P x ∈ Matrix.unitaryGroup (Fin W) ℂ) (k : ℤ) :
    ContDiff ℝ n (fun x => (P x) ^ k) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp only [zpow_natCast]
    exact hP.pow m
  · have h : ∀ x, P x ^ (-(m : ℤ)) = ((P x) ^ m)ᴴ := fun x => by
      rw [Matrix.zpow_neg (Matrix.isUnit_det_of_right_inverse
        (Matrix.mem_unitaryGroup_iff.mp (hU x))), zpow_natCast,
        lgs_inv_eq_conjTranspose (pow_mem (hU x) m)]
    simp only [h]
    exact lgs_contDiff_conjTranspose W (hP.pow m)

/-- The matrix `C'` of (11.3) [lg:eq:matrix-update] and the direction `F(C, V)^{-*} v` of (11.7)
[lg:eq:update] are smooth in the fresh block. -/
private theorem lgs_contDiff_data (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun ω : Ω W 1 => stepC g E X.1 (gueBlock W 1 ω 0)) ∧
    ContDiff ℝ n (fun ω : Ω W 1 => stepVec g E X (gueBlock W 1 ω 0)) := by
  have hV := lgs_contDiff_gueBlock (n := n) W
  have hF : ContDiff ℝ n (fun ω : Ω W 1 => stepF g E X.1 (gueBlock W 1 ω 0)) := by
    unfold stepF
    exact contDiff_const.sub ((hV.mul contDiff_const).const_smul _)
  have hFi : ContDiff ℝ n (fun ω : Ω W 1 => (stepF g E X.1 (gueBlock W 1 ω 0))⁻¹) :=
    lgs_contDiff_inv W hF fun ω => isUnit_stepF g E hX.1 (gueBlock_isHermitian W 1 ω 0)
  refine ⟨?_, ?_⟩
  · unfold stepC
    exact (((contDiff_const.add ((hV.mul contDiff_const).const_smul _)).mul hFi)).const_smul _
  · unfold stepVec
    exact lgs_contDiff_toEuclideanLin W (lgs_contDiff_conjTranspose W hFi) contDiff_const

/-- The direction `F(C, V)^{-*} v` of (11.7) [lg:eq:update] is nonzero for a state. -/
private theorem lgs_stepVec_ne_zero (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    (ω : Ω W 1) : stepVec g E X (gueBlock W 1 ω 0) ≠ 0 := by
  intro h
  have h1 := (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)).2
  change ‖(stepPhase E * ((‖stepVec g E X (gueBlock W 1 ω 0)‖⁻¹ : ℝ) : ℂ)) •
    stepVec g E X (gueBlock W 1 ω 0)‖ = 1 at h1
  rw [h] at h1
  simp at h1

/-- The norm `‖F(C, V)^{-*} v‖` of (11.7) [lg:eq:update] is smooth in the fresh block. -/
private theorem lgs_contDiff_norm (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun ω : Ω W 1 => ‖stepVec g E X (gueBlock W 1 ω 0)‖) := by
  rw [contDiff_iff_contDiffAt]
  intro ω
  exact ContDiffAt.norm ℂ (lgs_contDiff_data g E hX).2.contDiffAt (lgs_stepVec_ne_zero g E hX ω)

/-- The updated state `(C', v')` of (11.7) [lg:eq:update] is smooth in the fresh block. -/
private theorem lgs_contDiff_state (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun ω : Ω W 1 => (stepState g E X (gueBlock W 1 ω 0)).1) ∧
    ContDiff ℝ n (fun ω : Ω W 1 => (stepState g E X (gueBlock W 1 ω 0)).2) := by
  refine ⟨(lgs_contDiff_data g E hX).1, ?_⟩
  have hn := lgs_contDiff_norm (n := n) g E hX
  have hs : ContDiff ℝ n (fun ω : Ω W 1 =>
      stepPhase E * (((‖stepVec g E X (gueBlock W 1 ω 0)‖⁻¹ : ℝ)) : ℂ)) :=
    contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (hn.inv fun ω => by
        simpa using lgs_stepVec_ne_zero g E hX ω))
  exact hs.smul (lgs_contDiff_data g E hX).2

/-- `dC' = i h_θ g⁻¹ (C' - e^{-2iθ} I) dV (I + C) F(C, V)⁻¹` (proof of Lemma 11.2
[uvg:lem:drifts]; (11.15) [lg:eq:gradients]). -/
theorem hasDerivAt_stepC (g E : ℝ) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian)
    (H : Matrix (Fin W) (Fin W) ℂ) :
    HasDerivAt (fun s : ℝ => stepC g E C (V + (s : ℂ) • H))
      ((Complex.I * ((normalH E / g : ℝ) : ℂ)) •
        ((stepC g E C V - normalPhase E • (1 : Matrix (Fin W) (Fin W) ℂ)) * H * (1 + C) *
          (stepF g E C V)⁻¹)) 0 := by
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
  have hinv : HasDerivAt (fun s : ℝ => (stepF g E C (V + (s : ℂ) • H))⁻¹)
      ((stepF g E C V)⁻¹ * (t • (H * (1 + C))) * (stepF g E C V)⁻¹) 0 := by
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
  have hA : HasDerivAt (fun s : ℝ => C + t • ((V + (s : ℂ) • H) * (1 + C)))
      (t • (H * (1 + C))) 0 :=
    ((hG.mul_const (1 + C)).const_smul t).const_add C
  have hP := (hA.mul hinv).const_smul (-normalPhase E)
  refine hP.congr_deriv ?_
  simp only [Complex.ofReal_zero, zero_smul, add_zero]
  have e1 : stepC g E C V =
      -normalPhase E • ((C + t • (V * (1 + C))) * (stepF g E C V)⁻¹) := rfl
  rw [e1]
  generalize (stepF g E C V)⁻¹ = Fi
  generalize C + t • (V * (1 + C)) = X
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, smul_add,
    smul_sub, smul_smul, Matrix.mul_assoc, Matrix.one_mul]
  module

/-- `ω ↦ m_k(C')` is `C¹` in the fresh block (proof of Lemma 11.2 [uvg:lem:drifts]). -/
theorem contDiff_obsM_stepState (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) (k : ℤ) :
    ContDiff ℝ 1 (fun ω : Ω W 1 => obsM k (stepState g E X (gueBlock W 1 ω 0))) := by
  unfold obsM
  exact contDiff_const.mul (lgs_contDiff_trace W (lgs_contDiff_zpow W (lgs_contDiff_state g E hX).1
    (fun ω => isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0) |>.1) k))

/-- `ω ↦ f_k(C', v')` is `C¹` in the fresh block (proof of Lemma 11.2 [uvg:lem:drifts]). -/
theorem contDiff_obsF_stepState (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) (k : ℤ) :
    ContDiff ℝ 1 (fun ω : Ω W 1 => obsF k (stepState g E X (gueBlock W 1 ω 0))) := by
  unfold obsF vecForm
  exact (lgs_contDiff_state g E hX).2.inner ℂ (lgs_contDiff_toEuclideanLin W
    (lgs_contDiff_zpow W (lgs_contDiff_state g E hX).1
      (fun ω => isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0) |>.1) k)
    (lgs_contDiff_state g E hX).2)

/-- `ω ↦ c(X, V)` is `C¹` in the fresh block (proof of Lemma 11.2 [uvg:lem:drifts]). -/
theorem contDiff_stepInc (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X) :
    ContDiff ℝ 1 (fun ω : Ω W 1 => stepInc g E X (gueBlock W 1 ω 0)) := by
  unfold stepInc
  exact ((lgs_contDiff_norm g E hX).log fun ω => by
    simpa using lgs_stepVec_ne_zero g E hX ω).neg

end LSBA
