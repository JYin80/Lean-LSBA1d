import LSBA.Upper.Operator

/-!
# Simultaneous unitary invariance

Simultaneous unitary invariance (8.25) [up:eq:invariant-function]: a common conjugation of the
inputs conjugates the batch by `diag(Ṽ, Ṽ)`, so `P_{1/2}` preserves (8.25)
[up:eq:invariant-function] for every invariant
function, and every `P_{1/2}^k 1` is invariant (Section 8.3 [sec:upper-inputs]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Simultaneous unitary invariance (8.25) [up:eq:invariant-function]:
`h(diag(Ṽ, Ṽ) U, diag(Ṽ, Ṽ) Y) = h(U, Y)` for every unitary `Ṽ`. -/
def IsSimulInvariant {W : ℕ} (h : IsoFlag W → ℝ) : Prop :=
  ∀ V ∈ Matrix.unitaryGroup (Fin W) ℂ, ∀ x : IsoFlag W,
    h (flagAct ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) x) = h x

private theorem opinv_gram {W : ℕ} (V : Matrix.unitaryGroup (Fin W) ℂ) :
    (V : Matrix (Fin W) (Fin W) ℂ) * (V : Matrix (Fin W) (Fin W) ℂ)ᴴ = 1 ∧
      (V : Matrix (Fin W) (Fin W) ℂ)ᴴ * (V : Matrix (Fin W) (Fin W) ℂ) = 1 := by
  have h1 := Matrix.mem_unitaryGroup_iff.mp V.2
  have h2 := Matrix.mem_unitaryGroup_iff'.mp V.2
  rw [Matrix.star_eq_conjTranspose] at h1 h2
  exact ⟨h1, h2⟩

private theorem opinv_kron_mul {W : ℕ} {V : Matrix (Fin W) (Fin W) ℂ} (h1 : V * Vᴴ = 1) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)ᴴ = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
    Matrix.mul_one, h1, Matrix.one_kronecker_one]

private theorem opinv_kron_mul' {W : ℕ} {V : Matrix (Fin W) (Fin W) ℂ} (h1 : Vᴴ * V = 1) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)ᴴ * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
    Matrix.mul_one, h1, Matrix.one_kronecker_one]

private theorem opinv_transferMat {W : ℕ} (g : ℝ) (z : ℂ) {V : Matrix (Fin W) (Fin W) ℂ}
    (h1 : V * Vᴴ = 1) (B : Matrix (Fin W) (Fin W) ℂ) :
    transferMat g z (V * B * Vᴴ) =
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) * transferMat g z B *
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)ᴴ := by
  unfold transferMat transferFree
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, h1]

private theorem opinv_transferProd {W : ℕ} (g : ℝ) (z : ℂ) {V : Matrix (Fin W) (Fin W) ℂ}
    (h1 : V * Vᴴ = 1) (h2 : Vᴴ * V = 1) (B : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) :
    transferProd g z (fun k => V * B k * Vᴴ) n =
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) * transferProd g z B n *
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)ᴴ := by
  have k1 := opinv_kron_mul h1
  have k2 := opinv_kron_mul' h2
  induction n with
  | zero =>
    simp only [transferProd, Matrix.mul_one]
    exact k1.symm
  | succ n ih =>
    change transferMat g z (V * B n * Vᴴ) * transferProd g z (fun k => V * B k * Vᴴ) n =
      _ * (transferMat g z (B n) * transferProd g z B n) * _
    rw [ih, opinv_transferMat g z h1]
    calc _ = ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) * transferMat g z (B n) *
          (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)ᴴ * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)) *
          transferProd g z B n * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [k2, Matrix.mul_one]; simp only [Matrix.mul_assoc]

private theorem opinv_commute_freeConj {W : ℕ} (V : Matrix (Fin W) (Fin W) ℂ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) * freeConj W 0 =
      freeConj W 0 * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) := by
  unfold freeConj
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_one, Matrix.one_mul]

/-- Common conjugation of the inputs conjugates the batch by `diag(Ṽ, Ṽ)` (Section 8.3
[sec:upper-inputs]). -/
theorem batchMat_conjMap (W : ℕ) (g E : ℝ) (n : ℕ) (V : Matrix.unitaryGroup (Fin W) ℂ)
    (ω : Ω W n) :
    batchMat W g E n (conjMap W n V ω) =
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (V : Matrix (Fin W) (Fin W) ℂ)) * batchMat W g E n ω *
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (V : Matrix (Fin W) (Fin W) ℂ))ᴴ := by
  obtain ⟨h1, h2⟩ := opinv_gram V
  have hB : (fun k => if h : k < n then gueBlock W n (conjMap W n V ω) ⟨k, h⟩ else 0) =
      fun k => (V : Matrix (Fin W) (Fin W) ℂ) *
        (if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) * (V : Matrix (Fin W) (Fin W) ℂ)ᴴ := by
    funext k
    by_cases h : k < n
    · simp only [h, dite_true]
      rw [gueBlock_conjMap, Matrix.star_eq_conjTranspose]
    · simp only [h, dite_false, Matrix.mul_zero, Matrix.zero_mul]
  unfold batchMat
  rw [hB, opinv_transferProd _ _ h1 h2]
  have hc := opinv_commute_freeConj (W := W) (V : Matrix (Fin W) (Fin W) ℂ)ᴴ
  have hk : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (V : Matrix (Fin W) (Fin W) ℂ))ᴴ =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (V : Matrix (Fin W) (Fin W) ℂ)ᴴ := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  have hc2 : (freeConj W 0)ᴴ * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (V : Matrix (Fin W) (Fin W) ℂ)) =
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (V : Matrix (Fin W) (Fin W) ℂ)) * (freeConj W 0)ᴴ := by
    have := congrArg Matrix.conjTranspose hc
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose] at this
    exact this
  rw [hk]
  calc _ = ((freeConj W 0)ᴴ * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (V : Matrix (Fin W) (Fin W) ℂ))) *
        transferProd g ((max 1 g * E / g : ℝ) : ℂ)
          (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) n *
        (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (V : Matrix (Fin W) (Fin W) ℂ)ᴴ) * freeConj W 0) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hc2, hc]
        simp only [Matrix.mul_assoc]

private theorem opinv_isoJ {W : ℕ} {V : Matrix (Fin W) (Fin W) ℂ} (h2 : Vᴴ * V = 1) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)ᴴ * isoJ W * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) =
      isoJ W := by
  unfold isoJ
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, h2]

private theorem opinv_mem_unitaryGroup {W : ℕ} {V : Matrix (Fin W) (Fin W) ℂ}
    (h1 : V * Vᴴ = 1) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) ∈ Matrix.unitaryGroup (Fin 2 × Fin W) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  exact opinv_kron_mul h1

private theorem opinv_isUnit_of_isoGroup {W : ℕ}
    {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hT : T ∈ isoGroup W) : IsUnit T := by
  rw [Matrix.isUnit_iff_isUnit_det, hT.2]
  exact isUnit_one

/-- The conjugated batch acts on the conjugated flag as the original batch, and has the same
cocycle. -/
private theorem opinv_pointwise (W : ℕ) (g E : ℝ) (n : ℕ) (V : Matrix.unitaryGroup (Fin W) ℂ)
    (ω : Ω W n) (x : IsoFlag W) :
    volCocycle (batchMat W g E n (conjMap W n V ω))
        (flagAct ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (V : Matrix (Fin W) (Fin W) ℂ)) x) =
      volCocycle (batchMat W g E n ω) x ∧
    flagAct (batchMat W g E n (conjMap W n V ω))
        (flagAct ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (V : Matrix (Fin W) (Fin W) ℂ)) x) =
      flagAct ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (V : Matrix (Fin W) (Fin W) ℂ))
        (flagAct (batchMat W g E n ω) x) := by
  obtain ⟨h1, h2⟩ := opinv_gram V
  have k1 := opinv_kron_mul h1
  have k2 := opinv_kron_mul' h2
  set K := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (V : Matrix (Fin W) (Fin W) ℂ) with hK
  have hF' : batchMat W g E n (conjMap W n V ω) = K * batchMat W g E n ω * Kᴴ :=
    batchMat_conjMap W g E n V ω
  have hKF : batchMat W g E n (conjMap W n V ω) * K = K * batchMat W g E n ω := by
    rw [hF']
    calc _ = K * batchMat W g E n ω * (Kᴴ * K) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [k2, Matrix.mul_one]
  have hKJ := opinv_isoJ h2
  have hKU : IsUnit K := (Matrix.isUnit_iff_isUnit_det K).mpr (Matrix.isUnit_det_of_right_inverse k1)
  have hFg := batchMat_mem_isoGroup W g E n ω
  have hF'g := batchMat_mem_isoGroup W g E n (conjMap W n V ω)
  have hK0 := volCocycle_of_mem_unitaryGroup (opinv_mem_unitaryGroup h1) x
  have hK0' := volCocycle_of_mem_unitaryGroup (opinv_mem_unitaryGroup h1)
    (flagAct (batchMat W g E n ω) x)
  constructor
  · have e1 := volCocycle_mul hKJ (opinv_isUnit_of_isoGroup hF'g) x
    have e2 := volCocycle_mul hFg.1 hKU x
    rw [hKF] at e1
    rw [e2, hK0] at e1
    rw [hK0'] at e1
    linarith
  · have e1 := flagAct_mul hKJ hF'g.1 x
    have e2 := flagAct_mul hFg.1 hKJ x
    rw [hKF] at e1
    rw [e2] at e1
    exact e1.symm

private theorem opinv_conj_cancel {W : ℕ} {V : Matrix (Fin W) (Fin W) ℂ}
    (h2 : Vᴴ * V = 1) (B : Matrix (Fin W) (Fin W) ℂ) : Vᴴ * (V * B * Vᴴ) * V = B := by
  calc Vᴴ * (V * B * Vᴴ) * V = (Vᴴ * V) * B * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
    _ = B := by rw [h2, Matrix.one_mul, Matrix.mul_one]

private theorem opinv_conjMap_injective (W n : ℕ) (V : Matrix.unitaryGroup (Fin W) ℂ) :
    Function.Injective (conjMap W n V) := by
  obtain ⟨h1, h2⟩ := opinv_gram V
  intro ω ω' h
  have hb : gueBlock W n ω = gueBlock W n ω' := by
    funext a
    have := congrArg (fun η => gueBlock W n η a) h
    simp only [gueBlock_conjMap, Matrix.star_eq_conjTranspose] at this
    rw [← opinv_conj_cancel h2 (gueBlock W n ω a), this, opinv_conj_cancel h2]
  rw [← gueCoord_gueBlock W n ω, ← gueCoord_gueBlock W n ω', hb]

/-- `P_{1/2}` preserves (8.25) [up:eq:invariant-function], for every invariant `h`. -/
theorem halfOp_isSimulInvariant {W : ℕ} (g E : ℝ) (q : ℕ) {h : IsoFlag W → ℝ}
    (hinv : IsSimulInvariant h) : IsSimulInvariant (halfOp W g E q h) := by
  intro V hV x
  set V' : Matrix.unitaryGroup (Fin W) ℂ := ⟨V, hV⟩ with hV'
  have hmp := measurePreserving_conjMap W q V'
  have hemb : MeasurableEmbedding (conjMap W q V') :=
    hmp.measurable.measurableEmbedding (opinv_conjMap_injective W q V')
  unfold halfOp
  rw [← hmp.integral_comp hemb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  obtain ⟨hc, ha⟩ := opinv_pointwise W g E q V' ω x
  simp only
  rw [hc, ha]
  exact congrArg _ (hinv V hV _)

/-- Every `P_{1/2}^k 1` satisfies (8.25) [up:eq:invariant-function]. -/
theorem iterate_halfOp_one_isSimulInvariant (W : ℕ) (g E : ℝ) (q k : ℕ) :
    IsSimulInvariant ((halfOp W g E q)^[k] fun _ => 1) := by
  induction k with
  | zero => exact fun V _ x => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact halfOp_isSimulInvariant g E q ih

end LSBA
