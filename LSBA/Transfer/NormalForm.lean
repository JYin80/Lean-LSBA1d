import LSBA.Transfer.Basic
import LSBA.Transfer.Frames

/-!
# Normal coordinates and the one-step update

Normal coordinates of the transfer matrix at energy `E`, `|E| < 2`: the angle quantities `h_θ`,
`e^{−2iθ}` and `−ie^{iθ}` of (11.1) [lg:eq:normal], written through `ϑ = freeAngle E`; the
normal form `S_E⁻¹ T S_E` (Definition 7.1 [def:transfer-matrices]); and the graph update (11.3)
[lg:eq:matrix-update] `C′ = −e^{−2iθ}[C + i h_θ g⁻¹ V(I + C)]F⁻¹` with `F = I − i h_θ g⁻¹ V(I + C)`:
`F` is invertible and `C′` is unitary for unitary `C` and Hermitian `V`, the exact inverse of `F`
and its finite expansion, and `‖F‖, ‖F⁻¹‖ ≤ 1 + 2h_θ‖V‖/g` (the constant of (11.13)
[uvg:eq:global]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `h_θ = (2 cos θ)⁻¹ = (2 sin ϑ)⁻¹` of (11.1) [lg:eq:normal], where `θ = π/2 - ϑ` and
`ϑ = arccos(E/2)` is the angle of Definition 7.1 [def:transfer-matrices]. -/
def normalH (E : ℝ) : ℝ := (2 * Real.sin (freeAngle E))⁻¹

/-- `e^{-2iθ} = -e^{2iϑ}` with `θ` of (11.1) [lg:eq:normal]. -/
def normalPhase (E : ℝ) : ℂ := -Complex.exp (2 * (freeAngle E * Complex.I))

/-- `-i e^{iθ} = e^{-iϑ}`, the scalar factor in (11.3) [lg:eq:matrix-update]. -/
def stepPhase (E : ℝ) : ℂ := Complex.exp (-(freeAngle E * Complex.I))

/-- `F(C, V) = I - i h_θ g⁻¹ V (I + C)` of (11.3) [lg:eq:matrix-update]. -/
def stepF (g E : ℝ) {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  1 - (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))

/-- The graph update `C' = -e^{-2iθ} [C + i h_θ g⁻¹ V (I + C)] F(C, V)⁻¹` of (11.3)
[lg:eq:matrix-update]. -/
def stepC (g E : ℝ) {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  -normalPhase E • ((C + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) *
    (stepF g E C V)⁻¹)

private theorem nf_normalH_nonneg (E : ℝ) : 0 ≤ normalH E := by
  unfold normalH freeAngle
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg (E / 2))
    (Real.arccos_le_pi (E / 2))
  positivity

private theorem nf_star_I_mul (t : ℝ) :
    star (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ)) := by
  simp

private theorem nf_star_normalPhase_mul (E : ℝ) :
    star (normalPhase E) * normalPhase E = 1 := by
  unfold normalPhase
  rw [star_neg, neg_mul_neg, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
    show (2 : ℂ) * (↑(freeAngle E) * -Complex.I) + 2 * (↑(freeAngle E) * Complex.I) = 0 by ring,
    Complex.exp_zero]

private theorem nf_norm_normalPhase (E : ℝ) : ‖normalPhase E‖ = 1 := by
  unfold normalPhase
  rw [norm_neg, show 2 * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem nf_mem_unitary_iff {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} :
    U ∈ Matrix.unitaryGroup (Fin W) ℂ ↔ Uᴴ * U = 1 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]

private theorem nf_conjTranspose_stepF (g E : ℝ) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hV : V.IsHermitian) :
    (stepF g E C V)ᴴ = 1 + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • ((1 + C)ᴴ * V) := by
  unfold stepF
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, hV.eq, nf_star_I_mul, neg_smul, sub_neg_eq_add]

/-- `A* A = F* F` for `A = C + i h g⁻¹ V (I + C)`, `F = I - i h g⁻¹ V (I + C)`. -/
private theorem nf_gram (g E : ℝ) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) :
    (C + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C)))ᴴ *
        (C + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) =
      (stepF g E C V)ᴴ * stepF g E C V := by
  have hC' := nf_mem_unitary_iff.mp hC
  set c : ℂ := Complex.I * ((normalH E / g : ℝ) : ℂ) with hc
  have hFA : C + c • (V * (1 + C)) = (1 + C) - stepF g E C V := by
    unfold stepF; abel
  have h1 : (1 + C)ᴴ * (1 + C) = (1 + C)ᴴ + (1 + C) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hC']
    abel
  have h2 : (1 + C)ᴴ * stepF g E C V + (stepF g E C V)ᴴ * (1 + C) = (1 + C)ᴴ + (1 + C) := by
    rw [nf_conjTranspose_stepF g E hV]
    unfold stepF
    generalize 1 + C = U
    simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [hFA, Matrix.conjTranspose_sub]
  calc ((1 + C)ᴴ - (stepF g E C V)ᴴ) * ((1 + C) - stepF g E C V)
      = (1 + C)ᴴ * (1 + C) - ((1 + C)ᴴ * stepF g E C V + (stepF g E C V)ᴴ * (1 + C)) +
          (stepF g E C V)ᴴ * stepF g E C V := by noncomm_ring
    _ = (stepF g E C V)ᴴ * stepF g E C V := by rw [h1, h2, sub_self, zero_add]

open scoped ComplexOrder in
private theorem nf_isUnit_stepF (g E : ℝ) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) : IsUnit (stepF g E C V) := by
  set c : ℂ := Complex.I * ((normalH E / g : ℝ) : ℂ) with hc
  set F := stepF g E C V with hF
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have hker : ∀ x : Fin W → ℂ, F *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hA : (C + c • (V * (1 + C))) *ᵥ x = 0 := by
      have h0 : star ((C + c • (V * (1 + C))) *ᵥ x) ⬝ᵥ ((C + c • (V * (1 + C))) *ᵥ x) = 0 := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
          nf_gram g E hC hV, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, dotProduct_zero]
      exact dotProduct_star_self_eq_zero.mp h0
    have hU : (1 + C) *ᵥ x = 0 := by
      have : (1 + C) = (C + c • (V * (1 + C))) + F := by rw [hF]; unfold stepF; abel
      rw [this, Matrix.add_mulVec, hA, hx, add_zero]
    calc x = F *ᵥ x + (c • (V * (1 + C))) *ᵥ x := by
          rw [hF]; unfold stepF; rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
      _ = 0 := by
          rw [hx, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hU, Matrix.mulVec_zero, smul_zero,
            add_zero]
  intro x y hxy
  have : F *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hker _ this)

private theorem nf_sin_pos {E : ℝ} (hE : |E| < 2) : 0 < Real.sin (freeAngle E) := by
  have h := abs_lt.mp hE
  exact Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr (by linarith))
    (Real.arccos_lt_pi.mpr (by linarith))

private theorem nf_exp_neg_sub_exp (E : ℝ) :
    Complex.exp (-(freeAngle E * Complex.I)) - Complex.exp (freeAngle E * Complex.I) =
      -(2 * (Real.sin (freeAngle E) : ℂ)) * Complex.I := by
  rw [← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

set_option linter.flexible false in
private theorem nf_block_aux (a b h : ℂ) (hh : Complex.I * h * (b - a) = 1) :
    (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 1; a, b] =
      (Complex.I * h) • (!![1, 1; a, b] * Matrix.diagonal ![b, a] * !![1, 1; -1, -1]) := by
  have hD : (Matrix.diagonal ![b, a] : Matrix (Fin 2) (Fin 2) ℂ) = !![b, 0; 0, a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hD]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -hh
  · linear_combination -hh
  · right; ring
  · right; ring

private theorem nf_block {E : ℝ} (hE : |E| < 2) :
    (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
        !![1, 1; Complex.exp (freeAngle E * Complex.I), Complex.exp (-(freeAngle E * Complex.I))] =
      (Complex.I * ((normalH E : ℝ) : ℂ)) •
        (!![1, 1; Complex.exp (freeAngle E * Complex.I),
              Complex.exp (-(freeAngle E * Complex.I))] *
          Matrix.diagonal ![Complex.exp (-(freeAngle E * Complex.I)),
            Complex.exp (freeAngle E * Complex.I)] * !![1, 1; -1, -1]) := by
  have hd := nf_exp_neg_sub_exp E
  have hs : (Real.sin (freeAngle E) : ℂ) ≠ 0 := by exact_mod_cast (nf_sin_pos hE).ne'
  refine nf_block_aux _ _ _ ?_
  have hnh : ((normalH E : ℝ) : ℂ) = (2 * (Real.sin (freeAngle E) : ℂ))⁻¹ := by
    unfold normalH
    rw [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [hd, hnh]
  field_simp
  rw [Complex.I_sq, neg_neg]


private theorem nf_shear_eq {W : ℕ} {E : ℝ} (hE : |E| < 2) (V : Matrix (Fin W) (Fin W) ℂ) :
    (freeConj W E)⁻¹ * (!![1, 0; 0, 0] ⊗ₖ V) * freeConj W E =
      (Complex.I * ((normalH E : ℝ) : ℂ)) • (freeRot W E * (!![1, 1; -1, -1] ⊗ₖ V)) := by
  have hU := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_freeConj W hE)
  have key : (!![1, 0; 0, 0] ⊗ₖ V) * freeConj W E = freeConj W E *
      ((Complex.I * ((normalH E : ℝ) : ℂ)) • (freeRot W E * (!![1, 1; -1, -1] ⊗ₖ V))) := by
    unfold freeConj freeRot
    simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul]
    rw [← Matrix.mul_assoc, nf_block hE, Matrix.smul_kronecker, smul_comm]
  rw [Matrix.mul_assoc, key, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]

/-- The free normal form after (11.1) [lg:eq:normal]:
`S_E⁻¹ T_i S_E = R_E [I - i h_θ g⁻¹ (V V; -V -V)]`. -/
theorem inv_freeConj_mul_transferMat_mul_eq_freeRot_mul {W : ℕ} {E : ℝ} (hE : |E| < 2) (g : ℝ)
    (V : Matrix (Fin W) (Fin W) ℂ) :
    (freeConj W E)⁻¹ * transferMat g (E : ℂ) V * freeConj W E =
      freeRot W E * (1 - (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (!![1, 1; -1, -1] ⊗ₖ V)) := by
  have h0 := inv_freeConj_mul_transferMat_mul hE g 0 V
  have hz : ((E : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = (E : ℂ) := by simp
  rw [hz] at h0
  rw [h0, nf_shear_eq hE, Complex.ofReal_zero, zero_mul, zero_smul, add_zero, Matrix.mul_sub,
    Matrix.mul_one, Matrix.mul_smul, smul_smul]
  congr 2
  rw [Complex.ofReal_div]
  ring

/-- `F(C, V)` is invertible for unitary `C` and Hermitian `V` (11.3) [lg:eq:matrix-update]. -/
theorem isUnit_stepF (g E : ℝ) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) : IsUnit (stepF g E C V) := by
  exact nf_isUnit_stepF g E hC hV

/-- The graph update of (11.3) [lg:eq:matrix-update] keeps `C` unitary. -/
theorem stepC_mem_unitaryGroup (g E : ℝ) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) :
    stepC g E C V ∈ Matrix.unitaryGroup (Fin W) ℂ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_stepF g E hC hV)
  have hν : star (-normalPhase E) * (-normalPhase E) = 1 := by
    rw [star_neg, neg_mul_neg]; exact nf_star_normalPhase_mul E
  rw [nf_mem_unitary_iff]
  unfold stepC
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hν, one_smul]
  calc (stepF g E C V)⁻¹ᴴ *
        (C + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C)))ᴴ *
        ((C + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) * (stepF g E C V)⁻¹)
      = (stepF g E C V)⁻¹ᴴ * ((C + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C)))ᴴ *
        (C + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C)))) * (stepF g E C V)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = (stepF g E C V)⁻¹ᴴ * ((stepF g E C V)ᴴ * stepF g E C V) * (stepF g E C V)⁻¹ := by
        rw [nf_gram g E hC hV]
    _ = (stepF g E C V * (stepF g E C V)⁻¹)ᴴ * (stepF g E C V * (stepF g E C V)⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one, Matrix.mul_one]

private theorem nf_colStack_mul {W : ℕ} (X Y Z : Matrix (Fin W) (Fin W) ℂ) :
    colStack X Y * Z = colStack (X * Z) (Y * Z) := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack, Matrix.mul_apply]

private theorem nf_smul_colStack {W : ℕ} (c : ℂ) (X Y : Matrix (Fin W) (Fin W) ℂ) :
    c • colStack X Y = colStack (c • X) (c • Y) := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack]

private theorem nf_kron_colStack {W : ℕ} (V X Y : Matrix (Fin W) (Fin W) ℂ) :
    (!![1, 1; -1, -1] ⊗ₖ V) * colStack X Y = colStack (V * (X + Y)) (-(V * (X + Y))) := by
  ext ⟨i, α⟩ β
  fin_cases i
  · simp [colStack, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, mul_add, Finset.sum_add_distrib]
  · simp [colStack, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, mul_add, Finset.sum_add_distrib]
    abel

private theorem nf_freeRot_colStack {W : ℕ} (E : ℝ) (X Y : Matrix (Fin W) (Fin W) ℂ) :
    freeRot W E * colStack X Y =
      colStack (Complex.exp (-(freeAngle E * Complex.I)) • X)
        (Complex.exp (freeAngle E * Complex.I) • Y) := by
  ext ⟨i, α⟩ β
  fin_cases i <;>
    simp [colStack, freeRot, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Matrix.one_apply]

private theorem nf_colStack_sub {W : ℕ} (X Y X' Y' : Matrix (Fin W) (Fin W) ℂ) :
    colStack X Y - colStack X' Y' = colStack (X - X') (Y - Y') := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack]

/-- (11.3) [lg:eq:matrix-update]: `S_E⁻¹ T_i S_E (I; C) = -i e^{iθ} (I; C') F(C, V)`. -/
theorem inv_freeConj_mul_transferMat_mul_colStack {W : ℕ} {E : ℝ} (hE : |E| < 2) (g : ℝ)
    {C V : Matrix (Fin W) (Fin W) ℂ} (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ)
    (hV : V.IsHermitian) :
    (freeConj W E)⁻¹ * transferMat g (E : ℂ) V * freeConj W E * colStack 1 C =
      stepPhase E • (colStack 1 (stepC g E C V) * stepF g E C V) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_stepF g E hC hV)
  have hCF : stepC g E C V * stepF g E C V =
      (-normalPhase E) • (C + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) := by
    unfold stepC
    rw [Matrix.smul_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  have hphase : stepPhase E * (-normalPhase E) = Complex.exp (freeAngle E * Complex.I) := by
    unfold stepPhase normalPhase
    rw [neg_neg, ← Complex.exp_add]
    congr 1
    ring
  have hmid : (1 - (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (!![1, 1; -1, -1] ⊗ₖ V)) *
      colStack 1 C = colStack (stepF g E C V)
        (C + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, nf_kron_colStack, nf_smul_colStack,
      nf_colStack_sub, smul_neg, sub_neg_eq_add]
    rfl
  rw [inv_freeConj_mul_transferMat_mul_eq_freeRot_mul hE g V, Matrix.mul_assoc, hmid,
    nf_freeRot_colStack, nf_colStack_mul, nf_smul_colStack, Matrix.one_mul, hCF, smul_smul,
    hphase]
  rfl

/-- The exact inverse `F(C, V)⁻¹ = I + i h_θ g⁻¹ V (I - e^{2iθ} C')` (Section 11.2
[sec:uniform-large-g], proof of (11.12) [lg:eq:c2]). -/
theorem inv_stepF (g E : ℝ) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) :
    (stepF g E C V)⁻¹ = 1 + (Complex.I * ((normalH E / g : ℝ) : ℂ)) •
      (V * (1 - star (normalPhase E) • stepC g E C V)) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_stepF g E hC hV)
  have hFinv : (stepF g E C V)⁻¹ * stepF g E C V = 1 := Matrix.nonsing_inv_mul _ hdet
  have hCF : star (normalPhase E) • stepC g E C V = -((C +
      (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) * (stepF g E C V)⁻¹) := by
    unfold stepC
    rw [smul_smul, mul_neg, nf_star_normalPhase_mul, neg_smul, one_smul]
  rw [hCF]
  refine Matrix.inv_eq_left_inv ?_
  calc (1 + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 - -((C +
        (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) * (stepF g E C V)⁻¹)))) *
        stepF g E C V
      = stepF g E C V + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (stepF g E C V +
          (C + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) *
            ((stepF g E C V)⁻¹ * stepF g E C V))) := by
        simp only [sub_neg_eq_add, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
          Matrix.mul_add, Matrix.mul_assoc]
    _ = 1 := by
        rw [hFinv, Matrix.mul_one]
        unfold stepF
        generalize Complex.I * ((normalH E / g : ℝ) : ℂ) = c
        simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
        abel_nf

/-- Finite Neumann expansion of `F(C, V)⁻¹` with exact remainder: with
`X = i h_θ g⁻¹ V (I + C)`, `F⁻¹ = Σ_{k<N} X^k + X^N F⁻¹`. -/
theorem inv_stepF_eq_sum_add (g E : ℝ) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) (N : ℕ) :
    (stepF g E C V)⁻¹ =
      ∑ k ∈ Finset.range N, ((Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) ^ k +
        ((Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) ^ N * (stepF g E C V)⁻¹ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_stepF g E hC hV)
  have hFinv : (stepF g E C V)⁻¹ * stepF g E C V = 1 := Matrix.nonsing_inv_mul _ hdet
  have hFinv' : stepF g E C V * (stepF g E C V)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  generalize hX : (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C)) = X
  have hF : stepF g E C V = 1 - X := by unfold stepF; rw [hX]
  have hcomm : X * (stepF g E C V)⁻¹ = (stepF g E C V)⁻¹ * X := by
    have hXF : X * stepF g E C V = stepF g E C V * X := by
      rw [hF, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    calc X * (stepF g E C V)⁻¹
        = ((stepF g E C V)⁻¹ * stepF g E C V) * X * (stepF g E C V)⁻¹ := by
          rw [hFinv, Matrix.one_mul]
      _ = (stepF g E C V)⁻¹ * (stepF g E C V * X) * (stepF g E C V)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (stepF g E C V)⁻¹ * (X * stepF g E C V) * (stepF g E C V)⁻¹ := by rw [hXF]
      _ = (stepF g E C V)⁻¹ * X * (stepF g E C V * (stepF g E C V)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = (stepF g E C V)⁻¹ * X := by rw [hFinv', Matrix.mul_one]
  have hgeom : stepF g E C V * ∑ k ∈ Finset.range N, X ^ k = 1 - X ^ N := by
    rw [hF]
    exact mul_neg_geom_sum X N
  have hsum : ∑ k ∈ Finset.range N, X ^ k = (stepF g E C V)⁻¹ - X ^ N * (stepF g E C V)⁻¹ := by
    calc ∑ k ∈ Finset.range N, X ^ k
        = ((stepF g E C V)⁻¹ * stepF g E C V) * ∑ k ∈ Finset.range N, X ^ k := by
          rw [hFinv, Matrix.one_mul]
      _ = (stepF g E C V)⁻¹ * (1 - X ^ N) := by rw [Matrix.mul_assoc, hgeom]
      _ = (stepF g E C V)⁻¹ - X ^ N * (stepF g E C V)⁻¹ := by
          rw [Matrix.mul_sub, Matrix.mul_one, (Commute.pow_left (show Commute X _ from hcomm) N).eq]
  rw [hsum]
  abel

private theorem nf_norm_one_add_le {W : ℕ} [Nontrivial (Matrix (Fin W) (Fin W) ℂ)] (c : ℂ)
    (V Q : Matrix (Fin W) (Fin W) ℂ) {q : ℝ} (hq : ‖Q‖ ≤ q) :
    ‖1 + c • (V * Q)‖ ≤ 1 + ‖c‖ * (‖V‖ * q) := by
  calc ‖1 + c • (V * Q)‖ ≤ ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ + ‖c • (V * Q)‖ := norm_add_le _ _
    _ ≤ 1 + ‖c‖ * (‖V‖ * q) := by
        rw [norm_one, norm_smul]
        gcongr
        exact (norm_mul_le _ _).trans (by gcongr)

/-- The first half of (11.13) [uvg:eq:global] with the constant `2 h_θ`:
`‖F‖, ‖F⁻¹‖ ≤ 1 + 2 h_θ g⁻¹ ‖V‖`. -/
theorem norm_stepF_le {g : ℝ} (hg : 0 < g) (E : ℝ) {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) :
    ‖stepF g E C V‖ ≤ 1 + 2 * normalH E * ‖V‖ / g ∧
      ‖(stepF g E C V)⁻¹‖ ≤ 1 + 2 * normalH E * ‖V‖ / g := by
  have hh := nf_normalH_nonneg E
  have ht : 0 ≤ normalH E / g := div_nonneg hh hg.le
  have hrhs : 1 + 2 * normalH E * ‖V‖ / g = 1 + (normalH E / g) * (‖V‖ * 2) := by ring
  rcases subsingleton_or_nontrivial (Matrix (Fin W) (Fin W) ℂ) with hsub | hnt
  · have h0 : ∀ M : Matrix (Fin W) (Fin W) ℂ, ‖M‖ = 0 := fun M => by
      rw [Subsingleton.elim M 0, norm_zero]
    have h1 : 0 ≤ 1 + 2 * normalH E * ‖V‖ / g := by positivity
    exact ⟨(h0 _).le.trans h1, (h0 _).le.trans h1⟩
  · have hnC : ‖C‖ = 1 := CStarRing.norm_of_mem_unitary hC
    have hnC' : ‖stepC g E C V‖ = 1 :=
      CStarRing.norm_of_mem_unitary (stepC_mem_unitaryGroup g E hC hV)
    have hnc : ‖Complex.I * ((normalH E / g : ℝ) : ℂ)‖ = normalH E / g := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg ht]
    constructor
    · have hF : stepF g E C V = 1 + (-Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C)) := by
        unfold stepF
        rw [sub_eq_add_neg, neg_mul, neg_smul]
      have hQ : ‖1 + C‖ ≤ 2 := by
        calc ‖1 + C‖ ≤ ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ + ‖C‖ := norm_add_le _ _
          _ = 2 := by rw [norm_one, hnC]; norm_num
      calc ‖stepF g E C V‖ ≤ 1 + ‖-Complex.I * ((normalH E / g : ℝ) : ℂ)‖ * (‖V‖ * 2) := by
            rw [hF]; exact nf_norm_one_add_le _ V (1 + C) hQ
        _ = 1 + 2 * normalH E * ‖V‖ / g := by
            rw [neg_mul, norm_neg, hnc]; ring
    · have hQ : ‖1 - star (normalPhase E) • stepC g E C V‖ ≤ 2 := by
        calc ‖1 - star (normalPhase E) • stepC g E C V‖
            ≤ ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ + ‖star (normalPhase E) • stepC g E C V‖ :=
              norm_sub_le _ _
          _ = 2 := by rw [norm_one, norm_smul, norm_star, nf_norm_normalPhase, hnC']; norm_num
      rw [inv_stepF g E hC hV]
      calc _ ≤ 1 + ‖Complex.I * ((normalH E / g : ℝ) : ℂ)‖ * (‖V‖ * 2) :=
            nf_norm_one_add_le _ V _ hQ
        _ = 1 + 2 * normalH E * ‖V‖ / g := by rw [hnc]; ring

end LSBA
