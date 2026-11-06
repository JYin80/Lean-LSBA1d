import LSBA.Transfer.FlagAction

/-!
# The volume cocycle

The logarithmic volume ratio `c(T; U, Y)` of (8.17) [eq:c-volume-cocycle] through Gram determinants
of frames, its measurability, `e^{c} = dist(Te, TU)`, the cocycle identity and (F.2) [cc:eq:boundc]
`|c| ≤ log‖T‖` (Lemma F.1 [cc:lem:quotient]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `log vol(T|_{ran P}) = ½ log det(P T* T P + 1 - P)` for an orthogonal projection `P`
(Definition 8.5 [up:def:transfer-operator]; `vol(T|_{0}) = 1`). -/
def logVol {ι : Type*} [Fintype ι] [DecidableEq ι] (T P : Matrix ι ι ℂ) : ℝ :=
  Real.log ‖(P * Tᴴ * T * P + (1 - P)).det‖ / 2

/-- The logarithmic volume ratio `c(T; U, Y)` of (8.17) [eq:c-volume-cocycle]. -/
def volCocycle {W : ℕ} (T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x : IsoFlag W) : ℝ :=
  logVol T x.1.2 - logVol T x.1.1

/-! ### Gram matrices of projections -/

open scoped ComplexOrder in
private theorem volCocycle_isUnit_gram {ι : Type*} [Fintype ι] [DecidableEq ι] {T P : Matrix ι ι ℂ}
    (hT : IsUnit T) (hP : Pᴴ = P) (hPP : P * P = P) :
    IsUnit (P * Tᴴ * T * P + (1 - P)) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have hker : ∀ z : ι → ℂ, (P * Tᴴ * T * P + (1 - P)) *ᵥ z = 0 → z = 0 := by
    intro z hz
    have h1 : P *ᵥ ((P * Tᴴ * T * P + (1 - P)) *ᵥ z) = 0 := by rw [hz, Matrix.mulVec_zero]
    have h2 : P * (P * Tᴴ * T * P + (1 - P)) = P * Tᴴ * T * P := by
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPP]
      abel
    rw [Matrix.mulVec_mulVec, h2] at h1
    set w : ι → ℂ := P *ᵥ z with hw
    have hPw : P *ᵥ w = w := by rw [hw, Matrix.mulVec_mulVec, hPP]
    have h3 : P *ᵥ (Tᴴ *ᵥ (T *ᵥ w)) = 0 := by
      rw [← h1, hw]; simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have hs : star w = star w ᵥ* P := by
      conv_lhs => rw [← hPw]
      rw [Matrix.star_mulVec, hP]
    have h4 : star (T *ᵥ w) ⬝ᵥ (T *ᵥ w) = 0 := by
      calc star (T *ᵥ w) ⬝ᵥ (T *ᵥ w) = star w ⬝ᵥ (Tᴴ *ᵥ (T *ᵥ w)) := by
            rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
        _ = (star w ᵥ* P) ⬝ᵥ (Tᴴ *ᵥ (T *ᵥ w)) := by rw [← hs]
        _ = star w ⬝ᵥ (P *ᵥ (Tᴴ *ᵥ (T *ᵥ w))) := (Matrix.dotProduct_mulVec _ _ _).symm
        _ = 0 := by rw [h3, dotProduct_zero]
    have h5 : T *ᵥ w = 0 := dotProduct_star_self_eq_zero.mp h4
    have h6 : w = 0 := by
      obtain ⟨U, rfl⟩ := hT
      have := congrArg (fun v => (↑U⁻¹ : Matrix ι ι ℂ) *ᵥ v) h5
      simpa [Matrix.mulVec_mulVec] using this
    have h7 : (1 - P) *ᵥ z = 0 := by
      have : (P * Tᴴ * T * P + (1 - P)) *ᵥ z = (P * Tᴴ * T * P) *ᵥ z + (1 - P) *ᵥ z :=
        Matrix.add_mulVec _ _ _
      rw [hz, h1, zero_add] at this
      exact this.symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hw, h6, sub_zero] at h7
    exact h7
  intro x y hxy
  have := hker (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.mp this

private theorem volCocycle_aux {ι : Type*} [Fintype ι] [DecidableEq ι] {T P : Matrix ι ι ℂ}
    (hT : IsUnit T) (hP : Pᴴ = P) (hPP : P * P = P) :
    ∃ N : Matrix ι ι ℂ, flagProj T P = T * N * Tᴴ ∧ Nᴴ = N ∧ P * N = N ∧ N * P = N ∧
      N * (P * Tᴴ * T * P) = P := by
  set M : Matrix ι ι ℂ := P * Tᴴ * T * P + (1 - P) with hM
  have hMd : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp (volCocycle_isUnit_gram hT hP hPP)
  have hMh : Mᴴ = M := by
    rw [hM, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hP]
    simp only [Matrix.mul_assoc]
  have hPM : P * M = P * Tᴴ * T * P := by
    rw [hM]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPP]
    abel
  have hMP : M * P = P * Tᴴ * T * P := by
    rw [hM]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hPP]
    abel
  have hi1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hMd
  have hi2 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMd
  have hcomm : P * M⁻¹ = M⁻¹ * P := by
    calc P * M⁻¹ = (M⁻¹ * M) * P * M⁻¹ := by rw [hi1, Matrix.one_mul]
      _ = M⁻¹ * (M * P) * M⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ * (P * M) * M⁻¹ := by rw [hMP, hPM]
      _ = M⁻¹ * P * (M * M⁻¹) := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ * P := by rw [hi2, Matrix.mul_one]
  have hMiH : (M⁻¹)ᴴ = M⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hMh]
  have e : P * M⁻¹ * P = M⁻¹ * P := by rw [hcomm, Matrix.mul_assoc, hPP]
  refine ⟨M⁻¹ * P, ?_, ?_, ?_, ?_, ?_⟩
  · have hf : flagProj T P = T * P * M⁻¹ * P * Tᴴ := rfl
    calc flagProj T P = T * (P * M⁻¹ * P) * Tᴴ := by rw [hf]; simp only [Matrix.mul_assoc]
      _ = T * (M⁻¹ * P) * Tᴴ := by rw [e]
  · rw [Matrix.conjTranspose_mul, hP, hMiH, hcomm]
  · rw [← Matrix.mul_assoc, e]
  · rw [Matrix.mul_assoc, hPP]
  · calc M⁻¹ * P * (P * Tᴴ * T * P) = M⁻¹ * P * (M * P) := by rw [hMP]
      _ = M⁻¹ * (P * M) * P := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ * (M * P) * P := by rw [hPM, hMP]
      _ = (M⁻¹ * M) * P * P := by simp only [Matrix.mul_assoc]
      _ = P := by rw [hi1, Matrix.one_mul, hPP]

private theorem volCocycle_isUnit_of_isoJ {W : ℕ}
    {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hT : Tᴴ * isoJ W * T = isoJ W) :
    IsUnit T := by
  have h : isoJ W * Tᴴ * isoJ W * T = 1 := by
    calc isoJ W * Tᴴ * isoJ W * T = isoJ W * (Tᴴ * isoJ W * T) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hT, isoJ_mul_isoJ]
  exact (Matrix.isUnit_iff_isUnit_det T).mpr (Matrix.isUnit_det_of_left_inverse h)

/-- `det(P G P + 1 - P) = det(1 + (G - 1) P)` for `P² = P`. -/
private theorem volCocycle_det_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (G P : Matrix ι ι ℂ)
    (hPP : P * P = P) : (P * G * P + (1 - P)).det = (1 + (G - 1) * P).det := by
  have h : P * G * P + (1 - P) = 1 + P * ((G - 1) * P) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc, hPP]
    abel
  rw [h, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hPP]

private theorem volCocycle_PGN {ι : Type*} [Fintype ι] [DecidableEq ι] {T P N : Matrix ι ι ℂ}
    (hP : Pᴴ = P) (hNh : Nᴴ = N) (hNP : N * P = N) (hNK : N * (P * Tᴴ * T * P) = P) :
    P * Tᴴ * T * N = P := by
  have hK : N * Tᴴ * T * P = P := by
    calc N * Tᴴ * T * P = N * P * Tᴴ * T * P := by rw [hNP]
      _ = N * (P * Tᴴ * T * P) := by simp only [Matrix.mul_assoc]
      _ = P := hNK
  have := congrArg Matrix.conjTranspose hK
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hNh, hP] at this
  simpa only [Matrix.mul_assoc] using this

/-- `det M_P(T₂ T₁) = det M_P(T₁) · det M_Π(T₂)` for `Π = flagProj T₁ P` and
`M_P(T) = P T* T P + 1 - P`. -/
private theorem volCocycle_det_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {T₁ P : Matrix ι ι ℂ}
    (T₂ : Matrix ι ι ℂ) (h₁ : IsUnit T₁) (hP : P.IsHermitian) (hPP : P * P = P) :
    (P * (T₂ * T₁)ᴴ * (T₂ * T₁) * P + (1 - P)).det =
      (P * T₁ᴴ * T₁ * P + (1 - P)).det *
        (flagProj T₁ P * T₂ᴴ * T₂ * flagProj T₁ P + (1 - flagProj T₁ P)).det := by
  obtain ⟨N, hf, hNh, hPN, hNP, hNK⟩ := volCocycle_aux h₁ hP.eq hPP
  obtain ⟨hFh, hFF, -⟩ := flagProj_spec h₁ hP hPP
  have hPGN := volCocycle_PGN hP.eq hNh hNP hNK
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Matrix ι ι ℂ, Δ = T₁ᴴ * (T₂ᴴ * T₂ - 1) * T₁ := ⟨_, rfl⟩
  have hMN : (P * T₁ᴴ * T₁ * P + (1 - P)) * N = P := by
    calc (P * T₁ᴴ * T₁ * P + (1 - P)) * N = P * T₁ᴴ * T₁ * (P * N) + (N - P * N) := by
          simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = P := by rw [hPN, hPGN]; abel
  have hM : P * (T₂ * T₁)ᴴ * (T₂ * T₁) * P + (1 - P) =
      (P * T₁ᴴ * T₁ * P + (1 - P)) * (1 + N * Δ * P) := by
    have e1 : P * (T₂ * T₁)ᴴ * (T₂ * T₁) * P = P * T₁ᴴ * T₁ * P + P * Δ * P := by
      rw [hΔ, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    have e3 : (P * T₁ᴴ * T₁ * P + (1 - P)) * (N * Δ * P) = P * Δ * P := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMN]
    rw [e1, Matrix.mul_add, Matrix.mul_one, e3]
    abel
  have hA : (1 + N * Δ * P).det = (1 + N * Δ).det := by
    rw [Matrix.det_one_add_mul_comm (N * Δ) P, ← Matrix.mul_assoc, hPN]
  have hB : (flagProj T₁ P * T₂ᴴ * T₂ * flagProj T₁ P + (1 - flagProj T₁ P)).det =
      (1 + N * Δ).det := by
    have := volCocycle_det_eq (T₂ᴴ * T₂) (flagProj T₁ P) hFF
    rw [show flagProj T₁ P * T₂ᴴ * T₂ * flagProj T₁ P =
      flagProj T₁ P * (T₂ᴴ * T₂) * flagProj T₁ P by simp only [Matrix.mul_assoc], this, hf]
    have e2 : (T₂ᴴ * T₂ - 1) * (T₁ * N * T₁ᴴ) = ((T₂ᴴ * T₂ - 1) * (T₁ * N)) * T₁ᴴ := by
      simp only [Matrix.mul_assoc]
    have e4 : T₁ᴴ * ((T₂ᴴ * T₂ - 1) * (T₁ * N)) = Δ * N := by
      rw [hΔ]; simp only [Matrix.mul_assoc]
    rw [e2, Matrix.det_one_add_mul_comm, e4, Matrix.det_one_add_mul_comm]
  rw [hM, Matrix.det_mul, hA, hB]

/-- `vol(T|_Z)` does not depend on the frame: for `Φ* Φ = 1`,
`det(ΦΦ* T* T ΦΦ* + 1 - ΦΦ*) = det(Φ* T* T Φ)` (Definition 8.5 [up:def:transfer-operator]). -/
theorem det_flagGram_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : Matrix ι ι ℂ) {Φ : Matrix ι κ ℂ} (hΦ : Φᴴ * Φ = 1) :
    (Φ * Φᴴ * Tᴴ * T * (Φ * Φᴴ) + (1 - Φ * Φᴴ)).det = (Φᴴ * Tᴴ * T * Φ).det := by
  have h : Φ * Φᴴ * Tᴴ * T * (Φ * Φᴴ) + (1 - Φ * Φᴴ) =
      1 + Φ * ((Φᴴ * Tᴴ * T * Φ - 1) * Φᴴ) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [h, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hΦ, Matrix.mul_one]
  congr 1
  abel


private theorem volCocycle_vecMul_eq {ι : Type*} [Fintype ι] {A : Matrix ι ι ℂ} (hA : Aᴴ = A)
    {e v : ι → ℂ} (h : A *ᵥ e = v) : star e ᵥ* A = star v := by
  have := Matrix.star_mulVec A e
  rw [hA, h] at this
  exact this.symm

open scoped ComplexOrder in
/-- `ran P_Y = ran P_U ⊕ ℂ e` for the flag `U ⊂ Y` and a unit `e ∈ Y ⊖ U`: `P_Y = P_U + e e*`. -/
private theorem volCocycle_rank_one {ι : Type*} [Fintype ι] [DecidableEq ι] {PU PY : Matrix ι ι ℂ}
    (hUh : PUᴴ = PU) (hYh : PYᴴ = PY) (hUU : PU * PU = PU) (hYY : PY * PY = PY)
    (hYU : PY * PU = PU) (htr : PY.trace = PU.trace + 1) {e : ι → ℂ} (heY : PY *ᵥ e = e)
    (heU : PU *ᵥ e = 0) (he : star e ⬝ᵥ e = 1) :
    PY = PU + Matrix.vecMulVec e (star e) := by
  set E : Matrix ι ι ℂ := Matrix.vecMulVec e (star e) with hE
  have hEh : Eᴴ = E := by rw [hE, Matrix.conjTranspose_vecMulVec, star_star]
  have hEE : E * E = E := by
    rw [hE, Matrix.vecMulVec_mul_vecMulVec, he, one_smul]
  have hrow : ∀ A : Matrix ι ι ℂ, Aᴴ = A → ∀ v : ι → ℂ, A *ᵥ e = v → star e ᵥ* A = star v :=
    fun A hA v h => volCocycle_vecMul_eq hA h
  have hYE : PY * E = E := by rw [hE, Matrix.mul_vecMulVec, heY]
  have hEY : E * PY = E := by rw [hE, Matrix.vecMulVec_mul, hrow PY hYh e heY]
  have hUE : PU * E = 0 := by rw [hE, Matrix.mul_vecMulVec, heU, Matrix.zero_vecMulVec]
  have hEU : E * PU = 0 := by
    rw [hE, Matrix.vecMulVec_mul, hrow PU hUh 0 heU, star_zero, Matrix.vecMulVec_zero]
  have hUY : PU * PY = PU := by
    have := congrArg Matrix.conjTranspose hYU
    rwa [Matrix.conjTranspose_mul, hUh, hYh] at this
  have hDh : (PY - PU - E)ᴴ = PY - PU - E := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_sub, hYh, hUh, hEh]
  have hDD : (PY - PU - E) * (PY - PU - E) = PY - PU - E := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, hYY, hYU, hYE, hUY, hUU, hUE, hEY, hEU, hEE]
    abel
  have htrD : ((PY - PU - E)ᴴ * (PY - PU - E)).trace = 0 := by
    rw [hDh, hDD, Matrix.trace_sub, Matrix.trace_sub, htr, hE, Matrix.trace_vecMulVec,
      dotProduct_comm, he]
    ring
  have h0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htrD
  exact sub_eq_iff_eq_add'.mp (sub_eq_zero.mp h0)

private theorem volCocycle_det_rank_one {ι : Type*} [Fintype ι] [DecidableEq ι] {T P : Matrix ι ι ℂ}
    (hT : IsUnit T) (hP : P.IsHermitian) (hPP : P * P = P) {e : ι → ℂ} (heU : P *ᵥ e = 0)
    (he : star e ⬝ᵥ e = 1) :
    ((P + Matrix.vecMulVec e (star e)) * Tᴴ * T * (P + Matrix.vecMulVec e (star e)) +
        (1 - (P + Matrix.vecMulVec e (star e)))).det =
      (P * Tᴴ * T * P + (1 - P)).det *
        (star (T *ᵥ e) ⬝ᵥ ((1 - flagProj T P) *ᵥ (T *ᵥ e))) := by
  obtain ⟨N, hf, hNh, hPN, hNP, hNK⟩ := volCocycle_aux hT hP.eq hPP
  have hPGN := volCocycle_PGN hP.eq hNh hNP hNK
  obtain ⟨G, hG⟩ : ∃ G : Matrix ι ι ℂ, G = Tᴴ * T := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Matrix ι ι ℂ, E = Matrix.vecMulVec e (star e) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix ι ι ℂ, Q = 1 - P := ⟨_, rfl⟩
  have hPGN' : P * G * N = P := by rw [hG]; simpa only [Matrix.mul_assoc] using hPGN
  have hrP : star e ᵥ* P = 0 := by rw [volCocycle_vecMul_eq hP.eq heU, star_zero]
  have hNe : N *ᵥ e = 0 := by
    calc N *ᵥ e = (N * P) *ᵥ e := by rw [hNP]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, heU, Matrix.mulVec_zero]
  have hrN : star e ᵥ* N = 0 := by rw [volCocycle_vecMul_eq hNh hNe, star_zero]
  have hPE : P * E = 0 := by rw [hE, Matrix.mul_vecMulVec, heU, Matrix.zero_vecMulVec]
  have hEP : E * P = 0 := by rw [hE, Matrix.vecMulVec_mul, hrP, Matrix.vecMulVec_zero]
  have hEE : E * E = E := by rw [hE, Matrix.vecMulVec_mul_vecMulVec, he, one_smul]
  have hRR : (P + E) * (P + E) = P + E := by
    simp only [Matrix.add_mul, Matrix.mul_add, hPP, hPE, hEP, hEE]; abel
  have hQQ : Q * Q = Q := by
    rw [hQ]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hPP]
    abel
  have hQN : Q * N = 0 := by rw [hQ, Matrix.sub_mul, Matrix.one_mul, hPN, sub_self]
  have hPQ : P * Q = 0 := by rw [hQ, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  have hQP : Q * P = 0 := by rw [hQ, Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  have hL : 1 + (G - 1) * P = Q + G * P := by
    rw [hQ, Matrix.sub_mul, Matrix.one_mul]; abel
  have hLL : (Q + G * P) * (Q + N - Q * G * N) = 1 := by
    have e1 : (Q + G * P) * (Q + N - Q * G * N) =
        Q * Q + Q * N - Q * Q * G * N + G * (P * Q) + G * (P * N) - G * (P * Q) * G * N := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    have h5 : Q * G * N = G * N - P := by
      rw [hQ, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, hPGN']
    rw [e1, hQQ, hQN, hPQ, hPN, h5, hQ]
    simp only [Matrix.mul_zero, Matrix.zero_mul]
    abel
  -- the scalar `1 + e* L⁻¹ (G - 1) e`
  have hPa : ∀ a : ι → ℂ, star e ⬝ᵥ (P *ᵥ a) = 0 := fun a => by
    rw [Matrix.dotProduct_mulVec, hrP, zero_dotProduct]
  have hNa : ∀ a : ι → ℂ, star e ⬝ᵥ (N *ᵥ a) = 0 := fun a => by
    rw [Matrix.dotProduct_mulVec, hrN, zero_dotProduct]
  have hQa : ∀ a : ι → ℂ, star e ⬝ᵥ (Q *ᵥ a) = star e ⬝ᵥ a := fun a => by
    rw [hQ, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hPa, sub_zero]
  have hz : ∀ y : ι → ℂ, star e ⬝ᵥ ((Q + N - Q * G * N) *ᵥ y) =
      star e ⬝ᵥ y - star e ⬝ᵥ (G *ᵥ (N *ᵥ y)) := fun y => by
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add, hQa, hNa,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQa, add_zero]
  have hGv : ∀ x : ι → ℂ, Tᴴ *ᵥ (T *ᵥ x) = G *ᵥ x := fun x => by
    rw [Matrix.mulVec_mulVec, hG]
  have hkey : ∀ y : ι → ℂ, star (T *ᵥ e) ⬝ᵥ y = star e ⬝ᵥ (Tᴴ *ᵥ y) := fun y => by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have hL1 : 1 + star e ⬝ᵥ ((Q + N - Q * G * N) *ᵥ ((G - 1) *ᵥ e)) =
      star e ⬝ᵥ (G *ᵥ e) - star e ⬝ᵥ (G *ᵥ (N *ᵥ (G *ᵥ e))) := by
    have h1 : (G - 1) *ᵥ e = G *ᵥ e - e := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    have h2 : N *ᵥ (G *ᵥ e - e) = N *ᵥ (G *ᵥ e) := by rw [Matrix.mulVec_sub, hNe, sub_zero]
    rw [hz, h1, h2, dotProduct_sub, he]
    ring
  have hR1 : star (T *ᵥ e) ⬝ᵥ ((1 - flagProj T P) *ᵥ (T *ᵥ e)) =
      star e ⬝ᵥ (G *ᵥ e) - star e ⬝ᵥ (G *ᵥ (N *ᵥ (G *ᵥ e))) := by
    have h3 : (1 - flagProj T P) *ᵥ (T *ᵥ e) = T *ᵥ e - T *ᵥ (N *ᵥ (Tᴴ *ᵥ (T *ᵥ e))) := by
      rw [hf, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]
    rw [h3, dotProduct_sub, hkey, hkey]
    simp only [hGv]
  have hdetP : (P * Tᴴ * T * P + (1 - P)).det = (Q + G * P).det := by
    rw [← hL, ← volCocycle_det_eq G P hPP, hG]
    simp only [Matrix.mul_assoc]
  have hdetR : ((P + E) * Tᴴ * T * (P + E) + (1 - (P + E))).det =
      (1 + (G - 1) * (P + E)).det := by
    rw [← volCocycle_det_eq G (P + E) hRR, hG]
    simp only [Matrix.mul_assoc]
  have hX : (G - 1) * E = Matrix.vecMulVec ((G - 1) *ᵥ e) (star e) := by
    rw [hE, Matrix.mul_vecMulVec]
  have hRight : (Q + G * P) * (1 + (Q + N - Q * G * N) *
      Matrix.vecMulVec ((G - 1) *ᵥ e) (star e)) = (Q + G * P) +
      Matrix.vecMulVec ((G - 1) *ᵥ e) (star e) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hLL, Matrix.one_mul]
  have hLeft : 1 + (G - 1) * (P + E) = (Q + G * P) +
      Matrix.vecMulVec ((G - 1) *ᵥ e) (star e) := by
    rw [Matrix.mul_add, ← add_assoc, hL, hX]
  rw [← hE, hdetR, hLeft, ← hRight, Matrix.det_mul, ← hdetP, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, hL1, hR1]

private theorem volCocycle_dot_self {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_sum,
    Complex.ofReal_pow]

private theorem volCocycle_dot_proj {ι : Type*} [Fintype ι] {F : Matrix ι ι ℂ} (hFh : Fᴴ = F)
    (hFF : F * F = F) (w : ι → ℂ) : star (F *ᵥ w) ⬝ᵥ (F *ᵥ w) = star w ⬝ᵥ (F *ᵥ w) := by
  rw [Matrix.star_mulVec, hFh, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hFF]

/-- `e^{c(T; U, Y)} = ‖(1 - Π_{TU}) T e‖` for a unit `e ∈ Y ⊖ U`. -/
private theorem volCocycle_exp_aux {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : IsUnit T) (x : IsoFlag W) {e : Fin 2 × Fin W → ℂ} (heY : x.1.2 *ᵥ e = e)
    (heU : x.1.1 *ᵥ e = 0) (he : star e ⬝ᵥ e = 1) :
    Real.exp (volCocycle T x) =
      Real.sqrt (∑ i, ‖((1 - flagProj T x.1.1) *ᵥ (T *ᵥ e)) i‖ ^ 2) := by
  obtain ⟨⟨hUh, hUU, hUtr, hUJ⟩, hYh, hYY, hYtr, hYU, hYJ⟩ := x.2
  have hW : 1 ≤ W := by
    by_contra h
    have hW0 : W = 0 := by omega
    subst hW0
    have : star e ⬝ᵥ e = 0 := by
      simp only [dotProduct]
      exact Finset.sum_eq_zero fun i _ => (Fin.elim0 i.2)
    rw [this] at he
    exact zero_ne_one he
  have htr : x.1.2.trace = x.1.1.trace + 1 := by
    have h1 : W - 1 + 1 = W := Nat.sub_add_cancel hW
    rw [hYtr, hUtr]
    exact_mod_cast h1.symm
  have hY' : x.1.2 = x.1.1 + Matrix.vecMulVec e (star e) :=
    volCocycle_rank_one hUh.eq hYh.eq hUU hYY hYU htr heY heU he
  obtain ⟨hFh, hFF, -⟩ := flagProj_spec hT hUh hUU
  have hdet := volCocycle_det_rank_one hT hUh hUU heU he
  rw [← hY'] at hdet
  have hu1 : (x.1.1 * Tᴴ * T * x.1.1 + (1 - x.1.1)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (volCocycle_isUnit_gram hT hUh.eq hUU)).ne_zero
  have hu2 : (x.1.2 * Tᴴ * T * x.1.2 + (1 - x.1.2)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (volCocycle_isUnit_gram hT hYh.eq hYY)).ne_zero
  set w : Fin 2 × Fin W → ℂ := T *ᵥ e with hw
  set F : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := 1 - flagProj T x.1.1 with hF
  have hFh' : Fᴴ = F := by rw [hF, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hFh.eq]
  have hFF' : F * F = F := by
    rw [hF]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hFF]
    abel
  have hs : star w ⬝ᵥ (F *ᵥ w) = ((∑ i, ‖(F *ᵥ w) i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← volCocycle_dot_proj hFh' hFF' w, volCocycle_dot_self]
  rw [hs] at hdet
  set t : ℝ := ∑ i, ‖(F *ᵥ w) i‖ ^ 2 with ht
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => by positivity
  have hnorm : ‖(x.1.2 * Tᴴ * T * x.1.2 + (1 - x.1.2)).det‖ =
      ‖(x.1.1 * Tᴴ * T * x.1.1 + (1 - x.1.1)).det‖ * t := by
    rw [hdet, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
  have hpos2 : 0 < ‖(x.1.2 * Tᴴ * T * x.1.2 + (1 - x.1.2)).det‖ := norm_pos_iff.mpr hu2
  have hpos1 : 0 < ‖(x.1.1 * Tᴴ * T * x.1.1 + (1 - x.1.1)).det‖ := norm_pos_iff.mpr hu1
  have htpos : 0 < t := by
    by_contra h
    have : t = 0 := le_antisymm (not_lt.mp h) ht0
    rw [this, mul_zero] at hnorm
    exact hpos2.ne' hnorm
  have hlog : Real.log ‖(x.1.2 * Tᴴ * T * x.1.2 + (1 - x.1.2)).det‖ =
      Real.log ‖(x.1.1 * Tᴴ * T * x.1.1 + (1 - x.1.1)).det‖ + Real.log t := by
    rw [hnorm, Real.log_mul hpos1.ne' htpos.ne']
  have hc : volCocycle T x = Real.log t / 2 := by
    unfold volCocycle logVol
    rw [hlog]; ring
  rw [hc, Real.sqrt_eq_rpow, Real.rpow_def_of_pos htpos]
  congr 1
  ring

/-- Base times height (Definition 8.5 [up:def:transfer-operator]): for invertible `T` and a unit
`e ∈ Y ⊖ U`, `e^{c(T; U, Y)} = dist(T e, T U)`. -/
theorem exp_volCocycle_eq {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hT : IsUnit T)
    (x : IsoFlag W) {e : Fin 2 × Fin W → ℂ} (heY : x.1.2 *ᵥ e = e) (heU : x.1.1 *ᵥ e = 0)
    (he : star e ⬝ᵥ e = 1) :
    Real.exp (volCocycle T x) =
      Real.sqrt (∑ i, ‖((1 - flagProj T x.1.1) *ᵥ (T *ᵥ e)) i‖ ^ 2) :=
  volCocycle_exp_aux hT x heY heU he

private theorem volCocycle_logVol_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T₁ T₂ P : Matrix ι ι ℂ} (h₁ : IsUnit T₁) (h₂ : IsUnit T₂) (hP : P.IsHermitian)
    (hPP : P * P = P) : logVol (T₂ * T₁) P = logVol T₁ P + logVol T₂ (flagProj T₁ P) := by
  obtain ⟨hFh, hFF, -⟩ := flagProj_spec h₁ hP hPP
  have u1 : (P * T₁ᴴ * T₁ * P + (1 - P)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (volCocycle_isUnit_gram h₁ hP.eq hPP)).ne_zero
  have u2 : (flagProj T₁ P * T₂ᴴ * T₂ * flagProj T₁ P + (1 - flagProj T₁ P)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (volCocycle_isUnit_gram h₂ hFh.eq hFF)).ne_zero
  unfold logVol
  rw [volCocycle_det_mul T₂ h₁ hP hPP, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr u1) (norm_ne_zero_iff.mpr u2)]
  ring

private theorem volCocycle_of_gram_eq_one {W : ℕ}
    {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hT : Tᴴ * T = 1) (x : IsoFlag W) :
    volCocycle T x = 0 := by
  obtain ⟨⟨hUh, hUU, -, -⟩, hYh, hYY, -⟩ := x.2
  have hP : ∀ P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, P * P = P →
      (P * Tᴴ * T * P + (1 - P)).det = 1 := by
    intro P hPP
    have : P * Tᴴ * T * P + (1 - P) = 1 := by
      calc P * Tᴴ * T * P + (1 - P) = P * (Tᴴ * T) * P + (1 - P) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hT, Matrix.mul_one, hPP]; abel
    rw [this, Matrix.det_one]
  unfold volCocycle logVol
  rw [hP _ hYY, hP _ hUU]
  simp

/-- The cocycle identity `c(T₂T₁; U, Y) = c(T₁; U, Y) + c(T₂; T₁U, T₁Y)` (proof of Lemma 8.6
[up:lem:operator-reduction]; Lemma F.1 [cc:lem:quotient]). -/
theorem volCocycle_mul {W : ℕ} {T₁ T₂ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (h₁ : T₁ᴴ * isoJ W * T₁ = isoJ W) (h₂ : IsUnit T₂) (x : IsoFlag W) :
    volCocycle (T₂ * T₁) x = volCocycle T₁ x + volCocycle T₂ (flagAct T₁ x) := by
  have hu₁ := volCocycle_isUnit_of_isoJ h₁
  obtain ⟨⟨hUh, hUU, -, -⟩, hYh, hYY, -⟩ := x.2
  have c := flagAct_coe h₁ x
  have c1 : (flagAct T₁ x).1.1 = flagProj T₁ x.1.1 := congrArg Prod.fst c
  have c2 : (flagAct T₁ x).1.2 = flagProj T₁ x.1.2 := congrArg Prod.snd c
  unfold volCocycle
  rw [c1, c2, volCocycle_logVol_mul hu₁ h₂ hUh hUU, volCocycle_logVol_mul hu₁ h₂ hYh hYY]
  ring

private theorem volCocycle_proj_le {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Matrix ι ι ℂ}
    (hFh : Fᴴ = F) (hFF : F * F = F) (w : ι → ℂ) :
    ∑ i, ‖(F *ᵥ w) i‖ ^ 2 ≤ ∑ i, ‖w i‖ ^ 2 := by
  have hGh : (1 - F)ᴴ = 1 - F := by rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hFh]
  have hGG : (1 - F) * (1 - F) = 1 - F := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hFF]
    abel
  have h1 : star w ⬝ᵥ w = star w ⬝ᵥ (F *ᵥ w) + star w ⬝ᵥ ((1 - F) *ᵥ w) := by
    rw [← dotProduct_add, ← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  rw [← volCocycle_dot_proj hFh hFF, ← volCocycle_dot_proj hGh hGG, volCocycle_dot_self,
    volCocycle_dot_self, volCocycle_dot_self] at h1
  have h2 : ∑ i, ‖w i‖ ^ 2 = ∑ i, ‖(F *ᵥ w) i‖ ^ 2 + ∑ i, ‖((1 - F) *ᵥ w) i‖ ^ 2 := by
    exact_mod_cast h1
  have h3 : 0 ≤ ∑ i, ‖((1 - F) *ᵥ w) i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  linarith

private theorem volCocycle_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (e : ι → ℂ) (he : ∑ i, ‖e i‖ ^ 2 = 1) : ∑ i, ‖(A *ᵥ e) i‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 e)
  simp only [EuclideanSpace.norm_eq, he, Real.sqrt_one, mul_one] at h
  have h0 : 0 ≤ ∑ i, ‖(A *ᵥ e) i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have := (Real.sqrt_le_left (norm_nonneg A)).mp (by simpa using h)
  exact this

private theorem volCocycle_exists_unit {W : ℕ} (x : IsoFlag W) (hW : 1 ≤ W) :
    ∃ e : Fin 2 × Fin W → ℂ, x.1.2 *ᵥ e = e ∧ x.1.1 *ᵥ e = 0 ∧ star e ⬝ᵥ e = 1 := by
  obtain ⟨⟨hUh, hUU, hUtr, hUJ⟩, hYh, hYY, hYtr, hYU, hYJ⟩ := x.2
  have hUY : x.1.1 * x.1.2 = x.1.1 := by
    have := congrArg Matrix.conjTranspose hYU
    rwa [Matrix.conjTranspose_mul, hUh.eq, hYh.eq] at this
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Q = x.1.2 - x.1.1 := ⟨_, rfl⟩
  have hQQ : Q * Q = Q := by
    rw [hQ]
    simp only [Matrix.sub_mul, Matrix.mul_sub, hYY, hYU, hUY, hUU]
    abel
  have hYQ : x.1.2 * Q = Q := by
    rw [hQ, Matrix.mul_sub, hYY, hYU]
  have hUQ : x.1.1 * Q = 0 := by
    rw [hQ, Matrix.mul_sub, hUY, hUU, sub_self]
  have htr : Q.trace = 1 := by
    have h1 : W - 1 + 1 = W := Nat.sub_add_cancel hW
    rw [hQ, Matrix.trace_sub, hYtr, hUtr]
    have : ((W : ℕ) : ℂ) = ((W - 1 : ℕ) : ℂ) + 1 := by exact_mod_cast h1.symm
    rw [this]; ring
  have hQne : Q ≠ 0 := fun h => by
    rw [h, Matrix.trace_zero] at htr
    exact zero_ne_one htr
  obtain ⟨v, hv⟩ : ∃ v : Fin 2 × Fin W → ℂ, Q *ᵥ v ≠ 0 := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    refine hQne (Matrix.ext fun i j => ?_)
    have := congrFun (hcon (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one] using this
  obtain ⟨w, hw⟩ : ∃ w : Fin 2 × Fin W → ℂ, w = Q *ᵥ v := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := hw ▸ hv
  have hQw : Q *ᵥ w = w := by
    calc Q *ᵥ w = Q *ᵥ (Q *ᵥ v) := by rw [hw]
      _ = (Q * Q) *ᵥ v := Matrix.mulVec_mulVec v Q Q
      _ = w := by rw [hQQ, hw]
  have hYw : x.1.2 *ᵥ w = w := by
    calc x.1.2 *ᵥ w = x.1.2 *ᵥ (Q *ᵥ w) := by rw [hQw]
      _ = (x.1.2 * Q) *ᵥ w := Matrix.mulVec_mulVec w x.1.2 Q
      _ = w := by rw [hYQ, hQw]
  have hUw : x.1.1 *ᵥ w = 0 := by
    calc x.1.1 *ᵥ w = x.1.1 *ᵥ (Q *ᵥ w) := by rw [hQw]
      _ = (x.1.1 * Q) *ᵥ w := Matrix.mulVec_mulVec w x.1.1 Q
      _ = 0 := by rw [hUQ, Matrix.zero_mulVec]
  have hnw : 0 < ∑ i, ‖w i‖ ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hcon
      simp only [ne_eq, not_exists, not_not] at hcon
      exact hw0 (funext hcon)
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => ‖w i‖ ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ i))
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ∑ i, ‖w i‖ ^ 2 := ⟨_, rfl⟩
  have htpos : 0 < t := ht ▸ hnw
  refine ⟨(((Real.sqrt t)⁻¹ : ℝ) : ℂ) • w, ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, hYw]
  · rw [Matrix.mulVec_smul, hUw, smul_zero]
  · rw [volCocycle_dot_self]
    have : ∑ i, ‖((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • w) i‖ ^ 2 = 1 := by
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, mul_pow,
        ← Finset.mul_sum, ← ht]
      rw [Real.norm_of_nonneg (by positivity), inv_pow, Real.sq_sqrt htpos.le]
      field_simp
    rw [this]; simp

private theorem volCocycle_le_log_norm {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : IsUnit T) (x : IsoFlag W) (hW : 1 ≤ W) : volCocycle T x ≤ Real.log ‖T‖ := by
  obtain ⟨e, heY, heU, he⟩ := volCocycle_exists_unit x hW
  have h := volCocycle_exp_aux hT x heY heU he
  obtain ⟨⟨hUh, hUU, -, -⟩, hYh, hYY, -⟩ := x.2
  obtain ⟨hFh, hFF, -⟩ := flagProj_spec hT hUh hUU
  have hFh' : (1 - flagProj T x.1.1)ᴴ = 1 - flagProj T x.1.1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hFh.eq]
  have hFF' : (1 - flagProj T x.1.1) * (1 - flagProj T x.1.1) = 1 - flagProj T x.1.1 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hFF]
    abel
  have he' : ∑ i, ‖e i‖ ^ 2 = 1 := by
    have := volCocycle_dot_self e
    rw [he] at this
    exact_mod_cast this.symm
  have hsum : ∑ i, ‖((1 - flagProj T x.1.1) *ᵥ (T *ᵥ e)) i‖ ^ 2 ≤ ‖T‖ ^ 2 :=
    (volCocycle_proj_le hFh' hFF' (T *ᵥ e)).trans (volCocycle_sq_le T e he')
  have hexp : Real.exp (volCocycle T x) ≤ ‖T‖ := by
    rw [h]
    exact Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hsum⟩
  calc volCocycle T x = Real.log (Real.exp (volCocycle T x)) := (Real.log_exp _).symm
    _ ≤ Real.log ‖T‖ := Real.log_le_log (Real.exp_pos _) hexp

/-- (F.2) [cc:eq:boundc]: `|c(T; U, Y)| ≤ log ‖T‖` for `T* J T = J`. -/
theorem abs_volCocycle_le {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : Tᴴ * isoJ W * T = isoJ W) (x : IsoFlag W) : |volCocycle T x| ≤ Real.log ‖T‖ := by
  rcases Nat.eq_zero_or_pos W with h0 | hW
  · subst h0
    have hY : x.1.2 = x.1.1 := Matrix.ext fun i _ => Fin.elim0 i.2
    have hT0 : T = 0 := Matrix.ext fun i _ => Fin.elim0 i.2
    have h1 : volCocycle T x = 0 := by
      unfold volCocycle
      rw [hY, sub_self]
    rw [h1, hT0]
    simp
  · have hu := volCocycle_isUnit_of_isoJ hT
    have hinv : IsUnit T⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hu
    have hup := volCocycle_le_log_norm hu x hW
    have hup' := volCocycle_le_log_norm hinv (flagAct T x) hW
    rw [norm_inv_eq_of_isoJ hT] at hup'
    have hmul := volCocycle_mul hT hinv x
    have e1 : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp hu)
    rw [e1, volCocycle_of_gram_eq_one (by simp) x] at hmul
    rw [abs_le]
    constructor <;> linarith

/-- `c(T; U, Y) = 0` for unitary `T`. -/
theorem volCocycle_of_mem_unitaryGroup {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : T ∈ Matrix.unitaryGroup (Fin 2 × Fin W) ℂ) (x : IsoFlag W) : volCocycle T x = 0 := by
  refine volCocycle_of_gram_eq_one ?_ x
  have := Matrix.mem_unitaryGroup_iff'.mp hT
  rwa [Matrix.star_eq_conjTranspose] at this

private theorem volCocycle_measurable_logVol {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable fun q : Matrix ι ι ℂ × Matrix ι ι ℂ => logVol q.1 q.2 := by
  have hc : Continuous fun q : Matrix ι ι ℂ × Matrix ι ι ℂ =>
      q.2 * q.1ᴴ * q.1 * q.2 + (1 - q.2) := by
    fun_prop
  have hd : Continuous fun q : Matrix ι ι ℂ × Matrix ι ι ℂ =>
      (q.2 * q.1ᴴ * q.1 * q.2 + (1 - q.2)).det := hc.matrix_det
  have hn : Continuous fun q : Matrix ι ι ℂ × Matrix ι ι ℂ =>
      ‖(q.2 * q.1ᴴ * q.1 * q.2 + (1 - q.2)).det‖ := continuous_norm.comp hd
  exact (Real.measurable_log.comp hn.measurable).div_const 2

/-- The cocycle is jointly measurable in `(T, U, Y)`. -/
theorem measurable_volCocycle (W : ℕ) :
    Measurable fun p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × IsoFlag W =>
      volCocycle p.1 p.2 := by
  have h1 : Measurable fun p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × IsoFlag W =>
      (p.1, p.2.1.1) :=
    measurable_fst.prodMk (measurable_fst.comp (measurable_subtype_coe.comp measurable_snd))
  have h2 : Measurable fun p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × IsoFlag W =>
      (p.1, p.2.1.2) :=
    measurable_fst.prodMk (measurable_snd.comp (measurable_subtype_coe.comp measurable_snd))
  have e : (fun p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × IsoFlag W => volCocycle p.1 p.2) =
      fun p => (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => logVol q.1 q.2) (p.1, p.2.1.2) -
      (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => logVol q.1 q.2) (p.1, p.2.1.1) := by
    funext p
    rfl
  rw [e]
  exact (volCocycle_measurable_logVol.comp h2).sub (volCocycle_measurable_logVol.comp h1)

end LSBA
