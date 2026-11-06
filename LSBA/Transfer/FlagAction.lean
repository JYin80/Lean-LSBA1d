import LSBA.Transfer.IsoGroup

/-!
# Isotropic flags and the action of 𝒢

Isotropic flags `U ⊂ Y` encoded by their orthogonal projections, with the Borel structure of the
projections, and the action `T·(U, Y) = (TU, TY)` of `J`-unitary matrices: well defined, a group
action, and measurable (Definition 8.5 [up:def:transfer-operator]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The `(W-1)`-dimensional `J`-isotropic subspaces `U ⊂ ℂ^{2W}`, as orthogonal projections. -/
def isoBases (W : ℕ) : Set (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :=
  {P | P.IsHermitian ∧ P * P = P ∧ P.trace = ((W - 1 : ℕ) : ℂ) ∧ P * isoJ W * P = 0}

/-- Isotropic flags `U ⊂ Y` (`dim U = W - 1`, `dim Y = W`, `Y` `J`-isotropic) of
Definition 8.5 [up:def:transfer-operator], as pairs of orthogonal projections `(P_U, P_Y)`. -/
def isoFlags (W : ℕ) :
    Set (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :=
  {x | x.1 ∈ isoBases W ∧ x.2.IsHermitian ∧ x.2 * x.2 = x.2 ∧ x.2.trace = (W : ℂ) ∧
    x.2 * x.1 = x.1 ∧ x.2 * isoJ W * x.2 = 0}

/-- The isotropic flags, with the Borel structure of the pair `(P_U, P_Y)`. -/
abbrev IsoFlag (W : ℕ) : Type := ↥(isoFlags W)

/-- `T P (P T* T P + 1 - P)⁻¹ P T*`: for invertible `T` and an orthogonal projection `P`, the
orthogonal projection onto `T (ran P)`. -/
def flagProj {ι : Type*} [Fintype ι] [DecidableEq ι] (T P : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  T * P * (P * Tᴴ * T * P + (1 - P))⁻¹ * P * Tᴴ

/-- The image flag `(TU, TY)`; the flag `x` itself if the image pair is not a flag. -/
def flagAct {W : ℕ} (T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x : IsoFlag W) : IsoFlag W :=
  if h : (flagProj T x.1.1, flagProj T x.1.2) ∈ isoFlags W then ⟨_, h⟩ else x

open scoped ComplexOrder in
private theorem flagAction_isUnit_gram {ι : Type*} [Fintype ι] [DecidableEq ι] {T P : Matrix ι ι ℂ}
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

private theorem flagAction_aux {ι : Type*} [Fintype ι] [DecidableEq ι] {T P : Matrix ι ι ℂ}
    (hT : IsUnit T) (hP : Pᴴ = P) (hPP : P * P = P) :
    ∃ N : Matrix ι ι ℂ, flagProj T P = T * N * Tᴴ ∧ Nᴴ = N ∧ P * N = N ∧ N * P = N ∧
      N * (P * Tᴴ * T * P) = P := by
  set M : Matrix ι ι ℂ := P * Tᴴ * T * P + (1 - P) with hM
  have hMd : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp (flagAction_isUnit_gram hT hP hPP)
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

private theorem flagAction_aux_K {ι : Type*} [Fintype ι] {T P N : Matrix ι ι ℂ} (hNP : N * P = N)
    (hNK : N * (P * Tᴴ * T * P) = P) : N * Tᴴ * T * P = P := by
  calc N * Tᴴ * T * P = N * P * Tᴴ * T * P := by rw [hNP]
    _ = N * (P * Tᴴ * T * P) := by simp only [Matrix.mul_assoc]
    _ = P := hNK

private theorem flagAction_aux_NTN {ι : Type*} [Fintype ι] {T P N : Matrix ι ι ℂ}
    (hPN : P * N = N) (hK : N * Tᴴ * T * P = P) : N * Tᴴ * T * N = N := by
  calc N * Tᴴ * T * N = N * Tᴴ * T * (P * N) := by rw [hPN]
    _ = (N * Tᴴ * T * P) * N := by simp only [Matrix.mul_assoc]
    _ = N := by rw [hK, hPN]

/-- For invertible `T` and an orthogonal projection `P`, `flagProj T P` is an orthogonal
projection and fixes `T P`; it is the projection onto `T (ran P)`. -/
theorem flagProj_spec {ι : Type*} [Fintype ι] [DecidableEq ι] {T P : Matrix ι ι ℂ} (hT : IsUnit T)
    (hP : P.IsHermitian) (hPP : P * P = P) :
    (flagProj T P).IsHermitian ∧ flagProj T P * flagProj T P = flagProj T P ∧
      flagProj T P * (T * P) = T * P := by
  obtain ⟨N, hf, hNh, hPN, hNP, hNK⟩ := flagAction_aux hT hP.eq hPP
  have hK := flagAction_aux_K hNP hNK
  have hNTN := flagAction_aux_NTN hPN hK
  refine ⟨?_, ?_, ?_⟩
  · unfold Matrix.IsHermitian
    rw [hf, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hNh, Matrix.mul_assoc]
  · calc flagProj T P * flagProj T P = T * (N * Tᴴ * T * N) * Tᴴ := by
          rw [hf]; simp only [Matrix.mul_assoc]
      _ = flagProj T P := by rw [hNTN, hf]
  · calc flagProj T P * (T * P) = T * (N * Tᴴ * T * P) := by
          rw [hf]; simp only [Matrix.mul_assoc]
      _ = T * P := by rw [hK]

/-- For a unitary `T`, `flagProj T P = T P T*`. -/
theorem flagProj_of_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι] {T P : Matrix ι ι ℂ}
    (hT : T ∈ Matrix.unitaryGroup ι ℂ) (hPP : P * P = P) : flagProj T P = T * P * Tᴴ := by
  have h1 : Tᴴ * T = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hT
    rwa [Matrix.star_eq_conjTranspose] at this
  have hM : P * Tᴴ * T * P + (1 - P) = 1 := by
    calc P * Tᴴ * T * P + (1 - P) = P * (Tᴴ * T) * P + (1 - P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hPP]; abel
  unfold flagProj
  rw [hM, inv_one, Matrix.mul_one, Matrix.mul_assoc T P P, hPP]

private theorem flagAction_isUnit_of_isoJ {W : ℕ}
    {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hT : Tᴴ * isoJ W * T = isoJ W) :
    IsUnit T := by
  have h : isoJ W * Tᴴ * isoJ W * T = 1 := by
    calc isoJ W * Tᴴ * isoJ W * T = isoJ W * (Tᴴ * isoJ W * T) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hT, isoJ_mul_isoJ]
  exact (Matrix.isUnit_iff_isUnit_det T).mpr (Matrix.isUnit_det_of_left_inverse h)

private theorem flagAction_trace {ι : Type*} [Fintype ι] [DecidableEq ι] {T P : Matrix ι ι ℂ}
    (hT : IsUnit T) (hP : P.IsHermitian) (hPP : P * P = P) :
    (flagProj T P).trace = P.trace := by
  obtain ⟨N, hf, -, hPN, hNP, hNK⟩ := flagAction_aux hT hP.eq hPP
  have hK := flagAction_aux_K hNP hNK
  calc (flagProj T P).trace = (T * (N * Tᴴ)).trace := by rw [hf, Matrix.mul_assoc]
    _ = (N * Tᴴ * T).trace := Matrix.trace_mul_comm _ _
    _ = (P * (N * Tᴴ * T)).trace := by simp only [← Matrix.mul_assoc, hPN]
    _ = (N * Tᴴ * T * P).trace := Matrix.trace_mul_comm _ _
    _ = P.trace := by rw [hK]

private theorem flagAction_isotropic {W : ℕ} {T P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hTJ : Tᴴ * isoJ W * T = isoJ W) (hP : P.IsHermitian) (hPP : P * P = P)
    (hPJ : P * isoJ W * P = 0) : flagProj T P * isoJ W * flagProj T P = 0 := by
  obtain ⟨N, hf, -, hPN, hNP, -⟩ := flagAction_aux (flagAction_isUnit_of_isoJ hTJ) hP.eq hPP
  have hNJN : N * isoJ W * N = 0 := by
    calc N * isoJ W * N = (N * P) * isoJ W * (P * N) := by rw [hNP, hPN]
      _ = N * (P * isoJ W * P) * N := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hPJ, Matrix.mul_zero, Matrix.zero_mul]
  calc flagProj T P * isoJ W * flagProj T P
      = T * N * (Tᴴ * isoJ W * T) * N * Tᴴ := by rw [hf]; simp only [Matrix.mul_assoc]
    _ = T * (N * isoJ W * N) * Tᴴ := by rw [hTJ]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hNJN, Matrix.mul_zero, Matrix.zero_mul]

private theorem flagAction_nested {ι : Type*} [Fintype ι] [DecidableEq ι] {T PU PY : Matrix ι ι ℂ}
    (hT : IsUnit T) (hPU : PU.IsHermitian) (hUU : PU * PU = PU) (hPY : PY.IsHermitian)
    (hYY : PY * PY = PY) (hYU : PY * PU = PU) : flagProj T PY * flagProj T PU = flagProj T PU := by
  obtain ⟨N, hf, -, hPN, -, -⟩ := flagAction_aux hT hPU.eq hUU
  have hY := (flagProj_spec hT hPY hYY).2.2
  have hfU : flagProj T PU = (T * PY) * (PU * N * Tᴴ) := by
    calc flagProj T PU = T * (PY * PU * N) * Tᴴ := by rw [hf, hYU, hPN]
      _ = (T * PY) * (PU * N * Tᴴ) := by simp only [Matrix.mul_assoc]
  calc flagProj T PY * flagProj T PU
      = (flagProj T PY * (T * PY)) * (PU * N * Tᴴ) := by rw [hfU]; simp only [Matrix.mul_assoc]
    _ = flagProj T PU := by rw [hY, ← hfU]

/-- For `T* J T = J` the image of a flag is a flag: `flagAct T x = (TU, TY)`. -/
theorem flagAct_coe {W : ℕ} {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : Tᴴ * isoJ W * T = isoJ W) (x : IsoFlag W) :
    ((flagAct T x : IsoFlag W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) = (flagProj T x.1.1, flagProj T x.1.2) := by
  have hTu := flagAction_isUnit_of_isoJ hT
  obtain ⟨⟨hUh, hUU, hUtr, hUJ⟩, hYh, hYY, hYtr, hYU, hYJ⟩ := x.2
  have hU := flagProj_spec hTu hUh hUU
  have hY := flagProj_spec hTu hYh hYY
  have hmem : (flagProj T x.1.1, flagProj T x.1.2) ∈ isoFlags W :=
    ⟨⟨hU.1, hU.2.1, by rw [flagAction_trace hTu hUh hUU, hUtr],
      flagAction_isotropic hT hUh hUU hUJ⟩, hY.1, hY.2.1,
      by rw [flagAction_trace hTu hYh hYY, hYtr], flagAction_nested hTu hUh hUU hYh hYY hYU,
      flagAction_isotropic hT hYh hYY hYJ⟩
  unfold flagAct
  simp only [hmem, ↓reduceDIte]

private theorem flagAction_eq_of_fixed {ι : Type*} [Fintype ι] {A B K Z Z' : Matrix ι ι ℂ}
    (hA : Aᴴ = A) (hB : Bᴴ = B) (hAK : A * K = K) (hBK : B * K = K) (hAZ : A = K * Z)
    (hBZ : B = K * Z') : A = B := by
  have h1 : A * B = B := by
    calc A * B = (A * K) * Z' := by rw [hBZ, Matrix.mul_assoc]
      _ = B := by rw [hAK, ← hBZ]
  have h2 : B * A = A := by
    calc B * A = (B * K) * Z := by rw [hAZ, Matrix.mul_assoc]
      _ = A := by rw [hBK, ← hAZ]
  calc A = B * A := h2.symm
    _ = (A * B)ᴴ := by rw [Matrix.conjTranspose_mul, hA, hB]
    _ = B := by rw [h1, hB]

private theorem flagAction_flagProj_eq_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T P : Matrix ι ι ℂ) :
    ∃ Z : Matrix ι ι ℂ, flagProj T P = T * P * Z :=
  ⟨(P * Tᴴ * T * P + (1 - P))⁻¹ * P * Tᴴ, by unfold flagProj; simp only [Matrix.mul_assoc]⟩

private theorem flagAction_comp {ι : Type*} [Fintype ι] [DecidableEq ι] {T₁ T₂ P : Matrix ι ι ℂ}
    (h₁ : IsUnit T₁) (h₂ : IsUnit T₂) (hP : P.IsHermitian) (hPP : P * P = P) :
    flagProj (T₂ * T₁) P = flagProj T₂ (flagProj T₁ P) := by
  obtain ⟨hH₁, hI₁, hF₁⟩ := flagProj_spec h₁ hP hPP
  obtain ⟨hH', -, hF'⟩ := flagProj_spec h₂ hH₁ hI₁
  obtain ⟨hH, -, hF⟩ := flagProj_spec (h₂.mul h₁) hP hPP
  obtain ⟨X₁, hX₁⟩ := flagAction_flagProj_eq_mul T₁ P
  obtain ⟨Z₂, hZ₂⟩ := flagAction_flagProj_eq_mul T₂ (flagProj T₁ P)
  obtain ⟨Z, hZ⟩ := flagAction_flagProj_eq_mul (T₂ * T₁) P
  refine flagAction_eq_of_fixed (K := T₂ * T₁ * P) (Z := Z) (Z' := X₁ * Z₂) hH.eq hH'.eq hF ?_ hZ
    ?_
  · have e : T₂ * T₁ * P = T₂ * flagProj T₁ P * (T₁ * P) := by
      rw [Matrix.mul_assoc T₂ (flagProj T₁ P), hF₁, ← Matrix.mul_assoc]
    calc flagProj T₂ (flagProj T₁ P) * (T₂ * T₁ * P)
        = flagProj T₂ (flagProj T₁ P) * (T₂ * flagProj T₁ P * (T₁ * P)) := by rw [← e]
      _ = (flagProj T₂ (flagProj T₁ P) * (T₂ * flagProj T₁ P)) * (T₁ * P) := by
          simp only [Matrix.mul_assoc]
      _ = T₂ * T₁ * P := by rw [hF', ← e]
  · calc flagProj T₂ (flagProj T₁ P) = T₂ * (T₁ * P * X₁) * Z₂ := by rw [hZ₂, hX₁]
      _ = T₂ * T₁ * P * (X₁ * Z₂) := by simp only [Matrix.mul_assoc]

private theorem flagAction_isoJ_mul {W : ℕ} {T₁ T₂ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (h₁ : T₁ᴴ * isoJ W * T₁ = isoJ W) (h₂ : T₂ᴴ * isoJ W * T₂ = isoJ W) :
    (T₂ * T₁)ᴴ * isoJ W * (T₂ * T₁) = isoJ W := by
  calc (T₂ * T₁)ᴴ * isoJ W * (T₂ * T₁) = T₁ᴴ * (T₂ᴴ * isoJ W * T₂) * T₁ := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = isoJ W := by rw [h₂, h₁]

/-- The action is multiplicative on `J`-unitary matrices. -/
theorem flagAct_mul {W : ℕ} {T₁ T₂ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (h₁ : T₁ᴴ * isoJ W * T₁ = isoJ W) (h₂ : T₂ᴴ * isoJ W * T₂ = isoJ W) (x : IsoFlag W) :
    flagAct (T₂ * T₁) x = flagAct T₂ (flagAct T₁ x) := by
  have h₂₁ := flagAction_isoJ_mul h₁ h₂
  have hT₁ := flagAction_isUnit_of_isoJ h₁
  have hT₂ := flagAction_isUnit_of_isoJ h₂
  obtain ⟨⟨hUh, hUU, -, -⟩, hYh, hYY, -⟩ := x.2
  have c₁ := flagAct_coe h₁ x
  apply Subtype.ext
  rw [flagAct_coe h₂₁ x, flagAct_coe h₂ (flagAct T₁ x), c₁]
  exact Prod.ext (flagAction_comp hT₁ hT₂ hUh hUU) (flagAction_comp hT₁ hT₂ hYh hYY)

private theorem flagAction_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
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

private theorem flagAction_measurable_mul {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι]
    {f g : α → Matrix ι ι ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x * g x :=
  (continuous_fst.matrix_mul continuous_snd :
    Continuous fun q : Matrix ι ι ℂ × Matrix ι ι ℂ => q.1 * q.2).measurable.comp (hf.prodMk hg)

private theorem flagAction_measurable_flagProj {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable fun p : Matrix ι ι ℂ × Matrix ι ι ℂ => flagProj p.1 p.2 := by
  have hT : Measurable fun p : Matrix ι ι ℂ × Matrix ι ι ℂ => p.1 := measurable_fst
  have hP : Measurable fun p : Matrix ι ι ℂ × Matrix ι ι ℂ => p.2 := measurable_snd
  have hTH : Measurable fun p : Matrix ι ι ℂ × Matrix ι ι ℂ => p.1ᴴ :=
    (continuous_fst.matrix_conjTranspose).measurable
  have hM : Measurable fun p : Matrix ι ι ℂ × Matrix ι ι ℂ =>
      (p.2 * p.1ᴴ * p.1 * p.2 + (1 - p.2))⁻¹ := by
    have : Continuous fun p : Matrix ι ι ℂ × Matrix ι ι ℂ =>
        p.2 * p.1ᴴ * p.1 * p.2 + (1 - p.2) := by
      fun_prop
    exact flagAction_measurable_inv.comp this.measurable
  exact flagAction_measurable_mul (flagAction_measurable_mul (flagAction_measurable_mul
    (flagAction_measurable_mul hT hP) hM) hP) hTH

private theorem flagAction_isClosed_isoFlags (W : ℕ) : IsClosed (isoFlags W) := by
  have hc : ∀ f g : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      Continuous f → Continuous g → IsClosed {x | f x = g x} :=
    fun f g hf hg => isClosed_eq hf hg
  have ht : ∀ (f : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℂ) (c : ℂ), Continuous f →
      IsClosed {x | f x = c} := fun f c hf => isClosed_eq hf continuous_const
  change IsClosed {x : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ | (x.1.IsHermitian ∧ x.1 * x.1 = x.1 ∧
      x.1.trace = ((W - 1 : ℕ) : ℂ) ∧ x.1 * isoJ W * x.1 = 0) ∧ x.2.IsHermitian ∧ x.2 * x.2 = x.2 ∧
      x.2.trace = (W : ℂ) ∧ x.2 * x.1 = x.1 ∧ x.2 * isoJ W * x.2 = 0}
  simp only [Set.ofPred_and]
  refine IsClosed.inter (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))
    (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))))
  · exact hc (fun a => a.1ᴴ) (fun a => a.1) (by fun_prop) (by fun_prop)
  · exact hc (fun a => a.1 * a.1) (fun a => a.1) (by fun_prop) (by fun_prop)
  · exact ht (fun a => a.1.trace) _ (by fun_prop)
  · exact hc (fun a => a.1 * isoJ W * a.1) (fun _ => 0) (by fun_prop) (by fun_prop)
  · exact hc (fun a => a.2ᴴ) (fun a => a.2) (by fun_prop) (by fun_prop)
  · exact hc (fun a => a.2 * a.2) (fun a => a.2) (by fun_prop) (by fun_prop)
  · exact ht (fun a => a.2.trace) _ (by fun_prop)
  · exact hc (fun a => a.2 * a.1) (fun a => a.1) (by fun_prop) (by fun_prop)
  · exact hc (fun a => a.2 * isoJ W * a.2) (fun _ => 0) (by fun_prop) (by fun_prop)

/-- The action is jointly measurable in `(T, U, Y)`. -/
theorem measurable_flagAct (W : ℕ) :
    Measurable fun p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × IsoFlag W => flagAct p.1 p.2 := by
  let G : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × IsoFlag W →
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
    fun p => (flagProj p.1 p.2.1.1, flagProj p.1 p.2.1.2)
  have hGm : Measurable G := by
    have h1 : Measurable fun p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × IsoFlag W =>
        (p.1, p.2.1.1) :=
      measurable_fst.prodMk (measurable_fst.comp (measurable_subtype_coe.comp measurable_snd))
    have h2 : Measurable fun p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × IsoFlag W =>
        (p.1, p.2.1.2) :=
      measurable_fst.prodMk (measurable_snd.comp (measurable_subtype_coe.comp measurable_snd))
    have h3 := flagAction_measurable_flagProj.comp h1
    have h4 := flagAction_measurable_flagProj.comp h2
    exact h3.prodMk h4
  have hS : MeasurableSet {p | G p ∈ isoFlags W} :=
    hGm (flagAction_isClosed_isoFlags W).measurableSet
  have hval : Measurable fun p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × IsoFlag W =>
      ((flagAct p.1 p.2 : IsoFlag W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) := by
    have : (fun p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × IsoFlag W =>
        ((flagAct p.1 p.2 : IsoFlag W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
          Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) =
        fun p => if G p ∈ isoFlags W then G p else (p.2 : Matrix (Fin 2 × Fin W)
          (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) := by
      funext p
      unfold flagAct
      dsimp only [G]
      by_cases h : (flagProj p.1 p.2.1.1, flagProj p.1 p.2.1.2) ∈ isoFlags W
      · simp only [h, ↓reduceDIte, ↓reduceIte]
      · simp only [h, ↓reduceDIte, ↓reduceIte]
    rw [this]
    exact Measurable.ite hS hGm (measurable_subtype_coe.comp measurable_snd)
  exact (MeasurableEmbedding.subtype_coe (flagAction_isClosed_isoFlags W).measurableSet
    ).measurable_comp_iff.mp hval

end LSBA
