import LSBA.Analysis.FlagDerivative

/-!
# Image projections moving by a rotation

For a matrix function `T` with line derivative `D` at `ω` along `v`, `T(ω)` invertible, an
orthogonal projection `P` and a skew-Hermitian `A`: if `(D - A T(ω)) P = T(ω) P M` for some `M`,
that is, `D = A T(ω) + T(ω) N` with `N` leaving `ran P` invariant, then the image projection
`Π = flagProj (T ω) P` has line derivative `[A, Π]` and `log vol(T|_{ran P})` has line derivative
`Re Tr(P M)`. This is the first-order motion of the terminal flag in (8.34)
[up:eq:angular-geometry] and (9.11) [su:eq:field-geometry], a common unitary rotation `e^{tA}`
composed with a motion inside the incoming subspaces.
-/

open Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- If `(D - A T(ω)) P = T(ω) P M` with `A* = -A`, the image projection `Π = flagProj (T ω) P`
has line derivative `A Π - Π A` and the log-volume has line derivative `Re Tr(P M)`. -/
theorem hasLineDerivAt_flagProj_logVol_of_rot {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι] {T : E → Matrix ι ι ℂ} {D A M : Matrix ι ι ℂ}
    {ω v : E} (hT : HasLineDerivAt ℝ T D ω v) (hu : IsUnit (T ω)) (hA : Aᴴ = -A)
    {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (hM : (D - A * T ω) * P = T ω * P * M) :
    HasLineDerivAt ℝ (fun η => flagProj (T η) P)
        (A * flagProj (T ω) P - flagProj (T ω) P * A) ω v ∧
      HasLineDerivAt ℝ (fun η => logVol (T η) P) (P * M).trace.re ω v := by
  have hP' : Pᴴ = P := hP
  obtain ⟨hQh, hQQ, hQT⟩ := flagProj_spec hu hP hPP
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hTiT : (T ω)⁻¹ * T ω = 1 := Matrix.nonsing_inv_mul _ hdet
  have hTH : (T ω)ᴴ * ((T ω)⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hTiT, Matrix.conjTranspose_one]
  have hTiT' : ∀ X : Matrix ι ι ℂ, (T ω)⁻¹ * (T ω * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hTiT, Matrix.one_mul]
  have hTH' : ∀ X : Matrix ι ι ℂ, (T ω)ᴴ * (((T ω)⁻¹)ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hTH, Matrix.one_mul]
  have hQ : flagProj (T ω) P =
      T ω * P * (P * (T ω)ᴴ * T ω * P + (1 - P))⁻¹ * P * (T ω)ᴴ := rfl
  set G := P * (T ω)ᴴ * T ω * P + (1 - P) with hGdef
  set Q := flagProj (T ω) P with hQdef
  have hGd : IsUnit G.det := by
    by_contra hn
    have h0 : G⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hn
    have hQ0 : Q = 0 := by
      rw [hQ, h0]
      simp only [Matrix.mul_zero, Matrix.zero_mul]
    have hTP : T ω * P = 0 := by rw [← hQT, hQ0, Matrix.zero_mul]
    have hP0 : P = 0 := by
      calc P = (T ω)⁻¹ * (T ω * P) := (hTiT' P).symm
        _ = 0 := by rw [hTP, Matrix.mul_zero]
    apply hn
    have hG1 : G = 1 := by
      rw [hGdef, hP0]
      simp
    rw [hG1, Matrix.det_one]
    exact isUnit_one
  have hGP : G * P = P * (T ω)ᴴ * T ω * P := by
    rw [hGdef]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hPP]
    abel
  have hGiG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hGd
  have hA1 : G⁻¹ * (P * (T ω)ᴴ * T ω * P) = P := by
    rw [← hGP, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
  have hk1 : (1 - Q) * (T ω * P) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hQT, sub_self]
  have hk2 : P * (T ω)ᴴ * (1 - Q) = 0 := by
    have := congrArg Matrix.conjTranspose hk1
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      hQh.eq, hP', Matrix.conjTranspose_zero, Matrix.mul_assoc] using this
  have hDP : D * P = T ω * P * M + A * (T ω * P) := by
    have := hM
    rw [Matrix.sub_mul, sub_eq_iff_eq_add] at this
    rw [this]
    simp only [Matrix.mul_assoc]
  have hPDH : P * Dᴴ = -(P * (T ω)ᴴ * A) + Mᴴ * (P * (T ω)ᴴ) := by
    have := congrArg Matrix.conjTranspose hDP
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_add, hP', hA, Matrix.mul_neg,
      Matrix.mul_assoc] at this ⊢
    rw [this, add_comm]
  have hTiQ : (T ω)⁻¹ * Q = P * G⁻¹ * P * (T ω)ᴴ := by
    rw [hQ]; simp only [Matrix.mul_assoc, hTiT']
  have hQTi : Q * ((T ω)⁻¹)ᴴ = T ω * P * G⁻¹ * P := by
    rw [hQ]; simp only [Matrix.mul_assoc]; rw [hTH, Matrix.mul_one]
  have hDTiQ : D * (T ω)⁻¹ * Q = A * Q + T ω * P * M * G⁻¹ * P * (T ω)ᴴ := by
    calc D * (T ω)⁻¹ * Q = (D * P) * G⁻¹ * P * (T ω)ᴴ := by
          rw [Matrix.mul_assoc, hTiQ]; simp only [Matrix.mul_assoc]
      _ = A * Q + T ω * P * M * G⁻¹ * P * (T ω)ᴴ := by
          rw [hDP, hQ]; simp only [Matrix.add_mul, Matrix.mul_assoc]; abel
  constructor
  · have h1 : (1 - Q) * D * (T ω)⁻¹ * Q = (1 - Q) * A * Q := by
      calc (1 - Q) * D * (T ω)⁻¹ * Q = (1 - Q) * (D * (T ω)⁻¹ * Q) := by
            simp only [Matrix.mul_assoc]
        _ = (1 - Q) * (A * Q) + ((1 - Q) * (T ω * P)) * (M * G⁻¹ * P * (T ω)ᴴ) := by
            rw [hDTiQ, Matrix.mul_add]; simp only [Matrix.mul_assoc]
        _ = (1 - Q) * A * Q := by
            rw [hk1, Matrix.zero_mul, add_zero, Matrix.mul_assoc]
    have h2 : Q * ((T ω)⁻¹)ᴴ * Dᴴ * (1 - Q) = -(Q * A * (1 - Q)) := by
      calc Q * ((T ω)⁻¹)ᴴ * Dᴴ * (1 - Q) = T ω * P * G⁻¹ * (P * Dᴴ * (1 - Q)) := by
            rw [hQTi]; simp only [Matrix.mul_assoc]
        _ = T ω * P * G⁻¹ * (-(P * (T ω)ᴴ * A * (1 - Q)) +
              Mᴴ * (P * (T ω)ᴴ * (1 - Q))) := by
            rw [hPDH, Matrix.add_mul, Matrix.neg_mul]; simp only [Matrix.mul_assoc]
        _ = -(Q * A * (1 - Q)) := by
            rw [hk2, Matrix.mul_zero, add_zero, hQ]
            simp only [Matrix.mul_neg, Matrix.mul_assoc]
    convert hasLineDerivAt_flagProj hT hu hP hPP using 1
    rw [h1, h2]
    have hQ1 : Q * (1 - Q) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hQQ, sub_self]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  · have hAQ : (A * Q).trace.re = 0 := by
      have h' : ((A * Q)ᴴ).trace = -((A * Q).trace) := by
        rw [Matrix.conjTranspose_mul, hQh.eq, hA, Matrix.mul_neg, Matrix.trace_neg,
          Matrix.trace_mul_comm]
      rw [Matrix.trace_conjTranspose] at h'
      have := congrArg Complex.re h'
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
      linarith
    have hMP : (T ω * P * M * G⁻¹ * P * (T ω)ᴴ).trace = (P * M).trace := by
      calc (T ω * P * M * G⁻¹ * P * (T ω)ᴴ).trace
          = (T ω * (P * (M * G⁻¹ * P * (T ω)ᴴ))).trace := by simp only [Matrix.mul_assoc]
        _ = ((P * (M * G⁻¹ * P * (T ω)ᴴ)) * T ω).trace := Matrix.trace_mul_comm _ _
        _ = (P * (M * G⁻¹ * P * (T ω)ᴴ * T ω)).trace := by simp only [Matrix.mul_assoc]
        _ = ((M * G⁻¹ * P * (T ω)ᴴ * T ω) * P).trace := Matrix.trace_mul_comm _ _
        _ = (M * (G⁻¹ * (P * (T ω)ᴴ * T ω * P))).trace := by simp only [Matrix.mul_assoc]
        _ = (M * P).trace := by rw [hA1]
        _ = (P * M).trace := Matrix.trace_mul_comm _ _
    have e1 : (Q * (A * Q)).trace = (A * Q).trace := by
      rw [Matrix.trace_mul_comm, Matrix.mul_assoc, hQQ]
    have e2 : Q * (T ω * P * M * G⁻¹ * P * (T ω)ᴴ) = T ω * P * M * G⁻¹ * P * (T ω)ᴴ := by
      calc Q * (T ω * P * M * G⁻¹ * P * (T ω)ᴴ)
          = (Q * (T ω * P)) * M * G⁻¹ * P * (T ω)ᴴ := by simp only [Matrix.mul_assoc]
        _ = T ω * P * M * G⁻¹ * P * (T ω)ᴴ := by rw [hQT]
    have htr : (Q * D * (T ω)⁻¹).trace = (A * Q).trace + (P * M).trace := by
      calc (Q * D * (T ω)⁻¹).trace = (Q * (Q * D * (T ω)⁻¹)).trace := by
            rw [show Q * (Q * D * (T ω)⁻¹) = Q * Q * D * (T ω)⁻¹ by simp only [Matrix.mul_assoc],
              hQQ]
        _ = (Q * D * (T ω)⁻¹ * Q).trace := Matrix.trace_mul_comm _ _
        _ = (Q * (D * (T ω)⁻¹ * Q)).trace := by simp only [Matrix.mul_assoc]
        _ = (Q * (A * Q + T ω * P * M * G⁻¹ * P * (T ω)ᴴ)).trace := by rw [hDTiQ]
        _ = (A * Q).trace + (P * M).trace := by
            rw [Matrix.mul_add, Matrix.trace_add, e1, e2, hMP]
    convert hasLineDerivAt_logVol hT hu hP hPP using 1
    rw [htr, Complex.add_re, hAQ, zero_add]

end LSBA
