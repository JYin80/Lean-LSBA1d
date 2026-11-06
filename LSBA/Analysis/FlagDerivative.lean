import LSBA.Transfer.VolCocycle

/-!
# Derivatives of image projections and of log-volumes

For a matrix function `T` with line derivative `D` at `ω` along `v`, `T(ω)` invertible and an
orthogonal projection `P`, the image projection `Π = flagProj (T ω) P` onto `T(ω) ran P` and
the log-volume `log vol(T|_{ran P})` have line derivatives
`(1 - Π) D T⁻¹ Π + Π T^{-*} D* (1 - Π)` and `Re Tr(Π D T⁻¹)`. If `D = T(ω) N` with `N` leaving
`ran P` invariant (`N P = P N P`), the projection does not move and the log-volume has
derivative `Re Tr(P N)`. This is the motion of the terminal flag and of the cocycle in (8.34)
[up:eq:angular-geometry] (proof of Lemma 8.13 [up:lem:density-contraction]).
-/

open Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

open scoped ComplexOrder in
/-- The Gram matrix `P T* T P + 1 - P` of an invertible `T` and an orthogonal projection `P` is
invertible. -/
private theorem flagDerivative_isUnit_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T P : Matrix ι ι ℂ} (hT : IsUnit T) (hP : Pᴴ = P) (hPP : P * P = P) :
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

/-- An entry of a differentiable matrix curve is differentiable. -/
private theorem flagDerivative_hasDerivAt_entry {ι : Type*} [Finite ι]
    {c : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} {x : ℝ} (h : HasDerivAt c D x) (i j : ι) :
    HasDerivAt (fun t => c t i j) (D i j) x := by
  have := Fintype.ofFinite ι
  let L : Matrix ι ι ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun A => A i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt x h

/-- Jacobi's formula along a curve: `d det c = Tr(adj(c) c')`. -/
private theorem flagDerivative_hasDerivAt_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} {x : ℝ} (h : HasDerivAt c D x) :
    HasDerivAt (fun t => (c t).det) ((c x).adjugate * D).trace x := by
  have hs : HasDerivAt
      (fun t => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, c t (σ i) i)
      (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, c x (σ j) j) • D (σ i) i) x := by
    refine HasDerivAt.fun_sum fun σ _ => ?_
    refine HasDerivAt.const_mul _ ?_
    exact HasDerivAt.fun_finsetProd fun i _ => flagDerivative_hasDerivAt_entry h (σ i) i
  have key : ∀ (i : ι) (σ : Equiv.Perm ι),
      ∏ j, ((c x).updateCol i (fun k => D k i)) (σ j) j =
        (∏ j ∈ Finset.univ.erase i, c x (σ j) j) * D (σ i) i := by
    intro i σ
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    congr 1
    · refine Finset.prod_congr rfl fun j hj => ?_
      rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)]
    · rw [Matrix.updateCol_self]
  convert hs using 1
  · funext t
    rw [Matrix.det_apply]
    simp only [Units.smul_def, zsmul_eq_mul]
  · calc ((c x).adjugate * D).trace = ∑ i, ((c x).updateCol i (fun k => D k i)).det := by
          simp only [Matrix.trace, Matrix.diag, ← Matrix.cramer_apply,
            Matrix.cramer_eq_adjugate_mulVec, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      _ = _ := by
          simp only [Matrix.det_apply, key, Units.smul_def, zsmul_eq_mul, smul_eq_mul,
            Finset.mul_sum]
          exact Finset.sum_comm

/-- `d log ‖f‖ = Re(f' / f)` at a point where `f ≠ 0`. -/
private theorem flagDerivative_hasDerivAt_logNorm {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (h : HasDerivAt f f' x) (h0 : f x ≠ 0) :
    HasDerivAt (fun t => Real.log ‖f t‖) (f' / f x).re x := by
  have hre : HasDerivAt (fun t => (f t).re) f'.re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  have him : HasDerivAt (fun t => (f t).im) f'.im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h
  have hn : HasDerivAt (fun t => (f t).re * (f t).re + (f t).im * (f t).im)
      (f'.re * (f x).re + (f x).re * f'.re + (f'.im * (f x).im + (f x).im * f'.im)) x :=
    (hre.mul hre).add (him.mul him)
  have hpos : (f x).re * (f x).re + (f x).im * (f x).im ≠ 0 := by
    rw [← Complex.normSq_apply]; exact (Complex.normSq_pos.mpr h0).ne'
  have hl := (hn.log hpos).div_const 2
  convert hl using 1
  · funext t
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, Real.log_pow]
    push_cast; ring
  · rw [Complex.div_re, Complex.normSq_apply]
    field_simp
    ring

/-- The inverse along a curve through a unit: `d c⁻¹ = -c⁻¹ c' c⁻¹`. -/
private theorem flagDerivative_hasDerivAt_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : ℝ → Matrix ι ι ℂ} {G' : Matrix ι ι ℂ} {x : ℝ} (h : HasDerivAt G G' x)
    (hu : IsUnit (G x)) :
    HasDerivAt (fun t => (G t)⁻¹) (-((G x)⁻¹ * G' * (G x)⁻¹)) x := by
  obtain ⟨u, hux⟩ := hu
  have hf := (hasFDerivAt_ringInverse (𝕜 := ℂ) u).restrictScalars ℝ
  rw [hux] at hf
  have hc := hf.comp_hasDerivAt x h
  simp only [Matrix.nonsing_inv_eq_ringInverse]
  convert hc using 1
  · rfl
  · rw [← hux, Ring.inverse_unit]
    simp

/-- The Gram matrix along a curve: `d(P c* c P + 1 - P) = P c'* c P + P c* c' P`. -/
private theorem flagDerivative_hasDerivAt_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : ℝ → Matrix ι ι ℂ} {D P : Matrix ι ι ℂ} {x : ℝ} (h : HasDerivAt c D x) :
    HasDerivAt (fun t => P * (c t)ᴴ * c t * P + (1 - P))
      (P * Dᴴ * c x * P + P * (c x)ᴴ * D * P) x := by
  have hs : HasDerivAt (fun t => (c t)ᴴ) Dᴴ x := h.star
  have := (((hs.const_mul P).mul h).mul_const P).add_const (1 - P)
  convert this using 1
  noncomm_ring

/-- The image projection along a curve `c` through `c(0) = T₀`: its derivative is
`(1 - Π) D T₀⁻¹ Π + Π T₀^{-*} D* (1 - Π)`, `Π = flagProj T₀ P`. -/
private theorem flagDerivative_flagProj_curve {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : ℝ → Matrix ι ι ℂ} {D T₀ P : Matrix ι ι ℂ} (hc : HasDerivAt c D 0) (h0 : c 0 = T₀)
    (hu : IsUnit T₀) (hP : Pᴴ = P) (hPP : P * P = P) :
    HasDerivAt (fun t => flagProj (c t) P)
      ((1 - flagProj T₀ P) * D * T₀⁻¹ * flagProj T₀ P +
        flagProj T₀ P * (T₀⁻¹)ᴴ * Dᴴ * (1 - flagProj T₀ P)) 0 := by
  have hG := flagDerivative_hasDerivAt_gram (P := P) hc
  have hGu := flagDerivative_isUnit_gram hu hP hPP
  have hGi := flagDerivative_hasDerivAt_inv hG (by simpa only [h0] using hGu)
  have hF := (((hc.mul_const P).mul hGi).mul_const P).mul hc.star
  convert hF using 1
  · rfl
  simp only [h0, Pi.mul_apply, Matrix.star_eq_conjTranspose]
  have hTiT : T₀⁻¹ * T₀ = 1 :=
    Matrix.nonsing_inv_mul T₀ ((Matrix.isUnit_iff_isUnit_det T₀).mp hu)
  have hTH : T₀ᴴ * (T₀⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hTiT, Matrix.conjTranspose_one]
  have hTiT' : ∀ X : Matrix ι ι ℂ, T₀⁻¹ * (T₀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hTiT, Matrix.one_mul]
  have hTH' : ∀ X : Matrix ι ι ℂ, T₀ᴴ * ((T₀⁻¹)ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hTH, Matrix.one_mul]
  unfold flagProj
  set Gi := (P * T₀ᴴ * T₀ * P + (1 - P))⁻¹
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hTiT', hTH]
  abel

/-- The log-volume along a curve `c` through `c(0) = T₀`: its derivative is
`Re Tr(Π D T₀⁻¹)`, `Π = flagProj T₀ P`. -/
private theorem flagDerivative_logVol_curve {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : ℝ → Matrix ι ι ℂ} {D T₀ P : Matrix ι ι ℂ} (hc : HasDerivAt c D 0) (h0 : c 0 = T₀)
    (hu : IsUnit T₀) (hP : Pᴴ = P) (hPP : P * P = P) :
    HasDerivAt (fun t => logVol (c t) P) (flagProj T₀ P * D * T₀⁻¹).trace.re 0 := by
  have hG := flagDerivative_hasDerivAt_gram (P := P) hc
  have hGu := flagDerivative_isUnit_gram hu hP hPP
  have hdu : IsUnit (P * T₀ᴴ * T₀ * P + (1 - P)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hGu
  have hdet := flagDerivative_hasDerivAt_det hG
  have hl := (flagDerivative_hasDerivAt_logNorm hdet
    (by simpa only [h0] using hdu.ne_zero)).div_const 2
  convert hl using 1
  · rfl
  simp only [h0]
  set G := P * T₀ᴴ * T₀ * P + (1 - P) with hGdef
  have hGH : Gᴴ = G := by
    rw [hGdef, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hP]
    simp only [Matrix.mul_assoc]
  have hGiH : (G⁻¹)ᴴ = G⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hGH]
  have hTiT : T₀⁻¹ * T₀ = 1 :=
    Matrix.nonsing_inv_mul T₀ ((Matrix.isUnit_iff_isUnit_det T₀).mp hu)
  have hadj : (G.adjugate * (P * Dᴴ * T₀ * P + P * T₀ᴴ * D * P)).trace / G.det =
      (G⁻¹ * (P * Dᴴ * T₀ * P)).trace + (G⁻¹ * (P * T₀ᴴ * D * P)).trace := by
    rw [← Matrix.trace_add, ← Matrix.mul_add, Matrix.inv_def, Matrix.smul_mul, Matrix.trace_smul,
      Ring.inverse_eq_inv', smul_eq_mul, div_eq_inv_mul]
  have h1 : (G⁻¹ * (P * T₀ᴴ * D * P)).trace = (flagProj T₀ P * D * T₀⁻¹).trace := by
    calc (G⁻¹ * (P * T₀ᴴ * D * P)).trace = (P * (G⁻¹ * P * T₀ᴴ * D)).trace := by
          rw [Matrix.trace_mul_comm P]; simp only [Matrix.mul_assoc]
      _ = (T₀⁻¹ * (T₀ * P * G⁻¹ * P * T₀ᴴ * D)).trace := by
          simp only [← Matrix.mul_assoc, hTiT, Matrix.one_mul]
      _ = (flagProj T₀ P * D * T₀⁻¹).trace := by
          rw [Matrix.trace_mul_comm]; unfold flagProj; rw [← hGdef]
  have h2 : (G⁻¹ * (P * Dᴴ * T₀ * P)).trace = star (G⁻¹ * (P * T₀ᴴ * D * P)).trace := by
    rw [Matrix.trace_mul_comm G⁻¹ (P * T₀ᴴ * D * P), ← Matrix.trace_conjTranspose]
    congr 1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP, hGiH,
      Matrix.mul_assoc]
  rw [hadj, h2, h1, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

/-- The line derivative of the image projection `Π = flagProj (T ω) P`:
`(1 - Π) D T⁻¹ Π + Π T^{-*} D* (1 - Π)`. -/
theorem hasLineDerivAt_flagProj {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] {T : E → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} {ω v : E}
    (hT : HasLineDerivAt ℝ T D ω v) (hu : IsUnit (T ω)) {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) :
    HasLineDerivAt ℝ (fun η => flagProj (T η) P)
      ((1 - flagProj (T ω) P) * D * (T ω)⁻¹ * flagProj (T ω) P +
        flagProj (T ω) P * ((T ω)⁻¹)ᴴ * Dᴴ * (1 - flagProj (T ω) P)) ω v := by
  unfold HasLineDerivAt at hT ⊢
  exact flagDerivative_flagProj_curve hT (by simp) hu hP hPP

/-- The line derivative of `log vol(T|_{ran P})` is `Re Tr(Π D T⁻¹)`, `Π = flagProj (T ω) P`. -/
theorem hasLineDerivAt_logVol {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] {T : E → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} {ω v : E}
    (hT : HasLineDerivAt ℝ T D ω v) (hu : IsUnit (T ω)) {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) :
    HasLineDerivAt ℝ (fun η => logVol (T η) P) (flagProj (T ω) P * D * (T ω)⁻¹).trace.re ω v := by
  unfold HasLineDerivAt at hT ⊢
  exact flagDerivative_logVol_curve hT (by simp) hu hP hPP

/-- For `D = T(ω) N` with `N P = P N P`: the image projection has line derivative `0` and the
log-volume has line derivative `Re Tr(P N)`. -/
theorem hasLineDerivAt_flagProj_logVol_of_mul {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι] {T : E → Matrix ι ι ℂ} {N : Matrix ι ι ℂ}
    {ω v : E} (hT : HasLineDerivAt ℝ T (T ω * N) ω v) (hu : IsUnit (T ω)) {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hN : N * P = P * N * P) :
    HasLineDerivAt ℝ (fun η => flagProj (T η) P) 0 ω v ∧
      HasLineDerivAt ℝ (fun η => logVol (T η) P) (P * N).trace.re ω v := by
  have hP' : Pᴴ = P := hP
  have hTiT : (T ω)⁻¹ * T ω = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hTH : (T ω)ᴴ * ((T ω)⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hTiT, Matrix.conjTranspose_one]
  have hTiT' : ∀ X : Matrix ι ι ℂ, (T ω)⁻¹ * (T ω * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hTiT, Matrix.one_mul]
  have hTH' : ∀ X : Matrix ι ι ℂ, (T ω)ᴴ * (((T ω)⁻¹)ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hTH, Matrix.one_mul]
  have hGd := (Matrix.isUnit_iff_isUnit_det _).mp (flagDerivative_isUnit_gram hu hP' hPP)
  have hQ : flagProj (T ω) P =
      T ω * P * (P * (T ω)ᴴ * T ω * P + (1 - P))⁻¹ * P * (T ω)ᴴ := rfl
  set G := P * (T ω)ᴴ * T ω * P + (1 - P) with hGdef
  set Q := flagProj (T ω) P with hQdef
  have hGP : G * P = P * (T ω)ᴴ * T ω * P := by
    rw [hGdef]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hPP]
    abel
  have hPG : P * G = P * (T ω)ᴴ * T ω * P := by
    rw [hGdef]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPP]
    abel
  have hA : G⁻¹ * (P * (T ω)ᴴ * T ω * P) = P := by
    rw [← hGP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hGd, Matrix.one_mul]
  have hB : P * (T ω)ᴴ * T ω * P * G⁻¹ = P := by
    rw [← hPG, Matrix.mul_assoc, Matrix.mul_nonsing_inv G hGd, Matrix.mul_one]
  constructor
  · have hNH : P * Nᴴ = P * Nᴴ * P := by
      have := congrArg Matrix.conjTranspose hN
      simpa only [Matrix.conjTranspose_mul, hP', Matrix.mul_assoc] using this
    have hk1 : (1 - Q) * (T ω * P) = 0 := by
      have e : T ω * P * G⁻¹ * P * (T ω)ᴴ * (T ω * P) =
          T ω * P * (G⁻¹ * (P * (T ω)ᴴ * T ω * P)) := by
        simp only [Matrix.mul_assoc]
      rw [Matrix.sub_mul, Matrix.one_mul, hQ, e, hA, Matrix.mul_assoc, hPP, sub_self]
    have hk2 : P * (T ω)ᴴ * (1 - Q) = 0 := by
      have e : P * (T ω)ᴴ * (T ω * P * G⁻¹ * P * (T ω)ᴴ) =
          P * (T ω)ᴴ * T ω * P * G⁻¹ * (P * (T ω)ᴴ) := by
        simp only [Matrix.mul_assoc]
      rw [Matrix.mul_sub, Matrix.mul_one, hQ, e, hB, ← Matrix.mul_assoc, hPP, sub_self]
    have e1 : ∀ A : Matrix ι ι ℂ, A * (T ω * N) * (T ω)⁻¹ * Q =
        A * (T ω * P) * (N * P * G⁻¹ * P * (T ω)ᴴ) := fun A => by
      calc A * (T ω * N) * (T ω)⁻¹ * Q = A * T ω * (N * P) * G⁻¹ * P * (T ω)ᴴ := by
            rw [hQ]; simp only [Matrix.mul_assoc, hTiT']
        _ = A * T ω * (P * N * P) * G⁻¹ * P * (T ω)ᴴ := by rw [hN]
        _ = A * (T ω * P) * (N * P * G⁻¹ * P * (T ω)ᴴ) := by simp only [Matrix.mul_assoc]
    have e2 : ∀ B : Matrix ι ι ℂ, Q * ((T ω)⁻¹)ᴴ * (T ω * N)ᴴ * B =
        T ω * P * G⁻¹ * P * Nᴴ * (P * (T ω)ᴴ * B) := fun B => by
      calc Q * ((T ω)⁻¹)ᴴ * (T ω * N)ᴴ * B = T ω * P * G⁻¹ * (P * Nᴴ) * (T ω)ᴴ * B := by
            rw [hQ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hTH']
        _ = T ω * P * G⁻¹ * (P * Nᴴ * P) * (T ω)ᴴ * B := by conv_lhs => rw [hNH]
        _ = T ω * P * G⁻¹ * P * Nᴴ * (P * (T ω)ᴴ * B) := by simp only [Matrix.mul_assoc]
    convert hasLineDerivAt_flagProj hT hu hP hPP using 1
    rw [e1, e2, hk1, hk2, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  · convert hasLineDerivAt_logVol hT hu hP hPP using 1
    congr 1
    symm
    calc (Q * (T ω * N) * (T ω)⁻¹).trace = ((T ω)⁻¹ * (Q * (T ω * N))).trace :=
          Matrix.trace_mul_comm _ _
      _ = (P * (G⁻¹ * P * (T ω)ᴴ * T ω * N)).trace := by
          rw [hQ]; simp only [Matrix.mul_assoc, hTiT']
      _ = (G⁻¹ * P * (T ω)ᴴ * T ω * (N * P)).trace := by
          rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
      _ = (G⁻¹ * P * (T ω)ᴴ * T ω * (P * N * P)).trace := by rw [hN]
      _ = (G⁻¹ * (P * (T ω)ᴴ * T ω * P) * (N * P)).trace := by simp only [Matrix.mul_assoc]
      _ = (P * N).trace := by
          rw [hA, Matrix.trace_mul_comm P, Matrix.mul_assoc, hPP, Matrix.trace_mul_comm]

end LSBA
