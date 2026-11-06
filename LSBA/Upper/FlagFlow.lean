import LSBA.Upper.LieAlgebra
import LSBA.Transfer.VolCocycle

/-!
# The direction of a flag

For an isotropic flag `U ⊂ Y` (`dim U = W - 1`, `dim Y = W`) with projections `P_U, P_Y`, the
projection `Π = P_Y - P_U` has rank one, onto a unit `e ∈ Y ⊖ U`, and
`M₀ = 2^{-1/2} (Π - J Π J) = 2^{-1/2} (e e* - (J e)(J e)*)` of Section 10
[sec:compact-proof] does not depend on the choice or the phase of `e`. It is Hermitian, lies in
`𝔤` of (10.1) [up:eq:lie-algebra], has Hilbert–Schmidt norm one, vanishes on `U` and leaves `Y`
invariant, with `Re Tr(P_Y M₀) = 2^{-1/2}`.
-/

open Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The direction `M₀ = 2^{-1/2} (Π - J Π J)`, `Π = P_Y - P_U`, of the flag `x`
(Section 10 [sec:compact-proof], before (10.2) [up:eq:lift-flag-flow]). -/
def flagDir {W : ℕ} (x : IsoFlag W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ((x.1.2 - x.1.1) - isoJ W * (x.1.2 - x.1.1) * isoJ W)

/-- The algebra of `P = Y - U` and `K = J P J` for a flag `U ⊂ Y`: both are Hermitian idempotents
with `P K = K P = 0`, `P J P = 0`, and `K` kills `U` and `Y` while `P` is absorbed by them. -/
private theorem flagFlow_core {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J U Y P K : Matrix ι ι ℂ} (hP : P = Y - U) (hK : K = J * P * J) (hJh : Jᴴ = J)
    (hJJ : J * J = 1) (hUh : Uᴴ = U) (hUU : U * U = U) (hYh : Yᴴ = Y) (hYY : Y * Y = Y)
    (hYU : Y * U = U) (hYJ : Y * J * Y = 0) :
    Pᴴ = P ∧ P * P = P ∧ Y * P = P ∧ P * Y = P ∧ U * P = 0 ∧ P * U = 0 ∧ P * J * P = 0 ∧
      Kᴴ = K ∧ K * K = K ∧ P * K = 0 ∧ K * P = 0 ∧ Y * K = 0 ∧ K * Y = 0 ∧ U * K = 0 ∧
      K * U = 0 := by
  have hUY : U * Y = U := by
    have := congrArg Matrix.conjTranspose hYU
    rwa [Matrix.conjTranspose_mul, hUh, hYh] at this
  have hPh : Pᴴ = P := by
    rw [hP, Matrix.conjTranspose_sub, hUh, hYh]
  have hPP : P * P = P := by
    rw [hP]
    simp only [Matrix.sub_mul, Matrix.mul_sub, hYY, hYU, hUY, hUU]
    abel
  have hYP : Y * P = P := by rw [hP, Matrix.mul_sub, hYY, hYU]
  have hPY : P * Y = P := by rw [hP, Matrix.sub_mul, hYY, hUY]
  have hUP : U * P = 0 := by rw [hP, Matrix.mul_sub, hUY, hUU, sub_self]
  have hPU : P * U = 0 := by rw [hP, Matrix.sub_mul, hYU, hUU, sub_self]
  have hPJP : P * J * P = 0 := by
    calc P * J * P = (P * Y) * J * (Y * P) := by rw [hPY, hYP]
      _ = P * (Y * J * Y) * P := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hYJ, Matrix.mul_zero, Matrix.zero_mul]
  have hKh : Kᴴ = K := by
    rw [hK, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh, hPh]
    simp only [Matrix.mul_assoc]
  have hKK : K * K = K := by
    calc K * K = J * (P * (J * J) * P) * J := by rw [hK]; simp only [Matrix.mul_assoc]
      _ = K := by rw [hJJ, Matrix.mul_one, hPP, hK]
  have hPK : P * K = 0 := by
    calc P * K = (P * J * P) * J := by rw [hK]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hPJP, Matrix.zero_mul]
  have hKP : K * P = 0 := by
    calc K * P = J * (P * J * P) := by rw [hK]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hPJP, Matrix.mul_zero]
  have hYK : Y * K = 0 := by
    calc Y * K = Y * J * (Y * P) * J := by rw [hK, hYP]; simp only [Matrix.mul_assoc]
      _ = (Y * J * Y) * P * J := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hYJ, Matrix.zero_mul, Matrix.zero_mul]
  have hKY : K * Y = 0 := by
    have := congrArg Matrix.conjTranspose hYK
    rwa [Matrix.conjTranspose_mul, hKh, hYh, Matrix.conjTranspose_zero] at this
  have hUK : U * K = 0 := by
    calc U * K = U * (Y * K) := by rw [← Matrix.mul_assoc, hUY]
      _ = 0 := by rw [hYK, Matrix.mul_zero]
  have hKU : K * U = 0 := by
    have := congrArg Matrix.conjTranspose hUK
    rwa [Matrix.conjTranspose_mul, hKh, hUh, Matrix.conjTranspose_zero] at this
  exact ⟨hPh, hPP, hYP, hPY, hUP, hPU, hPJP, hKh, hKK, hPK, hKP, hYK, hKY, hUK, hKU⟩

/-- `‖A‖_HS² = Re Tr(A* A)`. -/
private theorem flagFlow_hsSq {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    hsSq A = (Aᴴ * A).trace.re := by
  simp only [hsSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- `Tr(Y - U) = 1` for a flag `U ⊂ Y` of `W ≥ 1`. -/
private theorem flagFlow_trace {W : ℕ} (hW : 1 ≤ W) (x : IsoFlag W) :
    (x.1.2 - x.1.1).trace = 1 := by
  obtain ⟨⟨-, -, hUtr, -⟩, -, -, hYtr, -⟩ := x.2
  rw [Matrix.trace_sub, hYtr, hUtr, Nat.cast_sub hW, Nat.cast_one]
  ring

/-- `Tr(J P J) = Tr P` for `J² = 1`. -/
private theorem flagFlow_trace_conj {ι : Type*} [Fintype ι] [DecidableEq ι] {J P : Matrix ι ι ℂ}
    (hJJ : J * J = 1) : (J * P * J).trace = P.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]

/-- The direction `M₀` of Section 10 [sec:compact-proof], the algebraic part: for `W ≥ 1`, `M₀` lies
in `𝔤` of (10.1)
[up:eq:lie-algebra], is Hermitian with `‖M₀‖_HS = 1`, satisfies `M₀ P_U = P_U M₀ = 0` and
`M₀ P_Y = P_Y M₀ P_Y`, and `Re Tr(P_Y M₀) = 2^{-1/2}`. -/
theorem flagDir_spec {W : ℕ} (hW : 1 ≤ W) (x : IsoFlag W) :
    flagDir x ∈ lieJ W ∧ (flagDir x).IsHermitian ∧ hsSq (flagDir x) = 1 ∧
      flagDir x * x.1.1 = 0 ∧ x.1.1 * flagDir x = 0 ∧
      flagDir x * x.1.2 = x.1.2 * flagDir x * x.1.2 ∧
      (x.1.2 * flagDir x).trace.re = (Real.sqrt 2)⁻¹ := by
  obtain ⟨⟨hUh, hUU, -, hUJ⟩, hYh, hYY, -, hYU, hYJ⟩ := x.2
  have hJJ := isoJ_mul_isoJ W
  have hptr := flagFlow_trace hW x
  have hktr : (isoJ W * (x.1.2 - x.1.1) * isoJ W).trace = 1 := by
    rw [flagFlow_trace_conj hJJ, hptr]
  have hKJ : isoJ W * (x.1.2 - x.1.1) * isoJ W * isoJ W = isoJ W * (x.1.2 - x.1.1) := by
    rw [Matrix.mul_assoc _ (isoJ W), hJJ, Matrix.mul_one]
  have hJK : isoJ W * (isoJ W * (x.1.2 - x.1.1) * isoJ W) = (x.1.2 - x.1.1) * isoJ W := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  obtain ⟨hPh, hPP, hYP, hPY, hUP, hPU, hPJP, hKh, hKK, hPK, hKP, hYK, hKY, hUK, hKU⟩ :=
    flagFlow_core (P := x.1.2 - x.1.1) (K := isoJ W * (x.1.2 - x.1.1) * isoJ W) rfl rfl
      (isoJ_conjTranspose W) hJJ hUh.eq hUU hYh.eq hYY hYU hYJ
  unfold flagDir
  generalize x.1.2 - x.1.1 = P at *
  generalize isoJ W * P * isoJ W = K at *
  generalize x.1.1 = U at *
  generalize x.1.2 = Y at *
  generalize hc : ((Real.sqrt 2)⁻¹ : ℝ) = c
  have hc2 : (c : ℂ) * c = 1 / 2 := by
    rw [← hc, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
    push_cast; ring
  have hMh : ((c : ℂ) • (P - K))ᴴ = (c : ℂ) • (P - K) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hPh, hKh]
    simp
  have hMM : (c : ℂ) • (P - K) * ((c : ℂ) • (P - K)) = ((c : ℂ) * c) • (P + K) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [Matrix.sub_mul, Matrix.mul_sub, hPP, hKK, hPK, hKP]
    module
  have hMU : (c : ℂ) • (P - K) * U = 0 := by
    rw [Matrix.smul_mul, Matrix.sub_mul, hPU, hKU, sub_zero, smul_zero]
  have hMY : (c : ℂ) • (P - K) * Y = (c : ℂ) • P := by
    rw [Matrix.smul_mul, Matrix.sub_mul, hPY, hKY, sub_zero]
  refine ⟨⟨?_, ?_⟩, hMh, ?_, hMU, ?_, ?_, ?_⟩
  · rw [hMh]
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
    rw [Matrix.sub_mul, Matrix.mul_sub, hKJ, hJK]
    abel_nf
    simp
  · rw [Matrix.trace_smul, Matrix.trace_sub, hptr, hktr, sub_self, smul_zero]
  · rw [flagFlow_hsSq, hMh, hMM, Matrix.trace_smul, Matrix.trace_add, hptr, hktr, hc2]
    simp
    norm_num
  · have := congrArg Matrix.conjTranspose hMU
    rwa [Matrix.conjTranspose_mul, hMh, hUh.eq, Matrix.conjTranspose_zero] at this
  · rw [hMY, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, hYP, hYK, sub_zero, hPY]
  · rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub, 
      hYP, hYK, hptr, Matrix.trace_zero]
    simp

end LSBA
