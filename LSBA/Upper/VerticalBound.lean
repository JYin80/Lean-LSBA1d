import LSBA.Upper.BatchCutoff
import LSBA.Upper.CircleSpeed
import LSBA.Upper.LiftGeneral
import LSBA.Upper.BatchSmooth
import LSBA.Upper.FlagApprox
import LSBA.Analysis.FlagDerivative

/-!
# The vertical bound in the lift form

(F.8) [cc:eq:vertical] in the lift form, under the law of the GUE inputs (Lemma F.3
[lem:c-operators] with the cutoff of Appendix G.5 [sec:c-component-proof]): for a batch of
`1000 + n` inputs with the batch cutoff `χ_q`, `‖T‖ ≤ K` on its support, and a cut lift `X` of
`√2 K_U` on the first `1000` inputs (`D_X T = 2 T K_U` on the support of the cutoff `χ`,
`𝔼 |δ_G(χ X)|² ≤ b`; Lemma 10.1 [lem:c-gaussian-lift]), every `C¹` function `ψ` of the
projection pair with `|ψ| ≤ S` on the flags satisfies
`|𝔼[χ_q ∂_θ ψ(TU, TY)]| ≤ ½ K² (b^{1/2} + 2) S`.
The proof is Gaussian integration by parts (8.33) [up:eq:gaussian-divergence] for the field
`χ_q e^{2c} X` with the product rule: `D_X ψ(TU, TY) = 2 e^{-2c} ∂_θ ψ(TU, TY)` by the
infinitesimal (8.36) [cc:eq:jac], `e^{2c} ≤ K²` and `|D_X e^{2c}| ≤ 2K²` on the support.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Helpers -/

/-- The extension by zero of a sample of the first `p` blocks to a sample of `p + q` blocks. -/
private def vbEmb (W p q : ℕ) (v : Ω W p) : Ω W (p + q) :=
  fun i => if h : (i.1 : ℕ) < p then v (⟨i.1, h⟩, i.2) else 0

/-- Moving along an extension by zero moves the first `p` blocks. -/
private theorem vbEmb_fst (W p q : ℕ) (ω : Ω W (p + q)) (t : ℝ) (v : Ω W p) :
    (blockAppend W p q (ω + t • vbEmb W p q v)).1 = (blockAppend W p q ω).1 + t • v := by
  funext i
  simp [blockAppend, vbEmb]

/-- Moving along an extension by zero leaves the last `q` blocks fixed. -/
private theorem vbEmb_snd (W p q : ℕ) (ω : Ω W (p + q)) (t : ℝ) (v : Ω W p) :
    (blockAppend W p q (ω + t • vbEmb W p q v)).2 = (blockAppend W p q ω).2 := by
  funext i
  simp [blockAppend, vbEmb]

/-- The extension by zero is homogeneous. -/
private theorem vbEmb_smul (W p q : ℕ) (a : ℝ) (v : Ω W p) :
    vbEmb W p q (a • v) = a • vbEmb W p q v := by
  funext i
  by_cases h : (i.1 : ℕ) < p <;> simp [vbEmb, h]

/-- The extension by zero is `C^∞` (linear). -/
private theorem vbEmb_contDiff (W p q : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (vbEmb W p q) := by
  refine contDiff_pi.2 fun i => ?_
  by_cases h : (i.1 : ℕ) < p
  · simp only [vbEmb, h, dite_true]
    exact contDiff_apply ℝ (fun _ => ℝ) _
  · simp only [vbEmb, h, dite_false]
    exact contDiff_const

/-- The first `p` blocks are a `C^∞` (linear) function of the sample. -/
private theorem vb_contDiff_fst (W p q : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) fun ω : Ω W (p + q) => (blockAppend W p q ω).1 :=
  contDiff_pi.2 fun x => contDiff_apply ℝ (fun _ => ℝ) (Fin.castAdd q x.1, x.2)

/-- The Gaussian divergence (8.33) [up:eq:gaussian-divergence] of a field on the first `p`
blocks, extended by zero, is its divergence on the first `p` blocks. -/
private theorem vb_gaussDiv_emb (W p q : ℕ) (X : Ω W p → Ω W p) (ω : Ω W (p + q)) :
    gaussDiv (fun η => vbEmb W p q (X (blockAppend W p q η).1)) ω =
      gaussDiv X (blockAppend W p q ω).1 := by
  unfold gaussDiv
  symm
  refine Fintype.sum_of_injective (fun i : Fin p × Fin W × Fin W => (Fin.castAdd q i.1, i.2))
    ?_ _ _ ?_ ?_
  · intro i j hij
    simp only [Prod.mk.injEq, Fin.castAdd_inj] at hij
    exact Prod.ext hij.1 hij.2
  · intro i hi
    have h : ¬ ((i.1 : ℕ) < p) := fun h => hi ⟨(⟨i.1, h⟩, i.2), Prod.ext (Fin.ext rfl) rfl⟩
    have h0 : (fun y : Ω W (p + q) => vbEmb W p q (X (blockAppend W p q y).1) i) = fun _ => 0 :=
      funext fun y => by simp [vbEmb, h]
    simp only [h0]
    simp [vbEmb, h, lineDeriv]
  · intro i
    have h1 : (fun y : Ω W (p + q) => vbEmb W p q (X (blockAppend W p q y).1)
        (Fin.castAdd q i.1, i.2)) = fun y => X (blockAppend W p q y).1 i :=
      funext fun y => by simp [vbEmb]
    simp only [h1]
    congr 1
    · simp [blockAppend, vbEmb]
    unfold lineDeriv
    congr 1
    funext t
    congr 1
    funext j
    simp only [blockAppend, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Prod.mk.injEq,
      Fin.castAdd_inj, smul_eq_mul]
    simp only [← Prod.ext_iff]

/-- On the support of the cutoff, the extended lift moves the batch `T = T_rest F` as
`D T = T (2 K)` when `D F = √2 F (√2 K)` (Lemma 10.1 [lem:c-gaussian-lift]). -/
private theorem vb_hasLineDerivAt_batchMat {W n : ℕ} {g E b : ℝ}
    {K : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {χ : Ω W 1000 → ℝ}
    {Y : Ω W 1000 → Ω W 1000}
    (hY : IsCutLift W 1000 (batchMat W g E 1000) (((Real.sqrt 2 : ℝ) : ℂ) • K) b χ Y)
    {ω : Ω W (1000 + n)} (hω : (blockAppend W 1000 n ω).1 ∈ tsupport χ) :
    HasLineDerivAt ℝ (batchMat W g E (1000 + n)) (batchMat W g E (1000 + n) ω * ((2 : ℂ) • K)) ω
      (vbEmb W 1000 n (Y (blockAppend W 1000 n ω).1)) := by
  have h := hY.1 _ hω
  unfold HasLineDerivAt at h ⊢
  let A := batchMat W g E n (blockAppend W 1000 n ω).2
  let L : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ →ₗ[ℝ]
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
    { toFun := fun B => A * B, map_add' := fun B C => Matrix.mul_add A B C,
      map_smul' := fun r B => Matrix.mul_smul A r B }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have hfun : (fun t : ℝ => batchMat W g E (1000 + n)
      (ω + t • vbEmb W 1000 n (Y (blockAppend W 1000 n ω).1))) =
      (LinearMap.toContinuousLinearMap L) ∘
        fun t => batchMat W g E 1000
          ((blockAppend W 1000 n ω).1 + t • Y (blockAppend W 1000 n ω).1) := by
    funext t
    simp only [Function.comp, LinearMap.coe_toContinuousLinearMap', L, LinearMap.coe_mk,
      AddHom.coe_mk]
    rw [batchMat_add, vbEmb_fst, vbEmb_snd]
  rw [hfun]
  convert h2 using 1
  simp only [LinearMap.coe_toContinuousLinearMap', L, LinearMap.coe_mk, AddHom.coe_mk]
  rw [batchMat_add W g E 1000 n ω]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  simp only [Matrix.mul_smul, Matrix.mul_assoc, smul_smul, hs]
  rfl

/-- The test function `ψ(TU, TY)` of the inputs. -/
private def vbTest (W : ℕ) (g E : ℝ) (q : ℕ) (x : IsoFlag W)
    (ψ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ)
    (η : Ω W q) : ℝ :=
  ψ ((flagAct (batchMat W g E q η) x : IsoFlag W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)

/-- Every batch is invertible. -/
private theorem vb_isUnit {W q : ℕ} (g E : ℝ) (ω : Ω W q) : IsUnit (batchMat W g E q ω) :=
  (Matrix.isUnit_iff_isUnit_det _).2 (by rw [(batchMat_mem_isoGroup W g E q ω).2]; exact isUnit_one)

/-- The chain rule of the proof of Lemma F.3 [lem:c-operators]: along a direction with
`D T = T (2 K_U)`, `D ψ(TU, TY) = 2 e^{-2c} ∂_θ ψ(TU, TY)`, by the infinitesimal (8.36)
[cc:eq:jac]. -/
private theorem vb_fderiv_test {W q : ℕ} (hW : 1 ≤ W) {g E : ℝ} {x : IsoFlag W}
    {ψ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) {ω u : Ω W q}
    (hT : HasLineDerivAt ℝ (batchMat W g E q) (batchMat W g E q ω * ((2 : ℂ) • circleGen x.1.1))
      ω u) :
    fderiv ℝ (vbTest W g E q x ψ) ω u =
      2 * Real.exp (-2 * volCocycle (batchMat W g E q ω) x) *
        circleDeriv ψ (flagAct (batchMat W g E q ω) x) := by
  have hJ : ∀ η, (batchMat W g E q η)ᴴ * isoJ W * batchMat W g E q η = isoJ W :=
    fun η => (batchMat_mem_isoGroup W g E q η).1
  have hu := vb_isUnit (W := W) g E ω
  obtain ⟨⟨hUh, hUU, -, -⟩, hYh, hYY, -, -, -⟩ := x.2
  obtain ⟨-, -, hKP, hPK⟩ := circleGen_mem_lieJ hW x.2.1
  have hG : vbTest W g E q x ψ =
      ψ ∘ fun η => (flagProj (batchMat W g E q η) x.1.1, flagProj (batchMat W g E q η) x.1.2) :=
    funext fun η => by simp only [vbTest, Function.comp, flagAct_coe (hJ η) x]
  have hU := (hasLineDerivAt_flagProj_logVol_of_mul hT hu hUh hUU
    (by rw [Matrix.smul_mul, Matrix.mul_smul, hKP, hPK]; simp)).1
  have hYd := hasLineDerivAt_flagProj hT hu hYh hYY
  have hd : DifferentiableAt ℝ (vbTest W g E q x ψ) ω :=
    (hψ.comp (contDiff_flagAct_batchMat W g E q x).1).differentiable one_ne_zero ω
  rw [← hd.lineDeriv_eq_fderiv]
  have hΦ : HasLineDerivAt ℝ (vbTest W g E q x ψ)
      (fderiv ℝ ψ (flagProj (batchMat W g E q ω) x.1.1, flagProj (batchMat W g E q ω) x.1.2)
        (0, (1 - flagProj (batchMat W g E q ω) x.1.2) *
            (batchMat W g E q ω * ((2 : ℂ) • circleGen x.1.1)) * (batchMat W g E q ω)⁻¹ *
              flagProj (batchMat W g E q ω) x.1.2 +
          flagProj (batchMat W g E q ω) x.1.2 * ((batchMat W g E q ω)⁻¹)ᴴ *
            (batchMat W g E q ω * ((2 : ℂ) • circleGen x.1.1))ᴴ *
              (1 - flagProj (batchMat W g E q ω) x.1.2))) ω u := by
    rw [hG]
    unfold HasLineDerivAt at hU hYd ⊢
    exact (hψ.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (hU.prodMk hYd) (by simp)
  rw [hΦ.lineDeriv]
  have hmot := flagProj_circleGen_motion (hJ ω) x
  have h2 : (1 - flagProj (batchMat W g E q ω) x.1.2) *
            (batchMat W g E q ω * ((2 : ℂ) • circleGen x.1.1)) * (batchMat W g E q ω)⁻¹ *
              flagProj (batchMat W g E q ω) x.1.2 +
          flagProj (batchMat W g E q ω) x.1.2 * ((batchMat W g E q ω)⁻¹)ᴴ *
            (batchMat W g E q ω * ((2 : ℂ) • circleGen x.1.1))ᴴ *
              (1 - flagProj (batchMat W g E q ω) x.1.2) =
      (2 : ℂ) • ((1 - flagProj (batchMat W g E q ω) x.1.2) *
            (batchMat W g E q ω * circleGen x.1.1) * (batchMat W g E q ω)⁻¹ *
              flagProj (batchMat W g E q ω) x.1.2 +
          flagProj (batchMat W g E q ω) x.1.2 * ((batchMat W g E q ω)⁻¹)ᴴ *
            (batchMat W g E q ω * circleGen x.1.1)ᴴ *
              (1 - flagProj (batchMat W g E q ω) x.1.2)) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_smul, smul_add]
    norm_num
  rw [h2, hmot]
  set C := circleGen (flagProj (batchMat W g E q ω) x.1.1) * flagProj (batchMat W g E q ω) x.1.2 -
    flagProj (batchMat W g E q ω) x.1.2 * circleGen (flagProj (batchMat W g E q ω) x.1.1)
  set r := Real.exp (-2 * volCocycle (batchMat W g E q ω) x)
  have hv : ((0 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), (2 : ℂ) • ((r : ℂ) • C)) =
      (2 * r) • ((0 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), C) := by
    refine Prod.ext (by simp) ?_
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
    ring
  rw [hv, map_smul, smul_eq_mul, circleDeriv, flagAct_coe (hJ ω)]

/-- Along a direction with `D T = T (2 K_U)`, the cocycle (8.17) [eq:c-volume-cocycle] has
derivative at most `e^{-c} ‖T‖` in absolute value. -/
private theorem vb_hasLineDerivAt_cocycle {W q : ℕ} {g E : ℝ} {x : IsoFlag W} {ω u : Ω W q}
    (hT : HasLineDerivAt ℝ (batchMat W g E q) (batchMat W g E q ω * ((2 : ℂ) • circleGen x.1.1))
      ω u) :
    ∃ c' : ℝ, HasLineDerivAt ℝ (fun η => volCocycle (batchMat W g E q η) x) c' ω u ∧
      |c'| ≤ Real.exp (-volCocycle (batchMat W g E q ω) x) * ‖batchMat W g E q ω‖ := by
  have hu := vb_isUnit (W := W) g E ω
  obtain ⟨⟨hUh, hUU, -, -⟩, hYh, hYY, -, -, -⟩ := x.2
  have hYd := hasLineDerivAt_logVol hT hu hYh hYY
  have hUd := hasLineDerivAt_logVol hT hu hUh hUU
  refine ⟨(flagProj (batchMat W g E q ω) x.1.2 *
      (batchMat W g E q ω * ((2 : ℂ) • circleGen x.1.1)) *
      (batchMat W g E q ω)⁻¹).trace.re - (flagProj (batchMat W g E q ω) x.1.1 *
      (batchMat W g E q ω * ((2 : ℂ) • circleGen x.1.1)) * (batchMat W g E q ω)⁻¹).trace.re,
    ?_, ?_⟩
  · unfold HasLineDerivAt at hYd hUd ⊢
    exact hYd.sub hUd
  · have hb := abs_cocycle_circleGen_le (batchMat_mem_isoGroup W g E q ω).1 x
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    have h2 : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp
    rw [h2, h2, ← mul_sub, abs_mul, abs_two]
    linarith

/-- The extension by zero of `0` is `0`. -/
private theorem vbEmb_zero (W p q : ℕ) : vbEmb W p q 0 = 0 := by
  funext i
  by_cases h : (i.1 : ℕ) < p <;> simp [vbEmb, h]

/-- `𝔼 |δ_G X| ≤ b^{1/2}` when `𝔼 |δ_G X|² ≤ b`, for a field `X` on the first `1000` of
`1000 + n` inputs. -/
private theorem vb_integral_abs_div_le {W n : ℕ} {b : ℝ} {X : Ω W 1000 → Ω W 1000}
    (hm : Measurable (gaussDiv X))
    (hb : ∫⁻ ω, ‖gaussDiv X ω‖ₑ ^ 2 ∂(μ W 1000) ≤ ENNReal.ofReal b) :
    Integrable (fun ω : Ω W (1000 + n) => |gaussDiv X (blockAppend W 1000 n ω).1|)
        (μ W (1000 + n)) ∧
      ∫ ω, |gaussDiv X (blockAppend W 1000 n ω).1| ∂(μ W (1000 + n)) ≤ Real.sqrt b := by
  have hmp : MeasurePreserving (fun ω : Ω W (1000 + n) => (blockAppend W 1000 n ω).1)
      (μ W (1000 + n)) (μ W 1000) :=
    measurePreserving_fst.comp (measurePreserving_blockAppend W 1000 n)
  have hae : AEStronglyMeasurable (gaussDiv X) (μ W 1000) := hm.aestronglyMeasurable
  have h2 : eLpNorm (gaussDiv X) 2 (μ W 1000) ≤ ENNReal.ofReal (Real.sqrt b) := by
    rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hae, eLpNorm']
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    calc _ ≤ ENNReal.ofReal b ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hb (by norm_num)
      _ ≤ _ := by
        rcases le_total 0 b with h | h
        · rw [ENNReal.ofReal_rpow_of_nonneg h (by norm_num), Real.sqrt_eq_rpow]
        · rw [ENNReal.ofReal_eq_zero.2 h, ENNReal.zero_rpow_of_pos (by norm_num)]
          exact bot_le
  have h1 : eLpNorm (gaussDiv X) 1 (μ W 1000) ≤ ENNReal.ofReal (Real.sqrt b) :=
    (eLpNorm_le_eLpNorm_of_exponent_le one_le_two).trans h2
  have hint : Integrable (gaussDiv X) (μ W 1000) :=
    memLp_one_iff_integrable.1 (h1.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hmp.integrable_comp_of_integrable hint.abs, ?_⟩
  have heq : ∫ ω, |gaussDiv X (blockAppend W 1000 n ω).1| ∂(μ W (1000 + n)) =
      ∫ v, |gaussDiv X v| ∂(μ W 1000) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact hint.abs.aestronglyMeasurable)]
  have hn : ∫ v, |gaussDiv X v| ∂(μ W 1000) = (∫⁻ v, ‖gaussDiv X v‖ₑ ∂(μ W 1000)).toReal := by
    rw [← integral_norm_eq_lintegral_enorm hae]
    rfl
  rw [heq, hn, ← eLpNorm_one_eq_lintegral_enorm hae]
  exact ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg b) h1

/-- The product `∏_i χ̃(V_{1000+i})` of the cutoffs of the last `n` inputs. -/
private def vbRest (W n : ℕ) (ω : Ω W (1000 + n)) : ℝ :=
  ∏ i : Fin n, blockCut W fun k => (blockAppend W 1000 n ω).2 (i, k)

/-- The product of the cutoffs of the last `n` inputs is `C¹`. -/
private theorem vbRest_contDiff (W n : ℕ) : ContDiff ℝ 1 (vbRest W n) := by
  unfold vbRest
  refine contDiff_prod fun i _ => ?_
  have hb : ContDiff ℝ 1 (blockCut W) := by
    unfold blockCut
    exact Real.smoothTransition.contDiff.comp (by fun_prop)
  exact hb.comp (contDiff_pi.2 fun k => contDiff_apply ℝ (fun _ => ℝ) (Fin.natAdd 1000 i, k))

/-- The product of the cutoffs of the last `n` inputs does not move along an extension by zero
from the first `1000` inputs. -/
private theorem vbRest_snd (W n : ℕ) (ω : Ω W (1000 + n)) (t : ℝ) (v : Ω W 1000) :
    vbRest W n (ω + t • vbEmb W 1000 n v) = vbRest W n ω := by
  unfold vbRest
  rw [vbEmb_snd]

/-- The product of the cutoffs of the last `n` inputs takes values in `[0, 1]`. -/
private theorem vbRest_mem (W n : ℕ) (ω : Ω W (1000 + n)) :
    0 ≤ vbRest W n ω ∧ vbRest W n ω ≤ 1 :=
  ⟨Finset.prod_nonneg fun _ _ => Real.smoothTransition.nonneg _,
    Finset.prod_le_one₀ (fun _ _ => Real.smoothTransition.nonneg _)
      fun _ _ => Real.smoothTransition.le_one _⟩

/-- The field `e^{2c} χ_q X̃` of the proof of Lemma F.3 [lem:c-operators]: `e^{2c}` times the
cutoffs of the last `n` inputs times the field `X` on the first `1000` inputs, extended by
zero. -/
private def vbField (W n : ℕ) (g E : ℝ) (x : IsoFlag W) (X : Ω W 1000 → Ω W 1000)
    (ω : Ω W (1000 + n)) : Ω W (1000 + n) :=
  (Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) * vbRest W n ω) •
    vbEmb W 1000 n (X (blockAppend W 1000 n ω).1)

/-- (F.8) [cc:eq:vertical] in the lift form: `|𝔼[χ_q ∂_θ ψ(TU, TY)]| ≤ ½ K² (b^{1/2} + 2) S`
for every `C¹` function `ψ` of the projection pair with `|ψ| ≤ S` on the flags, where
`‖T‖ ≤ K` on the support of the batch cutoff and `X` is a cut lift of `√2 K_U` on the first
`1000` inputs with `𝔼 |δ_G(χ X)|² ≤ b` (proof of Lemma F.3 [lem:c-operators]). -/
theorem abs_integral_circleDeriv_le {W n : ℕ} {g E K b S : ℝ} {x : IsoFlag W}
    {χ : Ω W 1000 → ℝ} {Y : Ω W 1000 → Ω W 1000} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχ01 : ∀ ω, 0 ≤ χ ω ∧ χ ω ≤ 1)
    (hY : IsCutLift W 1000 (batchMat W g E 1000) (((Real.sqrt 2 : ℝ) : ℂ) • circleGen x.1.1) b χ
      Y)
    (hK : ∀ ω ∈ tsupport (batchCut W n χ), ‖batchMat W g E (1000 + n) ω‖ ≤ K)
    {ψ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hS : ∀ y : IsoFlag W, |ψ y.1| ≤ S) :
    |∫ ω, batchCut W n χ ω * circleDeriv ψ (flagAct (batchMat W g E (1000 + n) ω) x)
        ∂(μ W (1000 + n))| ≤ K ^ 2 * (Real.sqrt b + 2) / 2 * S := by
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS x)
  rcases Nat.eq_zero_or_pos W with hW0 | hW
  · subst hW0
    have h0 : ∀ y : IsoFlag 0, circleDeriv ψ y = 0 := fun y => by
      have hz : ((0 : Matrix (Fin 2 × Fin 0) (Fin 2 × Fin 0) ℂ),
          circleGen y.1.1 * y.1.2 - y.1.2 * circleGen y.1.1) = 0 :=
        Prod.ext rfl (Matrix.ext fun i _ => Fin.elim0 i.2)
      rw [circleDeriv, hz, map_zero]
    simp only [h0, mul_zero, integral_zero, abs_zero]
    exact mul_nonneg (by positivity) hS0
  -- notation
  have hbc : ∀ ω : Ω W (1000 + n),
      batchCut W n χ ω = χ (blockAppend W 1000 n ω).1 * vbRest W n ω := fun _ => rfl
  have hfC : ContDiff ℝ 1 fun ω : Ω W (1000 + n) =>
      Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) * vbRest W n ω :=
    (Real.contDiff_exp.comp
      (contDiff_const.mul (contDiff_volCocycle_batchMat W g E (1000 + n) x).1)).mul
      (vbRest_contDiff W n)
  have hVC : ContDiff ℝ 1 fun ω : Ω W (1000 + n) =>
      vbEmb W 1000 n ((fun η => χ η • Y η) (blockAppend W 1000 n ω).1) :=
    ((vbEmb_contDiff W 1000 n).comp (hY.2.1.comp (vb_contDiff_fst W 1000 n))).of_le
      (by exact_mod_cast le_top)
  have hZeq : vbField W n g E x (fun η => χ η • Y η) = fun ω =>
      (Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) * vbRest W n ω) •
        vbEmb W 1000 n ((fun η => χ η • Y η) (blockAppend W 1000 n ω).1) := rfl
  have hZω : ∀ ω, vbField W n g E x (fun η => χ η • Y η) ω =
      (Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) * vbRest W n ω) •
        vbEmb W 1000 n (χ (blockAppend W 1000 n ω).1 • Y (blockAppend W 1000 n ω).1) :=
    fun _ => rfl
  have hZC : ContDiff ℝ 1 (vbField W n g E x (fun η => χ η • Y η)) := by
    rw [hZeq]; exact hfC.smul hVC
  have hV0 : ∀ ω : Ω W (1000 + n), χ (blockAppend W 1000 n ω).1 = 0 →
      vbEmb W 1000 n (χ (blockAppend W 1000 n ω).1 • Y (blockAppend W 1000 n ω).1) = 0 :=
    fun ω h => by simp only [h, zero_smul, vbEmb_zero]
  have hsupp : ∀ ω, vbField W n g E x (fun η => χ η • Y η) ω ≠ 0 → batchCut W n χ ω ≠ 0 := by
    intro ω h h0
    apply h
    rw [hbc] at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · rw [hZω, hV0 ω h1, smul_zero]
    · rw [hZω, h1, mul_zero, zero_smul]
  have hZcs : HasCompactSupport (vbField W n g E x (fun η => χ η • Y η)) :=
    (batchCut_spec hχ hχc hχ01).2.1.mono fun ω h => hsupp ω h
  have hZadm : IBPAdmissible (vbField W n g E x (fun η => χ η • Y η)) := by
    obtain ⟨C, hC⟩ := hZC.continuous.bounded_above_of_compact_support hZcs
    obtain ⟨C', hC'⟩ := (hZC.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
      (hZcs.fderiv (𝕜 := ℝ))
    exact ibpAdmissible_of_contDiff hZC ⟨C, 0, fun ω => by simpa using hC ω⟩
      ⟨C', 0, fun ω => by simpa using hC' ω⟩
  have hGC := contDiff_flagAct_batchMat W g E (1000 + n) x
  have hΦ : IsIBPTest (vbTest W g E (1000 + n) x ψ) := by
    refine ⟨hψ.comp hGC.1, ⟨S, fun ω => hS _⟩, ?_⟩
    obtain ⟨Cg, k, hg⟩ := hGC.2
    obtain ⟨Mψ, hMψ⟩ := (isCompact_isoFlags W).exists_bound_of_continuousOn
      (hψ.continuous_fderiv one_ne_zero).continuousOn
    refine ⟨Mψ * Cg, k, fun ω => ?_⟩
    have hmem := (flagAct (batchMat W g E (1000 + n) ω) x).2
    have hcomp : fderiv ℝ (vbTest W g E (1000 + n) x ψ) ω =
        (fderiv ℝ ψ ((flagAct (batchMat W g E (1000 + n) ω) x : IsoFlag W) :
          Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).comp
          (fderiv ℝ (fun η : Ω W (1000 + n) => ((flagAct (batchMat W g E (1000 + n) η) x :
            IsoFlag W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
              Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) ω) :=
      fderiv_comp ω (hψ.differentiable one_ne_zero _) (hGC.1.differentiable one_ne_zero ω)
    rw [hcomp]
    calc _ ≤ _ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Mψ * (Cg * (1 + ‖ω‖) ^ k) :=
          mul_le_mul (hMψ _ hmem) (hg ω) (norm_nonneg _) ((norm_nonneg _).trans (hMψ _ hmem))
      _ = _ := by ring
  obtain ⟨-, hint, hibp⟩ := hZadm.2 _ hΦ
  rw [← μ_eq_stdGauss] at hint hibp
  -- the integrand of the left side
  have hlhs : ∀ ω : Ω W (1000 + n),
      fderiv ℝ (vbTest W g E (1000 + n) x ψ) ω (vbField W n g E x (fun η => χ η • Y η) ω) =
        2 * (batchCut W n χ ω * circleDeriv ψ (flagAct (batchMat W g E (1000 + n) ω) x)) := by
    intro ω
    by_cases h0 : χ (blockAppend W 1000 n ω).1 = 0
    · rw [hZω, hV0 ω h0, smul_zero, map_zero, hbc, h0]
      ring
    · have hmem : (blockAppend W 1000 n ω).1 ∈ tsupport χ := subset_tsupport _ h0
      have hT := vb_hasLineDerivAt_batchMat hY hmem
      have hv : vbField W n g E x (fun η => χ η • Y η) ω =
          (Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) * vbRest W n ω *
            χ (blockAppend W 1000 n ω).1) • vbEmb W 1000 n (Y (blockAppend W 1000 n ω).1) := by
        rw [hZω, vbEmb_smul, smul_smul]
      rw [hv, map_smul, smul_eq_mul, vb_fderiv_test hW hψ hT, hbc]
      have he : Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) *
          Real.exp (-2 * volCocycle (batchMat W g E (1000 + n) ω) x) = 1 := by
        rw [← Real.exp_add]; simp
      linear_combination (2 * χ (blockAppend W 1000 n ω).1 * vbRest W n ω *
        circleDeriv ψ (flagAct (batchMat W g E (1000 + n) ω) x)) * he
  -- the pointwise bound on the right side
  have hrhs : ∀ ω : Ω W (1000 + n),
      |vbTest W g E (1000 + n) x ψ ω * gaussDiv (vbField W n g E x (fun η => χ η • Y η)) ω| ≤
        S * (K ^ 2 * |gaussDiv (fun η => χ η • Y η) (blockAppend W 1000 n ω).1| + 2 * K ^ 2) := by
    intro ω
    rw [abs_mul]
    refine mul_le_mul (hS _) ?_ (abs_nonneg _) hS0
    by_cases hω : ω ∈ tsupport (batchCut W n χ)
    · have hTK := hK ω hω
      have hJ := (batchMat_mem_isoGroup W g E (1000 + n) ω).1
      have hc := abs_volCocycle_le hJ x
      have : Nonempty (Fin W) := ⟨⟨0, hW⟩⟩
      have hTpos : 0 < ‖batchMat W g E (1000 + n) ω‖ :=
        norm_pos_iff.2 (vb_isUnit (W := W) g E ω).ne_zero
      have hec : Real.exp (volCocycle (batchMat W g E (1000 + n) ω) x) ≤
          ‖batchMat W g E (1000 + n) ω‖ := by
        calc _ ≤ Real.exp (Real.log ‖batchMat W g E (1000 + n) ω‖) :=
              Real.exp_le_exp.2 ((le_abs_self _).trans hc)
          _ = _ := Real.exp_log hTpos
      have hK0 : 0 ≤ K := (norm_nonneg _).trans hTK
      have hcK : Real.exp (volCocycle (batchMat W g E (1000 + n) ω) x) *
          ‖batchMat W g E (1000 + n) ω‖ ≤ K ^ 2 := by
        rw [sq]; exact mul_le_mul (hec.trans hTK) hTK (norm_nonneg _) hK0
      have he2 : Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) ≤ K ^ 2 := by
        rw [two_mul, Real.exp_add]
        exact (mul_le_mul_of_nonneg_left hec (Real.exp_pos _).le).trans hcK
      have hρ := vbRest_mem W n ω
      have hf : |Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) * vbRest W n ω| ≤
          K ^ 2 := by
        rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hρ.1)]
        exact (mul_le_of_le_one_right (Real.exp_pos _).le hρ.2).trans he2
      have hDf : |fderiv ℝ (fun ω : Ω W (1000 + n) =>
          Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) * vbRest W n ω) ω
            (vbEmb W 1000 n ((fun η => χ η • Y η) (blockAppend W 1000 n ω).1))| ≤ 2 * K ^ 2 := by
        by_cases h0 : χ (blockAppend W 1000 n ω).1 = 0
        · rw [hV0 ω h0, map_zero, abs_zero]; positivity
        have hmem : (blockAppend W 1000 n ω).1 ∈ tsupport χ := subset_tsupport _ h0
        have hT := vb_hasLineDerivAt_batchMat hY hmem
        obtain ⟨c', hc', hc'b⟩ := vb_hasLineDerivAt_cocycle hT
        have hfl : HasLineDerivAt ℝ (fun ω : Ω W (1000 + n) =>
            Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) * vbRest W n ω)
            (Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) * (2 * c') *
              vbRest W n ω) ω (vbEmb W 1000 n (Y (blockAppend W 1000 n ω).1)) := by
          unfold HasLineDerivAt at hc' ⊢
          have hfun : (fun t : ℝ => Real.exp (2 * volCocycle (batchMat W g E (1000 + n)
              (ω + t • vbEmb W 1000 n (Y (blockAppend W 1000 n ω).1))) x) *
                vbRest W n (ω + t • vbEmb W 1000 n (Y (blockAppend W 1000 n ω).1))) =
              fun t => Real.exp (2 * volCocycle (batchMat W g E (1000 + n)
                (ω + t • vbEmb W 1000 n (Y (blockAppend W 1000 n ω).1))) x) * vbRest W n ω :=
            funext fun t => by rw [vbRest_snd]
          rw [hfun]
          have h3 := ((hc'.const_mul 2).exp).mul_const (vbRest W n ω)
          simp only [zero_smul, add_zero] at h3
          exact h3
        have hfd := (hfC.differentiable one_ne_zero ω).lineDeriv_eq_fderiv
          (v := vbEmb W 1000 n (Y (blockAppend W 1000 n ω).1))
        rw [hfl.lineDeriv] at hfd
        have hχ1 := hχ01 (blockAppend W 1000 n ω).1
        have hec' : Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) *
            Real.exp (-volCocycle (batchMat W g E (1000 + n) ω) x) =
            Real.exp (volCocycle (batchMat W g E (1000 + n) ω) x) := by
          rw [← Real.exp_add]; ring_nf
        simp only [vbEmb_smul, map_smul, ← hfd, smul_eq_mul]
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hχ1.1,
          abs_of_pos (Real.exp_pos _), abs_of_nonneg hρ.1, abs_two]
        calc χ (blockAppend W 1000 n ω).1 *
              (Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) * (2 * |c'|) *
                vbRest W n ω)
            ≤ 1 * (Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) *
                (2 * (Real.exp (-volCocycle (batchMat W g E (1000 + n) ω) x) *
                  ‖batchMat W g E (1000 + n) ω‖)) * 1) := by
              have := hρ.1; have := hρ.2; have := hχ1.2
              gcongr
          _ = 2 * (Real.exp (volCocycle (batchMat W g E (1000 + n) ω) x) *
                ‖batchMat W g E (1000 + n) ω‖) := by rw [← hec']; ring
          _ ≤ 2 * K ^ 2 := by linarith
      rw [hZeq, gaussDiv_smul (hfC.differentiable one_ne_zero ω)
        (fun i => ((contDiff_pi.1 hVC i).differentiable one_ne_zero ω).lineDifferentiableAt),
        vb_gaussDiv_emb W 1000 n (fun η => χ η • Y η) ω]
      calc _ ≤ |Real.exp (2 * volCocycle (batchMat W g E (1000 + n) ω) x) * vbRest W n ω *
              gaussDiv (fun η => χ η • Y η) (blockAppend W 1000 n ω).1| + |fderiv ℝ
                (fun ω : Ω W (1000 + n) => Real.exp (2 * volCocycle (batchMat W g E (1000 + n)
                  ω) x) * vbRest W n ω) ω
                (vbEmb W 1000 n ((fun η => χ η • Y η) (blockAppend W 1000 n ω).1))| :=
            abs_sub _ _
        _ ≤ _ := by
            rw [abs_mul]
            exact add_le_add (mul_le_mul_of_nonneg_right hf (abs_nonneg _)) hDf
    · have hev : vbField W n g E x (fun η => χ η • Y η) =ᶠ[nhds ω] 0 := by
        filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hω] with y hy
        by_contra hne
        exact hy (subset_tsupport _ (hsupp y hne))
      have hd0 : gaussDiv (vbField W n g E x (fun η => χ η • Y η)) ω = 0 := by
        unfold gaussDiv
        refine Finset.sum_eq_zero fun i _ => ?_
        have hz : vbField W n g E x (fun η => χ η • Y η) ω i = 0 := by
          rw [hev.eq_of_nhds]; rfl
        have hf : HasFDerivAt (fun y => vbField W n g E x (fun η => χ η • Y η) y i)
            (0 : Ω W (1000 + n) →L[ℝ] ℝ) ω :=
          (hasFDerivAt_const (0 : ℝ) ω).congr_of_eventuallyEq
            (hev.mono fun y hy => congrFun hy i)
        rw [hz, (hf.hasLineDerivAt (Pi.single i 1)).lineDeriv]
        simp
      rw [hd0, abs_zero]
      positivity
  have hsum := vb_integral_abs_div_le (n := n) hY.2.2.1.1 hY.2.2.2
  have h2I : ∫ ω, fderiv ℝ (vbTest W g E (1000 + n) x ψ) ω
        (vbField W n g E x (fun η => χ η • Y η) ω) ∂(μ W (1000 + n)) =
      2 * ∫ ω, batchCut W n χ ω * circleDeriv ψ (flagAct (batchMat W g E (1000 + n) ω) x)
        ∂(μ W (1000 + n)) := by
    simp_rw [hlhs]
    exact integral_const_mul _ _
  have hbound : |∫ ω, vbTest W g E (1000 + n) x ψ ω *
      gaussDiv (vbField W n g E x (fun η => χ η • Y η)) ω ∂(μ W (1000 + n))| ≤
        S * (K ^ 2 * Real.sqrt b + 2 * K ^ 2) := by
    calc _ ≤ ∫ ω, |vbTest W g E (1000 + n) x ψ ω *
          gaussDiv (vbField W n g E x (fun η => χ η • Y η)) ω| ∂(μ W (1000 + n)) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, S * (K ^ 2 * |gaussDiv (fun η => χ η • Y η) (blockAppend W 1000 n ω).1| +
            2 * K ^ 2) ∂(μ W (1000 + n)) :=
          integral_mono hint.abs
            (((hsum.1.const_mul (K ^ 2)).add (integrable_const (2 * K ^ 2))).const_mul S) hrhs
      _ = S * (K ^ 2 * ∫ ω, |gaussDiv (fun η => χ η • Y η) (blockAppend W 1000 n ω).1|
            ∂(μ W (1000 + n)) + 2 * K ^ 2) := by
          rw [integral_const_mul, integral_add (hsum.1.const_mul _) (integrable_const _),
            integral_const_mul, integral_const]
          simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [hsum.2, sq_nonneg K]) hS0
  have h2 : |2 * ∫ ω, batchCut W n χ ω * circleDeriv ψ (flagAct (batchMat W g E (1000 + n) ω) x)
      ∂(μ W (1000 + n))| ≤ S * (K ^ 2 * Real.sqrt b + 2 * K ^ 2) := by
    rw [← h2I, hibp]; exact hbound
  rw [abs_mul, abs_two] at h2
  have he : K ^ 2 * (Real.sqrt b + 2) / 2 * S = S * (K ^ 2 * Real.sqrt b + 2 * K ^ 2) / 2 := by
    ring
  rw [he]
  linarith

end LSBA
