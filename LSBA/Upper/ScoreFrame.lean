import LSBA.Upper.ChosenGenerator
import LSBA.Gauss.RotationDiv
import LSBA.Analysis.ComplexMatrix

/-!
# The rotation frame of the active inputs

The hypotheses of Lemma 9.4 [us:lem:score] at a fixed preparation `(R_4, v_4) = (R, v)`, and the
first step of its proof. For `A ∈ 𝔨_P`, `Z_A` is the direction of the change (9.24)
[su:eq:cut-generator-equivariance] with `U = e^{t A}`: `[A, V_5 - g² R_4]` on `V_5` and
`[A, V_i]` on `V_6, …, V_{q-1}`. Differentiating the equivariance of Lemma 9.3
[su:lem:chosen-generator](ii), (v) gives the chain rule
`Z_A(χ K) = [A, χ K] - ((A v_4) · ∇_{v_4})(χ̂ K̂)`; expanding `χ K` in the frame
`K_k = P (i H_k) P` writes the active part of `χ X` as `Σ_k a_k Z_{K_k}` with
`a_k = ⟨i H_k, χ K⟩`, so that its Gaussian divergence is `Σ_k (a_k b_k - Z_{K_k} a_k)` with
`b_k = δ_G Z_{K_k}`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The hypotheses of Lemma 9.4 [us:lem:score] at the preparation `(R_4, v_4) = (R, v)`:
`W ≥ 1`, `q ≥ 7`, `0 < g ≤ 1`, `R` Hermitian, `v ≠ 0`, `P` an orthogonal projection commuting with
`R`, the family clauses of Lemma 9.3 [su:lem:chosen-generator], and on `{χ ≠ 0}`:
`K* = -K`, `K = P K P`, (9.8) [su:eq:generator-normalization] and `‖K‖²_HS ≤ C_K`; and
`g² ‖P R P‖ ≤ M₀`. -/
def ScoreData (W q : ℕ) (g E M₀ CK : ℝ) (R P : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ)
    (Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ) (χh : Ω W q → (Fin W → ℂ) → ℝ) :
    Prop :=
  1 ≤ W ∧ 7 ≤ q ∧ 0 < g ∧ g ≤ 1 ∧ 0 ≤ M₀ ∧ R.IsHermitian ∧ v ≠ 0 ∧ P.IsHermitian ∧
  P * P = P ∧ P * R = R * P ∧ GenFamily W q g E P R Kh χh ∧
  (∀ ω, χh ω v ≠ 0 → (Kh ω v)ᴴ = -Kh ω v ∧ P * Kh ω v * P = Kh ω v ∧
    IsGenNormalized W g E q R v (Kh ω v) ω ∧ hsSq (Kh ω v) ≤ CK) ∧
  g ^ 2 * ‖P * R * P‖ ≤ M₀

/-- `χ̂ K̂` is differentiable at every `(ω, w)` with `w ≠ 0`: near the support of `χ̂` it is a
product of `C²` maps, away from it it vanishes. -/
private lemma ScoreFrame_diff {W q : ℕ} {g E : ℝ} {P R : Matrix (Fin W) (Fin W) ℂ}
    {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {χh : Ω W q → (Fin W → ℂ) → ℝ}
    (hF : GenFamily W q g E P R Kh χh) (ω : Ω W q) {w : Fin W → ℂ} (hw : w ≠ 0) :
    DifferentiableAt ℝ (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2 • Kh p.1 p.2) (ω, w) := by
  obtain ⟨-, -, -, -, hχ, ⟨G, hGo, hK, hG⟩, -⟩ := hF
  by_cases hp : (ω, w) ∈ tsupport (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2)
  · have hpG := (hG _ hp hw).1
    have h1 : ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => Kh p.1 p.2) (ω, w) :=
      hK.contDiffAt (hGo.mem_nhds hpG)
    have hopen : IsOpen {p : Ω W q × (Fin W → ℂ) | p.2 ≠ 0} :=
      isOpen_ne_fun continuous_snd continuous_const
    have h2 : ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2) (ω, w) :=
      hχ.contDiffAt (hopen.mem_nhds hw)
    exact (h2.smul h1).differentiableAt (by norm_num)
  · rw [notMem_tsupport_iff_eventuallyEq] at hp
    have h0 : (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2 • Kh p.1 p.2) =ᶠ[nhds (ω, w)]
        fun _ => 0 := by
      filter_upwards [hp] with p hp'
      have : χh p.1 p.2 = 0 := hp'
      simp [this]
    exact (differentiableAt_const _).congr_of_eventuallyEq h0

/-- `exp(t A)` is unitary for `A* = -A`. -/
private lemma ScoreFrame_exp_unitary {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : Aᴴ = -A)
    (t : ℝ) : NormedSpace.exp (t • A) ∈ Matrix.unitaryGroup (Fin W) ℂ := by
  have : NormedAlgebra ℚ (Matrix (Fin W) (Fin W) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have h : t • A ∈ skewAdjoint (Matrix (Fin W) (Fin W) ℂ) := by
    rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, hA]
    simp
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint h

/-- `t ↦ exp(t A)` has derivative `A` at `0`. -/
private lemma ScoreFrame_hasDerivAt_exp {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) A 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
  simpa using h

/-- `t ↦ exp(t A)*` has derivative `-A` at `0` for `A* = -A`. -/
private lemma ScoreFrame_hasDerivAt_star_exp {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ}
    (hA : Aᴴ = -A) : HasDerivAt (fun t : ℝ => star (NormedSpace.exp (t • A))) (-A) 0 := by
  have h := (ScoreFrame_hasDerivAt_exp A).star
  simpa [Matrix.star_eq_conjTranspose, hA] using h

/-- `exp(t A)` fixes `1 - P` when `A = P A P` and `P² = P`. -/
private lemma ScoreFrame_exp_fix {W : ℕ} {P A : Matrix (Fin W) (Fin W) ℂ} (hPP : P * P = P)
    (hAP : P * A * P = A) (t : ℝ) : NormedSpace.exp (t • A) * (1 - P) = 1 - P := by
  have hAP' : A * P = A := by
    calc A * P = P * A * P * P := by rw [hAP]
      _ = P * A * P := by simp only [Matrix.mul_assoc, hPP]
      _ = A := hAP
  have hAQ : A * (1 - P) = 0 := by rw [mul_sub, mul_one, hAP', sub_self]
  have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A) * (1 - P)) 0 s := by
    intro s
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A s).mul_const (1 - P)
    simpa [mul_assoc, hAQ] using h
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa using hc

/-- The direction `Z_A` of the change (9.24) [su:eq:cut-generator-equivariance] with
`U = e^{t A}`, in standard coordinates. -/
def rotFrame (W q : ℕ) (g : ℝ) (R A : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) : Ω W q :=
  hermCoord W q fun i =>
    if (i : ℕ) = 4 then
      A * (gueBlock W q ω i - ((g : ℂ) ^ 2) • R) - (gueBlock W q ω i - ((g : ℂ) ^ 2) • R) * A
    else if 5 ≤ (i : ℕ) ∧ (i : ℕ) + 2 ≤ q then A * gueBlock W q ω i - gueBlock W q ω i * A
    else 0

/-- The commutator of a skew-Hermitian matrix with a Hermitian one is Hermitian. -/
private lemma ScoreFrame_comm_isHermitian {W : ℕ} {A B : Matrix (Fin W) (Fin W) ℂ}
    (hA : Aᴴ = -A) (hB : B.IsHermitian) : (A * B - B * A).IsHermitian := by
  have hB' : Bᴴ = B := hB
  change (A * B - B * A)ᴴ = A * B - B * A
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA, hB']
  noncomm_ring

/-- The shift `g² R` is Hermitian. -/
private lemma ScoreFrame_shift_isHermitian {W : ℕ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (g : ℝ) : (((g : ℂ) ^ 2) • R).IsHermitian := by
  change (((g : ℂ) ^ 2) • R)ᴴ = ((g : ℂ) ^ 2) • R
  rw [Matrix.conjTranspose_smul, hR.eq]
  congr 1
  simp

/-- The part of the block tuple moved by `U ↦ U · U*` in `srcAct`: `V_5 - g² R`, `V_i`
(`6 ≤ i ≤ q - 1`), and `0` on the other blocks. -/
private def ScoreFrame_B (W q : ℕ) (g : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q)
    (i : Fin q) : Matrix (Fin W) (Fin W) ℂ :=
  if (i : ℕ) = 4 then gueBlock W q ω i - ((g : ℂ) ^ 2) • R
  else if 5 ≤ (i : ℕ) ∧ (i : ℕ) + 2 ≤ q then gueBlock W q ω i else 0

/-- The part of the block tuple fixed by `srcAct`: `g² R` on block `4`, `0` on the moved blocks
and `V_i` on the unchanged ones. -/
private def ScoreFrame_C (W q : ℕ) (g : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q)
    (i : Fin q) : Matrix (Fin W) (Fin W) ℂ :=
  if (i : ℕ) = 4 then ((g : ℂ) ^ 2) • R
  else if 5 ≤ (i : ℕ) ∧ (i : ℕ) + 2 ≤ q then 0 else gueBlock W q ω i

private lemma ScoreFrame_B_add_C (W q : ℕ) (g : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q)
    (i : Fin q) : ScoreFrame_B W q g R ω i + ScoreFrame_C W q g R ω i = gueBlock W q ω i := by
  unfold ScoreFrame_B ScoreFrame_C
  by_cases h4 : (i : ℕ) = 4
  · simp [h4]
  · by_cases h5 : 5 ≤ (i : ℕ) ∧ (i : ℕ) + 2 ≤ q <;> simp [h4, h5]

private lemma ScoreFrame_B_isHermitian {W q : ℕ} {g : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (ω : Ω W q) (i : Fin q) :
    (ScoreFrame_B W q g R ω i).IsHermitian := by
  unfold ScoreFrame_B
  split_ifs
  · exact (gueBlock_isHermitian W q ω i).sub (ScoreFrame_shift_isHermitian hR g)
  · exact gueBlock_isHermitian W q ω i
  · exact Matrix.isHermitian_zero

/-- `Z_A` in terms of the tuple `B`: block `i` moves along `[A, B_i]`. -/
private lemma ScoreFrame_rotFrame_eq (W q : ℕ) (g : ℝ) (R A : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) : rotFrame W q g R A ω = hermCoord W q fun i =>
      A * ScoreFrame_B W q g R ω i - ScoreFrame_B W q g R ω i * A := by
  unfold rotFrame
  congr 1
  funext i
  unfold ScoreFrame_B
  by_cases h4 : (i : ℕ) = 4
  · simp [h4]
  · by_cases h5 : 5 ≤ (i : ℕ) ∧ (i : ℕ) + 2 ≤ q <;> simp [h4, h5]

/-- `srcAct` in terms of the tuples `B`, `C`. -/
private lemma ScoreFrame_srcAct_eq (W q : ℕ) (g : ℝ) (R U : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) : srcAct W q g R U ω = gueCoord W q fun i =>
      U * ScoreFrame_B W q g R ω i * star U + ScoreFrame_C W q g R ω i := by
  unfold srcAct
  congr 1
  funext i
  unfold ScoreFrame_B ScoreFrame_C
  by_cases h4 : (i : ℕ) = 4
  · simp [h4, Matrix.star_eq_conjTranspose]
  · by_cases h5 : 5 ≤ (i : ℕ) ∧ (i : ℕ) + 2 ≤ q <;> simp [h4, h5, Matrix.star_eq_conjTranspose]

/-- `srcAct` at `U = 1` is the identity. -/
private lemma ScoreFrame_srcAct_one (W q : ℕ) (g : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) : srcAct W q g R 1 ω = ω := by
  rw [ScoreFrame_srcAct_eq]
  have : (fun i : Fin q => (1 : Matrix (Fin W) (Fin W) ℂ) * ScoreFrame_B W q g R ω i * star 1 +
      ScoreFrame_C W q g R ω i) = gueBlock W q ω := by
    funext i
    simp [ScoreFrame_B_add_C]
  rw [this, gueCoord_gueBlock]

/-- `gueBlock` is zero at `ω = 0`. -/
private lemma ScoreFrame_gueBlock_zero (W q : ℕ) (i : Fin q) :
    gueBlock W q (0 : Ω W q) i = 0 := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Pi.zero_apply, Complex.ofReal_zero, zero_div, mul_zero,
    add_zero, sub_zero, Matrix.zero_apply]
  split_ifs <;> simp

/-- For Hermitian `X`, the two coordinate systems agree: `gueCoord X = hermCoord X`. -/
private lemma ScoreFrame_gueCoord_eq_hermCoord {W q : ℕ}
    {X : Fin q → Matrix (Fin W) (Fin W) ℂ} (hX : ∀ i, (X i).IsHermitian) :
    gueCoord W q X = hermCoord W q X := by
  have h : gueBlock W q (hermCoord W q X) = X := by
    funext i
    have := gueBlock_add_smul_hermCoord hX (0 : Ω W q) 1 i
    simpa [ScoreFrame_gueBlock_zero] using this
  calc gueCoord W q X = gueCoord W q (gueBlock W q (hermCoord W q X)) := by rw [h]
    _ = hermCoord W q X := gueCoord_gueBlock _ _ _

/-- `gueCoord` as a continuous real-linear map. -/
private def ScoreFrame_gueCoordL (W q : ℕ) :
    (Fin q → Matrix (Fin W) (Fin W) ℂ) →L[ℝ] Ω W q :=
  LinearMap.toContinuousLinearMap
    { toFun := gueCoord W q
      map_add' := fun V V' => by
        funext x
        simp only [gueCoord, Pi.add_apply, Matrix.add_apply, Complex.add_re, Complex.add_im]
        split_ifs <;> ring
      map_smul' := fun c V => by
        funext x
        simp only [gueCoord, Pi.smul_apply, Matrix.smul_apply, Complex.smul_re, Complex.smul_im,
          smul_eq_mul, RingHom.id_apply]
        split_ifs <;> ring }

/-- `M ↦ M v` as a continuous real-linear map. -/
private def ScoreFrame_mulVecL (W : ℕ) (v : Fin W → ℂ) :
    Matrix (Fin W) (Fin W) ℂ →L[ℝ] (Fin W → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => by
        funext a
        simp [Matrix.mulVec, dotProduct, Finset.smul_sum, mul_assoc] }

/-- The curve `t ↦ srcAct (e^{tA}) ω` has velocity `Z_A(ω)` at `t = 0`. -/
private lemma ScoreFrame_hasDerivAt_srcAct {W q : ℕ} {g : ℝ} {R A : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (hA : Aᴴ = -A) (ω : Ω W q) :
    HasDerivAt (fun t : ℝ => srcAct W q g R (NormedSpace.exp (t • A)) ω)
      (rotFrame W q g R A ω) 0 := by
  have hS : HasDerivAt (fun t : ℝ => fun i : Fin q =>
      NormedSpace.exp (t • A) * ScoreFrame_B W q g R ω i * star (NormedSpace.exp (t • A)) +
        ScoreFrame_C W q g R ω i)
      (fun i => A * ScoreFrame_B W q g R ω i - ScoreFrame_B W q g R ω i * A) 0 := by
    rw [hasDerivAt_pi]
    intro i
    have h3 := (((ScoreFrame_hasDerivAt_exp A).mul_const (ScoreFrame_B W q g R ω i)).mul
      (ScoreFrame_hasDerivAt_star_exp hA)).add_const (ScoreFrame_C W q g R ω i)
    convert h3 using 1
    simp [sub_eq_add_neg]
  have h4 := (ScoreFrame_gueCoordL W q).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hS
  have hX : ∀ i, (A * ScoreFrame_B W q g R ω i - ScoreFrame_B W q g R ω i * A).IsHermitian :=
    fun i => ScoreFrame_comm_isHermitian hA (ScoreFrame_B_isHermitian hR ω i)
  convert h4 using 1
  · funext t
    simp only [Function.comp, ScoreFrame_srcAct_eq]
    rfl
  · rw [ScoreFrame_rotFrame_eq]
    exact (ScoreFrame_gueCoord_eq_hermCoord hX).symm

/-- The curve `t ↦ e^{tA} v` has velocity `A v` at `t = 0`. -/
private lemma ScoreFrame_hasDerivAt_mulVec {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v : Fin W → ℂ) : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A) *ᵥ v) (A *ᵥ v) 0 :=
  (ScoreFrame_mulVecL W v).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (ScoreFrame_hasDerivAt_exp A)

/-- The chain rule of the proof of Lemma 9.4 [us:lem:score]: for `A* = -A`, `A = P A P`,
`Z_A(χ̂ K̂) = [A, χ̂ K̂] - ((A v) · ∇_v)(χ̂ K̂)`. -/
theorem rotFrame_chain {W q : ℕ} {g E M₀ CK : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Ω W q → (Fin W → ℂ) → ℝ} (hD : ScoreData W q g E M₀ CK R P v Kh χh)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : Aᴴ = -A) (hAP : P * A * P = A) (ω : Ω W q) :
    lineDeriv ℝ (fun η => χh η v • Kh η v) ω (rotFrame W q g R A ω) =
      A * (χh ω v • Kh ω v) - (χh ω v • Kh ω v) * A -
        lineDeriv ℝ (fun w => χh ω w • Kh ω w) v (A *ᵥ v) := by
  obtain ⟨-, -, -, -, -, hR, hv, -, hPP, -, hF, -, -⟩ := hD
  have hEq := hF.2.2.2.1
  -- the curve `t ↦ (srcAct (e^{tA}) ω, e^{tA} v)` through `(ω, v)` with velocity `(Z_A ω, A v)`
  have hγd : HasDerivAt (fun t : ℝ => ((srcAct W q g R (NormedSpace.exp (t • A)) ω,
      NormedSpace.exp (t • A) *ᵥ v) : Ω W q × (Fin W → ℂ)))
      (rotFrame W q g R A ω, A *ᵥ v) 0 :=
    (ScoreFrame_hasDerivAt_srcAct hR hA ω).prodMk (ScoreFrame_hasDerivAt_mulVec A v)
  have hγ0 : ((srcAct W q g R (NormedSpace.exp ((0 : ℝ) • A)) ω,
      NormedSpace.exp ((0 : ℝ) • A) *ᵥ v) : Ω W q × (Fin W → ℂ)) = (ω, v) := by
    simp [ScoreFrame_srcAct_one]
  have hdiff := ScoreFrame_diff hF ω hv
  have hcomp : HasDerivAt ((fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2 • Kh p.1 p.2) ∘
      fun t : ℝ => ((srcAct W q g R (NormedSpace.exp (t • A)) ω,
        NormedSpace.exp (t • A) *ᵥ v) : Ω W q × (Fin W → ℂ)))
      (fderiv ℝ (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2 • Kh p.1 p.2) (ω, v)
        (rotFrame W q g R A ω, A *ᵥ v)) 0 := by
    have h1 : HasFDerivAt (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2 • Kh p.1 p.2)
        (fderiv ℝ (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2 • Kh p.1 p.2) (ω, v))
        ((fun t : ℝ => ((srcAct W q g R (NormedSpace.exp (t • A)) ω,
          NormedSpace.exp (t • A) *ᵥ v) : Ω W q × (Fin W → ℂ))) 0) := by
      change HasFDerivAt _ _ ((srcAct W q g R (NormedSpace.exp ((0 : ℝ) • A)) ω,
        NormedSpace.exp ((0 : ℝ) • A) *ᵥ v) : Ω W q × (Fin W → ℂ))
      rw [hγ0]
      exact hdiff.hasFDerivAt
    exact h1.comp_hasDerivAt 0 hγd
  -- along the curve the map is conjugated by `e^{tA}` (equivariance of Lemma 9.3
  -- [su:lem:chosen-generator])
  have hform : ((fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2 • Kh p.1 p.2) ∘
      fun t : ℝ => ((srcAct W q g R (NormedSpace.exp (t • A)) ω,
        NormedSpace.exp (t • A) *ᵥ v) : Ω W q × (Fin W → ℂ))) =
      fun t : ℝ => NormedSpace.exp (t • A) * (χh ω v • Kh ω v) *
        star (NormedSpace.exp (t • A)) := by
    funext t
    obtain ⟨h1, h2⟩ := hEq _ (ScoreFrame_exp_unitary hA t) (ScoreFrame_exp_fix hPP hAP t) ω v
    simp only [Function.comp, h1, h2, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.star_eq_conjTranspose]
  have hrhs : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A) * (χh ω v • Kh ω v) *
      star (NormedSpace.exp (t • A))) (A * (χh ω v • Kh ω v) - (χh ω v • Kh ω v) * A) 0 := by
    have h3 := ((ScoreFrame_hasDerivAt_exp A).mul_const (χh ω v • Kh ω v)).mul
      (ScoreFrame_hasDerivAt_star_exp hA)
    convert h3 using 1
    simp [sub_eq_add_neg]
  rw [hform] at hcomp
  have huniq := hcomp.unique hrhs
  -- the two partial line derivatives
  have hZ : ∀ Z : Ω W q, lineDeriv ℝ (fun η => χh η v • Kh η v) ω Z =
      fderiv ℝ (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2 • Kh p.1 p.2) (ω, v) (Z, 0) := by
    intro Z
    have h1 : HasFDerivAt (fun η : Ω W q => ((η, v) : Ω W q × (Fin W → ℂ)))
        ((ContinuousLinearMap.id ℝ (Ω W q)).prod (0 : Ω W q →L[ℝ] (Fin W → ℂ))) ω :=
      (hasFDerivAt_id ω).prodMk (hasFDerivAt_const v ω)
    have h2 := hdiff.hasFDerivAt.comp ω h1
    refine Eq.trans (h2.hasLineDerivAt Z).lineDeriv ?_
    simp
  have hV : lineDeriv ℝ (fun w => χh ω w • Kh ω w) v (A *ᵥ v) =
      fderiv ℝ (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2 • Kh p.1 p.2) (ω, v) (0, A *ᵥ v) := by
    have h1 : HasFDerivAt (fun w : Fin W → ℂ => ((ω, w) : Ω W q × (Fin W → ℂ)))
        ((0 : (Fin W → ℂ) →L[ℝ] Ω W q).prod (ContinuousLinearMap.id ℝ (Fin W → ℂ))) v :=
      (hasFDerivAt_const ω v).prodMk (hasFDerivAt_id v)
    have h2 := hdiff.hasFDerivAt.comp v h1
    refine Eq.trans (h2.hasLineDerivAt (A *ᵥ v)).lineDeriv ?_
    simp
  have hsplit : ((rotFrame W q g R A ω, A *ᵥ v) : Ω W q × (Fin W → ℂ)) =
      (rotFrame W q g R A ω, 0) + (0, A *ᵥ v) := by simp
  rw [hsplit, map_add] at huniq
  rw [hZ, hV, ← huniq]
  abel

/-- The line derivative of a finite sum of line-differentiable functions. -/
private lemma ScoreFrame_lineDeriv_sum {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset κ) (f : κ → E → ℝ) (x v : E)
    (h : ∀ k ∈ s, LineDifferentiableAt ℝ (f k) x v) :
    lineDeriv ℝ (fun y => ∑ k ∈ s, f k y) x v = ∑ k ∈ s, lineDeriv ℝ (f k) x v := by
  have h1 : ∀ k ∈ s, HasDerivAt (fun t : ℝ => f k (x + t • v)) (lineDeriv ℝ (f k) x v) 0 :=
    fun k hk => (h k hk).hasLineDerivAt
  have h2 := HasDerivAt.sum h1
  have h3 : HasLineDerivAt ℝ (fun y => ∑ k ∈ s, f k y) (∑ k ∈ s, lineDeriv ℝ (f k) x v) x v := by
    unfold HasLineDerivAt
    convert h2 using 1
    funext t
    simp
  exact h3.lineDeriv

/-- `δ_G` of a finite sum of fields with line-differentiable components. -/
private lemma ScoreFrame_gaussDiv_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι] (s : Finset κ)
    (Y : κ → (ι → ℝ) → ι → ℝ) (x : ι → ℝ)
    (h : ∀ k ∈ s, ∀ i, LineDifferentiableAt ℝ (fun y => Y k y i) x (Pi.single i 1)) :
    gaussDiv (fun y => ∑ k ∈ s, Y k y) x = ∑ k ∈ s, gaussDiv (Y k) x := by
  unfold gaussDiv
  have hl : ∀ i, lineDeriv ℝ (fun y => ∑ k ∈ s, Y k y i) x (Pi.single i 1) =
      ∑ k ∈ s, lineDeriv ℝ (fun y => Y k y i) x (Pi.single i 1) := fun i =>
    ScoreFrame_lineDeriv_sum s (fun k y => Y k y i) x (Pi.single i 1) (fun k hk => h k hk i)
  simp only [Finset.sum_apply, hl, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_comm

/-- `B ↦ ⟨A, B⟩` as a continuous real-linear map. -/
private def ScoreFrame_hsInnerL {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => hsInner A B
      map_add' := fun B C => by
        simp only [hsInner, Matrix.add_apply, mul_add, Complex.add_re, Finset.sum_add_distrib]
      map_smul' := fun c B => by
        simp only [hsInner, Matrix.smul_apply, Complex.real_smul, RingHom.id_apply, smul_eq_mul,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [mul_left_comm, Complex.re_ofReal_mul] }

/-- `⟨H, -i F⟩ = ⟨i H, F⟩`. -/
private lemma ScoreFrame_hsInner_smul_I {W : ℕ} (H F : Matrix (Fin W) (Fin W) ℂ) :
    hsInner H ((-Complex.I) • F) = hsInner (Complex.I • H) F := by
  unfold hsInner
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, star_mul', Complex.star_def,
    Complex.conj_I]
  congr 1
  ring

/-- The frame expansion `F = Σ_k ⟨i H_k, F⟩ K_k` of a skew-Hermitian `F = P F P`, with
`K_k = P (i H_k) P`. -/
private lemma ScoreFrame_frame {W : ℕ} {P F : Matrix (Fin W) (Fin W) ℂ} (hF : Fᴴ = -F)
    (hPF : P * F * P = F) :
    F = ∑ k, hsInner (Complex.I • hermBasis W k) F • skewProjBasis P k := by
  have hM : ((-Complex.I) • F).IsHermitian := by
    change ((-Complex.I) • F)ᴴ = (-Complex.I) • F
    rw [Matrix.conjTranspose_smul, hF]
    simp
  have h1 := (hermBasis_parseval W ((-Complex.I) • F)).2 hM
  have h2 : F = Complex.I • ((-Complex.I) • F) := by simp [smul_smul]
  have h3 : F = ∑ k, ((hsInner (Complex.I • hermBasis W k) F : ℝ) : ℂ) •
      (Complex.I • hermBasis W k) := by
    conv_lhs => rw [h2, h1]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm, ScoreFrame_hsInner_smul_I]
  calc F = P * F * P := hPF.symm
    _ = ∑ k, ((hsInner (Complex.I • hermBasis W k) F : ℝ) : ℂ) •
        (P * (Complex.I • hermBasis W k) * P) := by
      conv_lhs => rw [h3]
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = _ := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.coe_smul]
      rfl

/-- `A ↦ Z_A(ω)` is real-linear. -/
private def ScoreFrame_rotL (W q : ℕ) (g : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) :
    Matrix (Fin W) (Fin W) ℂ →ₗ[ℝ] Ω W q where
  toFun A := rotFrame W q g R A ω
  map_add' A A' := by
    rw [ScoreFrame_rotFrame_eq, ScoreFrame_rotFrame_eq, ScoreFrame_rotFrame_eq,
      ← (hermCoord_isLinearMap W q).map_add]
    congr 1
    funext i
    simp only [Matrix.add_mul, Matrix.mul_add, Pi.add_apply]
    abel
  map_smul' c A := by
    rw [ScoreFrame_rotFrame_eq, ScoreFrame_rotFrame_eq, RingHom.id_apply,
      ← (hermCoord_isLinearMap W q).map_smul]
    congr 1
    funext i
    simp only [Matrix.smul_mul, Matrix.mul_smul, Pi.smul_apply, smul_sub]

/-- `hermCoord` as a continuous real-linear map. -/
private def ScoreFrame_hermCoordL (W q : ℕ) :
    (Fin q → Matrix (Fin W) (Fin W) ℂ) →L[ℝ] Ω W q :=
  LinearMap.toContinuousLinearMap (IsLinearMap.mk' (hermCoord W q) (hermCoord_isLinearMap W q))

/-- `ω ↦ V_i(ω)` as a continuous real-linear map. -/
private def ScoreFrame_gueBlockL (W q : ℕ) (i : Fin q) :
    Ω W q →L[ℝ] Matrix (Fin W) (Fin W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ω => gueBlock W q ω i
      map_add' := fun ω ω' => by
        ext α β
        simp only [gueBlock, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
        split_ifs <;> push_cast <;> ring
      map_smul' := fun c ω => by
        ext α β
        simp only [gueBlock, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
          Complex.real_smul, RingHom.id_apply]
        split_ifs <;> push_cast <;> ring }

/-- `ω ↦ Z_A(ω)` is differentiable (it is affine). -/
private lemma ScoreFrame_rotFrame_differentiable (W q : ℕ) (g : ℝ)
    (R A : Matrix (Fin W) (Fin W) ℂ) : Differentiable ℝ (rotFrame W q g R A) := by
  have hV : ∀ i, Differentiable ℝ fun ω : Ω W q => gueBlock W q ω i :=
    fun i => (ScoreFrame_gueBlockL W q i).differentiable
  have hB : ∀ i, Differentiable ℝ fun ω : Ω W q => ScoreFrame_B W q g R ω i := by
    intro i
    unfold ScoreFrame_B
    by_cases h4 : (i : ℕ) = 4
    · simp only [h4, ite_true]
      exact (hV i).sub (differentiable_const _)
    · by_cases h5 : 5 ≤ (i : ℕ) ∧ (i : ℕ) + 2 ≤ q
      · simp only [h4, h5, ite_false]
        exact hV i
      · simp only [h4, h5, ite_false]
        exact differentiable_const _
  have h : rotFrame W q g R A = fun ω => ScoreFrame_hermCoordL W q
      (fun i => A * ScoreFrame_B W q g R ω i - ScoreFrame_B W q g R ω i * A) := by
    funext ω
    rw [ScoreFrame_rotFrame_eq]
    rfl
  rw [h]
  refine (ScoreFrame_hermCoordL W q).differentiable.comp (differentiable_pi.2 fun i => ?_)
  exact ((differentiable_const A).mul (hB i)).sub ((hB i).mul (differentiable_const A))

/-- For `q ≥ 7`, the active part of `smallField` is `Z_K`. -/
private lemma ScoreFrame_smallField_eq {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hq : 7 ≤ q) (v : Fin W → ℂ) (K : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) :
    hermCoord W q (fun i => if (i : ℕ) + 1 < q then smallField W g E q R v K ω i else 0) =
      rotFrame W q g R K ω := by
  unfold rotFrame
  congr 1
  funext i
  by_cases h4 : (i : ℕ) = 4
  · have h1 : 5 < q := by omega
    simp [smallField, h4, h1]
  · by_cases h5 : 5 ≤ (i : ℕ) ∧ (i : ℕ) + 2 ≤ q
    · have h1 : (i : ℕ) + 1 < q := by omega
      have h2 : ¬ (i : ℕ) < 4 := by omega
      simp [smallField, h4, h5, h1, h2]
    · by_cases h1 : (i : ℕ) + 1 < q
      · have h2 : (i : ℕ) < 4 := by omega
        simp [smallField, h4, h5, h1, h2]
      · simp [h4, h5, h1]

/-- The active part of `δ_G(χ X)` (proof of Lemma 9.4 [us:lem:score]):
`δ_act = Σ_k (a_k b_k - Z_{K_k} a_k)` with `a_k = ⟨i H_k, χ K⟩`, `b_k = δ_G Z_{K_k}`. -/
theorem active_gaussDiv_eq {W q : ℕ} {g E M₀ CK : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Ω W q → (Fin W → ℂ) → ℝ} (hD : ScoreData W q g E M₀ CK R P v Kh χh) (ω : Ω W q) :
    gaussDiv (fun η => χh η v • hermCoord W q fun i =>
        if (i : ℕ) + 1 < q then smallField W g E q R v (Kh η v) η i else 0) ω =
      ∑ k, (hsInner (Complex.I • hermBasis W k) (χh ω v • Kh ω v) *
          gaussDiv (rotFrame W q g R (skewProjBasis P k)) ω -
        lineDeriv ℝ (fun η => hsInner (Complex.I • hermBasis W k) (χh η v • Kh η v)) ω
          (rotFrame W q g R (skewProjBasis P k) ω)) := by
  obtain ⟨-, hq, -, -, -, -, hv, -, -, -, hF, hK, -⟩ := hD
  have hFs : ∀ η : Ω W q, (χh η v • Kh η v)ᴴ = -(χh η v • Kh η v) ∧
      P * (χh η v • Kh η v) * P = χh η v • Kh η v := by
    intro η
    by_cases hχ : χh η v = 0
    · simp [hχ]
    · obtain ⟨hk1, hk2, -, -⟩ := hK η hχ
      refine ⟨?_, ?_⟩
      · rw [Matrix.conjTranspose_smul, hk1]
        simp
      · rw [Matrix.mul_smul, Matrix.smul_mul, hk2]
  -- the integrand is `Σ_k a_k Z_{K_k}`
  have hY : ∀ η : Ω W q, χh η v • hermCoord W q (fun i =>
      if (i : ℕ) + 1 < q then smallField W g E q R v (Kh η v) η i else 0) =
      ∑ k, hsInner (Complex.I • hermBasis W k) (χh η v • Kh η v) •
        rotFrame W q g R (skewProjBasis P k) η := by
    intro η
    rw [ScoreFrame_smallField_eq hq]
    have h1 : χh η v • rotFrame W q g R (Kh η v) η = rotFrame W q g R (χh η v • Kh η v) η :=
      ((ScoreFrame_rotL W q g R η).map_smul (χh η v) (Kh η v)).symm
    rw [h1]
    conv_lhs => rw [ScoreFrame_frame (hFs η).1 (hFs η).2]
    change ScoreFrame_rotL W q g R η _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
  have hFd : DifferentiableAt ℝ (fun η : Ω W q => χh η v • Kh η v) ω := by
    have h1 := ScoreFrame_diff hF ω hv
    have h2 : DifferentiableAt ℝ (fun η : Ω W q => ((η, v) : Ω W q × (Fin W → ℂ))) ω :=
      differentiableAt_id.prodMk (differentiableAt_const v)
    exact h1.comp ω h2
  have hZd : ∀ k, DifferentiableAt ℝ (rotFrame W q g R (skewProjBasis P k)) ω :=
    fun k => ScoreFrame_rotFrame_differentiable W q g R _ ω
  have had : ∀ k, DifferentiableAt ℝ
      (fun η : Ω W q => hsInner (Complex.I • hermBasis W k) (χh η v • Kh η v)) ω :=
    fun k => (ScoreFrame_hsInnerL _).differentiableAt.comp ω hFd
  have hterm : ∀ k, DifferentiableAt ℝ (fun η : Ω W q =>
      hsInner (Complex.I • hermBasis W k) (χh η v • Kh η v) •
        rotFrame W q g R (skewProjBasis P k) η) ω :=
    fun k => (had k).smul (hZd k)
  have hfun : (fun η : Ω W q => χh η v • hermCoord W q (fun i =>
      if (i : ℕ) + 1 < q then smallField W g E q R v (Kh η v) η i else 0)) =
      fun η => ∑ k, hsInner (Complex.I • hermBasis W k) (χh η v • Kh η v) •
        rotFrame W q g R (skewProjBasis P k) η := funext hY
  rw [hfun, ScoreFrame_gaussDiv_sum _ (fun k η => hsInner (Complex.I • hermBasis W k)
    (χh η v • Kh η v) • rotFrame W q g R (skewProjBasis P k) η) ω
    (fun k _ i => (differentiableAt_pi.1 (hterm k) i).lineDifferentiableAt)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gaussDiv_smul (f := fun η : Ω W q => hsInner (Complex.I • hermBasis W k)
      (χh η v • Kh η v)) (Y := rotFrame W q g R (skewProjBasis P k)) (had k)
    (fun i => (differentiableAt_pi.1 (hZd k) i).lineDifferentiableAt),
    (had k).lineDeriv_eq_fderiv]

end LSBA
