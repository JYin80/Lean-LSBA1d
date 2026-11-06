import LSBA.Upper.SmallScorePrefix
import LSBA.Upper.SmallCutLocal
import LSBA.Upper.SmallContractionRates
import LSBA.Gauss.PrefixProduct

/-!
# The Gaussian divergence bound of Lemma 8.12 [up:lem:small-contraction]

The second moment of the Gaussian divergence (8.33) [up:eq:gaussian-divergence] of the field of
Lemma 8.12 [up:lem:small-contraction] (proof of Lemma 8.12 [up:lem:small-contraction]): Lemma 9.4
[us:lem:score] at the
preparation of each sample, averaged over the preparation blocks, with the averaged clauses of
Lemma 9.3 [su:lem:chosen-generator]: `𝔼 χ² ‖K‖²_HS ≤ C σ` (9.25) [su:eq:pair-generator-size] and
`𝔼[‖P v_4‖² ‖K‖²_HS ‖∇_{v_4} χ̂‖²] ≤ C` (9.30) [su:eq:pair-cutoff-derivative]. The source energy
is then at most `6 C³ W σ + 2 C` ((9.38) [su:eq:pair-source-energy]), and
`𝔼 |δ_G(χ X)|² ≤ C_s (6 C³ W σ + 2 C) + C_s C W (1 + M₀²) σ + 36 C⁴ W⁻¹ g⁴ + C_s W M₀ e^{-c W}`
(the first inequality of (9.39) [su:eq:local], and (9.40) [nc:eq:finalscore], before the choice of
the regime).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Auxiliary lemmas -/

/-- Samples that agree on the coordinates of the blocks `< p` have the same blocks `< p`. -/
private lemma SmallCutDiv_gueBlock_eq_lt {W q p : ℕ} {ω₁ ω₂ : Ω W q}
    (h : ∀ k : Fin q × Fin W × Fin W, (k.1 : ℕ) < p → ω₁ k = ω₂ k) (i : Fin q)
    (hi : (i : ℕ) < p) : gueBlock W q ω₁ i = gueBlock W q ω₂ i := by
  have he : ∀ α β, ω₁ (i, α, β) = ω₂ (i, α, β) := fun α β => h (i, α, β) hi
  ext α β
  simp only [gueBlock, Matrix.of_apply, he]

/-- Samples that agree on the coordinates of the blocks `≥ p` have the same blocks `≥ p`. -/
private lemma SmallCutDiv_gueBlock_eq_ge {W q p : ℕ} {ω₁ ω₂ : Ω W q}
    (h : ∀ k : Fin q × Fin W × Fin W, p ≤ (k.1 : ℕ) → ω₁ k = ω₂ k) (i : Fin q)
    (hi : p ≤ (i : ℕ)) : gueBlock W q ω₁ i = gueBlock W q ω₂ i := by
  have he : ∀ α β, ω₁ (i, α, β) = ω₂ (i, α, β) := fun α β => h (i, α, β) hi
  ext α β
  simp only [gueBlock, Matrix.of_apply, he]

/-- Under the family clauses of Lemma 9.3 [su:lem:chosen-generator], the generator `K̂` and the
cutoff `χ̂` depend only on the coordinates of the blocks `V_5, …, V_q`. -/
private lemma SmallCutDiv_family_congr {W q : ℕ} {g E : ℝ} {P R : Matrix (Fin W) (Fin W) ℂ}
    {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {χh : Ω W q → (Fin W → ℂ) → ℝ}
    (hF : GenFamily W q g E P R Kh χh) {ω₁ ω₂ : Ω W q}
    (h : ∀ k : Fin q × Fin W × Fin W, 4 ≤ (k.1 : ℕ) → ω₁ k = ω₂ k) :
    Kh ω₁ = Kh ω₂ ∧ χh ω₁ = χh ω₂ := by
  obtain ⟨hF1, -⟩ := hF
  have hw := fun w => hF1 ω₁ ω₂ (fun i hi _ => SmallCutDiv_gueBlock_eq_ge h i hi) w
  exact ⟨funext fun w => (hw w).1, funext fun w => (hw w).2⟩

/-- Conditioning on the preparation blocks (proof of Lemma 8.12 [up:lem:small-contraction]) for a
function `F ω' ω` of the preparation `(pre, R_4, v_4)` of `ω'` and the sample `ω`, vanishing where
`pre ω' = 0` and depending on `ω` only through the blocks `≥ 4` where `pre ω' ≠ 0`. -/
private lemma SmallCutDiv_diag {W q : ℕ} {g E C σ M₀ : ℝ} {x : IsoFlag W}
    {Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} {pre : Ω W q → ℝ}
    {Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ} {vf : Ω W q → Fin W → ℂ}
    {Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ}
    (hG : ChosenGenerator W q g E x Pf C σ M₀ pre Rf vf Kh χh) {F : Ω W q → Ω W q → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F))
    (hdep : ∀ ω₁ ω₂ ω : Ω W q, pre ω₁ = pre ω₂ → Rf ω₁ = Rf ω₂ → vf ω₁ = vf ω₂ →
      F ω₁ ω = F ω₂ ω)
    (hzero : ∀ ω' ω : Ω W q, pre ω' = 0 → F ω' ω = 0)
    (hcongr : ∀ ω' : Ω W q, pre ω' ≠ 0 → ∀ ω₁ ω₂ : Ω W q,
      (∀ k : Fin q × Fin W × Fin W, 4 ≤ (k.1 : ℕ) → ω₁ k = ω₂ k) → F ω' ω₁ = F ω' ω₂) :
    ∫⁻ ω, F ω ω ∂(μ W q) = ∫⁻ ω', ∫⁻ ω, F ω' ω ∂(μ W q) ∂(μ W q) := by
  obtain ⟨-, -, -, -, hpre, -⟩ := hG
  refine lintegral_prefix_diag 4 hF (fun ω₁ ω₂ ω h => ?_) (fun ω' ω₁ ω₂ h => ?_)
  · obtain ⟨h1, h2, h3⟩ := hpre ω₁ ω₂ fun i hi => SmallCutDiv_gueBlock_eq_lt h i hi
    exact hdep ω₁ ω₂ ω h1 h2 h3
  · by_cases hp : pre ω' = 0
    · rw [hzero _ _ hp, hzero _ _ hp]
    · exact hcongr ω' hp ω₁ ω₂ h

/-- The linear combination of three nonnegative measurable functions inside `ofReal`, integrated
term by term. -/
private lemma SmallCutDiv_lintegral_comb {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {u₁ u₂ u₃ : α → ℝ} (h₁ : Measurable u₁) (h₂ : Measurable u₂) (h₃ : Measurable u₃)
    (n₁ : ∀ a, 0 ≤ u₁ a) (n₂ : ∀ a, 0 ≤ u₂ a) (n₃ : ∀ a, 0 ≤ u₃ a)
    {b₁ b₂ b₃ : ℝ} (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃) :
    ∫⁻ a, ENNReal.ofReal (b₁ * u₁ a + b₂ * u₂ a + b₃ * u₃ a) ∂ν =
      ENNReal.ofReal b₁ * ∫⁻ a, ENNReal.ofReal (u₁ a) ∂ν +
        ENNReal.ofReal b₂ * ∫⁻ a, ENNReal.ofReal (u₂ a) ∂ν +
        ENNReal.ofReal b₃ * ∫⁻ a, ENNReal.ofReal (u₃ a) ∂ν := by
  have e : ∀ a, ENNReal.ofReal (b₁ * u₁ a + b₂ * u₂ a + b₃ * u₃ a) =
      ENNReal.ofReal b₁ * ENNReal.ofReal (u₁ a) + ENNReal.ofReal b₂ * ENNReal.ofReal (u₂ a) +
        ENNReal.ofReal b₃ * ENNReal.ofReal (u₃ a) := fun a => by
    rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg hb₁ (n₁ a)) (mul_nonneg hb₂ (n₂ a)))
      (mul_nonneg hb₃ (n₃ a)), ENNReal.ofReal_add (mul_nonneg hb₁ (n₁ a)) (mul_nonneg hb₂ (n₂ a)),
      ENNReal.ofReal_mul hb₁, ENNReal.ofReal_mul hb₂, ENNReal.ofReal_mul hb₃]
  have m₁ : Measurable fun a => ENNReal.ofReal (u₁ a) := ENNReal.measurable_ofReal.comp h₁
  have m₂ : Measurable fun a => ENNReal.ofReal (u₂ a) := ENNReal.measurable_ofReal.comp h₂
  have m₃ : Measurable fun a => ENNReal.ofReal (u₃ a) := ENNReal.measurable_ofReal.comp h₃
  simp only [e]
  rw [lintegral_add_left (f := fun a => ENNReal.ofReal b₁ * ENNReal.ofReal (u₁ a) +
      ENNReal.ofReal b₂ * ENNReal.ofReal (u₂ a)) ((m₁.const_mul _).add (m₂.const_mul _)),
    lintegral_add_left (f := fun a => ENNReal.ofReal b₁ * ENNReal.ofReal (u₁ a))
      (m₁.const_mul _), lintegral_const_mul _ m₁, lintegral_const_mul _ m₂,
    lintegral_const_mul _ m₃]

/-- The squared cutoff `(pre · χ̂)²` of Lemma 8.12 [up:lem:small-contraction] at the preparation of
`ω'`, evaluated at the sample `ω`. -/
private def SmallCutDiv_u1 {W q : ℕ} (pre : Ω W q → ℝ)
    (Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ) (vf : Ω W q → Fin W → ℂ)
    (χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ) (ω' ω : Ω W q) : ℝ :=
  (pre ω' * χh (Rf ω') ω (vf ω')) ^ 2

/-- The integrand `(pre · χ̂)² ‖K̂‖²_HS` of (9.25) [su:eq:pair-generator-size] at the preparation of
`ω'`, evaluated at the sample `ω`. -/
private def SmallCutDiv_u2 {W q : ℕ} (pre : Ω W q → ℝ)
    (Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ) (vf : Ω W q → Fin W → ℂ)
    (Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ)
    (χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ) (ω' ω : Ω W q) : ℝ :=
  (pre ω' * χh (Rf ω') ω (vf ω')) ^ 2 * hsSq (Kh (Rf ω') ω (vf ω'))

/-- The integrand `pre ‖P v_4‖² ‖K̂‖²_HS ‖∇_{v_4} χ̂‖²` of (9.30) [su:eq:pair-cutoff-derivative] at
the preparation of `ω'`, evaluated at the sample `ω`. -/
private def SmallCutDiv_u3 {W q : ℕ} (Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ)
    (pre : Ω W q → ℝ) (Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ) (vf : Ω W q → Fin W → ℂ)
    (Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ)
    (χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ) (ω' ω : Ω W q) : ℝ :=
  pre ω' * (∑ i, ‖(Pf (Rf ω') *ᵥ vf ω') i‖ ^ 2) * hsSq (Kh (Rf ω') ω (vf ω')) *
    tangGradSq (Pf (Rf ω')) (vf ω') (χh (Rf ω') ω)

/-- `hsSq` is a continuous, hence measurable, function of the matrix. -/
private lemma SmallCutDiv_measurable_hsSq {W : ℕ} :
    Measurable fun A : Matrix (Fin W) (Fin W) ℂ => hsSq A := by
  unfold hsSq
  refine (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_).measurable
  exact (continuous_norm.comp ((continuous_apply b).comp (continuous_apply a))).pow 2

/-- The three integrands are jointly measurable in `(ω', ω)`. -/
private lemma SmallCutDiv_measurable_u {W q : ℕ} {g E C σ M₀ : ℝ} {x : IsoFlag W}
    {Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} {pre : Ω W q → ℝ}
    {Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ} {vf : Ω W q → Fin W → ℂ}
    {Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ}
    (hG : ChosenGenerator W q g E x Pf C σ M₀ pre Rf vf Kh χh) :
    Measurable (fun p : Ω W q × Ω W q => SmallCutDiv_u1 pre Rf vf χh p.1 p.2) ∧
      Measurable (fun p : Ω W q × Ω W q => SmallCutDiv_u2 pre Rf vf Kh χh p.1 p.2) ∧
      Measurable (fun p : Ω W q × Ω W q => SmallCutDiv_u3 Pf pre Rf vf Kh χh p.1 p.2) := by
  have hTG := measurable_tangGradSq_smallCut hG
  obtain ⟨-, hpm, hRm, hvm, -, -, hPm, hKm, hχm, -⟩ := hG
  have hp1 : Measurable fun p : Ω W q × Ω W q => pre p.1 := hpm.comp measurable_fst
  have hR : Measurable fun p : Ω W q × Ω W q => Rf p.1 := hRm.comp measurable_fst
  have hv : Measurable fun p : Ω W q × Ω W q => vf p.1 := hvm.comp measurable_fst
  have hχ : Measurable fun p : Ω W q × Ω W q => χh (Rf p.1) p.2 (vf p.1) :=
    hχm.comp (hR.prodMk (measurable_snd.prodMk hv))
  have hK : Measurable fun p : Ω W q × Ω W q => Kh (Rf p.1) p.2 (vf p.1) :=
    hKm.comp (hR.prodMk (measurable_snd.prodMk hv))
  have hsK : Measurable fun p : Ω W q × Ω W q => hsSq (Kh (Rf p.1) p.2 (vf p.1)) :=
    SmallCutDiv_measurable_hsSq.comp hK
  have hPv : Measurable fun p : Ω W q × Ω W q => Pf (Rf p.1) *ᵥ vf p.1 :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp
      ((hPm.comp hR).prodMk hv)
  have hPs : Measurable fun p : Ω W q × Ω W q => ∑ i, ‖(Pf (Rf p.1) *ᵥ vf p.1) i‖ ^ 2 :=
    Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hPv).norm.pow_const 2
  have h1 : Measurable fun p : Ω W q × Ω W q => (pre p.1 * χh (Rf p.1) p.2 (vf p.1)) ^ 2 :=
    (hp1.mul hχ).pow_const 2
  refine ⟨h1, h1.mul hsK, ?_⟩
  have hid : (fun p : Ω W q × Ω W q => SmallCutDiv_u3 Pf pre Rf vf Kh χh p.1 p.2) =
      fun p => (∑ i, ‖(Pf (Rf p.1) *ᵥ vf p.1) i‖ ^ 2) * hsSq (Kh (Rf p.1) p.2 (vf p.1)) *
        (pre p.1 * tangGradSq (Pf (Rf p.1)) (vf p.1) (χh (Rf p.1) p.2)) := by
    funext p
    unfold SmallCutDiv_u3
    ring
  rw [hid]
  exact (hPs.mul hsK).mul hTG

/-- The second moment of the Gaussian divergence of the field of Lemma 8.12
[up:lem:small-contraction] in terms of `C`, `σ` and `M₀` of Lemma 9.3 [su:lem:chosen-generator];
the constants `C_s, c` depend only on `C`. -/
theorem lintegral_gaussDiv_smallCut_le (C : ℝ) (hC : 0 < C) :
    ∃ Cs c : ℝ, 0 < Cs ∧ 0 < c ∧ ∀ (W q : ℕ) (g E σ M₀ : ℝ) (x : IsoFlag W)
      (Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ) (pre : Ω W q → ℝ)
      (Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ) (vf : Ω W q → Fin W → ℂ)
      (Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ)
      (χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ),
      1 ≤ W → 7 ≤ q → 0 < g → g ≤ 1 → 0 ≤ σ → 0 ≤ M₀ →
      ChosenGenerator W q g E x Pf C σ M₀ pre Rf vf Kh χh →
      ∫⁻ ω, ‖gaussDiv (fun η => smallCut pre Rf vf χh η • smallVec W g E q Rf vf Kh η) ω‖ₑ ^ 2
          ∂(μ W q) ≤
        ENNReal.ofReal (smallDivBound Cs c C W g σ M₀) := by
  obtain ⟨Cs, c, hCs, hc, hbound⟩ := lintegral_gaussDiv_smallScore_le C hC
  refine ⟨Cs, c, hCs, hc, fun W q g E σ M₀ x Pf pre Rf vf Kh χh hW hq hg hg1 hσ hM₀ hG => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨hp01, -, -, -, -, -, -, -, -, hfam, -, -, h13, h14⟩ := id hG
  obtain ⟨hu1m, hu2m, hu3m⟩ := SmallCutDiv_measurable_u hG
  obtain ⟨hcut0, hcut1, -⟩ := smallCut_basic hG
  set u1 := SmallCutDiv_u1 pre Rf vf χh with hu1def
  set u2 := SmallCutDiv_u2 pre Rf vf Kh χh with hu2def
  set u3 := SmallCutDiv_u3 Pf pre Rf vf Kh χh with hu3def
  -- nonnegativity of the three integrands
  have n1 : ∀ ω' ω, 0 ≤ u1 ω' ω := fun ω' ω => sq_nonneg _
  have hs0 : ∀ {A : Matrix (Fin W) (Fin W) ℂ}, 0 ≤ hsSq A := fun {A} => by
    unfold hsSq; positivity
  have n2 : ∀ ω' ω, 0 ≤ u2 ω' ω := fun ω' ω => mul_nonneg (sq_nonneg _) hs0
  have n3 : ∀ ω' ω, 0 ≤ u3 ω' ω := fun ω' ω => by
    have hp : 0 ≤ pre ω' := by rcases hp01 ω' with h | h <;> simp [h]
    have hT : 0 ≤ tangGradSq (Pf (Rf ω')) (vf ω') (χh (Rf ω') ω) := by
      unfold tangGradSq; positivity
    have hP : 0 ≤ ∑ i, ‖(Pf (Rf ω') *ᵥ vf ω') i‖ ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hp hP) hs0) hT
  -- the weights
  obtain ⟨b1, hb1⟩ : ∃ b : ℝ, b = Cs * (2 * C ^ 3 * W * σ) := ⟨_, rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ b : ℝ, b = Cs * (4 * C ^ 2 * W) + Cs * W * (1 + M₀ ^ 2) := ⟨_, rfl⟩
  obtain ⟨b3, hb3⟩ : ∃ b : ℝ, b = 2 * Cs := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ b : ℝ,
      b = 36 * C ^ 4 * (W : ℝ)⁻¹ * g ^ 4 + Cs * W * M₀ * Real.exp (-c * W) := ⟨_, rfl⟩
  have hb1' : 0 ≤ b1 := by rw [hb1]; positivity
  have hb2' : 0 ≤ b2 := by rw [hb2]; positivity
  have hb3' : 0 ≤ b3 := by rw [hb3]; positivity
  have hc0' : 0 ≤ c0 := by rw [hc0]; positivity
  obtain ⟨S, hS⟩ : ∃ S : Ω W q → Ω W q → ℝ,
      ∀ ω' ω, S ω' ω = b1 * u1 ω' ω + b2 * u2 ω' ω + b3 * u3 ω' ω := ⟨fun _ _ => _, fun _ _ => rfl⟩
  have hSm : Measurable (fun p : Ω W q × Ω W q => S p.1 p.2) := by
    have : (fun p : Ω W q × Ω W q => S p.1 p.2) =
        fun p => b1 * u1 p.1 p.2 + b2 * u2 p.1 p.2 + b3 * u3 p.1 p.2 := funext fun p => hS p.1 p.2
    rw [this]
    exact ((hu1m.const_mul b1).add (hu2m.const_mul b2)).add (hu3m.const_mul b3)
  have hmω : ∀ ω' : Ω W q, Measurable (u1 ω') ∧ Measurable (u2 ω') ∧ Measurable (u3 ω') :=
    fun ω' => ⟨hu1m.comp (measurable_prodMk_left (x := ω')),
      hu2m.comp (measurable_prodMk_left (x := ω')), hu3m.comp (measurable_prodMk_left (x := ω'))⟩
  have hmd : Measurable (fun ω : Ω W q => u1 ω ω) ∧ Measurable (fun ω : Ω W q => u2 ω ω) ∧
      Measurable (fun ω : Ω W q => u3 ω ω) :=
    ⟨hu1m.comp (measurable_id.prodMk measurable_id), hu2m.comp (measurable_id.prodMk measurable_id),
      hu3m.comp (measurable_id.prodMk measurable_id)⟩
  have e1 : ENNReal.ofReal b1 = ENNReal.ofReal Cs * ENNReal.ofReal (2 * C ^ 3 * W * σ) := by
    rw [hb1, ENNReal.ofReal_mul hCs.le]
  have e2 : ENNReal.ofReal b2 = ENNReal.ofReal Cs * ENNReal.ofReal (4 * C ^ 2 * W) +
      ENNReal.ofReal (Cs * W * (1 + M₀ ^ 2)) := by
    rw [hb2, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hCs.le]
  have e3 : ENNReal.ofReal b3 = ENNReal.ofReal 2 * ENNReal.ofReal Cs := by
    rw [hb3, ENNReal.ofReal_mul (by norm_num)]
  have e0 : ENNReal.ofReal c0 = ENNReal.ofReal (36 * C ^ 4 * (W : ℝ)⁻¹ * g ^ 4) +
      ENNReal.ofReal (Cs * W * M₀ * Real.exp (-c * W)) := by
    rw [hc0, ENNReal.ofReal_add (by positivity) (by positivity)]
  -- Lemma 9.4 [us:lem:score] at the preparation of `ω'`, weighted by `pre ω'`
  obtain ⟨Gf, hGf⟩ : ∃ Gf : Ω W q → Ω W q → ℝ≥0∞, ∀ ω' ω, Gf ω' ω =
      ‖pre ω' * gaussDiv (smallScoreField W g E q (Rf ω') (vf ω') (Kh (Rf ω'))
        (χh (Rf ω'))) ω‖ₑ ^ 2 := ⟨fun _ _ => _, fun _ _ => rfl⟩
  have hGfm : Measurable (Function.uncurry Gf) := by
    have : Function.uncurry Gf = fun p : Ω W q × Ω W q =>
        ‖pre p.1 * gaussDiv (smallScoreField W g E q (Rf p.1) (vf p.1) (Kh (Rf p.1))
          (χh (Rf p.1))) p.2‖ₑ ^ 2 := funext fun p => hGf p.1 p.2
    rw [this]
    exact (measurable_smallCut_field hG).2.enorm.pow_const 2
  have hdiagG : ∫⁻ ω, Gf ω ω ∂(μ W q) = ∫⁻ ω', ∫⁻ ω, Gf ω' ω ∂(μ W q) ∂(μ W q) := by
    refine SmallCutDiv_diag hG hGfm (fun ω₁ ω₂ ω h1 h2 h3 => ?_) (fun ω' ω h => ?_)
      (fun ω' hp ω₁ ω₂ h => ?_)
    · rw [hGf, hGf, h1, h2, h3]
    · rw [hGf, h]
      simp
    · rw [hGf, hGf, gaussDiv_smallScoreField_congr (hfam ω' hp).2.2.2 h]
  have hdiagS : ∫⁻ ω, ENNReal.ofReal (S ω ω) ∂(μ W q) =
      ∫⁻ ω', ∫⁻ ω, ENNReal.ofReal (S ω' ω) ∂(μ W q) ∂(μ W q) := by
    refine SmallCutDiv_diag hG (F := fun ω' ω => ENNReal.ofReal (S ω' ω))
      (ENNReal.measurable_ofReal.comp hSm) (fun ω₁ ω₂ ω h1 h2 h3 => ?_) (fun ω' ω h => ?_)
      (fun ω' hp ω₁ ω₂ h => ?_)
    · simp only [hS, hu1def, hu2def, hu3def, SmallCutDiv_u1, SmallCutDiv_u2, SmallCutDiv_u3, h1,
        h2, h3]
    · simp [hS, hu1def, hu2def, hu3def, SmallCutDiv_u1, SmallCutDiv_u2, SmallCutDiv_u3, h]
    · obtain ⟨hK, hχ⟩ := SmallCutDiv_family_congr (hfam ω' hp).2.2.2 h
      simp only [hS, hu1def, hu2def, hu3def, SmallCutDiv_u1, SmallCutDiv_u2, SmallCutDiv_u3, hK,
        hχ]
  -- the per-preparation bound: Lemma 9.4 [us:lem:score] with (9.37)
  -- [su:eq:chosen-generator-cut-costs] and the terminal correction (Section 9.3
  -- [su:sec:generator-bounds])
  have hP : ∀ ω' : Ω W q, ∫⁻ ω, Gf ω' ω ∂(μ W q) ≤
      ∫⁻ ω, ENNReal.ofReal (S ω' ω) ∂(μ W q) + ENNReal.ofReal c0 := by
    intro ω'
    by_cases hz : pre ω' = 0
    · have h0 : ∀ ω, Gf ω' ω = 0 := fun ω => by rw [hGf, hz]; simp
      simp only [h0, lintegral_zero]
      exact zero_le
    · have h1 : pre ω' = 1 := (hp01 ω').resolve_left hz
      have hb := hbound W q g E σ M₀ x Pf pre Rf vf Kh χh hW hq hg hg1 hσ hM₀ hG ω' hz
      have hGf1 : ∀ ω, Gf ω' ω = ‖gaussDiv (smallScoreField W g E q (Rf ω') (vf ω')
          (Kh (Rf ω')) (χh (Rf ω'))) ω‖ₑ ^ 2 := fun ω => by rw [hGf, h1, one_mul]
      simp only [hGf1]
      refine hb.trans (le_of_eq ?_)
      have hA : ∀ ω, 2 * χh (Rf ω') ω (vf ω') ^ 2 * C ^ 2 *
          (C * W * σ + 2 * W * hsSq (Kh (Rf ω') ω (vf ω'))) +
          2 * (∑ i, ‖(Pf (Rf ω') *ᵥ vf ω') i‖ ^ 2) * hsSq (Kh (Rf ω') ω (vf ω')) *
            tangGradSq (Pf (Rf ω')) (vf ω') (χh (Rf ω') ω) =
          (2 * C ^ 3 * W * σ) * u1 ω' ω + (4 * C ^ 2 * W) * u2 ω' ω + 2 * u3 ω' ω := fun ω => by
        simp only [hu1def, hu2def, hu3def, SmallCutDiv_u1, SmallCutDiv_u2, SmallCutDiv_u3, h1]
        ring
      have hB : ∀ ω, χh (Rf ω') ω (vf ω') ^ 2 * hsSq (Kh (Rf ω') ω (vf ω')) = u2 ω' ω :=
        fun ω => by simp only [hu2def, SmallCutDiv_u2, h1, one_mul]
      obtain ⟨m1, m2, m3⟩ := hmω ω'
      simp only [hA, hB, hS]
      rw [SmallCutDiv_lintegral_comb m1 m2 m3 (n1 ω') (n2 ω') (n3 ω') (by positivity)
        (by positivity) (by norm_num), SmallCutDiv_lintegral_comb m1 m2 m3 (n1 ω') (n2 ω')
        (n3 ω') hb1' hb2' hb3', e1, e2, e3, e0]
      ring
  have hD1 : ∫⁻ ω, ENNReal.ofReal (u1 ω ω) ∂(μ W q) ≤ 1 := by
    calc ∫⁻ ω, ENNReal.ofReal (u1 ω ω) ∂(μ W q) ≤ ∫⁻ _ : Ω W q, 1 ∂(μ W q) :=
          lintegral_mono fun ω => by
            rw [ENNReal.ofReal_le_one]
            exact pow_le_one₀ (hcut1 ω).1 (hcut1 ω).2
      _ = 1 := by simp
  have hD2 : ∫⁻ ω, ENNReal.ofReal (u2 ω ω) ∂(μ W q) ≤ ENNReal.ofReal (C * σ) := h13
  have hD3 : ∫⁻ ω, ENNReal.ofReal (u3 ω ω) ∂(μ W q) ≤ ENNReal.ofReal C := h14
  have hCσ : 0 ≤ C * σ := mul_nonneg hC.le hσ
  have hfin : ENNReal.ofReal b1 * 1 + ENNReal.ofReal b2 * ENNReal.ofReal (C * σ) +
      ENNReal.ofReal b3 * ENNReal.ofReal C + ENNReal.ofReal c0 =
      ENNReal.ofReal (smallDivBound Cs c C W g σ M₀) := by
    rw [mul_one, ← ENNReal.ofReal_mul hb2', ← ENNReal.ofReal_mul hb3',
      ← ENNReal.ofReal_add hb1' (mul_nonneg hb2' hCσ),
      ← ENNReal.ofReal_add (add_nonneg hb1' (mul_nonneg hb2' hCσ)) (mul_nonneg hb3' hC.le),
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg hb1' (mul_nonneg hb2' hCσ))
        (mul_nonneg hb3' hC.le)) hc0']
    congr 1
    unfold smallDivBound
    rw [hb1, hb2, hb3, hc0]
    ring
  calc ∫⁻ ω, ‖gaussDiv (fun η => smallCut pre Rf vf χh η • smallVec W g E q Rf vf Kh η) ω‖ₑ ^ 2
        ∂(μ W q)
      = ∫⁻ ω, Gf ω ω ∂(μ W q) :=
        lintegral_congr fun ω => by rw [hGf, gaussDiv_smallCut_eq hG ω]
    _ = ∫⁻ ω', ∫⁻ ω, Gf ω' ω ∂(μ W q) ∂(μ W q) := hdiagG
    _ ≤ ∫⁻ ω', (∫⁻ ω, ENNReal.ofReal (S ω' ω) ∂(μ W q) + ENNReal.ofReal c0) ∂(μ W q) :=
        lintegral_mono hP
    _ = ∫⁻ ω', ∫⁻ ω, ENNReal.ofReal (S ω' ω) ∂(μ W q) ∂(μ W q) + ENNReal.ofReal c0 := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ ω, ENNReal.ofReal (S ω ω) ∂(μ W q) + ENNReal.ofReal c0 := by rw [← hdiagS]
    _ = ENNReal.ofReal b1 * ∫⁻ ω, ENNReal.ofReal (u1 ω ω) ∂(μ W q) +
        ENNReal.ofReal b2 * ∫⁻ ω, ENNReal.ofReal (u2 ω ω) ∂(μ W q) +
        ENNReal.ofReal b3 * ∫⁻ ω, ENNReal.ofReal (u3 ω ω) ∂(μ W q) + ENNReal.ofReal c0 := by
        simp only [hS]
        rw [SmallCutDiv_lintegral_comb hmd.1 hmd.2.1 hmd.2.2 (fun ω => n1 ω ω) (fun ω => n2 ω ω)
          (fun ω => n3 ω ω) hb1' hb2' hb3']
    _ ≤ ENNReal.ofReal b1 * 1 + ENNReal.ofReal b2 * ENNReal.ofReal (C * σ) +
        ENNReal.ofReal b3 * ENNReal.ofReal C + ENNReal.ofReal c0 := by gcongr
    _ = ENNReal.ofReal (smallDivBound Cs c C W g σ M₀) := hfin

end LSBA
