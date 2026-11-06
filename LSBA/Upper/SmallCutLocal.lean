import LSBA.Upper.SmallCut
import LSBA.Upper.SmallScoreSmooth
import LSBA.Upper.SmallPrefix
import LSBA.Analysis.LineDerivMeas

/-!
# The Gaussian divergence of the small-coupling field at a fixed preparation

The components of the field of Lemma 8.12 [up:lem:small-contraction] on the preparation blocks
vanish, and a coordinate line in an active direction keeps the preparation blocks, hence the
preparation indicator, the chart `R_4` and the source `v_4`. So the Gaussian divergence (8.33)
[up:eq:gaussian-divergence] of `χ X` at a sample is `pre` times that of the cut field of Lemma 9.4
[us:lem:score] at the preparation of the sample ("conditional Fubini introduces no preparation
derivatives"), and the latter depends only on the coordinates of the blocks `V_5, …, V_q`. The
divergence, the field and the tangential gradient of (9.30) [su:eq:pair-cutoff-derivative] are
measurable, jointly in the preparation and the sample.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Auxiliary lemmas -/

/-- Moving the sample along the coordinate `k` does not change the blocks `i ≠ k.1`. -/
private lemma SmallCutLocal_gueBlock_line {W q : ℕ} (ω : Ω W q) (k : Fin q × Fin W × Fin W)
    (t : ℝ) {i : Fin q} (hi : i ≠ k.1) :
    gueBlock W q (ω + t • Pi.single k 1) i = gueBlock W q ω i := by
  have h : ∀ α β, (ω + t • (Pi.single k 1 : Ω W q)) (i, α, β) = ω (i, α, β) := fun α β => by
    have hne : (i, α, β) ≠ k := fun h => hi (by rw [← h])
    simp [hne]
  ext α β
  simp only [gueBlock, Matrix.of_apply, h]

/-- The standard coordinates of the field `X` of (9.10) [us:eq:physical] on the preparation blocks
vanish. -/
private lemma SmallCutLocal_hermCoord_prep {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {K : Matrix (Fin W) (Fin W) ℂ} (η : Ω W q) {k : Fin q × Fin W × Fin W}
    (hk : (k.1 : ℕ) < 4) : hermCoord W q (smallField W g E q R v K η) k = 0 := by
  simp [hermCoord, smallField, hk]

/-- If `f = c h` on the line through `x` in direction `d`, then `∂_d f (x) = c ∂_d h (x)`. -/
private lemma SmallCutLocal_lineDeriv_const_mul {W q : ℕ} {f h : Ω W q → ℝ} {x d : Ω W q}
    (c : ℝ) (hfh : ∀ t : ℝ, f (x + t • d) = c * h (x + t • d)) :
    lineDeriv ℝ f x d = c * lineDeriv ℝ h x d := by
  unfold lineDeriv
  rw [show (fun t : ℝ => f (x + t • d)) = fun t => c * h (x + t • d) from funext hfh,
    deriv_const_mul_field']

/-- If `f` on the line through `x` agrees with `h` on the line through `y` (same direction `d`),
then `∂_d f (x) = ∂_d h (y)`. -/
private lemma SmallCutLocal_lineDeriv_congr {W q : ℕ} {f h : Ω W q → ℝ} {x y d : Ω W q}
    (hfh : ∀ t : ℝ, f (x + t • d) = h (y + t • d)) :
    lineDeriv ℝ f x d = lineDeriv ℝ h y d := by
  unfold lineDeriv
  rw [show (fun t : ℝ => f (x + t • d)) = fun t => h (y + t • d) from funext hfh]

/-- Each block is a continuous function of the sample. -/
private lemma SmallCutLocal_continuous_gueBlock (W q : ℕ) (i : Fin q) :
    Continuous fun η : Ω W q => gueBlock W q η i := by
  refine continuous_pi fun α => continuous_pi fun β => ?_
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The input sequence is a continuous function of the sample. -/
private lemma SmallCutLocal_continuous_blockSeq (W q k : ℕ) :
    Continuous fun η : Ω W q => blockSeq W q η k := by
  unfold blockSeq
  by_cases hk : k < q
  · simp only [hk, ↓reduceDIte]
    exact SmallCutLocal_continuous_gueBlock W q ⟨k, hk⟩
  · simp only [hk, ↓reduceDIte]
    exact continuous_const

/-- The standard coordinates are a continuous function of the input array. -/
private lemma SmallCutLocal_continuous_hermCoord (W q : ℕ) : Continuous (hermCoord W q) := by
  unfold hermCoord
  exact continuous_pi fun p => continuous_const.mul (Complex.continuous_re.comp
    ((continuous_const.matrix_mul (continuous_apply p.1)).matrix_trace))

/-- The matrix inverse `A⁻¹ = (det A)⁻¹ adj A` is measurable. -/
private lemma SmallCutLocal_measurable_inv (W : ℕ) :
    Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A⁻¹ := by
  have h : (fun A : Matrix (Fin W) (Fin W) ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (measurable_inv.comp continuous_id.matrix_det.measurable).smul
    continuous_id.matrix_adjugate.measurable

section Meas

variable {α : Type*} [MeasurableSpace α] {W : ℕ}

/-- `x ↦ A(x) v(x)` is measurable. -/
private lemma SmallCutLocal_measurable_mulVec {A : α → Matrix (Fin W) (Fin W) ℂ}
    {a : α → Fin W → ℂ} (hA : Measurable A) (ha : Measurable a) :
    Measurable fun x => A x *ᵥ a x :=
  (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp (hA.prodMk ha)

/-- `x ↦ a(x)* b(x)` is measurable. -/
private lemma SmallCutLocal_measurable_dot {a b : α → Fin W → ℂ} (ha : Measurable a)
    (hb : Measurable b) : Measurable fun x => star (a x) ⬝ᵥ b x :=
  ((continuous_star.comp continuous_fst).dotProduct continuous_snd).measurable.comp
    (ha.prodMk hb)

/-- `x ↦ a(x) b(x)*` is measurable. -/
private lemma SmallCutLocal_measurable_vecMulVec {a b : α → Fin W → ℂ} (ha : Measurable a)
    (hb : Measurable b) : Measurable fun x => Matrix.vecMulVec (a x) (star (b x)) :=
  (Continuous.matrix_vecMulVec continuous_fst (continuous_star.comp continuous_snd)).measurable.comp
    (ha.prodMk hb)

/-- The correction `rotCorr a b` of (9.9) [us:eq:L] is measurable in `(a, b)`. -/
private lemma SmallCutLocal_measurable_rotCorr {a b : α → Fin W → ℂ} (ha : Measurable a)
    (hb : Measurable b) : Measurable fun x => rotCorr (a x) (b x) := by
  unfold rotCorr
  have hc := (SmallCutLocal_measurable_dot ha ha).inv
  exact (hc.smul ((SmallCutLocal_measurable_vecMulVec hb ha).sub
    (SmallCutLocal_measurable_vecMulVec ha hb))).sub
    (((hc.pow_const 2).mul (SmallCutLocal_measurable_dot ha hb)).smul
      (SmallCutLocal_measurable_vecMulVec ha ha))

/-- The projection `tangProj P v w` onto `𝓗_v` is measurable in `(P, v)`. -/
private lemma SmallCutLocal_measurable_tangProj {P : α → Matrix (Fin W) (Fin W) ℂ}
    {v : α → Fin W → ℂ} (hP : Measurable P) (hv : Measurable v) (w : Fin W → ℂ) :
    Measurable fun x => tangProj (P x) (v x) w := by
  unfold tangProj
  have hPv := SmallCutLocal_measurable_mulVec hP hv
  have hn : Measurable fun x => ∑ i, ‖(P x *ᵥ v x) i‖ ^ 2 :=
    Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hPv).norm.pow_const 2
  exact (SmallCutLocal_measurable_mulVec hP measurable_const).sub
    ((Complex.measurable_ofReal.comp ((Complex.measurable_re.comp
      (SmallCutLocal_measurable_dot hPv measurable_const)).div hn)).smul hPv)

end Meas

/-- The graph coordinates `R_j` of (9.2) [su:eq:transported-normal] are measurable in
`(R_4, ω)`. -/
private lemma SmallCutLocal_measurable_chartR (W : ℕ) (g E : ℝ) (q j : ℕ) :
    Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q => chartR W g E q p.1 p.2 j := by
  induction j with
  | zero =>
    simp only [chartR]
    exact measurable_fst
  | succ j ih =>
    by_cases h4 : j < 4
    · simp only [chartR, h4, ↓reduceIte]
      exact measurable_fst
    · simp only [chartR, h4, ↓reduceIte]
      exact (SmallCutLocal_measurable_inv W).comp
        ((((SmallCutLocal_continuous_blockSeq W q j).measurable.comp measurable_snd).sub
          measurable_const).sub ((measurable_const_smul ((g : ℂ) ^ 2)).comp ih))

/-- The products `R_{[j,5]}` of (9.2) [su:eq:transported-normal] are measurable in `(R_4, ω)`. -/
private lemma SmallCutLocal_measurable_chartProd (W : ℕ) (g E : ℝ) (q j : ℕ) :
    Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q => chartProd W g E q p.1 p.2 j := by
  induction j with
  | zero =>
    simp only [chartProd]
    exact measurable_const
  | succ j ih =>
    by_cases h4 : j < 4
    · simp only [chartProd, h4, ↓reduceIte]
      exact measurable_const
    · simp only [chartProd, h4, ↓reduceIte]
      exact (SmallCutLocal_measurable_chartR W g E q (j + 1)).mul ih

/-- The standard coordinates of the field `X` of (9.10) [us:eq:physical] are measurable in
`(R_4, v_4, K, ω)`. -/
private lemma SmallCutLocal_measurable_hermField {α : Type*} [MeasurableSpace α] {W q : ℕ}
    (g E : ℝ) {R : α → Matrix (Fin W) (Fin W) ℂ} {v : α → Fin W → ℂ}
    {K : α → Matrix (Fin W) (Fin W) ℂ} {η : α → Ω W q} (hR : Measurable R) (hv : Measurable v)
    (hK : Measurable K) (hη : Measurable η) :
    Measurable fun x => hermCoord W q (smallField W g E q (R x) (v x) (K x) (η x)) := by
  refine (SmallCutLocal_continuous_hermCoord W q).measurable.comp
    (f := fun x => smallField W g E q (R x) (v x) (K x) (η x)) ?_
  have hRq : Measurable fun x => chartR W g E q (R x) (η x) (q - 1) :=
    (SmallCutLocal_measurable_chartR W g E q (q - 1)).comp (hR.prodMk hη)
  have hPq : Measurable fun x => chartProd W g E q (R x) (η x) (q - 1) :=
    (SmallCutLocal_measurable_chartProd W g E q (q - 1)).comp (hR.prodMk hη)
  have ha := SmallCutLocal_measurable_mulVec hPq hv
  have hL : Measurable fun x => smallCorr W g E q (R x) (v x) (K x) (η x) := by
    unfold smallCorr
    exact SmallCutLocal_measurable_rotCorr ha
      ((SmallCutLocal_measurable_mulVec hPq (SmallCutLocal_measurable_mulVec hK hv)).sub ha)
  refine measurable_pi_iff.mpr fun i => ?_
  have hV := (SmallCutLocal_continuous_gueBlock W q i).measurable.comp hη
  by_cases h1 : (i : ℕ) < 4
  · simp only [smallField, h1, ↓reduceIte]
    exact measurable_const
  by_cases h2 : (i : ℕ) = 4
  · simp only [smallField, h2, ↓reduceIte]
    have hA := hV.sub ((measurable_const_smul ((g : ℂ) ^ 2)).comp hR)
    exact (hK.mul hA).sub (hA.mul hK)
  by_cases h3 : (i : ℕ) + 1 < q
  · simp only [smallField, h1, h2, h3, ↓reduceIte]
    exact (hK.mul hV).sub (hV.mul hK)
  · simp only [smallField, h1, h2, h3, ↓reduceIte]
    have hA := hV.sub ((measurable_const_smul ((g : ℂ) ^ 2)).comp hRq)
    exact ((hK.mul hV).sub (hV.mul hK)).sub ((hL.mul hA).sub (hA.mul hL))

/-- The cut field of Lemma 9.4 [us:lem:score] at the preparation of `a x`, evaluated at `b x`,
is measurable in `x`, for measurable data of Lemma 9.3 [su:lem:chosen-generator]. -/
private lemma SmallCutLocal_measurable_field {α : Type*} [MeasurableSpace α] {W q : ℕ}
    {g E : ℝ} {Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ} {vf : Ω W q → Fin W → ℂ}
    {Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ}
    (hRm : Measurable Rf) (hvm : Measurable vf)
    (hKm : Measurable
      (fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) => Kh p.1 p.2.1 p.2.2))
    (hχm : Measurable
      (fun p : Matrix (Fin W) (Fin W) ℂ × Ω W q × (Fin W → ℂ) => χh p.1 p.2.1 p.2.2))
    {a b : α → Ω W q} (ha : Measurable a) (hb : Measurable b) :
    Measurable fun x =>
      smallScoreField W g E q (Rf (a x)) (vf (a x)) (Kh (Rf (a x))) (χh (Rf (a x))) (b x) := by
  have hR := hRm.comp ha
  have hv := hvm.comp ha
  have hK : Measurable fun x => Kh (Rf (a x)) (b x) (vf (a x)) :=
    hKm.comp (hR.prodMk (hb.prodMk hv))
  have hχ : Measurable fun x => χh (Rf (a x)) (b x) (vf (a x)) :=
    hχm.comp (hR.prodMk (hb.prodMk hv))
  have hX : Measurable fun x => hermCoord W q
      (smallField W g E q (Rf (a x)) (vf (a x)) (Kh (Rf (a x)) (b x) (vf (a x))) (b x)) :=
    SmallCutLocal_measurable_hermField g E hR hv hK hb
  show Measurable fun x => χh (Rf (a x)) (b x) (vf (a x)) • hermCoord W q
    (smallField W g E q (Rf (a x)) (vf (a x)) (Kh (Rf (a x)) (b x) (vf (a x))) (b x))
  exact hχ.smul hX

/-! ### Localization and measurability -/

/-- Localization of the Gaussian divergence (8.33) [up:eq:gaussian-divergence] of the field of
Lemma 8.12 [up:lem:small-contraction] to the preparation of the sample. -/
theorem gaussDiv_smallCut_eq {W q : ℕ} {g E C σ M₀ : ℝ} {x : IsoFlag W}
    {Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} {pre : Ω W q → ℝ}
    {Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ} {vf : Ω W q → Fin W → ℂ}
    {Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ}
    (hG : ChosenGenerator W q g E x Pf C σ M₀ pre Rf vf Kh χh) (ω : Ω W q) :
    gaussDiv (fun η => smallCut pre Rf vf χh η • smallVec W g E q Rf vf Kh η) ω =
      pre ω * gaussDiv (smallScoreField W g E q (Rf ω) (vf ω) (Kh (Rf ω)) (χh (Rf ω))) ω := by
  obtain ⟨-, -, -, -, hpre, -⟩ := hG
  have hline : ∀ (k : Fin q × Fin W × Fin W) (t : ℝ),
      (smallCut pre Rf vf χh (ω + t • Pi.single k 1) •
        smallVec W g E q Rf vf Kh (ω + t • Pi.single k 1)) k =
      pre ω * smallScoreField W g E q (Rf ω) (vf ω) (Kh (Rf ω)) (χh (Rf ω))
        (ω + t • Pi.single k 1) k := by
    intro k t
    by_cases hk : (k.1 : ℕ) < 4
    · simp [smallScoreField, smallVec, SmallCutLocal_hermCoord_prep _ hk]
    · obtain ⟨h1, h2, h3⟩ := hpre (ω + t • Pi.single k 1) ω fun i hi =>
        SmallCutLocal_gueBlock_line ω k t fun h => hk (h ▸ hi)
      simp only [smallScoreField, smallVec, smallCut, Pi.smul_apply, smul_eq_mul, h1, h2, h3]
      ring
  unfold gaussDiv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h0 := hline k 0
  simp only [zero_smul, add_zero] at h0
  beta_reduce
  rw [h0, SmallCutLocal_lineDeriv_const_mul
    (f := fun y => (smallCut pre Rf vf χh y • smallVec W g E q Rf vf Kh y) k)
    (h := fun y => smallScoreField W g E q (Rf ω) (vf ω) (Kh (Rf ω)) (χh (Rf ω)) y k)
    (pre ω) (hline k)]
  ring

/-- Under the family clauses of Lemma 9.3 [su:lem:chosen-generator], the Gaussian divergence of
the cut field of Lemma 9.4 [us:lem:score] depends only on the coordinates of the blocks
`V_5, …, V_q`. -/
theorem gaussDiv_smallScoreField_congr {W q : ℕ} {g E : ℝ} {P R : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Ω W q → (Fin W → ℂ) → ℝ} (hF : GenFamily W q g E P R Kh χh) {ω₁ ω₂ : Ω W q}
    (h : ∀ k : Fin q × Fin W × Fin W, 4 ≤ (k.1 : ℕ) → ω₁ k = ω₂ k) :
    gaussDiv (smallScoreField W g E q R v Kh χh) ω₁ =
      gaussDiv (smallScoreField W g E q R v Kh χh) ω₂ := by
  obtain ⟨hF1, -⟩ := hF
  have hcongr : ∀ η η' : Ω W q, (∀ k : Fin q × Fin W × Fin W, 4 ≤ (k.1 : ℕ) → η k = η' k) →
      smallScoreField W g E q R v Kh χh η = smallScoreField W g E q R v Kh χh η' := by
    intro η η' hη
    have hb : ∀ i : Fin q, 4 ≤ (i : ℕ) → gueBlock W q η i = gueBlock W q η' i := fun i hi => by
      have he : ∀ α β, η (i, α, β) = η' (i, α, β) := fun α β => hη (i, α, β) hi
      ext α β
      simp only [gueBlock, Matrix.of_apply, he]
    obtain ⟨hK, hχ⟩ := hF1 η η' (fun i hi _ => hb i hi) v
    simp only [smallScoreField, hK, hχ, smallField_congr_active hb]
  unfold gaussDiv
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : (k.1 : ℕ) < 4
  · have hz : ∀ η, smallScoreField W g E q R v Kh χh η k = 0 := fun η => by
      simp [smallScoreField, SmallCutLocal_hermCoord_prep η hk]
    have hl : ∀ y : Ω W q, lineDeriv ℝ (fun η => smallScoreField W g E q R v Kh χh η k) y
        (Pi.single k 1) = 0 := fun y => by
      rw [SmallCutLocal_lineDeriv_const_mul (h := fun _ => (0 : ℝ)) 0 fun t => by simp [hz]]
      simp
    rw [hz, hz, hl, hl]
    ring
  · have hline : ∀ t : ℝ, smallScoreField W g E q R v Kh χh (ω₁ + t • Pi.single k 1) k =
        smallScoreField W g E q R v Kh χh (ω₂ + t • Pi.single k 1) k := fun t => by
      rw [hcongr (ω₁ + t • Pi.single k 1) (ω₂ + t • Pi.single k 1) fun k' hk' => by
        simp [h k' hk']]
    rw [h k (not_lt.mp hk), hcongr ω₁ ω₂ h, SmallCutLocal_lineDeriv_congr
      (f := fun y => smallScoreField W g E q R v Kh χh y k)
      (h := fun y => smallScoreField W g E q R v Kh χh y k) hline]

/-- The field of Lemma 8.12 [up:lem:small-contraction] is measurable, and the Gaussian divergence
of the cut field of Lemma 9.4 [us:lem:score] at the preparation of `ω'`, weighted by `pre ω'`, is
jointly measurable in `(ω', ω)`. -/
theorem measurable_smallCut_field {W q : ℕ} {g E C σ M₀ : ℝ} {x : IsoFlag W}
    {Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} {pre : Ω W q → ℝ}
    {Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ} {vf : Ω W q → Fin W → ℂ}
    {Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ}
    (hG : ChosenGenerator W q g E x Pf C σ M₀ pre Rf vf Kh χh) :
    Measurable (fun η => smallCut pre Rf vf χh η • smallVec W g E q Rf vf Kh η) ∧
      Measurable (fun p : Ω W q × Ω W q => pre p.1 *
        gaussDiv (smallScoreField W g E q (Rf p.1) (vf p.1) (Kh (Rf p.1)) (χh (Rf p.1))) p.2) := by
  have hcut := (smallCut_basic hG).1
  obtain ⟨-, hpm, hRm, hvm, -, hprep, -, hKm, hχm, hfam, -⟩ := hG
  refine ⟨?_, ?_⟩
  · have hK : Measurable fun η => Kh (Rf η) η (vf η) :=
      hKm.comp (hRm.prodMk (measurable_id.prodMk hvm))
    have hX : Measurable fun η => smallVec W g E q Rf vf Kh η :=
      SmallCutLocal_measurable_hermField g E hRm hvm hK measurable_id
    exact hcut.smul hX
  set S : Set (Ω W q × Ω W q) := {p | pre p.1 ≠ 0} with hSdef
  have hS : MeasurableSet S :=
    (hpm.comp measurable_fst) (measurableSet_singleton (0 : ℝ)).compl
  have hp1 : Measurable fun p : Ω W q × Ω W q => pre p.1 := hpm.comp measurable_fst
  simp only [gaussDiv, Finset.mul_sum]
  refine Finset.measurable_sum _ fun k _ => ?_
  set F : Ω W q × Ω W q → Ω W q → ℝ := fun p y =>
    smallScoreField W g E q (Rf p.1) (vf p.1) (Kh (Rf p.1)) (χh (Rf p.1)) y k with hFdef
  have hFm : Measurable (Function.uncurry F) :=
    (measurable_pi_apply k).comp (SmallCutLocal_measurable_field (g := g) (E := E) hRm hvm hKm
      hχm (a := fun r : (Ω W q × Ω W q) × Ω W q => r.1.1) (b := fun r => r.2)
      measurable_fst.fst measurable_snd)
  have hval : Measurable fun p : Ω W q × Ω W q => p.2 k * F p p.2 :=
    ((measurable_pi_apply k).comp measurable_snd).mul
      ((measurable_pi_apply k).comp (SmallCutLocal_measurable_field (g := g) (E := E) hRm hvm
        hKm hχm (a := fun p : Ω W q × Ω W q => p.1) (b := fun p => p.2) measurable_fst
        measurable_snd))
  have hdiff : ∀ p ∈ S, LineDifferentiableAt ℝ (F p) p.2 (Pi.single k 1) := by
    intro p hp
    have hC := contDiff_smallScoreField (hfam p.1 hp).2.2.2 (hprep p.1 hp).2.1
    exact (differentiableAt_pi.1 (hC.differentiable one_ne_zero p.2) k).lineDifferentiableAt
  have hD := measurable_indicator_lineDeriv hFm measurable_snd measurable_const hS hdiff
  have hid : (fun p : Ω W q × Ω W q => pre p.1 * (p.2 k *
      smallScoreField W g E q (Rf p.1) (vf p.1) (Kh (Rf p.1)) (χh (Rf p.1)) p.2 k -
      lineDeriv ℝ (fun y => smallScoreField W g E q (Rf p.1) (vf p.1) (Kh (Rf p.1))
        (χh (Rf p.1)) y k) p.2 (Pi.single k 1))) =
      fun p => pre p.1 * (p.2 k * F p p.2) -
        pre p.1 * S.indicator (fun p => lineDeriv ℝ (F p) p.2 (Pi.single k 1)) p := by
    funext p
    by_cases hp : pre p.1 = 0
    · simp [hp]
    · have hpS : p ∈ S := hp
      rw [Set.indicator_of_mem hpS]
      simp only [hFdef]
      ring
  rw [hid]
  exact (hp1.mul hval).sub (hp1.mul hD)

/-- The tangential gradient `‖∇_{v_4} χ̂‖²` of (9.30) [su:eq:pair-cutoff-derivative] at the
preparation of `ω'`, weighted by `pre ω'`, is jointly measurable in `(ω', ω)`. -/
theorem measurable_tangGradSq_smallCut {W q : ℕ} {g E C σ M₀ : ℝ} {x : IsoFlag W}
    {Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} {pre : Ω W q → ℝ}
    {Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ} {vf : Ω W q → Fin W → ℂ}
    {Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ}
    (hG : ChosenGenerator W q g E x Pf C σ M₀ pre Rf vf Kh χh) :
    Measurable (fun p : Ω W q × Ω W q =>
      pre p.1 * tangGradSq (Pf (Rf p.1)) (vf p.1) (χh (Rf p.1) p.2)) := by
  obtain ⟨-, hpm, hRm, hvm, -, hprep, hPm, -, hχm, hfam, -⟩ := hG
  set S : Set (Ω W q × Ω W q) := {p | pre p.1 ≠ 0} with hSdef
  have hS : MeasurableSet S :=
    (hpm.comp measurable_fst) (measurableSet_singleton (0 : ℝ)).compl
  have hp1 : Measurable fun p : Ω W q × Ω W q => pre p.1 := hpm.comp measurable_fst
  set f : Ω W q × Ω W q → (Fin W → ℂ) → ℝ := fun p => χh (Rf p.1) p.2 with hfdef
  have hfm : Measurable (Function.uncurry f) :=
    hχm.comp ((hRm.comp measurable_fst.fst).prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hx : Measurable fun p : Ω W q × Ω W q => vf p.1 := hvm.comp measurable_fst
  have hP : Measurable fun p : Ω W q × Ω W q => Pf (Rf p.1) :=
    hPm.comp (hRm.comp measurable_fst)
  have hdiff : ∀ (w : Fin W → ℂ), ∀ p ∈ S,
      LineDifferentiableAt ℝ (f p) (vf p.1) (tangProj (Pf (Rf p.1)) (vf p.1) w) := by
    intro w p hp
    obtain ⟨-, -, -, -, h5, -⟩ := (hfam p.1 hp).2.2.2
    have hv : vf p.1 ≠ 0 := (hprep p.1 hp).2.1
    have hopen : IsOpen {r : Ω W q × (Fin W → ℂ) | r.2 ≠ 0} :=
      isOpen_ne_fun continuous_snd continuous_const
    have h2 : ContDiffAt ℝ 2 (fun r : Ω W q × (Fin W → ℂ) => χh (Rf p.1) r.1 r.2)
        (p.2, vf p.1) := h5.contDiffAt (hopen.mem_nhds hv)
    have hemb : DifferentiableAt ℝ (fun w : Fin W → ℂ => (p.2, w)) (vf p.1) :=
      (differentiableAt_const p.2).prodMk differentiableAt_id
    exact ((h2.differentiableAt (by norm_num)).comp (vf p.1) hemb).lineDifferentiableAt
  have hD : ∀ w : Fin W → ℂ, Measurable (S.indicator fun p =>
      lineDeriv ℝ (f p) (vf p.1) (tangProj (Pf (Rf p.1)) (vf p.1) w)) := fun w =>
    measurable_indicator_lineDeriv hfm hx (SmallCutLocal_measurable_tangProj hP hx w) hS
      (hdiff w)
  have hid : (fun p : Ω W q × Ω W q =>
      pre p.1 * tangGradSq (Pf (Rf p.1)) (vf p.1) (χh (Rf p.1) p.2)) =
      fun p => ∑ j : Fin W,
        (pre p.1 * (S.indicator (fun p => lineDeriv ℝ (f p) (vf p.1)
          (tangProj (Pf (Rf p.1)) (vf p.1) (Pi.single j 1))) p) ^ 2 +
        pre p.1 * (S.indicator (fun p => lineDeriv ℝ (f p) (vf p.1)
          (tangProj (Pf (Rf p.1)) (vf p.1) (Pi.single j Complex.I))) p) ^ 2) := by
    funext p
    unfold tangGradSq
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hp : pre p.1 = 0
    · simp [hp]
    · have hpS : p ∈ S := hp
      rw [Set.indicator_of_mem hpS, Set.indicator_of_mem hpS]
      simp only [hfdef]
      ring
  rw [hid]
  exact Finset.measurable_sum _ fun j _ =>
    (hp1.mul ((hD _).pow_const 2)).add (hp1.mul ((hD _).pow_const 2))

end LSBA
