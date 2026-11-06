import LSBA.Upper.ChosenGenerator

/-!
# Smoothness of the cut field at a fixed preparation

The cut field `χ̂(R_4; ·; v_4) X` of Lemma 9.4 [us:lem:score] at a fixed preparation
`(R_4, v_4) = (R, v)`, in standard coordinates, with `X` of (9.10) [us:eq:physical] built from
`K = K̂(R_4; ω; v_4)`. Under the family clauses of Lemma 9.3 [su:lem:chosen-generator] and
`v_4 ≠ 0` it is `C¹` on all of `Ω W q`: near a point of the support of `χ̂` the generator is `C²`,
the graph coordinates `R_5, …, R_{q-1}` of (9.2) [su:eq:transported-normal] are inverses of
invertible matrices, `R_{[q-1,5]} v_4 ≠ 0` and the correction (9.9) [us:eq:L] is smooth; off the
support of `χ̂` the field vanishes on a neighbourhood. This is the smoothness in the active
inputs required by Lemma 8.11 [up:lem:angular] in the proof of Lemma 8.12
[up:lem:small-contraction].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Auxiliary lemmas -/

section Aux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x : X}

/-- A matrix-valued map is `C^n` at a point iff all its entries are. -/
private lemma SmallScoreSmooth_contDiffAt_matrix_iff {W : ℕ}
    {Φ : X → Matrix (Fin W) (Fin W) ℂ} :
    ContDiffAt ℝ n Φ x ↔ ∀ i j, ContDiffAt ℝ n (fun y => Φ y i j) x := by
  let e : Matrix (Fin W) (Fin W) ℂ ≃L[ℝ] (Fin W → Fin W → ℂ) :=
    (Matrix.ofLinearEquiv ℝ).symm.toContinuousLinearEquiv
  rw [← e.comp_contDiffAt_iff, contDiffAt_pi]
  refine forall_congr' fun i => ?_
  rw [contDiffAt_pi]
  rfl

/-- Complex conjugation preserves `C^n` regularity over `ℝ`. -/
private lemma SmallScoreSmooth_contDiffAt_star {f : X → ℂ} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun y => star (f y)) x :=
  Complex.conjCLE.contDiff.contDiffAt.comp x hf

/-- `y ↦ A(y) *ᵥ a(y)` is `C^n` when `A` and `a` are. -/
private lemma SmallScoreSmooth_contDiffAt_mulVec {W : ℕ} {A : X → Matrix (Fin W) (Fin W) ℂ}
    {a : X → Fin W → ℂ} (hA : ContDiffAt ℝ n A x) (ha : ContDiffAt ℝ n a x) :
    ContDiffAt ℝ n (fun y => A y *ᵥ a y) x := by
  rw [SmallScoreSmooth_contDiffAt_matrix_iff] at hA
  rw [contDiffAt_pi] at ha ⊢
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiffAt.sum fun j _ => (hA i j).mul (ha j)

/-- `y ↦ a(y)* b(y)` is `C^n` when `a` and `b` are. -/
private lemma SmallScoreSmooth_contDiffAt_dot {W : ℕ} {a b : X → Fin W → ℂ}
    (ha : ContDiffAt ℝ n a x) (hb : ContDiffAt ℝ n b x) :
    ContDiffAt ℝ n (fun y => star (a y) ⬝ᵥ b y) x := by
  rw [contDiffAt_pi] at ha hb
  simp only [dotProduct, Pi.star_apply]
  exact ContDiffAt.sum fun j _ => (SmallScoreSmooth_contDiffAt_star (ha j)).mul (hb j)

/-- `y ↦ a(y) b(y)*` is `C^n` when `a` and `b` are. -/
private lemma SmallScoreSmooth_contDiffAt_vecMulVec {W : ℕ} {a b : X → Fin W → ℂ}
    (ha : ContDiffAt ℝ n a x) (hb : ContDiffAt ℝ n b x) :
    ContDiffAt ℝ n (fun y => Matrix.vecMulVec (a y) (star (b y))) x := by
  rw [contDiffAt_pi] at ha hb
  rw [SmallScoreSmooth_contDiffAt_matrix_iff]
  intro i j
  simp only [Matrix.vecMulVec_apply, Pi.star_apply]
  exact (ha i).mul (SmallScoreSmooth_contDiffAt_star (hb j))

/-- The correction `rotCorr a b` of (9.9) [us:eq:L] is `C^n` in `(a, b)` where `a ≠ 0`. -/
private lemma SmallScoreSmooth_contDiffAt_rotCorr {W : ℕ} {a b : X → Fin W → ℂ}
    (ha : ContDiffAt ℝ n a x) (hb : ContDiffAt ℝ n b x) (ha0 : a x ≠ 0) :
    ContDiffAt ℝ n (fun y => rotCorr (a y) (b y)) x := by
  have hc0 : star (a x) ⬝ᵥ a x ≠ 0 := by
    intro h
    apply ha0
    funext i
    have hre := congrArg Complex.re h
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.star_def, Complex.conj_mul',
      Complex.zero_re] at hre
    norm_cast at hre
    have hsq := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖a x j‖)).1 hre i
      (Finset.mem_univ i)
    simpa using hsq
  have hc : ContDiffAt ℝ n (fun y => star (a y) ⬝ᵥ a y) x :=
    SmallScoreSmooth_contDiffAt_dot ha ha
  have hci : ContDiffAt ℝ n (fun y => (star (a y) ⬝ᵥ a y)⁻¹) x :=
    (contDiffAt_inv ℝ hc0).comp x hc
  unfold rotCorr
  refine ContDiffAt.sub (hci.fun_smul ((SmallScoreSmooth_contDiffAt_vecMulVec hb ha).sub
    (SmallScoreSmooth_contDiffAt_vecMulVec ha hb))) ?_
  exact ((hci.pow 2).mul (SmallScoreSmooth_contDiffAt_dot ha hb)).fun_smul
    (SmallScoreSmooth_contDiffAt_vecMulVec ha ha)

end Aux

/-- Each block `η ↦ gueBlock W q η i` is a smooth (real-linear) function of the sample. -/
private lemma SmallScoreSmooth_contDiff_gueBlock (W q : ℕ) (i : Fin q) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun η : Ω W q => gueBlock W q η i) := by
  rw [contDiff_iff_contDiffAt]
  intro η₀
  rw [SmallScoreSmooth_contDiffAt_matrix_iff]
  intro α β
  have hc : ∀ p : Fin q × Fin W × Fin W,
      ContDiff ℝ n (fun η : Ω W q => ((η p : ℝ) : ℂ)) := fun p =>
    Complex.ofRealCLM.contDiff.comp (contDiff_pi.1 contDiff_id p)
  simp only [gueBlock, Matrix.of_apply]
  split_ifs
  · exact ((hc _).div_const _).contDiffAt
  · exact (((hc _).add (contDiff_const.mul (hc _))).div_const _).contDiffAt
  · exact (((hc _).sub (contDiff_const.mul (hc _))).div_const _).contDiffAt

/-- The input sequence `η ↦ blockSeq W q η k` is smooth. -/
private lemma SmallScoreSmooth_contDiff_blockSeq (W q k : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun η : Ω W q => blockSeq W q η k) := by
  unfold blockSeq
  by_cases hk : k < q
  · simp only [hk, ↓reduceDIte]
    exact SmallScoreSmooth_contDiff_gueBlock W q ⟨k, hk⟩
  · simp only [hk, ↓reduceDIte]
    exact contDiff_const

/-- The graph coordinates `R_j` of (9.2) [su:eq:transported-normal] are `C^n` near a sample where
`R_5, …, R_{q-1}` are invertible, for every `j ≤ q - 1`. -/
private lemma SmallScoreSmooth_contDiffAt_chartR {W q : ℕ} {g E : ℝ}
    {R : Matrix (Fin W) (Fin W) ℂ} {η₀ : Ω W q} {n : WithTop ℕ∞}
    (hU : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R η₀ j)) :
    ∀ j, j ≤ q - 1 → ContDiffAt ℝ n (fun η => chartR W g E q R η j) η₀
  | 0, _ => by
    simp only [chartR]
    exact contDiffAt_const
  | j + 1, hj => by
    by_cases h4 : j < 4
    · simp only [chartR, h4, ↓reduceIte]
      exact contDiffAt_const
    · have ih := SmallScoreSmooth_contDiffAt_chartR (n := n) hU j (by omega)
      have hu := hU (j + 1) (by omega) hj
      simp only [chartR, h4, ↓reduceIte] at hu ⊢
      rw [Matrix.isUnit_nonsing_inv_iff] at hu
      have hM : ContDiffAt ℝ n (fun η => blockSeq W q η j - (E : ℂ) • (1 : Matrix (Fin W)
          (Fin W) ℂ) - ((g : ℂ) ^ 2) • chartR W g E q R η j) η₀ :=
        (((SmallScoreSmooth_contDiff_blockSeq W q j).contDiffAt).sub contDiffAt_const).sub
          (ih.const_smul _)
      simp_rw [Matrix.nonsing_inv_eq_ringInverse]
      have hinv := contDiffAt_ringInverse ℝ (n := n) hu.unit
      rw [hu.unit_spec] at hinv
      exact hinv.comp η₀ hM

/-- The product `R_{[j,5]}` is `C^n` near a sample where `R_5, …, R_{q-1}` are invertible, for
every `j ≤ q - 1`. -/
private lemma SmallScoreSmooth_contDiffAt_chartProd {W q : ℕ} {g E : ℝ}
    {R : Matrix (Fin W) (Fin W) ℂ} {η₀ : Ω W q} {n : WithTop ℕ∞}
    (hU : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R η₀ j)) :
    ∀ j, j ≤ q - 1 → ContDiffAt ℝ n (fun η => chartProd W g E q R η j) η₀
  | 0, _ => by
    simp only [chartProd]
    exact contDiffAt_const
  | j + 1, hj => by
    by_cases h4 : j < 4
    · simp only [chartProd, h4, ↓reduceIte]
      exact contDiffAt_const
    · simp only [chartProd, h4, ↓reduceIte]
      exact (SmallScoreSmooth_contDiffAt_chartR hU (j + 1) hj).mul
        (SmallScoreSmooth_contDiffAt_chartProd hU j (by omega))

/-- `R_{[j,5]} = R_j ⋯ R_5` is invertible when `R_5, …, R_j` are. -/
private lemma SmallScoreSmooth_isUnit_chartProd {W q : ℕ} {g E : ℝ}
    {R : Matrix (Fin W) (Fin W) ℂ} {η₀ : Ω W q}
    (hU : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R η₀ j)) :
    ∀ j, j ≤ q - 1 → IsUnit (chartProd W g E q R η₀ j)
  | 0, _ => by simp [chartProd]
  | j + 1, hj => by
    simp only [chartProd]
    split_ifs with h4
    · exact isUnit_one
    · exact (hU (j + 1) (by omega) hj).mul (SmallScoreSmooth_isUnit_chartProd hU j (by omega))

/-- In standard coordinates, the field `X` of (9.10) [us:eq:physical] with generator `K(η)` is
`C^n` near a sample where `K` is `C^n`, `R_5, …, R_{q-1}` are invertible and `v ≠ 0`. -/
private lemma SmallScoreSmooth_contDiffAt_field {W q : ℕ} {g E : ℝ}
    {R : Matrix (Fin W) (Fin W) ℂ} {v : Fin W → ℂ} (hv : v ≠ 0)
    {Kf : Ω W q → Matrix (Fin W) (Fin W) ℂ} {η₀ : Ω W q} {n : WithTop ℕ∞}
    (hK : ContDiffAt ℝ n Kf η₀)
    (hU : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R η₀ j)) :
    ContDiffAt ℝ n (fun η => hermCoord W q (smallField W g E q R v (Kf η) η)) η₀ := by
  have hP := SmallScoreSmooth_contDiffAt_chartProd (n := n) hU (q - 1) le_rfl
  have hRq := SmallScoreSmooth_contDiffAt_chartR (n := n) hU (q - 1) le_rfl
  have ha : ContDiffAt ℝ n (fun η => chartProd W g E q R η (q - 1) *ᵥ v) η₀ :=
    SmallScoreSmooth_contDiffAt_mulVec hP contDiffAt_const
  have hb : ContDiffAt ℝ n (fun η => chartProd W g E q R η (q - 1) *ᵥ (Kf η *ᵥ v) -
      chartProd W g E q R η (q - 1) *ᵥ v) η₀ :=
    (SmallScoreSmooth_contDiffAt_mulVec hP
      (SmallScoreSmooth_contDiffAt_mulVec hK contDiffAt_const)).sub ha
  have ha0 : chartProd W g E q R η₀ (q - 1) *ᵥ v ≠ 0 := by
    intro h
    apply hv
    have hu := SmallScoreSmooth_isUnit_chartProd hU (q - 1) le_rfl
    exact Matrix.mulVec_injective_iff_isUnit.2 hu (h.trans (Matrix.mulVec_zero _).symm)
  have hL : ContDiffAt ℝ n (fun η => smallCorr W g E q R v (Kf η) η) η₀ :=
    SmallScoreSmooth_contDiffAt_rotCorr ha hb ha0
  have hV : ∀ i : Fin q, ContDiffAt ℝ n (fun η => gueBlock W q η i) η₀ := fun i =>
    (SmallScoreSmooth_contDiff_gueBlock W q i).contDiffAt
  have hX : ∀ i : Fin q, ContDiffAt ℝ n (fun η => smallField W g E q R v (Kf η) η i) η₀ := by
    intro i
    unfold smallField
    split_ifs
    · exact contDiffAt_const
    · have hA := (hV i).sub (contDiffAt_const (c := ((g : ℂ) ^ 2) • R))
      exact (hK.mul hA).sub (hA.mul hK)
    · exact (hK.mul (hV i)).sub ((hV i).mul hK)
    · have hA := (hV i).sub (hRq.const_smul ((g : ℂ) ^ 2))
      exact ((hK.mul (hV i)).sub ((hV i).mul hK)).sub ((hL.mul hA).sub (hA.mul hL))
  rw [contDiffAt_pi]
  intro p
  simp only [hermCoord]
  refine contDiffAt_const.mul (Complex.reCLM.contDiff.contDiffAt.comp η₀ ?_)
  simp only [Matrix.trace, Matrix.diag]
  have hM := (contDiffAt_const (c := hermBasis W (p.2.1, p.2.2))).mul (hX p.1)
  rw [SmallScoreSmooth_contDiffAt_matrix_iff] at hM
  exact ContDiffAt.sum fun k _ => hM k k

/-- The cut field `χ̂(R_4; ·; v_4) X` of Lemma 9.4 [us:lem:score] at the preparation
`(R_4, v_4) = (R, v)`, in standard coordinates, with `X` of (9.10) [us:eq:physical] built from
`K = K̂(R_4; ω; v_4)`. -/
def smallScoreField (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ)
    (Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ) (χh : Ω W q → (Fin W → ℂ) → ℝ) :
    Ω W q → Ω W q :=
  fun η => χh η v • hermCoord W q (smallField W g E q R v (Kh η v) η)

/-- Under the family clauses of Lemma 9.3 [su:lem:chosen-generator] at `(R_4, P) = (R, P)` and
`v_4 = v ≠ 0`, the cut field of Lemma 9.4 [us:lem:score] is `C¹` on `Ω W q`. -/
theorem contDiff_smallScoreField {W q : ℕ} {g E : ℝ} {P R : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Ω W q → (Fin W → ℂ) → ℝ} (hF : GenFamily W q g E P R Kh χh) (hv : v ≠ 0) :
    ContDiff ℝ 1 (smallScoreField W g E q R v Kh χh) := by
  obtain ⟨-, -, -, -, h5, ⟨G, hGo, hKG, hsupp⟩, -⟩ := hF
  rw [contDiff_iff_contDiffAt]
  intro η₀
  have hemb : ContDiff ℝ 1 (fun η : Ω W q => (η, v)) := contDiff_id.prodMk contDiff_const
  have h12 : (1 : WithTop ℕ∞) ≤ 2 := by norm_num
  have hχ : ContDiffAt ℝ 1 (fun η => χh η v) η₀ := by
    have hopen : IsOpen {p : Ω W q × (Fin W → ℂ) | p.2 ≠ 0} :=
      isOpen_ne_fun continuous_snd continuous_const
    have h2 : ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2) (η₀, v) :=
      h5.contDiffAt (hopen.mem_nhds hv)
    exact (h2.of_le h12).comp η₀ hemb.contDiffAt
  by_cases hs : (η₀, v) ∈ tsupport (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2)
  · obtain ⟨hG, hU⟩ := hsupp _ hs hv
    have hK2 : ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => Kh p.1 p.2) (η₀, v) :=
      hKG.contDiffAt (hGo.mem_nhds hG)
    have hK : ContDiffAt ℝ 1 (fun η => Kh η v) η₀ :=
      ContDiffAt.comp (g := fun p : Ω W q × (Fin W → ℂ) => Kh p.1 p.2) η₀ (hK2.of_le h12)
        hemb.contDiffAt
    exact hχ.fun_smul (SmallScoreSmooth_contDiffAt_field hv hK hU)
  · rw [notMem_tsupport_iff_eventuallyEq] at hs
    have h0 : ∀ᶠ η in nhds η₀, χh η v = 0 :=
      (hemb.continuous.tendsto η₀).eventually hs
    refine (contDiffAt_const (c := (0 : Ω W q))).congr_of_eventuallyEq ?_
    filter_upwards [h0] with η hη
    simp [smallScoreField, hη]

end LSBA
