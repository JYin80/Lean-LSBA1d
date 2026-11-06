import LSBA.Upper.ScoreFrame

/-!
# The preparation of Lemma 8.12 [up:lem:small-contraction]

At fixed `R_4`, the graph coordinates `R_j` and products `R_{[j,5]}` of (9.2)
[su:eq:transported-normal] up to `j = q - 1` depend only on the active inputs `V_5, …, V_{q-1}`
(blocks `4, …, q - 2`), and the field `X` of (9.10) [us:eq:physical] only on `V_5, …, V_q`. Hence
the pointwise clauses of Lemma 9.3 [su:lem:chosen-generator] transfer between samples with the
same active inputs. Replacing the preparation blocks of a sample by those of `ω'` (proof of
Lemma 8.12 [up:lem:small-contraction]) then gives the pointwise clauses at the data
`(R_4, v_4)` of `ω'` wherever `χ̂(R_4; ·; v_4) ≠ 0`, and the hypotheses of Lemma 9.4
[us:lem:score] at that preparation when `χ̂(R_4; ·; v_4)` is not identically zero.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Block `a` of `Ω W L` depends only on the coordinates `ω (a, ·, ·)`. -/
private lemma SmallPrefix_gueBlock_congr {W L : ℕ} {ω ω' : Ω W L} {a : Fin L}
    (h : ∀ α β, ω (a, α, β) = ω' (a, α, β)) : gueBlock W L ω a = gueBlock W L ω' a := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, h]

/-- Splicing: for `ω, ω'` there is a sample with the blocks `0, …, 3` of `ω'` and the blocks
`4, …` of `ω`. -/
private lemma SmallPrefix_splice {W q : ℕ} (ω ω' : Ω W q) :
    ∃ ω'' : Ω W q, (∀ i : Fin q, (i : ℕ) < 4 → gueBlock W q ω'' i = gueBlock W q ω' i) ∧
      (∀ i : Fin q, 4 ≤ (i : ℕ) → gueBlock W q ω'' i = gueBlock W q ω i) := by
  refine ⟨fun k => if (k.1 : ℕ) < 4 then ω' k else ω k, fun i hi => ?_, fun i hi => ?_⟩
  · exact SmallPrefix_gueBlock_congr fun α β => by simp [hi]
  · exact SmallPrefix_gueBlock_congr fun α β => by simp [not_lt.mpr hi]

/-- The graph coordinates `R_j`, `j ≤ q - 1`, of (9.2) [su:eq:transported-normal] at a fixed `R_4`
depend only on the active inputs `V_5, …, V_{q-1}` (blocks `4, …, q - 2`). -/
theorem chartR_congr_active {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ} {ω ω' : Ω W q}
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q ω i = gueBlock W q ω' i)
    {j : ℕ} (hj : j ≤ q - 1) : chartR W g E q R ω j = chartR W g E q R ω' j := by
  induction j with
  | zero => simp [chartR]
  | succ j ih =>
    have ih' := ih (by omega)
    rw [chartR, chartR]
    by_cases h4 : j < 4
    · simp [h4]
    · have hjq : j < q := by omega
      have hb : blockSeq W q ω j = blockSeq W q ω' j := by
        simp only [blockSeq, hjq, ↓reduceDIte]
        exact h ⟨j, hjq⟩ (by simp; omega) (by simp; omega)
      simp only [h4, ↓reduceIte, hb, ih']

/-- The products `R_{[j,5]}`, `j ≤ q - 1`, of (9.2) [su:eq:transported-normal] at a fixed `R_4`
depend only on the active inputs `V_5, …, V_{q-1}`. -/
theorem chartProd_congr_active {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ} {ω ω' : Ω W q}
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q ω i = gueBlock W q ω' i)
    {j : ℕ} (hj : j ≤ q - 1) : chartProd W g E q R ω j = chartProd W g E q R ω' j := by
  induction j with
  | zero => simp [chartProd]
  | succ j ih =>
    have ih' := ih (by omega)
    rw [chartProd, chartProd]
    by_cases h4 : j < 4
    · simp [h4]
    · simp only [h4, ↓reduceIte, ih', chartR_congr_active h hj]

/-- The field `X` of (9.10) [us:eq:physical] at fixed `R_4`, `v_4` and `K` depends only on the
inputs `V_5, …, V_q`. -/
theorem smallField_congr_active {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {K : Matrix (Fin W) (Fin W) ℂ} {ω ω' : Ω W q}
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → gueBlock W q ω i = gueBlock W q ω' i) :
    smallField W g E q R v K ω = smallField W g E q R v K ω' := by
  funext i
  by_cases hi : (i : ℕ) < 4
  · simp [smallField, hi]
  · have hb := h i (not_lt.mp hi)
    have hc := chartR_congr_active (g := g) (E := E) (R := R) (fun i hi _ => h i hi)
      (le_refl (q - 1))
    have hp := chartProd_congr_active (g := g) (E := E) (R := R) (fun i hi _ => h i hi)
      (le_refl (q - 1))
    have hL : smallCorr W g E q R v K ω = smallCorr W g E q R v K ω' := by
      unfold smallCorr
      rw [hp]
    simp only [smallField, hb, hc, hL]

/-- The pointwise clauses of Lemma 9.3 [su:lem:chosen-generator] at the data `(R_4, v_4) = (R, v)`
depend only on the active inputs `V_5, …, V_{q-1}`. -/
theorem genPoint_congr_active {W q : ℕ} {g E C M₀ σ : ℝ} {P R : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {Kv : (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {ω ω' : Ω W q}
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q ω i = gueBlock W q ω' i)
    (hp : GenPoint W q g E P R v C M₀ σ Kv ω) : GenPoint W q g E P R v C M₀ σ Kv ω' := by
  have hc : ∀ j, j ≤ q - 1 → chartR W g E q R ω j = chartR W g E q R ω' j := fun j hj =>
    chartR_congr_active (g := g) (E := E) (R := R) h hj
  have hP : chartProd W g E q R ω (q - 1) = chartProd W g E q R ω' (q - 1) :=
    chartProd_congr_active (g := g) (E := E) (R := R) h (le_refl (q - 1))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  refine ⟨h1, h2, h3, ?_, fun j hj5 hjq => ?_, h6, ?_, h8, ?_, h10⟩
  · unfold IsGenNormalized at h4 ⊢
    rw [← hP]
    exact h4
  · rw [← hc j hjq]
    exact h5 j hj5 hjq
  · rw [← hP]
    exact h7
  · rw [← hc _ (le_refl (q - 1))]
    exact h9

/-- The transfer of the pointwise clauses of Lemma 9.3 [su:lem:chosen-generator] by replacing
the preparation blocks (proof of Lemma 8.12 [up:lem:small-contraction]): if `pre ω' ≠ 0`, they
hold at the data `(R_4, v_4) = (Rf ω', vf ω')` at every sample `ω` with
`χ̂(R_4; ω; v_4) ≠ 0`. -/
theorem genPoint_of_chosenGenerator {W q : ℕ} {g E C σ M₀ : ℝ} {x : IsoFlag W}
    {Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} {pre : Ω W q → ℝ}
    {Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ} {vf : Ω W q → Fin W → ℂ}
    {Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ}
    (hG : ChosenGenerator W q g E x Pf C σ M₀ pre Rf vf Kh χh) {ω' : Ω W q} (hpre : pre ω' ≠ 0)
    {ω : Ω W q} (hχ : χh (Rf ω') ω (vf ω') ≠ 0) :
    GenPoint W q g E (Pf (Rf ω')) (Rf ω') (vf ω') C M₀ σ (Kh (Rf ω') ω) ω := by
  obtain ⟨h01, -, -, -, hdep, -, -, -, -, hfam, hpt, -⟩ := hG
  obtain ⟨ω'', hlow, hhigh⟩ := SmallPrefix_splice ω ω'
  obtain ⟨hpre'', hR'', hv''⟩ := hdep ω'' ω' hlow
  have hF := (hfam ω' hpre).2.2.2
  have hK : Kh (Rf ω') ω'' = Kh (Rf ω') ω := funext fun w =>
    (hF.1 ω'' ω (fun i hi _ => hhigh i hi) w).1
  have hχ'' : χh (Rf ω') ω'' = χh (Rf ω') ω := funext fun w =>
    (hF.1 ω'' ω (fun i hi _ => hhigh i hi) w).2
  have hpre1 : pre ω' = 1 := (h01 ω').resolve_left hpre
  have hne : pre ω'' * χh (Rf ω'') ω'' (vf ω'') ≠ 0 := by
    rw [hpre'', hR'', hv'', hχ'', hpre1, one_mul]
    exact hχ
  have hp := hpt ω'' hne
  rw [hR'', hv'', hK] at hp
  exact genPoint_congr_active (fun i hi _ => hhigh i hi) hp

/-- The hypotheses of Lemma 9.4 [us:lem:score] at the preparation `(R_4, v_4) = (Rf ω', vf ω')` of a
sample with `pre ω' ≠ 0`, with `C_K = C`, when `χ̂(R_4; ·; v_4)` is not identically zero (proof of
Lemma 8.12 [up:lem:small-contraction]). -/
theorem scoreData_of_chosenGenerator {W q : ℕ} {g E C σ M₀ : ℝ} {x : IsoFlag W}
    {Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} {pre : Ω W q → ℝ}
    {Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ} {vf : Ω W q → Fin W → ℂ}
    {Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ} (hW : 1 ≤ W) (hq : 7 ≤ q)
    (hg : 0 < g) (hg1 : g ≤ 1) (hM₀ : 0 ≤ M₀)
    (hG : ChosenGenerator W q g E x Pf C σ M₀ pre Rf vf Kh χh) {ω' : Ω W q} (hpre : pre ω' ≠ 0)
    (hne : ∃ ω, χh (Rf ω') ω (vf ω') ≠ 0) :
    ScoreData W q g E M₀ C (Rf ω') (Pf (Rf ω')) (vf ω') (Kh (Rf ω')) (χh (Rf ω')) := by
  have hGP : ∀ ω, χh (Rf ω') ω (vf ω') ≠ 0 →
      GenPoint W q g E (Pf (Rf ω')) (Rf ω') (vf ω') C M₀ σ (Kh (Rf ω') ω) ω :=
    fun ω hω => genPoint_of_chosenGenerator hG hpre hω
  obtain ⟨-, -, -, -, -, hprep, -, -, -, hfam, -⟩ := hG
  obtain ⟨hRh, hv0, -⟩ := hprep ω' hpre
  obtain ⟨hPh, hPP, hPR, hF⟩ := hfam ω' hpre
  obtain ⟨ω₀, hω₀⟩ := hne
  have hlast := (hGP ω₀ hω₀).2.2.2.2.2.2.2.2.2
  refine ⟨hW, hq, hg, hg1, hM₀, hRh, hv0, hPh, hPP, hPR, hF, fun ω hω => ?_, hlast⟩
  obtain ⟨-, hk, hpkp, hn, -, hs, -⟩ := hGP ω hω
  exact ⟨hk, hpkp, hn, hs⟩

end LSBA
