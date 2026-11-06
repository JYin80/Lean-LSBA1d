import LSBA.Gauss.FreshBlock

/-!
# Events of one fresh GUE block

A function on `Ω W L` that does not see block `a` is fixed before block `a` is sampled. For an
event that is jointly measurable in the block `V_a` and in such data `D`, a bound
`P(event) ≤ b` for the `W × W` GUE matrix at every fixed value of `D` on a set `S` of the other
blocks passes to the full sample as `P(S ∩ event) ≤ b P(S)`. This is the conditioning on the past
used for the fresh blocks of Appendix G [app:upper-gue] (after (G.5)
[us:eq:preliminary-range]) and for Lemma 9.5 [us:lem:range] and Corollary 9.7
[nc:lem:compression] applied to block `V_5`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `f` does not depend on block `a`: it takes the same value on samples that agree off
block `a`. -/
def OffBlock {X : Type*} (W L : ℕ) (a : Fin L) (f : Ω W L → X) : Prop :=
  ∀ ω ω' : Ω W L, (∀ x, x.1 ≠ a → ω x = ω' x) → f ω = f ω'

/-- The sample that is `ρ` on the blocks other than `a` and `0` on block `a`. -/
private def freshEvent_ext (W L : ℕ) (a : Fin L)
    (ρ : {x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) : Ω W L :=
  fun x => if h : x.1 ≠ a then ρ ⟨x, h⟩ else 0

private lemma freshEvent_measurable_ext (W L : ℕ) (a : Fin L) :
    Measurable (freshEvent_ext W L a) := by
  refine measurable_pi_iff.mpr fun x => ?_
  unfold freshEvent_ext
  by_cases h : x.1 = a
  · simp only [ne_eq, h, not_true_eq_false, ↓reduceDIte]
    exact measurable_const
  · simp only [ne_eq, h, not_false_eq_true, ↓reduceDIte]
    exact measurable_pi_apply _

private lemma freshEvent_ext_split (W L : ℕ) (a : Fin L) (ω : Ω W L) (x : Fin L × Fin W × Fin W)
    (hx : x.1 ≠ a) : freshEvent_ext W L a (blockSplit W L a ω).2 x = ω x := by
  simp [freshEvent_ext, blockSplit, hx]

/-- Block `a` of the sample, as a `W × W` matrix, is measurable in the sample. -/
private lemma freshEvent_measurable_gueBlock (W L : ℕ) (a : Fin L) :
    Measurable fun ω : Ω W L => gueBlock W L ω a := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- An event of block `a` and of data `D` fixed before block `a`: if, for every sample in a
measurable set `S` not depending on block `a`, the `W × W` GUE matrix falls in the section of `T`
at `D ω` with probability at most `b`, then `P(S ∩ {(V_a, D) ∈ T}) ≤ b P(S)`. -/
theorem measure_gueBlock_fresh_le (W L : ℕ) (a : Fin L) {X : Type*} [MeasurableSpace X]
    {D : Ω W L → X} (hD : Measurable D) (hDa : OffBlock W L a D) {S : Set (Ω W L)}
    (hS : MeasurableSet S) (hSa : OffBlock W L a (· ∈ S))
    {T : Set (Matrix (Fin W) (Fin W) ℂ × X)} (hT : MeasurableSet T) {b : ℝ≥0∞}
    (hb : ∀ ω ∈ S, μ W 1 {ω' | (gueMat W ω', D ω) ∈ T} ≤ b) :
    μ W L {ω | ω ∈ S ∧ (gueBlock W L ω a, D ω) ∈ T} ≤ b * μ W L S := by
  have hE := freshEvent_measurable_ext W L a
  have hgm : Measurable fun ω : Ω W 1 => gueMat W ω := freshEvent_measurable_gueBlock W 1 0
  have hag : ∀ ω : Ω W L, ∀ x, x.1 ≠ a →
      freshEvent_ext W L a (blockSplit W L a ω).2 x = ω x :=
    fun ω x hx => freshEvent_ext_split W L a ω x hx
  have hDe : ∀ ω : Ω W L, D (freshEvent_ext W L a (blockSplit W L a ω).2) = D ω :=
    fun ω => hDa _ _ (hag ω)
  have hSe : ∀ ω : Ω W L, freshEvent_ext W L a (blockSplit W L a ω).2 ∈ S ↔ ω ∈ S :=
    fun ω => Eq.to_iff (hSa _ _ (hag ω))
  let F : Matrix (Fin W) (Fin W) ℂ → ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) → ℝ≥0∞ :=
    fun V ρ => Set.indicator {p : Matrix (Fin W) (Fin W) ℂ ×
      ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) |
      freshEvent_ext W L a p.2 ∈ S ∧ (p.1, D (freshEvent_ext W L a p.2)) ∈ T}
      (fun _ => (1 : ℝ≥0∞)) (V, ρ)
  have hmeasSet : MeasurableSet {p : Matrix (Fin W) (Fin W) ℂ ×
      ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) |
      freshEvent_ext W L a p.2 ∈ S ∧ (p.1, D (freshEvent_ext W L a p.2)) ∈ T} :=
    (hS.preimage (hE.comp measurable_snd)).inter
      (hT.preimage (measurable_fst.prodMk (hD.comp (hE.comp measurable_snd))))
  have hF : Measurable (Function.uncurry F) := measurable_const.indicator hmeasSet
  let B : ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) → ℝ≥0∞ :=
    fun ρ => S.indicator (fun _ => b) (freshEvent_ext W L a ρ)
  have hB : ∀ ρ, ∫⁻ ω', F (gueMat W ω') ρ ∂(μ W 1) ≤ B ρ := by
    intro ρ
    by_cases hρ : freshEvent_ext W L a ρ ∈ S
    · have hT' : MeasurableSet {ω' : Ω W 1 |
          (gueMat W ω', D (freshEvent_ext W L a ρ)) ∈ T} :=
        hT.preimage (hgm.prodMk measurable_const)
      have e : (fun ω' : Ω W 1 => F (gueMat W ω') ρ) =
          Set.indicator {ω' : Ω W 1 | (gueMat W ω', D (freshEvent_ext W L a ρ)) ∈ T}
            (fun _ => (1 : ℝ≥0∞)) := by
        funext ω'
        simp only [F, Set.indicator_apply, Set.mem_ofPred_eq, hρ, true_and]
      rw [e, lintegral_indicator_const hT', one_mul]
      simpa only [B, Set.indicator_of_mem hρ] using hb _ hρ
    · have e : (fun ω' : Ω W 1 => F (gueMat W ω') ρ) = fun _ => 0 := by
        funext ω'
        simp only [F, Set.indicator_apply, Set.mem_ofPred_eq, hρ, false_and, ite_false]
      rw [e, lintegral_zero]
      exact zero_le
  have key := lintegral_gueBlock_fresh_le W L a hF hB
  have hL : ∫⁻ ω, F (gueBlock W L ω a) (blockSplit W L a ω).2 ∂(μ W L) =
      μ W L {ω | ω ∈ S ∧ (gueBlock W L ω a, D ω) ∈ T} := by
    have hset : MeasurableSet {ω : Ω W L | ω ∈ S ∧ (gueBlock W L ω a, D ω) ∈ T} := by
      exact (hS.inter (hT.preimage ((freshEvent_measurable_gueBlock W L a).prodMk hD)))
    rw [← lintegral_indicator_one hset]
    refine lintegral_congr fun ω => ?_
    simp only [F, Set.indicator_apply, Set.mem_ofPred_eq, hSe, hDe, Pi.one_apply]
  have hR : ∫⁻ ω, B (blockSplit W L a ω).2 ∂(μ W L) = b * μ W L S := by
    have : (fun ω => B (blockSplit W L a ω).2) = S.indicator (fun _ => b) := by
      funext ω
      simp only [B, Set.indicator_apply, hSe]
    rw [this, lintegral_indicator_const hS]
  rw [← hL, ← hR]
  exact key

end LSBA
