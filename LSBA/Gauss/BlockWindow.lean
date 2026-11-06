import LSBA.Gauss.StdGauss
import LSBA.Model.Basic

/-!
# Block windows of a GUE sample

The blocks of a sample in an injective window `s : Fin q → Fin L` form a sample of `q` independent
GUE blocks (1.2) [eq:covariance]; joining window blocks with exterior coordinates, and Tonelli's
theorem for that product (conditioning on the exterior of a window).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The blocks of `ω` in the window `s`, as a sample of `q` blocks: `(V_{s(0)}, …, V_{s(q-1)})`
of (1.2) [eq:covariance]. -/
def windowSample {W L q : ℕ} (s : Fin q → Fin L) (ω : Ω W L) : Ω W q :=
  fun p => ω (s p.1, p.2)

/-- The sample of `L` blocks whose blocks in the window `s` are those of `v` and whose other
coordinates are `e`. -/
def windowJoin {W L q : ℕ} (s : Fin q → Fin L) (v : Ω W q)
    (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range s} → ℝ) : Ω W L :=
  fun p => if h : p.1 ∈ Set.range s then v (h.choose, p.2) else e ⟨p, h⟩

/-- The indices of the window blocks as a subtype of all indices. -/
private def blockWindowIdx {W L q : ℕ} {s : Fin q → Fin L} (hs : Function.Injective s) :
    Fin q × Fin W × Fin W ≃ {x : Fin L × Fin W × Fin W // x.1 ∈ Set.range s} where
  toFun k := ⟨(s k.1, k.2), ⟨k.1, rfl⟩⟩
  invFun x := (x.2.choose, x.1.2)
  left_inv k := by
    have h : s (Exists.choose (⟨k.1, rfl⟩ : s k.1 ∈ Set.range s)) = s k.1 :=
      Exists.choose_spec (⟨k.1, rfl⟩ : s k.1 ∈ Set.range s)
    simp [hs h]
  right_inv x := by
    obtain ⟨⟨a, k⟩, hx⟩ := x
    have h : s hx.choose = a := hx.choose_spec
    apply Subtype.ext
    simp [h]

/-- The window blocks together with the exterior coordinates, jointly standard Gaussian. -/
private lemma blockWindow_split {W L q : ℕ} {s : Fin q → Fin L} (hs : Function.Injective s) :
    MeasurePreserving
      (fun ω : Ω W L => (windowSample s ω, fun x : {p : Fin L × Fin W × Fin W //
        p.1 ∉ Set.range s} => ω x.1))
      (μ W L)
      ((μ W q).prod (stdGauss {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range s})) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin L × Fin W × Fin W =>
    gaussianReal 0 1) (fun x => x.1 ∈ Set.range s)
  have h2 := (measurePreserving_piCongrLeft
    (α := fun _ : {x : Fin L × Fin W × Fin W // x.1 ∈ Set.range s} => ℝ)
    (fun _ => gaussianReal 0 1) (blockWindowIdx (W := W) hs)).symm
  have h3 := h2.prod (MeasurePreserving.id
    (Measure.pi fun _ : {x : Fin L × Fin W × Fin W // ¬ x.1 ∈ Set.range s} =>
      gaussianReal 0 1))
  have h4 := h3.comp h1
  have key : (fun ω : Ω W L => (windowSample s ω, fun x : {p : Fin L × Fin W × Fin W //
        p.1 ∉ Set.range s} => ω x.1)) = Prod.map
      (⇑(MeasurableEquiv.piCongrLeft
        (fun _ : {x : Fin L × Fin W × Fin W // x.1 ∈ Set.range s} => ℝ)
        (blockWindowIdx (W := W) hs)).symm) id ∘
      ⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin L × Fin W × Fin W => ℝ)
        (fun x => x.1 ∈ Set.range s)) := by
    funext ω
    refine Prod.ext ?_ ?_
    · funext k
      simp [windowSample, blockWindowIdx, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
        MeasurableEquiv.piEquivPiSubtypeProd]
    · rfl
  rw [key]
  exact h4

private lemma blockWindow_measurable_join {W L q : ℕ} (s : Fin q → Fin L) :
    Measurable (fun z : Ω W q × ({p : Fin L × Fin W × Fin W // p.1 ∉ Set.range s} → ℝ) =>
      windowJoin s z.1 z.2) := by
  refine measurable_pi_iff.mpr fun p => ?_
  unfold windowJoin
  by_cases h : p.1 ∈ Set.range s
  · simp only [h, dite_true]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [h, dite_false]
    exact (measurable_pi_apply _).comp measurable_snd

private lemma blockWindow_join_split {W L q : ℕ} (s : Fin q → Fin L) (ω : Ω W L) :
    windowJoin s (windowSample s ω) (fun x => ω x.1) = ω := by
  funext p
  unfold windowJoin windowSample
  by_cases h : p.1 ∈ Set.range s
  · simp only [h, dite_true]
    have := h.choose_spec
    rw [this]
  · simp [h]

/-- For an injective window, the blocks in the window are `q` independent GUE blocks
(1.2) [eq:covariance]. -/
theorem measurePreserving_windowSample (W L q : ℕ) {s : Fin q → Fin L}
    (hs : Function.Injective s) :
    MeasurePreserving (windowSample (W := W) s) (μ W L) (μ W q) := by
  exact (measurePreserving_fst (μ := μ W q)
    (ν := stdGauss {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range s})).comp
    (blockWindow_split (W := W) (L := L) (q := q) hs)

/-- Conditioning on the coordinates outside an injective window: Tonelli's theorem for the
product of the window law `μ W q` and the exterior law. -/
theorem lintegral_windowJoin (W L q : ℕ) {s : Fin q → Fin L} (hs : Function.Injective s)
    {F : Ω W L → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F ω ∂(μ W L) =
      ∫⁻ e, ∫⁻ v, F (windowJoin s v e) ∂(μ W q)
        ∂(stdGauss {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range s}) := by
  have hsplit := blockWindow_split (W := W) (L := L) (q := q) hs
  have hG : Measurable fun z : Ω W q × ({p : Fin L × Fin W × Fin W // p.1 ∉ Set.range s} → ℝ) =>
      F (windowJoin s z.1 z.2) := hF.comp (blockWindow_measurable_join s)
  have h1 : ∫⁻ ω, F ω ∂(μ W L) = ∫⁻ ω, (fun z : Ω W q × ({p : Fin L × Fin W × Fin W //
      p.1 ∉ Set.range s} → ℝ) => F (windowJoin s z.1 z.2))
        ((fun ω : Ω W L => (windowSample s ω, fun x : {p : Fin L × Fin W × Fin W //
          p.1 ∉ Set.range s} => ω x.1)) ω) ∂(μ W L) := by
    refine lintegral_congr fun ω => ?_
    simp only [blockWindow_join_split]
  rw [h1, hsplit.lintegral_comp hG, lintegral_prod _ hG.aemeasurable,
    lintegral_lintegral_swap hG.aemeasurable]

theorem gueBlock_windowSample {W L q : ℕ} (s : Fin q → Fin L) (ω : Ω W L) (j : Fin q) :
    gueBlock W q (windowSample s ω) j = gueBlock W L ω (s j) := by
  rfl

theorem gueBlock_windowJoin_apply {W L q : ℕ} {s : Fin q → Fin L} (hs : Function.Injective s)
    (v : Ω W q) (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range s} → ℝ) (j : Fin q) :
    gueBlock W L (windowJoin s v e) (s j) = gueBlock W q v j := by
  have hj : ∀ (α β : Fin W), windowJoin s v e (s j, α, β) = v (j, α, β) := by
    intro α β
    have hm : s j ∈ Set.range s := ⟨j, rfl⟩
    have hc : hm.choose = j := hs hm.choose_spec
    simp [windowJoin, hm, hc]
  ext α β
  simp only [gueBlock, Matrix.of_apply, hj]

theorem gueBlock_windowJoin_of_not_mem {W L q : ℕ} (s : Fin q → Fin L) (v v' : Ω W q)
    (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range s} → ℝ) {a : Fin L}
    (ha : a ∉ Set.range s) :
    gueBlock W L (windowJoin s v e) a = gueBlock W L (windowJoin s v' e) a := by
  have hj : ∀ (α β : Fin W), windowJoin s v e (a, α, β) = windowJoin s v' e (a, α, β) := by
    intro α β
    simp [windowJoin, ha]
  ext α β
  simp only [gueBlock, Matrix.of_apply, hj]

end LSBA
