import LSBA.Gauss.StdGauss
import LSBA.Model.Basic

/-!
# Independence of one block

The coordinates of block `a` and of the other blocks are independent standard Gaussian vectors
under `μ W L` (the product structure of (1.2) [eq:covariance]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Coordinates of block `a` and of the other blocks. -/
def blockSplit (W L : ℕ) (a : Fin L) (ω : Ω W L) :
    (Fin W × Fin W → ℝ) × ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) :=
  (fun k => ω (a, k), fun x => ω x.1)

/-- The indices of block `a` as a subtype of all indices. -/
private def blockSplitIdx (W L : ℕ) (a : Fin L) :
    Fin W × Fin W ≃ {x : Fin L × Fin W × Fin W // x.1 = a} where
  toFun k := ⟨(a, k), rfl⟩
  invFun x := x.1.2
  left_inv _ := rfl
  right_inv x := by
    obtain ⟨⟨i, k⟩, h⟩ := x
    simp only at h
    subst h
    rfl

/-- Block `a` is independent of the other blocks, both standard Gaussian. -/
theorem measurePreserving_blockSplit (W L : ℕ) (a : Fin L) :
    MeasurePreserving (blockSplit W L a) (μ W L)
      ((stdGauss (Fin W × Fin W)).prod (stdGauss {x : Fin L × Fin W × Fin W // x.1 ≠ a})) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin L × Fin W × Fin W =>
    gaussianReal 0 1) (fun x => x.1 = a)
  have h2 := (measurePreserving_piCongrLeft
    (α := fun _ : {x : Fin L × Fin W × Fin W // x.1 = a} => ℝ)
    (fun _ => gaussianReal 0 1) (blockSplitIdx W L a)).symm
  have h3 := h2.prod (MeasurePreserving.id
    (Measure.pi fun _ : {x : Fin L × Fin W × Fin W // ¬ x.1 = a} => gaussianReal 0 1))
  have h4 := h3.comp h1
  have key : blockSplit W L a = Prod.map
      (⇑(MeasurableEquiv.piCongrLeft (fun _ : {x : Fin L × Fin W × Fin W // x.1 = a} => ℝ)
        (blockSplitIdx W L a)).symm) id ∘
      ⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin L × Fin W × Fin W => ℝ)
        (fun x => x.1 = a)) := by
    funext ω
    refine Prod.ext ?_ ?_
    · funext k
      simp [blockSplit, blockSplitIdx, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
        MeasurableEquiv.piEquivPiSubtypeProd]
    · rfl
  rw [key]
  exact h4

end LSBA
