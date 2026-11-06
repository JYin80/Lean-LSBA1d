import LSBA.Gauss.StdGauss
import LSBA.Model.Basic

/-!
# Appending GUE samples

Two independent GUE samples of `p` and `q` blocks form one sample of `p + q` blocks (1.2)
[eq:covariance]; used for the independence of transfer batches.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The first `p` and the last `q` blocks of a sample of `p + q` blocks. -/
def blockAppend (W p q : ℕ) (ω : Ω W (p + q)) : Ω W p × Ω W q :=
  (fun x => ω (Fin.castAdd q x.1, x.2), fun x => ω (Fin.natAdd p x.1, x.2))

/-- The first `p` and the last `q` blocks are independent samples of `p` and `q` GUE blocks
(1.2) [eq:covariance]. -/
theorem measurePreserving_blockAppend (W p q : ℕ) :
    MeasurePreserving (blockAppend W p q) (μ W (p + q)) ((μ W p).prod (μ W q)) := by
  let e : (Fin p × Fin W × Fin W) ⊕ (Fin q × Fin W × Fin W) ≃ Fin (p + q) × Fin W × Fin W :=
    { toFun := Sum.elim (fun x => (Fin.castAdd q x.1, x.2)) (fun x => (Fin.natAdd p x.1, x.2))
      invFun := fun y =>
        if h : (y.1 : ℕ) < p then Sum.inl (⟨y.1, h⟩, y.2)
        else Sum.inr (⟨(y.1 : ℕ) - p, by omega⟩, y.2)
      left_inv := by
        rintro (x | x)
        · simp
        · have h : ¬ ((Fin.natAdd p x.1 : Fin (p + q)) : ℕ) < p := by simp
          simp
      right_inv := by
        rintro ⟨y, a, b⟩
        by_cases h : (y : ℕ) < p
        · simp [h]
        · simp [h]; ext; simp; omega }
  have h1 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (p + q) × Fin W × Fin W => ℝ) e)
      (Measure.pi fun _ => gaussianReal 0 1) (Measure.pi fun _ => gaussianReal 0 1) :=
    measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1) e
  have h2 := measurePreserving_sumPiEquivProdPi
    (X := fun _ : (Fin p × Fin W × Fin W) ⊕ (Fin q × Fin W × Fin W) => ℝ)
    (fun _ => gaussianReal 0 1)
  have h3 := h1.symm.trans h2
  have hfun : blockAppend W p q =
      ⇑((MeasurableEquiv.piCongrLeft (fun _ : Fin (p + q) × Fin W × Fin W => ℝ) e).symm.trans
        (MeasurableEquiv.sumPiEquivProdPi fun _ : (Fin p × Fin W × Fin W) ⊕
          (Fin q × Fin W × Fin W) => ℝ)) := by
    funext ω
    rfl
  rw [hfun]
  exact h3

theorem gueBlock_blockAppend_fst (W p q : ℕ) (ω : Ω W (p + q)) (j : Fin p) :
    gueBlock W p (blockAppend W p q ω).1 j = gueBlock W (p + q) ω (Fin.castAdd q j) := by
  rfl

theorem gueBlock_blockAppend_snd (W p q : ℕ) (ω : Ω W (p + q)) (j : Fin q) :
    gueBlock W q (blockAppend W p q ω).2 j = gueBlock W (p + q) ω (Fin.natAdd p j) := by
  rfl

end LSBA
