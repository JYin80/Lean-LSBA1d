import LSBA.Gauss.BlockWindow

/-!
# Appending one fresh block

A sample of `n + 1` GUE blocks is a sample of `n` blocks and one fresh block (`blockSnoc`), measure
preserving through the window of the first `n` blocks; Tonelli for one fresh block, as used by the
transition operator (11.11) [lg:eq:transition].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The sample of `n + 1` blocks whose first `n` blocks are those of `ω` and whose last block
is that of `ω'` (1.2) [eq:covariance]. -/
def blockSnoc {W n : ℕ} (ω : Ω W n) (ω' : Ω W 1) : Ω W (n + 1) :=
  fun p => if h : (p.1 : ℕ) < n then ω (⟨p.1, h⟩, p.2) else ω' (0, p.2)

/-- The splitting of the index set of `n + 1` blocks into the first `n` blocks and the last one. -/
private def blockSnocIdx (W n : ℕ) :
    (Fin n × Fin W × Fin W) ⊕ (Fin 1 × Fin W × Fin W) ≃ Fin (n + 1) × Fin W × Fin W where
  toFun x := Sum.elim (fun a => (Fin.castSucc a.1, a.2)) (fun b => (Fin.last n, b.2)) x
  invFun p :=
    if h : (p.1 : ℕ) < n then Sum.inl (⟨p.1, h⟩, p.2) else Sum.inr (0, p.2)
  left_inv x := by
    rcases x with ⟨a, α, β⟩ | ⟨b, α, β⟩
    · simp
    · have hb : b = 0 := Subsingleton.elim _ _
      simp [hb]
  right_inv p := by
    obtain ⟨a, α, β⟩ := p
    by_cases h : (a : ℕ) < n
    · simp [h]
    · have ha : a = Fin.last n := Fin.ext (by have := a.2; simp only [Fin.val_last]; omega)
      simp [ha]

/-- The map `blockSnoc` carries the product `μ W n ⊗ μ W 1` to `μ W (n + 1)`. -/
private lemma blockSnoc_measurePreserving (W n : ℕ) :
    MeasurePreserving (fun p : Ω W n × Ω W 1 => blockSnoc p.1 p.2)
      ((μ W n).prod (μ W 1)) (μ W (n + 1)) := by
  have h1 := measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : (Fin n × Fin W × Fin W) ⊕ (Fin 1 × Fin W × Fin W) => ℝ)
    (fun _ => gaussianReal 0 1)
  have h2 := measurePreserving_piCongrLeft
    (α := fun _ : Fin (n + 1) × Fin W × Fin W => ℝ)
    (fun _ => gaussianReal 0 1) (blockSnocIdx W n)
  have h3 := h2.comp h1
  have key : (fun p : Ω W n × Ω W 1 => blockSnoc p.1 p.2) =
      ⇑(MeasurableEquiv.piCongrLeft
        (fun _ : Fin (n + 1) × Fin W × Fin W => ℝ) (blockSnocIdx W n)) ∘
      ⇑(MeasurableEquiv.sumPiEquivProdPi
        (fun _ : (Fin n × Fin W × Fin W) ⊕ (Fin 1 × Fin W × Fin W) => ℝ)).symm := by
    funext ⟨ω, ω'⟩ p
    obtain ⟨a, α, β⟩ := p
    have hp : (a, α, β) = blockSnocIdx W n (((blockSnocIdx W n).symm (a, α, β))) := by simp
    simp only [Function.comp_apply]
    rw [hp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    by_cases h : (a : ℕ) < n
    · simp [blockSnoc, blockSnocIdx, h]
      rfl
    · simp [blockSnoc, blockSnocIdx, h]
      rfl
  rw [key]
  exact h3

/-- A fresh last block is independent of the first `n` blocks: Tonelli's theorem for
`μ W (n + 1) = μ W n ⊗ μ W 1` along `blockSnoc`. -/
theorem lintegral_blockSnoc (W n : ℕ) {F : Ω W (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F ω ∂(μ W (n + 1)) = ∫⁻ ω, ∫⁻ ω', F (blockSnoc ω ω') ∂(μ W 1) ∂(μ W n) := by
  have hmp := blockSnoc_measurePreserving W n
  have h := hmp.lintegral_comp hF
  rw [← h]
  exact lintegral_prod _ (hF.comp hmp.measurable).aemeasurable

theorem windowSample_blockSnoc {W n : ℕ} (ω : Ω W n) (ω' : Ω W 1) :
    windowSample Fin.castSucc (blockSnoc ω ω') = ω := by
  funext p
  obtain ⟨a, α, β⟩ := p
  simp [windowSample, blockSnoc]

theorem gueBlock_blockSnoc_last {W n : ℕ} (ω : Ω W n) (ω' : Ω W 1) :
    gueBlock W (n + 1) (blockSnoc ω ω') (Fin.last n) = gueBlock W 1 ω' 0 := by
  ext α β
  simp [gueBlock, blockSnoc]

end LSBA
