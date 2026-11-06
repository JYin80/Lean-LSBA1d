import LSBA.Gauss.BlockWindow
import LSBA.Gauss.BlockAppend

/-!
# Conditioning on the first blocks of a GUE sample

Tonelli's theorem for a function `F ω' ω` of two samples of `q` GUE blocks (1.2) [eq:covariance]
that depends on `ω'` only through the coordinates of blocks `0, …, p - 1` and on `ω` only through
those of blocks `p, …, q - 1`: since the two groups of blocks are independent, the integral of
`F ω ω` equals the iterated integral. This is the averaging over the preparation blocks in the
proof of Lemma 8.12 [up:lem:small-contraction].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- The sample of `p + r` blocks whose first `p` blocks are those of `a` and whose last `r`
blocks are those of `b`. -/
private def prefixProductJoin {W p r : ℕ} (z : Ω W p × Ω W r) : Ω W (p + r) :=
  fun k => if h : (k.1 : ℕ) < p then z.1 (⟨k.1, h⟩, k.2)
    else z.2 (⟨(k.1 : ℕ) - p, by omega⟩, k.2)

private lemma prefixProductJoin_measurable {W p r : ℕ} :
    Measurable (prefixProductJoin (W := W) (p := p) (r := r)) := by
  refine measurable_pi_iff.mpr fun k => ?_
  unfold prefixProductJoin
  by_cases h : (k.1 : ℕ) < p
  · simp only [h, dite_true]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [h, dite_false]
    exact (measurable_pi_apply _).comp measurable_snd

private lemma prefixProductJoin_blockAppend {W p r : ℕ} (ω : Ω W (p + r)) :
    prefixProductJoin (blockAppend W p r ω) = ω := by
  funext k
  unfold prefixProductJoin blockAppend
  by_cases h : (k.1 : ℕ) < p
  · simp only [h, dite_true]
    congr 2
  · simp only [h, dite_false]
    congr 2
    ext
    simp
    omega

private lemma prefixProductJoin_fst {W p r : ℕ} (z : Ω W p × Ω W r)
    (k : Fin (p + r) × Fin W × Fin W) (h : (k.1 : ℕ) < p) :
    prefixProductJoin z k = z.1 (⟨k.1, h⟩, k.2) := by
  unfold prefixProductJoin
  simp [h]

private lemma prefixProductJoin_snd {W p r : ℕ} (z : Ω W p × Ω W r)
    (k : Fin (p + r) × Fin W × Fin W) (h : ¬ (k.1 : ℕ) < p) :
    prefixProductJoin z k = z.2 (⟨(k.1 : ℕ) - p, by omega⟩, k.2) := by
  unfold prefixProductJoin
  simp [h]

/-- Conditioning on blocks `0, …, p - 1` (1.2) [eq:covariance]: if `F ω' ω` depends on `ω'` only
through the coordinates of blocks `< p` and on `ω` only through those of blocks `≥ p`, then
`∫ F ω ω dμ(ω) = ∫∫ F ω' ω dμ(ω) dμ(ω')`. -/
theorem lintegral_prefix_diag {W q : ℕ} (p : ℕ) {F : Ω W q → Ω W q → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F))
    (h₁ : ∀ ω₁ ω₂ ω : Ω W q, (∀ k : Fin q × Fin W × Fin W, (k.1 : ℕ) < p → ω₁ k = ω₂ k) →
      F ω₁ ω = F ω₂ ω)
    (h₂ : ∀ ω' ω₁ ω₂ : Ω W q, (∀ k : Fin q × Fin W × Fin W, p ≤ (k.1 : ℕ) → ω₁ k = ω₂ k) →
      F ω' ω₁ = F ω' ω₂) :
    ∫⁻ ω, F ω ω ∂(μ W q) = ∫⁻ ω', ∫⁻ ω, F ω' ω ∂(μ W q) ∂(μ W q) := by
  by_cases hpq : q ≤ p
  · have hc : ∀ ω' ω : Ω W q, F ω' ω = F ω' 0 := fun ω' ω =>
      h₂ ω' ω 0 fun k hk => absurd (lt_of_lt_of_le k.1.2 hpq) (not_lt.mpr hk)
    simp only [hc _ _, lintegral_const, measure_univ, mul_one]
  · obtain ⟨r, rfl⟩ : ∃ r, q = p + r := ⟨q - p, by omega⟩
    set G : Ω W p × Ω W r → ℝ≥0∞ := fun z =>
      F (prefixProductJoin (z.1, 0)) (prefixProductJoin (0, z.2)) with hGdef
    have hG : Measurable G := by
      refine hF.comp (Measurable.prodMk ?_ ?_)
      · exact prefixProductJoin_measurable.comp (measurable_fst.prodMk measurable_const)
      · exact prefixProductJoin_measurable.comp (measurable_const.prodMk measurable_snd)
    have hFG : ∀ ω' ω : Ω W (p + r),
        F ω' ω = G ((blockAppend W p r ω').1, (blockAppend W p r ω).2) := by
      intro ω' ω
      simp only [hGdef]
      rw [h₁ ω' (prefixProductJoin ((blockAppend W p r ω').1, 0)) ω, h₂ _ ω
        (prefixProductJoin (0, (blockAppend W p r ω).2))]
      · intro k hk
        rw [prefixProductJoin_snd _ k (not_lt.mpr hk)]
        conv_lhs => rw [← prefixProductJoin_blockAppend ω]
        rw [prefixProductJoin_snd _ k (not_lt.mpr hk)]
      · intro k hk
        rw [prefixProductJoin_fst _ k hk]
        conv_lhs => rw [← prefixProductJoin_blockAppend ω']
        rw [prefixProductJoin_fst _ k hk]
    have hmp := measurePreserving_blockAppend W p r
    have hfst : MeasurePreserving (fun ω => (blockAppend W p r ω).1) (μ W (p + r)) (μ W p) :=
      measurePreserving_fst.comp hmp
    have hsnd : MeasurePreserving (fun ω => (blockAppend W p r ω).2) (μ W (p + r)) (μ W r) :=
      measurePreserving_snd.comp hmp
    have hinner : ∀ ω' : Ω W (p + r), ∫⁻ ω, F ω' ω ∂(μ W (p + r)) =
        ∫⁻ b, G ((blockAppend W p r ω').1, b) ∂(μ W r) := by
      intro ω'
      simp only [hFG ω']
      exact hsnd.lintegral_comp (f := fun b => G ((blockAppend W p r ω').1, b))
        (hG.comp (measurable_prodMk_left))
    have hH : Measurable fun a : Ω W p => ∫⁻ b, G (a, b) ∂(μ W r) :=
      hG.lintegral_prod_right'
    calc ∫⁻ ω, F ω ω ∂(μ W (p + r))
        = ∫⁻ ω, G (blockAppend W p r ω) ∂(μ W (p + r)) := by simp only [hFG]
      _ = ∫⁻ z, G z ∂((μ W p).prod (μ W r)) := hmp.lintegral_comp hG
      _ = ∫⁻ a, ∫⁻ b, G (a, b) ∂(μ W r) ∂(μ W p) := lintegral_prod _ hG.aemeasurable
      _ = ∫⁻ ω', ∫⁻ b, G ((blockAppend W p r ω').1, b) ∂(μ W r) ∂(μ W (p + r)) :=
        (hfst.lintegral_comp (f := fun a => ∫⁻ b, G (a, b) ∂(μ W r)) hH).symm
      _ = ∫⁻ ω', ∫⁻ ω, F ω' ω ∂(μ W (p + r)) ∂(μ W (p + r)) := by simp only [hinner]

end LSBA
