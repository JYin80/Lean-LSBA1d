import LSBA.Transfer.Transition

/-!
# Products along the state chain with time-dependent factors

If, for every time `i`, the one-step integral of a factor `Z_i(X, V)` over a fresh block is at
most `q_i` at every state, then `𝔼 ∏_{i<n} Z_i(X_i, V_i) ≤ ∏_{i<n} q_i` along the chain of
Section 11.1 [lg:sec:scalar-growth] started at any state. The Markov property is used through the
integrated identities of the transition operator (11.11) [lg:eq:transition], with no filtration.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `𝔼 ∏_{i<n} Z_i(X_i, V_i) ≤ ∏_{i<n} q_i` when every one-step integral of `Z_i` is at most
`q_i` at every state. -/
theorem lintegral_prodSeq_chainState_le (g E : ℝ) {W : ℕ}
    (Z : ℕ → State W → Matrix (Fin W) (Fin W) ℂ → ℝ≥0∞)
    (hZ : ∀ i, Measurable (fun p : State W × Matrix (Fin W) (Fin W) ℂ => Z i p.1 p.2))
    (q : ℕ → ℝ≥0∞)
    (hq : ∀ i, ∀ X : State W, IsState X → ∫⁻ ω, Z i X (gueBlock W 1 ω 0) ∂(μ W 1) ≤ q i)
    {X₀ : State W} (hX₀ : IsState X₀) (n : ℕ) :
    ∫⁻ ω, ∏ i ∈ Finset.range n,
        Z i (chainState g E X₀ (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) i)
          (if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) ∂(μ W n) ≤
      ∏ i ∈ Finset.range n, q i := by
  -- The blocks of a sample of `m` blocks as a sequence padded by `0`.
  let tb : (m : ℕ) → Ω W m → ℕ → Matrix (Fin W) (Fin W) ℂ :=
    fun m ω k => if h : k < m then gueBlock W m ω ⟨k, h⟩ else 0
  have hmgb : ∀ (L : ℕ) (a : Fin L), Measurable fun ω : Ω W L => gueBlock W L ω a := by
    intro L a
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    unfold gueBlock
    simp only [Matrix.of_apply]
    split_ifs <;> fun_prop
  have hmtb : ∀ m, Measurable (tb m) := by
    intro m
    refine measurable_pi_iff.mpr fun k => ?_
    by_cases h : k < m
    · simp only [tb, h, dite_true]
      exact hmgb m ⟨k, h⟩
    · simp only [tb, h, dite_false]
      exact measurable_const
  have hmch : ∀ m i, Measurable fun ω : Ω W m => chainState g E X₀ (tb m ω) i := by
    intro m i
    induction i with
    | zero => exact measurable_const
    | succ i ih =>
      have hb : Measurable fun ω : Ω W m => tb m ω i :=
        (measurable_pi_apply i).comp (hmtb m)
      have h := (measurable_stepState g E W).comp (ih.prodMk hb)
      exact h
  have hcongr : ∀ {V V' : ℕ → Matrix (Fin W) (Fin W) ℂ} {i : ℕ},
      (∀ k < i, V k = V' k) → chainState g E X₀ V i = chainState g E X₀ V' i := by
    intro V V' i h
    induction i with
    | zero => rfl
    | succ i ih =>
      change stepState g E (chainState g E X₀ V i) (V i) =
        stepState g E (chainState g E X₀ V' i) (V' i)
      rw [ih fun k hk => h k (Nat.lt_succ_of_lt hk), h i (Nat.lt_succ_self i)]
  have hstate : ∀ m (ω : Ω W m) i, IsState (chainState g E X₀ (tb m ω) i) := by
    intro m ω i
    induction i with
    | zero => exact hX₀
    | succ i ih =>
      refine isState_stepState g E ih ?_
      simp only [tb]
      split_ifs
      · exact gueBlock_isHermitian W m ω _
      · exact Matrix.isHermitian_zero
  have hsl : ∀ {m : ℕ} (ω : Ω W m) (ω' : Ω W 1) {k : ℕ}, k < m →
      tb (m + 1) (blockSnoc ω ω') k = tb m ω k := by
    intro m ω ω' k hk
    have hk' : k < m + 1 := Nat.lt_succ_of_lt hk
    simp only [tb, hk', hk, dite_true]
    ext α β
    simp [gueBlock, blockSnoc, hk]
  have hsn : ∀ {m : ℕ} (ω : Ω W m) (ω' : Ω W 1),
      tb (m + 1) (blockSnoc ω ω') m = gueBlock W 1 ω' 0 := by
    intro m ω ω'
    have hm : m < m + 1 := Nat.lt_succ_self m
    simp only [tb, hm, dite_true]
    exact gueBlock_blockSnoc_last ω ω'
  have hcl : ∀ {m : ℕ} (ω : Ω W m) (ω' : Ω W 1) {i : ℕ}, i ≤ m →
      chainState g E X₀ (tb (m + 1) (blockSnoc ω ω')) i = chainState g E X₀ (tb m ω) i := by
    intro m ω ω' i hi
    exact hcongr fun _ hk => hsl ω ω' (lt_of_lt_of_le hk hi)
  have hmeas : ∀ m : ℕ, Measurable fun ω : Ω W m => ∏ i ∈ Finset.range m,
      Z i (chainState g E X₀ (tb m ω) i) (tb m ω i) := fun m =>
    Finset.measurable_prod _ fun i _ => (hZ i).comp
      ((hmch m i).prodMk ((measurable_pi_apply i).comp (hmtb m)))
  change ∫⁻ ω, ∏ i ∈ Finset.range n,
    Z i (chainState g E X₀ (tb n ω) i) (tb n ω i) ∂(μ W n) ≤ ∏ i ∈ Finset.range n, q i
  induction n with
  | zero => simp
  | succ n ih =>
    have hpt : ∀ (ω : Ω W n) (ω' : Ω W 1), ∏ i ∈ Finset.range (n + 1),
        Z i (chainState g E X₀ (tb (n + 1) (blockSnoc ω ω')) i)
          (tb (n + 1) (blockSnoc ω ω') i) =
        (∏ i ∈ Finset.range n, Z i (chainState g E X₀ (tb n ω) i) (tb n ω i)) *
          Z n (chainState g E X₀ (tb n ω) n) (gueBlock W 1 ω' 0) := by
      intro ω ω'
      rw [Finset.prod_range_succ]
      congr 1
      · refine Finset.prod_congr rfl fun i hi => ?_
        have hin : i < n := Finset.mem_range.mp hi
        rw [hcl ω ω' hin.le, hsl ω ω' hin]
      · rw [hcl ω ω' le_rfl, hsn]
    rw [lintegral_blockSnoc W n (hmeas (n + 1))]
    simp only [hpt]
    calc ∫⁻ ω, ∫⁻ ω', (∏ i ∈ Finset.range n,
            Z i (chainState g E X₀ (tb n ω) i) (tb n ω i)) *
          Z n (chainState g E X₀ (tb n ω) n) (gueBlock W 1 ω' 0) ∂(μ W 1) ∂(μ W n)
        = ∫⁻ ω, (∏ i ∈ Finset.range n,
            Z i (chainState g E X₀ (tb n ω) i) (tb n ω i)) *
          ∫⁻ ω', Z n (chainState g E X₀ (tb n ω) n) (gueBlock W 1 ω' 0) ∂(μ W 1)
            ∂(μ W n) := by
          refine lintegral_congr fun ω => ?_
          exact lintegral_const_mul _
            ((hZ n).comp (measurable_const.prodMk (hmgb 1 0)))
      _ ≤ ∫⁻ ω, (∏ i ∈ Finset.range n,
            Z i (chainState g E X₀ (tb n ω) i) (tb n ω i)) * q n ∂(μ W n) := by
          refine lintegral_mono fun ω => ?_
          exact mul_le_mul_right (hq n _ (hstate n ω n)) _
      _ = (∫⁻ ω, ∏ i ∈ Finset.range n,
            Z i (chainState g E X₀ (tb n ω) i) (tb n ω i) ∂(μ W n)) * q n :=
          lintegral_mul_const _ (hmeas n)
      _ ≤ (∏ i ∈ Finset.range n, q i) * q n := mul_le_mul_left ih _
      _ = ∏ i ∈ Finset.range (n + 1), q i := (Finset.prod_range_succ q n).symm

end LSBA
