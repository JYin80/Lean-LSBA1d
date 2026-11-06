import LSBA.Transfer.StateChain
import LSBA.Gauss.BlockSnoc

/-!
# The transition operator

The one-block transition operator `P_g` of (11.11) [lg:eq:transition] on functions of the state
(Bochner and lintegral forms) and the mean increment `P_g c`; the Markov property as integrated
identities with an arbitrary measurable factor of the first `n` blocks, with no filtration; and the
product bound `𝔼 ∏_{i<n} Z(X_i, V_i) ≤ q^n` when every one-step integral is at most `q`, used for
(11.24) [uvg:eq:scalarfraction].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The transition operator `P_g` of (11.11) [lg:eq:transition]:
`(P_g f)(X) = 𝔼 f(X')` over one fresh GUE block. -/
def transOp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (g E : ℝ) {W : ℕ}
    (f : State W → G) (X : State W) : G :=
  ∫ ω, f (stepState g E X (gueBlock W 1 ω 0)) ∂(μ W 1)

/-- `P_g` of (11.11) [lg:eq:transition] on nonnegative functions. -/
def transOpL (g E : ℝ) {W : ℕ} (f : State W → ℝ≥0∞) (X : State W) : ℝ≥0∞ :=
  ∫⁻ ω, f (stepState g E X (gueBlock W 1 ω 0)) ∂(μ W 1)

/-- The conditional mean `P_g c` of the increment (Section 11.2 [sec:uniform-large-g]). -/
def incMean (g E : ℝ) {W : ℕ} (X : State W) : ℝ :=
  ∫ ω, stepInc g E X (gueBlock W 1 ω 0) ∂(μ W 1)

/-! ### Helpers: the blocks of a sample, the chain along them, and one appended block -/

/-- The blocks of a sample of `n` blocks as a sequence, padded by `0`. -/
private def trBlocks {W : ℕ} (n : ℕ) (ω : Ω W n) : ℕ → Matrix (Fin W) (Fin W) ℂ :=
  fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0

private lemma tr_measurable_gueBlock (W L : ℕ) (a : Fin L) :
    Measurable fun ω : Ω W L => gueBlock W L ω a := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma tr_measurable_trBlocks (W n : ℕ) : Measurable (trBlocks (W := W) n) := by
  refine measurable_pi_iff.mpr fun k => ?_
  unfold trBlocks
  by_cases h : k < n
  · simp only [h, dite_true]
    exact tr_measurable_gueBlock W n ⟨k, h⟩
  · simp only [h, dite_false]
    exact measurable_const

private lemma tr_measurable_chain (g E : ℝ) {W : ℕ} (X₀ : State W) (n : ℕ) (i : ℕ) :
    Measurable fun ω : Ω W n => chainState g E X₀ (trBlocks n ω) i := by
  induction i with
  | zero => exact measurable_const
  | succ i ih =>
    have hb : Measurable fun ω : Ω W n => trBlocks n ω i :=
      (measurable_pi_apply i).comp (tr_measurable_trBlocks W n)
    have h := (measurable_stepState g E W).comp (ih.prodMk hb)
    exact h

private lemma tr_chain_congr (g E : ℝ) {W : ℕ} (X₀ : State W)
    {V V' : ℕ → Matrix (Fin W) (Fin W) ℂ} {i : ℕ} (h : ∀ k < i, V k = V' k) :
    chainState g E X₀ V i = chainState g E X₀ V' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change stepState g E (chainState g E X₀ V i) (V i) =
      stepState g E (chainState g E X₀ V' i) (V' i)
    rw [ih fun k hk => h k (Nat.lt_succ_of_lt hk), h i (Nat.lt_succ_self i)]

private lemma tr_isState_chain (g E : ℝ) {W : ℕ} {X₀ : State W} (hX₀ : IsState X₀) (n : ℕ)
    (ω : Ω W n) (i : ℕ) : IsState (chainState g E X₀ (trBlocks n ω) i) := by
  induction i with
  | zero => exact hX₀
  | succ i ih =>
    refine isState_stepState g E ih ?_
    unfold trBlocks
    split_ifs
    · exact gueBlock_isHermitian W n ω _
    · exact Matrix.isHermitian_zero

private lemma tr_trBlocks_snoc_lt {W n : ℕ} (ω : Ω W n) (ω' : Ω W 1) {k : ℕ} (hk : k < n) :
    trBlocks (n + 1) (blockSnoc ω ω') k = trBlocks n ω k := by
  have hk' : k < n + 1 := Nat.lt_succ_of_lt hk
  simp only [trBlocks, hk', hk, dite_true]
  ext α β
  simp [gueBlock, blockSnoc, hk]

private lemma tr_trBlocks_snoc_last {W n : ℕ} (ω : Ω W n) (ω' : Ω W 1) :
    trBlocks (n + 1) (blockSnoc ω ω') n = gueBlock W 1 ω' 0 := by
  have hn : n < n + 1 := Nat.lt_succ_self n
  simp only [trBlocks, hn, dite_true]
  exact gueBlock_blockSnoc_last ω ω'

private lemma tr_chain_snoc_le (g E : ℝ) {W n : ℕ} (X₀ : State W) (ω : Ω W n) (ω' : Ω W 1)
    {i : ℕ} (hi : i ≤ n) :
    chainState g E X₀ (trBlocks (n + 1) (blockSnoc ω ω')) i = chainState g E X₀ (trBlocks n ω) i :=
  tr_chain_congr g E X₀ fun _ hk => tr_trBlocks_snoc_lt ω ω' (lt_of_lt_of_le hk hi)

private lemma tr_chain_snoc_succ (g E : ℝ) {W n : ℕ} (X₀ : State W) (ω : Ω W n) (ω' : Ω W 1) :
    chainState g E X₀ (trBlocks (n + 1) (blockSnoc ω ω')) (n + 1) =
      stepState g E (chainState g E X₀ (trBlocks n ω) n) (gueBlock W 1 ω' 0) := by
  change stepState g E (chainState g E X₀ (trBlocks (n + 1) (blockSnoc ω ω')) n)
    (trBlocks (n + 1) (blockSnoc ω ω') n) = _
  rw [tr_chain_snoc_le g E X₀ ω ω' le_rfl, tr_trBlocks_snoc_last]

private lemma tr_measurable_step (g E : ℝ) {W : ℕ} {f : State W → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun p : State W × Ω W 1 => f (stepState g E p.1 (gueBlock W 1 p.2 0)) := by
  have hb : Measurable fun p : State W × Ω W 1 => gueBlock W 1 p.2 0 :=
    (tr_measurable_gueBlock W 1 0).comp measurable_snd
  have h := (measurable_stepState g E W).comp (measurable_fst.prodMk hb)
  exact hf.comp h

private lemma tr_measurable_slice (g E : ℝ) {W : ℕ} {f : State W → ℝ≥0∞} (hf : Measurable f)
    (X : State W) : Measurable fun ω : Ω W 1 => f (stepState g E X (gueBlock W 1 ω 0)) := by
  have hpair : Measurable fun ω : Ω W 1 => (X, ω) := measurable_prodMk_left
  have h := (tr_measurable_step g E hf).comp hpair
  exact h

/-- (11.11) [lg:eq:transition] in integrated form: for a measurable function `G` of the first
`n` blocks, `𝔼[G f(X_{n+1})] = 𝔼[G (P_g f)(X_n)]`. -/
theorem lintegral_mul_chainState_succ (g E : ℝ) {W n : ℕ} (X₀ : State W)
    {G : Ω W n → ℝ≥0∞} (hG : Measurable G) {f : State W → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, G (windowSample Fin.castSucc ω) *
        f (chainState g E X₀ (fun k => if h : k < n + 1 then gueBlock W (n + 1) ω ⟨k, h⟩ else 0)
          (n + 1)) ∂(μ W (n + 1)) =
      ∫⁻ ω, G ω * transOpL g E f
        (chainState g E X₀ (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) n)
          ∂(μ W n) := by
  have hws : Measurable (windowSample (W := W) (Fin.castSucc : Fin n → Fin (n + 1))) :=
    (measurePreserving_windowSample W (n + 1) n (Fin.castSucc_injective n)).measurable
  have hF : Measurable fun ω : Ω W (n + 1) => G (windowSample Fin.castSucc ω) *
      f (chainState g E X₀ (trBlocks (n + 1) ω) (n + 1)) :=
    (hG.comp hws).mul (hf.comp (tr_measurable_chain g E X₀ (n + 1) (n + 1)))
  change ∫⁻ ω, G (windowSample Fin.castSucc ω) *
      f (chainState g E X₀ (trBlocks (n + 1) ω) (n + 1)) ∂(μ W (n + 1)) =
    ∫⁻ ω, G ω * transOpL g E f (chainState g E X₀ (trBlocks n ω) n) ∂(μ W n)
  rw [lintegral_blockSnoc W n hF]
  refine lintegral_congr fun ω => ?_
  have hpt : ∀ ω' : Ω W 1, G (windowSample Fin.castSucc (blockSnoc ω ω')) *
      f (chainState g E X₀ (trBlocks (n + 1) (blockSnoc ω ω')) (n + 1)) =
      G ω * f (stepState g E (chainState g E X₀ (trBlocks n ω) n) (gueBlock W 1 ω' 0)) := by
    intro ω'
    rw [windowSample_blockSnoc, tr_chain_snoc_succ]
  simp only [hpt]
  have hm : Measurable fun ω' : Ω W 1 =>
      f (stepState g E (chainState g E X₀ (trBlocks n ω) n) (gueBlock W 1 ω' 0)) :=
    tr_measurable_slice g E hf _
  rw [lintegral_const_mul _ hm]
  rfl

/-- The adapted product bound: if `𝔼 Z(X, V) ≤ q` over a fresh block for every state `X`,
then `𝔼 ∏_{i<n} Z(X_i, V_i) ≤ q^n` (proof of (11.24) [uvg:eq:scalarfraction]). -/
theorem lintegral_prod_chainState_le (g E : ℝ) {W : ℕ}
    (Z : State W → Matrix (Fin W) (Fin W) ℂ → ℝ≥0∞)
    (hZ : Measurable (fun p : State W × Matrix (Fin W) (Fin W) ℂ => Z p.1 p.2)) {q : ℝ≥0∞}
    (hq : ∀ X : State W, IsState X → ∫⁻ ω, Z X (gueBlock W 1 ω 0) ∂(μ W 1) ≤ q)
    {X₀ : State W} (hX₀ : IsState X₀) (n : ℕ) :
    ∫⁻ ω, ∏ i ∈ Finset.range n,
        Z (chainState g E X₀ (fun k => if h : k < n then gueBlock W n ω ⟨k, h⟩ else 0) i)
          (if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) ∂(μ W n) ≤ q ^ n := by
  have hmeas : ∀ m : ℕ, Measurable fun ω : Ω W m => ∏ i ∈ Finset.range m,
      Z (chainState g E X₀ (trBlocks m ω) i) (trBlocks m ω i) := fun m =>
    Finset.measurable_prod _ fun i _ => hZ.comp
      ((tr_measurable_chain g E X₀ m i).prodMk
        ((measurable_pi_apply i).comp (tr_measurable_trBlocks W m)))
  change ∫⁻ ω, ∏ i ∈ Finset.range n,
    Z (chainState g E X₀ (trBlocks n ω) i) (trBlocks n ω i) ∂(μ W n) ≤ q ^ n
  induction n with
  | zero => simp
  | succ n ih =>
    have hpt : ∀ (ω : Ω W n) (ω' : Ω W 1), ∏ i ∈ Finset.range (n + 1),
        Z (chainState g E X₀ (trBlocks (n + 1) (blockSnoc ω ω')) i)
          (trBlocks (n + 1) (blockSnoc ω ω') i) =
        (∏ i ∈ Finset.range n, Z (chainState g E X₀ (trBlocks n ω) i) (trBlocks n ω i)) *
          Z (chainState g E X₀ (trBlocks n ω) n) (gueBlock W 1 ω' 0) := by
      intro ω ω'
      rw [Finset.prod_range_succ]
      congr 1
      · refine Finset.prod_congr rfl fun i hi => ?_
        have hin : i < n := Finset.mem_range.mp hi
        rw [tr_chain_snoc_le g E X₀ ω ω' hin.le, tr_trBlocks_snoc_lt ω ω' hin]
      · rw [tr_chain_snoc_le g E X₀ ω ω' le_rfl, tr_trBlocks_snoc_last]
    rw [lintegral_blockSnoc W n (hmeas (n + 1))]
    simp only [hpt]
    calc ∫⁻ ω, ∫⁻ ω', (∏ i ∈ Finset.range n,
            Z (chainState g E X₀ (trBlocks n ω) i) (trBlocks n ω i)) *
          Z (chainState g E X₀ (trBlocks n ω) n) (gueBlock W 1 ω' 0) ∂(μ W 1) ∂(μ W n)
        = ∫⁻ ω, (∏ i ∈ Finset.range n,
            Z (chainState g E X₀ (trBlocks n ω) i) (trBlocks n ω i)) *
          ∫⁻ ω', Z (chainState g E X₀ (trBlocks n ω) n) (gueBlock W 1 ω' 0) ∂(μ W 1)
            ∂(μ W n) := by
          refine lintegral_congr fun ω => ?_
          exact lintegral_const_mul _
            (hZ.comp (measurable_const.prodMk (tr_measurable_gueBlock W 1 0)))
      _ ≤ ∫⁻ ω, (∏ i ∈ Finset.range n,
            Z (chainState g E X₀ (trBlocks n ω) i) (trBlocks n ω i)) * q ∂(μ W n) := by
          refine lintegral_mono fun ω => ?_
          exact mul_le_mul_right (hq _ (tr_isState_chain g E hX₀ n ω n)) _
      _ = (∫⁻ ω, ∏ i ∈ Finset.range n,
            Z (chainState g E X₀ (trBlocks n ω) i) (trBlocks n ω i) ∂(μ W n)) * q :=
          lintegral_mul_const _ (hmeas n)
      _ ≤ q ^ n * q := mul_le_mul_left ih _
      _ = q ^ (n + 1) := (pow_succ q n).symm

end LSBA
