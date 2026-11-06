import LSBA.Upper.OperatorInvariance
import LSBA.Transfer.CircleMeasure
import LSBA.Analysis.SplitIterate

/-!
# From angular contraction to power decay

Lemma 8.10 [up:lem:operator-iteration]: the operator form of Lemma 8.9 [up:lem:good-bad]
(`GoodBadSplitAt`, `GoodBadSplit`: (8.28) [eq:c-good-bad-operators], (8.29) [up:eq:GB-bounds]) and
the angular contraction (8.30) [up:eq:P-contraction] (`AngContractionAt`) give
`‖P_{1/2}^k 1‖_∞ ≤ (1 + 4K) ρ^k` ((8.31) [cc:eq:firstgood], (8.32) [cc:eq:pointwise]) and
hence (8.21) [up:eq:power-input].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- (8.28) [eq:c-good-bad-operators] and (8.29) [up:eq:GB-bounds] at one point, operator form:
`P_{1/2} = G_{1/2} + B_{1/2}` with `B_{1/2}` linear on bounded measurable functions,
`‖B_{1/2} h‖_∞ ≤ ½ ‖h‖_∞` and `‖G_{1/2} h‖_∞ ≤ K sup_U ‖h(U, ·)‖_{L⁴(𝒞_U, m_U)}`. -/
def GoodBadSplitAt (W : ℕ) (g E : ℝ) (q : ℕ) (K : ℝ) : Prop :=
  ∃ Bop : (IsoFlag W → ℝ) → IsoFlag W → ℝ,
    (∀ h, IsBddMeas h → IsBddMeas (Bop h)) ∧
    (∀ h h', IsBddMeas h → IsBddMeas h' → Bop (h + h') = Bop h + Bop h') ∧
    (∀ (r : ℝ) h, IsBddMeas h → Bop (r • h) = r • Bop h) ∧
    (∀ h M, IsBddMeas h → (∀ x, |h x| ≤ M) → ∀ x, |Bop h x| ≤ M / 2) ∧
    (∀ h M, IsBddMeas h → 0 ≤ M → AngL4Le h M → ∀ x, |halfOp W g E q h x - Bop h x| ≤ K * M)

/-- Lemma 8.9 [up:lem:good-bad], operator form: for fixed `B, E₀ > 0` and `q ≥ 1000` divisible
by `1000` there are `C, W₀` such that (8.29) [up:eq:GB-bounds] holds with `W^C` for all
`W ≥ W₀`, `W^{-B} ≤ g ≤ W^B`, `|E| ≤ E₀`. -/
def GoodBadSplit : Prop :=
  ∀ B E₀ : ℝ, 0 < B → 0 < E₀ → ∀ q : ℕ, 1000 ≤ q → 1000 ∣ q →
    ∃ C : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g E : ℝ, (W : ℝ) ^ (-B) ≤ g → g ≤ (W : ℝ) ^ B →
      |E| ≤ E₀ → GoodBadSplitAt W g E q ((W : ℝ) ^ C)

/-- (8.30) [up:eq:P-contraction] at one point, with factor `ρ`, for bounded nonnegative
measurable `h` satisfying (8.25) [up:eq:invariant-function]. -/
def AngContractionAt (W : ℕ) (g E : ℝ) (q : ℕ) (ρ : ℝ) : Prop :=
  ∀ h : IsoFlag W → ℝ, IsBddMeas h → 0 ≤ h → IsSimulInvariant h →
    ∀ M : ℝ, 0 ≤ M → AngL4Le h M → AngL4Le (halfOp W g E q h) (ρ * M)

/-- Lemma 8.10 [up:lem:operator-iteration] at one point: (8.29) [up:eq:GB-bounds] and (8.30)
[up:eq:P-contraction] with
`ρ = 1 - c/𝔟` give `‖P_{1/2}^k 1‖_∞ ≤ (1 + 4K) ρ^k` ((8.31) [cc:eq:firstgood],
(8.32) [cc:eq:pointwise]). -/
theorem iterate_halfOp_one_le {W : ℕ} {g E : ℝ} {q : ℕ} {K b c : ℝ} (hK : 0 ≤ K) (hb : 1 ≤ b)
    (hc0 : 0 < c) (hc : c ≤ 1 / 4) (hsplit : GoodBadSplitAt W g E q K)
    (hcon : AngContractionAt W g E q (1 - c / b)) (k : ℕ) (x : IsoFlag W) :
    |(halfOp W g E q)^[k] (fun _ => 1) x| ≤ (1 + 4 * K) * (1 - c / b) ^ k := by
  obtain ⟨Bop, -, -, -, hB, hG⟩ := hsplit
  have hbdd : ∀ r : ℕ, IsBddMeas ((halfOp W g E q)^[r] fun _ => (1 : ℝ)) := by
    intro r
    induction r with
    | zero => exact ⟨measurable_const, 1, fun x => by simp⟩
    | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact halfOp_isBddMeas g E q ih
  have hnn : ∀ r : ℕ, 0 ≤ (halfOp W g E q)^[r] fun _ => (1 : ℝ) := by
    intro r
    induction r with
    | zero => exact fun x => zero_le_one
    | succ r ih =>
      rw [Function.iterate_succ_apply']
      intro x
      exact integral_nonneg fun ω => mul_nonneg (Real.exp_pos _).le (ih _)
  have hone : AngL4Le (fun _ : IsoFlag W => (1 : ℝ)) 1 := by
    intro x
    have := isProbabilityMeasure_circleMeasure x
    simp
  have hρ : 3 / 4 ≤ 1 - c / b := by
    have : c / b ≤ c := div_le_self hc0.le hb
    linarith
  have hang : ∀ r : ℕ, AngL4Le ((halfOp W g E q)^[r] fun _ => (1 : ℝ)) ((1 - c / b) ^ r) := by
    intro r
    induction r with
    | zero =>
      rw [pow_zero]
      exact hone
    | succ r ih =>
      rw [Function.iterate_succ_apply', pow_succ']
      exact hcon _ (hbdd r) (hnn r)
        (iterate_halfOp_one_isSimulInvariant W g E q r) _ (pow_nonneg (by linarith) r) ih
  exact iterate_one_le_of_split (good := @IsBddMeas W) (angLe := @AngL4Le W) (halfOp W g E q) Bop
    hK hρ hbdd hB hG hang k x

/-- Lemma 8.10 [up:lem:operator-iteration]: under Lemma 8.9 [up:lem:good-bad] (operator form) and
(8.30)
[up:eq:P-contraction] with `0 < c ≤ 1/4`, (8.21) [up:eq:power-input] holds with `C, W₀`
depending only on `B, E₀, q, c`. -/
theorem powerDecay_of_contraction (hsplit : GoodBadSplit) {B E₀ : ℝ} (hB : 0 < B)
    (hE₀ : 0 < E₀) {q : ℕ} (hq : 1000 ≤ q) (hq' : 1000 ∣ q) {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ 1 / 4) :
    ∃ C : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g E b : ℝ, (W : ℝ) ^ (-B) ≤ g → g ≤ (W : ℝ) ^ B →
      |E| ≤ E₀ → 1 ≤ b → AngContractionAt W g E q (1 - c / b) → PowerDecayAt W g E q b c C := by
  obtain ⟨C₁, W₀', hW⟩ := hsplit B E₀ hB hE₀ q hq hq'
  refine ⟨max 5 C₁, max W₀' 1, ?_⟩
  intro W hW0 g E b hg1 hg2 hE hb hcon k x
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW0
  have hWpos : (0 : ℝ) < W := by linarith
  have hsp := hW W (le_trans (le_max_left _ _) hW0) g E hg1 hg2 hE
  have hK : 0 ≤ (W : ℝ) ^ C₁ := (Real.rpow_pos_of_pos hWpos _).le
  have h1 := iterate_halfOp_one_le hK hb hc0 hc hsp hcon k x
  have hb0 : 0 < b := by linarith
  have hcb : c / b ≤ c := div_le_self hc0.le hb
  have hρ0 : 0 ≤ 1 - c / b := by linarith
  have h2 : (1 - c / b) ^ k ≤ Real.exp (-c * k / b) := by
    calc (1 - c / b) ^ k ≤ (Real.exp (-(c / b))) ^ k :=
          pow_le_pow_left₀ hρ0 (by linarith [Real.add_one_le_exp (-(c / b))]) k
      _ = Real.exp (-c * k / b) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have hC0 : (0 : ℝ) ≤ max 5 C₁ := le_trans (by norm_num) (le_max_left _ _)
  have hpow1 : (W : ℝ) ^ C₁ ≤ (W : ℝ) ^ (max 5 C₁) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (le_max_right _ _)
  have hpow2 : (1 : ℝ) ≤ (W : ℝ) ^ (max 5 C₁) := Real.one_le_rpow hW1 hC0
  have h3 : 1 + 4 * (W : ℝ) ^ C₁ ≤ max 5 C₁ * (W : ℝ) ^ (max 5 C₁) := by
    have := mul_le_mul_of_nonneg_right (le_max_left (5 : ℝ) C₁)
      (by linarith : (0 : ℝ) ≤ (W : ℝ) ^ (max 5 C₁))
    linarith
  have hpos : 0 ≤ max 5 C₁ * (W : ℝ) ^ (max 5 C₁) := by positivity
  calc |(halfOp W g E q)^[k] (fun _ => 1) x| ≤ (1 + 4 * (W : ℝ) ^ C₁) * (1 - c / b) ^ k := h1
    _ ≤ max 5 C₁ * (W : ℝ) ^ (max 5 C₁) * Real.exp (-c * k / b) :=
        mul_le_mul h3 h2 (pow_nonneg hρ0 k) hpos

end LSBA
