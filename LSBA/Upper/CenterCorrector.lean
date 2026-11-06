import LSBA.Upper.CorrectorDrift
import LSBA.Upper.CenterStability

/-!
# A bounded corrector and positive drift

Lemma 11.9 [lg:lem:centerQ]: for `0 < ε < B_g`, `D > 0`, `B_1 > 1 + 2B_g` and
`0 < η < min(ε, 1/4)` there are an order `R`, a finite index set, coefficients `q(g, E)`, an
energy window, `C_*`, `C` and `W_0` such that, for `W ≥ W_0`, `W^ε ≤ g < W^{B_g}` and `|E|` in the
window, the corrector `Q_g = Re Σ_k q_k F_k` satisfies (11.28) [lg:eq:Q-regularity] (size and
Lipschitz bounds on states), the corrected drift bound of (11.61) [lg:eq:corrected-drift] holds on
the good set with exponent `η/2`, and along the chain from any state the good set is reached at
every time `n_* ≤ n ≤ N` (`n_* = ⌈C_* g² log W⌉` of (11.25) [lg:eq:initial-time],
`N ≤ W^{B_1}`) with probability at least `1 − W^{−D}`.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Lemma 11.9 [lg:lem:centerQ], with (11.28) [lg:eq:Q-regularity] in Lipschitz form and (11.61)
[lg:eq:corrected-drift] as a deterministic bound on the good set together with the event (11.44)
[lg:eq:burnevent]. -/
theorem center_corrector {ε Bg : ℝ} (hε : 0 < ε) (hεB : ε < Bg) {D B₁ : ℝ} (hD : 0 < D)
    (hB₁ : 1 + 2 * Bg < B₁) {η : ℝ} (hη0 : 0 < η) (hη : η < min ε (1 / 4)) :
    ∃ R : ℕ, ∃ Ks : Finset NzInt, ∃ q : ℝ → ℝ → NzInt → ℂ, ∃ E₁ : ℝ, 0 < E₁ ∧
      ∃ Cs CQ : ℝ, 0 < Cs ∧ 0 < CQ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        ∀ g : ℝ, (W : ℝ) ^ ε ≤ g → g < (W : ℝ) ^ Bg → ∀ E : ℝ, |E| ≤ E₁ →
          ∑ k ∈ Ks, ‖q g E k‖ ≤ CQ / g ^ 2 ∧
          (∀ X : State W, IsState X → |corrQ g E R Ks (q g E) X| ≤ CQ / g ^ 2) ∧
          (∀ X Y : State W, IsState X → IsState Y →
            |corrQ g E R Ks (q g E) X - corrQ g E R Ks (q g E) Y| ≤
              CQ / g ^ 2 * (‖X.1 - Y.1‖ + ‖X.2 - Y.2‖)) ∧
          (∀ X : State W, IsState X → corrGood g E R Ks (η / 2) X →
            |incMean g E X - (transOp g E (corrQ g E R Ks (q g E)) X -
                corrQ g E R Ks (q g E) X) - normalH E ^ 2 / (2 * W * g ^ 2)| ≤
              normalH E ^ 2 / (6 * W * g ^ 2)) ∧
          ∀ X₀ : State W, IsState X₀ → ∀ N : ℕ, (N : ℝ) ≤ (W : ℝ) ^ B₁ →
            μ W N {ω | ∃ n : ℕ, ⌈Cs * g ^ 2 * Real.log W⌉₊ ≤ n ∧ n ≤ N ∧
                ¬ corrGood g E R Ks (η / 2) (chainState g E X₀
                  (fun i => if h : i < N then gueBlock W N ω ⟨i, h⟩ else 0) n)} ≤
              ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  set R : ℕ := ⌊1 / (2 * ε)⌋₊ + 2 with hR
  have hR2 : 2 ≤ R := Nat.le_add_left 2 _
  have hεR : 1 < 2 * ε * R := by
    have h2ε : 0 < 2 * ε := by positivity
    have h1 : 1 / (2 * ε) < (⌊1 / (2 * ε)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : 1 < ((⌊1 / (2 * ε)⌋₊ : ℝ) + 1) * (2 * ε) := (div_lt_iff₀ h2ε).mp h1
    have hRr : (R : ℝ) = (⌊1 / (2 * ε)⌋₊ : ℝ) + 2 := by rw [hR]; push_cast; ring
    rw [hRr]
    nlinarith
  obtain ⟨Ks, q, Ea, hEa, Ca, hCa, hdr⟩ := corrector_drift hε R hεR
  obtain ⟨Wa, hWa⟩ := hdr η hη0 hη
  obtain ⟨Eb, hEb, K, hK, hQb⟩ := corrQ_bounds R Ks
  have hB₁0 : 0 < B₁ := by linarith
  obtain ⟨Ec, hEc, Cs, hCs, Wc, hst⟩ :=
    corrObs_stability hε R hR2 hεR Ks D (η / 2) B₁ hD (by linarith) hB₁0
  refine ⟨R, Ks, q, min Ea (min Eb Ec), lt_min hEa (lt_min hEb hEc), Cs, Ca * max 1 K, hCs,
    mul_pos hCa (lt_max_of_lt_left one_pos), max (max Wa Wc) 1, ?_⟩
  intro W hW g hg hgB E hE
  have hWa' : Wa ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hWc' : Wc ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hEa' : |E| ≤ Ea := hE.trans (min_le_left _ _)
  have hEb' : |E| ≤ Eb := hE.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hEc' : |E| ≤ Ec := hE.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hg1 : 1 ≤ g := (Real.one_le_rpow hWr hε.le).trans hg
  have hg0 : 0 < g ^ 2 := by positivity
  obtain ⟨hsum, hdrift⟩ := hWa W hWa' g hg E hEa'
  have hsum' : ∑ k ∈ Ks, ‖q g E k‖ ≤ Ca * max 1 K / g ^ 2 :=
    hsum.trans (by gcongr; exact le_mul_of_one_le_right hCa.le (le_max_left _ _))
  have hKs : K * ∑ k ∈ Ks, ‖q g E k‖ ≤ Ca * max 1 K / g ^ 2 :=
    calc K * ∑ k ∈ Ks, ‖q g E k‖ ≤ K * (Ca / g ^ 2) := by gcongr
      _ = Ca * K / g ^ 2 := by ring
      _ ≤ Ca * max 1 K / g ^ 2 := by gcongr; exact le_max_right _ _
  refine ⟨hsum', fun X hX => ?_, fun X Y hX hY => ?_, fun X hX hgood => hdrift X hX hgood,
    fun X₀ hX₀ N hN => ?_⟩
  · exact (hQb W hW1 g hg1 E hEb' (q g E) X X hX hX).1.trans hKs
  · refine (hQb W hW1 g hg1 E hEb' (q g E) X Y hX hY).2.trans ?_
    exact mul_le_mul_of_nonneg_right hKs (by positivity)
  · refine le_trans (measure_mono ?_) (hst W hWc' g hg E hEc' X₀ hX₀ N (hN.trans ?_))
    · rintro ω ⟨n, hn1, hn2, hbad⟩
      unfold corrGood at hbad
      push Not at hbad
      obtain ⟨k, hk, hk'⟩ := hbad
      refine ⟨k, hk, n, hn1, hn2, ?_⟩
      by_cases h : ‖obsEval g (chainState g E X₀
          (fun i => if h : i < N then gueBlock W N ω ⟨i, h⟩ else 0) n) (corrObsM E R k) -
          center g E R k.1‖ ≤ (W : ℝ) ^ (η / 2 - 1)
      · exact Or.inr (hk' h)
      · exact Or.inl (not_le.mp h)
    · exact le_rfl

end LSBA
