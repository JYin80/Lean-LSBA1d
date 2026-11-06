import LSBA.Upper.FracMoment
import LSBA.Upper.ConversionCycle
import LSBA.Upper.NearZeroTransfer

/-!
# From paths to cycles

The passage from the fixed-energy bound (8.2) [up:eq:fmr-pointwise] on the Dirichlet path of
`L - 1` blocks to the same bound on the cycle of `L` blocks, at half the exponent and half the
rate, by the Schur identity (E.15) [eq:c-cycle-Schur], Cauchy–Schwarz and (8.7) [eq:c-apriori]:
the step (E.16) [eq:c-cycle] of Appendix E.2 [app:finite-volume-criterion] and the step of the
proof of Theorem 3.1 [thm:strong-upper] at `p = 1/2`. Here `g = 0` is allowed.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- From paths to cycles: for fixed `C₀ ≥ 1`, `p ∈ (0, 1)`, `C ≥ 0`, `c > 0` there is a width
threshold, independent of `L, g, 𝔟, J`, such that for `L ≥ 3`, `0 ≤ g ≤ W^{C₀}` and `𝔟 ≥ 1`,
(8.2) [up:eq:fmr-pointwise] at exponent `p` on the path of `L - 1` blocks gives (8.2)
[up:eq:fmr-pointwise] at exponent
`p/2` on the cycle of `L` blocks, with `C′ = ((C₀ + 2) p + C)/2 + 1` and rate `c/2`. -/
theorem frac_cycle_of_path {C₀ p C c : ℝ} (hC₀ : 1 ≤ C₀) (hp0 : 0 < p) (hp1 : p < 1) (hC : 0 ≤ C)
    (hc : 0 < c) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g b : ℝ, 0 ≤ g → g ≤ (W : ℝ) ^ C₀ → 1 ≤ b →
      ∀ J : Set ℝ, FracPath W (L - 1) g J p C c b →
        FracCycle W L g J (p / 2) (((C₀ + 2) * p + C) / 2 + 1) (c / 2) b := by
  have hB : 0 < C₀ := by linarith
  have hap : ∀ r : ℝ, r < 1 → 0 < aprioriConst r := fun r hr => by
    unfold aprioriConst
    have : 0 < 1 - r := by linarith
    positivity
  have hCp := hap p hp1
  have hCq := hap (p / 2) (by linarith)
  refine ⟨max 1 (max ⌈2 * Real.sqrt (aprioriConst p) * Real.exp (c / 2)⌉₊
    ⌈aprioriConst (p / 2)⌉₊), ?_⟩
  intro W hW L hL g b hg0 hgB hb1 J hF E hE x y
  have hW1' : 1 ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1'
  have hW0 : (0 : ℝ) < W := by linarith
  have hWa : 2 * Real.sqrt (aprioriConst p) * Real.exp (c / 2) ≤ (W : ℝ) :=
    (Nat.le_ceil _).trans (by
      exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW)
  have hWb : aprioriConst (p / 2) ≤ (W : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW)
  have hb0 : 0 < b := by linarith
  have hmB : max 1 g ≤ (W : ℝ) ^ C₀ := max_le (Real.one_le_rpow hW1 hB.le) hgB
  have hm0 : 0 ≤ max 1 g * (W : ℝ) ^ 2 :=
    mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (by positivity)
  have hX : ∀ r : ℝ, 0 ≤ r → (max 1 g * (W : ℝ) ^ 2) ^ r ≤ (W : ℝ) ^ ((C₀ + 2) * r) := by
    intro r hr
    have h1 : max 1 g * (W : ℝ) ^ 2 ≤ (W : ℝ) ^ (C₀ + 2) := by
      rw [Real.rpow_add hW0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_right hmB (by positivity)
    calc (max 1 g * (W : ℝ) ^ 2) ^ r ≤ ((W : ℝ) ^ (C₀ + 2)) ^ r := Real.rpow_le_rpow hm0 h1 hr
      _ = _ := (Real.rpow_mul hW0.le _ _).symm
  set C' : ℝ := ((C₀ + 2) * p + C) / 2 + 1 with hC'
  by_cases hxy : x = y
  · subst hxy
    have hd : cycDist x x = 0 := by simp [cycDist]
    simp only [hd, Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, mul_one]
    refine (Hmat_moment_le g (by positivity) (by linarith) E x x).trans
      (ENNReal.ofReal_le_ofReal ?_)
    calc aprioriConst (p / 2) * (max 1 g * (W : ℝ) ^ 2) ^ (p / 2)
        ≤ W * (W : ℝ) ^ ((C₀ + 2) * (p / 2)) :=
          mul_le_mul hWb (hX _ (by positivity)) (by positivity) hW0.le
      _ = (W : ℝ) ^ (1 + (C₀ + 2) * (p / 2)) := by rw [Real.rpow_add hW0, Real.rpow_one]
      _ ≤ (W : ℝ) ^ C' := Real.rpow_le_rpow_of_exponent_le hW1 (by rw [hC']; nlinarith)
  · have hκ : 0 ≤ c / (2 * b) := by positivity
    have hP : ∀ u v : Fin (L - 1),
        ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1) ω) 0 0) E) u v‖ₑ ^ p
            ∂(μ W (L - 1)) ≤
          ENNReal.ofReal ((W : ℝ) ^ C *
            Real.exp (-(2 * (c / (2 * b))) * |((u : ℕ) : ℝ) - (v : ℕ)|)) := by
      intro u v
      have e : -(2 * (c / (2 * b))) * |((u : ℕ) : ℝ) - (v : ℕ)| =
          -c * |((u : ℕ) : ℝ) - (v : ℕ)| / b := by
        field_simp
      rw [e]
      exact hF E hE u v
    refine (cycle_moment_of_path hp0 hp1 hg0 hL (by positivity) hκ hP hxy).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hs1 : Real.sqrt (aprioriConst p * (max 1 g * (W : ℝ) ^ 2) ^ p) ≤
        Real.sqrt (aprioriConst p) * (W : ℝ) ^ ((C₀ + 2) * p / 2) := by
      rw [Real.sqrt_mul hCp.le]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      rw [Real.sqrt_le_left (by positivity), ← Real.rpow_natCast ((W : ℝ) ^ _),
        ← Real.rpow_mul hW0.le]
      convert hX p hp0.le using 2
      push_cast
      ring
    have hs2 : Real.sqrt ((W : ℝ) ^ C) = (W : ℝ) ^ (C / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hW0.le]
      congr 1
      ring
    have hex : Real.exp (c / (2 * b)) ≤ Real.exp (c / 2) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_left hc.le (by norm_num)
      linarith
    have hed : -(c / (2 * b)) * (cycDist x y : ℝ) = -(c / 2) * cycDist x y / b := by
      field_simp
    rw [hs2, hed]
    have hW' : (W : ℝ) ^ C' = W * ((W : ℝ) ^ ((C₀ + 2) * p / 2) * (W : ℝ) ^ (C / 2)) := by
      rw [← Real.rpow_add hW0, hC', show ((C₀ + 2) * p + C) / 2 + 1 =
        1 + ((C₀ + 2) * p / 2 + C / 2) by ring, Real.rpow_add hW0, Real.rpow_one]
    rw [hW']
    have hp1' : (0 : ℝ) ≤ (W : ℝ) ^ ((C₀ + 2) * p / 2) := by positivity
    have hp2' : (0 : ℝ) ≤ (W : ℝ) ^ (C / 2) := by positivity
    calc 2 * Real.sqrt (aprioriConst p * (max 1 g * (W : ℝ) ^ 2) ^ p) * (W : ℝ) ^ (C / 2) *
          Real.exp (c / (2 * b)) * Real.exp (-(c / 2) * cycDist x y / b)
        ≤ 2 * (Real.sqrt (aprioriConst p) * (W : ℝ) ^ ((C₀ + 2) * p / 2)) * (W : ℝ) ^ (C / 2) *
          Real.exp (c / 2) * Real.exp (-(c / 2) * cycDist x y / b) := by gcongr
      _ = (2 * Real.sqrt (aprioriConst p) * Real.exp (c / 2)) *
            ((W : ℝ) ^ ((C₀ + 2) * p / 2) * (W : ℝ) ^ (C / 2)) *
            Real.exp (-(c / 2) * cycDist x y / b) := by ring
      _ ≤ _ := by gcongr

end LSBA
