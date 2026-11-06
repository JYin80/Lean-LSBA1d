import LSBA.Upper.CorrelatorAverage
import LSBA.Volume.LocalComparison
import LSBA.Model.Cycle
import LSBA.Upper.ConversionApriori

/-!
# Decay of block correlators

(E.1) [up:eq:correlator-intro] from a block resolvent decay of the form (E.16) [eq:c-cycle] and
the spectral averaging of [ASFH, Appendix A, proof of Theorem A.1, (A.10)–(A.12)]
(proof of Lemma 8.1(i) [uva:thm:upper-audit]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- (E.1) [up:eq:correlator-intro] from a block resolvent decay of the form (E.16)
[eq:c-cycle] and the spectral averaging of [ASFH, Appendix A, proof of Theorem A.1, (A.10)–(A.12)]
(proof of Lemma 8.1(i) [uva:thm:upper-audit]). -/
theorem blockCorr_decay {u B E₀ Cg Pg cg b : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hB : 0 < B)
    (hE₀ : 0 < E₀) (hCg : 0 ≤ Cg) (hcg : 0 < cg) (hb : 0 < b) {W L : ℕ} (hW : 1 ≤ W)
    (hL : 3 ≤ L) {g : ℝ} (hg0 : 0 ≤ g) (hgB : g ≤ (W : ℝ) ^ B) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJE : J ⊆ Set.Icc (-E₀) E₀)
    (hG : ∀ E ∈ J, ∀ a c : Fin L, a ≠ c →
      ∫⁻ ω, ‖blockOf (resolventMat (Hmat g W L ω) E) a c‖ₑ ^ u ∂(μ W L) ≤
        ENNReal.ofReal (Cg * (W : ℝ) ^ Pg * Real.exp (-cg * cycDist a c / b)))
    {a c : Fin L} (hac : a ≠ c) :
    ∫ ω, blockCorr (Hmat g W L ω) J a c ∂(μ W L) ≤
      (4 * absMomentConst u * E₀ * Cg / Real.sqrt (2 * π)) ^ (1 / (4 - u)) *
        (W : ℝ) ^ (2 + ((1 - u) / 2 + B * (1 - u) + Pg) / (4 - u)) *
          Real.exp (-(cg / (4 - u)) * cycDist a c / b) := by
  -- an entry of a matrix is bounded by its operator norm
  have hentry : ∀ (M : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W), ‖M i j‖ ≤ ‖M‖ := by
    intro M i j
    have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
    have hn : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
    rw [hn, mul_one] at h
    refine le_trans ?_ h
    have := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin W) ℂ).symm
      (M.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
    convert this using 2
    simp
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hu4 : 0 < 4 - u := by linarith
  have hp0 : 0 < 1 / (4 - u) := by positivity
  have hCu : 0 ≤ absMomentConst u := by
    unfold absMomentConst
    have : 0 < Real.Gamma ((u + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
    positivity
  have hK0 : 0 ≤ 4 * absMomentConst u * E₀ * Cg / Real.sqrt (2 * π) := by positivity
  have hm0 : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left 1 g)
  have hmW : max 1 g ≤ (W : ℝ) ^ B :=
    max_le (Real.one_le_rpow hW1 hB.le) hgB
  have hexp0 : 0 ≤ Real.exp (-cg * cycDist a c / b) := (Real.exp_pos _).le
  have hJb : Bornology.IsBounded J := (Metric.isBounded_Icc (-E₀) E₀).subset hJE
  -- the bound on `m^{1-u}`
  have hmu : (max 1 g) ^ (1 - u) ≤ (W : ℝ) ^ (B * (1 - u)) := by
    rw [Real.rpow_mul hW0.le]
    exact Real.rpow_le_rpow hm0.le hmW (by linarith)
  -- the bound on a single pair of coordinates
  have hpair : ∀ α β : Fin W,
      ∫ ω, eigCorr (Hmat g W L ω) J (a, α) (c, β) ∂(μ W L) ≤
        (4 * absMomentConst u * E₀ * Cg / Real.sqrt (2 * π)) ^ (1 / (4 - u)) *
          (W : ℝ) ^ (((1 - u) / 2 + B * (1 - u) + Pg) * (1 / (4 - u))) *
            Real.exp (-(cg / (4 - u)) * cycDist a c / b) := by
    intro α β
    have h1 := correlator_spectral_average hu0 hu1 hg0 hW hL hJ hJb (a, α) (c, β)
    have hin : ∫⁻ E in J, ∫⁻ ω, ‖resolventMat (Hmat g W L ω) E (a, α) (c, β)‖ₑ ^ u ∂(μ W L) ≤
        ENNReal.ofReal (Cg * (W : ℝ) ^ Pg * Real.exp (-cg * cycDist a c / b) * (2 * E₀)) := by
      calc ∫⁻ E in J, ∫⁻ ω, ‖resolventMat (Hmat g W L ω) E (a, α) (c, β)‖ₑ ^ u ∂(μ W L)
          ≤ ∫⁻ _ in J, ENNReal.ofReal
              (Cg * (W : ℝ) ^ Pg * Real.exp (-cg * cycDist a c / b)) := by
            refine setLIntegral_mono measurable_const fun E hE => ?_
            refine le_trans (lintegral_mono fun ω => ?_) (hG E hE a c hac)
            refine ENNReal.rpow_le_rpow ?_ hu0.le
            rw [enorm_le_iff_norm_le]
            exact hentry (blockOf (resolventMat (Hmat g W L ω) E) a c) α β
        _ = ENNReal.ofReal (Cg * (W : ℝ) ^ Pg * Real.exp (-cg * cycDist a c / b)) *
              volume J := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal (Cg * (W : ℝ) ^ Pg * Real.exp (-cg * cycDist a c / b)) *
              ENNReal.ofReal (2 * E₀) := by
            have hv : volume J ≤ ENNReal.ofReal (2 * E₀) := by
              refine (measure_mono hJE).trans ?_
              rw [Real.volume_Icc]
              exact le_of_eq (by congr 1; ring)
            gcongr
        _ = ENNReal.ofReal (Cg * (W : ℝ) ^ Pg * Real.exp (-cg * cycDist a c / b) * (2 * E₀)) :=
            (ENNReal.ofReal_mul (by positivity)).symm
    have hA0 : 0 ≤ 2 * (absMomentConst u * (W : ℝ) ^ (-u / 2) * (max 1 g) ^ (-u)) *
        (max 1 g * Real.sqrt (W / (2 * π))) := by positivity
    have h2 : ENNReal.ofReal (2 * (absMomentConst u * (W : ℝ) ^ (-u / 2) * (max 1 g) ^ (-u)) *
          (max 1 g * Real.sqrt (W / (2 * π)))) *
        ∫⁻ E in J, ∫⁻ ω, ‖resolventMat (Hmat g W L ω) E (a, α) (c, β)‖ₑ ^ u ∂(μ W L) ≤
        ENNReal.ofReal (2 * (absMomentConst u * (W : ℝ) ^ (-u / 2) * (max 1 g) ^ (-u)) *
          (max 1 g * Real.sqrt (W / (2 * π))) *
          (Cg * (W : ℝ) ^ Pg * Real.exp (-cg * cycDist a c / b) * (2 * E₀))) := by
      rw [ENNReal.ofReal_mul hA0]
      gcongr
    have hX : 2 * (absMomentConst u * (W : ℝ) ^ (-u / 2) * (max 1 g) ^ (-u)) *
          (max 1 g * Real.sqrt (W / (2 * π))) *
          (Cg * (W : ℝ) ^ Pg * Real.exp (-cg * cycDist a c / b) * (2 * E₀)) ≤
        4 * absMomentConst u * E₀ * Cg / Real.sqrt (2 * π) *
          (W : ℝ) ^ ((1 - u) / 2 + B * (1 - u) + Pg) * Real.exp (-cg * cycDist a c / b) := by
      have hW2 : (W : ℝ) ^ (-u / 2) * Real.sqrt W * (W : ℝ) ^ Pg =
          (W : ℝ) ^ ((1 - u) / 2 + Pg) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
        congr 1
        ring
      have hm2 : (max 1 g) ^ (-u) * max 1 g = (max 1 g) ^ (1 - u) := by
        rw [show 1 - u = -u + 1 by ring, Real.rpow_add hm0, Real.rpow_one]
      have hW3 : (W : ℝ) ^ ((1 - u) / 2 + B * (1 - u) + Pg) =
          (W : ℝ) ^ ((1 - u) / 2 + Pg) * (W : ℝ) ^ (B * (1 - u)) := by
        rw [← Real.rpow_add hW0]
        congr 1
        ring
      have hrw : 2 * (absMomentConst u * (W : ℝ) ^ (-u / 2) * (max 1 g) ^ (-u)) *
          (max 1 g * Real.sqrt (W / (2 * π))) *
          (Cg * (W : ℝ) ^ Pg * Real.exp (-cg * cycDist a c / b) * (2 * E₀)) =
          4 * absMomentConst u * E₀ * Cg / Real.sqrt (2 * π) *
            (((W : ℝ) ^ (-u / 2) * Real.sqrt W * (W : ℝ) ^ Pg) *
              ((max 1 g) ^ (-u) * max 1 g)) * Real.exp (-cg * cycDist a c / b) := by
        rw [Real.sqrt_div hW0.le]
        ring
      rw [hrw, hW2, hm2, hW3]
      gcongr
    have hXnn : 0 ≤ 2 * (absMomentConst u * (W : ℝ) ^ (-u / 2) * (max 1 g) ^ (-u)) *
          (max 1 g * Real.sqrt (W / (2 * π))) *
          (Cg * (W : ℝ) ^ Pg * Real.exp (-cg * cycDist a c / b) * (2 * E₀)) := by positivity
    have h3 := h1.trans (ENNReal.rpow_le_rpow h2 hp0.le)
    rw [ENNReal.ofReal_rpow_of_nonneg hXnn hp0.le,
      ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hXnn _)] at h3
    refine h3.trans ?_
    refine (Real.rpow_le_rpow hXnn hX hp0.le).trans (le_of_eq ?_)
    rw [Real.mul_rpow (by positivity) hexp0, Real.mul_rpow hK0 (by positivity),
      ← Real.rpow_mul hW0.le, ← Real.exp_mul]
    congr 2
    ring
  -- sum over the `W²` pairs of coordinates
  calc ∫ ω, blockCorr (Hmat g W L ω) J a c ∂(μ W L)
      ≤ ∫ ω, ∑ α, ∑ β, eigCorr (Hmat g W L ω) J (a, α) (c, β) ∂(μ W L) :=
        integral_mono (integrable_blockCorr_Hmat g W L hJ a c)
          (integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
            integrable_eigCorr_Hmat g W L hJ (a, α) (c, β))
          fun ω => blockCorr_le_sum_eigCorr _ _ _ _
    _ = ∑ α, ∑ β, ∫ ω, eigCorr (Hmat g W L ω) J (a, α) (c, β) ∂(μ W L) := by
        rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
          integrable_eigCorr_Hmat g W L hJ (a, α) (c, β)]
        exact Finset.sum_congr rfl fun α _ =>
          integral_finsetSum _ fun β _ => integrable_eigCorr_Hmat g W L hJ (a, α) (c, β)
    _ ≤ ∑ _α : Fin W, ∑ _β : Fin W,
          (4 * absMomentConst u * E₀ * Cg / Real.sqrt (2 * π)) ^ (1 / (4 - u)) *
            (W : ℝ) ^ (((1 - u) / 2 + B * (1 - u) + Pg) * (1 / (4 - u))) *
              Real.exp (-(cg / (4 - u)) * cycDist a c / b) :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hpair α β
    _ = _ := by
        rw [show (2 : ℝ) + ((1 - u) / 2 + B * (1 - u) + Pg) / (4 - u) =
          2 + ((1 - u) / 2 + B * (1 - u) + Pg) * (1 / (4 - u)) by ring,
          Real.rpow_add hW0, Real.rpow_two]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end LSBA
