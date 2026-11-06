import LSBA.Upper.PathMoment
import LSBA.Upper.FracCyclePath
import LSBA.Upper.FracConcentration
import LSBA.Upper.TailUnion
import LSBA.Spectral.OutlierCount

/-!
# Theorem 3.1 [thm:strong-upper]: strong-disorder concentration

Theorem 3.1 [thm:strong-upper] with (3.7) [eq:strong-radius], proved as at the end of Section 8.1
[sec:fr-concentration]: the path form of [PSSS, Theorem 1] gives (8.2) [up:eq:fmr-pointwise] on
every Dirichlet path at exponent `1/2`, with `𝔟 = 1`, for `0 ≤ g ≤ c_* W^{-1/2}`; the Schur
identity (E.15) [eq:c-cycle-Schur] and (8.7) [eq:c-apriori] give (8.2) [up:eq:fmr-pointwise] on the
cycle at `q = 1/4`;
Lemma 8.1 [uva:thm:upper-audit] (i) on `J = [-33/2, 33/2]` with exponents `A` and `D + 1` gives
(3.6) [eq:averaged-tail] at radius `⌈C log W⌉ ≤ ⌈(log W)²⌉`; the mean fraction of eigenvalues
outside `J` is at most `e^{-W/2}`. Then `W^{-D-1} + e^{-W/2} ≤ W^{-D}` gives (3.6)
[eq:averaged-tail] on `ℝ`, uniformly
in `L ≥ 3`; the case `g = 0` is included.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `e^{-W/2} ≤ W^{-D}/2` for `W ≥ 16 (D + 1)²`. -/
private theorem strongUpper_outlier {D W : ℝ} (hD : 0 < D) (hW : 16 * (D + 1) ^ 2 ≤ W) :
    Real.exp (-W / 2) ≤ 1 / 2 * W ^ (-D) := by
  have hW0 : 0 < W := lt_of_lt_of_le (by positivity) hW
  set s := Real.sqrt W with hs_def
  have hs4 : 4 * (D + 1) ≤ s := by
    rw [hs_def]
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hs0 : 0 < s := by nlinarith
  have hss : s * s = W := Real.mul_self_sqrt hW0.le
  have hlogW : Real.log W ≤ 2 * s := by
    have h := Real.log_le_sub_one_of_pos hs0
    have h2 : Real.log s = Real.log W / 2 := Real.log_sqrt hW0.le
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hhalf : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have h1 : -W / 2 ≤ -Real.log 2 + Real.log W * -D := by
    have : D * Real.log W ≤ D * (2 * s) := mul_le_mul_of_nonneg_left hlogW hD.le
    have h4 : 4 * (D + 1) * s ≤ s * s := mul_le_mul_of_nonneg_right hs4 hs0.le
    nlinarith
  rw [Real.rpow_def_of_pos hW0, hhalf, ← Real.exp_add]
  exact Real.exp_le_exp.2 h1

/-- The eigenvalue count is at most the dimension `L * W`. -/
private theorem strongUpper_countIn_le (W L : ℕ) (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (J : Set ℝ) : countIn H J ≤ L * W := by
  unfold countIn
  split_ifs
  · refine (Finset.card_filter_le _ _).trans ?_
    simp
  · exact Nat.zero_le _

/-- Theorem 3.1 [thm:strong-upper] with (3.7) [eq:strong-radius]. -/
theorem strong_upper : StrongUpper := by
  obtain ⟨cs, hcs0, hcs1, W₁, hpath⟩ := fracPath_strong
  obtain ⟨W₂, hcyc⟩ := frac_cycle_of_path (C₀ := 1) (p := 1 / 2) (C := 9 / 4) (c := 1) le_rfl
    (by norm_num) (by norm_num) (by norm_num) one_pos
  refine ⟨cs, hcs0, hcs1, fun A D hA hD => ?_⟩
  obtain ⟨CD, hCD, W₃, hconc⟩ := frac_concentration_fixed (C₀ := 1) (E₀ := 33 / 2)
    (q := 1 / 2 / 2) (C := ((1 + 2) * (1 / 2) + 9 / 4) / 2 + 1) (c := 1 / 2) le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) A (D + 1) hA (by linarith)
  refine ⟨max (max W₁ W₂) (max W₃ (max (max 32 ⌈16 * (D + 1) ^ 2⌉₊) ⌈Real.exp CD⌉₊)), ?_⟩
  intro W hW L hL g hg0 hg
  have hW₁ : W₁ ≤ W := by omega
  have hW₂ : W₂ ≤ W := by omega
  have hW₃ : W₃ ≤ W := by omega
  have hW32 : 32 ≤ W := by omega
  have hW16 : 16 * (D + 1) ^ 2 ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (by omega))
  have hWexp : Real.exp CD ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (by omega))
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast (by omega : 2 ≤ W)
  have hlogW : CD ≤ Real.log W := by
    rw [← Real.log_exp CD]
    exact Real.log_le_log (Real.exp_pos _) hWexp
  have hlog0 : 0 ≤ Real.log W := hCD.le.trans hlogW
  -- `g ≤ 1/4`, as `cs ≤ 1` and `W ≥ 32`
  have hg4 : g ≤ 1 / 4 := by
    have hs : (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 4 := by
      rw [Real.rpow_neg hWpos.le, ← Real.sqrt_eq_rpow, one_div, inv_le_inv₀
        (Real.sqrt_pos.2 hWpos) (by norm_num)]
      exact Real.le_sqrt_of_sq_le (by
        have : (32 : ℝ) ≤ W := by exact_mod_cast hW32
        linarith)
    have hrp : 0 ≤ (W : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    nlinarith
  have hgW : g ≤ (W : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    linarith
  set J₀ : Set ℝ := Set.Icc (-(33 / 2 : ℝ)) (33 / 2) with hJ₀
  have hJm : MeasurableSet J₀ := measurableSet_Icc
  -- (8.2) [up:eq:fmr-pointwise] on the cycle at `q = 1/4`, `𝔟 = 1`
  have hF : FracCycle W L g J₀ (1 / 2 / 2) (((1 + 2) * (1 / 2) + 9 / 4) / 2 + 1) (1 / 2) 1 :=
    (hcyc W hW₂ L hL g 1 hg0 hgW le_rfl Set.univ
      (hpath W hW₁ (L - 1) g hg0 hg)).mono (by omega) (Set.subset_univ _) le_rfl
      (by norm_num) le_rfl one_pos le_rfl
  -- Lemma 8.1(i) [uva:thm:upper-audit] at `A`, `D + 1`, and the radius
  have hRle : (⌈CD * 1 * Real.log W⌉₊ : ℝ) ≤ (⌈Real.log W ^ 2⌉₊ : ℝ) := by
    refine Nat.cast_le.mpr (Nat.ceil_mono ?_)
    rw [mul_one, sq]
    exact mul_le_mul_of_nonneg_right hlogW hlog0
  have hmain : AveragedTailBound W L g J₀ (⌈Real.log W ^ 2⌉₊ : ℝ) A (D + 1) :=
    averagedTailBound_mono subset_rfl hJm hRle
      (hconc W hW₃ L hL g 1 hg0 hgW le_rfl (by rw [Real.rpow_one]; exact hW1) J₀ hJm
        (Set.Subset.refl _) hF)
  set R : ℝ := (⌈Real.log W ^ 2⌉₊ : ℝ) with hR_def
  have hmain' : ((W : ℝ) * L)⁻¹ * ∫ ω, (tailCount W L (Hmat g W L ω) J₀ R A : ℝ) ∂(μ W L) ≤
      1 / 2 * (W : ℝ) ^ (-D) := by
    refine hmain.trans ?_
    rw [neg_add', Real.rpow_sub_one hWpos.ne']
    rw [div_eq_mul_inv]
    have hp : 0 < (W : ℝ) ^ (-D) := Real.rpow_pos_of_pos hWpos _
    have hinv : (W : ℝ)⁻¹ ≤ 1 / 2 := (inv_anti₀ (by norm_num) hW2).trans_eq (by norm_num)
    exact mul_comm (1 / 2 : ℝ) _ ▸ mul_le_mul_of_nonneg_left hinv hp.le
  have hout : ((W : ℝ) * L)⁻¹ * ∫ ω, (countIn (Hmat g W L ω) J₀ᶜ : ℝ) ∂(μ W L) ≤
      1 / 2 * (W : ℝ) ^ (-D) :=
    (outlier_mean_le hg0 hg4 hW32 L).trans (strongUpper_outlier hD hW16)
  -- integrate `tailCount univ ≤ tailCount J₀ + countIn J₀ᶜ`
  have hi1 := integrable_tailCount_Hmat g W L hJm R A
  have hiU := integrable_tailCount_Hmat g W L MeasurableSet.univ R A
  have hi2 : Integrable (fun ω => (countIn (Hmat g W L ω) J₀ᶜ : ℝ)) (μ W L) := by
    refine Integrable.of_bound (C := (L * W : ℕ)) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact (measurable_from_nat.comp
        (measurable_countIn_Hmat g W L hJm.compl)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact Nat.cast_le.2 (strongUpper_countIn_le _ _ _ _)
  have hle : ∫ ω, (tailCount W L (Hmat g W L ω) Set.univ R A : ℝ) ∂(μ W L) ≤
      ∫ ω, (tailCount W L (Hmat g W L ω) J₀ R A : ℝ) ∂(μ W L) +
        ∫ ω, (countIn (Hmat g W L ω) J₀ᶜ : ℝ) ∂(μ W L) := by
    rw [← integral_add hi1 hi2]
    refine integral_mono hiU (hi1.add hi2) fun ω => ?_
    have h1 := tailCount_union_le W L (Hmat g W L ω) J₀ J₀ᶜ R A
    have h2 := tailCount_le_countIn W L (Hmat g W L ω) J₀ᶜ R A
    rw [Set.union_compl_self] at h1
    have h3 : tailCount W L (Hmat g W L ω) Set.univ R A ≤
        tailCount W L (Hmat g W L ω) J₀ R A + countIn (Hmat g W L ω) J₀ᶜ := h1.trans (by omega)
    exact_mod_cast h3
  unfold AveragedTailBound
  have hnn : (0 : ℝ) ≤ ((W : ℝ) * L)⁻¹ := inv_nonneg.2 (by positivity)
  calc ((W : ℝ) * L)⁻¹ * ∫ ω, (tailCount W L (Hmat g W L ω) Set.univ R A : ℝ) ∂(μ W L)
      ≤ ((W : ℝ) * L)⁻¹ * (∫ ω, (tailCount W L (Hmat g W L ω) J₀ R A : ℝ) ∂(μ W L) +
        ∫ ω, (countIn (Hmat g W L ω) J₀ᶜ : ℝ) ∂(μ W L)) :=
        mul_le_mul_of_nonneg_left hle hnn
    _ = ((W : ℝ) * L)⁻¹ * ∫ ω, (tailCount W L (Hmat g W L ω) J₀ R A : ℝ) ∂(μ W L) +
        ((W : ℝ) * L)⁻¹ * ∫ ω, (countIn (Hmat g W L ω) J₀ᶜ : ℝ) ∂(μ W L) := by ring
    _ ≤ 1 / 2 * (W : ℝ) ^ (-D) + 1 / 2 * (W : ℝ) ^ (-D) := add_le_add hmain' hout
    _ = (W : ℝ) ^ (-D) := by ring

end LSBA
