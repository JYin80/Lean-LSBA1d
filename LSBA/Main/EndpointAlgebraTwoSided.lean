import LSBA.Main.EndpointAlgebra
import LSBA.Spectral.TwoSidedCounts

/-!
# Endpoint algebra for both halves

(1.17) [eq:main] and (1.18) [eq:simultaneous], both halves, from the count form (2.12)
[uv:eq:lower-regions-output] (E1), the upper count (3.11) [uv:eq:upper-count] and Lemma 1.3
[lem:rough-density] (E4), as in (3.12) [uv:eq:sampling].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `ℓ_{W,g,L} ≥ 0`. -/
private lemma endpointAlgebraTwoSided_ellStar_nonneg (W L : ℕ) (g : ℝ) : 0 ≤ ellStar W L g :=
  le_min (by positivity) (le_max_of_le_left (Nat.cast_nonneg _))

/-- For large `W`, `C e^{-c W² L} ≤ W^{-D}/2` for every `L ≥ 3`. -/
private lemma endpointAlgebraTwoSided_exp_small (C c D : ℝ) (hC : 0 < C) (hc : 0 < c) :
    ∀ᶠ W : ℕ in Filter.atTop, ∀ L : ℕ, 3 ≤ L →
      C * Real.exp (-c * (W : ℝ) ^ 2 * L) ≤ (W : ℝ) ^ (-D) / 2 := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero D (3 * c) (by positivity)
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, x ^ D * Real.exp (-(3 * c) * x) < 1 / (2 * C) :=
    ht.eventually (gt_mem_nhds (by positivity))
  have h2 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h1
  filter_upwards [h2, Filter.eventually_ge_atTop 1] with W hW hW1 L hL
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hexp : Real.exp (-c * (W : ℝ) ^ 2 * L) ≤ Real.exp (-(3 * c) * W) := by
    apply Real.exp_le_exp.mpr
    have h3 : 3 * (W : ℝ) ≤ (W : ℝ) ^ 2 * L := by nlinarith
    nlinarith
  have hWD : 0 < (W : ℝ) ^ D := Real.rpow_pos_of_pos hWpos D
  rw [Real.rpow_neg hWpos.le D]
  rw [lt_div_iff₀ (by positivity)] at hW
  have h4 : C * Real.exp (-(3 * c) * W) * 2 * (W : ℝ) ^ D < 1 := by linarith
  have h5 : C * Real.exp (-(3 * c) * W) ≤ ((W : ℝ) ^ D)⁻¹ / 2 := by
    have h7 : C * Real.exp (-(3 * c) * W) * 2 ≤ 1 / (W : ℝ) ^ D :=
      (le_div_iff₀ hWD).mpr (by linarith)
    rw [one_div] at h7
    linarith
  have h6 : C * Real.exp (-c * (W : ℝ) ^ 2 * L) ≤ C * Real.exp (-(3 * c) * W) :=
    mul_le_mul_of_nonneg_left hexp hC.le
  linarith

/-- (E1), the upper count (3.11) [uv:eq:upper-count] and (E4) imply (1.17) [eq:main], both halves,
as in (3.12)
[uv:eq:sampling]; `τ ≥ 1` by monotonicity in `τ`. -/
theorem ratio_of_counts_rough (κ : ℝ) (hκ : 0 < κ ∧ κ < 1 / 2)
    (hE1 : ∀ D τ : ℝ, 0 < D → 0 < τ ∧ τ < 1 → ∀ L₀ : ℕ,
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        AEMeasurable (fun ω => (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
            ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ)) (μ W L) ∧
        ((W : ℝ) * L)⁻¹ * ∫ ω, (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
            ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ) ∂(μ W L) ≤ (W : ℝ) ^ (-D))
    (hU1 : ∀ D τ : ℝ, 0 < D → 0 < τ ∧ τ < 1 → ∀ L₀ : ℕ,
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        AEMeasurable (fun ω => (badCountUp W L (Hmat g W L ω) (bulkSet g κ L₀ L)
            ((W : ℝ) ^ τ * ellStar W L g) : ℝ)) (μ W L) ∧
        ((W : ℝ) * L)⁻¹ * ∫ ω, (badCountUp W L (Hmat g W L ω) (bulkSet g κ L₀ L)
            ((W : ℝ) ^ τ * ellStar W L g) : ℝ) ∂(μ W L) ≤ (W : ℝ) ^ (-D))
    (hE4 : ∃ Wδ Lδ : ℕ, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ W : ℕ, Wδ ≤ W → ∀ L : ℕ, max Lδ 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        μ W L {ω | ∃ x : ℝ, κ / 2 < |empCDF (Hmat g W L ω) x - Fdist g x|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (W : ℝ) ^ 2 * L))) :
    ∃ L₀ : ℕ, ∀ L₁ : ℕ, L₀ ≤ L₁ → ∀ D τ : ℝ, 0 < D → 0 < τ →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        1 - (W : ℝ) ^ (-D) ≤
          ∫ ω, (goodCountTwoSided W L (Hmat g W L ω) (bulkSet g κ L₁ L)
                  ((W : ℝ) ^ (-τ) * ellStar W L g) ((W : ℝ) ^ τ * ellStar W L g) : ℝ) /
                (countIn (Hmat g W L ω) (bulkSet g κ L₁ L) : ℝ) ∂(μ W L) := by
  obtain ⟨Wδ, Lδ, C, c, hC, hc, hE4'⟩ := hE4
  refine ⟨Lδ, fun L₁ hL₁ D τ hD hτ => ?_⟩
  set τ' := min τ (1 / 2) with hτ'def
  have hτ' : 0 < τ' ∧ τ' < 1 :=
    ⟨lt_min hτ (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
  obtain ⟨W₁, hW₁⟩ := hE1 (D + 1) τ' (by linarith) hτ' L₁
  obtain ⟨W₂, hW₂⟩ := hU1 (D + 1) τ' (by linarith) hτ' L₁
  have hκ2 : 0 < 1 - 2 * κ := by linarith [hκ.2]
  have hev : ∀ᶠ W : ℕ in Filter.atTop, W₁ ≤ W ∧ W₂ ≤ W ∧ Wδ ≤ W ∧ 2 ≤ W ∧
      4 / (1 - 2 * κ) ≤ (W : ℝ) ∧
      ∀ L : ℕ, 3 ≤ L → C * Real.exp (-c * (W : ℝ) ^ 2 * L) ≤ (W : ℝ) ^ (-D) / 2 :=
    (Filter.eventually_ge_atTop W₁).and ((Filter.eventually_ge_atTop W₂).and
      ((Filter.eventually_ge_atTop Wδ).and ((Filter.eventually_ge_atTop 2).and
        ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and
          (endpointAlgebraTwoSided_exp_small C c D hC hc)))))
  obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨W₀, fun W hW L hL g hg => ?_⟩
  obtain ⟨hWW₁, hWW₂, hWWδ, hW2, hWκ, hWexp⟩ := hW₀ W hW
  have hW1 : 1 ≤ W := by omega
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW2' : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  have hWpos : (0 : ℝ) < W := by linarith
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  set J := bulkSet g κ L₁ L with hJdef
  have hJm : MeasurableSet J := measurableSet_bulkSet g κ L₁ L
  set r := (W : ℝ) ^ (-τ) * ellStar W L g with hrdef
  set R := (W : ℝ) ^ τ * ellStar W L g with hRdef
  set r' := (W : ℝ) ^ (-τ') * ellStar W L g with hr'def
  set R' := (W : ℝ) ^ τ' * ellStar W L g with hR'def
  have hrr : r ≤ r' := rpow_neg_mul_ellStar_le hW1 L g (min_le_left τ (1 / 2))
  have hRR : R' ≤ R := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hW1' (min_le_left τ (1 / 2)))
    (endpointAlgebraTwoSided_ellStar_nonneg W L g)
  obtain ⟨-, hbadW⟩ := hW₁ W hWW₁ L hL g hg
  obtain ⟨-, hupW⟩ := hW₂ W hWW₂ L hL g hg
  have hBm : ∫ ω, (badCount W L (Hmat g W L ω) J r' : ℝ) ∂(μ W L) ≤
      (W : ℝ) ^ (-(D + 1)) * ((L : ℝ) * W) := by
    rw [inv_mul_le_iff₀ (by positivity)] at hbadW
    linarith
  have hBp : ∫ ω, (badCountUp W L (Hmat g W L ω) J R' : ℝ) ∂(μ W L) ≤
      (W : ℝ) ^ (-(D + 1)) * ((L : ℝ) * W) := by
    rw [inv_mul_le_iff₀ (by positivity)] at hupW
    linarith
  -- good count, bad count := count - good count
  have hgle : ∀ ω, goodCountTwoSided W L (Hmat g W L ω) J r R ≤ countIn (Hmat g W L ω) J :=
    fun ω => by
      have h1 := goodCountTwoSided_le_goodCount W L (Hmat g W L ω) J r R
      have h2 := goodCount_add_badCount W L (Hmat g W L ω) J r
      omega
  have hsum : ∀ ω, goodCountTwoSided W L (Hmat g W L ω) J r R +
      (countIn (Hmat g W L ω) J - goodCountTwoSided W L (Hmat g W L ω) J r R) =
        countIn (Hmat g W L ω) J := fun ω => by
    have := hgle ω
    omega
  have hbadle : ∀ ω, countIn (Hmat g W L ω) J - goodCountTwoSided W L (Hmat g W L ω) J r R ≤
      badCount W L (Hmat g W L ω) J r' + badCountUp W L (Hmat g W L ω) J R' := fun ω => by
    have h1 := countIn_le_goodTwoSided_add W L (Hmat g W L ω) J r' R'
    have h2 := goodCountTwoSided_mono W L (Hmat g W L ω) J hrr hRR
    omega
  have hcntm : Measurable fun ω => countIn (Hmat g W L ω) J := measurable_countIn_Hmat g W L hJm
  have hgoodAE := aemeasurable_goodCountTwoSided_Hmat g W L hJm r R
  have hR : AEMeasurable (fun ω => (goodCountTwoSided W L (Hmat g W L ω) J r R : ℝ) /
      (countIn (Hmat g W L ω) J : ℝ)) (μ W L) :=
    hgoodAE.div (measurable_from_nat.comp hcntm).aemeasurable
  have hbadAE : AEMeasurable (fun ω =>
      ((countIn (Hmat g W L ω) J - goodCountTwoSided W L (Hmat g W L ω) J r R : ℕ) : ℝ))
      (μ W L) := by
    have heq : (fun ω => ((countIn (Hmat g W L ω) J -
        goodCountTwoSided W L (Hmat g W L ω) J r R : ℕ) : ℝ)) =
        fun ω => (countIn (Hmat g W L ω) J : ℝ) -
          (goodCountTwoSided W L (Hmat g W L ω) J r R : ℝ) :=
      funext fun ω => Nat.cast_sub (hgle ω)
    rw [heq]
    exact (measurable_from_nat.comp hcntm).aemeasurable.sub hgoodAE
  have hbm := integrable_badCount_Hmat g W L hJm r'
  have hbp := integrable_badCountUp_Hmat g W L hJm R'
  have hbs : Integrable (fun ω => (badCount W L (Hmat g W L ω) J r' : ℝ) +
      (badCountUp W L (Hmat g W L ω) J R' : ℝ)) (μ W L) := hbm.add hbp
  have hb : Integrable (fun ω =>
      ((countIn (Hmat g W L ω) J - goodCountTwoSided W L (Hmat g W L ω) J r R : ℕ) : ℝ))
      (μ W L) := by
    refine Integrable.mono' hbs hbadAE.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hbadle ω
  have hbad : ∫ ω, ((countIn (Hmat g W L ω) J -
      goodCountTwoSided W L (Hmat g W L ω) J r R : ℕ) : ℝ) ∂(μ W L) ≤
      (2 * (W : ℝ) ^ (-(D + 1))) * ((L : ℝ) * W) := by
    have h1 : ∫ ω, ((countIn (Hmat g W L ω) J -
        goodCountTwoSided W L (Hmat g W L ω) J r R : ℕ) : ℝ) ∂(μ W L) ≤
        ∫ ω, ((badCount W L (Hmat g W L ω) J r' : ℝ) +
          (badCountUp W L (Hmat g W L ω) J R' : ℝ)) ∂(μ W L) :=
      integral_mono hb hbs fun ω => by exact_mod_cast hbadle ω
    rw [integral_add hbm hbp] at h1
    linarith
  have hcard : (Fintype.card (Fin L × Fin W) : ℝ) = (L : ℝ) * W := by simp
  have hWD : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg hWpos.le _
  have hsplit : (W : ℝ) ^ (-(D + 1)) = (W : ℝ) ^ (-D) * (W : ℝ)⁻¹ := by
    rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
  by_cases hLL : L < L₁
  · -- `L < L₁`: `J = ℝ` and the count is `L W`
    have hJu : J = Set.univ := by simp [hJdef, bulkSet, hLL]
    have h := integral_ratio_ge (μ W L)
      (fun ω => goodCountTwoSided W L (Hmat g W L ω) J r R)
      (fun ω => countIn (Hmat g W L ω) J - goodCountTwoSided W L (Hmat g W L ω) J r R)
      (fun ω => countIn (Hmat g W L ω) J) hsum hR hb
      Set.univ (m := (L : ℝ) * W) (by positivity)
      (fun ω _ => by
        rw [hJu, countIn_univ (Hmat_isHermitian g W L ω), hcard])
      (ε₁ := 0) le_rfl (by simp) (ε₂ := 2 * (W : ℝ) ^ (-(D + 1))) hbad
    have hq : (W : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hW2'
    have h2 : 2 * (W : ℝ) ^ (-(D + 1)) ≤ (W : ℝ) ^ (-D) := by
      rw [hsplit]
      have := mul_le_mul_of_nonneg_left hq hWD
      linarith
    linarith
  · -- `L ≥ L₁`: the bulk set of (1.16) [eq:bulk-sampling] and the event of Lemma 1.3
    -- [lem:rough-density]
    have hJb : J = {E | κ / 2 ≤ Fdist g (-|E|)} := by simp [hJdef, bulkSet, hLL]
    set G := {ω : Ω W L | ∀ x, |empCDF (Hmat g W L ω) x - Fdist g x| ≤ κ / 2} with hGdef
    have hGc : μ W L Gᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * (W : ℝ) ^ 2 * L)) := by
      refine le_trans (measure_mono ?_)
        (hE4' W hWWδ L (max_le (hL₁.trans (not_lt.mp hLL)) hL) g hg)
      intro ω hω
      simpa [hGdef, not_forall, not_le] using hω
    have h := integral_ratio_ge (μ W L)
      (fun ω => goodCountTwoSided W L (Hmat g W L ω) J r R)
      (fun ω => countIn (Hmat g W L ω) J - goodCountTwoSided W L (Hmat g W L ω) J r R)
      (fun ω => countIn (Hmat g W L ω) J) hsum hR hb
      G (m := (1 - 2 * κ) * ((L : ℝ) * W)) (by positivity)
      (fun ω hω => by
        rw [hJb, ← hcard]
        exact countIn_bulk_ge (Hmat_isHermitian g W L ω) (Fdist_continuous g hg)
          (Fdist_monotone g) (Fdist_neg g hg) hω)
      (by positivity) hGc (ε₂ := (1 - 2 * κ)⁻¹ * (2 * (W : ℝ) ^ (-(D + 1))))
      (by
        have : (1 - 2 * κ)⁻¹ * (2 * (W : ℝ) ^ (-(D + 1))) * ((1 - 2 * κ) * ((L : ℝ) * W)) =
            (2 * (W : ℝ) ^ (-(D + 1))) * ((L : ℝ) * W) := by
          field_simp
        rw [this]
        exact hbad)
    have h1 := hWexp L hL
    have hq : (1 - 2 * κ)⁻¹ * (W : ℝ)⁻¹ ≤ 1 / 4 := by
      rw [div_le_iff₀ hκ2] at hWκ
      calc (1 - 2 * κ)⁻¹ * (W : ℝ)⁻¹ = ((1 - 2 * κ) * W)⁻¹ := (mul_inv _ _).symm
        _ ≤ 4⁻¹ := inv_anti₀ (by norm_num) (by linarith)
        _ = 1 / 4 := by norm_num
    have h2 : (1 - 2 * κ)⁻¹ * (2 * (W : ℝ) ^ (-(D + 1))) ≤ (W : ℝ) ^ (-D) / 2 := by
      rw [hsplit]
      have := mul_le_mul_of_nonneg_left hq hWD
      calc (1 - 2 * κ)⁻¹ * (2 * ((W : ℝ) ^ (-D) * (W : ℝ)⁻¹)) =
          2 * ((W : ℝ) ^ (-D) * ((1 - 2 * κ)⁻¹ * (W : ℝ)⁻¹)) := by ring
        _ ≤ 2 * ((W : ℝ) ^ (-D) * (1 / 4)) := by linarith
        _ = (W : ℝ) ^ (-D) / 2 := by ring
    linarith

/-- (E1) and the upper count (3.11) [uv:eq:upper-count] imply (1.18) [eq:simultaneous], both halves,
by Markov's
inequality. -/
theorem simultaneous_of_counts (BL D τ κ : ℝ) (hBL : 0 < BL) (hD : 0 < D) (hτ : 0 < τ) (L₀ : ℕ)
    (hE1 : ∀ D' τ' : ℝ, 0 < D' → 0 < τ' ∧ τ' < 1 →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        AEMeasurable (fun ω => (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
            ((W : ℝ) ^ (-τ') * ellStar W L g) : ℝ)) (μ W L) ∧
        ((W : ℝ) * L)⁻¹ * ∫ ω, (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
            ((W : ℝ) ^ (-τ') * ellStar W L g) : ℝ) ∂(μ W L) ≤ (W : ℝ) ^ (-D'))
    (hU1 : ∀ D' τ' : ℝ, 0 < D' → 0 < τ' ∧ τ' < 1 →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        AEMeasurable (fun ω => (badCountUp W L (Hmat g W L ω) (bulkSet g κ L₀ L)
            ((W : ℝ) ^ τ' * ellStar W L g) : ℝ)) (μ W L) ∧
        ((W : ℝ) * L)⁻¹ * ∫ ω, (badCountUp W L (Hmat g W L ω) (bulkSet g κ L₀ L)
            ((W : ℝ) ^ τ' * ellStar W L g) : ℝ) ∂(μ W L) ≤ (W : ℝ) ^ (-D')) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → (L : ℝ) ≤ (W : ℝ) ^ BL → ∀ g : ℝ, 0 ≤ g →
      μ W L {ω | 0 < badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ (-τ) * ellStar W L g) +
        badCountUp W L (Hmat g W L ω) (bulkSet g κ L₀ L) ((W : ℝ) ^ τ * ellStar W L g)} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  set τ' := min τ (1 / 2) with hτ'def
  have hτ' : 0 < τ' ∧ τ' < 1 :=
    ⟨lt_min hτ (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
  obtain ⟨W₁, hW₁⟩ := hE1 (D + BL + 2) τ' (by linarith) hτ'
  obtain ⟨W₂, hW₂⟩ := hU1 (D + BL + 2) τ' (by linarith) hτ'
  refine ⟨max (max W₁ W₂) 2, fun W hW L hL hLW g hg => ?_⟩
  have hWW₁ : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hWW₂ : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW2 : 2 ≤ W := (le_max_right _ _).trans hW
  have hW1 : 1 ≤ W := by omega
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW2' : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  have hWpos : (0 : ℝ) < W := by linarith
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  set J := bulkSet g κ L₀ L with hJdef
  have hJm : MeasurableSet J := measurableSet_bulkSet g κ L₀ L
  have hrr : (W : ℝ) ^ (-τ) * ellStar W L g ≤ (W : ℝ) ^ (-τ') * ellStar W L g :=
    rpow_neg_mul_ellStar_le hW1 L g (min_le_left τ (1 / 2))
  have hRR : (W : ℝ) ^ τ' * ellStar W L g ≤ (W : ℝ) ^ τ * ellStar W L g :=
    mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hW1' (min_le_left τ (1 / 2)))
      (endpointAlgebraTwoSided_ellStar_nonneg W L g)
  obtain ⟨-, hbadW⟩ := hW₁ W hWW₁ L hL g hg
  obtain ⟨-, hupW⟩ := hW₂ W hWW₂ L hL g hg
  have hbm := integrable_badCount_Hmat g W L hJm ((W : ℝ) ^ (-τ') * ellStar W L g)
  have hbp := integrable_badCountUp_Hmat g W L hJm ((W : ℝ) ^ τ' * ellStar W L g)
  have hsub : {ω | 0 < badCount W L (Hmat g W L ω) J ((W : ℝ) ^ (-τ) * ellStar W L g) +
        badCountUp W L (Hmat g W L ω) J ((W : ℝ) ^ τ * ellStar W L g)} ⊆
      {ω | 0 < badCount W L (Hmat g W L ω) J ((W : ℝ) ^ (-τ') * ellStar W L g) +
        badCountUp W L (Hmat g W L ω) J ((W : ℝ) ^ τ' * ellStar W L g)} := by
    intro ω hω
    have h1 := badCount_mono W L (Hmat g W L ω) (subset_refl J) hrr
    have h2 := badCountUp_mono W L (Hmat g W L ω) (subset_refl J) hRR
    simp only [Set.mem_ofPred_eq] at hω ⊢
    omega
  have hbs : Integrable (fun ω =>
      ((badCount W L (Hmat g W L ω) J ((W : ℝ) ^ (-τ') * ellStar W L g) +
        badCountUp W L (Hmat g W L ω) J ((W : ℝ) ^ τ' * ellStar W L g) : ℕ) : ℝ)) (μ W L) := by
    have h : Integrable (fun ω => (badCount W L (Hmat g W L ω) J
        ((W : ℝ) ^ (-τ') * ellStar W L g) : ℝ) +
        (badCountUp W L (Hmat g W L ω) J ((W : ℝ) ^ τ' * ellStar W L g) : ℝ)) (μ W L) :=
      hbm.add hbp
    simpa only [Nat.cast_add] using h
  refine (measure_mono hsub).trans ((measure_pos_le_integral _ _ hbs).trans
    (ENNReal.ofReal_le_ofReal ?_))
  have hint : ∫ ω, ((badCount W L (Hmat g W L ω) J ((W : ℝ) ^ (-τ') * ellStar W L g) +
        badCountUp W L (Hmat g W L ω) J ((W : ℝ) ^ τ' * ellStar W L g) : ℕ) : ℝ) ∂(μ W L) =
      ∫ ω, (badCount W L (Hmat g W L ω) J ((W : ℝ) ^ (-τ') * ellStar W L g) : ℝ) ∂(μ W L) +
      ∫ ω, (badCountUp W L (Hmat g W L ω) J ((W : ℝ) ^ τ' * ellStar W L g) : ℝ) ∂(μ W L) := by
    simp only [Nat.cast_add]
    exact integral_add hbm hbp
  rw [hint]
  rw [inv_mul_le_iff₀ (by positivity)] at hbadW hupW
  have hWD' : 0 ≤ (W : ℝ) ^ (-(D + BL + 2)) := Real.rpow_nonneg hWpos.le _
  have hsplit : (W : ℝ) ^ (-(D + 1)) = (W : ℝ) ^ (-D) * (W : ℝ)⁻¹ := by
    rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
  have hkey : ((W : ℝ) * L) * (W : ℝ) ^ (-(D + BL + 2)) ≤ (W : ℝ) ^ (-(D + 1)) := by
    calc ((W : ℝ) * L) * (W : ℝ) ^ (-(D + BL + 2)) ≤
        ((W : ℝ) * (W : ℝ) ^ BL) * (W : ℝ) ^ (-(D + BL + 2)) := by gcongr
      _ = (W : ℝ) ^ (-(D + 1)) := by
        rw [show (W : ℝ) * (W : ℝ) ^ BL = (W : ℝ) ^ (1 + BL) by
          rw [Real.rpow_add hWpos, Real.rpow_one], ← Real.rpow_add hWpos]
        congr 1
        ring
  have hq : (W : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hW2'
  have hWD : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg hWpos.le _
  have h2 := mul_le_mul_of_nonneg_left hq hWD
  linarith

end LSBA
