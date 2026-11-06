import LSBA.Main.AssemblyWindow
import LSBA.Main.AssemblyScales
import LSBA.Transfer.ShortSpreading
import LSBA.Small.Lower
import LSBA.Final.Large
import LSBA.Main.RoughDensity

/-!
# The endpoints of the lower bound

(E1) the count form (2.12) [uv:eq:lower-regions-output] of the proof of the lower bound in
Theorem 1.4 [thm:main]; (E2) the lower half of (1.17) [eq:main]; (E3) the lower half of (1.18)
[eq:simultaneous] in Corollary 1.5 [cor:simultaneous]; (E4) Lemma 1.3 [lem:rough-density].
(E1) combines Lemma 2.1 [thm:orbital], Lemma 2.4 [uv:lem:short-spreading], Theorem 2.2
[uv:lem:lower-volume] and the resolvent moments at small and bounded coupling (Theorem 2.3
[thm:bounded-lower]) and at large coupling (Theorem 2.5 [uvu:thm:terminal]).
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `A ≤ W^s` for large `W`, when `s > 0`. -/
private lemma endpoints_le_rpow (A : ℝ) {s : ℝ} (hs : 0 < s) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → A ≤ (W : ℝ) ^ s := by
  have h := (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h.eventually_ge_atTop A)
  exact ⟨N, hN⟩

/-- (E1) (2.12) [uv:eq:lower-regions-output], every fixed threshold `L₀`. -/
theorem lower_count_endpoint (κ D τ : ℝ) (hκ : 0 < κ ∧ κ < 1 / 2) (hD : 0 < D)
    (hτ : 0 < τ ∧ τ < 1) (L₀ : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
      AEMeasurable (fun ω => (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ)) (μ W L) ∧
      ((W : ℝ) * L)⁻¹ * ∫ ω, (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ) ∂(μ W L) ≤ (W : ℝ) ^ (-D) := by
  obtain ⟨hκ0, hκ1⟩ := hκ
  obtain ⟨hτ0, hτ1⟩ := hτ
  -- exponents: ν = τ/4 < τ/2, p = 2 + (D+1)/(τ-ν)
  set ν : ℝ := τ / 4 with hνdef
  have hν0 : 0 < ν := by positivity
  have hντ : ν < τ / 2 := by linarith
  have hν1 : ν < 1 := by linarith
  have hq : 0 < (D + 1) / (τ - ν) := div_pos (by linarith) (by linarith)
  set p : ℝ := 2 + (D + 1) / (τ - ν) with hpdef
  have hp : 1 + (D + 1) / (τ - ν) < p := by linarith
  have hp0 : 0 < p := by linarith
  -- Lemma 2.4 [uv:lem:short-spreading]: C_κ, then (W₀, c_κ, C, c) at L₀
  obtain ⟨Css, hss⟩ := short_spreading κ ⟨hκ0, hκ1⟩
  obtain ⟨Wss, cκ, Cs, cs, hcκ, hcs, hssW⟩ := hss L₀
  -- Theorem 2.5 [uvu:thm:terminal] at the margin κ²/64
  have hκL : 0 < κ ^ 2 / 64 ∧ κ ^ 2 / 64 < 2 := ⟨by positivity, by nlinarith⟩
  obtain ⟨CκL, CpL, hCκL, hCpL, hlarge⟩ := large_lower (κ ^ 2 / 64) ν p hκL ⟨hν0, hν1⟩ hp0
  -- the split point C_*
  set Cst : ℝ := max (max CκL (128 / κ ^ 2)) (max Css 1) with hCst
  have hCst1 : 1 ≤ Cst := le_trans (le_max_right _ _) (le_max_right _ _)
  have hCstL : CκL ≤ Cst := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCst128 : 128 / κ ^ 2 ≤ Cst := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCstss : Css ≤ Cst := le_trans (le_max_left _ _) (le_max_right _ _)
  -- the moment bound on [W^{-1/2}, C_*] with the window F_g(-|E|) ≥ κ/4
  obtain ⟨CpS, hCpS, hsmall⟩ := small_lower_fdist Cst (κ / 4) ν p (by linarith)
    ⟨by linarith, by linarith⟩ ⟨hν0, hν1⟩ hp0
  set Cp : ℝ := max CpS CpL with hCp
  -- Theorem 2.2 [uv:lem:lower-volume] with E₀ = 4
  obtain ⟨WLV, hLV⟩ := lower_volume 4 D τ ν p Cp (by norm_num) hD ⟨hτ0, hτ1⟩ ⟨hν0, hντ⟩ hp
  -- the rates, then the thresholds of the moment theorems
  obtain ⟨WS, hS⟩ := hsmall _ (tendsto_min_rpow_div_log hτ0 hν1)
  obtain ⟨WL, hL⟩ := hlarge _ (tendsto_rpow_div_log (s := τ / 2) (by positivity))
  -- Lemma 2.1 [thm:orbital] on (2.4) [uv:eq:haar-lower-region] and on the short cycles L < L₀
  obtain ⟨WH, hH⟩ := haar_region_count τ D hτ0 hD
  obtain ⟨Wsc, hsc⟩ := haar_short_cycle_count τ D hτ0 hD L₀
  -- deterministic thresholds
  obtain ⟨Wt, ht⟩ := exp_tail_le_rpow Cs cs D hcs
  obtain ⟨W1, h1⟩ := endpoints_le_rpow 8 hτ0
  obtain ⟨W2, h2⟩ := endpoints_le_rpow (8 * Cst ^ 2) hν0
  obtain ⟨W3, h3⟩ := endpoints_le_rpow (32 / κ ^ 2) (s := 1 - ν) (by linarith)
  obtain ⟨W4, h4⟩ := endpoints_le_rpow (1 / cκ) (s := τ / 2) (by positivity)
  refine ⟨max (max (max (max Wss WLV) (max WS WL)) (max (max WH Wsc) (max Wt W1)))
    (max (max W2 W3) (max W4 3)), fun W hW L hL3 g hg => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨⟨hWss, hWLV⟩, hWS, hWL⟩, ⟨hWH, hWsc⟩, hWt, hW1⟩, ⟨hW2, hW3⟩, hW4, hW3'⟩ := hW
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hW1' : 1 ≤ W := by omega
  refine ⟨aemeasurable_badCount_Hmat g W L (measurableSet_bulkSet g κ L₀ L) _, ?_⟩
  -- case (i): L < L₀
  by_cases hi : L < L₀
  · exact hsc W hWsc L hi g _ (measurableSet_bulkSet g κ L₀ L)
  push Not at hi
  -- case (ii): the region (2.4) [uv:eq:haar-lower-region]
  by_cases hii : ellStar W L g ≤ (W : ℝ) ^ (1 + τ) / 8
  · exact hH W hWH L g hii _ (measurableSet_bulkSet g κ L₀ L)
  push Not at hii
  -- `c = W^{-τ/2}` in the two scale bounds
  have hcτ : (W : ℝ) ^ (-(τ / 2)) * (W : ℝ) ^ τ = (W : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hWpos]
    congr 1
    ring
  -- case (iii): `g ≥ C_*` and `L ≤ W^{τ/2} g²`, proof of Theorem 1.4 [thm:main]
  by_cases hiii : Cst ≤ g ∧ (L : ℝ) ≤ (W : ℝ) ^ (τ / 2) * g ^ 2
  · obtain ⟨hgC, hLg⟩ := hiii
    have hgss : Css ≤ g := hCstss.trans hgC
    have hg1 : 1 ≤ g := hCst1.trans hgC
    have hcW : 1 ≤ (W : ℝ) ^ (-(τ / 2)) * (W : ℝ) ^ τ := by
      rw [hcτ]
      exact Real.one_le_rpow (by exact_mod_cast hW1') (by positivity)
    have hLg' : (L : ℝ) ≤ (W : ℝ) ^ (-(τ / 2)) * (W : ℝ) ^ τ * g ^ 2 := by
      rw [hcτ]
      exact hLg
    have hcκW : (W : ℝ) ^ (-(τ / 2)) ≤ cκ := by
      have := h4 W hW4
      rw [div_le_iff₀ hcκ] at this
      rw [Real.rpow_neg hWpos.le, inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos hWpos _)]
      linarith
    have hthr : (W : ℝ) ^ (-τ) * ellStar W L g ≤ cκ * W * min (L : ℝ) (g ^ 2) :=
      (shortRegion_threshold hW1' L hg1 hcW hLg').trans (by gcongr)
    have hmono : ∫ ω, (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ) ∂(μ W L) ≤
        ∫ ω, (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          (cκ * W * min (L : ℝ) (g ^ 2)) : ℝ) ∂(μ W L) :=
      integral_mono (integrable_badCount_Hmat g W L (measurableSet_bulkSet g κ L₀ L) _)
        (integrable_badCount_Hmat g W L (measurableSet_bulkSet g κ L₀ L) _)
        (fun ω => by exact_mod_cast badCount_mono W L _ subset_rfl hthr)
    calc ((W : ℝ) * L)⁻¹ * ∫ ω, (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ) ∂(μ W L)
        ≤ ((W : ℝ) * L)⁻¹ * ∫ ω, (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          (cκ * W * min (L : ℝ) (g ^ 2)) : ℝ) ∂(μ W L) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ Cs * Real.exp (-cs * W) := hssW W hWss L hL3 g hgss
      _ ≤ (W : ℝ) ^ (-D) := ht W hWt
  -- case (iv): Theorem 2.2 [uv:lem:lower-volume] on J = [-a, a]
  obtain ⟨a, ha0, ha4, hFa, hJ⟩ := bulkSet_eq_Icc g κ hg ⟨hκ0, hκ1⟩ L₀ L hi
  rw [hJ]
  refine hLV W hWLV L hL3 g hg (-a) a (by linarith) ha4 ?_
  intro E hE x
  obtain ⟨hη0, hηle⟩ := volEta_pos_le hW1' (show 1 ≤ L by omega) g ν
  have hηκ : volEta W L g ν ≤ κ ^ 2 / 32 := by
    refine hηle.trans ?_
    have h3' := h3 W hW3
    have hpos : 0 < (W : ℝ) ^ (1 - ν) := Real.rpow_pos_of_pos hWpos _
    rw [show ν - 1 = -(1 - ν) by ring, Real.rpow_neg hWpos.le]
    rw [div_le_iff₀ (by positivity)] at h3'
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  have hF : κ / 4 ≤ Fdist g (-|E|) :=
    fdist_window g κ a _ hg ⟨hκ0, hκ1⟩ ha0 hFa hη0 hηκ E (by simpa using hE)
  have hlog : 0 < Real.log W := Real.log_pos (by exact_mod_cast (show 1 < W by omega))
  by_cases hgs : g ≤ Cst
  · -- g ≤ C_*: `small_lower_fdist` at the cycle length L_c
    obtain ⟨hlow, hup⟩ := volLc_small (show 3 ≤ W by omega) L hg hgs hCst1 (h2 W hW2) hii
    have hg12 := (haar_exclusion hW1' L hg (h1 W hW1) hii).2
    have hρ : min ((W : ℝ) ^ τ / 8) (4 * (W : ℝ) ^ (1 - ν)) / Real.log W * Real.log W ≤
        (volLc W L g ν : ℕ) := by
      rw [div_mul_cancel₀ _ hlog.ne']
      exact hlow
    exact ((hS W hWS (volLc W L g ν) hρ hup g hg12 hgs E hF x).2).trans (le_max_left _ _)
  · -- g > C_*: `large_lower` at the cycle length L_c, with Lemma 1.2(iii)
    -- [da:lem:distribution], (1.14) [eq:bulk-bridge]
    push Not at hgs
    have hg1 : 1 ≤ g := le_trans hCst1 hgs.le
    have hout : (W : ℝ) ^ (-(τ / 2)) * (W : ℝ) ^ τ * g ^ 2 < L := by
      rw [hcτ]
      by_contra hcon
      exact hiii ⟨hgs.le, not_lt.mp hcon⟩
    have h8 : 8 ≤ (W : ℝ) ^ ν := by
      have := h2 W hW2
      nlinarith
    have hc2 : 1 ≤ (W : ℝ) ^ (-(τ / 2)) * (W : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_add hWpos, neg_add_cancel, Real.rpow_zero]
    obtain ⟨hlow, hup⟩ := volLc_large (show 3 ≤ W by omega) L hg1 ⟨hτ0, hτ1⟩ ⟨hν0, hν1⟩ h8 hc2
      hout
    have hρ : (W : ℝ) ^ (τ / 2) / Real.log W * g ^ 2 * Real.log W ≤ (volLc W L g ν : ℕ) := by
      have : (W : ℝ) ^ (τ / 2) / Real.log W * g ^ 2 * Real.log W =
          g ^ 2 * (W : ℝ) ^ (τ / 2) := by
        field_simp
      rw [this]
      exact hlow
    have hE' : |E| ≤ 2 - κ ^ 2 / 64 := by
      have h128 : 8 / (κ / 4) ^ 2 ≤ g := by
        have : 8 / (κ / 4) ^ 2 = 128 / κ ^ 2 := by field_simp; norm_num
        rw [this]
        exact hCst128.trans hgs.le
      have := bulk_window_explicit (κ / 4) ⟨by linarith, by linarith⟩ g hg (Or.inr h128) E hF
      have hsq : (κ / 4) ^ 2 / 4 = κ ^ 2 / 64 := by ring
      linarith
    exact ((hL W hWL g (hCstL.trans hgs.le) (volLc W L g ν) hρ hup E hE' x).2).trans
      (le_max_right _ _)

/-- (E2) lower half of (1.17) [eq:main]; `x / 0 = 0` is real division. -/
theorem lower_ratio_endpoint (κ : ℝ) (hκ : 0 < κ ∧ κ < 1 / 2) :
    ∃ L₀ : ℕ, ∀ L₁ : ℕ, L₀ ≤ L₁ → ∀ D τ : ℝ, 0 < D → 0 < τ →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        1 - (W : ℝ) ^ (-D) ≤
          ∫ ω, (goodCount W L (Hmat g W L ω) (bulkSet g κ L₁ L)
                  ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ) /
                (countIn (Hmat g W L ω) (bulkSet g κ L₁ L) : ℝ) ∂(μ W L) :=
  lowerRatio_of_count_rough κ hκ
    (fun D τ hD hτ L₀ => lower_count_endpoint κ D τ hκ hD hτ L₀)
    (rough_density_law (κ / 2) (by linarith [hκ.1]))

/-- (E3) lower half of (1.18) [eq:simultaneous], every fixed threshold `L₀`. -/
theorem lower_simultaneous_endpoint (BL D τ κ : ℝ) (hBL : 0 < BL) (hD : 0 < D) (hτ : 0 < τ)
    (hκ : 0 < κ ∧ κ < 1 / 2) (L₀ : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → (L : ℝ) ≤ (W : ℝ) ^ BL → ∀ g : ℝ, 0 ≤ g →
      μ W L {ω | 0 < badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ (-τ) * ellStar W L g)} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) :=
  simultaneous_of_count BL D τ κ hBL hD hτ L₀
    (fun D' τ' hD' hτ' => lower_count_endpoint κ D' τ' hκ hD' hτ' L₀)

/-- (E4) Lemma 1.3 [lem:rough-density], (1.15) [eq:rough-counting]. -/
theorem rough_density_endpoint (δ : ℝ) (hδ : 0 < δ) :
    ∃ Wδ Lδ : ℕ, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ W : ℕ, Wδ ≤ W → ∀ L : ℕ, max Lδ 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        μ W L {ω | ∃ x : ℝ, δ < |empCDF (Hmat g W L ω) x - Fdist g x|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (W : ℝ) ^ 2 * L)) :=
  rough_density_law δ hδ

/-- (E2) from (E1) and (E4) by the endpoint algebra. -/
example (κ : ℝ) (hκ : 0 < κ ∧ κ < 1 / 2) :
    ∃ L₀ : ℕ, ∀ L₁ : ℕ, L₀ ≤ L₁ → ∀ D τ : ℝ, 0 < D → 0 < τ →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        1 - (W : ℝ) ^ (-D) ≤
          ∫ ω, (goodCount W L (Hmat g W L ω) (bulkSet g κ L₁ L)
                  ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ) /
                (countIn (Hmat g W L ω) (bulkSet g κ L₁ L) : ℝ) ∂(μ W L) :=
  lowerRatio_of_count_rough κ hκ
    (fun D τ hD hτ L₀ => lower_count_endpoint κ D τ hκ hD hτ L₀)
    (rough_density_endpoint (κ / 2) (by linarith [hκ.1]))

/-- (E3) from (E1) by Markov's inequality. -/
example (BL D τ κ : ℝ) (hBL : 0 < BL) (hD : 0 < D) (hτ : 0 < τ) (hκ : 0 < κ ∧ κ < 1 / 2)
    (L₀ : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → (L : ℝ) ≤ (W : ℝ) ^ BL → ∀ g : ℝ, 0 ≤ g →
      μ W L {ω | 0 < badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ (-τ) * ellStar W L g)} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) :=
  simultaneous_of_count BL D τ κ hBL hD hτ L₀
    (fun D' τ' hD' hτ' => lower_count_endpoint κ D' τ' hκ hD' hτ' L₀)

/-- (E4) is `rough_density_law`. -/
example (δ : ℝ) (hδ : 0 < δ) :
    ∃ Wδ Lδ : ℕ, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ W : ℕ, Wδ ≤ W → ∀ L : ℕ, max Lδ 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        μ W L {ω | ∃ x : ℝ, δ < |empCDF (Hmat g W L ω) x - Fdist g x|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (W : ℝ) ^ 2 * L)) :=
  rough_density_law δ hδ


/-- The parameter hypotheses of (E1)–(E4): `κ = 1/4`, `D = 1`, `τ = 1/2`, `L₀ = 5`, `B_L = 2`,
`δ = κ/2`, evaluated at `W = max W₀ 3`, `L = 5`, `g = 1`. -/
example : ∃ W : ℕ, 3 ≤ W ∧
    ((W : ℝ) * (5 : ℕ))⁻¹ * ∫ ω, (badCount W 5 (Hmat 1 W 5 ω) (bulkSet 1 (1 / 4) 5 5)
      ((W : ℝ) ^ (-(1 / 2 : ℝ)) * ellStar W 5 1) : ℝ) ∂(μ W 5) ≤ (W : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨W₀, hW₀⟩ := lower_count_endpoint (1 / 4) 1 (1 / 2) ⟨by norm_num, by norm_num⟩
    (by norm_num) ⟨by norm_num, by norm_num⟩ 5
  exact ⟨max W₀ 3, le_max_right _ _, (hW₀ _ (le_max_left _ _) 5 (by norm_num) 1 (by norm_num)).2⟩

example : ∃ L₀ : ℕ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
    1 - (W : ℝ) ^ (-(1 : ℝ)) ≤
      ∫ ω, (goodCount W 5 (Hmat 1 W 5 ω) (bulkSet 1 (1 / 4) (max L₀ 5) 5)
          ((W : ℝ) ^ (-(1 / 2 : ℝ)) * ellStar W 5 1) : ℝ) /
        (countIn (Hmat 1 W 5 ω) (bulkSet 1 (1 / 4) (max L₀ 5) 5) : ℝ) ∂(μ W 5) := by
  obtain ⟨L₀, hL₀⟩ := lower_ratio_endpoint (1 / 4) ⟨by norm_num, by norm_num⟩
  obtain ⟨W₀, hW₀⟩ := hL₀ (max L₀ 5) (le_max_left _ _) 1 (1 / 2) (by norm_num) (by norm_num)
  exact ⟨L₀, W₀, fun W hW => hW₀ W hW 5 (by norm_num) 1 (by norm_num)⟩

example : ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → (5 : ℝ) ≤ (W : ℝ) ^ (2 : ℝ) →
    μ W 5 {ω | 0 < badCount W 5 (Hmat 1 W 5 ω) (bulkSet 1 (1 / 4) 5 5)
      ((W : ℝ) ^ (-(1 / 2 : ℝ)) * ellStar W 5 1)} ≤ ENNReal.ofReal ((W : ℝ) ^ (-(1 : ℝ))) := by
  obtain ⟨W₀, hW₀⟩ := lower_simultaneous_endpoint 2 1 (1 / 2) (1 / 4) (by norm_num) (by norm_num)
    (by norm_num) ⟨by norm_num, by norm_num⟩ 5
  exact ⟨W₀, fun W hW hL => hW₀ W hW 5 (by norm_num) (by exact_mod_cast hL) 1 (by norm_num)⟩

example : ∃ Wδ Lδ : ℕ, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ W : ℕ, Wδ ≤ W → μ W (max Lδ 3) {ω | ∃ x : ℝ,
      (1 / 4 : ℝ) / 2 < |empCDF (Hmat 1 W (max Lδ 3) ω) x - Fdist 1 x|} ≤
        ENNReal.ofReal (C * Real.exp (-c * (W : ℝ) ^ 2 * (max Lδ 3 : ℕ))) := by
  obtain ⟨Wδ, Lδ, C, c, hC, hc, h⟩ := rough_density_endpoint ((1 / 4 : ℝ) / 2) (by norm_num)
  exact ⟨Wδ, Lδ, C, c, hC, hc, fun W hW => h W hW (max Lδ 3) le_rfl 1 (by norm_num)⟩

end LSBA
