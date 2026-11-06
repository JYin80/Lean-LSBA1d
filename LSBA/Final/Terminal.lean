import LSBA.Dyson.FiniteRegular
import LSBA.Kernel.Large
import LSBA.Main.EndpointAlgebra

/-!
# Deterministic bounds for the terminal comparison

Lemma 5.13 [fo:lem:terminal-deterministic]: (a) at bounded coupling, `F_g(−|E|) ≥ κ` implies
`|E| ≤ C′` and `Im m_{g,L}(E) ≥ c′`, (5.43) [fo:eq:terminal-bounded-regularity]; (b) at large
coupling, an anchor `E₀` with `|E₀| ≤ 2 − 3κ/4` and `E = E₀ + δg⁻² Re m_{g,L}(E₀)`, (5.44)
[fo:eq:terminal-large-anchor], with the root bounds there.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

private lemma terminal_hopB_nonneg {g : ℝ} (hg : 0 ≤ g) : 0 ≤ hopB g :=
  div_nonneg hg (le_trans zero_le_one (le_max_left _ _))

private lemma terminal_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

private lemma terminal_hopB_of_one_le {g : ℝ} (hg : 1 ≤ g) : hopB g = 1 := by
  unfold hopB; rw [max_eq_right hg, div_self (by linarith)]

private lemma terminal_gammaG_of_one_le {g : ℝ} (hg : 1 ≤ g) : gammaG g = (g ^ 2)⁻¹ := by
  unfold gammaG; rw [max_eq_right hg]

/-- Lemma 5.13(a) [fo:lem:terminal-deterministic], (5.43) [fo:eq:terminal-bounded-regularity]: for
`0 ≤ g ≤ C`, `L ≥ L₀` and `F_g(-|E|) ≥ κ`, the anchor `m_{g,L}(E)` solves (5.2)
[fo:eq:dyson-family] with `|E| ≤ C'`, `Im m ≥ c'`, `|m| ≤ max{1, g}`, and `Im m_{g,L}(E + iη) ≥ c'`
for `0 < η ≤ 1`. -/
theorem terminal_bdd_regular (C κ : ℝ) (hC : 0 < C) (hκ : 0 < κ ∧ κ < 1 / 2) :
    ∃ C' c' : ℝ, ∃ L₀ : ℕ, 0 < C' ∧ 0 < c' ∧ 3 ≤ L₀ ∧
      ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, L₀ ≤ L → ∀ E : ℝ, κ ≤ Fdist g (-|E|) →
        |E| ≤ C' ∧ IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E) ∧
        c' ≤ (mRoot g L E).im ∧ ‖mRoot g L E‖ ≤ max 1 g ∧
        ∀ η : ℝ, 0 < η → η ≤ 1 → c' ≤ (mDysonL g L (E + η * Complex.I)).im := by
  obtain ⟨b, c, C₁, L₁, hb, hc, hC₁, H⟩ := finite_regular_quantile C κ hC hκ
  refine ⟨2 * C + 2, c, max L₁ 3, by linarith, hc, le_max_right _ _, ?_⟩
  intro g hg hgC L hL E hE
  have hL1 : L₁ ≤ L := (le_max_left _ _).trans hL
  have hL3 : 3 ≤ L := (le_max_right _ _).trans hL
  obtain ⟨h1, h2, h3, -, h5⟩ := H g hg hgC L hL1 E ⟨E, hE, by simp [hb.le]⟩
  have hroot : IsDysonRootV (hopB g) (gammaG g) L E (mDysonLBdry g L E) :=
    ⟨lt_of_lt_of_le hc h2, h3⟩
  have heq : mRoot g L E = mDysonLBdry g L E :=
    (mRootV_spec (hopB g) (gammaG g) (terminal_hopB_nonneg hg) (terminal_gammaG_pos g) L hL3
      (E : ℂ) (by simp)).2 _ hroot
  rw [heq]
  exact ⟨h1, hroot, h2, (mDysonLBdry_norm_le g hg L (by omega) E).1,
    fun η h0 h1 => (h5 η h0 h1).1⟩

/-- Lemma 5.13(b) [fo:lem:terminal-deterministic], (5.44) [fo:eq:terminal-large-anchor]: for
`g ≥ C_κ`, `L ≥ C_κ g²`, `|E| ≤ 2 - κ` and `0 ≤ δ ≤ 1` there is an anchor
`|E₀| ≤ 2 - 3κ/4` with `E = E₀ + δ g^{-2} Re m_{g,L}(E₀)` and
`c ≤ Im m_{g,L}(E₀) ≤ |m_{g,L}(E₀)| ≤ C`. -/
theorem terminal_large_anchor (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ c C : ℝ, 1 < Cκ ∧ 0 < c ∧ 0 < C ∧ ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, Cκ * g ^ 2 ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        ∃ E₀ : ℝ, |E₀| ≤ 2 - 3 * κ / 4 ∧ E = E₀ + δ * (g ^ 2)⁻¹ * (mRoot g L E₀).re ∧
          IsDysonRootV (hopB g) (gammaG g) L E₀ (mRoot g L E₀) ∧
          c ≤ (mRoot g L E₀).im ∧ ‖mRoot g L E₀‖ ≤ C := by
  have hκ' : 0 < 3 * κ / 4 := by linarith
  have hκ'2 : 3 * κ / 4 < 2 := by linarith
  obtain ⟨C₁κ, R₁, c₁, C₁, hC₁κ, hR₁, hc₁, hC₁, H₁⟩ := large_periodic_comparison _ hκ' hκ'2
  obtain ⟨C₂κ, R₂, hC₂κ, hR₂, H₂⟩ := anchor_derivative _ hκ' hκ'2
  set s : ℝ := Real.sqrt (4 * C₁ / κ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 4 * C₁ / κ := Real.sq_sqrt (by positivity)
  refine ⟨C₁κ + C₂κ + R₁ + R₂ + 3 + s, C₁⁻¹, C₁, by linarith, inv_pos.2 hC₁, hC₁, ?_⟩
  intro g hg L hL E hE δ hδ0 hδ1
  have hg1 : 1 ≤ g := by linarith
  have hg0 : 0 < g := by linarith
  have hgsq : 1 ≤ g ^ 2 := one_le_pow₀ hg1
  have hb : hopB g = 1 := terminal_hopB_of_one_le hg1
  have hγ : gammaG g = (g ^ 2)⁻¹ := terminal_gammaG_of_one_le hg1
  have hL3 : (3 : ℝ) ≤ L := by nlinarith
  have hL3' : 3 ≤ L := by exact_mod_cast hL3
  have hLR1 : R₁ * g ^ 2 ≤ L := by nlinarith
  have hLR2 : R₂ / (g ^ 2)⁻¹ ≤ L := by
    rw [div_inv_eq_mul]; nlinarith
  have hgC₁ : C₁κ ≤ g := by linarith
  have hgC₂ : C₂κ ≤ ((g ^ 2)⁻¹) ^ (-(1 : ℝ) / 2) := by
    have : ((g ^ 2)⁻¹) ^ (-(1 : ℝ) / 2) = g := by
      rw [show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg (by positivity),
        Real.inv_rpow (by positivity), inv_inv, ← Real.sqrt_eq_rpow, Real.sqrt_sq hg0.le]
    rw [this]; linarith
  have hgs : s ≤ g := by linarith
  have hctrl : C₁ * (g ^ 2)⁻¹ ≤ κ / 4 := by
    have h1 : s ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ hs0 hgs 2
    rw [hs2, div_le_iff₀ hκ] at h1
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith
  -- the root at every energy of the cover
  have hcmp : ∀ e : ℝ, |e| ≤ 2 - 3 * κ / 4 →
      IsDysonRootV (hopB g) (gammaG g) L e (mRoot g L e) ∧ C₁⁻¹ ≤ (mRoot g L e).im ∧
        ‖mRoot g L e‖ ≤ C₁ := by
    intro e he
    obtain ⟨m, mInf, hm, -, him, hnorm, -⟩ := H₁ g hgC₁ L hLR1 e he
    have heq : mRoot g L e = m :=
      (mRootV_spec (hopB g) (gammaG g) (terminal_hopB_nonneg hg0.le) (terminal_gammaG_pos g) L
        hL3' (e : ℂ) (by simp)).2 _ hm
    rw [heq]
    exact ⟨hm, him, hnorm⟩
  -- continuity of the real part of the root on the cover
  have hcont : ∀ e : ℝ, |e| ≤ 2 - 3 * κ / 4 → ContinuousAt (fun e' : ℝ => mRoot g L e') e := by
    intro e he
    obtain ⟨-, hd, -⟩ := H₂ (g ^ 2)⁻¹ (by positivity) hgC₂ L hLR2 e he
    have hfun : (fun e' : ℝ => mRoot g L e') = fun e' : ℝ => mRootV 1 (g ^ 2)⁻¹ L e' := by
      funext e'; simp only [mRoot, hb, hγ]
    rw [hfun]
    exact hd.continuousAt
  set a : ℝ := 2 - 3 * κ / 4 with ha
  have ha0 : 0 ≤ a := by linarith
  set φ : ℝ → ℝ := fun e => e + δ * (g ^ 2)⁻¹ * (mRoot g L e).re with hφ
  have hφcont : ContinuousOn φ (Set.Icc (-a) a) := by
    intro e he
    have he' : |e| ≤ a := abs_le.2 ⟨he.1, he.2⟩
    refine ContinuousAt.continuousWithinAt ?_
    exact continuousAt_id.add (continuousAt_const.mul
      (Complex.continuous_re.continuousAt.comp (hcont e he')))
  have hdisp : ∀ e : ℝ, |e| ≤ a → |φ e - e| ≤ κ / 4 := by
    intro e he
    have h1 : φ e - e = δ * (g ^ 2)⁻¹ * (mRoot g L e).re := by simp only [hφ]; ring
    rw [h1, abs_mul, abs_mul, abs_of_nonneg hδ0, abs_of_nonneg (by positivity)]
    have h2 : |(mRoot g L e).re| ≤ C₁ := (Complex.abs_re_le_norm _).trans (hcmp e he).2.2
    have h3 : 0 ≤ (g ^ 2)⁻¹ := by positivity
    calc δ * (g ^ 2)⁻¹ * |(mRoot g L e).re| ≤ 1 * (g ^ 2)⁻¹ * C₁ := by gcongr
      _ = C₁ * (g ^ 2)⁻¹ := by ring
      _ ≤ κ / 4 := hctrl
  have hlo : φ (-a) ≤ E := by
    have h1 := (abs_le.1 (hdisp (-a) (by rw [abs_neg, abs_of_nonneg ha0]))).2
    have h2 := (abs_le.1 hE).1
    linarith
  have hhi : E ≤ φ a := by
    have h1 := (abs_le.1 (hdisp a (by rw [abs_of_nonneg ha0]))).1
    have h2 := (abs_le.1 hE).2
    linarith
  obtain ⟨E₀, hE₀, hφE⟩ := intermediate_value_Icc (by linarith : -a ≤ a) hφcont ⟨hlo, hhi⟩
  have hE₀' : |E₀| ≤ a := abs_le.2 ⟨hE₀.1, hE₀.2⟩
  obtain ⟨hroot, him, hnorm⟩ := hcmp E₀ hE₀'
  exact ⟨E₀, hE₀', by simpa only [hφ] using hφE.symm, hroot, him, hnorm⟩

end LSBA
