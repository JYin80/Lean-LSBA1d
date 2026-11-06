import LSBA.Final.Moments
import LSBA.Final.Terminal
import LSBA.Prop.Objects

/-!
# Terminal matching at large coupling

The matching in law `H_{t_*}(g̃) = H` with `g̃ = √t_* g`, `t_* = 1 − δ_*` (Lemma A.18
[fo:lem:matching], (A.75) [fo:eq:large-matching]), the characteristic point at the anchor of Lemma
5.13 [fo:lem:terminal-deterministic](b), and the end budget used in the proof of Theorem 2.5
[uvu:thm:terminal].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

private lemma matchLarge_gammaG_of_one_le {x : ℝ} (hx : 1 ≤ x) : gammaG x = (x ^ 2)⁻¹ := by
  unfold gammaG; rw [max_eq_right hx]

private lemma matchLarge_Ag_of_one_le {x : ℝ} (hx : 1 ≤ x) (L : ℕ) :
    Ag x L = cycleAdj L := by
  unfold Ag
  rw [max_eq_right hx, div_self (by linarith)]
  simp

/-- Lemma A.18 [fo:lem:matching]: for `g ≥ C_κ`, `L ≥ C_κ g²`, `1/2 ≤ t < 1` and `g̃ = t^{1/2} g`,
(A.75) [fo:eq:large-matching] `H_t(g̃) = H` for every sample, and (A.76) [fo:eq:large-match-domain]:
an anchor `|E₀| ≤ 2 - 3κ/4` with `Re z_t(g̃, E₀) = E` and
`c(1-t)g^{-2} ≤ Im z_t(g̃, E₀) ≤ C(1-t)g^{-2}`. -/
theorem terminal_match_large (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ c C : ℝ, 1 < Cκ ∧ 0 < c ∧ 0 < C ∧ ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, Cκ * g ^ 2 ≤ L →
      ∀ t : ℝ, 1 / 2 ≤ t → t < 1 → ∀ E : ℝ, |E| ≤ 2 - κ →
      ∃ E₀ : ℝ, |E₀| ≤ 2 - 3 * κ / 4 ∧
        IsDysonRootV (hopB (Real.sqrt t * g)) (gammaG (Real.sqrt t * g)) L E₀
          (mRoot (Real.sqrt t * g) L E₀) ∧
        c ≤ (mRoot (Real.sqrt t * g) L E₀).im ∧ ‖mRoot (Real.sqrt t * g) L E₀‖ ≤ C ∧
        (zChar (Real.sqrt t * g) E₀ (mRoot (Real.sqrt t * g) L E₀) t).re = E ∧
        c * (1 - t) / g ^ 2 ≤ (zChar (Real.sqrt t * g) E₀ (mRoot (Real.sqrt t * g) L E₀) t).im ∧
        (zChar (Real.sqrt t * g) E₀ (mRoot (Real.sqrt t * g) L E₀) t).im ≤ C * (1 - t) / g ^ 2 ∧
        ∀ (W : ℕ) (ω : Ω W L), flowH (Real.sqrt t * g) W L t ω = Hmat g W L ω := by
  obtain ⟨C1, c1, C2, hC1, hc1, hC2, H⟩ := terminal_large_anchor κ hκ hκ2
  refine ⟨max (Real.sqrt 2 * C1) 2, c1, 2 * C2, lt_max_of_lt_right (by norm_num), hc1,
    by linarith, ?_⟩
  intro g hg L hL t ht1 ht2 E hE
  have hg2 : 2 ≤ g := (le_max_right _ _).trans hg
  have hgs : Real.sqrt 2 * C1 ≤ g := (le_max_left _ _).trans hg
  have hg1 : 1 ≤ g := by linarith
  have ht0 : 0 < t := by linarith
  have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hst0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  set s : ℝ := Real.sqrt t * g with hs
  have hs0 : 0 ≤ s := by positivity
  have hs2 : s ^ 2 = t * g ^ 2 := by rw [hs, mul_pow, hst]
  have hC1pos : 0 < C1 := by linarith
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hC1s : C1 ≤ s := by
    by_contra hlt
    have hlt := not_le.1 hlt
    have h1 : s ^ 2 < C1 ^ 2 := by nlinarith
    have h2 : (Real.sqrt 2 * C1) ^ 2 ≤ g ^ 2 := by
      have : 0 ≤ Real.sqrt 2 * C1 := by positivity
      nlinarith
    have h3 : 2 * C1 ^ 2 ≤ g ^ 2 := by rw [mul_pow, hsq2] at h2; exact h2
    nlinarith [sq_nonneg g]
  have hs1 : 1 ≤ s := by linarith
  have hLs : C1 * s ^ 2 ≤ L := by
    have hC1m : C1 ≤ max (Real.sqrt 2 * C1) 2 := by
      have : 1 ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)
      exact le_trans (by nlinarith) (le_max_left _ _)
    have h1 : C1 * s ^ 2 ≤ max (Real.sqrt 2 * C1) 2 * g ^ 2 := by
      rw [hs2]
      have : t * g ^ 2 ≤ g ^ 2 := by nlinarith [sq_nonneg g]
      have hg2' : 0 ≤ g ^ 2 := sq_nonneg g
      nlinarith [mul_le_mul hC1m this (by positivity) (by positivity)]
    exact h1.trans hL
  obtain ⟨E₀, h0, hEeq, hroot, hc, hC⟩ := H s hC1s L hLs E hE (1 - t) (by linarith) (by linarith)
  have hγ : gammaG s = (s ^ 2)⁻¹ := matchLarge_gammaG_of_one_le hs1
  have hb : hopB s = 1 := by
    unfold hopB; rw [max_eq_right hs1, div_self (by linarith)]
  have hre : (zChar s E₀ (mRoot s L E₀) t).re = E₀ + (1 - t) * (s ^ 2)⁻¹ * (mRoot s L E₀).re := by
    have : (zChar s E₀ (mRoot s L E₀) t).re = E₀ + (1 - t) * gammaG s * (mRoot s L E₀).re := by
      simp [zChar]
    rw [this, hγ]
  have him : (zChar s E₀ (mRoot s L E₀) t).im = (1 - t) * (s ^ 2)⁻¹ * (mRoot s L E₀).im := by
    have : (zChar s E₀ (mRoot s L E₀) t).im = (1 - t) * gammaG s * (mRoot s L E₀).im := by
      simp [zChar]
    rw [this, hγ]
  have hg2p : 0 < g ^ 2 := by positivity
  have hkey : (1 - t) * (t * g ^ 2)⁻¹ * (mRoot s L E₀).im =
      ((1 - t) / g ^ 2) * ((mRoot s L E₀).im / t) := by
    field_simp
  have ha : 0 ≤ (1 - t) / g ^ 2 := div_nonneg (by linarith) hg2p.le
  refine ⟨E₀, h0, hroot, hc, hC.trans (by linarith), ?_, ?_, ?_, ?_⟩
  · rw [hre]; exact hEeq.symm
  · rw [him, hs2, hkey]
    have h1 : c1 ≤ (mRoot s L E₀).im / t := by
      rw [le_div_iff₀ ht0]; nlinarith
    calc c1 * (1 - t) / g ^ 2 = ((1 - t) / g ^ 2) * c1 := by ring
      _ ≤ ((1 - t) / g ^ 2) * ((mRoot s L E₀).im / t) := mul_le_mul_of_nonneg_left h1 ha
  · rw [him, hs2, hkey]
    have himle : (mRoot s L E₀).im ≤ C2 := (Complex.im_le_norm _).trans hC
    have h1 : (mRoot s L E₀).im / t ≤ 2 * C2 := by
      rw [div_le_iff₀ ht0]; nlinarith
    calc ((1 - t) / g ^ 2) * ((mRoot s L E₀).im / t) ≤ ((1 - t) / g ^ 2) * (2 * C2) :=
          mul_le_mul_of_nonneg_left h1 ha
      _ = 2 * C2 * (1 - t) / g ^ 2 := by ring
  · intro W ω
    have hA : Ag s L = ((1 : ℝ) : ℂ) • Ag g L := by
      rw [matchLarge_Ag_of_one_le hs1, matchLarge_Ag_of_one_le hg1]; simp
    have hγ' : t * gammaG s = (1 : ℝ) ^ 2 * (1 * gammaG g) := by
      rw [hγ, matchLarge_gammaG_of_one_le hg1, hs2]
      field_simp
    have := flowH_scaling g s W L (u := 1) (u' := t) (c := 1) zero_le_one zero_le_one hA hγ' ω
    rw [this, flowH_one]
    simp

/-- `ζ_t(g̃)` at `t = 1 - δ`, `g̃² = t g² ≥ 1`: `ζ = g̃² / (W δ ℓ)` with `ℓ = min{L, 1 + g̃²/√δ}`
((5.18) [fo:eq:scale]). -/
private lemma matchLarge_zeta {δ g : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hg : 2 ≤ g) (W L : ℕ) :
    zetaProp (Real.sqrt (1 - δ) * g) W L (1 - δ) =
      ((W : ℝ) * min (L : ℝ) (1 + (1 - δ) * g ^ 2 / Real.sqrt δ) * δ *
        ((1 - δ) * g ^ 2)⁻¹)⁻¹ := by
  have ht0 : 0 < 1 - δ := by linarith
  set s : ℝ := Real.sqrt (1 - δ) * g with hs
  have hs2 : s ^ 2 = (1 - δ) * g ^ 2 := by
    rw [hs, mul_pow, Real.sq_sqrt ht0.le]
  have hs0 : 0 ≤ s := by positivity
  have hs1 : 1 ≤ s := by
    by_contra h
    have h := not_le.1 h
    nlinarith [sq_nonneg g]
  have hγ : gammaG s = (s ^ 2)⁻¹ := matchLarge_gammaG_of_one_le hs1
  have hsp : 0 < s := by linarith
  have hx : s / Real.sqrt ((s ^ 2)⁻¹ * δ) = s ^ 2 / Real.sqrt δ := by
    have h1 : (s ^ 2)⁻¹ * δ = (Real.sqrt δ / s) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hδ.le]; field_simp
    have hδp : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
    rw [h1, Real.sqrt_sq (by positivity)]
    field_simp
  unfold zetaProp ellProp
  rw [sub_sub_cancel, hγ, hx, hs2]

private lemma matchLarge_aux {W s2 r : ℝ} (hW : 0 < W) (hs : 0 < s2) (hr : 0 < r) :
    W * r ≤ W * (1 + s2 / r) * (r * r) * s2⁻¹ := by
  have e : W * (1 + s2 / r) * (r * r) * s2⁻¹ = W * r + W * (r * r) * s2⁻¹ := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ W * (r * r) * s2⁻¹ := by positivity
  linarith

/-- The end budget in the proof of Theorem 2.5 [uvu:thm:terminal]: with
`δ_* = g² η_L ∈ [W^{ν-2}, W^{ν-1}]`, `t_* = 1 - δ_*` and `g̃ = t_*^{1/2} g`,
`ζ_{t_*}(g̃) ≤ W^{-ν/3}`. -/
theorem endBudget_large (ν : ℝ) (hν : 0 < ν ∧ ν < 1) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, 2 ≤ g → ∀ L : ℕ, g ^ 2 ≤ L →
      (W : ℝ) ^ (ν - 2) ≤ g ^ 2 * etaL W L g ν ∧ g ^ 2 * etaL W L g ν ≤ (W : ℝ) ^ (ν - 1) ∧
      g ^ 2 * etaL W L g ν ≤ 1 / 2 ∧ (W : ℝ) ^ (-3 : ℝ) ≤ g ^ 2 * etaL W L g ν ∧
      zetaProp (Real.sqrt (1 - g ^ 2 * etaL W L g ν) * g) W L (1 - g ^ 2 * etaL W L g ν) ≤
        (W : ℝ) ^ (-(ν / 3)) := by
  obtain ⟨hν0, hν1⟩ := hν
  have hev : ∀ᶠ W : ℕ in atTop, (2 : ℝ) ≤ (W : ℝ) ^ (1 - ν) :=
    ((tendsto_rpow_atTop (by linarith : 0 < 1 - ν)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  obtain ⟨W₁, hW₁⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max W₁ 2, ?_⟩
  intro W hW g hg L hL
  have hW2 : 2 ≤ W := (le_max_right _ _).trans hW
  have hWr : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  have hW0 : 0 < (W : ℝ) := by linarith
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hWpow : (2 : ℝ) ≤ (W : ℝ) ^ (1 - ν) := hW₁ W ((le_max_left _ _).trans hW)
  have hg0 : 0 < g := by linarith
  have hg2 : 4 ≤ g ^ 2 := by nlinarith
  have hg2p : 0 < g ^ 2 := by linarith
  have hLr : g ^ 2 ≤ (L : ℝ) := hL
  have hL0 : 0 < (L : ℝ) := by linarith
  have hscale : ellScale W g = (W : ℝ) ^ 2 * g ^ 2 := by
    unfold ellScale
    exact max_eq_right (by nlinarith)
  have hS1 : ellStar W L g ≤ (W : ℝ) * L := min_le_left _ _
  have hS2 : ellStar W L g ≤ (W : ℝ) ^ 2 * g ^ 2 := hscale ▸ min_le_right _ _
  have hS3 : (W : ℝ) * g ^ 2 ≤ ellStar W L g :=
    le_min (mul_le_mul_of_nonneg_left hLr hW0.le)
      (by rw [hscale]; exact mul_le_mul_of_nonneg_right (by nlinarith) hg2p.le)
  have hS0 : 0 < ellStar W L g := lt_of_lt_of_le (by positivity) hS3
  set S : ℝ := ellStar W L g with hSdef
  set P : ℝ := (W : ℝ) ^ ν with hPdef
  have hP0 : 0 < P := Real.rpow_pos_of_pos hW0 ν
  set δ : ℝ := g ^ 2 * etaL W L g ν with hδdef
  have hη : etaL W L g ν = P / S := rfl
  have hδS : δ * S = g ^ 2 * P := by
    rw [hδdef, hη]; field_simp
  have hδ0 : 0 < δ := by
    by_contra h
    have h := not_lt.1 h
    nlinarith [mul_pos hg2p hP0]
  -- (i) and (ii)
  have hP2 : P ≤ δ * (W : ℝ) ^ 2 := by
    have : g ^ 2 * P ≤ g ^ 2 * (δ * (W : ℝ) ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this hg2p
  have hi : (W : ℝ) ^ (ν - 2) ≤ δ := by
    rw [Real.rpow_sub hW0, Real.rpow_two, div_le_iff₀ (by positivity)]
    exact hP2
  have hii : δ ≤ (W : ℝ) ^ (ν - 1) := by
    rw [Real.rpow_sub hW0, Real.rpow_one, le_div_iff₀ hW0]
    have : g ^ 2 * (δ * W) ≤ g ^ 2 * P := by nlinarith
    exact le_of_mul_le_mul_left this hg2p
  have hiii : δ ≤ 1 / 2 := by
    refine hii.trans ?_
    rw [show ν - 1 = -(1 - ν) by ring, Real.rpow_neg hW0.le]
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hWpow
    linarith
  have hiv : (W : ℝ) ^ (-3 : ℝ) ≤ δ :=
    (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)).trans hi
  refine ⟨hi, hii, hiii, hiv, ?_⟩
  -- (v)
  have hδ1 : δ ≤ 1 / 2 := hiii
  rw [matchLarge_zeta hδ0 hδ1 hg W L]
  have ht0 : 0 < 1 - δ := by linarith
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  set s2 : ℝ := (1 - δ) * g ^ 2 with hs2
  have hs2p : 0 < s2 := by positivity
  have hs2le : s2 ≤ g ^ 2 := by nlinarith
  have hA : (W : ℝ) ^ (ν / 3) ≤ P := by
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hmin : 0 < min (L : ℝ) (1 + s2 / Real.sqrt δ) := lt_min hL0 (by positivity)
  have hlower : (W : ℝ) ^ (ν / 3) ≤
      (W : ℝ) * min (L : ℝ) (1 + s2 / Real.sqrt δ) * δ * s2⁻¹ := by
    rcases min_choice (L : ℝ) (1 + s2 / Real.sqrt δ) with h | h
    · rw [h]
      -- `ℓ = L`
      have h1 : P ≤ (W : ℝ) * L * δ * s2⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hs2p]
        calc P * s2 ≤ P * g ^ 2 := mul_le_mul_of_nonneg_left hs2le hP0.le
          _ = δ * S := by rw [hδS]; ring
          _ ≤ δ * ((W : ℝ) * L) := mul_le_mul_of_nonneg_left hS1 hδ0.le
          _ = (W : ℝ) * L * δ := by ring
      exact hA.trans h1
    · rw [h]
      -- `ℓ = 1 + g̃²/√δ`
      have h1 : (W : ℝ) * Real.sqrt δ ≤ (W : ℝ) * (1 + s2 / Real.sqrt δ) * δ * s2⁻¹ := by
        have := matchLarge_aux hW0 hs2p hsd
        rwa [Real.mul_self_sqrt hδ0.le] at this
      have h2 : (W : ℝ) ^ (ν / 3) ≤ (W : ℝ) * Real.sqrt δ := by
        have hsq : ((W : ℝ) * Real.sqrt δ) ^ 2 = (W : ℝ) ^ 2 * δ := by
          rw [mul_pow, Real.sq_sqrt hδ0.le]
        have hsq2 : ((W : ℝ) ^ (ν / 3)) ^ 2 ≤ P := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
          exact Real.rpow_le_rpow_of_exponent_le hW1 (by push_cast; linarith)
        have hnn : 0 ≤ (W : ℝ) * Real.sqrt δ := by positivity
        exact (pow_le_pow_iff_left₀ (by positivity) hnn (two_ne_zero)).1
          (by rw [hsq]; linarith [hsq2, hP2])
      exact h2.trans h1
  rw [Real.rpow_neg hW0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hW0 _) hlower

end LSBA
