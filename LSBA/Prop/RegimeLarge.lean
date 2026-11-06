import LSBA.Prop.Regime
import LSBA.Kernel.Large
import LSBA.Primitive.Large

/-!
# The large-coupling regime

The base family of Theorem 5.12 [gc:thm:common] (b) at large coupling (`g ≥ C_κ`, `|E| ≤ 2 − 3κ/4`,
`ρ g² log W ≤ L ≤ C_V g² W²`, with a rate `ρ → ∞`), and the existence of a regime on its reach
(Lemma 5.2 [fo:lem:deterministic](b) and the large-coupling estimates of Section 6
[sec:deterministic-inputs]).
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The large-coupling base family: `g ≥ C_κ`, `|E| ≤ 2 - 3κ/4` ((5.40)(b)
[gc:eq:initial-parameters]), `ρ(W) g² log W ≤ L ≤ C_V g² W²`, and a time in `[1/2, 1 - W^{-3}]`. -/
def baseLarge (κ Cκ CV : ℝ) (ρ : ℕ → ℝ) (W : ℕ) : Set FlowPt :=
  {p | Cκ ≤ p.g ∧ |p.E| ≤ 2 - 3 * κ / 4 ∧ ρ W * p.g ^ 2 * Real.log W ≤ p.L ∧
    (p.L : ℝ) ≤ CV * p.g ^ 2 * (W : ℝ) ^ 2 ∧ 1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u}

/-- `W ≥ 1` makes `W^{-3}` positive. -/
private lemma rl_rpow_pos {W : ℕ} (hW : 1 ≤ W) : 0 < (W : ℝ) ^ (-3 : ℝ) :=
  Real.rpow_pos_of_pos (by exact_mod_cast hW) _

/-- `1 ≤ log W` for `W ≥ 3`. -/
private lemma rl_one_le_log {W : ℕ} (hW : 3 ≤ W) : 1 ≤ Real.log W := by
  have h3 : (3 : ℝ) ≤ W := by exact_mod_cast hW
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- Volume at a point below the base coupling: `K g² log W ≤ L` once `K ≤ ρ(W)`. -/
private lemma rl_vol {W : ℕ} {ρW g₀ gg K : ℝ} {L : ℕ} (hW : 3 ≤ W) (hK : 0 ≤ K) (hKρ : K ≤ ρW)
    (hg0 : 0 ≤ gg) (hgg : gg ≤ g₀) (hL : ρW * g₀ ^ 2 * Real.log W ≤ L) :
    K * gg ^ 2 * Real.log W ≤ L := by
  have hlog : 0 ≤ Real.log W := (zero_le_one.trans (rl_one_le_log hW))
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hlog) hL
  exact mul_le_mul hKρ (pow_le_pow_left₀ hg0 hgg 2) (sq_nonneg _) (hK.trans hKρ)

/-- Dropping the factor `log W ≥ 1`: `K g² ≤ L` from `K g² log W ≤ L`. -/
private lemma rl_vol1 {W : ℕ} {g K : ℝ} {L : ℕ} (hW : 3 ≤ W) (hK : 0 ≤ K)
    (h : K * g ^ 2 * Real.log W ≤ L) : K * g ^ 2 ≤ L :=
  le_trans (le_mul_of_one_le_right (by positivity) (rl_one_le_log hW)) h

/-- `γ_g = g⁻²` for `g ≥ 1`. -/
private lemma rl_gamma {g : ℝ} (hg : 1 ≤ g) : gammaG g = (g ^ 2)⁻¹ := by
  simp [gammaG, max_eq_right hg]

/-- `ℓ_t > 0`. -/
private lemma rl_ell_pos {g t : ℝ} {L : ℕ} (hg : 0 ≤ g) (hL : 1 ≤ L) : 0 < ellProp g L t := by
  unfold ellProp
  exact lt_min (by exact_mod_cast hL) (by positivity)

/-- `ℓ_t ≥ g²` for `g ≥ 1`, `0 ≤ t < 1` and `L ≥ g²`. -/
private lemma rl_ell_ge {g t : ℝ} {L : ℕ} (hg : 1 ≤ g) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hL : g ^ 2 ≤ L) : g ^ 2 ≤ ellProp g L t := by
  have hg0 : 0 < g := by linarith
  have h1t : 0 < 1 - t := by linarith
  unfold ellProp
  refine le_min hL ?_
  have hx : 0 < gammaG g * (1 - t) := by rw [rl_gamma hg]; positivity
  have hs : 0 < Real.sqrt (gammaG g * (1 - t)) := Real.sqrt_pos.mpr hx
  have hs1 : Real.sqrt (gammaG g * (1 - t)) ≤ 1 / g := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [rl_gamma hg, div_pow, one_pow]
    have : (g ^ 2)⁻¹ * (1 - t) ≤ (g ^ 2)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    simpa using this
  calc g ^ 2 = g / (1 / g) := by field_simp
    _ ≤ g / Real.sqrt (gammaG g * (1 - t)) := div_le_div_of_nonneg_left hg0.le hs hs1
    _ ≤ 1 + g / Real.sqrt (gammaG g * (1 - t)) := by linarith

/-- `ζ_t ≥ 0` for `g ≥ 1`, `t < 1`, `L ≥ 1`. -/
private lemma rl_zeta_nonneg {g t : ℝ} {W L : ℕ} (hg : 1 ≤ g) (ht : t < 1) (hL : 1 ≤ L) :
    0 ≤ zetaProp g W L t := by
  unfold zetaProp
  refine inv_nonneg.mpr ?_
  have h1 := rl_ell_pos (g := g) (t := t) (by linarith) hL
  have h2 : 0 < 1 - t := by linarith
  have h3 : 0 < gammaG g := by rw [rl_gamma hg]; positivity
  positivity

/-- The polynomial budget (6.6) [fo:eq:spatial-sum-budget] at a point with `g ≥ 1`, `L ≥ g²` and
`L ≤ 4 C_V g² W²`, for `W ≥ 8 C_V`. -/
private lemma rl_budget {CV Cc : ℝ} {W : ℕ} {g u : ℝ} {L : ℕ} (hW3 : 3 ≤ W) (hW8 : 8 * CV ≤ W)
    (hCc3 : 3 ≤ Cc) (hg1 : 1 ≤ g) (hu : 1 / 2 ≤ u) (hWu : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - u)
    (hLg : g ^ 2 ≤ L) (hLhi : (L : ℝ) ≤ 4 * CV * g ^ 2 * (W : ℝ) ^ 2) :
    gammaG g * L + L / ellProp g L u ≤ (W : ℝ) ^ Cc := by
  have hg0 : 0 < g := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have hu1 : u < 1 := by have := rl_rpow_pos (W := W) (by omega); linarith
  have hell : g ^ 2 ≤ ellProp g L u := rl_ell_ge hg1 (by linarith) hu1 hLg
  have hLge : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hLg' : (L : ℝ) / g ^ 2 ≤ 4 * CV * (W : ℝ) ^ 2 := by
    rw [div_le_iff₀ hg2]; linarith
  have h1 : gammaG g * L ≤ 4 * CV * (W : ℝ) ^ 2 := by
    rw [rl_gamma hg1, inv_mul_eq_div]; exact hLg'
  have h2 : (L : ℝ) / ellProp g L u ≤ 4 * CV * (W : ℝ) ^ 2 :=
    (div_le_div_of_nonneg_left hLge hg2 hell).trans hLg'
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (show 1 ≤ W by omega)
  have hW8' : 8 * CV * (W : ℝ) ^ 2 ≤ (W : ℝ) ^ 3 := by
    have : 0 ≤ (W : ℝ) ^ 2 := sq_nonneg _
    calc 8 * CV * (W : ℝ) ^ 2 ≤ (W : ℝ) * (W : ℝ) ^ 2 := by gcongr
      _ = (W : ℝ) ^ 3 := by ring
  calc gammaG g * L + L / ellProp g L u ≤ 8 * CV * (W : ℝ) ^ 2 := by linarith
    _ ≤ (W : ℝ) ^ 3 := hW8'
    _ = (W : ℝ) ^ (3 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
    _ ≤ (W : ℝ) ^ Cc := Real.rpow_le_rpow_of_exponent_le hW1 hCc3

/-- At a Dyson root the real part of `m` is an entry of `M_B`, (5.3) [fo:eq:characteristic]: if
the entries are bounded by `C`, then `|Re m| ≤ C`. -/
private lemma rl_mre {g E C : ℝ} {L : ℕ} (hL : 1 ≤ L) (hγ : 0 < gammaG g)
    (hroot : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E))
    (hM : ∀ a b, ‖dysonMat (hopB g) (gammaG g) L E (mRoot g L E) a b‖ ≤ C) :
    |(mRoot g L E).re| ≤ C := by
  have hwim : 0 < ((E : ℂ) + (gammaG g : ℂ) * mRoot g L E).im := by
    have := hroot.1
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add,
      zero_mul]
    positivity
  have hd := dysonMat_diag (hopB g) (gammaG g) L hL (E : ℂ) (mRoot g L E) hwim ⟨0, hL⟩
  rw [← hroot.2] at hd
  calc |(mRoot g L E).re| ≤ ‖mRoot g L E‖ := Complex.abs_re_le_norm _
    _ = ‖dysonMat (hopB g) (gammaG g) L E (mRoot g L E) ⟨0, hL⟩ ⟨0, hL⟩‖ := by rw [hd]
    _ ≤ C := hM _ _

/-- The abscissa `x = Re z_u` of the comparison segment stays in `|x| ≤ 2 - κ/4`, (6.12)
[gc:eq:positive-stability], when `|E| ≤ 2 - κ/2`, `|Re m| ≤ C_s` and `g ≥ 2 C_s/κ`. -/
private lemma rl_xmargin {κ Cs g E u : ℝ} {m : ℂ} (hκ : 0 < κ) (hg : 1 ≤ g) (hCs : 2 * Cs / κ ≤ g)
    (hu : 1 / 2 ≤ u) (hu1 : u < 1) (hE : |E| ≤ 2 - κ / 2) (hm : |m.re| ≤ Cs) :
    |(zChar g E m u).re| ≤ 2 - κ / 2 / 2 := by
  have hx : (zChar g E m u).re = E + (1 - u) * gammaG g * m.re := by simp [zChar]
  have hγ : gammaG g = (g ^ 2)⁻¹ := rl_gamma hg
  have hg0 : 0 < g := by linarith
  have hCs' : Cs ≤ κ / 2 * g := by
    rw [div_le_iff₀ hκ] at hCs; linarith
  have hgg : g ≤ g ^ 2 := by nlinarith
  have h1 : (1 - u) * gammaG g * |m.re| ≤ κ / 4 := by
    rw [hγ]
    have h2 : |m.re| ≤ κ / 2 * g ^ 2 := hm.trans (hCs'.trans (by gcongr))
    have h3 : (1 - u) * (g ^ 2)⁻¹ * |m.re| ≤ (1 / 2) * (g ^ 2)⁻¹ * (κ / 2 * g ^ 2) := by
      gcongr
      linarith
    refine h3.trans (le_of_eq ?_)
    field_simp
    norm_num
  rw [hx]
  have h4 : |(1 - u) * gammaG g * m.re| ≤ κ / 4 := by
    have hnn : 0 ≤ (1 - u) * gammaG g := by
      rw [hγ]; have : 0 < 1 - u := by linarith
      positivity
    rw [abs_mul, abs_of_nonneg hnn]
    exact h1
  calc |E + (1 - u) * gammaG g * m.re| ≤ |E| + |(1 - u) * gammaG g * m.re| := abs_add_le _ _
    _ ≤ 2 - κ / 2 / 2 := by linarith

/-- The height `Im w ≤ C''(1-s)/(1-u) η_u` of (6.9) [da:eq:comparison-parameters] is at most
`C_p C_s / g²` when `Im m ≤ C_s`. -/
private lemma rl_ybound {Cp Cs g u s y : ℝ} {m : ℂ} (hCp : 0 < Cp) (hg : 1 ≤ g) (hu1 : u < 1)
    (hs : 1 / 2 ≤ s) (hsu : s ≤ u) (him : 0 < m.im) (hmC : m.im ≤ Cs)
    (hy : y ≤ Cp * ((1 - s) / (1 - u)) * etaChar g m u) : y ≤ Cp * Cs / g ^ 2 := by
  have h1u : 0 < 1 - u := by linarith
  have hγ : gammaG g = (g ^ 2)⁻¹ := rl_gamma hg
  have hg2 : 0 < g ^ 2 := by positivity
  have he : (1 - s) / (1 - u) * etaChar g m u = (1 - s) * (g ^ 2)⁻¹ * m.im := by
    unfold etaChar; rw [hγ]; field_simp
  have hs1 : 1 - s ≤ 1 := by linarith
  have hs0 : 0 ≤ 1 - s := by linarith
  calc y ≤ Cp * ((1 - s) * (g ^ 2)⁻¹ * m.im) := by rw [← he, ← mul_assoc]; exact hy
    _ ≤ Cp * (1 * (g ^ 2)⁻¹ * Cs) := by gcongr
    _ = Cp * Cs / g ^ 2 := by field_simp

/-- `L ≥ 3` from `3 g² log W ≤ L` with `g ≥ 1`. -/
private lemma rl_L3 {W : ℕ} {g : ℝ} {L : ℕ} (hW : 3 ≤ W) (hg1 : 1 ≤ g)
    (h : (3 : ℝ) * g ^ 2 * Real.log W ≤ L) : 3 ≤ L := by
  have h1 := rl_vol1 hW (by norm_num : (0 : ℝ) ≤ 3) h
  have : (3 : ℝ) ≤ L := le_trans (le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hg1)) h1
  exact_mod_cast this

/-- The chain data of a point reached from `baseLarge`: a base point with the same `L`, an
admissible chain of at most `d` comparisons leading to `(g, E)`, and a time below the last
comparison time. -/
private lemma rl_chain {κ Cκ CV : ℝ} {ρ : ℕ → ℝ} {W : ℕ} (hW : 1 ≤ W) {d : ℕ} {p : FlowPt}
    (h : CmpReach (baseLarge κ Cκ CV ρ) W d p) :
    ∃ (g₀ E₀ u₀ : ℝ) (steps : List (ℝ × ℝ)),
      (⟨g₀, E₀, p.L, u₀⟩ : FlowPt) ∈ baseLarge κ Cκ CV ρ W ∧ steps.length ≤ d ∧
      (∀ q ∈ steps, 1 / 2 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 < 1) ∧
      steps.IsChain (fun a b => b.2 ≤ a.1) ∧
      cmpChain p.L (g₀, E₀) steps = (p.g, p.E) ∧
      1 / 2 ≤ p.u ∧ p.u ≤ u₀ ∧ (∀ q ∈ steps.getLast?, p.u ≤ q.1) := by
  induction h with
  | base hp =>
    exact ⟨_, _, _, [], hp, by simp, by simp, List.isChain_nil, rfl, hp.2.2.2.2.1, le_rfl, by simp⟩
  | earlier v _ hv hvu ih =>
    obtain ⟨g₀, E₀, u₀, steps, hb, hl, hs, hc, hch, hu, hu0, hlast⟩ := ih
    exact ⟨g₀, E₀, u₀, steps, hb, hl, hs, hc, hch, hv, hvu.trans hu0,
      fun q hq => hvu.trans (hlast q hq)⟩
  | @cmp d p s _ hs hsu ih =>
    obtain ⟨g₀, E₀, u₀, steps, hb, hl, hsteps, hc, hch, hu, hu0, hlast⟩ := ih
    have hu1 : p.u < 1 := by
      have h6 : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - u₀ := hb.2.2.2.2.2
      have := rl_rpow_pos hW
      linarith
    refine ⟨g₀, E₀, u₀, steps ++ [(s, p.u)], hb, ?_, ?_, ?_, ?_, hs, hsu.trans hu0, ?_⟩
    · simpa using hl
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hsteps q hq
      · obtain rfl : q = (s, p.u) := List.mem_singleton.mp hq
        exact ⟨hs, hsu, hu1⟩
    · refine hc.append (List.isChain_singleton _) ?_
      intro x hx y hy
      have hy' : (s, p.u) = y := by simpa using hy
      subst hy'
      exact hlast x hx
    · change cmpChain p.L (g₀, E₀) (steps ++ [(s, p.u)]) = _
      simp only [cmpChain, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change cmpStep p.L (cmpChain p.L (g₀, E₀) steps) (s, p.u) = _
      rw [hch]
      rfl
    · intro q hq
      have hq' : (s, p.u) = q := by simpa using hq
      subst hq'
      exact le_rfl
  | lift _ ih =>
    obtain ⟨g₀, E₀, u₀, steps, hb, hl, hs, hc, hch, hu, hu0, hlast⟩ := ih
    exact ⟨g₀, E₀, u₀, steps, hb, hl.trans (Nat.le_succ _), hs, hc, hch, hu, hu0, hlast⟩

/-- The large-coupling regime: for every chain depth `J` there is a coupling threshold `C_κ`
(Lemmas 6.1 [da:lem:scales-propagators], 6.3(b) [da:lem:comparison-parameters], 6.4
[da:lem:positive-height] at large coupling, Lemma 5.2(b) [fo:lem:deterministic], (5.21)
[fo:eq:primitive-tail] and (B.16) [b:eq:primitive-long-pair]). -/
theorem regimeLarge_exists (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) (J : ℕ) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∃ R : PropRegime, R.base = baseLarge κ Cκ CV ρ ∧ R.J = J := by
  have hκ' : 0 < κ / 2 := by linarith
  have hκ'2 : κ / 2 < 2 := by linarith
  obtain ⟨Cκc, Rc, C''c, hCκc, hRc, hC''c, Hc⟩ := cmpChain_large κ hκ hκ2 J
  obtain ⟨Cκs, cs, Cs, hCκs, hcs, hCs, Hs⟩ := scalesProp_large (κ / 2) hκ' hκ'2
  obtain ⟨Cκp, Rp, Cp, hCκp, hRp, hCp, Hp⟩ := cmpParams_large (κ / 2) hκ' hκ'2
  obtain ⟨Cκ1, hCκ1, H1⟩ := primLoop_large' (κ / 2) hκ' hκ'2
  obtain ⟨Cκ2, hCκ2, H2⟩ := primLoop_large_tail' (κ / 2) hκ' hκ'2
  obtain ⟨Cκ3, hCκ3, H3⟩ := primLoop_longPair_large' (κ / 2) hκ' hκ'2
  obtain ⟨Cκh, Rh, ch, Ch, hCκh, hRh, hch, hCh, Hh⟩ :=
    positiveHeight_large (κ / 2) (Cp * Cs) hκ' hκ'2 (by positivity)
  have hCsκ : 0 < 2 * Cs / κ := by positivity
  obtain ⟨T, hTc, hTs, hTp, hT1, hT2, hT3, hTh, hTκ, hT0⟩ : ∃ T : ℝ, Cκc ≤ T ∧ Cκs ≤ T ∧
      Cκp ≤ T ∧ Cκ1 ≤ T ∧ Cκ2 ≤ T ∧ Cκ3 ≤ T ∧ Cκh ≤ T ∧ 2 * Cs / κ ≤ T ∧ 1 ≤ T :=
    ⟨Cκc + Cκs + Cκp + Cκ1 + Cκ2 + Cκ3 + Cκh + 2 * Cs / κ, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨Cc, hCcs, hCcp, hCch, hCc3⟩ : ∃ Cc : ℝ, Cs ≤ Cc ∧ Cp ≤ Cc ∧ Ch ≤ Cc ∧ 3 ≤ Cc :=
    ⟨Cs + Cp + Ch + 3, by linarith, by linarith, by linarith, by linarith⟩
  have hcc : 0 < min cs ch := lt_min hcs hch
  -- the facts at a point reached from the base family
  have key : ∀ (Cκ : ℝ), 2 * T ≤ Cκ → ∀ (ρ : ℕ → ℝ) (W : ℕ), 3 ≤ W → Rc + 3 ≤ ρ W →
      ∀ (d : ℕ) (p : FlowPt), d ≤ J → CmpReach (baseLarge κ Cκ CV ρ) W d p →
      T ≤ p.g ∧ |p.E| ≤ 2 - κ / 2 ∧
      IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ∧
      1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u ∧
      (∀ K : ℝ, 0 ≤ K → K ≤ ρ W → K * p.g ^ 2 * Real.log W ≤ p.L) ∧
      (p.L : ℝ) ≤ 4 * CV * p.g ^ 2 * (W : ℝ) ^ 2 := by
    intro Cκ hCκ ρ W hW hρW d p hd hreach
    obtain ⟨g₀, E₀, u₀, steps, hb, hl, hs, hc, hch, hu, hu0, hlast⟩ := rl_chain (by omega) hreach
    obtain ⟨hg₀, hE₀, hLlo, hLhi, -, h6⟩ := hb
    have hlog := rl_one_le_log hW
    have hρ0 : 0 ≤ ρ W := by linarith
    have hg₀c : Cκc ≤ g₀ := by linarith
    have hLlo' : ρ W * g₀ ^ 2 * Real.log W ≤ p.L := hLlo
    have hLhi' : (p.L : ℝ) ≤ CV * g₀ ^ 2 * (W : ℝ) ^ 2 := hLhi
    have hL' : Rc * g₀ ^ 2 ≤ p.L :=
      le_trans (le_mul_of_one_le_right (by positivity) hlog)
        (rl_vol hW hRc.le (by linarith) (by linarith) le_rfl hLlo')
    obtain ⟨-, -, hlo, hhi, hE, hroot, -⟩ := Hc g₀ hg₀c p.L hL' E₀ hE₀ steps (hl.trans hd) hs hc
    rw [hch] at hlo hhi hE hroot
    dsimp only at hlo hhi hE hroot
    have hsq : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hg2 : g₀ / 2 ≤ p.g :=
      hlo.trans' (div_le_div_of_nonneg_left (by linarith) (Real.sqrt_pos.mpr two_pos) hsq)
    have hTg : T ≤ p.g := by linarith
    have hg0 : 0 ≤ p.g := by linarith
    have h6' : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - u₀ := h6
    refine ⟨hTg, hE, hroot, hu, by linarith, ?_, ?_⟩
    · exact fun K hK hKρ => rl_vol hW hK hKρ hg0 hhi hLlo'
    · have hg₀2 : g₀ ^ 2 ≤ 4 * p.g ^ 2 := by
        have := pow_le_pow_left₀ (by linarith) (show g₀ ≤ 2 * p.g by linarith) 2
        nlinarith
      calc (p.L : ℝ) ≤ CV * g₀ ^ 2 * (W : ℝ) ^ 2 := hLhi'
        _ ≤ CV * (4 * p.g ^ 2) * (W : ℝ) ^ 2 := by gcongr
        _ = 4 * CV * p.g ^ 2 * (W : ℝ) ^ 2 := by ring
  refine ⟨2 * T, by linarith, fun Cκ hCκ ρ hρ => ?_⟩
  have hCκT : 2 * T ≤ Cκ := hCκ
  have hnat : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop := tendsto_natCast_atTop_atTop
  have hρ3 : ∀ K : ℝ, ∀ᶠ W : ℕ in atTop, 3 ≤ W ∧ K ≤ ρ W := fun K =>
    (eventually_ge_atTop 3).and (hρ.eventually_ge_atTop K)
  refine ⟨{ base := baseLarge κ Cκ CV ρ
            J := J
            C := Cc
            c := min cs ch
            one_le_C := by linarith
            c_pos := hcc
            time := ?_
            dyson := ?_
            kernel := ?_
            budget := ?_
            cmp := ?_
            height := ?_
            prim := ?_
            primTail := ?_
            longPair := ?_ }, rfl, rfl⟩
  · exact fun W p hp => ⟨hp.2.2.2.2.1, hp.2.2.2.2.2⟩
  · obtain ⟨CA, W₀s, hCA, HA⟩ := Hs 1 one_pos
    obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp ((eventually_ge_atTop W₀s).and (hρ3 (Rc + 3 + CA)))
    refine ⟨W₀, fun W hW d p hd hreach => ?_⟩
    obtain ⟨hWs, h3, hρW⟩ := hW₀ W hW
    obtain ⟨hTg, hE, hroot, hu, hWu, hvol, -⟩ := key Cκ hCκT ρ W h3 (by linarith) d p hd hreach
    have hg1 : 1 ≤ p.g := hT0.trans hTg
    have hLA := hvol CA hCA.le (by linarith)
    have hL3 : 3 ≤ p.L := by
      have h := rl_vol1 h3 (by norm_num : (0 : ℝ) ≤ 3) (hvol 3 (by norm_num) (by linarith))
      have : (3 : ℝ) ≤ p.L := le_trans (le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hg1)) h
      exact_mod_cast this
    obtain ⟨hmim, hMb, hMrow, hQ, -⟩ := HA W hWs p.g (hTs.trans hTg) p.L hLA p.E hE _ hroot
    exact ⟨hL3, by linarith, hroot, (inv_anti₀ hCs hCcs).trans hmim.1, hmim.2.trans hCcs,
      fun a b => (hMb a b).trans hCcs, fun a => (hMrow a).trans hCcs,
      fun u hu0 hu1 a => (hQ u hu0 hu1 a).trans hCcs⟩
  · intro A hA
    obtain ⟨CA, W₀s, hCA, HA⟩ := Hs A hA
    obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp ((eventually_ge_atTop W₀s).and (hρ3 (Rc + 3 + CA)))
    refine ⟨W₀, fun W hW d p hd hreach => ?_⟩
    obtain ⟨hWs, h3, hρW⟩ := hW₀ W hW
    obtain ⟨hTg, hE, hroot, hu, hWu, hvol, hLhi⟩ := key Cκ hCκT ρ W h3 (by linarith) d p hd hreach
    have hg1 : 1 ≤ p.g := hT0.trans hTg
    have hLA := hvol CA hCA.le (by linarith)
    have hL3 : 1 ≤ p.L := by
      have h := rl_vol1 h3 (by norm_num : (0 : ℝ) ≤ 3) (hvol 3 (by norm_num) (by linarith))
      have : (3 : ℝ) ≤ p.L := le_trans (le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hg1)) h
      have : (1 : ℝ) ≤ p.L := by linarith
      exact_mod_cast this
    have hu1 : p.u < 1 := by have := rl_rpow_pos (W := W) (by omega); linarith
    have hℓ : 0 < ellProp p.g p.L p.u := rl_ell_pos (by linarith) hL3
    have h1u : 0 < 1 - p.u := by linarith
    obtain ⟨-, -, -, -, hker⟩ := HA W hWs p.g (hTs.trans hTg) p.L hLA p.E hE _ hroot
    intro a b
    obtain ⟨h0, hle⟩ := hker p.u (by linarith) hWu a b
    refine ⟨h0, hle.trans ?_⟩
    have hexp : Real.exp (-(cs * cycDist a b / ellProp p.g p.L p.u)) ≤
        Real.exp (-(min cs ch * cycDist a b / ellProp p.g p.L p.u)) := by
      refine Real.exp_le_exp.mpr (neg_le_neg ?_)
      gcongr
      exact min_le_left _ _
    have h1 : Cs / ((1 - p.u) * ellProp p.g p.L p.u) ≤ Cc / ((1 - p.u) * ellProp p.g p.L p.u) :=
      div_le_div_of_nonneg_right hCcs (by positivity)
    gcongr
  · obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp
      ((hnat.eventually_ge_atTop (8 * CV)).and (hρ3 (Rc + 3)))
    refine ⟨W₀, fun W hW d p hd hreach => ?_⟩
    obtain ⟨hW8, h3, hρW⟩ := hW₀ W hW
    obtain ⟨hTg, hE, hroot, hu, hWu, hvol, hLhi⟩ := key Cκ hCκT ρ W h3 hρW d p hd hreach
    exact rl_budget h3 hW8 hCc3 (hT0.trans hTg) hu hWu
      (by simpa using rl_vol1 h3 zero_le_one (hvol 1 zero_le_one (by linarith))) hLhi
  · obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp (hρ3 (Rc + 3 + Rp))
    refine ⟨W₀, fun W hW d p s hd hreach hs hsu => ?_⟩
    obtain ⟨h3, hρW⟩ := hW₀ W hW
    obtain ⟨hTg, hE, hroot, hu, hWu, hvol, -⟩ :=
      key Cκ hCκT ρ W h3 (by linarith) d p hd.le hreach
    have hu1 : p.u < 1 := by have := rl_rpow_pos (W := W) (by omega); linarith
    have hRL : Rp * p.g ^ 2 ≤ p.L := rl_vol1 h3 hRp.le (hvol Rp hRp.le (by linarith))
    obtain ⟨hξ, -, -, -, -, -, hre, hη1, hη2, hw, -⟩ :=
      Hp p.g (hTp.trans hTg) p.L hRL p.E hE _ hroot s p.u hs hsu hu1
    refine ⟨hre, hη1, hη2.trans ?_, ?_⟩
    · have hη0 : 0 ≤ etaChar p.g (mRoot p.g p.L p.E) p.u := by
        have := hroot.1
        have hg1 : 1 ≤ p.g := hT0.trans hTg
        unfold etaChar
        rw [rl_gamma hg1]
        have : 0 < 1 - p.u := by linarith
        positivity
      have : 0 ≤ (1 - s) / (1 - p.u) := div_nonneg (by linarith) (by linarith)
      gcongr
    · rw [hξ, Complex.ofReal_one, inv_one, one_mul]
      exact hw
  · obtain ⟨CA, W₀s, hCA, HA⟩ := Hs 1 one_pos
    obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp
      ((eventually_ge_atTop W₀s).and (hρ3 (Rc + 3 + CA + Rp + Rh)))
    refine ⟨W₀, fun W hW d p s y hd hreach hs hsu hy1 hy2 => ?_⟩
    obtain ⟨hWs, h3, hρW⟩ := hW₀ W hW
    obtain ⟨hTg, hE, hroot, hu, hWu, hvol, -⟩ :=
      key Cκ hCκT ρ W h3 (by linarith) d p hd.le hreach
    have hg1 : 1 ≤ p.g := hT0.trans hTg
    have hu1 : p.u < 1 := by have := rl_rpow_pos (W := W) (by omega); linarith
    have hRLp : Rp * p.g ^ 2 ≤ p.L := rl_vol1 h3 hRp.le (hvol Rp hRp.le (by linarith))
    have hRLh : Rh * p.g ^ 2 ≤ p.L := rl_vol1 h3 hRh.le (hvol Rh hRh.le (by linarith))
    have hLA := hvol CA hCA.le (by linarith)
    have hL1 : 1 ≤ p.L := by
      have h := rl_vol1 h3 (by norm_num : (0 : ℝ) ≤ 3) (hvol 3 (by norm_num) (by linarith))
      have : (3 : ℝ) ≤ p.L := le_trans (le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hg1)) h
      have : (1 : ℝ) ≤ p.L := by linarith
      exact_mod_cast this
    obtain ⟨hmim, hMb, -, -, -⟩ := HA W hWs p.g (hTs.trans hTg) p.L hLA p.E hE _ hroot
    obtain ⟨-, -, -, -, -, -, -, hη1, hη2, -, -⟩ :=
      Hp p.g (hTp.trans hTg) p.L hRLp p.E hE _ hroot s p.u hs hsu hu1
    have hγ : 0 < gammaG p.g := by rw [rl_gamma hg1]; positivity
    have hmre := rl_mre hL1 hγ hroot (fun a b => hMb a b)
    have hx := rl_xmargin hκ hg1 (hTκ.trans hTg) hu hu1 hE hmre
    have hη0 : 0 < etaChar p.g (mRoot p.g p.L p.E) p.u := by
      have := hroot.1
      have : 0 < 1 - p.u := by linarith
      unfold etaChar
      positivity
    have hy0 : 0 < y := lt_of_lt_of_le hη0 hy1
    have hyC := rl_ybound (zero_lt_one.trans_le hCp) hg1 hu1 hs hsu hroot.1 hmim.2 (hy2.trans hη2)
    obtain ⟨hr, hcm, -, hMb', hMrow', hQ', hdiff, hderiv, -⟩ :=
      Hh p.g (hTh.trans hTg) p.L hRLh _ y p.u hx hy0 hyC hu hu1.le
    refine ⟨hr, (min_le_right _ _).trans hcm, fun a b => (hMb' a b).trans hCch,
      fun a => (hMrow' a).trans hCch, fun a => ?_, hdiff, fun a b => (hderiv a b).trans hCch⟩
    refine le_trans (Finset.sum_le_sum fun b _ => ?_) ((hQ' a).trans hCch)
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))
  · intro kmax δ hδ
    have hall : ∀ k ∈ Finset.range (kmax + 1), ∀ᶠ W : ℕ in atTop, ∀ (d : ℕ) (p : FlowPt),
        d ≤ J → CmpReach (baseLarge κ Cκ CV ρ) W d p → 2 ≤ k → k ≤ kmax →
        ∀ (a : Fin k → Fin p.L) (σ : Fin k → Bool),
        ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u a σ‖ ≤
          (W : ℝ) ^ δ * zetaProp p.g W p.L p.u ^ (k - 1) := by
      intro k _
      by_cases hk : 2 ≤ k
      · obtain ⟨Cs1, C', hCs1, hC', Hk⟩ := H1 k hk
        have hev : ∀ᶠ W : ℕ in atTop, (3 ≤ W ∧ Rc + 3 + Cs1 ≤ ρ W) ∧ C' ≤ (W : ℝ) ^ δ :=
          (hρ3 (Rc + 3 + Cs1)).and (((tendsto_rpow_atTop hδ).comp hnat).eventually_ge_atTop C')
        refine hev.mono fun W ⟨⟨h3, hρW⟩, hCW⟩ d p hd hreach _ _ a σ => ?_
        obtain ⟨hTg, hE, hroot, hu, hWu, hvol, -⟩ :=
          key Cκ hCκT ρ W h3 (by linarith) d p hd hreach
        have hg1 : 1 ≤ p.g := hT0.trans hTg
        have hL3 : 3 ≤ p.L := rl_L3 h3 hg1 (hvol 3 (by norm_num) (by linarith))
        have hu1 : p.u < 1 := by have := rl_rpow_pos (W := W) (by omega); linarith
        have hζ := rl_zeta_nonneg (W := W) hg1 hu1 (by omega : 1 ≤ p.L)
        refine (Hk W h3 p.g (hT1.trans hTg) p.L hL3 (hvol Cs1 hCs1.le (by linarith)) p.E hE _
          hroot p.u (by linarith) hWu a σ).trans ?_
        exact mul_le_mul_of_nonneg_right hCW (pow_nonneg hζ _)
      · exact Filter.Eventually.of_forall fun W d p hd hreach h2 => absurd h2 hk
    obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp ((Filter.eventually_all_finset _).mpr hall)
    exact ⟨W₀, fun W hW d p hd hreach k hk2 hkm a σ =>
      hW₀ W hW k (Finset.mem_range.mpr (by omega)) d p hd hreach hk2 hkm a σ⟩
  · intro k hk ε Q hε hQ
    obtain ⟨Cs1, W₀s, hCs1, Hk⟩ := H2 ε Q hε hQ k hk
    obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp
      ((eventually_ge_atTop W₀s).and (hρ3 (Rc + 3 + Cs1)))
    refine ⟨W₀, fun W hW d p hd hreach a σ hdiam => ?_⟩
    obtain ⟨hWs, h3, hρW⟩ := hW₀ W hW
    obtain ⟨hTg, hE, hroot, hu, hWu, hvol, -⟩ :=
      key Cκ hCκT ρ W h3 (by linarith) d p hd hreach
    have hg1 : 1 ≤ p.g := hT0.trans hTg
    have hL3 : 3 ≤ p.L := rl_L3 h3 hg1 (hvol 3 (by norm_num) (by linarith))
    exact Hk W hWs p.g (hT2.trans hTg) p.L hL3 (hvol Cs1 hCs1.le (by linarith)) p.E hE _
      hroot p.u (by linarith) hWu a σ hdiam
  · intro θ cp F hθ hθ2 hcp hF
    obtain ⟨Cs1, C', W₀s, hCs1, hC', Hk⟩ := H3 θ cp F hθ hθ2 hcp hF
    obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp
      ((eventually_ge_atTop W₀s).and (hρ3 (Rc + 3 + Cs1)))
    refine ⟨C', W₀, fun W hW d p hd hreach a b σ₁ σ₂ hdist => ?_⟩
    obtain ⟨hWs, h3, hρW⟩ := hW₀ W hW
    obtain ⟨hTg, hE, hroot, hu, hWu, hvol, -⟩ :=
      key Cκ hCκT ρ W h3 (by linarith) d p hd hreach
    have hg1 : 1 ≤ p.g := hT0.trans hTg
    have hL3 : 3 ≤ p.L := rl_L3 h3 hg1 (hvol 3 (by norm_num) (by linarith))
    exact Hk W hWs p.g (hT3.trans hTg) p.L hL3 (hvol Cs1 hCs1.le (by linarith)) p.E hE _
      hroot p.u hu hWu a b σ₁ σ₂ hdist

end LSBA
