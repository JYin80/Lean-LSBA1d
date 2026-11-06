import LSBA.Dyson.Regular

/-!
# Finite-cycle regularity (Lemma A.3 [bl:lem:finite])

Lemma A.3 [bl:lem:finite] at `γ = γ_g`: at every regular point of the line (`Im m_g(x + i0) ≥ c₀`),
on the quantile domain (A.9) [da:eq:finite-domain], for `L ≥ L₀`: the finite-cycle boundary value
solves (5.2) [fo:eq:dyson-family] with `Im ≥ c`, and `|m_{g,L} − m_g| ≤ C′e^{-cL}` at `η = 0` and
for `0 < η ≤ 1` ((A.10) [da:eq:finite-regularity], (A.12) [bl:eq:finitebulk]).
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-! ### The parameters `γ_g`, `b = √γ_g g` for `0 ≤ g ≤ C` -/

private lemma finiteRegular_max_pos (g : ℝ) : 0 < max 1 g :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

private lemma finiteRegular_gamma_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have := finiteRegular_max_pos g
  positivity

private lemma finiteRegular_gamma_le_one (g : ℝ) : gammaG g ≤ 1 := by
  unfold gammaG
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_max_left _ _))

/-- `γ_g ≥ max{1, C}^{-2}` for `g ≤ C`. -/
private lemma finiteRegular_gamma_ge {g C : ℝ} (hgC : g ≤ C) : ((max 1 C) ^ 2)⁻¹ ≤ gammaG g := by
  unfold gammaG
  have h1 := finiteRegular_max_pos g
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h1.le (max_le_max le_rfl hgC) 2)

private lemma finiteRegular_hopB_nonneg {g : ℝ} (hg : 0 ≤ g) : 0 ≤ hopB g := by
  unfold hopB
  exact div_nonneg hg (finiteRegular_max_pos g).le

private lemma finiteRegular_hopB_le_one (g : ℝ) : hopB g ≤ 1 := by
  unfold hopB
  rw [div_le_one (finiteRegular_max_pos g)]
  exact le_max_right _ _

/-- `γ_g r ≤ 1` when `r ≤ max{1, g}`. -/
private lemma finiteRegular_gamma_mul_le {g r : ℝ} (hr : r ≤ max 1 g) : gammaG g * r ≤ 1 := by
  have hM := finiteRegular_max_pos g
  have hγ := finiteRegular_gamma_pos g
  calc gammaG g * r ≤ gammaG g * max 1 g := mul_le_mul_of_nonneg_left hr hγ.le
    _ = (max 1 g)⁻¹ := by unfold gammaG; field_simp
    _ ≤ 1 := inv_le_one_of_one_le₀ (le_max_left _ _)

/-! ### A uniform lower bound on `Im m_g(x + iη)`, `0 < η ≤ 1`, at a regular point -/

/-- Along the vertical line over `x`, `η ↦ (Im m_g(x + iη))³ + 3η/(2γ_g²)` is nondecreasing on
`η > 0`, by the first `z`-derivative bound `|m_g'| ≤ (2γ_g²(Im m_g)²)⁻¹` of Lemma A.2
[bl:lem:regular]. -/
private lemma finiteRegular_cube_mono (g : ℝ) (hg : 0 ≤ g) (x : ℝ) :
    MonotoneOn (fun η : ℝ => (mDyson g (x + η * I)).im ^ 3 + 3 * (2 * gammaG g ^ 2)⁻¹ * η)
      (Set.Ioi 0) := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hγ := finiteRegular_gamma_pos g
  have hD : ∀ η : ℝ, 0 < η → HasDerivAt
      (fun η : ℝ => (mDyson g (x + η * I)).im ^ 3 + 3 * (2 * gammaG g ^ 2)⁻¹ * η)
      (3 * (mDyson g (x + η * I)).im ^ 2 * (deriv (mDyson g) (x + η * I)).re +
        3 * (2 * gammaG g ^ 2)⁻¹) η := by
    intro η hη
    have hz : 0 < ((x : ℂ) + η * I).im := by simpa using hη
    have hd : HasDerivAt (mDyson g) (deriv (mDyson g) (x + η * I)) (x + η * I) :=
      ((mDyson_differentiableOn g hg _ hz).differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have hh : HasDerivAt (fun t : ℝ => (x : ℂ) + t * I) I η := by
      have := (((hasDerivAt_id η).ofReal_comp).mul_const I).const_add (x : ℂ)
      simpa using this
    have hc := hd.comp η hh
    have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt η hc
    have h3 := (him.pow 3).add ((hasDerivAt_id η).const_mul (3 * (2 * gammaG g ^ 2)⁻¹))
    convert h3 using 1
    · ext t
      simp [Function.comp]
    · simp [Function.comp]
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    (fun η hη => (hD η hη).continuousAt.continuousWithinAt) ?_ ?_
  · rw [interior_Ioi]
    exact fun η hη => (hD η hη).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro η hη
    rw [(hD η hη).deriv]
    have hz : 0 < ((x : ℂ) + η * I).im := by simpa using hη
    have hφ := (mDyson_spec g hg _ hz).1
    set φ := (mDyson g (x + η * I)).im
    set d := deriv (mDyson g) (x + η * I)
    have hd := mDyson_deriv_le g hg _ hz
    have hre : -‖d‖ ≤ d.re := by
      have := Complex.abs_re_le_norm d
      linarith [neg_abs_le d.re]
    have h1 : φ ^ 2 * ‖d‖ ≤ (2 * gammaG g ^ 2)⁻¹ := by
      calc φ ^ 2 * ‖d‖ ≤ φ ^ 2 * (2 * gammaG g ^ 2 * φ ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left hd (by positivity)
        _ = (2 * gammaG g ^ 2)⁻¹ := by field_simp
    nlinarith [sq_nonneg φ]

/-- `(Im m_g(x + i0))³ ≤ (Im m_g(x + iη))³ + 3η/(2γ_g²)` for every `η > 0`. -/
private lemma finiteRegular_cube_bound (g : ℝ) (hg : 0 ≤ g) (x η : ℝ) (hη : 0 < η) :
    (mDysonBdry g x).im ^ 3 ≤ (mDyson g (x + η * I)).im ^ 3 + 3 * (2 * gammaG g ^ 2)⁻¹ * η := by
  have hmono := finiteRegular_cube_mono g hg x
  have hT := mDysonBdry_tendsto g hg x
  have hT' : Tendsto (fun ε : ℝ => (mDyson g (x + ε * I)).im ^ 3 + 3 * (2 * gammaG g ^ 2)⁻¹ * ε)
      (𝓝[>] 0) (𝓝 ((mDysonBdry g x).im ^ 3 + 3 * (2 * gammaG g ^ 2)⁻¹ * 0)) := by
    refine (((Complex.continuous_im.tendsto _).comp hT).pow 3).add ?_
    exact ((continuous_const.mul continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [mul_zero, add_zero] at hT'
  refine le_of_tendsto hT' ?_
  filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
  exact hmono hε.1 hη hε.2.le

/-- Ward bound away from the real axis: `Im m_g(z) ≥ Im z/64` when `‖z‖ ≤ 5`, from (A.6)
[da:eq:ward], since `|2b cos p − z − γ_g m_g(z)| ≤ 8`. -/
private lemma finiteRegular_im_ge (g : ℝ) (hg : 0 ≤ g) (z : ℂ) (hz : 0 < z.im) (hz5 : ‖z‖ ≤ 5) :
    z.im / 64 ≤ (mDyson g z).im := by
  have hward := mDyson_ward g hg z hz
  obtain ⟨hm, -⟩ := mDyson_spec g hg z hz
  have hγ := finiteRegular_gamma_pos g
  have hb0 := finiteRegular_hopB_nonneg hg
  have hb1 := finiteRegular_hopB_le_one g
  have hγm : gammaG g * ‖mDyson g z‖ ≤ 1 :=
    finiteRegular_gamma_mul_le (mDyson_norm_le_max g hg z hz)
  set m := mDyson g z with hmdef
  have hne : ∀ p : ℝ, ((2 * hopB g * Real.cos p : ℝ) : ℂ) - z - gammaG g * m ≠ 0 := by
    intro p h
    have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.sub_im, Complex.ofReal_im, Complex.im_ofReal_mul,
      Complex.zero_im] at this
    have : 0 < gammaG g * m.im := mul_pos hγ hm
    linarith
  have hpt : ∀ p : ℝ, (1 / 64 : ℝ) ≤
      ‖(((2 * hopB g * Real.cos p : ℝ) : ℂ) - z - gammaG g * m)⁻¹‖ ^ 2 := by
    intro p
    have h8 : ‖((2 * hopB g * Real.cos p : ℝ) : ℂ) - z - gammaG g * m‖ ≤ 8 := by
      have ha : ‖((2 * hopB g * Real.cos p : ℝ) : ℂ)‖ ≤ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
        have := Real.abs_cos_le_one p
        nlinarith
      have hgm : ‖(gammaG g : ℂ) * m‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le]
        exact hγm
      calc ‖((2 * hopB g * Real.cos p : ℝ) : ℂ) - z - gammaG g * m‖
          ≤ ‖((2 * hopB g * Real.cos p : ℝ) : ℂ) - z‖ + ‖(gammaG g : ℂ) * m‖ := norm_sub_le _ _
        _ ≤ ‖((2 * hopB g * Real.cos p : ℝ) : ℂ)‖ + ‖z‖ + ‖(gammaG g : ℂ) * m‖ := by
            gcongr; exact norm_sub_le _ _
        _ ≤ 8 := by linarith
    have hpos : 0 < ‖((2 * hopB g * Real.cos p : ℝ) : ℂ) - z - gammaG g * m‖ :=
      norm_pos_iff.mpr (hne p)
    rw [norm_inv]
    have h18 : (1 / 8 : ℝ) ≤ ‖((2 * hopB g * Real.cos p : ℝ) : ℂ) - z - gammaG g * m‖⁻¹ := by
      rw [one_div]
      exact inv_anti₀ hpos h8
    nlinarith
  have hcont : Continuous fun p : ℝ =>
      ‖(((2 * hopB g * Real.cos p : ℝ) : ℂ) - z - gammaG g * m)⁻¹‖ ^ 2 := by
    refine ((Continuous.inv₀ ?_ hne).norm).pow 2
    fun_prop
  have hpi := Real.pi_pos
  have hint : ∫ p in (-π)..π, (1 / 64 : ℝ) ≤
      ∫ p in (-π)..π, ‖(((2 * hopB g * Real.cos p : ℝ) : ℂ) - z - gammaG g * m)⁻¹‖ ^ 2 :=
    intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hcont.intervalIntegrable _ _) (fun p _ => hpt p)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have havg : (1 / 64 : ℝ) ≤ m.im / (z.im + gammaG g * m.im) := by
    rw [← hward]
    calc (1 / 64 : ℝ) = (2 * π)⁻¹ * ((π - -π) * (1 / 64)) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hint (by positivity)
  have hden : 0 < z.im + gammaG g * m.im := by positivity
  rw [le_div_iff₀ hden] at havg
  have : 0 ≤ gammaG g * m.im := by positivity
  nlinarith

/-- At a regular point `Im m_g(x + i0) ≥ c₀`, `0 ≤ g ≤ C`: `Im m_g(x + iη) ≥ c₁` for every
`0 < η ≤ 1`, with `c₁ ∈ (0, c₀]` depending on `(C, c₀)` only. -/
private lemma finiteRegular_line_lower (C c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ c₀ ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ x : ℝ, c₀ ≤ (mDysonBdry g x).im →
      ∀ η : ℝ, 0 < η → η ≤ 1 → c₁ ≤ (mDyson g (x + η * I)).im := by
  set M := max 1 C with hMdef
  have hM : 0 < M := finiteRegular_max_pos C
  set β₀ := (M ^ 2)⁻¹ with hβ₀def
  have hβ₀ : 0 < β₀ := by positivity
  set k := 3 * (2 * β₀ ^ 2)⁻¹ with hkdef
  have hk : 0 < k := by positivity
  set η₁ := c₀ ^ 3 / (2 * k) with hη₁def
  have hη₁ : 0 < η₁ := by positivity
  refine ⟨min (c₀ / 2) (η₁ / 64), lt_min (by positivity) (by positivity),
    (min_le_left _ _).trans (by linarith), ?_⟩
  intro g hg hgC x hx η hη hη1
  have hγ := finiteRegular_gamma_pos g
  have hβγ : β₀ ≤ gammaG g := finiteRegular_gamma_ge hgC
  have hz : 0 < ((x : ℂ) + η * I).im := by simpa using hη
  have hφ := (mDyson_spec g hg _ hz).1
  rcases le_or_gt η η₁ with hηη | hηη
  · refine (min_le_left _ _).trans ?_
    have hcube := finiteRegular_cube_bound g hg x η hη
    have hkg : 3 * (2 * gammaG g ^ 2)⁻¹ ≤ k := by
      rw [hkdef]
      gcongr
    have hc3 : c₀ ^ 3 ≤ (mDysonBdry g x).im ^ 3 := pow_le_pow_left₀ hc₀.le hx 3
    have hkη : k * η ≤ c₀ ^ 3 / 2 := by
      calc k * η ≤ k * η₁ := mul_le_mul_of_nonneg_left hηη hk.le
        _ = c₀ ^ 3 / 2 := by rw [hη₁def]; field_simp
    have h1 : 3 * (2 * gammaG g ^ 2)⁻¹ * η ≤ k * η := mul_le_mul_of_nonneg_right hkg hη.le
    have h2 : (c₀ / 2) ^ 3 ≤ (mDyson g (x + η * I)).im ^ 3 := by
      have : (c₀ / 2) ^ 3 ≤ c₀ ^ 3 / 2 := by
        have : 0 < c₀ ^ 3 := by positivity
        nlinarith
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) hφ.le h2
  · refine (min_le_right _ _).trans ?_
    have hxim : 0 < (mDysonBdry g x).im := lt_of_lt_of_le hc₀ hx
    have hxe := (mDysonBdry_im_pos_iff g hg x).1 hxim
    have hx4 : |x| < 4 := lt_of_lt_of_le hxe ((bandEdge_le g hg).trans (support_bound_le_four g hg))
    have hz5 : ‖(x : ℂ) + η * I‖ ≤ 5 := by
      calc ‖(x : ℂ) + η * I‖ ≤ ‖(x : ℂ)‖ + ‖(η : ℂ) * I‖ := norm_add_le _ _
        _ = |x| + η := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_of_nonneg hη.le]
        _ ≤ 5 := by linarith
    have := finiteRegular_im_ge g hg _ hz hz5
    have hzim : ((x : ℂ) + η * I).im = η := by simp
    rw [hzim] at this
    linarith

/-! ### Lemma A.3 [bl:lem:finite] -/

/-- Lemma A.3 [bl:lem:finite] at a regular point of the line: (A.10)
[da:eq:finite-regularity] (values, lower bounds, `e^{-cL}` comparison) and (A.12)
[bl:eq:finitebulk], for `0 ≤ η ≤ 1`. -/
theorem finite_regular_point (C c₀ : ℝ) (hC : 0 < C) (hc₀ : 0 < c₀) :
    ∃ c C' : ℝ, ∃ L₀ : ℕ, 0 < c ∧ 0 < C' ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, L₀ ≤ L →
      ∀ x : ℝ, c₀ ≤ (mDysonBdry g x).im →
        c ≤ (mDysonLBdry g L x).im ∧
        mDysonLBdry g L x = dysonRHSL g L x (mDysonLBdry g L x) ∧
        ‖mDysonLBdry g L x - mDysonBdry g x‖ ≤ C' * Real.exp (-(c * L)) ∧
        ∀ η : ℝ, 0 < η → η ≤ 1 → c ≤ (mDysonL g L (x + η * I)).im ∧
          ‖mDysonL g L (x + η * I) - mDyson g (x + η * I)‖ ≤ C' * Real.exp (-(c * L)) := by
  obtain ⟨c₁, hc₁, hc₁c₀, hline⟩ := finiteRegular_line_lower C c₀ hc₀
  set M := max 1 C with hMdef
  have hM : 0 < M := finiteRegular_max_pos C
  set β₀ := (M ^ 2)⁻¹ with hβ₀def
  have hβ₀ : 0 < β₀ := by positivity
  obtain ⟨cr, C', L₀, hcr, hC', H⟩ := finiteRoot_of_lineRoot 1 β₀ c₁ one_pos hβ₀ hc₁
  refine ⟨min (c₁ / 2) cr, C', max L₀ 1, lt_min (by positivity) hcr, hC', ?_⟩
  intro g hg hgC L hL x hx
  have hL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hb0 := finiteRegular_hopB_nonneg hg
  have hb1 := finiteRegular_hopB_le_one g
  have hβγ : β₀ ≤ gammaG g := finiteRegular_gamma_ge hgC
  have hγ1 := finiteRegular_gamma_le_one g
  have hexp : C' * Real.exp (-(cr * L)) ≤ C' * Real.exp (-(min (c₁ / 2) cr * L)) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC'.le
    have : min (c₁ / 2) cr * L ≤ cr * L :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg L)
    linarith
  have hxim : 0 < (mDysonBdry g x).im := lt_of_lt_of_le hc₀ hx
  have hxe := (mDysonBdry_im_pos_iff g hg x).1 hxim
  obtain ⟨-, hfix⟩ := mDysonBdry_spec g hg x hxe
  rw [dysonRHS_eq_freeT] at hfix
  obtain ⟨m, hm, hmroot, hmc, hmd⟩ := H (hopB g) hb0 hb1 (gammaG g) hβγ hγ1 L hL₀ (x : ℂ)
    (by simp) _ hxim hfix (hc₁c₀.trans hx)
  have hmL : m = dysonRHSL g L x m := hmroot
  have hB := (mDysonL_tendsto_root g hg L hL1 x m hm hmL).2.1
  refine ⟨?_, ?_, ?_, fun η hη hη1 => ?_⟩
  · rw [hB]; exact (min_le_left _ _).trans hmc
  · rw [hB]; exact hmL
  · rw [hB]; exact hmd.trans hexp
  · have hz : 0 < ((x : ℂ) + η * I).im := by simpa using hη
    obtain ⟨hmi, hfix'⟩ := mDyson_spec g hg _ hz
    rw [dysonRHS_eq_freeT] at hfix'
    obtain ⟨m', hm', hroot', hmc', hmd'⟩ := H (hopB g) hb0 hb1 (gammaG g) hβγ hγ1 L hL₀ _ hz.le
      _ hmi hfix' (hline g hg hgC x hx η hη hη1)
    have hu := mDysonL_unique g hg L hL1 _ hz m' hm' hroot'
    rw [← hu]
    exact ⟨(min_le_left _ _).trans hmc', hmd'.trans hexp⟩

/-- Lemma A.3 [bl:lem:finite] on the quantile domain (A.9) [da:eq:finite-domain] at
`γ = γ_g`. -/
theorem finite_regular_quantile (C κ : ℝ) (hC : 0 < C) (hκ : 0 < κ ∧ κ < 1 / 2) :
    ∃ b c C' : ℝ, ∃ L₀ : ℕ, 0 < b ∧ 0 < c ∧ 0 < C' ∧
      ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, L₀ ≤ L → ∀ x : ℝ,
      (∃ E : ℝ, κ ≤ Fdist g (-|E|) ∧ |x - E| ≤ b) →
        |x| ≤ 2 * C + 2 ∧ c ≤ (mDysonLBdry g L x).im ∧
        mDysonLBdry g L x = dysonRHSL g L x (mDysonLBdry g L x) ∧
        ‖mDysonLBdry g L x - mDysonBdry g x‖ ≤ C' * Real.exp (-(c * L)) ∧
        ∀ η : ℝ, 0 < η → η ≤ 1 → c ≤ (mDysonL g L (x + η * I)).im ∧
          ‖mDysonL g L (x + η * I) - mDyson g (x + η * I)‖ ≤ C' * Real.exp (-(c * L)) := by
  obtain ⟨b, a, hb, ha, hq⟩ := regular_quantile C κ hC hκ
  obtain ⟨c, C', L₀, hc, hC', H⟩ := finite_regular_point C a hC ha
  refine ⟨b, c, C', L₀, hb, hc, hC', fun g hg hgC L hL x hx => ?_⟩
  obtain ⟨h1, -, h3, -⟩ := hq g hg hgC x hx
  exact ⟨h1, H g hg hgC L hL x h3⟩

end LSBA
