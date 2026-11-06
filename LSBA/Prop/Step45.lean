import LSBA.Prop.Step3Cone

/-!
# Steps 4 and 5 of the one-step propagation

Steps 4 and 5 of Appendix C.3 [sec:gc-one-step] at each deterministic time: the remaining loop
errors and the regeneration of the input (5.22) [gc:eq:one-step-input] with `θ/2`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Stochastic domination: relabeling, minima, slowly growing factors -/

private lemma step45_two_le (W : ℕ) (hW : 2 ≤ W) (D : ℝ) :
    ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) ≤
      ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  have hWpos : (0 : ℝ) < W := by linarith
  have hnn : 0 ≤ (W : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hWpos.le _
  rw [← ENNReal.ofReal_add hnn hnn]
  apply ENNReal.ofReal_le_ofReal
  have e : (W : ℝ) ^ (-(D + 1)) = (W : ℝ) ^ (-D) * (W : ℝ)⁻¹ := by
    rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
  have hpos : 0 < (W : ℝ) ^ (-D) := Real.rpow_pos_of_pos hWpos _
  have hinv : (W : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW2
  rw [e]
  nlinarith

/-- Transfer of a domination along a map of labels, with a pointwise comparison of the
quantities and of the bounds for large `W`. -/
private lemma step45_relabel {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι}
    {Λ Λ' : ℕ → ι → Type*}
    {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ} {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ}
    {X' : (W : ℕ) → (p : ι) → Λ' W p → Ω W (vol p) → ℂ} {Y' : (W : ℕ) → (p : ι) → Λ' W p → ℝ}
    (h : PrecMax vol Dom X Y) (f : ∀ W p, Λ' W p → Λ W p) (W₁ : ℕ)
    (hX : ∀ W, W₁ ≤ W → ∀ p ∈ Dom W, ∀ l ω, ‖X' W p l ω‖ ≤ ‖X W p (f W p l) ω‖)
    (hY : ∀ W, W₁ ≤ W → ∀ p ∈ Dom W, ∀ l, Y W p (f W p l) ≤ Y' W p l) :
    PrecMax vol Dom X' Y' := by
  intro ε D hε hD
  obtain ⟨W₀, hW₀⟩ := h ε D hε hD
  refine ⟨max W₀ W₁, fun W hW p hp =>
    (measure_mono ?_).trans (hW₀ W (le_of_max_le_left hW) p hp)⟩
  rintro ω ⟨l, hl⟩
  have hW1 : W₁ ≤ W := le_of_max_le_right hW
  exact ⟨f W p l, lt_of_lt_of_le (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hY W hW1 p hp l)
    (Real.rpow_nonneg (Nat.cast_nonneg W) ε)) hl) (hX W hW1 p hp l ω)⟩

/-- Two bounds for the same quantity give the minimum of the bounds. -/
private lemma step45_min {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι} {Λ : ℕ → ι → Type*}
    {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ}
    {Y₁ Y₂ : (W : ℕ) → (p : ι) → Λ W p → ℝ} (h₁ : PrecMax vol Dom X Y₁)
    (h₂ : PrecMax vol Dom X Y₂) :
    PrecMax vol Dom X (fun W p l => min (Y₁ W p l) (Y₂ W p l)) := by
  intro ε D hε hD
  obtain ⟨W₁, hW₁⟩ := h₁ ε (D + 1) hε (by linarith)
  obtain ⟨W₂, hW₂⟩ := h₂ ε (D + 1) hε (by linarith)
  refine ⟨max (max W₁ W₂) 2, fun W hW p hp => ?_⟩
  have h1 : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have h2 : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have h3 : 2 ≤ W := (le_max_right _ _).trans hW
  calc μ W (vol p) {ω | ∃ l : Λ W p, (W : ℝ) ^ ε * min (Y₁ W p l) (Y₂ W p l) < ‖X W p l ω‖}
      ≤ μ W (vol p) ({ω | ∃ l : Λ W p, (W : ℝ) ^ ε * Y₁ W p l < ‖X W p l ω‖} ∪
          {ω | ∃ l : Λ W p, (W : ℝ) ^ ε * Y₂ W p l < ‖X W p l ω‖}) := by
        apply measure_mono
        rintro ω ⟨l, hl⟩
        rcases min_choice (Y₁ W p l) (Y₂ W p l) with h | h
        · rw [h] at hl; exact Or.inl ⟨l, hl⟩
        · rw [h] at hl; exact Or.inr ⟨l, hl⟩
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) :=
        add_le_add (hW₁ W h1 p hp) (hW₂ W h2 p hp)
    _ ≤ _ := step45_two_le W h3 D

/-- A factor `K_W` in the bound with `K_W ≤ W^δ` for large `W`, for every `δ > 0`, is absorbed
by `W^ε`. -/
private lemma step45_absorb {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι} {Λ : ℕ → ι → Type*}
    {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ} {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ}
    (K : ℕ → ℝ) (hK : ∀ δ : ℝ, 0 < δ → ∃ W₂ : ℕ, ∀ W : ℕ, W₂ ≤ W → K W ≤ (W : ℝ) ^ δ)
    (h : PrecMax vol Dom X (fun W p l => K W * Y W p l)) (W₁ : ℕ)
    (hY : ∀ W, W₁ ≤ W → ∀ p ∈ Dom W, ∀ l, 0 ≤ Y W p l) : PrecMax vol Dom X Y := by
  intro ε D hε hD
  obtain ⟨W₀, hW₀⟩ := h (ε / 2) D (by linarith) hD
  obtain ⟨W₂, hW₂⟩ := hK (ε / 2) (by linarith)
  refine ⟨max (max W₀ W₁) (max W₂ 1), fun W hW p hp =>
    (measure_mono ?_).trans (hW₀ W (by omega) p hp)⟩
  rintro ω ⟨l, hl⟩
  refine ⟨l, lt_of_le_of_lt ?_ hl⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hKW : K W ≤ (W : ℝ) ^ (ε / 2) := hW₂ W (by omega)
  have hYn := hY W (by omega) p hp l
  have hsq : (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) = (W : ℝ) ^ ε := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  calc (W : ℝ) ^ (ε / 2) * (K W * Y W p l)
      ≤ (W : ℝ) ^ (ε / 2) * ((W : ℝ) ^ (ε / 2) * Y W p l) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKW hYn)
          (Real.rpow_nonneg (by linarith) _)
    _ = (W : ℝ) ^ ε * Y W p l := by rw [← mul_assoc, hsq]

/-- A fixed constant is at most `W^δ` for large `W`. -/
private lemma step45_const_le (K : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ W₂ : ℕ, ∀ W : ℕ, W₂ ≤ W → K ≤ (W : ℝ) ^ δ := by
  have ht : Tendsto (fun W : ℕ => (W : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_ge_atTop K)

/-- `e^{C√(log W)} ≤ W^δ` for large `W`. -/
private lemma step45_expSqrtLog_le (C : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ W₂ : ℕ, ∀ W : ℕ, W₂ ≤ W → Real.exp (C * Real.sqrt (Real.log W)) ≤ (W : ℝ) ^ δ := by
  have ht : Tendsto (fun W : ℕ => Real.log W) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨W₂, hW₂⟩ := eventually_atTop.mp (ht.eventually_ge_atTop ((|C| / δ) ^ 2))
  refine ⟨max W₂ 1, fun W hW => ?_⟩
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hlog := hW₂ W (le_of_max_le_left hW)
  have hl0 : 0 ≤ Real.log W := le_trans (sq_nonneg _) hlog
  have hs : |C| / δ ≤ Real.sqrt (Real.log W) := by
    calc |C| / δ = Real.sqrt ((|C| / δ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hlog
  rw [Real.rpow_def_of_pos hWpos, mul_comm (Real.log W) δ]
  apply Real.exp_le_exp.mpr
  have hs0 : 0 ≤ Real.sqrt (Real.log W) := Real.sqrt_nonneg _
  have hss : Real.sqrt (Real.log W) * Real.sqrt (Real.log W) = Real.log W :=
    Real.mul_self_sqrt hl0
  have h1 : C * Real.sqrt (Real.log W) ≤ |C| * Real.sqrt (Real.log W) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hs0
  have h2 : |C| ≤ δ * Real.sqrt (Real.log W) := by
    rw [div_le_iff₀ hδ] at hs; linarith
  calc C * Real.sqrt (Real.log W) ≤ |C| * Real.sqrt (Real.log W) := h1
    _ ≤ δ * Real.sqrt (Real.log W) * Real.sqrt (Real.log W) :=
        mul_le_mul_of_nonneg_right h2 hs0
    _ = δ * Real.log W := by rw [mul_assoc, hss]

/-! ### Scales -/

private lemma step45_gamma_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

private lemma step45_ell_ge_one {g : ℝ} (hg : 0 ≤ g) {L : ℕ} (hL : 1 ≤ L) (u : ℝ) :
    1 ≤ ellProp g L u := by
  unfold ellProp
  refine le_min (by exact_mod_cast hL) ?_
  have : 0 ≤ g / Real.sqrt (gammaG g * (1 - u)) := div_nonneg hg (Real.sqrt_nonneg _)
  linarith

private lemma step45_ell_mono {g : ℝ} (hg : 0 ≤ g) (L : ℕ) {r v : ℝ} (hrv : r ≤ v)
    (hv : v < 1) : ellProp g L r ≤ ellProp g L v := by
  unfold ellProp
  refine min_le_min le_rfl ?_
  have hγ := step45_gamma_pos g
  have h1 : 0 < Real.sqrt (gammaG g * (1 - v)) := Real.sqrt_pos.2 (by nlinarith)
  have h2 : Real.sqrt (gammaG g * (1 - v)) ≤ Real.sqrt (gammaG g * (1 - r)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have : g / Real.sqrt (gammaG g * (1 - r)) ≤ g / Real.sqrt (gammaG g * (1 - v)) :=
    div_le_div_of_nonneg_left hg h1 h2
  linarith

/-- `(1 - v)ℓ_v ≤ (1 - r)ℓ_r` for `r ≤ v < 1`. -/
private lemma step45_rho_ell {g : ℝ} (hg : 0 ≤ g) {L : ℕ} (hL : 1 ≤ L) {r v : ℝ}
    (hrv : r ≤ v) (hv : v < 1) :
    1 ≤ (1 - r) / (1 - v) * ellProp g L r / ellProp g L v := by
  have hγ := step45_gamma_pos g
  have hℓv := step45_ell_ge_one hg hL v
  have h1v : 0 < 1 - v := by linarith
  rw [le_div_iff₀ (by linarith), one_mul, div_mul_eq_mul_div, le_div_iff₀ h1v]
  unfold ellProp
  rw [mul_comm (min _ _) (1 - v)]
  rw [mul_min_of_nonneg _ _ h1v.le, mul_min_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ 1 - r)]
  refine min_le_min (by nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]) ?_
  have key : ∀ u : ℝ, u < 1 → (1 - u) * (1 + g / Real.sqrt (gammaG g * (1 - u))) =
      (1 - u) + g * Real.sqrt (1 - u) / Real.sqrt (gammaG g) := by
    intro u hu
    have hu' : 0 < 1 - u := by linarith
    have hs : Real.sqrt (gammaG g * (1 - u)) = Real.sqrt (gammaG g) * Real.sqrt (1 - u) :=
      Real.sqrt_mul hγ.le _
    have hsu : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 hu'
    have hsg : 0 < Real.sqrt (gammaG g) := Real.sqrt_pos.2 hγ
    rw [hs]
    have hsq : Real.sqrt (1 - u) * Real.sqrt (1 - u) = 1 - u := Real.mul_self_sqrt hu'.le
    field_simp
    nlinarith [hsq]
  rw [key v hv, key r (lt_of_le_of_lt hrv hv)]
  have hsr : Real.sqrt (1 - v) ≤ Real.sqrt (1 - r) := Real.sqrt_le_sqrt (by linarith)
  have hsg : 0 < Real.sqrt (gammaG g) := Real.sqrt_pos.2 hγ
  have : g * Real.sqrt (1 - v) / Real.sqrt (gammaG g) ≤
      g * Real.sqrt (1 - r) / Real.sqrt (gammaG g) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsr hg) hsg.le
  linarith

/-- `(ρℓ_r/ℓ_v)ζ_r = ζ_v` with `ρ = (1 - r)/(1 - v)`. -/
private lemma step45_zeta_rho {g : ℝ} (hg : 0 ≤ g) {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L)
    {r v : ℝ} (hrv : r ≤ v) (hv : v < 1) :
    (1 - r) / (1 - v) * ellProp g L r / ellProp g L v * zetaProp g W L r = zetaProp g W L v := by
  have hγ := step45_gamma_pos g
  have hℓr := step45_ell_ge_one hg hL r
  have hℓv := step45_ell_ge_one hg hL v
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1v : 0 < 1 - v := by linarith
  have h1r : 0 < 1 - r := by linarith
  unfold zetaProp
  field_simp

private lemma step45_zeta_pos {g : ℝ} (hg : 0 ≤ g) {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L)
    {r : ℝ} (hr : r < 1) : 0 < zetaProp g W L r := by
  have hγ := step45_gamma_pos g
  have hℓ := step45_ell_ge_one hg hL r
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1r : 0 < 1 - r := by linarith
  unfold zetaProp
  have : 0 < (W : ℝ) * ellProp g L r * (1 - r) * gammaG g := by positivity
  positivity

/-- `ζ` is nondecreasing in time. -/
private lemma step45_zeta_mono {g : ℝ} (hg : 0 ≤ g) {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L)
    {r v : ℝ} (hrv : r ≤ v) (hv : v < 1) : zetaProp g W L r ≤ zetaProp g W L v := by
  rw [← step45_zeta_rho hg hW hL hrv hv]
  have h0 := (step45_zeta_pos hg hW hL (lt_of_le_of_lt hrv hv)).le
  have h1 := step45_rho_ell hg hL hrv hv
  nlinarith

/-- `ζ_v ≥ (2W)⁻¹`: `ℓ_v(1 - v)γ_g ≤ 2`. -/
private lemma step45_zeta_lower {g : ℝ} (hg : 0 ≤ g) {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L)
    {v : ℝ} (hv0 : 0 ≤ v) (hv : v < 1) : (2 * (W : ℝ))⁻¹ ≤ zetaProp g W L v := by
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hγ := step45_gamma_pos g
  have h1v : 0 < 1 - v := by linarith
  have h1v' : 1 - v ≤ 1 := by linarith
  have hsq : 0 < Real.sqrt (gammaG g * (1 - v)) := Real.sqrt_pos.mpr (by positivity)
  have hℓ1 := step45_ell_ge_one hg hL v
  have hprod : ellProp g L v * (1 - v) * gammaG g ≤ 2 := by
    have hle : ellProp g L v ≤ 1 + g / Real.sqrt (gammaG g * (1 - v)) := min_le_right _ _
    have hγ1 : gammaG g ≤ 1 := by
      unfold gammaG
      have : (1 : ℝ) ≤ max 1 g := le_max_left _ _
      exact inv_le_one_of_one_le₀ (one_le_pow₀ this)
    have hgm : g * Real.sqrt (gammaG g * (1 - v)) ≤ 1 := by
      have hmx : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
      have hsq1 : Real.sqrt (gammaG g * (1 - v)) ≤ Real.sqrt (gammaG g) :=
        Real.sqrt_le_sqrt (by nlinarith)
      have hsγ : Real.sqrt (gammaG g) = (max 1 g)⁻¹ := by
        unfold gammaG
        rw [Real.sqrt_inv, Real.sqrt_sq hmx.le]
      calc g * Real.sqrt (gammaG g * (1 - v)) ≤ g * (max 1 g)⁻¹ := by
            rw [← hsγ]; exact mul_le_mul_of_nonneg_left hsq1 hg
        _ ≤ 1 := by
            rw [← div_eq_mul_inv, div_le_one hmx]; exact le_max_right _ _
    have hkey : (1 + g / Real.sqrt (gammaG g * (1 - v))) * (1 - v) * gammaG g =
        (1 - v) * gammaG g + g * Real.sqrt (gammaG g * (1 - v)) := by
      have hss : Real.sqrt (gammaG g * (1 - v)) ^ 2 = gammaG g * (1 - v) :=
        Real.sq_sqrt (by positivity)
      field_simp
      nlinarith [hss]
    calc ellProp g L v * (1 - v) * gammaG g ≤
        (1 + g / Real.sqrt (gammaG g * (1 - v))) * (1 - v) * gammaG g := by
          gcongr
      _ = (1 - v) * gammaG g + g * Real.sqrt (gammaG g * (1 - v)) := hkey
      _ ≤ 1 * 1 + 1 := by gcongr
      _ = 2 := by norm_num
  have hpos : 0 < (W : ℝ) * ellProp g L v * (1 - v) * gammaG g := by
    have : 0 < ellProp g L v := by linarith
    positivity
  unfold zetaProp
  rw [inv_le_inv₀ (by positivity) hpos]
  calc (W : ℝ) * ellProp g L v * (1 - v) * gammaG g =
      (W : ℝ) * (ellProp g L v * (1 - v) * gammaG g) := by ring
    _ ≤ (W : ℝ) * 2 := by gcongr
    _ = 2 * W := by ring

/-- The facts on the scales used in Steps 4 and 5 at an admissible step point for large `W`. -/
private structure step45_Good (W : ℕ) (q : StepPt) : Prop where
  W3 : 3 ≤ W
  L3 : 3 ≤ q.L
  root : IsDysonRootV (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E)
  zs : 0 < zetaProp q.g W q.L q.s
  zsu : zetaProp q.g W q.L q.s ≤ zetaProp q.g W q.L q.u
  zut : zetaProp q.g W q.L q.u ≤ zetaProp q.g W q.L q.t
  zs1 : zetaProp q.g W q.L q.s ≤ 1
  R1 : 1 ≤ q.ratio
  RW : q.ratio ≤ (W : ℝ) ^ 3
  R12 : q.ratio ^ 12 * zetaProp q.g W q.L q.t ≤ 1
  tt : zetaProp q.g W q.L q.t * zetaProp q.g W q.L q.t ≤ zetaProp q.g W q.L q.s
  zlow : (2 * (W : ℝ))⁻¹ ≤ zetaProp q.g W q.L q.u
  ell1 : 1 ≤ ellProp q.g q.L q.u

private lemma step45_good (R : PropRegime) (c N : ℝ) (hc : 0 < c) (hN : 20 ≤ N)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) :
    ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ q ∈ S W, step45_Good W q := by
  obtain ⟨Wd, hWd⟩ := R.dyson
  refine ⟨max Wd 3, fun W hW q hq => ?_⟩
  obtain ⟨⟨d, hdJ, hreach⟩, hs1, hsu, hut, hst, hWt, hRN⟩ := hS W hq
  obtain ⟨hL3, hg0, hroot, -⟩ := hWd W (le_of_max_le_left hW) d (q.at q.t) hdJ.le hreach
  change 3 ≤ q.L at hL3
  change 0 ≤ q.g at hg0
  have hW3 : 3 ≤ W := le_of_max_le_right hW
  have hW1 : 1 ≤ W := by omega
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  have hL1 : 1 ≤ q.L := by omega
  have hW3pos : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hWpos _
  have ht1 : q.t < 1 := by linarith
  have hu1 : q.u < 1 := lt_of_le_of_lt hut ht1
  have hZ : 0 < zetaProp q.g W q.L q.s :=
    step45_zeta_pos hg0 hW1 hL1 (lt_of_le_of_lt hsu hu1)
  have hZu : zetaProp q.g W q.L q.s ≤ zetaProp q.g W q.L q.u :=
    step45_zeta_mono hg0 hW1 hL1 hsu hu1
  have hZt : zetaProp q.g W q.L q.u ≤ zetaProp q.g W q.L q.t :=
    step45_zeta_mono hg0 hW1 hL1 hut ht1
  have h1t : 0 < 1 - q.t := by linarith
  have hR1 : 1 ≤ q.ratio := by
    unfold StepPt.ratio
    rw [le_div_iff₀ h1t]
    linarith
  -- `ζ_t ≤ R ζ_s`
  have hZtR : zetaProp q.g W q.L q.t ≤ q.ratio * zetaProp q.g W q.L q.s := by
    have e := step45_zeta_rho hg0 hW1 hL1 hst.le ht1
    have hℓs := step45_ell_ge_one hg0 hL1 q.s
    have hℓt := step45_ell_ge_one hg0 hL1 q.t
    have hℓ : ellProp q.g q.L q.s / ellProp q.g q.L q.t ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact step45_ell_mono hg0 q.L hst.le ht1
    rw [← e]
    have hR0 : 0 ≤ (1 - q.s) / (1 - q.t) := by
      unfold StepPt.ratio at hR1; linarith
    calc (1 - q.s) / (1 - q.t) * ellProp q.g q.L q.s / ellProp q.g q.L q.t *
          zetaProp q.g W q.L q.s
        = (1 - q.s) / (1 - q.t) * (ellProp q.g q.L q.s / ellProp q.g q.L q.t) *
          zetaProp q.g W q.L q.s := by ring
      _ ≤ (1 - q.s) / (1 - q.t) * 1 * zetaProp q.g W q.L q.s := by gcongr
      _ = q.ratio * zetaProp q.g W q.L q.s := by unfold StepPt.ratio; ring
  have hZt0 : 0 ≤ zetaProp q.g W q.L q.t := by linarith
  -- `R^20 ζ_t ≤ 1`
  have hR20 : q.ratio ^ 20 * zetaProp q.g W q.L q.t ≤ 1 := by
    have hc1 : (W : ℝ) ^ (-c) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith)
    have hpow : q.ratio ^ 20 ≤ q.ratio ^ N := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hR1 (by exact_mod_cast hN)
    calc q.ratio ^ 20 * zetaProp q.g W q.L q.t ≤ q.ratio ^ N * zetaProp q.g W q.L q.t :=
          mul_le_mul_of_nonneg_right hpow hZt0
      _ ≤ 1 := hRN.trans hc1
  have hRk : ∀ k : ℕ, k ≤ 20 → q.ratio ^ k * zetaProp q.g W q.L q.t ≤ 1 := fun k hk =>
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR1 hk) hZt0).trans hR20
  have hR1t : q.ratio * zetaProp q.g W q.L q.t ≤ 1 := by simpa using hRk 1 (by norm_num)
  refine ⟨hW3, hL3, hroot, hZ, hZu, hZt, ?_, hR1, ?_, hRk 12 (by norm_num), ?_, ?_,
    step45_ell_ge_one hg0 hL1 q.u⟩
  · have h1 := hRk 0 (by norm_num)
    rw [pow_zero, one_mul] at h1
    linarith
  · unfold StepPt.ratio
    rw [div_le_iff₀ h1t]
    have e : (W : ℝ) ^ (-3 : ℝ) = ((W : ℝ) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hWpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e] at hWt
    have hW3' : 0 < (W : ℝ) ^ 3 := by positivity
    have : 1 ≤ (W : ℝ) ^ 3 * (1 - q.t) := by
      calc (1 : ℝ) = (W : ℝ) ^ 3 * ((W : ℝ) ^ 3)⁻¹ := (mul_inv_cancel₀ hW3'.ne').symm
        _ ≤ (W : ℝ) ^ 3 * (1 - q.t) := mul_le_mul_of_nonneg_left hWt hW3'.le
    linarith
  · calc zetaProp q.g W q.L q.t * zetaProp q.g W q.L q.t
        ≤ q.ratio * zetaProp q.g W q.L q.s * zetaProp q.g W q.L q.t :=
          mul_le_mul_of_nonneg_right hZtR hZt0
      _ = zetaProp q.g W q.L q.s * (q.ratio * zetaProp q.g W q.L q.t) := by ring
      _ ≤ zetaProp q.g W q.L q.s * 1 := mul_le_mul_of_nonneg_left hR1t hZ.le
      _ = zetaProp q.g W q.L q.s := mul_one _
  · exact step45_zeta_lower hg0 hW1 hL1 (by linarith) hu1

/-! ### Lengths one and two -/

/-- Length one at a root of (5.2) [fo:eq:dyson-family]: `|D_1(a; σ)| = |⟨G_u - M⟩_{aa}|`. -/
private lemma step45_one (W : ℕ) (hW : 1 ≤ W) (p : FlowPt) (hL : 3 ≤ p.L)
    (hm : IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E))
    (a : Fin 1 → Fin p.L) (σ : Fin 1 → Bool) (ω : Ω W p.L) :
    ‖flowErr W p a σ ω‖ = ‖blockTr (flowG W p ω - flowM W p) (a 0) (a 0)‖ := by
  have ha : a = ![a 0] := by funext i; fin_cases i; rfl
  have hσ : σ = ![σ 0] := by funext i; fin_cases i; rfl
  rw [ha, hσ, flowErr_one W hW p hL hm (a 0) (σ 0) ω]
  simp only [Matrix.cons_val_zero]
  split_ifs
  · rfl
  · rw [norm_star]

/-- A word of length two written by its entries. -/
private lemma step45_two (W : ℕ) (p : FlowPt) (a : Fin 2 → Fin p.L) (σ : Fin 2 → Bool)
    (ω : Ω W p.L) : flowErr W p a σ ω = flowErr W p ![a 0, a 1] ![σ 0, σ 1] ω := by
  have ha : a = ![a 0, a 1] := by funext i; fin_cases i <;> rfl
  have hσ : σ = ![σ 0, σ 1] := by funext i; fin_cases i <;> rfl
  conv_lhs => rw [ha, hσ]

/-- The swap of a mixed pair: `D_2(a, b; -, +) = D_2(b, a; +, -)`, by cyclicity of the trace and
the symmetry of the two-loops. -/
private lemma step45_swap (W : ℕ) (p : FlowPt) (a₀ a₁ : Fin p.L) (ω : Ω W p.L) :
    flowErr W p ![a₀, a₁] ![false, true] ω = flowErr W p ![a₁, a₀] ![true, false] ω := by
  unfold flowErr
  have h1 := loopTr_rotate (flowG W p ω) ![a₁, a₀] ![true, false]
  have e1 : (![a₁, a₀] ∘ finRotate 2) = ![a₀, a₁] := by funext i; fin_cases i <;> rfl
  have e2 : (![true, false] ∘ finRotate 2) = ![false, true] := by funext i; fin_cases i <;> rfl
  rw [e1, e2] at h1
  rw [h1, primLoop_two_swap]

private lemma step45_P1 (W : ℕ) (p : FlowPt) (a : Fin 2 → Fin p.L) (σ : Fin 2 → Bool)
    (ω : Ω W p.L) :
    ‖if σ 0 = true ∧ σ 1 = false then flowErr W p a σ ω else 0‖ ≤
      ‖flowErr W p ![a 0, a 1] ![true, false] ω‖ := by
  split_ifs with hσ
  · rw [step45_two W p a σ ω, hσ.1, hσ.2]
  · rw [norm_zero]; exact norm_nonneg _

private lemma step45_P2 (W : ℕ) (p : FlowPt) (a : Fin 2 → Fin p.L) (σ : Fin 2 → Bool)
    (ω : Ω W p.L) :
    ‖if σ 0 = false ∧ σ 1 = true then flowErr W p a σ ω else 0‖ ≤
      ‖flowErr W p ![a 1, a 0] ![true, false] ω‖ := by
  split_ifs with hσ
  · rw [step45_two W p a σ ω, hσ.1, hσ.2, step45_swap]
  · rw [norm_zero]; exact norm_nonneg _

private lemma step45_P3 (W : ℕ) (p : FlowPt) (a : Fin 2 → Fin p.L) (σ : Fin 2 → Bool)
    (ω : Ω W p.L) :
    ‖if σ 0 = σ 1 then flowErr W p a σ ω else 0‖ ≤
      ‖flowErr W p ![a 0, a 1] ![σ 0, σ 0] ω‖ := by
  split_ifs with hσ
  · rw [step45_two W p a σ ω, ← hσ]
  · rw [norm_zero]; exact norm_nonneg _

private lemma step45_P123 (W : ℕ) (p : FlowPt) (a : Fin 2 → Fin p.L) (σ : Fin 2 → Bool)
    (ω : Ω W p.L) :
    ‖flowErr W p a σ ω‖ ≤
      ‖(if σ 0 = true ∧ σ 1 = false then flowErr W p a σ ω else 0) +
        (if σ 0 = false ∧ σ 1 = true then flowErr W p a σ ω else 0) +
        (if σ 0 = σ 1 then flowErr W p a σ ω else 0)‖ := by
  rcases Bool.dichotomy (σ 0) with h0 | h0 <;> rcases Bool.dichotomy (σ 1) with h1 | h1 <;>
    simp [h0, h1]

/-- Length one: `D_1(u; a; ±)` is `⟨G_u - M⟩_{aa}` or its conjugate, bounded by the averaged
local law of Step 2: `|D_1(u)| ≺ ζ_u`. -/
private lemma step45_base1 (R : PropRegime) (c N cp₂ θ : ℝ) (hc : 0 < c) (hN : 20 ≤ N)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) (h2 : Step2Out cp₂ θ S) :
    PrecMax StepPt.L S (Λ := fun _ q => Word 1 q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => zetaProp q.g W q.L q.u ^ 1) := by
  obtain ⟨W₁, hW₁⟩ := step45_good R c N hc hN S hS
  refine step45_relabel h2.avg (fun _ _ w => (w.1 0, w.1 0)) W₁ ?_ ?_
  · intro W hW q hq w ω
    have hg := hW₁ W hW q hq
    exact le_of_eq (step45_one W (by have := hg.W3; omega) (q.at q.u) hg.L3 hg.root w.1 w.2 ω)
  · intro W hW q hq w
    simp

/-- Length two before the improvement: the mixed pair of Step 2 (`(+,-)`, and `(-,+)` by the swap)
at `F = 1` and the same-sign pair `R^{7/2} ≤ R^6`, so `|D_2(u)| ≺ 5R^6ζ_u^2`. -/
private lemma step45_base2 (R : PropRegime) (c N cp₂ θ : ℝ) (hc : 0 < c) (hN : 20 ≤ N)
    (hcp₂ : 0 < cp₂) (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (h2 : Step2Out cp₂ θ S) (h3 : Step3Out S) :
    PrecMax StepPt.L S (Λ := fun _ q => Word 2 q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => 5 * q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2) := by
  obtain ⟨W₁, hW₁⟩ := step45_good R c N hc hN S hS
  have hp := h2.pair 1 one_pos
  have hwt : ∀ W, W₁ ≤ W → ∀ q ∈ S W, ∀ d : ℕ, q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2 *
      weightFn cp₂ θ 1 W (ellProp q.g q.L q.u) d ≤
        2 * q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2 := by
    intro W hW q hq d
    have hg := hW₁ W hW q hq
    have hWr : (1 : ℝ) ≤ W := by exact_mod_cast (by have := hg.W3; omega : 1 ≤ W)
    have hw2 : weightFn cp₂ θ 1 W (ellProp q.g q.L q.u) d ≤ 2 := by
      unfold weightFn
      have hd : 0 ≤ (d : ℝ) / ellProp q.g q.L q.u :=
        div_nonneg (Nat.cast_nonneg _) (by linarith [hg.ell1])
      have he : Real.exp (-(cp₂ * ((d : ℝ) / ellProp q.g q.L q.u) ^ θ)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_nonpos]
        exact mul_nonneg hcp₂.le (Real.rpow_nonneg hd _)
      have hw : (W : ℝ) ^ (-(1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hWr (by norm_num)
      linarith
    have h0 : 0 ≤ q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2 := by positivity
    calc q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2 * weightFn cp₂ θ 1 W (ellProp q.g q.L q.u) d
        ≤ q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2 * 2 := mul_le_mul_of_nonneg_left hw2 h0
      _ = 2 * q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2 := by ring
  have P1 : PrecMax StepPt.L S (Λ := fun _ q => Word 2 q.L)
      (fun W q w ω => if w.2 0 = true ∧ w.2 1 = false then flowErr W (q.at q.u) w.1 w.2 ω
        else 0)
      (fun W q _ => 2 * q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2) := by
    refine step45_relabel hp (fun _ _ w => (w.1 0, w.1 1)) W₁ ?_
      (fun W hW q hq w => hwt W hW q hq _)
    intro W hW q hq w ω
    exact step45_P1 W (q.at q.u) w.1 w.2 ω
  have P2 : PrecMax StepPt.L S (Λ := fun _ q => Word 2 q.L)
      (fun W q w ω => if w.2 0 = false ∧ w.2 1 = true then flowErr W (q.at q.u) w.1 w.2 ω
        else 0)
      (fun W q _ => 2 * q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2) := by
    refine step45_relabel hp (fun _ _ w => (w.1 1, w.1 0)) W₁ ?_
      (fun W hW q hq w => hwt W hW q hq _)
    intro W hW q hq w ω
    exact step45_P2 W (q.at q.u) w.1 w.2 ω
  have P3 : PrecMax StepPt.L S (Λ := fun _ q => Word 2 q.L)
      (fun W q w ω => if w.2 0 = w.2 1 then flowErr W (q.at q.u) w.1 w.2 ω else 0)
      (fun W q _ => q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2) := by
    refine step45_relabel h3.same (fun _ _ w => (w.1 0, w.1 1, w.2 0)) W₁ ?_ ?_
    · intro W hW q hq w ω
      exact step45_P3 W (q.at q.u) w.1 w.2 ω
    · intro W hW q hq w
      have hR1 := (hW₁ W hW q hq).R1
      have h76 : q.ratio ^ ((7 : ℝ) / 2) ≤ q.ratio ^ 6 := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
      exact mul_le_mul_of_nonneg_right h76 (by positivity)
  have P12 := PrecMax.add P1 P2 (fun W q _ => by positivity) (fun W q _ => by positivity)
  have P123 := PrecMax.add P12 P3 (fun W q _ => by positivity) (fun W q _ => by positivity)
  refine step45_relabel P123 (fun _ _ w => w) W₁ ?_ ?_
  · intro W _ q _ w ω
    exact step45_P123 W (q.at q.u) w.1 w.2 ω
  · intro W hW q hq w
    apply le_of_eq
    ring

/-! ### Step 4 -/

/-- `Ψ_2 = 4 + 25R^{12}ζ_t` for `E_1 = 1`, `E_2 = 5R^6` and `B ≡ 1`. -/
private lemma step45_env_two (r ζ : ℝ) :
    nodeEnv 2 (fun j => if j = 2 then 5 * r ^ 6 else 1) (fun _ => 1) ζ =
      4 + 25 * (r ^ 12 * ζ) := by
  unfold nodeEnv
  rw [show Finset.Ico 1 2 = {1} by decide, show Finset.Icc 2 2 = {2} by decide]
  simp only [Finset.sum_singleton, Real.sqrt_one]
  norm_num
  ring

/-- The right side of (C.36) [gc:eq:recurrence] at length `n ≥ 3` with `E_j = 1` for `j < n`,
`E_n = Y ≥ 1`, `B ≡ 1` and `ζY ≤ 1` is at most `2n + 3`. -/
private lemma step45_env_high (n : ℕ) (hn : 3 ≤ n) (Y ζ : ℝ) (hY : 1 ≤ Y) (hζ : 0 ≤ ζ)
    (hζY : ζ * Y ≤ 1) :
    nodeEnv n (fun j => if j < n then 1 else Y) (fun _ => 1) ζ ≤ 2 * n + 3 := by
  unfold nodeEnv
  have h1 : ∑ j ∈ Finset.Ico 1 n, (if j < n then (1 : ℝ) else Y) ≤ n := by
    calc ∑ j ∈ Finset.Ico 1 n, (if j < n then (1 : ℝ) else Y) = ∑ _j ∈ Finset.Ico 1 n, (1 : ℝ) :=
          Finset.sum_congr rfl (fun j hj => by simp [(Finset.mem_Ico.mp hj).2])
      _ ≤ n := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico]
          exact_mod_cast Nat.sub_le n 1
  have h2 : ∑ p ∈ Finset.Icc 2 n, (if p < n then (1 : ℝ) else Y) *
      (if n + 2 - p < n then 1 else Y) ≤ n * Y := by
    have hb : ∀ p ∈ Finset.Icc 2 n, (if p < n then (1 : ℝ) else Y) *
        (if n + 2 - p < n then 1 else Y) ≤ Y := by
      intro p hp
      rw [Finset.mem_Icc] at hp
      by_cases ha : p < n <;> by_cases hb : n + 2 - p < n
      · simp only [ha, hb, ↓reduceIte, mul_one]; exact hY
      · simp only [ha, hb, ↓reduceIte, one_mul]; exact le_rfl
      · simp only [ha, hb, ↓reduceIte, mul_one]; exact le_rfl
      · omega
    refine (Finset.sum_le_card_nsmul _ _ _ hb).trans ?_
    rw [nsmul_eq_mul, Nat.card_Icc]
    have : ((n + 1 - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n + 1 - 2 ≤ n)
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have h3 : ζ * (n * Y) ≤ n := by
    calc ζ * (n * Y) = n * (ζ * Y) := by ring
      _ ≤ n * 1 := mul_le_mul_of_nonneg_left hζY (Nat.cast_nonneg n)
      _ = n := mul_one _
  have h4 : ζ * ∑ p ∈ Finset.Icc 2 n, (if p < n then (1 : ℝ) else Y) *
      (if n + 2 - p < n then 1 else Y) ≤ n :=
    (mul_le_mul_of_nonneg_left h2 hζ).trans h3
  simp only [show 1 < n by omega, ↓reduceIte, Real.sqrt_one, one_mul]
  linarith

/-- Length two: one node with `E_1 = 1`, `E_2 = 5R^6`, `B ≡ 1`, and `R^{12}ζ_t ≤ 1`. -/
private lemma step45_len2 (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N cp₂ : ℝ)
    (hc : 0 < c) (hcp₂ : 0 < cp₂) (hN : 20 ≤ N) (hinc : IncrementInput R.base R.J)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (hSu : ∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
      (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W)
    (hin : OneStepInput cp θ (fun q : StepPt => q.at q.s) S)
    (h2 : Step2Out cp₂ θ S) (h3 : Step3Out S) :
    PrecMax StepPt.L S (Λ := fun _ q => Word 2 q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => zetaProp q.g W q.L q.u ^ 2) := by
  obtain ⟨W₁, hW₁⟩ := step45_good R c N hc hN S hS
  have hb1 := step45_base1 R c N cp₂ θ hc hN S hS h2
  have hb2 := step45_base2 R c N cp₂ θ hc hN hcp₂ S hS h2 h3
  have hnode := step3_node R I c N cp θ hinc S hS hSu hin h3.tail 2 le_rfl
    (fun j _ q => if j = 2 then 5 * q.ratio ^ 6 else 1) (fun _ _ _ => 1)
    (fun j W q => by split_ifs <;> positivity) (fun _ _ _ => zero_le_one)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun j hj1 hj2 => by
      rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
      · exact PrecMax.mono hb1 fun W q _ _ => by simp
      · exact PrecMax.mono hb2 fun W q _ _ => by simp)
    (fun j hj => by simpa using h3.loop j (by omega))
  refine step45_absorb (fun _ => (29 : ℝ)) (fun δ hδ => step45_const_le 29 δ hδ) ?_ W₁
    (fun W hW q hq _ => pow_nonneg (by linarith [(hW₁ W hW q hq).zs, (hW₁ W hW q hq).zsu]) _)
  refine step45_relabel hnode (fun _ _ w => w) W₁ (fun _ _ _ _ _ _ => le_rfl) ?_
  intro W hW q hq w
  have hg := hW₁ W hW q hq
  have henv := step45_env_two q.ratio (zetaProp q.g W q.L q.t)
  rw [henv]
  have hz : 0 ≤ zetaProp q.g W q.L q.u ^ 2 := by positivity
  have := hg.R12
  nlinarith

/-- Length `n ≥ 3`: one node with `E_j = 1` for `j < n` (the shorter lengths), `E_n = ζ_s^{-1/2}`
from (C.28) [fo:eq:step3-error], `B ≡ 1` from (C.27) [fo:eq:step3], and `ζ_tζ_s^{-1/2} ≤ 1`. -/
private lemma step45_high (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N : ℝ)
    (hc : 0 < c) (hN : 20 ≤ N) (hinc : IncrementInput R.base R.J)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (hSu : ∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
      (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W)
    (hin : OneStepInput cp θ (fun q : StepPt => q.at q.s) S) (h3 : Step3Out S)
    (n : ℕ) (hn : 3 ≤ n)
    (hlow : ∀ j : ℕ, 1 ≤ j → j < n → PrecMax StepPt.L S (Λ := fun _ q => Word j q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => zetaProp q.g W q.L q.u ^ j)) :
    PrecMax StepPt.L S (Λ := fun _ q => Word n q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => zetaProp q.g W q.L q.u ^ n) := by
  obtain ⟨W₁, hW₁⟩ := step45_good R c N hc hN S hS
  have hnode := step3_node R I c N cp θ hinc S hS hSu hin h3.tail n (by omega)
    (fun j W q => if j < n then 1 else (Real.sqrt (zetaProp q.g W q.L q.s))⁻¹) (fun _ _ _ => 1)
    (fun j W q => by
      split_ifs
      exacts [zero_le_one, inv_nonneg.2 (Real.sqrt_nonneg _)])
    (fun _ _ _ => zero_le_one) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun j hj1 hjn => by
      by_cases h : j < n
      · exact PrecMax.mono (hlow j hj1 h) fun W q _ _ => by simp [h]
      · have hj : j = n := by omega
        subst hj
        exact PrecMax.mono (h3.err j hj1) fun W q _ _ => by simp)
    (fun j hj => by simpa using h3.loop j (by omega))
  refine step45_absorb (fun _ => (2 * n + 3 : ℝ))
    (fun δ hδ => step45_const_le (2 * n + 3) δ hδ) ?_ W₁
    (fun W hW q hq _ => pow_nonneg (by linarith [(hW₁ W hW q hq).zs, (hW₁ W hW q hq).zsu]) _)
  refine step45_relabel hnode (fun _ _ w => w) W₁ (fun _ _ _ _ _ _ => le_rfl) ?_
  intro W hW q hq w
  have hg := hW₁ W hW q hq
  set ζs := zetaProp q.g W q.L q.s
  set ζt := zetaProp q.g W q.L q.t
  have hsq : 0 < Real.sqrt ζs := Real.sqrt_pos.2 hg.zs
  have hY : 1 ≤ (Real.sqrt ζs)⁻¹ := by
    rw [one_le_inv₀ hsq]
    calc Real.sqrt ζs ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hg.zs1
      _ = 1 := Real.sqrt_one
  have hζt : 0 ≤ ζt := by linarith [hg.zs, hg.zsu, hg.zut]
  have hζY : ζt * (Real.sqrt ζs)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hsq]
    calc ζt = Real.sqrt (ζt ^ 2) := (Real.sqrt_sq hζt).symm
      _ ≤ Real.sqrt ζs := Real.sqrt_le_sqrt (by nlinarith [hg.tt])
  have henv := step45_env_high n hn _ ζt hY hζt hζY
  have hz : 0 ≤ zetaProp q.g W q.L q.u ^ n := pow_nonneg (by linarith [hg.zs, hg.zsu]) _
  calc zetaProp q.g W q.L q.u ^ n *
        nodeEnv n (fun j => if j < n then 1 else (Real.sqrt ζs)⁻¹) (fun _ => 1) ζt
      ≤ zetaProp q.g W q.L q.u ^ n * (2 * n + 3) := mul_le_mul_of_nonneg_left henv hz
    _ = (2 * n + 3) * zetaProp q.g W q.L q.u ^ n := mul_comm _ _

/-- Step 4 of Appendix C.3 [sec:gc-one-step] at fixed times: (C.42) [fo:eq:step4]
`|D_k(u)| ≺ ζ_u^k`, through the two sharpenings (C.43) [fo:eq:two-loop-sharpening] at length two
and induction on the length. -/
theorem step4 (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N cp₂ : ℝ) (hc : 0 < c)
    (hcp₂ : 0 < cp₂) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hN : lemmaNN0 I.Cw ≤ N)
    (hinc : IncrementInput R.base R.J)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (hSu : ∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
      (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W)
    (hin : OneStepInput cp θ (fun q : StepPt => q.at q.s) S)
    (hcmp : OneStepInput cp θ (fun q : StepPt => cmpPt (q.at q.u) q.s) S)
    (h1 : Step1Out S) (h2 : Step2Out cp₂ θ S) (h3 : Step3Out S) :
    ∀ k : ℕ, 1 ≤ k → PrecMax StepPt.L S (Λ := fun _ q => Word k q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => zetaProp q.g W q.L q.u ^ k) := by
  have hN20 : (20 : ℝ) ≤ N := le_trans (le_max_left _ _) hN
  have key : ∀ n k : ℕ, 1 ≤ k → k ≤ n → PrecMax StepPt.L S (Λ := fun _ q => Word k q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => zetaProp q.g W q.L q.u ^ k) := by
    intro n
    induction n with
    | zero => intro k hk1 hk0; omega
    | succ n ih =>
      intro k hk1 hkn
      by_cases hkn' : k ≤ n
      · exact ih k hk1 hkn'
      · rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
        · exact step45_base1 R c N cp₂ θ hc hN20 S hS h2
        · exact step45_len2 R I c cp θ N cp₂ hc hcp₂ hN20 hinc S hS hSu hin h2 h3
        · exact step45_high R I c cp θ N hc hN20 hinc S hS hSu hin h3 k hk3
            (fun j hj1 hjk => ih j hj1 (by omega))
  exact fun k hk => key k k hk le_rfl

/-! ### Step 5: the spatial profile -/

/-- `min(a, b + c) ≤ min(a, b) + c` for `c ≥ 0`. -/
private lemma step45_min_add (a b c : ℝ) (hc : 0 ≤ c) : min a (b + c) ≤ min a b + c := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]; exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right h]; exact min_le_right _ _

/-- The deterministic part of (C.44) [fo:eq:step5]: the minimum of the Step 4 bound `ζ_u^2` and
the Step 2 bound `R^6ζ_u^2(e^{-c_p x^θ} + W^{-F-18})` is at most `e^{C'√(log W)}` times
`ζ_u^2(e^{-c'x^{θ/2}} + W^{-F})`, by the profile minimum (A.56) [da:eq:profile-minimum]. -/
private lemma step45_pair_det (cp₂ θ c' C' F : ℝ) (hC' : 0 < C') (W : ℕ) (hW : 3 ≤ W)
    (R ℓ d z : ℝ) (hR1 : 1 ≤ R) (hRW : R ≤ (W : ℝ) ^ 3) (hz : 0 ≤ z)
    (hprof : min 1 (R ^ 10 * Real.exp (-(cp₂ * (d / ℓ) ^ θ))) ≤
      Real.exp (C' * Real.sqrt (Real.log W)) * Real.exp (-(c' * (d / ℓ) ^ (θ / 2)))) :
    min z (R ^ 6 * z * weightFn cp₂ θ (F + 18) W ℓ d) ≤
      Real.exp (C' * Real.sqrt (Real.log W)) * (z * weightFn c' (θ / 2) F W ℓ d) := by
  unfold weightFn
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  set e := Real.exp (-(cp₂ * (d / ℓ) ^ θ))
  set e' := Real.exp (-(c' * (d / ℓ) ^ (θ / 2)))
  set E := Real.exp (C' * Real.sqrt (Real.log W))
  have he : 0 ≤ e := Real.exp_nonneg _
  have he' : 0 ≤ e' := Real.exp_nonneg _
  have hE : 1 ≤ E := Real.one_le_exp (mul_nonneg hC'.le (Real.sqrt_nonneg _))
  have hwF : 0 ≤ (W : ℝ) ^ (-F) := Real.rpow_nonneg hWpos.le _
  have hR0 : 0 ≤ R := by linarith
  have h18 : (W : ℝ) ^ (-(F + 18)) = (W : ℝ) ^ (-F) * ((W : ℝ) ^ 18)⁻¹ := by
    rw [show -(F + 18) = -F + -18 by ring, Real.rpow_add hWpos, Real.rpow_neg hWpos.le 18,
      show (18 : ℝ) = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hR6 : R ^ 6 ≤ (W : ℝ) ^ 18 := by
    calc R ^ 6 ≤ ((W : ℝ) ^ 3) ^ 6 := pow_le_pow_left₀ hR0 hRW 6
      _ = (W : ℝ) ^ 18 := by rw [← pow_mul]
  have hW18 : 0 < (W : ℝ) ^ 18 := by positivity
  have hRw : R ^ 6 * (W : ℝ) ^ (-(F + 18)) ≤ (W : ℝ) ^ (-F) := by
    rw [h18]
    calc R ^ 6 * ((W : ℝ) ^ (-F) * ((W : ℝ) ^ 18)⁻¹)
        = (W : ℝ) ^ (-F) * (R ^ 6 * ((W : ℝ) ^ 18)⁻¹) := by ring
      _ ≤ (W : ℝ) ^ (-F) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hwF
          rw [← div_eq_mul_inv, div_le_one hW18]; exact hR6
      _ = (W : ℝ) ^ (-F) := mul_one _
  have h6 : R ^ 6 ≤ R ^ 10 := pow_le_pow_right₀ hR1 (by norm_num)
  have hmin : min 1 (R ^ 6 * e) ≤ E * e' :=
    (min_le_min_left 1 (mul_le_mul_of_nonneg_right h6 he)).trans hprof
  have hw18 : 0 ≤ (W : ℝ) ^ (-(F + 18)) := Real.rpow_nonneg hWpos.le _
  calc min z (R ^ 6 * z * (e + (W : ℝ) ^ (-(F + 18))))
      = min z (R ^ 6 * z * e + z * (R ^ 6 * (W : ℝ) ^ (-(F + 18)))) := by ring_nf
    _ ≤ min z (R ^ 6 * z * e) + z * (R ^ 6 * (W : ℝ) ^ (-(F + 18))) :=
        step45_min_add _ _ _ (by positivity)
    _ = z * min 1 (R ^ 6 * e) + z * (R ^ 6 * (W : ℝ) ^ (-(F + 18))) := by
        rw [mul_min_of_nonneg _ _ hz, mul_one]; ring_nf
    _ ≤ z * (E * e') + z * (W : ℝ) ^ (-F) :=
        add_le_add (mul_le_mul_of_nonneg_left hmin hz) (mul_le_mul_of_nonneg_left hRw hz)
    _ ≤ z * (E * e') + E * (z * (W : ℝ) ^ (-F)) := by
        have : 0 ≤ z * (W : ℝ) ^ (-F) := mul_nonneg hz hwF
        nlinarith
    _ = E * (z * (e' + (W : ℝ) ^ (-F))) := by ring

/-- (C.44) [fo:eq:step5]: the minimum of Step 4 at length two and the mixed pair of Step 2 with
`F + 18`, then the profile minimum (A.56) [da:eq:profile-minimum]. -/
private lemma step45_pair (R : PropRegime) (c N cp₂ θ : ℝ) (hc : 0 < c) (hN : 20 ≤ N)
    (c' C' : ℝ) (hC' : 0 < C')
    (hprof : ∀ W : ℕ, 3 ≤ W → ∀ R x : ℝ, 1 ≤ R → R ≤ (W : ℝ) ^ 3 → 0 ≤ x →
      min 1 (R ^ 10 * Real.exp (-(cp₂ * x ^ θ))) ≤
        Real.exp (C' * Real.sqrt (Real.log W)) * Real.exp (-(c' * x ^ (θ / 2))))
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) (h2 : Step2Out cp₂ θ S)
    (h4 : PrecMax StepPt.L S (Λ := fun _ q => Word 2 q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => zetaProp q.g W q.L q.u ^ 2)) (F : ℝ) (hF : 0 < F) :
    PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
      (fun W q ab ω => flowErr W (q.at q.u) ![ab.1, ab.2] ![true, false] ω)
      (fun W q ab => zetaProp q.g W q.L q.u ^ 2 *
        weightFn c' (θ / 2) F W (ellProp q.g q.L q.u) (cycDist ab.1 ab.2)) := by
  obtain ⟨W₁, hW₁⟩ := step45_good R c N hc hN S hS
  have hA := h2.pair (F + 18) (by linarith)
  have hB : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
      (fun W q ab ω => flowErr W (q.at q.u) ![ab.1, ab.2] ![true, false] ω)
      (fun W q _ => zetaProp q.g W q.L q.u ^ 2) :=
    step45_relabel h4 (fun _ _ ab => (![ab.1, ab.2], ![true, false])) 0
      (fun _ _ _ _ _ _ => le_rfl) (fun _ _ _ _ _ => le_rfl)
  have hM := step45_min hB hA
  refine step45_absorb (fun W => Real.exp (C' * Real.sqrt (Real.log W)))
    (fun δ hδ => step45_expSqrtLog_le C' δ hδ) ?_ W₁ ?_
  · refine step45_relabel hM (fun _ _ ab => ab) W₁ (fun _ _ _ _ _ _ => le_rfl) ?_
    intro W hW q hq ab
    have hg := hW₁ W hW q hq
    have hz : 0 ≤ zetaProp q.g W q.L q.u ^ 2 := by positivity
    have hx : 0 ≤ (cycDist ab.1 ab.2 : ℝ) / ellProp q.g q.L q.u :=
      div_nonneg (Nat.cast_nonneg _) (by linarith [hg.ell1])
    exact step45_pair_det cp₂ θ c' C' F hC' W hg.W3 q.ratio (ellProp q.g q.L q.u)
      (cycDist ab.1 ab.2) _ hg.R1 hg.RW hz (hprof W hg.W3 q.ratio _ hg.R1 hg.RW hx)
  · intro W hW q hq ab
    unfold weightFn
    have hWpos : (0 : ℝ) < W := by exact_mod_cast (by have := (hW₁ W hW q hq).W3; omega : 0 < W)
    have : 0 ≤ (W : ℝ) ^ (-F) := Real.rpow_nonneg hWpos.le _
    positivity

/-! ### Vectors, Hilbert–Schmidt and operator norms -/

section LinAlg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Squared Euclidean norm of a vector. -/
private def step45_nsq (x : n → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

/-- Squared Hilbert–Schmidt norm of a square matrix. -/
private def step45_hs (A : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

omit [DecidableEq n] in
private lemma step45_hs_nonneg (A : Matrix n n ℂ) : 0 ≤ step45_hs A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

open scoped Matrix.Norms.L2Operator

omit [DecidableEq n] in
/-- `‖A u‖² ≤ ‖A‖²_HS ‖u‖²`. -/
private lemma step45_nsq_le_hs (A : Matrix n n ℂ) (u : n → ℂ) :
    step45_nsq (A *ᵥ u) ≤ step45_hs A * step45_nsq u := by
  unfold step45_nsq step45_hs
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : ‖(A *ᵥ u) i‖ ≤ ∑ j, ‖A i j‖ * ‖u j‖ := by
    simp only [Matrix.mulVec, dotProduct]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  calc ‖(A *ᵥ u) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖u j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- The operator norm is at most the Hilbert–Schmidt norm. -/
private lemma step45_opNorm_sq_le_hs (A : Matrix n n ℂ) : ‖A‖ ^ 2 ≤ step45_hs A := by
  have hK : 0 ≤ Real.sqrt (step45_hs A) := Real.sqrt_nonneg _
  have hop : ‖A‖ ≤ Real.sqrt (step45_hs A) := by
    rw [Matrix.cstar_norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
    have h1 : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ^ 2 = step45_nsq (A *ᵥ x.ofLp) := by
      rw [EuclideanSpace.norm_sq_eq]; rfl
    have h2 : ‖x‖ ^ 2 = step45_nsq x.ofLp := by
      rw [EuclideanSpace.norm_sq_eq]; rfl
    have h3 := step45_nsq_le_hs A x.ofLp
    rw [← h1, ← h2] at h3
    have h4 : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ^ 2 ≤
        (Real.sqrt (step45_hs A) * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (step45_hs_nonneg _)]; exact h3
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h4
  calc ‖A‖ ^ 2 ≤ Real.sqrt (step45_hs A) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hop 2
    _ = _ := Real.sq_sqrt (step45_hs_nonneg _)

/-- For a Hermitian matrix, `‖A^(2^j)‖ = ‖A‖^(2^j)`. -/
private lemma step45_norm_pow_two_pow {A : Matrix n n ℂ} (hA : A.IsHermitian) (j : ℕ) :
    ‖A ^ (2 ^ j)‖ = ‖A‖ ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hH : (A ^ (2 ^ j))ᴴ = A ^ (2 ^ j) := by
      rw [Matrix.conjTranspose_pow, hA.eq]
    have e : A ^ (2 ^ (j + 1)) = (A ^ (2 ^ j))ᴴ * A ^ (2 ^ j) := by
      rw [hH, ← pow_add, pow_succ, mul_two]
    rw [e, Matrix.l2_opNorm_conjTranspose_mul_self, ih, ← pow_add, pow_succ 2 j, mul_two]

omit [DecidableEq n] in
/-- `Tr(Z* Z) = ‖Z‖²_HS`. -/
private lemma step45_trace_conjTranspose_mul_self (Z : Matrix n n ℂ) :
    (Zᴴ * Z).trace = ((step45_hs Z : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, step45_hs]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj']

/-- Positive loops bound the operator norm: `‖B‖^(2·2^j) ≤ Tr((B B*)^(2^j))`, and the trace is
real. -/
private lemma step45_opNorm_pow_le_trace (B : Matrix n n ℂ) (j : ℕ) :
    ((B * Bᴴ) ^ (2 ^ j)).trace = ((((B * Bᴴ) ^ (2 ^ j)).trace.re : ℝ) : ℂ) ∧
      ‖B‖ ^ (2 * 2 ^ j) ≤ ((B * Bᴴ) ^ (2 ^ j)).trace.re := by
  have hA : (B * Bᴴ).IsHermitian := by
    unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hnA : ‖B * Bᴴ‖ = ‖B‖ ^ 2 := by
    have := Matrix.l2_opNorm_conjTranspose_mul_self Bᴴ
    rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at this
    rw [this, sq]
  obtain ⟨Z, hZ, hnZ⟩ : ∃ Z : Matrix n n ℂ, (B * Bᴴ) ^ (2 ^ j) = Zᴴ * Z ∧
      ‖Z‖ ^ 2 = ‖B‖ ^ (2 * 2 ^ j) := by
    cases j with
    | zero =>
      refine ⟨Bᴴ, by simp, ?_⟩
      rw [Matrix.l2_opNorm_conjTranspose]; norm_num
    | succ j =>
      refine ⟨(B * Bᴴ) ^ (2 ^ j), ?_, ?_⟩
      · rw [Matrix.conjTranspose_pow, hA.eq, ← pow_add, pow_succ 2 j, mul_two]
      · rw [step45_norm_pow_two_pow hA, hnA, ← pow_mul, ← pow_mul, pow_succ 2 j]
  rw [hZ, step45_trace_conjTranspose_mul_self, Complex.ofReal_re]
  exact ⟨rfl, hnZ ▸ step45_opNorm_sq_le_hs Z⟩

end LinAlg

/-! ### Loops as traces of block products -/

section Loops

variable {W L : ℕ}

/-- The matrix whose block `(a, b)` is `B` and whose other blocks vanish. -/
private def step45_emb (a b : Fin L) (B : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.of fun x y => if x.1 = a ∧ y.1 = b then B x.2 y.2 else 0

/-- The projection `P_a` onto block `a`. -/
private def step45_proj (a : Fin L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.diagonal fun p => if p.1 = a then 1 else 0

private lemma step45_blockE_eq (a : Fin L) :
    blockE W L a = ((W : ℂ)⁻¹) • (step45_proj a : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy; by_cases h : x.1 = a <;> simp [blockE, step45_proj, h]
  · simp [blockE, step45_proj, Matrix.diagonal_apply_ne _ hxy]

private lemma step45_proj_eq_emb (a : Fin L) :
    (step45_proj a : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) = step45_emb a a 1 := by
  ext x y
  by_cases hxy : x = y
  · subst hxy; by_cases h : x.1 = a <;> simp [step45_emb, step45_proj, h]
  · simp only [step45_proj, Matrix.diagonal_apply_ne _ hxy, step45_emb, Matrix.of_apply]
    by_cases h1 : x.1 = a
    · by_cases h2 : y.1 = a
      · have h3 : x.2 ≠ y.2 := fun h => hxy (Prod.ext (h1.trans h2.symm) h)
        simp [h1, h2, Matrix.one_apply_ne h3]
      · simp [h2]
    · simp [h1]

private lemma step45_emb_mul (a b c : Fin L) (A B : Matrix (Fin W) (Fin W) ℂ) :
    step45_emb a b A * step45_emb b c B = step45_emb a c (A * B) := by
  ext x y
  simp only [step45_emb, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · by_cases hx : x.1 = a <;> by_cases hy : y.1 = c <;> simp [hx, hy]
  · intro e _ he; simp [he]
  · simp

private lemma step45_proj_mul_proj (a : Fin L) :
    (step45_proj a : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) * step45_proj a = step45_proj a := by
  rw [step45_proj_eq_emb, step45_emb_mul, Matrix.one_mul]

private lemma step45_proj_mul_mul_proj (a b : Fin L)
    (Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    step45_proj a * Y * step45_proj b = step45_emb a b (blockOf Y a b) := by
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  simp only [step45_proj, Matrix.diagonal_mul, Matrix.mul_diagonal, step45_emb, Matrix.of_apply,
    blockOf]
  by_cases hx : x1 = a <;> by_cases hy : y1 = b
  · subst hx; subst hy; simp
  all_goals simp [hx, hy]

private lemma step45_trace_emb (a : Fin L) (B : Matrix (Fin W) (Fin W) ℂ) :
    (step45_emb a a B).trace = B.trace := by
  simp only [Matrix.trace, Matrix.diag, step45_emb, Matrix.of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp
  · intro e _ he; simp [he]
  · simp

/-- The product of the blocks `Y_{c, a_1}, Y_{a_1, a_2}, …` along a list of pairs `(Y, a)`. -/
private def step45_chain : Fin L → List (Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ × Fin L) →
    Matrix (Fin W) (Fin W) ℂ
  | _, [] => 1
  | c, p :: l => blockOf p.1 c p.2 * step45_chain p.2 l

/-- The last label of a list of pairs (the start `c` if the list is empty). -/
private def step45_endLabel : Fin L → List (Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ × Fin L) →
    Fin L
  | c, [] => c
  | _, p :: l => step45_endLabel p.2 l

private lemma step45_endLabel_append (c : Fin L)
    (l : List (Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ × Fin L))
    (p : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ × Fin L) :
    step45_endLabel c (l ++ [p]) = p.2 := by
  induction l generalizing c with
  | nil => rfl
  | cons q l ih => exact ih q.2

private lemma step45_proj_mul_prod (c : Fin L)
    (l : List (Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ × Fin L)) :
    step45_proj c * (l.map fun p => p.1 * blockE W L p.2).prod =
      ((W : ℂ)⁻¹) ^ l.length • step45_emb c (step45_endLabel c l) (step45_chain c l) := by
  induction l generalizing c with
  | nil => simp [step45_endLabel, step45_chain, step45_proj_eq_emb]
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, step45_endLabel, step45_chain]
    set R := (List.map (fun p => p.1 * blockE W L p.2) l).prod with hR
    have e1 : step45_proj c * (p.1 * step45_proj p.2 * R) =
        (step45_proj c * p.1 * step45_proj p.2) * (step45_proj p.2 * R) := by
      rw [← Matrix.mul_assoc (step45_proj c * p.1 * step45_proj p.2),
        Matrix.mul_assoc (step45_proj c * p.1) (step45_proj p.2), step45_proj_mul_proj]
      simp only [Matrix.mul_assoc]
    rw [step45_blockE_eq]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, ih p.2, step45_proj_mul_mul_proj, Matrix.mul_smul, step45_emb_mul, smul_smul, pow_succ']

/-- A loop of length `k + 1` is `W^{-(k+1)}` times the trace of the product of its blocks
`(X^{σ_i})_{a_{i-1} a_i}`, with `a_{-1} = a_k`. -/
private lemma step45_loopTr_eq_chain (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {k : ℕ}
    (a : Fin (k + 1) → Fin L) (σ : Fin (k + 1) → Bool) :
    loopTr X a σ = ((W : ℂ)⁻¹) ^ (k + 1) *
      (step45_chain (a (Fin.last k)) (List.ofFn fun i => (sgnMat X (σ i), a i))).trace := by
  set c := a (Fin.last k) with hc
  set M := (List.ofFn fun i => sgnMat X (σ i) * blockE W L (a i)).prod with hM
  have hMl : M = ((List.ofFn fun i => (sgnMat X (σ i), a i)).map
      fun p => p.1 * blockE W L p.2).prod := by
    rw [hM, List.map_ofFn]; rfl
  have hMP : M * step45_proj c = M := by
    rw [hM, List.ofFn_succ', List.prod_concat, Matrix.mul_assoc, Matrix.mul_assoc,
      step45_blockE_eq, Matrix.smul_mul, step45_proj_mul_proj]
  have htr : loopTr X a σ = (step45_proj c * M).trace := by
    unfold loopTr
    rw [← hM, Matrix.trace_mul_comm, hMP]
  have hend : step45_endLabel c (List.ofFn fun i => (sgnMat X (σ i), a i)) = c := by
    rw [List.ofFn_succ', List.concat_eq_append, step45_endLabel_append]
  rw [htr, hMl, step45_proj_mul_prod, hend, Matrix.trace_smul, step45_trace_emb, List.length_ofFn,
    smul_eq_mul]

private lemma step45_blockOf_conjTranspose (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (e f : Fin L) : blockOf Xᴴ e f = (blockOf X f e)ᴴ := by
  ext α β; simp [blockOf, Matrix.conjTranspose_apply]

/-- The alternating chain `X_{cd}, X*_{dc}, …` of length `2p` is `(B B*)^p`, `B = X_{cd}`. -/
private lemma step45_chain_alt (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c d : Fin L) :
    ∀ p : ℕ, step45_chain c (List.ofFn fun i : Fin (2 * p) =>
      if i.val % 2 = 0 then (X, d) else (Xᴴ, c)) =
        (blockOf X c d * (blockOf X c d)ᴴ) ^ p
  | 0 => by simp [step45_chain]
  | p + 1 => by
    have ih := step45_chain_alt X c d p
    have e : (List.ofFn fun i : Fin (2 * (p + 1)) => if i.val % 2 = 0 then (X, d) else (Xᴴ, c)) =
        (X, d) :: (Xᴴ, c) :: List.ofFn fun i : Fin (2 * p) =>
          if i.val % 2 = 0 then (X, d) else (Xᴴ, c) := by
      rw [List.ofFn_succ (n := 2 * p + 1), List.ofFn_succ]
      simp only [Fin.val_zero, Nat.zero_mod, ↓reduceIte, Fin.val_succ]
      congr 2
      congr 1
      funext i
      have h2 : (i.val + 1 + 1) % 2 = 0 ↔ i.val % 2 = 0 := by omega
      simp only [h2]
    rw [e]
    simp only [step45_chain]
    rw [ih, step45_blockOf_conjTranspose, pow_succ', Matrix.mul_assoc]

end Loops

/-! ### Positive loops and the operator norm -/

section PosLoop

variable {W L : ℕ}

/-- The alternating loop
`ℒ_{2m}(d, c, d, c, …; +, -, +, -, …) = W^{-2m} Tr((X_{cd} X_{cd}^*)^m)`. -/
private lemma step45_loopTr_alt (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c d : Fin L)
    (m : ℕ) (hm : 1 ≤ m) :
    loopTr X (fun i : Fin (2 * m) => if i.val % 2 = 0 then d else c)
        (fun i => decide (i.val % 2 = 0)) =
      ((W : ℂ)⁻¹) ^ (2 * m) * ((blockOf X c d * (blockOf X c d)ᴴ) ^ m).trace := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  rw [step45_loopTr_eq_chain (k := 2 * p + 1)]
  have hlast : (if (Fin.last (2 * p + 1)).val % 2 = 0 then d else c) = c := by
    have h1 : (2 * p + 1) % 2 ≠ 0 := by omega
    simp only [Fin.val_last, h1, ↓reduceIte]
  have hl : (List.ofFn fun i : Fin (2 * p + 1 + 1) =>
      (sgnMat X (decide (i.val % 2 = 0)), if i.val % 2 = 0 then d else c)) =
      List.ofFn fun i : Fin (2 * (p + 1)) => if i.val % 2 = 0 then (X, d) else (Xᴴ, c) := by
    congr 1
    funext i
    by_cases h : i.val % 2 = 0 <;> simp [h, sgnMat]
  rw [hlast, hl, step45_chain_alt, show 2 * p + 1 + 1 = 2 * (p + 1) by ring]

open scoped Matrix.Norms.L2Operator

/-- A bound `T` on the positive `2·2^j`-loops at `(d, c)` gives
`‖X_{cd}‖^{2·2^j} ≤ W^{2·2^j} T`, as in (C.7) [fo:eq:starting-positive-loop]. -/
private lemma step45_opNorm_le_of_loop (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (c d : Fin L) (j : ℕ) (hW : 1 ≤ W) {T : ℝ}
    (h : ‖loopTr X (fun i : Fin (2 * 2 ^ j) => if i.val % 2 = 0 then d else c)
        (fun i => decide (i.val % 2 = 0))‖ ≤ T) :
    ‖blockOf X c d‖ ^ (2 * 2 ^ j) ≤ (W : ℝ) ^ (2 * 2 ^ j) * T := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [step45_loopTr_alt X c d (2 ^ j) Nat.one_le_two_pow] at h
  obtain ⟨hre, hle⟩ := step45_opNorm_pow_le_trace (blockOf X c d) j
  rw [hre, norm_mul, norm_pow, norm_inv, Complex.norm_natCast, Complex.norm_real,
    Real.norm_of_nonneg ((pow_nonneg (norm_nonneg _) _).trans hle)] at h
  have hWp : (0 : ℝ) < (W : ℝ) ^ (2 * 2 ^ j) := pow_pos hW0 _
  calc ‖blockOf X c d‖ ^ (2 * 2 ^ j) ≤ ((blockOf X c d * (blockOf X c d)ᴴ) ^ 2 ^ j).trace.re := hle
    _ = (W : ℝ) ^ (2 * 2 ^ j) * ((W : ℝ)⁻¹ ^ (2 * 2 ^ j) *
          ((blockOf X c d * (blockOf X c d)ᴴ) ^ 2 ^ j).trace.re) := by
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hW0.ne', one_pow, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h hWp.le

end PosLoop

/-! ### Step 5: the operator bound -/

open scoped Matrix.Norms.L2Operator in
/-- (C.46) [fo:eq:operator-regeneration]: the positive loops of length `k = 2·2^j` with
`εk ≥ 3` and (C.27) [fo:eq:step3] give `‖G_{ab}‖^k ≤ W^k · Wζ_u^{k-1}`, and
`ζ_u ≥ (2W)⁻¹` gives `‖G_{ab}‖ ≤ W^ε Wζ_u`. -/
private lemma step45_op (R : PropRegime) (c N : ℝ) (hc : 0 < c) (hN : 20 ≤ N)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) (h3 : Step3Out S) :
    PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
      (fun W q ab ω => ((‖blockOf (flowG W (q.at q.u) ω) ab.1 ab.2‖ : ℝ) : ℂ))
      (fun W q _ => W * zetaProp q.g W q.L q.u) := by
  obtain ⟨W₁, hW₁⟩ := step45_good R c N hc hN S hS
  intro ε D hε hD
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 3 ≤ ε * ((2 * 2 ^ j : ℕ) : ℝ) := by
    obtain ⟨m, hm⟩ := exists_nat_ge (3 / ε)
    refine ⟨m, ?_⟩
    have h1 : (m : ℝ) ≤ ((2 * 2 ^ m : ℕ) : ℝ) := by
      exact_mod_cast ((Nat.lt_two_pow_self).le.trans (by omega) : m ≤ 2 * 2 ^ m)
    rw [div_le_iff₀ hε] at hm
    nlinarith
  obtain ⟨W₀, hW₀⟩ := h3.loop (2 * 2 ^ j)
    (by have := Nat.one_le_two_pow (n := j); omega) 1 D one_pos hD
  refine ⟨max W₀ W₁, fun W hW q hq =>
    (measure_mono ?_).trans (hW₀ W (le_of_max_le_left hW) q hq)⟩
  rintro ω ⟨ab, hab⟩
  have hg := hW₁ W (le_of_max_le_right hW) q hq
  by_contra hcon
  have hl := not_lt.mp fun h => hcon ⟨((fun i : Fin (2 * 2 ^ j) =>
    if i.val % 2 = 0 then ab.2 else ab.1), fun i => decide (i.val % 2 = 0)), h⟩
  have hW1 : 1 ≤ W := by have := hg.W3; omega
  have hb := step45_opNorm_le_of_loop (flowG W (q.at q.u) ω) ab.1 ab.2 j hW1 hl
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hab
  refine absurd hab (not_lt.mpr ?_)
  set k := 2 * 2 ^ j with hk
  set ζ := zetaProp q.g W q.L q.u with hζ
  set B := ‖blockOf (flowG W (q.at q.u) ω) ab.1 ab.2‖ with hB
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW3 : (3 : ℝ) ≤ W := by exact_mod_cast hg.W3
  have hWpos : (0 : ℝ) < W := by linarith
  have hζ0 : 0 < ζ := lt_of_lt_of_le (by positivity) hg.zlow
  have hk0 : k ≠ 0 := by positivity
  have hWε : 0 ≤ (W : ℝ) ^ ε := Real.rpow_nonneg hWpos.le _
  -- `W ≤ W^3 ζ`
  have hWζ : (W : ℝ) ≤ (W : ℝ) ^ 3 * ζ := by
    have h := mul_le_mul_of_nonneg_left hg.zlow (by positivity : (0 : ℝ) ≤ (W : ℝ) ^ 3)
    have e : (W : ℝ) ^ 3 * (2 * (W : ℝ))⁻¹ = (W : ℝ) ^ 2 / 2 := by
      field_simp
    rw [e] at h
    nlinarith
  -- `W^3 ≤ W^{εk}`
  have hW3k : (W : ℝ) ^ 3 ≤ ((W : ℝ) ^ ε) ^ k := by
    rw [← Real.rpow_natCast ((W : ℝ) ^ ε), ← Real.rpow_mul hWpos.le,
      show (W : ℝ) ^ 3 = (W : ℝ) ^ ((3 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
    exact Real.rpow_le_rpow_of_exponent_le hWr (by push_cast; exact hj)
  have hk1 : ζ ^ (k - 1) * ζ = ζ ^ k := by
    rw [← pow_succ]; congr 1; omega
  have hpow : B ^ k ≤ ((W : ℝ) ^ ε * (W * ζ)) ^ k := by
    refine hb.trans ?_
    rw [Real.rpow_one]
    have hζk : 0 ≤ ζ ^ (k - 1) := pow_nonneg hζ0.le _
    have hWk : 0 ≤ (W : ℝ) ^ k := by positivity
    calc (W : ℝ) ^ k * ((W : ℝ) * ζ ^ (k - 1))
        ≤ (W : ℝ) ^ k * (((W : ℝ) ^ 3 * ζ) * ζ ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hWζ hζk) hWk
      _ = (W : ℝ) ^ 3 * ((W : ℝ) ^ k * (ζ ^ (k - 1) * ζ)) := by ring
      _ ≤ ((W : ℝ) ^ ε) ^ k * ((W : ℝ) ^ k * ζ ^ k) := by
          rw [hk1]; exact mul_le_mul_of_nonneg_right hW3k (by positivity)
      _ = ((W : ℝ) ^ ε * (W * ζ)) ^ k := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hk0).mp hpow

open scoped Matrix.Norms.L2Operator in
/-- Step 5 of Appendix C.3 [sec:gc-one-step] at fixed times: the profile minimum (A.56)
[da:eq:profile-minimum] restores the spatial profile (C.44) [fo:eq:step5] with exponent `θ/2`, and
the positive loops give the operator bound (C.46) [fo:eq:operator-regeneration]. -/
theorem step5 (R : PropRegime) (c N cp₂ θ : ℝ) (hc : 0 < c) (hcp₂ : 0 < cp₂) (hθ : 0 < θ)
    (hθ2 : θ ≤ 1 / 2) (hN : 20 ≤ N) :
    ∃ cp' : ℝ, 0 < cp' ∧ ∀ S : ℕ → Set StepPt, (∀ W, S W ⊆ {q | StepAdm R c N W q}) →
      (∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
        (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W) →
      Step2Out cp₂ θ S → Step3Out S →
      (∀ k : ℕ, 1 ≤ k → PrecMax StepPt.L S (Λ := fun _ q => Word k q.L)
        (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
        (fun W q _ => zetaProp q.g W q.L q.u ^ k)) →
      (∀ F : ℝ, 0 < F → PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
        (fun W q ab ω => flowErr W (q.at q.u) ![ab.1, ab.2] ![true, false] ω)
        (fun W q ab => zetaProp q.g W q.L q.u ^ 2 *
          weightFn cp' (θ / 2) F W (ellProp q.g q.L q.u) (cycDist ab.1 ab.2))) ∧
      PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
        (fun W q ab ω => ((‖blockOf (flowG W (q.at q.u) ω) ab.1 ab.2‖ : ℝ) : ℂ))
        (fun W q _ => W * zetaProp q.g W q.L q.u) := by
  obtain ⟨c', C', hc', hC', hprof⟩ := profile_minimum cp₂ θ hcp₂ hθ
  refine ⟨c', hc', fun S hS _ h2 h3 h4 => ⟨fun F hF => ?_, step45_op R c N hc hN S hS h3⟩⟩
  exact step45_pair R c N cp₂ θ hc hN c' C' hC' hprof S hS h2 (h4 2 (by norm_num)) F hF

end LSBA
