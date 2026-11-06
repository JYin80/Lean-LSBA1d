import LSBA.Prop.Step3Tail
import LSBA.Prop.Step3Same
import LSBA.Loop.Projection
import LSBA.Kernel.Tensor
import LSBA.Kernel.Scales
import LSBA.Prop.Increment
import LSBA.Prop.ConeNode

/-!
# Step 3 of the one-step propagation: the cone

The projected error equation (C.35) [fo:eq:projected-error-equation] with the Ward projection
(C.33) [fo:eq:ward-projection], the cone of Step 3 of Appendix C.3 [sec:gc-one-step], and Step 3
assembled from the tails, the same-sign pair and the cone.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Stochastic domination: relabeling, deterministic parts, constants, the chain -/

private lemma step3Cone_two_le (W : ℕ) (hW : 2 ≤ W) (D : ℝ) :
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
private lemma step3Cone_relabel {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι}
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

/-- A dominated quantity plus a quantity bounded by `W^δ Y₂` for every `δ > 0`. -/
private lemma step3Cone_addDet {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι} {Λ : ℕ → ι → Type*}
    {X X₁ : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ}
    {Y₁ Y₂ : (W : ℕ) → (p : ι) → Λ W p → ℝ} (h : PrecMax vol Dom X₁ Y₁)
    (h₂ : ∀ δ : ℝ, 0 < δ → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ p ∈ Dom W, ∀ l ω,
      ‖X W p l ω‖ ≤ ‖X₁ W p l ω‖ + (W : ℝ) ^ δ * Y₂ W p l) :
    PrecMax vol Dom X (fun W p l => Y₁ W p l + Y₂ W p l) := by
  intro ε D hε hD
  obtain ⟨W₀, hW₀⟩ := h (ε / 2) D (by linarith) hD
  obtain ⟨W₂, hW₂⟩ := h₂ (ε / 2) (by linarith)
  refine ⟨max (max W₀ W₂) 1, fun W hW p hp =>
    (measure_mono ?_).trans (hW₀ W (by omega) p hp)⟩
  rintro ω ⟨l, hl⟩
  refine ⟨l, ?_⟩
  by_contra hc
  push Not at hc
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hb := hW₂ W (by omega) p hp l ω
  have hpos : 0 < (W : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos (by linarith) _
  have hle : (W : ℝ) ^ (ε / 2) ≤ (W : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hsum : ‖X W p l ω‖ ≤ (W : ℝ) ^ (ε / 2) * (Y₁ W p l + Y₂ W p l) := by
    rw [mul_add]; linarith
  have hnn : 0 ≤ Y₁ W p l + Y₂ W p l := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg hpos hneg
    linarith [norm_nonneg (X W p l ω)]
  have : ‖X W p l ω‖ ≤ (W : ℝ) ^ ε * (Y₁ W p l + Y₂ W p l) :=
    hsum.trans (mul_le_mul_of_nonneg_right hle hnn)
  exact absurd hl (not_lt.mpr this)

/-- A fixed constant factor in the bound is absorbed by `W^ε`. -/
private lemma step3Cone_const {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι} {Λ : ℕ → ι → Type*}
    {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ} {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ}
    (K : ℝ) (h : PrecMax vol Dom X (fun W p l => K * Y W p l)) (W₁ : ℕ)
    (hY : ∀ W, W₁ ≤ W → ∀ p ∈ Dom W, ∀ l, 0 ≤ Y W p l) : PrecMax vol Dom X Y := by
  intro ε D hε hD
  obtain ⟨W₀, hW₀⟩ := h (ε / 2) D (by linarith) hD
  have ht : Tendsto (fun W : ℕ => (W : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨W₂, hW₂⟩ := eventually_atTop.mp (ht.eventually_ge_atTop K)
  refine ⟨max (max W₀ W₁) (max W₂ 1), fun W hW p hp =>
    (measure_mono ?_).trans (hW₀ W (by omega) p hp)⟩
  rintro ω ⟨l, hl⟩
  refine ⟨l, lt_of_le_of_lt ?_ hl⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hK : K ≤ (W : ℝ) ^ (ε / 2) := hW₂ W (by omega)
  have hYn := hY W (by omega) p hp l
  have hsq : (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) = (W : ℝ) ^ ε := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  calc (W : ℝ) ^ (ε / 2) * (K * Y W p l)
      ≤ (W : ℝ) ^ (ε / 2) * ((W : ℝ) ^ (ε / 2) * Y W p l) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK hYn)
          (Real.rpow_nonneg (by linarith) _)
    _ = (W : ℝ) ^ ε * Y W p l := by rw [← mul_assoc, hsq]

/-- The chain bound (C.40) [gc:eq:chain] under domination: loops of lengths `2l₁` and `2l₂`
bounded by `Y₁` and `Y₂` give loops of length `2(l₁ + l₂)` bounded by `Y₁ Y₂`. -/
private lemma step3Cone_chain (S : ℕ → Set StepPt) (l₁ l₂ : ℕ) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂)
    (Y₁ Y₂ : ℕ → StepPt → ℝ)
    (h₁ : PrecMax StepPt.L S (Λ := fun _ q => Word (2 * l₁) q.L)
      (fun W q w ω => loopTr (flowG W (q.at q.u) ω) w.1 w.2) (fun W q _ => Y₁ W q))
    (h₂ : PrecMax StepPt.L S (Λ := fun _ q => Word (2 * l₂) q.L)
      (fun W q w ω => loopTr (flowG W (q.at q.u) ω) w.1 w.2) (fun W q _ => Y₂ W q)) :
    PrecMax StepPt.L S (Λ := fun _ q => Word (2 * (l₁ + l₂)) q.L)
      (fun W q w ω => loopTr (flowG W (q.at q.u) ω) w.1 w.2) (fun W q _ => Y₁ W q * Y₂ W q) := by
  intro ε D hε hD
  obtain ⟨W₁, hW₁⟩ := h₁ (ε / 2) (D + 1) (by linarith) (by linarith)
  obtain ⟨W₂, hW₂⟩ := h₂ (ε / 2) (D + 1) (by linarith) (by linarith)
  refine ⟨max (max W₁ W₂) 2, fun W hW q hq => ?_⟩
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hsq : (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) = (W : ℝ) ^ ε := by
    rw [← Real.rpow_add hWpos]; congr 1; ring
  have hsub : {ω : Ω W q.L | ∃ w : Word (2 * (l₁ + l₂)) q.L, (W : ℝ) ^ ε * (Y₁ W q * Y₂ W q) <
      ‖loopTr (flowG W (q.at q.u) ω) w.1 w.2‖} ⊆
      {ω : Ω W q.L | ∃ w : Word (2 * l₁) q.L, (W : ℝ) ^ (ε / 2) * Y₁ W q <
        ‖loopTr (flowG W (q.at q.u) ω) w.1 w.2‖} ∪
      {ω : Ω W q.L | ∃ w : Word (2 * l₂) q.L, (W : ℝ) ^ (ε / 2) * Y₂ W q <
        ‖loopTr (flowG W (q.at q.u) ω) w.1 w.2‖} := by
    rintro ω ⟨w, hw⟩
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hc
    obtain ⟨c1, c2⟩ := hc
    have hch := loopTr_chain (flowG W (q.at q.u) ω) l₁ l₂ hl₁ hl₂ _ _
      (fun b s => c1 (b, s)) (fun b s => c2 (b, s)) w.1 w.2
    have e : (W : ℝ) ^ (ε / 2) * Y₁ W q * ((W : ℝ) ^ (ε / 2) * Y₂ W q) =
        (W : ℝ) ^ ε * (Y₁ W q * Y₂ W q) := by rw [← hsq]; ring
    rw [e] at hch
    exact absurd hw (not_lt.mpr hch)
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    ((add_le_add (hW₁ W (by omega) q hq) (hW₂ W (by omega) q hq)).trans
      (step3Cone_two_le W (by omega) D)))

/-! ### Scales -/

private lemma step3Cone_gamma_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

private lemma step3Cone_ell_ge_one {g : ℝ} (hg : 0 ≤ g) {L : ℕ} (hL : 1 ≤ L) (u : ℝ) :
    1 ≤ ellProp g L u := by
  unfold ellProp
  refine le_min (by exact_mod_cast hL) ?_
  have : 0 ≤ g / Real.sqrt (gammaG g * (1 - u)) := div_nonneg hg (Real.sqrt_nonneg _)
  linarith

private lemma step3Cone_ell_mono {g : ℝ} (hg : 0 ≤ g) (L : ℕ) {r v : ℝ} (hrv : r ≤ v)
    (hv : v < 1) : ellProp g L r ≤ ellProp g L v := by
  unfold ellProp
  refine min_le_min le_rfl ?_
  have hγ := step3Cone_gamma_pos g
  have h1 : 0 < Real.sqrt (gammaG g * (1 - v)) := Real.sqrt_pos.2 (by nlinarith)
  have h2 : Real.sqrt (gammaG g * (1 - v)) ≤ Real.sqrt (gammaG g * (1 - r)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have : g / Real.sqrt (gammaG g * (1 - r)) ≤ g / Real.sqrt (gammaG g * (1 - v)) :=
    div_le_div_of_nonneg_left hg h1 h2
  linarith

/-- `(1 - v)ℓ_v ≤ (1 - r)ℓ_r` for `r ≤ v < 1`. -/
private lemma step3Cone_rho_ell {g : ℝ} (hg : 0 ≤ g) {L : ℕ} (hL : 1 ≤ L) {r v : ℝ}
    (hrv : r ≤ v) (hv : v < 1) :
    1 ≤ (1 - r) / (1 - v) * ellProp g L r / ellProp g L v := by
  have hγ := step3Cone_gamma_pos g
  have hℓv := step3Cone_ell_ge_one hg hL v
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
private lemma step3Cone_zeta_rho {g : ℝ} (hg : 0 ≤ g) {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L)
    {r v : ℝ} (hrv : r ≤ v) (hv : v < 1) :
    (1 - r) / (1 - v) * ellProp g L r / ellProp g L v * zetaProp g W L r = zetaProp g W L v := by
  have hγ := step3Cone_gamma_pos g
  have hℓr := step3Cone_ell_ge_one hg hL r
  have hℓv := step3Cone_ell_ge_one hg hL v
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1v : 0 < 1 - v := by linarith
  have h1r : 0 < 1 - r := by linarith
  unfold zetaProp
  field_simp

private lemma step3Cone_zeta_pos {g : ℝ} (hg : 0 ≤ g) {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L)
    {r : ℝ} (hr : r < 1) : 0 < zetaProp g W L r := by
  have hγ := step3Cone_gamma_pos g
  have hℓ := step3Cone_ell_ge_one hg hL r
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1r : 0 < 1 - r := by linarith
  unfold zetaProp
  have : 0 < (W : ℝ) * ellProp g L r * (1 - r) * gammaG g := by positivity
  positivity

/-- `ζ` is nondecreasing in time. -/
private lemma step3Cone_zeta_mono {g : ℝ} (hg : 0 ≤ g) {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L)
    {r v : ℝ} (hrv : r ≤ v) (hv : v < 1) : zetaProp g W L r ≤ zetaProp g W L v := by
  rw [← step3Cone_zeta_rho hg hW hL hrv hv]
  have h0 := (step3Cone_zeta_pos hg hW hL (lt_of_le_of_lt hrv hv)).le
  have h1 := step3Cone_rho_ell hg hL hrv hv
  nlinarith

/-- The scale `X = ζ_s^{-1/40}` of a step point, in which every envelope of the cone is a
power: `ζ_s = X^{-40}`, `R ≤ X²` and `ζ_t ≤ X^{-38}`. -/
private def step3Cone_X (W : ℕ) (q : StepPt) : ℝ :=
  (|zetaProp q.g W q.L q.s|⁻¹) ^ ((40 : ℝ)⁻¹)

/-- The facts on the scales used by the cone, at the admissible step points for large `W`. -/
private lemma step3Cone_good (R : PropRegime) (c N : ℝ) (hc : 0 < c) (hN : 20 ≤ N)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) :
    ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → ∀ q ∈ S W,
      1 ≤ W ∧ 3 ≤ q.L ∧ IsDysonRootV (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E) ∧
      0 < zetaProp q.g W q.L q.s ∧ zetaProp q.g W q.L q.s ≤ zetaProp q.g W q.L q.u ∧
      zetaProp q.g W q.L q.u ≤ zetaProp q.g W q.L q.t ∧ 1 ≤ step3Cone_X W q ∧
      step3Cone_X W q ^ 40 * zetaProp q.g W q.L q.s = 1 ∧ 1 ≤ q.ratio ∧
      q.ratio ≤ step3Cone_X W q ^ 2 ∧ zetaProp q.g W q.L q.t * step3Cone_X W q ^ 38 ≤ 1 ∧
      step3Cone_X W q ^ 20 = (Real.sqrt (zetaProp q.g W q.L q.s))⁻¹ ∧
      1 ≤ ellProp q.g q.L q.u := by
  obtain ⟨Wd, hWd⟩ := R.dyson
  refine ⟨max Wd 1, fun W hW q hq => ?_⟩
  obtain ⟨⟨d, hdJ, hreach⟩, hs1, hsu, hut, hst, hWt, hRN⟩ := hS W hq
  obtain ⟨hL3, hg0, hroot, -⟩ := hWd W (le_of_max_le_left hW) d (q.at q.t) hdJ.le hreach
  change 3 ≤ q.L at hL3
  change 0 ≤ q.g at hg0
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hL1 : 1 ≤ q.L := by omega
  have ht1 : q.t < 1 := by
    have : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    linarith
  have hu1 : q.u < 1 := lt_of_le_of_lt hut ht1
  have hZ : 0 < zetaProp q.g W q.L q.s :=
    step3Cone_zeta_pos hg0 hW1 hL1 (lt_of_le_of_lt hsu hu1)
  have hZu : zetaProp q.g W q.L q.s ≤ zetaProp q.g W q.L q.u :=
    step3Cone_zeta_mono hg0 hW1 hL1 hsu hu1
  have hZt : zetaProp q.g W q.L q.u ≤ zetaProp q.g W q.L q.t :=
    step3Cone_zeta_mono hg0 hW1 hL1 hut ht1
  have h1t : 0 < 1 - q.t := by linarith
  have hR1 : 1 ≤ q.ratio := by
    unfold StepPt.ratio
    rw [le_div_iff₀ h1t]
    linarith
  -- `ζ_t ≤ R ζ_s`
  have hZtR : zetaProp q.g W q.L q.t ≤ q.ratio * zetaProp q.g W q.L q.s := by
    have e := step3Cone_zeta_rho hg0 hW1 hL1 hst.le ht1
    have hℓs := step3Cone_ell_ge_one hg0 hL1 q.s
    have hℓt := step3Cone_ell_ge_one hg0 hL1 q.t
    have hℓ : ellProp q.g q.L q.s / ellProp q.g q.L q.t ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact step3Cone_ell_mono hg0 q.L hst.le ht1
    rw [← e]
    have hR0 : 0 ≤ (1 - q.s) / (1 - q.t) := by
      unfold StepPt.ratio at hR1; linarith
    calc (1 - q.s) / (1 - q.t) * ellProp q.g q.L q.s / ellProp q.g q.L q.t *
          zetaProp q.g W q.L q.s
        = (1 - q.s) / (1 - q.t) * (ellProp q.g q.L q.s / ellProp q.g q.L q.t) *
          zetaProp q.g W q.L q.s := by ring
      _ ≤ (1 - q.s) / (1 - q.t) * 1 * zetaProp q.g W q.L q.s := by gcongr
      _ = q.ratio * zetaProp q.g W q.L q.s := by unfold StepPt.ratio; ring
  -- `R^20 ζ_s ≤ 1`
  have hR20 : q.ratio ^ 20 * zetaProp q.g W q.L q.s ≤ 1 := by
    have hc1 : (W : ℝ) ^ (-c) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith)
    have hpow : q.ratio ^ 20 ≤ q.ratio ^ N := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hR1 (by exact_mod_cast hN)
    have hRN0 : 0 ≤ q.ratio ^ N := Real.rpow_nonneg (by linarith) _
    calc q.ratio ^ 20 * zetaProp q.g W q.L q.s ≤ q.ratio ^ N * zetaProp q.g W q.L q.t :=
          mul_le_mul hpow (hZu.trans hZt) hZ.le hRN0
      _ ≤ 1 := hRN.trans hc1
  have hZ1 : zetaProp q.g W q.L q.s ≤ 1 := by
    have : 1 ≤ q.ratio ^ 20 := one_le_pow₀ hR1
    nlinarith
  set Z := zetaProp q.g W q.L q.s with hZdef
  have hX0 : 0 ≤ step3Cone_X W q := Real.rpow_nonneg (inv_nonneg.2 (abs_nonneg _)) _
  have hX40 : step3Cone_X W q ^ 40 = Z⁻¹ := by
    unfold step3Cone_X
    rw [abs_of_pos hZ]
    have := Real.rpow_inv_natCast_pow (inv_nonneg.2 hZ.le) (n := 40) (by norm_num)
    simpa using this
  have hX40' : step3Cone_X W q ^ 40 * Z = 1 := by rw [hX40]; exact inv_mul_cancel₀ hZ.ne'
  have hZi : 1 ≤ Z⁻¹ := one_le_inv₀ hZ |>.2 hZ1
  have hX1 : 1 ≤ step3Cone_X W q := by
    by_contra hlt
    push Not at hlt
    have : step3Cone_X W q ^ 40 < 1 := pow_lt_one₀ hX0 hlt (by norm_num)
    linarith
  have hRX : q.ratio ≤ step3Cone_X W q ^ 2 := by
    have h20 : q.ratio ^ 20 ≤ (step3Cone_X W q ^ 2) ^ 20 := by
      rw [← pow_mul, hX40, le_inv_comm₀ (by positivity) hZ, ← one_div,
        le_div_iff₀ (by positivity)]
      linarith
    exact (pow_le_pow_iff_left₀ (by linarith) (by positivity) (by norm_num)).1 h20
  refine ⟨hW1, hL3, hroot, hZ, hZu, hZt, hX1, hX40', hR1, hRX, ?_, ?_, ?_⟩
  · calc zetaProp q.g W q.L q.t * step3Cone_X W q ^ 38
        ≤ q.ratio * Z * step3Cone_X W q ^ 38 :=
          mul_le_mul_of_nonneg_right hZtR (by positivity)
      _ ≤ step3Cone_X W q ^ 2 * Z * step3Cone_X W q ^ 38 := by gcongr
      _ = step3Cone_X W q ^ 40 * Z := by ring
      _ = 1 := hX40'
  · have hs0 : 0 < Real.sqrt Z := Real.sqrt_pos.2 hZ
    have e1 : (step3Cone_X W q ^ 20) ^ 2 = ((Real.sqrt Z)⁻¹) ^ 2 := by
      rw [← pow_mul, hX40, inv_pow, Real.sq_sqrt hZ.le]
    exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).1 e1
  · exact step3Cone_ell_ge_one hg0 hL1 q.u

/-- The primitive loops at the time `u` of an admissible step point: `|𝒦_k| ≤ W^δ ζ_u^{k-1}`
for `k ≥ 2`, from the primitive-loop slot of the regime. -/
private lemma step3Cone_prim (R : PropRegime) (c N : ℝ) (S : ℕ → Set StepPt)
    (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) (k : ℕ) (hk : 2 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ q ∈ S W, ∀ (a : Fin k → Fin q.L) (σ : Fin k → Bool),
      ‖primLoop q.g W q.L q.E (mRoot q.g q.L q.E) q.u a σ‖ ≤
        (W : ℝ) ^ δ * zetaProp q.g W q.L q.u ^ (k - 1) := by
  obtain ⟨W₀, hW₀⟩ := R.prim k δ hδ
  refine ⟨W₀, fun W hW q hq a σ => ?_⟩
  obtain ⟨⟨d, hdJ, hreach⟩, hs1, hsu, hut, -⟩ := hS W hq
  have hr : CmpReach R.base W d (q.at q.u) :=
    CmpReach.earlier q.u hreach (by linarith) hut
  exact hW₀ W hW d (q.at q.u) hdJ.le hr k hk le_rfl a σ

/-- `ζ X^a ≤ X^{a-38}` when `ζ X^{38} ≤ 1` and `X ≥ 1`. -/
private lemma step3Cone_pow_sub {X ζ : ℝ} (hX : 1 ≤ X) (hζ : 0 ≤ ζ) (h : ζ * X ^ 38 ≤ 1)
    (a : ℕ) : ζ * X ^ a ≤ X ^ (a - 38) := by
  have hX0 : 0 ≤ X := by linarith
  by_cases ha : 38 ≤ a
  · have e : X ^ a = X ^ (a - 38) * X ^ 38 := by rw [← pow_add]; congr 1; omega
    rw [e]
    have : 0 ≤ X ^ (a - 38) := pow_nonneg hX0 _
    nlinarith
  · have h1 : X ^ a ≤ X ^ 38 := pow_le_pow_right₀ hX (by omega)
    have h2 : ζ * X ^ a ≤ 1 := (mul_le_mul_of_nonneg_left h1 hζ).trans h
    exact h2.trans (one_le_pow₀ hX)

/-- `√(X^c) ≤ X^{⌈c/2⌉}` for `X ≥ 1`. -/
private lemma step3Cone_sqrt_pow {X : ℝ} (hX : 1 ≤ X) (c : ℕ) :
    Real.sqrt (X ^ c) ≤ X ^ ((c + 1) / 2) := by
  have hX0 : 0 ≤ X := by linarith
  calc Real.sqrt (X ^ c) ≤ Real.sqrt ((X ^ ((c + 1) / 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [← pow_mul]
        exact pow_le_pow_right₀ hX (by omega)
    _ = X ^ ((c + 1) / 2) := Real.sqrt_sq (pow_nonneg hX0 _)

private lemma step3Cone_sqrt_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-! ### The envelope of one node -/

/-- The right side of (C.36) [gc:eq:recurrence] for envelopes that are powers of `X`: with
`E_i = K_i X^{e_i}`, `B_{n+1} = 1 + K_b X^b` and
`B_{2n+2} = X^{40} + K₁X^{c₁} + K₂X^{c₂} + K₁K₂X^{c₁+c₂-38}`, every term is at most a constant
times `X^A` when the exponents satisfy the rows of (C.41) [fo:eq:finite-improvement]. -/
private lemma step3Cone_env (n A : ℕ) (X ζ : ℝ) (hX : 1 ≤ X) (hζ : 0 ≤ ζ)
    (hζX : ζ * X ^ 38 ≤ 1) (K : ℕ → ℝ) (e : ℕ → ℕ) (hK : ∀ i, 0 ≤ K i)
    (Kb K₁ K₂ : ℝ) (hKb : 0 ≤ Kb) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (b c₁ c₂ : ℕ)
    (hn : 1 ≤ n) (h20 : 20 ≤ A) (hlin : ∀ i, 1 ≤ i → i < n → e i ≤ A)
    (hquad : ∀ p, 2 ≤ p → p ≤ n → e p + e (n + 2 - p) - 38 ≤ A) (hb : e 1 + b ≤ A)
    (hc₁ : (c₁ + 1) / 2 ≤ A) (hc₂ : (c₂ + 1) / 2 ≤ A) (hc : (c₁ + c₂ - 38 + 1) / 2 ≤ A) :
    nodeEnv n (fun i => K i * X ^ e i)
      (fun i => if i = 2 * n + 2 then X ^ 40 + K₁ * X ^ c₁ + K₂ * X ^ c₂ +
        K₁ * K₂ * X ^ (c₁ + c₂ - 38) else 1 + Kb * X ^ b) ζ ≤
      (1 + ∑ i ∈ Finset.Ico 1 n, K i + ∑ p ∈ Finset.Icc 2 n, K p * K (n + 2 - p) +
        K 1 * (1 + Kb) + (1 + Real.sqrt K₁ + Real.sqrt K₂ + Real.sqrt (K₁ * K₂))) * X ^ A := by
  have hX0 : 0 ≤ X := by linarith
  have hXA : 1 ≤ X ^ A := one_le_pow₀ hX
  have hmono : ∀ m, m ≤ A → X ^ m ≤ X ^ A := fun m hm => pow_le_pow_right₀ hX hm
  unfold nodeEnv
  dsimp only
  simp only [show ¬(n + 1 = 2 * n + 2) by omega, ↓reduceIte]
  -- linear terms
  have t2 : ∑ i ∈ Finset.Ico 1 n, K i * X ^ e i ≤ (∑ i ∈ Finset.Ico 1 n, K i) * X ^ A := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    exact mul_le_mul_of_nonneg_left (hmono _ (hlin i hi.1 hi.2)) (hK i)
  -- quadratic terms
  have t3 : ζ * ∑ p ∈ Finset.Icc 2 n, K p * X ^ e p * (K (n + 2 - p) * X ^ e (n + 2 - p)) ≤
      (∑ p ∈ Finset.Icc 2 n, K p * K (n + 2 - p)) * X ^ A := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [Finset.mem_Icc] at hp
    have h1 := step3Cone_pow_sub hX hζ hζX (e p + e (n + 2 - p))
    have h2 := hmono _ (hquad p hp.1 hp.2)
    have hKK : 0 ≤ K p * K (n + 2 - p) := mul_nonneg (hK p) (hK _)
    calc ζ * (K p * X ^ e p * (K (n + 2 - p) * X ^ e (n + 2 - p)))
        = K p * K (n + 2 - p) * (ζ * X ^ (e p + e (n + 2 - p))) := by rw [pow_add]; ring
      _ ≤ K p * K (n + 2 - p) * X ^ A :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hKK
  -- light term
  have t4 : K 1 * X ^ e 1 * (1 + Kb * X ^ b) ≤ K 1 * (1 + Kb) * X ^ A := by
    have hb1 : 1 ≤ X ^ b := one_le_pow₀ hX
    have h1 : 1 + Kb * X ^ b ≤ (1 + Kb) * X ^ b := by nlinarith
    have h2 : X ^ e 1 * X ^ b ≤ X ^ A := by rw [← pow_add]; exact hmono _ hb
    have hK1 := hK 1
    calc K 1 * X ^ e 1 * (1 + Kb * X ^ b) ≤ K 1 * X ^ e 1 * ((1 + Kb) * X ^ b) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hK1 (pow_nonneg hX0 _))
      _ = K 1 * (1 + Kb) * (X ^ e 1 * X ^ b) := by ring
      _ ≤ K 1 * (1 + Kb) * X ^ A :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hK1 (by linarith))
  -- bracket term
  have t5 : Real.sqrt (X ^ 40 + K₁ * X ^ c₁ + K₂ * X ^ c₂ + K₁ * K₂ * X ^ (c₁ + c₂ - 38)) ≤
      (1 + Real.sqrt K₁ + Real.sqrt K₂ + Real.sqrt (K₁ * K₂)) * X ^ A := by
    have p1 : 0 ≤ X ^ 40 := pow_nonneg hX0 _
    have p2 : 0 ≤ K₁ * X ^ c₁ := mul_nonneg hK₁ (pow_nonneg hX0 _)
    have p3 : 0 ≤ K₂ * X ^ c₂ := mul_nonneg hK₂ (pow_nonneg hX0 _)
    have p4 : 0 ≤ K₁ * K₂ * X ^ (c₁ + c₂ - 38) :=
      mul_nonneg (mul_nonneg hK₁ hK₂) (pow_nonneg hX0 _)
    have s1 : Real.sqrt (X ^ 40) ≤ X ^ A := by
      have : Real.sqrt (X ^ 40) = X ^ 20 := by
        rw [show (40 : ℕ) = 20 * 2 by norm_num, pow_mul, Real.sqrt_sq (pow_nonneg hX0 _)]
      rw [this]; exact hmono _ h20
    have s2 : ∀ (Kc : ℝ) (c : ℕ), 0 ≤ Kc → (c + 1) / 2 ≤ A →
        Real.sqrt (Kc * X ^ c) ≤ Real.sqrt Kc * X ^ A := by
      intro Kc c hKc hcA
      rw [Real.sqrt_mul hKc]
      exact mul_le_mul_of_nonneg_left ((step3Cone_sqrt_pow hX c).trans (hmono _ hcA))
        (Real.sqrt_nonneg _)
    calc Real.sqrt (X ^ 40 + K₁ * X ^ c₁ + K₂ * X ^ c₂ + K₁ * K₂ * X ^ (c₁ + c₂ - 38))
        ≤ Real.sqrt (X ^ 40 + K₁ * X ^ c₁ + K₂ * X ^ c₂) +
            Real.sqrt (K₁ * K₂ * X ^ (c₁ + c₂ - 38)) := step3Cone_sqrt_add (by positivity) p4
      _ ≤ Real.sqrt (X ^ 40 + K₁ * X ^ c₁) + Real.sqrt (K₂ * X ^ c₂) +
            Real.sqrt (K₁ * K₂ * X ^ (c₁ + c₂ - 38)) := by
          gcongr; exact step3Cone_sqrt_add (by positivity) p3
      _ ≤ Real.sqrt (X ^ 40) + Real.sqrt (K₁ * X ^ c₁) + Real.sqrt (K₂ * X ^ c₂) +
            Real.sqrt (K₁ * K₂ * X ^ (c₁ + c₂ - 38)) := by
          gcongr; exact step3Cone_sqrt_add p1 p2
      _ ≤ X ^ A + Real.sqrt K₁ * X ^ A + Real.sqrt K₂ * X ^ A + Real.sqrt (K₁ * K₂) * X ^ A :=
          add_le_add (add_le_add (add_le_add s1 (s2 K₁ c₁ hK₁ hc₁)) (s2 K₂ c₂ hK₂ hc₂))
            (s2 (K₁ * K₂) _ (mul_nonneg hK₁ hK₂) hc)
      _ = (1 + Real.sqrt K₁ + Real.sqrt K₂ + Real.sqrt (K₁ * K₂)) * X ^ A := by ring
  nlinarith [t2, t3, t4, t5, hXA]

/-- The chain envelope: `(1 + A₁ζ)(1 + A₂ζ) ≤ ζ B_{2n+2}` with
`B_{2n+2} = X^{40} + A₁ + A₂ + K₁K₂X^{c₁+c₂-38}`, `A_i = K_iX^{c_i}`, when `X^{40}ζ ≥ 1` and
`ζX^{38} ≤ 1`. -/
private lemma step3Cone_chain_env {X ζ : ℝ} (hX : 1 ≤ X) (hζ : 0 ≤ ζ) (h40 : 1 ≤ X ^ 40 * ζ)
    (h38 : ζ * X ^ 38 ≤ 1) (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (c₁ c₂ : ℕ) :
    (1 + K₁ * X ^ c₁ * ζ) * (1 + K₂ * X ^ c₂ * ζ) ≤
      (X ^ 40 + K₁ * X ^ c₁ + K₂ * X ^ c₂ + K₁ * K₂ * X ^ (c₁ + c₂ - 38)) * ζ := by
  have h := step3Cone_pow_sub hX hζ h38 (c₁ + c₂)
  have hKKζ : 0 ≤ K₁ * K₂ * ζ := mul_nonneg (mul_nonneg hK₁ hK₂) hζ
  have h2 : K₁ * K₂ * ζ * (ζ * X ^ (c₁ + c₂)) ≤ K₁ * K₂ * ζ * X ^ (c₁ + c₂ - 38) :=
    mul_le_mul_of_nonneg_left h hKKζ
  have e : (1 + K₁ * X ^ c₁ * ζ) * (1 + K₂ * X ^ c₂ * ζ) =
      1 + K₁ * X ^ c₁ * ζ + K₂ * X ^ c₂ * ζ + K₁ * K₂ * ζ * (ζ * X ^ (c₁ + c₂)) := by
    rw [pow_add]; ring
  rw [e]
  nlinarith

/-! ### The cone -/

private lemma step3Cone_err_le (W : ℕ) (p : FlowPt) {k : ℕ} (a : Fin k → Fin p.L)
    (σ : Fin k → Bool) (ω : Ω W p.L) :
    ‖flowErr W p a σ ω‖ ≤ ‖loopTr (flowG W p ω) a σ‖ +
      ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u a σ‖ := norm_sub_le _ _

private lemma step3Cone_loop_le (W : ℕ) (p : FlowPt) {k : ℕ} (a : Fin k → Fin p.L)
    (σ : Fin k → Bool) (ω : Ω W p.L) :
    ‖loopTr (flowG W p ω) a σ‖ ≤ ‖flowErr W p a σ ω‖ +
      ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u a σ‖ := by
  have e : loopTr (flowG W p ω) a σ = flowErr W p a σ ω +
      primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u a σ := by
    unfold flowErr; ring
  rw [e]
  exact norm_add_le _ _

/-- `|D_i(u)| ≺ Y ζ_u^i` on the family `S`, with the maximum over all words of length `i`. -/
private def step3Cone_ErrB (S : ℕ → Set StepPt) (i : ℕ) (Y : ℕ → StepPt → ℝ) : Prop :=
  PrecMax StepPt.L S (Λ := fun _ q => Word i q.L)
    (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
    (fun W q _ => Y W q * zetaProp q.g W q.L q.u ^ i)

private lemma step3Cone_ErrB_congr {S : ℕ → Set StepPt} {i : ℕ} {Y Y' : ℕ → StepPt → ℝ}
    (h : step3Cone_ErrB S i Y) (hY : ∀ W q, Y W q = Y' W q) : step3Cone_ErrB S i Y' :=
  PrecMax.mono h fun W q _ _ => le_of_eq (by rw [hY W q])

/-- The exponents of the envelopes of the cone (C.41) [fo:eq:finite-improvement] in the scale
`X = ζ_s^{-1/40}` at round `j` and length `i`: `0` for `i = 1`, `12` for `i = 2` (the loss
`R^6 ≤ X^{12}`), and `max(20, 38 + 2i - 10j)` for `i ≥ 3`; `X^{20} = ζ_s^{-1/2}`. -/
private def step3Cone_a (j i : ℕ) : ℕ :=
  if i = 1 then 0 else if i = 2 then 12 else max 20 (38 + 2 * i - 10 * j)

/-- Length one at a root of (5.2) [fo:eq:dyson-family]: `|D_1(a; σ)| = |⟨G_u - M⟩_{aa}|`. -/
private lemma step3Cone_one (W : ℕ) (hW : 1 ≤ W) (p : FlowPt) (hL : 3 ≤ p.L)
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
private lemma step3Cone_two (W : ℕ) (p : FlowPt) (a : Fin 2 → Fin p.L) (σ : Fin 2 → Bool)
    (ω : Ω W p.L) : flowErr W p a σ ω = flowErr W p ![a 0, a 1] ![σ 0, σ 1] ω := by
  have ha : a = ![a 0, a 1] := by funext i; fin_cases i <;> rfl
  have hσ : σ = ![σ 0, σ 1] := by funext i; fin_cases i <;> rfl
  conv_lhs => rw [ha, hσ]

/-- Length one: `D_1(u; a; ±)` is `⟨G_u - M⟩_{aa}` or its conjugate, bounded by the averaged
local law of Step 2. -/
private lemma step3Cone_base1 (R : PropRegime) (c N cp₂ θ : ℝ) (hc : 0 < c) (hN : 20 ≤ N)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) (h2 : Step2Out cp₂ θ S)
    (j : ℕ) : step3Cone_ErrB S 1 (fun W q => 1 * step3Cone_X W q ^ step3Cone_a j 1) := by
  obtain ⟨W₁, hW₁⟩ := step3Cone_good R c N hc hN S hS
  unfold step3Cone_ErrB
  refine step3Cone_relabel h2.avg (fun _ _ w => (w.1 0, w.1 0)) W₁ ?_ ?_
  · intro W hW q hq w ω
    obtain ⟨hW1, hL3, hroot, -⟩ := hW₁ W hW q hq
    exact le_of_eq (step3Cone_one W hW1 (q.at q.u) hL3 hroot w.1 w.2 ω)
  · intro W hW q hq w
    simp [step3Cone_a]

/-- The swap of a mixed pair: `D_2(a, b; -, +) = D_2(b, a; +, -)`, by cyclicity of the trace and
the symmetry of the two-loops. -/
private lemma step3Cone_swap (W : ℕ) (p : FlowPt) (a₀ a₁ : Fin p.L) (ω : Ω W p.L) :
    flowErr W p ![a₀, a₁] ![false, true] ω = flowErr W p ![a₁, a₀] ![true, false] ω := by
  unfold flowErr
  have h1 := loopTr_rotate (flowG W p ω) ![a₁, a₀] ![true, false]
  have e1 : (![a₁, a₀] ∘ finRotate 2) = ![a₀, a₁] := by funext i; fin_cases i <;> rfl
  have e2 : (![true, false] ∘ finRotate 2) = ![false, true] := by funext i; fin_cases i <;> rfl
  rw [e1, e2] at h1
  rw [h1, primLoop_two_swap]

private lemma step3Cone_P1 (W : ℕ) (p : FlowPt) (a : Fin 2 → Fin p.L) (σ : Fin 2 → Bool)
    (ω : Ω W p.L) :
    ‖if σ 0 = true ∧ σ 1 = false then flowErr W p a σ ω else 0‖ ≤
      ‖flowErr W p ![a 0, a 1] ![true, false] ω‖ := by
  split_ifs with hσ
  · rw [step3Cone_two W p a σ ω, hσ.1, hσ.2]
  · rw [norm_zero]; exact norm_nonneg _

private lemma step3Cone_P2 (W : ℕ) (p : FlowPt) (a : Fin 2 → Fin p.L) (σ : Fin 2 → Bool)
    (ω : Ω W p.L) :
    ‖if σ 0 = false ∧ σ 1 = true then flowErr W p a σ ω else 0‖ ≤
      ‖flowErr W p ![a 1, a 0] ![true, false] ω‖ := by
  split_ifs with hσ
  · rw [step3Cone_two W p a σ ω, hσ.1, hσ.2, step3Cone_swap]
  · rw [norm_zero]; exact norm_nonneg _

private lemma step3Cone_P3 (W : ℕ) (p : FlowPt) (a : Fin 2 → Fin p.L) (σ : Fin 2 → Bool)
    (ω : Ω W p.L) :
    ‖if σ 0 = σ 1 then flowErr W p a σ ω else 0‖ ≤
      ‖flowErr W p ![a 0, a 1] ![σ 0, σ 0] ω‖ := by
  split_ifs with hσ
  · rw [step3Cone_two W p a σ ω, ← hσ]
  · rw [norm_zero]; exact norm_nonneg _

private lemma step3Cone_P123 (W : ℕ) (p : FlowPt) (a : Fin 2 → Fin p.L) (σ : Fin 2 → Bool)
    (ω : Ω W p.L) :
    ‖flowErr W p a σ ω‖ ≤
      ‖(if σ 0 = true ∧ σ 1 = false then flowErr W p a σ ω else 0) +
        (if σ 0 = false ∧ σ 1 = true then flowErr W p a σ ω else 0) +
        (if σ 0 = σ 1 then flowErr W p a σ ω else 0)‖ := by
  rcases Bool.dichotomy (σ 0) with h0 | h0 <;> rcases Bool.dichotomy (σ 1) with h1 | h1 <;>
    simp [h0, h1]

/-- Length two: the mixed pair of Step 2 (`(+,-)`, and `(-,+)` by the swap) at `F = 1` and the
same-sign pair `R^{7/2} ≤ R^6`, so `|D_2| ≺ 5R^6ζ_u^2 ≤ 5X^{12}ζ_u^2`. -/
private lemma step3Cone_base2 (R : PropRegime) (c N cp₂ θ : ℝ) (hc : 0 < c) (hN : 20 ≤ N)
    (hcp₂ : 0 < cp₂) (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (h2 : Step2Out cp₂ θ S)
    (hsame : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L × Bool)
      (fun W q x ω => flowErr W (q.at q.u) ![x.1, x.2.1] ![x.2.2, x.2.2] ω)
      (fun W q _ => q.ratio ^ ((7 : ℝ) / 2) * zetaProp q.g W q.L q.u ^ 2)) (j : ℕ) :
    step3Cone_ErrB S 2 (fun W q => 5 * step3Cone_X W q ^ step3Cone_a j 2) := by
  obtain ⟨W₁, hW₁⟩ := step3Cone_good R c N hc hN S hS
  have hp := h2.pair 1 one_pos
  have hwt : ∀ W, W₁ ≤ W → ∀ q ∈ S W, ∀ d : ℕ, q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2 *
      weightFn cp₂ θ 1 W (ellProp q.g q.L q.u) d ≤
        2 * q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2 := by
    intro W hW q hq d
    obtain ⟨hW1, -, -, -, -, -, -, -, -, -, -, -, hℓ⟩ := hW₁ W hW q hq
    have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    have hw2 : weightFn cp₂ θ 1 W (ellProp q.g q.L q.u) d ≤ 2 := by
      unfold weightFn
      have hd : 0 ≤ (d : ℝ) / ellProp q.g q.L q.u := div_nonneg (Nat.cast_nonneg _) (by linarith)
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
    refine step3Cone_relabel hp (fun _ _ w => (w.1 0, w.1 1)) W₁ ?_
      (fun W hW q hq w => hwt W hW q hq _)
    intro W hW q hq w ω
    exact step3Cone_P1 W (q.at q.u) w.1 w.2 ω
  have P2 : PrecMax StepPt.L S (Λ := fun _ q => Word 2 q.L)
      (fun W q w ω => if w.2 0 = false ∧ w.2 1 = true then flowErr W (q.at q.u) w.1 w.2 ω
        else 0)
      (fun W q _ => 2 * q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2) := by
    refine step3Cone_relabel hp (fun _ _ w => (w.1 1, w.1 0)) W₁ ?_
      (fun W hW q hq w => hwt W hW q hq _)
    intro W hW q hq w ω
    exact step3Cone_P2 W (q.at q.u) w.1 w.2 ω
  have P3 : PrecMax StepPt.L S (Λ := fun _ q => Word 2 q.L)
      (fun W q w ω => if w.2 0 = w.2 1 then flowErr W (q.at q.u) w.1 w.2 ω else 0)
      (fun W q _ => q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2) := by
    refine step3Cone_relabel hsame (fun _ _ w => (w.1 0, w.1 1, w.2 0)) W₁ ?_ ?_
    · intro W hW q hq w ω
      exact step3Cone_P3 W (q.at q.u) w.1 w.2 ω
    · intro W hW q hq w
      obtain ⟨-, -, -, -, -, -, -, -, hR1, -, -, -, -⟩ := hW₁ W hW q hq
      have h76 : q.ratio ^ ((7 : ℝ) / 2) ≤ q.ratio ^ 6 := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
      exact mul_le_mul_of_nonneg_right h76 (by positivity)
  have P12 := PrecMax.add P1 P2 (fun W q _ => by positivity) (fun W q _ => by positivity)
  have P123 := PrecMax.add P12 P3 (fun W q _ => by positivity) (fun W q _ => by positivity)
  unfold step3Cone_ErrB
  refine step3Cone_relabel P123 (fun _ _ w => w) W₁ ?_ ?_
  · intro W _ q _ w ω
    exact step3Cone_P123 W (q.at q.u) w.1 w.2 ω
  · intro W hW q hq w
    obtain ⟨-, -, -, -, -, -, hX1, -, hR1, hRX, -, -, -⟩ := hW₁ W hW q hq
    have h6 : q.ratio ^ 6 ≤ step3Cone_X W q ^ 12 := by
      calc q.ratio ^ 6 ≤ (step3Cone_X W q ^ 2) ^ 6 := pow_le_pow_left₀ (by linarith) hRX 6
        _ = step3Cone_X W q ^ 12 := by rw [← pow_mul]
    have hz : 0 ≤ zetaProp q.g W q.L q.u ^ 2 := by positivity
    have ha : step3Cone_a j 2 = 12 := by simp [step3Cone_a]
    dsimp only
    rw [ha]
    nlinarith

/-- The rough round of the cone: `|D_i| ≤ |ℒ_i| + |𝒦_i| ≺ (Rζ_u)^{i-1} + ζ_u^{i-1}` by the loop
bound of Step 1 and the primitive loops, `≤ 2R^{i-1}ζ_s^{-1}ζ_u^i ≤ 2X^{38+2i}ζ_u^i`. -/
private lemma step3Cone_rough (R : PropRegime) (c N : ℝ) (hc : 0 < c) (hN : 20 ≤ N)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) (h1 : Step1Out S)
    (i : ℕ) (hi : 3 ≤ i) :
    step3Cone_ErrB S i (fun W q => 2 * step3Cone_X W q ^ step3Cone_a 0 i) := by
  obtain ⟨W₁, hW₁⟩ := step3Cone_good R c N hc hN S hS
  have hadd := step3Cone_addDet (h1.loop i (by omega))
    (X := fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
    (Y₂ := fun W q _ => zetaProp q.g W q.L q.u ^ (i - 1)) (fun δ hδ => by
      obtain ⟨W₀, hW₀⟩ := step3Cone_prim R c N S hS i (by omega) δ hδ
      exact ⟨W₀, fun W hW q hq w ω => (step3Cone_err_le W (q.at q.u) w.1 w.2 ω).trans
        (add_le_add le_rfl (hW₀ W hW q hq w.1 w.2))⟩)
  unfold step3Cone_ErrB
  refine step3Cone_relabel hadd (fun _ _ w => w) W₁ (fun _ _ _ _ _ _ => le_rfl) ?_
  intro W hW q hq w
  obtain ⟨-, -, -, hZ, hZu, -, hX1, hX40, hR1, hRX, -, -, -⟩ := hW₁ W hW q hq
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have ha : step3Cone_a 0 (m + 1) = 40 + 2 * m := by
    unfold step3Cone_a; split_ifs <;> omega
  dsimp only
  rw [ha, Nat.add_sub_cancel]
  set X := step3Cone_X W q
  set ζ := zetaProp q.g W q.L q.u
  have hζ : 0 ≤ ζ := by linarith
  have hX0 : 0 ≤ X := by linarith
  have h40 : 1 ≤ X ^ 40 * ζ := by
    calc (1 : ℝ) = X ^ 40 * zetaProp q.g W q.L q.s := hX40.symm
      _ ≤ X ^ 40 * ζ := mul_le_mul_of_nonneg_left hZu (pow_nonneg hX0 _)
  have hζm : ζ ^ m ≤ X ^ 40 * ζ ^ (m + 1) := by
    have : 0 ≤ ζ ^ m := pow_nonneg hζ _
    calc ζ ^ m = ζ ^ m * 1 := (mul_one _).symm
      _ ≤ ζ ^ m * (X ^ 40 * ζ) := mul_le_mul_of_nonneg_left h40 this
      _ = X ^ 40 * ζ ^ (m + 1) := by rw [pow_succ]; ring
  have hRm : q.ratio ^ m ≤ X ^ (2 * m) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by linarith) hRX m
  have hXm : 1 ≤ X ^ (2 * m) := one_le_pow₀ hX1
  have e : X ^ (40 + 2 * m) = X ^ 40 * X ^ (2 * m) := pow_add _ _ _
  have hA : 0 ≤ X ^ 40 * ζ ^ (m + 1) := by positivity
  rw [mul_pow, e]
  have h1' := mul_le_mul hRm hζm (pow_nonneg hζ _) (pow_nonneg hX0 _)
  have h2' : X ^ 40 * ζ ^ (m + 1) ≤ X ^ (2 * m) * (X ^ 40 * ζ ^ (m + 1)) :=
    le_mul_of_one_le_left hA hXm
  linarith

/-- From the loop errors to the loops at length `m ≥ 2`: `ℒ_m = D_m + 𝒦_m`. -/
private lemma step3Cone_loopOf (R : PropRegime) (c N : ℝ) (S : ℕ → Set StepPt)
    (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) (m : ℕ) (hm : 2 ≤ m) (K : ℝ) (e : ℕ)
    (h : step3Cone_ErrB S m (fun W q => K * step3Cone_X W q ^ e)) :
    PrecMax StepPt.L S (Λ := fun _ q => Word m q.L)
      (fun W q w ω => loopTr (flowG W (q.at q.u) ω) w.1 w.2)
      (fun W q _ => zetaProp q.g W q.L q.u ^ (m - 1) *
        (1 + K * step3Cone_X W q ^ e * zetaProp q.g W q.L q.u)) := by
  unfold step3Cone_ErrB at h
  have hadd := step3Cone_addDet h
    (X := fun W q w ω => loopTr (flowG W (q.at q.u) ω) w.1 w.2)
    (Y₂ := fun W q _ => zetaProp q.g W q.L q.u ^ (m - 1)) (fun δ hδ => by
      obtain ⟨W₀, hW₀⟩ := step3Cone_prim R c N S hS m hm δ hδ
      exact ⟨W₀, fun W hW q hq w ω => (step3Cone_loop_le W (q.at q.u) w.1 w.2 ω).trans
        (add_le_add le_rfl (hW₀ W hW q hq w.1 w.2))⟩)
  refine PrecMax.mono hadd fun W q _ _ => le_of_eq ?_
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  ring

/-- One node `(n, j + 1)` of the cone (C.41) [fo:eq:finite-improvement], `n ≥ 3`: the error
envelopes of the shorter lengths from the same round, the length `n` and the loops of lengths
`n + 1` and `2n + 2` (the latter by (C.40) [gc:eq:chain]) from the previous round, then
`step3_node` and the rows of (C.41) [fo:eq:finite-improvement]. -/
private lemma step3Cone_node (R : PropRegime) (I : PropInputs R.base R.J) (c N cp θ : ℝ)
    (hc : 0 < c) (hN : 20 ≤ N) (hinc : IncrementInput R.base R.J)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (hSu : ∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
      (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W)
    (hin : OneStepInput cp θ (fun q : StepPt => q.at q.s) S)
    (htail : ∀ k : ℕ, 2 ≤ k → ∀ ε A : ℝ, 0 < ε → 0 < A → PrecMax StepPt.L S
      (Λ := fun W q => {w : Word k q.L // (W : ℝ) ^ ε * ellProp q.g q.L q.u < wordDiam w.1})
      (fun W q w ω => ((‖loopTr (flowG W (q.at q.u) ω) w.1.1 w.1.2‖ +
        ‖flowErr W (q.at q.u) w.1.1 w.1.2 ω‖ : ℝ) : ℂ))
      (fun W _ _ => (W : ℝ) ^ (-A)))
    (j n : ℕ) (hn : 3 ≤ n) (Kn Ko : ℕ → ℝ) (hKn : ∀ i, 0 ≤ Kn i) (hKo : ∀ i, 0 ≤ Ko i)
    (hnew : ∀ i, 1 ≤ i → i < n →
      step3Cone_ErrB S i (fun W q => Kn i * step3Cone_X W q ^ step3Cone_a (j + 1) i))
    (hold : ∀ i, 1 ≤ i → i ≤ n + 2 →
      step3Cone_ErrB S i (fun W q => Ko i * step3Cone_X W q ^ step3Cone_a j i)) :
    ∃ K : ℝ, 0 ≤ K ∧
      step3Cone_ErrB S n (fun W q => K * step3Cone_X W q ^ step3Cone_a (j + 1) n) := by
  obtain ⟨W₁, hW₁⟩ := step3Cone_good R c N hc hN S hS
  obtain ⟨l₁, l₂, hl, hl₁, hl₂, hl₁', hl₂'⟩ : ∃ l₁ l₂ : ℕ, l₁ + l₂ = n + 1 ∧ 2 ≤ l₁ ∧ 2 ≤ l₂ ∧
      2 * l₁ ≤ n + 2 ∧ 2 * l₂ ≤ n + 2 :=
    ⟨(n + 1) / 2, n + 1 - (n + 1) / 2, by omega, by omega, by omega, by omega, by omega⟩
  set Kc : ℕ → ℝ := fun i => if i < n then Kn i else Ko i with hKc
  set ec : ℕ → ℕ := fun i => if i < n then step3Cone_a (j + 1) i else step3Cone_a j i
    with hec
  set K₁ := Ko (2 * l₁)
  set K₂ := Ko (2 * l₂)
  set c₁ := step3Cone_a j (2 * l₁)
  set c₂ := step3Cone_a j (2 * l₂)
  set Kb := Ko (n + 1)
  set b := step3Cone_a j (n + 1) - 38
  have hKc0 : ∀ i, 0 ≤ Kc i := fun i => by simp only [hKc]; split_ifs; exacts [hKn i, hKo i]
  have hXnn : ∀ W q, 0 ≤ step3Cone_X W q := fun W q =>
    Real.rpow_nonneg (inv_nonneg.2 (abs_nonneg _)) _
  -- envelope premises of `step3_node`
  have hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → PrecMax StepPt.L S (Λ := fun _ q => Word i q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => (fun i W q => Kc i * step3Cone_X W q ^ ec i) i W q *
        zetaProp q.g W q.L q.u ^ i) := by
    intro i hi1 hin
    by_cases h : i < n
    · exact PrecMax.mono (hnew i hi1 h) fun W q _ _ => le_of_eq (by simp [hKc, hec, h])
    · have hi : i = n := by omega
      subst hi
      exact PrecMax.mono (hold i hi1 (by omega)) fun W q _ _ => le_of_eq (by simp [hKc, hec])
  have hL : ∀ i : ℕ, i = n + 1 ∨ i = 2 * n + 2 → PrecMax StepPt.L S (Λ := fun _ q => Word i q.L)
      (fun W q w ω => loopTr (flowG W (q.at q.u) ω) w.1 w.2)
      (fun W q _ => (fun i W q => if i = 2 * n + 2 then step3Cone_X W q ^ 40 +
          K₁ * step3Cone_X W q ^ c₁ + K₂ * step3Cone_X W q ^ c₂ +
          K₁ * K₂ * step3Cone_X W q ^ (c₁ + c₂ - 38) else 1 + Kb * step3Cone_X W q ^ b) i W q *
        zetaProp q.g W q.L q.u ^ (i - 1)) := by
    intro i hi
    rcases hi with rfl | rfl
    · have hlo := step3Cone_loopOf R c N S hS (n + 1) (by omega) Kb (step3Cone_a j (n + 1))
        (hold (n + 1) (by omega) (by omega))
      refine step3Cone_relabel hlo (fun _ _ w => w) W₁ (fun _ _ _ _ _ _ => le_rfl) ?_
      intro W hW q hq w
      obtain ⟨-, -, -, hZ, hZu, hZt, hX1, -, -, -, h38, -, -⟩ := hW₁ W hW q hq
      dsimp only
      simp only [show ¬(n + 1 = 2 * n + 2) by omega, ↓reduceIte]
      have hζ : 0 ≤ zetaProp q.g W q.L q.u := by linarith
      have h38u : zetaProp q.g W q.L q.u * step3Cone_X W q ^ 38 ≤ 1 :=
        (mul_le_mul_of_nonneg_right hZt (pow_nonneg (by linarith) _)).trans h38
      have hs := step3Cone_pow_sub hX1 hζ h38u (step3Cone_a j (n + 1))
      have hKb : 0 ≤ Kb := hKo _
      have : 1 + Kb * step3Cone_X W q ^ step3Cone_a j (n + 1) * zetaProp q.g W q.L q.u ≤
          1 + Kb * step3Cone_X W q ^ b := by
        have := mul_le_mul_of_nonneg_left hs hKb
        nlinarith
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right this (pow_nonneg hζ _)
    · have hlo₁ := step3Cone_loopOf R c N S hS (2 * l₁) (by omega) K₁ c₁
        (hold (2 * l₁) (by omega) hl₁')
      have hlo₂ := step3Cone_loopOf R c N S hS (2 * l₂) (by omega) K₂ c₂
        (hold (2 * l₂) (by omega) hl₂')
      have hch := step3Cone_chain S l₁ l₂ (by omega) (by omega) _ _ hlo₁ hlo₂
      have e : 2 * (l₁ + l₂) = 2 * n + 2 := by omega
      rw [e] at hch
      refine step3Cone_relabel hch (fun _ _ w => w) W₁ (fun _ _ _ _ _ _ => le_rfl) ?_
      intro W hW q hq w
      obtain ⟨-, -, -, hZ, hZu, hZt, hX1, hX40, -, -, h38, -, -⟩ := hW₁ W hW q hq
      dsimp only
      simp only [↓reduceIte]
      set X := step3Cone_X W q
      set ζ := zetaProp q.g W q.L q.u
      have hζ : 0 ≤ ζ := by linarith
      have hX0 : 0 ≤ X := by linarith
      have h40 : 1 ≤ X ^ 40 * ζ := by
        calc (1 : ℝ) = X ^ 40 * zetaProp q.g W q.L q.s := hX40.symm
          _ ≤ X ^ 40 * ζ := mul_le_mul_of_nonneg_left hZu (pow_nonneg hX0 _)
      have h38u : ζ * X ^ 38 ≤ 1 :=
        (mul_le_mul_of_nonneg_right hZt (pow_nonneg hX0 _)).trans h38
      have hce := step3Cone_chain_env hX1 hζ h40 h38u K₁ K₂ (hKo _) (hKo _) c₁ c₂
      have epow : ζ ^ (2 * l₁ - 1) * ζ ^ (2 * l₂ - 1) = ζ ^ (2 * n) := by
        rw [← pow_add]; congr 1; omega
      have epow' : ζ ^ (2 * n + 2 - 1) = ζ ^ (2 * n) * ζ := by
        rw [show 2 * n + 2 - 1 = 2 * n + 1 by omega, pow_succ]
      have hp : 0 ≤ ζ ^ (2 * n) := pow_nonneg hζ _
      calc ζ ^ (2 * l₁ - 1) * (1 + K₁ * X ^ c₁ * ζ) * (ζ ^ (2 * l₂ - 1) * (1 + K₂ * X ^ c₂ * ζ))
          = ζ ^ (2 * n) * ((1 + K₁ * X ^ c₁ * ζ) * (1 + K₂ * X ^ c₂ * ζ)) := by
            rw [← epow]; ring
        _ ≤ ζ ^ (2 * n) * ((X ^ 40 + K₁ * X ^ c₁ + K₂ * X ^ c₂ + K₁ * K₂ * X ^ (c₁ + c₂ - 38)) *
            ζ) := mul_le_mul_of_nonneg_left hce hp
        _ = (X ^ 40 + K₁ * X ^ c₁ + K₂ * X ^ c₂ + K₁ * K₂ * X ^ (c₁ + c₂ - 38)) *
            ζ ^ (2 * n + 2 - 1) := by rw [epow']; ring
  have hnode := step3_node R I c N cp θ hinc S hS hSu hin htail n (by omega)
    (fun i W q => Kc i * step3Cone_X W q ^ ec i)
    (fun i W q => if i = 2 * n + 2 then step3Cone_X W q ^ 40 +
          K₁ * step3Cone_X W q ^ c₁ + K₂ * step3Cone_X W q ^ c₂ +
          K₁ * K₂ * step3Cone_X W q ^ (c₁ + c₂ - 38) else 1 + Kb * step3Cone_X W q ^ b)
    (fun i W q => mul_nonneg (hKc0 i) (pow_nonneg (hXnn W q) _))
    (fun i W q => by
      have := hXnn W q
      have hK1 : 0 ≤ K₁ := hKo _
      have hK2 : 0 ≤ K₂ := hKo _
      have hKb : 0 ≤ Kb := hKo _
      split_ifs <;> positivity)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) hD hL
  refine ⟨1 + ∑ i ∈ Finset.Ico 1 n, Kc i + ∑ p ∈ Finset.Icc 2 n, Kc p * Kc (n + 2 - p) +
      Kc 1 * (1 + Kb) + (1 + Real.sqrt K₁ + Real.sqrt K₂ + Real.sqrt (K₁ * K₂)), ?_, ?_⟩
  · have h1 : 0 ≤ ∑ i ∈ Finset.Ico 1 n, Kc i := Finset.sum_nonneg fun i _ => hKc0 i
    have h2 : 0 ≤ ∑ p ∈ Finset.Icc 2 n, Kc p * Kc (n + 2 - p) :=
      Finset.sum_nonneg fun p _ => mul_nonneg (hKc0 p) (hKc0 _)
    have h3 : 0 ≤ Kc 1 * (1 + Kb) := mul_nonneg (hKc0 1) (by linarith [hKo (n + 1)])
    have h4 : 0 ≤ 1 + Real.sqrt K₁ + Real.sqrt K₂ + Real.sqrt (K₁ * K₂) := by positivity
    linarith
  unfold step3Cone_ErrB
  refine step3Cone_relabel hnode (fun _ _ w => w) W₁ (fun _ _ _ _ _ _ => le_rfl) ?_
  intro W hW q hq w
  obtain ⟨-, -, -, hZ, hZu, hZt, hX1, -, -, -, h38, -, -⟩ := hW₁ W hW q hq
  have hζt : 0 ≤ zetaProp q.g W q.L q.t := by linarith
  have henv := step3Cone_env n (step3Cone_a (j + 1) n) (step3Cone_X W q)
    (zetaProp q.g W q.L q.t) hX1 hζt h38 Kc ec hKc0 Kb K₁ K₂ (hKo _) (hKo _) (hKo _) b c₁ c₂
    (by omega)
    (by unfold step3Cone_a; split_ifs <;> omega)
    (by intro i hi1 hin; simp only [hec, step3Cone_a]; split_ifs <;> omega)
    (by intro p hp2 hpn; simp only [hec, step3Cone_a]; split_ifs <;> omega)
    (by simp only [hec, b, step3Cone_a]; split_ifs <;> omega)
    (by simp only [c₁, step3Cone_a]; split_ifs <;> omega)
    (by simp only [c₂, step3Cone_a]; split_ifs <;> omega)
    (by simp only [c₁, c₂, step3Cone_a]; split_ifs <;> omega)
  have hζ : 0 ≤ zetaProp q.g W q.L q.u ^ n := pow_nonneg (by linarith) _
  calc zetaProp q.g W q.L q.u ^ n * nodeEnv n _ _ (zetaProp q.g W q.L q.t)
      ≤ zetaProp q.g W q.L q.u ^ n * ((1 + ∑ i ∈ Finset.Ico 1 n, Kc i +
          ∑ p ∈ Finset.Icc 2 n, Kc p * Kc (n + 2 - p) + Kc 1 * (1 + Kb) +
          (1 + Real.sqrt K₁ + Real.sqrt K₂ + Real.sqrt (K₁ * K₂))) *
          step3Cone_X W q ^ step3Cone_a (j + 1) n) := mul_le_mul_of_nonneg_left henv hζ
    _ = _ := by ring

/-- The rounds of the cone (C.41) [fo:eq:finite-improvement]: for every round `j` and every
length bound `n`, constants `K_i` with `|D_i(u)| ≺ K_i X^{a(j, i)} ζ_u^i` for `1 ≤ i ≤ n`. -/
private lemma step3Cone_rounds (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N cp₂ : ℝ)
    (hc : 0 < c) (hcp₂ : 0 < cp₂) (hN : 20 ≤ N) (hinc : IncrementInput R.base R.J)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (hSu : ∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
      (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W)
    (hin : OneStepInput cp θ (fun q : StepPt => q.at q.s) S)
    (h1 : Step1Out S) (h2 : Step2Out cp₂ θ S)
    (htail : ∀ k : ℕ, 2 ≤ k → ∀ ε A : ℝ, 0 < ε → 0 < A → PrecMax StepPt.L S
      (Λ := fun W q => {w : Word k q.L // (W : ℝ) ^ ε * ellProp q.g q.L q.u < wordDiam w.1})
      (fun W q w ω => ((‖loopTr (flowG W (q.at q.u) ω) w.1.1 w.1.2‖ +
        ‖flowErr W (q.at q.u) w.1.1 w.1.2 ω‖ : ℝ) : ℂ))
      (fun W _ _ => (W : ℝ) ^ (-A)))
    (hsame : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L × Bool)
      (fun W q x ω => flowErr W (q.at q.u) ![x.1, x.2.1] ![x.2.2, x.2.2] ω)
      (fun W q _ => q.ratio ^ ((7 : ℝ) / 2) * zetaProp q.g W q.L q.u ^ 2)) :
    ∀ j n : ℕ, ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧ ∀ i, 1 ≤ i → i ≤ n →
      step3Cone_ErrB S i (fun W q => K i * step3Cone_X W q ^ step3Cone_a j i) := by
  have hbase : ∀ j i, 1 ≤ i → i ≤ 2 →
      step3Cone_ErrB S i
        (fun W q => (if i = 1 then 1 else 5) * step3Cone_X W q ^ step3Cone_a j i) := by
    intro j i hi1 hi2
    rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
    · exact step3Cone_base1 R c N cp₂ θ hc hN S hS h2 j
    · exact step3Cone_base2 R c N cp₂ θ hc hN hcp₂ S hS h2 hsame j
  intro j
  induction j with
  | zero =>
    intro n
    refine ⟨fun i => if i ≤ 2 then (if i = 1 then 1 else 5) else 2,
      fun i => by dsimp only; split_ifs <;> norm_num, fun i hi1 _ => ?_⟩
    by_cases h : i ≤ 2
    · exact step3Cone_ErrB_congr (hbase 0 i hi1 h) fun W q => by simp [h]
    · exact step3Cone_ErrB_congr (step3Cone_rough R c N hc hN S hS h1 i (by omega))
        fun W q => by simp [h]
  | succ j ih =>
    intro n
    induction n with
    | zero => exact ⟨fun _ => 0, fun _ => le_rfl, fun i h1 h2 => absurd h2 (by omega)⟩
    | succ n ihn =>
      obtain ⟨K, hK0, hK⟩ := ihn
      by_cases hn : n + 1 ≤ 2
      · refine ⟨fun i => if i ≤ n then K i else (if i = 1 then 1 else 5), fun i => ?_,
          fun i hi1 hi => ?_⟩
        · dsimp only; split_ifs <;> first | exact hK0 i | norm_num
        · by_cases h : i ≤ n
          · exact step3Cone_ErrB_congr (hK i hi1 h) fun W q => by simp [h]
          · exact step3Cone_ErrB_congr (hbase (j + 1) i hi1 (by omega)) fun W q => by simp [h]
      · obtain ⟨Ko, hKo0, hKo⟩ := ih (n + 3)
        obtain ⟨Ks, hKs0, hs⟩ := step3Cone_node R I c N cp θ hc hN hinc S hS hSu hin htail j
          (n + 1) (by omega) K Ko hK0 hKo0 (fun i h1 h2 => hK i h1 (by omega))
          (fun i h1 h2 => hKo i h1 (by omega))
        refine ⟨fun i => if i ≤ n then K i else Ks, fun i => ?_, fun i hi1 hi => ?_⟩
        · dsimp only; split_ifs; exacts [hK0 i, hKs0]
        · by_cases h : i ≤ n
          · exact step3Cone_ErrB_congr (hK i hi1 h) fun W q => by simp [h]
          · have hi' : i = n + 1 := by omega
            subst hi'
            exact step3Cone_ErrB_congr hs fun W q => by simp

/-- Step 3 of Appendix C.3 [sec:gc-one-step], the finite cone (C.41) [fo:eq:finite-improvement] at
fixed times: at each node, the projected hierarchy (C.35) [fo:eq:projected-error-equation] for
alternating words (or the stable-leg form), the moment comparison with deterministic envelopes from
the earlier nodes, the chain bound (C.40) [gc:eq:chain], Markov and sampling at the time `u`; this
gives (C.27) [fo:eq:step3] and (C.28) [fo:eq:step3-error]. -/
theorem step3_cone (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N cp₂ : ℝ) (hc : 0 < c)
    (hcp₂ : 0 < cp₂) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hN : lemmaNN0 I.Cw ≤ N)
    (hinc : IncrementInput R.base R.J)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (hSu : ∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
      (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W)
    (hin : OneStepInput cp θ (fun q : StepPt => q.at q.s) S)
    (hcmp : OneStepInput cp θ (fun q : StepPt => cmpPt (q.at q.u) q.s) S)
    (h1 : Step1Out S) (h2 : Step2Out cp₂ θ S)
    (htail : ∀ k : ℕ, 2 ≤ k → ∀ ε A : ℝ, 0 < ε → 0 < A → PrecMax StepPt.L S
      (Λ := fun W q => {w : Word k q.L // (W : ℝ) ^ ε * ellProp q.g q.L q.u < wordDiam w.1})
      (fun W q w ω => ((‖loopTr (flowG W (q.at q.u) ω) w.1.1 w.1.2‖ +
        ‖flowErr W (q.at q.u) w.1.1 w.1.2 ω‖ : ℝ) : ℂ))
      (fun W _ _ => (W : ℝ) ^ (-A)))
    (hsame : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L × Bool)
      (fun W q x ω => flowErr W (q.at q.u) ![x.1, x.2.1] ![x.2.2, x.2.2] ω)
      (fun W q _ => q.ratio ^ ((7 : ℝ) / 2) * zetaProp q.g W q.L q.u ^ 2)) :
    (∀ k : ℕ, 1 ≤ k → PrecMax StepPt.L S (Λ := fun _ q => Word k q.L)
      (fun W q w ω => loopTr (flowG W (q.at q.u) ω) w.1 w.2)
      (fun W q _ => zetaProp q.g W q.L q.u ^ (k - 1))) ∧
    ∀ k : ℕ, 1 ≤ k → PrecMax StepPt.L S (Λ := fun _ q => Word k q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => (Real.sqrt (zetaProp q.g W q.L q.s))⁻¹ * zetaProp q.g W q.L q.u ^ k) := by
  have hN20 : (20 : ℝ) ≤ N := le_trans (le_max_left _ _) hN
  have hR := step3Cone_rounds R I c cp θ N cp₂ hc hcp₂ hN20 hinc S hS hSu hin h1 h2 htail hsame
  obtain ⟨W₁, hW₁⟩ := step3Cone_good R c N hc hN20 S hS
  have herr : ∀ k : ℕ, 1 ≤ k → PrecMax StepPt.L S (Λ := fun _ q => Word k q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => (Real.sqrt (zetaProp q.g W q.L q.s))⁻¹ * zetaProp q.g W q.L q.u ^ k) := by
    intro k hk
    obtain ⟨K, hK0, hK⟩ := hR (k + 2) k
    have h := hK k hk le_rfl
    unfold step3Cone_ErrB at h
    refine step3Cone_const (K k) ?_ W₁ ?_
    · refine step3Cone_relabel h (fun _ _ w => w) W₁ (fun _ _ _ _ _ _ => le_rfl) ?_
      intro W hW q hq w
      obtain ⟨-, -, -, hZ, hZu, -, hX1, -, -, -, -, hX20, -⟩ := hW₁ W hW q hq
      have ha : step3Cone_a (k + 2) k ≤ 20 := by unfold step3Cone_a; split_ifs <;> omega
      have hXa : step3Cone_X W q ^ step3Cone_a (k + 2) k ≤ step3Cone_X W q ^ 20 :=
        pow_le_pow_right₀ hX1 ha
      rw [hX20] at hXa
      have hz : 0 ≤ zetaProp q.g W q.L q.u ^ k := pow_nonneg (by linarith) _
      dsimp only
      calc K k * step3Cone_X W q ^ step3Cone_a (k + 2) k * zetaProp q.g W q.L q.u ^ k
          ≤ K k * (Real.sqrt (zetaProp q.g W q.L q.s))⁻¹ * zetaProp q.g W q.L q.u ^ k := by
            gcongr; exact hK0 k
        _ = K k * ((Real.sqrt (zetaProp q.g W q.L q.s))⁻¹ * zetaProp q.g W q.L q.u ^ k) := by
            ring
    · intro W hW q hq w
      obtain ⟨-, -, -, hZ, hZu, -⟩ := hW₁ W hW q hq
      have : 0 ≤ zetaProp q.g W q.L q.u := by linarith
      positivity
  refine ⟨fun k hk => ?_, herr⟩
  rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk2
  · exact PrecMax.mono (h1.loop 1 le_rfl) fun W q _ _ => by simp
  · have hadd := step3Cone_addDet (herr k hk)
      (X := fun W q w ω => loopTr (flowG W (q.at q.u) ω) w.1 w.2)
      (Y₂ := fun W q _ => zetaProp q.g W q.L q.u ^ (k - 1)) (fun δ hδ => by
        obtain ⟨W₀, hW₀⟩ := step3Cone_prim R c N S hS k hk2 δ hδ
        exact ⟨W₀, fun W hW q hq w ω => (step3Cone_loop_le W (q.at q.u) w.1 w.2 ω).trans
          (add_le_add le_rfl (hW₀ W hW q hq w.1 w.2))⟩)
    refine step3Cone_const 2 ?_ W₁ ?_
    · refine step3Cone_relabel hadd (fun _ _ w => w) W₁ (fun _ _ _ _ _ _ => le_rfl) ?_
      intro W hW q hq w
      obtain ⟨-, -, -, hZ, hZu, hZt, hX1, -, -, -, h38, hX20, -⟩ := hW₁ W hW q hq
      rw [← hX20]
      set X := step3Cone_X W q
      set ζ := zetaProp q.g W q.L q.u
      have hζ : 0 ≤ ζ := by linarith
      have hX0 : 0 ≤ X := by linarith
      have h20 : X ^ 20 * ζ ≤ 1 := by
        have : X ^ 20 ≤ X ^ 38 := pow_le_pow_right₀ hX1 (by norm_num)
        calc X ^ 20 * ζ ≤ X ^ 38 * zetaProp q.g W q.L q.t :=
              mul_le_mul this hZt hζ (pow_nonneg hX0 _)
          _ ≤ 1 := by linarith
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ ζ m]
      have h0 : 0 ≤ ζ ^ m := pow_nonneg hζ _
      have h3 := mul_le_mul_of_nonneg_left h20 h0
      have e : X ^ 20 * (ζ ^ m * ζ) = ζ ^ m * (X ^ 20 * ζ) := by ring
      rw [e]
      linarith
    · intro W hW q hq w
      obtain ⟨-, -, -, hZ, hZu, -⟩ := hW₁ W hW q hq
      have : 0 ≤ zetaProp q.g W q.L q.u := by linarith
      positivity

/-- Step 3 of Appendix C.3 [sec:gc-one-step] at fixed times: the joint tails (C.29)
[fo:eq:step5-tails], the same-sign pair by the deterministic majorant
`|ℒ₂^{++}| ≤ (ℒ₂^{+-}ℒ₂^{+-})^{1/2}` and the moment comparison, and the projected hierarchy (C.35)
[fo:eq:projected-error-equation] at each node of the finite cone (C.41) [fo:eq:finite-improvement],
giving (C.27) [fo:eq:step3] and (C.28) [fo:eq:step3-error]. -/
theorem step3 (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N cp₂ : ℝ) (hc : 0 < c)
    (hcp₂ : 0 < cp₂) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hN : lemmaNN0 I.Cw ≤ N)
    (hinc : IncrementInput R.base R.J)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (hSu : ∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
      (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W)
    (hin : OneStepInput cp θ (fun q : StepPt => q.at q.s) S)
    (hcmp : OneStepInput cp θ (fun q : StepPt => cmpPt (q.at q.u) q.s) S)
    (h1 : Step1Out S) (h2 : Step2Out cp₂ θ S) : Step3Out S := by
  have htail := step3_tail R I c cp θ N cp₂ hc hcp₂ hθ hθ2 hN S hS h1 h2
  have hsame := step3_same R I c cp θ N cp₂ hc hcp₂ hθ hθ2 hN S hS hSu hin h1 h2
  obtain ⟨hloop, herr⟩ := step3_cone R I c cp θ N cp₂ hc hcp₂ hθ hθ2 hN hinc S hS hSu hin hcmp
    h1 h2 htail hsame
  exact ⟨htail, hsame, hloop, herr⟩

end LSBA
